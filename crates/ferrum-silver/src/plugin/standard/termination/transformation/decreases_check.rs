//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/DecreasesCheck.scala
//!
//! Purpose:
//! Generate conditional and lexicographic termination assertions.
//!
//! Planned Rust structure:
//! Port DecreasesCheck createConditionCheck, createTupleCheck, recursive createLexDecreaseCheck
//! and missing-function reporting.
//!
//! Behavior to preserve:
//! Missing decreasing/bounded functions produce consistency errors and EmptyStmt. Conditions use
//! !required || given to support reason transformation, simplifying true cases. Lexicographic
//! checks use decreasing(smaller,bigger) and bounded(bigger), equality and recursive tails; tuples
//! are extended by TOP, and incompatible types fail. Preserve source type substitution maps and
//! reason transformations.
//!
//! Integration:
//! program_manager, error_trafo_factory, function_check and method_check; ast domain functions and
//! verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered substitutions, metadata and diagnostics.
//!
//! Open decisions:
//! Reconcile source type-variable map and its bounded-function key choice with domain interfaces;
//! avoid silent correction.
//!
//! Status: partial; condition and lexicographic tuple checks, reason transforms and missing
//! domain-function reports are implemented. Plugin proof generation integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::error_trafo_factory::ReasonTrafoFactory;
use crate::ast::ast::{ErrorTrafo, ErrorTransformation, Metadata};
use crate::ast::expression::{Exp, ExpExtra, ExpKind, ExpressionTypeError};
use crate::ast::program::DomainFunc;
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::r#type::TypeVar;
use std::sync::Arc;

fn with_error(error: ErrorTrafo) -> Metadata {
    Metadata {
        error_trafo: error,
        ..Metadata::default()
    }
}
fn reason_error(reason: Arc<dyn ErrorTransformation>) -> ErrorTrafo {
    ErrorTrafo::trafos(vec![], vec![reason], None)
}
/// Build `assert !required || given`, simplifying literal true cases exactly as upstream.
pub fn create_condition_check(
    required: Option<Exp>,
    given: Option<Exp>,
    error: ErrorTrafo,
    reason: ErrorTrafo,
) -> Stmt {
    let required =
        required.unwrap_or_else(|| Exp::new(ExpKind::TrueLit, with_error(reason.clone())));
    let given = given.unwrap_or_else(|| Exp::new(ExpKind::TrueLit, with_error(reason.clone())));
    if matches!(given.kind(), ExpKind::TrueLit) {
        return crate::ast::utility::statements::empty_stmt();
    }
    let condition = if matches!(required.kind(), ExpKind::TrueLit) {
        let mut metadata = given.metadata().clone();
        metadata.error_trafo = reason;
        Exp::with_extra(given.kind().clone(), metadata, given.0.extra.clone())
    } else {
        let not = Exp::new(ExpKind::Not(required), with_error(reason.clone()));
        Exp::new(ExpKind::Or(not, given), with_error(reason))
    };
    Stmt::new(StmtKind::Assert(condition), with_error(error))
}
#[derive(Debug)]
pub enum DecreasesCheckError {
    ExpressionType(ExpressionTypeError),
    MissingTypeVariable(&'static str),
}
impl From<ExpressionTypeError> for DecreasesCheckError {
    fn from(e: ExpressionTypeError) -> Self {
        Self::ExpressionType(e)
    }
}
/// Lexicographic decrease comparison. The optional TOP tail follows the exact
/// source base cases and each subexpression retains its own reason transformation.
pub fn create_lex_decrease_check(
    bigger: &[Exp],
    smaller: &[Exp],
    decreasing: &DomainFunc,
    bounded: &DomainFunc,
    factory: &ReasonTrafoFactory,
) -> Result<Exp, DecreasesCheckError> {
    let simple = reason_error(factory.generate_tuple_simple_false(None));
    let decreases = reason_error(factory.generate_tuple_decreases_false(None));
    let bound = reason_error(factory.generate_tuple_bounded_false(None));
    let decr_vars: Vec<TypeVar> = decreasing
        .formal_args
        .iter()
        .flat_map(|p| p.typ().type_variables())
        .collect();
    let bound_vars: Vec<TypeVar> = bounded
        .formal_args
        .iter()
        .flat_map(|p| p.typ().type_variables())
        .collect();
    fn go(
        bigger: &[Exp],
        smaller: &[Exp],
        decreasing: &DomainFunc,
        bounded: &DomainFunc,
        decr_vars: &[TypeVar],
        bound_vars: &[TypeVar],
        simple: &ErrorTrafo,
        decreases: &ErrorTrafo,
        bound: &ErrorTrafo,
    ) -> Result<Exp, DecreasesCheckError> {
        if smaller.is_empty() {
            return Ok(Exp::new(ExpKind::FalseLit, with_error(decreases.clone())));
        }
        if bigger.is_empty() {
            return Ok(Exp::new(ExpKind::TrueLit, with_error(simple.clone())));
        }
        let bt = bigger[0].typ()?;
        let st = smaller[0].typ()?;
        if !(bt.is_subtype(&st) || st.is_subtype(&bt)) {
            return Ok(Exp::new(ExpKind::FalseLit, with_error(decreases.clone())));
        }
        let first = decr_vars
            .first()
            .ok_or(DecreasesCheckError::MissingTypeVariable("decreasing first"))?;
        let last = decr_vars
            .last()
            .ok_or(DecreasesCheckError::MissingTypeVariable("decreasing last"))?;
        let bound_first = bound_vars
            .first()
            .ok_or(DecreasesCheckError::MissingTypeVariable("bounded first"))?;
        let mut dec_types = std::collections::HashMap::new();
        dec_types.insert(first.clone(), st);
        dec_types.insert(last.clone(), bt.clone());
        let mut bound_types = std::collections::HashMap::new();
        bound_types.insert(bound_first.clone(), bt.clone());
        bound_types.insert(last.clone(), bt);
        let app = |func: &DomainFunc, args: Vec<Exp>, types, trafo: &ErrorTrafo| {
            Exp::with_extra(
                ExpKind::DomainFuncApp(func.name.clone(), args, types),
                with_error(trafo.clone()),
                ExpExtra {
                    typ: Some(func.typ.clone()),
                    domain_name: Some(func.domain_name.clone()),
                    ..Default::default()
                },
            )
        };
        let dec = app(
            decreasing,
            vec![smaller[0].clone(), bigger[0].clone()],
            dec_types,
            decreases,
        );
        let bounded_exp = app(bounded, vec![bigger[0].clone()], bound_types, bound);
        let and = Exp::new(ExpKind::And(dec, bounded_exp), with_error(simple.clone()));
        let equal = Exp::new(
            ExpKind::EqCmp(smaller[0].clone(), bigger[0].clone()),
            with_error(decreases.clone()),
        );
        let next = go(
            &bigger[1..],
            &smaller[1..],
            decreasing,
            bounded,
            decr_vars,
            bound_vars,
            simple,
            decreases,
            bound,
        )?;
        let rest = Exp::new(ExpKind::And(equal, next), with_error(simple.clone()));
        Ok(Exp::new(ExpKind::Or(and, rest), with_error(simple.clone())))
    }
    go(
        bigger,
        smaller,
        decreasing,
        bounded,
        &decr_vars,
        &bound_vars,
        &simple,
        &decreases,
        &bound,
    )
}
/// Missing source domain functions are reported in decreasing-then-bounded order,
/// and source then returns an empty statement.
pub fn create_tuple_check(
    tuple_condition: Option<Exp>,
    bigger: &[Exp],
    smaller: &[Exp],
    decreasing: Option<&DomainFunc>,
    bounded: Option<&DomainFunc>,
    error: ErrorTrafo,
    factory: &ReasonTrafoFactory,
    mut report_missing: impl FnMut(&str),
) -> Result<Stmt, DecreasesCheckError> {
    if decreasing.is_none() {
        report_missing("function \"decreasing\" is required but not declared.");
    }
    if bounded.is_none() {
        report_missing("function \"bounded\" is required but not defined.");
    }
    let (Some(decreasing), Some(bounded)) = (decreasing, bounded) else {
        return Ok(crate::ast::utility::statements::empty_stmt());
    };
    let lex = create_lex_decrease_check(bigger, smaller, decreasing, bounded, factory)?;
    let condition = match tuple_condition {
        Some(c) => Exp::new(
            ExpKind::Implies(c, lex),
            with_error(reason_error(factory.generate_tuple_simple_false(None))),
        ),
        None => lex,
    };
    Ok(Stmt::new(StmtKind::Assert(condition), with_error(error)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::utility::nodes::Node;
    #[test]
    fn lexicographic_check_builds_decrease_and_bound_applications() {
        use crate::ast::program::{
            AnyLocalVarDecl, DomainFuncData, UnnamedLocalVarDecl, UnnamedLocalVarDeclData,
        };
        use crate::ast::r#type::{Type, TypeVar};
        let t = TypeVar::new("T");
        let arg = || {
            AnyLocalVarDecl::Unnamed(UnnamedLocalVarDecl::new(UnnamedLocalVarDeclData {
                typ: Type::Var(t.clone()),
                meta: Metadata::default(),
            }))
        };
        let make = |name: &str, args| {
            DomainFunc::new(DomainFuncData {
                name: name.into(),
                formal_args: args,
                typ: Type::Bool,
                unique: false,
                interpretation: None,
                domain_name: "Order".into(),
                meta: Metadata::default(),
            })
        };
        let decreasing = make("decreasing", vec![arg(), arg()]);
        let bounded = make("bounded", vec![arg()]);
        let bigger = Exp::new(ExpKind::IntLit(2.into()), Metadata::default());
        let smaller = Exp::new(ExpKind::IntLit(1.into()), Metadata::default());
        let factory = ReasonTrafoFactory {
            offending_node: Node::Exp(bigger.clone()),
        };
        let result =
            create_lex_decrease_check(&[bigger], &[smaller], &decreasing, &bounded, &factory)
                .unwrap();
        let ExpKind::Or(left, right) = result.kind() else {
            panic!("lex disjunction")
        };
        assert!(
            matches!(left.kind(), ExpKind::And(a,b) if matches!(a.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "decreasing") && matches!(b.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "bounded"))
        );
        assert!(
            matches!(right.kind(), ExpKind::And(_, tail) if matches!(tail.kind(), ExpKind::FalseLit))
        );
    }
    #[test]
    fn condition_simplification_and_missing_function_order() {
        let true_exp = Exp::new(ExpKind::TrueLit, Metadata::default());
        let false_exp = Exp::new(ExpKind::FalseLit, Metadata::default());
        let check = create_condition_check(
            Some(true_exp),
            Some(false_exp.clone()),
            ErrorTrafo::default(),
            ErrorTrafo::default(),
        );
        assert!(
            matches!(check.kind(), StmtKind::Assert(e) if matches!(e.kind(), ExpKind::FalseLit))
        );
        let factory = ReasonTrafoFactory {
            offending_node: Node::Exp(false_exp),
        };
        let mut messages = Vec::new();
        let empty = create_tuple_check(
            None,
            &[],
            &[],
            None,
            None,
            ErrorTrafo::default(),
            &factory,
            |message| messages.push(message.to_owned()),
        )
        .unwrap();
        assert!(matches!(empty.kind(), StmtKind::Seqn { statements, .. } if statements.is_empty()));
        assert!(messages[0].contains("decreasing"));
        assert!(messages[1].contains("bounded"));
    }
}
