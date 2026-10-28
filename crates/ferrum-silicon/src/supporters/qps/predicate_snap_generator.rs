//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/PredicateSnapGenerator.scala
//!
//! Purpose:
//! Determine predicate snapshot sorts and formal symbolic variables.
//!
//! Planned Rust structure:
//! Port PredicateSnapGenerator setup/getSnap, snapMap/formalVarMap and lifecycle.
//!
//! Behavior to preserve:
//! Visit predicate accesses; derive sort from body optimalSnapshotSort or Snap for abstract
//! predicate, convert formal parameters to variables. getSnap returns cached sort with true or
//! default Snap with false; reset clears maps.
//!
//! Integration:
//! supporters::snapshot_supporter and qps::predicate_and_wand_snap_functions_contributor;
//! state::symbol_converter and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for snapshot identity and lifecycle.
//!
//! Open decisions:
//! Reconcile setup ordering and cache ownership with verifier and snapshot_supporter.
//!
//! Status: predicate access traversal, snapshot/formal-variable maps and reset implemented.
//! Snapshot strategy is supplied by the selected heap encoding.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::identifiers::Identifier;
use crate::state::package::OrderedMap;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{Sort, Term, TermFactory};
use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::{Predicate, Program};
use ferrum_silver::ast::utility::nodes::{Node, TraversalError, subnodes};

#[derive(Debug)]
pub enum PredicateSnapError<E> {
    Traversal(TraversalError),
    MissingPredicate(String),
    Sort(SymbolConversionError),
    Snapshot(E),
}
#[derive(Default)]
pub struct PredicateSnapGenerator {
    pub snap_map: OrderedMap<String, Sort>,
    pub formal_var_map: OrderedMap<String, Vec<Term>>,
}
impl PredicateSnapGenerator {
    /// Visit each predicate access and cache its optimal body snapshot sort and
    /// unsuffixed formal variables, including repeated accesses in source order.
    pub fn setup<E>(
        &mut self,
        factory: &TermFactory,
        converter: &DefaultSymbolConverter,
        program: &Program,
        mut optimal: impl FnMut(&Exp, &Program) -> Result<(Sort, bool), E>,
    ) -> Result<(), PredicateSnapError<E>> {
        fn visit<E>(
            generator: &mut PredicateSnapGenerator,
            factory: &TermFactory,
            converter: &DefaultSymbolConverter,
            program: &Program,
            node: &Node,
            optimal: &mut impl FnMut(&Exp, &Program) -> Result<(Sort, bool), E>,
        ) -> Result<(), PredicateSnapError<E>> {
            let access = match node {
                Node::PredicateAccess(access) => Some(access),
                Node::Exp(exp) => match exp.kind() {
                    ExpKind::PredicateAccess(access) => Some(access),
                    _ => None,
                },
                _ => None,
            };
            if let Some(access) = access {
                let predicate = program
                    .find_predicate_optionally(&access.predicate_name)
                    .ok_or_else(|| {
                        PredicateSnapError::MissingPredicate(access.predicate_name.clone())
                    })?;
                let sort = match &predicate.body {
                    Some(body) => {
                        optimal(body, program)
                            .map_err(PredicateSnapError::Snapshot)?
                            .0
                    }
                    None => Sort::Snap,
                };
                let formals = predicate
                    .formal_args
                    .iter()
                    .map(|arg| {
                        Ok(factory.var(
                            Identifier::new(&arg.name),
                            converter
                                .to_sort(&arg.typ)
                                .map_err(PredicateSnapError::Sort)?,
                            false,
                        ))
                    })
                    .collect::<Result<Vec<_>, PredicateSnapError<E>>>()?;
                generator
                    .formal_var_map
                    .insert(predicate.name.clone(), formals);
                generator.snap_map.insert(predicate.name.clone(), sort);
            }
            for child in subnodes(node).map_err(PredicateSnapError::Traversal)? {
                visit(generator, factory, converter, program, &child, optimal)?;
            }
            Ok(())
        }
        visit(
            self,
            factory,
            converter,
            program,
            &Node::Program(program.clone()),
            &mut optimal,
        )
    }
    pub fn get_snap(&self, predicate: &Predicate) -> (Sort, bool) {
        match self.snap_map.get(&predicate.name) {
            Some(sort) => (sort.clone(), true),
            None => (Sort::Snap, false),
        }
    }
    pub fn reset(&mut self) {
        self.snap_map = OrderedMap::new();
        self.formal_var_map = OrderedMap::new();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    use ferrum_silver::ast::expression::PredicateAccess;
    use ferrum_silver::ast::program::{Method, MethodData, PredicateData};
    use ferrum_silver::ast::statement::PredicateAccessPredicate;

    #[test]
    fn finds_access_predicate_location_in_method_precondition() {
        let meta = ferrum_silver::ast::ast::Metadata::default();
        let predicate = Predicate::new(PredicateData {
            name: "P".into(),
            formal_args: vec![],
            body: Some(Exp::new(ExpKind::TrueLit, meta.clone())),
            meta: meta.clone(),
        });
        let location = PredicateAccess::new(vec![], "P".into(), meta.clone());
        let access = Exp::new(
            ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                location,
                None,
                meta.clone(),
            )),
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![access],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![predicate.clone()],
            vec![method],
            vec![],
            meta,
        );
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let mut generator = PredicateSnapGenerator::default();
        generator
            .setup(&factory, &converter, &program, |_, _| {
                Ok::<_, ()>((Sort::Int, true))
            })
            .unwrap();
        assert_eq!(generator.get_snap(&predicate), (Sort::Int, true));
        assert!(generator.formal_var_map.get(&"P".to_string()).is_some());
    }
}
