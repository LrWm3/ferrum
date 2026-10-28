//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/writer/TermWriter.scala
//!
//! Purpose:
//! Serialize symbolic terms and sorts to log JSON.
//!
//! Planned Rust structure:
//! Port TermWriter toJSON overloads and unary/binary/variable helpers.
//!
//! Behavior to preserve:
//! Preserve JSON type/key strings for quantification, application, lookups, Boolean combinators,
//! ITE, variables, let, literals and collection forms; quantification omits triggers/global flag.
//! Unknown terms use upstream misspelled unstructrured type. Preserve sort-specific
//! field/predicate names and array order.
//!
//! Integration:
//! logger::writer::symb_ex_log_report_writer and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term identity, ordering and JSON compatibility.
//!
//! Open decisions:
//! Decide how to represent newer terms while retaining existing fallback and wire schema.
//!
//! Status: partial; native JSON schema and source operator dispatch implemented.
//! Exact literal/fallback rendering is injected; nullable quantifier names remain unrepresented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::{
    logger::records::symbolic_record::{RecordError, RecordRenderer},
    state::terms::{Sort, Term, TermKind},
};
use serde_json::{Value, json};
pub fn sort_to_json(sort: &Sort) -> Value {
    match sort {
        Sort::Unit => json!({"id":"Unit"}),
        Sort::Seq(element) => json!({"id":"Seq","elementsSort":sort_to_json(element)}),
        Sort::Set(element) => json!({"id":"Set","elementsSort":sort_to_json(element)}),
        Sort::Multiset(element) => json!({"id":"Multiset","elementsSort":sort_to_json(element)}),
        Sort::UserSort(id) => json!({"id":"UserSort","name":id.name()}),
        Sort::FieldValueFunction {
            codomain,
            field_name,
        } => json!({"id":"FVF","fieldName":field_name,"elementSort":sort_to_json(codomain)}),
        Sort::PredicateSnapFunction {
            codomain,
            predicate_name,
        } => json!({"id":"PSF","predName":predicate_name,"elementSort":sort_to_json(codomain)}),
        _ => json!({"id":sort.id().name()}),
    }
}
/// Source term serialization keeps fallback spelling and delegates exact literal
/// and fallback text to the source renderer, never Rust Debug formatting.
pub fn term_to_json(term: &Term, renderer: &dyn RecordRenderer) -> Result<Value, RecordError> {
    use TermKind::*;
    let binary = match term.kind() {
        Plus(a, b) | PermPlus(a, b) => Some(("+", a, b)),
        Minus(a, b) | PermMinus(a, b) => Some(("-", a, b)),
        Times(a, b) | PermTimes(a, b) | IntPermTimes(a, b) => Some(("*", a, b)),
        Div(a, b) | PermIntDiv(a, b) | PermPermDiv(a, b) => Some(("/", a, b)),
        Mod(a, b) => Some(("%", a, b)),
        Implies(a, b) => Some(("==>", a, b)),
        Iff(a, b) => Some(("<==>", a, b)),
        BuiltinEquals(a, b) => Some(("==", a, b)),
        CustomEquals(a, b) => Some(("===", a, b)),
        Less(a, b) | PermLess(a, b) => Some(("<", a, b)),
        AtMost(a, b) | PermAtMost(a, b) => Some(("<=", a, b)),
        Greater(a, b) => Some((">", a, b)),
        AtLeast(a, b) => Some((">=", a, b)),
        PermMin(a, b) => Some(("PermMin", a, b)),
        SeqAppend(a, b) => Some(("++", a, b)),
        SeqDrop(a, b) => Some(("SeqDrop", a, b)),
        SeqTake(a, b) => Some(("SeqTake", a, b)),
        SeqAt(a, b) => Some(("SeqAt", a, b)),
        SeqIn(a, b) => Some(("SeqIn", a, b)),
        SeqInTrigger(a, b) => Some(("SeqInTrigger", a, b)),
        SetAdd(a, b) | MultisetAdd(a, b) => Some(("+", a, b)),
        SetUnion(a, b) | MultisetUnion(a, b) => Some(("∪", a, b)),
        SetIntersection(a, b) | MultisetIntersection(a, b) => Some(("∩", a, b)),
        SetSubset(a, b) | MultisetSubset(a, b) => Some(("⊂", a, b)),
        SetDifference(a, b) | MultisetDifference(a, b) => Some(("\\", a, b)),
        SetDisjoint(a, b) => Some(("disj", a, b)),
        SetIn(a, b) => Some(("in", a, b)),
        MultisetCount(a, b) => Some(("MultisetCount", a, b)),
        MapLookup(a, b) => Some(("MapLookup", a, b)),
        Combine(a, b) => Some(("Combine", a, b)),
        MwsfLookup(a, b) => Some(("MWSFLookup", a, b)),
        MagicWandToken(a, b) => Some(("MagicWandToken", a, b)),
        _ => None,
    };
    if let Some((op, a, b)) = binary {
        return Ok(
            json!({"type":"binary","op":op,"lhs":term_to_json(a,renderer)?,"rhs":term_to_json(b,renderer)?}),
        );
    }
    let unary = match term.kind() {
        Not(p) => Some(("!", p)),
        PermNegation(p) => Some(("-", p)),
        SeqLength(p) => Some(("SeqLength:", p)),
        SetCardinality(p) => Some(("SetCardinality:", p)),
        MultisetCardinality(p) => Some(("MultisetCardinality:", p)),
        MapCardinality(p) => Some(("MapCardinality:", p)),
        MapDomain(p) => Some(("MapDomain:", p)),
        MapRange(p) => Some(("MapRange:", p)),
        First(p) => Some(("First:", p)),
        Second(p) => Some(("Second:", p)),
        _ => None,
    };
    if let Some((op, p)) = unary {
        return Ok(json!({"type":"unary","op":op,"p":term_to_json(p,renderer)?}));
    }
    let values = |terms: &[Term]| {
        terms
            .iter()
            .map(|t| term_to_json(t, renderer))
            .collect::<Result<Vec<_>, _>>()
    };
    Ok(match term.kind() {
        Quantification {
            quantifier,
            vars,
            body,
            name,
            ..
        } => {
            json!({"type":"quantification","quantifier":match quantifier { crate::state::terms::Quantifier::Forall => "QA", crate::state::terms::Quantifier::Exists => "QE" },"vars":values(vars)?,"body":term_to_json(body,renderer)?,"name":name})
        }
        App { applicable, args } => {
            json!({"type":"application","applicable":applicable.id().name(),"args":values(args)?,"sort":sort_to_json(term.sort())})
        }
        Lookup(field, function, receiver) => {
            json!({"type":"lookup","field":field,"fieldValueFunction":term_to_json(function,renderer)?,"receiver":term_to_json(receiver,renderer)?})
        }
        PredicateLookup(predicate, function, args) => {
            json!({"type":"predicateLookup","predicate":predicate,"predicateSnapFunction":term_to_json(function,renderer)?,"args":values(args)?})
        }
        And(terms) => json!({"type":"and","terms":values(terms)?}),
        Or(terms) => json!({"type":"or","terms":values(terms)?}),
        Distinct(symbols) => {
            json!({"type":"distinct","symbols":symbols.iter().map(|s| s.data().id.name()).collect::<Vec<_>>()})
        }
        Ite(cond, yes, no) => {
            json!({"type":"ite","cond":term_to_json(cond,renderer)?,"thenBranch":term_to_json(yes,renderer)?,"elseBranch":term_to_json(no,renderer)?})
        }
        Var(var) => {
            json!({"type":"variable","id":var.id.name(),"sort":sort_to_json(&var.sort),"isWildcard":var.is_wildcard})
        }
        SortWrapper(t, sort) => {
            json!({"type":"sortWrapper","term":term_to_json(t,renderer)?,"sort":sort_to_json(sort)})
        }
        Let(bindings, body) => {
            json!({"type":"let","bindings":bindings.iter().map(|(v,t)| Ok(json!({"var":term_to_json(v,renderer)?,"value":term_to_json(t,renderer)?}))).collect::<Result<Vec<Value>,RecordError>>()?,"body":term_to_json(body,renderer)?})
        }
        Unit
        | IntLiteral(_)
        | Null
        | ZeroMask
        | PredZeroMask
        | True
        | False
        | SeqNil(_)
        | EmptySet(_)
        | EmptyMultiset(_)
        | EmptyMap(..)
        | NoPerm
        | FullPerm
        | FractionPermLiteral(_) => {
            json!({"type":"literal","sort":sort_to_json(term.sort()),"value":renderer.term(term)?})
        }
        SeqRanged(a, b) => {
            json!({"type":"seqRanged","lhs":term_to_json(a,renderer)?,"rhs":term_to_json(b,renderer)?})
        }
        SeqSingleton(p) => json!({"type":"seqSingleton","value":term_to_json(p,renderer)?}),
        SeqUpdate(seq, index, value) => {
            json!({"type":"seqUpdate","seq":term_to_json(seq,renderer)?,"index":term_to_json(index,renderer)?,"value":term_to_json(value,renderer)?})
        }
        SingletonSet(p) => json!({"type":"singletonSet","value":term_to_json(p,renderer)?}),
        SingletonMultiset(p) => {
            json!({"type":"singletonMultiset","value":term_to_json(p,renderer)?})
        }
        _ => json!({"type":"unstructrured","value":renderer.term(term)?}),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{
        chunks::Chunk,
        identifiers::Identifier,
        terms::{Quantifier, TermFactory, TermOptions},
    };
    use ferrum_silver::ast::utility::nodes::Node;
    struct Text;
    impl RecordRenderer for Text {
        fn node(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("node"))
        }
        fn term(&self, term: &Term) -> Result<String, RecordError> {
            match term.kind() {
                TermKind::ZeroMask => Ok("ZeroMask".into()),
                TermKind::PredZeroMask => Ok("PredZeroMask".into()),
                _ => Err(RecordError::Unsupported("fallback")),
            }
        }
        fn chunk(&self, _: &Chunk) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("chunk"))
        }
        fn source_line_column(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("position"))
        }
    }
    #[test]
    fn empty_masks_keep_source_literal_shape() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        for term in [factory.zero_mask(), factory.pred_zero_mask()] {
            assert_eq!(
                term_to_json(&term, &Text).unwrap(),
                json!({"type":"literal","sort":sort_to_json(term.sort()),"value":Text.term(&term).unwrap()})
            );
        }
    }
    #[test]
    fn quantifier_wire_names_follow_source_overridden_strings() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let variable = factory.var(Identifier::new("b"), Sort::Bool, false);
        for (kind, wire) in [(Quantifier::Forall, "QA"), (Quantifier::Exists, "QE")] {
            let term = factory
                .quantification(
                    kind,
                    vec![variable.clone()],
                    variable.clone(),
                    vec![],
                    "q".into(),
                    true,
                    Some(9),
                )
                .unwrap();
            assert_eq!(
                term_to_json(&term, &Text).unwrap(),
                json!({"type":"quantification","quantifier":wire,"vars":[{"type":"variable","id":"b","sort":{"id":"Bool"},"isWildcard":false}],"body":{"type":"variable","id":"b","sort":{"id":"Bool"},"isWildcard":false},"name":"q"})
            );
        }
    }
}
