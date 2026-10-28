//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/MaskHeapFunctionsContributor.scala
//!
//! Purpose:
//! Contribute map, mask and wrapper preambles for mask-heap encoding.
//!
//! Planned Rust structure:
//! Port MaskHeapFunctionsContributor analysis, field/predicate/wand sort collection, parameterized
//! declaration and axiom generation, and lifecycle/emission.
//!
//! Behavior to preserve:
//! Only analyze under maskHeapMode; collect all fields and predicates, add mask/predicate sorts
//! and wand heap sort when wands occur. Emit map and zero-mask definitions, predicate/wand
//! variants and per-resource wrappers in source order with exact sort/name substitutions.
//!
//! Integration:
//! rules::mask_heap_supporter, state::terms sorts, config, preamble_reader and prover;
//! default_sets_contributor.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and ordered prover emission; retain maps_*,
//! mask_* and heapwrappers_*.smt2 resources.
//!
//! Open decisions:
//! Reconcile template substitutions, predicate/wand sort identity and configuration ownership with
//! mask heap rules.
//!
//! Status: mask-heap sort/resource analysis, source templates and emission implemented.
//! Source sort display is supplied explicitly.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::decider::term_to_smt_lib2_converter::{ConversionError, TermToSmtLib2Converter};
use crate::interfaces::decider::prover::ProverLike;
use crate::interfaces::preamble::PreambleReader;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{Sort, TermFactory};
use crate::supporters::qps::field_value_functions_contributor::{
    FieldValueFunctionsContributor, PreambleBlock,
};
use ferrum_silver::ast::expression::ExpKind;
use ferrum_silver::ast::program::{Field, Predicate, Program};
use ferrum_silver::ast::utility::nodes::{Node, TraversalError, subnodes};
use ferrum_silver::ast::utility::visitor::exists_defined;

#[derive(Debug)]
pub enum MaskHeapContributorError<E> {
    Traversal(TraversalError),
    Sort(SymbolConversionError),
    Conversion(ConversionError),
    Resource(std::io::Error),
    Render(E),
}
#[derive(Default)]
pub struct MaskHeapFunctionsContributor {
    pub wand_heaps_required: bool,
    pub fields: Vec<Field>,
    pub predicates: Vec<Predicate>,
    pub heap_sorts: InsertionOrderedSet<Sort>,
    pub predicate_sorts: InsertionOrderedSet<Sort>,
    pub function_blocks: Vec<PreambleBlock>,
    pub axiom_blocks: Vec<PreambleBlock>,
}
impl MaskHeapFunctionsContributor {
    pub fn reset(&mut self) {
        *self = Self::default();
    }
    pub fn analyze<E>(
        &mut self,
        program: &Program,
        mask_heap_mode: bool,
        converter: &DefaultSymbolConverter,
        terms: &mut TermToSmtLib2Converter,
        reader: &impl PreambleReader,
        render_sort: impl Fn(&Sort) -> Result<String, E>,
        render_predicate: impl Fn(&Predicate) -> Result<String, E>,
    ) -> Result<(), MaskHeapContributorError<E>> {
        if !mask_heap_mode {
            return Ok(());
        }
        let mut fields = self.fields.clone();
        for field in &program.fields {
            if !fields.contains(field) {
                fields.push(field.clone());
            }
        }
        let mut predicates = self.predicates.clone();
        for predicate in &program.predicates {
            if !predicates.contains(predicate) {
                predicates.push(predicate.clone());
            }
        }
        let has_wand = exists_defined(&Node::Program(program.clone()), &subnodes,
            &mut |node| matches!(node, Node::Exp(exp) if matches!(exp.kind(),ExpKind::MagicWand(..))))
            .map_err(MaskHeapContributorError::Traversal)?;
        let wand = self.wand_heaps_required || has_wand;
        let mut heap_sorts = InsertionOrderedSet::new();
        for field in &fields {
            heap_sorts = heap_sorts.incl(Sort::Heap(Box::new(
                converter
                    .to_sort(&field.typ)
                    .map_err(MaskHeapContributorError::Sort)?,
            )));
        }
        heap_sorts = heap_sorts.incl(Sort::Heap(Box::new(Sort::Perm)));
        let mut predicate_sorts: InsertionOrderedSet<_> =
            [Sort::PredHeap, Sort::PredMask].into_iter().collect();
        if wand {
            predicate_sorts = predicate_sorts.incl(Sort::WandHeap);
        }
        fn blocks<E>(
            fields: &[Field],
            predicates: &[Predicate],
            heap_sorts: &InsertionOrderedSet<Sort>,
            wand: bool,
            converter: &DefaultSymbolConverter,
            terms: &mut TermToSmtLib2Converter,
            reader: &impl PreambleReader,
            render: &impl Fn(&Sort) -> Result<String, E>,
            render_predicate: &impl Fn(&Predicate) -> Result<String, E>,
            axioms: bool,
        ) -> Result<Vec<PreambleBlock>, MaskHeapContributorError<E>> {
            let maps = if axioms {
                "/maps_axioms.smt2"
            } else {
                "/maps_functions.smt2"
            };
            let masks = if axioms {
                "/mask_axioms.smt2"
            } else {
                "/mask_functions.smt2"
            };
            let wrappers = if axioms {
                "/heapwrappers_axioms.smt2"
            } else {
                "/heapwrappers_functions.smt2"
            };
            let mut output = Vec::new();
            let mut emit = |file: &str,
                            comment: String,
                            replacements: Vec<(String, String)>|
             -> Result<(), MaskHeapContributorError<E>> {
                output.push(PreambleBlock {
                    comment,
                    commands: reader
                        .read_parametric_preamble(file, &replacements)
                        .map_err(MaskHeapContributorError::Resource)?,
                });
                Ok(())
            };
            for heap in heap_sorts.iter() {
                let Sort::Heap(value) = heap else {
                    unreachable!("heap sorts")
                };
                let s = terms
                    .convert_sort(value)
                    .map_err(MaskHeapContributorError::Conversion)?;
                let t = terms
                    .convert_sanitized_sort(value)
                    .map_err(MaskHeapContributorError::Conversion)?;
                let display = render(value).map_err(MaskHeapContributorError::Render)?;
                emit(
                    maps,
                    format!("{maps} [sort: {display}]"),
                    vec![("$S$".into(), s), ("$T$".into(), t)],
                )?;
            }
            emit(masks, masks.into(), vec![])?;
            let r = terms
                .convert_sort(&Sort::Ref)
                .map_err(MaskHeapContributorError::Conversion)?;
            let snap = terms
                .convert_sort(&Sort::Snap)
                .map_err(MaskHeapContributorError::Conversion)?;
            let perm = terms
                .convert_sort(&Sort::Perm)
                .map_err(MaskHeapContributorError::Conversion)?;
            let mwsf = terms
                .convert_sort(&Sort::MagicWandSnapFunction)
                .map_err(MaskHeapContributorError::Conversion)?;
            if !predicates.is_empty() || wand {
                for (tag, value) in [("$Pred", snap.clone()), ("$PredMask", perm.clone())]
                    .into_iter()
                    .chain(wand.then_some(("$MWSF", mwsf.clone())))
                {
                    let rep = vec![
                        ("$Hp.get_$Perm".into(), "$Hp.get_$PredMask".into()),
                        ("$Hp<$Perm>".into(), "$Hp<$PredMask>".into()),
                        ("$S$".into(), value),
                        ("$T$".into(), tag.into()),
                        (r.clone(), snap.clone()),
                    ];
                    emit(
                        maps,
                        format!("{maps} [{}]", tag.trim_start_matches('$')),
                        rep,
                    )?;
                }
                emit(
                    masks,
                    masks.into(),
                    vec![
                        (r.clone(), snap.clone()),
                        (perm.clone(), "$PredMask".into()),
                        ("zeroMask".into(), "zeroPredMask".into()),
                    ],
                )?;
            }
            for field in fields {
                let sort = converter
                    .to_sort(&field.typ)
                    .map_err(MaskHeapContributorError::Sort)?;
                let s = terms
                    .convert_sort(&sort)
                    .map_err(MaskHeapContributorError::Conversion)?;
                let t = terms
                    .convert_sanitized_sort(&sort)
                    .map_err(MaskHeapContributorError::Conversion)?;
                let display = render(&sort).map_err(MaskHeapContributorError::Render)?;
                emit(
                    wrappers,
                    format!("{wrappers} [id: {}, sort: {display}]", field.name),
                    vec![
                        ("$FLD$".into(), field.name.clone()),
                        ("$S$".into(), s),
                        ("$T$".into(), t),
                    ],
                )?;
            }
            for predicate in predicates {
                let rep = vec![
                    ("$Hp.get_$Perm".into(), "$Hp.get_$PredMask".into()),
                    ("$Hp<$Perm>".into(), "$Hp<$PredMask>".into()),
                    ("$T$".into(), "$Pred".into()),
                    ("$FLD$".into(), predicate.name.clone()),
                    ("$S$".into(), snap.clone()),
                    (r.clone(), snap.clone()),
                ];
                emit(
                    wrappers,
                    format!(
                        "{wrappers} [predicate: {}.name,]",
                        render_predicate(predicate).map_err(MaskHeapContributorError::Render)?
                    ),
                    rep,
                )?;
            }
            if wand {
                let get = if axioms {
                    "$Hp.get_$PredMask"
                } else {
                    "$Hp.get_$MWSF"
                };
                let rep = vec![
                    ("$Hp.get_$Perm".into(), get.into()),
                    ("$Hp<$Perm>".into(), "$Hp<$PredMask>".into()),
                    ("$T$".into(), "$MWSF".into()),
                    ("$FLD$".into(), "$MWSF".into()),
                    ("$S$".into(), mwsf),
                    (r, snap),
                ];
                emit(wrappers, format!("{wrappers} [wands,]"), rep)?;
            }
            Ok(output)
        }
        let declarations = blocks(
            &fields,
            &predicates,
            &heap_sorts,
            wand,
            converter,
            terms,
            reader,
            &render_sort,
            &render_predicate,
            false,
        )?;
        let axioms = blocks(
            &fields,
            &predicates,
            &heap_sorts,
            wand,
            converter,
            terms,
            reader,
            &render_sort,
            &render_predicate,
            true,
        )?;
        self.fields = fields;
        self.predicates = predicates;
        self.wand_heaps_required = wand;
        self.heap_sorts = heap_sorts;
        self.predicate_sorts = predicate_sorts;
        self.function_blocks = declarations;
        self.axiom_blocks = axioms;
        Ok(())
    }
    pub fn declare_sorts<E>(
        &self,
        factory: &TermFactory,
        sink: &mut impl ProverLike<Error = E>,
    ) -> Result<(), E> {
        for sort in self.heap_sorts.iter().chain(self.predicate_sorts.iter()) {
            sink.declare(&factory.sort_decl(sort.clone()))?;
        }
        Ok(())
    }
    pub fn emit_blocks<E>(
        blocks: &[PreambleBlock],
        sink: &mut impl ProverLike<Error = E>,
    ) -> Result<(), E> {
        FieldValueFunctionsContributor::emit_blocks(blocks, sink)
    }
    pub fn eagerly_captured_symbols(&self) -> &[String] {
        &[]
    }
    pub fn eagerly_captured_axioms(&self) -> &[String] {
        &[]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader;
    use crate::state::terms::TermOptions;
    #[test]
    fn empty_mask_program_still_generates_mask_preamble() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), true);
        let mut terms = TermToSmtLib2Converter::new(factory);
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        );
        let mut contributor = MaskHeapFunctionsContributor::default();
        let reader = SmtLib2PreambleReader::default();
        contributor
            .analyze(
                &program,
                true,
                &converter,
                &mut terms,
                &reader,
                |s| Ok::<_, ()>(s.to_string()),
                |p| Ok::<_, ()>(p.name.clone()),
            )
            .unwrap();
        assert!(
            contributor
                .heap_sorts
                .contains(&Sort::Heap(Box::new(Sort::Perm)))
        );
        assert!(
            contributor
                .function_blocks
                .iter()
                .any(|block| block.comment == "/mask_functions.smt2" && !block.commands.is_empty())
        );
        assert!(
            contributor
                .axiom_blocks
                .iter()
                .any(|block| block.comment == "/mask_axioms.smt2" && !block.commands.is_empty())
        );
        assert!(!contributor.wand_heaps_required);
    }
}
