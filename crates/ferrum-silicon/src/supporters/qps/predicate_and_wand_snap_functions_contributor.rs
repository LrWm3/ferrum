//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/PredicateAndWandSnapFunctionsContributor.scala
//!
//! Purpose:
//! Contribute quantified predicate and wand snapshot function preambles.
//!
//! Planned Rust structure:
//! Port PredicateSnapFunctionsContributor and DefaultPredicateAndWandSnapFunctionsContributor
//! analysis, sort, template and emission groups.
//!
//! Behavior to preserve:
//! Collect predicate accesses in quantified permissions and triggers, plus quantified wand
//! identifiers. Use predicate snapshot generator sort or MagicWandSnapFunction for wands; emit
//! sorts and parameterized predicate_snap_functions declarations/axioms, switching to no-trigger
//! template under disableISCTriggers. Predicate collection is insertion ordered; wand identifiers
//! are converted to a plain Set, so its traversal order is not guaranteed. Reconcile this with
//! deterministic emission rather than assuming it is insertion ordered.
//!
//! Integration:
//! supporters::qps::predicate_snap_generator and default_sets_contributor,
//! state::chunks and state::terms and preamble/prover interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering and triggers; retain
//! predicate_snap_functions_*.smt2 templates.
//!
//! Open decisions:
//! Agree on wand identifier order and snapshot sort setup with snapshot generator and verifier.
//!
//! Status: partial; source predicate/wand discovery, templates and emission implemented.
//! Source rendering and selected snapshot strategy are explicitly supplied.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::decider::term_to_smt_lib2_converter::{ConversionError, TermToSmtLib2Converter};
use crate::interfaces::decider::prover::ProverLike;
use crate::interfaces::preamble::PreambleReader;
use crate::state::chunks::MagicWandIdentifier;
use crate::state::terms::{Sort, TermFactory};
use crate::supporters::qps::field_value_functions_contributor::{
    FieldValueFunctionsContributor, PreambleBlock,
};
use crate::supporters::qps::predicate_snap_generator::PredicateSnapGenerator;
use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::{Predicate, Program};
use ferrum_silver::ast::utility::nodes::{Node, TraversalError, subnodes};
use ferrum_silver::ast::utility::visitor::deep_collect;

#[derive(Debug)]
pub enum PredicateWandContributorError<E> {
    Traversal(TraversalError),
    MissingPredicate(String),
    Quantified(ferrum_silver::ast::utility::quantified_permissions::QuantifiedPermissionError),
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    Conversion(ConversionError),
    Resource(std::io::Error),
    Render(E),
}
#[derive(Default)]
pub struct PredicateAndWandSnapFunctionsContributor {
    pub predicates: Vec<Predicate>,
    pub wands: Vec<MagicWandIdentifier>,
    pub sorts: InsertionOrderedSet<Sort>,
    pub function_blocks: Vec<PreambleBlock>,
    pub axiom_blocks: Vec<PreambleBlock>,
}
impl PredicateAndWandSnapFunctionsContributor {
    pub fn reset(&mut self) {
        self.predicates.clear();
        self.wands.clear();
        self.sorts = InsertionOrderedSet::new();
        self.function_blocks.clear();
        self.axiom_blocks.clear();
    }
    pub fn analyze<E>(
        &mut self,
        program: &Program,
        snapshots: &PredicateSnapGenerator,
        term_converter: &mut TermToSmtLib2Converter,
        reader: &impl PreambleReader,
        disable_isc_triggers: bool,
        render_sort: impl Fn(&Sort) -> Result<String, E>,
        render_wand: impl Fn(&Exp) -> Result<String, E>,
    ) -> Result<(), PredicateWandContributorError<E>> {
        fn visit<E>(
            node: &Node,
            program: &Program,
            predicates: &mut Vec<Predicate>,
        ) -> Result<(), PredicateWandContributorError<E>> {
            if let Node::Exp(exp) = node {
                let quantified = ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(exp)
                    .and_then(|(_,_,access)|match access.kind() { ExpKind::PredicateAccessPredicate(pred) => Some(pred.location.predicate_name.clone()),_=>None });
                let mut names = Vec::new();
                if let Some(name) = quantified {
                    names.push(name);
                } else if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) =
                    exp.kind()
                {
                    for trigger in triggers {
                        for expression in &trigger.exps {
                            names.extend(
                                deep_collect(
                                    &[Node::Exp(expression.clone())],
                                    &subnodes,
                                    &mut |node| match node {
                                        Node::PredicateAccess(access) => {
                                            Some(access.predicate_name.clone())
                                        }
                                        Node::Exp(exp) => match exp.kind() {
                                            ExpKind::PredicateAccess(access) => {
                                                Some(access.predicate_name.clone())
                                            }
                                            _ => None,
                                        },
                                        _ => None,
                                    },
                                )
                                .map_err(PredicateWandContributorError::Traversal)?,
                            );
                        }
                    }
                }
                for name in names {
                    let predicate = program
                        .find_predicate_optionally(&name)
                        .cloned()
                        .ok_or(PredicateWandContributorError::MissingPredicate(name))?;
                    if !predicates.contains(&predicate) {
                        predicates.push(predicate);
                    }
                }
            }
            for child in subnodes(node).map_err(PredicateWandContributorError::Traversal)? {
                visit(&child, program, predicates)?;
            }
            Ok(())
        }
        let mut predicates = self.predicates.clone();
        visit(&Node::Program(program.clone()), program, &mut predicates)?;
        let mut wands = Vec::new();
        for wand in ferrum_silver::ast::utility::quantified_permissions::quantified_magic_wands(
            &Node::Program(program.clone()),
            program,
        )
        .map_err(PredicateWandContributorError::Quantified)?
        {
            let identifier = MagicWandIdentifier::new(wand, program)
                .map_err(PredicateWandContributorError::Wand)?;
            if !wands.contains(&identifier) {
                wands.push(identifier);
            }
        }
        // Source wand Set iteration is unspecified; native order follows first discovery.
        let mut sorts = InsertionOrderedSet::new();
        let mut declarations = Vec::new();
        let mut axioms = Vec::new();
        let declaration_file = "/predicate_snap_functions_declarations.smt2";
        let axiom_file = if disable_isc_triggers {
            "/predicate_snap_functions_axioms_no_triggers.smt2"
        } else {
            "/predicate_snap_functions_axioms.smt2"
        };
        for predicate in &predicates {
            let sort = snapshots.get_snap(predicate).0;
            sorts = sorts.incl(Sort::PredicateSnapFunction {
                codomain: Box::new(sort.clone()),
                predicate_name: predicate.name.clone(),
            });
            let converted = term_converter
                .convert_sort(&sort)
                .map_err(PredicateWandContributorError::Conversion)?;
            let display = render_sort(&sort).map_err(PredicateWandContributorError::Render)?;
            let replacements = vec![
                ("$PRD$".into(), predicate.name.clone()),
                ("$S$".into(), converted),
            ];
            declarations.push(PreambleBlock {
                comment: format!("{declaration_file} [{}: {display}]", predicate.name),
                commands: reader
                    .read_parametric_preamble(declaration_file, &replacements)
                    .map_err(PredicateWandContributorError::Resource)?,
            });
            // The pinned no-trigger template uses a snapshot-sort-based PSF
            // name and a misspelled domain placeholder. Instantiate both with
            // the declared resource identifier without changing resource bytes.
            let mut axiom_replacements = Vec::new();
            if disable_isc_triggers {
                axiom_replacements.push(("$PSF<$S$>".into(), "$PSF<$PRD$>".into()));
                axiom_replacements.push(("$FRD$".into(), "$PRD$".into()));
            }
            axiom_replacements.extend(replacements.iter().cloned());
            axioms.push(PreambleBlock {
                comment: format!("{axiom_file} [{}: {display}]", predicate.name),
                commands: reader
                    .read_parametric_preamble(axiom_file, &axiom_replacements)
                    .map_err(PredicateWandContributorError::Resource)?,
            });
        }
        for wand in &wands {
            let sort = Sort::MagicWandSnapFunction;
            let id = wand.to_string();
            sorts = sorts.incl(Sort::PredicateSnapFunction {
                codomain: Box::new(sort.clone()),
                predicate_name: id.clone(),
            });
            let converted = term_converter
                .convert_sort(&sort)
                .map_err(PredicateWandContributorError::Conversion)?;
            let display = render_sort(&sort).map_err(PredicateWandContributorError::Render)?;
            let original = render_wand(&wand.ghost_free_wand)
                .map_err(PredicateWandContributorError::Render)?;
            let replacements = vec![("$PRD$".into(), id.clone()), ("$S$".into(), converted)];
            declarations.push(PreambleBlock {
                comment: format!("{declaration_file} [{original}: {display}]"),
                commands: reader
                    .read_parametric_preamble(declaration_file, &replacements)
                    .map_err(PredicateWandContributorError::Resource)?,
            });
            // The pinned no-trigger template uses a snapshot-sort-based PSF
            // name and a misspelled domain placeholder. Instantiate both with
            // the declared resource identifier without changing resource bytes.
            let mut axiom_replacements = Vec::new();
            if disable_isc_triggers {
                axiom_replacements.push(("$PSF<$S$>".into(), "$PSF<$PRD$>".into()));
                axiom_replacements.push(("$FRD$".into(), "$PRD$".into()));
            }
            axiom_replacements.extend(replacements.iter().cloned());
            axioms.push(PreambleBlock {
                comment: format!("{axiom_file} [{id}: {display}]"),
                commands: reader
                    .read_parametric_preamble(axiom_file, &axiom_replacements)
                    .map_err(PredicateWandContributorError::Resource)?,
            });
        }
        self.predicates = predicates;
        self.wands = wands;
        self.sorts = sorts;
        self.function_blocks = declarations;
        self.axiom_blocks = axioms;
        Ok(())
    }
    pub fn declare_sorts<E>(
        &self,
        factory: &TermFactory,
        sink: &mut impl ProverLike<Error = E>,
    ) -> Result<(), E> {
        for sort in self.sorts.iter() {
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
