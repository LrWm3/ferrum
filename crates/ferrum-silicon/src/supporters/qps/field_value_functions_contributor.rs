//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/FieldValueFunctionsContributor.scala
//!
//! Purpose:
//! Contribute field value function preambles for quantified permissions.
//!
//! Planned Rust structure:
//! Port FieldValueFunctionsContributor and DefaultFieldValueFunctionsContributor with analyze,
//! declaration/axiom template generation, emission and reset.
//!
//! Behavior to preserve:
//! Collect fields from quantified permissions and field accesses in forall/exists triggers in
//! insertion order; emit field-value-function sorts and parameterized declarations/axioms. Select
//! no-trigger axiom template when disableISCTriggers is set.
//!
//! Integration:
//! supporters::default_sets_contributor, state::{symbol_converter,terms},
//! interfaces::preamble and interfaces::decider::term_converter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for prover emission and ordering; retain
//! field_value_functions_*.smt2 templates as resources.
//!
//! Open decisions:
//! Agree on template substitution and preamble ownership with prover and set contributor.
//!
//! Status: partial; field discovery, source template instantiation, declarations and axiom
//! emission implemented. Source sort display is supplied explicitly.

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
use ferrum_silver::ast::expression::ExpKind;
use ferrum_silver::ast::program::{Field, Program};
use ferrum_silver::ast::utility::nodes::{Node, TraversalError, subnodes};
use ferrum_silver::ast::utility::visitor::deep_collect;

#[derive(Clone, Debug)]
pub struct PreambleBlock {
    pub comment: String,
    pub commands: Vec<String>,
}
#[derive(Debug)]
pub enum FieldContributorError<E> {
    Traversal(TraversalError),
    Sort(SymbolConversionError),
    Conversion(ConversionError),
    Resource(std::io::Error),
    Render(E),
}
#[derive(Default)]
pub struct FieldValueFunctionsContributor {
    pub fields: Vec<Field>,
    pub sorts: InsertionOrderedSet<Sort>,
    pub function_blocks: Vec<PreambleBlock>,
    pub axiom_blocks: Vec<PreambleBlock>,
}
impl FieldValueFunctionsContributor {
    pub fn reset(&mut self) {
        self.fields.clear();
        self.sorts = InsertionOrderedSet::new();
        self.function_blocks.clear();
        self.axiom_blocks.clear();
    }
    /// Scan quantified permissions and field accesses in explicit quantifier triggers.
    pub fn analyze<E>(
        &mut self,
        program: &Program,
        converter: &DefaultSymbolConverter,
        term_converter: &mut TermToSmtLib2Converter,
        reader: &impl PreambleReader,
        disable_isc_triggers: bool,
        render_sort: impl Fn(&Sort) -> Result<String, E>,
    ) -> Result<(), FieldContributorError<E>> {
        fn visit(node: &Node, fields: &mut Vec<Field>) -> Result<(), TraversalError> {
            if let Node::Exp(exp) = node {
                let quantified_field = ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(exp)
                    .and_then(|(_,_,access)| match access.kind() { ExpKind::FieldAccessPredicate(field,_) => Some(field.field.clone()), _ => None });
                if let Some(field) = quantified_field {
                    if !fields.contains(&field) {
                        fields.push(field);
                    }
                } else if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) =
                    exp.kind()
                {
                    for trigger in triggers {
                        for expression in &trigger.exps {
                            let found = deep_collect(
                                &[Node::Exp(expression.clone())],
                                &subnodes,
                                &mut |node| match node {
                                    Node::FieldAccess(access) => Some(access.field.clone()),
                                    Node::Exp(exp) => match exp.kind() {
                                        ExpKind::FieldAccess(access) => Some(access.field.clone()),
                                        _ => None,
                                    },
                                    _ => None,
                                },
                            )?;
                            for field in found {
                                if !fields.contains(&field) {
                                    fields.push(field);
                                }
                            }
                        }
                    }
                }
            }
            for child in subnodes(node)? {
                visit(&child, fields)?;
            }
            Ok(())
        }
        let mut fields = self.fields.clone();
        visit(&Node::Program(program.clone()), &mut fields)
            .map_err(FieldContributorError::Traversal)?;
        let mut sorts = InsertionOrderedSet::new();
        let mut declarations = Vec::new();
        let mut axioms = Vec::new();
        let axiom_file = if disable_isc_triggers {
            "/field_value_functions_axioms_no_triggers.smt2"
        } else {
            "/field_value_functions_axioms.smt2"
        };
        for field in fields.iter() {
            let sort = converter
                .to_sort(&field.typ)
                .map_err(FieldContributorError::Sort)?;
            sorts = sorts.incl(Sort::FieldValueFunction {
                codomain: Box::new(sort.clone()),
                field_name: field.name.clone(),
            });
            let rendered = term_converter
                .convert_sort(&sort)
                .map_err(FieldContributorError::Conversion)?;
            let sanitized = term_converter
                .convert_sanitized_sort(&sort)
                .map_err(FieldContributorError::Conversion)?;
            let display = render_sort(&sort).map_err(FieldContributorError::Render)?;
            let replacements = vec![
                ("$FLD$".into(), field.name.clone()),
                ("$S$".into(), rendered),
                ("$T$".into(), sanitized),
            ];
            let decl_file = "/field_value_functions_declarations.smt2";
            declarations.push(PreambleBlock {
                comment: format!("{decl_file} [{}: {display}]", field.name),
                commands: reader
                    .read_parametric_preamble(decl_file, &replacements)
                    .map_err(FieldContributorError::Resource)?,
            });
            axioms.push(PreambleBlock {
                comment: format!("{axiom_file} [{}: {display}]", field.name),
                commands: reader
                    .read_parametric_preamble(axiom_file, &replacements)
                    .map_err(FieldContributorError::Resource)?,
            });
        }
        self.fields = fields;
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
        for block in blocks {
            sink.comment(&mut || block.comment.clone())?;
            sink.emit_all(&block.commands)?;
        }
        Ok(())
    }
    /// Source `val` snapshots were evaluated before analysis and stay empty.
    pub fn eagerly_captured_symbols(&self) -> &[String] {
        &[]
    }
    pub fn eagerly_captured_axioms(&self) -> &[String] {
        &[]
    }
}
