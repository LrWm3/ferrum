//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MagicWandSnapFunctionsContributor.scala
//!
//! Purpose:
//! Declare magic-wand snapshot functions when the program uses wands.
//!
//! Planned Rust structure:
//! Port MagicWandSnapFunctionsContributor analyze, declarations, sort emission and lifecycle.
//!
//! Behavior to preserve:
//! Only contribute MagicWandSnapFunction sort and declaration lines when an AST magic wand occurs;
//! no axioms. Reset clears collected data.
//!
//! Integration:
//! interfaces::preamble, prover and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for preamble ordering; retain
//! magic_wand_snap_functions_declarations.smt2.
//!
//! Open decisions:
//! Agree on resource loading and sort declaration deduplication with other snapshot contributors.
//!
//! Status: implemented source existence traversal, resource loading, reset and declarations.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2024 ETH Zurich.
use crate::interfaces::decider::prover::ProverLike;
use crate::interfaces::preamble::PreambleReader;
use crate::state::terms::{Sort, TermFactory};
use ferrum_silver::ast::expression::ExpKind;
use ferrum_silver::ast::program::Program;
use ferrum_silver::ast::utility::nodes::{Node, TraversalError, subnodes};
use ferrum_silver::ast::utility::visitor::exists_defined;

pub const DECLARATIONS_RESOURCE: &str = "/magic_wand_snap_functions_declarations.smt2";
#[derive(Debug)]
pub enum AnalyzeError {
    Traversal(TraversalError),
    Resource(std::io::Error),
}
#[derive(Default)]
pub struct MagicWandSnapFunctionsContributor {
    pub sorts: Vec<Sort>,
    pub declarations: Vec<String>,
}
impl MagicWandSnapFunctionsContributor {
    pub fn reset(&mut self) {
        self.sorts.clear();
        self.declarations.clear();
    }
    pub fn analyze(
        &mut self,
        program: &Program,
        reader: &impl PreambleReader,
    ) -> Result<(), AnalyzeError> {
        if !exists_defined(&Node::Program(program.clone()), &subnodes, &mut |node| matches!(node, Node::Exp(exp) if matches!(exp.kind(), ExpKind::MagicWand(..)))).map_err(AnalyzeError::Traversal)? {
            return Ok(());
        }
        self.sorts = vec![Sort::MagicWandSnapFunction];
        self.declarations = reader
            .read_preamble(DECLARATIONS_RESOURCE)
            .map_err(AnalyzeError::Resource)?;
        Ok(())
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        sink: &mut P,
    ) -> Result<(), P::Error> {
        for sort in &self.sorts {
            sink.declare(&factory.sort_decl(sort.clone()))?;
        }
        Ok(())
    }
    pub fn declare_symbols<P: ProverLike>(&self, sink: &mut P) -> Result<(), P::Error> {
        sink.emit_all(&self.declarations)
    }
}
