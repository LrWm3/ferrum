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
//! Status: description only; implementation has not started.
