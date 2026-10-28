//! Port plan: Collect statements, free locals and written locals.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Statements.scala
//!
//! Purpose:
//! Collect statements, free locals and written locals.
//!
//! Planned Rust structure:
//! Statements.EmptyStmt, children, undeclLocalVars and writtenVars.
//!
//! Behavior to preserve:
//! Children flatten sequences but include If/While and recurse into their bodies. Local
//! collection tracks quantified, Seqn and Let declarations, fails on mismatched variable
//! types, and deduplicates. Written variables use source traversal and ordering, including
//! nested-loop intersection with undeclared locals.
//!
//! Integration:
//! ast::{statement,expression,ast}, ast::utility::{nodes,visitor} and cfg::silver::silver_cfg.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on local variable equality and traversal/context semantics with visitor and CFG
//! analysis.
//!
//! Status: description only; implementation has not started.
