//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/extensions/TryBlockStmt.scala
//!
//! Purpose:
//! Represent try blocks in parse and verification ASTs.
//!
//! Planned Rust structure:
//! Port PTryKeyword, PTryBlock typecheck/translateStmt and TryBlock extension statement with child
//! and pretty printing.
//!
//! Behavior to preserve:
//! Typecheck body, translate it retaining position, and expose body as sole extension subnode.
//!
//! Integration:
//! extensions::try_block_parser_plugin, Silicon executor and Silver parser/AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST extension and position handling.
//!
//! Open decisions:
//! Agree on execution failure semantics with rules::executor.
//!
//! Status: description only; implementation has not started.
