//! Port plan: ASTTransformationTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ASTTransformationTests.scala
//!
//! Purpose:
//! Port the upstream ASTTransformationTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ASTTransformationTests with custom-context and parse-tree rewrites.
//!
//! Behavior to preserve:
//! Check shared FalseLit under Not rewrites only in that context; independent siblings each
//! transform 1 to 3. Nested calls transform first arguments by depth to 2, 3 and 4; name analysis
//! at forall sees f and x. Compare reconstructed parse ASTs structurally.
//!
//! Integration:
//! ast::utility::{viper_strategy,rewriter}, parser parse tree/name analysis and frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Ensure context is branch-local and preserve shared node identity distinctions.
//!
//! Status: description only; implementation has not started.
