//! Port plan: RewriteWithCycles.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/RewriteWithCycles.scala
//!
//! Purpose:
//! Port the upstream RewriteWithCycles.scala test or test-harness component.
//!
//! Planned Rust structure:
//! RewriteWithCycles, visitAll and mutable SlimGraph test type.
//!
//! Behavior to preserve:
//! Use ancestor identity/noRec to avoid cycles while allowing a shared node to be visited again.
//! Assert simple three-node cycle totals 222 after doubling and complex graph totals 3933 after
//! tripling, including repeated shared node.
//!
//! Integration:
//! ast::utility::rewriter::{rewritable,strategy}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Preserve cyclic graph identity and actual visiting behavior; do not rely on recursive
//! structural hashing.
//!
//! Status: description only; implementation has not started.
