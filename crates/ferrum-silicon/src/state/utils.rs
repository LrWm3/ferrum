//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Utils.scala
//!
//! Purpose:
//! Provide term traversal/reconstruction and reference disjointness helpers.
//!
//! Planned Rust structure:
//! computeReferenceDisjointnesses and expression variant inspect store and supported
//! chunks; subterms enumerates term families; transform applies pre, recursive
//! reconstruction and post.
//!
//! Behavior to preserve:
//! Exclude the reference itself; quantified fields contribute only singleton receivers;
//! expression variant uses optional debug expressions. Distinct is treated as leaf;
//! equality reconstruction asserts unchanged sort. Recursive predicate is evaluated on
//! original term, not pre-rewritten term.
//!
//! Integration:
//! state::terms, state::chunks, state::state and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Exhaustive reconstruction and preserving upstream omissions with terms.
//!
//! Status: description only; implementation has not started.
