//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/concurrency/package.scala
//!
//! Purpose:
//! Adapt a deferred computation to synchronous Future semantics.
//!
//! Planned Rust structure:
//! SynchronousFuture stores callable and optional result; functionToCallable wraps a
//! by-name function.
//!
//! Behavior to preserve:
//! get executes on first successful call and caches result; isDone reflects cache,
//! isCancelled is false. Timed get and cancel are upstream unimplemented.
//!
//! Integration:
//! verifier worker and execution scheduling.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Represent unimplemented timed get/cancel explicitly without reporting success.
//!
//! Status: description only; implementation has not started.
