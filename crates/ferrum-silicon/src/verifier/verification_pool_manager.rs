//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/VerificationPoolManager.scala
//!
//! Purpose:
//! Manage reusable worker verifiers and parallel verification tasks.
//!
//! Planned Rust structure:
//! VerificationPoolManager owns workers, synchronized blocking object pool, ForkJoinPool and
//! pooledVerifiers broadcast ProverLike; nested worker thread factory/worker/task bind one borrowed
//! worker per thread.
//!
//! Behavior to preserve:
//! Start creates configured workers, starts them, and creates executor; reset each worker; nested
//! tasks fork on worker threads, external calls submit. Broadcast preamble operations in worker
//! order and lazily evaluate comment. Shutdown attempts every worker stop, thread
//! shutdown/ten-second wait and pool close even after errors; interrupted teardown restores
//! interrupt and warns, other first exception propagates.
//!
//! Integration:
//! verifier::worker_verifier, verifier::default_main_verifier, interfaces::decider::prover and
//! rules::brancher.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Thread-local solver ownership, nested scheduling and cancellation cleanup.
//!
//! Status: description only; implementation has not started.
