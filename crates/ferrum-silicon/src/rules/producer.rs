//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Producer.scala
//!
//! Purpose:
//! Produce assertions and permissions into symbolic state using snapshot functions.
//!
//! Planned Rust structure:
//! ProductionRules and producer implement produce/produces, recursive produceR, ordered
//! produceTlcs, wrappedProduceTlc and produceTlc. Dispatch impure implication/conditional with
//! branch or more-joins, impure let, ordinary access, quantified permissions, invalid inhale-exhale
//! node and pure expressions.
//!
//! Behavior to preserve:
//! Select whenInhaling, adapt and split snapshot functions per conjunct, retaining error
//! attribution and order. If snapshot pairing throws illegal argument, return Unreachable only when
//! solver proves False; otherwise propagate exception. Implication false branch assumes empty
//! snapshot constraint. Extended exhale updates reserve heap before Q. Access evaluates args then
//! permissions, checks nonnegative, restores ARPs, scales permissions with configured wildcard
//! optimization and produces a chunk. Quantified path tracks recorder and delegates
//! injectivity/negative-permission checks; pure expression assumes its value after empty snapshot
//! constraint. Preserve impure join consolidation differences and logging scope.
//!
//! Integration:
//! rules::consumer, evaluator, brancher, joiner, heap_supporter, permission_supporter and
//! supporters::snapshot_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot-function, continuation and branch context ownership with consumer.
//!
//! Status: description only; implementation has not started.
