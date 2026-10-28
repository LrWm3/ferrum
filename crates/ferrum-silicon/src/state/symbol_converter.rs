//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/SymbolConverter.scala
//!
//! Purpose:
//! Translate Silver types and functions into Silicon symbols.
//!
//! Planned Rust structure:
//! SymbolConverter and DefaultSymbolConverter implement toSort, toSortSpecificId and
//! domain/heap-dependent toFunction overloads.
//!
//! Behavior to preserve:
//! Require concrete domain types and SMTLIB backend names; reject internal, type variable
//! and wand sorts. Interpreted domain functions use SMTFun; in mask-heap mode function
//! arguments use resource-specific heaps, otherwise leading Snap.
//!
//! Integration:
//! ferrum_silver::ast, state::terms, rules::mask_heap_supporter and verifier config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Converter context and configuration ownership.
//!
//! Status: description only; implementation has not started.
