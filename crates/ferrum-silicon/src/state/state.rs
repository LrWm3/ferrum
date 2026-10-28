//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/State.scala
//!
//! Purpose:
//! Carry complete symbolic execution state and merge branch states.
//!
//! Planned Rust structure:
//! State holds store, heap, program/member/CFG, old/debug heaps and records, cycle
//! tracking, quantified variables, permission factors, wand reserves, caches, trigger and
//! exhale/join flags. HeapCause, HeapRecord and IntermediateHeapRecord record provenance.
//! Implement resource/formal argument queries, cycle/ARP updates, scaling, merge variants,
//! mergeHeap, local-evaluation preservation and conflict-free map helpers.
//!
//! Behavior to preserve:
//! None member denotes CFG/method verification; config controls permission upper bounds and
//! debug expressions. Merge checks compatible fields and reports mismatches; combines
//! recorders, caches and flags according to each merge path. Conditional branch merge keeps
//! common chunks unconditional, conditions branch-only chunks, and merges mask chunks by
//! resource; matching mask chunks merge with Ite, while a mask chunk present on only one
//! branch is retained as-is. Store and old heaps receive branch conditions. Preserve retry, visited and
//! reserve-heap rules and independent branch state.
//!
//! Unconditional merge requires matching store and heap and unions ordered
//! quantified variables; conditional merge requires those variables to match.
//! Conditional store/old-heap merge discards entries present on one branch only;
//! differing store values become Ite, and invariant/reserve stacks require equal
//! lengths. Partially consumed heaps are conditionalized if only one exists.
//! Local evaluation retains only post debug records, recorder, possible triggers,
//! snapshot cache and constrainable ARPs. Temporary records with different label
//! or cause warn and are discarded; triggerExp merges by AND, caches by union.
//!
//! Integration:
//! state::heap, store, chunks, caches, terms; decider path conditions; rules, supporters
//! and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Merge invariants, branch cloning and record/solver ownership with rules and verifier.
//!
//! Status: description only; implementation has not started.
