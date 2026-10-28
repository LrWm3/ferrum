//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/HeapSupporter.scala
//!
//! Purpose:
//! Define heap encoding contract and implement the default chunk-based heap rules.
//!
//! Planned Rust structure:
//! HeapSupportRules specifies single/quantified consumption and production, field
//! access/assignment, current permission, havoc, forperm, triggers, snapshots, wand reserve
//! operations and empty heap. DefaultHeapSupportRules/defaultHeapSupporter route to chunkSupporter
//! and quantifiedChunkSupporter; helper groups construct wand chunks, trigger variants and
//! conditional havoc.
//!
//! Behavior to preserve:
//! Field assignment consumes full permission before producing new value; greedy quantified modes
//! retry and continuation must leave retry action before executing later work. Current permission
//! sums alias-guarded chunks or uses summarised quantified maps and assumes field upper bounds.
//! Field access uses cached summary with re-emitted definitions or singleton/summarised map, checks
//! positive permission except in trigger mode, records snapshot and possible triggers.
//! Produce/consume dispatch by quantified resource, preserving distinct insufficient-permission and
//! missing-wand errors and configured predicate inhale triggers. Havoc replaces snapshots
//! conditionally; quantified havoc assumes agreement of old/new maps outside condition, with
//! inverse-based havocall conditions. Forperm builds per-chunk matching/positive conditions.
//! Preserve resource snapshot conversions, fresh quantified wand maps, trigger generation and
//! reserve heap merges.
//!
//! Integration:
//! rules::chunk_supporter, quantified_chunk_support, mask_heap_supporter, evaluator, consumer,
//! producer, havoc_supporter, predicate_supporter and magic_wand_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Encoding interface, snapshot/trigger alternatives and continuation/context ownership.
//!
//! Status: description only; implementation has not started.
