//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/PredicateSupporter.scala
//!
//! Purpose:
//! Fold and unfold predicate resources, including cached predicate contents.
//!
//! Planned Rust structure:
//! PredicateSupportRules and predicateSupporter implement fold, unfold and producePredicateContents
//! for leaf and branch trees.
//!
//! Behavior to preserve:
//! Fold binds formal arguments, scales permission, consumes body with snapshot, restores store and
//! scaling, produces predicate chunk, then optionally assumes unfold trigger and resource trigger.
//! Unfold consumes predicate chunk, chooses cached contents or produces body from its snapshot,
//! saturates, assumes configured trigger and restores store/scaling. Cached leaves substitute and
//! scale chunks, convert singleton resources to quantified chunks where needed, record maps and
//! consolidate; branches use optional impure join except while unfolding, otherwise branch
//! directly.
//!
//! Integration:
//! rules::consumer, producer, heap_supporter, brancher, joiner, quantified_chunk_support,
//! state_consolidator and supporters::predicate_verification_unit.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot and permission scaling, branch continuation and predicate-content ownership.
//!
//! Status: description only; implementation has not started.
