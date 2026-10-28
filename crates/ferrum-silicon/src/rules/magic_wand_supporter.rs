//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MagicWandSupporter.scala
//!
//! Purpose:
//! Package, apply and transfer resources for magic wands.
//!
//! Planned Rust structure:
//! magicWandSupporter implements createChunk/evaluateWandArguments, consumeFromMultipleHeaps,
//! packageWand/packageWandWithArguments, applyWand, transfer, getEvalHeap/getExecutionHeap,
//! moveToReserveHeap and getOutEdges. The earlier self-framing check is commented out.
//!
//! Behavior to preserve:
//! Evaluate wand arguments with extended exhale disabled, restoring it. Transfer consumes reserve
//! heaps in order with retry and preserves stack order. For ordinary chunks, equate snapshots
//! under same-location and positive-permission guards; quantified basic chunks instead equate
//! snapshot maps directly. Do not equate wand snapshots. Packaging consolidates outer state first,
//! disables branch parallelism, creates abstract LHS root and wand snapshot function, produces LHS,
//! runs proof CFG with used/ops/LHS reserve heaps, then consumes RHS. Record per-branch conditions
//! and snapshot definitions; substitute a fresh unknown LHS for each merged branch, guard recorded
//! conditions with universally quantified wand token, retain LHS-independent definitions,
//! consolidate multiple branches and create wand chunk. If no branch records a result construct an
//! unconstrained wand snapshot. Application consumes wand and LHS, labels old LHS heap, applies
//! snapshot function and assumes token, produces RHS, consolidates and restores old heaps/store.
//! Preserve failure combination, reserves and nested package CFG.
//!
//! Integration:
//! rules::consumer, producer, executor, execution_flow_controller, heap_supporter,
//! state_consolidator; state::chunks and decider::path_conditions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! LHS snapshot/token representation and solver scope/continuation ownership.
//!
//! Status: description only; implementation has not started.
