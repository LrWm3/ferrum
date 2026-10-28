//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Executor.scala
//!
//! Purpose:
//! Execute Silver CFGs and statements over symbolic state.
//!
//! Planned Rust structure:
//! ExecutionRules and executor implement CFG/block/statement exec, execs, follow/follows,
//! handleOutEdge, path IDs, ssaifyRhs and hack407 helpers. Dispatch sequence, labels, declarations,
//! local/field assignments, allocation, inhale/exhale/assert, method calls, fold/unfold,
//! package/apply, havoc/havocall and TryBlock.
//!
//! Behavior to preserve:
//! Follow edge conditions through brancher; optional all-join mode merges if-statement branches,
//! while loop incoming edges first havoc written locals, check invariant well-definedness in a
//! local scope, consume invariant, retain leftover heap in invariantContexts, replay recorded
//! assumptions, check guard framing and follow ordered internal then exit edges. Backedges consume
//! invariant and terminate; out edges merge leftover context. Preserve block/path reports and
//! nonfatal/fatal result combination. Allocation assumes nonnull and reference disjointness. Assert
//! false uses smoke check; assertions restore heap unless extended exhale transfers resources;
//! disableSubsumption uses isolated consume. Calls evaluate actuals, bind formals, consume
//! preconditions, fresh returns, produce postconditions and restore caller store/old heaps; during
//! packaging reconstruct old heap from consumed precondition snapshot. SSAify RHS terms other than
//! variables and literals with a fresh equality definition. Preserve special havoc and consolidation
//! calls, wand reserve movement, TryBlock fallback and rejection of unexpected CFG-level statements.
//!
//! Integration:
//! rules::evaluator, consumer, producer, brancher, joiner, execution_flow_controller,
//! predicate_supporter, magic_wand_supporter, havoc_supporter, heap_supporter and silver::cfg.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! CFG path reporting, branch state, snapshots and continuation/verifier ownership.
//!
//! Status: description only; implementation has not started.
