//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Brancher.scala
//!
//! Purpose:
//! Split symbolic execution on a condition with optional parallel else branch.
//!
//! Planned Rust structure:
//! BranchingRules and brancher.branch perform feasibility checks, construct then/else tasks,
//! preserve solver scopes, report branch failures and combine results.
//!
//! Behavior to preserve:
//! Skip feasibility checks for short-circuit conjunctions or conditions containing quantified
//! variables, excluding wand snapshot variables; otherwise check negation first. If then is
//! infeasible, assume else feasible without a second check; otherwise check the condition. Represent
//! skipped paths as Unreachable. Execute then before waiting for else; synchronous future
//! defers else, while parallel mode transfers path conditions, declarations and prover options to
//! worker. Restore worker/current options and path conditions as needed, wait even after terminal
//! failure when parallel, propagate worker exceptions, and retain fresh declarations across joins.
//!
//! Integration:
//! rules::execution_flow_controller, rules::state_consolidator, rules::joiner,
//! interfaces::verification, verifier pool and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Worker/solver ownership and deferred continuation protocol.
//!
//! Status: description only; implementation has not started.
