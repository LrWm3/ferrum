//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Decider.scala
//!
//! Purpose:
//! Coordinate solver, path conditions, fresh symbols and assertions for a verifier.
//!
//! Planned Rust structure:
//! Decider interface and DefaultDeciderProvider.decider implement prover selection/lifecycle,
//! option save/reset, scope and path stack, assumptions/definitions/debug recording,
//! checks/assertions, fresh variables/functions/macros/ARPs, aliases, model and statistics, and
//! branch worker declaration transfer.
//!
//! Behavior to preserve:
//! Unknown prover name warns and falls back to Z3 stdio; start probes version and warns outside
//! bounds. Push path stack then solver, pop solver then stack; setPcs replays layers into solver
//! scopes for parallel work. Filter already-known facts unless enforced, retain ordered definition
//! versus ordinary assumptions; checkSmoke means unsat, assert stores failing query and calls
//! continuation. Fresh declarations use ordered set except parallel branch mode, macros retain
//! order and deduplicate by name. Alias only eligible HasVarRepr terms in method verification
//! outside quantified and wand packaging contexts. Reset solver/path/declarations/options; model
//! generation asserts False.
//!
//! Integration:
//! interfaces::decider::prover, decider::path_conditions, verifier::base_verifier, state::terms and
//! rules::brancher.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Per-worker solver, mutable term alias, path stack and continuation ownership.
//!
//! Status: description only; implementation has not started.
