//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Config.scala
//!
//! Purpose:
//! Define Silicon command-line configuration, validation and solver policy.
//!
//! Planned Rust structure:
//! Config extends Silver frontend config; port SMT option/assertion/exhale/saturation converters,
//! all option groups and derived values, validation and final verify. Companion defines
//! ConfigValue, Sink, AssertionMode, ExhaleMode, JoinMode, ProverStateSaturationTimeout and
//! StateConsolidationMode.
//!
//! Behavior to preserve:
//! Preserve defaults and distinction between supplied and default values: Z3 stdio default, QP
//! more-complete default, ordinary greedy default, zero global timeout and error count zero meaning
//! unlimited. Solver timeout derives from config arguments before -t option; flyweight iff Z3-API.
//! Saturation scales five weights with minimum 10ms and disables zero weights/base. Z3 path
//! considers option, environment then PATH; cvc5 option/environment/default. Preserve mode and
//! resource/cache/trigger/branch/debug/axiomatization switches and validation of incompatible
//! mask-heap, parallel/debug, counterexample and solver choices. Prover log $infile is explicitly
//! unimplemented. Preserve parent frontend option behavior and exact error distinctions.
//!
//! Integration:
//! ferrum_silver::frontend::sil_front_end_config, decider solver implementations, verifier and rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native CLI parsing, validation and execution-wide config ownership.
//!
//! Status: description only; implementation has not started.
