//! Upstream:
//! Ferrum-owned crate assembly described in PLAN.md, gathering the pinned Silicon source modules.
//! Backend boundary reference:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Assemble the native symbolic execution backend on top of ferrum_silver.
//!
//! Planned Rust structure:
//! Declare silicon, config, utils, package, common, state, interfaces, decider, rules,
//! supporters, resources, verifier, reporting, logger, debugger and extensions modules as
//! implementations arrive. Keep tightly coupled state/rule/verifier APIs in this crate and
//! expose the backend/session boundary to the facade. Account separately for the dormant
//! annotation module; its existence does not require enabling its historical macro behavior.
//!
//! Behavior to preserve:
//! Use Silver's AST and public results rather than a second AST definition. Preserve explicit
//! backend/worker/solver lifecycle, configuration-controlled alternatives and resource loading.
//! Crate import alone does not start solvers or verification. Maintain distinctions between
//! symbolic snapshots, chunk permissions and solver terms while assembling the modules.
//!
//! Integration:
//! ferrum_silver supplies language, frontend, diagnostic and reporting contracts. The root
//! ferrum library uses silicon/config entry points; all internal rule and solver services
//! remain coordinated through verifier interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, continuations, ordered collections and solver
//! sessions. Module visibility/re-exports and native runtime dependencies remain provisional.
//!
//! Open decisions:
//! Resolve public session/configuration APIs, worker context sharing, optional debugger/logging
//! features and packaged solver resources with the owning modules before workspace activation.
//!
//! Status: description only; implementation has not started.
