//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/Frontend.scala
//!
//! Purpose:
//! Define phase execution and the reusable default frontend state machine.
//!
//! Planned Rust structure:
//! Represent Frontend, Phase, DefaultPhases, SingleFileFrontend, DefaultFrontend, Succ/Fail and
//! DefaultStates; retain input, loader, verifier, phase results and errors.
//!
//! Behavior to preserve:
//! Run phases in declared order; range endpoints are inclusive and membership asserted. Reset
//! requires initialization and clears prior results/messages. Each phase runs only at its
//! expected state and without prior errors, but advances state after its own failure. Result
//! returns errors or requires verification. Single-file reset rejects other counts.
//!
//! Integration:
//! frontend::sil_frontend supplies phase bodies; ast::utility loader, reporter and verifier
//! supply interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on phase callbacks, loader errors and verifier ownership with sil_frontend and verifier.
//!
//! Status: description only; implementation has not started.
