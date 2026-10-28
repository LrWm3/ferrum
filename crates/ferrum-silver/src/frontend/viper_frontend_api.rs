//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperFrontendAPI.scala
//!
//! Purpose:
//! Accept constructed Silver programs through a reusable frontend and plugin pipeline.
//!
//! Planned Rust structure:
//! Represent ViperFrontendAPI and MinimalViperFrontendAPI with initialize, verify, stop and
//! starting-state override.
//!
//! Behavior to preserve:
//! Initialize builds/configures verifier with ignoreFile and dummy filename, resets plugins;
//! verify and stop require initialization. Preserve upstream starting state and phase lists,
//! including Minimal’s verification-only path. The base API sets state to ConsistencyCheck
//! before running phases; DefaultFrontend.consistencyCheck only runs at Translation, so its
//! listed consistency phase is skipped in this call path. Verification still runs, including
//! plugin filtering. SiliconFrontendAPI supplies no override of this state or phase method.
//!
//! Integration:
//! frontend::sil_frontend, ast::program, plugin manager and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Reconcile repeated-call state/reset and the apparent skipped consistency check with
//! frontend::frontend, SiliconFrontendAPI and PLAN.md; record any deliberate correction.
//!
//! Status: description only; implementation has not started.
