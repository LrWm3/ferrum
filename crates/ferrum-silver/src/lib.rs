//! Upstream:
//! Ferrum-owned crate assembly described in PLAN.md, gathering the pinned Silver source modules.
//! Verification boundary reference:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Verifier.scala
//!
//! Purpose:
//! Assemble Silver's language infrastructure as the shared library beneath Silicon and Ferrum.
//!
//! Planned Rust structure:
//! Declare ast, cfg, components, frontend, logger, parser, plugin, reporter, testing, utility
//! and verifier modules as they become implemented. Re-export only stable public boundaries;
//! keep file-level symbols in their mapped modules until cross-file interfaces are reconciled.
//! Package-object aliases live in package.rs; keyword names such as type need raw identifiers
//! in eventual module declarations. Test harness assembly remains separate from normal startup.
//!
//! Behavior to preserve:
//! Preserve a single shared AST and diagnostic type vocabulary. Importing the crate must not
//! start a verifier, load plugins implicitly, or allocate a solver process. Preserve explicit
//! component lifecycles and frontend plugin ordering through the owning implementations.
//!
//! Integration:
//! Used by ferrum_silicon and the root facade. The crate must not depend on Silicon; verifier
//! traits and reporter interfaces provide the direction of control across that boundary.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for module assembly, visibility and common representation
//! decisions. Native replacement dependencies and feature flags are chosen during implementation.
//!
//! Open decisions:
//! Reconcile public re-exports, plugin extension traits and optional harness dependencies with
//! frontend, AST and verifier owners before exposing stable APIs.
//!
//! Status: workspace assembly active; backend implementation is incomplete.

pub mod ast;
pub mod cfg;
pub mod components;
pub mod frontend;
pub mod logger;
pub mod parser;
pub mod plugin;
pub mod reporter;
pub mod resources;
pub mod testing;
pub mod utility;
pub mod verifier;
