//! Upstream:
//! Ferrum-owned assembly described in PLAN.md; this file has no one-to-one Scala counterpart.
//! Backend and embedding reference:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Expose the native verification library used by the CLI and a future Prusti adapter.
//!
//! Planned Rust structure:
//! Re-export selected Silver program, diagnostic and verification-result types. Provide a thin
//! configuration/session facade over ferrum_silicon::silicon and its frontend APIs, with entry
//! paths for source input and already constructed programs. Keep verification rules in Silicon.
//!
//! Behavior to preserve:
//! Retain configure/start/verify/reset/stop lifecycle boundaries, reporter delivery and failure
//! distinctions. Source inputs run the translated frontend phases; constructed AST inputs use
//! the embedding path. Reconcile that path's upstream skipped frontend consistency phase with
//! Silicon's own consistency checks before defining a public guarantee. Library calls return
//! results and diagnostics; process exit belongs to the CLI.
//!
//! Integration:
//! ferrum_silver::{ast,frontend,verifier,reporter}, ferrum_silicon::{silicon,config,verifier},
//! and src/main.rs. A Prusti adapter consumes this facade without rustc_private in these crates.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for explicit session ownership and lifecycle cleanup. Public
//! signatures, cancellation and borrowing of programs/reporters remain provisional.
//!
//! Open decisions:
//! Agree on source-versus-AST entry APIs, repeated-run reset, cancellation and error ownership
//! with both crate roots and backend orchestration. Do not duplicate configuration translation.
//!
//! Status: facade skeleton; verification pipeline is not implemented.

/// Symbolic execution backend modules under active translation.
pub use ferrum_silicon as silicon;
/// Shared language infrastructure for callers constructing a Silver program.
pub use ferrum_silver as silver;

/// An explicit integration gap; this is never a successful verification result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortIncomplete {
    pub component: &'static str,
}

impl std::fmt::Display for PortIncomplete {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ferrum port incomplete: {}", self.component)
    }
}

impl std::error::Error for PortIncomplete {}

/// The CLI uses this until the real frontend and verification engine are connected.
pub fn verify_file(_path: &std::path::Path) -> Result<(), PortIncomplete> {
    Err(PortIncomplete {
        component: "frontend and verification pipeline",
    })
}
