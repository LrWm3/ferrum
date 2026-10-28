//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperPAstProvider.scala
//!
//! Purpose:
//! Provide a parsed and semantically analyzed parse AST without translating or verifying.
//!
//! Planned Rust structure:
//! Represent ViperPAstProvider, Config and PAstProvidingVerifier; override phase list, result,
//! creation and plugin selection.
//!
//! Behavior to preserve:
//! Run Parsing then SemanticAnalysis only; require semantic state for success and return recorded
//! errors otherwise. Disabled plugins select empty manager after reset.
//!
//! Integration:
//! frontend::sil_frontend, parser::parse_ast and reporter/verifier interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and shared plugin lifetime with viper_ast_provider.
//!
//! Status: description only; implementation has not started.
