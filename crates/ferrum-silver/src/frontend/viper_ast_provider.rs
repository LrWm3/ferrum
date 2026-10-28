//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperAstProvider.scala
//!
//! Purpose:
//! Produce a checked Silver AST without backend verification.
//!
//! Planned Rust structure:
//! Represent ViperAstProvider, Config and AstProvidingVerifier; specialize phase list, result,
//! finish, verifier creation and optional disabled-plugin manager.
//!
//! Behavior to preserve:
//! Run parsing, analysis, translation and consistency only; success requires a program and
//! consistency state. Report AST construction result; disabled plugins use an empty manager on
//! reset. The stub verifier succeeds but is not a verification phase.
//!
//! Integration:
//! frontend::sil_frontend, parser and reporter::message; reformatter_ast_provider specializes
//! this provider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and plugin manager lifetime with sil_frontend.
//!
//! Status: description only; implementation has not started.
