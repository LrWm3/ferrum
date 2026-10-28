//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ReformatterAstProvider.scala
//!
//! Purpose:
//! Expose parse-only AST construction for reformatting.
//!
//! Planned Rust structure:
//! Provide ReformatterAstProvider over ViperAstProvider, overriding phase list, parsing and
//! result.
//!
//! Behavior to preserve:
//! Run only parsing with macro expansion disabled; return Success after Parsing when no errors,
//! otherwise Failure.
//!
//! Integration:
//! frontend::viper_ast_provider and parser::fast_parser feed parser::reformat_pretty_printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on reuse/composition with viper_ast_provider.
//!
//! Status: description only; implementation has not started.
