//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFPAstExtensions.scala
//!
//! Purpose:
//! Typecheck and translate low, lowEvent and rel parse expressions.
//!
//! Planned Rust structure:
//! Port PLowExp, PLowEventExp and PRelExp typechecking, substitution and translateExp hooks.
//!
//! Behavior to preserve:
//! low and lowEvent are Bool accepted as Bool or Impure; low checks operand without expected type.
//! rel checks its operand and integer index, permits only 0 or 1, and matches expected operand
//! type. Preserve positions and substitution behavior.
//!
//! Integration:
//! sif_plugin grammar, parser::resolver/translator and sif_ast_extensions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable parse AST, types and positions.
//!
//! Open decisions:
//! Agree on extension typechecking and substitution representation with parser.
//!
//! Status: description only; implementation has not started.
