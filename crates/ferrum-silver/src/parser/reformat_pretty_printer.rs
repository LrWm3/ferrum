//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ReformatPrettyPrinter.scala
//!
//! Purpose:
//! Reformat parse AST while preserving comments and selected original whitespace.
//!
//! Planned Rust structure:
//! Port RNode variants, RTrivia, padding traits, ReformatterContext, PrettyPrintContext and
//! ReformatPrettyPrinter showNode/showProgram/showList.
//!
//! Behavior to preserve:
//! Extract trivia between source positions once, retain trailing comments, restore newline after
//! line comments and collapse whitespace to spaces, single or double breaks. Merge pending
//! formatting whitespace with trivia, nest and group according to token pads; use width 75 and
//! indent 4.
//!
//! Integration:
//! parser::parse_ast and parse_ast_keyword, fast_parser trivia parser,
//! ast::pretty::fast_pretty_printer; frontend::reformatter_ast_provider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Reconcile source offset units and parse tree traversal with fast_parser and ast position
//! types.
//!
//! Status: description only; implementation has not started.
