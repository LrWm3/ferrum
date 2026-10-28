//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/FastParser.scala
//!
//! Purpose:
//! Parse source into a position-bearing parse tree, recursively load imports and optionally
//! expand macros.
//!
//! Planned Rust structure:
//! Port FastParser, ParserData, RecParser, SuffixedExpressionGenerator and companion
//! lexical/trivia/grouping helpers. Organize grammar by expressions and precedence, types,
//! statements, declarations/specifications and ParserExtension hooks.
//!
//! Behavior to preserve:
//! Normalize and deduplicate local and standard import paths separately; local imports inside
//! standard imports become standard. Apply beforeParse to imports and report failures at import
//! positions. Parse full file first, then recover member by member with errors and warnings;
//! retain raw source and offsets on success. Preserve operator precedence, chained comparisons,
//! delimiters, source spans, extension order and deprecated call whitespace and Rational
//! warnings. Chained comparisons copy the middle operand into conjunctions; suffix and
//! arithmetic chains fold left, while implication and Boolean chains recurse right. Call type
//! annotations require parentheses.
//!
//! Integration:
//! parser::parse_ast, parse_ast_keyword, macro_expander; plugin parser hooks, ast::utility
//! file_loader and verifier parse reports; frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Parser strategy, extension API, position encoding and mutable parser ownership require
//! agreement with parse_ast, plugin and reformatter.
//!
//! Status: description only; implementation has not started.
