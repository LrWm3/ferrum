//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ParseAst.scala
//!
//! Purpose:
//! Define the mutable intermediate syntax tree shared by parsing, formatting, resolution and
//! translation.
//!
//! Planned Rust structure:
//! Represent Where, PNode/PLeaf traversal and parent/sibling properties;
//! identifiers/declarations/scopes; PType and substitutions/renaming; PExp/POpApp and literals,
//! resources, quantifiers and collections; PStmt, PProgram, members, annotations, extensions and
//! trivia. Preserve TypeHelper operations and per-variant signatures.
//!
//! Behavior to preserve:
//! Positions and syntax tokens survive parsing; initProperties sets parents, child order and
//! sibling links, while deepCopyAll reconstructs mutable nodes. Name uses accumulate declaration
//! candidates and filters; scopes have stable IDs independent of changing content. Types carry
//! mutable resolution/substitution state and fresh variables. PProgram collects local members
//! before imports and aggregates errors; reformat only local members. Keep temporary macro nodes
//! and extension hooks. PLetNestedScope exposes its binder only in the body, after the
//! initializer; binary expression equality uses operator spelling and operands, not positions.
//! Empty collection literals infer element types; access predicates default to full permission.
//!
//! Integration:
//! parser::fast_parser, resolver, macro_expander, translator, parse_ast_keyword and
//! reformat_pretty_printer; ast::utility visitors/rewriter and verifier parse reports.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on mutable node handles, stable scope identity, parent links and copy/rewrite semantics
//! with all parser modules and shared conventions.
//!
//! Status: description only; implementation has not started.
