//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/Translator.scala
//!
//! Purpose:
//! Translate resolved parse AST to verification AST and report translation consistency failures.
//!
//! Planned Rust structure:
//! Port Translator translate, signature/member table, member/stmt/exp/ttyp dispatch,
//! methodCallAssign, havoc and annotation helpers, and position/info conversion.
//!
//! Behavior to preserve:
//! Build domain and extension signatures first, then domain functions and other signatures before
//! bodies. Preserve positions and SourcePNodeInfo/annotations; translate field call targets using
//! receiver temporaries before call and field writes afterward, reporting duplicate fields.
//! Rewrite impure assumes, desugar impure forall quantified permissions, validate forperm and
//! triggers; return None when consistency messages exist. Preserve operator/type-dependent
//! arithmetic, collections, domain substitutions and extensions.
//!
//! Integration:
//! parser::parse_ast and resolver; ast declarations, expression, statement, utility consistency
//! and quantified permissions; plugin::standard::adt and frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on signature table and AST identity, metadata, extension translation and consistency
//! message ownership with AST and plugins.
//!
//! Status: description only; implementation has not started.
