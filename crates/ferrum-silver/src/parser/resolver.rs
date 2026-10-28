//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/Resolver.scala
//!
//! Purpose:
//! Resolve names and typecheck parse AST before translation.
//!
//! Planned Rust structure:
//! Port Resolver, NameAnalyser, DeclarationMap and TypeChecker with scope collection/merge,
//! declaration and body checks, statement and expression dispatch, unification/grounding and
//! extension hooks.
//!
//! Behavior to preserve:
//! Run typechecking even after name errors, recording internal typechecker exceptions. Check
//! domain/function/method signatures before extensions and bodies; preserve visibility, backward
//! references, override/uniqueness and opaque traversal. Resolve overloaded operators by ordered
//! substitutions and ground first candidate, warning on unconstrained variables. Retain
//! permission/wand restrictions, assignment and quantifier context, and configurable function
//! permission warning.
//!
//! Integration:
//! parser::parse_ast and parse_ast_keyword, fast_message, macro_expander and translator;
//! frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Resolve stable scope identity, mutable references, substitution ordering and error context
//! with parse_ast and translator.
//!
//! Status: description only; implementation has not started.
