//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Sanitizer.scala
//!
//! Purpose:
//! Perform capture-avoiding substitutions and optional parse-tree bound-variable sanitization.
//!
//! Planned Rust structure:
//! Port fresh, sanitizeBoundVariables and replaceFreeVariablesInExpression with their rewrite
//! contexts.
//!
//! Behavior to preserve:
//! Fresh names use $0 onward; parse sanitization renames clashing forall binders and uses
//! NameAnalyser scope, and is currently unused. Expression substitution renames clashing
//! quantified binders, asserts replacement/rename disjointness, and clears substitutions when
//! visiting a replacement. Preserve positions and metadata.
//!
//! Integration:
//! parser::resolver and parse_ast; ast::utility::rewriter and expression/declaration nodes.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on traversal/context and node reconstruction with parser and AST rewriter.
//!
//! Status: description only; implementation has not started.
