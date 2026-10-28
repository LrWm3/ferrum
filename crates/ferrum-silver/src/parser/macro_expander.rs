//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/MacroExpander.scala
//!
//! Purpose:
//! Expand global and method-local macros hygienically before resolution.
//!
//! Planned Rust structure:
//! Port MacroException, expandDefines, doExpandDefines, ReplaceContext and makeReplacer; group
//! validation, cycle detection, name hygiene, copying, replacement and sequence linearization.
//!
//! Behavior to preserve:
//! Detect duplicate/clashing names, illegal proof-script definitions, unused parameters and
//! recursive macros. Local macros precede globals; remove local definitions and flatten macro
//! sequences without introducing scope. Validate arity and syntactic position, rename clashes
//! using scope identity, deep-copy arguments and bodies, suppress substitution under binders and
//! adapt positions to call sites. Convert failures to parse errors with position fallback.
//!
//! Integration:
//! parser::parse_ast and resolver::NameAnalyser; ast::utility::rewriter, verifier parse reports
//! and fast_parser.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on parse node identity, parent context and reconstruction with parse_ast and rewriter.
//!
//! Status: description only; implementation has not started.
