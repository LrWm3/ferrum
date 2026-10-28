//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Caching.scala
//!
//! Purpose:
//! Collect method dependencies and derive cache entity hashes.
//!
//! Planned Rust structure:
//! Port DependencyAware getDependencies and recursive marking, plus CacheHelper buildHash and
//! computeEntityHash with domain orderings.
//!
//! Behavior to preserve:
//! Include method, all domains and fields; follow calls through contracts and function/predicate
//! bodies with visited sub-AST markers. Normalize domain functions and axioms by pretty output
//! for hashing; preserve MD5 byte/string conversion and prefix/type name behavior. Its
//! conservative but imperfect dependencies affect soundness.
//!
//! Integration:
//! ast declarations, expressions, traversal and ast::pretty::pretty_printer; verifier caching
//! clients.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Resolve stable cross-runtime cache serialization and hashing with AST equality and cache
//! consumers.
//!
//! Status: description only; implementation has not started.
