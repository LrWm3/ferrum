//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/NameGenerator.scala
//!
//! Purpose:
//! Generate valid and unique identifiers in nested scopes.
//!
//! Planned Rust structure:
//! Port NameGenerator, DefaultNameGenerator and mutable NameContext, including identifier
//! conversion, counters and subcontexts.
//!
//! Behavior to preserve:
//! Greek and operator substitutions are explicit; invalid characters are removed, default prefix
//! applied where needed and reserved names repeatedly prefixed. Unique names check ancestors and
//! descendants, while siblings may overlap; increment counters and skip existing suffixed names.
//!
//! Integration:
//! utility::sil_name_generator supplies Silver syntax and ast::utility::consistency reserved
//! names.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on owned context tree and mutation/thread-safety with name generator consumers.
//!
//! Status: description only; implementation has not started.
