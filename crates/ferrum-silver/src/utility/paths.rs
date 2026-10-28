//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Paths.scala
//!
//! Purpose:
//! Provide path, resource URL and environment expansion helpers.
//!
//! Planned Rust structure:
//! Port Paths resolveEnvVars, pathFromResource, canonize and isInSubDirectory; replace JVM
//! resource filesystem management.
//!
//! Behavior to preserve:
//! Only substitute existing ${ENV} variables; support file, jar and resource schemes upstream,
//! retain resource filesystem lifetime/reuse, reject other schemes. Canonize joins relative paths
//! to working directory; directory containment walks parents, including equality.
//!
//! Integration:
//! Resource consumers and ast::utility file loading depend on accessible paths.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Decide native packaged-resource representation and lifetime with resource and file-loader
//! modules.
//!
//! Status: description only; implementation has not started.
