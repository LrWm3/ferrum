//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/Trafo.scala
//!
//! Purpose:
//! Assemble and memoize function and method termination transformations.
//!
//! Planned Rust structure:
//! Port Trafo with program, reportError, respectFuncPermAmounts and getTransformedProgram.
//!
//! Behavior to preserve:
//! Generate function proof methods first, then transform original methods; append proof methods to
//! transformed methods, preserve program metadata and cache the result.
//!
//! Integration:
//! function_check, method_check and program_manager; termination_plugin invokes it.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for contexts, ownership and configuration.
//!
//! Open decisions:
//! Agree on cached program handle and error callback lifetime with termination_plugin.
//!
//! Status: description only; implementation has not started.
