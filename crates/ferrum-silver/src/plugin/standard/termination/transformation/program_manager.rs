//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ProgramManager.scala
//!
//! Purpose:
//! Manage original program, fresh generated names and transformation errors.
//!
//! Planned Rust structure:
//! Port ProgramManager containsName/uniqueName and ErrorReporter callback.
//!
//! Behavior to preserve:
//! Seed used names from transitive scoped declarations; choose base then append 1, 2, ... and
//! reserve each generated name.
//!
//! Integration:
//! trafo, decreases_check, exp_transformer, nested_predicates and function/method checks.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable transformation context and stable names.
//!
//! Open decisions:
//! Choose program and reporter ownership shared by cooperating transformers.
//!
//! Status: description only; implementation has not started.
