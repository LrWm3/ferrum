//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/DecreasesCheck.scala
//!
//! Purpose:
//! Generate conditional and lexicographic termination assertions.
//!
//! Planned Rust structure:
//! Port DecreasesCheck createConditionCheck, createTupleCheck, recursive createLexDecreaseCheck
//! and missing-function reporting.
//!
//! Behavior to preserve:
//! Missing decreasing/bounded functions produce consistency errors and EmptyStmt. Conditions use
//! !required || given to support reason transformation, simplifying true cases. Lexicographic
//! checks use decreasing(smaller,bigger) and bounded(bigger), equality and recursive tails; tuples
//! are extended by TOP, and incompatible types fail. Preserve source type substitution maps and
//! reason transformations.
//!
//! Integration:
//! program_manager, error_trafo_factory, function_check and method_check; ast domain functions and
//! verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered substitutions, metadata and diagnostics.
//!
//! Open decisions:
//! Reconcile source type-variable map and its bounded-function key choice with domain interfaces;
//! avoid silent correction.
//!
//! Status: description only; implementation has not started.
