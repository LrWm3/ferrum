//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ErrorTrafoFactory.scala
//!
//! Purpose:
//! Map failed generated assertions to termination-specific reasons.
//!
//! Planned Rust structure:
//! Port AbstractReasonTrafoFactory and ReasonTrafoFactory with termination condition, tuple
//! condition, simple, decreases and bounded reason constructors.
//!
//! Behavior to preserve:
//! Transform AssertionFalse into the corresponding reason at the selected offending node; retain
//! default node behavior.
//!
//! Integration:
//! decreases_check, function_check, method_check and termination_errors; ast error/reason trafos.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for error transformations and source attribution.
//!
//! Open decisions:
//! Agree on composable reason transform ownership with ast and verifier.
//!
//! Status: description only; implementation has not started.
