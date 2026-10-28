//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationASTExtension.scala
//!
//! Purpose:
//! Represent decreases clauses and attach termination specifications to AST members and loops.
//!
//! Planned Rust structure:
//! Port DecreasesClause, DecreasesTuple, DecreasesWildcard, DecreasesStar and
//! DecreasesSpecification with condition helpers, append/fromNode, metadata and pretty printing.
//!
//! Behavior to preserve:
//! Clauses are pure Bool extensions; tuple expressions and conditions require purity. Missing
//! clause conditions mean true; termination condition is tuple/wildcard disjunction, or false when
//! neither exists. Specifications preserve tuple, wildcard and star and are not cached. Direct
//! verification is unimplemented and must be preceded by extraction.
//!
//! Integration:
//! termination_plugin extracts clauses;
//! transformation::{decreases_check,function_check,method_check}; ast metadata/consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for metadata, extension nodes and failure handling.
//!
//! Open decisions:
//! Agree on information lookup and lifetime with AST and termination transformation.
//!
//! Status: description only; implementation has not started.
