//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFExtendedTransformer.scala
//!
//! Purpose:
//! Translate relational SIF programs into a two-execution product program.
//!
//! Planned Rust structure:
//! Port Config, NameTransformer, transform, relational-predicate dependency closure and
//! field/domain/function/predicate/method translation; TranslationContext and
//! MethodControlFlowVars; expression/assertion, statement, loop, try/catch, lowness and helper
//! groups.
//!
//! Behavior to preserve:
//! Clear primedNames, used names, fields and predicates per transform, then rebuild relational
//! predicate closure in both dependency directions. Other singleton state, including
//! primedNamesPerMethod, configured replacements and domainFuncsToDuplicate, is not cleared
//! there. Duplicate fields, heap-dependent functions and predicates, and report unsupported
//! relational domain/function assertions. Preserve options for control-flow and sequential
//! optimization, restriction of active variables, selective methods, all-low functions,
//! experimental rel/goto, Nagini adaptations, timing and callbacks. Duplicate method
//! inputs/outputs, translate pre/postconditions and termination channels, and preserve
//! active-execution flags. Translate assignments, calls, allocation, branches, assertions,
//! inhale/exhale, fold/unfold, refute and control-flow extensions in source order; loops retain
//! bypass, idle, target-preservation and reconstruction logic, and try/finally saves and restores
//! control flags. Translate relational low/event/exit, quantifiers, dynamic checks and predicate
//! low functions with original versus primed expressions and backtransformed errors. Preserve
//! unsupported-feature reports and source-specific naming/triggers.
//!
//! Integration:
//! plugin::sif::{sif_ast_extensions,sif_error,sif_plugin},
//! plugin::standard::{predicateinstance,refute}, ast::utility::{simplifier,rewriter} and
//! verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for product-state independence, ordered collections, metadata and
//! explicit contexts; JVM singleton state replacement remains provisional.
//!
//! Open decisions:
//! Reconcile configuration lifetime and resets, source graph/set ordering, loop-reconstruction
//! assumptions and primed-name scope with SIF consumers and AST; do not silently repair upstream
//! TODOs.
//!
//! Status: description only; implementation has not started.
