//! Port plan: Represent raw and resolved counterexamples and typed model values.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Counterexample.scala
//!
//! Purpose:
//! Represent raw and resolved counterexamples and typed model values.
//!
//! Planned Rust structure:
//! RawCounterexample, ResolvedCounterexample, CounterexampleValue, store/heap entries,
//! CEVariable/CECollection, BasicDomainEntry/BasicFunctionEntry, HeapEntryType variants and
//! Rational.
//!
//! Behavior to preserve:
//! Parse SMT negative integers, booleans and rational tokens/division exactly; preserve typed
//! fallback as BackendValueLit and references as RefLit. Resolve wand structure holes in order
//! with typed substitutions. Render store and heap entries, including quantified-permission
//! warning; normalize Rational sign and reject zero denominator. Source Rational hash uses
//! original arguments despite normalized equality: investigate compatibility.
//!
//! Integration:
//! ast::{expression,program,type}, verifier::verification_error and Silicon counterexample
//! conversion.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile collection/model order, normalized rational hashing and raw/resolved ownership with
//! Silicon and AST equality; investigate source hash inconsistency.
//!
//! Status: description only; implementation has not started.
