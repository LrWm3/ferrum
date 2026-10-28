//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/Domains.scala
//!
//! Purpose:
//! Instantiate user-defined domains and translate their axioms into prover preamble terms.
//!
//! Planned Rust structure:
//! Port DomainsContributor, DefaultDomainsContributor and
//! DomainsTranslator/DefaultDomainsTranslator, including sort, function, axiom and uniqueness
//! collections.
//!
//! Behavior to preserve:
//! Instantiate concrete ground domain types; deduplicate by translated sort/symbol, skip
//! interpreted functions and group unique nullary symbols by result sort for Distinct. Conjoin
//! function precondition transformation with each axiom; assign named quantifier IDs when missing
//! and restore builtin translation mode. Declare sorts then symbols and assume axioms/uniqueness.
//!
//! Integration:
//! supporters::expression_translator, state::{symbol_converter,function_precondition_transformer},
//! interfaces::preamble and prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered preamble emission, term identity and explicit
//! translator context.
//!
//! Open decisions:
//! Agree on translator mode lifetime and stable collection order with builtin contributor and
//! decider.
//!
//! Status: description only; implementation has not started.
