//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/BuiltinDomainsContributor.scala
//!
//! Purpose:
//! Load, instantiate and emit builtin collection domain axioms.
//!
//! Planned Rust structure:
//! Port BuiltinDomainsContributor and BuiltinDomainAwareSymbolConverter with analyze, source
//! transformations, sort/function/axiom collection, lifecycle and shared source-program cache.
//!
//! Behavior to preserve:
//! Skip source loading when no ground instances. Select user file or default resource;
//! parse/resolve/translate and cache by URL plus file modification time. Instantiate source
//! functions/axioms, retain insertion-ordered deduplication, skip interpreted functions, translate
//! builtin equality and prefix quantifier names, then declare sorts/symbols and assume axioms.
//!
//! Integration:
//! supporters::domains and default collection contributors, interfaces::preamble,
//! state::symbol_converter, Silver parser and prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered collections and native resource/cache ownership;
//! preserve .vpr resources.
//!
//! Open decisions:
//! Resolve cache synchronization, source loading and failure propagation with verifier and
//! frontend.
//!
//! Status: description only; implementation has not started.
