//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/SmtlibNameGenerator.scala
//!
//! Purpose:
//! Sanitize solver symbols against SMT-LIB and solver reserved words.
//!
//! Planned Rust structure:
//! NameSanitizer, AbstractNameSanitizer and SmtlibNameSanitizer specify allowed initial/subsequent
//! characters, substitutions, fallback and reserved set.
//!
//! Behavior to preserve:
//! Reject empty names; map invalid characters with specific substitutions or underscore; append
//! underscores until no reserved name matches. Reserved entries are exact strings, including
//! Float[0-9]+ as a literal set member. Preserve collisions and spelling rather than silently
//! introducing uniqueness.
//!
//! Integration:
//! decider::term_to_smt_lib2_converter, state::identifiers and prover serializers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Name collision and solver-specific escaping policy.
//!
//! Status: description only; implementation has not started.
