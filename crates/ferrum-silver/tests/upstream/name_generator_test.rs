//! Port plan: NameGeneratorTest.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/NameGeneratorTest.scala
//!
//! Purpose:
//! Port the upstream NameGeneratorTest.scala test or test-harness component.
//!
//! Planned Rust structure:
//! NameGeneratorTest with nested and sibling contexts.
//!
//! Behavior to preserve:
//! Check sanitization of empty/invalid/reserved names, replacement of punctuation and deleted
//! characters; unique foo, foo_1 etc.; enclosing/subcontext shared counters, independent siblings,
//! partially independent contexts and pre-reserved counter suffixes.
//!
//! Integration:
//! utility::{name_generator,sil_name_generator} and parser identifier restrictions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Keep scoped allocation and exact generated names across nested contexts.
//!
//! Status: description only; implementation has not started.
