//! Port plan: SiliconTestsMaskHeapMode.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsMaskHeapMode.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsMaskHeapMode inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run all/{basic,functions,inhale_exhale,old,permissions}, examples, quantifiedpredicates/basic,
//! quantifiedcombinations and wands/{mwsf,examples} with --timeout 300 --maskHeapMode.
//! quantifiedpermissions/sets is commented out.
//!
//! Integration:
//! silicon_tests, mask heap rules and fixture corpus.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve included and excluded subset, not broader inferred coverage.
//!
//! Status: description only; implementation has not started.
