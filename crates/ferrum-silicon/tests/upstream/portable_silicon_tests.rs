//! Port plan: PortableSiliconTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/PortableSiliconTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! PortableSiliconTests extends Silver StatisticalTestSuite and is DoNotDiscover.
//!
//! Behavior to preserve:
//! Use SILICONTESTS_{REPETITIONS,WARMUP,TARGET,CSV,INCL_FILE,RANDOMIZE_Z3,TIMEOUT}; default
//! timeout 180, randomization implementation defaults false despite comment saying true. Pass
//! --disableCatchingExceptions and optional --proverRandomizeSeeds; inherited suite performs
//! warmup, repetitions and trimmed metrics. Single file required.
//!
//! Integration:
//! Silver statistical_test_suite and Silicon frontend/config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve actual defaults and non-discovery rather than documented but contradictory
//! randomization default.
//!
//! Status: description only; implementation has not started.
