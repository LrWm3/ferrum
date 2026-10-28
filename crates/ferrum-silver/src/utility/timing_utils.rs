//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/TimingUtils.scala
//!
//! Purpose:
//! Format and measure elapsed milliseconds.
//!
//! Planned Rust structure:
//! Port TimingUtils formatTimeForTable, formatTime and time closure helper.
//!
//! Behavior to preserve:
//! Use seconds with two decimals only when millis > 1000; otherwise milliseconds, including table
//! widths and suffix spacing. Return closure result with elapsed milliseconds.
//!
//! Integration:
//! Frontend and reporting timing callers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose clock abstraction with frontend timing while preserving observable formatting.
//!
//! Status: description only; implementation has not started.
