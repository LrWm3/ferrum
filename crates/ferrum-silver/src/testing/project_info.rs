//! Port plan: Carry project names for shared test infrastructure.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/testing/ProjectInfo.scala
//!
//! Purpose:
//! Carry project names for shared test infrastructure.
//!
//! Planned Rust structure:
//! ProjectInfo.projectNames, fullName and update.
//!
//! Behavior to preserve:
//! fullName joins names with hyphens; update prepends a new name and returns a new instance.
//!
//! Integration:
//! testing harness and downstream backend suite setup.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Agree on test harness configuration and naming with upstream suite ports.
//!
//! Status: description only; implementation has not started.
