//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/structural/BranchingRecord.scala
//!
//! Purpose:
//! Track ordered symbolic execution branches and reachability.
//!
//! Planned Rust structure:
//! Port BranchingRecord condition/conditionExp, current index and BranchInfo
//! records/reachable/startTime, plus append, switch and query helpers.
//!
//! Behavior to preserve:
//! Allocate requested number of branches, mark current branch reachable with start time, append in
//! order and assert index bounds; display condition or null.
//!
//! Integration:
//! logger::symb_ex_logger, logger::renderer::simple_tree_renderer and writer; state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered branch records and term identity.
//!
//! Open decisions:
//! Agree on branch ownership and timing with concurrent logger.
//!
//! Status: description only; implementation has not started.
