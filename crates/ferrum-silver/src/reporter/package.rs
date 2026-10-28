//! Port plan: Provide reporting aliases and source symbol definitions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/package.scala
//!
//! Purpose:
//! Provide reporting aliases and source symbol definitions.
//!
//! Planned Rust structure:
//! Time, File, Entity, DefPosition/DefScope/ViperType, SymbolKind and TypedSymbol variants,
//! Definition and Import; print entity helper.
//!
//! Behavior to preserve:
//! Entity printing replaces newlines and collapses whitespace. Preserve symbol kind display names,
//! typed payloads, optional scope and import origin.
//!
//! Integration:
//! reporter::{message,reporter}, ast::{program,type,position} and frontend definition reporting.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Agree on member handles and file/scope ownership with frontend and reporter consumers.
//!
//! Status: description only; implementation has not started.
