//! Port plan: ReformatterTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ReformatterTests.scala
//!
//! Purpose:
//! Port the upstream ReformatterTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ReformatterTests.Provider and check_inner fixture comparison.
//!
//! Behavior to preserve:
//! Read reformatter/<name>.vpr and <name>_expected.vpr; parse and compare exact reformatted text
//! for adts, annotations, domains, expressions, fields, functions, macros, methods, predicates,
//! trailing_comment and not_working.
//!
//! Integration:
//! parser::reformat_pretty_printer, frontend reformatter and ast::utility::file_loader.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Keep whitespace-sensitive expected files and loader failures visible.
//!
//! Status: description only; implementation has not started.
