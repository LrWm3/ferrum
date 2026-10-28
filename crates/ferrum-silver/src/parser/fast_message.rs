//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/FastMessage.scala
//!
//! Purpose:
//! Store and order parser and typechecker diagnostics.
//!
//! Planned Rust structure:
//! Represent FastMessage and FastMessaging constructors, conditional message creation and
//! sortmessages.
//!
//! Behavior to preserve:
//! Require compatible source/file positions; conditional messages use node errorPosition. Sort by
//! line then column and remove duplicates, preserving error/warning flag.
//!
//! Integration:
//! parser::parse_ast and resolver; frontend::sil_frontend maps messages to verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Reconcile position and diagnostic types with ast::position and verifier.
//!
//! Status: description only; implementation has not started.
