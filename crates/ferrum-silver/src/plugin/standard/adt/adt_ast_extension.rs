//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtASTExtension.scala
//!
//! Purpose:
//! Represent ADT declarations, types and constructor/destructor/discriminator expressions.
//!
//! Planned Rust structure:
//! Port Adt, AdtConstructor, AdtType, AdtConstructorApp, AdtDestructorApp and AdtDiscriminatorApp,
//! constructors, custom reconstruction, pretty printing and consistency/trigger checks.
//!
//! Behavior to preserve:
//! Require at least one constructor and pure expression arguments/receivers; fill missing type
//! parameters with themselves and substitute structurally. Constructor/destructor triggers are
//! valid only without forbidden subexpressions; discriminators are forbidden. Preserve extra
//! metadata and unresolved direct verification failure until encoding.
//!
//! Integration:
//! adt_past_extension and encoding::adt_encoder; ast types, rewriter, consistency and pretty
//! printing.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for type equality, metadata, reconstruction and ownership.
//!
//! Open decisions:
//! Agree on ADT/type handles and extension elimination with ast and encoder.
//!
//! Status: description only; implementation has not started.
