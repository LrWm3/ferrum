//! Port plan: Adapt generic rewrite strategies to Silver AST metadata and error backtranslation.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/ViperStrategy.scala
//!
//! Purpose:
//! Adapt generic rewrite strategies to Silver AST metadata and error backtranslation.
//!
//! Planned Rust structure:
//! ViperStrategy, ViperRegexStrategy, SlimViperRegexStrategy, corresponding regex builders and
//! Slim/Ancestor/Context/CustomContext/Regex factories, plus preserveMetaData.
//!
//! Behavior to preserve:
//! When an ErrorNode is replaced, inherit old metadata only when all new metadata is default.
//! For changed nodes add old-node backtranslation only for direct rewrites and only if none
//! already exists; copied parents preserve existing transformations. Identity determines
//! whether nodes differ.
//!
//! Integration:
//! ast::{ast,expression}, ast::utility::rewriter::{strategy,regex_strategy,t_regex} and
//! verifier::errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile metadata propagation invocation with generic Strategy and regex engine; preserve
//! distinction between copied parents and direct rewrites.
//!
//! Status: description only; implementation has not started.
