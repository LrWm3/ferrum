//! Port plan: Analyze and scale permission expressions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Permissions.scala
//!
//! Purpose:
//! Analyze and scale permission expressions.
//!
//! Planned Rust structure:
//! Permissions.positivityConstraints, isConditional and multiplyExpByPerm with
//! optional-permission helper.
//!
//! Behavior to preserve:
//! Require permission-typed inputs. Positivity returns no constraints for an expression
//! containing a conditional, otherwise the expression itself. FullPerm scaling returns
//! original; scale field/predicate access permission or fill absent permission, and fail on
//! MagicWand.
//!
//! Integration:
//! ast::{expression,type}, ast::utility::rewriter and callers constructing assertions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile AST transformation metadata and failure behavior with expression and rewriter
//! ports.
//!
//! Status: description only; implementation has not started.
