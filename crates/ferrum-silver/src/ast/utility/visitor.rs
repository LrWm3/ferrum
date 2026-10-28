//! Port plan: Generic tree visitors, queries and reductions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Visitor.scala
//!
//! Purpose:
//! Generic tree visitors, queries and reductions.
//!
//! Planned Rust structure:
//! Visitor.visit overloads, context and manual variants, visitOpt, existsDefined, hasSubnode,
//! deepCollect, shallowCollect, find, reduceTree and reduceWithContext.
//!
//! Behavior to preserve:
//! Visit is preorder; manual context stops automatic descent on a match; shallow collection
//! stops below matched nodes. deepCollect computes child results first but assembles parent
//! result before descendants. reduceWithContext passes updated context to children and
//! original context to combine. hasSubnode excludes nodes structurally equal to root.
//!
//! Integration:
//! ast::{ast,utility::nodes}, expression, consistency, chopper and many transformations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile generic callbacks, short-circuiting and structural versus identity comparisons
//! with AST and rewriter.
//!
//! Status: description only; implementation has not started.
