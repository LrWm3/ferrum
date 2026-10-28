//! Port plan: Describe AST traversal children and referenced members.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Nodes.scala
//!
//! Purpose:
//! Describe AST traversal children and referenced members.
//!
//! Planned Rust structure:
//! Nodes.subnodes dispatch over program/member/domain-member, statement, expression, type and
//! extension families; children, memberReferencingNodes and referencedMembers.
//!
//! Behavior to preserve:
//! Preserve child order, optional permissions and type children added to every Typed node;
//! avoid treating FieldAccess field as traversed child, while NewStmt fields are children.
//! Match MagicWand before generic AccessPredicate to avoid self-recursion. children uses
//! product fields and separates node/non-node data without metadata. Referenced members
//! include method/function calls and fold/unfold/unfolding and are distinct.
//!
//! Integration:
//! ast::{ast,expression,statement,program,type},
//! ast::utility::{visitor,rewriter,quantified_permissions,chopper}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile explicit reconstruction, typed children, extension dispatch and structural
//! equality with visitor and rewriter.
//!
//! Status: description only; implementation has not started.
