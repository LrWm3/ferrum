//! Port plan: Shared node traversal, metadata, scope and diagnostic back-transformation contracts.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Ast.scala
//!
//! Purpose:
//! Shared node traversal, metadata, scope and diagnostic back-transformation contracts.
//!
//! Planned Rust structure:
//! Node exposes subnodes, reductions, visits, collection, replacement and strategy-based transforms;
//! retain Hashable collaborators and metadata-bearing traits Positioned, Infoed, Typed, Declaration and
//! Scope.
//! Model Info variants NoInfo, SourcePNodeInfo, AnnotationInfo, SimpleInfo, AutoTriggered,
//! WeightedQuantifier, Cached, Synthesized, FailureExpectedInfo, ConsInfo and MakeInfoPair; model
//! ErrorTrafo variants and TransformableErrors.
//!
//! Behavior to preserve:
//! Node traversal and transitive checks include ordered children; default metadata is
//! NoPosition/NoInfo/NoTrafos. Error and reason transformations fold right, then repeatedly
//! back-transform offending nodes; combining trafos concatenates transformations and prefers the right
//! node. Info pairs drop NoInfo, concatenate comments, OR cache flags, and recursively find/remove
//! typed entries. Scope includes nested scoped declarations.
//!
//! Integration:
//! Coordinate ast::utility::{nodes,visitor,viper_strategy,rewriter},
//! ast::{program,position,pretty::pretty_printer}, parser and verifier::verification_error::errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Node extension and typed metadata/back-transformation ownership require agreement with the rewriter,
//! diagnostics and plugins; preserve case-class structural equality fields without treating metadata as
//! ordinary product fields.
//!
//! Status: description only; implementation has not started.
