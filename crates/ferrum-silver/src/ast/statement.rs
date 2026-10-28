//! Port plan: Verification statements, scope, metadata and local consistency checks.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Statement.scala
//!
//! Purpose:
//! Verification statements, scope, metadata and local consistency checks.
//!
//! Planned Rust structure:
//! Represent Stmt and AbstractAssign with LocalVarAssign/FieldAssign, NewStmt, MethodCall,
//! Exhale/Inhale/Assert/Assume, Fold/Unfold, Package/Apply, Seqn, If/While, Label/Goto,
//! LocalVarDeclStmt, Quasihavoc/Quasihavocall and ExtensionStmt.
//!
//! Behavior to preserve:
//! Preserve check order and error locations for forbidden Result, purity, assignability, Boolean
//! conditions/assertions, duplicate call targets, wand type and loop contracts. Assume has its own
//! narrower check. Seqn includes plugin declarations in parent scope; quantified havoc scopes its
//! variables. CFG conversion retains simplify/detect flags; written and undeclared variables delegate
//! to utilities.
//!
//! Integration:
//! Uses ast::{expression,program,ast}, ast::utility::{consistency,statements},
//! cfg::silver::cfg_generator and verifier consistency errors; plugin statements extend this surface.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Agree on extension dispatch and declaration/statement handles with AST visitors, CFG generator and
//! plugin transformations.
//!
//! Status: description only; implementation has not started.
