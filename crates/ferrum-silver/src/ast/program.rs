//! Port plan: Program declarations, resources, built-in operators and program-wide consistency.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Program.scala
//!
//! Purpose:
//! Program declarations, resources, built-in operators and program-wide consistency.
//!
//! Planned Rust structure:
//! Model Program, Hashable, Field, Predicate, Method, Function, local declarations, Domain, DomainFunc,
//! named/anonymous DomainAxiom and Substitution. Preserve Member, DomainMember, Callable, FuncLike,
//! Contracted, Resource, Location, AbstractDomainFunc and ExtensionMember interfaces.
//! Include built-in integer, Boolean and permission operator families and BackendFunc.
//!
//! Behavior to preserve:
//! Keep ordered member lists and name-based lookup across cyclic call relationships; strict lookup
//! fails when absent. Name validation tracks nested scopes and checks duplicate declarations, while
//! domain function scopes start empty. Check calls against argument and return types, abstract
//! predicate fold/unfold, and ordered program-level diagnostics; preserve local and transitive
//! consistency checks, declaration scoping, abstract predicate usage restrictions, contracts and
//! optional bodies. Missing method bodies have a bodyOrAssumeFalse helper containing inhale false.
//! Retain program-dependent hashing and operator signatures/precedence, domain substitutions and
//! interpretation fields; metadata does not automatically belong to structural equality.
//!
//! Integration:
//! Used throughout ast::{expression,statement,type,pretty::pretty_printer}, ast::utility
//! consistency/domain/visitor routines, parser translation, CFG generation and Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile program-aware hash/equality, lookup lifetime, substitution and plugin extension ownership
//! with ast::ast, rewriter and Silicon consumers.
//!
//! Status: description only; implementation has not started.
