//! Port plan: Reconstruct rewritable AST and parser nodes with extra fields.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/Rewritable.scala
//!
//! Purpose:
//! Reconstruct rewritable AST and parser nodes with extra fields.
//!
//! Planned Rust structure:
//! Rewritable.children/withChildren/withMeta/initProperties, HasExtraValList, HasExtraVars and
//! ParseTreeDuplicationError.
//!
//! Behavior to preserve:
//! Return original when children equal and copy not forced, and preserve AtomicType singleton
//! identity. Reconstruction carries special extra constructor fields for DomainType,
//! DomainAxiom, FuncApp, DomainFunc, DomainFuncApp and BackendFuncApp, generic metadata and
//! parser extra values; copy mutable extra vars. Parser reconstruction failures become
//! ParseTreeDuplicationError.
//!
//! Integration:
//! ast::{ast,program,expression,type}, parser parse nodes and
//! ast::utility::rewriter::strategy.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Replace runtime reflection with explicit reconstruction while agreeing on all extra fields,
//! metadata, singleton and identity semantics across parser and AST.
//!
//! Status: description only; implementation has not started.
