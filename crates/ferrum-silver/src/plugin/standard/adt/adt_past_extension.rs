//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtPASTExtension.scala
//!
//! Purpose:
//! Represent, resolve, typecheck and translate ADT syntax in the parse tree.
//!
//! Planned Rust structure:
//! Port PAdt, constructors/fields/derives, PAdtType and kind, PAdtOpApp and
//! constructor/destructor/discriminator calls with typechecking, substitution and translation.
//!
//! Behavior to preserve:
//! Check constructor argument types and discriminator name clashes, duplicate derivations and
//! without-field membership. Resolve ADT type arity and undefined/ambiguous references. Refresh
//! ADT type variables, unify operator signatures and force grounded substitutions before
//! translating calls; preserve member-signature-before-body construction and metadata.
//!
//! Integration:
//! adt_plugin rewrites parse nodes; parser::resolver/translator, adt_ast_extension and ast
//! rewriter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parse node identity, mutation and type substitutions.
//!
//! Open decisions:
//! Agree on ADT declaration lookup and mutable inference state with parser and AST.
//!
//! Status: description only; implementation has not started.
