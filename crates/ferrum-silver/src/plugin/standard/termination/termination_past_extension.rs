//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationPASTExtension.scala
//!
//! Purpose:
//! Represent decreases syntax and resolve its types before AST translation.
//!
//! Planned Rust structure:
//! Port PDecreasesKeyword, PIfKeyword, PWildcardSym, PDecreasesClause and tuple/wildcard/star
//! variants with typecheck and translateExp.
//!
//! Behavior to preserve:
//! Clause is Bool with identity substitution; conditions are checked Bool and tuple expressions
//! checked without a required type. Translate corresponding AST clause with position; star has no
//! condition.
//!
//! Integration:
//! termination_plugin supplies grammar; parser::resolver and translator;
//! termination_ast_extension.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions, type inference and positions.
//!
//! Open decisions:
//! Reconcile extension dispatch and position ownership with parser and AST.
//!
//! Status: description only; implementation has not started.
