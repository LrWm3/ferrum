//! Port plan: Render Silver AST and expressions as formatted Viper text.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/pretty/PrettyPrinter.scala
//!
//! Purpose:
//! Render Silver AST and expressions as formatted Viper text.
//!
//! Planned Rust structure:
//! Port Bounce/Call/Done/FlatMap trampoline, PrettyPrintPrimitives and FastPrettyPrinterBase;
//! associativity/fixity and PrettyOperatorExpression traits, BracketPrettyPrinter and FastPrettyPrinter
//! dispatch for nodes, types, members, statements and expressions.
//!
//! Behavior to preserve:
//! Preserve default width 75 and Silver indentation 2, layout grouping, nesting and width-dependent
//! breaks, operator precedence and associativity parentheses. Print metadata comments and annotations,
//! contract/decreases partitions, declarations, extension hooks, and all expression/collection forms;
//! special-case MagicWand before AccessPredicate. Domain function applications with type substitutions
//! print explicit result types. Unknown expressions fail; empty blocks and else-if chains have
//! source-specific rendering.
//!
//! Integration:
//! Uses ast::{ast,expression,statement,program,type}, termination plugin decreases clauses, and
//! extension pretty hooks; Node and Exp string conversion call it.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile document continuation/trampoline design and plugin expression/statement/member/type
//! rendering interfaces with AST and plugin ports.
//!
//! Status: description only; implementation has not started.
