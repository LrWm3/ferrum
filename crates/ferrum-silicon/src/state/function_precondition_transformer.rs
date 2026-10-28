//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/FunctionPreconditionTransformer.scala
//!
//! Purpose:
//! Construct well-definedness conditions for heap-dependent function applications.
//!
//! Planned Rust structure:
//! FunctionPreconditionTransformer.transform dispatches literals, short-circuit boolean
//! operators, conditionals, lets, quantifiers, applications and generic subterms.
//!
//! Behavior to preserve:
//! Guard right-hand transformations of And, Or and Implies; transform let bindings and
//! body; quantified well-definedness is universally quantified even for existential input,
//! retaining triggers and metadata; heap-dependent applications add preconditionVersion
//! after argument transforms.
//!
//! Integration:
//! state::terms, rules::function_supporter and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Term traversal and function supporter interface.
//!
//! Status: description only; implementation has not started.
