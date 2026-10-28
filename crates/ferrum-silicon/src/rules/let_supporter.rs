//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/LetSupporter.scala
//!
//! Purpose:
//! Evaluate nested let expressions and return bound store to the caller.
//!
//! Planned Rust structure:
//! LetSupportRules and letSupporter.handle overloads recursively evaluate each binding with
//! evaluator; extend store and collect bindings before passing final body and Store to Q.
//!
//! Behavior to preserve:
//! Evaluate bindings left to right with each prior binding in scope; non-let input invokes Q with
//! an empty store. Evaluation failure prevents Q; restoration belongs to callers.
//!
//! Integration:
//! rules::evaluator, rules::consumer, rules::producer and state::store.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Typed expression and continuation interfaces.
//!
//! Status: description only; implementation has not started.
