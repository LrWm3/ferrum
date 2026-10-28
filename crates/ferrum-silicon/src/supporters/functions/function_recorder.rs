//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionRecorder.scala
//!
//! Purpose:
//! Record symbolic snapshots and fresh definitions during function or predicate verification.
//!
//! Planned Rust structure:
//! Port FunctionRecorder, ActualFunctionRecorder, NoopFunctionRecorder,
//! LetContext/QuantifierContext and guarded snapshot merge/toTerm.
//!
//! Behavior to preserve:
//! Record location/function application snapshots only at depth 0; fresh
//! map/inverse/constraint/path symbols at depth <=2, snapshots <=3 and macros <=1. Preserve
//! context stack checks, insertion-ordered guard sets and recursive ITE reconstruction; merge
//! snapshots at depth 0 and other records at depth <=1, leaving deeper recorder unchanged. Noop
//! merge requires same type.
//!
//! Integration:
//! functions::function_data and heap_access_replacing_expression_translator; rules
//! evaluator/producer/consumer and predicate_verification_unit.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branch-independent records, identity, guarded ordering and
//! symbolic terms.
//!
//! Open decisions:
//! Agree on key equality for AST/context and merge ownership with evaluator and FunctionData.
//!
//! Status: description only; implementation has not started.
