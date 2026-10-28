//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionVerificationUnit.scala
//!
//! Purpose:
//! Verify functions in phases and emit their usable axioms to prover workers.
//!
//! Planned Rust structure:
//! Port FunctionVerificationUnit and provider analysis, ordered function data, two-phase
//! verification, recording and preamble/lifecycle methods; select default or mask heap
//! FunctionEncoding.
//!
//! Behavior to preserve:
//! Order by dependency height and source order. Declare base/limited/stateless/precondition and
//! auxiliary functions. Phase 1 locally produces preconditions and fresh-snapshot postconditions
//! for well-definedness, records paths, then emits limited, trigger, auxiliary and
//! post/propagation axioms only on nonfatal result. Phase 2 restores each precondition path,
//! evaluates body, equates result and consumes posts; emit definition/body propagation only if
//! nonfatal. Respect permission and prover options, declare recorded macros last and replay
//! accumulated axioms. reset clears functionData, emitted axioms and fresh variables, but does
//! not clear postConditionAxioms; axiomsAfterVerification is an eagerly initialized val while
//! emitAxiomsAfterVerification reads the current vector. Record these reuse differences for
//! reconciliation rather than silently changing them.
//!
//! Integration:
//! functions::{function_data,function_encoding,mask_heap_function_encoding,function_recorder,heap_access_replacing_expression_translator};
//! rules::{producer,consumer,evaluator,execution_flow_controller}, state and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for continuations, solver ordering, branch-local state and
//! explicit encoding context.
//!
//! Open decisions:
//! Reconcile phase/cache reset, failure cleanup and prover option lifetime with verifier and
//! function data.
//!
//! Status: description only; implementation has not started.
