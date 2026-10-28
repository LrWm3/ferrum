//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/MaskHeapFunctionEncoding.scala
//!
//! Purpose:
//! Encode heap-dependent functions using resource heaps and footprint-based framing.
//!
//! Planned Rust structure:
//! Port MaskHeapFunctionEncoding stateArgs/adaptAxiom, predicate triggers and application
//! translation; FrameInfo cache, frame/precondition-frame functions and
//! computeFrame/qpFrameAxioms.
//!
//! Behavior to preserve:
//! Use one heap argument per ordered precondition resource; unpack snapshot trees or HeapMapTerm,
//! distribute applications over ITE. Definitional axiom retains direct function trigger and adds
//! predicate-trigger pattern, using stateless trigger only when all quantified arguments are
//! covered, otherwise limited application. Generate value frame axiom, precondition frame only
//! when predicate triggers exist, and QP frame axioms equating condition functions when two heaps
//! agree at permitted quantified locations. Frame expressions handle accesses, conjunction,
//! implication, conditional, let and quantified permissions; preserve wildcard-to-full permission,
//! resource order and recorded QP declarations.
//!
//! Integration:
//! functions::{function_encoding,function_data,heap_access_replacing_expression_translator},
//! rules::{mask_heap_supporter,function_supporter}, state::terms and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for heap isolation, exact permission checks, trigger coverage,
//! ordered resource maps and solver declarations.
//!
//! Open decisions:
//! Reconcile FrameInfo lifetime, resource indexing and heap/snapshot aliases with mask heap rules
//! and function verification.
//!
//! Status: description only; implementation has not started.
