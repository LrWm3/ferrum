//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionEncoding.scala
//!
//! Purpose:
//! Define interchangeable heap-dependent function axiom and state-argument encodings.
//!
//! Planned Rust structure:
//! Port FunctionEncoding hooks and DefaultFunctionEncoding stateArgs, predicate trigger state,
//! definitional axiom and function application.
//!
//! Behavior to preserve:
//! Default passes one snapshot argument; definitions trigger directly on function application and
//! additionally on paired stateless/predicate triggers. Auxiliary symbols, axioms and
//! well-definedness declarations default empty; preserve hook ordering and substitutions.
//!
//! Integration:
//! supporters::functions::{function_data,function_verification_unit,heap_access_replacing_expression_translator}
//! and mask_heap_function_encoding; state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for snapshots, triggers and explicit verifier contexts.
//!
//! Open decisions:
//! Agree on trait ownership and state-argument/axiom interfaces with mask heap and function
//! verification.
//!
//! Status: description only; implementation has not started.
