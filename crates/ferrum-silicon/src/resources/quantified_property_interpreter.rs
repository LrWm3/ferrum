//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/QuantifiedPropertyInterpreter.scala
//!
//! Purpose:
//! Instantiate an instance property as a quantified condition over a quantified chunk.
//!
//! Planned Rust structure:
//! Port QuantifiedPropertyInterpreter Info, buildPathConditionForChunk, accessors, Check and
//! ForEach overrides.
//!
//! Behavior to preserve:
//! Substitute quantified chunk variables with supplied arguments, generate forall with supplied
//! triggers and qid prefix/property name. Guard by condition only when arguments or value were
//! accessed; reset argsUsed after each build. Check becomes ITE and ForEach is unsupported. Debug
//! value access is unimplemented upstream.
//!
//! Integration:
//! resources::property_interpreter, interfaces::state quantified chunks, state::terms and Silver
//! debug AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for quantifier triggers, explicit mutable context and debugging.
//!
//! Open decisions:
//! Resolve unsupported debug value access and argsUsed ownership with quantified chunk producers
//! and verifier.
//!
//! Status: description only; implementation has not started.
