//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/NonQuantifiedPropertyInterpreter.scala
//!
//! Purpose:
//! Instantiate resource properties over ordinary and singleton quantified heap chunks.
//!
//! Planned Rust structure:
//! Port NonQuantifiedPropertyInterpreter, placeholder Info map, chunk/resource entry points,
//! accessors, solver Check and recursive ForEach.
//!
//! Behavior to preserve:
//! Select nonquantified and singleton quantified chunks, substitute singleton arguments in
//! permissions/values. ForEach groups by resource and chunk ID, enumerates distinct chunk
//! identities, conjoins results; reject ForEach when This is bound. Check uses decider with
//! configured timeout and chooses one branch. Preserve debug expressions and traversal order.
//!
//! Integration:
//! resources::property_interpreter, state chunk interfaces, verifier::verifier and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, solver access and debug metadata.
//!
//! Open decisions:
//! Agree on heap iteration, reference identity and singleton chunk handling with state and
//! decider.
//!
//! Status: description only; implementation has not started.
