//! Port plan: MethodDependencyTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/MethodDependencyTests.scala
//!
//! Purpose:
//! Port the upstream MethodDependencyTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! MethodDependencyTests with explicit dependency graph and recursion fixture.
//!
//! Behavior to preserve:
//! Assert all fields/domains are global dependencies, plus method pre/post/body and transitive
//! function/predicate dependencies; exclude unrelated functions/predicates and callee bodies, and
//! reject duplicates. Mutual recursion across functions/predicates/methods terminates without
//! stack overflow and yields the specified dependency set.
//!
//! Integration:
//! ast::program and utility dependency/hash analysis.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile member-vs-spec dependency boundaries and ordering with cache helper.
//!
//! Status: description only; implementation has not started.
