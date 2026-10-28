//! Port plan: Silver trigger generation and axiom rewriting adapters.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Triggers.scala
//!
//! Purpose:
//! Specialize generic trigger generation and arithmetic rewriting for Silver expressions.
//!
//! Planned Rust structure:
//! TriggerGeneration, DefaultTriggerGeneration, TriggerGenerationWithAddAndSubtract,
//! AxiomRewriter and SimpleArithmeticSolver; bridge expression traversal, arguments,
//! quantifier variables, fresh variables and constructors to generic utility interfaces.
//!
//! Behavior to preserve:
//! Custom filters precede defaults; extension expressions and old-wrapped possible
//! triggers have special handling. Rewrap inferred terms under old/labelled old;
//! inline let bindings only when permitted, account for variables in the bound value,
//! and exclude nested bound variables. The alternate generator permits Add and Sub.
//! Rewriter copies Forall/Exists with metadata, uses __rw_ fresh names, and rejects
//! other quantifier shapes. Shared generator filter mutation is not thread-safe.
//!
//! Integration:
//! Connect ast::{expression,program}, ast::utility::{expressions,visitor,
//! generic_trigger_generator,generic_axiom_rewriter,generic_arithmetic_solver} and
//! quantifier clients in Silver and Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering and explicit ownership;
//! interfaces and generator ownership remain provisional.
//!
//! Open decisions:
//! Reconcile fresh counters and mutable filters with generic generator and concurrent
//! verification; preserve extension trigger hooks and quantifier metadata.
//!
//! Status: description only; implementation has not started.
