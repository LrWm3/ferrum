//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtPlugin.scala
//!
//! Purpose:
//! Register ADT syntax, identify ADT uses and invoke domain encoding.
//!
//! Planned Rust structure:
//! Port AdtPlugin grammar for declarations, constructors and derives/without; beforeParse,
//! beforeResolve and beforeVerify with derivesImported and termination-option state.
//!
//! Behavior to preserve:
//! Disabled plugin leaves input unchanged. Register grammar only on main input; detect derives
//! import in any source. Before resolution rewrite ADT types, constructor calls, destructors and
//! discriminators using declared names, while preserving field-assignment targets for ordinary
//! resolution; drop derives when resource import absent. Encode before verification with
//! well-foundedness conditional on active termination plugin and configuration.
//!
//! Integration:
//! parser::fast_parser/resolver; adt_past_extension, encoding::adt_encoder,
//! frontend::sil_front_end_config and termination plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for native parser/plugin registration and contextual rewriting.
//!
//! Open decisions:
//! Reconcile per-run derivesImported lifetime and plugin ordering with frontend and parser.
//!
//! Status: description only; implementation has not started.
