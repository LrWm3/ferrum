//! Port plan: Silver expression hierarchy, typing, local checks, resource access and
//! expression-specific helpers.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Expression.scala
//!
//! Purpose:
//! Silver expression hierarchy, typing, local checks, resource access and expression-specific helpers.
//!
//! Planned Rust structure:
//! Represent Exp and operation/trigger traits, literals and arithmetic/comparison/Boolean nodes;
//! permissions and access predicates; MagicWand, inhale-exhale, function/domain/backend calls and
//! field/predicate access.
//! Include conditional, unfolding/applying/asserting, old/labelled old, let, quantifiers and Trigger,
//! local/result/versioned variables; sequence (empty, explicit, range, append, index, take/drop,
//! contains, update, length), set/multiset (empty, explicit, union, intersection, subset, minus,
//! contains, cardinality) and map (empty, explicit, maplet, update, lookup, contains, cardinality,
//! domain/range) families; ExtensionExp and operator support.
//!
//! Behavior to preserve:
//! Retain node-specific type and purity checks, defaults and diagnostic positions, including default
//! full permission and distinct inhale/exhale interpretations. Expressions carry lazy purity, conjuncts
//! and simplified cache; direct string conversion removes newlines. Wands are simultaneously resource,
//! access and predicate: collect heap-independent unbound holes, canonicalize bound variables and
//! optional unique hole names, and reject ForPerm or impure forall in either side. Quantifiers require
//! nonempty variables and trigger coverage; forall checks quantified-permission form and nested impure
//! quantifiers, while exists requires a pure body. Auto-trigger only when absent and mark generated
//! triggers with AutoTriggered. Explicit sequences require nonempty equal-typed elements and desugar
//! left-to-right into singleton appends. Preserve collection typing and name-based lookups. RefLit and
//! BackendValueLit are counterexample-only.
//!
//! Integration:
//! Uses ast::{ast,program,type,position,pretty::pretty_printer},
//! ast::utility::{expressions,consistency,quantified_permissions,rewriter}, verifier; consumed by
//! parser, plugins and Silicon rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile extension dispatch, lazy caches, node equality and bound-variable/AST handle ownership
//! with ast::ast, utility::rewriter and downstream symbolic evaluation.
//!
//! Status: description only; implementation has not started.
