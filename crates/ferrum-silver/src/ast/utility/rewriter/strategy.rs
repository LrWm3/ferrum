//! Port plan: Generic rewriting, context and strategy composition.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/Strategy.scala
//!
//! Purpose:
//! Generic rewriting, context and strategy composition.
//!
//! Planned Rust structure:
//! Traverse, StrategyInterface, StrategyBuilder, SlimStrategy/Strategy, ConcatenatedStrategy,
//! RepeatedStrategy, context/partial-context variants, StrategyVisitor, Query and
//! Rule/Append/CondAppend/Ternary.
//!
//! Behavior to preserve:
//! TopDown applies before children, BottomUp after reconstruction, Innermost stops descent
//! after identity-changing rewrite; noRec is identity-based, with optional child selection and
//! force copy. Recurse through maps, options, tuples, eithers and iterables. Repetition stops
//! when unchanged and asserts before 10000 iterations; context tracks ancestors/siblings and
//! custom values. Outermost is declared but selectStrat has no matching dispatch branch;
//! investigate before choosing behavior.
//!
//! Integration:
//! ast::utility::{viper_strategy,rewriter::{rewritable,regex_strategy}}, parser and plugin
//! transformations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Coordinate node identity, reconstruction and metadata hook behavior with rewritable and
//! viper_strategy; resolve unsupported Outermost against callers.
//!
//! Status: description only; implementation has not started.
