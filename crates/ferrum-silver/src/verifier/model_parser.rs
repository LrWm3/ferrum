//! Port plan: Parse solver model text into Silver model entries.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/ModelParser.scala
//!
//! Purpose:
//! Parse solver model text into Silver model entries.
//!
//! Planned Rust structure:
//! ModelParser.model, modelEntry, identifier, mapping/options/default, value/let/binding and
//! entries2Model.
//!
//! Behavior to preserve:
//! Do not consume newline after arrow when parsing an optional definition: missing value becomes
//! UnspecifiedEntry. Parse map options and optional else/default, nested applications and let
//! bindings with left-to-right substitution. Repeated map entries merge options but keep existing
//! default; non-map entries replace. Parse full input and preserve reserved-word restrictions.
//!
//! Integration:
//! verifier::verification_error defines Model and entry variants; parser whitespace and Silicon
//! counterexample consumers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Choose native parser and ordered map representation with error reporting consistent with
//! Model::apply and existing callers.
//!
//! Status: description only; implementation has not started.
