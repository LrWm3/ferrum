//! Port plan: Represent proof errors, reasons and legacy solver models.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/VerificationError.scala
//!
//! Purpose:
//! Represent proof errors, reasons and legacy solver models.
//!
//! Planned Rust structure:
//! ModelEntry/ValueEntry variants, MapEntry, Model, Counterexample and transformer; ErrorMessage,
//! VerificationError, FailureContext, PartialVerificationError, AbstractVerificationError/Reason,
//! DummyNode/Reason, errors and reasons families.
//!
//! Behavior to preserve:
//! Keep distinct error IDs and reason IDs, offending node and reason, cached flag and failure
//! contexts. Include
//! assignment/call/contracts/assert/inhale/exhale/loop/fold/wand/havoc/termination/internal errors
//! and permission, null, arithmetic, bounds, injectivity, timeout and unsupported reasons.
//! Transform error node first then reason and retain contexts; special node positions and
//! counterexample wrappers matter. Model resolution accepts ordered :var constraints, rejects
//! malformed forms, and model parse failures throw.
//!
//! Integration:
//! ast::{ast,expression,statement,program},
//! verifier::{model_parser,verification_result,counterexample}, reporter and Silicon rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile error-node and callback ownership, extensibility, transformed counterexamples and
//! result boundary with AST metadata, plugins and Silicon.
//!
//! Status: partial. Model entries, concrete error/reason families and rendering
//! fragments are implemented; error wrappers, metadata transformations, failure
//! contexts, subtype-safe construction and full result integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

/// Solver model values as represented in VerificationError.scala.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueEntry {
    Unspecified,
    Constant(String),
    Application {
        name: String,
        arguments: Vec<ValueEntry>,
    },
}
impl fmt::Display for ValueEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unspecified => f.write_str("#unspecified"),
            Self::Constant(v) => f.write_str(v),
            Self::Application { name, arguments } => write!(
                f,
                "({} {})",
                name,
                arguments
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapEntry {
    pub options: HashMap<Vec<ValueEntry>, ValueEntry>,
    pub default: ValueEntry,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelEntry {
    Value(ValueEntry),
    Map(MapEntry),
}
impl fmt::Display for ModelEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(v) => v.fmt(f),
            Self::Map(m) => m.fmt(f),
        }
    }
}
impl fmt::Display for MapEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.options.is_empty() {
            write!(f, "{{\n    {}\n}}", self.default)
        } else {
            let options = self
                .options
                .iter()
                .map(|(args, value)| {
                    format!(
                        "    {} -> {}",
                        args.iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" "),
                        value
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            write!(f, "{{\n{}\n    else -> {}\n}}", options, self.default)
        }
    }
}
impl MapEntry {
    fn single(entry: &ValueEntry) -> Option<(String, ValueEntry)> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "=" && arguments.len() == 2 => {
                match &arguments[0] {
                    ValueEntry::Application {
                        name,
                        arguments: vars,
                    } if name == ":var" && vars.len() == 1 => match &vars[0] {
                        ValueEntry::Constant(i) => Some((i.clone(), arguments[1].clone())),
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }
    pub fn parse_arg_constraint_conjunction(entry: &ValueEntry) -> Option<Vec<ValueEntry>> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "and" => {
                let entries = arguments
                    .iter()
                    .map(Self::single)
                    .collect::<Option<Vec<_>>>()?;
                if entries
                    .iter()
                    .enumerate()
                    .all(|(i, (index, _))| *index == i.to_string())
                {
                    Some(entries.into_iter().map(|(_, v)| v).collect())
                } else {
                    None
                }
            }
            _ => match Self::single(entry) {
                Some((index, value)) if index == "0" => Some(vec![value]),
                _ => None,
            },
        }
    }
    pub fn parse_arg_constraint_disjunction(entry: &ValueEntry) -> Option<Vec<Vec<ValueEntry>>> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "or" => arguments
                .iter()
                .map(Self::parse_arg_constraint_conjunction)
                .collect(),
            _ => Self::parse_arg_constraint_conjunction(entry).map(|v| vec![v]),
        }
    }
    pub fn resolve_function_definition(&self) -> Self {
        if self.options.is_empty() && matches!(self.default, ValueEntry::Application { .. }) {
            if let Some(args) = Self::parse_arg_constraint_disjunction(&self.default) {
                return Self {
                    options: args
                        .into_iter()
                        .map(|a| (a, ValueEntry::Constant("true".into())))
                        .collect(),
                    default: ValueEntry::Constant("false".into()),
                };
            }
        }
        self.clone()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Model {
    pub entries: HashMap<String, ModelEntry>,
}
impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.entries
                .iter()
                .map(|(k, v)| format!("{k} -> {v}"))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
pub trait Counterexample: fmt::Debug + Send + Sync {
    fn model(&self) -> &Model;
}
#[derive(Clone, Debug)]
pub struct SimpleCounterexample {
    pub model: Model,
}
impl Counterexample for SimpleCounterexample {
    fn model(&self) -> &Model {
        &self.model
    }
}
pub type CounterexampleTransformer =
    Arc<dyn Fn(Arc<dyn Counterexample>) -> Arc<dyn Counterexample> + Send + Sync>;

/// Concrete source error reasons. Expression subtypes are retained as their typed
/// expression handles; constructors that need a particular subtype must validate it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorReason {
    Dummy,
    Internal {
        node: crate::ast::utility::nodes::Node,
        explanation: String,
    },
    FeatureUnsupported {
        node: crate::ast::utility::nodes::Node,
        explanation: String,
    },
    UnexpectedNode {
        node: crate::ast::utility::nodes::Node,
        explanation: String,
        stack_trace: Vec<String>,
    },
    AssertionFalse(crate::ast::expression::Exp),
    EpsilonAsParam(crate::ast::expression::Exp),
    ReceiverNull(crate::ast::utility::nodes::Node),
    DivisionByZero(crate::ast::expression::Exp),
    NegativePermission(crate::ast::expression::Exp),
    NonPositivePermission(crate::ast::expression::Exp),
    InsufficientPermission(crate::ast::utility::nodes::Node),
    InvalidPermMultiplication(crate::ast::expression::Exp),
    MagicWandChunkNotFound(crate::ast::expression::Exp),
    QPAssertionNotInjective(crate::ast::utility::nodes::Node),
    QuasihavocallNotInjective(crate::ast::statement::Stmt),
    LabelledStateNotReached(crate::ast::expression::Exp),
    SeqIndexNegative {
        sequence: crate::ast::expression::Exp,
        index: crate::ast::expression::Exp,
    },
    SeqIndexExceedsLength {
        sequence: crate::ast::expression::Exp,
        index: crate::ast::expression::Exp,
    },
    MapKeyNotContained {
        map: crate::ast::expression::Exp,
        key: crate::ast::expression::Exp,
    },
    QueryTimedOut {
        inner: Box<ErrorReason>,
        query_time: i32,
    },
}
impl ErrorReason {
    pub fn id(&self) -> &str {
        use ErrorReason::*;
        match self {
            Dummy => "?",
            Internal { .. } => "internal",
            FeatureUnsupported { .. } => "feature.unsupported",
            UnexpectedNode { .. } => "unexpected.node",
            AssertionFalse(_) => "assertion.false",
            EpsilonAsParam(_) => "epsilon.as.param",
            ReceiverNull(_) => "receiver.null",
            DivisionByZero(_) => "division.by.zero",
            NegativePermission(_) => "negative.permission",
            NonPositivePermission(_) => "permission.not.positive",
            InsufficientPermission(_) => "insufficient.permission",
            InvalidPermMultiplication(_) => "invalid.perm.multiplication",
            MagicWandChunkNotFound(_) => "wand.not.found",
            QPAssertionNotInjective(_) => "qp.not.injective",
            QuasihavocallNotInjective(_) => "quasihavocall.not.injective",
            LabelledStateNotReached(_) => "labelled.state.not.reached",
            SeqIndexNegative { .. } => "seq.index.negative",
            SeqIndexExceedsLength { .. } => "seq.index.length",
            MapKeyNotContained { .. } => "map.key.contains",
            QueryTimedOut { inner, .. } => inner.id(),
        }
    }
    /// Uses the AST printer supplied by the caller. A printer failure is propagated.
    pub fn readable_message(
        &self,
        render: &impl Fn(
            &crate::ast::utility::nodes::Node,
        ) -> Result<String, super::verification_result::DiagnosticError>,
    ) -> Result<String, super::verification_result::DiagnosticError> {
        use crate::ast::utility::nodes::Node;
        use ErrorReason::*;
        let exp = |e: &crate::ast::expression::Exp| render(&Node::Exp(e.clone()));
        Ok(match self {
            Dummy => "?".into(), Internal { explanation,.. } => explanation.clone(),
            FeatureUnsupported { node, explanation } => format!("{} is not supported. {explanation}", render(node)?),
            UnexpectedNode { node, explanation,.. } => format!("{} occurred unexpectedly. {explanation}", render(node)?),
            AssertionFalse(e) => format!("Assertion {} might not hold.", exp(e)?),
            EpsilonAsParam(e) => format!("The parameter {} might be an epsilon permission, which is not allowed for method parameters.", exp(e)?),
            ReceiverNull(n) => format!("Receiver of {} might be null.", render(n)?),
            DivisionByZero(e) => format!("Divisor {} might be zero.", exp(e)?),
            NegativePermission(e) => format!("Fraction {} might be negative.", exp(e)?),
            NonPositivePermission(e) => format!("Fraction {} might not be positive.", exp(e)?),
            InsufficientPermission(n) => format!("There might be insufficient permission to access {}", render(n)?),
            InvalidPermMultiplication(_) => "Permission multiplication might not be possible, as an operand might contain epsilons.".into(),
            MagicWandChunkNotFound(_) => "Magic wand instance not found.".into(),
            QPAssertionNotInjective(n) => format!("Quantified resource {} might not be injective.", render(n)?),
            QuasihavocallNotInjective(s) => format!("Quasihavocall statement {} might not be injective.", render(&Node::Stmt(s.clone()))?),
            LabelledStateNotReached(node) => {
                let crate::ast::expression::ExpKind::LabelledOld(_, label) = node.kind() else {
                    return Err(super::verification_result::DiagnosticError::InvalidNode("LabelledStateNotReached requires LabelledOld"));
                };
                format!("Did not reach labelled state {label} required to evaluate {}.", exp(node)?)
            },
            SeqIndexNegative {sequence,index} => format!("Index {} into {} might be negative.", exp(index)?, exp(sequence)?),
            SeqIndexExceedsLength {sequence,index} => format!("Index {} into {} might exceed sequence length.", exp(index)?, exp(sequence)?),
            MapKeyNotContained {map,key} => format!("Map {} might not contain an entry at key {}.", exp(map)?, exp(key)?),
            QueryTimedOut {inner,query_time} => format!("{} An SMT query timed out after {query_time}ms.", inner.readable_message(render)?),
        })
    }
}

impl ErrorReason {
    pub fn offending_node(&self) -> Option<crate::ast::utility::nodes::Node> {
        use crate::ast::utility::nodes::Node;
        use ErrorReason::*;
        match self {
            Dummy => None,
            Internal { node, .. }
            | FeatureUnsupported { node, .. }
            | UnexpectedNode { node, .. }
            | ReceiverNull(node)
            | InsufficientPermission(node)
            | QPAssertionNotInjective(node) => Some(node.clone()),
            AssertionFalse(e)
            | EpsilonAsParam(e)
            | DivisionByZero(e)
            | NegativePermission(e)
            | NonPositivePermission(e)
            | InvalidPermMultiplication(e)
            | MagicWandChunkNotFound(e)
            | LabelledStateNotReached(e) => Some(Node::Exp(e.clone())),
            QuasihavocallNotInjective(s) => Some(Node::Stmt(s.clone())),
            SeqIndexNegative { index, .. } | SeqIndexExceedsLength { index, .. } => {
                Some(Node::Exp(index.clone()))
            }
            MapKeyNotContained { key, .. } => Some(Node::Exp(key.clone())),
            QueryTimedOut { inner, .. } => inner.offending_node(),
        }
    }
    /// Mirror withNode, rejecting invalid casts instead of constructing malformed reasons.
    pub fn with_node(
        &self,
        replacement: crate::ast::utility::nodes::Node,
    ) -> Result<Self, super::verification_result::DiagnosticError> {
        use super::verification_result::DiagnosticError;
        use crate::ast::{expression::ExpKind, statement::StmtKind, utility::nodes::Node};
        use ErrorReason::*;
        let invalid = || DiagnosticError::InvalidNode("replacement has the wrong reason node type");
        let exp = || match &replacement {
            Node::Exp(e) => Ok(e.clone()),
            _ => Err(invalid()),
        };
        Ok(match self {
            Dummy => Dummy,
            Internal { explanation, .. } => Internal {
                node: replacement,
                explanation: explanation.clone(),
            },
            FeatureUnsupported { explanation, .. } => FeatureUnsupported {
                node: replacement,
                explanation: explanation.clone(),
            },
            UnexpectedNode {
                explanation,
                stack_trace,
                ..
            } => UnexpectedNode {
                node: replacement,
                explanation: explanation.clone(),
                stack_trace: stack_trace.clone(),
            },
            AssertionFalse(_) => AssertionFalse(exp()?),
            EpsilonAsParam(_) => EpsilonAsParam(exp()?),
            DivisionByZero(_) => DivisionByZero(exp()?),
            NegativePermission(_) => NegativePermission(exp()?),
            NonPositivePermission(_) => NonPositivePermission(exp()?),
            ReceiverNull(_) | InsufficientPermission(_) => {
                if !matches!(
                    &replacement,
                    Node::FieldAccess(_) | Node::PredicateAccess(_)
                ) && !matches!(&replacement, Node::Exp(e) if matches!(e.kind(), ExpKind::FieldAccess(..) | ExpKind::PredicateAccess(..)))
                {
                    return Err(invalid());
                }
                if matches!(self, ReceiverNull(_)) {
                    ReceiverNull(replacement)
                } else {
                    InsufficientPermission(replacement)
                }
            }
            InvalidPermMultiplication(_) => {
                let e = exp()?;
                if !matches!(e.kind(), ExpKind::PermMul(..)) {
                    return Err(invalid());
                }
                InvalidPermMultiplication(e)
            }
            MagicWandChunkNotFound(_) => {
                let e = exp()?;
                if !matches!(e.kind(), ExpKind::MagicWand(..)) {
                    return Err(invalid());
                }
                MagicWandChunkNotFound(e)
            }
            QPAssertionNotInjective(_) => {
                if !matches!(
                    &replacement,
                    Node::FieldAccess(_) | Node::PredicateAccess(_) | Node::Exp(_)
                ) {
                    return Err(invalid());
                }
                if let Node::Exp(e) = &replacement {
                    if !matches!(
                        e.kind(),
                        ExpKind::MagicWand(..)
                            | ExpKind::FieldAccess(..)
                            | ExpKind::PredicateAccess(..)
                    ) {
                        return Err(invalid());
                    }
                }
                QPAssertionNotInjective(replacement)
            }
            QuasihavocallNotInjective(_) => {
                let Node::Stmt(s) = replacement else {
                    return Err(invalid());
                };
                if !matches!(s.kind(), StmtKind::Quasihavocall { .. }) {
                    return Err(invalid());
                }
                QuasihavocallNotInjective(s)
            }
            LabelledStateNotReached(_) => {
                let e = exp()?;
                if !matches!(e.kind(), ExpKind::LabelledOld(..)) {
                    return Err(invalid());
                }
                LabelledStateNotReached(e)
            }
            SeqIndexNegative { sequence, .. } => SeqIndexNegative {
                sequence: sequence.clone(),
                index: exp()?,
            },
            SeqIndexExceedsLength { sequence, .. } => SeqIndexExceedsLength {
                sequence: sequence.clone(),
                index: exp()?,
            },
            MapKeyNotContained { map, .. } => MapKeyNotContained {
                map: map.clone(),
                key: exp()?,
            },
            QueryTimedOut { inner, query_time } => QueryTimedOut {
                inner: Box::new(inner.with_node(replacement)?),
                query_time: *query_time,
            },
        })
    }
}

/// Source verification-error cases, carrying the actual offending source nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationErrorKind {
    Internal(Option<crate::ast::utility::nodes::Node>),
    AssignmentFailed(crate::ast::statement::Stmt),
    CallFailed(crate::ast::statement::Stmt),
    ContractNotWellformed(crate::ast::expression::Exp),
    PreconditionInCallFalse(crate::ast::statement::Stmt),
    PreconditionInAppFalse(crate::ast::expression::Exp),
    ExhaleFailed(crate::ast::statement::Stmt),
    InhaleFailed(crate::ast::statement::Stmt),
    IfFailed(crate::ast::expression::Exp),
    WhileFailed(crate::ast::expression::Exp),
    AssertFailed(crate::ast::statement::Stmt),
    TerminationFailed(crate::ast::program::Function),
    PostconditionViolated {
        node: crate::ast::expression::Exp,
        member: crate::ast::program::Member,
    },
    FoldFailed(crate::ast::statement::Stmt),
    UnfoldFailed(crate::ast::statement::Stmt),
    PackageFailed(crate::ast::statement::Stmt),
    ApplyFailed(crate::ast::statement::Stmt),
    LoopInvariantNotPreserved(crate::ast::expression::Exp),
    LoopInvariantNotEstablished(crate::ast::expression::Exp),
    FunctionNotWellformed(crate::ast::program::Function),
    PredicateNotWellformed(crate::ast::program::Predicate),
    MagicWandNotWellformed(crate::ast::expression::Exp),
    LetWandFailed(crate::ast::statement::Stmt),
    QuasihavocFailed(crate::ast::statement::Stmt),
    HavocallFailed(crate::ast::statement::Stmt),
    HeuristicsFailed(crate::ast::utility::nodes::Node),
}
impl VerificationErrorKind {
    pub fn id(&self) -> &'static str {
        use VerificationErrorKind::*;
        match self {
            Internal(_) => "internal",
            AssignmentFailed(_) => "assignment.failed",
            CallFailed(_) => "call.failed",
            ContractNotWellformed(_) => "not.wellformed",
            PreconditionInCallFalse(_) => "call.precondition",
            PreconditionInAppFalse(_) => "application.precondition",
            ExhaleFailed(_) => "exhale.failed",
            InhaleFailed(_) => "inhale.failed",
            IfFailed(_) => "if.failed",
            WhileFailed(_) => "while.failed",
            AssertFailed(_) => "assert.failed",
            TerminationFailed(_) => "termination.failed",
            PostconditionViolated { .. } => "postcondition.violated",
            FoldFailed(_) => "fold.failed",
            UnfoldFailed(_) => "unfold.failed",
            PackageFailed(_) => "package.failed",
            ApplyFailed(_) => "apply.failed",
            LoopInvariantNotPreserved(_) => "invariant.not.preserved",
            LoopInvariantNotEstablished(_) => "invariant.not.established",
            FunctionNotWellformed(_) => "function.not.wellformed",
            PredicateNotWellformed(_) => "predicate.not.wellformed",
            MagicWandNotWellformed(_) => "wand.not.wellformed",
            LetWandFailed(_) => "letwand.failed",
            QuasihavocFailed(_) => "quasihavoc.failed",
            HavocallFailed(_) => "quasihavocall.failed",
            HeuristicsFailed(_) => "heuristics.failed",
        }
    }
    pub fn offending_node(&self) -> Option<crate::ast::utility::nodes::Node> {
        use crate::ast::{program::Member, utility::nodes::Node};
        use VerificationErrorKind::*;
        match self {
            Internal(n) => n.clone(),
            HeuristicsFailed(n) => Some(n.clone()),
            AssignmentFailed(s)
            | CallFailed(s)
            | PreconditionInCallFalse(s)
            | ExhaleFailed(s)
            | InhaleFailed(s)
            | AssertFailed(s)
            | FoldFailed(s)
            | UnfoldFailed(s)
            | PackageFailed(s)
            | ApplyFailed(s)
            | LetWandFailed(s)
            | QuasihavocFailed(s)
            | HavocallFailed(s) => Some(Node::Stmt(s.clone())),
            ContractNotWellformed(e)
            | PreconditionInAppFalse(e)
            | IfFailed(e)
            | WhileFailed(e)
            | LoopInvariantNotPreserved(e)
            | LoopInvariantNotEstablished(e)
            | MagicWandNotWellformed(e)
            | PostconditionViolated { node: e, .. } => Some(Node::Exp(e.clone())),
            TerminationFailed(f) | FunctionNotWellformed(f) => {
                Some(Node::Member(Member::Function(f.clone())))
            }
            PredicateNotWellformed(p) => Some(Node::Member(Member::Predicate(p.clone()))),
        }
    }
}

impl VerificationErrorKind {
    pub fn text(
        &self,
        render: &impl Fn(
            &crate::ast::utility::nodes::Node,
        ) -> Result<String, super::verification_result::DiagnosticError>,
    ) -> Result<String, super::verification_result::DiagnosticError> {
        use super::verification_result::DiagnosticError;
        use crate::ast::{expression::ExpKind, statement::StmtKind, utility::nodes::Node};
        use VerificationErrorKind::*;
        let invalid = || {
            DiagnosticError::InvalidNode("verification error has the wrong offending node subtype")
        };
        Ok(match self {
            Internal(_) => "An internal error occurred.".into(),
            AssignmentFailed(_) => "Assignment might fail.".into(),
            CallFailed(_) => "Method call might fail.".into(),
            ContractNotWellformed(_) => "Contract might not be well-formed.".into(),
            PreconditionInCallFalse(s) => {
                let StmtKind::MethodCall { method_name, .. } = s.kind() else {
                    return Err(invalid());
                };
                format!("The precondition of method {method_name} might not hold.")
            }
            PreconditionInAppFalse(e) => {
                let ExpKind::FuncApp(name, _) = e.kind() else {
                    return Err(invalid());
                };
                format!("Precondition of function {name} might not hold.")
            }
            ExhaleFailed(_) => "Exhale might fail.".into(),
            InhaleFailed(_) => "Inhale might fail.".into(),
            IfFailed(_) => "Conditional statement might fail.".into(),
            WhileFailed(_) => "While statement might fail.".into(),
            AssertFailed(_) => "Assert might fail.".into(),
            TerminationFailed(f) => format!("Function {} might not terminate.", f.name),
            PostconditionViolated { member, .. } => {
                format!("Postcondition of {} might not hold.", member.name())
            }
            FoldFailed(s) | UnfoldFailed(s) => {
                let acc = match s.kind() {
                    StmtKind::Fold(a) if matches!(self, FoldFailed(_)) => a,
                    StmtKind::Unfold(a) if matches!(self, UnfoldFailed(_)) => a,
                    _ => return Err(invalid()),
                };
                let action = if matches!(self, FoldFailed(_)) {
                    "Folding"
                } else {
                    "Unfolding"
                };
                format!(
                    "{action} {} might fail.",
                    render(&Node::PredicateAccess(acc.location.clone()))?
                )
            }
            PackageFailed(_) => "Packaging wand might fail.".into(),
            ApplyFailed(_) => "Applying wand might fail.".into(),
            LoopInvariantNotPreserved(e) => format!(
                "Loop invariant {} might not be preserved.",
                render(&Node::Exp(e.clone()))?
            ),
            LoopInvariantNotEstablished(e) => format!(
                "Loop invariant {} might not hold on entry.",
                render(&Node::Exp(e.clone()))?
            ),
            FunctionNotWellformed(_) => "Function might not be well-formed.".into(),
            PredicateNotWellformed(_) => "Predicate might not be well-formed.".into(),
            MagicWandNotWellformed(_) => "Magic wand might not be well-formed.".into(),
            LetWandFailed(_) => "Referencing a wand might fail.".into(),
            QuasihavocFailed(_) => "Quasihavoc might fail.".into(),
            HavocallFailed(_) => "Quasihavocall might fail.".into(),
            HeuristicsFailed(_) => "Applying heuristics failed.".into(),
        })
    }
}

#[cfg(test)]
mod reason_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
        utility::nodes::Node,
    };
    #[test]
    fn timeout_preserves_reason_id_and_updates_nested_node() {
        let a = Exp::new(ExpKind::TrueLit, Metadata::default());
        let b = Exp::new(ExpKind::FalseLit, Metadata::default());
        let reason = ErrorReason::QueryTimedOut {
            inner: Box::new(ErrorReason::AssertionFalse(a)),
            query_time: 30,
        };
        let result = reason.with_node(Node::Exp(b.clone())).unwrap();
        assert_eq!(result.id(), "assertion.false");
        assert_eq!(result.offending_node(), Some(Node::Exp(b)));
        assert_eq!(
            result
                .readable_message(&|_| Ok("expression".into()))
                .unwrap(),
            "Assertion expression might not hold. An SMT query timed out after 30ms."
        );
    }
}

fn node_position(
    node: &crate::ast::utility::nodes::Node,
) -> Result<crate::ast::position::Position, super::verification_result::DiagnosticError> {
    use super::verification_result::DiagnosticError;
    use crate::ast::{
        program::{DomainAxiomKind, Member},
        utility::nodes::Node,
    };
    let meta = match node {
        Node::Program(v) => &v.meta,
        Node::Member(Member::Domain(v)) => &v.meta,
        Node::Member(Member::Field(v)) => &v.meta,
        Node::Member(Member::Function(v)) => &v.meta,
        Node::Member(Member::Predicate(v)) => &v.meta,
        Node::Member(Member::Method(v)) => &v.meta,
        Node::DomainFunc(v) => &v.meta,
        Node::DomainAxiom(a) => match a.kind() {
            DomainAxiomKind::Named { meta, .. } | DomainAxiomKind::Anonymous { meta, .. } => meta,
        },
        Node::LocalDecl(v) => &v.meta,
        Node::UnnamedLocalDecl(v) => &v.meta,
        Node::Exp(v) => v.metadata(),
        Node::Stmt(v) => v.metadata(),
        Node::LocalVar(v) => &v.meta,
        Node::FieldAccess(v) => &v.meta,
        Node::PredicateAccess(v) => &v.meta,
        Node::PredicateAccessPredicate(v) => &v.meta,
        Node::Trigger(v) => &v.meta,
        Node::Type(_) => {
            return Err(DiagnosticError::InvalidNode(
                "type is not a positioned error node",
            ));
        }
        Node::Member(Member::Extension(_)) => {
            return Err(DiagnosticError::Unsupported("extension member position"));
        }
    };
    Ok(meta.position.clone())
}
impl ErrorReason {
    pub fn position(
        &self,
    ) -> Result<crate::ast::position::Position, super::verification_result::DiagnosticError> {
        match self.offending_node() {
            Some(n) => node_position(&n),
            None => Ok(crate::ast::position::Position::NoPosition),
        }
    }
}
impl VerificationErrorKind {
    pub fn position(
        &self,
    ) -> Result<crate::ast::position::Position, super::verification_result::DiagnosticError> {
        use super::verification_result::DiagnosticError;
        use crate::ast::{
            statement::{ResourceAccess, StmtKind},
            utility::nodes::Node,
        };
        let invalid = || {
            DiagnosticError::InvalidNode("verification error has the wrong offending node subtype")
        };
        let resource = |r: &ResourceAccess| match r {
            ResourceAccess::Field(v) => Node::FieldAccess(v.clone()),
            ResourceAccess::Predicate(v) => Node::PredicateAccess(v.clone()),
            ResourceAccess::MagicWand(v) => Node::Exp(v.clone()),
        };
        let special = match self {
            Self::ExhaleFailed(s) => match s.kind() {
                StmtKind::Exhale(e) => Some(Node::Exp(e.clone())),
                _ => return Err(invalid()),
            },
            Self::InhaleFailed(s) => match s.kind() {
                StmtKind::Inhale(e) => Some(Node::Exp(e.clone())),
                _ => return Err(invalid()),
            },
            Self::AssertFailed(s) => match s.kind() {
                StmtKind::Assert(e) => Some(Node::Exp(e.clone())),
                _ => return Err(invalid()),
            },
            Self::QuasihavocFailed(s) => match s.kind() {
                StmtKind::Quasihavoc { resource: r, .. } => Some(resource(r)),
                _ => return Err(invalid()),
            },
            Self::HavocallFailed(s) => match s.kind() {
                StmtKind::Quasihavocall { resource: r, .. } => Some(resource(r)),
                _ => return Err(invalid()),
            },
            _ => self.offending_node(),
        };
        match special {
            Some(n) => node_position(&n),
            None => Ok(crate::ast::position::Position::NoPosition),
        }
    }
}

/// The source allows failure contexts to be appended after constructing an error.
pub trait FailureContext: fmt::Debug + Send + Sync {
    fn counterexample(&self) -> Option<Arc<dyn Counterexample>>;
    fn render(&self) -> String;
}
#[derive(Clone, Debug)]
pub struct VerificationError {
    pub kind: VerificationErrorKind,
    pub reason: ErrorReason,
    pub cached: bool,
    pub failure_contexts: Vec<Arc<dyn FailureContext>>,
}
impl VerificationError {
    pub fn new(kind: VerificationErrorKind, reason: ErrorReason) -> Self {
        Self {
            kind,
            reason,
            cached: false,
            failure_contexts: Vec::new(),
        }
    }
    pub fn full_id(&self) -> String {
        format!("{}:{}", self.kind.id(), self.reason.id())
    }
    /// Source case-class copies reset the separately mutable failure contexts.
    pub fn with_reason(&self, reason: ErrorReason) -> Self {
        Self {
            kind: self.kind.clone(),
            reason,
            cached: self.cached,
            failure_contexts: Vec::new(),
        }
    }
    pub fn with_node(
        &self,
        node: crate::ast::utility::nodes::Node,
    ) -> Result<Self, super::verification_result::DiagnosticError> {
        Ok(Self {
            kind: self.kind.with_node(node)?,
            reason: self.reason.clone(),
            cached: self.cached,
            failure_contexts: Vec::new(),
        })
    }
    pub fn readable_message(
        &self,
        with_id: bool,
        with_position: bool,
        render: &impl Fn(
            &crate::ast::utility::nodes::Node,
        ) -> Result<String, super::verification_result::DiagnosticError>,
    ) -> Result<String, super::verification_result::DiagnosticError> {
        let id = if with_id {
            format!("[{}] ", self.full_id())
        } else {
            String::new()
        };
        let pos = if with_position {
            format!(" ({})", self.kind.position()?)
        } else {
            String::new()
        };
        Ok(format!(
            "{id}{} {}{pos}",
            self.kind.text(render)?,
            self.reason.readable_message(render)?
        ))
    }
    pub fn message_with_contexts(
        &self,
        render: &impl Fn(
            &crate::ast::utility::nodes::Node,
        ) -> Result<String, super::verification_result::DiagnosticError>,
    ) -> Result<String, super::verification_result::DiagnosticError> {
        let mut s = self.readable_message(false, true, render)?;
        for context in &self.failure_contexts {
            s.push('\n');
            s.push_str(&context.render());
        }
        Ok(s)
    }
    pub fn loggable_message(&self) -> Result<String, super::verification_result::DiagnosticError> {
        Ok(format!(
            "{}-{}{}",
            self.full_id(),
            self.kind.position()?,
            if self.cached { "-cached" } else { "" }
        ))
    }
}

impl VerificationErrorKind {
    /// Reproduce source withNode casts without permitting invalid replacement types.
    pub fn with_node(
        &self,
        node: crate::ast::utility::nodes::Node,
    ) -> Result<Self, super::verification_result::DiagnosticError> {
        use super::verification_result::DiagnosticError;
        use crate::ast::{
            expression::ExpKind, program::Member, statement::StmtKind, utility::nodes::Node,
        };
        use VerificationErrorKind::*;
        let invalid = || {
            DiagnosticError::InvalidNode("replacement has the wrong verification error node type")
        };
        let exp = || {
            if let Node::Exp(e) = &node {
                Ok(e.clone())
            } else {
                Err(invalid())
            }
        };
        let stmt = || {
            if let Node::Stmt(s) = &node {
                Ok(s.clone())
            } else {
                Err(invalid())
            }
        };
        Ok(match self {
            Internal(_) => Internal(Some(node)),
            HeuristicsFailed(_) => HeuristicsFailed(node),
            AssignmentFailed(_) => {
                let s = stmt()?;
                if !matches!(
                    s.kind(),
                    StmtKind::LocalVarAssign { .. } | StmtKind::FieldAssign { .. }
                ) {
                    return Err(invalid());
                }
                AssignmentFailed(s)
            }
            CallFailed(_) | PreconditionInCallFalse(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::MethodCall { .. }) {
                    return Err(invalid());
                }
                if matches!(self, CallFailed(_)) {
                    CallFailed(s)
                } else {
                    PreconditionInCallFalse(s)
                }
            }
            ContractNotWellformed(_) => ContractNotWellformed(exp()?),
            PreconditionInAppFalse(_) => {
                let e = exp()?;
                if !matches!(e.kind(), ExpKind::FuncApp(..)) {
                    return Err(invalid());
                }
                PreconditionInAppFalse(e)
            }
            ExhaleFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Exhale(_)) {
                    return Err(invalid());
                }
                ExhaleFailed(s)
            }
            InhaleFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Inhale(_)) {
                    return Err(invalid());
                }
                InhaleFailed(s)
            }
            IfFailed(_) => IfFailed(exp()?),
            WhileFailed(_) => WhileFailed(exp()?),
            AssertFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Assert(_)) {
                    return Err(invalid());
                }
                AssertFailed(s)
            }
            TerminationFailed(_) | FunctionNotWellformed(_) => {
                let Node::Member(Member::Function(f)) = node else {
                    return Err(invalid());
                };
                if matches!(self, TerminationFailed(_)) {
                    TerminationFailed(f)
                } else {
                    FunctionNotWellformed(f)
                }
            }
            PostconditionViolated { member, .. } => PostconditionViolated {
                node: exp()?,
                member: member.clone(),
            },
            FoldFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Fold(_)) {
                    return Err(invalid());
                }
                FoldFailed(s)
            }
            UnfoldFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Unfold(_)) {
                    return Err(invalid());
                }
                UnfoldFailed(s)
            }
            PackageFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Package { .. }) {
                    return Err(invalid());
                }
                PackageFailed(s)
            }
            ApplyFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Apply(_)) {
                    return Err(invalid());
                }
                ApplyFailed(s)
            }
            LoopInvariantNotPreserved(_) => LoopInvariantNotPreserved(exp()?),
            LoopInvariantNotEstablished(_) => LoopInvariantNotEstablished(exp()?),
            PredicateNotWellformed(_) => {
                let Node::Member(Member::Predicate(p)) = node else {
                    return Err(invalid());
                };
                PredicateNotWellformed(p)
            }
            MagicWandNotWellformed(_) => {
                let e = exp()?;
                if !matches!(e.kind(), ExpKind::MagicWand(..)) {
                    return Err(invalid());
                }
                MagicWandNotWellformed(e)
            }
            LetWandFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::LocalVarAssign { .. }) {
                    return Err(invalid());
                }
                LetWandFailed(s)
            }
            QuasihavocFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Quasihavoc { .. }) {
                    return Err(invalid());
                }
                QuasihavocFailed(s)
            }
            HavocallFailed(_) => {
                let s = stmt()?;
                if !matches!(s.kind(), StmtKind::Quasihavocall { .. }) {
                    return Err(invalid());
                }
                HavocallFailed(s)
            }
        })
    }
}

/// Rendering is supplied by the AST printer, which is not yet fully ported.
pub trait ErrorNodeRenderer: fmt::Debug + Send + Sync {
    fn render_node(
        &self,
        node: &crate::ast::utility::nodes::Node,
    ) -> Result<String, super::verification_result::DiagnosticError>;
}
#[derive(Clone, Debug)]
pub struct RenderedVerificationError {
    error: VerificationError,
    renderer: Arc<dyn ErrorNodeRenderer>,
}
impl super::verification_result::VerificationDiagnostic for RenderedVerificationError {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn full_id(&self) -> String {
        self.error.full_id()
    }
    fn position(&self) -> crate::ast::position::Position {
        // The diagnostic interface currently cannot return position errors.
        // Restrict construction to validated errors with supported positions.
        self.error
            .kind
            .position()
            .expect("validated verification error position")
    }
    fn readable_message(&self) -> Result<String, super::verification_result::DiagnosticError> {
        self.error
            .message_with_contexts(&|node| self.renderer.render_node(node))
    }
    fn render(&self) -> Result<String, super::verification_result::DiagnosticError> {
        let mut text = self
            .error
            .readable_message(true, true, &|node| self.renderer.render_node(node))?;
        if self.error.cached {
            text.push_str(" - cached");
        }
        Ok(text)
    }
    fn cached(&self) -> bool {
        self.error.cached
    }
    fn transformed_error(
        &self,
    ) -> Result<
        Arc<dyn super::verification_result::VerificationDiagnostic>,
        super::verification_result::DiagnosticError,
    > {
        Err(super::verification_result::DiagnosticError::Unsupported(
            "verification error back transformation and AST reconstruction",
        ))
    }
}
impl RenderedVerificationError {
    pub fn error(&self) -> &VerificationError {
        &self.error
    }
    pub fn new(
        error: VerificationError,
        renderer: Arc<dyn ErrorNodeRenderer>,
    ) -> Result<Self, super::verification_result::DiagnosticError> {
        error.kind.position()?;
        if let Some(node) = error.kind.offending_node() {
            error.kind.with_node(node)?;
        }
        if let Some(node) = error.reason.offending_node() {
            error.reason.with_node(node)?;
        }
        Ok(Self { error, renderer })
    }
}

/// A source partial verification error is a factory awaiting its reason.
#[derive(Clone)]
pub struct PartialVerificationError {
    factory: Arc<
        dyn Fn(
                ErrorReason,
            )
                -> Result<VerificationError, super::verification_result::DiagnosticError>
            + Send
            + Sync,
    >,
}
impl PartialVerificationError {
    pub fn new(
        factory: impl Fn(
            ErrorReason,
        )
            -> Result<VerificationError, super::verification_result::DiagnosticError>
        + Send
        + Sync
        + 'static,
    ) -> Self {
        Self {
            factory: Arc::new(factory),
        }
    }
    pub fn for_kind(kind: VerificationErrorKind) -> Self {
        Self::new(move |reason| Ok(VerificationError::new(kind.clone(), reason)))
    }
    pub fn due_to(
        &self,
        reason: ErrorReason,
    ) -> Result<VerificationError, super::verification_result::DiagnosticError> {
        (self.factory)(reason)
    }
    pub fn with_reason_node_transformed(
        &self,
        transform: impl Fn(
            crate::ast::utility::nodes::Node,
        ) -> Result<
            crate::ast::utility::nodes::Node,
            super::verification_result::DiagnosticError,
        > + Send
        + Sync
        + 'static,
    ) -> Self {
        let original = self.clone();
        Self::new(move |reason| {
            let reason = if let Some(node) = reason.offending_node() {
                reason.with_node(transform(node)?)?
            } else {
                return Err(super::verification_result::DiagnosticError::Unsupported(
                    "transforming DummyNode requires an AST dummy-node representation",
                ));
            };
            original.due_to(reason)
        })
    }
    pub fn render(
        &self,
        render: &impl Fn(
            &crate::ast::utility::nodes::Node,
        ) -> Result<String, super::verification_result::DiagnosticError>,
    ) -> Result<String, super::verification_result::DiagnosticError> {
        self.due_to(ErrorReason::Dummy)?
            .readable_message(true, true, render)
    }
}
