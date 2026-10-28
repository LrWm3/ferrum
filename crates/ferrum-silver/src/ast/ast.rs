//! Common Silver AST metadata and contracts.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Ast.scala
//!
//! Status: partial. Metadata and info composition are implemented; node traversal,
//! rewriting, consistency and typed diagnostic backtransformation await their collaborators.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::any::Any;
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::Arc;

use super::position::Position;
use super::r#type::Type;
use crate::parser::parse_ast::PNodeHandle;

/// Metadata supplied by extensions, including failure-expected tags and source nodes.
/// Its precise parser handle and plugin dispatch require cross-module reconciliation.
pub trait ExtensionInfo: Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn comments(&self) -> Vec<String> {
        Vec::new()
    }
    fn is_cached(&self) -> bool {
        false
    }
    /// Source FailureExpectedInfo marker for diagnostics such as refute.
    fn is_failure_expected(&self) -> bool {
        false
    }
}

#[derive(Clone, Debug, Default)]
pub enum Info {
    #[default]
    NoInfo,
    SourcePNode(PNodeHandle),
    Annotation(HashMap<String, Vec<String>>),
    Simple(Vec<String>),
    AutoTriggered,
    WeightedQuantifier(i32),
    Cached,
    Synthesized,
    /// Includes FailureExpectedInfo and other plugin-provided metadata.
    Extension(Arc<dyn ExtensionInfo>),
    Cons(Box<Info>, Box<Info>),
}
impl Info {
    pub fn pair(head: Self, tail: Self) -> Self {
        match (head, tail) {
            (Self::NoInfo, b) => b,
            (a, Self::NoInfo) => a,
            (a, b) => Self::Cons(Box::new(a), Box::new(b)),
        }
    }
    pub fn comments(&self) -> Vec<String> {
        match self {
            Self::Simple(c) => c.clone(),
            Self::Extension(e) => e.comments(),
            Self::Cons(a, b) => {
                let mut c = a.comments();
                c.extend(b.comments());
                c
            }
            _ => Vec::new(),
        }
    }
    pub fn is_cached(&self) -> bool {
        match self {
            Self::Cached => true,
            Self::Extension(e) => e.is_cached(),
            Self::Cons(a, b) => a.is_cached() || b.is_cached(),
            _ => false,
        }
    }
    pub fn is_failure_expected(&self) -> bool {
        match self {
            Self::Extension(info) => info.is_failure_expected(),
            Self::Cons(head, tail) => head.is_failure_expected() || tail.is_failure_expected(),
            _ => false,
        }
    }
    /// Find the first matching info in source order, including composed infos.
    pub fn find(&self, predicate: &impl Fn(&Info) -> bool) -> Option<&Info> {
        if predicate(self) {
            return Some(self);
        }
        match self {
            Self::Cons(a, b) => a.find(predicate).or_else(|| b.find(predicate)),
            _ => None,
        }
    }
    pub fn all_matching<'a>(&'a self, predicate: &impl Fn(&Info) -> bool) -> Vec<&'a Info> {
        if predicate(self) {
            return vec![self];
        }
        match self {
            Self::Cons(a, b) => {
                let mut out = a.all_matching(predicate);
                out.extend(b.all_matching(predicate));
                out
            }
            _ => Vec::new(),
        }
    }
    pub fn remove_matching(&self, predicate: &impl Fn(&Info) -> bool) -> Info {
        // Upstream recurses into ConsInfo before testing the requested subtype.
        match self {
            Self::Cons(a, b) => {
                Self::pair(a.remove_matching(predicate), b.remove_matching(predicate))
            }
            _ if predicate(self) => Self::NoInfo,
            _ => self.clone(),
        }
    }
    pub fn find_extension<T: Any>(&self) -> Option<&T> {
        match self {
            Self::Extension(e) => e.as_any().downcast_ref(),
            Self::Cons(a, b) => a.find_extension().or_else(|| b.find_extension()),
            _ => None,
        }
    }
    pub fn all_extensions<T: Any>(&self) -> Vec<&T> {
        match self {
            Self::Extension(e) => e.as_any().downcast_ref().into_iter().collect(),
            Self::Cons(a, b) => {
                let mut result = a.all_extensions::<T>();
                result.extend(b.all_extensions::<T>());
                result
            }
            _ => Vec::new(),
        }
    }
    pub fn remove_extension<T: Any>(&self) -> Self {
        match self {
            Self::Extension(e) if e.as_any().is::<T>() => Self::NoInfo,
            Self::Cons(a, b) => Self::pair(a.remove_extension::<T>(), b.remove_extension::<T>()),
            _ => self.clone(),
        }
    }
}

/// Object-safe extension boundary for source partial error transformations.
/// An unsupported callback must fail rather than silently discard a transformation.
pub trait ErrorTransformation: Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    /// `None` means the source partial function is not defined for this error.
    fn transform_error(
        &self,
        _error: &Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
    ) -> Result<
        Option<Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "error transformation callback",
            ),
        )
    }
    /// `None` means that this source partial function does not match the reason.
    fn transform_reason(
        &self,
        _reason: &crate::verifier::verification_error::ErrorReason,
    ) -> Result<
        Option<crate::verifier::verification_error::ErrorReason>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "reason transformation callback",
            ),
        )
    }
}
/// Node back-link attached by a direct Viper rewrite.
#[derive(Clone, Debug)]
pub struct PreviousNode(pub super::utility::nodes::Node);
impl ErrorTransformation for PreviousNode {
    fn as_any(&self) -> &dyn Any {
        self
    }
}
#[derive(Clone, Debug)]
pub struct ErrorTrafo {
    pub error: Vec<Arc<dyn ErrorTransformation>>,
    pub reason: Vec<Arc<dyn ErrorTransformation>>,
    pub node: Option<Arc<dyn ErrorTransformation>>,
    no_trafos: bool,
}
impl Default for ErrorTrafo {
    fn default() -> Self {
        Self {
            error: Vec::new(),
            reason: Vec::new(),
            node: None,
            no_trafos: true,
        }
    }
}
impl ErrorTrafo {
    /// Construct source Trafos, including an explicitly empty Trafos value.
    pub fn trafos(
        error: Vec<Arc<dyn ErrorTransformation>>,
        reason: Vec<Arc<dyn ErrorTransformation>>,
        node: Option<Arc<dyn ErrorTransformation>>,
    ) -> Self {
        Self {
            error,
            reason,
            node,
            no_trafos: false,
        }
    }
    pub fn is_no_trafos(&self) -> bool {
        self.no_trafos && self.error.is_empty() && self.reason.is_empty() && self.node.is_none()
    }
    /// Source MakeTrafoPair preserves NoTrafos identity before concatenating.
    pub fn combine(&self, other: &Self) -> Self {
        if self.is_no_trafos() {
            return other.clone();
        }
        if other.is_no_trafos() {
            return self.clone();
        }
        let mut error = self.error.clone();
        error.extend(other.error.iter().cloned());
        let mut reason = self.reason.clone();
        reason.extend(other.reason.iter().cloned());
        Self {
            error,
            reason,
            node: other.node.clone().or_else(|| self.node.clone()),
            no_trafos: false,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Metadata {
    pub position: Position,
    pub info: Info,
    pub error_trafo: ErrorTrafo,
}

pub trait Positioned {
    fn position(&self) -> &Position;
}
pub trait Infoed {
    fn info(&self) -> &Info;
}
pub trait Typed {
    fn typ(&self) -> &Type;
    fn is_subtype(&self, other: &Type) -> bool {
        self.typ().is_subtype(other)
    }
}
pub trait Declaration: Positioned {
    fn name(&self) -> &str;
}
