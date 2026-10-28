//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/package.scala
//!
//! Purpose:
//! Convert Silicon results and exceptions to Silver result boundaries.
//!
//! Planned Rust structure:
//! Port unwrapExecutionExceptions, exceptionToViperError, convertToViperResult(s),
//! condenseToViperResult and classpath diagnostic constant.
//!
//! Behavior to preserve:
//! Unwrap nested ExecutionExceptions; SiliconException maps to its Silver error, other exceptions
//! to AbortedExceptionally and fatal Error stays distinct. Success and Unreachable map to Silver
//! Success; aggregate all failures in order, returning Success only if none.
//!
//! Integration:
//! reporting::exceptions, interfaces::verification, verifier and Silver result types.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for distinct failures and exception conversion.
//!
//! Open decisions:
//! Reconcile native panic/error boundary and JVM-specific classpath message disposition with
//! verifier.
//!
//! Status: ordered result conversion and explicit exception-wrapper conversion implemented.
//! Native worker/panic capture and stack-trace adapters remain. The obsolete JVM classpath
//! advice is retained only as a compatibility constant and is not emitted by native paths.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::exceptions::SiliconException;
use crate::interfaces::verification::{ResultKind, VerificationResult};
use ferrum_silver::ast::position::Position;
use ferrum_silver::verifier::verification_result::{
    AbstractError, FrontendError, FrontendErrorKind, VerificationResult as ViperResult,
};

/// Native callers classify recoverable errors and fatal runtime failures explicitly.
/// This does not classify arbitrary panic payloads or invent JVM stack frames.
#[derive(Clone, Debug)]
pub enum ExceptionCause {
    Execution(Box<ExceptionCause>),
    Silicon(SiliconException),
    Ordinary {
        message: String,
        stack_trace: Vec<String>,
    },
    Fatal {
        message: String,
    },
}
pub fn unwrap_execution_exceptions(mut cause: ExceptionCause) -> ExceptionCause {
    while let ExceptionCause::Execution(inner) = cause {
        cause = *inner;
    }
    cause
}
pub fn exception_to_viper_error(
    exception: ExceptionCause,
) -> Result<(ExceptionCause, ViperResult), ExceptionCause> {
    let cause = unwrap_execution_exceptions(exception);
    let error = match &cause {
        ExceptionCause::Silicon(error) => error.as_viper_error(),
        ExceptionCause::Ordinary {
            message,
            stack_trace,
        } => AbstractError::Frontend(FrontendError::new(
            FrontendErrorKind::AbortedExceptionally {
                cause: message.clone(),
                stack_trace: stack_trace.clone(),
            },
            Position::NoPosition,
        )),
        ExceptionCause::Fatal { .. } => return Err(cause),
        ExceptionCause::Execution(_) => unreachable!("wrappers were removed"),
    };
    Ok((cause, ViperResult::Failure(vec![error])))
}
pub const NO_CLASS_DEF_FOUND_ERROR_MESSAGE: &str = "A NoClassDefFoundError occurred (see below). As an attempt of solving this problem, please delete the file 'silicon_classpath.txt' (should be in Silicon's home directory), recompile Silicon (if possible) and then execute Silicon again.";

/// Conversion intentionally examines the result head only, as the source does;
/// callers decide which predecessor results to aggregate.
pub fn convert_to_viper_result_with<E>(
    result: &VerificationResult<E>,
    mut convert: impl FnMut(&E) -> AbstractError,
) -> ViperResult {
    result.with_kind(|kind| match kind {
        ResultKind::Success | ResultKind::Unreachable => ViperResult::Success,
        ResultKind::Failure(error) => ViperResult::Failure(vec![convert(error)]),
    })
}
pub fn convert_to_viper_result(result: &VerificationResult<AbstractError>) -> ViperResult {
    convert_to_viper_result_with(result, Clone::clone)
}
pub fn convert_to_viper_results(results: &[VerificationResult<AbstractError>]) -> Vec<ViperResult> {
    results.iter().map(convert_to_viper_result).collect()
}
pub fn condense_to_viper_result(results: &[VerificationResult<AbstractError>]) -> ViperResult {
    let errors: Vec<_> = convert_to_viper_results(results)
        .into_iter()
        .flat_map(|result| match result {
            ViperResult::Success => Vec::new(),
            ViperResult::Failure(errors) => errors,
        })
        .collect();
    if errors.is_empty() {
        ViperResult::Success
    } else {
        ViperResult::Failure(errors)
    }
}
