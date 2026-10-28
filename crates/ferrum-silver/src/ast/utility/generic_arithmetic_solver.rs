//! Generic isolation of a variable in integer addition/subtraction expressions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericArithmeticSolver.scala
//! Status: implemented generic algorithm; concrete expression adapters are separate.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

pub trait ArithmeticAdapter {
    type Exp: Clone + Eq;
    type Var: Clone + Eq;
    type Type;
    type Error;
    fn render_exp(&self, exp: &Self::Exp) -> Result<String, Self::Error>;
    fn render_var(&self, var: &Self::Var) -> Result<String, Self::Error>;
    fn render_type(&self, typ: &Self::Type) -> Result<String, Self::Error>;
    fn var_exp(&self, var: &Self::Var) -> Self::Exp;
    fn typ(&self, exp: &Self::Exp) -> Result<Self::Type, Self::Error>;
    fn is_int(&self, typ: &Self::Type) -> bool;
    fn occurrences(&self, node: &Self::Exp, target: &Self::Exp) -> Result<usize, Self::Error>;
    fn contains(&self, node: &Self::Exp, target: &Self::Exp) -> Result<bool, Self::Error>;
    fn plus(&self, left: Self::Exp, right: Self::Exp) -> Self::Exp;
    fn minus(&self, left: Self::Exp, right: Self::Exp) -> Self::Exp;
    fn as_plus(&self, exp: &Self::Exp) -> Option<(Self::Exp, Self::Exp)>;
    fn as_minus(&self, exp: &Self::Exp) -> Option<(Self::Exp, Self::Exp)>;
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolverResult<E, V> {
    PreSolvingError(String),
    SolvingFailure { lhs: E, rhs: E, y: V },
    SolvingSuccess { y: V, rhs: E },
}
impl<E, V> SolverResult<E, V> {
    pub fn readable_message<A: ArithmeticAdapter<Exp = E, Var = V>>(
        &self,
        adapter: &A,
    ) -> Result<String, A::Error> {
        Ok(match self {
            Self::PreSolvingError(s) => s.clone(),
            Self::SolvingFailure { lhs, rhs, y } => format!(
                "Solving for {} failed at {} == {}",
                adapter.render_var(y)?,
                adapter.render_exp(lhs)?,
                adapter.render_exp(rhs)?
            ),
            Self::SolvingSuccess { y, rhs } => format!(
                "Solving succeeded with {} == {}",
                adapter.render_var(y)?,
                adapter.render_exp(rhs)?
            ),
        })
    }
}
pub fn solve<A: ArithmeticAdapter>(
    adapter: &A,
    lhs: A::Var,
    rhs: A::Exp,
    y: A::Var,
) -> Result<SolverResult<A::Exp, A::Var>, A::Error> {
    let lhs_exp = adapter.var_exp(&lhs);
    let y_exp = adapter.var_exp(&y);
    let lhs_type = adapter.typ(&lhs_exp)?;
    if !adapter.is_int(&lhs_type) {
        return Ok(SolverResult::PreSolvingError(format!(
            "LHS must be an int, but found {} of type {}",
            adapter.render_var(&lhs)?,
            adapter.render_type(&lhs_type)?
        )));
    }
    let rhs_type = adapter.typ(&rhs)?;
    if !adapter.is_int(&rhs_type) {
        return Ok(SolverResult::PreSolvingError(format!(
            "RHS must be an int, but found {} of sort {}",
            adapter.render_exp(&rhs)?,
            adapter.render_type(&rhs_type)?
        )));
    }
    let occurrences = adapter.occurrences(&rhs, &y_exp)?;
    if lhs == y {
        return Ok(SolverResult::PreSolvingError(format!(
            "The LHS must be different from {}",
            adapter.render_var(&y)?
        )));
    }
    if occurrences != 1 {
        return Ok(SolverResult::PreSolvingError(format!(
            "{} must occur exactly once in the RHS, but it occurs {occurrences} in {}",
            adapter.render_var(&y)?,
            adapter.render_exp(&rhs)?
        )));
    }
    let (mut lhs, mut rhs) = (lhs_exp, rhs);
    loop {
        if rhs == y_exp {
            return Ok(SolverResult::SolvingSuccess { y, rhs: lhs });
        }
        if let Some((left, right)) = adapter.as_plus(&rhs) {
            if adapter.contains(&left, &y_exp)? {
                lhs = adapter.minus(lhs, right);
                rhs = left;
            } else {
                lhs = adapter.minus(lhs, left);
                rhs = right;
            }
        } else if let Some((left, right)) = adapter.as_minus(&rhs) {
            if adapter.contains(&left, &y_exp)? {
                lhs = adapter.plus(lhs, right);
                rhs = left;
            } else {
                lhs = adapter.minus(left, lhs);
                rhs = right;
            }
        } else {
            return Ok(SolverResult::SolvingFailure { lhs, rhs, y });
        }
    }
}
