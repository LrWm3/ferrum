//! Shared interpreted-backend-type verification fixtures.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/testing/BackendTypeTest.scala
//! Status: fixture generators and verifier lifecycle/assertion matching implemented;
//! execution still requires a concrete backend and its solver.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpExtra, ExpKind, FieldAccess, PredicateAccess},
    program::{
        Declaration, Domain, DomainFunc, Field, FieldData, Function, FunctionData, LocalVarDecl,
        Member, Method, MethodData, Predicate, PredicateData, Program,
    },
    statement::{PredicateAccessPredicate, Stmt, StmtKind},
    r#type::Type,
    utility::backend_type_factories::{BVFactory, FloatFactory, RoundingMode},
};
use crate::verifier::{
    verification_error::{VerificationError, VerificationErrorKind},
    verification_result::{AbstractError, VerificationResult},
    verifier::{Verifier, VerifierError},
};
use std::sync::Arc;
fn meta() -> Metadata {
    Metadata::default()
}
fn exp(kind: ExpKind) -> Exp {
    Exp::new(kind, meta())
}
fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(kind, meta())
}
fn local(decl: &LocalVarDecl) -> Exp {
    exp(ExpKind::LocalVar(decl.local_var()))
}
fn decl(name: &str, typ: Type) -> LocalVarDecl {
    LocalVarDecl::new(name.into(), typ, meta())
}
fn backend(function: &DomainFunc, args: Vec<Exp>) -> Exp {
    Exp::with_extra(
        ExpKind::BackendFuncApp(function.name.clone(), args),
        meta(),
        ExpExtra {
            typ: Some(function.typ.clone()),
            domain_name: None,
            interpretation: function.interpretation.clone(),
        },
    )
}
fn bv(size: i32) -> BVFactory {
    BVFactory { size }
}
fn float(mant: i32, exponent: i32) -> FloatFactory {
    FloatFactory {
        mant,
        exp: exponent,
        rounding_mode: RoundingMode::RNE,
    }
}
fn int(value: impl Into<num_bigint::BigInt>) -> Exp {
    exp(ExpKind::IntLit(value.into()))
}
fn field_access(receiver: Exp, field: &Field) -> FieldAccess {
    FieldAccess::new(receiver, field.clone(), meta())
}
fn permission(field: FieldAccess, amount: Option<Exp>) -> Exp {
    exp(ExpKind::FieldAccessPredicate(field, amount))
}
fn full_perm() -> Exp {
    exp(ExpKind::FullPerm)
}
/// Source wrapper: variables are scoped by the method-body Seqn; parameters are
/// formal arguments and the helper method has no contracts or return variables.
pub fn wrap_in_program(
    domains: Vec<Domain>,
    statements: Vec<Stmt>,
    params: Vec<LocalVarDecl>,
    vars: Vec<LocalVarDecl>,
    fields: Vec<Field>,
) -> Program {
    let body = stmt(StmtKind::Seqn {
        statements,
        declarations: vars.into_iter().map(Declaration::Local).collect(),
    });
    let method = Method::new(MethodData {
        name: "test".into(),
        formal_args: params,
        formal_returns: vec![],
        pres: vec![],
        posts: vec![],
        body: Some(body),
        meta: meta(),
    });
    Program::new(
        domains,
        fields,
        vec![],
        vec![],
        vec![method],
        vec![],
        meta(),
    )
}
pub fn generate_type_combination_test(success: bool) -> (Program, Stmt) {
    let typ = if success {
        bv(23).typ()
    } else {
        float(23, 11).typ()
    };
    let first = decl("three", typ.clone());
    let second = decl("lol", Type::Set(Arc::new(typ)));
    let member = exp(ExpKind::AnySetContains(local(&first), local(&second)));
    let assertion = stmt(StmtKind::Assert(member.clone()));
    let mut body = Vec::new();
    if success {
        body.push(stmt(StmtKind::Inhale(member)));
    }
    body.push(assertion.clone());
    let domain = if success {
        bv(23).construct_domain(vec![])
    } else {
        float(23, 11).construct_domain(vec![])
    };
    (
        wrap_in_program(vec![domain], body, vec![first, second], vec![], vec![]),
        assertion,
    )
}
pub fn generate_field_type_test(success: bool) -> (Program, Stmt) {
    let typ = if success {
        float(23, 11).typ()
    } else {
        bv(23).typ()
    };
    let field = Field::new(FieldData {
        name: "f".into(),
        typ: typ.clone(),
        meta: meta(),
    });
    let first = decl("three", Type::Ref);
    let second = decl("lol", Type::Set(Arc::new(typ)));
    let access = field_access(local(&first), &field);
    let perm = permission(access.clone(), Some(full_perm()));
    let member = exp(ExpKind::AnySetContains(
        exp(ExpKind::FieldAccess(access)),
        local(&second),
    ));
    let assertion = stmt(StmtKind::Assert(member.clone()));
    let mut body = vec![stmt(StmtKind::Inhale(perm))];
    if success {
        body.push(stmt(StmtKind::Inhale(member)));
    }
    body.push(assertion.clone());
    let domain = if success {
        float(23, 11).construct_domain(vec![])
    } else {
        bv(23).construct_domain(vec![])
    };
    (
        wrap_in_program(vec![domain], body, vec![first, second], vec![], vec![field]),
        assertion,
    )
}
pub fn generate_float_qp_test() -> Program {
    let fp = float(24, 8);
    let field = Field::new(FieldData {
        name: "myfield".into(),
        typ: fp.typ(),
        meta: meta(),
    });
    let refs = decl("refs", Type::Set(Arc::new(Type::Ref)));
    let value = decl("val", fp.typ());
    let x = decl("x", Type::Ref);
    let member = exp(ExpKind::AnySetContains(local(&x), local(&refs)));
    let qp = exp(ExpKind::Forall(
        vec![x.clone()],
        vec![],
        exp(ExpKind::Implies(
            member.clone(),
            permission(field_access(local(&x), &field), None),
        )),
    ));
    let neq = exp(ExpKind::NeCmp(
        exp(ExpKind::FieldAccess(field_access(local(&x), &field))),
        local(&value),
    ));
    let info = exp(ExpKind::Forall(
        vec![x],
        vec![],
        exp(ExpKind::Implies(member, neq)),
    ));
    wrap_in_program(
        vec![fp.construct_domain(vec![])],
        vec![stmt(StmtKind::Inhale(qp)), stmt(StmtKind::Inhale(info))],
        vec![refs, value],
        vec![],
        vec![field],
    )
}
fn float_literals(
    fp: &FloatFactory,
    bv: &BVFactory,
) -> (DomainFunc, DomainFunc, Exp, Exp, Exp, Exp) {
    let from = bv.from_int("toBV32");
    let to = fp.from_bv("tofp");
    let make = |v| backend(&to, vec![backend(&from, vec![int(v)])]);
    (
        from.clone(),
        to.clone(),
        make(1081081856),
        make(1103888384),
        make(1105854464),
        make(0),
    )
}
pub fn generate_float_op_test(success: bool) -> (Program, Stmt) {
    let fp = float(24, 8);
    let bit = bv(32);
    let (from, to, first, second, result, zero) = float_literals(&fp, &bit);
    let eq = fp.eq("fp_eq");
    let add = fp.add("fp_add");
    let left = backend(&add, vec![first.clone(), second]);
    let right = backend(&add, vec![result, if success { zero } else { first }]);
    let assertion = stmt(StmtKind::Assert(backend(&eq, vec![left, right])));
    (
        wrap_in_program(
            vec![
                bit.construct_domain(vec![from]),
                fp.construct_domain(vec![to, eq, add]),
            ],
            vec![assertion.clone()],
            vec![],
            vec![],
            vec![],
        ),
        assertion,
    )
}
pub fn generate_float_min_max_test(success: bool) -> (Program, Stmt) {
    let fp = float(24, 8);
    let bit = bv(32);
    let (from, to, first, second, _, _) = float_literals(&fp, &bit);
    let eq = fp.eq("fp_eq");
    let min = fp.min("fp_min");
    let max = fp.max("fp_max");
    let left = backend(
        &eq,
        vec![
            backend(&min, vec![first.clone(), second.clone()]),
            first.clone(),
        ],
    );
    let right = backend(
        &eq,
        vec![backend(&max, vec![first, second.clone()]), second],
    );
    let conjunction = exp(ExpKind::And(left, right));
    let assertion = stmt(StmtKind::Assert(if success {
        conjunction
    } else {
        exp(ExpKind::Not(conjunction))
    }));
    (
        wrap_in_program(
            vec![
                bit.construct_domain(vec![from]),
                fp.construct_domain(vec![to, eq, min, max]),
            ],
            vec![assertion.clone()],
            vec![],
            vec![],
            vec![],
        ),
        assertion,
    )
}
pub fn generate_float_op_function_test(success: bool) -> (Program, Function, Exp) {
    let fp = float(24, 8);
    let bit = bv(32);
    let (from, to, first, second, result, zero) = float_literals(&fp, &bit);
    let eq = fp.eq("fp_eq");
    let add = fp.add("fp_add");
    let addition = backend(&add, vec![first.clone(), second]);
    let expected = backend(&add, vec![result, if success { zero } else { first }]);
    let post = backend(&eq, vec![exp(ExpKind::Result(fp.typ())), expected]);
    let function = Function::new(FunctionData {
        name: "test".into(),
        formal_args: vec![],
        typ: fp.typ(),
        pres: vec![],
        posts: vec![post.clone()],
        body: Some(addition),
        meta: meta(),
    });
    (
        Program::new(
            vec![
                fp.construct_domain(vec![to, eq, add]),
                bit.construct_domain(vec![from]),
            ],
            vec![],
            vec![function.clone()],
            vec![],
            vec![],
            vec![],
            meta(),
        ),
        function,
        post,
    )
}
pub fn generate_bv_op_test(success: bool) -> (Program, Stmt) {
    let bit = bv(23);
    let from = bit.from_int("toBV23");
    let one = backend(&from, vec![int(1)]);
    let two = backend(&from, vec![int(2)]);
    let three = backend(&from, vec![int(3)]);
    let result = decl("three", bit.typ());
    let assign = stmt(StmtKind::LocalVarAssign {
        lhs: result.local_var(),
        rhs: if success { three } else { one.clone() },
    });
    let xor = bit.xor("xorBV23");
    let assertion = stmt(StmtKind::Assert(exp(ExpKind::EqCmp(
        local(&result),
        backend(&xor, vec![one, two]),
    ))));
    (
        wrap_in_program(
            vec![bit.construct_domain(vec![from, xor])],
            vec![assign, assertion.clone()],
            vec![],
            vec![result],
            vec![],
        ),
        assertion,
    )
}
pub fn generate_bv_op_test2() -> Program {
    let bit = bv(23);
    let from = bit.from_int("toBV23");
    let one = backend(&from, vec![int(1)]);
    let two = backend(&from, vec![int(2)]);
    let result = decl("res", bit.typ());
    let operations = vec![
        bit.xor("xorBV23"),
        bit.xnor("xnorBV23"),
        bit.and("andBV23"),
        bit.nand("nandBV23"),
        bit.or("orBV23"),
        bit.nor("norBV23"),
        bit.add("addBV23"),
        bit.sub("subBV23"),
        bit.mul("mulBV23"),
        bit.smod("smodBV23"),
        bit.srem("sremBV23"),
        bit.udiv("udivBV23"),
        bit.urem("uremBV23"),
        bit.shl("shlBV23"),
        bit.lshr("lshrBV23"),
        bit.ashr("ashrBV23"),
    ];
    let body = operations
        .iter()
        .map(|operation| {
            stmt(StmtKind::LocalVarAssign {
                lhs: result.local_var(),
                rhs: backend(operation, vec![one.clone(), two.clone()]),
            })
        })
        .collect();
    let functions = std::iter::once(from).chain(operations).collect();
    wrap_in_program(
        vec![bit.construct_domain(functions)],
        body,
        vec![],
        vec![result],
        vec![],
    )
}
pub fn generate_predicate_test() -> Program {
    let fp = float(52, 12);
    let bit = bv(64);
    let from = bit.from_int("toBV64");
    let to = fp.from_bv("tofp");
    let field = Field::new(FieldData {
        name: "val_float".into(),
        typ: fp.typ(),
        meta: meta(),
    });
    let self_var = decl("self", Type::Ref);
    let access = field_access(local(&self_var), &field);
    let access_perm = permission(access.clone(), Some(full_perm()));
    let predicate = Predicate::new(PredicateData {
        name: "f64".into(),
        formal_args: vec![self_var.clone()],
        body: Some(access_perm.clone()),
        meta: meta(),
    });
    let value = backend(
        &to,
        vec![backend(&from, vec![int(4591870180066957722_i64)])],
    );
    let location = PredicateAccess::new(vec![local(&self_var)], predicate.name.clone(), meta());
    let pred_perm = PredicateAccessPredicate::new(location, None, meta());
    let body = stmt(StmtKind::Seqn {
        statements: vec![
            stmt(StmtKind::Inhale(access_perm)),
            stmt(StmtKind::FieldAssign {
                lhs: access,
                rhs: value,
            }),
            stmt(StmtKind::Fold(pred_perm.clone())),
            stmt(StmtKind::Exhale(exp(ExpKind::PredicateAccessPredicate(
                pred_perm,
            )))),
        ],
        declarations: vec![],
    });
    let method = Method::new(MethodData {
        name: "m_id".into(),
        formal_args: vec![],
        formal_returns: vec![self_var],
        pres: vec![],
        posts: vec![],
        body: Some(body),
        meta: meta(),
    });
    Program::new(
        vec![
            fp.construct_domain(vec![to]),
            bit.construct_domain(vec![from]),
        ],
        vec![field],
        vec![],
        vec![predicate],
        vec![method],
        vec![],
        meta(),
    )
}

pub enum Expected {
    Success,
    AssertFailed(Stmt),
    PostconditionViolated { expression: Exp, function: Function },
}
#[derive(Debug)]
pub enum HarnessError {
    Verifier(VerifierError),
    UnexpectedResult,
}
/// Source beforeAll: parse dummy.vpr once and start the supplied verifier.
pub fn start(verifier: &mut dyn Verifier) {
    verifier.parse_command_line(&["dummy.vpr".into()]);
    verifier.start();
}
pub fn stop(verifier: &mut dyn Verifier) {
    verifier.stop();
}
/// Source negative cases require exactly one concrete error with the original
/// structurally equal assertion or postcondition/function nodes.
pub fn verify_case(
    verifier: &mut dyn Verifier,
    program: &Program,
    expected: &Expected,
) -> Result<(), HarnessError> {
    let result = verifier.verify(program).map_err(HarnessError::Verifier)?;
    let matches = match (&result, expected) {
        (VerificationResult::Success, Expected::Success) => true,
        (VerificationResult::Failure(errors), expected) if errors.len() == 1 => match &errors[0] {
            AbstractError::Verification(error) => {
                match error.as_any().downcast_ref::<VerificationError>() {
                    Some(error) => match (&error.kind, expected) {
                        (
                            VerificationErrorKind::AssertFailed(actual),
                            Expected::AssertFailed(expected),
                        ) => actual == expected,
                        (
                            VerificationErrorKind::PostconditionViolated {
                                node,
                                member: Member::Function(actual),
                            },
                            Expected::PostconditionViolated {
                                expression,
                                function,
                            },
                        ) => node == expression && actual == function,
                        _ => false,
                    },
                    None => false,
                }
            }
            _ => false,
        },
        _ => false,
    };
    if matches {
        Ok(())
    } else {
        Err(HarnessError::UnexpectedResult)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_suite_builds_all_registered_cases() {
        let cases = cases();
        assert_eq!(cases.len(), 15);
        assert_eq!(cases.first().unwrap().name, "typeCombinationSuccess");
        assert_eq!(cases.last().unwrap().name, "predicateSuccess");
    }
    #[test]
    fn bv_fixture_keeps_assertion_and_interpreted_operations() {
        let (program, assertion) = generate_bv_op_test(false);
        assert_eq!(program.domains[0].functions.len(), 2);
        let StmtKind::Seqn {
            statements,
            declarations,
        } = program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("sequence")
        };
        assert_eq!(declarations.len(), 1);
        assert!(statements[1].same_node(&assertion));
        assert!(
            matches!(statements[0].kind(),StmtKind::LocalVarAssign{rhs,..} if matches!(rhs.kind(),ExpKind::BackendFuncApp(name,_) if name=="toBV23"))
        );
    }
}

pub struct BackendTypeCase {
    pub name: &'static str,
    pub program: Program,
    pub expected: Expected,
}
/// Source registration order, including every positive and negative fixture.
pub fn cases() -> Vec<BackendTypeCase> {
    let mut out = Vec::new();
    let (program, _) = generate_type_combination_test(true);
    out.push(BackendTypeCase {
        name: "typeCombinationSuccess",
        program,
        expected: Expected::Success,
    });
    let (program, assertion) = generate_type_combination_test(false);
    out.push(BackendTypeCase {
        name: "typeCombinationFail",
        program,
        expected: Expected::AssertFailed(assertion),
    });
    let (program, _) = generate_field_type_test(true);
    out.push(BackendTypeCase {
        name: "fieldTypeSuccess",
        program,
        expected: Expected::Success,
    });
    out.push(BackendTypeCase {
        name: "fieldQpTest",
        program: generate_float_qp_test(),
        expected: Expected::Success,
    });
    let (program, assertion) = generate_field_type_test(false);
    out.push(BackendTypeCase {
        name: "fieldTypeFail",
        program,
        expected: Expected::AssertFailed(assertion),
    });
    let (program, _) = generate_bv_op_test(true);
    out.push(BackendTypeCase {
        name: "bvOpSuccess",
        program,
        expected: Expected::Success,
    });
    let (program, assertion) = generate_bv_op_test(false);
    out.push(BackendTypeCase {
        name: "bvOpFail",
        program,
        expected: Expected::AssertFailed(assertion),
    });
    out.push(BackendTypeCase {
        name: "bvOp2Success",
        program: generate_bv_op_test2(),
        expected: Expected::Success,
    });
    let (program, _) = generate_float_op_test(true);
    out.push(BackendTypeCase {
        name: "floatOpSuccess",
        program,
        expected: Expected::Success,
    });
    let (program, assertion) = generate_float_op_test(false);
    out.push(BackendTypeCase {
        name: "floatOpFail",
        program,
        expected: Expected::AssertFailed(assertion),
    });
    let (program, _) = generate_float_min_max_test(true);
    out.push(BackendTypeCase {
        name: "floatMinMaxSuccess",
        program,
        expected: Expected::Success,
    });
    let (program, assertion) = generate_float_min_max_test(false);
    out.push(BackendTypeCase {
        name: "floatMinMaxFail",
        program,
        expected: Expected::AssertFailed(assertion),
    });
    let (program, _, _) = generate_float_op_function_test(true);
    out.push(BackendTypeCase {
        name: "floatOpFunctionSuccess",
        program,
        expected: Expected::Success,
    });
    let (program, function, expression) = generate_float_op_function_test(false);
    out.push(BackendTypeCase {
        name: "floatOpFunctionFail",
        program,
        expected: Expected::PostconditionViolated {
            expression,
            function,
        },
    });
    out.push(BackendTypeCase {
        name: "predicateSuccess",
        program: generate_predicate_test(),
        expected: Expected::Success,
    });
    out
}

/// Run every registered source case with one verifier start/stop cycle. Stop is
/// performed after a verification mismatch or execution error as well.
pub fn run_suite(verifier: &mut dyn Verifier) -> Result<(), (&'static str, HarnessError)> {
    start(verifier);
    let result = cases().into_iter().try_for_each(|case| {
        verify_case(verifier, &case.program, &case.expected).map_err(|error| (case.name, error))
    });
    stop(verifier);
    result
}
