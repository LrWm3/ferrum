//! Synthetic helpers and inhale splitting for impure-assume rewriting.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/ImpureAssumeRewriter.scala
//! Status: partial; helper definitions and inhale splitting are implemented. Whole-program
//! rewriting, inverse generation, contextual permissions and error back-translation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpExtra, ExpKind, LocalVar, Trigger},
    program::{AnyLocalVarDecl, DomainAxiom, DomainFunc, LocalVarDecl},
    statement::{Stmt, StmtKind},
    r#type::Type,
};
use std::collections::HashMap;
pub const DOMAIN_NAME: &str = "__ns__impure_assume_rewriter";
pub fn split(exp: &Exp) -> Vec<Exp> {
    if let ExpKind::And(a, b) = exp.kind() {
        let mut out = split(a);
        out.extend(split(b));
        out
    } else {
        vec![exp.clone()]
    }
}
pub fn rewrite_inhale(inhale: &Stmt) -> Result<Stmt, &'static str> {
    let StmtKind::Inhale(exp) = inhale.kind() else {
        return Err("expected inhale statement");
    };
    let statements = split(exp)
        .into_iter()
        .map(|e| Stmt::new(StmtKind::Inhale(e.clone()), e.metadata().clone()))
        .collect();
    Ok(Stmt::new(
        StmtKind::Seqn {
            statements,
            declarations: vec![],
        },
        inhale.metadata().clone(),
    ))
}
fn variable(name: String, typ: Type) -> Exp {
    Exp::new(
        ExpKind::LocalVar(LocalVar::new(name, typ, Metadata::default())),
        Metadata::default(),
    )
}
/// Construct the source helper and defining quantified axiom. Argument declarations
/// are prepended in each loop, while references in the conditional sum are appended.
pub fn generate_func(num_of_conds: i32) -> (DomainFunc, DomainAxiom) {
    let name = format!("__iar__assume_helper_{num_of_conds}");
    let mut condition_decls = Vec::new();
    let mut perm_decls = vec![LocalVarDecl::new(
        "p_0".into(),
        Type::Perm,
        Metadata::default(),
    )];
    let mut conditions = Vec::new();
    let mut permissions = Vec::new();
    for i in 0..num_of_conds {
        let n = format!("c_{}", i + 1);
        condition_decls.insert(
            0,
            LocalVarDecl::new(n.clone(), Type::Bool, Metadata::default()),
        );
        conditions.push(variable(n, Type::Bool));
    }
    for i in 0..num_of_conds {
        let n = format!("p_{}", i + 1);
        perm_decls.insert(
            0,
            LocalVarDecl::new(n.clone(), Type::Perm, Metadata::default()),
        );
        permissions.push(variable(n, Type::Perm));
    }
    let args: Vec<_> = condition_decls.into_iter().chain(perm_decls).collect();
    let mut body = variable("p_0".into(), Type::Perm);
    for (condition, permission) in conditions.into_iter().zip(permissions) {
        let zero = Exp::new(ExpKind::NoPerm, Metadata::default());
        let conditional = Exp::new(
            ExpKind::CondExp(condition, permission, zero),
            Metadata::default(),
        );
        body = Exp::new(ExpKind::PermAdd(body, conditional), Metadata::default());
    }
    let function = DomainFunc::new(crate::ast::program::DomainFuncData {
        name: name.clone(),
        formal_args: args.iter().cloned().map(AnyLocalVarDecl::Named).collect(),
        typ: Type::Perm,
        unique: false,
        interpretation: None,
        domain_name: DOMAIN_NAME.into(),
        meta: Metadata::default(),
    });
    let app = || {
        Exp::with_extra(
            ExpKind::DomainFuncApp(
                name.clone(),
                args.iter()
                    .map(|v| Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone()))
                    .collect(),
                HashMap::new(),
            ),
            Metadata::default(),
            ExpExtra {
                typ: Some(Type::Perm),
                domain_name: Some(DOMAIN_NAME.into()),
                interpretation: None,
            },
        )
    };
    let trigger = Trigger::new(vec![app()], Metadata::default());
    let equality = Exp::new(ExpKind::EqCmp(app(), body), Metadata::default());
    let axiom = Exp::new(
        ExpKind::Forall(args, vec![trigger], equality),
        Metadata::default(),
    );
    (
        function,
        DomainAxiom::new(crate::ast::program::DomainAxiomKind::Named {
            name: format!("{name}_axiom"),
            exp: axiom,
            domain_name: DOMAIN_NAME.into(),
            meta: Metadata::default(),
        }),
    )
}
