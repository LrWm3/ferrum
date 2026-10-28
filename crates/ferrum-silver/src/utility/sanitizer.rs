//! Capture-avoiding expression replacement from the source sanitizer.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Sanitizer.scala
//! Status: partial; expression replacement and bound-variable renaming are implemented.
//! Parse-program sanitizer awaits parser scope analysis and typed parser reconstruction.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::{Exp, ExpKind, FieldAccess, LocalVar, PredicateAccess, Trigger},
    program::LocalVarDecl,
};
use std::collections::{HashMap, HashSet};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SanitizeError {
    ConflictingReplacementAndRename,
    Extension,
}
pub fn fresh(name: &str, scope: &HashSet<String>) -> String {
    if !scope.contains(name) {
        return name.into();
    }
    let mut number = 0u64;
    loop {
        let result = format!("{name}${number}");
        if !scope.contains(&result) {
            return result;
        }
        number += 1;
    }
}
#[derive(Clone)]
struct Context {
    scope: HashSet<String>,
    replacements: HashMap<String, Exp>,
    renaming: HashMap<String, String>,
}
fn quantifier_context(vars: &[LocalVarDecl], context: &Context) -> Result<Context, SanitizeError> {
    let mut next = context.clone();
    let bounds: HashSet<_> = vars.iter().map(|v| v.name.clone()).collect();
    let intersection: Vec<_> = bounds.intersection(&next.scope).cloned().collect();
    next.scope.extend(bounds);
    for name in intersection {
        let new_name = fresh(&name, &next.scope);
        next.renaming.insert(name, new_name.clone());
        next.scope.insert(new_name);
    }
    if next
        .replacements
        .keys()
        .any(|k| next.renaming.contains_key(k))
    {
        return Err(SanitizeError::ConflictingReplacementAndRename);
    }
    Ok(next)
}
fn renamed_decl(d: &LocalVarDecl, context: &Context) -> LocalVarDecl {
    if let Some(name) = context.renaming.get(&d.name) {
        LocalVarDecl::new(name.clone(), d.typ.clone(), d.meta.clone())
    } else {
        d.clone()
    }
}
fn rewrite(e: &Exp, context: &Context, skip_root_rewrite: bool) -> Result<Exp, SanitizeError> {
    if !skip_root_rewrite {
        if let ExpKind::LocalVar(v) = e.kind() {
            if let Some(name) = context.renaming.get(&v.name) {
                return Ok(Exp::new(
                    ExpKind::LocalVar(LocalVar::new(name.clone(), v.typ.clone(), v.meta.clone())),
                    v.meta.clone(),
                ));
            }
            if let Some(replacement) = context.replacements.get(&v.name) {
                let cleared = Context {
                    scope: context.scope.clone(),
                    replacements: HashMap::new(),
                    renaming: HashMap::new(),
                };
                return rewrite(replacement, &cleared, true);
            }
        }
    }
    let active = match e.kind() {
        ExpKind::Forall(vars, ..) | ExpKind::Exists(vars, ..) | ExpKind::ForPerm(vars, ..) => {
            quantifier_context(vars, context)?
        }
        _ => context.clone(),
    };
    let child = |x: &Exp| rewrite(x, &active, false);
    let mapped = e.map_expression_children(
        &mut |x| child(x),
        &mut |extension| {
            let saved = std::cell::RefCell::new(None);
            let result = extension.0.map_expressions(&|child| {
                rewrite(child, &active, false).map_err(|error| {
                    *saved.borrow_mut() = Some(error);
                    crate::verifier::verification_result::DiagnosticError::Unsupported(
                        "sanitizer extension child",
                    )
                })
            });
            match result {
                Ok(value) => Ok(value),
                Err(_) => Err(saved.into_inner().unwrap_or(SanitizeError::Extension)),
            }
        },
        &mut |f| {
            let r = child(&f.receiver)?;
            Ok(if r == f.receiver {
                f.clone()
            } else {
                FieldAccess::new(r, f.field.clone(), f.meta.clone())
            })
        },
        &mut |p| {
            let args = p.args.iter().map(child).collect::<Result<Vec<_>, _>>()?;
            Ok(if args == p.args {
                p.clone()
            } else {
                PredicateAccess::new(args, p.predicate_name.clone(), p.meta.clone())
            })
        },
        &mut |t| {
            let exps = t.exps.iter().map(child).collect::<Result<Vec<_>, _>>()?;
            Ok(if exps == t.exps {
                t.clone()
            } else {
                Trigger::new(exps, t.meta.clone())
            })
        },
    )?;
    // The generic expression mapper intentionally leaves declarations untouched.
    let kind = match mapped.kind() {
        ExpKind::Forall(vars, triggers, body) => Some(ExpKind::Forall(
            vars.iter().map(|v| renamed_decl(v, &active)).collect(),
            triggers.clone(),
            body.clone(),
        )),
        ExpKind::Exists(vars, triggers, body) => Some(ExpKind::Exists(
            vars.iter().map(|v| renamed_decl(v, &active)).collect(),
            triggers.clone(),
            body.clone(),
        )),
        ExpKind::ForPerm(vars, resource, body) => Some(ExpKind::ForPerm(
            vars.iter().map(|v| renamed_decl(v, &active)).collect(),
            resource.clone(),
            body.clone(),
        )),
        ExpKind::Let(var, value, body) => Some(ExpKind::Let(
            renamed_decl(var, &active),
            value.clone(),
            body.clone(),
        )),
        _ => None,
    };
    if let Some(kind) = kind {
        if &kind != mapped.kind() {
            return Ok(Exp::with_extra(
                kind,
                mapped.metadata().clone(),
                mapped.0.extra.clone(),
            ));
        }
    }
    Ok(mapped)
}
pub fn replace_free_variables_in_expression(
    expression: &Exp,
    replacements: HashMap<String, Exp>,
    scope: HashSet<String>,
) -> Result<Exp, SanitizeError> {
    rewrite(
        expression,
        &Context {
            scope,
            replacements,
            renaming: HashMap::new(),
        },
        false,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ast::Metadata, r#type::Type};
    #[test]
    fn substitution_descends_through_extension_expression_children() {
        use crate::plugin::standard::predicateinstance::predicate_instance_ast_extension::PredicateInstance;
        let m = Metadata::default();
        let x = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, m.clone())),
            m.clone(),
        );
        let replacement = Exp::new(ExpKind::IntLit(7.into()), m.clone());
        let ext = PredicateInstance {
            predicate: "p".into(),
            args: vec![x],
            meta: m,
        }
        .expression();
        let result = replace_free_variables_in_expression(
            &ext,
            HashMap::from([("x".into(), replacement.clone())]),
            HashSet::new(),
        )
        .unwrap();
        let ExpKind::Extension(handle) = result.kind() else {
            panic!("extension")
        };
        let value = handle
            .0
            .as_any()
            .downcast_ref::<PredicateInstance>()
            .unwrap();
        assert_eq!(value.args, vec![replacement]);
    }
    #[test]
    fn quantifier_renames_conflicting_binder_and_preserves_replacement() {
        let m = Metadata::default();
        let var = |name: &str| {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), Type::Int, m.clone())),
                m.clone(),
            )
        };
        let body = Exp::new(ExpKind::Add(var("x"), var("y")), m.clone());
        let quantifier = Exp::new(
            ExpKind::Forall(
                vec![LocalVarDecl::new("x".into(), Type::Int, m.clone())],
                vec![],
                body,
            ),
            m.clone(),
        );
        let result = replace_free_variables_in_expression(
            &quantifier,
            HashMap::from([("y".into(), var("x"))]),
            HashSet::from(["x".into()]),
        )
        .unwrap();
        let ExpKind::Forall(vars, _, body) = result.kind() else {
            panic!("forall")
        };
        assert_eq!(vars[0].name, "x$0");
        let ExpKind::Add(a, b) = body.kind() else {
            panic!("addition")
        };
        assert!(matches!(a.kind(),ExpKind::LocalVar(v) if v.name == "x$0"));
        assert!(matches!(b.kind(),ExpKind::LocalVar(v) if v.name == "x"));
    }
}
