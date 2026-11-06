//! Printing must preserve Boolean and separating-conjunction tree structure.
use ferrum_silver::{
    ast::{
        ast::Metadata,
        expression::{Exp, ExpKind, LocalVar, PredicateAccess},
        pretty::pretty_printer::pretty_expression,
        program::{LocalVarDecl, Program},
        statement::{PredicateAccessPredicate, StmtKind},
        r#type::Type,
        utility::nodes::{Node, subnodes},
    },
    frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
    plugin::silver_plugin_manager::SilverPluginManager,
};

fn exp(kind: ExpKind) -> Exp {
    Exp::new(kind, Metadata::default())
}

fn variable(name: &str, typ: Type) -> Exp {
    exp(ExpKind::LocalVar(LocalVar::new(
        name.into(),
        typ,
        Metadata::default(),
    )))
}

fn parse_expression(source: &str, pure: bool) -> Exp {
    let operation = if pure { "assert" } else { "inhale" };
    let source = format!(
        "predicate P(x: Ref)\nmethod test(a: Bool, b: Bool, c: Bool, d: Bool, x: Ref, n: Int) {{\n{operation} {source}\n}}\n"
    );
    let mut phases = SilFrontendPhases::new(
        "boolean-roundtrip.vpr".into(),
        SilverPluginManager::new(vec![]),
    );
    let parsed = phases.parse(&source).unwrap();
    let analyzed = phases.analyze(parsed).unwrap();
    let translated = phases.translate(analyzed).unwrap();
    let checked: Program = phases.check_consistency(translated).unwrap();
    let mut pending = vec![Node::Program(checked)];
    while let Some(node) = pending.pop() {
        if let Node::Stmt(statement) = &node {
            if let StmtKind::Assert(value) | StmtKind::Inhale(value) = statement.kind() {
                return value.clone();
            }
        }
        pending.extend(subnodes(&node).unwrap().into_iter().rev());
    }
    panic!("no expression in parsed fixture: {source}");
}

fn check(original: &Exp) {
    let printed = pretty_expression(original).unwrap();
    let parsed = parse_expression(&printed, original.is_pure());
    // Exp equality compares kinds/operands, excluding source metadata.
    assert!(
        parsed == *original,
        "AST grouping changed when printing {printed}"
    );
}

fn trees(leaves: &[Exp], operator: fn(Exp, Exp) -> ExpKind) -> Vec<Exp> {
    if leaves.len() == 1 {
        return vec![leaves[0].clone()];
    }
    let mut result = Vec::new();
    for split in 1..leaves.len() {
        for left in trees(&leaves[..split], operator) {
            for right in trees(&leaves[split..], operator) {
                result.push(exp(operator(left.clone(), right)));
            }
        }
    }
    result
}

#[test]
fn conjunction_trees_roundtrip() {
    let leaves = ["a", "b", "c", "d"].map(|name| variable(name, Type::Bool));
    let expressions = trees(&leaves, ExpKind::And);
    assert_eq!(expressions.len(), 5);
    expressions.iter().for_each(check);
}

#[test]
fn disjunction_trees_roundtrip() {
    let leaves = ["a", "b", "c", "d"].map(|name| variable(name, Type::Bool));
    trees(&leaves, ExpKind::Or).iter().for_each(check);
}

#[test]
fn mixed_permission_conjunction_trees_roundtrip() {
    let permission = exp(ExpKind::PredicateAccessPredicate(
        PredicateAccessPredicate::new(
            PredicateAccess::new(
                vec![variable("x", Type::Ref)],
                "P".into(),
                Metadata::default(),
            ),
            Some(exp(ExpKind::FullPerm)),
            Metadata::default(),
        ),
    ));
    let leaves = [
        permission,
        variable("a", Type::Bool),
        variable("b", Type::Bool),
        variable("c", Type::Bool),
    ];
    trees(&leaves, ExpKind::And).iter().for_each(check);
}

#[test]
fn definedness_guard_and_mixed_precedence_roundtrip() {
    let guard = exp(ExpKind::NeCmp(
        variable("n", Type::Int),
        exp(ExpKind::IntLit(0.into())),
    ));
    let division = exp(ExpKind::GtCmp(
        exp(ExpKind::Div(
            exp(ExpKind::IntLit(1.into())),
            variable("n", Type::Int),
        )),
        exp(ExpKind::IntLit(0.into())),
    ));
    let leaves = [guard, division, variable("a", Type::Bool)];
    trees(&leaves, ExpKind::And).iter().for_each(check);
    check(&exp(ExpKind::And(
        exp(ExpKind::Or(
            variable("a", Type::Bool),
            variable("b", Type::Bool),
        )),
        variable("c", Type::Bool),
    )));
}

#[test]
fn let_scope_is_preserved() {
    let local = LocalVarDecl::new("saved".into(), Type::Bool, Metadata::default());
    let body = exp(ExpKind::And(
        variable("saved", Type::Bool),
        variable("c", Type::Bool),
    ));
    let binding = exp(ExpKind::Let(
        local,
        exp(ExpKind::And(
            variable("a", Type::Bool),
            variable("b", Type::Bool),
        )),
        body,
    ));
    check(&exp(ExpKind::And(binding, variable("d", Type::Bool))));
}
