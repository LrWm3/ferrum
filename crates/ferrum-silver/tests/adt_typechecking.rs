//! Regression coverage for repeated receiver inference in nested ADT accesses.
use ferrum_silver::{
    frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
    parser::parse_ast::{PIdnRef, PNodeHandle, PNodeKind, subnodes},
    plugin::{silver_plugin_manager::SilverPluginManager, standard::adt::adt_plugin::AdtPlugin},
};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

fn count_root_resolution(node: &PNodeHandle, visits: &Arc<AtomicUsize>) {
    let is_root = matches!(
        &node.read().unwrap().kind,
        PNodeKind::IdnRef(reference) if reference.name == "root"
    );
    if is_root {
        let visits = visits.clone();
        PIdnRef::filter_decls(
            node,
            Arc::new(move |_| {
                visits.fetch_add(1, Ordering::Relaxed);
                true
            }),
            |_| true,
        );
    }
    for child in subnodes(node).unwrap() {
        count_root_resolution(&child, visits);
    }
}

#[test]
fn nested_adt_access_checks_the_leaf_call_once() {
    // Both fields named `next` must be resolved against the receiver's ADT.
    // Keep the generic result and discriminator constraints in the same path.
    for (suffix, result_type, succeeds) in [
        ("value", "Int", true),
        ("isLeaf", "Bool", true),
        ("value", "Bool", false),
        ("isLeaf", "Int", false),
    ] {
        let source = format!(
            "adt Tree[T] {{ Leaf(value: T) Node(next: Tree[T]) }}
             adt Other {{ OtherNode(next: Other) }}
             function root(): Tree[Int]
             function get(): {result_type} {{ root(){}.{suffix} }}",
            ".next".repeat(8),
        );
        let mut phases = SilFrontendPhases::new(
            "nested-adt.vpr".into(),
            SilverPluginManager::new(vec![Box::new(AdtPlugin::default())]),
        );
        let program = phases.parse(&source).unwrap();
        let visits = Arc::new(AtomicUsize::new(0));
        count_root_resolution(program.node(), &visits);
        let result = phases.analyze(program);
        assert_eq!(result.is_ok(), succeeds, "{source}: {result:?}");
        // Count work instead of wall time. Previously every enclosing field
        // rechecked its receiver, multiplying these resolutions exponentially.
        let visits = visits.load(Ordering::Relaxed);
        assert!(visits > 0 && visits <= 16, "leaf resolved {visits} times");
    }
}
