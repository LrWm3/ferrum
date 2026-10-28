//! Ferrum integration checks for source Decider symbolic logging (see PLAN.md).
//! Source: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Decider.scala
//! Exercises scope ordering, model-generation records and retained failure queries.
//! The injected test formatter does not establish JVM floating-point text parity.

use ferrum_silicon::{
    decider::{
        decider::{DeciderLogging, DefaultDecider},
        path_conditions::LayeredPathConditionStack,
        z3_prover_std_io,
    },
    logger::{
        log_config::LogConfig,
        records::data::{
            member_record::MemberRecord, predicate_record::PredicateRecord,
            prover_assert_record::ProverAssertRecord,
        },
        state_reporting::NativeStateRecordRenderer,
        symb_ex_logger::SymbExLog,
    },
    state::terms::{TermFactory, TermOptions},
};
use ferrum_silver::ast::program::{Member, Predicate, PredicateData};

#[test]
#[ignore = "requires Z3; set FERRUM_TEST_Z3"]
fn source_decider_records_and_failed_query_follow_continuation_order() {
    let z3 = std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let prover = z3_prover_std_io::new(
        "log-test".into(),
        z3_prover_std_io::settings(z3.into()),
        factory.clone(),
        |_| {},
    );
    let mut decider = DefaultDecider::new(prover, false, None, None, None);
    decider.start(None).unwrap();
    use ferrum_silicon::interfaces::decider::prover::TextEmitter;
    decider
        .prover
        .emit("(set-option :print-success true)")
        .unwrap();
    let root = SymbExLog::new(LogConfig::default());
    let renderer = NativeStateRecordRenderer { factory: &factory };
    let predicate = Predicate::new(PredicateData {
        name: "p".into(),
        formal_args: vec![],
        body: None,
        meta: Default::default(),
    });
    let log = root
        .open_member_scope(
            Member::Predicate(predicate),
            &LayeredPathConditionStack::new(false),
            &renderer,
        )
        .unwrap();
    decider.set_logging(Some(DeciderLogging {
        member: log.clone(),
        factory: factory.clone(),
        render_double: |n| n.to_string(),
    }));
    // Filtered overload emits no record; sequence overload emits even when empty.
    decider
        .assume([(factory.boolean(true), None)], false, false)
        .unwrap();
    decider.assume_sequence([], None).unwrap();
    assert!(decider.check(&factory.boolean(true), None).unwrap());
    assert!(
        !decider
            .assert_with(&factory.boolean(false), None, |value| value)
            .unwrap()
    );
    let records = log.records().unwrap();
    let labels: Vec<_> = records
        .iter()
        .filter_map(|r| r.as_data_record().map(|_| r.type_string()))
        .collect();
    assert_eq!(
        labels,
        [
            "predicate",
            "decider assume",
            "decider assert",
            "decider assert",
            "prover assert"
        ]
    );
    let prover_record = records
        .iter()
        .find_map(|r| r.as_any().downcast_ref::<ProverAssertRecord>())
        .unwrap();
    assert!(prover_record.statistics.lock().unwrap().is_some());
    let member = records[0]
        .as_any()
        .downcast_ref::<PredicateRecord>()
        .unwrap();
    assert_eq!(
        member.last_failed_query().unwrap(),
        Some(factory.boolean(false))
    );
    let before_model = log.records().unwrap().len();
    decider.generate_model(&factory).unwrap();
    let model_records = log.records().unwrap();
    assert_eq!(
        model_records[before_model..]
            .iter()
            .map(|r| r.type_string())
            .collect::<Vec<_>>(),
        ["prover assert", "open", "close"]
    );
    assert_eq!(
        member.last_failed_query().unwrap(),
        Some(factory.boolean(false))
    );
    assert!(
        decider
            .assert_with(&factory.boolean(true), None, |value| value)
            .unwrap()
    );
    assert_eq!(member.last_failed_query().unwrap(), None);
    decider.stop().unwrap();
    let before = log.records().unwrap().len();
    assert!(decider.check(&factory.boolean(false), None).is_err());
    let failed = log.records().unwrap();
    assert_eq!(
        failed[before..]
            .iter()
            .map(|r| r.type_string())
            .collect::<Vec<_>>(),
        ["decider assert", "open", "prover assert", "open"]
    );
    root.close().unwrap();
}
