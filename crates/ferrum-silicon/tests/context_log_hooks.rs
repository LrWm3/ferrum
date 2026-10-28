//! Ferrum symbolic logging integration checks described in PLAN.md.

use ferrum_silicon::{
    config::{Config, JoinMode},
    decider::{path_conditions::LayeredPathConditionStack, z3_prover_std_io},
    logger::{
        log_config::LogConfig,
        records::data::{
            consume_record::ConsumeRecord, data_record::FullStateRecordFactory,
            evaluate_record::EvaluateRecord, produce_record::ProduceRecord,
        },
        state_reporting::NativeStateRecordRenderer,
        symb_ex_logger::{NativeSymbExLogger, SymbExLog},
    },
    rules::{
        consumer::ConsumptionContext, evaluator::EvaluationContext, producer::ProductionContext,
    },
    state::terms::{TermFactory, TermOptions},
    verifier::{
        native_context::{NativeError, NativeOptions},
        verification_pool_manager::{NativeBranchState, native_method_worker},
    },
};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    program::{Member, Predicate, PredicateData, Program},
};
use std::{rc::Rc, sync::Arc};

#[test]
fn context_scope_hooks_capture_full_state_and_reject_missing_factory() {
    let config = Config::default();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let prover = z3_prover_std_io::new(
        "test".into(),
        z3_prover_std_io::settings("z3".into()),
        factory.clone(),
        |_| {},
    );
    let identifiers = prover.identifier_factory();
    let mut worker = native_method_worker(
        "test".into(),
        prover,
        identifiers,
        factory.clone(),
        NativeOptions::from_config(&config).unwrap(),
        &config,
    );
    let program = Program::new(
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Default::default(),
    );
    let mut state = NativeBranchState::new(
        program,
        Default::default(),
        Default::default(),
        JoinMode::Off,
        &factory,
        false,
        false,
    );
    state.under_join = true;
    let expr = Exp::new(ExpKind::TrueLit, Default::default());
    let root = SymbExLog::new(LogConfig::default());
    let member = Member::Predicate(Predicate::new(PredicateData {
        name: "p".into(),
        formal_args: vec![],
        body: None,
        meta: Default::default(),
    }));
    let renderer = NativeStateRecordRenderer { factory: &factory };
    let log = root
        .open_member_scope(member, &LayeredPathConditionStack::new(false), &renderer)
        .unwrap();
    worker.context.set_member_logging(Some(log.clone()), None);
    assert!(matches!(
        worker.context.open_evaluation_scope(&state, &expr),
        Err(NativeError::Unsupported(
            "active symbolic logger requires record factory"
        ))
    ));
    worker
        .context
        .set_member_logging(Some(log.clone()), Some(Rc::new(FullStateRecordFactory)));
    let evaluate = worker.context.open_evaluation_scope(&state, &expr).unwrap();
    let produce = worker.context.open_produce_scope(&state, &expr).unwrap();
    let consume = worker
        .context
        .open_consumption_scope(&state, &expr)
        .unwrap();
    let records = log.records().unwrap();
    let eval = records
        .iter()
        .find(|r| r.id() == evaluate.unwrap())
        .unwrap()
        .as_any()
        .downcast_ref::<EvaluateRecord<NativeBranchState>>()
        .unwrap();
    assert!(eval.state.as_ref().unwrap().under_join);
    assert!(
        records
            .iter()
            .any(|r| r.as_any().is::<ProduceRecord<NativeBranchState>>())
    );
    assert!(
        records
            .iter()
            .any(|r| r.as_any().is::<ConsumeRecord<NativeBranchState>>())
    );
    worker.context.close_consumption_scope(consume).unwrap();
    worker.context.close_produce_scope(produce).unwrap();
    worker.context.close_evaluation_scope(evaluate).unwrap();
    let implies = worker
        .context
        .open_implies_scope(&state, None, "ForPerm")
        .unwrap();
    let conditional = worker
        .context
        .open_conditional_scope(&state, &expr)
        .unwrap();
    let records = log.records().unwrap();
    let for_perm = records.iter().find(|r| r.id() == implies.unwrap()).unwrap()
        .as_any().downcast_ref::<ferrum_silicon::logger::records::data::implies_record::ImpliesRecord<NativeBranchState>>().unwrap();
    assert!(for_perm.value.is_none());
    assert_eq!(for_perm.env, "ForPerm");
    let cond = records.iter().find(|r| r.id() == conditional.unwrap()).unwrap()
        .as_any().downcast_ref::<ferrum_silicon::logger::records::data::cond_exp_record::CondExpRecord<NativeBranchState>>().unwrap();
    assert!(cond.value.as_ref().unwrap().same_node(&expr));
    assert_eq!(cond.env, "CondExp");
    worker.context.close_expression_scope(conditional).unwrap();
    worker.context.close_expression_scope(implies).unwrap();
    let imp = Exp::new(
        ExpKind::Implies(expr.clone(), expr.clone()),
        Default::default(),
    );
    let conditional = Exp::new(
        ExpKind::CondExp(expr.clone(), expr.clone(), expr.clone()),
        Default::default(),
    );
    let produce_cond = worker
        .context
        .open_production_conditional_scope(&state, &imp)
        .unwrap();
    let consume_cond = worker
        .context
        .open_consumption_conditional_scope(&state, &conditional)
        .unwrap();
    let records = log.records().unwrap();
    let produced = records.iter().find(|record| record.id() == produce_cond.unwrap()).unwrap()
        .as_any().downcast_ref::<ferrum_silicon::logger::records::data::implies_record::ImpliesRecord<NativeBranchState>>().unwrap();
    assert_eq!(produced.env, "produce");
    assert!(produced.value.as_ref().unwrap().same_node(&imp));
    let consumed = records.iter().find(|record| record.id() == consume_cond.unwrap()).unwrap()
        .as_any().downcast_ref::<ferrum_silicon::logger::records::data::cond_exp_record::CondExpRecord<NativeBranchState>>().unwrap();
    assert_eq!(consumed.env, "consume");
    assert!(consumed.value.as_ref().unwrap().same_node(&conditional));
    worker
        .context
        .close_consumption_conditional_scope(consume_cond)
        .unwrap();
    worker
        .context
        .close_production_conditional_scope(produce_cond)
        .unwrap();
    use ferrum_silicon::interfaces::verification::VerificationResult;
    use ferrum_silver::ast::statement::{Stmt, StmtKind};
    let statement = Stmt::new(
        StmtKind::Seqn {
            statements: vec![],
            declarations: vec![],
        },
        Default::default(),
    );
    ferrum_silicon::rules::executor::execute(&mut worker.context, state.clone(), &statement, &mut |_, _| {
        let records = log.records().unwrap();
        let record = records.iter().find(|r| r.as_any().is::<ferrum_silicon::logger::records::data::execute_record::ExecuteRecord<NativeBranchState>>()).unwrap();
        let execution = record.as_any().downcast_ref::<ferrum_silicon::logger::records::data::execute_record::ExecuteRecord<NativeBranchState>>().unwrap();
        assert!(execution.value.as_ref().unwrap().same_node(&statement));
        assert!(execution.state.as_ref().unwrap().under_join);
        assert!(records.iter().any(|r| r.as_any().downcast_ref::<ferrum_silicon::logger::records::scoping::close_scope_record::CloseScopeRecord>().is_some_and(|close| close.ref_id == record.id())));
        Ok(VerificationResult::success())
    }).unwrap();
    let disabled = NativeSymbExLogger::of_config(
        &config,
        Arc::new(ferrum_silver::reporter::reporter::NoopReporter),
        factory.clone(),
        |_| {},
        |_| {},
    )
    .unwrap();
    let disabled_member = disabled
        .open_member_scope(
            Member::Predicate(Predicate::new(PredicateData {
                name: "p".into(),
                formal_args: vec![],
                body: None,
                meta: Default::default(),
            })),
            &LayeredPathConditionStack::new(false),
            &renderer,
        )
        .unwrap();
    worker
        .context
        .set_member_logging(Some(disabled_member), None);
    assert_eq!(
        worker.context.open_evaluation_scope(&state, &expr).unwrap(),
        None
    );
}

#[test]
fn member_lifecycle_opens_and_closes_the_run_log() {
    use ferrum_silicon::supporters::{
        method_supporter::MethodVerificationServices,
        predicate_verification_unit::PredicateVerificationServices,
    };
    use ferrum_silver::{
        ast::program::{Method, MethodData},
        reporter::reporter::NoopReporter,
    };
    let config = Config::default();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let prover = z3_prover_std_io::new(
        "test".into(),
        z3_prover_std_io::settings("z3".into()),
        factory.clone(),
        |_| {},
    );
    let ids = prover.identifier_factory();
    let mut worker = native_method_worker(
        "test".into(),
        prover,
        ids,
        factory.clone(),
        NativeOptions::from_config(&config).unwrap(),
        &config,
    );
    let root = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
        LogConfig::default(),
    )));
    worker.context.set_logging_root(Some(root.clone()), None);
    let predicate = Predicate::new(PredicateData {
        name: "p".into(),
        formal_args: vec![],
        body: None,
        meta: Default::default(),
    });
    assert!(matches!(
        worker.context.open_predicate_verification(&predicate),
        Err(NativeError::Unsupported(
            "active symbolic logger requires record factory"
        ))
    ));
    assert!(root.logs().unwrap().is_empty());
    worker
        .context
        .set_logging_root(Some(root.clone()), Some(Rc::new(FullStateRecordFactory)));
    worker
        .context
        .open_predicate_verification(&predicate)
        .unwrap();
    let logs = root.logs().unwrap();
    assert_eq!(logs.len(), 1);
    assert_eq!(logs[0].records().unwrap().len(), 2);
    worker.context.close_predicate_verification().unwrap();
    assert_eq!(logs[0].records().unwrap().len(), 3);
    let method = Method::new(MethodData {
        name: "m".into(),
        formal_args: vec![],
        formal_returns: vec![],
        pres: vec![],
        posts: vec![],
        body: None,
        meta: Default::default(),
    });
    worker.context.open_method_log(&method).unwrap();
    worker.context.close_method_log().unwrap();
    assert_eq!(root.logs().unwrap().len(), 2);
    root.close().unwrap();
    let disabled = Arc::new(
        NativeSymbExLogger::of_config(&config, Arc::new(NoopReporter), factory, |_| {}, |_| {})
            .unwrap(),
    );
    worker
        .context
        .set_logging_root(Some(disabled.clone()), None);
    worker
        .context
        .open_predicate_verification(&predicate)
        .unwrap();
    worker.context.close_predicate_verification().unwrap();
    assert!(disabled.logs().unwrap().is_empty());
}

#[test]
#[ignore = "requires Z3; set FERRUM_TEST_Z3"]
fn joining_scope_captures_initial_state_and_closes_only_after_success() {
    use ferrum_silicon::{
        interfaces::{decider::prover::TextEmitter, verification::VerificationResult},
        logger::records::{
            scoping::close_scope_record::CloseScopeRecord,
            structural::joining_record::JoiningRecord,
        },
        rules::evaluator::EvaluationError,
    };
    use ferrum_silver::ast::{
        program::{Function, FunctionData},
        r#type::Type,
    };
    let z3 = std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    let config = Config::default();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let prover = z3_prover_std_io::new(
        "test".into(),
        z3_prover_std_io::settings(z3.into()),
        factory.clone(),
        |_| {},
    );
    let identifiers = prover.identifier_factory();
    let mut worker = native_method_worker(
        "test".into(),
        prover,
        identifiers,
        factory.clone(),
        NativeOptions::from_config(&config).unwrap(),
        &config,
    );
    worker.context.base.decider.start(None).unwrap();
    worker
        .context
        .base
        .decider
        .prover
        .emit("(set-option :print-success true)")
        .unwrap();
    let program = Program::new(
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Default::default(),
    );
    let state = NativeBranchState::new(
        program,
        Default::default(),
        Default::default(),
        JoinMode::Off,
        &factory,
        false,
        false,
    );
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
    worker
        .context
        .set_member_logging(Some(log.clone()), Some(Rc::new(FullStateRecordFactory)));
    let function = Function::new(FunctionData {
        name: "f".into(),
        formal_args: vec![],
        typ: Type::Bool,
        pres: vec![],
        posts: vec![],
        body: None,
        meta: Default::default(),
    });
    worker
        .context
        .join_function_application(
            state.clone(),
            &function,
            &[],
            None,
            &mut |_ctx, _state, _done| Ok(VerificationResult::success()),
            &mut |_, _, _, _| panic!("empty join must not continue"),
        )
        .unwrap();
    let records = log.records().unwrap();
    let joining = records
        .iter()
        .find_map(|r| {
            r.as_any()
                .downcast_ref::<JoiningRecord<NativeBranchState>>()
        })
        .unwrap();
    assert!(!joining.state.as_ref().unwrap().under_join);
    assert!(records.iter().any(|r| {
        r.as_any()
            .downcast_ref::<CloseScopeRecord>()
            .is_some_and(|c| c.ref_id == joining.header.id())
    }));
    let result = worker.context.join_function_application(
        state,
        &function,
        &[],
        None,
        &mut |_ctx, _state, _done| {
            Err(EvaluationError::Context(NativeError::Unsupported(
                "test error",
            )))
        },
        &mut |_, _, _, _| unreachable!(),
    );
    assert!(result.is_err());
    let records = log.records().unwrap();
    let joins: Vec<_> = records
        .iter()
        .filter_map(|r| {
            r.as_any()
                .downcast_ref::<JoiningRecord<NativeBranchState>>()
        })
        .collect();
    assert_eq!(joins.len(), 2);
    assert!(!records.iter().any(|r| {
        r.as_any()
            .downcast_ref::<CloseScopeRecord>()
            .is_some_and(|c| c.ref_id == joins[1].header.id())
    }));
    worker.context.base.decider.stop().unwrap();
}
