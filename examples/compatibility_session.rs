//! Ferrum compatibility session harness; see [PLAN.md](../PLAN.md) and [compatibility tooling](../tools/compatibility/README.md).
//! Status: focused tooling for repeated backend sessions and frontend result mapping.
use ferrum::{
    Session,
    silicon::{config::Config, extensions::try_block_parser_plugin::TryBlockParserPlugin},
    silver::{
        frontend::{
            frontend::FrontendPhases,
            sil_frontend::{SilFrontendPhases, standard_plugin_manager_with_resolver},
        },
        plugin::silver_plugin::SilverPlugin,
        verifier::verification_result::{AbstractError, VerificationResult},
    },
};
use serde_json::json;
use std::collections::HashSet;

fn warnings(p: &SilFrontendPhases) -> Vec<String> {
    p.parsing_warnings
        .iter()
        .map(|w| w.readable_message())
        .chain(
            p.typechecking_warnings
                .iter()
                .map(|w| w.readable_message().unwrap_or_else(|_| w.full_id().into())),
        )
        .collect()
}
fn emit(path: &str, phase: &str, outcome: &str, errors: Vec<AbstractError>, warnings: Vec<String>) {
    let mut rendered = Vec::new();
    for e in errors {
        match e.readable_message() {
            Ok(message) => rendered.push(
                json!({"id":e.full_id(), "position":e.position().to_string(), "message":message}),
            ),
            Err(error) => {
                println!(
                    "@@COMPAT@@{}",
                    json!({"case":path,"phase":phase,"outcome":"rendering_error","message":format!("{error:?}"),"warnings":warnings})
                );
                return;
            }
        }
    }
    let errors = rendered;
    println!(
        "@@COMPAT@@{}",
        json!({"case":path,"phase":phase,"outcome":outcome,"errors":errors,"warnings":warnings})
    );
}
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert!(args.len() >= 2, "z3 path, then input files required");
    let separator = args
        .iter()
        .position(|arg| arg == "--")
        .expect("flags must be followed by -- and inputs");
    assert!(separator + 1 < args.len(), "missing input");
    std::thread::Builder::new().stack_size(ferrum::VERIFICATION_STACK_SIZE).spawn(move || {
        let mut options = vec!["--z3Exe".to_string(), args[0].clone(), "--disableCaches".into(), "--numberOfParallelVerifiers".into(), "1".into()];
        options.extend_from_slice(&args[1..separator]); options.push(args[separator + 1].clone());
        let config = Config::parse(&options).unwrap();
        let mut session = Session::new(config.clone()).unwrap();
        'cases: for path in &args[separator + 1..] {
            let source = std::fs::read_to_string(path).unwrap();
            let plugins = standard_plugin_manager_with_resolver(&config.frontend, |name| Ok(match name {
                "viper.silicon.extensions.TryBlockParserPlugin" => Some(Box::new(TryBlockParserPlugin) as Box<dyn SilverPlugin>), _ => None
            })).unwrap();
            let mut p = SilFrontendPhases::new(path.into(), plugins);
            p.configure_consistency(&config.frontend); p.backend_type_format = Some("SMTLIB".into());
            p.retain_source_program = config.enable_debugging;
            macro_rules! phase { ($name:expr, $expr:expr) => { match $expr { Ok(x) => x, Err(e) => { let outcome = if e.is_empty() {"unknown_failure"} else {"failure"}; emit(path, $name, outcome, e, warnings(&p)); continue; } } } }
            let parsed = phase!("parsing", p.parse(&source));
            if config.frontend.parse_only { emit(path, "parsing", "parsed", vec![], warnings(&p)); continue; }
            let analyzed = phase!("semantic_analysis", p.analyze(parsed));
            let translated = phase!("translation", p.translate(analyzed));
            let checked = phase!("consistency", p.check_consistency(translated));
            let program = phase!("prepare_verification", p.prepare_verification(checked));
            let raw = match session.verify(&program, &[]) { Ok(x) => x, Err(e) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":e.to_string(),"warnings":warnings(&p)})); break; } };
            let mut all_warnings = warnings(&p); all_warnings.extend(session.take_warnings());
            let mapped = match p.map_verification(&program, raw) { Ok(x) => x, Err(e) => { let outcome = if e.is_empty() {"unknown_failure"} else {"failure"}; emit(path, "map_verification", outcome, e, all_warnings); continue; } };
            let transformed = match mapped.transformed_result() { Ok(x) => x, Err(e) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":format!("{e:?}"),"warnings":all_warnings})); break; } };
            let result = p.plugins.before_finish(transformed);
            match result {
                VerificationResult::Success => emit(path, "verification", "verified", vec![], all_warnings),
                VerificationResult::Failure(errors) => {
                    let mut seen = HashSet::new();
                    let mut unique = vec![];
                    for e in errors {
                        let key = match e.transformed_error().and_then(|e| e.readable_message()) { Ok(x) => x, Err(err) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":format!("{err:?}")})); break 'cases; } };
                        if seen.insert(key) { unique.push(e); }
                    }
                    let outcome = if unique.is_empty() {"unknown_failure"} else {"failure"};
                    emit(path, "verification", outcome, unique, all_warnings);
                }
            }
        }
        if let Err(error) = session.stop() { println!("@@COMPAT@@{}", json!({"outcome":"cleanup_error","message":error.to_string()})); }
    }).unwrap().join().unwrap();
}
