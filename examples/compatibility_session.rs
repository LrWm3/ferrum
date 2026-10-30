//! Ferrum compatibility session harness; see [PLAN.md](../PLAN.md) and [compatibility tooling](../tools/compatibility/README.md).
//! Status: focused tooling for repeated backend sessions and frontend result mapping.
use ferrum::silver::reporter::{
    message::{Message, SimpleMessageKind},
    reporter::{ReportError, Reporter},
};
use ferrum::{
    Session,
    silicon::{config::Config, extensions::try_block_parser_plugin::TryBlockParserPlugin},
    silver::{
        frontend::{
            frontend::FrontendPhases,
            sil_frontend::{
                SilFrontendPhases, report_configured_plugin_warnings,
                standard_plugin_manager_with_resolver,
            },
        },
        plugin::silver_plugin::SilverPlugin,
        verifier::verification_result::{AbstractError, VerificationResult},
    },
};
use serde_json::json;
use std::collections::HashSet;
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct CaptureReporter {
    warnings: Mutex<Vec<String>>,
    configuration: Mutex<Vec<String>>,
}
impl Reporter for CaptureReporter {
    fn name(&self) -> &str {
        "compatibility"
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let values = match message {
            Message::WarningsDuringParsing { warnings } => {
                warnings.iter().map(|w| w.readable_message()).collect()
            }
            Message::WarningsDuringTypechecking { warnings }
            | Message::WarningsDuringVerification { warnings } => warnings
                .iter()
                .map(|w| w.readable_message())
                .collect::<Result<Vec<_>, _>>()?,
            Message::Simple {
                kind: SimpleMessageKind::ConfigurationWarning,
                text,
            } => {
                self.configuration.lock().unwrap().push(text);
                return Ok(());
            }
            Message::Simple {
                kind: SimpleMessageKind::AnnotationWarning | SimpleMessageKind::InternalWarning,
                text,
            } => vec![text],
            _ => return Ok(()),
        };
        self.warnings.lock().unwrap().extend(values);
        Ok(())
    }
}

fn emit(
    path: &str,
    phase: &str,
    outcome: &str,
    errors: Vec<AbstractError>,
    reporter: &CaptureReporter,
    backend_warnings: &[String],
) {
    let warnings = reporter.warnings.lock().unwrap().clone();
    let mut rendered = Vec::new();
    for e in errors {
        match e.readable_message() {
            Ok(message) => rendered.push(
                json!({"id":e.full_id(), "position":e.position().to_string(), "message":message}),
            ),
            Err(error) => {
                println!(
                    "@@COMPAT@@{}",
                    json!({"case":path,"phase":phase,"outcome":"rendering_error","message":format!("{error:?}"),"warnings":warnings,"backend_warnings":backend_warnings})
                );
                return;
            }
        }
    }
    let errors = rendered;
    println!(
        "@@COMPAT@@{}",
        json!({"case":path,"phase":phase,"outcome":outcome,"errors":errors,"warnings":warnings,"backend_warnings":backend_warnings,"configuration_warnings":*reporter.configuration.lock().unwrap()})
    );
}
fn worker_options(options: &[String]) -> Vec<String> {
    let mut result = Vec::new();
    if !options.iter().any(|option| {
        option == "--numberOfParallelVerifiers"
            || option.starts_with("--numberOfParallelVerifiers=")
    }) {
        result.extend(["--numberOfParallelVerifiers".into(), "1".into()]);
    }
    result.extend_from_slice(options);
    result
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
        let mut options = vec!["--z3Exe".to_string(), args[0].clone(), "--disableCaches".into()];
        options.extend(worker_options(&args[1..separator])); options.push(args[separator + 1].clone());
        let config = Config::parse(&options).unwrap();
        let reporter = Arc::new(CaptureReporter::default());
        let mut session = Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
        'cases: for path in &args[separator + 1..] {
            reporter.warnings.lock().unwrap().clear();
            let source = std::fs::read_to_string(path).unwrap();
            report_configured_plugin_warnings(&config.frontend, reporter.as_ref()).unwrap();
            let plugins = standard_plugin_manager_with_resolver(&config.frontend, |name| Ok(match name {
                "viper.silicon.extensions.TryBlockParserPlugin" => Some(Box::new(TryBlockParserPlugin) as Box<dyn SilverPlugin>), _ => None
            })).unwrap();
            let mut p = SilFrontendPhases::new(path.into(), plugins);
            p.set_phase_reporter(reporter.clone());
            p.configure_consistency(&config.frontend); p.backend_type_format = Some("SMTLIB".into());
            p.retain_source_program = config.enable_debugging;
            macro_rules! phase { ($name:expr, $expr:expr) => { match $expr { Ok(x) => x, Err(e) => { let outcome = if e.is_empty() {"unknown_failure"} else {"failure"}; emit(path, $name, outcome, e, &reporter, &session.take_warnings()); continue; } } } }
            let parsed = phase!("parsing", p.parse(&source));
            if config.frontend.parse_only { emit(path, "parsing", "parsed", vec![], &reporter, &session.take_warnings()); continue; }
            let analyzed = phase!("semantic_analysis", p.analyze(parsed));
            let translated = phase!("translation", p.translate(analyzed));
            let checked = phase!("consistency", p.check_consistency(translated));
            let program = phase!("prepare_verification", p.prepare_verification(checked));
            let raw = match session.verify(&program, &[]) { Ok(x) => x, Err(e) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":e.to_string(),"warnings":*reporter.warnings.lock().unwrap(),"backend_warnings":session.take_warnings()})); break; } };
            let backend_warnings = session.take_warnings();
            let mapped = match p.map_verification(&program, raw) { Ok(x) => x, Err(e) => { let outcome = if e.is_empty() {"unknown_failure"} else {"failure"}; emit(path, "map_verification", outcome, e, &reporter, &backend_warnings); continue; } };
            let transformed = match mapped.transformed_result() { Ok(x) => x, Err(e) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":format!("{e:?}"),"warnings":*reporter.warnings.lock().unwrap(),"backend_warnings":backend_warnings})); break; } };
            let result = p.plugins.before_finish(transformed);
            match result {
                VerificationResult::Success => emit(path, "verification", "verified", vec![], &reporter, &backend_warnings),
                VerificationResult::Failure(errors) => {
                    let mut seen = HashSet::new();
                    let mut unique = vec![];
                    for e in errors {
                        let key = match e.transformed_error().and_then(|e| e.readable_message()) { Ok(x) => x, Err(err) => { println!("@@COMPAT@@{}", json!({"case":path,"outcome":"exception","message":format!("{err:?}"),"warnings":*reporter.warnings.lock().unwrap(),"backend_warnings":backend_warnings})); break 'cases; } };
                        if seen.insert(key) { unique.push(e); }
                    }
                    let outcome = if unique.is_empty() {"unknown_failure"} else {"failure"};
                    emit(path, "verification", outcome, unique, &reporter, &backend_warnings);
                }
            }
        }
        if let Err(error) = session.stop() { println!("@@COMPAT@@{}", json!({"outcome":"cleanup_error","message":error.to_string()})); }
    }).unwrap().join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn configuration_warnings_accumulate_across_resets() {
        let config = Config::parse(&[
            "--plugin=viper.silver.plugin.standard.adt.AdtPlugin".into(),
            "--ignoreFile".into(),
            "dummy.vpr".into(),
        ])
        .unwrap();
        let reporter = CaptureReporter::default();
        for _ in 0..2 {
            report_configured_plugin_warnings(&config.frontend, &reporter).unwrap();
        }
        let warnings = reporter.configuration.lock().unwrap();
        assert_eq!(warnings.len(), 2);
        assert_eq!(warnings[0], warnings[1]);
        assert!(warnings[0].contains("viper.silver.plugin.standard.adt.AdtPlugin"));
    }

    #[test]
    fn worker_default_does_not_duplicate_explicit_options() {
        let cases = [
            vec![],
            vec!["--numberOfParallelVerifiers", "2"],
            vec!["--numberOfParallelVerifiers=2"],
        ];
        for (index, args) in cases.into_iter().enumerate() {
            let args: Vec<String> = args.into_iter().map(str::to_owned).collect();
            let mut actual = worker_options(&args);
            actual.push("tests/fixtures/termination_function_spec_order.vpr".into());
            assert_eq!(
                Config::parse(&actual).unwrap().number_of_parallel_verifiers,
                if index == 0 { 1 } else { 2 }
            );
        }
        let duplicate = vec![
            "--numberOfParallelVerifiers".into(),
            "1".into(),
            "--numberOfParallelVerifiers=2".into(),
        ];
        assert_eq!(worker_options(&duplicate), duplicate);
    }
}
