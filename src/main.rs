//! Upstream:
//! Ferrum-owned CLI assembly described in PLAN.md. Runner behavior is referenced from:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Provide the ferrum executable that configures and runs the native verification pipeline.
//!
//! Planned Rust structure:
//! Keep main as argument capture, reporter/logging setup, facade invocation and exit handling.
//! Model SiliconRunnerInstance.runMain's orchestration through the library session, leaving
//! option definitions in ferrum_silicon::config and frontend phases in Silver.
//!
//! Behavior to preserve:
//! Preserve help/version/configuration handling, diagnostic delivery, source loading and
//! verification result interpretation. Upstream starts with failure exit status and changes it
//! only after reaching verification successfully; keep this distinction from merely parsing
//! input. Ensure cleanup on normal results, failures, exceptions and timeouts. Preserve optional
//! submission/reporting hooks only according to their explicit configuration and native design.
//!
//! Integration:
//! src/lib.rs, ferrum_silicon::{silicon,config}, ferrum_silver::{frontend,reporter,logger},
//! and solver dependency discovery through Silicon's decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for replacing JVM startup and exception handling with native
//! lifecycle/result handling. Exact CLI parsing and logging libraries are not chosen here.
//!
//! Open decisions:
//! Reconcile CLI compatibility, intentional Ferrum naming, signal cancellation and help/version
//! exit behavior with the configuration port; record adopted differences before implementation.
//!
//! Status: configuration, frontend and native solver session connected; unsupported
//! features report execution failure.

fn main() -> std::process::ExitCode {
    use ferrum::{RunOutcome, silver::verifier::verification_result::VerificationResult};
    let started = std::time::Instant::now();
    let args = match std::env::args_os()
        .skip(1)
        .map(|a| a.into_string())
        .collect::<Result<Vec<_>, _>>()
    {
        Ok(args) => args,
        Err(_) => {
            eprintln!("Arguments must be UTF-8");
            return std::process::ExitCode::from(2);
        }
    };
    let config = match ferrum::silicon::config::Config::parse(&args) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("{error}");
            return std::process::ExitCode::from(2);
        }
    };
    if config.frontend.print_help {
        println!(
            "Ferrum native Viper port\nUsage: ferrum [options] <file.vpr>\n\n  --parseOnly                 Parse source without verification\n  --z3Exe <path>              Select the Z3 executable\n  --prover <Z3|cvc5|Z3-API>   Select solver (API needs native-z3 feature)\n  --assertTimeout <ms>        Limit each assertion query\n  --proverEnableTimeBounds    Use time bounds instead of resource bounds\n  --numberOfErrorsToReport N  Error limit per member (0: unlimited)\n  --numberOfParallelVerifiers N  Verify members with N workers\n  --disableDefaultPlugins    Disable default source transformations\n\nPort in progress; unconnected features return an explicit error."
        );
        return std::process::ExitCode::SUCCESS;
    }
    if config.frontend.print_version {
        println!("ferrum {}", env!("CARGO_PKG_VERSION"));
        return std::process::ExitCode::SUCCESS;
    }
    if config.frontend.dependencies {
        println!("The following dependencies are used:");
        for dependency in [
            ferrum::silicon::decider::z3_prover_std_io::profile(),
            ferrum::silicon::decider::cvc5_prover_std_io::profile(),
        ] {
            println!(
                "  {} {}, located at {}.",
                dependency.name, dependency.minimum_version, dependency.dependency_url
            );
        }
    }
    let time_info = !config.frontend.no_timing;
    let catch_exceptions = !config.disable_catching_exceptions;
    let debug_config = config.enable_debugging.then(|| config.clone());
    let report = match ferrum::run_file(config) {
        Ok(report) => report,
        Err(ferrum::FerrumError::SourceException(_)) if catch_exceptions => {
            return std::process::ExitCode::from(1);
        }
        Err(error) => {
            eprintln!("{error}");
            return std::process::ExitCode::from(2);
        }
    };
    for warning in report.warnings {
        eprintln!("{warning}");
    }
    let time = if time_info {
        let milliseconds = i64::try_from(started.elapsed().as_millis()).unwrap_or(i64::MAX);
        let elapsed =
            ferrum::silver::reporter::format::package::format_millis_readably(milliseconds)
                .expect("nonnegative elapsed duration has a representable residual timestamp");
        format!(" in {elapsed}")
    } else {
        String::new()
    };
    if let Some(config) = debug_config {
        let errors = match &report.outcome {
            RunOutcome::Verified(VerificationResult::Failure(errors)) => Some(errors.clone()),
            RunOutcome::Verified(VerificationResult::Success) => Some(Vec::new()),
            RunOutcome::Parsed => None,
        };
        if let Some(errors) = errors {
            if let Err(error) = ferrum::debug_failures(config, errors) {
                eprintln!("{error}");
                return std::process::ExitCode::from(2);
            }
        }
    }
    match report.outcome {
        RunOutcome::Parsed => {
            println!("Parsing completed{time}.");
            std::process::ExitCode::SUCCESS
        }
        RunOutcome::Verified(VerificationResult::Success) => {
            println!("Verification succeeded{time}.");
            std::process::ExitCode::SUCCESS
        }
        RunOutcome::Verified(VerificationResult::Failure(errors)) => {
            for error in &errors {
                eprintln!(
                    "[{}] {}",
                    error.full_id(),
                    error.readable_message().unwrap_or_else(|_| error.full_id())
                );
            }
            eprintln!("Verification failed with {} error(s){time}.", errors.len());
            std::process::ExitCode::from(1)
        }
    }
}
