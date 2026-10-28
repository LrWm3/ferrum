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
            "Ferrum native Viper port\nUsage: ferrum [options] <file.vpr>\n\n  --parseOnly                 Parse source without verification\n  --z3Exe <path>              Select the Z3 executable\n  --prover <Z3|cvc5|Z3-API>   Select solver (native API binding pending)\n  --assertTimeout <ms>        Limit each assertion query\n  --proverEnableTimeBounds    Use time bounds instead of resource bounds\n  --numberOfErrorsToReport N  Error limit per member (0: unlimited)\n  --disableDefaultPlugins    Disable default source transformations\n\nPort in progress; unconnected features return an explicit error."
        );
        return std::process::ExitCode::SUCCESS;
    }
    if config.frontend.print_version {
        println!("ferrum {}", env!("CARGO_PKG_VERSION"));
        return std::process::ExitCode::SUCCESS;
    }
    let report = match ferrum::run_file(config) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("{error}");
            return std::process::ExitCode::from(2);
        }
    };
    for warning in report.warnings {
        eprintln!("{warning}");
    }
    match report.outcome {
        RunOutcome::Parsed => {
            println!("Parsing completed.");
            std::process::ExitCode::SUCCESS
        }
        RunOutcome::Verified(VerificationResult::Success) => {
            println!("Verification succeeded.");
            std::process::ExitCode::SUCCESS
        }
        RunOutcome::Verified(VerificationResult::Failure(errors)) => {
            for error in &errors {
                eprintln!("{}", error.render().unwrap_or_else(|_| error.full_id()));
            }
            eprintln!("Verification failed with {} error(s).", errors.len());
            std::process::ExitCode::from(1)
        }
    }
}
