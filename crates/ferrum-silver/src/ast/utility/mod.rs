//! Ferrum module assembly for ast/utility.
//! See PLAN.md; declaring a module does not mark its implementation complete.

pub mod backend_type_factories;
pub mod chopper;
pub mod consistency;
pub mod domain_instances;
pub mod expressions;
pub mod file_loader;
pub mod functions;
pub mod generic_arithmetic_solver;
pub mod generic_axiom_rewriter;
pub mod generic_trigger_generator;
pub mod impure_assume_rewriter;
pub mod inverse_functions;
pub mod nodes;
pub mod permissions;
pub mod quantified_permissions;
pub mod rewriter;
pub mod simplifier;
pub mod statements;
pub mod triggers;
pub mod types;
pub mod viper_strategy;
pub mod visitor;
