//! Ferrum debugger runtime assembly described in PLAN.md.
//! Source-shaped proof-obligation presentation for the native debugger.
//! Unsupported native term and AST renderings are returned as errors.
use super::{
    debug_exp::{DebugExp, DebugExpPrintConfiguration},
    silicon_debugger::{DebuggerPresentation, ProofObligation},
};
use crate::{
    interfaces::state::chunks::{GeneralChunk, QuantifiedChunk},
    reporting::formatters,
    resources::resources::BaseId,
    state::{
        chunks::Chunk,
        heap::{Heap, ListBackedHeap},
        state::{HeapCause, IntermediateHeapRecord, State},
        store::Store,
        terms::{Term, TermFactory, TermKind},
    },
};
use ferrum_silver::{
    ast::{
        expression::{Exp, ExpKind},
        pretty::pretty_printer::{expression_to_string, pretty_node, show_type},
        program::{LocalVarDecl, Program},
        utility::nodes::Node,
        utility::{rewriter::strategy::replace_expressions, simplifier},
    },
    verifier::{verification_error::ErrorReason, verification_result::DiagnosticError},
};
use std::fmt;

#[derive(Debug)]
pub struct NativePresentationError(pub String);
impl fmt::Display for NativePresentationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
fn error(e: impl fmt::Debug) -> NativePresentationError {
    NativePresentationError(format!("{e:?}"))
}
fn term(t: &Term) -> Result<String, NativePresentationError> {
    // Native Vec/Set erases the source Scala collection class; the diagnostic
    // renderer supplies its documented canonical Seq/Set adaptation.
    formatters::render_diagnostic_term(t).map_err(error)
}
fn expression(e: &Exp) -> Result<String, NativePresentationError> {
    expression_to_string(e).map_err(error)
}
fn simplified(e: &Exp) -> Result<String, NativePresentationError> {
    let e = simplifier::simplify(e, true, &|_| Ok::<_, ()>(true)).map_err(error)?;
    expression(&e)
}
fn required<T>(v: Option<T>, what: &'static str) -> Result<T, NativePresentationError> {
    v.ok_or_else(|| NativePresentationError(format!("missing debugger {what}")))
}
fn local(v: &LocalVarDecl) -> Exp {
    let l = v.local_var();
    Exp::new(ExpKind::LocalVar(l), v.meta.clone())
}
fn variables(vars: &[LocalVarDecl]) -> Result<String, NativePresentationError> {
    vars.iter()
        .map(|v| Ok(format!("{}: {}", v.name, show_type(&v.typ).map_err(error)?)))
        .collect::<Result<Vec<_>, NativePresentationError>>()
        .map(|v| v.join(", "))
}
fn substitute(e: &Exp, replacements: &[(Exp, Exp)]) -> Result<Exp, NativePresentationError> {
    replace_expressions(e, replacements).map_err(error)
}
fn inverse_parts(
    invs: &[crate::rules::quantified_chunk_support::InverseFunctions],
    vars: &[LocalVarDecl],
) -> Result<(String, String, Vec<Exp>), NativePresentationError> {
    let inv = required(invs.first(), "inverse functions")?;
    let qvars = required(inv.qvar_exps.as_ref(), "inverse quantified variables")?;
    let exps = required(inv.invertible_exps.as_ref(), "inverse expressions")?;
    let equal = vars
        .iter()
        .zip(exps)
        .map(|(v, e)| Ok(format!("{} == {}", v.name, simplified(e)?)))
        .collect::<Result<Vec<_>, NativePresentationError>>()?
        .join(" && ");
    Ok((variables(qvars)?, equal, exps.clone()))
}
fn source_chunk(c: &Chunk, program: &Program) -> Result<String, NativePresentationError> {
    Ok(match c {
        Chunk::Basic(c) => {
            match c.resource_id {
                BaseId::Field => {
                    let args = required(c.args_exp.as_ref(), "chunk arguments")?;
                    let receiver = required(args.first(), "field receiver")?;
                    let perm = simplified(required(c.perm_exp.as_ref(), "chunk permission")?)?;
                    let snap = c
                        .snap_exp
                        .as_ref()
                        .map(|e| simplified(e).map(|s| format!(" -> {s}")))
                        .transpose()?
                        .unwrap_or_default();
                    format!("acc({}.{}, {}){}", expression(receiver)?, c.id, perm, snap)
                }
                BaseId::Predicate => {
                    // Scala's Option[Seq] mkString uses the sequence's own class
                    // name. Native Vec erases that class; List is canonical here.
                    let perm = simplified(required(c.perm_exp.as_ref(), "chunk permission")?)?;
                    let args = c
                        .args_exp
                        .as_ref()
                        .map(|args| {
                            args.iter()
                                .map(expression)
                                .collect::<Result<Vec<_>, _>>()
                                .map(|args| format!("List({})", args.join(", ")))
                        })
                        .transpose()?
                        .unwrap_or_default();
                    format!("acc({}({args}), {})", c.id, perm)
                }
            }
        }
        Chunk::MagicWand(c) => {
            let replacements = c
                .bindings
                .iter()
                .map(|(key, (_, value))| {
                    Ok((
                        key.expression().clone(),
                        required(value.clone(), "wand binding")?,
                    ))
                })
                .collect::<Result<Vec<_>, NativePresentationError>>()?;
            let shape = substitute(&c.id.ghost_free_wand, &replacements)?;
            format!(
                "acc({}, {})",
                expression(&shape)?,
                simplified(required(c.perm_exp.as_ref(), "wand permission")?)?
            )
        }
        Chunk::QuantifiedField(c) => {
            let vars = required(c.quantified_var_exps(), "quantified field variables")?;
            let perm = required(c.permission_exp(), "quantified field permission")?;
            if let Some(receivers) = c.singleton_argument_exps() {
                let receiver = required(receivers.first(), "singleton field receiver")?;
                let first = required(vars.first(), "field variable")?;
                let perm = substitute(&perm, &[(local(first), receiver.clone())])?;
                format!(
                    "acc({}.{}, {})",
                    simplified(receiver)?,
                    c.id,
                    simplified(&perm)?
                )
            } else {
                let (qvars, equals, _) = inverse_parts(&c.invs, &vars)?;
                let first = required(vars.first(), "field variable")?;
                format!(
                    "forall {} :: forall {} :: {} ==> acc({}.{}, {})",
                    variables(&vars)?,
                    qvars,
                    equals,
                    first.name,
                    c.id,
                    simplified(&perm)?
                )
            }
        }
        Chunk::QuantifiedPredicate(c) => {
            let perm = required(c.permission_exp(), "quantified predicate permission")?;
            if let Some(args) = c.singleton_argument_exps() {
                format!(
                    "acc({}({}), {})",
                    c.id,
                    args.iter()
                        .map(simplified)
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", "),
                    simplified(&perm)?
                )
            } else {
                let vars = required(c.quantified_var_exps(), "quantified predicate variables")?;
                let (qvars, equals, _) = inverse_parts(&c.invs, &vars)?;
                let names = vars
                    .iter()
                    .map(|v| v.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "forall {} :: forall {} :: {} ==> acc({}({}), {})",
                    variables(&vars)?,
                    qvars,
                    equals,
                    c.id,
                    names,
                    simplified(&perm)?
                )
            }
        }
        Chunk::QuantifiedMagicWand(c) => {
            let vars = required(c.quantified_var_exps(), "quantified wand variables")?;
            let perm = required(c.permission_exp(), "quantified wand permission")?;
            let shape = &c.id.ghost_free_wand;
            let parts = shape.magic_wand_subexpressions(program).map_err(error)?;
            if let Some(args) = c.singleton_argument_exps() {
                let values = args
                    .iter()
                    .map(|e| simplifier::simplify(e, true, &|_| Ok::<_, ()>(true)).map_err(error))
                    .collect::<Result<Vec<_>, _>>()?;
                let shape = substitute(shape, &parts.into_iter().zip(values).collect::<Vec<_>>())?;
                let replacements = vars
                    .iter()
                    .zip(args)
                    .map(|(v, e)| (local(v), e.clone()))
                    .collect::<Vec<_>>();
                format!(
                    "acc({}, {})",
                    expression(&shape)?,
                    simplified(&substitute(&perm, &replacements)?)?
                )
            } else {
                let (qvars, equals, inverse) = inverse_parts(&c.invs, &vars)?;
                let values = inverse
                    .iter()
                    .map(|e| simplifier::simplify(e, true, &|_| Ok::<_, ()>(true)).map_err(error))
                    .collect::<Result<Vec<_>, _>>()?;
                let shape = substitute(shape, &parts.into_iter().zip(values).collect::<Vec<_>>())?;
                format!(
                    "forall {} :: forall {} :: {} ==> acc({}, {})",
                    variables(&vars)?,
                    qvars,
                    equals,
                    expression(&shape)?,
                    simplified(&perm)?
                )
            }
        }
        Chunk::MaskHeap(_) => {
            return Err(NativePresentationError(
                "unsupported debugger mask heap chunk".into(),
            ));
        }
    })
}
fn cause(c: &HeapCause) -> Result<String, NativePresentationError> {
    Ok(match c {
        HeapCause::InhalePre => "inhale precondition".into(),
        HeapCause::ExhalePost => "exhale postcondition".into(),
        HeapCause::InhaleInv => "inhale loop invariants".into(),
        HeapCause::ExhaleInv => "exhale loop invariants".into(),
        HeapCause::StateMerge => "merge framed heap or branches".into(),
        HeapCause::CreateLabel => "heap label".into(),
        HeapCause::StateConsolidation => "state consolidation".into(),
        HeapCause::ExecStmt(s) => format!(
            "\"{}\"",
            pretty_node(&Node::Stmt(s.clone())).map_err(error)?
        ),
        HeapCause::EvalExp(e) => format!("\"{}\"", expression(e)?),
    })
}

pub struct NativeDebuggerPresentation {
    pub factory: TermFactory,
}
impl NativeDebuggerPresentation {
    fn chunks(
        &self,
        h: &ListBackedHeap,
        program: &Program,
        internal: bool,
        tabs: &str,
    ) -> Result<String, NativePresentationError> {
        if h.values().is_empty() {
            return Ok(format!("{tabs}(Empty heap)\n"));
        }
        h.values()
            .iter()
            .map(|c| {
                let text = if internal {
                    formatters::render_diagnostic_chunk_with_factory(c, &self.factory)
                        .map_err(error)?
                } else {
                    source_chunk(c, program)?
                };
                Ok(format!("{tabs}{text}\n"))
            })
            .collect()
    }
    fn intermediate(
        &self,
        label: &str,
        record: &IntermediateHeapRecord,
        program: &Program,
        internal: bool,
    ) -> Result<String, NativePresentationError> {
        let mut out = format!("\tIntermediate heap {label}:\n");
        if let Some(c) = &record.intermediate_cause {
            out += &format!("\t\tCause: {}\n", cause(c)?);
        }
        if !record.new_branch_conditions.is_empty() {
            out += &format!(
                "\t\tNew branch conditions: {}\n",
                record
                    .new_branch_conditions
                    .iter()
                    .map(|(e, _)| expression(e))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            );
        }
        out += &self.chunks(&record.heap, program, internal, "\t\t\t")?;
        Ok(out)
    }
}
impl<P, D, J, V> DebuggerPresentation<State<P, D, J>, V, ErrorReason>
    for NativeDebuggerPresentation
{
    type Error = NativePresentationError;
    fn error_message(&self, error: &Self::Error) -> String {
        error.to_string()
    }
    fn obligation(
        &mut self,
        obl: &ProofObligation<State<P, D, J>, V, ErrorReason>,
    ) -> Result<String, Self::Error> {
        let config = obl
            .print_config
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();
        let state = &obl.state;
        let reason = obl
            .original_error_reason
            .readable_message(&|node| {
                pretty_node(node)
                    .map_err(|_| DiagnosticError::Unsupported("debugger reason printer"))
            })
            .map_err(error)?;
        let pos = obl.original_error_reason.position().map_err(error)?;
        let member = state
            .current_member
            .as_ref()
            .map(|m| format!(" (inside {})", m.name()))
            .unwrap_or_default();
        let mut out = format!("\nOriginal Error: \n\t\t{pos}{member}\n\t\t{reason}\n\n");
        let branches = if config.print_internal_terms {
            obl.branch_conditions
                .iter()
                .filter(|t| !matches!(t.kind(), TermKind::True))
                .map(term)
                .collect::<Result<Vec<_>, _>>()?
        } else {
            obl.branch_condition_exps
                .iter()
                .map(|(_, e)| simplified(e))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .filter(|s| s != "true")
                .collect()
        };
        out += &format!(
            "Branch Conditions:\n\t\t{}\n\n",
            if branches.is_empty() {
                "(none)".into()
            } else {
                branches.join("\n\t\t")
            }
        );
        let store = state
            .g
            .values()
            .iter()
            .map(|(key, (t, e))| {
                Ok(format!(
                    "{} -> {}",
                    expression(key.expression())?,
                    if config.print_internal_terms {
                        term(t)?
                    } else {
                        expression(required(e.as_ref(), "store expression")?)?
                    }
                ))
            })
            .collect::<Result<Vec<_>, NativePresentationError>>()?;
        out += &format!("Store:\n\t\t{}\n\n", store.join("\n\t\t"));
        if config.print_old_heaps {
            let eval_heap = if state.exhale_ext {
                if self.factory.options().mask_heap_mode {
                    return Err(NativePresentationError(
                        "debugging with mask heap mode is unsupported by Silicon".into(),
                    ));
                }
                let [used, operations, lhs, ..] = state.reserve_heaps.as_slice() else {
                    return Err(NativePresentationError(
                        "missing wand evaluation reserve heap".into(),
                    ));
                };
                std::sync::Arc::new(used.with_heap(operations.as_ref()).with_heap(lhs.as_ref()))
            } else {
                state.h.clone()
            };
            let mut labelled = Vec::new();
            let mut debug = Vec::new();
            for (label, record) in state.debug_old_heaps.iter() {
                if eval_heap
                    .equal_chunks_by(record.heap.as_ref(), |c| {
                        formatters::render_diagnostic_chunk_with_factory(c, &self.factory)
                    })
                    .map_err(error)?
                {
                    if label.contains("debug") {
                        debug.push(label.as_str());
                    } else {
                        labelled.push(label.as_str());
                    }
                }
            }
            let mut label = labelled.last().or_else(|| debug.last()).copied();
            if label.is_none() {
                'search: for (_, record) in state.debug_old_heaps.iter() {
                    for (candidate, heap) in record.intermediate_heaps.iter() {
                        if eval_heap
                            .equal_chunks_by(heap.heap.as_ref(), |c| {
                                formatters::render_diagnostic_chunk_with_factory(c, &self.factory)
                            })
                            .map_err(error)?
                        {
                            label = Some(candidate);
                            break 'search;
                        }
                    }
                }
            }
            if label.is_none() {
                if let Some(temp) = &state.temporary_heap_record {
                    for (candidate, heap) in temp.intermediate_heaps.iter() {
                        if eval_heap
                            .equal_chunks_by(heap.heap.as_ref(), |c| {
                                formatters::render_diagnostic_chunk_with_factory(c, &self.factory)
                            })
                            .map_err(error)?
                        {
                            label = Some(candidate);
                            break;
                        }
                    }
                }
            }
            out += &format!(
                "Current Heap{}:\n",
                label.map(|label| format!(" ({label})")).unwrap_or_default()
            );
        } else {
            out += "Heap:\n";
        }
        out += &self.chunks(
            &state.h,
            &state.program,
            config.print_internal_terms,
            "\t\t",
        )?;
        out += "\n";
        if config.print_old_heaps {
            for (label, record) in state.debug_old_heaps.iter() {
                out += &format!(
                    "Heap {label}:\n\tParent: {}\n\tCause: {}\n",
                    record.parent_label,
                    cause(&record.cause)?
                );
                if !record.branch_conditions.is_empty() {
                    out += &format!(
                        "\tNew branch conditions: {}\n",
                        record
                            .branch_conditions
                            .iter()
                            .map(|(e, _)| expression(e))
                            .collect::<Result<Vec<_>, _>>()?
                            .join(", ")
                    );
                }
                out += &self.chunks(
                    &record.heap,
                    &state.program,
                    config.print_internal_terms,
                    "\t\t",
                )?;
                out += "\n";
                for (label, intermediate) in record.intermediate_heaps.iter() {
                    out += &self.intermediate(
                        label,
                        intermediate,
                        &state.program,
                        config.print_internal_terms,
                    )?;
                    out += "\n";
                }
            }
            if let Some(temp) = &state.temporary_heap_record {
                out += &format!(
                    "Current intermediate heaps:\n\tParent: {}\n\tCause: {}\n\n",
                    temp.label,
                    cause(&temp.cause)?
                );
                for (label, intermediate) in temp.intermediate_heaps.iter() {
                    out += &self.intermediate(
                        label,
                        intermediate,
                        &state.program,
                        config.print_internal_terms,
                    )?;
                    out += "\n";
                }
            }
        }
        if config.print_axioms && !obl.preamble_assumptions.is_empty() {
            out += "Axioms: ";
            for (i, axiom) in obl.preamble_assumptions.iter().enumerate() {
                out += &format!(
                    "\n\t[A{i}] {}:\n\t\t{}\n",
                    axiom.description,
                    axiom
                        .terms
                        .iter()
                        .map(term)
                        .collect::<Result<Vec<_>, _>>()?
                        .join("\n\t\t")
                );
            }
            out += "\n\n";
        }
        if config.print_axioms && !obl.prover_emits.is_empty() {
            out += &format!("Declarations: \n\t{}\n\n", obl.prover_emits.join("\n\t"));
        }
        let assumptions = obl
            .assumptions
            .iter()
            .filter(|d| config.print_internal || !d.is_internal())
            .map(|d| d.render(&config, &expression, &term))
            .collect::<Result<Vec<_>, _>>()?;
        if !assumptions.is_empty() {
            out += &format!("Assumptions: {}\n\n", assumptions.join(""));
        }
        if obl.assertion_exp.final_exp().is_some() {
            out += &format!(
                "Assertion:\n\t{}\n\n",
                obl.assertion_exp.render(
                    &DebugExpPrintConfiguration {
                        hierarchy_level: 6,
                        ..DebugExpPrintConfiguration::default()
                    },
                    &expression,
                    &term
                )?
            );
        } else {
            out += required(obl.assertion_exp.description(), "assertion description")?;
        }
        Ok(out)
    }
    fn expression(
        &mut self,
        exp: &DebugExp,
        config: &DebugExpPrintConfiguration,
    ) -> Result<String, Self::Error> {
        exp.render(config, &expression, &term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        resources::resources::BaseId,
        state::{
            chunks::{BasicChunk, BasicChunkIdentifier},
            identifiers::Identifier,
            terms::{Sort, TermOptions},
        },
    };
    use ferrum_silver::ast::{ast::Metadata, expression::LocalVar, r#type::Type};
    #[test]
    fn renders_obligation_and_old_heap_label() {
        use crate::state::state::{HeapCause, HeapRecord, State};
        use std::sync::{Arc, Mutex};
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let mut state = State::<(), (), ()>::new(
            program,
            Default::default(),
            Default::default(),
            (),
            &f,
            true,
            false,
        );
        let r = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, Metadata::default())),
            Metadata::default(),
        );
        let perm = Exp::new(ExpKind::FullPerm, Metadata::default());
        let receiver = f.var(Identifier::new("r"), Sort::Ref, false);
        let pred = Chunk::Basic(BasicChunk::new(
            BaseId::Predicate,
            BasicChunkIdentifier("p".into()),
            vec![receiver],
            Some(vec![r]),
            f.var(Identifier::new("snap"), Sort::Snap, false),
            None,
            f.full_perm(),
            Some(perm),
            None,
        ));
        let heap = Arc::new(ListBackedHeap::from_chunks([pred]));
        state.h = heap.clone();
        state.debug_old_heaps.insert(
            "L".into(),
            HeapRecord {
                heap,
                parent_label: "root".into(),
                cause: HeapCause::CreateLabel,
                branch_conditions: vec![],
                intermediate_heaps: Default::default(),
            },
        );
        let failed = Exp::new(ExpKind::FalseLit, Metadata::default());
        let debug = DebugExp::create(
            None,
            Some(failed.clone()),
            Some(failed.clone()),
            Some(f.boolean(false)),
            false,
            Default::default(),
            false,
            &|e| Ok::<_, ()>(e.clone()),
        )
        .unwrap();
        let config = DebugExpPrintConfiguration {
            print_old_heaps: true,
            ..Default::default()
        };
        let mut obl = ProofObligation {
            state,
            verifier: (),
            prover_emits: vec![],
            preamble_assumptions: vec![],
            branch_conditions: vec![],
            branch_condition_exps: vec![],
            assumptions: Default::default(),
            assertion: f.boolean(false),
            assertion_exp: debug,
            timeout: None,
            print_config: Arc::new(Mutex::new(config)),
            original_error_reason: ErrorReason::AssertionFalse(failed),
        };
        let mut presenter = NativeDebuggerPresentation { factory: f };
        let text = presenter.obligation(&obl).unwrap();
        assert!(text.contains("Current Heap (L):"));
        assert!(text.contains("acc(p(List(r)), write)"));
        assert!(text.contains("Cause: heap label"));
        assert!(text.contains("Assertion false might not hold."));
        let retained = obl.state.h.clone();
        obl.state.h = Arc::new(ListBackedHeap::new());
        obl.state.exhale_ext = true;
        obl.state.reserve_heaps = vec![
            Arc::new(ListBackedHeap::new()),
            retained,
            Arc::new(ListBackedHeap::new()),
        ];
        let text = presenter.obligation(&obl).unwrap();
        assert!(text.contains("Current Heap (L):\n\t\t(Empty heap)"));
        obl.state.reserve_heaps.clear();
        assert!(
            presenter
                .obligation(&obl)
                .unwrap_err()
                .to_string()
                .contains("missing wand evaluation reserve heap")
        );
    }
    #[test]
    fn quantified_field_inverse_renders_source_fixture() {
        use crate::{
            rules::quantified_chunk_support::{InverseFunctions, VariableFunctions},
            state::chunks::{QuantifiedFieldChunk, QuantifiedPredicateChunk},
        };
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let variable = LocalVarDecl::new("r@0".into(), Type::Ref, Metadata::default());
        let v = local(&variable);
        let cond = Exp::new(
            ExpKind::NeCmp(v.clone(), Exp::new(ExpKind::NullLit, Metadata::default())),
            Metadata::default(),
        );
        let permission = Exp::new(ExpKind::FullPerm, Metadata::default());
        let inv = InverseFunctions {
            condition: f.boolean(true),
            invertibles: vec![],
            invertible_exps: Some(vec![v]),
            additional_arguments: vec![],
            axiom_inverses_of_invertibles: f.boolean(true),
            axiom_invertibles_of_inverses: f.boolean(true),
            qvar_exps: Some(vec![variable]),
            qvars_to_inverses: VariableFunctions::default(),
            qvars_to_images: VariableFunctions::default(),
        };
        let chunk = QuantifiedFieldChunk::new(
            &f,
            BasicChunkIdentifier("f".into()),
            f.var(
                Identifier::new("fvf"),
                Sort::FieldValueFunction {
                    codomain: Box::new(Sort::Int),
                    field_name: "f".into(),
                },
                false,
            ),
            f.boolean(true),
            f.boolean(true),
            Some(cond.clone()),
            f.full_perm(),
            Some(permission.clone()),
            vec![inv.clone()],
            None,
            None,
            None,
            vec![],
            true,
        );
        assert_eq!(
            source_chunk(&Chunk::QuantifiedField(chunk), &program).unwrap(),
            "forall r: Ref :: forall r@0: Ref :: r == r@0 ==> acc(r.f, (r@0 != null ? write : none))"
        );
        let qvar = f.var(Identifier::new("r"), Sort::Ref, false);
        let qpred = QuantifiedPredicateChunk::new(
            &f,
            BasicChunkIdentifier("p".into()),
            vec![qvar],
            Some(vec![LocalVarDecl::new(
                "r".into(),
                Type::Ref,
                Metadata::default(),
            )]),
            f.var(
                Identifier::new("psf"),
                Sort::PredicateSnapFunction {
                    codomain: Box::new(Sort::Snap),
                    predicate_name: "p".into(),
                },
                false,
            ),
            f.boolean(true),
            f.boolean(true),
            Some(cond),
            f.full_perm(),
            Some(permission),
            vec![inv],
            None,
            None,
            None,
            vec![],
        );
        assert_eq!(
            source_chunk(&Chunk::QuantifiedPredicate(qpred), &program).unwrap(),
            "forall r: Ref :: forall r@0: Ref :: r == r@0 ==> acc(p(r), (r@0 != null ? write : none))"
        );
    }
    #[test]
    fn quantified_wand_inverse_renders_source_fixture() {
        use crate::{
            rules::quantified_chunk_support::{InverseFunctions, VariableFunctions},
            state::chunks::{MagicWandIdentifier, QuantifiedMagicWandChunk},
        };
        use ferrum_silver::ast::{
            expression::PredicateAccess,
            program::{Predicate, PredicateData},
            statement::PredicateAccessPredicate,
        };
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let meta = Metadata::default();
        let parameter = LocalVarDecl::new("r".into(), Type::Ref, meta.clone());
        let predicate = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![parameter],
            body: Some(Exp::new(ExpKind::TrueLit, meta.clone())),
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![predicate],
            vec![],
            vec![],
            meta.clone(),
        );
        let vars = vec![
            LocalVarDecl::new("x0".into(), Type::Ref, meta.clone()),
            LocalVarDecl::new("x1".into(), Type::Ref, meta.clone()),
        ];
        let make_access = |v: &LocalVarDecl| {
            let p = PredicateAccess::new(vec![local(v)], "p".into(), meta.clone());
            Exp::new(
                ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                    p,
                    None,
                    meta.clone(),
                )),
                meta.clone(),
            )
        };
        let shape = Exp::new(
            ExpKind::MagicWand(make_access(&vars[0]), make_access(&vars[1])),
            meta.clone(),
        );
        let inverse_var = LocalVarDecl::new("r@0".into(), Type::Ref, meta.clone());
        let v = local(&inverse_var);
        let cond = Exp::new(
            ExpKind::NeCmp(v.clone(), Exp::new(ExpKind::NullLit, meta.clone())),
            meta.clone(),
        );
        let full = Exp::new(ExpKind::FullPerm, meta.clone());
        let none = Exp::new(ExpKind::NoPerm, meta.clone());
        let perm = Exp::new(ExpKind::CondExp(cond, full, none), meta.clone());
        let inv = InverseFunctions {
            condition: f.boolean(true),
            invertibles: vec![],
            invertible_exps: Some(vec![v.clone(), v]),
            additional_arguments: vec![],
            axiom_inverses_of_invertibles: f.boolean(true),
            axiom_invertibles_of_inverses: f.boolean(true),
            qvar_exps: Some(vec![inverse_var]),
            qvars_to_inverses: VariableFunctions::default(),
            qvars_to_images: VariableFunctions::default(),
        };
        let qwand = QuantifiedMagicWandChunk::new(
            MagicWandIdentifier::from_structure_index(shape, 0),
            vec![
                f.var(Identifier::new("x0"), Sort::Ref, false),
                f.var(Identifier::new("x1"), Sort::Ref, false),
            ],
            Some(vars),
            f.var(
                Identifier::new("qws"),
                Sort::PredicateSnapFunction {
                    codomain: Box::new(Sort::MagicWandSnapFunction),
                    predicate_name: "w".into(),
                },
                false,
            ),
            f.boolean(true),
            f.full_perm(),
            Some(perm),
            vec![inv],
            None,
            None,
            None,
            vec![],
        );
        assert_eq!(
            source_chunk(&Chunk::QuantifiedMagicWand(qwand), &program).unwrap(),
            "forall x0: Ref, x1: Ref :: forall r@0: Ref :: x0 == r@0 && x1 == r@0 ==> acc(acc(p(r@0), write) --* acc(p(r@0), write), (r@0 != null ? write : none))"
        );
    }
    #[test]
    fn wand_and_quantified_wand_render_source_shape() {
        use crate::state::chunks::{
            ChunkBindings, MagicWandChunk, MagicWandIdentifier, QuantifiedMagicWandChunk,
        };
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let boolean = Exp::new(ExpKind::TrueLit, Metadata::default());
        let wand = Exp::new(
            ExpKind::MagicWand(boolean.clone(), boolean),
            Metadata::default(),
        );
        let id = MagicWandIdentifier::from_structure_index(wand, 0);
        let perm = Exp::new(ExpKind::FullPerm, Metadata::default());
        let ws = f.var(Identifier::new("ws"), Sort::MagicWandSnapFunction, false);
        let basic = MagicWandChunk::new(
            id.clone(),
            ChunkBindings::new([]),
            vec![],
            Some(vec![]),
            f.magic_wand_snapshot(ws),
            f.full_perm(),
            Some(perm.clone()),
            None,
        );
        let text = source_chunk(&Chunk::MagicWand(basic), &program).unwrap();
        assert!(text.starts_with("acc("));
        assert!(text.contains("--*"));
        assert!(text.ends_with(", write)"));
        let qwand = QuantifiedMagicWandChunk::new(
            id,
            vec![],
            Some(vec![]),
            f.var(
                Identifier::new("qws"),
                Sort::PredicateSnapFunction {
                    codomain: Box::new(Sort::MagicWandSnapFunction),
                    predicate_name: "w".into(),
                },
                false,
            ),
            f.boolean(true),
            f.full_perm(),
            Some(perm),
            vec![],
            Some(vec![]),
            Some(vec![]),
            None,
            vec![],
        );
        let text = source_chunk(&Chunk::QuantifiedMagicWand(qwand), &program).unwrap();
        assert!(text.contains("--*"));
        assert!(text.ends_with(", write)"));
    }
    #[test]
    fn quantified_singletons_render_debug_expressions() {
        use crate::state::chunks::{QuantifiedFieldChunk, QuantifiedPredicateChunk};
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let r = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, Metadata::default())),
            Metadata::default(),
        );
        let condition = Exp::new(ExpKind::TrueLit, Metadata::default());
        let permission = Exp::new(ExpKind::FullPerm, Metadata::default());
        let receiver = f.var(Identifier::new("r"), Sort::Ref, false);
        let qfield = QuantifiedFieldChunk::new(
            &f,
            BasicChunkIdentifier("f".into()),
            f.var(
                Identifier::new("fvf"),
                Sort::FieldValueFunction {
                    codomain: Box::new(Sort::Int),
                    field_name: "f".into(),
                },
                false,
            ),
            f.boolean(true),
            f.boolean(true),
            Some(condition.clone()),
            f.full_perm(),
            Some(permission.clone()),
            vec![],
            Some(receiver.clone()),
            Some(r.clone()),
            None,
            vec![],
            true,
        );
        assert_eq!(
            source_chunk(&Chunk::QuantifiedField(qfield), &program).unwrap(),
            "acc(r.f, write)"
        );
        let qpred = QuantifiedPredicateChunk::new(
            &f,
            BasicChunkIdentifier("p".into()),
            vec![receiver.clone()],
            None,
            f.var(
                Identifier::new("psf"),
                Sort::PredicateSnapFunction {
                    codomain: Box::new(Sort::Snap),
                    predicate_name: "p".into(),
                },
                false,
            ),
            f.boolean(true),
            f.boolean(true),
            Some(condition),
            f.full_perm(),
            Some(permission),
            vec![],
            Some(vec![receiver]),
            Some(vec![r]),
            None,
            vec![],
        );
        assert_eq!(
            source_chunk(&Chunk::QuantifiedPredicate(qpred), &program).unwrap(),
            "acc(p(r), write)"
        );
    }
    #[test]
    fn basic_field_presentation_and_missing_metadata() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let r = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, Metadata::default())),
            Metadata::default(),
        );
        let permission = Exp::new(ExpKind::FullPerm, Metadata::default());
        let value = Exp::new(ExpKind::IntLit(7.into()), Metadata::default());
        let receiver = f.var(Identifier::new("r"), Sort::Ref, false);
        let v = f.int_literal(7);
        let chunk = Chunk::Basic(BasicChunk::new(
            BaseId::Field,
            BasicChunkIdentifier("f".into()),
            vec![receiver.clone()],
            Some(vec![r]),
            v.clone(),
            Some(value),
            f.full_perm(),
            Some(permission),
            None,
        ));
        assert_eq!(
            source_chunk(&chunk, &program).unwrap(),
            "acc(r.f, write) -> 7"
        );
        let no_debug = Chunk::Basic(BasicChunk::new(
            BaseId::Field,
            BasicChunkIdentifier("f".into()),
            vec![receiver],
            None,
            v,
            None,
            f.full_perm(),
            None,
            None,
        ));
        assert!(
            source_chunk(&no_debug, &program)
                .unwrap_err()
                .to_string()
                .contains("missing debugger chunk arguments")
        );
        let internal = formatters::render_chunk_with_factory(&chunk, &f).unwrap();
        assert!(internal.contains("r.f -> 7"));
    }
}
