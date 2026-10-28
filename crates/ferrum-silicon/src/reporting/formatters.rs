//! State formatting for debugger and symbolic-execution logs.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Formatters.scala
//! Status: source layout, term filters and JSON-like text are implemented. Term,
//! Silicon term and chunk rendering remain fallible; native Silver AST rendering is available.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::decider::path_conditions::RecordedPathConditions;
use crate::state::{
    chunks::Chunk,
    heap::{Heap, ListBackedHeap},
    state::State,
    store::{MapBackedStore, Store},
    terms::{Term, TermKind},
};
use ferrum_silver::ast::{expression::Exp, r#type::Type};

/// Source `toString` calls, kept fallible until complete printer implementations exist.
pub trait StateRenderer {
    type Error;
    fn term(&self, term: &Term) -> Result<String, Self::Error>;
    fn expression(&self, expression: &Exp) -> Result<String, Self::Error>;
    fn typ(&self, typ: &Type) -> Result<String, Self::Error>;
    fn chunk(&self, chunk: &Chunk) -> Result<String, Self::Error>;
}
/// Source Silicon term `toString`, for the term families listed below.
/// Other families fail explicitly until their source renderers are ported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsupportedTermRendering;
fn render_resource(
    resource: &crate::state::terms::ResourceKey,
) -> Result<String, UnsupportedTermRendering> {
    use crate::state::terms::ResourceKey;
    use ferrum_silver::ast::{
        pretty::pretty_printer::pretty_node, program::Member, utility::nodes::Node,
    };
    let member = match resource {
        ResourceKey::Field(field) => Member::Field((**field).clone()),
        ResourceKey::Predicate(predicate) => Member::Predicate((**predicate).clone()),
        ResourceKey::Wand(wand) => return Ok(wand.to_string()),
    };
    pretty_node(&Node::Member(member)).map_err(|_| UnsupportedTermRendering)
}
fn render_applicable(
    target: &crate::state::terms::ApplicationTarget,
) -> Result<String, UnsupportedTermRendering> {
    use crate::state::terms::{ApplicableKind, ApplicationTarget};
    match target {
        ApplicationTarget::Variable(v) => render_term(v),
        ApplicationTarget::Function(f) => {
            let data = f.data();
            if data.kind == ApplicableKind::Macro {
                // Macro's flyweight product includes a Scala sequence whose concrete
                // collection representation is not retained by this model.
                return Err(UnsupportedTermRendering);
            }
            if data.arg_sorts.is_empty() {
                Ok(format!("{}: {}", data.id, data.result_sort))
            } else {
                Ok(format!(
                    "{}: {} -> {}",
                    data.id,
                    data.arg_sorts
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" x "),
                    data.result_sort
                ))
            }
        }
    }
}
pub fn render_term(term: &Term) -> Result<String, UnsupportedTermRendering> {
    use TermKind::*;
    let binary = |a: &Term, op: &str, b: &Term| -> Result<String, UnsupportedTermRendering> {
        Ok(format!("{} {} {}", render_term(a)?, op, render_term(b)?))
    };
    let unary = |op: &str, a: &Term| -> Result<String, UnsupportedTermRendering> {
        Ok(format!("{}({})", op, render_term(a)?))
    };
    Ok(match term.kind() {
        Unit => "_".into(),
        IntLiteral(n) => n.to_string(),
        Null => "Null".into(),
        ZeroMask => "ZeroMask".into(),
        PredZeroMask => "PredZeroMask".into(),
        True => "True".into(),
        False => "False".into(),
        Var(v) => v.id.to_string(),
        AppHint(applicable) => format!("AppHint({})", render_applicable(applicable)?),
        Let(bindings, body) => {
            let entries = bindings
                .iter()
                .map(|(var, value)| Ok(format!("{} = {}", render_term(var)?, render_term(value)?)))
                .collect::<Result<Vec<_>, UnsupportedTermRendering>>()?;
            format!("let List({}) in {}", entries.join(", "), render_term(body)?)
        }
        App { applicable, args } => {
            let id = applicable.id().to_string();
            if args.is_empty() {
                id
            } else {
                format!(
                    "{}({})",
                    id,
                    args.iter()
                        .map(render_term)
                        .collect::<Result<Vec<_>, _>>()?
                        .join(", ")
                )
            }
        }
        Quantification {
            quantifier,
            vars,
            body,
            ..
        } => {
            let q = match quantifier {
                crate::state::terms::Quantifier::Forall => "QA",
                crate::state::terms::Quantifier::Exists => "QE",
            };
            format!(
                "{} {} :: {}",
                q,
                vars.iter()
                    .map(render_term)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(","),
                render_term(body)?
            )
        }
        Plus(a, b) | PermPlus(a, b) | MultisetAdd(a, b) => binary(a, "+", b)?,
        Minus(a, b) => binary(a, "-", b)?,
        PermMinus(a, b) => {
            let right = render_term(b)?;
            let is_binary = matches!(
                b.kind(),
                Plus(..)
                    | Minus(..)
                    | Times(..)
                    | Div(..)
                    | Mod(..)
                    | Implies(..)
                    | Iff(..)
                    | BuiltinEquals(..)
                    | CustomEquals(..)
                    | Less(..)
                    | AtMost(..)
                    | Greater(..)
                    | AtLeast(..)
                    | PermTimes(..)
                    | IntPermTimes(..)
                    | PermIntDiv(..)
                    | PermPermDiv(..)
                    | PermPlus(..)
                    | PermMinus(..)
                    | PermLess(..)
                    | PermAtMost(..)
                    | PermMin(..)
                    | SeqAppend(..)
                    | SeqDrop(..)
                    | SeqTake(..)
                    | SeqAt(..)
                    | SeqIn(..)
                    | SeqInTrigger(..)
                    | SetAdd(..)
                    | SetUnion(..)
                    | SetIntersection(..)
                    | SetSubset(..)
                    | SetDisjoint(..)
                    | SetDifference(..)
                    | SetIn(..)
                    | MultisetAdd(..)
                    | MultisetUnion(..)
                    | MultisetIntersection(..)
                    | MultisetSubset(..)
                    | MultisetDifference(..)
                    | MultisetCount(..)
                    | MapLookup(..)
                    | Combine(..)
                    | MwsfLookup(..)
                    | MagicWandToken(..)
            );
            if is_binary {
                format!("{} - ({})", render_term(a)?, right)
            } else {
                format!("{} - {}", render_term(a)?, right)
            }
        }
        Times(a, b) | PermTimes(a, b) | IntPermTimes(a, b) => binary(a, "*", b)?,
        Div(a, b) | PermIntDiv(a, b) | PermPermDiv(a, b) => binary(a, "/", b)?,
        Mod(a, b) => binary(a, "%", b)?,
        Not(a) => match a.kind() {
            BuiltinEquals(a, b) => binary(a, "!=", b)?,
            _ => unary("!", a)?,
        },
        Or(v) | And(v) => v
            .iter()
            .map(render_term)
            .collect::<Result<Vec<_>, _>>()?
            .join(if matches!(term.kind(), Or(_)) {
                " || "
            } else {
                " && "
            }),
        Implies(a, b) => binary(a, "==>", b)?,
        Iff(a, b) => binary(a, "<==>", b)?,
        Ite(a, b, c) => format!(
            "({} ? {} : {})",
            render_term(a)?,
            render_term(b)?,
            render_term(c)?
        ),
        BuiltinEquals(a, b) => binary(a, "==", b)?,
        CustomEquals(a, b) => binary(a, "===", b)?,
        Less(a, b) => binary(a, "<", b)?,
        AtMost(a, b) | PermAtMost(a, b) => binary(a, "<=", b)?,
        Greater(a, b) => binary(a, ">", b)?,
        AtLeast(a, b) => binary(a, ">=", b)?,
        NoPerm => "Z".into(),
        FullPerm => "W".into(),
        FractionPermLiteral(r) => r.to_string(),
        FractionPerm(a, b) => format!("{}/{}", render_term(a)?, render_term(b)?),
        IsValidPermVal(a) => unary("PVal", a)?,
        IsReadPermVar(a) => unary("RdVar", a)?,
        PermNegation(a) => unary("-", a)?,
        PermLess(a, b) => format!("({}) < ({})", render_term(a)?, render_term(b)?),
        PermMin(a, b) => format!("min ({}, {})", render_term(a)?, render_term(b)?),
        SeqRanged(a, b) => format!("[{}..{}]", render_term(a)?, render_term(b)?),
        SeqNil(_) => "Nil".into(),
        SeqSingleton(a) => format!("[{}]", render_term(a)?),
        SeqAppend(a, b) => binary(a, "++", b)?,
        SeqDrop(a, b) => format!("{}[{}:]", render_term(a)?, render_term(b)?),
        SeqTake(a, b) => format!("{}[:{}]", render_term(a)?, render_term(b)?),
        SeqLength(a) | SetCardinality(a) | MultisetCardinality(a) | MapCardinality(a) => {
            format!("|{}|", render_term(a)?)
        }
        SeqAt(a, b) | MapLookup(a, b) => format!("{}[{}]", render_term(a)?, render_term(b)?),
        SeqIn(a, b) | SeqInTrigger(a, b) => format!("{} in {}", render_term(b)?, render_term(a)?),
        SeqUpdate(a, b, c) => format!(
            "{}[{}] := {}",
            render_term(a)?,
            render_term(b)?,
            render_term(c)?
        ),
        EmptySet(_) | EmptyMultiset(_) | EmptyMap(..) => "Ø".into(),
        SingletonSet(a) | SingletonMultiset(a) => format!("{{{}}}", render_term(a)?),
        SetAdd(a, b) => binary(a, "+", b)?,
        SetUnion(a, b) | MultisetUnion(a, b) => binary(a, "∪", b)?,
        SetIntersection(a, b) | MultisetIntersection(a, b) => binary(a, "∩", b)?,
        SetSubset(a, b) | MultisetSubset(a, b) => binary(a, "⊂", b)?,
        SetDisjoint(a, b) => binary(a, "disj", b)?,
        SetDifference(a, b) | MultisetDifference(a, b) => binary(a, "\\", b)?,
        SetIn(a, b) => binary(a, "in", b)?,
        MultisetCount(a, b) => format!("{}({})", render_term(a)?, render_term(b)?),
        MapDomain(a) => unary("domain", a)?,
        MapRange(a) => unary("range", a)?,
        MapUpdate(a, b, c) => format!(
            "MapUpdate({}, {}, {})",
            render_term(a)?,
            render_term(b)?,
            render_term(c)?
        ),
        First(a) => unary("First:", a)?,
        Second(a) => unary("Second:", a)?,
        SortWrapper(a, _) => render_term(a)?,
        Combine(a, b) => format!("({}, {})", render_term(a)?, render_term(b)?),
        Lookup(name, map, at) | PermLookup(name, map, at) | FieldTrigger(name, map, at) => {
            let kind = match term.kind() {
                Lookup(..) => "Lookup",
                PermLookup(..) => "PermLookup",
                _ => "FieldTrigger",
            };
            format!(
                "{}({}, {}, {})",
                kind,
                name,
                render_term(map)?,
                render_term(at)?
            )
        }
        Domain(name, map) | PredicateDomain(name, map) => {
            let kind = if matches!(term.kind(), Domain(..)) {
                "Domain"
            } else {
                "PredicateDomain"
            };
            format!("{}({}, {})", kind, name, render_term(map)?)
        }
        HasDomain(name, map, global) | HasPredicateDomain(name, map, global) => {
            let kind = if matches!(term.kind(), HasDomain(..)) {
                "HasDomain"
            } else {
                "HasPredicateDomain"
            };
            format!("{}({}, {}, {})", kind, name, render_term(map)?, global)
        }
        MagicWandChunkTerm(chunk) => {
            format!("wand@{}}}", chunk.id.ghost_free_wand.metadata().position)
        }
        HeapLookup(a, b) | MaskEq(a, b) | MaskSum(a, b) | MaskDiff(a, b) => {
            let kind = match term.kind() {
                HeapLookup(..) => "HeapLookup",
                MaskEq(..) => "MaskEq",
                MaskSum(..) => "MaskSum",
                _ => "MaskDiff",
            };
            format!("{}({}, {})", kind, render_term(a)?, render_term(b)?)
        }
        HeapUpdate(a, b, c) | MaskAdd(a, b, c) | IdenticalOnKnownLocations(a, b, c) => {
            let kind = match term.kind() {
                HeapUpdate(..) => "HeapUpdate",
                MaskAdd(..) => "MaskAdd",
                _ => "IdenticalOnKnownLocations",
            };
            format!(
                "{}({}, {}, {})",
                kind,
                render_term(a)?,
                render_term(b)?,
                render_term(c)?
            )
        }
        MergeSingle(a, b, c, d) | MergeHeaps(a, b, c, d) | HeapsOverlap(a, b, c, d) => {
            let kind = match term.kind() {
                MergeSingle(..) => "MergeSingle",
                MergeHeaps(..) => "MergeHeaps",
                _ => "HeapsOverlap",
            };
            format!(
                "{}({}, {}, {}, {})",
                kind,
                render_term(a)?,
                render_term(b)?,
                render_term(c)?,
                render_term(d)?
            )
        }
        GoodFieldMask(a, bound) => format!("GoodFieldMask({}, {})", render_term(a)?, bound),
        // ConditionalFlyweight prints the product elements of a single Product
        // equality member, rather than that member's own `toString`.
        GoodMask(mask) => match mask.kind() {
            AppHint(applicable) => format!("GoodMask({})", render_applicable(applicable)?),
            Unit | Null | ZeroMask | PredZeroMask | True | False | NoPerm | FullPerm => {
                "GoodMask()".into()
            }
            _ => unary("GoodMask", mask)?,
        },
        MaskMapTerm(entries) | HeapMapTerm(entries) => {
            let kind = if matches!(term.kind(), MaskMapTerm(_)) {
                "MaskMapTerm"
            } else {
                "HeapMapTerm"
            };
            let entries = entries
                .iter()
                .map(|(resource, value)| {
                    Ok(format!(
                        "{} -> {}",
                        render_resource(resource)?,
                        render_term(value)?
                    ))
                })
                .collect::<Result<Vec<_>, UnsupportedTermRendering>>()?;
            format!("{kind}(ListMap({}))", entries.join(", "))
        }
        HeapToSnap(heap, mask, resource) => format!(
            "HeapToSnap({}, {}, {})",
            render_term(heap)?,
            render_term(mask)?,
            render_resource(resource)?
        ),
        SnapToHeap(snap, resource, sort) => format!(
            "SnapToHeap({}, {}, {})",
            render_term(snap)?,
            render_resource(resource)?,
            sort
        ),
        DummyHeap(sort) => {
            use crate::state::terms::Sort;
            let members = match sort {
                Sort::Seq(s) | Sort::Set(s) | Sort::Multiset(s) | Sort::Heap(s) => s.to_string(),
                Sort::Map(k, v) => format!("{k}, {v}"),
                Sort::UserSort(id) | Sort::SmtSort(id) => id.to_string(),
                Sort::FieldValueFunction {
                    codomain,
                    field_name,
                } => format!("{codomain}, {field_name}"),
                Sort::PredicateSnapFunction {
                    codomain,
                    predicate_name,
                } => format!("{codomain}, {predicate_name}"),
                Sort::Snap
                | Sort::Int
                | Sort::Bool
                | Sort::Ref
                | Sort::Perm
                | Sort::Unit
                | Sort::MagicWandSnapFunction
                | Sort::FieldPermFunction
                | Sort::PredicatePermFunction
                | Sort::WandHeap
                | Sort::PredHeap
                | Sort::PredMask => String::new(),
            };
            format!("DummyHeap({members})")
        }
        HeapSingleton(a, b, sort) => format!(
            "HeapSingleton({}, {}, {})",
            render_term(a)?,
            render_term(b)?,
            sort
        ),
        MagicWandSnapshot(a) => unary("wandSnap", a)?,
        MwsfLookup(a, b) => format!("{}[{}]", render_term(a)?, render_term(b)?),
        MagicWandToken(a, b) => format!("MW_token({}, {})", render_term(a)?, render_term(b)?),
        _ => return Err(UnsupportedTermRendering),
    })
}

/// Source non-quantified and mask-heap chunk rendering; quantified chunks use separate handling.
pub fn render_chunk(chunk: &Chunk) -> Result<String, UnsupportedTermRendering> {
    match chunk {
        Chunk::Basic(chunk) => {
            let snapshot = render_term(&chunk.snap)?;
            let permission = render_term(&chunk.perm)?;
            Ok(match chunk.resource_id {
                crate::resources::resources::BaseId::Field => {
                    let receiver = chunk.args.first().ok_or(UnsupportedTermRendering)?;
                    format!(
                        "{}.{} -> {} # {}",
                        render_term(receiver)?,
                        chunk.id,
                        snapshot,
                        permission
                    )
                }
                crate::resources::resources::BaseId::Predicate => {
                    let args = chunk
                        .args
                        .iter()
                        .map(render_term)
                        .collect::<Result<Vec<_>, _>>()?
                        .join(",");
                    format!("{}({}; {}) # {}", chunk.id, snapshot, args, permission)
                }
            })
        }
        Chunk::MaskHeap(chunk) => {
            use crate::resources::resources::ResourceId;
            let id = match chunk.resource_id {
                ResourceId::Field => "FieldID",
                ResourceId::Predicate => "PredicateID",
                ResourceId::MagicWand => "MagicWandID",
            };
            Ok(format!(
                "BasicMaskHeapChunk({id},{},{},{})",
                render_resource(&chunk.resource)?,
                render_term(&chunk.mask)?,
                render_term(&chunk.heap)?
            ))
        }
        Chunk::MagicWand(chunk) => {
            let pos = &chunk.id.ghost_free_wand.metadata().position;
            let position = pos.line_column().map_or_else(
                || pos.to_string(),
                |p| format!("{}:{}", p.line(), p.column()),
            );
            let args = chunk
                .args
                .iter()
                .map(render_term)
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            Ok(format!(
                "wand@{}[{}; {}]",
                position,
                render_term(&chunk.snap)?,
                args
            ))
        }
        _ => Err(UnsupportedTermRendering),
    }
}

/// Render quantified chunks with their originating term factory, which supplies
/// the source receiver variable and cached conditional permission.
pub fn render_chunk_with_factory(
    chunk: &Chunk,
    factory: &crate::state::terms::TermFactory,
) -> Result<String, UnsupportedTermRendering> {
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    let tag = |v: Option<i32>| v.map_or_else(|| "None".into(), |n| format!("Some({n})"));
    let vars = |v: &[Term]| {
        v.iter()
            .map(render_term)
            .collect::<Result<Vec<_>, _>>()
            .map(|x| x.join(","))
    };
    Ok(match chunk {
        Chunk::QuantifiedField(c) => {
            let receiver = render_term(&c.quantified_vars(factory)[0])?;
            format!(
                "QA {receiver} :: {receiver}.{} -> {} # {} # {} # {}",
                c.id,
                render_term(&c.fvf)?,
                render_term(&c.permission(factory))?,
                tag(c.tag),
                render_term(&c.org_condition)?
            )
        }
        Chunk::QuantifiedPredicate(c) => {
            let names = vars(&c.quantified_vars)?;
            format!(
                "QA {names} :: {}({names}) -> {} # {} # {} # {}",
                c.id,
                render_term(&c.psf)?,
                render_term(&c.permission(factory))?,
                tag(c.tag),
                render_term(&c.org_condition)?
            )
        }
        Chunk::QuantifiedMagicWand(c) => {
            let names = vars(&c.quantified_vars)?;
            format!(
                "QA {names} :: {}({names}) -> {} # {} # {} # {}",
                c.id,
                render_term(&c.wsf)?,
                render_term(&c.perm)?,
                tag(c.tag),
                render_term(&c.org_condition)?
            )
        }
        _ => return render_chunk(chunk),
    })
}

/// A formatter bridge using Silver's actual AST printer and caller-provided
/// Silicon term and chunk renderers (whose source Display is still incomplete).
pub struct NativeAstStateRenderer<T, C> {
    pub render_term: T,
    pub render_chunk: C,
}
#[derive(Debug)]
pub enum NativeStateRenderError<E> {
    Ast(ferrum_silver::ast::pretty::pretty_printer::PrintError),
    Silicon(E),
}
impl<T, C, E> StateRenderer for NativeAstStateRenderer<T, C>
where
    T: Fn(&Term) -> Result<String, E>,
    C: Fn(&Chunk) -> Result<String, E>,
{
    type Error = NativeStateRenderError<E>;
    fn term(&self, term: &Term) -> Result<String, Self::Error> {
        (self.render_term)(term).map_err(NativeStateRenderError::Silicon)
    }
    fn expression(&self, expression: &Exp) -> Result<String, Self::Error> {
        ferrum_silver::ast::pretty::pretty_printer::expression_to_string(expression)
            .map_err(NativeStateRenderError::Ast)
    }
    fn typ(&self, typ: &Type) -> Result<String, Self::Error> {
        ferrum_silver::ast::pretty::pretty_printer::show_type(typ)
            .map_err(NativeStateRenderError::Ast)
    }
    fn chunk(&self, chunk: &Chunk) -> Result<String, Self::Error> {
        (self.render_chunk)(chunk).map_err(NativeStateRenderError::Silicon)
    }
}
/// Ready-to-use source renderer. Unsupported Silicon families remain explicit errors.
pub fn native_state_formatter<'a>(
    factory: &'a crate::state::terms::TermFactory,
    trace_enabled: bool,
) -> DefaultStateFormatter<
    NativeAstStateRenderer<
        fn(&Term) -> Result<String, UnsupportedTermRendering>,
        impl Fn(&Chunk) -> Result<String, UnsupportedTermRendering> + 'a,
    >,
> {
    DefaultStateFormatter {
        renderer: NativeAstStateRenderer {
            render_term,
            render_chunk: move |chunk: &Chunk| render_chunk_with_factory(chunk, factory),
        },
        trace_enabled,
    }
}
/// Source hides built-in equalities involving a Combine, and `not(x == null)`
/// when null is the right operand. Other equalities and reversed null are retained.
pub fn visible_path_condition(term: &Term) -> bool {
    match term.kind() {
        TermKind::BuiltinEquals(left, right) => {
            !matches!(left.kind(), TermKind::Combine(..))
                && !matches!(right.kind(), TermKind::Combine(..))
        }
        TermKind::Not(inner) => {
            !matches!(inner.kind(), TermKind::BuiltinEquals(_, right) if matches!(right.kind(), TermKind::Null))
        }
        _ => true,
    }
}
pub struct DefaultStateFormatter<R> {
    pub renderer: R,
    pub trace_enabled: bool,
}
impl<R: StateRenderer> DefaultStateFormatter<R> {
    pub fn format_store(&self, store: &MapBackedStore) -> Result<String, R::Error> {
        let entries = store
            .values()
            .iter()
            .map(|(key, (term, expression))| {
                let extra = match expression {
                    Some(e) => format!("Some({})", self.renderer.expression(e)?),
                    None => "None".into(),
                };
                Ok(format!(
                    "({},({},{}))",
                    self.renderer.expression(key.expression())?,
                    self.renderer.term(term)?,
                    extra
                ))
            })
            .collect::<Result<Vec<_>, R::Error>>()?;
        Ok(format!("({})", entries.join(", ")))
    }
    pub fn format_heap(&self, heap: &ListBackedHeap) -> Result<String, R::Error> {
        Ok(format!(
            "({})",
            heap.values()
                .iter()
                .map(|c| self.renderer.chunk(c))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ))
    }
    pub fn format_conditions<'a>(
        &self,
        pcs: impl IntoIterator<Item = &'a Term>,
    ) -> Result<String, R::Error> {
        Ok(format!(
            "({})",
            pcs.into_iter()
                .filter(|term| visible_path_condition(term))
                .map(|term| self.renderer.term(term))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ))
    }
    pub fn format_state<P, D, J>(
        &self,
        state: &State<P, D, J>,
        pcs: &RecordedPathConditions,
    ) -> Result<String, R::Error> {
        let old = state
            .old_heaps
            .iter()
            .map(|(name, heap)| Ok(format!("{}: {}", name, self.format_heap(heap)?)))
            .collect::<Result<Vec<_>, R::Error>>()?
            .join(",\n");
        let conditions = if self.trace_enabled {
            format!("{}\n", self.format_conditions(pcs.assumptions().iter())?)
        } else {
            String::new()
        };
        Ok(format!(
            "Store: {},\nHeap: {},\nOHs: ({}),\nPCs: {})",
            self.format_store(&state.g)?,
            self.format_heap(&state.h)?,
            old,
            conditions
        ))
    }
    /// Exact source JSON-like formatting, including its lack of string escaping.
    pub fn to_json<P, D, J>(
        &self,
        state: &State<P, D, J>,
        pcs: &[Term],
    ) -> Result<String, R::Error> {
        let store = state
            .g
            .term_values()
            .map(|(key, term)| {
                let typ = key
                    .expression()
                    .typ()
                    .expect("AbstractLocalVar always has a type");
                Ok(format!(
                    "{{\"value\":\"{} -> {}\",\"type\":\"{}\"}}",
                    self.renderer.expression(key.expression())?,
                    self.renderer.term(term)?,
                    self.renderer.typ(&typ)?
                ))
            })
            .collect::<Result<Vec<_>, R::Error>>()?
            .join(",");
        let heap = self.json_heap(&state.h)?;
        let old = match state.old_heaps.get(&"old".to_string()) {
            Some(h) => self.json_heap(h)?,
            None => "[]".into(),
        };
        let mut seen = Vec::<&Term>::new();
        let mut conditions = Vec::new();
        for term in pcs {
            if visible_path_condition(term) && !seen.contains(&term) {
                seen.push(term);
                conditions.push(format!("\"{}\"", self.renderer.term(term)?));
            }
        }
        let conditions = conditions.join(",");
        Ok(format!(
            "{{\"store\":[{}],\"heap\":{},\"oldHeap\":{},\"pcs\":[{}]}}",
            store, heap, old, conditions
        ))
    }
    fn json_heap(&self, heap: &ListBackedHeap) -> Result<String, R::Error> {
        Ok(format!(
            "[{}]",
            heap.values()
                .iter()
                .map(|c| self.renderer.chunk(c).map(|s| format!("\"{}\"", s)))
                .collect::<Result<Vec<_>, _>>()?
                .join(",")
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{
        identifiers::Identifier,
        terms::{Sort, TermFactory, TermOptions},
    };
    #[test]
    fn renders_source_let_hint_and_mask_terms() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let x = f.var(Identifier::new("x"), Sort::Int, false);
        let y = f.var(Identifier::new("y"), Sort::Int, false);
        let term = f.let_term(
            [(x.clone(), f.int_literal(1)), (y.clone(), f.int_literal(2))],
            x.clone(),
        );
        assert_eq!(render_term(&term).unwrap(), "let List(x = 1, y = 2) in x");
        assert_eq!(render_term(&f.app_hint_var(x)).unwrap(), "AppHint(x)");
        let function = f.applicable(crate::state::terms::ApplicableData {
            kind: crate::state::terms::ApplicableKind::Fun,
            id: Identifier::new("fun"),
            arg_sorts: vec![Sort::Int, Sort::Bool],
            result_sort: Sort::Ref,
        });
        assert_eq!(
            render_term(&f.app_hint(function)).unwrap(),
            "AppHint(fun: Int x Bool -> Ref)"
        );
        assert_eq!(
            render_term(&f.mask_map_term([])).unwrap(),
            "MaskMapTerm(ListMap())"
        );
        assert_eq!(
            render_term(&f.heap_map_term([])).unwrap(),
            "HeapMapTerm(ListMap())"
        );
        let mask = f.var(Identifier::new("m"), Sort::PredMask, false);
        assert_eq!(render_term(&f.good_mask(mask)).unwrap(), "GoodMask(m)");
        assert_eq!(
            render_term(&f.dummy_heap(Sort::PredHeap)).unwrap(),
            "DummyHeap()"
        );
        assert_eq!(
            render_term(&f.dummy_heap(Sort::Heap(Box::new(Sort::Int)))).unwrap(),
            "DummyHeap(Int)"
        );
    }
    #[test]
    fn renders_resource_maps_and_snapshot_conversions() {
        use crate::state::terms::ResourceKey;
        use ferrum_silver::ast::{
            ast::Metadata,
            program::{Field, FieldData},
            r#type::Type,
        };
        use std::sync::Arc;
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let field = ResourceKey::Field(Arc::new(Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: Metadata::default(),
        })));
        let chunk = Chunk::MaskHeap(crate::state::chunks::BasicMaskHeapChunk {
            resource_id: crate::resources::resources::ResourceId::Field,
            resource: field.clone(),
            mask: f.zero_mask(),
            heap: f.dummy_heap(Sort::Heap(Box::new(Sort::Int))),
        });
        assert_eq!(
            render_chunk(&chunk).unwrap(),
            "BasicMaskHeapChunk(FieldID,field f: Int,ZeroMask,DummyHeap(Int))"
        );
        let map = f.mask_map_term([(field.clone(), f.zero_mask())]);
        assert_eq!(
            render_term(&map).unwrap(),
            "MaskMapTerm(ListMap(field f: Int -> ZeroMask))"
        );
        let heap = f.var(Identifier::new("h"), Sort::Heap(Box::new(Sort::Int)), false);
        let snap = f.var(Identifier::new("s"), Sort::Snap, false);
        assert_eq!(
            render_term(&f.heap_to_snap(heap, f.zero_mask(), field.clone())).unwrap(),
            "HeapToSnap(h, ZeroMask, field f: Int)"
        );
        assert_eq!(
            render_term(&f.snap_to_heap(snap, field, Sort::Heap(Box::new(Sort::Int)))).unwrap(),
            "SnapToHeap(s, field f: Int, Hp[Int])"
        );
    }
    #[test]
    fn native_rendering_matches_source_for_basic_field_and_conditions() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let receiver = f.var(Identifier::new("r"), Sort::Ref, false);
        let value = f.var(Identifier::new("v"), Sort::Int, false);
        let chunk = Chunk::Basic(crate::state::chunks::BasicChunk::new(
            crate::resources::resources::BaseId::Field,
            crate::state::chunks::BasicChunkIdentifier("field".into()),
            vec![receiver.clone()],
            None,
            value,
            None,
            f.full_perm(),
            None,
            None,
        ));
        assert_eq!(render_chunk(&chunk).unwrap(), "r.field -> v # W");
        assert_eq!(
            render_term(&f.not(f.builtin_equals(receiver, f.null()))).unwrap(),
            "r != Null"
        );
    }
    #[test]
    fn filter_hides_only_source_null_orientation_and_combine_equalities() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = f.var(Identifier::new("x"), Sort::Ref, false);
        let hidden = f.not(f.builtin_equals(x.clone(), f.null()));
        let reversed = f.not(f.builtin_equals(f.null(), x));
        let a = f.var(Identifier::new("a"), Sort::Snap, false);
        let b = f.var(Identifier::new("b"), Sort::Snap, false);
        let combined = f.builtin_equals(f.combine(a.clone(), b), a);
        assert!(!visible_path_condition(&hidden));
        assert!(visible_path_condition(&reversed));
        assert!(!visible_path_condition(&combined));
    }
}
