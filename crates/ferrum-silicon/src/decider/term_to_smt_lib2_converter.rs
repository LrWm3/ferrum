// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! SMT-LIB term conversion from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/TermToSMTLib2Converter.scala
//! Status: typed syntax translation in progress. Source pretty-printer line wrapping is
//! not reproduced; unsupported source cases return explicit errors.

use crate::decider::smtlib_name_generator::{EmptyName, SmtlibNameSanitizer};
use crate::interfaces::decider::term_converter::TermConverter;
use crate::state::identifiers::Identifier;
use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Declaration, DeclarationKind, Quantifier, ResourceKey, Sort,
    Term, TermFactory, TermKind, sort_wrapper_id,
};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConversionError {
    EmptyName,
    UnsupportedTerm(&'static str),
    InvalidSort(&'static str),
    InvalidIdentifierTemplate,
}
impl From<EmptyName> for ConversionError {
    fn from(_: EmptyName) -> Self {
        Self::EmptyName
    }
}
impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SMT conversion error: {self:?}")
    }
}
impl std::error::Error for ConversionError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConversionWarning {
    EmptyQuantifier {
        quantifier: Quantifier,
        name: String,
    },
}

pub struct TermToSmtLib2Converter {
    factory: TermFactory,
    names: HashMap<String, String>,
    warnings: Vec<ConversionWarning>,
}
impl TermToSmtLib2Converter {
    pub fn new(factory: TermFactory) -> Self {
        Self {
            factory,
            names: HashMap::new(),
            warnings: Vec::new(),
        }
    }
    pub fn start(&mut self) {
        self.names.clear();
        self.warnings.clear();
    }
    pub fn reset(&mut self) {
        self.names.clear();
        self.warnings.clear();
    }
    pub fn stop(&mut self) {
        self.names.clear();
        self.warnings.clear();
    }
    pub fn warnings(&self) -> &[ConversionWarning] {
        &self.warnings
    }
    pub fn take_warnings(&mut self) -> Vec<ConversionWarning> {
        std::mem::take(&mut self.warnings)
    }
    fn sanitize(&mut self, text: &str) -> Result<String, ConversionError> {
        if let Some(value) = self.names.get(text) {
            return Ok(value.clone());
        }
        let value = SmtlibNameSanitizer.sanitize(text)?;
        self.names.insert(text.into(), value.clone());
        Ok(value)
    }
    fn identifier_raw(&mut self, id: &Identifier) -> Result<String, ConversionError> {
        Ok(match id {
            Identifier::Simple(s) => s.clone(),
            Identifier::Suffixed {
                prefix,
                separator,
                suffix,
            } => format!("{}{}{}", self.identifier_raw(prefix)?, separator, suffix),
            Identifier::SortBased { template, sorts } => {
                let mut chars = template.chars();
                let mut sorts = sorts.iter();
                let mut out = String::new();
                while let Some(c) = chars.next() {
                    if c != '%' {
                        out.push(c);
                        continue;
                    }
                    match chars.next() {
                        Some('%') => out.push('%'),
                        Some('s') => out.push_str(
                            &self.convert_sort(
                                sorts
                                    .next()
                                    .ok_or(ConversionError::InvalidIdentifierTemplate)?,
                            )?,
                        ),
                        _ => return Err(ConversionError::InvalidIdentifierTemplate),
                    }
                }
                out
            }
        })
    }
    pub fn convert_identifier(&mut self, id: &Identifier) -> Result<String, ConversionError> {
        let raw = self.identifier_raw(id)?;
        self.sanitize(&raw)
    }
    fn sort(&mut self, sort: &Sort, sanitize: bool) -> Result<String, ConversionError> {
        Ok(match sort {
            Sort::Int => "Int".into(),
            Sort::Bool => "Bool".into(),
            Sort::Perm => "$Perm".into(),
            Sort::Snap => "$Snap".into(),
            Sort::Ref => "$Ref".into(),
            Sort::Unit => String::new(),
            Sort::Seq(s) => format!("Seq<{}>", self.sort(s, true)?),
            Sort::Set(s) => format!("Set<{}>", self.sort(s, true)?),
            Sort::Multiset(s) => format!("Multiset<{}>", self.sort(s, true)?),
            Sort::Map(k, v) => format!("Map<{}~_{}>", self.sort(k, true)?, self.sort(v, true)?),
            Sort::Heap(s) => format!("$Hp<{}>", self.sort(s, true)?),
            Sort::WandHeap => "$Hp<$MWSF>".into(),
            Sort::PredHeap => "$Hp<$Pred>".into(),
            Sort::PredMask => "$Hp<$PredMask>".into(),
            Sort::UserSort(id) => self.convert_identifier(id)?,
            Sort::SmtSort(id) => {
                if sanitize {
                    self.convert_identifier(id)?
                } else {
                    id.name()
                }
            }
            Sort::FieldValueFunction { field_name, .. } => format!("$FVF<{field_name}>"),
            Sort::PredicateSnapFunction { predicate_name, .. } => format!("$PSF<{predicate_name}>"),
            Sort::MagicWandSnapFunction => "$MWSF".into(),
            Sort::FieldPermFunction => "$FPM".into(),
            Sort::PredicatePermFunction => "$PPM".into(),
        })
    }
    pub fn convert_sort(&mut self, sort: &Sort) -> Result<String, ConversionError> {
        self.sort(sort, false)
    }
    pub fn convert_sanitized_sort(&mut self, sort: &Sort) -> Result<String, ConversionError> {
        self.sort(sort, true)
    }
    fn heap_type(&mut self, sort: &Sort) -> Result<String, ConversionError> {
        match sort {
            Sort::Heap(s) => self.sort(s, true),
            Sort::PredHeap => Ok("$Pred".into()),
            Sort::PredMask => Ok("$PredMask".into()),
            Sort::WandHeap => Ok("$MWSF".into()),
            _ => Err(ConversionError::InvalidSort("expected heap sort")),
        }
    }
    fn application(
        &mut self,
        name: &str,
        args: &[Term],
        sort: &Sort,
        raw: bool,
    ) -> Result<String, ConversionError> {
        let name = if raw {
            name.to_owned()
        } else {
            self.sanitize(name)?
        };
        if args.is_empty() {
            return if raw {
                Ok(name)
            } else {
                Ok(format!("(as {name} {})", self.convert_sort(sort)?))
            };
        }
        let args = args
            .iter()
            .map(|t| self.convert_term(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("({name} {})", args.join(" ")))
    }
    fn op(&mut self, op: &str, args: &[&Term]) -> Result<String, ConversionError> {
        let args = args
            .iter()
            .map(|t| self.convert_term(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if args.is_empty() {
            format!("({op})")
        } else {
            format!("({op} {})", args.join(" "))
        })
    }
    fn real(&mut self, term: &Term) -> Result<String, ConversionError> {
        let rendered = self.convert_term(term)?;
        Ok(if term.sort() == &Sort::Int {
            format!("(to_real {rendered})")
        } else {
            rendered
        })
    }
    fn real_binary(&mut self, op: &str, a: &Term, b: &Term) -> Result<String, ConversionError> {
        Ok(format!("({op} {} {})", self.real(a)?, self.real(b)?))
    }
    fn resource_name(resource: &ResourceKey) -> &str {
        match resource {
            ResourceKey::Field(f) => &f.name,
            ResourceKey::Predicate(p) => &p.name,
            ResourceKey::Wand(_) => "$MWSF",
        }
    }
}

impl TermToSmtLib2Converter {
    pub fn convert_declaration(&mut self, decl: &Declaration) -> Result<String, ConversionError> {
        match decl.kind() {
            DeclarationKind::Sort(sort) => {
                Ok(format!("(declare-sort {} 0)", self.convert_sort(sort)?))
            }
            DeclarationKind::Function(fun) => self.function_declaration(fun),
            DeclarationKind::SortWrapper(from, to) => {
                let id = self.convert_identifier(&sort_wrapper_id(from.clone(), to.clone()))?;
                Ok(format!(
                    "(declare-fun {id} ({}) {})",
                    self.convert_sort(from)?,
                    self.convert_sort(to)?
                ))
            }
            DeclarationKind::Macro { id, args, body } => {
                let id = self.convert_identifier(id)?;
                let mut vars = Vec::new();
                for arg in args {
                    let TermKind::Var(v) = arg.kind() else {
                        return Err(ConversionError::InvalidSort(
                            "macro argument is not variable",
                        ));
                    };
                    vars.push(format!(
                        "({} {})",
                        self.convert_identifier(&v.id)?,
                        self.convert_sort(&v.sort)?
                    ));
                }
                Ok(format!(
                    "(define-fun {id} ({}) {}\n  {})",
                    vars.join(" "),
                    self.convert_sort(body.sort())?,
                    self.convert_term(body)?
                ))
            }
        }
    }
    fn function_declaration(
        &mut self,
        target: &ApplicationTarget,
    ) -> Result<String, ConversionError> {
        let id = self.convert_identifier(target.id())?;
        let (args, result) = match target {
            ApplicationTarget::Function(fun) => {
                (fun.data().arg_sorts.clone(), fun.data().result_sort.clone())
            }
            ApplicationTarget::Variable(var) => (vec![Sort::Unit], var.sort().clone()),
        };
        if args.is_empty() {
            Ok(format!(
                "(declare-const {id} {})",
                self.convert_sort(&result)?
            ))
        } else {
            let args = args
                .iter()
                .map(|s| self.convert_sort(s))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!(
                "(declare-fun {id} ({}) {})",
                args.join(" "),
                self.convert_sort(&result)?
            ))
        }
    }
    pub fn convert_term(&mut self, term: &Term) -> Result<String, ConversionError> {
        use TermKind::*;
        if matches!(
            term.kind(),
            HeapToSnap(..)
                | SnapToHeap(..)
                | HeapUpdate(..)
                | MaskAdd(..)
                | MergeSingle(..)
                | MergeHeaps(..)
        ) {
            if let Some(repr) = term.var_repr() {
                return self.convert_term(&repr);
            }
        }
        match term.kind() {
            Unit => Ok("$Snap.unit".into()),
            Null => Ok("$Ref.null".into()),
            ZeroMask => Ok("$Hp.zeroMask".into()),
            PredZeroMask => Ok("$Hp.zeroPredMask".into()),
            True => Ok("true".into()),
            False => Ok("false".into()),
            IntLiteral(n) => {
                use num_traits::Signed;
                Ok(if n.is_negative() {
                    format!("(- 0 {})", -n)
                } else {
                    n.to_string()
                })
            }
            Var(v) => self.convert_identifier(&v.id),
            SeqNil(_) => self.application("Seq_empty", &[], term.sort(), false),
            EmptySet(_) => self.application("Set_empty", &[], term.sort(), false),
            EmptyMultiset(_) => self.application("Multiset_empty", &[], term.sort(), false),
            EmptyMap(..) => self.application("Map_empty", &[], term.sort(), false),
            App { applicable, args } => {
                let raw = matches!(applicable, ApplicationTarget::Function(fun) if fun.data().kind == ApplicableKind::SmtFun);
                self.application(&applicable.id().name(), args, term.sort(), raw)
            }
            Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } => {
                if vars.is_empty() {
                    self.warnings.push(ConversionWarning::EmptyQuantifier {
                        quantifier: *quantifier,
                        name: name.clone(),
                    });
                    return Ok(format!(
                        "; WARNING: Got invalid quantifier (empty binders)\n{}",
                        self.convert_term(body)?
                    ));
                }
                let mut converted_vars = Vec::new();
                for v in vars {
                    let Var(v) = v.kind() else {
                        return Err(ConversionError::InvalidSort(
                            "quantifier binder is not variable",
                        ));
                    };
                    converted_vars.push(format!(
                        "({} {})",
                        self.convert_identifier(&v.id)?,
                        self.convert_sort(&v.sort)?
                    ));
                }
                let q = if *quantifier == Quantifier::Forall {
                    "forall"
                } else {
                    "exists"
                };
                let body = self.convert_term(body)?;
                let mut attrs = Vec::new();
                for trigger in triggers {
                    if !trigger.terms.is_empty() {
                        let ts = trigger
                            .terms
                            .iter()
                            .map(|t| self.convert_term(t))
                            .collect::<Result<Vec<_>, _>>()?;
                        attrs.push(format!(":pattern ({})", ts.join(" ")));
                    }
                }
                if !name.is_empty() {
                    attrs.push(format!(":qid |{name}|"));
                }
                if let Some(weight) = weight {
                    attrs.push(format!(":weight {weight}"));
                }
                if name.is_empty() && triggers.is_empty() {
                    Ok(format!(
                        "({q} ({}) {body}{})",
                        converted_vars.join(" "),
                        weight.map(|w| format!(" :weight {w}")).unwrap_or_default()
                    ))
                } else {
                    Ok(format!(
                        "({q} ({}) (! {body}{}))",
                        converted_vars.join(" "),
                        if attrs.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", attrs.join(" "))
                        }
                    ))
                }
            }
            Ite(a, b, c) => self.op("ite", &[a, b, c]),
            Not(a) => self.op("not", &[a]),
            And(ts) => self.op("and", &ts.iter().collect::<Vec<_>>()),
            Or(ts) => self.op("or", &ts.iter().collect::<Vec<_>>()),
            Implies(a, b) => self.op("=>", &[a, b]),
            Iff(a, b) => {
                let first = self.factory.implies(a.clone(), b.clone());
                let second = self.factory.implies(b.clone(), a.clone());
                let result = self.factory.and([first, second]);
                self.convert_term(&result)
            }
            BuiltinEquals(a, b) => self.op("=", &[a, b]),
            CustomEquals(a, b) => match a.sort() {
                Sort::Seq(_) => self.op("Seq_equal", &[a, b]),
                Sort::Set(_) => {
                    self.application("Set_equal", &[a.clone(), b.clone()], term.sort(), false)
                }
                Sort::Multiset(_) => self.application(
                    "Multiset_equal",
                    &[a.clone(), b.clone()],
                    term.sort(),
                    false,
                ),
                Sort::Map(..) => {
                    self.application("Map_equal", &[a.clone(), b.clone()], term.sort(), false)
                }
                _ => Err(ConversionError::InvalidSort("custom equality")),
            },
            Plus(a, b) => self.op("+", &[a, b]),
            Minus(a, b) => self.op("-", &[a, b]),
            Times(a, b) => self.op("*", &[a, b]),
            Div(a, b) => self.op("div", &[a, b]),
            Mod(a, b) => self.op("mod", &[a, b]),
            Less(a, b) => self.op("<", &[a, b]),
            AtMost(a, b) => self.op("<=", &[a, b]),
            Greater(a, b) => self.op(">", &[a, b]),
            AtLeast(a, b) => self.op(">=", &[a, b]),
            NoPerm => Ok("$Perm.No".into()),
            FullPerm => Ok("$Perm.Write".into()),
            FractionPermLiteral(r) => {
                let n = self.factory.int_literal(r.numerator().clone());
                let d = self.factory.int_literal(r.denominator().clone());
                self.real_binary("/", &n, &d)
            }
            FractionPerm(a, b) => self.real_binary("/", a, b),
            PermNegation(a) => self.op("-", &[a]),
            PermTimes(a, b) | IntPermTimes(a, b) => self.real_binary("*", a, b),
            PermIntDiv(a, b) | PermPermDiv(a, b) => self.real_binary("/", a, b),
            PermPlus(a, b) => self.real_binary("+", a, b),
            PermMinus(a, b) => self.real_binary("-", a, b),
            PermLess(a, b) => self.op("<", &[a, b]),
            PermAtMost(a, b) => self.op("<=", &[a, b]),
            PermMin(a, b) => self.op("$Perm.min", &[a, b]),
            IsValidPermVal(a) => self.op("$Perm.isValidVar", &[a]),
            IsReadPermVar(a) => self.op("$Perm.isReadVar", &[a]),
            SeqRanged(a, b) => self.op("Seq_range", &[a, b]),
            SeqSingleton(a) => self.op("Seq_singleton", &[a]),
            SeqAppend(a, b) => self.op("Seq_append", &[a, b]),
            SeqLength(a) => self.op("Seq_length", &[a]),
            SeqAt(a, b) => self.op("Seq_index", &[a, b]),
            SeqTake(a, b) => self.op("Seq_take", &[a, b]),
            SeqDrop(a, b) => self.op("Seq_drop", &[a, b]),
            SeqIn(a, b) => self.op("Seq_contains", &[a, b]),
            SeqInTrigger(a, b) => self.op("Seq_contains_trigger", &[a, b]),
            SeqUpdate(a, b, c) => self.op("Seq_update", &[a, b, c]),
            SingletonSet(a) => self.application("Set_singleton", &[a.clone()], term.sort(), false),
            SetAdd(a, b) => {
                self.application("Set_unionone", &[a.clone(), b.clone()], term.sort(), false)
            }
            SetCardinality(a) => self.application("Set_card", &[a.clone()], term.sort(), false),
            SetDifference(a, b) => self.application(
                "Set_difference",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            SetIntersection(a, b) => self.application(
                "Set_intersection",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            SetUnion(a, b) => {
                self.application("Set_union", &[a.clone(), b.clone()], term.sort(), false)
            }
            SetIn(a, b) => self.application("Set_in", &[a.clone(), b.clone()], term.sort(), false),
            SetSubset(a, b) => {
                self.application("Set_subset", &[a.clone(), b.clone()], term.sort(), false)
            }
            SetDisjoint(a, b) => {
                self.application("Set_disjoint", &[a.clone(), b.clone()], term.sort(), false)
            }
            SingletonMultiset(a) => {
                self.application("Multiset_singleton", &[a.clone()], term.sort(), false)
            }
            MultisetAdd(a, b) => self.application(
                "Multiset_unionone",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MultisetCardinality(a) => {
                self.application("Multiset_card", &[a.clone()], term.sort(), false)
            }
            MultisetDifference(a, b) => self.application(
                "Multiset_difference",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MultisetIntersection(a, b) => self.application(
                "Multiset_intersection",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MultisetUnion(a, b) => self.application(
                "Multiset_union",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MultisetSubset(a, b) => self.application(
                "Multiset_subset",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MultisetCount(a, b) => self.application(
                "Multiset_count",
                &[a.clone(), b.clone()],
                term.sort(),
                false,
            ),
            MapCardinality(a) => self.application("Map_card", &[a.clone()], term.sort(), false),
            MapDomain(a) => self.application("Map_domain", &[a.clone()], term.sort(), false),
            MapRange(a) => self.application("Map_values", &[a.clone()], term.sort(), false),
            MapLookup(a, b) => {
                self.application("Map_apply", &[a.clone(), b.clone()], term.sort(), false)
            }
            MapUpdate(a, b, c) => self.application(
                "Map_update",
                &[a.clone(), b.clone(), c.clone()],
                term.sort(),
                false,
            ),
            Domain(id, fvf) => self.op(&format!("$FVF.domain_{id}"), &[fvf]),
            HasDomain(id, fvf, _) => self.op(&format!("$FVF.has_domain_{id}"), &[fvf]),
            Lookup(id, fvf, at) => self.op(&format!("$FVF.lookup_{id}"), &[fvf, at]),
            PermLookup(id, pm, at) => self.op(&format!("$FVF.perm_{id}"), &[pm, at]),
            FieldTrigger(id, fvf, at) => {
                if matches!(fvf.sort(), Sort::FieldValueFunction { .. }) {
                    let lookup = self.factory.lookup(id.clone(), fvf.clone(), at.clone());
                    self.op(&format!("$FVF.loc_{id}"), &[&lookup, at])
                } else {
                    self.op(&format!("$FVF.loc_{id}"), &[fvf, at])
                }
            }
            PredicateDomain(id, psf) => self.op(&format!("$PSF.domain_{id}"), &[psf]),
            HasPredicateDomain(id, psf, _) => self.op(&format!("$PSF.has_domain_{id}"), &[psf]),
            PredicateLookup(id, psf, args) => {
                let snap = self.factory.to_snap_tree(args.clone());
                self.op(&format!("$PSF.lookup_{id}"), &[psf, &snap])
            }
            PredicatePermLookup(id, pm, args) => {
                let snap = self.factory.to_snap_tree(args.clone());
                self.op(&format!("$PSF.perm_{id}"), &[pm, &snap])
            }
            PredicateTrigger(id, psf, args) => {
                let snap = self.factory.to_snap_tree(args.clone());
                let lookup = self
                    .factory
                    .predicate_lookup(id.clone(), psf.clone(), args.clone());
                self.op(&format!("$PSF.loc_{id}"), &[&lookup, &snap])
            }
            HeapLookup(heap, at) => {
                let ty = self.heap_type(heap.sort())?;
                self.op(&format!("$Hp.get_{ty}"), &[heap, at])
            }
            HeapUpdate(heap, at, value) => {
                let ty = self.heap_type(heap.sort())?;
                self.op(&format!("$Hp.update_{ty}"), &[heap, at, value])
            }
            HeapSingleton(at, value, sort) => {
                let ty = self.heap_type(sort)?;
                self.op(&format!("$Hp.singleton_{ty}"), &[at, value])
            }
            IdenticalOnKnownLocations(old, new, mask) => {
                let ty = self.heap_type(new.sort())?;
                self.op(&format!("$Hp.identicalOnKnown_{ty}"), &[old, new, mask])
            }
            GoodMask(mask) => self.op("$Hp.maskGood", &[mask]),
            GoodFieldMask(mask, upper) => Ok(format!(
                "($Hp.maskGoodField {} {})",
                self.convert_term(mask)?,
                upper
            )),
            DummyHeap(sort) => Ok(format!("$Hp.default_{}", self.heap_type(sort)?)),
            MergeSingle(heap, mask, at, value) => {
                let ty = self.heap_type(heap.sort())?;
                self.op(&format!("$Hp.merge_single_{ty}"), &[heap, mask, at, value])
            }
            MergeHeaps(a, b, c, d) => {
                let ty = self.heap_type(a.sort())?;
                self.op(&format!("$Hp.merge_{ty}"), &[a, b, c, d])
            }
            HeapsOverlap(a, b, c, d) => {
                let ty = self.heap_type(a.sort())?;
                self.op(&format!("$Hp.overlap_{ty}"), &[a, b, c, d])
            }
            MaskEq(a, b) => self.op("$Hp.maskEq", &[a, b]),
            MaskSum(a, b) => self.op("$Hp.maskSum", &[a, b]),
            MaskDiff(a, b) => self.op("$Hp.maskDiff", &[a, b]),
            MaskAdd(a, b, c) => self.op("$Hp.maskAdd", &[a, b, c]),
            HeapToSnap(heap, mask, resource) => self.op(
                &format!(
                    "$SortWrappers.$Heap<{}>To$Snap",
                    Self::resource_name(resource)
                ),
                &[heap, mask],
            ),
            SnapToHeap(snap, resource, _) => self.op(
                &format!(
                    "$SortWrappers.$SnapTo$Heap<{}>",
                    Self::resource_name(resource)
                ),
                &[snap],
            ),
            First(a) => self.op("$Snap.first", &[a]),
            Second(a) => self.op("$Snap.second", &[a]),
            Combine(a, b) => self.op("$Snap.combine", &[a, b]),
            SortWrapper(a, to) => {
                let name =
                    self.convert_identifier(&sort_wrapper_id(a.sort().clone(), to.clone()))?;
                self.op(&name, &[a])
            }
            Distinct(functions) => {
                let names = functions
                    .iter()
                    .map(|fun| self.convert_identifier(&fun.data().id))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("(distinct {})", names.join(" ")))
            }
            Let(bindings, body) => {
                let mut pairs = Vec::new();
                for (var, value) in bindings.iter() {
                    pairs.push(format!(
                        "({} {})",
                        self.convert_term(var)?,
                        self.convert_term(value)?
                    ));
                }
                Ok(format!(
                    "(let ({}) {})",
                    pairs.join(" "),
                    self.convert_term(body)?
                ))
            }
            MagicWandSnapshot(mwsf) => self.convert_term(mwsf),
            MwsfLookup(mwsf, snap) => self.application(
                "MWSF_apply",
                &[mwsf.clone(), snap.clone()],
                &Sort::Snap,
                false,
            ),
            MagicWandToken(mwsf, snap) => self.application(
                "MW_token",
                &[mwsf.clone(), snap.clone()],
                &Sort::Bool,
                false,
            ),
            MagicWandChunkTerm(_) => Err(ConversionError::UnsupportedTerm("MagicWandChunkTerm")),
            AppHint(_) => Err(ConversionError::UnsupportedTerm("AppHint")),
            MaskMapTerm(_) => Err(ConversionError::UnsupportedTerm("MaskMapTerm")),
            HeapMapTerm(_) => Err(ConversionError::UnsupportedTerm("HeapMapTerm")),
        }
    }
}
impl TermConverter for TermToSmtLib2Converter {
    type TermOutput = String;
    type SortOutput = String;
    type DeclarationOutput = String;
    type Error = ConversionError;
    fn convert_term(&mut self, term: &Term) -> Result<String, ConversionError> {
        Self::convert_term(self, term)
    }
    fn convert_sort(&mut self, sort: &Sort) -> Result<String, ConversionError> {
        Self::convert_sort(self, sort)
    }
    fn convert_sanitized_sort(&mut self, sort: &Sort) -> Result<String, ConversionError> {
        Self::convert_sanitized_sort(self, sort)
    }
    fn convert_declaration(&mut self, decl: &Declaration) -> Result<String, ConversionError> {
        Self::convert_declaration(self, decl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::{TermOptions, Trigger};
    fn factory() -> TermFactory {
        TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: true,
            mask_heap_mode: false,
        })
    }
    #[test]
    fn sorts_names_and_quantified_empty_patterns_follow_source_dispatch() {
        let f = factory();
        let mut converter = TermToSmtLib2Converter::new(f.clone());
        let x = f.var(Identifier::new("x#1"), Sort::Int, false);
        let q = f
            .quantification(
                Quantifier::Forall,
                vec![x.clone()],
                f.equals(x, f.int_literal(1)),
                vec![Trigger { terms: vec![] }],
                "qid".into(),
                false,
                Some(2),
            )
            .unwrap();
        assert_eq!(
            converter.convert_term(&q).unwrap(),
            "(forall ((x%1 Int)) (! (= x%1 1) :qid |qid| :weight 2))"
        );
        assert_eq!(
            converter
                .convert_sanitized_sort(&Sort::SmtSort(Identifier::new("Int")))
                .unwrap(),
            "Int_"
        );
        assert_eq!(
            converter
                .convert_sort(&Sort::SmtSort(Identifier::new("Int")))
                .unwrap(),
            "Int"
        );
    }
    #[test]
    fn empty_quantifier_warns_and_renders_body() {
        let f = factory();
        let mut converter = TermToSmtLib2Converter::new(f.clone());
        let term = f.quantification_without_triggers(
            Quantifier::Forall,
            vec![],
            f.boolean(true),
            "empty".into(),
            false,
            None,
        );
        let output = converter.convert_term(&term).unwrap();
        assert!(output.starts_with("; WARNING: Got invalid quantifier"));
        assert!(output.ends_with("\ntrue"));
        assert_eq!(
            converter.warnings(),
            &[ConversionWarning::EmptyQuantifier {
                quantifier: Quantifier::Forall,
                name: "empty".into()
            }]
        );
    }

    #[test]
    fn zero_argument_application_and_negative_numbers_are_solver_syntax() {
        let f = factory();
        let mut converter = TermToSmtLib2Converter::new(f.clone());
        assert_eq!(
            converter.convert_term(&f.int_literal(-3)).unwrap(),
            "(- 0 3)"
        );
        assert_eq!(
            converter.convert_term(&f.seq_nil(Sort::Int)).unwrap(),
            "(as Seq_empty Seq<Int>)"
        );
    }
}
