//! Counterexample values and rational permissions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Counterexample.scala
//! Status: partial; raw and resolved data, rendering, literal conversion, Rational,
//! and wand substitution are implemented. Backend model extraction and unported AST
//! pretty-printer/rewriter extension cases remain explicit fallible boundaries.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind},
    r#type::Type,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use regex::Regex;
use std::{cmp::Ordering, fmt, sync::OnceLock};

pub fn parse_int(value: &str) -> Option<BigInt> {
    let value = value.trim();
    if let Ok(i) = value.parse() {
        return Some(i);
    }
    static NEGATIVE: OnceLock<Regex> = OnceLock::new();
    let captures = NEGATIVE
        .get_or_init(|| Regex::new(r"^\(\s*-\s*(\d+)\s*\)$").unwrap())
        .captures(value)?;
    captures[1].parse::<BigInt>().ok().map(|n| -n)
}
pub fn parse_bool(value: &str) -> Option<bool> {
    match value.trim().to_lowercase().as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}
fn rational_token(value: &str) -> Option<(BigInt, BigInt)> {
    let value = value.trim();
    let mut pieces: Vec<_> = value.split('/').collect();
    if !value.is_empty() {
        while pieces.last() == Some(&"") {
            pieces.pop();
        }
    }
    match pieces.as_slice() {
        [n, d] => {
            let n = parse_int(n)?;
            let d = parse_int(d)?;
            (!d.is_zero()).then_some((n, d))
        }
        [single] if single.contains('.') => {
            let (i, f) = single.split_once('.')?;
            let digits = format!("{i}{f}");
            Some((
                parse_int(if digits.is_empty() { "0" } else { &digits })?,
                BigInt::from(10).pow(f.len().try_into().ok()?),
            ))
        }
        [single] => Some((parse_int(single)?, BigInt::one())),
        _ => None,
    }
}
pub fn parse_perm(value: &str) -> Option<Exp> {
    static DIV: OnceLock<Regex> = OnceLock::new();
    let value = value.trim();
    let (n, d) = if let Some(c) = DIV
        .get_or_init(|| Regex::new(r"^\(\s*/\s+(\S+)\s+(\S+)\s*\)$").unwrap())
        .captures(value)
    {
        let (an, ad) = rational_token(&c[1])?;
        let (bn, bd) = rational_token(&c[2])?;
        if bn.is_zero() {
            return None;
        }
        (an * bd, ad * bn)
    } else {
        rational_token(value)?
    };
    // Scala reduces by a nonnegative gcd, but does not normalize the denominator's sign here.
    let gcd = BigRational::new(n.clone(), d.clone()).denom().clone();
    let divisor = d.abs() / gcd;
    Some(Exp::new(
        ExpKind::BackendValueLit(format!("{}/{}", n / &divisor, d / divisor), Type::Perm),
        Metadata::default(),
    ))
}
pub fn infer_literal(value: &str) -> Exp {
    literal(value, None)
}
pub fn literal(value: &str, typ: Option<&Type>) -> Exp {
    let kind = match typ {
        Some(Type::Int) => parse_int(value)
            .map(ExpKind::IntLit)
            .unwrap_or_else(|| ExpKind::BackendValueLit(value.into(), Type::Int)),
        Some(Type::Bool) => parse_bool(value)
            .map(|v| {
                if v {
                    ExpKind::TrueLit
                } else {
                    ExpKind::FalseLit
                }
            })
            .unwrap_or_else(|| ExpKind::BackendValueLit(value.into(), Type::Bool)),
        Some(Type::Ref) => ExpKind::RefLit(value.into()),
        Some(Type::Perm) => {
            return parse_perm(value).unwrap_or_else(|| {
                Exp::new(
                    ExpKind::BackendValueLit(value.into(), Type::Perm),
                    Metadata::default(),
                )
            });
        }
        Some(t) => ExpKind::BackendValueLit(value.into(), t.clone()),
        None => {
            if let Some(n) = parse_int(value) {
                ExpKind::IntLit(n)
            } else if let Some(b) = parse_bool(value) {
                if b {
                    ExpKind::TrueLit
                } else {
                    ExpKind::FalseLit
                }
            } else {
                ExpKind::BackendValueLit(value.into(), Type::InternalType)
            }
        }
    };
    Exp::new(kind, Metadata::default())
}

/// Exact normalized rational. The Scala hash uses the original inputs despite normalized
/// equality, so no Hash implementation is offered here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rational(BigRational);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroDenominator;
impl Rational {
    pub fn new(n: BigInt, d: BigInt) -> Result<Self, ZeroDenominator> {
        if d.is_zero() {
            Err(ZeroDenominator)
        } else {
            Ok(Self(BigRational::new(n, d)))
        }
    }
    pub fn numerator(&self) -> &BigInt {
        self.0.numer()
    }
    pub fn denominator(&self) -> &BigInt {
        self.0.denom()
    }
    pub fn inverse(&self) -> Result<Self, ZeroDenominator> {
        Self::new(self.denominator().clone(), self.numerator().clone())
    }
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }
    pub fn signum(&self) -> Self {
        Self(BigRational::from_integer(self.numerator().signum()))
    }
    pub fn add(&self, other: &Self) -> Self {
        Self(&self.0 + &other.0)
    }
    pub fn subtract(&self, other: &Self) -> Self {
        Self(&self.0 - &other.0)
    }
    pub fn multiply(&self, other: &Self) -> Self {
        Self(&self.0 * &other.0)
    }
    pub fn divide(&self, other: &Self) -> Result<Self, ZeroDenominator> {
        Ok(self.multiply(&other.inverse()?))
    }
    pub fn negate(&self) -> Self {
        Self(-&self.0)
    }
}
impl Ord for Rational {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.0.cmp(&rhs.0)
    }
}
impl PartialOrd for Rational {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}
impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator(), self.denominator())
    }
}

/// The six source heap-entry categories, including the quantified variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HeapEntryType {
    Field,
    Predicate,
    QuantifiedField,
    QuantifiedPredicate,
    MagicWand,
    QuantifiedMagicWand,
}
impl HeapEntryType {
    pub fn is_quantified(self) -> bool {
        matches!(
            self,
            Self::QuantifiedField | Self::QuantifiedPredicate | Self::QuantifiedMagicWand
        )
    }
}

/// Source map entries use expression equality. A vector retains those keys without
/// imposing a new hash implementation on the Silver AST; iteration order is supplied
/// by the backend and is not a guarantee of Scala map ordering.
#[derive(Clone, Debug)]
pub struct PredicateModel(Vec<(Exp, super::verification_error::ModelEntry)>);
impl PredicateModel {
    pub fn new(
        entries: impl IntoIterator<Item = (Exp, super::verification_error::ModelEntry)>,
    ) -> Self {
        let mut values: Vec<(Exp, super::verification_error::ModelEntry)> = Vec::new();
        for (key, value) in entries {
            if let Some((_, old)) = values.iter_mut().find(|(k, _)| *k == key) {
                *old = value;
            } else {
                values.push((key, value));
            }
        }
        Self(values)
    }
    pub fn entries(&self) -> &[(Exp, super::verification_error::ModelEntry)] {
        &self.0
    }
}
impl PartialEq for PredicateModel {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(key, value)| other.0.iter().any(|(k, v)| key == k && value == v))
    }
}
impl Eq for PredicateModel {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawHeapEntry {
    pub reference: Vec<String>,
    pub field: Vec<String>,
    pub value_id: String,
    pub perm: Option<Rational>,
    pub entry_type: HeapEntryType,
    pub inside_predicate: Option<PredicateModel>,
}
#[derive(Clone, Debug)]
pub struct RawHeap {
    entries: Vec<RawHeapEntry>,
}
impl PartialEq for RawHeap {
    fn eq(&self, other: &Self) -> bool {
        self.entries.len() == other.entries.len()
            && self.entries.iter().all(|e| other.entries.contains(e))
    }
}
impl Eq for RawHeap {}
impl RawHeap {
    /// Scala's source stores a Set: keep one structurally equal entry.
    pub fn new(entries: impl IntoIterator<Item = RawHeapEntry>) -> Self {
        let mut unique = Vec::new();
        for entry in entries {
            if !unique.contains(&entry) {
                unique.push(entry);
            }
        }
        Self { entries: unique }
    }
    pub fn entries(&self) -> &[RawHeapEntry] {
        &self.entries
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CeVariable {
    pub name: String,
    pub value: Exp,
    pub typ: Option<Type>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CeCollection {
    pub id: String,
    pub value: Exp,
}
/// String-keyed source map with last-write semantics and order-independent equality.
#[derive(Clone, Debug, Default)]
pub struct FunctionOptions(Vec<(Vec<String>, String)>);
impl FunctionOptions {
    pub fn new(entries: impl IntoIterator<Item = (Vec<String>, String)>) -> Self {
        let mut result: Vec<(Vec<String>, String)> = Vec::new();
        for (key, value) in entries {
            if let Some((_, old)) = result.iter_mut().find(|(existing, _)| *existing == key) {
                *old = value;
            } else {
                result.push((key, value));
            }
        }
        Self(result)
    }
    pub fn entries(&self) -> &[(Vec<String>, String)] {
        &self.0
    }
}
impl PartialEq for FunctionOptions {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(key, value)| other.0.iter().any(|(k, v)| key == k && value == v))
    }
}
impl Eq for FunctionOptions {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicFunctionEntry {
    pub name: String,
    pub argument_types: Vec<Type>,
    pub return_type: Type,
    pub options: FunctionOptions,
    pub default: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicDomainEntry {
    pub name: String,
    pub types: Vec<Type>,
    pub functions: Vec<BasicFunctionEntry>,
}
/// The backend supplies the model data; collection order is sequences, sets,
/// multisets, then maps, exactly as in the source lazy accessor.
pub trait RawCounterexample {
    fn basic_variables(&self) -> &[CeVariable];
    fn all_sequences(&self) -> &[CeCollection];
    fn all_sets(&self) -> &[CeCollection];
    fn all_multisets(&self) -> &[CeCollection];
    fn all_maps(&self) -> &[CeCollection];
    fn all_raw_heaps(&self) -> &[(String, RawHeap)];
    fn domain_entries(&self) -> &[BasicDomainEntry];
    fn non_domain_functions(&self) -> &[BasicFunctionEntry];
    fn all_collections(&self) -> Vec<&CeCollection> {
        self.all_sequences()
            .iter()
            .chain(self.all_sets())
            .chain(self.all_multisets())
            .chain(self.all_maps())
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoreEntry {
    id: Exp,
    pub entry: Exp,
}
impl StoreEntry {
    /// AbstractLocalVar includes local, result, and versioned-variable forms.
    pub fn new(id: Exp, entry: Exp) -> Result<Self, InvalidStoreVariable> {
        if matches!(
            id.kind(),
            ExpKind::LocalVar(_) | ExpKind::Result(_) | ExpKind::LocalVarWithVersion(..)
        ) {
            Ok(Self { id, entry })
        } else {
            Err(InvalidStoreVariable)
        }
    }
    pub fn id(&self) -> &Exp {
        &self.id
    }
    pub fn name(&self) -> &str {
        match self.id.kind() {
            ExpKind::LocalVar(v) => &v.name,
            ExpKind::LocalVarWithVersion(name, _) => name,
            ExpKind::Result(_) => "result",
            _ => unreachable!("StoreEntry::new validates the variable"),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidStoreVariable;
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StoreCounterexample {
    pub store_entries: Vec<StoreEntry>,
}
impl StoreCounterexample {
    /// Source `toMap` keeps the last value for repeated names.
    pub fn as_map(&self) -> std::collections::HashMap<String, Exp> {
        self.store_entries
            .iter()
            .map(|e| (e.name().to_owned(), e.entry.clone()))
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedHeapEntry {
    Field {
        reference: String,
        field: String,
        entry: Exp,
        perm: Option<Rational>,
        typ: Type,
        entry_type: HeapEntryType,
    },
    Predicate {
        name: String,
        args: Vec<Exp>,
        perm: Option<Rational>,
        inside_predicate: Option<PredicateModel>,
        entry_type: HeapEntryType,
    },
    Wand {
        left: Exp,
        right: Exp,
        perm: Option<Rational>,
        entry_type: HeapEntryType,
    },
}
impl ResolvedHeapEntry {
    pub fn entry_type(&self) -> HeapEntryType {
        match self {
            Self::Field { entry_type, .. }
            | Self::Predicate { entry_type, .. }
            | Self::Wand { entry_type, .. } => *entry_type,
        }
    }
    /// Canonicalize with unique hole names, zip available backend values with
    /// holes, and simultaneously substitute as in WandResolvedEntry.fromStructure.
    pub fn wand_from_structure(
        wand: &Exp,
        values: &[String],
        perm: Option<Rational>,
        entry_type: HeapEntryType,
        program: &crate::ast::program::Program,
    ) -> Result<Self, WandResolutionError> {
        use crate::ast::utility::{
            expressions::magic_wand_subexpressions,
            nodes::{Node, replace_expressions},
        };
        let structure = wand
            .magic_wand_structure(program, true)
            .map_err(WandResolutionError::Wand)?;
        let holes =
            magic_wand_subexpressions(&structure, program).map_err(WandResolutionError::Wand)?;
        let replacements = holes
            .iter()
            .zip(values)
            .map(|(hole, value)| {
                let typ = hole.typ().map_err(WandResolutionError::Type)?;
                Ok((hole.clone(), literal(value, Some(&typ))))
            })
            .collect::<Result<Vec<_>, WandResolutionError>>()?;
        let Node::Exp(result) = replace_expressions(&Node::Exp(structure), &replacements)
            .map_err(WandResolutionError::Replacement)?
        else {
            return Err(WandResolutionError::InvalidResult);
        };
        let ExpKind::MagicWand(left, right) = result.kind() else {
            return Err(WandResolutionError::InvalidResult);
        };
        Ok(Self::Wand {
            left: left.clone(),
            right: right.clone(),
            perm,
            entry_type,
        })
    }
}
#[derive(Debug)]
pub enum WandResolutionError {
    Wand(crate::ast::utility::expressions::MagicWandError),
    Type(crate::ast::expression::ExpressionTypeError),
    Replacement(crate::ast::utility::nodes::NodeReplacementError),
    InvalidResult,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HeapCounterexample {
    pub heap_entries: Vec<(
        crate::ast::utility::quantified_permissions::Resource,
        ResolvedHeapEntry,
    )>,
}
impl HeapCounterexample {
    pub fn contains_quantified_permissions(&self) -> bool {
        self.heap_entries
            .iter()
            .any(|(_, entry)| entry.entry_type().is_quantified())
    }
}
/// Resolved model exposes source heap and domain/function views without forcing
/// a display implementation for unsupported AST printer extensions.
pub trait ResolvedCounterexample {
    fn raw_ce(&self) -> &dyn RawCounterexample;
    fn store(&self) -> &StoreCounterexample;
    fn heaps(&self) -> &[(String, HeapCounterexample)];
    fn domain_entries(&self) -> &[BasicDomainEntry];
    fn function_entries(&self) -> &[BasicFunctionEntry];
    fn heap_map(&self) -> std::collections::HashMap<String, &HeapCounterexample> {
        self.heaps()
            .iter()
            .map(|(name, heap)| (name.clone(), heap))
            .collect()
    }
}

impl CeVariable {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        use crate::ast::pretty::pretty_printer::{pretty_expression, show_type};
        Ok(format!(
            "Variable Name: {}, Value: {}, Type: {}",
            self.name,
            pretty_expression(&self.value)?,
            match &self.typ {
                Some(t) => show_type(t)?,
                None => "None".into(),
            }
        ))
    }
}
impl CeCollection {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        Ok(format!(
            "{} = {}",
            self.id,
            crate::ast::pretty::pretty_printer::pretty_expression(&self.value)?
        ))
    }
}
impl StoreCounterexample {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        let lines = self
            .store_entries
            .iter()
            .map(StoreEntry::render)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{}\n", lines.join("\n")))
    }
}
impl StoreEntry {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        use crate::ast::pretty::pretty_printer::{pretty_expression, show_type};
        let typ = match self.id.kind() {
            ExpKind::LocalVar(v) => &v.typ,
            ExpKind::LocalVarWithVersion(_, typ) | ExpKind::Result(typ) => typ,
            _ => unreachable!("validated variable"),
        };
        Ok(format!(
            "Variable Name: {}, Value: {}, Type: {}",
            self.name(),
            pretty_expression(&self.entry)?,
            show_type(typ)?
        ))
    }
}
fn render_predicate_model(
    value: &Option<PredicateModel>,
) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
    match value {
        Some(model) if !model.entries().is_empty() => {
            let entries = model
                .entries()
                .iter()
                .map(|(key, value)| {
                    Ok(format!(
                        "{} --> {}",
                        crate::ast::pretty::pretty_printer::pretty_expression(key)?,
                        value
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("{{\n   {}\n}}", entries.join("\n   ")))
        }
        _ => Ok(String::new()),
    }
}
impl RawHeapEntry {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        let reference = format!("({})", self.reference.join(", "));
        let field = format!("({})", self.field.join(", "));
        let perm = self
            .perm
            .as_ref()
            .map(ToString::to_string)
            .unwrap_or_else(|| "None".into());
        if self.entry_type == HeapEntryType::Predicate {
            Ok(format!(
                "Heap entry: {reference} + {field} --> (Permission: {perm}) {}",
                render_predicate_model(&self.inside_predicate)?
            ))
        } else {
            Ok(format!(
                "Heap entry: {reference} + {field} --> (Value: {}, Permission: {perm})",
                self.value_id
            ))
        }
    }
}
impl RawHeap {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        Ok(self
            .entries
            .iter()
            .map(RawHeapEntry::render)
            .collect::<Result<Vec<_>, _>>()?
            .join("\n"))
    }
}
impl ResolvedHeapEntry {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        use crate::ast::pretty::pretty_printer::{pretty_expression, show_type};
        fn permission(p: &Option<Rational>) -> String {
            p.as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "#undefined".into())
        }
        Ok(match self {
            Self::Field {
                reference,
                field,
                entry,
                perm,
                typ,
                ..
            } => format!(
                "Field Entry: {reference}.{field} --> (Value: {}, Type: {}, Perm: {})",
                pretty_expression(entry)?,
                show_type(typ)?,
                permission(perm)
            ),
            Self::Predicate {
                name,
                args,
                perm,
                inside_predicate,
                ..
            } => format!(
                "Predicate Entry: {name}({}) --> (Perm: {}) {}",
                args.iter()
                    .map(pretty_expression)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", "),
                permission(perm),
                render_predicate_model(inside_predicate)?
            ),
            Self::Wand {
                left, right, perm, ..
            } => {
                let wand = Exp::new(
                    ExpKind::MagicWand(left.clone(), right.clone()),
                    Metadata::default(),
                );
                format!(
                    "Magic Wand Entry: {} (Perm: {})",
                    pretty_expression(&wand)?,
                    permission(perm)
                )
            }
        })
    }
}
impl HeapCounterexample {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        let mut result = String::new();
        if self.contains_quantified_permissions() {
            result.push_str("The heap contains quantified permissions. Thus, we might own some permissions which are not shown in the counterexample.\n");
        }
        for (_, entry) in &self.heap_entries {
            result.push_str(&entry.render()?);
            result.push('\n');
        }
        Ok(result)
    }
}

impl BasicDomainEntry {
    pub fn value_name(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        let types = self
            .types
            .iter()
            .map(crate::ast::pretty::pretty_printer::show_type)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if types.is_empty() {
            self.name.clone()
        } else {
            format!("{}[{}]", self.name, types.join(", "))
        })
    }
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        Ok(format!(
            "domain {}{{\n {}\n}}",
            self.value_name()?,
            self.functions
                .iter()
                .map(BasicFunctionEntry::render)
                .collect::<Result<Vec<_>, _>>()?
                .join("\n")
        ))
    }
}
impl BasicFunctionEntry {
    pub fn render(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        use crate::ast::pretty::pretty_printer::show_type;
        if self.options.entries().is_empty() {
            return Ok(format!("{}{{\n    {}\n}}", self.name, self.default));
        }
        let args = self
            .argument_types
            .iter()
            .map(show_type)
            .collect::<Result<Vec<_>, _>>()?
            .join(",");
        let options = self
            .options
            .entries()
            .iter()
            .map(|(args, value)| format!("    {} -> {}", args.join(" "), value))
            .collect::<Vec<_>>()
            .join("\n");
        Ok(format!(
            "{}({}):{}{{\n{}\n    else -> {}\n}}",
            self.name,
            args,
            show_type(&self.return_type)?,
            options,
            self.default
        ))
    }
}
/// Heterogeneous source `domainsAndFunctions` view, preserving each sequence's order.
pub enum DomainOrFunction<'a> {
    Domain(&'a BasicDomainEntry),
    Function(&'a BasicFunctionEntry),
}
impl dyn ResolvedCounterexample + '_ {
    pub fn domains_and_functions(&self) -> Vec<DomainOrFunction<'_>> {
        self.domain_entries()
            .iter()
            .map(DomainOrFunction::Domain)
            .chain(
                self.function_entries()
                    .iter()
                    .map(DomainOrFunction::Function),
            )
            .collect()
    }
}

#[cfg(test)]
mod model_tests {
    use super::*;
    #[test]
    fn wand_resolution_substitutes_backend_values_in_hole_order() {
        let meta = Metadata::default();
        let wand = Exp::new(
            ExpKind::MagicWand(
                Exp::new(ExpKind::TrueLit, meta.clone()),
                Exp::new(ExpKind::FalseLit, meta.clone()),
            ),
            meta.clone(),
        );
        let program =
            crate::ast::program::Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta);
        let result = ResolvedHeapEntry::wand_from_structure(
            &wand,
            &["false".into(), "true".into()],
            None,
            HeapEntryType::MagicWand,
            &program,
        )
        .unwrap();
        let ResolvedHeapEntry::Wand { left, right, .. } = result else {
            panic!("wand")
        };
        assert!(matches!(left.kind(), ExpKind::FalseLit));
        assert!(matches!(right.kind(), ExpKind::TrueLit));
    }
    #[test]
    fn heap_and_function_maps_compare_without_insertion_order() {
        let left = FunctionOptions::new([
            (vec!["x".into()], "1".into()),
            (vec!["y".into()], "2".into()),
        ]);
        let right = FunctionOptions::new([
            (vec!["y".into()], "2".into()),
            (vec!["x".into()], "old".into()),
            (vec!["x".into()], "1".into()),
        ]);
        assert_eq!(left, right);
        let entry = RawHeapEntry {
            reference: vec!["r".into()],
            field: vec!["f".into()],
            value_id: "v".into(),
            perm: None,
            entry_type: HeapEntryType::Field,
            inside_predicate: None,
        };
        assert_eq!(
            RawHeap::new([entry.clone(), entry.clone()]).entries().len(),
            1
        );
        assert_eq!(RawHeap::new([entry.clone()]), RawHeap::new([entry]));
    }
}
