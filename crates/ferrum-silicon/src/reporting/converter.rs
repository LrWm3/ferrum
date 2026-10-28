//! Silicon model extraction and interpretation.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Converter.scala
//! Status: partial; extracted data families, function application, scalar conversion,
//! and source term evaluation are implemented. Recursive heap/store extraction and
//! domain/function discovery remain explicit integration boundaries.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use crate::state::{chunks::Chunk, terms::Sort};
use ferrum_silver::{
    ast::r#type::Type,
    utility::common::Rational,
    verifier::verification_error::{Model, ModelEntry, ValueEntry},
};
use num_bigint::BigInt;
use std::fmt;

#[derive(Clone, Debug)]
pub enum ExtractedModelEntry {
    Int(BigInt),
    Bool(bool),
    Perm(Rational),
    Ref {
        name: String,
        fields: Vec<(String, (ExtractedModelEntry, Option<Rational>))>,
    },
    NullRef(String),
    RecursiveRef(String),
    Var {
        name: String,
        sort: Sort,
    },
    Other {
        value: String,
        problem: String,
    },
    Seq {
        name: String,
        values: Vec<ExtractedModelEntry>,
    },
    Set {
        name: String,
        values: Vec<ExtractedModelEntry>,
    },
    Multiset {
        name: String,
        values: Vec<(ExtractedModelEntry, i32)>,
    },
    Unprocessed(ValueEntry),
    DomainValue {
        domain: String,
        id: String,
    },
    ExtendedDomain {
        original: Box<ExtractedModelEntry>,
        info: Vec<(ExtractedFunction, ExtractedModelEntry)>,
    },
    Predicate {
        name: String,
        args: Vec<ExtractedModelEntry>,
        perm: Option<Rational>,
    },
}
fn unordered_map_equal<K: PartialEq, V: PartialEq>(a: &[(K, V)], b: &[(K, V)]) -> bool {
    a.len() == b.len()
        && a.iter()
            .all(|(key, value)| b.iter().any(|(k, v)| key == k && value == v))
}
impl PartialEq for ExtractedModelEntry {
    fn eq(&self, other: &Self) -> bool {
        use ExtractedModelEntry::*;
        match (self, other) {
            (Int(a), Int(b)) => a == b,
            (Bool(a), Bool(b)) => a == b,
            (Perm(a), Perm(b)) => a == b,
            (Ref { name: a, fields: x }, Ref { name: b, fields: y }) => {
                a == b && unordered_map_equal(x, y)
            }
            (NullRef(a), NullRef(b)) | (RecursiveRef(a), RecursiveRef(b)) => a == b,
            (Var { name: a, sort: x }, Var { name: b, sort: y }) => a == b && x == y,
            (
                Other {
                    value: a,
                    problem: x,
                },
                Other {
                    value: b,
                    problem: y,
                },
            ) => a == b && x == y,
            (Seq { name: a, values: x }, Seq { name: b, values: y }) => a == b && x == y,
            (Set { name: a, values: x }, Set { name: b, values: y }) => {
                a == b && x.len() == y.len() && x.iter().all(|v| y.contains(v))
            }
            (Multiset { name: a, values: x }, Multiset { name: b, values: y }) => {
                a == b && unordered_map_equal(x, y)
            }
            (Unprocessed(a), Unprocessed(b)) => a == b,
            (DomainValue { domain: a, id: x }, DomainValue { domain: b, id: y }) => {
                a == b && x == y
            }
            (
                ExtendedDomain {
                    original: a,
                    info: x,
                },
                ExtendedDomain {
                    original: b,
                    info: y,
                },
            ) => a == b && unordered_map_equal(x, y),
            (
                Predicate {
                    name: a,
                    args: x,
                    perm: p,
                },
                Predicate {
                    name: b,
                    args: y,
                    perm: q,
                },
            ) => a == b && x == y && p == q,
            _ => false,
        }
    }
}
impl Eq for ExtractedModelEntry {}
impl ExtractedModelEntry {
    pub fn as_value_entry(&self) -> ValueEntry {
        match self {
            Self::Int(value) if value < &BigInt::from(0) => ValueEntry::Application {
                name: "-".into(),
                arguments: vec![ValueEntry::Constant((-value).to_string())],
            },
            Self::Int(value) => ValueEntry::Constant(value.to_string()),
            Self::Bool(value) => ValueEntry::Constant(value.to_string()),
            Self::Perm(value) => ValueEntry::Constant(value.to_string()),
            Self::Ref { name, .. }
            | Self::NullRef(name)
            | Self::RecursiveRef(name)
            | Self::Var { name, .. }
            | Self::Seq { name, .. }
            | Self::Set { name, .. }
            | Self::Multiset { name, .. }
            | Self::Predicate { name, .. } => ValueEntry::Constant(name.clone()),
            Self::Other { value, .. } => ValueEntry::Constant(value.clone()),
            Self::Unprocessed(value) => value.clone(),
            Self::DomainValue { .. } => ValueEntry::Constant(self.to_string()),
            Self::ExtendedDomain { original, .. } => original.as_value_entry(),
        }
    }
    pub fn domain_name(&self) -> Option<&str> {
        if let Self::DomainValue { domain, .. } = self {
            Some(domain.split('[').next().unwrap_or(domain))
        } else {
            None
        }
    }
}
impl fmt::Display for ExtractedModelEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(v) => write!(f, "{v}"),
            Self::Bool(v) => write!(f, "{v}"),
            Self::Perm(v) => write!(f, "{v}"),
            Self::Ref { name, fields } => {
                write!(f, "Ref ({name}) {{\n")?;
                for (name, (entry, perm)) in fields {
                    write!(
                        f,
                        "\t{}(perm: {}) <- {}\n",
                        name,
                        perm.as_ref()
                            .map(ToString::to_string)
                            .unwrap_or_else(|| "?".into()),
                        entry.to_string().replace('\n', "\n\t")
                    )?;
                }
                write!(f, "}}")
            }
            Self::NullRef(name) => write!(f, "Null({name})"),
            Self::RecursiveRef(name) => write!(f, "recursive reference to {name}"),
            Self::Var { name, .. } => write!(f, "{name}"),
            Self::Other { value, problem } => write!(f, "{value} [{problem}]"),
            Self::Seq { name, values } => write!(
                f,
                "({name}): [{}]",
                values
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Set { name, values } => write!(
                f,
                "({name}): {{{}}}",
                values
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Multiset { name, values } => write!(
                f,
                "({name}): {{{}}}",
                values
                    .iter()
                    .map(|(v, n)| format!("({v},{n})"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::Unprocessed(v) => write!(f, "{v}"),
            Self::DomainValue { domain, id } => write!(f, "{domain}_{id}"),
            Self::ExtendedDomain { original, info } => write!(
                f,
                "{} where {{\n\t{}\n\t}}",
                original,
                info.iter()
                    .map(|(fun, value)| format!(
                        "{} = {}",
                        fun.name,
                        value.to_string().replace('\n', "\n\t")
                    ))
                    .collect::<Vec<_>>()
                    .join(";\n\t")
            ),
            Self::Predicate { name, args, perm } => write!(
                f,
                "acc({name}({})), {}",
                args.iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", "),
                perm.as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_else(|| "?".into())
            ),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtractedModel {
    pub entries: Vec<(String, ExtractedModelEntry)>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeapEntry {
    Predicate {
        name: String,
        args: Vec<ExtractedModelEntry>,
        perm: Option<Rational>,
    },
    Field {
        receiver: ExtractedModelEntry,
        field: String,
        perm: Option<Rational>,
        sort: Sort,
        entry: ExtractedModelEntry,
    },
    FieldValueFunction {
        fvf: ExtractedModelEntry,
        field: String,
        values: (
            Vec<(ExtractedModelEntry, ExtractedModelEntry)>,
            ExtractedModelEntry,
        ),
        perms: (
            Vec<(ExtractedModelEntry, Option<Rational>)>,
            Option<Rational>,
        ),
        sort: Sort,
    },
    Unresolved {
        chunk: Chunk,
        reason: String,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtractedHeap {
    pub entries: Vec<HeapEntry>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainEntry {
    pub name: String,
    pub types: Vec<Type>,
    pub functions: Vec<ExtractedFunction>,
}
impl DomainEntry {
    pub fn value_name(
        &self,
    ) -> Result<String, ferrum_silver::ast::pretty::pretty_printer::PrintError> {
        let types = self
            .types
            .iter()
            .map(ferrum_silver::ast::pretty::pretty_printer::show_type)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if types.is_empty() {
            self.name.clone()
        } else {
            format!("{}[{}]", self.name, types.join(", "))
        })
    }
}
#[derive(Clone, Debug)]
pub struct ExtractedFunction {
    pub name: String,
    pub argument_types: Vec<Sort>,
    pub return_type: Sort,
    pub options: Vec<(Vec<ExtractedModelEntry>, ExtractedModelEntry)>,
    pub default: ExtractedModelEntry,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionApplication {
    Partial(ExtractedFunction),
    Value(ExtractedModelEntry),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionError {
    TooManyArguments,
    WrongTypes,
    UnsupportedTypecheck,
}
impl PartialEq for ExtractedFunction {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.argument_types == other.argument_types
            && self.return_type == other.return_type
            && unordered_map_equal(&self.options, &other.options)
            && self.default == other.default
    }
}
impl Eq for ExtractedFunction {}
impl ExtractedFunction {
    pub fn apply(
        &self,
        args: &[ExtractedModelEntry],
    ) -> Result<FunctionApplication, FunctionError> {
        if args.len() > self.argument_types.len() {
            return Err(FunctionError::TooManyArguments);
        }
        for (arg, sort) in args.iter().zip(&self.argument_types) {
            if !typecheck(arg, sort)? {
                return Err(FunctionError::WrongTypes);
            }
        }
        if args.len() == self.argument_types.len() {
            return Ok(FunctionApplication::Value(
                self.options
                    .iter()
                    .find(|(key, _)| key == args)
                    .map(|(_, value)| value.clone())
                    .unwrap_or_else(|| self.default.clone()),
            ));
        }
        let options = self
            .options
            .iter()
            .filter(|(key, _)| key.starts_with(args))
            .map(|(key, value)| (key[args.len()..].to_vec(), value.clone()))
            .collect();
        Ok(FunctionApplication::Partial(Self {
            name: format!("{}_{}", self.name, self.argument_types.len() - args.len()),
            argument_types: self.argument_types[args.len()..].to_vec(),
            return_type: self.return_type.clone(),
            options,
            default: self.default.clone(),
        }))
    }
    pub fn image(&self) -> Vec<ExtractedModelEntry> {
        self.options
            .iter()
            .map(|(_, v)| v.clone())
            .chain(std::iter::once(self.default.clone()))
            .collect()
    }
}
pub fn typecheck(value: &ExtractedModelEntry, sort: &Sort) -> Result<bool, FunctionError> {
    Ok(match value {
        ExtractedModelEntry::Int(_) => *sort == Sort::Int,
        ExtractedModelEntry::Bool(_) => *sort == Sort::Bool,
        ExtractedModelEntry::Perm(_) => *sort == Sort::Perm,
        ExtractedModelEntry::Ref { .. }
        | ExtractedModelEntry::NullRef(_)
        | ExtractedModelEntry::RecursiveRef(_) => *sort == Sort::Ref,
        ExtractedModelEntry::Var { sort: s, .. } => s == sort,
        ExtractedModelEntry::Other { .. } | ExtractedModelEntry::Unprocessed(_) => false,
        ExtractedModelEntry::Seq { values, .. } => match sort {
            Sort::Seq(_) if values.is_empty() => true,
            Sort::Seq(elem) => typecheck(&values[0], elem)?,
            _ => false,
        },
        ExtractedModelEntry::DomainValue { domain, .. } => sort.to_string() == *domain,
        ExtractedModelEntry::ExtendedDomain { original, .. } => typecheck(original, sort)?,
        ExtractedModelEntry::Set { .. }
        | ExtractedModelEntry::Multiset { .. }
        | ExtractedModelEntry::Predicate { .. } => return Err(FunctionError::UnsupportedTypecheck),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConversionError {
    InvalidInteger(String),
    InvalidPermission(String),
    MissingApplicationArgument,
    ZeroDenominator,
}
fn other(value: impl Into<String>, problem: impl Into<String>) -> ExtractedModelEntry {
    ExtractedModelEntry::Other {
        value: value.into(),
        problem: problem.into(),
    }
}
/// Source scalar conversion, including its approximate decimal-permission rule
/// and its 0/1 boolean special cases. Malformed inputs become typed failures where
/// Scala would throw instead of being treated as a successful model value.
pub fn get_constant_entry(
    sort: &Sort,
    entry: &ModelEntry,
) -> Result<ExtractedModelEntry, ConversionError> {
    use ExtractedModelEntry as E;
    if matches!(entry, ModelEntry::Value(ValueEntry::Unspecified))
        || matches!(entry, ModelEntry::Value(ValueEntry::Constant(s)) if s == "#unspecified")
    {
        return Ok(other("#unspecified", "default case"));
    }
    let value = match entry {
        ModelEntry::Value(v) => Some(v),
        ModelEntry::Map(_) => None,
    };
    let rendered = entry.to_string();
    Ok(match sort {
        Sort::Ref => E::Var {
            name: rendered,
            sort: Sort::Ref,
        },
        Sort::Int => match value {
            Some(ValueEntry::Constant(x)) => E::Int(
                x.parse()
                    .map_err(|_| ConversionError::InvalidInteger(x.clone()))?,
            ),
            Some(ValueEntry::Application { name, arguments }) => {
                let first = arguments
                    .first()
                    .ok_or(ConversionError::MissingApplicationArgument)?;
                match (
                    get_constant_entry(sort, &ModelEntry::Value(first.clone()))?,
                    name.as_str(),
                ) {
                    (E::Int(n), "-") => E::Int(-n),
                    _ => other(rendered, "not an integer literal"),
                }
            }
            _ => other(rendered, "not an integer literal"),
        },
        Sort::Bool => match value {
            Some(ValueEntry::Constant(s)) if s == "true" || s == "1" => E::Bool(true),
            Some(ValueEntry::Constant(s)) if s == "false" || s == "0" => E::Bool(false),
            Some(ValueEntry::Application { arguments, .. }) => get_constant_entry(
                sort,
                &ModelEntry::Value(
                    arguments
                        .first()
                        .ok_or(ConversionError::MissingApplicationArgument)?
                        .clone(),
                ),
            )?,
            _ => other(rendered, "not a boolean literal"),
        },
        Sort::Seq(_) | Sort::Set(_) => E::Var {
            name: rendered,
            sort: sort.clone(),
        },
        Sort::Perm => match value {
            Some(ValueEntry::Constant(s)) => {
                let x: f64 = s
                    .parse()
                    .map_err(|_| ConversionError::InvalidPermission(s.clone()))?;
                let rational = if x == 0.0 {
                    Rational::zero()
                } else if x == 1.0 {
                    Rational::one()
                } else {
                    let integral = x as i32;
                    let decimal = x - f64::from(integral);
                    let denominator = (1.0 / decimal) as i32;
                    if denominator == 0 {
                        return Err(ConversionError::ZeroDenominator);
                    }
                    Rational::new(integral.into(), 1.into())
                        + Rational::new(1.into(), denominator.into())
                };
                E::Perm(rational)
            }
            Some(ValueEntry::Application { name, arguments }) => {
                let first = arguments
                    .first()
                    .ok_or(ConversionError::MissingApplicationArgument)?;
                let left = get_constant_entry(sort, &ModelEntry::Value(first.clone()))?;
                match (name.as_str(), left) {
                    ("-", E::Perm(x)) => E::Perm(-x),
                    ("/", left) => {
                        let right = get_constant_entry(
                            sort,
                            &ModelEntry::Value(
                                arguments
                                    .get(1)
                                    .ok_or(ConversionError::MissingApplicationArgument)?
                                    .clone(),
                            ),
                        )?;
                        match (left, right) {
                            (E::Perm(x), E::Perm(y)) => {
                                if y.numerator() == &BigInt::from(0) {
                                    return Err(ConversionError::ZeroDenominator);
                                }
                                E::Perm(x / y)
                            }
                            _ => other(rendered, "not a permission literal div"),
                        }
                    }
                    _ => other(rendered, "not a permission literal"),
                }
            }
            _ => other(rendered, "not a permission literal"),
        },
        Sort::UserSort(id) => match value {
            Some(ValueEntry::Constant(s)) => E::DomainValue {
                domain: id.to_string(),
                id: s.split('!').next_back().unwrap_or("").into(),
            },
            _ => other(id.to_string(), "not a constant entry---"),
        },
        _ => match value {
            Some(v) => E::Unprocessed(v.clone()),
            None => other(rendered, "MapEntry instead of Constant"),
        },
    })
}
pub fn get_function_value(
    model: &Model,
    name: &str,
    args: &[ValueEntry],
    sort: &Sort,
) -> Result<ExtractedModelEntry, ConversionError> {
    match model.entries.get(name) {
        Some(ModelEntry::Map(map)) => get_constant_entry(
            sort,
            &ModelEntry::Value(map.options.get(args).unwrap_or(&map.default).clone()),
        ),
        Some(entry) => get_constant_entry(sort, entry),
        None => Ok(other(name, "function not found in model")),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvaluationError {
    Conversion(ConversionError),
    Render(String),
    Unsupported(&'static str),
    SmtConversion(String),
}
impl From<ConversionError> for EvaluationError {
    fn from(value: ConversionError) -> Self {
        Self::Conversion(value)
    }
}
/// Evaluate the implemented source term families against a model. A source term
/// renderer is required for variable lookup and diagnostic text.
pub fn evaluate_term(
    term: &crate::state::terms::Term,
    model: &Model,
    env: &std::collections::HashMap<crate::state::terms::Var, ExtractedModelEntry>,
    render: &impl Fn(&crate::state::terms::Term) -> Result<String, String>,
) -> Result<ExtractedModelEntry, EvaluationError> {
    use crate::state::terms::TermKind as T;
    use ExtractedModelEntry as E;
    use num_traits::Zero;
    let evaluate = |t: &crate::state::terms::Term| evaluate_term(t, model, env, render);
    let text = || render(term).map_err(EvaluationError::Render);
    let not_evaluable =
        || -> Result<ExtractedModelEntry, EvaluationError> { Ok(other(text()?, "not evaluable")) };
    let function = |name: &str, args: Vec<ValueEntry>, sort: &Sort| {
        get_function_value(model, name, &args, sort).map_err(EvaluationError::from)
    };
    Ok(match term.kind() {
        T::Unit => E::Unprocessed(ValueEntry::Constant("$Snap.unit".into())),
        T::IntLiteral(n) => E::Int(n.clone()),
        T::True => E::Bool(true),
        T::False => E::Bool(false),
        T::Null => E::Var {
            name: model
                .entries
                .get("$Ref.null")
                .map(ToString::to_string)
                .unwrap_or_else(|| "$Ref.null".into()),
            sort: Sort::Ref,
        },
        T::Var(v) => {
            if let Some(value) = env.get(v) {
                value.clone()
            } else {
                let name = text()?;
                match model.entries.get(&name) {
                    Some(entry) => get_constant_entry(&v.sort, entry)?,
                    None => other(name, "variable not found in model"),
                }
            }
        }
        T::App { applicable, args } => {
            let id = applicable.id().to_string();
            let limited = format!("{id}%limited");
            let name = if model.entries.contains_key(&limited) {
                limited
            } else if model.entries.contains_key(&id) {
                id
            } else {
                id.replace('[', "<").replace(']', ">")
            };
            let mut values = Vec::with_capacity(args.len());
            for arg in args {
                let value = evaluate(arg)?;
                values.push(match value {
                    E::Unprocessed(v) => v,
                    _ => ValueEntry::Constant(value.to_string()),
                });
            }
            function(&name, values, applicable.result_sort())?
        }
        T::Combine(a, b) => E::Unprocessed(ValueEntry::Application {
            name: "$Snap.combine".into(),
            arguments: vec![evaluate(a)?.as_value_entry(), evaluate(b)?.as_value_entry()],
        }),
        T::First(t) | T::Second(t) => {
            let value = evaluate(t)?;
            match value {
                E::Unprocessed(ValueEntry::Application { name, arguments })
                    if name == "$Snap.combine" =>
                {
                    E::Unprocessed(
                        arguments
                            .get(if matches!(term.kind(), T::First(_)) {
                                0
                            } else {
                                1
                            })
                            .ok_or(EvaluationError::Conversion(
                                ConversionError::MissingApplicationArgument,
                            ))?
                            .clone(),
                    )
                }
                E::Unprocessed(ValueEntry::Application { .. }) => {
                    let original = render(t).map_err(EvaluationError::Render)?;
                    if matches!(term.kind(), T::First(_)) {
                        other(format!("First({original})"), "unapplicable")
                    } else {
                        other(format!("Second({original}}})"), "unapplicable")
                    }
                }
                E::Other { value, problem: _ } if matches!(term.kind(), T::First(_)) => {
                    other(format!("First({value})"), "unapplicable")
                }
                E::Other { value, problem } => {
                    other(format!("Second({value}){problem}"), "unapplicable")
                }
                other_value => other(
                    format!(
                        "{}({})",
                        if matches!(term.kind(), T::First(_)) {
                            "First"
                        } else {
                            "Second"
                        },
                        other_value
                    ),
                    "unapplicable",
                ),
            }
        }
        T::SeqLength(s) => function(
            "Seq_length",
            vec![evaluate(s)?.as_value_entry()],
            &Sort::Int,
        )?,
        T::SetIn(element, set) => function(
            "Set_in",
            vec![
                evaluate(element)?.as_value_entry(),
                evaluate(set)?.as_value_entry(),
            ],
            &Sort::Bool,
        )?,
        T::MultisetCount(set, element) => function(
            "Multiset_count",
            vec![
                evaluate(set)?.as_value_entry(),
                evaluate(element)?.as_value_entry(),
            ],
            &Sort::Int,
        )?,
        T::MapDomain(map) => function(
            "Map_domain",
            vec![evaluate(map)?.as_value_entry()],
            term.sort(),
        )?,
        T::MapLookup(map, key) => function(
            "Map_apply",
            vec![
                evaluate(map)?.as_value_entry(),
                evaluate(key)?.as_value_entry(),
            ],
            term.sort(),
        )?,
        T::MapCardinality(map) => function(
            "Map_card",
            vec![evaluate(map)?.as_value_entry()],
            &Sort::Int,
        )?,
        T::Ite(condition, yes, no) => match evaluate(condition)? {
            E::Bool(true) => evaluate(yes)?,
            E::Bool(false) => evaluate(no)?,
            _ => other(text()?, "condition not evaluable"),
        },
        T::Not(t) => match evaluate(t)? {
            E::Bool(b) => E::Bool(!b),
            _ => not_evaluable()?,
        },
        T::And(ts) | T::Or(ts) => {
            let values = ts.iter().map(evaluate).collect::<Result<Vec<_>, _>>()?;
            let is_and = matches!(term.kind(), T::And(_));
            if values
                .iter()
                .any(|v| matches!(v,E::Bool(b) if *b != is_and))
            {
                E::Bool(!is_and)
            } else if values
                .iter()
                .all(|v| matches!(v,E::Bool(b) if *b == is_and))
            {
                E::Bool(is_and)
            } else {
                not_evaluable()?
            }
        }
        T::BuiltinEquals(a, b) => {
            let a = evaluate(a)?;
            let b = evaluate(b)?;
            if matches!(a, E::Other { .. }) || matches!(b, E::Other { .. }) {
                not_evaluable()?
            } else {
                E::Bool(a.to_string() == b.to_string())
            }
        }
        T::AtMost(a, b) | T::AtLeast(a, b) | T::Less(a, b) | T::Greater(a, b) => {
            match (evaluate(a)?, evaluate(b)?) {
                (E::Int(a), E::Int(b)) => E::Bool(match term.kind() {
                    T::AtMost(..) => a <= b,
                    T::AtLeast(..) => a >= b,
                    T::Less(..) => a < b,
                    _ => a > b,
                }),
                _ => other(
                    format!(
                        "comparison of {} and {}",
                        render(a).map_err(EvaluationError::Render)?,
                        render(b).map_err(EvaluationError::Render)?
                    ),
                    "not evaluable",
                ),
            }
        }
        T::NoPerm => E::Perm(Rational::zero()),
        T::FullPerm => E::Perm(Rational::one()),
        T::FractionPermLiteral(r) => E::Perm(r.clone()),
        T::FractionPerm(a, b) => match (evaluate(a)?, evaluate(b)?) {
            (E::Int(n), E::Int(d)) if !d.is_zero() => E::Perm(Rational::new(n, d)),
            _ => not_evaluable()?,
        },
        T::PermPlus(a, b) | T::PermMinus(a, b) | T::PermTimes(a, b) | T::PermMin(a, b) => {
            match (evaluate(a)?, evaluate(b)?) {
                (E::Perm(a), E::Perm(b)) => E::Perm(match term.kind() {
                    T::PermPlus(..) => a + b,
                    T::PermMinus(..) => a - b,
                    T::PermTimes(..) => a * b,
                    _ => {
                        if a < b {
                            a
                        } else {
                            b
                        }
                    }
                }),
                _ => other(
                    format!(
                        "permission arithmetic on {} and {}",
                        render(a).map_err(EvaluationError::Render)?,
                        render(b).map_err(EvaluationError::Render)?
                    ),
                    "not evaluable",
                ),
            }
        }
        T::Plus(a, b) | T::Minus(a, b) | T::Times(a, b) | T::Div(a, b) | T::Mod(a, b) => {
            match (evaluate(a)?, evaluate(b)?) {
                (E::Int(_), E::Int(y))
                    if matches!(term.kind(), T::Div(..) | T::Mod(..)) && y.is_zero() =>
                {
                    other(
                        format!(
                            "division of {} by zero",
                            render(a).map_err(EvaluationError::Render)?
                        ),
                        "not evaluable",
                    )
                }
                (E::Int(x), E::Int(y)) => {
                    let result = match term.kind() {
                        T::Plus(..) => x + y,
                        T::Minus(..) => x - y,
                        T::Times(..) => x * y,
                        T::Div(..) | T::Mod(..) => {
                            use num_traits::Signed;
                            let rem = &x % &y;
                            let rem = if rem < 0.into() { rem + y.abs() } else { rem };
                            if matches!(term.kind(), T::Div(..)) {
                                (x - rem) / y
                            } else {
                                rem
                            }
                        }
                        _ => unreachable!(),
                    };
                    E::Int(result)
                }
                _ => {
                    let label = if matches!(term.kind(), T::Div(..) | T::Mod(..)) {
                        "division of"
                    } else {
                        "integer arithmetic on"
                    };
                    let sep = if matches!(term.kind(), T::Div(..) | T::Mod(..)) {
                        "by"
                    } else {
                        "and"
                    };
                    other(
                        format!(
                            "{label} {} {sep} {}",
                            render(a).map_err(EvaluationError::Render)?,
                            render(b).map_err(EvaluationError::Render)?
                        ),
                        "not evaluable",
                    )
                }
            }
        }
        T::SortWrapper(inner, to) => {
            let value = evaluate(inner)?;
            match value {
                E::Unprocessed(entry) => {
                    use crate::state::terms::{TermFactory, TermOptions};
                    let factory = TermFactory::new(TermOptions {
                        use_flyweight: term.uses_flyweight(),
                        use_old_axiomatization: false,
                        mask_heap_mode: false,
                    });
                    let mut converter =
                        crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(
                            factory,
                        );
                    let from = converter
                        .convert_sort(inner.sort())
                        .map_err(|e| EvaluationError::SmtConversion(e.to_string()))?;
                    let target = converter
                        .convert_sort(to)
                        .map_err(|e| EvaluationError::SmtConversion(e.to_string()))?;
                    function(&format!("$SortWrappers.{from}To{target}"), vec![entry], to)?
                }
                E::Other { value, .. } => other(format!("SortWrapper({value})"), "unapplicable"),
                _ => other(
                    format!(
                        "SortWrapper({})",
                        render(inner).map_err(EvaluationError::Render)?
                    ),
                    "unapplicable",
                ),
            }
        }
        T::Lookup(field, fvf, at) => {
            let sort = match fvf.sort() {
                Sort::FieldValueFunction { codomain, .. } => codomain.as_ref(),
                _ => &Sort::Snap,
            };
            function(
                &format!("$FVF.lookup_{field}"),
                vec![
                    evaluate(fvf)?.as_value_entry(),
                    evaluate(at)?.as_value_entry(),
                ],
                sort,
            )?
        }
        T::PredicateLookup(name, psf, args) => {
            use crate::state::terms::{TermFactory, TermOptions};
            let factory = TermFactory::new(TermOptions {
                use_flyweight: term.uses_flyweight(),
                use_old_axiomatization: false,
                mask_heap_mode: false,
            });
            let snap = factory.to_snap_tree(args.clone());
            function(
                &format!("$PSF.lookup_{name}"),
                vec![
                    evaluate(psf)?.as_value_entry(),
                    evaluate(&snap)?.as_value_entry(),
                ],
                &Sort::Snap,
            )?
        }
        _ => other(text()?, "unhandled"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::{TermFactory, TermOptions};
    #[test]
    fn term_evaluation_uses_euclidean_division() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let model = Model {
            entries: Default::default(),
        };
        let env = Default::default();
        let div = f.div(f.int_literal(-7), f.int_literal(3));
        let rem = f.modulo(f.int_literal(-7), f.int_literal(3));
        let render = |_: &crate::state::terms::Term| Ok(String::new());
        assert_eq!(
            evaluate_term(&div, &model, &env, &render).unwrap(),
            ExtractedModelEntry::Int((-3).into())
        );
        assert_eq!(
            evaluate_term(&rem, &model, &env, &render).unwrap(),
            ExtractedModelEntry::Int(2.into())
        );
    }
    #[test]
    fn partial_function_application_filters_options_and_checks_types() {
        let one = ExtractedModelEntry::Int(1.into());
        let two = ExtractedModelEntry::Int(2.into());
        let function = ExtractedFunction {
            name: "f".into(),
            argument_types: vec![Sort::Int, Sort::Bool],
            return_type: Sort::Int,
            options: vec![(
                vec![one.clone(), ExtractedModelEntry::Bool(true)],
                two.clone(),
            )],
            default: one.clone(),
        };
        let FunctionApplication::Partial(partial) =
            function.apply(std::slice::from_ref(&one)).unwrap()
        else {
            panic!("partial")
        };
        assert_eq!(partial.name, "f_1");
        assert_eq!(
            partial.apply(&[ExtractedModelEntry::Bool(true)]).unwrap(),
            FunctionApplication::Value(two)
        );
        assert_eq!(partial.apply(&[one]), Err(FunctionError::WrongTypes));
    }
}

/// Source legacy permission extractor: it intentionally does not evaluate
/// applications, fractional terms, comparisons or minima here.
pub fn eval_permission(
    term: &crate::state::terms::Term,
    model: &Model,
    render: &impl Fn(&crate::state::terms::Term) -> Result<String, String>,
) -> Result<Option<Rational>, EvaluationError> {
    use crate::state::terms::TermKind as T;
    Ok(match term.kind() {
        T::Var(_) => match evaluate_term(term, model, &Default::default(), render)? {
            ExtractedModelEntry::Perm(v) => Some(v),
            _ => None,
        },
        T::NoPerm => Some(Rational::zero()),
        T::FullPerm => Some(Rational::one()),
        T::FractionPermLiteral(v) => Some(v.clone()),
        T::PermTimes(a, b)
        | T::IntPermTimes(a, b)
        | T::PermIntDiv(a, b)
        | T::PermPlus(a, b)
        | T::PermMinus(a, b) => {
            match (
                eval_permission(a, model, render)?,
                eval_permission(b, model, render)?,
            ) {
                (Some(a), Some(b)) => Some(match term.kind() {
                    T::PermTimes(..) | T::IntPermTimes(..) => a * b,
                    T::PermIntDiv(..) => {
                        if b.numerator() == &BigInt::from(0) {
                            return Err(ConversionError::ZeroDenominator.into());
                        }
                        a / b
                    }
                    T::PermPlus(..) => a + b,
                    _ => a - b,
                }),
                _ => None,
            }
        }
        _ => None,
    })
}
/// Extract the legacy mapped heap. The source skips quantified predicate chunks
/// and swallows failed quantified-field probes; remaining unsupported chunks are
/// retained as explicit Unresolved entries with their original chunk.
pub fn extract_heap(
    chunks: &[Chunk],
    model: &Model,
    render: &impl Fn(&crate::state::terms::Term) -> Result<String, String>,
) -> Result<ExtractedHeap, EvaluationError> {
    use crate::resources::resources::BaseId;
    use crate::state::terms::TermKind;
    let mut entries = Vec::new();
    for chunk in chunks {
        match chunk {
            Chunk::Basic(c) if c.resource_id == BaseId::Field => {
                let receiver = c.args.first().ok_or(EvaluationError::Conversion(
                    ConversionError::MissingApplicationArgument,
                ))?;
                let receiver = evaluate_term(receiver, model, &Default::default(), render)?;
                let perm = match c.perm.kind() {
                    TermKind::NoPerm => Some(Rational::zero()),
                    TermKind::FullPerm => Some(Rational::one()),
                    TermKind::FractionPermLiteral(v) => Some(v.clone()),
                    _ => None,
                };
                let entry = evaluate_term(&c.snap, model, &Default::default(), render)?;
                if matches!(receiver, ExtractedModelEntry::Var { .. }) {
                    entries.push(HeapEntry::Field {
                        receiver,
                        field: c.id.0.clone(),
                        perm,
                        sort: c.snap.sort().clone(),
                        entry,
                    });
                } else {
                    entries.push(HeapEntry::Unresolved {
                        chunk: chunk.clone(),
                        reason: "the receiver term is not a variable (unexpected)".into(),
                    });
                }
            }
            Chunk::Basic(c) if c.resource_id == BaseId::Predicate => {
                let args = c
                    .args
                    .iter()
                    .map(|v| evaluate_term(v, model, &Default::default(), render))
                    .collect::<Result<Vec<_>, _>>()?;
                entries.push(HeapEntry::Predicate {
                    name: c.id.to_string(),
                    args,
                    perm: eval_permission(&c.perm, model, render)?,
                });
            }
            Chunk::QuantifiedField(c) => {
                let probe = || -> Result<Vec<HeapEntry>, EvaluationError> {
                    let singleton = c
                        .singleton_rcvr
                        .as_ref()
                        .ok_or(EvaluationError::Unsupported("quantified field receiver"))?;
                    let recv_sort = singleton.sort().clone();
                    let value_sort = match c.fvf.sort() {
                        Sort::FieldValueFunction { codomain, .. } => codomain.as_ref().clone(),
                        _ => return Err(EvaluationError::Unsupported("field value function sort")),
                    };
                    let fvf = evaluate_term(&c.fvf, model, &Default::default(), render)?;
                    let recv0 = ExtractedModelEntry::Var {
                        name: "$Ref!val!0".into(),
                        sort: Sort::Ref,
                    };
                    let permission = get_function_value(
                        model,
                        &format!("$FVF.perm_{}", c.id.0),
                        &[fvf.as_value_entry(), recv0.as_value_entry()],
                        &Sort::Perm,
                    )?;
                    let ExtractedModelEntry::Perm(permission) = permission else {
                        return Err(EvaluationError::Unsupported("quantified field permission"));
                    };
                    let mut result = Vec::new();
                    for i in 0..=10 {
                        let receiver = ExtractedModelEntry::Var {
                            name: format!("$Ref!val!{i}"),
                            sort: recv_sort.clone(),
                        };
                        let entry = get_function_value(
                            model,
                            &format!("$FVF.lookup_{}", c.id.0),
                            &[fvf.as_value_entry(), receiver.as_value_entry()],
                            &value_sort,
                        )?;
                        result.push(HeapEntry::Field {
                            receiver,
                            field: c.id.0.clone(),
                            perm: Some(permission.clone()),
                            sort: value_sort.clone(),
                            entry,
                        });
                    }
                    Ok(result)
                };
                if let Ok(probed) = probe() {
                    entries.extend(probed);
                }
            }
            Chunk::QuantifiedPredicate(_) => {}
            _ => entries.push(HeapEntry::Unresolved {
                chunk: chunk.clone(),
                reason: "Non-basic chunks not supported".into(),
            }),
        }
    }
    Ok(ExtractedHeap { entries })
}

fn scala_int(value: &BigInt) -> i32 {
    use num_traits::Signed;
    let bytes = value.to_signed_bytes_le();
    let mut result = if value.is_negative() {
        [0xff; 4]
    } else {
        [0; 4]
    };
    for (i, b) in bytes.iter().take(4).enumerate() {
        result[i] = *b;
    }
    i32::from_le_bytes(result)
}
fn synthetic_entry(sort: &Sort, index: i32) -> ExtractedModelEntry {
    match sort {
        Sort::Bool => ExtractedModelEntry::Bool(index % 2 == 0),
        Sort::Int => ExtractedModelEntry::Int(index.into()),
        Sort::UserSort(id) => ExtractedModelEntry::DomainValue {
            domain: id.to_string(),
            id: index.to_string(),
        },
        _ => ExtractedModelEntry::Var {
            name: format!(
                "{}!val!{}",
                sort.id().to_string().replace('[', "<").replace(']', ">"),
                index
            ),
            sort: sort.clone(),
        },
    }
}
/// Recursive source mapLocalVar: references follow extracted fields; sequences
/// use Seq_length/Seq_index; sets use the source's cardinality-based synthetic
/// entries. Cycles return RecursiveRef, not an empty successful object.
pub fn map_local_var(
    sort: Option<&Sort>,
    value: &ExtractedModelEntry,
    heap: &ExtractedHeap,
    model: &Model,
    encountered: &std::collections::HashSet<String>,
    null_ref_name: &str,
) -> Result<ExtractedModelEntry, EvaluationError> {
    use ExtractedModelEntry as E;
    let name = value.to_string();
    Ok(match sort {
        Some(Sort::Ref) => {
            if name == null_ref_name {
                E::NullRef(name)
            } else if encountered.contains(&name) {
                E::RecursiveRef(name)
            } else {
                let mut next = encountered.clone();
                next.insert(name.clone());
                let mut fields = Vec::<(String, (E, Option<Rational>))>::new();
                for entry in &heap.entries {
                    let found = match entry {
                        HeapEntry::Field {
                            receiver,
                            field,
                            perm,
                            sort,
                            entry,
                        } if value == receiver => Some((
                            field,
                            map_local_var(Some(sort), entry, heap, model, &next, null_ref_name)?,
                            perm.clone(),
                        )),
                        HeapEntry::FieldValueFunction {
                            field,
                            values,
                            perms,
                            sort,
                            ..
                        } => {
                            if !matches!(value, E::Var { .. }) {
                                return Err(EvaluationError::Unsupported(
                                    "field-value-function receiver is not a variable",
                                ));
                            }
                            let source = values
                                .0
                                .iter()
                                .find(|(key, _)| key == value)
                                .map(|(_, value)| value)
                                .unwrap_or(&values.1);
                            let permission = perms
                                .0
                                .iter()
                                .find(|(key, _)| key == value)
                                .map(|(_, value)| value.clone())
                                .unwrap_or_else(|| perms.1.clone());
                            Some((
                                field,
                                map_local_var(
                                    Some(sort),
                                    source,
                                    heap,
                                    model,
                                    &next,
                                    null_ref_name,
                                )?,
                                permission,
                            ))
                        }
                        _ => None,
                    };
                    if let Some((field, entry, perm)) = found {
                        if let Some((_, old)) = fields.iter_mut().find(|(name, _)| name == field) {
                            *old = (entry, perm);
                        } else {
                            fields.push((field.clone(), (entry, perm)));
                        }
                    }
                }
                E::Ref { name, fields }
            }
        }
        Some(Sort::Seq(element)) => {
            if encountered.contains(&name) {
                E::RecursiveRef(name)
            } else {
                let length = get_function_value(
                    model,
                    "Seq_length",
                    &[ValueEntry::Constant(name.clone())],
                    &Sort::Int,
                );
                match length {
                    Ok(E::Int(length)) => {
                        let mut next = encountered.clone();
                        next.insert(name.clone());
                        let length = scala_int(&length);
                        let mut values = Vec::new();
                        for index in 0..length.max(0) {
                            let item = get_function_value(
                                model,
                                "Seq_index",
                                &[
                                    ValueEntry::Constant(name.clone()),
                                    ValueEntry::Constant(index.to_string()),
                                ],
                                element,
                            )?;
                            values.push(map_local_var(
                                Some(element),
                                &item,
                                heap,
                                model,
                                &next,
                                null_ref_name,
                            )?);
                        }
                        E::Seq { name, values }
                    }
                    _ => other("unresolvable-length Sequence (unexpected)", ""),
                }
            }
        }
        Some(Sort::Set(element)) => {
            let count = match get_function_value(
                model,
                "Set_card",
                &[ValueEntry::Constant(name.clone())],
                &Sort::Int,
            ) {
                Ok(E::Int(n)) => scala_int(&n),
                _ => 0,
            };
            let mut values = Vec::new();
            for index in 0..count.max(0) {
                let entry = synthetic_entry(element, index);
                if !values.contains(&entry) {
                    values.push(entry);
                }
            }
            E::Set { name, values }
        }
        _ => value.clone(),
    })
}
/// Source store mapping; versioned locals are a source MatchError and remain an
/// explicit error rather than being silently renamed.
pub fn map_heap_to_store(
    store: &crate::state::store::MapBackedStore,
    heap: &ExtractedHeap,
    model: &Model,
    converter: &crate::state::symbol_converter::DefaultSymbolConverter,
    render: &impl Fn(&crate::state::terms::Term) -> Result<String, String>,
) -> Result<ExtractedModel, EvaluationError> {
    use ferrum_silver::ast::expression::ExpKind;
    let null_name = model
        .entries
        .get("$Ref.null")
        .map(ToString::to_string)
        .unwrap_or_else(|| "Ref!val!0".into());
    let mut entries: Vec<(String, ExtractedModelEntry)> = Vec::new();
    for (variable, term) in store.term_values() {
        let (name, typ) = match variable.expression().kind() {
            ExpKind::LocalVar(v) => (v.name.clone(), &v.typ),
            ExpKind::Result(t) => ("Result()".into(), t),
            ExpKind::LocalVarWithVersion(..) => {
                return Err(EvaluationError::Unsupported(
                    "versioned variable in mapped counterexample",
                ));
            }
            _ => return Err(EvaluationError::Unsupported("invalid store variable")),
        };
        let sort = converter.to_sort(typ).ok();
        let value = evaluate_term(term, model, &Default::default(), render)?;
        let entry = map_local_var(
            sort.as_ref(),
            &value,
            heap,
            model,
            &Default::default(),
            &null_name,
        )?;
        if let Some((_, old)) = entries.iter_mut().find(|(key, _)| key == &name) {
            *old = entry;
        } else {
            entries.push((name, entry));
        }
    }
    Ok(ExtractedModel { entries })
}
