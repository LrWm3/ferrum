//! Silicon raw and resolved counterexample reconstruction.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/SiliconResolvedCounterexample.scala
//! Status: partial; basic variables, sequence/set/multiset/map reconstruction,
//! resolved heap and store/name translation, and assembly from extracted raw data
//! are implemented, including quantified raw heap candidates and permissions.
//! Domain/function extraction and complete automatic model assembly remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use crate::state::{
    store::{MapBackedStore, Store},
    terms::Term,
};
use ferrum_silver::{
    ast::{
        expression::{Exp, ExpKind},
        r#type::Type,
    },
    verifier::{
        counterexample::{
            self, BasicDomainEntry, BasicFunctionEntry, CeCollection, CeVariable, FunctionOptions,
            StoreCounterexample, StoreEntry,
        },
        verification_error::{Model, ModelEntry, ValueEntry},
    },
};
use std::collections::HashMap;

pub fn ast_type_from_string(value: &str) -> Option<Type> {
    match value {
        "Int" => Some(Type::Int),
        "Bool" => Some(Type::Bool),
        "Perm" => Some(Type::Perm),
        "Ref" => Some(Type::Ref),
        _ => None,
    }
}
/// Split only the first top-level ~_ separator; nested angle and square brackets
/// count toward the same depth, as in the source parser.
pub fn map_types_from_string(inner: &str) -> (Option<Type>, Option<Type>) {
    let mut depth = 0_i32;
    let mut chars = inner.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '<' | '[' => depth += 1,
            '>' | ']' => depth -= 1,
            '~' if depth == 0 && chars.peek().is_some_and(|(_, c)| *c == '_') => {
                return (
                    ast_type_from_string(&inner[..i]),
                    ast_type_from_string(&inner[i + 2..]),
                );
            }
            _ => {}
        }
    }
    (None, None)
}
fn variable_name(expression: &Exp) -> &str {
    match expression.kind() {
        ExpKind::LocalVar(v) => &v.name,
        ExpKind::LocalVarWithVersion(name, _) => name,
        ExpKind::Result(_) => "result",
        _ => unreachable!("store key is an AbstractLocalVar"),
    }
}
/// Preserve source prepend order and its deliberate omission of model maps.
pub fn basic_variables<E>(
    model: &Model,
    store: &MapBackedStore,
    render_term: &impl Fn(&Term) -> Result<String, E>,
) -> Result<Vec<CeVariable>, E> {
    let mut result = Vec::new();
    for (key, (value, _)) in store.values() {
        let value = render_term(value)?;
        let typ = match key.expression().kind() {
            ExpKind::LocalVar(local) => Some(local.typ.clone()),
            _ => None,
        };
        if value.contains('@') {
            match model.entries.get(&value) {
                Some(ModelEntry::Value(
                    entry @ (ValueEntry::Constant(_)
                    | ValueEntry::Application { .. }
                    | ValueEntry::Unspecified),
                )) => result.insert(
                    0,
                    CeVariable {
                        name: variable_name(key.expression()).into(),
                        value: counterexample::literal(&entry.to_string(), typ.as_ref()),
                        typ,
                    },
                ),
                _ => {}
            }
        } else {
            result.insert(
                0,
                CeVariable {
                    name: variable_name(key.expression()).into(),
                    value: counterexample::literal(&value, typ.as_ref()),
                    typ,
                },
            );
        }
    }
    if let Some(ModelEntry::Value(value @ (ValueEntry::Constant(_) | ValueEntry::Unspecified))) =
        model.entries.get("$Ref.null")
    {
        result.insert(
            0,
            CeVariable {
                name: "null".into(),
                value: counterexample::literal(&value.to_string(), Some(&Type::Ref)),
                typ: Some(Type::Ref),
            },
        );
    }
    Ok(result)
}
fn expression_string(
    exp: &Exp,
) -> Result<String, ferrum_silver::ast::pretty::pretty_printer::PrintError> {
    let rendered = ferrum_silver::ast::pretty::pretty_printer::pretty_expression(exp)?;
    let mut out = String::new();
    let mut lines = rendered.split('\n');
    if let Some(first) = lines.next() {
        out.push_str(first)
    }
    for line in lines {
        out.push(' ');
        out.push_str(line.trim_start());
    }
    Ok(out)
}
#[derive(Debug)]
pub enum ResolutionError {
    Printer(ferrum_silver::ast::pretty::pretty_printer::PrintError),
    InvalidVariable,
    Type(ferrum_silver::ast::expression::ExpressionTypeError),
}
pub type ReferenceOccurrences = HashMap<String, (String, usize)>;
pub fn det_store(
    store: &MapBackedStore,
    variables: &[CeVariable],
    collections: &[CeCollection],
) -> Result<(StoreCounterexample, ReferenceOccurrences), ResolutionError> {
    let mut occurrences = HashMap::<String, (String, usize)>::new();
    let mut result = Vec::new();
    for (key, _) in store.values() {
        let name = variable_name(key.expression());
        let typ = key.expression().typ().map_err(ResolutionError::Type)?;
        for var in variables.iter().filter(|v| v.name == name) {
            let value = expression_string(&var.value).map_err(ResolutionError::Printer)?;
            if typ == Type::Ref {
                if let Some((previous, count)) = occurrences.get_mut(&value) {
                    if previous != name {
                        *previous = name.into();
                        *count += 1;
                    }
                } else {
                    occurrences.insert(value.clone(), (name.into(), 1));
                }
            }
            let mut found = false;
            for coll in collections.iter().filter(|c| c.id == value) {
                result.insert(
                    0,
                    StoreEntry::new(key.expression().clone(), coll.value.clone())
                        .map_err(|_| ResolutionError::InvalidVariable)?,
                );
                found = true;
            }
            if !found {
                result.insert(
                    0,
                    StoreEntry::new(key.expression().clone(), var.value.clone())
                        .map_err(|_| ResolutionError::InvalidVariable)?,
                );
            }
        }
    }
    Ok((
        StoreCounterexample {
            store_entries: result,
        },
        occurrences,
    ))
}
pub fn translation_map(
    variables: &[CeVariable],
    collections: &[CeCollection],
    occurrences: &ReferenceOccurrences,
) -> Result<HashMap<String, String>, ResolutionError> {
    let mut result = HashMap::new();
    for var in variables {
        let value = expression_string(&var.value).map_err(ResolutionError::Printer)?;
        if let Some(coll) = collections.iter().find(|c| c.id == value) {
            let suffix = match &var.typ {
                Some(Type::Seq(_)) => " (Seq)",
                Some(Type::Set(_)) => " (Set)",
                Some(Type::Multiset(_)) => " (MultiSet)",
                _ => "",
            };
            result.insert(coll.id.clone(), format!("{}{suffix}", var.name));
        }
    }
    for (key, (name, count)) in occurrences {
        if *count == 1 {
            result.insert(key.clone(), name.clone());
        }
    }
    Ok(result)
}
pub fn translated_functions(
    functions: &[BasicFunctionEntry],
    names: &HashMap<String, String>,
) -> Vec<BasicFunctionEntry> {
    let translate = |s: &String| names.get(s).cloned().unwrap_or_else(|| s.clone());
    functions
        .iter()
        .map(|f| BasicFunctionEntry {
            name: f.name.clone(),
            argument_types: f.argument_types.clone(),
            return_type: f.return_type.clone(),
            options: FunctionOptions::new(
                f.options
                    .entries()
                    .iter()
                    .map(|(args, value)| (args.iter().map(&translate).collect(), translate(value))),
            ),
            default: translate(&f.default),
        })
        .collect()
}
pub fn translated_domains(
    domains: &[BasicDomainEntry],
    names: &HashMap<String, String>,
) -> Vec<BasicDomainEntry> {
    domains
        .iter()
        .map(|d| BasicDomainEntry {
            name: d.name.clone(),
            types: d.types.clone(),
            functions: translated_functions(&d.functions, names),
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectionError {
    MissingArgument(&'static str),
    InvalidInteger(String),
    InvalidBoolean(String),
    InvalidIndex(i32),
    NegativeLength(i32),
    NoProgress(&'static str),
}
fn model_options<'a>(
    model: &'a Model,
    name: &str,
) -> Option<&'a ferrum_silver::verifier::verification_error::MapEntry> {
    match model.entries.get(name) {
        Some(ModelEntry::Map(map)) => Some(map),
        _ => None,
    }
}
fn argument<'a>(
    args: &'a [String],
    i: usize,
    op: &'static str,
) -> Result<&'a str, CollectionError> {
    args.get(i)
        .map(String::as_str)
        .ok_or(CollectionError::MissingArgument(op))
}
fn number(s: &str) -> Result<i32, CollectionError> {
    s.parse()
        .map_err(|_| CollectionError::InvalidInteger(s.into()))
}
fn sort_parameter(id: &str) -> &str {
    match (id.find('<'), id.rfind('>')) {
        (Some(start), Some(end)) if start < end => &id[start + 1..end],
        _ => id,
    }
}
/// Source sequence seeding and fixpoint over append/take/drop/index/update.
/// Model maps have no guaranteed cross-runtime iteration order; malformed model
/// entries return the same failure boundary where Scala throws.
pub fn det_sequences(model: &Model) -> Result<Vec<CeCollection>, CollectionError> {
    let mut sequences = HashMap::<String, Vec<String>>::new();
    let mut ops = Vec::<(String, Vec<String>, String)>::new();
    for (name, entry) in &model.entries {
        let ModelEntry::Map(map) = entry else {
            continue;
        };
        for (key, value) in &map.options {
            let args = key.iter().map(ToString::to_string).collect::<Vec<_>>();
            let result = value.to_string();
            match name.as_str() {
                "Seq_length" => {
                    let len = number(&result)?;
                    sequences.insert(
                        argument(&args, 0, "Seq_length")?.into(),
                        vec!["#undefined".into(); len.max(0) as usize],
                    );
                }
                "Seq_empty" => {
                    sequences.insert(result, vec![]);
                }
                "Seq_singleton" => {
                    sequences.insert(result, vec![argument(&args, 0, "Seq_singleton")?.into()]);
                }
                "Seq_range" => {
                    argument(&args, 0, "Seq_range")?;
                    argument(&args, 1, "Seq_range")?;
                    if !matches!(key.first(), Some(ValueEntry::Constant(_)))
                        || !matches!(key.get(1), Some(ValueEntry::Constant(_)))
                    {
                        continue;
                    }
                    let start = number(argument(&args, 0, "Seq_range")?)?;
                    let end = number(argument(&args, 1, "Seq_range")?)?;
                    sequences.insert(result, (start..end).map(|v| v.to_string()).collect());
                }
                _ if name.starts_with("Seq_") => ops.push((name.clone(), args, result)),
                _ => {}
            }
        }
    }
    loop {
        let mut progressed = false;
        let mut pending = Vec::new();
        for (name, args, result) in ops {
            let mut remove = false;
            match name.as_str() {
                "Seq_append" => {
                    let a = argument(&args, 0, "Seq_append")?;
                    let b = argument(&args, 1, "Seq_append")?;
                    if let (Some(left), Some(right)) = (sequences.get(a), sequences.get(b)) {
                        if !sequences.contains_key(&result) {
                            let mut value = left.clone();
                            value.extend_from_slice(right);
                            sequences.insert(result.clone(), value);
                            remove = true;
                            progressed = true;
                        }
                    }
                }
                "Seq_take" | "Seq_drop" | "Seq_index" | "Seq_update" => {
                    let id = argument(&args, 0, "sequence operation")?;
                    let index = argument(&args, 1, "sequence operation")?;
                    if let Some(value) = sequences.get(id).cloned() {
                        if !index.starts_with('(') {
                            let index = number(index)?;
                            match name.as_str() {
                                "Seq_take" => {
                                    sequences.insert(
                                        result.clone(),
                                        value.into_iter().take(index.max(0) as usize).collect(),
                                    );
                                }
                                "Seq_drop" => {
                                    sequences.insert(
                                        result.clone(),
                                        value.into_iter().skip(index.max(0) as usize).collect(),
                                    );
                                }
                                "Seq_index" => {
                                    if index < value.len() as i32 {
                                        if index < 0 {
                                            return Err(CollectionError::InvalidIndex(index));
                                        }
                                        let mut updated = value;
                                        updated[index as usize] = result.clone();
                                        sequences.insert(id.into(), updated);
                                    }
                                }
                                _ => {
                                    let replacement = argument(&args, 2, "Seq_update")?;
                                    if index < 0 || index as usize >= value.len() {
                                        return Err(CollectionError::InvalidIndex(index));
                                    }
                                    let mut updated = value;
                                    updated[index as usize] = replacement.into();
                                    sequences.insert(result.clone(), updated);
                                }
                            }
                        }
                        remove = true;
                        progressed = true;
                    }
                }
                _ => {}
            }
            if !remove {
                pending.push((name, args, result));
            }
        }
        ops = pending;
        if !progressed {
            break;
        }
    }
    Ok(sequences
        .into_iter()
        .map(|(id, values)| {
            let typ = ast_type_from_string(sort_parameter(&id));
            let values = values
                .iter()
                .map(|v| counterexample::literal(v, typ.as_ref()))
                .collect::<Vec<_>>();
            let value = if values.is_empty() {
                Exp::new(
                    ExpKind::EmptySeq(typ.unwrap_or(Type::InternalType)),
                    Default::default(),
                )
            } else {
                Exp::new(ExpKind::ExplicitSeq(values), Default::default())
            };
            CeCollection { id, value }
        })
        .collect())
}

/// Reconstruct update chains and, for otherwise unknown maps, combine explicit
/// Map_domain, Set_in and Map_apply facts, as the source does.
pub fn det_maps(model: &Model) -> Result<Vec<CeCollection>, CollectionError> {
    let mut maps = HashMap::<String, HashMap<String, String>>::new();
    if let Some(entry) = model.entries.get("Map_empty") {
        match entry {
            ModelEntry::Map(m) => {
                for value in m.options.values() {
                    maps.insert(value.to_string(), HashMap::new());
                }
            }
            ModelEntry::Value(ValueEntry::Constant(s)) if s != "true" && s != "false" => {
                maps.insert(s.clone(), HashMap::new());
            }
            _ => {}
        }
    }
    if let Some(m) = model_options(model, "Map_card") {
        for (args, value) in &m.options {
            if value.to_string().starts_with('0') {
                let first = args
                    .first()
                    .ok_or(CollectionError::MissingArgument("Map_card"))?;
                maps.insert(first.to_string(), HashMap::new());
            }
        }
    }
    let mut updates = Vec::new();
    if let Some(m) = model_options(model, "Map_update") {
        for (args, value) in &m.options {
            updates.push((
                args.iter().map(ToString::to_string).collect::<Vec<_>>(),
                value.to_string(),
            ));
        }
    }
    loop {
        let mut progress = false;
        let mut pending = Vec::new();
        for (args, result) in updates {
            let base = argument(&args, 0, "Map_update")?;
            if let Some(old) = maps.get(base) {
                let mut next = old.clone();
                next.insert(
                    argument(&args, 1, "Map_update")?.into(),
                    argument(&args, 2, "Map_update")?.into(),
                );
                maps.insert(result, next);
                progress = true;
            } else {
                pending.push((args, result));
            }
        }
        updates = pending;
        if !progress {
            break;
        }
    }
    let domains = model_options(model, "Map_domain")
        .map(|m| {
            m.options
                .iter()
                .filter_map(|(key, value)| key.first().map(|k| (k.to_string(), value.to_string())))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    if !domains.is_empty() {
        let mut memberships = HashMap::<String, Vec<String>>::new();
        if let Some(m) = model_options(model, "Set_in") {
            for (key, value) in &m.options {
                if value.to_string() == "true" && key.len() >= 2 {
                    let values = memberships.entry(key[1].to_string()).or_default();
                    let member = key[0].to_string();
                    if !values.contains(&member) {
                        values.push(member);
                    }
                }
            }
        }
        let mut apply = HashMap::new();
        if let Some(m) = model_options(model, "Map_apply") {
            for (key, value) in &m.options {
                if key.len() >= 2 {
                    apply.insert((key[0].to_string(), key[1].to_string()), value.to_string());
                }
            }
        }
        for (id, domain) in domains {
            if !maps.contains_key(&id) {
                let mut entries = HashMap::new();
                if let Some(keys) = memberships.get(&domain) {
                    for key in keys {
                        if let Some(value) = apply.get(&(id.clone(), key.clone())) {
                            entries.insert(key.clone(), value.clone());
                        }
                    }
                }
                maps.insert(id, entries);
            }
        }
    }
    Ok(maps
        .into_iter()
        .map(|(id, entries)| {
            let (key_type, value_type) = map_types_from_string(sort_parameter(&id));
            let maplets = entries
                .into_iter()
                .map(|(key, value)| {
                    Exp::new(
                        ExpKind::Maplet(
                            counterexample::literal(&key, key_type.as_ref()),
                            counterexample::literal(&value, value_type.as_ref()),
                        ),
                        Default::default(),
                    )
                })
                .collect::<Vec<_>>();
            let value = if maplets.is_empty() {
                Exp::new(
                    ExpKind::EmptyMap(
                        key_type.unwrap_or(Type::InternalType),
                        value_type.unwrap_or(Type::InternalType),
                    ),
                    Default::default(),
                )
            } else {
                Exp::new(ExpKind::ExplicitMap(maplets), Default::default())
            };
            CeCollection { id, value }
        })
        .collect())
}

#[derive(Debug)]
pub enum HeapResolutionError {
    MissingReference,
    MissingField,
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    WandEntry(counterexample::WandResolutionError),
}
/// Resolve the raw field/predicate/wand identities against the actual Program;
/// source uses prepend order and silently leaves unmatched resource names out.
pub fn det_heap(
    raw: &counterexample::RawHeap,
    program: &ferrum_silver::ast::program::Program,
    collections: &[CeCollection],
    names: &HashMap<String, String>,
    model: &Model,
) -> Result<counterexample::HeapCounterexample, HeapResolutionError> {
    use counterexample::{HeapEntryType as H, PredicateModel, ResolvedHeapEntry as E};
    use ferrum_silver::ast::utility::quantified_permissions::Resource;
    let mut entries = Vec::new();
    for item in raw.entries() {
        match item.entry_type {
            H::Field | H::QuantifiedField => {
                let field_name = item
                    .field
                    .first()
                    .ok_or(HeapResolutionError::MissingField)?;
                if let Some(field) = program.find_field_optionally(field_name) {
                    let reference = item
                        .reference
                        .first()
                        .ok_or(HeapResolutionError::MissingReference)?
                        .clone();
                    let value = collections
                        .iter()
                        .find(|c| c.id == item.value_id)
                        .map(|c| c.value.clone())
                        .unwrap_or_else(|| {
                            counterexample::literal(&item.value_id, Some(&field.typ))
                        });
                    entries.insert(
                        0,
                        (
                            Resource::Field(field.clone()),
                            E::Field {
                                reference,
                                field: field_name.clone(),
                                entry: value,
                                perm: item.perm.clone(),
                                typ: field.typ.clone(),
                                entry_type: item.entry_type,
                            },
                        ),
                    );
                }
            }
            H::Predicate | H::QuantifiedPredicate => {
                let name = item
                    .reference
                    .first()
                    .ok_or(HeapResolutionError::MissingReference)?;
                if let Some(predicate) = program.find_predicate_optionally(name) {
                    let args = item
                        .field
                        .iter()
                        .zip(&predicate.formal_args)
                        .map(|(value, formal)| counterexample::literal(value, Some(&formal.typ)))
                        .collect();
                    let inside_predicate = item.inside_predicate.as_ref().map(|entries| {
                        PredicateModel::new(entries.entries().iter().map(|(key, value)| {
                            let raw = value.to_string();
                            let translated = names.get(&raw).cloned().unwrap_or_else(|| {
                                model
                                    .entries
                                    .get(&raw)
                                    .map(ToString::to_string)
                                    .unwrap_or(raw)
                            });
                            (
                                key.clone(),
                                ModelEntry::Value(ValueEntry::Constant(translated)),
                            )
                        }))
                    });
                    entries.insert(
                        0,
                        (
                            Resource::Predicate(predicate.clone()),
                            E::Predicate {
                                name: name.clone(),
                                args,
                                perm: item.perm.clone(),
                                inside_predicate,
                                entry_type: item.entry_type,
                            },
                        ),
                    );
                }
            }
            H::MagicWand | H::QuantifiedMagicWand => {
                let name = item
                    .reference
                    .first()
                    .ok_or(HeapResolutionError::MissingReference)?;
                let values = item
                    .field
                    .iter()
                    .map(|v| names.get(v).cloned().unwrap_or_else(|| v.clone()))
                    .collect::<Vec<_>>();
                for (index, wand) in program
                    .magic_wand_structures()
                    .map_err(HeapResolutionError::Wand)?
                    .into_iter()
                    .enumerate()
                {
                    if name == &format!("wand@{index}") {
                        let value = E::wand_from_structure(
                            &wand,
                            &values,
                            item.perm.clone(),
                            item.entry_type,
                            program,
                        )
                        .map_err(HeapResolutionError::WandEntry)?;
                        entries.insert(0, (Resource::MagicWand(wand), value));
                    }
                }
            }
        }
    }
    Ok(counterexample::HeapCounterexample {
        heap_entries: entries,
    })
}

fn operations(model: &Model, names: &[&str]) -> Vec<(String, Vec<String>, String)> {
    let mut result = Vec::new();
    for name in names {
        if let Some(map) = model_options(model, name) {
            for (args, value) in &map.options {
                result.push((
                    (*name).into(),
                    args.iter().map(ToString::to_string).collect(),
                    value.to_string(),
                ));
            }
        }
    }
    result
}
/// The upstream set fixpoint loops forever when a referenced operand is never
/// seeded. Return `NoProgress` for that same incomplete dependency instead.
pub fn det_sets(model: &Model) -> Result<Vec<CeCollection>, CollectionError> {
    use std::collections::HashSet;
    let mut sets = HashMap::<String, HashSet<String>>::new();
    if let Some(entry) = model.entries.get("Set_empty") {
        match entry {
            ModelEntry::Map(m) => {
                for value in m.options.values() {
                    sets.insert(value.to_string(), HashSet::new());
                }
            }
            ModelEntry::Value(ValueEntry::Constant(value))
                if value != "true" && value != "false" =>
            {
                sets.insert(value.clone(), HashSet::new());
            }
            _ => {}
        }
    }
    if let Some(m) = model_options(model, "Set_singleton") {
        for (args, value) in &m.options {
            sets.insert(
                value.to_string(),
                HashSet::from([args
                    .first()
                    .ok_or(CollectionError::MissingArgument("Set_singleton"))?
                    .to_string()]),
            );
        }
    }
    if let Some(m) = model_options(model, "Set_card") {
        for (args, value) in &m.options {
            if value.to_string().starts_with('0') {
                sets.insert(
                    args.first()
                        .ok_or(CollectionError::MissingArgument("Set_card"))?
                        .to_string(),
                    HashSet::new(),
                );
            }
        }
    }
    for names in [
        &["Set_unionone", "Set_in"][..],
        &["Set_union", "Set_difference", "Set_intersection"][..],
    ] {
        let mut pending = operations(model, names);
        while !pending.is_empty() {
            let mut progress = false;
            let mut next = Vec::new();
            for (op, args, result) in pending {
                let a = argument(&args, 0, "set operation")?;
                let b = argument(&args, 1, "set operation")?;
                let value = match op.as_str() {
                    "Set_in" => {
                        let yes = if result.eq_ignore_ascii_case("true") {
                            true
                        } else if result.eq_ignore_ascii_case("false") {
                            false
                        } else {
                            return Err(CollectionError::InvalidBoolean(result));
                        };
                        if yes {
                            sets.entry(b.into()).or_default().insert(a.into());
                        }
                        Some(None)
                    }
                    "Set_unionone" => sets.get(a).map(|old| {
                        let mut s = old.clone();
                        s.insert(b.into());
                        Some(s)
                    }),
                    _ => match (sets.get(a), sets.get(b)) {
                        (Some(x), Some(y)) => Some(Some(match op.as_str() {
                            "Set_union" => x.union(y).cloned().collect(),
                            "Set_intersection" => x.intersection(y).cloned().collect(),
                            _ => x.difference(y).cloned().collect(),
                        })),
                        _ => None,
                    },
                };
                match value {
                    Some(value) => {
                        if let Some(value) = value {
                            sets.insert(result, value);
                        }
                        progress = true;
                    }
                    None => next.push((op, args, result)),
                }
            }
            pending = next;
            if !progress {
                return Err(CollectionError::NoProgress("set operations"));
            }
        }
    }
    Ok(sets
        .into_iter()
        .map(|(id, values)| {
            let typ = ast_type_from_string(sort_parameter(&id));
            let values = values
                .iter()
                .filter(|v| *v != "#undefined")
                .map(|v| counterexample::literal(v, typ.as_ref()))
                .collect::<Vec<_>>();
            let value = if values.is_empty() {
                Exp::new(
                    ExpKind::EmptySet(typ.unwrap_or(Type::InternalType)),
                    Default::default(),
                )
            } else {
                Exp::new(ExpKind::ExplicitSet(values), Default::default())
            };
            CeCollection { id, value }
        })
        .collect())
}

/// Multiset model reconstruction, retaining the source's difference rule (which
/// keeps keys occurring only in the right operand) and i32 wraparound arithmetic.
pub fn det_multisets(model: &Model) -> Result<Vec<CeCollection>, CollectionError> {
    use std::collections::HashSet;
    let mut sets = HashMap::<String, HashMap<String, i32>>::new();
    if let Some(entry) = model.entries.get("Multiset_empty") {
        match entry {
            ModelEntry::Map(m) => {
                for value in m.options.values() {
                    sets.insert(value.to_string(), HashMap::new());
                }
            }
            ModelEntry::Value(ValueEntry::Constant(value))
                if value != "true" && value != "false" =>
            {
                sets.insert(value.clone(), HashMap::new());
            }
            _ => {}
        }
    }
    if let Some(m) = model_options(model, "Multiset_singleton") {
        for (args, value) in &m.options {
            sets.insert(
                value.to_string(),
                HashMap::from([(
                    args.first()
                        .ok_or(CollectionError::MissingArgument("Multiset_singleton"))?
                        .to_string(),
                    1,
                )]),
            );
        }
    }
    if let Some(m) = model_options(model, "Multiset_count") {
        for (args, value) in &m.options {
            if !value.to_string().starts_with('0') {
                let id = args
                    .first()
                    .ok_or(CollectionError::MissingArgument("Multiset_count"))?
                    .to_string();
                let item = args
                    .get(1)
                    .ok_or(CollectionError::MissingArgument("Multiset_count"))?
                    .to_string();
                sets.entry(id)
                    .or_default()
                    .insert(item, number(&value.to_string())?);
            }
        }
    }
    if let Some(m) = model_options(model, "Multiset_card") {
        for (args, value) in &m.options {
            if value.to_string().starts_with('0') {
                sets.insert(
                    args.first()
                        .ok_or(CollectionError::MissingArgument("Multiset_card"))?
                        .to_string(),
                    HashMap::new(),
                );
            }
        }
    }
    for names in [
        &["Multiset_unionone"][..],
        &[
            "Multiset_union",
            "Multiset_difference",
            "Multiset_intersection",
        ][..],
    ] {
        let mut pending = operations(model, names);
        while !pending.is_empty() {
            let mut progress = false;
            let mut next = Vec::new();
            for (op, args, result) in pending {
                let a = argument(&args, 0, "multiset operation")?;
                let b = argument(&args, 1, "multiset operation")?;
                let value = if op == "Multiset_unionone" {
                    sets.get(a).map(|old| {
                        let mut value = old.clone();
                        let n = value.get(b).copied().unwrap_or(0).wrapping_add(1);
                        value.insert(b.into(), n);
                        value
                    })
                } else if let (Some(left), Some(right)) = (sets.get(a), sets.get(b)) {
                    let mut value = HashMap::new();
                    match op.as_str() {
                        "Multiset_union" => {
                            let keys = left.keys().chain(right.keys()).collect::<HashSet<_>>();
                            for key in keys {
                                value.insert(
                                    key.clone(),
                                    left.get(key)
                                        .copied()
                                        .unwrap_or(0)
                                        .wrapping_add(right.get(key).copied().unwrap_or(0)),
                                );
                            }
                        }
                        "Multiset_intersection" => {
                            for (key, count) in left {
                                if let Some(other) = right.get(key) {
                                    value.insert(key.clone(), (*count).min(*other));
                                }
                            }
                        }
                        _ => {
                            for (key, count) in left {
                                let difference =
                                    count.wrapping_sub(right.get(key).copied().unwrap_or(0));
                                if difference > 0 {
                                    value.insert(key.clone(), difference);
                                }
                            }
                            for (key, count) in right {
                                if !left.contains_key(key) {
                                    value.insert(key.clone(), *count);
                                }
                            }
                        }
                    }
                    Some(value)
                } else {
                    None
                };
                if let Some(value) = value {
                    sets.insert(result, value);
                    progress = true;
                } else {
                    next.push((op, args, result));
                }
            }
            pending = next;
            if !progress {
                return Err(CollectionError::NoProgress("multiset operations"));
            }
        }
    }
    Ok(sets
        .into_iter()
        .map(|(id, values)| {
            let typ = ast_type_from_string(sort_parameter(&id));
            let mut entries = Vec::new();
            for (value, count) in values {
                for _ in 0..count.max(0) {
                    entries.push(counterexample::literal(&value, typ.as_ref()));
                }
            }
            let value = if entries.is_empty() {
                Exp::new(
                    ExpKind::EmptyMultiset(typ.unwrap_or(Type::InternalType)),
                    Default::default(),
                )
            } else {
                Exp::new(ExpKind::ExplicitMultiset(entries), Default::default())
            };
            CeCollection { id, value }
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::verifier::verification_error::MapEntry;
    fn c(value: &str) -> ValueEntry {
        ValueEntry::Constant(value.into())
    }
    fn map(entries: Vec<(Vec<ValueEntry>, ValueEntry)>) -> ModelEntry {
        ModelEntry::Map(MapEntry {
            options: entries.into_iter().collect(),
            default: ValueEntry::Unspecified,
        })
    }
    #[test]
    fn sequence_fixpoint_reconstructs_append_from_singletons() {
        let model = Model {
            entries: HashMap::from([
                (
                    "Seq_singleton".into(),
                    map(vec![
                        (vec![c("1")], c("Seq<Int>!a")),
                        (vec![c("2")], c("Seq<Int>!b")),
                    ]),
                ),
                (
                    "Seq_append".into(),
                    map(vec![(
                        vec![c("Seq<Int>!a"), c("Seq<Int>!b")],
                        c("Seq<Int>!c"),
                    )]),
                ),
            ]),
        };
        let collections = det_sequences(&model).unwrap();
        let result = collections.iter().find(|c| c.id == "Seq<Int>!c").unwrap();
        assert!(
            matches!(result.value.kind(),ExpKind::ExplicitSeq(values) if values.len()==2 && matches!(values[0].kind(),ExpKind::IntLit(n) if *n==1.into()) && matches!(values[1].kind(),ExpKind::IntLit(n) if *n==2.into()))
        );
    }
    #[test]
    fn quantified_singleton_candidate_uses_evaluated_permission() {
        use crate::state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let variable = factory.var(Identifier::new("r"), Sort::Ref, false);
        let model = Model {
            entries: HashMap::new(),
        };
        let render = |_: &Term| Ok(String::new());
        let result = quantified_arguments(
            &[variable],
            &[],
            Some(&[factory.null()]),
            &factory.full_perm(),
            &model,
            &render,
        )
        .unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0, vec!["$Ref.null"]);
        assert_eq!(result[0].1.to_string(), "1/1");
    }
    #[test]
    fn unresolved_set_dependency_is_reported_instead_of_spinning() {
        let model = Model {
            entries: HashMap::from([(
                "Set_unionone".into(),
                map(vec![(vec![c("unknown"), c("x")], c("out"))]),
            )]),
        };
        assert!(matches!(
            det_sets(&model),
            Err(CollectionError::NoProgress("set operations"))
        ));
    }
}

/// Data collected by the raw extraction phases. `raw_heaps` is in source order:
/// old heaps are prepended as encountered, followed by the current heap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiliconRawCounterexample {
    pub basic_variables: Vec<CeVariable>,
    pub sequences: Vec<CeCollection>,
    pub sets: Vec<CeCollection>,
    pub multisets: Vec<CeCollection>,
    pub maps: Vec<CeCollection>,
    pub raw_heaps: Vec<(String, counterexample::RawHeap)>,
    pub domains: Vec<BasicDomainEntry>,
    pub functions: Vec<BasicFunctionEntry>,
}
impl counterexample::RawCounterexample for SiliconRawCounterexample {
    fn basic_variables(&self) -> &[CeVariable] {
        &self.basic_variables
    }
    fn all_sequences(&self) -> &[CeCollection] {
        &self.sequences
    }
    fn all_sets(&self) -> &[CeCollection] {
        &self.sets
    }
    fn all_multisets(&self) -> &[CeCollection] {
        &self.multisets
    }
    fn all_maps(&self) -> &[CeCollection] {
        &self.maps
    }
    fn all_raw_heaps(&self) -> &[(String, counterexample::RawHeap)] {
        &self.raw_heaps
    }
    fn domain_entries(&self) -> &[BasicDomainEntry] {
        &self.domains
    }
    fn non_domain_functions(&self) -> &[BasicFunctionEntry] {
        &self.functions
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiliconResolvedCounterexample {
    pub raw: SiliconRawCounterexample,
    pub store: StoreCounterexample,
    pub heaps: Vec<(String, counterexample::HeapCounterexample)>,
    pub domains: Vec<BasicDomainEntry>,
    pub functions: Vec<BasicFunctionEntry>,
}
impl counterexample::ResolvedCounterexample for SiliconResolvedCounterexample {
    fn raw_ce(&self) -> &dyn counterexample::RawCounterexample {
        &self.raw
    }
    fn store(&self) -> &StoreCounterexample {
        &self.store
    }
    fn heaps(&self) -> &[(String, counterexample::HeapCounterexample)] {
        &self.heaps
    }
    fn domain_entries(&self) -> &[BasicDomainEntry] {
        &self.domains
    }
    fn function_entries(&self) -> &[BasicFunctionEntry] {
        &self.functions
    }
}
#[derive(Debug)]
pub enum ResolveModelError {
    Store(ResolutionError),
    Heap(HeapResolutionError),
}
impl SiliconResolvedCounterexample {
    /// Assemble the source resolved view from already extracted raw phases.
    /// Model-to-raw heap and domain extraction must finish before this is called.
    pub fn from_raw(
        raw: SiliconRawCounterexample,
        store: &MapBackedStore,
        program: &ferrum_silver::ast::program::Program,
        model: &Model,
    ) -> Result<Self, ResolveModelError> {
        let collections = raw
            .sequences
            .iter()
            .chain(&raw.sets)
            .chain(&raw.multisets)
            .chain(&raw.maps)
            .cloned()
            .collect::<Vec<_>>();
        let (store, occurrences) = det_store(store, &raw.basic_variables, &collections)
            .map_err(ResolveModelError::Store)?;
        let names = translation_map(&raw.basic_variables, &collections, &occurrences)
            .map_err(ResolveModelError::Store)?;
        let heaps = raw
            .raw_heaps
            .iter()
            .rev()
            .map(|(name, heap)| {
                Ok((
                    name.clone(),
                    det_heap(heap, program, &collections, &names, model)
                        .map_err(ResolveModelError::Heap)?,
                ))
            })
            .collect::<Result<Vec<_>, ResolveModelError>>()?;
        let domains = translated_domains(&raw.domains, &names);
        let functions = translated_functions(&raw.functions, &names);
        Ok(Self {
            raw,
            store,
            heaps,
            domains,
            functions,
        })
    }
    pub fn render(&self) -> Result<String, ferrum_silver::ast::pretty::pretty_printer::PrintError> {
        let mut out = String::from("      Resolved Counterexample: \n   Store: \n");
        if !self.store.store_entries.is_empty() {
            out.push_str(&self.store.render()?);
        }
        for (name, heap) in &self.heaps {
            if !heap.heap_entries.is_empty() {
                out.push_str(&format!("   {name} Heap: \n{}", heap.render()?));
            }
        }
        if !self.domains.is_empty() || !self.functions.is_empty() {
            out.push_str("   Domains: \n");
            for domain in &self.domains {
                out.push_str(&domain.render()?);
                out.push('\n');
            }
            for function in &self.functions {
                out.push_str(&function.render()?);
                out.push('\n');
            }
        }
        Ok(out)
    }
}

#[derive(Debug)]
pub enum RawHeapError {
    Evaluation(super::converter::EvaluationError),
    Type(crate::state::symbol_converter::SymbolConversionError),
    Printer(ferrum_silver::ast::pretty::pretty_printer::PrintError),
    MissingArgument,
    Unsupported(&'static str),
}
fn eval_raw(
    term: &Term,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<super::converter::ExtractedModelEntry, RawHeapError> {
    super::converter::evaluate_term(term, model, &HashMap::new(), render)
        .map_err(RawHeapError::Evaluation)
}
fn raw_permission(
    term: &Term,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<Option<counterexample::Rational>, RawHeapError> {
    match eval_raw(term, model, render)? {
        super::converter::ExtractedModelEntry::Perm(value) => Ok(Some(
            counterexample::Rational::new(value.numerator().clone(), value.denominator().clone())
                .expect("normalized denominator is nonzero"),
        )),
        _ => Ok(None),
    }
}
/// Reconstruct fields inside one concrete predicate snapshot, preserving source
/// top-level conjunct order and its right-associated snapshot projection.
fn inside_predicate(
    assertion: &Exp,
    snapshot: &Term,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
    values: &mut Vec<(Exp, ModelEntry)>,
) -> Result<(), RawHeapError> {
    use super::converter::ExtractedModelEntry;
    use crate::state::terms::{TermFactory, TermOptions};
    let conjuncts = ferrum_silver::ast::utility::impure_assume_rewriter::split(assertion);
    let factory = TermFactory::new(TermOptions {
        use_flyweight: snapshot.uses_flyweight(),
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    if conjuncts.len() > 1 {
        for (index, conjunct) in conjuncts.iter().enumerate() {
            let mut part = snapshot.clone();
            for _ in 0..index {
                part = factory.second(part);
            }
            if index + 1 < conjuncts.len() {
                part = factory.first(part);
            }
            inside_predicate(conjunct, &part, model, render, values)?;
        }
        return Ok(());
    }
    match assertion.kind() {
        ExpKind::FieldAccessPredicate(field, _) => {
            let sort =
                crate::state::symbol_converter::DefaultSymbolConverter::new(factory.clone(), false)
                    .to_sort(&field.field.typ)
                    .map_err(RawHeapError::Type)?;
            let wrapped = factory.sort_wrapper(snapshot.clone(), sort);
            let value = match eval_raw(&wrapped, model, render)? {
                ExtractedModelEntry::Other { .. } => ValueEntry::Constant("#undefined".into()),
                value => value.as_value_entry(),
            };
            let key = Exp::new(ExpKind::FieldAccess(field.clone()), field.meta.clone());
            if let Some((_, old)) = values.iter_mut().find(|(existing, _)| existing == &key) {
                *old = ModelEntry::Value(value);
            } else {
                values.push((key, ModelEntry::Value(value)));
            }
        }
        ExpKind::Implies(guard, body) => {
            if body_condition_holds(guard, values)? {
                inside_predicate(body, snapshot, model, render, values)?
            }
        }
        ExpKind::CondExp(cond, yes, no) => {
            if body_condition_holds(cond, values)? {
                inside_predicate(yes, snapshot, model, render, values)?
            } else {
                inside_predicate(no, snapshot, model, render, values)?
            }
        }
        _ => {}
    }
    Ok(())
}
fn body_condition_holds(
    expression: &Exp,
    lookup: &[(Exp, ModelEntry)],
) -> Result<bool, RawHeapError> {
    let (left, right, negate) = match expression.kind() {
        ExpKind::EqCmp(a, b) => (a, b, false),
        ExpKind::NeCmp(a, b) => (a, b, true),
        _ => return Ok(false),
    };
    let value = |exp: &Exp| -> Result<String, RawHeapError> {
        match lookup.iter().find(|(e, _)| e == exp) {
            Some((_, v)) => Ok(v.to_string()),
            None => expression_string(exp).map_err(RawHeapError::Printer),
        }
    };
    let a = value(left)?;
    let b = value(right)?;
    if !a.is_ascii() || !b.is_ascii() {
        return Err(RawHeapError::Unsupported(
            "Java equalsIgnoreCase on non-ASCII model values",
        ));
    }
    Ok(a.eq_ignore_ascii_case(&b) ^ negate)
}
fn candidate_tuples(
    inverses: &[crate::rules::quantified_chunk_support::InverseFunctions],
    singleton: Option<&[Term]>,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<Vec<Vec<String>>, RawHeapError> {
    let mut tuples = Vec::new();
    for inverse in inverses {
        for function in inverse.inverses().chain(inverse.images()) {
            if let Some(ModelEntry::Map(map)) = model.entries.get(&function.id().to_string()) {
                for key in map.options.keys() {
                    let tuple = key.iter().map(ToString::to_string).collect::<Vec<_>>();
                    if !tuples.contains(&tuple) {
                        tuples.push(tuple);
                    }
                }
            }
        }
    }
    if tuples.is_empty() {
        if let Some(values) = singleton {
            let tuple = values
                .iter()
                .map(|t| eval_raw(t, model, render).map(|v| v.as_value_entry().to_string()))
                .collect::<Result<Vec<_>, _>>()?;
            tuples.push(tuple);
        }
    }
    Ok(tuples)
}
fn evaluated_quantified_permission(
    variables: &[Term],
    args: &[String],
    permission: &Term,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<Option<counterexample::Rational>, RawHeapError> {
    use crate::state::terms::TermKind;
    if args.len() < variables.len() {
        return Ok(None);
    }
    let mut env = HashMap::new();
    for (variable, value) in variables.iter().zip(args) {
        let TermKind::Var(variable) = variable.kind() else {
            return Err(RawHeapError::Unsupported("quantified non-variable"));
        };
        env.insert(
            variable.clone(),
            super::converter::ExtractedModelEntry::Unprocessed(ValueEntry::Constant(value.clone())),
        );
    }
    match super::converter::evaluate_term(permission, model, &env, render)
        .map_err(RawHeapError::Evaluation)?
    {
        super::converter::ExtractedModelEntry::Perm(value) if value.numerator() > &0.into() => {
            Ok(Some(
                counterexample::Rational::new(
                    value.numerator().clone(),
                    value.denominator().clone(),
                )
                .expect("positive rational"),
            ))
        }
        _ => Ok(None),
    }
}
fn quantified_arguments(
    variables: &[Term],
    inverses: &[crate::rules::quantified_chunk_support::InverseFunctions],
    singleton: Option<&[Term]>,
    permission: &Term,
    model: &Model,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<Vec<(Vec<String>, counterexample::Rational)>, RawHeapError> {
    let mut out = Vec::new();
    for tuple in candidate_tuples(inverses, singleton, model, render)? {
        if let Some(perm) =
            evaluated_quantified_permission(variables, &tuple, permission, model, render)?
        {
            out.push((tuple[..variables.len()].to_vec(), perm));
        }
    }
    Ok(out)
}
/// Extract source field, predicate, wand and quantified chunks. Concrete
/// quantified candidates come from inverse/image model keys or singleton terms.
pub fn det_raw_heap(
    model: &Model,
    chunks: &[crate::state::chunks::Chunk],
    program: &ferrum_silver::ast::program::Program,
    render: &impl Fn(&Term) -> Result<String, String>,
) -> Result<counterexample::RawHeap, RawHeapError> {
    use super::converter::ExtractedModelEntry;
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    use crate::state::terms::{TermFactory, TermKind, TermOptions};
    use crate::{resources::resources::BaseId, state::chunks::Chunk};
    use counterexample::{HeapEntryType as H, PredicateModel, RawHeapEntry};
    let mut entries = Vec::new();
    let mut quantified_fields =
        HashMap::<(String, String), (counterexample::Rational, String)>::new();
    let mut quantified_predicates =
        HashMap::<(String, Vec<String>), counterexample::Rational>::new();
    let mut quantified_wands = HashMap::<(String, Vec<String>), counterexample::Rational>::new();
    for chunk in chunks {
        match chunk {
            Chunk::Basic(chunk) if chunk.resource_id == BaseId::Field => {
                let receiver = chunk.args.first().ok_or(RawHeapError::MissingArgument)?;
                let value = match eval_raw(&chunk.snap, model, render)? {
                    ExtractedModelEntry::Other { .. } => "#undefined".into(),
                    v => v.to_string(),
                };
                entries.push(RawHeapEntry {
                    reference: vec![eval_raw(receiver, model, render)?.to_string()],
                    field: vec![chunk.id.0.clone()],
                    value_id: value,
                    perm: raw_permission(&chunk.perm, model, render)?,
                    entry_type: H::Field,
                    inside_predicate: None,
                });
            }
            Chunk::Basic(chunk) if chunk.resource_id == BaseId::Predicate => {
                let args = chunk
                    .args
                    .iter()
                    .map(|term| eval_raw(term, model, render).map(|e| e.to_string()))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut inside = Vec::new();
                if let Some(predicate) = program.find_predicate_optionally(&chunk.id.0) {
                    if let Some(body) = &predicate.body {
                        inside_predicate(body, &chunk.snap, model, render, &mut inside)?;
                    }
                }
                entries.push(RawHeapEntry {
                    reference: vec![chunk.id.0.clone()],
                    field: args,
                    value_id: render(&chunk.snap).map_err(|e| {
                        RawHeapError::Evaluation(super::converter::EvaluationError::Render(e))
                    })?,
                    perm: raw_permission(&chunk.perm, model, render)?,
                    entry_type: H::Predicate,
                    inside_predicate: Some(PredicateModel::new(inside)),
                });
            }
            Chunk::MagicWand(chunk) => {
                let mut args = Vec::new();
                for term in &chunk.args {
                    let value = eval_raw(term, model, render)?;
                    args.push(match value {
                        ExtractedModelEntry::Other { .. } => {
                            match raw_permission(term, model, render)? {
                                Some(permission) => permission.to_string(),
                                None => render(term).map_err(|e| {
                                    RawHeapError::Evaluation(
                                        super::converter::EvaluationError::Render(e),
                                    )
                                })?,
                            }
                        }
                        v => v.to_string(),
                    });
                }
                entries.push(RawHeapEntry {
                    reference: vec![chunk.id.to_string()],
                    field: args,
                    value_id: "#undefined".into(),
                    perm: raw_permission(&chunk.perm, model, render)?,
                    entry_type: H::MagicWand,
                    inside_predicate: None,
                });
            }
            Chunk::QuantifiedField(chunk) => {
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: chunk.fvf.uses_flyweight(),
                    use_old_axiomatization: false,
                    mask_heap_mode: false,
                });
                let variables = chunk.quantified_vars(&factory);
                let variable = variables.first().ok_or(RawHeapError::MissingArgument)?;
                let TermKind::Var(variable_data) = variable.kind() else {
                    return Err(RawHeapError::Unsupported("quantified field variable"));
                };
                let tuples = candidate_tuples(chunk.inverse_functions(), None, model, render)?;
                let mut receivers = Vec::new();
                for tuple in tuples {
                    if let Some(value) = tuple.last() {
                        if !receivers.contains(value) {
                            receivers.push(value.clone());
                        }
                    }
                }
                if receivers.is_empty() {
                    if let Some(receiver) = &chunk.singleton_rcvr {
                        receivers.push(
                            eval_raw(receiver, model, render)?
                                .as_value_entry()
                                .to_string(),
                        );
                    }
                }
                for receiver in receivers {
                    let permission = chunk.permission(&factory);
                    if let Some(perm) = evaluated_quantified_permission(
                        &variables,
                        std::slice::from_ref(&receiver),
                        &permission,
                        model,
                        render,
                    )? {
                        let mut env = HashMap::new();
                        env.insert(
                            variable_data.clone(),
                            ExtractedModelEntry::Unprocessed(ValueEntry::Constant(
                                receiver.clone(),
                            )),
                        );
                        let value = super::converter::evaluate_term(
                            &chunk.value_at(&factory, std::slice::from_ref(variable)),
                            model,
                            &env,
                            render,
                        )
                        .map_err(RawHeapError::Evaluation)?;
                        let value = if matches!(value, ExtractedModelEntry::Other { .. }) {
                            "#undefined".into()
                        } else {
                            value.to_string()
                        };
                        let key = (receiver, chunk.id.0.clone());
                        if let Some((old, known)) = quantified_fields.get_mut(&key) {
                            *old = old.add(&perm);
                            if known == "#undefined" {
                                *known = value;
                            }
                        } else {
                            quantified_fields.insert(key, (perm, value));
                        }
                    }
                }
            }
            Chunk::QuantifiedPredicate(chunk) => {
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: chunk.psf.uses_flyweight(),
                    use_old_axiomatization: false,
                    mask_heap_mode: false,
                });
                for (args, perm) in quantified_arguments(
                    &chunk.quantified_vars(&factory),
                    chunk.inverse_functions(),
                    chunk.singleton_arguments(),
                    &chunk.permission(&factory),
                    model,
                    render,
                )? {
                    let key = (chunk.id.0.clone(), args);
                    if let Some(old) = quantified_predicates.get_mut(&key) {
                        *old = old.add(&perm);
                    } else {
                        quantified_predicates.insert(key, perm);
                    }
                }
            }
            Chunk::QuantifiedMagicWand(chunk) => {
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: chunk.wsf.uses_flyweight(),
                    use_old_axiomatization: false,
                    mask_heap_mode: false,
                });
                for (args, perm) in quantified_arguments(
                    &chunk.quantified_vars(&factory),
                    chunk.inverse_functions(),
                    chunk.singleton_arguments(),
                    &chunk.permission(&factory),
                    model,
                    render,
                )? {
                    let key = (chunk.id.to_string(), args);
                    if let Some(old) = quantified_wands.get_mut(&key) {
                        *old = old.add(&perm);
                    } else {
                        quantified_wands.insert(key, perm);
                    }
                }
            }
            _ => return Err(RawHeapError::Unsupported("raw heap chunk")),
        }
    }
    for ((receiver, field), (perm, value)) in quantified_fields {
        entries.push(RawHeapEntry {
            reference: vec![receiver],
            field: vec![field],
            value_id: value,
            perm: Some(perm),
            entry_type: H::QuantifiedField,
            inside_predicate: None,
        });
    }
    for ((name, args), perm) in quantified_predicates {
        entries.push(RawHeapEntry {
            reference: vec![name],
            field: args,
            value_id: "#undefined".into(),
            perm: Some(perm),
            entry_type: H::QuantifiedPredicate,
            inside_predicate: None,
        });
    }
    for ((name, args), perm) in quantified_wands {
        entries.push(RawHeapEntry {
            reference: vec![name],
            field: args,
            value_id: "#undefined".into(),
            perm: Some(perm),
            entry_type: H::QuantifiedMagicWand,
            inside_predicate: None,
        });
    }
    Ok(counterexample::RawHeap::new(entries))
}
