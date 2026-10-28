//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/writer/SymbExLogReportWriter.scala
//!
//! Purpose:
//! Serialize member symbolic execution logs and state data to JSON.
//!
//! Planned Rust structure:
//! Port SymbExLogReportWriter toJSON overloads, getAllRecords, heapChunkToJSON and
//! inverseFunctionsToJSON.
//!
//! Behavior to preserve:
//! Flatten each branching record before its branch records in order; emit id/kind/value,
//! scope/join flags, branch IDs and optional data only when present. Serialize stores, ordered
//! PCS, basic and quantified field/predicate/wand chunks including inverse axioms, hints and
//! singleton arguments; unknown chunks use upstream unstructrured_chunk fallback.
//!
//! Integration:
//! logger::records, log_config, logger::writer::term_writer, state::{heap,store,chunks} and
//! rules::quantified_chunk_support.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state capture, collection order and JSON schema.
//!
//! Open decisions:
//! Reconcile mask-heap chunk fallback and schema evolution with log consumers.
//!
//! Status: native JSON record, store, heap, inverse and branch serialization implemented.
//! Exact term and fallback rendering remain injected until source printers are complete.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::term_writer::{sort_to_json, term_to_json};
use crate::{
    logger::{
        log_config::LogConfig,
        records::{
            record_data::RecordData,
            scoping::{close_scope_record::CloseScopeRecord, open_scope_record::OpenScopeRecord},
            structural::branching_record::{BranchInfo, BranchingRecord},
            symbolic_record::{RecordError, RecordRef, RecordRenderer, SymbolicRecord},
        },
        symb_ex_logger::MemberSymbExLog,
    },
    resources::resources::BaseId,
    rules::quantified_chunk_support::InverseFunctions,
    state::{
        chunks::Chunk,
        heap::{Heap, ListBackedHeap},
        store::MapBackedStore,
        terms::Term,
    },
};
use serde_json::{Map, Value, json};
fn terms_json(terms: &[Term], renderer: &dyn RecordRenderer) -> Result<Value, RecordError> {
    Ok(Value::Array(
        terms
            .iter()
            .map(|t| term_to_json(t, renderer))
            .collect::<Result<_, _>>()?,
    ))
}
fn optional_terms(terms: &[Term], renderer: &dyn RecordRenderer) -> Result<Value, RecordError> {
    if terms.is_empty() {
        Ok(Value::Null)
    } else {
        terms_json(terms, renderer)
    }
}
fn singleton_args(
    args: &Option<Vec<Term>>,
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    // Scala maps Option to a zero- or one-element array containing the argument array.
    Ok(Value::Array(
        args.iter()
            .map(|args| terms_json(args, renderer))
            .collect::<Result<_, _>>()?,
    ))
}
fn tag(value: &Option<i32>) -> String {
    value
        .map(|v| format!("Some({v})"))
        .unwrap_or_else(|| "None".into())
}
fn inverses_json(
    inverses: &[InverseFunctions],
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    if inverses.is_empty() {
        return Ok(Value::Null);
    }
    Ok(Value::Array(
        inverses
            .iter()
            .flat_map(|i| i.definitional_axioms())
            .map(|t| term_to_json(t, renderer))
            .collect::<Result<_, _>>()?,
    ))
}
pub fn chunk_to_json(chunk: &Chunk, renderer: &dyn RecordRenderer) -> Result<Value, RecordError> {
    Ok(match chunk {
        Chunk::Basic(c) if *c.resource_id_ref() == BaseId::Predicate => {
            json!({"type":"basic_predicate_chunk","predicate":c.id_ref().to_string(),"args":terms_json(c.args_ref(),renderer)?,"snap":term_to_json(c.snap_ref(),renderer)?,"perm":term_to_json(c.perm_ref(),renderer)?,"tag":tag(c.tag_ref())})
        }
        Chunk::Basic(c) if *c.resource_id_ref() == BaseId::Field && c.args_ref().len() == 1 => {
            json!({"type":"basic_field_chunk","field":c.id_ref().to_string(),"receiver":term_to_json(&c.args_ref()[0],renderer)?,"snap":term_to_json(c.snap_ref(),renderer)?,"perm":term_to_json(c.perm_ref(),renderer)?,"tag":tag(c.tag_ref())})
        }
        Chunk::MagicWand(c) => {
            json!({"type":"basic_magic_wand_chunk","args":terms_json(c.args_ref(),renderer)?,"snap":term_to_json(c.snap_ref(),renderer)?,"perm":term_to_json(c.perm_ref(),renderer)?,"tag":tag(c.tag_ref())})
        }
        Chunk::QuantifiedField(c) => {
            json!({"type":"quantified_field_chunk","field":c.id_ref().to_string(),"field_value_function":term_to_json(c.fvf_ref(),renderer)?,"condition":term_to_json(c.condition_ref(),renderer)?,"perm":term_to_json(c.perm_value_ref(),renderer)?,"invs":inverses_json(c.invs_ref(),renderer)?,"receiver":c.singleton_rcvr_ref().as_ref().map(|r| term_to_json(r,renderer)).transpose()?.unwrap_or(Value::Null),"tag":tag(c.tag_ref()),"hints":optional_terms(c.hints_ref(),renderer)?})
        }
        Chunk::QuantifiedPredicate(c) => {
            json!({"type":"quantified_predicate_chunk","vars":terms_json(c.quantified_vars_ref(),renderer)?,"predicate":c.id_ref().to_string(),"predicate_snap_function":term_to_json(c.psf_ref(),renderer)?,"condition":term_to_json(c.condition_ref(),renderer)?,"perm":term_to_json(c.perm_value_ref(),renderer)?,"invs":inverses_json(c.invs_ref(),renderer)?,"singleton_args":singleton_args(c.singleton_args_ref(),renderer)?,"tag":tag(c.tag_ref()),"hints":optional_terms(c.hints_ref(),renderer)?})
        }
        Chunk::QuantifiedMagicWand(c) => {
            json!({"type":"quantified_magic_wand_chunk","vars":terms_json(c.quantified_vars_ref(),renderer)?,"predicate":c.id_ref().to_string(),"wand_snap_function":term_to_json(c.wsf_ref(),renderer)?,"perm":term_to_json(c.perm_ref(),renderer)?,"invs":inverses_json(c.invs_ref(),renderer)?,"singleton_args":singleton_args(c.singleton_args_ref(),renderer)?,"tag":tag(c.tag_ref()),"hints":optional_terms(c.hints_ref(),renderer)?})
        }
        _ => json!({"type":"unstructrured_chunk","value":renderer.chunk(chunk)?}),
    })
}
pub fn heap_to_json(
    heap: &ListBackedHeap,
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    Ok(Value::Array(
        heap.values()
            .iter()
            .map(|c| chunk_to_json(c, renderer))
            .collect::<Result<_, _>>()?,
    ))
}
pub fn store_to_json(
    store: &MapBackedStore,
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    use ferrum_silver::ast::expression::ExpKind;
    Ok(Value::Array(store.term_values().map(|(var,value)| {
        let name = match var.expression().kind() {
            ExpKind::LocalVar(var) => var.name.clone(),
            ExpKind::LocalVarWithVersion(name, _) => name.clone(),
            ExpKind::Result(_) => "result".into(),
            _ => return Err(RecordError::Unsupported("unexpected abstract local variable")),
        };
        Ok(json!({"name":name,"value":term_to_json(value,renderer)?,"sort":sort_to_json(value.sort())}))
    }).collect::<Result<_,_>>()?))
}
pub fn branch_to_json(branch: &BranchInfo) -> Value {
    json!({"isReachable":branch.is_reachable,"startTimeMs":branch.start_time_ms,"records":branch.records.iter().map(|r| r.id()).collect::<Vec<_>>()})
}
pub fn data_to_json(
    data: &RecordData,
    renderer: &dyn RecordRenderer,
) -> Result<Option<Value>, RecordError> {
    let mut fields = Map::new();
    if let Some(id) = data.ref_id {
        fields.insert("refId".into(), json!(id));
    }
    if data.is_smt_query {
        fields.insert("isSmtQuery".into(), json!(true));
    }
    if let Some(stats) = &data.smt_statistics {
        fields.insert(
            "smtStatistics".into(),
            Value::Object(
                stats
                    .iter()
                    .map(|(k, v)| (k.clone(), Value::String(v.clone())))
                    .collect(),
            ),
        );
    }
    if let Some(ms) = data.time_ms {
        fields.insert("timeMs".into(), json!(ms));
    }
    if let Some(pos) = &data.pos {
        fields.insert("pos".into(), json!(pos));
    }
    if let Some(query) = &data.last_smt_query {
        fields.insert("lastSMTQuery".into(), term_to_json(query, renderer)?);
    }
    if let Some(store) = &data.store {
        fields.insert("store".into(), store_to_json(store, renderer)?);
    }
    if let Some(heap) = &data.heap {
        fields.insert("heap".into(), heap_to_json(heap, renderer)?);
    }
    if let Some(heap) = &data.old_heap {
        fields.insert("oldHeap".into(), heap_to_json(heap, renderer)?);
    }
    if let Some(pcs) = &data.pcs {
        fields.insert(
            "pcs".into(),
            Value::Array(
                pcs.iter()
                    .map(|t| term_to_json(t, renderer))
                    .collect::<Result<_, _>>()?,
            ),
        );
    }
    Ok(if fields.is_empty() {
        None
    } else {
        Some(Value::Object(fields))
    })
}
/// Flatten a branching record before its branches, preserving branch and record order.
pub fn get_all_records(records: &[RecordRef]) -> Result<Vec<RecordRef>, RecordError> {
    let mut result = Vec::new();
    for record in records {
        result.push(record.clone());
        if let Some(branch) = record.as_any().downcast_ref::<BranchingRecord>() {
            for info in branch.branch_infos()? {
                result.extend(get_all_records(&info.records)?);
            }
        }
    }
    Ok(result)
}
pub fn record_to_json(
    record: &dyn SymbolicRecord,
    config: &LogConfig,
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    let data = data_to_json(&record.get_data(config, renderer)?, renderer)?;
    let mut fields = Map::new();
    fields.insert("id".into(), json!(record.id()));
    fields.insert("kind".into(), json!(record.type_string()));
    fields.insert("value".into(), json!(record.simple_string(renderer)?));
    if record.is_joining() {
        fields.insert("isJoinPoint".into(), json!(true));
    }
    if record.as_any().is::<OpenScopeRecord>() {
        fields.insert("isScopeOpen".into(), json!(true));
    }
    if record.as_any().is::<CloseScopeRecord>() {
        fields.insert("isScopeClose".into(), json!(true));
    }
    if let Some(branch) = record.as_any().downcast_ref::<BranchingRecord>() {
        fields.insert(
            "branches".into(),
            Value::Array(branch.branch_infos()?.iter().map(branch_to_json).collect()),
        );
    }
    if let Some(data) = data {
        fields.insert("data".into(), data);
    }
    Ok(Value::Object(fields))
}
pub fn members_to_json(
    members: &[&MemberSymbExLog],
    config: &LogConfig,
    renderer: &dyn RecordRenderer,
) -> Result<Value, RecordError> {
    let mut records = Vec::new();
    for member in members {
        for record in get_all_records(&member.records()?)? {
            records.push(record_to_json(record.as_ref(), config, renderer)?);
        }
    }
    Ok(Value::Array(records))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::records::data::comment_record::CommentRecord;
    use ferrum_silver::ast::utility::nodes::Node;
    use std::sync::Arc;
    struct Text;
    impl RecordRenderer for Text {
        fn node(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("node"))
        }
        fn term(&self, _: &Term) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("term"))
        }
        fn chunk(&self, _: &Chunk) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("chunk"))
        }
        fn source_line_column(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("position"))
        }
    }
    #[test]
    fn source_schema_flattens_branches_and_omits_absent_data() {
        let root = Arc::new(BranchingRecord::new(2, None, None));
        root.set_id(10);
        let comment = Arc::new(CommentRecord::<()>::new(Some("a\n\"b".into()), None, None));
        comment.set_id(11);
        root.append_log(comment).unwrap();
        root.mark_reachable_at(120).unwrap();
        let roots: Vec<RecordRef> = vec![root.clone()];
        let flattened = get_all_records(&roots).unwrap();
        assert_eq!(
            flattened.iter().map(|r| r.id()).collect::<Vec<_>>(),
            vec![10, 11]
        );
        let actual = record_to_json(root.as_ref(), &LogConfig::default(), &Text).unwrap();
        assert_eq!(
            actual,
            json!({"id":10,"kind":"branching","value":"null","branches":[{"isReachable":true,"startTimeMs":120,"records":[11]},{"isReachable":false,"startTimeMs":0,"records":[]}]})
        );
        let json = record_to_json(flattened[1].as_ref(), &LogConfig::default(), &Text).unwrap();
        assert_eq!(json, json!({"id":11,"kind":"comment","value":"a\n\"b"}));
        let encoded = serde_json::to_string(&json).unwrap();
        assert_eq!(serde_json::from_str::<Value>(&encoded).unwrap(), json);
    }
}
