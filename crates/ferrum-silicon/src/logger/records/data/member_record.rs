//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/MemberRecord.scala
//!
//! Purpose:
//! Attach the last failed prover query to member log data.
//!
//! Planned Rust structure:
//! Port MemberRecord extension of DataRecord and lastFailedProverQuery.
//!
//! Behavior to preserve:
//! getData preserves base data and sets lastSMTQuery from the optional stored term.
//!
//! Integration:
//! function_record, method_record, predicate_record and symb_ex_logger/writer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for recorded term ownership.
//!
//! Open decisions:
//! Agree on member record mutation and query lifetime with logger.
//!
//! Status: member failed-query contract and report enrichment implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::logger::records::{data::data_record::DataRecord, symbolic_record::RecordError};
use crate::state::terms::Term;
pub trait MemberRecord: DataRecord {
    fn last_failed_query(&self) -> Result<Option<Term>, RecordError>;
    fn set_last_failed_query(&self, query: Option<Term>) -> Result<(), RecordError>;
}
