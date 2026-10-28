// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Term converter contract from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/decider/TermConverter.scala
//! Status: source operations represented with explicit conversion errors.

use crate::state::terms::{Declaration, Sort, Term};
pub trait TermConverter {
    type TermOutput;
    type SortOutput;
    type DeclarationOutput;
    type Error;
    fn convert_term(&mut self, term: &Term) -> Result<Self::TermOutput, Self::Error>;
    fn convert_sort(&mut self, sort: &Sort) -> Result<Self::SortOutput, Self::Error>;
    fn convert_sanitized_sort(&mut self, sort: &Sort) -> Result<Self::SortOutput, Self::Error>;
    fn convert_declaration(
        &mut self,
        decl: &Declaration,
    ) -> Result<Self::DeclarationOutput, Self::Error>;
}
