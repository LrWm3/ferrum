// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Chunk contracts from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/state/Chunks.scala
//! Status: contracts implemented against concrete Rust chunk representations.

use crate::resources::resources::ResourceId;
use crate::rules::quantified_chunk_support::InverseFunctions;
use crate::state::chunks::{ChunkError, ChunkIdentifier};
use crate::state::terms::{ResourceKey, Term, TermFactory};
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::LocalVarDecl;
use std::collections::HashMap;

pub trait Chunk: Sized {
    fn substitute(
        &self,
        factory: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError>;
}
pub trait MaskHeapChunk: Chunk {
    fn resource_id(&self) -> ResourceId;
    fn resource(&self) -> &ResourceKey;
    fn mask(&self) -> &Term;
    fn heap(&self) -> &Term;
}
pub trait GeneralChunk: Chunk {
    fn resource_id(&self) -> ResourceId;
    fn identifier(&self) -> ChunkIdentifier;
    fn permission(&self, factory: &TermFactory) -> Term;
    fn permission_exp(&self) -> Option<Exp>;
    fn tag(&self) -> Option<i32>;
    fn apply_condition(
        &self,
        factory: &TermFactory,
        condition: Term,
        condition_exp: Option<Exp>,
    ) -> Self;
    fn perm_minus(
        &self,
        factory: &TermFactory,
        permission: Term,
        permission_exp: Option<Exp>,
    ) -> Self;
    fn perm_plus(
        &self,
        factory: &TermFactory,
        permission: Term,
        permission_exp: Option<Exp>,
    ) -> Self;
    fn perm_scale(
        &self,
        factory: &TermFactory,
        permission: Term,
        permission_exp: Option<Exp>,
    ) -> Self;
}
pub trait NonQuantifiedChunk: GeneralChunk {
    fn args(&self) -> &[Term];
    fn args_exp(&self) -> Option<&[Exp]>;
    fn snapshot(&self) -> &Term;
    fn with_permission(&self, permission: Term, permission_exp: Option<Exp>) -> Self;
    fn with_snapshot(&self, snapshot: Term, snapshot_exp: Option<Exp>) -> Self;
}
pub trait QuantifiedChunk: GeneralChunk {
    fn quantified_vars(&self, factory: &TermFactory) -> Vec<Term>;
    fn quantified_var_exps(&self) -> Option<Vec<LocalVarDecl>>;
    fn inverse_functions(&self) -> &[InverseFunctions];
    fn original_condition(&self) -> &Term;
    fn snapshot_map(&self) -> &Term;
    fn value_at(&self, factory: &TermFactory, arguments: &[Term]) -> Term;
    fn with_snapshot_map(&self, snapshot: Term) -> Self;
}
