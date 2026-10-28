//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Chunks.scala
//!
//! Purpose:
//! Implement heap chunks for ordinary, quantified, wand and mask-heap resources.
//!
//! Planned Rust structure:
//! ChunkIdentifier/BasicChunkIdentifier and MagicWandIdentifier; BasicChunk,
//! QuantifiedBasicChunk, QuantifiedFieldChunk, QuantifiedPredicateChunk,
//! QuantifiedMagicWandChunk, MagicWandChunk and BasicMaskHeapChunk. Implement condition,
//! permission arithmetic, snapshot replacement, lookup and substitution for each.
//!
//! Behavior to preserve:
//! Check permission/snapshot sorts and field lookup arity; quantified field/predicate
//! permission is conditional and their scaling uses computed permission. Preserve optional
//! expression assumptions, tags, hints, inverse functions and singleton arguments. Wand
//! identifier equality uses structure index hash only; wand snapshot replacement requires
//! MagicWandSnapshot and no expression. Substitution follows each class fields, not all
//! metadata.
//!
//! Merging quantified chunks may retain inverse functions from multiple source
//! assertions because their definitions and matching triggers remain needed.
//! Quantified wand snapshots use predicate snapshot functions with wand-snapshot
//! codomain; the field's synthetic receiver is ?r and debug declarations are
//! created only in debugging mode.
//!
//! Integration:
//! interfaces::state::chunks, state::terms, resources, rules::quantified_chunk_support
//! (InverseFunctions) and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Chunk representation and expression pairing with heap and state remain open.
//!
//! Status: chunk identifier representations and program-based wand indexing are
//! implemented; chunk implementations remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::Program;
use ferrum_silver::ast::utility::expressions::MagicWandError;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BasicChunkIdentifier(pub String);
impl fmt::Display for BasicChunkIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Equality is deliberately only the program's wand-structure index, as upstream.
/// The retained expression is used for source positions, not equality.
#[derive(Clone, Debug)]
pub struct MagicWandIdentifier {
    pub ghost_free_wand: Exp,
    pub structure_index: i32,
}
impl MagicWandIdentifier {
    /// Compute the program-local structure index, retaining -1 if the structure is absent.
    pub fn new(ghost_free_wand: Exp, program: &Program) -> Result<Self, MagicWandError> {
        let structure = ghost_free_wand.magic_wand_structure(program, false)?;
        let structures = program.magic_wand_structures()?;
        let index = structures
            .iter()
            .position(|candidate| candidate == &structure)
            .map_or(-1, |i| {
                i32::try_from(i).expect("too many magic wand structures")
            });
        Ok(Self::from_structure_index(ghost_free_wand, index))
    }
    /// Use the structure index computed from the Silver program (including -1 when absent).
    pub fn from_structure_index(ghost_free_wand: Exp, structure_index: i32) -> Self {
        assert!(
            matches!(ghost_free_wand.kind(), ExpKind::MagicWand(..)),
            "expected a magic wand expression"
        );
        Self {
            ghost_free_wand,
            structure_index,
        }
    }
}
impl PartialEq for MagicWandIdentifier {
    fn eq(&self, other: &Self) -> bool {
        self.structure_index == other.structure_index
    }
}
impl Eq for MagicWandIdentifier {}
impl Hash for MagicWandIdentifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.structure_index.hash(state);
    }
}
impl fmt::Display for MagicWandIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wand@{}", self.structure_index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::ast::ast::Metadata;

    #[test]
    fn wand_identity_is_the_program_structure_index() {
        let truth = Exp::new(ExpKind::TrueLit, Metadata::default());
        let wand = Exp::new(
            ExpKind::MagicWand(truth.clone(), truth),
            Metadata::default(),
        );
        let a = MagicWandIdentifier::from_structure_index(wand.clone(), -1);
        let b = MagicWandIdentifier::from_structure_index(wand.clone(), -1);
        let c = MagicWandIdentifier::from_structure_index(wand, 0);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(a.to_string(), "wand@-1");
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let absent = MagicWandIdentifier::new(a.ghost_free_wand.clone(), &program).unwrap();
        assert_eq!(absent.structure_index, -1);
    }
}
