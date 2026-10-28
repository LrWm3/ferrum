// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Ordered symbolic heap from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Heap.scala
//! Status: list-backed operations implemented; source-compatible rendering for
//! `equalChunks` must be supplied by the caller until term/chunk Display is ported.

use super::chunks::Chunk;

pub trait Heap {
    fn values(&self) -> &[Chunk];
}

#[derive(Clone, Debug, Default)]
pub struct ListBackedHeap {
    chunks: Vec<Chunk>,
}
impl ListBackedHeap {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn from_chunks(chunks: impl IntoIterator<Item = Chunk>) -> Self {
        let chunks: Vec<_> = chunks.into_iter().collect();
        for chunk in &chunks {
            chunk.validate();
        }
        Self { chunks }
    }
    #[must_use]
    pub fn with_chunk(&self, chunk: Chunk) -> Self {
        chunk.validate();
        let mut result = self.clone();
        result.chunks.push(chunk);
        result
    }
    #[must_use]
    pub fn with_heap(&self, other: &impl Heap) -> Self {
        let mut result = self.clone();
        result.chunks.extend(other.values().iter().cloned());
        result
    }
    #[must_use]
    pub fn without_chunk(&self, chunk: &Chunk) -> Self {
        let index = self
            .chunks
            .iter()
            .position(|c| c == chunk)
            .expect("cannot remove a chunk absent from the heap");
        let mut result = self.clone();
        result.chunks.remove(index);
        result
    }
    /// Source sorts by each chunk's `toString`, then compares the sorted sequences.
    /// Equal renderings retain original order; Java's UTF-16 string ordering is used.
    pub fn equal_chunks_by<E>(
        &self,
        other: &impl Heap,
        render: impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<bool, E> {
        fn sorted<'a, E>(
            chunks: &'a [Chunk],
            render: &impl Fn(&Chunk) -> Result<String, E>,
        ) -> Result<Vec<&'a Chunk>, E> {
            let mut entries = chunks
                .iter()
                .map(|chunk| Ok((render(chunk)?, chunk)))
                .collect::<Result<Vec<_>, E>>()?;
            entries.sort_by(|(a, _), (b, _)| a.encode_utf16().cmp(b.encode_utf16()));
            Ok(entries.into_iter().map(|(_, chunk)| chunk).collect())
        }
        Ok(sorted(&self.chunks, &render)? == sorted(other.values(), &render)?)
    }
}
impl Heap for ListBackedHeap {
    fn values(&self) -> &[Chunk] {
        &self.chunks
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resources::resources::BaseId;
    use crate::state::chunks::{BasicChunk, BasicChunkIdentifier};
    use crate::state::terms::{TermFactory, TermOptions};
    fn chunk(f: &TermFactory, value: i32) -> Chunk {
        Chunk::Basic(BasicChunk::new(
            BaseId::Field,
            BasicChunkIdentifier("f".into()),
            vec![],
            None,
            f.int_literal(value),
            None,
            f.full_perm(),
            None,
            None,
        ))
    }
    #[test]
    fn removal_deletes_only_first_and_equal_render_ties_keep_order() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let a = chunk(&f, 1);
        let b = chunk(&f, 2);
        let left = ListBackedHeap::from_chunks([a.clone(), b.clone(), a.clone()]);
        assert_eq!(left.without_chunk(&a).values(), &[b.clone(), a.clone()]);
        let reversed = ListBackedHeap::from_chunks([b, a.clone(), a]);
        assert!(
            !left
                .equal_chunks_by(&reversed, |_| Ok::<_, ()>("same".to_owned()))
                .unwrap()
        );
    }
}
