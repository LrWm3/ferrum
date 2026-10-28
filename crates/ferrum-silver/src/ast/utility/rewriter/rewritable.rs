//! Typed product reconstruction for Silver's rewriter.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/Rewritable.scala
//! Status: partial. Generic product reconstruction protocol is implemented; concrete
//! Silver AST and parser product adapters, metadata replacement and extra vars are pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

/// Source constructor-product fields, including nested Scala container shapes.
/// Atoms are retained verbatim by the adapter; they are not recursively visited.
#[derive(Clone, Debug)]
pub enum ProductValue<N, A> {
    Node(N),
    Sequence(Vec<ProductValue<N, A>>),
    Optional(Option<Box<ProductValue<N, A>>>),
    Left(Box<ProductValue<N, A>>),
    Right(Box<ProductValue<N, A>>),
    Tuple(Vec<ProductValue<N, A>>),
    Map(Vec<(ProductValue<N, A>, ProductValue<N, A>)>),
    Atom(A),
}
impl<N: PartialEq, A: PartialEq> PartialEq for ProductValue<N, A> {
    fn eq(&self, other: &Self) -> bool {
        use ProductValue::*;
        match (self, other) {
            (Node(a), Node(b)) => a == b,
            (Sequence(a), Sequence(b)) | (Tuple(a), Tuple(b)) => a == b,
            (Optional(a), Optional(b)) => a == b,
            (Left(a), Left(b)) | (Right(a), Right(b)) => a == b,
            (Map(a), Map(b)) => {
                a.len() == b.len()
                    && a.iter().all(|(key, value)| {
                        b.iter().any(|(other_key, other_value)| {
                            key == other_key && value == other_value
                        })
                    })
            }
            (Atom(a), Atom(b)) => a == b,
            _ => false,
        }
    }
}
impl<N: Eq, A: Eq> Eq for ProductValue<N, A> {}

/// Supplies the original constructor product and rebuilds the same concrete
/// kind, including extra constructor lists, metadata and mutable extra vars.
/// Implementations snapshot parser node fields before returning from `children`.
pub trait Rewritable {
    type Node: Clone + PartialEq;
    type Atom: Clone + PartialEq;
    type Error;
    fn children(
        &self,
        node: &Self::Node,
    ) -> Result<Vec<ProductValue<Self::Node, Self::Atom>>, Self::Error>;
    fn rebuild(
        &self,
        original: &Self::Node,
        children: Vec<ProductValue<Self::Node, Self::Atom>>,
    ) -> Result<Self::Node, Self::Error>;
    fn same_node(&self, a: &Self::Node, b: &Self::Node) -> bool;
    fn is_atomic(&self, _node: &Self::Node) -> bool {
        false
    }
    fn init_properties(&self, _node: &Self::Node) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// Upstream preserves the original object if its product children compare equal,
/// unless forced, and always preserves atomic singleton types.
pub fn with_children<R: Rewritable>(
    adapter: &R,
    original: &R::Node,
    children: Vec<ProductValue<R::Node, R::Atom>>,
    force: bool,
) -> Result<R::Node, R::Error> {
    if (!force && adapter.children(original)? == children) || adapter.is_atomic(original) {
        Ok(original.clone())
    } else {
        adapter.rebuild(original, children)
    }
}
