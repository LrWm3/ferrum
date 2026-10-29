//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/NonQuantifiedPropertyInterpreter.scala
//!
//! Purpose:
//! Instantiate resource properties over ordinary and singleton quantified heap chunks.
//!
//! Planned Rust structure:
//! Port NonQuantifiedPropertyInterpreter, placeholder Info map, chunk/resource entry points,
//! accessors, solver Check and recursive ForEach.
//!
//! Behavior to preserve:
//! Select nonquantified and singleton quantified chunks, substitute singleton arguments in
//! permissions/values. ForEach groups by resource and chunk ID, enumerates distinct chunk
//! identities, conjoins results; reject ForEach when This is bound. Check uses decider with
//! configured timeout and chooses one branch. Preserve debug expressions and traversal order.
//!
//! Integration:
//! resources::property_interpreter, state chunk interfaces, verifier::verifier and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, solver access and debug metadata.
//!
//! Open decisions:
//! Agree on heap iteration, reference identity and singleton chunk handling with state and
//! decider.
//!
//! Status: partial; nonquantified and singleton-quantified term interpretation implemented.
//! Debug-expression construction remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property::Property;
use super::property_expressions::{BooleanExpression, ChunkPlaceholder};
use super::property_interpreter::{PropertyContext, PropertyError, PropertyInterpreter};
use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
use crate::resources::resources::ResourceId;
use crate::state::chunks::{Chunk, ChunkIdentifier};
use crate::state::terms::{Term, TermFactory, UnsupportedTriggerTransform};
use std::collections::HashMap;

#[derive(Debug)]
pub enum NonQuantifiedError<E> {
    Solver(E),
    MissingChunk,
    ForEachWithThis,
    UnsupportedChunk,
    Transform(UnsupportedTriggerTransform),
    ZeroDenominator,
    InvalidQuantifier,
    MissingDebugExpression,
    DebugSubstitution,
}
fn identity(c: &Chunk) -> Option<(ResourceId, ChunkIdentifier)> {
    match c {
        Chunk::Basic(c) => Some((c.resource_id(), c.identifier())),
        Chunk::MagicWand(c) => Some((c.resource_id(), c.identifier())),
        Chunk::QuantifiedField(c) if c.singleton_arguments().is_some() => {
            Some((c.resource_id(), c.identifier()))
        }
        Chunk::QuantifiedPredicate(c) if c.singleton_arguments().is_some() => {
            Some((c.resource_id(), c.identifier()))
        }
        Chunk::QuantifiedMagicWand(c) if c.singleton_arguments().is_some() => {
            Some((c.resource_id(), c.identifier()))
        }
        _ => None,
    }
}
struct Context<'a, 'h, F> {
    factory: &'a TermFactory,
    heap: &'h [&'h Chunk],
    resource: ResourceId,
    bindings: HashMap<ChunkPlaceholder, &'h Chunk>,
    check: &'a mut F,
}
impl<'a, 'h, F, E> Context<'a, 'h, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    fn get(&self, c: &ChunkPlaceholder) -> Result<&'h Chunk, NonQuantifiedError<E>> {
        self.bindings
            .get(c)
            .copied()
            .ok_or(NonQuantifiedError::MissingChunk)
    }
    fn singleton<Q: QuantifiedChunk>(
        &self,
        c: &Q,
        args: Vec<Term>,
    ) -> Result<Term, NonQuantifiedError<E>> {
        let replacements = c
            .quantified_vars(self.factory)
            .into_iter()
            .zip(args)
            .collect();
        self.factory
            .replace(&c.permission(self.factory), &replacements)
            .map_err(NonQuantifiedError::Transform)
    }
    fn permutations(
        &mut self,
        chunks: &[&'h Chunk],
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<Term, PropertyError<NonQuantifiedError<E>>> {
        let mut results = Vec::new();
        for chunk in chunks {
            if self
                .bindings
                .values()
                .any(|existing| std::ptr::eq(*existing, *chunk))
            {
                continue;
            }
            let old = self.bindings.insert(vars[0].clone(), *chunk);
            let result = if vars.len() == 1 {
                PropertyInterpreter {
                    factory: self.factory,
                    context: &mut *self,
                }
                .boolean(body)
            } else {
                self.permutations(chunks, &vars[1..], body)
            };
            if let Some(old) = old {
                self.bindings.insert(vars[0].clone(), old);
            } else {
                self.bindings.remove(&vars[0]);
            }
            results.push(result?);
        }
        Ok(self.factory.and(results))
    }
}
impl<F, E> PropertyContext for &mut Context<'_, '_, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    type Error = NonQuantifiedError<E>;
    fn permission(&mut self, key: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.permission(self.factory)),
            Chunk::MagicWand(c) => Ok(c.permission(self.factory)),
            Chunk::QuantifiedField(c) => self.singleton(
                c,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            ),
            Chunk::QuantifiedPredicate(c) => self.singleton(
                c,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?
                    .to_vec(),
            ),
            Chunk::QuantifiedMagicWand(c) => self.singleton(
                c,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?
                    .to_vec(),
            ),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn value(&mut self, key: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.snap_ref().clone()),
            Chunk::MagicWand(c) => Ok(c.snap_ref().clone()),
            Chunk::QuantifiedField(c) => Ok(c.value_at(
                self.factory,
                &c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            )),
            Chunk::QuantifiedPredicate(c) => Ok(c.value_at(
                self.factory,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            )),
            Chunk::QuantifiedMagicWand(c) => Ok(c.value_at(
                self.factory,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            )),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn arguments(&mut self, key: &ChunkPlaceholder) -> Result<Vec<Term>, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.args_ref().clone()),
            Chunk::MagicWand(c) => Ok(c.args_ref().clone()),
            Chunk::QuantifiedField(c) => c
                .singleton_arguments()
                .ok_or(NonQuantifiedError::UnsupportedChunk),
            Chunk::QuantifiedPredicate(c) => Ok(c
                .singleton_arguments()
                .ok_or(NonQuantifiedError::UnsupportedChunk)?
                .to_vec()),
            Chunk::QuantifiedMagicWand(c) => Ok(c
                .singleton_arguments()
                .ok_or(NonQuantifiedError::UnsupportedChunk)?
                .to_vec()),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn check(&mut self, term: &Term) -> Result<Option<bool>, Self::Error> {
        (self.check)(term)
            .map(Some)
            .map_err(NonQuantifiedError::Solver)
    }
    fn for_each(
        &mut self,
        factory: &TermFactory,
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<Term, PropertyError<Self::Error>> {
        if self.bindings.contains_key(&ChunkPlaceholder::This) {
            return Err(PropertyError::Context(NonQuantifiedError::ForEachWithThis));
        }
        let mut groups: Vec<(ChunkIdentifier, Vec<&Chunk>)> = Vec::new();
        for chunk in self.heap {
            if let Some((resource, id)) = identity(chunk) {
                if resource == self.resource {
                    if let Some((_, group)) = groups.iter_mut().find(|(key, _)| *key == id) {
                        group.push(chunk);
                    } else {
                        groups.push((id, vec![chunk]));
                    }
                }
            }
        }
        let mut result = Vec::new();
        for (_, chunks) in groups {
            result.push(self.permutations(&chunks, vars, body)?);
        }
        Ok(factory.and(result))
    }
}
impl<'a, 'h, F, E> Context<'a, 'h, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    fn permutations_debug(
        &mut self,
        chunks: &[&'h Chunk],
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<super::debug_property_interpreter::Pair, PropertyError<NonQuantifiedError<E>>> {
        let mut terms = Vec::new();
        let mut exps = Vec::new();
        for chunk in chunks {
            if self
                .bindings
                .values()
                .any(|existing| std::ptr::eq(*existing, *chunk))
            {
                continue;
            }
            let old = self.bindings.insert(vars[0].clone(), *chunk);
            let result = if vars.len() == 1 {
                super::debug_property_interpreter::DebugPropertyInterpreter {
                    factory: self.factory,
                    context: &mut *self,
                }
                .boolean(body)
            } else {
                self.permutations_debug(chunks, &vars[1..], body)
            };
            if let Some(old) = old {
                self.bindings.insert(vars[0].clone(), old);
            } else {
                self.bindings.remove(&vars[0]);
            }
            let (term, exp) = result?;
            terms.push(term);
            exps.push(exp);
        }
        Ok((
            self.factory.and(terms),
            crate::utils::ast::big_and(
                exps,
                |e| e,
                ferrum_silver::ast::position::Position::NoPosition,
            ),
        ))
    }
}
impl<F, E> super::debug_property_interpreter::DebugPropertyContext for &mut Context<'_, '_, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    type Error = NonQuantifiedError<E>;
    fn permission(
        &mut self,
        key: &ChunkPlaceholder,
    ) -> Result<super::debug_property_interpreter::Pair, Self::Error> {
        use crate::interfaces::state::chunks::GeneralChunk;
        let chunk = self.get(key)?;
        let term = PropertyContext::permission(self, key)?;
        let exp = match chunk {
            Chunk::Basic(c) => c.permission_exp(),
            Chunk::MagicWand(c) => c.permission_exp(),
            Chunk::QuantifiedField(c) => {
                let exp = c
                    .permission_exp()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let vars = c
                    .quantified_var_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let args = c
                    .singleton_argument_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                Some(
                    crate::utils::ast::replace_vars_in_exp(
                        &exp,
                        &vars.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
                        &args,
                    )
                    .map_err(|_| NonQuantifiedError::DebugSubstitution)?,
                )
            }
            Chunk::QuantifiedPredicate(c) => {
                let exp = c
                    .permission_exp()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let vars = c
                    .quantified_var_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let args = c
                    .singleton_argument_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                Some(
                    crate::utils::ast::replace_vars_in_exp(
                        &exp,
                        &vars.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
                        args,
                    )
                    .map_err(|_| NonQuantifiedError::DebugSubstitution)?,
                )
            }
            Chunk::QuantifiedMagicWand(c) => {
                let exp = c
                    .permission_exp()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let vars = c
                    .quantified_var_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                let args = c
                    .singleton_argument_exps()
                    .ok_or(NonQuantifiedError::MissingDebugExpression)?;
                Some(
                    crate::utils::ast::replace_vars_in_exp(
                        &exp,
                        &vars.iter().map(|v| v.name.clone()).collect::<Vec<_>>(),
                        args,
                    )
                    .map_err(|_| NonQuantifiedError::DebugSubstitution)?,
                )
            }
            _ => return Err(NonQuantifiedError::UnsupportedChunk),
        }
        .ok_or(NonQuantifiedError::MissingDebugExpression)?;
        Ok((term, exp))
    }
    fn value(
        &mut self,
        key: &ChunkPlaceholder,
    ) -> Result<super::debug_property_interpreter::Pair, Self::Error> {
        let term = PropertyContext::value(self, key)?;
        let (_, args) =
            super::debug_property_interpreter::DebugPropertyContext::arguments(self, key)?;
        Ok((
            term,
            args.into_iter()
                .next()
                .ok_or(NonQuantifiedError::MissingDebugExpression)?,
        ))
    }
    fn arguments(
        &mut self,
        key: &ChunkPlaceholder,
    ) -> Result<(Vec<Term>, Vec<ferrum_silver::ast::expression::Exp>), Self::Error> {
        use crate::interfaces::state::chunks::NonQuantifiedChunk;
        let terms = PropertyContext::arguments(self, key)?;
        let args = match self.get(key)? {
            Chunk::Basic(c) => c.args_exp().map(|v| v.to_vec()),
            Chunk::MagicWand(c) => c.args_exp().map(|v| v.to_vec()),
            Chunk::QuantifiedField(c) => c.singleton_argument_exps(),
            Chunk::QuantifiedPredicate(c) => c.singleton_argument_exps().map(|v| v.to_vec()),
            Chunk::QuantifiedMagicWand(c) => c.singleton_argument_exps().map(|v| v.to_vec()),
            _ => return Err(NonQuantifiedError::UnsupportedChunk),
        }
        .ok_or(NonQuantifiedError::MissingDebugExpression)?;
        Ok((terms, args))
    }
    fn check(&mut self, term: &Term) -> Result<Option<bool>, Self::Error> {
        PropertyContext::check(self, term)
    }
    fn for_each(
        &mut self,
        factory: &TermFactory,
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<super::debug_property_interpreter::Pair, PropertyError<Self::Error>> {
        if self.bindings.contains_key(&ChunkPlaceholder::This) {
            return Err(PropertyError::Context(NonQuantifiedError::ForEachWithThis));
        }
        let mut groups: Vec<(ChunkIdentifier, Vec<&Chunk>)> = Vec::new();
        for chunk in self.heap {
            if let Some((resource, id)) = identity(chunk) {
                if resource == self.resource {
                    if let Some((_, group)) = groups.iter_mut().find(|(key, _)| *key == id) {
                        group.push(chunk);
                    } else {
                        groups.push((id, vec![chunk]));
                    }
                }
            }
        }
        let mut terms = Vec::new();
        let mut exps = Vec::new();
        for (_, chunks) in groups {
            let (term, exp) = self.permutations_debug(&chunks, vars, body)?;
            terms.push(term);
            exps.push(exp);
        }
        Ok((
            factory.and(terms),
            crate::utils::ast::big_and(
                exps,
                |e| e,
                ferrum_silver::ast::position::Position::NoPosition,
            ),
        ))
    }
}
/// Interpret a property with its source debug expression in the same traversal.
pub fn build_debug<E>(
    factory: &TermFactory,
    heap: &[&Chunk],
    resource: ResourceId,
    this: Option<&Chunk>,
    property: &Property,
    mut check: impl FnMut(&Term) -> Result<bool, E>,
) -> Result<super::debug_property_interpreter::Pair, PropertyError<NonQuantifiedError<E>>> {
    let mut bindings = HashMap::new();
    if let Some(chunk) = this {
        bindings.insert(ChunkPlaceholder::This, chunk);
    }
    let mut context = Context {
        factory,
        heap,
        resource,
        bindings,
        check: &mut check,
    };
    super::debug_property_interpreter::DebugPropertyInterpreter {
        factory,
        context: &mut context,
    }
    .boolean(&property.expression)
}
/// Evaluate a property against a resource group or a particular chunk. Debug expressions
/// are deliberately not fabricated: the debug-aware source counterpart is still pending.
pub fn build<E>(
    factory: &TermFactory,
    heap: &[&Chunk],
    resource: ResourceId,
    this: Option<&Chunk>,
    property: &Property,
    mut check: impl FnMut(&Term) -> Result<bool, E>,
) -> Result<Term, PropertyError<NonQuantifiedError<E>>> {
    let mut bindings = HashMap::new();
    if let Some(chunk) = this {
        bindings.insert(ChunkPlaceholder::This, chunk);
    }
    let mut context = Context {
        factory,
        heap,
        resource,
        bindings,
        check: &mut check,
    };
    PropertyInterpreter {
        factory,
        context: &mut context,
    }
    .boolean(&property.expression)
}

#[cfg(test)]
mod debug_tests {
    use super::*;
    use crate::resources::property_expressions::BooleanExpression as B;
    use crate::resources::resources::BaseId;
    use crate::state::chunks::{BasicChunk, BasicChunkIdentifier};
    use crate::state::terms::{TermKind, TermOptions};
    #[test]
    fn foreach_checks_each_distinct_chunk_pair_once() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let make = |n| {
            Chunk::Basic(BasicChunk::new(
                BaseId::Field,
                BasicChunkIdentifier("f".into()),
                vec![f.null()],
                None,
                f.int_literal(n),
                None,
                f.full_perm(),
                None,
                None,
            ))
        };
        let first = make(1);
        let second = make(2);
        let heap = [&first, &second];
        let a = ChunkPlaceholder::variable("a").unwrap();
        let b = ChunkPlaceholder::variable("b").unwrap();
        let body = B::Check(
            Box::new(B::Literal(true)),
            Box::new(B::Literal(true)),
            Box::new(B::Literal(false)),
        );
        let property = Property::new(B::for_each(vec![a, b], body).unwrap(), "pairs", "").unwrap();
        let mut checks = Vec::new();
        let (term, _) = build_debug(&f, &heap, ResourceId::Field, None, &property, |term| {
            checks.push(term.clone());
            Ok::<_, ()>(true)
        })
        .unwrap();
        assert!(matches!(term.kind(), TermKind::True));
        assert_eq!(checks.len(), 2);
        assert!(
            checks
                .iter()
                .all(|term| matches!(term.kind(), TermKind::True))
        );
    }
}

#[cfg(test)]
mod debug_wand_tests {
    use super::*;
    use crate::resources::property_expressions::{
        ArgumentExpression as A, BooleanExpression as B, PermissionExpression as P,
        ValueExpression as V,
    };
    use crate::state::chunks::{MagicWandIdentifier, QuantifiedMagicWandChunk};
    use crate::state::identifiers::Identifier;
    use crate::state::terms::{Sort, TermKind, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
    };
    #[test]
    fn singleton_quantified_wand_debug_properties_use_real_chunk_operands() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let lit = |kind| Exp::new(kind, Metadata::default());
        let wand = lit(ExpKind::MagicWand(
            lit(ExpKind::TrueLit),
            lit(ExpKind::FalseLit),
        ));
        let qvar = factory.var(Identifier::new("r"), Sort::Ref, false);
        let qdecl = ferrum_silver::ast::program::LocalVarDecl::new(
            "r".into(),
            ferrum_silver::ast::r#type::Type::Ref,
            Metadata::default(),
        );
        let chunk = Chunk::QuantifiedMagicWand(QuantifiedMagicWandChunk::new(
            MagicWandIdentifier::from_structure_index(wand, 0),
            vec![qvar],
            Some(vec![qdecl]),
            factory.var(
                Identifier::new("w"),
                Sort::PredicateSnapFunction {
                    codomain: Box::new(Sort::MagicWandSnapFunction),
                    predicate_name: "w".into(),
                },
                false,
            ),
            factory.boolean(true),
            factory.full_perm(),
            Some(lit(ExpKind::FullPerm)),
            vec![],
            Some(vec![factory.null()]),
            Some(vec![lit(ExpKind::NullLit)]),
            None,
            vec![],
        ));
        let heap = [&chunk];
        for expression in [
            B::EqualsPermission(
                P::Access(ChunkPlaceholder::This),
                P::Literal(1.into(), 1.into()),
            ),
            B::EqualsArgument(A::Access(ChunkPlaceholder::This), A::Null),
            B::EqualsValue(
                V::Access(ChunkPlaceholder::This),
                V::Access(ChunkPlaceholder::This),
            ),
        ] {
            let property = Property::new(expression, "wand", "").unwrap();
            let (term, exp) = build_debug(
                &factory,
                &heap,
                ResourceId::MagicWand,
                Some(&chunk),
                &property,
                |_| Ok::<_, ()>(true),
            )
            .unwrap();
            assert!(matches!(term.kind(), TermKind::True));
            assert!(matches!(
                exp.kind(),
                ExpKind::EqCmp(..) | ExpKind::TrueLit | ExpKind::And(..)
            ));
        }
    }
}
