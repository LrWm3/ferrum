//! Generic ordered tree visitors and reductions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Visitor.scala
//! Status: partial. Generic operations are implemented; AST and parser child providers are
//! being connected separately. Providers may return a typed error for unsupported extensions.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

/// Visit in preorder. Child providers return owned handles, so mutable graph locks
/// need not be held during visitor callbacks.
pub fn visit<N, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N),
) -> Result<(), E> {
    f(node);
    for child in subs(node)? {
        visit(&child, subs, f)?;
    }
    Ok(())
}

pub fn visit_with_context<N, C: Clone, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    context: C,
    f: &mut impl FnMut(&N, &C) -> Option<C>,
) -> Result<(), E> {
    let next = f(node, &context).unwrap_or(context);
    for child in subs(node)? {
        visit_with_context(&child, subs, next.clone(), f)?;
    }
    Ok(())
}

/// A matching callback takes responsibility for descending into the node.
pub fn visit_with_context_manually<N, C: Clone, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    context: C,
    f: &mut impl FnMut(&N, &C) -> bool,
) -> Result<(), E> {
    if !f(node, &context) {
        for child in subs(node)? {
            visit_with_context_manually(&child, subs, context.clone(), f)?;
        }
    }
    Ok(())
}

pub fn visit_before_after<N, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    before: &mut impl FnMut(&N),
    after: &mut impl FnMut(&N),
) -> Result<(), E> {
    before(node);
    for child in subs(node)? {
        visit_before_after(&child, subs, before, after)?;
    }
    after(node);
    Ok(())
}

pub fn visit_opt<N, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    before: &mut impl FnMut(&N) -> bool,
    after: &mut impl FnMut(&N),
) -> Result<(), E> {
    if before(node) {
        for child in subs(node)? {
            visit_opt(&child, subs, before, after)?;
        }
    }
    after(node);
    Ok(())
}

pub fn find<N, R, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N) -> Option<R>,
) -> Result<Option<R>, E> {
    if let Some(result) = f(node) {
        return Ok(Some(result));
    }
    for child in subs(node)? {
        if let Some(result) = find(&child, subs, f)? {
            return Ok(Some(result));
        }
    }
    Ok(None)
}

pub fn exists_defined<N, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N) -> bool,
) -> Result<bool, E> {
    Ok(find(node, subs, &mut |n| f(n).then_some(()))?.is_some())
}

pub fn has_subnode<N: PartialEq, E>(
    parent: &N,
    target: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
) -> Result<bool, E> {
    exists_defined(parent, subs, &mut |found| {
        found == target && found != parent
    })
}

/// Callback execution is bottom-up; results are assembled parent-first.
pub fn deep_collect<N, R, E>(
    nodes: &[N],
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N) -> Option<R>,
) -> Result<Vec<R>, E> {
    let mut results = Vec::new();
    for node in nodes {
        let children = subs(node)?;
        let mut descendants = deep_collect(&children, subs, f)?;
        if let Some(value) = f(node) {
            results.push(value);
        }
        results.append(&mut descendants);
    }
    Ok(results)
}

pub fn shallow_collect<N, R, E>(
    nodes: &[N],
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N) -> Option<R>,
) -> Result<Vec<R>, E> {
    let mut result = Vec::new();
    for node in nodes {
        if let Some(value) = f(node) {
            result.push(value);
        } else {
            result.extend(shallow_collect(&subs(node)?, subs, f)?);
        }
    }
    Ok(result)
}

pub fn reduce_tree<N, R, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    f: &mut impl FnMut(&N, Vec<R>) -> R,
) -> Result<R, E> {
    let children = subs(node)?
        .iter()
        .map(|child| reduce_tree(child, subs, f))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(f(node, children))
}

pub fn reduce_with_context<N, C: Clone, R, E>(
    node: &N,
    subs: &impl Fn(&N) -> Result<Vec<N>, E>,
    context: C,
    enter: &mut impl FnMut(&N, &C) -> C,
    combine: &mut impl FnMut(&N, &C, Vec<R>) -> R,
) -> Result<R, E> {
    let next = enter(node, &context);
    let children = subs(node)?
        .iter()
        .map(|child| reduce_with_context(child, subs, next.clone(), enter, combine))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(combine(node, &context, children))
}
