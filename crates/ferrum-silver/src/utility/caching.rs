//! Dependency collection for verifier cache keys.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Caching.scala
//! Status: partial; dependency collection, MD5 and normalized entity hashing are
//! implemented. Complete class naming and source-node rendering are supplied by callers.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::ExpKind,
    program::{Member, Method, Program},
    statement::StmtKind,
    utility::nodes::{Node, TraversalError, subnodes},
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DependencyError {
    Traversal(TraversalError),
    MissingFunction(String),
    MissingPredicate(String),
    MissingMethod(String),
}
impl From<TraversalError> for DependencyError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
fn is_hashable(n: &Node) -> bool {
    !matches!(n, Node::Program(_) | Node::Trigger(_))
}
fn mark_subtree(root: &Node, marker: &mut Vec<Node>) -> Result<(), DependencyError> {
    for child in subnodes(root)? {
        mark_subtree(&child, marker)?;
    }
    if is_hashable(root) && !marker.contains(root) {
        marker.push(root.clone());
    }
    Ok(())
}
/// Emulate deepCollect: children are evaluated before the callback, while returned
/// callback results precede the collected child results.
fn collect(
    root: &Node,
    callback: &mut impl FnMut(&Node) -> Result<Vec<Node>, DependencyError>,
) -> Result<Vec<Node>, DependencyError> {
    let mut children = Vec::new();
    for child in subnodes(root)? {
        children.extend(collect(&child, callback)?);
    }
    let mut own = callback(root)?;
    own.extend(children);
    Ok(own)
}
fn recursive_dependencies(
    program: &Program,
    roots: &[Node],
    marker: &mut Vec<Node>,
) -> Result<Vec<Node>, DependencyError> {
    let mut result = Vec::new();
    for root in roots {
        let mut callback = |node: &Node| -> Result<Vec<Node>, DependencyError> {
            match node {
                Node::Exp(exp) if matches!(exp.kind(), ExpKind::FuncApp(..)) => {
                    let ExpKind::FuncApp(name, _) = exp.kind() else {
                        unreachable!()
                    };
                    let f = program
                        .find_function_optionally(name)
                        .ok_or_else(|| DependencyError::MissingFunction(name.clone()))?;
                    let member = Node::Member(Member::Function(f.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = f
                        .pres
                        .iter()
                        .chain(&f.posts)
                        .chain(f.body.iter())
                        .cloned()
                        .map(Node::Exp)
                        .collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                Node::PredicateAccess(p) => {
                    let pred = program
                        .find_predicate_optionally(&p.predicate_name)
                        .ok_or_else(|| {
                            DependencyError::MissingPredicate(p.predicate_name.clone())
                        })?;
                    let member = Node::Member(Member::Predicate(pred.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = pred.body.iter().cloned().map(Node::Exp).collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                Node::Exp(exp) if matches!(exp.kind(), ExpKind::PredicateAccess(..)) => {
                    let ExpKind::PredicateAccess(p) = exp.kind() else {
                        unreachable!()
                    };
                    let pred = program
                        .find_predicate_optionally(&p.predicate_name)
                        .ok_or_else(|| {
                            DependencyError::MissingPredicate(p.predicate_name.clone())
                        })?;
                    let member = Node::Member(Member::Predicate(pred.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = pred.body.iter().cloned().map(Node::Exp).collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                _ => Ok(Vec::new()),
            }
        };
        result.extend(collect(root, &mut callback)?);
    }
    Ok(result)
}
/// The source marks the initial method and function/predicate subtrees, but deliberately
/// does not mark a called method when it visits its specification.
pub fn get_dependencies(program: &Program, method: &Method) -> Result<Vec<Node>, DependencyError> {
    let root = Node::Member(Member::Method(method.clone()));
    let mut marker = Vec::new();
    mark_subtree(&root, &mut marker)?;
    let mut out = vec![root];
    out.extend(
        program
            .domains
            .iter()
            .cloned()
            .map(|v| Node::Member(Member::Domain(v))),
    );
    out.extend(
        program
            .fields
            .iter()
            .cloned()
            .map(|v| Node::Member(Member::Field(v))),
    );
    let roots: Vec<Node> = method
        .pres
        .iter()
        .chain(&method.posts)
        .cloned()
        .map(Node::Exp)
        .chain(method.body.iter().cloned().map(Node::Stmt))
        .collect();
    for root in roots {
        let mut callback = |node: &Node| -> Result<Vec<Node>, DependencyError> {
            match node {
                Node::Stmt(s) if matches!(s.kind(), StmtKind::MethodCall { .. }) => {
                    let StmtKind::MethodCall { method_name, .. } = s.kind() else {
                        unreachable!()
                    };
                    let m = program
                        .find_method_optionally(method_name)
                        .ok_or_else(|| DependencyError::MissingMethod(method_name.clone()))?;
                    if marker.contains(&Node::Member(Member::Method(m.clone()))) {
                        return Ok(Vec::new());
                    }
                    let spec: Vec<_> = m
                        .formal_args
                        .iter()
                        .chain(&m.formal_returns)
                        .cloned()
                        .map(Node::LocalDecl)
                        .chain(m.pres.iter().chain(&m.posts).cloned().map(Node::Exp))
                        .collect();
                    let mut result = spec.clone();
                    result.extend(recursive_dependencies(program, &spec, &mut marker)?);
                    Ok(result)
                }
                Node::Exp(e)
                    if matches!(
                        e.kind(),
                        ExpKind::FuncApp(..) | ExpKind::PredicateAccess(..)
                    ) =>
                {
                    recursive_dependencies(program, std::slice::from_ref(node), &mut marker)
                }
                Node::PredicateAccess(_) => {
                    recursive_dependencies(program, std::slice::from_ref(node), &mut marker)
                }
                _ => Ok(Vec::new()),
            }
        };
        out.extend(collect(&root, &mut callback)?);
    }
    Ok(out)
}

/// Byte-level MD5 used by the source cache helper. This is a cache identifier,
/// not a cryptographic authentication primitive.
pub fn md5_digest(input: &[u8]) -> [u8; 16] {
    const S: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5,
        9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10,
        15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    const K: [u32; 64] = [
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613,
        0xfd469501, 0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193,
        0xa679438e, 0x49b40821, 0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d,
        0x02441453, 0xd8a1e681, 0xe7d3fbc8, 0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
        0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a, 0xfffa3942, 0x8771f681, 0x6d9d6122,
        0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70, 0x289b7ec6, 0xeaa127fa,
        0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665, 0xf4292244,
        0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb,
        0xeb86d391,
    ];
    let bit_len = (input.len() as u64).wrapping_mul(8);
    let mut bytes = input.to_vec();
    bytes.push(0x80);
    while bytes.len() % 64 != 56 {
        bytes.push(0);
    }
    bytes.extend_from_slice(&bit_len.to_le_bytes());
    let mut state = [0x67452301_u32, 0xefcdab89, 0x98badcfe, 0x10325476];
    for chunk in bytes.chunks_exact(64) {
        let mut words = [0_u32; 16];
        for (i, word) in words.iter_mut().enumerate() {
            *word = u32::from_le_bytes(chunk[i * 4..i * 4 + 4].try_into().expect("four-byte word"));
        }
        let [mut a, mut b, mut c, mut d] = state;
        for i in 0..64 {
            let (f, g) = if i < 16 {
                ((b & c) | (!b & d), i)
            } else if i < 32 {
                ((d & b) | (!d & c), (5 * i + 1) % 16)
            } else if i < 48 {
                (b ^ c ^ d, (3 * i + 5) % 16)
            } else {
                (c ^ (b | !d), (7 * i) % 16)
            };
            let next = b.wrapping_add(
                a.wrapping_add(f)
                    .wrapping_add(K[i])
                    .wrapping_add(words[g])
                    .rotate_left(S[i]),
            );
            a = d;
            d = c;
            c = b;
            b = next;
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d]) {
            *slot = slot.wrapping_add(value);
        }
    }
    let mut digest = [0_u8; 16];
    for (i, word) in state.iter().enumerate() {
        digest[i * 4..i * 4 + 4].copy_from_slice(&word.to_le_bytes());
    }
    digest
}

/// JVM source uses the platform default charset in both conversions, and decodes
/// digest bytes directly instead of hex-encoding them. These callbacks preserve
/// that platform-dependent boundary for non-UTF-8 JVMs.
pub fn build_hash_with_charset(
    value: &str,
    encode: &impl Fn(&str) -> Vec<u8>,
    decode: &impl Fn(&[u8]) -> String,
) -> String {
    decode(&md5_digest(&encode(value)))
}
/// Decode bytes with Java's UTF-8 replacement policy. Java replaces a complete
/// encoded surrogate as one malformed sequence; Rust's lossy decoder replaces
/// each of its bytes separately.
pub fn decode_java_utf8(mut bytes: &[u8]) -> String {
    let mut result = String::new();
    while !bytes.is_empty() {
        match std::str::from_utf8(bytes) {
            Ok(valid) => {
                result.push_str(valid);
                break;
            }
            Err(error) => {
                let valid = error.valid_up_to();
                result.push_str(
                    std::str::from_utf8(&bytes[..valid]).expect("validated UTF-8 prefix"),
                );
                bytes = &bytes[valid..];
                let malformed =
                    if bytes.len() >= 2 && bytes[0] == 0xed && (0xa0..=0xbf).contains(&bytes[1]) {
                        if bytes.len() >= 3 && (0x80..=0xbf).contains(&bytes[2]) {
                            3
                        } else {
                            2
                        }
                    } else {
                        error.error_len().unwrap_or(bytes.len())
                    };
                result.push('\u{fffd}');
                bytes = &bytes[malformed..];
            }
        }
    }
    result
}
/// UTF-8 JVM-compatible cache string (invalid digest bytes become replacements).
pub fn build_hash_utf8(value: &str) -> String {
    build_hash_with_charset(value, &|s| s.as_bytes().to_vec(), &|bytes| {
        decode_java_utf8(bytes)
    })
}

/// Normalize a domain by source pretty-print ordering, then hash exactly the
/// prefixed class name and normalized source rendering. The callbacks supply
/// source class names, complete rendering, and the JVM charset boundary.
pub fn compute_entity_hash<E>(
    prefix: &str,
    node: &Node,
    class_name: &impl Fn(&Node) -> Result<String, E>,
    render: &impl Fn(&Node) -> Result<String, E>,
    encode: &impl Fn(&str) -> Vec<u8>,
    decode: &impl Fn(&[u8]) -> String,
) -> Result<String, E> {
    let normalized = match node {
        Node::Member(Member::Domain(domain)) => {
            let mut functions = domain
                .functions
                .iter()
                .cloned()
                .map(|f| Ok((render(&Node::DomainFunc(f.clone()))?, f)))
                .collect::<Result<Vec<_>, E>>()?;
            let mut axioms = domain
                .axioms
                .iter()
                .cloned()
                .map(|a| Ok((render(&Node::DomainAxiom(a.clone()))?, a)))
                .collect::<Result<Vec<_>, E>>()?;
            functions.sort_by(|a, b| a.0.encode_utf16().cmp(b.0.encode_utf16()));
            axioms.sort_by(|a, b| a.0.encode_utf16().cmp(b.0.encode_utf16()));
            Node::Member(Member::Domain(domain.copy_with(|d| {
                d.functions = functions.into_iter().map(|(_, f)| f).collect();
                d.axioms = axioms.into_iter().map(|(_, a)| a).collect();
            })))
        }
        _ => node.clone(),
    };
    let text = format!(
        "{}_<{}>_{}",
        prefix,
        class_name(node)?,
        render(&normalized)?
    );
    Ok(build_hash_with_charset(&text, encode, decode))
}

#[cfg(test)]
mod cache_hash_tests {
    use super::*;
    #[test]
    fn md5_matches_standard_vectors() {
        fn hex(input: &[u8]) -> String {
            md5_digest(input)
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect()
        }
        assert_eq!(hex(b""), "d41d8cd98f00b204e9800998ecf8427e");
        assert_eq!(hex(b"abc"), "900150983cd24fb0d6963f7d28e17f72");
        assert_eq!(
            hex(
                b"12345678901234567890123456789012345678901234567890123456789012345678901234567890"
            ),
            "57edf4a22be3c955ac49da2e2107b67a"
        );
        assert_eq!(
            decode_java_utf8(&[0xed, 0xa0, 0x80, 0x80]),
            "\u{fffd}\u{fffd}"
        );
        assert_eq!(decode_java_utf8(&[0xed, 0xa0, b'A']), "\u{fffd}A");
        assert_eq!(
            hex(b"abcdefghijklmnopqrstuvwxyz"),
            "c3fcd3d76192e4007dfb496cca67e13b"
        );
    }
}
