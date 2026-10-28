//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/config/package.scala
//!
//! Purpose:
//! Supply wildcard and version utilities.
//!
//! Planned Rust structure:
//! wildcardToRegex, VersionComparator and Version relational, equality and prefix
//! operators.
//!
//! Behavior to preserve:
//! Replacement order escapes dot and dollar and maps ? to .? and * to .*?; comparator
//! consumes integer dot components until one stops, while equality compares original
//! strings.
//!
//! Integration:
//! config and interfaces::decider::prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Exact Scanner integer token behavior and version wrapper API.
//!
//! Status: version/wildcard operations implemented for native ASCII version components; Java Scanner locale-specific integer forms remain a compatibility gap.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::{cmp::Ordering, fmt};

/// Deliberately does not escape other regex metacharacters: neither does upstream.
pub fn wildcard_to_regex(pattern: &str) -> String {
    pattern
        .replace('.', "\\.")
        .replace('?', ".?")
        .replace('*', ".*?")
        .replace('$', "\\$")
}

/// Compare dot-separated integer components, stopping at the first noninteger.
/// A remaining numeric component sorts after a finished/noninteger version.
pub fn compare_versions(left: &str, right: &str) -> Ordering {
    fn components(s: &str) -> impl Iterator<Item = &str> {
        // Scanner skips a delimiter at the beginning and does not yield a final empty token.
        s.strip_prefix('.').unwrap_or(s).split_terminator('.')
    }
    let (mut left, mut right) = (components(left), components(right));
    loop {
        let a = left.next().and_then(|s| s.parse::<i32>().ok());
        let b = right.next().and_then(|s| s.parse::<i32>().ok());
        match (a, b) {
            (Some(a), Some(b)) => match a.cmp(&b) {
                Ordering::Equal => {}
                order => return order,
            },
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (None, None) => return Ordering::Equal,
        }
    }
}

/// Raw spelling determines equality; numeric comparison is a separate source operation.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Version {
    pub version: String,
}
impl Version {
    pub fn new(version: impl Into<String>) -> Self {
        Self {
            version: version.into(),
        }
    }
    pub fn compare(&self, other: &Self) -> Ordering {
        compare_versions(&self.version, &other.version)
    }
    pub fn greater_than(&self, other: &Self) -> bool {
        self.compare(other).is_gt()
    }
    pub fn greater_or_equal(&self, other: &Self) -> bool {
        !self.compare(other).is_lt()
    }
    pub fn less_than(&self, other: &Self) -> bool {
        self.compare(other).is_lt()
    }
    pub fn less_or_equal(&self, other: &Self) -> bool {
        !self.compare(other).is_gt()
    }
    pub fn extends(&self, other: &Self) -> bool {
        self == other || self.version.starts_with(&format!("{}.", other.version))
    }
}
impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.version)
    }
}
