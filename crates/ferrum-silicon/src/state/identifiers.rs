// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

//! Silicon identifiers, ported from
//! <https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Identifiers.scala>.
//!
//! Status: identifier representation and fresh-name generation implemented. Sort-template
//! formatting currently supports the `%s` and `%%` forms used by Silicon itself.

use std::fmt;

use super::terms::Sort;

pub const DEFAULT_SEPARATOR: &str = "@";

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Identifier {
    Simple(String),
    Suffixed {
        prefix: Box<Identifier>,
        separator: String,
        suffix: String,
    },
    SortBased {
        template: String,
        sorts: Vec<Sort>,
    },
}

impl Identifier {
    pub fn new(name: impl Into<String>) -> Self {
        Self::Simple(name.into())
    }

    pub fn sort_based(template: impl Into<String>, sorts: Vec<Sort>) -> Self {
        Self::SortBased {
            template: template.into(),
            sorts,
        }
    }

    pub fn suffixed(
        prefix: Identifier,
        separator: impl Into<String>,
        suffix: impl Into<String>,
    ) -> Self {
        assert!(
            !matches!(prefix, Self::Suffixed { .. }),
            "a suffixed identifier cannot have a suffixed prefix"
        );
        Self::Suffixed {
            prefix: Box::new(prefix),
            separator: separator.into(),
            suffix: suffix.into(),
        }
    }

    pub fn name(&self) -> String {
        self.to_string()
    }

    pub fn rename(&self, f: &impl Fn(&str) -> String) -> Self {
        match self {
            Self::Simple(name) => Self::Simple(f(name)),
            Self::Suffixed {
                prefix,
                separator,
                suffix,
            } => Self::suffixed(prefix.rename(f), separator.clone(), suffix.clone()),
            Self::SortBased { template, sorts } => Self::sort_based(f(template), sorts.clone()),
        }
    }

    pub fn with_suffix(&self, suffix: impl Into<String>) -> Self {
        self.with_separator_suffix(DEFAULT_SEPARATOR, suffix)
    }

    pub fn with_separator_suffix(
        &self,
        separator: impl Into<String>,
        suffix: impl Into<String>,
    ) -> Self {
        let prefix = match self {
            Self::Suffixed { prefix, .. } => (**prefix).clone(),
            other => other.clone(),
        };
        Self::suffixed(prefix, separator, suffix)
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Simple(name) => f.write_str(name),
            Self::Suffixed {
                prefix,
                separator,
                suffix,
            } => write!(f, "{prefix}{separator}{suffix}"),
            Self::SortBased { template, sorts } => {
                let mut chars = template.chars();
                let mut sorts = sorts.iter();
                while let Some(c) = chars.next() {
                    if c != '%' {
                        write!(f, "{c}")?;
                        continue;
                    }
                    match chars.next() {
                        Some('%') => f.write_str("%")?,
                        Some('s') => write!(f, "{}", sorts.next().ok_or(fmt::Error)?)?,
                        _ => return Err(fmt::Error),
                    }
                }
                Ok(())
            }
        }
    }
}

pub trait IdentifierFactory {
    fn separator(&self) -> &str;
    fn fresh(&mut self, name: &str) -> Identifier;
}

#[derive(Clone, Debug)]
pub struct DefaultIdentifierFactory {
    namespace: String,
    next: i32,
}

impl DefaultIdentifierFactory {
    pub fn new(namespace: impl Into<String>) -> Self {
        Self {
            namespace: namespace.into(),
            next: 0,
        }
    }
    pub fn start(&mut self) {}
    pub fn reset(&mut self) {
        self.next = 0;
    }
    pub fn stop(&mut self) {}
}

impl IdentifierFactory for DefaultIdentifierFactory {
    fn separator(&self) -> &str {
        DEFAULT_SEPARATOR
    }
    fn fresh(&mut self, name: &str) -> Identifier {
        let current = self.next;
        self.next = self.next.wrapping_add(1);
        Identifier::suffixed(
            Identifier::new(name),
            DEFAULT_SEPARATOR,
            format!("{current}@{}", self.namespace),
        )
    }
}
