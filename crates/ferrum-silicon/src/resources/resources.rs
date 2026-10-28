//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/Resources.scala
//!
//! Purpose:
//! Map resource categories to property descriptions.
//!
//! Planned Rust structure:
//! Port ResourceID, BaseID, PredicateID, FieldID, MagicWandID and resourceDescriptions registry.
//!
//! Behavior to preserve:
//! Keep predicate and field as base resources, wand separate, and map each to its matching
//! description.
//!
//! Integration:
//! resources::resource_descriptions; state chunks and resource interpreters.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for enum and context ownership.
//!
//! Open decisions:
//! Agree on resource IDs with state and chunk interfaces.
//!
//! Status: resource IDs and property-description registry implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// Resource categories. Field and predicate are the source's `BaseID` cases;
/// magic wands form a separate resource category.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResourceId {
    Field,
    Predicate,
    MagicWand,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BaseId {
    Field,
    Predicate,
}
impl From<BaseId> for ResourceId {
    fn from(id: BaseId) -> Self {
        match id {
            BaseId::Field => Self::Field,
            BaseId::Predicate => Self::Predicate,
        }
    }
}
impl ResourceId {
    pub fn description(self) -> super::resource_descriptions::ResourceDescription {
        use super::resource_descriptions::ResourceDescription;
        match self {
            Self::Field => ResourceDescription::Field,
            Self::Predicate => ResourceDescription::Predicate,
            Self::MagicWand => ResourceDescription::MagicWand,
        }
    }
}
