//! Port plan: Carry project names for shared test infrastructure.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/testing/ProjectInfo.scala
//!
//! Purpose:
//! Carry project names for shared test infrastructure.
//!
//! Planned Rust structure:
//! ProjectInfo.projectNames, fullName and update.
//!
//! Behavior to preserve:
//! fullName joins names with hyphens; update prepends a new name and returns a new instance.
//!
//! Integration:
//! testing harness and downstream backend suite setup.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Agree on test harness configuration and naming with upstream suite ports.
//!
//! Status: implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectInfo {
    pub project_names: Vec<String>,
    pub full_name: String,
}
impl ProjectInfo {
    pub fn new(project_names: Vec<String>) -> Self {
        let full_name = project_names.join("-");
        Self {
            project_names,
            full_name,
        }
    }
    pub fn update(&self, project_name: impl Into<String>) -> Self {
        let mut names = Vec::with_capacity(self.project_names.len() + 1);
        names.push(project_name.into());
        names.extend(self.project_names.iter().cloned());
        Self::new(names)
    }
}
