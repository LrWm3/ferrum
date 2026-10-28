//! Reading and emitting SMT-LIB preambles.
//!
//! Port of [`SMTLib2PreambleReader.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/SMTLib2PreambleReader.scala).
//! Status: implemented; shared prover and resource integration remains pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::io;
use std::path::{Path, PathBuf};

use crate::interfaces::preamble::{PreambleReader, ResourceProvider};

/// Preambles embedded from the pinned upstream resources.
#[derive(Clone, Copy, Debug, Default)]
pub struct BundledResources;
impl ResourceProvider for BundledResources {
    fn read_resource(&self, name: &str) -> io::Result<String> {
        crate::resources::bundled::get(name)
            .map(str::to_owned)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::NotFound,
                    format!("cannot read preamble resource {name}"),
                )
            })
    }
}

/// Filesystem-backed provider for copied upstream resources.
pub struct DirectoryResources {
    root: PathBuf,
}
impl DirectoryResources {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }
    pub fn root(&self) -> &Path {
        &self.root
    }
}
impl ResourceProvider for DirectoryResources {
    fn read_resource(&self, name: &str) -> io::Result<String> {
        std::fs::read_to_string(self.root.join(name.trim_start_matches('/')))
    }
}

pub struct SmtLib2PreambleReader<R> {
    resources: R,
}
impl<R> SmtLib2PreambleReader<R> {
    pub fn new(resources: R) -> Self {
        Self { resources }
    }
}
impl Default for SmtLib2PreambleReader<BundledResources> {
    fn default() -> Self {
        Self::new(BundledResources)
    }
}
impl<R: ResourceProvider> PreambleReader for SmtLib2PreambleReader<R> {
    /// Remove blank/comment lines and join indented continuations to their command.
    fn read_preamble(&self, resource: &str) -> io::Result<Vec<String>> {
        let source = self.resources.read_resource(resource)?;
        let mut commands: Vec<String> = Vec::new();
        for line in source.lines().filter(|line| {
            let trimmed = line.trim();
            !trimmed.is_empty() && !trimmed.starts_with(';')
        }) {
            if (line.starts_with('\t') || line.starts_with("  ")) && !commands.is_empty() {
                let last = commands.last_mut().expect("nonempty commands");
                last.push('\n');
                last.push_str(line);
            } else {
                commands.push(line.to_owned());
            }
        }
        Ok(commands)
    }

    /// Apply literal substitutions sequentially, in the supplied order.
    fn read_parametric_preamble(
        &self,
        resource: &str,
        substitutions: &[(String, String)],
    ) -> io::Result<Vec<String>> {
        Ok(self
            .read_preamble(resource)?
            .into_iter()
            .map(|line| {
                substitutions
                    .iter()
                    .fold(line, |line, (from, to)| line.replace(from, to))
            })
            .collect())
    }
}
