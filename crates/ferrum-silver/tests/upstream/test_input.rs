//! Port plan: TestInput.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/TestInput.scala
//!
//! Purpose:
//! Port the upstream TestInput.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestInput, DefaultTestInput and filename grouping/tag creation.
//!
//! Behavior to preserve:
//! Group files matching <base>_file<number> in same directory sorted numerically; derive canonical
//! name and tags from full/relative paths, filename, stem and parent prefixes. file returns first
//! entry; preserve source parsing and failure behavior for malformed numeric suffixes.
//!
//! Integration:
//! resource_based_test_suite, annotation_based_test_suite and test annotations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Agree on platform path handling, resource discovery and tagging semantics.
//!
//! Status: partial; grouping and tag derivation implemented. Suite integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use regex::Regex;
use std::path::{Path, PathBuf};

pub trait TestInput {
    fn name(&self) -> &str;
    fn prefix(&self) -> &str;
    fn files(&self) -> &[PathBuf];
    fn tags(&self) -> &[String];
    fn file(&self) -> Option<&Path> {
        self.files().first().map(PathBuf::as_path)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefaultTestInput {
    pub name: String,
    pub prefix: String,
    pub files: Vec<PathBuf>,
    pub tags: Vec<String>,
}
#[derive(Debug)]
pub enum InputError {
    Io(std::io::Error),
    MissingFilename,
    MissingParent,
    MissingExtension,
    InvalidFileNumber,
    InvalidUnicode,
}
impl DefaultTestInput {
    pub fn from_file(file: &Path, prefix: impl Into<String>) -> Result<Self, InputError> {
        let prefix = prefix.into();
        let filename = file
            .file_name()
            .ok_or(InputError::MissingFilename)?
            .to_str()
            .ok_or(InputError::InvalidUnicode)?;
        let path = file.to_str().ok_or(InputError::InvalidUnicode)?;
        let file_list = Regex::new(r"^(.*)_file[0-9]*.*$").expect("valid source regex");
        let name_part = file_list
            .captures(filename)
            .map(|c| c[1].to_string())
            .unwrap_or_else(|| filename.to_owned());
        let name = format!("{prefix}/{name_part}");
        let files = if let Some(captures) = file_list.captures(path) {
            let base = &captures[1];
            let matching = Regex::new(&format!(r"^{}_file([0-9]*).*$", regex::escape(base)))
                .expect("escaped file regex");
            let parent = file
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .ok_or(InputError::MissingParent)?;
            let mut found = Vec::new();
            for entry in std::fs::read_dir(parent).map_err(InputError::Io)? {
                let path = entry.map_err(InputError::Io)?.path();
                let text = path.to_str().ok_or(InputError::InvalidUnicode)?;
                if let Some(parts) = matching.captures(text) {
                    let index = parts[1]
                        .parse::<i32>()
                        .map_err(|_| InputError::InvalidFileNumber)?;
                    found.push((path, index));
                }
            }
            // Scala prepends directory entries before its stable numeric sort.
            found.reverse();
            found.sort_by_key(|(_, index)| *index);
            found.into_iter().map(|(file, _)| file).collect()
        } else {
            vec![file.to_owned()]
        };
        let dot = filename.rfind('.').ok_or(InputError::MissingExtension)?;
        let relative = format!("{prefix}/{filename}");
        let mut tags = vec![
            relative.clone(),
            path.to_owned(),
            filename.to_owned(),
            filename[..dot].to_owned(),
        ];
        let mut components = relative.split(['/', '\\']).collect::<Vec<_>>();
        components.pop();
        loop {
            tags.push(format!("{}/", components.join("/")));
            if components.pop().is_none() {
                break;
            }
        }
        Ok(Self {
            name,
            prefix,
            files,
            tags,
        })
    }
}
impl TestInput for DefaultTestInput {
    fn name(&self) -> &str {
        &self.name
    }
    fn prefix(&self) -> &str {
        &self.prefix
    }
    fn files(&self) -> &[PathBuf] {
        &self.files
    }
    fn tags(&self) -> &[String] {
        &self.tags
    }
}
