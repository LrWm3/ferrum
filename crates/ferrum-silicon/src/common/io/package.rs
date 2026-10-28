//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/io/package.scala
//!
//! Purpose:
//! Provide file writing and unique filename utilities.
//!
//! Planned Rust structure:
//! toFile, PrintWriter and makeFilenameUnique create parents, write or append and select a
//! path.
//!
//! Behavior to preserve:
//! Unique naming checks existence and increments a decimal suffix; extension separator
//! remains even for empty extension; target directory must exist and be a directory.
//!
//! Integration:
//! logging, prover and reporting file output.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Native I/O error mapping and race behavior.
//!
//! Status: implemented; integration and broad differential checks remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::path::{Path, PathBuf};

// The same native writer preserves buffering, parent creation and optional line flushing.
pub use ferrum_silver::utility::common::{PrintWriter, print_writer, to_file};

/// Find the first unused path, preserving the source trailing dot for empty extensions.
/// This does not create the file and has the same check/use race as the source helper.
pub fn make_filename_unique(
    file: &Path,
    target_directory: Option<&Path>,
    new_extension: Option<&str>,
) -> PathBuf {
    if let Some(directory) = target_directory {
        assert!(directory.is_dir(), "expected a target directory");
    }
    // FilenameUtils recognizes both separator spellings, independently of host platform.
    let name = file.to_string_lossy();
    let split = name.rfind(['/', '\\']).map_or(0, |index| index + 1);
    let filename = &name[split..];
    let (base, extension) = filename.rsplit_once('.').unwrap_or((filename, ""));
    let directory = target_directory
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from(&name[..split]));
    let extension = new_extension.unwrap_or(extension);
    let mut counter = 0_i64;
    loop {
        let stem = if counter == 0 {
            base.to_owned()
        } else {
            format!("{base}{counter}")
        };
        let candidate = directory.join(format!("{stem}.{extension}"));
        if !candidate.exists() {
            return candidate;
        }
        counter = counter.wrapping_add(1);
    }
}
