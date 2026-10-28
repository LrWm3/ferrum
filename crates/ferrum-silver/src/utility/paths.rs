//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Paths.scala
//!
//! Purpose:
//! Provide path, resource URL and environment expansion helpers.
//!
//! Planned Rust structure:
//! Port Paths resolveEnvVars, pathFromResource, canonize and isInSubDirectory; replace JVM
//! resource filesystem management.
//!
//! Behavior to preserve:
//! Only substitute existing ${ENV} variables; support file, jar and resource schemes upstream,
//! retain resource filesystem lifetime/reuse, reject other schemes. Canonize joins relative paths
//! to working directory; directory containment walks parents, including equality.
//!
//! Integration:
//! Resource consumers and ast::utility file loading depend on accessible paths.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Decide native packaged-resource representation and lifetime with resource and file-loader
//! modules.
//!
//! Status: partially implemented; jar/resource resolution needs native resource integration.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::path::{Path, PathBuf};
use std::{env, io};

/// Substitute matches from the original input, using global replacement for each match as upstream.
pub fn resolve_env_vars(path: &str) -> String {
    let mut result = path.to_owned();
    let mut rest = path;
    while let Some(start) = rest.find("${") {
        rest = &rest[start + 2..];
        let Some(end) = rest.find('}') else { break };
        let key = &rest[..end];
        if !key.is_empty() {
            if let Ok(value) = env::var(key) {
                result = result.replace(&format!("${{{key}}}"), &value);
            }
        }
        rest = &rest[end + 1..];
    }
    result
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourcePathError {
    InvalidFileUrl,
    UnsupportedResourceScheme(String),
}

/// File URLs are decoded locally; archive and bundled-resource URLs need a native resolver.
pub fn path_from_resource(resource: &str) -> Result<PathBuf, ResourcePathError> {
    let Some((scheme, rest)) = resource.split_once(':') else {
        return Err(ResourcePathError::InvalidFileUrl);
    };
    if scheme != "file" {
        return Err(ResourcePathError::UnsupportedResourceScheme(
            scheme.to_owned(),
        ));
    }
    let path = if let Some(after) = rest.strip_prefix("//") {
        if !after.starts_with('/') {
            return Err(ResourcePathError::InvalidFileUrl);
        }
        after
    } else {
        rest
    };
    if !path.starts_with('/') || path.contains(['?', '#']) {
        return Err(ResourcePathError::InvalidFileUrl);
    }
    let mut decoded = Vec::with_capacity(path.len());
    let bytes = path.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            if i + 2 >= bytes.len() {
                return Err(ResourcePathError::InvalidFileUrl);
            }
            let hex = |c: u8| (c as char).to_digit(16);
            let (Some(a), Some(b)) = (hex(bytes[i + 1]), hex(bytes[i + 2])) else {
                return Err(ResourcePathError::InvalidFileUrl);
            };
            decoded.push((a * 16 + b) as u8);
            i += 3;
        } else {
            decoded.push(bytes[i]);
            i += 1;
        }
    }
    let decoded = String::from_utf8(decoded).map_err(|_| ResourcePathError::InvalidFileUrl)?;
    Ok(PathBuf::from(decoded))
}

/// This joins to the working directory but does not normalize components or resolve symlinks.
pub fn canonize(path: impl AsRef<Path>) -> io::Result<PathBuf> {
    let path = path.as_ref();
    if path.is_absolute() {
        Ok(path.to_owned())
    } else {
        Ok(env::current_dir()?.join(path))
    }
}

pub fn is_in_sub_directory(dir: &Path, file: Option<&Path>) -> bool {
    assert!(dir.is_dir(), "directory must exist and be a directory");
    let mut current = file;
    while let Some(path) = current {
        if path == dir {
            return true;
        }
        current = path.parent().filter(|p| !p.as_os_str().is_empty());
    }
    false
}
