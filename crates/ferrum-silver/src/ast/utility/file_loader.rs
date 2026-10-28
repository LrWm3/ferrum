//! Injectable source-file loading.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/FileLoader.scala
//! Status: partial; disk loading uses UTF-8 rather than JVM platform-default encoding.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright notice: the pinned upstream file does not carry an individual notice.

use std::{io, path::Path};

pub trait FileLoader: Send + Sync {
    fn load_content(&self, path: &Path) -> io::Result<String>;
}
#[derive(Clone, Copy, Debug, Default)]
pub struct DiskLoader;
impl FileLoader for DiskLoader {
    fn load_content(&self, path: &Path) -> io::Result<String> {
        std::fs::read_to_string(path)
    }
}
