//! Silver source positions.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Position.scala
//!
//! Status: implemented; parser and diagnostic integration remains provisional.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::fmt;
use std::path::{Path, PathBuf};

/// A line and column without a source-file association.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LineColumnPosition {
    pub line: i32,
    pub column: i32,
}

impl LineColumnPosition {
    pub fn new(line: i32, column: i32) -> Self {
        Self { line, column }
    }
    pub fn delta_column(&self, delta: i32) -> Self {
        Self::new(self.line, self.column.wrapping_add(delta))
    }
}

/// The possible upstream `HasLineColumn` values, including nested source positions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LineColumn {
    LineColumn(LineColumnPosition),
    Source(Box<SourcePosition>),
    Identifier(Box<IdentifierPosition>),
    Translated(Box<AbstractSourcePosition>),
    File(FilePosition),
}

impl LineColumn {
    pub fn line(&self) -> i32 {
        match self {
            Self::LineColumn(p) => p.line,
            Self::Source(p) => p.start.line(),
            Self::Identifier(p) => p.start.line(),
            Self::Translated(p) => p.start().line(),
            Self::File(p) => p.line,
        }
    }
    pub fn column(&self) -> i32 {
        match self {
            Self::LineColumn(p) => p.column,
            Self::Source(p) => p.start.column(),
            Self::Identifier(p) => p.start.column(),
            Self::Translated(p) => p.start().column(),
            Self::File(p) => p.column,
        }
    }
    pub fn less_or_equal(&self, other: &Self) -> bool {
        (self.line(), self.column()) <= (other.line(), other.column())
    }
    pub fn delta_column(&self, delta: i32) -> Self {
        match self {
            Self::LineColumn(p) => Self::LineColumn(p.delta_column(delta)),
            Self::Source(p) => Self::Source(Box::new(p.delta_column(delta))),
            Self::Identifier(p) => Self::Identifier(Box::new(p.delta_column(delta))),
            Self::Translated(p) => Self::Translated(Box::new(p.delta_column(delta))),
            Self::File(p) => Self::File(p.delta_column(delta)),
        }
    }
}

impl From<LineColumnPosition> for LineColumn {
    fn from(value: LineColumnPosition) -> Self {
        Self::LineColumn(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourcePosition {
    /// `None` represents upstream's nullable path.
    pub file: Option<PathBuf>,
    pub start: Box<LineColumn>,
    pub end: Option<Box<LineColumn>>,
}
impl SourcePosition {
    pub fn new(file: impl Into<PathBuf>, line: i32, column: i32) -> Self {
        Self {
            file: Some(file.into()),
            start: Box::new(LineColumnPosition::new(line, column).into()),
            end: None,
        }
    }
    pub fn delta_column(&self, delta: i32) -> Self {
        Self {
            file: self.file.clone(),
            start: Box::new(self.start.delta_column(delta)),
            end: self.end.as_ref().map(|p| Box::new(p.delta_column(delta))),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IdentifierPosition {
    pub file: Option<PathBuf>,
    pub start: Box<LineColumn>,
    pub end: Option<Box<LineColumn>>,
    pub id: String,
}
impl IdentifierPosition {
    pub fn delta_column(&self, delta: i32) -> Self {
        Self {
            file: self.file.clone(),
            start: Box::new(self.start.delta_column(delta)),
            end: self.end.as_ref().map(|p| Box::new(p.delta_column(delta))),
            id: self.id.clone(),
        }
    }
}

/// A source-position value, preserving the runtime class used for equality.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AbstractSourcePosition {
    Source(SourcePosition),
    Identifier(IdentifierPosition),
    Translated(Box<AbstractSourcePosition>),
}
impl AbstractSourcePosition {
    pub fn file(&self) -> Option<&Path> {
        match self {
            Self::Source(p) => p.file.as_deref(),
            Self::Identifier(p) => p.file.as_deref(),
            Self::Translated(p) => p.file(),
        }
    }
    pub fn start(&self) -> &LineColumn {
        match self {
            Self::Source(p) => &p.start,
            Self::Identifier(p) => &p.start,
            Self::Translated(p) => p.start(),
        }
    }
    pub fn end(&self) -> Option<&LineColumn> {
        match self {
            Self::Source(p) => p.end.as_deref(),
            Self::Identifier(p) => p.end.as_deref(),
            Self::Translated(p) => p.end(),
        }
    }
    pub fn delta_column(&self, delta: i32) -> Self {
        match self {
            Self::Source(p) => Self::Source(p.delta_column(delta)),
            Self::Identifier(p) => Self::Identifier(p.delta_column(delta)),
            Self::Translated(p) => Self::Translated(Box::new(p.delta_column(delta))),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FilePosition {
    pub file: PathBuf,
    pub line: i32,
    pub column: i32,
}
impl FilePosition {
    pub fn delta_column(&self, delta: i32) -> Self {
        Self {
            file: self.file.clone(),
            line: self.line,
            column: self.column.wrapping_add(delta),
        }
    }
    pub fn line_contents(&self) -> String {
        self.to_string()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub enum Position {
    #[default]
    NoPosition,
    LineColumn(LineColumn),
    Virtual(String),
}
impl Position {
    pub fn delta_column(&self, delta: i32) -> Self {
        match self {
            Self::NoPosition => Self::NoPosition,
            Self::LineColumn(p) => Self::LineColumn(p.delta_column(delta)),
            Self::Virtual(id) => Self::Virtual(id.clone()),
        }
    }
    pub fn line_column(&self) -> Option<&LineColumn> {
        match self {
            Self::LineColumn(p) => Some(p),
            _ => None,
        }
    }
}

fn source_display(
    f: &mut fmt::Formatter<'_>,
    file: Option<&Path>,
    start: &LineColumn,
    end: Option<&LineColumn>,
) -> fmt::Result {
    if let Some(name) = file.and_then(Path::file_name) {
        write!(f, "{}@", name.to_string_lossy())?;
    }
    write!(f, "{}.{}", start.line(), start.column())?;
    if let Some(end) = end {
        write!(f, "--{}.{}", end.line(), end.column())?;
    }
    Ok(())
}
impl fmt::Display for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        source_display(f, self.file.as_deref(), &self.start, self.end.as_deref())
    }
}
impl fmt::Display for IdentifierPosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        source_display(f, self.file.as_deref(), &self.start, self.end.as_deref())
    }
}
impl fmt::Display for AbstractSourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        source_display(f, self.file(), self.start(), self.end())
    }
}
impl fmt::Display for FilePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}@{}.{}",
            self.file
                .file_name()
                .map(|n| n.to_string_lossy())
                .unwrap_or_default(),
            self.line,
            self.column
        )
    }
}
impl fmt::Display for LineColumn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LineColumn(p) => write!(f, "{}.{}", p.line, p.column),
            Self::Source(p) => p.fmt(f),
            Self::Identifier(p) => p.fmt(f),
            Self::Translated(p) => p.fmt(f),
            Self::File(p) => p.fmt(f),
        }
    }
}
impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoPosition => f.write_str("<no position>"),
            Self::LineColumn(p) => p.fmt(f),
            Self::Virtual(id) => f.write_str(id),
        }
    }
}

/// `LineCol` consults the parser's line-start offsets. Negative/out-of-range offsets
/// that would index before the first line are reported instead of indexing blindly.
pub struct LineCol<'a> {
    pub line_offsets: &'a [i32],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidLineOffset {
    pub index: i32,
}
impl LineCol<'_> {
    pub fn get_pos(&self, index: i32) -> Result<(i32, i32), InvalidLineOffset> {
        if self.line_offsets.is_empty() {
            return Ok((1, 1));
        }
        let line = match self.line_offsets.binary_search(&index) {
            Ok(i) => i,
            Err(0) => return Err(InvalidLineOffset { index }),
            Err(i) => i - 1,
        };
        Ok((
            (line as i32).wrapping_add(1),
            index.wrapping_sub(self.line_offsets[line]).wrapping_add(1),
        ))
    }
}
