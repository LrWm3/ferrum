//! Solver model parser.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/ModelParser.scala
//! Status: partial. Model/value/map grammar and let substitution are implemented;
//! exact FastParse diagnostic wording and parser-combinator backtracking remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::verification_error::{MapEntry, Model, ModelEntry, ValueEntry};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelParseError {
    pub offset: usize,
    pub expected: &'static str,
}
struct Parser<'a> {
    input: &'a str,
    offset: usize,
}
impl<'a> Parser<'a> {
    fn rest(&self) -> &'a str {
        &self.input[self.offset..]
    }
    fn error(&self, expected: &'static str) -> ModelParseError {
        ModelParseError {
            offset: self.offset,
            expected,
        }
    }
    fn starts(&self, s: &str) -> bool {
        self.rest().starts_with(s)
    }
    fn consume(&mut self, s: &str) -> bool {
        if self.starts(s) {
            self.offset += s.len();
            true
        } else {
            false
        }
    }
    fn whitespace(&mut self) -> Result<(), ModelParseError> {
        loop {
            let mut count = 0;
            for c in self.rest().chars() {
                if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                    count += c.len_utf8()
                } else {
                    break;
                }
            }
            self.offset += count;
            if self.consume("//") {
                let length = self.rest().find('\n').unwrap_or(self.rest().len());
                self.offset += length;
                continue;
            }
            if self.consume("/*") {
                let end = self
                    .rest()
                    .find("*/")
                    .ok_or_else(|| self.error("end of block comment"))?;
                self.offset += end + 2;
                continue;
            }
            break;
        }
        Ok(())
    }
    fn token(&mut self, s: &str) -> Result<(), ModelParseError> {
        self.whitespace()?;
        if self.consume(s) {
            Ok(())
        } else {
            Err(self.error("token"))
        }
    }
    fn identifier(&mut self) -> Result<String, ModelParseError> {
        self.whitespace()?;
        let len = self
            .rest()
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || b"[]\"'#+-*/:=!$_@<>.%~".contains(b))
            .count();
        if len == 0 {
            return Err(self.error("identifier"));
        }
        let name = self.rest()[..len].to_owned();
        self.offset += len;
        if name == "else" || name == "let" || name == "->" {
            return Err(self.error("non-reserved identifier"));
        }
        Ok(name)
    }
    fn value(&mut self) -> Result<ValueEntry, ModelParseError> {
        self.whitespace()?;
        if self.consume("(#unspecified)") {
            return Ok(ValueEntry::Unspecified);
        }
        let let_form = self.rest().strip_prefix("(let").is_some_and(|rest| {
            rest.starts_with('(')
                || rest.starts_with(' ')
                || rest.starts_with('\t')
                || rest.starts_with('\n')
                || rest.starts_with('\r')
                || rest.starts_with("/*")
                || rest.starts_with("//")
        });
        if let_form && self.consume("(let") {
            self.token("(")?;
            let mut bindings = Vec::new();
            loop {
                self.whitespace()?;
                if !self.starts("(") {
                    break;
                }
                self.token("(")?;
                let name = self.identifier()?;
                let value = self.value()?;
                self.token(")")?;
                bindings.push((name, value));
            }
            if bindings.is_empty() {
                return Err(self.error("let binding"));
            }
            self.token(")")?;
            let mut body = self.value()?;
            self.token(")")?;
            for (name, replacement) in bindings {
                body = substitute(body, &name, &replacement);
            }
            return Ok(body);
        }
        if self.consume("(") {
            let name = self.identifier()?;
            let mut arguments = Vec::new();
            loop {
                self.whitespace()?;
                if self.consume(")") {
                    break;
                }
                arguments.push(self.value()?);
            }
            return Ok(ValueEntry::Application { name, arguments });
        }
        Ok(ValueEntry::Constant(self.identifier()?))
    }
    fn mapping(&mut self) -> Result<ModelEntry, ModelParseError> {
        self.token("{")?;
        self.whitespace()?;
        let start = self.offset;
        let mut options = HashMap::new();
        loop {
            self.whitespace()?;
            if self.starts("}") {
                break;
            }
            let else_start = self.offset;
            let is_else_clause = if self.consume("else") {
                self.whitespace()?;
                self.starts("->")
            } else {
                false
            };
            self.offset = else_start;
            if is_else_clause {
                break;
            }
            let before = self.offset;
            let mut args = Vec::new();
            loop {
                let checkpoint = self.offset;
                match self.value() {
                    Ok(value) => args.push(value),
                    Err(_) => {
                        self.offset = checkpoint;
                        break;
                    }
                }
                self.whitespace()?;
                if self.starts("->") {
                    break;
                }
            }
            if args.is_empty() || !self.consume("->") {
                self.offset = before;
                break;
            }
            let value = self.value()?;
            options.insert(args, value);
        }
        let default = if options.is_empty() {
            self.offset = start;
            self.whitespace()?;
            let checkpoint = self.offset;
            if self.consume("else") {
                self.whitespace()?;
                if !self.consume("->") {
                    self.offset = checkpoint;
                }
            }
            self.value()?
        } else {
            self.whitespace()?;
            if self.consume("else") {
                self.token("->")?;
                self.value()?
            } else {
                ValueEntry::Unspecified
            }
        };
        self.token("}")?;
        let result = MapEntry { options, default };
        Ok(ModelEntry::Map(if result.options.is_empty() {
            result.resolve_function_definition()
        } else {
            result
        }))
    }
    fn definition(&mut self) -> Result<ModelEntry, ModelParseError> {
        if self.starts("{") {
            self.mapping()
        } else {
            self.value().map(ModelEntry::Value)
        }
    }
}
fn substitute(value: ValueEntry, name: &str, replacement: &ValueEntry) -> ValueEntry {
    match value {
        ValueEntry::Constant(ref v) if v == name => replacement.clone(),
        ValueEntry::Application {
            name: op,
            arguments,
        } => ValueEntry::Application {
            name: op,
            arguments: arguments
                .into_iter()
                .map(|a| substitute(a, name, replacement))
                .collect(),
        },
        other => other,
    }
}
/// Merge repeated map entries by retaining the first default and replacing options.
pub fn entries_to_model(entries: impl IntoIterator<Item = (String, ModelEntry)>) -> Model {
    let mut result = HashMap::new();
    for (key, entry) in entries {
        match entry {
            ModelEntry::Map(new) => match result.get_mut(&key) {
                Some(ModelEntry::Map(existing)) => existing.options.extend(new.options),
                _ => {
                    result.insert(key, ModelEntry::Map(new));
                }
            },
            other => {
                result.insert(key, other);
            }
        }
    }
    Model { entries: result }
}
pub fn parse_model(input: &str) -> Result<Model, ModelParseError> {
    let mut parser = Parser { input, offset: 0 };
    let mut entries = Vec::new();
    loop {
        parser.whitespace()?;
        if parser.rest().is_empty() {
            break;
        }
        let name = parser.identifier()?;
        // Entry-level whitespace after the arrow excludes newlines and comments.
        while parser.starts(" ") || parser.starts("\t") {
            parser.offset += 1;
        }
        if !parser.consume("->") {
            return Err(parser.error("->"));
        }
        while parser.starts(" ") || parser.starts("\t") {
            parser.offset += 1;
        }
        let entry = if parser.rest().is_empty()
            || parser.starts("\n")
            || parser.starts("\r")
            || parser.starts("//")
            || parser.starts("/*")
        {
            ModelEntry::Value(ValueEntry::Unspecified)
        } else {
            parser.definition()?
        };
        entries.push((name, entry));
    }
    Ok(entries_to_model(entries))
}
impl Model {
    pub fn parse(input: &str) -> Result<Self, ModelParseError> {
        parse_model(input)
    }
}

#[cfg(test)]
mod review_tests {
    use super::*;
    #[test]
    fn parses_options_with_else_prefixed_identifiers() {
        let model = parse_model("f -> { elseValue -> 1 else -> 0 }").unwrap();
        let ModelEntry::Map(map) = &model.entries["f"] else {
            panic!("map")
        };
        assert_eq!(
            map.options[&vec![ValueEntry::Constant("elseValue".into())]],
            ValueEntry::Constant("1".into())
        );
        assert_eq!(map.default, ValueEntry::Constant("0".into()));
        let model = parse_model("f -> { elseValue }").unwrap();
        let ModelEntry::Map(map) = &model.entries["f"] else {
            panic!("map")
        };
        assert_eq!(map.default, ValueEntry::Constant("elseValue".into()));
    }
}
