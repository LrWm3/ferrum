//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/ParserPluginTemplate.scala
//!
//! Purpose:
//! Specify parser and AST extension hooks with illustrative extension types.
//!
//! Planned Rust structure:
//! Represent ParserPluginTemplate extension callbacks for declaration, statement and expression
//! start/end; pre/post/invariant specifications and keywords. Include combine/defaultExtension and
//! account for example parse/AST nodes as documentation.
//!
//! Behavior to preserve:
//! Start hooks precede base grammar and end hooks follow it; combine tries left before right.
//! Default parsers fail, while default spec hooks wrap an expression in the implied specification
//! token. Example implementations contain upstream unimplemented methods and are examples, not
//! successful verification logic.
//!
//! Integration:
//! parser::fast_parser registers and invokes extensions; parser::parse_ast, resolver and
//! translator call PExtender hooks; ast extension nodes and reporter/verifier types are shared.
//!
//! Rust adaptations:
//! Follow porting/conventions.md; replace FastParse parser functions and JVM extension mechanism
//! without committing to parser technology.
//!
//! Open decisions:
//! Agree on extension parser interface and native registration with fast_parser and
//! silver_plugin_manager.
//!
//! Status: partial; ordered native hook protocols implemented. FastParser integration,
//! annotation-position constructors and typed specification wrappers remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::parser::parse_ast::{PExpHandle, PMemberHandle, PStmtHandle};

/// Hook input uses a byte cursor into UTF-8 source; positions are constructed by the parser.
pub struct HookContext<'a> {
    pub source: &'a str,
    pub cursor: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HookError {
    Committed { offset: usize, message: String },
}
/// `None` denotes an unmatched alternative. A committed parse failure is distinct.
pub type HookResult<T> = Result<Option<T>, HookError>;
pub type Hook<T> = Box<dyn for<'a> Fn(&mut HookContext<'a>) -> HookResult<T> + Send + Sync>;
/// Ordered parser alternative, restoring the cursor when the left alternative does not match.
pub fn combine<T: 'static>(left: Hook<T>, right: Hook<T>) -> Hook<T> {
    Box::new(move |ctx| {
        let checkpoint = ctx.cursor;
        match left(ctx)? {
            Some(value) => Ok(Some(value)),
            None => {
                ctx.cursor = checkpoint;
                right(ctx)
            }
        }
    })
}
pub fn default_extension<T: 'static>() -> Hook<T> {
    Box::new(|_| Ok(None))
}

/// Optional hooks are tried before and after the built-in grammar in source order.
/// Pre/post/invariant hooks produce their underlying expression; the parser constructs
/// the implied `requires`, `ensures`, or `invariant` specification token.
pub trait ParserPluginTemplate: Send + Sync {
    fn new_decl_at_start(&self) -> Hook<PMemberHandle> {
        default_extension()
    }
    fn new_decl_at_end(&self) -> Hook<PMemberHandle> {
        default_extension()
    }
    fn new_stmt_at_start(&self) -> Hook<PStmtHandle> {
        default_extension()
    }
    fn new_stmt_at_end(&self) -> Hook<PStmtHandle> {
        default_extension()
    }
    fn new_exp_at_start(&self) -> Hook<PExpHandle> {
        default_extension()
    }
    fn new_exp_at_end(&self) -> Hook<PExpHandle> {
        default_extension()
    }
    fn pre_specification(&self) -> Hook<PExpHandle> {
        default_extension()
    }
    fn post_specification(&self) -> Hook<PExpHandle> {
        default_extension()
    }
    fn inv_specification(&self) -> Hook<PExpHandle> {
        default_extension()
    }
    fn extended_keywords(&self) -> Vec<String> {
        Vec::new()
    }
}
