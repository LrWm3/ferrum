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
//! Status: description only; implementation has not started.
