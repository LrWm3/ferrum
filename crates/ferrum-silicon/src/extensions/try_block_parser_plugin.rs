//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/extensions/TryBlockParserPlugin.scala
//!
//! Purpose:
//! Register syntax for Silicon try blocks.
//!
//! Planned Rust structure:
//! Port TryBlockParserPlugin tryBlock parser and beforeParse hook.
//!
//! Behavior to preserve:
//! Register try keyword and end-statement parser, parse a statement block and preserve source
//! span; return input unchanged.
//!
//! Integration:
//! extensions::try_block_stmt and ferrum_silver::parser::fast_parser and plugin interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for native parser extension registration.
//!
//! Open decisions:
//! Agree on parser hook and plugin lifetime with Silver frontend.
//!
//! Status: partial; typed statement-block parser registration is implemented. Silicon execution
//! of the resulting extension remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2020 ETH Zurich.

use super::try_block_stmt::{PTryBlock, try_keyword};
use ferrum_silver::parser::fast_parser::ParserFeature;
use ferrum_silver::parser::parse_ast::PStmtHandle;
use ferrum_silver::parser::parse_ast_keyword::Span;
use ferrum_silver::plugin::silver_plugin::SilverPlugin;

fn make_try_block(keyword: Span, body: PStmtHandle, pos: Span) -> PStmtHandle {
    PTryBlock {
        keyword: try_keyword(keyword),
        body,
        pos,
    }
    .statement()
}
#[derive(Default)]
pub struct TryBlockParserPlugin;
impl SilverPlugin for TryBlockParserPlugin {
    fn shared_entity_mapper(
        &self,
    ) -> Option<std::sync::Arc<dyn ferrum_silver::reporter::reporter::EntityResultMapper>> {
        Some(ferrum_silver::plugin::silver_plugin_manager::identity_entity_mapper())
    }
    fn parser_features(&self) -> Vec<ParserFeature> {
        vec![ParserFeature::StatementBlock {
            keyword: "try",
            factory: make_try_block,
        }]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extensions::try_block_stmt::TryBlock;
    use ferrum_silver::ast::statement::StmtKind;
    use ferrum_silver::frontend::frontend::FrontendPhases;
    use ferrum_silver::frontend::sil_frontend::SilFrontendPhases;
    use ferrum_silver::parser::reformat_pretty_printer::{LeafReformatAdapter, show_program};
    use ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager;
    use std::path::PathBuf;

    #[test]
    fn reformats_nested_try_blocks_like_source() {
        let plugins = SilverPluginManager::new(vec![Box::new(TryBlockParserPlugin)]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases
            .parse("method m(){try{assert true;} try {try { assert false; }}}")
            .unwrap();
        assert_eq!(
            show_program(parsed.node(), &LeafReformatAdapter).unwrap(),
            "method m() {\n    try {\n        assert true;\n    }\n    try {\n        try {\n            assert false;\n        }\n    }\n}"
        );
    }

    #[test]
    fn try_block_is_duplicated_inside_macro_expansion() {
        let plugins = SilverPluginManager::new(vec![Box::new(TryBlockParserPlugin)]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases
            .parse("define guard(v) { try { assert v; } } method m() { guard(true); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn parses_checks_and_translates_try_block() {
        let plugins = SilverPluginManager::new(vec![Box::new(TryBlockParserPlugin)]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases.parse("method m() { try { assert true; } }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let StmtKind::Seqn { statements, .. } = program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("method block")
        };
        let StmtKind::Extension(extension) = statements[0].kind() else {
            panic!("try statement")
        };
        assert!(extension.0.as_any().is::<TryBlock>());
        phases.check_consistency(program).unwrap();
    }
}
