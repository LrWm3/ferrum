//! Standalone method-CFG diagnostic driver.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/CfgTest.scala
//! Status: partial; the driver runs the native parser, available name/type/translation
//! subset and CFG generator. DOT rendering is supplied by the caller until AST printing lands.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::{
    cfg::silver::{
        cfg_generator::{GeneratorError, method_to_cfg},
        silver_cfg::SilverCfg,
    },
    parser::{
        fast_parser::{SyntaxError, parse_program},
        resolver::{NameAnalyser, NameAnalysisError, TypeCheckError, check_program_core},
        translator::{TranslationError, translate_program_core},
    },
};
use std::{io, path::Path};
#[derive(Debug)]
pub enum CfgTestError<E> {
    MissingInput,
    Io(io::Error),
    Parse(SyntaxError),
    NameAnalysis(NameAnalysisError),
    NameErrors,
    TypeCheck(TypeCheckError),
    Translation(TranslationError),
    Cfg(GeneratorError),
    Render(E),
}
/// Return lines in the same method order as the source driver. Warnings do not reject parsing.
pub fn run<E>(
    args: &[String],
    dot: &impl Fn(&SilverCfg) -> Result<String, E>,
) -> Result<Vec<String>, CfgTestError<E>> {
    let path = args.first().ok_or(CfgTestError::MissingInput)?;
    let text = std::fs::read_to_string(path).map_err(CfgTestError::Io)?;
    let program = parse_program(&text, Path::new(path)).map_err(CfgTestError::Parse)?;
    let mut names = NameAnalyser::default();
    if !names
        .run(program.node())
        .map_err(CfgTestError::NameAnalysis)?
    {
        return Err(CfgTestError::NameErrors);
    }
    check_program_core(&program, &mut |_, _| {}).map_err(CfgTestError::TypeCheck)?;
    let program = translate_program_core(&program).map_err(CfgTestError::Translation)?;
    let mut output = Vec::new();
    for method in &program.methods {
        let cfg = method_to_cfg(method, true, true).map_err(CfgTestError::Cfg)?;
        output.push(method.name.clone());
        output.push(dot(&cfg).map_err(CfgTestError::Render)?);
    }
    Ok(output)
}
