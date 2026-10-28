//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtPlugin.scala
//!
//! Purpose:
//! Register ADT syntax, identify ADT uses and invoke domain encoding.
//!
//! Planned Rust structure:
//! Port AdtPlugin grammar for declarations, constructors and derives/without; beforeParse,
//! beforeResolve and beforeVerify with derivesImported and termination-option state.
//!
//! Behavior to preserve:
//! Disabled plugin leaves input unchanged. Register grammar only on main input; detect derives
//! import in any source. Before resolution rewrite ADT types, constructor calls, destructors and
//! discriminators using declared names, while preserving field-assignment targets for ordinary
//! resolution; drop derives when resource import absent. Encode before verification with
//! well-foundedness conditional on active termination plugin and configuration.
//!
//! Integration:
//! parser::fast_parser/resolver; adt_past_extension, encoding::adt_encoder,
//! frontend::sil_front_end_config and termination plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for native parser/plugin registration and contextual rewriting.
//!
//! Open decisions:
//! Reconcile per-run derivesImported lifetime and plugin ordering with frontend and parser.
//!
//! Status: partial; ADT declaration grammar, derives-import tracking, termination configuration and
//! AST encoding hook are implemented. ADT declaration/type analysis and constructor/destructor/
//! discriminator dispatch and declaration annotations are active; full grammar formatting metadata
//! and some extension corner cases remain incomplete.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::encoding::adt_encoder::AdtEncoder;
use crate::ast::program::Program;
use crate::ast::utility::consistency::transitive_scoped_names;
use crate::plugin::silver_plugin::{PluginHookError, SilverPlugin};

/// Register ADT syntax, resolve ADT operators and encode checked ADT ASTs.
#[derive(Clone, Debug, Default)]
pub struct AdtPlugin {
    pub has_config: bool,
    pub disabled: bool,
    pub disable_termination: bool,
    pub disable_default_plugins: bool,
    pub explicit_plugins: Vec<String>,
    derives_imported: bool,
    errors: Vec<crate::verifier::verification_result::AbstractError>,
}
impl AdtPlugin {
    fn deactivated(&self) -> bool {
        self.has_config && self.disabled
    }
    pub fn derives_imported(&self) -> bool {
        self.derives_imported
    }
    pub fn termination_active(&self) -> bool {
        self.has_config
            && !self.disable_termination
            && (!self.disable_default_plugins
                || self.explicit_plugins.iter().any(|name| {
                    name == "viper.silver.plugin.standard.termination.TerminationPlugin"
                }))
    }
}
impl SilverPlugin for AdtPlugin {
    fn shared_entity_mapper(
        &self,
    ) -> Option<std::sync::Arc<dyn crate::reporter::reporter::EntityResultMapper>> {
        Some(crate::plugin::silver_plugin_manager::identity_entity_mapper())
    }

    fn errors(&self) -> &[crate::verifier::verification_result::AbstractError] {
        &self.errors
    }
    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        if self.deactivated() {
            Vec::new()
        } else {
            vec![crate::parser::fast_parser::ParserFeature::Adt]
        }
    }
    fn before_parse(&mut self, input: String, _: bool) -> String {
        if !self.deactivated() {
            self.derives_imported |= input.match_indices("import").any(|(i, _)| {
                let tail = &input[i + "import".len()..];
                let is_source_space =
                    |c| matches!(c, ' ' | '\t' | '\n' | '\r' | '\u{000b}' | '\u{000c}');
                tail.chars().next().is_some_and(is_source_space)
                    && tail
                        .trim_start_matches(is_source_space)
                        .starts_with("<adt/derives.vpr>")
            });
        }
        input
    }
    fn before_resolve(
        &mut self,
        input: crate::parser::parse_ast::PProgramHandle,
    ) -> crate::parser::parse_ast::PProgramHandle {
        if self.deactivated() {
            return input;
        }
        use super::adt_past_extension::{PAdt, PAdtConstructor};
        use crate::parser::parse_ast::{
            PDeclarationClass, PDomainTypeKind, PExpressionKind, PMemberKind, PNodeHandle,
            PNodeKind, PTypeKind, subnodes,
        };
        use std::{collections::HashSet, sync::Arc};
        let mut names = HashSet::new();
        let mut constructor_names = HashSet::new();
        let mut field_names = HashSet::new();
        for member in input.all_members() {
            let mut node = member.node().write().expect("poisoned parse node");
            if let PNodeKind::Member(member) = &mut node.kind {
                if let PMemberKind::Extension(extension) = &mut member.kind {
                    if let Some(adt) = extension.as_any().downcast_ref::<PAdt>() {
                        for constructor in &adt.constructors {
                            if let PNodeKind::Extension(ext) =
                                &constructor.read().expect("poisoned parse node").kind
                            {
                                if let Some(ctor) = ext.as_any().downcast_ref::<PAdtConstructor>() {
                                    for field in ctor.formal_args() {
                                        if let PNodeKind::Declaration(decl) =
                                            &field.node().read().expect("poisoned parse node").kind
                                        {
                                            if let PNodeKind::IdnDef(id) = &decl
                                                .idndef
                                                .read()
                                                .expect("poisoned parse node")
                                                .kind
                                            {
                                                field_names.insert(id.name.clone());
                                            }
                                        }
                                    }
                                    if let PNodeKind::IdnDef(id) =
                                        &ctor.idndef.read().expect("poisoned parse node").kind
                                    {
                                        constructor_names.insert(id.name.clone());
                                    }
                                }
                            }
                        }
                        if let PNodeKind::IdnDef(id) =
                            &adt.idndef.read().expect("poisoned parse node").kind
                        {
                            names.insert(id.name.clone());
                        }
                        if !self.derives_imported {
                            let mut adt = adt.clone();
                            adt.deriving.clear();
                            *extension = Arc::new(adt);
                        }
                    }
                }
            }
        }
        fn rewrite(
            node: &PNodeHandle,
            names: &HashSet<String>,
            constructor_names: &HashSet<String>,
            field_names: &HashSet<String>,
        ) -> Result<(), String> {
            let kind = node.read().expect("poisoned parse node").kind.clone();
            if let PNodeKind::Statement(stmt) = &kind {
                if let crate::parser::parse_ast::PStatementKind::Assign { targets, rhs, .. } =
                    &stmt.kind
                {
                    if targets.len() == 1 {
                        let target = targets.head();
                        let target_kind = target
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .kind
                            .clone();
                        if let PNodeKind::Expression(crate::parser::parse_ast::PExpression {
                            kind:
                                PExpressionKind::FieldAccess {
                                    receiver, idnref, ..
                                },
                            ..
                        }) = target_kind
                        {
                            let protected = matches!(&idnref.read().expect("poisoned parse node").kind, PNodeKind::IdnRef(id) if field_names.contains(&id.name) || id.name.strip_prefix("is").is_some_and(|name| constructor_names.contains(name)));
                            if protected {
                                rewrite(receiver.node(), names, constructor_names, field_names)?;
                                rewrite(rhs.node(), names, constructor_names, field_names)?;
                                return Ok(());
                            }
                        }
                    }
                }
            }
            if let PNodeKind::Type(PTypeKind::Domain { domain, .. }) = &kind {
                let matching = matches!(&domain.read().expect("poisoned parse node").kind, PNodeKind::IdnRef(id) if names.contains(&id.name));
                if matching {
                    if let PNodeKind::Type(PTypeKind::Domain { kind, .. }) =
                        &mut node.write().expect("poisoned parse node").kind
                    {
                        *kind = PDomainTypeKind::Adt;
                    }
                }
            }
            if let PNodeKind::Expression(expression) = &kind {
                if let PExpressionKind::Call { idnref, .. } = &expression.kind {
                    let mut reference = idnref.write().expect("poisoned parse node");
                    if let PNodeKind::IdnRef(id) = &mut reference.kind {
                        if constructor_names.contains(&id.name) {
                            id.declaration_class = PDeclarationClass::AdtConstructor;
                        }
                    }
                }
                if let PExpressionKind::FieldAccess { idnref, .. } = &expression.kind {
                    let mut reference = idnref.write().expect("poisoned parse node");
                    let mut discriminator = false;
                    if let PNodeKind::IdnRef(id) = &mut reference.kind {
                        if field_names.contains(&id.name) {
                            id.declaration_class = PDeclarationClass::AdtField;
                        } else if let Some(name) = id
                            .name
                            .strip_prefix("is")
                            .filter(|name| constructor_names.contains(*name))
                        {
                            id.name = name.to_owned();
                            id.declaration_class = PDeclarationClass::AdtConstructor;
                            discriminator = true;
                        }
                    }
                    if discriminator {
                        reference.pos.0 = reference.pos.0.delta_column(2);
                    }
                }
            }
            for child in subnodes(node).map_err(|e| format!("ADT parse-tree traversal: {e:?}"))? {
                rewrite(&child, names, constructor_names, field_names)?;
            }
            Ok(())
        }
        if let Err(message) = rewrite(input.node(), &names, &constructor_names, &field_names) {
            use crate::verifier::verification_result::{
                AbstractError, FrontendError, FrontendErrorKind,
            };
            let position = input
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .0
                .clone();
            self.errors.push(AbstractError::Frontend(FrontendError::new(
                FrontendErrorKind::TypecheckerError(message),
                position,
            )));
        }
        input
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        if self.deactivated() {
            return Ok(input);
        }
        let names = transitive_scoped_names(&input)
            .map_err(|e| PluginHookError(format!("ADT scoped-name collection: {e:?}")))?;
        AdtEncoder::new(input, names)
            .encode(self.termination_active())
            .map_err(|e| PluginHookError(format!("ADT encoding: {e:?}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ast::Metadata;
    use crate::ast::program::ExtensionMemberHandle;
    use crate::plugin::standard::adt::adt_ast_extension::{Adt, AdtConstructor};
    use std::{collections::HashMap, sync::Arc};

    #[test]
    fn encodes_checked_adt_program_and_tracks_configuration() {
        let meta = Metadata::default();
        let constructor = Arc::new(AdtConstructor::new(
            "Tree",
            vec![],
            "Leaf",
            vec![],
            meta.clone(),
        ));
        let adt = Adt {
            name: "Tree".into(),
            constructors: vec![constructor],
            type_vars: vec![],
            deriving_info: HashMap::new(),
            meta: meta.clone(),
        };
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![ExtensionMemberHandle(Arc::new(adt))],
            meta,
        );
        let mut plugin = AdtPlugin::default();
        assert!(!plugin.termination_active());
        plugin.before_parse("import  <adt/derives.vpr>".into(), true);
        assert!(plugin.derives_imported());
        let output = plugin.before_verify(program).unwrap();
        assert!(output.extensions.is_empty());
        assert_eq!(output.domains[0].name, "Tree");
    }
}
