//! Recursive interpretation of extracted model values.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/DomainInterpreter.scala
//! Status: source identity and generic recursive interpreters implemented; the
//! converter supplies domain/function lists and variable extraction through the
//! typed fallible context boundary.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::converter::{
    DomainEntry, ExtractedFunction, ExtractedModelEntry, FunctionApplication, FunctionError,
};
use crate::state::{identifiers::Identifier, terms::Sort};

pub trait AbstractInterpreter<E, I, T> {
    type Error;
    fn interpret(&self, entry: &E, info: &I) -> Result<T, Self::Error>;
}
pub struct IdentityInterpreter;
impl<I> AbstractInterpreter<ExtractedModelEntry, I, ExtractedModelEntry> for IdentityInterpreter {
    type Error = std::convert::Infallible;
    fn interpret(
        &self,
        entry: &ExtractedModelEntry,
        _: &I,
    ) -> Result<ExtractedModelEntry, Self::Error> {
        Ok(entry.clone())
    }
}
/// The converter's completed heap and model view. Extraction failures must be
/// propagated; an absent implementation cannot masquerade as a model value.
pub trait InterpretationContext {
    type Error;
    fn domains(&self) -> &[DomainEntry];
    fn non_domain_functions(&self) -> &[ExtractedFunction];
    fn extract_variable(
        &self,
        entry: &ExtractedModelEntry,
    ) -> Result<ExtractedModelEntry, Self::Error>;
}
#[derive(Debug)]
pub enum InterpretError<E> {
    Context(E),
    Function(FunctionError),
    TypePrinter(ferrum_silver::ast::pretty::pretty_printer::PrintError),
}
pub struct GenericDomainInterpreter<'a, C> {
    pub context: &'a C,
}
impl<C: InterpretationContext>
    AbstractInterpreter<ExtractedModelEntry, Vec<ExtractedModelEntry>, ExtractedModelEntry>
    for GenericDomainInterpreter<'_, C>
{
    type Error = InterpretError<C::Error>;
    fn interpret(
        &self,
        entry: &ExtractedModelEntry,
        visited: &Vec<ExtractedModelEntry>,
    ) -> Result<ExtractedModelEntry, Self::Error> {
        if visited.contains(entry) {
            return Ok(entry.clone());
        }
        let mut next = Vec::with_capacity(visited.len() + 1);
        next.push(entry.clone());
        next.extend_from_slice(visited);
        match entry {
            ExtractedModelEntry::DomainValue { domain, .. } => {
                let mut functions = self
                    .context
                    .non_domain_functions()
                    .iter()
                    .collect::<Vec<_>>();
                for dom in self.context.domains() {
                    if dom.value_name().map_err(InterpretError::TypePrinter)? == *domain {
                        functions.extend(dom.functions.iter());
                    }
                }
                let expected = Sort::UserSort(Identifier::new(domain.clone()));
                let mut info = Vec::new();
                for function in functions
                    .into_iter()
                    .filter(|f| f.argument_types.len() == 1 && f.argument_types[0] == expected)
                {
                    let result = match function
                        .apply(std::slice::from_ref(entry))
                        .map_err(InterpretError::Function)?
                    {
                        FunctionApplication::Value(value) => self.interpret(&value, &next)?,
                        FunctionApplication::Partial(_) => ExtractedModelEntry::Other {
                            value: function.name.clone(),
                            problem: "not been able to resolve function".into(),
                        },
                    };
                    if let Some((_, old)) =
                        info.iter_mut().find(|(existing, _)| existing == function)
                    {
                        *old = result;
                    } else {
                        info.push((function.clone(), result));
                    }
                }
                Ok(ExtractedModelEntry::ExtendedDomain {
                    original: Box::new(entry.clone()),
                    info,
                })
            }
            ExtractedModelEntry::Var { .. } => {
                let value = self
                    .context
                    .extract_variable(entry)
                    .map_err(InterpretError::Context)?;
                self.interpret(&value, &next)
            }
            ExtractedModelEntry::Ref { name, fields } => {
                let mut result = Vec::with_capacity(fields.len());
                for (field, (value, perm)) in fields {
                    result.push((field.clone(), (self.interpret(value, &next)?, perm.clone())));
                }
                Ok(ExtractedModelEntry::Ref {
                    name: name.clone(),
                    fields: result,
                })
            }
            _ => Ok(entry.clone()),
        }
    }
}
