//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/NameGenerator.scala
//!
//! Purpose:
//! Generate valid and unique identifiers in nested scopes.
//!
//! Planned Rust structure:
//! Port NameGenerator, DefaultNameGenerator and mutable NameContext, including identifier
//! conversion, counters and subcontexts.
//!
//! Behavior to preserve:
//! Greek and operator substitutions are explicit; invalid characters are removed, default prefix
//! applied where needed and reserved names repeatedly prefixed. Unique names check ancestors and
//! descendants, while siblings may overlap; increment counters and skip existing suffixed names.
//!
//! Integration:
//! utility::sil_name_generator supplies Silver syntax and ast::utility::consistency reserved
//! names.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on owned context tree and mutation/thread-safety with name generator consumers.
//!
//! Status: implemented; not yet wired or validated.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub trait NameGenerator: Sized {
    fn create_unique_identifier(&self, input: &str) -> String;
    fn create_unique(&self, input: &str) -> String;
    fn create_identifier(&self, input: &str) -> String;
    fn create_sub_context(&self) -> Self;
}

/// Character and reserved-word rules shared by all contexts of a generator.
pub struct NameRules {
    pub separator: String,
    pub default_ident: String,
    pub first_character: fn(char) -> bool,
    pub other_character: fn(char) -> bool,
    pub reserved_names: HashSet<String>,
}
impl NameRules {
    pub fn create_identifier(&self, input: &str) -> String {
        let Some(first) = input.chars().next() else {
            return self.default_ident.clone();
        };
        let mut result = String::new();
        if !(self.first_character)(first) && replacement(first).is_none() {
            result.push_str(&self.default_ident);
        }
        for ch in input.chars() {
            if (self.other_character)(ch) {
                result.push(ch);
            } else if let Some(text) = replacement(ch) {
                result.push_str(text);
            }
        }
        while self.reserved_names.contains(&result) {
            result.insert_str(0, &self.default_ident);
        }
        result
    }
}

fn replacement(ch: char) -> Option<&'static str> {
    match ch {
        'Α' => Some("Alpha"),
        'Β' => Some("Beta"),
        'Γ' => Some("Gamma"),
        'Δ' => Some("Delta"),
        'Ε' => Some("Epsilon"),
        'Ζ' => Some("Zeta"),
        'Η' => Some("Eta"),
        'Θ' => Some("Theta"),
        'Ι' => Some("Iota"),
        'Κ' => Some("Kappa"),
        'Λ' => Some("Lambda"),
        'Μ' => Some("My"),
        'Ν' => Some("Ny"),
        'Ξ' => Some("Xi"),
        'Ο' => Some("Omikron"),
        'Π' => Some("Pi"),
        'Ρ' => Some("Rho"),
        'Σ' => Some("Sigma"),
        'Τ' => Some("Tau"),
        'Υ' => Some("Ypsilon"),
        'Φ' => Some("Phi"),
        'Χ' => Some("Chi"),
        'Ψ' => Some("Psi"),
        'Ω' => Some("Omega"),
        'α' => Some("alpha"),
        'β' => Some("beta"),
        'γ' => Some("gamma"),
        'δ' => Some("delta"),
        'ε' => Some("epsilon"),
        'ζ' => Some("zeta"),
        'η' => Some("eta"),
        'θ' => Some("theta"),
        'ι' => Some("iota"),
        'κ' => Some("kappa"),
        'λ' => Some("lambda"),
        'μ' => Some("my"),
        'ν' => Some("ny"),
        'ξ' => Some("xi"),
        'ο' => Some("omikron"),
        'π' => Some("pi"),
        'ρ' => Some("rho"),
        'σ' => Some("sigma"),
        'τ' => Some("tau"),
        'υ' => Some("ypsilon"),
        'φ' => Some("phi"),
        'χ' => Some("chi"),
        'ψ' => Some("psi"),
        'ω' => Some("omega"),
        'ς' => Some("varsigma"),
        '+' => Some("plus"),
        '-' => Some("minus"),
        '*' => Some("times"),
        '/' => Some("divided"),
        '%' => Some("mod"),
        '!' => Some("bang"),
        '<' => Some("less"),
        '>' => Some("greater"),
        '=' => Some("eq"),
        _ => None,
    }
}

#[derive(Default)]
struct ContextData {
    counters: HashMap<String, i32>,
    parent: Option<usize>,
    children: Vec<usize>,
}

/// Handles share a context tree; sibling contexts intentionally do not conflict.
#[derive(Clone)]
pub struct NameContext {
    rules: Rc<NameRules>,
    tree: Rc<RefCell<Vec<ContextData>>>,
    id: usize,
}
impl NameContext {
    pub fn new(rules: NameRules) -> Self {
        Self {
            rules: Rc::new(rules),
            tree: Rc::new(RefCell::new(vec![ContextData::default()])),
            id: 0,
        }
    }
    pub fn create_sub_context(&self) -> Self {
        let mut tree = self.tree.borrow_mut();
        let id = tree.len();
        tree.push(ContextData {
            parent: Some(self.id),
            ..ContextData::default()
        });
        tree[self.id].children.push(id);
        Self {
            rules: self.rules.clone(),
            tree: self.tree.clone(),
            id,
        }
    }
    pub fn create_identifier(&self, input: &str) -> String {
        self.rules.create_identifier(input)
    }
    pub fn create_unique_identifier(&self, input: &str) -> String {
        self.create_unique(&self.create_identifier(input))
    }
    pub fn create_unique(&self, input: &str) -> String {
        fn descendants(tree: &[ContextData], id: usize, result: &mut Vec<usize>) {
            for &child in &tree[id].children {
                result.push(child);
                descendants(tree, child, result);
            }
        }
        let mut tree = self.tree.borrow_mut();
        let mut contexts = vec![self.id];
        let mut parent = tree[self.id].parent;
        while let Some(id) = parent {
            parent = tree[id].parent;
            contexts.push(id);
        }
        descendants(&tree, self.id, &mut contexts);
        let counters: Vec<i32> = contexts
            .iter()
            .filter_map(|&id| tree[id].counters.get(input).copied())
            .collect();
        if counters.is_empty() {
            tree[self.id].counters.insert(input.to_owned(), 0);
            return input.to_owned();
        }
        let mut counter = counters.into_iter().max().unwrap().wrapping_add(1);
        let name = loop {
            let name = format!("{}{}{}", input, self.rules.separator, counter);
            if !contexts
                .iter()
                .any(|&id| tree[id].counters.contains_key(&name))
            {
                break name;
            }
            counter = counter.wrapping_add(1);
        };
        tree[self.id].counters.insert(input.to_owned(), counter);
        tree[self.id].counters.insert(name.clone(), 0);
        name
    }
}

pub type DefaultNameGenerator = NameContext;

impl NameGenerator for NameContext {
    fn create_unique_identifier(&self, input: &str) -> String {
        NameContext::create_unique_identifier(self, input)
    }
    fn create_unique(&self, input: &str) -> String {
        NameContext::create_unique(self, input)
    }
    fn create_identifier(&self, input: &str) -> String {
        NameContext::create_identifier(self, input)
    }
    fn create_sub_context(&self) -> Self {
        NameContext::create_sub_context(self)
    }
}
