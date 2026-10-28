//! Ferrum optional linked Z3 driver, assembled under PLAN.md from Silicon's
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverAPI.scala
//! and TermToZ3APIConverter.scala. This driver is optional; default verification uses stdio.
//! Status: partial; context-owned handles, primitive terms, datatypes, solver scopes,
//! quantifiers, SMT-LIB preamble parsing and parse-based interpreted sorts/functions
//! are implemented. Structured model extraction is available; the complete Prover
//! adapter covers push/pop and soft-constraint verification; custom options and trigger
//! repair remain explicit unsupported paths. Source default options are available
//! through `new_with_source_options`. The linked library is selected at build/run time;
//! pinned Silicon requires Z3 4.16.0.0, independently of the stdio executable.
//!
//! Z3_mk_context retains AST allocations until the final handle/context is dropped.
//! This avoids dangling references and per-AST reference management, but long-lived
//! contexts can retain more memory than a reference-counted Java binding.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::term_to_z3_api_converter::{NativeLiteral, NativeOp, NativeSort, Z3NativeContext};
use super::z3_prover_api::NativeZ3Solver;
use crate::interfaces::decider::prover::SatResult;
use crate::state::terms::Quantifier;
use std::{
    cell::RefCell,
    collections::HashMap,
    ffi::{CStr, CString, c_char, c_int, c_uint, c_void},
    fmt, ptr,
    rc::Rc,
};

type Raw = *mut c_void;
#[link(name = "z3")]
unsafe extern "C" {
    fn Z3_mk_config() -> Raw;
    fn Z3_del_config(c: Raw);
    fn Z3_set_param_value(c: Raw, name: *const c_char, value: *const c_char);
    fn Z3_mk_context(c: Raw) -> Raw;
    fn Z3_update_param_value(c: Raw, name: *const c_char, value: *const c_char);
    fn Z3_del_context(c: Raw);
    fn Z3_set_error_handler(c: Raw, h: Option<unsafe extern "C" fn(Raw, c_uint)>);
    fn Z3_get_error_code(c: Raw) -> c_uint;
    fn Z3_get_error_msg(c: Raw, e: c_uint) -> *const c_char;
    fn Z3_mk_string_symbol(c: Raw, s: *const c_char) -> Raw;
    fn Z3_mk_int_sort(c: Raw) -> Raw;
    fn Z3_mk_bool_sort(c: Raw) -> Raw;
    fn Z3_mk_real_sort(c: Raw) -> Raw;
    fn Z3_mk_uninterpreted_sort(c: Raw, n: Raw) -> Raw;
    fn Z3_mk_func_decl(c: Raw, n: Raw, count: c_uint, args: *const Raw, ret: Raw) -> Raw;
    fn Z3_mk_const(c: Raw, n: Raw, sort: Raw) -> Raw;
    fn Z3_mk_app(c: Raw, decl: Raw, count: c_uint, args: *const Raw) -> Raw;
    fn Z3_mk_numeral(c: Raw, n: *const c_char, sort: Raw) -> Raw;
    fn Z3_mk_true(c: Raw) -> Raw;
    fn Z3_mk_false(c: Raw) -> Raw;
    fn Z3_mk_unary_minus(c: Raw, a: Raw) -> Raw;
    fn Z3_mk_not(c: Raw, a: Raw) -> Raw;
    fn Z3_mk_int2real(c: Raw, a: Raw) -> Raw;
    fn Z3_mk_and(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_or(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_add(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_sub(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_mul(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_distinct(c: Raw, n: c_uint, a: *const Raw) -> Raw;
    fn Z3_mk_implies(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_eq(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_div(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_mod(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_lt(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_le(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_gt(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_ge(c: Raw, a: Raw, b: Raw) -> Raw;
    fn Z3_mk_ite(c: Raw, a: Raw, b: Raw, d: Raw) -> Raw;
    fn Z3_mk_constructor(
        c: Raw,
        name: Raw,
        recognizer: Raw,
        fields: c_uint,
        names: *const Raw,
        sorts: *const Raw,
        refs: *mut c_uint,
    ) -> Raw;
    fn Z3_mk_datatype(c: Raw, name: Raw, n: c_uint, constructors: *mut Raw) -> Raw;
    fn Z3_query_constructor(
        c: Raw,
        constructor: Raw,
        fields: c_uint,
        decl: *mut Raw,
        tester: *mut Raw,
        accessors: *mut Raw,
    );
    fn Z3_del_constructor(c: Raw, constructor: Raw);
    fn Z3_mk_pattern(c: Raw, n: c_uint, terms: *const Raw) -> Raw;
    fn Z3_to_app(c: Raw, ast: Raw) -> Raw;
    fn Z3_mk_quantifier_const_ex(
        c: Raw,
        forall: bool,
        weight: c_uint,
        qid: Raw,
        skid: Raw,
        n: c_uint,
        bound: *const Raw,
        np: c_uint,
        patterns: *const Raw,
        nn: c_uint,
        no_patterns: *const Raw,
        body: Raw,
    ) -> Raw;
    fn Z3_mk_solver(c: Raw) -> Raw;
    fn Z3_solver_inc_ref(c: Raw, s: Raw);
    fn Z3_solver_dec_ref(c: Raw, s: Raw);
    fn Z3_solver_assert(c: Raw, s: Raw, a: Raw);
    fn Z3_solver_push(c: Raw, s: Raw);
    fn Z3_solver_pop(c: Raw, s: Raw, n: c_uint);
    fn Z3_solver_check(c: Raw, s: Raw) -> c_int;
    fn Z3_solver_check_assumptions(c: Raw, s: Raw, n: c_uint, assumptions: *const Raw) -> c_int;
    fn Z3_solver_get_statistics(c: Raw, s: Raw) -> Raw;
    fn Z3_stats_inc_ref(c: Raw, s: Raw);
    fn Z3_stats_dec_ref(c: Raw, s: Raw);
    fn Z3_stats_size(c: Raw, s: Raw) -> c_uint;
    fn Z3_stats_get_key(c: Raw, s: Raw, i: c_uint) -> *const c_char;
    fn Z3_stats_is_uint(c: Raw, s: Raw, i: c_uint) -> bool;
    fn Z3_stats_get_uint_value(c: Raw, s: Raw, i: c_uint) -> c_uint;
    fn Z3_stats_is_double(c: Raw, s: Raw, i: c_uint) -> bool;
    fn Z3_stats_get_double_value(c: Raw, s: Raw, i: c_uint) -> f64;
    fn Z3_solver_get_model(c: Raw, s: Raw) -> Raw;
    fn Z3_model_inc_ref(c: Raw, m: Raw);
    fn Z3_model_dec_ref(c: Raw, m: Raw);
    fn Z3_model_to_string(c: Raw, m: Raw) -> *const c_char;
    fn Z3_model_get_num_consts(c: Raw, m: Raw) -> c_uint;
    fn Z3_model_get_const_decl(c: Raw, m: Raw, i: c_uint) -> Raw;
    fn Z3_model_get_const_interp(c: Raw, m: Raw, d: Raw) -> Raw;
    fn Z3_model_get_num_funcs(c: Raw, m: Raw) -> c_uint;
    fn Z3_model_get_func_decl(c: Raw, m: Raw, i: c_uint) -> Raw;
    fn Z3_model_get_func_interp(c: Raw, m: Raw, d: Raw) -> Raw;
    fn Z3_func_interp_get_num_entries(c: Raw, f: Raw) -> c_uint;
    fn Z3_func_interp_get_entry(c: Raw, f: Raw, i: c_uint) -> Raw;
    fn Z3_func_interp_get_else(c: Raw, f: Raw) -> Raw;
    fn Z3_func_entry_get_num_args(c: Raw, e: Raw) -> c_uint;
    fn Z3_func_entry_get_arg(c: Raw, e: Raw, i: c_uint) -> Raw;
    fn Z3_func_entry_get_value(c: Raw, e: Raw) -> Raw;
    fn Z3_get_decl_name(c: Raw, d: Raw) -> Raw;
    fn Z3_get_symbol_kind(c: Raw, s: Raw) -> c_uint;
    fn Z3_get_symbol_int(c: Raw, s: Raw) -> c_int;
    fn Z3_get_symbol_string(c: Raw, s: Raw) -> *const c_char;
    fn Z3_ast_to_string(c: Raw, a: Raw) -> *const c_char;
    fn Z3_is_numeral_ast(c: Raw, a: Raw) -> bool;
    fn Z3_get_numeral_string(c: Raw, a: Raw) -> *const c_char;
    fn Z3_get_sort_kind(c: Raw, s: Raw) -> c_uint;
    fn Z3_solver_get_reason_unknown(c: Raw, s: Raw) -> *const c_char;
    fn Z3_get_version(
        major: *mut c_uint,
        minor: *mut c_uint,
        build: *mut c_uint,
        revision: *mut c_uint,
    );
    fn Z3_mk_params(c: Raw) -> Raw;
    fn Z3_params_inc_ref(c: Raw, p: Raw);
    fn Z3_params_dec_ref(c: Raw, p: Raw);
    fn Z3_params_set_bool(c: Raw, p: Raw, name: Raw, value: bool);
    fn Z3_params_set_uint(c: Raw, p: Raw, name: Raw, value: c_uint);
    fn Z3_params_set_double(c: Raw, p: Raw, name: Raw, value: f64);
    fn Z3_params_set_symbol(c: Raw, p: Raw, name: Raw, value: Raw);
    fn Z3_solver_get_param_descrs(c: Raw, solver: Raw) -> Raw;
    fn Z3_param_descrs_get_kind(c: Raw, descrs: Raw, name: Raw) -> c_uint;
    fn Z3_solver_set_params(c: Raw, solver: Raw, p: Raw);
    fn Z3_parse_smtlib2_string(
        c: Raw,
        input: *const c_char,
        ns: c_uint,
        sn: *const Raw,
        sorts: *const Raw,
        nd: c_uint,
        dn: *const Raw,
        decls: *const Raw,
    ) -> Raw;
    fn Z3_ast_vector_inc_ref(c: Raw, v: Raw);
    fn Z3_ast_vector_dec_ref(c: Raw, v: Raw);
    fn Z3_ast_vector_size(c: Raw, v: Raw) -> c_uint;
    fn Z3_ast_vector_get(c: Raw, v: Raw, i: c_uint) -> Raw;
    fn Z3_get_app_arg(c: Raw, app: Raw, index: c_uint) -> Raw;
    fn Z3_get_app_decl(c: Raw, app: Raw) -> Raw;
    fn Z3_get_app_num_args(c: Raw, app: Raw) -> c_uint;
    fn Z3_get_sort(c: Raw, ast: Raw) -> Raw;
    fn Z3_sort_to_string(c: Raw, sort: Raw) -> *const c_char;
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeZ3Error {
    InvalidString,
    ContextMismatch,
    InvalidHandleKind,
    InvalidArity,
    InvalidCount,
    Solver(String),
    Unsupported(&'static str),
}
impl fmt::Display for NativeZ3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for NativeZ3Error {}
unsafe extern "C" fn ignore_error(_: Raw, _: c_uint) {}
struct Context(Raw);
impl Drop for Context {
    fn drop(&mut self) {
        unsafe { Z3_del_context(self.0) }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HandleKind {
    Sort,
    Expr,
    Function,
}
#[derive(Clone)]
pub struct Handle {
    context: Rc<Context>,
    raw: Raw,
    kind: HandleKind,
}
impl PartialEq for Handle {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.context, &other.context)
            && self.raw == other.raw
            && self.kind == other.kind
    }
}
impl Eq for Handle {}
impl fmt::Debug for Handle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Z3Handle({:p})", self.raw)
    }
}
/// A model keeps its originating context and its own Z3 model reference alive.
struct RetainedModel {
    context: Rc<Context>,
    raw: Raw,
}
impl Drop for RetainedModel {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.context.0, self.raw) }
    }
}
#[derive(Clone)]
struct Snap {
    sort: Handle,
    unit: Handle,
    combine: Handle,
    first: Handle,
    second: Handle,
}
/// Every returned handle retains its context; Rc deliberately makes the driver and
/// handles !Send/!Sync, so Z3 contexts cannot be moved between verification threads.
pub struct LinkedZ3 {
    context: Rc<Context>,
    solver: Raw,
    source_options: bool,
    functions: HashMap<(String, Vec<usize>, usize), Handle>,
    smt_functions: HashMap<(String, Vec<usize>), (Handle, Vec<Handle>)>,
    snap: RefCell<Option<Snap>>,
}
impl LinkedZ3 {
    pub fn new() -> Result<Self, NativeZ3Error> {
        Self::create(false)
    }
    /// Initialize the solver with the pinned Z3ProverAPI's standard options.
    pub fn new_with_source_options() -> Result<Self, NativeZ3Error> {
        Self::create(true)
    }
    fn create(source_options: bool) -> Result<Self, NativeZ3Error> {
        unsafe {
            let config = Z3_mk_config();
            if config.is_null() {
                return Err(NativeZ3Error::Solver("Z3_mk_config failed".into()));
            }
            if source_options {
                Z3_set_param_value(config, c"auto_config".as_ptr(), c"false".as_ptr());
                Z3_set_param_value(config, c"type_check".as_ptr(), c"true".as_ptr());
            }
            let raw = Z3_mk_context(config);
            Z3_del_config(config);
            if raw.is_null() {
                return Err(NativeZ3Error::Solver("Z3_mk_context failed".into()));
            }
            Z3_set_error_handler(raw, Some(ignore_error));
            let context = Rc::new(Context(raw));
            let solver = Z3_mk_solver(raw);
            if solver.is_null() {
                return Err(NativeZ3Error::Solver("Z3_mk_solver failed".into()));
            }
            Z3_solver_inc_ref(raw, solver);
            let this = Self {
                context,
                solver,
                source_options,
                functions: HashMap::new(),
                smt_functions: HashMap::new(),
                snap: RefCell::new(None),
            };
            this.checked()?;
            if source_options {
                this.set_source_solver_options(&[], false)?;
            }
            Ok(this)
        }
    }
    fn set_source_solver_options(
        &self,
        custom: &[(String, String)],
        disable_nonlinear: bool,
    ) -> Result<(), NativeZ3Error> {
        struct Params {
            context: Rc<Context>,
            raw: Raw,
        }
        impl Drop for Params {
            fn drop(&mut self) {
                unsafe { Z3_params_dec_ref(self.context.0, self.raw) }
            }
        }
        let c = self.context.0;
        let raw = unsafe { Z3_mk_params(c) };
        self.checked()?;
        if raw.is_null() {
            return Err(NativeZ3Error::Solver("Z3 returned no parameters".into()));
        }
        unsafe { Z3_params_inc_ref(c, raw) };
        self.checked()?;
        let _owned = Params {
            context: self.context.clone(),
            raw,
        };
        for (name, value) in [("delay_units", true), ("mbqi", false), ("model.v2", true)] {
            let name = self.symbol(name)?;
            unsafe { Z3_params_set_bool(c, raw, name, value) };
            self.checked()?;
        }
        for (name, value) in [
            ("case_split", 3),
            ("qi.max_multi_patterns", 1000),
            ("arith.solver", 2),
        ] {
            let name = self.symbol(name)?;
            unsafe { Z3_params_set_uint(c, raw, name, value) };
            self.checked()?;
        }
        let name = self.symbol("qi.eager_threshold")?;
        unsafe { Z3_params_set_double(c, raw, name, 100.0) };
        self.checked()?;
        if disable_nonlinear {
            let name = self.symbol("arith.nl")?;
            unsafe { Z3_params_set_bool(c, raw, name, false) };
            self.checked()?;
        }
        let descrs = unsafe { Z3_solver_get_param_descrs(c, self.solver) };
        self.checked()?;
        for (original, value) in custom {
            let key = original.strip_prefix("smt.").unwrap_or(original);
            let name = self.symbol(key)?;
            let kind = unsafe { Z3_param_descrs_get_kind(c, descrs, name) };
            self.checked()?;
            let invalid = || {
                NativeZ3Error::Solver(format!(
                    "invalid value {value:?} for Z3 parameter {original}"
                ))
            };
            unsafe {
                match kind {
                    0 => Z3_params_set_uint(c, raw, name, value.parse().map_err(|_| invalid())?),
                    1 => Z3_params_set_bool(c, raw, name, value.parse().map_err(|_| invalid())?),
                    2 => Z3_params_set_double(c, raw, name, value.parse().map_err(|_| invalid())?),
                    4 => Z3_params_set_symbol(c, raw, name, self.symbol(value)?),
                    _ => {
                        return Err(NativeZ3Error::Solver(format!(
                            "unknown or unsupported Z3 parameter {original}"
                        )));
                    }
                }
            }
            self.checked()?;
        }
        unsafe { Z3_solver_set_params(c, self.solver, raw) };
        self.checked()
    }
    fn randomize_seed(&self) -> Result<(), NativeZ3Error> {
        use std::hash::{BuildHasher, Hasher};
        let seed = (std::collections::hash_map::RandomState::new()
            .build_hasher()
            .finish()
            % 10_000) as u32;
        let c = self.context.0;
        let params = unsafe { Z3_mk_params(c) };
        self.checked()?;
        if params.is_null() {
            return Err(NativeZ3Error::Solver("Z3 returned no parameters".into()));
        }
        unsafe { Z3_params_inc_ref(c, params) };
        let result = (|| {
            let key = self.symbol("random_seed")?;
            unsafe { Z3_params_set_uint(c, params, key, seed) };
            self.checked()?;
            unsafe { Z3_solver_set_params(c, self.solver, params) };
            self.checked()
        })();
        unsafe { Z3_params_dec_ref(c, params) };
        result
    }
    /// Linked library version; this may differ from the configured stdio executable.
    pub fn library_version() -> (u32, u32, u32, u32) {
        let (mut major, mut minor, mut build, mut revision) = (0, 0, 0, 0);
        unsafe { Z3_get_version(&mut major, &mut minor, &mut build, &mut revision) };
        (major, minor, build, revision)
    }
    /// Obtain Z3's textual model from the most recent satisfiable check.
    /// This raw string is useful for diagnostics; `model()` returns Silver entries.
    pub fn model_text(&self) -> Result<String, NativeZ3Error> {
        let c = self.context.0;
        unsafe {
            let model = Z3_solver_get_model(c, self.solver);
            self.checked()?;
            if model.is_null() {
                return Err(NativeZ3Error::Solver("Z3 returned no model".into()));
            }
            Z3_model_inc_ref(c, model);
            let text = Z3_model_to_string(c, model);
            let result = if text.is_null() {
                Err(NativeZ3Error::Solver("Z3 returned no model text".into()))
            } else {
                Ok(CStr::from_ptr(text).to_string_lossy().into_owned())
            };
            Z3_model_dec_ref(c, model);
            self.checked()?;
            result
        }
    }
    fn retain_model(&self) -> Result<RetainedModel, NativeZ3Error> {
        let c = self.context.0;
        let raw = unsafe { Z3_solver_get_model(c, self.solver) };
        self.checked()?;
        if raw.is_null() {
            return Err(NativeZ3Error::Solver("Z3 returned no model".into()));
        }
        unsafe { Z3_model_inc_ref(c, raw) };
        self.checked()?;
        Ok(RetainedModel {
            context: self.context.clone(),
            raw,
        })
    }
    /// Convert constants and finite function interpretations to Silver's model,
    /// preserving source rational spelling and reporting unsupported values as errors.
    pub fn model(
        &self,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, NativeZ3Error> {
        self.model_from_retained(&self.retain_model()?)
    }
    fn model_from_retained(
        &self,
        guard: &RetainedModel,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, NativeZ3Error> {
        use ferrum_silver::verifier::verification_error::{
            MapEntry, Model, ModelEntry, ValueEntry,
        };
        if !Rc::ptr_eq(&self.context, &guard.context) {
            return Err(NativeZ3Error::ContextMismatch);
        }
        let c = self.context.0;
        let value = |ast: Raw| -> Result<ValueEntry, NativeZ3Error> {
            if ast.is_null() {
                return Err(NativeZ3Error::Solver("Z3 returned no model value".into()));
            }
            let sort = unsafe { Z3_get_sort(c, ast) };
            self.checked()?;
            let real = unsafe { Z3_get_sort_kind(c, sort) } == 3;
            self.checked()?;
            let numeral = unsafe { Z3_is_numeral_ast(c, ast) };
            self.checked()?;
            let text = unsafe {
                if real && numeral {
                    Z3_get_numeral_string(c, ast)
                } else {
                    Z3_ast_to_string(c, ast)
                }
            };
            self.checked()?;
            if text.is_null() {
                return Err(NativeZ3Error::Solver(
                    "Z3 returned no model value text".into(),
                ));
            }
            let mut text = unsafe { CStr::from_ptr(text) }
                .to_string_lossy()
                .into_owned();
            if real && numeral {
                let (num, den) = text.split_once('/').unwrap_or((&text, "1"));
                text = format!("(/ {num} {den})");
            }
            let mut parsed =
                ferrum_silver::verifier::model_parser::parse_model(&format!("value -> {text}"))
                    .map_err(|e| NativeZ3Error::Solver(format!("model value {text}: {e:?}")))?;
            match parsed.entries.remove("value") {
                Some(ModelEntry::Value(v)) => Ok(v),
                _ => Err(NativeZ3Error::Solver("invalid parsed model value".into())),
            }
        };
        let name = |decl: Raw| -> Result<String, NativeZ3Error> {
            if decl.is_null() {
                return Err(NativeZ3Error::Solver(
                    "Z3 returned no model declaration".into(),
                ));
            }
            let sym = unsafe { Z3_get_decl_name(c, decl) };
            self.checked()?;
            let kind = unsafe { Z3_get_symbol_kind(c, sym) };
            self.checked()?;
            match kind {
                0 => {
                    let n = unsafe { Z3_get_symbol_int(c, sym) };
                    self.checked()?;
                    Ok(n.to_string())
                }
                1 => {
                    let text = unsafe { Z3_get_symbol_string(c, sym) };
                    self.checked()?;
                    if text.is_null() {
                        return Err(NativeZ3Error::Solver("Z3 returned no symbol name".into()));
                    }
                    Ok(unsafe { CStr::from_ptr(text) }
                        .to_string_lossy()
                        .into_owned())
                }
                _ => Err(NativeZ3Error::Solver("unexpected Z3 symbol kind".into())),
            }
        };
        let mut entries = HashMap::new();
        let count = unsafe { Z3_model_get_num_consts(c, guard.raw) };
        self.checked()?;
        for i in 0..count {
            let decl = unsafe { Z3_model_get_const_decl(c, guard.raw, i) };
            self.checked()?;
            let key = name(decl)?;
            let interpretation = unsafe { Z3_model_get_const_interp(c, guard.raw, decl) };
            self.checked()?;
            entries.insert(key, ModelEntry::Value(value(interpretation)?));
        }
        let count = unsafe { Z3_model_get_num_funcs(c, guard.raw) };
        self.checked()?;
        for i in 0..count {
            let decl = unsafe { Z3_model_get_func_decl(c, guard.raw, i) };
            self.checked()?;
            let key = name(decl)?;
            let interp = unsafe { Z3_model_get_func_interp(c, guard.raw, decl) };
            self.checked()?;
            if interp.is_null() {
                return Err(NativeZ3Error::Solver(
                    "Z3 returned no function interpretation".into(),
                ));
            }
            let count = unsafe { Z3_func_interp_get_num_entries(c, interp) };
            self.checked()?;
            let mut options = HashMap::new();
            for j in 0..count {
                let entry = unsafe { Z3_func_interp_get_entry(c, interp, j) };
                self.checked()?;
                let n = unsafe { Z3_func_entry_get_num_args(c, entry) };
                self.checked()?;
                let mut args = Vec::new();
                for k in 0..n {
                    let arg = unsafe { Z3_func_entry_get_arg(c, entry, k) };
                    self.checked()?;
                    args.push(value(arg)?);
                }
                let result = unsafe { Z3_func_entry_get_value(c, entry) };
                self.checked()?;
                options.insert(args, value(result)?);
            }
            let default = unsafe { Z3_func_interp_get_else(c, interp) };
            self.checked()?;
            entries.insert(
                key,
                ModelEntry::Map(MapEntry {
                    options,
                    default: value(default)?,
                }),
            );
        }
        Ok(Model { entries })
    }
    pub fn statistics(&self) -> Result<Vec<(String, String)>, NativeZ3Error> {
        struct Stats {
            context: Rc<Context>,
            raw: Raw,
        }
        impl Drop for Stats {
            fn drop(&mut self) {
                unsafe { Z3_stats_dec_ref(self.context.0, self.raw) }
            }
        }
        let c = self.context.0;
        let raw = unsafe { Z3_solver_get_statistics(c, self.solver) };
        self.checked()?;
        if raw.is_null() {
            return Err(NativeZ3Error::Solver("Z3 returned no statistics".into()));
        }
        unsafe { Z3_stats_inc_ref(c, raw) };
        self.checked()?;
        let stats = Stats {
            context: self.context.clone(),
            raw,
        };
        let count = unsafe { Z3_stats_size(c, stats.raw) };
        self.checked()?;
        let mut result = Vec::new();
        for i in 0..count {
            let key = unsafe { Z3_stats_get_key(c, stats.raw, i) };
            self.checked()?;
            if key.is_null() {
                return Err(NativeZ3Error::Solver("Z3 returned no statistic key".into()));
            }
            let key = unsafe { CStr::from_ptr(key) }
                .to_string_lossy()
                .into_owned();
            let is_uint = unsafe { Z3_stats_is_uint(c, stats.raw, i) };
            self.checked()?;
            let value = if is_uint {
                let v = unsafe { Z3_stats_get_uint_value(c, stats.raw, i) };
                self.checked()?;
                v.to_string()
            } else {
                let is_double = unsafe { Z3_stats_is_double(c, stats.raw, i) };
                self.checked()?;
                if !is_double {
                    return Err(NativeZ3Error::Solver("unknown Z3 statistic type".into()));
                }
                let v = unsafe { Z3_stats_get_double_value(c, stats.raw, i) };
                self.checked()?;
                v.to_string()
            };
            result.push((key, value));
        }
        Ok(result)
    }
    pub fn reason_unknown(&self) -> Result<String, NativeZ3Error> {
        let text = unsafe { Z3_solver_get_reason_unknown(self.context.0, self.solver) };
        self.checked()?;
        if text.is_null() {
            return Err(NativeZ3Error::Solver(
                "Z3 returned no unknown reason".into(),
            ));
        }
        Ok(unsafe { CStr::from_ptr(text) }
            .to_string_lossy()
            .into_owned())
    }
    /// Z3's one-shot check-under-assumptions, used by source soft assertions.
    pub fn check_assumptions(&self, assumptions: &[Handle]) -> Result<SatResult, NativeZ3Error> {
        let raw = self.raws(assumptions, HandleKind::Expr)?;
        let result = unsafe {
            Z3_solver_check_assumptions(
                self.context.0,
                self.solver,
                Self::count(raw.len())?,
                raw.as_ptr(),
            )
        };
        self.checked()?;
        match result {
            -1 => Ok(SatResult::Unsat),
            0 => Ok(SatResult::Unknown),
            1 => Ok(SatResult::Sat),
            _ => Err(NativeZ3Error::Solver(format!(
                "unexpected check result {result}"
            ))),
        }
    }
    fn checked(&self) -> Result<(), NativeZ3Error> {
        unsafe {
            let code = Z3_get_error_code(self.context.0);
            if code == 0 {
                Ok(())
            } else {
                let message = Z3_get_error_msg(self.context.0, code);
                Err(NativeZ3Error::Solver(if message.is_null() {
                    format!("Z3 error {code}")
                } else {
                    CStr::from_ptr(message).to_string_lossy().into_owned()
                }))
            }
        }
    }
    fn handle(&self, raw: Raw, kind: HandleKind) -> Result<Handle, NativeZ3Error> {
        self.checked()?;
        if raw.is_null() {
            return Err(NativeZ3Error::Solver("Z3 returned a null handle".into()));
        }
        Ok(Handle {
            context: self.context.clone(),
            raw,
            kind,
        })
    }
    fn check_handle(&self, value: &Handle, expected: HandleKind) -> Result<Raw, NativeZ3Error> {
        if Rc::ptr_eq(&self.context, &value.context) {
            if value.kind != expected {
                return Err(NativeZ3Error::InvalidHandleKind);
            }
            Ok(value.raw)
        } else {
            Err(NativeZ3Error::ContextMismatch)
        }
    }
    fn symbol(&self, text: &str) -> Result<Raw, NativeZ3Error> {
        let text = CString::new(text).map_err(|_| NativeZ3Error::InvalidString)?;
        let value = unsafe { Z3_mk_string_symbol(self.context.0, text.as_ptr()) };
        self.checked()?;
        if value.is_null() {
            Err(NativeZ3Error::Solver("null symbol".into()))
        } else {
            Ok(value)
        }
    }
    fn count(n: usize) -> Result<c_uint, NativeZ3Error> {
        n.try_into().map_err(|_| NativeZ3Error::InvalidCount)
    }
    fn raws(&self, values: &[Handle], expected: HandleKind) -> Result<Vec<Raw>, NativeZ3Error> {
        values
            .iter()
            .map(|x| self.check_handle(x, expected))
            .collect()
    }
    fn app(&self, f: &Handle, args: &[Handle]) -> Result<Handle, NativeZ3Error> {
        let f = self.check_handle(f, HandleKind::Function)?;
        let args = self.raws(args, HandleKind::Expr)?;
        self.handle(
            unsafe { Z3_mk_app(self.context.0, f, Self::count(args.len())?, args.as_ptr()) },
            HandleKind::Expr,
        )
    }
    // Parse in the same context but without caller declarations, as the upstream
    // builtin and SMT-sort workaround does. The non-reference-counted context owns
    // ASTs; the parser vector itself is explicitly retained until extraction.
    fn parse_single_assertion(&self, text: &str) -> Result<Handle, NativeZ3Error> {
        let text = CString::new(text).map_err(|_| NativeZ3Error::InvalidString)?;
        let c = self.context.0;
        unsafe {
            let vector = Z3_parse_smtlib2_string(
                c,
                text.as_ptr(),
                0,
                ptr::null(),
                ptr::null(),
                0,
                ptr::null(),
                ptr::null(),
            );
            self.checked()?;
            if vector.is_null() {
                return Err(NativeZ3Error::Solver("null parsed assertion vector".into()));
            }
            Z3_ast_vector_inc_ref(c, vector);
            let size = Z3_ast_vector_size(c, vector);
            let result = if size == 1 {
                self.handle(Z3_ast_vector_get(c, vector, 0), HandleKind::Expr)
            } else {
                Err(NativeZ3Error::Solver(format!(
                    "expected one parsed assertion, got {size}"
                )))
            };
            Z3_ast_vector_dec_ref(c, vector);
            result
        }
    }
    fn parsed_first_operand(&self, text: &str) -> Result<Handle, NativeZ3Error> {
        let assertion = self.parse_single_assertion(text)?;
        let app = unsafe {
            Z3_to_app(
                self.context.0,
                self.check_handle(&assertion, HandleKind::Expr)?,
            )
        };
        self.checked()?;
        self.handle(
            unsafe { Z3_get_app_arg(self.context.0, app, 0) },
            HandleKind::Expr,
        )
    }
    fn parsed_sort(&self, text: &str) -> Result<Handle, NativeZ3Error> {
        let expr = self.parsed_first_operand(&format!(
            "(declare-const workaround {text}) (assert (= workaround workaround))"
        ))?;
        self.handle(
            unsafe { Z3_get_sort(self.context.0, self.check_handle(&expr, HandleKind::Expr)?) },
            HandleKind::Sort,
        )
    }
    fn parsed_builtin(
        &mut self,
        name: &str,
        sorts: &[Handle],
        args: &[Handle],
    ) -> Result<Handle, NativeZ3Error> {
        let raw_sorts = self.raws(sorts, HandleKind::Sort)?;
        let key = (
            name.to_string(),
            raw_sorts.iter().map(|v| *v as usize).collect::<Vec<_>>(),
        );
        if let Some((function, extra)) = self.smt_functions.get(&key) {
            let mut actual = extra.clone();
            actual.extend_from_slice(args);
            return self.app(function, &actual);
        }
        let mut declarations = String::from("(define-sort $Perm () Real) ");
        for (i, sort) in raw_sorts.iter().enumerate() {
            let text = unsafe { Z3_sort_to_string(self.context.0, *sort) };
            self.checked()?;
            if text.is_null() {
                return Err(NativeZ3Error::Solver("null sort rendering".into()));
            }
            let text = unsafe { CStr::from_ptr(text) }.to_string_lossy();
            declarations.push_str(&format!("(declare-const workaround{i} {text}) "));
        }
        let application = if args.is_empty() {
            name.to_string()
        } else {
            format!(
                "({name} {})",
                (0..args.len())
                    .map(|i| format!("workaround{i}"))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        };
        let expr = self.parsed_first_operand(&format!(
            "{declarations}(assert (= {application} {application}))"
        ))?;
        let app = unsafe { Z3_to_app(self.context.0, self.check_handle(&expr, HandleKind::Expr)?) };
        self.checked()?;
        let function = self.handle(
            unsafe { Z3_get_app_decl(self.context.0, app) },
            HandleKind::Function,
        )?;
        let count = unsafe { Z3_get_app_num_args(self.context.0, app) } as usize;
        self.checked()?;
        if count < args.len() {
            return Err(NativeZ3Error::InvalidArity);
        }
        let mut extra = Vec::new();
        for i in 0..count - args.len() {
            extra.push(self.handle(
                unsafe { Z3_get_app_arg(self.context.0, app, Self::count(i)?) },
                HandleKind::Expr,
            )?);
        }
        self.smt_functions
            .insert(key, (function.clone(), extra.clone()));
        extra.extend_from_slice(args);
        self.app(&function, &extra)
    }
    fn snap(&self) -> Result<Snap, NativeZ3Error> {
        if let Some(s) = self.snap.borrow().as_ref() {
            return Ok(s.clone());
        }
        struct Constructors {
            context: Rc<Context>,
            values: Vec<Raw>,
        }
        impl Drop for Constructors {
            fn drop(&mut self) {
                for value in &self.values {
                    unsafe { Z3_del_constructor(self.context.0, *value) }
                }
            }
        }
        unsafe {
            let c = self.context.0;
            let mut owned = Constructors {
                context: self.context.clone(),
                values: Vec::new(),
            };
            let n = self.symbol("$Snap.unit")?;
            let test = self.symbol("is_$Snap.unit")?;
            let unit = Z3_mk_constructor(c, n, test, 0, ptr::null(), ptr::null(), ptr::null_mut());
            if !unit.is_null() {
                owned.values.push(unit);
            }
            self.checked()?;
            let names = [self.symbol("$Snap.first")?, self.symbol("$Snap.second")?];
            let sorts = [ptr::null_mut(), ptr::null_mut()];
            let mut refs = [0, 0];
            let combine = Z3_mk_constructor(
                c,
                self.symbol("$Snap.combine")?,
                self.symbol("is_$Snap.combine")?,
                2,
                names.as_ptr(),
                sorts.as_ptr(),
                refs.as_mut_ptr(),
            );
            if !combine.is_null() {
                owned.values.push(combine);
            }
            self.checked()?;
            let mut constructors = [unit, combine];
            let raw_sort = Z3_mk_datatype(c, self.symbol("$Snap")?, 2, constructors.as_mut_ptr());
            self.checked()?;
            let mut unit_decl = ptr::null_mut();
            let mut tester = ptr::null_mut();
            Z3_query_constructor(c, unit, 0, &mut unit_decl, &mut tester, ptr::null_mut());
            self.checked()?;
            let mut combine_decl = ptr::null_mut();
            let mut accessors = [ptr::null_mut(), ptr::null_mut()];
            Z3_query_constructor(
                c,
                combine,
                2,
                &mut combine_decl,
                &mut tester,
                accessors.as_mut_ptr(),
            );
            self.checked()?;
            drop(owned);
            let snap = Snap {
                sort: self.handle(raw_sort, HandleKind::Sort)?,
                unit: self.handle(unit_decl, HandleKind::Function)?,
                combine: self.handle(combine_decl, HandleKind::Function)?,
                first: self.handle(accessors[0], HandleKind::Function)?,
                second: self.handle(accessors[1], HandleKind::Function)?,
            };
            *self.snap.borrow_mut() = Some(snap.clone());
            Ok(snap)
        }
    }
}
impl Drop for LinkedZ3 {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.context.0, self.solver) }
    }
}
impl Z3NativeContext for LinkedZ3 {
    type Sort = Handle;
    type Expr = Handle;
    type Function = Handle;
    type Error = NativeZ3Error;
    fn function(
        &mut self,
        name: &str,
        args: &[Handle],
        result: &Handle,
    ) -> Result<Handle, Self::Error> {
        let raw_args = self.raws(args, HandleKind::Sort)?;
        let ret = self.check_handle(result, HandleKind::Sort)?;
        let key = (
            name.to_string(),
            raw_args.iter().map(|p| *p as usize).collect(),
            ret as usize,
        );
        if let Some(v) = self.functions.get(&key) {
            return Ok(v.clone());
        }
        let symbol = self.symbol(name)?;
        let result = self.handle(
            unsafe {
                Z3_mk_func_decl(
                    self.context.0,
                    symbol,
                    Self::count(raw_args.len())?,
                    raw_args.as_ptr(),
                    ret,
                )
            },
            HandleKind::Function,
        )?;
        self.functions.insert(key, result.clone());
        Ok(result)
    }
    fn sort(&mut self, spec: NativeSort) -> Result<Handle, Self::Error> {
        let c = self.context.0;
        match spec {
            NativeSort::Int => self.handle(unsafe { Z3_mk_int_sort(c) }, HandleKind::Sort),
            NativeSort::Bool => self.handle(unsafe { Z3_mk_bool_sort(c) }, HandleKind::Sort),
            NativeSort::Real => self.handle(unsafe { Z3_mk_real_sort(c) }, HandleKind::Sort),
            NativeSort::Snap => Ok(self.snap()?.sort),
            NativeSort::Uninterpreted(name) => {
                let n = self.symbol(&name)?;
                self.handle(unsafe { Z3_mk_uninterpreted_sort(c, n) }, HandleKind::Sort)
            }
            NativeSort::ParsedSmt(text) => self.parsed_sort(&text),
        }
    }
    fn literal(&mut self, literal: NativeLiteral, sort: &Handle) -> Result<Handle, Self::Error> {
        let s = self.check_handle(sort, HandleKind::Sort)?;
        let c = self.context.0;
        match literal {
            NativeLiteral::Integer(n) => {
                let n = CString::new(n).map_err(|_| NativeZ3Error::InvalidString)?;
                self.handle(unsafe { Z3_mk_numeral(c, n.as_ptr(), s) }, HandleKind::Expr)
            }
            NativeLiteral::Real(n) => {
                let n = CString::new(n.to_string()).unwrap();
                self.handle(unsafe { Z3_mk_numeral(c, n.as_ptr(), s) }, HandleKind::Expr)
            }
            NativeLiteral::Bool(true) => self.handle(unsafe { Z3_mk_true(c) }, HandleKind::Expr),
            NativeLiteral::Bool(false) => self.handle(unsafe { Z3_mk_false(c) }, HandleKind::Expr),
            NativeLiteral::SnapUnit => {
                let snap = self.snap()?;
                self.app(&snap.unit, &[])
            }
        }
    }
    fn constant(&mut self, name: &str, sort: &Handle) -> Result<Handle, Self::Error> {
        let n = self.symbol(name)?;
        let s = self.check_handle(sort, HandleKind::Sort)?;
        self.handle(
            unsafe { Z3_mk_const(self.context.0, n, s) },
            HandleKind::Expr,
        )
    }
    fn builtin(&mut self, op: NativeOp, args: &[Handle]) -> Result<Handle, Self::Error> {
        let c = self.context.0;
        let raw = self.raws(args, HandleKind::Expr)?;
        let n = Self::count(raw.len())?;
        let unary = || {
            if raw.len() == 1 {
                Ok(raw[0])
            } else {
                Err(NativeZ3Error::InvalidArity)
            }
        };
        let binary = || {
            if raw.len() == 2 {
                Ok((raw[0], raw[1]))
            } else {
                Err(NativeZ3Error::InvalidArity)
            }
        };
        let result = unsafe {
            match op {
                NativeOp::Neg => Z3_mk_unary_minus(c, unary()?),
                NativeOp::Not => Z3_mk_not(c, unary()?),
                NativeOp::ToReal => Z3_mk_int2real(c, unary()?),
                NativeOp::And => Z3_mk_and(c, n, raw.as_ptr()),
                NativeOp::Or => Z3_mk_or(c, n, raw.as_ptr()),
                NativeOp::Add => Z3_mk_add(c, n, raw.as_ptr()),
                NativeOp::Sub => Z3_mk_sub(c, n, raw.as_ptr()),
                NativeOp::Mul => Z3_mk_mul(c, n, raw.as_ptr()),
                NativeOp::Distinct => Z3_mk_distinct(c, n, raw.as_ptr()),
                NativeOp::Ite => {
                    if raw.len() != 3 {
                        return Err(NativeZ3Error::InvalidArity);
                    }
                    Z3_mk_ite(c, raw[0], raw[1], raw[2])
                }
                NativeOp::SnapCombine | NativeOp::SnapFirst | NativeOp::SnapSecond => {
                    let snap = self.snap()?;
                    return self.app(
                        match op {
                            NativeOp::SnapCombine => &snap.combine,
                            NativeOp::SnapFirst => &snap.first,
                            _ => &snap.second,
                        },
                        args,
                    );
                }
                other => {
                    let (a, b) = binary()?;
                    match other {
                        NativeOp::Implies => Z3_mk_implies(c, a, b),
                        NativeOp::Equal => Z3_mk_eq(c, a, b),
                        NativeOp::Div => Z3_mk_div(c, a, b),
                        NativeOp::Mod => Z3_mk_mod(c, a, b),
                        NativeOp::Less => Z3_mk_lt(c, a, b),
                        NativeOp::LessEqual => Z3_mk_le(c, a, b),
                        NativeOp::Greater => Z3_mk_gt(c, a, b),
                        NativeOp::GreaterEqual => Z3_mk_ge(c, a, b),
                        _ => unreachable!(),
                    }
                }
            }
        };
        self.handle(result, HandleKind::Expr)
    }
    fn application(
        &mut self,
        name: &str,
        arg_sorts: &[Handle],
        result: &Handle,
        args: &[Handle],
        smt_builtin: bool,
    ) -> Result<Handle, Self::Error> {
        if args.len() != arg_sorts.len() {
            return Err(NativeZ3Error::InvalidArity);
        }
        self.check_handle(result, HandleKind::Sort)?;
        if smt_builtin {
            return self.parsed_builtin(name, arg_sorts, args);
        }
        let fun = self.function(name, arg_sorts, result)?;
        self.app(&fun, args)
    }
    fn quantifier(
        &mut self,
        q: Quantifier,
        vars: &[Handle],
        body: &Handle,
        patterns: &[Vec<Handle>],
        name: &str,
        weight: i32,
    ) -> Result<Handle, Self::Error> {
        let c = self.context.0;
        let body = self.check_handle(body, HandleKind::Expr)?;
        let vars = self.raws(vars, HandleKind::Expr)?;
        let mut bound = Vec::new();
        for v in vars {
            let a = unsafe { Z3_to_app(c, v) };
            self.checked()?;
            bound.push(a)
        }
        let mut native_patterns = Vec::new();
        for p in patterns {
            let p = self.raws(p, HandleKind::Expr)?;
            let v = unsafe { Z3_mk_pattern(c, Self::count(p.len())?, p.as_ptr()) };
            self.checked()?;
            native_patterns.push(v)
        }
        let id = if name.is_empty() {
            ptr::null_mut()
        } else {
            self.symbol(name)?
        };
        let weight = c_uint::try_from(weight).map_err(|_| NativeZ3Error::InvalidCount)?;
        self.handle(
            unsafe {
                Z3_mk_quantifier_const_ex(
                    c,
                    matches!(q, Quantifier::Forall),
                    weight,
                    id,
                    ptr::null_mut(),
                    Self::count(bound.len())?,
                    bound.as_ptr(),
                    Self::count(native_patterns.len())?,
                    native_patterns.as_ptr(),
                    0,
                    ptr::null(),
                    body,
                )
            },
            HandleKind::Expr,
        )
    }
}
impl NativeZ3Solver for LinkedZ3 {
    fn parse_and_add_preamble(
        &mut self,
        commands: &[String],
        sorts: &[(String, Handle)],
        functions: &[(String, Handle)],
    ) -> Result<(), Self::Error> {
        let mut sn = Vec::new();
        let mut sv = Vec::new();
        for (n, v) in sorts {
            sn.push(self.symbol(n)?);
            sv.push(self.check_handle(v, HandleKind::Sort)?)
        }
        let mut dn = Vec::new();
        let mut dv = Vec::new();
        for (n, v) in functions {
            dn.push(self.symbol(n)?);
            dv.push(self.check_handle(v, HandleKind::Function)?)
        }
        let prefix = if self.source_options {
            "(set-option :auto_config false)\n(set-option :type_check true)\n(set-option :smt.delay_units true)\n(set-option :smt.mbqi false)\n(set-option :model.v2 true)\n(set-option :smt.case_split 3)\n(set-option :smt.qi.max_multi_patterns 1000)\n(set-option :smt.arith.solver 2)\n(set-option :smt.qi.eager_threshold 100.0)\n"
        } else {
            ""
        };
        let text = CString::new(format!("{prefix}{}", commands.join("\n")))
            .map_err(|_| NativeZ3Error::InvalidString)?;
        let c = self.context.0;
        unsafe {
            let vec = Z3_parse_smtlib2_string(
                c,
                text.as_ptr(),
                Self::count(sn.len())?,
                sn.as_ptr(),
                sv.as_ptr(),
                Self::count(dn.len())?,
                dn.as_ptr(),
                dv.as_ptr(),
            );
            self.checked()?;
            if vec.is_null() {
                return Err(NativeZ3Error::Solver("null parsed preamble".into()));
            }
            Z3_ast_vector_inc_ref(c, vec);
            let count = Z3_ast_vector_size(c, vec);
            for i in 0..count {
                let a = Z3_ast_vector_get(c, vec, i);
                Z3_solver_assert(c, self.solver, a);
                if let Err(e) = self.checked() {
                    Z3_ast_vector_dec_ref(c, vec);
                    return Err(e);
                }
            }
            Z3_ast_vector_dec_ref(c, vec);
            self.checked()
        }
    }
    fn add(&mut self, term: &Handle) -> Result<(), Self::Error> {
        let t = self.check_handle(term, HandleKind::Expr)?;
        unsafe { Z3_solver_assert(self.context.0, self.solver, t) };
        self.checked()
    }
    fn push(&mut self) -> Result<(), Self::Error> {
        unsafe { Z3_solver_push(self.context.0, self.solver) };
        self.checked()
    }
    fn pop(&mut self, n: usize) -> Result<(), Self::Error> {
        unsafe { Z3_solver_pop(self.context.0, self.solver, Self::count(n)?) };
        self.checked()
    }
    fn set_limit(&mut self, resource_limit: bool, value: i64) -> Result<(), Self::Error> {
        let value = c_uint::try_from(value).map_err(|_| NativeZ3Error::InvalidCount)?;
        let name = if resource_limit {
            c"rlimit"
        } else {
            c"timeout"
        };
        let value = CString::new(value.to_string()).map_err(|_| NativeZ3Error::InvalidString)?;
        unsafe { Z3_update_param_value(self.context.0, name.as_ptr(), value.as_ptr()) };
        self.checked()
    }
    fn check(&mut self) -> Result<SatResult, Self::Error> {
        let v = unsafe { Z3_solver_check(self.context.0, self.solver) };
        self.checked()?;
        match v {
            -1 => Ok(SatResult::Unsat),
            0 => Ok(SatResult::Unknown),
            1 => Ok(SatResult::Sat),
            _ => Err(NativeZ3Error::Solver(format!(
                "unexpected check result {v}"
            ))),
        }
    }
}

/// Configuration for the source-shaped linked prover adapter. Unsupported source
/// modes are rejected explicitly instead of silently changing solver behavior.
#[derive(Clone, Debug)]
pub struct LinkedProverOptions {
    pub timeout: super::z3_prover_api::ApiTimeoutSettings,
    pub counterexamples: bool,
    pub report_reason_unknown: bool,
    pub debug: bool,
    pub soft_assertions: bool,
    pub custom_options: Vec<(String, String)>,
    pub disable_nonlinear: bool,
}
#[derive(Debug)]
pub enum LinkedProverError {
    Native(NativeZ3Error),
    Session(super::z3_prover_api::ApiProverError<NativeZ3Error>),
    Inactive,
    AlreadyStarted,
    Unsupported(&'static str),
    NoModel,
    NoReasonUnknown,
    OperationAndCleanup {
        operation: Box<LinkedProverError>,
        cleanup: Box<LinkedProverError>,
    },
}
impl From<NativeZ3Error> for LinkedProverError {
    fn from(e: NativeZ3Error) -> Self {
        Self::Native(e)
    }
}
impl From<super::z3_prover_api::ApiProverError<NativeZ3Error>> for LinkedProverError {
    fn from(e: super::z3_prover_api::ApiProverError<NativeZ3Error>) -> Self {
        Self::Session(e)
    }
}
/// Source Prover adapter for the linked Z3 session. It is intentionally thread-bound.
pub struct LinkedZ3Prover {
    factory: crate::state::terms::TermFactory,
    identifiers: crate::state::identifiers::DefaultIdentifierFactory,
    options: LinkedProverOptions,
    session: Option<super::z3_prover_api::Z3ApiSession<LinkedZ3>>,
    last_model: Option<RetainedModel>,
    last_reason_unknown: Option<String>,
    randomize_options: Vec<String>,
}
impl LinkedZ3Prover {
    pub fn new(
        unique_id: impl Into<String>,
        factory: crate::state::terms::TermFactory,
        options: LinkedProverOptions,
    ) -> Self {
        Self {
            identifiers: crate::state::identifiers::DefaultIdentifierFactory::new(unique_id),
            factory,
            options,
            session: None,
            last_model: None,
            last_reason_unknown: None,
            randomize_options: vec!["RANDOMIZE_SEEDS".into()],
        }
    }
    /// Share the source fresh-name counter with the verifier's decider.
    pub fn identifier_factory(&self) -> crate::state::identifiers::DefaultIdentifierFactory {
        self.identifiers.clone()
    }
    fn active(
        &mut self,
    ) -> Result<&mut super::z3_prover_api::Z3ApiSession<LinkedZ3>, LinkedProverError> {
        self.session.as_mut().ok_or(LinkedProverError::Inactive)
    }
}
impl crate::interfaces::decider::prover::TextEmitter for LinkedZ3Prover {
    type Error = LinkedProverError;
    fn emit(&mut self, content: &str) -> Result<(), Self::Error> {
        self.active()?.emit(content.to_string()).map_err(Into::into)
    }
    fn emit_settings(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        use crate::interfaces::preamble::PreambleReader;
        if contents.is_empty() {
            return Ok(());
        }
        let expected = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default()
            .read_preamble("/z3config.smt2")
            .map_err(|_| LinkedProverError::Unsupported("missing Z3 static settings"))?;
        if contents == expected {
            return Ok(());
        }
        let randomized = contents
            .iter()
            .any(|s| s.starts_with("(set-option :RANDOMIZE_SEEDS"));
        if randomized
            && contents
                .iter()
                .all(|s| s.starts_with("(set-option :RANDOMIZE_SEEDS") || expected.contains(s))
        {
            self.active()?.converter.context.randomize_seed()?;
            return Ok(());
        }
        Err(LinkedProverError::Unsupported("custom Z3 API settings"))
    }
}
impl crate::interfaces::decider::prover::ProverLike for LinkedZ3Prover {
    fn assume_axioms(
        &mut self,
        terms: &crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::state::terms::Term,
        >,
        _: &str,
    ) -> Result<(), Self::Error> {
        for term in terms.iter() {
            self.active()?.assume(term)?;
        }
        Ok(())
    }
    fn set_option(&mut self, _: &str, _: &str) -> Result<String, Self::Error> {
        Err(LinkedProverError::Unsupported("dynamic Z3 API options"))
    }
    fn assume(&mut self, term: &crate::state::terms::Term) -> Result<(), Self::Error> {
        self.active()?.assume(term).map_err(Into::into)
    }
    fn declare(
        &mut self,
        declaration: &crate::state::terms::Declaration,
    ) -> Result<(), Self::Error> {
        self.active()?.declare(declaration).map_err(Into::into)
    }
    fn comment(&mut self, _: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        Ok(())
    }
    fn saturate(&mut self, timeout_ms: i32, _: &str) -> Result<(), Self::Error> {
        self.active()?.check(Some(timeout_ms))?;
        Ok(())
    }
    fn saturate_configured(
        &mut self,
        data: Option<&crate::interfaces::decider::prover::ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        self.active()?.end_preamble()?;
        if let Some(data) = data {
            self.active()?.check(Some(data.timeout_ms))?;
        }
        Ok(())
    }
}
impl crate::interfaces::decider::prover::Prover for LinkedZ3Prover {
    type Model = ferrum_silver::verifier::verification_error::Model;
    type Version = crate::common::config::package::Version;
    fn start(&mut self, user_args: Option<&str>) -> Result<(), Self::Error> {
        if self.session.is_some() {
            return Err(LinkedProverError::AlreadyStarted);
        }
        if user_args.is_some_and(|s| !s.is_empty()) {
            return Err(LinkedProverError::Unsupported(
                "Z3 API command-line arguments",
            ));
        }
        let driver = LinkedZ3::new_with_source_options()?;
        driver.set_source_solver_options(
            &self.options.custom_options,
            self.options.disable_nonlinear,
        )?;
        let converter = super::term_to_z3_api_converter::TermToZ3ApiConverter::new(
            driver,
            self.factory.clone(),
        );
        self.session = Some(super::z3_prover_api::Z3ApiSession::new(
            converter,
            self.options.timeout,
        ));
        self.identifiers.start();
        Ok(())
    }
    fn reset(&mut self) -> Result<(), Self::Error> {
        self.stop()?;
        self.identifiers.reset();
        self.start(None)
    }
    fn stop(&mut self) -> Result<(), Self::Error> {
        self.last_model = None;
        self.last_reason_unknown = None;
        self.session = None;
        self.identifiers.stop();
        Ok(())
    }
    fn assert_goal(
        &mut self,
        goal: &crate::state::terms::Term,
        timeout_ms: Option<i32>,
    ) -> Result<bool, Self::Error> {
        if self.options.soft_assertions {
            use crate::state::terms::{ApplicationTarget, Sort};
            self.active()?.end_preamble()?;
            self.active()?.set_timeout(timeout_ms)?;
            let guard = match self.fresh("grd", &[], &Sort::Bool)? {
                ApplicationTarget::Function(value) => value,
                _ => {
                    return Err(LinkedProverError::Unsupported(
                        "invalid soft assertion guard",
                    ));
                }
            };
            let guard = self.factory.app(guard, vec![]);
            let implication = self
                .factory
                .implies(guard.clone(), self.factory.not(goal.clone()));
            let want_model = self.options.counterexamples;
            let (result, model) = {
                let session = self.active()?;
                session.assume(&implication)?;
                let guard = session
                    .converter
                    .convert_term(&guard)
                    .map_err(super::z3_prover_api::ApiProverError::from)?;
                let result = session.converter.context.check_assumptions(&[guard])?;
                let model = if result != SatResult::Unsat && want_model {
                    session.converter.context.retain_model().ok()
                } else {
                    None
                };
                (result, model)
            };
            if result != SatResult::Unsat && want_model {
                self.last_model = model;
            }
            return Ok(result == SatResult::Unsat);
        }
        let want_model = self.options.counterexamples;
        let want_reason = self.options.report_reason_unknown;
        let (proved, model, reason) = {
            let session = self.active()?;
            session.push(1, None)?;
            let check = (|| -> Result<SatResult, LinkedProverError> {
                let expr = session
                    .converter
                    .convert_term(goal)
                    .map_err(super::z3_prover_api::ApiProverError::from)?;
                let negated = session.converter.context.builtin(NativeOp::Not, &[expr])?;
                session.converter.context.add(&negated)?;
                Ok(session.check(timeout_ms)?)
            })();
            let cleanup = session.pop(1).map_err(LinkedProverError::from);
            let result = match (check, cleanup) {
                (Ok(value), Ok(())) => value,
                (Err(error), Ok(())) | (Ok(_), Err(error)) => return Err(error),
                (Err(operation), Err(cleanup)) => {
                    return Err(LinkedProverError::OperationAndCleanup {
                        operation: Box::new(operation),
                        cleanup: Box::new(cleanup),
                    });
                }
            };
            let proved = result == SatResult::Unsat;
            let model = if !proved && want_model {
                session.converter.context.retain_model().ok()
            } else {
                None
            };
            let reason = if !proved && want_reason {
                Some(session.converter.context.reason_unknown()?)
            } else {
                None
            };
            (proved, model, reason)
        };
        if !proved && want_model {
            self.last_model = model;
        }
        if !proved && want_reason {
            self.last_reason_unknown = reason;
        }
        Ok(proved)
    }
    fn check(&mut self, timeout_ms: Option<i32>) -> Result<SatResult, Self::Error> {
        self.active()?.check(timeout_ms).map_err(Into::into)
    }
    fn fresh(
        &mut self,
        name: &str,
        arg_sorts: &[crate::state::terms::Sort],
        result_sort: &crate::state::terms::Sort,
    ) -> Result<crate::state::terms::ApplicationTarget, Self::Error> {
        use crate::state::{
            identifiers::IdentifierFactory,
            terms::{ApplicableData, ApplicableKind, ApplicationTarget},
        };
        let id = self.identifiers.fresh(name);
        let function = self.factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id,
            arg_sorts: arg_sorts.to_vec(),
            result_sort: result_sort.clone(),
        });
        let declaration = self.factory.function_decl(function.clone());
        let target = ApplicationTarget::Function(function);
        self.active()?
            .converter
            .convert_declaration(&declaration)
            .map_err(super::z3_prover_api::ApiProverError::from)?;
        Ok(target)
    }
    fn statistics(&mut self) -> Result<Vec<(String, String)>, Self::Error> {
        self.active()?
            .converter
            .context
            .statistics()
            .map_err(Into::into)
    }
    fn has_model(&self) -> bool {
        self.last_model.is_some()
    }
    fn is_model_valid(&self) -> bool {
        self.last_model.is_some()
    }
    fn get_model(&mut self) -> Result<Self::Model, Self::Error> {
        let model = self.last_model.as_ref().ok_or(LinkedProverError::NoModel)?;
        let session = self.session.as_ref().ok_or(LinkedProverError::Inactive)?;
        session
            .converter
            .context
            .model_from_retained(model)
            .map_err(Into::into)
    }
    fn get_reason_unknown(&mut self) -> Result<String, Self::Error> {
        self.last_reason_unknown
            .clone()
            .ok_or(LinkedProverError::NoReasonUnknown)
    }
    fn clear_last_assert(&mut self) {
        self.last_model = None;
        self.last_reason_unknown = None;
    }
    fn name(&self) -> &str {
        "Z3"
    }
    fn min_version(&self) -> Self::Version {
        Self::Version::new("4.16.0.0")
    }
    fn max_version(&self) -> Option<Self::Version> {
        Some(Self::Version::new("4.16.0.0"))
    }
    fn version(&mut self) -> Result<Self::Version, Self::Error> {
        let (a, b, c, d) = LinkedZ3::library_version();
        Ok(Self::Version::new(&format!("{a}.{b}.{c}.{d}")))
    }
    fn static_preamble(&self) -> &str {
        "/z3config.smt2"
    }
    fn randomize_seeds_options(&self) -> &[String] {
        &self.randomize_options
    }
    fn push_pop_scope_depth(&self) -> usize {
        self.session.as_ref().map_or(0, |s| s.scope_depth())
    }
    fn push(&mut self, n: usize, timeout_ms: Option<i32>) -> Result<(), Self::Error> {
        self.active()?.push(n, timeout_ms).map_err(Into::into)
    }
    fn pop(&mut self, n: usize) -> Result<(), Self::Error> {
        self.active()?.pop(n).map_err(Into::into)
    }
    fn all_declarations(&self) -> Vec<crate::state::terms::Declaration> {
        if self.options.debug {
            self.session
                .as_ref()
                .map_or_else(Vec::new, |s| s.declarations().to_vec())
        } else {
            vec![]
        }
    }
    fn all_emits(&self) -> Vec<String> {
        self.session
            .as_ref()
            .map_or_else(Vec::new, |s| s.emissions().to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn linked_z3_checks_scopes_snapshots_and_context_ownership() {
        let mut z = LinkedZ3::new().unwrap();
        let int = z.sort(NativeSort::Int).unwrap();
        let one = z.literal(NativeLiteral::Integer("1".into()), &int).unwrap();
        let two = z.literal(NativeLiteral::Integer("2".into()), &int).unwrap();
        let eq = z.builtin(NativeOp::Equal, &[one.clone(), two]).unwrap();
        z.push().unwrap();
        z.add(&eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
        z.pop(1).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        let snap = z.sort(NativeSort::Snap).unwrap();
        let unit = z.literal(NativeLiteral::SnapUnit, &snap).unwrap();
        let pair = z
            .builtin(NativeOp::SnapCombine, &[unit.clone(), unit.clone()])
            .unwrap();
        let first = z.builtin(NativeOp::SnapFirst, &[pair]).unwrap();
        let same = z.builtin(NativeOp::Equal, &[first, unit]).unwrap();
        let not = z.builtin(NativeOp::Not, &[same]).unwrap();
        z.push().unwrap();
        z.add(&not).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
        z.pop(1).unwrap();
        assert_eq!(z.add(&int), Err(NativeZ3Error::InvalidHandleKind));
        assert_eq!(
            z.constant("bad", &one),
            Err(NativeZ3Error::InvalidHandleKind)
        );
        let mut other = LinkedZ3::new().unwrap();
        assert_eq!(other.add(&one), Err(NativeZ3Error::ContextMismatch));
        drop(z);
        drop(one);
    }
    #[test]
    fn linked_z3_parses_preamble_and_binds_quantifier_constants() {
        let mut z = LinkedZ3::new().unwrap();
        let int = z.sort(NativeSort::Int).unwrap();
        let f = z.function("preamble_x", &[], &int).unwrap();
        z.parse_and_add_preamble(
            &["(assert (= preamble_x 1))".into()],
            &[],
            &[("preamble_x".into(), f)],
        )
        .unwrap();
        let x = z.constant("preamble_x", &int).unwrap();
        let two = z.literal(NativeLiteral::Integer("2".into()), &int).unwrap();
        let eq = z.builtin(NativeOp::Equal, &[x, two]).unwrap();
        z.push().unwrap();
        z.add(&eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
        z.pop(1).unwrap();
        let x = z.constant("bound", &int).unwrap();
        let body = z.builtin(NativeOp::Equal, &[x.clone(), x.clone()]).unwrap();
        let quant = z
            .quantifier(Quantifier::Forall, &[x], &body, &[], "test_quantifier", 1)
            .unwrap();
        let not = z.builtin(NativeOp::Not, &[quant]).unwrap();
        z.push().unwrap();
        z.add(&not).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
        z.pop(1).unwrap();
    }
    #[test]
    fn linked_z3_parses_bitvector_and_float_builtins() {
        let mut z = LinkedZ3::new().unwrap();
        let int = z.sort(NativeSort::Int).unwrap();
        let bool_sort = z.sort(NativeSort::Bool).unwrap();
        let bv = z
            .sort(NativeSort::ParsedSmt("(_ BitVec 32)".into()))
            .unwrap();
        let fp = z
            .sort(NativeSort::ParsedSmt("(_ FloatingPoint 8 24)".into()))
            .unwrap();
        let one = z
            .literal(NativeLiteral::Integer("1065353216".into()), &int)
            .unwrap();
        let bits = z
            .application("(_ int2bv 32)", &[int], &bv, &[one], true)
            .unwrap();
        let one_fp = z
            .application("(_ to_fp 8 24)", &[bv], &fp, &[bits], true)
            .unwrap();
        let sum = z
            .application(
                "fp.add RNE",
                &[fp.clone(), fp.clone()],
                &fp,
                &[one_fp.clone(), one_fp.clone()],
                true,
            )
            .unwrap();
        let equal = z
            .application(
                "fp.eq",
                &[fp.clone(), fp],
                &bool_sort,
                &[sum.clone(), sum],
                true,
            )
            .unwrap();
        let not = z.builtin(NativeOp::Not, &[equal]).unwrap();
        z.add(&not).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
    }
    #[test]
    fn linked_z3_session_converts_and_checks_terms() {
        use crate::decider::{
            term_to_z3_api_converter::TermToZ3ApiConverter,
            z3_prover_api::{ApiTimeoutSettings, Z3ApiSession},
        };
        use crate::state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = TermToZ3ApiConverter::new(LinkedZ3::new().unwrap(), factory.clone());
        let mut session = Z3ApiSession::new(
            converter,
            ApiTimeoutSettings {
                default_timeout_ms: 0,
                use_time_bounds: true,
                resources_per_millisecond: 1,
            },
        );
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let one = factory.int_literal(1);
        let two = factory.int_literal(2);
        let premise = factory.equals(x.clone(), one.clone());
        session.assume(&premise).unwrap();
        assert!(
            session
                .assert_push_pop(
                    &factory.equals(factory.plus(x.clone(), one), two.clone()),
                    None
                )
                .unwrap()
        );
        assert!(
            !session
                .assert_push_pop(&factory.equals(x, two), None)
                .unwrap()
        );
        assert_eq!(session.scope_depth(), 0);
    }
    #[test]
    fn linked_z3_reports_version_and_sat_model_text() {
        assert!(LinkedZ3::library_version().0 >= 4);
        let mut z = LinkedZ3::new().unwrap();
        let int = z.sort(NativeSort::Int).unwrap();
        let x = z.constant("model_x", &int).unwrap();
        let one = z.literal(NativeLiteral::Integer("1".into()), &int).unwrap();
        let eq = z.builtin(NativeOp::Equal, &[x, one]).unwrap();
        z.add(&eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        let model = z.model_text().unwrap();
        assert!(model.contains("model_x"));
        assert!(model.contains("1"));
        let model = z.model().unwrap();
        assert_eq!(
            model.entries.get("model_x"),
            Some(
                &ferrum_silver::verifier::verification_error::ModelEntry::Value(
                    ferrum_silver::verifier::verification_error::ValueEntry::Constant("1".into())
                )
            )
        );
    }
    #[test]
    fn linked_z3_converts_function_interpretation_to_silver_model() {
        use ferrum_silver::verifier::verification_error::ModelEntry;
        let mut z = LinkedZ3::new().unwrap();
        let int = z.sort(NativeSort::Int).unwrap();
        let one = z.literal(NativeLiteral::Integer("1".into()), &int).unwrap();
        let two = z.literal(NativeLiteral::Integer("2".into()), &int).unwrap();
        let f1 = z
            .application("model_f", &[int.clone()], &int, &[one], false)
            .unwrap();
        let eq = z.builtin(NativeOp::Equal, &[f1, two]).unwrap();
        z.add(&eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        let model = z.model().unwrap();
        assert!(matches!(
            model.entries.get("model_f"),
            Some(ModelEntry::Map(_))
        ));
    }
    #[test]
    fn linked_z3_model_preserves_rational_values() {
        use ferrum_silver::verifier::verification_error::{ModelEntry, ValueEntry};
        let mut z = LinkedZ3::new().unwrap();
        let real = z.sort(NativeSort::Real).unwrap();
        let x = z.constant("rational_x", &real).unwrap();
        let one = z.literal(NativeLiteral::Real(1), &real).unwrap();
        let two = z.literal(NativeLiteral::Real(2), &real).unwrap();
        let half = z.builtin(NativeOp::Div, &[one, two]).unwrap();
        let eq = z.builtin(NativeOp::Equal, &[x, half]).unwrap();
        z.add(&eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        let model = z.model().unwrap();
        assert_eq!(
            model.entries.get("rational_x"),
            Some(&ModelEntry::Value(ValueEntry::Application {
                name: "/".into(),
                arguments: vec![
                    ValueEntry::Constant("1".into()),
                    ValueEntry::Constant("2".into())
                ]
            }))
        );
    }
    #[test]
    fn linked_z3_custom_solver_options_validate_types() {
        let mut z = LinkedZ3::new_with_source_options().unwrap();
        z.set_source_solver_options(
            &[
                ("smt.mbqi".into(), "true".into()),
                ("random_seed".into(), "123".into()),
                ("qi.eager_threshold".into(), "5.5".into()),
            ],
            true,
        )
        .unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        assert!(
            z.set_source_solver_options(&[("mbqi".into(), "wrong".into())], false)
                .is_err()
        );
        assert!(
            z.set_source_solver_options(&[("ferrum_unknown_option".into(), "true".into())], false)
                .is_err()
        );
    }
    #[test]
    fn linked_z3_source_options_and_context_timeout_are_accepted() {
        let mut z = LinkedZ3::new_with_source_options().unwrap();
        z.parse_and_add_preamble(&[], &[], &[]).unwrap();
        z.set_limit(false, 1000).unwrap();
        let boolean = z.sort(NativeSort::Bool).unwrap();
        let value = z.literal(NativeLiteral::Bool(true), &boolean).unwrap();
        z.add(&value).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
    }
    #[test]
    fn linked_prover_adapter_checks_and_resets_real_solver() {
        use crate::interfaces::decider::prover::{Prover, ProverLike, TextEmitter};
        use crate::state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let options = LinkedProverOptions {
            timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                default_timeout_ms: 0,
                use_time_bounds: true,
                resources_per_millisecond: 1,
            },
            counterexamples: false,
            report_reason_unknown: false,
            debug: false,
            soft_assertions: false,
            custom_options: vec![],
            disable_nonlinear: false,
        };
        let mut prover = LinkedZ3Prover::new("test", factory.clone(), options);
        prover.start(None).unwrap();
        prover.emit_settings(&[]).unwrap();
        use crate::interfaces::preamble::PreambleReader;
        let settings = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default()
            .read_preamble("/z3config.smt2")
            .unwrap();
        prover.emit_settings(&settings).unwrap();
        prover
            .emit_settings(&["(set-option :RANDOMIZE_SEEDS true)".into()])
            .unwrap();
        prover.saturate_configured(None).unwrap();
        assert!(prover.emit("(assert true)").is_err());
        assert!(matches!(
            prover.emit_settings(&["(set-option :mbqi true)".into()]),
            Err(LinkedProverError::Unsupported("custom Z3 API settings"))
        ));
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let one = factory.int_literal(1);
        let two = factory.int_literal(2);
        prover
            .assume(&factory.equals(x.clone(), one.clone()))
            .unwrap();
        assert!(
            prover
                .assert_goal(
                    &factory.equals(factory.plus(x.clone(), one), two.clone()),
                    None
                )
                .unwrap()
        );
        assert!(!prover.assert_goal(&factory.equals(x, two), None).unwrap());
        assert_eq!(prover.push_pop_scope_depth(), 0);
        assert!(!prover.statistics().unwrap().is_empty());
        use crate::state::identifiers::IdentifierFactory;
        let mut shared = prover.identifier_factory();
        let prior = shared.fresh("v");
        let a = prover.fresh("v", &[], &Sort::Int).unwrap();
        assert_ne!(&prior, a.id());
        let b = prover.fresh("v", &[], &Sort::Int).unwrap();
        assert_ne!(a.id(), b.id());
        prover.reset().unwrap();
        assert_eq!(prover.check(None).unwrap(), SatResult::Sat);
        prover.stop().unwrap();
    }
    #[test]
    fn linked_prover_reports_counterexample_when_available() {
        use crate::interfaces::decider::prover::{Prover, ProverLike};
        use crate::state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let options = LinkedProverOptions {
            timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                default_timeout_ms: 0,
                use_time_bounds: true,
                resources_per_millisecond: 1,
            },
            counterexamples: true,
            report_reason_unknown: false,
            debug: false,
            soft_assertions: false,
            custom_options: vec![],
            disable_nonlinear: false,
        };
        let mut prover = LinkedZ3Prover::new("model", factory.clone(), options);
        prover.start(None).unwrap();
        let x = factory.var(Identifier::new("model_x"), Sort::Int, false);
        prover
            .assume(&factory.equals(x.clone(), factory.int_literal(1)))
            .unwrap();
        assert!(
            !prover
                .assert_goal(&factory.equals(x, factory.int_literal(2)), None)
                .unwrap()
        );
        assert!(prover.has_model());
        assert!(prover.get_model().unwrap().entries.contains_key("model_x"));
        prover.clear_last_assert();
        assert!(!prover.has_model());
    }
    #[test]
    fn linked_prover_soft_assertions_preserve_guarded_scope_and_model() {
        use crate::interfaces::decider::prover::{Prover, ProverLike};
        use crate::state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let options = LinkedProverOptions {
            timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                default_timeout_ms: 0,
                use_time_bounds: true,
                resources_per_millisecond: 1,
            },
            counterexamples: true,
            report_reason_unknown: false,
            debug: false,
            soft_assertions: true,
            custom_options: vec![],
            disable_nonlinear: false,
        };
        let mut prover = LinkedZ3Prover::new("soft", factory.clone(), options);
        prover.start(None).unwrap();
        let x = factory.var(Identifier::new("soft_x"), Sort::Int, false);
        prover
            .assume(&factory.equals(x.clone(), factory.int_literal(1)))
            .unwrap();
        assert!(
            !prover
                .assert_goal(&factory.equals(x.clone(), factory.int_literal(2)), None)
                .unwrap()
        );
        assert!(prover.has_model());
        assert!(prover.get_model().unwrap().entries.contains_key("soft_x"));
        assert!(
            prover
                .assert_goal(&factory.equals(x, factory.int_literal(1)), None)
                .unwrap()
        );
        assert_eq!(prover.push_pop_scope_depth(), 0);
        assert_eq!(prover.check(None).unwrap(), SatResult::Sat);
    }
}
