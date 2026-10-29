//! Ferrum optional linked Z3 driver, assembled under PLAN.md from Silicon's
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverAPI.scala
//! and TermToZ3APIConverter.scala. This driver is optional; default verification uses stdio.
//! Status: partial; context-owned handles, primitive terms, datatypes, solver scopes,
//! quantifiers, SMT-LIB preamble parsing and parse-based interpreted sorts/functions
//! are implemented. Structured model extraction is available; the complete Prover
//! adapter covers push/pop and soft-constraint verification, typed solver options,
//! seed randomization and trigger repair. Warning callback and buffering are available;
//! host reporting and context options beyond documented Z3 keys remain pending.
//! Source default options are available
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
    sync::{Arc, Mutex},
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
    fn Z3_interrupt(c: Raw);
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
    fn Z3_func_interp_inc_ref(c: Raw, f: Raw);
    fn Z3_func_interp_dec_ref(c: Raw, f: Raw);
    fn Z3_func_entry_inc_ref(c: Raw, e: Raw);
    fn Z3_func_entry_dec_ref(c: Raw, e: Raw);
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
type InterruptSlot = Arc<Mutex<Option<usize>>>;

/// Cross-thread access is limited to Z3's documented interrupt operation.
/// The slot synchronizes the call with solver and context destruction. It does
/// not queue cancellation before start or during reset, nor make the driver Send.
#[derive(Clone, Default)]
pub struct LinkedZ3CancellationHandle(InterruptSlot);
impl LinkedZ3CancellationHandle {
    /// Request interruption of the current context, returning false if inactive.
    pub fn interrupt(&self) -> bool {
        let slot = self.0.lock().unwrap_or_else(|error| error.into_inner());
        if let Some(address) = *slot {
            // SAFETY: context installation and teardown are synchronized by this
            // mutex. Z3_interrupt is the C API's cross-thread interrupt operation.
            unsafe { Z3_interrupt(ptr::with_exposed_provenance_mut(address)) };
            true
        } else {
            false
        }
    }
}
struct Context(Raw, InterruptSlot);
impl Drop for Context {
    fn drop(&mut self) {
        let mut slot = self.1.lock().unwrap_or_else(|error| error.into_inner());
        if *slot == Some(self.0.expose_provenance()) {
            *slot = None;
        }
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
        Self::create(false, &[], Default::default())
    }
    /// Initialize the solver with the pinned Z3ProverAPI's standard options.
    pub fn new_with_source_options() -> Result<Self, NativeZ3Error> {
        Self::create(true, &[], Default::default())
    }
    fn create(
        source_options: bool,
        context_options: &[(String, String)],
        interrupt: LinkedZ3CancellationHandle,
    ) -> Result<Self, NativeZ3Error> {
        // Z3_set_param_value has no error return. Restrict this native boundary to
        // context keys documented by the linked Z3 C API, rather than silently
        // accepting global/module parameters which must be configured elsewhere.
        let mut options = Vec::new();
        for (name, value) in context_options {
            match name.as_str() {
                "proof" | "debug_ref_count" | "trace" | "well_sorted_check" | "auto_config"
                | "type_check" | "model" | "model_validate" | "unsat_core" => {
                    if value != "true" && value != "false" {
                        return Err(NativeZ3Error::Solver(format!(
                            "invalid Boolean Z3 context option {name}={value}"
                        )));
                    }
                }
                "timeout" => {
                    value.parse::<u32>().map_err(|_| {
                        NativeZ3Error::Solver(format!("invalid Z3 context timeout {value}"))
                    })?;
                }
                "trace_file_name" => (),
                "encoding" if matches!(value.as_str(), "unicode" | "bmp" | "ascii") => (),
                "encoding" => {
                    return Err(NativeZ3Error::Solver(format!(
                        "invalid Z3 encoding {value}"
                    )));
                }
                _ => {
                    return Err(NativeZ3Error::Unsupported(
                        "Z3 context option outside documented context configuration",
                    ));
                }
            }
            options.push((
                CString::new(name.as_str()).map_err(|_| NativeZ3Error::InvalidString)?,
                CString::new(value.as_str()).map_err(|_| NativeZ3Error::InvalidString)?,
            ));
        }
        unsafe {
            let config = Z3_mk_config();
            if config.is_null() {
                return Err(NativeZ3Error::Solver("Z3_mk_config failed".into()));
            }
            if source_options {
                Z3_set_param_value(config, c"auto_config".as_ptr(), c"false".as_ptr());
                Z3_set_param_value(config, c"type_check".as_ptr(), c"true".as_ptr());
            }
            for (name, value) in &options {
                Z3_set_param_value(config, name.as_ptr(), value.as_ptr());
            }
            let raw = Z3_mk_context(config);
            Z3_del_config(config);
            if raw.is_null() {
                return Err(NativeZ3Error::Solver("Z3_mk_context failed".into()));
            }
            Z3_set_error_handler(raw, Some(ignore_error));
            let context = Rc::new(Context(raw, interrupt.0));
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
            *this
                .context
                .1
                .lock()
                .unwrap_or_else(|error| error.into_inner()) = Some(raw.expose_provenance());
            Ok(this)
        }
    }
    fn set_source_solver_options(
        &self,
        custom: &[(String, String)],
        disable_nonlinear: bool,
    ) -> Result<Vec<String>, NativeZ3Error> {
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
        let mut warnings = Vec::new();
        for (original, value) in custom {
            let key = original.strip_prefix("smt.").unwrap_or(original);
            let name = self.symbol(key)?;
            let kind = unsafe { Z3_param_descrs_get_kind(c, descrs, name) };
            if kind > 4 {
                warnings.push(format!("Z3 error: unknown parameter{key}"));
                continue;
            }
            self.checked()?;
            let invalid = || {
                NativeZ3Error::Solver(format!(
                    "invalid value {value:?} for Z3 parameter {original}"
                ))
            };
            unsafe {
                match kind {
                    0 => Z3_params_set_uint(
                        c,
                        raw,
                        name,
                        value.parse::<i32>().map_err(|_| invalid())? as u32,
                    ),
                    1 => {
                        let parsed = if value.eq_ignore_ascii_case("true") {
                            true
                        } else if value.eq_ignore_ascii_case("false") {
                            false
                        } else {
                            return Err(invalid());
                        };
                        Z3_params_set_bool(c, raw, name, parsed)
                    }
                    2 => Z3_params_set_double(c, raw, name, value.parse().map_err(|_| invalid())?),
                    4 => Z3_params_set_symbol(c, raw, name, self.symbol(value)?),
                    _ => {
                        warnings.push(format!("Z3 error: unknown parameter{key}"));
                        continue;
                    }
                }
            }
            self.checked()?;
        }
        unsafe { Z3_solver_set_params(c, self.solver, raw) };
        self.checked()?;
        Ok(warnings)
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
        struct Interpretation(Raw, Raw);
        impl Drop for Interpretation {
            fn drop(&mut self) {
                unsafe { Z3_func_interp_dec_ref(self.0, self.1) }
            }
        }
        struct Entry(Raw, Raw);
        impl Drop for Entry {
            fn drop(&mut self) {
                unsafe { Z3_func_entry_dec_ref(self.0, self.1) }
            }
        }
        let c = self.context.0;
        let value = |ast: Raw, normalize_rational: bool| -> Result<ValueEntry, NativeZ3Error> {
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
                if normalize_rational && real && numeral {
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
            if normalize_rational && real && numeral {
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
            entries.insert(key, ModelEntry::Value(value(interpretation, true)?));
        }
        let count = unsafe { Z3_model_get_num_funcs(c, guard.raw) };
        self.checked()?;
        for i in 0..count {
            let decl = unsafe { Z3_model_get_func_decl(c, guard.raw, i) };
            self.checked()?;
            let key = name(decl)?;
            let interp = unsafe { Z3_model_get_func_interp(c, guard.raw, decl) };
            if interp.is_null() {
                self.checked()?;
                return Err(NativeZ3Error::Solver(
                    "Z3 returned no function interpretation".into(),
                ));
            }
            unsafe { Z3_func_interp_inc_ref(c, interp) };
            let _interp_guard = Interpretation(c, interp);
            self.checked()?;
            let count = unsafe { Z3_func_interp_get_num_entries(c, interp) };
            self.checked()?;
            let mut options = HashMap::new();
            for j in 0..count {
                let entry = unsafe { Z3_func_interp_get_entry(c, interp, j) };
                if entry.is_null() {
                    self.checked()?;
                    return Err(NativeZ3Error::Solver(
                        "Z3 returned no function entry".into(),
                    ));
                }
                unsafe { Z3_func_entry_inc_ref(c, entry) };
                let _entry_guard = Entry(c, entry);
                self.checked()?;
                let n = unsafe { Z3_func_entry_get_num_args(c, entry) };
                self.checked()?;
                let mut args = Vec::new();
                for k in 0..n {
                    let arg = unsafe { Z3_func_entry_get_arg(c, entry, k) };
                    self.checked()?;
                    args.push(value(arg, false)?);
                }
                let result = unsafe { Z3_func_entry_get_value(c, entry) };
                self.checked()?;
                options.insert(args, value(result, false)?);
            }
            let default = unsafe { Z3_func_interp_get_else(c, interp) };
            self.checked()?;
            entries.insert(
                key,
                ModelEntry::Map(MapEntry {
                    options,
                    default: value(default, false)?,
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
    pub fn reason_unknown(&self) -> Result<Option<String>, NativeZ3Error> {
        let text = unsafe { Z3_solver_get_reason_unknown(self.context.0, self.solver) };
        self.checked()?;
        if text.is_null() {
            return Ok(None);
        }
        Ok(Some(
            unsafe { CStr::from_ptr(text) }
                .to_string_lossy()
                .into_owned(),
        ))
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
        let mut slot = self
            .context
            .1
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if *slot == Some(self.context.0.expose_provenance()) {
            *slot = None;
        }
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

/// Source API retry removes entire trigger groups containing a bare variable or
/// forbidden operator. Plus and minus are explicitly allowed by the advanced rule.
fn clean_invalid_triggers(
    factory: &crate::state::terms::TermFactory,
    term: &crate::state::terms::Term,
) -> Result<crate::state::terms::Term, LinkedProverError> {
    use crate::state::terms::TermKind;
    fn forbidden(t: &crate::state::terms::Term) -> Result<bool, LinkedProverError> {
        if matches!(
            t.kind(),
            TermKind::Times(..)
                | TermKind::Div(..)
                | TermKind::Mod(..)
                | TermKind::Not(..)
                | TermKind::Or(..)
                | TermKind::And(..)
                | TermKind::Implies(..)
                | TermKind::Iff(..)
                | TermKind::Ite(..)
                | TermKind::BuiltinEquals(..)
                | TermKind::Less(..)
                | TermKind::AtMost(..)
                | TermKind::Greater(..)
                | TermKind::AtLeast(..)
                | TermKind::PermTimes(..)
                | TermKind::IntPermTimes(..)
                | TermKind::PermIntDiv(..)
                | TermKind::PermPermDiv(..)
                | TermKind::PermPlus(..)
                | TermKind::PermMinus(..)
                | TermKind::PermLess(..)
                | TermKind::PermAtMost(..)
                | TermKind::Distinct(..)
        ) {
            return Ok(true);
        }
        for child in t
            .subterms()
            .map_err(|_| LinkedProverError::Unsupported("trigger subterm traversal"))?
        {
            if forbidden(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    let failure = std::cell::RefCell::new(None);
    let result = factory
        .transform_preorder_descending(term, &|current| {
            let TermKind::Quantification { triggers, .. } = current.kind() else {
                return None;
            };
            let mut kept = Vec::new();
            for trigger in triggers {
                let mut bad = false;
                for pattern in &trigger.terms {
                    if matches!(pattern.kind(), TermKind::Var(_)) {
                        bad = true;
                        break;
                    }
                    match forbidden(pattern) {
                        Ok(true) => {
                            bad = true;
                            break;
                        }
                        Ok(false) => {}
                        Err(e) => {
                            *failure.borrow_mut() = Some(e);
                            return None;
                        }
                    }
                }
                if !bad {
                    kept.push(trigger.clone());
                }
            }
            if kept.len() == triggers.len() {
                None
            } else {
                factory.quantification_with_raw_triggers(current, kept)
            }
        })
        .map_err(|_| LinkedProverError::Unsupported("trigger term reconstruction"))?;
    if let Some(error) = failure.into_inner() {
        return Err(error);
    }
    Ok(result)
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
    SourceInteraction {
        prover_id: String,
        message: String,
    },
    SourceToolError(String),
    SourceOrdinary {
        message: String,
        stack_trace: Vec<String>,
    },
    Native(NativeZ3Error),
    Session(super::z3_prover_api::ApiProverError<NativeZ3Error>),
    Inactive,
    AlreadyStarted,
    Unsupported(&'static str),
    NoModel,
    OperationAndCleanup {
        operation: Box<LinkedProverError>,
        cleanup: Box<LinkedProverError>,
    },
}
impl LinkedProverError {
    fn z3_message(&self) -> Option<&str> {
        use super::term_to_z3_api_converter::NativeConversionError;
        use super::z3_prover_api::ApiProverError;
        match self {
            Self::Native(NativeZ3Error::Solver(message))
            | Self::Session(ApiProverError::Driver(NativeZ3Error::Solver(message)))
            | Self::Session(ApiProverError::Conversion(NativeConversionError::Context(
                NativeZ3Error::Solver(message),
            ))) => Some(message),
            _ => None,
        }
    }
    fn is_z3_failure(&self) -> bool {
        use super::term_to_z3_api_converter::NativeConversionError;
        use super::z3_prover_api::ApiProverError;
        matches!(
            self,
            Self::Native(NativeZ3Error::Solver(_))
                | Self::Session(ApiProverError::Driver(NativeZ3Error::Solver(_)))
                | Self::Session(ApiProverError::Conversion(NativeConversionError::Context(
                    NativeZ3Error::Solver(_)
                )))
        )
    }
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
    unique_id: String,
    factory: crate::state::terms::TermFactory,
    identifiers: crate::state::identifiers::DefaultIdentifierFactory,
    options: LinkedProverOptions,
    session: Option<super::z3_prover_api::Z3ApiSession<LinkedZ3>>,
    last_model: Option<RetainedModel>,
    last_reason_unknown: Option<String>,
    randomize_options: Vec<String>,
    debug_preamble: Vec<crate::debugger::debug_exp::DebugAxiom>,
    warnings: Vec<String>,
    warning_reporter: Option<Box<dyn FnMut(&str)>>,
    interrupt: LinkedZ3CancellationHandle,
}
impl LinkedZ3Prover {
    pub fn new(
        unique_id: impl Into<String>,
        factory: crate::state::terms::TermFactory,
        options: LinkedProverOptions,
    ) -> Self {
        let unique_id = unique_id.into();
        Self {
            identifiers: crate::state::identifiers::DefaultIdentifierFactory::new(
                unique_id.clone(),
            ),
            unique_id,
            factory,
            options,
            session: None,
            last_model: None,
            last_reason_unknown: None,
            randomize_options: vec!["RANDOMIZE_SEEDS".into()],
            debug_preamble: Vec::new(),
            warnings: Vec::new(),
            warning_reporter: None,
            interrupt: LinkedZ3CancellationHandle::default(),
        }
    }
    /// Obtain a cross-thread interrupt handle shared across subsequent resets.
    pub fn cancellation_handle(&self) -> LinkedZ3CancellationHandle {
        self.interrupt.clone()
    }
    /// Install a sink for future internal warnings; warnings are also retained until drained.
    pub fn set_warning_reporter(&mut self, reporter: impl FnMut(&str) + 'static) {
        self.warning_reporter = Some(Box::new(reporter));
    }
    /// Drain warnings even when no reporter was installed at the time they occurred.
    pub fn take_warnings(&mut self) -> Vec<String> {
        std::mem::take(&mut self.warnings)
    }
    fn report_warning(&mut self, message: String) {
        if let Some(reporter) = &mut self.warning_reporter {
            reporter(&message);
        }
        self.warnings.push(message);
    }
    /// Share the source fresh-name counter with the verifier's decider.
    pub fn identifier_factory(&self) -> crate::state::identifiers::DefaultIdentifierFactory {
        self.identifiers.clone()
    }
    fn assert_goal_once(
        &mut self,
        goal: &crate::state::terms::Term,
        timeout_ms: Option<i32>,
    ) -> Result<bool, LinkedProverError> {
        if self.options.soft_assertions {
            use crate::interfaces::decider::prover::Prover;
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
                session.converter.context.reason_unknown()?
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
    fn assume_with_trigger_retry(
        &mut self,
        term: &crate::state::terms::Term,
    ) -> Result<(), LinkedProverError> {
        match self.active()?.assume(term).map_err(LinkedProverError::from) {
            Ok(()) => Ok(()),
            Err(error) if error.is_z3_failure() => {
                let clean = clean_invalid_triggers(&self.factory, term)?;
                self.active()?.assume(&clean).map_err(|retry| {
                    let retry = LinkedProverError::from(retry);
                    if retry.is_z3_failure() {
                        LinkedProverError::SourceOrdinary {
                            message: format!(
                                "Z3 error: {}",
                                retry.z3_message().unwrap_or("unknown solver error")
                            ),
                            stack_trace: std::backtrace::Backtrace::force_capture()
                                .to_string()
                                .lines()
                                .map(str::to_owned)
                                .collect(),
                        }
                    } else {
                        retry
                    }
                })?;
                self.report_warning(format!(
                    "Z3 error: {}",
                    error.z3_message().unwrap_or("unknown solver error")
                ));
                Ok(())
            }
            Err(error) => Err(error),
        }
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
        description: &str,
    ) -> Result<(), Self::Error> {
        if self.options.debug {
            self.debug_preamble
                .push(crate::debugger::debug_exp::DebugAxiom {
                    description: description.into(),
                    terms: terms.clone(),
                });
        }
        for term in terms.iter() {
            self.assume_with_trigger_retry(term)?;
        }
        Ok(())
    }
    fn set_option(&mut self, _: &str, _: &str) -> Result<String, Self::Error> {
        Err(LinkedProverError::SourceInteraction {
            prover_id: self.unique_id.clone(),
            message: "Dynamically setting prover options via Z3 API is currently not supported."
                .into(),
        })
    }
    fn assume(&mut self, term: &crate::state::terms::Term) -> Result<(), Self::Error> {
        self.assume_with_trigger_retry(term)
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
    type Version = crate::common::config::package::Version;
    fn comment_fallible(
        &mut self,
        _: &mut dyn FnMut() -> Result<String, String>,
    ) -> Result<(), crate::interfaces::decider::prover::CommentError<Self::Error>> {
        Ok(())
    }
    fn start(&mut self, user_args: Option<&str>) -> Result<(), Self::Error> {
        if self.session.is_some() {
            return Err(LinkedProverError::AlreadyStarted);
        }
        let mut context_options = Vec::new();
        if let Some(args) = user_args {
            for arg in args.split_whitespace() {
                let (key, value) = arg
                    .split_once('=')
                    .filter(|(key, value)| {
                        !key.is_empty() && !value.is_empty() && !value.contains('=')
                    })
                    .ok_or(LinkedProverError::Unsupported(
                        "malformed Z3 context argument",
                    ))?;
                context_options.push((key.to_owned(), value.to_owned()));
            }
        }
        let driver = LinkedZ3::create(true, &context_options, self.interrupt.clone())?;
        let warnings = driver.set_source_solver_options(
            &self.options.custom_options,
            self.options.disable_nonlinear,
        )?;
        for warning in warnings {
            self.report_warning(warning);
        }
        let converter = super::term_to_z3_api_converter::TermToZ3ApiConverter::new(
            driver,
            self.factory.clone(),
        );
        let mut session = super::z3_prover_api::Z3ApiSession::new(converter, self.options.timeout);
        if self.options.debug {
            session.enable_debug_replay();
        }
        self.session = Some(session);
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
        self.debug_preamble.clear();
        self.session = None;
        self.identifiers.stop();
        Ok(())
    }
    fn assert_goal(
        &mut self,
        goal: &crate::state::terms::Term,
        timeout_ms: Option<i32>,
    ) -> Result<bool, Self::Error> {
        match self.assert_goal_once(goal, timeout_ms) {
            Err(error) if error.is_z3_failure() => {
                let clean = clean_invalid_triggers(&self.factory, goal)?;
                if clean == *goal {
                    Err(LinkedProverError::SourceToolError(format!(
                        "Z3 error: {}",
                        error.z3_message().unwrap_or("unknown solver error")
                    )))
                } else {
                    self.assert_goal(&clean, timeout_ms)
                }
            }
            result => result,
        }
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
        if self.options.debug {
            self.active()?.record_fresh_declaration(declaration);
        }
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
    fn get_model(
        &mut self,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, Self::Error> {
        let model = self.last_model.as_ref().ok_or(LinkedProverError::NoModel)?;
        let session = self.session.as_ref().ok_or(LinkedProverError::Inactive)?;
        session
            .converter
            .context
            .model_from_retained(model)
            .map_err(Into::into)
    }
    fn get_reason_unknown(&mut self) -> Result<Option<String>, Self::Error> {
        Ok(self.last_reason_unknown.clone())
    }
    fn clear_last_assert(&mut self) {
        self.last_model = None;
        self.last_reason_unknown = None;
    }
    fn name(&self) -> &str {
        "Z3-API"
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
    fn debug_replay_events(
        &self,
    ) -> Option<Vec<crate::interfaces::decider::prover::DebugReplayEvent>> {
        if self.options.debug {
            self.session
                .as_ref()
                .map(|s| s.debug_replay_events().to_vec())
        } else {
            None
        }
    }
    fn debug_preamble_assumptions(&self) -> Option<Vec<crate::debugger::debug_exp::DebugAxiom>> {
        self.options.debug.then(|| self.debug_preamble.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn linked_debug_preamble_records_and_resets() {
        use crate::{
            interfaces::decider::prover::{Prover, ProverLike},
            state::terms::{TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        for debug in [false, true] {
            let options = LinkedProverOptions {
                timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                    default_timeout_ms: 0,
                    use_time_bounds: true,
                    resources_per_millisecond: 1,
                },
                counterexamples: false,
                report_reason_unknown: false,
                debug,
                soft_assertions: false,
                custom_options: vec![],
                disable_nonlinear: false,
            };
            let mut prover = LinkedZ3Prover::new("debug-api", factory.clone(), options);
            prover.start(None).unwrap();
            let terms = [factory.boolean(true)].into_iter().collect();
            prover.assume_axioms(&terms, "test axiom").unwrap();
            if debug {
                let recorded = prover.debug_preamble_assumptions().unwrap();
                assert_eq!(recorded.len(), 1);
                assert_eq!(recorded[0].description, "test axiom");
                assert_eq!(recorded[0].terms, terms);
            } else {
                assert!(prover.debug_preamble_assumptions().is_none());
            }
            prover.reset().unwrap();
            if debug {
                assert!(prover.debug_preamble_assumptions().unwrap().is_empty());
            }
            prover.stop().unwrap();
        }
    }
    #[test]
    fn linked_soft_assertion_reason_remains_absent() {
        use crate::{
            interfaces::decider::prover::Prover,
            state::terms::{TermFactory, TermOptions},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        for soft in [false, true] {
            let options = LinkedProverOptions {
                timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                    default_timeout_ms: 0,
                    use_time_bounds: true,
                    resources_per_millisecond: 1,
                },
                counterexamples: false,
                report_reason_unknown: true,
                debug: false,
                soft_assertions: soft,
                custom_options: vec![],
                disable_nonlinear: false,
            };
            let mut prover = LinkedZ3Prover::new("reason", factory.clone(), options);
            prover.start(None).unwrap();
            assert_eq!(prover.get_reason_unknown().unwrap(), None);
            assert!(!prover.assert_goal(&factory.boolean(false), None).unwrap());
            assert_eq!(prover.get_reason_unknown().unwrap().is_some(), !soft);
            if soft {
                prover.last_reason_unknown = Some("prior".into());
                assert!(!prover.assert_goal(&factory.boolean(false), None).unwrap());
                assert_eq!(
                    prover.get_reason_unknown().unwrap().as_deref(),
                    Some("prior")
                );
            }
            prover.clear_last_assert();
            assert_eq!(prover.get_reason_unknown().unwrap(), None);
            prover.stop().unwrap();
        }
    }
    #[test]
    fn interrupt_unblocks_solver_and_context_lifetime_is_synchronized() {
        use std::time::Duration;
        let interrupt = LinkedZ3CancellationHandle::default();
        assert!(!interrupt.interrupt());
        let worker_interrupt = interrupt.clone();
        let (ready_tx, ready_rx) = std::sync::mpsc::channel();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let mut solver = LinkedZ3::create(false, &[], worker_interrupt.clone()).unwrap();
            let mut input = String::new();
            for i in 0..35 {
                for j in 0..34 {
                    input.push_str(&format!("(declare-const p{i}_{j} Bool)\n"));
                }
                input.push_str("(assert (or");
                for j in 0..34 {
                    input.push_str(&format!(" p{i}_{j}"));
                }
                input.push_str("))\n");
            }
            for j in 0..34 {
                for i in 0..35 {
                    for k in i + 1..35 {
                        input.push_str(&format!("(assert (or (not p{i}_{j}) (not p{k}_{j})))\n"));
                    }
                }
            }
            solver.parse_and_add_preamble(&[input], &[], &[]).unwrap();
            ready_tx.send(()).unwrap();
            let result = solver.check();
            done_tx.send(result).unwrap();
        });
        ready_rx.recv().unwrap();
        std::thread::sleep(Duration::from_millis(100));
        assert!(
            matches!(
                done_rx.try_recv(),
                Err(std::sync::mpsc::TryRecvError::Empty)
            ),
            "solver returned before interruption"
        );
        assert!(interrupt.interrupt());
        let result = done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("solver did not interrupt");
        assert!(
            matches!(result, Ok(SatResult::Unknown) | Err(_)),
            "{result:?}"
        );
        worker.join().unwrap();
        assert!(!interrupt.interrupt());

        // Handles from an old context can outlive its solver and a later reset.
        let mut old = LinkedZ3::create(false, &[], interrupt.clone()).unwrap();
        let retained = old.sort(NativeSort::Int).unwrap();
        drop(old);
        assert!(!interrupt.interrupt());
        let new = LinkedZ3::create(false, &[], interrupt.clone()).unwrap();
        drop(retained);
        assert!(interrupt.interrupt());
        drop(new);
        assert!(!interrupt.interrupt());
    }
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
    fn linked_model_function_reals_keep_raw_z3_spelling() {
        use ferrum_silver::verifier::verification_error::{ModelEntry, ValueEntry};
        let mut z = LinkedZ3::new().unwrap();
        let real = z.sort(NativeSort::Real).unwrap();
        let one = z.literal(NativeLiteral::Real(1), &real).unwrap();
        let two = z.literal(NativeLiteral::Real(2), &real).unwrap();
        let three = z.literal(NativeLiteral::Real(3), &real).unwrap();
        let half = z
            .builtin(NativeOp::Div, &[one.clone(), two.clone()])
            .unwrap();
        let third = z
            .builtin(NativeOp::Div, &[one.clone(), three.clone()])
            .unwrap();
        let two_thirds = z.builtin(NativeOp::Div, &[two, three]).unwrap();
        let a = z
            .application("real_f", &[real.clone()], &real, &[half], false)
            .unwrap();
        let b = z
            .application("real_f", &[real.clone()], &real, &[one], false)
            .unwrap();
        let a_eq = z.builtin(NativeOp::Equal, &[a, third]).unwrap();
        let b_eq = z.builtin(NativeOp::Equal, &[b, two_thirds]).unwrap();
        z.add(&a_eq).unwrap();
        z.add(&b_eq).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Sat);
        let retained = z.retain_model().unwrap();
        let model = z.model_from_retained(&retained).unwrap();
        let ModelEntry::Map(mapped) = &model.entries["real_f"] else {
            panic!("missing function map")
        };
        assert!(
            !mapped.options.is_empty(),
            "two distinct function values require an explicit entry"
        );
        let c = z.context.0;
        let parse = |ast: Raw| {
            let text = unsafe { CStr::from_ptr(Z3_ast_to_string(c, ast)) }.to_string_lossy();
            let parsed =
                ferrum_silver::verifier::model_parser::parse_model(&format!("value -> {text}"))
                    .unwrap();
            let ModelEntry::Value(value) = parsed.entries["value"].clone() else {
                panic!("not a value")
            };
            value
        };
        let count = unsafe { Z3_model_get_num_funcs(c, retained.raw) };
        let interp = (0..count)
            .find_map(|i| {
                let decl = unsafe { Z3_model_get_func_decl(c, retained.raw, i) };
                let sym = unsafe { Z3_get_decl_name(c, decl) };
                let name =
                    unsafe { CStr::from_ptr(Z3_get_symbol_string(c, sym)) }.to_string_lossy();
                (name == "real_f")
                    .then(|| unsafe { Z3_model_get_func_interp(c, retained.raw, decl) })
            })
            .expect("real_f interpretation");
        unsafe { Z3_func_interp_inc_ref(c, interp) };
        let default = unsafe { Z3_func_interp_get_else(c, interp) };
        assert_eq!(mapped.default, parse(default));
        for i in 0..unsafe { Z3_func_interp_get_num_entries(c, interp) } {
            let entry = unsafe { Z3_func_interp_get_entry(c, interp, i) };
            unsafe { Z3_func_entry_inc_ref(c, entry) };
            let args = (0..unsafe { Z3_func_entry_get_num_args(c, entry) })
                .map(|k| parse(unsafe { Z3_func_entry_get_arg(c, entry, k) }))
                .collect::<Vec<_>>();
            let value = parse(unsafe { Z3_func_entry_get_value(c, entry) });
            assert_eq!(mapped.options.get(&args), Some(&value));
            unsafe { Z3_func_entry_dec_ref(c, entry) };
        }
        unsafe { Z3_func_interp_dec_ref(c, interp) };
        assert!(matches!(
            mapped.default,
            ValueEntry::Application { .. } | ValueEntry::Constant(_)
        ));
    }
    #[test]
    fn linked_prover_retries_invalid_bare_variable_trigger_without_losing_assumption() {
        use crate::interfaces::decider::prover::{Prover, ProverLike};
        use crate::state::{
            identifiers::Identifier,
            terms::{Quantifier, Sort, TermFactory, TermKind, TermOptions, Trigger},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let q = factory.quantification_without_triggers(
            Quantifier::Forall,
            vec![x.clone()],
            factory.greater(x.clone(), factory.int_literal(0)),
            "invalid".into(),
            false,
            None,
        );
        let q = factory
            .quantification_with_raw_triggers(&q, vec![Trigger { terms: vec![x] }])
            .unwrap();
        let y = factory.var(Identifier::new("y"), Sort::Int, false);
        let outer = factory.quantification_without_triggers(
            Quantifier::Forall,
            vec![y.clone()],
            q.clone(),
            "outer".into(),
            false,
            None,
        );
        let outer = factory
            .quantification_with_raw_triggers(&outer, vec![Trigger { terms: vec![y] }])
            .unwrap();
        let cleaned_outer = clean_invalid_triggers(&factory, &outer).unwrap();
        assert!(
            matches!(cleaned_outer.kind(), TermKind::Quantification { triggers, body, .. } if triggers.is_empty() && matches!(body.kind(), TermKind::Quantification { triggers, .. } if triggers.is_empty()))
        );
        let clean = clean_invalid_triggers(&factory, &q).unwrap();
        assert!(
            matches!(clean.kind(), TermKind::Quantification { triggers, .. } if triggers.is_empty())
        );
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
        let mut raw = LinkedZ3Prover::new("raw", factory.clone(), options.clone());
        raw.start(None).unwrap();
        assert!(
            raw.active().unwrap().assume(&q).is_err(),
            "raw invalid pattern should provoke Z3 error"
        );
        let mut p = LinkedZ3Prover::new("retry", factory.clone(), options);
        let reported = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let sink = reported.clone();
        p.set_warning_reporter(move |warning| sink.borrow_mut().push(warning.to_owned()));
        p.start(None).unwrap();
        p.assume(&q).unwrap();
        let warnings = p.take_warnings();
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].starts_with("Z3 error: "));
        assert_eq!(*reported.borrow(), warnings);
        assert!(p.assert_goal(&clean, None).unwrap());
    }
    #[test]
    fn invalid_trigger_goal_retry_keeps_both_assertion_modes_scoped() {
        use crate::interfaces::decider::prover::Prover;
        use crate::state::{
            identifiers::Identifier,
            terms::{Quantifier, Sort, TermFactory, TermOptions, Trigger},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let q = factory.quantification_without_triggers(
            Quantifier::Forall,
            vec![x.clone()],
            factory.greater(x.clone(), factory.int_literal(0)),
            "goal".into(),
            false,
            None,
        );
        let q = factory
            .quantification_with_raw_triggers(&q, vec![Trigger { terms: vec![x] }])
            .unwrap();
        for soft_assertions in [false, true] {
            let options = LinkedProverOptions {
                timeout: super::super::z3_prover_api::ApiTimeoutSettings {
                    default_timeout_ms: 0,
                    use_time_bounds: true,
                    resources_per_millisecond: 1,
                },
                counterexamples: false,
                report_reason_unknown: false,
                debug: false,
                soft_assertions,
                custom_options: vec![],
                disable_nonlinear: false,
            };
            let mut p = LinkedZ3Prover::new("goal-retry", factory.clone(), options);
            p.start(None).unwrap();
            assert!(!p.assert_goal(&q, None).unwrap());
            assert_eq!(p.push_pop_scope_depth(), 0);
            assert!(p.assert_goal(&factory.boolean(true), None).unwrap());
            assert!(!p.assert_goal(&factory.boolean(false), None).unwrap());
            assert_eq!(p.push_pop_scope_depth(), 0);
        }
    }
    #[test]
    fn documented_context_args_enable_proofs_and_reject_unknown_options() {
        use crate::interfaces::decider::prover::Prover;
        use crate::state::terms::{TermFactory, TermOptions};
        unsafe extern "C" {
            fn Z3_solver_get_proof(context: Raw, solver: Raw) -> Raw;
        }
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
        let mut p = LinkedZ3Prover::new("context", factory, options);
        let interrupt = p.cancellation_handle();
        assert!(!interrupt.interrupt());
        assert!(p.start(Some("unknown=true")).is_err());
        assert!(p.start(Some("proof=maybe")).is_err());
        assert!(p.start(Some("malformed")).is_err());
        p.start(Some("proof=true auto_config=false")).unwrap();
        let z = &mut p.active().unwrap().converter.context;
        let bool_sort = z.sort(NativeSort::Bool).unwrap();
        let no = z.literal(NativeLiteral::Bool(false), &bool_sort).unwrap();
        z.add(&no).unwrap();
        assert_eq!(z.check().unwrap(), SatResult::Unsat);
        let proof = unsafe { Z3_solver_get_proof(z.context.0, z.solver) };
        z.checked().unwrap();
        assert!(!proof.is_null());
        p.reset().unwrap();
        assert!(interrupt.interrupt());
        p.stop().unwrap();
        assert!(!interrupt.interrupt());
    }
    #[test]
    fn unknown_custom_option_is_reported_at_start() {
        use crate::interfaces::decider::prover::Prover;
        use crate::state::terms::{TermFactory, TermOptions};
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
            custom_options: vec![("smt.ferrum_unknown_option".into(), "true".into())],
            disable_nonlinear: false,
        };
        let mut p = LinkedZ3Prover::new("unknown", factory, options);
        let received = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let sink = received.clone();
        p.set_warning_reporter(move |message| sink.borrow_mut().push(message.to_owned()));
        p.start(None).unwrap();
        assert_eq!(
            p.take_warnings(),
            vec!["Z3 error: unknown parameterferrum_unknown_option"]
        );
        assert_eq!(received.borrow().len(), 1);
    }
    #[test]
    fn linked_z3_custom_solver_options_validate_types() {
        let mut z = LinkedZ3::new_with_source_options().unwrap();
        z.set_source_solver_options(
            &[
                ("smt.mbqi".into(), "TRUE".into()),
                ("random_seed".into(), "-1".into()),
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
            z.set_source_solver_options(&[("random_seed".into(), "2147483648".into())], false)
                .is_err()
        );
        assert_eq!(
            z.set_source_solver_options(&[("ferrum_unknown_option".into(), "true".into())], false)
                .unwrap(),
            vec!["Z3 error: unknown parameterferrum_unknown_option"]
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
