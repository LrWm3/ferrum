//! Bundled upstream resources for the native Ferrum runtime.
//! See PLAN.md and porting/resources.toml for provenance and checksums.

pub fn get(name: &str) -> Option<&'static str> {
    match name.trim_start_matches('/') {
        "cvc5config.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/cvc5config.smt2"
        ))),
        "dafny_axioms/DafnyPrelude.bpl" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/DafnyPrelude.bpl"
        ))),
        "dafny_axioms/LICENSE.txt" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/LICENSE.txt"
        ))),
        "dafny_axioms/maps.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/maps.vpr"
        ))),
        "dafny_axioms/multisets.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/multisets.vpr"
        ))),
        "dafny_axioms/multisets_old.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/multisets_old.vpr"
        ))),
        "dafny_axioms/sequences.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/sequences.vpr"
        ))),
        "dafny_axioms/sequences_old.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/sequences_old.vpr"
        ))),
        "dafny_axioms/sets.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/sets.vpr"
        ))),
        "dafny_axioms/sets_old.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/dafny_axioms/sets_old.vpr"
        ))),
        "field_value_functions_axioms.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/field_value_functions_axioms.smt2"
        ))),
        "field_value_functions_axioms_no_triggers.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/field_value_functions_axioms_no_triggers.smt2"
        ))),
        "field_value_functions_declarations.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/field_value_functions_declarations.smt2"
        ))),
        "heapwrappers_axioms.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/heapwrappers_axioms.smt2"
        ))),
        "heapwrappers_functions.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/heapwrappers_functions.smt2"
        ))),
        "logback.xml" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/logback.xml"
        ))),
        "magic_wand_snap_functions_declarations.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/magic_wand_snap_functions_declarations.smt2"
        ))),
        "maps_axioms.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/maps_axioms.smt2"
        ))),
        "maps_functions.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/maps_functions.smt2"
        ))),
        "mask_axioms.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/mask_axioms.smt2"
        ))),
        "mask_functions.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/mask_functions.smt2"
        ))),
        "preamble.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/preamble.smt2"
        ))),
        "predicate_snap_functions_axioms.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/predicate_snap_functions_axioms.smt2"
        ))),
        "predicate_snap_functions_axioms_no_triggers.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/predicate_snap_functions_axioms_no_triggers.smt2"
        ))),
        "predicate_snap_functions_declarations.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/predicate_snap_functions_declarations.smt2"
        ))),
        "sortwrappers.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/sortwrappers.smt2"
        ))),
        "z3config.smt2" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/z3config.smt2"
        ))),
        _ => None,
    }
}
