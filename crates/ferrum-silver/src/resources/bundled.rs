//! Bundled upstream resources for the native Ferrum runtime.
//! See PLAN.md and porting/resources.toml for provenance and checksums.

/// Native replacement for FastParser.importStandard's class-loader resource lookup.
/// The parser supplies a normalized path relative to the upstream import directory.
#[derive(Clone, Copy, Debug, Default)]
pub struct BundledImportLoader;

impl crate::ast::utility::file_loader::FileLoader for BundledImportLoader {
    fn load_content(&self, path: &std::path::Path) -> std::io::Result<String> {
        let path = path.to_str().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "non-UTF-8 standard import",
            )
        })?;
        let name = format!("import/{}", path.replace('\\', "/"));
        let source = get(&name).ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::NotFound,
                format!("resource '{name}' was not found in bundled imports"),
            )
        })?;
        // Source.fromResource.getLines().mkString("\n") + "\n".
        Ok(source.lines().collect::<Vec<_>>().join("\n") + "\n")
    }
}

pub fn get(name: &str) -> Option<&'static str> {
    match name.trim_start_matches('/') {
        "import/adt/contains.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/adt/contains.vpr"
        ))),
        "import/adt/derives.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/adt/derives.vpr"
        ))),
        "import/decreases/all.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/all.vpr"
        ))),
        "import/decreases/bool.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/bool.vpr"
        ))),
        "import/decreases/declaration.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/declaration.vpr"
        ))),
        "import/decreases/int.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/int.vpr"
        ))),
        "import/decreases/multiset.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/multiset.vpr"
        ))),
        "import/decreases/perm.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/perm.vpr"
        ))),
        "import/decreases/predicate_instance.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/predicate_instance.vpr"
        ))),
        "import/decreases/predicate_instance_nested.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/predicate_instance_nested.vpr"
        ))),
        "import/decreases/rational.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/rational.vpr"
        ))),
        "import/decreases/ref.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/ref.vpr"
        ))),
        "import/decreases/seq.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/seq.vpr"
        ))),
        "import/decreases/set.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/decreases/set.vpr"
        ))),
        "import/predicateinstance/pi.vpr" => Some(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/resources/import/predicateinstance/pi.vpr"
        ))),
        _ => None,
    }
}
