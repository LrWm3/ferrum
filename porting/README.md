# Port status and checks

The description pass covered all 336 mapped Silver/Silicon source and test files
and four Ferrum assembly files. Implementation is now underway in the Cargo
workspace. `described` files remain comment-only; `skeleton` files contain partial
implementations with explicit gaps, and `ported` files have translated bodies
that compile. Most of the verifier is still unimplemented, and verification
requests explicitly fail with `PortIncomplete`.

- [sources.toml](sources.toml) pins the two semantic baselines.
- [modules.toml](modules.toml) maps every source file to its Rust destination and
  records reviewed progress. Symbol outlines live in the destination comments.
- [resources.toml](resources.toml) records unchanged embedded upstream resources
  and their checksums.
- [non_rust_files.tsv](non_rust_files.tsv) accounts for the other 1,993 tracked
  upstream paths, including fixtures, resources, documentation, tooling and the
  duplicate Silver submodule. Dispositions are provisional plans, not completed
  asset imports or exhaustive content reviews.
- [conventions.md](conventions.md) separates shared requirements from open Rust
  representation choices. [differences.md](differences.md) records adopted
  behavioral departures.

Three `gpt-6.1-terra` agents read source files and their relevant collaborators,
wrote separate batches, and performed targeted peer reviews. Coordinator review
included representative source/brief comparisons, mapping and stage checks, and
reconciliation of peer corrections. Higher-risk peer checks covered parser and
plugin transformations, state merging, heap encodings, retries, continuations,
quantified permissions, snapshot caches and function-axiom phases. This does not
prove code correct or replace the broader testing pass in [PLAN.md](../PLAN.md).

The implementation pass has activated every module, embedded the pinned resources,
and added core AST/parser representations, source type and name utilities, generic
CFG algorithms and lowering, and Silicon terms, stores and heap/chunk support.
Most source modules still contain descriptions only. Parser ownership and rewriting, verification rules,
solver orchestration and complete frontend assembly remain open. Targeted
regressions cover specific identity and translation issues; no end-to-end
verification or performance improvement has been demonstrated.

Run the inventory and implementation checks from the repository root:

```sh
python3 tools/check_porting.py --complete --upstream
cargo fmt --all --check
cargo check --workspace --all-targets --locked
git diff --check
```

`--upstream` requires the pinned Git objects in the sibling checkouts named in
`sources.toml`; omit it for local document checks without those checkouts. To
check selected descriptions while editing, pass their repository-relative paths.
The checker validates inventory coverage, unique destinations, source links,
stage-specific documentation requirements, comment-only contents for files still
marked `described`, attribution for translated code and copied resource bytes.
`--complete` means all source descriptions exist or have progressed; it does not
mean all implementations are complete. Source-specific prose and implementation
semantics still need review; these checks do not establish behavioral compatibility.

When implementing a file, retain its pinned source reference, update the brief
and inventory, and replace the description-stage checks with the implementation
checks in the plan. Resolve cross-file representation choices before treating
proposed signatures or ownership as settled.
