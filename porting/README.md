# Port status and checks

The description pass covered all 336 mapped Silver/Silicon source and test files.
The Cargo workspace now has 403 mapped and assembly modules. `described` files
remain comment-only; `skeleton` files contain partial implementations with explicit
gaps; `ported` means translated bodies compile, not that compatibility has been
proved. Reviewed progress and remaining work are recorded per file.

The CLI connects configuration, parsing, default plugins, consistency checks and
source-shaped Silicon rules to the native Z3 stdio transport. End-to-end smoke
checks cover valid and invalid ordinary methods, contracts, branches, allocation,
field permissions and method calls. Unsupported features return execution errors.
The default runtime currently uses one worker. Loops, fold/unfold, scoped
unfolding, heap-independent quantifiers, selected generic domain axioms and
primitive Seq/Set/Map instances now reach Z3. Heap-dependent functions, general
domain instances, quantified resources, wands, complete exhale and advanced
reporting remain incomplete. No comparative speed improvement has been established.

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

Every one of the 269 mapped production source files now has a first Rust
implementation, with remaining work recorded explicitly. The workspace has
activated every module and embedded the pinned resources. It includes typed
ASTs, checked parser/frontend subsets, CFG lowering,
plugin transformations, terms and heap representations, solver process transport,
and translated symbolic execution, permission, predicate and function algorithms.
Several algorithms depend on explicit service traits that still need concrete
implementations. Unsupported paths return errors; they must not imply successful
verification.

Focused checks cover specific identity, translation, traversal and solver-protocol
questions. Review has already caught differences in rewrite recursion and AST
location traversal; corresponding regressions accompany the fixes. These checks
are not a substitute for the compatibility campaign in the plan.

Of 67 source-mapped files under `tests/upstream/`, 66 intentionally remain briefs
for the later broad testing pass in PLAN.md. `TestInput` already has grouping/tag
helpers; it is not a completed suite. Production `testing/` helpers are part of
the implementation pass. A source module having a Rust body marks first-pass
coverage only; it does not close the gaps listed in its header
and inventory entry.

The final first-pass workspace checks, build and test-target compilation passed
with the lockfile and offline dependencies. Clippy completed with warnings about
source-shaped type/API complexity, nested conditionals, mutable key types and
other cleanup items; these remain review work. Subsequent native integration
checks distinguish successful verification (exit 0), proof failure (exit 1), and
syntax/unsupported execution errors (exit 2). The source frontend and diagnostic
regressions pass; the broad upstream compatibility suite has not been run.

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
