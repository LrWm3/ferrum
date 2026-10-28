# Differences from upstream

Implementation has begun. Unresolved upstream issues remain proposals in source
comments; the following changes are adopted explicitly.

## Dominator label update

Silver `cfg/utility/Dominators.scala` evaluates `label(index) == ancestorLabel`
where path compression requires assigning the ancestor's better label. The
source-compatible translation was committed separately before this correction.

For blocks 0 through 3, entry 0, and edges in order
`0->1, 0->2, 1->2, 1->3, 2->3`, upstream behavior gives immediate dominator 1
for block 3. Path `0->2->3` avoids block 1, so only block 0 can immediately
dominate block 3. A temporary independent iterative-dominator implementation
and the compiled source-compatible Rust port confirmed the mismatch.

Ferrum assigns the better label during compression. The four-block regression
checks the correct result, guarding a graph relation needed by loop detection.
This is an explicit correctness fix, not a claim that every CFG algorithm has
been broadly validated.

## Canonical rational hashing

Silver `utility/Common.scala` compares normalized rational values but hashes its
original numerator/denominator arguments. Ferrum hashes the reduced representation,
so equal fractions satisfy Rust's `Eq`/`Hash` contract. Exact arithmetic, ordering
and displayed reduced fractions remain unchanged. Native hash values are not a
cross-runtime serialization format. Focused equivalent-fraction hash checks pass;
term interning and cache behavior remain part of later integration validation.

## Explicit native I/O failures

Silver `Common.PrintWriter` uses Java's error-suppressing writer. The Rust adapter
returns `io::Result` for writes and flushes rather than silently suppressing errors.
Callers must propagate or explicitly report these errors. Parent-directory creation,
append/truncate behavior and explicit line auto-flush are retained.

## Stable term equality mode

Silicon's term equality consults the global flyweight configuration. Rust terms
will retain the mode chosen at construction, with process-wide strong flyweight
pooling and structural nonflyweight equality. Mixing modes in one graph is rejected
to preserve a stable, symmetric `Eq`/`Hash` contract. Configuration remains explicit;
this does not normalize formulas or change solver encodings. This boundary is
being implemented and still needs term/cache integration checks.

## Native resource loading

Pinned text resources are embedded byte-for-byte; no Java classloader is required.
Preamble lookup uses an injectable native resource provider. General `jar:` and
`resource:` URL-to-filesystem conversion in Silver Paths remains an explicit port
gap, not an equivalent implementation. File URLs and ordinary path helpers retain
their implemented native behavior. Resource bytes are checked against pinned Git
objects; full parser/frontend resource integration is still pending.

When adopting a deviation, record its pinned source location, upstream behavior,
Rust behavior, reason, affected callers, and validation plan here. Moving files,
changing representations, or replacing JVM mechanisms does not itself establish
that behavior is equivalent.
