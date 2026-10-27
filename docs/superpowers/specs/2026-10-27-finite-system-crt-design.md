# Verified finite-system CRT

## Purpose

Extend the pair example into a useful finite-system solver whose implementation
has explicit machine limits and whose proof explains composition and ordering.
Preserve the existing pair API and its checked certificates as a regression
baseline. Use native Inference projects throughout.

## Approaches and decisions

The alternatives are a scalar streaming kernel with host orchestration, or an
Inference batch solver over fixed arrays. The latter keeps validation, checking,
and accumulation in Inference; the former supports arbitrary host list lengths
but leaves the concrete host loop outside the Inference execution proof.

The proposed default is an Inference batch solver with capacity 16, backed by a
full-width scalar merge API. This is the implementer's proposed boundary, not a
user-selected capacity. Mathematical finite-list theorems have no capacity bound.
The pinned compiler supports fixed arrays but does not support aggregate arguments
to specification applications. Consequently scalar contracts use source specs;
batch contracts must be stated directly over the emitted Wasm execution relation.
Do not present successful specification emission as proof of batch correctness.

The second choice concerns error precedence. The proposed default is invalid
input, then incompatibility, then overflow, then success. Validate the entire
active input and check all pairs before accumulating, so an early overflow cannot
hide a later contradiction. This costs quadratic compatibility checking.

These defaults may be revised by the user's pending clarification. No compiler,
verifier, or WasmCert upgrade is part of this work.

## API and representation

Create the native project `systems/`, independently buildable with `infs build`.
Keep the root pair project's source and emitted-code certificates stable.

Scalar exports:

- `crt_merge_solve(a: i64, m: i64, b: i64, n: i64) -> i64`
- `crt_merge_period(a: i64, m: i64, b: i64, n: i64) -> i64`

Batch exports:

- `crt_system_solve(residues: [i64; 16], moduli: [i64; 16], count: i32) -> i64`
- `crt_system_period(residues: [i64; 16], moduli: [i64; 16], count: i32) -> i64`

Active entries are the prefix of length `count`. Inactive slots are ignored.
Every active modulus satisfies `1 <= m <= 9223372036854775807`; residues are
normalized, `0 <= a < m`. Batch length outside 0..16 is invalid. Scalar parameters
are ordinary i64 values. Array ABI pointers must denote readable complete arrays
under the compiler ABI; arbitrary forged raw host pointers are not source values.
The runner must enforce this boundary and document it.

An emitted-code probe with the pinned compiler confirms that read-only array
parameters require only loads, with no shadow-stack allocation or writes. Keep
batch arrays read-only and avoid compound locals/returns. The execution proof
must check that the final emitted bodies retain this property. Then arbitrary
aliasing between the two input regions is harmless, the stack global is unused,
and input addresses need only fit the complete 128-byte readable regions without
32-bit address wrap. The runner will place arrays at offsets 0 and 128 in the
exported one-page memory. If compilation introduces writes, revisit these
premises before claiming verification.

Both fields use the same error codes and classification:

| Code | Meaning |
| --- | --- |
| -2 | Invalid input |
| -1 | Valid but inconsistent system |
| -3 | Valid compatible system whose mathematical LCM exceeds i64 maximum |
| nonnegative | Canonical solution (solve) or positive LCM (period) |

The empty system returns solution 0 and period 1. Overflow concerns representation
of the entire solution class, even when a small solution such as zero exists.

## Algorithms and safety

Use Euclid and extended Euclid as in the existing implementation, generalizing
coefficient and remainder bounds to the full positive i64 range. Before computing
`(m / gcd(m,n)) * n`, check `m / gcd(m,n) > MAX / n`.

Use modular addition and repeated doubling for modular multiplication. For
`0 <= x,y < d`, compute `(x+y) mod d` as `x-(d-y)` when `x >= d-y`, otherwise
`x+y`. The multiplication loop halves a nonnegative multiplier, retaining a
normalized accumulator and multiplicand. This avoids overflowing the CRT product
even when the final period fits. Do not rely on wrapping arithmetic for a theorem
about mathematical multiplication.

Batch phases: validate active prefix; check compatibility for all active pairs;
fold canonical states from `(0,1)` using the full-width merge operation. Detect
overflow before multiplying. Once a compatible prefix overflows, its LCM divides
the final LCM, so overflow is final. Avoid any unchecked intermediate arithmetic.

## Mathematical contracts and invariants

For a list C of normalized residue/modulus pairs, define:

- `Sol(C,x)`: every `(a,m)` in C satisfies `m | x-a`.
- `L(C)`: fold of positive LCM, starting at 1.
- `Pairwise(C)`: for all entries `(a,m),(b,n)`, `gcd(m,n) | b-a`.
- `Rep(C,r,L)`: `L=L(C)`, `0<=r<L`, and for every integer x,
  `Sol(C,x) <-> L | x-r`.

Prove finite CRT existence iff pairwise compatibility; canonical existence and
uniqueness; the exact complete solution class; empty, singleton and duplicate
laws; and period divisibility for prefixes/subsystems.

Prove merge composition: if states represent A and B, their successful merge
represents `A ++ B`. Incompatibility of the merge is equivalent to inconsistency
of the concatenation. Overflow is exact when valid compatible concatenation has
LCM above MAX. State precisely that independently overflowing blocks cannot be
reconstructed from a bare error code; composition theorems require representable
successful block summaries, or reason over mathematical summaries.

Prove order independence for all permutations: validation class, compatibility,
LCM, and canonical successful value are unchanged. Derive associativity and
commutativity of successful composition, including representability hypotheses.

Validation invariant: all entries before the cursor are valid. Pair scan
invariant: all lexicographically earlier pairs are compatible. Accumulation
invariant: the current `(r,L)` represents exactly the processed prefix, is
canonical, and fits i64. Variants are finite index distances. Modular multiply
invariant: ranges plus `acc + multiplicand * remaining` congruent to the original
product; variant is the remaining multiplier. EEA retains Bezout, determinant,
opposite-sign and weighted absolute coefficient invariants from the pair proof.

## Verification and evidence

Connect every public export to actual compiler-emitted Wasm, with no mathematical
postcondition baked into the execution relation. Prove existence of a terminating
nontrapping normal execution and correctness of every normal result, matching the
existing execution-target convention. Do not claim universal termination of every
possible operational reduction schedule without proving that stronger statement.
For array functions, include input memory and ABI premises explicitly and account
for generated bounds checks and shadow-stack operations.

All handwritten proofs close with Qed/Defined and pass transitive-assumption audits
and independent kernel checking. Generated admitted certificates must not enter
the dependency closure. Use the existing upstream assumption allowlist. Keep all
Rocq/opam work in the WasmVerifier container. Record source, manifest, emitted Wasm,
and proof hashes; stale artifacts must fail the proof gate.

Runtime tests use an independent Python arbitrary-integer oracle, exhaustive small
systems, deterministic random systems, every permutation of selected systems,
partition/regrouping cases, both signs of residue differences, repeated moduli,
empty/singleton/capacity boundaries, and exact/above-i64 LCM boundaries. Include a
valid inconsistent system with an overflowing prefix and all input permutations.
Exercise mutations of overflow guards and composition so vacuous tests/proofs fail.

## Completion

Document running both native projects, the exact proved properties, execution
semantics, array ABI, finite runtime capacity, overflow precedence, and trusted
dependencies. Rerun the existing checks plus the new gates in a clean output
directory, record results, review the whole branch, and open a follow-up PR.
Repository visibility and licensing changes are outside this extension.
