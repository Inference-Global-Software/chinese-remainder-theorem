# Chinese Remainder Theorem in Inference

A constructive implementation of the generalized Chinese Remainder Theorem
(CRT), written in Inference and compiled to WebAssembly.

**Status: implemented, tested, and proved against the generated Wasm contracts.**
The generalized CRT, construction, arithmetic bounds, and Euclid loop invariants
are proved in Rocq. Execution proofs connect all five emitted function bodies to
the mathematical model and discharge the compiler's exact module and 15 source
contracts using the real WasmVerifier library. All five original execution
targets are also proved: calls have terminating executions, and every normally
returned result satisfies its contract. See [proof coverage and trust
boundary](proofs/README.md).

## Run it

Requirements: Python 3.9+, Node with WebAssembly/BigInt support, and the Inference
compiler. The recorded compiler is `infc 0.0.6`, revision `95db5e4`, ABI `1.10`.
Checking the mathematical proofs additionally requires Coq 8.20.x (`coqc` and
`coqchk`). Generated-Wasm proofs use the [pinned verifier container](scripts/wasm_environment/README.md).

```sh
make demo INFC=/path/to/infc
```

This compiles [src/crt.inf](src/crt.inf) in proof mode and runs the schedule example:

```text
First coincidence: 14
Repeat period: 18
All integer solutions: 14 + 18 * k
```

Pass your own residues and moduli in order `a m b n`:

```sh
node scripts/demo.mjs 2 6 4 9
node scripts/demo.mjs --json 2147483646 2147483647 2147483645 2147483646
make check INFC=/path/to/infc
```

All integer transport uses BigInt or decimal strings. The CLI rejects values
outside signed `i64` before passing arguments to Wasm. Exit status is 0 for a
solution, 1 for incompatibility, 2 for invalid input, and 3 for an execution/setup
error. `make check` runs the runtime, CLI, mutation, and proof-audit tests, then
compiles and independently checks the mathematical proofs.

## The problem

Given positive moduli `m`, `n` and normalized remainders `a`, `b`, find the smallest
nonnegative integer `x` satisfying both:

```text
x mod m = a
x mod n = b
```

The generalized CRT says that a solution exists exactly when `gcd(m, n)` divides
`b - a`. When it exists, the solution is unique in `0 <= x < lcm(m, n)`.

For example, `x mod 6 = 2` and `x mod 9 = 5` have the canonical solution **14**.
All integer solutions are `14 + 18k`, for integer `k`. Changing the second
remainder to **4** makes the conditions incompatible.

## A useful application: synchronizing periodic schedules

One process runs at times `2, 8, 14, 20, ...`; another at `5, 14, 23, 32, ...`.
Their first coincidence is at time **14**, and they coincide every **18** time
units thereafter. The same algorithm can identify offsets for which they never
coincide.

This example connects the mathematics to an executable algorithm for developers
and gives a public demonstration a concrete question to answer.

## Contracts

- The gcd and modular-inverse routines compute their mathematical specifications.
- Every successful CRT result satisfies both congruences.
- Every compatible input produces a solution.
- The returned solution is the unique one in the canonical interval.
- A mathematical failure result means that no solution exists.
- Calls have terminating executions and arithmetic stays within its machine representation.
- Invalid API inputs are distinguished from mathematically incompatible inputs.

The implementation accepts moduli from `1` through `2^31 - 1`, normalized
nonnegative remainders, and uses `i64` arithmetic. `crt_solve(a,m,b,n)` returns
`-2` for invalid input, `-1` for valid incompatible input, and otherwise the
canonical solution. `crt_period(m,n)` returns `-2` for invalid moduli and otherwise
their lcm. These are the only two exported functions. Internal helpers have
explicit preconditions. The mathematical CRT theorem covers unbounded integers.

## Verification approach

Inference contains the executable algorithm and 15 source specifications. The
compiler produces Wasm and Rocq proof obligations. The mathematical proofs are
assumption-free. Separate proofs establish actual finite executions in one
instantiated runtime, realize the function interpretation, and discharge the
exact generated helper and public `ValidSpec` obligations. These proofs use the
verifier's explicitly audited upstream assumptions. An operational confluence
proof establishes unique normal results for actual Wasm executions; it connects
the witnesses to all five original execution targets.

The demonstration must execute the artifact covered by the proof evidence.
Builds record compiler and artifact hashes in `build/crt/manifest.json`. The proof
checks write target names, source hashes, and assumption audits to
`build/proofs/report.json` and `build/wasm-proofs/report.json`. Run the latter
inside the verifier container with `make wasm-proofs`; see the
[reproduction commands](docs/implementation.md).

See the [proposed design](docs/superpowers/specs/2026-10-23-generalized-crt-design.md)
for the interfaces, proof structure, and acceptance criteria.

## Specifications and feasibility results

- [Exact theorem statements, loop invariants, and arithmetic bounds](docs/specifications.md).
- [Rocq proposition definitions](specifications/CRTStatements.v) and [completed mathematical proofs](proofs/README.md).
- [Inference implementation and contracts](src/crt.inf).
- [Implementation checks and reproduction commands](docs/implementation.md).
- [Historical feasibility check](docs/specification-check.md).

All 15 source contracts translate, including nested existence/uniqueness
quantifiers. Sixteen exact mathematical/loop targets and four recurrence
termination/correctness results are proved, together with all five execution
targets. The public Wasm functions pass 23,274 reference-vector checks; three deliberately faulty variants produce concrete
counterexamples. Loop proofs live in Rocq, and source quantifiers remain bounded
by their machine types.

## References

Start with the [implementation reading guide](references/README.md). It includes
two research PDFs, four paper citations, a computational number-theory textbook,
arithmetic-bounds analysis, and the relevant proof-library and compiler contracts.
Each reference is mapped to the implementation or proof obligation it supports.

The collection also contains [BibTeX citations](references/references.bib) and
[PDF provenance, licenses, and checksums](references/manifest.json).

RSA round-trip correctness is a possible later application of the verified
arithmetic. It is outside the initial project scope.
