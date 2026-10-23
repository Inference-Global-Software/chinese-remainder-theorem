# Generalized CRT Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans for integration and
> superpowers:dispatching-parallel-agents for the independent mathematical proof
> files. Steps use checkboxes to record progress.

**Goal:** Implement and test the bounded generalized CRT in Inference, discharge
the mathematical targets, and connect generated Wasm obligations to the real
verifier where its required environment is available.

**Architecture:** Keep the executable arithmetic and source contracts together
in `src/crt.inf`. Separate abstract CRT proofs and loop/safety proofs over the
existing statements. Compile one proof-mode artifact for runtime tests and the
schedule demo; preserve the distinction between mathematical proofs, tests,
and certificates for generated Wasm.

**Tech stack:** Inference 0.0.6 / ABI 1.10, Coq 8.20, Python 3, Node BigInt,
WasmVerifier with its pinned container dependencies.

**Spec:** [Exact contracts and invariants](../../specifications.md),
[`CRTStatements.v`](../../../specifications/CRTStatements.v).

## Global constraints

- `1 <= m,n <= 2147483647`; `0 <= a < m`; `0 <= b < n`.
- `i64` inputs, intermediates, and results; public APIs validate all `i64` inputs.
- `crt_solve(a,m,b,n)` returns `-2` invalid, `-1` incompatible, otherwise canonical.
- `crt_period(m,n)` returns `-2` invalid, otherwise the lcm.
- No admissions, new axioms, or altered target statements in completed proofs.
- Run the artifact whose exact bytes are recorded. Never present stub elaboration
  or finite testing as a proof of compiled execution.
- Existing authorization is to implement and test now. Execute without another
  design approval round; the previous documents supply the accepted design.

## Review focus

- CLI must reject integers outside `i64` before JavaScript/Wasm can truncate them.
- Negative differences must be normalized; modulus one must skip inversion.
- Equal/noncoprime moduli must distinguish incompatibility from invalid input.
- Values above `2^53` must survive argument and result transport exactly.
- Proof audit must detect admissions and expose transitive assumptions; generated
  Wasm obligations must remain visibly pending until independently discharged.

### Task 1: Executable implementation and runtime interface

**Files:** `src/crt.inf`, `scripts/build.py`, `scripts/demo.mjs`,
`tests/test_runtime.py`, `tests/runtime.mjs`, `Makefile`.

**Interfaces:** Preserve the five scalar functions and all 15 contracts in the
probe. Build writes `build/crt/crt.wasm`, `crt.v`, and a hash manifest. Demo takes
four decimal arguments in order `a m b n` and uses BigInt throughout.

- [x] Add tests for the real build and CLI; verify failure before implementation.
- [x] Move the tested recurrence into `src/crt.inf` with documented contracts.
- [x] Implement build and CLI; reuse independent runtime-vector generators.
- [x] Exercise exhaustive small inputs, deterministic large inputs, full-width
  invalid values, and literal success/impossibility/error demo cases.
- [x] Compile three deliberate faulty variants and require concrete failing cases
  for missing compatibility, missing signed normalization, and noncanonical output.
- [x] Run the complete runtime suite and commit the implementation/tests.

### Task 2: Abstract generalized CRT proofs

**Files:** `proofs/CRTMath.v`; imports the unchanged `CRTStatements.v`.

**Interfaces:** Theorems `normalization_proved`, `reduction_proved`,
`generalized_crt_proved`, `canonical_unique_proved`, `all_solutions_proved`,
`incompatible_proved`, `construct_proved`, `crt_bounds_proved` discharge their
corresponding `T_*` targets, without relying on any executable/probe assumptions.

- [x] Attempt the target proof build before the file exists and record the failure.
- [x] Prove divisibility/reduction helpers, existence, uniqueness, periodicity,
  construction, and machine arithmetic bounds.
- [x] Compile using `coqc -Q specifications CRT -Q proofs CRT proofs/CRTMath.v`.
- [x] Audit `Print Assumptions` for every exported theorem; require closure.

### Task 3: Loop invariants, bounds, and termination proofs

**Files:** `proofs/CRTLoops.v`; imports the unchanged statements, independently
of `CRTMath.v`.

**Interfaces:** Close `T_normalize`, `T_gcd_init/step/exit`,
`T_eea_init/step/step_bounds/exit`. Add a terminating mathematical recurrence
whose result follows from the invariants, with no claim of Wasm refinement.

- [x] Attempt the target proof build before the file exists and record the failure.
- [x] Prove invariant initialization, preservation, final result and decreasing
  natural-number variant, including final-iteration coefficient bounds.
- [x] Compile using `coqc -Q specifications CRT -Q proofs CRT proofs/CRTLoops.v`.
- [x] Audit `Print Assumptions` for every exported theorem; require closure.

### Task 4: Verification integration, evidence, and publication

**Files:** `scripts/check_proofs.py`, `proofs/README.md`, `docs/implementation.md`,
`docs/evidence/implementation.json`, updated README and Makefile; generated-Wasm
proof companions if the real verifier environment is accessible.

- [x] Make a single command build, run runtime and mutation tests, compile the
  proofs, run `coqchk`, and audit all theorem assumptions.
- [x] Retry the real verifier container; user is enabling Docker access. Preserve
  raw generated definitions and target types in any discharge companion.
- [x] Discharge structural typing and behavioral obligations against real
  semantics; do not substitute the signature stub for this step.
- [x] Record artifact hashes, versions, proof endpoints and any unresolved gap.
- [x] Review the whole change independently, fix substantive findings, rerun
  relevant checks, then publish the work with accurate proof status.
