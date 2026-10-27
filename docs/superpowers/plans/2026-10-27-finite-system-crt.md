# Finite-System CRT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement and certify a full-width finite-system CRT solver, including exact overflow, composition, and permutation invariance.

**Architecture:** Preserve the root pair project; add a native `systems/` project with a scalar merge kernel and read-only fixed-array batch exports. Prove unbounded finite-list mathematics, then connect bounded machine execution to it. Reuse existing arithmetic and operational proof machinery where its hypotheses apply.

**Tech Stack:** Inference 0.0.6 commit 95db5e4170fdfd5080afdcb938c7704a790a7b24; WasmVerifier 8f485f037a270271bf2e1393c24fc0684097163b; Coq 8.20.1 in its devcontainer; Python and Node test harnesses.

**Spec:** `docs/superpowers/specs/2026-10-27-finite-system-crt-design.md`

## Global Constraints

- Use native Inference projects throughout.
- Keep the root pair project's source and emitted-code certificates stable.
- Batch capacity is 16; mathematical finite-list theorems have no capacity bound.
- Error precedence is invalid (-2), incompatible (-1), overflow (-3), then success.
- Overflow means the mathematical LCM exceeds 9223372036854775807.
- Empty input returns solution 0 and period 1. Inactive array slots are ignored.
- All handwritten proofs must be admission-free, independently kernel-checked, and audited against the existing assumption allowlist.
- All Rocq/opam work runs in the WasmVerifier container; do not change pinned dependencies.
- Connect every public export to actual compiler-emitted Wasm; distinguish proved mathematics, source contracts, and execution theorems.
- Do not claim universal termination of every reduction schedule from the existing existential-termination/all-normal-results convention.

## Review Focus

- A later contradiction or invalid entry must take precedence over an overflowing prefix, in every permutation.
- Fitting LCM does not imply intermediate CRT multiplication fits; use modular multiplication.
- Array prefixes and raw host pointer boundaries must not create unproved memory assumptions.
- Bare error codes lose information; composition of successful summaries requires representability hypotheses.
- Proof gates must fail on stale source/artifacts, missing targets, unexpected assumptions, and admitted generated certificates.

---

### Task 1: Native finite-system implementation and independent runtime tests

**Files:** Create `systems/Inference.toml`, `systems/src/main.inf`, `systems/scripts/demo.mjs`, `systems/scripts/check_runtime.mjs`, `tests/test_system_runtime.py`; extend `scripts/build.py` with a project-directory option and `.gitignore` for nested outputs.

**Interfaces:** Produce the four exact public scalar and batch signatures in the design. Helpers `gcd_positive`, `normalize`, `inverse_coprime` retain the old algorithms and occupy the first three generated function positions, enabling proof reuse. Add `add_mod` and `mul_mod`. Keep arrays read-only and avoid aggregate locals/returns.

- [ ] Write runtime tests using an independent arbitrary-integer oracle; observe expected failure without the project. Include empty, singleton, duplicate, count -1/17, inactive-invalid tails, full capacity, MAX modulus, exact-MAX period, overflowing zero solution, negative residue difference, and conflicting overflow-prefix permutations.
- [ ] Implement safe scalar merges and batch validation/pairwise/fold phases with the prescribed precedence. Implement source scalar contracts using safe terms, not overflowing specification expressions. Batch contracts remain Rocq targets because aggregate applications are unsupported.
- [ ] Add the runner with decimal string parsing before i64 coercion; marshal full arrays at offsets 0 and 128 and preserve JSON integer digits. CLI accepts `--json` followed by residue/modulus pairs; no pairs means empty. Exit codes 0 solved, 1 incompatible, 2 invalid, 3 overflow.
- [ ] Extend the build helper minimally with `--project-dir`, retaining root defaults and provenance checks. Native `infs build` must work in `systems/` directly.
- [ ] Run exhaustive small-system and deterministic full-width vectors, permutation and partition tests, and the existing runtime suite. Inspect emitted bodies for memory writes/stack mutation. Commit implementation and test evidence.

### Task 2: Full-width arithmetic and finite-list mathematics

**Files:** Create `specifications/CRTSystemStatements.v`, `proofs/CRTSystemArithmetic.v`, `proofs/CRTFinite.v`; extend the mathematical proof gate with exact targets and independent audits without weakening legacy checks.

**Interfaces:** Define normalized full-width inputs, finite-list solutions, periods, pairwise compatibility, canonical representation, result classification, and functional merge/fold models. Provide exact named targets for full-width arithmetic, finite existence, complete solution classes, canonical uniqueness, composition, overflow exactness, and permutation invariance. Existing `CRTMath.v` generalized CRT lemmas remain available.

- [ ] State exact targets and define executable mathematical models, including real finite-loop models matching Task 1 and their invariants/variants.
- [ ] Prove modular-add/multiply correctness and every machine bound; generalize EEA coefficient bounds without changing legacy bounded contracts. Prove guarded LCM and full-width scalar construction.
- [ ] Prove finite pairwise CRT using gcd/LCM distributivity; establish prefix representation, finite solver correctness, canonical uniqueness, all solutions, empty/singleton/duplicate laws.
- [ ] Prove concatenation composition, successful summary associativity/commutativity under precise hypotheses, monotone LCM overflow, and full result permutation invariance including failure classification.
- [ ] Run exact-target checks, transitive assumption audit, and coqchk in the container. Commit.

### Task 3: Execution semantics for read-only native modules

**Files:** Add focused modules under `proofs/systems/` for the runtime, read-only code predicate, store preservation, and normal-result uniqueness; reuse legacy generic context/confluence results where possible.

**Interfaces:** A shared runtime for `systems/out/main.v`, an invocation relation containing only actual Wasm reduction and result decoding, explicit input-memory predicates, and a theorem giving uniqueness of normal numeric results for reachable read-only native code. No postcondition may be baked into the relation.

- [ ] Establish module validity and runtime instantiation under the generated module; array regions are readable 128-byte areas with no pointer wrap. Confirm source read-only parameters cause no writes or stack allocation.
- [ ] Extend/prove operational uniqueness for the actual read-only instruction subset, including loads, and native calls with read-only bodies. Do not apply the legacy resource-free theorem to memoryful stores.
- [ ] Check a small generated array-access execution case before applying the machinery to the batch loop. Prove load semantics and bounds guards against the input-memory predicate.
- [ ] Compile, audit assumptions, independently kernel-check, and commit reusable execution machinery.

### Task 4: Scalar compiled-Wasm correctness

**Files:** Add focused arithmetic/helper/merge proof modules under `proofs/systems/`; add exact scalar execution targets and exact emitted scalar specification certificates.

**Interfaces:** Task 1 emitted functions, Task 2 arithmetic/model theorems, and Task 3 runtime/invocation/normal-uniqueness results. Public targets quantify over all signed i64 inputs and classify every normal result exactly.

- [ ] Reuse or generalize old gcd/normalize/EEA semantic proofs for full-width preconditions and the new runtime without altering certified old statements.
- [ ] Prove emitted modular multiplication loop execution and arithmetic guards from its mathematical invariant/variant.
- [ ] Prove both scalar public exports, including validation, incompatibility and overflow branches, with existence of normal execution and correctness of every normal result.
- [ ] Prove exact generated scalar source specifications; ensure their closure excludes generated admitted skeletons. Compile, audit, kernel-check, commit.

### Task 5: Batch execution, public documentation, and final verification

**Files:** Batch and final target modules under `proofs/systems/`; `scripts/check_system_proofs.py`; proof-gate tests; `systems/README.md`; root README/walkthrough/proof documentation; new evidence JSON.

**Interfaces:** Task 2 finite solver correctness, Task 3 array execution/uniqueness, Task 4 scalar execution, and exact Task 1 emitted batch functions.

- [ ] Prove validation/pair scanning/fold emitted loops with their exact prefix invariants, bounds guards, and finite variants. Instantiate both batch execution targets with explicit ABI memory premises.
- [ ] Connect composition and permutation theorems to actual public execution results, not just an unrelated mathematical model.
- [ ] Add a fail-closed proof gate binding project/source/artifact/proof hashes and checking every exact target, assumptions, and kernel integrity. Include mutation/negative-control tests for overflow guard errors, wrong composition, missing/stale targets, and generated admission leakage.
- [ ] Document native build/run commands, all four error outcomes, capacity versus unbounded mathematics, precise proof strength and trust boundary. Include three-or-more-constraint public examples and reusable scalar merging.
- [ ] Rerun legacy and new checks from clean output directories, capture evidence, review the whole branch, fix findings, and create/attach a follow-up PR with accurate results.
