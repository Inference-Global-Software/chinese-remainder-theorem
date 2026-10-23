# CRT Execution Targets Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans for integration and
> superpowers:dispatching-parallel-agents for the independent operational
> uniqueness proof and target adapters. Track progress with checkboxes.

**Goal:** Prove all five original execution targets and update PR #1.

**Architecture:** Define execution by actual WasmCert reductions of calls in the
existing CRT runtime, with signed decoding of returned i64 values. Combine the
existing terminating witnesses with an operational normal-result uniqueness
proof, then instantiate each unchanged target. Keep the common semantics proof
separate from the five API adapters.

**Tech stack:** Pinned Coq 8.20.1/WasmCert 2.2.0/WasmVerifier container; existing
Inference proof-mode artifact and Python proof gate.

**Spec:** `specifications/CRTStatements.v`, `docs/specifications.md`.

## Global constraints

- Preserve every original target definition and the existing executable bytes.
- Execution must not encode the expected answer, mathematical model, or desired
  postcondition. Include every normally returned result of actual invocation.
- Quantify over arbitrary initial host state; account for final host/store state.
- No admissions, additional axioms, unchecked tactics, or unresolved uniqueness
  hypotheses in final endpoints.
- Compile all Wasm proofs only in the existing authorized Docker environment.
- Reuse the current PR branch and update the existing PR; no merge is requested.

## Review focus

- A raw result is decoded as signed i64, preventing congruent out-of-range Z
  aliases from satisfying the execution relation.
- Existence premises are inhabited and cannot hide invalid public inputs.
- Universal correctness covers all normal results, not just selected witnesses.
- Host callbacks and resource mutations are excluded by proved runtime facts.
- Contextual trap reductions, branches, and return/frame behavior must be handled
  by the operational uniqueness proof, not assumed deterministic by inspection.

### Task 1: Raw invocation semantics and operational uniqueness

**Files:** `proofs/wasm/CRTExecutionFrames.v`,
`proofs/wasm/CRTExecutionDeterminism.v`.

**Interfaces:** Preservation of host state for resource-free native stores;
normal-result uniqueness for actual `reduce_trans` runs from a shared initial
configuration. Existing `CRTStorePure` supplies store preservation.

- [x] Observe that the required uniqueness endpoint is absent in the real library.
- [x] Prove preservation/context foundations and normal-result uniqueness.
- [x] Compile and audit assumptions under the pinned real verifier.

### Task 2: Five unchanged execution targets

**File:** `proofs/wasm/CRTExecutionTargets.v`.

**Interfaces:** `crt_run hs index args result` uses actual invocation reduction
and signed result decoding; `solve_execution_proved`, `period_execution_proved`,
`gcd_execution_proved`, `normalize_execution_proved`, `inverse_execution_proved`
inhabit their exact original `T_*_execution` propositions for these relations.

- [x] Add exact target checks and observe failure before endpoint definitions.
- [x] Extract actual call witnesses from the existing body/call certificates.
- [x] Combine operational uniqueness with mathematical API postconditions.
- [x] Compile exact endpoints with no retained operational hypotheses.

### Task 3: Proof gate, evidence, review, and PR update

**Files:** `scripts/check_wasm_proofs.py`, proof/status documentation,
`docs/evidence/implementation.json`.

- [x] Add all new modules and five exact target checks to the clean-source gate.
- [x] Run full proof compilation, transitive-assumption audit, negative control,
  and independent `coqchk`; run relevant regression checks.
- [x] Replace pending-target status with evidence only after checks pass.
- [x] Obtain fresh independent review; address substantive findings.
- [x] Commit, push to the existing PR branch, and update PR #1's description.
