# Finite-system compiled execution proofs

This directory proves the scalar and bounded batch exports of the separate
`systems/` project. The full gate certifies actual execution of both merge exports
and both batch exports, together with their operational dependencies.

- `ReadOnly` defines a recursive allowed instruction predicate and native-function
  store invariant. Every real reduction, including a native call or scalar load,
  preserves the host, the entire store, and this code invariant. The transitive
  theorem retains the invariant at intermediate configurations.
- `ReadOnlyDeterminism`, `ReadOnlyFlatJoin`, and `ReadOnlyConfluence` reuse the
  unchanged generic legacy context proofs and prove uniqueness of normal values
  for this read-only subset. They do not assume a resource-free store.
- `SystemRuntime` proves validity, allocation and instantiation of the exact
  generated system module. `system_initial_runtime` contains freshly allocated
  zero memory. `system_store mem` instead describes subsequent host-prepared
  memory. `system_run` contains only actual Wasm reduction and signed decoding;
  it has no mathematical CRT postcondition or memory-validity assumption.
- `SystemMemory` supplies the additional input premises: a one-page memory with
  the declared fixed limits, two complete 128-byte i64 regions, and no 32-bit
  pointer wrap. Regions may alias whenever both contents are represented.
  `system_inputs_inhabited` constructs memory for arbitrary 16-element input
  lists at the runner's offsets 0 and 128 using the abstract memory write laws.
- `SystemArrayExecution` extracts a contiguous eight-instruction slice from the
  actual classifier's first validation loop. Its exact shape is checked. Given
  the pointer/index operand prefix and the index in scratch local 7, the slice
  executes the generated unsigned bounds guard, address calculation and i64
  load. There is a normal execution returning the represented element, and
  every normal execution returns that element.

The existence/uniqueness results make no claim that every possible reduction
schedule terminates. The closed scalar and batch targets supply the mathematical preconditions
and explicit input-memory premises.

## Reproduce

Build the native project's current artifacts using the pinned compiler:

```sh
python3 scripts/build.py --project-dir systems
```

Run all Rocq work inside the existing pinned verifier container (with this
checkout mounted at `/workspaces/crt`):

```sh
sg docker -c 'docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real opam exec -- python3 scripts/check_system_infrastructure.py'
```

The checker stages fresh copies of these sources, the exact generated module,
and the minimal unchanged legacy context dependency closure. It checks source
and artifact freshness, rejects proof holes, compiles eight closed exact target
wrappers, audits every handwritten theorem and definition against the existing
upstream allowlist, rejects a deliberate dependency on a generated admitted
certificate, and runs independent `coqchk`. Evidence and logs are written to
`build/system-infrastructure/`; the report explicitly marks public CRT execution
correctness as uncertified. No ignored prototype or precompiled project object
is required.

## Scalar execution and source contracts

`FullWidthExecution`, `FullWidthInversePrefix`, and `FullWidthInverseExecution`
connect the unchanged helper algorithms to the full signed-i64 bounds and the
new module runtime. `AddModExecution` and `MulModExecution` prove the exact
emitted overflow-safe arithmetic. The multiplication proof follows all loop
instructions, including the final factor doubling, and uses the fixed 64-step
mathematical state recurrence to justify each backedge.

`SystemCalls` and `SystemControl` compose native calls and structured control
at `system_store mem`. Read-only preservation restores that same store before
continuations. `MergeValidation`, `MergeSolvePure`, `MergeSolveExecution`, and
`MergePeriodExecution` cover all signed-i64 inputs and all four outcomes:
invalid (-2), incompatible (-1), overflow (-3), or success. Their results refine
`FiniteSystem.merge`, whose classification is already proved in `CRTFinite`.

`ScalarExecutionTargets` quantifies over arbitrary prepared memory and proves
existence of a normal execution and correctness of every normal result for all
seven scalar functions. It does not assert termination of every reduction
schedule. No precondition excludes invalid public scalar inputs.

`SystemSpecModel`, `SystemSpecPayloads`, `SystemSpecRealization`, and
`SystemSpecCertificates` connect the exact eight emitted helper assertions and
five public assertions to one interpretation realized in
`system_initial_runtime`. The shared-runtime theorem exposes both sets of
payloads together; the two `ValidSpec` certificates use that actual initial
runtime. Prepared memory is never presented as an independently instantiated
`module_runtime`.

Run the scalar proof gate in the pinned container:

```sh
sg docker -c 'docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real opam exec -- python3 scripts/check_system_scalars.py'
```

The gate rebuilds the mathematical, unchanged legacy, generated, and new scalar
source closure in a clean staging directory. It checks closed fixed signatures,
audits handwritten declarations transitively against the existing assumption
allowlist, rejects generated admitted certificates, and kernel-checks the
results independently. Its report binds source and artifact hashes for both
projects, verifier environment pins, checker dependencies, and staged bytes,
and rejects input or staging drift before writing success. The report does not
claim batch execution correctness. Host-safe failure controls live in
`tests/test_system_scalar_gate.py`; they mock every compiler subprocess.

## Complete batch execution and algebra

`ArrayAccess`, `BatchArithmetic`, `BatchCount`, `BatchValidation`, and `BatchPair`
prove the emitted per-access, checked increment, count, validity and pair tests.
`BatchValidateLoop`, `BatchPairRow`, and `BatchPairLoop` prove the exact finite
validation and lexicographic pair scans. `BatchClassModel` identifies their
cursor recurrences with the unbounded finite-list model; `BatchClassExecution`
closes the complete classifier body and native call for every signed-i32 count.
`BatchPeriodFold` and `BatchSolveFold` prove the emitted accumulation loops.
`BatchPublicPrefix`, `BatchPeriodExecution`, and `BatchSolveExecution` connect
classification and accumulation to both exact public function bodies.

`BatchExecutionTargets` supplies seven closed final targets:

- `batch_export_bindings`: exact public module and instantiated export names/indices.
- `system_batch_solve_execution` and `system_batch_period_execution`: normal
  execution exists and every normal result equals the precisely classified model.
- `system_batch_permutation`: both actual returned fields agree for permuted
  active input, including all error classifications.
- `system_batch_success_summary`: actual successful outputs represent the whole
  active system, with valid count and representable period.
- `system_batch_composition`: actual scalar merge executions of two successful
  batch summaries have the complete concatenated-system result and postcondition.
- `system_batch_concat`: those actual scalar results agree with a direct batch
  invocation of a permutation of the concatenation, subject to count 0..16.

The algebra helper `be_refines` is discharged by the compiled execution targets;
it is not a premise of these closed algebra targets. Incompatible and overflowing
unions of successful blocks remain covered. Bare error codes cannot be composed
as summaries. Finite-model singleton/duplicate laws and successful associativity
and commutativity transfer through these execution refinements; they are not
additional separately named closed batch targets. Inactive-tail independence
follows because the model uses exactly the active prefix. Empty output is `(0,1)`.

Public batch targets quantify arbitrary signed counts and i64 array contents,
with `system_input_memory` and `batch_word32` premises. For count outside 0..16
the result is invalid regardless of contents; the finite-list `result_post` is
therefore required only when the count is in range. This avoids falsely treating
an invalid raw count as a mathematical invalidity of the empty list.

The full gate is `python3 scripts/check_system_proofs.py --out build/system-proofs`
inside the pinned container. It includes the 14 scalar exact targets plus the
seven closed batch targets, rebuilds every dependency from a snapshot, audits
all declarations (not just endpoint names), rejects generated admission leakage,
and runs `coqchk`. `system_proof_engine.py` shares the audit engine with the scalar
entry point; each entry point fixes its own target set and report metadata.
The infrastructure-only and scalar-only reports intentionally remain narrower.

The [committed evidence record](../../docs/evidence/finite-system.json) binds the
accepted full-system snapshot and the independently rerun mathematical/legacy
gates. Full generated audit outputs are reproducible in the listed build paths.
