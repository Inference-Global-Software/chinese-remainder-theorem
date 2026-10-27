# Finite-system operational infrastructure

This directory provides infrastructure for the separate `systems/` project.
It does **not yet certify the four public CRT exports**.

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
schedule terminates. Later scalar/batch correctness targets must supply the
mathematical preconditions and explicit input-memory premises.

## Reproduce

Build the native project's current artifacts using the pinned compiler:

```sh
python3 scripts/build.py --project-dir systems
```

Run all Rocq work inside the existing pinned verifier container (with this
checkout mounted at `/workspaces/crt`):

```sh
sg docker -c 'docker exec -u coq -w /workspaces/crt crt-finite-system-verifier opam exec -- python3 scripts/check_system_infrastructure.py'
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
