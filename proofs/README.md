# Proof coverage

## Completed mathematical proofs

The existing targets in [`CRTStatements.v`](../specifications/CRTStatements.v)
are unchanged. The following exact propositions now have proofs ending in `Qed`:

| File | Exact targets |
| --- | --- |
| [CRTMath.v](CRTMath.v) | `T_normalization`, `T_reduction`, `T_generalized_CRT`, `T_canonical_unique`, `T_all_solutions`, `T_incompatible`, `T_construct`, `T_crt_bounds` |
| [CRTLoops.v](CRTLoops.v) | `T_normalize`, `T_gcd_init`, `T_gcd_step`, `T_gcd_exit`, `T_eea_init`, `T_eea_step`, `T_eea_step_bounds`, `T_eea_exit` |

`CRTLoops.v` also defines finite mathematical Euclid/extended-Euclid runs and
proves `gcd_run_terminates`, `gcd_initial_run_correct`, `eea_run_terminates`, and
`eea_initial_run_correct`. The variant is the natural-number interpretation of
the second remainder. Invariants and coefficient bounds apply on the final
iteration as well as intermediate ones.

The proof gate checks all 29 lemma/theorem declarations in these two files.
Every assumption audit reports **Closed under the global context**. `coqchk`
independently checks their compiled proof terms. The gate rejects admissions,
new axioms, and unchecked proof tactics; regression tests inject an axiom and an
admitted theorem and require rejection.

```sh
make proofs
```

This command uses only the standard Coq integer library, copies inputs to
`build/proofs`, and emits source hashes, exact endpoint names, and a report.
It also checks that each endpoint inhabits its original `T_*` target, rather
than trusting a theorem name alone.

## Exact generated module and contracts

[`wasm/CRTRealization.v`](wasm/CRTRealization.v) proves:

- `checked_model_realized`: each application in the mathematical interpretation
  is backed by execution of its actual emitted Wasm body in `crt_runtime`.
- `checked_helper_contracts`: `ValidSpec crt.crt crt.crt__HelperContracts_specs`.
- `checked_public_contracts`: `ValidSpec crt.crt crt.crt__PublicContracts_specs`.
- `checked_crt_certificate`: the independently proved `ValidModule` together
  with both exact `ValidSpec` propositions.

These cover all six helper and nine public source contracts, including the
nested existence/uniqueness assertion. The public execution witnesses cover
**all i64 inputs**, so validation and realization cannot be made vacuous by
excluding invalid inputs from the interpretation. Helper execution witnesses
cover their stated preconditions.

The proof follows the actual generated instructions, including validation,
branches, checked arithmetic, Euclid and extended-Euclid loops, native calls,
and returns. Loop runs have decreasing natural-number variants; arithmetic
bounds justify the generated overflow checks. All calls share an instantiated,
structurally valid module/runtime.

| Proof files | Role |
| --- | --- |
| `CRTModule`, `CRTStorePure` | Independent module typing, allocation, initialization, resource-free store |
| `CRTExecution`, `CRTLoopRules` | Gcd/normalization execution and loop rules |
| `CRTCheckedArithmetic`, `CRTGeneralArithmetic` | Actual compiler-emitted arithmetic checks |
| `CRTCalls`, `CRTInverseExecution` | Native-call composition and complete modular-inverse execution |
| `CRTPublicExecution`, `CRTSolveExecution` | Full period and solver execution witnesses |
| `CRTAPIModel`, `CRTContracts` | Mathematical API model and interpretation |
| `CRTSpecPayloads`, `CRTRealization` | Exact generated assertion payloads and final certificates |

Run the checker inside the [real verifier container](../scripts/wasm_environment/README.md):

```sh
make wasm-proofs
```

It recompiles isolated source copies, checks the exact certificate types,
audits every companion theorem/lemma, and independently runs `coqchk`.
It rejects unapproved transitive assumptions and proves the rejection works
with a real compiled negative control. The raw generated `crt.v` contains three
`Admitted` skeletons; the completed proofs import its definitions but **do not
depend on those skeletons**. Report hashes identify the checked source snapshot
and the runtime-tested Wasm artifact.

## Precise scope and trust boundary

The mathematical CRT theorem covers unbounded integers; the executable uses the
specified bounded moduli and i64 arithmetic. Source quantifiers have their
machine-type domains. `ValidSpec` is the real WasmVerifier proposition: the
assertion payloads hold under an interpretation realized by actual finite Wasm
executions. It is not a substitute for every possible total-correctness notion.

The five original `T_*_execution` targets in `CRTStatements.v` additionally
quantify over **every normally returned result** of a supplied execution
relation. They remain uninstantiated. Connecting the concrete execution
witnesses to those targets needs an operational result-uniqueness argument;
this project does not claim that argument from witness existence alone.
The 16 exact mathematical/loop targets are all discharged without changing
their statements.

The generated-Wasm proofs use nine audited upstream assumptions: classical
logic, functional extensionality, two classical-real decision principles,
and five abstract SIMD operations inherited through the verifier. The CRT
program uses no SIMD instructions. The exact names are in the evidence report;
[`assumptions.allow`](wasm/assumptions.allow) is the reviewed upstream allowlist.
There are no project axioms, admissions, or unchecked proof tactics in completed
proof sources.

The trusted boundary includes Rocq's kernel and libraries, WasmCert/WasmVerifier
semantics and their listed assumptions, and the compiler's translation from
Inference into the matching Wasm and Rocq module representations. Hashes bind
the checked representations and tested binary; they do not prove the compiler
correct or verify the Node WebAssembly engine. The compiler's signature stub
is not used by these proofs.

See [implementation evidence and commands](../docs/implementation.md) for
reproduction. The original [feasibility report](../docs/specification-check.md)
is historical and records the earlier signature-only check separately.
