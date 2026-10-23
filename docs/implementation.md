# Implementation and validation

The implementation is [`src/main.inf`](../src/main.inf), the entry file of the
native project defined by [`Inference.toml`](../Inference.toml). It preserves the agreed
domain, result conventions, recurrence, and 15 source contracts. Helpers are
private; only `crt_solve` and `crt_period` are exported.

## Build and run

```sh
infs build
node scripts/demo.mjs 2 6 5 9
node scripts/demo.mjs --json 2 6 4 9
```

The first example returns 14 and period 18. The second prints
`{"status":"incompatible","period":"18"}` and exits 1. Invalid arguments
exit 2; setup/runtime errors exit 3. The CLI validates decimal syntax and the
full signed-64-bit range before making a Wasm call, preventing silent integer
truncation. JSON integer values are decimal strings.

The manifest selects `[build] mode = "proof"` and
`[verification] output-dir = "out"`. `infs build` discovers the project and
emits `out/main.wasm` and `out/main.v`. The demo and runtime tests execute that
same Wasm artifact. Use `INFC_PATH=/absolute/path/to/infc` to select the compiler;
the recorded compiler revision is documented in the [walkthrough](walkthrough.md).

For proof auditing, `python3 scripts/build.py` runs the same native project build
and additionally records `out/manifest.json`. It records the compiler selected
by `infs`, both toolchain binary hashes, the project manifest, source, and output
hashes. It respects `INFC_PATH` and accepts `--infs` or `INFS` for a toolchain
outside `PATH`. A plain `infs build` is sufficient to run the demo.

This project exports a library API. The Node runner invokes its two exports;
project-mode `infs run` expects a function named `main`, which this library does
not export.

## Runtime and regression tests

```sh
python3 -m unittest discover -s tests -v
```

The suite currently contains 14 test methods, with table-driven subcases:

- Native `infs build` project discovery followed by the scheduling demo.

- 23,274 public API vectors, including exhaustive normalized residue combinations
  for moduli 1–16, deterministic large inputs, and full-width invalid inputs.
  Small inputs use brute-force enumeration. Large inputs use Python unbounded
  integers, `math.gcd`/`math.lcm`, and the builtin modular inverse as the oracle.
- Concrete CLI cases for noncoprime/equal/dividing moduli, modulus one, negative
  differences, incompatibility, invalid domain, and missing arguments.
- Exact transport of solution `4611686011984936961` and period
  `4611686011984936962`, both beyond JavaScript's exact `Number` range.
- Rejection before Wasm conversion of `2^64+1`, both out-of-range signed bounds,
  decimal fractions, exponent syntax, and non-integer text.
- Three independently compiled faulty Wasm variants, with concrete failures:
  missing compatibility check `(2,6,4,9)`; missing negative-remainder
  normalization `(5,9,2,6)`; noncanonical output `(2,3,3,5)`.
- Proof-gate rejection of an injected axiom and an admitted theorem.
- Wasm audit rejection of dependencies on the compiler's admitted placeholders,
  and of incomplete or unparseable assumption output.

Runtime tests provide finite execution evidence. They do not replace the
quantified proof obligations.

## Mathematical proofs

```sh
python3 scripts/check_proofs.py
```

The 16 exact mathematical/loop targets and four additional finite-run results
are proved. All 29 lemma/theorem declarations in `CRTMath.v` and `CRTLoops.v`
pass assumption auditing and independent `coqchk`. The original statement
definitions are unchanged. See [proof coverage](../proofs/README.md).

The recorded baseline uses Inference 0.0.6 (`95db5e4`, ABI 1.10), Coq 8.20.1,
and Node v26.10.0. The mathematical proof command checks the abstract targets;
the generated behavioral obligations have their own container check below.

## Generated-Wasm proofs

Build the [pinned environment](../scripts/wasm_environment/README.md) and start
its container with this checkout mounted at `/workspaces/crt`. Build the program
on the host first, then run:

```sh
python3 scripts/build.py
docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real \
  opam exec -- python3 scripts/check_wasm_proofs.py
```

The checker verifies artifact hashes, copies and recompiles the mathematical,
generated, and companion sources in dependency order, checks the exact
`ValidModule`, both `ValidSpec` types, and all five original execution target
types, audits every companion lemma/theorem's transitive assumptions, and runs
independent `coqchk`. A negative control
deliberately compiles a theorem using the generated admitted skeleton and
requires the assumption audit to reject it. No generated placeholder is used
by the completed certificate.

`build/wasm-proofs/report.json` records the proof-source hashes, compiler/artifact
manifest, verifier source-tree hash, and actual upstream assumptions. The
committed [evidence snapshot](evidence/implementation.json) records this run,
including a separate fingerprint of its compiled verifier objects. The checker
currently records verifier source hashes automatically; automatically recording
compiled-object hashes for future or custom environments remains a reproduction
improvement. A source hash alone does not identify stale compiled dependencies.

The [clean reproduction record](evidence/clean-reproduction.json) identifies the
fresh image built with `CRT_DOCKER_NO_CACHE=1`, its recipe hashes, all 78 locked
package versions checked, and the upstream audit results: 85 sources without
proof holes and 135 declarations using only the 10 allowlisted dependencies.
Both CRT proof gates were then run in a new container with separate, new output
directories under `build/reproduction/`. The record includes the exact commands
and local log hashes. This validates the packaged recipe starting from its
pinned Coq base image; the Inference compiler was the existing pinned binary.

All five original `T_*_execution` targets are now instantiated with actual
WasmCert invocation and signed i64 decoding. A proved operational confluence
argument ensures uniqueness of normal results; the endpoints combine it with
the existing finite execution witnesses. The checker closes each exact target
without any retained uniqueness premise and audits all supporting modules.
The execution targets assert existence of a terminating execution and
correctness of every normal return, as defined in the original specification.

## Historical probes

`probes/` and `scripts/check_specifications.py` retain the earlier expressibility
experiment and its independently recorded hashes. They are not the implementation
entry point. That experiment also exposes the helper functions for direct
testing and uses the compiler's signature-only stub to check generated Rocq
syntax. The implementation test/proof commands above do not use that stub.
