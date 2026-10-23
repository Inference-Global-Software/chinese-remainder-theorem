# Implementation and validation

The implementation is [`src/crt.inf`](../src/crt.inf). It preserves the agreed
domain, result conventions, recurrence, and 15 source contracts. Helpers are
private; only `crt_solve` and `crt_period` are exported.

## Build and run

```sh
make build INFC=/path/to/infc
node scripts/demo.mjs 2 6 5 9
node scripts/demo.mjs --json 2 6 4 9
```

The first example returns 14 and period 18. The second prints
`{"status":"incompatible","period":"18"}` and exits 1. Invalid arguments
exit 2; setup/runtime errors exit 3. The CLI validates decimal syntax and the
full signed-64-bit range before making a Wasm call, preventing silent integer
truncation. JSON integer values are decimal strings.

`scripts/build.py` accepts either an absolute compiler path or a compiler name
on `PATH`. The default is `INFC` or `infc` on `PATH`. Builds always use
`--mode proof`; the demo and runtime tests use that same `crt.wasm` artifact.
`build/crt/manifest.json` records its compiler, input, and output hashes.

## Runtime and regression tests

```sh
make test INFC=/path/to/infc
```

The suite currently contains 13 test methods, with table-driven subcases:

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
make proofs
# Or run everything:
make check INFC=/path/to/infc
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
make build INFC=/path/to/infc
docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real \
  opam exec -- make wasm-proofs
```

The checker verifies artifact hashes, copies and recompiles the mathematical,
generated, and companion sources in dependency order, checks the exact
`ValidModule` and both `ValidSpec` types, audits every companion lemma/theorem's
transitive assumptions, and runs independent `coqchk`. A negative control
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
The five original `T_*_execution` adapters remain separate: their universal
quantification over returned executions requires an additional operational
result-uniqueness argument. The checked `ValidSpec` certificates and concrete
finite execution proofs do not claim to discharge those adapters.

## Historical probes

`probes/` and `scripts/check_specifications.py` retain the earlier expressibility
experiment and its independently recorded hashes. They are not the implementation
entry point. That experiment also exposes the helper functions for direct
testing and uses the compiler's signature-only stub to check generated Rocq
syntax. The implementation test/proof commands above do not use that stub.
