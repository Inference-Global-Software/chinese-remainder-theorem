# Interactive CRT playground

A local browser interface to the verified finite-system Inference solver. Add or
remove up to 16 congruences, solve, reverse their order, or explore the examples.
Results show the canonical residue, period, complete solution family, exact sample
solutions, and remainder checks. Editing inputs clears the previous answer.

The proof explorer below the solver presents four properties: the canonical
answer and all solutions, overflow safety, order independence, and actual Wasm
execution. Select a property and switch between its statement, exact Rocq proof,
and Inference code. Expand the guided argument or the verification scope to see
the reasoning, recorded checks, and assumptions. Proof browsing preserves the
solver inputs and result; the tabs support arrow keys, Home, and End.

## Launch

Use Node 20+ and a modern browser with WebAssembly, BigInt, and Web Crypto.
From the repository root, build the native Inference project if needed:

```sh
cd systems
infs build
cd ..
node web/serve.mjs
```

Open **http://127.0.0.1:4173/**. Keep the terminal running; Ctrl+C stops it.
Choose another port with `node web/serve.mjs --port 4174`.
No package installation or external service is required. Inputs stay in the
browser; the local server only serves a fixed list of assets.

Both the server and browser check the Wasm SHA256 against
[`docs/evidence/finite-system.json`](../docs/evidence/finite-system.json) before
enabling computation. Use the recorded pinned compiler to reproduce that artifact;
an unrelated compiler build may differ and will deliberately fail this check.
If the artifact is missing, build `systems/` with `infs`. If it does not match,
restore/rebuild the recorded artifact; changing the expected hash alone does not
certify a different solver.

## Behavior and proof boundary

Decimal strings go directly to BigInt and signed-i64 memory cells. The browser
calls `crt_system_solve` and `crt_system_period`; it does not implement a second
CRT algorithm. The empty system is `(0,1)`. Invalid input, incompatibility, and
overflow are distinct outcomes, with incompatibility before overflow. A loading,
integrity, or execution failure is displayed separately from mathematical results.

The original compiled-Wasm proofs and evidence are unchanged. They cover the
solver under the documented memory premises; this UI, its JavaScript formatting,
the JavaScript engine, and compiler translation are not formally verified. The
browser constructs the complete two-array memory representation. Displayed sample
solutions use arbitrary-precision BigInt and may exceed i64: the returned
canonical residue and period fit i64, while their mathematical solution class is
unbounded. See the [proof inventory](../proofs/systems/README.md).

The recorded proof evidence includes hashes of documentation from its original
snapshot. The new demo and README launch link are subsequent documentation/UI
changes; they do not change the certified Inference source or Wasm bytes.

[`proof-data.json`](proof-data.json) contains curated excerpts with source paths,
line ranges, and source SHA256 hashes. The HTTP integration tests compare every
excerpt against its repository source and the evidence record's `bound_inputs`,
and compare the displayed audit counts and assumptions against that record.
Update excerpts and their provenance together when the checked sources change.
The explorer displays recorded proof results; it does not run Rocq in the browser.
A proof-data loading failure is reported independently of solver availability.

## Check the demo

With the compiled artifact available, run the dependency-free real-Wasm and HTTP
integration tests (these bind an ephemeral loopback port):

```sh
node --test tests/test_web.mjs
```

Optional browser tests use an existing `playwright-core` installation and Chrome.
Set `PLAYWRIGHT_MODULE` to that installation's absolute `index.mjs` path and
`CHROME_PATH` to the browser executable, then run:

```sh
node --test tests/web_browser.mjs
```

If `playwright-core` resolves normally from Node and its browser is installed,
those environment overrides can be omitted. Screenshots are saved under the
ignored `build/web-demo/` directory. The tests cover presets, invalidation after
editing, full-width values, capacity controls, clipboard output, artifact failure,
and mobile layout, plus proof selection, keyboard tabs, solver-state preservation,
source provenance, and proof-loading failure. Existing regression tests remain:

```sh
python3 -m unittest discover -s tests -v
```
