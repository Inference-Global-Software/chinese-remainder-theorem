# Finite-system CRT

This native Inference project solves up to **16 congruences** with moduli from
1 through **9223372036854775807**. Its mathematical theorems cover arbitrary
finite lists. Moduli may share factors; active residues must be normalized.
The original pair project in the repository root remains separately buildable.

From the repository root, using the pinned `infs`/`infc` toolchain:

```sh
cd systems
infs build
cd ..
node systems/scripts/demo.mjs --json 2 6 5 9 8 15
```

The result is `{"status":"solved","solution":"68","period":"90"}`.
Every integer solution is `68 + 90*k`. The first two constraints have summary
`14 mod 18`; merging that summary with `8 mod 15` gives the same answer.
An empty invocation returns solution 0 and period 1.

## API and outcomes

The scalar exports take four signed i64 arguments `(a,m,b,n)`:

- `crt_merge_solve` returns the canonical residue or an error.
- `crt_merge_period` returns the positive period or the same error.

The batch exports `crt_system_solve` and `crt_system_period` take two read-only
`[i64;16]` arrays and a signed i32 count. Only the first `count` entries matter.
Both fields use this precedence:

| Result | Meaning |
| --- | --- |
| `-2` | Count outside 0..16, a nonpositive modulus, or an active residue outside 0..m-1. |
| `-1` | Valid entries with no common integer solution. |
| `-3` | A common solution exists, but its mathematical LCM exceeds signed i64 maximum. |
| nonnegative | Canonical solution; the corresponding period is positive. |

Overflow concerns the complete solution class, even when zero is a solution.
Validation and all pairwise compatibility checks finish before accumulation.
For example, this input has an overflowing prefix but returns incompatibility:

```sh
node systems/scripts/demo.mjs --json 0 3037000500 0 3037000501 1 2
```

The result is `{"status":"incompatible"}` with exit code 1. Every permutation
has the same classification. CLI exits are 0 for success, 1 for incompatibility,
2 for invalid input, and 3 for overflow or an execution/setup failure; the JSON
status distinguishes those last two outcomes.
Transport uses BigInt and decimal strings; the runner rejects out-of-range words.

Successful summaries can be reused without arrays:

```js
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync('systems/out/main.wasm'));
const api = instance.exports;
console.log(api.crt_merge_solve(14n, 18n, 8n, 15n));  // 68n
console.log(api.crt_merge_period(14n, 18n, 8n, 15n)); // 90n
```

Combining two successfully represented blocks can describe more than 16 original
constraints; the scalar merge itself takes four words. Comparing with one direct
batch invocation additionally requires that the combined list fit capacity 16.
An error code is not a summary and cannot reconstruct an overflowing block.

## Memory boundary and proof strength

At the raw Wasm ABI, the first two arguments are i32 byte pointers. Each must
represent a complete readable 128-byte array, fit the declared one-page memory,
and avoid 32-bit address wrap. The two regions may alias if their represented
contents agree where they overlap. All active and inactive i64 bit patterns are
covered; validation belongs to the implementation. The demo writes complete arrays at offsets 0 and 128. The test runner
additionally checks memory preservation.

The proofs establish existence of a terminating, nontrapping normal execution
and correctness of **every normal result**, with explicit input-memory premises.
They do not assert termination under every possible operational reduction
schedule. Exact emitted bounds guards, checked arithmetic, calls and finite
validation/pair/fold loops are included. Modular multiplication uses repeated
doubling to avoid forming an unrepresentable intermediate product.

The closed execution targets also transfer permutation (including errors),
summary extraction, composition, and concatenated-batch comparison to actual
Wasm invocations. Empty, singleton, duplicate, complete-solution-class and
inactive-tail properties follow from the execution refinement and finite model;
see the [proof inventory](../proofs/systems/README.md).

The pinned compiler cannot put aggregate arguments into source specification
applications. Batch contracts are therefore direct Rocq execution theorems.
The exact eight generated helper assertions and five scalar public assertions
are separately proved in the same runtime. Generated admitted certificates are
excluded from the trusted proof closure. The JavaScript runner and the compiler's
source-to-Wasm translation are not themselves verified by these theorems.

## Reproduce checks

Record native artifact provenance for both projects, then run host tests:

```sh
python3 scripts/build.py
python3 scripts/build.py --project-dir systems
python3 -m unittest discover -s tests -v
```

All Rocq work runs in the [pinned verifier container](../scripts/wasm_environment/README.md),
with this checkout mounted at `/workspaces/crt`:

```sh
sg docker -c 'docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real opam exec -- python3 scripts/check_system_proofs.py --out build/system-proofs'
```

The gate rebuilds a byte snapshot, checks 21 fixed target signatures, audits every
handwritten declaration against the unchanged upstream assumption allowlist,
rejects generated admission leakage, runs independent `coqchk`, and rejects
input or staged-file drift. The report binds source, manifests, artifacts, proof
sources, all checker dependencies, environment pins, and the allowlist.

[Recorded verification evidence](../docs/evidence/finite-system.json) includes
all bound input hashes, exact target names, fresh legacy checks, host tests and
negative controls. Local reproduction emits full reports and logs under `build/`.
