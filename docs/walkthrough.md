# From periodic schedules to proved WebAssembly: CRT in Inference

One process runs at times `2, 8, 14, 20, ...`. Another runs at
`5, 14, 23, 32, ...`. When do they coincide?

The first coincidence is **14**, and subsequent coincidences are **18** time
units apart. This repository computes that answer in Inference, compiles it to
WebAssembly, and proves properties of the mathematics and the emitted program.
It also handles schedules that never coincide.

The example demonstrates mutable loops, checked integer arithmetic, helper
contracts, and an existence-and-uniqueness specification in Inference. The
compiler emits Rocq proof obligations; the repository supplies the proofs that
discharge them. Compiling in proof mode alone does not complete those proofs.

## Run the example

You need Git, Node with WebAssembly and BigInt support, and the `infs` Inference
toolchain. Tests and proof auditing also use Python 3.9+. The recorded compiler is
**0.0.6**, revision
[`95db5e4170fdfd5080afdcb938c7704a790a7b24`](https://github.com/Inferara/inference/tree/95db5e4170fdfd5080afdcb938c7704a790a7b24),
ABI **1.10**. The recorded runtime is Node **v26.10.0**.

To build `infs` and its matching compiler, the source requires Rust 1.91 or newer:

```sh
git clone https://github.com/Inferara/inference.git inference-compiler
cd inference-compiler
git checkout 95db5e4170fdfd5080afdcb938c7704a790a7b24
cargo build --release -p infs -p inference-cli
export PATH="$(pwd)/target/release:$PATH"
export INFC_PATH="$(pwd)/target/release/infc"
cd ..
```

With an installed `infs` on `PATH`, it resolves its compiler automatically.
To select a particular compiler for reproducing the evidence, use its native
override:

```sh
export INFC_PATH=/absolute/path/to/infc
```

From the directory where you keep your checkouts:

```sh
git clone https://github.com/Inference-Global-Software/chinese-remainder-theorem.git
cd chinese-remainder-theorem
infs build
node scripts/demo.mjs 2 6 5 9
```

After the build messages, the demo prints:

```text
First coincidence: 14
Repeat period: 18
All integer solutions: 14 + 18 * k
```

The checkout is a native Inference project:

```text
Inference.toml       project metadata and build settings
src/main.inf        algorithm and 15 source specifications
out/main.wasm       generated executable
out/main.v          generated Rocq definitions and proof obligations
proofs/             completed mathematical and execution proofs
scripts/demo.mjs    command-line host for the exported functions
```

[`Inference.toml`](../Inference.toml) selects proof mode and keeps generated
files separate from the completed proofs:

```toml
[package]
name = "chinese-remainder-theorem"
version = "0.1.0"
infc_version = "0.0.6"
description = "Generalized Chinese Remainder Theorem with proved WebAssembly contracts"

[build]
target = "wasm32"
mode = "proof"

[verification]
output-dir = "out"
```

`infc_version` records the compiler version in the project metadata. To
reproduce the exact compiler revision, use the pinned checkout and
`INFC_PATH` above.

`infs build` discovers the manifest and compiles
[`src/main.inf`](../src/main.inf). The Node runner executes `out/main.wasm`
through its exported CRT functions. This is a library project: project-mode
`infs run` expects a function named `main`, while this example exports
`crt_solve` and `crt_period`.

Pass your own inputs in the order **`a m b n`**, meaning
`x mod m = a` and `x mod n = b`:

```sh
node scripts/demo.mjs 5 9 2 6
```

This swaps the schedules and produces the same output. It also exercises a
negative `b - a`, an important case for signed remainder arithmetic.

Changing the second offset from 5 to 4 makes the schedules incompatible:

```sh
node scripts/demo.mjs --json 2 6 4 9
```

```json
{"status":"incompatible","period":"18"}
```

That command intentionally exits with status **1**. Successful calls exit **0**;
invalid inputs exit **2**; setup or execution errors exit **3**. For example,
`node scripts/demo.mjs --json 6 6 4 9` is invalid because residue 6 is outside
`0 <= a < 6`.

## The theorem behind the result

For arbitrary integers `a`, `b` and positive integers `m`, `n`, define
`g = gcd(m, n)` and `L = lcm(m, n) = (m / g) * n`. The generalized Chinese
Remainder Theorem says:

> There exists an integer `x` satisfying `x ≡ a (mod m)` and
> `x ≡ b (mod n)` if and only if `g` divides `b - a`. When it exists,
> exactly one solution lies in `0 <= x < L`. Every integer solution is
> `x + k * L` for an integer `k`, using that canonical solution `x`.

Congruence means that the modulus divides the difference. The theorem covers
unbounded mathematical integers. For schedules, retain the nonnegative times.

Here `gcd(6, 9) = 3`. The difference `5 - 2 = 3` is divisible by 3, so a
solution exists. The difference `4 - 2 = 2` is not, so the changed schedules
never coincide. Handling moduli with a common factor is what makes this the
*generalized* CRT.

For the implementation's construction, now assume compatible inputs and
normalized residues `0 <= a < m` and `0 <= b < n`. Write `x = a + m * t`.
Substitution into the second congruence and division by `g` give:

```text
m1 = m / g
n1 = n / g
m1 * t ≡ (b - a) / g  (mod n1)
```

The reduced moduli are coprime. If `n1 > 1`, compute an inverse `u` of `m1`
modulo `n1`, then take:

```text
t = (((b - a) / g) * u) mod n1, with 0 <= t < n1
x = a + m * t
```

For the running example, `m1 = 2`, `n1 = 3`, `u = 2`, and `t = 2`, giving
`x = 2 + 6 * 2 = 14`. If `n1 = 1`, compatibility already makes `a` the
canonical solution; no inverse is needed.

## The Inference implementation

The executable accepts **`1 <= m,n <= 2147483647`**, normalized residues
**`0 <= a < m`**, **`0 <= b < n`**, and uses signed `i64` arithmetic. Only
`crt_solve` and `crt_period` are exported. These are their actual definitions:

```inference
pub fn crt_period(m: i64, n: i64) -> i64 {
    if m < 1 || m > 2147483647 || n < 1 || n > 2147483647 {
        return -2;
    }
    let g: i64 = gcd_positive(m, n);
    return (m / g) * n;
}

pub fn crt_solve(a: i64, m: i64, b: i64, n: i64) -> i64 {
    if m < 1 || m > 2147483647 || n < 1 || n > 2147483647 {
        return -2;
    }
    if a < 0 || a >= m || b < 0 || b >= n { return -2; }
    let g: i64 = gcd_positive(m, n);
    let delta: i64 = b - a;
    if delta % g != 0 { return -1; }
    let m1: i64 = m / g;
    let n1: i64 = n / g;
    if n1 == 1 { return a; }
    let B: i64 = m1 % n1;
    let u: i64 = inverse_coprime(B, n1);
    let t: i64 = normalize((delta / g) * u, n1);
    return a + m * t;
}
```

The solver distinguishes three outcomes:

| Result | Meaning |
| --- | --- |
| `-2` | At least one input violates the API domain. |
| `-1` | Inputs are valid, but no mathematical solution exists. |
| `x >= 0` | The unique solution in `0 <= x < lcm(m, n)`. |

`crt_period` returns `-2` for invalid moduli and their lcm otherwise. It does
not take residues: even incompatible schedules have an lcm of their periods.

Euclid's algorithm supplies the gcd:

```inference
fn gcd_positive(m: i64, n: i64) -> i64 {
    let mut r0: i64 = m;
    let mut r1: i64 = n;
    loop r1 > 0 {
        let r2: i64 = r0 % r1;
        r0 = r1;
        r1 = r2;
    }
    return r0;
}
```

Extended Euclid carries two coefficient pairs alongside those remainders.
Its precondition is `1 <= B < A <= 2147483647` and `gcd(A, B) = 1`:

```inference
fn inverse_coprime(B: i64, A: i64) -> i64 {
    let mut r0: i64 = A;
    let mut r1: i64 = B;
    let mut s0: i64 = 1;
    let mut s1: i64 = 0;
    let mut t0: i64 = 0;
    let mut t1: i64 = 1;
    loop r1 > 0 {
        let q: i64 = r0 / r1;
        let r2: i64 = r0 % r1;
        let s2: i64 = s0 - q * s1;
        let t2: i64 = t0 - q * t1;
        r0 = r1;
        r1 = r2;
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }
    return normalize(t0, A);
}
```

At exit, `A * s0 + B * t0 = 1`. Thus `t0` is an inverse of `B` modulo `A`.
The last helper turns a signed remainder into its nonnegative representative:

```inference
fn normalize(z: i64, d: i64) -> i64 {
    let r: i64 = z % d;
    if r < 0 { return r + d; }
    return r;
}
```

For example, signed `-2 % 3` is `-2`; normalization produces `1`. This is
needed both for negative inverse coefficients and for negative `b - a`.

## Expressing the claim in Inference

The source also contains six helper specifications and nine public
specifications. Here is the existence-and-uniqueness specification, copied
from inside `spec PublicContracts`:

```inference
    fn compatible_exists_unique(a: i64, m: i64, b: i64, n: i64) forall {
        assume { assert(1 <= m && m <= 2147483647 && 1 <= n && n <= 2147483647); }
        assume { assert(0 <= a && a < m && 0 <= b && b < n); }
        assume { assert((b - a) % gcd_positive(m, n) == 0); }
        exists {
            let x: i64 = @;
            // Assertions constrain the witness; assume would change the logic.
            assert(0 <= x && x < crt_period(m, n));
            assert(x % m == a && x % n == b);
            assert(x == crt_solve(a, m, b, n));
            forall {
                let y: i64 = @;
                assume { assert(0 <= y && y < crt_period(m, n)); }
                if y % m == a && y % n == b { assert(y == x); }
            }
        }
    }
```

Read this from outside in: **for every valid compatible input**, there
**exists** a canonical solution equal to the solver's result, and **every**
canonical candidate satisfying both congruences equals that solution.

`@` introduces a choice governed by the enclosing quantifier. These choices
express logical quantification over `i64` values; they are not random test
samples. `assume { assert(...) }` restricts a quantifier's domain. The assertions
inside `exists` require the witness to have the desired properties.

All 15 source specifications are covered by the two exact generated
`ValidSpec` proofs:

| Source specification(s) | Obligation |
| --- | --- |
| `gcd_total`, `normalize_total`, `inverse_total` | A terminating, nontrapping execution exists under each helper's preconditions. |
| `gcd_characterization` | The result is positive, divides both inputs, and is divisible by every positive common divisor in the specified range. |
| `normalize_correct` | The result is in `[0,d)` and equals the signed remainder corrected when negative. |
| `inverse_correct` | The result is in `[0,A)` and multiplying it by `B` gives remainder 1 modulo `A`. |
| `solve_total`, `period_total` | A terminating, nontrapping execution exists for every combination of `i64` arguments, including invalid inputs. |
| `solve_validation` | Invalid inputs return `-2`; valid inputs return at least `-1`. |
| `period_contract` | Invalid moduli return `-2`; valid ones return `(m/gcd(m,n))*n`, in `[1,2147483647²]`. |
| `solve_compatibility` | Valid compatible inputs return a nonnegative result; valid incompatible inputs return `-1`. |
| `solve_soundness` | A successful result satisfies both congruences and is less than the period. |
| `canonical_uniqueness` | Every canonical candidate satisfying both congruences equals the solver's result. |
| `incompatible_has_no_canonical_witness` | If the solver returns `-1` on valid inputs, every canonical candidate fails at least one congruence. |
| `compatible_exists_unique` | The nested `forall / exists / forall` claim shown above. |

Helper preconditions matter: gcd requires bounded positive inputs;
normalization accepts any `i64` numerator and `1 <= d <= 2147483647`;
inverse requires the coprime inputs stated above. The two public functions
validate inputs before calling helpers.

## Exactly what the proofs establish

### Mathematical CRT and construction

The exact proposition definitions are in
[`CRTStatements.v`](../specifications/CRTStatements.v); their proofs are in
[`CRTMath.v`](../proofs/CRTMath.v).

| Target | Proved statement |
| --- | --- |
| `T_normalization` | For positive moduli, replacing arbitrary integer residues with their nonnegative modular representatives preserves the solution set. |
| `T_reduction` | The gcd is positive and divides both moduli; dividing by it gives positive coprime moduli; `(m/g)*n` is their original lcm and is positive. |
| `T_generalized_CRT` | For positive moduli and arbitrary integer residues, a solution exists exactly when `gcd(m,n)` divides `b-a`. |
| `T_canonical_unique` | Under those conditions and compatibility, exactly one solution lies in `[0,L)`. |
| `T_all_solutions` | Given any integer solution `x`, an integer `y` is a solution exactly when `y = x + k*L` for some integer `k`. |
| `T_incompatible` | For positive moduli, incompatibility excludes every integer solution. |
| `T_construct` | On valid compatible API inputs, `a` is canonical when `n/g = 1`; otherwise the inverse-based construction above is canonical. |
| `T_crt_bounds` | On that API domain, the reduced inputs, difference, period, construction product, and final result satisfy their stated bounds and fit signed `i64`. |

The first six targets use unbounded integers. The last two deliberately use
the executable's bounded domain. In particular, with `M = 2147483647`:

```text
1 <= L <= M² = 4611686014132420609 < 2^63
abs(((b - a) / g) * u) <= (M - 1)²
0 <= m * t <= M * (M - 1)
0 <= a + m * t < L
```

The API requires normalized residues; `T_normalization` does not mean that
`crt_solve` silently normalizes invalid arguments.

### Loop invariants and arithmetic safety

[`CRTLoops.v`](../proofs/CRTLoops.v) proves eight more exact targets.
`T_normalize` proves the correction from signed remainder to Euclidean modulo,
including its range and machine bounds.

`T_gcd_init`, `T_gcd_step`, and `T_gcd_exit` establish initialization,
preservation, and the exit result for:

```text
1 <= r0 <= M
0 <= r1 <= M
gcd(r0, r1) = gcd(m, n)
```

`T_eea_init`, `T_eea_step`, and `T_eea_exit` do the same for extended Euclid.
Its invariant includes the two Bézout identities and coefficient bounds:

```text
0 <= r1 < r0 <= A
gcd(r0, r1) = gcd(A, B)
r0 = A*s0 + B*t0
r1 = A*s1 + B*t1
abs(s0), abs(s1) <= B
abs(t0), abs(t1) <= A
```

The complete invariant also retains determinant, sign, and weighted absolute
value identities; see [`eea_inv`](../specifications/CRTStatements.v).
These support `T_eea_step_bounds`: each coefficient multiplication and update
fits `i64`, including on the final iteration.

Both loops strictly decrease the nonnegative second remainder on each
iteration. The additional results `gcd_run_terminates`,
`gcd_initial_run_correct`, `eea_run_terminates`, and
`eea_initial_run_correct` establish finite mathematical runs and their results.
These invariants and proofs live in Rocq; they are not extra Inference loop
annotation syntax.

### Actual WebAssembly execution

The [execution endpoints](../proofs/wasm/CRTExecutionTargets.v) instantiate
the five original targets with calls to the actual emitted bodies in the
proved CRT runtime:

| Endpoint → target | Domain and result |
| --- | --- |
| `gcd_execution_proved` → `T_gcd_execution` | Bounded positive inputs; returns their mathematical gcd. |
| `normalize_execution_proved` → `T_normalize_execution` | Any signed `i64` numerator and bounded positive divisor; returns Euclidean modulo. |
| `inverse_execution_proved` → `T_inverse_execution` | `1 <= B < A <= M`, coprime; returns `0 <= u < A` with `B*u ≡ 1 (mod A)`. |
| `period_execution_proved` → `T_period_execution` | Every pair of `i64` inputs; returns `-2` for invalid moduli, otherwise their lcm. |
| `solve_execution_proved` → `T_solve_execution` | Every four `i64` inputs; returns exactly the invalid, incompatible, or canonical-solution outcome described above. |

For each target, the exact meaning of `total_correct` is:

1. There exists a finite execution returning a result.
2. Every normally returned result fits `i64` and satisfies the postcondition.

**This does not assert that every possible reduction sequence terminates.**
The relation being proved describes actual WasmCert reductions and signed
decoding of the return value. It contains no assumed answer or embedded
mathematical postcondition. An operational confluence proof establishes
uniqueness of normal results and connects the finite execution witnesses to
the second clause.

Separately, [`CRTRealization.v`](../proofs/wasm/CRTRealization.v) discharges
the generated module's `ValidModule` and both exact `ValidSpec` obligations.
The interpretation used for those source contracts is realized by finite
executions of the emitted functions. Together, these proofs connect the
source specifications, mathematical construction, and concrete function bodies.

## Reproduce the checks

Run the runtime suite with the same compiler used for the demo:

```sh
python3 -m unittest discover -s tests -v
```

The recorded suite has **14 test methods** and **23,274 public API vectors**.
The suite builds through `infs`, including a project-build-and-demo regression.
It includes exhaustive small cases, deterministic large cases, invalid inputs,
CLI checks, and three compiled faulty variants that expose missing
compatibility checks, incorrect negative-remainder handling, and noncanonical
results. Tests give concrete regression evidence alongside the quantified proofs.

For an example beyond JavaScript's exact `Number` range:

```sh
node scripts/demo.mjs --json 2147483646 2147483647 2147483645 2147483646
```

```json
{"status":"solved","solution":"4611686011984936961","period":"4611686011984936962"}
```

The CLI passes integers as BigInt and prints JSON integers as decimal strings.
It rejects values outside signed `i64` before calling Wasm. This transport
behavior is tested; the formal execution targets concern the Wasm functions.

With Coq 8.20.x (`coqc` and `coqchk`) installed, check the mathematical proofs:

```sh
python3 scripts/check_proofs.py
```

The generated-Wasm proof gate is a separate check. For that gate,
build the [pinned verifier environment](../scripts/wasm_environment/README.md)
and start its container with **this checkout** mounted at `/workspaces/crt`.
Then, from the project root on the host:

```sh
python3 scripts/build.py
docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real \
  opam exec -- python3 scripts/check_wasm_proofs.py
```

`scripts/build.py` runs `infs build` and records the project, resolved compiler,
and generated artifact hashes for the audit. The project manifest remains the
build configuration; the helper adds provenance for formal verification.

The gate checks artifact hashes and exact theorem types, recompiles the
proofs, audits transitive assumptions, and independently checks compiled proof
terms with `coqchk`. A negative control verifies that the audit rejects a proof
depending on a generated admitted placeholder.

| Generated record | What it identifies |
| --- | --- |
| `out/manifest.json` | Project and toolchain identity, compiler identity, and source/Wasm/generated-Rocq hashes, recorded by the audit build helper; building alone leaves proof status pending. |
| `build/proofs/report.json` | Mathematical targets, source hashes, assumption audits, and kernel-check result. |
| `build/wasm-proofs/report.json` | Generated contracts, five execution targets, artifact/proof hashes, verifier source identity, and assumption audits. |

The committed [evidence snapshot](evidence/implementation.json) records the
completed checks for this implementation, including the compiled verifier
object fingerprint. Its reproduction notes distinguish that checked environment
from the packaged Docker recipe, which was not separately rebuilt from scratch.

## What the assurance depends on

All mathematical proofs pass assumption auditing with no global assumptions.
The generated-Wasm proofs use nine explicitly audited upstream assumptions:
classical logic, functional extensionality, two classical-real decision
principles, and five abstract SIMD operations inherited through the libraries.
The CRT program uses no SIMD. The exact names are in the
[allowlist](../proofs/wasm/assumptions.allow) and evidence snapshot.

The completed proofs use no project axioms, admissions, or unchecked proof
tactics. The generated Rocq file contains three admitted proof skeletons;
the completed certificate does not depend on them.

The trust boundary includes Rocq's kernel and libraries, the
WasmCert/WasmVerifier semantics and listed assumptions, and the compiler's
translation into matching Wasm and Rocq module representations. Hashes identify
the representations and tested binary; they do not prove the compiler or Node's
WebAssembly engine correct. See the [full proof coverage](../proofs/README.md)
and [implementation reading guide](../references/README.md) for the formal
interfaces and supporting literature.
