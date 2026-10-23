# Exact CRT contracts and loop invariants

Status, 2026-10-23: **mathematical, loop, exact generated-contract, and all five execution-target proofs completed**.
The authoritative machine-readable targets are in
[`CRTStatements.v`](../specifications/CRTStatements.v). Each `T_*` is a definition
of a proposition to prove, not an asserted theorem. The file has no admitted
proofs or axioms. Its successful elaboration establishes that the statements are
well-typed, not that they hold. The separate
[completed proofs](../proofs/README.md) now establish all 16 mathematical and
loop targets. Actual Wasm execution witnesses and both exact generated `ValidSpec`
obligations are also proved. All five execution-relation targets below are
instantiated with actual WasmCert invocation and signed result decoding.
An operational confluence proof establishes uniqueness of normal results;
[proof coverage](../proofs/README.md) states the exact guarantee and trust boundary.

[`crt_contracts.inf`](../probes/crt_contracts.inf) contains executable feasibility
bodies and 15 source contracts. Keeping bodies in the probe makes applications
refer to actual compiled functions. These bodies are an unverified prototype,
not the project's verified implementation.
The implemented and tested entry point is [`src/main.inf`](../src/main.inf).

## Definitions and quantifier domains

In the mathematical statements, every variable ranges over `Z`, unless stated
otherwise. Define:

```text
M = 2147483647
Word(z) iff -9223372036854775808 <= z <= 9223372036854775807
Moduli(m,n) iff 1 <= m <= M and 1 <= n <= M
Domain(a,m,b,n) iff Moduli(m,n) and 0 <= a < m and 0 <= b < n
S(a,m,b,n,x) iff m divides (x-a) and n divides (x-b)
g = gcd(m,n)
L = (m/g)*n
C(a,m,b,n) iff g divides (b-a)
Canonical(a,m,b,n,x) iff 0 <= x < L and S(a,m,b,n,x)
```

Mathematical `mod` is Euclidean modulo with a positive divisor. Inference `%`
uses signed remainder; it agrees with mathematical modulo on nonnegative
dividends. Divisibility by a positive integer can be tested by either remainder
being zero, even when the dividend is negative. All divisions used in the CRT
construction are by positive integers; `(b-a)/g` is used only after divisibility
has been established, so signed truncation agrees with exact mathematical
division there.

## Mathematical theorem targets

1. **Normalization (`T_normalization`).** For all `a,b,x` and positive `m,n`,
   `S(a,m,b,n,x) iff S(a mod m,m,b mod n,n,x)`.

2. **Gcd reduction (`T_reduction`).** For all positive `m,n`, `g>0`, `g|m`,
   `g|n`, `m/g>0`, `n/g>0`, `gcd(m/g,n/g)=1`, and
   `L=lcm(m,n)>0`.

3. **Generalized CRT (`T_generalized_CRT`).** For all `a,b` and positive `m,n`,
   `(exists x in Z, S(a,m,b,n,x)) iff C(a,m,b,n)`.

4. **Canonical existence and uniqueness (`T_canonical_unique`).** For all `a,b`
   and positive `m,n`, compatibility implies
   `exists x in Z, Canonical(a,m,b,n,x) and
   (forall y in Z, Canonical(a,m,b,n,y) implies y=x)`.

5. **All solutions (`T_all_solutions`).** For all `a,b,x` and positive `m,n`,
   if `S(a,m,b,n,x)`, then for every integer `y`,
   `S(a,m,b,n,y) iff (exists k in Z, y=x+k*L)`.

6. **Impossibility (`T_incompatible`).** For all `a,b` and positive `m,n`,
   incompatibility implies `forall x in Z, not S(a,m,b,n,x)`.

7. **Constructive witness (`T_construct`).** For every valid compatible input,
   put `m1=m/g`, `n1=n/g`. If `n1=1`, `a` is canonical. Otherwise, for every
   `u` with `0<=u<n1` and `m1*u = 1 (mod n1)`, put
   `t=(((b-a)/g)*u) mod n1`. Then `a+m*t` is canonical.

8. **Signed normalization (`T_normalize`).** For every `Word(z)` and
   `1<=d<=M`, set `r=Z.rem(z,d)` and `result=r+d` if `r<0`, otherwise `r`.
   Then `result=z mod d`, `0<=result<d`, and both `r` and `result` fit `i64`.
   This includes `z=i64_min`; do not normalize by negating `z` or forming
   `result-z`, either of which can overflow.

Targets 1–6 concern arbitrary mathematical integers and positive moduli.
The machine envelope applies to targets 7–8 and the implementation contracts.

## Executable contracts

`Exec_f(args,result)` must ultimately mean normal, terminating execution of the
specific generated Wasm function in a valid runtime, with arguments and result
decoded as signed integers. The deterministic executable bodies contain no
nondeterministic choices. `total_correct` requires an execution to exist and
every normally returned result to fit `i64` and satisfy its postcondition.
The `T_*_execution` definitions take an execution relation as a parameter; they
do not supply that relation or assume its correctness.
[`CRTExecutionTargets.v`](../proofs/wasm/CRTExecutionTargets.v) supplies concrete
relations and proves each original target. The guarantee requires a terminating
normal execution to exist and every normal return to satisfy its postcondition;
it does not assert that every possible reduction sequence terminates.

| Function | Preconditions | Exact postcondition |
| --- | --- | --- |
| `gcd_positive(m,n)` | `Moduli(m,n)` | Result is `gcd(m,n)` |
| `normalize(z,d)` | `Word(z)`, `1<=d<=M` | Result is `z mod d` |
| `inverse_coprime(B,A)` | `1<=B<A<=M`, `gcd(A,B)=1` | `0<=u<A` and `B*u = 1 (mod A)` |
| `crt_period(m,n)` | Both arguments are `Word` | Invalid moduli: exactly `-2`; valid moduli: exactly `lcm(m,n)` |
| `crt_solve(a,m,b,n)` | All four arguments are `Word` | Invalid domain: exactly `-2`; valid incompatible input: exactly `-1`; valid compatible input: its canonical solution |

Each row requires termination and absence of traps on its entire precondition.
In particular, the public contracts cover **every `i64` input**, including
extremes; validation occurs before subtraction, multiplication, division, and
remainder that depend on the input envelope. A valid period says nothing about
whether particular residues are compatible.

## Euclid loop

Initialize `(r0,r1)=(m,n)`. While `r1>0`, compute `r2=r0%r1` and update
`(r0,r1)=(r1,r2)` using the old values.

Invariant at each loop head, including exit:

```text
1 <= r0 <= M
0 <= r1 <= M
gcd(r0,r1) = gcd(m,n)
```

Variant: `Z.to_nat(r1)`. Under the guard, `0<=r2<r1`, so the variant strictly
decreases. No ordering between the initial `m,n` is required. On exit `r1=0`,
so `r0=gcd(m,n)`. The positive divisor excludes both divide-by-zero and the
signed `MIN/-1` trap. These are `T_gcd_init`, `T_gcd_step`, and `T_gcd_exit`.

## Extended-Euclid loop

The inverse call uses `A=n1`, `B=m1%n1` after the `n1=1` branch. Gcd reduction
gives `gcd(A,B)=1`, and `1<=B<A<=M`. For the recurrence and its safety invariants
alone, coprimality is unnecessary: `eea_inputs` only requires `1<=B<A<=M`.

Initialize `(r0,r1,s0,s1,t0,t1)=(A,B,1,0,0,1)`. While `r1>0`, compute:

```text
q  = r0 / r1
r2 = r0 % r1
s2 = s0 - q*s1
t2 = t0 - q*t1
(r0,r1,s0,s1,t0,t1) = (r1,r2,s1,s2,t1,t2)
```

All right-hand sides use the old state; the probe uses immutable temporaries
before its sequential assignments. The complete `eea_inv` is:

```text
0 <= r1 < r0 <= A
gcd(r0,r1) = gcd(A,B)
r0 = A*s0 + B*t0
r1 = A*s1 + B*t1
abs(s0*t1 - s1*t0) = 1
s0*s1 <= 0                 and t0*t1 <= 0
r0*abs(s1) + r1*abs(s0) = B
r0*abs(t1) + r1*abs(t0) = A
abs(s0), abs(s1) <= B      and abs(t0), abs(t1) <= A
```

Variant: `Z.to_nat(r1)`. The remainder update strictly decreases it. The targets
`T_eea_init`, `T_eea_step`, and `T_eea_exit` state initialization, preservation
plus decrease, and the final Bézout/inverse result. At exit `r0=gcd(A,B)`;
when this is 1, `A*s0+B*t0=1` and `normalize(t0,A)` is the required inverse.

The weighted absolute-value equalities are needed for intermediate safety.
For example, with `r1>=1` and `q*r1<=r0`:

```text
q*abs(t1) <= r0*abs(t1) <= A
abs(t0-q*t1) = abs(t0) + q*abs(t1)
r1*abs(t0-q*t1) <= r1*abs(t0) + r0*abs(t1) = A
```

Thus both the multiplication and subtraction fit, even on the final iteration.
The analogous argument bounds `q*s1` and `s2` by `B`.
`T_eea_step_bounds` states `1<=q<=A`, `0<=q*r1<=A`, these four coefficient
bounds, and their representability as `i64`. The corresponding Rocq propositions
are now proved in
[`CRTLoops.v`](../proofs/CRTLoops.v).

## CRT arithmetic bounds

`T_crt_bounds` quantifies over every valid compatible input and every normalized
inverse candidate `0<=u<n1`:

| Expression | Bound |
| --- | --- |
| `g`, `m1`, `n1` | Between 1 and `M` |
| `delta=b-a`, `delta/g` | Absolute value at most `M-1` |
| `B=m1%n1`, when `n1>1` | `1<=B<n1` |
| `(delta/g)*u` | Absolute value at most `(M-1)^2` |
| `t=normalize((delta/g)*u,n1)` | `0<=t<n1` |
| `m*t` | `0<=m*t<=M*(M-1)` |
| `x=a+m*t` | `0<=x<L`, because `a<m` and `t<n1` |
| `L=(m/g)*n=m*n1` | `1<=L<=M^2=4611686014132420609` |

The arithmetic is within `i64`. Even products and sums occurring in the
mathematical invariant expressions have absolute bounds at most
`2*M^2=9223372028264841218 < i64_max`. The executable EEA coefficient updates
have the much tighter bounds above. Division and remainder use positive
divisors. The `n1=1` branch skips inversion entirely.

## What Inference can express in the checked compiler

Checked with Inference `0.0.6`, reported revision `95db5e4`, ABI `1.10`.

| Property or construct | Result and implementation approach |
| --- | --- |
| Scalar input guards, signed comparisons, arithmetic, immutable bindings | All 15 contracts translate in proof mode |
| Calls to deterministic scalar helper and public functions | Translate as `T_app`; bare calls yield `HA_app_ok` |
| Termination/nontrapping contract | Bare calls in `solve_total` and `period_total` cover all typed inputs without restrictive assumptions |
| Constructive existence and mathematical uniqueness | `compatible_exists_unique` translates nested `exists` and `forall` as `HA_ex` and `Hall` |
| Correct incompatibility rejection | Directly stated by `solve_compatibility`; bounded absence of a witness is stated separately |
| Loops in executable functions | The two loops compile to standard Wasm in the proof-mode artifact |
| Loops in specification bodies | Rejected with `P002`, reproduced by `rejected_loop.inf` |
| Reassignment in specification bodies | Rejected with `P003`, reproduced by `rejected_mutation.inf` |
| Inductive loop invariants and termination variants | Supply `gcd_inv` and `eea_inv` to the Rocq execution proof; the source translator does not attach or infer them |
| Quantification over all mathematical integers | Use Rocq `Z`; source `i64` quantifiers cover only representable values |

The source canonical interval is complete for the accepted API domain because
`L<=M^2<i64_max`. Therefore every canonical witness is representable. The
unbounded `forall y, exists k` description of all integer solutions belongs in
Rocq. Extend bounded impossibility to all integers using normalization modulo
`L` and the fact that `m|L` and `n|L`.

Do not use operational `unique` as a shortcut for the mathematical theorem.
Its observation-based execution semantics is different; this probe explicitly
compares every canonical witness with the result.

Arithmetic **inside translated assertions** uses machine operations. Writing
an equality does not by itself prove absence of overflow. The ordinary
executable operators carry overflow checks; realizing a bare call requires
normal termination. The mathematical bounds must connect these checked
operations and the source assertions to the `Z` statements.

An application in an `assume` can make an antecedent unsatisfiable if it is
undefined. Consequently, helper and period totality/correctness must be proved
before relying on the call-based compatibility and range assumptions. The two
public totality contracts have no such filters. No property should be certified
from an isolated conditional assertion while these dependencies remain open.

The generated obligations reference the actual module. For functions making
direct calls, establish the appropriate runtime-indexed realization using the
verifier's `ValidSpec_at` route and actual instances of the callees. Proving the
pure `Z` targets alone cannot discharge the executable guarantee.

## Evidence and completed execution targets

See the [reproducible check report](specification-check.md) and its
[machine-readable evidence](evidence/2026-10-23-specifications.json).
The compiler's [versioned Rocq contract](https://github.com/Inferara/inference/blob/95db5e4170fdfd5080afdcb938c7704a790a7b24/core/wasm-to-v/ROCQ_CONTRACT.md)
governs the translation and realization claims above.

The [implementation evidence](evidence/implementation.json) records the completed
connection to generated Wasm instructions and calls, independent `ValidModule`,
both exact `ValidSpec` certificates, pinned dependencies, and assumption audit.
These proofs use the real verifier; the earlier signature-only check remains
historical evidence of expressibility. All five universal `T_*_execution`
targets are discharged by combining finite execution witnesses with the proved
operational result-uniqueness argument. The proof gate checks the exact original
target types with no retained uniqueness premises, as explained in
[proof coverage](../proofs/README.md).
