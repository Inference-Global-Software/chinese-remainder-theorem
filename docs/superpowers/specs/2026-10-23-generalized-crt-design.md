# Generalized CRT demonstration design

Date: 2026-10-23

Status: historical design baseline. The implementation and all original proof
targets are now completed; see the [current specifications](../../specifications.md)
and [proof coverage](../../../proofs/README.md) for the delivered guarantees.

Repository: `Inference-Global-Software/chinese-remainder-theorem`.

Implementation references: [annotated research and reading guide](../../../references/README.md).

## Purpose

Demonstrate Inference to both mathematicians and software developers through a
recognizable mathematical theorem behind a useful executable algorithm. Success
means a working generalized CRT solver, explicit source specifications, completed
proofs about its compiled execution, and a reproducible periodic-schedule example.

The theorem selection and organization follow the project discussion. The exact
API and first-release boundaries below are proposed engineering choices.

## Mathematical statement

For positive integers `m`, `n`, and integers `a`, `b`, the simultaneous
congruences `x = a (mod m)` and `x = b (mod n)` are solvable exactly when
`gcd(m, n)` divides `b - a`. When solvable, exactly one solution lies in
`0 <= x < lcm(m, n)`; every integer solution differs from that representative
by an integer multiple of `lcm(m, n)`.

The implementation accepts normalized remainders. The abstract mathematical
statement may use arbitrary integer remainders, with an explicit normalization
lemma connecting the two formulations.

## First-release scope

- Two congruences, including non-coprime moduli.
- `1 <= m, n <= 2147483647`, `0 <= a < m`, and `0 <= b < n`.
- `i64` arithmetic for inputs, results, and intermediates.
- Executable gcd, modular inversion, CRT construction, and repeat-period routines.
- Source specifications and Rocq proofs of their behavioral contracts.
- A small command-line demonstration executing Wasm and explaining the schedule
  example. Integer transport must preserve `i64` values exactly.
- Deterministic runtime checks, independent mathematical reference checks,
  deliberate faulty variants, and reproducible proof checking.

Arbitrary-length systems, arbitrary-precision executable arithmetic, RSA, a
browser interface, and a formal asymptotic complexity bound are subsequent work.
The initial proof includes termination.

## Public interfaces

Use scalar interfaces so source specifications can refer directly to executable
functions without depending on aggregate-call support in the proof translator.

```text
crt_solve(a: i64, m: i64, b: i64, n: i64) -> i64
crt_period(m: i64, n: i64) -> i64
```

`crt_solve` returns:

- `-2` when any argument violates the accepted domain;
- `-1` for valid arguments with incompatible congruences;
- otherwise the canonical solution in `0 <= x < lcm(m, n)`.

`crt_period` returns `-2` for an invalid modulus and otherwise `lcm(m, n)`.
The period is a property of the moduli; it does not assert compatibility of a
particular pair of residues.

Both exported functions must reject invalid arguments safely across the full
`i64` input domain. Validate arguments before division, subtraction, or
multiplication that relies on the bounded-domain assumptions. Internal helper
contracts may use explicit preconditions.

## Construction

1. Validate the public arguments.
2. Compute `g = gcd(m, n)` using Euclid's remainder algorithm.
3. Reject as incompatible when `g` does not divide `b - a`.
4. Set `m1 = m / g`, `n1 = n / g`.
5. When `n1 = 1`, return `a` directly; no modular inverse is needed.
6. Otherwise compute the inverse `u` of `m1` modulo `n1` with extended Euclid.
7. Compute `t = normalize(((b - a) / g) * u, n1)`.
8. Return `a + m * t`. The repeat period is `(m / g) * n`.

Normalization produces a residue in `0 <= t < n1` even when the dividend is
negative. All intermediate bounds, including extended-Euclid coefficient
updates, must be proved. A bound on the final result alone is insufficient.

## Proof structure

### Mathematical layer

- Euclid preserves the gcd and decreases a nonnegative remainder measure.
- Extended Euclid preserves a Bezout relation and yields the required inverse.
- The compatibility condition is necessary and sufficient.
- The construction satisfies both congruences and the canonical range.
- Any two solutions differ by a multiple of the lcm.
- Incompatible residues admit no integer solution.

### Executable layer

- The compiled helper routines implement their mathematical models.
- Each loop terminates under its contract.
- Arithmetic, division, and remainder operations are defined wherever executed.
- Public input validation implements the documented result conventions.
- The generated source-specification obligations follow from these execution
  facts, including completeness and correct rejection.

Uniqueness should initially be stated by universally comparing canonical
solutions. Any use of Inference's operational `unique` construct requires a
separate justification that the observed execution states express the intended
mathematical uniqueness.

Keep loops in executable functions. Source specification bodies use supported
quantifiers, immutable scalar bindings, assumptions, assertions, and scalar
function applications. Proving a separate mathematical model without connecting
it to the emitted function bodies does not meet the project goal.

## Artifact and dependency policy

Record immutable compiler and proof-library revisions when the first working
proof baseline is established. Publish the generated Wasm, generated obligations,
proof completions, a machine-readable evidence manifest, and reproduction steps.

The initial demonstration should execute the same proof-mode Wasm artifact from
which the verified module is translated. Any separately produced executable
requires checked correspondence before inheriting the correctness claim.

Proof completion must preserve generated program definitions and target theorem
statements. Supporting lemmas must be checked. No admitted target or newly
introduced axiom may stand in for a required proof. Audit transitive assumptions
and identify the existing proof framework's trusted dependencies explicitly.

A verified public release requires proof dependencies that an unaffiliated
reviewer can obtain. Accessible dependencies and a successful clean reproduction
are release acceptance conditions; a local developer checkout alone is not
public reproduction evidence.

## Validation

Runtime validation should include:

- `(a,m,b,n) = (2,6,5,9)` gives `14`, with period `18`;
- `(2,6,4,9)` gives `-1`;
- `(2,3,3,5)` gives `8`, with period `15`;
- `(0,1,0,1)` gives `0`, with period `1`;
- equal moduli with both equal and unequal residues;
- one modulus dividing the other;
- negative `b - a`, zero residues, and moduli near the upper bound;
- invalid moduli and residues, including extreme `i64` arguments;
- cases whose correct result exceeds JavaScript's exact-number range, with an
  exact integer interface in the demonstration driver;
- exhaustive small-domain comparison against a simple independent solver and
  deterministic large-domain comparison against an unbounded-integer oracle.

Faulty variants should exercise omitted compatibility checks, incorrect handling
of negative remainders, and wrong canonical normalization. Exhibit concrete
counterexamples and establish that the corresponding correctness statement is
false. A proof search merely timing out is not evidence of a refutation.

## Completion criteria

1. The documented Wasm commands run the examples with exact integer results.
2. Every required behavioral obligation is closed and independently checked.
3. The evidence identifies the exact program, specifications, dependency pins,
   and assumptions being certified.
4. Runtime and proof reproduction succeed from the documented environment.
5. The README states the implemented domain, completed guarantees, and remaining
   limitations accurately.
6. The public demonstration explains both a successful synchronization and a
   mathematically impossible one.
