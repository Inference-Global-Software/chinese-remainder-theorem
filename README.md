# Chinese Remainder Theorem in Inference

A planned constructive implementation and formal verification of the generalized
Chinese Remainder Theorem (CRT), written in Inference and compiled to WebAssembly.

**Status: design stage.** This repository currently contains the project scope and
design. The solver, executable artifacts, and completed proofs are not present yet.
No verification result is claimed.

## The problem

Given positive moduli `m`, `n` and normalized remainders `a`, `b`, find the smallest
nonnegative integer `x` satisfying both:

```text
x mod m = a
x mod n = b
```

The generalized CRT says that a solution exists exactly when `gcd(m, n)` divides
`b - a`. When it exists, the solution is unique in `0 <= x < lcm(m, n)`.

For example, `x mod 6 = 2` and `x mod 9 = 5` have the canonical solution **14**.
All integer solutions are `14 + 18k`, for integer `k`. Changing the second
remainder to **4** makes the conditions incompatible.

## A useful application: synchronizing periodic schedules

One process runs at times `2, 8, 14, 20, ...`; another at `5, 14, 23, 32, ...`.
Their first coincidence is at time **14**, and they coincide every **18** time
units thereafter. The same algorithm can identify offsets for which they never
coincide.

This example connects the mathematics to an executable algorithm for developers
and gives a public demonstration a concrete question to answer.

## Planned guarantees

- The gcd and modular-inverse routines compute their mathematical specifications.
- Every successful CRT result satisfies both congruences.
- Every compatible input produces a solution.
- The returned solution is the unique one in the canonical interval.
- A mathematical failure result means that no solution exists.
- Execution terminates and arithmetic stays within its machine representation.
- Invalid API inputs are distinguished from mathematically incompatible inputs.

The first version will accept moduli from `1` through `2^31 - 1`, normalized
nonnegative remainders, and use `i64` arithmetic. Its implementation guarantee will
explicitly cover that bounded domain. Supporting mathematical lemmas can use
unbounded integers in Rocq.

## Verification approach

Inference will contain the executable algorithm and source specifications. The
compiler will produce Wasm and Rocq proof obligations. Completed proofs must
connect the generated executable functions to the mathematical result and pass
independent Rocq checking.

The demonstration must execute the artifact covered by the proof evidence.
Compiler versions, proof dependencies, artifact hashes, theorem assumptions, and
reproduction commands will be recorded before any verified release is claimed.

See the [proposed design](docs/superpowers/specs/2026-10-23-generalized-crt-design.md)
for the interfaces, proof structure, and acceptance criteria.

## References

- [Chinese Remainder Theorem — UMBC](https://userpages.cs.umbc.edu/chang/cs203.f10/crt.shtml)
- [Generalized CRT compatibility — University of Colorado](https://math.colorado.edu/~kearnes/Teaching/Courses/S26/crt.pdf)

RSA round-trip correctness is a possible later application of the verified
arithmetic. It is outside the initial project scope.
