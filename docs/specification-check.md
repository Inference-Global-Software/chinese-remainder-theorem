# Specification feasibility check

Checked on 2026-10-23. **Inference can express the bounded CRT contracts.**
The unrestricted mathematical statements and inductive loop proofs require
Rocq. No theorem or compiled-program correctness proof is claimed complete.

## Recorded results

| Check | Result |
| --- | --- |
| Inference proof-mode compilation | 15 source contracts, 15 emitted `hassert` definitions |
| Existence/uniqueness quantifier shape | `HA_ex` and nested `Hall` present |
| Execution realization shape | `HA_app_ok` present; full-domain public totality contracts emitted |
| Mathematical statement elaboration | 21 `T_*` proposition definitions accepted by Coq 8.20.1 |
| Generated Rocq elaboration | Accepted against the compiler's public **signature-only stub** |
| Negative specification probes | Loops rejected with `P002`; mutation rejected with `P003` |
| Exact proof-mode Wasm runtime checks | 44,719 passed with Node v26.10.0 and BigInt transport |
| Extended-Euclid invariant model audit | 9,155 input pairs; 56,995 visited states; 47,840 steps |
| Generated proof closure | **Not done: three `Admitted` obligations remain** |

The runtime checks include every normalized residue pair for moduli 1–16,
compared with independent brute-force enumeration; deterministic large inputs
checked with Python's unbounded arithmetic and builtin modular inverse; invalid
inputs including both `i64` extremes; negative differences; modulus 1; equal and
dividing moduli; and correct results above JavaScript's exact `Number` range.
They also cover helper routines. These are finite tests, not quantified proofs.

The model audit evaluates the proposed EEA invariant at every loop head,
including exit, for every `1<=B<A<=128`, 1,024 deterministic large pairs, and
three boundary/long-recurrence pairs. It checks the intermediate bounds and
decreasing remainder. It does not prove induction for arbitrary states or
establish correspondence with Wasm execution.

## Compiler and proof-status boundary

The checked local compiler reports `infc 0.0.6`, revision `95db5e4`, ABI `1.10`.
Its clean source checkout was at
`95db5e4170fdfd5080afdcb938c7704a790a7b24`. The
[JSON report](evidence/2026-10-23-specifications.json) records the compiler binary,
input, and generated artifact SHA-256 hashes. The existing local binary was
used; this check does not attest that it was reproducibly built from that
source. Future certified artifacts need a clean build and dependency pins.

The generated file contains these unfinished theorems:

```text
valid_crt_contracts                    : ValidModule ...
valid_crt_contracts__HelperContracts   : ValidSpec ...
valid_crt_contracts__PublicContracts   : ValidSpec ...
```

Each ends in `Admitted.`. The generated file was elaborated using the compiler's
public `rocq-stub`, which supplies signatures and axioms without verification
semantics. This detects malformed constructor applications; it cannot certify
the truth of any obligation. The separate `CRTStatements.v` uses only the
standard integer library and defines targets without admissions or axioms.

Generated `.v`, `.wasm`, elaboration products, logs, and runtime vectors stay in
the ignored `build/` directory. The checked-in evidence is a feasibility record,
not a verified release manifest.

## Reproduce

Requirements: Python 3.8+, Node with WebAssembly/BigInt support, Coq 8.20.x
providing `coqc`, and an Inference compiler plus its matching source checkout.
The recorded run used Node v26.10.0 and Coq 8.20.1. Use the revision above for
the same compiler contract and stub; build the compiler using its repository
instructions.

From this repository root, replacing both compiler paths:

```sh
python3 scripts/check_specifications.py \
  --infc /path/to/inference/target/debug/infc \
  --inference-source /path/to/inference
```

The script writes `build/specifications/report.json`, the exact compiled
artifacts, compiler diagnostics, and generated test inputs. It copies the stub
into `build/` before elaboration, so it does not modify the compiler checkout.
It fails on an unexpected compiler outcome, a missing expected assertion
constructor, a contract-count mismatch, elaboration failure, runtime mismatch,
or a failed finite invariant check. It never marks the generated admissions as
proved. Compare its input/artifact hashes with the recorded report when using
the same toolchain; binary build hashes may differ across builds.

To check only the mathematical statement syntax and types:

```sh
coqc specifications/CRTStatements.v
```

For the full theorem statements, invariant definitions, machine bounds, and
source-language limitations, read [the specification document](specifications.md).
