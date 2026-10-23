# Research and implementation references

Collected on 2026-10-23 for the [generalized CRT design](../docs/superpowers/specs/2026-10-23-generalized-crt-design.md).
These references guide the work; they do not certify an implementation in this
repository. [BibTeX](references.bib) covers the papers, book, and technical note.

## Reading order and proof coverage

| Work to do | Read first | What we must establish in this project |
| --- | --- | --- |
| Mathematical contracts and construction | Shoup, Sections 2.3–2.4 and 4.1–4.3 | Compatibility, canonical solution, uniqueness modulo the lcm |
| Euclid and inverse proofs | Okazaki–Aoki–Shidama; Coq `Znumtheory` | Loop invariants, Bezout identity, decreasing remainder |
| Machine arithmetic | Collins; Hurchalla; Wasm numeric semantics | Bounds on every intermediate, correct signed-remainder normalization |
| Compiled-program correctness | Watt et al. 2019; Inference's Rocq contract | Generated obligations connected to actual function execution |
| Semantic foundations and reproducibility | Watt et al. 2021; WasmCert-Coq | Exact semantics, dependency versions, and audited assumptions |

## Papers

### 1. Extended Euclidean Algorithm and CRT Algorithm

**Hiroyuki Okazaki, Yosiki Aoki, Yasunari Shidama (2012).**
*Formalized Mathematics* 20(2), 175–179.
[DOI](https://doi.org/10.2478/v10037-012-0020-2) ·
[Local PDF](papers/okazaki-aoki-shidama-2012-extended-euclidean-crt.pdf) ·
[Publisher PDF](https://reference-global.com/download/article/10.2478/v10037-012-0020-2.pdf)

The closest formalization reference for the algorithm chain. Read Sections 1–3:
proposition (2) identifies the computed gcd; (6) gives the Bezout identity; (7)
establishes modular inversion; (11) and (15) concern the CRT construction.

**Scope:** the CRT results assume pairwise coprime moduli, and the formalization
uses Mizar and mathematical integers. Our non-coprime compatibility test, lcm
period, machine bounds, and Inference/Wasm execution proofs remain necessary.

### 2. Computing Multiplicative Inverses in GF(p)

**George E. Collins (1969).** *Mathematics of Computation* 23(105), 197–200.
[Publisher](https://www.ams.org/journals/mcom/1969-23-105/S0025-5718-1969-0242345-5/) ·
[Publisher PDF](https://www.ams.org/journals/mcom/1969-23-105/S0025-5718-1969-0242345-5/S0025-5718-1969-0242345-5.pdf)

A historical source for extended-Euclid coefficient bounds, identified and
discussed in Hurchalla's analysis below. Use the pair to choose invariants for
coefficient updates. Check input ordering and final-iteration assumptions before
applying a bound to our implementation.

**Access:** the publisher returned HTTP 403 to automated retrieval during
collection. Bibliographic details and the publisher PDF link were cross-checked
against Hurchalla's references. No local copy is included.

### 3. A Program Logic for First-Order Encapsulated WebAssembly

**Conrad Watt, Petar Maksimović, Neelakantan R. Krishnaswami, Philippa Gardner
(2019).** *ECOOP 2019*, LIPIcs 134, 9:1–9:30.
[Publisher and DOI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2019.9) ·
[Local PDF](papers/watt-et-al-2019-wasm-logic.pdf)

Read the assertion language, structured-control proof rules, and soundness
argument. This is the program-logic foundation identified by the Inference
verifier, and explains how stack-based execution supports compositional proofs.

**Scope:** the paper's mechanization is in Isabelle/HOL. Our selected Rocq
verifier's definitions and compiler contract govern the actual obligations.
This reference does not discharge our loop-termination or executable CRT proofs.

### 4. Two Mechanisations of WebAssembly 1.0

**Conrad Watt, Xiaojia Rao, Jean Pichon-Pharabod, Martin Bodin, Philippa Gardner
(2021).** *Formal Methods (FM 2021)*.
[Author publication page](https://www.doc.ic.ac.uk/~pg/publications/Watt2021Two.html) ·
[Author PDF](https://www.doc.ic.ac.uk/~pg/publications/Watt2021Two.pdf) ·
[DOI](https://doi.org/10.1007/978-3-030-90870-6_4)

Explains the WasmCert-Isabelle and WasmCert-Coq semantic foundations, including
type soundness, numeric definitions, and instantiation. Read it to understand
which semantic layer the compiled-program proof depends on.

**Scope:** the article describes WebAssembly 1.0-era work. Pin the actual
WasmCert-Coq revision used by our verifier; later repository features are not
established merely by citing this paper. Linked only; redistribution permission
for this particular author PDF was not established.

## Mathematical and implementation companions

### 5. A Computational Introduction to Number Theory and Algebra

**Victor Shoup, electronic Version 2 (2008), corresponding to the second edition.**
[Author page](https://shoup.net/ntb/) ·
[Version 2 PDF](https://shoup.net/ntb/ntb-v2.pdf) ·
[Version 2 errata](https://shoup.net/ntb/errata-v2.pdf)

Use Sections 2.3–2.4 for linear congruences and CRT, and 4.1–4.3 for Euclid,
extended Euclid, modular inversion, and construction. Theorem 4.3 supplies
coefficient invariants; Example 4.3 treats a linear congruence with a possible
no-solution result; Theorem 4.6 gives effective CRT for coprime moduli.

Our pairwise generalized problem reduces to a linear congruence by substituting
`x = a + m*t`, giving `m*t = b-a (mod n)`. This is the connection to formalize
using the linear-congruence results; do not apply the coprime theorem directly
to arbitrary `m,n`.

**Access:** linked, not mirrored. The electronic book carries
CC BY-NC-ND 3.0 terms; its copyright page and the author's errata remain authoritative.

### 6. Proof of Bounds for the Extended Euclidean Algorithm

**Jeffrey Hurchalla (2018).** Author's technical article.
[Article and supporting derivations](https://jeffhurchalla.com/2018/10/09/analysis-of-bounds-in-the-extended-euclidean-algorithm/)

Useful for the gap between mathematical integers and fixed-width execution:
the analysis addresses coefficient-update products as well as stored coefficients,
and separates the final iteration from tighter non-final bounds.

Treat these as candidate invariants to prove in Rocq for our exact recurrence
and input envelope. This is an implementation-focused article, not a
machine-checked proof or a peer-reviewed research paper. Linked only.

## Authoritative technical references

### 7. Coq 8.20 number-theory library

[Versioned `ZArith/Znumtheory.v`](https://github.com/rocq-prover/rocq/blob/V8.20.0/theories/ZArith/Znumtheory.v)

The inspected source contains `extgcd`, `extgcd_correct`, `Zis_gcd_bezout`,
`Gauss`, and `Zis_gcd_rel_prime`. They are useful starting points for Bezout,
divisibility, and the coprimality of gcd-reduced moduli. Use the chosen build's
actual signatures. This versioned reading reference does not select the
project's eventual compiler or proof-library pins.

### 8. WebAssembly numeric semantics and WasmCert-Coq

[Official Core Specification](https://webassembly.github.io/spec/core/bikeshed/index.html) ·
[WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq)

Check signed division, signed remainder, and trap conditions. A signed remainder
can be negative; it is not automatically the canonical mathematical modulo.
Ordinary Wasm integer add/subtract/multiply wrap. Inference's checked arithmetic
adds behavior that must be accounted for using its emitted code and contract.

The official specification link tracks development. Pin the semantics consumed
by the verifier, and establish the bridge from mathematical integers to its
machine-word operations.

### 9. Inference's generated Rocq contract

[Compiler-owned `ROCQ_CONTRACT.md`](https://github.com/Inferara/inference/blob/main/core/wasm-to-v/ROCQ_CONTRACT.md)

Use this for supported specification constructs, emitted obligation forms,
function-application semantics, arithmetic definedness, and exact-artifact
checking. It is the implementation reference for writing `.inf` specifications.
Pin its compiler revision when implementation starts. Module typing alone does
not establish behavioral correctness.

## Proof obligations that the reading does not replace

For our two-modulus construction, formalize these connections explicitly:

1. Compatibility is equivalent to divisibility of `b-a` by `gcd(m,n)`.
2. Division by that positive gcd produces coprime reduced moduli.
3. The modulus-one branch is correct without invoking an inverse routine.
4. Normalizing the signed intermediate produces `0 <= t < n/g`.
5. `a + m*t` satisfies both congruences and lies below `(m/g)*n`.
6. All solutions agree modulo that lcm; incompatibility excludes all solutions.
7. Coefficient updates and CRT arithmetic fit in `i64`, including intermediates.
8. Loop termination, input validation, and source contracts hold for the actual
   generated function bodies and the demonstrated artifact.

These are project obligations, not additional theorems claimed as already proved.

## Local copies and attribution

Both checked-in PDFs are unmodified publisher copies. They retain their original
copyright and license notices. Their licenses apply to those documents; they are
not relicensed by this repository. No author endorsement is implied.

| File | Attribution and license |
| --- | --- |
| [Extended Euclidean Algorithm and CRT Algorithm](papers/okazaki-aoki-shidama-2012-extended-euclidean-crt.pdf) | Okazaki, Aoki, Shidama; © 2012 University of Białystok; [CC BY-SA 3.0 or later](https://creativecommons.org/licenses/by-sa/3.0/), as stated on page 175 |
| [A Program Logic for First-Order Encapsulated WebAssembly](papers/watt-et-al-2019-wasm-logic.pdf) | Watt, Maksimović, Krishnaswami, Gardner; [CC BY 3.0](https://creativecommons.org/licenses/by/3.0/), as stated by the publisher |

[manifest.json](manifest.json) records source URLs, retrieval date, sizes, and
SHA-256 digests. [SHA256SUMS](SHA256SUMS) can be checked from the repository root:

```sh
(cd references && sha256sum --check SHA256SUMS)
```
