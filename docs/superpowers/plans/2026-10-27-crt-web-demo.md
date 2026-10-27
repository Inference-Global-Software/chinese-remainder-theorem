# Interactive CRT Demo Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Launch a local interactive web demo backed by the exact verified Wasm.
**Architecture:** Buildless browser app plus allowlisted Node HTTP server; a small
browser/Node-compatible module checks artifact integrity and marshals the ABI.
**Tech Stack:** HTML, CSS, JavaScript modules, Node built-ins, WebAssembly, BigInt.
**Spec:** docs/superpowers/specs/2026-10-27-crt-web-demo-design.md

## Global Constraints

- Capacity16; signed i64 decimal transport; no Number conversion for inputs/results.
- Preserve Inference/proof/evidence bytes; no new solver implementation.
- Local127.0.0.1 only; no publication or runtime dependencies.
- Verify artifact hash against committed evidence before execution.

## Review Focus

- Large integers beyond2^53 must round-trip exactly (Task1 bridge/browser tests).
- Edits must never leave an apparently current old result (Task2 browser test).
- Mismatched/missing Wasm must disable solving and explain recovery (Tasks1/2).
- Empty systems and capacity16 must be reachable by real controls (Task2).
- Mobile result widths and keyboard control labels must remain usable (Task2).

## Task1: Exact browser bridge and local server

**Files:** web/solver.mjs, web/serve.mjs, tests/test_web.mjs.
**Interfaces:** createSolver(bytes, expectedSha256) resolves to solve(rows), where
rows are pairs of decimal strings; result is a tagged solved/invalid/incompatible/
overflow object with BigInt solution and period only for solved. startServer({port,
root}) returns the HTTP server; a CLI wrapper defaults to4173.

- [ ] Write real-Wasm tests for68/90, >2^53, all error classes, precedence, empty,
  capacity, repeated calls, input transport rejection, tampered bytes, and server
  route isolation/integrity failures. Watch failure before implementation.
- [ ] Implement the bridge and allowlisted server. Run Node tests to green.

## Task2: Interactive page, documentation, local launch

**Files:** web/index.html, web/styles.css, web/app.mjs, web/README.md,
  tests/web_browser.mjs, README.md (new launch paragraph only).
**Consumes:** Task1 bridge and server; retained browser QA uses installed Chrome.

- [ ] Write browser checks for default and preset outcomes, edit invalidation,
  exact large values, add/remove/reverse/empty/capacity, loading failure, keyboard
  submit, and mobile overflow. Observe the missing-interface failure.
- [ ] Implement responsive interface, accessible controls, exact solution display,
  example selection, remainder checks, and concise proof-boundary explanation.
- [ ] Document launch/build/test commands. Run Node/browser checks, inspect desktop
  and mobile screenshots, run the existing host regression suite once, and confirm
  all proof-bound source hashes are unchanged.
- [ ] Commit completed feature; obtain one fresh final review, resolve substantive
  findings, and leave local server/preview open for the user.
