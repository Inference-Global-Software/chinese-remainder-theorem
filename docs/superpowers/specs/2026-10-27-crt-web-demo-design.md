# Interactive CRT demo

Build and launch a local browser interface to the existing verified finite-system
Wasm solver. The user enters congruences and sees the complete solution class or
an explicit invalid, incompatible, or overflow outcome. Keep the native Inference
project, executable algorithm, mathematical proofs, and evidence unchanged.

## Approach

A buildless HTML/CSS/JavaScript application in `web/` uses the existing Wasm
exports directly. A dependency-free Node server binds to 127.0.0.1 and serves
only named demo assets. This fits the existing Node CLI and avoids adding a
framework/build tool for a single interactive form. A framework would add setup
without useful state-management benefits; a server-side solver would unnecessarily
move computation outside the browser. These are implementation choices.

## Experience

Use a responsive, accessible two-column workspace: editable congruences on the
left, a prominent result on the right. Default to the existing shared-factor
example (2 mod 6, 5 mod 9, 8 mod 15). Add/remove up to16 rows, clear to the empty
system, reverse input order, and choose examples for coprime success, shared
factors, incompatibility, overflow, and incompatible-before-overflow. Editing
invalidates the displayed answer until Solve is pressed. Examples solve at once.
Show canonical residue, period, the full integer solution family, exact sample
solutions, and a remainder check for each input. Use exact BigInt throughout.
All controls work by keyboard; inputs have labels, errors are announced, small
screens remain usable, and large integer results wrap without truncation.

## Verified boundary

Read the expected Wasm SHA256 from the existing committed evidence. Verify it
before serving and again before browser instantiation; refuse mismatched bytes.
Marshal two complete128-byte arrays at offsets0/128. Format/range validation
rejects nonintegers and out-of-i64 values without Number conversion. Mathematical
classification comes from the actual Wasm exports. The UI explains that proofs
cover the solver; the browser interface/compiler translation are outside that
proof boundary. A failure to load/verify/execute is not a mathematical outcome.

## Delivery and verification

No external services, remote assets, package install, hosting registration, or
public deployment. Launch on localhost, open the preview, and leave it running.
Test the real Wasm bridge, local server, browser flows, loading failure, large
integers, mobile layout, and stale-answer handling. Preserve all proof-bound files.
