# Real WasmVerifier container

This recipe builds Coq 8.20.1, WasmCert-Coq 2.2.0, and the real WasmVerifier
theory. It checks the installed package versions, builds the entire theory,
rejects proof holes, and runs the verifier's transitive-assumptions audit.
The audit compares against WasmVerifier's reviewed upstream allowlist; it does
not claim that upstream code is axiom-free.

The immutable versions are recorded in `provenance.json`:

- Coq base image: `coqorg/coq:8.20@sha256:e50d77c4c5a9aa0d76ae1b343d79c5f922da3a75054b79c5dc635895438e4674`.
- WasmCert: `0fd83fa708922721132b6d6737179568d1f1d553`, the source behind `v2.2.0`.
- WasmVerifier: `8f485f037a270271bf2e1393c24fc0684097163b`.

`worker-opam.lock.json` is copied unchanged from
`inference-ai-prover/contracts/worker-opam.lock.json` at commit
`8248124b80e01a1ea89b633ff54d74ea96b3effb`. Its checksum is recorded in
`provenance.json`. Its original `wasmVerifierCommit` and `sourceImage` fields
describe where those package versions were recorded. This recipe uses the
verifier revision in `provenance.json` instead. It does not pull the private
worker image.

From the CRT project root, provide a local verifier repository containing the
pinned commit:

```sh
bash scripts/wasm_environment/build.sh /path/to/wasm-verifier
```

The script archives that commit into a temporary build context. It does not
copy local build outputs, `.git`, credentials, or uncommitted changes. All opam,
Coq, and dune commands run inside Docker. The host needs Docker, Python 3, git,
and tar. The base image is `linux/amd64`; the initial dependency compilation is
substantial. `CRT_WASM_IMAGE` overrides the output image name.

If the current login session does not yet have the Docker group, run:

```sh
sg docker -c 'bash scripts/wasm_environment/build.sh /path/to/wasm-verifier'
```

On Linux, if Docker bridge DNS cannot resolve package servers but host
networking works, the build can use it without changing host DNS settings:

```sh
CRT_DOCKER_BUILD_NETWORK=host bash scripts/wasm_environment/build.sh /path/to/wasm-verifier
```

Start the resulting environment with the CRT checkout mounted for compilation:

```sh
docker run --detach --name crt-wasm-verifier-real \
  --mount type=bind,source="$(pwd)",target=/workspaces/crt \
  crt-wasm-verifier:locked
```

For example, compile the generated module from the project root in-container:

```sh
docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real \
  opam exec -- coqc \
  -R /workspaces/wasm-verifier/_build/default/theories WasmVerifier \
  -Q build/crt CRTGenerated build/crt/crt.v
```

`WASM_VERIFIER_PATH` in the image points to the compiled real theory. Follow the
project's proof instructions for the required build order and companion proof
namespace flags. Rebuild pure Coq modules in this container before importing
them into the generated-Wasm proof modules.

Check the full CRT certificate (after building `build/crt` with Inference):

```sh
docker exec -u coq -w /workspaces/crt crt-wasm-verifier-real \
  opam exec -- make wasm-proofs
```

This includes exact generated contract checks, transitive assumption auditing,
a negative control that rejects the generated admitted certificate, and an
independent `coqchk` run. Results are written to `build/wasm-proofs/report.json`.
