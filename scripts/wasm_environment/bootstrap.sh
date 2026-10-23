#!/usr/bin/env bash
# Run only inside the pinned Coq image, with cwd=/workspaces/wasm-verifier.
set -euo pipefail

crt_recipe_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
python3 "$crt_recipe_dir/lock.py" render coq-wasm-verifier.opam
crt_wasm_pin=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["pins"]["coq-wasm"]["source"])' "$crt_recipe_dir/worker-opam.lock.json")

opam exec -- coqc --version
opam update -y
opam pin add -y -n coq-wasm.2.2.0 "$crt_wasm_pin"
opam install -y . --deps-only --locked -j "${COQ_DEPS_JOBS:-2}"
python3 "$crt_recipe_dir/lock.py" check

# Make the modules needed by CRT proofs available before compiling all examples.
opam exec -- dune build -j 2 \
  theories/Verifier.vo theories/Automation.vo theories/NumericDischarge.vo \
  theories/Loop.vo theories/Soundness.vo theories/examples/Issue316OverflowExample.vo
opam exec -- dune build -j 2
python3 ci/check-proof-completeness.py
bash ci/check-assumptions.sh
