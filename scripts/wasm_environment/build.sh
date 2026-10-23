#!/usr/bin/env bash
# Run on the host; all Coq/opam/dune operations are in the Dockerfile.
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: bash scripts/wasm_environment/build.sh /path/to/wasm-verifier" >&2
  exit 2
fi

crt_recipe_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
crt_verifier_repo=$1
crt_verifier_commit=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["wasmVerifierCommit"])' "$crt_recipe_dir/provenance.json")
git -C "$crt_verifier_repo" cat-file -e "${crt_verifier_commit}^{commit}"

crt_build_context=$(mktemp -d)
trap 'rm -rf -- "$crt_build_context"' EXIT
mkdir "$crt_build_context/wasm-verifier"
git -C "$crt_verifier_repo" archive "$crt_verifier_commit" \
  _CoqProject dune-project coq-wasm-verifier.opam theories ci \
  | tar -x -C "$crt_build_context/wasm-verifier"
cp "$crt_recipe_dir"/{Dockerfile,bootstrap.sh,lock.py,worker-opam.lock.json,provenance.json} \
  "$crt_build_context/"

crt_build_options=()
if [[ ${CRT_DOCKER_NO_CACHE:-0} == 1 ]]; then
  crt_build_options+=(--no-cache)
fi

docker build "${crt_build_options[@]}" --platform linux/amd64 \
  --network "${CRT_DOCKER_BUILD_NETWORK:-default}" \
  --tag "${CRT_WASM_IMAGE:-crt-wasm-verifier:locked}" "$crt_build_context"
