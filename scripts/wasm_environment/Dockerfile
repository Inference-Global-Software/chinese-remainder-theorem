FROM coqorg/coq:8.20@sha256:e50d77c4c5a9aa0d76ae1b343d79c5f922da3a75054b79c5dc635895438e4674

USER coq
COPY --chown=coq:coq wasm-verifier/ /workspaces/wasm-verifier/
COPY --chown=coq:coq bootstrap.sh lock.py worker-opam.lock.json provenance.json /opt/crt-wasm-environment/
WORKDIR /workspaces/wasm-verifier
RUN bash /opt/crt-wasm-environment/bootstrap.sh

ENV WASM_VERIFIER_PATH=/workspaces/wasm-verifier/_build/default/theories
WORKDIR /workspaces/crt
CMD ["sleep", "infinity"]
