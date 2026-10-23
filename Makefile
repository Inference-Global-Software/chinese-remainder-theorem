PYTHON ?= python3
INFC ?= infc
WASM_VERIFIER ?= /workspaces/wasm-verifier
export INFC

.PHONY: build test proofs check demo wasm-proofs wasm-components
build:
	$(PYTHON) scripts/build.py --infc "$(INFC)"

test:
	$(PYTHON) -m unittest discover -s tests -v

proofs:
	$(PYTHON) scripts/check_proofs.py

check: test proofs

wasm-proofs:
	$(PYTHON) scripts/check_wasm_proofs.py --verifier "$(WASM_VERIFIER)"

wasm-components: wasm-proofs

demo: build
	node scripts/demo.mjs 2 6 5 9
