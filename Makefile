PYTHON ?= python3
INFC ?= infc
export INFC

.PHONY: build test proofs check demo
build:
	$(PYTHON) scripts/build.py --infc "$(INFC)"

test:
	$(PYTHON) -m unittest discover -s tests -v

proofs:
	$(PYTHON) scripts/check_proofs.py

check: test proofs

demo: build
	node scripts/demo.mjs 2 6 5 9
