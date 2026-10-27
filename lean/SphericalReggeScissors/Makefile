.PHONY: verify

verify:
	lake build
	python3 scripts/check_lean_source.py
	python3 scripts/check_lean_axioms.py
	python3 scripts/check_formal_coverage.py
	python3 scripts/check_contract_parity.py
