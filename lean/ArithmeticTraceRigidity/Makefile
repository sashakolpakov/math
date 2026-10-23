.PHONY: verify

verify:
	python3 scripts/check_lean_source.py
	lake build
	python3 scripts/check_lean_axioms.py
