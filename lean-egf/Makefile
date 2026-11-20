# lean-egf — the gate of the egf library (see lakefile.toml, DEC-133).
# bash with pipefail: a failure inside a pipeline is not swallowed by the last command.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

.PHONY: check build scaffold audit

check: build scaffold audit
	@echo "lean-egf: all gates green"

# The strict library: warningAsError, so a `sorry`, an unused variable or a deprecation fails.
build:
	lake build EGF 2>&1 | tee build.log

scaffold:
	lake build EGFScaffold 2>&1 | tee -a build.log

# `sorry` read off the sources, then every declaration's axioms read off the environment.
audit:
	python3 scripts/sorry_count.py
	lake env lean scripts/AxiomSweep.lean
