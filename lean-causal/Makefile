# lean-causal — the gate of the ETT library while it lives outside `lean/` (see lakefile.toml).
# bash with pipefail: a failure inside a pipeline is not swallowed by the last command.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

.PHONY: check build scaffold audit

check: build scaffold audit
	@echo "lean-causal: all gates green"

# The strict library: warningAsError, so a `sorry`, an unused variable or a deprecation fails.
build:
	lake build Causal 2>&1 | tee build.log

scaffold:
	lake build CausalScaffold 2>&1 | tee -a build.log

# `sorry` read off the sources, then every declaration's axioms read off the environment.
audit:
	python3 scripts/sorry_count.py
	lake env lean scripts/AxiomSweep.lean
