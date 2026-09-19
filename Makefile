# LeanArticles — the gate, and the self-test that proves each gate can fail.
#
# `make check` is what pre-push runs. bash with pipefail so a failure inside a pipeline is not
# swallowed by the last command's exit status (`cmd | tail` reports tail's status; tail always
# succeeds). No `-` recipe prefixes: a gate that cannot fail proves nothing.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
PY := python3

.PHONY: check selftest gate-host gate-dropbox-ignore gate-registers gate-deps lib-check papers-check \
        ledgers regression

check: gate-host gate-dropbox-ignore gate-registers gate-deps lib-check papers-check
	@echo "check: all gates green"

gate-host:
	$(PY) tools/host_guard.py

gate-dropbox-ignore:
	$(PY) tools/dropbox_ignore.py --check

# The registers are well formed and append-only; the freeze (DEC-2) and every blocked paper's
# open question are checked here too, so a block cannot outlive the question it names.
gate-registers:
	$(PY) tools/registers.py check

gate-deps:
	$(PY) tools/deps_register.py

# The Lean library's own gate. Under FREEZE=1 (DEC-2, until hub.toml [freeze].until, enforced by
# gate-registers) the library is a read-only submodule of GFNBoundsLean and its gate is that
# repository's; this target then only records the pin it would have checked.
lib-check:
ifeq ($(FREEZE),1)
	@echo "lib-check: FREEZE=1 — lean/ is the read-only submodule at $$(git -C lean rev-parse --short HEAD); its gate is GFNBoundsLean's (DEC-2)"
else
	$(MAKE) -C lean check
endif

papers-check:
	$(PY) tools/papers_check.py

# Regenerate every paper's ledger, markdown and DAG (papers_check then diffs them).
ledgers:
	@for c in papers/*/ledger/ledger.toml; do $(PY) tools/ledger.py -c $$c build || true; done

# The generalised ledger reproduces the GFN Bounds ledger byte for byte (modulo commit ids).
regression:
	bash tools/regression_ledger.sh

# Every gate has a fixture that makes it fail; selftest fails if one passes on its fixture.
selftest:
	$(PY) tools/selftest.py
