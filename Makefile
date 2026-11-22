# LeanArticles — the gate, and the self-test that proves each gate can fail.
#
# `make check` is what pre-push runs. bash with pipefail so a failure inside a pipeline is not
# swallowed by the last command's exit status (`cmd | tail` reports tail's status; tail always
# succeeds). No `-` recipe prefixes: a gate that cannot fail proves nothing.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
PY := python3

.PHONY: check mirror selftest gate-host gate-dropbox-ignore gate-registers gate-deps lib-check papers-check \
        gate-cassettes gate-tests ledgers regression test doubledag

check: gate-host gate-dropbox-ignore gate-registers gate-deps gate-cassettes gate-tests lib-check papers-check
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

# Every recorded model exchange is sound and keyed by its own contents: a cassette edited by
# hand no longer answers the question it claims to answer, and that is a failure.
gate-cassettes:
	$(PY) tools/llm.py verify

# The tools' own tests. They run with the model backend in replay -- `tests/
# test_no_model_in_gates.py` asserts that the whole gate passes with every ask refused.
# `tests/test_no_model_in_gates.py` runs this whole target to prove the gate needs no model, so
# running the suite again from inside it would not terminate. That test sets the variable.
gate-tests:
ifeq ($(LEANARTICLES_IN_TESTS),1)
	@echo "gate-tests: already inside the suite (test_no_model_in_gates) -- not re-entering"
else
	LEANARTICLES_LLM=cassette LEANARTICLES_LLM_CMD=false \
	  $(PY) -m unittest discover -s tests -t . -q
endif

# The Lean library's own gate: lean/, GFNBoundsLean absorbed in-tree (DEC-157, T-gfn-absorb).
# FREEZE=1 (DEC-2) is retired (DEC-131); gate-registers fails if it is still set, and this target
# then only records the commit it would have checked.
lib-check:
ifeq ($(LEANARTICLES_SKIP_LIB),1)
	@echo "lib-check: skipped (LEANARTICLES_SKIP_LIB=1, set only by tests/test_no_model_in_gates.py: the library gate builds Lean and calls no model)"
else ifeq ($(FREEZE),1)
	@echo "lib-check: FREEZE=1 — skipped at $$(git rev-parse --short HEAD) (DEC-2, retired by DEC-131)"
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

# The public mirror LBrunswic/MathAtlas (DEC-203, DEC-207): filtered main and the atlas on Pages.
# Not a gate; needs git filter-repo ($$GIT_FILTER_REPO) and push rights.
mirror:
	$(PY) tools/public_mirror.py push

# The test suite on its own, verbosely.
test:
	LEANARTICLES_LLM=cassette LEANARTICLES_LLM_CMD=false $(PY) -m unittest discover -s tests -t . -v

# The double DAG of the one pair on this host where both halves exist (read-only on both).
doubledag:
	bash tools/doubledag_gfnbounds.sh

# Every gate has a fixture that makes it fail; selftest fails if one passes on its fixture.
selftest:
	$(PY) tools/selftest.py
