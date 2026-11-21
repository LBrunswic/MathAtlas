# The ETT programme's blueprint site: regenerate index.html from the programme's files.
#
#   make           build.py over programme/ladder.toml, programme/roadmap.toml, every
#                  papers/*/certificate/binder.toml and the ledgers; writes index.html. Runs no Lean.
#   make check     the build, then a second build to a temporary file compared byte for byte, then
#                  the headless smoke test (smoke.cjs: Chromium through the Playwright in the npx
#                  cache; it fails on any page error and on any click that does not open its panel,
#                  among them every drawn segment of every implication, on its line and 4 px beside
#                  it, and every ∧ junction). Needs the network for the CDN libraries.
#   make smoke     the smoke test alone, on the current index.html. SHOTS=DIR keeps screenshots.
#
# The inputs are many files across the repository (and lean-causal's sources, read for locations),
# so the page is rebuilt every time rather than tracked by make.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
PLAYWRIGHT ?= $(firstword $(wildcard $(HOME)/.npm/_npx/*/node_modules/playwright))
SHOTS ?=

.PHONY: all index.html check twice smoke
all: index.html

index.html:
	python3 build.py

twice: index.html
	t=$$(mktemp --suffix=.html); trap 'rm -f "$$t"' EXIT; \
	python3 build.py --out "$$t" > /dev/null; \
	cmp index.html "$$t"; \
	echo "blueprint: two builds, same bytes (sha256 $$(sha256sum index.html | cut -c1-16), $$(wc -c < index.html) bytes)"

smoke:
	@test -n "$(PLAYWRIGHT)" || { echo "blueprint: no Playwright under ~/.npm/_npx (set PLAYWRIGHT=...)"; exit 1; }
	PLAYWRIGHT="$(PLAYWRIGHT)" SHOTS="$(SHOTS)" node smoke.cjs index.html

check: twice smoke
