# The progress report of the ETT programme of 2026-11-21.
#
#   make         regenerate generated/ from commit REV (reports/programme/numbers.py), then build
#                report.pdf (latexmk -lualatex, as reports/status-2026-11)
#   make check   the build, then: a second generation into a temporary directory compared byte for
#                byte with generated/; a second PDF build in a temporary copy compared byte for
#                byte with report.pdf; zero undefined references and zero missing glyphs in
#                report.log; no run of words shared with a legacy draft (numbers.py --prose)
#   make clean   latexmk -C: removes the LaTeX outputs, report.pdf included (sources and generated/ stay)
#
# REV pins the commit the figures are read from, so the report is reproducible whatever the shared
# checkout holds later; `make REV=<sha>` regenerates it for another commit. SOURCE_DATE_EPOCH is
# REV's commit time: the PDF's dates and /ID are functions of REV, not of the build.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
REV ?= 963b755
EPOCH := $(shell git log -1 --format=%ct $(REV))
TEX := SOURCE_DATE_EPOCH=$(EPOCH) FORCE_SOURCE_DATE=1 latexmk -lualatex -interaction=nonstopmode -halt-on-error
NUMBERS := python3 ../numbers.py

.PHONY: all numbers pdf check clean
all: pdf

numbers:
	$(NUMBERS) . --rev $(REV)

pdf: numbers
	$(TEX) report.tex > /dev/null
	@echo "report: report.pdf ($$(wc -c < report.pdf) bytes, sha256 $$(sha256sum report.pdf | cut -c1-16))"

check: pdf
	set -e; t=$$(mktemp -d); trap 'rm -rf "$$t"' EXIT; \
	$(NUMBERS) "$$t" --rev $(REV) > /dev/null; \
	diff -r generated "$$t/generated"; \
	echo "report: two generations of generated/, same bytes ($$(ls generated | wc -l) files)"; \
	cp report.tex preamble.tex "$$t/"; \
	(cd "$$t" && $(TEX) report.tex > /dev/null); \
	cmp report.pdf "$$t/report.pdf"; \
	echo "report: two builds of report.pdf, same bytes (sha256 $$(sha256sum report.pdf | cut -c1-16))"
	@set -e; u=$$(grep -c -E "(Reference|Citation) .* undefined|There were undefined" report.log || true); \
	g=$$(grep -c "Missing character" report.log || true); \
	echo "report: report.log: $$u undefined reference line(s), $$g missing glyph line(s)"; \
	test "$$u" = 0 && test "$$g" = 0
	$(NUMBERS) --prose report.tex generated/*.tex

clean:
	latexmk -C report.tex
