# The dependency atlas: regenerate from the ledgers, hub.toml, roadmap/roadmap.toml and the EGF programme's
# roadmap and corrections register (papers/egf/programme)
# (run `make ledgers` at the hub root first). `make LOGS=<dir>` refreshes the declaration counts
# from `make -C <pkg> check` logs named check-<pkg>.log, one per package of hub.toml's lib table;
# a package with no cached count yet is drawn as "not swept", never given a number.
#
# The Lean overlay is read from the committed lean/edges-<paper>.json; the default target never
# runs Lean. Refresh it explicitly:
#   make lean-facts   RUNS LEAN, read-only: `lake env lean --stdin` in each package over its built
#                     oleans, one package at a time (lean_facts.lean); writes lean/facts-<pkg>.json,
#                     a local cache that git ignores
#   make lean-edges   no Lean: tools/doubledag.py over the cached facts and the current ledgers;
#                     writes lean/edges-<paper>.json (committed)
#   make lean         both, in that order
#   make lean-status  is each edge file still what `make lean` would write?
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
LOGS ?=

atlas.html: extract.py build.py lean_edges.py template.html hub.toml ../../roadmap/roadmap.toml \
            ../../papers/egf/programme/roadmap.toml ../../papers/egf/programme/corrections.toml $(wildcard lean/edges-*.json)
	python3 extract.py data.json 2>/dev/null
	python3 build.py $(if $(LOGS),--logs $(LOGS))
	{ echo '<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><style>:root{color-scheme:light}body{margin:0;font:14px system-ui}[hidden]{display:none!important}</style></head><body>'; cat atlas.body.html; echo '</body></html>'; } > atlas.html
	rm -f data.json atlas.body.html

.PHONY: lean lean-facts lean-edges lean-status
lean: lean-facts
	$(MAKE) lean-edges

lean-facts:
	python3 lean_edges.py facts

lean-edges:
	python3 lean_edges.py edges

lean-status:
	python3 lean_edges.py status
