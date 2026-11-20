# The dependency atlas: regenerate from the ledgers, hub.toml and roadmap/roadmap.toml
# (run `make ledgers` at the hub root first). `make LOGS=<dir>` refreshes the declaration counts
# from `make -C <pkg> check` logs named check-<pkg>.log.
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c
LOGS ?=

atlas.html: extract.py build.py template.html hub.toml ../../roadmap/roadmap.toml
	python3 extract.py data.json 2>/dev/null
	python3 build.py $(if $(LOGS),--logs $(LOGS))
	{ echo '<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><style>:root{color-scheme:light}body{margin:0;font:14px system-ui}[hidden]{display:none!important}</style></head><body>'; cat atlas.body.html; echo '</body></html>'; } > atlas.html
	rm -f data.json atlas.body.html
