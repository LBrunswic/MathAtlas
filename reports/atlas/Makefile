# The dependency atlas: regenerate from the ledgers (run `make ledgers` at the hub root first).
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

atlas.html: extract.py build.py template.html
	python3 extract.py data.json
	python3 build.py
	{ echo '<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><style>:root{color-scheme:light}body{margin:0;font:14px system-ui}[hidden]{display:none!important}</style></head><body>'; cat atlas.body.html; echo '</body></html>'; } > atlas.html
	rm -f data.json atlas.body.html
