#!/usr/bin/env bash
# A paper directory with no ledger.toml (nobody counts it) must fail the fan-out.
set -u
T=$(mktemp -d); mkdir -p "$T/papers/uncounted"; cp "$LEANARTICLES_HUB/hub.toml" "$T/"
LEANARTICLES_ROOT="$T" python3 "$LEANARTICLES_HUB/tools/papers_check.py"; s=$?
rm -rf "$T"; exit $s
