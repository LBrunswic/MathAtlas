#!/usr/bin/env bash
# Removing one \label leaves an unlabeled statement: ledger check must fail.
set -u
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/syracuse" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/legacy/labeled/syracuse.tex" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p, encoding="utf-8").read()
m = re.search(r"\\label\{theo:[^}]*\}", s); assert m, "no theorem label to remove"
open(p, "w", encoding="utf-8").write(s[:m.start()] + s[m.end():])
PY
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s=$?
rm -rf "$T"; exit $s
