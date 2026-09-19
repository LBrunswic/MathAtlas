#!/usr/bin/env bash
# One word changed in labeled/ (not a \label) must fail.
set -u
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/syracuse" "$T/paper"; chmod -R u+w "$T/paper"
sed -i '0,/cycle/s/cycle/cycl/' "$T/paper/legacy/labeled/syracuse.tex"
python3 "$LEANARTICLES_HUB/tools/legacy_check.py" --paper "$T/paper"; s=$?
rm -rf "$T"; exit $s
