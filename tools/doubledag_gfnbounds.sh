#!/usr/bin/env bash
# The double DAG of the GFN pair: the draft `~/Dropbox/GFN Bounds` against the Lean library
# `lean/` (GFNBoundsLean, absorbed in-tree by DEC-157). Read-only on both. The first run
# (2026-09-20, the submodule under the DEC-2 freeze) is pinned in reports/doubledag/gfnbounds/
# 2026-09-20/ as a dated measurement (DEC-199); this script regenerates the current one.
#
# It is the only pair on this host where both halves of the double DAG exist, so it is where the
# tool is measured. The artifacts land in reports/doubledag/gfnbounds/ and are committed.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); HUB=$(dirname "$HERE")
DRAFT="${GFN_DRAFT:-$HOME/Dropbox/GFN Bounds}"
OUT="$HUB/reports/doubledag/gfnbounds"
LEDGER="$DRAFT/formalization-ledger.json"
FACTS="$HUB/lean/docs/lean-facts.json"
MAP="$HUB/lean/paper-map.json"
for f in "$LEDGER" "$FACTS" "$MAP"; do
  [ -f "$f" ] || { echo "doubledag_gfnbounds: missing $f" >&2; exit 2; }
done
mkdir -p "$OUT"
python3 "$HERE/doubledag.py" build  --ledger "$LEDGER" --facts "$FACTS" --map "$MAP" -o "$OUT/doubledag.json"
python3 "$HERE/doubledag.py" report --ledger "$LEDGER" --facts "$FACTS" --map "$MAP" -o "$OUT/DOUBLEDAG.md"
python3 "$HERE/doubledag.py" dot    --ledger "$LEDGER" --facts "$FACTS" --map "$MAP" -o "$OUT/coupled.dot"
command -v dot >/dev/null && dot -Tsvg "$OUT/coupled.dot" -o "$OUT/coupled.svg" || true
echo "doubledag_gfnbounds: wrote $OUT"
