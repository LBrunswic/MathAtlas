#!/usr/bin/env bash
# The generalised ledger must reproduce the GFN Bounds ledger byte for byte. Read-only on the
# source repository: outputs land in a tmp dir seeded with the committed JSON (curated fields
# carry over exactly as the original tool carries them over). Exit 1 on any difference.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
SRC="/home/maxbrain/Dropbox/GFN Bounds"
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
cp "$SRC/formalization-ledger.json" "$OUT/"
sed "s|__OUT__|$OUT|" "$HERE/fixtures/regression/gfnbounds.toml" > "$OUT/ledger.toml"
python3 "$HERE/ledger.py" -c "$OUT/ledger.toml" build > "$OUT/build.log"
status=0
# The committed ledger names the commits it was built at; HEAD has moved since, so the commit
# ids are the one permitted difference (the plan's "except the path fields"). Everything else
# -- every row, every digest, every table -- must agree.
norm() { sed -E 's/("git_commit": ")[0-9a-f]+"/\1X"/; s/ at `[0-9a-f]{7,}`/ at `X`/g' "$1"; }
for f in formalization-ledger.json FORMALIZATION-LEDGER.md formalization-dag.dot; do
  if cmp -s <(norm "$SRC/$f") <(norm "$OUT/$f"); then echo "identical (modulo commit ids): $f"
  else echo "DIFFERS: $f"; (diff <(norm "$SRC/$f") <(norm "$OUT/$f") || true) | head -"${DIFF_LINES:-20}"; status=1; fi
done
exit $status
