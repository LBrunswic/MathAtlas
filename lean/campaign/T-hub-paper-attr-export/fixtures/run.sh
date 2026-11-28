#!/usr/bin/env bash
# Fixture of the paper export (PAPER-ATTRIBUTE.md §5) in lean/scripts/lean_facts.lean.
#
#     bash lean/campaign/T-hub-paper-attr-export/fixtures/run.sh    # from the hub root, on node1
#
# Exit 0 iff every scenario behaves as expected: the positive export carries exactly the
# expected `paper`/`conjuncts` fields, and each of the three throws fires with its exact message,
# leaves the scenario's docs/lean-facts.json (a sentinel) untouched, and exits non-zero. Requires
# a built lean/ (lake build GFNBounds); builds nothing in the package. The fixture modules are
# compiled with `lean -o` into a temporary directory, and every export runs with that directory
# as its working directory, so nothing reaches lean/.lake, lean/docs or the committed
# lean-facts.json (checked by sha256 at the end).
set -euo pipefail

HUB="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../../.." && pwd)}"
PKG="$HUB/lean"
FIX="$(cd "$(dirname "$0")" && pwd)"
SCRIPT="${LEAN_FACTS_SCRIPT:-$PKG/scripts/lean_facts.lean}"   # override: run against another exporter
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

LP="$(cd "$PKG" && lake env printenv LEAN_PATH)"
LEAN="$(cd "$PKG" && lake env which lean)"
export LEAN_PATH="$TMP/olean:$LP"
committed_before="$(sha256sum "$PKG/docs/lean-facts.json" | cut -d' ' -f1)"
fail=0

[ "$(head -n1 "$SCRIPT")" = "import GFNBounds" ] || { echo "run.sh: $SCRIPT no longer starts with 'import GFNBounds'"; exit 2; }

# Lean resolves a module under the first search-path entry holding its root directory, so the
# fixture oleans cannot sit in a second GFNBounds/ tree: $TMP/olean mirrors the package's built
# GFNBounds/ as symlinks (read-only use; nothing is written through them) and adds the fixtures.
mkdir -p "$TMP/src/GFNBounds/Paper" "$TMP/olean"
cp -rs "$PKG/.lake/build/lib/lean/GFNBounds" "$PKG/.lake/build/lib/lean/GFNBounds.olean" "$TMP/olean/"
for m in AppendixFixA FixB FixC AppendixFixD; do
  [ ! -e "$TMP/olean/GFNBounds/Paper/$m.olean" ] || { echo "run.sh: $m already exists in the package"; exit 2; }
  cp "$FIX/$m.lean" "$TMP/src/GFNBounds/Paper/$m.lean"
  "$LEAN" -R "$TMP/src" -o "$TMP/olean/GFNBounds/Paper/$m.olean" "$TMP/src/GFNBounds/Paper/$m.lean"
done

# driver <name> <prelude file or -> <module>... : a copy of the exporter importing the modules.
driver() {
  local name="$1" prelude="$2"; shift 2
  local dir="$TMP/run-$name"; mkdir -p "$dir/docs"
  { echo "import GFNBounds"; for m in "$@"; do echo "import GFNBounds.Paper.$m"; done
    [ "$prelude" = - ] || cat "$FIX/$prelude"
    tail -n +2 "$SCRIPT"; } > "$dir/lean_facts.lean"
  echo "$dir"
}

# The baseline: the same exporter, no fixture imported.
d="$(driver base -)"
(cd "$d" && "$LEAN" lean_facts.lean) > "$d/out.txt" 2>&1 || { echo "run.sh: FAIL baseline export failed"; cat "$d/out.txt"; exit 1; }
cp "$d/docs/lean-facts.json" "$TMP/baseline.json"

# pos: fixtures A and C (no import between them; one identical pair placed in both).
d="$(driver pos - AppendixFixA FixC)"
if (cd "$d" && "$LEAN" lean_facts.lean) > "$d/out.txt" 2>&1; then
  python3 -I "$FIX/check_positive.py" "$d/docs/lean-facts.json" "$TMP/baseline.json" || fail=1
else
  echo "run.sh: FAIL pos: the export threw"; cat "$d/out.txt"; fail=1
fi

# expect_throw <name> <exact message> <prelude> <module>...
expect_throw() {
  local name="$1" msg="$2" prelude="$3"; shift 3
  local d; d="$(driver "$name" "$prelude" "$@")"
  echo sentinel > "$d/docs/lean-facts.json"
  if (cd "$d" && "$LEAN" lean_facts.lean) > "$d/out.txt" 2>&1; then
    echo "run.sh: FAIL $name: the export did not throw"; fail=1; return
  fi
  if ! grep -qF -- "error: $msg" "$d/out.txt"; then
    echo "run.sh: FAIL $name: expected 'error: $msg', got:"; cat "$d/out.txt"; fail=1; return
  fi
  if [ "$(cat "$d/docs/lean-facts.json")" != sentinel ]; then
    echo "run.sh: FAIL $name: docs/lean-facts.json was written before the throw"; fail=1; return
  fi
  echo "run.sh: $name threw before any write: $(grep -F -- "error: $msg" "$d/out.txt")"
}

expect_throw dup \
  "lean_facts: label 'lem:paperattr_test_export_dup' is placed on two declarations: GFNBounds.Paper.labels and GFNBounds.Paper.validLabel" \
  - AppendixFixA FixB FixC
expect_throw unwalked \
  "lean_facts: label 'lem:paperattr_test_export_unwalked' is placed on GFNBounds.Paper.FixNotWalked.t, which the walk did not emit (declared in the main module)" \
  NotWalked.prelude.lean AppendixFixA FixC
expect_throw glue \
  "paper: conjunctsOf GFNBounds.Paper.FixD.glued: the head Nat.le_of_lt of a leaf is not a project theorem" \
  - AppendixFixA FixC AppendixFixD

committed_after="$(sha256sum "$PKG/docs/lean-facts.json" | cut -d' ' -f1)"
if [ "$committed_before" != "$committed_after" ]; then
  echo "run.sh: FAIL lean/docs/lean-facts.json changed"; fail=1
fi
if [ "$fail" -ne 0 ]; then echo "run.sh: FAIL"; exit 1; fi
echo "run.sh: ok: positive export as expected; the three throws fired, each before any write"
