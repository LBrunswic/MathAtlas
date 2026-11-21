#!/usr/bin/env bash
# `tools/ladder.py check` must fail on each breakage of breakages.py (one per rule T-tool-ladder-py
# added: standing words, unknown keys and tables, namespace-exact names, conjunctive `at`, labels
# against papers/ett's ledger, sorts, `fails` with a list `from`, [[transfer]]), each applied to a
# copy of programme/ladder.toml in a temporary directory, never in the tree. The unbroken copy must
# pass first (else the fixture proves nothing: exit 0). Exit non-zero only if every breakage fails.
set -u
set -o pipefail
H="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}"
F="$H/tools/fixtures/ladder/breakages.py"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cp "$H/programme/ladder.toml" "$T/ladder.toml"
python3 -B "$H/tools/ladder.py" check --file "$T/ladder.toml" > "$T/base.out" \
  || { echo "ladder fixture: the unbroken copy fails: $(tail -n 1 "$T/base.out")"; exit 0; }
names=$(python3 -B "$F" --list) || { echo "ladder fixture: no breakage list"; exit 0; }
passed=0
for n in $names; do
  python3 -B "$F" "$T/ladder.toml" "$n" "$T/$n.toml" || { echo "ladder fixture: breakage $n not built"; exit 0; }
  if python3 -B "$H/tools/ladder.py" check --file "$T/$n.toml" > "$T/$n.out"; then
    echo "ladder fixture: $n PASSED the check: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  else
    echo "ladder fixture: $n -> $(grep -m 1 -v '^ladder: [0-9]* properties' "$T/$n.out")"
  fi
done
[ "$passed" -eq 0 ] && { echo "ladder fixture: every breakage fails the check"; exit 1; }
exit 0
