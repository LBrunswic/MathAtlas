#!/usr/bin/env bash
# `tools/restate.py check --file` must fail on each breakage of restate_breakages.py (one per rule),
# each applied to a copy of papers/gx's restatement register in a temporary directory, never in the
# tree. The unbroken copy must pass first (else the fixture proves nothing: exit 0). Exit non-zero
# only if every breakage fails the check.
set -u
set -o pipefail
H="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}"
F="$H/tools/fixtures/restate/restate_breakages.py"
S=gx
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cp "$H/papers/$S/certificate/restatements.toml" "$T/base.toml"
python3 -B "$H/tools/restate.py" check "$S" --file "$T/base.toml" > "$T/base.out" \
  || { echo "restate fixture: the unbroken copy fails: $(tail -n 1 "$T/base.out")"; exit 0; }
names=$(RESTATE_FIXTURE_SLUG=$S python3 -B "$F" --list) || { echo "restate fixture: no breakage list"; exit 0; }
passed=0
for n in $names; do
  python3 -B "$F" "$S" "$n" "$T/$n.toml" || { echo "restate fixture: breakage $n not built"; exit 0; }
  if python3 -B "$H/tools/restate.py" check "$S" --file "$T/$n.toml" > "$T/$n.out"; then
    echo "restate fixture: $n PASSED the check: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  else
    echo "restate fixture: $n -> $(grep -m 1 -v '^restate: [0-9]* entries' "$T/$n.out")"
  fi
done
[ "$passed" -eq 0 ] && { echo "restate fixture: every breakage fails the check"; exit 1; }
exit 0
