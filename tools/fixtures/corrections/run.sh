#!/usr/bin/env bash
# `tools/corrections.py check` must fail on each breakage of breakages.py (one per rule), each
# applied to a copy of papers/egf/programme/corrections.toml in a temporary directory, never in the
# tree. The unbroken copy must pass first (else the fixture proves nothing: exit 0). Exit non-zero
# only if every breakage fails the check.
set -u
set -o pipefail
H="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}"
F="$H/tools/fixtures/corrections/breakages.py"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cp "$H/papers/egf/programme/corrections.toml" "$T/corrections.toml"
python3 -B "$H/tools/corrections.py" check --file "$T/corrections.toml" > "$T/base.out" \
  || { echo "corrections fixture: the unbroken copy fails: $(tail -n 1 "$T/base.out")"; exit 0; }
names=$(python3 -B "$F" --list) || { echo "corrections fixture: no breakage list"; exit 0; }
passed=0
for n in $names; do
  python3 -B "$F" "$T/corrections.toml" "$n" "$T/$n.toml" || { echo "corrections fixture: breakage $n not built"; exit 0; }
  if python3 -B "$H/tools/corrections.py" check --file "$T/$n.toml" > "$T/$n.out"; then
    echo "corrections fixture: $n PASSED the check: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  else
    echo "corrections fixture: $n -> $(grep -m 1 -v '^corrections: [0-9]* entries' "$T/$n.out")"
  fi
done
[ "$passed" -eq 0 ] && { echo "corrections fixture: every breakage fails the check"; exit 1; }
exit 0
