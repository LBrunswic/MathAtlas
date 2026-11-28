#!/usr/bin/env bash
# `tools/import_gate.py check` must fail on each breakage of import_breakages.py (one per rule), each built
# as a miniature hub in a temporary directory, never in the tree, and must name the rule it was
# built to break. The unbroken miniature hub must pass first (else the fixture proves nothing:
# exit 0). Exit non-zero only if every breakage fails the check with its rule.
set -u
set -o pipefail
H="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}"
F="$H/tools/fixtures/import-gate/import_breakages.py"
G="$H/tools/import_gate.py"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir "$T/base"
python3 -B "$F" "$T/base" || { echo "import-gate fixture: the base hub not built"; exit 0; }
python3 -B "$G" check --hub "$T/base" --tiers "$T/base/tiers.toml" > "$T/base.out" \
  || { echo "import-gate fixture: the unbroken hub fails: $(tail -n 1 "$T/base.out")"; exit 0; }
list=$(python3 -B "$F" --list) || { echo "import-gate fixture: no breakage list"; exit 0; }
passed=0
while read -r n rule; do
  mkdir "$T/$n"
  python3 -B "$F" "$T/$n" "$n" || { echo "import-gate fixture: breakage $n not built"; exit 0; }
  if python3 -B "$G" check --hub "$T/$n" --tiers "$T/$n/tiers.toml" > "$T/$n.out"; then
    echo "import-gate fixture: $n PASSED the check: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  elif ! grep -q "^$rule " "$T/$n.out"; then
    echo "import-gate fixture: $n failed, but not by $rule: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  else
    echo "import-gate fixture: $n -> $(grep -m 1 "^$rule " "$T/$n.out")"
  fi
done <<< "$list"
[ "$passed" -eq 0 ] && { echo "import-gate fixture: every breakage fails the check"; exit 1; }
exit 0
