#!/usr/bin/env bash
# The rename tool's resolution check (tools/rename_tool.py) must fail on each breakage of
# minihub.py, each built as a miniature hub in a temporary directory, never in the tree, and must
# name the rule it was built to break (`dangling` from `check`, `regression` from `apply`). The
# unbroken miniature hub must pass `check`, and `apply` of its map must pass too, first (else the
# fixture proves nothing: exit 0). Exit non-zero only if every breakage fails with its rule.
set -u
set -o pipefail
H="${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}"
F="$H/tools/fixtures/rename/minihub.py"
G="$H/tools/rename_tool.py"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir "$T/base"
python3 -B "$F" "$T/base" || { echo "rename fixture: the base hub not built"; exit 0; }
python3 -B "$G" check --target "$T/base" > "$T/base.out" \
  || { echo "rename fixture: the unbroken hub fails check: $(tail -n 1 "$T/base.out")"; exit 0; }
cp -a "$T/base" "$T/base-applied"
python3 -B "$G" apply "$T/base/rename.toml" --target "$T/base-applied" > "$T/base-apply.out" \
  || { echo "rename fixture: apply fails on the unbroken hub: $(tail -n 1 "$T/base-apply.out")"; exit 0; }
list=$(python3 -B "$F" --list) || { echo "rename fixture: no breakage list"; exit 0; }
passed=0
while read -r n rule how; do
  mkdir "$T/$n"
  python3 -B "$F" "$T/$n" "$n" || { echo "rename fixture: breakage $n not built"; exit 0; }
  if [ "$how" = apply ]; then
    cmd=(python3 -B "$G" apply "$T/$n/rename.toml" --target "$T/$n")
  else
    cmd=(python3 -B "$G" check --target "$T/$n")
  fi
  if "${cmd[@]}" > "$T/$n.out"; then
    echo "rename fixture: $n PASSED $how: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  elif ! grep -q "^$rule " "$T/$n.out"; then
    echo "rename fixture: $n failed, but not by $rule: $(tail -n 1 "$T/$n.out")"; passed=$((passed + 1))
  else
    echo "rename fixture: $n -> $(grep -m 1 "^$rule " "$T/$n.out")"
  fi
done <<< "$list"
[ "$passed" -eq 0 ] && { echo "rename fixture: every breakage fails with its rule"; exit 1; }
exit 0
