#!/usr/bin/env bash
# Three breakages, each must make `ledger.py check` fail (exit non-zero only if all do):
#  1. removing one \label leaves an unlabeled statement;
#  2. a curated decl carrying prose ("(related, …) Causal.foo") is not a Lean name
#     (T-ett-curation-decls: such a decl was found by its last component and passed);
#  3. a configured proof macro that opens no proof (T-barbot-proof-macros: a misspelled macro
#     would silently drop every proof and edge of the paper).
set -u
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/syracuse" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/legacy/labeled/syracuse.tex" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p, encoding="utf-8").read()
m = re.search(r"\\label\{theo:[^}]*\}", s); assert m, "no theorem label to remove"
open(p, "w", encoding="utf-8").write(s[:m.start()] + s[m.end():])
PY
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s1=$?
rm -rf "$T"

T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/ett" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/ledger/ledger.toml" "$LEANARTICLES_HUB/lean-causal" <<'PY'
import re, sys
p, root = sys.argv[1], sys.argv[2]; s = open(p, encoding="utf-8").read()
t = re.sub(r'(\[lean\][^\[]*?\nroot = )"[^"]*"', lambda m: m.group(1) + '"' + root + '"', s, count=1, flags=re.S)
assert t != s, "no [lean] root to repoint"; open(p, "w", encoding="utf-8").write(t)
PY
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" build >/dev/null || { rm -rf "$T"; exit 0; }
python3 - "$T/paper/ledger/ledger.json" <<'PY'
import json, sys
p = sys.argv[1]; L = json.load(open(p, encoding="utf-8"))
s = next(s for s in L["statements"] if s.get("decls"))
s["decls"][0] = "(related, a prose prefix) " + s["decls"][0]
json.dump(L, open(p, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
PY
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s2=$?
rm -rf "$T"
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/barbot" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/ledger/ledger.toml" "$LEANARTICLES_HUB/lean-causal" <<'PY'
import re, sys
p, root = sys.argv[1], sys.argv[2]; s = open(p, encoding="utf-8").read()
t = re.sub(r'(\[lean\][^\[]*?\nroot = )"[^"]*"', lambda m: m.group(1) + '"' + root + '"', s, count=1, flags=re.S)
assert t != s, "no [lean] root to repoint"
u = t.replace('["\\\\preua", "\\\\fin"]', '["\\\\preuva", "\\\\fin"]', 1)
assert u != t, "no proof macro to misspell"; open(p, "w", encoding="utf-8").write(u)
PY
# Build first, so that only the macro rule (not drift) can make check fail.
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" build >/dev/null || { rm -rf "$T"; exit 0; }
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s3=$?
rm -rf "$T"
[ "$s1" -ne 0 ] && [ "$s2" -ne 0 ] && [ "$s3" -ne 0 ] && exit 1
exit 0
