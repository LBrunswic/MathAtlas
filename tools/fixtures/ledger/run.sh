#!/usr/bin/env bash
# Five breakages, each must make `ledger.py check` fail (exit non-zero only if all do):
#  1. removing one \label leaves an unlabeled statement;
#  2. a curated decl carrying prose ("(related, …) Causal.foo") is not a Lean name
#     (T-ett-curation-decls: such a decl was found by its last component and passed);
#  3. a configured proof macro that opens no proof (T-barbot-proof-macros: a misspelled macro
#     would silently drop every proof and edge of the paper).
#  4. a proof title that \ref's no statement (T-texgraph-proof-titles: such a proof falls back to the
#     most recent statement without a proof, silently the wrong row).
#  5. a curated decl moved into another namespace, with the same last component (T-ledger-decl-
#     fullname: decl_line matched the last component only, so BTZAxioms.K_neq_I passed against
#     E0.K_neq_I).
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
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/yamabe" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/ledger/ledger.toml" "$LEANARTICLES_HUB/lean-yamabe" "$T/paper/legacy/labeled/Yamabegap.tex" <<'PY'
import re, sys
p, root, tex = sys.argv[1], sys.argv[2], sys.argv[3]; s = open(p, encoding="utf-8").read()
t = re.sub(r'(\[lean\][^\[]*?\nroot = )"[^"]*"', lambda m: m.group(1) + '"' + root + '"', s, count=1, flags=re.S)
assert t != s, "no [lean] root to repoint"; open(p, "w", encoding="utf-8").write(t)
x = open(tex, encoding="utf-8").read()
y = x.replace("[Proof of Theorem~\\ref{thm:upper-bound}]", "[Proof of Theorem~\\ref{thm:upper-bnd}]", 1)
assert y != x, "no titled proof to break"; open(tex, "w", encoding="utf-8").write(y)
PY
# Build first, so that only the proof-title rule (not drift) can make check fail.
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" build >/dev/null || { rm -rf "$T"; exit 0; }
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s4=$?
rm -rf "$T"
T=$(mktemp -d); cp -r "$LEANARTICLES_HUB/papers/syracuse" "$T/paper"; chmod -R u+w "$T/paper"
python3 - "$T/paper/ledger/ledger.toml" "$LEANARTICLES_HUB/lean-syracuse" <<'PY'
import re, sys
p, root = sys.argv[1], sys.argv[2]; s = open(p, encoding="utf-8").read()
t = re.sub(r'(\[lean\][^\[]*?\nroot = )"[^"]*"', lambda m: m.group(1) + '"' + root + '"', s, count=1, flags=re.S)
assert t != s, "no [lean] root to repoint"; open(p, "w", encoding="utf-8").write(t)
PY
# Build first, so that only the full-name rule (not drift) can make check fail.
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" build >/dev/null || { rm -rf "$T"; exit 0; }
python3 - "$T/paper/ledger/ledger.json" <<'PY'
import json, sys
p = sys.argv[1]; L = json.load(open(p, encoding="utf-8"))
s = next(s for s in L["statements"] if any(d.count(".") >= 1 for d in s.get("decls", [])))
i = next(i for i, d in enumerate(s["decls"]) if d.count(".") >= 1)
head, last = s["decls"][i].rsplit(".", 1)
s["decls"][i] = head + ".MovedByFixture." + last
json.dump(L, open(p, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
PY
python3 "$LEANARTICLES_HUB/tools/ledger.py" -c "$T/paper/ledger/ledger.toml" check; s5=$?
rm -rf "$T"
[ "$s1" -ne 0 ] && [ "$s2" -ne 0 ] && [ "$s3" -ne 0 ] && [ "$s4" -ne 0 ] && [ "$s5" -ne 0 ] && exit 1
exit 0
