#!/usr/bin/env bash
# A committed doubledag.json that is not what a build would write must fail `doubledag check`.
set -u
T=$(mktemp -d)
mkdir -p "$T/paper/ledger" "$T/paper/doubledag" "$T/lean/docs"
cat > "$T/lean/docs/lean-facts.json" <<'JSON'
{"declarations": {"A.main": {"kind":"theorem","module":"M","line":1,"type":"True","doc":"",
 "uses_value":["B.main"],"uses_type":[],"axioms":[],"nonstandard_axioms":[],"uses_external":0},
 "B.main": {"kind":"theorem","module":"M","line":2,"type":"True","doc":"",
 "uses_value":[],"uses_type":[],"axioms":[],"nonstandard_axioms":[],"uses_external":0}}}
JSON
cat > "$T/paper/ledger/ledger.json" <<'JSON'
{"paper":{},"lean":{},"statements":[
 {"label":"theo:a","kind":"theorem","title":"A","number":"","file":"p.tex","line":1,
  "tex_span":[1,2],"proof":null,"proof_span":null,"twin":null,"twin_of":null,"cites":[],
  "deps":[],"decls":["A.main"],"lean_stated":"strict","lean_proved":"closed"},
 {"label":"lem:b","kind":"lemma","title":"B","number":"","file":"p.tex","line":3,
  "tex_span":[3,4],"proof":null,"proof_span":null,"twin":null,"twin_of":null,"cites":[],
  "deps":[],"decls":["B.main"],"lean_stated":"strict","lean_proved":"closed"}]}
JSON
printf '[paper]\nroot = "."\ndocument = "p.tex"\n\n[lean]\nroot = "../../lean"\nstrict = ["X"]\n\n[output]\ndir = "."\n' > "$T/paper/ledger/ledger.toml"
# a stale artifact: the edge the build finds is missing from it
echo '{"projection":"principal","summary":{},"nodes":[],"edges":[]}' > "$T/paper/doubledag/doubledag.json"
python3 "$LEANARTICLES_HUB/tools/doubledag.py" check --paper "$T/paper"; s=$?
rm -rf "$T"; exit $s
