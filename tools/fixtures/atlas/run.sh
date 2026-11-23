#!/usr/bin/env bash
# Three breakages of the built page, each must make `reports/atlas/check.py` fail (exit non-zero only
# if all do):
#  1. a benzecri statement carrying \bzcf{printed}{\ref{...}} raw outside math (T-atlas-tex-text-macros:
#     MathJax expands a paper's macros inside math only, so the panel showed the call raw);
#  2. a gx statement cut inside math, `$\pi_1(\reg(N)` left open, so \reg falls outside math (the
#     1400-character cut before textmode.cut);
#  3. a page with no statement at all.
set -u
HUB=${LEANARTICLES_HUB:-$(cd "$(dirname "$0")/../../.." && pwd)}
A="$HUB/reports/atlas"
T=$(mktemp -d)
python3 - "$A/atlas.html" "$T" <<'PY' || { rm -rf "$T"; exit 0; }
import json, re, sys
page, out = sys.argv[1], sys.argv[2]
s = open(page, encoding="utf-8").read()
m = re.search(r"^const DATA = (.*);$", s, re.M); assert m, "no DATA line"
def write(name, data):
    open(out + "/" + name, "w", encoding="utf-8").write(
        s[:m.start(1)] + json.dumps(data, ensure_ascii=False, separators=(",", ":")) + s[m.end(1):])
d = json.loads(m.group(1))
n = next(n for n in d["benzecri"]["nodes"] if "$" in n["tex"])
assert "bzcf" in d["benzecri"]["macros"], "benzecri defines no \\bzcf"
n["tex"] += "\n(\\bzcf{cf. chap. 1, \\S\\,3, prop. 1}{\\ref{bzcor:c1s3p1c_produit_cercle}})"
write("one.html", d)
d = json.loads(m.group(1))
n = next(n for n in d["gx"]["nodes"] if "\\reg(" in n["tex"])
assert "reg" in d["gx"]["macros"], "gx defines no \\reg"
n["tex"] += " such that $\\pi_1(\\reg(N) …"
write("two.html", d)
d = json.loads(m.group(1))
for p in d:
    d[p]["nodes"] = []
write("three.html", d)
PY
python3 "$A/check.py" "$T/one.html"; s1=$?
python3 "$A/check.py" "$T/two.html"; s2=$?
python3 "$A/check.py" "$T/three.html"; s3=$?
rm -rf "$T"
[ "$s1" -ne 0 ] && [ "$s2" -ne 0 ] && [ "$s3" -ne 0 ] && exit 1
exit 0
