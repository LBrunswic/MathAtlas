# Which `Causal/<File>.lean:<n>` references of programme/ladder.toml (and of the edited modules'
# own docstrings) point into a file this target edited, and where the line they named is now.
# HEAD's sources are read from /tmp/T-abs-sc-open-hoist/headsrc (git archive HEAD lean-causal/Causal).
# Writes nothing. Run: python3 -I lineref_probe.py
import re, pathlib, difflib
HUB = pathlib.Path("/home/maxbrain/Dropbox/LeanArticles")
OLD = pathlib.Path("/tmp/T-abs-sc-open-hoist/headsrc/lean-causal")
NEW = HUB / "lean-causal"
EDITED = ["SCOpenWithoutTarentin", "Model/FlatSpaceCylinder", "CauchyExtension", "TimelikeHomotopy",
          "ChronalNeighbourBridge", "CurvesExtend", "FlrwType", "C0ExtensionSkeleton",
          "FlrwTypeClosedAmbient", "CurvesExtendSecondCountable", "ErsSecondCountable",
          "CauchySeparation"]
pat = re.compile(r"(?:Causal/)?((?:Model/)?[A-Za-z0-9]+)\.lean:(\d+)")

def linemap(f):
    a = (OLD / "Causal" / f"{f}.lean").read_text(encoding="utf-8").splitlines()
    b = (NEW / "Causal" / f"{f}.lean").read_text(encoding="utf-8").splitlines()
    m = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal":
            for k in range(i2 - i1):
                m[i1 + k + 1] = j1 + k + 1
    return a, m

maps = {f: linemap(f) for f in EDITED}
src = (HUB / "programme" / "ladder.toml").read_text(encoding="utf-8").splitlines()
for no, line in enumerate(src, 1):
    for mm in pat.finditer(line):
        f, n = mm.group(1), int(mm.group(2))
        if f not in maps:
            continue
        a, m = maps[f]
        new = m.get(n)
        if new != n:
            text = a[n - 1].strip()[:70] if n <= len(a) else "?"
            print(f"ladder.toml:{no}: {f}.lean:{n} -> {new if new else 'MOVED/EDITED'}   [{text}]")
