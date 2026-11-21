# Faithfulness check of T-ett-gxsingular-dec25 (kb/0060): each gx source range, renamed GX.x -> Causal.x,
# must be found as one contiguous verbatim block of its port; no ETT-prefixed bold mark in the first
# 4000 characters; no sorry and no GX. name in code. Run: python3 -I check_port.py
import re
GX = "/home/maxbrain/Dropbox/LeanArticles/lean-gx/GX/"
P = "/home/maxbrain/Dropbox/LeanArticles/lean-causal/scaffold/CausalScaffold/"
NAME = re.compile(r"(?<![\w.])GX\.(?=[A-Za-z_])")
def ren(l):
    if l == "namespace GX": return "namespace Causal"
    if l == "end GX": return "end Causal"
    return NAME.sub("Causal.", l)
def find(port, block):
    n = len(block)
    return [i+1 for i in range(len(port)-n+1) if port[i:i+n] == block]
checks = [("Topology/Portly.lean", "Port/Portly.lean", [(72, 646)]),
          ("Singular/Atlas.lean", "Port/SingularAtlas.lean", [(150, 1812)]),
          ("Branched/Basic.lean", "GXSingularDEC25.lean", [(728, 739)]),
          ("SingularII/Tame.lean", "GXSingularDEC25.lean", [(145, 147), (149, 182)])]
for srcf, portf, ranges in checks:
    src = open(GX + srcf, encoding="utf-8").read().split("\n")
    port = open(P + portf, encoding="utf-8").read().split("\n")
    for a, b in ranges:
        block = [ren(l) for l in src[a-1:b]]
        print(f"{srcf} l.{a}-{b} ({b-a+1} lines) -> {portf}: at line(s) {find(port, block)}; renamed lines: {sum(1 for l in src[a-1:b] if ren(l)!=l)}")
for f in ["Port/Portly.lean", "Port/SingularAtlas.lean", "GXSingularDEC25.lean"]:
    t = open(P + f, encoding="utf-8").read()
    marks = re.findall(r"\*\*`((?:theo|lem|prop|cor|def|defi|rem|propri|ex|cex|cexemple):[A-Za-z_0-9.\-]+)`\*\*", t[:4000])
    code = re.sub(r"/-.*?-/", "", t, flags=re.S); code = re.sub(r"--.*", "", code)
    print(f, "| marks in head:", marks, "| sorry in code:", len(re.findall(r"(?<![\w'])sorry(?![\w'])", code)), "| GX. in code:", re.findall(r"(?<![\w.])GX\.[A-Za-z_]+", code), "| imports:", re.findall(r"^import .*", t, re.M))
