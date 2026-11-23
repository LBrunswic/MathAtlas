"""No same-side pair from 1, 2 or 3 properties is derived only through the dual rules (the SCOPE
claim of Causal.Ladder.Dual), in dual_closure.py's model. python3 -I same_side.py"""
import importlib.util
import itertools
import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "dc", os.path.join(HERE, "..", "T-tac-ladder-dual", "dual_closure.py"))
dc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dc)
data, edges, ids, two, form = dc.setup()
bad, n = [], 0
for k in (1, 2, 3):
    for src in itertools.combinations(ids, k):
        base = dc.ld._saturate(src, edges)
        for s in (0, 1):
            n += 1
            clo = dc.close({(a, s) for a in src}, edges, two)
            extra = {x for x, t in clo if t == s} - base
            if extra:
                bad.append((src, s, sorted(extra)))
print(len(ids), "properties,", n, "premise sets (each side):", len(bad), "with a same-side detour")
for b in bad[:20]:
    print(" ", b)
