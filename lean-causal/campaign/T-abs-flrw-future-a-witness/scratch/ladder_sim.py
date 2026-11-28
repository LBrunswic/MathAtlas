"""In-memory simulation (kb/0276) of the keeper's fourth GH entry for T-lad-record-flrw-future-a.
Reads programme/ladder.toml and lean-causal/Causal; writes nothing outside stdout."""
import copy
import sys

sys.path.insert(0, "/home/maxbrain/Dropbox/LeanArticles/tools")
import ladder  # noqa: E402

data = ladder.load()
idx = ladder.lean_index()
names = set(idx["decls"])
new = [
    "Causal.Causality.iUnion_Iminus_eq_of_dual_pastInextensible",
    "Causal.timelikeLine_posHalfLine_iUnion_Iminus_eq",
    "Causal.timelikeLine_posHalfLine_not_futureBoundaryChart_of_flrwTypeA",
    "Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA",
]
for n in new:
    print("resolves", n, ladder.resolves(n, names), idx["decls"].get(n))
mod = "Causal.FlrwTypeClosedAmbient"
print("imports", idx["imports"][mod])
print("model_path", ladder.model_path(mod, idx["imports"]))
for t in ("Causal.Ladder.Rules", "Causal.Ladder.Dual"):
    print("chain", mod, "->", t, ladder.import_chain(mod, idx["imports"], t))
    print("chain", t, "->", mod, ladder.import_chain(t, idx["imports"], mod))

errs0 = ladder.check(data, names=names)
m0 = ladder.matrix(data)
c0 = ladder._contradictions(data)
n0 = len(data.get("consequence", []))
sim = copy.deepcopy(data)
sim["consequence"].append({
    "at": ["globally_hyperbolic", "tarentin"],
    "statement": "Sbierski 2312.07443 Thm 1.5, (A) alone in a closed ambient, time-reversed: on a "
                 "globally hyperbolic, tarentin M, an open W every future-inextensible chronal curve "
                 "of which has chronological past W in W has a future boundary chart at no point "
                 "(¬ C.FutureBoundaryChart W Ũ p for every open Ũ and every p)",
    "witness": "Causal.Causality.GloballyHyperbolic.not_futureBoundaryChart_of_flrwTypeA",
    "under": "W any open set of M; (A⁻) on W: every future-inextensible chronal curve γ of W "
             "(C.FutureInextensible W, chronal on its segments) has ⋃ t I⁻(γ t, W) = W (hA); no (B), "
             "no future one-connectedness and no causal arc-connectedness of W is asked; ≤_M is closed "
             "through Causal.Causality.GloballyHyperbolic.isClosed_le and antisymmetric through "
             "globally_hyperbolic's IsCausal conjunct; the conclusion refutes the time reversal of "
             "past_boundary_chart (Causal.Causality.FutureBoundaryChart, C.dual.PastBoundaryChart, no "
             "id of its own) at W, for every Ũ and p",
    "standing": ["T2"],
    "status": "checked",
})
errs1 = ladder.check(sim, names=names)
m1 = ladder.matrix(sim)
c1 = ladder._contradictions(sim)
print("check errors before/after", len(errs0), len(errs1))
for e in errs1:
    print("  ", e)
print("matrix cells", len(m0), "changed", sum(1 for k in m0 if m0[k] != m1.get(k)))
print("contradictions before/after", len(c0), len(c1))
print("consequences before/after", n0, len(sim["consequence"]))
