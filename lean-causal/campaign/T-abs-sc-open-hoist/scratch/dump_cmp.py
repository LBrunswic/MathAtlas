# Compare two constant dumps of T-abs-sc-open-hoist (scratch/Dump.lean; kb/0063).
# Usage: python3 -I dump_cmp.py BEFORE AFTER
# Prints: counts, names removed/added, constants whose module changed (with the expected-move
# check), and every field difference other than the module (type hash, telescope, levels, value
# hash, ...). The moved declarations and the re-proved values are listed in EXPECTED_* below; a
# difference outside them is printed under UNEXPECTED.
import sys

FIELDS = ["name", "module", "kind", "levels", "typehash", "telescope", "valuehash", "red", "prot",
          "nc", "internal"]

# full name prefix -> (module before, module after); auxiliary constants (`._simp_1_1`, `.match_1`,
# `.eq_1`, ...) move with their parent (kb/0066), so the prefix test covers them.
EXPECTED_MOVES = {
    # (a)
    "Causal.Causality.subset_Jplus_top_inter_Jminus_top": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.causallyConvexIn_Jplus_top_inter_Jminus_top": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.causallyConvexIn_top_iff": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.CausallyConvexIn.Jplus_top_inter_Jminus_top_subset": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.exists_opens_causallyConvexIn_of_isOpen_hull": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_hull": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_Jplus_Jminus": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.CausallyOpen.isOpen_Jplus_top_Jminus_top": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.stronglyCausalOpen_iff_stronglyCausal_of_causallyOpen": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.GloballyHyperbolic.stronglyCausalOpen_of_isOpen_Jplus_Jminus": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.StronglyCausal.exists_not_isOpen_hull": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    "Causal.Causality.StronglyCausal.not_causallyOpen_of_not_stronglyCausalOpen": ("Causal.SCOpenWithoutTarentin", "Causal.StrongCausalityHull"),
    # (b)
    "Causal.IsEMorphismOn.chronalCurveOn_comp": ("Causal.Model.FlatSpaceCylinder", "Causal.CauchyExtension"),
    "Causal.Causality.ChronalHomotopyOn.homotopicRel": ("Causal.Model.FlatSpaceCylinder", "Causal.TimelikeHomotopy"),
    # (d)
    "Causal.IsEMorphismOn.pastInextensible_invComp": ("Causal.FlrwType", "Causal.CauchyExtension"),
    "Causal.IsSpacetimeExtension.isEMorphismOn": ("Causal.FlrwType", "Causal.C0ExtensionSkeleton"),
    # (e)
    "Causal.Causality.IsCauchySurfaceOn.mem_Jplus_union_Jminus": ("Causal.FlrwTypeClosedAmbient", "Causal.CurvesExtendSecondCountable"),
}
# (e): the two re-proved twins; their value may change, nothing else.
EXPECTED_VALUE_CHANGES = {
    "Causal.Causality.splitBy_of_t1_secondCountable",
    "Causal.Causality.IsCauchySurface.cover_of_t1_secondCountable",
}


def parent(name):
    for p in EXPECTED_MOVES:
        if name == p or name.startswith(p + "."):
            return p
    for p in EXPECTED_VALUE_CHANGES:
        if name == p or name.startswith(p + "."):
            return p
    return None


def load(path):
    d, dup = {}, 0
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if f[0] in d:
            dup += 1
        d.setdefault(f[0], []).append(f)
    return d, dup


a, da = load(sys.argv[1])
b, db = load(sys.argv[2])
print("entries", sum(len(v) for v in a.values()), sum(len(v) for v in b.values()),
      "names", len(a), len(b), "dups", da, db)
removed = sorted(set(a) - set(b))
added = sorted(set(b) - set(a))
print("removed:", removed)
print("added:", added)
unexpected = []
for n in removed + added:
    unexpected.append(("removed" if n in a else "added", n))
moved, diffs = [], []
for n in sorted(set(a) & set(b)):
    ra, rb = sorted(a[n]), sorted(b[n])
    ma, mb = {r[1] for r in ra}, {r[1] for r in rb}
    if ma != mb:
        moved.append((n, sorted(ma), sorted(mb)))
        p = parent(n)
        if p is None or p not in EXPECTED_MOVES or (sorted(ma), sorted(mb)) != ([EXPECTED_MOVES[p][0]], [EXPECTED_MOVES[p][1]]):
            unexpected.append(("module", n, sorted(ma), sorted(mb)))
    fa = sorted(tuple(r[2:]) for r in ra)
    fb = sorted(tuple(r[2:]) for r in rb)
    if fa != fb:
        for x, y in zip(fa, fb):
            for i, (u, v) in enumerate(zip(x, y)):
                if u != v:
                    diffs.append((n, FIELDS[i + 2], u, v))
                    p = parent(n)
                    if not (FIELDS[i + 2] == "valuehash" and p in EXPECTED_VALUE_CHANGES):
                        unexpected.append(("field", n, FIELDS[i + 2], u, v))
        if len(fa) != len(fb):
            diffs.append((n, "count", len(fa), len(fb)))
            unexpected.append(("count", n))
print("moved module:", len(moved))
for m in moved:
    print("  ", m)
print("field diffs:", len(diffs))
for d in diffs:
    print("  ", d)
# every expected move happened
missing = [p for p in EXPECTED_MOVES if p not in {m[0] for m in moved}]
print("expected moves not seen:", missing)
print("UNEXPECTED:", len(unexpected))
for u in unexpected:
    print("  ", u)
