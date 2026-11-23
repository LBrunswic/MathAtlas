"""Compare the before-dump (Dump.lean, HEAD's oleans) with the after-dump (DumpSubst.lean).

usage: python3 -I dump_subst_cmp.py before.txt after-subst.txt

1. Raw: by name, as dump_cmp.py (T-tac-curves-fact-rule): removed, added, field differences.
2. Substituted (kb/0063 for a rename): every after-constant is keyed by its name with the renamed
   prefixes mapped back to the old ones, and its type and value hashes are taken after the same
   substitution inside the terms. The deprecated wrappers (the after-constants that carry a
   deprecation entry) are set aside: they are the added aliases. Every other after-constant must
   then match a before-constant field for field, and every before-constant must be matched.
"""
import sys

FIELDS = ["name", "module", "kind", "levels", "typehash", "telescope", "valuehash", "red", "prot",
          "nc", "internal"]


def load(p, ncol):
    d = {}
    for line in open(p, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        assert len(f) == ncol, (p, len(f), f[:2])
        assert f[0] not in d, ("duplicate", f[0])
        d[f[0]] = f
    return d


before = load(sys.argv[1], 11)
after = load(sys.argv[2], 15)
print("constants: before %d, after %d" % (len(before), len(after)))

# 1. raw
removed = sorted(set(before) - set(after))
added = sorted(set(after) - set(before))
print("\n== raw comparison by name")
print("removed (%d):" % len(removed))
for n in removed:
    print("  ", n)
print("added (%d):" % len(added))
for n in added:
    print("  ", n)
raw = []
for n in sorted(set(before) & set(after)):
    for i in range(1, 11):
        if before[n][i] != after[n][i]:
            raw.append((n, FIELDS[i]))
print("same name, a field differs (%d):" % len(raw))
for n, fld in raw:
    print("  ", n, fld)

# 2. substituted
# the new aliases: deprecated after-constants named as the old name of a renamed constant
# (constants deprecated before the change, e.g. E0GX.*, are compared as any other)
old_names = {f[11] for f in after.values() if f[11] != f[0]}
wrappers = sorted(n for n, f in after.items() if f[14] == "deprecated" and n in old_names)
print("\n== substituted comparison")
print("new deprecated aliases set aside (%d):" % len(wrappers))
for n in wrappers:
    f = after[n]
    print("   %s  [%s, %s, levels %s, %s]" % (n, f[1], f[2], f[3], f[7]))
keyed = {}
for n, f in after.items():
    if n in wrappers:
        continue
    k = f[11]
    assert k not in keyed, ("two after-constants map to", k)
    # module, kind, levels, substituted type hash, telescope, substituted value hash, red, prot,
    # nc, internal
    keyed[k] = (n, [f[1], f[2], f[3], f[12], f[5], f[13], f[7], f[8], f[9], f[10]])
renamed = sorted((n, k) for k, (n, _) in keyed.items() if n != k)
print("renamed (%d), new <- old:" % len(renamed))
for n, k in renamed:
    print("   %s <- %s" % (n, k))
unmatched_before = sorted(set(before) - set(keyed))
unmatched_after = sorted(set(keyed) - set(before))
print("before-constants with no after-constant (%d):" % len(unmatched_before))
for n in unmatched_before:
    print("  ", n)
print("after-constants with no before-constant (%d):" % len(unmatched_after))
for k in unmatched_after:
    print("  ", keyed[k][0])
diffs = []
for k in sorted(set(before) & set(keyed)):
    b = before[k][1:11]
    a = keyed[k][1]
    for i, (u, v) in enumerate(zip(b, a)):
        if u != v:
            diffs.append((keyed[k][0], FIELDS[i + 1], u, v))
print("field differences after substitution (%d):" % len(diffs))
for x in diffs:
    print("  ", x)
# how many raw hash changes the substitution explains
explained = sorted({n for n, fld in raw if fld in ("typehash", "valuehash")} - set(wrappers))
print("\nwrappers whose fields differ from the old constant of the same name (the old\n"
      "constant is now the wrapper: compared above under its new name): %s"
      % sorted({n for n, _ in raw if n in wrappers}))
print("\nraw type/value hash changes under the same name (%d), all explained by the substitution: %s"
      % (len(explained), all(not any(d[0] == n for d in diffs) for n in explained)))
for n in explained:
    print("  ", n)
