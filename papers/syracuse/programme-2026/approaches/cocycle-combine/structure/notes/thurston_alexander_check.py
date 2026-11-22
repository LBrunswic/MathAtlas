"""Numerical sanity battery for the Alexander-Thurston inequality of
notes/thurston-alexander-formal.md.  Not a Z[X,Y] identity (it involves a real
direction phi and absolute values), so it lives here rather than in
verify_structure.py.  The theorem itself is proved by hand in the note; this only
guards against indexing/sign slips.

Run:  python3 approaches/cocycle-combine/structure/notes/thurston_alexander_check.py
"""
import os, sys, math, random

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))
from lib.cocycle import partial_sums  # noqa: E402


def support_S(w):
    o = len(w); e = partial_sums(w)
    return [(e[k], o - 1 - k) for k in range(o)]


def width_N_S(w, a, b):                 # span of the Magnus path = width_phi N(S)
    vals = [a * x + b * y for (x, y) in support_S(w)]
    return max(vals) - min(vals)


def alexander_D(w, a, b):               # width_phi N(D) = |aE - b o|
    return abs(a * sum(w) - b * len(w))


def thurston(w, a, b):                  # total variation = sum_k |a d_k - b|
    return sum(abs(a * d - b) for d in w)


def phi_monotone(w, a, b):              # all per-letter defects same sign
    inc = [a * d - b for d in w]
    return all(i >= 0 for i in inc) or all(i <= 0 for i in inc)


def main():
    random.seed(1)
    words = [(1, 2), (3, 1, 1, 2, 4), (1, 1, 2, 2, 3, 3), (2, 2, 2), (1, 1, 1, 1),
             (5, 2, 1, 1), (2, 1, 3), (3, 3, 3)]
    words += [tuple(random.randint(1, 5) for _ in range(random.randint(2, 8)))
              for _ in range(200)]
    random.seed(2)
    dirs = [(math.log(2), math.log(3)), (1, 1), (1, 2), (2, 1), (1, 0), (0, 1)]
    dirs += [(random.uniform(-3, 3), random.uniform(-3, 3)) for _ in range(60)]

    nA = nS = neq = ninc = 0
    for w in words:
        p = support_S(w)
        if not all((p[k + 1][0] - p[k][0], p[k + 1][1] - p[k][1]) == (w[k], -1)
                   for k in range(len(w) - 1)):
            ninc += 1
        for (a, b) in dirs:
            T = thurston(w, a, b)
            if alexander_D(w, a, b) > T + 1e-9:                 # Alexander(D) <= Thurston
                nA += 1
            if width_N_S(w, a, b) > T + 1e-9:                   # cocycle span <= Thurston
                nS += 1
            if (abs(alexander_D(w, a, b) - T) < 1e-9) != phi_monotone(w, a, b):
                neq += 1

    N = len(words) * len(dirs)
    assert ninc == 0, "increment law (d_k,-1) failed"
    assert nA == 0, f"Alexander(D)<=Thurston violated {nA}/{N}"
    assert nS == 0, f"cocycle-span<=Thurston violated {nS}/{N}"
    assert neq == 0, f"equality<=>monotone mismatch {neq}/{N}"
    print(f"PASS  increment law (d_k,-1)            [{len(words)} words]")
    print(f"PASS  |aE-bo| <= sum|a d_k - b|          [{N} cases]")
    print(f"PASS  width N(S) <= sum|a d_k - b|       [{N} cases]")
    print(f"PASS  equality <=> phi-monotone gaps     [{N} cases]")
    print("\nthurston_alexander_check: Alexander-Thurston inequality holds on the battery.")


if __name__ == "__main__":
    main()
