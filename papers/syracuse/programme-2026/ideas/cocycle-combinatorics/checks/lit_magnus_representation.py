"""Verification for drafts/lit-magnus-representation.md.

Leverages Florens-Massuyeau-Serrano de Rodrigo, "A functorial extension of the
Magnus representation to the category of three-dimensional cobordisms"
(arXiv:1604.06905). We test the *rank-1* shadow of that paper's algebra on our
kernel:

  M(w) = [[Y^{len w}, 0], [S(w), X^{|w|}]]   (lower-triangular transfer matrix)

is the "graph of the crossed homomorphism S" -- the rank-1 analogue of the
paper's functorial repair of the (non-homomorphic) Magnus representation by
passing to graphs / Lagrangian relations (Lemma 5.4: Mag(c(f)) is the *graph*
of the unitary isomorphism f).

Checks:
  V1  M is a monoid homomorphism and  det M(w) = X^{|w|} Y^{len w}  is a pure
      6-unit -- the rank-1 image of the paper's "det(r_phi) in +-G" (Rem. 6.4).
  V2  rotation = conjugation by M(prefix): the S^{(j)} are off-diagonals of a
      conjugacy class; det and trace are the cyclic (rotation) invariants.
  V3  D(w)^2 = tr M(w)^2 - 4 det M(w); the eigenvalues of M(w) are X^{|w|}, Y^{len w},
      so D = X^{|w|} - Y^{len w} is the *eigenvalue gap* / discriminant root, and
      G = |D| on a cycle is therefore the discriminant of the transfer matrix.
  V4  THE LEVER CEILING IS WELL-DEFINED (the det=unit consequence): for a
      bounded-arc word d^k beta d^{L-k}, the rotation-pair wedge equals
      X^{kd} Y^{L-k-1} (S(beta d) - S(d beta)); hence sixfree(wedge) is
      INDEPENDENT of k and L, equal to sixfree(S(beta d) - S(d beta)). The
      ceiling is the canonical 6-free representative of a full +-G coset -- it is
      NOT a Z[1/6]-coset that a determinant could promote to a finer integer.
  V5  REVERSAL = TRANSPOSE stays a dead end: (a) S(w^R) is NOT a 6-unit multiple
      of the antipode S(w)|_{X->1/X,Y->1/Y}; (b) no CONSTANT skew-Hermitian form
      H makes the 2x2 transfer matrix unitary (M-bar^T H M = H). The paper's
      antipode-transpose duality (Sakasai symplecticity) is a feature of the
      rank-2g unitary Magnus rep, not of our rank-1 transfer matrix.

Run from the repo root, or from anywhere -- the kernel path is inserted robustly.
Exit code 0 iff every check passes.
"""

from __future__ import annotations

import sys
from math import gcd
from pathlib import Path

# --- robust kernel import (repo-root OR script-relative) ------------------- #
_KERNEL_REL = Path("approaches/cocycle-combine/lib")
_here = Path(__file__).resolve()
_candidates = [
    Path.cwd() / _KERNEL_REL,                 # running from repo root
    _here.parents[3] / _KERNEL_REL,           # checks/ -> idea -> ideas -> repo
]
for _c in _candidates:
    if (_c / "cocycle.py").exists():
        sys.path.insert(0, str(_c))
        break
else:  # pragma: no cover
    sys.stderr.write(
        "ERROR: could not locate approaches/cocycle-combine/lib/cocycle.py.\n"
        "Run from the repo root (Syracuse/) or keep this file under "
        "ideas/cocycle-combinatorics/checks/.\n"
    )
    sys.exit(2)

import sympy as sp  # noqa: E402
from cocycle import S, D, X, Y, rotate  # noqa: E402

Z2 = sp.zeros(2)


def M(w):
    """Lower-triangular transfer matrix; off-diagonal is the cocycle S."""
    return sp.Matrix([[Y ** len(w), 0], [S(w), X ** sum(w)]])


def antipode(expr):
    """The Z[X,Y] antipode x -> x^{-1} on group-like generators: X->1/X, Y->1/Y."""
    return expr.subs({X: 1 / X, Y: 1 / Y}, simultaneous=True)


def sixfree(n):
    """Strip every factor 2 and 3 from |n| (canonical rep of the +-G coset)."""
    n = abs(int(n))
    if n == 0:
        return 0
    while n % 2 == 0:
        n //= 2
    while n % 3 == 0:
        n //= 3
    return n


WORDS = [(1,), (2,), (3,), (1, 2), (2, 1), (1, 2, 4), (3, 1, 5), (2, 2, 3, 1), (4, 1, 1, 3)]
PAIRS = [((1, 2), (4,)), ((2,), (3, 1)), ((1, 2, 4), (3, 1)), ((5,), (1, 2, 2))]


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" :: {detail}" if detail else ""))
    return ok


def v1_monoid_hom_and_det():
    ok = True
    for u, v in PAIRS:
        ok &= sp.expand((M(tuple(u) + tuple(v)) - M(u) * M(v))).is_zero_matrix or \
              sp.simplify(M(tuple(u) + tuple(v)) - M(u) * M(v)) == Z2
    det_ok = all(
        sp.expand(M(w).det() - X ** sum(w) * Y ** len(w)) == 0 for w in WORDS
    )
    return check("V1 M monoid-hom", ok) & \
        check("V1 det M(w) = X^|w| Y^len(w) (pure 6-unit)", det_ok)


def v2_rotation_is_conjugation():
    # full-block rotation w = uv -> vu is conjugation by M(u); det/trace invariant
    ok = True
    for u, v in PAIRS:
        uv = tuple(u) + tuple(v)
        vu = tuple(v) + tuple(u)
        ok &= sp.simplify(M(vu) - M(u).inv() * M(uv) * M(u)) == Z2
    # single-letter rotation (the S^{(j)} shift) keeps det & trace fixed
    inv_ok = True
    for w in WORDS:
        if len(w) < 2:
            continue
        wr = tuple(rotate(w, 1))
        inv_ok &= sp.expand(M(w).det() - M(wr).det()) == 0
        inv_ok &= sp.expand(M(w).trace() - M(wr).trace()) == 0
    return check("V2 rotation = conjugation by M(prefix)", ok) & \
        check("V2 det & trace are rotation-invariant", inv_ok)


def v3_discriminant_eigenvalue_gap():
    ok = True
    for w in WORDS:
        Mw = M(w)
        ok &= sp.expand(D(w) ** 2 - (Mw.trace() ** 2 - 4 * Mw.det())) == 0
        # eigenvalues are literally the diagonal X^|w|, Y^len(w)
        eig = set(Mw.eigenvals().keys())
        ok &= eig == {X ** sum(w), Y ** len(w)}
    return check("V3 D^2 = tr^2 - 4det; eigenvalues = X^|w|, Y^len(w) (D = eigen-gap)", ok)


def v4_lever_ceiling_well_defined():
    """det = unit  =>  sixfree(wedge) is k- and L-independent = sixfree(core)."""
    betas = [(3,), (3, 4), (4, 3, 4), (2, 3), (4, 1, 1, 3)]
    all_ok = True
    report = []
    for beta in betas:
        for d in (1, 2, 5):
            core = S(tuple(beta) + (d,)) - S((d,) + tuple(beta))
            base = sixfree(int(core.subs({X: 2, Y: 3})))
            vals = set()
            for L in range(2, 9):
                for k in range(0, L):
                    w1 = (d,) * k + tuple(beta) + (d,) * (L - k)
                    w2 = (d,) * (k + 1) + tuple(beta) + (d,) * (L - k - 1)
                    wedge = S(w1) - S(w2)
                    # symbolic factorisation = unit * core
                    sym = sp.expand(
                        wedge - X ** (k * d) * Y ** (L - k - 1) * core
                    )
                    if sym != 0:
                        all_ok = False
                    vals.add(sixfree(int(wedge.subs({X: 2, Y: 3}))))
            ok = vals == {base}
            all_ok &= ok
            if not ok:
                report.append(f"beta={beta} d={d}: {vals} != {base}")
    return check(
        "V4 sixfree(wedge) indep of k,L = sixfree(core) (ceiling well-defined)",
        all_ok, "; ".join(report),
    )


def v5_reversal_transpose_deadend():
    # (a) S(w^R) is not a 6-unit (monomial) multiple of antipode(S(w))
    not_unit = True
    for w in WORDS:
        if len(w) < 2:
            continue
        wR = tuple(reversed(w))
        ratio = sp.simplify(S(wR) / antipode(S(w)))
        # a 6-unit would be +- X^a Y^b (a single Laurent monomial)
        is_monomial = ratio.free_symbols <= {X, Y} and len(sp.Add.make_args(sp.expand(ratio))) == 1 \
            and sp.expand(ratio).is_Mul or sp.expand(ratio).is_Pow or sp.expand(ratio).is_Atom
        # robust monomial test: numerator and denominator each single-term
        num, den = sp.fraction(sp.together(ratio))
        mono = (len(sp.Add.make_args(sp.expand(num))) == 1 and
                len(sp.Add.make_args(sp.expand(den))) == 1)
        if mono:
            not_unit = False
    # (b) no CONSTANT form H makes the 2x2 transfer matrix unitary
    a, b, c, d = sp.symbols("a b c d")
    H = sp.Matrix([[a, b], [c, d]])
    eqs = set()
    for w in [(1,), (2,), (1, 2), (3,), (1, 2, 4)]:
        Mbar = M(w).applyfunc(antipode)
        Rmat = Mbar.T * H * M(w) - H
        for e in Rmat:
            e = sp.expand(sp.together(e))
            if e != 0:
                eqs.add(e)
    sol = sp.solve(list(eqs), [a, b, c, d], dict=True)
    only_trivial = all(
        all(s.get(v, 0) == 0 for v in (a, b, c, d)) for s in sol
    ) if sol else True
    return check("V5a S(w^R) is NOT a 6-unit multiple of antipode(S(w))", not_unit) & \
        check("V5b no constant unitary form for the 2x2 transfer matrix "
              "(antipode-transpose duality is rank-2g only)", only_trivial,
              f"solutions={sol}")


def main():
    print("=== lit_magnus_representation: rank-1 shadow of arXiv:1604.06905 ===")
    results = [
        v1_monoid_hom_and_det(),
        v2_rotation_is_conjugation(),
        v3_discriminant_eigenvalue_gap(),
        v4_lever_ceiling_well_defined(),
        v5_reversal_transpose_deadend(),
    ]
    ok = all(results)
    print("=" * 60)
    print("ALL PASS" if ok else "SOME FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
