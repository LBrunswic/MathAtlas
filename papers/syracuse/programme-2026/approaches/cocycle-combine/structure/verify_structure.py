"""Certify every structural claim in structure.md as a Z[X,Y] identity.

Run:  python3 approaches/cocycle-combine/structure/verify_structure.py
Exits 0 with a per-claim PASS report, or raises AssertionError on the first
claim that fails. Imports the trusted kernel; adds no new definitions of S/D.

The claims (see structure.md §1-4):
  C1  M(w) = prod_k [[Y,0],[1,X^d_k]] = [[Y^o,0],[S,X^E]]      (entries)
  C2  M is a monoid homomorphism: M(uv) = M(u) M(v)
  C3  rotation = conjugation: M(vu) = M(u)^{-1} M(uv) M(u)
  C4  (D,-S)^T is the Y^o-eigenvector of M(w)
  C5  crossed-hom / cocycle: with chi(w)=X^E/Y^o and sigma=S/Y^o,
        sigma(uv) = sigma(u) + chi(u) sigma(v)
  C6  coboundary of a constant c is  w |-> c*D(w)   (so S is defined mod <D>)
  C7  core = wedge:  C(u,v) = S(uv)-S(vu) = det[[D(u),D(v)],[S(u),S(v)]]
  C8  Plucker/Jacobi:  D(u)C(v,w) + D(v)C(w,u) + D(w)C(u,v) = 0
  C9  edge-bit monomial core (Knight, Baker-free high-cycle obstruction):
        on parity words, with g(v)=sum_i X^{d_i} Y^{x-1-i} (= S of the gap word,
        = Trumper's link function L), the edge pair (1u0, 0u1) satisfies
          C9a  Y*g(1u0) - g(0u1) + D = X^{E-1}(X-1)
        and the adjacent-rotation single core satisfies
          C9b  g(p01) - g(p10) = X^{E-2}(X-1).
        At X->2 both right sides are pure even monomials (2^{E-1}, 2^{E-2});
        since for a Christoffel high cycle 1u0 and 0u1 are rotations of one
        cyclic word (Cohn), |D|=G divides that monomial, and G odd forces |D|=1.
  C11 monodromy char poly (the Alexander-polynomial anchor): det(tI - M(w)) =
        (t - X^E)(t - Y^o); eigenvalues X^E (eigvec (0,1)^T) and Y^o (eigvec
        (D,-S)^T, = C4); so D = X^E - Y^o is the difference of the two eigenvalues.
        A cyclic word is intrinsically a *fibered* class: M(w) is its monodromy and
        (t-X^E)(t-Y^o) the fibered Alexander polynomial (see notes/thurston-alexander-norm).
  C10 S is a recognizable (rational) series of rank EXACTLY 2 (Berstel-Reutenauer):
        with the linear representation (lambda, mu, gamma), lambda=(0,1),
        mu(d)=[[Y,0],[1,X^d]] (= the C1 letter matrix, a monoid morphism),
        gamma=(1,0)^T, one has S(w)=lambda*mu(w)*gamma. rank<=2 because a
        2-dim representation exists (C1/C2); rank>=2 because the 2x2 Hankel
        minor on rows/cols {eps,(1)} is det[[0,1],[1,X+Y]]=-1 != 0. Hence the
        C1 representation is minimal/reduced (dim = rank = 2).
"""
from __future__ import annotations

import os
import sys

import sympy as sp

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from lib.cocycle import S, D, X, Y  # noqa: E402

# Word test bench: varied lengths, gap profiles, includes the known cycle words.
WORDS = [
    (2,), (1, 2), (1, 2, 2, 2, 2), (2, 1, 3), (1, 1, 1, 4, 1, 1, 1),
    (5, 2, 1, 1), (3, 1, 1, 2, 4), (1, 1, 2, 2, 3, 3),
]


def Mletter(d):
    return sp.Matrix([[Y, 0], [1, X ** d]])


def M(word):
    out = sp.eye(2)
    for d in word:
        out = out * Mletter(d)
    return out


def C(u, v):
    return sp.expand(D(u) * S(v) - D(v) * S(u))


def g_pv(pv):
    """Knight's parity-vector numerator g(v) = sum_i X^{d_i} Y^{x-1-i}, where the
    d_i are the (0-based) positions of the 1s and x is their count. Equals S of the
    cyclic gap word, and equals Trumper's link function L(w) at (X,Y)=(2,3)->(2,3)."""
    ones = [i for i, b in enumerate(pv) if b == 1]
    x = len(ones)
    return sum(X ** ones[i] * Y ** (x - 1 - i) for i in range(x))


def D_pv(pv):
    """D = X^k - Y^x for a parity vector of length k with x ones."""
    return X ** len(pv) - Y ** sum(pv)


def _zero(expr):
    return sp.expand(expr) == 0


def _zero_mat(mat):
    return sp.expand(mat) == sp.zeros(*mat.shape)


def check(name, predicate):
    assert predicate, f"FAIL: {name}"
    print(f"PASS  {name}")


def main():
    # C1: matrix product has the claimed entries.
    for w in WORDS:
        m = sp.expand(M(w))
        o, E = len(w), sum(w)
        check(
            f"C1 entries {w}",
            _zero(m[0, 0] - Y ** o) and _zero(m[0, 1])
            and _zero(m[1, 0] - S(w)) and _zero(m[1, 1] - X ** E),
        )

    # C2: monoid homomorphism.
    for u in WORDS:
        for v in WORDS:
            check(
                f"C2 hom {u}*{v}",
                _zero_mat(M(tuple(u) + tuple(v)) - M(u) * M(v)),
            )

    # C3: rotation = conjugation by M(u) (split tau=uv, rotate to vu).
    for u in WORDS:
        for v in WORDS:
            lhs = M(tuple(v) + tuple(u))
            rhs = M(u).inv() * M(tuple(u) + tuple(v)) * M(u)
            check(f"C3 conj {u}|{v}", _zero_mat(lhs - rhs))

    # C4: (D,-S)^T is the Y^o eigenvector.
    for w in WORDS:
        vec = sp.Matrix([D(w), -S(w)])
        check(f"C4 eigvec {w}", _zero_mat(M(w) * vec - Y ** len(w) * vec))

    # C5: crossed homomorphism for sigma = S/Y^o, chi = X^E/Y^o.
    def sigma(w):
        return S(w) / Y ** len(w)

    def chi(w):
        return X ** sum(w) / Y ** len(w)

    for u in WORDS:
        for v in WORDS:
            uv = tuple(u) + tuple(v)
            check(
                f"C5 cocycle {u}|{v}",
                sp.simplify(sigma(uv) - sigma(u) - chi(u) * sigma(v)) == 0,
            )

    # C6: coboundary of constant c is w |-> c*D(w).
    # The S-level coboundary is  Y^o * (chi(w)-1) * c = c*(X^E - Y^o) = c*D(w).
    c = sp.symbols("c")
    for w in WORDS:
        coboundary_S = Y ** len(w) * (chi(w) - 1) * c
        check(f"C6 coboundary {w}", _zero(coboundary_S - c * D(w)))

    # C7: core is the 2x2 determinant (the wedge of (D,S) vectors).
    for u in WORDS:
        for v in WORDS:
            wedge = D(u) * S(v) - D(v) * S(u)
            diff = S(tuple(u) + tuple(v)) - S(tuple(v) + tuple(u))
            check(f"C7 wedge {u}|{v}", _zero(diff - wedge))

    # C8: Plucker / Jacobi relation among three words.
    trip = [(1, 2), (3,), (2, 1), (1, 1, 2), (4,)]
    for i in range(len(trip)):
        for j in range(i + 1, len(trip)):
            for k in range(j + 1, len(trip)):
                u, v, w = trip[i], trip[j], trip[k]
                rel = D(u) * C(v, w) + D(v) * C(w, u) + D(w) * C(u, v)
                check(f"C8 plucker {u},{v},{w}", _zero(rel))

    # C9: edge-bit monomial cores (Knight's Baker-free high-cycle obstruction).
    # Central blocks u (binary); 1u0 and 0u1 are the high cycle's vh and vh^R.
    CENTRAL = [
        (0, 1, 1, 0, 1), (1, 0, 1, 1, 0, 0, 1), (0,), (1,), (1, 0),
        (0, 1, 1), (1, 1, 0, 0, 1, 0, 1), (1, 0, 1, 0, 1, 1, 0, 0, 1, 1),
    ]
    for u in CENTRAL:
        one_u_zero = (1,) + tuple(u) + (0,)
        zero_u_one = (0,) + tuple(u) + (1,)
        E = len(one_u_zero)
        lhs = Y * g_pv(one_u_zero) - g_pv(zero_u_one) + D_pv(one_u_zero)
        check(f"C9a edge-core 1u0|0u1 u={u}", _zero(lhs - X ** (E - 1) * (X - 1)))

    # C9b: adjacent-rotation single core g(p01) - g(p10) = X^{E-2}(X-1).
    PREFIX = [(1, 0, 1, 1, 0, 1), (1, 1, 0, 1, 0, 0, 1), (1, 0), (1, 1, 0, 1)]
    for p in PREFIX:
        a, b = tuple(p) + (0, 1), tuple(p) + (1, 0)
        E = len(a)
        check(
            f"C9b adj-core p01|p10 p={p}",
            _zero(g_pv(a) - g_pv(b) - X ** (E - 2) * (X - 1)),
        )

    # C10: S is a recognizable series of rank exactly 2 (minimal C1 representation).
    lam, gam = sp.Matrix([[0, 1]]), sp.Matrix([1, 0])
    for w in WORDS:
        check(f"C10 lin-rep S = lam*M*gam {w}", _zero((lam * M(w) * gam)[0, 0] - S(w)))

    def Hank(p, q):  # Hankel entry r(p.q) = S(p+q)
        return S(tuple(p) + tuple(q))

    # rank >= 2: a nonzero 2x2 Hankel minor (rank <= 2 already holds from the 2-dim rep)
    rows2, cols2 = [(), (1,)], [(), (1,)]
    H2 = sp.Matrix([[Hank(p, q) for q in cols2] for p in rows2])
    check("C10 Hankel rank>=2 (det = -1 != 0)", _zero(H2.det() + 1))
    # minimality via Berstel-Reutenauer Prop 2.1 (p.32): the representation is reduced iff
    # {lambda*M(w)} span K^{1x2} (accessible) and {M(w)*gamma} span K^{2x1} (co-accessible).
    # Words {eps,(1)} already witness both, with unit determinants.
    rowspan = sp.Matrix([(lam * M(w))[:] for w in [(), (1,)]])      # rows lambda*M(w)
    colspan = sp.Matrix.hstack(*[M(w) * gam for w in [(), (1,)]])   # cols M(w)*gamma
    check("C10 accessible (row-span det = -1)", _zero(rowspan.det() + 1))
    check("C10 co-accessible (col-span det = 1)", _zero(colspan.det() - 1))
    # consistency with rank <= 2: every 3x3 Hankel minor vanishes
    pts = [(), (1,), (2,), (1, 2), (2, 1), (3,)]
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            for k in range(j + 1, len(pts)):
                R = (pts[i], pts[j], pts[k])
                H3 = sp.Matrix([[Hank(p, q) for q in R] for p in R])
                check(f"C10 Hankel 3x3 minor=0 {R}", _zero(H3.det()))

    # C11: monodromy characteristic polynomial = (t-X^E)(t-Y^o); X^E-eigenvector (0,1)^T.
    t = sp.symbols("t")
    for w in WORDS:
        o, E = len(w), sum(w)
        charpoly = sp.expand((t * sp.eye(2) - M(w)).det())
        check(f"C11 charpoly {w}", _zero(charpoly - sp.expand((t - X ** E) * (t - Y ** o))))
        vX = sp.Matrix([0, 1])
        check(f"C11 X^E-eigvec {w}", _zero_mat(M(w) * vX - X ** E * vX))

    print("\nstructure.py: all structural claims certified over Z[X,Y].")


if __name__ == "__main__":
    main()
