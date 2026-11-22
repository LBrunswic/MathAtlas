#!/usr/bin/env python3
r"""R2 verification -- McMullen's Alexander norm / Newton polytope, the GO/NO-GO.

Reads C. T. McMullen, "The Alexander polynomial of a 3-manifold and the Thurston
norm on cohomology", Ann. Sci. ENS 35 (2002) 153-171
(sources/mcmullen-alexander-thurston-norm-2002.pdf).  Cited results:

  eq (1.2) / Thm 5.1 :  I(G) = m^{p(M)} . (Delta_G)   (Alexander ideal =
                        augmentation-ideal power times principal Alexander poly),
                        p = 0 if b_1<=1, else 1+b_3(M).
  eq (1.3) / Thm 4.1 :  b_1(ker phi) = deg Delta_G(s^phi) + p(M) = ||phi||_A + p.
  sec 4 / eq (7.1)   :  ||phi||_A = sup_{a_alpha a_beta != 0} phi(alpha - beta)
                        = WIDTH of the Newton polytope N(Delta_G) in direction phi;
                        the unit ball is (up to scale 2) DUAL to N(Delta_G).
  eq (4.3)           :  deg Delta_G(s^phi) = ||phi||_A  PROVIDED the extreme values
                        phi(alpha) are attained UNIQUELY (else cancellation drops deg).
  Examples 4 (5_1^2), 10 (trivial Delta): a binomial / vanishing slice -> the
                        1-variable poly under-reports; norm = polytope width.
  "Failure of convexity" (D_oo x D_oo): I(G)=<x^2-1,y^2-1,(x-1)(y-1)>, a genuine
                        2-DIM Newton polytope -> b_1(ker phi) convex+periodic. The
                        template for what a rank->=2 enrichment must look like.

DICTIONARY (OUR objects; STRUCTURE.md sec.1-3, lit-silver-williams.md):
  H = ab(G) = <X,Y> = Z^2  (X<->2, Y<->3);  m = <X-1,Y-1> the augmentation ideal.
  S = chi o d/dx1 (the cocycle);  T = chi o d/dx0 (2nd cocycle, R1);
  D = X^E - Y^o = (X-1)T - (Y-1)S  (binary Fox fundamental formula).
  cores C(u,v) = D(u)S(v)-D(v)S(u) = 2x2 minors = the maximal-minor (Alexander) ideal.
  Delta_1 = gcd(T,S)  (the genuine 2-variable Crowell/McMullen Alexander poly; =1
            for primitive shapes, = period factor for w=u^k).
  cycle / period Alexander poly  Delta(t) = X^E - Y^o t  over Z[X^+-,Y^+-,t^+-]
            (Silver-Williams cyclic-cover poly; t the deck variable of w^r).

HEADLINE TO DECIDE:  Delta_G is a BINOMIAL (or collinear) in EVERY guise =>
  N(Delta_G) is at most 1-DIMENSIONAL (segment/point) => ||.||_A is a degenerate
  rank-<=1 seminorm => NO vertex-isolating ("unit") slice exists.  A constructively
  small slice needs a 2-DIM Newton polytope (>=3 non-collinear monomials), which a
  binomial can NEVER supply.  Verify, and test whether natural rank-1-derived
  enrichments escape the segment (they do not).

Exit 0 iff every asserted check passes.
"""
from __future__ import annotations

import itertools
import os
import sys
from functools import reduce
from math import gcd

import sympy as sp

# --- robust kernel import --------------------------------------------------- #
_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (
    os.path.join(_HERE, "..", "..", "..", "approaches", "cocycle-combine", "lib"),
    os.path.join(os.getcwd(), "approaches", "cocycle-combine", "lib"),
):
    _p = os.path.abspath(_p)
    if os.path.exists(os.path.join(_p, "cocycle.py")):
        sys.path.insert(0, _p)
        break
from cocycle import X, Y, S as Sker, D as Dker, core_C, rotations  # noqa: E402

t, s = sp.symbols("t s")
PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("  [ok] " if cond else "  [XX] ") + name)
    return cond


# --------------------------------------------------------------------------- #
# binary rebuild of the two cocycles S (d/dx1) and T (d/dx0)  (R1 idiom)       #
# --------------------------------------------------------------------------- #
def gap_to_binary(w):
    b = []
    for d in w:
        b.append(1)
        b.extend([0] * d)
    return b


def ST(w):
    b = gap_to_binary(w)
    tot1 = sum(b)
    pre0 = pre1 = 0
    S = sp.Integer(0)
    T = sp.Integer(0)
    for bi in b:
        aft1 = tot1 - pre1 - (1 if bi == 1 else 0)
        term = (X ** pre0) * (Y ** aft1)
        if bi == 1:
            S += term
            pre1 += 1
        else:
            T += term
            pre0 += 1
    return sp.expand(S), sp.expand(T)


# --------------------------------------------------------------------------- #
# Newton-polytope machinery                                                    #
# --------------------------------------------------------------------------- #
def support(monomials):
    """monomials: dict exponent-tuple -> coeff.  Return list of exponent tuples."""
    return [m for m, c in monomials.items() if c != 0]


def affine_dim(pts):
    """Dimension of the affine hull of a set of integer points (-1 if empty)."""
    if not pts:
        return -1
    base = pts[0]
    rows = [[p[i] - base[i] for i in range(len(base))] for p in pts[1:]]
    if not rows:
        return 0
    return sp.Matrix(rows).rank()


def poly_support(expr, gens):
    """Newton support of a sympy polynomial expr in the given generators."""
    P = sp.Poly(sp.expand(expr), *gens)
    return {tuple(m): c for m, c in zip(P.monoms(), P.coeffs())}


def width(supp, phi):
    """McMullen ||phi||_A on this support = max phi.alpha - min phi.alpha."""
    vals = [sum(p * e for p, e in zip(phi, m)) for m in supp]
    return max(vals) - min(vals)


def mcmullen_slice(monomials, phi):
    """The 1-variable slice Delta(s^phi): collapse t_i -> s^{phi_i}, sum like powers.
    Returns dict {s-degree: coeff} with zero coeffs removed."""
    out = {}
    for m, c in monomials.items():
        deg = sum(p * e for p, e in zip(phi, m))
        out[deg] = out.get(deg, 0) + c
    return {d: c for d, c in out.items() if c != 0}


WORDS = [(1,), (2,), (1, 2), (2, 1), (1, 2, 3), (3, 1, 2), (2, 1, 1, 3),
         (3, 1, 1, 2, 2), (1, 3, 1, 2), (4, 1, 1, 3)]


# ======================================================================= #
print("=" * 74)
print("PART A -- N(Delta_G) is at most 1-DIMENSIONAL: dim <= #monomials - 1.")
print("          The cycle Delta = X^E - Y^o t is a BINOMIAL (segment); the genuine")
print("          2-var Crowell Delta_1 = gcd(T,S) is a unit (point) / collinear.")
print("=" * 74)

# (A1) cycle/period Alexander poly Delta(t)=X^E - Y^o t : 2 monomials in (X,Y,t).
a1 = True
for w in WORDS:
    E, o = sum(w), len(w)
    Delta = X ** E - Y ** o * t
    supp = support(poly_support(Delta, (X, Y, t)))
    a1 &= (len(supp) == 2 and affine_dim(supp) == 1)
check("cycle Delta = X^E - Y^o t : 2 monomials, N(Delta) a SEGMENT (dim 1)", a1)
print("       -> t IS a formal 3rd variable, but adds NO polytope dimension:")
print("          2 monomials force dim<=1 in ANY number of variables.")

# (A2) D = X^E - Y^o is itself the binomial (segment).
a2 = all(affine_dim(support(poly_support(Dker(w), (X, Y)))) == 1 for w in WORDS)
check("D = X^E - Y^o : N(D) a SEGMENT (dim 1)", a2)

# (A3) genuine 2-variable Crowell/McMullen Alexander poly Delta_1 = gcd(T,S).
#      primitive shapes -> Delta_1 = 1 (a UNIT: Newton polytope a POINT, dim 0).
prim = [(1, 2), (2, 1), (1, 2, 3), (3, 1, 2), (2, 1, 1, 3), (1, 3, 1, 2)]
a3 = True
for w in prim:
    S, T = ST(w)
    g = sp.gcd(sp.Poly(S, X, Y), sp.Poly(T, X, Y)).as_expr()
    dim = affine_dim(support(poly_support(g, (X, Y))))
    a3 &= (sp.expand(g - 1) == 0 and dim == 0)
check("primitive: Delta_1 = gcd(T,S) = 1 (UNIT; N a POINT, dim 0; ||.||_A == 0)", a3)

# (A4) imprimitive w=u^k : Delta_1 a proper factor of D, but its monomials are COLLINEAR
#      (the cyclotomic-like sum sum_i X^{ai} Y^{b(k-1-i)}), so still dim <= 1.
imprim = [((2, 1), 2), ((1,), 3), ((1, 2), 2), ((3, 1), 2), ((1, 1, 2), 2)]
a4 = True
for u, k in imprim:
    w = u * k
    S, T = ST(w)
    g = sp.gcd(sp.Poly(S, X, Y), sp.Poly(T, X, Y)).as_expr()
    supp = support(poly_support(g, (X, Y)))
    a4 &= (sp.expand(g - 1) != 0 and affine_dim(supp) <= 1)
check("imprimitive w=u^k: Delta_1 nontrivial but COLLINEAR (N dim <= 1)", a4)
print("       => in EVERY guise the Alexander polytope is a segment or a point.")
print("          The Alexander norm ||.||_A is a DEGENERATE rank-<=1 seminorm.")


# ======================================================================= #
print("=" * 74)
print("PART B -- ||phi||_A = Newton-polytope WIDTH, and it is DEGENERATE: it")
print("          vanishes on a codim-1 hyperplane (the direction along the segment).")
print("=" * 74)
# For the cycle binomial, segment endpoints alpha1=(E,0,0), alpha2=(0,o,1).
# ||phi||_A = |phi.(alpha1-alpha2)|; kernel = {phi : phi.(alpha1-alpha2)=0}, codim 1.
b1ok = True
b1deg = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    Delta = X ** E - Y ** o * t
    supp = support(poly_support(Delta, (X, Y, t)))
    a1v, a2v = (E, 0, 0), (0, o, 1)
    # width matches |phi.(a1-a2)| on a grid of phi
    for phi in itertools.product(range(-2, 3), repeat=3):
        wd = width(supp, phi)
        pred = abs(sum(p * (a1v[i] - a2v[i]) for i, p in enumerate(phi)))
        b1ok &= (wd == pred)
    # exhibit a NONZERO kernel direction phi _|_ (alpha1-alpha2): width 0
    diff = tuple(a1v[i] - a2v[i] for i in range(3))   # (E, -o, -1)
    phi0 = (0, 1, -o)         # phi0 . diff = 0*E + 1*(-o) + (-o)*(-1) = 0
    b1deg &= (phi0 != (0, 0, 0) and width(supp, phi0) == 0)
check("||phi||_A == width N(Delta) == |phi.(alpha1-alpha2)| on a 5^3 grid", b1ok)
check("DEGENERATE: a nonzero phi _|_ segment has ||phi||_A = 0 (rank-1 seminorm)", b1deg)


# ======================================================================= #
print("=" * 74)
print("PART C -- THE BINOMIAL SLICE DICHOTOMY (the McMullen-language floor reason):")
print("          every phi gives EITHER a degree-||phi||_A binomial slice s^a - s^b")
print("          (NOT a unit) OR a VANISHING slice (the two unit monomials collide,")
print("          b_1(ker phi)=infty).  NO direction yields a UNIT (single-monomial)")
print("          slice -> no vertex-isolating, finite-small cover.")
print("=" * 74)
c_lens_ok = True       # every nonzero-coeff slice has 1 or 2 distinct degrees... we
c_no_unit = True       # assert NEVER a single monomial (unit) and width-0 => vanish
c_deg_eq = True        # eq (4.3): when width>0 the slice deg-span == ||phi||_A
c_vanish = True        # width-0 directions vanish (cancellation of +1,-1)
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    Delta = X ** E - Y ** o * t
    mon = poly_support(Delta, (X, Y, t))       # {(E,0,0):1, (0,o,1):-1}
    supp = support(mon)
    for phi in itertools.product(range(-2, 3), repeat=3):
        if phi == (0, 0, 0):
            continue
        sl = mcmullen_slice(mon, phi)
        wd = width(supp, phi)
        if len(sl) == 1:                      # a UNIT slice would land here
            c_no_unit = False
        if wd == 0:
            c_vanish &= (len(sl) == 0)        # the two unit monomials cancel -> 0
        else:
            # nonzero slice: exactly the binomial s^a - s^b, deg-span = width
            degspan = (max(sl) - min(sl)) if sl else -1
            c_deg_eq &= (len(sl) == 2 and degspan == wd)
            c_lens_ok &= (len(sl) == 2)
check("width>0 : slice is a BINOMIAL s^a-s^b, deg-span == ||phi||_A  (eq 4.3)", c_deg_eq and c_lens_ok)
check("width=0 (phi _|_ segment): slice VANISHES (b_1(ker phi)=infty)", c_vanish)
check("NO phi gives a UNIT (single-monomial) slice -- the headline NO-GO", c_no_unit)
print("       => a binomial Delta has no vertex-isolating direction: the only")
print("          degree-0 directions kill it.  This is the polytope-geometric reason")
print("          the orbit/period residue never bottoms out small (cf. L1.9).")


# ======================================================================= #
print("=" * 74)
print("PART D -- THE RANK->=2 REQUIREMENT, made concrete: a 2-DIM Newton polytope")
print("          (>=3 non-collinear monomials) DOES have a vertex-isolating / unit")
print("          slice.  Natural rank-1-derived enrichments stay collinear; only a")
print("          genuine independent 3rd modulus / non-abelian twist breaks it.")
print("=" * 74)
# (D1) a genuine trinomial (3 non-collinear monomials, e.g. a 3rd modulus Z=5):
#      Delta_GO = X^E - Y^o t + Z^f t^2  with support (E,0,0,0),(0,o,1,0),(0,0,2,1)
#      in (X,Y,t,Z).  dim N = 2, and SOME phi isolates a single vertex (unit slice).
Z, f = sp.symbols("Z"), 1
sup_go = {(2, 0, 0, 0): 1, (0, 3, 1, 0): -1, (0, 0, 2, 1): 1}   # non-collinear
dim_go = affine_dim(support(sup_go))
# search a phi that makes the slice a single monomial (unit): two monomials must
# collide-and-cancel OR be dominated; with +1,-1 coeffs a clean cancellation exists.
found_unit = False
for phi in itertools.product(range(-3, 4), repeat=4):
    if phi == (0, 0, 0, 0):
        continue
    sl = mcmullen_slice(sup_go, phi)
    if len(sl) == 1 and abs(list(sl.values())[0]) == 1:
        found_unit = True
        break
check("genuine trinomial (3 non-collinear monomials): N is 2-DIMENSIONAL", dim_go == 2)
check("  ...and a vertex-isolating phi gives a UNIT slice (impossible for binomial)", found_unit)

# (D2) the natural rank-1-derived enrichments STAY collinear / binomial:
#      (a) the pair (S,T)/object (D,S,T): the Alexander poly Delta_1=gcd(T,S) is a
#          unit or collinear (PART A); D is a binomial; no non-collinear Delta_G.
#      (b) the within-orbit circulant reduces (based module, R-SW3) to the binomial
#          Delta=X^E-Y^o t.  Concretely: D itself, the 2nd cocycle's D-analog, and
#          Delta_1 all have polytope dim <= 1.
d2 = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3), (3, 1, 1, 2, 2)]:
    S, T = ST(w)
    g = sp.gcd(sp.Poly(S, X, Y), sp.Poly(T, X, Y)).as_expr()
    dims = [
        affine_dim(support(poly_support(Dker(w), (X, Y)))),          # D
        affine_dim(support(poly_support(X ** sum(w) - Y ** len(w) * t, (X, Y, t)))),  # cycle
        affine_dim(support(poly_support(g, (X, Y)))),                # Delta_1
    ]
    d2 &= all(d <= 1 for d in dims)
check("natural enrichments (D, cycle-Delta, Delta_1=gcd(T,S)) all have N dim <= 1", d2)
print("       => rank-1-derived enrichments CANNOT manufacture a 2-dim polytope.")


# ======================================================================= #
print("=" * 74)
print("PART E -- McMullen's I(G)=m^p.(Delta_G) and the augmentation filtration:")
print("          the cores live in m^1 \\ m^2, with m/m^2 leading term = the L1.5")
print("          cup product -- consistent with p=1.  (Honest mismatch on <T,S>.)")
print("=" * 74)


def m_lin(fexpr):
    """m/m^2 linearization (cX,cY) of f with f(1,1)=0:  f == cX(X-1)+cY(Y-1) mod m^2."""
    f = sp.expand(fexpr)
    cX = sp.expand(sp.diff(f, X)).subs({X: 1, Y: 1})
    cY = sp.expand(sp.diff(f, Y)).subs({X: 1, Y: 1})
    return sp.Integer(cX), sp.Integer(cY)


# (E1) every core and D lie in m  (augmentation epsilon: X,Y -> 1 kills them).
e1 = True
for u, v in [((1,), (2,)), ((1, 2), (3,)), ((2, 1), (1, 2)), ((3, 1, 2), (2, 3))]:
    e1 &= (sp.expand(core_C(u, v)).subs({X: 1, Y: 1}) == 0)
for w in WORDS:
    e1 &= (sp.expand(Dker(w)).subs({X: 1, Y: 1}) == 0)
check("every core C(u,v) and every D lie in m = <X-1,Y-1>  (so I(G) ⊆ m, p>=1)", e1)

# (E2) D in m \ m^2 with linearization E(X-1) - o(Y-1)  (the (E,o) cup-product vector).
e2 = True
for w in WORDS:
    E, o = sum(w), len(w)
    cX, cY = m_lin(Dker(w))
    e2 &= (cX == E and cY == -o and (E, o) != (0, 0))
check("D in m \\ m^2 : linearization E(X-1) - o(Y-1)  [the (E,o) cup-product vector]", e2)

# (E3) core C(u,v) in m \ m^2 with m/m^2 class = (E_u o_v - E_v o_u)(X-1) [cup product];
#      the Y-component vanishes identically.  Generic nonzero => cores in m^1 \ m^2 => p=1.
e3 = True
e3_nonzero = False
for u, v in [((1,), (2,)), ((1, 2), (3,)), ((2, 1), (1, 2)), ((3, 1, 2), (2, 3)),
             ((1, 2, 3), (2, 1))]:
    Eu, ou, Ev, ov = sum(u), len(u), sum(v), len(v)
    cup = Eu * ov - Ev * ou
    cX, cY = m_lin(core_C(u, v))
    e3 &= (cX == cup and cY == 0)
    if cup != 0:
        e3_nonzero = True
check("core C(u,v) == (E_u o_v - E_v o_u)(X-1) mod m^2  [m-leading term = cup product]", e3)
check("  ...cores generically in m^1 \\ m^2  => augmentation power p=1 (b_3=0 link case)", e3_nonzero)

# (E4) HONEST MISMATCH: <T,S> is NOT inside m (epsilon(S)=o, epsilon(T)=E are != 0),
#      so the m^p factorization attaches to the maximal-minor (core) ideal = McMullen's
#      I(G), NOT to the order ideal <T,S>.  Our free 1-relator Crowell module is not
#      literally a 3-manifold Alexander ideal -> the m^p structure is a translation, not
#      an identity, for <T,S>.
e4 = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    S, T = ST(w)
    e4 &= (sp.expand(S).subs({X: 1, Y: 1}) == len(w)
           and sp.expand(T).subs({X: 1, Y: 1}) == sum(w))
check("MISMATCH (honest): eps(S)=o, eps(T)=E != 0 => <T,S> ⊄ m; m^p attaches to CORES", e4)


# ======================================================================= #
print("=" * 74)
print("PART F -- the degree/torsion split: McMullen norm (RANK) vs Silver-Williams")
print("          Mahler (TORSION).  Both are faces of the SAME degree-1 binomial.")
print("=" * 74)
# deg_t Delta = 1 = ||phi_t||_A (t-direction width); the cover b_1 is constant (=1+p),
# while the FLOOR G = |2^E-3^o| lives in the TORSION (Mahler>1), governed by L1.9.
ff = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3), (3, 1, 1, 2, 2)]:
    E, o = sum(w), len(w)
    Delta = X ** E - Y ** o * t
    supp = support(poly_support(Delta, (X, Y, t)))
    phi_t = (0, 0, 1)                       # the cyclic-cover (t) direction
    # width in the t-direction = deg_t Delta = 1 (minimal nonzero)
    ff &= (width(supp, phi_t) == 1)
    # torsion side: G = |D(2,3)| = |2^E - 3^o|, the McMullen-invisible part
    G = abs(int(Dker(w, 2, 3)))
    ff &= (G == abs(2 ** E - 3 ** o) and G >= 1)
check("deg_t Delta = ||phi_t||_A = 1 (RANK, bounded); G=|2^E-3^o| is the TORSION (L1.9)", ff)
print("       => McMullen's b_1=||phi||_A+p caps the cover-homology RANK at 1+p;")
print("          the floor G is pure TORSION (Mahler>1) -- orthogonal to the norm.")


# ======================================================================= #
print("=" * 74)
print(f"SUMMARY: {len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for x in FAIL:
        print("  FAILED:", x)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
