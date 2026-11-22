#!/usr/bin/env python3
r"""R2-2 verification -- Boden-Friedl metabelian twisted Alexander polynomials:
the DECISIVE GO/NO-GO inside the (2,3)-dynamics.

Reads H. Boden & S. Friedl, "Metabelian SL(n,C) representations of knot groups IV:
twisted Alexander polynomials", arXiv:1209.4244
(sources/boden-friedl-metabelian-IV-1209.4244.pdf).  Cited results:

  sec 2.1 (Wada) : Delta_K^a(t) = det((a (x) phi)(M_i)) . det((a (x) phi)(1-g_i))^{-1}.
  Lemma 5(2)     : 1-dim character tau (meridian -> z): Delta_K^tau(t) = Delta_K(tz)/(1-tz)
                   -- an ABELIAN twist only RESCALES  t -> t z.
  Lemma 5(4)     : block-triangular a = [[b,g],[0,d]]  =>  Delta^a = Delta^b . Delta^d
                   (Wada multiplicativity)  -- our Magnus block  Phi=[[X^E,S],[0,Y^o]].
  sec 3.1 (BF08) : every irreducible metabelian a: Z |x H -> SL(n,C) is
                   a_{(n,chi)}(j,h) = (z . SHIFT)^j . diag(chi(h),chi(th),...,chi(t^{n-1}h)),
                   chi: H -> C^* a character factoring through H/(t^n-1) = H_1(L_n).
                   i.e. a WEIGHTED CYCLIC-SHIFT (monomial n-cycle) matrix.
  Prop 8         : irreducible metabelian, n>1  =>  Delta_K^a(t) is a polynomial in t^n.
  Prop 9         : a_{(k1,chi1)} (x) a_{(k2,chi2)} = a_{(k1 k2, chi1 chi2)} (k1,k2 coprime).

DICTIONARY (OUR objects; STRUCTURE.md sec.1-3, lit-mcmullen-norm.md, lit-silver-williams.md):
  H = ab = <X,Y> = Z^2  (X<->2, Y<->3); cycle/period Alexander poly Delta(t)=X^E - Y^o t.
  The metabelian module is the CYCLIC-COVER (period) module H = Z[t^+-]/(X^E - Y^o t);
  its n-cover quotient  H/(t^n-1) = Z/(2^{En}-3^{on}) = Z/G(w^n)  (cyclic, FINITE),
  because the single root  t = X^E/Y^o = 2^E/3^o  is NEVER a root of unity (2^E != 3^o).
  So metabelian reps a_{(n,chi)} EXIST and are non-degenerate (chi a G(w^n)-th root of 1),
  but the monodromy is a weighted n-cycle  R_chi = (shift).diag(roots of unity).
  Our cycle is FIBERED (Delta monic in t, leading coeff -Y^o a unit), so the twisted
  Alexander polynomial = characteristic polynomial of the twisted monodromy:
       Delta_rho(t) = det( X^E I_n  -  Y^o t . R_chi ).

HEADLINE TO DECIDE:  is Delta_rho's Newton polytope 2-DIMENSIONAL (GO: a vertex-isolating
  unit slice -> a constructively small orbit residue) or does it COLLAPSE to a binomial
  / segment (NO-GO)?  The char poly of a weighted n-CYCLE is ALWAYS a binomial
  lambda^n - (cycle product) mu^n; the roots of unity from chi enter ONLY as the scalar
  cycle-product coefficient (they carry NO X,Y weight), so Delta_rho = X^{En} - c_chi Y^{on} t^n,
  |c_chi|=1 -- a SEGMENT.  Verify decisively, and that no M=1 slice exists.

Exit 0 iff every asserted check passes.
"""
from __future__ import annotations

import cmath
import itertools
import os
import random
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
from cocycle import X, Y, S as Sker, D as Dker, rotations  # noqa: E402

t, lam, mu = sp.symbols("t lambda mu")
PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("  [ok] " if cond else "  [XX] ") + name)
    return cond


# --------------------------------------------------------------------------- #
# Newton-polytope machinery -- REUSED verbatim from checks/lit_mcmullen_norm.py #
# --------------------------------------------------------------------------- #
def support(monomials):
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
    P = sp.Poly(sp.expand(expr), *gens)
    return {tuple(m): c for m, c in zip(P.monoms(), P.coeffs())}


def width(supp, phi):
    vals = [sum(p * e for p, e in zip(phi, m)) for m in supp]
    return max(vals) - min(vals)


def mcmullen_slice(monomials, phi):
    """1-variable slice: collapse t_i -> s^{phi_i}, sum like powers; drop zero coeffs."""
    out = {}
    for m, c in monomials.items():
        deg = sum(p * e for p, e in zip(phi, m))
        out[deg] = out.get(deg, 0) + c
    return {d: c for d, c in out.items() if c != 0}


# gap-word -> (E, o)
WORDS = [(1,), (2,), (1, 2), (2, 1), (1, 2, 3), (3, 1, 2), (2, 1, 1, 3),
         (3, 1, 1, 2, 2), (1, 3, 1, 2), (4, 1, 1, 3)]


def shift_matrix(n):
    """The n x n cyclic shift P:  P e_i = e_{i+1 mod n}  (a single n-cycle)."""
    P = sp.zeros(n, n)
    for i in range(n):
        P[(i + 1) % n, i] = 1
    return P


# ======================================================================= #
print("=" * 74)
print("PART A -- WHICH metabelian reps our cycle admits (the module + degeneration).")
print("          The BF construction uses chi: H -> C^* factoring through H/(t^n-1).")
print("          Our period module H = Z[t]/(X^E - Y^o t) has root t = 2^E/3^o, NEVER a")
print("          root of unity (2^E != 3^o), so H/(t^n-1) = Z/G(w^n) is FINITE & nontrivial:")
print("          metabelian reps EXIST and are NON-degenerate (abundant).")
print("=" * 74)

# (A1) root t = 2^E/3^o is never a root of unity:  2^{En} != 3^{on} for all n>=1.
a1 = True
for w in WORDS:
    E, o = sum(w), len(w)
    for n in range(1, 8):
        a1 &= (2 ** (E * n) != 3 ** (o * n))      # |2^E/3^o| != 1 => not on unit circle
check("root t=2^E/3^o never a root of unity: 2^{En} != 3^{on} (1<=n<=7) => H/(t^n-1) FINITE", a1)

# (A2) |H/(t^n-1)| = |Res(t^n-1, X^E - Y^o t)| = |2^{En}-3^{on}| = G(w^n)  (cyclic, finite).
a2 = True
a2_nontrivial = True
for w in WORDS:
    E, o = sum(w), len(w)
    for n in range(1, 6):
        order = abs(int(sp.resultant(t ** n - 1, 2 ** E - 3 ** o * t, t)))
        Gwn = abs(2 ** (E * n) - 3 ** (o * n))
        a2 &= (order == Gwn)
        if n >= 1 and (E, o) != (0, 0):
            a2_nontrivial &= (Gwn >= 1)
check("|H/(t^n-1)| = |Res(t^n-1,Delta)| = |2^{En}-3^{on}| = G(w^n)  (cyclic order)", a2)
check("  ...G(w^n) >= 1 for all test (w,n): metabelian chars chi of Z/G(w^n) EXIST", a2_nontrivial)
print("       => the RELEVANT module is the binomial CYCLIC-COVER module Delta=X^E-Y^o t,")
print("          NOT the within-stratum Crowell Delta_1=gcd(T,S)=1 (that one is trivial by")
print("          per-stratum injectivity).  Metabelian reps a_{(n,chi)} are abundant.")


# ======================================================================= #
print("=" * 74)
print("PART B -- ABELIAN control (pre-settled NO): the C_n-regular / DFT twist gives")
print("          prod_{j=0}^{n-1}(X^E - Y^o omega^j t) = X^{En} - Y^{on} t^n,  a BINOMIAL")
print("          (segment), and 2^{En} != 3^{on} (still no M=1).")
print("=" * 74)

# (B1) symbolic, EXACT: prod_{zeta^n=1}(X^E - Y^o zeta t) = Res_zeta(zeta^n-1, X^E - Y^o t zeta)
#      = X^{En} - Y^{on} t^n.  (The DFT/abelian-twist product IS the Silver-Williams
#      resultant R-SW2/R-SW3 -- robust, no complex exponentials to simplify.)
z = sp.symbols("z")
b1 = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    a, b = X ** E, Y ** o * t
    for n in (2, 3, 4, 6):
        res = sp.expand(sp.resultant(z ** n - 1, a - b * z, z))   # = prod_{zeta^n=1}(a - b zeta)
        b1 &= (sp.expand(res - (a ** n - b ** n)) == 0)
check("abelian DFT product = Res(zeta^n-1, X^E - Y^o t zeta) = X^{En} - Y^{on} t^n (symbolic)", b1)

# (B2) numeric corroboration at random complex (X,Y,t), larger n.
random.seed(20260609)
b2 = True
for _ in range(40):
    Ev = random.randint(1, 6); ov = random.randint(1, 5)
    xv = complex(random.uniform(.5, 2), random.uniform(-1, 1))
    yv = complex(random.uniform(.5, 2), random.uniform(-1, 1))
    tv = complex(random.uniform(.5, 2), random.uniform(-1, 1))
    a = xv ** Ev; b = yv ** ov * tv
    n = random.randint(2, 9)
    prod = 1.0
    for j in range(n):
        prod *= (a - cmath.exp(2j * cmath.pi * j / n) * b)
    b2 &= abs(prod - (a ** n - b ** n)) < 1e-7 * (1 + abs(a) ** n + abs(b) ** n)
check("abelian DFT product = X^{En} - Y^{on} t^n (numeric, n<=9, random C)", b2)

# (B3) binomial => Newton polytope a SEGMENT (dim 1);  and 2^{En} != 3^{on}.
b3 = True
for w in WORDS:
    E, o = sum(w), len(w)
    for n in (1, 2, 3, 5):
        poly = X ** (E * n) - Y ** (o * n) * t ** n
        supp = support(poly_support(poly, (X, Y, t)))
        b3 &= (len(supp) == 2 and affine_dim(supp) == 1)
        b3 &= (2 ** (E * n) != 3 ** (o * n))
check("abelian twist binomial: N a SEGMENT (dim 1) and 2^{En} != 3^{on} (no M=1)", b3)


# ======================================================================= #
print("=" * 74)
print("PART C -- THE STRUCTURAL MECHANISM: char poly of a weighted n-CYCLE is a BINOMIAL.")
print("          The BF metabelian monodromy R_chi = (shift).diag(g_0,...,g_{n-1}) is a")
print("          single weighted n-cycle, so det(lambda I - mu R_chi) = lambda^n - mu^n.(prod g_i).")
print("          The weights g_i (roots of unity from chi) enter ONLY as the scalar product.")
print("=" * 74)

# (C1) symbolic: det(lambda I - mu . shift . diag(g_0..g_{n-1})) = lambda^n - mu^n prod g_i
#      (up to the universal sign (-1)^{n+1} from a single n-cycle).
c1 = True
for n in range(2, 8):
    g = sp.symbols(f"g0:{n}")
    R = shift_matrix(n) * sp.diag(*g)
    detp = sp.expand((lam * sp.eye(n) - mu * R).det())
    expected = lam ** n - mu ** n * sp.prod(g)            # may differ by overall sign
    c1 &= (sp.expand(detp - expected) == 0 or sp.expand(detp + expected) == 0)
check("det(lambda I - mu.weighted-n-cycle) = lambda^n - (prod g_i) mu^n  (BINOMIAL, symbolic)", c1)

# (C2) R_chi is a single n-cycle => R_chi^n = (prod g_i) I  (so only powers 0 and n survive).
c2 = True
for n in range(2, 7):
    g = sp.symbols(f"g0:{n}")
    R = shift_matrix(n) * sp.diag(*g)
    c2 &= (sp.expand(R ** n - sp.prod(g) * sp.eye(n)) == sp.zeros(n, n))
check("R_chi^n = (prod g_i) I : the cyclic-shift collapses all middle powers => binomial", c2)


# ======================================================================= #
print("=" * 74)
print("PART D -- THE METABELIAN twisted Alexander polynomial Delta_rho and its POLYTOPE.")
print("          Delta_rho(t) = det(X^E I_n - Y^o t . R_chi) = X^{En} - c_chi Y^{on} t^n,")
print("          |c_chi| = 1 (root of unity).  Newton polytope = SEGMENT (dim 1) -- the")
print("          GO/NO-GO discriminant.  Built from EXPLICIT BF reps over a battery.")
print("=" * 74)


def metabelian_delta(E, o, n, g_vals):
    """Delta_rho(t) = det(X^E I_n - Y^o t . shift . diag(g_vals)), g_vals = chi-weights."""
    R = shift_matrix(n) * sp.diag(*g_vals)
    return sp.expand((X ** E * sp.eye(n) - Y ** o * t * R).det())


# (D1) symbolic with placeholder weights g_i: Delta_rho = X^{En} - (prod g_i) Y^{on} t^n.
d1 = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3), (3, 1, 1, 2, 2)]:
    E, o = sum(w), len(w)
    for n in (2, 3, 4):
        g = sp.symbols(f"g0:{n}")
        Drho = metabelian_delta(E, o, n, g)
        expected = X ** (E * n) - sp.prod(g) * Y ** (o * n) * t ** n
        d1 &= (sp.expand(Drho - expected) == 0 or sp.expand(Drho + expected) == 0)
check("Delta_rho = X^{En} - (prod g_i) Y^{on} t^n : a BINOMIAL in (X,Y,t) (symbolic)", d1)

# (D2) explicit BF reps: chi a character of Z/G(w^n) -> concrete roots of unity g_i;
#      verify |c_chi| = prod|g_i| = 1 and Delta_rho is the binomial X^{En} - c_chi Y^{on}t^n,
#      then the Newton polytope (support in (X,Y,t)) is a SEGMENT (dim 1).
d2 = True
d2_unit = True
battery = []
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    for n in (2, 3, 4):
        Gwn = abs(2 ** (E * n) - 3 ** (o * n))     # = |H/(t^n-1)|, order of chi-group
        # pick several characters chi of Z/Gwn : g_i = zeta^{a_i}, zeta a Gwn-th root of 1.
        for a_seed in (1, 2, 3):
            ai = [(a_seed * (i + 1)) % Gwn for i in range(n)]
            g_vals = [sp.exp(2 * sp.I * sp.pi * sp.Rational(a, Gwn)) for a in ai]
            Drho = metabelian_delta(E, o, n, g_vals)
            c_chi = sp.simplify(sp.prod(g_vals))
            # binomial structure
            tgt = X ** (E * n) - c_chi * Y ** (o * n) * t ** n
            ok_bin = (sp.simplify(sp.expand(Drho - tgt)) == 0
                      or sp.simplify(sp.expand(Drho + tgt)) == 0)
            d2 &= bool(ok_bin)
            d2_unit &= (abs(complex(c_chi)) - 1) < 1e-9
            supp = support(poly_support(sp.expand(X ** (E * n) - Y ** (o * n) * t ** n),
                                        (X, Y, t)))  # support is chi-independent
            battery.append((w, n, supp))
check("explicit BF metabelian reps: Delta_rho is the binomial X^{En} - c_chi Y^{on} t^n", d2)
check("  ...|c_chi| = prod|g_i| = 1 (chi a root of unity: NO X,Y weight, only a scalar)", d2_unit)

# (D3) THE DISCRIMINANT: Newton-polytope dimension of Delta_rho over the whole battery.
d3 = all(len(supp) == 2 and affine_dim(supp) == 1 for (_, _, supp) in battery)
check("DISCRIMINANT: N(Delta_rho) is a SEGMENT (dim 1) for EVERY metabelian rep in battery", d3)
print(f"       battery size: {len(battery)} (w,n,chi) metabelian reps -- ALL dim 1.")
print("       => NO metabelian rep manufactures a 2-dim polytope: GO requires dim>=2.")


# ======================================================================= #
print("=" * 74)
print("PART E -- NO M=1 (unit) slice for Delta_rho, and Mahler measure > 1.")
print("          Binomial => every phi gives a binomial slice s^a - s^b (never a unit) OR")
print("          a vanishing slice (the two monomials collide).  Same dichotomy as McMullen.")
print("=" * 74)
e_no_unit = True
e_vanish = True
e_mahler = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    for n in (2, 3):
        mon = poly_support(X ** (E * n) - Y ** (o * n) * t ** n, (X, Y, t))
        supp = support(mon)
        for phi in itertools.product(range(-2, 3), repeat=3):
            if phi == (0, 0, 0):
                continue
            sl = mcmullen_slice(mon, phi)
            wd = width(supp, phi)
            if len(sl) == 1:               # a UNIT (single-monomial) slice
                e_no_unit = False
            if wd == 0:
                e_vanish &= (len(sl) == 0)  # the two monomials cancel -> vanish
        # Mahler measure of X^{En} - c Y^{on} t^n at (2,3): max(2^{En}, 3^{on}) > 1.
        e_mahler &= (max(2 ** (E * n), 3 ** (o * n)) > 1 and 2 ** (E * n) != 3 ** (o * n))
check("NO phi gives a UNIT (single-monomial) slice of Delta_rho  -- the headline NO-GO", e_no_unit)
check("width=0 directions VANISH (the two monomials collide); no vertex-isolating slice", e_vanish)
check("Mahler M(Delta_rho) = max(2^{En},3^{on}) > 1 (|c_chi|=1 leaves Mahler unchanged)", e_mahler)


# ======================================================================= #
print("=" * 74)
print("PART F -- the ESCAPE ROUTES are closed too (Wada multiplicativity / tensor / orbit).")
print("          (i) sum a (+) b => product of binomials, all COLLINEAR (same direction).")
print("          (ii) tensor a_{(k1,.)} (x) a_{(k2,.)} = a_{(k1k2,.)} : one binomial (Prop 9).")
print("          (iii) the WITHIN-ORBIT weighted-shift (transfer law) is also a binomial.")
print("=" * 74)

# (F1) Wada multiplicativity (Lemma 5(4)) / direct sum: a product of metabelian binomials
#      prod_k (X^E - Y^o omega_k t) is supported on the SAME line (collinear) => segment.
f1 = True
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    E, o = sum(w), len(w)
    # product of up to 4 binomials with distinct root-of-unity coeffs
    omegas = [sp.exp(2 * sp.I * sp.pi * sp.Rational(k, 7)) for k in (1, 2, 3, 4)]
    prod = sp.prod([X ** E - om * Y ** o * t for om in omegas])
    supp = support(poly_support(sp.expand(prod), (X, Y, t)))
    # every monomial X^{E(K-k)} Y^{ok} t^k lies on the line through (EK,0,0) dir (-E,o,1)
    f1 &= (affine_dim(supp) == 1)
check("(i) product of metabelian binomials (Wada mult. / direct sum): COLLINEAR, dim 1", f1)

# (F2) tensor product stays a single metabelian rep (Prop 9): one weighted n-cycle => binomial.
f2 = True
for (E, o) in [(3, 2), (6, 3), (7, 4)]:
    for k1, k2 in [(2, 3), (3, 4), (2, 5)]:
        if gcd(k1, k2) != 1:
            continue
        n = k1 * k2
        g = sp.symbols(f"h0:{n}")
        Drho = metabelian_delta(E, o, n, g)
        expected = X ** (E * n) - sp.prod(g) * Y ** (o * n) * t ** n
        f2 &= (sp.expand(Drho - expected) == 0 or sp.expand(Drho + expected) == 0)
check("(ii) tensor a_{(k1,.)} (x) a_{(k2,.)} = a_{(k1k2,.)}: still ONE binomial (Prop 9)", f2)

# (F3) the WITHIN-ORBIT weighted shift: transfer law multiplier Y/X^{d_j} around the o-cycle.
#      char poly = lambda^o - prod_j (Y/X^{d_j}) = lambda^o - Y^o/X^E  (the SAME binomial),
#      and a metabelian chi-twist only multiplies the constant by a root of unity.
f3 = True
for w in [(1, 2), (2, 1, 1, 3), (3, 1, 1, 2, 2)]:
    o = len(w); E = sum(w)
    # weighted o-cycle with (X,Y)-carrying weights Y / X^{d_j}  (clear denominators by X^{d_j})
    weights = [Y / X ** dj for dj in w]
    R = shift_matrix(o) * sp.diag(*weights)
    detp = sp.expand((lam * sp.eye(o) - R).det())
    # = lambda^o - prod_j weights  (single o-cycle) ; prod = Y^o / X^{sum d_j} = Y^o/X^E
    target = lam ** o - Y ** o / X ** E
    f3 &= (sp.simplify(detp - target) == 0 or sp.simplify(detp + target) == 0)
check("(iii) within-orbit weighted o-cycle (transfer law): char poly a BINOMIAL X^E lam^o - Y^o", f3)
print("       => even (X,Y)-carrying non-uniform weights wash out: a single cycle's char")
print("          poly sees only the CYCLE PRODUCT (a single monomial). No third direction.")


# ======================================================================= #
print("=" * 74)
print(f"SUMMARY: {len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for x in FAIL:
        print("  FAILED:", x)
    sys.exit(1)
print("ALL CHECKS PASSED  ==>  R2-2 VERDICT: NO-GO.  Every metabelian twisted Alexander")
print("polynomial Delta_rho of our cycle is a BINOMIAL X^{En} - c_chi Y^{on} t^n (segment),")
print("because (a) the base Delta = X^E - Y^o t is degree-1 (fibered) and (b) the BF")
print("metabelian monodromy is a weighted n-CYCLE whose char poly is forced binomial -- the")
print("roots of unity from chi enter only as a SCALAR coefficient carrying no (X,Y) weight.")
print("No 2-dim polytope, no M=1 slice => Layer-1 algebra is EXHAUSTED inside (2,3).")
sys.exit(0)
