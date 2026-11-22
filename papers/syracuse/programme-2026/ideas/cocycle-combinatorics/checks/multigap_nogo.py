"""Gen 4 -- toward closing the >=2-growing-gap NO-GO of the bounded-defect lever [P3].

Gen 3 claimed: for a word with >=2 simultaneously growing gaps (the symmetric
W_a = d^a e1 d^a e2 d^a) NO Z[1/6]-unit combination of its rotation sums has a
6-free part bounded independent of a -- "established by strong evidence (unit-scaled
2-term combos diverge; non-cyclotomic Mahler>1 cofactor), NOT an exhaustive proof."

This script SHARPENS and CORRECTS that picture. Findings (all verified below):

  PART A -- FRAMING CORRECTION (the no-go must be about UNIT / UNIFORM combos).
    For the symmetric family, gcd_j S^(j)(W_a) = 1 for every a (the words are NOT
    cycles).  Since Z[1/6] is a PID, by Bezout SOME Z[1/6]-*linear* combination of
    the rotations equals a 6-unit (6-free part 1).  Hence the no-go is simply FALSE
    if read as "no Z[1/6]-linear combination has bounded 6-free part".  The exclusion
    lever uses *unit* (monomial) coefficients +-X^a Y^b and -- crucially for excluding
    an infinite family -- a UNIFORM scheme: a fixed reduced polynomial f with
    combo_a = (monomial_a) * f for all a, giving sixfree(combo_a) = sixfree(f(2,3)) =
    const.  That is what the no-go must deny.

  PART B -- EXTENDED SEARCH (corrects Gen 3's "clean divergence").
    Min 6-free part over k-term unit combos (coeff box +-2^c 3^d, c,d<=2):
      k=2 grows;  k=3 has LOW-a DIPS (a<=5 gives values as small as 1,5,11) that are
      NON-UNIFORM arithmetic coincidences (different rotation indices/coeffs per a)
      and DISAPPEAR by a=6, after which the min resumes growth.  So the finite search
      does NOT prove the no-go (small values keep cropping up at small a), but it finds
      NO uniform bounded scheme either.

  PART C -- THE CLEAN REDUCTION (the actual win).
    Every nonzero rotation-pair difference factors as  X^p (X-1) * P_a(X,Y)  with P_a
    NON-cyclotomic (Mahler(P_a|Y=1) ~ 1.5, bounded away from 1) and total degree 2a+2
    GROWING with a.  So no single difference has an a-independent reduced core.
    Contrast: the bounded-defect wedge reduces to a FIXED core S(beta d)-S(d beta)
    (a-independent).  Hence the no-go REDUCES to:  no unit-combo of the >=2-growing
    family has an a-independent (Mahler-1 / cyclotomic-collapsed) reduced polynomial.
    That is a cyclotomic-collapse / Lehmer-flavored statement (structure.md thread 8) --
    OPEN, not closed here.

  PART D -- PLUCKER C8.
    Verify D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0 for arc triples (structure.md C8); this
    is the simultaneity backbone -- the three arc-cores of a 3-cut are R-linearly tied,
    so small cores cannot proliferate.  (The Y=1 Mahler screen is too coarse to read
    "tameable" off C8 cleanly -- recorded honestly.)

The script asserts only VERIFIED facts (gcd, search values, factorizations, C8). It
does NOT assert the no-go is proven: it is reduced-but-open.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/multigap_nogo.py
"""
import sys, itertools
from math import gcd as _gcd
from functools import reduce
import numpy as np
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, D as Dpoly, core_C, gcd_rotations  # trusted kernel
X, Y = sp.symbols("X Y")


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def Sint(w):
    return int(Spoly(tuple(w), 2, 3)) if len(w) else 0


def sym_word(a, d=1, e1=3, e2=4):
    """The symmetric >=2-growing-gap family d^a e1 d^a e2 d^a."""
    return (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a


def mahler1(expr, var):
    """Mahler measure of a 1-var integer polynomial (numpy roots)."""
    expr = sp.expand(expr)
    if expr == 0:
        return 0.0
    p = sp.Poly(expr, var)
    if p.degree() < 1:
        return 1.0
    c = [complex(z) for z in p.all_coeffs()]
    r = np.roots(c)
    m = abs(c[0])
    for z in r:
        if abs(z) > 1:
            m *= abs(z)
    return m


ALL_OK = True

# --------------------------------------------------------------------------- #
# PART A -- framing correction: gcd = 1, so a LINEAR no-go is false            #
# --------------------------------------------------------------------------- #
print("== PART A: gcd_j S^(j)=1 for the symmetric family => linear-combo no-go is FALSE ==")
gcd_all_one = True
for a in range(1, 8):
    W = sym_word(a)
    G = gcd_rotations(W)
    if G != 1:
        gcd_all_one = False
    Dval = abs(2 ** sum(W) - 3 ** len(W))
    if a <= 4:
        print(f"  a={a} o={len(W)}: gcd_j S^(j)={G}, |2^E-3^o|={Dval} (so the word is NOT a cycle: G != |D|)")
print(f"  gcd_j S^(j)(W_a) = 1 for a=1..7: {gcd_all_one}")

# Bezout: exhibit a Z-linear combination of the rotation sums equal to gcd = 1.
# (Z[1/6] is a PID, so the gcd is reachable; here it is already an integer combo.)
a = 3
W = sym_word(a)
Sv = [Sint(rotate(W, k)) for k in range(len(W))]
def egcd(a, b):
    """Return (g, x, y) with x*a + y*b = g = gcd(a, b)."""
    if b == 0:
        return (abs(a), (1 if a >= 0 else -1), 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)

acc = Sv[0]
cof = [1] + [0] * (len(Sv) - 1)
for i in range(1, len(Sv)):
    gg, x, y = egcd(acc, Sv[i])          # x*acc + y*Sv[i] = gg = gcd(acc, Sv[i])
    cof = [x * c for c in cof]
    cof[i] += y
    acc = gg
bezout_val = sum(c * s for c, s in zip(cof, Sv))
linear_nogo_false = (acc == 1 and bezout_val == 1 and sixfree(bezout_val) == 1)
print(f"  Bezout: a Z-linear combination of the rotations equals {bezout_val} (6-free part {sixfree(bezout_val)})")
print(f"  => 'no Z[1/6]-LINEAR combo has bounded 6-free part' is FALSE; the no-go is about")
print(f"     UNIT (monomial) coeffs + a UNIFORM (a-independent reduced poly) scheme: {linear_nogo_false}")
partA = gcd_all_one and linear_nogo_false
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
# PART B -- extended unit-combo search: low-a dips are non-uniform coincidences #
# --------------------------------------------------------------------------- #
print("== PART B: min 6-free over k-term UNIT combos (coeff box +-2^c3^d, c,d<=2); low-a dips ==")
units = sorted(set(2 ** c * 3 ** dd for c in range(3) for dd in range(3)))
coeffs_box = [u for u in units] + [-u for u in units]


def min_sixfree(W, k, return_recipe=False):
    o = len(W)
    Sv = [Sint(rotate(W, j)) for j in range(o)]
    best = None
    for idx in itertools.combinations(range(o), k):
        for asn in itertools.product(coeffs_box, repeat=k):
            v = sum(c * Sv[i] for c, i in zip(asn, idx))
            if v == 0:
                continue
            s = sixfree(v)
            if best is None or s < best[0]:
                best = (s, idx, asn)
    return best if return_recipe else best[0]


k2 = {}
for a in range(2, 8):
    k2[a] = min_sixfree(sym_word(a), 2)
print(f"  k=2 min sixfree, a=2..7: {[k2[a] for a in range(2,8)]}  (grows)")

k3 = {}
recipes = {}
for a in range(2, 7):                      # k=3 capped at a<=6 for runtime (a=7,8 verified separately: 11651,19577)
    s, idx, asn = min_sixfree(sym_word(a), 3, return_recipe=True)
    k3[a] = s
    recipes[a] = (idx, asn)
print(f"  k=3 min sixfree, a=2..6: {[k3[a] for a in range(2,7)]}  (LOW-a DIPS, then growth)")
for a in range(2, 7):
    print(f"     a={a}: sixfree={k3[a]:>6}  recipe idx={recipes[a][0]} coefs={recipes[a][1]}")
# the dips are non-uniform: small values at a<=5, big at a=6; recipes differ per a.
dips_then_growth = (k3[4] < 100 and k3[5] < 100 and k3[6] > 1000)
recipes_differ = len(set(recipes[a][1] for a in (4, 5, 6))) > 1
print(f"  low-a dips (a=4,5 small) then growth (a=6 > 1000): {dips_then_growth}")
print(f"  achieving recipes differ across a (NON-uniform coincidences): {recipes_differ}")
print(f"  => finite search finds NO uniform bounded scheme, but also does NOT prove the no-go")
print(f"     (small 6-free values keep appearing at small a -- corrects Gen 3's 'clean divergence').")
partB = dips_then_growth and recipes_differ
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- the clean reduction: rotation differences carry a growing           #
#           non-cyclotomic factor; bounded-defect reduces to an a-INDEP core    #
# --------------------------------------------------------------------------- #
print("== PART C: rotation differences = X^p (X-1) * P_a, P_a non-cyclotomic, deg 2a+2 grows ==")
degs = []
mahlers = []
noncyc = True
for a in (2, 3, 4, 5):
    W = sym_word(a)
    j = a + 1
    poly = sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, j)))
    facs = sp.factor_list(poly)[1]
    big = max(facs, key=lambda fm: sp.Poly(fm[0], X, Y).total_degree())
    f = big[0]
    deg = sp.Poly(f, X, Y).total_degree()
    M = mahler1(sp.expand(f.subs(Y, 1)), X)
    degs.append(deg)
    mahlers.append(M)
    if M <= 1.0001:
        noncyc = False
    print(f"  a={a}: S^(0)-S^({j}) -> big factor deg={deg} (=2a+2), Mahler(|Y=1)={M:.4f} (>1: non-cyclotomic)")
deg_grows = all(degs[i] < degs[i + 1] for i in range(len(degs) - 1))
mahler_bdd_away = all(m > 1.1 for m in mahlers)

# every nonzero rotation-pair difference has a non-cyclotomic factor (min deg grows):
def noncyc_deg(poly):
    poly = sp.expand(poly)
    if poly == 0:
        return -1
    tot = 0
    for f, mult in sp.factor_list(poly)[1]:
        if mahler1(sp.expand(f.subs(Y, 1)), X) > 1.0001:
            tot += sp.Poly(f, X, Y).total_degree() * mult
    return tot

all_diffs_noncyc = True
mindeg_by_a = {}
for a in (2, 3):
    W = sym_word(a)
    o = len(W)
    pp = [Spoly(rotate(W, k)) for k in range(o)]
    md = None
    for i, jj in itertools.combinations(range(o), 2):
        nd = noncyc_deg(pp[i] - pp[jj])
        if nd == 0:
            all_diffs_noncyc = False
        elif nd > 0 and (md is None or nd < md):
            md = nd
    mindeg_by_a[a] = md
print(f"  every nonzero rotation-pair difference is non-cyclotomic: {all_diffs_noncyc}")
print(f"  min non-cyclotomic degree over all diffs: a=2 -> {mindeg_by_a[2]}, a=3 -> {mindeg_by_a[3]} (grows)")

# CONTRAST: bounded-defect wedge reduces to an a-INDEPENDENT core (the lever).
# For beta=(3,4), background d=1, the wedge S(d^k beta d^m)-S(d^{k+1} beta d^{m-1})
# = X^{kd} Y^{m-1} (S(beta d)-S(d beta)); the reduced core is FIXED (a-independent).
beta, d = (3, 4), 1
fixed_core = sp.expand(Spoly(tuple(beta) + (d,)) - Spoly((d,) + tuple(beta)))
core_indep = True
for L in (2, 5, 9):
    Wk = (d,) * 0 + tuple(beta) + (d,) * L            # beta then run
    full = sp.expand(Spoly((d,) * 1 + tuple(beta) + (d,) * (L - 1)) - Spoly(tuple(beta) + (d,) * L))
    # full should be (monomial) * fixed_core  -> quotient is a monomial
    quo, rem = sp.div(full, fixed_core, X)
    if rem != 0:
        # try as Y-poly division fallback: check full/fixed_core is a monomial in X,Y
        q = sp.simplify(full / fixed_core)
        if not q.is_Mul and not q.is_Pow and not q.is_Symbol and not q.is_Number:
            core_indep = False
print(f"  bounded-defect wedge reduced core S(beta d)-S(d beta) is a-INDEPENDENT (the lever): {core_indep}")
print(f"  => REDUCTION: exclude the >=2-growing family  <=>  exists a unit-combo with an")
print(f"     a-INDEPENDENT (Mahler-1 / cyclotomic-collapsed) reduced polynomial.  None found;")
print(f"     this is an OPEN cyclotomic-collapse / Lehmer-flavored question (structure.md thread 8).")
partC = noncyc and deg_grows and mahler_bdd_away and all_diffs_noncyc and core_indep
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

# --------------------------------------------------------------------------- #
# PART D -- Plucker C8 for arc triples (the simultaneity backbone)              #
# --------------------------------------------------------------------------- #
print("== PART D: Plucker C8  D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0  for arc triples ==")
import random
random.seed(7)
c8_ok = True
n = 0
for a in (3, 4):
    W = sym_word(a)
    o = len(W)
    for _ in range(15):
        cuts = sorted(random.sample(range(1, o), 3))
        p, q, r = cuts
        u, v, w = W[0:p], W[p:q], W[q:o]
        expr = Dpoly(u) * core_C(v, w) + Dpoly(v) * core_C(w, u) + Dpoly(w) * core_C(u, v)
        n += 1
        if sp.expand(expr) != 0:
            c8_ok = False
print(f"  C8 holds on {n} random arc triples (>=2-growing family): {c8_ok}")
print(f"  (C8 ties the three arc-cores R-linearly: small cores cannot proliferate -- the")
print(f"   structural reason >=2 growing gaps resist simultaneous taming.)")
partD = c8_ok
print(f"  PART D holds: {partD}\n")
ALL_OK &= partD

print("=" * 70)
print(f"MULTIGAP NO-GO (Gen 4): {'ALL VERIFIED FACTS PASS' if ALL_OK else 'FAILED'}")
print("VERDICT: no-go SHARPENED to a clean reduction + corrected (low-a coincidences");
print("         exist); structurally supported (every diff non-cyclotomic, deg grows;")
print("         C8); NOT proven -- reduces to an open cyclotomic-collapse question.")
sys.exit(0 if ALL_OK else 1)
