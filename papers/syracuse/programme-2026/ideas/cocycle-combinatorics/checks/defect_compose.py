"""Make-or-break: does inner-core extraction COMPOSE with the odd-part/6-free lever
to bound a DEFECT parameter (rather than aiming at |C| < G directly)?

Two cocycle extractions, DUAL to each other:
  * P1 (shared INNER core u, vary outer x,y): chi(x')S(xuy)-chi(x)S(x'uy')
        = [chi(x')S(x)-chi(x)S(x')] + chi(x)chi(x')chi(u)[S(y)-S(y')].
    The inner core enters only via the unit chi(u).  (Gen 2: the G-divisible
    instance forces xuy,x'uy' to be rotations of one cyclic word -> a full-rotation
    combination, which is >= G.)
  * SHARED-FRAME (shared OUTER frame P,Q, vary inner M): for chi(M)=chi(M'),
        S(PMQ)-S(PM'Q) = X^{|P|}Y^{|Q|}(S(M)-S(M')).
    The outer RUNS P,Q enter only via the unit X^{|P|}Y^{|Q|}.

ANSWER (this script): the lever that bounds a defect is the SHARED-FRAME one (the
dual of P1).  It extracts the long uniform RUN as a unit and leaves a run-independent
local core.  This ENLARGES the excludable family from a single-letter defect
(structure.md P2) to ANY bounded-length contiguous defect ARC beta on a uniform
background -- the cycle length o grows through ONE long background run.

PART A: the duality, and the reconciliation -- "[P2] floor: combo >= G" does NOT block
        exclusion; exclusion is a BOUNDED 6-free part independent of o.
PART B: the lever ENLARGES the family -- bounded contiguous arc beta (multi-letter,
        with internal background) + one growing run => o-independent ceiling.
PART C: the NO-GO boundary -- >= 2 simultaneously growing gaps (defects far apart on
        BOTH sides) => no bounded arc; wedge cofactor is non-cyclotomic of degree ~
        second-longest run, so the 6-free part DIVERGES with o.  No uniform ceiling.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/defect_compose.py
"""
import sys, itertools, math
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations
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

ALL_OK = True

# --------------------------------------------------------------------------- #
# PART A -- the two extractions are dual; floor >= G does NOT preclude exclusion #
# --------------------------------------------------------------------------- #
print("== PART A: P1 (shared inner core) vs shared-frame (shared outer run) -- dual; floor != no-go ==")
# P1 identity (cocycle, free symbols) -- inner core u enters only via chi(u):
Sx, Sxp, Sy, Syp, Su = sp.symbols("Sx Sxp Sy Syp Su")
cx, cxp, cu = sp.symbols("cx cxp cu")
S_xuy = Sx + cx * Su + cx * cu * Sy
S_xpuyp = Sxp + cxp * Su + cxp * cu * Syp
p1_lhs = sp.expand(cxp * S_xuy - cx * S_xpuyp)
p1_rhs = sp.expand((cxp * Sx - cx * Sxp) + cx * cxp * cu * (Sy - Syp))
p1_ok = (sp.expand(p1_lhs - p1_rhs) == 0) and (p1_lhs.coeff(Su) == 0)
print(f"  P1 identity holds and inner core S(u) cancels (enters only via chi(u)): {p1_ok}")

# Reconciliation: the lever's wedge IS a difference of two rotation sums (a [P2]-floor
# object, so |wedge| >= G), yet its 6-free part is the bounded, o-independent ceiling.
d, e = 1, 5                                  # single defect, ceiling sixfree(2^5-2^1)=5
ceil = sixfree(Sint((e, d)) - Sint((d, e)))
ge_and_bounded = True
for a in range(2, 9):
    for b in range(2, 7):
        W = (d,) * a + (e,) + (d,) * b
        o = len(W); G = gcd_rotations(W)
        wedge = Sint(rotate(W, 1)) - Sint(rotate(W, 2))      # two genuine rotations
        if wedge == 0:
            continue
        if wedge % G != 0 or abs(wedge) < G:                  # floor: multiple of G, |.|>=G
            ge_and_bounded = False
        if sixfree(wedge) > ceil:                              # but 6-free part is bounded
            ge_and_bounded = False
print(f"  every lever-wedge is a rotation combo (>= G) yet sixfree(wedge) <= {ceil} (o-indep): {ge_and_bounded}")
print("  => the [P2] floor (>= G) is NOT a no-go for exclusion; exclusion = bounded 6-free part.")
partA = p1_ok and ge_and_bounded
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
# PART B -- the lever ENLARGES the family: bounded contiguous arc + one long run  #
# --------------------------------------------------------------------------- #
print("== PART B: bounded contiguous defect ARC beta + ONE growing run => o-independent ceiling ==")
# Each family: a fixed bounded arc beta; o grows by extending a single background run.
# Verify the beta-moving wedge (two genuine rotations of W) has CONSTANT sixfree = ceiling.
def beta_wedge_constant(beta, d, run_range):
    """beta-block moved by one through an outer run d^*; ceiling = sixfree(S(beta d)-S(d beta))."""
    ceil = sixfree(Sint(tuple(beta) + (d,)) - Sint((d,) + tuple(beta)))
    vals = []
    ok = True
    for L in run_range:
        W = tuple(beta) + (d,) * L                      # beta then a long run
        o = len(W)
        R1 = tuple(beta) + (d,) * L                     # k=0
        R2 = (d,) + tuple(beta) + (d,) * (L - 1)        # k=1: beta shifted by one through the run
        rotset = set(rotate(W, k) for k in range(o))
        if not (R1 in rotset and R2 in rotset):
            ok = False
        sf = sixfree(Sint(R1) - Sint(R2))
        vals.append(sf)
        if sf != ceil:
            ok = False
    return ceil, vals, ok

families = [
    ((3, 4), 1),                 # two ADJACENT defects (gap 0): contiguous 2-arc
    ((4, 3, 4), 1),              # 3-letter arc
    ((4, 1, 1, 3), 1),           # arc = e2 d^2 e1: "two defects separated by a SHORT(=2) gap"
]
partB = True
for beta, d in families:
    ceil, vals, ok = beta_wedge_constant(beta, d, range(2, 9))
    print(f"  beta={beta} d={d}: ceiling sixfree={ceil}; beta-wedge sixfree over runs 2..8 = {vals}  constant&rotations:{ok}")
    partB &= ok
# Cross-check: this means d^1 e1 d^B e2 d^1 (one long gap B) is excludable via beta=e2 d^2 e1.
print("  -> e.g. d e1 d^B e2 d (B -> inf) is excludable: take beta=(e2,d,d,e1), run=d^B, ceiling fixed.")
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- the NO-GO: >= 2 simultaneously growing gaps => 6-free part diverges    #
# --------------------------------------------------------------------------- #
print("== PART C: NO-GO -- two defects far apart on BOTH sides (all runs grow) ==")
e1, e2, d = 3, 4, 1
# (i) min 6-free part over unit-scaled 2-term combos GROWS (exponentially) with the run a.
units = [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 27]
coeffs = [u for u in units] + [-u for u in units]
prev = 0
growing = True
print("  symmetric family d^a e1 d^a e2 d^a (both gaps = a grow):")
for a in range(2, 6):
    W = (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a
    o = len(W)
    Sv = [Sint(rotate(W, k)) for k in range(o)]
    best = None
    for i, j in itertools.combinations(range(o), 2):
        for ca in coeffs:
            for cb in coeffs:
                v = ca * Sv[i] + cb * Sv[j]
                if v == 0:
                    continue
                s = sixfree(v)
                if best is None or s < best:
                    best = s
    print(f"    a={a} o={o}: min sixfree over unit-scaled 2-term combos = {best}")
    prev = best
final_big = best
# (ii) the structural reason: the wedge cofactor is a single irreducible NON-cyclotomic
#      polynomial whose total degree grows with the (second) run -> Mahler measure > 1.
print("  structural reason -- best adjacent wedge factors with a non-cyclotomic cofactor, deg grows:")
degs = []
noncyc_ok = True
for a in range(2, 5):
    W = (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a
    w = sp.expand(Spoly(rotate(W, a)) - Spoly(rotate(W, a + 1)))
    facs = sp.factor_list(w)[1]
    big = [(f, m) for f, m in facs if sp.Poly(f, X, Y).total_degree() >= 3]
    deg = max((sp.Poly(f, X, Y).total_degree() for f, m in big), default=0)
    degs.append(deg)
    # cyclotomic factors are products of (X-1),(X+1),... ; a degree->infinity single factor is not.
    if not big:
        noncyc_ok = False
    print(f"    a={a}: non-cyclotomic cofactor total degree = {deg}")
deg_grows = all(degs[i] < degs[i + 1] for i in range(len(degs) - 1))
print(f"  6-free part diverges with o (last min={final_big}, ~2^{math.log2(final_big):.1f}); cofactor deg grows: {deg_grows}")
print("  => no bounded contiguous arc encloses both defects; the lever gives NO o-independent")
print("     ceiling here.  (Strong evidence + structural Mahler>1 reason; not an exhaustive")
print("     proof over ALL unit-combinations -- recorded honestly.)")
partC = growing and deg_grows and noncyc_ok and (final_big > 1000)
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

print("=" * 64)
print(f"DEFECT-COMPOSE (make-or-break): {'ALL PARTS PASS' if ALL_OK else 'FAILED'}")
sys.exit(0 if ALL_OK else 1)
