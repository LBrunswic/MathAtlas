"""The G-divisibility bridge for principle [P1] (the make-or-break question).

When is  L := chi(x') S(xuy) - chi(x) S(x'uy')  divisible by the shift-gcd
G = gcd_j S^{(j)} (= |D| on a genuine cycle, coprime to 6)?

SUFFICIENT CONSTRUCTION (the bridge):  let W = u R be a cyclic word in which the
inner core u occurs ONCE; pick two splits R = R1 R2 = R1' R2'.  Then
    xuy   = R2  u R1   = rotate(W, len(u)+len(R1))
    x'uy' = R2' u R1'  = rotate(W, len(u)+len(R1'))
are BOTH rotations of the single cyclic word W, with
    x=R2, y=R1, x'=R2', y'=R1'   -- and NONE of x,x',y,y' contains u.
Since G | S(any rotation of W) and chi(.) is a unit (G perp 6), G | L.

Combined with P1, L equals the boundary term
    B = [chi(x') S(x) - chi(x) S(x')] + chi(x) chi(x') chi(u) [S(y) - S(y')],
in which the (arbitrarily long) core u enters ONLY through the unit chi(u).
=> the divisibility constraint  G | B  is *blind to u beyond its chi-signature*.

This script verifies, over many (u, R, split, split') instances:
  (1) xuy and x'uy' are genuine rotations of one cyclic word W;
  (2) the P1 identity L == B numerically (cross-check of the certificate);
  (3) G | L  in Z[1/6] (numerator divisible by G; denominator 6-smooth);
  (4) u-invariance: for fixed (|u|,len u) and fixed R-splits, the numerator
      that G divides is IDENTICAL across different cores u (the elimination);
  (5) CONTROL: when x'uy' is NOT a rotation of xuy, G | L generally FAILS.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/g_divisibility_bridge.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, gcd_rotations, rotate

def Sk(w):  return int(Spoly(tuple(w), 2, 3)) if len(w) else 0
def lenw(w): return len(w)
def sumw(w): return sum(w)
def chi(w):  return sp.Rational(2) ** sumw(w) / sp.Rational(3) ** lenw(w)
def Su(w):
    n = len(w)
    return sp.Rational(Sk(w), 3 ** (n - 1)) if n >= 1 else sp.Integer(0)

def is_6smooth(n):
    n = abs(int(n))
    if n == 0: return True
    for p in (2, 3):
        while n % p == 0: n //= p
    return n == 1

def L_comb(x, xp, y, yp, u):
    return chi(xp) * Su(tuple(x)+tuple(u)+tuple(y)) \
         - chi(x)  * Su(tuple(xp)+tuple(u)+tuple(yp))

def B_boundary(x, xp, y, yp, u):
    return (chi(xp)*Su(x) - chi(x)*Su(xp)) \
         + chi(x)*chi(xp)*chi(u)*(Su(y) - Su(yp))

def g_divides(r, G):
    """G | r in Z[1/6]:  r = N / (2^a 3^b) lowest terms, return (denom 6-smooth, N % G == 0)."""
    r = sp.Rational(r)
    return is_6smooth(r.q), (r.p % G == 0)

ALL_OK = True
letters = (1, 2, 3, 4)

# --------------------------------------------------------------------------- #
# (1)-(3) the bridge family W = u R, two splits                               #
# --------------------------------------------------------------------------- #
print("== bridge family  W = u R,  splits R=R1R2=R1'R2'  ==")
def words_upto(maxlen):
    out = []
    for L in range(0, maxlen + 1):
        out += list(itertools.product(letters, repeat=L)) if L else [()]
    return out

cores = [(), (1,), (2,), (1, 2), (3, 1), (2, 2, 1)]
Rs = [w for w in words_upto(4) if len(w) >= 2]   # need >=2 to have two interior splits

n_inst = 0
rot_ok = ident_ok = gdiv_ok = True
ratios = []   # |numerator| / G  -- exclusion gauge
for u in cores:
    for R in Rs:
        W = tuple(u) + tuple(R)
        G = gcd_rotations(W)
        m = len(u)
        # two distinct splits of R
        for j, jp in itertools.combinations(range(len(R) + 1), 2):
            x, y   = R[j:],  R[:j]
            xp, yp = R[jp:], R[:jp]
            xuy   = tuple(x) + tuple(u) + tuple(y)
            xpuyp = tuple(xp) + tuple(u) + tuple(yp)
            # (1) rotation structure
            if not (xuy == rotate(W, m + len(y)) and xpuyp == rotate(W, m + len(yp))):
                rot_ok = False
            # (2) P1 identity
            L = L_comb(x, xp, y, yp, u)
            B = B_boundary(x, xp, y, yp, u)
            if sp.simplify(L - B) != 0:
                ident_ok = False
            # (3) G | L
            smooth, divides = g_divides(L, G)
            if not (smooth and divides):
                gdiv_ok = False
                if n_inst < 5:
                    print(f"   GDIV FAIL u={u} R={R} j={j},{jp}: L={L} G={G}")
            n_inst += 1
            if L != 0 and G > 0:
                ratios.append((abs(sp.Rational(L).p), G, u, R, (j, jp)))
print(f"  instances: {n_inst}")
print(f"  (1) xuy,x'uy' are rotations of W : {rot_ok}")
print(f"  (2) L == B  (P1 identity)        : {ident_ok}")
print(f"  (3) G | L  in Z[1/6]             : {gdiv_ok}")
ALL_OK &= rot_ok and ident_ok and gdiv_ok

# exclusion gauge: how often is |numerator(L)| < G  (a non-vacuous ceiling)?
small = [(N, G, u, R, sp_) for (N, G, u, R, sp_) in ratios if 0 < N < G]
print(f"\n  exclusion gauge: instances with 0 < |num(L)| < G : {len(small)} / {len(ratios)}")
if small:
    for N, G, u, R, sp_ in small[:5]:
        print(f"    |num|={N} < G={G}   u={u} R={R} splits={sp_}")
else:
    print("    (none -- numerator never strictly below G in this range)")
print()

# --------------------------------------------------------------------------- #
# (4) u-invariance: fix (|u|,len u) and R-splits, vary the actual core u       #
# --------------------------------------------------------------------------- #
print("== (4) u-elimination: numerator depends on u only via chi(u) ==")
# Among cores of EQUAL (sum,len) the unit chi(u) is identical => B identical =>
# numerator of L identical (G differs because W differs, but L itself is fixed).
R = (1, 2, 3)
j, jp = 1, 2
x, y, xp, yp = R[j:], R[:j], R[jp:], R[:jp]
# all 2-letter cores with letter-sum 4 -> chi = 2^4/3^2, identical
group = [u for u in itertools.product(letters, repeat=2) if sum(u) == 4]
Ls = []
for u in group:
    Ls.append(sp.Rational(L_comb(x, xp, y, yp, u)))
inv_ok = all(v == Ls[0] for v in Ls)
print(f"  cores with (sum,len)=(4,2): {group}")
print(f"  L values: {[str(v) for v in Ls]}")
print(f"  all equal (core eliminated beyond chi-signature): {inv_ok}")
# and a DIFFERENT chi-signature gives a DIFFERENT L (chi(u) really is the only handle)
u2 = (1, 1)   # (sum,len)=(2,2) -> different chi
diff_sig = (sp.Rational(L_comb(x, xp, y, yp, u2)) != Ls[0])
print(f"  core (1,1) [different chi] gives different L: {diff_sig}\n")
ALL_OK &= inv_ok and diff_sig

# --------------------------------------------------------------------------- #
# (5) CONTROL: non-rotation pairs are NOT forced G-divisible                   #
# --------------------------------------------------------------------------- #
print("== (5) CONTROL: x'uy' NOT a rotation of xuy => G | L typically FAILS ==")
# Use G := gcd_rotations(xuy); it divides S(xuy) but need not divide S(x'uy').
ctrl_total = ctrl_div = 0
ctrl_examples = []
small_alpha = [(1,), (2,), (3,), (1, 1), (1, 2)]
for x, xp, y, yp, u in itertools.product(small_alpha, small_alpha, small_alpha,
                                         small_alpha, [(), (1,), (1, 2)]):
    xuy   = tuple(x)+tuple(u)+tuple(y)
    xpuyp = tuple(xp)+tuple(u)+tuple(yp)
    # only count genuine non-rotation pairs of equal length (so a shared cycle is conceivable)
    if len(xuy) != len(xpuyp):
        continue
    if xpuyp in set(rotate(xuy, k) for k in range(len(xuy))):
        continue
    G = gcd_rotations(xuy)
    if G <= 1:
        continue
    L = L_comb(x, xp, y, yp, u)
    if L == 0:
        continue
    ctrl_total += 1
    smooth, divides = g_divides(L, G)
    if smooth and divides:
        ctrl_div += 1
    elif len(ctrl_examples) < 4:
        ctrl_examples.append((x, xp, y, yp, u, sp.Rational(L), G))
print(f"  non-rotation pairs tested (G>1): {ctrl_total}")
print(f"  of those, G | L holds          : {ctrl_div}  (expected: a small minority/coincidence)")
print("  sample NON-divisible controls:")
for x, xp, y, yp, u, L, G in ctrl_examples:
    print(f"    x={x} x'={xp} y={y} y'={yp} u={u}: num(L)={L.p} not div by G={G}")
control_ok = (ctrl_div < ctrl_total)   # the rotation hypothesis is doing real work
print(f"  control shows rotation hypothesis is necessary: {control_ok}\n")
ALL_OK &= control_ok

print("=" * 60)
print(f"G-DIVISIBILITY BRIDGE: {'ALL CHECKS PASS' if ALL_OK else 'FAILED'}")
sys.exit(0 if ALL_OK else 1)
