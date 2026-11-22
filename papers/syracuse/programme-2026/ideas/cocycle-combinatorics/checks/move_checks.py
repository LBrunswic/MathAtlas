"""Verification for ideas/cocycle-combinatorics/drafts/seed.md.

Uses the trusted kernel S (homogenized: S(uv)=Y^{len v}S(u)+X^{|u|}S(v)) and the
chi-normalized functional Su(w) = S(w)|_{(2,3)} / 3^{len(w)-1}, chi(u)=2^|u|/3^{len u},
which satisfies Su(uv)=Su(u)+chi(u)Su(v)  (the convention in the draft).

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/move_checks.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, X, Y, gcd_rotations  # trusted kernel

def Sk(w):                       # kernel S at (2,3), integer
    return int(Spoly(tuple(w), 2, 3)) if len(w) else 0
def lenw(w): return len(w)
def sumw(w): return sum(w)
def chi(w):  return sp.Rational(2) ** sumw(w) / sp.Rational(3) ** lenw(w)
def Su(w):                       # chi-normalized functional, Su(single)=1
    n = len(w)
    return sp.Rational(Sk(w), 3 ** (n - 1)) if n >= 1 else sp.Integer(0)

def is_unit(r):                  # r is +-2^a 3^b ?
    if r == 0: return False
    r = abs(sp.Rational(r)); num, den = r.p, r.q
    for p in (2, 3):
        while num % p == 0: num //= p
        while den % p == 0: den //= p
    return num == 1 and den == 1

# fidelity: Su matches the chi-cocycle on a sample, and kernel self-test value
assert Su((1,)) == 1 and Su((3,)) == 1
assert sp.simplify(Su((1, 2, 3)) - (Su((1,)) + chi((1,)) * Su((2, 3)))) == 0
print("fidelity: Su is the chi-cocycle, Su(single)=1  [OK]\n")

# ---- G is coprime to 6 (so '~' absorbs every Z[1/6] unit: 2- AND 3-powers) ----
bad = [w for L in range(1, 6) for w in itertools.product(range(1, 5), repeat=L)
       if sp.gcd(gcd_rotations(w), 6) != 1]
print(f"G coprime to 6 over all words len<=5, letters 1..4: {'OK' if not bad else bad[:3]}\n")

# ---- Move 1: repeated-block reduction ----
print("== Move 1:  S(xyxz)-S(xzxy) ~ S(yxz)-S(zxy) ==")
m1_ok = True
for x, y, z in [((1,), (2,), (3,)), ((2,), (1, 1), (3,)), ((1, 2), (3,), (2, 1)),
                ((3,), (1,), (2, 2))]:
    lhs = Su(x + y + x + z) - Su(x + z + x + y)
    rhs = Su(y + x + z) - Su(z + x + y)
    ratio = sp.nsimplify(lhs / rhs) if rhs != 0 else None
    okk = (ratio == chi(x))                 # chi-convention prefactor
    # kernel convention: prefactor is the pure 2-power X^{|x|}
    kl = Sk(x + y + x + z) - Sk(x + z + x + y)
    kr = Sk(y + x + z) - Sk(z + x + y)
    okk2 = (kl == 2 ** sumw(x) * kr)
    m1_ok &= okk and okk2
    print(f"  x={x} y={y} z={z}: Su-ratio={ratio} == chi(x)={chi(x)}? {okk}; "
          f"kernel prefactor 2^|x|? {okk2}")
print(f"  Move 1 holds: {m1_ok}\n")

# ---- Move 2: proposed balanced swap ----
# chi(x')S(xuy) - chi(x)S(x'uy')  ~?  S(yx) - S(y'x')   when chi(xy)=chi(x'y')
print("== Move 2:  chi(x')S(xuy)-chi(x)S(x'uy') ~? S(yx)-S(y'x'),  chi(xy)=chi(x'y') ==")
alph = [(1,), (2,), (3,), (1, 1), (1, 2), (2, 1)]
us = [(), (1,), (2,), (1, 2)]
tested = unit_ratio = nonunit = 0
examples = []
for x, xp, y, yp in itertools.product(alph, repeat=4):
    if chi(x + y) != chi(xp + yp):        # balance condition
        continue
    for u in us:
        lhs = chi(xp) * Su(x + u + y) - chi(x) * Su(xp + u + yp)
        rhs = Su(y + x) - Su(yp + xp)
        if rhs == 0:
            continue
        tested += 1
        r = sp.nsimplify(lhs / rhs)
        if is_unit(r):
            unit_ratio += 1
        else:
            nonunit += 1
            if len(examples) < 4:
                examples.append((x, xp, y, yp, u, r))
print(f"  instances tested: {tested}")
print(f"  ratio is a unit (+-2^a 3^b)  : {unit_ratio}")
print(f"  ratio is NOT a unit          : {nonunit}")
print("  sample non-unit ratios (Move 2 fails as stated):")
for x, xp, y, yp, u, r in examples:
    print(f"    x={x} x'={xp} y={y} y'={yp} u={u}:  LHS/RHS = {r}")

# ---- Move 2, symbolic obstruction: coefficient form in free S-symbols ----
print("\n== Move 2 obstruction (symbolic, free S-symbols) ==")
Sx, Sxp, Sy, Syp, Su_, cx, cxp, cy, cyp, cu = sp.symbols(
    "Sx Sxp Sy Syp Su cx cxp cy cyp cu")
# Su(xuy)=Sx+cx Su+cx cu Sy ; chi-cocycle expansion
S_xuy = Sx + cx * Su_ + cx * cu * Sy
S_xpuyp = Sxp + cxp * Su_ + cxp * cu * Syp
LHS = sp.expand(cxp * S_xuy - cx * S_xpuyp)
RHS = sp.expand((Sy + cy * Sx) - (Syp + cyp * Sxp))   # S(yx)-S(y'x')
print("  LHS =", LHS)
print("  RHS =", RHS)
print("  LHS = lambda*RHS would need coeff(S(x)) match with lambda=cx*cxp*cu:")
print("    -> forces  chi(x)chi(u)chi(y)=1  (chi of a non-empty word), impossible.")
