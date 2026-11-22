"""Characterize the 210 'unit' cases of the (false) literal Move 2.

In move_checks.py, over 392 chi-balanced instances (chi(xy)=chi(x'y')), the
literal-swap ratio  R := L / (S(yx)-S(y'x'))  is a unit (+-2^a 3^b) in exactly
210 cases and a non-unit in 182.

FINDINGS:
 (A) The previous draft CLAIMED the 210 are exactly {x=x'} u {y=y'}.  FALSE:
     that predicate covers only 96 of them.
 (B) PROVEN sufficient condition (0 false positives, 152 cases):
       Su(y) = Su(y')  ==>  R is a unit, and in fact  R = chi(x)/chi(y').
     Proof: with balance chi(x)chi(y)=chi(x')chi(y'), put lam=chi(x')/chi(x)
     (=chi(y)/chi(y')).  By P1, when Su(y)=Su(y') the core u drops and
       L   = chi(x')Su(x) - chi(x)Su(x')   = chi(x) [ lam Su(x) - Su(x') ],
       RHS = Su(yx)-Su(y'x') = chi(y)Su(x) - chi(y')Su(x')
                              = chi(y')[ lam Su(x) - Su(x') ],
     so R = chi(x)/chi(y') whenever the common factor is nonzero (RHS != 0).
 (C) The remaining 58 unit cases have Su(y) != Su(y'); there R depends on u and
     is a unit only sporadically (numerical coincidence) -- NO clean closed form.

So the honest statement: Su(y)=Su(y') is the *structural* unit family (and it is
exactly the case where P1's core-term vanishes); {x=x'}u{y=y'} is a strict subset.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/unit_cases.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly

def Sk(w):  return int(Spoly(tuple(w), 2, 3)) if len(w) else 0
def lenw(w): return len(w)
def sumw(w): return sum(w)
def chi(w):  return sp.Rational(2) ** sumw(w) / sp.Rational(3) ** lenw(w)
def Su(w):
    n = len(w)
    return sp.Rational(Sk(w), 3 ** (n - 1)) if n >= 1 else sp.Integer(0)
def is_unit(r):
    if r == 0: return False
    r = abs(sp.Rational(r)); num, den = r.p, r.q
    for p in (2, 3):
        while num % p == 0: num //= p
        while den % p == 0: den //= p
    return num == 1 and den == 1

alph = [(1,), (2,), (3,), (1, 1), (1, 2), (2, 1)]
us = [(), (1,), (2,), (1, 2)]

records = []
for x, xp, y, yp in itertools.product(alph, repeat=4):
    if chi(x + y) != chi(xp + yp):
        continue
    for u in us:
        lhs = chi(xp) * Su(x + u + y) - chi(x) * Su(xp + u + yp)
        rhs = Su(y + x) - Su(yp + xp)
        if rhs == 0:
            continue
        r = sp.nsimplify(lhs / rhs)
        records.append((x, xp, y, yp, u, r, is_unit(r)))

tested = len(records)
unit = sum(1 for *_, f in records if f)
print(f"instances tested : {tested}   unit : {unit}   non-unit : {tested-unit}")
assert (tested, unit) == (392, 210), "battery counts drifted"

# (A) old predicate is a strict subset, NOT a characterization
old_tp = sum(1 for x, xp, y, yp, u, r, f in records if f and ((x == xp) or (y == yp)))
old_fp = sum(1 for x, xp, y, yp, u, r, f in records if (not f) and ((x == xp) or (y == yp)))
print(f"\n(A) OLD predicate {{x=x'}}u{{y=y'}}: covers {old_tp}/210 unit cases, "
      f"{old_fp} false positives -> exact? {old_tp == 210 and old_fp == 0}")
assert old_fp == 0 and old_tp == 96, "old-predicate accounting changed"

# (B) Su(y)=Su(y') is a SUFFICIENT unit condition with R = chi(x)/chi(y') exactly
suff_n = 0
suff_all_unit = True
formula_ok = True
for x, xp, y, yp, u, r, f in records:
    if Su(y) == Su(yp):
        suff_n += 1
        if not f:
            suff_all_unit = False
        if r != chi(x) / chi(yp):           # the proven closed form
            formula_ok = False
print(f"(B) Su(y)=Su(y') cases: {suff_n}; all unit? {suff_all_unit}; "
      f"R == chi(x)/chi(y') in every one? {formula_ok}")
assert suff_n == 152 and suff_all_unit and formula_ok

# (C) the leftover unit cases all have Su(y) != Su(y')  (sporadic, u-dependent)
leftover = [(x, xp, y, yp, u, r) for x, xp, y, yp, u, r, f in records
            if f and Su(y) != Su(yp)]
print(f"(C) unit cases with Su(y)!=Su(y') (sporadic): {len(leftover)}")
# show that within such a sporadic (x,x',y,y') the ratio genuinely varies with u
from collections import defaultdict
blk = defaultdict(set)
for x, xp, y, yp, u, r, f in records:
    if Su(y) != Su(yp):
        blk[(x, xp, y, yp)].add(r)
u_varies = sum(1 for v in blk.values() if len(v) > 1)
print(f"    (x,x',y,y') blocks with Su(y)!=Su(y') where R varies with u: "
      f"{u_varies}/{len(blk)} -> the 58 are u-dependent coincidences")
assert len(leftover) == 58

print("\nSUMMARY: structural unit family = {Su(y)=Su(y')} (152, R=chi(x)/chi(y'), proven).")
print("Old {x=x'}u{y=y'} is a strict subset (96). 58 further units are sporadic.")
print("ALL ASSERTIONS PASS")
sys.exit(0)
