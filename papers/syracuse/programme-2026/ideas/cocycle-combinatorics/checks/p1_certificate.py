"""Airtight certificate for principle [P1] inner-core extraction.

Claim (exact, for ALL blocks x,x',y,y' and inner core u):

  chi(x') S(xuy) - chi(x) S(x'uy')
      = [ chi(x') S(x) - chi(x) S(x') ]                       (outer boundary, u-free)
        + chi(x) chi(x') chi(u) [ S(y) - S(y') ]              (unit-scaled short diff)

S is the chi-normalized cocycle  Su(w) = S_homog(w) / Y^{len-1},
chi(w) = X^{|w|} / Y^{len w}, satisfying  Su(uv) = Su(u) + chi(u) Su(v)
and chi multiplicative: chi(uv) = chi(u) chi(v).

Two INDEPENDENT certificates, both must pass:
  PART A: free-symbol cocycle proof (the algebra, length-agnostic).
  PART B: real-kernel polynomial identity in Z[X,Y], over a grid of *actual*
          block lengths and letters, X,Y kept symbolic (so each pass certifies
          the identity for that block-length signature, not just at (2,3)).

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/p1_certificate.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, X, Y          # trusted kernel, homogenized

ALL_OK = True

# --------------------------------------------------------------------------- #
# PART A -- free-symbol cocycle proof (length-agnostic algebra)               #
# --------------------------------------------------------------------------- #
print("== PART A: free-symbol cocycle proof ==")
Sx, Sxp, Sy, Syp, Su = sp.symbols("Sx Sxp Sy Syp Su")
cx, cxp, cy, cyp, cu = sp.symbols("cx cxp cy cyp cu")

# Su(xuy): expand (x u) y with chi multiplicative chi(xu)=chi(x)chi(u).
#   Su(xu)  = Su(x) + chi(x) Su(u)
#   Su(xuy) = Su(xu) + chi(xu) Su(y) = Su(x)+cx*Su + cx*cu*Sy
S_xuy   = Sx  + cx  * Su + cx  * cu * Sy
S_xpuyp = Sxp + cxp * Su + cxp * cu * Syp

LHS = sp.expand(cxp * S_xuy - cx * S_xpuyp)
RHS = sp.expand((cxp * Sx - cx * Sxp) + cx * cxp * cu * (Sy - Syp))
diff = sp.expand(LHS - RHS)
print("  LHS =", LHS)
print("  RHS =", RHS)
print("  LHS - RHS =", diff)
partA = (diff == 0)
# also confirm the inner-core symbol Su drops out of the LHS entirely
su_free = (sp.expand(LHS).coeff(Su) == 0)
print(f"  inner-core S(u) cancels in LHS: {su_free}")
print(f"  PART A holds: {partA and su_free}\n")
ALL_OK &= partA and su_free

# --------------------------------------------------------------------------- #
# PART B -- real-kernel polynomial identity in Z[X,Y]                         #
# --------------------------------------------------------------------------- #
def lenw(w): return len(w)
def sumw(w): return sum(w)
def chi(w):  return X ** sumw(w) / Y ** lenw(w)              # symbolic unit
def Su_k(w):                                                 # chi-normalized S
    n = len(w)
    if n == 0:
        return sp.Integer(0)
    return sp.together(Spoly(tuple(w)) / Y ** (n - 1))       # poly in X,Y

def inner_core_lhs(x, xp, y, yp, u):
    return chi(xp) * Su_k(tuple(x) + tuple(u) + tuple(y)) \
         - chi(x)  * Su_k(tuple(xp) + tuple(u) + tuple(yp))

def inner_core_rhs(x, xp, y, yp, u):
    return (chi(xp) * Su_k(x) - chi(x) * Su_k(xp)) \
         + chi(x) * chi(xp) * chi(u) * (Su_k(y) - Su_k(yp))

print("== PART B: real-kernel Z[X,Y] identity over a grid of block lengths ==")
# vary the *lengths* of x,x',y,y',u over a grid; letters from 1..3.
# (lengths chosen to exercise asymmetric/empty cases too.)
letters = (1, 2, 3)
def words_of_len(L):
    return list(itertools.product(letters, repeat=L)) if L > 0 else [()]

length_signatures = [
    (1, 1, 1, 1, 0),   # empty core
    (1, 1, 1, 1, 1),
    (1, 2, 1, 2, 1),
    (2, 1, 2, 1, 2),
    (2, 2, 1, 1, 2),
    (1, 1, 2, 2, 3),   # core length 3
    (3, 1, 1, 2, 1),   # long x
    (1, 3, 2, 1, 0),   # long x', empty core
    (2, 2, 2, 2, 2),
]
total = 0
failures = []
for (lx, lxp, ly, lyp, lu) in length_signatures:
    # sample a few concrete words per length signature (cap the product)
    import random
    random.seed(lx * 1000 + lxp * 100 + ly * 10 + lyp + lu)
    Xs  = words_of_len(lx);  Xps = words_of_len(lxp)
    Ys  = words_of_len(ly);  Yps = words_of_len(lyp)
    Us  = words_of_len(lu)
    combos = list(itertools.product(Xs, Xps, Ys, Yps, Us))
    if len(combos) > 24:
        combos = random.sample(combos, 24)
    sig_ok = True
    for x, xp, y, yp, u in combos:
        d = sp.simplify(inner_core_lhs(x, xp, y, yp, u)
                        - inner_core_rhs(x, xp, y, yp, u))
        total += 1
        if d != 0:
            sig_ok = False
            failures.append((x, xp, y, yp, u, d))
    print(f"  lengths (x,x',y,y',u)={ (lx,lxp,ly,lyp,lu) }: "
          f"{len(combos)} instances  ->  {'OK' if sig_ok else 'FAIL'}")
print(f"  total instances certified == 0 in Z[X,Y]: {total}")
if failures:
    print("  FAILURES:", failures[:3])
partB = (len(failures) == 0)
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- fully symbolic letters (extra airtight): one signature with the   #
#           letters themselves left as free symbols, identity over Q(X,Y).    #
# --------------------------------------------------------------------------- #
print("== PART C: symbolic-letter identity (lengths fixed, letters free) ==")
# x=(a,), x'=(b,), y=(c,d), y'=(e,f), u=(g,h)  -- a 2-letter core, 2-letter y's
a, b, c, d, e, f, g, h = sp.symbols("a b c d e f g h", positive=True)
def Su_sym(w):
    n = len(w)
    if n == 0:
        return sp.Integer(0)
    return Spoly(tuple(w)) / Y ** (n - 1)
def chi_sym(w):
    return X ** sum(w) / Y ** len(w)
x_, xp_, y_, yp_, u_ = (a,), (b,), (c, d), (e, f), (g, h)
lhsC = chi_sym(xp_) * Su_sym(x_ + u_ + y_) - chi_sym(x_) * Su_sym(xp_ + u_ + yp_)
rhsC = (chi_sym(xp_) * Su_sym(x_) - chi_sym(x_) * Su_sym(xp_)) \
       + chi_sym(x_) * chi_sym(xp_) * chi_sym(u_) * (Su_sym(y_) - Su_sym(yp_))
diffC = sp.simplify(lhsC - rhsC)
print("  LHS - RHS (symbolic letters) =", diffC)
partC = (diffC == 0)
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

print("=" * 60)
print(f"P1 CERTIFICATE: {'ALL PARTS PASS' if ALL_OK else 'FAILED'}")
sys.exit(0 if ALL_OK else 1)
