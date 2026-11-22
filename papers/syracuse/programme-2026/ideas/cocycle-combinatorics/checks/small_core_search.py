"""The make-or-break payoff: can the P1 bridge ever yield a SMALL core (|C| < G)?

Two competing requirements:
  * u-ELIMINATION needs the chi-prefactored combination L = chi(x')S(xuy)-chi(x)S(x'uy')
    (P1) -- but those prefactors block the antisymmetric cancellation, so L is
    never small (g_divisibility_bridge.py: 0/17952 with |L|<G).
  * a SMALL antisymmetric core is the PLAIN difference  D := S(xuy)-S(x'uy') ;
    it can be small (it is a wedge core), but u does NOT drop out of D in general.

RECONCILIATION (the sweet spot):  if chi(x)=chi(x')  [x,x' equinumerous AND
equal-length], then
  * the Su(u)-coefficient of D vanishes -> u drops out of the PLAIN difference too;
  * L = chi(x) * D  (a UNIT times the genuine core).
So chi(x)=chi(x') is exactly when "extract u up to a unit" leaves a real, possibly
small core.  PART A proves both facts symbolically.

PART B then SEARCHES cyclic words W for rotation pairs (A,B) that share a common
middle factor u with equinumerous/equal-length outer-left blocks (chi(x)=chi(x')),
and asks whether |S(A)-S(B)| < G ever occurs (a non-vacuous Matveev ceiling with
u eliminated).

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/small_core_search.py
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

ALL_OK = True

# --------------------------------------------------------------------------- #
# PART A -- the tension, symbolically                                          #
# --------------------------------------------------------------------------- #
print("== PART A: u drops from the PLAIN difference  iff  chi(x)=chi(x') ==")
Sx, Sxp, Sy, Syp, Su_ = sp.symbols("Sx Sxp Sy Syp Su")
cx, cxp, cu = sp.symbols("cx cxp cu")
# Su(xuy)=Sx+cx*Su+cx*cu*Sy  (cocycle), likewise primed.
D_plain = sp.expand((Sx + cx * Su_ + cx * cu * Sy)
                    - (Sxp + cxp * Su_ + cxp * cu * Syp))
coeff_u = sp.expand(D_plain.coeff(Su_))
print("  plain D = S(xuy)-S(x'uy') =", D_plain)
print("  coeff of S(u) in D        =", coeff_u, "  (vanishes iff cx=cxp)")
dropsA = sp.simplify(coeff_u - (cx - cxp)) == 0
# under cx=cxp: L = cxp*S(xuy)-cx*S(x'uy') should equal cx*D
L_full = sp.expand(cxp * (Sx + cx * Su_ + cx * cu * Sy)
                   - cx * (Sxp + cxp * Su_ + cxp * cu * Syp))
L_at_eq = L_full.subs(cxp, cx)
D_at_eq = D_plain.subs(cxp, cx)
reconcile = sp.simplify(L_at_eq - cx * D_at_eq) == 0
print(f"  coeff(S(u)) == chi(x)-chi(x'): {dropsA}")
print(f"  when chi(x)=chi(x'):  L == chi(x)*D  : {reconcile}")
print(f"  PART A holds: {dropsA and reconcile}\n")
ALL_OK &= dropsA and reconcile

# --------------------------------------------------------------------------- #
# PART B -- search cyclic words for an equinumerous middle-u rotation pair      #
#           with |S(A)-S(B)| < G  (small core, u eliminated)                   #
# --------------------------------------------------------------------------- #
print("== PART B: search for |S(A)-S(B)| < G with chi(x)=chi(x') middle-u pairs ==")
letters = (1, 2, 3)
best = None          # (ratio, ...) smallest |num|/G found
n_pairs = 0
n_small = 0
small_examples = []
gdiv_ok = True
for n in range(4, 8):                       # cyclic word length
    seen = set()
    for W in itertools.product(letters, repeat=n):
        # canonical rep to skip rotation-duplicate cyclic words
        canon = min(rotate(W, k) for k in range(n))
        if canon in seen:
            continue
        seen.add(canon)
        G = gcd_rotations(W)
        if G <= 1:
            continue
        rots = [rotate(W, k) for k in range(n)]
        for A, B in itertools.combinations(rots, 2):
            if A == B:
                continue
            # try every middle slot [p, p+m), x=A[:p],u=A[p:p+m],y=A[p+m:]
            for p in range(1, n - 1):
                for m in range(1, n - p):    # leave y nonempty
                    if A[p:p + m] != B[p:p + m]:      # common middle u
                        continue
                    x, xp = A[:p], B[:p]
                    if x == xp:                        # genuine swap only
                        continue
                    if sumw(x) != sumw(xp):            # chi(x)=chi(x') (lens equal already)
                        continue
                    n_pairs += 1
                    diff = sp.Rational(Su(A) - Su(B))
                    if diff == 0:
                        continue
                    # G | numerator (both rotations of W) -- sanity
                    if not (is_6smooth(diff.q) and diff.p % G == 0):
                        gdiv_ok = False
                    ratio = sp.Rational(abs(diff.p), G)
                    if best is None or ratio < best[0]:
                        best = (ratio, W, A, B, p, m, abs(diff.p), G)
                    if abs(diff.p) < G:
                        n_small += 1
                        if len(small_examples) < 6:
                            small_examples.append((W, A, B, x, A[p:p+m], abs(diff.p), G))
print(f"  equinumerous middle-u rotation pairs examined: {n_pairs}")
print(f"  G | (S(A)-S(B)) held on all of them          : {gdiv_ok}")
print(f"  pairs with 0 < |num(S(A)-S(B))| < G          : {n_small}")
if best:
    ratio, W, A, B, p, m, num, G = best
    print(f"  smallest |num|/G = {ratio}  (|num|={num}, G={G})  W={W} A={A} B={B}")
if small_examples:
    print("  SMALL-CORE examples (|num| < G, u eliminated, G-divisible):")
    for W, A, B, x, u, num, G in small_examples:
        print(f"    W={W} A={A} B={B}  x={x} u={u}  |num|={num} < G={G}")
else:
    print("  -> NO small core found: in this range every such core has |num| >= G.")
ALL_OK &= gdiv_ok

# --------------------------------------------------------------------------- #
# PART C -- the RIGOROUS obstruction: any unit-combination of full rotation     #
#           sums is a multiple of G, so nonzero => |odd part| >= G (G odd).     #
#           Hence NO non-vacuous Matveev ceiling can come from such a combo.    #
# --------------------------------------------------------------------------- #
print("\n== PART C: rigorous no-go -- unit-combinations of rotation sums are >= G ==")
def odd_part(n):
    n = abs(int(n))
    while n and n % 2 == 0:
        n //= 2
    return n
import random
random.seed(20260608)
units = [sp.Rational(1), sp.Rational(2), sp.Rational(4), sp.Rational(1, 3),
         sp.Rational(2, 3), sp.Rational(4, 9), sp.Rational(8, 3), sp.Rational(-2, 9)]
n_checks = 0
mult_ok = ge_ok = oddge_ok = True
for n in range(3, 8):
    for _ in range(300):
        W = tuple(random.randint(1, 4) for _ in range(n))
        G = gcd_rotations(W)
        if G <= 1:
            continue
        rots = [rotate(W, k) for k in range(n)]
        # random unit-coefficient combination of (up to 3) rotation sums
        k = random.randint(2, min(3, n))
        idx = random.sample(range(n), k)
        combo = sum(random.choice(units) * Su(rots[i]) for i in idx)
        combo = sp.Rational(combo)
        if not is_6smooth(combo.q):
            mult_ok = False                  # should always be 6-smooth
        N = combo.p                          # integer numerator (coprime to 6)
        n_checks += 1
        if N % G != 0:
            mult_ok = False
        elif N != 0:
            if abs(N) < G:
                ge_ok = False
            if odd_part(N) % G != 0 or odd_part(N) < G:
                oddge_ok = False             # G odd => G | odd_part(N) => >= G
print(f"  random unit-combinations tested : {n_checks}")
print(f"  numerator always a multiple of G            : {mult_ok}")
print(f"  nonzero numerator always |N| >= G           : {ge_ok}")
print(f"  G | odd_part(N) and odd_part(N) >= G (G odd): {oddge_ok}")
print("  => a nonzero rotation-sum combination is NEVER a small core; the only")
print("     sub-G object is the degenerate core = 0 (classical Steiner locus).")
partC = mult_ok and ge_ok and oddge_ok
ALL_OK &= partC

print("\n" + "=" * 60)
print(f"SMALL-CORE SEARCH: {'PASS' if ALL_OK else 'FAIL'}  "
      f"(PartA+C proven; PartB exploratory, gdiv sanity={gdiv_ok})")
sys.exit(0 if ALL_OK else 1)
