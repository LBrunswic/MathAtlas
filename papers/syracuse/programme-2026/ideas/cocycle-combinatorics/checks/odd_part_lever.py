"""The odd-part / 6-free lever, made explicit (structure.md P2/C9 reconstructed).

How do P2/C9 actually beat the size barrier?  NOT by a core < G (the [P2]
rotation-combination floor forbids that).  They win by a DIFFERENT mechanism:

  * the relevant core is a WEDGE of two rotation sums of the cyclic word W,
    so by the floor it is a multiple of G and |core| >= G;  BUT
  * its 6-FREE PART (strip every factor of 2 and 3 -- legitimate since G is
    coprime to 6) is BOUNDED INDEPENDENT of the cycle length o.

Then on a genuine cycle  G = |2^E - 3^o|  divides the core, so
      G  <=  sixfree(core)  =  a constant depending only on the DEFECT,
and Ellison's lower bound |2^E-3^o| >~ 2.56^o forces o bounded -> finitely many.

ENGINE (the "shared-frame extraction", DUAL of P1).  When M' is a permutation of
M (so chi(M)=chi(M'), i.e. equal letter-sum AND length -- the rationale's balance
condition), the cocycle gives the EXACT identity
      S(P M Q) - S(P M' Q) = X^{|P|} Y^{len Q} ( S(M) - S(M') ).            (*)
The shared outer frame P,Q (the long uniform RUNS) factors out as the UNIT
X^{|P|}Y^{len Q}, leaving the run-INDEPENDENT local core S(M)-S(M').  This is why
the ceiling is o-independent.

PART A  : prove (*) symbolically (and exhibit the correction term when chi(M)!=chi(M')).
PART B  : the single-defect AND defect-BLOCK lever; ceiling = sixfree(S(beta d)-S(d beta)),
          verified o-independent and tight over a grid of run lengths.
PART C  : reconcile with the [P2] floor: the wedge IS a rotation combo (>= G), yet its
          6-free part is the bounded ceiling -> exclusion is bounded-sixfree, NOT sub-G.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/odd_part_lever.py
"""
import sys, itertools, random
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations   # trusted kernel
X, Y = sp.symbols("X Y")

def sixfree(n):
    """strip every factor of 2 and 3 (G is coprime to 6, so G | n  iff  G | sixfree(n))."""
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
# PART A -- the shared-frame extraction identity (*)                          #
# --------------------------------------------------------------------------- #
print("== PART A: shared-frame extraction  S(PMQ)-S(PM'Q)=X^|P|Y^|Q|(S(M)-S(M'))  [chi(M)=chi(M')] ==")
random.seed(11)
perm_ok = True
n_perm = 0
for _ in range(80):
    P = tuple(random.randint(1, 3) for _ in range(random.randint(0, 3)))
    Q = tuple(random.randint(1, 3) for _ in range(random.randint(0, 3)))
    M = tuple(random.randint(1, 4) for _ in range(random.randint(1, 3)))
    Mp = list(M); random.shuffle(Mp); Mp = tuple(Mp)         # permutation => chi(M)=chi(M')
    lhs = sp.expand(Spoly(P + M + Q) - Spoly(P + Mp + Q))
    rhs = sp.expand(X ** sum(P) * Y ** len(Q) * (Spoly(M) - Spoly(Mp)))
    n_perm += 1
    if sp.expand(lhs - rhs) != 0:
        perm_ok = False
print(f"  identity (*) holds on {n_perm} permutation (chi-balanced) instances: {perm_ok}")

# the general correction term when |M| != |M'| (length equal, letter-sum not):
P, Q, M, Mp = (1, 2), (3,), (2, 1, 4), (1, 2, 3)             # same length, diff letter-sum
extra = sp.expand(X ** sum(P) * (X ** sum(M) - X ** sum(Mp)) * Spoly(Q))
lhs = sp.expand(Spoly(P + M + Q) - Spoly(P + Mp + Q))
rhs = sp.expand(X ** sum(P) * Y ** len(Q) * (Spoly(M) - Spoly(Mp)) + extra)
gen_ok = (sp.expand(lhs - rhs) == 0)
print(f"  general case carries extra term X^|P|(X^|M|-X^|M'|)S(Q) (vanishes iff |M|=|M'|): {gen_ok}")
partA = perm_ok and gen_ok
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
# PART B -- the lever: single-defect and defect-BLOCK ceilings, o-independent   #
# --------------------------------------------------------------------------- #
print("== PART B: lever ceiling = sixfree(S(beta d) - S(d beta)), o-independent & tight ==")
# The winning wedge is two ADJACENT rotations that move the contiguous defect
# block beta by one step through the uniform d-run; by (*) with M=beta·d, M'=d·beta,
#   wedge = X^{kd} Y^{m-1} (S(beta d) - S(d beta)),  6-free part = sixfree(S(beta d)-S(d beta)).
cases = [
    ((5,), 1),      # single-letter defect (structure.md P2): e=5,d=1, defect 4
    ((4,), 1),      # defect 3
    ((6,), 2),      # defect 4
    ((3, 4), 1),    # 2-letter contiguous block
    ((2, 5), 3),    # 2-letter contiguous block, background d=3
]
partB = True
for beta, d in cases:
    M, Mp = tuple(beta) + (d,), (d,) + tuple(beta)
    local_core = Sint(M) - Sint(Mp)
    ceil = sixfree(local_core)
    rows = []
    for k in range(1, 7):          # left run length
        for m in range(1, 6):      # right run length
            W = (d,) * k + tuple(beta) + (d,) * m
            G = gcd_rotations(W)
            rows.append((len(W), G))
    div_ok = all(ceil % G == 0 for _, G in rows)         # G | ceiling for all run lengths
    le_ok = all(G <= ceil for _, G in rows)              # ceiling is a true upper bound
    maxG = max(G for _, G in rows)
    tight = (maxG == ceil)                               # ceiling is attained somewhere
    o_indep = len(set([ceil])) == 1                      # ceil computed once, run-free by construction
    print(f"  beta={beta} d={d}: local core(2,3)={local_core} -> ceiling sixfree={ceil}"
          f" | over runs 1..6 x 1..5: maxG={maxG} G|ceil={div_ok} G<=ceil={le_ok} tight={tight}")
    partB &= div_ok and le_ok
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- reconcile with the [P2] floor: wedge >= G, yet sixfree(wedge) bounded #
# --------------------------------------------------------------------------- #
print("== PART C: the wedge IS a rotation combo (>= G), but its 6-free part is the bounded ceiling ==")
# single-defect W = d^a e d^b; wedge of two ADJACENT rotations (genuine rotations of W).
d, e = 1, 5                      # defect e-d = 4; ceiling sixfree(2^5-2^1)=sixfree(30)=5
ceil = sixfree(Sint((e, d)) - Sint((d, e)))
floor_ge = sixfree_bounded = True
maxsix = 0
for a in range(2, 8):
    for b in range(2, 6):
        W = (d,) * a + (e,) + (d,) * b
        o = len(W)
        G = gcd_rotations(W)
        rots = [rotate(W, k) for k in range(o)]
        Sv = [Sint(r) for r in rots]
        # adjacent-rotation wedge moving e by one through the run (genuine rotations):
        # find the two rotations d^k e d^{o-1-k} and d^{k+1} e d^{o-2-k}
        wedge = Sv[1] - Sv[2]            # any adjacent pair works; both are rotations of W
        if wedge == 0:
            continue
        # floor: |wedge| >= G  (it is a difference of two rotation sums, divisible by G)
        if wedge % G != 0 or abs(wedge) < G:
            floor_ge = False
        sf = sixfree(wedge)
        maxsix = max(maxsix, sf)
        if sf > ceil:                    # 6-free part must stay <= the o-independent ceiling
            sixfree_bounded = False
print(f"  ceiling sixfree(local core) = {ceil}")
print(f"  every adjacent wedge is divisible by G with |wedge| >= G (the floor): {floor_ge}")
print(f"  yet sixfree(wedge) <= ceiling for all run lengths (max seen {maxsix}): {sixfree_bounded}")
print("  => exclusion comes from a BOUNDED 6-free part (o-independent), NOT from a sub-G core.")
partC = floor_ge and sixfree_bounded
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

print("=" * 64)
print(f"ODD-PART / 6-FREE LEVER: {'ALL PARTS PASS' if ALL_OK else 'FAILED'}")
sys.exit(0 if ALL_OK else 1)
