"""Gen 6 (2026-06-08): GENERALIZE the Gen-5 two-ended extraction; make-or-break
test against the >=2-simultaneously-growing-gap NO-GO of the bounded-defect lever.

THE GEN-5 "LAST COMBINATION" (normalized P1, hatS = S/chi):
    [chi(x')S(xuy) - chi(x)S(x'uy')]/(chi(x)chi(x'))
        = [hatS(x)-hatS(x')]   (suffix / right extraction)
        + [S(uy)-S(uy')]       (prefix-shared core u, left extraction)
i.e. P1 = a prefix extraction PLUS a suffix extraction (the dual shared-frame lever
applied at BOTH ends), reversal-symmetric.

USER HEADLINE: try a chi-weighted combination sharing a prefix frame P AND a suffix
frame Q at once -- words P M Q with P,Q the long growing runs, M a bounded middle --
and ask whether (...)/(chi(P)chi(Q)) leaves a RUN-INDEPENDENT core, taming TWO
growing runs together.  Test on the symmetric family W_a = d^a e1 d^a e2 d^a
(cyclically C(a,2a)).

=========================  VERDICT (this script proves)  =======================
The two-ended extraction does NOT tame two growing runs.  It SHARPENS the no-go to
an EXACT, Zsygmondy-provable picture for this family, and pins the reason cleanly:

  PART A (PROVEN identity).  The literal headline shared-frame two-ended extraction
    of W_a = P M Q (P=Q=d^a, M=e1 d^a e2 -> M'=e2 d^a e1) reduces EXACTLY to
        S(M) - S(M')  =  (X^{e1} - X^{e2}) * S(d^{a+1}),
    a BOUNDED defect-factor (X^{e1}-X^{e2}) TIMES the TRAPPED middle run's sum
    S(d^{a+1}).  Its 6-free part = sixfree(3^{a+1}-2^{a+1}) -> GROWS (Zsygmondy: a
    primitive prime > a+1 divides it).  Note M<->M' is the REVERSAL of W_a, NOT a
    rotation (verified) -- so it is not even a valid G-ceiling; but it is the cleanest
    exhibit of the obstruction.  NO FREE LUNCH: extracting the two OUTER runs spends
    both defects on the bounded factor and exposes a LONE run's raw defect 2^L-3^L --
    the original transcendence barrier itself.

  PART B (verified).  Whichever run you slide the defect-arc through, the arc swallows
    the OTHER growing run -> the residual core's 6-free part grows (both choices).

  PART C (verified).  The VALID two-ended rotation combo (the two both-runs-intact
    rotations of C(a,2a), chi-weighted) has min 6-free part 23,23,1537,26857 -> grows.

  PART D (verified).  Iterated extraction maps C(a,2a) -> a wedge of the shorter word
    C(a,1), but a NON-special one (6-free part grows 305,691,1625,3979,10145).  The
    bounded arc-through-run wedge of C(a,1) IS a-indep (53) but has the wrong length,
    so it is unreachable as a rotation combo of C(a,2a): small G(C(a,1)) does NOT
    transfer to G(C(a,2a)).

  PART E (verified).  For the truly reversal-symmetric e1=e2, reversal == a rotation,
    and the two-ended core (X^{e1}-X^{e2})S(...) = 0 -- the reversal/transpose (hatS)
    direction (direction 4) adds nothing new.

  PART F (verified, consistent w/ Gen-4 multigap_nogo.py).  k=2 unit combos grow;
    k>=3 have NON-uniform low-a coincidences (no uniform bounded scheme).

So: the two-ended generalization is REAL and clarifying but does NOT crack the no-go.
It refines Gen-4's "non-cyclotomic Mahler>1 factor" reading: the cleanest two-ended
core here is CYCLOTOMIC (S(d^{a+1}) = prod_{k|a+1,k>1} Phi_k), yet still diverges
because its cyclotomic INDICES (divisors of a+1) do NOT collapse into {1,2,6}.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/two_ended_lever.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations          # trusted kernel
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


def Cword(p, q, e1=3, e2=4, d=1):
    """Cyclic 2-defect word e1 d^p e2 d^q (the C(p,q) family)."""
    return (e1,) + (d,) * p + (e2,) + (d,) * q


def sym(a, e1=3, e2=4, d=1):
    """The >=2-growing family W_a = d^a e1 d^a e2 d^a (cyclically C(a,2a))."""
    return (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a


ALL_OK = True
e1, e2, d = 3, 4, 1

# --------------------------------------------------------------------------- #
print("== PART A: headline two-ended core = (X^e1-X^e2) S(d^{a+1}); 6-free part GROWS ==")
# W_a = P M Q with P=Q=d^a, M=e1 d^a e2.  Shared-frame identity (the dual lever):
#   S(PMQ)-S(PM'Q) = X^{|P|} Y^{lenQ} (S(M)-S(M')),  M'=e2 d^a e1 (a permutation).
# And S(M)-S(M') = (X^e1-X^e2) S(d^{a+1})  EXACTLY (proven below over a=1..8).
ident_ok = True
sf = []
for a in range(1, 9):
    M = (e1,) + (d,) * a + (e2,)
    Mp = (e2,) + (d,) * a + (e1,)
    lhs = sp.expand(Spoly(M) - Spoly(Mp))
    rhs = sp.expand((X ** e1 - X ** e2) * Spoly((d,) * (a + 1)))
    if sp.expand(lhs - rhs) != 0:
        ident_ok = False
    # also confirm the full shared-frame identity on W_a itself:
    P = Q = (d,) * a
    full = sp.expand(Spoly(P + M + Q) - Spoly(P + Mp + Q))
    fpred = sp.expand(X ** sum(P) * Y ** len(Q) * (Spoly(M) - Spoly(Mp)))
    if sp.expand(full - fpred) != 0:
        ident_ok = False
    s = sixfree(int(lhs.subs({X: 2, Y: 3})))
    sf.append(s)
    if s != sixfree(3 ** (a + 1) - 2 ** (a + 1)):
        ident_ok = False
print(f"  S(e1 d^a e2)-S(e2 d^a e1) == (X^e1-X^e2)S(d^{{a+1}}) for a=1..8: {ident_ok}")
print(f"  6-free part of the core, a=1..8: {sf}  (== sixfree(3^{{a+1}}-2^{{a+1}}))")
sf_grows = all(sf[i] < sf[i + 1] for i in range(len(sf) - 1))
print(f"  strictly increasing (diverges; Zsygmondy primitive prime > a+1): {sf_grows}")

# M<->M' swap is the REVERSAL of W_a, NOT a rotation -> not a valid G-ceiling.
swap_not_rotation = True
for a in (2, 3, 4, 5):
    W = sym(a)
    Wr = (d,) * a + (e2,) + (d,) * a + (e1,) + (d,) * a   # = P M' Q (the reversal)
    if Wr in set(rotate(W, k) for k in range(len(W))):
        swap_not_rotation = False
print(f"  P M' Q (the M<->M' swap) is the reversal of W_a, NOT a rotation: {swap_not_rotation}")
partA = ident_ok and sf_grows and swap_not_rotation
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
print("== PART B: trapped run -- sliding EITHER run leaves the other; core grows ==")
# C(a,2a) cyclic = e1 d^a e2 d^{2a}.  Slide run-q (len 2a): arc beta_q = e1 d^a e2
# (contains run-a).  Slide run-p (len a): arc beta_p = e2 d^{2a} e1 (contains run-2a).
# Each residual core S(beta d)-S(d beta) keeps the swallowed run -> 6-free grows.
def arc_core(beta):
    return Sint(tuple(beta) + (d,)) - Sint((d,) + tuple(beta))
cq, cp = [], []
for a in (2, 3, 4, 5):
    beta_q = (e1,) + (d,) * a + (e2,)              # arc when sliding the q-run
    beta_p = (e2,) + (d,) * (2 * a) + (e1,)        # arc when sliding the p-run
    cq.append(sixfree(arc_core(beta_q)))
    cp.append(sixfree(arc_core(beta_p)))
print(f"  slide q-run (arc=e1 d^a e2): 6-free core a=2..5 = {cq}  (grows)")
print(f"  slide p-run (arc=e2 d^2a e1): 6-free core a=2..5 = {cp}  (grows)")
partB = all(cq[i] < cq[i + 1] for i in range(len(cq) - 1)) and \
        all(cp[i] < cp[i + 1] for i in range(len(cp) - 1))
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
print("== PART C: VALID two-ended rotation combo (both-runs-intact pair) GROWS ==")
# The only 2 rotations of C(a,2a) keeping both runs un-split:
#   w1 = e1 d^a e2 d^{2a}     w2 = e2 d^{2a} e1 d^a   (a rotation of w1)
# chi-weighted 2-term combos c1 S(w1)+c2 S(w2), unit coeffs +-2^c3^d (c,d<=3).
units = sorted(set(2 ** c * 3 ** dd for c in range(4) for dd in range(4)))
coeffs = sorted(set(units + [-u for u in units]))
c_min = []
both_rot = True
for a in (2, 3, 4, 5):
    w1 = Cword(a, 2 * a)
    w2 = Cword(2 * a, a, e1=e2, e2=e1)             # e2 d^{2a} e1 d^a
    if w2 not in set(rotate(w1, k) for k in range(len(w1))):
        both_rot = False
    S1, S2 = Sint(w1), Sint(w2)
    best = min(sixfree(c1 * S1 + c2 * S2) for c1 in coeffs for c2 in coeffs
               if c1 * S1 + c2 * S2 != 0)
    c_min.append(best)
print(f"  w2 is a rotation of w1 (so combo is a valid G-multiple): {both_rot}")
print(f"  min 6-free over unit-weighted both-runs-intact pair, a=2..5 = {c_min}  (grows large)")
# honest: low-a plateau (23,23) then growth -- not a fixed ceiling (cf Gen-4 caveat).
partC = both_rot and max(c_min) >= 1000 and c_min[-1] > c_min[0]
print(f"  -> not bounded by a fixed ceiling in range (max {max(c_min)}); low-a plateau noted")
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

# --------------------------------------------------------------------------- #
print("== PART D: iterated extraction lands on a NON-special wedge of C(a,1) ==")
# Extracting run-q from C(p,q) leaves unit*[S(e1 d^p e2 d)-S(d e1 d^p e2)], a wedge
# of the SHORTER word C(p,1)=e1 d^p e2 d.  But it is NOT the bounded arc-through-run
# wedge of C(p,1) -> its 6-free part grows.  The good wedge (a-indep) has length
# p+3 != p+2a+2, so it cannot be a rotation combo of C(p,2a).
res = []
for p in (2, 3, 4, 5, 6):
    r = Sint((e1,) + (d,) * p + (e2,) + (d,)) - Sint((d, e1) + (d,) * p + (e2,))
    res.append(sixfree(r))
good = sixfree(Sint((e2, d, e1, d)) - Sint((d, e2, d, e1)))   # good wedge of C(p,1), p-indep
print(f"  residual (wedge of C(p,1)) 6-free, p=2..6 = {res}  (grows)")
print(f"  bounded arc-through-run wedge of C(p,1) is p-indep = {good} (length-mismatched, unreachable)")
partD = all(res[i] < res[i + 1] for i in range(len(res) - 1))
print(f"  PART D holds: {partD}\n")
ALL_OK &= partD

# --------------------------------------------------------------------------- #
print("== PART E: e1=e2 -> reversal == rotation; two-ended core vanishes (direction 4 nil) ==")
rev_is_rot = True
for a in (2, 3, 4):
    W = sym(a, e1=3, e2=3)
    if tuple(reversed(W)) not in set(rotate(W, k) for k in range(len(W))):
        rev_is_rot = False
# the two-ended core (X^e1-X^e2)S(d^{a+1}) is identically 0 when e1=e2:
core_e1e2 = sp.expand((X ** 3 - X ** 3) * Spoly((d,) * 4))
print(f"  e1=e2: reversal of W_a IS a rotation (transpose/hatS adds nothing): {rev_is_rot}")
print(f"  two-ended core (X^e1-X^e2)S(d^{{a+1}}) at e1=e2 = {core_e1e2} (vanishes)")
partE = rev_is_rot and core_e1e2 == 0
print(f"  PART E holds: {partE}\n")
ALL_OK &= partE

# --------------------------------------------------------------------------- #
print("== PART F: k=2 grows; k>=3 low-a coincidences are non-uniform (cf Gen-4) ==")
box = [u for u in sorted(set(2 ** c * 3 ** dd for c in range(3) for dd in range(3)))]
box = box + [-u for u in box]
def min_sf(W, k):
    o = len(W)
    Sv = [Sint(rotate(W, j)) for j in range(o)]
    best = None
    for idx in itertools.combinations(range(o), k):
        for asn in itertools.product(box, repeat=k):
            v = sum(c * Sv[i] for c, i in zip(asn, idx))
            if v == 0:
                continue
            s = sixfree(v)
            if best is None or s < best:
                best = s
    return best
k2 = [min_sf(sym(a), 2) for a in (2, 3, 4, 5)]
k3 = [min_sf(sym(a), 3) for a in (2, 3, 4)]
print(f"  k=2 min 6-free a=2..5 = {k2}  (grows large; low-a plateau 23,23)")
print(f"  k=3 min 6-free a=2..4 = {k3}  (low-a dip a=2:1 -- non-uniform recipe; NOT a uniform scheme)")
# honest (Gen-4 lesson): a finite search CANNOT prove the no-go; it shows no uniform
# bounded scheme + the known low-a coincidences (min hits 1 at small a).
partF = (max(k2) >= 1000 and k2[-1] > k2[0]) and (min(k3) == 1)
print(f"  PART F holds: {partF}\n")
ALL_OK &= partF

print("=" * 72)
print(f"TWO-ENDED LEVER (Gen 6): {'ALL VERIFIED FACTS PASS' if ALL_OK else 'FAILED'}")
print("VERDICT: two-ended extraction does NOT tame >=2 growing runs.  It reduces W_a")
print("         (via the shared-frame swap) EXACTLY to (X^e1-X^e2)S(d^{a+1}) -- a")
print("         bounded defect TIMES one TRAPPED run's sum, 6-free = sixfree(3^{a+1}-")
print("         2^{a+1}), diverging by Zsygmondy.  No free lunch: the lone trapped run's")
print("         defect 2^L-3^L is the original barrier.  No-go SHARPENED, not cracked.")
sys.exit(0 if ALL_OK else 1)
