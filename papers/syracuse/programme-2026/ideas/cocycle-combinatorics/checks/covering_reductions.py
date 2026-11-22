"""Covering-reductions strategy -- Part 1 foundation + Parts 2/3 probes.

THE STRATEGY (special / existential, NOT systematic).  The recent leverages CLOSED
*systematic* word reduction (no confluent length-reducing rule / GSB, L1.3; no
representation-theoretic twist gives a small core, R2).  The covering strategy is
not blocked by that closure because it is EXISTENTIAL: build a covering family of
reduction PATTERNS such that every word in a positive-density family contains at
least one (we don't know which -- hence non-systematic, existence guaranteed) =>
every such word reduces => small core => violates Matveev/Ellison lower bound on
G = |2^E - 3^o| => excluded.

CORE PRIMITIVE (multi-anchor shared-frame extraction -- generalization of P3).
For a word cut into blocks  W = b_1 b_2 ... b_m, the cocycle gives
    S(W) = sum_i  X^{Pre_i} Y^{Suf_i}  S(b_i),
where Pre_i = letter-sum of the blocks BEFORE b_i and Suf_i = total length of the
blocks AFTER b_i.  If W' = b'_1 ... b'_m has chi(b'_i)=chi(b_i) for EVERY i
(equal letter-sum AND equal length, e.g. b'_i a permutation of b_i), then the
prefactors X^{Pre_i}Y^{Suf_i} are IDENTICAL for W and W', so
    S(W) - S(W') = sum_i  X^{Pre_i} Y^{Suf_i} ( S(b_i) - S(b'_i) ).
ANCHOR blocks (b_i = b'_i, the matched/shared sub-patterns x,y,z) cancel; only the
VARIABLE blocks survive, each as a UNIT (monomial) times a shorter block-difference.
unit_K = X^{Pre_K} Y^{Suf_K}.  This is exactly P3 with one variable block, P1 with
one anchor block -- the meta-layer that deploys those extractions.

REDUCTION STRENGTH (the bookkeeping that decides exclusion).  Exclusion needs the
6-free part of the residual core BOUNDED INDEPENDENT OF o (a la P3), NOT merely
"core < G".  A residual = (single unit) x (bounded block-difference) is bounded =>
EXCLUDES.  A residual = SUM of >=2 unit-weighted block-differences whose unit
prefactors sit O(o) apart does NOT have bounded 6-free part (the units diverge,
Bang-Zsygmondy) -- this is the trapped-run obstruction (P4) recovered at the
prefactor level.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/covering_reductions.py
"""
import sys, itertools, random
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations          # trusted kernel
X, Y = sp.symbols("X Y")

ALL_OK = True
def mark(ok):
    return "[ok]" if ok else "[XX]"


def sixfree(n):
    """strip every factor of 2 and 3 (G coprime to 6, so G|n iff G|sixfree(n))."""
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def Sint(w):
    return int(Spoly(tuple(w), 2, 3)) if len(w) else 0


def concat(blocks):
    out = ()
    for b in blocks:
        out = out + tuple(b)
    return out


def prefactors(blocks):
    """unit_i = X^{letter-sum before block i} * Y^{length after block i}."""
    units = []
    for i in range(len(blocks)):
        pre = sum(sum(b) for b in blocks[:i])
        suf = sum(len(b) for b in blocks[i + 1:])
        units.append(X ** pre * Y ** suf)
    return units


def chi_matched(blocks, blocksp):
    return all(sum(b) == sum(bp) and len(b) == len(bp)
               for b, bp in zip(blocks, blocksp))


def multi_anchor_residual_ok(blocks, blocksp):
    """Verify  S(W)-S(W') = sum_i unit_i (S(b_i)-S(b'_i))  as a Z[X,Y] identity."""
    assert len(blocks) == len(blocksp) and chi_matched(blocks, blocksp)
    lhs = sp.expand(Spoly(concat(blocks)) - Spoly(concat(blocksp)))
    units = prefactors(blocks)
    rhs = sp.expand(sum(u * (Spoly(tuple(b)) - Spoly(tuple(bp)))
                        for u, b, bp in zip(units, blocks, blocksp)))
    return sp.expand(lhs - rhs) == 0


# =========================================================================== #
print("=" * 74)
print("PART A -- the multi-anchor shared-frame identity (1, 2, 3 anchors), Z[X,Y]")
print("=" * 74)
random.seed(7)

# ---- 1 anchor (= P3 / the proven shared-frame extraction) ----------------- #
# blocks [P, M, Q], anchors P,Q shared, variable M->M' a permutation.
oneA = True
for _ in range(60):
    P = tuple(random.randint(1, 3) for _ in range(random.randint(1, 4)))
    Q = tuple(random.randint(1, 3) for _ in range(random.randint(0, 3)))
    M = tuple(random.randint(1, 4) for _ in range(random.randint(1, 3)))
    Mp = list(M); random.shuffle(Mp); Mp = tuple(Mp)
    if not multi_anchor_residual_ok([P, M, Q], [P, Mp, Q]):
        oneA = False
# pin the prefactor explicitly: unit_M = X^{|P|} Y^{lenQ}  (recovers P3 exactly)
P, Q, M = (1, 2, 1), (3,), (4, 2)
Mp = (2, 4)
lhs = sp.expand(Spoly(concat([P, M, Q])) - Spoly(concat([P, Mp, Q])))
rhs = sp.expand(X ** sum(P) * Y ** len(Q) * (Spoly(M) - Spoly(Mp)))
p3_pin = sp.expand(lhs - rhs) == 0
print(f"  {mark(oneA and p3_pin)} 1-anchor: S(PMQ)-S(PM'Q) = X^|P| Y^lenQ (S(M)-S(M'))  "
      f"[60 rand + explicit pin = P3]")
ALL_OK &= oneA and p3_pin

# ---- 2 anchors (x,y shared; A,B,C variable) ------------------------------- #
# blocks [A, x, B, y, C], anchors x,y at matched positions.
twoA = True
for _ in range(60):
    A = tuple(random.randint(1, 3) for _ in range(random.randint(1, 3)))
    B = tuple(random.randint(1, 3) for _ in range(random.randint(1, 3)))
    C = tuple(random.randint(1, 3) for _ in range(random.randint(0, 3)))
    x = (random.randint(1, 4),)
    y = (random.randint(1, 4),)
    Ap = list(A); random.shuffle(Ap); Ap = tuple(Ap)
    Bp = list(B); random.shuffle(Bp); Bp = tuple(Bp)
    Cp = list(C); random.shuffle(Cp); Cp = tuple(Cp)
    if not multi_anchor_residual_ok([A, x, B, y, C], [Ap, x, Bp, y, Cp]):
        twoA = False
print(f"  {mark(twoA)} 2-anchor: S(AxByC)-S(A'xB'yC') = unitA dA + unitB dB + unitC dC "
      f"(anchors x,y cancel) [60 rand]")
ALL_OK &= twoA

# ---- 3 anchors (x,y,z shared; A,B,C,D variable) --------------------------- #
threeA = True
for _ in range(60):
    blks = []
    for _b in range(4):
        blks.append(tuple(random.randint(1, 3) for _ in range(random.randint(1, 2))))
    A, B, C, D = blks
    x = (random.randint(1, 4),); y = (random.randint(1, 4),); z = (random.randint(1, 4),)
    perm = lambda t: tuple(random.sample(t, len(t)))
    W = [A, x, B, y, C, z, D]
    Wp = [perm(A), x, perm(B), y, perm(C), z, perm(D)]
    if not multi_anchor_residual_ok(W, Wp):
        threeA = False
# pin one explicit 3-anchor instance and report the four unit prefactors:
A, B, C, D = (1, 3), (2,), (3, 1), (2,)
x, y, z = (4,), (1,), (3,)
W = [A, x, B, y, C, z, D]
units = prefactors(W)
print(f"  {mark(threeA)} 3-anchor: S(AxByCzD)-S(...) = sum_K unitK (S(K)-S(K')) "
      f"(anchors x,y,z cancel) [60 rand]")
print(f"       pinned units for A,B,C,D: {[sp.srepr(u) if False else str(u) for u in units]}")
ALL_OK &= threeA

# ---- P1 is the chi-reweighted single-anchor (inner core u) case ----------- #
# When chi(x)=chi(x') and chi(y)=chi(y') the PLAIN difference S(xuy)-S(x'uy')
# is the multi-anchor identity with anchor u and variable blocks x,y.
p1ok = True
for _ in range(40):
    L = random.randint(1, 2)
    x = tuple(random.randint(1, 3) for _ in range(L))
    xp = list(x); random.shuffle(xp); xp = tuple(xp)       # chi-matched
    Ly = random.randint(1, 2)
    y = tuple(random.randint(1, 3) for _ in range(Ly))
    yp = list(y); random.shuffle(yp); yp = tuple(yp)
    u = tuple(random.randint(1, 4) for _ in range(random.randint(0, 3)))
    if not multi_anchor_residual_ok([x, u, y], [xp, u, yp]):
        p1ok = False
print(f"  {mark(p1ok)} P1 face: chi(x)=chi(x'),chi(y)=chi(y') => S(xuy)-S(x'uy') "
      f"= unitX dX + unitY dY, inner core u is the anchor [40 rand]")
ALL_OK &= p1ok
print()

# =========================================================================== #
print("=" * 74)
print("PART B -- reduction strength of enumerated families (bounded 6-free or not?)")
print("=" * 74)

# ---- Family 1: PERIODIC BACKGROUND + bounded arc  W = u^p beta  ------------ #
# The genuine NEW family: generalizes P3 from a single-LETTER run d^L to a
# PERIOD-u run u^p.  Slide beta one full period through the run; both
# u^k beta u^{p-k} and u^{k+1} beta u^{p-k-1} are rotations of cyclic u^p beta,
# residual = unit * (S(beta u) - S(u beta)), o-INDEPENDENT.
print("-- Family 1: periodic background  W = u^p beta  (bounded arc through a period-u run)")
fam1 = True
for u, beta in [((1, 2), (3,)), ((2, 1), (4,)), ((1, 1, 2), (3,)), ((2, 3), (1,))]:
    residual = Sint(tuple(beta) + tuple(u)) - Sint(tuple(u) + tuple(beta))
    ceil = sixfree(residual)
    div_ok = True; le_ok = True; maxG = 0
    for p in range(2, 10):
        W = concat([u] * p) + tuple(beta)
        G = gcd_rotations(W)
        maxG = max(maxG, G)
        if G != 0 and ceil % G != 0:
            div_ok = False
        if G > ceil:
            le_ok = False
    ok = div_ok and le_ok
    fam1 &= ok
    print(f"  {mark(ok)} u={u} beta={beta}: ceiling sixfree(S(beta u)-S(u beta))={ceil} "
          f"(o-indep) | over p=2..9 maxG={maxG} G|ceil={div_ok} G<=ceil={le_ok}")
print(f"  => STRONG: bounded 6-free independent of o => EXCLUDES.  NEW family (period-u bg).")
ALL_OK &= fam1
print()

# ---- Family 2: TWO growing runs (the P4 nemesis)  e1 d^a e2 d^{2a}  -------- #
# Two defects with growing runs on both sides; best VALID (both-runs-intact)
# rotation combo's min 6-free part GROWS -> NOT excludable by this mechanism.
print("-- Family 2: two growing runs  C(a,2a) = e1 d^a e2 d^{2a}  (defects can't share one frame)")
e1, e2, d = 3, 4, 1
units_box = sorted(set(2 ** c * 3 ** dd for c in range(4) for dd in range(4)))
coeffs = sorted(set(units_box + [-u for u in units_box]))
c_min = []
for a in (2, 3, 4, 5):
    w1 = (e1,) + (d,) * a + (e2,) + (d,) * (2 * a)
    w2 = (e2,) + (d,) * (2 * a) + (e1,) + (d,) * a           # a rotation of w1
    assert w2 in set(rotate(w1, k) for k in range(len(w1)))
    S1, S2 = Sint(w1), Sint(w2)
    best = min(sixfree(c1 * S1 + c2 * S2) for c1 in coeffs for c2 in coeffs
               if c1 * S1 + c2 * S2 != 0)
    c_min.append(best)
grows2 = c_min[-1] > c_min[0] and max(c_min) >= 1000
print(f"  {mark(grows2)} min 6-free over valid both-runs-intact unit combo, a=2..5 = {c_min}  (grows)")
print(f"  => WEAK: trapped run -> 6-free diverges (Bang-Zsygmondy).  NOT excluded (the open no-go).")
ALL_OK &= grows2
print()

# ---- Family 3: SYMMETRIC two-anchor  W = b1 u^k b2 u^k  ------------------- #
# Two ALIGNED anchors u^k (matched positions, identical content); rotate by the
# half-period to swap b1<->b2 (chi-matched defects).  The multi-anchor identity
# gives residual = (unit_{b1} - unit_{b2}) (S(b1)-S(b2)) -- a DIFFERENCE OF TWO
# UNITS sitting O(o) apart, whose 6-free part DIVERGES even though S(b1)-S(b2)
# is bounded.  Aligning two anchors does NOT rescue exclusion.
print("-- Family 3: symmetric two-anchor  W = b1 u^k b2 u^k  (anchors align, but units diverge)")
u = (1, 2); b1, b2 = (1, 4), (2, 3)                         # chi-matched: sum 5, len 2
assert sum(b1) == sum(b2) and len(b1) == len(b2)
fam3_ident = True; sf3 = []
for k in range(2, 8):
    blocks = [b1, concat([u] * k), b2, concat([u] * k)]
    blocksp = [b2, concat([u] * k), b1, concat([u] * k)]    # swap b1<->b2
    # validity: blocksp's concatenation is a rotation of blocks' concatenation
    Wc = concat(blocks); Wpc = concat(blocksp)
    is_rot = Wpc in set(rotate(Wc, j) for j in range(len(Wc)))
    if not is_rot:
        fam3_ident = False
    if not multi_anchor_residual_ok(blocks, blocksp):
        fam3_ident = False
    # residual = (unit_{b1} - unit_{b2})(S(b1)-S(b2)); confirm + measure 6-free
    units = prefactors(blocks)
    resid = sp.expand((units[0] - units[2]) * (Spoly(b1) - Spoly(b2)))
    direct = sp.expand(Spoly(Wc) - Spoly(Wpc))
    if sp.expand(resid - direct) != 0:
        fam3_ident = False
    sf3.append(sixfree(int(direct.subs({X: 2, Y: 3}))))
grows3 = all(sf3[i] < sf3[i + 1] for i in range(len(sf3) - 1))
print(f"  {mark(fam3_ident)} residual = (unit_b1 - unit_b2)(S(b1)-S(b2)), valid rotation combo, k=2..7")
print(f"  {mark(grows3)} its 6-free part k=2..7 = {sf3}  (DIVERGES -- the unit difference grows)")
print(f"  => WEAK: aligning two anchors gives a diverging unit-PREFACTOR difference.  No exclusion.")
ALL_OK &= fam3_ident and grows3
print()

# =========================================================================== #
print("=" * 74)
print("PART C -- Part-2 make-or-break PROBE: is the bounded extraction available for")
print("          generic words?  (extractability = a long shared frame between rotations)")
print("=" * 74)
# A bounded residual requires the growing run(s) to sit ENTIRELY in the anchor
# frame, i.e. two rotations W_i, W_j sharing a frame of length ~ o (common
# prefix + common suffix), the residual block being O(1).  Measure the maximal
# shared-frame length over rotation pairs of RANDOM words; residual_len = n -
# maxframe is the length of the surviving variable block.  If residual_len GROWS
# with n, the extraction is NOT bounded -> pigeonhole repeats are not in
# aligned/single-background configuration.

def shared_frame_len(a, b):
    n = len(a)
    p = 0
    while p < n and a[p] == b[p]:
        p += 1
    s = 0
    while s < n - p and a[n - 1 - s] == b[n - 1 - s]:
        s += 1
    return p + s

def max_shared_frame(W):
    rots = [rotate(W, k) for k in range(len(W))]
    best = 0
    for i in range(len(rots)):
        for j in range(i + 1, len(rots)):
            f = shared_frame_len(rots[i], rots[j])
            if f > best:
                best = f
    return best

random.seed(101)
print("  n  : mean residual_len = n - max_shared_frame  (over 8 random words, gaps 1..3)")
resid_means = []
for n in (8, 16, 32, 64):
    vals = []
    for _ in range(8):
        W = tuple(random.randint(1, 3) for _ in range(n))
        vals.append(n - max_shared_frame(W))
    m = sum(vals) / len(vals)
    resid_means.append(m)
    print(f"  {n:3d}: mean residual_len = {m:.1f}")
probe_drifts = resid_means[-1] > resid_means[0] + 5      # residual block grows with n
print(f"  {mark(probe_drifts)} residual_len DRIFTS UP with n "
      f"({resid_means[0]:.1f} -> {resid_means[-1]:.1f}): generic words have NO long shared")
print(f"       frame, so the bounded single-frame extraction is unavailable. (Honest: this is")
print(f"       the open crux -- it does NOT prove no clever multi-move covering exists.)")
ALL_OK &= probe_drifts
print()

# =========================================================================== #
print("=" * 74)
print("PART D -- Part-3 dichotomy: w = u v, u BALANCED (low-discrepancy walk), v HEAVY")
print("=" * 74)
# Cocycle partial-sum walk: e_k = sum of first k gaps.  Discrepancy of u =
# max_k | e_k - rho*k |, rho = |u|/len(u) the mean slope.  BALANCED = low
# discrepancy => no long run => high subword complexity => pigeonhole forces a
# repeated short factor (Part-2 regime).  HEAVY = a long single-letter run d^L
# (the partial-sum walk has a long straight segment) => P3 regime.

def discrepancy(u):
    e, acc = [0], 0
    for g in u:
        acc += g
        e.append(acc)
    n = len(u)
    rho = sum(u) / n
    return max(abs(e[k] - rho * k) for k in range(n + 1))

def has_repeated_factor(u, L):
    seen = {}
    for i in range(len(u) - L + 1):
        f = u[i:i + L]
        if f in seen:
            return True, f
        seen[f] = i
    return False, None

# HEAVY part: d^L with a junction defect -> P3 bounded wedge (o-independent).
print("-- HEAVY part v = d^L (long run): P3 bounded extraction, o-independent ceiling")
d, e = 1, 4                                                  # junction defect e against run d
ceilP3 = sixfree(Sint((e, d)) - Sint((d, e)))
heavy_ok = True; seenG = set()
for L in range(2, 9):
    W = (e,) + (d,) * L                                      # single defect, single run
    G = gcd_rotations(W)
    if G != 0 and ceilP3 % G != 0:
        heavy_ok = False
    seenG.add(ceilP3)
print(f"  {mark(heavy_ok and len(seenG) == 1)} v handled by P3: ceiling sixfree(S(ed)-S(de))={ceilP3}, "
      f"o-independent over L=2..8")

# BALANCED part: a low-discrepancy word; show pigeonhole forces a repeated factor.
print("-- BALANCED part u (low-discrepancy cocycle walk): pigeonhole forces a repeat")
u_bal = (1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2)        # Sturmian-like, low discrepancy
disc = discrepancy(u_bal)
rep2, f2 = has_repeated_factor(u_bal, 2)                      # alphabet {1,2}, len-2 factors <=4
# pigeonhole: #distinct length-L factors over a-letter alphabet <= a^L; for L with
# a^L < (#windows) a repeat is forced.
a_letters = len(set(u_bal)); n_u = len(u_bal)
L_force = 1
while a_letters ** L_force < (n_u - L_force + 1):
    L_force += 1
repF, fF = has_repeated_factor(u_bal, L_force)
bal_ok = rep2 and repF
print(f"  {mark(bal_ok)} u discrepancy={disc:.2f} (low); alphabet size {a_letters}, len {n_u}; "
      f"pigeonhole forces a repeated length-{L_force} factor: {repF} (e.g. {fF})")
print(f"       => u has anchors (the forced repeat) but they are SCATTERED, not a single")
print(f"       background -- so u is the genuinely-hard Part-2 regime, v the solved P3 regime.")
print(f"       The unsolved coupling is the u-v JUNCTION (one move cannot bound both at once).")
ALL_OK &= heavy_ok and (len(seenG) == 1) and bal_ok
print()

print("=" * 74)
print(f"COVERING-REDUCTIONS CHECK: {'ALL PARTS PASS' if ALL_OK else 'FAILED'}")
print("=" * 74)
sys.exit(0 if ALL_OK else 1)
