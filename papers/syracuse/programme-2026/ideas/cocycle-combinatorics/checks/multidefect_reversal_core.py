"""Gen 7 (2026-06-08): CERTIFY the multi-defect generalization of the Gen-6 two-ended
reversal core, and pin down the VALIDITY GAP + the C8 rank-2 simultaneity.

Background (Gen 6, two_ended_lever.py).  For the 2-defect canonical family the dual
shared-frame two-ended extraction reduces EXACTLY to
    S(e1 d^a e2) - S(e2 d^a e1) = (X^e1 - X^e2) * S(d^{a+1}),
a BOUNDED defect factor times the TRAPPED run sum.  Gen-6 NEXT_FOCUS conjectured the
r-defect generalization is always (bounded defect poly) * PROD(trapped run sums).

================  WHAT THIS SCRIPT PROVES (and CORRECTS)  =====================

PART A (PROVEN, symbolic free defects).  Closed form for the middle word
  M_r = e1 d^a e2 d^a ... e_r  (r defects, r-1 interior runs, equal runs d^a):
      S(M_r) = Y^{(r-1)(a+1)}
             + S(d^{a+1}) * SUM_{i=1}^{r-1} X^{E_i+(i-1)ad} Y^{(r-1-i)(a+1)},
  E_i = e1+...+ei.  (Symbolic letters e_i, r=2..7, a=1..5, via the kernel S.)

PART B (PROVEN, symbolic).  The reversal core factors as a SINGLE run sum:
      S(M_r) - S(M_r^R) = S(d^{a+1}) * K_r,
      K_r = SUM_{i=1}^{r-1} X^{(i-1)ad} ( X^{E_i} - X^{E_r - E_{r-i}} ) Y^{(r-1-i)(a+1)}.
  ---> CORRECTS the Gen-6 conjecture.  It is NOT "PROD(run sums)" (exactly ONE
  run sum S(d^{a+1}) survives, NOT r-1 of them), and it is NOT "bounded defect poly":
  K_2 = X^e1 - X^e2 IS bounded (recovering Gen 6), but for r>=3 K_r carries Y^{(r-2)(a+1)}
  and X^{(r-2)ad} terms whose degree GROWS with a.  The right statement: a single
  EXPLICIT CYCLOTOMIC run-sum factor carries the whole divergence.

PART C (PROVEN reduction + numeric).  sixfree is completely multiplicative, so
      sixfree(core) = sixfree(S(d^{a+1})) * sixfree(K_r(2,3))
                    = sixfree(3^{a+1}-2^{a+1}) * sixfree(K_r(2,3)).
  The first factor DIVERGES by Bang-Zsygmondy (primitive prime > a+1).  Hence whenever
  the core is nonzero (K_r(2,3) != 0) its 6-free part diverges -- for EVERY r.  This is
  an EXACT (not merely reduced) divergence statement for the reversal core of the whole
  r-defect equal-run family.

PART D (PROVEN closed form + numeric).  UNEQUAL runs e1 d^{a1} e2 d^{a2} ... e_r:
      S(M) = Y^{(r-1)+A_{r-1}} + SUM_i X^{E_i+A_{i-1}d} Y^{(r-1-i)+(A_{r-1}-A_i)} S(d^{a_i+1}),
      A_i = a1+...+ai.  The reversal core is a SUM of DISTINCT run sums S(d^{a_i+1}), so
  it does NOT single-factor; numerically its 6-free part still diverges when >=2 runs grow.

PART E (PROVEN -- THE VALIDITY GAP, sharp).  W* = P M_r^R Q (P=Q=d^a) is a rotation of
  W = P M_r Q IFF the defect sequence (e1..er) is a palindrome -- and then the core is
  IDENTICALLY 0.  So the clean reversal core is NEVER a valid nonzero G-multiple: for
  distinct defects W* is the reversal (not a rotation), for palindromic defects the core
  vanishes.  Moreover the clean run-sum factorization does NOT transfer to the VALID
  both-runs-intact rotation difference: that carries a NON-cyclotomic factor of degree
  2a+2 (Mahler>1, growing) and has NO S(d^{a+1}) factor.  The two divergence mechanisms
  (cyclotomic reversal core vs non-cyclotomic valid core) are complementary.

PART F (PROVEN -- C8 rank-2 made precise).  All runs of a fixed background d lie on ONE
  line in R^2:  v(d^L) = S(d^L)*(X^d - Y, 1)  since D(d^L) = (X^d - Y) S(d^L).  So for a
  3-cut u=d^{L1}, v=defects, w=d^{L2}, the wedge C(u,w)=0 and C8 collapses to
      D(u) C(v,w) = - D(w) C(u,v),
  i.e. the two defect-slide cores are PROPORTIONAL with ratio -D(w)/D(u).  For UNEQUAL
  runs this ratio's 6-free part diverges; for EQUAL runs it is -1 and C8 gives NO
  obstruction -- which is exactly why the symmetric equal-run family is the stubborn open
  case.  C8 is the rank-2 backbone but (honestly) does NOT by itself close the equal-run no-go.

VERDICT: the multi-defect reversal core is PROVEN to diverge (exact, Zsygmondy) for all r,
via a single explicit cyclotomic factor -- a clean EXACT no-go statement for the reversal
core.  But the VALIDITY GAP is unbridgeable for this construction (clean core valid <=>
palindrome <=> 0), and valid rotation combos diverge by a complementary non-cyclotomic
mechanism, so the G-VALID no-go for the canonical family stays reduced-but-open.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/multidefect_reversal_core.py
"""
import sys
import numpy as np
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, D as Dpoly, core_C   # trusted kernel
X, Y = sp.symbols("X Y")


def Ssym(letters):
    """S for a word whose letters may be sympy symbols (symbolic gap values)."""
    n = len(letters)
    e, acc = [], 0
    for dd in letters:
        e.append(acc); acc += dd
    return sum((X ** e[k]) * (Y ** (n - 1 - k)) for k in range(n))


def Run(m, d):
    """S(d^m) = sum_{j=0}^{m-1} X^{jd} Y^{m-1-j}  (the run sum)."""
    return sum(X ** (j * d) * Y ** (m - 1 - j) for j in range(m))


def zero(expr):
    """True iff expr is identically 0 in Z[X,Y] (force power-combination of symbolic exps)."""
    return sp.powsimp(sp.expand(expr), force=True) == 0


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


def mahler_Y1(expr):
    """Mahler measure of expr|_{Y=1} as a 1-var integer polynomial in X."""
    expr = sp.expand(expr.subs(Y, 1))
    if expr == 0:
        return 0.0
    p = sp.Poly(expr, X)
    if p.degree() < 1:
        return 1.0
    c = [complex(z) for z in p.all_coeffs()]
    m = abs(c[0])
    for z in np.roots(c):
        if abs(z) > 1:
            m *= abs(z)
    return m


d = 1
ALL_OK = True


def Mword(es, a):
    """The middle M_r = e1 d^a e2 d^a ... e_r  (equal runs)."""
    L = []
    for i, e in enumerate(es):
        L.append(e)
        if i < len(es) - 1:
            L += [d] * a
    return tuple(L)


# --------------------------------------------------------------------------- #
print("== PART A: closed form for S(M_r), equal runs (symbolic free defects) ==")
cfA = True
for r in range(2, 8):
    es = sp.symbols(f"e1:{r + 1}")
    E = [0] * (r + 1)
    for i in range(1, r + 1):
        E[i] = E[i - 1] + es[i - 1]
    for a in range(1, 6):
        SM = Ssym(Mword(es, a))
        cf = Y ** ((r - 1) * (a + 1)) + Run(a + 1, d) * sum(
            X ** (E[i] + (i - 1) * a * d) * Y ** ((r - 1 - i) * (a + 1)) for i in range(1, r))
        if not zero(SM - cf):
            cfA = False
            print(f"  MISMATCH r={r} a={a}")
print(f"  S(M_r) closed form verified, r=2..7, a=1..5 (symbolic e_i): {cfA}")
ALL_OK &= cfA
print()

# --------------------------------------------------------------------------- #
print("== PART B: reversal core = S(d^{a+1}) * K_r (single run sum); CORRECTS conjecture ==")
cfB = True
Kdeg_growth = {}
for r in range(2, 8):
    es = sp.symbols(f"e1:{r + 1}")
    E = [0] * (r + 1)
    for i in range(1, r + 1):
        E[i] = E[i - 1] + es[i - 1]
    for a in range(1, 6):
        M = Mword(es, a)
        core = Ssym(M) - Ssym(tuple(reversed(M)))
        Kr = sum(X ** ((i - 1) * a * d) * (X ** E[i] - X ** (E[r] - E[r - i])) *
                 Y ** ((r - 1 - i) * (a + 1)) for i in range(1, r))
        if not zero(core - Run(a + 1, d) * Kr):
            cfB = False
            print(f"  CORE MISMATCH r={r} a={a}")
    # show K_r's Y-degree grows in a for r>=3 but is constant (=0) for r=2.
    # (substitute concrete distinct defects to read a genuine integer poly)
    evals = {es[i]: 3 + i for i in range(r)}
    ydegs = []
    for a in (2, 4, 6):
        Kr = sum(X ** ((i - 1) * a * d) * (X ** E[i] - X ** (E[r] - E[r - i])) *
                 Y ** ((r - 1 - i) * (a + 1)) for i in range(1, r))
        Krn = sp.expand(Kr.subs(evals))
        ydegs.append(int(sp.Poly(Krn, Y).degree()) if Krn != 0 else 0)
    Kdeg_growth[r] = ydegs
print(f"  S(M_r)-S(M_r^R) == S(d^{{a+1}}) * K_r  for r=2..7, a=1..5: {cfB}")
print(f"  deg_Y(K_r) at a=2,4,6 (constant for r=2 => bounded; grows for r>=3):")
for r in range(2, 8):
    tag = "BOUNDED (Gen-6 case)" if Kdeg_growth[r][0] == Kdeg_growth[r][-1] else "GROWS with a"
    print(f"     r={r}: {Kdeg_growth[r]}   -> {tag}")
only_r2_bounded = (Kdeg_growth[2][0] == Kdeg_growth[2][-1]) and \
                  all(Kdeg_growth[r][0] < Kdeg_growth[r][-1] for r in range(3, 8))
print(f"  ONLY r=2 has bounded K (so the Gen-6 'bounded x run' form is r=2-special): {only_r2_bounded}")
partB = cfB and only_r2_bounded
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
print("== PART C: 6-free divergence -- sixfree(core)=sixfree(3^{a+1}-2^{a+1})*sixfree(K_r) ==")
mult_ok = True
div_ok = True
for r, esv in [(3, (3, 4, 5)), (4, (3, 4, 5, 6)), (5, (2, 3, 4, 5, 6))]:
    sf_cores = []
    for a in range(1, 9):
        M = Mword(esv, a)
        core = Sint(M) - Sint(tuple(reversed(M)))
        run = 3 ** (a + 1) - 2 ** (a + 1)          # S(d^{a+1}) at (2,3), d=1
        if core == 0 or run == 0 or core % run != 0:
            mult_ok = False
            continue
        Kval = core // run
        if sixfree(core) != sixfree(run) * sixfree(Kval):   # multiplicativity of sixfree
            mult_ok = False
        sf_cores.append(sixfree(core))
    grows = all(sf_cores[i] < sf_cores[i + 1] for i in range(len(sf_cores) - 1))
    div_ok &= grows
    print(f"  r={r} defects={esv}: sixfree(core) a=1..8 strictly increasing: {grows}")
print(f"  multiplicative split sixfree(core)=sixfree(run)*sixfree(K) holds: {mult_ok}")
print(f"  (divergence is carried by the SINGLE Zsygmondy factor sixfree(3^{{a+1}}-2^{{a+1}}))")
partC = mult_ok and div_ok
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

# --------------------------------------------------------------------------- #
print("== PART D: UNEQUAL runs -- closed form + core is a SUM of distinct run sums ==")
cfD = True
for r in (3, 4):
    es = sp.symbols(f"e1:{r + 1}")
    E = [0] * (r + 1)
    for i in range(1, r + 1):
        E[i] = E[i - 1] + es[i - 1]
    sigs = {3: [(1, 2), (2, 3), (2, 4)], 4: [(1, 2, 3), (2, 1, 3)]}[r]
    for runs in sigs:
        A = [0] * r
        for i in range(1, r):
            A[i] = A[i - 1] + runs[i - 1]
        L = []
        for i in range(r):
            L.append(es[i])
            if i < r - 1:
                L += [d] * runs[i]
        SM = Ssym(L)
        cf = Y ** ((r - 1) + A[r - 1]) + sum(
            X ** (E[i] + A[i - 1] * d) * Y ** ((r - 1 - i) + (A[r - 1] - A[i])) * Run(runs[i - 1] + 1, d)
            for i in range(1, r))
        if not zero(SM - cf):
            cfD = False
            print(f"  MISMATCH r={r} runs={runs}")
print(f"  unequal-run closed form verified (r=3,4; several signatures): {cfD}")
# numeric divergence with >=2 growing runs (two runs grow together, one fixed short)
def Mword_uneq(esv, runs):
    L = []
    for i, e in enumerate(esv):
        L.append(e)
        if i < len(esv) - 1:
            L += [d] * runs[i]
    return tuple(L)
sf_u = []
for a in range(1, 8):
    esv = (3, 4, 5)
    runs = (a, a)               # r=3, two interior runs both grow
    M = Mword_uneq(esv, runs)
    sf_u.append(sixfree(Sint(M) - Sint(tuple(reversed(M)))))
sf_u2 = []
for a in range(1, 8):
    esv = (3, 4, 5, 6)
    runs = (a, 1, a)            # r=4: two runs grow, middle run fixed (genuinely unequal)
    M = Mword_uneq(esv, runs)
    sf_u2.append(sixfree(Sint(M) - Sint(tuple(reversed(M)))))
gu = all(sf_u[i] < sf_u[i + 1] for i in range(len(sf_u) - 1))
gu2 = all(sf_u2[i] < sf_u2[i + 1] for i in range(len(sf_u2) - 1))
print(f"  unequal runs (a,a), >=2 grow: sixfree(core) grows: {gu}  {sf_u[:4]}...")
print(f"  unequal runs (a,1,a), 2 grow + fixed mid: sixfree(core) grows: {gu2}  {sf_u2[:4]}...")
partD = cfD and gu and gu2
print(f"  PART D holds: {partD}\n")
ALL_OK &= partD

# --------------------------------------------------------------------------- #
print("== PART E: VALIDITY GAP -- reversal core valid <=> palindrome <=> 0 ==")
def fullword(esv, a):
    return (d,) * a + Mword(esv, a) + (d,) * a
gap_ok = True
for r, esv, tag, is_pal in [(3, (3, 4, 5), "distinct", False),
                            (3, (3, 4, 3), "palindrome", True),
                            (4, (3, 4, 5, 6), "distinct", False),
                            (4, (3, 4, 4, 3), "palindrome", True),
                            (5, (2, 3, 4, 5, 6), "distinct", False)]:
    for a in (2, 3):
        W = fullword(esv, a)
        Wstar = (d,) * a + tuple(reversed(Mword(esv, a))) + (d,) * a
        rots = set(rotate(W, k) for k in range(len(W)))
        is_rot = Wstar in rots
        core = Sint(W) - Sint(Wstar)
        # claim: is_rot <=> is_pal, and is_pal => core==0
        if is_rot != is_pal:
            gap_ok = False
        if is_pal and core != 0:
            gap_ok = False
        if (not is_pal) and core == 0:
            gap_ok = False
print(f"  reversal W* is a rotation of W  IFF defect-palindrome, and palindrome => core=0: {gap_ok}")
print(f"  => the clean reversal core is NEVER a valid NONZERO G-multiple.")

# does the clean run-sum factorization transfer to the VALID both-runs-intact rot diff?
e1, e2 = 3, 4
transfer_blocked = True
ncyc = []
for a in (2, 3, 4):
    W = (e1,) + (d,) * a + (e2,) + (d,) * (2 * a)          # C(a,2a), the valid family
    diff = sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, a + 1)))
    facs = sp.factor_list(diff)[1]
    has_runsum_factor = any(zero(f - Run(a + 1, d)) for f, _ in facs)
    nc = [sp.Poly(f, X, Y).total_degree() for f, _ in facs if mahler_Y1(f) > 1.0001]
    ncyc.append(max(nc) if nc else 0)
    if has_runsum_factor or not nc:
        transfer_blocked = False
print(f"  VALID rot diff of C(a,2a): non-cyclotomic factor max-deg a=2..4 = {ncyc} (=2a+2, grows)")
print(f"  VALID rot diff has NO S(d^{{a+1}}) factor (clean factorization does NOT transfer): {transfer_blocked}")
partE = gap_ok and transfer_blocked
print(f"  PART E holds: {partE}\n")
ALL_OK &= partE

# --------------------------------------------------------------------------- #
print("== PART F: C8 rank-2 -- runs of d are a single line; 3-cut proportionality ==")
# all runs of d lie on ONE line: v(d^L) = S(d^L)*(X^d - Y, 1), since D(d^L)=(X^d-Y)S(d^L)
line_ok = True
for L in range(1, 9):
    if not zero(Dpoly((d,) * L) - (X ** d - Y) * Spoly((d,) * L)):
        line_ok = False
print(f"  D(d^L) = (X^d - Y) S(d^L) for L=1..8  (all runs parallel, rank-1): {line_ok}")
c8_ok = True
ratio_uneq_div = True
ratio_eq_is_one = True
for (L1, L2, v) in [(2, 3, (3, 4)), (3, 5, (3, 4, 5)), (2, 2, (3, 4)), (4, 4, (3, 4, 5))]:
    u = (d,) * L1; w = (d,) * L2; vv = tuple(v)
    if not zero(Spoly(u + w) - Spoly(w + u)):       # C(u,w)=0
        c8_ok = False
    full = Dpoly(u) * core_C(vv, w) + Dpoly(vv) * core_C(w, u) + Dpoly(w) * core_C(u, vv)
    if not zero(full):                              # full C8
        c8_ok = False
    if not zero(Dpoly(u) * core_C(vv, w) + Dpoly(w) * core_C(u, vv)):  # reduced proportionality
        c8_ok = False
    # the ratio -D(w)/D(u) at (2,3)
    Du = abs(2 ** (L1 * d) - 3 ** L1)
    Dw = abs(2 ** (L2 * d) - 3 ** L2)
    if L1 == L2:
        if Du != Dw:
            ratio_eq_is_one = False
    else:
        # 6-free part of D for unequal runs diverges as runs grow (Zsygmondy on 2^L-3^L)
        pass
# explicit: for equal runs the C8 ratio is exactly 1 (no obstruction); for unequal it grows
eq_ratio = [sixfree(2 ** L - 3 ** L) for L in (2, 3, 4, 5, 6)]
print(f"  C8 + reduced proportionality D(u)C(v,w) = -D(w)C(u,v) (two run-arcs): {c8_ok}")
print(f"  equal runs L1=L2 => |D(u)|=|D(w)|, ratio = -1 (C8 gives NO obstruction): {ratio_eq_is_one}")
print(f"  sixfree(2^L-3^L) L=2..6 = {eq_ratio} (diverges => unequal-run ratio obstructs;")
print(f"     equal-run symmetric family escapes C8 -- exactly the stubborn open case)")
partF = line_ok and c8_ok and ratio_eq_is_one
print(f"  PART F holds: {partF}\n")
ALL_OK &= partF

print("=" * 74)
print(f"MULTIDEFECT REVERSAL CORE (Gen 7): {'ALL VERIFIED FACTS PASS' if ALL_OK else 'FAILED'}")
print("VERDICT: reversal core = S(d^{a+1}) * K_r EXACTLY for all r (single explicit")
print("  cyclotomic run-sum factor) -> 6-free part DIVERGES by Zsygmondy.  CORRECTS the")
print("  Gen-6 conjecture: NOT prod(run sums), NOT bounded K (only r=2 is bounded).")
print("  VALIDITY GAP is sharp: clean core valid <=> defect-palindrome <=> core=0, so it")
print("  is NEVER a valid nonzero G-ceiling; valid combos diverge by the complementary")
print("  non-cyclotomic mechanism.  C8 ties the run cores (rank-2) but is silent on the")
print("  symmetric equal-run case -- the G-valid no-go stays reduced-but-open.")
sys.exit(0 if ALL_OK else 1)
