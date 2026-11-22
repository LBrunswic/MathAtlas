"""Chase the user's hint on the proven P1 identity (Gen 5, 2026-06-08).

Proven P1 identity (S = the draft's chi-normalized cocycle, S(ab)=S(a)+chi(a)S(b)):

  chi(x') S(xuy) - chi(x) S(x'uy')
     = [chi(x') S(x) - chi(x) S(x')]                 (u-free boundary term)
       + chi(x) chi(x') chi(u) [S(y) - S(y')].

USER HINT: divide by chi(x)chi(x')chi(u), impose the balance chi(xuy)=chi(x'uy')
(i.e. chi(x)chi(y)=chi(x')chi(y')), reassemble with the cocycle. Introduce the
suffix-weighted (reversed) sum  hatS(w) := S(w)/chi(w), whose cocycle reads
  hatS(ab) = hatS(b) + hatS(a)/chi(b).
QUESTION: does
  Q := [chi(x') S(xuy) - chi(x) S(x'uy')] / (chi(x)chi(x')chi(u))
collapse to a CLEAN u-free difference of two (shorter/rearranged) cocycle sums?

This script settles it, every step certified as a Z[X,Y] identity via the kernel.

  PART A  free-symbol algebra: the two normalized closed forms + Su cancellation.
  PART B  real kernel: hatS suffix-cocycle is a Z[X,Y] identity; both closed forms
          are exact Z[X,Y] identities over a grid of block-length signatures.
  PART C  the u-dependence test + shorter-word candidate search (generic AND under
          balance): is Q ever a u-free single difference hatS(w1)-hatS(w2) /
          S(w1)-S(w2) up to a unit?  Pin the obstruction.
  PART D  reversal/transpose: hatS is the suffix reading (prefix sums of w^R).

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/p1_hint_reduction.py
"""
import sys, itertools
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, X, Y          # trusted kernel, homogenized S

ALL_OK = True

# --------------------------------------------------------------------------- #
# normalized functionals built on the trusted kernel                          #
# --------------------------------------------------------------------------- #
def lenw(w):  return len(w)
def sumw(w):  return sum(w)
def chi(w):   return X ** sumw(w) / Y ** lenw(w)         # the unit character

def sig(w):                                             # the draft's S (= sigma)
    n = len(w)
    if n == 0:
        return sp.Integer(0)
    return sp.together(Spoly(tuple(w)) / Y ** (n - 1))

def hatS(w):                                            # suffix-weighted sum S/chi
    if len(w) == 0:
        return sp.Integer(0)
    return sp.together(sig(w) / chi(w))

def W(*parts):                                          # concatenate block tuples
    out = ()
    for p in parts:
        out += tuple(p)
    return out

# --------------------------------------------------------------------------- #
# PART A -- free-symbol algebra                                               #
# --------------------------------------------------------------------------- #
print("== PART A: free-symbol algebra (the user's manipulation) ==")
Sx, Sxp, Sy, Syp, Su = sp.symbols("Sx Sxp Sy Syp Su")
cx, cxp, cy, cyp, cu = sp.symbols("cx cxp cy cyp cu")
S_xuy   = Sx  + cx  * Su + cx  * cu * Sy          # S(xuy)  via cocycle
S_xpuyp = Sxp + cxp * Su + cxp * cu * Syp         # S(x'uy')
LHS = cxp * S_xuy - cx * S_xpuyp
hSx, hSxp, hSy, hSyp, hSu = Sx/cx, Sxp/cxp, Sy/cy, Syp/cyp, Su/cu

Q  = sp.expand(LHS / (cx * cxp * cu))             # divide by chi(x)chi(x')chi(u)
QB = sp.expand(LHS / (cx * cxp))                  # divide by chi(x)chi(x')

# form A:  Q = [S(y)-S(y')] + [hatS(xu)-hatS(x'u)],  hatS(xu)=hatS(u)+hatS(x)/chi(u)
formA = (Sy - Syp) + ((hSu + hSx/cu) - (hSu + hSxp/cu))
# form B:  QB = [hatS(x)-hatS(x')] + [S(uy)-S(uy')],  S(uy)=S(u)+chi(u)S(y)
formB = (hSx - hSxp) + ((Su + cu*Sy) - (Su + cu*Syp))
# merged: Q = chi(y) hatS(xuy) - chi(y') hatS(x'uy')
merged = cy*(S_xuy/(cx*cu*cy)) - cyp*(S_xpuyp/(cxp*cu*cyp))

cA = sp.simplify(Q  - formA)
cB = sp.simplify(QB - formB)
cM = sp.simplify(Q  - merged)
cSu = sp.expand(Q).coeff(Su)
cbd = sp.simplify((cxp*Sx - cx*Sxp) - cx*cxp*(hSx - hSxp))   # boundary normalizes
for name, val in [("Q  = [S(y)-S(y')] + [hatS(xu)-hatS(x'u)]", cA),
                  ("QB = [hatS(x)-hatS(x')] + [S(uy)-S(uy')]", cB),
                  ("Q  = chi(y)hatS(xuy) - chi(y')hatS(x'uy')", cM),
                  ("boundary = chi(x)chi(x')[hatS(x)-hatS(x')]", cbd)]:
    print(f"  {name:48s} residual = {val}")
print(f"  inner-core S(u) coeff in Q (must be 0): {cSu}")
partA = all(v == 0 for v in (cA, cB, cM, cbd)) and cSu == 0
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
# PART B -- real kernel Z[X,Y] identities                                     #
# --------------------------------------------------------------------------- #
print("== PART B: real-kernel Z[X,Y] identities ==")
letters = (1, 2, 3)
def words_of_len(L):
    return list(itertools.product(letters, repeat=L)) if L > 0 else [()]

# B1: suffix cocycle hatS(ab) = hatS(b) + hatS(a)/chi(b)  (defines hatS as reversed)
print("  B1: suffix cocycle hatS(ab)=hatS(b)+hatS(a)/chi(b)")
b1_fail = 0; b1_n = 0
for la, lb in [(1,1),(2,1),(1,2),(2,2),(3,1),(1,3),(2,3)]:
    for a in words_of_len(la):
        for b in words_of_len(lb):
            d = sp.simplify(hatS(W(a,b)) - (hatS(b) + hatS(a)/chi(b)))
            b1_n += 1
            if d != 0: b1_fail += 1
print(f"     {b1_n} instances, failures: {b1_fail}")

# B2: both closed forms as exact Z[X,Y] identities over block-length signatures
print("  B2: closed forms over block-length signatures")
def Q_real(x, xp, y, yp, u):
    num = chi(xp)*sig(W(x,u,y)) - chi(x)*sig(W(xp,u,yp))
    return sp.together(num / (chi(x)*chi(xp)*chi(u)))
def QB_real(x, xp, y, yp, u):
    num = chi(xp)*sig(W(x,u,y)) - chi(x)*sig(W(xp,u,yp))
    return sp.together(num / (chi(x)*chi(xp)))
def formA_real(x, xp, y, yp, u):
    return (sig(y)-sig(yp)) + (hatS(W(x,u))-hatS(W(xp,u)))
def formB_real(x, xp, y, yp, u):
    return (hatS(x)-hatS(xp)) + (sig(W(u,y))-sig(W(u,yp)))

length_signatures = [
    (1,1,1,1,1),(1,2,1,2,1),(2,1,2,1,2),(2,2,1,1,2),
    (1,1,2,2,3),(3,1,1,2,1),(2,2,2,2,2),(1,1,1,1,2),
]
import random
b2_fail = 0; b2_n = 0
for sig_ in length_signatures:
    lx,lxp,ly,lyp,lu = sig_
    random.seed(sum(s*10**i for i,s in enumerate(sig_)))
    combos = list(itertools.product(words_of_len(lx), words_of_len(lxp),
                                     words_of_len(ly), words_of_len(lyp),
                                     words_of_len(lu)))
    if len(combos) > 16: combos = random.sample(combos, 16)
    ok = True
    for x,xp,y,yp,u in combos:
        dA = sp.simplify(Q_real(x,xp,y,yp,u)  - formA_real(x,xp,y,yp,u))
        dB = sp.simplify(QB_real(x,xp,y,yp,u) - formB_real(x,xp,y,yp,u))
        b2_n += 1
        if dA != 0 or dB != 0:
            ok = False; b2_fail += 1
    print(f"     lengths {sig_}: {len(combos)} instances -> {'OK' if ok else 'FAIL'}")
print(f"     total {b2_n}, failures: {b2_fail}")
partB = (b1_fail == 0 and b2_fail == 0)
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- the u-dependence test + shorter-word candidate search             #
# --------------------------------------------------------------------------- #
print("== PART C: is Q a u-free shorter-word difference? ==")

def is_monomial(e):
    """True iff e is +/- (rational const) * X^i * Y^j (Laurent), i.e. a unit."""
    e = sp.expand(e)
    if e == 0:
        return False
    if e.free_symbols - {X, Y}:
        return False
    return len(sp.Add.make_args(e)) == 1

def is_unit_ratio(a, b):
    """True iff a/b is a Laurent monomial in X,Y (a ~ b up to a Z[1/6] unit)."""
    if b == 0:
        return a == 0
    r = sp.cancel(sp.together(a) / sp.together(b))
    n, d = sp.fraction(sp.together(r))
    return is_monomial(n) and is_monomial(d)

# C1: u-dependence -- fix x,x',y,y', vary u over DIFFERENT chi-signatures; does Q move?
print("  C1: u-dependence of Q (fix x,x',y,y'; vary u)")
u_variants = [(1,), (2,), (3,), (1,1), (1,2), (2,1)]   # different chi-signatures
xx = [((1,),(2,),(1,),(3,)),       # generic (x,x',y,y')
      ((1,2),(2,1),(3,),(1,)),
      ((2,),(2,),(1,),(3,))]       # x = x' (=> hatS(x)=hatS(x'): Q should be u-free)
for (x,xp,y,yp) in xx:
    vals = [sp.simplify(Q_real(x,xp,y,yp,u)) for u in u_variants]
    distinct = len({sp.srepr(sp.simplify(v)) for v in vals})
    ufree = (distinct == 1)
    print(f"     x={x} x'={xp} y={y} y'={yp}: distinct Q over {len(u_variants)} u's = {distinct}"
          f"  -> {'u-FREE' if ufree else 'u-DEPENDENT'}"
          f"   (hatS(x)=hatS(x')? {sp.simplify(hatS(x)-hatS(xp))==0})")

# C2: shorter-word candidate search.  Is Q ~ (unit) * target for any target built
#     from x,x',y,y' only (u gone)?  Test generically and under balance.
print("  C2: candidate u-free shorter-word targets  Q ?~ target")
def candidates(x, xp, y, yp):
    cs = {
        "hatS(yx)-hatS(y'x')":  hatS(W(y,x))  - hatS(W(yp,xp)),
        "hatS(xy)-hatS(x'y')":  hatS(W(x,y))  - hatS(W(xp,yp)),
        "S(yx)-S(y'x')":        sig(W(y,x))   - sig(W(yp,xp)),
        "S(xy)-S(x'y')":        sig(W(x,y))   - sig(W(xp,yp)),
        "hatS(x)-hatS(x')":     hatS(x)       - hatS(xp),
        "S(y)-S(y')":           sig(y)        - sig(yp),
        "hatS(xy)-hatS(y'x')":  hatS(W(x,y))  - hatS(W(yp,xp)),
    }
    return cs

# balance: chi(x)chi(y)=chi(x')chi(y')  <=>  |x|+|y|=|x'|+|y'| and lenx+leny=lenx'+leny'
def balanced_quads():
    out = []
    for lx,lxp,ly,lyp in itertools.product((1,2),repeat=4):
        if lx+ly != lxp+lyp: continue          # length balance
        for x in words_of_len(lx):
            for xp in words_of_len(lxp):
                for y in words_of_len(ly):
                    for yp in words_of_len(lyp):
                        if sumw(x)+sumw(y) == sumw(xp)+sumw(yp):   # weight balance
                            out.append((x,xp,y,yp))
    random.seed(7); random.shuffle(out)
    return out[:40]

for label, quads, u in [("generic (no balance)",
                         [((1,),(2,),(1,),(3,)), ((1,2),(2,1),(3,),(1,)),
                          ((2,),(1,),(1,2),(3,))], (1,)),
                        ("under balance chi(x)chi(y)=chi(x')chi(y')",
                         balanced_quads(), (2,))]:
    cand_pass = {k: 0 for k in candidates((1,),(2,),(1,),(3,))}
    cand_tot = 0
    for (x,xp,y,yp) in quads:
        if label.startswith("under"):
            # double-check balance really holds
            if sp.simplify(chi(x)*chi(y) - chi(xp)*chi(yp)) != 0:
                continue
        q = Q_real(x,xp,y,yp,u)
        if sp.simplify(q) == 0:    # skip trivial zeros
            continue
        cand_tot += 1
        for k, tgt in candidates(x,xp,y,yp).items():
            if is_unit_ratio(q, tgt):
                cand_pass[k] += 1
    print(f"  [{label}]  ({cand_tot} nonzero instances)")
    for k, c in cand_pass.items():
        verdict = "ALWAYS unit-ratio" if c == cand_tot and cand_tot>0 else f"{c}/{cand_tot}"
        print(f"     Q ~ {k:24s}: {verdict}")

# C2b: the airtight kill -- a genuine reduction Q ~ (unit)*target would need the
#      unit-ratio to hold for ALL u (the unit X^aY^b may depend on u, so a single-u
#      hit is not enough).  Split DEGENERATE (S(y)=S(y'), the known unit family,
#      where the y-term vanishes and Q collapses to the pure suffix-extraction)
#      from GENERIC (S(y)!=S(y')).  Claim: survivors exist ONLY in the degenerate
#      family; GENERICALLY no u-free target works for all u.
print("  C2b: holds-for-ALL-u test, split by S(y)=?=S(y')")
allu = [(1,), (2,), (3,), (1,1), (2,1), (1,2), (2,2)]
quads = [
    ((1,),(2,),(2,),(1,)),        # y,y' single letters -> S(y)=S(y') (degenerate)
    ((2,1),(1,1),(1,),(2,)),      # degenerate again (single-letter y,y')
    ((1,2),(2,1),(1,2),(2,1)),    # GENERIC: S(y)!=S(y'), chi-balanced
    ((2,1),(1,2),(1,2),(2,1)),    # GENERIC: S(y)!=S(y'), chi-balanced
]
for (x,xp,y,yp) in quads:
    if sp.simplify(chi(x)*chi(y) - chi(xp)*chi(yp)) != 0:
        print(f"     x={x} x'={xp} y={y} y'={yp}: NOT balanced, skipped"); continue
    degen = (sp.simplify(sig(y) - sig(yp)) == 0)
    cand = candidates(x,xp,y,yp)
    survs = [k for k, tgt in cand.items()
             if all(is_unit_ratio(Q_real(x,xp,y,yp,u), tgt) for u in allu)]
    tag = "DEGENERATE S(y)=S(y')" if degen else "GENERIC S(y)!=S(y')"
    print(f"     x={x} x'={xp} y={y} y'={yp}  [{tag}]: "
          f"u-free targets working for ALL u = {len(survs)} {survs if survs else ''}")

# C3: the precise obstruction -- Q is u-free iff chi(u)=1 (impossible for |u|>0).
print("  C3: obstruction -- Q's u-dependence vanishes iff chi(u)=1")
# Q = [S(y)-S(y')] + [hatS(x)-hatS(x')]/chi(u).  d Q / d(1/chi(u)) = hatS(x)-hatS(x').
# So Q is u-free  <=>  hatS(x)=hatS(x')  OR formally chi(u)=1.  Show the second:
cu_sym = sp.symbols("chi_u", positive=True)
x,xp,y,yp = (1,),(2,),(1,),(3,)
Qsym = (sig(y)-sig(yp)) + (hatS(x)-hatS(xp))/cu_sym
# at chi_u -> 1 this is the would-be u-free value; the discrepancy is the obstruction
obstruction = sp.simplify(Qsym - Qsym.subs(cu_sym, 1))
print(f"     Q - Q|_(chi_u=1) = (hatS(x)-hatS(x'))(1/chi_u - 1) ; "
      f"hatS(x)-hatS(x') = {sp.simplify(hatS(x)-hatS(xp))}")
print(f"     => nonzero unless chi_u=1 (reconciles old Move-2 obstruction chi(xuy)=1)")
partC = True   # this part is descriptive; C2 results are the finding
print(f"  PART C complete (findings reported above)\n")

# --------------------------------------------------------------------------- #
# PART D -- reversal / transpose: hatS is the suffix reading                  #
# --------------------------------------------------------------------------- #
print("== PART D: hatS(w) = suffix reading (prefix sums of reversed word) ==")
def hatS_reversed_formula(w):
    """hatS(w) = sum_{j=1..o} X^{-e^R_j} Y^{j},  e^R_j = prefix sums of reverse(w)."""
    wr = tuple(reversed(w))
    o = len(wr)
    acc = 0
    tot = sp.Integer(0)
    for j in range(1, o + 1):
        acc += wr[j - 1]
        tot += X ** (-acc) * Y ** j
    return tot
d_fail = 0; d_n = 0
for L in (1, 2, 3, 4):
    for w in words_of_len(L):
        d = sp.simplify(hatS(w) - hatS_reversed_formula(w))
        d_n += 1
        if d != 0: d_fail += 1
print(f"  hatS(w) == sum X^(-eR_j) Y^j over {d_n} words: failures = {d_fail}")
partD = (d_fail == 0)
print(f"  PART D holds: {partD}\n")
ALL_OK &= partD

print("=" * 64)
print(f"P1 HINT REDUCTION: {'ALL CERTIFIED PARTS PASS' if ALL_OK else 'FAILED'}")
sys.exit(0 if ALL_OK else 1)
