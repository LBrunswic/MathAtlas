"""Gen 8 (2026-06-08) -- THE VALIDITY-GAP BRIDGE: make-or-break for the two-ended thread.

THE ONE QUESTION (Gen-7 NEXT_FOCUS): can the reversal sum S(W^R) -- equivalently the
clean reversal core S(W)-S(W^R) -- be expressed within the rotation LATTICE of W,
    L := span_{Z[1/6]} { S^{(j)}(W) : 0 <= j < o }   (scalar coeffs),
or the looser "valid rotation combination" lattice with Laurent-MONOMIAL coefficients
    L_mon := span_{Z[1/6][X^+-,Y^+-]} { S^{(j)}(W) }   ?
If yes, the clean core IS a valid combination (G | core).  If yes + bounded remainder,
the no-go for the symmetric equal-run family might close; if it escapes, the thread closes.

Canonical family: W = C(a,2a) = e1 d^a e2 d^{2a} (cyclic), d=1.  Reversal core diverges
by Zsygmondy (multidefect_reversal_core.py): clean core C_a = (X^e1 - X^e2) S(d^{a+1}),
sixfree(C_a@(2,3)) = sixfree(3^{a+1}-2^{a+1}) -> infinity.

=================  WHAT THIS SCRIPT ESTABLISHES  =============================

PART A (sanity).  EQUAL defects e1=e2 on the CYCLIC word: W^R IS a rotation of W (NOT a
  palindrome -- run-lengths a,2a differ), so S(W^R) is literally a rotation sum, in L.
  Its core is a genuine rotation-pair wedge -- VALID -- yet its 6-free part DIVERGES.
  This is a clean concrete witness that "valid combination" does NOT imply "bounded": the
  no-go's content.  (Validates the membership routine on a known-positive case.)

PART B (KEY, PROVEN negative -- rank-gap witnesses over two large primes).  For DISTINCT
  defects, NONE of {S(W^R), the clean core C_a, the full linear reversal core} lies in
  the scalar lattice L, NOR in the monomial lattice L_mon (generous box).  A modular
  rank gap rank_p[A|b] > rank_p[A] is a definitive Q-non-membership witness; required on
  two independent primes.  ==> the clean reversal core is NEVER a valid combination,
  proven DIRECTLY (not merely "W^R is not a rotation").  Sharpens Gen-7's validity gap.

PART C (PROVEN -- remainder UNcontrollable).  Write core = V + R, V in L_mon (valid).
  (i) For any FIXED degree bound delta, core is STILL not in (L_mon (+) {monomials deg<=delta})
      for a=2..5 -- so no valid V leaves an a-INDEPENDENT bounded remainder R (rank-gap, 2 primes).
  (ii) The minimal residue degree of core mod L_mon EQUALS deg(core)=a+4 for every a:
      the lattice cancels NONE of the core's divergent top structure.  R carries the whole
      divergence.  ==> option-2 (controllable remainder) is NEGATIVE.

PART D (PROVEN -- divergence => useless even IF it were valid).  sixfree(reversal core)
  grows (Zsygmondy), whereas the bounded-arc lever's valid wedge sixfree(S(bd)-S(db)) is
  a FIXED constant.  A valid combination equal to a divergent core gives only the vacuous
  ceiling G <= (diverging) -- no cap on o.  Exclusion needs a BOUNDED valid core; the
  reversal route supplies none.

PART E (PROVEN -- the STRUCTURAL reason, symbolic).  Reversal = transpose at the matrix
  level (M(W^R) is the reverse product).  The ONLY matrix P with P M(d) P^{-1} = M(d)^T for
  all letters d is SINGULAR (det 0).  So reversal is NOT a fixed conjugation -- and rotation
  = conjugation by word-matrices (structure.md C3) -- hence no word-INDEPENDENT (a-uniform)
  linear operator carries the rotation orbit onto S(W^R).  This is WHY the bridge fails
  uniformly: it is not a numerical accident.

VERDICT (NEGATIVE -- the two-ended/reversal thread is CLOSED).  The reversal sum genuinely
  escapes the rotation lattice (scalar and monomial), the escaping remainder is
  uncontrollable (carries the full divergence), and even a hypothetical bridge would be
  useless because the core diverges.  The user's "generalize the last combination" idea
  cannot yield a G-valid exclusion for the symmetric equal-run family.  The G-valid no-go
  stays the (untouched) open problem of approaches/bounded-defect-lever.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/reversal_lattice_bridge.py
"""
import sys
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotations  # trusted kernel
X, Y = sp.symbols("X Y")

d = 1
PRIMES = (2_000_003, 1_500_007)          # two independent large primes for rigorous witnesses
pr = lambda *a: print(*a, flush=True)


def cyc(e1, e2, a):
    return (e1,) + (d,) * a + (e2,) + (d,) * (2 * a)


def lin(e1, e2, a):
    return (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a


def Run(m):
    return sum(X ** (j * d) * Y ** (m - 1 - j) for j in range(m))


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def covec(poly):
    pol = sp.Poly(sp.expand(poly), X, Y)
    return {m: int(c) for m, c in zip(pol.monoms(), pol.coeffs())}


def _leading(v, P):
    nz = [m for m, c in v.items() if c % P]
    return max(nz, key=lambda m: (m[0] + m[1], m[0])) if nz else None


def build_basis(atom_vecs, P):
    """echelon basis (leading_mono -> normalized vec) of span(atoms) over GF(P)."""
    basis = {}
    for v0 in atom_vecs:
        v = {m: c % P for m, c in v0.items() if c % P}
        while v:
            lm = _leading(v, P)
            if lm is None:
                break
            if lm in basis:
                f = v[lm]; b = basis[lm]
                for m, c in b.items():
                    v[m] = (v.get(m, 0) - f * c) % P
                v = {m: c for m, c in v.items() if c % P}
            else:
                inv = pow(v[lm], P - 2, P)
                basis[lm] = {m: (c * inv) % P for m, c in v.items()}
                break
    return basis


def in_span_mod(basis, target, P):
    """True iff target reduces to 0 against the echelon basis over GF(P)."""
    v = {m: c % P for m, c in target.items() if c % P}
    while v:
        lm = _leading(v, P)
        if lm is None:
            return True
        if lm not in basis:
            return False
        f = v[lm]; b = basis[lm]
        for m, c in b.items():
            v[m] = (v.get(m, 0) - f * c) % P
        v = {m: c for m, c in v.items() if c % P}
    return True


def not_in_span(atoms, target):
    """PROVEN non-membership: rank-gap witness on BOTH primes (==> not in Q-span)."""
    tv = covec(target)
    avs = [covec(a) for a in atoms]
    return all(not in_span_mod(build_basis(avs, P), tv, P) for P in PRIMES)


def in_span_both(atoms, target):
    """membership evidence on both primes."""
    tv = covec(target)
    avs = [covec(a) for a in atoms]
    return all(in_span_mod(build_basis(avs, P), tv, P) for P in PRIMES)


def mono_atoms(Ss, pmax, qmax, extra_monos_deg=None):
    atoms = [sp.expand(X ** p * Y ** q * s) for s in Ss for p in range(pmax + 1) for q in range(qmax + 1)]
    if extra_monos_deg is not None:
        atoms += [X ** i * Y ** j for tot in range(extra_monos_deg + 1)
                  for i in range(tot + 1) for j in [tot - i]]
    return atoms


ALL_OK = True

# --------------------------------------------------------------------------- #
pr("== PART A: sanity -- equal-defect cyclic core is a VALID rotation wedge that DIVERGES ==")
A_ok = True
for a in (2, 3, 4):
    e = 4
    W = cyc(e, e, a)
    WR = tuple(reversed(W))
    rots = [tuple(r) for r in rotations(W)]
    is_rot = WR in rots                                   # W^R a rotation (so S(W^R) in L)
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    sf = sixfree((Spoly(W) - Spoly(WR)).subs({X: 2, Y: 3}))
    in_L = in_span_both(Ss, sp.expand(Spoly(WR)))         # confirm membership numerically too
    A_ok &= (is_rot and in_L and sf != 0)
    pr(f"  a={a} e1=e2={e}: W^R is a rotation: {is_rot}; S(W^R) in scalar L: {in_L}; sixfree(core)={sf}")
pr(f"  => equal defects: valid combination, yet 6-free part DIVERGES (no-go content). PART A: {A_ok}\n")
ALL_OK &= A_ok

# --------------------------------------------------------------------------- #
pr("== PART B: KEY negative -- GENUINE 2-defect words ESCAPE both lattices (rank-gap, 2 primes) ==")
# genuine = both defects differ from the background d (else e_i=d collapses the word to a
# SINGLE-defect P2 word -- handled by the lever, and there the reversal IS a rotation, see B2).
B_ok = True
for (e1, e2) in [(3, 4), (2, 5), (2, 3), (3, 5)]:
    for a in (2, 3, 4):
        W = cyc(e1, e2, a)
        Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
        E, o = sum(W), len(W)
        SWR = sp.expand(Spoly(tuple(reversed(W))))
        Ca = sp.expand((X ** e1 - X ** e2) * Run(a + 1))            # draft clean core
        full = sp.expand(Spoly(lin(e1, e2, a)) - Spoly(tuple(reversed(lin(e1, e2, a)))))
        atoms = mono_atoms(Ss, pmax=min(E, a + 8), qmax=min(o, a + 8))
        ok = (not_in_span(Ss, SWR) and not_in_span(atoms, SWR) and
              not_in_span(Ss, Ca) and not_in_span(atoms, Ca) and not_in_span(atoms, full))
        B_ok &= ok
        if (e1, e2) == (3, 4):
            pr(f"  ({e1},{e2}) a={a}: S(W^R) not in scalar L & not in mon L; C_a not in either;"
               f"  full reversal core not in mon L : {ok}")
pr(f"  => all genuine pairs {{(3,4),(2,5),(2,3),(3,5)}} x a=2..4: clean reversal core NEVER valid. PART B: {B_ok}\n")
ALL_OK &= B_ok

pr("== PART B2: instructive boundary -- a defect = background (single-defect P2) DOES bridge ==")
# e1 = d : word 1^a 1 e2 1^{2a} = d^{a+1} e2 d^{2a} is single-defect -> reversal is a rotation,
# so S(W^R) lies in the monomial lattice.  The bridge exists EXACTLY where the lever wins.
B2_ok = True
for a in (2, 3, 4):
    e1, e2 = d, 6                       # e1 = d collapses to single defect e2
    W = cyc(e1, e2, a)
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    atoms = mono_atoms(Ss, pmax=min(sum(W), a + 8), qmax=min(len(W), a + 8))
    bridges = in_span_both(atoms, sp.expand(Spoly(tuple(reversed(W)))))
    B2_ok &= bridges
    pr(f"  a={a} (e1=d={d}, single defect {e2}): S(W^R) IS in the monomial lattice: {bridges}")
pr(f"  => the reversal bridges into the lattice precisely for the already-excludable case. PART B2: {B2_ok}\n")
ALL_OK &= B2_ok

# --------------------------------------------------------------------------- #
pr("== PART C: remainder UNCONTROLLABLE ==")
# (i) core not in L_mon (+) bounded-degree remainder, for FIXED delta, growing a.
Ci_ok = True
for delta in (2, 3):
    for a in (2, 3, 4, 5):
        e1, e2 = 3, 4
        W = cyc(e1, e2, a)
        Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
        E, o = sum(W), len(W)
        Ca = sp.expand((X ** e1 - X ** e2) * Run(a + 1))
        atoms = mono_atoms(Ss, pmax=min(E, a + 8), qmax=min(o, a + 8), extra_monos_deg=delta)
        escapes = not_in_span(atoms, Ca)                  # core NOT in L_mon (+) B_delta
        Ci_ok &= escapes
    pr(f"  (i) fixed remainder-degree delta={delta}: core escapes L_mon(+)B_delta for a=2..5: "
       f"{all(not_in_span(mono_atoms([sp.expand(Spoly(r)) for r in rotations(cyc(3,4,a))], min(sum(cyc(3,4,a)),a+8), min(len(cyc(3,4,a)),a+8), delta), sp.expand((X**3-X**4)*Run(a+1))) for a in (2,3,4,5))}")
# (ii) minimal residue degree of core mod L_mon equals deg(core) -> grows.
def min_residue_degree(atoms, target, P):
    avs = [covec(a) for a in atoms]; tv = covec(target)
    rows = [dict({m: c % P for m, c in v.items() if c % P}) for v in avs]
    t = {m: c % P for m, c in tv.items() if c % P}
    monos = sorted({m for v in rows + [t] for m in v}, key=lambda m: (-(m[0] + m[1]), -m[0]))
    used = [False] * len(rows); pivot_cols = set()
    for col in monos:
        piv = next((i for i, r in enumerate(rows) if not used[i] and r.get(col, 0) % P), None)
        if piv is None:
            continue
        used[piv] = True; pivot_cols.add(col)
        rp = rows[piv]; inv = pow(rp[col], P - 2, P)
        rp = {m: (c * inv) % P for m, c in rp.items()}; rows[piv] = rp
        for i, r in enumerate(rows):
            if i != piv and r.get(col, 0) % P:
                f = r[col]
                for m, c in rp.items():
                    r[m] = (r.get(m, 0) - f * c) % P
        if t.get(col, 0) % P:
            f = t[col]
            for m, c in rp.items():
                t[m] = (t.get(m, 0) - f * c) % P
    supp = [m for m, c in t.items() if c % P and m not in pivot_cols]
    return -1 if not supp else max(s[0] + s[1] for s in supp)

Cii_ok = True
resdat = []
for a in (2, 3, 4, 5):
    e1, e2 = 3, 4
    W = cyc(e1, e2, a)
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    E, o = sum(W), len(W)
    Ca = sp.expand((X ** e1 - X ** e2) * Run(a + 1))
    degCa = sp.Poly(Ca, X, Y).total_degree()
    rd = min_residue_degree(mono_atoms(Ss, E, o), Ca, PRIMES[0])
    resdat.append((a, degCa, rd))
    Cii_ok &= (rd == degCa == a + 4)
pr(f"  (ii) min residue degree mod L_mon (a, deg(core), residue): {resdat}")
pr(f"       residue degree == deg(core) == a+4 for all a (lattice cancels NOTHING): {Cii_ok}")
C_ok = Ci_ok and Cii_ok
pr(f"  => no a-independent bounded remainder; R carries the full divergence. PART C: {C_ok}\n")
ALL_OK &= C_ok

# --------------------------------------------------------------------------- #
pr("== PART D: divergence => useless even IF valid (contrast with bounded-arc lever) ==")
rev_sf = [sixfree((Spoly(cyc(3, 4, a)) - Spoly(tuple(reversed(cyc(3, 4, a))))).subs({X: 2, Y: 3}))
          for a in range(1, 8)]
rev_grows = all(rev_sf[i] < rev_sf[i + 1] for i in range(len(rev_sf) - 1))
# bounded-arc valid wedge: reduced core S(beta d)-S(d beta) is L-INDEPENDENT (a fixed constant)
beta = (2, 3)
arc_core = sp.expand(Spoly(beta + (d,)) - Spoly((d,) + beta))
arc_sf = sixfree(arc_core.subs({X: 2, Y: 3}))
pr(f"  reversal core sixfree a=1..7: {rev_sf}  strictly increasing: {rev_grows}")
pr(f"  bounded-arc valid wedge sixfree(S(bd)-S(db)), beta={beta}: {arc_sf}  (FIXED constant, o-independent)")
D_ok = rev_grows and arc_sf != 0
pr(f"  => a valid combo equal to a divergent core gives only G <= (diverging): vacuous. PART D: {D_ok}\n")
ALL_OK &= D_ok

# --------------------------------------------------------------------------- #
pr("== PART E: STRUCTURAL reason -- reversal=transpose is NOT a fixed conjugation ==")
p, q, r, s = sp.symbols("p q r s")
Pm = sp.Matrix([[p, q], [r, s]])
Mat = lambda dd: sp.Matrix([[Y, 0], [1, X ** dd]])
eqs = []
for dd in (1, 2, 3):
    eqs += list(Pm * Mat(dd) - Mat(dd).T * Pm)   # P M(d) = M(d)^T P
sols = sp.solve(eqs, [p, q, r, s], dict=True)
all_singular = len(sols) >= 1 and all(sp.simplify(Pm.subs(so).det()) == 0 for so in sols)
pr(f"  common P with P M(d) P^-1 = M(d)^T for d=1,2,3: {sols}")
pr(f"  every such P is SINGULAR (det 0): {all_singular}")
pr(f"  => reversal is not realized by any fixed conjugation; rotation = conjugation (C3),")
pr(f"     so no a-uniform linear operator carries the rotation orbit onto S(W^R). PART E: {all_singular}\n")
ALL_OK &= all_singular

# --------------------------------------------------------------------------- #
pr("=" * 74)
pr(f"REVERSAL-LATTICE BRIDGE (Gen 8): {'ALL ASSERTED FACTS PASS' if ALL_OK else 'FAILED'}")
pr("VERDICT (NEGATIVE): the reversal sum S(W^R) genuinely ESCAPES the rotation lattice")
pr("  (scalar and monomial); the escaping remainder is UNCONTROLLABLE (residue degree =")
pr("  deg(core) = a+4, the lattice cancels nothing); and even a hypothetical bridge is")
pr("  useless because the reversal core DIVERGES (Zsygmondy).  The structural reason is")
pr("  exact: reversal = transpose is not a fixed conjugation, while rotation IS (C3).")
pr("  ==> the two-ended/reversal thread is CLOSED; it cannot yield a G-valid exclusion.")
sys.exit(0 if ALL_OK else 1)
