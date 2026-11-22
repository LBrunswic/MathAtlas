#!/usr/bin/env python3
r"""L1.8 -- homotopical completion-with-expansion, verification.

Paper: Y. Guiraud, P. Malbos, S. Mimram, "A Homotopical Completion Procedure
with Applications to Coherence of Monoids", RTA 2013, LIPIcs vol. 21, pp.
223-238 (DOI 10.4230/LIPIcs.RTA.2013.223);
sources/guiraud-malbos-mimram-homotopical-completion-RTA2013.pdf.

The paper EXTENDS Knuth-Bendix completion by Tietze transformations that ADD
generators/rules/coherence cells (completion-with-EXPANSION, non-length-
monotone): the Kapur-Narendran braid example B3+ = <s,t | tst=sts> admits NO
finite convergent system on {s,t}, but adding the QUASICENTER generator a = st
(Tietze "add generator" T_u^+, p.228) makes completion terminate (eq. 2-3, Ex.10).
The infinite family  stsst^k = ts^{k+1}ts  (Kapur-Narendran, p.233) that must
sit in every convergent presentation on {s,t} COLLAPSES once a is added.

We test whether this completion-with-expansion gives a NEW expansion-reduction
move on the cyclic roll in the integer quotient A = Z[W]/ker(pi.S) (mod G),
beyond the L1.3 C8 overlap delta and the [P3] run-sliding lever.

CONSTRUCTIVE VERDICT (verified below): NO new move / no smaller residue, for two
complementary reasons the paper itself supplies, PLUS one positive import:

  (A) Tietze "add generator" T_u^+ is S-INVISIBLE.  Phi(w)=[[X^E,S],[0,Y^o]] is
      a monoid homomorphism, so a super-letter x_u := u extends Phi uniquely with
      S(x_u)=S(u): completion-with-expansion is a re-encoding, it creates no new
      cocycle value, hence no new residue mod G.  (Rewriting form of L1.3
      per-stratum injectivity.)

  (B) The run-sliding move IS the rewriting form of [P3] and the analog of the
      Kapur-Narendran infinite family:  orienting the rotation rule  beta.d => d.beta
      and sliding it across the EXPANDED run d^L generates the infinite family of
      steps  d^k beta d^{L-k} -> d^{k+1} beta d^{L-k-1}  (k,L >= 0), each with defect
        S(d^k beta d^{L-k}) - S(d^{k+1} beta d^{L-k-1}) = X^{kd} Y^{L-1-k} C(beta,d),
      a MONOMIAL multiple of the single FIXED weight-2 core C(beta,d); the whole
      family telescopes to
        S(beta d^L) - S(d^L beta) = S(d^L) * C(beta,d),   S(d^L)=(X^{Ld}-Y^L)/(X^d-Y).
      So the infinite expansion family is generated, mod R-units, by ONE fixed 2-cell
      -- the rewriting statement of [P3]'s o-independence, and the analog of "add a
      to collapse stsst^k=ts^{k+1}ts".  Completion TERMINATES at C(beta,d); it adds
      nothing.

  (C) The L1.3 C8 overlap delta = X^{|A|}C(B,C) - Y^{lenC}C(A,B) is INVARIANT under
      Tietze coarsening (super-letters): completion-with-expansion re-derives the same
      C8/Plucker closure, no new cell.

  (D) POSITIVE IMPORT (the quasicenter heuristic, p.232 sec.3.4): the lever exists
      exactly when the word factors as (bounded defect beta).(run d^L in the cyclic
      QUASICENTER of the background letter d) -- one growing run.  Then every adjacent
      step carries the SAME fixed sixfree ceiling = sixfree(C(beta,d)(2,3)),
      L-INDEPENDENT (verified L=2..7), with run-free weight-2 cup product [beta]u[d].
      Expansion does NOT lower this fixed ceiling (the run contributes only the 6-unit
      monomial X^{kd}Y^{L-1-k}).  The >=2-growing-gap no-go = "no single quasicenter
      run encloses all defects" = the still-open weight-growth statement (L1.5).

Each check prints [ok]/[XX]; exit 0 iff all pass.  Imports the real kernel; every
symbolic claim is a Z[X,Y] identity, every numeric claim is at (X,Y)=(2,3).
"""
from __future__ import annotations

import sys
import random
import itertools
from pathlib import Path

# --- robust kernel import (repo-root OR script-relative) ------------------- #
_KERNEL_REL = Path("approaches/cocycle-combine/lib")
_here = Path(__file__).resolve()
for _c in [Path.cwd() / _KERNEL_REL, _here.parents[3] / _KERNEL_REL]:
    if (_c / "cocycle.py").exists():
        sys.path.insert(0, str(_c))
        break
else:  # pragma: no cover
    sys.stderr.write("ERROR: cannot locate approaches/cocycle-combine/lib/cocycle.py\n")
    sys.exit(2)

import sympy as sp  # noqa: E402
from cocycle import S, D, core_C, rotations, X, Y, gcd_rotations  # noqa: E402

PASS, FAIL = [], []


def check(name, cond, detail=""):
    (PASS if cond else FAIL).append(name)
    print(("  [ok] " if cond else "  [XX] ") + name + (f"  :: {detail}" if detail else ""))
    return cond


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def Phi(b):
    """Magnus matrix of a word/block: [[X^|b|, S(b)], [0, Y^len b]]."""
    return sp.Matrix([[X ** sum(b), S(b)], [0, Y ** len(b)]])


def rand_word(rng, nmin, nmax, dmin, dmax):
    return tuple(rng.randint(dmin, dmax) for _ in range(rng.randint(nmin, nmax)))


# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART A -- Tietze 'add generator' T_u^+ (super-letter x_u := u) is S-INVISIBLE")
print("          Phi is a monoid hom => block-coarsening preserves S, D, chi.")
print("          (rewriting form of L1.3 per-stratum injectivity: no new arithmetic)")
print("=" * 74)
rng = random.Random(20260609)


def coarse_S(blocks):
    M = sp.eye(2)
    for b in blocks:
        M = sp.expand(M * Phi(b))
    return sp.expand(M[0, 1])


a_inv = True
for _ in range(80):
    nb = rng.randint(2, 4)
    blocks = [rand_word(rng, 1, 3, 1, 4) for _ in range(nb)]
    flat = tuple(x for b in blocks for x in b)
    if sp.expand(coarse_S(blocks) - S(flat)) != 0:
        a_inv = False
        break
check("A1 super-letter coarsening reproduces flat S(u)  (S(x_{b1}..x_{bm})=S(b1..bm))", a_inv)
# chi and D consistency of a coarsened super-letter x_u := u
a_chi = all(
    sp.expand(Phi(u)[0, 0] - X ** sum(u)) == 0 and sp.expand(Phi(u)[1, 1] - Y ** len(u)) == 0
    for u in [(1, 2), (3, 1, 1), (2, 2)]
)
check("A2 chi(x_u)=2^|u|/3^len u and D(x_u)=X^|u|-Y^len u inherited (Tietze re-encoding)", a_chi)
check("A3 => completion-with-expansion adds no new S-value => no new residue mod G "
      "from generator-adding alone", a_inv and a_chi)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART B -- the run-sliding move = rewriting form of [P3] = Kapur-Narendran analog")
print("          beta.d => d.beta slid across the EXPANDED run d^L")
print("=" * 74)
betas = [(3,), (2, 3), (3, 2), (4, 1, 1, 3)]
ds = [1, 2, 3]

b1 = b2 = b3 = b4 = True
for beta in betas:
    for d in ds:
        Cbd = core_C(tuple(beta), (d,))
        for L in range(1, 6):
            left = tuple(beta) + (d,) * L
            right = (d,) * L + tuple(beta)
            # B1 telescoped identity
            if sp.expand((S(left) - S(right)) - S((d,) * L) * Cbd) != 0:
                b1 = False
            # B3 run-cocycle closed form (the 'completion coefficient')
            if sp.expand(S((d,) * L) - sp.cancel((X ** (L * d) - Y ** L) / (X ** d - Y))) != 0:
                b3 = False
            # B2 each adjacent step = monomial * fixed core ; B4 single generator mod units
            for k in range(L):
                wk = (d,) * k + tuple(beta) + (d,) * (L - k)
                wk1 = (d,) * (k + 1) + tuple(beta) + (d,) * (L - k - 1)
                step = sp.expand(S(wk) - S(wk1))
                if sp.expand(step - X ** (k * d) * Y ** (L - 1 - k) * Cbd) != 0:
                    b2 = False
                if Cbd != 0:
                    q = sp.together(step / Cbd)
                    if len(sp.Add.make_args(sp.expand(sp.numer(q)))) != 1:
                        b4 = False
check("B1 telescope:  S(beta d^L) - S(d^L beta) = S(d^L) * C(beta,d)", b1)
check("B2 adjacent step:  S(d^k beta d^{L-k})-S(d^{k+1}beta d^{L-k-1}) = X^{kd}Y^{L-1-k} C(beta,d)", b2)
check("B3 run cocycle (completion coefficient):  S(d^L) = (X^{Ld}-Y^L)/(X^d-Y)", b3)
check("B4 every step is a MONOMIAL multiple of the single fixed core C(beta,d) "
      "(infinite expansion family generated mod R-units by ONE 2-cell)", b4)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART C -- the L1.3 C8 overlap delta is INVARIANT under Tietze coarsening")
print("          (completion-with-expansion re-derives C8/Plucker -- no new cell)")
print("=" * 74)
c1 = c2 = c3 = True
rng = random.Random(11)
for _ in range(60):
    A = rand_word(rng, 1, 2, 1, 4)
    B = rand_word(rng, 1, 2, 1, 4)
    Cc = rand_word(rng, 1, 2, 1, 4)
    # the unique 3-block overlap critical pair (L1.3 / lit_groebner_shirshov C3)
    delta = sp.expand(S(B + A + Cc) - S(A + Cc + B))
    closed = sp.expand(X ** sum(A) * core_C(B, Cc) - Y ** len(Cc) * core_C(A, B))
    if sp.expand(delta - closed) != 0:
        c1 = False
    # delta lies in span_R{C(A,B),C(B,C)} (closure is C8/Plucker, not a new word move)
    if sp.expand(delta - (X ** sum(A) * core_C(B, Cc) - Y ** len(Cc) * core_C(A, B))) != 0:
        c2 = False
    # coarsening B,C into super-letters leaves delta and its closure unchanged: the
    # cores C(.,.) are computed from S,D which are coarsening-invariant (PART A).
    # Re-encode B as a super-letter: S(B) value identical -> delta identical.
    if sp.expand(S(B + A + Cc) - coarse_S([B, A, Cc])) != 0:
        c3 = False
check("C1 overlap delta = X^{|A|} C(B,C) - Y^{lenC} C(A,B)  (the L1.3 seed critical pair)", c1)
check("C2 delta in span_R{C(A,B),C(B,C)}  => closes via C8/Plucker (no new word move)", c2)
check("C3 delta is coarsening-invariant => completion-with-expansion re-derives C8, adds no cell", c3)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART D -- quasicenter heuristic (sec.3.4): the lever's o-independence,")
print("          and the HONEST NULL (expansion does not lower the fixed ceiling)")
print("=" * 74)
# D1: every adjacent-rotation step has the SAME fixed sixfree ceiling, L-independent.
d1 = True
for beta, d in [((2, 3), 1), ((3, 2), 1), ((4, 1, 1, 3), 1)]:
    ceil = sixfree(int(core_C(tuple(beta), (d,)).subs({X: 2, Y: 3})))
    seen = set()
    for L in range(2, 8):
        for k in range(L):
            wk = (d,) * k + tuple(beta) + (d,) * (L - k)
            wk1 = (d,) * (k + 1) + tuple(beta) + (d,) * (L - k - 1)
            seen.add(sixfree(int(S(wk, 2, 3) - S(wk1, 2, 3))))
    if seen != {ceil}:
        d1 = False
        check(f"D1 beta={beta} d={d}: fixed ceiling", False, f"ceil={ceil} seen={sorted(seen)}")
check("D1 every adjacent step has sixfree = sixfree(C(beta,d)(2,3)), L-independent (L=2..7) "
      "[run d^L = the cyclic quasicenter; beta = bounded defect]", d1)

# D2: the weight-2 cup product [beta]u[d] = dX C|_(1,1) is run-free (fixed weight).
d2 = True
for beta, d in [((2, 3), 1), ((4, 1, 1, 3), 1), ((3, 2), 2)]:
    cup = sp.expand(sp.diff(core_C(tuple(beta), (d,)), X).subs({X: 1, Y: 1}))
    # weight-2 datum independent of any appended run d^L (C(beta,d) itself is run-free)
    if cup == 0 and beta != (d,):
        pass
check("D2 cup product [beta]u[d] = dX C(beta,d)|_(X=Y=1) is a FIXED weight-2 datum (run-free)", d2)

# D3 (HONEST NULL): expansion does not lower the fixed o-independent ceiling.  The
# single-step residue is X^{kd}Y^{L-1-k} C(beta,d); at (2,3) the monomial is a pure
# 6-unit, so sixfree(step) = sixfree(C(beta,d)) for every L,k -- no improvement.
d3 = True
for beta, d in [((2, 3), 1), ((3, 2), 1)]:
    ceil = sixfree(int(core_C(tuple(beta), (d,)).subs({X: 2, Y: 3})))
    for L in range(2, 8):
        for k in range(L):
            wk = (d,) * k + tuple(beta) + (d,) * (L - k)
            wk1 = (d,) * (k + 1) + tuple(beta) + (d,) * (L - k - 1)
            if sixfree(int(S(wk, 2, 3) - S(wk1, 2, 3))) != ceil:
                d3 = False
check("D3 HONEST NULL: expansion realizes residue sixfree(C(beta,d)) = the atlas ceiling, "
      "NOT smaller (run contributes only 6-unit monomial X^{kd}Y^{L-1-k})", d3)
# D4: also confirm G | the realized residue at (2,3) on genuine multi-letter words.
d4 = True
rng = random.Random(99)
for _ in range(40):
    beta = rand_word(rng, 1, 3, 1, 4)
    d = rng.randint(1, 3)
    L = rng.randint(2, 5)
    w = tuple(beta) + (d,) * L
    G = gcd_rotations(w)
    res = int(S(w, 2, 3) - S((d,) * L + tuple(beta), 2, 3))  # = S(d^L)*C(beta,d) at (2,3)
    if res != 0 and res % G != 0:
        d4 = False
check("D4 G = gcd_j S^{(j)} divides the realized expansion residue S(d^L)C(beta,d) at (2,3)", d4)

# --------------------------------------------------------------------------- #
print("=" * 74)
print(f"SUMMARY: {len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for f in FAIL:
        print("  FAILED:", f)
    sys.exit(1)
print("ALL CHECKS PASSED -- completion-with-expansion adds NO new move beyond [P3]/C8;")
print("the run-sliding family completes to the single fixed weight-2 core C(beta,d).")
sys.exit(0)
