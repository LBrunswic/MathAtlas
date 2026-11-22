"""Gen 4 (secondary) -- atlas of bounded-defect ceilings and the cyclotomic-collapse gate.

For the bounded-defect lever [P3], a word over background d whose defects fit one
bounded contiguous arc beta (rest a single growing run) has the o-INDEPENDENT ceiling
        G <= sixfree( S(beta d) - S(d beta) ) =: ceil(beta, d).
A *small* ceiling is the strongest exclusion.  This script maps which arcs hit the
smallest ceilings and ties them to the Bang-Zsygmondy / cyclotomic-collapse gate of
structure.md thread 8.

PART A -- single-letter defect (structure.md P2).  ceil = sixfree(2^|e-d| - 1).  Since
          2^n - 1 = prod_{k|n} Phi_k(2) and Phi_k(2) is 6-smooth only for k in {1,2,6}
          (values 1,3,3), every divisor k of n with k not in {1,2,6} drops a NEW
          primitive prime (Bang-Zsygmondy) into the ceiling.  So the ceiling COLLAPSES
          to 1 -- the STRONGEST exclusion (G<=1: only the trivial circuit) -- exactly
          when n=|e-d| in {1,2} (the only n whose divisor set sits in {1,2,6}).

PART B -- genuine 2-defect bounded arcs beta = e1 d^g e2 (g fixed).  Tabulate ceilings,
          find the smallest.  The local core S(beta d)-S(d beta) always carries a FIXED
          (bounded-degree) non-cyclotomic factor, so the ceiling is a fixed constant >1
          (smallest found: 5 for beta=(2,3),d=1) -- a valid o-independent exclusion, but
          weaker than the single-defect collapse.  The ceiling is run-length independent
          (verified across runs), confirming it is a genuine lever.

PART C -- the gate, made explicit.  Single-defect cores are products of cyclotomics
          (Mahler 1); their ceiling = sixfree of prod Phi_k(2) over k|n, k not in {1,2,6}.
          2-defect cores carry an irreducible non-cyclotomic factor (Mahler>1) -> ceiling
          never collapses to 1.  Verified on examples.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/ceiling_atlas.py
"""
import sys, itertools
import numpy as np
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations
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


def ceiling(beta, d):
    return sixfree(Sint(tuple(beta) + (d,)) - Sint((d,) + tuple(beta)))


def mahler1(expr, var):
    expr = sp.expand(expr)
    if expr == 0:
        return 0.0
    p = sp.Poly(expr, var)
    if p.degree() < 1:
        return 1.0
    c = [complex(z) for z in p.all_coeffs()]
    r = np.roots(c)
    m = abs(c[0])
    for z in r:
        if abs(z) > 1:
            m *= abs(z)
    return m


ALL_OK = True

# --------------------------------------------------------------------------- #
# PART A -- single-letter defect: ceiling = sixfree(2^|e-d|-1); gate = {1,2}    #
# --------------------------------------------------------------------------- #
print("== PART A: single-defect ceiling = sixfree(2^|e-d|-1); collapses to 1 iff |e-d| in {1,2} ==")
gate_ok = True
for d in (1, 2, 3):
    row = []
    for e in range(1, 9):
        if e == d:
            continue
        n = abs(e - d)
        c = ceiling((e,), d)
        # cross-check against sixfree(prod_{k|n} Phi_k(2))
        prod = 1
        for k in sp.divisors(n):
            prod *= int(sp.cyclotomic_poly(k, 2))
        if sixfree(prod) != c:
            gate_ok = False
        # the gate: collapse to 1 iff every divisor of n is in {1,2,6}
        collapsed = all(k in (1, 2, 6) for k in sp.divisors(n))
        if (c == 1) != collapsed:
            gate_ok = False
        row.append((n, c))
    print(f"  d={d}: (|e-d|, ceiling) = {row}")
print(f"  ceiling == sixfree(prod_k|n Phi_k(2)) and (ceiling==1 <=> divisors(n) subset {{1,2,6}}): {gate_ok}")
print(f"  => STRONGEST exclusion: |e-d| in {{1,2}} gives G<=1 (only the trivial circuit survives).")
partA = gate_ok
print(f"  PART A holds: {partA}\n")
ALL_OK &= partA

# --------------------------------------------------------------------------- #
# PART B -- genuine 2-defect bounded arcs: smallest ceilings, run-independent   #
# --------------------------------------------------------------------------- #
print("== PART B: genuine 2-defect arcs e1 d^g e2 (g fixed) -- smallest ceilings, o-independent ==")
d = 1
res = []
for e1 in range(2, 7):
    for e2 in range(2, 7):
        for g in (0, 1, 2):
            beta = (e1,) + (d,) * g + (e2,)
            res.append((ceiling(beta, d), beta))
res.sort()
print("  smallest 2-defect ceilings (d=1):")
for c, beta in res[:8]:
    print(f"     ceiling={c:>3}  beta={beta}")
smallest = res[0]
print(f"  smallest genuine 2-defect ceiling: {smallest[0]} at beta={smallest[1]} (>1: no full collapse)")

# the ceiling is o-INDEPENDENT: slide beta through a growing run, G stays <= ceiling.
run_indep = True
for c, beta in res[:6]:
    ceil = c
    for L in range(2, 9):
        W = tuple(beta) + (d,) * L
        G = gcd_rotations(W)
        if ceil % G != 0 or G > ceil:
            run_indep = False
print(f"  ceiling is run-length independent (G | ceil and G <= ceil over runs 2..8): {run_indep}")
partB = (smallest[0] > 1) and run_indep
print(f"  PART B holds: {partB}\n")
ALL_OK &= partB

# --------------------------------------------------------------------------- #
# PART C -- the gate made explicit: single-defect cyclotomic vs 2-defect non-cyc #
# --------------------------------------------------------------------------- #
print("== PART C: single-defect core = product of cyclotomics (Mahler 1); 2-defect = non-cyclotomic ==")
# single-defect cores X^d(X^{e-d}-1): Mahler 1.
sd_cyc = True
for e in (2, 3, 4, 5, 7):
    core = sp.expand(Spoly((e, d)) - Spoly((d, e)))
    if mahler1(sp.expand(core.subs(Y, 1)), X) > 1.0001:
        sd_cyc = False
print(f"  single-defect cores are Mahler-1 (cyclotomic*monomial): {sd_cyc}")
# 2-defect cores carry an irreducible non-cyclotomic factor (Mahler>1).
td_noncyc = True
examples = [(2, 3), (3, 2), (2, 4), (3, 5)]
for beta in examples:
    core = sp.expand(Spoly(tuple(beta) + (d,)) - Spoly((d,) + tuple(beta)))
    M = mahler1(sp.expand(core.subs(Y, 1)), X)
    if M <= 1.0001:
        td_noncyc = False
    print(f"  beta={beta}: ceiling={ceiling(beta,d)}, Mahler(core|Y=1)={M:.3f}, core={sp.factor(core)}")
print(f"  2-defect cores all carry a non-cyclotomic factor (Mahler>1) -> ceiling never 1: {td_noncyc}")
partC = sd_cyc and td_noncyc
print(f"  PART C holds: {partC}\n")
ALL_OK &= partC

print("=" * 70)
print(f"CEILING ATLAS (Gen 4 secondary): {'ALL PASS' if ALL_OK else 'FAILED'}")
print("Takeaway: strongest exclusions are single-defect |e-d| in {1,2} (ceiling 1, full);")
print("          genuine 2-defect arcs give fixed o-independent ceilings >=5 (still valid).")
sys.exit(0 if ALL_OK else 1)
