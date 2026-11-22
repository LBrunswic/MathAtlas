#!/usr/bin/env python3
r"""L1.9 (circulant / Z[Z/o] arithmetic of the orbit mod G) verification.

Reads Silver-Williams, *Mahler measure, links and homology growth*
(Topology 41 (2002) 873-887, arXiv:math/0003127) -- the COMPANION of the
prompt's primary math/0105234.  Identity confirmed there:

  Thm 2.1 :  (1/|Z^d/Lambda|) log b_Lambda  ->  log M(Delta),     b_Lambda = |TH_1(M_Lambda)|
  Cor 2.2 (Gordon):  Delta_1/Delta_2 | t^N-1  =>  H_1(M_r) periodic in r.

The classical d=1 (knot) face is the Fox formula
  |H_1(M_r)| = prod_{zeta^r=1} |Delta(zeta)| = |Res(t^r - 1, Delta(t))|,
fixed Delta, cover degree r -> infinity, growth M(Delta).

This script translates that onto our rotation orbit and tests, on the kernel,
whether the integer circulant CONSTRUCTS a small orbit residue mod G or only
reproduces Mahler GROWTH (Layer-2 obstruction).

Map:
  * within-orbit DFT     S^hat(zeta) = sum_j S^(j) zeta^j   (circulant of the orbit)
  * period direction     w^r  <->  r-fold cyclic cover M_r
  * cycle Alexander poly Delta(t) = X^E - Y^o t  (DEGREE 1),  M(Delta)=max(2^E,3^o)
  * orbit residue        G = gcd_j S^(j) = |D| = |2^E-3^o| on a cycle

Exit 0 iff every asserted check passes.
"""
from __future__ import annotations

import sys
import os
import math
from math import gcd
from functools import reduce

import sympy as sp

sys.path.insert(
    0,
    os.path.join(os.path.dirname(__file__), "..", "..", "..",
                 "approaches", "cocycle-combine", "lib"),
)
from cocycle import S, D, rotations, X, Y  # noqa: E402

t = sp.symbols("t")
PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("  [ok] " if cond else "  [XX] ") + name)
    return cond


def circ_det(c):
    """det of the circulant with first row (c_0,...,c_{o-1}); M_{ik}=c_{(k-i) mod o}."""
    o = len(c)
    M = sp.Matrix(o, o, lambda i, k: c[(k - i) % o])
    return sp.expand(M.det())


def poly_of(c):
    return sum(c[k] * t**k for k in range(len(c)))


def gall(xs):
    xs = [abs(int(x)) for x in xs if x != 0]
    return reduce(gcd, xs) if xs else 0


# ======================================================================= #
print("=" * 72)
print("PART A -- the ROTATION TRANSFER law: the orbit is a cyclic Z[Z/o]-module")
print("          X^{d_j} S(w_{j+1}) = Y S(w_j) + D(w)   (the affine monodromy)")
print("=" * 72)
# This is the precise 'shift'/monodromy that makes the orbit a circulant module
# and exposes the cycle Alexander structure.  It is the Syracuse step in disguise:
# at (2,3),  2^{d_j} S^(j+1) = 3 S^(j) + (2^E - 3^o).
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3), (3, 1, 1, 2, 2)]:
    rots = rotations(w)
    o = len(w)
    Dw = sp.expand(D(w))
    ok = all(
        sp.expand(X ** rots[j][0] * S(rots[(j + 1) % o]) - Y * S(rots[j]) - Dw) == 0
        for j in range(o)
    )
    check(f"transfer recurrence holds on all rotations   w={w}", ok)
print("  -> the multiplier X^{d_j} is POSITION-DEPENDENT: within one orbit there is")
print("     NO fixed-Delta resultant; the fixed Delta lives in the PERIOD direction.")

# ======================================================================= #
print("=" * 72)
print("PART B -- circulant determinant = resultant = product over o-th roots")
print("          det circ(S^(0..o-1)) = Res(t^o-1, S^hat(t)) = prod_{zeta^o=1} S^hat(zeta)")
print("=" * 72)
for w in [(1, 2), (1, 2, 3), (2, 1, 1, 3)]:
    rots = rotations(w)
    Sv = [sp.expand(S(r)) for r in rots]
    o = len(w)
    cd = circ_det(Sv)
    res = sp.expand(sp.resultant(t**o - 1, poly_of(Sv), t))
    check(f"det circ == Res(t^o-1, S^hat)  (symbolic Z[X,Y])   w={w}",
          sp.expand(cd - res) == 0)
    # numeric: also equals prod over roots of unity at (2,3)
    Si = [int(S(r, 2, 3)) for r in rots]
    cdN = int(circ_det(Si))
    prodN = 1.0
    for j in range(o):
        z = complex(math.cos(2 * math.pi * j / o), math.sin(2 * math.pi * j / o))
        val = sum(Si[k] * z**k for k in range(o))
        prodN *= val
    tol = 1e-6 * (abs(cdN) + 1)        # relative: product of large complex factors
    check(f"det circ == prod_zeta S^hat(zeta)  (numeric (2,3))   w={w}",
          abs(prodN.real - cdN) < tol and abs(prodN.imag) < tol)

# ======================================================================= #
print("=" * 72)
print("PART C -- PRIZE #1 (honest NULL): the circulant AMPLIFIES G, never below it.")
print("          G | every DFT component  =>  G^phi(d) | every cyclotomic block")
print("          => no Fourier block is a SMALL orbit residue; floor is G.")
print("=" * 72)
# Scan for words with g = gcd_j S^(j) > 1 AND not all rotations equal (non-degenerate).
battery = []
for w in [(1, 2), (1, 1), (2, 2), (1, 2, 3), (2, 1, 1, 3), (1, 3, 1, 2),
          (1, 2, 1, 1, 2), (2, 2, 1, 1), (1, 1, 2, 2), (3, 1, 2, 1, 1),
          (3, 1, 1, 2, 4), (4, 3, 4, 3), (4, 3, 1, 1, 2), (2, 4, 2, 4)]:
    rots = rotations(w)
    Si = [int(S(r, 2, 3)) for r in rots]
    g = gall(Si)
    battery.append((w, rots, Si, g))

all_div = all_block = all_floor = True
nontrivial_shown = 0
for (w, rots, Si, g) in battery:
    o = len(w)
    # G divides every rotation sum (definition) -> g^o | det circ
    cd = int(circ_det(Si))
    div_go = (cd == 0) or (cd % (g**o) == 0)
    all_div &= div_go
    # every cyclotomic block Res(Phi_d, S^hat) at (2,3) is divisible by g^phi(d)
    # and (if nonzero) has |.| >= g  -> no block below the floor G.
    block_ok = True
    floor_ok = True
    for d in range(1, o + 1):
        if o % d != 0:
            continue
        Phi = sp.cyclotomic_poly(d, t)
        blk = int(sp.resultant(Phi, poly_of(Si), t))
        gp = g ** sp.totient(d)
        if blk != 0:
            block_ok &= (blk % gp == 0)
            floor_ok &= (abs(blk) >= g)
    all_block &= block_ok
    all_floor &= floor_ok
    distinct = len(set(Si)) > 1
    if g > 1 and distinct and nontrivial_shown < 4:
        # reduced residual circulant on m_j = S^(j)/g (gcd = 1): never a unit shrink
        m = [s // g for s in Si]
        red = int(circ_det(m))
        print(f"  w={str(w):>16}  g=gcd_j S^(j)={g:>4}  S^(j)={Si}  "
              f"det circ={cd}  reduced det circ(m)={red}  (g^o={g**o})")
        nontrivial_shown += 1
check("G | every DFT component  =>  g^o | det circ(S^(0..o-1))", all_div)
check("g^phi(d) | every cyclotomic block Res(Phi_d, S^hat)", all_block)
check("FLOOR: every nonzero cyclotomic block has |.| >= G (no small block)", all_floor)
print("  -> the DFT splits the orbit lattice but G survives in EVERY Fourier")
print("     component (an INTEGER-quotient fact; R3's J-collapse, amplified).")

# ======================================================================= #
print("=" * 72)
print("PART D -- PERIOD direction = the Silver-Williams Fox formula (Thm 2.1).")
print("          Delta(t) = X^E - Y^o t (deg 1);  Res(t^r-1,Delta) = D(w^r);")
print("          cyclotomic blocks = homogenized Phi_d(2^E,3^o) (Zsygmondy).")
print("=" * 72)
for w in [(1, 2), (2, 1, 1, 3), (1, 1, 2)]:
    E = sum(w)
    o = len(w)
    Delta = X**E - Y**o * t
    for r in (1, 2, 3, 4):
        res = sp.expand(sp.resultant(t**r - 1, Delta, t))
        wr = tuple(w) * r
        check(f"Res(t^r-1, X^E-Y^o t) == D(w^r)   w={w} r={r}",
              sp.expand(res - D(wr)) == 0)
    # cyclotomic block factorization over d | r  (the cyclic-cover / Zsygmondy split)
    r = 6
    prod_blocks = sp.Integer(1)
    for d in range(1, r + 1):
        if r % d == 0:
            prod_blocks *= sp.resultant(sp.cyclotomic_poly(d, t), Delta, t)
    check(f"prod_{{d|r}} Res(Phi_d, Delta) == D(w^r)   w={w} r={r}",
          sp.expand(prod_blocks - D(tuple(w) * r)) == 0)
    # each block is the homogenized cyclotomic Phi_d^*(X^E, Y^o)
    for d in (1, 2, 3):
        blk = sp.expand(sp.resultant(sp.cyclotomic_poly(d, t), Delta, t))
        # homogenize Phi_d(s) of degree phi(d):  Y^{o phi(d)} Phi_d(X^E / Y^o)
        s = sp.symbols("s")
        phid = sp.cyclotomic_poly(d, s)
        deg = sp.degree(phid, s)
        hom = sp.expand(Y**(o * deg) * phid.subs(s, X**E / Y**o))
        check(f"block d={d} == homogenized Phi_d(X^E,Y^o)   w={w}",
              sp.expand(blk - hom) == 0)

# ======================================================================= #
print("=" * 72)
print("PART E -- Mahler GROWTH + Gordon criterion (PRIZE #3 = obstruction, NOT")
print("          construction): M(Delta)=max(2^E,3^o)>1 ALWAYS => G(w^r) grows,")
print("          never periodic; small G would need a CYCLOTOMIC Delta we never have.")
print("=" * 72)
for w in [(1, 2), (2, 1, 1, 3), (1, 1, 2), (3, 1, 1, 2, 2)]:
    E = sum(w)
    o = len(w)
    a, b = 2**E, 3**o
    # Delta root = 2^E/3^o is never a root of unity (2,3 mult. independent => 2^E != 3^o)
    check(f"2^E != 3^o (Delta non-cyclotomic, M(Delta)>1)   w={w}", a != b)
    Mdelta = max(a, b)            # Mahler measure of X^E - Y^o t at (2,3)
    # growth of |H_1(M_r)| = |2^{rE}-3^{ro}| is strictly increasing (never bounded/periodic)
    Gs = [abs(a**r - b**r) for r in range(1, 6)]
    check(f"G(w^r)=|2^rE-3^ro| strictly increasing (Gordon: non-periodic)   w={w}",
          all(Gs[i] < Gs[i + 1] for i in range(len(Gs) - 1)))
    # (1/r) log G(w^r) -> log M(Delta) = log max(2^E,3^o).  Convergence speed is
    # set by (min/max)^r, slow when 2^E ~ 3^o (e.g. (1,2): 8 vs 9), so take r large.
    r = 200
    rate = math.log(abs(a**r - b**r)) / r
    check(f"(1/r) log G(w^r) -> log max(2^E,3^o)   w={w} "
          f"(rate={rate:.6f}, target={math.log(Mdelta):.6f})",
          abs(rate - math.log(Mdelta)) < 1e-6)
print("  -> Silver-Williams growth (M(Delta)>1) IS our Layer-2 obstruction:")
print("     the cycle Delta is NEVER cyclotomic, so the orbit residue G never")
print("     bottoms out small.  The circulant CONSTRUCTS no smaller representative.")

# ======================================================================= #
print("=" * 72)
print(f"SUMMARY: {len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for f in FAIL:
        print("  FAILED:", f)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
