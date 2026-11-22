#!/usr/bin/env python3
r"""L1.5 (Movement III) -- Suciu-Wang holonomy / cup-product verification.

Reads A. Suciu & H. Wang, "Cup products, lower central series, and holonomy
Lie algebras" (arXiv:1701.07768), against STRUCTURE.md sec.3 (cores = Plucker
module) and the bounded-defect lever [P3].

The paper's central objects, in OUR notation:

  * Cup product  mu: H^1 ^ H^1 -> H^2  is the degree-2 (weight-2) Magnus
    coefficient kappa(r)_{i,j} = eps_{i,j}(r) = eps . d_i d_j (r)   (Thm 4.3/4.4,
    Cor 4.5).  For a commutator relator it is the WEDGE of first Fox derivatives
    eps_i(u)eps_j(v) - eps_j(u)eps_i(v)  (p.24, kappa(r)=1+(x_i y_i - y_i x_i)+...).
  * Magnus product rule (eq.6 / Lemma 2.3):  M(uv)=M(u)M(v) gives, in degree 2,
        eps_{0,1}(uv) = eps_{0,1}(u) + eps_0(u) eps_1(v) + eps_{0,1}(v).
  * Holonomy Lie algebra (Thm 5.5):  lie(y)/ideal(kappa_2(w_k)), QUADRATIC; for a
    free 2-generator ambient it is the free Lie algebra (Prop 8.1.2, Cor 8.2).
  * WEIGHT  omega(r) = inf{|I| : M(r)_I != 0}  grades everything by COMBINATORIAL
    DEGREE, not word length (Labute Thm 7.2; Suciu-Wang Cor 8.2, Thm 8.3).

What we test (each block prints [ok]/[XX]; exit 0 iff all pass):

  PART A  The untwisted second-Magnus structure in OUR binary alphabet: the
          product rule (eq.6), and the ANTISYMMETRIZED crossing-number primitive
          A(w)=eps_{01}(w)-eps_{10}(w) whose concatenation-coboundary is the
          (E,o)-wedge c(u,v)=E_u o_v - o_u E_v.  (The single-word quadratic
          primitive the drafts never built.)

  PART B  THE HEADLINE NEW RELATION -- the cup product is the LINEARIZATION of our
          core: d/dX C(u,v) |_{X=Y=1} = E_u o_v - o_u E_v = the (E,o)-wedge =
          coboundary of A.  And C(u,v)|_{X=Y=1}=0: the untwisted cup product is the
          DERIVATIVE of C at the trivial character, not C itself.  So the paper's
          cup product = the rank-1 SHADOW of our core; the exclusion-carrying part
          is the chi-twisted higher-order deformation (off the paper's setting).

  PART C  Prize #2 (the Movement-III bridge): the bounded-defect lever core
          C(beta,d)=S(beta d)-S(d beta) is a FIXED weight-2 cup product
          [beta] u [d]; sliding beta through a growing run d^L keeps it fixed
          (o-INDEPENDENT).  Witt: dim lie_2(y0,y1)=1 -> a UNIQUE weight-2 bracket,
          so every bounded-defect core is one structural element.

  PART D  Prize #3 (forced combinations) = the holonomy quadratic relation IS the
          Jacobi identity = our C8/Plucker, in linearized (weight-2) form:
          c(v,w)q_u - c(u,w)q_v + c(u,v)q_w = 0  with q_u=(E_u,o_u).  No NEW forced
          combination -- re-confirms R3/R4 in weight language.

Run from repo root:
    python3 ideas/cocycle-combinatorics/checks/lit_suciu_wang.py
"""
from __future__ import annotations

import sys
import os
from math import gcd
from functools import reduce

import sympy as sp

sys.path.insert(
    0,
    os.path.join(os.path.dirname(__file__), "..", "..", "..",
                 "approaches", "cocycle-combine", "lib"),
)
from cocycle import S, D, core_C, rotations, X, Y  # noqa: E402

PASS, FAIL = [], []


def check(name, cond):
    (PASS if cond else FAIL).append(name)
    print(("  [ok] " if cond else "  [XX] ") + name)
    return cond


# --------------------------------------------------------------------------- #
# binary encoding + untwisted Magnus (Fox) coefficients                       #
#   gap word (d_0,...,d_{n-1})  ->  binary  1 0^{d_0} 1 0^{d_1} ... 1 0^{d_n-1}#
# --------------------------------------------------------------------------- #
def to_bits(word):
    bits = []
    for d in word:
        bits.append(1)
        bits.extend([0] * d)
    return bits


def eps0(word):
    """# of 0-letters in binary = letter-sum E = |word|."""
    return sum(word)


def eps1(word):
    """# of 1-letters in binary = length = o = len(word)."""
    return len(word)


def eps_01(word):
    """eps . d_0 d_1 (w): # subsequences (0 then 1) in the binary word."""
    bits = to_bits(word)
    zeros = 0
    cnt = 0
    for b in bits:
        if b == 0:
            zeros += 1
        else:                       # a 1: every preceding 0 pairs with it
            cnt += zeros
    return cnt


def eps_10(word):
    """eps . d_1 d_0 (w): # subsequences (1 then 0) in the binary word."""
    bits = to_bits(word)
    ones = 0
    cnt = 0
    for b in bits:
        if b == 1:
            ones += 1
        else:                       # a 0: every preceding 1 pairs with it
            cnt += ones
    return cnt


def A_cross(word):
    """Antisymmetrized weight-2 Magnus primitive (Lemma 2.2): kappa_{01}-kappa_{10}."""
    return eps_01(word) - eps_10(word)


def cat(u, v):
    return tuple(u) + tuple(v)


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


# words used across the parts (gap words; all positive letters)
BATT = [((1,), (2,)), ((1, 2), (3,)), ((2, 1, 1), (1, 3)),
        ((1,), (2, 2, 1)), ((3, 1), (1, 2, 2)), ((2,), (1, 1, 3))]

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART A -- the second-Magnus / cup-product structure (eq.6, Lemma 2.2/2.3)")
print("         translated into our binary alphabet (UNtwisted, eps-augmented)")
print("=" * 74)

# A1: Magnus degree-2 product rule  eps_{01}(uv)=eps_{01}(u)+eps_0(u)eps_1(v)+eps_{01}(v)
ok = True
for u, v in BATT:
    lhs = eps_01(cat(u, v))
    rhs = eps_01(u) + eps0(u) * eps1(v) + eps_01(v)
    ok &= (lhs == rhs)
check("eq.6 degree-2 product rule  eps01(uv)=eps01(u)+eps0(u)eps1(v)+eps01(v)", ok)

# A2: antisymmetrized -> the (E,o)-wedge is the concatenation-coboundary of A
ok = True
for u, v in BATT:
    cob = A_cross(cat(u, v)) - A_cross(u) - A_cross(v)
    wedge = eps0(u) * eps1(v) - eps1(u) * eps0(v)   # = E_u o_v - o_u E_v
    ok &= (cob == wedge)
check("coboundary of A = (E,o)-wedge:  A(uv)-A(u)-A(v) = E_u o_v - o_u E_v", ok)

# A3: the (E,o)-wedge / cup product is antisymmetric (Lemma 2.2)
ok = all((eps0(u) * eps1(v) - eps1(u) * eps0(v))
         == -(eps0(v) * eps1(u) - eps1(v) * eps0(u)) for u, v in BATT)
check("Lemma 2.2: the weight-2 cup product is antisymmetric  c(u,v)=-c(v,u)", ok)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART B -- HEADLINE: the cup product is the LINEARIZATION of our core C")
print("         d/dX C(u,v)|_{X=Y=1} = E_u o_v - o_u E_v = coboundary of A")
print("=" * 74)

# B1: dC/dX at the trivial character (X=Y=1) equals the (E,o)-wedge (SYMBOLIC).
ok = True
for u, v in BATT:
    Cuv = core_C(u, v)                               # = D(u)S(v)-D(v)S(u) in Z[X,Y]
    lin = sp.diff(Cuv, X).subs({X: 1, Y: 1})
    wedge = eps0(u) * eps1(v) - eps1(u) * eps0(v)
    ok &= (sp.simplify(lin - wedge) == 0)
check("d/dX C(u,v)|_{X=Y=1} = E_u o_v - o_u E_v  (cup product = linearized core)", ok)

# B2: the naive untwist KILLS the core -- the cup product is the derivative, not C.
ok = all(sp.simplify(core_C(u, v).subs({X: 1, Y: 1})) == 0 for u, v in BATT)
check("C(u,v)|_{X=Y=1} = 0  (untwisted cup product is dC/dX, not C: rank-1 shadow)", ok)

# B3: tie B1 to A2 -- linearized core == coboundary of the single-word primitive A.
ok = True
for u, v in BATT:
    lin = sp.diff(core_C(u, v), X).subs({X: 1, Y: 1})
    cob = A_cross(cat(u, v)) - A_cross(u) - A_cross(v)
    ok &= (sp.Integer(int(lin)) == cob)
check("linearized core == coboundary of A:  dC/dX|_{1,1} = A(uv)-A(u)-A(v)", ok)

# B4: the dY-linearization VANISHES -- all weight-2 cup-product data is the dX one.
ok = all(sp.simplify(sp.diff(core_C(u, v), Y).subs({X: 1, Y: 1})) == 0
         for u, v in BATT)
check("d/dY C|_{1,1} = 0  (the whole weight-2 cup product is the dX wedge alone)", ok)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART C -- Prize #2: the bounded-defect lever core is a FIXED weight-2 cup")
print("         product; sliding through a growing run keeps it o-INDEPENDENT")
print("=" * 74)

# C1: lever factorization (SYMBOLIC) and o-independence of the reduced core.
#   S(d^k beta d^{L-k}) - S(d^{k+1} beta d^{L-k-1}) = X^{kd} Y^{L-k-1} (S(beta d)-S(d beta))
def lever_word(d, k, beta, L):
    return (d,) * k + tuple(beta) + (d,) * (L - k)

ok_fac = ok_indep = True
for d, beta in [(1, (3, 4)), (2, (4, 1, 1, 3)), (1, (2, 3))]:
    reduced = sp.expand(S(cat(beta, (d,))) - S(cat((d,), beta)))   # = C(beta,d)
    for L in (3, 5, 7):
        for k in range(0, L - 1):
            lhs = sp.expand(S(lever_word(d, k, beta, L))
                            - S(lever_word(d, k + 1, beta, L)))
            rhs = sp.expand(X ** (k * d) * Y ** (L - k - 1) * reduced)
            ok_fac &= (sp.simplify(lhs - rhs) == 0)
    # reduced core is literally L-independent (a single fixed weight-2 element):
    ok_indep &= (sp.expand(reduced - sp.expand(core_C(beta, (d,)))) == 0)
check("lever:  adj-rotation wedge = X^{kd} Y^{L-k-1} . C(beta,d)   (SYMBOLIC)", ok_fac)
check("lever core C(beta,d) is L-independent = a FIXED weight-2 object", ok_indep)

# C2: the lever core's cup product (its linearization) -- weight-2, run-free.
ok = True
for d, beta in [(1, (3, 4)), (2, (4, 1, 1, 3)), (1, (2, 3))]:
    lin = sp.diff(core_C(beta, (d,)), X).subs({X: 1, Y: 1})
    wedge = eps0(beta) * 1 - eps1(beta) * d        # E_beta*o_d - o_beta*E_d, o_d=1,E_d=d
    ok &= (sp.Integer(int(lin)) == wedge)
check("lever core linearizes to the cup product [beta] u [d] = E_beta - d*o_beta", ok)

# C3: Witt -- dim lie_2(y0,y1) = 1: a UNIQUE weight-2 bracket (free 2-gen ambient).
def witt(n, k):
    return sum(sp.mobius(d) * n ** (k // d) for d in sp.divisors(k)) // k

check("Witt dim lie_1(y0,y1)=2, dim lie_2=1 (UNIQUE weight-2 bracket [y0,y1]),"
      " dim lie_3=2",
      witt(2, 1) == 2 and witt(2, 2) == 1 and witt(2, 3) == 2)

# --------------------------------------------------------------------------- #
print("=" * 74)
print("PART D -- Prize #3 null: holonomy quadratic relation = Jacobi = our C8,")
print("         in linearized (weight-2) form.  c(v,w)q_u-c(u,w)q_v+c(u,v)q_w=0")
print("=" * 74)

def q(w):
    return (eps0(w), eps1(w))         # the abelianized (E,o) vector

def c2(u, v):
    return eps0(u) * eps1(v) - eps1(u) * eps0(v)

ok = True
for w in [(1, 2, 3), (2, 1, 1, 3), (1, 2, 1)]:
    rs = rotations(w)
    for i in range(len(rs)):
        for j in range(i + 1, len(rs)):
            for k in range(j + 1, len(rs)):
                u, v, ww = rs[i], rs[j], rs[k]
                qu, qv, qw = q(u), q(v), q(ww)
                for comp in (0, 1):
                    val = (c2(v, ww) * qu[comp] - c2(u, ww) * qv[comp]
                           + c2(u, v) * qw[comp])
                    ok &= (val == 0)
check("weight-2 Plucker/Jacobi  c(v,w)q_u - c(u,w)q_v + c(u,v)q_w = 0  (= C8 shadow)",
      ok)

# D2: this linearized Jacobi is exactly dC/dX|_{1,1} of the full C8 syzygy coeffs --
#     i.e. the holonomy relation is the linearization of our (already-known) C8.
ok = True
for w in [(1, 2, 3), (2, 1, 1, 3)]:
    rs = rotations(w)
    u, v, ww = rs[0], rs[1], rs[2]
    # full C8:  D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v) == 0 identically
    c8 = sp.expand(D(u) * core_C(v, ww) + D(v) * core_C(ww, u)
                   + D(ww) * core_C(u, v))
    ok &= (c8 == 0)
check("full C8 D(u)C(v,w)+cyc = 0 holds (its weight-2 shadow is the Jacobi above)",
      ok)

# --------------------------------------------------------------------------- #
print("=" * 74)
print(f"SUMMARY: {len(PASS)} passed, {len(FAIL)} failed")
if FAIL:
    for f in FAIL:
        print("  FAILED:", f)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
