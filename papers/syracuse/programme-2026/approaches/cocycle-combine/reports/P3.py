#!/usr/bin/env python3
"""P3 -- two-block periodic  tau = (u v)^q.

Pattern (PATTERNS.md, Tier 1):
    period word  A = u v   (two blocks u, v),  tau = A^q.
    "S^0 - S^{|uv|}, then iterate u<->v; a second difference exploiting the
     inner u|v boundary; two telescopings may pin a smaller joint core."

WHAT THIS SCRIPT CERTIFIES
==========================

This is an HONEST NEGATIVE (✗) result for the single-word rotation programme,
with the exact obstruction certified symbolically, plus the q=1 reduction to the
known P0 core and the cross-length (P4-territory) identity that *would* give a
q-free core but does not constrain any genuine cycle.

(0)  Naive reading "P0 with w=uv, w'=empty" is vacuous:
        C(uv, empty) = D(uv) S(empty) - D(empty) S(uv) = 0   (S(empty)=D(empty)=0).

(1)  STRUCTURAL OBSTRUCTION (the heart of the result).
     tau = A^q is a perfect q-th power, hence IMPRIMITIVE for q>=2.  Its distinct
     cyclic rotations are exactly the len(A) inner rotations of the period, each
     raised to the q-th power:   rot(tau, i) = A_i^q,  A_i := rot(A, i).
     Iterating the cocycle (P1 closed form for a periodic block) gives, for EVERY i,

         S(A_i^q) = S(A_i) * geo_q,        geo_q := sum_{k=0}^{q-1} X^{k|A|} Y^{(q-1-k) len A}
                                                 = D(A^q) / D(A).

     The factor geo_q is the SAME for every rotation (it depends only on |A|, len A,
     not on i).  Therefore EVERY Z[X,Y]-linear combination of rotation sums of tau
     factors through geo_q:

         sum_j c_j S^{(j)}(tau) = geo_q * ( sum_i c_i' S(A_i) ).

     geo_q is NOT a pure power of X (it mixes X and Y); its X-degree is (q-1)|A|,
     which GROWS LINEARLY in q.  So no single-word combination of rotations of
     (uv)^q can compensate to a q-free core: the geo_q factor is unavoidable and
     q-dependent.  The smallest q-free core attainable is at q=1 (geo_1 = 1).

(2)  q=1 REDUCTION (no improvement over P0/P2).
     At q=1 the word is the single period uv; the inner-boundary difference is the
     ordinary antisymmetry core
         S(uv) - S(vu) = D(u)S(v) - D(v)S(u) = C(u,v),
     i.e. exactly the P0 core C(w, w') with (w,w')=(u,v).  No smaller joint core.

(3)  CROSS-LENGTH q-free identity (P4 territory, NOT single-word).
     The geo_q factor *can* be telescoped away by a FINITE DIFFERENCE IN q that
     mixes words of different lengths (A^q and A^{q-1}), which are NOT rotations of
     a single tau:
         [S(A^q)-S(B^q)] - Y^{len A} [S(A^{q-1})-S(B^{q-1})] = C(u,v) * X^{(q-1)|A|},
     with B = v u.  This IS a clean q-free core C(u,v) up to a pure X-power -- but it
     is a P4-style cross-length combination, not a Z[X,Y]-combination of rotations of
     one word, so it is outside the P3 single-word remit.

(4)  VACUITY ON CYCLES.  A genuine Syracuse cycle's gap word is PRIMITIVE (aperiodic).
     (uv)^q with q>=2 is imprimitive, hence never a cycle, so even if a q-free core
     C were extracted the ceiling G | C is not a constraint on any cycle.  Indeed the
     numeric battery below shows G does NOT divide C(u,v) for q>=2 -- consistent with
     "these are not cycles" (G = gcd of rotations grows like D(A^q) here).

VERDICT:  ✗  no useful single-word compensation beyond the P0 core; P3 collapses to
          P0/P2 at q=1 and the only q-free extraction is the cross-length P4 identity,
          which moreover is vacuous on cycles (imprimitive words).
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

from cocycle import (  # noqa: E402
    X, Y, S, D, rotate, rotations, gcd_rotations,
    verify_symbolic_identity, verify_divisibility_battery,
)
import sympy as sp  # noqa: E402


# --------------------------------------------------------------------------- #
# Builders                                                                    #
# --------------------------------------------------------------------------- #
def geo_q(A, q):
    """geo_q = sum_{k=0}^{q-1} X^{k|A|} Y^{(q-1-k) len A} = D(A^q)/D(A)."""
    lenA, sumA = len(A), sum(A)
    return sum(X ** (k * sumA) * Y ** ((q - 1 - k) * lenA) for k in range(q))


def C_uv(u, v):
    """The P0/antisymmetry core  C(u,v) = D(u)S(v) - D(v)S(u) = S(uv) - S(vu)."""
    return sp.expand(D(u) * S(v) - D(v) * S(u))


# --------------------------------------------------------------------------- #
# Certification                                                               #
# --------------------------------------------------------------------------- #
def main():
    cases = [
        ((1, 2), (3,)),
        ((2,), (1, 4)),
        ((1, 1, 3), (2,)),
        ((3, 2), (1,)),
        ((1,), (2,)),
        ((2, 1), (1, 3)),
    ]

    # (0) naive P0-with-empty-tail is identically zero.
    naive_zero = sp.expand(D((1, 2, 3)) * S(()) - D(()) * S((1, 2, 3))) == 0

    # (1) every rotation sum of (uv)^q factors as S(A_i) * geo_q  (common factor).
    factor_ok = True
    for (u, v) in cases:
        A = u + v
        for q in range(1, 6):
            tau = A * q
            g = geo_q(A, q)
            for i in range(len(A)):
                Ai = rotate(A, i)
                if rotate(tau, i) != Ai * q:          # rotation = inner-rot powered
                    factor_ok = False
                if not verify_symbolic_identity(S(rotate(tau, i)), S(Ai) * g):
                    factor_ok = False

    # (1b) consequence: every pairwise rotation difference = (S(A_i)-S(A_j)) * geo_q,
    #      so the geo_q factor (X-degree (q-1)|A|, q-dependent) is unavoidable.
    combo_factor_ok = True
    for (u, v) in cases:
        A = u + v
        for q in range(2, 5):
            tau = A * q
            rots = rotations(tau)
            g = geo_q(A, q)
            # arbitrary integer combo (here: S^{(1)} - 2 S^{(2)} + S^{(len u)}) -> still geo_q*...
            j1, j2, j3 = 1 % len(tau), 2 % len(tau), len(u) % len(tau)
            comb = S(rots[j1]) - 2 * S(rots[j2]) + S(rots[j3])
            inner = S(rotate(A, j1)) - 2 * S(rotate(A, j2)) + S(rotate(A, j3 % len(A)))
            if not verify_symbolic_identity(comb, g * inner):
                combo_factor_ok = False

    # (2) q=1 reduction to the P0 core.
    q1_ok = True
    for (u, v) in cases:
        if not verify_symbolic_identity(S(u + v) - S(v + u), C_uv(u, v)):
            q1_ok = False

    # (3) cross-length P4-style q-free identity (documented, NOT single-word).
    crosslen_ok = True
    for (u, v) in cases:
        A, B = u + v, v + u
        for q in range(2, 6):
            comb = (S(A * q) - S(B * q)) - Y ** len(A) * (S(A * (q - 1)) - S(B * (q - 1)))
            tgt = C_uv(u, v) * X ** ((q - 1) * sum(A))
            if not verify_symbolic_identity(comb, tgt):
                crosslen_ok = False

    # (4) numeric battery: the q-free core C(u,v) is NOT a valid ceiling for q>=2
    #     (imprimitive words are not cycles).  We DOCUMENT the failures rather than
    #     claim a bound.  For q=1 it does divide (it IS the P0 core).
    def core_fn_q1(word):
        # only meaningful at q=1; word = uv, split in half by gap-sum is ambiguous,
        # so we just report C for a fixed canonical split recorded alongside.
        return 0  # placeholder; real check done explicitly below

    fail_q_ge2 = []   # (word, G, C) where G does NOT divide C(u,v)  -> expected
    ok_q1 = True
    for (u, v) in cases:
        A = u + v
        c = int(C_uv(u, v).subs({X: 2, Y: 3}))
        for q in range(1, 6):
            tau = A * q
            G = gcd_rotations(tau)
            divides = (c == 0) or (c % G == 0)
            if q == 1:
                if not divides:
                    ok_q1 = False
            else:
                if not divides:
                    fail_q_ge2.append((tau, G, c))

    # ----- report -----
    print("=" * 72)
    print("P3  two-block periodic  tau = (u v)^q     [HONEST NEGATIVE]")
    print("=" * 72)
    print("Naive 'P0 with w=uv, w''=empty' core C(uv,empty) = 0 :",
          "yes (vacuous)" if naive_zero else "NO")
    print("-" * 72)
    print("Structural fact: every rotation sum factors")
    print("    S^{(j)}((uv)^q) = S(A_i) * geo_q,   geo_q = D(A^q)/D(A),")
    print("    A=uv, A_i = inner rotation of the period.  geo_q is COMMON to all j.")
    print("=> every Z[X,Y]-combination = geo_q * (combo of S(A_i)); X-deg geo_q =")
    print("   (q-1)|A| GROWS with q.  No single-word q-free core exists for q>=2.")
    print("-" * 72)
    print("q=1 reduction      :  S(uv)-S(vu) = C(u,v) = D(u)S(v)-D(v)S(u)  (the P0 core)")
    print("smallest q-free core:  C(u,v)  -- same as P0/P2, NO improvement")
    print("cross-length (P4)   :  [S(A^q)-S(B^q)] - Y^{lenA}[S(A^{q-1})-S(B^{q-1})]")
    print("                       = C(u,v) * X^{(q-1)|A|}   (q-free core, but NOT")
    print("                       a single-word rotation combination)")
    print("vacuity on cycles   :  (uv)^q, q>=2 is IMPRIMITIVE => never a Syracuse cycle;")
    print("                       so no cycle ceiling is obtained from this family.")
    print("-" * 72)
    print(f"naive-core-zero          : {'PASS' if naive_zero else 'FAIL'}")
    print(f"rotation factor (geo_q)  : {'PASS' if factor_ok else 'FAIL'}")
    print(f"combo inherits geo_q     : {'PASS' if combo_factor_ok else 'FAIL'}")
    print(f"q=1 -> P0 core identity  : {'PASS' if q1_ok else 'FAIL'}")
    print(f"cross-length q-free id   : {'PASS' if crosslen_ok else 'FAIL'}")
    print(f"q=1 G|C(u,v) (cycle ok)  : {'PASS' if ok_q1 else 'FAIL'}")
    print(f"q>=2 G does NOT div C    : {len(fail_q_ge2)} documented non-divisions "
          f"(EXPECTED -- imprimitive, not cycles)")
    if fail_q_ge2[:3]:
        for w, G, c in fail_q_ge2[:3]:
            print(f"    word={w}  G={G}  C(u,v)={c}  (C % G = {c % G})")
    print("-" * 72)

    all_certs = (naive_zero and factor_ok and combo_factor_ok
                 and q1_ok and crosslen_ok and ok_q1)
    print("VERDICT: ✗  no useful single-word compensation beyond P0 core")
    print("RESULT:", "PASS (obstruction certified)" if all_certs else "FAIL")
    sys.exit(0 if all_certs else 1)


if __name__ == "__main__":
    main()
