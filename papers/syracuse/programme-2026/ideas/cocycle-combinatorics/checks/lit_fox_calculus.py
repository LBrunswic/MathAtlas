"""Verification for drafts/lit-fox-calculus.md  (leverage L1.2).

Source: R. H. Fox, "Free Differential Calculus I: Derivation in the Free Group
Ring", Annals of Math. 57 (1953) 547-560 (scan in sources/), with the complete
rigorous exposition Han, "The Fox Calculus and Differentiation in Group Rings"
(Portland State MTH 501, 2022; sources/han-fox-calculus-exposition.pdf).

We test the rank-1 image of Fox calculus on our kernel.  Fox's free monoid is on
generators x_d, one per gap value d in N_{>0} (an infinite alphabet -- Fox allows
this explicitly, footnote p.550).  For a POSITIVE word w = (d_0,...,d_{n-1}) the
genuine Fox derivative is the closed form (Fox eq. (2.8), all eps_k = +1):

    d w / d x_j  =  sum over positions p with d_p = j of the prefix  w[0:p].

Our cocycle S is the (alpha_X, eps_Y)-TWISTED total Fox derivative under the
rank-1 abelianization

    alpha_X : x_d |-> X^d        (left abelianization, the gap-weight)
    eps_Y   : x_d |-> Y          (right retraction, the position/length weight),

so that Fox's product rule (1.2)/(1.5)  D(uv) = Du.v^o + u.Dv  becomes our
cocycle  S(uv) = Y^{len v} S(u) + X^{|u|} S(v).

Checks (every one a Z[X,Y] symbolic identity unless noted; ranges stated inline):

  F1  per-gap split:  S(w) = sum_d S_d(w),  S_d(w) = sum_{p:d_p=d} X^{e_p} Y^{n-1-p}
      = (alpha_X,eps_Y)-evaluation of the genuine Fox derivative d w/d x_d.
  F2  S|_{Y=1} = sum_d alpha_X( d w/d x_d )   (the clean "S = sum of abelianized
      Fox derivatives" identity; the Y-grading is the only twist).
  F3  FUNDAMENTAL FORMULA (Fox 2.3) in our rep:
          D(w) = sum_d S_d(w) (X^d - Y),
      i.e. w-1 = sum (d w/d x_j)(x_j-1) maps to D(w) = sum_d S_d (X^d - Y),
      realizing the cycle-ideal generator D as a Fox-derivative combination.
      Also its Y=1 slice  X^{|w|}-1 = sum_d alpha_X(dw/dx_d)(X^d-1).
  F4  rank-1 Magnus rep / 1-cocycle (Fox Intro C): Phi(x_d)=[[X^d,1],[0,Y]] is a
      monoid hom with Phi(w)_{12}=S(w), diag (X^{|w|},Y^{len w}); product rule
      (1.5) multi-factor.
  F5  P0 telescoping = power rule (2.4) instance:
          S(w^q w') - S(w^{q-1} w' w) = X^{(q-1)|w|} C(w,w').
  F6  P1 inner-core = product rule + shared-core cancellation (chi-form):
          chi(x')S(xuy)-chi(x)S(x'uy') = [chi(x')S(x)-chi(x)S(x')]
                                          + chi(x)chi(x')chi(u)[S(y)-S(y')].
  F7  P2/P3 shared-frame = THE unified generator (slot-difference of the product
      rule):  S(PMQ)-S(PM'Q) = X^{|P|}Y^{len Q}(S(M)-S(M')) when chi(M)=chi(M');
      plus the general unbalanced identity and that balance kills the extra terms.
  F8  chain rule (2.6) / block-coarsening: Phi(B)=[[X^{|B|},S(B)],[0,Y^{len B}]]
      is a monoid hom on the free monoid of gap-BLOCKS, so every move is
      granularity-independent (a block acts as one super-letter); coarse P0.
  F9  inverse-rule mismatch (one-sided monoid): Fox's (1.6) D(g^{-1})=-g^{-1}Dg
      is unavailable (no letter inverses); its formal substitute -- reversal --
      is NOT the antipode times a 6-unit, i.e. reversal = transpose, not inverse.

Run from the repo root OR from anywhere: the kernel path is inserted robustly.
Exit code 0 iff every check passes.
"""

from __future__ import annotations

import sys
import random
from pathlib import Path

# --- robust kernel import (repo-root OR script-relative) ------------------- #
_KERNEL_REL = Path("approaches/cocycle-combine/lib")
_here = Path(__file__).resolve()
_candidates = [
    Path.cwd() / _KERNEL_REL,            # running from repo root
    _here.parents[3] / _KERNEL_REL,      # checks/ -> idea -> ideas -> repo
]
for _c in _candidates:
    if (_c / "cocycle.py").exists():
        sys.path.insert(0, str(_c))
        break
else:  # pragma: no cover
    sys.stderr.write(
        "ERROR: could not locate approaches/cocycle-combine/lib/cocycle.py.\n"
        "Run from the repo root (Syracuse/) or keep this file under "
        "ideas/cocycle-combinatorics/checks/.\n"
    )
    sys.exit(2)

import sympy as sp  # noqa: E402
from cocycle import S, D, X, Y, core_C  # noqa: E402

Z2 = sp.zeros(2)


# --------------------------------------------------------------------------- #
# helpers                                                                     #
# --------------------------------------------------------------------------- #
def partial_sums(w):
    e, acc = [], 0
    for d in w:
        e.append(acc)
        acc += d
    return e


def S_d_closed(w, dval):
    """Per-gap partial cocycle (closed form): sum_{p:d_p=dval} X^{e_p} Y^{n-1-p}."""
    n = len(w)
    e = partial_sums(w)
    return sum(X ** e[p] * Y ** (n - 1 - p) for p in range(n) if w[p] == dval)


def fox_derivative_prefixes(w, dval):
    """Genuine Fox derivative d w / d x_{dval} for a POSITIVE word (Fox eq. 2.8):
    the list of prefixes w[0:p] over positions p with letter == dval."""
    return [tuple(w[:p]) for p in range(len(w)) if w[p] == dval]


def alphaX(u):
    """Left abelianization alpha_X : x_d |-> X^d, so a word u |-> X^{|u|}."""
    return X ** sum(u)


def twisted_eval(prefix, n):
    """(alpha_X, eps_Y) evaluation of a Fox-derivative prefix term inside a word
    of total length n: a prefix of length p sits with X^{|prefix|} to its left and
    n-1-p letters (each -> Y) to its right."""
    p = len(prefix)
    return X ** sum(prefix) * Y ** (n - 1 - p)


def chi(w):
    """chi(w) = X^{|w|}/Y^{len w}  (the kernel's unit; Su_k is chi-normalized S)."""
    return X ** sum(w) / Y ** len(w)


def Su_k(w):
    """chi-normalized cocycle Su(w) = S_homog(w)/Y^{len-1} (drafts' S)."""
    n = len(w)
    return sp.Integer(0) if n == 0 else sp.together(S(tuple(w)) / Y ** (n - 1))


def Phi(w):
    """Rank-1 Magnus representation (upper-triangular). Off-diagonal is S(w);
    diagonal is (X^{|w|}, Y^{len w}). For a single letter d this is
    [[X^d, 1],[0, Y]] = [[alpha(x_d), d x_d/d x_d],[0, eps(x_d)]]."""
    return sp.Matrix([[X ** sum(w), S(tuple(w))], [0, Y ** len(w)]])


def antipode(expr):
    return expr.subs({X: 1 / X, Y: 1 / Y}, simultaneous=True)


def rand_word(rng, nmin, nmax, dmin, dmax):
    n = rng.randint(nmin, nmax)
    return tuple(rng.randint(dmin, dmax) for _ in range(n))


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" :: {detail}" if detail else ""))
    return ok


# Deterministic random word battery: lengths 1..7, gaps 1..6.
RNG = random.Random(20260608)
WORDS = [rand_word(RNG, 1, 7, 1, 6) for _ in range(120)]
# A few hand words exercising repeats / small alphabets.
WORDS += [(1, 1, 1, 1), (2, 2, 2), (1, 2, 1, 2, 1), (3,), (5, 1, 5, 1), (1, 2, 3, 4, 5)]


# --------------------------------------------------------------------------- #
# F1  per-gap split and the twisted Fox-derivative identity                   #
# --------------------------------------------------------------------------- #
def f1_per_gap_split():
    ok_sum = ok_fox = True
    for w in WORDS:
        ds = set(w)
        n = len(w)
        # closed-form per-gap cocycles sum to S
        if sp.expand(sum(S_d_closed(w, d) for d in ds) - S(w)) != 0:
            ok_sum = False
        # S_d equals the (alpha_X, eps_Y) twisted evaluation of the Fox derivative
        for d in ds:
            twisted = sum(twisted_eval(pre, n) for pre in fox_derivative_prefixes(w, d))
            if sp.expand(twisted - S_d_closed(w, d)) != 0:
                ok_fox = False
    return check("F1 S = sum_d S_d  (per-gap split)", ok_sum) & \
        check("F1 S_d = (alpha_X,eps_Y) eval of Fox derivative d w/d x_d", ok_fox)


# --------------------------------------------------------------------------- #
# F2  S|_{Y=1} = sum_d alpha_X( d w/d x_d )                                    #
# --------------------------------------------------------------------------- #
def f2_abelianized_fox_sum():
    ok = True
    for w in WORDS:
        ds = set(w)
        foxsum = sum(alphaX(pre) for d in ds for pre in fox_derivative_prefixes(w, d))
        if sp.expand(foxsum - S(w).subs(Y, 1)) != 0:
            ok = False
    return check("F2 S|_{Y=1} = sum_d alpha_X(d w/d x_d) (S is the total Fox deriv)", ok)


# --------------------------------------------------------------------------- #
# F3  fundamental formula in our rep:  D(w) = sum_d S_d(w)(X^d - Y)            #
# --------------------------------------------------------------------------- #
def f3_fundamental_formula():
    ok_full = ok_y1 = True
    for w in WORDS:
        ds = set(w)
        ff = sum(S_d_closed(w, d) * (X ** d - Y) for d in ds)
        if sp.expand(ff - D(w)) != 0:
            ok_full = False
        # Y=1 slice: X^{|w|}-1 = sum_d alpha_X(dw/dx_d)(X^d-1)
        ffy = sum(alphaX(pre) * (X ** d - 1)
                  for d in ds for pre in fox_derivative_prefixes(w, d))
        if sp.expand(ffy - (X ** sum(w) - 1)) != 0:
            ok_y1 = False
    return check("F3 fundamental formula  D(w) = sum_d S_d(w)(X^d - Y)", ok_full) & \
        check("F3 Y=1 slice  X^|w|-1 = sum_d alpha_X(dw/dx_d)(X^d-1)", ok_y1)


# --------------------------------------------------------------------------- #
# F4  rank-1 Magnus rep / 1-cocycle + product rule (1.5)                       #
# --------------------------------------------------------------------------- #
def f4_magnus_and_product_rule():
    # Phi is a monoid hom on single letters; off-diagonal/diagonal correct.
    ok_hom = ok_entry = True
    for w in WORDS:
        P = sp.eye(2)
        for d in w:
            P = P * sp.Matrix([[X ** d, 1], [0, Y]])
        if sp.expand(P[0, 1] - S(w)) != 0:
            ok_entry = False
        if sp.expand(P[0, 0] - X ** sum(w)) != 0 or sp.expand(P[1, 1] - Y ** len(w)) != 0:
            ok_entry = False
    # multi-factor product rule (1.5)
    ok_pr = True
    rng = random.Random(11)
    for _ in range(60):
        m = rng.randint(2, 4)
        facs = [rand_word(rng, 1, 3, 1, 5) for _ in range(m)]
        w = tuple(x for A in facs for x in A)
        rhs = 0
        for i, A in enumerate(facs):
            pre = sum(sum(B) for B in facs[:i])
            post = sum(len(B) for B in facs[i + 1:])
            rhs += X ** pre * Y ** post * S(A)
        if sp.expand(S(w) - rhs) != 0:
            ok_pr = False
            break
    return check("F4 Phi(x_d)=[[X^d,1],[0,Y]] hom; Phi(w)_12=S, diag=(X^|w|,Y^len)",
                 ok_entry & ok_hom) & \
        check("F4 product rule (1.5)  S(A1..Am)=sum_i X^|pref| Y^len(suf) S(Ai)", ok_pr)


# --------------------------------------------------------------------------- #
# F5  P0 telescoping = power rule (2.4)                                        #
# --------------------------------------------------------------------------- #
def f5_p0_power_rule():
    ok = True
    rng = random.Random(5)
    cases = []
    for _ in range(40):
        w = rand_word(rng, 1, 3, 1, 5)
        wp = rand_word(rng, 1, 3, 1, 5)
        q = rng.randint(2, 5)
        cases.append((w, wp, q))
    for w, wp, q in cases:
        L = sum(w)
        lhs = S(w * q + wp) - S(w * (q - 1) + wp + w)
        rhs = X ** ((q - 1) * L) * core_C(w, wp)
        if sp.expand(lhs - rhs) != 0:
            ok = False
            break
    return check("F5 P0 telescoping  S(w^q w')-S(w^{q-1}w'w)=X^{(q-1)|w|}C(w,w')", ok)


# --------------------------------------------------------------------------- #
# F6  P1 inner-core = product rule + shared-core cancellation                  #
# --------------------------------------------------------------------------- #
def f6_p1_inner_core():
    ok = True
    rng = random.Random(7)
    for _ in range(60):
        x = rand_word(rng, 1, 2, 1, 4)
        xp = rand_word(rng, 1, 2, 1, 4)
        y = rand_word(rng, 1, 2, 1, 4)
        yp = rand_word(rng, 1, 2, 1, 4)
        u = rand_word(rng, 0, 3, 1, 4)
        lhs = chi(xp) * Su_k(x + u + y) - chi(x) * Su_k(xp + u + yp)
        rhs = (chi(xp) * Su_k(x) - chi(x) * Su_k(xp)) \
            + chi(x) * chi(xp) * chi(u) * (Su_k(y) - Su_k(yp))
        if sp.simplify(lhs - rhs) != 0:
            ok = False
            break
    return check("F6 P1 inner-core  (shared core u cancels; chi-form)", ok)


# --------------------------------------------------------------------------- #
# F7  P2/P3 shared-frame = THE unified generator                              #
# --------------------------------------------------------------------------- #
def f7_shared_frame_generator():
    # general unbalanced slot-difference identity (always holds):
    #   S(PMQ)-S(PM'Q) = X^|P|Y^lenQ (S(M)-S(M'))
    #                    + X^|P|(X^|M|-X^|M'|)S(Q)
    #                    + Y^lenQ (Y^lenM - Y^lenM') S(P)
    ok_gen = ok_bal = True
    rng = random.Random(9)
    for _ in range(60):
        P = rand_word(rng, 0, 3, 1, 5)
        Q = rand_word(rng, 0, 3, 1, 5)
        M = rand_word(rng, 1, 3, 1, 5)
        Mp = rand_word(rng, 1, 3, 1, 5)
        lhs = S(P + M + Q) - S(P + Mp + Q)
        rhs = (X ** sum(P) * Y ** len(Q) * (S(M) - S(Mp))
               + X ** sum(P) * (X ** sum(M) - X ** sum(Mp)) * S(Q)
               + Y ** len(Q) * (Y ** len(M) - Y ** len(Mp)) * S(P))
        if sp.expand(lhs - rhs) != 0:
            ok_gen = False
            break
    # balanced case chi(M)=chi(M')  (|M|=|M'| and lenM=lenM') kills the extra two
    for _ in range(60):
        P = rand_word(rng, 0, 3, 1, 5)
        Q = rand_word(rng, 0, 3, 1, 5)
        M = rand_word(rng, 2, 3, 1, 5)
        Mp = tuple(M[::-1])  # a permutation: same |M|, same len -> chi(M)=chi(M')
        if rng.random() < 0.5 and len(M) >= 2:
            Mp = (M[1], M[0]) + M[2:]
        if sum(M) != sum(Mp) or len(M) != len(Mp):
            continue
        lhs = S(P + M + Q) - S(P + Mp + Q)
        rhs = X ** sum(P) * Y ** len(Q) * (S(M) - S(Mp))
        if sp.expand(lhs - rhs) != 0:
            ok_bal = False
            break
    return check("F7 generator: general slot-difference identity (unbalanced)", ok_gen) & \
        check("F7 P2/P3 balanced  S(PMQ)-S(PM'Q)=X^|P|Y^lenQ(S(M)-S(M'))", ok_bal)


# --------------------------------------------------------------------------- #
# F8  chain rule (2.6) / block-coarsening                                      #
# --------------------------------------------------------------------------- #
def f8_chain_rule_coarsening():
    # Phi is a monoid hom on the free monoid of gap-BLOCKS:
    #   Phi(B0 B1 ... ) = Phi(B0) Phi(B1) ...   with Phi(B)=[[X^|B|,S(B)],[0,Y^lenB]]
    ok_hom = True
    rng = random.Random(13)
    for _ in range(40):
        m = rng.randint(2, 4)
        blocks = [rand_word(rng, 1, 3, 1, 5) for _ in range(m)]
        w = tuple(x for B in blocks for x in B)
        P = sp.eye(2)
        for B in blocks:
            P = P * Phi(B)
        if sp.expand(P[0, 1] - S(w)) != 0:
            ok_hom = False
            break
    # coarse P0: telescoping a repeated multi-letter BLOCK C (P0 with |w|>1).
    ok_coarse = True
    for C, Cp, q in [((1, 2), (3,), 2), ((2, 1), (1, 3), 2),
                     ((1, 1, 2), (4,), 3), ((3, 2), (1,), 4)]:
        lhs = S(C * q + Cp) - S(C * (q - 1) + Cp + C)
        rhs = X ** ((q - 1) * sum(C)) * core_C(C, Cp)
        if sp.expand(lhs - rhs) != 0:
            ok_coarse = False
            break
    return check("F8 chain rule: Phi(B) hom on gap-blocks (granularity-independent)",
                 ok_hom) & \
        check("F8 coarse P0: multi-letter block telescopes (P0 with |w|>1)", ok_coarse)


# --------------------------------------------------------------------------- #
# F9  inverse-rule mismatch: reversal = transpose, not antipode               #
# --------------------------------------------------------------------------- #
def f9_no_inverse_rule():
    # Fox's inverse rule D(g^{-1})=-g^{-1}Dg needs letter inverses we do not have
    # in the gap MONOID.  Its only formal substitute is reversal w^R, but reversal
    # is NOT the antipode (X->1/X, Y->1/Y) times a 6-unit: i.e. the candidate
    # identity  S(w^R) = (+-X^a Y^b) . antipode(S(w))  FAILS in general.  We
    # exhibit a witness where S(w^R)/antipode(S(w)) is not a single Laurent
    # monomial.  (It IS a monomial for palindromes / equal-letter words, which is
    # exactly why reversal = transpose, not inverse -- see L1.1 RE-3.)
    def is_monomial(w):
        wR = tuple(reversed(w))
        ratio = sp.together(S(wR) / antipode(S(w)))
        num, den = sp.fraction(ratio)
        return (len(sp.Add.make_args(sp.expand(num))) == 1 and
                len(sp.Add.make_args(sp.expand(den))) == 1)
    witnesses = [w for w in WORDS if len(w) >= 2 and len(set(w)) >= 2 and not is_monomial(w)]
    # palindrome control: for an equal-letter word the ratio IS a monomial
    pal_monomial = is_monomial((2, 2, 2))
    ok = len(witnesses) > 0 and pal_monomial
    return check("F9 reversal != antipode in general (no inverse rule; one-sided)",
                 ok, f"{len(witnesses)} non-monomial witnesses; equal-letter ctrl monomial={pal_monomial}")


def main():
    print("=== lit_fox_calculus: rank-1 image of Fox free differential calculus ===")
    print("    Fox, Annals 57 (1953) 547-560  (sources/fox-free-diff-calc-I-1953.pdf)")
    print(f"    word battery: {len(WORDS)} words, lengths 1..7, gaps 1..6\n")
    results = [
        f1_per_gap_split(),
        f2_abelianized_fox_sum(),
        f3_fundamental_formula(),
        f4_magnus_and_product_rule(),
        f5_p0_power_rule(),
        f6_p1_inner_core(),
        f7_shared_frame_generator(),
        f8_chain_rule_coarsening(),
        f9_no_inverse_rule(),
    ]
    ok = all(results)
    print("=" * 64)
    print("ALL PASS" if ok else "SOME FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
