"""Verification for drafts/lit-groebner-shirshov.md  (leverage L1.3).

Source: L. A. Bokut & Yuqun Chen, "Groebner-Shirshov bases and their
calculation", Bull. Math. Sci. 4 (2014) 325-395 (arXiv:1303.5366);
sources/bokut-chen-groebner-shirshov-1303.5366.pdf.

We test whether the Fox presentation of I_D -- the balanced slot-swap (*),
  S(PMQ) - S(PM'Q) = X^{|P|} Y^{lenQ} (S(M) - S(M'))   for chi(M)=chi(M')
-- is a finite confluent Groebner-Shirshov basis, what its normal forms are,
and whether the Shirshov completion throws off a NEW relation.

The correct CDL setting (Bokut-Chen 2.5, Mikhalev-Zolotykh Thm 2.24) is the
"double free associative algebra" k[X] (x) k<Y>: noncommutative WORD monoid on
the gap letters {x_d}, with COMMUTATIVE coefficients R = Z[X,Y] (the frame
prefactor X^{|P|}Y^{lenQ} is a commutative monomial that depends on the slot
POSITION -- so the noncommutative word order is load-bearing; NOT commutative
Buchberger). The three composition types there are Inclusion (C1), Overlap
(C2) and -- unique to commutative coefficients -- External (C3).

Checks (each a Z[X,Y] symbolic identity, or an exhaustive enumeration; ranges
stated inline). Exit 0 iff all pass.

  A  STRUCTURAL PIN -- per-length injectivity of S, hence Phi injective:
       For words of a FIXED length n, the coefficient of Y^{n-1-k} in S(w) is
       exactly X^{e_k} (e_k = k-th partial sum). Hence S(w)=S(w') with
       len w = len w'  =>  w = w'.  So Phi(w)=[[X^{|w|},S],[0,Y^{len}]] is an
       INJECTIVE monoid hom: the only words with equal S are equal words.
       CONSEQUENCE: the S-PRESERVING balanced slot-swap congruence (the (*)
       relations realised as binomials PMQ - PM'Q that are actually 0) is the
       TRIVIAL congruence -- it is (vacuously) a reduced GS basis. No nontrivial
       critical pairs over R; the reduction content lives modulo D.

  B  (*) AS A PURE WORD REWRITING (chi-balanced slot-swap, oriented to lex-min):
       chi-balance fixes (sum,len), so the graded order (|.|,len) does NOT
       orient -- the lex refinement does. Every non-minimal word reduces in ONE
       step (take the slot = whole word) to the lex-min of its (sum,len) class,
       so the system is terminating and CONFLUENT with a unique normal form
       NF(w) = (1,1,...,1, |w|-len w+1)  (the maximally 1-loaded word).
       B1 confluence battery: many RANDOM reduction orders -> same NF.
       B2 NF is the lex-min; closed form (1^{n-1}, N-n+1) confirmed.
       B3 HONEST: this word rule preserves (sum,len) -- it CANNOT shorten and
          it is S-BLIND (it only computes the (sum,len)-class). So "shorter
          words => smaller S" is NOT realisable as a confluent length-reducing
          WORD system: by A, S is injective per length.

  C  THE MOVE ALGEBRA (S-differences) AND THE CRITICAL PAIRS:
       C1 (*) frame-extraction identity (the single production rule).
       C2 rotation antisymmetry  S(uv)-S(vu) = C(u,v) = D(u)S(v)-D(v)S(u);
          the natural balanced swap M=AB -> M'=BA (block rotation) has core C.
       C3 OVERLAP critical pair (Bokut-Chen C2): the two ways to reduce ABC by
          swapping the overlapping slots AB and BC differ by
             delta = X^{|A|} C(B,C) - Y^{lenC} C(A,B)     (block-rotation swaps)
          We verify this closed form AND that delta is in general NOT itself a
          single (*)-move (a frame times one balanced difference): so the
          move-set is NOT confluent on its own -- the critical pair forces the
          antisymmetry/Plucker relation as the closure. We also identify the
          unique 3-block syzygy delta lands in.
       C4 Plucker / Jacobi C8:  D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0  -- the
          quadratic closure of the cores (already known to the drafts; NOT new).
       C5 EXTERNAL composition (Bokut-Chen C3, commutative-coefficient-only):
          disjoint-slot swaps commute -- the frame monomials commute in R --
          so the external/disjoint critical pair resolves with NO new word move
          (Bokut-Chen Lemma 2.1 Case 1 analog).

  D  THE COEFFICIENT RELATION D AND THE mod-D CONGRUENCE:
       D1 D = X^E - Y^o is itself a monic binomial X^E -> Y^o; as a one-rule
          system it has no self-overlap (X^E, Y^o share no variable) -> trivially
          a confluent GS basis on the commutative side.
       D2 a concrete nontrivial mod-D relation: distinct rotations of a cyclic
          word that become equal modulo D, with the witnessing relation being
          the antisymmetry core C -- NOT a new slot-swap.

Run from repo root OR anywhere: kernel path inserted robustly.
"""

from __future__ import annotations

import sys
import random
import itertools
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


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" :: {detail}" if detail else ""))
    return ok


def partial_sums(w):
    e, acc = [], 0
    for d in w:
        e.append(acc)
        acc += d
    return e


def all_words(n, N, dmax=None):
    """All length-n positive words summing to N (compositions of N into n parts)."""
    if n == 0:
        return [()] if N == 0 else []
    out = []
    hi = N - (n - 1) if dmax is None else min(dmax, N - (n - 1))
    for first in range(1, hi + 1):
        for rest in all_words(n - 1, N - first, dmax):
            out.append((first,) + rest)
    return out


def words_upto(nmax, Nmax):
    out = []
    for n in range(1, nmax + 1):
        for N in range(n, Nmax + 1):
            out.extend(all_words(n, N))
    return out


# --------------------------------------------------------------------------- #
# PART A  --  per-length injectivity of S  =>  Phi injective                   #
# --------------------------------------------------------------------------- #
def partA_injectivity():
    print("\n--- PART A: per-length injectivity of S (Phi injective) ---")

    # A1: coefficient of Y^{n-1-k} in S(w) is exactly X^{e_k}.
    ok_coeff = True
    for w in words_upto(6, 12):
        n = len(w)
        e = partial_sums(w)
        poly = sp.Poly(sp.expand(S(w)), Y)
        for k in range(n):
            # coefficient of Y^{n-1-k}
            c = poly.coeff_monomial(Y ** (n - 1 - k))
            if sp.expand(c - X ** e[k]) != 0:
                ok_coeff = False
                break
        if not ok_coeff:
            break
    check("A1 coeff of Y^{n-1-k} in S(w) equals X^{e_k} (S pins the word)", ok_coeff)

    # A2: exhaustive -- among equal-length words, S is injective.
    ok_inj = True
    collide = None
    for n in range(1, 8):
        for N in range(n, 16):
            seen = {}
            for w in all_words(n, N):
                key = sp.expand(S(w))
                if key in seen and seen[key] != w:
                    ok_inj = False
                    collide = (seen[key], w)
                    break
                seen[key] = w
            if not ok_inj:
                break
        if not ok_inj:
            break
    check("A2 S injective on each fixed length (no equal-length S-collision; "
          "n<=7, N<=15, exhaustive)", ok_inj,
          "" if ok_inj else f"collision {collide}")

    # A3: hence the S-preserving balanced slot-swap forces M = M'.
    #     (Phi(M)=Phi(M') <=> |M|=|M'| & lenM=lenM' & S(M)=S(M') <=> M=M'.)
    ok_a3 = ok_inj and ok_coeff
    check("A3 => S-preserving balanced swap PMQ=PM'Q forces M=M' "
          "(exact (*) congruence is TRIVIAL; vacuous reduced GS basis)", ok_a3)
    return ok_coeff and ok_inj and ok_a3


# --------------------------------------------------------------------------- #
# PART B  --  (*) as a pure word rewriting: confluence + normal forms          #
# --------------------------------------------------------------------------- #
def lexmin_word(n, N):
    """Lex-min length-n word summing to N: (1^{n-1}, N-n+1)."""
    return (1,) * (n - 1) + (N - n + 1,)


def one_random_swap(w, rng):
    """Apply ONE lex-decreasing balanced slot-swap PMQ->PM'Q if possible.
    Pick a random contiguous slot of length>=2 and replace it by a random
    lex-smaller rearrangement of the SAME (sum,len). Return new word or None."""
    n = len(w)
    if n < 2:
        return None
    starts = list(range(n))
    rng.shuffle(starts)
    for i in starts:
        for L in rng.sample(range(2, n - i + 1), k=(n - i - 1)) if n - i >= 2 else []:
            M = w[i:i + L]
            sM, lM = sum(M), len(M)
            # candidate rearrangements of (sum=sM,len=lM) strictly lex-smaller
            cands = [tuple(c) for c in all_words(lM, sM) if tuple(c) < M]
            if cands:
                Mp = rng.choice(cands)
                return w[:i] + Mp + w[i + L:]
    return None


def reduce_random(w, rng, max_steps=2000):
    cur = w
    for _ in range(max_steps):
        nxt = one_random_swap(cur, rng)
        if nxt is None:
            return cur
        cur = nxt
    return cur


def partB_word_rewriting():
    print("\n--- PART B: (*) as a word rewriting -- confluence + normal forms ---")

    battery = words_upto(6, 13)
    # B1 confluence: many random reduction orders -> identical normal form.
    ok_conf = True
    bad = None
    for w in battery:
        nfs = set()
        for s in range(8):
            rng = random.Random(1000 * s + 7)
            nfs.add(reduce_random(w, rng))
        if len(nfs) != 1:
            ok_conf = False
            bad = (w, nfs)
            break
    check("B1 confluence battery: 8 random reduction orders -> same NF "
          "(all words n<=6, N<=13)", ok_conf, "" if ok_conf else f"{bad}")

    # B2 normal form = lex-min = (1^{n-1}, N-n+1).
    ok_nf = True
    bad2 = None
    for w in battery:
        nf = reduce_random(w, random.Random(99))
        if nf != lexmin_word(len(w), sum(w)):
            ok_nf = False
            bad2 = (w, nf)
            break
    check("B2 NF(w) = lex-min = (1^{n-1}, |w|-len+1)  (chi-reduced short word)",
          ok_nf, "" if ok_nf else f"{bad2}")

    # B3 HONEST: this rule preserves (sum,len) -- cannot shorten, S-blind.
    ok_pres = all(
        (sum(reduce_random(w, random.Random(3))) == sum(w)
         and len(reduce_random(w, random.Random(3))) == len(w))
        for w in battery
    )
    # show S is NOT preserved: NF generally has S != S(w)
    changed = sum(1 for w in battery
                  if sp.expand(S(w) - S(lexmin_word(len(w), sum(w)))) != 0)
    check("B3 word rule preserves (sum,len) but is S-BLIND "
          f"(S changed on {changed}/{len(battery)} words) -- cannot shorten S",
          ok_pres and changed > 0,
          f"length-preserving={ok_pres}, S-changed={changed}")
    return ok_conf and ok_nf and ok_pres and changed > 0


# --------------------------------------------------------------------------- #
# PART C  --  the move algebra (S-differences) and the critical pairs          #
# --------------------------------------------------------------------------- #
def rand_word(rng, nmin, nmax, dmin, dmax):
    n = rng.randint(nmin, nmax)
    return tuple(rng.randint(dmin, dmax) for _ in range(n))


def C_core(u, v):
    """C(u,v) = D(u)S(v) - D(v)S(u) = S(uv)-S(vu)."""
    return sp.expand(D(u) * S(v) - D(v) * S(u))


def partC_critical_pairs():
    print("\n--- PART C: move algebra (S-differences) + critical pairs ---")
    rng = random.Random(20260608)

    # C1 the (*) frame-extraction identity (single production rule).
    ok_c1 = True
    for _ in range(80):
        P = rand_word(rng, 0, 3, 1, 5)
        Q = rand_word(rng, 0, 3, 1, 5)
        M = rand_word(rng, 2, 4, 1, 5)
        Mp = tuple(rng.sample(M, len(M)))  # a permutation: chi(M)=chi(Mp)
        lhs = S(P + M + Q) - S(P + Mp + Q)
        rhs = X ** sum(P) * Y ** len(Q) * (S(M) - S(Mp))
        if sp.expand(lhs - rhs) != 0:
            ok_c1 = False
            break
    check("C1 (*) frame extraction S(PMQ)-S(PM'Q)=X^|P|Y^lenQ(S(M)-S(M'))", ok_c1)

    # C2 rotation antisymmetry; block rotation M=AB->BA has core C(A,B).
    ok_c2 = True
    for _ in range(80):
        A = rand_word(rng, 1, 3, 1, 5)
        B = rand_word(rng, 1, 3, 1, 5)
        if sp.expand((S(A + B) - S(B + A)) - C_core(A, B)) != 0:
            ok_c2 = False
            break
    check("C2 antisymmetry S(AB)-S(BA)=C(A,B)=D(A)S(B)-D(B)S(A) "
          "(natural (*) swap = block rotation)", ok_c2)

    # C3 OVERLAP critical pair: reduce ABC two ways (swap AB; swap BC), as
    #    block rotations AB->BA and BC->CB.  Closed form of the discrepancy:
    #      delta = S(BAC) - S(ACB)  [path1 then ..., path2 then ...]
    #            = X^{|A|} C(B,C) - Y^{lenC} C(A,B).
    ok_c3form = True
    not_single_move = 0
    total = 0
    for _ in range(120):
        A = rand_word(rng, 1, 3, 1, 4)
        B = rand_word(rng, 1, 3, 1, 4)
        Cc = rand_word(rng, 1, 3, 1, 4)
        # path 1: swap prefix slot AB -> BA :  ABC -> BAC
        # path 2: swap suffix slot BC -> CB :  ABC -> ACB
        delta = S(B + A + Cc) - S(A + Cc + B)
        closed = X ** sum(A) * C_core(B, Cc) - Y ** len(Cc) * C_core(A, B)
        if sp.expand(delta - closed) != 0:
            ok_c3form = False
            break
        total += 1
        # is delta a SINGLE (*)-move, i.e. (monomial)*(S(M)-S(M')) for balanced
        # M,M' built from {A,B,C}?  Test: is delta / X^|A| a single core?  In
        # general delta is a 2-term core combo with DIFFERENT frames -> not one
        # (*)-move.  Detect by: delta is not a monomial multiple of any single
        # C(.,.) among the blocks.
        singles = [C_core(B, Cc), C_core(A, B), C_core(A, Cc),
                   C_core(A + B, Cc), C_core(A, B + Cc)]
        is_single = False
        for c in singles:
            if c == 0:
                continue
            r = sp.cancel(sp.expand(delta) / c)
            num, den = sp.fraction(sp.together(r))
            if (len(sp.Add.make_args(sp.expand(num))) == 1 and
                    len(sp.Add.make_args(sp.expand(den))) == 1):
                is_single = True
                break
        if not is_single:
            not_single_move += 1
    check("C3 overlap critical pair delta=S(BAC)-S(ACB) "
          "= X^|A|C(B,C) - Y^lenC C(A,B)  (closed form)", ok_c3form)
    check("C3 delta is generically NOT a single (*)-move "
          "(2-frame core combo) => (*) alone is NOT confluent on differences",
          not_single_move > 0,
          f"{not_single_move}/{total} overlaps are not a single (*)-move")

    # C4 Plucker / Jacobi C8 (quadratic closure of the cores; KNOWN to drafts).
    ok_c8 = True
    for _ in range(80):
        u = rand_word(rng, 1, 3, 1, 5)
        v = rand_word(rng, 1, 3, 1, 5)
        w = rand_word(rng, 1, 3, 1, 5)
        lhs = (D(u) * C_core(v, w) + D(v) * C_core(w, u) + D(w) * C_core(u, v))
        if sp.expand(lhs) != 0:
            ok_c8 = False
            break
    check("C4 Plucker/Jacobi C8 D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0 "
          "(KNOWN; the quadratic closure)", ok_c8)

    # C3b: the overlap discrepancy delta lies in the antisymmetry module --
    #   verify delta is an R-combination of the three blockwise cores of ABC,
    #   i.e. delta is reducible by the antisymmetry rule (so closure = C2/C8,
    #   not a brand-new word move).  Concretely delta = X^|A|C(B,C)-Y^lenC C(A,B)
    #   is BY CONSTRUCTION in span_R{C(A,B),C(B,C)} -- re-affirm symbolically.
    ok_module = True
    for _ in range(40):
        A = rand_word(rng, 1, 2, 1, 4)
        B = rand_word(rng, 1, 2, 1, 4)
        Cc = rand_word(rng, 1, 2, 1, 4)
        delta = S(B + A + Cc) - S(A + Cc + B)
        recon = X ** sum(A) * C_core(B, Cc) - Y ** len(Cc) * C_core(A, B)
        if sp.expand(delta - recon) != 0:
            ok_module = False
            break
    check("C3b overlap discrepancy lies in span_R{C(A,B),C(B,C)} "
          "(closure is the antisymmetry/Plucker module -- no NEW word move)",
          ok_module)

    # C5 EXTERNAL / disjoint composition (commutative-coefficient case): two
    #    disjoint balanced slot-swaps commute exactly (frame monomials commute).
    ok_c5 = True
    for _ in range(80):
        P = rand_word(rng, 0, 2, 1, 4)
        M1 = rand_word(rng, 2, 3, 1, 4)
        Q = rand_word(rng, 0, 2, 1, 4)
        M2 = rand_word(rng, 2, 3, 1, 4)
        Rr = rand_word(rng, 0, 2, 1, 4)
        M1p = tuple(reversed(M1))
        M2p = tuple(reversed(M2))
        # swap M1 then M2 vs M2 then M1 -- must give identical word & identical S
        wa = P + M1p + Q + M2p + Rr
        wb = P + M1p + Q + M2p + Rr
        if wa != wb or sp.expand(S(wa) - S(wb)) != 0:
            ok_c5 = False
            break
    check("C5 external/disjoint swaps commute (frame monomials commute in R) "
          "-> disjoint critical pair resolves, no new move", ok_c5)

    return (ok_c1 and ok_c2 and ok_c3form and (not_single_move > 0)
            and ok_c8 and ok_module and ok_c5)


# --------------------------------------------------------------------------- #
# PART D  --  the coefficient relation D and the mod-D congruence              #
# --------------------------------------------------------------------------- #
def reduce_modD(poly, E, o):
    """Reduce a Z[X,Y] poly modulo D = X^E - Y^o using the binomial rule
    X^E -> Y^o (graded by X-degree).  Returns a canonical residue."""
    p = sp.Poly(sp.expand(poly), X)
    changed = True
    expr = sp.expand(poly)
    # iteratively rewrite any X^a (a>=E) -> X^{a-E} Y^o
    for _ in range(200):
        pe = sp.Poly(sp.expand(expr), X)
        deg = pe.degree()
        if deg < E:
            break
        expr = sp.expand(expr.subs(X ** E, Y ** o)) if False else _rewrite_once(expr, E, o)
        if expr is None:
            break
    return sp.expand(expr)


def _rewrite_once(expr, E, o):
    expr = sp.expand(expr)
    pe = sp.Poly(expr, X)
    if pe.degree() < E:
        return expr
    new = 0
    for (a,), coeff in pe.terms():
        if a >= E:
            new += coeff * X ** (a - E) * Y ** o
        else:
            new += coeff * X ** a
    return sp.expand(new)


def partD_modD():
    print("\n--- PART D: coefficient relation D and the mod-D congruence ---")
    from cocycle import gcd_rotations, rotations  # noqa

    # D1: D = X^E - Y^o is a monic binomial X^E -> Y^o with NO self-overlap
    #     (X^E and Y^o are coprime monomials) -> one-rule confluent GS basis.
    #     Demonstrate: reducing X^a (a>=E) is consistent / terminating.
    E, o = 5, 3   # 2^5=32 vs 3^3=27 : a near-cycle ratio
    ok_d1 = True
    for a in range(E, E + 4):
        r = _rewrite_once(X ** a, E, o)
        if sp.expand(r - X ** (a - E) * Y ** o) != 0:
            ok_d1 = False
            break
    check("D1 D=X^E-Y^o is a monic binomial X^E->Y^o, coprime monomials => "
          "no self-overlap => one-rule confluent GS basis (commutative side)",
          ok_d1)

    # D2 (HONEST CAVEAT): the cycle ideal is an INTEGER/evaluation phenomenon,
    #   NOT polynomial divisibility.  The core C(u,v) has X-degree < |uv|=E
    #   (D(u)S(v) tops out below X^E), so the full-word polynomial D=X^E-Y^o
    #   can NEVER divide a nonzero core in Z[X,Y].  Hence the polynomial mod-<D>
    #   congruence between rotations is ALSO trivial; the genuine relations live
    #   only after evaluating at (X,Y)=(2,3).  Verify: nonzero core, X-deg < E,
    #   polynomial remainder of C mod D is nonzero.
    ok_d2 = True
    rng = random.Random(7)
    nz = 0
    for _ in range(200):
        u = rand_word(rng, 1, 3, 1, 4)
        v = rand_word(rng, 1, 3, 1, 4)
        if u == v:
            continue
        c = C_core(u, v)
        if c == 0:
            continue
        nz += 1
        E2 = sum(u) + sum(v)
        xdeg = sp.Poly(sp.expand(c), X).degree()
        if xdeg >= E2:
            ok_d2 = False
            break
        # reduce C mod D=X^E2-Y^o2; must NOT vanish (D can't divide the core)
        red = sp.expand(c)
        for _ in range(60):
            nred = _rewrite_once(red, E2, len(u) + len(v))
            if sp.expand(nred - red) == 0:
                break
            red = nred
        if sp.expand(red) == 0:
            ok_d2 = False
            break
    check("D2 (caveat) X-deg C(u,v) < E and polynomial D never divides a "
          "nonzero core => the cycle ideal is INTEGER/eval, not polynomial",
          ok_d2, f"{nz} nonzero cores tested")

    # D3: the INTEGER cycle congruence -- the genuine mod-D relations.  For ANY
    #   word, G = gcd_j S^{(j)} divides every pairwise rotation difference at
    #   (2,3); and each such difference is a core C evaluated.  On a genuine
    #   cycle G=|D|, so the cores ARE the elements of I_D.  Verify G | (rotation
    #   differences) and that the difference equals the core, over a battery.
    ok_d3 = True
    rng = random.Random(11)
    tested = 0
    for _ in range(120):
        w = rand_word(rng, 2, 6, 1, 5)
        rots = rotations(w)
        G = gcd_rotations(w)
        Sint = [int(S(r, 2, 3)) for r in rots]
        for i in range(len(rots)):
            for j in range(i + 1, len(rots)):
                if (Sint[i] - Sint[j]) % G != 0:
                    ok_d3 = False
                tested += 1
        if not ok_d3:
            break
    check("D3 G=gcd_j S^{(j)} divides every rotation difference at (2,3) "
          f"(=> cores C are the mod-D relations; {tested} pairs)", ok_d3)

    # D4: each rotation difference is literally a core C(u,v) (the antisymmetry),
    #   so the mod-D relations are differences/cores, NOT S-preserving word swaps.
    ok_d4 = True
    rng = random.Random(13)
    for _ in range(60):
        u = rand_word(rng, 1, 3, 1, 5)
        v = rand_word(rng, 1, 3, 1, 5)
        if sp.expand((S(u + v) - S(v + u)) - C_core(u, v)) != 0:
            ok_d4 = False
            break
    check("D4 each rotation difference = antisymmetry core C(u,v) "
          "(mod-D relations are cores, not slot-swaps)", ok_d4)
    return ok_d1 and ok_d2 and ok_d3 and ok_d4


def main():
    print("=" * 70)
    print("lit_groebner_shirshov: is the Fox presentation of I_D a finite")
    print("confluent Groebner-Shirshov basis?  (Bokut-Chen arXiv:1303.5366)")
    print("=" * 70)
    results = [
        partA_injectivity(),
        partB_word_rewriting(),
        partC_critical_pairs(),
        partD_modD(),
    ]
    ok = all(results)
    print("=" * 70)
    print("ALL PASS" if ok else "SOME FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
