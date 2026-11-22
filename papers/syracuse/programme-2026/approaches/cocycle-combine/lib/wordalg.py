#!/usr/bin/env python3
r"""wordalg.py -- the word algebra Z[W] and a guaranteed-gain simplifier.

This module is split into three clean layers, built on the trusted kernel
`cocycle.py` (imported below):

  Part 1  THE ALGEBRA  Z[W]
  -------------------------
  A word is a tuple of positive gaps; W is the free monoid (concatenation,
  identity = empty word) with two gradings  |w| = gap-sum (the X / 2-degree)
  and  len w = number of gaps (the Y / 3-degree).  Z[W] is the monoid algebra:
  finite linear combinations  sum_i m_i [w_i]  with coefficients m_i in Z[X,Y]
  (the units X^a Y^b are the integers 2^a 3^b).  The structure maps:

      chi(w) = X^{|w|} Y^{-len w}                     character (algebra hom)
      S(w)   = sum_k X^{e_k} Y^{len w-1-k}            cocycle, S(uv)=Y^{len v}S(u)+X^{|u|}S(v)
      M(w)   = [[ Y^{len w}, 0 ],[ S(w), X^{|w|} ]]   transfer rep (monoid hom)
      D(w)   = X^{|w|} - Y^{len w}                    = (diag1 - diag2) of M

  M packages everything: its diagonal is the character (chi = X^{|w|}/Y^{len w}
  is the ratio of the two diagonal entries), its off-diagonal is the cocycle S,
  D(w) = M[1,1]-M[0,0], and chi(w)=1 <=> X^{|w|}=Y^{len w} <=> D(w)=0. The quotient map is

      pi_w : Z[W] -> Z[1/6]/(D(w)) = Z_{2,3}/(1-chi(w)),   c |-> S(c) mod D(w).

  At (X,Y)=(2,3), D = 2^{|w|}-3^{len w} is 6-coprime, so the target is Z/|D|.

  Part 2  THE MOVES (quick guaranteed gain)
  -----------------------------------------
  We simplify a *representative* of the rotation ideal  I_w = <w0,...,w_{o-1}>
  (the cyclic rolls of w).  A representative here is a difference of two words
  S(u)-S(v); a move rewrites it within its pi_w-class (same S-value mod D up to a
  unit monomial) while strictly shrinking the total word length len u + len v --
  a guaranteed gain.  Three moves:

      prefix strip   S(x u') - S(x v') = X^{|x|} (S(u')-S(v'))           (exact)
      suffix strip   S(u' z) - S(v' z) = Y^{|z|} (S(u')-S(v'))          (exact, |u'|=|v'|)
      interior cancel + roll  (mod D, in-stratum only):
          S(P B Q) - S(P' B Q') = U ( S(Q P) - S(Q' P') )   (mod D),
          U = Y^{len B + len Q} X^{-|Q|},   when chi(Q)=chi(Q') and chi(PBQ)=chi(P'BQ').
          Exact residue:  X^{|Q|}(S(PBQ)-S(P'BQ')) - Y^{lenB+lenQ}(S(QP)-S(Q'P'))
                          = D * (S(Q)-S(Q')).

  Because the interior-cancel residue carries D = D(current word), it stays a
  multiple of the SEED D0 (hence of G = gcd_j S^{(j)}, the exclusion floor) only
  while the current word is still in the seed stratum (|.|=E0, len=o0).  We guard
  it there.  Exact strips are valid mod anything, so they may follow freely.
  (P11 lesson, reports/P11.md: never collapse to a Z/D residue -- we don't; the
  output is always an honest shorter word-difference sized by sixfree of S.)

  Part 3  THE ALGORITHM
  ---------------------
  greedy_simplify(w): seed rotations(w), reduce the chosen pairwise differences by
  repeatedly applying the largest-gain valid move, and report the smallest core,
  its sixfree(S-value), |D|, and the  S-value < 3^o  verdict (PROGRAM.md s5).

Run `python3 wordalg.py` for the self-test.
"""
from __future__ import annotations

import os
import sys
import itertools
from math import gcd
from functools import reduce as _reduce

import sympy as sp

# --- trusted kernel (robust to CWD) ---------------------------------------- #
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from cocycle import (  # noqa: E402
    S as _S_kernel, D as _D_kernel, rotate, rotations, partial_sums,
    X, Y, gcd_rotations, verify_symbolic_identity, verify_divisibility_battery,
)


# ===========================================================================
# Part 1 -- THE ALGEBRA  Z[W]
# ===========================================================================
def gapsum(w):
    """|w| -- the gap-sum (X / 2-degree)."""
    return sum(w)


def wlen(w):
    """len w -- the number of gaps (Y / 3-degree)."""
    return len(w)


def concat(u, v):
    """The monoid product (concatenation of words)."""
    return tuple(u) + tuple(v)


def chi(w):
    """The character chi(w) = X^{|w|} Y^{-len w}  (a Laurent unit monomial)."""
    return X ** gapsum(w) * Y ** (-wlen(w))


def chi_data(w):
    """(|w|, len w) -- chi(w) as an exponent pair; chi(u)=chi(v) iff equal pairs."""
    return (gapsum(w), wlen(w))


def Sword(w):
    """The cocycle S(w) in Z[X,Y] (kernel functional)."""
    return _S_kernel(tuple(w))


def Dword(w):
    """D(w) = X^{|w|} - Y^{len w} in Z[X,Y]."""
    return _D_kernel(tuple(w))


def M(w):
    """The transfer representation  M(w) = [[Y^{len w},0],[S(w),X^{|w|}]].

    Monoid hom: M(uv)=M(u)M(v).  Diagonal = character data, off-diagonal = S,
    D(w) = M[0,0]-M[1,1].
    """
    return sp.Matrix([[Y ** wlen(w), 0], [Sword(w), X ** gapsum(w)]])


def sixfree(m: int) -> int:
    """|m| with all factors of 2 and 3 removed (the exclusion axis)."""
    m = abs(int(m))
    if m == 0:
        return 0
    while m % 2 == 0:
        m //= 2
    while m % 3 == 0:
        m //= 3
    return m


def reduce_modD(expr, E, o):
    """Canonical remainder of `expr` modulo the ideal <X^E - Y^o>.

    X is the main variable and X^E - Y^o is monic in X, so the polynomial
    remainder is well defined; expr == 0 mod D  iff  this returns 0.  Used only
    to *certify* the mod-D moves -- never to size a representative.
    """
    expr = sp.expand(expr)
    if expr == 0:
        return sp.Integer(0)
    r = sp.Poly(expr, X).rem(sp.Poly(X ** E - Y ** o, X))
    return sp.expand(r.as_expr())


class Comb:
    """An element of the monoid algebra Z[W]:  sum_i coeff_i * [word_i].

    Coefficients live in Z[X,Y] (Laurent); words are tuples of positive gaps.
    This is the object the simplifier rewrites; a difference S(u)-S(v) is the
    two-term Comb {u: 1, v: -1}.
    """

    __slots__ = ("terms",)

    def __init__(self, terms=None):
        self.terms = {}
        if terms:
            for w, c in terms.items():
                self._add_term(tuple(w), sp.sympify(c))

    # -- construction ------------------------------------------------------- #
    @classmethod
    def word(cls, w, coeff=1):
        return cls({tuple(w): coeff})

    @classmethod
    def difference(cls, u, v):
        return cls({tuple(u): 1, tuple(v): -1})

    @classmethod
    def zero(cls):
        return cls()

    def _add_term(self, w, c):
        c = sp.expand(self.terms.get(w, sp.Integer(0)) + c)
        if c == 0:
            self.terms.pop(w, None)
        else:
            self.terms[w] = c

    # -- ring / module structure -------------------------------------------- #
    def __add__(self, other):
        out = Comb(self.terms)
        for w, c in other.terms.items():
            out._add_term(w, c)
        return out

    def __sub__(self, other):
        out = Comb(self.terms)
        for w, c in other.terms.items():
            out._add_term(w, -c)
        return out

    def __neg__(self):
        return Comb({w: -c for w, c in self.terms.items()})

    def scale(self, monomial):
        """Multiply every coefficient by a scalar / monomial in Z[X,Y]."""
        m = sp.sympify(monomial)
        return Comb({w: sp.expand(c * m) for w, c in self.terms.items()})

    def mul(self, other):
        """The monoid (concatenation) product, extended bilinearly."""
        out = Comb()
        for w1, c1 in self.terms.items():
            for w2, c2 in other.terms.items():
                out._add_term(concat(w1, w2), sp.expand(c1 * c2))
        return out

    # -- the structure maps applied to a combination ------------------------ #
    def S_value(self):
        """S(c) = sum_i coeff_i S(word_i)  in Z[X,Y]."""
        return sp.expand(sum((c * Sword(w) for w, c in self.terms.items()),
                             sp.Integer(0)))

    def value_at(self, x=2, y=3):
        """The integer (or rational) S-value at (X,Y)=(x,y)."""
        return self.S_value().subs({X: x, Y: y})

    def value_int(self):
        return int(self.value_at(2, 3))

    def sixfree_value(self):
        return sixfree(self.value_int())

    def pi(self, w):
        """Image under the quotient map pi_w: S(c) reduced mod D(w), at (2,3).

        Returns the least-magnitude residue in (-|D|/2, |D|/2].  Diagnostic only.
        """
        E, o = gapsum(w), wlen(w)
        Dabs = abs(2 ** E - 3 ** o)
        r = self.value_int() % Dabs
        if r > Dabs // 2:
            r -= Dabs
        return r

    # -- measures ----------------------------------------------------------- #
    def support(self):
        return list(self.terms.keys())

    def is_zero(self):
        return not self.terms

    def total_len(self):
        return sum(wlen(w) for w in self.terms)

    def n_terms(self):
        return len(self.terms)

    def __repr__(self):
        if not self.terms:
            return "0"
        parts = []
        for w, c in sorted(self.terms.items()):
            parts.append(f"({sp.srepr(c) if c.free_symbols else c})*{w}")
        return " + ".join(parts)


# ===========================================================================
# Part 2 -- THE MOVES (quick guaranteed gain)
# ===========================================================================
def _lcp(a, b):
    """Length of the longest common prefix."""
    k = 0
    for x, y in zip(a, b):
        if x != y:
            break
        k += 1
    return k


class Diff:
    """A reduction of a difference  S(u0)-S(v0)  of two SEED-stratum words.

    Invariant maintained (certified by .verify()):
        S(u0) - S(v0)  ==  unit * ( S(u) - S(v) )         (exact, or mod D0).
    The seed stratum is (E0,o0) = (|u0|, len u0); the interior-cancel (mod-D)
    move is only applied while (|u|,len u) == (E0,o0), so every residue it emits
    is a multiple of D0 and hence of G = gcd_j S^{(j)} -- the exclusion floor.
    """

    __slots__ = ("u0", "v0", "E0", "o0", "u", "v", "unit", "steps", "used_modD")

    def __init__(self, u0, v0):
        self.u0, self.v0 = tuple(u0), tuple(v0)
        self.E0, self.o0 = gapsum(u0), wlen(u0)
        self.u, self.v = tuple(u0), tuple(v0)
        self.unit = sp.Integer(1)
        self.steps = []
        self.used_modD = False

    # -- state -------------------------------------------------------------- #
    @property
    def in_stratum(self):
        return (gapsum(self.u), wlen(self.u)) == (self.E0, self.o0)

    @property
    def is_null(self):
        return self.u == self.v

    def core(self):
        return Comb.difference(self.u, self.v)

    def core_value(self):
        return int((Sword(self.u) - Sword(self.v)).subs({X: 2, Y: 3}))

    def core_sixfree(self):
        return sixfree(self.core_value())

    def mu(self):
        """The guaranteed-gain measure: total word length (3-degree budget)."""
        return wlen(self.u) + wlen(self.v)

    def __repr__(self):
        tag = "NULL(=0)" if self.is_null else f"6free={self.core_sixfree()}"
        return (f"<{self.u0}|{self.v0} -> {self.u}|{self.v} "
                f"unit={self.unit} {tag} steps={len(self.steps)}"
                f"{' modD' if self.used_modD else ''}>")

    # -- certification ------------------------------------------------------ #
    def verify(self):
        """Certify the cumulative invariant in Z[X,Y] (exact) or mod D0."""
        lhs = sp.expand(Sword(self.u0) - Sword(self.v0))
        rhs = sp.expand(self.unit * (Sword(self.u) - Sword(self.v)))
        if not self.used_modD:
            return sp.expand(lhs - rhs) == 0
        # mod-D moves used: clear the X-denominator of `unit`, then reduce mod D0.
        diff = sp.expand(lhs - rhs)
        diff = sp.expand(diff * X ** _denomX(self.unit))
        return reduce_modD(diff, self.E0, self.o0) == 0


def _denomX(expr):
    """Smallest k>=0 such that X^k * expr is X-polynomial (clears X^-a units)."""
    expr = sp.together(expr)
    num, den = sp.fraction(expr)
    p = sp.Poly(den, X)
    # den is a monomial c*X^a (the moves only ever divide by powers of X)
    return p.degree() if den.has(X) else 0


# --- the moves: each returns a NEW Diff (copy) or None --------------------- #
def _clone(d: Diff) -> Diff:
    e = Diff.__new__(Diff)
    e.u0, e.v0, e.E0, e.o0 = d.u0, d.v0, d.E0, d.o0
    e.u, e.v, e.unit = d.u, d.v, d.unit
    e.steps = list(d.steps)
    e.used_modD = d.used_modD
    return e


def move_prefix(d: Diff):
    """Strip the maximal shared prefix (exact). Gain = 2*len(prefix)."""
    if wlen(d.u) != wlen(d.v):
        return None
    k = _lcp(d.u, d.v)
    if k == 0:
        return None
    x = d.u[:k]
    e = _clone(d)
    e.u, e.v = d.u[k:], d.v[k:]
    e.unit = sp.expand(d.unit * X ** gapsum(x))
    e.steps.append(("prefix", x))
    return e


def move_suffix(d: Diff):
    """Strip the longest shared suffix whose remaining prefixes have equal
    gap-sum (exact). Gain = 2*len(suffix)."""
    if wlen(d.u) != wlen(d.v):
        return None
    m = _lcp(d.u[::-1], d.v[::-1])
    for t in range(m, 0, -1):
        up, vp = d.u[:wlen(d.u) - t], d.v[:wlen(d.v) - t]
        if gapsum(up) == gapsum(vp):
            z = d.u[wlen(d.u) - t:]
            e = _clone(d)
            e.u, e.v = up, vp
            e.unit = sp.expand(d.unit * Y ** wlen(z))
            e.steps.append(("suffix", z))
            return e
    return None


def interior_matches(u, v):
    """All (i, m): a shared interior block u[i:i+m]==v[i:i+m] (m>=1) whose flanks
    are character-equal (chi(prefix)=chi(prefix'), chi(suffix)=chi(suffix')).

    Yields (i, m) sorted by decreasing gain (block length m)."""
    if wlen(u) != wlen(v):
        return []
    n = wlen(u)
    out = []
    for i in range(0, n):
        for m in range(1, n - i + 1):
            B, Bp = u[i:i + m], v[i:i + m]
            if B != Bp:
                continue
            P, Pp = u[:i], v[:i]
            Q, Qp = u[i + m:], v[i + m:]
            if chi_data(P) == chi_data(Pp) and chi_data(Q) == chi_data(Qp):
                # skip the trivial whole-word block (would give u==v already)
                if m == n:
                    continue
                out.append((i, m))
    out.sort(key=lambda im: -im[1])
    return out


def move_interior_cancel(d: Diff):
    """Cancel a shared interior block and roll (mod D, in-stratum only).

        S(P B Q) - S(P' B Q')  ==  U ( S(Q P) - S(Q' P') )   (mod D0)
        U = Y^{len B + len Q} X^{-|Q|}.

    Valid as a chain step only while the current word is in the seed stratum
    (so the residue D*(S(Q)-S(Q')) is a multiple of D0, hence of G).
    Gain = 2*len(B)."""
    if not d.in_stratum:
        return None
    matches = interior_matches(d.u, d.v)
    if not matches:
        return None
    i, m = matches[0]                       # largest block = biggest gain
    P, B, Q = d.u[:i], d.u[i:i + m], d.u[i + m:]
    Pp, Qp = d.v[:i], d.v[i + m:]
    u_new, v_new = concat(Q, P), concat(Qp, Pp)
    if u_new == v_new:                      # degenerate (no representative left)
        return None
    U = Y ** (wlen(B) + wlen(Q)) * X ** (-gapsum(Q))
    e = _clone(d)
    e.u, e.v = u_new, v_new
    e.unit = sp.expand(d.unit * U)
    e.steps.append(("interior", (i, m, B)))
    e.used_modD = True
    return e


MOVES = (move_prefix, move_suffix, move_interior_cancel)


def reduce_diff(u0, v0, max_steps=10_000) -> Diff:
    """Greedy descent: at each step apply the valid move with the largest
    mu-gain, until irreducible. Returns the final Diff (its core is the
    simplest representative the moves reach)."""
    d = Diff(u0, v0)
    for _ in range(max_steps):
        if d.is_null:
            return d
        best, best_gain = None, 0
        for mv in MOVES:
            cand = mv(d)
            if cand is None:
                continue
            gain = d.mu() - cand.mu()
            if gain > best_gain:
                best, best_gain = cand, gain
        if best is None:
            return d
        d = best
    return d


# ===========================================================================
# Part 3 -- THE ALGORITHM (a strategy of simple combinations)
# ===========================================================================
def _pair_indices(n, pairs):
    if pairs == "all":
        return list(itertools.combinations(range(n), 2))
    if pairs == "adjacent":
        return [(i, (i + 1) % n) for i in range(n)]
    if pairs == "star":
        return [(0, j) for j in range(1, n)]
    return list(pairs)


def greedy_simplify(w, pairs="all"):
    """Seed rotations(w); reduce the chosen pairwise differences; return the
    smallest core and the squeeze report.

    pairs : "all" | "adjacent" | "star" | explicit list of (i,j) index pairs.
    """
    w = tuple(w)
    rots = rotations(w)
    n = len(rots)
    diffs = []
    for i, j in _pair_indices(n, pairs):
        diffs.append(reduce_diff(rots[i], rots[j]))
    nonnull = [d for d in diffs if not d.is_null]
    best = min(nonnull, key=lambda d: (d.core_sixfree(), d.mu()), default=None)

    E, o = gapsum(w), wlen(w)
    Dabs = abs(2 ** E - 3 ** o)
    G = gcd_rotations(w)
    report = {
        "word": w, "E": E, "o": o,
        "floor_|D|": Dabs, "gcd_rotations": G,
        "is_cycle(|D|==gcd)": (Dabs == G),
        "three_o": 3 ** o,
    }
    if best is not None:
        c6 = best.core_sixfree()
        report.update({
            "best_core": (best.u, best.v),
            "best_core_value": best.core_value(),
            "best_sixfree": c6,
            "best_mu": best.mu(),
            "sixfree<3^o": c6 < 3 ** o,
            "G_divides_core": (best.core_value() % G == 0) if G else None,
            "used_modD": best.used_modD,
        })
    return best, report, diffs


# ===========================================================================
# Self-test
# ===========================================================================
def _fmt(d):
    return "\n".join(f"  {k:>20}: {v}" for k, v in d.items())


def _selftest():
    import random
    print("=" * 72)
    print("Part 1 -- the algebra Z[W]")
    print("=" * 72)
    ok = True

    # M is a monoid hom: M(uv) = M(u) M(v).
    for u, v in [((1, 2), (3,)), ((2, 1, 3), (1, 4)), ((5,), (1, 1, 2))]:
        if sp.expand(M(concat(u, v)) - M(u) * M(v)) != sp.zeros(2):
            ok = False
            print(f"  [XX] M({u}{v}) != M({u})M({v})")
    print("  [..] M(uv) = M(u)M(v)            ", "ok" if ok else "FAIL")

    # chi is an algebra hom; D and S are the projections of M.
    chi_ok = S_ok = D_ok = True
    for u, v in [((1, 2), (3,)), ((2, 1, 3), (1, 4))]:
        if sp.simplify(chi(concat(u, v)) - chi(u) * chi(v)) != 0:
            chi_ok = False
        Mu = M(u)
        if sp.expand(Mu[1, 0] - Sword(u)) != 0:        # off-diagonal = S
            S_ok = False
        if sp.expand((Mu[1, 1] - Mu[0, 0]) - Dword(u)) != 0:   # diag diff = D
            D_ok = False
    print("  [..] chi(uv)=chi(u)chi(v)        ", "ok" if chi_ok else "FAIL")
    print("  [..] M off-diag = S, diag-diff=D ", "ok" if (S_ok and D_ok) else "FAIL")

    # Comb: concatenation product is bilinear and S-compatible with the cocycle.
    c = Comb.word((1, 2)).mul(Comb.word((3,)))
    comb_ok = (sp.expand(c.S_value() - Sword((1, 2, 3))) == 0)
    # quotient: on the -5->-7 cycle word (1,2), S(rot) all == |D| mod D == 0.
    pi_ok = all(Comb.word(r).pi((1, 2)) == 0 for r in rotations((1, 2)))
    print("  [..] Comb product <-> cocycle    ", "ok" if comb_ok else "FAIL")
    print("  [..] pi_w kills cycle rotations  ", "ok" if pi_ok else "FAIL")
    ok = ok and chi_ok and S_ok and D_ok and comb_ok and pi_ok

    print("\n" + "=" * 72)
    print("Part 2 -- every move is a certified identity")
    print("=" * 72)
    rng = random.Random(20260609)
    move_ok = True
    n_checked = 0
    # random critical-ish words; reduce all rotation pairs; verify each chain.
    for _ in range(40):
        o = rng.randint(2, 7)
        E = max(o, round(o * 1.5849625))
        gaps = [1] * o
        for _ in range(E - o):
            gaps[rng.randrange(o)] += 1
        w = tuple(gaps)
        rots = rotations(w)
        for i in range(len(rots)):
            for j in range(i + 1, len(rots)):
                d = reduce_diff(rots[i], rots[j])
                n_checked += 1
                if not d.verify():
                    move_ok = False
                    print(f"  [XX] verify failed: {w} pair ({i},{j}) -> {d}")
                # numeric net: G | core value (exclusion floor preserved).
                if not d.is_null and d.core_value() % gcd_rotations(w) != 0:
                    move_ok = False
                    print(f"  [XX] G does not divide core: {w} ({i},{j})")
    print(f"  [..] {n_checked} reduction chains certified "
          f"(exact Z[X,Y] / mod-D0, and G | core)  ",
          "ok" if move_ok else "FAIL")

    # explicit interior-cancel firing (uses a mod-D step) + symbolic identity.
    ic_ok = True
    ic_fired = 0
    for _ in range(200):
        o = rng.randint(3, 6)
        E = max(o, round(o * 1.5849625))
        gaps = [1] * o
        for _ in range(E - o):
            gaps[rng.randrange(o)] += 1
        w = tuple(gaps)
        rots = rotations(w)
        for i, j in itertools.combinations(range(len(rots)), 2):
            d0 = Diff(rots[i], rots[j])
            cand = move_interior_cancel(d0)
            if cand is None:
                continue
            ic_fired += 1
            # certify the single mod-D step: X^{|Q|}(S(u)-S(v)) - Y^{..}(S(u')-S(v')) = D*(...)
            if not cand.verify():
                ic_ok = False
            if cand.core_value() % gcd_rotations(w) != 0:
                ic_ok = False
            if ic_fired >= 30:
                break
        if ic_fired >= 30:
            break
    print(f"  [..] interior-cancel mod-D move fired {ic_fired}x, all certified  ",
          "ok" if ic_ok else "FAIL")
    ok = ok and move_ok and ic_ok

    print("\n" + "=" * 72)
    print("Part 3 -- reproduce P2 single-defect ceiling  sixfree(2^{|e-d|}-1)")
    print("=" * 72)
    print("  (P2 strips only the 2-power -> odd part 2^|e-d|-1; sixfree strips 2")
    print("   AND 3, so the tight ceiling is sixfree(2^|e-d|-1); both bound G.)")
    p2_ok = True
    for (a, b, d_, e_) in [(2, 3, 1, 4), (3, 3, 1, 5), (5, 0, 3, 7),
                           (0, 5, 1, 2), (2, 4, 2, 1), (4, 1, 1, 3)]:
        o = a + b + 1
        rho_a = (d_,) * (o - 2) + (e_,) + (d_,)      # rho_{o-2}
        rho_b = (d_,) * (o - 1) + (e_,)              # rho_{o-1}
        red = reduce_diff(rho_a, rho_b)
        oddpart = 2 ** abs(e_ - d_) - 1
        bound = sixfree(oddpart)
        got = red.core_sixfree()
        flag = "ok" if got == bound else "FAIL"
        if got != bound:
            p2_ok = False
        print(f"  d^{a} {e_} d^{b}  (o={o}):  reduced sixfree={got:<5} "
              f"vs sixfree(2^|e-d|-1)={bound:<5} (odd part {oddpart})  {flag}")
    ok = ok and p2_ok

    print("\n" + "=" * 72)
    print("Part 3 -- greedy_simplify squeeze report (critical words)")
    print("=" * 72)
    for w in [(1, 2), (1, 2, 1, 3), (1, 1, 2, 1, 1, 2),
              (2, 2, 2, 1, 2, 1, 1)]:   # last: the decisive core uses the mod-D move
        best, rep, _ = greedy_simplify(w)
        print(f"\n  w = {w}")
        print(_fmt(rep))

    # agreement with the existing engine on exact-only reductions.
    print("\n" + "=" * 72)
    print("Cross-check vs word_simplifier.reduce_pair (exact strips agree)")
    print("=" * 72)
    cross_ok = True
    try:
        sys.path.insert(0, os.path.join(
            _HERE, "..", "..", "..", "ideas", "cocycle-combinatorics", "tools"))
        import word_simplifier as ws  # noqa: E402
        for w in [(1, 2, 1, 3), (1, 1, 2, 1, 1, 2), (1, 2, 3, 4, 5)]:
            rots = rotations(w)
            for i, j in itertools.combinations(range(len(rots)), 2):
                old = ws.reduce_pair(rots[i], rots[j])
                if old.steps and all(s[0] in ("prefix", "suffix")
                                     for s in old.steps):
                    # pure-strip case: our exact path must agree on sixfree.
                    new_d = Diff(rots[i], rots[j])
                    cur = new_d
                    while True:
                        nxt = move_prefix(cur) or move_suffix(cur)
                        if nxt is None:
                            break
                        cur = nxt
                    if cur.core_sixfree() != sixfree(old.core_value()):
                        cross_ok = False
        print("  [..] exact-strip sixfree matches reduce_pair  ",
              "ok" if cross_ok else "FAIL")
    except Exception as ex:  # pragma: no cover
        print(f"  [--] skipped cross-check ({ex})")
    ok = ok and cross_ok

    print("\n" + "=" * 72)
    print("RESULT:", "ALL PASS" if ok else "FAILURES ABOVE")
    print("=" * 72)
    return ok


if __name__ == "__main__":
    sys.exit(0 if _selftest() else 1)
