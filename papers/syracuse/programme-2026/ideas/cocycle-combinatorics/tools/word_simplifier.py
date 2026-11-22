#!/usr/bin/env python3
r"""word_simplifier.py -- a simple word-difference simplification engine.

Goal (user strategy, 2026-06-09).  Do NOT look for a general reduction rule.
Instead apply *simple moves* to word-differences, track the simplification graph,
and read off -- near the "null node" (zero) -- the **simplest representative** of
the rotation ideal that the moves reach.  A second function compares the size of
that small representative to 1 - chi(w) (= the floor G = |2^E - 3^o|).

The objects (kernel: approaches/cocycle-combine/lib/cocycle.py)
--------------------------------------------------------------
A word w = (d_0,...,d_{n-1}) of positive gaps.  Cocycle
    S(uv) = Y^{len v} S(u) + X^{|u|} S(v),     |u| = gap-sum,  len = #gaps.
A *difference* node is an ordered pair (u, v) standing for the ideal element
S(u) - S(v).  The two boundary moves are exact Z[X,Y] identities:

  (P) strip shared PREFIX x   (always valid when len u = len v):
        S(x u') - S(x v') = X^{|x|} ( S(u') - S(v') )
  (S) strip shared SUFFIX z   (valid iff the remaining prefixes have equal
        gap-sum, |u'| = |v'|):
        S(u' z) - S(v' z) = Y^{|z|} ( S(u') - S(v') )

Each move multiplies the represented element by a 6-unit monomial X^a Y^b and
shortens both words.  Reduce greedily to an irreducible CORE (u*, v*); that is
"the simplest word possible" the moves reach.  S(u*) - S(v*) is the small
representative; its 6-free part is what the Matveev/Ellison bound squeezes.

The engine acts on a WORD SET, not a single word.  The fundamental object is a
set of words {w_1,...,w_k}; the moves reduce the differences drawn from the set
to the simplest generators of the lattice it spans.  The **roll is NOT built in**
-- it is one *seeding* operation: `roll(w)` returns the rotation set used to
initialise the first word set, after which the engine is roll-agnostic.  So
`simplify_set(roll(w))` is the rotation story ("1A1B - 1B1C", "1A1B - 1C1D", ...),
but `simplify_set(any_word_set)` works on an arbitrary set (mixed words, the
output of a previous move, a hand-built family) -- which is what makes multi-move
chains over evolving word sets possible.  A structured set (periodic / repeated
blocks) shares long frames and collapses hard; a generic set shares little.

Usage
-----
  python3 word_simplifier.py                 # self-test + demos
  python3 word_simplifier.py --dot W out.dot # emit the simplifying graph of word W
  (or import:  reduce_pair, simplify_word, compare_to_floor, family_scan, discover)
"""
from __future__ import annotations

import os
import sys
import argparse
import itertools
import random
from functools import reduce as _reduce
from math import gcd, log, log10, exp

import sympy as sp

# --- kernel import (robust to CWD) ----------------------------------------- #
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(_HERE, "..", "..", "..",
                                "approaches", "cocycle-combine", "lib"))
from cocycle import S, D, rotations, X, Y, gcd_rotations, partial_sums  # noqa: E402


# --------------------------------------------------------------------------- #
# small-integer helpers                                                       #
# --------------------------------------------------------------------------- #
def sixfree(m: int) -> int:
    """|m| with all factors of 2 and 3 removed (the exclusion axis)."""
    m = abs(int(m))
    if m == 0:
        return 0
    for p in (2, 3):
        while m % p == 0:
            m //= p
    return m


LOG10_2 = log10(2)
LOG10_3 = log10(3)


def character_bracket(word):
    """AM-GM estimator from the partial characters  chi(w_{<k}) = 2^{e_k} / 3^k  (k=0..n-1).

    S(w) = 3^{n-1} * sum_k chi_k, so the ARITHMETIC mean of the chi_k is
        A(w) = (1/n) sum_k chi_k = S(w) / (n * 3^{n-1}),
    while the GEOMETRIC mean is
        G(w) = (prod_k chi_k)^{1/n} = 2^{mean(e_k)} / 3^{(n-1)/2}.
    G(w) is ALMOST ABELIAN (it depends only on sum_k e_k and n, not on the order beyond
    that), which makes it a simple abelian estimator of the size of the (abelian) 6-free
    projection of the representative.  With the stark ratio  C(w) = max_k chi_k / min_k chi_k,
    AM-GM gives the two-sided bracket
        G(w)  <=  A(w)  <=  C(w) * G(w).
    Returned in log10 (the chi_k range over many orders for long words); the AM/GM gap
    log10(A/G) >= 0 is the Jensen / non-abelian spread."""
    w = tuple(word)
    n = len(w)
    e = partial_sums(w)
    lchi = [e[k] * LOG10_2 - k * LOG10_3 for k in range(n)]   # log10 chi_k
    lG = sum(lchi) / n                                        # log10 geometric mean
    m = max(lchi)                                             # log10 arithmetic mean (logsumexp)
    lA = m + log10(sum(10 ** (x - m) for x in lchi)) - log10(n)
    lC = max(lchi) - min(lchi)                               # log10 stark ratio max/min
    return {"log10_G": lG, "log10_A": lA, "log10_C": lC,
            "log10_CG": lG + lC, "amgm_gap": lA - lG}


def log10_int(n) -> float:
    """log10 of a (possibly huge) integer, robust past the float range."""
    n = abs(int(n))
    if n == 0:
        return float("-inf")
    if n < 10 ** 300:
        return log10(n)
    d = len(str(n))
    return (d - 15) + log10(int(str(n)[:15]))


def S_int(word) -> int:
    return int(S(word, 2, 3))


def D_abs(word) -> int:
    """|D| = |2^{gap-sum} - 3^{len}| -- the floor G on a genuine cycle (= |1-chi|*3^len)."""
    return abs(int(D(word, 2, 3)))


def _lcp(a, b) -> int:
    """length of the longest common prefix of tuples a, b."""
    k = 0
    for x, y in zip(a, b):
        if x != y:
            break
        k += 1
    return k


# --------------------------------------------------------------------------- #
# the effectively-controlled lower bound (the actual exclusion target)        #
# --------------------------------------------------------------------------- #
LOG2_3 = log(3) / log(2)        # 1.5849625... -- the critical slope E/o


def critical_bounds(E, o):
    """The floor |2^E - 3^o| and the *effectively-controlled* lower bound it targets.

    A representative C of a genuine cycle obeys 6free(C) >= G = |2^E - 3^o|, and a
    linear-form-in-logarithms bounds |2^E - 3^o| from below -- THAT controlled bound
    (not the raw |D| of one word) is the exclusion target.

    Critical (near-coincidence E ~ o*log2(3), where cycles live): the SHARP effective
    bound is Rhin's (1987), as used by Simons-de Weger (Math. Comp. 74, 2005, Lemma
    12 -- and the paper states Rhin is *best* for the case x log2 + y log3):
        Lambda := |E ln2 - o ln3|  >  exp(-13.3 (0.46057 + ln o))  =  0.00219 * o^-13.3,
    hence (since |2^E - 3^o| >= min(2^E,3^o) * Lambda)
        |2^E - 3^o|  >  min(2^E,3^o) * exp(-13.3 (0.46057 + ln o))  ~  0.00219 * 3^o / o^13.3.
    This is POLYNOMIAL with exponent 13.3 (and a tiny constant): weak in the practical
    range -- it only exceeds a *constant* ceiling c once o is ~60-90, which is the true
    rigorous exclusion threshold for a bounded-ceiling family.  (Conjecturally the
    irrationality measure of log2(3) is 2, giving |2^E-3^o| >= 3^{o(1-eps)} ~ 3^o, but
    that is NOT proven.)  Not critical: the gap is trivially ~min(2^E, 3^o).

    Earlier versions were wrong: mu(log 3)<=5.125 (Salikhov) is the WRONG number, and
    a "3^{0.9 o}" form (from a bad secondary source) is NOT a valid lower bound -- at
    deep convergents of log2(3) it exceeds |2^E-3^o|.  This Rhin/de Weger form is the
    verified one (de Weger 2005, Lemma 12)."""
    D = abs(2 ** E - 3 ** o)
    p2, p3 = 2 ** E, 3 ** o
    critical = abs(E - o * LOG2_3) <= 1.0
    if critical and o >= 2:
        denom = int(exp(13.3 * (0.46057 + log(o)))) + 1   # ~ 457.4 * o^13.3
        controlled = max(1, min(p2, p3) // denom)         # min(2^E,3^o) * Lambda_Rhin
        name = "Rhin/de Weger 2005 (effective)"
    elif critical:
        controlled = 1
        name = "n/a (o=1)"
    else:
        controlled = min(p2, p3)                          # |2^E-3^o| >= min when far apart
        name = "trivial min(2^E, 3^o)"
    return {"E": E, "o": o, "floor_D": D, "three_o": p3,
            "critical": critical, "controlled": controlled, "controlled_name": name}


def random_critical_word(o, rng):
    """A random length-o word in the critical regime: gap-sum E = round(o*log2 3),
    so 2^E ~ 3^o (a genuine-cycle-shaped word, gaps mostly 1s and 2s)."""
    E = max(o, round(o * LOG2_3))
    gaps = [1] * o
    for _ in range(E - o):
        gaps[rng.randrange(o)] += 1
    return tuple(gaps)


# --------------------------------------------------------------------------- #
# the reduction engine                                                        #
# --------------------------------------------------------------------------- #
class Reduction:
    """Result of reducing a difference (u0, v0) = S(u0) - S(v0).

    Invariant (verified):  S(u0) - S(v0) = X^ux * Y^uy * ( S(u*) - S(v*) ).
    """
    __slots__ = ("u0", "v0", "u", "v", "ux", "uy", "steps")

    def __init__(self, u0, v0):
        self.u0, self.v0 = tuple(u0), tuple(v0)
        self.u, self.v = tuple(u0), tuple(v0)
        self.ux = self.uy = 0
        self.steps = []  # list of ("prefix"|"suffix", frame_tuple)

    # -- the small representative ------------------------------------------- #
    @property
    def core_pair(self):
        return (self.u, self.v)

    @property
    def is_null(self) -> bool:
        return self.u == self.v               # reduced to 0: a genuine relation

    def core_value(self) -> int:
        return S_int(self.u) - S_int(self.v)

    def core_sixfree(self) -> int:
        return sixfree(self.core_value())

    def core_len(self) -> int:
        return len(self.u) + len(self.v)

    def __repr__(self):
        tag = "NULL(=0)" if self.is_null else f"core6f={self.core_sixfree()}"
        return (f"<{self.u0}|{self.v0} -> {self.u}|{self.v} "
                f"X^{self.ux}Y^{self.uy} {tag} steps={len(self.steps)}>")


def reduce_pair(u0, v0, max_steps: int = 10_000) -> Reduction:
    """Greedily strip shared boundary frames until irreducible (the simplest word)."""
    r = Reduction(u0, v0)
    if len(r.u) != len(r.v):
        return r  # the boundary moves need equal length (rotations supply this)
    for _ in range(max_steps):
        if r.u == r.v:
            return r
        # (P) maximal shared prefix -- always exact for equal-length pair
        k = _lcp(r.u, r.v)
        if k > 0:
            x = r.u[:k]
            r.ux += sum(x)
            r.u, r.v = r.u[k:], r.v[k:]
            r.steps.append(("prefix", x))
            continue
        # (S) longest shared suffix z whose remaining prefixes have equal gap-sum
        m = _lcp(r.u[::-1], r.v[::-1])
        stripped = False
        for t in range(m, 0, -1):
            up, vp = r.u[:len(r.u) - t], r.v[:len(r.v) - t]
            if sum(up) == sum(vp):                 # |u'| = |v'|  -> X-terms cancel
                z = r.u[len(r.u) - t:]
                r.uy += len(z)
                r.u, r.v = up, vp
                r.steps.append(("suffix", z))
                stripped = True
                break
        if not stripped:
            return r  # irreducible core
    return r


def verify_reduction(r: Reduction) -> bool:
    """Certify the invariant S(u0)-S(v0) == X^ux Y^uy (S(u*)-S(v*)) in Z[X,Y]."""
    lhs = sp.expand(S(r.u0) - S(r.v0))
    rhs = sp.expand(X ** r.ux * Y ** r.uy * (S(r.u) - S(r.v)))
    return sp.expand(lhs - rhs) == 0


# --------------------------------------------------------------------------- #
# the MULTI-STEP move: split a difference at every shared interior anchor      #
# --------------------------------------------------------------------------- #
def split_points(u, v):
    """Interior anchors: positions 0 < k < n where the prefix-gap-sums coincide
    (sum(u[:k]) == sum(v[:k])) -- the cocycle splits the difference cleanly there.
    Frame strips are the special cases k = lcp (left segment is NULL)."""
    eu, ev = partial_sums(u), partial_sums(v)
    return [k for k in range(1, len(u)) if eu[k] == ev[k]]


class DecompNode:
    """A node of the decomposition tree: contributes  X^ux Y^uy (S(u)-S(v))."""
    __slots__ = ("u", "v", "ux", "uy", "kind", "k", "children")

    def __init__(self, u, v, ux, uy):
        self.u, self.v = tuple(u), tuple(v)
        self.ux, self.uy = ux, uy
        self.kind = "LEAF"     # LEAF (atomic) | NULL (segment coincides) | SPLIT
        self.k = None
        self.children = []

    def value(self):
        return S_int(self.u) - S_int(self.v)

    def core_sixfree(self):
        return sixfree(self.value())


def decompose(u, v, ux=0, uy=0):
    """Multi-step reduction: peel the leftmost atomic segment at each shared
    anchor, recursing on the remainder, down to atomic leaves / NULL segments.
    Invariant: S(u)-S(v) = sum over leaves of  X^{leaf.ux} Y^{leaf.uy} (S-S).
    Returns the root DecompNode (a chain of splits)."""
    node = DecompNode(u, v, ux, uy)
    if len(node.u) != len(node.v):
        return node
    if node.u == node.v:
        node.kind = "NULL"
        return node
    ks = split_points(node.u, node.v)
    if not ks:
        node.kind = "LEAF"                       # no interior anchor -> atomic
        return node
    k = ks[0]
    n = len(node.u)
    ek = sum(node.u[:k])
    node.kind, node.k = "SPLIT", k
    node.children = [
        decompose(node.u[:k], node.v[:k], ux, uy + (n - k)),   # leftmost segment
        decompose(node.u[k:], node.v[k:], ux + ek, uy),        # the remainder
    ]
    return node


def decomp_leaves(node):
    if node.kind in ("LEAF", "NULL"):
        return [node]
    out = []
    for c in node.children:
        out.extend(decomp_leaves(c))
    return out


def verify_decomposition(u, v):
    """Certify S(u)-S(v) == sum_leaves X^ux Y^uy (S(u_seg)-S(v_seg)) in Z[X,Y]."""
    root = decompose(tuple(u), tuple(v))
    total = sum(X ** lf.ux * Y ** lf.uy * (S(lf.u) - S(lf.v))
                for lf in decomp_leaves(root))
    return sp.expand(S(tuple(u)) - S(tuple(v)) - total) == 0


# --------------------------------------------------------------------------- #
# ANCHORED free basis (not the redundant all-pairs) + a combination round      #
# --------------------------------------------------------------------------- #
def anchored_pairs(words, group_by="first"):
    """A FREE set of anchored differences (target, anchor) -- not all-pairs.

    All-pairs is redundant: (w_i-w_j)+(w_j-w_k)+(w_k-w_i)=0, so only n-1 of the
    n-choose-2 differences are independent.  Anchoring picks a reference per group
    and takes w_j - w_anchor, which IS a free (independent) generating set.
      group_by="w0"    : every word anchored at index 0  (free basis, rank n-1).
      group_by="first" : group by the first gap, anchor each group  (so each
                         anchored difference shares a prefix and reduces well).
    Returns a list of (anchor_idx, target_idx)."""
    ws = list(words)
    n = len(ws)
    if group_by in ("w0", "global"):
        return [(0, j) for j in range(1, n)]
    if group_by == "first":
        groups = {}
        for i, w in enumerate(ws):
            groups.setdefault(w[0], []).append(i)
        out = []
        for g in groups.values():
            out += [(g[0], j) for j in g[1:]]
        return out
    raise ValueError(f"unknown group_by={group_by!r}")


def lattice_simplify(words, group_by="first"):
    """Two-round anchored simplification.

    Round 1 : the free anchored basis  g = reduce(w_j - w_anchor).
    Round 2 : within-anchor COMBINATIONS  (w_{j1}-w_a) - (w_{j2}-w_a) = w_{j1}-w_{j2}
              -- the straightforward comparison of two simplified words, a linear
              combination of round 1, where shared structure can cancel further.
    Returns the generators, the combinations, and the global smallest core."""
    ws = list(dict.fromkeys(tuple(x) for x in words))
    gens = [{"a": a, "j": j, "r": reduce_pair(ws[j], ws[a])}
            for (a, j) in anchored_pairs(ws, group_by)]
    by_anchor = {}
    for gi, g in enumerate(gens):
        by_anchor.setdefault(g["a"], []).append(gi)
    combos = []
    for a, gis in by_anchor.items():
        for p, q in itertools.combinations(gis, 2):
            j1, j2 = gens[p]["j"], gens[q]["j"]
            combos.append({"a": a, "g1": p, "g2": q, "j1": j1, "j2": j2,
                           "r": reduce_pair(ws[j1], ws[j2])})
    allreds = [g["r"] for g in gens] + [c["r"] for c in combos]
    nonnull = [r for r in allreds if not r.is_null]
    best = min(nonnull, key=lambda r: (r.core_sixfree(), r.core_len()),
               default=None)
    rank = len(gens)                              # anchored generators are free
    return {"words": ws, "gens": gens, "combos": combos, "best": best,
            "n_groups": len(by_anchor), "rank": rank,
            "n_allpairs": len(ws) * (len(ws) - 1) // 2}


def lattice_dot(words, group_by="first"):
    """DOT of the anchored lattice: anchors -> round-1 free basis -> round-2 combos."""
    res = lattice_simplify(words, group_by)
    ws, best = res["words"], res["best"]
    L = ["digraph lattice {",
         '  rankdir=LR; node [shape=box,fontsize=11,fontname="Helvetica"];',
         '  edge [fontname="Helvetica",fontsize=9,color="#888888"];']
    cores = {}

    def core_node(r):
        if r.is_null:
            nid = "NULL"
            L.append(f'  {nid} [label="0 (relation)",shape=doublecircle,'
                     'style=filled,fillcolor="#f0e68c"];')
            return nid
        key = r.core_pair
        if key not in cores:
            cid = f"core{len(cores)}"
            cores[key] = cid
            hl = best is not None and key == best.core_pair
            fill = "#ffd95a" if hl else "#ffe1e6"
            L.append(f'  {cid} [label="{r.u} | {r.v}\\n6-free = '
                     f'{r.core_sixfree()}",style=filled,fillcolor="{fill}"];')
        return cores[key]

    for a in sorted({g["a"] for g in res["gens"]}):
        L.append(f'  a{a} [label="anchor w{a}\\n{ws[a]}",shape=oval,'
                 'style=filled,fillcolor="#bcdcf5"];')
    for gi, g in enumerate(res["gens"]):
        L.append(f'  g{gi} [label="round 1\\nw{g["j"]} - w{g["a"]}",'
                 'style=filled,fillcolor="#eef3f8"];')
        L.append(f'  a{g["a"]} -> g{gi};')
        L.append(f'  g{gi} -> {core_node(g["r"])};')
    for ci, c in enumerate(res["combos"]):
        L.append(f'  k{ci} [label="round 2\\nw{c["j1"]} - w{c["j2"]}",'
                 'style=filled,fillcolor="#e8f5e9"];')
        L.append(f'  g{c["g1"]} -> k{ci} [style=dashed,label="+"];')
        L.append(f'  g{c["g2"]} -> k{ci} [style=dashed,label="-"];')
        L.append(f'  k{ci} -> {core_node(c["r"])};')
    L.append("}")
    return "\n".join(L)


def decomposition_dot(u, v):
    """DOT of the multi-step decomposition tree of a single difference (u, v)."""
    root = decompose(tuple(u), tuple(v))
    atoms = [lf for lf in decomp_leaves(root) if lf.kind == "LEAF"]
    best = min(atoms, key=lambda lf: lf.core_sixfree(), default=None)
    L = ["digraph decomp {",
         '  rankdir=LR; node [shape=box,fontsize=11,fontname="Helvetica"];',
         '  edge [fontname="Helvetica",fontsize=9,color="#888888"];']
    ctr = [0]

    def emit(node):
        nid = f"n{ctr[0]}"
        ctr[0] += 1
        if node.kind == "NULL":
            L.append(f'  {nid} [label="{node.u} = {node.v}\\n0 (anchor segment)",'
                     f'shape=doublecircle,style=filled,fillcolor="#f0e68c"];')
        elif node.kind == "LEAF":
            hl = best is not None and (node.u, node.v) == (best.u, best.v)
            fill = "#ffd95a" if hl else "#ffe1e6"
            L.append(f'  {nid} [label="{node.u} | {node.v}\\n6-free = '
                     f'{node.core_sixfree()}",style=filled,fillcolor="{fill}"];')
        else:
            L.append(f'  {nid} [label="{node.u}\\n{node.v}\\nsplit @ {node.k}",'
                     f'style=filled,fillcolor="#eaf1f8"];')
            for c in node.children:
                cid = emit(c)
                L.append(f'  {nid} -> {cid} '
                         f'[label="X^{c.ux - node.ux} Y^{c.uy - node.uy}"];')
        return nid

    emit(root)
    L.append("}")
    return "\n".join(L)


# --------------------------------------------------------------------------- #
# seeding: the ROLL (the only place rotation enters -- not part of the engine) #
# --------------------------------------------------------------------------- #
def roll(w):
    """Seed a word set from one word: its rotation set.  ONLY rotation user."""
    return list(rotations(tuple(w)))


# --------------------------------------------------------------------------- #
# the engine: act on a WORD SET (reduce the differences it spans)             #
# --------------------------------------------------------------------------- #
def simplify_set(words, pairs="all"):
    """Reduce the differences drawn from a word SET; return (best, reductions).

    `words` : any iterable of words (a set).  No built-in roll -- pass roll(w)
              to get the rotation story, or any other set.
    `pairs`  : "all" (every i<j) | "adjacent" (cyclic j=i+1) |
               an explicit list of (a, b) where a, b are words or set-indices.
    best = the non-null reduction with the smallest 6-free core (the simplest
    nonzero representative); null reductions (genuine relations) are kept too.
    """
    ws = list(dict.fromkeys(tuple(x) for x in words))   # dedup, preserve order
    n = len(ws)
    if pairs == "all":
        idx = list(itertools.combinations(range(n), 2))
    elif pairs == "adjacent":
        idx = [(i, (i + 1) % n) for i in range(n)]
    elif pairs == "star":                       # w0 vs each other (the user's moves)
        idx = [(0, j) for j in range(1, n)]
    else:
        idx = []
        for a, b in pairs:
            ia = a if isinstance(a, int) else ws.index(tuple(a))
            ib = b if isinstance(b, int) else ws.index(tuple(b))
            idx.append((ia, ib))
    reds = []
    for i, j in idx:
        reds.append(((i, j), reduce_pair(ws[i], ws[j])))
    nonnull = [(ij, r) for ij, r in reds if not r.is_null]
    best = min(nonnull, key=lambda t: (t[1].core_sixfree(), t[1].core_len()),
               default=None)
    return best, reds


def simplify_word(w, pairs="all"):
    """Convenience wrapper: SEED the set with the roll of w, then run the engine.

    Identical to simplify_set(roll(w)); kept so the floor/family/discover helpers
    read naturally.  The roll is explicitly a seed here, not part of the engine.
    """
    return simplify_set(roll(w), pairs=pairs)


# --------------------------------------------------------------------------- #
# compare the small representative to 1 - chi  ( = the floor G = |D| )         #
# --------------------------------------------------------------------------- #
def compare_to_floor(w, r: Reduction | None = None):
    """Size of the small representative vs the floor 1-chi ~ G = |D| = |2^E-3^o|."""
    w = tuple(w)
    if r is None:
        best, _ = simplify_word(w)
        r = best[1] if best else reduce_pair(w, rotations(w)[1 % len(w)])
    G = D_abs(w)                          # |D| = the integer 1-chi ideal generator
    Ggcd = gcd_rotations(w)               # gcd_j S^{(j)} ( = |D| on a genuine cycle)
    c6 = r.core_sixfree()
    cval = r.core_value()
    return {
        "word": w,
        "E_gapsum": sum(w),
        "o_len": len(w),
        "floor_|D|": G,
        "gcd_rotations": Ggcd,
        "is_cycle(|D|==gcd)": (G == Ggcd),
        "core_pair": r.core_pair,
        "core_value": cval,
        "core_sixfree": c6,
        "core_len": r.core_len(),
        "sixfree(core)/|D|": (c6 / G) if G else float("inf"),
        "log10(6free/|D|)": (log10_int(c6) - log10_int(G)) if (c6 and G) else float("-inf"),
        "G_divides_core": (cval % Ggcd == 0) if Ggcd else None,
    }


# --------------------------------------------------------------------------- #
# family scan: does the simplest representative stay BOUNDED as o grows?       #
# --------------------------------------------------------------------------- #
def family_scan(family_fn, params, label=""):
    """family_fn(p) -> word.  Tabulate min-6free core vs |D| over p; flag bounded."""
    rows = []
    for p in params:
        w = tuple(family_fn(p))
        best, _ = simplify_word(w)
        if best is None:
            rows.append((p, w, None, D_abs(w), None))
            continue
        r = best[1]
        rows.append((p, w, r.core_sixfree(), D_abs(w), r.core_pair))
    c6s = [c for _, _, c, _, _ in rows if c is not None]
    # log10(6-free / |D|) trend: for a bounded ceiling this dives to -inf as |D| grows
    log10s = [round(log10_int(c) - log10_int(d), 2)
              for _, _, c, d, _ in rows if c is not None]
    # o-independent  <=>  the TAIL stabilises (early transients are fine)
    tail = c6s[-3:] if len(c6s) >= 3 else c6s
    bounded = bool(tail) and (max(tail) == min(tail))
    return {"label": label, "rows": rows, "ceiling_bounded": bounded,
            "ceiling_stabilises_to": (tail[-1] if bounded else None),
            "ceilings": c6s, "log10_6free_over_D": log10s}


# --------------------------------------------------------------------------- #
# discover: scan words, surface UNEXPECTEDLY small representatives            #
# --------------------------------------------------------------------------- #
def discover(length, max_gap=3, samples=None, ratio=0.5, seed_words=None):
    """Find words whose simplest representative is surprisingly small vs |D|.

    Returns the words where sixfree(core)/|D| <= ratio (the "unexpected" sinks).
    samples=None enumerates all words of the given length over gaps 1..max_gap.
    """
    if seed_words is not None:
        space = [tuple(w) for w in seed_words]
    elif samples is None:
        space = [w for w in itertools.product(range(1, max_gap + 1), repeat=length)]
    else:
        rng = random.Random(12345)
        space = [tuple(rng.randint(1, max_gap) for _ in range(length))
                 for _ in range(samples)]
    hits = []
    for w in space:
        if len(w) < 2:
            continue
        G = D_abs(w)
        if G == 0:
            continue
        best, _ = simplify_word(w)
        if best is None:
            continue
        r = best[1]
        c6 = r.core_sixfree()
        if c6 <= ratio * G:
            is_cyc = (gcd_rotations(w) == G)   # genuine cycle: floor = |D|, exclusion bites
            hits.append((w, c6, G, r.core_pair, is_cyc))
    hits.sort(key=lambda t: (t[1], -t[2]))
    return hits


# --------------------------------------------------------------------------- #
# graph export (DOT) -- "draw the simplifying graph"                          #
# --------------------------------------------------------------------------- #
def reduction_dot(words, pairs="all", seed_label=None, highlight_best=True):
    """Emit a Graphviz DOT of the simplifying graph of a word SET: pairs -> cores -> NULL.

    The smallest 6-free core (the simplest representative) is highlighted gold;
    cores reached by several pairs are drawn once (so convergence is visible).
    """
    ws = list(dict.fromkeys(tuple(x) for x in words))
    best, reds = simplify_set(ws, pairs=pairs)
    best_key = best[1].core_pair if best else None
    label = seed_label or ("set " + str(ws if len(ws) <= 4 else f"{ws[:4]}+{len(ws)-4}"))
    L = ["digraph simplify {",
         '  rankdir=LR; bgcolor="transparent";',
         '  node [shape=box,fontsize=11,fontname="Helvetica"];',
         '  edge [fontname="Helvetica",fontsize=9,color="#888888"];',
         f'  start [label="{label}",shape=oval,style=filled,fillcolor="#bcdcf5"];']
    core_id, has_null = {}, False
    for (i, j), r in reds:                                    # define nodes once
        L.append(f'  r{i}_{j} [label="w{i} - w{j}\\n{r.u0}\\n{r.v0}",'
                 f'style=filled,fillcolor="#f4f4f4"];')
        if r.is_null:
            has_null = True
            continue
        key = r.core_pair
        if key not in core_id:
            cid = f"c{len(core_id)}"
            core_id[key] = cid
            fill = "#ffd95a" if (highlight_best and key == best_key) else "#ffe1e6"
            L.append(f'  {cid} [label="{r.u} | {r.v}\\n6-free = {r.core_sixfree()}",'
                     f'style=filled,fillcolor="{fill}"];')
    if has_null:
        L.append('  NULL [label="0 (relation)",shape=doublecircle,'
                 'style=filled,fillcolor="#f0e68c"];')
    for (i, j), r in reds:                                    # edges
        L.append(f'  start -> r{i}_{j};')
        tgt = "NULL" if r.is_null else core_id[r.core_pair]
        L.append(f'  r{i}_{j} -> {tgt} [label="X^{r.ux} Y^{r.uy}"];')
    L.append("}")
    return "\n".join(L)


# --------------------------------------------------------------------------- #
# demos / self-test                                                           #
# --------------------------------------------------------------------------- #
def _fmt(d):
    return "  " + "\n  ".join(f"{k:>22}: {v}" for k, v in d.items())


def _demo():
    print("=" * 74)
    print("SELF-TEST -- every reduction's invariant is an exact Z[X,Y] identity")
    print("=" * 74)
    tests = [((1, 2, 1, 3), 1), ((1, 1, 2, 1, 1, 2), 2),
             ((2, 3, 2, 3, 2, 3), 3), ((1, 2, 3, 4, 5), 2)]
    ok = True
    for w, j in tests:
        for i in range(len(w)):
            r = reduce_pair(rotations(w)[i], rotations(w)[(i + j) % len(w)])
            good = verify_reduction(r)
            ok = ok and good
            if not good:
                print(f"  [XX] {w} pair ({i},{i+j}) FAILED invariant")
    print(f"  [{'ok' if ok else 'XX'}] all reduction invariants verified symbolically")

    print("\n" + "=" * 74)
    print("DEMO 0 -- the engine acts on a WORD SET; the roll is just one seeding")
    print("=" * 74)
    seed = roll((2, 3, 1))
    print(f"  roll((2,3,1)) seeds the set -> {seed}")
    b, _ = simplify_set(seed)
    print(f"  simplify_set(that set): simplest core = {b[1].core_pair}  "
          f"6free={b[1].core_sixfree()}")
    arb = [(2, 3, 1), (1, 3, 2), (3, 2, 1)]   # NOT a single word's rotation set
    b2, _ = simplify_set(arb)
    print(f"  simplify_set on a hand-built (non-roll) set {arb}:")
    print(f"     simplest core = {b2[1].core_pair}  6free={b2[1].core_sixfree()}  "
          f"-> engine is roll-agnostic")

    print("\n" + "=" * 74)
    print("DEMO 1 -- periodic background u^p . beta  (roll seeds, frame collapses)")
    print("=" * 74)
    for u, beta in [((1, 2), (3,)), ((2, 1), (4,)), ((2, 3), (1,))]:
        fam = family_scan(lambda p, u=u, beta=beta: u * p + beta, range(2, 9),
                          label=f"u={u} beta={beta}")
        cs = fam["ceilings"]
        print(f"  u={u} beta={beta}:  min-6free core over p=2..8 = {cs}  "
              f"-> bounded={fam['ceiling_bounded']}")
        print(f"     log10(6-free/|D|) over p=2..8 = {fam['log10_6free_over_D']}  "
              f"(dives as |D| grows -> the exclusion signal)")
        last = fam["rows"][-1]
        print(f"     largest word p=8: |D|={last[3]:>22}  simplest 6free={last[2]}  "
              f"core={last[4]}")

    print("\n" + "=" * 74)
    print("DEMO 2 -- a generic word barely simplifies (no long shared frame)")
    print("=" * 74)
    for w in [(1, 2, 3, 4, 5), (3, 1, 4, 1, 5, 2)]:
        print(_fmt(compare_to_floor(w)))
        print()

    print("=" * 74)
    print("DEMO 3 -- the circuit extreme  w = (1,1,...,1, K)  (one heavy run)")
    print("=" * 74)
    for w in [(1, 1, 1, 1, 6), (1, 1, 1, 1, 1, 1, 9)]:
        print(_fmt(compare_to_floor(w)))
        print()

    print("=" * 74)
    print("DISCOVER -- words of length 4 (gaps 1..3) whose simplest rep is")
    print("            unexpectedly small:  sixfree(core) <= 0.5 * |D|")
    print("=" * 74)
    hits = discover(length=4, max_gap=3, ratio=0.5)
    for w, c6, G, core, is_cyc in hits[:15]:
        flag = "  <== genuine cycle (exclusion bites)" if is_cyc else ""
        print(f"  w={w}  6free(core)={c6:<6} |D|={G:<8} ratio={c6/G:.3f}  "
              f"core={core}{flag}")
    print(f"  ... {len(hits)} words flagged (smallest representatives first)")


def main():
    ap = argparse.ArgumentParser(description="word-difference simplification engine")
    ap.add_argument("--dot", nargs=2, metavar=("WORD", "OUT"),
                    help='emit DOT graph; WORD like "1,2,1,3"')
    ap.add_argument("--word", metavar="WORD", help='compare one word to the floor')
    args = ap.parse_args()
    if args.dot:
        w = tuple(int(x) for x in args.dot[0].split(","))
        with open(args.dot[1], "w") as fh:
            fh.write(reduction_dot(roll(w), seed_label=f"roll{w}"))   # roll = the seed
        print(f"wrote {args.dot[1]} for word {w}  (render: dot -Tpng {args.dot[1]} -o g.png)")
        return
    if args.word:
        w = tuple(int(x) for x in args.word.split(","))
        print(_fmt(compare_to_floor(w)))
        return
    _demo()


if __name__ == "__main__":
    main()
