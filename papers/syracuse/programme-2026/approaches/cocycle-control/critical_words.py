#!/usr/bin/env python3
"""Words / cycle classes at the *critical* gap-sum, and their rotation ranges.

For a length o = len(w) the **critical** gap-sum is the project's
    E_crit(o) = ceil(o * log2 3) = smallest E with 2^E > 3^o,
the unique E minimizing the positive denominator D = 2^E - 3^o (cheatsheet:
cycle-gcd criticality lemma).  Computed exactly as (3**o).bit_length() -- no
floating point.

This module exposes three functions keyed on o:

  1. critical_words(o)          -> list of every gap word w with |w|=E_crit, len=o
                                   (the compositions of E_crit into o positive parts).
  2. critical_cycle_classes(o)  -> the same, deduped up to cyclic rotation
                                   (one representative per necklace = one "cycle").
  3. critical_extremes_by_range(o, k=100)
                                -> the top-k and bottom-k cycle classes ranked by the
                                   cycle range R(w) = max_j S^(j) - min_j S^(j).

S and R use the same big-int convention as the kernel (lib/cocycle.py); run the
module with --check to cross-verify on random words.

Combinatorics warning: #words = C(E_crit-1, o-1) grows fast (o=13 -> 125,970;
o=18 -> ~21.5M; o=20 -> ~141M).  Exact enumeration runs while #words <=
--max-exact; beyond that critical_extremes_by_range falls back to random
sampling of cycle classes (critical_words / critical_cycle_classes still
enumerate exactly -- don't call them for large o).

CLI:
    python critical_words.py --o 13            # summary + top/bottom 10
    python critical_words.py --o 13 --k 100 --dump 20
    python critical_words.py --o 18 --sample 200000
"""

from __future__ import annotations

import argparse
import heapq
import os
import random
import sys
from math import comb


# --------------------------------------------------------------------------- #
# Primitives (kernel convention)                                              #
# --------------------------------------------------------------------------- #
def critical_E(o: int) -> int:
    """Smallest E with 2^E > 3^o  (= ceil(o*log2 3)); minimal positive D=2^E-3^o."""
    if o < 1:
        raise ValueError("o must be >= 1")
    return (3 ** o).bit_length()


def S_word(word) -> int:
    """S(w) = sum_k 2^{e_k} 3^{o-1-k}  via  S(u.(d)) = 3 S(u) + 2^{|u|}."""
    s = cum = 0
    for d in word:
        s = 3 * s + (1 << cum)
        cum += d
    return s


def cycle_range(word) -> int:
    """R(w) = max_j S(rotate(w,j)) - min_j S(rotate(w,j))  (the 'cycle range')."""
    o = len(word)
    vals = [S_word(word[j:] + word[:j]) for j in range(o)]
    return max(vals) - min(vals)


def canonical(word):
    """Lexicographically minimal rotation -- the necklace representative."""
    return min(word[j:] + word[:j] for j in range(len(word)))


def words_at(E: int, o: int):
    """Generator of every composition of E into exactly o positive parts (tuples)."""
    def rec(prefix, rem, left):
        if left == 0:
            if rem == 0:
                yield tuple(prefix)
            return
        for d in range(1, rem - (left - 1) + 1):
            prefix.append(d)
            yield from rec(prefix, rem - d, left - 1)
            prefix.pop()
    yield from rec([], E, o)


def _random_word(E: int, o: int, rng) -> tuple:
    if o == 1:
        return (E,)
    cuts = sorted(rng.sample(range(1, E), o - 1))
    bounds = [0] + cuts + [E]
    return tuple(bounds[i + 1] - bounds[i] for i in range(o))


# --------------------------------------------------------------------------- #
# 1. all words at the critical gap-sum                                         #
# --------------------------------------------------------------------------- #
def critical_words(o: int) -> list:
    """All gap words with len = o and |w| = E_crit(o)."""
    return list(words_at(critical_E(o), o))


# --------------------------------------------------------------------------- #
# 2. cycle classes (necklaces) at the critical gap-sum                         #
# --------------------------------------------------------------------------- #
def critical_cycle_classes(o: int) -> list:
    """One representative (min rotation) per cyclic class, len=o, |w|=E_crit(o)."""
    E = critical_E(o)
    seen = set()
    out = []
    for w in words_at(E, o):
        c = canonical(w)
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


# --------------------------------------------------------------------------- #
# 3. top / bottom k cycle classes by cycle range                              #
# --------------------------------------------------------------------------- #
def critical_extremes_by_range(o: int, k: int = 100, *, sample: int = 0,
                               seed: int = 12345, max_exact: int = 4_000_000):
    """Top-k and bottom-k cycle classes ranked by cycle_range R.

    Returns a dict:
        E           : critical gap-sum
        D           : 2^E - 3^o  (signed; > 0 at criticality)
        n_words     : C(E-1, o-1)  (number of linear words)
        n_classes   : number of distinct cycle classes considered
        exact       : True if every class was enumerated, False if sampled
        top         : [(word, R), ...]  descending by R   (len <= k)
        bottom      : [(word, R), ...]  ascending  by R   (len <= k)

    Exact while n_words <= max_exact (or pass sample>0 to force sampling); else
    uniform-samples cycle classes.  Memory stays O(n_classes + k) via heaps for
    the extremes, but the dedup set holds all seen classes."""
    E = critical_E(o)
    n_words = comb(E - 1, o - 1)
    small, large = [], []          # k-smallest via max-heap (-R); k-largest via min-heap

    def consider(c, R):
        if len(small) < k:
            heapq.heappush(small, (-R, c))
        elif R < -small[0][0]:
            heapq.heapreplace(small, (-R, c))
        if len(large) < k:
            heapq.heappush(large, (R, c))
        elif R > large[0][0]:
            heapq.heapreplace(large, (R, c))

    seen = set()
    if sample == 0 and n_words <= max_exact:
        for w in words_at(E, o):
            c = canonical(w)
            if c not in seen:
                seen.add(c)
                consider(c, cycle_range(c))
        exact = True
    else:
        rng = random.Random(seed)
        target = sample if sample > 0 else min(max_exact, 200_000)
        target = min(target, n_words)
        attempts = 0
        while len(seen) < target and attempts < max(target * 4, 1000):
            attempts += 1
            c = canonical(_random_word(E, o, rng))
            if c not in seen:
                seen.add(c)
                consider(c, cycle_range(c))
        exact = False

    top = [(c, R) for R, c in sorted(large, key=lambda t: -t[0])]
    bottom = [(c, -negR) for negR, c in sorted(small, key=lambda t: -t[0])]
    return {
        "E": E, "D": 2 ** E - 3 ** o, "n_words": n_words,
        "n_classes": len(seen), "exact": exact, "top": top, "bottom": bottom,
    }


# --------------------------------------------------------------------------- #
# Self-check against the sympy kernel                                          #
# --------------------------------------------------------------------------- #
def _self_check():
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.join(here, "..", "cocycle-combine", "lib"))
    try:
        import cocycle
    except Exception as exc:
        print(f"[self-check skipped: {exc}]")
        return
    rng = random.Random(0)
    for _ in range(300):
        w = tuple(rng.randint(1, 5) for _ in range(rng.randint(1, 8)))
        assert S_word(w) == cocycle.S_int(w), w
        kr = [cocycle.S_int(cocycle.rotate(w, j)) for j in range(len(w))]
        assert cycle_range(w) == max(kr) - min(kr), w
    # critical_E sanity: 2^(E-1) <= 3^o < 2^E
    for o in range(1, 40):
        E = critical_E(o)
        assert 2 ** (E - 1) <= 3 ** o < 2 ** E, (o, E)
    print("[self-check OK: S_word, cycle_range, critical_E verified]")


# --------------------------------------------------------------------------- #
# CLI                                                                          #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(
        description="Critical-E words, cycle classes, and range extremes.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    ap.add_argument("--o", type=int, required=True, help="length len(w)=o")
    ap.add_argument("--k", type=int, default=100, help="how many extremes each side")
    ap.add_argument("--dump", type=int, default=10, help="how many to print each side")
    ap.add_argument("--sample", type=int, default=0, help="force sampling N classes")
    ap.add_argument("--max-exact", type=int, default=4_000_000)
    ap.add_argument("--check", action="store_true", help="run kernel self-check first")
    args = ap.parse_args()

    if args.check:
        _self_check()

    E = critical_E(args.o)
    n_words = comb(E - 1, args.o - 1)
    D = 2 ** E - 3 ** args.o
    print(f"\no = {args.o}   ->   critical E = {E}   (2^{E} > 3^{args.o})")
    print(f"D = 2^{E} - 3^{args.o} = {D:,}   |D| = {abs(D):,}")
    print(f"#words  = C({E-1},{args.o-1}) = {n_words:,}")

    res = critical_extremes_by_range(
        args.o, k=args.k, sample=args.sample, max_exact=args.max_exact)
    tag = "exact" if res["exact"] else "SAMPLED"
    print(f"#cycle classes ({tag}) = {res['n_classes']:,}\n")

    def show(title, rows):
        print(f"--- {title} {min(args.dump, len(rows))} of {len(rows)} "
              f"(by cycle range R) ---")
        print(f"{'R':>18} {'R/|D|':>9}   word")
        for c, R in rows[:args.dump]:
            print(f"{R:>18,} {R/abs(D):>9.2f}   {c}")
        print()

    show("TOP", res["top"])
    show("BOTTOM", res["bottom"])


if __name__ == "__main__":
    main()
