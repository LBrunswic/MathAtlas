#!/usr/bin/env python3
"""Empirical CDF (cumulative density) of S(w) over words of fixed |w| = E.

For a gap word w = (d_0,...,d_{o-1}) with partial sums e_k = sum_{i<k} d_i
(e_0 = 0) the project's sum functional is

    S(w) = sum_{k=0}^{o-1} 2^{e_k} 3^{o-1-k}.

This script enumerates the words with |w| = E (the compositions of E into
positive parts), computes S(w) for each, and plots the empirical CDF:
the x-axis is the S(w) value, the y-axis is the cumulative fraction of words
with S <= x.  By default |w| = E is fixed and the length o = len(w) is free
(this is literally "the range of S(w) when |w| is fixed"); pass --o to also
fix the length, or --by-len to draw one curve per length.

Enumeration is exact while the word count 2^(E-1) (or C(E-1,o-1) for fixed o)
stays under --max-exact; beyond that the script falls back to uniform random
sampling and says so on stdout.

S is computed directly with Python big integers for speed; on startup we
cross-check the direct formula against the trusted sympy kernel
(cocycle-combine/lib/cocycle.py) on a handful of words so the convention is
provably identical.

Examples
--------
    python plot_S_cdf.py --E 20
    python plot_S_cdf.py --E 18 --o 9
    python plot_S_cdf.py --E 20 --by-len 4 8 12 16
    python plot_S_cdf.py --E 28 --sample 300000 --out results/cdf_E28.png
"""

from __future__ import annotations

import argparse
import os
import sys
import random
from math import comb

import numpy as np


# --------------------------------------------------------------------------- #
# S(w) -- direct big-integer evaluation (matches lib/cocycle.py convention)    #
# --------------------------------------------------------------------------- #
def S_from_cuts(cuts, E):
    """S(w) for the word whose interior partial sums are `cuts` (sorted, in
    {1,...,E-1}); e = [0] + cuts, o = len(cuts)+1.  Returns a Python int."""
    e = (0,) + tuple(cuts)
    o = len(e)
    # S = sum_k 2^{e_k} 3^{o-1-k}, Horner in k from the front:
    s = 0
    for ek in e:
        s = 3 * s + (1 << ek)
    return s  # == sum 2^{e_k} 3^{o-1-k}


def _self_check():
    """Cross-check the direct formula against the sympy kernel."""
    here = os.path.dirname(os.path.abspath(__file__))
    libdir = os.path.join(here, "..", "cocycle-combine", "lib")
    sys.path.insert(0, libdir)
    try:
        import cocycle  # noqa: E402
    except Exception as exc:  # kernel optional; only used for the check
        print(f"[self-check skipped: could not import kernel: {exc}]")
        return
    rng = random.Random(0)
    for _ in range(200):
        o = rng.randint(1, 8)
        word = tuple(rng.randint(1, 5) for _ in range(o))
        E = sum(word)
        cuts = tuple(np.cumsum(word)[:-1].tolist())  # e_1..e_{o-1}
        mine = S_from_cuts(cuts, E)
        theirs = cocycle.S_int(word)
        assert mine == theirs, (word, mine, theirs)
    print("[self-check OK: direct S matches kernel on 200 random words]")


# --------------------------------------------------------------------------- #
# Exact enumeration of S over all words with |w| = E                           #
# --------------------------------------------------------------------------- #
def enumerate_all_o(E):
    """Yield S(w) for every composition of E (all lengths o = 1..E).

    Uses the cocycle recursion S(u.(d)) = 3 S(u) + 2^{|u|}: appending a letter
    bumps S the same way regardless of the letter's value (only |u| matters),
    so each prefix-state expands once and branches over the next gap length."""
    stack = [(0, 0)]  # (cumlen = |prefix|, S(prefix))
    while stack:
        cumlen, s = stack.pop()
        if cumlen == E:
            yield s
            continue
        new_s = 3 * s + (1 << cumlen)
        for d in range(1, E - cumlen + 1):
            stack.append((cumlen + d, new_s))


def enumerate_fixed_o(E, o):
    """Yield S(w) for every composition of E into exactly o positive parts."""
    target = E

    def rec(cumlen, s, parts_left):
        if parts_left == 0:
            if cumlen == target:
                yield s
            return
        new_s = 3 * s + (1 << cumlen)
        rem = target - cumlen
        # leave room for the remaining parts_left-1 parts (each >= 1)
        for d in range(1, rem - (parts_left - 1) + 1):
            yield from rec(cumlen + d, new_s, parts_left - 1)

    yield from rec(0, 0, o)


# --------------------------------------------------------------------------- #
# Random sampling (for E too large to enumerate)                               #
# --------------------------------------------------------------------------- #
def sample_all_o(E, n, rng):
    """n uniform random compositions of E (each interior cut flipped p=1/2)."""
    for _ in range(n):
        cuts = sorted(c for c in range(1, E) if rng.random() < 0.5)
        yield S_from_cuts(cuts, E)


def sample_fixed_o(E, o, n, rng):
    """n uniform random compositions of E into exactly o parts."""
    if o == 1:
        for _ in range(n):
            yield S_from_cuts((), E)  # the single word (E,) -> S = 1
        return
    for _ in range(n):
        cuts = sorted(rng.sample(range(1, E), o - 1))
        yield S_from_cuts(cuts, E)


# --------------------------------------------------------------------------- #
# Collect S values for one (E, o-or-None) stratum                             #
# --------------------------------------------------------------------------- #
def collect(E, o, max_exact, sample, rng):
    """Return (values: np.ndarray[float], exact: bool, total: int).

    total = exact population size; exact tells whether we enumerated it all."""
    if o is None:
        total = 1 << (E - 1)
        exact_gen = lambda: enumerate_all_o(E)
        sample_gen = lambda n: sample_all_o(E, n, rng)
    else:
        if not (1 <= o <= E):
            return np.array([], dtype=float), True, 0
        total = comb(E - 1, o - 1)
        exact_gen = lambda: enumerate_fixed_o(E, o)
        sample_gen = lambda n: sample_fixed_o(E, o, n, rng)

    if total <= max_exact:
        vals = np.fromiter((float(s) for s in exact_gen()), dtype=float)
        return vals, True, total
    n = sample if sample > 0 else min(max_exact, 300_000)
    n = min(n, total)
    vals = np.fromiter((float(s) for s in sample_gen(n)), dtype=float)
    return vals, False, total


def ecdf(values):
    """Sorted x and cumulative fraction y in (0,1]."""
    x = np.sort(values)
    y = np.arange(1, len(x) + 1) / len(x)
    return x, y


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(
        description="Empirical CDF of S(w) over words with |w| = E.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    ap.add_argument("--E", type=int, default=20, help="fixed gap-sum |w|")
    ap.add_argument("--o", type=int, default=None,
                    help="fix the length len(w)=o too (default: free)")
    ap.add_argument("--by-len", type=int, nargs="+", default=None,
                    help="draw one CDF per listed length o (overrides --o)")
    ap.add_argument("--max-exact", type=int, default=1_500_000,
                    help="enumerate exactly while population <= this, else sample")
    ap.add_argument("--sample", type=int, default=0,
                    help="sample size when sampling (0 = auto)")
    ap.add_argument("--linearx", action="store_true",
                    help="linear x-axis (default: log, S spans many orders)")
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--out", type=str, default=None, help="output PNG path")
    ap.add_argument("--show", action="store_true", help="also display the figure")
    args = ap.parse_args()

    _self_check()
    rng = random.Random(args.seed)

    import matplotlib
    if not args.show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(9, 6))

    if args.by_len:
        strata = [(o, f"o={o}") for o in args.by_len]
    elif args.o is not None:
        strata = [(args.o, f"o={args.o}")]
    else:
        strata = [(None, "all o")]

    print(f"\n|w| = E = {args.E}")
    print(f"{'stratum':>10} {'#words':>14} {'mode':>9} "
          f"{'min S':>16} {'median S':>18} {'max S':>20}")
    gmin = gmax = None  # global min/max of S over everything plotted
    for o, label in strata:
        vals, exact, total = collect(args.E, o, args.max_exact, args.sample, rng)
        if len(vals) == 0:
            print(f"{label:>10} {'0':>14}  (empty stratum, skipped)")
            continue
        x, y = ecdf(vals)
        mode = "exact" if exact else "sampled"
        suffix = "" if exact else f" (sampled {len(vals):,}/{total:,})"
        ax.plot(x, y, lw=1.6, label=f"{label}  [{mode}, N={total:,}]{suffix}"
                if not exact else f"{label}  [exact, N={total:,}]")
        vmin, vmax = int(vals.min()), int(vals.max())
        gmin = vmin if gmin is None else min(gmin, vmin)
        gmax = vmax if gmax is None else max(gmax, vmax)
        print(f"{label:>10} {total:>14,} {mode:>9} "
              f"{vmin:>16,} {int(np.median(vals)):>18,} {vmax:>20,}")

    # Red vertical lines at the global min and max S over the plotted data.
    if gmin is not None:
        for val, name, ha in ((gmin, "min", "left"), (gmax, "max", "right")):
            ax.axvline(val, color="red", lw=1.3, ls="--", alpha=0.85)
            ax.annotate(f"{name} S = {val:,}", xy=(val, 0.5),
                        xytext=(4 if ha == "left" else -4, 0),
                        textcoords="offset points", rotation=90,
                        va="center", ha=ha, color="red", fontsize=9)

    if not args.linearx:
        ax.set_xscale("log")
    ax.set_xlabel("S(w)")
    ax.set_ylabel("cumulative density  P[S <= x]")
    title = f"Empirical CDF of S(w),  |w| = E = {args.E}"
    if args.o is not None and not args.by_len:
        title += f",  len(w) = o = {args.o}"
    ax.set_title(title)
    ax.set_ylim(0, 1)
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="lower right", fontsize=9)
    fig.tight_layout()

    out = args.out
    if out is None:
        here = os.path.dirname(os.path.abspath(__file__))
        resdir = os.path.join(here, "results")
        os.makedirs(resdir, exist_ok=True)
        tag = f"E{args.E}"
        if args.by_len:
            tag += "_bylen"
        elif args.o is not None:
            tag += f"_o{args.o}"
        out = os.path.join(resdir, f"cdf_{tag}.png")
    fig.savefig(out, dpi=130)
    print(f"\nsaved: {out}")
    if args.show:
        plt.show()


if __name__ == "__main__":
    main()
