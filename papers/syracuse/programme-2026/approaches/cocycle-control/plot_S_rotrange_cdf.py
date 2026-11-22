#!/usr/bin/env python3
"""Empirical CDF of the rotation-sum range R(w) over cycles (cyclic words).

A "cycle" here is a gap word taken up to cyclic rotation (a necklace) -- exactly
the cycle-gcd / cocycle-combine notion, where a Collatz cycle's gap word is read
cyclically.  For a cyclic word w of length o, let S^{(j)} = S(rotate(w, j)) be the
rotation sums (j = 0..o-1); the sample's x-value is their *range*

    R(w) = max_j S^{(j)} - min_j S^{(j)}.

Each cyclic-equivalence class contributes one sample (we dedupe linear
compositions by their lexicographically-minimal rotation).  The plot is the
empirical CDF of R: x = R(w), y = cumulative fraction of cycles with R <= x.

Why R matters: differences of rotation sums are the compensation "cores"
(S^{(i)}-S^{(j)}); on a genuine cycle gcd_j S^{(j)} = |D| = |2^E-3^o|, so the
spread of the S^{(j)} bounds how large those cores can be.  R = 0 exactly for
rotation-invariant words (the circuit d^o and o=1) -- the degenerate C=0 locus;
the script reports P[R=0] and plots R on a symlog axis so the zeros are visible.

Like plot_S_cdf.py, enumeration is exact while the population stays under
--max-exact, else it uniform-samples linear words (each sample = its cycle;
slight orbit-size weighting, noted on stdout).  S is computed with big-ints via
the cocycle recursion and cross-checked against the sympy kernel on startup.

Examples
--------
    python plot_S_rotrange_cdf.py --E 20 --o 13
    python plot_S_rotrange_cdf.py --E 20            # all lengths
    python plot_S_rotrange_cdf.py --E 28 --o 18 --sample 200000
"""

from __future__ import annotations

import argparse
import os
import sys
import random
from math import comb

import numpy as np


# --------------------------------------------------------------------------- #
# S(w) and the rotation-range metric (big-int, kernel convention)             #
# --------------------------------------------------------------------------- #
def S_word(word):
    """S(w) = sum_k 2^{e_k} 3^{o-1-k} via the cocycle recursion
    S(u.(d)) = 3 S(u) + 2^{|u|}.  Returns a Python int."""
    s = 0
    cum = 0
    for d in word:
        s = 3 * s + (1 << cum)
        cum += d
    return s


def rot_range(word):
    """max_j S(rotate(w,j)) - min_j S(rotate(w,j))."""
    o = len(word)
    vals = [S_word(word[j:] + word[:j]) for j in range(o)]
    return max(vals) - min(vals)


def canonical(word):
    """Lexicographically minimal rotation -- the necklace representative."""
    o = len(word)
    return min(word[j:] + word[:j] for j in range(o))


def _self_check():
    """Cross-check S_word / rot_range against the sympy kernel."""
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.join(here, "..", "cocycle-combine", "lib"))
    try:
        import cocycle  # noqa: E402
    except Exception as exc:
        print(f"[self-check skipped: could not import kernel: {exc}]")
        return
    rng = random.Random(0)
    for _ in range(200):
        word = tuple(rng.randint(1, 5) for _ in range(rng.randint(1, 8)))
        assert S_word(word) == cocycle.S_int(word), word
        kr = [cocycle.S_int(cocycle.rotate(word, j)) for j in range(len(word))]
        assert rot_range(word) == max(kr) - min(kr), word
    print("[self-check OK: S_word & rot_range match kernel on 200 random words]")


# --------------------------------------------------------------------------- #
# Enumerate / sample cyclic words (necklaces) and their ranges                 #
# --------------------------------------------------------------------------- #
def gen_words_all_o(E):
    """Every composition of E (all lengths) as a tuple."""
    def rec(prefix, rem):
        if rem == 0:
            yield tuple(prefix)
            return
        for d in range(1, rem + 1):
            prefix.append(d)
            yield from rec(prefix, rem - d)
            prefix.pop()
    yield from rec([], E)


def gen_words_fixed_o(E, o):
    """Every composition of E into exactly o positive parts as a tuple."""
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


def random_word_all_o(E, rng):
    cuts = sorted(c for c in range(1, E) if rng.random() < 0.5)
    bounds = [0] + cuts + [E]
    return tuple(bounds[i + 1] - bounds[i] for i in range(len(bounds) - 1))


def random_word_fixed_o(E, o, rng):
    if o == 1:
        return (E,)
    cuts = sorted(rng.sample(range(1, E), o - 1))
    bounds = [0] + cuts + [E]
    return tuple(bounds[i + 1] - bounds[i] for i in range(o))


def collect_ranges(E, o, max_exact, sample, rng):
    """Return (ranges: np.ndarray[float], exact: bool, n_cycles: int, n_lin: int).

    One entry per cyclic-equivalence class (deduped by canonical rotation)."""
    if o is None:
        n_lin = 1 << (E - 1)
        words = gen_words_all_o(E)
        rand = lambda: random_word_all_o(E, rng)
    else:
        if not (1 <= o <= E):
            return np.array([], float), True, 0, 0
        n_lin = comb(E - 1, o - 1)
        words = gen_words_fixed_o(E, o)
        rand = lambda: random_word_fixed_o(E, o, rng)

    seen = {}
    if n_lin <= max_exact:
        for w in words:
            c = canonical(w)
            if c not in seen:
                seen[c] = rot_range(c)
        return (np.fromiter((float(v) for v in seen.values()), float),
                True, len(seen), n_lin)

    # sample: draw linear words, dedupe what collides; each kept = one cycle
    target = sample if sample > 0 else min(max_exact, 200_000)
    attempts = 0
    while len(seen) < target and attempts < target * 4:
        attempts += 1
        c = canonical(rand())
        if c not in seen:
            seen[c] = rot_range(c)
    return (np.fromiter((float(v) for v in seen.values()), float),
            False, len(seen), n_lin)


def ecdf(values):
    x = np.sort(values)
    y = np.arange(1, len(x) + 1) / len(x)
    return x, y


# --------------------------------------------------------------------------- #
# Main                                                                         #
# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(
        description="Empirical CDF of the rotation-sum range R(w) over cycles.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    ap.add_argument("--E", type=int, default=20, help="fixed gap-sum |w|")
    ap.add_argument("--o", type=int, default=13,
                    help="fixed length len(w)=o (use --all-o to free it)")
    ap.add_argument("--all-o", action="store_true",
                    help="let the length vary (overrides --o)")
    ap.add_argument("--by-len", type=int, nargs="+", default=None,
                    help="draw one CDF per listed length o")
    ap.add_argument("--max-exact", type=int, default=4_000_000,
                    help="enumerate exactly while #linear-words <= this, else sample")
    ap.add_argument("--sample", type=int, default=0, help="#cycles to sample (0=auto)")
    ap.add_argument("--linearx", action="store_true", help="linear x (default: symlog)")
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--show", action="store_true")
    args = ap.parse_args()

    _self_check()
    rng = random.Random(args.seed)

    import matplotlib
    if not args.show:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if args.by_len:
        strata = [(o, f"o={o}") for o in args.by_len]
    elif args.all_o:
        strata = [(None, "all o")]
    else:
        strata = [(args.o, f"o={args.o}")]

    fig, ax = plt.subplots(figsize=(9, 6))
    print(f"\n|w| = E = {args.E}   metric: R(w) = max_j S^(j) - min_j S^(j)")
    print(f"{'stratum':>9} {'#cycles':>12} {'mode':>8} {'P[R=0]':>8} "
          f"{'min R':>14} {'median R':>16} {'max R':>18}")
    gmin = gmax = None
    any_zero = False
    for o, label in strata:
        R, exact, ncyc, nlin = collect_ranges(
            args.E, o, args.max_exact, args.sample, rng)
        if len(R) == 0:
            print(f"{label:>9} {'0':>12}  (empty stratum, skipped)")
            continue
        p0 = float(np.mean(R == 0))
        any_zero = any_zero or p0 > 0
        x, y = ecdf(R)
        mode = "exact" if exact else "sampled"
        lab = (f"{label}  [exact, {ncyc:,} cycles]" if exact else
               f"{label}  [sampled {ncyc:,} of {nlin:,} lin.]")
        ax.plot(x, y, lw=1.6, label=lab)
        vmin, vmax = int(R.min()), int(R.max())
        gmin = vmin if gmin is None else min(gmin, vmin)
        gmax = vmax if gmax is None else max(gmax, vmax)
        print(f"{label:>9} {ncyc:>12,} {mode:>8} {p0:>8.4f} "
              f"{vmin:>14,} {int(np.median(R)):>16,} {vmax:>18,}")

    if gmin is not None:
        for val, name, ha in ((gmin, "min", "left"), (gmax, "max", "right")):
            ax.axvline(val, color="red", lw=1.3, ls="--", alpha=0.85)
            ax.annotate(f"{name} R = {val:,}", xy=(val, 0.5),
                        xytext=(4 if ha == "left" else -4, 0),
                        textcoords="offset points", rotation=90,
                        va="center", ha=ha, color="red", fontsize=9)

    if not args.linearx:
        if any_zero:
            ax.set_xscale("symlog", linthresh=1)  # shows R = 0 too
            ax.set_xlim(left=0)                    # R >= 0: hide the negative half
        else:
            ax.set_xscale("log")
    ax.set_xlabel("rotation-sum range  R(w) = max_j S^(j) - min_j S^(j)")
    ax.set_ylabel("cumulative density  P[R <= x]")
    title = f"Empirical CDF of rotation-sum range over cycles,  |w| = E = {args.E}"
    if not args.all_o and not args.by_len:
        title += f",  o = {args.o}"
    ax.set_title(title, fontsize=11)
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
        tag += "_bylen" if args.by_len else ("_allo" if args.all_o else f"_o{args.o}")
        out = os.path.join(resdir, f"rotrange_cdf_{tag}.png")
    fig.savefig(out, dpi=130)
    print(f"\nsaved: {out}")
    if args.show:
        plt.show()


if __name__ == "__main__":
    main()
