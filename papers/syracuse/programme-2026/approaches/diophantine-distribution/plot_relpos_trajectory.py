"""Plot  x - x*(w_n(x))  vs n, where w_n(x) is the length-n parity (gap) word of x
(first n accelerated odd steps) and x*(w) = S(w)/D(w) is its fundamental solution.

Closed form (exact, from FS1):  x - x*(w_n) = 2^{E_n} (x - a_n) / D_n,
with a_n = n-th odd term, E_n = cumulative halvings, D_n = 2^{E_n} - 3^n.

Values span a huge range, so we plot signed log2:  slog2(y) = sign(y)*log2(1+|y|).
Usage:  python3 plot_relpos_trajectory.py [x1 x2 ...]
"""
import sys, math, os
from fractions import Fraction
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)

def l2(m):                       # log2 of a big non-negative int, overflow-safe
    m = abs(int(m))
    if m == 0:
        return float("-inf")
    b = m.bit_length()
    sh = max(0, b - 53)
    return sh + math.log2(m >> sh)

def slog2(fr):                   # signed log2(1+|fr|) for a Fraction fr
    if fr == 0:
        return 0.0
    s = 1.0 if fr > 0 else -1.0
    num, den = abs(fr.numerator), fr.denominator
    # log2(1+|fr|) ; |fr| huge -> ~ log2|fr|, small -> ~|fr|/ln2
    if num >= den:
        return s * (l2(num + den) - l2(den))
    return s * math.log2(1 + num / den)

def series(x):
    cur = x; e = 0; n = 0
    ns, ys, a = [], [], []
    stop = fly = None
    while cur != 1 and n < 2000:
        t = 3 * cur + 1
        v = (t & -t).bit_length() - 1
        t >>= v
        cur = t; n += 1; e += v
        D = (1 << e) - 3**n
        y = Fraction((1 << e) * (x - cur), D)        # = x - x*(w_n)
        ns.append(n); ys.append(slog2(y)); a.append(cur)
        if stop is None and cur < x: stop = n
        if cur >= x: fly = n
    return ns, ys, stop, fly

seeds = [int(s) for s in sys.argv[1:]] or [27, 703, 871, 6171, 77031]

fig, ax = plt.subplots(figsize=(10, 6))
for x in seeds:
    ns, ys, stop, fly = series(x)
    line, = ax.plot(ns, ys, lw=1.1, marker=".", ms=3,
                    label=f"x={x}  (stop@{stop}, fly@{fly}, len {ns[-1]})")
    if stop: ax.axvline(stop, color=line.get_color(), ls=":", lw=0.7, alpha=0.5)

ax.axhline(0, color="k", lw=0.6)
ax.set_xlabel("n  (number of odd / accelerated steps)")
ax.set_ylabel(r"signed $\log_2(1+|x-x^*(w_n)|)$")
ax.set_title("Relative position  x - x*(w_n(x))  of the fundamental solution vs prefix length n")
ax.legend(fontsize=8, loc="upper left")
ax.grid(alpha=0.3)
fig.tight_layout()
fn = os.path.join(OUT, "relpos_trajectory.png")
fig.savefig(fn, dpi=120)
print("saved", fn)
for x in seeds:
    ns, ys, stop, fly = series(x)
    print(f"  x={x}: len={ns[-1]}  stop@{stop}  fly@{fly}  "
          f"slog2 range [{min(ys):.1f},{max(ys):.1f}]")
