"""Statistics: relative position of the fundamental solution vs Collatz dynamics.

For every odd start x in [3, N], walk the accelerated (odd-to-odd) Syracuse trajectory
to 1, recording:

  dynamical
    sig   = total stopping time to 1, in ODD steps  (len of full word to 1)
    fly   = flying time = max{ n : a_n >= x } in odd steps   (pitch's def)
    stop  = first-descent time = min{ n : a_n < x } in odd steps  (classic)
    lmax  = log2(max term / x)        (peak excursion)

  fundamental solution of the STOPPING word w (x -> first odd a_stop < x):
    E,o   = |w|, len(w);   D = 2^E - 3^o   (should be > 0: net contraction)
    rho   = (x - x*)/2^E  = (x - a_stop)/D        relative position (FS closed form)
    xsx   = x*/x          where x* = x - 2^E * rho                (x* = S/D)
    imb   = imbalance p = max_k |e_k - (E/o) k|
    eo    = E/o  ( = log2 beta;  contracting iff eo > log2 3 )

Then: Pearson + Spearman correlations between the FS quantities and the dynamics,
binned tables, and (if matplotlib present) scatter/hexbin plots in results/.
"""
import sys, math, os
import numpy as np

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
LOG23 = math.log2(3)

def fs_of_word(x, a_o, E, o, gaps_prefix):
    """fundamental-solution metrics of the word x->a_o (E halvings, o odd steps)."""
    D = (1 << E) - 3**o
    rho = (x - a_o) / D                    # = (x - x*)/2^E   (closed form)
    xstar = x - (2.0**E) * rho             # = S/D
    mean = E / o
    e_k = 0; imb = 0.0
    for k in range(o):
        d = abs(e_k - mean*k)
        if d > imb: imb = d
        e_k += gaps_prefix[k]
    imb = max(imb, abs(e_k - mean*o))      # k=o endpoint (=0)
    return D, rho, xstar, xstar/x, imb, E/o

def metrics(x):
    cur = x
    e = 0; o = 0
    gaps = []
    stop = None                            # (o,E,a) at first descent below x
    fly_o = 0; fly_E = 0; fly_a = x        # last odd index with a_o >= x
    maxv = x
    while cur != 1:
        t = 3*cur + 1
        v = (t & -t).bit_length() - 1
        t >>= v
        cur = t; o += 1; e += v; gaps.append(v)
        if cur > maxv: maxv = cur
        if cur >= x:
            fly_o, fly_E, fly_a = o, e, cur
        if stop is None and cur < x:
            stop = (o, e, cur)
    sig = o
    so, sE, sa = stop
    sD, srho, sxs_abs, sxsx, simb, seo = fs_of_word(x, sa, sE, so, gaps)
    # flying word (x .. a_fly), defined only if fly_o >= 1
    if fly_o >= 1:
        fD, frho, fx, fxsx, fimb, feo = fs_of_word(x, fly_a, fly_E, fly_o, gaps)
    else:
        fD = frho = fx = fxsx = fimb = feo = float("nan")
    return (sig, fly_o, so, math.log2(maxv / x),
            sE, so, sD, srho, sxsx, simb, seo,           # stopping word FS
            fly_E, frho, fxsx, fimb, feo)                # flying word FS

cols = ["sig", "fly", "stop", "lmax",
        "E", "o", "D", "rho", "xsx", "imb", "eo",
        "fE", "frho", "fxsx", "fimb", "feo"]
data = {c: [] for c in cols}

step = max(1, (N // 20))
for x in range(3, N + 1, 2):
    if (x % step) < 2:
        print(f"  ... x={x}", file=sys.stderr)
    vals = metrics(x)
    for c, val in zip(cols, vals):
        data[c].append(val)

A = {c: np.asarray(data[c], dtype=float) for c in cols}
n = len(A["sig"])
print(f"\nProcessed {n} odd starts in [3,{N}].")

# derived
A["absrho"] = np.log2(np.abs(A["rho"]) + 1e-12)
A["fabsrho"] = np.log2(np.abs(A["frho"]) + 1e-12)
print(f"stopping words contracting (E/o > log2 3): {(A['eo']>LOG23).mean()*100:.2f}%  "
      f"(stop D>0: {(A['D']>0).mean()*100:.2f}%)")
fly_def = np.isfinite(A["frho"])
print(f"flying words contracting: {(A['feo'][fly_def]>LOG23).mean()*100:.2f}%   "
      f"(fly>=1 defined: {fly_def.mean()*100:.2f}% of starts)")

def rank(v):
    order = v.argsort(); r = np.empty_like(order, dtype=float)
    r[order] = np.arange(len(v)); return r

def corr(a, b):
    m = np.isfinite(a) & np.isfinite(b)
    a, b = a[m], b[m]
    pear = np.corrcoef(a, b)[0, 1]
    spear = np.corrcoef(rank(a), rank(b))[0, 1]
    return pear, spear

fs_vars = ["absrho", "imb", "eo", "E", "fabsrho", "fimb", "feo", "fE"]
dyn_vars = ["fly", "stop", "sig", "lmax"]
print("\nPearson / Spearman correlation  (FS quantity  vs  dynamics):")
hdr = "  " + "FS\\dyn".ljust(10) + "".join(d.rjust(18) for d in dyn_vars)
print(hdr)
for f in fs_vars:
    row = "  " + f.ljust(10)
    for d in dyn_vars:
        p, s = corr(A[f], A[d])
        row += f"{p:+.3f}/{s:+.3f}".rjust(18)
    print(row)

# binned: relative-position metrics by flying-time bucket
print("\nMean FS quantities by flying-time (odd steps) bucket:")
fly = A["fly"]
buckets = [(0,0),(1,1),(2,3),(4,7),(8,15),(16,31),(32,10**9)]
print("  flybucket    count     mean|rho|(log2)   mean xsx     mean imb    mean E/o")
for lo, hi in buckets:
    m = (fly >= lo) & (fly <= hi)
    if m.sum() == 0: continue
    print(f"  [{lo:>3},{hi if hi<10**9 else 'inf':>4}]  {m.sum():>8}   "
          f"{A['absrho'][m].mean():>10.2f}     {A['xsx'][m].mean():>9.3f}   "
          f"{A['imb'][m].mean():>9.3f}   {A['eo'][m].mean():>8.3f}")

# save raw arrays for further analysis
np.savez_compressed(os.path.join(OUT, "stats.npz"),
                    **{c: A[c] for c in cols + ["absrho", "fabsrho"]})
print(f"\nSaved arrays -> {os.path.join(OUT,'stats.npz')}")

# plots
try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    def hexb(xk, yk, fn, xl, yl):
        fig, ax = plt.subplots(figsize=(6,5))
        hb = ax.hexbin(A[xk], A[yk], gridsize=60, mincnt=1, bins="log", cmap="viridis")
        ax.set_xlabel(xl); ax.set_ylabel(yl)
        p, s = corr(A[xk], A[yk])
        ax.set_title(f"{yl} vs {xl}   r={p:+.3f}  rho_s={s:+.3f}")
        fig.colorbar(hb, label="log10 count"); fig.tight_layout()
        fig.savefig(os.path.join(OUT, fn), dpi=110); plt.close(fig)
    hexb("fabsrho", "fly", "fly_vs_fabsrho.png", "log2 |relpos rho| (flying word)", "flying time")
    hexb("fimb", "fly", "fly_vs_fimb.png", "imbalance p (flying word)", "flying time")
    hexb("feo", "fly", "fly_vs_feo.png", "E/o (flying word)", "flying time")
    hexb("absrho", "stop", "stop_vs_absrho.png", "log2 |relpos rho| (stopping word)", "stopping time")
    print(f"Saved plots -> {OUT}/*.png")
except Exception as ex:
    print("matplotlib unavailable, skipped plots:", ex)
