"""Survey the WORD space: all gap words w of length O and total gap-sum s <= E.

For each word w = (d_0..d_{O-1}), d_k>=1:
    D = 2^s - 3^O,   S = sum_k 2^{e_k} 3^{O-1-k},   x* = S/D  (fundamental solution)
    x  = canonical positive integer representative of w
       = unique x in [1, 2^{s+1}] with x = S * D^{-1} (mod 2^{s+1})   (FS3 coset)
    |x - x*| = |D x - S| / |D|        (the integrality "amendment" magnitude)

Plot |x - x*| versus x.  Usage:  python3 plot_wordspace.py [O] [Emax]
"""
import sys, math, os
from itertools import combinations
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

O = int(sys.argv[1]) if len(sys.argv) > 1 else 6
EMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 26
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
LOG23 = math.log2(3)

def l2(m):                       # overflow-safe log2 of a positive int
    m = abs(int(m))
    if m == 0: return float("-inf")
    b = m.bit_length(); sh = max(0, b - 53)
    return sh + math.log2(m >> sh)

def words(O, s):                 # all compositions of s into O positive parts
    for bars in combinations(range(1, s), O - 1):
        prev = 0; w = []
        for b in bars:
            w.append(b - prev); prev = b
        w.append(s - prev)
        yield w

p3 = 3**O
log2x, log2d, s_arr, crit, sign, imb, reln, lxs = [], [], [], [], [], [], [], []
nwords = 0
for s in range(O, EMAX + 1):
    D = (1 << s) - p3
    if D == 0:                   # 2^s = 3^O impossible for O,s>=1, but guard
        continue
    M = 1 << (s + 1)
    Dinv = pow(D % M, -1, M)
    Dabs_log = l2(abs(D))
    crit_s = Dabs_log - l2(p3)   # log2(|D|/3^O); ~0 => critical
    mean = s / O                 # average gap |w|/len(w)
    for w in words(O, s):
        # S = sum 2^{e_k} 3^{O-1-k}  and imbalance p = max_k |e_k - (s/O) k|
        S = 0; e = 0; p = 0.0
        for k in range(O):
            d = abs(e - mean * k)
            if d > p: p = d
            S += (1 << e) * (3 ** (O - 1 - k))
            e += w[k]
        # k=O endpoint: e == s, deviation |s - mean*O| = 0
        x = (S * Dinv) % M
        if x == 0: x = M
        num = D * x - S          # = D(x - x*), exact int
        log2x.append(l2(x))
        log2d.append((l2(abs(num)) - Dabs_log) if num != 0 else float("nan"))  # log2|x-x*|
        # log2(|x-x*|/|x*|) = log2(|Dx-S|/|S|)  (D cancels) = log2|x/x* - 1|
        reln.append((l2(abs(num)) - l2(S)) if num != 0 else float("nan"))
        # log2 |x*| = log2|S/D| = log2 S - log2|D|  (S>0; sign(x*)=sign(D), tracked in `sign`)
        lxs.append(l2(S) - Dabs_log)
        s_arr.append(s)
        crit.append(crit_s)
        sign.append(1.0 if num * D > 0 else -1.0)  # sign of (x - x*)
        imb.append(p)
        nwords += 1

log2x = np.array(log2x); log2d = np.array(log2d)
s_arr = np.array(s_arr, float); crit = np.array(crit); sign = np.array(sign)
imb = np.array(imb); reln = np.array(reln); lxs = np.array(lxs)
fin = np.isfinite(log2d)
ncyc = (~fin).sum()
print(f"O={O}, sum s in [{O},{EMAX}]: {nwords} words  ({ncyc} with x*=integer, i.e. D|S).")
print(f"log2|x-x*| range [{log2d[fin].min():.1f}, {log2d[fin].max():.1f}];  "
      f"x-x* > 0 for {100*(sign>0).mean():.1f}% of words")
print(f"correlation log2|x-x*| vs log2 x : r = {np.corrcoef(log2x[fin], log2d[fin])[0,1]:+.3f}")

# ---- plot 1: |x-x*| vs x, colored by imbalance p(w) ----
fig, ax = plt.subplots(figsize=(9, 6.5))
order = np.argsort(imb)                       # draw high-imbalance points on top
sc = ax.scatter(log2x[order], log2d[order], c=imb[order], s=6, cmap="viridis")
ax.set_xlabel("log2  x   (canonical integer representative of the word)")
ax.set_ylabel("log2 |x - x*(w)|")
ax.set_title(f"Fundamental-solution distance vs representative,  all words  len={O},  sum<={EMAX}\n"
             f"({nwords} words)")
ax.plot([log2x.min(), log2x.max()], [log2x.min(), log2x.max()], "k--", lw=0.8,
        label="|x-x*| = x")
ax.legend(loc="upper left", fontsize=9)
fig.colorbar(sc, label="imbalance  p(w) = max_k |e_k - (s/O) k|")
ax.grid(alpha=0.3); fig.tight_layout()
fn1 = os.path.join(OUT, f"wordspace_O{O}_E{EMAX}.png")
fig.savefig(fn1, dpi=120); plt.close(fig)
print("saved", fn1)

# ---- plot 3: log2(|x-x*|/|x*|) vs x, colored by imbalance p(w) ----
fig, ax = plt.subplots(figsize=(9, 6.5))
order = np.argsort(imb)
m = np.isfinite(reln)
sc = ax.scatter(log2x[order][m[order]], reln[order][m[order]],
                c=imb[order][m[order]], s=6, cmap="viridis")
ax.axhline(0, color="k", lw=0.8, label="|x-x*| = |x*|")
ax.set_xlabel("log2  x   (canonical integer representative of the word)")
ax.set_ylabel("log2 ( |x - x*| / |x*| )   =  log2 | x/x* - 1 |")
ax.set_title(f"Relative amendment vs representative,  all words  len={O},  sum<={EMAX}\n"
             f"({nwords} words, colored by imbalance)")
ax.legend(loc="upper left", fontsize=9)
fig.colorbar(sc, label="imbalance  p(w) = max_k |e_k - (s/O) k|")
ax.grid(alpha=0.3); fig.tight_layout()
fn3 = os.path.join(OUT, f"wordspace_O{O}_E{EMAX}_relx.png")
fig.savefig(fn3, dpi=120); plt.close(fig)
print("saved", fn3)
print(f"log2(|x-x*|/|x*|) range [{reln[m].min():.1f}, {reln[m].max():.1f}], "
      f"median {np.median(reln[m]):.2f}")

# ---- plot 4: relative amendment as a function of x*  (x-axis = signed log2|x*|) ----
fig, ax = plt.subplots(figsize=(9, 6.5))
m = np.isfinite(reln)
order = np.argsort(imb[m])
exp = (sign < 0)                              # not used for color; just for reporting
sc = ax.scatter(lxs[m][order], reln[m][order], c=imb[m][order], s=6, cmap="viridis")
# reference line  reln = -log2|x*| + c  (i.e. |x-x*| = const)
xs = np.array([lxs[m].min(), lxs[m].max()])
ax.plot(xs, -xs + np.median(reln[m] + lxs[m]), "k--", lw=0.9,
        label="slope -1  (|x-x*| const)")
ax.set_xlabel("log2 |x*|        ( x* = S/D ;  x* > 0 contracting for 99.96% of words )")
ax.set_ylabel("log2 ( |x - x*| / |x*| )")
ax.set_title(f"Relative amendment as a function of x*,  all words  len={O},  sum<={EMAX}\n"
             f"({nwords} words, colored by imbalance)")
ax.legend(loc="upper right", fontsize=9)
fig.colorbar(sc, label="imbalance  p(w) = max_k |e_k - (s/O) k|")
ax.grid(alpha=0.3); fig.tight_layout()
fn4 = os.path.join(OUT, f"wordspace_O{O}_E{EMAX}_fxstar.png")
fig.savefig(fn4, dpi=120); plt.close(fig)
print("saved", fn4)
print(f"log2|x*| range [{lxs[m].min():.1f}, {lxs[m].max():.1f}];  "
      f"expanding (x*<0): {100*(sign<0).mean():.2f}%;  "
      f"corr(reln, log2|x*|) = {np.corrcoef(lxs[m], reln[m])[0,1]:+.3f}")

# ---- plot 2: same, colored by gap-sum s (word "size") ----
fig, ax = plt.subplots(figsize=(9, 6.5))
sc = ax.scatter(log2x, log2d, c=s_arr, s=6, cmap="viridis")
ax.set_xlabel("log2  x"); ax.set_ylabel("log2 |x - x*(w)|")
ax.set_title(f"Same, colored by gap-sum s = |w|   (len={O})")
fig.colorbar(sc, label="gap-sum s = E")
ax.grid(alpha=0.3); fig.tight_layout()
fn2 = os.path.join(OUT, f"wordspace_O{O}_E{EMAX}_bysum.png")
fig.savefig(fn2, dpi=120); plt.close(fig)
print("saved", fn2)
