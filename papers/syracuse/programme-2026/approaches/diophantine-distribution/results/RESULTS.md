# Statistics: fundamental-solution position vs Collatz dynamics

Run: [`stats_collatz.py`](../stats_collatz.py) over **all 499,999 odd starts in $[3,10^6]$**
(even starts halve to an odd immediately and share the trajectory). Arrays in
[`stats.npz`](stats.npz); hexbin plots in this folder.

## What was measured

For each odd $x$ we walk the accelerated (odd-to-odd) Syracuse orbit to $1$ and attach two
finite words, with the fundamental-solution quantities of each (via the closed form
$\rho := (x-x_w^\ast)/2^{E} = (x-a_o)/D$, so no big sum $S$ is needed):

- **stopping word** — $x \to$ first odd $a_o \lt x$ (length = stopping time);
- **flying word** — $x \to a_o$ at the *last* index with $a_o \ge x$ (length = **flying time**,
  the pitch's $\max\{n: T^n(x)\ge x\}$). Defined for the 71% of starts with flying time $\ge1$.

Dynamics: flying time `fly`, stopping time `stop`, total steps to 1 `sig`, peak $\log_2(\max/x)$.

## Headline correlations (Spearman $\rho_s$)

| flying-word quantity | vs flying time | 
|---|---|
| $\log_2\lvert\rho\rvert$ (relative position) | $-0.976$ |
| imbalance $p$ | $+0.919$ |
| contraction rate $E/o$ | $+0.737$ |
| word halvings $E$ | $+0.989$ |

So **yes, the relative position of the fundamental solution is almost monotonically related
to flying time**: visually (`fly_vs_fabsrho.png`) flying time vs $\log_2\lvert\rho\rvert$ is a
single tight downward band. Imbalance rises with flight (`fly_vs_fimb.png`). For the stopping
word the same holds against stopping time ($\rho_s=-0.80$ for relpos, $+0.91$ for imbalance).

## The crucial caveat — the correlation is largely *mechanical*

The flying word is, by construction, **longer** for longer flights: $E$ (halvings) has
$\rho_s=+0.989$ with flying time. Both headline quantities are functions of $E$:
$\log_2\lvert\rho\rvert = \log_2\lvert x-x_w^\ast\rvert - E$, and imbalance $p$ grows like a
random-walk excursion $\sim\sqrt{E}$. Removing $E$ collapses the signal:

| quantity | raw $\rho_s$ vs fly | **partial $\rho_s$ given $E$** |
|---|---|---|
| $\log_2\lvert\rho\rvert$ | $-0.976$ | $\mathbf{-0.160}$ |
| imbalance $p$ | $+0.919$ | $\mathbf{-0.126}$ |
| contraction rate $E/o$ | $+0.737$ | $\mathbf{-0.393}$ |

And the **numerator alone is flat**: median $\log_2\lvert x-x_w^\ast\rvert \approx 18.9$
across every flying-time bucket (fly $\in[1,3]$ up to $[16,31]$), i.e. $\lvert x-x_w^\ast\rvert
\sim x$ regardless of how long $x$ flies. **Long-flying integers are *not* anomalously close
to their fundamental solution in absolute terms** — the strong $\rho$-correlation is carried
almost entirely by the $2^{E}$ normalization, which is itself ~definitional for flight length.

## What genuinely survives

- **Contraction rate / criticality.** $E/o$ keeps a real (partial $-0.393$) link to flight:
  controlling for word length, longer-flying words sit at smaller $E/o$, i.e. **nearer the
  critical line $E/o = \log_2 3 \approx 1.585$** (near-expanding). This matches the program's
  regime-3 intuition that long flights live near criticality. (Flying words are $99.99\%$
  expanding, $D\lt0$; stopping words $100\%$ contracting, $D\gt0$ — both as expected.)

## Per-trajectory view: $x-x^\ast(w_n(x))$ vs prefix length $n$

[`plot_relpos_trajectory.py`](../plot_relpos_trajectory.py) → `relpos_trajectory.png`. For
fixed $x$, growing the prefix word $w_n$ step by step, $x-x^\ast(w_n)=2^{E_n}(x-a_n)/D_n$ is
**essentially flat at $\log_2|x-x^\ast|\approx\log_2 x$** for the whole orbit (e.g. $x=703$:
slog$_2\approx9.45$ constant over 62 steps) — i.e. $x^\ast(w_n)$ stays small relative to $x$
almost everywhere, reconfirming $|x-x^\ast|\sim x$. The exceptions are **sparse upward
spikes** at **near-critical prefixes**: for $x=871$ the jump to slog$_2=14.2$ at $n=53$ has
$E_n/n=1.585=\log_2 3$ and $|D_n|\approx2^{75}$ sitting $\sim2^{9}$ below the generic
$2^{E_n}=2^{84}$, inflating $x-x^\ast$ by that factor. So the fundamental solution only departs
from "$\approx x$" exactly when the prefix word is critical ($D_n$ anomalously small).

## Word-space view: $|x-x^\ast|$ vs $x$ over all words of fixed length

[`plot_wordspace.py`](../plot_wordspace.py) `O Emax` → `wordspace_O{O}_E{Emax}.png`. Enumerates
**every** gap word of length $O$ with gap-sum $s\le E_{\max}$, takes the canonical positive
integer representative $x\equiv S D^{-1}\pmod{2^{s+1}}$ of each, and plots $|x-x^\ast|=|Dx-S|/|D|$.

Result ($O=6$, $s\le26$, 230,230 words): points lie **exactly on $|x-x^\ast|=x$** ($r=1.000$
between $\log_2|x-x^\ast|$ and $\log_2 x$); $x>x^\ast$ for 100%; exactly one word has
$x^\ast\in\mathbb{Z}$ ($D\mid S$). So $x^\ast\ll x$ for the minimal representative — the
fundamental solution carries almost no information about *which* integer realizes the word
(the realizing integer is ~uniform in its $2^{s+1}$-cell). Colored by imbalance
$p(w)=\max_k|e_k-\tfrac{s}{O}k|$: $p$ appears as a **gradient along the diagonal** (low $p$ at
small $x$, high $p$ at large $x$), i.e. for fixed $O$ the imbalance just tracks the gap-sum $s$
(longer path ⇒ larger excursions ⇒ larger representative), not an independent lever on the
$|x-x^\ast|$-vs-$x$ law. The faint sub-diagonal points are all low-imbalance.

## Reading for the program

The notion of "relative position" $\rho=(x-x^\ast)/2^{E}$ is dominated by $E$ and so mostly
re-encodes flight length; it is **not** by itself evidence that integers shadow their
fundamental solution. The quantity with non-trivial predictive content is the **criticality
$E/o$** of the word. Any quantitative use of the fundamental solution for the flying-time
program should therefore work with $E$-residualized statistics, or directly with $D=2^E-3^o$
near-criticality, rather than with $\rho$ at face value.
