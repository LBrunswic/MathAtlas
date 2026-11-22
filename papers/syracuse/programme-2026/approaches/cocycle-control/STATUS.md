# Status — cocycle-control

## Current state

Active — sub-goal 1 (statistics) has a working tool: [`plot_S_cdf.py`](plot_S_cdf.py) plots the
empirical CDF of $S(w)$ at fixed $|w|=E$ (x = $S(w)$, y = cumulative density), either across all
lengths or split per $\operatorname{len}(w)=o$. First sweep at $E=20$ done; first range/extremal
observations in hand (below). Monotone-move / lattice (sub-goals 2,3) not yet attacked.

## Results

- **CDF tool ([`plot_S_cdf.py`](plot_S_cdf.py)).** Enumerates the compositions of $E$ exactly
  while the population ($2^{E-1}$, or $\binom{E-1}{o-1}$ at fixed $o$) stays under `--max-exact`,
  else uniform-samples; computes $S$ with Python big-ints (cross-checked against
  [`cocycle.S_int`](../cocycle-combine/lib/cocycle.py) on startup) via the cocycle recursion
  $S(u\!\cdot\!(d))=3S(u)+2^{|u|}$. Flags: `--E`, `--o`, `--by-len`, `--sample`, `--linearx`,
  `--out`, `--show`. Outputs in [`results/`](results/).
- **First sweep, $E=20$ ([`results/cdf_E20.png`](results/cdf_E20.png), [`results/cdf_E20_bylen.png`](results/cdf_E20_bylen.png)).**
  All $524{,}288$ words enumerated exactly. Combined CDF is a clean sigmoid on a log-$S$ axis,
  $S$ spanning $1$ to $\sim3.5\times10^9$.
- **Observed range at fixed $|w|=E$ (numeric, $E=20$; not yet proved).** $\min_w S=1$ at the
  single-letter word $(E)$; $\max_w S=3^E-2^E$ ($=3{,}485{,}735{,}825$ for $E=20$, $=|D|$) at the
  all-ones circuit word $1^E$ ($o=E$). Matches the rationale's "gap-mass early/long word $\Rightarrow$
  large $S$" intuition and is a candidate theorem for sub-goals 2–3.
- **Observed: length dominates magnitude (numeric, $E=20$).** The per-$o$ CDFs are tight,
  near-disjoint bands sliding monotonically rightward as $o$ grows (medians $\approx10^3\to10^8$
  for $o=2\to17$); within a fixed $(E,o)$ stratum the spread of $S$ is comparatively narrow.
- **Rotation-range CDF tool ([`plot_S_rotrange_cdf.py`](plot_S_rotrange_cdf.py)).** One sample
  per *cycle* (cyclic word / necklace, deduped by min rotation); x-value is the spread of the
  rotation sums $R(w)=\max_j S^{(j)}-\min_j S^{(j)}$ — the quantity bounding the
  `cocycle-combine` cores ($\gcd_j S^{(j)}=|D|$ on a cycle, so $R\ge|D|$ there). Reports
  $P[R=0]$ (the rotation-invariant / degenerate $C=0$ locus: constant words $d^o$ and $o=1$);
  symlog axis when zeros are present, log otherwise. Same exact-or-sample + kernel cross-check.
- **First rotation-range sweep, $E=20,\,o=13$ ([`results/rotrange_cdf_E20_o13.png`](results/rotrange_cdf_E20_o13.png)).**
  All $3{,}876$ cycles. $R$ spans $3{,}770{,}158$ to $133{,}945{,}630$ (median $1.59\times10^7$),
  $P[R=0]=0$ (no constant word: $13\nmid20$). For reference $|D|=|2^{20}-3^{13}|=545{,}747$, so
  every cycle here has $R\approx7\times|D|$ to $245\times|D|$ — consistent with $R\ge|D|$ and a
  candidate angle for an a-priori core ceiling. *(Note: $(20,13)$ is the negative side
  $2^E\lt3^o$; the critical positive side for $o=13$ is $E=21$ — see next.)*
- **Critical-$E$ word/cycle-class API ([`critical_words.py`](critical_words.py)).** Keyed on
  $o$: `critical_E(o)=ceil(o\log_2 3)=(3^o)`.bit_length() (smallest $E$ with $2^E\gt3^o$, minimal
  positive $D$); `critical_words(o)` (all $\binom{E-1}{o-1}$ words), `critical_cycle_classes(o)`
  (one per necklace), `critical_extremes_by_range(o,k=100)` (top/bottom-$k$ classes by cycle range
  $R$, heaps + dedup; exact under `--max-exact`, else uniform-samples classes). Kernel-checked.
- **Range extremes are structured (numeric, $o=13$, critical $E=21$, $|D|=502{,}829$, 9,690 classes).**
  - **Max-range cycles = single-defect circuits.** Top by $R$ are $(1^{o-1}$ with one big gap$)$,
    e.g. $(1^{12},9)$ at $R\approx535\,|D|$ — exactly `cocycle-combine`'s **P2 family**
    ($d^aed^b$, $d=1$): concentrated gap-mass $\Rightarrow$ widest rotation-sum spread.
  - **Min-range cycles = balanced words.** Bottom by $R$ are the flattest profiles, alternating
    1s and 2s (e.g. $(1,2,1,2,2,1,2,1,2,2,1,2,2)$) at $R\approx10.5\,|D|$ — the
    `diophantine-distribution` balanced-word regime ($p=\max_k|e_k-\tfrac{E}{o}k|$ minimized).
  - **Floor.** $\min_{\text{classes}}R\approx10\,|D|$ here; the *floor* of $R/|D|$ over classes is
    the cycle-relevant quantity (an a-priori lower bound on $R$ would cap the cores).
- **Extremes tables, $o=10\ldots16$ ([`results/extremes/`](results/extremes/): `TOP_<o>.md`,
  `BOTTOM_<o>.md`, top/bottom 100 each by $R$; driver [`write_extremes.py`](write_extremes.py)).**
  All exact. Floor/ceiling of $R/|D|$ over cycle classes:

  | $o$ | crit $E$ | #classes | $\min R/|D|$ | $\max R/|D|$ |
  |---:|---:|---:|---:|---:|
  | 10 | 16 | 504 | 18.31 | 372 |
  | 11 | 18 | 1,768 | 6.13 | 173 |
  | 12 | 20 | 6,310 | **2.80** | 173 |
  | 13 | 21 | 9,690 | 10.49 | 535 |
  | 14 | 23 | 35,530 | 5.57 | 450 |
  | 15 | 24 | 54,484 | 18.31 | 2006 |
  | 16 | 26 | 204,347 | 7.55 | 1217 |

  - **Max end is always P2** (single-defect circuit $(1^{o-1},\text{big gap})$).
  - **Min end is a periodic/balanced word**, and the global-low floor $o=12$, $R/|D|=2.80$ is the
    *exactly periodic* $w=(1,2,2)^4$ ($E/o=20/12=5/3\leftrightarrow(1,2,2)$) — i.e. the range
    floor is hit by `cocycle-combine`'s **P0** seed family $w^q$. Floor is non-monotonic in $o$,
    dipping when crit $E/o$ admits a short clean periodic pattern.

## Dead ends

- _(none yet)_

## Open questions

- **Statistics (sub-goal 1).** Over words with $|w|=E$ fixed, what is the distribution of
  $S(w)$ — min, max, spread, shape — and how do these scale with $E$ and with
  $\operatorname{len}(w)=o$? Should $\operatorname{len}(w)$ be held fixed too, or swept?
- **Monotone moves (sub-goal 2).** Which elementary transformations preserve both $|w|$ and
  $\operatorname{len}(w)$ while provably moving $S$ one way? (Candidate to test: transfer one
  unit of gap from a later position to an earlier one, $d_i\!\to\!d_i\!+\!1$,
  $d_j\!\to\!d_j\!-\!1$ with $i\lt j$.)
- **Lattice (sub-goal 3).** Is the componentwise order on partial-sum vectors
  $(e_1,\dots,e_{o-1})$ a lattice, and is $S$ provably monotone for it? What are the
  top/bottom elements (the $\arg\max/\arg\min$ of $S$ at fixed $(E,o)$)?
- **Payoff.** Once extremal words are identified, what sharp $\min/\max S$ bounds do they give,
  and how do those feed back into the cycle bound $a_0=S/D$ and the
  [`diophantine-distribution`](../diophantine-distribution/RATIONALE.md) imbalance $\eta$?

## Next step under consideration

Awaiting the user's direction — likely either (a) a first statistical sweep of $S(w)$ at fixed
$|w|$ using the existing kernel, or (b) a direct attack on the monotone-move / lattice claim.
