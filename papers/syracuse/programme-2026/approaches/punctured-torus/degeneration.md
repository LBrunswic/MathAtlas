# Mapping the degeneration locus — where the arithmetic does (and doesn't) show

**Certified by** [`degeneration.py`](degeneration.py). Probes the wall on which the Syracuse
cocycle sits (critically improper, [`properness.md`](properness.md)).

## Setup

Anchor at the reducible base (diagonal $2$–$3$ skeleton), where every Margulis invariant
vanishes because $\tau\sim S$ is null. Push off it by a generic linear-part deformation $L_t$,
keeping the Syracuse cocycle ($\tau(a)=\tfrac12E,\tau(b)=0$). Then $\alpha_t(\gamma)=O(t)$, and
the **first-order Margulis invariant** $\dot\alpha(\gamma)=\tfrac{d}{dt}\big|_0\langle\tau_t(\gamma),x^0_t(\gamma)\rangle$
is a concrete number per class — the leading geometric data of the degeneration.

## Finding — the footprint is $S/D$, the *value*, not $D\mid S$, the *integrality*

Across independent generic deformation directions, $\dot\alpha(\gamma)$ robustly **tracks the
fixed-point value** $x_0^\ast=S/D$ (the cycle value / ideal endpoint):

| quantity | Pearson corr | Spearman corr (outlier-proof) |
|---|---|---|
| $\lvert S/D\rvert$ | $+0.96$ | $\mathbf{+0.89}$ |
| $\beta=S/2^E$ (the cocycle value) | $+0.08$ | $+0.78$ |
| $S/D$ (signed) | $+0.94$ | $+0.41$ |
| $S$ | $+0.16$ | — |
| $1/D$ | $+0.06$ | — |
| $E$ | $+0.27$ | — |

The $\lvert S/D\rvert$ correlation magnitude is $\approx0.93$–$0.96$ in *every* generic
direction (the sign just follows the direction), and is exactly $0$ in the Cartan
(axis-preserving) direction. The largest $\dot\alpha$ all belong to the largest-$\lvert S/D\rvert$
classes (the $o{=}5,E{=}8,D{=}13$ words, $S/D\approx16$–$25$). This is geometrically natural:
the holonomy fixes a spacelike line at null-position $S/D$, so deforming, the Margulis
translation grows with how far that line sits from the origin — i.e. with $S/D$.

**But integrality is invisible.** The Syracuse *cycles* (integer $S/D$: $a,ab,aab\to-1,1,-5$)
do **not** stand out — their $\dot\alpha$ ($0.6,2.6,17.2$) just track their own $\lvert S/D\rvert$
like any class. No class has $\dot\alpha=0$ except the trivial $b$ ($S=0$). The relation to
$\lvert S/D\rvert$ is a trend, not exact (the word's internal arrangement perturbs it).

## Verdict

> The arithmetic leaves a footprint on the geometry **through the value $S/D$, not through
> the divisibility $D\mid S$.** The smooth Lorentzian degeneration hands you $S/D$ as a
> *continuous* observable (the fixed-line position / ideal endpoint), with $\approx0.9$
> rank-fidelity. The Collatz condition is the **integrality** of that observable — and
> integrality is exactly the step the smooth geometry cannot see.

This precisely localises the arithmetic gap: every geometric construction in this approach
(the half-plane axis, the BTZ endpoint, the Margulis degeneration) converges on the *same*
continuous quantity $S/D$, and the *entire* remaining difficulty of the cycle problem is the
one discrete question the geometry never reaches — **is the geometrically-visible $S/D$ an
integer?** Geometry reformulates Collatz down to its integrality core and stops there.
