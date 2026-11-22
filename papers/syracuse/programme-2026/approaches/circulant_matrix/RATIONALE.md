# Circulant-Matrix

> Child approach of [`cycle-gcd`](../cycle-gcd/RATIONALE.md). It inherits the cycle
> equation and the rotation sums $S^{(j)}$ and asks: **what linear-algebraic object are the
> rotations?** The answer is a diagonal-conjugated circulant whose every eigenvalue and whose
> determinant carry $D=2^E-3^o$ explicitly — a candidate a-priori handle on $\gcd_j S^{(j)}$.

## Idea

Recall from [`cycle-gcd`](../cycle-gcd/STATUS.md): for a gap word with even-step prefix sums
$e_0=0\le e_1\le\dots\le e_o=:E$ ($d_k=e_{k+1}-e_k$, $o$ odd steps), the rotation sums are
$$S^{(j)} \;=\; \sum_{m=0}^{o-1} 2^{\hat e^{(j)}_m}\,3^{\,o-1-m},
\qquad \hat e^{(j)}_m=\textstyle\sum_{l=0}^{m-1} d_{(j+l)\bmod o}\ (\text{wrapping adds }E).$$

**Step 1 — re-index by the absolute odd-term index.** Put $i=(j+m)\bmod o$. A single wrap
occurs exactly when $i \lt j$, contributing $+E$ to the exponent, and $(i-j)\bmod o = m$. This
  turns the rotation sum into a clean $j,i$ double-indexed integer sum:

$$\boxed{\,S^{(j)} \;=\; \sum_{i=0}^{o-1} 2^{\,e_i-e_j+E\cdot\mathbf 1[i \lt j]}\;
3^{\,o-1-((i-j)\bmod o)}\,}\tag{$\star$}$$

So $\vec S = M\,\mathbf 1$ is the **row-sum vector** of the integer matrix
$M_{j,i}=2^{\,e_i-e_j+E\,\mathbf 1[i \lt j]}\,3^{\,o-1-((i-j)\bmod o)}$ (all exponents $\ge 0$, so
$M\in\mathbb{Z}_{\ge0}^{o\times o}$).

**Step 2 — detrend to expose the circulant.** This is the seed observation: subtract the
*average gap* $E/o$ from each exponent. Define $\tilde e_k := e_k-\tfrac{k}{o}E$ (the
gap-word's deviation from a perfectly uniform word). Using
$i-j+o\,\mathbf 1[i \lt j]=(i-j)\bmod o$,

$$e_i-e_j+E\,\mathbf 1[i \lt j]\;=\;(\tilde e_i-\tilde e_j)\;+\;\tfrac{E}{o}\big((i-j)\bmod o\big).$$

The first piece is a pure **power-of-2 diagonal twist**; the second depends only on
$(i-j)\bmod o$. Hence ($\star$) factors as

$$\boxed{\;\vec S \;=\; \Delta^{-1}\,C\,\Delta\,\mathbf 1\;},

\qquad
\Delta=\operatorname{diag}\!\big(2^{\tilde e_0},\dots,2^{\tilde e_{o-1}}\big),\quad
C\ \text{circulant with symbol}\ c_r=2^{\,rE/o}\,3^{\,o-1-r}.$$
Equivalently $M_{j,i}=2^{\tilde e_i-\tilde e_j}\,c_{(i-j)\bmod o}$, i.e. **$M$ is the circulant
$C$ conjugated by the diagonal $\Delta$**. The conjugation factor $2^{\tilde e_i-\tilde e_j}
=2^{(e_i-e_j)-(i-j)E/o}$ is exactly the power-of-2 term in the seed sketch; $\Delta$ and $C$
separately involve the irrational $2^{E/o}$, but the product $M$ has integer entries.

## Why it might work

The point of [`cycle-gcd`](../cycle-gcd/RATIONALE.md) is to bound $\gcd_j S^{(j)}$ **a priori**
(word structure only), knowing it equals $|D|$ exactly on a genuine cycle. The circulant frame
makes $D$ appear three times over, structurally:

1. **Every eigenvalue of $C$ is $D$ over an algebraic factor.** With $\omega=e^{2\pi i/o}$,

   $$\hat c_\ell=\sum_{r=0}^{o-1}c_r\,\omega^{r\ell}
   =3^{o-1}\sum_{r=0}^{o-1}\!\Big(\tfrac{2^{E/o}\omega^\ell}{3}\Big)^{\!r}
   =\frac{D}{\,2^{E/o}\omega^\ell-3\,},\qquad \ell=0,\dots,o-1,$$

   because $\big(2^{E/o}\omega^\ell\big)^{o}=2^E$ makes the geometric sum telescope to
   $2^E/3^o-1=D/3^o$. So $D$ sits in the numerator of **all** $o$ eigenvalues.

2. **The determinant is a pure power of $D$.** Since $\prod_\ell\big(X-2^{E/o}\omega^\ell\big)
   =X^o-2^E$, evaluating at $X=3$ gives $\prod_\ell(3-2^{E/o}\omega^\ell)=3^o-2^E=-D$, hence

   $$\det M=\det C=\prod_{\ell}\hat c_\ell=(-1)^{o+1}\,D^{\,o-1}.$$

   (Verified: $1\to1$ gives $1$; $-5\to-7$ gives $1=(-1)^3(-1)^1$; the test word $E{=}8,o{=}5$
   gives $13^4=28561$.)

3. **$\vec S = M\mathbf 1$ is a single integer vector inside a lattice of known determinant.**
   $\gcd_j S^{(j)}$ is the content of the row-sum vector of an integer matrix with
   $\det=\pm D^{o-1}$. Its Smith normal form has invariant factors $d_1\mid\dots\mid d_o$ with
   $\prod d_k=|D|^{o-1}$; the largest, $d_o$, divides $|D|^{o-1}$ and bounds the content of any
   image vector. The bet: word-structure constraints on $M$ (a non-negative integer
   $\Delta$-twisted circulant) pin the SNF / content of $M\mathbf 1$ **without** invoking the
   cycle's divisibility — yielding the a-priori ceiling on $\gcd_j S^{(j)}$ that cycle-gcd needs.

In short: cycle-gcd asks for an a-priori bound on a gcd of $o$ integers; this child recasts
those integers as the row sums of an explicit matrix whose spectrum and determinant are closed
forms in $D$, moving the question into circulant/lattice territory (DFT, SNF, Hadamard) where
$D$ is already visible before any divisibility is assumed.

## Known prior art / why it isn't obviously dead

- That $\prod_\ell(X-2^{E/o}\omega^\ell)=X^o-2^E$ and the resulting $\det=\pm D^{o-1}$ are
  elementary; the novelty here is *which* matrix — the rotation/circulant frame for the cycle
  sums specifically, used as a route to the gcd.
- The honest barrier inherited from the parent stands: on a cycle $\gcd_j S^{(j)}=|D|$ exactly,
  so any genuine progress is an a-priori statement about $M$'s integer structure, ultimately
  equivalent to a lower bound on $|2^E-3^o|$ (Baker territory). The hope is only that the
  circulant/SNF packaging exposes a cheaper combinatorial bound for structured word classes
  (e.g. bounded circuits), not that it sidesteps transcendence in general.
- $\Delta$ carries the irrational $2^{E/o}$; all *integer* content lives in $M=\Delta^{-1}C\Delta$.
  Spectral statements about $C$ are statements about algebraic integers in
  $\mathbb{Z}[2^{1/o},\omega]$ — care needed before reading off integer divisibility.
