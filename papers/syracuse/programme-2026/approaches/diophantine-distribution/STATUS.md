# Status — diophantine-distribution

## Current state

Foundations proved and machine-checked: the fundamental-solution layer (cyclic + all
trajectories) and the imbalance bounds are in [`fundamental.md`](fundamental.md), verified by
[`verify_fundamental.py`](verify_fundamental.py). The target is settled in scope — flying-time
finiteness **does** imply the full conjecture (see Results). A 500k-start statistical survey
([`results/RESULTS.md`](results/RESULTS.md)) shows the raw "relative position" correlates with
flying time only mechanically (via word length $E$); the non-mechanical signal is word
criticality $E/o\to\log_2 3$. Remaining work is the quantitative program: the integrality
amendment bound and the polynomial denominator in the critical band.

## Results

- **Flying-time finiteness ⟹ Collatz (proved, strong induction).** If every positive integer
  has finite flying time $\tau(x)=\max\{n:T^n(x)\ge x\}$, then every $x$ reaches $1$: induct on
  $x$. Assume all $0\lt k\lt x$ reach $1$. Finite flying time gives some $p$ with
  $T^p(x)\lt x$; by the hypothesis $T^p(x)$ reaches $1$, hence so does $x$. So the approach's
  target is **equivalent in strength to the conjecture**, not weaker — the earlier scope
  caveat is resolved.
- **FS1 — word-map is affine, fixed point $=S/D$ (proved + checked).**
  $F_w(x)=\tfrac{3^o}{2^E}x+\tfrac{S(w)}{2^E}$, unique fixed point $x_w^\ast=S(w)/D(w)$. Since
  $D$ is odd, $x_w^\ast\in\mathbb{Z}_2$ for every word. [`fundamental.md`](fundamental.md) §FS1.
- **FS2 — cyclic interpretation (proved).** $x_w^\ast$ is the unique returning start; integer
  cycle $\iff D\mid S$ + parity consistency. Recovers the `cycle-gcd` cycle equation;
  reproduces $-1$ (word $(1)$) and $-7$ (word $(2,1)$).
- **FS3 — fundamental solution among all trajectories (proved + brute-forced).** The set of
  $x\in\mathbb{Z}_2$ with word exactly $w$ and $a_o$ odd is the single class
  $x_w^\ast + 2^{\,|w|+1}\mathbb{Z}_2 = x_w^\ast + 2k\cdot2^{|w|}\mathbb{Z}_2$ (Terras
  bijection + word↔compressed-string). **The pitch's factor of $2$ is exactly right**: it is
  the one extra bit certifying that the word *closes* on an odd $a_o$ (modulus $2^{E}\to2^{E+1}$).
- **FS4 — imbalance factorization (proved + checked).** $S(w)/D(w)=\eta/(\beta-3)$,
  $\beta=2^{E/o}$, with $\eta\in[2^{-p},2^p]$, $p=\max_k|e_k-\tfrac{E}{o}k|$. Via the balanced-word
  lemma $\sum_k\beta^k3^{o-1-k}=D/(\beta-3)$.
- **FS5a — contracting + large ⟹ power of 2 in imbalance (proved + checked).** If
  $\beta\ge\tfrac72$ then $0\lt x_w^\ast\le2^{\,p+1}$, independent of $E$.
- **FS5b — expanding/critical ⟹ large (partial).** $|x_w^\ast|=\eta/(3-\beta)$ with the
  Matveev lower bound on $|D|$ gives exponential-in-$E$ growth near criticality; the *polynomial*
  denominator version is still open (see below).
- **Statistics over all odd $x\le10^6$ ([`results/RESULTS.md`](results/RESULTS.md), 500k starts).**
  Relative position $\rho=(x-x_w^\ast)/2^E=(x-a_o)/D$ of the flying-word fundamental solution is
  almost monotone in flying time (Spearman $-0.976$); imbalance $+0.919$. **But mostly
  mechanical:** flying-word length $E$ has $\rho_s=0.989$ with flight, and both quantities are
  functions of $E$; partialling out $E$ collapses them to $-0.16$ / $-0.13$. The numerator
  $|x-x_w^\ast|\sim x$ is flat across flight buckets — long-flying integers are **not**
  anomalously close to their fundamental solution. **What survives:** the contraction rate
  $E/o$ keeps a partial link ($-0.393$) — long flights sit nearer the critical line
  $E/o=\log_2 3$. Lesson: use $E$-residualized / criticality statistics, not raw $\rho$.

## Dead ends

- _(none yet)_

## Open questions

- **Integrality linchpin.** Bound the amendment $k$ in $x_w^\ast + 2k\,2^{|w|}/D(w)$ that
  pulls the fundamental solution into $\mathbb{Z}$, *in terms of the imbalance $p$*. Without
  this bound the program stays heuristic. (FS-layer is done; this is the next real obstacle.)
- **Polynomial denominator in the critical band.** Upgrade FS5b from "exponential-in-$E$ via
  Matveev" to $|x_w^\ast|\ge 2^{|w|}/\operatorname{Poly}(w)$, uniformly over critical $(E,o)$.
- **Threshold function $f(n,p)$.** Make rigorous that initial conditions in $[1,2^n]$ with
  small $|w|$ or large imbalance lie above $f(n,p)$ (increasing in $n$, decreasing in $p$), and
  $f(n,p)\to\infty$ as $(n,p)\to\infty$ — then combine with the now-proved induction reduction.
- **Conjugacy.** Write up $Z(\operatorname{shift}(u)) = T(Z(u))$ for each of the three $T$
  conventions, completing the FS3 corollary (injectivity / common-root rigidity).

## Next step under consideration

Attack the integrality linchpin: express the integer-amendment $k$ explicitly from
$x_w^\ast = S/D \bmod 1$ and try to bound it by a function of the imbalance $p$ (e.g. via the
$\eta\in[2^{-p},2^p]$ control of FS4).
