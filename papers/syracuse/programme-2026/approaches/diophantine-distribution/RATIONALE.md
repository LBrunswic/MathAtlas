# Diophantine distribution

> Notation: a gap word $w$ has letters $d_0,\dots,d_{o-1}$, gap-sum
> $|w| := \sum_k d_k = E$, and length $\operatorname{len}(w) = o$. The word characters are
> $D(w) = 2^{E}-3^{o}$ and $S(w) = \sum_{k=0}^{o-1} 2^{e_k}3^{\,o-1-k}$ (the closed-form RHS
> sum, $e_k = d_0+\dots+d_{k-1}$). These are the characters of
> [`cycle-gcd`](../cycle-gcd/STATUS.md) / [`cocycle-combine`](../cocycle-combine/STATUS.md).

## Idea

Start from the Diophantine closed form and the word characters $D$, $S$. Define the map
$$Z : W \to \mathbb{Z}_2, \qquad Z(u) = S(u)/D(u).$$

The pitch rests on three observations.

**1. Conjugacy with the Collatz map.** $Z(\operatorname{shift}(u)) = T(Z(u))$, where $T$ is
the Collatz function. This holds for each of the three usual definitions of $T$ (each with
its associated flavor of words). Two consequences:

- $S$ is injective;
- $S(u)/D(u) = S(v)/D(v)$ implies there exist a word $w$ and exponents $p,q$ with
  $u = w^{p}$ and $v = w^{q}$ (rigidity: equal $Z$-value $\Rightarrow$ common root word).

**2. Fundamental solution for non-cyclic words.** The closed form is a *linear* Diophantine
equation, so its general solution is (inhomogeneous fundamental solution) + (homogeneous
family). Concretely, all initial conditions in $\mathbb{Z}_2$ that have parity vector $w$
are of the form
$$S(u)/D(u) \;+\; 2k\cdot 2^{|w|}, \qquad k \in \mathbb{Z}_2.$$
Thus $S(u)/D(u)$ is a canonical **fundamental solution** attached to *any* word $w$ — not
only to words that close up into a cycle.

**3. Imbalance factorization.** Writing $\beta = 2^{\,|w|/\operatorname{len}(w)} = 2^{E/o}$,
$$\frac{S(u)}{D(u)} \;=\; \frac{\eta}{\beta - 3},$$
where $\eta$ is an **imbalance factor** controlled by simple bounds on the variation of $w$:
typically $\eta \in [2^{-p}, 2^{p}]$ with
$$p \;=\; \max_{k}\;\bigl|\,(d_0 + \dots + d_{k-1}) - \tfrac{|w|}{\operatorname{len}(w)}\,k\,\bigr|,$$
the maximal discrepancy of the partial gap-sums from the mean line. (This mirrors
[`circulant_matrix`](../circulant_matrix/STATUS.md)'s $D = \pm N_{K/\mathbb{Q}}(\beta-3)$.)

**Regime dictionary** (here $n = o = \operatorname{len}(w)$):

1. Expanding $T^n(x) \gt x$ is associated to $|w| \lt n\log_2 3$, hence $D \lt 0$ and
   $1/(\beta - 3) \lt 0$.
2. Contracting $T^n(x) \lt x$ is associated to $|w| \gt n\log_2 3 + \epsilon$, hence positive.
3. "Large" $|w|$, i.e. $|w| \gt (\log_2 3 + \epsilon)\operatorname{len}(w)$, leads to
   $1/(\beta - 3) \lt 2$.

This gives a **heuristic for the size of the fundamental solution**:

- contractive + positive solution $\Rightarrow$ fundamental solution bounded by a power of
  $2$ in the imbalance;
- expanding + positive solution $\Rightarrow$ fundamental solution in
  $[\,2^{|w|}/\operatorname{Poly}(w),\; 2^{|w|}\,]$.

## Why it might work

Target: the **flying time** $\max\{\,n : T^n(x) \ge x\,\}$ is finite for every positive
integer $x$. Proposed route, via quantitative control of the fundamental solution over
words of bounded imbalance $p$:

- Initial conditions in $[1, 2^n]$ whose word has small $|w|$ **or** large imbalance sit
  close to $2^n$ — or at least above a threshold $f(n,p)$ that is increasing in $n$ and
  decreasing in $p$.
- Hence every initial condition in $[1, f(n,p)]$ has *large* $|w|$, so (regime 3 + the
  contractive/positive heuristic) has finite flying time.
- Letting $(n,p) \to \infty$ gives $f(n,p) \to \infty$, so every positive integer has finite
  flying time.

The leverage is that the fundamental-solution size is dictated by word geometry ($|w|$ vs
$\log_2 3 \cdot \operatorname{len}(w)$, and the imbalance $p$), which is a priori and
combinatorial, rather than by following individual trajectories.

## Known prior art / why it isn't obviously dead

- **Builds on the project's own machinery.** The closed form ([`diophantine`](../diophantine/RATIONALE.md))
  and the $D,S$ word-cocycle ([`cycle-gcd`](../cycle-gcd/STATUS.md),
  [`cocycle-combine`](../cocycle-combine/STATUS.md)) are already stated/derived here.
- **The conjugacy $Z\circ\operatorname{shift} = T\circ Z$** is the classical 2-adic
  conjugacy between the shift and the Collatz map (Lagarias; Bernstein–Lagarias). The novel
  twist is using it to transport a *fundamental solution* to **non-cyclic** words and to read
  off the rigidity $S(u)=S(v) \Rightarrow$ common root word.
- **Flying-time finiteness is weaker than the full conjecture.** It controls how long an
  orbit can stay at or above its start, but does not by itself exclude divergence or
  nontrivial cycles without further argument — so the goal is substantial yet not equivalent
  to the conjecture, which keeps it plausible.

## Known gap (the linchpin)

The fundamental solution lives in $\mathbb{Z}_2$ — really in a localization of $\mathbb{Z}$ —
not in $\mathbb{Z}$. One can **amend** it by some $2k\cdot 2^{|w|}/D(w)$ to land on a genuine
integer. The whole heuristic program becomes a proof **iff** the amendment $k$ can be bounded
in terms of the imbalance $p$. See STATUS open questions.
