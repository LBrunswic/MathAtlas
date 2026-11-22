# Derivation: $x_0 - x'_0$ for the general single-block shift $b'_k = b_k + a\,\mathbf{1}_{k\gt q}$

This generalizes `derivation-single-shift.md`: we allow the shift amount $a$ to be any positive integer (not just $a=1$). The pay-off is that the integrality obstruction we hit at $a=1$ disappears for the right choice of $a$, and we recover the **Collatz predecessor tree** as the simplest non-trivial perturbation family.

## Setup

Let $(b_k)_{k \ge 0}$ be a strictly increasing sequence of non-negative integers with $b_0 = 0$, defining a 2-adic starting point
$$
x_0 \;=\; -\sum_{k \ge 0} \frac{2^{b_k}}{3^{k+1}} \;\in\; \mathbb{Z}_2.
$$

Fix integers $q \ge 0$ and $a \ge 1$, and define
$$
b'_k \;=\; b_k + a\,\mathbf{1}_{k\gt q} \;=\; \begin{cases} b_k & 0 \le k \le q,\\ b_k + a & k \gt q.\end{cases}
$$
Since $(b_k)$ is strictly increasing and $a \ge 1$, $(b'_k)$ is also strictly increasing with $b'_0 = 0$, hence corresponds to a 2-adic starting point
$$
x'_0 \;=\; -\sum_{k \ge 0} \frac{2^{b'_k}}{3^{k+1}} \;\in\; \mathbb{Z}_2.
$$

Goal: derive $x_0 - x'_0$ explicitly, then characterize when this difference lies in $\mathbb{Z}$.

## Three equivalent forms

**Termwise difference.** For $k \le q$, $b'_k = b_k$; for $k \gt q$, $2^{b'_k} - 2^{b_k} = (2^a-1)\,2^{b_k}$. Hence
$$
x_0 - x'_0 \;=\; \sum_{k \gt q} \frac{2^{b'_k} - 2^{b_k}}{3^{k+1}} \;=\; (2^a - 1)\sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}.
$$

**Form 1 — Tail series:**
$$
\boxed{\; x_0 - x'_0 \;=\; (2^a - 1)\sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}. \;}
$$

The earlier derivation showed $\sum_{k\gt q} 2^{b_k}/3^{k+1} = -\,2^{b_{q+1}} x_{q+1}/3^{q+1}$ (using the 2-adic reconstruction of $x_{q+1}$). Substituting:

**Form 2 — Trajectory form:**
$$
\boxed{\; x_0 - x'_0 \;=\; -\,\frac{(2^a - 1)\,2^{b_{q+1}}\,x_{q+1}}{3^{q+1}}. \;}
$$

**Form 3 — Head identity.** Splitting $x_0$ at index $q$ and matching against $x'_0$:
$$
\boxed{\; x'_0 - 2^a\,x_0 \;=\; (2^a - 1)\sum_{k=0}^{q} \frac{2^{b_k}}{3^{k+1}}. \;}
$$
(For $a=1$ this collapses to $x'_0 - 2 x_0 = \sum_{k=0}^q 2^{b_k}/3^{k+1}$, as before.)

The case $a = 1$ of all three boxed identities recovers the previous file.

## Integrality condition

From Form 2, integrality of $x_0 - x'_0$ in $\mathbb{Q}$ (equivalently, divisibility in $\mathbb{Z}$ when $x_{q+1} \in \mathbb{Z}$) requires
$$
3^{q+1} \;\Big|\; (2^a - 1)\,2^{b_{q+1}}\,x_{q+1}.
$$

Since $\gcd(2, 3) = 1$, this is equivalent to
$$
\nu_3\!\big((2^a - 1)\,x_{q+1}\big) \;\ge\; q+1.
$$

For an **integer trajectory** ($x_0 \in \mathbb{Z}$), $3 \nmid x_n$ for $n \ge 1$ (since $3x_{n-1} + 1 \equiv 1 \pmod 3$), so $\nu_3(x_{q+1}) = 0$ whenever $q \ge 0$. The condition reduces to
$$
\nu_3(2^a - 1) \;\ge\; q+1.
$$

This is a clean number-theoretic condition on $a$. We compute it next.

## $\nu_3(2^a - 1)$ via lifting-the-exponent

**Lemma.** For $a \ge 1$,
$$
\nu_3(2^a - 1) \;=\; \begin{cases} 0 & a \text{ odd},\\ 1 + \nu_3(a) & a \text{ even}.\end{cases}
$$

*Proof.* Since $2 \equiv -1 \pmod 3$, $2^a - 1 \equiv (-1)^a - 1 \pmod 3$. If $a$ is odd this is $-2 \equiv 1$, so $\nu_3 = 0$. If $a = 2m$ is even, write $2^a - 1 = 4^m - 1$. Since $3 \mid 4 - 1$ and $3 \nmid 4, 1$, the lifting-the-exponent lemma gives
$$\nu_3(4^m - 1) \;=\; \nu_3(4 - 1) + \nu_3(m) \;=\; 1 + \nu_3(m) \;=\; 1 + \nu_3(a) - \nu_3(2) \;=\; 1 + \nu_3(a),$$
since $\nu_3(2) = 0$. $\square$

Equivalently: $\nu_3(2^a - 1) \ge q+1$ $\iff$ $a$ is even and $\nu_3(a) \ge q$, i.e. $2 \cdot 3^q \mid a$. (This is just the statement that the multiplicative order of $2$ modulo $3^{q+1}$ is exactly $2 \cdot 3^q$.)

## Main result

**Theorem.** Let $(b_k)$ be strictly increasing with $b_0 = 0$ and assume $x_0$ is an integer Collatz trajectory (so $x_{q+1} \in \mathbb{Z}$, $3 \nmid x_{q+1}$). Then
$$
x_0 - x'_0 \;\in\; \mathbb{Z} \quad\Longleftrightarrow\quad 2 \cdot 3^q \,\Big|\, a.
$$
When this holds,
$$
x_0 - x'_0 \;=\; -\,\frac{2^a - 1}{3^{q+1}} \cdot 2^{b_{q+1}} \cdot x_{q+1} \;\in\; \mathbb{Z},
$$
with $(2^a - 1)/3^{q+1} \in \mathbb{Z}$.

**Corollary (predecessor family).** For every $q \ge 0$, the minimal admissible shift is $a = 2 \cdot 3^q$, and choosing $a = 2 \cdot 3^q \cdot m$ for $m \in \mathbb{Z}_{\ge 1}$ produces an infinite family of integer perturbations $x_0 \mapsto x'_0$, each differing from $x_0$ by an explicit integer.

## Worked example: connection to the Collatz inverse tree

Take $x_0 = 1$, so $b_k = 2k$, $x_k = 1$ for all $k$.

**Case $q = 0$, $a = 2$ (minimal).** Form 2 gives
$$x_0 - x'_0 \;=\; -\,\frac{(4-1)\cdot 2^{b_1} \cdot x_1}{3^1} \;=\; -\,\frac{3 \cdot 4 \cdot 1}{3} \;=\; -4,$$
so $x'_0 = 5$. Check: $3 \cdot 5 + 1 = 16 = 2^4$, so $b'_1 = 4 = b_1 + 2$, and $T(5) = 1 = x_1$. Then the trajectory of $5$ from step $1$ onwards agrees with $1$'s, and $b'_k = b_k + 2$ for $k \ge 1$. ✓

In closed form, the map $x_0 \mapsto x'_0$ here is the well-known **predecessor map** $x \mapsto 4x + 1$.

**Case $q = 1$, $a = 6$ (minimal).** Form 2 gives
$$x_0 - x'_0 \;=\; -\,\frac{(64-1)\cdot 2^{b_2} \cdot x_2}{3^2} \;=\; -\,\frac{63 \cdot 16 \cdot 1}{9} \;=\; -112,$$
so $x'_0 = 113$. Check: $3 \cdot 113 + 1 = 340 = 2^2 \cdot 85$, so $b'_1 = 2 = b_1$, and $T(113) = 85$. Then $3 \cdot 85 + 1 = 256 = 2^8$, so $b'_2 = 2 + 8 = 10 = b_2 + 6$, and $T(85) = 1 = x_2$. From step $2$ onwards the trajectory of $113$ agrees with $1$'s, shifted by $a = 6$. ✓

Interpretation: $113$ is a depth-$2$ predecessor of $1$ in the Collatz inverse tree ($113 \to 85 \to 1$), and the perturbation $a = 6, q = 1$ is precisely this two-step backward move.

## Why this is the right generalization

The single-shift family $b'_k = b_k + a\,\mathbf{1}_{k\gt q}$ has a very clean dynamical meaning: it preserves the trajectory from step $q+1$ onwards ($x'_{q+1} = x_{q+1}$) while modifying the first $q+1$ steps to reach $x_{q+1}$ via a longer (by $a$ halvings) route. The integrality threshold $a = 2 \cdot 3^q$ is exactly the multiplicative order of $2$ modulo $3^{q+1}$ — the smallest power-of-$2$ jump that "closes up" the $3$-adic divisibility needed to keep $x'_k$ in $\mathbb{Z}$ for all $k \le q$.

Equivalently: the perturbation family $\{a = 2 \cdot 3^q \cdot m : m \ge 1\}$ at depth $q$ enumerates the predecessors of $x_{q+1}$ in the Collatz inverse tree, indexed by how many extra halvings $a$ we insert. The framework recovers — and parametrizes — the predecessor tree as a single-block parity perturbation.

## Cross-check: 3-adic propagation along the trajectory

A second derivation of the threshold $\nu_3(2^a - 1) \ge q+1$ from the forward recurrence:

For $k \lt q$, parities agree, so the recurrence $3 x_k + 1 = 2^{b_{k+1}-b_k} x_{k+1}$ also holds for $x'$, giving
$$x'_k - x_k \;=\; \frac{2^{b_{k+1}-b_k}}{3}\,(x'_{k+1} - x_{k+1}).$$
At the boundary $k = q$, the parities differ by $a$, so
$$x'_q - x_q \;=\; \frac{2^{b_{q+1}-b_q}\,(2^a - 1)\,x_{q+1}}{3}.$$
Propagating backwards $q$ times,
$$\nu_3(x'_{q-j} - x_{q-j}) \;=\; \nu_3(2^a - 1) - j - 1, \quad 0 \le j \le q.$$
For $x'_0 - x_0 \in \mathbb{Z}$ we need $\nu_3(x'_0 - x_0) \ge 0$, i.e. $\nu_3(2^a - 1) \ge q + 1$. ✓

This matches the algebraic derivation and shows the obstruction is a *propagated* 3-adic divisibility cost, accumulating one factor of 3 per step backwards from the perturbation point.

## Extension to negative shifts ($a \lt 0$)

The whole framework extends to negative $a$ — i.e. *removing* halvings from the trajectory rather than inserting them. This corresponds to the **forward** Collatz moves (the inverse of the predecessor moves above) and is dual to the positive-$a$ analysis.

### Validity constraint

Write $c_{k+1} := b_{k+1} - b_k = \nu_2(3 x_k + 1) \ge 1$ for the step sizes of the parity vector. For $(b'_k)$ to be strictly increasing we need $b'_{q+1} \gt b'_q$, i.e. $b_{q+1} + a \gt b_q$, i.e.
$$a \;\gt \; -\,c_{q+1}, \qquad\text{equivalently}\qquad |a| \;\le\; c_{q+1} - 1 \quad\text{(when }a\lt 0\text{)}.$$
So negative shifts are constrained by the local step size: we can only remove up to $c_{q+1} - 1$ halvings at position $q$.

### The same identity, the same condition

The termwise computation goes through verbatim for $a \in \mathbb{Z}$ (just interpret $2^a$ as a rational when $a\lt 0$):
$$x_0 - x'_0 \;=\; -\,\frac{(2^a - 1)\,2^{b_{q+1}}\,x_{q+1}}{3^{q+1}}.$$

For $a = -A \lt 0$ ($A \gt 0$), $2^a - 1 = -\,(2^A - 1)/2^A$, so
$$\boxed{\; x_0 - x'_0 \;=\; \frac{(2^A - 1)\,2^{b_{q+1} - A}\,x_{q+1}}{3^{q+1}}, \quad a = -A \lt 0. \;}$$
The numerator is now a positive product (the validity constraint $A \le c_{q+1} - 1 \le b_{q+1} - 1$ guarantees $b_{q+1} - A \ge 1 \ge 0$).

**Integrality.** The same $3$-adic accounting applies: $x_0 - x'_0 \in \mathbb{Z}$ iff $\nu_3(2^A - 1) \ge q+1$, iff $2 \cdot 3^q \mid A$. So the minimal negative shift is $a = -\,2 \cdot 3^q$, available exactly when $c_{q+1} \gt 2 \cdot 3^q$.

### Dynamical meaning: forward moves

A negative shift at $(q, a = -A)$ preserves $x'_{q+1} = x_{q+1}$ but routes there via a *shorter* parity step: $\nu_2(3 x'_q + 1) = c_{q+1} - A$ instead of $c_{q+1}$. Solving the recurrence: $3 x_q + 1 = 2^A\,(3 x'_q + 1)$, giving
$$x'_q \;=\; \frac{x_q - (2^A - 1)/3}{2^A} \cdot \frac{1}{?} \quad\Longleftrightarrow\quad x'_q \;=\; \frac{3 x_q + 1 - 2^A}{3 \cdot 2^A} \cdot 3 \;=\; \frac{3 x_q + 1}{2^A \cdot 3} - \frac{1}{3},$$
which simplifies (for $A$ with $3 \mid 2^A - 1$) to a polynomial map of $x_q$ with integer coefficients.

The clean special case $q=0, A=2$: $x'_0 = (x_0 - 1)/4$, the inverse of the predecessor map $4x+1$. More generally, the $(q, a=-2\cdot3^q)$ family inverts the predecessor family $(q, a=+2\cdot3^q)$.

### Worked examples

**$q=0$, $a=-2$.** Need $c_1 = b_1 \gt 2$. Take $x_0 = 5$ (then $3\cdot5+1 = 16$, $b_1 = 4$, $x_1 = 1$). Formula:
$$x_0 - x'_0 \;=\; \frac{(4-1) \cdot 2^{4-2} \cdot 1}{3} \;=\; \frac{3 \cdot 4 \cdot 1}{3} \;=\; 4,$$
so $x'_0 = 5 - 4 = 1$. Cross-check: $x'_0 = (x_0 - 1)/4 = 4/4 = 1$. ✓ This is the inverse of the $q=0,a=+2$ move $1 \mapsto 5$.

**$q=1$, $a=-6$.** Need $c_2 \gt 6$. Take $x_0 = 113$ (then $b_1 = 2$, $x_1 = 85$, $c_2 = 8$, $x_2 = 1$). Formula:
$$x_0 - x'_0 \;=\; \frac{(64-1) \cdot 2^{10-6} \cdot 1}{9} \;=\; \frac{63 \cdot 16}{9} \;=\; 112,$$
so $x'_0 = 113 - 112 = 1$. ✓ This is the inverse of the $q=1,a=+6$ move $1 \mapsto 113$.

### What negative shifts add

On their own, negative shifts give nothing new — they are formal inverses of the positive-shift (predecessor) moves, so the single-block family generates the *bi-directional* Collatz tree but no extra relations.

## Structural limitation: finite support only rewrites the past

A crucial observation that constrains *all* finite-support perturbations (single- or multi-block, any signs):

> If the perturbation $\delta(k) := b'_k - b_k$ vanishes for $k \ge N$ (i.e. has finite support), then the parity vector of the trajectory agrees with the original for $k \ge N$. Hence $x'_k = x_k$ for all $k \ge N$.

The two trajectories *converge to the same downstream sequence*. They do not move to a different position in the Collatz tree — they only re-route the **past** leading to the common future $x_N, x_{N+1}, \dots$. The new starting point $x'_0$ is just a different predecessor of the shared node $x_N$, reachable from it by the standard backward-tree moves.

**Consequence.** Any finite combination of single-block shifts — including mixed-sign double-block moves and arbitrary finite multi-block configurations — is reducible to a sequence of predecessor / successor moves on the same fixed downstream trajectory. It is, by construction, "stitch a new past onto a known $x_N$". This is exactly the inverse Collatz dynamics, parametrized differently.

**Therefore, to extract genuinely new arithmetic content from this framework, the perturbation must have unbounded support** — i.e. $\delta(k) \ne 0$ for infinitely many $k$. Only such perturbations can produce a $x'_0$ whose entire trajectory differs from $x_0$'s, putting $(x_0, x'_0)$ in genuinely *different* positions in the tree.

Candidates for infinite-support perturbations to study next:
- **Periodic shifts:** $\delta(k) = \pi(k)$ with $\pi$ periodic. The 2-adic series $\sum_k 2^{b_k + \pi(k)}/3^{k+1}$ can still be rational (e.g. when $(b_k)$ is eventually periodic and $\pi$ has the same period or a divisor).
- **Linear / sublinear growth:** $\delta(k) = \lfloor \alpha k \rfloor$ for $\alpha \gt 0$. Modifies the long-run growth of the parity vector itself.
- **Sparse but unbounded support:** $\delta$ supported on $\{q_i\}_{i \ge 1}$ with $q_i \to \infty$.

Each of these moves us off the existing Collatz tree, into a 2-adic neighborhood we haven't probed.

## Summary

| Quantity | Expression |
|---|---|
| Difference (any sign $a$) | $x_0 - x'_0 = -\,(2^a - 1)\,2^{b_{q+1}}\,x_{q+1}/3^{q+1}$ |
| Integrality condition | $2 \cdot 3^q \mid \lvert a \rvert$ (equivalently $\nu_3(2^{\lvert a\rvert} - 1) \ge q+1$) |
| Minimal admissible $\lvert a \rvert$ | $\lvert a \rvert = 2 \cdot 3^q$ |
| Validity (any sign $a$) | $a \gt -c_{q+1}$ — positive: unconstrained; negative: $\lvert a \rvert \le c_{q+1} - 1$ |
| Dynamical meaning | $a \gt 0$: backward (predecessor) move; $a \lt 0$: forward (successor) move |
| Family generated | The full Collatz tree (predecessors + their inverses), indexed by $(q, a) \in \mathbb{Z}_{\ge 0} \times \mathbb{Z}^\times$ with $a \in \pm\,2\cdot 3^q \cdot \mathbb{Z}_{\ge 1}$ |

The single-block shift, once $a$ is allowed to range over $\mathbb{Z}$, parametrizes the **full** Collatz tree (forward and backward moves). Structurally clean, but still the known tree — no new arithmetic content from one block alone, and (by the finite-support argument above) none from any finite combination of blocks either. The framework's potential lies entirely in **infinite-support** perturbations.
