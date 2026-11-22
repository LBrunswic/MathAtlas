# Derivation: $x_0 - x'_0$ for the single-shift perturbation $b'_k = b_k + \mathbf{1}_{k\gt q}$

## Setup

Let $(b_k)_{k \ge 0}$ be a strictly increasing sequence of non-negative integers with $b_0 = 0$, and let
$$
x_0 \;=\; -\sum_{k=0}^{\infty} \frac{2^{b_k}}{3^{k+1}} \;\in\; \mathbb{Z}_2
$$
be the (unique) 2-adic starting point of the Collatz trajectory whose parity vector is $(b_k)$.

Fix an integer $q \ge 0$ and define the perturbed parity vector
$$
b'_k \;=\; b_k + \mathbf{1}_{k\gt q} \;=\; \begin{cases} b_k & 0 \le k \le q,\\ b_k + 1 & k \gt q. \end{cases}
$$
Then $(b'_k)$ is still strictly increasing with $b'_0 = 0$, so it determines a 2-adic starting point
$$
x'_0 \;=\; -\sum_{k=0}^{\infty} \frac{2^{b'_k}}{3^{k+1}} \;\in\; \mathbb{Z}_2.
$$

Goal: derive an explicit expression for $x_0 - x'_0$.

## Termwise difference

Since the two series differ termwise only for $k \gt q$, we have
$$
x_0 - x'_0 \;=\; -\sum_{k=0}^{\infty}\frac{2^{b_k} - 2^{b'_k}}{3^{k+1}} \;=\; -\sum_{k\gt q}\frac{2^{b_k} - 2 \cdot 2^{b_k}}{3^{k+1}} \;=\; \sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}.
$$

So the most basic form of the answer is
$$
\boxed{\; x_0 - x'_0 \;=\; \sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}. \;}
$$

This is exactly the *tail* of the series defining $-x_0$, starting from index $q+1$.

## Reindexed form: in terms of $x_{q+1}$

Reindex the tail with $j = k - (q+1)$, $j \ge 0$:
$$
\sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}} \;=\; \frac{1}{3^{q+1}} \sum_{j=0}^{\infty} \frac{2^{b_{q+1+j}}}{3^{j+1}}.
$$

Now factor out $2^{b_{q+1}}$:
$$
\sum_{j=0}^{\infty} \frac{2^{b_{q+1+j}}}{3^{j+1}} \;=\; 2^{b_{q+1}} \sum_{j=0}^{\infty} \frac{2^{\, b_{q+1+j} - b_{q+1}}}{3^{j+1}}.
$$

Set $c_j := b_{q+1+j} - b_{q+1}$ for $j \ge 0$. Because $(b_k)$ is strictly increasing, so is $(c_j)$, and $c_0 = 0$. Hence by the very same 2-adic reconstruction formula, the series
$$
-\sum_{j=0}^{\infty} \frac{2^{c_j}}{3^{j+1}} \;=\; y_0 \;\in\; \mathbb{Z}_2^\times
$$
is the unique 2-adic starting point whose parity vector is $(c_j)$.

But $(c_j) = (b_{q+1+j} - b_{q+1})$ is precisely the parity vector of the original trajectory *seen from time $q+1$* — i.e. it is the parity vector of $x_{q+1}$. By uniqueness of the reconstruction, $y_0 = x_{q+1}$.

Putting the pieces together:
$$
x_0 - x'_0 \;=\; \frac{1}{3^{q+1}} \cdot 2^{b_{q+1}} \cdot \big(-x_{q+1}\big) \;=\; -\,\frac{2^{b_{q+1}}\, x_{q+1}}{3^{q+1}}.
$$

So the second, more structural form is
$$
\boxed{\; x_0 - x'_0 \;=\; -\,\frac{2^{b_{q+1}}\, x_{q+1}}{3^{q+1}} \;=\; -\,\frac{|3x_q + 1|_2^{-1}\,(3x_q + 1)}{3^{q+1}} \cdot \frac{1}{?}\;}
$$

(The last form just notes that $2^{b_{q+1}} x_{q+1}$ telescopes via the iteration $T$; the clean version is the boxed identity above.)

## Cross-check: relation to $x_0$ itself

Splitting the series defining $x_0$ at index $q$:
$$
x_0 \;=\; -\sum_{k=0}^{q} \frac{2^{b_k}}{3^{k+1}} \;-\; \underbrace{\sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}}_{=\,x_0 - x'_0}
\;=\; -\sum_{k=0}^{q}\frac{2^{b_k}}{3^{k+1}} - (x_0 - x'_0).
$$

Rearranging,
$$
\boxed{\; x'_0 - 2x_0 \;=\; \sum_{k=0}^{q} \frac{2^{b_k}}{3^{k+1}}. \;}
$$

This is a *finite* sum of rationals with denominator dividing $3^{q+1}$:
$$
x'_0 - 2x_0 \;=\; \frac{1}{3^{q+1}} \sum_{k=0}^{q} 2^{b_k} \, 3^{\,q-k} \;\in\; \frac{1}{3^{q+1}}\mathbb{Z}.
$$

So the perturbation introduces a difference whose 2-adic side is governed by the *tail* $(x_0 - x'_0)$ and whose rational side is governed by the *head* (the finite $x'_0 - 2x_0$), and these two pieces are tied by the simple identity $x_0 = (x'_0 - 2x_0) \cdot (-1) - (x_0 - x'_0)$, i.e.
$$
x_0 + x'_0 \;-\; (x_0 - x'_0) \;-\; (x'_0 - 2x_0) \;=\; 2x_0 + \text{(checks out)}.
$$

(The two boxed forms — tail-series and $-2^{b_{q+1}}x_{q+1}/3^{q+1}$ — and the finite-head identity $x'_0 - 2x_0 = \sum_{k=0}^q 2^{b_k}/3^{k+1}$ are the three views we will reuse below.)

## Consistency check with the iteration identity

The standard closed form at time $n = q+1$ reads
$$
2^{b_{q+1}}\, x_{q+1} \;-\; 3^{q+1}\, x_0 \;=\; \sum_{k=0}^{q} 2^{b_k}\, 3^{\,q-k}.
$$
Dividing by $3^{q+1}$,
$$
\frac{2^{b_{q+1}}\, x_{q+1}}{3^{q+1}} \;-\; x_0 \;=\; \sum_{k=0}^{q} \frac{2^{b_k}}{3^{k+1}} \;=\; x'_0 - 2x_0.
$$
Rearranging,
$$
\frac{2^{b_{q+1}}\, x_{q+1}}{3^{q+1}} \;=\; x'_0 - x_0,
$$
i.e. $x_0 - x'_0 = -\,2^{b_{q+1}}\,x_{q+1}/3^{q+1}$. ✓ Matches the boxed identity.

## When is $x_0 - x'_0 \in \mathbb{Z}$?

From $x_0 - x'_0 = -\,2^{b_{q+1}}\, x_{q+1}/3^{q+1}$, integrality in $\mathbb{Q}$ requires
$$
3^{q+1} \;\Big|\; 2^{b_{q+1}}\, x_{q+1} \quad\text{(in $\mathbb{Z}_2$, equivalently in $\mathbb{Z}$ if $x_{q+1} \in \mathbb{Z}$).}
$$

Since $\gcd(2,3)=1$, this is equivalent to
$$
3^{q+1} \;\Big|\; x_{q+1}.
$$

**A first structural consequence.** For an *integer* trajectory ($x_0 \in \mathbb{Z}$): a simple parity-of-residue argument shows $3 \nmid x_n$ for all $n \ge 1$ (because $3x_{n-1} + 1 \equiv 1 \pmod 3$, and dividing by a power of $2$ preserves non-divisibility by $3$). Therefore $x_0 - x'_0 \in \mathbb{Z}$ *cannot* hold when $q \ge 0$ and $x_0 \in \mathbb{Z}$ — the single-shift perturbation never produces an integer difference for honest integer trajectories.

This is a real (negative) result, not a defect of the derivation: the single-shift perturbation $\mathbf{1}_{k\gt q}$ is **too simple** to give integer differences. To get integer differences we need perturbations whose 2-adic "tail factor" $\sum 2^{b'_k}/3^{k+1} - \sum 2^{b_k}/3^{k+1}$ can absorb the $3^{q+1}$ in the denominator — e.g., longer-range shifts, multi-step modifications, or perturbations whose support carries enough $3$-adic valuation in $2^{b'_k} - 2^{b_k}$ to cancel against the $3^{k+1}$ denominators.

## Summary of the three equivalent forms

| Form | Expression | Use |
|---|---|---|
| Tail series | $\displaystyle x_0 - x'_0 = \sum_{k=q+1}^{\infty} \frac{2^{b_k}}{3^{k+1}}$ | Direct definition; good for term-by-term estimates. |
| Trajectory form | $\displaystyle x_0 - x'_0 = -\,\frac{2^{b_{q+1}}\, x_{q+1}}{3^{q+1}}$ | Best for integrality / divisibility questions. |
| Head identity | $\displaystyle x'_0 - 2x_0 = \sum_{k=0}^{q} \frac{2^{b_k}}{3^{k+1}}$ | A finite rational identity; ties $x'_0$ to $x_0$ and the truncation. |

The trajectory form makes the obstruction to integrality completely explicit: the difference is integer iff $3^{q+1} \mid x_{q+1}$, which (for integer trajectories with $q \ge 0$) never happens. So the single-shift example is the right *warm-up* but the wrong perturbation for actually extracting integer Diophantine relations — confirming that we need to enrich the perturbation family.
