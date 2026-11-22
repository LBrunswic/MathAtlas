# Derivation: twisting one circuit into another via parity perturbation

## Motivation

A **circuit** in the Steiner / Crandall sense is a Collatz cycle whose parity vector has the shape
$$
(c_k) \;=\; (\underbrace{1, 1, \ldots, 1}_{a-1}, b, \;\underbrace{1, 1, \ldots, 1}_{a-1}, b, \;\ldots)
$$
i.e. periodic with period $a$ and a single "long gap" $b$ at the end of each block. Steiner (1977) ruled out positive $1$-circuits beyond the trivial cycle, and Simons–de Weger extended this to higher $m$. Both proofs lean on Baker-style lower bounds for $|C\log 2 - P\log 3|$ — the $\log_2 3$ Diophantine machinery.

We use circuits as a **test case** for the perturbation framework: take two periodic parity vectors (typically known cycles), engineer the perturbation $\delta = b' - b$ that twists one into the other, and check both that the framework reproduces the known difference $x_0 - x'_0$ and what new structural content the integrality condition does (or does not) give us.

This file establishes:

1. The general symbolic formula for $x_0 - x'_0$ between two periodic parity vectors sharing a common period.
2. A worked unit test: trivial cycle ($x_0 = 1$) twisted into the negative-$5$ cycle ($x'_0 = -5$).
3. A structural reading of when the integrality condition has bite versus when it is redundant with the per-cycle equations.

## Setup

Two periodic parity vectors with a common period $P$:
$$
b_{k+P} = b_k + C,\qquad b'_{k+P} = b'_k + C',\qquad b_0 = b'_0 = 0.
$$
Both are strictly increasing in $k$. Their 2-adic reconstructions
$$
x_0 = -\sum_{k\ge 0}\frac{2^{b_k}}{3^{k+1}}, \qquad x'_0 = -\sum_{k\ge 0}\frac{2^{b'_k}}{3^{k+1}}
$$
converge in $\mathbb{Z}_2$ and are rational (closed-form below).

### Cycle formula (single periodic series)

Splitting $k = nP + r$ with $0 \le r \lt P$ and summing the geometric series in $n$:
$$
x_0 \;=\; -\sum_{r=0}^{P-1}\frac{2^{b_r}}{3^{r+1}}\cdot\frac{1}{1 - 2^C/3^P}
\;=\; \frac{1}{2^C - 3^P}\sum_{r=0}^{P-1} 2^{b_r}\,3^{P-1-r}.
$$
Writing $S := \sum_{r=0}^{P-1} 2^{b_r}\,3^{P-1-r}$ and similarly $S'$ for the primed vector:
$$
x_0 = \frac{S}{2^C - 3^P}, \qquad x'_0 = \frac{S'}{2^{C'} - 3^P}.
$$

For $x_0$ to be an honest integer, $(2^C - 3^P) \mid S$ — this is the standard Steiner cycle equation.

### Difference formula

The mean-gap difference is $\alpha := C'/P - C/P = (C' - C)/P$. The perturbation $\delta(k) := b'_k - b_k$ satisfies $\delta(k+P) = \delta(k) + (C' - C)$, so $\delta$ decomposes as
$$
\delta(k) \;=\; \alpha k \;+\; \pi(k), \qquad \pi \text{ periodic with period } P.
$$
A purely periodic perturbation ($\alpha = 0$) requires $C = C'$. Otherwise $\delta$ carries a linear drift, with slope tied to the difference of mean gaps.

Subtracting closed forms:
$$
\boxed{\;
x_0 - x'_0 \;=\; \frac{S}{2^C - 3^P} \;-\; \frac{S'}{2^{C'} - 3^P}
\;=\; \frac{(2^{C'} - 3^P)\,S \;-\; (2^C - 3^P)\,S'}{(2^C - 3^P)(2^{C'} - 3^P)}.
\;}
$$

The denominator $(2^C - 3^P)(2^{C'} - 3^P)$ contains the two Steiner-style obstructions; the numerator is a $\mathbb{Z}$-linear combination of the head sums.

## Unit test: trivial $\leftrightarrow$ $-5$ cycle

| | Period $P$ | Sum $C$ | Vector $b_r$ ($r = 0, 1$) | Head sum |
|---|---|---|---|---|
| Trivial cycle, $x_0 = 1$ | $2$ | $4$ | $0,\ 2$ | $S = 1\cdot 3 + 4\cdot 1 = 7$ |
| $-5$ cycle, $x'_0 = -5$ | $2$ | $3$ | $0,\ 1$ | $S' = 1\cdot 3 + 2\cdot 1 = 5$ |

(The trivial cycle has fundamental period $1$ with $C=2$, but we lift it to period $2$ to share a common $P$ with the $-5$ cycle. The lifted form is $b_k = 2k$, gaps $(2,2,\ldots)$.)

**Cycle formula check.**
$$
x_0 = \frac{7}{2^4 - 3^2} = \frac{7}{7} = 1,\qquad x'_0 = \frac{5}{2^3 - 3^2} = \frac{5}{-1} = -5. \;\checkmark
$$

**Difference via the boxed formula.**
$$
x_0 - x'_0 \;=\; \frac{(2^3 - 3^2)\cdot 7 \;-\; (2^4 - 3^2)\cdot 5}{(2^4 - 3^2)(2^3 - 3^2)}
\;=\; \frac{(-1)\cdot 7 \;-\; 7\cdot 5}{7 \cdot (-1)}
\;=\; \frac{-42}{-7} \;=\; 6. \;\checkmark
$$

**Direct termwise verification.** Split by parity of $k$, with $k = 2j$ giving $b_{2j} = 4j,\ b'_{2j} = 3j$ and $k = 2j+1$ giving $b_{2j+1} = 4j+2,\ b'_{2j+1} = 3j+1$:
$$
x_0 - x'_0 \;=\; \sum_{j\ge 0}\left[\frac{2^{3j} - 2^{4j}}{3^{2j+1}} + \frac{2^{3j+1} - 2^{4j+2}}{3^{2j+2}}\right]
\;=\; \sum_{j\ge 0}\frac{5\cdot 8^j \;-\; 7\cdot 16^j}{9^{j+1}}.
$$
Both geometric series converge in $\mathbb{Z}_2$:
$$
= \frac{5}{9}\cdot\frac{1}{1 - 8/9} - \frac{7}{9}\cdot\frac{1}{1 - 16/9}
\;=\; \frac{5}{9}\cdot 9 - \frac{7}{9}\cdot\frac{-9}{7}
\;=\; 5 - (-1) \;=\; 6. \;\checkmark
$$

**Perturbation shape.** $\delta(k) = b'_k - b_k$ evaluates as $\delta(2j) = -j$, $\delta(2j+1) = -j - 1$, so $\delta(k) = -\lceil k/2 \rceil$. This is **linear with slope $-1/2$ plus a periodic correction** — forced by $C - C' = 1$, $P = 2$, giving $\alpha = -1/2$.

## Reading the unit test

**The integrality of $x_0 - x'_0$ is redundant here.** Both $x_0$ and $x'_0$ are integers by their respective cycle equations $(2^C - 3^P) \mid S$ and $(2^{C'} - 3^P) \mid S'$. So integrality of the difference contains *no information beyond* the two cycle equations individually. The unit test is a consistency check on the framework, not a new structural constraint.

**Where the framework has leverage: the asymmetric setup.** Suppose $x_0$ is a *hypothetical* integer cycle (e.g. some unproven $m$-circuit) and $x'_0$ is a *known* one ($1$, $-5$, $-17$). Then the integrality of $x_0 - x'_0$ couples the unknown cycle equation $(2^C - 3^P) \mid S$ to a concrete integer, turning a Diophantine relation in $(P, C, S)$ into a *single* equation rather than a divisibility-plus-existence claim. Combined with the Baker / continued-fraction control on $|C \log 2 - P\log 3|$, this may force constraints that the cycle equation alone does not.

**Where the linear part lives.** The mean-gap slope $\alpha = (C' - C)/P$ is forced by the choice of source and target. For any two cycles with $C/P, C'/P'$ close to $\log_2 3$, $\alpha$ is rational with bounded denominator. The "smoothing" picture is then:
- The **linear part** $\alpha k$ absorbs the mean-gap drift between source and target — exactly the quantity controlled by Baker / Crandall–Lagarias.
- The **periodic part** $\pi(k)$ encodes the residual combinatorial twist after the drift is normalized away.

So a perturbation framework operating on $(\alpha, \pi)$ separates the Diophantine-approximation regime from the residual combinatorics, rather than tangling them together as raw gap sequences do.

## Open questions

- **Symmetric setup, generic periodic targets.** Beyond circuits, what does the difference formula say when $b'$ is an arbitrary periodic vector? The numerator $(2^{C'} - 3^P)S - (2^C - 3^P)S'$ is a bilinear form in the head sums and the cycle denominators. Does it factor non-trivially modulo specific primes?
- **Asymmetric one-sided test.** Pick a hypothetical $m$-circuit shape (e.g. $a = 17, b = 27$, just past the Simons–de Weger range), twist onto the trivial cycle, write down the integrality condition. Does it produce a Diophantine statement *cleaner* than the cycle equation itself?
- **The linear-plus-periodic decomposition.** Does treating $(\alpha, \pi)$ as independent parameters — rather than recovering them from $(b, b')$ — give a tractable parameter space in which to search for genuinely new arithmetic content?
- **Negative cycles as a probe.** $-5, -17$ are the natural "other endpoints" for twists from any positive integer trajectory. The mean gaps $3/2$ and $\approx 1.636$ bracket the trivial $2$ from below. Is there leverage in expressing a hypothetical positive non-trivial cycle as a sum of twists toward each of the three known cycles?
