# Diophantine

## Idea

A foundational, citable statement of the closed-form Diophantine identity linking the
$n$-th term of a Collatz/Syracuse trajectory back to its first term, under the assumption
that we start from an **odd** number and track the trajectory by its odd terms.

The target identity (to be stated and proved with iron-clad rigor and clean notation) is
$$2^{e_o}\,a_o \;-\; 3^{o}\,a_0 \;=\; \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k},$$
where:

- $a_0$ is the (odd) starting value and $a_1, a_2, \dots$ are the **subsequent odd terms**
  produced by the accelerated (odd-to-odd / Syracuse) map
  $$a_{k+1} = \frac{3a_k + 1}{2^{\,e_{k+1}-e_k}},$$
  i.e. each step applies $3x+1$ once and then divides out every factor of $2$;
- $o \ge 1$ is the index of the final odd term under consideration (so the LHS subscript is
  exactly $o$);
- $e_k$ is the number of even steps occurring **before** the $k$-th odd term, with $e_0 = 0$;
  equivalently $e_{k+1} - e_k = \nu_2(3a_k+1) \ge 1$ and $(e_k)$ is strictly increasing.

This approach is **infrastructure**: the identity (and its corollaries) will be reused
across the other approaches, so the notation choices here are binding and must be fixed
carefully, and every claim must have a complete proof.

## Why it might work

(This approach is not itself a proof strategy for the conjecture — it is the elementary
toolkit the other approaches build on. "Working" here means: a clean, unambiguous notation
and a fully rigorous derivation of the identity and its immediate corollaries.)

_To be filled in with the user once notation and scope are pinned down._

## Known prior art / why it isn't obviously dead

The closed form is classical (it is the standard parity-vector / 2-adic identity; see the
Lagarias survey and the related statement recorded in the `parity-manipulation` approach,
which writes it as $2^{b_n} x_n - 3^n x_0 = \sum_{k=0}^{n-1} 2^{b_k} 3^{n-1-k}$ with $b_k$
the cumulative count of halvings). The value added here is purely a matter of **rigor and
notational hygiene**: a single canonical statement, with proof, that the rest of the project
can cite without re-deriving.

_Notation reconciliation with `parity-manipulation` ($b_k$ vs. $e_k$, $x_k$ vs. $a_k$,
exponent $3^n$ vs. $3^o$) is an explicit open task — see STATUS.md._
