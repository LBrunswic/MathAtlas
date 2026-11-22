# Cycle-GCD

## Idea

Attack the **finiteness of Syracuse cycles** through the divisor structure of the
[`diophantine`](../diophantine/RATIONALE.md) closed form.

Setting $a_o = a_0$ (a cycle) in the core identity gives the **cycle equation**
$$(2^{E}-3^{o})\,a_0 \;=\; \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k} \;=:\; S^{(0)},
\qquad E := e_o .$$
So $D := 2^{E}-3^{o}$ must divide the RHS sum, and $a_0 = S^{(0)}/D$.

A cycle is invariant under **cyclic shift of its even–odd (gap) word**: starting the same
periodic orbit at $a_j$ produces the analogous sum $S^{(j)}$ with the *same* denominator
$D$ (it depends only on the rotation-invariant totals $E,o$). Hence $D$ divides **every**
shift $S^{(j)}$, so
$$D \;\big|\; \gcd_{0\le j\lt o} S^{(j)} .$$

The strategy: bound $\gcd_j S^{(j)}$ **from above**, a priori, using only the combinatorial
structure of the gap word. Such a bound $\gcd_j S^{(j)} \le f(o)$ forces
$|2^{E}-3^{o}| \le f(o)$ for any cycle, which (for $f$ growing slower than the typical size
of $\min_E|2^E-3^o|$) leaves only finitely many admissible $(E,o)$ — hence finitely many
cycles.

## Why it might work

Two facts make the reformulation clean (both proved, see STATUS):

1. **Rotation recursion (algebraic).** For a gap word $w$ and its left rotation $w'$,
   $$2^{d_0}\,S(w') = 3\,S(w) + D ,$$
   holding over $\mathbb{Z}$ for *any* word — no oddness/positivity needed.
2. **Exact gcd on cycles.** The recursion forces $\gcd_j S^{(j)} \mid D$ for every word;
   combined with the cycle condition $D \mid \gcd_j S^{(j)}$, a genuine cycle has
   $$\gcd_{j} S^{(j)} = |2^{E}-3^{o}| \quad\text{exactly.}$$

This turns "are there other cycles?" into a self-contained question about the gcd of the
rotations of a single integer sum — no reference to the dynamics beyond the gap word.

## Known prior art / why it isn't obviously dead

- The cycle equation and $D = 2^E-3^o$ are classical (Lagarias survey). Finiteness of cycles
  with a **bounded number of circuits** is known: Steiner (1977, 1-circuit), Simons–de Weger
  (multi-circuit, up to 68). General finiteness is open.
- The honest barrier: because $\gcd_j S^{(j)} = |D|$ *exactly* on cycles, any a-priori upper
  bound on the gcd is equivalent to a **lower bound on $|2^E-3^o|$** as a function of $o$ —
  i.e. linear forms in logarithms / Baker's theorem territory. The value of this approach is
  to phrase the open part as a crisp, elementary divisibility/gcd question and to see whether
  the combinatorial structure of the rotations yields a bound more cheaply than transcendence
  theory.

_Open task: pin down what an a-priori bound on $\gcd_j S^{(j)}$ could come from — small-prime
reductions of the rotations, or the spread of the $2^{e_k}$ digits. See STATUS.md._
