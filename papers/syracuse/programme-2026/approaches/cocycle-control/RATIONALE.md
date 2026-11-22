# Cocycle-Control

A sibling of [`cocycle-combine`](../cocycle-combine/RATIONALE.md): same word-cocycle engine,
but the target is the **size / range** of $S(w)$ rather than its divisibility by $G=|D|$.

## Idea

We want a **thorough understanding of the range of $S(w)$ when $|w|$ is fixed**. With the
project-wide notation (a gap word $w=(d_0,\dots,d_{o-1})$, $d_k=e_{k+1}-e_k\ge1$, partial sums
$e_k$, $\operatorname{len}(w)=o$, $|w|=E=e_o$),
$$S(w)\;=\;\sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k}\qquad\big(=\;S(w)|_{(X,Y)=(2,3)}\text{ of }S=\textstyle\sum_k X^{e_k}Y^{o-1-k}\big).$$
Three concrete sub-goals:

1. **Statistics.** Numerically map the distribution of $S(w)$ over words with $|w|$ fixed
   (and, where useful, $\operatorname{len}(w)$ also fixed): min, max, spread, shape, and how
   they scale with $E$ and $o$.

2. **Monotone moves.** Find **simple transformations of $w$ that preserve $|w|$ and
   $\operatorname{len}(w)$ and provably increase or decrease $S$** — elementary "pivots" that
   step from one word to a comparable one.

3. **A lattice for $S$.** Use those moves to define a **partial order — ideally a lattice —
   on the set of words with fixed $|w|$ and fixed $\operatorname{len}(w)$, for which $S$ is
   monotone increasing**. Then the lattice's extremal/comparison structure gives simple
   "pivots" to compare words and to pin the extreme values $\min_w S$, $\max_w S$ over the
   fixed-$(E,o)$ stratum.

## Why it might work

- **The range of $S$ is the size knob behind every other approach.** On a cycle the start is
  $a_0=S^{(0)}/D$; in [`diophantine-distribution`](../diophantine-distribution/RATIONALE.md)
  the fundamental solution is $x_w^\ast=S(w)/D(w)$ and the imbalance factor
  $\eta\in[2^{-p},2^p]$ is exactly a normalized range-of-$S$ statement. Sharp control of
  $\min/\max S$ at fixed $|w|$ feeds all of these directly.
- **$S$ is a positive sum tied monotonically to the geometry of $w$.** Each term $2^{e_k}$ is
  weighted by a positive $3^{\,o-1-k}$, so moving gap-mass earlier (raising the $e_k$) pushes
  $S$ up and moving it later pushes $S$ down — strongly suggesting an honest monotone partial
  order exists, which is precisely sub-goal 3.
- **Fixed $(E,o)$ is a clean finite combinatorial universe.** Words with $|w|=E$,
  $\operatorname{len}(w)=o$ are the compositions of $E$ into $o$ positive parts; their
  partial-sum vectors $0\lt e_1\lt\cdots\lt e_{o-1}\lt E$ are a textbook setting for
  dominance-type lattices — a natural home for a provably $S$-monotone order.
- **The cocycle gives ready-made algebra.** $S(uv)=Y^{\operatorname{len}v}S(u)+X^{|u|}S(v)$
  and the transfer-matrix homomorphism (see
  [`cocycle-combine/structure/structure.md`](../cocycle-combine/structure/structure.md)) make
  block-swaps and single-gap transfers easy to express and to certify symbolically.

## Known prior art / why it isn't obviously dead

- The **trusted kernel already exists**:
  [`cocycle-combine/lib/cocycle.py`](../cocycle-combine/lib/cocycle.py) computes $S$, $D$,
  rotations and the cocycle identities, with symbolic + numeric certifiers — reusable verbatim
  for both the statistics and the monotonicity proofs here.
- Related but distinct: [`cycle-gcd`](../cycle-gcd/RATIONALE.md) and
  [`cocycle-combine`](../cocycle-combine/RATIONALE.md) study $\gcd_j S^{(j)}$ and divisibility;
  [`diophantine-distribution`](../diophantine-distribution/RATIONALE.md) has the
  $\eta\in[2^{-p},2^p]$ balanced-word bound. None of them isolates the **order structure** of
  $S$ at fixed $|w|$ — that is the gap this approach fills.
- Honest caveat: range-of-$S$ bounds are "size" facts, so on cycles they ultimately re-express
  bounds on $|2^E-3^o|$ (the same Baker/Matveev wall the sibling approaches hit). The bet is
  that the **order/lattice** view yields cheap, structural extremal words and comparison pivots
  that the divisibility view does not.
