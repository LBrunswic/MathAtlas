# Status — diophantine

## Current state

Scaffolded with notation **locked**: accelerated odd-to-odd (Syracuse) map, $a_k$ = $k$-th
odd term ($a_0$ odd start), $e_k$ = even steps before the $k$-th odd term ($e_0=0$, strictly
increasing), and LHS index $= o$. Canonical statement:
$$2^{e_o}\,a_o - 3^{o}\,a_0 = \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k}.$$
Proof not yet written.

## Results

- _(none yet — statement fixed, proof pending)_

## Dead ends

- _(none yet)_

## Open questions

- **Reconcile with `parity-manipulation`.** That approach uses $2^{b_n} x_n - 3^n x_0 =
  \sum_{k=0}^{n-1} 2^{b_k} 3^{n-1-k}$ with $b_k$ = cumulative halvings over *all* steps and
  exponent $3^n$. Our form indexes by *odd* steps ($3^o$, $e_k$ = evens before $k$-th odd).
  Confirm the two coincide under the re-indexing $n \leftrightarrow o$, $b_k \leftrightarrow
  e_k$, $x_k \leftrightarrow a_k$, and decide which is the project's canonical citation.
- **Corollaries to record** once the identity is proved: the rational/2-adic reconstruction
  $a_0 = -\sum_{k\ge0} 2^{e_k} 3^{-(k+1)}$ for cycles/limits; the cycle equation (set
  $a_o = a_0$); growth/size bounds from the identity.

## Next step under consideration

Write the iron-clad proof by induction on $o$: base case $o=1$ from
$2^{e_1} a_1 = 3 a_0 + 1$, inductive step multiplying the order-$o$ identity by $3$ and
adding $2^{e_o}(3a_o+1) = 2^{e_{o+1}} a_{o+1}$. Then add the reconciliation note.
