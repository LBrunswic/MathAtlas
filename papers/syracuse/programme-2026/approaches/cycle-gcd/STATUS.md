# Status — cycle-gcd

## Current state

Active — strategy scaffolded with proved structural results (closed form, rotation recursion,
exact gcd identity, criticality reduction). The general a-priori gcd bound is still open, but a
**first concrete instance** is now in hand: for eventually-periodic words $w^q w'$ the gcd of
shifts divides a $q$-independent integer $C(w,w')$ (see [`periodic-words.md`](periodic-words.md)).

Formal Lemma/Theorem development with full proofs: [`theorems.md`](theorems.md)
(Prop. 2.1 closed form · Lemma 3.1 rotation recursion · Cor. 3.2 / Thm. 3.3 gcd · Lemma 4.2 +
Thm. 4.3 criticality · Prop. 4.4 size-route counterexample).

Periodic-word sub-development: [`periodic-words.md`](periodic-words.md) (Lemma 1.2 cocycle ·
Lemma 1.3 antisymmetry · Thm. 2.1 block telescoping · Prop. 3.1 / Cor. 3.2 $q$-free gcd bound).

Self-contained Bourbaki-style article (the $w=u^qv$ case, general bound → Matveev exclusion
zone): [`eventually-periodic.tex`](eventually-periodic.tex) → `eventually-periodic.pdf`
(compiles with `pdflatex`, 8 pp). §1 rebuilds the cocycle calculus (closed form, length/gap-sum
characters, concatenation cocycle, transfer-matrix homomorphism $M(uv)=M(u)M(v)$, rotation
recursion, $\gcd_j S^{(j)}=|D|$ on cycles); §2 does $w=u^qv$ with **no a-priori hypothesis on
$u,q,v$**: telescoping → $|2^E-3^o|\mid C(u,v)$ (Thm 2.3), $q$-free upper bound
$|C|<2^{a+b}3^{m+\ell}$ (Lem 2.5), explicit Matveev lower bound $2^E-3^o>3^o e^{-c_0(1+\log E)}$,
$c_0\approx5.86\times10^8$ (Prop 2.8), combined into the exclusion inequality
$(q-1)m\log3 < (a+b)\log2 + c_0(1+\log E)$ (Thm 2.9, LHS linear / RHS log in $q$ ⟹ effective
$q\le Q(u,v)$), then the critical-band simplification $3^o<2^E<3^{o+1}$ applied **after** Matveev
(Thm 2.13, pins $E$ to ≤2 values per $o$).

## Results

- **Cycle equation.** Setting $a_o=a_0$ in the [`diophantine`](../diophantine/STATUS.md)
  identity: $(2^{E}-3^{o})\,a_0 = S^{(0)} := \sum_{k=0}^{o-1}2^{e_k}3^{o-1-k}$, with
  $E:=e_o$. So $D:=2^{E}-3^{o}$ divides $S^{(0)}$ and $a_0 = S^{(0)}/D$.

- **Rotation recursion (proved, algebraic).** For a gap word $w=(d_0,\dots,d_{o-1})$
  ($d_k=e_{k+1}-e_k$) and its left rotation $w'=(d_1,\dots,d_{o-1},d_0)$, with $S(\cdot)$ the
  RHS sum of the word:
  $$2^{d_0}\,S(w') \;=\; 3\,S(w) \;+\; D .$$
  Derivation: with $e'_k = e_{k+1}-d_0$,
  $S(w') = 2^{-d_0}\!\sum_{j=1}^{o}2^{e_j}3^{o-j} = 2^{-d_0}\big[(3S(w)-3^o)+2^E\big]
  = 2^{-d_0}\big[3S(w)+D\big]$. Needs only the partial-sum bookkeeping — no oddness/positivity.

- **GCD divides $D$ (proved).** Any common divisor of $S(w),S(w')$ divides
  $2^{d_0}S(w')-3S(w)=D$. Iterating over all rotations: $\gcd_j S^{(j)} \mid D$ for every word.

- **Exact gcd on cycles (proved).** For a genuine cycle the condition $D\mid S^{(j)}$ (all $j$)
  gives $D\mid\gcd_j S^{(j)}$; with the above, $\gcd_j S^{(j)} = |2^{E}-3^{o}|$.

- **Criticality lemma (proved).** Call $(E,o)$ with $2^E\gt 3^o$ **critical** if $2^E-3^o$ is
  minimal over $E'$ (same $o$), i.e. $E=\lceil o\log_2 3\rceil$ (note $o\log_2 3\notin\mathbb Z$,
  so this $E$ is the unique integer in $(o\log_2 3,\,o\log_2 3+1)$). Then:
  - **Dichotomy.** $(E,o)$ non-critical $\iff E\gt o\log_2 3+1 \iff 2^{E-1}\gt 3^o$.
  - **Gap bound.** non-critical $\Rightarrow 2^E-3^o = 2^{E-1}+(2^{E-1}-3^o) \gt 2^{E-1}$.

- **Reduction of "every cycle is critical" (proved).** A positive cycle has $a_0=S^{(0)}/D\ge1$
  with $S^{(0)}\gt 0$, so $D=2^E-3^o\gt 0$ ($2^E\gt 3^o$ always). By the dichotomy, the cycle is critical
  $\iff 2^E\lt 2\cdot3^o \iff \prod_{k=0}^{o-1}(1+\tfrac1{3a_k})\lt 2$ (using $2^E=\prod_k\frac{3a_k+1}{a_k}$).
  Trivial cycle: $4/3\lt 2$ ✓. Primitivity is required — the imprimitive word $(2,2,2)=3\times(2,1)$
  gives non-critical $(E,o)=(6,3)$ with $a_j\equiv1$ (trivial cycle traversed thrice).

- **Eventually-periodic words $w^q w'$ (proved + verified)** — [`periodic-words.md`](periodic-words.md).
  Working in $\mathbb{Z}[X,Y]$ ($X\!\to\!2$ gap-sums, $Y\!\to\!3$ positions): a concatenation
  cocycle $S(uv)=Y^{\operatorname{len}(v)}S(u)+X^{|u|}S(v)$ yields the **block-telescoping**
  $S(w^qw')-S(w^{q-1}w'w)=X^{(q-1)|w|}\,C(w,w')$ with $q$-free core
  $C(w,w')=S(ww')-S(w'w)=D(w)S(w')-D(w')S(w)$. At $(2,3)$, since $D$ is odd, the shift gcd is
  coprime to $2$, so $\gcd_j S^{j}(w^qw')\mid C(w,w')$ — an **a-priori, $q$-independent** ceiling.
  Hence a cycle in the family forces $|2^E-3^o|\mid C(w,w')$: either $C=0$ or
  $|2^E-3^o|\le|C|$, so only finitely many $q$ per $(w,w')$ (verified $q\le6$ over several
  families). Degenerate locus $C=0\iff S(w)/D(w)=S(w')/D(w')$ (shared fixed point; contains
  $w'=w$, the pure-circuit case → known Steiner / Simons–de Weger finiteness).

- **Worked checks.**
  - Trivial $1\to1$: word $(2)$, $E=2,o=1$, $D=1$, $S^{(0)}=1$, $a_0=1$. ✓
  - Negative $-5\to-7$: word $(1,2)$, $E=3,o=2$, $D=-1$, $S^{(0)}=5$, $S^{(1)}=7$,
    $a_0=-5,a_1=-7$; recursion $2^1\cdot7 = 3\cdot5+(-1)$ ✓; $\gcd(5,7)=1=|D|$ ✓.

## Dead ends

- Bounding the gcd using anything that already assumes the cycle/divisibility is circular:
  it returns $|D|$ by the exact-gcd identity. The bound must be **a priori** (word structure
  only).
- **Size alone cannot prove criticality.** The natural finish — non-critical $\Rightarrow
  D\gt 2^{E-1}$ (gap bound) $\Rightarrow \min_j S^{(j)}\le 2^{E-1}\lt D \Rightarrow a_j\lt 1$ — fails
  because the size inequality $\min_j S^{(j)}\le 2^{E-1}$ is **false at the word level**.
  Witness $(E,o)=(9,5)$, primitive word $(1,2,2,2,2)$: $D=512-243=269$ but the rotation sums
  are $\{431,485,557,653,781\}$, so $\min_j S^{(j)}=431\gt 269=D$ — every $a_j\gt 1$. It is excluded
  as a cycle only because $269\nmid431$ ($\gcd$ of rotations $=1$): the **arithmetic** layer,
  not size. So criticality, if true, is not a counting fact — it needs the divisibility/gcd
  ([[cycle-gcd]] core) or transcendence (Baker) input.

## Open questions

- **Quantitative finiteness for $w^q w'$ (the live thread).** Trivial $q$-free bound proved:
  $|C(w,w')|\lt 2^{|w|+|w'|}3^{\operatorname{len}(w)+\operatorname{len}(w')}$ (the smaller
  $2^{|w'|}3^{\cdots}$ is false). Feed it to a
  Matveev lower bound on $|2^E-3^o|$ to get an explicit threshold on $(q,w,w')$. Characterize the
  $C=0$ stratum (integer vs. polynomial identity) and check it coincides with the bounded-circuit
  cases. See [`periodic-words.md`](periodic-words.md) §5.
- **A-priori upper bound on $\gcd_j S^{(j)}$.** Find $f(o)$ with $\gcd_j S^{(j)}\le f(o)$ for
  all gap words, derived from combinatorial structure (e.g. reductions mod small primes of the
  rotated sums, or the digit spread of the $2^{e_k}$). Any such $f$ growing slower than the
  typical $\min_E|2^E-3^o|$ yields finiteness.
- **Relation to known bounds.** Quantify the equivalence "a-priori gcd bound $\iff$ lower
  bound on $|2^E-3^o|$" and compare to Baker / Steiner / Simons–de Weger. Is the gcd phrasing
  ever cheaper, e.g. for restricted word classes (bounded circuits)?
- **Positivity layer.** The exact-gcd identity uses only $a_j\in\mathbb{Z}$. Fold in
  $a_j\ge1$ (positive cycles) and the standard $a_{\min}$ size bounds to see if they tighten
  the candidate $(E,o)$ range.
- **Close criticality via arithmetic.** The reduction leaves $2^E\lt 2\cdot3^o$ (equiv.
  $\prod_k(1+\tfrac1{3a_k})\lt 2$) for primitive cycles. Since the size-only route is dead (see
  Dead ends), try to kill the surviving non-critical witnesses (e.g. $(9,5)$, word
  $(1,2,2,2,2)$) with the divisibility/gcd machinery directly: does $\gcd_j S^{(j)}\mid D$
  with $\gcd_j S^{(j)}\lt D$ hold for every non-critical primitive word?

## Next step under consideration

Numerically tabulate $\gcd_j S^{(j)}$ over random/structured gap words (not assuming
divisibility) to see how large it gets relative to $|2^E-3^o|$, and whether a clean a-priori
ceiling is plausible before attempting a proof.
