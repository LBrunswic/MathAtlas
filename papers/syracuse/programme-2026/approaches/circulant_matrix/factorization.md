# Determinant factorization and proposed identities

This note states the circulant matrix formula (recap of [`RATIONALE.md`](RATIONALE.md)), then
factors $\det M$ several ways. Each factorization is read as an **identity** — a candidate
a-priori handle on $\gcd_j S^{(j)}$ for the parent [`cycle-gcd`](../cycle-gcd/STATUS.md) program.
All identities below are verified numerically on the words $(2)$, $(1,2)$, and the test words
$(E,o)=(8,5),(7,4)$.

## 0. The matrix formula (recap)

For a gap word with even-step prefix sums $0=e_0\le e_1\le\dots\le e_o=E$ and $o$ odd steps,
the rotation sums $S^{(j)}$ (cycle-gcd) are the **row sums** of the integer matrix

$$M_{j,i}=2^{\,e_i-e_j+E\,\mathbf 1[i \lt j]}\;3^{\,o-1-((i-j)\bmod o)},\qquad \vec S=M\mathbf 1 .$$

With $t:=2^{E/o}$, $\tilde e_k:=e_k-\tfrac{k}{o}E$, $\Delta:=\operatorname{diag}(2^{\tilde e_k})$,
and $C$ the circulant of symbol $c_r=t^{\,r}\,3^{\,o-1-r}$ ($r=0,\dots,o-1$):

$$M=\Delta^{-1}C\Delta,\qquad C=3^{\,o-1}\,\operatorname{Circ}\!\big(1,\rho,\rho^2,\dots,\rho^{\,o-1}\big),\quad \rho:=t/3=2^{E/o}/3 .$$

Conjugation leaves the determinant unchanged: $\det M=\det C$.

## 1. Three factorizations of the determinant

**(1a) Spectral.** A circulant has eigenvalues $\hat c_\ell=\sum_r c_r\omega^{r\ell}$,
$\omega=e^{2\pi i/o}$. The symbol is geometric, so the sum telescopes ($\,(t\omega^\ell)^o=t^o=2^E$):

$$\hat c_\ell=3^{\,o-1}\sum_{r=0}^{o-1}(\rho\omega^\ell)^r
=3^{\,o-1}\,\frac{\rho^{\,o}-1}{\rho\omega^\ell-1}
=\frac{D}{\,t\,\omega^\ell-3\,},\qquad D:=2^E-3^o .$$

Hence $\det M=\prod_{\ell=0}^{o-1}\hat c_\ell=\dfrac{D^{\,o}}{\prod_\ell(t\omega^\ell-3)}$.

**(1b) Root-of-unity (resultant).** The denominator is a resultant value:

$$\prod_{\ell=0}^{o-1}\big(X-t\,\omega^\ell\big)=X^{o}-t^{o}=X^{o}-2^{E}$$

$$\Rightarrow_{\,X=3\,}\;\; \prod_{\ell=0}^{o-1}\big(3-t\,\omega^\ell\big)=3^{o}-2^{E}=-D .$$

So $\prod_\ell(t\omega^\ell-3)=(-1)^{o}(-D)=(-1)^{o+1}D$, giving

$$\boxed{\;\det M=\det C=(-1)^{o+1}\,D^{\,o-1}\;}$$

**(1c) Geometric-circulant.** Directly, $\det\operatorname{Circ}(1,\rho,\dots,\rho^{o-1})
=(-1)^{o+1}(\rho^{o}-1)^{o-1}$, and with $\rho^{o}-1=D/3^{o}$,

$$\det C=(3^{o-1})^{o}\,(-1)^{o+1}\Big(\tfrac{D}{3^{o}}\Big)^{o-1}
=(-1)^{o+1}D^{o-1},$$

the powers of $3$ cancelling exactly ($3^{o(o-1)}/3^{o(o-1)}$).

## 2. Proposed identities

### Identity A — factorization of $D$ over the $o$-th roots of $2^E$

From (1b), $|D|$ splits into $o$ explicit algebraic factors:

$$|2^E-3^o|=\prod_{\ell=0}^{o-1}\big|\,3-2^{E/o}\,\omega^\ell\,\big|
=\big|3-2^{E/o}\big|\prod_{\ell=1}^{\lfloor o/2\rfloor}\!\Big(9-6\cdot2^{E/o}\cos\tfrac{2\pi\ell}{o}+2^{2E/o}\Big).$$

The single real factor $|3-2^{E/o}|$ is the only one that can be small; it $\to0$ exactly when
$2^{E/o}\to3$, i.e. $E/o\to\log_2 3$ — the **critical regime** flagged in cycle-gcd
(criticality $\iff 2^E \lt 2\cdot 3^o$). So this realizes the size of $D$ as a product whose
"smallness" is localized in the gap between $2^{E/o}$ and $3$ — the linear-forms-in-logs
quantity — while the remaining $\lfloor o/2\rfloor$ quadratic factors are each $\gtrsim 1$ and
grow with $o$. *Proposed use:* lower-bound $|D|$ from the non-critical factors; the open part is
the one critical factor, exactly where Baker's theorem lives.

### Identity B — word-independence of the determinant

$\det M$ depends only on the totals $(E,o)$, **not** on the internal exponents
$e_1,\dots,e_{o-1}$:
$$\det M(\text{word})=(-1)^{o+1}D^{o-1}\qquad\text{for every gap word with given }(E,o).$$
(Because $M=\Delta^{-1}C\Delta$ and $C$ depends only on $E,o$.) The word structure lives entirely
in $\Delta$, which the determinant cannot see — it surfaces only in the off-diagonal/row-sum data
$\vec S=M\mathbf 1$. *Proposed use:* the gcd $\gcd_j S^{(j)}$ is the word-sensitive shadow of a
word-blind determinant — a clean separation of what the matrix "remembers."

### Identity C — cofactor certificate for the gcd

Since $\vec S=M\mathbf 1$, multiplying by the (integer) adjugate gives

$$\operatorname{adj}(M)\,\vec S=\det M\cdot M^{-1}\vec S=\det M\cdot\mathbf 1
=(-1)^{o+1}D^{\,o-1}\,\mathbf 1 .$$

Reading any single row $j$: with integer cofactors $A_{ji}:=\operatorname{adj}(M)_{ji}$,

$$\sum_{i=0}^{o-1} A_{ji}\,S^{(i)}=(-1)^{o+1}D^{\,o-1}\qquad(\text{each }j).$$

This is an **a-priori, divisibility-free certificate** (pure linear algebra over $\mathbb Z$) that
$$\gcd_{j}S^{(j)}\ \big|\ D^{\,o-1}.$$
It is weaker than the parent's $\gcd_j S^{(j)}\mid D$ (from the rotation recursion), but it is
*explicit*: it exhibits integer multipliers realizing $D^{o-1}$ as a $\mathbb Z$-combination of the
rotation sums. *Proposed use:* sharpen the cofactors. The recursion already gives the exponent $1$;
the goal is a cofactor identity $\sum_i B_{ji}S^{(i)}=\pm D$ with $B$ controlled a priori — that
would be the cycle-gcd open core, recast as a search for a low-degree syzygy among the $S^{(j)}$.

### Identity D — Leibniz/permutation identity in $(2,3)$

Expanding $\det M=(-1)^{o+1}D^{o-1}$ by Leibniz gives a two-variable power-product identity:

$$\sum_{\sigma\in \mathfrak S_o}\operatorname{sgn}(\sigma)\prod_{j=0}^{o-1}
2^{\,e_{\sigma(j)}-e_j+E\,\mathbf 1[\sigma(j) \lt j]}\,3^{\,o-1-((\sigma(j)-j)\bmod o)}
=(-1)^{o+1}\big(2^E-3^o\big)^{o-1}.$$

The left side is a signed sum of $o!$ monomials $2^a3^b$ with $a+b\log_2 3$ bounded; the right side
collapses to a pure power of $D$. *Proposed use:* the massive cancellation (from $o!$ terms down to
$D^{o-1}$) is itself structure — track which monomials survive mod a prime $p\mid D$ to read off
$p$-adic content of the rotations.

## 3. Where this points (for STATUS open questions)

- Identity A turns "$|D|$ is large unless critical" into an explicit factorization; pair with the
  cycle-gcd **criticality lemma** to isolate the one hard factor.
- Identities B–C separate the word-blind determinant ($\pm D^{o-1}$) from the word-sensitive gcd,
  and give an explicit cofactor certificate $\gcd_j S^{(j)}\mid D^{o-1}$. Refining C from $D^{o-1}$
  to $D^1$ — an a-priori syzygy among the $S^{(j)}$ — is the bridge to the open gcd bound.
- Next: compute the Smith normal form of $M$ (invariant factors multiply to $|D|^{o-1}$ by
  Identity B) and see how the $o-1$ copies of $D$ distribute — that distribution *is* the a-priori
  gcd content the parent program wants to bound.
