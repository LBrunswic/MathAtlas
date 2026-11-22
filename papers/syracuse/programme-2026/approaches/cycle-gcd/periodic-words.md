# Periodic gap words $w^q w'$ in $\mathbb{Z}[X,Y]$

A focused sub-development of [`cycle-gcd`](RATIONALE.md), specializing the rotation/gcd
machinery of [`theorems.md`](theorems.md) to **eventually-periodic gap words** $\tau = w^q w'$.
The payoff: for fixed blocks $(w,w')$ the gcd of the cyclic shifts divides a single integer
$C(w,w')$ that does **not** depend on $q$, while on a genuine cycle that gcd equals
$|2^E-3^o|$, which grows exponentially in $q$. So a cycle in the family forces
$|2^E-3^o| \mid C(w,w')$ — finitely many $q$ unless $C=0$. A Matveev linear-forms-in-logs
lower bound on $|2^E-3^o|$ is meant to turn this into quantitative, uniform finiteness over
$(q,w,w')$.

Conventions follow [`theorems.md`](theorems.md). The only new device is to keep $2$ and $3$ as
indeterminates.

---

## 1. The polynomial sum functional

**Definition 1.1.** Lift the sum functional to $\mathbb{Z}[X,Y]$, with $X$ tracking the
power-of-two gap sums and $Y$ the power-of-three positions. For a gap word
$w=(d_0,\dots,d_{n-1})$ of positive integers, write $n=\operatorname{len}(w)$,
$|w|=\sum_i d_i$, and partial sums $e_0=0,\ e_k=\sum_{i\lt k}d_i$. Set
$$
S(w) \;=\; \sum_{k=0}^{n-1} X^{e_k}\,Y^{\,n-1-k} \;\in\; \mathbb{Z}[X,Y],
\qquad
D(w) \;=\; X^{|w|} - Y^{\,n}.
$$
Specializing $(X,Y)=(2,3)$ recovers $S(w)=\sum_k 2^{e_k}3^{n-1-k}=S^{(0)}$ and
$D(w)=2^{E}-3^{o}$ of [`theorems.md`](theorems.md) (with $E=|w|$, $o=n$). For a cyclic word
$\tau$ we write $S^{j}(\tau):=S(\tau^{(j)})$ for the value on the $j$-fold left rotation;
$D$ is rotation-invariant.

**Lemma 1.2 (concatenation cocycle).** For words $u,v$,
$$
S(uv) \;=\; Y^{\operatorname{len}(v)}\,S(u) \;+\; X^{|u|}\,S(v). \tag{1.1}
$$

*Proof.* In $uv$ the letters of $u$ keep their gap-sums $e_k$ but are shifted right by
$\operatorname{len}(v)$ positions (extra $Y^{\operatorname{len}(v)}$), and the letters of $v$
keep their positions but inherit the accumulated gap sum $|u|$ (extra $X^{|u|}$). Summing the
two blocks gives (1.1). $\blacksquare$

**Lemma 1.3 (antisymmetry / rotation).** For words $u,v$,
$$
S(uv) - S(vu) \;=\; D(u)\,S(v) \;-\; D(v)\,S(u). \tag{1.2}
$$

*Proof.* Apply (1.1) twice and subtract:
$S(uv)-S(vu) = S(u)\,[\,Y^{\operatorname{len}(v)}-X^{|v|}\,] + S(v)\,[\,X^{|u|}-Y^{\operatorname{len}(u)}\,]
= -D(v)S(u) + D(u)S(v)$, using $X^{|u|}-Y^{\operatorname{len}(u)}=D(u)$. $\blacksquare$

Taking $u=w$, $v=w'$ a single rotation by the first block, (1.2) is the polynomial form of the
rotation recursion (Lemma 3.1 of [`theorems.md`](theorems.md)).

---

## 2. Block telescoping for $w^q w'$

Fix blocks $w$ (length $n$, sum $|w|$) and $w'$, and let $\tau = w^q w'$. Left-rotating $\tau$
by $\operatorname{len}(w)=n$ moves the leading block to the tail:
$$
\tau^{(n)} \;=\; w^{q-1}\,w'\,w .
$$
Define the **block-shift difference**
$$
\Delta_q \;:=\; S^{0}(\tau) - S^{\,n}(\tau) \;=\; S(w^q w') - S(w^{q-1} w' w).
$$

**Theorem 2.1 (telescoping).** For all $q\ge 1$,
$$
\boxed{\;\Delta_q \;=\; X^{(q-1)\,|w|}\;\bigl(S(ww') - S(w'w)\bigr)\;=\; X^{(q-1)|w|}\,C(w,w'),\;}
$$
where the **core difference** is the $q$-independent element
$$
C(w,w') \;:=\; S(ww') - S(w'w) \;=\; D(w)\,S(w') - D(w')\,S(w) \;\in\; \mathbb{Z}[X,Y]
$$
(the second equality is (1.2) with $u=w,v=w'$). In particular the only $X^aY^b$ prefactor that
appears is the pure power $X^{(q-1)|w|}$ — i.e. $a=(q-1)|w|$, $b=0$.

*Proof.* For $q\ge 2$ split off the leading block with the cocycle (1.1):
$$
S(w^q w') = Y^{L}\,S(w) + X^{|w|} S(w^{q-1}w'),\qquad
S(w^{q-1}w'w) = Y^{L}\,S(w) + X^{|w|} S(w^{q-2}w'w),
$$
where both tails $w^{q-1}w'$ and $w^{q-2}w'w$ have the same length
$L=(q-1)n+\operatorname{len}(w')$, so the two $Y^{L}S(w)$ terms are identical. Subtracting,
$$
\Delta_q = X^{|w|}\,\bigl(S(w^{q-1}w') - S(w^{q-2}w'w)\bigr) = X^{|w|}\,\Delta_{q-1}.
$$
With base case $\Delta_1 = S(ww')-S(w'w)=C(w,w')$, induction gives
$\Delta_q = X^{(q-1)|w|}C(w,w')$. $\blacksquare$

Verified symbolically over generic $(X,Y)$ for many $(w,w',q)$, and the prefactor is always a
bare power of $X$ (the gap-sum variable), never mixed.

---

## 3. The gcd consequence at $(X,Y)=(2,3)$

Now specialize to integers. Recall from [`theorems.md`](theorems.md): $\gcd_j S^{j}(\tau)\mid
D(\tau)$ for every word (Cor. 3.2), with equality $\gcd_j S^{j}(\tau)=|D(\tau)|$ on a genuine
cycle (Thm. 3.3).

**Proposition 3.1 (the gcd lands in a $q$-free integer).** Let $\tau=w^q w'$ with
$(X,Y)=(2,3)$. Then
$$
\gcd_{0\le j\lt \operatorname{len}(\tau)} S^{j}(\tau)\ \Bigm|\ C(w,w'),
$$
the integer $C(w,w')=S(ww')-S(w'w)$, which does not depend on $q$.

*Proof.* Both $S^{0}(\tau)$ and $S^{n}(\tau)$ are cyclic shifts of $\tau$, so the gcd $G$ of all
shifts divides their difference $\Delta_q = 2^{(q-1)|w|}\,C(w,w')$ (Theorem 2.1). But
$D(\tau)=2^{E}-3^{o}$ is odd, and $G\mid D(\tau)$, so $G$ is odd, hence coprime to
$2^{(q-1)|w|}$. Therefore $G\mid C(w,w')$. $\blacksquare$

**Corollary 3.2 (finitely many $q$ per block pair).** If $w^q w'$ is the gap word of a genuine
cycle, then $G=|D(\tau)|=\bigl|\,2^{\,|w'|+q|w|}-3^{\,\operatorname{len}(w')+q\operatorname{len}(w)}\,\bigr|$, so by
Proposition 3.1
$$
\bigl|\,2^{\,|w'|+q|w|}-3^{\,\operatorname{len}(w')+q\operatorname{len}(w)}\,\bigr|\ \Bigm|\ C(w,w').
$$
Hence **either $C(w,w')=0$, or $|D(\tau)|\le |C(w,w')|$.** Since $|D(\tau)|$ grows like
$\max\!\bigl(2^{q|w|},3^{q\operatorname{len}(w)}\bigr)\to\infty$, for each fixed $(w,w')$ with
$C(w,w')\ne 0$ only finitely many $q$ can give a cycle, with an explicit threshold once a bound
on $|C(w,w')|$ is fixed.

**Numerical confirmation.** Over families $w^q w'$, $q=1,\dots,6$ at $(X,Y)=(2,3)$: $\gcd_j
S^{j}$ always divides the fixed $C(w,w')$, while $|D(\tau)|$ blows up. E.g.

| $w$ | $w'$ | $C(w,w')$ | $\lvert D\rvert$ at $q=1$ | … | $q=6$ |
|---|---|---|---|---|---|
| $(1,2)$ | $(3)$ | $-26$ | $37$ | | $502\,829$ |
| $(2,1,1)$ | $(4,1)$ | $-876$ | $269$ | | $2\,949\,913\,489$ |
| $(1,3)$ | $(2)$ | $2$ | $37$ | | $65\,514\,541$ |

In each row $\gcd_j S^{j}=1$ for all $q$ (no cycle), consistent with $1\mid C$ and
$|D|\nmid C$ for $q\ge1$.

---

## 4. The degenerate locus $C(w,w')=0$

$C(w,w')=D(w)S(w')-D(w')S(w)=0$ means (when $D(w),D(w')\ne0$)
$$
\frac{S(w)}{D(w)} \;=\; \frac{S(w')}{D(w')},
$$
i.e. $w$ and $w'$ define the **same rational fixed point** $S(\cdot)/D(\cdot)$ (the value that
the block, read as a stand-alone cycle equation $D\,a=S$, would force). This locus contains:

- $w'=w$ (then $\tau=w^{q+1}$ is a pure power — the **single-circuit / imprimitive** case);
- more generally any $w'$ that is itself periodic with $w$'s fixed point.

These are precisely the bounded-circuit configurations where finiteness of cycles is already a
theorem (Steiner 1977, one circuit; Simons–de Weger, multi-circuit up to 68). So the $C=0$
stratum is the "known/hard" core, and the $C\ne0$ complement is exactly where the cheap
$q$-independent bound of §3 bites.

---

## 5. Where Matveev enters

Corollary 3.2 already gives, for fixed $(w,w')$ with $C\ne0$, an *elementary* bound on $q$.
To upgrade to a **uniform, quantitative** finiteness of triples $(q,w,w')$:

1. **Trivial upper bound on $|C(w,w')|$** from the word data. Since
   $|C|\le \max\bigl(S(ww'),S(w'w)\bigr)$ and, for any word $u$ of length $\ell$ and sum
   $\sigma$, $S(u)=\sum_k 2^{e_k}3^{\ell-1-k}\le 2^{\sigma-1}\frac{3^{\ell}-1}{2}\lt 2^{\sigma-2}3^{\ell}$,
   and both $ww'$ and $w'w$ have length $\operatorname{len}(w)+\operatorname{len}(w')$ and sum
   $|w|+|w'|$,
   $$
   |C(w,w')| \;\lt\; 2^{\,|w|+|w'|}\,3^{\,\operatorname{len}(w)+\operatorname{len}(w')}
   \;=\; 2^{\,E-(q-1)|w|}\,3^{\,\operatorname{len}(w)+\operatorname{len}(w')},
   \qquad E=q|w|+|w'| .
   $$
   The exponent of $2$ is $|w|+|w'|=|ww'|$ — crucially **independent of $q$**. (The earlier
   guess $2^{|w'|}3^{\operatorname{len}(w)+\operatorname{len}(w')}$ — i.e. exponent
   $E-q|w|=|w'|$ — is *too small* and fails, e.g. $w=(3,3),w'=(1)$ gives $|C|=66\gt 54$: the
   $2^{|w|}$ from the terms of $S(ww')$ that have crossed the $w$-block cannot be dropped.)
2. **Matveev lower bound** on the linear form in logarithms
   $\Lambda = |\,E\log 2 - o\log 3\,|$, equivalently on $|2^E-3^o|=|D(\tau)|$, gives
   $|D(\tau)|\ge 2^{E}\exp(-c\log E)$ for an effective $c$. With $E=|w'|+q|w|$ and
   $o=\operatorname{len}(w')+q\operatorname{len}(w)$, this is exponential in $q$.
3. **Combine.** A cycle needs $|D(\tau)|\le |C(w,w')|$ (Cor. 3.2). The lower bound (2) and the
   $q$-free upper bound (1) are compatible only for $q,|w|,|w'|$ below an effective threshold —
   quantitative finiteness of the eventually-periodic families that close into actual cycles.

---

## Open items

- **Sharpen the trivial $C$-bound.** The honest bound is
  $|C(w,w')|\lt 2^{|w|+|w'|}3^{\operatorname{len}(w)+\operatorname{len}(w')}$ (proved above,
  verified with no failures; the smaller $2^{|w'|}3^{\cdots}$ is false). Worth checking whether
  cancellation in $C=D(w)S(w')-D(w')S(w)$ buys a genuinely smaller bound on average.
- **Make step 5.3 effective.** Plug an explicit Matveev constant in and read off the threshold
  on $(q,|w|,\operatorname{len}(w),|w'|,\operatorname{len}(w'))$; compare with the size of the
  $C=0$ stratum that must be handled by the bounded-circuit theorems.
- **Characterize $C(w,w')=0$ over $\mathbb{Z}[X,Y]$** (polynomial identity) vs. at $(2,3)$
  (integer identity): does the integer locus add solutions beyond shared-fixed-point blocks?
- **General eventually-periodic words.** Every cyclic word is some $w^q w'$ (trivially $q=1$);
  the leverage is choosing the *longest* repeated block. Quantify how the bound improves with
  the maximal $q$, and whether iterating over all block decompositions tightens the gcd ceiling
  of the parent [`cycle-gcd`](STATUS.md) program.
