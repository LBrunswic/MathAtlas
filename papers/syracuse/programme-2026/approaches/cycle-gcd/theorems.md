# Cycle sums, rotation, and the critical exponent

A formal development of the `cycle-gcd` results. Self-contained; the foundational identity of
the [`diophantine`](../diophantine/RATIONALE.md) approach is restated and proved here for
completeness. Conventions follow [`CHEATSHEET.md`](../../CHEATSHEET.md).

---

## 1. Setup

**Definition 1.1 (accelerated map).** For an odd integer $a$ let $\nu_2$ denote the $2$-adic
valuation and
$$
T(a) \;=\; \frac{3a+1}{2^{\nu_2(3a+1)}},
$$
which is again an odd integer. A *trajectory* is a sequence $a_0, a_1, \dots, a_o$ of odd
integers with $a_{k+1} = T(a_k)$ for $0 \le k \lt o$.

**Definition 1.2 (gaps, partial sums).** For a trajectory put
$$
d_k \;=\; \nu_2(3a_k+1) \;\ge\; 1, \qquad e_0 = 0, \quad e_k = \sum_{i=0}^{k-1} d_i, \qquad
E \;:=\; e_o = \sum_{i=0}^{o-1} d_i .
$$
Thus $2^{d_k} a_{k+1} = 3a_k + 1$ and $(e_k)$ is strictly increasing.

**Definition 1.3 (cycle).** A trajectory is a *cycle* of length $o$ if $a_o = a_0$ (so it
extends periodically with $a_{k+o} = a_k$). It is *positive* if every $a_k \ge 1$, and
*primitive* if $o$ is its minimal period, equivalently if $a_0, \dots, a_{o-1}$ are pairwise
distinct.

**Definition 1.4 (sum functional and the quantity $D$).** For a finite sequence
$w = (d_0, \dots, d_{o-1})$ of positive integers with partial sums $e_k$ ($e_0 = 0$,
$e_k = \sum_{i \lt k} d_i$) and total $E = \sum_i d_i$, set
$$
S(w) \;=\; \sum_{k=0}^{o-1} 2^{e_k}\, 3^{\,o-1-k}, \qquad D(w) \;=\; 2^{E} - 3^{o}.
$$
We call $w$ a *(gap) word*. A trajectory of length $o$ determines the word
$w = (d_0, \dots, d_{o-1})$; we write $S^{(0)} := S(w)$ and $D := D(w) = 2^{E}-3^{o}$.

**Remark 1.5.** $D \ne 0$ for all $o \ge 1$: $3^{o}$ is odd and $\gt 1$, while $2^{E}$ is a power
of $2$, so $2^{E} = 3^{o}$ is impossible. Equivalently $o\log_2 3 \notin \mathbb{Z}$.

---

## 2. The closed-form identity

**Proposition 2.1 (closed form).** For any trajectory $a_0, \dots, a_o$ and the associated
$e_k$,
$$
2^{e_o}\, a_o \;-\; 3^{o}\, a_0 \;=\; \sum_{k=0}^{o-1} 2^{e_k}\, 3^{\,o-1-k}. \tag{2.1}
$$

*Proof.* Induction on $o \ge 1$.

*Base $o=1$.* By Definition 1.1, $2^{e_1} a_1 = 2^{d_0} a_1 = 3a_0 + 1$, so
$2^{e_1}a_1 - 3 a_0 = 1 = 2^{e_0} 3^{0}$, which is the right-hand side of (2.1) for $o=1$.

*Step $o \to o+1$.* Assume (2.1). Multiplying by $3$,
$$
3\cdot 2^{e_o} a_o - 3^{o+1} a_0 = \sum_{k=0}^{o-1} 2^{e_k} 3^{\,o-k}. \tag{2.2}
$$
From $2^{d_o} a_{o+1} = 3a_o + 1$ and $e_{o+1} = e_o + d_o$,
$$
2^{e_{o+1}} a_{o+1} = 2^{e_o}(3a_o + 1) = 3\cdot 2^{e_o} a_o + 2^{e_o},
\quad\text{i.e.}\quad 3\cdot 2^{e_o} a_o = 2^{e_{o+1}} a_{o+1} - 2^{e_o}. \tag{2.3}
$$
Substituting (2.3) into (2.2),
$$
2^{e_{o+1}} a_{o+1} - 3^{o+1} a_0
= 2^{e_o} + \sum_{k=0}^{o-1} 2^{e_k} 3^{\,o-k}
= \sum_{k=0}^{o} 2^{e_k}\, 3^{\,o-k},
$$
since $2^{e_o} = 2^{e_o} 3^{0}$ is exactly the $k=o$ term. This is (2.1) with $o$ replaced by
$o+1$. $\blacksquare$

**Corollary 2.2 (cycle equation).** For a cycle of length $o$ (so $a_o = a_0$),
$$
\bigl(2^{E} - 3^{o}\bigr)\, a_0 \;=\; S^{(0)}, \qquad\text{i.e.}\qquad D\, a_0 = S^{(0)}. \tag{2.4}
$$
In particular $D \mid S^{(0)}$ and $a_0 = S^{(0)}/D$.

*Proof.* Set $a_o = a_0$ in (2.1); the left side becomes $(2^{e_o}-3^o)a_0 = D a_0$ and the
right side is $S^{(0)}$ by Definition 1.4. As $a_0 \in \mathbb{Z}$ and $D \ne 0$ (Remark 1.5),
$D \mid S^{(0)}$. $\blacksquare$

---

## 3. Rotation and the gcd of cyclic shifts

For a word $w = (d_0, \dots, d_{o-1})$, write $w' = (d_1, \dots, d_{o-1}, d_0)$ for its left
rotation, and $w^{(j)}$ for the $j$-fold left rotation. Put $S^{(j)} = S(w^{(j)})$. Since the
total $E$ and length $o$ are rotation-invariant, $D(w^{(j)}) = D$ for all $j$.

**Lemma 3.1 (rotation recursion).** For every word $w$,
$$
2^{d_0}\, S(w') \;=\; 3\, S(w) \;+\; D. \tag{3.1}
$$
The identity is purely algebraic: it holds for every finite sequence of positive integers,
with no reference to oddness, positivity, or the map $T$.

*Proof.* Let $e_k$ be the partial sums of $w$. The partial sums $e'_k$ of $w' $ satisfy
$e'_0 = 0$ and, for $1 \le k \le o-1$,
$$
e'_k = \sum_{i=0}^{k-1} d_{i+1} = \sum_{j=1}^{k} d_j = e_{k+1} - d_0.
$$
Hence
$$
S(w') = \sum_{k=0}^{o-1} 2^{e'_k} 3^{\,o-1-k}
= 3^{\,o-1} + 2^{-d_0}\sum_{k=1}^{o-1} 2^{e_{k+1}} 3^{\,o-1-k}
= 3^{\,o-1} + 2^{-d_0}\sum_{j=2}^{o} 2^{e_j} 3^{\,o-j}, \tag{3.2}
$$
where the last step substitutes $j = k+1$. Now evaluate $\sum_{j=1}^{o} 2^{e_j} 3^{o-j}$ in two
pieces. First, separating the $j=o$ term $2^{E}3^{0} = 2^{E}$:
$$
\sum_{j=1}^{o} 2^{e_j} 3^{\,o-j} = \Bigl(\sum_{j=1}^{o-1} 2^{e_j} 3^{\,o-j}\Bigr) + 2^{E}. \tag{3.3}
$$
Second, from $3\,S(w) = \sum_{k=0}^{o-1} 2^{e_k} 3^{\,o-k} = 3^{o} + \sum_{j=1}^{o-1} 2^{e_j}3^{\,o-j}$
(the $k=0$ term being $2^{0}3^{o} = 3^{o}$),
$$
\sum_{j=1}^{o-1} 2^{e_j} 3^{\,o-j} = 3\,S(w) - 3^{o}. \tag{3.4}
$$
Combining (3.3)–(3.4): $\sum_{j=1}^{o} 2^{e_j} 3^{o-j} = 3 S(w) - 3^{o} + 2^{E}$, and therefore
$$
\sum_{j=2}^{o} 2^{e_j} 3^{\,o-j}
= 3\,S(w) - 3^{o} + 2^{E} - 2^{e_1} 3^{\,o-1}
= 3\,S(w) - 3^{o} + 2^{E} - 2^{d_0} 3^{\,o-1}.
$$
Insert this into (3.2):
$$
S(w') = 3^{\,o-1} + 2^{-d_0}\bigl[\,3 S(w) - 3^{o} + 2^{E}\,\bigr] - 3^{\,o-1}
= 2^{-d_0}\bigl[\,3 S(w) + (2^{E}-3^{o})\,\bigr].
$$
Multiplying by $2^{d_0}$ gives (3.1). $\blacksquare$

**Corollary 3.2 ($\gcd$ divides $D$).** For every word $w$,
$$
\gcd_{0 \le j \lt o} S^{(j)} \;\bigm|\; D.
$$

*Proof.* Apply (3.1) to $w$: any common divisor $g$ of $S^{(0)}$ and $S^{(1)}$ divides
$2^{d_0} S^{(1)} - 3 S^{(0)} = D$. In particular $G := \gcd_j S^{(j)}$ divides both $S^{(0)}$
and $S^{(1)}$, hence $G \mid D$. $\blacksquare$

**Theorem 3.3 (exact gcd on cycles).** If $w$ is the gap word of a cycle, then
$$
\gcd_{0 \le j \lt o} S^{(j)} \;=\; |D| \;=\; \bigl|\,2^{E}-3^{o}\,\bigr|.
$$

*Proof.* The $j$-fold rotation $w^{(j)}$ is the gap word of the same cycle started at $a_j$;
by Corollary 2.2 applied to that starting point, $D\, a_j = S^{(j)}$ with $a_j \in \mathbb{Z}$.
Thus $D \mid S^{(j)}$ for every $j$, so $D$ is a common divisor and $D \mid G$, where
$G := \gcd_j S^{(j)} \gt 0$. By Corollary 3.2, $G \mid D$. Hence $G = |D|$. $\blacksquare$

---

## 4. The critical exponent

**Definition 4.1 (critical / non-critical).** Fix $o \ge 1$. By Remark 1.5 the function
$E \mapsto 2^{E} - 3^{o}$ is strictly increasing in $E$ and never zero, so
$$
E_*(o) \;:=\; \min\{\, E \in \mathbb{Z} : 2^{E} \gt 3^{o} \,\} \;=\; \lceil o\log_2 3\rceil
$$
is well defined and $2^{E_*(o)} - 3^{o}$ is the least positive value of $2^{E}-3^{o}$. A pair
$(E, o)$ with $2^{E} \gt 3^{o}$ is **critical** if $E = E_*(o)$, and **non-critical** if
$E \gt E_*(o)$.

**Lemma 4.2 (dichotomy and gap bound).** Let $(E, o)$ satisfy $2^{E} \gt 3^{o}$. Then:

1. $(E,o)$ is critical $\iff o\log_2 3 \lt E \lt o\log_2 3 + 1$;
2. $(E,o)$ is non-critical $\iff E \gt o\log_2 3 + 1 \iff 2^{E-1} \gt 3^{o}$;
3. if $(E,o)$ is non-critical then $\,2^{E} - 3^{o} \gt 2^{E-1}$.

*Proof.* Since $x := o\log_2 3 \notin \mathbb{Z}$ (Remark 1.5), the unique integer in $[x, x+1)$
lies in $(x, x+1)$ and equals $\lceil x\rceil = E_*(o)$.

(1) $2^{E} \gt 3^{o} \iff E \gt x$. Critical means $E = E_*(o)$, the least integer exceeding $x$,
i.e. the unique integer in $(x, x+1)$; so critical $\iff x \lt E \lt x+1$.

(2) Non-critical means $E \gt x$ and $E \ne E_*(o)$, i.e. $E \ge E_*(o)+1$. As $x+1 \notin
\mathbb{Z}$, the least integer exceeding $x+1$ is $\lceil x+1\rceil = \lceil x\rceil + 1 =
E_*(o)+1$; hence $E \ge E_*(o)+1 \iff E \gt x+1$. Finally $E \gt x+1 \iff E-1 \gt x \iff 2^{E-1} \gt 3^{o}$.

(3) By (2), $2^{E-1} \gt 3^{o}$, so
$2^{E} - 3^{o} = 2\cdot 2^{E-1} - 3^{o} \gt 2\cdot 2^{E-1} - 2^{E-1} = 2^{E-1}$. $\blacksquare$

**Theorem 4.3 (reduction of criticality).** Let $a_0, \dots, a_{o-1}$ be a positive cycle with
parameters $(E, o)$. Then:

1. $2^{E} \gt 3^{o}$, so $D = 2^{E} - 3^{o} \gt 0$;
2. the cycle is critical $\iff 2^{E} \lt 2\cdot 3^{o}\,$, equivalently
   $\displaystyle \prod_{k=0}^{o-1}\Bigl(1 + \tfrac{1}{3a_k}\Bigr) \lt 2.$

*Proof.* (1) Multiplying the relations $2^{d_k} a_{k+1} = 3 a_k + 1$ over $k = 0, \dots, o-1$
and using $\prod_k a_{k+1} = \prod_k a_k \gt 0$ (cycle, positive),
$$
2^{E} \prod_{k} a_k = \prod_{k}(3a_k + 1), \qquad\text{hence}\qquad
2^{E} = \prod_{k=0}^{o-1}\frac{3a_k+1}{a_k} = \prod_{k=0}^{o-1}\Bigl(3 + \tfrac{1}{a_k}\Bigr). \tag{4.1}
$$
Each factor exceeds $3$, so $2^{E} \gt 3^{o}$ and $D \gt 0$. (Equivalently: $D = S^{(0)}/a_0 \gt 0$
by (2.4), as $S^{(0)} \gt 0$ and $a_0 \ge 1$.)

(2) By (1), $(E,o)$ lies in the regime of Lemma 4.2. "Critical" is the negation of
"non-critical", so by Lemma 4.2(2),
$$
\text{critical} \iff \neg\,(2^{E-1} \gt 3^{o}) \iff 2^{E-1} \le 3^{o} \iff 2^{E-1} \lt 3^{o},
$$
the last step by Remark 1.5 ($2^{E-1} \ne 3^{o}$). Thus critical $\iff 2^{E} \lt 2\cdot 3^{o}$.
Dividing (4.1) by $3^{o}$ gives $2^{E}/3^{o} = \prod_k(1 + \tfrac{1}{3a_k})$, so the condition
is $\prod_k(1 + \tfrac{1}{3a_k}) \lt 2$. $\blacksquare$

**Proposition 4.4 (the gap bound alone does not force criticality).** Theorem 4.3 reduces
"every primitive positive cycle is critical" to the inequality $2^{E} \lt 2\cdot 3^{o}$, but this
inequality cannot be obtained from the gap bound Lemma 4.2(3) by a size comparison on the
sums $S^{(j)}$. Concretely, there is a primitive, non-critical word for which
$\min_j S^{(j)} \gt D$:
take $o = 5$ and $w = (1,2,2,2,2)$, so $E = 9$ and $D = 2^{9} - 3^{5} = 269$.

| rotation $w^{(j)}$ | partial sums $(e_k)$ | $S^{(j)}$ |
|---|---|---|
| $(1,2,2,2,2)$ | $0,1,3,5,7$ | $431$ |
| $(2,2,2,2,1)$ | $0,2,4,6,8$ | $781$ |
| $(2,2,2,1,2)$ | $0,2,4,6,7$ | $653$ |
| $(2,2,1,2,2)$ | $0,2,4,5,7$ | $557$ |
| $(2,1,2,2,2)$ | $0,2,3,5,7$ | $485$ |

*Proof / verification.* $E = 1+2+2+2+2 = 9$ and $D = 512 - 243 = 269$. Since
$o\log_2 3 = 7.924\ldots$, $E_*(5) = 8$ and $E = 9 \gt 8$, so $(9,5)$ is non-critical; indeed
$2^{E-1} = 256 \gt 243 = 3^{5}$, consistent with Lemma 4.2(2), and Lemma 4.2(3) gives
$D = 269 \gt 256 = 2^{E-1}$. The word is primitive (it has a unique entry $1$, so its rotations
are distinct). The sums in the table are computed from $S(w^{(j)}) = \sum_k 2^{e_k} 3^{4-k}$;
e.g. for $w^{(0)}$, $\,81 + 54 + 72 + 96 + 128 = 431$. Thus $\min_j S^{(j)} = 431 \gt 269 = D$.

Consequently the tempting chain
$$
\text{non-critical} \overset{\text{4.2(3)}}{\Longrightarrow} D \gt 2^{E-1}
\;\Longrightarrow\; \min_j S^{(j)} \le 2^{E-1} \lt D
\;\Longrightarrow\; \text{some } a_j = S^{(j)}/D \lt 1
$$
fails: its middle implication is false here. The word is nonetheless not a cycle, because by
Theorem 3.3 a cycle requires $\gcd_j S^{(j)} = D = 269$, whereas here
$\gcd(431, 781, 653, 557, 485) = 1$ (e.g. $431$ is prime and $431 \nmid 781$). Hence this
non-critical word is excluded *arithmetically*, via the gcd of its shifts, not by any size
inequality. $\blacksquare$

**Remark 4.5 (status and open problem).** Theorems 3.3 and 4.3 together isolate the open core:
*every primitive positive cycle is critical* would follow from showing that every non-critical
primitive word $w$ has $\gcd_j S^{(j)} \lt D$ — equivalently $\gcd_j S^{(j)} \ne D$, since
$\gcd_j S^{(j)} \mid D$ always (Corollary 3.2). By Theorem 3.3 this is exactly the failure of
the cycle condition. The size route being closed (Proposition 4.4), any proof must come from
the divisibility/gcd structure of the shifts or from a transcendence (linear-forms-in-logs)
lower bound on $|2^{E}-3^{o}|$. See [`STATUS.md`](STATUS.md).
