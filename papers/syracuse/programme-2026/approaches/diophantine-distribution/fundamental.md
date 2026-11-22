# The fundamental solution $S(w)/D(w)$ — claims and bounds

This note isolates and proves the structural backbone of the
[`diophantine-distribution`](RATIONALE.md) approach: that $x_w^\ast := S(w)/D(w)$ is a
*fundamental solution* attached to every gap word $w$ — first in the cyclic sense, then
among **all** trajectories — and the size bounds on it coming from the imbalance
factorization. Every claim below is proved here and checked numerically by
[`verify_fundamental.py`](verify_fundamental.py) (2006 random+seed words for the algebraic
identities, 1829 for the coset spacing, ~19000 for the size bound).

> All `<`/`>` in displayed math use the `\lt`/`\gt` macros (PyCharm-preview safe).

## Notation

A **gap word** is $w = (d_0,\dots,d_{o-1})$ with each $d_k \ge 1$. Write
$$e_k = d_0 + \dots + d_{k-1}\ (e_0=0),\qquad E = e_o = |w| = \sum_k d_k,\qquad o = \operatorname{len}(w).$$
The **word characters** (from [`cycle-gcd`](../cycle-gcd/STATUS.md)) are
$$D(w) = 2^{E} - 3^{o},\qquad S(w) = \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k}.$$
The **accelerated (odd-to-odd) Syracuse step** with gap $d$ is $T_d(x) = (3x+1)/2^{d}$, and
the **word-map** is the composite $F_w = T_{d_{o-1}}\circ\cdots\circ T_{d_0}$.

Throughout, $D(w)$ is **odd** (since $2^E$ is even and $3^o$ is odd), hence a unit in
$\mathbb{Z}_2$; so $S(w)/D(w) \in \mathbb{Z}_2$ always.

---

## FS1 — The word-map is affine; its fixed point is $S/D$

> **Claim FS1.** $\displaystyle F_w(x) = \frac{3^{o}}{2^{E}}\,x + \frac{S(w)}{2^{E}}$ for all
> $x$, and its unique fixed point is
> $$x_w^\ast \;=\; \frac{S(w)}{2^{E}-3^{o}} \;=\; \frac{S(w)}{D(w)}.$$

**Proof.** Each $T_d(x) = \tfrac{3}{2^d}x + \tfrac{1}{2^d}$ is affine, so $F_w(x)=\alpha x+\gamma$
with $\alpha = \prod_k \tfrac{3}{2^{d_k}} = 3^o/2^E$. For $\gamma$, run the Diophantine closed
form ([`diophantine`](../diophantine/RATIONALE.md)) with start $x$: after $o$ accelerated
steps, $2^{E}F_w(x) - 3^{o}x = S(w)$ (this is the closed form; it is a polynomial identity in
$x$, needing only the recurrence $2^{d_k}a_{k+1}=3a_k+1$, not oddness or positivity). Hence
$\gamma = S(w)/2^E$. The fixed point solves $x = \alpha x + \gamma$, i.e.
$x(1-3^o/2^E)=S/2^E$, giving $x_w^\ast = S/(2^E-3^o)=S/D$. Uniqueness: $\alpha = 3^o/2^E \ne 1$.
$\qquad\blacksquare$

Because $D$ is odd, $x_w^\ast$ exists in $\mathbb{Z}_2$ for **every** word — no divisibility
needed. (Verified: `check_affine`.)

---

## FS2 — Cyclic interpretation

> **Claim FS2.** $x_w^\ast = S(w)/D(w)$ is the unique value (in $\mathbb{Q}$, equivalently in
> $\mathbb{Z}_2$) whose Syracuse orbit has parity word exactly $w$ **and returns**:
> $F_w(x_w^\ast)=x_w^\ast$. It is the start of a genuine integer cycle iff
> $$D(w)\mid S(w)\quad\text{and the parities are consistent}$$
> (each $a_k$ odd with $d_k=\nu_2(3a_k+1)$). This recovers the cycle equation
> $D\,a_0=S$ of [`cycle-gcd`](../cycle-gcd/STATUS.md).

**Proof.** A cycle with word $w$ has $a_o=a_0$; FS1's closed form gives
$(2^E-3^o)a_0 = S$, i.e. $a_0 = S/D = x_w^\ast$, and conversely $x_w^\ast$ is the fixed point
of $F_w$. Integrality of $x_w^\ast$ is $D\mid S$; the parity conditions are what make the
fixed point a genuine Syracuse orbit (not merely an algebraic fixed point of $F_w$ over
$\mathbb{Q}$). $\qquad\blacksquare$

Examples (from `verify_fundamental.py`): $w=(1)$ gives $S=1,D=-1$, $x_w^\ast=-1$ (the $-1$
fixed point); $w=(2,1)$ gives $S=7,D=-1$, $x_w^\ast=-7$ (the $-7\to-5\to-7$ cycle).

---

## FS3 — Fundamental solution among **all** trajectories

The point of "fundamental solution" is that $x_w^\ast$ organizes *every* trajectory carrying
the word $w$, not just the periodic one.

> **Claim FS3.** Fix a word $w$ with $|w|=E$. The set of $x\in\mathbb{Z}_2$ whose accelerated
> Syracuse orbit performs **exactly** the word $w$ over its first $o$ odd steps and then has
> $a_o$ **odd** is a single residue class modulo $2^{\,E+1}$:
> $$\{\,x\in\mathbb{Z}_2 : \text{word}(x)=w,\ a_o\ \text{odd}\,\}\;=\; x_w^\ast + 2^{\,E+1}\,\mathbb{Z}_2
>  \;=\; x_w^\ast + 2\cdot 2^{|w|}\,\mathbb{Z}_2.$$
> Equivalently $x = x_w^\ast + 2k\cdot 2^{|w|}$, $k\in\mathbb{Z}_2$: a particular
> (fundamental) solution $x_w^\ast$ plus the homogeneous family.

**Proof.** Two ingredients.

*(Terras bijection.)* In the compressed Collatz map ($x\mapsto x/2$ if even,
$x\mapsto(3x+1)/2$ if odd), the parity vector of the first $n$ steps depends only on, and
is determined by, $x \bmod 2^{n}$; the map $\mathbb{Z}/2^{n}\to\{0,1\}^n$ is a bijection.

*(Word $\leftrightarrow$ compressed string.)* One accelerated step of gap $d_k$ is one
odd-type compressed step followed by $d_k-1$ even-type ones, i.e. the compressed substring
$1\,0^{\,d_k-1}$. So "orbit performs word $w$ then $a_o$ is odd" is *exactly* the event that
the first $E+1$ compressed parities equal the fixed string
$$1\,0^{d_0-1}\,1\,0^{d_1-1}\cdots 1\,0^{d_{o-1}-1}\,1\qquad(\text{length }E+1,\ o+1\text{ ones}).$$
By Terras with $n=E+1$ this is a single class mod $2^{E+1}$. The extra trailing $1$ — "$a_o$
odd" — is the one bit beyond the $E$ that the word itself occupies, and it is what forces the
modulus up from $2^{E}$ to $2^{E+1}=2\cdot 2^{|w|}$. Finally $x_w^\ast$ lies in this class:
its orbit is $w$ repeated, so $a_o = a_0=x_w^\ast$ is odd and the word is $w$. $\qquad\blacksquare$

**The factor of $2$.** Dropping "$a_o$ odd" (only fixing the first $E$ compressed parities)
gives the *coarser* class mod $2^{E}$; requiring the word to genuinely *close* on an odd term
— the natural condition for iterating $w$ — is the extra bit, giving spacing $2^{E+1}$. This
is the $2k\cdot 2^{|w|}$ of the pitch. (Verified by brute force over $2^{E+1}$ for all small
words: `check_coset`.)

> **Corollary (injectivity of the fundamental solution).** Distinct words give distinct
> classes, and within a class $x_w^\ast$ is the canonical representative $=S/D$. Combined with
> the conjugacy $Z\circ\operatorname{shift}=T\circ Z$ (RATIONALE, still to be written up),
> $S(u)/D(u)=S(v)/D(v)$ forces $u,v$ to be powers of a common word. *(Stated; the conjugacy
> half is an open item in STATUS.)*

---

## FS4 — Imbalance factorization and the bound $\eta\in[2^{-p},2^{p}]$

Set $\beta = 2^{\,E/o} = 2^{|w|/\operatorname{len}(w)}$ (so $\beta^o = 2^E$).

> **Lemma (balanced word).** $\displaystyle \sum_{k=0}^{o-1}\beta^{k}3^{\,o-1-k} = \frac{2^E-3^o}{\beta-3} = \frac{D(w)}{\beta-3}.$

**Proof.** Geometric sum: $\sum_{k=0}^{o-1}\beta^k 3^{o-1-k} = \dfrac{\beta^o-3^o}{\beta-3}$,
and $\beta^o=2^E$. $\qquad\blacksquare$

This is $S$ evaluated on the *balanced* word whose every gap is the average $E/o$; it makes
$x_{\bar w}^\ast = 1/(\beta-3)$ exactly.

> **Claim FS4.** $\displaystyle \frac{S(w)}{D(w)} = \frac{\eta}{\beta-3}$ with
> $$\eta \;=\; \frac{S(w)}{D(w)/(\beta-3)} \;\in\; [\,2^{-p},\,2^{p}\,],\qquad
>   p \;=\; \max_{0\le k\le o}\bigl|\,e_k - \tfrac{E}{o}\,k\,\bigr|.$$
> Here $\delta_k := e_k-\tfrac{E}{o}k$ is the deviation of the partial gap-sum from the mean
> line; it is pinned at both ends ($\delta_0=\delta_o=0$), and $p$ is its maximal excursion.

**Proof.** Write $2^{e_k} = \beta^{k}\,2^{\delta_k}$ (since $\beta^k = 2^{(E/o)k}$). Then
$$S(w) = \sum_{k=0}^{o-1} 2^{\delta_k}\,\bigl(\beta^{k}3^{\,o-1-k}\bigr).$$
Each weight $\beta^k 3^{o-1-k} \gt 0$ and $2^{-p}\le 2^{\delta_k}\le 2^{p}$, so summing,
$$2^{-p}\sum_k \beta^k 3^{o-1-k}\ \le\ S(w)\ \le\ 2^{p}\sum_k \beta^k 3^{o-1-k}.$$
Divide by the balanced sum $D/(\beta-3)$ (Lemma): $\eta = S/(D/(\beta-3))\in[2^{-p},2^p]$, and
then $S/D = \eta/(\beta-3)$. $\qquad\blacksquare$

(Verified: `check_imbalance`, 2006 words.)

---

## FS5 — Size of the fundamental solution; regime dictionary

From FS4, $\;|x_w^\ast| = \dfrac{\eta}{|\beta-3|}\;$ with $\eta\in[2^{-p},2^{p}]$, so the size
of $x_w^\ast$ is governed entirely by $|\beta-3| = |2^{E/o}-3|$.

> **Sign / regime.**
> - $\beta\gt3 \iff 2^E\gt3^o \iff D\gt0$ (**contracting**, $1/(\beta-3)\gt0$);
> - $\beta\lt3 \iff D\lt0$ (**expanding**, $1/(\beta-3)\lt0$, so $x_w^\ast\lt0$ since $\eta\gt0$);
> - **large** word $E/o \gt \log_2\tfrac72$ ($\beta\gt\tfrac72$) $\Rightarrow 1/(\beta-3)\lt2$.

> **Claim FS5a (contracting + large $\Rightarrow$ power of $2$ in the imbalance).** If
> $\beta\ge\tfrac72$ then $0\lt x_w^\ast \le 2^{\,p+1}$, **independent of $E$**.

**Proof.** $\beta\ge\tfrac72\Rightarrow \beta-3\ge\tfrac12$, so
$x_w^\ast=\eta/(\beta-3)\le 2^{p}/\tfrac12 = 2^{p+1}$; positive since both factors positive.
$\qquad\blacksquare$ (Verified on ~19000 words with $\beta\ge\tfrac72$.)

This is the clean half of the pitch's heuristic: words that are "large" and contracting have a
fundamental solution bounded by a power of $2$ in the imbalance alone.

> **Claim FS5b (expanding / critical $\Rightarrow$ large).** For expanding words
> ($\beta\lt3$), $|x_w^\ast| = \eta/(3-\beta)$ grows as $\beta\to3^{-}$. With the Matveev lower
> bound $|D| = |2^E-3^o| \ge 3^o e^{-c_0(1+\log E)}$ (from
> [`cycle-gcd`](../cycle-gcd/eventually-periodic.tex), $c_0\approx5.9\times10^8$) and
> $S(w)\ge 2^{\,e_{o-1}} = 2^{\,E-d_{o-1}}$ (the $k=o-1$ term), one gets a lower bound
> $|x_w^\ast| = S/|D| \ge 2^{\,E-d_{o-1}}/|D|$ that is exponentially large in $E$ whenever
> $|D|$ is near-critical.

**Proof of the two ingredients.** $S(w)=\sum_k 2^{e_k}3^{o-1-k}\ge 2^{e_{o-1}}3^0 = 2^{E-d_{o-1}}$
(drop all but the last term, all terms positive); the Matveev bound is cited. $\blacksquare$

The precise "$x_w^\ast\in[\,2^{|w|}/\operatorname{Poly}(w),\,2^{|w|}\,]$" of the pitch — a
*polynomial* (not just sub-exponential) denominator, uniformly over the critical band — is
**not yet proved**; it is the quantitative heart of the program. See Open questions.

---

## Open questions (carried to STATUS)

1. **Integrality amendment bound (linchpin).** $x_w^\ast\in\mathbb{Z}_2$, not $\mathbb{Z}$.
   Bound the amendment $k$ in $x_w^\ast + 2k\cdot 2^{|w|}/D(w)$ that lands on the nearest
   integer, *in terms of the imbalance $p$*.
2. **Polynomial denominator in the critical band.** Upgrade FS5b to
   $|x_w^\ast|\ge 2^{|w|}/\operatorname{Poly}(w)$ uniformly for critical $(E,o)$.
3. **Conjugacy.** Write up $Z\circ\operatorname{shift}=T\circ Z$ to complete the FS3
   corollary (injectivity / common-root rigidity).
