# Leverage: Filaseta–Schinzel 2004 vs the ≥2-growing-gap no-go

**Paper.** M. Filaseta & A. Schinzel, *On testing the divisibility of lacunary polynomials by
cyclotomic polynomials*, Math. Comp. **73** (2004), no. 246, 957–965.
PDF: `sources/filaseta-schinzel-2004.pdf`.

**Promise:** low–medium. FS itself does **not** close or advance the no-go (honest negative
result, with evidence). But the *attempt* extracts two genuinely new, verified clarifications the
drafts lacked, and re-points the no-go at the correct tool.
**Status:** read in full; criterion stated in our notation; verified on the kernel
(`checks/lit_filaseta_schinzel.py`, exit 0). The headline is a scope finding, not a new lever.
**Last iterated:** 2026-06-08 (leverage gen 1).

---

## 1. What the paper actually proves (exact statements)

Throughout $f(x)=\sum_{j=1}^N a_j x^{d_j}\in\mathbb Z[x]$, $N$ = number of **nonzero terms**,
$\deg f=n$. Define the **index weight** $\gamma(m)=2+\sum_{p\mid m}(p-2)$ (Conway–Jones'
$\gamma(r)$, the minimum length of a vanishing sum of roots of unity with reduced exponent $r$).

- **Theorem 2.** If $\Phi_n\mid f$ and distinct primes $p_1,\dots,p_k$ satisfy
  $2+\sum_{j}(p_j-2)\gt N$, then for **at least one** $j$, writing $p_j^{e_j}\Vert n$, one has
  $\Phi_{m}\mid f$ with $m=n/p_j^{e_j}$ — i.e. a whole prime power can be stripped from the index.
  (Proof: write $f=\sum_i f_i$ grouping terms equal mod $\Phi_n$; each $f_i(\zeta_n)$ is a *minimal*
  vanishing sum, so Conway–Jones gives $N=\sum t_i\ge\sum\gamma(n/\gcd(n,d_i))$, forcing some
  $p_j\nmid n/\gcd(n,d_i)$ for all $i$.)
- **Corollary 1 (the criterion).** If $f$ ($N$ terms) is divisible by **any** cyclotomic, then
  there is a positive integer $m$ with
  $$\gamma(m)=2+\sum_{p\mid m}(p-2)\ \le\ N\qquad\text{and}\qquad \Phi_m\mid f.$$
  In particular every prime $p\mid m$ satisfies $p\le N$. And from $\phi(m)\le\deg f$: for
  $p^e\Vert m$, $e\le r(p)=\lfloor\log\deg f/\log p\rfloor+1$.
- **Theorems 1 & 3 / Algorithms A,B.** A test for "does some $\Phi_m\mid f$" running in time
  $\ll\exp\!\big((2+o(1))\sqrt{N/\log N}(\log N+\log\log n)\big)\log(H+1)$, $H=\max|a_j|$ —
  **polynomial in $\log n$ for fixed $N$**. Algorithm A checks a *specific* $\Phi_m$ by reducing
  $f$ mod $x^m-1$ and repeatedly multiplying by $x^{m/p}-1$; Algorithm B enumerates the candidate
  radicals via Corollary 1.

**The reduction FS delivers.** Cyclotomic-divisibility of a sparse $f$ collapses to a finite set of
congruence conditions on exponents: the *radical* of the useful index $m$ is bounded by the **term
count $N$** (primes $\le N$, weight $\gamma(m)\le N$); only the *exponents* of $m$ scale with
$\deg f$ (via $r(p)$). So the "non-redundant part" of the index is controlled by lacunarity, not by
degree.

---

## 2. Dictionary FS → ours (and the blocking mismatch)

| FS object | our object |
|---|---|
| univariate $f(x)\in\mathbb Z[x]$, $N$ nonzero terms | reduced unit-combo $P_a(X,Y)$ = $\sum_i\pm X^{a_i}Y^{b_i}S^{(j_i)}$ with overall $X^pY^q$ stripped |
| $\Phi_n(x)\mid f$ | a factor of $P_a$ that is $6$-smooth at $(2,3)$ |
| index weight $\gamma(m)\le N$ | radical of any cyclotomic factor $\subseteq\{p\le N\}$ |
| value $\Phi_n(2)$ (single-letter core $X^{|e-d|}-1$) | univariate-in-$X$ ceiling $\operatorname{sixfree}(2^{|e-d|}-1)$ |
| (no FS analogue) | **bivariate, non-homogeneous** $P_a(X,Y)$ evaluated at $(X,Y)=(2,3)$ |

**Blocking mismatch — FS is univariate; our $P_a$ is bivariate and *non-homogeneous*.**
$S(W)=\sum_k X^{e_k}Y^{\,o-1-k}$ has a different total degree in each term, so $P_a(X,Y)$ is **not**
homogeneous. The ceiling is $\operatorname{sixfree}(P_a(2,3))$, a *bivariate* evaluation, which
**no single univariate slice computes**:

- The natural FS bridge, the slice $f(x)=P_a(x,1)$, evaluates at $x=2$ to $P_a(2,1)\ne P_a(2,3)$.
- Worse, slice-reducibility $\ne$ bivariate-reducibility: the slice picks up **spurious** cyclotomic
  factors. **Verified ($a=3$):** $P_3(x,1)$ has a $\Phi_2=x+1$ factor that is **not** a bivariate
  factor of $P_3(X,Y)$, and the actual ceiling $23$ has **no** factor $5=\Phi_2^{\,h}(2,3)$.

**Lacunarity question (the crux for "does FS apply?").** Each $S^{(j)}$ already has $\sim o$ monomials.
After cancellation:

- **Bivariate** term count of $P_a$ **grows** ($\Theta(a)$). The single irreducible factor carrying
  the ceiling has $3a+1$ terms and total degree $2a+2$ — **both grow**.
- The **$Y=1$ slice** is sparse ($N=6$, constant) — but, per above, it is the **wrong object**.

So FS's power-regime (bounded term count) contains only the *wrong* (slice) shadow; the *right*
object (the ceiling-carrying bivariate factor) is in the dense / growing-degree regime FS cannot touch.

---

## 3. The relation extracted (in our notation) — and why it is not load-bearing

**FS Corollary 1, translated.** *A reduced unit-combo polynomial whose $Y=1$ slice has $N$ nonzero
terms can have only those cyclotomic factors $\Phi_m$ with $\gamma(m)\le N$; in particular every
$\Phi_m$-factor index has all prime divisors $\le N$.* For our adjacent-difference family $N=6$
constant, so the slice's cyclotomic indices live in a **fixed finite radical set** $\{p\le 6\}$,
independent of $a$. **Verified:** the indices that occur are $\{1,2,3\}$, all with $\gamma\le 3\le 6$.

**Why this does not close the no-go.** The no-go needs to *forbid* the $6$-free part from collapsing.
But the collapse is **into small-index cyclotomics**, and FS's bound *permits* exactly those
($\gamma(1)=\gamma(2)=2$, $\gamma(6)=3$, all $\le N$). FS pushes toward small radical — the
collapse-prone direction — so it cannot be an obstruction. It is a **necessary condition that the
escape route satisfies**.

> **NEW? :** the stated relation ("cyclotomic part has radical $\le N$, $a$-uniformly") is new to the
> drafts, **but not load-bearing**. **TRANSLATABLE? :** yes (univariate→bivariate via the $Y=1$
> slice), with the caveat that the slice is the wrong object for the $(2,3)$ ceiling.

**What the leverage *did* expose (the actual value of this note).**

1. **The ceiling lives on a non-cyclotomic, non-homogeneous bivariate factor.** Every reduced
   adjacent-difference $P_a(X,Y)$ factors as
   $$P_a=(\,\underbrace{Y-X}_{=\ \Phi_1^{\,h},\ \text{value }-1\text{ at }(2,3)}\,)\cdot Q_a(X,Y),\qquad
   Q_a\ \text{irreducible, }\deg Q_a=2a+2,\ \#\mathrm{terms}=3a+1,$$
   and $\operatorname{sixfree}(P_a(2,3))=\operatorname{sixfree}(Q_a(2,3))$ carries the **entire**
   ceiling. So the draft's $Y=1$-Mahler / "cyclotomic-index" screen is a **red herring** for the
   ceiling — it reports slice cyclotomics that do not feed $\operatorname{sixfree}(P_a(2,3))$.
2. **The correct collapse gate is *homogeneous*, and it is $\{1\}$, not $\{1,2,6\}$.** For a genuinely
   $(2,3)$-bivariate evaluation, the $6$-smooth building blocks are the homogeneous cyclotomics
   $\Phi_n^{\,h}(X,Y)=Y^{\phi(n)}\Phi_n(X/Y)$ — the primitive parts of $3^n-2^n=\prod_{d\mid n}\Phi_d^{\,h}(2,3)$
   (these are the kernel's $D=2^E-3^o$ cyclotomically decomposed). By Bang–Zsygmondy for the pair
   $(2,3)$ (no exceptional case: $2+3=5$ is not a power of $2$, and $(2,3)\ne(2,1)$), **every**
   $\Phi_n^{\,h}(2,3)$ with $n\ge2$ has a primitive prime $\gt 3$:
   $\Phi_2^{\,h}=5,\ \Phi_3^{\,h}=19,\ \Phi_4^{\,h}=13,\ \Phi_6^{\,h}=7,\dots$ Only
   $\Phi_1^{\,h}(2,3)=2-3=-1$ is $6$-smooth. The draft's "$\{1,2,6\}$" set is the *univariate-at-2*
   gate ($\Phi_n(2)\in\{1,3\}$), correct **only** for the single-letter core $X^{|e-d|}-1$ (where $Y$
   cancels); it is the **wrong** gate for the multi-gap bivariate ceiling.
3. **Consequently the no-go is an S-unit / primitive-divisor problem, not a cyclotomic-divisibility
   problem.** Since $P_a$ is non-homogeneous it has *no* $\Phi_n^{\,h}$ factor beyond the linear unit
   $Y-X=\Phi_1^{\,h}$; the ceiling is the value at $(2,3)$ of a growing-degree **irreducible**
   $Q_a$. The no-go = "$\operatorname{sixfree}(Q_a(2,3))\to\infty$", i.e. *a growing-degree
   irreducible bivariate polynomial never takes a $6$-smooth value at the fixed point $(2,3)$*. FS,
   being about which $\Phi_m$ divide a *sparse* $f$, has nothing to say here.
4. **Lacunarity does not buy collapse.** Even the **sparsest** 2-term scalar combo $S^{(0)}-S^{(1)}$
   has a *fixed* 5-term bivariate shape $-(X-1)(X^{a+4}+X^{a+3}+X^{a+2}+XY^{a+1}+Y^{a+1})$ of
   **growing** degree, yet its $6$-free value at $(2,3)$ grows ($305,691,1625,3979,10145,26851,73385$
   for $a=2..8$). The minimum bivariate term count over all $k\le2$ unit combos is the **constant**
   $4$ — so a uniformly few-term reduced combo *does* exist, and FS *would* apply to its slice, yet
   the ceiling still grows because the growth is **non-cyclotomic**.

---

## 4. Verification

`checks/lit_filaseta_schinzel.py` imports the kernel (`approaches/cocycle-combine/lib/cocycle.py`)
and asserts five verified facts on the symmetric family $W_a=d^a e_1 d^a e_2 d^a$ for defects
$(d,e_1,e_2)\in\{(1,3,4),(1,2,3)\}$, $a=2\ldots8$. **Result: ALL PASS, exit 0.**

- **T1** $P_a=(Y-X)\cdot Q_a$ with $\deg Q_a=2a+2$, $\#\mathrm{terms}(Q_a)=3a+1$ (both grow) and
  $\operatorname{sixfree}(P_a(2,3))=\operatorname{sixfree}(Q_a(2,3))$ grows
  ($23,23,1537,26857,330097,3542137,35470657$ for $(1,3,4)$).
- **T2** slice term count $N(P_a(x,1))=6$ constant; at $a=3$ the slice's $\Phi_2$ is spurious
  (not a bivariate factor; ceiling $23$ has no factor $5$).
- **T3** FS Corollary 1 holds on the slice ($\gamma(m)\le N$, primes$(m)\le N$, exponent bound) —
  it must, it is a theorem — and the occurring indices $\{1,2,3\}$ are the small ones FS permits.
- **T4** homogeneous gate: $\operatorname{sixfree}\Phi_n^{\,h}(2,3)=1$ iff $n=1$, over $n=1..30$.
- **T5** sparsest combo $S^{(0)}-S^{(1)}$: fixed 5-term shape, growing degree, growing $6$-free value.

---

## 5. Proposed structure / rationale (what to build instead of FS)

**Re-state the no-go with the correct gate and object.** Replace "reduced polynomial = monomial ×
cyclotomics with indices in $\{1,2,6\}$" (the univariate-slice gate) by:

> **(No-go, corrected form.)** For every nonzero unit-combination of rotations of $W_a$, the reduced
> polynomial factors as $(\text{6-unit at }(2,3))\cdot Q_a(X,Y)$ with $Q_a$ carrying a factor that is
> **not** $6$-smooth at $(2,3)$; equivalently $\operatorname{sixfree}(Q_a(2,3))$ is unbounded in $a$.

This is a **value problem**: a sequence of growing-degree integer polynomials never $S$-unit
(i.e. $6$-smooth) at the fixed point $(2,3)$. The right machinery is **primitive-divisor /
Bang–Zsygmondy** theory for $3^n-2^n$ and, for the genuinely non-cyclotomic $Q_a$,
**lower bounds on $|2^E-3^o|$ / linear forms in logarithms** (the program already invokes Ellison).
FS contributes only the *auxiliary* uniform finiteness "the cyclotomic part has radical $\le N$",
which Bang–Zsygmondy already supplies in stronger form. **Does it close/advance the no-go?** It
**advances the framing** (correct object = bivariate $Q_a$; correct gate = homogeneous, target $\{1\}$;
the draft's $Y=1$ screen is a red herring) and **rules FS out as the closer**. It does **not** close
the no-go.

---

## 6. Open questions

- [ ] **Make "growing degree ⇒ non-$6$-smooth at $(2,3)$" rigorous for $Q_a$.** The honest reduction
      is now an $S$-unit value statement. Can a Bang–Zsygmondy/primitive-divisor argument on the
      *content* of $Q_a$ at $(2,3)$, or a Baker-type lower bound, force a primitive prime $\gt 3$ for
      all large $a$? (Note the low-$a$ coincidence $\operatorname{sixfree}=23$ at $a=2,3$ — any proof
      must be asymptotic.)
- [ ] **Bound the cyclotomic part's *degree*, not just its radical.** FS bounds radical($m$) by $N$
      but lets exponents grow with $\deg f$. Is the cyclotomic part of $Q_a$'s $Y=1$ slice actually of
      *bounded degree* (observed $\le 3$)? If yes, the non-cyclotomic part has degree $\to\infty$
      directly — the clean route the Gen-8 NEXT_FOCUS asked for. This needs a separate argument; FS
      does not give it.
- [ ] **Is the homogeneous gate the *only* way to be $6$-smooth at $(2,3)$?** $Q_a$ is irreducible and
      non-homogeneous, so it has no $\Phi_n^{\,h}$ factor; its value at $(2,3)$ could still be
      accidentally $6$-smooth. Quantify how often (it never is, for $a\ge4$ here) and whether a height
      bound forbids it uniformly.
- [ ] **Does any larger unit-combo (more terms / monomial coefficients) give a uniformly $6$-smooth
      $Q_a$?** The survey covered $k\le3$ scalar combos with small box; the dangerous direction
      (monomial coefficients, $\ge4$ terms) is not exhausted — a uniform $6$-smooth scheme would
      *reopen* the multi-defect case.

---

## 7. Followup references worth queuing

- **Y. Bilu, G. Hanrot, P. Voutier**, *Existence of primitive divisors of Lucas and Lehmer numbers*,
  J. reine angew. Math. **539** (2001), 75–122. — The sharp primitive-divisor theorem; the right
  lever for "$\Phi_n^{\,h}(2,3)$ carries a prime $\gt3$" uniformly (the corrected homogeneous gate).
- **A. Schinzel**, *Primitive divisors of the expression $A^n-B^n$ in algebraic number fields*
  (J. reine angew. Math. 268/269, 1974) or **C. L. Stewart**'s bounds on the greatest prime factor of
  $a^n-b^n$. — Quantitative growth of $\operatorname{sixfree}(3^n-2^n)$, feeding the $S$-unit reduction.

---

## Iteration log
- 2026-06-08 (leverage gen 1): read FS 2004 in full (`sources/filaseta-schinzel-2004.pdf`); stated
  Thm 2 / Cor 1 / Algorithms A,B in our notation. Computed reduced unit-combos for
  $W_a=d^a e_1 d^a e_2 d^a$ ($a=2..8$, defects $(1,3,4)$ and $(1,2,3)$). **Honest finding:** FS does
  not control the no-go — the ceiling is carried by a growing-degree, growing-term-count irreducible
  **non-homogeneous bivariate** factor, while FS needs bounded term count; the only sparse univariate
  shadow ($Y=1$ slice, $N=6$) is the wrong object (spurious cyclotomics; wrong evaluation point) and
  FS merely *permits* its small cyclotomic factors. Extracted two corrections to the draft framing:
  (i) the ceiling object is the bivariate $Q_a$, not the slice; (ii) the correct collapse gate is the
  *homogeneous* one (Zsygmondy on $3^n-2^n$), with target $\{1\}$ not $\{1,2,6\}$. Re-pointed the
  no-go at Bang–Zsygmondy / primitive-divisor machinery. Verified: `checks/lit_filaseta_schinzel.py`
  (T1–T5, exit 0).
