# Cheatsheet

Quick reference for the formulas and partial results in this project. **Statements only —
no proofs here.** Each item links to the approach file holding the full derivation. When a
result lands or changes, update the source file *and* this line.

See [`APPROACHES.md`](APPROACHES.md) for the index of approaches.

## Notation conventions

Canonical, project-wide (fixed in [`diophantine`](approaches/diophantine/RATIONALE.md)):

- **Accelerated (odd-to-odd / Syracuse) map.** $a_0$ is an odd start; $a_1, a_2, \dots$ are
  the successive odd terms produced by $a_{k+1} = (3a_k+1)/2^{\,e_{k+1}-e_k}$ (apply $3x+1$
  once, divide out all factors of $2$).
- $e_k$ = number of even steps **before** the $k$-th odd term, $e_0 = 0$. Equivalently
  $e_{k+1}-e_k = \nu_2(3a_k+1) \ge 1$; $(e_k)$ strictly increasing.
- $o$ = index of the final odd term under consideration.
- **Equivalence:** `parity-manipulation`'s $(b_k, x_k, n)$ are the *same objects* as
  $(e_k, a_k, o)$ — same accelerated map, identical identity. The $b/x/n$ vs $e/a/o$ choice
  is purely notational.

## Core identity

> **Diophantine closed form.** For an odd start $a_0$ and any $o \ge 1$,
> $$2^{e_o}\,a_o \;-\; 3^{o}\,a_0 \;=\; \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k}.$$
> The identity is **algebraic**: it needs only the recurrence
> $2^{e_{k+1}-e_k}a_{k+1}=3a_k+1$, not oddness or positivity — so it holds over
> $\mathbb{Z}$, $\mathbb{Q}$, and $\mathbb{Z}_2$. Oddness ($e_{k+1}-e_k=\nu_2(3a_k+1)$) is
> only needed to identify the sequence as a genuine Syracuse orbit.
> — [`diophantine`](approaches/diophantine/RATIONALE.md) · proof status:
> [`STATUS`](approaches/diophantine/STATUS.md) (skeleton verified, formal write-up pending)

> **2-adic reconstruction.** For a strictly increasing $(b_k)_{k\ge0}$ with $b_0=0$, there is
> a unique trajectory in $\mathbb{Z}_2$ with that parity behavior, with start
> $$x_0 = -\sum_{k=0}^{\infty}\frac{2^{b_k}}{3^{k+1}} \in \mathbb{Z}_2.$$
> The map (strictly increasing $(b_k)$) $\leftrightarrow$ ($x_0 \in \mathbb{Z}_2$) is a
> bijection. — [`parity-manipulation`](approaches/parity-manipulation/RATIONALE.md)

## Partial results

### cycle-gcd

> **Cycle equation.** A cycle ($a_o=a_0$) forces, with $D := 2^{E}-3^{o}$ and $E:=e_o$,
> $$D\,a_0 \;=\; S^{(0)} \;:=\; \sum_{k=0}^{o-1} 2^{e_k}\,3^{\,o-1-k}, \qquad a_0 = S^{(0)}/D.$$
> — [`STATUS`](approaches/cycle-gcd/STATUS.md)

> **Rotation recursion (algebraic).** For a gap word $w$ ($d_k=e_{k+1}-e_k$) and its left
> rotation $w'$, with $S(\cdot)$ the RHS sum: $2^{d_0}\,S(w') = 3\,S(w) + D$. Holds over
> $\mathbb{Z}$ for any word. Corollary: $\gcd_j S^{(j)} \mid 2^{E}-3^{o}$ for every word.
> — [`STATUS`](approaches/cycle-gcd/STATUS.md)

> **Exact gcd on cycles.** For a genuine cycle, $D \mid S^{(j)}$ for all $j$ collapses with the
> corollary above to $\gcd_{j} S^{(j)} = |2^{E}-3^{o}|$ exactly. Hence a finiteness bound must
> come from an *a-priori* upper bound on the gcd (word structure only), not from divisibility.
> — [`STATUS`](approaches/cycle-gcd/STATUS.md)

> **Criticality lemma.** With $2^E>3^o$, call $(E,o)$ *critical* if $E=\lceil o\log_2 3\rceil$
> (the unique integer in $(o\log_2 3,\,o\log_2 3+1)$, minimizing $2^E-3^o$). Then non-critical
> $\iff E>o\log_2 3+1 \iff 2^{E-1}>3^o$, and in that case $2^E-3^o>2^{E-1}$. A positive cycle
> has $2^E>3^o$ and is critical $\iff 2^E<2\cdot3^o \iff \prod_k(1+\tfrac1{3a_k})<2$.
> *Caveat:* "every primitive cycle is critical" is **not** provable from this size bound alone
> (witness $(E,o)=(9,5)$, word $(1,2,2,2,2)$: $\min_j S^{(j)}=431>D=269$); it needs the
> divisibility/gcd or Baker input. — [`STATUS`](approaches/cycle-gcd/STATUS.md)

### diophantine-distribution

> **Fundamental solution.** The word-map $F_w=T_{d_{o-1}}\circ\cdots\circ T_{d_0}$ ($T_d(x)=(3x+1)/2^d$)
> is affine, $F_w(x)=\tfrac{3^o}{2^E}x+\tfrac{S(w)}{2^E}$, with unique fixed point
> $x_w^\ast=S(w)/D(w)\in\mathbb{Z}_2$ ($D$ odd). On a cycle it is the start ($D\mid S$).
> — [`fundamental.md`](approaches/diophantine-distribution/fundamental.md) FS1–FS2

> **All trajectories with word $w$.** $\{x\in\mathbb{Z}_2 : \text{word}(x)=w,\ a_o\text{ odd}\}
> = x_w^\ast + 2^{\,|w|+1}\mathbb{Z}_2 = x_w^\ast + 2k\cdot2^{|w|}\mathbb{Z}_2$ (Terras + word↔
> compressed-string; the extra bit certifies the word closes on an odd $a_o$).
> — [`fundamental.md`](approaches/diophantine-distribution/fundamental.md) FS3

> **Imbalance factorization.** $S(w)/D(w)=\eta/(\beta-3)$, $\beta=2^{E/o}$, with
> $\eta\in[2^{-p},2^{p}]$, $p=\max_k|e_k-\tfrac{E}{o}k|$ (balanced-word lemma
> $\sum_k\beta^k3^{o-1-k}=D/(\beta-3)$). Contracting+large ($\beta\ge\tfrac72$) $\Rightarrow$
> $0\lt x_w^\ast\le2^{\,p+1}$, independent of $E$.
> — [`fundamental.md`](approaches/diophantine-distribution/fundamental.md) FS4–FS5

> **Flying time ⟺ conjecture.** Finite flying time $\max\{n:T^n(x)\ge x\}$ for all positive
> integers implies Collatz (strong induction). — [`STATUS`](approaches/diophantine-distribution/STATUS.md)

### cocycle-combine

> **Compensation principle.** On a cycle $G:=\gcd_j S^{(j)}=|2^E-3^o|$ is odd, so every
> $\mathbb{Z}[X,Y]$-linear combination $\sum_j c_j S^{(j)}$ of rotation sums is divisible by $G$.
> A combination *compensating* to a small core $C\neq0$ gives the a-priori ceiling
> $|2^E-3^o|\le|C|$. — [`STATUS`](approaches/cocycle-combine/STATUS.md)

> **Single-defect circuit ceiling (certified).** For a cycle with gap word $d^a e\,d^b$ (a
> constant circuit $d^{o-1}$ with one altered gap $e$, $o=a+b+1$): the last adjacent rotation
> difference is $S^{(o-2)}-S^{(o-1)}=X^{(o-1)d}(X^{e-d}-1)$, so
> $$|2^E-3^o|\ \le\ 2^{\,|e-d|}-1,$$
> **independent of the multiplicities $a,b$** — finitely many such cycles per defect $(d,e)$.
> Degenerate $\iff e=d$ (pure circuit). — [`reports/P2.md`](approaches/cocycle-combine/reports/P2.md)

### parity-manipulation

> **General single-block shift.** For $b'_k = b_k + a\,\mathbf{1}_{k>q}$ ($a\in\mathbb{Z}$,
> $a > -c_{q+1}$):
> $$x_0 - x'_0 = -(2^a-1)\,2^{b_{q+1}}\,x_{q+1}/3^{q+1}.$$
> — [`STATUS`](approaches/parity-manipulation/STATUS.md)

> **Integrality theorem.** For integer trajectories, $x_0 - x'_0 \in \mathbb{Z}
> \iff 2\cdot 3^q \mid a$. Minimal admissible shift $a = 2\cdot 3^q$. Positive $a$ →
> predecessor moves; negative $a$ (with $|a|\le c_{q+1}-1$) → successor moves.
> — [`STATUS`](approaches/parity-manipulation/STATUS.md)

> **3-adic / LTE lemma.** $\nu_3(2^a-1) = 0$ if $a$ odd, $=1+\nu_3(a)$ if $a$ even;
> equivalently $\operatorname{ord}_{3^{q+1}}(2) = 2\cdot 3^q$.
> — [`STATUS`](approaches/parity-manipulation/STATUS.md)

> **Finite-support no-go.** If $b'_k - b_k = 0$ for all $k \ge N$, then $x'_k = x_k$ for all
> $k \ge N$: any finite-support perturbation only re-routes the *past* of a fixed downstream
> node — it stays inside the inverse Collatz tree. New content requires **infinite-support**
> perturbations. — [`STATUS`](approaches/parity-manipulation/STATUS.md)

### places-elimination

> **Elimination criterion.** Take a family with growing blocks $\beta_i^{m_ia+c_i}$. An $o$-independent
> core exists iff $V(D,S)\subset\mathbb T\times T_F$ does not dominate $\mathbb T=\mathbb G_m^2$. When all
> growing blocks share one slope ($r=1$), $D$ and $\big(\prod(X^{|\beta|}-Y^{\mathrm{len}\beta})\big)S$ are
> binary forms in $[X^{pa}:Y^{qa}]$, and their resultant is the core.
> — [`RATIONALE`](approaches/places-elimination/RATIONALE.md) §3

> **Two-run ceiling.** Every cycle with gap word $d^ae_1d^ae_2d^a$ has
> $D\mid 4^{e_1}(2^d-2^{e_2})^3+3\cdot2^{e_2}(2^d-2^{e_1})^3$, which is nonzero unless $e_1=e_2=d$.
> — [`RATIONALE`](approaches/places-elimination/RATIONALE.md) §4 · Lean `TwoRun.twoRun_ceiling`

> **r = 1 classification.** For a one-parameter family whose growing blocks share one slope, either
> the cycle set is finite (explicit bound, no Baker input) or $S/D$ is constant along the family and
> the members are powers of one cycle word. The verified procedure is `R1.decideR1`.
> — [`CLASSIFICATION`](approaches/places-elimination/CLASSIFICATION.md)

> **Towers.** For fixed positive words $u_0\ne\varnothing,u_1,\dots,u_k$, the words
> $((u_0^{a_1}u_1)^{a_2}u_2)\cdots u_k$ (all $a_i\ge1$) contain cycle words of only finitely many
> cycles. — [`NESTED`](approaches/places-elimination/NESTED.md) · Lean `R1.tower_cycleStarts_finite`

> **Two-block skeleton.** For $\beta^ax\,\gamma^ay$ with $|\beta|=|\gamma|$ and $\mathrm{len}\beta=\mathrm{len}\gamma$,
> $D=2^p-3^q$: every cycle has
> $D(W)\mid P_xQ_x[(DS_y-P_yS_\beta)^2+2DQ_yS_\gamma S_y+Q_y^2S_\gamma^2]-P_yQ_y[(DS_x-P_xS_\gamma)^2+2DQ_xS_\beta S_x+Q_x^2S_\beta^2]$.
> — [`SKELETONS`](approaches/places-elimination/SKELETONS.md) · Lean `R1.Skel.TwoBlock.ceiling`

> **Same-side two exponents.** For $u^axv^by$ with $u,v$ on the same side of $\log_2 3$:
> $D(v)\,C(u,xv^by)=\alpha 2^{b|v|}-\beta 3^{b\,\mathrm{len}\,v}$, so $a$ is bounded, and each $a$ is a $w^aw'$
> family in $b$. — [`PATTERNS`](approaches/places-elimination/PATTERNS.md) · Lean `R1.twoExp_classification`

> **Any sides, from Matveev.** For $u^axv^by$ off the loci, $|D|\le k_uG_v^{\,b}$ and $|D|\le k_vG_u^{\,a}$ multiply to
> $\max(2^E,3^O)^2/2^{a+b}$, so $2^{a+b}\le K(a+b+1)^{2\lceil c_0\rceil}$. — [`PATTERNS`](approaches/places-elimination/PATTERNS.md) §6 · Lean `R1.twoExp_cycles_of_matveev`

> **Tropical budget.** Independent blocks $u_j^{a_j}$: with $P=2^{|u|}$ and $Q=3^{\mathrm{len}\,u}$, put
> $A=\sum_{P\gt Q}(1-\log Q/\log P)$ and $B=\sum_{P\lt Q}(1-\log P/\log Q)$. If $\min(A,B)\lt1$, finitely many
> cycles lie off the loci (Matveev). — [`SCHEME`](approaches/places-elimination/SCHEME.md) §2.4 · `budget.py`
