# Leverage L1·5 (Movement III): Suciu–Wang holonomy / cup products — the cup product is the *linearization* of our core, and weight is the structural source of the [P3] ceiling

**Promise:** medium. Continues the Plücker thread (R3) into the cup-product / holonomy /
lower-central-series layer, against STRUCTURE.md §3 (cores $=$ Plücker module $=$ cup product, R1
orientation) and the bounded-defect lever [P3]. Reads the *real* paper and settles the three
Movement-III constructive prizes with kernel proofs. Headline: **one genuinely new, precise relation**
(the cup product is the $\partial_X$-linearization of our core $C$ at the trivial character — the
rank-1 degeneracy made exact), **one structural bridge** (the *weight* / Chen-rank grading is the
named source of the lever's $o$-independence — prize #2), and **two honest nulls** (no smaller
representative is *constructed*, and the holonomy quadratic relation is the Jacobi/C8 we already have).

**Leveraged for / deepens:** the Plücker draft `lit-plucker-bracket.md` (R3; cores $=$ cup product,
C8 $=$ Jacobi) and `bounded-defect-lever.md` ([P3]; the $o$-independent ceiling
$G\le\operatorname{sixfree}(S(\beta d)-S(d\beta))$).

**Status:** read in full (all 27 pp.); dictionary built; all 13 transfers verified on the kernel
(`checks/lit_suciu_wang.py`, exit 0). **Last iterated:** 2026-06-08.

**Source (real, complete; read in full).**
- A. I. Suciu & H. Wang, *Cup products, lower central series, and holonomy Lie algebras*,
  arXiv:1701.07768 (J. Pure Appl. Algebra), v2, 27 pp. —
  [`sources/suciu-wang-holonomy-1701.07768.pdf`](../sources/suciu-wang-holonomy-1701.07768.pdf).
  Cited: Thm 1.1 / Thm 4.3 / 4.4 (cup-product formula $u_i\cup u_j=\kappa(w_k)_{i,j}$); Cor 4.5
  (commutator-relators: $u_i\cup u_j=\varepsilon_{ij}(r_k)$, the augmented **second** Fox derivative);
  eq (4)–(6) and Lemmas 2.2–2.5 (Magnus expansion, the degree-2 coefficient
  $M_2(y)=\sum_{i\lt j}\varepsilon_{i,j}(y)(x_ix_j-x_jx_i)$, antisymmetry, product rule); Thm 1.2 / 5.5
  / Cor 5.6 (holonomy Lie algebra $\mathfrak h(G)=\operatorname{lie}(\mathbf y)/\text{ideal}(\kappa_2(w_k))$,
  **quadratic**); Lemma 6.1 (the comparison $\Phi_G\colon\mathfrak h(G)\twoheadrightarrow\operatorname{gr}(G)$,
  iso in degrees 1, 2, with $\operatorname{im}\mu_G^\vee=\ker[\,,\,]^\vee$, eq (30)); §7 (mildness;
  Labute Thm 7.2 LCS-rank formula; the **weight** $\omega(r)$); §8 (one-relator groups: Prop 8.1, Cor
  8.2, Thm 8.3 — graded-formal $\iff\omega(r)\le2$; §8.2 Chen ranks).

---

## 1. Dictionary (paper ↔ our cocycle layer) — correspondences **and** mismatches

| Suciu–Wang (group $G=F/R$, $F=\langle x_1,\dots,x_n\rangle$) | Our binary cocycle layer |
|---|---|
| Magnus expansion $M(x_i)=1+x_i$, coefficients $\varepsilon_I=\varepsilon\circ\partial_I$ (Fox) | our $\Phi(w)=\begin{psmallmatrix}X^E&S\\0&Y^o\end{psmallmatrix}$ — a **2-dim, degree-$\le1$, $\chi$-twisted** Magnus rep on $F_2=\langle x_0,x_1\rangle$ |
| **degree-1** coeff $\varepsilon_i(w)$ (abelianization) | $\varepsilon_0(w)=E=\lvert w\rvert$, $\varepsilon_1(w)=o=\operatorname{len}w$; our $S$ is the **$\chi$-twisted** $\varepsilon_1$ ($S\rvert_{X=Y=1}=o$) |
| **degree-2** coeff / cup product $\kappa_{i,j}(w)=\varepsilon_{i,j}(w)$ (Thm 4.3, Cor 4.5) | the **single-word crossing number** $A(w)=\varepsilon_{01}(w)-\varepsilon_{10}(w)$ (PART A) — the primitive the drafts never built |
| cup product of a **commutator relator** $=$ wedge $\varepsilon_i(u)\varepsilon_j(v)-\varepsilon_j(u)\varepsilon_i(v)$ (p.24: $\kappa(r)=1+(x_iy_i-y_ix_i)+\dots$) | the **$(E,o)$-wedge** $c(u,v)=E_uo_v-o_uE_v$ — and (PART B) $c(u,v)=\partial_XC(u,v)\rvert_{X=Y=1}$, the **linearization of our core** |
| holonomy Lie algebra $\mathfrak h(G)=\operatorname{lie}(\mathbf y)/\text{ideal}(\kappa_2(w_k))$, **quadratic** (Thm 5.5) | for our free 2-generator ambient: $\mathfrak h=\operatorname{lie}(y_0,y_1)$ **free** (no relator $\Rightarrow$ no cup product; Prop 8.1.2) |
| holonomy quadratic relation $=$ image of $\mu_G^\vee=\ker$(Lie bracket) (eq 30, Lemma 6.1) | the **Jacobi/Plücker** $c(v,w)q_u-c(u,w)q_v+c(u,v)q_w=0$ $=$ the weight-2 **shadow of C8** (PART D) |
| **weight** $\omega(r)=\inf\{\lvert I\rvert:M(r)_I\ne0\}$; LCS ranks depend only on $(n,\omega)$ (Labute Thm 7.2; Cor 8.2; Thm 8.3) | the **combinatorial degree** of a core; the [P3] lever's core $C(\beta,d)$ is a **fixed weight 2** (PART C) |

**The two mismatches that drive everything.**
1. **Untwisted vs. $\chi$-twisted (the rank-1 wall, made precise).** The paper augments at the *trivial*
   character $\varepsilon$ ($x_i\mapsto1$); our $S$ uses the *non-trivial* character $\chi$
   ($x_0\mapsto X,\,x_1\mapsto Y^{-1}$). Their cup product is therefore the **abelianized** wedge
   $c(u,v)=E_uo_v-o_uE_v$, which is exactly the **first-order Taylor coefficient** of our information-rich
   core: $c(u,v)=\partial_XC(u,v)\rvert_{X=Y=1}$ (PART B). The exclusion-carrying content of $C$ lives in
   the **higher-order $\chi$-twist**, which the trivial-character cup product discards — the same rank-1
   degeneracy L1·1/R1 hit, now pinned to a derivative.
2. **Free group vs. free monoid.** The paper needs inverses ($r\in[F,F]$, commutator $uvu^{-1}v^{-1}$);
   our words are free-*monoid* gap words (positive letters, no inverses). The monoid analogue of "second
   Fox derivative of the commutator $[u,v]$" is the concatenation antisymmetrization
   $S(uv)-S(vu)=C(u,v)$ — so our $C$ *is* the monoid commutator-cup-product, no inverse needed.

---

## 2. Relation extracted — the cup product is the **linearization** of our core (NEW, precise)

The paper's degree-2 Magnus / cup-product machinery, translated faithfully, lands on a single clean,
new, **kernel-verified** identity (PART B, symbolic over $\mathbb Z[X,Y]$):
$$\boxed{\;\partial_X\,C(u,v)\big\rvert_{X=Y=1}\;=\;E_u\,o_v-o_u\,E_v\;=\;\langle u\rangle\cup\langle v\rangle\;}
\qquad\text{while}\qquad C(u,v)\big\rvert_{X=Y=1}=0,\quad \partial_Y C\big\rvert_{X=Y=1}=0.$$
That is: **the Suciu–Wang cup product is the $X$-derivative of our core $C$ at the trivial character**;
the value of $C$ there is $0$ and the $Y$-derivative is $0$, so the *entire* weight-2 datum is this one
$\partial_X$-wedge. Two further new objects make the structure transparent:

- **The single-word quadratic primitive** $A(w)=\varepsilon_{01}(w)-\varepsilon_{10}(w)$ (the crossing
  number of the binary word; the antisymmetric weight-2 Magnus coefficient, Lemma 2.2). Its
  concatenation-**coboundary is the cup product** (PART A/B3):
  $$A(uv)-A(u)-A(v)=E_uo_v-o_uE_v=\partial_XC(u,v)\rvert_{X=Y=1},$$
  from the degree-2 Magnus product rule (eq 6) $\varepsilon_{01}(uv)=\varepsilon_{01}(u)+\varepsilon_0(u)\varepsilon_1(v)+\varepsilon_{01}(v)$.
  We had only ever computed cores **pairwise**; $A$ is the **single-word** primitive whose 2-coboundary is
  the (linearized) core — which makes the Plücker/telescoping relations *automatic* (a coboundary is a
  cocycle).
- **NEW vs. R3?** Yes, sharper. R3/`lit-plucker-bracket.md` recorded "cores $=$ cup product" only as
  orientation (R1). The precise content — cup product $=\partial_XC\rvert_{\text{triv}}$, with $C$ the full
  $\chi$-twisted deformation and $A$ the single-word primitive — is new and is the exact statement of
  *what the cup product throws away*.

**Honest framing:** this is **new and translatable**, but it is a **structural / re-expression** result,
not a construction — it shows the paper's invariant is the **shadow** of ours, so it cannot, by itself,
produce a core our richer $C$ does not already see.

---

## 3. Prize #2 (the genuine Movement-III bridge): **weight is why the [P3] ceiling is $o$-independent**

The paper's most useful import is the **weight grading** (Labute Thm 7.2; Suciu–Wang Cor 8.2, Thm 8.3):
for a 1-relator / 2-generator group the holonomy Lie algebra and *all* LCS/Chen ranks depend only on
$(n,\omega(r))$ — on **combinatorial degree, not word length**. This is the named structural source of the
bounded-defect lever's $o$-independence (PART C, all symbolic/exact):

- The lever's reduced core $C(\beta,d)=S(\beta d)-S(d\beta)$ is a **fixed weight-2 cup product**
  $[\beta]\cup[d]$: $\partial_XC(\beta,d)\rvert_{1,1}=E_\beta-d\,o_\beta$, run-free.
- Sliding $\beta$ through the growing background run $d^L$,
  $S(d^k\beta d^{L-k})-S(d^{k+1}\beta d^{L-k-1})=X^{kd}Y^{L-k-1}\,C(\beta,d)$, the reduced core
  $C(\beta,d)$ is **literally $L$-independent** (verified symbolic) — the run only contributes the unit
  monomial $X^{kd}Y^{L-k-1}$. So the ceiling is $o$-independent **because the core sits in a fixed weight**,
  and weight is invariant under the length-growing run. *This is the structural form of [P3].*
- **Witt count** $\dim\operatorname{lie}_2(y_0,y_1)=1$: there is a **unique** weight-2 bracket
  $[y_0,y_1]$, so **every** bounded-defect core is (a $\chi$-evaluation of) the *same* structural element.
  This explains why the whole atlas of bounded-arc ceilings is "one family" (all
  $\operatorname{sixfree}$ of $\Phi_k(2)$-type values, `ceiling_atlas.py`).
- **The multi-gap no-go, in weight language.** When $\ge2$ cyclic gaps grow simultaneously, no *fixed*
  weight-2 commutator $[\beta,d]$ encloses all defects — the trapped second run forces the relevant
  combinatorial degree (the relator weight) to **grow** with $o$. So the open no-go of
  `bounded-defect-lever.md` is exactly *"the trapped configuration has unbounded weight"* — a clean
  weight/Chen-rank-growth restatement (still open; it is a $(2,3)$-arithmetic / Lehmer question the paper
  does not touch).

---

## 4. Prize #1 and Prize #3 — honest nulls

- **Prize #1 (core-generating cup product) — null/degenerate.** The cup product **does not BUILD a smaller
  core**: over the trivial character it *is* the degenerate $(E,o)$-wedge (the linearization, §2); over the
  full twist it *is* $C$, which the paper's machinery re-expresses but does not shrink. No new small member
  of $\mathcal I_D$, no new word-family, beyond P0–P4 and the [P3] arcs. Reason: rank-1 degeneracy — the
  constructive power is the $\chi$-twist, which is **off** the paper's untwisted-augmentation setting (door
  R2 / the integer specialization).
- **Prize #3 (which combinations are forced) — null (re-confirms R3/R4).** The holonomy quadratic relations
  are the image of $\mu_G^\vee=\ker(\text{Lie bracket})$ (eq 30, Lemma 6.1), i.e. the **Jacobi identity**.
  Its weight-2 shadow is $c(v,w)q_u-c(u,w)q_v+c(u,v)q_w=0$ (PART D) — exactly the **linearized C8/Plücker**
  we already have. For our free 2-generator ambient $\mathfrak h$ is *free* (Prop 8.1.2; no relator $\Rightarrow$
  no relation) or carries a single quadratic relation, so **no new forced combination** appears. This is the
  *constructive* re-reading of R4's "no holonomy 3-cell" (pd$E_0\le1$): the holonomy ideal is the Jacobi
  ideal, nothing more.

---

## 5. Verification — `checks/lit_suciu_wang.py` (exit 0, 13/13)

Run from repo root: `python3 ideas/cocycle-combinatorics/checks/lit_suciu_wang.py`.

- **PART A** — second-Magnus product rule (eq 6); the crossing-number primitive $A$ and its coboundary
  $A(uv)-A(u)-A(v)=E_uo_v-o_uE_v$; antisymmetry (Lemma 2.2). (Exact combinatorics on a 6-word battery.)
- **PART B** — *headline*: $\partial_XC\rvert_{X=Y=1}=$ the $(E,o)$-wedge $=$ coboundary of $A$;
  $C\rvert_{X=Y=1}=0$ and $\partial_YC\rvert_{X=Y=1}=0$ (the whole weight-2 datum is the $\partial_X$ wedge).
  Symbolic over $\mathbb Z[X,Y]$ via the kernel `core_C`.
- **PART C** — prize #2: lever factorization $=X^{kd}Y^{L-k-1}C(\beta,d)$ and $L$-independence of $C(\beta,d)$
  (symbolic, $\beta\in\{(3,4),(4,1,1,3),(2,3)\}$, runs $L=3,5,7$, all $k$); lever core linearizes to
  $[\beta]\cup[d]$; Witt $\dim\operatorname{lie}_2(y_0,y_1)=1$.
- **PART D** — prize #3: weight-2 Jacobi/Plücker vector identity on rotation triples; full C8 $=0$.

Symbolic identities use the kernel `S,D,core_C`; Magnus coefficients are exact integer combinatorics on
the binary encoding.

---

## 6. Proposed algebraic structure (what to build)

The paper says: build the **weighted (filtered) refinement of the core module**, indexed by Magnus/bracket
weight, with our cores at the *bottom* (weight 2) as the $\partial_X$-linearization.

1. **The $\chi$-deformation tower of the cup product.** Treat $C(u,v)$ as a one-parameter family in
   $X=1+s$; the weight-$k$ piece is $\partial_X^{\,k}C\rvert_{X=Y=1}/k!$. Weight 1 is the cup product (the
   $(E,o)$-wedge); the higher weights are the **$\chi$-twisted refinements** that carry exclusion. *Question
   to build toward:* is the $o$-independent ceiling of [P3] visible as a **bounded-weight** condition on
   this tower (a fixed finite set of $\partial_X^k C\rvert_{1,1}$ determining $\operatorname{sixfree}$)?
2. **The weight filtration as the home of the [P3] ceiling.** Formalize "the lever works $\iff$ the defect
   sits in a *fixed* weight-2 commutator," and "the no-go $\iff$ the trapped configuration has unbounded
   weight." Labute's LCS formula (eq 36) gives the *dimension* of each weight; the build is to read
   $\operatorname{sixfree}$-boundedness off a bounded-weight cut.
3. **Promote $A$ (the single-word crossing primitive) to a reduction bookkeeping device.** Since
   $\delta A=$ (linearized) core, $A$ turns pairwise core arithmetic into single-word arithmetic; it may
   give a cleaner certificate that a word-combination lies in $\mathcal I_D$ (a coboundary is automatically
   a cocycle / telescopes).

---

## 7. Open questions (feed the next probe — find-thread / R2 / the lever)

1. **Does the weight tower beat the linearization?** Compute $\partial_X^kC(\beta,d)\rvert_{1,1}$ for
   $k\ge2$ on the bounded-arc family: is $\operatorname{sixfree}(C(\beta,d)(2,3))$ determined by a *bounded*
   number of weight slices — i.e. is exclusion a **finite-weight** phenomenon? (If yes, that is the genuine
   bridge to "finitely many invariants per fixed combinatorial degree" — the L1·6 modular-knot Burau prize.)
2. **Weight of the trapped multi-gap configuration.** Make precise (and bound) the Magnus weight
   $\omega$ of the $\ge2$-growing-gap relator; show $\omega\to\infty$ in the second run length. A clean
   weight-growth lemma would convert the open no-go into a Chen-rank statement (then hand the residual
   $(2,3)$-arithmetic to the Layer-2 Bang–Zsygmondy/Lehmer thread).
3. **The twisted (rank-$\ge2$) cup product (door R2).** Suciu–Wang's machinery is exact for the trivial
   character; the informative part of $C$ is the $\chi$-twist. A genuine *twisted* (local-system) cup
   product — Massey-product / holonomy with the $\chi$-local system — would be the off-ring object that
   actually carries the exclusion. This is the natural L1·6 / R2 follow-up.

## Iteration log
- 2026-06-08 (L1·5, Gen 1): read Suciu–Wang in full; built the dictionary (untwisted cup product $=$
  our $(E,o)$-wedge; free-monoid vs free-group; weight $=$ combinatorial degree). Verified (13/13):
  the cup product is $\partial_XC\rvert_{X=Y=1}$ (the linearization of our core), with single-word
  primitive $A$ whose coboundary is the cup product; the [P3] lever core is a fixed weight-2 element
  ($o$-independent), unique weight-2 bracket (Witt); the holonomy quadratic relation $=$ Jacobi $=$ the
  weight-2 shadow of C8. **Constructive verdict: NO new smaller representative / family** — the cup
  product is the rank-1 shadow of $C$; the constructive power is the $\chi$-twist (off-ring). **Value:**
  prize #2 bridge — *weight* is the named structural source of the lever's $o$-independence, and the
  multi-gap no-go is a weight-growth statement. Two honest nulls (prizes #1, #3).
