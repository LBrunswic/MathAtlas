# Leverage L1·8 (Movement IV): homotopical completion-with-expansion — leveraged for the expansion-reduction spine

**Promise:** medium. L1·8 reads the *real* Guiraud–Malbos–Mimram homotopical
**completion–reduction** procedure (the procedure that ADDS generators / rules / coherence cells via
Tietze transformations — *completion-with-expansion*, non-length-monotone) against STRUCTURE.md §0
(the integer cyclic quotient $A$, expansion-reduction) / §2 / §3, the L1·3 C8 overlap $\delta$, and the
[P3] run-sliding lever. **Decides the Movement-IV question:** does completion-with-expansion give a
**new** expansion-reduction move on the cyclic roll — a longer-word path to a *small residue mod $G$*
beyond the single C8 closure — or does it terminate at C8/[P3] (honest null, with the reason)?

**Constructive verdict (verified, 14/14 on the kernel): NO new expansion / no smaller residue.**
Completion-with-expansion adds nothing beyond the C8 overlap $\delta$ and the fixed weight-2 core
$C(\beta,d)$ of [P3] — and the paper supplies the *two complementary reasons why*, plus **one genuinely
useful positive import**: the **quasicenter heuristic** (§3.4) is the exact constructive criterion for
*when the [P3] lever exists*, and its boundary is the still-open $\ge2$-growing-gap no-go. The
headline gain is a clean rewriting reading of [P3]: the run-sliding rule $\beta d\Rightarrow d\beta$
slid across the expanded run $d^L$ generates the **infinite family** of steps — the precise analog of
the Kapur–Narendran family $stsst^k=ts^{k+1}ts$ — whose **completion is the single fixed core**
$$\boxed{\,S(\beta\,d^L)-S(d^L\,\beta)=S(d^L)\cdot C(\beta,d)\,},\qquad
  S(d^L)=\frac{X^{Ld}-Y^L}{X^d-Y},$$
each adjacent step $X^{kd}Y^{L-1-k}C(\beta,d)$ a **monomial multiple of one fixed weight-2 2-cell**.

**Leveraged for / deepens:** the L1·3 critical pair $\delta$ (`lit-groebner-shirshov.md`), the [P3]
lever / weight bridge (`lit-suciu-wang.md`, `bounded-defect-lever.md`), the ceiling atlas
(`checks/ceiling_atlas.py`).

**Status:** read in full (all 16 pp., §1 intro → §5 conclusion + refs); dictionary built; verdict
verified (`checks/lit_homotopical_completion.py`, 14/14, exit 0). **Last iterated:** 2026-06-09.

**Source (real, complete; read in full; identity CONFIRMED before reading).**
- Y. Guiraud, P. Malbos, S. Mimram, *A Homotopical Completion Procedure with Applications to Coherence
  of Monoids*, **RTA 2013**, LIPIcs vol. 21, pp. 223–238, DOI 10.4230/LIPIcs.RTA.2013.223 —
  [`sources/guiraud-malbos-mimram-homotopical-completion-RTA2013.pdf`](../sources/guiraud-malbos-mimram-homotopical-completion-RTA2013.pdf).
  Cited: eq. (1)–(3) + Ex. 10 (Kapur–Narendran $\mathbf B_3^+$, the superfluous generator $a=st$);
  Def. (p.228, the **six elementary Tietze transformations** — esp. **add a generator** $\mathcal T_u^+$:
  $x_u\in\Sigma_1$, $\delta_u:u\Rightarrow x_u$); Thm 7 (Tietze-equivalence); §2.3 Thm 8 (Squier);
  §3.1 Thm 9 ($\mathcal{HC}$); §3.2 Ex. 12 (the **weight-homogeneity** argument); §3.3 Thm 13
  ($\mathcal{HCR}$) + Ex. 14; **§3.4 (p.232) — completion/reduction on generators, the QUASICENTER
  heuristic** $uX=Xu$; §4 (braid: Artin/Kapur–Narendran/Garside/Brieskorn–Saito presentations, the
  Kapur–Narendran obstruction $stsst^k=ts^{k+1}ts$ p.233; plactic column = quasicenter generators;
  Chinese quasicentral; Table 1).
  *Note — this is NOT the R4 paper:* R4 read Guiraud–Malbos arXiv:1011.0558 (*acyclicity*, Adv. Math.
  2012, the $H_2$/3-cell question); this is the distinct RTA 2013 *completion-with-expansion* paper.

---

## 1. Dictionary — completion-with-expansion ↔ our cocycle rewriting (with the two driving mismatches)

| Guiraud–Malbos–Mimram | Our cocycle / integer-quotient layer |
|---|---|
| presentation $\langle\Sigma_1\mid\Sigma_2\rangle$ of a monoid $\mathbf M$ (e.g. $\mathbf B_3^+=\langle s,t\mid tst{=}sts\rangle$) | the binary word monoid $W=\{x_0,x_1\}^\ast$ — **FREE**, $\Sigma_2=\varnothing$ (the central mismatch, below) |
| **rewriting rule** $\rho:u\Rightarrow v$ (a monoid relation, length-monotone or not) | the **rotation/antisymmetry rule** $uv\Rightarrow vu$ — an *algebra*-level relation with defect the core $C(u,v)=S(uv)-S(vu)$ |
| **Tietze "add a generator"** $\mathcal T_u^+$: $x_u\in\Sigma_1$, $\delta_u:u\Rightarrow x_u$ (the EXPANSION move; $a=st$ in $\mathbf B_3^+$) | **block-coarsening** to a super-letter $x_u:=u$ with $\Phi(x_u):=\Phi(u)$ — **$S$-INVISIBLE** ($S(x_u)=S(u)$): the Magnus map $\Phi=\begin{psmallmatrix}X^E&S\\0&Y^o\end{psmallmatrix}$ is a faithful monoid hom (PART A) |
| **Kapur–Narendran infinite family** $stsst^k=ts^{k+1}ts$ ($k\ge1$) forced in every convergent system on $\{s,t\}$; collapses on adding $a$ | the **run-sliding family** $d^k\beta d^{L-k}\to d^{k+1}\beta d^{L-k-1}$ ($k,L\ge0$); collapses to the single fixed core $C(\beta,d)$ (PART B = [P3]) |
| **quasicenter heuristic** (§3.4): add minimal $u$ with $uX=Xu$ for maximal $X\subseteq\Sigma_1$; $\lvert X\rvert$ sets the termination order | the lever exists $\iff$ word $=$ (bounded defect $\beta$)$\cdot$(run $d^L$ in the **cyclic quasicenter** $\langle d\rangle$); the run *is* the quasicenter, $\beta$ the bounded non-commuting part (PART D) |
| **weight-homogeneity** (Ex. 12: $s,t$ wt 1, $a$ wt 2 $\Rightarrow$ growing critical branchings add no new cell) | the core $C(\beta,d)$ is a **fixed weight 2** (cup product $[\beta]\cup[d]$, L1·5); sliding across $d^L$ preserves weight $\Rightarrow$ no new cell as $L\to\infty$ (PART D2) |
| coherent presentation / homotopy basis (3-cells fill confluence diagrams) | the **first-syzygy module** of the cores: Plücker pair + telescoping (R3/R4) — **complete, no 3-cell** over $\mathbb Q[X,Y]$ |

**The two mismatches that drive the verdict.**
1. **FREE monoid vs. monoid-with-relations (the central one).** The paper's whole engine acts on a
   *monoid presentation with genuine relations* — completion needs critical pairs, which need
   $\Sigma_2\ne\varnothing$. Our word monoid $W$ is **free**: trivially convergent, no critical pair,
   empty homotopy basis. So at the *monoid* layer there is literally nothing to complete. Our relations
   live one level up, in the **integer cyclic quotient algebra** $A=\mathbb Z[W]/\ker(\pi\circ S)$ (mod
   $G$) — $\mathbb Z$-linear relations among words, the **cores**, not monoid equalities $u=v$. The
   correct transfer is therefore *not* "complete the monoid $W$" but "what does the Tietze/expansion
   machinery do to the *core arithmetic* in $A$" — and the answer is governed by mismatch 2.
2. **Length-monotone vs. NON-length-monotone, but $S$-graded either way.** The paper's payoff is exactly
   that adding $a=st$ is **non-length-monotone** (a rule $st\Rightarrow a$ that *shortens*, plus
   $ta\Rightarrow as$ that doesn't respect $\lvert\cdot\rvert$). This is the door L1·3 left open
   ("relax the length order"). But in our setting the *cocycle is a homomorphism*: any Tietze
   re-encoding (length-monotone or not) extends $\Phi$ uniquely and **changes no value of $S,D,\chi$**.
   So relaxing the length order buys a different *presentation* of the same words but the **same
   arithmetic in $A$** — the door opens onto the same room.

---

## 2. Relation / move extracted — the rewriting form of [P3] (NEW packaging; no new lever)

The paper's "orient a relation and slide it across a growing context, watch the critical family
collapse onto an added generator" is, in our notation, the **run-sliding expansion** with a clean
closed form (PART B, symbolic over $\mathbb Z[X,Y]$, all $\beta,d,L$ in the stated ranges):

$$S(\beta\,d^L)-S(d^L\,\beta)=S(d^L)\cdot C(\beta,d),\qquad
  S(d^L)=\sum_{k=0}^{L-1}X^{kd}Y^{L-1-k}=\frac{X^{Ld}-Y^L}{X^d-Y},$$
$$S(d^k\beta d^{L-k})-S(d^{k+1}\beta d^{L-k-1})=X^{kd}\,Y^{L-1-k}\,C(\beta,d)\quad(\text{each step}).$$

Reading: orient the rotation rule $\beta d\Rightarrow d\beta$ and apply it once inside the context
$d^k\cdot\_\cdot d^{L-k-1}$. As $k,L$ range, this is the **infinite family of rewriting steps** — the
exact analog of Kapur–Narendran's $stsst^k=ts^{k+1}ts$ — and every step is a **monomial (=6-unit at
$(2,3)$) multiple of the single fixed weight-2 core** $C(\beta,d)$ (PART B4). The *completion* of this
infinite expansion family is therefore **one fixed 2-cell** $C(\beta,d)$, just as adding $a=st$
collapses the braid family. The "completion coefficient" is the run's own cocycle $S(d^L)$.

- **NEW vs. [P3]/L1·5?** The *identity content* is the same lever (L1·5 verified the per-step factor
  $X^{kd}Y^{L-k-1}C(\beta,d)$). What is new is the **rewriting packaging**: (i) the telescoped form
  $=S(d^L)\,C(\beta,d)$ with the explicit completion coefficient $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$, and
  (ii) the identification of the family as a *Kapur–Narendran infinite relation family that completes to
  one generator* — naming *why* the lever is a finite (single-cell) object rather than an unbounded one.
- **No new move, because** (PART A) the only thing completion-with-expansion can *add* is a
  super-letter $x_u:=u$, and $\Phi$ being a faithful hom makes that **$S$-invisible** — it produces no
  cocycle value, hence no residue, that the flat word didn't already have. (Rewriting form of L1·3
  per-stratum injectivity.) And (PART C) the L1·3 overlap $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$
  is **coarsening-invariant**: completion-with-expansion re-derives the same C8/Plücker closure, no new
  cell. So the system is *already* complete at C8 + the fixed [P3] core.

**Honest framing.** This is a **re-expression + a constructive criterion**, not a construction of a
smaller representative. The paper's non-length-monotone door is real *for monoids with relations*; for
our free monoid / faithful cocycle it adds no arithmetic. The win is naming the lever's finiteness
(completion of an infinite family to one fixed cell) and the criterion for when it exists.

---

## 3. Constructive verdict — does completion-with-expansion construct a smaller residue mod $G$?

**No, and the paper says precisely why — plus the positive criterion (the quasicenter heuristic).**

- **(why no — A)** *$S$-invisibility.* Tietze generator-adding $\mathcal T_u^+$ is the only expansion
  move, and it extends the faithful Magnus hom $\Phi$ with $S(x_u)=S(u)$: a re-encoding, no new value
  mod $G$ (PART A, 80 random block-coarsenings).
- **(why no — B/C)** *Weight-homogeneity / already-complete.* The run-sliding subsystem is a
  *deterministic chain* (one rewrite site per word $d^k\beta d^{L-k}$): no critical branching, trivially
  confluent, defect $=$ the fixed weight-2 core. The paper's own Ex. 12 weight-homogeneity argument is
  the mechanism — a weight-homogeneous system slid across a growing context generates no new cell. So
  $\mathcal{HC}$ terminates at $C(\beta,d)$; $\mathcal{HCR}$ removes the superfluous super-letters; the
  reduced coherent presentation is the L1·3 C8 + the fixed [P3] core. (PART B/C, 60 random overlaps.)
- **(the positive criterion — D)** *The quasicenter heuristic IS the lever's existence criterion.*
  §3.4: add the generator $u$ with $uX=Xu$ for a maximal $X$ — "$\lvert X\rvert$ determines the
  termination order." Translated: the [P3] lever works exactly when the word factors as a **bounded
  defect $\beta$** times a **run $d^L$ in the cyclic quasicenter $\langle d\rangle$** (one growing run);
  the run *is* the quasicenter (it commutes with itself), $\beta$ is the bounded non-commuting part, and
  the ceiling $\operatorname{sixfree}(C(\beta,d))$ is **$o$-independent** — every adjacent step carries
  the *same* fixed sixfree value, $L$-independent (PART D1, $L=2..7$), and $\textbf{not lowered}$ by
  expansion (the run contributes only the 6-unit monomial $X^{kd}Y^{L-1-k}$ — PART D3, the honest null).
  The **$\ge2$-growing-gap no-go** is exactly *"no single quasicenter run encloses all defects"*: the
  word needs two independent generators-to-add, the family does not complete to one fixed-weight cell,
  and the weight grows ($\omega\to\infty$, L1·5). That residual is still open and is a $(2,3)$-arithmetic
  question the paper does not touch.

---

## 4. Verification — `checks/lit_homotopical_completion.py` (exit 0, 14/14)

Run from repo root: `python3 ideas/cocycle-combinatorics/checks/lit_homotopical_completion.py`.

- **PART A (3)** — Tietze "add generator" $\mathcal T_u^+$ is $S$-invisible: super-letter coarsening
  reproduces flat $S(u)$ (Magnus hom via the kernel matrix $\Phi$, 80 random block-decompositions);
  $\chi,D$ inherited. $\Rightarrow$ no new residue mod $G$ from generator-adding.
- **PART B (4)** — the run-sliding identity: telescope $S(\beta d^L)-S(d^L\beta)=S(d^L)C(\beta,d)$;
  adjacent step $=X^{kd}Y^{L-1-k}C(\beta,d)$; run cocycle $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$; every step a
  **monomial** multiple of the single fixed core (infinite family $\to$ one 2-cell). Symbolic over
  $\mathbb Z[X,Y]$, $\beta\in\{(3),(2,3),(3,2),(4,1,1,3)\}$, $d\in\{1,2,3\}$, $L=1..5$.
- **PART C (3)** — the L1·3 overlap $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$ (60 random
  3-block overlaps), $\delta\in\operatorname{span}_R\{C(A,B),C(B,C)\}$ (closes via C8), and $\delta$ is
  coarsening-invariant (completion-with-expansion re-derives C8, no new cell).
- **PART D (4)** — quasicenter / honest null: every adjacent step has fixed $o$-independent ceiling
  $\operatorname{sixfree}(C(\beta,d)(2,3))$ ($L=2..7$); cup product $[\beta]\cup[d]=\partial_XC\rvert_{1,1}$
  fixed weight-2; **expansion does NOT lower the ceiling** (D3); $G\mid$ the realized residue
  $S(d^L)C(\beta,d)$ at $(2,3)$ (40 random words).

Symbolic identities use the kernel `S,D,core_C`; the super-letter $\Phi$ is the kernel's Magnus matrix;
numeric ceilings at $(X,Y)=(2,3)$ via `gcd_rotations`.

---

## 5. Proposed structure (what to build for Movement IV)

**Quasicenter-stratified completion of the cocycle rewriting system** — the home of `ceiling_atlas.py`,
named:

1. **Stratify word-families by quasicenter decomposition.** Each Collatz-relevant family is
   (bounded defect arc $\beta$)$\cdot$(growing run $d^L$, $d$ the background letter). The §3.4 heuristic
   says: the *background letter's run is the quasicenter generator to add*, and the family
   **completes** to the single weight-2 2-cell $C(\beta,d)$ iff there is **one** growing run. Build the
   atlas as exactly this table: rows $=$ bounded arcs $\beta$, the entry $=$ the fixed core
   $C(\beta,d)$ and its $\operatorname{sixfree}$ ceiling. This reframes `ceiling_atlas.py` as "the
   reduced coherent presentation ($\overline{\mathcal{HCR}}$) of the cocycle rewriting system."
2. **The completion coefficient $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$ as the run functor.** It is the only
   $L$-dependence; it is a **6-unit at $(2,3)$ up to the genuine factor**, so it never enters the
   ceiling. Formalize "the run contributes a unit, the defect contributes the fixed core" — the exact
   statement of $o$-independence as a *completion-terminates-in-one-cell* theorem.
3. **The $\ge2$-gap no-go as a non-completion / quasicenter-obstruction theorem.** Build the precise
   statement: when two gaps grow, no single quasicenter run encloses the defects, the Kapur–Narendran
   family does *not* collapse to one generator, and the relator weight $\omega\to\infty$ (L1·5). The
   residual is a $(2,3)$-arithmetic (Bang–Zsygmondy/Lehmer) question — hand to Layer-2. *This is the
   clean restatement of the open lever.*

---

## 6. Open questions (feed L1·9 circulant / find-thread)

1. **Two quasicenter generators (the $\ge2$-gap completion).** Make the $\ge2$-growing-gap no-go a
   precise non-completion statement: with two runs $d^{L},e^{M}$ and defects between them, does the
   critical-branching family fail to complete to a *finite* set of fixed-weight cells? Bound the relator
   weight $\omega$ as a function of $\min(L,M)$ (the weight-growth lemma L1·5 asks for). — feeds L1·9.
2. **Circulant lift (L1·9).** The run cocycle $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$ is a cyclotomic/resultant
   object ($\prod_\zeta$ over $d$-th-power roots). The rotation orbit is a $\mathbb Z[\mathbb Z/o]$
   circulant; does the Silver–Williams resultant $r_m(\Delta)=\prod_\zeta\Delta(\zeta)$ give the integer
   residue of the orbit mod $G$ that the polynomial layer can't see, and does it *construct* a smaller
   combination than the single fixed core? — the natural L1·9 probe.
3. **Garside/Brieskorn–Saito analog.** The paper's *finite* quasicenter presentations (Garside:
   generator of the quasicenter + all divisors; Brieskorn–Saito) terminate where Artin generators don't.
   Is there an arithmetic Garside object — a *finite* set of "quasicenter cores" $\{C(\beta_i,d)\}$ —
   whose ceilings cover a whole multi-gap family at once? (A finite atlas closing a family.)

## Iteration log
- 2026-06-09 (L1·8, Gen 1): downloaded & confirmed the **real** RTA 2013 Guiraud–Malbos–Mimram
  completion-with-expansion paper (distinct from R4's arXiv:1011.0558). Read in full. Built the
  dictionary (Tietze add-generator $=$ $S$-invisible block-coarsening; Kapur–Narendran infinite family
  $=$ run-sliding; quasicenter heuristic $=$ the lever's existence criterion; weight-homogeneity $=$ the
  $o$-independence mechanism). **Constructive verdict: NO new expansion / no smaller residue** — the
  run-sliding family completes to the single fixed weight-2 core $C(\beta,d)$, the C8 overlap $\delta$ is
  coarsening-invariant, and $\Phi$ faithful makes generator-adding $S$-invisible. **Gains:** the
  rewriting packaging of [P3] (telescope $=S(d^L)C(\beta,d)$, completion coefficient
  $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$) and the **quasicenter criterion** for when the lever exists (boundary
  $=$ the open $\ge2$-gap weight-growth no-go). Verified 14/14 (`checks/lit_homotopical_completion.py`,
  exit 0). Honest null on the new-move prize; the criterion + packaging are the value. **Next: L1·9
  (Silver–Williams circulant/resultant) — the integer orbit residue the polynomial layer can't see.**
