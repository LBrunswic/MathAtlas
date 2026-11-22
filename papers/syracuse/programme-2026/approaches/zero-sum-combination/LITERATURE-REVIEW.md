# Literature Review: The Central Ideal Filtration and Cocycle Structure

*Approach `zero-sum-combination` (foundational). Compiled from a web literature sweep, June 2026. Companion to [`general-theory.md`](general-theory.md) (the $\mathbb{Z}/\mathbb{Z}[1/6]$ statement) and [`lattice-and-cocycles.md`](lattice-and-cocycles.md) (the first-pass synthesis). This document is the thorough version: the state of the literature, organized, with an annotated bibliography and a synthesis aimed at the `cocycle-combine` cocycle $S(w)$.*

## 0. Scope and why this review exists

The `zero-sum-combination` observation was: from a family $x_1,\dots,x_p$ one builds a **lattice of ideals** by replacing the $x_i$ with linear combinations; the difference step $x_i\mapsto x_i-x_j$ gives a "central sub-ideal," and **iterating** produces a descending filtration. Two questions follow, and this review surveys the literature answering each:

1. **The central ideal filtration.** What is the theory of this iterated-difference / "central" tower of ideals? (Answer: it *is* the **augmentation-ideal filtration** $I\supseteq I^2\supseteq\cdots$ of a group ring, equivalently the **dimension / lower-central (N-series)** theory; there is also a parallel **associative-algebra lower central series of ideals**.)
2. **Cocycle structure.** Does this filtration carry / capture cocycles? (Answer: emphatically yes — its degree-1 layer *is* the space of 1-cocycles via **Fox free differential calculus**, the relevant named object is the **Magnus cocycle/representation**, the cup product into degree 2 is a **determinant/wedge**, and the higher layers carry **Massey products**.)

Throughout, the target application is the word-cocycle of `cocycle-combine`: the transfer matrix $M(w)=\big(\begin{smallmatrix}Y^{o}&0\\ S(w)&X^{E}\end{smallmatrix}\big)$, whose off-diagonal $S(w)$ satisfies $S(uv)=S(u)Y^{o_v}+X^{E_u}S(v)$ and is valued in $\mathbb{Z}[X,Y]$ (or the Laurent ring $\mathbb{Z}[X^{\pm},Y^{\pm}]$, specializing to $\mathbb{Z}[1/6]$ at $(2,3)$).

---

## Part I — The central (augmentation) ideal filtration

### I.1 The augmentation ideal and its powers

For a group ring $RG$ the **augmentation map** $\varepsilon:RG\to R$, $\varepsilon(\sum r_g g)=\sum r_g$, has kernel the **augmentation ideal** $\Delta=\Delta(G)=I(G)$, a free $R$-module on $\{g-1:g\neq1\}$. Powers $\Delta^n$ give the **augmentation filtration** $RG\supseteq\Delta\supseteq\Delta^2\supseteq\cdots$, and the **associated graded ring** is $\mathrm{gr}(RG)=\bigoplus_n\Delta^n/\Delta^{n+1}$. The standard monograph is **Passi, _Group Rings and Their Augmentation Ideals_** (Springer LNM 715, 1979); see also **Karpilovsky** and **Sehgal, _Topics in Group Rings_**. The free-group case is **Gupta, _Free Group Rings_** (Contemp. Math. 66, 1987). ([nLab](https://ncatlab.org/nlab/show/augmentation+ideal); modern overview in [Mikhailov–Passi functors, arXiv:2309.07605](https://arxiv.org/pdf/2309.07605).)

### I.2 Augmentation quotients $Q_n(G)=\Delta^n/\Delta^{n+1}$: structure and periodicity

The graded pieces $Q_n(G)$ are a long-studied invariant.

- $Q_1(G)\cong G^{\mathrm{ab}}=G/G'$; for abelian $G$, **Passi**: $Q_2(G)\cong\mathrm{Sym}^2(G)$ (second symmetric power). The functors $G\mapsto RG/\Delta^{n+1}$ are the **Passi (polynomial) functors**, classifying polynomial maps of degree $\le n$. [arXiv:0707.0371](https://arxiv.org/pdf/0707.0371).
- **Bachmann–Grünenfelder (1974), "The periodicity in the graded ring associated with an integral group ring":** for **finite** $G$ the sequence $Q_n(G)$ is **eventually periodic** — $\exists N,k$ with $Q_n\cong Q_{n+k}$ for $n\ge N$. This is the central finiteness theorem of the subject.
- Explicit computations: **Losey** ($Q_2$), **Tahara**, **Hales**, **Parmenter**, and recent work on homocyclic abelian groups ([Science China Math.](https://link.springer.com/article/10.1007/s11425-007-0112-6)), nonabelian 2-groups ([Czech. Math. J.](https://link.springer.com/article/10.1007/s10587-012-0013-x)), Baumslag–Solitar groups ([Springer](https://link.springer.com/chapter/10.1007/978-3-030-52200-1_12)), and stable augmentation quotients ([Pacific J. Math.](https://projecteuclid.org/journals/pacific-journal-of-mathematics/volume-118/issue-2/Stable-augmentation-quotients-of-abelian-groups/pjm/1102706448.pdf)).

> **Relevance.** $Q_n$ is precisely "the new content at the $n$-th difference level." Any *a-priori* bound on the size of difference combinations of $S$ would come from controlling these quotients — see Part III.

### I.3 Dimension subgroups and the dimension subgroup problem

The filtration descends to the group via the **dimension subgroups**
$$
D_n(G)=G\cap(1+\Delta^n(G)),\qquad \gamma_n(G)\subseteq D_n(G),
$$
where $\gamma_n$ is the lower central series. The **dimension subgroup problem** asks when $D_n=\gamma_n$:

- **True for $n\le3$** over $\mathbb{Z}$ (all groups): $D_1=G$, $D_2=\gamma_2$, $D_3=\gamma_3$. **(Critical for us: the degrees we use — 1-cocycles and their brackets — sit safely in this clean range.)**
- **False in general:** **Rips (1972)** built a finite 2-group with $D_4\neq\gamma_4$ (order $2^{38}$); **Gupta** produced families for all $n\ge4$; **Sjögren** bounded the exponent of $D_n/\gamma_n$. An **odd-order** counterexample is recent ([arXiv:1803.09428](https://arxiv.org/pdf/1803.09428)). Surveys: **Gupta, "The dimension subgroup conjecture"** (Bull. LMS 22 (1990)); [the dimension subgroup problem (J. Algebra)](https://www.sciencedirect.com/science/article/pii/002186937290018X); [Resenhas IME-USP survey](https://revistas.usp.br/resenhasimeusp/en/article/download/75101/78665/101596).
- **Free groups are perfect:** **Magnus / Chen–Fox–Lyndon:** $\gamma_c(F)=D_c(F)=(\Delta^c+1)\cap F$ for all $c$ — the dimension and lower-central series coincide. This is the regime of Fox calculus (Part II).
- The modern functorial treatment is **Mikhailov–Passi, _Lower Central and Dimension Series of Groups_** (Springer LNM 1952, 2009), and **"Dimension quotients, Fox subgroups and limits of functors"** [arXiv:1703.08304](https://arxiv.org/pdf/1703.08304).

### I.4 N-series, Lazard's Lie ring, Jennings–Quillen

The abstract framework is **Lazard's N-series**: a filtration $G=\nu_1\supseteq\nu_2\supseteq\cdots$ with $[\nu_i,\nu_j]\subseteq\nu_{i+j}$. Taking graded pieces is a functor to **Lie rings**, $\mathrm{gr}(\nu)=\bigoplus\nu_i/\nu_{i+1}$ with bracket = group commutator (Jacobi from the **Hall–Witt identity**). Key theorems:

- **Jennings (1941) / Quillen (1968):** for the augmentation filtration of $kG$, $\mathrm{gr}(kG)\cong U(\mathrm{gr}\,G)$, the (restricted, in char $p$) **universal enveloping algebra** of the associated graded Lie algebra. (Quillen, "On the associated graded ring of a group ring," J. Algebra 10.)
- **Magnus:** for free $F$, $\mathrm{gr}(F)$ is the **free Lie algebra**, and $\mathrm{gr}(\mathbb{Z}F)$ is the free associative algebra (Magnus embedding into noncommutative power series).
- Modern extensions: **Habiro–Massuyeau, "extended N-series"** and generalized **Johnson homomorphisms** [arXiv:1707.07428](https://arxiv.org/pdf/1707.07428); the **Andreadakis problem** (does the Andreadakis filtration equal the lower central series of $\mathrm{IA}_n$?) [arXiv:1711.05991](https://arxiv.org/pdf/1711.05991), [arXiv:2006.04398](https://arxiv.org/pdf/2006.04398).

### I.5 The associative analogue: a lower central series **of ideals**

Closest to the user's literal "lattice of central ideals": for an associative algebra $A$, regard it as a Lie algebra under $[a,b]=ab-ba$, form the **Lie lower central series** $L_1=A,\ L_{k+1}=[A,L_k]$, and the **two-sided ideals** $M_k=AL_kA$. Then $A=M_1\supseteq M_2\supseteq M_3\supseteq\cdots$ is a genuine descending **central series of ideals**, with quotients $B_k=L_k/L_{k+1}$, $N_k=M_k/M_{k+1}$.

- **Feigin–Shoikhet (2007):** for the free algebra $A_n$ in char 0, $A_n/M_3\cong$ differential forms, and the $B_k$ ($k\ge2$) are finite-length modules over the Lie algebra $W_n$ of polynomial vector fields. [arXiv:0709.1905](https://arxiv.org/pdf/0709.1905).
- Extended by **Etingof, Kim, Ma, Bapat–Jordan, Arbesfeld–Jordan** and others (structure of $N_k$, char $p$ and over $\mathbb{Z}$): [arXiv:1508.00943](https://arxiv.org/pdf/1508.00943), [arXiv:1302.3992](https://arxiv.org/pdf/1302.3992), [MIT/RSI notes](https://math.mit.edu/documents/rsi/2012Cordwell.pdf).

> **Relevance.** Two distinct "central series of ideals" live in the picture: the **augmentation** one (commutative, what we mainly use) and the **commutator** one (noncommutative). The transfer-matrix algebra of `cocycle-combine` is genuinely noncommutative ($2\times2$ upper-triangular over $\mathbb{Z}[X,Y]$), so the $M_k$ theory is the right lens if commutators of transfer matrices ever enter.

### I.6 The $G=\mathbb{Z}$ instance: finite differences and integer-valued polynomials

For $G=\mathbb{Z}=\langle t\rangle$, $\mathbb{Z}G=\mathbb{Z}[t^{\pm}]$, $\Delta=(t-1)$, and the **forward-difference operator $\Delta f=f(t{+}1)-f(t)$ is multiplication by $(t-1)$**; the augmentation filtration is the $(t-1)$-adic filtration. Dually, **integer-valued polynomials** $\mathrm{Int}(\mathbb{Z})=\{f\in\mathbb{Q}[x]:f(\mathbb{Z})\subseteq\mathbb{Z}\}$ are free on the **binomial basis** $\binom{x}{k}$ (Pólya–Ostrowski), and a sequence is a degree-$\lt n$ polynomial iff its $n$-th finite difference vanishes. Reference: **Cahen–Chabert, _Integer-Valued Polynomials_** (AMS Surveys 48, 1997); **Bhargava's** generalized factorials / $p$-orderings; [Wikipedia: integer-valued polynomial](https://en.wikipedia.org/wiki/Integer-valued_polynomial); [finite-difference survey, arXiv:math/9502210](https://arxiv.org/pdf/math/9502210).

> **Relevance.** This is the *one-variable shadow* of our setting and the cleanest place to see "iterate the difference operator = climb the augmentation filtration." The $2$–$3$ arithmetic of Collatz replaces $\mathrm{Int}(\mathbb{Z})$ by the $\mathbb{Z}[1/6]$-flavored version.

---

## Part II — Cocycle structure on the filtration

### II.1 Fox free differential calculus

**Fox (1953–60, five _Annals_ papers)** built a differential calculus on the free group ring $\mathbb{Z}F$, $F=\langle x_1,\dots,x_n\rangle$. The **Fox derivatives** $\partial/\partial x_i:\mathbb{Z}F\to\mathbb{Z}F$ satisfy $\partial x_j/\partial x_i=\delta_{ij}$ and the product rule $\partial(uv)/\partial x_i=\partial u/\partial x_i\cdot\varepsilon(v)+u\cdot\partial v/\partial x_i$. The **fundamental formula** is
$$
w-1=\sum_{i=1}^n \frac{\partial w}{\partial x_i}\,(x_i-1)\qquad(w\in F),
$$
which exhibits the augmentation ideal $\Delta_F$ as a **free left $\mathbb{Z}F$-module on the differences $(x_i-1)$**. So "the ideal generated by differences" of Part I is, in the universal/free case, *free* with the Fox derivatives as coordinate functionals. Refs: [Fox derivative (Wikipedia)](https://en.wikipedia.org/wiki/Fox_derivative); Magnus–Karrass–Solitar, _Combinatorial Group Theory_.

### II.2 Derivations = crossed homomorphisms = 1-cocycles $=\mathrm{Hom}_{\mathbb{Z}G}(\Delta,M)$

A **derivation** $D:G\to M$ ($M$ a $G$-module) satisfies $D(uv)=D(u)+u\!\cdot\!D(v)$ — identically the **crossed-homomorphism / 1-cocycle** identity $c(gh)=c(g)+g\!\cdot\!c(h)$. The standard identifications:
$$
\mathrm{Der}(G,M)\;\cong\;Z^1(G,M)\;\cong\;\mathrm{Hom}_{\mathbb{Z}G}(\Delta,M),\qquad H^1(G,M)=\mathrm{Der}/\mathrm{PDer}=Z^1/B^1.
$$
**The first augmentation layer $\Delta=\Delta^1$ literally represents the 1-cocycle functor.** The Fox derivatives generate $\mathrm{Der}(F,\cdot)$ freely. A **principal** derivation (coboundary $B^1$) is $g\mapsto g\!\cdot\!m-m$. Refs: [crossed homomorphism (nLab)](https://ncatlab.org/nlab/show/crossed+homomorphism), [Encyclopedia of Math](https://encyclopediaofmath.org/wiki/Crossed_homomorphism).

### II.3 The Magnus cocycle / Magnus representation (Burau, Gassner) — the exact match

The **Magnus representation** packages Fox derivatives into a matrix and is **a crossed homomorphism (1-cocycle) valued in a Laurent polynomial ring** — the precise named object that `cocycle-combine`'s $S$ instantiates:

- Given a homomorphism $\phi:F\to \pi$ and a representation, $w\mapsto\big(\overline{\partial w/\partial x_j}\big)$ is a **Magnus cocycle**; it obeys the crossed-homomorphism identity (not a plain homomorphism — it is **anti**/twisted multiplicative).
- The **Burau representation** of the braid group and the **Gassner representation** of the pure braid group are the canonical special cases, valued in $\mathbb{Z}[t^{\pm}]$ and $\mathbb{Z}[t_1^{\pm},\dots,t_n^{\pm}]$ respectively. Their kernels sit inside the **lower central series** of free subgroups. Refs: [Gassner = Magnus cocycle, PRIMS 53 (2017)](https://ems.press/content/serial-article-files/41306); functorial Magnus rep over cobordisms [arXiv:1604.06905](https://arxiv.org/pdf/1604.06905); [Gassner image, arXiv:2204.12469](https://arxiv.org/pdf/2204.12469).

> **This is the headline match.** $S(w)$ valued in $\mathbb{Z}[X^{\pm},Y^{\pm}]$ as the off-diagonal of a triangular representation **is a Magnus-type 1-cocycle**. The Gassner/Burau toolbox (determinant of the Magnus matrix, the Alexander/Reidemeister invariant, reduced vs. unreduced, the lower-central-series kernel filtration) is directly importable.

### II.4 Cup products, the wedge/determinant, holonomy Lie algebras

The product of two 1-cocycles lands in $H^2$ via the **cup product** $H^1\times H^1\to H^2$, antisymmetrized to $H^1\wedge H^1\to H^2$. For commutator-relator groups this map is given by **explicit determinant formulas**, and its data assembles the **holonomy Lie algebra** = the quadratic approximation to $\mathrm{gr}(G)\otimes\mathbb{Q}$ (the associated graded Lie algebra of §I.4). Reference: **Suciu–Wang, "Cup products, lower central series, and holonomy Lie algebras"** [arXiv:1701.07768](https://arxiv.org/pdf/1701.07768).

> **This grounds the wedge core.** The `cocycle-combine` core $C(u,v)=\det\big(\begin{smallmatrix}D(u)&D(v)\\ S(u)&S(v)\end{smallmatrix}\big)$ is the **cup/wedge product of two 1-cocycles** (determinant form), and its **Plücker/Jacobi relation $\sum_{\mathrm{cyc}}D(u)C(v,w)=0$ is the Jacobi identity of the holonomy/associated-graded Lie algebra.** What `cocycle-structure` found by hand is the standard cup-product-into-$H^2$ structure.

### II.5 Higher cocycles: Massey products and the Zassenhaus filtration

Beyond cup products, the graded layers $\Delta^n/\Delta^{n+1}$ carry **Massey products** (higher cohomology operations) and are organized by the **Zassenhaus (lower $p$-central) filtration**:

- **Massey products and the lower central series of free groups** (Canad. J. Math.) — Massey products detect deeper LCS terms / refined linking. [Cambridge](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/massey-products-and-lower-central-series-of-free-groups/291C7ED73FAF27895E70B09BFBFA8942).
- **Zassenhaus filtration, Massey products, profinite groups** (Galois-theoretic; Mináč–Tân, Efrat) [arXiv:1301.0896](https://arxiv.org/pdf/1301.0896); generalized Bockstein = augmentation-graded Massey [arXiv:2004.11510](https://arxiv.org/pdf/2004.11510).

> **Relevance.** If a single difference $S^{(i)}-S^{(j)}$ (a 1-cocycle gap) ever needs a *second-order* refinement, the language is Massey products in the augmentation graded — the systematic theory of "what's left after the cup product."

### II.6 The Fox subgroup problem and functorial dimension quotients

A persistent hard strand: identify the **normal subgroup $F\cap(1+\mathfrak{a})$** cut out by a two-sided ideal $\mathfrak{a}\subseteq\mathbb{Z}F$ (e.g. $\mathfrak{a}=\mathfrak{f}^n\mathfrak{r}$ for a relation ideal $\mathfrak{r}$) — the **Fox subgroup problem**, with answers via Fox calculus and **limits of functors** (Mikhailov–Passi, Hartl). [arXiv:1703.08304](https://arxiv.org/pdf/1703.08304), [arXiv:1508.04400](https://arxiv.org/pdf/1508.04400), [arXiv:0707.0286](https://arxiv.org/pdf/0707.0286). Mostly orthogonal to our needs, but it is the technology for "which group elements does an ideal in the filtration detect," should that question arise for the word monoid.

---

## Part III — Synthesis for `cocycle-combine`

### III.1 The dictionary

| `cocycle-combine` object | Classical name | Reference |
|---|---|---|
| difference ideal $\langle x_i-x_j\rangle$, iterated | augmentation ideal $\Delta$ and its powers $\Delta^n$ | Passi LNM 715 |
| "central" sub-ideal, the tower | dimension / lower-central / **N-series** filtration | Lazard; Jennings–Quillen |
| $S(w)$, off-diagonal of $M(w)$ | **1-cocycle / Magnus cocycle** (crossed hom.) valued in $\mathbb{Z}[X^{\pm},Y^{\pm}]$ | Fox; Gassner/Burau |
| cocycle identity $S(uv)=S(u)Y^{o_v}+X^{E_u}S(v)$ | crossed-homomorphism identity | nLab |
| coboundary $w\mapsto cD(w)$ | 1-coboundary $B^1$; "$S$ mod $\langle D\rangle$" $=H^1$ | §II.2 |
| wedge core $C(u,v)=\det\big(\begin{smallmatrix}D&D\\ S&S\end{smallmatrix}\big)$ | **cup product** $H^1\wedge H^1\to H^2$ (determinant form) | Suciu–Wang |
| Plücker relation $\sum_{\mathrm{cyc}}DC=0$ | **Jacobi identity** of the holonomy Lie algebra | §I.4, II.4 |
| evaluate $(X,Y)=(2,3)$ into $\mathbb{Z}[1/6]$ (a PID) | specialization of the Laurent-ring Magnus cocycle | [`general-theory.md`](general-theory.md) |
| rotation sums $S^{(j)}$, gcd of differences | the difference filtration at one cyclic word | §I.1, I.6 |

**Conclusion of the survey's central question:** the central-ideal filtration does not merely *touch* cocycles — **its degree-1 layer is the 1-cocycle functor, its cup product is the wedge core, and its graded Lie algebra carries the Jacobi relation already observed.** The `cocycle-combine` algebra is a concrete Magnus-cocycle computation.

### III.2 Where leverage might (and might not) come from

**Promising:**
- **Gassner/Burau toolbox (§II.3).** These are *the* worked examples of Laurent-ring Magnus cocycles. Their structural results — determinant of the Magnus matrix, the reduced cocycle, kernels inside the lower central series — are the closest off-the-shelf analogues for bounding/normalizing $S$. **Highest-value next read.**
- **Augmentation-quotient bounds (§I.2).** Bachmann–Grünenfelder periodicity and the explicit $Q_n$ computations bound "the new content at level $n$." If $\varphi(\gcd_{i,j}(S^{(i)}-S^{(j)}))$ (the $\mathbb{Z}[1/6]$ generator) can be read as living in a specific $Q_n$, periodicity could give an *a-priori* ceiling — the bridge to the `cycle-gcd` bound. Speculative but concrete.
- **Cup-product/holonomy (§II.4).** Reframing $C(u,v)$ as a cup product means the **whole compensation search is a computation in $H^2$ / the holonomy Lie algebra**; identities there (e.g. the determinant formula) may generate new $q$-/multiplicity-free cores beyond P0/P2.

**Cautionary:**
- **The dimension subgroup problem fails at $n\ge4$ (§I.3).** Any argument that silently assumes "augmentation level = commutator level" breaks past degree 3. *But* the cocycle content we use is degree 1 (the cocycle) and degree 2 (the cup product/wedge core), where $D_2=\gamma_2$, $D_3=\gamma_3$ hold unconditionally — so **our regime is in the safe range.** Worth stating explicitly so we never lean on a degree-$\ge4$ coincidence.
- **Two different "central series of ideals" (§I.5 vs I.2).** The transfer-matrix algebra is noncommutative; don't conflate the commutative augmentation filtration with the commutator filtration $M_k$. Our $S$-cocycle lives in the former.

### III.3 Concrete next reads (priority order)

1. **Gassner/Burau as Magnus cocycles** — Birman, _Braids, Links, and Mapping Class Groups_; [PRIMS 53 (2017)](https://ems.press/content/serial-article-files/41306); [arXiv:1604.06905](https://arxiv.org/pdf/1604.06905). *Goal: import a normalization/size result for the Magnus matrix.*
2. **Passi, _Group Rings and Their Augmentation Ideals_ (LNM 715)** + **Bachmann–Grünenfelder (1974)**. *Goal: turn $Q_n$ periodicity into a candidate a-priori bound.*
3. **Suciu–Wang, holonomy Lie algebras** [arXiv:1701.07768](https://arxiv.org/pdf/1701.07768). *Goal: the determinant cup-product formula as a core-generating identity.*
4. **Mikhailov–Passi, _Lower Central and Dimension Series of Groups_ (LNM 1952)** for the modern functorial synthesis.

---

## Annotated bibliography

**Books / monographs**
- I. B. S. Passi, *Group Rings and Their Augmentation Ideals*, Springer LNM 715 (1979). The canonical reference for $\Delta^n$, $Q_n$, polynomial functors. [Google Books](https://books.google.com/books/about/Group_Rings_and_Their_Augmentation_Ideal.html?id=FL0ZAQAAIAAJ).
- R. Mikhailov & I. B. S. Passi, *Lower Central and Dimension Series of Groups*, Springer LNM 1952 (2009). Modern functorial synthesis of dimension/Fox/lower-central theory.
- N. Gupta, *Free Group Rings*, Contemp. Math. 66 (1987). Free-group augmentation ideals, dimension subgroup counterexamples.
- P.-J. Cahen & J.-L. Chabert, *Integer-Valued Polynomials*, AMS Math. Surveys 48 (1997). The $G=\mathbb{Z}$ / finite-difference shadow.
- W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory* (1966). Fox calculus, Magnus embedding.
- J. Birman, *Braids, Links, and Mapping Class Groups* (1974). Burau/Gassner = Magnus representations.

**Foundational papers**
- R. H. Fox, *Free differential calculus I–V*, Annals of Math. (1953–1960). Fox derivatives; fundamental formula; $\Delta_F$ free on $(x_i-1)$.
- D. Quillen, *On the associated graded ring of a group ring*, J. Algebra 10 (1968). $\mathrm{gr}(kG)\cong U(\mathrm{gr}\,G)$.
- S. A. Jennings (1941); M. Lazard (1954, N-series & Lie rings). Associated graded Lie algebra of the augmentation/dimension filtration.
- E. Rips, *On the fourth integer dimension subgroup*, Israel J. Math. 12 (1972). $D_4\neq\gamma_4$. [Springer](https://link.springer.com/article/10.1007/BF02764625).
- O. Bachmann & L. Grünenfelder, *The periodicity in the graded ring associated with an integral group ring*, J. Pure Appl. Algebra (1974). Eventual periodicity of $Q_n(G)$ for finite $G$.

**Surveys / problem articles**
- N. Gupta, *The dimension subgroup conjecture*, Bull. LMS 22 (1990). [Wiley](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/blms/22.5.453).
- *The dimension subgroup problem*, J. Algebra. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/002186937290018X).
- Mikhailov–Passi & co., *Dimension quotients, Fox subgroups and limits of functors* [arXiv:1703.08304](https://arxiv.org/pdf/1703.08304); *On the Passi and Mal'cev functors* [arXiv:2309.07605](https://arxiv.org/pdf/2309.07605).

**Cocycle / cup-product / Magnus strand**
- crossed homomorphisms = 1-cocycles: [nLab](https://ncatlab.org/nlab/show/crossed+homomorphism), [Encyclopedia of Math](https://encyclopediaofmath.org/wiki/Crossed_homomorphism), [Wagemann LA-cohomology notes](https://www.math.sciences.univ-nantes.fr/~wagemann/LAlecture.pdf).
- Magnus cocycle / representation: [PRIMS 53 (2017)](https://ems.press/content/serial-article-files/41306), [arXiv:1604.06905](https://arxiv.org/pdf/1604.06905), [arXiv:2204.12469](https://arxiv.org/pdf/2204.12469).
- Cup products & holonomy Lie algebras: Suciu–Wang [arXiv:1701.07768](https://arxiv.org/pdf/1701.07768).
- Massey products / Zassenhaus: [Canad. J. Math.](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/massey-products-and-lower-central-series-of-free-groups/291C7ED73FAF27895E70B09BFBFA8942), [arXiv:1301.0896](https://arxiv.org/pdf/1301.0896), [arXiv:2004.11510](https://arxiv.org/pdf/2004.11510).

**Associative-algebra central series of ideals**
- Feigin–Shoikhet [arXiv:0709.1905](https://arxiv.org/pdf/0709.1905); Etingof et al. [arXiv:1508.00943](https://arxiv.org/pdf/1508.00943), [arXiv:1302.3992](https://arxiv.org/pdf/1302.3992).

**Value-side (toric / lattice ideals), from [`general-theory.md`](general-theory.md)**
- Eisenbud–Sturmfels, *Binomial Ideals* [arXiv:alg-geom/9401001](https://arxiv.org/pdf/alg-geom/9401001).

---

*Caveats: a few attributions (Losey/Tahara/Hales on $Q_2$; exact statements of Jennings 1941 and Lazard 1954) are cited from secondary sources and standard knowledge — verify against the primary texts before relying on a precise constant. The dimension-subgroup failure at $n\ge4$ is firmly established; our usage stays in degrees $\le2$ where the theory is unconditional.*
