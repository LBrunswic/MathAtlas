# Leverage R4: Squier / higher-dimensional rewriting homology — is a 3-cell ($H_2$ holonomy) forced?

**Promise:** medium. R4 reads the *real* Guiraud–Malbos paper (the modern, complete account of
Squier's finite-derivation-type theory and its $\infty$-dimensional / homological refinement) against
STRUCTURE.md §3/§5, and **decides the carried question**: are the syzygies (Plücker pair $+$
telescoping) the complete 2-cell set, or is a genuine **3-cell / $H_2$** (a holonomy obstruction beyond
C8 — the L1·5 signal) forced?

**Verdict (verified, 35/35 on the kernel): the 2-cells are COMPLETE — the resolution TERMINATES, there
is NO 3-cell, NO $H_2$ in the core layer. The structural program for the core layer is CLOSED.** The
candidate higher cells R3 flagged (telescoping, the $S$-row companion) are *extra 2-cells* (first-syzygy
generators), **not** 3-cells. The mechanism is sharp and citable: over the **two-variable** ring
$\mathbb{Q}[X,Y]$ the global dimension is $2$ (Hilbert's syzygy theorem), so $\operatorname{pd}(E_0)\le1$
and the **first-syzygy module of the cores is free** — there is nothing to relate at dimension $3$. This
is the honest null on the R4 prize (a genuine 3-cell), and a real structural result: it closes the
"is C8/the syzygy set complete?" thread opened in R1/R3.

**Status:** read in depth (§1 Squier overview, §2 polygraphic resolutions, §4 resolutions-from-
convergence + critical $n$-fold branchings, §5 abelianisation / Reidemeister–Fox–Squier complex,
Thm 5.6.5 + Thm 5.7.3); dictionary built; resolution of $E_0=I_2$ computed and the no-3-cell verdict
verified (`checks/lit_squier_rewriting.py`, exit 0). **Last iterated:** 2026-06-08.

**Source (real, complete; read in depth).**
- Y. Guiraud, P. Malbos, *Higher-dimensional normalisation strategies for acyclicity*, Adv. Math. **231**
  (2012) 2294–2351; arXiv:**1011.0558** —
  [`sources/guiraud-malbos-acyclicity-1011.0558.pdf`](../sources/guiraud-malbos-acyclicity-1011.0558.pdf).
  *(The task's stated id 1009.0381 is a different paper — Segev, group theory — so the correct
  Guiraud–Malbos id was located and downloaded.)*
- Companion theory cited throughout: C. Squier, *Word problems and a homological finiteness condition for
  monoids*, JPAA **49** (1987) (Fox-Jacobian resolution, left-FP$_3$); C. Squier, F. Otto, Y. Kobayashi,
  *A finiteness condition for rewriting systems* (1994) — **finite derivation type (FDT$_3$)**.

---

## 1. Dictionary — Squier / Guiraud–Malbos ↔ our core-layer rewriting

The paper's spine (their §1.1, §5.3): from a presentation $(\Sigma_1,\Sigma_2)$ of a monoid $\mathbf M$
one builds an exact sequence of free $\mathbf M$-modules, the **Reidemeister–Fox–Squier complex**
$$\cdots\to \mathbb Z\mathbf M[\Sigma_3]\xrightarrow{\;\delta_3\;}\mathbb Z\mathbf M[\Sigma_2]
  \xrightarrow{\;\delta_2\;}\mathbb Z\mathbf M[\Sigma_1]\xrightarrow{\;\delta_1\;}\mathbb Z\mathbf M
  \xrightarrow{\;\varepsilon\;}\mathbb Z\to0,$$
where $\delta_2$ is the **Fox Jacobian** $J(\alpha)=[u]-[v]$ on a relation $\alpha:u\Rightarrow v$
(§1.1.2 eq (1), §5.3), and $\delta[f^-]=-[f]$ (the inverse/reversal rule). **Squier's theorem**: when
$(\Sigma_1,\Sigma_2)$ is *convergent*, the **critical branchings** $\Sigma_3$ (minimal overlapping
applications of two relations on one word) form a generating set of $\ker\delta_2$ and extend the
sequence one step (eq (2)) $\Rightarrow$ left-FP$_3$; the homotopical refinement attaches one **3-cell**
per critical branching to make Squier's cellular complex contractible $\Rightarrow$ **FDT$_3$** (a finite
*homotopy basis* — "relations among relations finitely generated"). Guiraud–Malbos lift this to a
**polygraphic resolution** (§2, §4): an acyclic $(\infty,1)$-polygraph $\Sigma=(\Sigma_n)$ with
$\Sigma_{n+1}$ a homotopy basis in each dimension; from a convergent presentation, dimension $3$ =
critical branchings, dimension $4$ = **critical *triple* branchings** (minimal overlaps of three 2-cells),
etc. (Thm 4.5.3, FDT$_\infty$). Abelianising gives, in *natural systems*, a **free resolution of the
constant system $\mathbb Z$** (Thm 5.4.3), and the **homological 2-syzygies $\cong$ identities among
relations** (Thm 5.6.5); for a finitely presented category, **FP$_3\Leftrightarrow$ $h_2(\Sigma)$ f.g.
$\Leftrightarrow$ $\Pi(\Sigma)$ f.g. $\Leftrightarrow$ FDT$_{\mathrm{ab}}$** (Thm 5.7.3). The genuine
$H_2$ class (the 3-cell) is exactly a non-trivial *relation among relations* — Lemma 5.6.4: each element
of $h_2(\Sigma)$ is a closed 2-cell.

| Guiraud–Malbos / Squier | Our core layer |
|---|---|
| presentation $(\Sigma_1,\Sigma_2)$ of $\mathbf M$ | the **core ideal** $E_0=I_2$ over $R=\mathbb Q[X,Y]$ (R1) — the right object, see §2 |
| $0$-cell / base | the ring $R$ (resolving $R/E_0$, equiv. the relation module of $E_0$) |
| **1-cells $\Sigma_1$** (generators) | the **cores** $C(u,v)=\mathbf p(u)\wedge\mathbf p(v)=E_0$ generators |
| **$\delta_2=$ Fox Jacobian** $[u]-[v]$ | $C(u,v)=S(uv)-S(vu)$ — *literally a Fox-derivative value* ($S=\chi\circ\partial_{x_1}$, §1); the core **is** the abelianised boundary of the rotation relation $uv\!\sim\!vu$ |
| $\delta[f^-]=-[f]$ (inverse/reversal rule) | antisymmetry $C(u,v)=-C(v,u)$ = **reversal $=$ transpose** of the Magnus matrix |
| **2-cells $\Sigma_2$** (relations) $=\ker\delta_2$ generators | **first syzygies** of the cores: the **Plücker pair** ($D$-row C8 $+$ $S$-row companion) $+$ on the cycle stratum the **telescoping** $\sum_{\rm cyc}C=0$ (R3) |
| **critical branching $\Rightarrow$ 3-cell $\Sigma_3$** = relation-among-relations $=h_2=\operatorname{Tor}_2$ | **second syzygy** of the cores ($\operatorname{Syz}$ of the Plücker pair $+$ telescoping) — *the object Q2/Q3 ask about* |
| **critical *triple* branching $\Rightarrow$ 4-cell** (§4) | third syzygy / $\operatorname{Tor}_3$ |
| FDT$_3$ / FP$_3$ / FDT$_\infty$ (finiteness in each dim) | finiteness/termination of the free resolution of $E_0$ |

### Three mismatches that drive the verdict
1. **Monoid resolution vs commutative resolution.** Squier/GM resolve the *trivial module $\mathbb Z$ over
   the (noncommutative, possibly infinite) monoid ring $\mathbb Z\mathbf M$*; we resolve an *ideal $E_0$
   over the commutative $2$-variable ring $\mathbb Q[X,Y]$*. The structural transfer "critical
   branching $=$ 3-cell $=$ relation-among-relations $=$ 2nd syzygy $=H_2$" is exact, but the **finiteness
   mechanism differs**: in Squier-world FDT$_n$ is finiteness *in each dimension* of a possibly *infinite*
   tower; in our world **Hilbert's syzygy theorem caps the length at $\operatorname{gldim}\mathbb Q[X,Y]=2$.**
   This cap is *why* the question has a clean, decidable answer.
2. **The word monoid is FREE — vacuous Squier.** The binary monoid $W=\{x_0,x_1\}^\ast$ has
   $\Sigma_2=\varnothing$: trivially convergent, no critical branchings, FDT$_3$ holds vacuously, and its
   Fox-Jacobian resolution is the *trivial* two-term one. Word reduction is dead ($S$ injective per
   stratum, L1·3). **So all core-layer homology lives in the commutative layer, not the monoid layer** —
   the right object to feed Squier/GM is $E_0$, not $W$.
3. **No-inverse defect $=$ reversal=transpose, and it does NOT bite.** A monoid (not a group) is exactly
   where Squier's FDT can *fail* (a genuine $H_2$ with no finite homotopy basis) — but only when the
   monoid *has relations*. Ours is free, so the defect is invisible at the monoid layer; at the core
   layer the relevant homology is the commutative $\operatorname{Tor}^{\mathbb Q[X,Y]}$, capped at length
   $2$. The reversal/transpose involution is the $\delta[f^-]=-[f]$ **symmetry of the (free) syzygy
   module** — it organises the $D$-row/$S$-row pair, it does not create a 3-cell. (Honest scope: a
   *different* object — resolving $\mathbb Z$ over the cycle-quotient algebra $\mathbb Z[1/6][W]/\ker(\pi S)$
   — is again essentially commutative of Krull dim $\le2$, so it too cannot escape to a 3-cell. See §5.)
4. **Specialization kills the generic 3-cells.** Generic $2\times n$ minors resolve by **Eagon–Northcott**
   (length $n-1$): over the $2n$-variable ring there *are* genuine 3-cells (and higher) for $n\ge4$. Our
   cocycle specialization $a_i,b_i\mapsto D(w_i),S(w_i)\in\mathbb Q[X,Y]$ collapses the ambient ring to
   **two** variables, and with it the resolution to length $\le2$. (Control verified, §3.)

---

## 2. Q1 — our object as a polygraph (the core-ideal relation polygraph)

**Choice (justified).** The right object is the **core ideal $E_0=I_2$ over $R=\mathbb Q[X,Y]$**, *not*
the binary word monoid: the latter is free (mismatch 2 above), so its Squier complex is vacuous; the only
non-trivial "relations among relations" live in the commutative core layer. The polygraph is the
abelianised / Reidemeister–Fox–Squier one (GM §5.3), read as a free resolution:

- **dim 0:** the ring $R$ (we resolve $R/E_0$).
- **1-cells $\Sigma_1$ (generators):** the cores $C(u,v)$ — a minimal generating set of $E_0$.
- **2-cells $\Sigma_2$ (relations):** the **first syzygies** $\operatorname{Syz}(E_0)$:
  $$\textstyle\sum_{\rm cyc}D(w_i)C(w_j,w_k)=0\ \text{(C8, }D\text{-row)},\quad
    \sum_{\rm cyc}S(w_i)C(w_j,w_k)=0\ \text{($S$-row)},\quad
    \sum_{\rm cyc}C(w_i,w_j)=0\ \text{(telescoping, cycle stratum)}.$$
  These are the $\delta_2/$Fox-Jacobian relations among the cores. The reduction critical pair
  $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$ (STRUCTURE.md §3) is one such 2-cell, closing via
  C8.
- **3-cells $\Sigma_3$:** the **second syzygies** $\operatorname{Syz}\big(\operatorname{Syz}(E_0)\big)$ —
  relations among the Plücker pair $+$ telescoping $=h_2=\operatorname{Tor}_2^R(R/E_0)$. **The decisive
  question is whether $\Sigma_3=\varnothing$.**

---

## 3. Q2 — are the 2-cells complete, or is a 3-cell / $H_2$ forced? **Complete. No 3-cell.**

### 3a. The structural reason (Hilbert syzygy / gldim 2)
$R=\mathbb Q[X,Y]$ is a polynomial ring in **two** variables, so by Hilbert's syzygy theorem
$\operatorname{gldim}R=2$. Hence $\operatorname{pd}_R(R/E_0)\le2$, i.e. $\operatorname{pd}_R(E_0)\le1$:
the minimal free resolution of $E_0$ is
$$0\longrightarrow R^{\,b_2}\xrightarrow{\ \Psi\ } R^{\,b_1}\xrightarrow{\ [\text{cores}]\ } E_0\longrightarrow0,$$
with the **first-syzygy module $R^{b_2}$ FREE**. A minimal generating set of the first syzygies has **no
relations among it** — the second syzygy module is $0$. *There is no 3-cell, no $H_2$, no holonomy beyond
C8 at the relations-among-relations level.* Equivalently, for $R/E_0$ this is the **Hilbert–Burch**
resolution $0\to R^{b_1-1}\to R^{b_1}\to R\to R/E_0\to0$ (codim-2, Cohen–Macaulay; the cores are the
maximal minors of the $b_1\times(b_1-1)$ matrix $\Psi$), and $b_2=b_1-1$ with **no third term**.

### 3b. Verified on the kernel (`checks/lit_squier_rewriting.py`, 35/35, exit 0)
- **CONTROL (the detector works — PART B).** The 3-cell detector fires exactly when it should:
  Koszul ideal in $d$ variables has a genuine second syzygy (a 3-cell) **iff $d\ge3$** ($d{=}2$: none;
  $d{=}3$: present) — i.e. $\operatorname{gldim}=\#$variables. Generic $2\times n$ minors: $2\times3$
  ($6$ vars) → no 3-cell of the cores (Hilbert–Burch), $2\times4$ ($8$ vars) → **genuine 3-cell present**
  (Eagon–Northcott, codim $3$, $b_1{=}6,b_2{=}8$). So our computation *does* detect a 3-cell when one
  exists — the negative result on our matrix is real, not a tooling artefact.
- **DECISIVE (PART C).** For every cycle-stratum word (the Collatz-relevant locus) and distinct-word
  battery, the resolution of $E_0$ over $\mathbb Q[X,Y]$ terminates with **second syzygy $=$ none**
  (M1 free), Betti $(1,b_1,b_1-1)$, Hilbert–Burch $b_2=b_1-1$:

  | $w$ (cycle stratum) | $b_1$ (min gens) | $b_2$ (1st syz) | 2nd syz / 3-cell |
  |---|---|---|---|
  | $(1,2,3),(1,2,1),(1,1,2),(2,1,3),(3,1,2)$ | $2$ | $1$ | **none** |
  | $(2,1,1,3),(1,2,1,3)$ | $3$ | $2$ | **none** |

  (A nugget: for some distinct-word sets, e.g. $\{(1),(2),(12)\}$ and $\{(1),(2),(12),(211)\}$, $E_0$ is
  even **principal**, $b_1{=}1$.)
- **The candidate "higher cells" are 2-cells (PART D).** The telescoping vector $[\,1,-1,1\,]$, the
  $S$-row companion, and the $D$-row C8 **all lie in the first-syzygy module $M_1$** (a 2-cell each), and
  $M_1$ is **free of rank $b_1-1$**: none of them is a 3-cell. The R3 "extra cycle-stratum syzygies" are
  *additional generators of the free $M_1$* (more 2-cells / a richer FDT$_2$), **not** relations among
  the syzygies.

> **Verdict Q2.** The 2-cells (Plücker pair $+$ telescoping) are **COMPLETE**. The free resolution of
> $E_0=I_2$ over $\mathbb Q[X,Y]$ **terminates** at length $\le2$ ($\operatorname{pd}E_0\le1$): the
> first-syzygy module is free, **no second syzygy, no genuine 3-cell, no $H_2$ holonomy** in the core
> layer. The structural formalization of the core layer is **CLOSED**. (The prize — a genuine 3-cell —
> does not exist here, and the reason is sharp: only two variables $X,Y$.)

---

## 4. Q3 — the $S$-row second critical pair, and the no-inverse $H_2$

### 4a. Does the $S$-row Plücker companion close a *second* independent critical pair?
**Yes, as a second 2-cell — not a 3-cell.** R3 showed the generic first-syzygy module is the Plücker
**pair** (one row insufficient), so the $S$-row $\sum_{\rm cyc}S(u)C(v,w)=0$ is a genuine *independent*
first-syzygy generator distinct from the $D$-row C8. In rewriting terms it is a **second 2-cell**
(a second relation), and the reduction critical pair $\delta$ that closes via the $D$-row C8 has an
$S$-row analogue closing the parallel branching. Verified: $S$-row $\in M_1$ and is needed to generate
$M_1$ (PART A/D, and R3 PART B–C). Crucially this lives in **dimension 2**: it enlarges $\Sigma_2$, and
since $M_1$ is free there is still **no induced 3-cell**.

### 4b. Does the monoid no-inverse defect (reversal=transpose, the absent Fox inverse rule) force $H_2$?
**No.** The no-inverse defect is the locus where Squier's FDT can fail with a genuine $H_2$ — but *only
for a monoid that has relations*. Our binary monoid is **free** (mismatch 2), so its Squier complex is
vacuous and carries no homology; the core-layer homology is the **commutative**
$\operatorname{Tor}^{\mathbb Q[X,Y]}$, **capped at length $2$** by $\operatorname{gldim}=2$ (§3a). The
reversal $=$ transpose involution is precisely the $\delta[f^-]=-[f]$ rule (GM §5.3): a **symmetry of the
free first-syzygy module** (it swaps the $D$-row and $S$-row halves of the Plücker pair under transpose),
not a generator of a 3-cell. Verified: antisymmetry $C(u,v)+C(v,u)=0$ holds and $M_1$ is free (PARTS A,
C, D). **So neither the $S$-row nor the no-inverse defect forces an $H_2$.**

> **Verdict Q3.** The $S$-row is a genuine **second, independent 2-cell** (a second relation/critical
> pair), and the no-inverse / reversal=transpose defect is a **symmetry of the free syzygy module**.
> Neither produces a 3-cell: in the commutative two-variable core layer, $H_2=0$.

---

## 5. What is genuinely new (push past WHAT WE KNOW)

- **(structural, new — the R4 deliverable)** The cycle-stratum extra syzygies that R3 flagged as
  *candidate higher cells* are settled to be **extra 2-cells, not 3-cells**: the free resolution of
  $E_0=I_2$ over $\mathbb Q[X,Y]$ **terminates** ($\operatorname{pd}E_0\le1$, Hilbert–Burch
  $0\to R^{b_1-1}\to R^{b_1}\to R\to R/E_0\to0$), so the first-syzygy module is **free** and there is
  **no $H_2$/3-cell holonomy beyond C8** in the core layer. *The structural program for the core layer is
  CLOSED.* This is the sharp answer to the question STRUCTURE.md §5 left live.
- **(mechanism, new and citable)** The reason is the **two-variable cap**: $\operatorname{gldim}
  \mathbb Q[X,Y]=2$ (Hilbert syzygy). The very same determinantal object has genuine 3-cells generically
  (Eagon–Northcott over $2n$ variables); the cocycle specialization to $X,Y$ is exactly what kills them.
  So "more syzygies on the cycle stratum" (R3) does **not** mean "a 3-cell" — it means a *higher-rank free*
  $M_1$.
- **(dictionary, new and satisfying)** Our cocycle is *literally* the Squier differential: $\delta_2=$
  **Fox Jacobian** $[u]-[v]$ (GM §5.3) is, on the rotation relation $uv\sim vu$, exactly the core
  $C(u,v)=S(uv)-S(vu)$, and $S=\chi\circ\partial_{x_1}$ (§1) is a Fox-derivative value. The whole
  cocycle-combinatorics machine is one instance of the Reidemeister–Fox–Squier complex; the "identities
  among relations $=$ homological 2-syzygies" theorem (5.6.5) names our syzygy module.
- **(consolidation)** Combined with R1 (Fitting filtration terminates: no determinantal invariant finer
  than the cores) and R3 ($J$ collapses to the floor): the core layer is now understood **in all three
  homological directions** — Fitting (R1), first syzygies (R3), second/higher syzygies (R4, this) — and
  none yields a finer scalar handle. The obstruction set is *complete and finite*.

Not re-confirmed (R1/R3, already known): cores $=E_0=I_2=$ top Fitting ideal; the Plücker pair is the
generic first-syzygy generator (Lascoux/Eagon–Northcott); $S$ injective per stratum; $J=$ zero-sum ideal.

---

## 6. Verification — `checks/lit_squier_rewriting.py` (exit 0, 35/35)

- **PART A** — the Squier/Fox dictionary on our object: antisymmetry $C(u,v)+C(v,u)=0$ ($=\delta[f^-]=-[f]$,
  reversal=transpose); $D$-row C8 and $S$-row are genuine first syzygies (2-cells).
- **PART B** — *control*: the 3-cell detector fires iff a 3-cell exists — Koszul $d{=}2$ (none) vs $d{=}3$
  (present), $\operatorname{gldim}=\#$vars; generic $2\times3$ (no 3-cell, Hilbert–Burch) vs $2\times4$
  (**3-cell present**, Eagon–Northcott over $8$ vars). Validates the method.
- **PART C** — *decisive*: for every cycle-stratum and distinct-word battery, $\operatorname{Syz}(E_0)$ is
  **free** (second syzygy $=$ none), Betti $(1,b_1,b_1-1)$, Hilbert–Burch — **no 3-cell**.
- **PART D** — telescoping, $S$-row, $D$-row C8 all lie in the free $M_1$ (each a 2-cell), $M_1$ free of
  rank $b_1-1$ — the candidate higher cells are **not** 3-cells.
- **PART E** — headline: $\operatorname{pd}_R(E_0)\le1$, $\operatorname{pd}_R(R/E_0)\le2$ on all batteries
  (the gldim-2 cap); resolution terminates; 2-cells complete; core layer CLOSED.

Syzygy modules computed with sympy's `agca` over $\mathbb Q[X,Y]$; freeness certified by reducing to a
minimal generating set and checking its syzygy module is zero; controls validate both directions.

---

## 7. Open probes (feed R5 / L1·5 / the lever)

1. **Where can holonomy still live, if not the syzygy layer?** R4 kills the 3-cell in the *polynomial*
   relations-among-relations. The L1·5 holonomy, if real, must be in (a) the **rank-$\ge2$ enrichment**
   (R2: two coprime moduli making $\operatorname{gldim}\ge3$ — the only way a genuine 3-cell could
   reappear), or (b) the **arithmetic specialization at $(X,Y)=(2,3)$** (the integer $\operatorname{Tor}$,
   not the $\mathbb Q[X,Y]$ one). Which?
2. **Does the rank-$\ge2$ enrichment manufacture a 3-cell?** Over $\mathbb Q[X,Y,Z]$ (gldim 3) the same
   determinantal ideal *can* have a second syzygy. Is there an arithmetically meaningful third variable
   (a second prime/modulus) whose introduction makes $\operatorname{pd}(E_0)=2$ — a *real* holonomy
   obstruction? (Connects R2 and L1·5.)
3. **Hilbert–Burch matrix as the reduction engine.** The cores are the maximal minors of the explicit
   $b_1\times(b_1-1)$ syzygy matrix $\Psi$. Is $\Psi$ (its entries — degrees in $X,Y$) a *better*
   reduction handle than the cores themselves — e.g. does a small entry of $\Psi$ give an
   $o$-independent ceiling the cores miss?
4. **FDT$_{\mathrm{ab}}$ vs FDT$_3$ analogue.** GM Thm 5.7.3: FP$_3\Leftrightarrow$FDT$_{\mathrm{ab}}$ but
   (expected) FDT$_{\mathrm{ab}}\not\Rightarrow$FDT$_3$. Is there a *non-abelian* (genuinely homotopical,
   not homological) 3-cell obstruction in the **word/monoid** layer that the abelianised core-ideal
   resolution cannot see — i.e. does the full (non-abelian) Squier complex of the cycle-quotient *monoid*
   carry content the commutative $\operatorname{Tor}$ misses?

## Iteration log
- 2026-06-08 (R4, Gen 1): read Guiraud–Malbos arXiv:1011.0558 in depth (corrected the task's wrong id
  1009.0381). Built the Squier/Fox-Jacobian ↔ core-layer dictionary (cores $=\delta_2$ images; first
  syzygies $=$ 2-cells; second syzygies $=$ 3-cells $=h_2=\operatorname{Tor}_2$; Reidemeister–Fox–Squier
  complex; Thm 5.6.5/5.7.3). **Decided the carried question: 2-cells COMPLETE, NO 3-cell, NO $H_2$ in the
  core layer — resolution of $E_0=I_2$ over $\mathbb Q[X,Y]$ terminates (gldim $2$, Hilbert–Burch
  $b_2=b_1-1$).** Verified 35/35: control detector fires iff 3-cell exists (Koszul $d{=}2$ vs $3$; generic
  $2\times3$ vs $2\times4$); telescoping/$S$-row/C8 are 2-cells in the free $M_1$; $S$-row a second
  independent 2-cell; no-inverse defect a syzygy-module symmetry, not a 3-cell. Honest null on the
  3-cell prize; the structural-completeness result is the gain. Core layer CLOSED; holonomy (if any) is
  pushed to R2's rank-$\ge2$ enrichment or the integer specialization at $(2,3)$.
