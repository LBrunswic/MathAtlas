# Structure & Objective — the binary cocycle, the $\chi$-augmentation, the Plücker module

*Living formalization note for `cocycle-combinatorics`. Rewritten 2026-06-08 around the sharper facts
$S=\chi\circ\partial_{\mathrm{odd}}$ (binary words) and "word reduction $=$ mod $\ker(1-\chi)$".
This note is **iterated**: each literature pass (`--leverage`) reads ONE paper and updates it.
Roadmap of passes: [`LEVERAGE-ROADMAP-L1.md`](LEVERAGE-ROADMAP-L1.md); queue: [`THREADS.md`](THREADS.md).*

---

## 0. Objective (rewritten)

**Formalize the Syracuse cocycle as a twisted Fox derivative on the binary step-alphabet, and use the
literature on that exact structure — twisted/relative augmentation ideals, the Magnus/Alexander
module, the Plücker (bracket) algebra — to CONSTRUCT, for as many word-families as possible, a small
*representative* of the rotation ideal $\langle w_0,\dots,w_p\rangle$ ($w_j$ the cyclic shifts): an element
with a *small word representation*, hence a small ceiling $G=|2^E-3^o|\le|C|$.**

> **DIRECTION — we find representatives, NOT obstructions (read before prompting any leverage).**
> The exclusion is a *squeeze*: our small upper bound $G\le|C|$ (constructive) against Matveev/Ellison's
> *lower* bound on $G$ (their job — the obstruction/growth). **Do NOT prompt agents to prove a no-go, to show
> $\operatorname{sixfree}\to\infty$, or to ask "is C8 the complete obstruction set / is there a 3-cell."**
> Every leverage must ask: *does this structure let us CONSTRUCT a smaller representative, or extend the
> family for which one exists?* (R3/R4 drifted into obstruction-framing — corrected here.)
>
> **Refinement (2026-06-09 — the integer cyclic quotient, expansion-reduction).** The representative is built
> by an **expansion-reduction** strategy starting from the **cyclic roll** (rotation orbit) of $w$ inside
> $A=\mathbb{Z}[W]/\ker(\pi\circ S)$, where $\pi$ is the **integer/eval** projection
> $\mathbb{Z}[1/6]\twoheadrightarrow\mathbb{Z}[1/6]/(\chi(w)-1)\cong\mathbb{Z}/G\mathbb{Z}$ — *not* the
> polynomial reduction mod $\langle D\rangle\subset\mathbb{Z}[X,Y]$. *Expand* (powers, rolled-block insertion,
> orbit concatenation), then *reduce* to a small nonzero residue mod $G$ (the working [P3] lever is exactly
> this). **Caveat the closures don't cover:** L1·3/R3/R4 closed the *polynomial* relation module over
> $\mathbb{Q}[X,Y]$; the lever lives in the **integer cyclic quotient $A$**, which Hilbert–Burch does not
> touch. So "no length-reducing rule" (L1·3) and "no 3-cell" (R4) are *not* no-gos for expansion-reduction.

Concretely, the structure to formalize and mine is the triple:

1. **The cocycle is one twisted Fox derivative.** On the free monoid $W=\{0,1\}^\ast$ (0 = even/halving
   step, 1 = odd step), $S=\chi\circ\partial_{\mathrm{odd}}$ up to a $\mathbb{Z}[1/6]$-unit
   (§1). The Magnus matrix $\Phi$ packages it; $\det\Phi$ is a unit (L1·1); $S$ pins the word per
   stratum (injective, L1·3).
2. **Reduction lives in the $\chi$-augmentation quotient.** The relation $\sim$ is the congruence on
   $\mathbb{Z}[1/6][W]$ defined by $\ker(\pi\circ S)$, $\pi:\mathbb{Z}[1/6]\twoheadrightarrow
   \mathbb{Z}[1/6]/(1-\chi(w))$ (§2). Since $1-\chi(w)=-D/3^o$ generates $\langle D\rangle$, this is the
   **cycle-ideal**, and $(1-\chi)$ is the **augmentation ideal of the character $\chi$**. Word-level
   reduction is dead (injectivity); the real relations are the **cores**.
3. **The cores form the Plücker module.** Each word is a state vector $\mathbf p(w)=(D(w),S(w))\in R^2$;
   cores $C(u,v)=\mathbf p(u)\wedge\mathbf p(v)$ are the $2\times2$ minors; rank-2 forces the
   Grassmann–Plücker syzygy C8. The reduction calculus is arithmetic in this module (§3).

**Why it can work:** $\chi$-augmentation + Alexander-module theory is a mature body that controls
exactly "which combinations of words die mod $(1-\chi)$" — the membership problem for $\mathcal I_D$.
The bet is that it yields *new* membership certificates (small cores from small words) beyond the
hand-found P0–P4, or pins the obstruction (Plücker rank-2 / C8) as complete.

**What would count as progress:** a literature-imported relation, verified on the kernel, that either
(a) produces a word-family with an $o$-independent small core not in the current atlas, or (b) proves
the core module is finitely generated / bounded in a way that closes the $\ge2$-growing-gap no-go.

---

## 1. The binary cocycle $S=\chi\circ\partial_{\mathrm{odd}}$  *(verified)*

Free monoid $W=\{x_0,x_1\}^\ast$, $x_0=$ even step, $x_1=$ odd step. The **Magnus representation**
$$\Phi(x_0)=\begin{pmatrix}X&0\\0&1\end{pmatrix},\qquad
  \Phi(x_1)=\begin{pmatrix}1&1\\0&Y\end{pmatrix},\qquad
  \Phi(w)=\begin{pmatrix}X^{E}&S(w)\\0&Y^{o}\end{pmatrix}$$
($E=\#0=$ even steps $=|w|$, $o=\#1=$ odd steps $=\operatorname{len}$). The off-diagonal is the
**Fox derivative w.r.t. the odd letter, evaluated by the character**:
$$\boxed{\,S(w)=Y^{o-1}\,\chi\!\big(\partial w/\partial x_1\big)\ \sim\ \chi\circ\partial_{\mathrm{odd}}\,}
\qquad \chi(x_0)=X(=2),\ \chi(x_1)=Y^{-1}(=\tfrac13),$$
where $\partial w/\partial x_1=\sum_{p:\,b_p=1}b_{1}\cdots b_{p-1}$ (sum of prefixes ending before each
odd step) and $\chi(\text{prefix with }a\text{ zeros},\ c\text{ ones})=X^{a}Y^{-c}$. Equivalently
$S(w)=\sum_{p:\,b_p=1}X^{\#0\text{ before}}\,Y^{\#1\text{ after}}$.
**Verified** (gap↔binary $1\,0^{d_0}1\,0^{d_1}\cdots$): $S_{\text{kernel}}=\Phi_{12}=\chi(\partial_{\mathrm{odd}})$
on all test words; the $Y{=}1$ slice is the pure Fox prefix $\alpha_X(\partial_{\mathrm{odd}})$.

> **Why binary, not the gap alphabet.** The gap-alphabet (L1·2) needed an *infinite* generating set and a
> *sum over $d$* of derivatives; the binary alphabet needs **two** generators and **one** derivative
> $\partial_{\mathrm{odd}}$. The infinite gap alphabet is just $x_1x_0^{d}$ super-letters (run-length
> encoding); the binary form is the irreducible one and is where the literature ($\partial$ of a 2-letter
> word, Alexander modules) is stated.

The character itself is the ratio of the two diagonal characters: $\chi=\alpha_X/\varepsilon_Y$
($\alpha_X:x_0\mapsto X,x_1\mapsto1$; $\varepsilon_Y:x_0\mapsto1,x_1\mapsto Y$), so
$1-\chi(w)=1-X^{E}/Y^{o}=-D/Y^{o}$, $D=X^E-Y^o$.

---

## 2. Reduction $=$ the $\chi$-augmentation quotient  *(verified)*

Extend $S$ linearly to $\mathbb{Z}[1/6][W]$. The reduction relation is the congruence of
$$\mathbb{Z}[1/6][W]\ \big/\ \ker(\pi\circ S),\qquad
  \pi:\mathbb{Z}[1/6]\twoheadrightarrow \mathbb{Z}[1/6]/(1-\chi(w))\,\mathbb{Z}[1/6].$$
- **$(1-\chi(w))=-D/3^o$**, $3^o\in\mathbb{Z}[1/6]^\times$, so $\langle1-\chi(w)\rangle=\langle D\rangle$:
  $\pi$ is reduction mod the **cycle-ideal**, and $\pi\circ S=\bar S$. $\mathcal I_D=\ker\bar S$.
- **$(1-\chi)$ is the augmentation ideal of the character $\chi$** — the twisted (character) analogue of
  the classical augmentation $\ker\varepsilon$. "$w$ is a cycle" $\iff\chi(w)\equiv1$ in the quotient
  ($2^E\equiv3^o\!\!\pmod D$) — *trivialize the character*. This is exactly an **Alexander-module-type**
  object: $\mathcal I_D=\ker S$ read into the $\chi$-twisted quotient.
- **Why $\mathbb{Z}[1/6]$:** solely to make $\chi$ a *unit* character so $(1-\chi)$ is a clean ideal and the
  $Y^{o-1}$ in §1 is invisible.
- **No word shortening (L1·3):** $S$ is injective per stratum ($\Phi$ faithful), so $\ker S$ on
  same-stratum words (rotations) is trivial; the *only* relations appear after $\pi$ — i.e. in
  $\ker(\pi\circ S)=\mathcal I_D$, generated by the cores. Reduction is reformulated from "shorten a word"
  to "a small **combination** of words lies in $\langle D\rangle$".

**The named module (R1, verified — Crowell's derived module).** $\mathcal I_D$ sits inside the
**2-variable character-augmentation (Crowell) module** $\mathscr A_\psi$ of the abelianization
$\psi:W\to H=\langle X,Y\rangle\cong\mathbb{Z}^2$ ($t_1=X,t_2=Y$). The full presentation needs **both** Fox
derivatives: alongside $S=\chi\circ\partial_{x_1}$ there is a **second cocycle**
$$T:=\chi\circ\partial_{x_0}\ (\text{the even-letter derivative}),\qquad
  \boxed{\,D=(X-1)\,T-(Y-1)\,S\,}$$
— the **binary Fox fundamental formula** (the exact Crowell presentation, atoms $X-1,Y-1$), with $D$ the
augmentation value $\theta(dw)=\chi(w)-1$. Key consequences (all kernel-verified):
- **$\langle D\rangle$ is NOT the order ideal** (over $\mathbb{Z}[X,Y]$): $\langle D\rangle\subsetneq
  E_1=\langle T,S\rangle$. The Alexander polynomial $\Delta_1=\gcd(T,S)$ is **$1$ for primitive shapes** and
  the **period factor** $(X^{|w|}-Y^{o})/(X^{|u|}-Y^{o_u})$ for imprimitive $w=u^k$ — i.e. $\Delta_1$ detects
  *only the period* (e.g. $w=(2,1)^2$: $\Delta_1=X^3+Y^2\mid D=X^6-Y^4$). $\langle D\rangle$ is the
  *augmentation value / rank-1 homology order*, recovered as $E_1=\langle D\rangle=\langle G\rangle$ only after
  evaluating the **rotation family** at $(2,3)$.

---

## 3. The cores $=$ the Plücker module  *(verified)*

State vector $\mathbf p(w)=(D(w),S(w))\in R^2$. Core $C(u,v)=\det[\mathbf p(u)\,|\,\mathbf p(v)]
=D(u)S(v)-D(v)S(u)=\mathbf p(u)\wedge\mathbf p(v)$ (signed area; $=0\iff$ same fixed point $S/D$).
Any three state vectors are dependent — with the cores as coefficients:
$C(v,w)\mathbf p(u)+C(w,u)\mathbf p(v)+C(u,v)\mathbf p(w)=0$. Its **two rows** are the **Plücker pair**
(R3 — generic first-syzygy generators, Eagon–Northcott/Lascoux): the $D$-row **C8**
$D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0$ **and** the $S$-row companion
$S(u)C(v,w)+S(v)C(w,u)+S(w)C(u,v)=0$ (Koszul redundant). The **Plücker module** $=\Lambda^2$ of the rank-2
state module $=$ the ideal of $2\times2$ minors $E_0=I_2$, with relations antisymmetry $+$ the Plücker pair.
On a cycle $G=|D|$ divides every core; the mod-$D$ relations *are* the cores (L1·3). The reduction critical
pair $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$ lives here, closing via C8.

**The cores are the top Fitting ideal (R1, verified).** $C(u,v)=E_0=I_2$, the $2\times2$-minor (Fitting-0)
ideal of the state/Alexander matrix; C8 is its Grassmann–Plücker syzygy. Because the state matrix has only
**two columns**, the Fitting filtration **terminates at the cores** ($I_3=0$): *there is no determinantal
invariant finer than the cores* — they are the complete handle. (So no higher elementary ideal gives a new
scalar exclusion bound — see §5.) The one new sub-object R1 exposes: the core ideal factors
$E_0=\langle D\rangle\cdot J$ with **difference ideal** $J=\langle S^{(i)}-S^{(j)}\rangle$.

**R3 (verified): C8 is incomplete on the cycle stratum; $J$ collapses to the floor.**
- *Syzygies:* generically the Plücker **pair** generates (above); on the **cycle stratum** (rotations share
  the constant $D$-row) C8 becomes **non-minimal** — $\text{C8}=D\cdot(\text{telescoping})$ where
  $\sum_{\rm cyc}C(w_i,w_j)=0$ is a **constant-coefficient telescoping** syzygy (degree drop $\deg D\to0$),
  *not* in $\langle\text{Plücker pair, Koszul}\rangle$. So the specialized cores carry **strictly more**
  syzygies than the generic Grassmannian — the candidate higher cells for R4 (Squier).
- *The difference ideal $J$ is the zero-sum / augmentation ideal* of `approaches/zero-sum-combination`
  (confirmed): principal over $\mathbb{Z}[1/6]$, generator $=\varphi(\gcd_{i,j}(S^{(i)}-S^{(j)}))=\Delta$.
  It **collapses**: $\Delta$ is finer than any single difference, but $G\mid\Delta$, so on a cycle
  $\operatorname{sixfree}(\Delta)\ge G=|D|$ — *no finer $o$-independent ceiling*. The genuinely small
  $o$-independent object, the **polynomial gcd $X^a(X-1)$** (the bounded-defect lever's monomial core),
  divides every difference but — $\mathbb{Z}[X,Y]$ being a **non-PID** — is **not a member** of $J$, hence
  not a realizable zero-sum core. **$J$ is the ideal-theoretic *home* of the rotation-combo floor /
  bounded-defect lever / zero-sum ideal (one object), not a new lever.**

**R4 (verified): the core layer is homologically CLOSED — no 3-cell.** The Squier/Guiraud–Malbos
polygraphic resolution identifies 3-cells with *second* syzygies ($\operatorname{Tor}_2$ / $H_2$). But over
$R=\mathbb{Q}[X,Y]$, Hilbert's syzygy theorem gives $\operatorname{gldim}R=2$, so $\operatorname{pd}_R(E_0)\le1$:
the first-syzygy module of the cores is **free** (Hilbert–Burch, $0\to R^{b-1}\to R^{b}\to R\to R/E_0\to0$).
Hence **the 2-cells (Plücker pair + telescoping) are COMPLETE — there is no $H_2$ holonomy beyond C8**, and
the R3 "candidate higher cells" are extra **2-cells in the free $M_1$**, not 3-cells. (Detector validated
both ways: Koszul $d{=}3$ and generic $2\times4$ minors *do* show a 3-cell; our specialization does not.)
The cores are the **complete** handle in all three homological directions — Fitting (R1), first syzygies
(R3), higher syzygies (R4). A genuine 3-cell could appear only off this ring: a **rank-$\ge2$ enrichment**
(a third modulus → $\operatorname{gldim}\ge3$, R2) or the **integer specialization at $(2,3)$** (Layer-2).

**L1·5 (verified, Movement III — cup products / weight): the cup product is the *linearization* of the core,
and *weight* is why the lever is $o$-independent.** Suciu–Wang's cup product, translated, is precisely the
**$\partial_X$-linearization of our core at the trivial character**:
$$\partial_X C(u,v)\big\rvert_{X=Y=1}=E_u o_v-o_u E_v=\langle u\rangle\cup\langle v\rangle,\qquad
  C\big\rvert_{X=Y=1}=0,\quad \partial_Y C\big\rvert_{X=Y=1}=0,$$
with single-word primitive $A(w)=\varepsilon_{01}(w)-\varepsilon_{10}(w)$ (crossing number) whose coboundary
$A(uv)-A(u)-A(v)$ *is* the linearized core. So the cup product is the **rank-1 shadow** of $C$ — the
exclusion content is the higher-order $\chi$-twist, off the (trivial-character) cup-product setting; **no new
constructive lever** (the holonomy quadratic relation is the Jacobi $=$ weight-2 shadow of C8). The genuine
import is the **weight / Chen-rank grading** (Labute; LCS ranks depend on *combinatorial degree*, not word
length): the bounded-defect lever core $C(\beta,d)$ is a **fixed weight-2** cup product $[\beta]\cup[d]$,
literally $L$-independent under the sliding background run, and the weight-2 bracket is **unique**
($\dim\operatorname{lie}_2(y_0,y_1)=1$, Witt) — so the whole bounded-arc ceiling atlas is *one* structural
element. This names the structural source of [P3]'s $o$-independence and restates the open $\ge2$-growing-gap
no-go as **"the trapped configuration has unbounded Magnus weight $\omega\to\infty$"** (a Chen-rank-growth
statement; the residual $(2,3)$-arithmetic is unchanged). Suggested object: the **$\chi$-deformation / weight
tower** $\partial_X^k C\rvert_{1,1}/k!$ (weight 1 $=$ cup product; higher weights $=$ the exclusion-carrying
twist) — is $\operatorname{sixfree}$ determined by a *bounded* number of weight slices (finite-weight
exclusion)? That is the L1·6 prize.

**L1·9 (verified, Movement IV — the integer circulant): the orbit-residue floor is $G^o$, the integer avatar of
the $J$-collapse.** The rotation orbit is a cyclic $\mathbb{Z}[\mathbb{Z}/o]$-module; its **circulant determinant
is a resultant** (Silver–Williams' $r_m$, R-SW2):
$$\det\operatorname{circ}(S^{(0)},\dots,S^{(o-1)})=\operatorname{Res}(t^o-1,\widehat S)=\prod_{\zeta^o=1}\widehat S(\zeta),
  \qquad \widehat S(t)=\textstyle\sum_jS^{(j)}t^j.$$
Because $G\mid S^{(j)}$ for all $j$, $G$ survives in **every** DFT/Fourier component, so $\det\operatorname{circ}(S)=
G^{o}\det\operatorname{circ}(m)$ and every cyclotomic block $\operatorname{Res}(\Phi_d,\widehat S)\ge G^{\varphi(d)}$
(R-SW4): the **integer circulant amplifies the floor to $G^o$ — it never constructs a smaller orbit residue.**
This is the *integer-quotient* avatar of R3's (polynomial/ideal) $J$-collapse, now sharp. The **period** structure
is a Fox/cyclic-cover formula (R-SW3): $G(w^r)=\operatorname{Res}(t^r-1,\,X^E-Y^o t)=\prod_{d\mid r}\Phi_d^{*}(2^E,3^o)$,
identifying STRUCTURE §2's period factor $\Delta_1$ as the cyclic-cover cofactor and handing the $\Phi_d^{*}(2^E,3^o)$
blocks to the Layer-2 Bang–Zsygmondy program. **Why no construction is possible here:** the cycle Alexander polynomial
$\Delta=X^E-Y^o t$ is **degree-1 and never cyclotomic** ($2^E\ne3^o$), so $M(\Delta)=\max(2^E,3^o)\gt1$ ⇒ (Gordon) the
orbit residue grows, never periodic — Silver–Williams Mahler growth **is** our Layer-2 obstruction. A small residue
would need a *cyclotomic* $\Delta$, i.e. a **higher-degree** cycle polynomial — only door **R2** (rank-$\ge2$) can
supply one. (Transfer law R-SW1: $X^{d_j}S(w_{j+1})=Y\,S(w_j)+D$.)

**R2 pivot (verified, McMullen 2002 — the Alexander norm): one geometric law retires the R1 and L1·9 nulls.**
McMullen's theorem identifies the **Alexander norm with the width of the Newton polytope** of the Alexander
polynomial, $\lVert\phi\rVert_A=\operatorname{width}_\phi N(\Delta_G)$, and the **degree of the 1-variable slice in
direction $\phi$ equals that width** ($b_1(\ker\phi)=\deg\Delta_G(s^\phi)+p$). In *every* guise our Alexander
polynomial is a **binomial** — $\Delta=X^E-Y^o t$, $D=X^E-Y^o$, $\Delta_1=\gcd(T,S)=1$ — so its Newton polytope is a
**1-dimensional segment** ($t$ raises the ambient dimension but not the polytope dimension; two monomials force a
segment), and $\lVert\cdot\rVert_A$ is a **degenerate rank-$\le1$ seminorm**. The **binomial slice dichotomy**: every
$\phi$ yields either a non-unit binomial $s^a-s^b$ or, in the lone width-$0$ direction, a **vanishing** slice
($b_1=\infty$, the $+1,-1$ monomials collide) — **so no vertex-isolating (unit, $M=1$) slice exists.** This is the
*single geometric reason* behind both the R1 "filtration terminates / order ideal trivial" null and the L1·9
"orbit-residue floor $G^o$" null: **a binomial Alexander polynomial has no $M=1$ slice.** $\mathfrak m$-adic refinement
(McM-5): the cores satisfy $C(u,v)\equiv(E_uo_v-E_vo_u)(X-1)\bmod\mathfrak m^2$ — the $\mathfrak m$-leading term **is the
L1·5 cup product** — so $I=\mathfrak m^{1}\cdot(\cdots)$ ($p=1$, consistent with $b_1\ge2$). **The constructive
consequence (R2 requirement):** a small ($M=1$) slice **provably requires a $\ge2$-dimensional Newton polytope**
($\ge3$ non-collinear monomials). **Every natural rank-1-derived enrichment** — $D$, the second cocycle $T$, the pair
$(\Delta_S,\Delta_T)$, the orbit-circulant reduction — **stays $\dim N\le1$** (verified), so the only viable door is a
genuinely **multi-term** Alexander polynomial: a **non-abelian twisted $\Delta_\rho$** (Boden–Friedl, poly in $t^n$),
the single live R2 route inside the $(2,3)$-dynamics.

**R2·2 (verified, Boden–Friedl — the last door, CLOSED) + the unifying lemma.** Build the twisted Alexander polynomial
of the metabelian SL$(n)$ reps our cocycle admits (these come not from the Crowell module — $\Delta_1=1$, no torsion —
but from the **period / cyclic-cover module** $\mathbb Z[t^\pm]/(X^E-Y^o t)$, with $H/(t^n-1)=\mathbb Z/G(w^n)$, and the
root $t=2^E/3^o$ being **never a root of unity** makes them non-degenerate). The irreducible metabelian monodromy is a
**single weighted $n$-cycle** $R_\chi$, and the **characteristic polynomial of a single weighted cycle is forced
binomial**: $\det(\lambda I-\mu R_\chi)=\lambda^n-(\prod g_i)\mu^n$. Since our cocycle is fibered ($\Delta$ monic in $t$,
unit leading coeff),
$$\Delta_\rho=\det(X^E I_n-Y^o t\,R_\chi)=X^{En}-c_\chi\,Y^{on}t^n,\qquad |c_\chi|=1\ (\text{a weightless root of unity}),$$
a **binomial ⇒ segment polytope ⇒ no $M=1$ slice** — for every metabelian rep, and through every escape (Wada
multiplicativity / direct sum ⇒ collinear binomials; tensor $\alpha_{k_1}\otimes\alpha_{k_2}=\alpha_{k_1k_2}$ ⇒ one
binomial; the within-orbit weighted $o$-cycle / transfer law ⇒ binomial). **So R2 is a decisive NO-GO: no
representation-theoretic twist inside $(2,3)$ produces the 2-dim Newton polytope a constructively small residue
requires.** The single mechanism behind this — **"one weighted cycle ⇒ binomial characteristic polynomial"** — is also
exactly the abelian-DFT collapse (L1·9) and the orbit-circulant amplification; it unifies all three.

---

## 4. The reading program (iterate: note → read → update → iterate)

Redo the literature study **more thoroughly, in this binary/$\chi$-augmentation framing**, as a sustained
loop — each pass a `--leverage` that reads ONE paper *against this note* and proposes updates I fold here.
Re-frame the already-done passes (L1·1 Magnus, L1·2 Fox, L1·3 GSB) into §1–§3 above, then deepen:

| Pass | Read (binary/$\chi$ framing) | Update target |
|------|------------------------------|---------------|
| **R1 — twisted/relative augmentation** ✅ | Crowell, *The derived module of a homomorphism* (via Kontogeorgis–Paramantzoglou arXiv:1904.06665 + Dimca–Maxim) — `drafts/lit-alexander-module.md` | **DONE:** $\mathcal I_D\subset\mathscr A_\psi$ (2-var Crowell module); new cocycle $T=\chi\partial_{x_0}$, $D=(X{-}1)T-(Y{-}1)S$; $\langle D\rangle\subsetneq E_1=\langle T,S\rangle$ ($\Delta_1=\gcd(T,S)$ detects *period*); cores $=E_0=I_2$, **filtration terminates** (no finer $E_k$). Opened: difference ideal $J$ (R3), rank-$\ge2$ enrichment (R2). |
| **R2 — Magnus/Alexander = our $\chi$** | The Alexander matrix as $\chi$-evaluated Fox Jacobian; elementary ideals $E_k$, order ideal; the **order ideal** vs our $\langle D\rangle$ | §1/§3: is $D$ the order ideal? are higher elementary ideals new invariants the lever misses? |
| **R3 — Plücker / bracket algebra** ✅ | Huang–Perlman–Polini–Raicu–Sammartano (arXiv:1909.11705) — `drafts/lit-plucker-bracket.md` | **DONE:** generic generator $=$ Plücker **pair** ($D$- and $S$-row), Koszul redundant; on the cycle stratum **C8 is non-minimal** ($=D\cdot$telescoping) ⇒ extra syzygies (→ R4). $J=$ zero-sum ideal **collapses** to $G$; finer poly gcd $X^a(X{-}1)$ is **non-realizable** (non-PID). No new lever; unifies floor/lever/zero-sum. |
| **R4 — Squier rewriting homology** ✅ | Guiraud–Malbos (arXiv:**1011.0558**) — `drafts/lit-squier-rewriting.md` | **DONE:** 3-cells $=$ 2nd syzygies $=H_2$; over $\mathbb{Q}[X,Y]$ $\operatorname{pd}E_0\le1$ (Hilbert–Burch) ⇒ **resolution terminates, NO 3-cell**. Plücker pair + telescoping are the **complete** 2-cells. Core layer **closed**; holonomy (if real) lives off-ring (R2 / integer $(2,3)$). |
| **Movement IV — expansion-reduction in $A$** (the integer cyclic quotient, 2026-06-09 spine) | non-length-monotone **completion-with-expansion** (Guiraud–Malbos–Mimram homotopical completion–reduction, L1·8) + the **circulant $\mathbb{Z}[\mathbb{Z}/o]$ arithmetic** of the orbit mod $G$ (Silver–Williams resultant $\prod_\zeta$, L1·9) | §2/§3: an expansion-reduction *move* on the cyclic roll realizing a small residue mod $G$ — the lever the polynomial closures (L1·3/R3/R4) cannot see |
| **R5+ — find-thread off the updated note** | re-fan-out on whatever R1–R4 / Movement IV leave open | THREADS.md |

**Loop discipline.** One paper per pass; read the real source; translate into §1–§3 notation; **verify each
new relation on `approaches/cocycle-combine/lib/cocycle.py`** before folding; record honest nulls. After
each pass: update this note, the roadmap status, and (if a new membership certificate / family appears)
`drafts/`. Re-`--find-thread` whenever a pass opens a genuinely new sub-question.

---

## 5. Status / open points

- **Verified & folded:** §1 ($S=\chi\circ\partial_{\mathrm{odd}}$, binary Magnus), §2 ($\chi$-augmentation,
  injectivity), §3 (Plücker module, C8) — all kernel-checked.
- **Reframing TODO:** restate `drafts/lit-{fox-calculus,groebner-shirshov}.md` and the L1·3 "per length"
  wording into the binary/$\chi$ framing of this note (§2 already corrects it to per-stratum / $\chi$-aug).
- **R1 closed (2026-06-08):** $\mathcal I_D$ is the 2-variable Crowell character-augmentation module; exact
  presentation $D=(X{-}1)T-(Y{-}1)S$ with the new even-cocycle $T$. **Higher elementary ideals collapse** —
  the Alexander matrix has only 2 columns, so the Fitting filtration terminates at the cores ($E_0=I_2$);
  **no determinantal invariant finer than the cores**, and the multivariable order ideal is trivial for
  primitive shapes (the rank-1 evaluation at $(2,3)$ is what produces $\langle D\rangle=\langle G\rangle$).
  So: no *new scalar exclusion handle* from the elementary ideals. (Honest null on the R1 prize; the
  presentation is now exact.)
- **R3 closed (2026-06-08):** C8 is **not** the complete relation — the generic generator is the Plücker
  **pair** ($D$- and $S$-row), and on the cycle stratum C8 is *non-minimal* with an extra **constant-
  coefficient telescoping** syzygy. The difference ideal $J$ is the **zero-sum/augmentation ideal**; it
  **collapses** to the rotation-combo floor $G=|D|$ (no finer $o$-independent ceiling), and the finer
  polynomial gcd $X^a(X{-}1)$ is **non-realizable** (non-PID non-membership). Net: $J$ *unifies*
  `rotation-combo-floor` + `bounded-defect-lever` + `zero-sum-combination` under one object — **not a new
  lever**. (Honest null on the R3 prize; the syzygy correction is the gain.)
- **R4 closed (2026-06-08):** 3-cells $=$ second syzygies $=H_2$; over $\mathbb{Q}[X,Y]$ $\operatorname{pd}E_0\le1$
  (Hilbert–Burch) ⇒ **the resolution terminates — no 3-cell, no $H_2$ holonomy beyond C8.** The Plücker pair +
  telescoping are the *complete* 2-cells (the $S$-row is a genuine second 2-cell). (Honest null on the 3-cell
  prize; the closure is the gain.)
- **==> The Layer-1 (core) structural program is COMPLETE.** The cores are the complete handle in all three
  homological directions — Fitting (R1), first syzygies (R3), higher syzygies (R4). The algebra contains **no
  new exclusion lever**: every invariant collapses to the cores, which collapse (as a ceiling) to $G=|D|$. This
  *rigorously confirms the two-layer thesis*: the exclusion content is **not** in the Layer-1 algebra — it is
  in the **Layer-2 arithmetic** at $(2,3)$ (primitive divisors / $\operatorname{sixfree}\to\infty$).
- **L1·5 closed (2026-06-09; Movement III — cup products / weight):** the cup product is the
  **$\partial_X$-linearization of the core** at the trivial character ($\partial_X C\rvert_{1,1}=(E,o)$-wedge,
  the rank-1 shadow; single-word primitive $A$ with $\delta A=$ linearized core) — **no new constructive lever**
  (holonomy quadratic $=$ Jacobi $=$ C8 shadow). **Gain:** the **weight / Chen-rank grading** is the *named*
  structural source of [P3]'s $o$-independence ($C(\beta,d)$ a fixed weight-2 element, unique bracket), and the
  open $\ge2$-growing-gap no-go restates as **weight-growth $\omega\to\infty$**. Suggested build: the
  $\chi$-deformation **weight tower** $\partial_X^k C\rvert_{1,1}/k!$ — is exclusion a **finite-weight**
  phenomenon? (→ L1·6.) Honest null on a new lever; the weight bridge is the gain. (`drafts/lit-suciu-wang.md`.)
- **L1·8 done (2026-06-09; Movement IV — completion-with-expansion):** the non-length-monotone **completion**
  procedure (Guiraud–Malbos–Mimram) adds **no expansion-reduction move** on the cyclic roll. **(A)** Tietze
  generator-adding / block-coarsening is **$S$-invisible** ($\Phi$ a faithful monoid hom — the *rewriting form
  of the L1·3 per-stratum injectivity*); **(B)** the C8 overlap $\delta$ is coarsening-invariant ⇒ completion
  re-derives C8, adds no cell; the run-sliding family completes to **one fixed weight-2 cell** $C(\beta,d)$
  ([P3] repackaged). **⇒ word/monoid-level expansion is dead too** — the expansion-reduction lever, if it
  exists, must be the **integer circulant residue of the orbit mod $G$** (Movement IV / L1·9), not a rewriting
  move. Gain: the **quasicenter heuristic** is the constructive criterion for when [P3] exists. Honest null.
  (`drafts/lit-homotopical-completion.md`, 14/14.)
- **L1·9 done (2026-06-09; Movement IV — integer circulant):** the orbit circulant determinant is a **resultant**
  $\prod_\zeta\widehat S(\zeta)$ (R-SW2), and since $G$ sits in every DFT component it **amplifies the floor to
  $G^o$** (R-SW4) — the sharp integer avatar of R3's $J$-collapse: **no smaller orbit residue is constructible.**
  The obstruction is exact: the cycle $\Delta=X^E-Y^o t$ is degree-1 & non-cyclotomic ⇒ Mahler $\gt1$ ⇒ Gordon
  growth (Layer-2). Imports: transfer law (R-SW1), period Fox formula $G(w^r)=\prod_{d\mid r}\Phi_d^*(2^E,3^o)$
  (R-SW3, $\Delta_1=$ cyclic-cover cofactor → Layer-2 Zsygmondy). (`drafts/lit-silver-williams.md`, 49/49.)
- **==> Movement-IV verdict (both spine probes null on construction).** The expansion-reduction strategy on a
  **single rank-1 orbit** cannot beat the floor $G$: word/monoid completion is $S$-invisible (L1·8) and the integer
  circulant amplifies $G$ to $G^o$ (L1·9). The crux is structural — **the cycle Alexander polynomial is degree-1
  and never cyclotomic.** The two live doors are therefore both *off the single rank-1 orbit*: **(1) R2** — a
  rank-$\ge2$ enrichment giving a **higher-degree $\Delta$ that could be cyclotomic** for a structured family (the
  only route to a constructively small residue); **(2) Layer-2** — Bang–Zsygmondy / BHV on the $\Phi_d^*(2^E,3^o)$
  blocks (the [P3] no-go).
- **R2 narrowed (2026-06-09; McMullen pivot, verified).** The Alexander-norm$=$polytope-width law gives the *exact*
  shape R2 must take and **refutes every rank-1-derived enrichment**: a constructively small ($M=1$) slice requires a
  **2-dim Newton polytope**, but $D,T,(\Delta_S,\Delta_T)$ and the orbit circulant are all **binomial/segment**
  ($\dim N\le1$). This **unifies the R1 and L1·9 nulls into one geometric fact** (a binomial $\Delta$ has no $M=1$
  slice) and leaves **exactly one live door inside $(2,3)$:** a **non-abelian twisted Alexander polynomial $\Delta_\rho$**
  (multi-term in $t^n$, Boden–Friedl) — does it acquire a genuine 2-dim polytope (GO) or collapse to a binomial (NO-GO)?
  That is the next leverage. (A genuinely independent third modulus would also work but is artificial in the
  $(2,3)$-dynamics.) (`drafts/lit-mcmullen-norm.md`, 18/18.)
- **R2 CLOSED (2026-06-09; Boden–Friedl R2·2, verified) — the LAST Layer-1 door is shut.** The metabelian twisted
  Alexander polynomial — the one route McMullen left open — **stays binomial**: the metabelian monodromy is a single
  weighted $n$-cycle, whose char poly is forced binomial $\lambda^n-(\prod g_i)\mu^n$, so
  $\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$ (segment, no $M=1$ slice), and every escape (Wada mult./tensor/within-orbit)
  is binomial too. **Decisive NO-GO: no representation-theoretic twist inside $(2,3)$ gives a 2-dim Newton polytope.**
  Unifying lemma "one weighted cycle ⇒ binomial char poly" $=$ the common mechanism of the abelian-DFT (L1·9),
  metabelian (R2·2), and orbit-circulant collapses. (`drafts/lit-boden-friedl.md`, 18/18.)
- **==> THE LAYER-1 ALGEBRA IS NOW CLOSED IN ALL THREE DIRECTIONS, and the two-layer thesis is finalized.**
  (i) *polynomial syzygies* — Fitting (R1) / 1st syz (R3) / higher syz (R4): the cores are the complete handle, $\operatorname{pd}\le1$, no 3-cell.
  (ii) *integer-quotient expansion-reduction* (Movement IV) — word/monoid completion is $S$-invisible (L1·8); the integer circulant amplifies the floor to $G^o$ (L1·9).
  (iii) *representation-theoretic enrichment* (R2) — every rank-1-derived enrichment **and** every metabelian twist inside $(2,3)$ has a **binomial Alexander polynomial ⇒ segment Newton polytope ⇒ no $M=1$ slice** (McMullen R2·1 + Boden–Friedl R2·2).
  **Every avenue collapses to the same wall: the cocycle's Alexander polynomial is a binomial $X^E-Y^o t$, and a binomial
  has no unit slice.** Therefore the algebra contains **no constructive lever**, and exclusion lives **entirely in the
  Layer-2 $(2,3)$-arithmetic** — primitive divisors / $\operatorname{sixfree}\to\infty$ of the $\Phi_d^*(2^E,3^o)$ blocks
  (R-SW3), the home of the `approaches/bounded-defect-lever` no-go. **The algebraic incubation has reached its natural
  terminus.**
- **The two remaining doors (both off the closed ring):**
  1. **R2 — rank-$\ge2$ enrichment:** a third modulus → $\operatorname{gldim}\ge3$ → a *genuine* 3-cell, and
     $\Delta_1=\gcd(T,S)$ non-trivial on primitive shapes. The only route to new *algebraic* content.
  2. **The integer specialization at $(2,3)$** (Layer 2): the actual home of exclusion — the
     `bounded-defect-lever` no-go ($\operatorname{sixfree}(Q_a(2,3))\to\infty$) via Bang–Zsygmondy / BHV.
- **A handle worth a look:** the explicit **Hilbert–Burch matrix $\Psi$** (cores $=$ its maximal minors) — does a
  small entry of $\Psi$ give an $o$-independent ceiling the cores miss? (carried into R5/R2.)
