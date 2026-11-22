# Leverage R2 (group G, structural pivot): McMullen's Alexander norm — the GO/NO-GO for rank-$\ge2$ via the Newton polytope

**Promise:** high (as a *decision*). R2 reads the real McMullen paper against STRUCTURE §0
(the integer cyclic quotient, expansion-reduction), §2 (the Crowell module, $\mathfrak m$,
$D=(X{-}1)T-(Y{-}1)S$), §3 (the cores), and the L1·9 verdict (the cycle Alexander polynomial
$\Delta=X^E-Y^o t$ is degree-1 and never cyclotomic). It **decides** the Movement-IV door R2:
does a rank-$\ge2$ enrichment open a constructively small orbit residue, and if so what *exact*
shape must it take?

**Verdict (verified, 18/18 on the kernel): refined NO-GO for every natural
rank-1-derived enrichment.** McMullen's Alexander norm is the **width of the Newton polytope**
of $\Delta_G$, and our $\Delta_G$ is a **binomial / collinear in every guise** — the cycle
$\Delta=X^E-Y^o t$ (a 2-monomial segment), the 2-variable Crowell $\Delta_1=\gcd(T,S)=1$
(a unit, a point), and the imprimitive period factor (a collinear sum). A binomial has
$\dim N(\Delta_G)\le1$, so $\lVert\cdot\rVert_A$ is a **degenerate rank-$\le1$ seminorm** with
**no vertex-isolating direction**: every $\phi$ gives either a degree-$\lVert\phi\rVert_A$ binomial
slice $s^a-s^b$ (never a unit) or, in the one width-$0$ direction, a **vanishing** slice
($b_1(\ker\phi)=\infty$). A constructively small ("unit") slice provably requires a **2-dimensional**
Newton polytope ($\ge3$ non-collinear monomials), which **no rank-1-derived object can manufacture**
($D$, the second cocycle $T$, the pair $(\Delta_S,\Delta_T)$, and the orbit-circulant reduction all
stay $\dim\le1$). The only doors to a 2-dim polytope are a **genuinely independent third modulus**
(absent in the $(2,3)$-dynamics) or a **non-abelian twisted Alexander polynomial** (Boden–Friedl) —
the latter is the single door that stays inside $(2,3)$ and is the recommended next leverage.

**Leveraged for / deepens:** the L1·9 binomial-non-cyclotomic floor (`lit-silver-williams.md`),
the R1 terminating filtration / order-ideal-trivial null (`lit-alexander-module.md`), and the L1·5
cup product (now recovered as the $\mathfrak m/\mathfrak m^2$ leading term of the cores).

**Status:** read in full (§§1–7 + the degenerate-norm examples 4, 10 and the failure-of-convexity
$D_\infty\times D_\infty$ example; appendix table skimmed). Dictionary built; verdict verified
(`checks/lit_mcmullen_norm.py`, 18/18, exit 0). **Last iterated:** 2026-06-09.

---

## Source (real, complete; identity confirmed)

C. T. McMullen, *The Alexander polynomial of a 3-manifold and the Thurston norm on cohomology*,
Ann. Sci. École Norm. Sup. (4) **35** (2002) 153–171 —
[`sources/mcmullen-alexander-thurston-norm-2002.pdf`](../sources/mcmullen-alexander-thurston-norm-2002.pdf)
(23 pp., read in full). Cited results:

- **eq (1.1)** $\lVert\phi\rVert_A\le\lVert\phi\rVert_T$ (Alexander $\le$ Thurston norm), with
  **Thm 1.1** the equality-up-to-correction $\lVert\phi\rVert_A\le\lVert\phi\rVert_T+p(M)$-type bound.
- **eq (1.2) / Thm 5.1** $I(G)=\mathfrak m^{p(M)}\cdot(\Delta_G)$, $\mathfrak m=m(\operatorname{ab}(G))$
  the augmentation ideal, $p=0$ if $b_1\le1$ else $1+b_3(M)$.
- **eq (1.3) / Thm 4.1** $b_1(\ker\phi)=\deg\Delta_G(s^\phi)+p(M)=\lVert\phi\rVert_A+p$ for primitive
  $\phi$ in the cone on the open faces of the norm ball.
- **§4 / eq (7.1)** $\lVert\phi\rVert_A=\sup_{a_\alpha a_\beta\ne0}\phi(\alpha-\beta)=
  \operatorname{length}\big(\phi(N(\Delta_G))\big)$ — the Newton-polytope **width**; the unit ball is
  (up to scale 2) **dual** to $N(\Delta_G)$.
- **eq (4.3)** $\deg\Delta_G(s^\phi)=\lVert\phi\rVert_A$ **iff the extreme values $\phi(\alpha)$ are
  attained uniquely** (else cancellation drops the slice degree — the load-bearing caveat for us).
- **Examples 4 ($5_1^2$, $\Delta=(1-t_1)(1-t_2)$) and 10 (trivial $\Delta_K=1$):** the 1-variable
  slice under-reports / vanishes; "the genus is controlled more precisely by the Alexander norm than
  by the 1-variable Alexander polynomial." **Failure of convexity ($D_\infty\times D_\infty$):**
  $I(G)=\langle x^2-1,y^2-1,(x-1)(y-1)\rangle$, a genuine **2-dim** Newton polytope with
  convex+periodic $b_1(\ker\phi)$ — the template for a rank-$\ge2$ enrichment.

---

## §Dictionary — McMullen $\leftrightarrow$ ours (with the load-bearing mismatch)

Write $w$ a gap word, $E=|w|$ even steps, $o=\operatorname{len}w$ odd steps; abelianization
$H=\operatorname{ab}(G)=\langle X,Y\rangle\cong\mathbb Z^2$ ($X\leftrightarrow2$, $Y\leftrightarrow3$);
augmentation ideal $\mathfrak m=\langle X-1,Y-1\rangle$.

| McMullen | Ours | Status |
|---|---|---|
| Alexander polynomial $\Delta_G\in\mathbb Z[\operatorname{ab}(G)]$ | **two guises:** the 2-var Crowell $\Delta_1=\gcd(T,S)$ (R1), **and** the cycle/period $\Delta=X^E-Y^o t$ (L1·9) | exact, *both binomial/collinear* |
| Newton polytope $N(\Delta_G)$; Alexander norm $\lVert\phi\rVert_A=\operatorname{width}_\phi N$ (eq 7.1) | $N(\Delta)=$ segment $[(E,0,0),(0,o,1)]$; $N(\Delta_1)=$ point (primitive) / collinear (imprimitive) | exact; $\dim N\le1$ |
| augmentation ideal $\mathfrak m=m(\operatorname{ab}(G))$; $I(G)=\mathfrak m^{p}(\Delta_G)$ (eq 1.2) | $\mathfrak m=\langle X-1,Y-1\rangle$; cores $C(u,v)=2{\times}2$ minors $=$ McMullen's maximal-minor $I(G)$; **cores $\subset\mathfrak m^1\setminus\mathfrak m^2$, so $p=1$** | exact on the cores |
| $b_1(\ker\phi)=\lVert\phi\rVert_A+p$ (eq 1.3) — cover-homology RANK | $\deg_t\Delta=\lVert\phi_t\rVert_A=1$ (RANK, bounded); floor $G=|2^E-3^o|$ is the **torsion** (L1·9, Silver–Williams Mahler) | exact; the degree/torsion split |
| slice $\Delta_G(s^\phi)$ unique-extreme caveat (eq 4.3) | binomial $\Rightarrow$ width-$0$ slice **vanishes** ($+1,-1$ collide); else slice $=s^a-s^b$ | exact (PART C) |

**The two load-bearing facts.**
1. **The Alexander norm sees only $\Delta_G$ (the gcd / determinant), not the raw cocycle.** The
   *individual* cocycle $S(w)=\sum_k X^{e_k}Y^{o-1-k}$ has a fat (often 2-dim) Newton polytope, but
   the Alexander **polynomial** $\Delta_1=\gcd(T,S)$ collapses it to a **unit** ($=1$, primitive) and
   the cyclic-cover normalization (based module, R-SW3) collapses the circulant to the **binomial**
   $X^E-Y^o t$. So enrichments that merely "use more monomials of $S$" do not enlarge the norm — the
   norm is a property of the gcd, which is binomial.
2. **MISMATCH (honest): the $\mathfrak m^{p}$ factorization attaches to the CORES, not to
   $\langle T,S\rangle$.** $\epsilon(S)=o$, $\epsilon(T)=E$ are $\ne0$, so $\langle T,S\rangle\not\subseteq
   \mathfrak m$ and cannot be $\mathfrak m^{p}\langle\Delta_1\rangle$. McMullen's $I(G)$ is the
   **maximal-minor** ideal $=$ our cores $E_0$ (every core $\in\mathfrak m$), and *those* obey
   $I(G)=\mathfrak m^1\cdot(\Delta_G)$ with $p=1$. Our free single-relator Crowell module is **not
   literally a 3-manifold Alexander ideal** (no $\partial\partial=0$), so the $\mathfrak m^p$ structure
   is a *translation onto the cores*, not an identity on the order ideal.

---

## §Relation extracted (in OUR notation)

**The Alexander-norm restatement of the floor (NEW framing; unifies R1 + L1·9).**

> **(McM-1) Polytope-dimension bound.** $\dim N(\Delta_G)\le(\#\text{monomials of }\Delta_G)-1$.
> Our $\Delta_G$ is a binomial or a collinear sum in *every* guise:
> the cycle $\Delta=X^E-Y^o t$ (2 monomials $\Rightarrow$ a **segment**, even with $t$ a formal third
> variable — $t$ raises the ambient dimension but **not** the polytope dimension), $D=X^E-Y^o$
> (segment), $\Delta_1=\gcd(T,S)=1$ for primitive shapes (a **point**), and the imprimitive period
> factor $\sum_i X^{ai}Y^{b(k-1-i)}$ (**collinear**). Hence $\dim N(\Delta_G)\le1$ always.

> **(McM-2) The Alexander norm is a degenerate rank-$\le1$ seminorm.** $\lVert\phi\rVert_A=
> \operatorname{width}_\phi N(\Delta)=|\phi(\alpha_1-\alpha_2)|$ for the segment endpoints
> $\alpha_1=(E,0,0),\alpha_2=(0,o,1)$; it **vanishes on the codim-1 hyperplane** $\phi\perp(\alpha_1-
> \alpha_2)$. (A genuine 2-dim norm would vanish only at $\phi=0$.)

> **(McM-3) The binomial slice dichotomy — the precise reason there is no small slice.** For the
> cycle binomial, in *every* direction $\phi$ the McMullen slice $\Delta(s^\phi)$ is
> $$\Delta(s^\phi)=\begin{cases} s^{\phi(\alpha_1)}-s^{\phi(\alpha_2)} & \phi\not\perp\text{ segment:
> a degree-}\lVert\phi\rVert_A\text{ BINOMIAL, never a unit};\\[2pt]
> 0 & \phi\perp\text{ segment: the two unit monomials COLLIDE and CANCEL }(b_1(\ker\phi)=\infty).
> \end{cases}$$
> **No $\phi$ gives a UNIT (single-monomial) slice.** The only degree-$0$ directions *kill* $\Delta_G$
> rather than isolating a vertex. This is the McMullen-language statement of the L1·9 floor:
> the polytope being a segment is *exactly* why the orbit/period residue never bottoms out small.

> **(McM-4) The exact rank-$\ge2$ requirement.** A vertex-isolating ("unit") slice requires a
> **2-dimensional** Newton polytope, i.e. $\ge3$ **non-collinear** monomials, so that some normal
> cone of a $0$-dim face isolates a single monomial. A binomial (or any collinear support) structurally
> cannot. **Verified contrast:** a genuine trinomial with non-collinear support has $\dim N=2$ and a
> $\phi$ that yields a unit slice; the natural enrichments $(D,\ \text{cycle-}\Delta,\ \Delta_1=
> \gcd(T,S))$ all have $\dim N\le1$.

> **(McM-5) The $\mathfrak m$-adic / cup-product bridge (consistent with $p=1$).** Every core
> $C(u,v)\in\mathfrak m$, and its $\mathfrak m/\mathfrak m^2$ leading term is **the L1·5 cup product**:
> $$C(u,v)\equiv (E_u o_v-E_v o_u)\,(X-1)\pmod{\mathfrak m^2},\qquad
>   D\equiv E\,(X-1)-o\,(Y-1)\pmod{\mathfrak m^2}.$$
> So the cores sit in $\mathfrak m^1\setminus\mathfrak m^2$ generically $\Rightarrow$ augmentation
> power $p=1$ ($b_3=0$, the link-complement branch), and McMullen's $I(G)=\mathfrak m^{p}(\Delta_G)$
> recovers the cup product as the **first** ($\mathfrak m^1$) term of the augmentation filtration of
> the core ideal — i.e. the cup-product linearization is literally the McMullen leading term.

**The degree/torsion split (the clean synthesis of R2 + L1·9).** $\Delta=X^E-Y^o t$ is degree-1, so
McMullen's $b_1(\ker\phi)=\lVert\phi\rVert_A+p$ caps the cover-homology **rank** at $1+p$ (bounded),
while the **floor $G=|2^E-3^o|$ is pure torsion**, governed by the Silver–Williams Mahler measure
$M(\Delta)=\max(2^E,3^o)\gt1$ (L1·9). McMullen handles the rank/degree face; Silver–Williams handles
the torsion face; both are minimal/degenerate because the **same** polytope is a segment.

**New?** McM-1/2/3/4 are **new** (a polytope-dimension criterion not previously written; it *unifies*
R1's "order ideal trivial" and L1·9's "binomial, never cyclotomic" under one geometric statement and
names the exact rank-$\ge2$ shape). McM-5 is a **new derivation** linking McMullen's $\mathfrak m^p$
filtration to the L1·5 cup product. **Translatable?** yes — all in $S,T,D,C,\mathfrak m,G$ and the
Newton polytope, with the one honest mismatch (McM attaches to the cores, not $\langle T,S\rangle$).

---

## §Verification (`checks/lit_mcmullen_norm.py`, 18/18, exit 0)

Self-contained from repo root; imports the real kernel `from cocycle import X, Y, S, D, core_C,
rotations`. sympy `Poly` + affine-hull rank for polytope dimension; grid enumeration of $\phi$ for the
norm/slice.

- **PART A — polytope dimensions (McM-1).** cycle $\Delta=X^E-Y^o t$ a segment (dim 1, 2 monomials,
  $t$ adds no dimension); $D$ a segment; $\Delta_1=\gcd(T,S)=1$ a point (dim 0) for 6 primitive
  shapes; imprimitive $w=u^k$ nontrivial but collinear (dim $\le1$) for 5 shapes. ✓
- **PART B — norm = width, degenerate (McM-2).** $\lVert\phi\rVert_A=$ width $=|\phi(\alpha_1-\alpha_2)|$
  on a $5^3$ grid; an explicit nonzero $\phi\perp$ segment has $\lVert\phi\rVert_A=0$. ✓
- **PART C — slice dichotomy / no unit slice (McM-3).** width$>0\Rightarrow$ slice is a binomial of
  deg-span $=\lVert\phi\rVert_A$ (eq 4.3); width$=0\Rightarrow$ slice $\equiv0$ (vanishing); **no $\phi$
  over the grid yields a single-monomial slice.** ✓
- **PART D — rank-$\ge2$ requirement (McM-4).** a non-collinear trinomial has $\dim N=2$ **and** a
  unit-slice direction; the natural enrichments $(D,\text{cycle-}\Delta,\Delta_1)$ all have
  $\dim N\le1$. ✓
- **PART E — $\mathfrak m^p$ / cup-product bridge (McM-5).** cores and $D\in\mathfrak m$; $D\in
  \mathfrak m\setminus\mathfrak m^2$ with linearization $E(X-1)-o(Y-1)$; core $\equiv(E_uo_v-E_vo_u)(X-1)
  \bmod\mathfrak m^2$ (cup product, $Y$-part vanishes); generically $\in\mathfrak m^1\setminus\mathfrak
  m^2\Rightarrow p=1$; honest mismatch $\epsilon(S)=o,\epsilon(T)=E\ne0\Rightarrow\langle T,S\rangle
  \not\subseteq\mathfrak m$. ✓
- **PART F — degree/torsion split.** $\deg_t\Delta=\lVert\phi_t\rVert_A=1$ (rank); $G=|2^E-3^o|$ the
  torsion. ✓

---

## §R2 verdict — refined NO-GO (decisive), with the exact GO requirement named

**NO-GO for every natural rank-1-derived enrichment.** McMullen's machinery proves the floor is
unbeatable *off the polytope*: the Alexander norm is a property of $\Delta_G$, $\Delta_G$ is
binomial/collinear, so $N(\Delta_G)$ is a **segment** and $\lVert\cdot\rVert_A$ a **degenerate rank-$\le1$
seminorm** with **no vertex-isolating direction**. Concretely, none of
- the second cocycle $T$ / the pair $(\Delta_S,\Delta_T)$ / the object $(D,S,T)$,
- the orbit circulant $\widehat S(t)=\sum_jS^{(j)}t^j$ (which the based-module normalization R-SW3
  reduces to the binomial $X^E-Y^o t$),
- the imprimitive period factor,

escapes $\dim N\le1$. **What a GO strictly requires (McM-4):** a $\Delta_G$ with a **2-dimensional
Newton polytope** ($\ge3$ non-collinear monomials), so that a face/vertex direction isolates a single
monomial and a *bounded/small* slice exists — equivalently (Gordon, via L1·9) room for a **cyclotomic
factor** that a degree-1 binomial cannot house. The exact McMullen template is the failure-of-convexity
group $D_\infty\times D_\infty$: $I(G)=\langle x^2-1,y^2-1,(x-1)(y-1)\rangle$, a **non-principal**
Alexander ideal with $p$-structure and a 2-dim polytope and convex+periodic $b_1(\ker\phi)$.

**Two doors to a 2-dim polytope, exactly one of them inside $(2,3)$:**
1. **A genuinely independent third modulus** (a third multiplicatively-independent base / prime $\to$
   a third variable $Z$ with a non-collinear monomial $\Rightarrow H=\mathbb Z^3$, $b_1\ge2$,
   McMullen's $p=1+b_3$ branch active). This is **absent in the $(2,3)$-Syracuse dynamics** — it would
   be an artificial enrichment not reflecting the map. **Refined NO-GO.**
2. **A non-abelian twisted Alexander polynomial** (Boden–Friedl): a rank-$\ge2$ representation $\rho$ of
   the free group gives a twisted $\Delta_\rho(t)$ that is a genuine **polynomial in $t^n$** (multi-term,
   degree up to $n\dim\rho$) — **not** a binomial, so the segment obstruction does not apply, and it
   stays inside $(2,3)$ (no third prime). **This is the single live R2 door** and the recommended next
   leverage.

So: **R2 via natural (abelian, rank-1-derived) enrichments is NOT viable** — the precise obstruction is
"binomial $\Rightarrow$ segment $\Rightarrow$ degenerate seminorm $\Rightarrow$ no isolating vertex."
The one remaining route is the **non-abelian twist**, which alone can break the binomial without
inventing a third modulus.

---

## §Proposed structure (what to build for R2)

1. **Fold the polytope-dimension law into STRUCTURE §3 (one line that retires two nulls).** "The
   Alexander norm $\lVert\phi\rVert_A=\operatorname{width}_\phi N(\Delta_G)$ is a degenerate rank-$\le1$
   seminorm because $\Delta_G$ is binomial/collinear in every guise; this is the *single* geometric
   reason behind both R1 (order ideal trivial: $N(\Delta_1)$ a point) and L1·9 (binomial, never
   cyclotomic: $N(\Delta)$ a segment). A constructive small slice needs $\dim N(\Delta_G)\ge2$."
2. **Record McM-5 as the $\mathfrak m$-adic refinement of R1+L1·5:** cores $\in\mathfrak m^1\setminus
   \mathfrak m^2$, $\mathfrak m/\mathfrak m^2$-class $=(E_uo_v-E_vo_u)(X-1)$ (the cup product), giving
   $p=1$ in $I(G)=\mathfrak m^{p}(\Delta_G)$ — the augmentation filtration of the core ideal *is* the
   weight tower whose weight-1 layer is L1·5's cup product.
3. **Set up the twisted-Alexander test object** for the Boden–Friedl leverage: for a rank-2
   representation $\rho$ of the free group $\langle x_0,x_1\rangle$, compute $\Delta_\rho(t)$ of the
   rotation/period family and its Newton polytope — is it 2-dimensional (GO) or does the abelian
   collapse force it back to a binomial (NO-GO)? This is the decisive R2 follow-up.

**Promotion-readiness:** **no.** This is a decision (refined NO-GO on the abelian rank-$\ge2$ door) plus
a unifying geometric law and the $\mathfrak m$-adic cup-product bridge — it tightens STRUCTURE and names
the exact next test, but produces no new excludable family.

---

## §Open questions (feed the next group-G leverage)

- **Q1 (Boden–Friedl, the recommended next).** Does a non-abelian rank-2 twisted Alexander polynomial
  $\Delta_\rho(t)$ of the rotation/period family have a **2-dimensional** Newton polytope (a genuine
  norm, a vertex-isolating slice), or does the abelianization collapse it back to a binomial? This is
  the *only* door McM-4 leaves open inside $(2,3)$.
- **Q2 (Morifuji–Suzuki / twisted-norm).** If $\Delta_\rho$ is 2-dim, does the twisted Alexander norm
  still satisfy $\lVert\phi\rVert_{A,\rho}\le\lVert\phi\rVert_T$, and is there a $\rho$-direction with a
  **cyclotomic** slice (bounded torsion) — the constructive small residue?
- **Q3 (the third-modulus polytope, low promise).** Is there any *natural* (dynamics-respecting) third
  variable — e.g. tracking a second prime in a generalized $3x+1$-type map $(2,p)$ — that gives a
  non-collinear $\Delta_G$ without being artificial? (Likely no; the $(2,3)$-pair is irreducible.)
- **Q4 (the cup-product weight tower).** Does the $\mathfrak m$-adic filtration of the core ideal
  ($\mathfrak m^1=$ cup product, $\mathfrak m^2,\dots$) give a *finite-weight* characterization of the
  exclusion (the L1·5 weight-tower question), now that $p=1$ pins the $\mathfrak m^1$ layer?

**Follow-up refs worth queuing** (do not mine here): **Boden–Friedl**, *Metabelian $SL(n,\mathbb C)$
representations of knot groups* / the twisted-Alexander-polynomial-and-Thurston-norm line (the
multi-term $\Delta_\rho(t^n)$ — door Q1); **Suciu**, *Characteristic varieties and Betti numbers of
abelian covers* (the convex+periodic $b_1(\ker\phi)$ of the $D_\infty\times D_\infty$ template, the
exact rank-$\ge2$ shape McMullen points to).
