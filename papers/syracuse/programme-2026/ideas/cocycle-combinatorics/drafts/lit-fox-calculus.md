# Leverage: Fox free differential calculus (Fox, Annals 57 (1953) 547–560) — L1·2

**Promise:** high — Fox calculus is the *canonical* algebraic home of our cocycle, and it
delivers exactly what L1·2 asked for: a **systematic generator** that unifies P0/P1/P2/P3 into a
single identity (the abelianized product rule / slot-difference), plus two genuinely new objects in
our notation — the **per-gap splitting** $S=\sum_d S_d$ into honest Fox derivatives and the
**fundamental formula** $D(w)=\sum_d S_d(w)(X^d-Y)$ that realizes the cycle-ideal generator $D$ as a
Fox-derivative combination. It is the engine L1·3 (Gröbner–Shirshov) and L1·4 (Squier) consume.
**Status:** read in full (the original 14-pp. scan + a complete rigorous exposition); rank-1
dictionary built; all 14 transfers verified on the kernel (`checks/lit_fox_calculus.py`, exit 0).
**No new length-reducing move past the known obstruction** ($\chi(u)=1$ / reversal=transpose); the
yield is the unification + the generating machinery (an honest, valuable "systematize, don't add").
**Last iterated:** 2026-06-08

**Source:** R. H. Fox, *Free Differential Calculus I: Derivation in the Free Group Ring*, Annals of
Math. **57** (1953) 547–560 — [`sources/fox-free-diff-calc-I-1953.pdf`](../sources/fox-free-diff-calc-I-1953.pdf)
(JSTOR scan, read in full). Complete rigorous exposition with all proofs filled in: S. B. Han,
*The Fox Calculus and Differentiation in Group Rings*, Portland State MTH 501 (2022) —
[`sources/han-fox-calculus-exposition.pdf`](../sources/han-fox-calculus-exposition.pdf) (text dump
[`sources/han.txt`](../sources/han.txt)). Equation numbers below are **Fox's own**.

---

## 1. What Fox proves (the reduction primitives, with citations)

The free group ring $JX$ over a free group $X$ on generators $(x_j)_{j\in J}$ (Fox allows $J$
non-enumerable — footnote, p. 550). A **derivation** $D:JX\to JX$ satisfies (Fox §1):

| Fox eq. | rule | our reading |
|---|---|---|
| (1.1) | $D(u+v)=Du+Dv$ | additivity |
| (1.2) | $D(u\cdot v)=Du\cdot v^{\,o}+u\cdot Dv$ | **product rule** ($o$ = retraction $x_j\mapsto1$) |
| (1.2)' | $D(gh)=Dg+gDh$ | product rule on group elements |
| (1.5) | $D(u_1\cdots u_l)=\sum_{i}u_1\cdots u_{i-1}\,Du_i\,u^{o}_{i+1}\cdots u^{o}_l$ | **multi-factor product rule** |
| (1.6) | $D(g^{-1})=-g^{-1}Dg$ | **inverse rule** (needs inverses) |
| (2.1) | $\partial x_k/\partial x_j=\delta_{jk}$ | the $j$-th Fox derivative $\partial/\partial x_j$ |
| (2.2) | $f'(x)=\sum_j(\partial f/\partial x_j)\,h_j(x)$ | every derivation is $\sum_j h_j\,\partial/\partial x_j$ |
| **(2.3)** | $\boxed{f(x)=f(1)+\sum_j(\partial f/\partial x_j)(x_j-1)}$ | **fundamental formula** (the reduction primitive) |
| (2.4) | $\partial x_j^{p}/\partial x_j=(x_j^{p}-1)/(x_j-1)=1+x_j+\cdots+x_j^{p-1}$ | **power rule** (the telescoping engine) |
| (2.5) | $\partial u/\partial x_j=\sum_i u_0x_j^{p_1}u_1\cdots u_{i-1}\,(x_j^{p_i}-1)/(x_j-1)$ | practical rule |
| (2.6) | $\partial f^{\lambda}/\partial x_j=\sum_k(\partial f/\partial y_k)^{\lambda}\,\partial y_k^{\lambda}/\partial x_j$ | **chain rule** (block-coarsening) |
| (2.8) | $\partial u/\partial x_j=\sum_{k:\,j_k=j}\varepsilon_k\,u_{(k)}$ | **explicit "initial-sections" formula** |

Two framings Fox stresses that we use directly. **(i) Magnus = Fox** (Intro B, p. 547; §3, eq. (3.4)):
"the coefficients in the Magnus power-series representation are free derivatives evaluated at $x=1$",
i.e. the Magnus matrix is built from $\partial w/\partial x_j$. **(ii) Derivatives are 1-cocycles**
(Intro C, p. 547): "the derivatives are just the 1-dimensional cocycles, if one regards the group ring
as operating on itself; the partial derivatives $\partial/\partial x_j$ constitute a basis for the
1-dimensional cohomology group." That is precisely our "S is a Magnus/Fox 1-cocycle".

---

## 2. Dictionary — our $S/M/C$ $\leftrightarrow$ Fox derivatives (rank-1 rep)

Our words are **positive** words $w=(d_0,\dots,d_{n-1})$, $d_p\in\mathbb N_{\gt0}$, in the **free
monoid** on the gap-value alphabet $\{x_d:d\in\mathbb N_{\gt0}\}$ (one generator per gap value —
**infinitely many**). For a positive word every exponent $\varepsilon_k=+1$, so the $k$-th initial
section in (2.8) is just the **prefix** $w[0:p]$, and Fox's derivative is the explicit closed form
$$\boxed{\ \frac{\partial w}{\partial x_d}=\sum_{p:\,d_p=d}\ w[0:p]\ }\qquad(\text{a sum of prefixes, in }JX).$$

The **rank-1 abelianization** is the pair of one-variable homomorphisms
$$\alpha_X:\ x_d\mapsto X^{d}\quad(\text{left / gap-weight}),\qquad
  \varepsilon_Y:\ x_d\mapsto Y\quad(\text{right retraction }o\text{, replacing }x_d\mapsto1).$$

**The precise identity (answer to "is $S=\sum_i\partial w/\partial x_i$?").** Yes — $S$ is the
**total Fox derivative twisted by $(\alpha_X,\varepsilon_Y)$**. Define the **per-gap partial cocycle**
$$S_d(w)\ :=\ \sum_{p:\,d_p=d} X^{e_p}\,Y^{\,n-1-p}\ =\ (\alpha_X,\varepsilon_Y)\text{-evaluation of }\partial w/\partial x_d ,$$
(each prefix $w[0:p]$ contributes $X^{e_p}$ on its left and $Y^{n-1-p}$ from the $n-1-p$ letters to
the right of the differentiated occurrence). Then, exactly:
$$\boxed{\ S(w)=\sum_{d\ge1}S_d(w)\ }\qquad\text{and}\qquad
  S(w)\big|_{Y=1}=\sum_{d\ge1}\alpha_X\!\Big(\tfrac{\partial w}{\partial x_d}\Big).$$
The clean (untwisted) statement is the $Y=1$ slice: **$S|_{Y=1}$ is literally the sum of the
abelianized Fox derivatives.** The full $S$ adds the position grading $Y^{n-1-p}$, which is Fox's
right-retraction $o$ deformed from $x_d\mapsto1$ to $x_d\mapsto Y$. Equivalently $S$ is the
**off-diagonal of the rank-1 Magnus matrix**
$$\Phi(x_d)=\begin{pmatrix}X^{d}&1\\0&Y\end{pmatrix}
  =\begin{pmatrix}\alpha_X(x_d)&\partial x_d/\partial x_d\\[2pt]0&\varepsilon_Y(x_d)\end{pmatrix},
  \qquad \Phi(w)=\begin{pmatrix}X^{|w|}&S(w)\\0&Y^{\operatorname{len}w}\end{pmatrix}$$
(this is the transpose of the kernel's $M(w)$; the "$1$" off-diagonal is Fox's $\partial x_d/\partial x_d=1$,
eq. (2.1), and the product accumulates $\sum_p\alpha_X(\text{prefix})\cdot 1\cdot\varepsilon_Y(\text{suffix})$).

| our object | Fox object | status |
|---|---|---|
| cocycle $S(w)$ | total Fox derivative $\sum_d\partial w/\partial x_d$ under $(\alpha_X,\varepsilon_Y)$ | **correspond — the key match** |
| per-gap $S_d(w)$ | the single Fox derivative $\partial w/\partial x_d$, evaluated | **NEW in our notation** (drafts only ever used aggregate $S$) |
| cocycle rule $S(uv)=Y^{\operatorname{len}v}S(u)+X^{|u|}S(v)$ | product rule (1.2): $Du\cdot v^o+u\cdot Dv$, with $v^o=Y^{\operatorname{len}v}$, $u\!\cdot=\!X^{|u|}$ | **correspond exactly** |
| transfer matrix $M(w)$ | rank-1 Magnus matrix $\Phi(w)$ (graph of the crossed hom) | correspond (transpose convention) |
| $D(w)=X^{|w|}-Y^{\operatorname{len}w}$ | the value $\alpha_X(w)-\varepsilon_Y(w)=$ "$w-1$" in the twisted module | correspond |
| core $C(u,v)=D(u)S(v)-D(v)S(u)$ | derivative of a **commutator** (4.9): $D_j([u,v])=(1-uvu^{-1})D_ju+u(1-vu^{-1}v^{-1})D_jv$ | correspond (cup product = quadratic layer) |
| reversal $w^R$ | the inverse rule (1.6) $D(g^{-1})=-g^{-1}Dg$ | **MISMATCH** (no inverses; reversal=transpose, not antipode) |

**Mismatches, stated honestly.**
1. **Free monoid, not free group.** We have **no letter inverses**, so Fox's inverse rule (1.6) and
   free cancellation are *unavailable*. The fundamental formula (2.3), product rule (1.5), power rule
   (2.4), chain rule (2.6) **need no inverses** and all carry over verbatim; only the
   group-completion moves do not. The naive substitute for $g\mapsto g^{-1}$ is reversal $w^R$, and
   reversal $=$ **transpose**, not antipode (verified F9; matches L1·1 RE-3 / P4 Gen-8). *This is
   exactly why our reduction system is one-sided — i.e. a monoid rewriting system — which is why the
   right next tools are L1·3 Gröbner–Shirshov (monoid algebras) and L1·4 Squier (monoid rewriting),
   not group theory.*
2. **Infinite gap alphabet.** $\{x_d:d\in\mathbb N_{\gt0}\}$ is infinite — **no obstruction for Fox**
   (he permits non-enumerable $J$). The rank-1 abelianization $\alpha_X:x_d\mapsto X^{d}$ collapses
   the infinite alphabet onto the single one-parameter family $X^{d}$; that collapse is where the
   informative (rank-$\ge2$) content is lost, and is the *same* rank-1 degeneration flagged in L1·1.
   For L1·3 it means the monoid algebra has $\infty$-many generators but a **1-parameter grading**:
   leading terms are ordered by the bigraded weight $(|{\cdot}|,\operatorname{len})$.
3. **$\chi$-balance = equal abelianized weight.** Our rigidity $\chi(M)=\chi(M')\iff|M|=|M'|$ **and**
   $\operatorname{len}M=\operatorname{len}M'$ is exactly "$M,M'$ have equal image under the bigrading
   $(\alpha_X,\varepsilon_Y)$", which is the condition under which an unvaried slot's Fox-derivative
   term cancels in a difference (see §4).

---

## 3. The fundamental formula in our rep (the new, load-bearing relation)

Apply Fox's fundamental formula (2.3) $\,w-1=\sum_j(\partial w/\partial x_j)(x_j-1)\,$ in the twisted
module where "$w-1$" reads $\alpha_X(w)-\varepsilon_Y(w)=X^{|w|}-Y^{\operatorname{len}w}=D(w)$ and the
atom $x_d-1$ reads $X^{d}-Y=D\big((d)\big)$ (the $D$ of a *single letter* $d$). The result, **proven
and verified (F3) as a $\mathbb Z[X,Y]$ identity**:
$$\boxed{\ D(w)\ =\ \sum_{d\ge1} S_d(w)\,(X^{d}-Y)\ }\qquad\bigl(\text{Y=1 slice: } X^{|w|}-1=\textstyle\sum_d\alpha_X(\partial w/\partial x_d)(X^{d}-1)\bigr).$$
This is the **canonical decomposition of the cycle-ideal generator $D$** over the per-letter atoms
$(X^{d}-Y)$, weighted by the genuine Fox derivatives $S_d$. It telescopes: $\sum_p X^{e_p}Y^{n-1-p}(X^{d_p}-Y)
=\sum_p\big(X^{e_{p+1}}Y^{n-1-p}-X^{e_p}Y^{n-p}\big)=X^{|w|}-Y^{n}$.

**Why this is the engine for $\mathcal I_D$.** The target object is $\mathcal I_D=\ker(\bar S:\text{word
combos}\to R/\langle D\rangle)$. The fundamental formula says: in $R/\langle D\rangle$ the single relation
$\sum_d S_d(w)(X^d-Y)\equiv0$ holds for **every** word $w$; equivalently $S=\sum_d S_d$ splits the cocycle
into per-gap pieces tied together by the atoms $X^d-Y$. A **reduction** is a length-decreasing combination
$\sum_i c_i\,w_i$ with $\sum_i c_i S(w_i)\in\langle D\rangle$; the fundamental formula is precisely the
*membership certificate generator* — it expresses each $D$-multiple over the atoms, so any move whose
$S$-difference is a unit times $D$ (or a core $C$, itself a $D$-bilinear, eq. (4.9)) is witnessed
explicitly. The drafts had the moves; Fox supplies the **uniform reason they land in $\mathcal I_D$**.

---

## 4. P0/P1/P2/P3 as Fox identities — and the unified generator

**The single generator** is the **abelianized multi-factor product rule (1.5)**: for any slot
decomposition $w=A_1\cdots A_m$,
$$\boxed{\ S(A_1\cdots A_m)=\sum_{i=1}^{m}X^{\,|A_1\cdots A_{i-1}|}\,Y^{\operatorname{len}(A_{i+1}\cdots A_m)}\,S(A_i)\ }\tag{$\star$}$$
(verified F4). Every move is the **difference of two instances of $(\star)$ over a common slot
decomposition**, in which the *unvaried* slots' $S$-terms cancel because their $(\alpha_X,\varepsilon_Y)$
prefactors match, and the *varied* slot survives times a unit frame. Concretely:

- **P2/P3 — shared-frame** ($w=PMQ$ vs $PM'Q$, vary the middle slot). $(\star)$ at the cut points gives
  the **general slot-difference identity** (verified F7):
  $$S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}\big(S(M)-S(M')\big)+X^{|P|}\big(X^{|M|}-X^{|M'|}\big)S(Q)+Y^{\operatorname{len}Q}\big(Y^{\operatorname{len}M}-Y^{\operatorname{len}M'}\big)S(P).$$
  Under the balance $\chi(M)=\chi(M')$ the last two terms vanish (equal $\alpha_X,\varepsilon_Y$ weights),
  leaving $\,S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}(S(M)-S(M'))\,$ — **the bounded-defect-lever
  engine, exactly.** The unit frame $X^{|P|}Y^{\operatorname{len}Q}=\alpha_X(P)\,\varepsilon_Y(Q)$ is the
  Fox product-rule prefactor (left-multiply by $P$, right-retract $Q$).
- **P1 — inner-core** (vary the *outer* blocks, share the *inner* core $u$). Expanding $S(xuy),S(x'uy')$
  by $(\star)$ in $\chi$-form, $\chi(x')S(xuy)-\chi(x)S(x'uy')$ has the **shared-core term
  $\chi(x)\chi(x')S(u)$ identical in both, hence cancelling**, leaving
  $[\chi(x')S(x)-\chi(x)S(x')]+\chi(x)\chi(x')\chi(u)[S(y)-S(y')]$ (verified F6). In Fox terms: the
  core's own Fox derivative $\partial u/\partial x_d$ enters *both* terms identically and drops; $u$
  survives only through its abelianization $\chi(u)=\alpha_X,\varepsilon_Y(u)$ — never through its
  internal structure. That is **why $u$ cannot be deleted unless $\chi(u)=1$** (the recovered
  Move-2 obstruction), now read off the product rule.
- **P0 — telescoping** ($w^qw'$ vs $w^{q-1}w'w$) is the **power rule (2.4)**. The geometric series
  $\partial w^{q}/\partial w=1+w+\cdots+w^{q-1}$ is the telescoping; combined with the antisymmetry core
  $C(w,w')=D(w)S(w')-D(w')S(w)$ it gives $S(w^qw')-S(w^{q-1}w'w)=X^{(q-1)|w|}C(w,w')$ (verified F5). The
  prefactor $X^{(q-1)|w|}=\alpha_X(w^{q-1})$ is again a product-rule unit frame.
- **Chain rule (2.6) — block-coarsening.** $\Phi$ is a monoid hom on the free monoid of gap-**blocks**:
  $\Phi(B)=\big(\begin{smallmatrix}X^{|B|}&S(B)\\0&Y^{\operatorname{len}B}\end{smallmatrix}\big)$, so
  $\Phi(B_0B_1\cdots)=\prod\Phi(B_i)$ (verified F8). Hence **every move is granularity-independent**:
  treat any gap-block as one super-letter and the whole calculus (P0–P3) applies at the coarser level.
  This systematically generalizes P0 from a single repeated *letter*-power $w^q$ to *any* repeated
  block, and is the precise content needed to choose a generating set / leading-term order in L1·3.

**Verdict on "new move vs. unification" (the deliverable, stated explicitly).**
*No new length-reducing $S$-difference identity is generated*: P0–P3 are **all** the difference-of-$(\star)$
instances, and Fox supplies **no way past the obstruction** $\chi(u)=1$ (inner cores) or
reversal$=$transpose (no inverse rule (1.6)). What Fox *does* give is **(a)** the **unification** of
P0–P3 into the one generator $(\star)$ (slot-difference of the product rule; P0 = its power-rule case,
P1/P2/P3 = its balanced cases for inner/outer/frame slots), and **(b)** two new objects in our notation
— the **per-gap splitting $S=\sum_d S_d$** and the **fundamental formula $D=\sum_d S_d(X^d-Y)$** — which
together are the systematic **generator of $\mathcal I_D$** that L1·3/L1·4 consume. This is the honest
"systematize, don't add", with the precise obstruction it leaves for Squier (next).

---

## 5. Verification — `checks/lit_fox_calculus.py` (exit 0, all 14 PASS)

Battery: 126 words (120 random, lengths $1\le n\le7$, gaps $1\le d\le6$, seed fixed) + 6 hand words;
random factorizations/frames for the move checks. All identities are checked as **$\mathbb Z[X,Y]$
symbolic identities** (strongest possible), not merely at $(2,3)$. Robust kernel-path insertion (runs
from repo root or anywhere; confirmed from `/tmp`).

| Check | Claim | Result |
|---|---|---|
| F1 | $S=\sum_d S_d$; $S_d=(\alpha_X,\varepsilon_Y)$-eval of $\partial w/\partial x_d$ | PASS |
| F2 | $S|_{Y=1}=\sum_d\alpha_X(\partial w/\partial x_d)$ (S = total Fox deriv) | PASS |
| F3 | **fundamental formula** $D(w)=\sum_d S_d(w)(X^d-Y)$ (+ $Y{=}1$ slice) | PASS |
| F4 | rank-1 Magnus $\Phi$ hom, $\Phi_{12}=S$; product rule (1.5) multi-factor | PASS |
| F5 | P0 telescoping $=$ power rule (2.4) | PASS |
| F6 | P1 inner-core (shared core cancels) | PASS |
| F7 | generator $(\star)$: general + balanced slot-difference (P2/P3) | PASS |
| F8 | chain rule (2.6): $\Phi$ hom on gap-blocks; coarse P0 | PASS |
| F9 | reversal $\ne$ antipode (no inverse rule (1.6); 108 witnesses, equal-letter ctrl monomial) | PASS |

---

## 6. Proposed structure (what to build; how L1·3/L1·4 consume it)

**The object to build is the "Fox presentation of $\mathcal I_D$":**
1. **Generators / atoms.** The per-letter atoms $a_d:=X^{d}-Y=D((d))$ and the per-gap cocycles $S_d$,
   tied by the fundamental relation $D(w)=\sum_d S_d(w)\,a_d$. Working in $R/\langle D\rangle$, this is
   the binomial/lattice presentation L1·3 wants: $\bar S(w)=\sum_d \bar S_d(w)$ with one relation per word.
2. **The single rewriting rule (the generator $(\star)$).** Slot-difference: replace a slot filler $M$
   by any $M'$ with $\chi(M)=\chi(M')$ at cost a unit frame $X^{|P|}Y^{\operatorname{len}Q}$. P0–P3 are
   its instances; block-coarsening (chain rule) makes it scale-free. This is the one production rule the
   confluence analysis runs on.
3. **For L1·3 (Gröbner–Shirshov).** Present $S(w)\equiv S(w')\ (\mathrm{mod}\ D)$ as the binomial ideal
   generated by the balanced slot-swaps $PMQ\!\to\!PM'Q$ ($\chi(M)=\chi(M')$); the bigraded weight
   $(|{\cdot}|,\operatorname{len})$ is the admissible order; normal forms are the $\chi$-reduced short
   words. The fundamental formula §3 supplies the membership certificates. *Open input for L1·3: is the
   balanced slot-swap rule a finite Gröbner–Shirshov basis, and what are the normal forms?*
4. **For L1·4 (Squier).** The **critical pairs** of $(\star)$ are exactly our two known obstructions:
   the inner-core $\chi(u)=1$ failure (a critical pair where a core cannot be deleted) and
   reversal$=$transpose (the missing inverse rule (1.6) — a *one-sided* monoid, so the
   left/right confluence is genuinely asymmetric). Squier's homology should test whether **C8/Plücker
   + reversal=transpose are the complete obstruction set**. The Fox commutator-derivative (4.9)
   $D_j([u,v])\in\Re$ and the fundamental-ideal filtration $\mathfrak G\supset\mathfrak G^2\supset\cdots$
   (§4; (4.1): $f\in\mathfrak X^n$ iff all derivatives of order $\lt n$ vanish at $1$) are the natural
   home for the cores $C(u,v)$ as the **quadratic (degree-2) layer** — the bridge to L1·5
   (holonomy/cup products).

**Keep / record.** Name $S_d$ the per-gap Fox cocycles and $S=\sum_d S_d$ the total derivative; record
the fundamental formula $D=\sum_d S_d(X^d-Y)$ as the canonical $\mathcal I_D$-membership identity; treat
$(\star)$ as THE move generator. Do **not** reopen the inverse/reversal route (Fox names it the *absent*
rule (1.6), confirming L1·1 RE-3).

---

## 7. Open questions / probes (feeding L1·3 / L1·4)

- [ ] **(L1·3)** Is the balanced slot-swap rule $PMQ\to PM'Q$ ($\chi(M)=\chi(M')$) a **finite,
      confluent** Gröbner–Shirshov basis for $\mathcal I_D$ under the $(|{\cdot}|,\operatorname{len})$
      order, and are its normal forms the $\chi$-reduced short words ("shorter words $\Rightarrow$
      smaller $S$")? The infinite gap alphabet (collapsed to the $X^d$ grading) may force an
      *infinite* basis — does block-coarsening (chain rule (2.6)) tame it to finitely many block-types?
- [ ] **(L1·4)** Are the two critical pairs of $(\star)$ — inner-core $\chi(u)=1$ and the missing
      inverse rule (reversal=transpose) — the **complete** Squier obstruction set, or is there a third
      homology class (the C8/Plücker relation among cores)? I.e. does the holonomy quadratic relation
      sit as a genuine 3-cell?
- [ ] **(cores)** Does the commutator-derivative (4.9) $D_j([u,v])$ give a Fox-native formula for
      $C(u,v)$ that makes the cores a *module over the lower-central filtration* §4 — and hence a
      **multiplicativity / telescoping law for $\operatorname{sixfree}(C)$** under arc concatenation
      that the current P0–P3 miss? (This is the L1·5 hand-off.)
- [ ] **(higher Fox)** Fox's Taylor-with-remainder (3.3) expands $D(w)$ to all orders in the atoms
      $(X^d-Y)$. Does the *second-order* term ($\sum_{j,k}D_{jk}(\cdot)(x_j-1)(x_k-1)$) give a finer
      invariant than $D$ that the bounded-defect lever does not yet exploit — or does rank-1 collapse it
      (cf. L1·1's rank-$\ge2$ ceiling)?

---

## 8. Verdict for the roadmap

Fox calculus (L1·2) is the **systematic generator** the roadmap asked for. It **unifies** P0/P1/P2/P3
into the one slot-difference identity $(\star)$ (product rule), exhibits $S$ as the
$(\alpha_X,\varepsilon_Y)$-twisted total Fox derivative with the **new per-gap splitting** $S=\sum_d S_d$,
and — the headline — realizes the **cycle-ideal generator** via the fundamental formula
$D(w)=\sum_d S_d(w)(X^d-Y)$, the canonical $\mathcal I_D$-membership identity. It generates **no new
length-reducing move** (the $\chi(u)=1$ and reversal=transpose obstructions persist, the latter named by
Fox as the *absent* inverse rule (1.6) — confirming the free-monoid, one-sided nature), but it hands
L1·3 a binomial/lattice presentation with an admissible order and L1·4 a single production rule whose
two critical pairs are exactly our known obstructions. Honest yield: **the engine, not a new lever.**
