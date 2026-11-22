# Leverage R2·2 (the decisive door): Boden–Friedl metabelian twisted Alexander polynomials — the GO/NO-GO for the non-abelian twist

**Promise:** high (as a *decision* — it closes the single live R2 door inside $(2,3)$).
R2·2 reads the real Boden–Friedl IV paper against STRUCTURE §0 (the integer cyclic quotient,
expansion-reduction), §2 (the Crowell module, $\Delta_1=\gcd(T,S)$, the root $X^E/Y^o$, $\mathfrak m$),
§3 (the cores), the L1·9 verdict (the cycle Alexander polynomial $\Delta=X^E-Y^o t$ is degree-1 and
never cyclotomic), and the R2·1 McMullen pivot (a constructively small $M=1$ slice **requires** a
2-dimensional Newton polytope; every rank-1-derived enrichment is a binomial $\Rightarrow$ segment).
It decides: does a **non-abelian metabelian** twisted Alexander polynomial $\Delta_\rho$ of our cocycle
acquire a genuine 2-dim Newton polytope (**GO** — a vertex-isolating unit slice, a constructively small
orbit residue) or collapse back to a binomial / segment (**NO-GO**)?

**Verdict (verified, 18/18 on the kernel): decisive NO-GO.** Every metabelian twisted Alexander
polynomial available to our cycle is a **binomial**
$$\boxed{\,\Delta_\rho(t)=X^{En}-c_\chi\,Y^{on}\,t^{n},\qquad |c_\chi|=1\,}$$
whose Newton polytope is a **segment** (dim $1$) with **no $M=1$ slice**. The structural reason is
two-fold and rigid: **(a)** our base Alexander polynomial $\Delta=X^E-Y^o t$ is **degree-1 (fibered:
leading coefficient $-Y^o$ a unit)**, and **(b)** Boden–Friedl's irreducible metabelian rep is a
**weighted cyclic-shift (monomial $n$-cycle) matrix**, whose characteristic polynomial is *always* a
binomial $\lambda^n-(\text{cycle product})\,\mu^n$. The metabelian character $\chi$ — the
"non-abelianness" — enters **only as the scalar cycle-product coefficient $c_\chi$** (a $G(w^n)$-th
root of unity); it carries **no $(X,Y)$-weight**, so it can change a coefficient but **cannot move any
monomial off the line** $\{(E(n{-}k),ok,k)\}$. This closes the **Layer-1 $(2,3)$-algebra**: there is no
constructively small residue from any abelian, metabelian, induced, tensor, or orbit-twisted Alexander
polynomial. Exclusion is **purely Layer-2**.

**Leveraged for / deepens:** the R2·1 McMullen polytope-dimension requirement (`lit-mcmullen-norm.md`,
McM-4 — this supplies the missing "does the non-abelian twist escape?" with a definitive NO), the L1·9
binomial-never-cyclotomic floor (`lit-silver-williams.md`, R-SW3/Q4 — now *fully* decided), and the R1
$\Delta_1=1$ / which-module analysis (`lit-alexander-module.md`).

**Status:** read in full (all 21 pp.: §1 intro + Wada's question, §2.1 Wada's definition + Lemmas 4–7,
§3.1 the metabelian classification $\alpha_{(n,\chi)}$ + Prop 8, §3.2 tensor products Prop 9, §4 Wada's
question, §5 the Hirasawa–Murasugi proofs Prop 12 / Lemma 15 / Prop 16). Dictionary built; verdict
verified (`checks/lit_boden_friedl.py`, 18/18, exit 0). **Last iterated:** 2026-06-09.

---

## Source (real, complete; identity confirmed)

H. U. Boden & S. Friedl, *Metabelian $\mathrm{SL}(n,\mathbb C)$ representations of knot groups IV:
twisted Alexander polynomials*, arXiv:1209.4244v1 (19 Sep 2012) —
[`sources/boden-friedl-metabelian-IV-1209.4244.pdf`](../sources/boden-friedl-metabelian-IV-1209.4244.pdf)
(21 pp., read in full). Cited results:

- **§2.1 (Wada's definition).** For $\pi_K=\langle g_1,\dots,g_{k+1}\mid r_1,\dots,r_k\rangle$
  (deficiency one), $\phi:\pi_K\to\mathbb Z$ (meridian $\mapsto1$), $\alpha:\pi_K\to\operatorname{Aut}(V)$
  over a UFD $R$, $M=(\partial r_i/\partial g_j)$ the Fox Jacobian and $M_i$ its column-$i$ deletion:
  $$\Delta_K^\alpha(t)=\det\big((\alpha\otimes\phi)(M_i)\big)\cdot\det\big((\alpha\otimes\phi)(1-g_i)\big)^{-1}\in Q(t).$$
- **Lemma 5(2).** A $1$-dim character $\tau$ (meridian $\mapsto z$): $\Delta_K^\tau(t)\doteq\Delta_K(tz)/(1-tz)$
  — an **abelian twist only rescales** $t\mapsto tz$.
- **Lemma 5(4).** Block-triangular $\alpha=\big(\begin{smallmatrix}\beta&\gamma\\0&\delta\end{smallmatrix}\big)
  \Rightarrow\Delta_K^\alpha\doteq\Delta_K^\beta\cdot\Delta_K^\delta$ (**Wada multiplicativity**).
- **§3.1 (the classification recipe, from [BF08]).** Let $H=H_1(X_K;\mathbb Z[t^{\pm1}])$ be the
  Alexander module; $\pi/\pi^{(2)}\cong\mathbb Z\ltimes H$ ($n\in\mathbb Z$ acts by $t^n$). For a character
  $\chi:H\to\mathbb C^\ast$ **factoring through $H/(t^n-1)$** and $z\in U(1)$,
  $$\alpha_{(n,\chi,z)}(j,h)=\Big(z\cdot\mathrm{SHIFT}\Big)^{\!j}\cdot
    \operatorname{diag}\!\big(\chi(h),\chi(th),\dots,\chi(t^{n-1}h)\big)$$
  defines a $\mathrm{GL}(n,\mathbb C)$ rep (an $\mathrm{SL}(n)$ rep when $z^n=(-1)^{n+1}$); **every
  irreducible metabelian $\mathrm{SL}(n,\mathbb C)$ rep is some $\alpha_{(n,\chi)}$.** The monodromy
  (meridian image) is a **weighted cyclic-shift = monomial $n$-cycle matrix.**
- **Prop 8.** For irreducible metabelian $\alpha$, $n\gt1$: $\Delta_K^\alpha(t)$ is a **polynomial in $t^n$**.
- **Prop 9.** $\alpha_{(k_1,\chi_1)}\otimes\alpha_{(k_2,\chi_2)}\cong\alpha_{(k_1k_2,\chi_1\chi_2)}$
  ($k_1,k_2$ coprime).
- **§5 (Prop 12 / Lemma 15 / Prop 16).** The regular rep decomposes $\gamma=\gamma_0\oplus\dots\oplus\gamma_\ell$
  and $\Delta_K^{\gamma\circ\alpha}(t)=\prod_i\Delta_K^{\gamma_i\circ\alpha}(t)=\frac{\Delta_K(t)}{1-t}F(t)$,
  $F\in\mathbb Z[t^n]$ — the metabelian pieces collect into a polynomial in $t^n$ (the multi-term object).

---

## §Dictionary — Boden–Friedl $\leftrightarrow$ ours (with the load-bearing mismatch)

Write $w$ a gap word, $E=|w|$ even steps, $o=\operatorname{len}w$ odd steps; $H=\langle X,Y\rangle\cong
\mathbb Z^2$ ($X\leftrightarrow2,Y\leftrightarrow3$); $\mathfrak m=\langle X-1,Y-1\rangle$;
cycle/period Alexander polynomial $\Delta(t)=X^E-Y^o t$; $G(w^n)=|D(w^n)|=|2^{En}-3^{on}|$.

| Boden–Friedl | Ours | Status |
|---|---|---|
| Alexander module $H=H_1(X_K;\mathbb Z[t^{\pm1}])$ | the **cyclic-cover (period) module** $H=\mathbb Z[t^{\pm1}]/(X^E-Y^o t)$, the L1·9 module | exact (the **right** module) |
| $\chi:H\to\mathbb C^\ast$ factoring through $H/(t^n-1)\cong H_1(L_n)$ (the torsion point / eigenvalue) | a character of $H/(t^n-1)=\mathbb Z/G(w^n)=\mathbb Z/|2^{En}-3^{on}|$ (a $G(w^n)$-th root of unity) | exact; **cyclic, finite, nontrivial** |
| degeneration: $\Delta_\rho$ degenerates iff $\Delta$ has an $n$-th-root-of-unity root | $\Delta$'s only root is $t=X^E/Y^o=2^E/3^o$, **never** a root of unity ($2^E\ne3^o$) | exact; $\Rightarrow$ **non-degenerate**, reps abundant |
| irreducible metabelian $\alpha_{(n,\chi)}=(z\cdot\text{shift})^j\operatorname{diag}(\chi(t^ih))$ | a **weighted $n$-cycle monodromy** $R_\chi=\text{shift}\cdot\operatorname{diag}(g_0,\dots,g_{n-1})$, $g_i$ roots of unity | exact |
| Prop 8: $\Delta_K^\alpha\in\mathbb C[t^{\pm1}]$ a polynomial in $t^n$ | $\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$ — a polynomial in $t^n$ that is a **binomial** | exact, **but binomial** |
| Lemma 5(2) abelian twist $\Delta_K(tz)/(1-tz)$ | rescaling $X^E-Y^o t\mapsto X^E-Y^o(zt)$ — stays a binomial | exact |
| Lemma 5(4) Wada multiplicativity / Prop 9 tensor | product / single binomial — **collinear** | exact |

**The two load-bearing facts.**
1. **The metabelian rep is a weighted $n$-cycle, so its characteristic polynomial is *structurally*
   binomial.** A single monomial $n$-cycle $R$ satisfies $R^n=(\prod_i g_i)\,I$, so
   $\det(\lambda I-\mu R)=\lambda^n-(\prod_i g_i)\mu^n$ — *only* the top and bottom powers survive
   (all "middle" terms vanish because a single cycle has no shorter sub-cycle). With $\lambda=X^E$,
   $\mu=Y^o t$, this is $\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$, $c_\chi=z^n\prod_i g_i$. **Our cocycle is
   fibered** ($\Delta$ monic in $t$, leading coeff $-Y^o$ a unit), so the twisted Alexander polynomial
   *equals* this characteristic polynomial.
2. **The character $\chi$ carries no $(X,Y)$-weight.** The $(X,Y)$-grading comes only from the
   abelianization $\psi:W\to\langle X,Y\rangle$ (the $X^E,Y^o$ in the Magnus block); the rep entries
   $g_i,z$ are **roots of unity (scalars)**, contributing only to the coefficient $c_\chi$ (with
   $|c_\chi|=1$). So $\chi$ can zero/rotate a coefficient but **cannot create a monomial in a new
   lattice direction.** This is *exactly why* the non-abelian twist cannot escape the segment — the
   precise refutation of the door McMullen (McM-4) left open.

**MISMATCH (honest).** A knot group abelianizes to $\mathbb Z$ (rank 1, a single meridian $\phi$); our
free monoid abelianizes to $H=\mathbb Z^2$ (rank 2), and the metabelian construction $\mathbb Z\ltimes H$
needs a distinguished $\mathbb Z$ (the meridian). We take that $\mathbb Z$ to be the **period /
cyclic-cover direction** ($\mu=$ "advance one full period $w$", $\phi(\mu)=1$), with module $H$ the
period module — exactly the Silver–Williams cyclic-cover picture (R-SW3). The "$t$" of the twisted
polynomial is this period variable; the Newton polytope lives in $(X,Y,t)$, consistent with the
McMullen check. The within-stratum Crowell module ($\Delta_1=\gcd(T,S)=1$, R1) is the *wrong* module
(trivial by per-stratum injectivity); the right one is the **binomial** period module — which is the
root of the NO-GO.

---

## §What metabelian reps we admit (the $\Delta_1=1$ / root-of-unity analysis)

The brief's two candidate modules, resolved:

- **Not the Crowell module.** $\Delta_1=\gcd(T,S)=\mathbf 1$ for primitive shapes (R1): the within-stratum
  Alexander polynomial is a unit, so $H/(t^n-1)$ for *that* module is trivial — **no metabelian reps
  there.** This is the per-stratum injectivity of $S$ ($\Phi$ faithful): inside one stratum there is no
  torsion to build a character from. (For imprimitive $w=u^k$, $\Delta_1$ is the period factor — only the
  period gives torsion, and it reduces to the root $u$.)
- **Yes the cyclic-cover (period) module.** The metabelian construction lives on
  $H=\mathbb Z[t^{\pm1}]/(X^E-Y^o t)$, whose $n$-cover quotient is
  $$H/(t^n-1)=\mathbb Z[t^{\pm1}]/(X^E-Y^o t,\ t^n-1)\;\cong\;\mathbb Z/\big|\mathrm{Res}(t^n-1,X^E-Y^o t)\big|
    =\mathbb Z/\big|2^{En}-3^{on}\big|=\mathbb Z/G(w^n),$$
  a **nontrivial finite cyclic group**. Its characters are the $G(w^n)$-th roots of unity — **so
  metabelian reps $\alpha_{(n,\chi)}$ are abundant** for our cycle (one for each $n\ge1$ and each
  character of $\mathbb Z/G(w^n)$). [Verified PART A.]
- **The degeneration criterion is *not* triggered — but it doesn't help.** Boden–Friedl/Hirasawa–Murasugi
  degeneration: $\Delta_\rho$ degenerates iff $\Delta$ has a root that is an $n$-th root of unity. Our
  $\Delta=X^E-Y^o t$ has its single root at $t=2^E/3^o$, which is **never** a root of unity (and not even
  on the unit circle, $|2^E/3^o|\ne1$). So $H/(t^n-1)$ is **always finite**, the reps are **non-degenerate**,
  and $\Delta_\rho$ is a genuine nonzero binomial — *abundant and non-degenerate, yet still a segment.*
  **The root-never-a-root-of-unity fact guarantees existence; the degree-1 fact guarantees binomiality.**
  These are the two structural pins.

---

## §$\Delta_\rho$ + Newton polytope (the computation, in our notation)

**Abelian control (the $C_n$-regular / DFT twist — pre-settled NO).** The regular representation of the
deck group $\mathbb Z/n$ is the **unweighted** shift; its twisted polynomial is the DFT product, which is
the Silver–Williams resultant:
$$\prod_{j=0}^{n-1}\big(X^E-Y^o\omega^j t\big)=\operatorname{Res}_\zeta\big(\zeta^n-1,\ X^E-Y^o t\,\zeta\big)
  =X^{En}-Y^{on}t^{n},\qquad\omega=e^{2\pi i/n}.$$
A **binomial** (Newton polytope a segment), and $2^{En}\ne3^{on}$ (no $M=1$). [Verified PART B.]

**Non-abelian metabelian (the real test).** Replace the unweighted shift by the Boden–Friedl weighted
shift $R_\chi=\mathrm{SHIFT}\cdot\operatorname{diag}(g_0,\dots,g_{n-1})$ ($g_i=\chi(t^ih_0)$ roots of
unity). Because our cocycle is fibered, the metabelian twisted Alexander polynomial is the
characteristic polynomial of the twisted monodromy:
$$\Delta_\rho(t)=\det\!\big(X^E I_n-Y^o t\,R_\chi\big)=X^{En}-c_\chi\,Y^{on}\,t^{n},\qquad
  c_\chi=z^n\!\prod_{i=0}^{n-1}g_i,\ \ |c_\chi|=1.$$
This is a **binomial in $(X,Y,t)$** — support $\{(En,0,0),(0,on,n)\}$, **Newton polytope a segment
(dim $1$)** — for **every** $(n,\chi)$. [Verified PART C symbolic mechanism, PART D the discriminant over
a 27-rep battery: every $\dim N(\Delta_\rho)=1$.] The "non-abelianness" lives entirely in the scalar
$c_\chi$, which leaves the polytope and the Mahler measure $\max(2^{En},3^{on})$ unchanged.

**No $M=1$ slice (the McMullen dichotomy persists).** Every $\phi$ gives either a binomial slice
$s^a-s^b$ (never a unit) or a vanishing slice (the two monomials collide, $b_1=\infty$); **no direction
isolates a single monomial.** [Verified PART E.]

**The escape routes are closed too.** (i) Wada multiplicativity (Lemma 5(4)) / direct sum gives a
**product** of metabelian binomials $\prod_k(X^E-Y^o\omega_k t)$, all collinear in direction $(-E,o,1)$
$\Rightarrow$ still a segment. (ii) Tensor product (Prop 9) is again a single $\alpha_{(k_1k_2,\chi_1\chi_2)}$
$\Rightarrow$ one binomial. (iii) The **within-orbit** weighted shift (the transfer law multiplier
$Y/X^{d_j}$ around the $o$-cycle) has characteristic polynomial $X^E\lambda^o-Y^o$ — a binomial **even
though the weights $Y/X^{d_j}$ individually carry $(X,Y)$-weight**, because a single cycle's determinant
sees only the cycle product $\prod_j Y/X^{d_j}=Y^o/X^E$ (one monomial). [Verified PART F.]

**New?** The construction-and-collapse is **new** (no metabelian/non-abelian twist was previously built
or refuted in our objects; it is the decisive completion of McM-4). **Translatable?** yes — entirely in
$X,Y,t,\Delta,G(w^n)$, the weighted $n$-cycle monodromy, and the Newton polytope.

---

## §Verification (`checks/lit_boden_friedl.py`, 18/18, exit 0)

Self-contained from repo root; imports the real kernel `from cocycle import X, Y, S, D, rotations`.
**Reuses the Newton-polytope machinery** (`affine_dim`, `support`, `poly_support`, `width`,
`mcmullen_slice`) verbatim from `checks/lit_mcmullen_norm.py`.

- **PART A — which reps we admit.** root $2^E/3^o$ never a root of unity ($2^{En}\ne3^{on}$, $1\le n\le7$)
  $\Rightarrow H/(t^n-1)$ finite; $|H/(t^n-1)|=|\mathrm{Res}(t^n-1,\Delta)|=|2^{En}-3^{on}|=G(w^n)$ (cyclic);
  $G(w^n)\ge1$ $\Rightarrow$ metabelian characters exist. ✓
- **PART B — abelian control.** DFT product $=\mathrm{Res}(\zeta^n-1,X^E-Y^o t\zeta)=X^{En}-Y^{on}t^n$
  (symbolic, exact) + numeric corroboration ($n\le9$, random $\mathbb C$); binomial $\Rightarrow$ segment
  (dim 1); $2^{En}\ne3^{on}$. ✓
- **PART C — the structural mechanism.** $\det(\lambda I-\mu\cdot\text{weighted-}n\text{-cycle})=
  \lambda^n-(\prod g_i)\mu^n$ (symbolic, $n\le7$); $R_\chi^n=(\prod g_i)I$ (the cyclic collapse). ✓
- **PART D — the metabelian $\Delta_\rho$ + discriminant.** symbolic $\Delta_\rho=X^{En}-(\prod g_i)Y^{on}t^n$;
  explicit BF reps ($\chi$ a character of $\mathbb Z/G(w^n)$, concrete roots of unity) $\Rightarrow$ binomial,
  $|c_\chi|=1$; **the discriminant: $\dim N(\Delta_\rho)=1$ for all 27 reps in the battery.** ✓
- **PART E — no unit slice.** no $\phi$ gives a single-monomial slice; width-$0$ directions vanish;
  Mahler $\max(2^{En},3^{on})\gt1$. ✓
- **PART F — escape routes closed.** product of metabelian binomials collinear (dim 1); tensor $=$ one
  binomial (Prop 9); within-orbit weighted $o$-cycle $\Rightarrow X^E\lambda^o-Y^o$ binomial. ✓

---

## §R2 VERDICT — decisive NO-GO (the Layer-1 $(2,3)$-algebra is exhausted)

**NO-GO.** A constructively small ($M=1$) slice requires a **2-dimensional** Newton polytope (R2·1,
McM-4). The non-abelian metabelian twist — the *single* door McMullen left open inside $(2,3)$ — does
**not** supply one: every metabelian twisted Alexander polynomial of our cycle is a **binomial**
$\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$ (a segment, dim $1$, no unit slice). The structural reason is
rigid and two-fold:

1. **The base is degree-1 (fibered).** $\Delta=X^E-Y^o t$ is monic in $t$ with unit leading coefficient,
   so the twisted Alexander polynomial is the *characteristic polynomial of the twisted monodromy*, and
   any cyclic cover of a fibered, degree-1 base stays degree-1 / binomial.
2. **The metabelian monodromy is a weighted $n$-cycle.** Boden–Friedl's $\alpha_{(n,\chi)}$ is a monomial
   $n$-cycle; the characteristic polynomial of *any* weighted $n$-cycle is the binomial
   $\lambda^n-(\text{cycle product})\mu^n$. The character $\chi$ enters **only** as the scalar cycle-product
   $c_\chi$ (a root of unity, $|c_\chi|=1$), which carries **no $(X,Y)$-weight** and therefore cannot move
   a monomial into a new lattice direction.

**What this closes.** Together with R2·1 (every *abelian* rank-1-derived enrichment is a binomial), R2·2
shows that **no representation-theoretic twist available inside the $(2,3)$-dynamics — abelian, metabelian,
induced, direct sum, tensor, period-cover, or rotation-orbit — produces a 2-dim Newton polytope.** The
Alexander norm stays a degenerate rank-$\le1$ seminorm; there is **no $M=1$ slice, no cyclotomic factor,
no constructively small orbit residue.** This **completes the Layer-1 program** in the strongest sense:
the L1 (core/algebraic) structure carries the floor $G=|2^E-3^o|$ and *only* the floor; the exclusion
content is entirely **Layer-2 arithmetic** (primitive divisors / $\operatorname{sixfree}\to\infty$ via
Bang–Zsygmondy / BHV). The two-layer thesis is now rigorously confirmed against the last live algebraic
door.

**Why a GO was impossible in principle.** GO would have required a $\Delta_\rho$ with $\ge3$ non-collinear
monomials. The only way to non-collinear support is a base $\Delta$ that is *already* 2-dimensional (a
genuine multivariable/higher-degree Alexander polynomial) — i.e. a **third multiplicatively-independent
modulus** $Z$. That is artificial in the $(2,3)$-Syracuse dynamics (no third prime is intrinsic). The
metabelian twist was the one hope to manufacture multi-term structure *without* a third modulus; it fails
because the multi-term-ness it produces (the polynomial-in-$t^n$ of Prop 8) is, for a degree-1 fibered
base, a **product of binomials in one fixed direction** — collinear.

---

## §Open questions (NO-GO branch — what is left besides Layer-2?)

- **Q1 (is anything left in Layer-1?).** R2·1 + R2·2 exhaust the *representation-theoretic* twists. The
  only formally-untried algebraic object is a **genuinely independent third modulus** $Z$ (a generalized
  $(2,3,p)$ or $2x{+}1$-type dynamics) giving $H=\mathbb Z^3$ and a non-collinear $\Delta_G$. This is
  **artificial** for $(2,3)$-Collatz and not a property of the map — recommend recording it as closed, not
  pursued. (If ever a structured family *forced* a third modulus, McMullen's failure-of-convexity template
  $D_\infty\times D_\infty$, $I(G)=\langle x^2-1,y^2-1,(x-1)(y-1)\rangle$, is the 2-dim shape to aim at.)
- **Q2 (Suciu characteristic varieties — the last R2 sanity check).** Before declaring Layer-1 closed, one
  could read Suciu's characteristic/resonance varieties of abelian covers (the $b_1(\ker\phi)$ jump loci):
  does the binomial $\Delta$ pin the characteristic variety to a single translated subtorus (confirming no
  hidden 2-dim jump)? Expected to *confirm* the NO-GO (a binomial's variety is a single hypersurface
  $\{X^E=Y^o\omega\}$), so low promise — but it is the clean "last look" before the Layer-1 closure is
  declared final.
- **Q3 (Layer-2 hand-off — the real continuation).** The metabelian period blocks are exactly the
  $\Phi_d^\ast(2^{E},3^{o})$ cyclotomic-resultant factors of L1·9 (R-SW3); $c_\chi$ being a root of unity
  means the metabelian twist redistributes but never shrinks them. The live program is **Bang–Zsygmondy /
  BHV primitive divisors** on $\Phi_d^\ast(2^E,3^o)$ ($\operatorname{sixfree}\to\infty$), the
  `bounded-defect-lever` Layer-2 attack. This is where exclusion actually lives.

**Follow-up refs worth queuing** (do not mine here): **Suciu**, *Characteristic varieties and Betti numbers
of abelian covers* (Q2, the last Layer-1 check); **Boden–Friedl II/III** ([BF11] fixed points, [BF12]
deformations) only if a deformation of $\alpha_{(n,\chi)}$ off the metabelian locus is ever wanted (low —
deformations stay in the same $\mathbb Z\ltimes H$ and inherit the binomial); for Layer-2, **Bang /
Zsygmondy** primitive-divisor and **BHV** (Bilu–Hanrot–Voutier) — already in the `bounded-defect-lever`
queue.

---

## §Proposed structure (what this closes; the fold for STRUCTURE)

1. **Fold the R2·2 NO-GO into STRUCTURE §3 / §5 as the close of the two remaining doors' *first* door.**
   "Every metabelian (non-abelian) twisted Alexander polynomial $\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$ is a
   binomial because the base $\Delta=X^E-Y^o t$ is degree-1 (fibered) and the Boden–Friedl monodromy is a
   weighted $n$-cycle whose char poly is binomial; the metabelian character contributes only the
   root-of-unity scalar $c_\chi$ (no $(X,Y)$-weight). $\Rightarrow\dim N(\Delta_\rho)=1$, no $M=1$ slice.
   With R2·1 this exhausts every representation-theoretic twist inside $(2,3)$ — **Layer-1 is closed**;
   exclusion is purely Layer-2."
2. **Record the structural lemma (weighted-cycle $\Rightarrow$ binomial) as the unifying mechanism** behind
   the abelian (DFT), metabelian, and orbit-circulant collapses: all three are single weighted cycles, all
   three give binomials. This is the representation-theoretic shadow of the L1·9 "$G$ amplifies, never shrinks."
3. **Re-aim at Layer-2** (the $\Phi_d^\ast(2^E,3^o)$ Bang–Zsygmondy blocks) as the *only* remaining home of
   exclusion, optionally after the Suciu characteristic-variety last-look (Q2).

**Promotion-readiness:** **no.** This is a decisive *closure* (NO-GO on the last live Layer-1 door) plus
the unifying weighted-cycle lemma — it finalizes STRUCTURE's two-layer thesis and retires the R2 queue
row, but produces no new excludable family. The deliverable is the honest decisive NO-GO.
