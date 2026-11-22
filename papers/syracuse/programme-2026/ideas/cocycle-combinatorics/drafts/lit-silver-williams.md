# Leverage L1·9 (Movement IV): Silver–Williams resultant / cyclic-cover homology growth — leveraged for the integer-circulant spine

**Promise:** medium. L1·9 reads the *real* Silver–Williams homology-growth paper against STRUCTURE.md
§0 (the integer cyclic quotient $A$, expansion-reduction), §2/§3, the R3 difference-ideal $J$-collapse,
and the [P3] lever / $G=\gcd_jS^{(j)}=|D|$ floor. **Decides the Movement-IV question:** does the
circulant / $\mathbb{Z}[\mathbb{Z}/o]$ arithmetic of the rotation orbit, read through the
resultant/cyclic-cover identity, **construct** a small orbit residue mod $G$ (a Fourier block below the
floor), or does it only reproduce Mahler **growth** (the Layer-2 obstruction)?

**Constructive verdict (verified, 49/49 on the kernel): NO construction — the integer circulant
*amplifies* $G$.** Every DFT component of the orbit carries the full factor $G$, so each cyclotomic
block of the circulant resultant is $\ge G^{\varphi(d)}$; the Silver–Williams resultant translates onto
the **period family** $w^r$ with a *degree-1* cycle Alexander polynomial
$\Delta(t)=X^E-Y^o t$ whose Mahler measure $M(\Delta)=\max(2^E,3^o)\gt1$ **always** (the cycle $\Delta$
is never cyclotomic, since $2^E\ne3^o$), so $G(w^r)$ grows and is never bounded/periodic. This is the
**integer-quotient avatar of R3's $J$-collapse, now sharpened**: not "collapses to $G$" but "amplifies
to $G^o$, growth rate $\log\max(2^E,3^o)$." The leverage is **not a bare null** — it imports three new
verified identities (the rotation transfer law; the circulant = resultant; the period Fox formula) and
the precise dictionary that **unifies the orbit/circulant, the R3 floor, the period factor, and the
Layer-2 Bang–Zsygmondy/Mahler obstruction under one resultant**.

**Leveraged for / deepens:** the R3 difference-ideal $J$-collapse (`lit-plucker-bracket.md`,
`checks/lit_plucker_bracket.py` PART D), the rotation-combo floor (`rotation-combo-floor.md`), the [P3]
weight bridge (`lit-suciu-wang.md`, `bounded-defect-lever.md`), and the period-factor $\Delta_1$ of
STRUCTURE §2 (R1).

**Status:** read in full (both candidate PDFs; the companion read cover-to-cover, §1 intro → §6
conclusion + refs); dictionary built; verdict verified (`checks/lit_silver_williams.py`, 49/49, exit 0).
**Last iterated:** 2026-06-09.

---

## Source (real, complete; read in full; identity CONFIRMED — and I SWITCHED papers)

The prompt's **primary** target was Silver–Williams, *Mahler measure of Alexander polynomials*
(arXiv:**math/0105234**, J. London Math. Soc. 69 (2004) 767–782). I downloaded and read it in full
(18 pp.). **It does NOT contain the resultant / cyclic-cover identity.** Its content is *Dehn-surgery
Mahler-limits*: for $l(q)$ obtained by $1/q$-surgery, $\lim_{q\to\infty}M(\Delta_{l(q)})=M(\Delta_l)$
(Thm 2.2, p.4) and $\lim\frac1qM(\Delta_{l(q)})=M[\partial_{u_d}\Delta_l|_{u_d=1}]$ (Cor 2.5). That is a
*different* growth phenomenon (a surgery limit), not the $r_m=\prod_\zeta\Delta(\zeta)$ identity.

Per the brief ("if the resultant/growth identity lives in the companion, read THAT one instead"), I
**switched to the companion**:
- **D. S. Silver and S. G. Williams, *Mahler measure, links and homology growth*, Topology 41 (2002)
  873–887, arXiv:math/0003127** —
  [`sources/silver-williams-mahler-links-homology-0003127.pdf`](../sources/silver-williams-mahler-links-homology-0003127.pdf)
  (14 pp., read in full). Both PDFs are kept in `sources/`.
- **Cited results (companion):** the Mahler measure $\mathbf M(f)=\exp\int_{\mathbf S^d}\log|f|$ and
  Jensen $\mathbf M(f)=|c_n|\prod_j\max(|r_j|,1)$ (p.2); $b_\Lambda=|TH_1(M_\Lambda)|$ = order of the
  torsion subgroup of $H_1$ of the $\Lambda$-branched cover (§2, p.3); **Theorem 2.1** (p.3):
  $\limsup_{\langle\Lambda\rangle\to\infty}\frac1{|\mathbf Z^d/\Lambda|}\log b_\Lambda=\log\mathbf M(\Delta)$
  (ordinary limit when $d=1$); **Corollary 2.2 (Gordon)** (p.3): if $\Delta_1/\Delta_2\mid t^N-1$ then
  $H_1(M_r)\cong H_1(M_{r+N})$ (periodic homology); the dynamical mechanism §3–§4 ($\mathbf Z^d$-shift
  colorings, $\mathrm{Fix}_\Lambda$, Lind–Schmidt–Ward entropy = $\log\mathbf M(\Delta)$); the based
  Alexander module $B=A/\langle\tilde x_1\rangle$ with $(N{-}1)\times(N{-}1)$ presentation $R$,
  $\Delta=(u_1-1)\det R$ (p.8); Conjecture 6.1 (zero-Alexander case, p.13). The classical $d=1$ face
  — the **Fox formula** $|H_1(M_r)|=\prod_{\zeta^r=1}|\Delta(\zeta)|=|\mathrm{Res}(t^r-1,\Delta)|$ — is
  the special case underlying Gordon [Go] that the paper generalizes to links and to Mahler growth.

I am reporting the companion as the paper read. The primary is logged as "read, identity absent."

---

## §Dictionary — their objects ↔ ours (with the load-bearing mismatches)

Write $w$ a gap word, length $o$ (odd steps), weight $E=|w|$ (gap-sum / even steps); rotation orbit
$\{w_0,\dots,w_{o-1}\}$, rotation sums $S^{(j)}=S(w_j)$; $D=X^E-Y^o$, $G=\gcd_jS^{(j)}=|D|=|2^E-3^o|$ on
a cycle; the DFT $\widehat S(\zeta)=\sum_{j=0}^{o-1}S^{(j)}\zeta^j$.

| Silver–Williams (math/0003127) | Ours | Status |
|---|---|---|
| Alexander polynomial $\Delta(u)$ (fixed) | **cycle Alexander polynomial $\Delta(t)=X^E-Y^o t$, degree 1** (PART D) | exact, but only in the **period** direction |
| $r$-fold cyclic branched cover $M_r$ | the **period word** $w^r$ ($w$ repeated $r$ times) | exact |
| $\|H_1(M_r)\|=\prod_{\zeta^r=1}\|\Delta(\zeta)\|=\|\mathrm{Res}(t^r-1,\Delta)\|$ (Fox) | $G(w^r)=\|D(w^r)\|=\mathrm{Res}(t^r-1,\,X^E-Y^o t)=\prod_{\zeta^r=1}\|2^E-\zeta3^o\|$ | exact (PART D) |
| $\frac1r\log b_r\to\log\mathbf M(\Delta)$ (Thm 2.1) | $\frac1r\log G(w^r)\to\log\max(2^E,3^o)$ | exact (PART E) |
| Gordon periodicity: $\Delta$ cyclotomic ($\mathbf M{=}1$) ⇒ $H_1(M_r)$ bounded | $\Delta=X^E-Y^o t$ cyclotomic $\iff 2^E=3^o$ — **never** ⇒ $G(w^r)$ unbounded | exact (PART E) |
| circulant $\prod_{\zeta^o=1}\widehat S(\zeta)=\mathrm{Res}(t^o-1,\widehat S)$ | $\det\operatorname{circ}(S^{(0)},\dots,S^{(o-1)})$ | exact (PART B) |
| primes dividing $\|H_1(M_r)\|$ via which $\Delta(\zeta)$ are units | primes dividing $G(w^r)$ via cyclotomic blocks $\Phi_d^*(2^E,3^o)$ (Zsygmondy) | exact (PART D) |

**The two load-bearing mismatches.**
1. **Mahler-growth = obstruction, not target.** Their headline is the *growth* $b_\Lambda\sim\mathbf
   M(\Delta)^{|\mathbf Z^d/\Lambda|}$ — a Lehmer/lower-bound phenomenon. That is exactly our **Layer-2
   obstruction** side ($G\to\infty$), *not* the constructive small-representative target.
2. **Fixed $\Delta$ + varying cover vs. co-varying $(o,\widehat S)$.** Silver–Williams fix $\Delta$ and
   grow the cover degree $r$. Our **within-orbit** circulant $\mathrm{Res}(t^o-1,\widehat S)$ has the
   modulus $t^o-1$ *and* the generating polynomial $\widehat S$ (coefficients $S^{(j)}$) **co-varying**
   with $o$ — there is *no* fixed $\Delta$ inside a single orbit. The fixed-$\Delta$ resultant exists
   only in the orthogonal **period** direction $w^r$ (PART D). This mismatch is *why* the within-orbit
   circulant carries no Silver–Williams "small block" — see PART C.

---

## §Relation extracted (in OUR notation)

Three genuinely new, kernel-verified identities, plus the honest-null structure theorem.

**(R-SW1) The rotation transfer law (the affine monodromy that makes the orbit a $\mathbb{Z}[\mathbb{Z}/o]$-module).**
$$\boxed{\,X^{d_j}\,S(w_{j+1})=Y\,S(w_j)+D(w)\,}\qquad\text{at }(2,3):\quad 2^{d_j}S^{(j+1)}=3\,S^{(j)}+(2^E-3^o),$$
where $d_j=w_j[0]$ is the first gap of the $j$-th rotation. This is the precise "shift" of
Silver–Williams' $\mathbf Z^d$-action, in our setting; it is literally the **Syracuse step** in
normalized coordinates ($S^{(j+1)}=(3S^{(j)}+D)/2^{d_j}$). The multiplier $X^{d_j}$ is
**position-dependent**, which is exactly the reason a *single* fixed $\Delta$ does not govern the
within-orbit circulant (mismatch 2).

**(R-SW2) Circulant = resultant = product over roots (the orbit residue object).**
$$\det\operatorname{circ}\!\big(S^{(0)},\dots,S^{(o-1)}\big)=\mathrm{Res}\big(t^o-1,\ \widehat S(t)\big)
   =\prod_{\zeta^o=1}\widehat S(\zeta),\qquad \widehat S(t)=\sum_{j}S^{(j)}t^j.$$
This is the precise analogue of Silver–Williams' $r_m=\prod_\zeta\Delta(\zeta)$, verified symbolically
over $\mathbb{Z}[X,Y]$ and numerically at $(2,3)$.

**(R-SW3) The period Fox formula (the fixed-$\Delta$ face — exact Silver–Williams translation).**
With $\Delta(t)=X^E-Y^o t$ (degree 1),
$$G(w^r)=|D(w^r)|=\Big|\mathrm{Res}\big(t^r-1,\ X^E-Y^o t\big)\Big|=\prod_{\zeta^r=1}\big|2^E-\zeta\,3^o\big|
   =\prod_{d\mid r}\big|\,\Phi_d^{*}(2^E,3^o)\,\big|,$$
where $\Phi_d^{*}(a,b)=b^{\varphi(d)}\Phi_d(a/b)$ is the homogenized cyclotomic. The $d=1$ block is the
base $D(w)=X^E-Y^o$; the $d\gt1$ blocks are the relative cyclic-cover homology — and this is **exactly
the period factor $\Delta_1=(X^{rE}-Y^{ro})/(X^E-Y^o)$ already noted in STRUCTURE §2 (R1)**, now
identified as $\prod_{d\mid r,\,d\gt1}\Phi_d^{*}(X^E,Y^o)$.

**(R-SW4, the honest-null structure theorem) The integer circulant AMPLIFIES $G$.** Because $G\mid
S^{(j)}$ for every $j$, every Fourier component factors $\widehat S(\zeta)=G\cdot\widehat m(\zeta)$ with
$\widehat m(\zeta)=\sum_j m_j\zeta^j$, $m_j=S^{(j)}/G$, $\gcd_j m_j=1$. Hence
$$\det\operatorname{circ}(S)=G^{\,o}\cdot\det\operatorname{circ}(m),\qquad
   \mathrm{Res}\big(\Phi_d,\widehat S\big)=G^{\,\varphi(d)}\cdot\mathrm{Res}\big(\Phi_d,\widehat m\big),$$
so **every nonzero cyclotomic block is $\ge G^{\varphi(d)}\ge G$** — no Fourier block of the orbit is a
small residue. The DFT splits the orbit lattice, but $G$ survives **uniformly in every component**. This
is an *integer-quotient* statement (the $J$-collapse of R3 was a polynomial/ideal statement); it is
strictly sharper — $J$ collapsed to $G$, the circulant amplifies to $G^o$.

**New?** R-SW1/R-SW2/R-SW4 are **new** (not previously written in `cocycle.py`/STRUCTURE; R-SW1 follows
from the cocycle but the transfer/monodromy form is the new content). R-SW3 is a **new derivation +
interpretation** of the previously-noted period factor (now a cyclic-cover resultant with Mahler
growth). **Translatable?** yes — everything is in $S/D/G$, the DFT, and $\Delta=X^E-Y^o t$.

---

## §Verification (`checks/lit_silver_williams.py`, 49/49, exit 0)

Self-contained from repo root; imports the real kernel `from cocycle import S, D, rotations, X, Y`.

- **PART A — transfer law (R-SW1).** $X^{d_j}S(w_{j+1})-YS(w_j)-D(w)=0$ symbolically over
  $\mathbb{Z}[X,Y]$ on all rotations of $w\in\{(1,2),(1,2,3),(2,1,1,3),(3,1,1,2,2)\}$. ✓
- **PART B — circulant = resultant (R-SW2).** $\det\operatorname{circ}=\mathrm{Res}(t^o-1,\widehat S)$
  symbolically, and $=\prod_\zeta\widehat S(\zeta)$ numerically at $(2,3)$ (relative tol). ✓
- **PART C — honest null (R-SW4).** On a 14-word battery: $G\mid$ every $S^{(j)}$ ⇒ $G^o\mid
  \det\operatorname{circ}$; $G^{\varphi(d)}\mid$ every cyclotomic block; **every nonzero block
  $\ge G$ (no small block)**. Non-trivial illustration printed, e.g.
  $w=(3,1,1,2,4)$: $g=\gcd_jS^{(j)}=95$, $S^{(j)}=[665,475,1615,3325,2945]$ (5 distinct, all $\equiv0
  \bmod 95$), $\det\operatorname{circ}=53\,573\,496\,988\,750\,000=95^5\cdot6\,923\,600$ — the reduced
  residual $\det\operatorname{circ}(m)=6\,923\,600$ is **not** a unit (no shrink). (Here $g=95\mid|D|=
  1805$; $g=|D|$ only on a genuine cycle.) ✓
- **PART D — period Fox formula (R-SW3).** $\mathrm{Res}(t^r-1,X^E-Y^o t)=D(w^r)$ for $r=1,\dots,4$;
  $\prod_{d\mid 6}\mathrm{Res}(\Phi_d,\Delta)=D(w^6)$; each block $=$ homogenized $\Phi_d(X^E,Y^o)$. ✓
- **PART E — Mahler growth + Gordon (obstruction).** $2^E\ne3^o$ (so $\Delta$ non-cyclotomic,
  $\mathbf M(\Delta)\gt1$) on all test words; $G(w^r)$ strictly increasing (non-periodic, Gordon);
  $\frac1r\log G(w^r)\to\log\max(2^E,3^o)$ (rate matches target to $10^{-6}$ at $r=200$). ✓

---

## §Proposed structure (what to build for Movement IV)

The circulant door is **closed constructively**, with a precise reason; the build is to record that
closure as a structural law and re-aim:

1. **Fold the "orbit residue floor" law into STRUCTURE §3:** the orbit lattice
   $\Lambda_w=\langle S^{(0)},\dots,S^{(o-1)}\rangle\subseteq\mathbb{Z}$ is $G\cdot\langle
   m_0,\dots,m_{o-1}\rangle$ with $\gcd m_j=1$; **every** $\mathbb{Z}[\mathbb{Z}/o]$-combination (DFT
   component, circulant block, difference) is $\equiv0\pmod G$, so the *only* sub-$G$ residue is $0$.
   The circulant resultant lands at $G^o$, not below. (Integer avatar + amplification of R3's
   $J$-collapse — the two should be cross-referenced as one law: "the orbit residue floor is $G$,
   exactly.")
2. **The reduced circulant $\det\operatorname{circ}(m)=\mathrm{Res}(t^o-1,\widehat m)$** is the genuinely
   new sub-object Silver–Williams hands us: it is the "homology of the cover *relative to the base*."
   Worth one probe (open Q1) — but PART C already shows it is generically large, so promote only if a
   structured family makes it $\pm1$.
3. **Re-aim at the period/cover direction as the Layer-2 home.** R-SW3 makes precise that the cyclic
   Alexander polynomial is the *linear* $\Delta=X^E-Y^o t$, $\mathbf M=\max(2^E,3^o)$. The small-$G$
   prize is *equivalent* to a **cyclotomic $\Delta$** (Gordon) — which the cycle locus never reaches.
   This is the resultant-language restatement of the L1·5 "weight-growth $\omega\to\infty$" no-go and
   feeds the Bang–Zsygmondy/primitive-divisor machinery (each block $\Phi_d^*(2^E,3^o)$ a Zsygmondy
   factor) of the `bounded-defect-lever` Layer-2 program.

**Promotion-readiness:** **no** — this is a closure (honest null on construction) plus three imported
identities, not a new lever. It tightens STRUCTURE and unifies four existing objects; it does not
produce a new excludable family.

---

## §Open questions (feed find-thread / R2 / Layer-2)

- **Q1 (reduced circulant).** Is $\det\operatorname{circ}(m_0,\dots,m_{o-1})=\mathrm{Res}(t^o-1,\widehat
  m)=\pm1$ for any *structured* primitive family (a circulant "unit," the cover relative-homology
  trivial)? PART C shows it is generically large; a unit would be a genuinely small residual the floor
  $G$ hides. (Low promise, but cheap to scan.)
- **Q2 (period factor primes).** The block $\Phi_d^{*}(2^E,3^o)$ carries Zsygmondy primitive divisors.
  Does pinning *which* primes divide each block give an effective handle on $\operatorname{sixfree}$ in
  the period direction beyond [P3]? (Hands directly to the Bang–Zsygmondy / BHV Layer-2 sub-attack —
  `bounded-defect-lever`.)
- **Q3 (the based/reduced module).** Silver–Williams' *based* Alexander module $B=A/\langle\tilde
  x_1\rangle$ with $\Delta=(u_1-1)\det R$ is a rank-drop normalization. Is our $C(u,v)$-core ideal the
  $\det R$ of an analogous based presentation — i.e. does "based" normalize the unit ambiguity the L1·7
  $\operatorname{sixfree}$ representative already fixes? (Cross-check, low.)
- **Q4 (rank-$\ge2$ / door R2).** Silver–Williams is genuinely multivariable ($d$ components). Our
  single prime-pair is $d=1$ (degree-1 $\Delta$). A rank-$\ge2$ enrichment (third modulus, the open R2
  door) would give a *higher-degree* cycle $\Delta$ — could it be cyclotomic for a structured family,
  i.e. could R2 *construct* the small-$G$ case the $d=1$ cycle forbids? This is the one route where
  Silver–Williams' machinery could turn constructive.
  **→ DECIDED by R2 (`drafts/lit-mcmullen-norm.md`, McMullen 2002):** the cycle $\Delta=X^E-Y^o t$ is a
  binomial $\Rightarrow$ Newton polytope a **segment** $\Rightarrow$ the Alexander norm is a degenerate
  rank-$\le1$ seminorm with **no vertex-isolating slice**. A constructively small slice needs a
  **2-dim Newton polytope** ($\ge3$ non-collinear monomials), which no abelian rank-1-derived
  enrichment supplies. The only door staying inside $(2,3)$ is the **non-abelian twisted** Alexander
  polynomial (Boden–Friedl, multi-term in $t^n$). Refined NO-GO for the abelian rank-$\ge2$ door.

**Follow-up refs worth queuing** (do not mine here): Gordon, *Knots whose branched coverings have
periodic homology*, Trans. AMS 168 (1972) — the exact small/periodic ($\mathbf M=1$) criterion; and
the THREADS group-B **Davis–Ray** (arXiv:1105.2590, strong coprimality of $\Delta(\zeta)$) +
**Lind** Lind–Lehmer floor — to bracket $\operatorname{sixfree}$ between the Mahler ceiling and a
Lind–Lehmer floor on $\prod_\zeta S(\zeta)$.
