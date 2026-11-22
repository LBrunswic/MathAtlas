# Status — punctured-torus

## Current state

Stage-1 keystone certified (reducible, cusped, sub-Markoff point). Stage-2 = **LORENTZIAN
(flat)**: $D=2^E-3^o$ = Minkowski interval, criticality = light cone, $S$ = lightlike
translation. **Spacetime identified in Brunswic [arXiv:2108.12631]**: Syracuse = a point of
$T\,\mathrm{Teich}(\Sigma_{1,1})$, a GH Cauchy-compact flat spacetime with **one extreme BTZ at
the puncture**. **Complete description done** ([`spacetime-description.md`](spacetime-description.md),
[`spacetime.py`](spacetime.py)): representation $\tau=(S/2^E)E$, future-complete BTZ
white-hole spacetime, and **property P** — a class is a Syracuse cycle $\iff D\mid S\iff$ its
closed spacelike geodesic has an **integer ideal endpoint $x_0^\ast=S/D$** on the null
boundary. Caveat: reducible base is non-free (Margulis $\equiv0$); smooth realization needs an
interior Fuchsian base. Next: the smooth lift and the geometric form of P.

## Results

- **Consolidated geometric picture: [`SYNTHESIS.md`](SYNTHESIS.md)** — the single coherent account (homography choice → free-group rep → quotient manifold → cycle interpretations), with the layer structure (multiplicative/lengths · additive/$S$/endpoint · integrality/$p\mid D$) and the bottom line. Read this first.

- **Canonical lift chosen + cycle↔geodesic dictionary verified** ([`hyperbolic_model.py`](hyperbolic_model.py), plot [`hyperbolic_model.png`](hyperbolic_model.png)). Three candidate definitions of "affine maps on $\mathbb{R}^2$" were tried; the winner is the **affine group as the upper half-plane**, $\mathrm{Aff}_+(\mathbb{R})=\{x\mapsto\alpha x+\beta:\alpha\gt0\}\cong\mathbb{H}=\{\beta+i\alpha\}$ with its left-invariant (hyperbolic) metric. Generators $a:z\mapsto\tfrac{3z+1}{2}$, $b:z\mapsto\tfrac{z}{2}$ are **both hyperbolic isometries** (SL$_2$ traces $5/\sqrt6,\,3/\sqrt2\gt2$), with vertical axes $\mathrm{Re}=-1$ and $\mathrm{Re}=0$ and translation lengths $\log\tfrac32,\log2$.
  - **Cycle = vertical geodesic.** The period-cumulative map of a cycle is $z\mapsto\tfrac{3^o}{2^E}z+\tfrac{S}{2^E}$, a hyperbolic isometry whose **axis is the vertical geodesic $\mathrm{Re}(z)=x_0$ ending at the cycle value** $x_0=S/D\in\mathbb{R}=\partial\mathbb{H}$, with translation length $\ell=\bigl|\log(2^E/3^o)\bigr|$. Seeded on the axis, the period-iterates literally march down the geodesic ($z\mapsto x_0+i\,\alpha^k t$). Verified exactly on $1\to1$ ($x_0{=}1$, axis $\mathrm{Re}{=}1$, $\ell{=}\log\tfrac43$), $-1$ (axis $\mathrm{Re}{=}{-}1$), $-5\to-7$ (axis $\mathrm{Re}{=}{-}5$, $\ell{=}\log\tfrac89$).
  - **Length = the Baker/Matveev quantity.** $\ell=\log(2^E/3^o)=\log(1+D/3^o)$, so the lower bound on $|2^E-3^o|$ (`cycle-literature` Rhin/Baker, `cycle-gcd` Matveev zone) is exactly a **lower bound on the closed-geodesic length** — a systole/Margulis-type reading of the existing transcendence input. Criticality $E/o\to\log_2 3$ = short geodesics.
  - **Generic orbit zigzags.** A non-periodic trajectory's cumulative points are not on one geodesic (broken path) — the non-commutativity / the $+1$ lives in the turns; consistent with curvature concentrating at a puncture/cone.
- **Stage-1 keystone — location in the character variety (certified, [`markoff.py`](markoff.py) / [`markoff-coordinates.md`](markoff-coordinates.md)).** Trace coordinates $(x,y,z)=(\operatorname{tr}A,\operatorname{tr}B,\operatorname{tr}AB)=(\tfrac5{\sqrt6},\tfrac3{\sqrt2},\tfrac7{2\sqrt3})$. Via Fricke, $\operatorname{tr}[A,B]=+2$ **exactly** (cubic level set $x^2+y^2+z^2-xyz=4$).
  - **Reducible point.** $\operatorname{tr}[A,B]=2$ is the reducibility criterion — the generators share the eigenvector/fixed point $\infty$. The Syracuse holonomy lives on the **reducible sheet**, not the Markoff/Teichmüller sheet $\operatorname{tr}[A,B]=-2$.
  - **Genuine cusp.** $[A,B]=\big(\begin{smallmatrix}1&1/4\\0&1\end{smallmatrix}\big)$: $z\mapsto z+\tfrac14$, a **non-trivial parabolic** fixing $\infty$. The puncture is realised as a cusp at $\infty$; affine model = the *reducible, cusped degenerate* point.
  - **Sub-Markoff obstruction.** All traces $\lt 3$ = the Markoff minimum trace on the cusped-hyperbolic locus. Since $a,b$ are primitive (simple closed curves), they are **too short to uniformise a cusped finite-area hyperbolic punctured torus**; fixed-$(x,y)$ deformation to $\operatorname{tr}[A,B]=-2$ has negative discriminant ($-\tfrac{191}{12}$). Obstruction bites *only* the cusped-hyperbolic target — singular-flat / Lorentzian (and constrained Schottky) have no such length floor.
  - **Per-cycle consistency.** Cumulative matrices reproduce $\operatorname{tr}=2^E{+}3^o$, $\det=2^E3^o$, gap $=\lvert D\rvert$, $x_0=S/D$ on $1\to1,-1,-5\to-7$, cross-checking `structure.md` C1/C4/C11 (re-certified via `verify_symbolic_identity`) and `hyperbolic_model.py`.
- **Stage-2 scaffolding built (target-agnostic, [`markoff.py`](markoff.py) `deform`/`track_cycle`, plot [`markoff_deformation.png`](markoff_deformation.png)).** The naive conjugation path opening $\infty$ shows two design constraints: (i) $\operatorname{tr}[A,B_t]$ bottoms at $+2$ and **never reaches $-2$**; (ii) the trivial cycle's length **collapses to $0$ (goes elliptic) for $t\gtrsim0.1$** because $\operatorname{tr}G=7$ barely exceeds the hyperbolicity threshold $2\sqrt{12}\approx6.93$ — the geometric face of criticality. ⇒ a usable deformation must *lengthen* geodesics, or target a geometry with no hyperbolic length floor.
- **Stage-2 LORENTZIAN model — first build certified ([`lorentzian.py`](lorentzian.py) / [`lorentzian.md`](lorentzian.md)).** Minkowski $\mathbb{R}^{2,1}=\mathfrak{sl}_2$, $q(X)=-\det X$, linear isometries $\operatorname{Ad}(\mathrm{SL}_2)=\mathrm{SO}(2,1)$.
  - **Spectral picture (verified on 3 cycles).** $\operatorname{Ad}$ of a cycle element has eigenvalues $\{2^E/3^o,1,3^o/2^E\}$; rapidity (spacelike length) $=|\log(2^E/3^o)|=\ell$; neutral axis spacelike. In **null coordinates $(2^E,3^o)$** the **Lorentzian interval is $D=2^E-3^o$** and **criticality $2^E\approx3^o$ is the light cone** — a positive (critical-band) cycle grazes the light cone.
  - **$S$ = the lightlike Margulis translation (the surprise).** With diagonal (multiplicative $2$–$3$) linear part and the "$+1$" cocycle, $u(\gamma)\in\mathbb{R}\cdot E$ (null line), $q(u)=0$, transport law identical to $S$ (structure.md C5). So the Magnus cocycle $S$ *is* the lightlike translation part, and the **Margulis invariant $\alpha(\gamma)\equiv0$** — the naive flat model is degenerate (content all in a null cocycle). Geometrically: the "$+1$" is on the light cone, the precise face of criticality.
- **Spacetime identified in Brunswic's classification (certified, [`brunswic-spacetime.md`](brunswic-spacetime.md) + [`lorentzian.py`](lorentzian.py) part C).** *Cauchy-compact flat spacetimes with extreme BTZ* ([arXiv:2108.12631](https://arxiv.org/abs/2108.12631), Thm 1) parametrizes GH Cauchy-compact flat $\mathbb{E}^{1,2}_0$ spacetimes $\simeq\Sigma\times\mathbb{R}$ with $s$ extreme-BTZ lines by $T\,\mathrm{Teich}(\Sigma^*)$.
  - **Syracuse = such a spacetime over the once-punctured torus with ONE extreme BTZ at the puncture.** Certified: $g{=}1,s{=}1$, $2{-}2g{-}s={-}1\lt0$ (Thm 1 applies, $\dim_\mathbb{R}T\mathrm{Teich}=4$); the puncture holonomy $[A,B]$ has $\mathrm{Ad}$ **unipotent (eigenvalues $1,1,1$) fixing the null line $\mathbb{R}E$** = extreme BTZ (= the Lorentzian cusp, parabolic, paper p.7). Base $=$ linear holonomy; **tangent/BTZ datum $=S$** (null); interval $=D$.
  - **Route 3 vindicated:** the parabolic puncture (a hyperbolic-target *degeneracy*) **is** the extreme BTZ (a feature); the null cocycle $S$ (which killed the Margulis invariant) **is** the BTZ translation datum. Caveat: naive base is sub-Markoff (boundary of Teich) — a smooth realization needs an interior Fuchsian base with $S$ as the BTZ tangent.
- **Degeneration locus mapped — the footprint is $S/D$ (value), not $D\mid S$ (integrality)** ([`degeneration.md`](degeneration.md) + [`degeneration.py`](degeneration.py)). The first-order Margulis invariant $\dot\alpha(\gamma)$ off the reducible base (with the Syracuse cocycle) **robustly tracks $\lvert S/D\rvert$** (Spearman $+0.89$ across all generic directions; $0$ in the Cartan direction), far above $S$/$1/D$/$E$/$\beta$. Geometrically natural (the fixed line sits at null-position $S/D$). **But integrality is invisible:** cycles (integer $S/D$) don't stand out. Verdict: every geometric construction converges on the *continuous* observable $S/D$ (axis endpoint), and the whole residual difficulty of Collatz is the one discrete question geometry can't reach — *is $S/D$ an integer?* The approach reformulates the cycle problem down to its integrality core and stops there.
- **Properness tuned — a genuine Margulis spacetime exists, but it is arithmetic-blind** ([`properness.md`](properness.md) + [`properness.py`](properness.py)). Properness (all Margulis invariants one sign, Goldman–Labourie–Margulis) is a *linear* feasibility problem in $\tau\in\mathbb{R}^6$; solved by max–min over the sphere. **Found a proper cocycle** ($\tau_a=(-0.85,0.16,0.15),\tau_b=(0.30,0.35,0.13)$, uniform margin $+1.61$, robust to length 8) ⇒ a real Margulis/BTZ spacetime on the Syracuse-generator base (Drumm). **But:** (i) no Syracuse-type cocycle ($\tau_b=0$) is proper — margin $\le0$, the literal "$+1$" support is *critically improper*; (ii) the proper cocycle's Margulis spectrum on the Syracuse cycles ($\alpha=1.61,1.62,1.96$) shows **no relation to $S,D,S/D$**. Verdict: **properness ⟂ Syracuse arithmetic** — the arithmetic is a boundary/degeneracy (null cocycle) phenomenon, washed out by any genuine (proper, irreducible) spacetime.
- **Non-trivial (irreducible, discrete, free) representation found** ([`nontrivial-representation.md`](nontrivial-representation.md) + [`nontrivial_rep.py`](nontrivial_rep.py)): keep the Syracuse generator data (multipliers $\tfrac32,2$, exact traces $\tfrac5{\sqrt6},\tfrac3{\sqrt2}$) but **reposition the axes** → irreducible ($\operatorname{tr}[A,B]=827\neq2$), **discrete free Schottky** (4 disjoint isometric circles) = a convex-cocompact once-holed torus. Boundary $[A,B]$ **hyperbolic** = a *generic* (non-extreme) BTZ / geodesic funnel (length $13.4$); the extreme-BTZ cusp stays unreachable (sub-Markoff). Cost: cycle lengths become **word-dependent** (no longer Baker; only pure-generator words keep $\log\tfrac32$ etc.), and the **literal cocycle $S$ is not carried** (the affine part is a free $H^1$ choice; Margulis invariants now nonzero ⇒ free action, but mixed-sign so not yet proper). Confirms the classification: non-trivial reps exist but trade the literal arithmetic for genuineness.
- **LaTeX report written + compiled** ([`report/syracuse-btz.tex`](report/syracuse-btz.tex) → `report/syracuse-btz.pdf`, 7pp, Bourbaki style): *The flat Lorentzian spacetime of the Syracuse cycle problem: a closed geodesic with extreme BTZ* — synthesises the model, representation $\tau=(S/2^E)E$, future-completeness, the Brunswic identification, and the main theorem (Property P), with both figures and a certificate appendix.
- **Complete spacetime description (certified, [`spacetime-description.md`](spacetime-description.md) + [`spacetime.py`](spacetime.py)).**
  - **Representation:** $\rho(\gamma)=(L(\gamma),\tau(\gamma))$, $\tau(\gamma)=\tfrac{S(\gamma)}{2^E}E$ **exactly** (null; $\tau(a)=\tfrac12E,\tau(b)=0$) — the cocycle $S$ *is* the translation. Linear part $L$ = the multiplicative $2$–$3$ boost (reducible/noded base) or any Fuchsian cusped-torus uniformisation (smooth Brunswic base, a point of $T\,\mathrm{Teich}$). Puncture $[a,b]$ parabolic = extreme BTZ.
  - **Causal structure:** $M=\rho(F_2)\backslash\Omega$ (Bonsante regular domain), **future-complete** (cosmological time $\to+\infty$), past initial singularity ($\mathbb{R}$-tree dual to $\tau$); extreme-BTZ **white hole** at the cusp, time-orientation fixed by the sign of "$+1$".
  - **Cycle → geodesic map + property P:** primitive cyclic words $\to$ closed **spacelike** geodesics (axis dir $x^0$, $q\gt0$; length $\ell=|\log\tfrac{2^E}{3^o}|$). The holonomy fixes a spacelike line at null-position $x_0^\ast=S/D$. **Property P: $\gamma$ is a Syracuse cycle $\iff D\mid S\iff x_0^\ast\in\mathbb{Z}\iff$ the geodesic's ideal endpoint on the null boundary is an integer point (in the BTZ-cusp lattice).** Verified: cycles $\to1,-1,-5$; non-cycles $\to\tfrac15,\tfrac57$. (At the reducible base Margulis $\equiv0$ ⇒ non-free ⇒ smooth realization needs a Fuchsian base.)

## Dead ends

- **Naive projective/Borel lift is degenerate (informative, not fatal).** Putting $a,b$ in homogeneous coordinates as integer matrices $\big(\begin{smallmatrix}3&1\\0&2\end{smallmatrix}\big),\big(\begin{smallmatrix}1&0\\0&2\end{smallmatrix}\big)$ acting on $\mathbb{P}^1$ keeps the integer orbit on $\partial\mathbb{H}=\mathbb{R}$ (boundary, not a geodesic), and both maps fix $\infty$ — so $\langle a,b\rangle$ lands in the **Borel/affine subgroup, which is metabelian, NOT a discrete free group**. Consequence: per cycle we get an honest closed geodesic on the cylinder $\mathbb{H}/\langle G_{\rm period}\rangle$, but there is **no single punctured-torus surface** carrying all cycles at once — the shared fixed point $\infty$ must be broken. This is the precise obstacle the Teichmüller deformation has to remove.

## Open questions

- **Which geometry makes $D\mid S$ most visible?** (Not "which is forced" — deformation
  theory lets us move between them.) The generators have different linear parts, so the
  natural *starting* chart is affine (dilation/affine surface, or a $(G,X)$-structure with
  $G$ affine). Question is which target structure — hyperbolic, singular-flat
  (translation/half-translation), or Lorentzian (AdS / Margulis-spacetime) — best exposes
  the integrality/divisibility condition once we deform there.
- **Which Stage-2 target?** Given the sub-Markoff obstruction, the deformation off the
  reducible point should target **singular-flat / translation** (no length floor),
  **Lorentzian** (AdS / Margulis affine-deformation regime), or a **lengthened-Fuchsian**
  path (accept losing exact $\tfrac32,\tfrac12$ traces). Decision pending (user: decide
  after keystone — now done).
- **What does the divisibility/integrality condition become geometrically?** A cycle
  needs $D\mid S$ (an *integrality* constraint), not merely a closed loop. Which
  geometric quantity (holonomy fixed point being a lattice point? a closed geodesic
  passing through an integer marked point? a saddle connection?) encodes $D\mid S$?
  ($x_0=S/D$ is the axis endpoint; integrality of the endpoint is the candidate.)
- **Does a usable deformation exist that lengthens the critically-short cycles?** The
  naive path tips them elliptic; is there a deformation (or a non-hyperbolic target) under
  which all cycle classes stay loxodromic/geodesic on one surface?
- **~~Does the puncture carry the parabolic/affine degeneration?~~ (Resolved.)** Yes —
  $[a,b]$ is a non-trivial parabolic; the affine model is the reducible, cusped point.
- **Is this more than an analogy?** Does the geometric model give a *new* obstruction (a
  counting/rigidity theorem we can cite) or only re-encode the divisibility condition?

## Next step under consideration

Complete description done at the reducible/noded base: representation $\tau=(S/2^E)E$,
future-complete BTZ spacetime, and **property P** — Syracuse cycle $\iff$ closed spacelike
geodesic with **integer ideal endpoint $x_0^\ast=S/D$** on the null boundary. The remaining
work is the smooth lift and the geometric form of P:

1. **Lift to an interior Fuchsian base.** Does the multiplicative $2$–$3$ skeleton single out
   a canonical Fuchsian cusped once-punctured torus, or is the base a free modulus with $S$
   the only arithmetic input? Track how the ideal endpoint $x_0^\ast=S/D$ deforms under the
   lift (both endpoints become finite; Margulis length turns on).
2. **Geometrize P in the smooth spacetime.** Does "integer ideal endpoint" survive as a clean
   condition — a BTZ-extension / Cauchy-completeness statement (Brunswic Thm 2–3), or a
   closed-geodesic/return condition? "No nontrivial positive cycle" = "no closed spacelike
   geodesic (besides the trivial) has a positive integer ideal endpoint."
3. **The integer lattice geometrically.** Pin where $\mathbb{Z}\subset\partial_\infty$ lives
   relative to the BTZ cusp (the parabolic horocyclic orbit) so "integer endpoint" is intrinsic.
