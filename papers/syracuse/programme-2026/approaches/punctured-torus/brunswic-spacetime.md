# Identifying the Syracuse spacetime in Brunswic's classification

**Reference.** Léo Brunswic, *Cauchy-compact flat spacetimes with extreme BTZ*,
[arXiv:2108.12631](https://arxiv.org/abs/2108.12631). **Certificate:**
[`lorentzian.py`](lorentzian.py) part (C) (`ALL LORENTZIAN ASSERTS PASSED`).

## What the paper classifies

Globally hyperbolic, Cauchy-maximal, Cauchy-compact **flat** Lorentzian $3$-manifolds
($\mathbb{E}^{1,2}_0$-manifolds: $\mathbb{R}^{1,2}=\mathfrak{sl}_2$, isometries
$\mathrm{PSL}_2(\mathbb{R})\ltimes\mathbb{R}^3=\mathrm{SO}_0(1,2)\ltimes\mathbb{R}^{1,2}$)
with finitely many **extreme BTZ** singular lines — the Lorentzian analogue of complete
finite-volume hyperbolic surfaces (BTZ $\leftrightarrow$ cusp).

> **Theorem 1.** For $\Sigma^*$ of genus $g$ with $s$ marked points and $2-2g-s\lt0$, the
> deformation space of GH Cauchy-maximal $\mathbb{E}^{1,2}_0$-manifolds $\simeq\Sigma\times\mathbb{R}$
> with exactly $s$ extreme-BTZ singular lines $\cong$ the **tangent bundle of the
> Teichmüller space of $\Sigma^*$.**

Mess/Bonsante decomposition of the holonomy $\rho:\pi_1\to\mathrm{SO}(1,2)\ltimes\mathbb{R}^{1,2}$:
**linear part** $L$ = a Fuchsian rep (a point of $\mathrm{Teich}(\Sigma^*)$, the base),
**translation cocycle** $\tau\in H^1(\pi_1,\mathbb{R}^{1,2}_{\mathrm{Ad}L})=T_{[L]}\mathrm{Teich}$
(the fibre). Crucially (paper p.7): **extreme BTZ holonomy is parabolic** (same as a cusp);
massive particles are elliptic (conical). A cusp is the angle-$0$ end.

## The identification (certified pieces in **bold**)

Our generators $a:z\mapsto\tfrac{3z+1}{2},\,b:z\mapsto\tfrac z2$ on $\Sigma_{1,1}=$ the
**once-punctured torus**, $\pi_1=F_2$:

| Brunswic object | Syracuse object |
|---|---|
| Cauchy surface $\Sigma^*$ | once-punctured torus: $g=1$, $s=1$, **$2-2g-s=-1\lt0$** ✓ (Thm 1 applies; $\dim_{\mathbb R}T\mathrm{Teich}=4$) |
| isometry group $\mathrm{PSL}_2\ltimes\mathbb{R}^3$ | affine isometries of $\mathbb{R}^{1,2}=\mathfrak{sl}_2$ (our [`lorentzian.py`](lorentzian.py) setup) |
| extreme BTZ singular line (parabolic) | **the puncture**: $[a,b]=\big(\begin{smallmatrix}1&1/4\\0&1\end{smallmatrix}\big)$, $\mathrm{Ad}$ **unipotent (eigenvalues $1,1,1$) fixing the null line $\mathbb{R}E$** |
| base point $\in\mathrm{Teich}(\Sigma^*)$ | the $\mathrm{SO}(1,2)$ **linear holonomy** (the multiplicative $2$–$3$ skeleton) |
| tangent / translation cocycle $\tau$ | **the Magnus cocycle $S$** — valued in the null line $\mathbb{R}E$ (the BTZ datum), the lightlike translation along the BTZ axis |
| Minkowski interval | $D=2^E-3^o$ (null coordinates $(2^E,3^o)$); criticality $2^E\!\approx\!3^o$ = light cone |

So: **Syracuse $\cong$ a point of $T\,\mathrm{Teich}(\Sigma_{1,1})$ in Brunswic's Theorem 1 —
a GH Cauchy-compact flat spacetime over the once-punctured torus with exactly one extreme
BTZ singular line at the puncture, whose base is the Syracuse linear holonomy and whose
tangent/BTZ datum is the cocycle $S$.** This is route 3 ("embrace the null/parabolic
regime") realised exactly: the parabolic puncture — a *degeneracy* for the hyperbolic
Fuchsian target — **is** the extreme BTZ (a feature), and the null cocycle $S$ — which made
the Margulis invariant vanish — **is** precisely the BTZ translation datum.

## The honest caveat (where the work now is)

Theorem 1's base must be a *genuine Fuchsian* cusped once-punctured-torus structure (interior
of $\mathrm{Teich}(\Sigma_{1,1})$, the $\operatorname{tr}[A,B]=-2$ Markoff sheet). The naive
Syracuse linear holonomy is **reducible / sub-Markoff** ($\operatorname{tr}[A,B]=+2$, traces
$\lt3$) — a *boundary/noded* point, not an interior one. So as it stands Syracuse names a
**boundary point of the base** of $T\,\mathrm{Teich}$, with $S$ as the BTZ tangent. Realising
a smooth Brunswic spacetime means lifting the base into the interior (a true Markoff cusped
torus) while carrying the Syracuse arithmetic in the **BTZ tangent datum $S$**.

## Stage-3 payoff this opens (the cycle condition, geometrically)

In Brunswic's moduli the data is (base Fuchsian structure, BTZ tangent $S$) and the interval
is $D=2^E-3^o$. The cycle condition $D\mid S$ becomes a **commensurability/integrality
condition on the BTZ tangent datum relative to the interval**. Candidate translations of
"no nontrivial Syracuse cycle":
1. a **non-existence of closed (spacelike) geodesics** of prescribed combinatorial type in
   the BTZ spacetime — the Lorentzian closed-geodesic problem;
2. a condition in the **BTZ-extension** procedure (Def 1.1 / Thm 2): which tangent data $S$
   extend to a Cauchy-complete maximal BTZ-extension;
3. an **integrality** of the BTZ holonomy's translation ($S$) against the lattice fixed by
   the interval $D$ — the lightlike analogue of "the cusp closes up arithmetically."

**Open questions for the author (Brunswic):**
- Is there a *canonical* Fuchsian base to attach to the multiplicative $2$–$3$ skeleton, or
  should the base be a free parameter with $S$ the only arithmetic input?
- Does $D\mid S$ have a clean reading as a Cauchy-completeness / BTZ-extension obstruction in
  the Theorem 2 / Theorem 3 framework?
- The extreme-BTZ *white-hole* model $\mathrm{d}s_0^2=-2\,\mathrm{d}\tau\,\mathrm{d}r+\mathrm{d}r^2+r^2\mathrm{d}\theta^2$:
  does the Syracuse "$+1$" pick the white-hole vs black-hole (time) orientation?
