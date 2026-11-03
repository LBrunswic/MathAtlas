import GXScaffold.BTZ.Spear
import GX.BTZ.Holonomy
import Causal.Flat.CauchyComplete

/-!
# `GXScaffold.BTZ.Surgery` — Cauchy-surface surgery in spear neighbourhoods (B21 Lemmas 2.6–2.11)

Package WP-41j (WAVE5-PLAN.md, WP-39j); WP-43b (Lemma 2.6(i), Lemma 2.9, Cor 2.11 added; fixer
round 1: the global part of Prop 2.17 split into one declaration per obstruction, §5; fixer
round 2: `IsE0C1SpacelikeCauchy.rim` repaired — it lacked the shaft antecedent and was
contradictory whenever a spear datum exists, AUDIT-2 B1).
`brunswic2021cauchy` (**B21**, `papers/gx/sources/2108.12631/src/BTZ_1.tex`) §2.1: Lemma 2.6
`lem:curve_extension` (l.704), Lemma 2.7 `lem:surface_causal` (l.749), Lemma 2.8
`lem:surface_complete` (l.781), Lemmas 2.9/2.10 `lem:intersect_number_compact` /
`lem:intersect_number_complete` (l.885/897), Cor 2.11 `cor:intersect` (l.910), cut by SCOPE's K-3
(monotonicity + IVT in place of intersection numbers), and the output Section 4 consumes, B21
Prop 2.17's first assertion `prop:abs_max` (l.1078). **No label is marked**: these are cited
results built here (DEC-23), not gx ledger rows. Rows:

* `lem:surface_causal` (Lemma 2.7) — **partial**, 0 `sorry` (pointwise reading):
  `GX.E0Surgery.lem_surface_causal`; the printed identity is `GX.E0Surgery.graphQuad_eq`.
* `lem:curve_extension` (Lemma 2.6) — **partial**, both items 0 `sorry` (finding: the two printed
  proofs are swapped). (ii) `GX.E0Surgery.lem_curve_extension_ii_complete` (spacelike, complete,
  `C^n`, positive, periodic, `+∞` at the axis). (i) `GX.E0Surgery.lem_curve_extension_i` (two
  pieces, the slice `M/R` and a `C^n` piece, each spacelike by Lemma 2.7; positive, continuous;
  the graph spacelike over the closed disc in integrated form, `IsSpacelikeDiscGraph`; compact).
* `lem:surface_complete` (Lemma 2.8) — **partial**, both items **proved**, 0 `sorry`, under the
  reading « piecewise smooth » = `C¹` on the strip (one piece, ⚠ strengthened hypothesis) and
  « complete » = completeness of the pulled length over the strip `(0, R] × ℝ`:
  (1) `GX.E0Surgery.lem_surface_complete_one` — spacelike **and** complete under `δ ≥ C²/r²`;
  (2) `GX.E0Surgery.lem_surface_complete_two` — spacelike `C¹` and complete ⇒ `τ → +∞` at the axis.
* `lem:intersect_number_complete` (Lemma 2.10) — **partial**, 0 `sorry` (K-3 reading of the curve
  hypotheses): `GX.E0Surgery.lem_intersect_number_complete`; non-vacuity
  `GX.E0Surgery.lem_intersect_number_complete_vertical`.
* `lem:intersect_number_compact` (Lemma 2.9) — **partial**, 0 `sorry` (K-3 reading; curves may run
  along or cross the axis): `GX.E0Surgery.lem_intersect_number_compact`; non-vacuity
  `GX.E0Surgery.lem_intersect_number_compact_axis` (the BTZ axis itself).
* `cor:intersect` (Cor 2.11, `|c ∩ Σ| = |c* ∩ Σ*|`) — **partial**, 0 `sorry` (K-3):
  `GX.E0Surgery.cor_intersect_number` (`c* = c` on `{t | r(c t) > 0}`, same rim); non-vacuity
  `GX.E0Surgery.cor_intersect_number_vertical`. (`GX.E0Surgery.cor_intersect` is the K-3 arc lemma.)
* `rem:curve_spear` (Remark 2.12, l.913) — **stated** `GX.E0Surgery.rem_curve_spear` (the
  components of an inextensible causal curve of `Reg M` in a spear are spear arcs,
  `SpearSurgeryDatum.IsSpearArc`; one tagged `sorry`); their count, `IsSpearArc.ncard`, 0 `sorry`.
* `prop:abs_max` (Prop 2.17, first assertion: `Σ*` Cauchy in `Reg M`, `Reg M` Cauchy-complete) —
  **stated** `GX.E0Surgery.regM_isCauchyComplete`, now a composition with no `sorry` of its own
  (WP-43b round 1): (G0) smoothing `exists_isE0C1SpacelikeCauchy`, then
  `regM_isCauchyComplete_of_C1` (B21 l.227's « Cauchy-compact », `IsE0C1SpacelikeCauchy`, its
  `rim` well-posed by `eqOn_closedBall_of_rim_antecedent` since round 2), from
  (G1) `exists_surgeryData`, (G2) Remark 2.12 `rem_curve_spear`, (G3)
  `SurgeryData.isCauchySurface_sigmaStar`, (G4a) `SurgeryData.isSpacelikeLipschitzAt_cusp`, (G5)
  `SurgeryData.completeSpace_sigmaStar` — six tagged `sorry`s, one obstruction each. Proved:
  `Σ*` (`SurgeryData.sigmaStar`) is `Σ` off the spears and the cusp in each, lies in `Reg M`; one
  spear datum at every BTZ point of `I⁻(Σ)` (`exists_spearSurgeryDatum`), thinnable; (G4) off the
  spears; the topology field. Prop 2.17's maximality assertion is `GXScaffold.BTZ.AbsMax`'s
  `absMax_e0RegM`.

> \begin{lemou} Let $\mathcal S$ be a spear of vertex $(-2R,0,0)$ and radius $R$ in $\mass{0}$
> and let $\tau_{\Sigma}^R: \partial \mathbb D_R \rightarrow \R_+$ be a smooth positive function.
> Then (i) there exists a piecewise smooth function $\tau_\Sigma: \mathbb D_R\rightarrow \R_+$
> extending $\tau_\Sigma^R$ which graph is spacelike and compact. (ii) there exists a piecewise
> smooth function $\tau_\Sigma:\mathbb D_R^*\rightarrow \R_+$ extending $\tau_\Sigma^R$ which graph
> is spacelike and complete. \end{lemou} (l.704–712)
>
> \begin{lemou} Let $\Sigma$ be a piecewise smooth (possibly with boundary) submanifold of
> $\mass{0}$ which is the graph of some piecewise smooth map $\tau_\Sigma: D \rightarrow \R$ with
> $D\subset \{\tau=0\}\subset \mass{0}$. Then $\Sigma$ is spacelike iff on each smooth domain of
> $\tau_\Sigma$ $1-2\frac{\partial \tau_\Sigma}{\partial \r}-\left(\frac{1}{\r}\frac{\partial
> \tau_\Sigma}{\partial \theta}\right)^2 >0.$ \end{lemou} (l.749–754)
>
> \begin{lemou} Let $\Sigma^*$ be the graph of some piecewise smooth map $\tau_\Sigma: \mathbb
> D_R^*\rightarrow \RR$ with $R>0$; then: 1. $\Sigma^*$ is spacelike and complete if there exists
> $C>0$ such that $1-2\frac{\partial \tau_\Sigma}{\partial \r}-\left(\frac{1}{\r}\frac{\partial
> \tau_\Sigma}{\partial \theta}\right)^2\geq\frac{C^2}{\r^2}$ wherever this expression is well
> defined. 2. If $\Sigma$ is spacelike and complete then, $\lim_{(\r,\theta) \rightarrow
> 0}\tau_\Sigma(\r,\theta) = +\infty$ \end{lemou} (l.781–792)
>
> Lemma 2.9 (l.885–896): for a spear $\S = \{\r\le R\}\cap J^+(p)$, $\Sigma$ a spacelike graph
> over $\mathbb D_R$ in the shaft and $c$ a future causal curve of $\S$, closed, inextendible in
> $\mathrm{Int}(\S)$: $|c\cap\Sigma| = 1$ if $\sup(c)\in J^+(\C)\cup\{+\infty\}$, $0$ otherwise.
>
> Lemma 2.10 (l.897–908): for a blunt spear $\S^*$, $\Sigma^*$ a spacelike graph over
> $\mathbb D_R^*$ with $\lim \tau = +\infty$ and $c^*$ a future causal curve of $\S^*$, closed,
> inextendible in $\mathrm{Int}(\S^*)$: $|c^*\cap\Sigma^*| = 1$ if
> $\sup(c^*) \in J^+(\C^*)\cup\{+\infty\}$, $0$ otherwise. Cor 2.11 (l.910–912): if
> $\reg(c)=c^*$, $\reg(\S)=\S^*$ and $\C=\C^*$ then $|c\cap \Sigma| = |c^*\cap\Sigma^*|$.

## Hypothesis checklist

| paper | here |
|---|---|
| graphs over `D ⊆ {τ = 0}` in `(r, θ)` | ✓ `g : ℝ × ℝ → ℝ`, `(r, θ) ↦ τ`, `2π`-periodic in `θ` |
| « piecewise smooth » (Lemma 2.7) | ⚠ read pointwise: `HasFDerivAt` at the point (the piecewise case is the union of its pieces) |
| « piecewise smooth » (Lemma 2.8) | ⚠ strengthened: `ContDiffOn ℝ 1 g` on the strip `{0 < r ≤ R}` (one piece; the proof's `sup |∂_θ τ|` over an annulus, l.812, needs `C¹`), plus `HasFDerivAt` there |
| « spacelike » | ✓ positive definiteness of the pulled-back metric of `btzPaperDev` on the tangent plane |
| « complete » (Lemma 2.8, 2.6(ii)) | ⚠ read: `CompleteSpace (Causal.Flat.PulledLength (graphDev g R))` over the strip `(0, R] × ℝ` (the universal cover of `𝔻_R^*`; one development exists only there) |
| `τ^R` smooth positive (Lemma 2.6) | ⚠ weakened: `C^n`, `1 ≤ n`, periodic, positive |
| Lemma 2.10: `c*` future causal, closed in `S*`, inextendible in `Int S*` | ⚠ read (K-3): `c` continuous on an interval `I`, `≼`-increasing, in `{0 < r ≤ R}`; past end in `[p]` = a point with `F < 0`, or `inf r = 0`; future end `τ` unbounded (`sup = +∞`) or a last point on the rim |
| Lemma 2.10: `sup(c*) ∈ J⁺(C*)` | ✓ for a last point on the rim, `∃ y ∈ C*, y ≼ c(b)` (`height_nonneg_iff_mem_Jplus_rim`) |
| Lemma 2.6(i): « piecewise smooth », « spacelike », « compact » | ⚠ read: two pieces (`r ≤ R/2`, `r ≥ R/2`), each `IsSpacelikeGraph` (Lemma 2.7 pointwise, `r > 0`); the graph over the closed disc `IsSpacelikeDiscGraph` (height continuous on `{r ≤ R}` and strictly increasing along `≼`, axis included); `IsCompact (discGraphSet τ R)` |
| Lemma 2.9: `Σ` spacelike graph over `𝔻_R` | ⚠ read: `IsSpacelikeDiscGraph g R` (the integrated Lemma 2.7, which is what the proof uses; at the axis no derivative criterion exists) |
| Lemma 2.9: `c` closed in `S`, inextendible in `Int S` | ⚠ read (K-3), as Lemma 2.10: an arc of `{r ≤ R}` with a point below `Σ` (the head), and future end `τ` unbounded or a last point on the shaft |
| Cor 2.11: `reg(c) = c*`, `reg(S) = S*`, `C = C*` | ✓ `c* = c` on `I* = {t ∈ I | r(c t) > 0}`; `C = C*` as `τ_Σ = τ_{Σ*}` on `r = R`; the hypotheses of 2.9 for `c` and of 2.10 for `c*` |
| Prop 2.17: `E_A`-manifold, `A ⊆ ℝ₊` | ⚠ strengthened: `𝔼₀`-manifolds only (`A = {0}`), T2, connected, second countable |
| Prop 2.17: Cauchy-maximal | ⚠ read (DEC-77(c)): `E0Spear.IsE0CauchyMaximal` |
| Prop 2.17: Cauchy-compact | ⚠ read: a compact Cauchy surface in `regM_isCauchyComplete` (B21 l.227 asks a *smooth spacelike* one, Bernal–Sánchez: the gap is (G0)); in `regM_isCauchyComplete_of_C1` as l.227 does, `IsE0C1SpacelikeCauchy` (Cauchy, compact, spacelike Lipschitz in `Reg M`'s flat charts, `C¹` trace on the shaft circle of every spear chart in which `S` is the graph of a continuous `τ_Σ > v + R/2` over the closed disc) |
| Prop 2.17: Cauchy-complete | ⚠ read (DEC-31): `Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)` |

## SCOPE (disclosed)

* (a) The local machinery is complete in both directions (WP-43b): Lemma 2.6(i)/(ii), 2.7, 2.8,
  2.9, 2.10 and Cor 2.11 are proved in their readings, 0 `sorry`.
* (b) The global part (§5d) is split, one tagged `sorry` per obstruction, and
  `regM_isCauchyComplete` is their composition. Besides the upstream sorries of
  `GXScaffold.BTZ.Spear` (Lemma 2.3: `CylChartData.globallyHyperbolic_glued`,
  `CylChartData.isCauchySurface_glued`; Lemma 2.4's future case, `lem_add_BTZ_param_line`) — whose
  CBG inputs `hLine`/`hSC` are now LocalModel's proved (O2) `E0LM.e0_globalBTZ` and (O4′)
  `E0LM.e0_secondCountable_of_cauchy` (WP-43d, 0 `sorry`), instantiated in
  `exists_spearSurgeryDatum` — the six are: (G0) smoothing (a cited theorem: Bernal–Sánchez /
  Bernard–Suhr); (G1) finitely many disjoint closed spears; (G2) Remark 2.12 (relative curve
  extension in a spear); (G3) the counting argument from Remark 2.12 and Cor 2.11; (G4a) the cusp
  and the rim corner spacelike Lipschitz in flat charts; (G5) the gluing of completeness.

Provenance: mathlib `fabf563a` (tag `v4.31.0`); lean-causal `ca2ad78` (imports strict
`Causal.Flat.CauchyComplete`, DEC-33).
-/

namespace GX

open Set Filter Topology Function
open scoped Real

namespace E0Surgery

open E0

/-! ### §1 Lemma 2.7 — spacelike graphs (pointwise) -/

section SurfaceCausal

/-- **B21's `δ`** at a point `(r, θ)` of a graph with partial derivatives `gr = ∂_r τ`,
`gθ = ∂_θ τ`: `δ = 1 − 2∂_r τ − (∂_θ τ / r)²` (l.751). -/
noncomputable def spacelikeDelta (gr gθ r : ℝ) : ℝ := 1 - 2 * gr - (gθ / r) ^ 2

/-- **The printed metric on a tangent vector of a graph**: `(dτ, dr, dθ) = (gr u + gθ w, u, w)`
in `−2dτdr + dr² + r²dθ²`. -/
noncomputable def graphQuad (gr gθ r u w : ℝ) : ℝ :=
  -2 * (gr * u + gθ * w) * u + u ^ 2 + r ^ 2 * w ^ 2

/-- **B21's identity** (l.757): `ds²_Σ = δ dr² + ((∂_θ τ / r) dr − r dθ)²`. -/
theorem graphQuad_eq {gr gθ r : ℝ} (hr : r ≠ 0) (u w : ℝ) :
    graphQuad gr gθ r u w = spacelikeDelta gr gθ r * u ^ 2 + (gθ / r * u - r * w) ^ 2 := by
  unfold graphQuad spacelikeDelta
  field_simp
  ring

/-- Positive definiteness of the graph metric is `δ > 0` (`r > 0`). -/
theorem graphQuad_pos_iff {gr gθ r : ℝ} (hr : 0 < r) :
    (∀ u w : ℝ, (u, w) ≠ (0, 0) → 0 < graphQuad gr gθ r u w) ↔ 0 < spacelikeDelta gr gθ r := by
  constructor
  · intro h
    have h1 := h 1 (gθ / r ^ 2) (by simp)
    rw [graphQuad_eq hr.ne'] at h1
    have : gθ / r * 1 - r * (gθ / r ^ 2) = 0 := by field_simp; ring
    rw [this] at h1
    simpa using h1
  · intro hδ u w huw
    rw [graphQuad_eq hr.ne']
    by_cases hu : u = 0
    · have hw : w ≠ 0 := fun hw => huw (by rw [hu, hw])
      rw [hu]
      have : 0 < (r * w) ^ 2 := by positivity
      nlinarith [sq_nonneg (gθ / r * 0 - r * w)]
    · have : 0 < spacelikeDelta gr gθ r * u ^ 2 := mul_pos hδ (by positivity)
      nlinarith [sq_nonneg (gθ / r * u - r * w)]

/-- The graph immersion `(r, θ) ↦ (τ = g(r, θ), r, θ)` into the paper's coordinates. -/
def graphMap (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ := (g p, p.1, p.2)

theorem hasFDerivAt_graphMap {g : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (hg : HasFDerivAt g L p) :
    HasFDerivAt (graphMap g) (L.prod ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ))) p :=
  hg.prodMk (hasFDerivAt_fst.prodMk hasFDerivAt_snd)

/-- **The pulled-back Minkowski metric on the graph is `graphQuad`** (through
`GX.btzPaperDev_pullback`). -/
theorem minkQ_fderiv_graph {g : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (hg : HasFDerivAt g L p) (v : ℝ × ℝ) :
    Causal.Flat.minkQ (fderiv ℝ btzPaperDev (graphMap g p) (fderiv ℝ (graphMap g) p v)) =
      graphQuad (L (1, 0)) (L (0, 1)) p.1 v.1 v.2 := by
  rw [(hasFDerivAt_graphMap hg).fderiv, btzPaperDev_pullback]
  have hv : L v = L (1, 0) * v.1 + L (0, 1) * v.2 := by
    have : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', graphMap, hv, graphQuad]

/-- **B21 Lemma 2.7** (`lem:surface_causal`, l.749), pointwise: at a point `p = (r, θ)`, `r > 0`,
where `g` is differentiable, the graph of `g` is spacelike (the pulled-back metric of the paper's
developing map is positive definite on the tangent plane) iff `δ > 0`. -/
theorem lem_surface_causal {g : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {p : ℝ × ℝ}
    (hg : HasFDerivAt g L p) (hr : 0 < p.1) :
    (∀ v : ℝ × ℝ, v ≠ 0 → 0 < Causal.Flat.minkQ
        (fderiv ℝ btzPaperDev (graphMap g p) (fderiv ℝ (graphMap g) p v))) ↔
      0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := by
  rw [← graphQuad_pos_iff hr]
  simp only [minkQ_fderiv_graph hg]
  constructor
  · intro h u w huw
    exact h (u, w) (by simpa using huw)
  · intro h v hv
    exact h v.1 v.2 (fun h' => hv (by rw [show v = (v.1, v.2) from rfl, h']; rfl))

end SurfaceCausal

/-! ### §2 Lemma 2.6(ii) — the complete cusp -/

section CurveExtension

/-- **The cusp extension** `τ(r, θ) = τ^R(θ) + M(1/r − 1/R)` (B21 l.858–859, given there as the proof
of (i): the proofs of (i) and (ii) are swapped). -/
noncomputable def cuspExt (τR : ℝ → ℝ) (R M : ℝ) (p : ℝ × ℝ) : ℝ :=
  τR p.2 + M * (1 / p.1 - 1 / R)

theorem cuspExt_rim (τR : ℝ → ℝ) (R M θ : ℝ) : cuspExt τR R M (R, θ) = τR θ := by
  simp [cuspExt]

theorem hasFDerivAt_cuspExt {τR : ℝ → ℝ} {R M : ℝ} {p : ℝ × ℝ} (hp : p.1 ≠ 0)
    (hτ : DifferentiableAt ℝ τR p.2) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (cuspExt τR R M) L p ∧
      L (1, 0) = -(M / p.1 ^ 2) ∧ L (0, 1) = deriv τR p.2 := by
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => τR q.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv τR p.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hτ.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(p.1 ^ 2)⁻¹)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (hasDerivAt_inv hp).hasFDerivAt.comp p hasFDerivAt_fst
  have H := h2.add ((h1.sub_const (1 / R)).const_mul M)
  have he : cuspExt τR R M = (fun q : ℝ × ℝ => τR q.2) + fun y => M * (y.1⁻¹ - 1 / R) := by
    funext q; simp [cuspExt, one_div]
  refine ⟨_, he ▸ H, ?_, ?_⟩
  · simp; field_simp
  · simp

/-- **B21 Lemma 2.6(ii)** (`lem:curve_extension`, l.704): a `C^n` (`n ≥ 1`) positive `2π`-periodic
`τ^R` on the rim `r = R` extends to `τ` on `{0 < r ≤ R}`, `C^n` on `{r > 0}`, positive, periodic, with
`δ ≥ 1/r²` — Lemma 2.8(1)'s criterion with `C = 1` (spacelike and complete:
`lem_curve_extension_ii_complete`). -/
theorem lem_curve_extension_ii {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) {R : ℝ} :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ (∀ r θ, τ (r, θ + 2 * π) = τ (r, θ)) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → 0 < τ p) ∧
      ContDiffOn ℝ n τ {p | 0 < p.1} ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt τ L p ∧
        1 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1) ∧
      Tendsto τ (comap Prod.fst (𝓝[>] 0)) atTop := by
  have hdiff : Differentiable ℝ τR := hτ.differentiable (by
    intro h; rw [h] at hn; exact absurd hn (by decide))
  have hdper : Periodic (deriv τR) (2 * π) := by
    intro θ
    have hf : (fun x => τR (x + 2 * π)) = τR := funext hper
    rw [← deriv_comp_add_const, hf]
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
    (hdper.isBounded_of_continuous (by positivity) (hτ.continuous_deriv hn))
  have hB' : ∀ θ, (deriv τR θ) ^ 2 ≤ B ^ 2 := fun θ => by
    have h := hB _ (mem_range_self θ)
    rw [Real.norm_eq_abs] at h
    have h0 : 0 ≤ B := (abs_nonneg _).trans h
    exact sq_le_sq' (by linarith [neg_abs_le (deriv τR θ)]) (h.trans' (le_abs_self _))
  set M : ℝ := 1 + B ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨cuspExt τR R M, fun θ => cuspExt_rim τR R M θ, fun r θ => ?_, fun p hp hpR => ?_, ?_,
    fun p hp => ?_, ?_⟩
  · simp only [cuspExt, hper θ]
  · have h1 : 1 / R ≤ 1 / p.1 := one_div_le_one_div_of_le hp hpR
    have := hpos p.2
    simp only [cuspExt]
    nlinarith
  · have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => τR p.2) {p | 0 < p.1} :=
      (hτ.comp contDiff_snd).contDiffOn
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => 1 / p.1) {p | 0 < p.1} :=
      contDiffOn_const.div contDiffOn_fst (fun p hp => ne_of_gt hp)
    exact h1.add (contDiffOn_const.mul (h2.sub contDiffOn_const))
  · obtain ⟨L, hL, hL1, hL2⟩ := hasFDerivAt_cuspExt (R := R) (M := M) hp.ne' (hdiff p.2)
    refine ⟨L, hL, ?_⟩
    rw [hL1, hL2]
    have hu : 0 < 1 / p.1 ^ 2 := by positivity
    have e : spacelikeDelta (-(M / p.1 ^ 2)) (deriv τR p.2) p.1 =
        1 + (2 * M - (deriv τR p.2) ^ 2) * (1 / p.1 ^ 2) := by
      unfold spacelikeDelta; field_simp; ring
    rw [e]
    have := hB' p.2
    nlinarith
  · -- `τ ≥ M (1/r − 1/R) → +∞` at the axis
    have hM : 0 < M := by positivity
    have h1 : Tendsto (fun p : ℝ × ℝ => M * (1 / p.1 - 1 / R)) (comap Prod.fst (𝓝[>] 0)) atTop := by
      have h0 : Tendsto (fun p : ℝ × ℝ => 1 / p.1) (comap Prod.fst (𝓝[>] 0)) atTop := by
        simp only [one_div]
        exact tendsto_inv_nhdsGT_zero.comp tendsto_comap
      exact (tendsto_atTop_add_const_right _ (-(1 / R)) h0).const_mul_atTop hM |>.congr
        (fun p => by ring)
    refine tendsto_atTop_mono (fun p => ?_) h1
    have := hpos p.2
    simp only [cuspExt]
    linarith

end CurveExtension

/-! ### §3 Lemmas 2.9–2.11 cut by K-3 — the height is increasing along `≼` -/

section Height

/-- **A spacelike graph over the blunt spear `{0 < r ≤ R}`**: `g` periodic in `θ`, differentiable at
every point of the region, with `δ > 0` there (Lemma 2.7). -/
structure IsSpacelikeGraph (g : ℝ × ℝ → ℝ) (R : ℝ) : Prop where
  periodic : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)
  deriv : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R →
    ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧ 0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.1

/-- The height of `x` above the graph, read with the angle `θ`: `F = τ − g(r, θ)`. -/
noncomputable def heightAt (g : ℝ × ℝ → ℝ) (x : E0) (θ : ℝ) : ℝ := x.1 - g (rad x, θ)

/-- **The height of `x` above the graph** `F(x) = τ − τ_Σ(r, θ)` (B21 l.760), angle-free by
periodicity (`heightAt_eq_height`). -/
noncomputable def height (g : ℝ × ℝ → ℝ) (x : E0) : ℝ := heightAt g x (Complex.arg x.2)

/-- **The graph `Σ*`** over the blunt spear region `{0 < r ≤ R}`. -/
def graphSet (g : ℝ × ℝ → ℝ) (R : ℝ) : Set E0 :=
  {x | 0 < rad x ∧ rad x ≤ R ∧ height g x = 0}

variable {g : ℝ × ℝ → ℝ} {R : ℝ}

theorem heightAt_eq_height (hg : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) {x : E0} {θ : ℝ}
    (hx : Polar x θ) (hr : 0 < rad x) : heightAt g x θ = height g x := by
  obtain ⟨k, hk⟩ := (polar_arg x).eq_add_int hx hr
  have hP : Periodic (fun t => g (rad x, t)) (2 * π) := fun t => hg _ t
  have := hP.int_mul k (Complex.arg x.2)
  unfold height heightAt
  rw [hk, show 2 * π * (k : ℝ) = k * (2 * π) by ring, this]

theorem clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (u w : ℝ) : L (u, w) = u * L (1, 0) + w * L (0, 1) := by
  have : ((u, w) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + w • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The height along the straight segment `P + s V` of the development, `P = (a₀, b₀, c₀)`,
`V = (A, B, C)`, read back in `𝔼₀` (`r = b`, `θ = −c/b`, `τ = (a − bθ² + b)/2`). -/
noncomputable def segHeight (g : ℝ × ℝ → ℝ) (a₀ b₀ c₀ A B C s : ℝ) : ℝ :=
  (a₀ + s * A - (b₀ + s * B) * (-(c₀ + s * C) / (b₀ + s * B)) ^ 2 + (b₀ + s * B)) / 2 -
    g (b₀ + s * B, -(c₀ + s * C) / (b₀ + s * B))

/-- **The pointwise monotonicity** (B21 l.759–777): along a future causal straight segment of the
development inside the region, the height has a positive derivative. -/
theorem hasDerivAt_segHeight_pos (hg : IsSpacelikeGraph g R) {a₀ b₀ c₀ A B C s : ℝ}
    (hb : 0 < b₀ + s * B) (hbR : b₀ + s * B ≤ R) (hB : 0 ≤ B) (hA : 0 ≤ A) (hC : C ^ 2 ≤ A * B)
    (hV : ¬(A = 0 ∧ B = 0 ∧ C = 0)) :
    ∃ e, HasDerivAt (segHeight g a₀ b₀ c₀ A B C) e s ∧ 0 < e := by
  set b := b₀ + s * B with hbdef
  set c := c₀ + s * C with hcdef
  set θ := -c / b with hθdef
  set w := (c * B - C * b) / b ^ 2 with hwdef
  obtain ⟨L, hL, hδ⟩ := hg.deriv (b, θ) hb hbR
  have hbf : HasDerivAt (fun s => b₀ + s * B) B s := by
    simpa using ((hasDerivAt_id s).mul_const B).const_add b₀
  have hcf : HasDerivAt (fun s => c₀ + s * C) C s := by
    simpa using ((hasDerivAt_id s).mul_const C).const_add c₀
  have haf : HasDerivAt (fun s => a₀ + s * A) A s := by
    simpa using ((hasDerivAt_id s).mul_const A).const_add a₀
  have hθf : HasDerivAt (fun s => -(c₀ + s * C) / (b₀ + s * B)) w s := by
    refine (hcf.neg.div hbf hb.ne').congr_deriv ?_
    simp only [Pi.neg_apply, hwdef, hcdef, hbdef]
    ring
  have hτf : HasDerivAt (fun s => (a₀ + s * A - (b₀ + s * B) * (-(c₀ + s * C) / (b₀ + s * B)) ^ 2 +
      (b₀ + s * B)) / 2) ((A - (B * θ ^ 2 + b * (2 * θ * w)) + B) / 2) s := by
    refine (((haf.sub (hbf.mul (hθf.pow 2))).add hbf).div_const 2).congr_deriv ?_
    simp only [Pi.pow_apply, hθdef, hbdef, hcdef]
    push_cast
    ring
  have hgf : HasDerivAt (fun s => g (b₀ + s * B, -(c₀ + s * C) / (b₀ + s * B))) (L (B, w)) s :=
    hL.comp_hasDerivAt s (hbf.prodMk hθf)
  refine ⟨_, hτf.sub hgf, ?_⟩
  rw [clm_apply_pair]
  set gr := L (1, 0)
  set gθ := L (0, 1)
  -- the key identity: `2B φ' = (AB − C²) + graphQuad gr gθ b B w`
  have hcb : c = -(b * θ) := by rw [hθdef]; field_simp
  have hkey : 2 * B * ((A - (B * θ ^ 2 + b * (2 * θ * w)) + B) / 2 - (B * gr + w * gθ)) =
      (A * B - C ^ 2) + graphQuad gr gθ b B w := by
    have hw : b * w = c * B / b - C := by rw [hwdef]; field_simp
    have hC' : C = -(B * θ + b * w) := by rw [hw, hcb]; field_simp; ring
    unfold graphQuad
    rw [hC']
    ring
  rcases hB.lt_or_eq with hB' | hB'
  · have hq := (graphQuad_pos_iff hb).2 hδ B w (by
      intro h; exact absurd (congrArg Prod.fst h) (by simpa using hB'.ne'))
    have : 0 < 2 * B * ((A - (B * θ ^ 2 + b * (2 * θ * w)) + B) / 2 - (B * gr + w * gθ)) := by
      rw [hkey]; nlinarith
    exact pos_of_mul_pos_right this (by positivity)
  · have hC0 : C = 0 := by
      rw [← hB', mul_zero] at hC
      exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hC (sq_nonneg _))
    have hA0 : 0 < A := by
      rcases hA.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨h.symm, hB'.symm, hC0⟩ hV
    have hw0 : w = 0 := by rw [hwdef, hC0, ← hB']; simp
    rw [hw0, ← hB']
    simp only [zero_mul, mul_zero, add_zero, sub_zero]
    linarith

/-- **The height is strictly increasing along `≼`** in the region `0 < r ≤ R` (B21's commented-out
proof of Lemma 2.7, l.759–777, integrated along the straight segment of the development). -/
theorem height_lt_of_le (hg : IsSpacelikeGraph g R) {x y : E0} (hxy : Le x y) (hx : 0 < rad x)
    (hy : rad y ≤ R) (hne : x ≠ y) : height g x < height g y := by
  have hrxy : rad x ≤ rad y := hxy.closed.2.1
  have hry : 0 < rad y := hx.trans_le hrxy
  obtain ⟨θ₁, θ₂, h₁, h₂, hV⟩ := hxy
  set P := lift x θ₁ with hP
  set Q := lift y θ₂ with hQ
  have hP1 : P.2.1 = rad x := rfl
  have hQ1 : Q.2.1 = rad y := rfl
  have hP2 : P.2.2 = -(rad x * θ₁) := rfl
  have hQ2 : Q.2.2 = -(rad y * θ₂) := rfl
  have hP0 : P.1 = 2 * x.1 + rad x * θ₁ ^ 2 - rad x := rfl
  have hQ0 : Q.1 = 2 * y.1 + rad y * θ₂ ^ 2 - rad y := rfl
  obtain ⟨hA, hB, hC⟩ := hV
  have hB1 : (Q - P).2.1 = rad y - rad x := by simp [hP1, hQ1]
  have hne' : ¬((Q - P).1 = 0 ∧ (Q - P).2.1 = 0 ∧ (Q - P).2.2 = 0) := by
    rintro ⟨e1, e2, e3⟩
    have hQP : Q = P := sub_eq_zero.1 (Prod.ext e1 (Prod.ext e2 e3))
    apply hne
    rw [← unlift_lift h₁, ← unlift_lift h₂]
    exact congrArg unlift hQP.symm
  set φ := segHeight g P.1 P.2.1 P.2.2 (Q - P).1 (Q - P).2.1 (Q - P).2.2 with hφ
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, ∃ e, HasDerivAt φ e s ∧ 0 < e := by
    intro s hs
    have hb0 : rad x ≤ P.2.1 + s * (Q - P).2.1 := by
      rw [hP1, hB1]; nlinarith [hs.1]
    have hb1 : P.2.1 + s * (Q - P).2.1 ≤ rad y := by
      rw [hP1, hB1]; nlinarith [hs.2]
    exact hasDerivAt_segHeight_pos hg (hx.trans_le hb0) (hb1.trans hy) hB hA hC hne'
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs =>
    (hder s hs).choose_spec.1.continuousAt.continuousWithinAt
  have hpos : ∀ s ∈ interior (Icc (0 : ℝ) 1), 0 < deriv φ s := by
    intro s hs
    rw [interior_Icc] at hs
    obtain ⟨e, he, he0⟩ := hder s (Ioo_subset_Icc_self hs)
    rw [he.deriv]; exact he0
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont hpos
  have hlt : φ 0 < φ 1 := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    zero_lt_one
  have e0 : φ 0 = heightAt g x θ₁ := by
    simp only [hφ, segHeight, zero_mul, add_zero, heightAt, hP0, hP1, hP2]
    have hθ : -(-(rad x * θ₁)) / rad x = θ₁ := by field_simp
    rw [hθ]
    ring
  have e1 : φ 1 = heightAt g y θ₂ := by
    simp only [hφ, segHeight, one_mul, Prod.fst_sub, Prod.snd_sub, add_sub_cancel, heightAt,
      hQ0, hQ1, hQ2]
    have hθ : -(-(rad y * θ₂)) / rad y = θ₂ := by field_simp
    rw [hθ]
    ring
  rw [← heightAt_eq_height hg.periodic h₁ hx, ← heightAt_eq_height hg.periodic h₂ hry, ← e0, ← e1]
  exact hlt

theorem height_le_of_le (hg : IsSpacelikeGraph g R) {x y : E0} (hxy : Le x y) (hx : 0 < rad x)
    (hy : rad y ≤ R) : height g x ≤ height g y := by
  rcases eq_or_ne x y with h | h
  · rw [h]
  · exact (height_lt_of_le hg hxy hx hy h).le

/-- **A spacelike graph is acausal** in `𝔼₀` (Lemma 2.7's « spacelike ⇒ acausal », B21 l.777). -/
theorem graph_acausal (hg : IsSpacelikeGraph g R) {x y : E0} (hx : x ∈ graphSet g R)
    (hy : y ∈ graphSet g R) (hxy : Le x y) : x = y := by
  by_contra hne
  have := height_lt_of_le hg hxy hx.1 hy.2.1 hne
  rw [hx.2.2, hy.2.2] at this
  exact lt_irrefl _ this

/-- `arg(−z) + π` is an angle of `z`. -/
theorem polar_neg_arg (y : E0) : Polar y (Complex.arg (-y.2) + π) := by
  unfold Polar
  have h := Complex.norm_mul_exp_arg_mul_I (-y.2)
  rw [norm_neg] at h
  have e : ((Complex.arg (-y.2) + π : ℝ) : ℂ) * Complex.I =
      (Complex.arg (-y.2) : ℂ) * Complex.I + π * Complex.I := by push_cast; ring
  have h' : y.2 = -((‖y.2‖ : ℂ) * Complex.exp ((Complex.arg (-y.2) : ℂ) * Complex.I)) := by
    rw [h, neg_neg]
  rw [e, Complex.exp_add, Complex.exp_pi_mul_I, rad]
  conv_lhs => rw [h']
  ring

/-- The height is continuous at every point of the region. -/
theorem continuousAt_height (hg : IsSpacelikeGraph g R) {x : E0} (hx : 0 < rad x)
    (hxR : rad x ≤ R) : ContinuousAt (height g) x := by
  have hgc : ∀ θ, ContinuousAt g (rad x, θ) := fun θ =>
    (hg.deriv (rad x, θ) hx hxR).choose_spec.1.continuousAt
  by_cases hs : x.2 ∈ Complex.slitPlane
  · have hpair : ContinuousAt (fun y : E0 => (rad y, Complex.arg y.2)) x :=
      continuous_rad.continuousAt.prodMk ((Complex.continuousAt_arg hs).comp
        continuous_snd.continuousAt)
    exact continuous_fst.continuousAt.sub ((hgc (Complex.arg x.2)).comp_of_eq hpair rfl)
  · have hx0 : x.2 ≠ 0 := fun h => by
      have := rad_pos.1 hx; exact this h
    have hs' : -x.2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      left
      have hre : x.2.re ≠ 0 := fun h => hx0 (Complex.ext h hs.2)
      simp only [Complex.neg_re]
      exact neg_pos.2 (lt_of_le_of_ne hs.1 hre)
    have hpair : ContinuousAt (fun y : E0 => (rad y, Complex.arg (-y.2) + π)) x :=
      continuous_rad.continuousAt.prodMk
        (((Complex.continuousAt_arg hs').comp_of_eq continuous_snd.continuousAt.neg rfl).add
          continuousAt_const)
    have hk : ContinuousAt (fun y : E0 => heightAt g y (Complex.arg (-y.2) + π)) x :=
      continuous_fst.continuousAt.sub ((hgc (Complex.arg (-x.2) + π)).comp_of_eq hpair rfl)
    refine hk.congr ?_
    filter_upwards [(isOpen_lt continuous_const continuous_rad).mem_nhds hx] with y hy
    exact heightAt_eq_height hg.periodic (polar_neg_arg y) hy

/-- **The K-3 arc lemma** (the monotonicity + IVT core of B21 Lemmas 2.9–2.10, SCOPE K-3; the
name is historical — B21 Cor 2.11 itself is `cor_intersect_number`): a continuous `≼`-increasing arc `c : [a, b] → 𝔼₀` of the region
`0 < r ≤ R` meets the spacelike graph `Σ*` in at most one point, and meets it iff the height changes
sign along it, `F(c a) ≤ 0 ≤ F(c b)`. The count of Lemma 2.10 is
`lem_intersect_number_complete`. -/
theorem cor_intersect (hg : IsSpacelikeGraph g R) {c : ℝ → E0} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b))
    (hmono : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ Icc a b, 0 < rad (c s) ∧ rad (c s) ≤ R) :
    (c '' Icc a b ∩ graphSet g R).Subsingleton ∧
      ((∃ s ∈ Icc a b, c s ∈ graphSet g R) ↔ height g (c a) ≤ 0 ∧ 0 ≤ height g (c b)) := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rintro _ ⟨⟨s, hs, rfl⟩, hps⟩ _ ⟨⟨t, ht, rfl⟩, hpt⟩
    rcases le_total s t with hst | hts
    · exact graph_acausal hg hps hpt (hmono s hs t ht hst)
    · exact (graph_acausal hg hpt hps (hmono t ht s hs hts)).symm
  · rintro ⟨s, hs, hcs⟩
    refine ⟨?_, ?_⟩
    · rw [← hcs.2.2]
      exact height_le_of_le hg (hmono a ha s hs hs.1) (hreg a ha).1 hcs.2.1
    · rw [← hcs.2.2]
      exact height_le_of_le hg (hmono s hs b hb hs.2) hcs.1 (hreg b hb).2
  · rintro ⟨h0, h1⟩
    have hcont : ContinuousOn (fun s => height g (c s)) (Icc a b) := fun s hs =>
      (continuousAt_height hg (hreg s hs).1 (hreg s hs).2).comp_continuousWithinAt (hc s hs)
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hab hcont ⟨h0, h1⟩
    exact ⟨s, hs, (hreg s hs).1, (hreg s hs).2, hs0⟩

/-- The library's causal curves of `𝔼₀` are `≼`-increasing in parameter order
(`Causal.CurveOn.rel_of_lt`). -/
theorem le_of_curveOn {W : TopologicalSpace.Opens E0} {c : ℝ → E0} {a b : ℝ}
    (hc : Causal.CurveOn (relOn Le) W c a b) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → Le (c s) (c t) := by
  intro s hs t ht hst
  rcases hst.lt_or_eq with h | h
  · exact (hc.rel_of_lt isRelFamily_le hs.1 h ht.2).2.2
  · rw [h]; exact le_refl' _

/-- **Non-vacuity of `cor_intersect`** (kb/0011): a vertical (future null) segment of the region
through `(g(r₀, θ), z₀)` meets the graph in exactly one point. -/
theorem vertical_meets_graph (hg : IsSpacelikeGraph g R) {z₀ : ℂ} (hz : 0 < ‖z₀‖)
    (hzR : ‖z₀‖ ≤ R) :
    let τ₀ := g (‖z₀‖, Complex.arg z₀)
    ((fun t : ℝ => ((t, z₀) : E0)) '' Icc (τ₀ - 1) (τ₀ + 1) ∩ graphSet g R).Subsingleton ∧
      ∃ t ∈ Icc (τ₀ - 1) (τ₀ + 1), ((t, z₀) : E0) ∈ graphSet g R := by
  intro τ₀
  have hab : τ₀ - 1 ≤ τ₀ + 1 := by linarith
  have hh : ∀ t : ℝ, height g ((t, z₀) : E0) = t - τ₀ := fun t => rfl
  obtain ⟨h1, h2⟩ := cor_intersect hg (c := fun t : ℝ => ((t, z₀) : E0)) hab
    (Continuous.continuousOn (by fun_prop))
    (fun s _ t _ hst => le_of_le (E0Spear.le_vertical_top (z := z₀) hst))
    (fun _ _ => ⟨hz, hzR⟩)
  refine ⟨h1, h2.2 ⟨?_, ?_⟩⟩
  · rw [hh]; linarith
  · rw [hh]; linarith

/-- **Lemma 2.6(ii)'s cusp is a spacelike graph of the blunt spear**, going to `+∞` at the axis
(the hypothesis `lim τ = +∞` of Lemma 2.10, l.900): it feeds `cor_intersect`. -/
theorem exists_cusp_isSpacelikeGraph {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) (R : ℝ) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ IsSpacelikeGraph τ R ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → 0 < τ p) ∧
      Tendsto τ (comap Prod.fst (𝓝[>] 0)) atTop := by
  obtain ⟨τ, hrim, hp, hpos', -, hδ, hlim⟩ := lem_curve_extension_ii hn hτ hper hpos (R := R)
  refine ⟨τ, hrim, ⟨hp, fun p hp0 _ => ?_⟩, hpos', hlim⟩
  obtain ⟨L, hL, h⟩ := hδ p hp0
  exact ⟨L, hL, (by positivity : (0 : ℝ) < 1 / p.1 ^ 2).trans_le h⟩

end Height

/-! ### §4 Lemma 2.8 — completeness of graphs over the punctured disc -/

section SurfaceComplete

open MeasureTheory

/-- **The development of a graph** over the strip `(0, R] × ℝ` (the universal cover of `𝔻_R^*`):
`(r, θ) ↦ D(g(r, θ), r, θ)`. -/
noncomputable def graphDev (g : ℝ × ℝ → ℝ) (R : ℝ) (p : {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ R}) :
    Causal.Minkowski 2 :=
  btzPaperDev (graphMap g p.1)

/-- **The key estimate of B21 Lemma 2.8(1)** (l.799–806): if `δ ≥ C²/r²` along a `C¹` curve
`γ = (r, θ)` of the strip, its length (the library's `Causal.Flat.localLength` of the developed
graph) is at least `C |log r(b) − log r(a)|`; in particular a finite-length curve stays away from
the axis, `r ≥ r(a) e^{−ℓ/C}`. -/
theorem log_rad_le_length {g : ℝ × ℝ → ℝ} {R C : ℝ} (hC : 0 ≤ C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    {γ γ' : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hreg : ∀ t ∈ Icc a b, 0 < (γ t).1 ∧ (γ t).1 ≤ R) :
    ENNReal.ofReal (C * |Real.log (γ b).1 - Real.log (γ a).1|) ≤
      Causal.Flat.localLength (fun _ y => btzPaperDev (graphMap g y)) γ a b := by
  have hγc : ContinuousOn γ (Icc a b) := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hγ1 : ContinuousOn (fun t => (γ t).1) (Icc a b) := continuous_fst.comp_continuousOn hγc
  have hγ'1 : ContinuousOn (fun t => (γ' t).1) (Icc a b) := continuous_fst.comp_continuousOn hγ'
  -- the lower density `C |r'| / r`
  set f : ℝ → ℝ := fun t => C * |(γ' t).1| / (γ t).1 with hf
  have hfc : ContinuousOn f (Icc a b) :=
    (continuousOn_const.mul hγ'1.abs).div hγ1 (fun t ht => (hreg t ht).1.ne')
  have hfint : IntegrableOn f (Ioc a b) :=
    (hfc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- pointwise: the density dominates `C |r'| / r`
  have hpt : ∀ t ∈ Icc a b, ENNReal.ofReal (f t) ≤
      Causal.Flat.localDensity (fun _ y => btzPaperDev (graphMap g y)) γ t := by
    intro t ht
    obtain ⟨L, hL, hδL⟩ := hδ (γ t) (hreg t ht).1 (hreg t ht).2
    obtain ⟨N, hN, -⟩ := hasFDerivAt_btzPaperNull (graphMap g (γ t))
    have hD : HasFDerivAt btzPaperDev ((LinearMap.toContinuousLinearMap
        (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).comp N) (graphMap g (γ t)) := by
      have hfun : btzPaperDev = (LinearMap.toContinuousLinearMap
          (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)) ∘ btzPaperNull :=
        funext fun q => btzPaperDev_eq_nullToMink q
      rw [hfun]
      exact (LinearMap.toContinuousLinearMap
        (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).hasFDerivAt.comp _ hN
    have hgm := hasFDerivAt_graphMap hL
    have hcomp := hD.differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hgm.comp_hasDerivAt t (hγ t ht))
    have hder : deriv (fun s => btzPaperDev (graphMap g (γ s))) t =
        fderiv ℝ btzPaperDev (graphMap g (γ t)) (fderiv ℝ (graphMap g) (γ t) (γ' t)) := by
      rw [hgm.fderiv]; exact hcomp.deriv
    unfold Causal.Flat.localDensity
    rw [hder, minkQ_fderiv_graph hL, graphQuad_eq (hreg t ht).1.ne']
    apply ENNReal.ofReal_le_ofReal
    have hr := (hreg t ht).1
    have hf0 : 0 ≤ f t := by simp only [hf]; positivity
    rw [Real.le_sqrt hf0 (by
      have := sq_nonneg (L (0, 1) / (γ t).1 * (γ' t).1 - (γ t).1 * (γ' t).2)
      have : 0 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) (γ t).1 :=
        (by positivity : (0 : ℝ) ≤ C ^ 2 / (γ t).1 ^ 2).trans hδL
      positivity)]
    have h1 : f t ^ 2 = C ^ 2 / (γ t).1 ^ 2 * (γ' t).1 ^ 2 := by
      simp only [hf]; rw [div_pow, mul_pow, sq_abs]; ring
    rw [h1]
    nlinarith [sq_nonneg (L (0, 1) / (γ t).1 * (γ' t).1 - (γ t).1 * (γ' t).2),
      mul_le_mul_of_nonneg_right hδL (sq_nonneg (γ' t).1)]
  -- integrate
  have hlint : ENNReal.ofReal (∫ t in Ioc a b, f t) ≤
      Causal.Flat.localLength (fun _ y => btzPaperDev (graphMap g y)) γ a b := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have := (hreg t (Ioc_subset_Icc_self ht)).1
      simp only [hf]; positivity)]
    unfold Causal.Flat.localLength
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpt t (Ioc_subset_Icc_self ht)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlint
  -- the fundamental theorem of calculus for `log r`
  have hftc : ∫ t in a..b, (γ' t).1 / (γ t).1 = Real.log (γ b).1 - Real.log (γ a).1 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.log (γ t).1)
      (fun t ht => ?_) ?_
    · rw [uIcc_of_le hab] at ht
      have h1 : HasDerivAt (fun s => (γ s).1) (γ' t).1 t :=
        (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hγ t ht)
      exact h1.log (hreg t ht).1.ne'
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact (hγ'1.div hγ1 (fun t ht => (hreg t ht).1.ne')).integrableOn_Icc
  have habs := intervalIntegral.abs_integral_le_integral_abs (f := fun t => (γ' t).1 / (γ t).1)
    (μ := MeasureTheory.volume) hab
  rw [hftc] at habs
  have heq : ∫ t in Ioc a b, f t = C * ∫ t in a..b, |(γ' t).1 / (γ t).1| := by
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have := (hreg t (Ioc_subset_Icc_self ht)).1
    simp only [hf, abs_div, abs_of_pos this]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left habs hC

/-! #### Infrastructure: the strip, coordinates of the development, lengths of Lipschitz paths -/

/-- **The strip** `{0 < r ≤ R}` of `ℝ × ℝ`, in coordinates `(r, θ)` (the universal cover of the
punctured disc `𝔻_R^*`). -/
def stripSet (R : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ R}

/-- The strip as a type (the domain of `graphDev`). -/
abbrev Strip (R : ℝ) : Type := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ R}

theorem convex_stripSet (R : ℝ) : Convex ℝ (stripSet R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [hx.1, hy.1]
    · rw [← ha'] at hab ⊢; simp only [zero_add] at hab; rw [hab]; simpa using hy.1
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have e : a * R + b * R = R := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

theorem uniqueDiffOn_stripSet {R : ℝ} (hR : 0 < R) : UniqueDiffOn ℝ (stripSet R) := by
  refine uniqueDiffOn_convex (convex_stripSet R) ⟨(R / 2, 0), mem_interior.2 ⟨Ioo 0 R ×ˢ univ,
    fun p hp => ⟨hp.1.1, hp.1.2.le⟩, isOpen_Ioo.prod isOpen_univ, ⟨⟨by linarith, by linarith⟩,
    mem_univ _⟩⟩⟩

/-- The `r`-coordinate of the development, `t − x` (`rCoordL_btzPaperDev`). -/
noncomputable def rCoordL : Causal.Minkowski 2 →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 2)) -
    (EuclideanSpace.proj (0 : Fin 2)).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2)))

/-- The `y`-coordinate of the development, `−rθ` (`yCoordL_btzPaperDev`). -/
noncomputable def yCoordL : Causal.Minkowski 2 →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2)).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 2)))

theorem rCoordL_btzPaperDev (p : ℝ × ℝ × ℝ) : rCoordL (btzPaperDev p) = p.2.1 := by
  simp [rCoordL, btzPaperDev]

theorem yCoordL_btzPaperDev (p : ℝ × ℝ × ℝ) : yCoordL (btzPaperDev p) = -(p.2.1 * p.2.2) := by
  simp [yCoordL, btzPaperDev]

theorem contDiff_btzPaperDev : ContDiff ℝ 1 btzPaperDev := by
  have hfun : btzPaperDev = (LinearMap.toContinuousLinearMap
      (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)) ∘ btzPaperNull :=
    funext fun q => btzPaperDev_eq_nullToMink q
  have hN : ContDiff ℝ 1 btzPaperNull := by unfold btzPaperNull; fun_prop
  rw [hfun]
  exact (LinearMap.toContinuousLinearMap
    (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).contDiff.comp hN

theorem differentiableAt_btzPaperDev (q : ℝ × ℝ × ℝ) : DifferentiableAt ℝ btzPaperDev q :=
  (contDiff_btzPaperDev.differentiable one_ne_zero) q

variable {g : ℝ × ℝ → ℝ} {R : ℝ}

/-- **The density of a curve of the strip** at a point where it is differentiable (velocity
`v = (dr, dθ)`), and `g` differentiable: `√(ds²_Σ(v))`, `ds²_Σ` the printed graph metric. -/
theorem localDensity_graphDev {γe : ℝ → Strip R} {t : ℝ} {v : ℝ × ℝ}
    (hγ : HasDerivAt (fun s => (γe s : ℝ × ℝ)) v t) {L : ℝ × ℝ →L[ℝ] ℝ}
    (hL : HasFDerivAt g L (γe t : ℝ × ℝ)) :
    Causal.Flat.localDensity (fun (_ : Strip R) z => graphDev g R z) γe t =
      ENNReal.ofReal (Real.sqrt (graphQuad (L (1, 0)) (L (0, 1)) (γe t : ℝ × ℝ).1 v.1 v.2)) := by
  have hgm := hasFDerivAt_graphMap hL
  have hcomp := (differentiableAt_btzPaperDev (graphMap g (γe t : ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt
    t (HasFDerivAt.comp_hasDerivAt (l := graphMap g) t hgm hγ)
  have hder : deriv (fun s => btzPaperDev (graphMap g (γe s : ℝ × ℝ))) t =
      fderiv ℝ btzPaperDev (graphMap g (γe t : ℝ × ℝ))
        (fderiv ℝ (graphMap g) (γe t : ℝ × ℝ) v) := by
    rw [hgm.fderiv]; exact hcomp.deriv
  unfold Causal.Flat.localDensity
  change ENNReal.ofReal (Real.sqrt (Causal.Flat.minkQ
    (deriv (fun s => btzPaperDev (graphMap g (γe s : ℝ × ℝ))) t))) = _
  rw [hder, minkQ_fderiv_graph hL]

/-- `√(ds²_Σ) ≥ k |dr|` when `δ ≥ k²`. -/
theorem mul_abs_le_sqrt_graphQuad {gr gθ r k u w : ℝ} (hr : 0 < r)
    (hδ : k ^ 2 ≤ spacelikeDelta gr gθ r) :
    k * |u| ≤ Real.sqrt (graphQuad gr gθ r u w) := by
  rw [graphQuad_eq hr.ne']
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg (gθ / r * u - r * w), mul_le_mul_of_nonneg_right hδ (sq_nonneg u)]

/-- `√(ds²_Σ) ≥ ρ |dθ| − (S/ρ) |dr|` when `r ≥ ρ > 0`, `|∂_θ τ| ≤ S` and `δ ≥ 0`. -/
theorem sub_le_sqrt_graphQuad {gr gθ r ρ S u w : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hS : |gθ| ≤ S)
    (hδ : 0 ≤ spacelikeDelta gr gθ r) :
    ρ * |w| - S / ρ * |u| ≤ Real.sqrt (graphQuad gr gθ r u w) := by
  have hr : 0 < r := hρ.trans_le hρr
  have h1 : |gθ / r * u - r * w| ≤ Real.sqrt (graphQuad gr gθ r u w) := by
    rw [graphQuad_eq hr.ne', ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hδ (sq_nonneg u)])
  have h2 : r * |w| - |gθ| / r * |u| ≤ |gθ / r * u - r * w| := by
    have := abs_sub_abs_le_abs_sub (r * w) (gθ / r * u)
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hr, abs_sub_comm] at this
    linarith
  have h3 : |gθ| / r * |u| ≤ S / ρ * |u| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg u)
    exact div_le_div₀ ((abs_nonneg _).trans hS) hS hρ hρr
  have h4 : ρ * |w| ≤ r * |w| := mul_le_mul_of_nonneg_right hρr (abs_nonneg w)
  linarith

/-- **The fundamental theorem of calculus for a length**: if `k |f'| ≤` the density a.e. on
`(a, b]`, `f` Lipschitz on `[a, b]`, then `k |f(b) − f(a)| ≤` the length over `(a, b]`
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). -/
theorem le_localLength_of_lipschitzOnWith {X : Type*} (φ : X → X → Causal.Minkowski 2)
    (c : ℝ → X) {f : ℝ → ℝ} {K : NNReal} {a b k : ℝ} (hab : a ≤ b) (hk : 0 ≤ k)
    (hf : LipschitzOnWith K f (Icc a b))
    (hd : ∀ᵐ t, t ∈ Ioc a b → ENNReal.ofReal (k * |deriv f t|) ≤ Causal.Flat.localDensity φ c t) :
    ENNReal.ofReal (k * |f b - f a|) ≤ Causal.Flat.localLength φ c a b := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    (uIcc_of_le hab ▸ hf).absolutelyContinuousOnInterval
  have hint : IntervalIntegrable (deriv f) MeasureTheory.volume a b := hac.intervalIntegrable_deriv
  have hftc := hac.integral_deriv_eq_sub
  have hint' : IntegrableOn (fun t => k * |deriv f t|) (Ioc a b) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hint).abs.const_mul k
  have h1 : k * |f b - f a| ≤ ∫ t in Ioc a b, k * |deriv f t| := by
    rw [MeasureTheory.integral_const_mul, ← hftc, ← intervalIntegral.integral_of_le hab]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.abs_integral_le_integral_abs hab) hk
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall fun t => by
    simp only [Pi.zero_apply]; positivity)]
  unfold Causal.Flat.localLength
  refine lintegral_mono_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae hd] with t ht h
  exact h ht

/-- **A path of the strip, Lipschitz in charts, has Lipschitz coordinates bounded away from the
axis**: through `r = rCoordL ∘ D`, `θ = −yCoordL ∘ D / r` and the compactness of `[0, 1]`. -/
theorem path_coords {x y : Strip R} (γ : Path x y)
    (hγ : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend) :
    ∃ m : ℝ, 0 < m ∧ (∀ t, m ≤ (γ.extend t : ℝ × ℝ).1) ∧
      ∃ K : NNReal, LipschitzWith K (fun t => (γ.extend t : ℝ × ℝ)) := by
  obtain ⟨K, hK⟩ := (Causal.Flat.isLocLip_pulled_iff _ γ).1 hγ
  have hmem : ∀ t, γ.extend t ∈ range γ := fun t => ⟨projIcc 0 1 zero_le_one t, rfl⟩
  have hcpt : IsCompact (range γ) := isCompact_range γ.continuous
  have hfc : Continuous fun z : Strip R => (z : ℝ × ℝ).1 := continuous_fst.comp continuous_subtype_val
  obtain ⟨z₀, -, hz₀⟩ := hcpt.exists_isMinOn (range_nonempty γ) hfc.continuousOn
  set m := (z₀ : ℝ × ℝ).1 with hm
  have hm0 : 0 < m := z₀.2.1
  have hmt : ∀ t, m ≤ (γ.extend t : ℝ × ℝ).1 := fun t => hz₀ (hmem t)
  have hyc : Continuous fun z : Strip R => (z : ℝ × ℝ).1 * (z : ℝ × ℝ).2 :=
    hfc.mul (continuous_snd.comp continuous_subtype_val)
  obtain ⟨Y, hY⟩ := hcpt.exists_bound_of_continuousOn hyc.continuousOn
  -- `r` and `y` are Lipschitz
  have hr : LipschitzWith (‖rCoordL‖₊ * K) fun t => (γ.extend t : ℝ × ℝ).1 := by
    have e : (fun t => (γ.extend t : ℝ × ℝ).1) = rCoordL ∘ fun t => graphDev g R (γ.extend t) := by
      funext t; simp only [Function.comp_apply, graphDev, rCoordL_btzPaperDev, graphMap]
    rw [e]; exact rCoordL.lipschitz.comp hK
  have hy : LipschitzWith (‖yCoordL‖₊ * K) fun t =>
      -((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2) := by
    have e : (fun t => -((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2)) =
        yCoordL ∘ fun t => graphDev g R (γ.extend t) := by
      funext t; simp only [Function.comp_apply, graphDev, yCoordL_btzPaperDev, graphMap]
    rw [e]; exact yCoordL.lipschitz.comp hK
  -- `θ = −y / r` on the box `[−Y, Y] × [m, R]`
  set B : Set (ℝ × ℝ) := Icc (-Y) Y ×ˢ Icc m R with hB
  have hdiv : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => -q.1 / q.2) B :=
    contDiffOn_fst.neg.div contDiffOn_snd (fun q hq => (hm0.trans_le hq.2.1).ne')
  obtain ⟨K', hK'⟩ := hdiv.exists_lipschitzOnWith one_ne_zero
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  have hyr := hy.prodMk hr
  have hθ : LipschitzWith (K' * max (‖yCoordL‖₊ * K) (‖rCoordL‖₊ * K))
      fun t => (γ.extend t : ℝ × ℝ).2 := by
    have hmaps : MapsTo (fun t => (-((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2),
        (γ.extend t : ℝ × ℝ).1)) univ B := by
      intro t _
      have h1 := hY _ (hmem t)
      rw [Real.norm_eq_abs] at h1
      refine ⟨⟨?_, ?_⟩, hmt t, (γ.extend t).2.2⟩
      · have := neg_abs_le (-((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2))
        rw [abs_neg] at this; linarith
      · have := le_abs_self (-((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2))
        rw [abs_neg] at this; linarith
    have e : (fun t => (γ.extend t : ℝ × ℝ).2) = (fun q : ℝ × ℝ => -q.1 / q.2) ∘
        (fun t => (-((γ.extend t : ℝ × ℝ).1 * (γ.extend t : ℝ × ℝ).2), (γ.extend t : ℝ × ℝ).1)) := by
      funext t
      have h0 : (γ.extend t : ℝ × ℝ).1 ≠ 0 := (γ.extend t).2.1.ne'
      simp only [Function.comp_apply]
      field_simp
    rw [e]; exact lipschitzOnWith_univ.1 (hK'.comp hyr.lipschitzOnWith hmaps)
  exact ⟨m, hm0, hmt, _, hr.prodMk hθ⟩


/-! #### Periodic functions on the annulus `[ρ, R] × ℝ` -/

/-- Integer-periodicity of `g` in `θ`. -/
theorem periodic_int (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) (n : ℤ) (r θ : ℝ) :
    g (r, θ + n * (2 * π)) = g (r, θ) :=
  (Function.Periodic.int_mul (show Function.Periodic (fun t => g (r, t)) (2 * π) from
    fun t => hper r t) n) θ

/-- **The derivative of a `θ`-periodic `g` is `θ`-periodic.** -/
theorem fderiv_periodic (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) (n : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ g (p.1, p.2 + n * (2 * π)) = fderiv ℝ g p := by
  have hfun : (fun q : ℝ × ℝ => g (q + (0, n * (2 * π)))) = g := by
    funext q
    have : q + ((0 : ℝ), (n : ℝ) * (2 * π)) = (q.1, q.2 + n * (2 * π)) := by
      ext <;> simp
    rw [this, periodic_int hper]
  have e : ((p.1, p.2 + n * (2 * π)) : ℝ × ℝ) = p + (0, n * (2 * π)) := by ext <;> simp
  rw [e, ← fderiv_comp_add_right, hfun]

/-- Every angle is an integer translate of one in `[0, 2π]`. -/
theorem exists_int_sub_mem_Icc (θ : ℝ) : ∃ n : ℤ, θ - n * (2 * π) ∈ Icc 0 (2 * π) := by
  refine ⟨toIcoDiv Real.two_pi_pos 0 θ, ?_⟩
  have h := toIcoMod_mem_Ico' Real.two_pi_pos θ
  rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul] at h
  exact ⟨h.1, h.2.le⟩

/-- A function on the strip, continuous and `θ`-periodic, is bounded on each annulus
`[ρ, R] × ℝ`, `ρ > 0`. -/
theorem exists_bound_annulus {h : ℝ × ℝ → ℝ} (hc : ContinuousOn h (stripSet R))
    (hp : ∀ (n : ℤ) (p : ℝ × ℝ), h (p.1, p.2 + n * (2 * π)) = h p) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ S, 0 ≤ S ∧ ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R → |h p| ≤ S := by
  have hB : Icc ρ R ×ˢ Icc 0 (2 * π) ⊆ stripSet R := fun q hq => ⟨hρ.trans_le hq.1.1, hq.1.2⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (hc.mono hB)
  refine ⟨max C 0, le_max_right _ _, fun p hp1 hp2 => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_sub_mem_Icc p.2
  have e : h p = h (p.1, (p.2 - n * (2 * π))) := by
    rw [← hp n (p.1, p.2 - n * (2 * π))]; simp
  rw [e, ← Real.norm_eq_abs]
  exact (hC _ (show ((p.1, p.2 - n * (2 * π)) : ℝ × ℝ) ∈ Icc ρ R ×ˢ Icc 0 (2 * π) from
    ⟨⟨hp1, hp2⟩, hn⟩)).trans (le_max_left _ _)

/-- A positive function on the strip, continuous and `θ`-periodic, is bounded below by a
positive constant on each annulus `[ρ, R] × ℝ`, `0 < ρ ≤ R`. -/
theorem exists_pos_le_annulus {h : ℝ × ℝ → ℝ} (hc : ContinuousOn h (stripSet R))
    (hp : ∀ (n : ℤ) (p : ℝ × ℝ), h (p.1, p.2 + n * (2 * π)) = h p)
    (hpos : ∀ p ∈ stripSet R, 0 < h p) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ∃ δ₀ > 0, ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R → δ₀ ≤ h p := by
  have hB : Icc ρ R ×ˢ Icc 0 (2 * π) ⊆ stripSet R := fun q hq => ⟨hρ.trans_le hq.1.1, hq.1.2⟩
  obtain ⟨q₀, hq₀, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(ρ, 0), ⟨le_rfl, hρR⟩, ⟨le_rfl, by positivity⟩⟩ (hc.mono hB)
  refine ⟨h q₀, hpos q₀ (hB hq₀), fun p hp1 hp2 => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_sub_mem_Icc p.2
  have e : h p = h (p.1, (p.2 - n * (2 * π))) := by
    rw [← hp n (p.1, p.2 - n * (2 * π))]; simp
  rw [e]
  exact hmin (show ((p.1, p.2 - n * (2 * π)) : ℝ × ℝ) ∈ Icc ρ R ×ˢ Icc 0 (2 * π) from
    ⟨⟨hp1, hp2⟩, hn⟩)

/-- **`C¹` on the strip, differentiable at its points: the derivative is continuous there.** -/
theorem continuousOn_fderiv_strip (hR : 0 < R) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p) :
    ContinuousOn (fderiv ℝ g) (stripSet R) :=
  (hC1.continuousOn_fderivWithin (uniqueDiffOn_stripSet hR) le_rfl).congr fun p hp =>
    ((hd p hp).fderivWithin (uniqueDiffOn_stripSet hR p hp)).symm

/-- `∂_θ g` is bounded on each annulus (B21 l.812's `sup_{𝔻_{r*} ∖ 𝔻_{r_*}} |∂_θ τ|`). -/
theorem exists_bound_dtheta (hR : 0 < R) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p) (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ S, 0 ≤ S ∧ ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R → |fderiv ℝ g p (0, 1)| ≤ S :=
  exists_bound_annulus ((continuousOn_fderiv_strip hR hC1 hd).clm_apply continuousOn_const)
    (fun n p => by rw [fderiv_periodic hper]) hρ

/-- **`F = D ∘ (g, id)` is Lipschitz on every compact convex subset of the strip.** -/
theorem exists_lipschitzOnWith_dev (hC1 : ContDiffOn ℝ 1 g (stripSet R)) {K : Set (ℝ × ℝ)}
    (hK : K ⊆ stripSet R) (hKc : Convex ℝ K) (hKk : IsCompact K) :
    ∃ L, LipschitzOnWith L (fun p => btzPaperDev (graphMap g p)) K := by
  have hG : ContDiffOn ℝ 1 (graphMap g) (stripSet R) :=
    hC1.prodMk (contDiffOn_fst.prodMk contDiffOn_snd)
  exact ((contDiff_btzPaperDev.comp_contDiffOn hG).mono hK).exists_lipschitzOnWith one_ne_zero
    hKc hKk

/-! #### Lower bounds for the pulled length -/

/-- **The log-estimate along a Lipschitz path** (B21 l.797–803, now for every path Lipschitz in
charts): `C |log r(b) − log r(a)| ≤ ℓ(γ|_{(a, b]})` under `δ ≥ C²/r²`. -/
theorem log_le_localLength {C : ℝ} (hC : 0 ≤ C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    {x y : Strip R} (γ : Path x y)
    (hγ : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend)
    {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (C * |Real.log (γ.extend b : ℝ × ℝ).1 - Real.log (γ.extend a : ℝ × ℝ).1|) ≤
      Causal.Flat.localLength (fun (_ : Strip R) z => graphDev g R z) γ.extend a b := by
  obtain ⟨m, hm, hmt, K, hK⟩ := path_coords γ hγ
  set c : ℝ → ℝ × ℝ := fun t => (γ.extend t : ℝ × ℝ) with hc
  have hr : LipschitzWith K fun t => (c t).1 := (LipschitzWith.prod_fst.comp hK).weaken
    (by simp)
  obtain ⟨K₁, hK₁⟩ := (Real.contDiffOn_log.mono (fun z (hz : z ∈ Icc m R) =>
    (hm.trans_le hz.1).ne')).exists_lipschitzOnWith one_ne_zero (convex_Icc m R) isCompact_Icc
  have hf : LipschitzOnWith (K₁ * K) (fun t => Real.log (c t).1) (Icc a b) :=
    hK₁.comp hr.lipschitzOnWith (fun t _ => ⟨hmt t, (γ.extend t).2.2⟩)
  refine le_localLength_of_lipschitzOnWith _ _ hab hC hf ?_
  filter_upwards [hK.ae_differentiableAt_real] with t ht _
  set v := deriv c t
  have hv : HasDerivAt c v t := ht.hasDerivAt
  have hr0 : 0 < (c t).1 := (γ.extend t).2.1
  obtain ⟨L, hL, hδL⟩ := hδ (c t) hr0 (γ.extend t).2.2
  rw [localDensity_graphDev hv hL]
  have h1 : HasDerivAt (fun s => (c s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  rw [(h1.log hr0.ne').deriv]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_abs_le_sqrt_graphQuad (u := v.1) (w := v.2) hr0 (k := C / (c t).1)
    (by rw [div_pow]; exact hδL)
  rw [abs_div, abs_of_pos hr0]
  calc C * (|v.1| / (c t).1) = C / (c t).1 * |v.1| := by ring
    _ ≤ _ := this

/-- **The angular estimate along a Lipschitz path** (B21 l.805–818): a path staying in the annulus
`r ≥ ρ`, where `|∂_θ g| ≤ S`, has `ρ / (1 + SR/(Cρ)) · |θ(1) − θ(0)| ≤ ℓ(γ)`. -/
theorem theta_le_pathLength {C : ℝ} (hC : 0 < C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    {ρ S : ℝ} (hρ : 0 < ρ) (hS0 : 0 ≤ S)
    (hS : ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R → |fderiv ℝ g p (0, 1)| ≤ S)
    {x y : Strip R} (γ : Path x y)
    (hγ : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend)
    (hρt : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ (γ.extend t : ℝ × ℝ).1) :
    ENNReal.ofReal (ρ / (1 + S * R / (C * ρ)) * |(y : ℝ × ℝ).2 - (x : ℝ × ℝ).2|) ≤
      Causal.Flat.pathLength (fun (_ : Strip R) z => graphDev g R z) γ := by
  obtain ⟨m, hm, hmt, K, hK⟩ := path_coords γ hγ
  set c : ℝ → ℝ × ℝ := fun t => (γ.extend t : ℝ × ℝ) with hc
  have hθ : LipschitzWith K fun t => (c t).2 := (LipschitzWith.prod_snd.comp hK).weaken
    (by simp)
  rw [Causal.Flat.pathLength_of_isLocLip _ hγ]
  have hR : ρ ≤ R := (hρt 0 ⟨le_rfl, zero_le_one⟩).trans (γ.extend 0).2.2
  have hden : 0 < 1 + S * R / (C * ρ) := by
    have : 0 ≤ S * R / (C * ρ) := by
      apply div_nonneg (mul_nonneg hS0 (hρ.le.trans hR)) (by positivity)
    linarith
  have key := le_localLength_of_lipschitzOnWith (fun (_ : Strip R) z => graphDev g R z)
    γ.extend zero_le_one (div_nonneg hρ.le hden.le) hθ.lipschitzOnWith (k := ρ / (1 + S * R / (C * ρ)))
    (f := fun t => (c t).2) ?_
  · simpa [hc, Path.extend_zero, Path.extend_one] using key
  filter_upwards [hK.ae_differentiableAt_real] with t ht htI
  set v := deriv c t
  have hv : HasDerivAt c v t := ht.hasDerivAt
  have hr0 : 0 < (c t).1 := (γ.extend t).2.1
  have hrR : (c t).1 ≤ R := (γ.extend t).2.2
  have hρr : ρ ≤ (c t).1 := hρt t (Ioc_subset_Icc_self htI)
  obtain ⟨L, hL, hδL⟩ := hδ (c t) hr0 hrR
  rw [localDensity_graphDev hv hL]
  have h2 : HasDerivAt (fun s => (c s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
  rw [h2.deriv]
  refine ENNReal.ofReal_le_ofReal ?_
  set D := Real.sqrt (graphQuad (L (1, 0)) (L (0, 1)) (c t).1 v.1 v.2)
  have hLS : |L (0, 1)| ≤ S := by rw [← hL.fderiv]; exact hS _ hρr hrR
  have hδ0 : 0 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) (c t).1 :=
    (by positivity : (0 : ℝ) ≤ C ^ 2 / (c t).1 ^ 2).trans hδL
  have hA := sub_le_sqrt_graphQuad (u := v.1) (w := v.2) hρ hρr hLS hδ0
  have hB := mul_abs_le_sqrt_graphQuad (w := v.2) (u := v.1) hr0 (k := C / (c t).1)
    (by rw [div_pow]; exact hδL)
  -- `|r'| ≤ (R/C) D`
  have hB' : |v.1| ≤ R / C * D := by
    have h1 : C / R * |v.1| ≤ C / (c t).1 * |v.1| :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC.le hr0 hrR) (abs_nonneg _)
    have h2 : C / R * |v.1| ≤ D := h1.trans hB
    have hR0 : 0 < R := hr0.trans_le hrR
    rw [div_mul_eq_mul_div, div_le_iff₀ hR0] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hC]
    linarith
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have : S / ρ * |v.1| ≤ S / ρ * (R / C * D) :=
    mul_le_mul_of_nonneg_left hB' (div_nonneg hS0 hρ.le)
  have e : S / ρ * (R / C * D) = D * (S * R / (C * ρ)) := by field_simp
  nlinarith

/-- **The radius stays above `r(0) e^{−L/C}`** along a path of length `≤ L` (B21 l.803). -/
theorem rad_ge_of_pathLength {C : ℝ} (hC : 0 < C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    {x y : Strip R} (γ : Path x y)
    (hγ : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : Causal.Flat.pathLength (fun (_ : Strip R) z => graphDev g R z) γ ≤ ENNReal.ofReal L)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (x : ℝ × ℝ).1 * Real.exp (-(L / C)) ≤ (γ.extend t : ℝ × ℝ).1 := by
  have h := log_le_localLength hC.le hδ γ hγ ht.1
  rw [Causal.Flat.pathLength_of_isLocLip _ hγ] at hL
  have hmono : Causal.Flat.localLength (fun (_ : Strip R) z => graphDev g R z) γ.extend 0 t ≤
      Causal.Flat.localLength (fun (_ : Strip R) z => graphDev g R z) γ.extend 0 1 :=
    MeasureTheory.lintegral_mono_set (Ioc_subset_Ioc_right ht.2)
  have h2 := (h.trans hmono).trans hL
  rw [ENNReal.ofReal_le_ofReal_iff hL0, Path.extend_zero] at h2
  have hx0 : 0 < (x : ℝ × ℝ).1 := x.2.1
  have hy0 : 0 < (γ.extend t : ℝ × ℝ).1 := (γ.extend t).2.1
  have h3 : Real.log (x : ℝ × ℝ).1 - L / C ≤ Real.log (γ.extend t : ℝ × ℝ).1 := by
    have := neg_abs_le (Real.log (γ.extend t : ℝ × ℝ).1 - Real.log (x : ℝ × ℝ).1)
    have h4 : |Real.log (γ.extend t : ℝ × ℝ).1 - Real.log (x : ℝ × ℝ).1| ≤ L / C := by
      rw [le_div_iff₀ hC]; linarith
    linarith
  calc (x : ℝ × ℝ).1 * Real.exp (-(L / C)) = Real.exp (Real.log (x : ℝ × ℝ).1 - L / C) := by
        rw [Real.exp_sub, Real.exp_log hx0, Real.exp_neg, ← div_eq_mul_inv]
    _ ≤ Real.exp (Real.log (γ.extend t : ℝ × ℝ).1) := Real.exp_le_exp.2 h3
    _ = _ := Real.exp_log hy0


/-! #### Distances of the pulled length -/

/-- A lower bound of every Lipschitz path is a lower bound of the pulled distance. -/
theorem le_edist_of_forall_path {P : ENNReal} {x y : Causal.Flat.PulledLength (graphDev g R)}
    (h : ∀ γ : Path (Causal.Flat.PulledLength.toSpace (graphDev g R) x) (Causal.Flat.PulledLength.toSpace (graphDev g R) y),
      Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend →
        P ≤ Causal.Flat.pathLength (fun (_ : Strip R) z => graphDev g R z) γ) :
    P ≤ edist x y := by
  change P ≤ ⨅ γ : Path (Causal.Flat.PulledLength.toSpace (graphDev g R) x)
    (Causal.Flat.PulledLength.toSpace (graphDev g R) y), Causal.Flat.pathLength _ γ
  refine le_iInf fun γ => ?_
  by_cases hγ : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) γ.extend
  · exact h γ hγ
  · rw [Causal.Flat.pathLength_of_not_isLocLip _ hγ]; exact le_top

theorem stripSegment_mem (x y : Strip R) (t : unitInterval) :
    (x : ℝ × ℝ) + (t : ℝ) • ((y : ℝ × ℝ) - x) ∈ stripSet R := by
  have h := convex_stripSet R x.2 y.2 (sub_nonneg.2 t.2.2) t.2.1 (by ring)
  have e : (x : ℝ × ℝ) + (t : ℝ) • ((y : ℝ × ℝ) - x) =
      (1 - (t : ℝ)) • (x : ℝ × ℝ) + (t : ℝ) • (y : ℝ × ℝ) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [e]; exact h

/-- **The straight segment of the strip** (the strip is convex). -/
noncomputable def stripSegment (x y : Strip R) : Path x y where
  toFun t := ⟨(x : ℝ × ℝ) + (t : ℝ) • ((y : ℝ × ℝ) - x), stripSegment_mem x y t⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

theorem stripSegment_extend_coe (x y : Strip R) (s : ℝ) :
    ((stripSegment x y).extend s : ℝ × ℝ) =
      (x : ℝ × ℝ) + (projIcc 0 1 zero_le_one s : ℝ) • ((y : ℝ × ℝ) - x) := rfl

theorem stripSegment_extend_mem (x y : Strip R) (s : ℝ) :
    ((stripSegment x y).extend s : ℝ × ℝ) ∈ segment ℝ (x : ℝ × ℝ) y := by
  rw [segment_eq_image', stripSegment_extend_coe]
  exact ⟨_, (projIcc 0 1 zero_le_one s).2, rfl⟩

theorem lipschitzWith_stripSegment (x y : Strip R) :
    LipschitzWith ‖(y : ℝ × ℝ) - x‖₊ fun s => ((stripSegment x y).extend s : ℝ × ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [stripSegment_extend_coe, stripSegment_extend_coe, dist_add_left, dist_eq_norm, ← sub_smul,
    norm_smul, Real.norm_eq_abs, coe_nnnorm, Real.dist_eq, mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (norm_nonneg _)

/-- **The pulled distance is at most `L` times the coordinate distance** along a segment on which
the development is `L`-Lipschitz. -/
theorem edist_le_of_segment {K : Set (ℝ × ℝ)} {L : NNReal}
    (hL : LipschitzOnWith L (fun p => btzPaperDev (graphMap g p)) K)
    (x y : Causal.Flat.PulledLength (graphDev g R))
    (hseg : segment ℝ (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ)
      (Causal.Flat.PulledLength.toSpace (graphDev g R) y) ⊆ K) :
    edist x y ≤ ENNReal.ofReal (L * dist (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ)
      (Causal.Flat.PulledLength.toSpace (graphDev g R) y)) := by
  set x' := Causal.Flat.PulledLength.toSpace (graphDev g R) x
  set y' := Causal.Flat.PulledLength.toSpace (graphDev g R) y
  have hlip : LipschitzWith (L * ‖(y' : ℝ × ℝ) - x'‖₊)
      fun t => graphDev g R ((stripSegment x' y').extend t) :=
    lipschitzOnWith_univ.1 (hL.comp (lipschitzWith_stripSegment x' y').lipschitzOnWith
      (fun s _ => hseg (stripSegment_extend_mem x' y' s)))
  have hloc : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z)
      (stripSegment x' y').extend := (Causal.Flat.isLocLip_pulled_iff _ _).2 ⟨_, hlip⟩
  change ⨅ γ : Path x' y', Causal.Flat.pathLength _ γ ≤ _
  refine (iInf_le _ (stripSegment x' y')).trans ?_
  rw [Causal.Flat.pathLength_of_isLocLip _ hloc, Causal.Flat.localLength_pulled]
  refine (Causal.Flat.lorentzLength_le_of_lipschitzWith hlip 0 1).trans_eq ?_
  congr 1
  rw [NNReal.coe_mul, coe_nnnorm, dist_eq_norm, norm_sub_rev]; ring

/-- **The log-estimate for the pulled distance**: `C |log r(y) − log r(x)| ≤ d(x, y)`. -/
theorem log_le_edist {C : ℝ} (hC : 0 ≤ C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    (x y : Causal.Flat.PulledLength (graphDev g R)) :
    ENNReal.ofReal (C * |Real.log (Causal.Flat.PulledLength.toSpace (graphDev g R) y : ℝ × ℝ).1 -
      Real.log (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).1|) ≤ edist x y := by
  refine le_edist_of_forall_path fun γ hγ => ?_
  have h := log_le_localLength hC hδ γ hγ zero_le_one
  rw [Path.extend_zero, Path.extend_one] at h
  rwa [Causal.Flat.pathLength_of_isLocLip _ hγ]

/-- **The angular estimate for the pulled distance**: below `L₀`, the distance controls the angle
(the path cannot reach the axis, `rad_ge_of_pathLength`, and `theta_le_pathLength` applies). -/
theorem theta_le_edist {C : ℝ} (hC : 0 < C)
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    {ρ S L₀ : ℝ} (hρ : 0 < ρ) (hS0 : 0 ≤ S) (hL₀ : 0 ≤ L₀)
    (hS : ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R → |fderiv ℝ g p (0, 1)| ≤ S)
    (x y : Causal.Flat.PulledLength (graphDev g R))
    (hρx : ρ ≤ (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).1 * Real.exp (-(L₀ / C))) :
    min (ENNReal.ofReal L₀) (ENNReal.ofReal (ρ / (1 + S * R / (C * ρ)) *
      |(Causal.Flat.PulledLength.toSpace (graphDev g R) y : ℝ × ℝ).2 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).2|)) ≤ edist x y := by
  refine le_edist_of_forall_path fun γ hγ => ?_
  by_cases hγL : Causal.Flat.pathLength (fun (_ : Strip R) z => graphDev g R z) γ ≤
      ENNReal.ofReal L₀
  · refine (min_le_right _ _).trans (theta_le_pathLength hC hδ hρ hS0 hS γ hγ fun t ht => ?_)
    exact hρx.trans (rad_ge_of_pathLength hC hδ γ hγ hL₀ hγL ht)
  · exact (min_le_left _ _).trans (not_le.1 hγL).le

/-- `C |log b − log a| ≤ L` forces `b ≥ a e^{−L/C}`. -/
theorem le_of_abs_log_sub_le {a b C L : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (h : C * |Real.log b - Real.log a| ≤ L) : a * Real.exp (-(L / C)) ≤ b := by
  have h3 : Real.log a - L / C ≤ Real.log b := by
    have := neg_abs_le (Real.log b - Real.log a)
    have h4 : |Real.log b - Real.log a| ≤ L / C := by rw [le_div_iff₀ hC]; linarith
    linarith
  calc a * Real.exp (-(L / C)) = Real.exp (Real.log a - L / C) := by
        rw [Real.exp_sub, Real.exp_log ha, Real.exp_neg, ← div_eq_mul_inv]
    _ ≤ Real.exp (Real.log b) := Real.exp_le_exp.2 h3
    _ = b := Real.exp_log hb


/-! #### Lemma 2.8(1) -/

/-- **B21 Lemma 2.8(1)** (`lem:surface_complete`, l.781–785, proof l.794–822), in the pulled-length
reading: `g` `C¹` on the strip (« piecewise smooth », one piece), `2π`-periodic, with
`δ ≥ C²/r²`: the graph is **spacelike** (Lemma 2.7, at every point) and its development over the
strip is **complete**. The proof is the printed one, made metric: a Cauchy sequence has `log r`
Cauchy (`log_le_edist`, l.797–803), hence stays in an annulus, hence has `θ` Cauchy
(`theta_le_edist`, l.805–818, with `sup |∂_θ τ|` over the annulus from `C¹` and periodicity); its
coordinate limit is a point of the strip, reached in the pulled length along segments
(`edist_le_of_segment`). -/
theorem lem_surface_complete_one {g : ℝ × ℝ → ℝ} {R C : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (hδ : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      C ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1) :
    (∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∀ v : ℝ × ℝ, v ≠ 0 → 0 < Causal.Flat.minkQ
        (fderiv ℝ btzPaperDev (graphMap g p) (fderiv ℝ (graphMap g) p v))) ∧
      CompleteSpace (Causal.Flat.PulledLength (graphDev g R)) := by
  refine ⟨fun p hp hpR v hv => ?_, ?_⟩
  · obtain ⟨L, hL, hδL⟩ := hδ p hp hpR
    exact (lem_surface_causal hL hp).2 ((by positivity : (0 : ℝ) < C ^ 2 / p.1 ^ 2).trans_le hδL)
      v hv
  have hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p := fun p hp =>
    (hδ p hp.1 hp.2).choose_spec.1.differentiableAt
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set z : ℕ → ℝ × ℝ := fun n => (Causal.Flat.PulledLength.toSpace (graphDev g R) (u n) : ℝ × ℝ)
    with hz
  have hz0 : ∀ n, 0 < (z n).1 := fun n => (Causal.Flat.PulledLength.toSpace (graphDev g R) (u n)).2.1
  have hzR : ∀ n, (z n).1 ≤ R := fun n => (Causal.Flat.PulledLength.toSpace (graphDev g R) (u n)).2.2
  have hlog : ∀ m n, ENNReal.ofReal (C * |Real.log (z n).1 - Real.log (z m).1|) ≤
      edist (u m) (u n) := fun m n => log_le_edist hC.le hδ (u m) (u n)
  -- the radius stays above `r₀`
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff.1 hu 1 one_pos
  set r₀ := (z N₀).1 * Real.exp (-(1 / C)) with hr₀
  have hr₀0 : 0 < r₀ := mul_pos (hz0 N₀) (Real.exp_pos _)
  have hrlow : ∀ n, N₀ ≤ n → r₀ ≤ (z n).1 := by
    intro n hn
    refine le_of_abs_log_sub_le (hz0 N₀) (hz0 n) hC ?_
    have h := (hlog N₀ n).trans (hN₀ N₀ le_rfl n hn).le
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h
  -- `log r` is Cauchy
  have hcs : CauchySeq fun n => Real.log (z n).1 := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.1 hu (ENNReal.ofReal (C * ε))
      (ENNReal.ofReal_pos.2 (mul_pos hC hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := (hlog m n).trans_lt (hN m hm n hn)
    rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hC hε)] at h
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_mul_lt_mul_left h hC.le
  obtain ⟨sL, hsL⟩ := cauchySeq_tendsto_of_complete hcs
  set rL := Real.exp sL with hrL
  have hrt : Tendsto (fun n => (z n).1) atTop (𝓝 rL) := by
    have := (Real.continuous_exp.tendsto sL).comp hsL
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, Real.exp_log (hz0 n)]
  have hrL0 : 0 < rL := Real.exp_pos _
  have hrLR : rL ≤ R := le_of_tendsto' hrt hzR
  -- `θ` is Cauchy
  set ρ := r₀ * Real.exp (-(1 / C)) with hρ
  have hρ0 : 0 < ρ := mul_pos hr₀0 (Real.exp_pos _)
  obtain ⟨S, hS0, hS⟩ := exists_bound_dtheta hR hC1 hd hper hρ0
  set k := ρ / (1 + S * R / (C * ρ)) with hk
  have hden : 0 < 1 + S * R / (C * ρ) := by
    have : 0 ≤ S * R / (C * ρ) := div_nonneg (mul_nonneg hS0 hR.le) (by positivity)
    linarith
  have hk0 : 0 < k := div_pos hρ0 hden
  have hθb : ∀ m n, N₀ ≤ m → min (ENNReal.ofReal 1) (ENNReal.ofReal (k * |(z n).2 - (z m).2|)) ≤
      edist (u m) (u n) := by
    intro m n hm
    refine theta_le_edist hC hδ hρ0 hS0 zero_le_one hS (u m) (u n) ?_
    exact mul_le_mul_of_nonneg_right (hrlow m hm) (Real.exp_pos _).le
  have hcθ : CauchySeq fun n => (z n).2 := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε' : 0 < min 1 (k * ε) := lt_min one_pos (mul_pos hk0 hε)
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.1 hu (ENNReal.ofReal (min 1 (k * ε)))
      (ENNReal.ofReal_pos.2 hε')
    refine ⟨max N N₀, fun m hm n hn => ?_⟩
    have h := (hθb m n (le_of_max_le_right hm)).trans_lt
      (hN m (le_of_max_le_left hm) n (le_of_max_le_left hn))
    rw [Real.dist_eq, abs_sub_comm]
    by_contra hcon
    push Not at hcon
    refine (not_le.2 h) (le_min ?_ ?_)
    · exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans
        (mul_le_mul_of_nonneg_left hcon hk0.le))
  obtain ⟨θL, hθL⟩ := cauchySeq_tendsto_of_complete hcθ
  -- the limit point
  set pL : Strip R := ⟨(rL, θL), hrL0, hrLR⟩ with hpL
  refine ⟨(Causal.Flat.PulledLength.toSpace (graphDev g R)).symm pL, ?_⟩
  have hzt : Tendsto z atTop (𝓝 (rL, θL)) := by
    have := hrt.prodMk_nhds hθL
    exact this.congr fun n => rfl
  set B : Set (ℝ × ℝ) := Icc (rL / 2) R ×ˢ Icc (θL - 1) (θL + 1) with hB
  have hBs : B ⊆ stripSet R := fun q hq => ⟨(half_pos hrL0).trans_le hq.1.1, hq.1.2⟩
  have hBc : Convex ℝ B := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨Lc, hLc⟩ := exists_lipschitzOnWith_dev hC1 hBs hBc (isCompact_Icc.prod isCompact_Icc)
  have hpLB : ((rL, θL) : ℝ × ℝ) ∈ B :=
    ⟨⟨by linarith, hrLR⟩, ⟨by linarith, by linarith⟩⟩
  have hev : ∀ᶠ n in atTop, z n ∈ B := by
    have h1 : ∀ᶠ n in atTop, rL / 2 < (z n).1 := hrt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ n in atTop, θL - 1 < (z n).2 := hθL.eventually (lt_mem_nhds (by linarith))
    have h3 : ∀ᶠ n in atTop, (z n).2 < θL + 1 := hθL.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2, h3] with n h1 h2 h3
    exact ⟨⟨h1.le, hzR n⟩, ⟨h2.le, h3.le⟩⟩
  rw [tendsto_iff_edist_tendsto_0]
  have hdist : Tendsto (fun n => ENNReal.ofReal (Lc * dist (z n) (rL, θL))) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (Lc : ℝ))).mul
      (tendsto_iff_dist_tendsto_zero.1 hzt)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdist
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hev] with n hn
  have := edist_le_of_segment hLc (u n) ((Causal.Flat.PulledLength.toSpace (graphDev g R)).symm pL)
    (hBc.segment_subset hn (by simpa using hpLB))
  simpa using this


/-! #### Lemma 2.8(2) -/

/-- `δ` (read with `fderiv g`) is continuous on the strip. -/
theorem continuousOn_delta (hR : 0 < R) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p) :
    ContinuousOn (fun p : ℝ × ℝ => spacelikeDelta (fderiv ℝ g p (1, 0)) (fderiv ℝ g p (0, 1)) p.1)
      (stripSet R) := by
  have hf := continuousOn_fderiv_strip hR hC1 hd
  have h1 : ContinuousOn (fun p => fderiv ℝ g p (1, 0)) (stripSet R) :=
    hf.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun p => fderiv ℝ g p (0, 1)) (stripSet R) :=
    hf.clm_apply continuousOn_const
  unfold spacelikeDelta
  exact (continuousOn_const.sub (continuousOn_const.mul h1)).sub
    ((h2.div continuousOn_fst fun p hp => hp.1.ne').pow 2)

/-- **`δ` is bounded below by a positive constant on each annulus** of a `C¹` spacelike graph. -/
theorem exists_delta_pos_annulus (hR : 0 < R) (hg : IsSpacelikeGraph g R)
    (hC1 : ContDiffOn ℝ 1 g (stripSet R)) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ∃ δ₀ > 0, ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R →
      δ₀ ≤ spacelikeDelta (fderiv ℝ g p (1, 0)) (fderiv ℝ g p (0, 1)) p.1 := by
  have hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p := fun p hp =>
    (hg.deriv p hp.1 hp.2).choose_spec.1.differentiableAt
  refine exists_pos_le_annulus (continuousOn_delta hR hC1 hd) (fun n p => ?_) (fun p hp => ?_) hρ hρR
  · simp only [fderiv_periodic hg.periodic]
  · obtain ⟨L, hL, hδ⟩ := hg.deriv p hp.1 hp.2
    rwa [hL.fderiv]

/-- **A path from `r ≥ ρ` to `r ≤ ρ` is long**: where `δ ≥ δ₀` on the annulus `r ≥ ρ`, the pulled
distance is at least `√δ₀ (r(x) − ρ)` (the clamped radius `max(r, ρ)` is Lipschitz, with
derivative `r'` above `ρ` and `0` elsewhere). -/
theorem clamp_le_edist (hg : IsSpacelikeGraph g R) {ρ δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hδ₀le : ∀ p : ℝ × ℝ, ρ ≤ p.1 → p.1 ≤ R →
      δ₀ ≤ spacelikeDelta (fderiv ℝ g p (1, 0)) (fderiv ℝ g p (0, 1)) p.1)
    (x y : Causal.Flat.PulledLength (graphDev g R))
    (hx : ρ ≤ (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).1)
    (hy : (Causal.Flat.PulledLength.toSpace (graphDev g R) y : ℝ × ℝ).1 ≤ ρ) :
    ENNReal.ofReal (Real.sqrt δ₀ *
      ((Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).1 - ρ)) ≤ edist x y := by
  refine le_edist_of_forall_path fun γ hγ => ?_
  obtain ⟨m, -, -, K, hK⟩ := path_coords γ hγ
  set c : ℝ → ℝ × ℝ := fun t => (γ.extend t : ℝ × ℝ) with hc
  set f : ℝ → ℝ := fun t => max (c t).1 ρ with hf
  have hfl : LipschitzWith K f := ((LipschitzWith.prod_fst.comp hK).weaken (by simp)).max_const ρ
  rw [Causal.Flat.pathLength_of_isLocLip _ hγ]
  have key := le_localLength_of_lipschitzOnWith (fun (_ : Strip R) z => graphDev g R z)
    γ.extend zero_le_one (Real.sqrt_nonneg δ₀) hfl.lipschitzOnWith (f := f) ?_
  · have e1 : f 1 = ρ := by
      simp only [hf, hc, Path.extend_one]; exact max_eq_right hy
    have e0 : f 0 = (Causal.Flat.PulledLength.toSpace (graphDev g R) x : ℝ × ℝ).1 := by
      simp only [hf, hc, Path.extend_zero]; exact max_eq_left hx
    rw [e1, e0, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx)] at key
    exact key
  filter_upwards [hK.ae_differentiableAt_real] with t ht _
  have hcc : Continuous c := hK.continuous
  rcases lt_or_ge ρ (c t).1 with hlt | hle
  · -- above `ρ`: `f = r` near `t`
    have hev : f =ᶠ[𝓝 t] fun s => (c s).1 := by
      filter_upwards [(continuous_fst.comp hcc).continuousAt.eventually (lt_mem_nhds hlt)] with s hs
      exact max_eq_left hs.le
    set v := deriv c t
    have hv : HasDerivAt c v t := ht.hasDerivAt
    have h1 : HasDerivAt (fun s => (c s).1) v.1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hv
    rw [hev.deriv_eq, h1.deriv]
    have hr0 : 0 < (c t).1 := (γ.extend t).2.1
    obtain ⟨L, hL, -⟩ := hg.deriv (c t) hr0 (γ.extend t).2.2
    rw [localDensity_graphDev hv hL]
    refine ENNReal.ofReal_le_ofReal (mul_abs_le_sqrt_graphQuad hr0 ?_)
    rw [Real.sq_sqrt hδ₀, ← hL.fderiv]
    exact hδ₀le _ hlt.le (γ.extend t).2.2
  · -- at or below `ρ`: `f` has a local minimum at `t`, so `f' = 0`
    have hmin : IsLocalMin f t := Eventually.of_forall fun s => by
      simp only [hf, max_eq_right hle]; exact le_max_right _ _
    rw [hmin.deriv_eq_zero, abs_zero, mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- `√X ≤ (1 + 2π²) dr − dτ` along a straight piece of a curve `r ↦ (r, θ(r))` with
`dr ≥ r_b / 2`, `r ≤ r_b`, `|dθ| ≤ π` (B21 l.842–844's bound `ℓ ≤ ∫ √(5 − 2τ')`, with the
constant the stated slope `|θ'| ≤ 2π/r_n` gives: `1 + 4π²` in place of `5`). -/
theorem sqrt_graphQuad_le_seg {gr gθ r rb u w : ℝ} (hu : 0 < u) (hub : rb / 2 ≤ u) (hr : 0 < r)
    (hrb : r ≤ rb) (hw : |w| ≤ π) (hX : 0 ≤ graphQuad gr gθ r u w) :
    Real.sqrt (graphQuad gr gθ r u w) ≤ (1 + 2 * π ^ 2) * u - (u * gr + w * gθ) := by
  set X := graphQuad gr gθ r u w with hXdef
  have hs := Real.sq_sqrt hX
  have h1 : 2 * u * Real.sqrt X ≤ X + u ^ 2 := by nlinarith [sq_nonneg (Real.sqrt X - u)]
  have hw2 : w ^ 2 ≤ π ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
  have hr2 : r ^ 2 ≤ 4 * u ^ 2 := by nlinarith
  have h2 : r ^ 2 * w ^ 2 ≤ 4 * u ^ 2 * π ^ 2 :=
    mul_le_mul hr2 hw2 (sq_nonneg w) (by positivity)
  have hXe : X = -2 * (gr * u + gθ * w) * u + u ^ 2 + r ^ 2 * w ^ 2 := rfl
  have h3 : 2 * u * Real.sqrt X ≤ 2 * u * ((1 + 2 * π ^ 2) * u - (u * gr + w * gθ)) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- **The length of a straight piece** `a → b` of the strip with `r_b − r_a ≥ r_b/2` and
`|θ_b − θ_a| ≤ π` is at most `(1 + 2π²)(r_b − r_a) − (τ(b) − τ(a))` (B21 l.842–848). -/
theorem edist_le_seg (hR : 0 < R) (hg : IsSpacelikeGraph g R) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (a b : Causal.Flat.PulledLength (graphDev g R))
    (hab : (Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 / 2 ≤
      (Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1)
    (hθ : |(Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).2 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).2| ≤ π) :
    0 ≤ (1 + 2 * π ^ 2) * ((Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1) -
        (g (Causal.Flat.PulledLength.toSpace (graphDev g R) b) -
          g (Causal.Flat.PulledLength.toSpace (graphDev g R) a)) ∧
    edist a b ≤ ENNReal.ofReal ((1 + 2 * π ^ 2) *
      ((Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1) -
        (g (Causal.Flat.PulledLength.toSpace (graphDev g R) b) -
          g (Causal.Flat.PulledLength.toSpace (graphDev g R) a))) := by
  set x' := Causal.Flat.PulledLength.toSpace (graphDev g R) a
  set y' := Causal.Flat.PulledLength.toSpace (graphDev g R) b
  set V : ℝ × ℝ := (y' : ℝ × ℝ) - x' with hV
  have hd : ∀ p ∈ stripSet R, DifferentiableAt ℝ g p := fun p hp =>
    (hg.deriv p hp.1 hp.2).choose_spec.1.differentiableAt
  have hfc := continuousOn_fderiv_strip hR hC1 hd
  set pt : ℝ → ℝ × ℝ := fun s => (x' : ℝ × ℝ) + s • V with hpt
  have hptm : ∀ s ∈ Icc (0 : ℝ) 1, pt s ∈ stripSet R := fun s hs =>
    stripSegment_mem x' y' ⟨s, hs⟩
  have hptd : ∀ s, HasDerivAt pt V s := fun s => by
    have := ((hasDerivAt_id s).smul_const V).const_add (x' : ℝ × ℝ)
    simp only [id, one_smul] at this
    exact this
  set φ' : ℝ → ℝ := fun s => fderiv ℝ g (pt s) V with hφ'
  have hφ'c : ContinuousOn φ' (Icc 0 1) :=
    (hfc.comp (by fun_prop : Continuous pt).continuousOn hptm).clm_apply continuousOn_const
  have hφd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => g (pt s)) (φ' s) s := fun s hs =>
    ((hd _ (hptm s hs)).hasFDerivAt.comp_hasDerivAt s (hptd s))
  have hr0 : 0 < (x' : ℝ × ℝ).1 := x'.2.1
  have hu : 0 < V.1 := by
    have := y'.2.1
    simp only [hV, Prod.fst_sub]; linarith
  -- pointwise
  have hpw : ∀ s ∈ Icc (0 : ℝ) 1, Real.sqrt (graphQuad (fderiv ℝ g (pt s) (1, 0))
      (fderiv ℝ g (pt s) (0, 1)) (pt s).1 V.1 V.2) ≤ (1 + 2 * π ^ 2) * V.1 - φ' s := by
    intro s hs
    have hm := hptm s hs
    obtain ⟨L, hL, hδL⟩ := hg.deriv (pt s) hm.1 hm.2
    have hLf : fderiv ℝ g (pt s) = L := hL.fderiv
    have hφe : φ' s = V.1 * L (1, 0) + V.2 * L (0, 1) := by
      simp only [hφ', hLf]; rw [← clm_apply_pair]
    rw [hφe, hLf]
    have hab' : (y' : ℝ × ℝ).1 / 2 ≤ V.1 := by simpa [hV] using hab
    have hθ' : |V.2| ≤ π := by simpa [hV] using hθ
    refine sqrt_graphQuad_le_seg hu hab' hm.1 ?_ hθ' ?_
    · simp only [hpt, Prod.fst_add, Prod.smul_fst, smul_eq_mul, hV, Prod.fst_sub]
      nlinarith [hs.1, hs.2]
    · rw [graphQuad_eq hm.1.ne']
      nlinarith [sq_nonneg (L (0, 1) / (pt s).1 * V.1 - (pt s).1 * V.2), sq_nonneg V.1]
  have hint : IntervalIntegrable φ' MeasureTheory.volume 0 1 :=
    (hφ'c.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  have hftc : ∫ s in (0 : ℝ)..1, φ' s = g y' - g x' := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hφd s
      (by rwa [uIcc_of_le zero_le_one] at hs)) hint]
    simp [hpt, hV]
  set T := (1 + 2 * π ^ 2) * V.1 - (g y' - g x') with hT
  have hTi : ∫ s in Ioc (0 : ℝ) 1, ((1 + 2 * π ^ 2) * V.1 - φ' s) = T := by
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_sub
      intervalIntegrable_const hint, hftc]
    simp [hT]
  have hnn : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (1 + 2 * π ^ 2) * V.1 - φ' s := fun s hs =>
    (Real.sqrt_nonneg _).trans (hpw s hs)
  have hIi : IntegrableOn (fun s => (1 + 2 * π ^ 2) * V.1 - φ' s) (Ioc 0 1) :=
    ((continuousOn_const.sub hφ'c).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hTe : (1 + 2 * π ^ 2) * ((y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1) - (g y' - g x') = T := by
    simp [hT, hV]
  rw [hTe]
  refine ⟨?_, ?_⟩
  · rw [← hTi]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun s hs =>
      hnn s (Ioc_subset_Icc_self hs)
  -- the length of the segment
  obtain ⟨Lc, hLc⟩ := exists_lipschitzOnWith_dev hC1
    ((convex_stripSet R).segment_subset x'.2 y'.2) (convex_segment _ _)
    (by rw [segment_eq_image']; exact isCompact_Icc.image (by fun_prop))
  have hlip : LipschitzWith (Lc * ‖(y' : ℝ × ℝ) - x'‖₊)
      fun t => graphDev g R ((stripSegment x' y').extend t) :=
    lipschitzOnWith_univ.1 (hLc.comp (lipschitzWith_stripSegment x' y').lipschitzOnWith
      (fun s _ => stripSegment_extend_mem x' y' s))
  have hloc : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z)
      (stripSegment x' y').extend := (Causal.Flat.isLocLip_pulled_iff _ _).2 ⟨_, hlip⟩
  change ⨅ γ : Path x' y', Causal.Flat.pathLength _ γ ≤ _
  refine (iInf_le _ (stripSegment x' y')).trans ?_
  rw [Causal.Flat.pathLength_of_isLocLip _ hloc, ← hTi,
    ofReal_integral_eq_lintegral_ofReal hIi (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      exact hnn s (Ioc_subset_Icc_self hs))]
  unfold Causal.Flat.localLength
  refine MeasureTheory.lintegral_mono_ae ?_
  have hae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)), s ∈ Ioo (0 : ℝ) 1 := by
    rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [hae] with s hs
  have hev : (fun s => ((stripSegment x' y').extend s : ℝ × ℝ)) =ᶠ[𝓝 s] pt := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
    rw [stripSegment_extend_coe, projIcc_of_mem _ ⟨hs'.1.le, hs'.2.le⟩]
  have hσd : HasDerivAt (fun s => ((stripSegment x' y').extend s : ℝ × ℝ)) V s :=
    (hptd s).congr_of_eventuallyEq hev
  have hps : ((stripSegment x' y').extend s : ℝ × ℝ) = pt s := hev.eq_of_nhds
  have hm := hptm s (Ioo_subset_Icc_self hs)
  have hfd : HasFDerivAt g (fderiv ℝ g (pt s)) ((stripSegment x' y').extend s : ℝ × ℝ) := by
    rw [hps]; exact (hd _ hm).hasFDerivAt
  rw [localDensity_graphDev hσd hfd, hps]
  exact ENNReal.ofReal_le_ofReal (hpw s (Ioo_subset_Icc_self hs))


/-- **B21 Lemma 2.8(2)** (`lem:surface_complete`, l.786–788, proof l.823–850), in the pulled-length
reading: a `C¹` spacelike graph over the strip whose development is complete goes to `+∞` at the
axis. The printed proof by contraposition: if `τ < A` along `(r_n, θ_n) → 0`, with
`r_{n+1} < r_n / 2` and the angles realigned so that `|θ_{n+1} − θ_n| ≤ π` (l.828–834), the broken
line through the `(r_n, θ_n)` has finite length, `ℓ ≤ (1 + 2π²) R − τ(r_0) + A` (`edist_le_seg`,
l.842–848, telescoping); so the points form a Cauchy sequence, which converges by completeness to a
point at positive radius, and they cannot approach it (`clamp_le_edist`). -/
theorem lem_surface_complete_two {g : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hg : IsSpacelikeGraph g R) (hC1 : ContDiffOn ℝ 1 g (stripSet R))
    (hcomp : CompleteSpace (Causal.Flat.PulledLength (graphDev g R))) :
    Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop := by
  rw [tendsto_atTop]
  intro A
  by_contra hA
  rw [Filter.not_eventually] at hA
  have hfreq : ∀ ε : ℝ, ∃ p : ℝ × ℝ, 0 < ε → 0 < p.1 ∧ p.1 < ε ∧ g p < A := by
    intro ε
    by_cases hε : 0 < ε
    · have hmem : {p : ℝ × ℝ | p.1 ∈ Ioo 0 ε} ∈ comap Prod.fst (𝓝[>] (0 : ℝ)) :=
        preimage_mem_comap (Ioo_mem_nhdsGT hε)
      obtain ⟨p, hp1, hp2⟩ := (hA.and_eventually hmem).exists
      exact ⟨p, fun _ => ⟨hp2.1, hp2.2, not_le.1 hp1⟩⟩
    · exact ⟨0, fun h => absurd h hε⟩
  choose P hP using hfreq
  -- the sequence, realigned
  set step : ℝ × ℝ → ℝ × ℝ := fun q =>
    ((P (q.1 / 2)).1, q.2 + toIcoMod Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2)) with hstep
  set u : ℕ → ℝ × ℝ := fun n => step^[n] (P R) with hu
  have hu0 : u 0 = P R := rfl
  have husucc : ∀ n, u (n + 1) = step (u n) := fun n => Function.iterate_succ_apply' _ _ _
  have hstep_g : ∀ q : ℝ × ℝ, g (step q) = g (P (q.1 / 2)) := by
    intro q
    have e : q.2 + toIcoMod Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2) =
        (P (q.1 / 2)).2 + ((-toIcoDiv Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2) : ℤ) : ℝ) *
          (2 * π) := by
      rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]; push_cast; ring
    simp only [hstep]
    rw [e, periodic_int hg.periodic]
  have hstep_θ : ∀ q : ℝ × ℝ, |(step q).2 - q.2| ≤ π := by
    intro q
    have h := toIcoMod_mem_Ico Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2)
    simp only [hstep, add_sub_cancel_left]
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hinv : ∀ n, 0 < (u n).1 ∧ (u n).1 < R ∧ g (u n) < A := by
    intro n
    induction n with
    | zero => exact hP R hR
    | succ n ih =>
      rw [husucc]
      obtain ⟨h1, h2, h3⟩ := hP ((u n).1 / 2) (half_pos ih.1)
      refine ⟨h1, by linarith [ih.2.1], ?_⟩
      rw [hstep_g]; exact h3
  have hhalf : ∀ n, (u (n + 1)).1 < (u n).1 / 2 := by
    intro n; rw [husucc]; exact (hP ((u n).1 / 2) (half_pos (hinv n).1)).2.1
  -- the points of the pulled length
  set w : ℕ → Causal.Flat.PulledLength (graphDev g R) := fun n =>
    (Causal.Flat.PulledLength.toSpace (graphDev g R)).symm ⟨u n, (hinv n).1, (hinv n).2.1.le⟩
    with hw
  have hwc : ∀ n, (Causal.Flat.PulledLength.toSpace (graphDev g R) (w n) : ℝ × ℝ) = u n :=
    fun n => rfl
  set T : ℕ → ℝ := fun n => (1 + 2 * π ^ 2) * ((u n).1 - (u (n + 1)).1) - (g (u n) - g (u (n + 1)))
    with hT
  have hseg : ∀ n, 0 ≤ T n ∧ edist (w (n + 1)) (w n) ≤ ENNReal.ofReal (T n) := by
    intro n
    have h := edist_le_seg hR hg hC1 (w (n + 1)) (w n)
      (by rw [hwc, hwc]; linarith [hhalf n])
      (by rw [hwc, hwc, husucc, abs_sub_comm]; exact hstep_θ (u n))
    rw [hwc, hwc] at h
    exact h
  have hsum : Summable T := by
    refine summable_of_sum_range_le (c := (1 + 2 * π ^ 2) * R - g (u 0) + A)
      (fun n => (hseg n).1) fun N => ?_
    have e : ∑ i ∈ Finset.range N, T i =
        ((1 + 2 * π ^ 2) * (u 0).1 - g (u 0)) - ((1 + 2 * π ^ 2) * (u N).1 - g (u N)) := by
      rw [← Finset.sum_range_sub' (fun i => (1 + 2 * π ^ 2) * (u i).1 - g (u i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hT]; ring
    rw [e]
    have := hinv N
    have h0 := hinv 0
    have hpi : 0 ≤ 1 + 2 * π ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h0.2.1.le hpi, mul_pos (by positivity : (0:ℝ) < 1 + 2 * π ^ 2) this.1]
  have hcs : CauchySeq w := by
    refine cauchySeq_of_edist_le_of_tsum_ne_top (fun n => ENNReal.ofReal (T n))
      (fun n => by rw [edist_comm]; exact (hseg n).2) ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hseg n).1) hsum]
    exact ENNReal.ofReal_ne_top
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  -- the limit is at positive radius; the points go to the axis
  set ra := (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1 with hra
  have hra0 : 0 < ra := (Causal.Flat.PulledLength.toSpace (graphDev g R) a).2.1
  have hraR : ra ≤ R := (Causal.Flat.PulledLength.toSpace (graphDev g R) a).2.2
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_delta_pos_annulus hR hg hC1 (half_pos hra0)
    ((half_le_self hra0.le).trans hraR)
  have hgeom : ∀ n, (u n).1 ≤ R * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using (hinv 0).2.1.le
    | succ n ih => rw [pow_succ]; nlinarith [hhalf n]
  have hto0 : Tendsto (fun n => R * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul R
  obtain ⟨N₁, hN₁⟩ := (hto0.eventually (gt_mem_nhds (half_pos hra0))).exists_forall_of_atTop
  set ε := ENNReal.ofReal (Real.sqrt δ₀ * (ra - ra / 2)) with hε
  have hεpos : 0 < ε := ENNReal.ofReal_pos.2 (mul_pos (Real.sqrt_pos.2 hδ₀) (by linarith))
  obtain ⟨N₂, hN₂⟩ := EMetric.tendsto_atTop.1 ha ε hεpos
  set n := max N₁ N₂
  have hlow := clamp_le_edist hg hδ₀.le hδ₀le a (w n) (half_le_self hra0.le)
    (by rw [hwc]; exact (hgeom n).trans (hN₁ n (le_max_left _ _)).le)
  rw [edist_comm] at hlow
  exact absurd (hN₂ n (le_max_right _ _)) (not_lt.2 hlow)


/-- **B21 Lemma 2.6(ii), in full** (`lem:curve_extension`, l.704–710, the construction printed as
the proof of (i), l.858–866): for `R > 0` and `τ^R` `C^n` (`n ≥ 1`), positive and `2π`-periodic,
there is `τ` on the strip extending `τ^R`, positive, periodic, `C^n`, whose graph is **spacelike**
(Lemma 2.7, `δ ≥ 1/r²`) and **complete** (Lemma 2.8(1) with `C = 1`), and which goes to `+∞` at
the axis. -/
theorem lem_curve_extension_ii_complete {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) {R : ℝ}
    (hR : 0 < R) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ IsSpacelikeGraph τ R ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → 0 < τ p) ∧ ContDiffOn ℝ n τ {p | 0 < p.1} ∧
      CompleteSpace (Causal.Flat.PulledLength (graphDev τ R)) ∧
      Tendsto τ (comap Prod.fst (𝓝[>] 0)) atTop := by
  obtain ⟨τ, hrim, hp, hpos', hC, hδ, hlim⟩ := lem_curve_extension_ii hn hτ hper hpos (R := R)
  have hδ1 : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt τ L p ∧
      (1 : ℝ) ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := fun p hp0 _ => by
    obtain ⟨L, hL, h⟩ := hδ p hp0
    exact ⟨L, hL, by simpa using h⟩
  have hC1 : ContDiffOn ℝ 1 τ (stripSet R) :=
    (hC.of_le hn).mono fun p hp => hp.1
  refine ⟨τ, hrim, ⟨hp, fun p hp0 _ => ?_⟩, hpos', hC,
    (lem_surface_complete_one hR one_pos hp hC1 hδ1).2, hlim⟩
  obtain ⟨L, hL, h⟩ := hδ p hp0
  exact ⟨L, hL, (by positivity : (0 : ℝ) < 1 / p.1 ^ 2).trans_le h⟩


/-! #### Lemma 2.10, cut by K-3: the intersection count -/

/-- Future causal relations of `𝔼₀` increase the time `τ`. -/
theorem fst_le_of_le {x y : E0} (h : Le x y) : x.1 ≤ y.1 := by
  have := h.norm_sub_le
  linarith [norm_nonneg (y.2 - x.2)]

/-- Future causal relations of `𝔼₀` increase the radius. -/
theorem rad_le_of_le {x y : E0} (h : Le x y) : rad x ≤ rad y := h.closed.2.1

/-- **A causal arc of any interval** of the region meets the spacelike graph in at most one point,
and meets it iff the height takes a value `≤ 0` and a value `≥ 0` along it (monotonicity + IVT). -/
theorem arc_meets_graph_iff (hg : IsSpacelikeGraph g R) {c : ℝ → E0} {I : Set ℝ}
    (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, 0 < rad (c s) ∧ rad (c s) ≤ R) :
    (c '' I ∩ graphSet g R).Subsingleton ∧
      ((∃ s ∈ I, c s ∈ graphSet g R) ↔
        (∃ t ∈ I, height g (c t) ≤ 0) ∧ ∃ t ∈ I, 0 ≤ height g (c t)) := by
  refine ⟨?_, ⟨fun ⟨s, hs, hcs⟩ => ⟨⟨s, hs, hcs.2.2.le⟩, ⟨s, hs, hcs.2.2.ge⟩⟩, ?_⟩⟩
  · rintro _ ⟨⟨s, hs, rfl⟩, hps⟩ _ ⟨⟨t, ht, rfl⟩, hpt⟩
    rcases le_total s t with hst | hts
    · exact graph_acausal hg hps hpt (hmono s hs t ht hst)
    · exact (graph_acausal hg hpt hps (hmono t ht s hs hts)).symm
  · rintro ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩
    rcases le_total t₁ t₂ with h12 | h21
    · have hsub : Icc t₁ t₂ ⊆ I := hI.out ht₁ ht₂
      obtain ⟨-, H⟩ := cor_intersect hg h12 (hc.mono hsub)
        (fun s hs t ht hst => hmono s (hsub hs) t (hsub ht) hst)
        (fun s hs => hreg s (hsub hs))
      obtain ⟨s, hs, hcs⟩ := H.2 ⟨h₁, h₂⟩
      exact ⟨s, hsub hs, hcs⟩
    · have hle := height_le_of_le hg (hmono t₂ ht₂ t₁ ht₁ h21) (hreg t₂ ht₂).1 (hreg t₁ ht₁).2
      exact ⟨t₂, ht₂, (hreg t₂ ht₂).1, (hreg t₂ ht₂).2, le_antisymm (hle.trans h₁) h₂⟩

/-- `g` is continuous on the strip (it is differentiable there). -/
theorem IsSpacelikeGraph.continuousOn (hg : IsSpacelikeGraph g R) : ContinuousOn g (stripSet R) :=
  fun p hp => (hg.deriv p hp.1 hp.2).choose_spec.1.continuousAt.continuousWithinAt

/-- **The past end on the axis** (B21 l.930–931, the role of `lim τ = +∞`): a causal arc of the
region approaching the axis has a point strictly below the graph. -/
theorem exists_height_neg_of_axis (hlim : Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop)
    {c : ℝ → E0} {I : Set ℝ} (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, 0 < rad (c s) ∧ rad (c s) ≤ R)
    (hax : ∀ ε > 0, ∃ t ∈ I, rad (c t) < ε) :
    ∃ t ∈ I, height g (c t) < 0 := by
  obtain ⟨t₀, ht₀, -⟩ := hax 1 one_pos
  set M := (c t₀).1
  obtain ⟨U, hU, hUs⟩ := mem_comap.1 (hlim.eventually (eventually_ge_atTop (M + 1)))
  obtain ⟨ε, hε, hεU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  obtain ⟨t, ht, hrt⟩ := hax (min ε (rad (c t₀))) (lt_min hε (hreg t₀ ht₀).1)
  have htt₀ : t ≤ t₀ := by
    by_contra h
    have := rad_le_of_le (hmono t₀ ht₀ t ht (not_le.1 h).le)
    linarith [min_le_right ε (rad (c t₀))]
  have hτ : (c t).1 ≤ M := fst_le_of_le (hmono t ht t₀ ht₀ htt₀)
  have hgM : M + 1 ≤ g (rad (c t), Complex.arg (c t).2) :=
    hUs (hεU ⟨(hreg t ht).1, hrt.trans_le (min_le_left _ _)⟩)
  refine ⟨t, ht, ?_⟩
  change (c t).1 - g (rad (c t), Complex.arg (c t).2) < 0
  linarith

/-- **The future end at `+∞`** (`sup(c) = +∞`, B21 l.917): a causal arc of the region along which
`τ` is unbounded has a point on or above the graph (`g` is bounded on the annulus the arc stays
in). -/
theorem exists_height_nonneg_of_unbounded (hg : IsSpacelikeGraph g R) {c : ℝ → E0} {I : Set ℝ}
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, 0 < rad (c s) ∧ rad (c s) ≤ R)
    (hinf : ∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) :
    ∃ t ∈ I, 0 ≤ height g (c t) := by
  obtain ⟨t₀, ht₀, -⟩ := hinf 0
  obtain ⟨S, -, hS⟩ := exists_bound_annulus hg.continuousOn
    (fun n p => periodic_int hg.periodic n p.1 p.2) (hreg t₀ ht₀).1
  obtain ⟨t, ht, hMt⟩ := hinf (max S ((c t₀).1 + 1))
  have ht₀t : t₀ ≤ t := by
    by_contra h
    have := fst_le_of_le (hmono t ht t₀ ht₀ (not_le.1 h).le)
    linarith [le_max_right S ((c t₀).1 + 1)]
  have hr := rad_le_of_le (hmono t₀ ht₀ t ht ht₀t)
  have hb := hS (rad (c t), Complex.arg (c t).2) hr (hreg t ht).2
  refine ⟨t, ht, ?_⟩
  change 0 ≤ (c t).1 - g (rad (c t), Complex.arg (c t).2)
  linarith [le_abs_self (g (rad (c t), Complex.arg (c t).2)), le_max_left S ((c t₀).1 + 1)]

/-- **On the rim `r = R`, `J⁺(C*)` is « on or above the graph »** (`C* = Σ* ∩ ∂S*`, B21 l.900):
`x ∈ J⁺(C*) ⟺ F(x) ≥ 0`. -/
theorem height_nonneg_iff_mem_Jplus_rim (hg : IsSpacelikeGraph g R) {x : E0} (hx : rad x = R)
    (hR : 0 < R) :
    0 ≤ height g x ↔ ∃ y ∈ graphSet g R, rad y = R ∧ Le y x := by
  constructor
  · intro h
    set y : E0 := (g (rad x, Complex.arg x.2), x.2)
    have hry : rad y = rad x := rfl
    refine ⟨y, ⟨by rw [hry, hx]; exact hR, by rw [hry, hx], ?_⟩, by rw [hry, hx], ?_⟩
    · change y.1 - g (rad y, Complex.arg y.2) = 0
      rw [hry]; exact sub_self _
    · have h' : y.1 ≤ x.1 := by
        change 0 ≤ x.1 - g (rad x, Complex.arg x.2) at h
        change g (rad x, Complex.arg x.2) ≤ x.1
        linarith
      exact le_of_le (E0Spear.le_vertical_top (z := x.2) h')
  · rintro ⟨y, hy, hyR, hyx⟩
    rw [← hy.2.2]
    exact height_le_of_le hg hyx hy.1 hx.le

open Classical in
/-- **B21 Lemma 2.10** (`lem:intersect_number_complete`, l.897–908), cut by K-3: for a spacelike
graph `Σ*` over the blunt spear with `lim τ = +∞` at the axis, and a future causal arc `c*` of the
region over an interval `I`, whose past end is in the past component `[p]` of the complement of
`Σ*` (read: a point strictly below `Σ*`, e.g. in the head, or an approach to the axis) and whose
future end is `sup(c*) = +∞` or a last point on the rim `∂S* = {r = R}` (read for « inextendible in
`Int S*`, a closed subset of `S*` »):
`|c* ∩ Σ*| = 1` if `sup(c*) ∈ J⁺(C*) ∪ {+∞}`, `0` otherwise. -/
theorem lem_intersect_number_complete (hg : IsSpacelikeGraph g R) (hR : 0 < R)
    (hlim : Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop)
    {c : ℝ → E0} {I : Set ℝ} (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, 0 < rad (c s) ∧ rad (c s) ≤ R)
    (hpast : (∃ t ∈ I, height g (c t) < 0) ∨ ∀ ε > 0, ∃ t ∈ I, rad (c t) < ε)
    (hfut : (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨ ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ rad (c b) = R) :
    (c '' I ∩ graphSet g R).ncard =
      if (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨
          ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ ∃ y ∈ graphSet g R, rad y = R ∧ Le y (c b)
        then 1 else 0 := by
  obtain ⟨hsub, hiff⟩ := arc_meets_graph_iff hg hI hc hmono hreg
  split_ifs with hcond
  · obtain ⟨t₁, ht₁, h₁⟩ : ∃ t ∈ I, height g (c t) < 0 := by
      rcases hpast with h | h
      · exact h
      · exact exists_height_neg_of_axis hlim hmono hreg h
    have h₂ : ∃ t ∈ I, 0 ≤ height g (c t) := by
      rcases hcond with h | ⟨b, hb, -, hJ⟩
      · exact exists_height_nonneg_of_unbounded hg hmono hreg h
      · rcases hfut with h' | ⟨b', hb', hmax', hrim'⟩
        · exact exists_height_nonneg_of_unbounded hg hmono hreg h'
        · refine ⟨b, hb, ?_⟩
          obtain ⟨y, hy, hyR, hyb⟩ := hJ
          rw [← hy.2.2]
          exact height_le_of_le hg hyb hy.1 (hreg b hb).2
    obtain ⟨s, hs, hcs⟩ := hiff.2 ⟨⟨t₁, ht₁, h₁.le⟩, h₂⟩
    rw [Set.ncard_eq_one]
    exact ⟨c s, hsub.eq_singleton_of_mem ⟨⟨s, hs, rfl⟩, hcs⟩⟩
  · rw [Set.ncard_eq_zero hsub.finite]
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨s, hs, rfl⟩, hcs⟩
    apply hcond
    rcases hfut with h | ⟨b, hb, hmax, hrim⟩
    · exact Or.inl h
    · refine Or.inr ⟨b, hb, hmax, (height_nonneg_iff_mem_Jplus_rim hg hrim hR).1 ?_⟩
      rw [← hcs.2.2]
      exact height_le_of_le hg (hmono s hs b hb (hmax s hs)) hcs.1 (hreg b hb).2


/-- **Non-vacuity of `lem_intersect_number_complete`** (kb/0011): the vertical future ray from
just below the graph meets it exactly once (`sup = +∞`). -/
theorem lem_intersect_number_complete_vertical (hg : IsSpacelikeGraph g R) (hR : 0 < R)
    (hlim : Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop) {z₀ : ℂ} (hz : 0 < ‖z₀‖)
    (hzR : ‖z₀‖ ≤ R) :
    ((fun t : ℝ => ((t, z₀) : E0)) '' Ici (g (‖z₀‖, Complex.arg z₀) - 1) ∩
      graphSet g R).ncard = 1 := by
  set τ₀ := g (‖z₀‖, Complex.arg z₀)
  have hinf : ∀ M : ℝ, ∃ t ∈ Ici (τ₀ - 1), M ≤ ((fun t : ℝ => ((t, z₀) : E0)) t).1 :=
    fun M => ⟨max M (τ₀ - 1), mem_Ici.2 (le_max_right _ _), le_max_left _ _⟩
  have h := lem_intersect_number_complete hg hR hlim (c := fun t : ℝ => ((t, z₀) : E0))
    (I := Ici (τ₀ - 1)) ordConnected_Ici (Continuous.continuousOn (by fun_prop))
    (fun s _ t _ hst => le_of_le (E0Spear.le_vertical_top (z := z₀) hst))
    (fun _ _ => ⟨hz, hzR⟩)
    (Or.inl ⟨τ₀ - 1, self_mem_Ici, by change τ₀ - 1 - τ₀ < 0; linarith⟩) (Or.inl hinf)
  rw [h, if_pos (Or.inl hinf)]

open Classical in
/-- **The spear-local surgery** (B21 Prop 2.17's proof, l.1090, inside one blunt spear): rim
data `τ^R` (`C^n`, `n ≥ 1`, positive, `2π`-periodic) extends to a spacelike graph `Σ*` over the
strip which is complete (Lemma 2.6(ii) + Lemma 2.8(1)) and meets every future causal arc of the
blunt spear with past end in `[p]` and future end at `+∞` or on the rim exactly as Lemma 2.10
prescribes. -/
theorem spear_surgery_local {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) {R : ℝ}
    (hR : 0 < R) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ IsSpacelikeGraph τ R ∧
      ContDiffOn ℝ n τ {p | 0 < p.1} ∧ CompleteSpace (Causal.Flat.PulledLength (graphDev τ R)) ∧
      ∀ {c : ℝ → E0} {I : Set ℝ}, I.OrdConnected → ContinuousOn c I →
        (∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t)) →
        (∀ s ∈ I, 0 < rad (c s) ∧ rad (c s) ≤ R) →
        ((∃ t ∈ I, height τ (c t) < 0) ∨ ∀ ε > 0, ∃ t ∈ I, rad (c t) < ε) →
        ((∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨ ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ rad (c b) = R) →
        (c '' I ∩ graphSet τ R).ncard =
          if (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨
              ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ ∃ y ∈ graphSet τ R, rad y = R ∧ Le y (c b)
            then 1 else 0 := by
  obtain ⟨τ, hrim, hg, -, hC, hcomp, hlim⟩ := lem_curve_extension_ii_complete hn hτ hper hpos hR
  exact ⟨τ, hrim, hg, hC, hcomp, fun hI hc hmono hreg hpast hfut =>
    lem_intersect_number_complete hg hR hlim hI hc hmono hreg hpast hfut⟩

end SurfaceComplete


/-! ### §4b Lemma 2.6(i), Lemma 2.9, Cor 2.11 — the compact disc (K-3) -/

section Disc

variable {g : ℝ × ℝ → ℝ} {R : ℝ}

/-- `x ↦ h(r, θ)` read with the principal angle is continuous at a point off the axis where `h` is
continuous at every angle (`h` `2π`-periodic). -/
theorem continuousAt_polarEval {h : ℝ × ℝ → ℝ} (hper : ∀ r θ, h (r, θ + 2 * π) = h (r, θ))
    {x : E0} (hx : 0 < rad x) (hc : ∀ θ, ContinuousAt h (rad x, θ)) :
    ContinuousAt (fun y : E0 => h (rad y, Complex.arg y.2)) x := by
  by_cases hs : x.2 ∈ Complex.slitPlane
  · have hpair : ContinuousAt (fun y : E0 => (rad y, Complex.arg y.2)) x :=
      continuous_rad.continuousAt.prodMk ((Complex.continuousAt_arg hs).comp
        continuous_snd.continuousAt)
    exact (hc (Complex.arg x.2)).comp_of_eq hpair rfl
  · have hx0 : x.2 ≠ 0 := fun h => by
      have := rad_pos.1 hx; exact this h
    have hs' : -x.2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      left
      have hre : x.2.re ≠ 0 := fun h => hx0 (Complex.ext h hs.2)
      simp only [Complex.neg_re]
      exact neg_pos.2 (lt_of_le_of_ne hs.1 hre)
    have hpair : ContinuousAt (fun y : E0 => (rad y, Complex.arg (-y.2) + π)) x :=
      continuous_rad.continuousAt.prodMk
        (((Complex.continuousAt_arg hs').comp_of_eq continuous_snd.continuousAt.neg rfl).add
          continuousAt_const)
    have hk : ContinuousAt (fun y : E0 => h (rad y, Complex.arg (-y.2) + π)) x :=
      (hc (Complex.arg (-x.2) + π)).comp_of_eq hpair rfl
    refine hk.congr ?_
    filter_upwards [(isOpen_lt continuous_const continuous_rad).mem_nhds hx] with y hy
    have := heightAt_eq_height hper (polar_neg_arg y) hy
    simp only [heightAt, height] at this
    linarith

/-- Along `≼`, `τ` increases strictly between distinct points (`Le.norm_sub_le`). -/
theorem fst_lt_of_le_of_ne {x y : E0} (h : Le x y) (hne : x ≠ y) : x.1 < y.1 := by
  rcases (fst_le_of_le h).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have hn := h.norm_sub_le
    rw [h', sub_self, mul_zero] at hn
    have h2 : y.2 = x.2 := sub_eq_zero.1 (norm_le_zero_iff.1 hn)
    exact hne (Prod.ext h' h2.symm)

/-- **A spacelike graph over the closed disc `𝔻_R`** (the `Σ` of B21 Lemma 2.9), read by the
integrated form of Lemma 2.7 (B21 l.759–777): `g` periodic in `θ`, the height `F = τ − τ_Σ`
continuous on the solid cylinder `{r ≤ R}` (axis included), and strictly increasing along `≼`
there. For a smooth graph off the axis this is `height_lt_of_le`; at the axis it is not a
derivative condition (the coordinates degenerate), so it is asked in integrated form. -/
structure IsSpacelikeDiscGraph (g : ℝ × ℝ → ℝ) (R : ℝ) : Prop where
  periodic : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)
  continuousOn : ContinuousOn (height g) {x : E0 | rad x ≤ R}
  height_lt : ∀ x y : E0, Le x y → rad y ≤ R → x ≠ y → height g x < height g y

/-- **The graph `Σ`** over the closed disc `𝔻_R` (axis included). -/
def discGraphSet (g : ℝ × ℝ → ℝ) (R : ℝ) : Set E0 := {x | rad x ≤ R ∧ height g x = 0}

theorem IsSpacelikeDiscGraph.height_le (hg : IsSpacelikeDiscGraph g R) {x y : E0} (hxy : Le x y)
    (hy : rad y ≤ R) : height g x ≤ height g y := by
  rcases eq_or_ne x y with h | h
  · rw [h]
  · exact (hg.height_lt x y hxy hy h).le

/-- **A spacelike disc graph is acausal.** -/
theorem IsSpacelikeDiscGraph.acausal (hg : IsSpacelikeDiscGraph g R) {x y : E0}
    (hx : x ∈ discGraphSet g R) (hy : y ∈ discGraphSet g R) (hxy : Le x y) : x = y := by
  by_contra hne
  have := hg.height_lt x y hxy hy.1 hne
  rw [hx.2, hy.2] at this
  exact lt_irrefl _ this

/-- **The graph over the closed disc is compact** (the « compact » of Lemma 2.6(i)): it is the image
of the closed disc `‖z‖ ≤ R` under `z ↦ (τ_Σ(z), z)`. -/
theorem IsSpacelikeDiscGraph.isCompact (hg : IsSpacelikeDiscGraph g R) :
    IsCompact (discGraphSet g R) := by
  set G : ℂ → ℝ := fun z => -height g ((0 : ℝ), z) with hG
  have hGc : ContinuousOn G (Metric.closedBall 0 R) := by
    refine (hg.continuousOn.comp (Continuous.continuousOn (by fun_prop)) ?_).neg
    intro z hz
    change ‖z‖ ≤ R
    simpa using hz
  have hcomp := (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    ((hGc.prodMk continuousOn_id) : ContinuousOn (fun z => (G z, z)) _)
  convert hcomp using 1
  ext x
  simp only [discGraphSet, mem_setOf_eq, mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨hr, hh⟩
    refine ⟨x.2, hr, Prod.ext ?_ rfl⟩
    simp only [hG, height, heightAt, rad] at hh ⊢
    linarith
  · rintro ⟨z, hz, rfl⟩
    refine ⟨hz, ?_⟩
    simp only [hG, height, heightAt, rad]
    ring

/-- `g` is bounded on the closed disc (read through the height). -/
theorem IsSpacelikeDiscGraph.exists_bound (hg : IsSpacelikeDiscGraph g R) :
    ∃ S : ℝ, ∀ x : E0, rad x ≤ R → x.1 - height g x ≤ S := by
  set G : ℂ → ℝ := fun z => -height g ((0 : ℝ), z) with hG
  have hGc : ContinuousOn G (Metric.closedBall 0 R) := by
    refine (hg.continuousOn.comp (Continuous.continuousOn (by fun_prop)) ?_).neg
    intro z hz
    change ‖z‖ ≤ R
    simpa using hz
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hGc
  refine ⟨S, fun x hx => ?_⟩
  have h := hS x.2 (by simpa [rad] using hx)
  rw [Real.norm_eq_abs] at h
  have e : x.1 - height g x = G x.2 := by simp only [hG, height, heightAt, rad]; ring
  rw [e]
  exact (le_abs_self _).trans h

/-- **Spacelike disc graphs from a slice and a spacelike graph** (the piecewise-smooth surfaces of
Lemma 2.6(i)): if `g = c` on the axis and `g = min(c, f)` on `0 < r ≤ R` with `f` a spacelike graph
(Lemma 2.7, `δ > 0`), the height of `g` is strictly increasing along `≼` on `{r ≤ R}`: it is
`τ − c` near the axis and `max(τ − c, F_f)` off it, a maximum of two increasing functions. -/
theorem isSpacelikeDiscGraph_of_min {f : ℝ × ℝ → ℝ} {c : ℝ} (hf : IsSpacelikeGraph f R)
    (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ))
    (hcont : ContinuousOn (height g) {x : E0 | rad x ≤ R}) (hg0 : ∀ θ, g (0, θ) = c)
    (hgmin : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → g p = min c (f p)) :
    IsSpacelikeDiscGraph g R := by
  refine ⟨hper, hcont, fun x y hxy hy hne => ?_⟩
  have hτ := fst_lt_of_le_of_ne hxy hne
  have hry := rad_le_of_le hxy
  -- `height g y ≥ τ(y) − c`
  have hy1 : y.1 - c ≤ height g y := by
    unfold height heightAt
    rcases (rad_nonneg y).lt_or_eq with h | h
    · rw [hgmin _ h hy]; linarith [min_le_left c (f (rad y, Complex.arg y.2))]
    · rw [← h, hg0]
  rcases (rad_nonneg x).lt_or_eq with hx | hx
  · have hy0 : 0 < rad y := hx.trans_le hry
    have ex : height g x = max (x.1 - c) (height f x) := by
      unfold height heightAt
      rw [hgmin _ hx (hry.trans hy)]
      rw [← max_sub_sub_left]
    have ey : height g y = max (y.1 - c) (height f y) := by
      unfold height heightAt
      rw [hgmin _ hy0 hy]
      rw [← max_sub_sub_left]
    rw [ex, ey]
    have hfl := height_lt_of_le hf hxy hx hy hne
    exact max_lt (lt_max_of_lt_left (by linarith)) (lt_max_of_lt_right hfl)
  · have ex : height g x = x.1 - c := by
      unfold height heightAt
      rw [← hx, hg0]
    rw [ex]
    linarith

/-- A horizontal slice `τ = c` is a spacelike graph (`δ = 1`, Lemma 2.7). -/
theorem isSpacelikeGraph_const (c R : ℝ) : IsSpacelikeGraph (fun _ => c) R :=
  ⟨fun _ _ => rfl, fun p _ _ => ⟨0, hasFDerivAt_const c p, by simp [spacelikeDelta]⟩⟩

/-- **The outer piece of the compact disc** (B21 l.872–877, printed as the proof of **(ii)**: the
proofs of (i) and (ii) are swapped): `((2r − R)/R)² τ^R(θ) + M(1/r − 1/R)`. -/
noncomputable def discPiece (τR : ℝ → ℝ) (R M : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((2 * p.1 - R) / R) ^ 2 * τR p.2 + M * (1 / p.1 - 1 / R)

/-- **The compact-disc extension** of B21 Lemma 2.6(i): `M/R` on `r ≤ R/2`, `discPiece` on
`r ≥ R/2` (written with `max r (R/2)`, which makes it globally continuous). -/
noncomputable def discExt (τR : ℝ → ℝ) (R M : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((2 * max p.1 (R / 2) - R) / R) ^ 2 * τR p.2 + M * (1 / max p.1 (R / 2) - 1 / R)

theorem discExt_of_le {τR : ℝ → ℝ} {R M : ℝ} (hR : 0 < R) {p : ℝ × ℝ} (hp : p.1 ≤ R / 2) :
    discExt τR R M p = M / R := by
  simp only [discExt, max_eq_right hp]
  field_simp
  ring

theorem discExt_of_ge {τR : ℝ → ℝ} {R M : ℝ} {p : ℝ × ℝ} (hp : R / 2 ≤ p.1) :
    discExt τR R M p = discPiece τR R M p := by
  simp only [discExt, discPiece, max_eq_left hp]

theorem continuous_discExt {τR : ℝ → ℝ} (hτ : Continuous τR) {R : ℝ} (hR : 0 < R) (M : ℝ) :
    Continuous (discExt τR R M) := by
  have hm : Continuous fun p : ℝ × ℝ => max p.1 (R / 2) := continuous_fst.max continuous_const
  have hm0 : ∀ p : ℝ × ℝ, max p.1 (R / 2) ≠ 0 := fun p =>
    ((by positivity : (0 : ℝ) < R / 2).trans_le (le_max_right _ _)).ne'
  unfold discExt
  refine Continuous.add (Continuous.mul ?_ (hτ.comp continuous_snd))
    (continuous_const.mul ((continuous_const.div hm hm0).sub continuous_const))
  exact ((continuous_const.mul hm).sub continuous_const).div_const R |>.pow 2

theorem hasFDerivAt_discPiece {τR : ℝ → ℝ} {R M : ℝ} {p : ℝ × ℝ} (hp : p.1 ≠ 0)
    (hτ : DifferentiableAt ℝ τR p.2) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (discPiece τR R M) L p ∧
      L (1, 0) = 4 * (2 * p.1 - R) / R ^ 2 * τR p.2 - M / p.1 ^ 2 ∧
      L (0, 1) = ((2 * p.1 - R) / R) ^ 2 * deriv τR p.2 := by
  have hu : HasDerivAt (fun r : ℝ => ((2 * r - R) / R) ^ 2)
      (2 * ((2 * p.1 - R) / R) * (2 / R)) p.1 := by
    have h1 : HasDerivAt (fun r : ℝ => (2 * r - R) / R) (2 / R) p.1 := by
      simpa using (((hasDerivAt_id p.1).const_mul 2).sub_const R).div_const R
    refine (h1.fun_pow 2).congr_deriv ?_
    push_cast
    ring
  have hU := hu.hasFDerivAt.comp p hasFDerivAt_fst
  have hT := hτ.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(p.1 ^ 2)⁻¹)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (hasDerivAt_inv hp).hasFDerivAt.comp p hasFDerivAt_fst
  have H := (hU.mul hT).add ((h1.sub_const (1 / R)).const_mul M)
  have he : discPiece τR R M =
      (fun q : ℝ × ℝ => ((2 * q.1 - R) / R) ^ 2 * τR q.2) + fun y => M * (y.1⁻¹ - 1 / R) := by
    funext q; simp [discPiece, one_div]
  refine ⟨_, he ▸ H, ?_, ?_⟩
  · simp
    field_simp
    ring
  · simp

/-- **B21 Lemma 2.6(i)** (`lem:curve_extension` (i), l.704–712; the construction printed as the
proof of **(ii)**, l.872–877): a `C^n` (`n ≥ 1`) positive `2π`-periodic `τ^R` on the rim `r = R`
extends to a positive continuous `τ` on the closed disc `𝔻_R` which is **piecewise smooth** — the
constant `M/R` on `r ≤ R/2` (`δ = 1`) and a `C^n` spacelike piece on `r ≥ R/2` (`δ > 0` on all of
`0 < r ≤ R`, Lemma 2.7) — whose graph is **spacelike** over the closed disc (axis included,
`IsSpacelikeDiscGraph`: `τ = min(M/R, piece)`) and **compact**. -/
theorem lem_curve_extension_i {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) {R : ℝ}
    (hR : 0 < R) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧
      (∀ p : ℝ × ℝ, 0 ≤ p.1 → p.1 ≤ R → 0 < τ p) ∧ Continuous τ ∧
      (∃ (c : ℝ) (f : ℝ × ℝ → ℝ), IsSpacelikeGraph (fun _ => c) R ∧
        ContDiffOn ℝ n f {p | 0 < p.1} ∧ IsSpacelikeGraph f R ∧
        (∀ p : ℝ × ℝ, p.1 ≤ R / 2 → τ p = c) ∧ (∀ p : ℝ × ℝ, R / 2 ≤ p.1 → τ p = f p)) ∧
      IsSpacelikeDiscGraph τ R ∧ IsCompact (discGraphSet τ R) := by
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; exact absurd hn (by decide)
  have hdiff : Differentiable ℝ τR := hτ.differentiable hn0
  have hdper : Periodic (deriv τR) (2 * π) := by
    intro θ
    have hf : (fun x => τR (x + 2 * π)) = τR := funext hper
    rw [← deriv_comp_add_const, hf]
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1
    (hdper.isBounded_of_continuous (by positivity) (hτ.continuous_deriv hn))
  obtain ⟨T, hT⟩ := isBounded_iff_forall_norm_le.1
    (hper.isBounded_of_continuous (by positivity) hτ.continuous)
  have hT' : ∀ θ, τR θ ≤ T := fun θ => by
    have h := hT _ (mem_range_self θ); rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hT0 : 0 ≤ T := (hpos 0).le.trans (hT' 0)
  have hB' : ∀ θ, (deriv τR θ) ^ 2 ≤ B ^ 2 := fun θ => by
    have h := hB _ (mem_range_self θ)
    rw [Real.norm_eq_abs] at h
    have h0 : 0 ≤ B := (abs_nonneg _).trans h
    exact sq_le_sq' (by linarith [neg_abs_le (deriv τR θ)]) (h.trans' (le_abs_self _))
  set M : ℝ := 1 + B ^ 2 + 5 * T * R with hM
  have hM0 : 0 < M := by positivity
  have hMR : T ≤ M / R := by rw [le_div_iff₀ hR]; nlinarith
  -- the outer piece is a spacelike graph over `0 < r ≤ R`
  have hpiece : IsSpacelikeGraph (discPiece τR R M) R := by
    refine ⟨fun r θ => by simp only [discPiece, hper θ], fun p hp hpR => ?_⟩
    obtain ⟨L, hL, hL1, hL2⟩ := hasFDerivAt_discPiece (R := R) (M := M) hp.ne' (hdiff p.2)
    refine ⟨L, hL, ?_⟩
    rw [hL1, hL2]
    set s := (2 * p.1 - R) / R with hs
    have hs1 : s ≤ 1 := by rw [hs, div_le_one hR]; linarith
    have hs1' : -1 ≤ s := by rw [hs, le_div_iff₀ hR]; linarith
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hs4 : s ^ 4 ≤ 1 := by nlinarith [sq_nonneg s]
    have hsT : s * τR p.2 ≤ T := by
      have := hpos p.2; have := hT' p.2
      rcases le_total 0 s with h | h <;> nlinarith
    have e : spacelikeDelta (4 * (2 * p.1 - R) / R ^ 2 * τR p.2 - M / p.1 ^ 2)
        (s ^ 2 * deriv τR p.2) p.1 =
        1 - 8 * (s * τR p.2) / R + (2 * M - s ^ 4 * (deriv τR p.2) ^ 2) * (1 / p.1 ^ 2) := by
      unfold spacelikeDelta; rw [hs]; field_simp; ring
    rw [e]
    have hD : 8 * T * R ≤ 2 * M - s ^ 4 * (deriv τR p.2) ^ 2 := by
      have := hB' p.2
      have : s ^ 4 * (deriv τR p.2) ^ 2 ≤ B ^ 2 := by
        nlinarith [sq_nonneg (deriv τR p.2)]
      rw [hM]; nlinarith
    have hr2 : 1 / R ^ 2 ≤ 1 / p.1 ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le hpR 2)
    have h8 : 8 * T / R ≤ (2 * M - s ^ 4 * (deriv τR p.2) ^ 2) * (1 / p.1 ^ 2) := by
      have h0 : 0 ≤ 2 * M - s ^ 4 * (deriv τR p.2) ^ 2 := le_trans (by positivity) hD
      calc 8 * T / R = (8 * T * R) * (1 / R ^ 2) := by field_simp
        _ ≤ (2 * M - s ^ 4 * (deriv τR p.2) ^ 2) * (1 / R ^ 2) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hr2 h0
    have h8' : 8 * (s * τR p.2) / R ≤ 8 * T / R := by
      apply div_le_div_of_nonneg_right _ hR.le; linarith
    linarith
  have hcont := continuous_discExt hτ.continuous hR M
  -- the min representation on `0 < r ≤ R`
  have hmin : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R →
      discExt τR R M p = min (M / R) (discPiece τR R M p) := by
    intro p hp hpR
    rcases le_total p.1 (R / 2) with h | h
    · rw [discExt_of_le hR h, min_eq_left]
      have h2 : 2 / R ≤ 1 / p.1 := by
        rw [div_le_div_iff₀ hR hp]; linarith
      have := hpos p.2
      simp only [discPiece]
      have : M / R = M * (2 / R - 1 / R) := by field_simp; ring
      rw [this]
      nlinarith [sq_nonneg ((2 * p.1 - R) / R)]
    · rw [discExt_of_ge h, min_eq_right]
      set s := (2 * p.1 - R) / R with hs
      have hs0 : 0 ≤ s := div_nonneg (by linarith) hR.le
      have hs1 : s ≤ 1 := by rw [hs, div_le_one hR]; linarith
      have e : M / R - discPiece τR R M p = s * (M / p.1 - s * τR p.2) := by
        simp only [discPiece]; rw [hs]; field_simp; ring
      have hMr : M / R ≤ M / p.1 := div_le_div_of_nonneg_left hM0.le hp hpR
      have := hpos p.2; have := hT' p.2
      have : s * τR p.2 ≤ M / p.1 := by nlinarith
      have : 0 ≤ s * (M / p.1 - s * τR p.2) := mul_nonneg hs0 (by linarith)
      linarith
  have hperE : ∀ r θ, discExt τR R M (r, θ + 2 * π) = discExt τR R M (r, θ) := fun r θ => by
    simp only [discExt, hper θ]
  -- the height is continuous everywhere
  have hhc : Continuous (height (discExt τR R M)) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rcases (rad_nonneg x).lt_or_eq with hx | hx
    · exact continuous_fst.continuousAt.sub
        (continuousAt_polarEval hperE hx fun θ => hcont.continuousAt)
    · have hev : ∀ᶠ y in 𝓝 x, height (discExt τR R M) y = y.1 - M / R := by
        filter_upwards [(isOpen_lt continuous_rad continuous_const).mem_nhds
          (show rad x < R / 2 by rw [← hx]; positivity)] with y hy
        simp only [height, heightAt]
        rw [discExt_of_le hR (le_of_lt hy)]
      exact (continuous_fst.continuousAt.sub continuousAt_const).congr
        (Filter.EventuallyEq.symm hev)
  have hdisc : IsSpacelikeDiscGraph (discExt τR R M) R :=
    isSpacelikeDiscGraph_of_min hpiece hperE hhc.continuousOn
      (fun θ => discExt_of_le hR (by simp; positivity)) hmin
  refine ⟨discExt τR R M, fun θ => ?_, fun p hp hpR => ?_, hcont,
    ⟨M / R, discPiece τR R M, isSpacelikeGraph_const (M / R) R, ?_, hpiece,
      fun p hp => discExt_of_le hR hp,
      fun p hp => discExt_of_ge hp⟩, hdisc, hdisc.isCompact⟩
  · rw [discExt_of_ge (by linarith)]
    simp [discPiece]
    field_simp
    norm_num
  · rcases le_total p.1 (R / 2) with h | h
    · rw [discExt_of_le hR h]; positivity
    · rw [discExt_of_ge h]
      simp only [discPiece]
      have := hpos p.2
      rcases hpR.lt_or_eq with h' | h'
      · have : 1 / R < 1 / p.1 := one_div_lt_one_div_of_lt (by linarith) h'
        have : 0 < M * (1 / p.1 - 1 / R) := mul_pos hM0 (by linarith)
        nlinarith [sq_nonneg ((2 * p.1 - R) / R)]
      · rw [h']
        field_simp
        nlinarith
  · have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => τR p.2) {p | 0 < p.1} :=
      (hτ.comp contDiff_snd).contDiffOn
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => 1 / p.1) {p | 0 < p.1} :=
      contDiffOn_const.div contDiffOn_fst (fun p hp => ne_of_gt hp)
    have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((2 * p.1 - R) / R) ^ 2) {p | 0 < p.1} :=
      (((contDiffOn_const.mul contDiffOn_fst).sub contDiffOn_const).div_const R).pow 2
    exact (h3.mul h1).add (contDiffOn_const.mul (h2.sub contDiffOn_const))

/-- **On the rim, `J⁺(C)` is « on or above the graph »** for a disc graph (`C = Σ ∩ ∂S`). -/
theorem IsSpacelikeDiscGraph.height_nonneg_iff_rim (hg : IsSpacelikeDiscGraph g R) {x : E0}
    (hx : rad x = R) : 0 ≤ height g x ↔ ∃ y ∈ discGraphSet g R, rad y = R ∧ Le y x := by
  constructor
  · intro h
    set y : E0 := (g (rad x, Complex.arg x.2), x.2)
    have hry : rad y = rad x := rfl
    refine ⟨y, ⟨by rw [hry, hx], ?_⟩, by rw [hry, hx], ?_⟩
    · change y.1 - g (rad y, Complex.arg y.2) = 0
      rw [hry]; exact sub_self _
    · have h' : y.1 ≤ x.1 := by
        change 0 ≤ x.1 - g (rad x, Complex.arg x.2) at h
        change g (rad x, Complex.arg x.2) ≤ x.1
        linarith
      exact le_of_le (E0Spear.le_vertical_top (z := x.2) h')
  · rintro ⟨y, hy, -, hyx⟩
    rw [← hy.2]
    exact hg.height_le hyx hx.le

/-- **A causal arc of the solid cylinder `{r ≤ R}`** (axis included) meets the spacelike disc graph
in at most one point, and meets it iff the height takes a value `≤ 0` and a value `≥ 0` along it
(monotonicity + IVT, SCOPE K-3). -/
theorem IsSpacelikeDiscGraph.arc_meets_iff (hg : IsSpacelikeDiscGraph g R) {c : ℝ → E0}
    {I : Set ℝ} (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t)) (hreg : ∀ s ∈ I, rad (c s) ≤ R) :
    (c '' I ∩ discGraphSet g R).Subsingleton ∧
      ((∃ s ∈ I, c s ∈ discGraphSet g R) ↔
        (∃ t ∈ I, height g (c t) ≤ 0) ∧ ∃ t ∈ I, 0 ≤ height g (c t)) := by
  refine ⟨?_, ⟨fun ⟨s, hs, hcs⟩ => ⟨⟨s, hs, hcs.2.le⟩, ⟨s, hs, hcs.2.ge⟩⟩, ?_⟩⟩
  · rintro _ ⟨⟨s, hs, rfl⟩, hps⟩ _ ⟨⟨t, ht, rfl⟩, hpt⟩
    rcases le_total s t with hst | hts
    · exact hg.acausal hps hpt (hmono s hs t ht hst)
    · exact (hg.acausal hpt hps (hmono t ht s hs hts)).symm
  · rintro ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩
    rcases le_total t₁ t₂ with h12 | h21
    · have hsub : Icc t₁ t₂ ⊆ I := hI.out ht₁ ht₂
      have hcont : ContinuousOn (fun s => height g (c s)) (Icc t₁ t₂) :=
        hg.continuousOn.comp (hc.mono hsub) (fun s hs => hreg s (hsub hs))
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc h12 hcont ⟨h₁, h₂⟩
      exact ⟨s, hsub hs, hreg s (hsub hs), hs0⟩
    · have hle := hg.height_le (hmono t₂ ht₂ t₁ ht₁ h21) (hreg t₁ ht₁)
      exact ⟨t₂, ht₂, hreg t₂ ht₂, le_antisymm (hle.trans h₁) h₂⟩

open Classical in
/-- **B21 Lemma 2.9** (`lem:intersect_number_compact`, l.885–896), cut by K-3: for a spacelike
graph `Σ` over the closed disc of a spear `S = {r ≤ R} ∩ J⁺(p)` and a future causal arc `c` of
`{r ≤ R}` (axis included) over an interval `I`, whose past end is in the component `[p]` of the
complement of `Σ` (read: a point strictly below `Σ`, e.g. in the head) and whose future end is
`sup c = +∞` or a last point on the shaft `r = R` (read for « closed in `S`, inextendible in
`Int S` »): `|c ∩ Σ| = 1` if `sup c ∈ J⁺(C) ∪ {+∞}`, `0` otherwise. -/
theorem lem_intersect_number_compact (hg : IsSpacelikeDiscGraph g R)
    {c : ℝ → E0} {I : Set ℝ} (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, rad (c s) ≤ R)
    (hpast : ∃ t ∈ I, height g (c t) < 0)
    (hfut : (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨ ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ rad (c b) = R) :
    (c '' I ∩ discGraphSet g R).ncard =
      if (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨
          ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ ∃ y ∈ discGraphSet g R, rad y = R ∧ Le y (c b)
        then 1 else 0 := by
  obtain ⟨hsub, hiff⟩ := hg.arc_meets_iff hI hc hmono hreg
  split_ifs with hcond
  · obtain ⟨t₁, ht₁, h₁⟩ := hpast
    have h₂ : ∃ t ∈ I, 0 ≤ height g (c t) := by
      rcases hcond with h | ⟨b, hb, -, y, hy, -, hyb⟩
      · obtain ⟨S, hS⟩ := hg.exists_bound
        obtain ⟨t, ht, hSt⟩ := h S
        exact ⟨t, ht, by linarith [hS (c t) (hreg t ht)]⟩
      · exact ⟨b, hb, hy.2 ▸ hg.height_le hyb (hreg b hb)⟩
    obtain ⟨s, hs, hcs⟩ := hiff.2 ⟨⟨t₁, ht₁, h₁.le⟩, h₂⟩
    rw [Set.ncard_eq_one]
    exact ⟨c s, hsub.eq_singleton_of_mem ⟨⟨s, hs, rfl⟩, hcs⟩⟩
  · rw [Set.ncard_eq_zero hsub.finite]
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨s, hs, rfl⟩, hcs⟩
    apply hcond
    rcases hfut with h | ⟨b, hb, hmax, hrim⟩
    · exact Or.inl h
    · refine Or.inr ⟨b, hb, hmax, (hg.height_nonneg_iff_rim hrim).1 ?_⟩
      rw [← hcs.2]
      exact hg.height_le (hmono s hs b hb (hmax s hs)) (hreg b hb)

/-- **Non-vacuity of `lem_intersect_number_compact`** (kb/0011): the future ray up the BTZ axis
from below the graph meets it exactly once (`sup = +∞`). -/
theorem lem_intersect_number_compact_axis (hg : IsSpacelikeDiscGraph g R) (hR : 0 ≤ R) :
    ((fun t : ℝ => ((t, (0 : ℂ)) : E0)) '' Ici (g (0, 0) - 1) ∩ discGraphSet g R).ncard = 1 := by
  set τ₀ := g (0, 0)
  have hh : ∀ t : ℝ, height g ((t, (0 : ℂ)) : E0) = t - τ₀ := fun t => by
    simp [height, heightAt, rad, τ₀]
  have hinf : ∀ M : ℝ, ∃ t ∈ Ici (τ₀ - 1), M ≤ ((fun t : ℝ => ((t, (0 : ℂ)) : E0)) t).1 :=
    fun M => ⟨max M (τ₀ - 1), mem_Ici.2 (le_max_right _ _), le_max_left _ _⟩
  have h := lem_intersect_number_compact hg (c := fun t : ℝ => ((t, (0 : ℂ)) : E0))
    (I := Ici (τ₀ - 1)) ordConnected_Ici (Continuous.continuousOn (by fun_prop))
    (fun s _ t _ hst => le_of_le (E0Spear.le_vertical_top (z := 0) hst))
    (fun _ _ => by simpa [rad] using hR)
    ⟨τ₀ - 1, self_mem_Ici, by rw [hh]; linarith⟩ (Or.inl hinf)
  rw [h, if_pos (Or.inl hinf)]

open Classical in
/-- **B21 Cor 2.11** (`cor:intersect`, l.910–912), cut by K-3: under the hypotheses of Lemmas 2.9
(`c`, `Σ` over the closed disc) and 2.10 (`c* = reg c`, `Σ*` over the punctured disc,
`lim τ = +∞`), with the same rim circle `C = C*` (`τ_Σ = τ_{Σ*}` on `r = R`):
`|c ∩ Σ| = |c* ∩ Σ*|`. Here `c* = c` on `I* = {t ∈ I | r(c t) > 0}` (`reg(c) = c*`; the parameter
set `I*` is a final segment of `I`, `r` being non-decreasing along `c`). -/
theorem cor_intersect_number {gc gs : ℝ × ℝ → ℝ} (hgc : IsSpacelikeDiscGraph gc R)
    (hgs : IsSpacelikeGraph gs R) (hR : 0 < R)
    (hlim : Tendsto gs (comap Prod.fst (𝓝[>] 0)) atTop) (hrim : ∀ θ, gc (R, θ) = gs (R, θ))
    {c : ℝ → E0} {I : Set ℝ} (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, rad (c s) ≤ R)
    (hpast : ∃ t ∈ I, height gc (c t) < 0)
    (hpast' : (∃ t ∈ {t ∈ I | 0 < rad (c t)}, height gs (c t) < 0) ∨
      ∀ ε > 0, ∃ t ∈ {t ∈ I | 0 < rad (c t)}, rad (c t) < ε)
    (hfut : (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨ ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ rad (c b) = R) :
    (c '' I ∩ discGraphSet gc R).ncard =
      (c '' {t ∈ I | 0 < rad (c t)} ∩ graphSet gs R).ncard := by
  set I' := {t ∈ I | 0 < rad (c t)} with hI'
  -- `I*` is non-empty, a final segment of `I`
  obtain ⟨t₀, ht₀⟩ : I'.Nonempty := by
    rcases hpast' with ⟨t, ht, -⟩ | h
    · exact ⟨t, ht⟩
    · obtain ⟨t, ht, -⟩ := h 1 one_pos; exact ⟨t, ht⟩
  have hfin : ∀ s ∈ I', ∀ t ∈ I, s ≤ t → t ∈ I' := fun s hs t ht hst =>
    ⟨ht, hs.2.trans_le (rad_le_of_le (hmono s hs.1 t ht hst))⟩
  have hI'o : I'.OrdConnected := ⟨fun s hs u hu t ht =>
    hfin s hs t (hI.out hs.1 hu.1 ht) ht.1⟩
  have hfut' : (∀ M : ℝ, ∃ t ∈ I', M ≤ (c t).1) ∨
      ∃ b ∈ I', (∀ t ∈ I', t ≤ b) ∧ rad (c b) = R := by
    rcases hfut with h | ⟨b, hb, hmax, hrb⟩
    · left; intro M
      obtain ⟨t, ht, hMt⟩ := h M
      have hmem : max t t₀ ∈ I := by
        rcases le_total t t₀ with h' | h'
        · rw [max_eq_right h']; exact ht₀.1
        · rw [max_eq_left h']; exact ht
      exact ⟨max t t₀, hfin t₀ ht₀ _ hmem (le_max_right _ _),
        hMt.trans (fst_le_of_le (hmono t ht _ hmem (le_max_left _ _)))⟩
    · right
      exact ⟨b, ⟨hb, hrb ▸ hR⟩, fun t ht => hmax t ht.1, hrb⟩
  have hc' := lem_intersect_number_complete hgs hR hlim hI'o (hc.mono fun t ht => ht.1)
    (fun s hs t ht => hmono s hs.1 t ht.1) (fun s hs => ⟨hs.2, hreg s hs.1⟩) hpast' hfut'
  rw [lem_intersect_number_compact hgc hI hc hmono hreg hpast hfut, hc']
  -- the two conditions agree
  have hrimset : ∀ y : E0, rad y = R → (y ∈ discGraphSet gc R ↔ y ∈ graphSet gs R) := by
    intro y hy
    have e : height gc y = height gs y := by
      simp only [height, heightAt, hy, hrim]
    simp only [discGraphSet, graphSet, mem_setOf_eq, hy, e, le_refl, true_and]
    exact ⟨fun h => ⟨hR, h⟩, fun h => h.2⟩
  congr 1
  apply propext
  constructor
  · rintro (h | ⟨b, hb, hmax, y, hy, hyR, hyb⟩)
    · rcases hfut' with h' | ⟨b, hb, hmax, hrb⟩
      · exact Or.inl h'
      · -- `τ` unbounded along `c` but bounded by the last point: impossible
        exfalso
        obtain ⟨t, ht, hlt⟩ := h ((c b).1 + 1)
        have := fst_le_of_le (hmono t ht b hb.1 (hmax t (hfin t₀ ht₀ t ht ?_)))
        · linarith
        · by_contra hlt'
          push Not at hlt'
          have := fst_le_of_le (hmono t ht t₀ ht₀.1 hlt'.le)
          have := fst_le_of_le (hmono t₀ ht₀.1 b hb.1 (hmax t₀ ht₀))
          linarith
    · have hRb : R ≤ rad (c b) := hyR ▸ rad_le_of_le hyb
      have hb' : b ∈ I' := ⟨hb, hR.trans_le hRb⟩
      exact Or.inr ⟨b, hb', fun t ht => hmax t ht.1, y, (hrimset y hyR).1 hy, hyR, hyb⟩
  · rintro (h | ⟨b, hb, hmax, y, hy, hyR, hyb⟩)
    · left; intro M
      obtain ⟨t, ht, hMt⟩ := h M
      exact ⟨t, ht.1, hMt⟩
    · refine Or.inr ⟨b, hb.1, fun t ht => ?_, y, (hrimset y hyR).2 hy, hyR, hyb⟩
      by_contra hlt
      push Not at hlt
      exact absurd (hmax t (hfin b hb t ht hlt.le)) (not_le.2 hlt)

/-- **Non-vacuity of `cor_intersect_number`** (kb/0011): the hypotheses are jointly inhabited —
for `R > 0` and `τ^R ≡ 1`, Lemma 2.6(i)'s disc and Lemma 2.6(ii)'s cusp share their rim — and
a vertical future ray off the axis, started below both graphs, meets each exactly once. -/
theorem cor_intersect_number_vertical {R : ℝ} (hR : 0 < R) {z₀ : ℂ} (hz : 0 < ‖z₀‖)
    (hzR : ‖z₀‖ ≤ R) :
    ∃ gc gs : ℝ × ℝ → ℝ, IsSpacelikeDiscGraph gc R ∧ IsSpacelikeGraph gs R ∧
      Tendsto gs (comap Prod.fst (𝓝[>] 0)) atTop ∧ (∀ θ, gc (R, θ) = gs (R, θ)) ∧
      ∃ t₀ : ℝ,
        ((fun t : ℝ => ((t, z₀) : E0)) '' Ici t₀ ∩ discGraphSet gc R).ncard = 1 ∧
        ((fun t : ℝ => ((t, z₀) : E0)) '' {t ∈ Ici t₀ | 0 < rad ((t, z₀) : E0)} ∩
          graphSet gs R).ncard = 1 := by
  have h1 : ContDiff ℝ ⊤ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have hper : Periodic (fun _ : ℝ => (1 : ℝ)) (2 * π) := fun _ => rfl
  obtain ⟨gc, hrc, -, -, -, hgc, -⟩ :=
    lem_curve_extension_i (n := ⊤) le_top h1 hper (fun _ => one_pos) hR
  obtain ⟨gs, hrs, hgs, -, -, -, hlim⟩ :=
    lem_curve_extension_ii_complete (n := ⊤) le_top h1 hper (fun _ => one_pos) hR
  have hrim : ∀ θ, gc (R, θ) = gs (R, θ) := fun θ => by rw [hrc, hrs]
  set c : ℝ → E0 := fun t => ((t, z₀) : E0)
  set t₀ := min (gc (‖z₀‖, Complex.arg z₀)) (gs (‖z₀‖, Complex.arg z₀)) - 1
  have hhc : ∀ t, height gc (c t) = t - gc (‖z₀‖, Complex.arg z₀) := fun t => rfl
  have hhs : ∀ t, height gs (c t) = t - gs (‖z₀‖, Complex.arg z₀) := fun t => rfl
  have hmono : ∀ s ∈ Ici t₀, ∀ t ∈ Ici t₀, s ≤ t → Le (c s) (c t) :=
    fun s _ t _ hst => le_of_le (E0Spear.le_vertical_top (z := z₀) hst)
  have hinf : ∀ M : ℝ, ∃ t ∈ Ici t₀, M ≤ (c t).1 :=
    fun M => ⟨max M t₀, mem_Ici.2 (le_max_right _ _), le_max_left _ _⟩
  have hm1 : t₀ < gc (‖z₀‖, Complex.arg z₀) := by
    have := min_le_left (gc (‖z₀‖, Complex.arg z₀)) (gs (‖z₀‖, Complex.arg z₀)); linarith
  have hm2 : t₀ < gs (‖z₀‖, Complex.arg z₀) := by
    have := min_le_right (gc (‖z₀‖, Complex.arg z₀)) (gs (‖z₀‖, Complex.arg z₀)); linarith
  have hpast : ∃ t ∈ Ici t₀, height gc (c t) < 0 :=
    ⟨t₀, self_mem_Ici, by rw [hhc]; linarith⟩
  have hpast' : (∃ t ∈ {t ∈ Ici t₀ | 0 < rad (c t)}, height gs (c t) < 0) ∨
      ∀ ε > 0, ∃ t ∈ {t ∈ Ici t₀ | 0 < rad (c t)}, rad (c t) < ε :=
    Or.inl ⟨t₀, ⟨self_mem_Ici, hz⟩, by rw [hhs]; linarith⟩
  have hcd := lem_intersect_number_compact hgc (c := c) (I := Ici t₀) ordConnected_Ici
    (Continuous.continuousOn (by fun_prop)) hmono (fun _ _ => hzR) hpast (Or.inl hinf)
  rw [if_pos (Or.inl hinf)] at hcd
  have hcor := cor_intersect_number hgc hgs hR hlim hrim (c := c) (I := Ici t₀) ordConnected_Ici
    (Continuous.continuousOn (by fun_prop)) hmono (fun _ _ => hzR) hpast hpast' (Or.inl hinf)
  exact ⟨gc, gs, hgc, hgs, hlim, hrim, t₀, hcd, hcor ▸ hcd⟩

end Disc


/-! ### §5 The output: `Σ*` a Cauchy surface of `Reg M`, `Reg M` Cauchy-complete -/

/-! ### §5a Lemma 2.6(ii) with an arbitrary lower bound on the rim -/

/-- **Lemma 2.6(ii) shifted** (the form the surgery consumes): for a `C^n` periodic rim
`τ^R > c₀` (not necessarily positive), a spacelike complete graph over the blunt spear,
`C^n` off the axis, `> c₀` on `0 < r ≤ R`, `τ → +∞` at the axis. The paper's « positive » is a
normalisation of the vertex (`τ ↦ τ − c₀`, an isometry of `𝔼₀`). -/
theorem lem_curve_extension_ii_shift {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) {c₀ : ℝ} (hpos : ∀ θ, c₀ < τR θ)
    {R : ℝ} (hR : 0 < R) :
    ∃ G : ℝ × ℝ → ℝ, (∀ θ, G (R, θ) = τR θ) ∧ IsSpacelikeGraph G R ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → c₀ < G p) ∧ ContDiffOn ℝ n G {p | 0 < p.1} ∧
      CompleteSpace (Causal.Flat.PulledLength (graphDev G R)) ∧
      Tendsto G (comap Prod.fst (𝓝[>] 0)) atTop := by
  obtain ⟨τ, hrim, hp, hpos', hC, hδ, hlim⟩ :=
    lem_curve_extension_ii (τR := fun θ => τR θ - c₀) hn (hτ.sub contDiff_const)
      (fun θ => by simp only [hper θ]) (fun θ => sub_pos.2 (hpos θ)) (R := R)
  set G : ℝ × ℝ → ℝ := fun p => τ p + c₀ with hGdef
  have hGp : ∀ r θ, G (r, θ + 2 * π) = G (r, θ) := fun r θ => by simp only [G, hp r θ]
  have hδG : ∀ p : ℝ × ℝ, 0 < p.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt G L p ∧
      1 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := fun p hp0 => by
    obtain ⟨L, hL, h⟩ := hδ p hp0
    exact ⟨L, hL.add_const c₀, h⟩
  have hδ1 : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt G L p ∧
      (1 : ℝ) ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := fun p hp0 _ => by
    obtain ⟨L, hL, h⟩ := hδG p hp0
    exact ⟨L, hL, by simpa using h⟩
  have hCG : ContDiffOn ℝ n G {p | 0 < p.1} := hC.add contDiffOn_const
  have hC1 : ContDiffOn ℝ 1 G (stripSet R) := (hCG.of_le hn).mono fun p hp => hp.1
  refine ⟨G, fun θ => by simp [G, hrim θ], ⟨hGp, fun p hp0 _ => ?_⟩, fun p hp0 hpR => ?_, hCG,
    (lem_surface_complete_one hR one_pos hGp hC1 hδ1).2,
    tendsto_atTop_add_const_right _ c₀ hlim⟩
  · obtain ⟨L, hL, h⟩ := hδG p hp0
    exact ⟨L, hL, (by positivity : (0 : ℝ) < 1 / p.1 ^ 2).trans_le h⟩
  · have := hpos' p hp0 hpR
    simp only [G]; linarith

/-- **The rim circle** `θ ↦ τ_Σ(R e^{iθ})` of a graph function `τ_Σ : ℂ → ℝ` over the disc. -/
noncomputable def rimFun (τS : ℂ → ℝ) (R θ : ℝ) : ℝ :=
  τS ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

theorem rimFun_periodic (τS : ℂ → ℝ) (R : ℝ) : Periodic (rimFun τS R) (2 * π) := fun θ => by
  simp only [rimFun]
  congr 1
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem norm_rimPoint {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    ‖(R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = R := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hR]

/-- On the rim `r = R`, the angle-free value of a graph whose rim is `rimFun τS R` is `τ_Σ`. -/
theorem rim_value {G : ℝ × ℝ → ℝ} {τS : ℂ → ℝ} {R : ℝ} (hrim : ∀ θ, G (R, θ) = rimFun τS R θ)
    {x : E0} (hx : rad x = R) : G (rad x, Complex.arg x.2) = τS x.2 := by
  rw [hx, hrim, rimFun, ← hx]
  congr 1
  exact Complex.norm_mul_exp_arg_mul_I x.2

/-- **`C = C*`** (B21 Cor 2.11's hypothesis, l.910): on the rim `r = R`, the graph `Σ*` of `G`
and the graph `τ = τ_Σ` coincide. -/
theorem mem_graphSet_iff_of_rim {G : ℝ × ℝ → ℝ} {τS : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrim : ∀ θ, G (R, θ) = rimFun τS R θ) {x : E0} (hx : rad x = R) :
    x ∈ graphSet G R ↔ x.1 = τS x.2 := by
  have h := rim_value hrim hx
  rw [hx] at h
  simp only [graphSet, mem_setOf_eq, height, heightAt, hx, hR, le_refl, true_and, sub_eq_zero, h]


/-! ### §5c Spacelike Lipschitz is a local property -/

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Causal.Minkowski 2) X]

/-- **`IsSpacelikeLipschitz` at one point** (the body of `Causal.Flat.IsSpacelikeLipschitz`). -/
def IsSpacelikeLipschitzAt (T : Set X) (x : X) : Prop :=
  ∃ V : TopologicalSpace.Opens (Causal.Minkowski 2), chartAt (Causal.Minkowski 2) x x ∈ V ∧
    (V : Set (Causal.Minkowski 2)) ⊆ (chartAt (Causal.Minkowski 2) x).target ∧
    Causal.Flat.IsSpacelikeLipschitzIn V
      ((chartAt (Causal.Minkowski 2) x) '' (T ∩ (chartAt (Causal.Minkowski 2) x).source) ∩
        (V : Set (Causal.Minkowski 2)))

theorem isSpacelikeLipschitz_iff_at {T : Set X} :
    Causal.Flat.IsSpacelikeLipschitz 2 T ↔ ∀ x ∈ T, IsSpacelikeLipschitzAt T x := Iff.rfl

/-- **Locality**: if `T` agrees with `T'` near `x` and `T'` is spacelike Lipschitz at `x`, so is
`T`. -/
theorem IsSpacelikeLipschitzAt.congr {T T' : Set X} {x : X} (h : IsSpacelikeLipschitzAt T' x)
    {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) (hTO : T ∩ O = T' ∩ O) :
    IsSpacelikeLipschitzAt T x := by
  obtain ⟨V₀, hxV₀, hV₀t, hL⟩ := h
  set e := chartAt (Causal.Minkowski 2) x
  let V₁ : TopologicalSpace.Opens (Causal.Minkowski 2) :=
    ⟨e.target ∩ e.symm ⁻¹' O, e.isOpen_inter_preimage_symm hO⟩
  have hxs : x ∈ e.source := mem_chart_source _ _
  refine ⟨V₀ ⊓ V₁, ⟨hxV₀, e.map_source hxs, by
    show e.symm (e x) ∈ O; rw [e.left_inv hxs]; exact hxO⟩,
    fun z hz => hz.2.1, ?_⟩
  have hR := hL.restrict (V' := V₀ ⊓ V₁) inf_le_left
  convert hR using 1
  ext z
  simp only [TopologicalSpace.Opens.coe_inf, mem_inter_iff, mem_image]
  constructor
  · rintro ⟨⟨y, ⟨hyT, hys⟩, rfl⟩, hzV₀, hzV₁⟩
    have hyO : y ∈ O := by
      have h := hzV₁.2
      rwa [mem_preimage, e.left_inv hys] at h
    have hyT' : y ∈ T' := ((Set.ext_iff.1 hTO y).1 ⟨hyT, hyO⟩).1
    exact ⟨⟨⟨y, ⟨hyT', hys⟩, rfl⟩, hzV₀⟩, hzV₀, hzV₁⟩
  · rintro ⟨⟨⟨y, ⟨hyT', hys⟩, rfl⟩, -⟩, hzV₀, hzV₁⟩
    have hyO : y ∈ O := by
      have h := hzV₁.2
      rwa [mem_preimage, e.left_inv hys] at h
    have hyT : y ∈ T := ((Set.ext_iff.1 hTO y).2 ⟨hyT', hyO⟩).1
    exact ⟨⟨y, ⟨hyT, hys⟩, rfl⟩, hzV₀, hzV₁⟩

end Local

/-! ### §5b The data of the surgery -/

section SurgeryData

variable (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The point of `M` under a point of `Reg M` (the carrier of `e0RegMFlat M` is `E0LM.e0RegM M`). -/
def regVal (y : e0RegMFlat M) : M := (show E0LM.e0RegM M from y).1

/-- A subset of `M`, read in `Reg M`. -/
def regSet (S : Set M) : Set (e0RegMFlat M) := {y | regVal M y ∈ S}

/-- **A `C¹` spacelike compact Cauchy surface of an `𝔼₀`-manifold** (B21 l.227's « Cauchy-compact »:
« a smooth spacelike Cauchy-surface which is compact », read as what the surgery consumes): a
compact Cauchy surface `S` of `M`, spacelike Lipschitz in the flat charts of `Reg M`, whose trace
on the shaft of every spear chart meeting it along a graph `τ = τ_Σ(z)` over the closed disc, in
the shaft (`τ_Σ > v + R/2` on `‖z‖ ≤ R`) and continuous there, is a `C¹` circle.

The shaft and continuity antecedents of `rim` are the WP-43b round-2 repair (AUDIT-2, blocker):
without the shaft condition `τ_Σ` was unconstrained wherever the spear misses `S` (raise the
vertex above `sup τ_Σ`), so a discontinuous `τ_Σ` satisfied the antecedent and `rim` was
contradictory. With it, `τ_Σ` is determined on the closed disc by `S`
(`eqOn_closedBall_of_rim_antecedent`), so the rim circle is a property of `S` alone
(`rimFun_eq_of_rim_antecedent`). -/
structure IsE0C1SpacelikeCauchy (S : Set M) : Prop where
  cauchy : (E0CBG.CE M).IsCauchySurface S
  compact : IsCompact S
  reg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S)
  rim : ∀ (R v : ℝ) (W : Set E0Y) (ψ : E0Y → M) (τS : ℂ → ℝ), 0 < R → IsOpen W →
    E0Spear.spearY v R ⊆ W → E0Spear.IsE0Mor ψ W → InjOn ψ W →
    ContinuousOn τS (Metric.closedBall 0 R) →
    (∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS z) →
    (∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2)) →
    ContDiff ℝ 1 (rimFun τS R)

omit [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] in
/-- **Well-posedness of `IsE0C1SpacelikeCauchy.rim`** (the round-2 repair): two graph functions
of the trace of `S` on a spear, one of them in the shaft, agree on the closed disc. -/
theorem eqOn_closedBall_of_rim_antecedent {S : Set M} {R v : ℝ} {ψ : E0Y → M} {τS τS' : ℂ → ℝ}
    (h : ∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2))
    (h' : ∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS' x.2))
    (hs' : ∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS' z) {z : ℂ} (hz : ‖z‖ ≤ R) : τS z = τS' z := by
  have hx : ((τS' z, z) : E0) ∈ E0Spear.spear v R := by
    refine ⟨?_, hz⟩
    have := hs' z hz
    simp only [fcoord, rad]
    linarith
  exact ((h _ hx).1 ((h' _ hx).2 rfl)).symm

omit [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] in
/-- Under `rim`'s antecedents the rim circle depends on `S` only. -/
theorem rimFun_eq_of_rim_antecedent {S : Set M} {R v : ℝ} {ψ : E0Y → M} {τS τS' : ℂ → ℝ}
    (hR : 0 ≤ R)
    (h : ∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2))
    (h' : ∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS' x.2))
    (hs' : ∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS' z) : rimFun τS R = rimFun τS' R := by
  funext θ
  exact eqOn_closedBall_of_rim_antecedent M h h' hs' (norm_rimPoint hR θ).le

/-- **One spear of the surgery** (B21 Prop 2.17's proof, l.1090): a spear chart `ψ` of vertex
`p ∈ sing₀(M) ∩ I⁻(S)` (Lemmas 2.3, 2.4), meeting `S` exactly along the graph of `τ_Σ` over the
closed disc, in the shaft, and the complete spacelike graph `G` of Lemma 2.6(ii) over the blunt
spear with the same rim. -/
structure SpearSurgeryDatum (S : Set M) where
  p : M
  R : ℝ
  v : ℝ
  W : Set E0Y
  ψ : E0Y → M
  τS : ℂ → ℝ
  G : ℝ × ℝ → ℝ
  p_mem : p ∈ E0CBG.S0 M
  p_past : p ∈ (E0CBG.CE M).Iminus ⊤ S
  pos : 0 < R
  isOpen : IsOpen W
  spear_sub : E0Spear.spearY v R ⊆ W
  mor : E0Spear.IsE0Mor ψ W
  inj : InjOn ψ W
  vertex : ψ (E0Spear.yVertex v) = p
  continuousOn : ContinuousOn τS (Metric.closedBall 0 R)
  shaft : ∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS z
  graph : ∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2)
  rim : ∀ θ, G (R, θ) = rimFun τS R θ
  spacelike : IsSpacelikeGraph G R
  above : ∀ q : ℝ × ℝ, 0 < q.1 → q.1 ≤ R → v + R / 2 < G q
  smooth : ContDiffOn ℝ 1 G {q | 0 < q.1}
  complete : CompleteSpace (Causal.Flat.PulledLength (graphDev G R))
  lim : Tendsto G (comap Prod.fst (𝓝[>] 0)) atTop

variable {M}

namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- The spear `𝒮_Δ = ψ(spear)` in `M`. -/
def spearSet : Set M := D.ψ '' E0Spear.spearY D.v D.R

/-- The cusp `Σ*_Δ = ψ(graph of G)` in `M`. -/
def cusp : Set M := D.ψ '' (paperInY '' graphSet D.G D.R)

/-- The coordinates `x ∈ spear` of a point `ψ(x)` of the spear. -/
noncomputable def coord (y : M) : E0 :=
  Function.invFunOn (fun x : E0 => D.ψ (paperInY x)) (E0Spear.spear D.v D.R) y

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem graphSet_subset_spear : graphSet D.G D.R ⊆ E0Spear.spear D.v D.R := by
  intro x hx
  obtain ⟨h0, hR, hh⟩ := hx
  have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    simp only [height, heightAt] at hh; linarith
  have h2 := D.above (rad x, Complex.arg x.2) h0 hR
  refine ⟨?_, hR⟩
  simp only [fcoord]
  rw [h1]; linarith

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cusp_subset_spearSet : D.cusp ⊆ D.spearSet := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨paperInY x, ⟨x, D.graphSet_subset_spear hx, rfl⟩, rfl⟩

theorem paperInY_mem_e0SingY_iff (x : E0) : paperInY x ∈ e0SingY 0 ↔ rad x = 0 := by
  rw [paperInY_apply, E0LM.inr_mem_e0SingY_zero_iff, Homeomorph.apply_symm_apply]
  show x.2 = 0 ↔ ‖x.2‖ = 0
  rw [norm_eq_zero]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- A point `ψ(x)` of the spear is BTZ iff `x` is on the axis (morphisms preserve the type). -/
theorem mem_S0_iff {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) :
    D.ψ (paperInY x) ∈ E0CBG.S0 M ↔ rad x = 0 := by
  rw [← paperInY_mem_e0SingY_iff,
    ← Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem D.isOpen D.mor
      (D.spear_sub ⟨x, hx, rfl⟩) le_rfl]
  show chartAt E0Y (paperInY x) (paperInY x) ∈ e0SingY 0 ↔ _
  rw [chartAt_self_eq]
  rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The cusp lies in `Reg M`.** -/
theorem cusp_inter_S0 : D.cusp ∩ E0CBG.S0 M = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro _ ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hS⟩
  have := (D.mem_S0_iff (D.graphSet_subset_spear hx)).1 hS
  exact absurd hx.1 (by rw [this]; exact lt_irrefl 0)

/-- **The K-3 hypotheses of Lemma 2.10 for an arc of the blunt spear of `D`** (what Remark 2.12
asserts of the components of an inextensible causal curve of `Reg M` in a spear): `c` over an
interval `J`, continuous, `≼`-increasing, in `0 < r ≤ R`; past end below `Σ*` (e.g. on the head)
or at the axis; future end `τ → +∞` or a last point on the shaft. -/
def IsSpearArc (c : ℝ → E0) (J : Set ℝ) : Prop :=
  J.OrdConnected ∧ ContinuousOn c J ∧ (∀ s ∈ J, ∀ t ∈ J, s ≤ t → Le (c s) (c t)) ∧
    (∀ s ∈ J, 0 < rad (c s) ∧ rad (c s) ≤ D.R) ∧
    ((∃ t ∈ J, height D.G (c t) < 0) ∨ ∀ ε > 0, ∃ t ∈ J, rad (c t) < ε) ∧
    ((∀ M : ℝ, ∃ t ∈ J, M ≤ (c t).1) ∨ ∃ b ∈ J, (∀ t ∈ J, t ≤ b) ∧ rad (c b) = D.R)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
open Classical in
/-- **Lemma 2.10 on a spear arc**: a spear arc meets the cusp `Σ*_Δ` once if its future end is
`+∞` or in `J⁺(C*)`, and not at all otherwise (`lem_intersect_number_complete`). -/
theorem IsSpearArc.ncard {c : ℝ → E0} {J : Set ℝ} (h : D.IsSpearArc c J) :
    (c '' J ∩ graphSet D.G D.R).ncard =
      if (∀ M : ℝ, ∃ t ∈ J, M ≤ (c t).1) ∨
          ∃ b ∈ J, (∀ t ∈ J, t ≤ b) ∧ ∃ y ∈ graphSet D.G D.R, rad y = D.R ∧ Le y (c b)
        then 1 else 0 :=
  lem_intersect_number_complete D.spacelike D.pos D.lim h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2

end SpearSurgeryDatum

/-- **One spear of the surgery exists at every BTZ point in the past of `S`** (B21 Prop 2.17's
proof, l.1090: « Lemma 2.3 … Lemma 2.4 … and finally the point (ii) of Lemma 2.6 »): Lemma 2.3
(`E0Spear.lem_tube`) and Lemma 2.4 (`E0Spear.lem_add_BTZ_param_of_cauchyMaximal`), with their CBG
inputs `hLine`/`hSC` discharged by `E0LM.e0_globalBTZ` ((O2)) and
`E0LM.e0_secondCountable_of_cauchy` ((O4′)), give a spear chart of vertex `p` meeting `S` along
the graph of `τ_Σ` in the shaft; its rim is `C¹` (`IsE0C1SpacelikeCauchy.rim`), and Lemma 2.6(ii)
(`lem_curve_extension_ii_shift`, with Lemma 2.8(1)) extends it to a complete spacelike graph. -/
theorem exists_spearSurgeryDatum (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) {p : M}
    (hp : p ∈ E0CBG.S0 M) (hpS : p ∈ (E0CBG.CE M).Iminus ⊤ S) :
    ∃ D : SpearSurgeryDatum M S, D.p = p := by
  obtain ⟨R, v, W, ψ, hR, hW, hsub, hψ, hinj, hpv, τS, h0, h1, h2⟩ :=
    E0Spear.lem_add_BTZ_param_of_cauchyMaximal E0LM.e0_globalBTZ
      (fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy) hGH hS.cauchy hmax hp hpS
  have hC1 := hS.rim R v W ψ τS hR hW hsub hψ hinj h0 h1 h2
  obtain ⟨G, hrim, hsl, habove, hC, hcomp, hlim⟩ :=
    lem_curve_extension_ii_shift (n := 1) le_rfl hC1 (rimFun_periodic τS R) (c₀ := v + R / 2)
      (fun θ => h1 _ (norm_rimPoint hR.le θ).le) hR
  exact ⟨⟨p, R, v, W, ψ, τS, G, hp, hpS, hR, hW, hsub, hψ, hinj, hpv, h0, h1, h2, hrim, hsl,
    habove, hC, hcomp, hlim⟩, rfl⟩


omit [SecondCountableTopology M] in
/-- **A spear of the surgery can be thinned** (the tool of B21's « one can take the spear
neighbourhoods disjoint », l.1091): for every `0 < R' ≤ R` the same chart, restricted to the spear
of radius `R'`, carries a datum (the rim at `R'` is again `C¹`, and Lemma 2.6(ii) is re-applied). -/
theorem SpearSurgeryDatum.exists_shrink {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (D : SpearSurgeryDatum M S) {R' : ℝ} (hR' : 0 < R') (hle : R' ≤ D.R) :
    ∃ D' : SpearSurgeryDatum M S, D'.p = D.p ∧ D'.ψ = D.ψ ∧ D'.v = D.v ∧ D'.R = R' := by
  have hsub : E0Spear.spear D.v R' ⊆ E0Spear.spear D.v D.R :=
    E0Spear.spear_mono le_rfl hle
  have hsubY : E0Spear.spearY D.v R' ⊆ D.W :=
    (image_mono hsub).trans D.spear_sub
  have hgraph : ∀ x ∈ E0Spear.spear D.v R', (D.ψ (paperInY x) ∈ S ↔ x.1 = D.τS x.2) :=
    fun x hx => D.graph x (hsub hx)
  have hshaft : ∀ z : ℂ, ‖z‖ ≤ R' → D.v + R' / 2 < D.τS z := fun z hz => by
    have := D.shaft z (hz.trans hle); linarith
  have hC1 := hS.rim R' D.v D.W D.ψ D.τS hR' D.isOpen hsubY D.mor D.inj
    (D.continuousOn.mono (Metric.closedBall_subset_closedBall hle)) hshaft hgraph
  obtain ⟨G, hrim, hsl, habove, hC, hcomp, hlim⟩ :=
    lem_curve_extension_ii_shift (n := 1) le_rfl hC1 (rimFun_periodic D.τS R')
      (c₀ := D.v + R' / 2) (fun θ => hshaft _ (norm_rimPoint hR'.le θ).le) hR'
  exact ⟨⟨D.p, R', D.v, D.W, D.ψ, D.τS, G, D.p_mem, D.p_past, hR', D.isOpen, hsubY, D.mor, D.inj,
    D.vertex, D.continuousOn.mono (Metric.closedBall_subset_closedBall hle), hshaft, hgraph, hrim,
    hsl, habove, hC, hcomp, hlim⟩, rfl, rfl, rfl, rfl⟩

variable (M) in
/-- **The data of the surgery** (B21 Prop 2.17's proof, l.1091): finitely many spears, one
around each BTZ line, pairwise disjoint, closed (B21 Def 2.1: the boundary of a spear
neighbourhood is its head and its shaft), covering `S ∩ sing₀(M)`. -/
structure SurgeryData (S : Set M) where
  ι : Type
  finite : Finite ι
  D : ι → SpearSurgeryDatum M S
  disjoint : Pairwise fun i j => Disjoint (D i).spearSet (D j).spearSet
  isClosed : ∀ i, IsClosed (D i).spearSet
  covers : S ∩ E0CBG.S0 M ⊆ ⋃ i, (D i).spearSet

namespace SurgeryData

variable {S : Set M} (Dat : SurgeryData M S)

/-- **The surgery `Σ*`** (B21 l.1091): « equal to `Σ` outside the spear neighbourhoods and
equal to the graph obtained by the point (ii) of Lemma 2.6 inside each ». -/
def sigmaStar : Set M := (S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, (Dat.D i).cusp

/-- `Σ*` read in `Reg M`. -/
def sigmaStarReg : Set (e0RegMFlat M) := regSet M Dat.sigmaStar

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is `Σ` outside the spears. -/
theorem sigmaStar_diff : Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet = S \ ⋃ i, (Dat.D i).spearSet := by
  ext y
  simp only [sigmaStar, Set.mem_sdiff, mem_union, mem_iUnion]
  constructor
  · rintro ⟨h | ⟨i, hi⟩, hn⟩
    · exact h
    · exact absurd ⟨i, (Dat.D i).cusp_subset_spearSet hi⟩ hn
  · rintro ⟨h, hn⟩
    exact ⟨Or.inl ⟨h, hn⟩, hn⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is the cusp inside each spear. -/
theorem sigmaStar_inter_spearSet (i : Dat.ι) :
    Dat.sigmaStar ∩ (Dat.D i).spearSet = (Dat.D i).cusp := by
  ext y
  simp only [sigmaStar, mem_inter_iff, mem_union, Set.mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨⟨-, hn⟩ | ⟨j, hj⟩, hi⟩
    · exact absurd ⟨i, hi⟩ hn
    · rcases eq_or_ne j i with rfl | hji
      · exact hj
      · exact absurd hi (Set.disjoint_left.1 (Dat.disjoint hji) ((Dat.D j).cusp_subset_spearSet hj))
  · intro hy
    exact ⟨Or.inr ⟨i, hy⟩, (Dat.D i).cusp_subset_spearSet hy⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **`Σ*` lies in `Reg M`.** -/
theorem sigmaStar_subset_regM : Dat.sigmaStar ⊆ (E0LM.e0RegM M : Set M) := by
  intro y hy hS0
  rcases hy with ⟨hyS, hn⟩ | hy
  · exact hn (Dat.covers ⟨hyS, hS0⟩)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    have := (Dat.D i).cusp_inter_S0
    exact (Set.eq_empty_iff_forall_notMem.1 this) y ⟨hi, hS0⟩

end SurgeryData


/-! ### §5d The global part of the surgery, one obstruction per declaration -/

/-- **(G1) The surgery data exist** (B21 l.1091: « Since `M` is Cauchy-compact, it admits
finitely many BTZ-lines and one can take the spear neighborhoods `𝒮_Δ` disjoint »). Each spear is
`exists_spearSurgeryDatum` (proved, through Lemmas 2.3/2.4 upstream) and can be thinned
(`SpearSurgeryDatum.exists_shrink`, proved). -/
theorem exists_surgeryData (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Nonempty (SurgeryData M S) := by
  sorry -- SORRY(prop:abs_max): (G1) the finite disjoint family of spears; three steps are unbuilt. (i) FINITENESS: S ∩ sing₀(M) is compact (sing₀ closed) and must be shown discrete, i.e. each BTZ point has a neighbourhood meeting sing₀ in one arc of its line which meets the acausal S once (the local structure of sing₀ in a chart is the axis, Rigid/LocalModel, but its transversality to S is not stated anywhere). (ii) VERTICES: for each q ∈ S ∩ sing₀ a point p of q's BTZ line in I⁻(S) (the line below q is in J⁻(q); that its points are in I⁻(S), the hypothesis of Lemma 2.4, is not proved). (iii) DISJOINT AND CLOSED SPEARS: B21 asserts both without proof; thinning (exists_shrink) separates the compact parts ψ({τ ≤ T} ∩ spear), but the spears are non-compact (rays to +∞), and neither the uniform separation along the two rays nor the closedness of ψ(spear) in M (B21 Def 2.1: frontier = head ∪ shaft) is built

/-- **(G2) Remark 2.12** (`rem:curve_spear`, B21 l.913–915): the component through `t₀` of the
trace of an inextensible causal curve of `Reg M` on a spear of the surgery is, in the spear's
coordinates, a spear arc (the K-3 hypotheses of Lemma 2.10). -/
theorem rem_curve_spear (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (Dat : SurgeryData M S) {I : Set ℝ}
    {c : ℝ → e0RegMFlat M}
    (hc : (Causal.Flat.flatCausality 2 (e0RegMFlat M)).Inextensible ⊤ I c) (i : Dat.ι) {t₀ : ℝ}
    (ht₀ : t₀ ∈ I) (hin : regVal M (c t₀) ∈ (Dat.D i).spearSet) :
    (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (regVal M (c t)))
      (connectedComponentIn {t ∈ I | regVal M (c t) ∈ (Dat.D i).spearSet} t₀) := by
  sorry -- SORRY(prop:abs_max): (G2) Remark 2.12 needs the relative curve theory of a spear of M, absent: (i) coordinates — ψ is an injective E0-morphism on the open W, hence an open embedding there, so coord ∘ c is continuous and ≼-increasing on the component (causal curves of Reg M are causal curves of M through flatCausality_e0RegM_eq / the inclusion, then read in the chart: le_of_isE0Mor); (ii) past end — at the first point of the component the chart point is on the head (r non-decreasing along future curves, rad_le_of_le), where height < 0; if the component is open at the left, the curve is past-inextensible inside the compact {v ≤ τ ≤ τ(c t), r ≤ R} and either tends to the axis or converges in Reg M, against inextensibility (no limit-extension lemma for flatCausality curves of Reg M is stated); (iii) future end — symmetric, on the shaft r = R (ψ(spear) closed, SurgeryData.isClosed) or τ unbounded. Spear's isCauchySurface_glued (ii) has the same gap

/-- **(G3) `Σ*` is a Cauchy surface of `Reg M`, modulo Remark 2.12** (B21 l.1093: « by
Remark 2.12 and Corollary 2.11 applied in each spear neighborhood, a Cauchy-surface of `M*` »). -/
theorem SurgeryData.isCauchySurface_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (Dat : SurgeryData M S)
    (hrem : ∀ (I : Set ℝ) (c : ℝ → e0RegMFlat M),
      (Causal.Flat.flatCausality 2 (e0RegMFlat M)).Inextensible ⊤ I c → ∀ (i : Dat.ι) (t₀ : ℝ),
      t₀ ∈ I → regVal M (c t₀) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (regVal M (c t)))
        (connectedComponentIn {t ∈ I | regVal M (c t) ∈ (Dat.D i).spearSet} t₀)) :
    (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg := by
  sorry -- SORRY(prop:abs_max): (G3) the counting argument, with Remark 2.12 (hrem) and Lemma 2.10 (SpearSurgeryDatum.IsSpearArc.ncard) given. Unbuilt: (i) TRANSFER — an inextensible causal curve c of Reg M is a causal curve of M (flatCausality_e0RegM_eq, AbsMax) which may be extensible in M only at ends in sing₀; its extension c̄ (E0LM.e0_curvesExtend) meets S exactly once (hS.cauchy); (ii) DECOMPOSITION — c(I) ∩ Σ* splits as c(I) ∩ (S ∖ spears) (sigmaStar_diff) plus, for each spear and each component J, c(J) ∩ cusp (sigmaStar_inter_spearSet); finiteness of the components meeting a spear needs ψ(spear) closed and r monotone (a curve leaving through the shaft does not re-enter in the chart, but may re-enter ψ(spear) after leaving ψ(W): not excluded); (iii) MATCHING — on each component, |c(J) ∩ Σ*_Δ| = |c̄(J̄) ∩ S| by Cor 2.11, which needs S ∩ spear (graph of the continuous τ_Σ, SpearSurgeryDatum.graph) to be an IsSpacelikeDiscGraph; from the acausality of S one gets height_lt only along ≼ of 𝔼₀ inside ψ(W), and the identification of the two orders (le_of_isE0Mor in one direction) and the continuity of the height of τ_Σ across the axis are not stated

/-- **(G4a) `Σ*` is spacelike Lipschitz at the points of the cusps** (Lemma 2.7, read in the flat
charts of `Reg M`). -/
theorem SurgeryData.isSpacelikeLipschitzAt_cusp {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M}
    (hy : regVal M y ∈ (Dat.D i).cusp) : IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  sorry -- SORRY(prop:abs_max): (G4a) at y = ψ(x), x ∈ graphSet G R. (i) INTERIOR, r(x) < R: near y, Σ* is the cusp (sigmaStar_inter_spearSet, the open ψ(paperInY '' {fcoord > v, r < R})); Lemma 2.7 (lem_surface_causal / lem_surface_complete_one (1)) gives a C¹ immersion graphMap G with positive-definite pullback of btzPaperDev, and the flat chart of Reg M at y is btzPaperDev ∘ ψ⁻¹ up to Isom(𝐌³) (E0.chartIso_e0Atlas, regChart_subtypeRestr_eq) — the step « C¹ spacelike immersion ⇒ locally a Lipschitz graph of slope < 1 in a frame » (implicit function theorem, IsSpacelikeLipschitzIn.locGraph) is not in lean-gx or lean-causal; (ii) RIM, r(x) = R: Σ* is S outside and the cusp inside, a corner along the C¹ circle C = C* (mem_graphSet_iff_of_rim); both pieces are spacelike, and the union is spacelike Lipschitz by the cone-increasing zero-set criterion (Causal.Flat.Cla.isSpacelikeLipschitz_of_locally_coneIncreasing, applied to max/min of the two height functions) — the two height functions in one flat chart are not built

/-- **(G4) `Σ*` is spacelike Lipschitz** in the flat charts of `Reg M`: outside the (closed)
spears it is `S` near the point (`IsSpacelikeLipschitzAt.congr`, `sigmaStar_diff`); inside a
spear it is the cusp (`isSpacelikeLipschitzAt_cusp`). -/
theorem SurgeryData.isSpacelikeLipschitz_sigmaStar {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) : Causal.Flat.IsSpacelikeLipschitz 2 Dat.sigmaStarReg := by
  intro y hy
  by_cases hin : regVal M y ∈ ⋃ i, (Dat.D i).spearSet
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hin
    have hc : regVal M y ∈ (Dat.D i).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hy, hi⟩
    exact Dat.isSpacelikeLipschitzAt_cusp hS i hc
  · have hcl : IsClosed (⋃ i, (Dat.D i).spearSet) := by
      haveI := Dat.finite
      exact isClosed_iUnion_of_finite Dat.isClosed
    set O : Set (e0RegMFlat M) := regSet M (⋃ i, (Dat.D i).spearSet)ᶜ
    have hO : IsOpen O := hcl.isOpen_compl.preimage continuous_subtype_val
    have hyS : y ∈ regSet M S := by
      have h : regVal M y ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨hy, hin⟩
      rw [Dat.sigmaStar_diff] at h
      exact h.1
    refine IsSpacelikeLipschitzAt.congr (hS.reg y hyS) hO hin ?_
    ext z
    simp only [SurgeryData.sigmaStarReg, regSet, O, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hz, hzO⟩
      have h : regVal M z ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨hz, hzO⟩
      rw [Dat.sigmaStar_diff] at h
      exact ⟨h.1, hzO⟩
    · rintro ⟨hz, hzO⟩
      have h : regVal M z ∈ S \ ⋃ i, (Dat.D i).spearSet := ⟨hz, hzO⟩
      rw [← Dat.sigmaStar_diff] at h
      exact ⟨h.1, hzO⟩

/-- **(G5) `Σ*` is complete for its induced length** (B21 l.1093: « The surface `Σ*` is
metrically complete », no proof printed; DEC-31). -/
theorem SurgeryData.completeSpace_sigmaStar {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) :
    CompleteSpace (Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) := by
  sorry -- SORRY(prop:abs_max): (G5) the gluing of completeness. Available: each cusp's development is complete over the strip (SpearSurgeryDatum.complete, Lemma 2.8(1)); the chart comparison of the glued length with chart lengths (Causal.Flat.Cla.edist_le_edist_chart, edist_chart_le_pathLength, localLength_chartSys_eq_lorentzLength); compact pieces are complete (Causal.Flat.Cla.completeSpace_inducedLengthSpace_of_isCompact). Unbuilt: (i) PATH LIFTING — a path of Σ* inside ψ(spear) lifts to the strip (0, R] × ℝ, the universal cover of the punctured disc, with the same length (the flat charts of Reg M there are btzPaperDev ∘ ψ⁻¹ up to Isom(𝐌³), locally), so that strip edist ≤ glued edist; (ii) the Cauchy-sequence argument: a Cauchy sequence of Σ* either has a subsequence in the compact part S ∖ ⋃ ψ(interior spears) ∪ rims (compact as S is), or eventually in one cusp, where (i) and the strip's completeness give a limit, and the limit is a point of Σ* (not on the axis, by the log r estimate of Lemma 2.8, log_le_edist)

/-- **`Reg M` is Cauchy-complete, from a `C¹` spacelike compact Cauchy surface** (B21 Prop 2.17's
first assertion with B21 l.227's « Cauchy-compact »): the composition of (G1)–(G5) and Remark
2.12; the topology field of `IsCauchyComplete` is
`Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype` (proved, from (G4)). -/
theorem regM_isCauchyComplete_of_C1 (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) := by
  obtain ⟨Dat⟩ := exists_surgeryData hGH hS hmax
  have hL := Dat.isSpacelikeLipschitz_sigmaStar hS
  exact ⟨Dat.sigmaStarReg,
    Dat.isCauchySurface_sigmaStar hGH hS fun _ _ hc i _ ht₀ hin => rem_curve_spear hGH hS Dat hc i ht₀ hin,
    hL, Dat.completeSpace_sigmaStar hS, Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype hL⟩

/-- **(G0) Smoothing** (B21 l.227, `sanchez_smooth` for Lorentzian manifolds, Bernard–Suhr for
closed cone fields, B21 l.568–570): a globally hyperbolic `𝔼₀`-manifold with a compact Cauchy
surface has a `C¹` spacelike compact one. -/
theorem exists_isE0C1SpacelikeCauchy (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, (E0CBG.CE M).IsCauchySurface S ∧ IsCompact S) :
    ∃ S : Set M, IsE0C1SpacelikeCauchy M S := by
  sorry -- SORRY(prop:abs_max): (G0) a CITED theorem, not built in lean-gx or lean-causal: Bernal–Sánchez smoothing (B21 l.227) for 𝔼₀-manifolds, i.e. Bernard–Suhr for closed cone fields (B21 l.568–570), with the regularity read as IsE0C1SpacelikeCauchy (spacelike Lipschitz in the flat charts of Reg M, C¹ trace on every spear shaft). lean-causal's Causal.Flat.Cla.exists_isSpacelikeLipschitz_of_isCompact_cauchy (the cap envelope K ∖ I⁻(K)) does the flat, Lipschitz, Cauchy-compact case only: it applies neither across sing₀ nor with the C¹ rim Lemma 2.6(ii) needs, and Reg M is not Cauchy-compact

variable (M) in
/-- **`Reg M` is Cauchy-complete** (B21 Prop 2.17's first assertion, l.1078–1081, proof
l.1088–1093, through Lemmas 2.3, 2.4, 2.6(ii), 2.8, 2.10/2.11 and Remark 2.12): for `M` a globally
hyperbolic, Cauchy-compact, Cauchy-maximal `𝔼₀`-manifold, the surgery `Σ*` of a compact Cauchy
surface along spears around its finitely many BTZ lines is a Cauchy surface of `Reg M`, spacelike
Lipschitz, with complete induced length (`Causal.Flat.IsCauchyComplete`, DEC-31). The composition
of (G0) smoothing and `regM_isCauchyComplete_of_C1` ((G1)–(G5), Remark 2.12); no `sorry` of its
own. -/
theorem regM_isCauchyComplete (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, (E0CBG.CE M).IsCauchySurface S ∧ IsCompact S)
    (hmax : E0Spear.IsE0CauchyMaximal M) :
    Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) := by
  obtain ⟨S, hS⟩ := exists_isE0C1SpacelikeCauchy hGH hCC
  exact regM_isCauchyComplete_of_C1 hGH hS hmax

end SurgeryData

end E0Surgery

end GX
