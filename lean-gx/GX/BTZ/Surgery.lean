import GX.BTZ.Spear
import GX.BTZ.Holonomy
import Causal.Flat.CauchyComplete

/-!
# `GX.BTZ.Surgery` — Cauchy-surface surgery in spear neighbourhoods (B21 Lemmas 2.6–2.11)

Package WP-41j (WAVE5-PLAN.md, WP-39j); WP-43b (Lemma 2.6(i), Lemma 2.9, Cor 2.11; the global
part of Prop 2.17 split one declaration per obstruction; `IsE0C1SpacelikeCauchy.rim` repaired);
WP-44e (DEC-107: (G1) proved, the C¹ form of record); **WP-46e** (DEC-116 (d), DEC-117: the
readings accepted, the rows marked; (G4a) and (G5) **proved**, §5f; the topological route and its
smoothing step (G0) **deleted**); WP-46e fixer round 1 (**(G3) proved**, §5g: 0 `sorry` in the file;
the pointwise-to-integrated bridge for Lemma 2.9); **WP-47c** (DEC-125 (d)(e): Remark 2.12 and
Prop 2.17's first assertion **closed and marked**, docstrings only).
`brunswic2021cauchy` (**B21**, `papers/gx/sources/2108.12631/src/BTZ_1.tex`) §2.1: Lemma 2.6
`lem:curve_extension` (l.704), Lemma 2.7 `lem:surface_causal` (l.749), Lemma 2.8
`lem:surface_complete` (l.781), Lemmas 2.9/2.10 `lem:intersect_number_compact` /
`lem:intersect_number_complete` (l.885/897), Cor 2.11 `cor:intersect` (l.910), Remark 2.12
`rem:curve_spear` (l.913), cut by SCOPE's K-3 (monotonicity + IVT in place of intersection
numbers), and B21 Prop 2.17's first assertion `prop:abs_max` (l.1078). These are cited results
built here (DEC-23), not gx ledger rows, so they are marked with their source prefix
`brunswic2021cauchy:` (no gx label is claimed). Rows, under DEC-117's readings (spacelike
pointwise; `C¹` on the strip; the strip as the domain of completeness; the K-3 curve hypotheses)
and DEC-116 (d):

* **`brunswic2021cauchy:lem:surface_causal`** (Lemma 2.7) — **closed**, 0 `sorry` (pointwise):
  `GX.E0Surgery.lem_surface_causal`; the printed identity is `GX.E0Surgery.graphQuad_eq`.
* **`brunswic2021cauchy:lem:curve_extension`** (Lemma 2.6, both items) — **closed**, 0 `sorry`
  (finding: the two printed proofs are swapped). (ii) `GX.E0Surgery.lem_curve_extension_ii_complete`
  (spacelike, complete, `C^n`, positive, periodic, `+∞` at the axis). (i)
  `GX.E0Surgery.lem_curve_extension_i` (two pieces, each spacelike by Lemma 2.7; positive,
  continuous; spacelike over the closed disc in integrated form, `IsSpacelikeDiscGraph`; compact).
* **`brunswic2021cauchy:lem:surface_complete`** (Lemma 2.8) — **closed**, both items, 0 `sorry`
  (« piecewise smooth » = `C¹` on the strip, « complete » over the strip `(0, R] × ℝ`):
  (1) `GX.E0Surgery.lem_surface_complete_one`; (2) `GX.E0Surgery.lem_surface_complete_two`.
* **`brunswic2021cauchy:lem:intersect_number_complete`** (Lemma 2.10) — **closed**, 0 `sorry`
  (K-3): `GX.E0Surgery.lem_intersect_number_complete`; non-vacuity `…_vertical`.
* **`brunswic2021cauchy:lem:intersect_number_compact`** (Lemma 2.9) — **closed**, 0 `sorry` (K-3;
  curves may run along or cross the axis): `GX.E0Surgery.lem_intersect_number_compact`; pointwise
  `Σ` (DEC-117): `…_pointwise`, via `isSpacelikeDiscGraph_of_isSpacelikeGraph`.
* **`brunswic2021cauchy:cor:intersect`** (Cor 2.11, `|c ∩ Σ| = |c* ∩ Σ*|`) — **closed**, 0 `sorry`
  (K-3): `GX.E0Surgery.cor_intersect_number` (`c* = c` on `{t | r(c t) > 0}`, same rim).
* **`brunswic2021cauchy:rem:curve_spear`** (Remark 2.12) — **closed**, 0 `sorry` (DEC-116 (d),
  DEC-125 (d): `M` globally hyperbolic, the spears those of a surgery datum):
  `GX.E0Surgery.rem_curve_spear`, from `SpearSurgeryDatum.isSpearArc_of_inextensible`.
* **`brunswic2021cauchy:prop:abs_max`** (Prop 2.17, first assertion: `Σ*` Cauchy in `Reg M`,
  `Reg M` Cauchy-complete) — **closed**, 0 `sorry` (DEC-125 (e): `𝔼₀`-manifolds only, `A = {0}`).
  Of record (DEC-107/117: a compact `C¹` spacelike Cauchy surface,
  `IsE0C1SpacelikeCauchy`): `GX.E0Surgery.regM_isCauchyComplete_of_C1`, the composition of (G1)
  `exists_surgeryData`, (G2) `rem_curve_spear`, (G3) `SurgeryData.isCauchySurface_sigmaStar`
  (**proved**, WP-46e fixer), (G4) `SurgeryData.isSpacelikeLipschitz_sigmaStar` with (G4a)
  `SurgeryData.isSpacelikeLipschitzAt_cusp` and (G5) `SurgeryData.completeSpace_sigmaStar`, all
  proved. The maximality assertion is `GX.BTZ.AbsMax`'s `absMax_e0RegM`.

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
| Lemma 2.6(i): « piecewise smooth », « spacelike », « compact » | ⚠ read: two pieces (`r ≤ R/2`, `r ≥ R/2`), each `IsSpacelikeGraph` (Lemma 2.7 pointwise on each smooth domain, `r > 0`, DEC-117); proved in addition (a stronger conclusion, not a reading): the graph over the closed disc is `IsSpacelikeDiscGraph` (height continuous on `{r ≤ R}` and strictly increasing along `≼`, axis included); `IsCompact (discGraphSet τ R)` |
| Lemma 2.9: `Σ` spacelike graph over `𝔻_R` | ⚠ read pointwise (DEC-117): `IsSpacelikeGraph g R` off the axis with the height continuous on `{r ≤ R}` (`lem_intersect_number_compact_pointwise`); it implies the integrated `IsSpacelikeDiscGraph g R` (`isSpacelikeDiscGraph_of_isSpacelikeGraph`), the form `lem_intersect_number_compact` takes |
| Lemma 2.9: `c` closed in `S`, inextendible in `Int S` | ⚠ read (K-3), as Lemma 2.10: an arc of `{r ≤ R}` with a point below `Σ` (the head), and future end `τ` unbounded or a last point on the shaft |
| Cor 2.11: `reg(c) = c*`, `reg(S) = S*`, `C = C*` | ✓ `c* = c` on `I* = {t ∈ I | r(c t) > 0}`; `C = C*` as `τ_Σ = τ_{Σ*}` on `r = R`; the hypotheses of 2.9 for `c` and of 2.10 for `c*` |
| Remark 2.12: an inextendible causal curve of any `𝔼_{≥0}`-manifold, any (blunt) spear | ⚠ read (DEC-125 (d), DEC-116 (d)): `M` globally hyperbolic (closedness of the spear, `isClosed_image_spearY`; limits in compact parts, `regM_facts`); the spears of a surgery datum (the K-3 past end is read against its cusp `G`) |
| Prop 2.17: `E_A`-manifold, `A ⊆ ℝ₊` | ⚠ read (DEC-125 (e)): `𝔼₀`-manifolds only (`A = {0}`), T2, connected, second countable |
| Prop 2.17: Cauchy-maximal | ⚠ read (DEC-77(c)): `E0Spear.IsE0CauchyMaximal` |
| Prop 2.17: Cauchy-compact | ⚠ read (DEC-107/117, B21 l.227): `IsE0C1SpacelikeCauchy` in `regM_isCauchyComplete_of_C1` (Cauchy, compact, spacelike Lipschitz in `Reg M`'s flat charts, `C¹` trace on the shaft circle of every spear chart in which `S` is the graph of a continuous `τ_Σ > v + R/2` over the closed disc) |
| Prop 2.17: Cauchy-complete | ⚠ read (DEC-31): `Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)` |

## SCOPE (disclosed)

* (a) The local machinery is complete in both directions (WP-43b): Lemma 2.6(i)/(ii), 2.7, 2.8,
  2.9, 2.10 and Cor 2.11 are proved in their readings, 0 `sorry`.
* (b) The global part (§5d): `regM_isCauchyComplete_of_C1` composes (G1)–(G5) and Remark 2.12.
  (G1) is proved (§5e): `S ∩ sing₀` is finite; at each of its points a spear of vertex below it on
  its BTZ line, in `I⁻(S)`, its ray through the point; the spears are closed and, thinned until
  each head avoids the other spears, pairwise disjoint. (G2) is proved (§5e).
* (c) (G4a) is proved (§5f, WP-46e) by the cone-increasing zero-set criterion
  (`Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet`) read at a point and in a frame
  (`isSpacelikeLipschitzAt_of_coneZeroSet`): in the interior of a cusp the chart picture is the
  zero set of the height `chartHeight G g`, whose derivative is positive on the future causal cone
  (Lemma 2.7 in null coordinates, `fderiv_nullHeight_pos`), hence cone-increasing on a ball; at
  the rim, in the frame of `S`'s Lipschitz graph, the height is glued to the null-shift height of
  `S` along the developed `∂_τ` (`exists_nullShift`), the two agreeing on the cylinder `r = R`
  (`C = C*`). The chart of `Reg M` read in a spear chart is `g •` a sector chart
  (`SpearSurgeryDatum.eventually_regChart`).
* (d) (G5) is proved (§5f, WP-46e) by B21 Lemma 2.8's `log r` estimate on the glued surface: the
  clamped log-radius `log (min r (R/2))` of each cusp is `1`-Lipschitz for the induced length
  (`SurgeryData.ofReal_abs_logRad_sub_le_edist`: Rademacher in a chart near each time and the
  tangent bound `ds² ≥ (dr/r)²` from `δ ≥ 1/r²`, `sq_le_minkQ_of_tangent`), so a Cauchy sequence
  stays in a compact part of `Σ*` and converges (`SurgeryData.completeSpace_sigmaStar_of_delta`).
  It consumes `δ ≥ 1/r²` on the cusp, now the field `SpearSurgeryDatum.delta` (Lemma 2.6(ii)'s
  construction has it; `lem_curve_extension_ii_shift` exports it).
* (e) (G3) is proved (§5g, WP-46e fixer) by the two closed sides of `Σ*` in `Reg M` (B21's
  « Remark 2.12 and Corollary 2.11 applied in each spear neighborhood », read through the
  monotone height of Lemma 2.7 instead of a count). (G0), smoothing, and the topological
  `regM_isCauchyComplete` are **deleted** (DEC-117); `GX.BTZ.AbsMax` has since retired
  its topological route (`prop_abs_max_C1` / `cor_abs_max_C1` are its forms of record).
* (f) WP-47c (DEC-125 (d)(e)): the two remaining rows, Remark 2.12 (with `M` globally hyperbolic)
  and Prop 2.17's first assertion (`𝔼₀` only, `A = {0}`), close under the author's readings with
  no code change; both were already 0 `sorry`.

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

/-- **The bridge from the pointwise to the integrated reading** (WP-46e fixer, AUDIT-1 m1): a
pointwise spacelike graph (`IsSpacelikeGraph`, Lemma 2.7 at every point `0 < r ≤ R`) whose height
is continuous on the closed solid cylinder `{r ≤ R}` is a spacelike disc graph
(`IsSpacelikeDiscGraph`): the integrated reading is implied by the pointwise one. Off the axis it is `height_lt_of_le`; from an
axis point `x ≼ y` it integrates Lemma 2.7 along the straight segment of the development, which
leaves the axis at once (`r = s · r(y)`), the endpoint `s = 0` by continuity of the height. -/
theorem isSpacelikeDiscGraph_of_isSpacelikeGraph (hg : IsSpacelikeGraph g R)
    (hcont : ContinuousOn (height g) {x : E0 | rad x ≤ R}) : IsSpacelikeDiscGraph g R := by
  refine ⟨hg.periodic, hcont, fun x y hxy hy hne => ?_⟩
  set c := g (0, 0) with hc
  have hax : ∀ z : E0, rad z = 0 → height g z = z.1 - c := by
    intro z hz
    have hz2 : z.2 = 0 := norm_eq_zero.1 hz
    unfold height heightAt
    rw [hz, hz2, Complex.arg_zero]
  rcases (rad_nonneg x).lt_or_eq with hx | hx
  · exact height_lt_of_le hg hxy hx hy hne
  have hxh : height g x = x.1 - c := hax x hx.symm
  rcases (rad_nonneg y).lt_or_eq with hy0 | hy0
  swap
  · have hyh : height g y = y.1 - c := hax y hy0.symm
    rw [hxh, hyh]; linarith [fst_lt_of_le_of_ne hxy hne]
  obtain ⟨θ₁, θ₂, h₁, h₂, hV⟩ := hxy
  set P := lift x θ₁ with hP
  set Q := lift y θ₂ with hQ
  have hP1 : P.2.1 = 0 := by
    have : P.2.1 = rad x := rfl
    rw [this, ← hx]
  have hP2 : P.2.2 = 0 := by
    have : P.2.2 = -(rad x * θ₁) := rfl
    rw [this, ← hx]; ring
  have hP0 : P.1 = 2 * x.1 := by
    have : P.1 = 2 * x.1 + rad x * θ₁ ^ 2 - rad x := rfl
    rw [this, ← hx]; ring
  have hQ1 : Q.2.1 = rad y := rfl
  have hQ2 : Q.2.2 = -(rad y * θ₂) := rfl
  have hQ0 : Q.1 = 2 * y.1 + rad y * θ₂ ^ 2 - rad y := rfl
  obtain ⟨hA, hB, hC⟩ := hV
  set A := (Q - P).1 with hAdef
  set B := (Q - P).2.1 with hBdef
  set C := (Q - P).2.2 with hCdef
  have hBv : B = rad y := by simp [hBdef, hP1, hQ1]
  have hB0 : 0 < B := hBv ▸ hy0
  have hne' : ¬(A = 0 ∧ B = 0 ∧ C = 0) := fun h => hB0.ne' h.2.1
  set φ := segHeight g P.1 P.2.1 P.2.2 A B C with hφ
  have hder : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ e, HasDerivAt φ e s ∧ 0 < e := by
    intro s hs
    have hb : 0 < P.2.1 + s * B := by rw [hP1, zero_add]; exact mul_pos hs.1 hB0
    have hb1 : P.2.1 + s * B ≤ R := by
      rw [hP1, zero_add, hBv]; nlinarith [hs.2, rad_nonneg y]
    exact hasDerivAt_segHeight_pos hg hb hb1 hB hA hC hne'
  -- the segment read back in `𝔼₀`
  set θc : ℝ := -C / B with hθc
  set w : ℝ → E0 := fun s =>
    ((P.1 + s * A - (s * B) * θc ^ 2 + s * B) / 2, ((s * B : ℝ) : ℂ) * Complex.exp (θc * Complex.I))
    with hw
  have hwr : ∀ s, 0 ≤ s → rad (w s) = s * B := by
    intro s hs
    simp only [hw, rad, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [abs_of_nonneg hs, abs_of_nonneg hB0.le]
  have hwc : Continuous w := by
    simp only [hw]; fun_prop
  have hl : φ 0 = x.1 - c := by
    simp only [hφ, segHeight, hP1, hP2, hP0, zero_mul, add_zero, neg_zero, zero_div, hc]
    ring
  have hφw : ∀ s ∈ Icc (0 : ℝ) 1, φ s = height g (w s) := by
    intro s hs
    rcases hs.1.lt_or_eq with hs0 | hs0
    · have hpol : Polar (w s) θc := by
        unfold Polar; rw [hwr s hs.1]
      rw [← heightAt_eq_height hg.periodic hpol (by rw [hwr s hs.1]; positivity)]
      have hθ : -(0 + s * C) / (0 + s * B) = θc := by
        rw [hθc]; field_simp; ring
      show segHeight g P.1 P.2.1 P.2.2 A B C s = _
      unfold segHeight heightAt
      rw [hP1, hP2, hθ, hwr s hs.1]
      simp only [hw, zero_add]
    · subst hs0
      have h0 : rad (w 0) = 0 := by rw [hwr 0 le_rfl, zero_mul]
      have hr : height g (w 0) = x.1 - c := by
        rw [hax _ h0]; simp only [hw, hP0]; ring
      rw [hl, hr]
  have hcφ : ContinuousOn φ (Icc 0 1) := by
    refine ((hcont.comp hwc.continuousOn fun s hs => ?_).congr hφw)
    change rad (w s) ≤ R
    rw [hwr s hs.1, hBv]; nlinarith [hs.2, rad_nonneg y]
  have hpos : ∀ s ∈ interior (Icc (0 : ℝ) 1), 0 < deriv φ s := by
    intro s hs
    rw [interior_Icc] at hs
    obtain ⟨e, he, he0⟩ := hder s hs
    rw [he.deriv]; exact he0
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcφ hpos
  have hlt : φ 0 < φ 1 := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    zero_lt_one
  have e1 : φ 1 = heightAt g y θ₂ := by
    have hA' : P.1 + A = Q.1 := by simp [hAdef]
    have hB' : P.2.1 + B = Q.2.1 := by simp [hBdef]
    have hC' : P.2.2 + C = Q.2.2 := by simp [hCdef]
    show segHeight g P.1 P.2.1 P.2.2 A B C 1 = _
    unfold segHeight heightAt
    simp only [one_mul, hA', hB', hC', hQ0, hQ1, hQ2]
    have hθ : -(-(rad y * θ₂)) / rad y = θ₂ := by field_simp
    rw [hθ]
    ring
  rw [hxh, ← hl, ← heightAt_eq_height hg.periodic h₂ hy0, ← e1]
  exact hlt

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


open Classical in
/-- **B21 Lemma 2.9 in the pointwise reading** (WP-46e fixer, AUDIT-1 m1): `Σ` spacelike pointwise
off the axis (`IsSpacelikeGraph`, Lemma 2.7) with height continuous on the closed solid cylinder;
through `isSpacelikeDiscGraph_of_isSpacelikeGraph`. -/
theorem lem_intersect_number_compact_pointwise (hg : IsSpacelikeGraph g R)
    (hgc : ContinuousOn (height g) {x : E0 | rad x ≤ R})
    {c : ℝ → E0} {I : Set ℝ} (hI : I.OrdConnected) (hc : ContinuousOn c I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → Le (c s) (c t))
    (hreg : ∀ s ∈ I, rad (c s) ≤ R)
    (hpast : ∃ t ∈ I, height g (c t) < 0)
    (hfut : (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨ ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ rad (c b) = R) :
    (c '' I ∩ discGraphSet g R).ncard =
      if (∀ M : ℝ, ∃ t ∈ I, M ≤ (c t).1) ∨
          ∃ b ∈ I, (∀ t ∈ I, t ≤ b) ∧ ∃ y ∈ discGraphSet g R, rad y = R ∧ Le y (c b)
        then 1 else 0 :=
  lem_intersect_number_compact (isSpacelikeDiscGraph_of_isSpacelikeGraph hg hgc) hI hc hmono hreg
    hpast hfut

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
      Tendsto G (comap Prod.fst (𝓝[>] 0)) atTop ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt G L p ∧
        1 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1) := by
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
    tendsto_atTop_add_const_right _ c₀ hlim, hδG⟩
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

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The `C¹` rim condition** on a surface `S` (the field `rim` of `IsE0C1SpacelikeCauchy`,
verbatim; T-gx-btz-cleanup, moved here from `GXScaffold.BTZ.SpearFamily`): the trace of `S` on the
shaft of every spear chart meeting it along a continuous graph is a `C¹` circle. With the Cauchy
property it is all the spear data of the surgery use of `S` (`exists_spearSurgeryDatum`,
`exists_spearSurgeryDatum_cover`, `SpearSurgeryDatum.exists_shrink`); neither compactness nor the
spacelike Lipschitz condition is used there. -/
def RimC1 (S : Set M) : Prop :=
  ∀ (R v : ℝ) (W : Set E0Y) (ψ : E0Y → M) (τS : ℂ → ℝ), 0 < R → IsOpen W →
    E0Spear.spearY v R ⊆ W → E0Spear.IsE0Mor ψ W → InjOn ψ W →
    ContinuousOn τS (Metric.closedBall 0 R) →
    (∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS z) →
    (∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2)) →
    ContDiff ℝ 1 (rimFun τS R)

omit [SecondCountableTopology M] in
variable {M} in
/-- A `C¹` spacelike compact Cauchy surface satisfies the rim condition. -/
theorem IsE0C1SpacelikeCauchy.rimC1 {S : Set M} (hS : IsE0C1SpacelikeCauchy M S) : RimC1 M S :=
  hS.rim

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
  /-- Lemma 2.8(1)'s hypothesis with `C = 1`, which Lemma 2.6(ii)'s cusp satisfies on all of
  `{r > 0}` (WP-46e: consumed by the completeness of `Σ*`, (G5)). -/
  delta : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt G L q ∧
    1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1

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
the graph of `τ_Σ` in the shaft; its rim is `C¹` (`RimC1`, e.g. `IsE0C1SpacelikeCauchy.rimC1`),
and Lemma 2.6(ii) (`lem_curve_extension_ii_shift`, with Lemma 2.8(1)) extends it to a complete
spacelike graph. Of `S` only its Cauchy property and its rim condition are used
(T-gx-btz-cleanup: for `hS : IsE0C1SpacelikeCauchy M S`, pass `hS.cauchy hS.rimC1`). -/
theorem exists_spearSurgeryDatum (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) (hrim : RimC1 M S)
    (hmax : E0Spear.IsE0CauchyMaximal M) {p : M}
    (hp : p ∈ E0CBG.S0 M) (hpS : p ∈ (E0CBG.CE M).Iminus ⊤ S) :
    ∃ D : SpearSurgeryDatum M S, D.p = p := by
  obtain ⟨R, v, W, ψ, hR, hW, hsub, hψ, hinj, hpv, τS, h0, h1, h2⟩ :=
    E0Spear.lem_add_BTZ_param_of_cauchyMaximal E0LM.e0_globalBTZ
      (fun {_} _ _ _ _ _ => E0LM.e0_secondCountable_of_cauchy) hGH hS hmax hp hpS
  have hC1 := hrim R v W ψ τS hR hW hsub hψ hinj h0 h1 h2
  obtain ⟨G, hrim, hsl, habove, hC, hcomp, hlim, hδ⟩ :=
    lem_curve_extension_ii_shift (n := 1) le_rfl hC1 (rimFun_periodic τS R) (c₀ := v + R / 2)
      (fun θ => h1 _ (norm_rimPoint hR.le θ).le) hR
  exact ⟨⟨p, R, v, W, ψ, τS, G, hp, hpS, hR, hW, hsub, hψ, hinj, hpv, h0, h1, h2, hrim, hsl,
    habove, hC, hcomp, hlim, hδ⟩, rfl⟩


omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **A spear of the surgery can be thinned** (the tool of B21's « one can take the spear
neighbourhoods disjoint », l.1091): for every `0 < R' ≤ R` the same chart, restricted to the spear
of radius `R'`, carries a datum (the rim at `R'` is again `C¹`, and Lemma 2.6(ii) is re-applied).
Of `S` only the rim condition is used (T-gx-btz-cleanup). -/
theorem SpearSurgeryDatum.exists_shrink {S : Set M} (hrim : RimC1 M S)
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
  have hC1 := hrim R' D.v D.W D.ψ D.τS hR' D.isOpen hsubY D.mor D.inj
    (D.continuousOn.mono (Metric.closedBall_subset_closedBall hle)) hshaft hgraph
  obtain ⟨G, hrim, hsl, habove, hC, hcomp, hlim, hδ⟩ :=
    lem_curve_extension_ii_shift (n := 1) le_rfl hC1 (rimFun_periodic D.τS R')
      (c₀ := D.v + R' / 2) (fun θ => hshaft _ (norm_rimPoint hR'.le θ).le) hR'
  exact ⟨⟨D.p, R', D.v, D.W, D.ψ, D.τS, G, D.p_mem, D.p_past, hR', D.isOpen, hsubY, D.mor, D.inj,
    D.vertex, D.continuousOn.mono (Metric.closedBall_subset_closedBall hle), hshaft, hgraph, hrim,
    hsl, habove, hC, hcomp, hlim, hδ⟩, rfl, rfl, rfl, rfl⟩

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


/-! ### §5e The global part: the pieces that are proved (WP-44e)

The spears of the surgery are **closed** in `M` (`isClosed_image_spearY`: a sequence of the spear
either stays in a compact `{τ ≤ B}` part or climbs, and then the vertical line under its limit
would be a monotone curve in a compact diamond, against `E0Spear.spear_vertical_noLimit`). -/

section GlobalPieces

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **A spear of an injective `𝔼₀`-chart is closed in `M`** (B21 Def 2.1: the frontier of a spear
neighbourhood is its head and its shaft). -/
theorem isClosed_image_spearY (hGH : (E0CBG.CE M).GloballyHyperbolic) {v R : ℝ} {W : Set E0Y}
    {ψ : E0Y → M} (hW : IsOpen W) (hsub : E0Spear.spearY v R ⊆ W) (hψ : E0Spear.IsE0Mor ψ W)
    (hinj : InjOn ψ W) : IsClosed (ψ '' E0Spear.spearY v R) := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hT := hA.tarentin
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage E0Spear.continuous_paperInY
  set O : TopologicalSpace.Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
  have hSO : E0Spear.spear v R ⊆ O := fun x hx => hsub ⟨x, hx, rfl⟩
  have hΦc : ∀ x ∈ E0Spear.spear v R, ContinuousAt (fun x : E0 => ψ (paperInY x)) x := fun x hx =>
    (hψc.continuousAt (hW.mem_nhds (hSO hx))).comp E0Spear.continuous_paperInY.continuousAt
  rw [← isSeqClosed_iff_isClosed]
  intro u m hu hlim
  choose y hy hyu using hu
  choose x hx hxy using hy
  have hux : ∀ n, u n = ψ (paperInY (x n)) := fun n => by rw [hxy, hyu]
  by_cases hb : ∃ B, ∃ᶠ n in atTop, (x n).1 ≤ B
  · obtain ⟨B, hB⟩ := hb
    obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_of_frequently_atTop hB
    have hK : IsCompact (Icc v B ×ˢ Metric.closedBall (0 : ℂ) R) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hxK : ∀ n, x (φ n) ∈ Icc v B ×ˢ Metric.closedBall (0 : ℂ) R := fun n => by
      have h1 := (hx (φ n)).1
      have h2 := (hx (φ n)).2
      simp only [fcoord] at h1
      refine ⟨⟨by linarith [rad_nonneg (x (φ n))], hφB n⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]; exact h2
    obtain ⟨x₀, -, φ', hφ', hlim'⟩ := hK.tendsto_subseq hxK
    have hx₀ : x₀ ∈ E0Spear.spear v R :=
      (E0Spear.isClosed_spear v R).mem_of_tendsto hlim' (Eventually.of_forall fun n => hx _)
    have h1 : Tendsto (fun n => u (φ (φ' n))) atTop (𝓝 (ψ (paperInY x₀))) := by
      simp only [hux]
      exact (hΦc x₀ hx₀).tendsto.comp hlim'
    have h2 : Tendsto (fun n => u (φ (φ' n))) atTop (𝓝 m) :=
      hlim.comp (hφ.comp hφ').tendsto_atTop
    rw [tendsto_nhds_unique h2 h1]
    exact ⟨paperInY x₀, ⟨x₀, hx₀, rfl⟩, rfl⟩
  · exfalso
    push Not at hb
    have hzK : ∀ n, (x n).2 ∈ Metric.closedBall (0 : ℂ) R := fun n => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (hx n).2
    obtain ⟨z, hz, φ, hφ, hzlim⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hzK
    have hzR : ‖z‖ ≤ R := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
    set c : ℝ := v + R / 2 with hc
    have hmemT : ∀ (T : ℝ) (w : ℂ), c ≤ T → ‖w‖ ≤ R → ((T, w) : E0) ∈ E0Spear.spear v R :=
      fun T w hT hw => ⟨by simp only [fcoord, rad]; linarith, hw⟩
    have hle_closed := hGH.isClosed_le hT
    -- every point of the vertical line over the limit `z` lies below `m`
    have hbelow : ∀ T, c ≤ T → (E0CBG.CE M).le ⊤ (ψ (paperInY (T, z))) m := by
      intro T hTc
      have hev : ∀ᶠ n in atTop, (E0CBG.CE M).le ⊤ (ψ (paperInY (T, (x (φ n)).2))) (u (φ n)) := by
        filter_upwards [(hφ.tendsto_atTop).eventually (hb T)] with n hn
        rw [hux]
        have hxn : x (φ n) = ((x (φ n)).1, (x (φ n)).2) := rfl
        conv_rhs => rw [hxn]
        exact E0Spear.le_of_isE0Mor_paper hW hψ (U := O) subset_rfl
          (E0Spear.le_of_le_top_of_mem_spear hSO (hmemT T _ hTc (hx (φ n)).2)
            (by rw [← hxn]; exact hx (φ n)) (E0Spear.le_vertical_top hn.le))
      have hpair : Tendsto (fun n => (ψ (paperInY (T, (x (φ n)).2)), u (φ n))) atTop
          (𝓝 (ψ (paperInY (T, z)), m)) := by
        refine Tendsto.prodMk_nhds ?_ (hlim.comp hφ.tendsto_atTop)
        exact (hΦc _ (hmemT T z hTc hzR)).tendsto.comp
          ((tendsto_const_nhds (x := T)).prodMk_nhds hzlim)
      exact hle_closed.mem_of_tendsto hpair hev
    have hmono : ∀ s t, c ≤ s → s ≤ t →
        (E0CBG.CE M).le ⊤ (ψ (paperInY (s, z))) (ψ (paperInY (t, z))) := fun s t hs hst =>
      E0Spear.le_of_isE0Mor_paper hW hψ (U := O) subset_rfl
        (E0Spear.le_of_le_top_of_mem_spear hSO (hmemT s z hs hzR) (hmemT t z (hs.trans hst) hzR)
          (E0Spear.le_vertical_top hst))
    obtain ⟨q, hq⟩ := E0Spear.exists_tendsto_of_monotone hGH (t₀ := c) hmono
      (hGH.2 (ψ (paperInY (c, z))) m) fun t ht =>
        Causal.Causality.mem_diamond.2 ⟨hmono c t le_rfl ht, hbelow t ht⟩
    exact E0Spear.spear_vertical_noLimit hGH hW hsub hψ hinj hzR q hq


/-- **A point strictly below a point of a Cauchy surface is in its chronological past** (the
hypothesis `p ∈ I⁻(Σ)` of Lemma 2.4 for the vertices of the surgery, B21 l.1090): `p ∉ J⁺(Σ)`
(acausality), `J⁺(Σ)` is closed, `p` is a limit of its chronological future (every point is
strongly tarentin in the future), and a point of `I⁺(p)` off `J⁺(Σ)` is in `J⁻(Σ)`; push-up. -/
theorem mem_Iminus_of_le_of_mem (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) {p q : M} (hq : q ∈ S)
    (hpq : (E0CBG.CE M).le ⊤ p q) (hne : p ≠ q) : p ∈ (E0CBG.CE M).Iminus ⊤ S := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hS.isAcausal E0LM.e0_causallyArcConnected hext
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hS
  have hpJ : p ∉ (E0CBG.CE M).Jplus ⊤ S := by
    rintro ⟨s, hs, hsp⟩
    have hsq := hac s hs q hq ((E0CBG.CE M).le_trans hsp hpq)
    subst hsq
    exact hne (hGH.1 hpq hsp)
  have hcl : p ∈ closure ((E0CBG.CE M).Iplus ⊤ {p}) :=
    E0LM.Jplus_subset_closure_Iplus hA.pushUp hA.mem_Zplus p
      (Causal.Precausality.mem_Jplus_singleton.2
        ((E0CBG.CE M).le_refl (show p ∈ (⊤ : TopologicalSpace.Opens M) from trivial)))
  obtain ⟨y, hyN, hyI⟩ := mem_closure_iff_nhds.1 hcl _ (hJp.isOpen_compl.mem_nhds hpJ)
  obtain ⟨s, hs, hys⟩ :=
    (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hS y).resolve_left hyN
  exact ⟨s, hs, hA.pushUp.lt_of_lt_of_le (Causal.Precausality.mem_Iplus_singleton.1 hyI) hys⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- `S₀(M)` is closed. -/
theorem isClosed_S0 : IsClosed (E0CBG.S0 M) :=
  E0LM.charted_isClosed_sing e0_sing_mem le_rfl (E0LM.isClosed_e0SingY 0)

namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The BTZ ray of a spear datum. -/
theorem ray : E0Spear.IsFullFutureBTZRay D.p (fun t => D.ψ (E0Spear.yAxis D.v t)) :=
  ⟨D.v, D.W, D.ψ, D.isOpen, fun _ ht => D.spear_sub (E0Spear.yAxis_mem_spearY D.pos.le ht), D.mor,
    D.inj, D.vertex, fun _ => rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The ray of a spear datum lies in the BTZ line (component of `S₀`) of its vertex. -/
theorem ray_mem_component {t : ℝ} (ht : 0 ≤ t) :
    D.ψ (E0Spear.yAxis D.v t) ∈ connectedComponentIn (E0CBG.S0 M) D.p := by
  have hr := D.ray
  have hpre : IsPreconnected ((fun t => D.ψ (E0Spear.yAxis D.v t)) '' Ici 0) :=
    isPreconnected_Ici.image _ hr.continuousOn
  exact hpre.subset_connectedComponentIn ⟨0, self_mem_Ici, hr.zero⟩
    (by rintro _ ⟨u, hu, rfl⟩; exact hr.mem_S0 hu) ⟨t, ht, rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The BTZ points of a spear are those of its ray.** -/
theorem eq_ray_of_mem_S0 {y : M} (hy : y ∈ D.spearSet) (hy0 : y ∈ E0CBG.S0 M) :
    ∃ t, 0 ≤ t ∧ y = D.ψ (E0Spear.yAxis D.v t) := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  have hr0 : rad x = 0 := (D.mem_S0_iff hx).1 hy0
  have hx2 : x.2 = 0 := norm_eq_zero.1 hr0
  refine ⟨x.1 - D.v, ?_, ?_⟩
  · have := hx.1; simp only [fcoord, hr0] at this; linarith
  · show D.ψ (paperInY x) = D.ψ (paperInY ((D.v + (x.1 - D.v), 0) : E0))
    congr 2
    exact Prod.ext (by simp) hx2

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem spearSet_inter_S0_subset {y : M} (hy : y ∈ D.spearSet) (hy0 : y ∈ E0CBG.S0 M) :
    y ∈ connectedComponentIn (E0CBG.S0 M) D.p := by
  obtain ⟨t, ht, rfl⟩ := D.eq_ray_of_mem_S0 hy hy0
  exact D.ray_mem_component ht

omit [ConnectedSpace M] in
/-- **A Cauchy surface meets a spear's BTZ points at most once** (they lie on one ray). -/
theorem eq_of_mem_S0_of_mem (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {y y' : M} (hy : y ∈ D.spearSet ∩ E0CBG.S0 M ∩ S)
    (hy' : y' ∈ D.spearSet ∩ E0CBG.S0 M ∩ S) : y = y' := by
  have hac := hS.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)
  obtain ⟨t, ht, rfl⟩ := D.eq_ray_of_mem_S0 hy.1.1 hy.1.2
  obtain ⟨t', ht', rfl⟩ := D.eq_ray_of_mem_S0 hy'.1.1 hy'.1.2
  rcases le_total t t' with h | h
  · exact hac _ hy.2 _ hy'.2 (D.ray.le ht h)
  · exact (hac _ hy'.2 _ hy.2 (D.ray.le ht' h)).symm

end SpearSurgeryDatum

/-- **A spear datum whose ray passes through a given BTZ point of `S`** (B21 l.1090–1091: the
vertex is taken on the BTZ line below the point, in `I⁻(Σ)` by `mem_Iminus_of_le_of_mem`; the ray
then covers the future half of the line, `IsFullFutureBTZRay.exists_eq_of_line`). Of `S` only its
Cauchy property and its rim condition are used (T-gx-btz-cleanup). -/
theorem exists_spearSurgeryDatum_cover (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) (hrim : RimC1 M S)
    (hmax : E0Spear.IsE0CauchyMaximal M) {q : M} (hq : q ∈ S) (hq0 : q ∈ E0CBG.S0 M) :
    ∃ D : SpearSurgeryDatum M S, q ∈ connectedComponentIn (E0CBG.S0 M) D.p ∧
      ∃ t, 0 < t ∧ q = D.ψ (E0Spear.yAxis D.v t) := by
  obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := (E0LM.e0_globalBTZ M).line q hq0
  have hγe' := hγe hGH.1
  have hpq : (E0CBG.CE M).le ⊤ (γ (-1)) q := by
    rw [← hγ0]; exact hγi.1.le_of_le trivial trivial (by norm_num)
  have hne : γ (-1) ≠ q := fun h => by
    have := hγe'.injective (h.trans hγ0.symm); norm_num at this
  have hpcomp : γ (-1) ∈ connectedComponentIn (E0CBG.S0 M) q := hγr ▸ mem_range_self _
  have hp0 : γ (-1) ∈ E0CBG.S0 M := connectedComponentIn_subset _ _ hpcomp
  have hpS := mem_Iminus_of_le_of_mem hGH hS hq hpq hne
  obtain ⟨D, hDp⟩ := exists_spearSurgeryDatum hGH hS hrim hmax hp0 hpS
  have hqcomp : q ∈ connectedComponentIn (E0CBG.S0 M) D.p := by
    rw [hDp, ← connectedComponentIn_eq hpcomp]; exact mem_connectedComponentIn hq0
  refine ⟨D, hqcomp, ?_⟩
  obtain ⟨γ', hγ'0, hγ'e, hγ'i, hγ'r⟩ := (E0LM.e0_globalBTZ M).line D.p D.p_mem
  obtain ⟨s, hs⟩ : q ∈ range γ' := hγ'r ▸ hqcomp
  have hs0 : 0 ≤ s := by
    by_contra hneg
    push Not at hneg
    have h1 : (E0CBG.CE M).le ⊤ q D.p := by
      rw [← hs, ← hγ'0]; exact hγ'i.1.le_of_le trivial trivial hneg.le
    rw [hDp] at h1
    exact hne (hGH.1 hpq h1)
  obtain ⟨t, ht, hts⟩ := D.ray.exists_eq_of_line hGH hγ'0 (hγ'e hGH.1) hγ'i.1 hγ'r hs0
  refine ⟨t, lt_of_le_of_ne ht fun h0 => ?_, by rw [← hs, ← hts]⟩
  subst h0
  have : D.ψ (E0Spear.yAxis D.v 0) = D.p := D.ray.zero
  rw [hts, hs, hDp] at this
  exact hne this.symm

/-- **`S ∩ sing₀(M)` is finite** (B21 l.1091: « Since `M` is Cauchy-compact, it admits finitely
many BTZ-lines »): it is compact, and each of its points `q` has an open neighbourhood — the
interior of a spear whose ray passes through `q` — in which it is the only one (the BTZ points of
a spear are on one causal ray, and `S` is acausal). -/
theorem finite_inter_S0 (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    (S ∩ E0CBG.S0 M).Finite := by
  have hK : IsCompact (S ∩ E0CBG.S0 M) := hS.compact.inter_right isClosed_S0
  have hD : ∀ q : ↥(S ∩ E0CBG.S0 M), ∃ D : SpearSurgeryDatum M S,
      q.1 ∈ connectedComponentIn (E0CBG.S0 M) D.p ∧
        ∃ t, 0 < t ∧ q.1 = D.ψ (E0Spear.yAxis D.v t) := fun q =>
    exists_spearSurgeryDatum_cover hGH hS.cauchy hS.rimC1 hmax q.2.1 q.2.2
  choose D hDc t ht hqt using hD
  set A : ℝ → ℝ → Set E0 := fun v R => {x | v < fcoord x ∧ rad x < R}
  have hAo : ∀ v R, IsOpen (A v R) := fun v R =>
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  set O : ↥(S ∩ E0CBG.S0 M) → Set M := fun q =>
    (D q).ψ '' (paperInY '' A (D q).v (D q).R)
  have hAsub : ∀ q, paperInY '' A (D q).v (D q).R ⊆ (D q).W := by
    rintro q _ ⟨x, hx, rfl⟩
    exact (D q).spear_sub ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
  have hOo : ∀ q, IsOpen (O q) := fun q =>
    (Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ
      (W := ⟨(D q).W, (D q).isOpen⟩) (D q).mor).isOpen_image
      ⟨_, E0Spear.isOpen_paperInY_image (hAo _ _)⟩ (hAsub q)
  have hqO : ∀ q, q.1 ∈ O q := fun q => by
    rw [hqt q]
    refine ⟨_, ⟨((D q).v + t q, 0), ⟨?_, ?_⟩, rfl⟩, rfl⟩
    · simp only [fcoord, rad, norm_zero]; linarith [ht q]
    · simp only [rad, norm_zero]; exact (D q).pos
  have hOsub : ∀ q, O q ⊆ (D q).spearSet := fun q => by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := hK.elim_finite_subcover O hOo fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hqO _⟩
  refine (u.finite_toSet.image Subtype.val).subset fun y hy => ?_
  obtain ⟨q, hqu, hyq⟩ := mem_iUnion₂.1 (hu hy)
  refine ⟨q, hqu, ?_⟩
  have hqmem : q.1 ∈ (D q).spearSet ∩ E0CBG.S0 M ∩ S := ⟨⟨hOsub q (hqO q), q.2.2⟩, q.2.1⟩
  exact (D q).eq_of_mem_S0_of_mem hGH hS.cauchy hqmem ⟨⟨hOsub q hyq, hy.2⟩, hy.1⟩


/-- The radial null segment of `𝔼₀` from the axis point `(f(x), 0)` (`s = 0`) to `x` (`s = 1`). -/
noncomputable def radialSeg (x : E0) (s : ℝ) : E0 :=
  (x.1 - rad x / 2 + s * (rad x / 2), (s : ℂ) * x.2)

theorem rad_radialSeg (x : E0) {s : ℝ} (hs : 0 ≤ s) : rad (radialSeg x s) = s * rad x := by
  simp only [radialSeg, rad, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

theorem fcoord_radialSeg (x : E0) {s : ℝ} (hs : 0 ≤ s) : fcoord (radialSeg x s) = fcoord x := by
  simp only [fcoord, rad_radialSeg x hs]
  simp only [radialSeg]
  ring

theorem continuous_radialSeg (x : E0) : Continuous (radialSeg x) := by
  unfold radialSeg; fun_prop

theorem radialSeg_one (x : E0) : radialSeg x 1 = x := by
  simp only [radialSeg, Complex.ofReal_one, one_mul]
  exact Prod.ext (by ring) rfl

theorem radialSeg_zero (x : E0) : radialSeg x 0 = ((fcoord x, 0) : E0) := by
  simp only [radialSeg, Complex.ofReal_zero, zero_mul, fcoord]
  exact Prod.ext (by ring) rfl

/-- **The radial segment is future null**: `σ(s) ≼ σ(s′)` for `0 ≤ s ≤ s′` (same angle, `δ = 0`). -/
theorem le_radialSeg (x : E0) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') :
    Le (radialSeg x s) (radialSeg x s') := by
  have hpol : ∀ u, 0 ≤ u → Polar (radialSeg x u) (Complex.arg x.2) := fun u hu => by
    show (radialSeg x u).2 = (rad (radialSeg x u) : ℂ) * Complex.exp (Complex.arg x.2 * Complex.I)
    rw [rad_radialSeg x hu]
    have h := polar_arg x
    simp only [Polar] at h
    simp only [radialSeg]
    conv_lhs => rw [h]
    push_cast
    ring
  rw [le_iff_closed]
  refine ⟨_, _, hpol s hs, hpol s' (hs.trans hss'), ?_⟩
  rw [rad_radialSeg x hs, rad_radialSeg x (hs.trans hss')]
  have hr := rad_nonneg x
  refine ⟨?_, mul_le_mul_of_nonneg_right hss' hr, ?_⟩
  · simp only [radialSeg]; nlinarith
  · simp only [radialSeg, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]
    nlinarith

namespace SpearSurgeryDatum

variable {S : Set M}

/-- **The head argument for disjoint spears** (B21 l.1091, « one can take the spear
neighbourhoods disjoint », with the argument B21 does not print). If the ray of `D₁` misses the
spear of `D₂` and the head of `D₂` misses the spear of `D₁`, the two spears are disjoint: a common
point `ψ₁(x)` is joined to the ray of `D₁` by the radial null segment, inside the first spear; the
last time it enters the (closed) second spear, read in the second chart (the inverse chart is an
`𝔼₀`-morphism, so the segment stays `≼`-below the entry point there), the entry point has `r ≤ R₂`
below it and `f ≥ v₂`, so the points just before it would be in the spear unless the entry is on
the head `{f = v₂}`. -/
theorem disjoint_of_head (hGH : (E0CBG.CE M).GloballyHyperbolic) (D₁ D₂ : SpearSurgeryDatum M S)
    (h0 : ∀ t, 0 ≤ t → D₁.ψ (E0Spear.yAxis D₁.v t) ∉ D₂.spearSet)
    (hhead : ∀ x ∈ E0Spear.spear D₂.v D₂.R, fcoord x = D₂.v → D₂.ψ (paperInY x) ∉ D₁.spearSet) :
    Disjoint D₁.spearSet D₂.spearSet := by
  rw [Set.disjoint_left]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ha
  set Φ₁ : E0 → M := fun y => D₁.ψ (paperInY y) with hΦ₁
  have hσmem : ∀ s ∈ Icc (0 : ℝ) 1, radialSeg x s ∈ E0Spear.spear D₁.v D₁.R := fun s hs => by
    refine ⟨?_, ?_⟩
    · rw [fcoord_radialSeg x hs.1]; exact hx.1
    · rw [rad_radialSeg x hs.1]
      calc s * rad x ≤ 1 * rad x := mul_le_mul_of_nonneg_right hs.2 (rad_nonneg x)
        _ = rad x := one_mul _
        _ ≤ D₁.R := hx.2
  have hψ₁c : ContinuousOn D₁.ψ D₁.W := fun y hy => (D₁.mor y hy).continuousWithinAt
  have hP₁ : IsOpen (paperInY ⁻¹' D₁.W) := D₁.isOpen.preimage E0Spear.continuous_paperInY
  have hΦ₁c : ContinuousOn Φ₁ (paperInY ⁻¹' D₁.W) :=
    hψ₁c.comp E0Spear.continuous_paperInY.continuousOn (fun _ h => h)
  have hσW : ∀ s ∈ Icc (0 : ℝ) 1, radialSeg x s ∈ paperInY ⁻¹' D₁.W := fun s hs =>
    D₁.spear_sub ⟨_, hσmem s hs, rfl⟩
  have hcl₂ : IsClosed D₂.spearSet := isClosed_image_spearY hGH D₂.isOpen D₂.spear_sub D₂.mor D₂.inj
  set A : Set ℝ := {s ∈ Icc (0 : ℝ) 1 | Φ₁ (radialSeg x s) ∈ D₂.spearSet} with hA
  have hAcl : IsClosed A :=
    ((hΦ₁c.comp (continuous_radialSeg x).continuousOn hσW).preimage_isClosed_of_isClosed
      isClosed_Icc hcl₂)
  have h1A : (1 : ℝ) ∈ A := ⟨⟨zero_le_one, le_rfl⟩, by simp only [hΦ₁, radialSeg_one]; exact ha⟩
  have h0A : (0 : ℝ) ∉ A := by
    rintro ⟨-, h⟩
    have hfx : D₁.v ≤ fcoord x := hx.1
    refine h0 (fcoord x - D₁.v) (by linarith) ?_
    simp only [hΦ₁, radialSeg_zero] at h
    show D₁.ψ (paperInY ((D₁.v + (fcoord x - D₁.v), 0) : E0)) ∈ D₂.spearSet
    rwa [show D₁.v + (fcoord x - D₁.v) = fcoord x by ring]
  set B : Set ℝ := Icc (0 : ℝ) 1 \ A with hB
  have hB0 : (0 : ℝ) ∈ B := ⟨⟨le_rfl, zero_le_one⟩, h0A⟩
  have hBbdd : BddAbove B := ⟨1, fun s hs => hs.1.2⟩
  set s₀ := sSup B with hs₀
  have hs₀1 : s₀ ≤ 1 := csSup_le ⟨0, hB0⟩ fun s hs => hs.1.2
  have hs₀0 : 0 ≤ s₀ := le_csSup hBbdd hB0
  have hs₀A : s₀ ∈ A := by
    by_contra hn
    have hs₀ne : s₀ ≠ 1 := fun h => hn (h ▸ h1A)
    have hs₀lt : s₀ < 1 := lt_of_le_of_ne hs₀1 hs₀ne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAcl.isOpen_compl s₀ hn
    set s' := min 1 (s₀ + ε / 2)
    have hs'B : s' ∈ B := by
      refine ⟨⟨by positivity, min_le_left _ _⟩, fun hs'A => hball ?_ hs'A⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have : s₀ ≤ s' := le_min hs₀1 (by linarith)
        linarith
      · have : s' ≤ s₀ + ε / 2 := min_le_right _ _
        linarith
    have : s' ≤ s₀ := le_csSup hBbdd hs'B
    have : s₀ < s' := lt_min hs₀lt (by linarith)
    linarith
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, hy₀⟩ := hs₀A.2
  -- `y₀ = ψ₂(x₀)` lies on the head of the second spear
  have hhd : fcoord x₀ ≤ D₂.v := by
    by_contra hlt
    push Not at hlt
    -- the inverse of the second chart
    set g := invFunOn D₂.ψ D₂.W with hg
    have hgmor : E0Spear.IsE0Mor g (D₂.ψ '' D₂.W) :=
      Causal.CBG.liftPropOn_invFunOn D₂.isOpen D₂.mor D₂.inj
    have hM₂ := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ (W := ⟨D₂.W, D₂.isOpen⟩) D₂.mor
    have hM₁ := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ (W := ⟨D₁.W, D₁.isOpen⟩) D₁.mor
    have hV₂o : IsOpen (D₂.ψ '' D₂.W) := hM₂.isOpen_image ⟨D₂.W, D₂.isOpen⟩ le_rfl
    have hMg := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ (W := ⟨_, hV₂o⟩) hgmor
    -- the open neighbourhood of `x₀` above the head
    set N₀ : Set E0 := paperInY ⁻¹' D₂.W ∩ {u | D₂.v < fcoord u} with hN₀
    have hN₀o : IsOpen N₀ := (D₂.isOpen.preimage E0Spear.continuous_paperInY).inter
      (isOpen_lt continuous_const continuous_fcoord)
    have hN₀W : paperInY '' N₀ ⊆ D₂.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    set U₂ : Set M := D₂.ψ '' (paperInY '' N₀) with hU₂
    have hU₂o : IsOpen U₂ := hM₂.isOpen_image ⟨_, E0Spear.isOpen_paperInY_image hN₀o⟩ hN₀W
    have hx₀N : x₀ ∈ N₀ := ⟨D₂.spear_sub ⟨x₀, hx₀, rfl⟩, hlt⟩
    have hy₀U : D₂.ψ (paperInY x₀) ∈ U₂ := ⟨_, ⟨x₀, hx₀N, rfl⟩, rfl⟩
    -- the open neighbourhood of `σ(s₀)` sent into `U₂`
    set O : Set E0 := paperInY ⁻¹' D₁.W ∩ Φ₁ ⁻¹' U₂ with hO
    have hOo : IsOpen O := hΦ₁c.isOpen_inter_preimage hP₁ hU₂o
    have hσ₀O : radialSeg x s₀ ∈ O := ⟨hσW s₀ ⟨hs₀0, hs₀1⟩, by
      show Φ₁ (radialSeg x s₀) ∈ U₂; rw [← hy₀]; exact hy₀U⟩
    obtain ⟨V, hVn, hVO, hVc⟩ := E0.stronglyCausal (radialSeg x s₀) O (hOo.mem_nhds hσ₀O)
    have hσV : radialSeg x ⁻¹' V ∈ 𝓝 s₀ := (continuous_radialSeg x).continuousAt.preimage_mem_nhds hVn
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hσV
    obtain ⟨s, hsB, hs⟩ := exists_lt_of_lt_csSup ⟨0, hB0⟩ (show s₀ - δ < s₀ by linarith)
    have hss₀ : s ≤ s₀ := le_csSup hBbdd hsB
    have hsV : radialSeg x s ∈ V := hδV (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hs₀V : radialSeg x s₀ ∈ V := hδV (Metric.mem_ball_self hδ)
    -- the relation along the segment, realised in `O`
    set OO : TopologicalSpace.Opens E0 := ⟨O, hOo⟩
    have hle₀ : E0.causality.le OO (radialSeg x s) (radialSeg x s₀) :=
      Causal.Causality.le_of_causallyConvexIn E0.causallyArcConnected hVc hVO hsV hs₀V
        ((E0.le_top_iff).2 (le_radialSeg x hsB.1.1 hss₀))
    -- into `M`, inside `U₂`
    have hOW₁ : (Causal.chartImage paperInY OO : Set E0Y) ⊆ D₁.W := by
      rw [Causal.coe_chartImage]
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      exact hz.1
    have hleM : (E0CBG.CE M).le ⟨U₂, hU₂o⟩ (Φ₁ (radialSeg x s)) (Φ₁ (radialSeg x s₀)) := by
      refine hM₁.map_le (Causal.chartImage paperInY OO) ⟨U₂, hU₂o⟩ hOW₁ ?_ ?_
      · rw [Causal.coe_chartImage]
        rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
        exact hz.2
      · have hD := E0Spear.D_le_of_le hle₀
        exact (E0Spear.ceY_le_iff (E0LM.D.le_mem_left hD) (E0LM.D.le_mem_right hD)).2 hD
    -- back into `𝔼₀` through the second chart
    obtain ⟨_, ⟨u, huN, rfl⟩, hu⟩ : Φ₁ (radialSeg x s) ∈ U₂ := (hVO hsV).2
    set RI : TopologicalSpace.Opens E0Y := ⟨range Sum.inr, isOpen_range_inr⟩
    have hgu : g (D₂.ψ (paperInY u)) = paperInY u :=
      D₂.inj.leftInvOn_invFunOn (hN₀W ⟨u, huN, rfl⟩)
    have hgx₀ : g (D₂.ψ (paperInY x₀)) = paperInY x₀ :=
      D₂.inj.leftInvOn_invFunOn (hN₀W ⟨x₀, hx₀N, rfl⟩)
    have hU₂V₂ : (⟨U₂, hU₂o⟩ : TopologicalSpace.Opens M) ≤ ⟨_, hV₂o⟩ :=
      image_mono hN₀W
    have hmaps : MapsTo g U₂ RI := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show g (D₂.ψ (paperInY w)) ∈ range Sum.inr
      rw [show g (D₂.ψ (paperInY w)) = paperInY w from
        D₂.inj.leftInvOn_invFunOn (hN₀W ⟨w, hw, rfl⟩), paperInY_apply]
      exact mem_range_self _
    have hleY := hMg.map_le ⟨U₂, hU₂o⟩ RI hU₂V₂ hmaps (x := Φ₁ (radialSeg x s))
      (y := Φ₁ (radialSeg x s₀)) hleM
    rw [← hu, ← hy₀, hgu, hgx₀] at hleY
    have hRu : paperInY u ∈ RI := ⟨_, (paperInY_apply u).symm⟩
    have hRx : paperInY x₀ ∈ RI := ⟨_, (paperInY_apply x₀).symm⟩
    have hLe : Le u x₀ :=
      (E0.le_top_iff).1 ((E0Spear.D_le_rangeInr_iff u x₀).1 ((E0Spear.ceY_le_iff hRu hRx).1 hleY))
    -- so `u` is in the second spear, and `s ∈ A`
    have huS : u ∈ E0Spear.spear D₂.v D₂.R := ⟨huN.2.le, hLe.closed.2.1.trans hx₀.2⟩
    exact hsB.2 ⟨hsB.1, by rw [← hu]; exact ⟨_, ⟨u, huS, rfl⟩, rfl⟩⟩
  refine hhead x₀ hx₀ (le_antisymm hhd hx₀.1) ?_
  rw [hy₀]
  exact ⟨_, ⟨_, hσmem s₀ ⟨hs₀0, hs₀1⟩, rfl⟩, rfl⟩

end SpearSurgeryDatum


/-- **A Cauchy surface meets each BTZ line at most once** (a BTZ line is a causal curve). -/
theorem eq_of_mem_component (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) {p : M} (hp : p ∈ E0CBG.S0 M) {q q' : M}
    (hq : q ∈ S ∩ connectedComponentIn (E0CBG.S0 M) p)
    (hq' : q' ∈ S ∩ connectedComponentIn (E0CBG.S0 M) p) : q = q' := by
  have hac := hS.isAcausal E0LM.e0_causallyArcConnected (E0LM.e0_curvesExtend hGH)
  obtain ⟨γ, -, -, hγi, hγr⟩ := (E0LM.e0_globalBTZ M).line p hp
  obtain ⟨a, rfl⟩ : q ∈ range γ := hγr ▸ hq.2
  obtain ⟨b, rfl⟩ : q' ∈ range γ := hγr ▸ hq'.2
  rcases le_total a b with h | h
  · exact hac _ hq.1 _ hq'.1 (hγi.1.le_of_le trivial trivial h)
  · exact (hac _ hq'.1 _ hq.1 (hγi.1.le_of_le trivial trivial h)).symm

/-- A finite family of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ > 0, ∀ i, ρ ≤ f i := by
  haveI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The head of a spear can be made to avoid a closed set missing its vertex.** -/
theorem SpearSurgeryDatum.exists_head_avoid {S : Set M} (D : SpearSurgeryDatum M S) {F : Set M}
    (hF : IsClosed F) (hpF : D.p ∉ F) :
    ∃ ρ > 0, ∀ x : E0, fcoord x = D.v → rad x ≤ ρ → D.ψ (paperInY x) ∉ F := by
  have hψc : ContinuousOn D.ψ D.W := fun y hy => (D.mor y hy).continuousWithinAt
  have hvW : paperInY (E0Spear.vertex D.v) ∈ D.W :=
    D.spear_sub ⟨_, E0Spear.vertex_mem_spear D.pos.le, rfl⟩
  have hc : ContinuousAt (fun x : E0 => D.ψ (paperInY x)) (E0Spear.vertex D.v) :=
    (hψc.continuousAt (D.isOpen.mem_nhds hvW)).comp E0Spear.continuous_paperInY.continuousAt
  have hmem : (fun x : E0 => D.ψ (paperInY x)) ⁻¹' Fᶜ ∈ 𝓝 (E0Spear.vertex D.v) :=
    hc.preimage_mem_nhds (hF.isOpen_compl.mem_nhds (by
      show D.ψ (E0Spear.yVertex D.v) ∈ Fᶜ; rw [D.vertex]; exact hpF))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨δ / 2, by positivity, fun x hfx hrx => hball ?_⟩
  have hr0 := rad_nonneg x
  have h1 : x.1 = D.v + rad x / 2 := by simp only [fcoord] at hfx; linarith
  rw [Metric.mem_ball, Prod.dist_eq]
  refine max_lt ?_ ?_
  · rw [Real.dist_eq, E0Spear.vertex, abs_lt]; constructor <;> simp only [h1] <;> linarith
  · rw [E0Spear.vertex, dist_zero_right]; exact lt_of_le_of_lt hrx (by linarith)

/-- **(G1) The surgery data exist** (B21 l.1091: « Since `M` is Cauchy-compact, it admits
finitely many BTZ-lines and one can take the spear neighborhoods `𝒮_Δ` disjoint »): one spear for
each of the finitely many points of `S ∩ sing₀(M)` (`finite_inter_S0`), of vertex on its BTZ line
in `I⁻(S)` and with that point on its ray (`exists_spearSurgeryDatum_cover`), each thinned
(`SpearSurgeryDatum.exists_shrink`) until its head avoids the other (closed,
`isClosed_image_spearY`) spears, which makes them pairwise disjoint (`disjoint_of_head`; distinct
points of `S` are on distinct BTZ lines, `eq_of_mem_component`). -/
theorem exists_surgeryData (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Nonempty (SurgeryData M S) := by
  set ι := ↥(S ∩ E0CBG.S0 M)
  haveI hfin : Finite ι := Set.finite_coe_iff.2 (finite_inter_S0 hGH hS hmax)
  have hD : ∀ q : ι, ∃ D : SpearSurgeryDatum M S,
      q.1 ∈ connectedComponentIn (E0CBG.S0 M) D.p ∧
        ∃ t, 0 < t ∧ q.1 = D.ψ (E0Spear.yAxis D.v t) := fun q =>
    exists_spearSurgeryDatum_cover hGH hS.cauchy hS.rimC1 hmax q.2.1 q.2.2
  choose D₀ hDc t ht hqt using hD
  -- distinct points are on distinct lines
  have hsep : ∀ i j : ι, ∀ a : M, a ∈ connectedComponentIn (E0CBG.S0 M) (D₀ i).p →
      a ∈ connectedComponentIn (E0CBG.S0 M) (D₀ j).p → i = j := by
    intro i j a hai haj
    have hij : connectedComponentIn (E0CBG.S0 M) (D₀ i).p =
        connectedComponentIn (E0CBG.S0 M) (D₀ j).p := by
      rw [connectedComponentIn_eq hai, connectedComponentIn_eq haj]
    have hjS : j.1 ∈ S ∩ connectedComponentIn (E0CBG.S0 M) (D₀ j).p := ⟨j.2.1, hDc j⟩
    have hiS : i.1 ∈ S ∩ connectedComponentIn (E0CBG.S0 M) (D₀ j).p := ⟨i.2.1, hij ▸ hDc i⟩
    exact Subtype.ext (eq_of_mem_component hGH hS.cauchy (D₀ j).p_mem hiS hjS)
  have hcl : ∀ i, IsClosed (D₀ i).spearSet := fun i =>
    isClosed_image_spearY hGH (D₀ i).isOpen (D₀ i).spear_sub (D₀ i).mor (D₀ i).inj
  have hvert : ∀ i j : ι, i ≠ j → (D₀ j).p ∉ (D₀ i).spearSet := fun i j hij hp =>
    hij (hsep i j _ ((D₀ i).spearSet_inter_S0_subset hp (D₀ j).p_mem)
      (mem_connectedComponentIn (D₀ j).p_mem))
  have hρ : ∀ i j : ι, ∃ ρ > 0, i ≠ j → ∀ x : E0, fcoord x = (D₀ j).v → rad x ≤ ρ →
      (D₀ j).ψ (paperInY x) ∉ (D₀ i).spearSet := by
    intro i j
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h => absurd hij h⟩
    · obtain ⟨ρ, hρ, h⟩ := (D₀ j).exists_head_avoid (hcl i) (hvert i j hij)
      exact ⟨ρ, hρ, fun _ => h⟩
  choose ρ hρpos hρ using hρ
  have hR : ∀ j : ι, ∃ R' > 0, R' ≤ (D₀ j).R ∧ ∀ i, R' ≤ ρ i j := by
    intro j
    obtain ⟨r, hr, hle⟩ := exists_pos_le_of_finite (fun i => ρ i j) fun i => hρpos i j
    exact ⟨min r (D₀ j).R, lt_min hr (D₀ j).pos, min_le_right _ _,
      fun i => (min_le_left _ _).trans (hle i)⟩
  choose R' hR'pos hR'le hR'ρ using hR
  have hshr : ∀ j : ι, ∃ D' : SpearSurgeryDatum M S, D'.p = (D₀ j).p ∧ D'.ψ = (D₀ j).ψ ∧
      D'.v = (D₀ j).v ∧ D'.R = R' j := fun j =>
    (D₀ j).exists_shrink hS.rimC1 (hR'pos j) (hR'le j)
  choose D hDp hDψ hDv hDR using hshr
  have hsub : ∀ j, (D j).spearSet ⊆ (D₀ j).spearSet := fun j => by
    show (D j).ψ '' E0Spear.spearY (D j).v (D j).R ⊆ _
    rw [hDψ, hDv, hDR]
    exact image_mono (image_mono (E0Spear.spear_mono le_rfl (hR'le j)))
  refine ⟨⟨ι, hfin, D, ?_, fun i => isClosed_image_spearY hGH (D i).isOpen (D i).spear_sub
    (D i).mor (D i).inj, ?_⟩⟩
  · intro i j hij
    refine SpearSurgeryDatum.disjoint_of_head hGH (D i) (D j) ?_ ?_
    · intro s hs hmem
      have h0 : (D i).ψ (E0Spear.yAxis (D i).v s) ∈ E0CBG.S0 M := (D i).ray.mem_S0 hs
      have hci := (D i).ray_mem_component hs
      have hcj := (D j).spearSet_inter_S0_subset hmem h0
      rw [hDp] at hci hcj
      exact hij (hsep i j _ hci hcj)
    · intro x hx hfx hmem
      have hfx' : fcoord x = (D₀ j).v := by rw [hfx, hDv]
      have hrx : rad x ≤ ρ i j := hx.2.trans ((hDR j).le.trans (hR'ρ j i))
      refine hρ i j hij x hfx' hrx ?_
      rw [← hDψ]
      exact hsub i hmem
  · intro y hy
    refine mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    have hq := hqt ⟨y, hy⟩
    show y ∈ (D ⟨y, hy⟩).ψ '' E0Spear.spearY (D ⟨y, hy⟩).v (D ⟨y, hy⟩).R
    rw [hDψ, hDv, hDR]
    exact ⟨_, E0Spear.yAxis_mem_spearY (hR'pos _).le (ht ⟨y, hy⟩).le, hq.symm⟩


/-! #### The causality of `Reg M` read in `M` (copies of `GX.BTZ.AbsMax` §5, which imports
this file: `ce_opens_eq`, `regChart_subtypeRestr_eq`, `flatCausality_e0RegM_eq`) -/

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- The charted causality of an open subset is the restriction (`AbsMax.ce_opens_eq`). -/
theorem surgery_ce_opens_eq (W : TopologicalSpace.Opens M) :
    E0CBG.CE W = ((E0CBG.CE M).restrict W).toSubtype := by
  have hval : Causal.IsEMorphism (E0CBG.CE W) (E0CBG.CE M) Subtype.val :=
    E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val W)
  have hloc := (Causal.isEMorphism_iff.1 hval).2
  have hmaps : ∀ V : TopologicalSpace.Opens W,
      MapsTo Subtype.val (V : Set W) (Causal.imageOpens V : Set M) :=
    fun V x hx => ⟨x, hx, rfl⟩
  have hA := Causal.CBG.chartedCausality_absolutelyMinimalOn (M := M) E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ
  apply Causal.Causality.ext_toPrecausality
  ext V x y
  · exact ⟨fun h => hval.map_le V (Causal.imageOpens V) le_top (hmaps V) h, fun h =>
      (Causal.Flat.LocalIso.rel_of_image hloc Subtype.val_injective hA V (Causal.imageOpens V) rfl
        x y).1 h⟩
  · exact ⟨fun h => hval.map_lt V (Causal.imageOpens V) le_top (hmaps V) h, fun h =>
      (Causal.Flat.LocalIso.rel_of_image hloc Subtype.val_injective hA V (Causal.imageOpens V) rfl
        x y).2 h⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem surgery_regChart_subtypeRestr_eq (y : E0LM.e0RegM M) :
    (E0LM.regChartM y).subtypeRestr ⟨y⟩ = (chartAt E0Y y).trans (E0LM.regAtlasChart y) := by
  rw [OpenPartialHomeomorph.subtypeRestr_def, E0LM.regChartM, ← OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.subtypeRestr_def]
  rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The flat causality of `Reg M` is its `𝔼₀` causality** (`AbsMax.flatCausality_e0RegM_eq`). -/
theorem surgery_flatCausality_e0RegM_eq :
    Causal.Flat.flatCausality 2 (E0LM.e0RegM M) = E0CBG.CE (E0LM.e0RegM M) := by
  have hmin : (E0CBG.CE (E0LM.e0RegM M)).AbsolutelyMinimal :=
    Causal.CBG.chartedCausality_absolutelyMinimal E0.absolutelyMinimalOn_YBTZ
  have hatlas : ∀ e ∈ atlas (Causal.Minkowski 2) (E0LM.e0RegM M),
      Causal.ChartIso (E0CBG.CE (E0LM.e0RegM M)) (Causal.minkowski 2) e := by
    rintro _ ⟨y, rfl⟩
    show Causal.ChartIso _ _ ((E0LM.regChartM y).subtypeRestr ⟨y⟩)
    rw [surgery_regChart_subtypeRestr_eq]
    exact E0.chartIso_trans
      (Causal.CBG.chartedCausality_chartIso E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ y)
      (E0.chartIso_e0Atlas (E0LM.regAtlasChart_mem y))
  exact (Causal.Flat.eq_flatCausality _ (fun e he =>
    Causal.chartIso_of_mem_maximalAtlas Causal.minkowski_causallyArcConnected
      Causal.Flat.isom_strongMorphism hatlas hmin he) hmin).symm

/-- `Reg M` is causally convex in `M` (BTZ points precede). -/
theorem causallyConvexIn_regM :
    (E0CBG.CE M).CausallyConvexIn (E0LM.e0RegM M : Set M) ⊤ := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  refine ⟨subset_univ _, fun p hp q _ z hz hzs => ?_⟩
  exact hp (hA.mem_sing_zero_of_le hzs (Causal.Causality.mem_diamond.1 hz).1)

/-- **The relation of `Reg M` is that of `M`.** -/
theorem regM_le_iff (x y : E0LM.e0RegM M) :
    (E0CBG.CE (E0LM.e0RegM M)).le ⊤ x y ↔ (E0CBG.CE M).le ⊤ (x : M) y := by
  rw [surgery_ce_opens_eq]
  show (E0CBG.CE M).le (Causal.imageOpens (⊤ : TopologicalSpace.Opens (E0LM.e0RegM M))) x y ↔ _
  rw [Causal.imageOpens_top]
  exact Causal.Causality.le_iff_of_causallyConvexIn E0LM.e0_causallyArcConnected
    causallyConvexIn_regM y.2 x.2

/-- **`Reg M` is globally hyperbolic** (as an `𝔼₀`-manifold; its diamonds are those of `M`). -/
theorem regM_globallyHyperbolic (hGH : (E0CBG.CE M).GloballyHyperbolic) :
    (E0CBG.CE (E0LM.e0RegM M)).GloballyHyperbolic := by
  refine ⟨fun x y hxy hyx => Subtype.ext (hGH.1 ((regM_le_iff x y).1 hxy)
    ((regM_le_iff y x).1 hyx)), fun p q => ?_⟩
  have heq : (E0CBG.CE (E0LM.e0RegM M)).diamond ⊤ p q =
      Subtype.val ⁻¹' (E0CBG.CE M).diamond ⊤ (p : M) q := by
    ext z
    rw [mem_preimage, Causal.Causality.mem_diamond, Causal.Causality.mem_diamond, regM_le_iff,
      regM_le_iff]
  rw [heq, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
  · exact hGH.2 p q
  · rw [Subtype.range_coe]
    exact (causallyConvexIn_regM (M := M)).2 (p : M) p.2 (q : M) q.2

/-- Every point of `Reg M` has a point strictly in its causal past (in `Reg M`). -/
theorem regM_Jminus_ne (hGH : (E0CBG.CE M).GloballyHyperbolic) (p : E0LM.e0RegM M) :
    (E0CBG.CE (E0LM.e0RegM M)).Jminus ⊤ {p} ≠ {p} := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  have hZ : (p : M) ∈ (E0CBG.CE M).Zminus := (hA.mem_Zminus_iff p).2 p.2
  obtain ⟨z, hzI, hzR⟩ := hZ _ ((E0LM.e0RegM M).isOpen.mem_nhds p.2)
  have hzp : (E0CBG.CE M).lt ⊤ z p := Causal.Precausality.mem_Iminus_singleton.1 hzI
  intro heq
  have hmem : (⟨z, hzR⟩ : E0LM.e0RegM M) ∈ (E0CBG.CE (E0LM.e0RegM M)).Jminus ⊤ {p} :=
    ⟨p, rfl, (regM_le_iff _ _).2 ((E0CBG.CE M).le_of_lt hzp)⟩
  rw [heq, mem_singleton_iff] at hmem
  have : z = p := congrArg Subtype.val hmem
  rw [this] at hzp
  exact E0Spear.not_lt_self hGH _ hzp

/-- Every point of `Reg M` has a point strictly in its causal future (in `Reg M`). -/
theorem regM_Jplus_ne (hGH : (E0CBG.CE M).GloballyHyperbolic) (p : E0LM.e0RegM M) :
    (E0CBG.CE (E0LM.e0RegM M)).Jplus ⊤ {p} ≠ {p} := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  obtain ⟨z, hzI, hzR⟩ := hA.mem_Zplus (p : M) _ ((E0LM.e0RegM M).isOpen.mem_nhds p.2)
  have hzp : (E0CBG.CE M).lt ⊤ p z := Causal.Precausality.mem_Iplus_singleton.1 hzI
  intro heq
  have hmem : (⟨z, hzR⟩ : E0LM.e0RegM M) ∈ (E0CBG.CE (E0LM.e0RegM M)).Jplus ⊤ {p} :=
    ⟨p, rfl, (regM_le_iff _ _).2 ((E0CBG.CE M).le_of_lt hzp)⟩
  rw [heq, mem_singleton_iff] at hmem
  have : z = p := congrArg Subtype.val hmem
  rw [this] at hzp
  exact E0Spear.not_lt_self hGH _ hzp

omit [ConnectedSpace M] [SecondCountableTopology M] in
/-- **A past-monotone curve eventually in a compact set converges at `-∞`** (the time reverse of
`E0Spear.exists_tendsto_of_monotone`). -/
theorem exists_tendsto_atBot_of_monotone (hGH : (E0CBG.CE M).GloballyHyperbolic)
    {γ : ℝ → M} {t₀ : ℝ} (hmono : ∀ s t, s ≤ t → t ≤ t₀ → (E0CBG.CE M).le ⊤ (γ s) (γ t))
    {K : Set M} (hK : IsCompact K) (hKγ : ∀ t, t ≤ t₀ → γ t ∈ K) :
    ∃ q, Tendsto γ atBot (𝓝 q) := by
  have hT := E0LM.e0_tarentin (M := M)
  have hev : ∀ᶠ t in atBot, γ t ∈ K := eventually_atBot.2 ⟨t₀, hKγ⟩
  obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atBot) (u := γ) (le_principal_iff.2 hev)
  have hbelow : ∀ q', MapClusterPt q' atBot γ → ∀ s, s ≤ t₀ → (E0CBG.CE M).le ⊤ q' (γ s) := by
    intro q' hq' s hs
    have := E0Spear.mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jminus_singleton hT (γ s)) hq'
      (eventually_atBot.2 ⟨s, fun t ht => by simpa using hmono t s ht hs⟩)
    simpa using this
  have huniq : ∀ q', MapClusterPt q' atBot γ → q' = q := by
    intro q' hq'
    have h1 : (E0CBG.CE M).le ⊤ q q' := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jplus_singleton hT q) hq'
        (eventually_atBot.2 ⟨t₀, fun t ht => by simpa using hbelow q hq t ht⟩)
      simpa using this
    have h2 : (E0CBG.CE M).le ⊤ q' q := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jplus_singleton hT q') hq
        (eventually_atBot.2 ⟨t₀, fun t ht => by simpa using hbelow q' hq' t ht⟩)
      simpa using this
    exact hGH.1 h2 h1
  exact ⟨q, hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx⟩


/-! #### Reading a causal curve of `M` in a spear chart -/

namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- The inverse of the spear chart. -/
noncomputable def ginv : M → E0Y := invFunOn D.ψ D.W

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem ginv_apply {y : E0Y} (hy : y ∈ D.W) : D.ginv (D.ψ y) = y :=
  D.inj.leftInvOn_invFunOn hy

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
theorem isOpen_image {V : Set E0Y} (hV : IsOpen V) (hVW : V ⊆ D.W) : IsOpen (D.ψ '' V) :=
  (E0Spear.isEMorphismOn_of_isE0Mor (W := ⟨D.W, D.isOpen⟩) D.mor).isOpen_image ⟨V, hV⟩ hVW

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem coord_apply {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) :
    D.coord (D.ψ (paperInY x)) = x := by
  have hinj : InjOn (fun x : E0 => D.ψ (paperInY x)) (E0Spear.spear D.v D.R) :=
    fun a ha b hb h => paperInY.injOn (by simp) (by simp)
      (D.inj (D.spear_sub ⟨a, ha, rfl⟩) (D.spear_sub ⟨b, hb, rfl⟩) h)
  exact hinj.leftInvOn_invFunOn hx

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem coord_eq_ginv {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) :
    D.coord (D.ψ (paperInY x)) = paperOfY (D.ginv (D.ψ (paperInY x))) := by
  rw [D.coord_apply hx, D.ginv_apply (D.spear_sub ⟨x, hx, rfl⟩), E0Spear.paperOfY_paperInY]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **A causal curve of `M` inside the chart image of an open `V ⊆ 𝔼₀` reads as a `≼`-increasing
curve of `𝔼₀`** (`IsEMorphismOn.causalCurveIn_invComp`, then `D` on the `𝔼₀` summand). -/
theorem le_of_causalCurve {V : Set E0} (hV : IsOpen V) (hVW : paperInY '' V ⊆ D.W)
    {J : Set ℝ} {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ J e)
    (heV : ∀ t ∈ J, e t ∈ D.ψ '' (paperInY '' V)) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J)
    (hst : s ≤ t) : Le (paperOfY (D.ginv (e s))) (paperOfY (D.ginv (e t))) := by
  set VY : TopologicalSpace.Opens E0Y := ⟨paperInY '' V, E0Spear.isOpen_paperInY_image hV⟩
  set U : TopologicalSpace.Opens M := ⟨D.ψ '' (paperInY '' V), D.isOpen_image
    (E0Spear.isOpen_paperInY_image hV) hVW⟩
  have hM := E0Spear.isEMorphismOn_of_isE0Mor (W := ⟨D.W, D.isOpen⟩) D.mor
  have heU : (E0CBG.CE M).CausalCurveIn U J e :=
    ⟨he.nonempty, he.ordConnected, fun a ha b hb =>
      ⟨fun t ht => heV t (he.ordConnected.out ha hb ht),
        fun t ht N _ htN => (he.curve a ha b hb).rel t ht N le_top htN⟩⟩
  have hg : LeftInvOn D.ginv D.ψ D.W := fun y hy => D.ginv_apply hy
  have hcY := hM.causalCurveIn_invComp hg (V := VY) hVW (U := U) rfl heU
  have hle := hcY.le_of_le hs ht hst
  obtain ⟨_, ⟨u, hu, rfl⟩, hus⟩ := heV s hs
  obtain ⟨_, ⟨w, hw, rfl⟩, hwt⟩ := heV t ht
  have hgs : D.ginv (e s) = paperInY u := by rw [← hus]; exact D.ginv_apply (hVW ⟨u, hu, rfl⟩)
  have hgt : D.ginv (e t) = paperInY w := by rw [← hwt]; exact D.ginv_apply (hVW ⟨w, hw, rfl⟩)
  simp only [Function.comp] at hle
  rw [hgs, hgt] at hle ⊢
  rw [E0Spear.paperOfY_paperInY, E0Spear.paperOfY_paperInY]
  have hD := (E0Spear.ceY_le_iff (⟨u, hu, rfl⟩ : paperInY u ∈ VY)
    (⟨w, hw, rfl⟩ : paperInY w ∈ VY)).1 hle
  set RI : TopologicalSpace.Opens E0Y := ⟨range Sum.inr, isOpen_range_inr⟩
  have hVR : VY ≤ RI := by
    rintro _ ⟨z, -, rfl⟩; exact ⟨_, (paperInY_apply z).symm⟩
  exact (E0.le_top_iff).1 ((E0Spear.D_le_rangeInr_iff u w).1 (E0LM.D.le_mono hVR hD))

end SpearSurgeryDatum

/-- In a connected component of `K ⊆ ℝ` with a greatest element `b`, points of `ℝ ∖ K` come
arbitrarily close after `b`. -/
theorem exists_notMem_of_isGreatest_component {K : Set ℝ} {s₀ b : ℝ}
    (hb : IsGreatest (connectedComponentIn K s₀) b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, b < t ∧ t < b + δ ∧ t ∉ K := by
  by_contra h
  push Not at h
  have hbK : b ∈ K := connectedComponentIn_subset _ _ hb.1
  have hsub : Icc b (b + δ / 2) ⊆ K := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h']; exact hbK
    · exact h t h' (by linarith [ht.2])
  have hmem := (isPreconnected_Icc.subset_connectedComponentIn
    (left_mem_Icc.2 (by linarith : b ≤ b + δ / 2)) hsub)
    (right_mem_Icc.2 (by linarith : b ≤ b + δ / 2))
  rw [← connectedComponentIn_eq hb.1] at hmem
  linarith [hb.2 hmem]

/-- In a connected component of `K ⊆ ℝ` with a least element `a`, points of `ℝ ∖ K` come
arbitrarily close before `a`. -/
theorem exists_notMem_of_isLeast_component {K : Set ℝ} {s₀ a : ℝ}
    (ha : IsLeast (connectedComponentIn K s₀) a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t, a - δ < t ∧ t < a ∧ t ∉ K := by
  by_contra h
  push Not at h
  have haK : a ∈ K := connectedComponentIn_subset _ _ ha.1
  have hsub : Icc (a - δ / 2) a ⊆ K := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; exact haK
    · exact h t (by linarith [ht.1]) h'
  have hmem := (isPreconnected_Icc.subset_connectedComponentIn
    (right_mem_Icc.2 (by linarith : a - δ / 2 ≤ a)) hsub)
    (left_mem_Icc.2 (by linarith : a - δ / 2 ≤ a))
  rw [← connectedComponentIn_eq ha.1] at hmem
  linarith [ha.2 hmem]

/-- A connected component of a closed `K ⊆ ℝ` with no least element is unbounded below. -/
theorem component_unbounded_below {K : Set ℝ} (hK : IsClosed K) {s₀ : ℝ}
    (hs₀ : s₀ ∈ K) (hno : ¬ ∃ a, IsLeast (connectedComponentIn K s₀) a) (T : ℝ) :
    ∃ s ∈ connectedComponentIn K s₀, s ≤ T := by
  set J := connectedComponentIn K s₀
  have hJ0 : s₀ ∈ J := mem_connectedComponentIn hs₀
  have hJoc : J.OrdConnected := isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
  by_contra hcon
  push Not at hcon
  have hbdd : BddBelow J := ⟨T, fun s hs => (hcon s hs).le⟩
  set a := sInf J
  have haJ : a ∉ J := fun h => hno ⟨a, h, fun s hs => csInf_le hbdd hs⟩
  have has₀ : a ≤ s₀ := csInf_le hbdd hJ0
  have haK : a ∈ K := hK.closure_subset_iff.2 (connectedComponentIn_subset K s₀)
    (csInf_mem_closure ⟨s₀, hJ0⟩ hbdd)
  have hsub : Icc a s₀ ⊆ K := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h']; exact haK
    · obtain ⟨j, hj, hjt⟩ := exists_lt_of_csInf_lt ⟨s₀, hJ0⟩ h'
      exact connectedComponentIn_subset _ _ (hJoc.out hj hJ0 ⟨hjt.le, ht.2⟩)
  exact haJ ((isPreconnected_Icc.subset_connectedComponentIn (right_mem_Icc.2 has₀) hsub)
    (left_mem_Icc.2 has₀))

/-- A connected component of a closed `K ⊆ ℝ` with no greatest element is unbounded above. -/
theorem component_unbounded_above {K : Set ℝ} (hK : IsClosed K) {s₀ : ℝ}
    (hs₀ : s₀ ∈ K) (hno : ¬ ∃ b, IsGreatest (connectedComponentIn K s₀) b) (T : ℝ) :
    ∃ s ∈ connectedComponentIn K s₀, T ≤ s := by
  set J := connectedComponentIn K s₀
  have hJ0 : s₀ ∈ J := mem_connectedComponentIn hs₀
  have hJoc : J.OrdConnected := isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove J := ⟨T, fun s hs => (hcon s hs).le⟩
  set b := sSup J
  have hbJ : b ∉ J := fun h => hno ⟨b, h, fun s hs => le_csSup hbdd hs⟩
  have hs₀b : s₀ ≤ b := le_csSup hbdd hJ0
  have hbK : b ∈ K := hK.closure_subset_iff.2 (connectedComponentIn_subset K s₀)
    (csSup_mem_closure ⟨s₀, hJ0⟩ hbdd)
  have hsub : Icc s₀ b ⊆ K := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; exact hbK
    · obtain ⟨j, hj, hjt⟩ := exists_lt_of_lt_csSup ⟨s₀, hJ0⟩ h'
      exact connectedComponentIn_subset _ _ (hJoc.out hJ0 hj ⟨ht.1, hjt.le⟩)
  exact hbJ ((isPreconnected_Icc.subset_connectedComponentIn (left_mem_Icc.2 hs₀b) hsub)
    (right_mem_Icc.2 hs₀b))


namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem coord_mem {y : M} (hy : y ∈ D.spearSet) :
    D.coord y ∈ E0Spear.spear D.v D.R ∧ D.ψ (paperInY (D.coord y)) = y := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
  rw [D.coord_apply hx]; exact ⟨hx, rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem rad_coord_pos {y : M} (hy : y ∈ D.spearSet) (hyR : y ∉ E0CBG.S0 M) :
    0 < rad (D.coord y) := by
  obtain ⟨hx, hxy⟩ := D.coord_mem hy
  refine lt_of_le_of_ne (rad_nonneg _) fun h => hyR ?_
  rw [← hxy]; exact (D.mem_S0_iff hx).2 h.symm

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- `≼` along a causal curve of `M` inside a spear, in the spear's coordinates. -/
theorem le_coord_of_curve {J : Set ℝ} {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ J e)
    (heS : ∀ t ∈ J, e t ∈ D.spearSet) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) :
    Le (D.coord (e s)) (D.coord (e t)) := by
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  have hV : ∀ t ∈ J, e t ∈ D.ψ '' (paperInY '' (paperInY ⁻¹' D.W)) := fun t ht => by
    obtain ⟨hx, hxe⟩ := D.coord_mem (heS t ht)
    exact ⟨_, ⟨_, D.spear_sub ⟨_, hx, rfl⟩, rfl⟩, hxe⟩
  have h := D.le_of_causalCurve hPo (image_preimage_subset _ _) he hV hs ht hst
  obtain ⟨hxs, hxes⟩ := D.coord_mem (heS s hs)
  obtain ⟨hxt, hxet⟩ := D.coord_mem (heS t ht)
  rwa [← hxes, ← hxet, ← D.coord_eq_ginv hxs, ← D.coord_eq_ginv hxt, hxes, hxet] at h

end SpearSurgeryDatum

/-- The `Reg M` facts the limit arguments need, packaged. -/
theorem regM_facts (hGH : (E0CBG.CE M).GloballyHyperbolic) :
    (∀ x, IsClosed ((E0CBG.CE (E0LM.e0RegM M)).Jminus ⊤ {x})) ∧
      (∀ x, IsClosed ((E0CBG.CE (E0LM.e0RegM M)).Jplus ⊤ {x})) ∧
      (E0CBG.CE (E0LM.e0RegM M)).StronglyCausal ∧
      (E0CBG.CE (E0LM.e0RegM M)).CausallyArcConnected ∧
      (E0CBG.CE (E0LM.e0RegM M)).IsCausal := by
  have hG := regM_globallyHyperbolic hGH
  have hT := E0LM.e0_tarentin (M := E0LM.e0RegM M)
  exact ⟨hG.isClosed_Jminus_singleton hT, hG.isClosed_Jplus_singleton hT, hG.stronglyCausal hT,
    E0LM.e0_causallyArcConnected, hG.1⟩

namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- **The past end of a spear arc** (Remark 2.12, for curves over `ℝ`): the component through `s₀`
of the trace on a spear of an inextensible causal curve of `Reg M` either has a first point — on
the head, below the cusp — or approaches the axis. -/
theorem pastEnd (hGH : (E0CBG.CE M).GloballyHyperbolic) {d : ℝ → E0LM.e0RegM M}
    (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d) {s₀ : ℝ}
    (hs₀ : (d s₀ : M) ∈ D.spearSet) :
    (∃ t ∈ connectedComponentIn {s | (d s : M) ∈ D.spearSet} s₀,
        height D.G (D.coord (d t)) < 0) ∨
      ∀ ε > 0, ∃ t ∈ connectedComponentIn {s | (d s : M) ∈ D.spearSet} s₀,
        rad (D.coord (d t)) < ε := by
  set K : Set ℝ := {s | (d s : M) ∈ D.spearSet} with hK
  set J := connectedComponentIn K s₀ with hJ
  set e : ℝ → M := fun s => (d s : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  have hec : Continuous e := he.continuous
  have hKcl : IsClosed K :=
    (isClosed_image_spearY hGH D.isOpen D.spear_sub D.mor D.inj).preimage hec
  have hJK : J ⊆ K := connectedComponentIn_subset _ _
  have hJ0 : s₀ ∈ J := mem_connectedComponentIn hs₀
  have hJoc : J.OrdConnected :=
    isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
  have heJ : (E0CBG.CE M).CausalCurveIn ⊤ J e :=
    ⟨⟨s₀, hJ0⟩, hJoc, fun a _ b _ => he.curve a trivial b trivial⟩
  have hmono : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → Le (D.coord (e s)) (D.coord (e t)) :=
    fun s hs t ht hst => D.le_coord_of_curve heJ (fun u hu => hJK hu) hs ht hst
  by_cases hmin : ∃ a, IsLeast J a
  · obtain ⟨a, ha⟩ := hmin
    left
    obtain ⟨hxa, hxae⟩ : D.coord (e a) ∈ E0Spear.spear D.v D.R ∧
        D.ψ (paperInY (D.coord (e a))) = e a := D.coord_mem (hJK ha.1)
    have hra : 0 < rad (D.coord (e a)) := D.rad_coord_pos (hJK ha.1) (d a).2
    have hf : fcoord (D.coord (e a)) ≤ D.v := by
      by_contra hlt
      push Not at hlt
      set N₀ : Set E0 := paperInY ⁻¹' D.W ∩ {u | D.v < fcoord u} with hN₀
      have hN₀o : IsOpen N₀ := (D.isOpen.preimage E0Spear.continuous_paperInY).inter
        (isOpen_lt continuous_const continuous_fcoord)
      have hN₀W : paperInY '' N₀ ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
      have hU₀o : IsOpen (D.ψ '' (paperInY '' N₀)) :=
        D.isOpen_image (E0Spear.isOpen_paperInY_image hN₀o) hN₀W
      have heaU : e a ∈ D.ψ '' (paperInY '' N₀) :=
        ⟨_, ⟨_, ⟨D.spear_sub ⟨_, hxa, rfl⟩, hlt⟩, rfl⟩, hxae⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
        (hec.continuousAt.preimage_mem_nhds (hU₀o.mem_nhds heaU))
      obtain ⟨t, hta, hta', htK⟩ := exists_notMem_of_isLeast_component ha hδ
      have hIcc : (E0CBG.CE M).CausalCurveIn ⊤ (Icc t a) e :=
        ⟨⟨t, left_mem_Icc.2 hta'.le⟩, ordConnected_Icc, fun a' _ b' _ => he.curve a' trivial b' trivial⟩
      have hU : ∀ s ∈ Icc t a, e s ∈ D.ψ '' (paperInY '' N₀) := fun s hs => hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
      have hle := D.le_of_causalCurve hN₀o hN₀W hIcc hU (left_mem_Icc.2 hta'.le)
        (right_mem_Icc.2 hta'.le) hta'.le
      obtain ⟨_, ⟨u, hu, rfl⟩, hut⟩ := hU t (left_mem_Icc.2 hta'.le)
      rw [← hut, ← hxae, D.ginv_apply (hN₀W ⟨u, hu, rfl⟩),
        D.ginv_apply (D.spear_sub ⟨_, hxa, rfl⟩), E0Spear.paperOfY_paperInY,
        E0Spear.paperOfY_paperInY] at hle
      have huS : u ∈ E0Spear.spear D.v D.R := ⟨hu.2.le, hle.closed.2.1.trans hxa.2⟩
      exact htK (show e t ∈ D.spearSet by rw [← hut]; exact ⟨_, ⟨u, huS, rfl⟩, rfl⟩)
    refine ⟨a, ha.1, ?_⟩
    have h1 : (D.coord (e a)).1 = fcoord (D.coord (e a)) + rad (D.coord (e a)) / 2 := by
      simp only [fcoord]; ring
    have h2 := D.above (rad (D.coord (e a)), Complex.arg (D.coord (e a)).2) hra hxa.2
    simp only [height, heightAt]
    linarith [hxa.2]
  · right
    intro ε hε
    by_contra hcon
    push Not at hcon
    obtain ⟨hJm, -, hSC, hC, hcaus⟩ := regM_facts hGH
    set x₀ := D.coord (e s₀)
    have hIic : ∀ t, t ≤ s₀ → t ∈ J := fun t ht => by
      obtain ⟨s, hs, hst⟩ := component_unbounded_below hKcl hs₀ hmin t
      exact hJoc.out hs hJ0 ⟨hst, ht⟩
    set A : Set E0 := Icc D.v x₀.1 ×ˢ Metric.closedBall (0 : ℂ) D.R ∩
      ({x | D.v ≤ fcoord x} ∩ {x | ε ≤ rad x}) with hA
    have hAc : IsCompact A := (isCompact_Icc.prod (isCompact_closedBall _ _)).inter_right
      ((isClosed_le continuous_const continuous_fcoord).inter
        (isClosed_le continuous_const continuous_rad))
    have hAsp : A ⊆ E0Spear.spear D.v D.R := fun x hx =>
      ⟨hx.2.1, by have := hx.1.2; rwa [Metric.mem_closedBall, dist_zero_right] at this⟩
    have hψc : ContinuousOn D.ψ D.W := fun y hy => (D.mor y hy).continuousWithinAt
    have hΦc : ContinuousOn (fun x : E0 => D.ψ (paperInY x)) A := fun x hx =>
      ((hψc.continuousAt (D.isOpen.mem_nhds (D.spear_sub ⟨x, hAsp hx, rfl⟩))).comp
        E0Spear.continuous_paperInY.continuousAt).continuousWithinAt
    have hKc : IsCompact ((fun x : E0 => D.ψ (paperInY x)) '' A) := hAc.image_of_continuousOn hΦc
    have hin : ∀ t, t ≤ s₀ → e t ∈ (fun x : E0 => D.ψ (paperInY x)) '' A := fun t ht => by
      obtain ⟨hx, hxe⟩ := D.coord_mem (hJK (hIic t ht))
      have hle := hmono t (hIic t ht) s₀ hJ0 ht
      refine ⟨_, ⟨⟨⟨?_, hle.closed.1⟩, ?_⟩, hx.1, hcon t (hIic t ht)⟩, hxe⟩
      · have := hx.1; simp only [fcoord] at this; linarith [rad_nonneg (D.coord (e t))]
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
    obtain ⟨q, hq⟩ := exists_tendsto_atBot_of_monotone hGH (t₀ := s₀)
      (fun s t hst _ => he.le_of_le trivial trivial hst) hKc hin
    have hqK : q ∈ (fun x : E0 => D.ψ (paperInY x)) '' A :=
      hKc.isClosed.mem_of_tendsto hq (eventually_atBot.2 ⟨s₀, hin⟩)
    obtain ⟨x, hxA, rfl⟩ := hqK
    have hqR : D.ψ (paperInY x) ∉ E0CBG.S0 M := fun h => by
      have h0 := (D.mem_S0_iff (hAsp hxA)).1 h
      have h3 : ε ≤ rad x := hxA.2.2
      linarith
    exact Causal.Causality.Inextensible.not_tendsto_atBot hJm hSC hC hcaus
      (regM_Jminus_ne hGH) hd ⟨_, hqR⟩ (tendsto_subtype_rng.2 hq)

end SpearSurgeryDatum


namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- **The future end of a spear arc** (Remark 2.12, for curves over `ℝ`): the component through
`s₀` of the trace on a spear of an inextensible causal curve of `Reg M` either climbs to
`τ = +∞` or has a last point, on the shaft. -/
theorem futureEnd (hGH : (E0CBG.CE M).GloballyHyperbolic) {d : ℝ → E0LM.e0RegM M}
    (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d) {s₀ : ℝ}
    (hs₀ : (d s₀ : M) ∈ D.spearSet) :
    (∀ T : ℝ, ∃ t ∈ connectedComponentIn {s | (d s : M) ∈ D.spearSet} s₀,
        T ≤ (D.coord (d t)).1) ∨
      ∃ b ∈ connectedComponentIn {s | (d s : M) ∈ D.spearSet} s₀,
        (∀ t ∈ connectedComponentIn {s | (d s : M) ∈ D.spearSet} s₀, t ≤ b) ∧
          rad (D.coord (d b)) = D.R := by
  set K : Set ℝ := {s | (d s : M) ∈ D.spearSet} with hK
  set J := connectedComponentIn K s₀ with hJ
  set e : ℝ → M := fun s => (d s : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  have hec : Continuous e := he.continuous
  have hKcl : IsClosed K :=
    (isClosed_image_spearY hGH D.isOpen D.spear_sub D.mor D.inj).preimage hec
  have hJK : J ⊆ K := connectedComponentIn_subset _ _
  have hJ0 : s₀ ∈ J := mem_connectedComponentIn hs₀
  have hJoc : J.OrdConnected :=
    isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
  have heJ : (E0CBG.CE M).CausalCurveIn ⊤ J e :=
    ⟨⟨s₀, hJ0⟩, hJoc, fun a _ b _ => he.curve a trivial b trivial⟩
  have hmono : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → Le (D.coord (e s)) (D.coord (e t)) :=
    fun s hs t ht hst => D.le_coord_of_curve heJ (fun u hu => hJK hu) hs ht hst
  by_cases hmax : ∃ b, IsGreatest J b
  · obtain ⟨b, hb⟩ := hmax
    right
    obtain ⟨hxb, hxbe⟩ : D.coord (e b) ∈ E0Spear.spear D.v D.R ∧
        D.ψ (paperInY (D.coord (e b))) = e b := D.coord_mem (hJK hb.1)
    refine ⟨b, hb.1, hb.2, le_antisymm hxb.2 ?_⟩
    by_contra hlt
    push Not at hlt
    set N₁ : Set E0 := paperInY ⁻¹' D.W ∩ {u | rad u < D.R} with hN₁
    have hN₁o : IsOpen N₁ := (D.isOpen.preimage E0Spear.continuous_paperInY).inter
      (isOpen_lt continuous_rad continuous_const)
    have hN₁W : paperInY '' N₁ ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    have hU₁o : IsOpen (D.ψ '' (paperInY '' N₁)) :=
      D.isOpen_image (E0Spear.isOpen_paperInY_image hN₁o) hN₁W
    have hebU : e b ∈ D.ψ '' (paperInY '' N₁) :=
      ⟨_, ⟨_, ⟨D.spear_sub ⟨_, hxb, rfl⟩, hlt⟩, rfl⟩, hxbe⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
      (hec.continuousAt.preimage_mem_nhds (hU₁o.mem_nhds hebU))
    obtain ⟨t, hbt, hbt', htK⟩ := exists_notMem_of_isGreatest_component hb hδ
    have hIcc : (E0CBG.CE M).CausalCurveIn ⊤ (Icc b t) e :=
      ⟨⟨b, left_mem_Icc.2 hbt.le⟩, ordConnected_Icc, fun a' _ b' _ => he.curve a' trivial b' trivial⟩
    have hU : ∀ s ∈ Icc b t, e s ∈ D.ψ '' (paperInY '' N₁) := fun s hs => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
    have hle := D.le_of_causalCurve hN₁o hN₁W hIcc hU (left_mem_Icc.2 hbt.le)
      (right_mem_Icc.2 hbt.le) hbt.le
    obtain ⟨_, ⟨u, hu, rfl⟩, hut⟩ := hU t (right_mem_Icc.2 hbt.le)
    rw [← hut, ← hxbe, D.ginv_apply (hN₁W ⟨u, hu, rfl⟩),
      D.ginv_apply (D.spear_sub ⟨_, hxb, rfl⟩), E0Spear.paperOfY_paperInY,
      E0Spear.paperOfY_paperInY] at hle
    have hf := (E0.calculus_le ((E0.le_top_iff).2 hle)).2.2.2.2.1
    have huS : u ∈ E0Spear.spear D.v D.R := ⟨hxb.1.trans hf, hu.2.le⟩
    exact htK (show e t ∈ D.spearSet by rw [← hut]; exact ⟨_, ⟨u, huS, rfl⟩, rfl⟩)
  · left
    intro T₀
    by_contra hcon
    push Not at hcon
    obtain ⟨-, hJp, hSC, hC, hcaus⟩ := regM_facts hGH
    set x₀ := D.coord (e s₀)
    have hr₀ : 0 < rad x₀ := D.rad_coord_pos (hJK hJ0) (d s₀).2
    have hIci : ∀ t, s₀ ≤ t → t ∈ J := fun t ht => by
      obtain ⟨s, hs, hst⟩ := component_unbounded_above hKcl hs₀ hmax t
      exact hJoc.out hJ0 hs ⟨ht, hst⟩
    set A : Set E0 := Icc D.v T₀ ×ˢ Metric.closedBall (0 : ℂ) D.R ∩
      ({x | D.v ≤ fcoord x} ∩ {x | rad x₀ ≤ rad x}) with hA
    have hAc : IsCompact A := (isCompact_Icc.prod (isCompact_closedBall _ _)).inter_right
      ((isClosed_le continuous_const continuous_fcoord).inter
        (isClosed_le continuous_const continuous_rad))
    have hAsp : A ⊆ E0Spear.spear D.v D.R := fun x hx =>
      ⟨hx.2.1, by have := hx.1.2; rwa [Metric.mem_closedBall, dist_zero_right] at this⟩
    have hψc : ContinuousOn D.ψ D.W := fun y hy => (D.mor y hy).continuousWithinAt
    have hΦc : ContinuousOn (fun x : E0 => D.ψ (paperInY x)) A := fun x hx =>
      ((hψc.continuousAt (D.isOpen.mem_nhds (D.spear_sub ⟨x, hAsp hx, rfl⟩))).comp
        E0Spear.continuous_paperInY.continuousAt).continuousWithinAt
    have hKc : IsCompact ((fun x : E0 => D.ψ (paperInY x)) '' A) := hAc.image_of_continuousOn hΦc
    have hin : ∀ t, s₀ ≤ t → e t ∈ (fun x : E0 => D.ψ (paperInY x)) '' A := fun t ht => by
      obtain ⟨hx, hxe⟩ := D.coord_mem (hJK (hIci t ht))
      have hle := hmono s₀ hJ0 t (hIci t ht) ht
      refine ⟨_, ⟨⟨⟨?_, (hcon t (hIci t ht)).le⟩, ?_⟩, hx.1, hle.closed.2.1⟩, hxe⟩
      · have := hx.1; simp only [fcoord] at this; linarith [rad_nonneg (D.coord (e t))]
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
    obtain ⟨q, hq⟩ := E0Spear.exists_tendsto_of_monotone hGH (t₀ := s₀)
      (fun s t _ hst => he.le_of_le trivial trivial hst) hKc hin
    have hqK : q ∈ (fun x : E0 => D.ψ (paperInY x)) '' A :=
      hKc.isClosed.mem_of_tendsto hq (eventually_atTop.2 ⟨s₀, hin⟩)
    obtain ⟨x, hxA, rfl⟩ := hqK
    have hqR : D.ψ (paperInY x) ∉ E0CBG.S0 M := fun h => by
      have h0 := (D.mem_S0_iff (hAsp hxA)).1 h
      have h3 : rad x₀ ≤ rad x := hxA.2.2
      linarith
    exact Causal.Causality.Inextensible.not_tendsto_atTop hJp hSC hC hcaus
      (regM_Jplus_ne hGH) hd ⟨_, hqR⟩ (tendsto_subtype_rng.2 hq)

end SpearSurgeryDatum


namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- **Remark 2.12 for one spear** (`rem:curve_spear`, B21 l.913–915): the connected component
through `t₀` of the trace on a spear of an inextensible causal curve of `Reg M` is, in the spear's
coordinates, a spear arc — continuous and `≼`-increasing in `0 < r ≤ R`, with its past end on the
head (below the cusp) or at the axis, its future end at `τ = +∞` or on the shaft. The ends are read
on a reparametrisation over `ℝ` (`Inextensible.reparam`), where a bounded end would be a limit in
`Reg M` (`exists_tendsto_of_monotone` in a compact part of the spear), against
`Inextensible.not_tendsto_atBot`/`atTop`. -/
theorem isSpearArc_of_inextensible (hGH : (E0CBG.CE M).GloballyHyperbolic) {I : Set ℝ}
    {c : ℝ → E0LM.e0RegM M} (hc : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ I c) {t₀ : ℝ}
    (ht₀ : t₀ ∈ I) (hin : (c t₀ : M) ∈ D.spearSet) :
    D.IsSpearArc (fun t => D.coord (c t))
      (connectedComponentIn {t ∈ I | (c t : M) ∈ D.spearSet} t₀) := by
  set K : Set ℝ := {t ∈ I | (c t : M) ∈ D.spearSet} with hK
  set J := connectedComponentIn K t₀ with hJ
  set e : ℝ → M := fun t => (c t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ I e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hc.1
  have hJK : J ⊆ K := connectedComponentIn_subset _ _
  have hJ0 : t₀ ∈ J := mem_connectedComponentIn ⟨ht₀, hin⟩
  have hJoc : J.OrdConnected :=
    isPreconnected_iff_ordConnected.1 isPreconnected_connectedComponentIn
  have heJ : (E0CBG.CE M).CausalCurveIn ⊤ J e :=
    ⟨⟨t₀, hJ0⟩, hJoc, fun a ha b hb => he.curve a (hJK ha).1 b (hJK hb).1⟩
  have hcont : ContinuousOn (fun t => D.coord (e t)) J := by
    have hgmor : E0Spear.IsE0Mor D.ginv (D.ψ '' D.W) :=
      Causal.CBG.liftPropOn_invFunOn D.isOpen D.mor D.inj
    have hgc : ContinuousOn D.ginv (D.ψ '' D.W) := fun y hy => (hgmor y hy).continuousWithinAt
    have hVo : IsOpen (D.ψ '' D.W) := D.isOpen_image D.isOpen subset_rfl
    have hec := E0Spear.continuousOn_of_causalCurveIn heJ
    refine ContinuousOn.congr (f := fun t => paperOfY (D.ginv (e t))) (fun t ht => ?_)
      (fun t ht => ?_)
    · obtain ⟨hx, hxe⟩ : D.coord (e t) ∈ E0Spear.spear D.v D.R ∧
          D.ψ (paperInY (D.coord (e t))) = e t := D.coord_mem (hJK ht).2
      have hW : e t ∈ D.ψ '' D.W := ⟨_, D.spear_sub ⟨_, hx, rfl⟩, hxe⟩
      have hgt : D.ginv (e t) = paperInY (D.coord (e t)) := by
        rw [← hxe, D.ginv_apply (D.spear_sub ⟨_, hx, rfl⟩), hxe]
      have hpo : ContinuousAt paperOfY (D.ginv (e t)) := by
        refine paperOfY.continuousAt ?_
        rw [paperOfY_source, hgt, paperInY_apply]; exact mem_range_self _
      exact (hpo.comp (hgc.continuousAt (hVo.mem_nhds hW))).comp_continuousWithinAt (hec t ht)
    · obtain ⟨hx, hxe⟩ : D.coord (e t) ∈ E0Spear.spear D.v D.R ∧
          D.ψ (paperInY (D.coord (e t))) = e t := D.coord_mem (hJK ht).2
      show D.coord (e t) = paperOfY (D.ginv (e t))
      rw [← hxe]; exact D.coord_eq_ginv hx
  refine ⟨hJoc, hcont, fun s hs t ht hst => D.le_coord_of_curve heJ (fun u hu => (hJK hu).2) hs
    ht hst, fun s hs => ⟨D.rad_coord_pos (hJK hs).2 (c s).2, (D.coord_mem (hJK hs).2).1.2⟩, ?_⟩
  -- the ends, on a reparametrisation over `ℝ`
  obtain ⟨hJm, hJp, hSC, hC, hcaus⟩ := regM_facts hGH
  obtain ⟨φ, hφ, hφc, hφr, hd⟩ := hc.reparam hC hcaus (regM_Jminus_ne hGH) (regM_Jplus_ne hGH)
  obtain ⟨s₀, hs₀⟩ : t₀ ∈ range φ := hφr ▸ ht₀
  have hds₀ : (((c ∘ φ) s₀ : E0LM.e0RegM M) : M) ∈ D.spearSet := by
    simp only [Function.comp, hs₀]; exact hin
  set Jd := connectedComponentIn {s | (((c ∘ φ) s : E0LM.e0RegM M) : M) ∈ D.spearSet} s₀
  have hJeq : φ '' Jd = J := by
    apply Subset.antisymm
    · refine (isPreconnected_connectedComponentIn.image φ hφc.continuousOn).subset_connectedComponentIn
        ⟨s₀, mem_connectedComponentIn hds₀, hs₀⟩ ?_
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s ∈ {s | (((c ∘ φ) s : E0LM.e0RegM M) : M) ∈ D.spearSet} :=
        connectedComponentIn_subset _ _ hs
      exact ⟨hφr ▸ mem_range_self s, hs'⟩
    · intro t ht
      obtain ⟨s, rfl⟩ : t ∈ range φ := hφr ▸ (hJK ht).1
      have hpre : IsPreconnected (φ ⁻¹' J) := by
        refine isPreconnected_iff_ordConnected.2 ⟨fun a ha b hb x hx => ?_⟩
        exact hJoc.out ha hb ⟨hφ.monotone hx.1, hφ.monotone hx.2⟩
      have hsub := hpre.subset_connectedComponentIn (x := s₀)
        (show φ s₀ ∈ J by rw [hs₀]; exact hJ0) (fun u hu => (hJK hu).2)
      exact ⟨s, hsub ht, rfl⟩
  have hmemJ : ∀ s ∈ Jd, φ s ∈ J := fun s hs => hJeq ▸ mem_image_of_mem φ hs
  refine ⟨?_, ?_⟩
  · rcases D.pastEnd hGH hd hds₀ with ⟨s, hs, hneg⟩ | hax
    · exact Or.inl ⟨φ s, hmemJ s hs, hneg⟩
    · exact Or.inr fun ε hε => by
        obtain ⟨s, hs, hr⟩ := hax ε hε
        exact ⟨φ s, hmemJ s hs, hr⟩
  · rcases D.futureEnd hGH hd hds₀ with hup | ⟨b, hb, hbmax, hbR⟩
    · exact Or.inl fun T => by
        obtain ⟨s, hs, hT⟩ := hup T
        exact ⟨φ s, hmemJ s hs, hT⟩
    · refine Or.inr ⟨φ b, hmemJ b hb, fun t ht => ?_, hbR⟩
      rw [← hJeq] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact hφ.monotone (hbmax s hs)

end SpearSurgeryDatum

end GlobalPieces

/-! ### §5f (G4a) — the cusps are spacelike Lipschitz in the flat charts of `Reg M` (WP-46e)

The cone-increasing criterion (`Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet`) read at one
point and in a frame (`isSpacelikeLipschitzAt_of_coneZeroSet`); a `C¹` function whose derivative is
positive on the future causal cone is cone-increasing on a ball (`exists_ball_isConeIncreasingOn`);
the height above a graph `τ = G(r, θ)` read in null coordinates (`nullHeight`) has, at a spacelike
point, derivative positive on the closed future cone (Lemma 2.7, `fderiv_nullHeight_pos`); the flat
chart of `Reg M` read in a spear chart is `g •` a sector chart (`SpearSurgeryDatum.eventually_regChart`);
and the null-shift height of a Lipschitz graph along the developed `∂_τ` (`exists_nullShift`) glues
the cusp to `S` across the rim. -/

section ConeCriterion

variable {d : ℕ}

/-- A functional positive on the nonzero future causal vectors of `𝐌ⁿ`: its spatial part has
norm `<` its value on `(1, 0)`. -/
theorem norm_comp_inr_lt_of_pos {ℓ : Causal.Minkowski d →L[ℝ] ℝ}
    (hpos : ∀ v : Causal.Minkowski d, v ≠ 0 → Causal.Flat.IsFutureCausal v → 0 < ℓ v) :
    ‖ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))‖ < ℓ ((1 : ℝ), 0) := by
  set B := ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))) with hBdef
  set b := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm B with hbdef
  have hB : ∀ u, B u = inner ℝ b u := fun u => (InnerProductSpace.toDual_symm_apply).symm
  have hnorm : ‖B‖ = ‖b‖ := by
    rw [hbdef, LinearIsometryEquiv.norm_map]
  rw [hnorm]
  have h10 : ℓ ((1 : ℝ), 0) > 0 := hpos _ (by simp) ⟨by norm_num, by simp [Causal.Flat.minkQ]⟩
  by_cases hb : b = 0
  · rw [hb, norm_zero]; exact h10
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
    have hv : ((‖b‖, -b) : Causal.Minkowski d) ≠ 0 := fun h => by
      have := congrArg Prod.fst h; simp at this; exact hb this
    have hfc : Causal.Flat.IsFutureCausal ((‖b‖, -b) : Causal.Minkowski d) :=
      ⟨norm_nonneg _, by simp [Causal.Flat.minkQ]⟩
    have h := hpos _ hv hfc
    have hsplit : ℓ ((‖b‖, -b) : Causal.Minkowski d) = ‖b‖ * ℓ ((1 : ℝ), 0) + B (-b) := by
      have : ((‖b‖, -b) : Causal.Minkowski d) = ‖b‖ • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) +
          (0, -b) := by ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    rw [hsplit, hB, inner_neg_right, real_inner_self_eq_norm_sq] at h
    nlinarith

/-- `ℓ v ≥ ℓ(1,0) v.1 − ‖ℓ ∘ inr‖ ‖v.2‖`. -/
theorem apply_ge_of_split (ℓ : Causal.Minkowski d →L[ℝ] ℝ) (v : Causal.Minkowski d) :
    ℓ ((1 : ℝ), 0) * v.1 -
      ‖ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))‖ * ‖v.2‖ ≤ ℓ v := by
  have hsplit : ℓ v = v.1 * ℓ ((1 : ℝ), 0) +
      (ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))) v.2 := by
    have : v = v.1 • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) + (0, v.2) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, smul_eq_mul]
    rfl
  have h := (ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))).le_opNorm v.2
  have h' := neg_abs_le ((ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d)))) v.2)
  rw [Real.norm_eq_abs] at h
  rw [hsplit]; nlinarith

/-- **The derivative criterion for cone-increase**: a `C¹` function whose derivative at `p₀` is
positive on the nonzero future causal vectors is, on a ball around `p₀`, `c`-cone-increasing for
some `c < 1` (mean value theorem on segments). -/
theorem exists_ball_isConeIncreasingOn {f : Causal.Minkowski d → ℝ} {U : Set (Causal.Minkowski d)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {p₀ : Causal.Minkowski d} (hp₀ : p₀ ∈ U)
    (hpos : ∀ v : Causal.Minkowski d, v ≠ 0 → Causal.Flat.IsFutureCausal v →
      0 < fderiv ℝ f p₀ v) :
    ∃ ε > 0, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ Metric.ball p₀ ε ⊆ U ∧
      Causal.Flat.Cla.IsConeIncreasingOn c f (Metric.ball p₀ ε) := by
  set ι := ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d))
  set A : Causal.Minkowski d → ℝ := fun p => fderiv ℝ f p ((1 : ℝ), 0)
  set Bn : Causal.Minkowski d → ℝ := fun p => ‖(fderiv ℝ f p).comp ι‖
  have hlt := norm_comp_inr_lt_of_pos hpos
  have hA0 : 0 < A p₀ := (norm_nonneg _).trans_lt hlt
  set c : ℝ := (Bn p₀ + A p₀) / (2 * A p₀) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by rw [hcdef, div_lt_one (by positivity)]; linarith
  have hfd : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hfdc : ContinuousAt (fderiv ℝ f) p₀ := hfd.continuousAt (hU.mem_nhds hp₀)
  have hAc : ContinuousAt A p₀ :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin d)))).continuous.continuousAt.comp hfdc
  have hBc : ContinuousAt Bn p₀ :=
    continuous_norm.continuousAt.comp
      ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) (Causal.Minkowski d) ℝ).flip ι
        |>.continuous.continuousAt.comp hfdc)
  have hstrict : Bn p₀ < c * A p₀ := by
    rw [hcdef, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have hev : ∀ᶠ p in 𝓝 p₀, Bn p < c * A p ∧ p ∈ U := by
    refine (((hBc.sub (hAc.const_mul c)).eventually (gt_mem_nhds (by linarith : Bn p₀ - c * A p₀ < 0)))).and
      (hU.mem_nhds hp₀) |>.mono fun p hp => ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ε, hε, c, hc0, hc1, fun p hp => (hball p hp).2, ?_⟩
  intro a ha b hb hab
  -- the segment `a + s (b − a)`
  set φ : ℝ → ℝ := fun s => f (a + s • (b - a))
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, a + s • (b - a) ∈ Metric.ball p₀ ε := fun s hs => by
    have hconv := (convex_ball p₀ ε)
    have := hconv.add_smul_sub_mem ha hb hs
    exact this
  have hdiff : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (fderiv ℝ f (a + s • (b - a)) (b - a)) s := by
    intro s hs
    have hpU : a + s • (b - a) ∈ U := (hball _ (hseg s hs)).2
    have hfa : HasFDerivAt f (fderiv ℝ f (a + s • (b - a))) (a + s • (b - a)) :=
      ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hpU)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) s := by
      simpa using ((hasDerivAt_id s).smul_const (b - a)).const_add a
    exact hfa.comp_hasDerivAt s hl
  have hderpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < fderiv ℝ f (a + s • (b - a)) (b - a) := by
    intro s hs
    obtain ⟨hB, -⟩ := hball _ (hseg s hs)
    set p := a + s • (b - a)
    have hge := apply_ge_of_split (fderiv ℝ f p) (b - a)
    have hAp : 0 < A p := by
      have : 0 ≤ Bn p := norm_nonneg _
      by_contra h; push Not at h
      nlinarith
    show 0 < fderiv ℝ f p (b - a)
    have h1 : Bn p * ‖(b - a).2‖ ≤ c * A p * ‖(b - a).2‖ :=
      mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)
    have h2 : c * ‖b.2 - a.2‖ < (b - a).1 := by simpa using hab
    have h3 : A p * (c * ‖(b - a).2‖) < A p * (b - a).1 := by
      apply mul_lt_mul_of_pos_left _ hAp; simpa using h2
    simp only [A, Bn] at hge h1 h3
    linarith
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ _ (by norm_num : (0 : ℝ) < 1) hcont
    (fun s hs => hdiff s (Ioo_subset_Icc_self hs))
  have hpos' := hderpos ξ (Ioo_subset_Icc_self hξ)
  rw [hξeq] at hpos'
  simp only [φ, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero, div_one] at hpos'
  linarith

/-! #### The null-shift height of a Lipschitz graph -/

section NullShift

variable {u : EuclideanSpace ℝ (Fin d) → ℝ} {U' : Set (EuclideanSpace ℝ (Fin d))} {c₁ : NNReal}
  {m : Causal.Minkowski d}

/-- Two shifts of `q` along `m` landing on the `c₁`-Lipschitz graph (`c₁ < 1`, `m` future causal
with `m.1 > 0`) agree. -/
theorem nullShift_unique (hc₁ : c₁ < 1) (hu : LipschitzOnWith c₁ u U') (hm : 0 < m.1)
    (hmn : ‖m.2‖ ≤ m.1) {q : Causal.Minkowski d} {s s' : ℝ}
    (hs : (q - s • m).2 ∈ U') (hsu : (q - s • m).1 = u (q - s • m).2)
    (hs' : (q - s' • m).2 ∈ U') (hsu' : (q - s' • m).1 = u (q - s' • m).2) : s = s' := by
  have hL := hu.dist_le_mul _ hs _ hs'
  rw [← hsu, ← hsu', Real.dist_eq, dist_eq_norm] at hL
  simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.smul_snd] at hL
  have h1 : q.1 - s * m.1 - (q.1 - s' * m.1) = (s' - s) * m.1 := by ring
  have h2 : q.2 - s • m.2 - (q.2 - s' • m.2) = (s' - s) • m.2 := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]
  rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hm] at hL
  have hc : (c₁ : ℝ) < 1 := hc₁
  by_contra hne
  have hpos : 0 < |s' - s| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have : (c₁ : ℝ) * (|s' - s| * ‖m.2‖) ≤ (c₁ : ℝ) * (|s' - s| * m.1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmn hpos.le) c₁.2
  have h3 : (c₁ : ℝ) * (|s' - s| * m.1) < |s' - s| * m.1 := by
    have := mul_pos hpos hm
    nlinarith
  linarith

/-- **The null-shift height is `c₁`-cone-increasing** on any set where it lands on the graph. -/
theorem isConeIncreasingOn_nullShift (hc₁ : c₁ < 1) (hu : LipschitzOnWith c₁ u U')
    (hm : 0 < m.1) (hmn : ‖m.2‖ ≤ m.1) {σ : Causal.Minkowski d → ℝ} {A : Set (Causal.Minkowski d)}
    (hσ : ∀ q ∈ A, (q - σ q • m).2 ∈ U' ∧ (q - σ q • m).1 = u (q - σ q • m).2) :
    Causal.Flat.Cla.IsConeIncreasingOn c₁ σ A := by
  intro a ha b hb hab
  by_contra hle
  push Not at hle
  obtain ⟨ha1, ha2⟩ := hσ a ha
  obtain ⟨hb1, hb2⟩ := hσ b hb
  have hL := hu.dist_le_mul _ hb1 _ ha1
  rw [← ha2, ← hb2, Real.dist_eq, dist_eq_norm] at hL
  simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.smul_snd] at hL
  set k := σ a - σ b with hk
  have hk0 : 0 ≤ k := by rw [hk]; linarith
  have h1 : b.1 - σ b * m.1 - (a.1 - σ a * m.1) = (b.1 - a.1) + k * m.1 := by rw [hk]; ring
  have h2 : b.2 - σ b • m.2 - (a.2 - σ a • m.2) = (b.2 - a.2) + k • m.2 := by
    rw [hk, sub_smul]; abel
  rw [h1, h2] at hL
  have hn : ‖(b.2 - a.2) + k • m.2‖ ≤ ‖b.2 - a.2‖ + k * m.1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hmn hk0) _
  have hc : (c₁ : ℝ) < 1 := hc₁
  have hc0 : (0 : ℝ) ≤ c₁ := c₁.2
  have h3 : (c₁ : ℝ) * ‖(b.2 - a.2) + k • m.2‖ ≤ c₁ * ‖b.2 - a.2‖ + c₁ * (k * m.1) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hn hc0
  have h4 : (c₁ : ℝ) * (k * m.1) ≤ k * m.1 := by
    have := mul_nonneg hk0 hm.le
    nlinarith
  have hpos : 0 < (b.1 - a.1) + k * m.1 := by
    have := mul_nonneg hk0 hm.le
    have : 0 ≤ (c₁ : ℝ) * ‖b.2 - a.2‖ := mul_nonneg hc0 (norm_nonneg _)
    linarith
  rw [abs_of_pos hpos] at hL
  linarith

/-- **The null-shift height is Lipschitz** on any set where it lands on the graph. -/
theorem continuousOn_nullShift (hc₁ : c₁ < 1) (hu : LipschitzOnWith c₁ u U')
    (hm : 0 < m.1) (hmn : ‖m.2‖ ≤ m.1) {σ : Causal.Minkowski d → ℝ} {A : Set (Causal.Minkowski d)}
    (hσ : ∀ q ∈ A, (q - σ q • m).2 ∈ U' ∧ (q - σ q • m).1 = u (q - σ q • m).2) :
    ContinuousOn σ A := by
  have hc : (c₁ : ℝ) < 1 := hc₁
  have hc0 : (0 : ℝ) ≤ c₁ := c₁.2
  have hK : 0 < (1 - c₁) * m.1 := mul_pos (by linarith) hm
  have hest : ∀ a ∈ A, ∀ b ∈ A, |σ b - σ a| * ((1 - c₁) * m.1) ≤ 2 * ‖b - a‖ := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := hσ a ha
    obtain ⟨hb1, hb2⟩ := hσ b hb
    have hL := hu.dist_le_mul _ hb1 _ ha1
    rw [← ha2, ← hb2, Real.dist_eq, dist_eq_norm] at hL
    simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.smul_snd] at hL
    set k := σ a - σ b
    have h1 : b.1 - σ b * m.1 - (a.1 - σ a * m.1) = (b.1 - a.1) + k * m.1 := by ring
    have h2 : b.2 - σ b • m.2 - (a.2 - σ a • m.2) = (b.2 - a.2) + k • m.2 := by
      simp only [k, sub_smul]; abel
    rw [h1, h2] at hL
    have hn : ‖(b.2 - a.2) + k • m.2‖ ≤ ‖b.2 - a.2‖ + |k| * m.1 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hmn (abs_nonneg _)) _
    have hb1' : |b.1 - a.1| ≤ ‖b - a‖ := by
      have := norm_fst_le (b - a); rwa [Real.norm_eq_abs] at this
    have hb2' : ‖b.2 - a.2‖ ≤ ‖b - a‖ := norm_snd_le (b - a)
    have hkm : |k| * m.1 ≤ |b.1 - a.1| + |(b.1 - a.1) + k * m.1| := by
      have : |k * m.1| = |k| * m.1 := by rw [abs_mul, abs_of_pos hm]
      rw [← this]
      have := abs_sub_abs_le_abs_sub ((b.1 - a.1) + k * m.1) (b.1 - a.1)
      calc |k * m.1| = |((b.1 - a.1) + k * m.1) - (b.1 - a.1)| := by ring_nf
        _ ≤ |(b.1 - a.1) + k * m.1| + |b.1 - a.1| := abs_sub _ _
        _ = _ := by ring
    have hk : |σ b - σ a| = |k| := by simp only [k]; rw [abs_sub_comm]
    rw [hk]
    have h3 : (c₁ : ℝ) * ‖(b.2 - a.2) + k • m.2‖ ≤ c₁ * ‖b.2 - a.2‖ + c₁ * (|k| * m.1) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hn hc0
    have h4 : (c₁ : ℝ) * ‖b.2 - a.2‖ ≤ ‖b - a‖ := by
      have := mul_le_mul_of_nonneg_left hb2' hc0
      nlinarith [norm_nonneg (b - a)]
    nlinarith
  intro a ha
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε * ((1 - c₁) * m.1) / 2, by positivity, fun b hb hab => ?_⟩
  have h := hest a ha b hb
  rw [Real.dist_eq]
  rw [dist_eq_norm] at hab
  by_contra hcon
  push Not at hcon
  have : ε * ((1 - c₁) * m.1) ≤ |σ b - σ a| * ((1 - c₁) * m.1) :=
    mul_le_mul_of_nonneg_right hcon hK.le
  linarith

open Classical in
/-- **The null-shift height of a Lipschitz graph exists near a point of the graph**: for a
`c₁`-Lipschitz `u` (`c₁ < 1`) on an open `U'`, a point `q₀` of its graph and `m` with
`0 < m.1`, `‖m.2‖ ≤ m.1`, near `q₀` every `q` has a shift `q − σ(q) m` on the graph (intermediate
value theorem on `[−T, T]`), and `σ(q₀) = 0`. -/
theorem exists_nullShift (hU' : IsOpen U') (hc₁ : c₁ < 1) (hu : LipschitzOnWith c₁ u U')
    (hm : 0 < m.1) (hmn : ‖m.2‖ ≤ m.1) {q₀ : Causal.Minkowski d} (hq₀ : q₀.2 ∈ U')
    (hq₀u : q₀.1 = u q₀.2) :
    ∃ δ > 0, ∃ σ : Causal.Minkowski d → ℝ, σ q₀ = 0 ∧ ∀ q ∈ Metric.ball q₀ δ, q.2 ∈ U' ∧
      (q - σ q • m).2 ∈ U' ∧ (q - σ q • m).1 = u (q - σ q • m).2 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU' q₀.2 hq₀
  have hc : (c₁ : ℝ) < 1 := hc₁
  have hc0 : (0 : ℝ) ≤ c₁ := c₁.2
  set T := ρ / (2 * m.1) with hT
  have hT0 : 0 < T := by positivity
  have hTm : T * m.1 = ρ / 2 := by rw [hT]; field_simp
  set δ := min (ρ / 2) (ρ * (1 - c₁) / 4) with hδ
  have h1c : 0 < 1 - (c₁ : ℝ) := by linarith
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ρ / 2 := min_le_left _ _
  have hδ2 : δ ≤ ρ * (1 - c₁) / 4 := min_le_right _ _
  set P : Causal.Minkowski d → ℝ → Prop := fun q s =>
    (q - s • m).2 ∈ U' ∧ (q - s • m).1 = u (q - s • m).2
  have hex : ∀ q ∈ Metric.ball q₀ δ, ∃ s, P q s := by
    intro q hq
    have hq1 : |q.1 - q₀.1| < δ := by
      have := (Prod.dist_eq (x := q) (y := q₀) ▸ Metric.mem_ball.1 hq : max (dist q.1 q₀.1) (dist q.2 q₀.2) < δ)
      rw [← Real.dist_eq]; exact (le_max_left _ _).trans_lt this
    have hq2 : dist q.2 q₀.2 < δ := by
      have := (Prod.dist_eq (x := q) (y := q₀) ▸ Metric.mem_ball.1 hq : max (dist q.1 q₀.1) (dist q.2 q₀.2) < δ)
      exact (le_max_right _ _).trans_lt this
    have hin : ∀ s ∈ Icc (-T) T, q.2 - s • m.2 ∈ Metric.ball q₀.2 ρ := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : q.2 - s • m.2 - q₀.2 = (q.2 - q₀.2) - s • m.2 := by abel
      rw [h1]
      refine (norm_sub_le _ _).trans_lt ?_
      rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
      have : |s| * ‖m.2‖ ≤ T * m.1 := mul_le_mul (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) hmn
        (norm_nonneg _) hT0.le
      linarith
    set φ : ℝ → ℝ := fun s => (q - s • m).1 - u (q - s • m).2
    have hφc : ContinuousOn φ (Icc (-T) T) := by
      refine (continuousOn_const.sub (continuousOn_id.mul continuousOn_const)).sub ?_
      refine hu.continuousOn.comp (continuousOn_const.sub (continuousOn_id.smul continuousOn_const))
        fun s hs => hball (hin s hs)
    have hu0 : ∀ z ∈ Metric.ball q₀.2 ρ, u z ≤ q₀.1 + c₁ * dist z q₀.2 ∧
        q₀.1 - c₁ * dist z q₀.2 ≤ u z := by
      intro z hz
      have := hu.dist_le_mul z (hball hz) q₀.2 hq₀
      rw [Real.dist_eq, ← hq₀u] at this
      exact ⟨by linarith [le_abs_self (u z - q₀.1)], by linarith [neg_abs_le (u z - q₀.1)]⟩
    have hdist : ∀ s ∈ Icc (-T) T, dist (q.2 - s • m.2) q₀.2 ≤ δ + T * m.1 := by
      intro s hs
      rw [dist_eq_norm]
      have h1 : q.2 - s • m.2 - q₀.2 = (q.2 - q₀.2) - s • m.2 := by abel
      rw [h1]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
      have : |s| * ‖m.2‖ ≤ T * m.1 := mul_le_mul (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) hmn
        (norm_nonneg _) hT0.le
      linarith
    have hmT : -T ∈ Icc (-T) T := ⟨le_rfl, by linarith⟩
    have hpT : T ∈ Icc (-T) T := ⟨by linarith, le_rfl⟩
    have hlo : 0 ≤ φ (-T) := by
      have h := (hu0 _ (hin _ hmT)).1
      have hd := hdist _ hmT
      simp only [φ, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.smul_snd]
      have : (c₁ : ℝ) * dist (q.2 - -T • m.2) q₀.2 ≤ c₁ * (δ + T * m.1) :=
        mul_le_mul_of_nonneg_left hd hc0
      have hab := abs_lt.1 hq1
      nlinarith
    have hhi : φ T ≤ 0 := by
      have h := (hu0 _ (hin _ hpT)).2
      have hd := hdist _ hpT
      simp only [φ, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, Prod.smul_snd]
      have : (c₁ : ℝ) * dist (q.2 - T • m.2) q₀.2 ≤ c₁ * (δ + T * m.1) :=
        mul_le_mul_of_nonneg_left hd hc0
      have hab := abs_lt.1 hq1
      nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (by linarith : -T ≤ T) hφc ⟨hhi, hlo⟩
    refine ⟨s, hball (hin s hs), ?_⟩
    have : φ s = 0 := hs0
    simp only [φ] at this
    linarith
  set σ : Causal.Minkowski d → ℝ := fun q => if h : ∃ s, P q s then Classical.choose h else 0
  have hσP : ∀ q ∈ Metric.ball q₀ δ, P q (σ q) := by
    intro q hq
    have h := hex q hq
    simp only [σ, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨δ, hδ0, σ, ?_, fun q hq => ⟨?_, hσP q hq⟩⟩
  · have h0 : P q₀ 0 := by simp only [P, zero_smul, sub_zero]; exact ⟨hq₀, hq₀u⟩
    obtain ⟨h1, h2⟩ := hσP q₀ (Metric.mem_ball_self hδ0)
    exact nullShift_unique hc₁ hu hm hmn h1 h2 h0.1 h0.2
  · refine hball ?_
    rw [Metric.mem_ball]
    have := (Prod.dist_eq (x := q) (y := q₀) ▸ Metric.mem_ball.1 hq : max (dist q.1 q₀.1) (dist q.2 q₀.2) < δ)
    exact ((le_max_right _ _).trans_lt this).trans_le (hδ1.trans (by linarith))

end NullShift

end ConeCriterion

section ConeLocal

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (Causal.Minkowski 2) X]

open scoped Pointwise in
/-- **The cone-increasing criterion at one point, in a frame** (`exists_isSpacelikeLipschitzIn_zeroSet`
read in the frame `g`, then moved back by `IsSpacelikeLipschitzIn.smul`): if near `chartAt x x`
the chart picture of `T` is the zero set of a continuous `f` which, read in the frame `g`, is
`c`-cone-increasing for some `c < 1`, then `T` is spacelike Lipschitz at `x`. -/
theorem isSpacelikeLipschitzAt_of_coneZeroSet {T : Set X} {x : X} (g : Causal.Flat.isom 2)
    {W : Set (Causal.Minkowski 2)} (hW : IsOpen W) (hxW : chartAt (Causal.Minkowski 2) x x ∈ W)
    (hWt : W ⊆ (chartAt (Causal.Minkowski 2) x).target) {f : Causal.Minkowski 2 → ℝ}
    (hfc : ContinuousOn f W) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinc : Causal.Flat.Cla.IsConeIncreasingOn c (fun p => f (g⁻¹ • p)) (g • W))
    (hiff : ∀ p ∈ W, (p ∈ chartAt (Causal.Minkowski 2) x '' (T ∩ (chartAt (Causal.Minkowski 2) x).source)
      ↔ f p = 0))
    (hx : x ∈ T) : IsSpacelikeLipschitzAt T x := by
  set e := chartAt (Causal.Minkowski 2) x
  have hW' : IsOpen (g • W) := by
    rw [← Set.image_smul]; exact (Causal.Flat.isom.toHomeomorph g).isOpenMap W hW
  have hFc : ContinuousOn (fun p => f (g⁻¹ • p)) (g • W) := by
    refine hfc.comp (continuous_const_smul _).continuousOn fun p hp => ?_
    exact (Set.mem_smul_set_iff_inv_smul_mem).1 hp
  have hgx : g • e x ∈ g • W := Set.smul_mem_smul_set hxW
  have hf0 : f (e x) = 0 := (hiff _ hxW).1 ⟨x, ⟨hx, mem_chart_source _ x⟩, rfl⟩
  obtain ⟨V', hpV', hV'W, hV'⟩ := Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet hW' hFc hc0
    hc1 hinc hgx (by simp [hf0])
  have hV := hV'.smul Causal.Flat.isom_strongMorphism g⁻¹
  have hmemV : ∀ p, p ∈ (Causal.smulOpens g⁻¹ V' : Set (Causal.Minkowski 2)) ↔ g • p ∈ V' := by
    intro p
    rw [Causal.Flat.coe_smulOpens, Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    rfl
  have hVW : ∀ p, p ∈ (Causal.smulOpens g⁻¹ V' : Set (Causal.Minkowski 2)) → p ∈ W := by
    intro p hp
    have := hV'W ((hmemV p).1 hp)
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_smul_smul] at this
    exact this
  refine ⟨Causal.smulOpens g⁻¹ V', (hmemV _).2 hpV', fun p hp => hWt (hVW p hp), ?_⟩
  convert hV using 1
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  simp only [mem_inter_iff, mem_setOf_eq, inv_smul_smul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hmemV p).1 h2, (hiff p (hVW p h2)).1 h1⟩
  · rintro ⟨h1, h2⟩
    have hp : p ∈ (Causal.smulOpens g⁻¹ V' : Set (Causal.Minkowski 2)) := (hmemV p).2 h1
    exact ⟨(hiff p (hVW p hp)).2 h2, hp⟩

open scoped Pointwise in
/-- `isSpacelikeLipschitzAt_of_coneZeroSet` with every datum read in the frame `g`. -/
theorem isSpacelikeLipschitzAt_of_coneZeroSet' {T : Set X} {x : X} (g : Causal.Flat.isom 2)
    {W' : Set (Causal.Minkowski 2)} (hW' : IsOpen W')
    (hxW' : g • chartAt (Causal.Minkowski 2) x x ∈ W')
    (hWt : ∀ q ∈ W', g⁻¹ • q ∈ (chartAt (Causal.Minkowski 2) x).target) {F : Causal.Minkowski 2 → ℝ}
    (hFc : ContinuousOn F W') {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hinc : Causal.Flat.Cla.IsConeIncreasingOn c F W')
    (hiff : ∀ q ∈ W', (g⁻¹ • q ∈ chartAt (Causal.Minkowski 2) x ''
      (T ∩ (chartAt (Causal.Minkowski 2) x).source) ↔ F q = 0))
    (hx : x ∈ T) : IsSpacelikeLipschitzAt T x := by
  have hmem : ∀ p, p ∈ g⁻¹ • W' ↔ g • p ∈ W' := fun p => by
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  have hgW : g • (g⁻¹ • W') = W' := smul_inv_smul g W'
  refine isSpacelikeLipschitzAt_of_coneZeroSet g (W := g⁻¹ • W') (f := fun p => F (g • p)) ?_
    ((hmem _).2 hxW') (fun p hp => by
      have := hWt _ ((hmem p).1 hp); rwa [inv_smul_smul] at this) ?_ hc0 hc1 ?_ ?_ hx
  · rw [← Set.image_smul]; exact (Causal.Flat.isom.toHomeomorph g⁻¹).isOpenMap W' hW'
  · exact hFc.comp (continuous_const_smul _).continuousOn fun p hp => (hmem p).1 hp
  · rw [hgW]; simpa only [smul_inv_smul] using hinc
  · intro p hp
    have := hiff _ ((hmem p).1 hp)
    rwa [inv_smul_smul] at this

end ConeLocal

section NullHeight

/-- **The height above the graph of `G`, read in null coordinates** (the development's
coordinates `(a, b, c) = btzPaperNull (τ, r, θ)`, `b = r`, `θ = −c/b`). -/
noncomputable def nullHeight (G : ℝ × ℝ → ℝ) (Q : ℝ × ℝ × ℝ) : ℝ := height G (unlift Q)

/-- The explicit form of `nullHeight` on `b > 0`. -/
noncomputable def nullHeightExpl (G : ℝ × ℝ → ℝ) (Q : ℝ × ℝ × ℝ) : ℝ :=
  (Q.1 - Q.2.2 ^ 2 / Q.2.1 + Q.2.1) / 2 - G (Q.2.1, -(Q.2.2 / Q.2.1))

theorem nullHeight_eq {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    {Q : ℝ × ℝ × ℝ} (hQ : 0 < Q.2.1) : nullHeight G Q = nullHeightExpl G Q := by
  have hrad := rad_unlift hQ.le
  rw [nullHeight, ← heightAt_eq_height hG (polar_unlift hQ.le) (by rw [hrad]; exact hQ),
    heightAt, hrad]
  rfl

theorem isOpen_nullPos : IsOpen {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
  isOpen_lt continuous_const (continuous_fst.comp continuous_snd)

theorem contDiffOn_nullHeightExpl {G : ℝ × ℝ → ℝ} (hG : ContDiffOn ℝ 1 G {q | 0 < q.1}) :
    ContDiffOn ℝ 1 (nullHeightExpl G) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} := by
  have hb : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.2.1) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hc : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.2.2) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have ha : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.1) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
    contDiff_fst.contDiffOn
  have hne : ∀ Q ∈ {Q : ℝ × ℝ × ℝ | 0 < Q.2.1}, Q.2.1 ≠ 0 := fun Q hQ => ne_of_gt hQ
  have hθ : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
    (hc.div hb hne).neg
  have hpair : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => ((Q.2.1, -(Q.2.2 / Q.2.1)) : ℝ × ℝ))
      {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} := hb.prodMk hθ
  have hGc : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => G (Q.2.1, -(Q.2.2 / Q.2.1)))
      {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} := hG.comp hpair fun Q hQ => hQ
  exact ((((ha.sub ((hc.pow 2).div hb hne)).add hb).div_const 2).sub hGc)

theorem contDiffOn_nullHeight {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    (hGs : ContDiffOn ℝ 1 G {q | 0 < q.1}) :
    ContDiffOn ℝ 1 (nullHeight G) {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
  (contDiffOn_nullHeightExpl hGs).congr fun _ hQ => nullHeight_eq hG hQ

/-- The algebra of Lemma 2.7 in the causal cone: on a spacelike graph (`δ > 0`), the covector
`dτ − dτ_Σ` is positive on every nonzero future causal vector `w` (`w_r ≥ 0`, `ds²(w) ≤ 0`; for
`w_r = w_θ = 0`, `w_τ > 0`). The decomposition `w = λ ∂_τ + u`, `u` tangent to the graph:
`ds²(w) = graphQuad(u) − 2λ w_r`. -/
theorem covector_pos {gr gθ r : ℝ} (hr : 0 < r) (hδ : 0 < spacelikeDelta gr gθ r)
    {wτ wr wθ : ℝ} (hwr : 0 ≤ wr) (hQ : -2 * wτ * wr + wr ^ 2 + r ^ 2 * wθ ^ 2 ≤ 0)
    (h0 : wr = 0 → wθ = 0 → 0 < wτ) : 0 < wτ - (wr * gr + wθ * gθ) := by
  rcases hwr.eq_or_lt with h | h
  · subst h
    have hθ : wθ = 0 := by
      have : r ^ 2 * wθ ^ 2 ≤ 0 := by linarith
      have h2 : 0 < r ^ 2 := by positivity
      have : wθ ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
    have := h0 rfl hθ
    subst hθ; simpa using this
  · have hq := (graphQuad_pos_iff hr).2 hδ wr wθ (fun h' => by
      have := congrArg Prod.fst h'; simp at this; linarith)
    have hid : -2 * wτ * wr + wr ^ 2 + r ^ 2 * wθ ^ 2 =
        graphQuad gr gθ r wr wθ - 2 * wr * (wτ - (wr * gr + wθ * gθ)) := by
      unfold graphQuad; ring
    rw [hid] at hQ
    nlinarith

/-- **Lemma 2.7, the derivative form in null coordinates**: at a point `p = (τ, r, θ)`, `r > 0`,
of a spacelike graph `τ = G(r, θ)`, the derivative of the height `nullHeight G` at
`btzPaperNull p` is positive on every nonzero vector of the closed future cone `NullCone`. -/
theorem fderiv_nullHeight_pos {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    {p : ℝ × ℝ × ℝ} (hr : 0 < p.2.1) {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt G L (p.2.1, p.2.2))
    (hδ : 0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.2.1)
    (hd : DifferentiableAt ℝ (nullHeight G) (btzPaperNull p)) {V : ℝ × ℝ × ℝ}
    (hV : NullCone V) (hV0 : V ≠ 0) : 0 < fderiv ℝ (nullHeight G) (btzPaperNull p) V := by
  obtain ⟨L', hL', hL'h⟩ := hasFDerivAt_btzPaperNull p
  set h : ℝ × ℝ × ℝ → ℝ := fun q => q.1 - G (q.2.1, q.2.2)
  have hh : HasFDerivAt h ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
      L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_fst.sub (hL.comp p hasFDerivAt_snd)
  have hev : (nullHeight G ∘ btzPaperNull) =ᶠ[𝓝 p] h := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hr]
      with q hq
    have hq' : 0 < (btzPaperNull q).2.1 := hq
    rw [comp_apply, nullHeight_eq hG hq']
    simp only [nullHeightExpl, h, btzPaperNull]
    have hq0 : q.2.1 ≠ 0 := ne_of_gt hq
    congr 1
    · field_simp; ring
    · congr 2; field_simp
  have hcomp := hd.hasFDerivAt.comp p hL'
  have heq := (hcomp.congr_of_eventuallyEq hev.symm).unique hh
  -- the preimage `w` of `V` under `dD`
  set r := p.2.1
  set θ := p.2.2
  set wr := V.2.1
  set wθ := -(V.2.2 + V.2.1 * θ) / r
  set wτ := (V.1 - V.2.1 * θ ^ 2 - 2 * r * θ * wθ + V.2.1) / 2
  have hw : L' (wτ, wr, wθ) = V := by
    rw [hL'h]
    have hr0 : r ≠ 0 := ne_of_gt hr
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [wτ, wθ, wr]; field_simp; ring
    · simp only [wθ, wr]; field_simp; ring
  have hval : fderiv ℝ (nullHeight G) (btzPaperNull p) V = wτ - (wr * L (1, 0) + wθ * L (0, 1)) := by
    have := congrArg (fun T : ℝ × ℝ × ℝ →L[ℝ] ℝ => T (wτ, wr, wθ)) heq
    simp only [ContinuousLinearMap.comp_apply, hw] at this
    rw [this, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', clm_apply_pair]
  rw [hval]
  obtain ⟨ha, hb, hc⟩ := hV
  refine covector_pos hr hδ hb ?_ ?_
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hid : -2 * wτ * wr + wr ^ 2 + r ^ 2 * wθ ^ 2 = V.2.2 ^ 2 - V.1 * V.2.1 := by
      simp only [wτ, wθ, wr]; field_simp; ring
    rw [hid]; linarith
  · intro h1 h2
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hb0 : V.2.1 = 0 := h1
    have hc0 : V.2.2 = 0 := by
      have : -(V.2.2 + V.2.1 * θ) / r = 0 := h2
      rw [hb0] at this; field_simp at this; linarith
    have ha0 : V.1 ≠ 0 := fun ha0 => hV0 (Prod.ext ha0 (Prod.ext hb0 hc0))
    have : wτ = V.1 / 2 := by simp only [wτ, wθ, hb0, hc0]; ring
    rw [this]; exact half_pos (lt_of_le_of_ne ha (Ne.symm ha0))

end NullHeight

section ChartRead

open TopologicalSpace
attribute [local instance] btzE0Structure

/-- Near a point of its source in the sector of `y₀`, a chart of `BTZE0`'s maximal a.e. atlas is
`g •` the sector chart `chartMap y₀` (a copy of `GX.BTZ.Uniformization`'s
`aeChart_eventually_chartMap_sector`, which imports this file). -/
theorem surgery_aeChart_eventually_chartMap
    {c : OpenPartialHomeomorph BTZE0 (Causal.Minkowski 2)}
    (hc : c ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) {x : BTZE0}
    (hx : x ∈ c.source) {y₀ : E0} (hy₀ : y₀.2 ≠ 0) (hxs : E0.toPaper x ∈ E0.sector y₀) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ z in 𝓝 x,
      c z = g • E0.chartMap y₀ (E0.toPaper z) := by
  set y := E0.toPaper x
  have hyax : y ∉ E0.axis := E0.not_mem_axis_of_mem_sector hxs
  set p : ℝ × ℝ × ℝ := (y.1, E0.rad y, E0.angle y₀ y)
  have hpx : orbitMk (GammaA (2 * π)) (btzPaperCyl p) = x := by
    rw [← E0.toPaper_symm_eq_orbitMk hyax (E0.polar_angle hy₀ y), Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc
    (p := p) (E0.rad_pos.2 hyax) (by rw [hpx]; exact hx)
  set φ : BTZE0 → ℝ × ℝ × ℝ := fun z =>
    ((E0.toPaper z).1, E0.rad (E0.toPaper z), E0.angle y₀ (E0.toPaper z))
  have hφ : ContinuousAt φ x := by
    have hang : ContinuousAt (E0.angle y₀) y :=
      (E0.continuousOn_angle y₀).continuousAt ((E0.isOpen_sector y₀).mem_nhds hxs)
    have h3 : ContinuousAt (fun z => E0.angle y₀ (E0.toPaper z)) x :=
      ContinuousAt.comp (g := E0.angle y₀) (f := E0.toPaper) hang E0.toPaper.continuous.continuousAt
    exact (continuous_fst.comp E0.toPaper.continuous).continuousAt.prodMk
      ((E0.continuous_rad.comp E0.toPaper.continuous).continuousAt.prodMk h3)
  have h1 : ∀ᶠ z in 𝓝 x, c (orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z))) =
      g • btzPaperDev (φ z) := hφ.eventually hg
  have h2 : ∀ᶠ z in 𝓝 x, E0.toPaper z ∈ E0.sector y₀ :=
    E0.toPaper.continuous.continuousAt.preimage_mem_nhds
      ((E0.isOpen_sector y₀).mem_nhds hxs)
  refine ⟨g, ?_⟩
  filter_upwards [h1, h2] with z hz1 hz2
  have hzax : E0.toPaper z ∉ E0.axis := E0.not_mem_axis_of_mem_sector hz2
  have hz : orbitMk (GammaA (2 * π)) (btzPaperCyl (φ z)) = z := by
    rw [← E0.toPaper_symm_eq_orbitMk hzax (E0.polar_angle hy₀ (E0.toPaper z)),
      Homeomorph.symm_apply_apply]
  rw [hz] at hz1
  rw [hz1, E0.chartMap_eq]

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The flat chart of `Reg M` read in a spear chart** (the chart identification behind (G4a)):
near an off-axis point `x` of the spear chart `ψ`, the flat chart of `Reg M` at `ψ(x)` composed
with `ψ` is `g •` the sector chart `chartMap x` of `𝔼₀`, for one `g ∈ Isom(𝐌³)` (`ψ` is locally a
groupoid element, `e0_flat_transition_aux`, and a chart of the a.e. atlas is `g •` a sector chart,
`btz_chart_eq_smul_btzPaperDev`). -/
theorem SpearSurgeryDatum.eventually_regChart {S : Set M} (D : SpearSurgeryDatum M S) {x : E0}
    (hx : x.2 ≠ 0) (hxW : paperInY x ∈ D.W) (y : E0LM.e0RegM M)
    (hy : (y : M) = D.ψ (paperInY x)) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ w in 𝓝 x,
      D.ψ (paperInY w) ∈ (E0LM.regChartM y).source ∧
        E0LM.regChartM y (D.ψ (paperInY w)) = g • E0.chartMap x w := by
  set q := paperInY x with hqdef
  set u : BTZE0 := E0.toPaper.symm x with hudef
  have hqu : q = Sum.inr u := paperInY_apply x
  have hus : E0.toPaper u ∈ E0.sector x := by
    rw [hudef, Homeomorph.apply_symm_apply]; exact E0.mem_sector_self hx
  have hureg : u ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 :=
    (E0.mem_reg_iff_toPaper u).2 (E0.not_mem_axis_of_mem_sector hus)
  obtain ⟨c'', hc'', hu''⟩ := mem_support.1 hureg
  obtain ⟨g3, hg3⟩ := surgery_aeChart_eventually_chartMap hc'' hu'' hx hus
  set c₂ := e0Inr.symm.trans c'' with hc₂def
  have hc₂ : c₂ ∈ e0Atlas := e0InrChart_mem_e0Atlas hc''
  have hqc₂ : q ∈ c₂.source := mem_e0InrChart_source.2 ⟨u, hu'', hqu⟩
  -- `ψ` is locally a groupoid element at `q`
  obtain ⟨hψc, t, ht, hteq, hqt⟩ : ContinuousWithinAt D.ψ D.W q ∧ ∃ t ∈ e0Groupoid,
      EqOn (chartAt E0Y (D.ψ q) ∘ D.ψ ∘ (chartAt E0Y q).symm) t
        ((chartAt E0Y q).symm ⁻¹' D.W ∩ t.source) ∧ chartAt E0Y q q ∈ t.source := by
    obtain ⟨h1, h2⟩ := D.mor q hxW
    exact ⟨h1, h2 (by simpa using hxW)⟩
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    preimage_id_eq, id_eq, comp_id] at hteq hqt
  rw [← hy] at hteq
  set em := chartAt E0Y (y : M) with hem
  set R := E0LM.regAtlasChart y with hR
  have htq : t q = em y := by rw [← hteq ⟨hxW, hqt⟩]; simp [hy]
  have hRsrc : t q ∈ R.source := by rw [htq]; exact E0LM.mem_regAtlasChart_source y
  have hvsrc : c₂ q ∈ (c₂.symm.trans (t.trans R)).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source, c₂.left_inv hqc₂]
    exact ⟨c₂.map_source hqc₂, hqt, hRsrc⟩
  obtain ⟨g4, hg4⟩ := E0LM.e0_flat_transition_aux ht hc₂ (E0LM.regAtlasChart_mem y) _ hvsrc
  have hpc : ContinuousAt (fun w : E0 => paperInY w) x :=
    paperInY.continuousAt (by rw [paperInY_source]; trivial)
  have hψq : ContinuousAt D.ψ q := hψc.continuousAt (D.isOpen.mem_nhds hxW)
  -- the eventual facts near `x`
  have hE1 : ∀ᶠ w in 𝓝 x, paperInY w ∈ t.source ∩ D.W :=
    hpc.preimage_mem_nhds ((t.open_source.inter D.isOpen).mem_nhds ⟨hqt, hxW⟩)
  have hE2 : ∀ᶠ w in 𝓝 x, paperInY w ∈ c₂.source :=
    hpc.preimage_mem_nhds (c₂.open_source.mem_nhds hqc₂)
  have hE3 : ∀ᶠ w in 𝓝 x, (c₂.symm.trans (t.trans R)) (c₂ (paperInY w)) =
      g4 • c₂ (paperInY w) :=
    (ContinuousAt.comp (g := c₂) (f := fun w : E0 => paperInY w) (c₂.continuousAt hqc₂)
      hpc).eventually hg4
  have hE4 : ∀ᶠ w in 𝓝 x, c'' (E0.toPaper.symm w) = g3 • E0.chartMap x (E0.toPaper (E0.toPaper.symm w)) :=
    E0.toPaper.symm.continuous.continuousAt.eventually hg3
  have hE5 : ∀ᶠ w in 𝓝 x, t (paperInY w) ∈ R.source :=
    (ContinuousAt.comp (g := t) (f := fun w : E0 => paperInY w) (t.continuousAt hqt)
      hpc).preimage_mem_nhds (R.open_source.mem_nhds hRsrc)
  have hE6 : ∀ᶠ w in 𝓝 x, D.ψ (paperInY w) ∈ em.source :=
    (ContinuousAt.comp (g := D.ψ) (f := fun w : E0 => paperInY w) hψq
      hpc).preimage_mem_nhds (em.open_source.mem_nhds (by
      show D.ψ q ∈ em.source; rw [← hy]; exact mem_chart_source E0Y (y : M)))
  refine ⟨g4 * g3, ?_⟩
  filter_upwards [hE1, hE2, hE3, hE4, hE5, hE6] with w h1 h2 h3 h4 h5 h6
  have hψt : em (D.ψ (paperInY w)) = t (paperInY w) := hteq ⟨h1.2, h1.1⟩
  refine ⟨?_, ?_⟩
  · rw [E0LM.regChartM, OpenPartialHomeomorph.trans_source]
    exact ⟨h6, show em _ ∈ R.source by rw [hψt]; exact h5⟩
  show R (em (D.ψ (paperInY w))) = _
  rw [hψt]
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply, c₂.left_inv h2] at h3
  rw [h3, mul_smul]
  congr 1
  rw [Homeomorph.apply_symm_apply] at h4
  rw [← h4]
  simp [c₂, paperInY_apply]

end ChartRead

section ChartHeight

variable {d : ℕ}

theorem isom_smul_eq_add (g : Causal.Flat.isom d) (p : Causal.Minkowski d) :
    g • p = g • (0 : Causal.Minkowski d) + (g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d).linear p := by
  have h := Causal.Flat.isom_sub (g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d) 0 p
  rw [sub_zero] at h
  rw [Causal.Flat.isom_smul_def, Causal.Flat.isom_smul_def, ← h]
  abel

/-- The derivative of an isometry is its linear part. -/
theorem hasFDerivAt_isom_act (g : Causal.Flat.isom d) (p : Causal.Minkowski d) :
    HasFDerivAt (fun p : Causal.Minkowski d => g • p)
      (LinearMap.toContinuousLinearMap
        ((g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d).linear : Causal.Minkowski d →ₗ[ℝ] Causal.Minkowski d)) p := by
  have : (fun p : Causal.Minkowski d => g • p) = fun p => g • (0 : Causal.Minkowski d) +
      LinearMap.toContinuousLinearMap
        ((g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d).linear : Causal.Minkowski d →ₗ[ℝ] Causal.Minkowski d) p :=
    funext fun p => isom_smul_eq_add g p
  rw [this]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

theorem contDiff_isom_smul (g : Causal.Flat.isom d) :
    ContDiff ℝ 1 (fun p : Causal.Minkowski d => g • p) := by
  have : (fun p : Causal.Minkowski d => g • p) = fun p => g • (0 : Causal.Minkowski d) +
      LinearMap.toContinuousLinearMap
        ((g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d).linear : Causal.Minkowski d →ₗ[ℝ] Causal.Minkowski d) p :=
    funext fun p => isom_smul_eq_add g p
  rw [this]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

/-- **The height above the graph of `G` read in a flat frame** `g`:
`p ↦ nullHeight G (D⁻¹(g⁻¹ p))`. -/
noncomputable def chartHeight (G : ℝ × ℝ → ℝ) (g : Causal.Flat.isom 2) (p : Causal.Minkowski 2) : ℝ :=
  nullHeight G (nullToMink.symm (g⁻¹ • p))

/-- The null coordinates of `g⁻¹ p`. -/
noncomputable def chartNull (g : Causal.Flat.isom 2) (p : Causal.Minkowski 2) : ℝ × ℝ × ℝ :=
  nullToMink.symm (g⁻¹ • p)

theorem contDiff_chartNull (g : Causal.Flat.isom 2) : ContDiff ℝ 1 (chartNull g) :=
  (LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).contDiff.comp
    (contDiff_isom_smul g⁻¹)

theorem isOpen_chartPos (g : Causal.Flat.isom 2) :
    IsOpen {p : Causal.Minkowski 2 | 0 < (chartNull g p).2.1} :=
  isOpen_nullPos.preimage (contDiff_chartNull g).continuous

theorem contDiffOn_chartHeight {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    (hGs : ContDiffOn ℝ 1 G {q | 0 < q.1}) (g : Causal.Flat.isom 2) :
    ContDiffOn ℝ 1 (chartHeight G g) {p : Causal.Minkowski 2 | 0 < (chartNull g p).2.1} :=
  (contDiffOn_nullHeight hG hGs).comp (contDiff_chartNull g).contDiffOn fun _ hp => hp

/-- **Lemma 2.7 in a flat frame**: at `p₀ = g • D(τ, r, θ)` (`r > 0`) of a spacelike graph,
the derivative of `chartHeight G g` is positive on every nonzero future causal vector. -/
theorem fderiv_chartHeight_pos {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    (hGs : ContDiffOn ℝ 1 G {q | 0 < q.1}) (g : Causal.Flat.isom 2) {pp : ℝ × ℝ × ℝ}
    (hr : 0 < pp.2.1) {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt G L (pp.2.1, pp.2.2))
    (hδ : 0 < spacelikeDelta (L (1, 0)) (L (0, 1)) pp.2.1) {v : Causal.Minkowski 2}
    (hv0 : v ≠ 0) (hv : Causal.Flat.IsFutureCausal v) :
    0 < fderiv ℝ (chartHeight G g) (g • nullToMink (btzPaperNull pp)) v := by
  have hQ : chartNull g (g • nullToMink (btzPaperNull pp)) = btzPaperNull pp := by
    simp [chartNull]
  have hd : DifferentiableAt ℝ (nullHeight G) (btzPaperNull pp) :=
    ((contDiffOn_nullHeight hG hGs).differentiableOn one_ne_zero).differentiableAt
      (isOpen_nullPos.mem_nhds (show 0 < (btzPaperNull pp).2.1 from hr))
  set N := LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)
  set Li := LinearMap.toContinuousLinearMap
    (((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
      Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)
  have hcn : HasFDerivAt (chartNull g) (N.comp Li) (g • nullToMink (btzPaperNull pp)) :=
    N.hasFDerivAt.comp _ (hasFDerivAt_isom_act g⁻¹ _)
  have hH : HasFDerivAt (chartHeight G g) ((fderiv ℝ (nullHeight G) (btzPaperNull pp)).comp
      (N.comp Li)) (g • nullToMink (btzPaperNull pp)) := by
    have := (hQ ▸ hd).hasFDerivAt.comp _ hcn
    rw [hQ] at this
    exact this
  rw [hH.fderiv, ContinuousLinearMap.comp_apply]
  set u := Li v
  have hu : Causal.Flat.IsFutureCausal u := Causal.Flat.lorentz.isFutureCausal_apply (g⁻¹).2 hv
  have hu0 : u ≠ 0 := by
    intro h
    apply hv0
    have hinj := ((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective
    exact hinj (by rw [map_zero]; exact h)
  refine fderiv_nullHeight_pos hG hr hL hδ hd ?_ ?_
  · rw [nullCone_iff_isFutureCausal]
    simpa [N] using hu
  · intro h
    apply hu0
    have h' : N u = 0 := h
    have : nullToMink (N u) = nullToMink 0 := by rw [h']
    simpa [N] using this

theorem chartNull_mul (g₁ g : Causal.Flat.isom 2) (q : Causal.Minkowski 2) :
    chartNull (g₁ * g) q = chartNull g (g₁⁻¹ • q) := by
  simp only [chartNull, mul_inv_rev, mul_smul]

theorem chartHeight_mul (G : ℝ × ℝ → ℝ) (g₁ g : Causal.Flat.isom 2) (q : Causal.Minkowski 2) :
    chartHeight G (g₁ * g) q = chartHeight G g (g₁⁻¹ • q) := by
  simp only [chartHeight, mul_inv_rev, mul_smul]

/-- The future null direction `∂_τ` of `𝔼₀`, developed: `D(τ + s, r, θ) = D(τ, r, θ) + s n₀`. -/
noncomputable def tauDir : Causal.Minkowski 2 := nullToMink (2, 0, 0)

theorem btzPaperNull_shift (τ r θ s : ℝ) :
    btzPaperNull (τ - s, r, θ) = btzPaperNull (τ, r, θ) - s • ((2 : ℝ), (0 : ℝ), (0 : ℝ)) := by
  simp only [btzPaperNull, Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk]
  refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem chartMap_shift (x w : E0) (s : ℝ) :
    E0.chartMap x ((w.1 - s, w.2) : E0) = E0.chartMap x w - s • tauDir := by
  simp only [E0.chartMap, locLift, lift, tauDir]
  rw [show rad ((w.1 - s, w.2) : E0) = rad w from rfl, btzPaperNull_shift, map_sub, map_smul]

theorem isom_smul_sub_smul (g : Causal.Flat.isom 2) (p v : Causal.Minkowski 2) (s : ℝ) :
    g • (p - s • v) = g • p - s • (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear v := by
  rw [isom_smul_eq_add g (p - s • v), isom_smul_eq_add g p, map_sub, map_smul]
  abel

theorem isFutureCausal_tauDir : Causal.Flat.IsFutureCausal tauDir := by
  rw [tauDir, ← nullCone_iff_isFutureCausal]
  exact ⟨by norm_num, le_rfl, by norm_num⟩

theorem tauDir_ne_zero : tauDir ≠ 0 := by
  intro h
  have : nullToMink.symm tauDir = nullToMink.symm 0 := by rw [h]
  simp [tauDir] at this

/-- An isometry's linear part sends a nonzero future causal vector to one with `m.1 > 0`,
`‖m.2‖ ≤ m.1`. -/
theorem lorentz_apply_pos {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hA : A ∈ Causal.Flat.lorentz 2)
    {v : Causal.Minkowski 2} (hv : Causal.Flat.IsFutureCausal v) (hv0 : v ≠ 0) :
    Causal.Flat.IsFutureCausal (A v) ∧ A v ≠ 0 ∧ 0 < (A v).1 ∧ ‖(A v).2‖ ≤ (A v).1 := by
  set m := A v
  have hm : Causal.Flat.IsFutureCausal m := Causal.Flat.lorentz.isFutureCausal_apply hA hv
  have hm0 : m ≠ 0 := fun h => hv0 (A.injective (by rw [map_zero]; exact h))
  refine ⟨hm, hm0, ?_⟩
  obtain ⟨h1, h2⟩ := hm
  simp only [Causal.Flat.minkQ] at h2
  have hn : ‖m.2‖ ≤ m.1 := by
    have : ‖m.2‖ ^ 2 ≤ m.1 ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h1 two_ne_zero).1 this
  refine ⟨lt_of_le_of_ne h1 fun h => hm0 ?_, hn⟩
  have h0 : ‖m.2‖ = 0 := le_antisymm (h ▸ hn) (norm_nonneg _)
  exact Prod.ext h.symm (norm_eq_zero.1 h0)

/-- The developed `∂_τ` read in a frame: future causal with `m.1 > 0`, `‖m.2‖ ≤ m.1`. -/
theorem frame_tauDir (g : Causal.Flat.isom 2) :
    0 < ((g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir).1 ∧
      ‖((g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir).2‖ ≤
        ((g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir).1 := by
  set m := (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir
  have hm : Causal.Flat.IsFutureCausal m := Causal.Flat.lorentz.isFutureCausal_apply g.2 isFutureCausal_tauDir
  have hm0 : m ≠ 0 := fun h => tauDir_ne_zero
    ((g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective (by rw [map_zero]; exact h))
  obtain ⟨h1, h2⟩ := hm
  simp only [Causal.Flat.minkQ] at h2
  have hn : ‖m.2‖ ≤ m.1 := by
    have : ‖m.2‖ ^ 2 ≤ m.1 ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h1 two_ne_zero).1 this
  refine ⟨lt_of_le_of_ne h1 fun h => hm0 ?_, hn⟩
  have h0 : ‖m.2‖ = 0 := le_antisymm (h ▸ hn) (norm_nonneg _)
  exact Prod.ext h.symm (norm_eq_zero.1 h0)

/-- **The tangent bound of Lemma 2.8 in null coordinates**: at a point `p = (τ, r, θ)`, `r > 0`,
of a graph with `δ ≥ 1/r²`, a vector `V` tangent to the level set of the height
(`fderiv (nullHeight G) (btzPaperNull p) V = 0`) has `ds²(V) = c² − ab ≥ (V_b / r)²`. -/
theorem sq_div_le_nullQ_of_tangent {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    {p : ℝ × ℝ × ℝ} (hr : 0 < p.2.1) {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt G L (p.2.1, p.2.2))
    (hδ : 1 / p.2.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.2.1)
    (hd : DifferentiableAt ℝ (nullHeight G) (btzPaperNull p)) {V : ℝ × ℝ × ℝ}
    (hV : fderiv ℝ (nullHeight G) (btzPaperNull p) V = 0) :
    (V.2.1 / p.2.1) ^ 2 ≤ V.2.2 ^ 2 - V.1 * V.2.1 := by
  obtain ⟨L', hL', hL'h⟩ := hasFDerivAt_btzPaperNull p
  set h : ℝ × ℝ × ℝ → ℝ := fun q => q.1 - G (q.2.1, q.2.2)
  have hh : HasFDerivAt h ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
      L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_fst.sub (hL.comp p hasFDerivAt_snd)
  have hev : (nullHeight G ∘ btzPaperNull) =ᶠ[𝓝 p] h := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hr]
      with q hq
    have hq' : 0 < (btzPaperNull q).2.1 := hq
    rw [comp_apply, nullHeight_eq hG hq']
    simp only [nullHeightExpl, h, btzPaperNull]
    have hq0 : q.2.1 ≠ 0 := ne_of_gt hq
    congr 1
    · field_simp; ring
    · congr 2; field_simp
  have hcomp := hd.hasFDerivAt.comp p hL'
  have heq := (hcomp.congr_of_eventuallyEq hev.symm).unique hh
  set r := p.2.1
  set θ := p.2.2
  set wr := V.2.1
  set wθ := -(V.2.2 + V.2.1 * θ) / r
  set wτ := (V.1 - V.2.1 * θ ^ 2 - 2 * r * θ * wθ + V.2.1) / 2
  have hw : L' (wτ, wr, wθ) = V := by
    rw [hL'h]
    have hr0 : r ≠ 0 := ne_of_gt hr
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [wτ, wθ, wr]; field_simp; ring
    · simp only [wθ, wr]; field_simp; ring
  have hval : fderiv ℝ (nullHeight G) (btzPaperNull p) V = wτ - (wr * L (1, 0) + wθ * L (0, 1)) := by
    have := congrArg (fun T : ℝ × ℝ × ℝ →L[ℝ] ℝ => T (wτ, wr, wθ)) heq
    simp only [ContinuousLinearMap.comp_apply, hw] at this
    rw [this, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', clm_apply_pair]
  rw [hval] at hV
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hid : V.2.2 ^ 2 - V.1 * V.2.1 = graphQuad (L (1, 0)) (L (0, 1)) r wr wθ -
      2 * wr * (wτ - (wr * L (1, 0) + wθ * L (0, 1))) := by
    have h1 : -2 * wτ * wr + wr ^ 2 + r ^ 2 * wθ ^ 2 = V.2.2 ^ 2 - V.1 * V.2.1 := by
      simp only [wτ, wθ, wr]; field_simp; ring
    rw [← h1]; unfold graphQuad; ring
  rw [hid, hV, mul_zero, sub_zero, graphQuad_eq hr0]
  have hδ' : wr ^ 2 / r ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) r * wr ^ 2 := by
    have := mul_le_mul_of_nonneg_right hδ (sq_nonneg wr)
    rw [one_div, inv_mul_eq_div] at this
    linarith
  rw [div_pow]
  nlinarith [sq_nonneg (L (0, 1) / r * wr - r * wθ)]

/-- The chain rule for `chartHeight`: its derivative at `p` is that of `nullHeight` at
`chartNull g p`, applied to `D⁻¹ (L⁻¹ v)`. -/
theorem hasFDerivAt_chartHeight {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    (hGs : ContDiffOn ℝ 1 G {q | 0 < q.1}) (g : Causal.Flat.isom 2) {p : Causal.Minkowski 2}
    (hp : 0 < (chartNull g p).2.1) :
    HasFDerivAt (chartHeight G g) ((fderiv ℝ (nullHeight G) (chartNull g p)).comp
      ((LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).comp
        (LinearMap.toContinuousLinearMap
          (((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
            Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)))) p := by
  have hd : DifferentiableAt ℝ (nullHeight G) (chartNull g p) :=
    ((contDiffOn_nullHeight hG hGs).differentiableOn one_ne_zero).differentiableAt
      (isOpen_nullPos.mem_nhds hp)
  exact hd.hasFDerivAt.comp p
    ((LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).hasFDerivAt.comp
      p (hasFDerivAt_isom_act g⁻¹ p))

/-- The radial coordinate `r = b` of `chartNull g p`, its derivative. -/
theorem hasFDerivAt_chartNull_rad (g : Causal.Flat.isom 2) (p : Causal.Minkowski 2) :
    HasFDerivAt (fun q => (chartNull g q).2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).comp
        (LinearMap.toContinuousLinearMap
          (((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
            Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2))))) p := by
  have h := (LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).hasFDerivAt.comp
      p (hasFDerivAt_isom_act g⁻¹ p)
  exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp p h

/-- **The tangent bound in a flat frame** (Lemma 2.8's `δ ≥ 1/r²`, read in a chart): at
`p = g • D(τ, r, θ)` on the graph, a vector `v` tangent to the level set of `chartHeight G g` has
`(dr(v) / r)² ≤ ds²(v)`. -/
theorem sq_le_minkQ_of_tangent {G : ℝ × ℝ → ℝ} (hG : ∀ r θ, G (r, θ + 2 * π) = G (r, θ))
    (hGs : ContDiffOn ℝ 1 G {q | 0 < q.1}) (g : Causal.Flat.isom 2) {pp : ℝ × ℝ × ℝ}
    (hr : 0 < pp.2.1) {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt G L (pp.2.1, pp.2.2))
    (hδ : 1 / pp.2.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) pp.2.1) {v : Causal.Minkowski 2}
    (hv : fderiv ℝ (chartHeight G g) (g • nullToMink (btzPaperNull pp)) v = 0) :
    (fderiv ℝ (fun q => (chartNull g q).2.1) (g • nullToMink (btzPaperNull pp)) v / pp.2.1) ^ 2 ≤
      Causal.Flat.minkQ v := by
  have hQ : chartNull g (g • nullToMink (btzPaperNull pp)) = btzPaperNull pp := by
    simp [chartNull]
  have hp : 0 < (chartNull g (g • nullToMink (btzPaperNull pp))).2.1 := by rw [hQ]; exact hr
  have hd : DifferentiableAt ℝ (nullHeight G) (btzPaperNull pp) :=
    ((contDiffOn_nullHeight hG hGs).differentiableOn one_ne_zero).differentiableAt
      (isOpen_nullPos.mem_nhds (show 0 < (btzPaperNull pp).2.1 from hr))
  rw [(hasFDerivAt_chartHeight hG hGs g hp).fderiv, hQ] at hv
  rw [(hasFDerivAt_chartNull_rad g _).fderiv]
  set Li := LinearMap.toContinuousLinearMap
    (((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
      Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)
  set V := nullToMink.symm (Li v) with hVdef
  have h := sq_div_le_nullQ_of_tangent hG hr hL hδ hd (V := V) hv
  have hmq : Causal.Flat.minkQ v = V.2.2 ^ 2 - V.1 * V.2.1 := by
    have h1 : Causal.Flat.minkQ v = Causal.Flat.minkQ (Li v) :=
      (Causal.Flat.lorentz.minkQ_apply (g⁻¹).2 v).symm
    rw [h1, show Li v = nullToMink V by simp [hVdef], minkQ_nullToMink]
    simp only [nullQ]
  rw [hmq]
  exact h
/-- `log` is `1/m`-Lipschitz on `[m, ∞)`. -/
theorem abs_log_sub_log_le {m u u' : ℝ} (hm : 0 < m) (hu : m ≤ u) (hu' : m ≤ u') :
    |Real.log u - Real.log u'| ≤ (1 / m) * |u - u'| := by
  have key : ∀ a b : ℝ, m ≤ a → m ≤ b → b ≤ a → Real.log a - Real.log b ≤ (1 / m) * (a - b) := by
    intro a b ha hb hba
    have hb0 : 0 < b := hm.trans_le hb
    have h1 : Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div (hm.trans_le ha).ne' hb0.ne']
    have h2 := Real.log_le_sub_one_of_pos (div_pos (hm.trans_le ha) hb0)
    have h3 : a / b - 1 = (a - b) / b := by field_simp
    have h4 : (a - b) / b ≤ (a - b) / m := div_le_div_of_nonneg_left (by linarith) hm hb
    rw [h1]; calc Real.log (a / b) ≤ (a - b) / m := by linarith
      _ = (1 / m) * (a - b) := by ring
  rcases le_total u' u with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log (hm.trans_le hu') h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key u u' hu hu' h
  · rw [abs_sub_comm, abs_sub_comm u u',
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log (hm.trans_le hu) h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key u' u hu' hu h

/-- The radial coordinate of `chartNull g` is Lipschitz. -/
theorem lipschitzWith_chartNull_rad (g : Causal.Flat.isom 2) :
    ∃ K : NNReal, LipschitzWith K fun q => (chartNull g q).2.1 := by
  set ℓ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((LinearMap.toContinuousLinearMap (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).comp
        (LinearMap.toContinuousLinearMap
          (((g⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear :
            Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2))))
  have hdiff : ∀ p q, (chartNull g p).2.1 - (chartNull g q).2.1 = ℓ (p - q) := by
    intro p q
    simp only [chartNull, ℓ, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', LinearEquiv.coe_coe]
    rw [← Causal.Flat.isom_sub, map_sub, Prod.snd_sub, Prod.fst_sub]
    rfl
  refine ⟨‖ℓ‖₊, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [Real.dist_eq, hdiff, dist_eq_norm, ← Real.norm_eq_abs]
  exact ℓ.le_opNorm _

/-- **Local a.e. statements on `ℝ` are global** (a countable subcover, `isOpen_biUnion_countable`). -/
theorem ae_of_local {P : ℝ → Prop}
    (h : ∀ t : ℝ, ∃ ε > 0, ∀ᵐ u, u ∈ Ioo (t - ε) (t + ε) → P u) : ∀ᵐ u, P u := by
  choose ε hε hP using h
  obtain ⟨T, -, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (univ : Set ℝ)
    (fun t => Ioo (t - ε t) (t + ε t)) (fun t _ => isOpen_Ioo)
  have hall := (MeasureTheory.ae_ball_iff hTc).2 (fun t _ => hP t)
  filter_upwards [hall] with u hu
  have : u ∈ ⋃ t ∈ (univ : Set ℝ), Ioo (t - ε t) (t + ε t) :=
    mem_biUnion (mem_univ u) ⟨by linarith [hε u], by linarith [hε u]⟩
  rw [← hTU] at this
  obtain ⟨t, ht, hut⟩ := mem_iUnion₂.1 this
  exact hu t ht hut

end ChartHeight

section CuspInterior

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `mem_S0_iff` on the whole domain of the spear chart. -/
theorem SpearSurgeryDatum.mem_S0_iff' {S : Set M} (D : SpearSurgeryDatum M S)
    {x : E0} (hx : paperInY x ∈ D.W) : D.ψ (paperInY x) ∈ E0CBG.S0 M ↔ rad x = 0 := by
  rw [← SpearSurgeryDatum.paperInY_mem_e0SingY_iff,
    ← Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem D.isOpen D.mor hx le_rfl]
  show chartAt E0Y (paperInY x) (paperInY x) ∈ e0SingY 0 ↔ _
  rw [chartAt_self_eq]
  rfl

omit [SecondCountableTopology M] in
theorem regChart_apply_eq (y z : e0RegMFlat M) :
    chartAt (Causal.Minkowski 2) y z = E0LM.regChartM (show E0LM.e0RegM M from y) (regVal M z) :=
  rfl

omit [SecondCountableTopology M] in
theorem mem_regChart_source_iff (y z : e0RegMFlat M) :
    z ∈ (chartAt (Causal.Minkowski 2) y).source ↔
      regVal M z ∈ (E0LM.regChartM (show E0LM.e0RegM M from y)).source := by
  show z ∈ ((E0LM.regChartM (show E0LM.e0RegM M from y)).subtypeRestr ⟨y⟩).source ↔ _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  rfl

omit [SecondCountableTopology M] in
open scoped Pointwise in
/-- **(G4a), interior case**: at a point `ψ(x)` of a cusp with `r(x) < R`, `Σ*` is spacelike
Lipschitz. Near `ψ(x)` the flat chart of `Reg M` is `g • chartMap x ∘ ψ⁻¹`
(`SpearSurgeryDatum.eventually_regChart`), `Σ*` is the cusp, and its chart picture is the zero
set of the height `chartHeight G g`, `C¹` with derivative positive on the future causal cone at
the point (Lemma 2.7, `fderiv_chartHeight_pos`), hence cone-increasing on a ball
(`exists_ball_isConeIncreasingOn`). -/
theorem SurgeryData.isSpacelikeLipschitzAt_cusp_interior {S : Set M} (Dat : SurgeryData M S)
    (i : Dat.ι) {y : e0RegMFlat M} {x : E0} (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R)
    (hxR : rad x < (Dat.D i).R) (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  set D := Dat.D i with hD
  set y' : E0LM.e0RegM M := y
  have hrx : 0 < rad x := hx.1
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
  have hxsp : x ∈ E0Spear.spear D.v D.R := D.graphSet_subset_spear hx
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_regChart hx0 hxW y' hy
  have hper := D.spacelike.periodic
  -- `x` is in the open interior of the spear
  have hfx : D.v < fcoord x := by
    have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
      have := hx.2.2; simp only [height, heightAt] at this; linarith
    have h2 := D.above (rad x, Complex.arg x.2) hrx hx.2.1
    simp only [fcoord]; rw [h1]; linarith
  have hOx : ∀ᶠ w in 𝓝 x, (D.ψ (paperInY w) ∈ (E0LM.regChartM y').source ∧
      E0LM.regChartM y' (D.ψ (paperInY w)) = g • E0.chartMap x w) ∧
      D.v < fcoord w ∧ 0 < rad w ∧ rad w < D.R := by
    have hfc : Continuous fcoord := continuous_fst.sub (continuous_rad.div_const 2)
    exact hg.and ((hfc.continuousAt.eventually (lt_mem_nhds hfx)).and
      ((continuous_rad.continuousAt.eventually (lt_mem_nhds hrx)).and
        (continuous_rad.continuousAt.eventually (gt_mem_nhds hxR))))
  -- the chart picture
  set e := chartAt (Causal.Minkowski 2) y with he
  set F := chartHeight D.G g with hF
  set U := {p : Causal.Minkowski 2 | 0 < (chartNull g p).2.1} with hU
  set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
  have hlocx : locLift x x = btzPaperNull pp := rfl
  have hp₀ : e y = g • nullToMink (btzPaperNull pp) := by
    rw [regChart_apply_eq, hy, (hg.self_of_nhds).2, E0.chartMap, hlocx]
  have hQ₀ : chartNull g (e y) = btzPaperNull pp := by rw [hp₀]; simp [chartNull]
  have hp₀U : e y ∈ U := by
    show 0 < (chartNull g (e y)).2.1
    rw [hQ₀]; exact hrx
  have hxR' : rad x ≤ D.R := hx.2.1
  obtain ⟨L, hL, hδ⟩ := D.spacelike.deriv (rad x, angle x x) hrx hxR'
  obtain ⟨ε, hε, c, hc0, hc1, hballU, hinc⟩ := exists_ball_isConeIncreasingOn (isOpen_chartPos g)
    (contDiffOn_chartHeight hper D.smooth g) hp₀U (by
      intro v hv0 hv
      rw [hp₀]
      exact fderiv_chartHeight_pos hper D.smooth g hrx hL hδ hv0 hv)
  -- the eventual facts at `e y`
  set Φ : Causal.Minkowski 2 → E0 := fun p => unlift (chartNull g p) with hΦ
  have hΦc : ContinuousAt Φ (e y) :=
    (continuousAt_unlift (by rw [hQ₀]; exact hrx.ne')).comp (contDiff_chartNull g).continuous.continuousAt
  have hΦ₀ : Φ (e y) = x := by
    simp only [Φ, hQ₀, ← hlocx]
    have := unlift_symm_chartMap hx0 x
    rwa [E0.chartMap, LinearEquiv.symm_apply_apply] at this
  have hImg : ∀ᶠ p in 𝓝 (e y), chartNull g p ∈ Img x := by
    have h0 : chartNull g (e y) ∈ Img x := by rw [hQ₀, ← hlocx]; exact locLift_mem_Img (mem_sector_self hx0)
    have hθc : ContinuousAt (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) (chartNull g (e y)) :=
      ((continuous_snd.comp continuous_snd).continuousAt.div
        (continuous_fst.comp continuous_snd).continuousAt (by rw [hQ₀]; exact hrx.ne')).neg
    have hev : ∀ᶠ Q in 𝓝 (chartNull g (e y)), Q ∈ Img x := by
      have h1 : ∀ᶠ Q in 𝓝 (chartNull g (e y)), 0 < Q.2.1 :=
        isOpen_nullPos.mem_nhds h0.1
      have h2 : ∀ᶠ Q in 𝓝 (chartNull g (e y)), |-(Q.2.2 / Q.2.1) - Complex.arg x.2| < π :=
        (hθc.sub continuousAt_const).abs.eventually (gt_mem_nhds h0.2)
      filter_upwards [h1, h2] with Q h1 h2 using ⟨h1, h2⟩
    exact (contDiff_chartNull g).continuous.continuousAt.eventually hev
  have hT : Tendsto Φ (𝓝 (e y)) (𝓝 x) := hΦ₀ ▸ hΦc.tendsto
  have hΦO := hT.eventually hOx
  have htgt : ∀ᶠ p in 𝓝 (e y), p ∈ e.target := e.open_target.mem_nhds (e.map_source (mem_chart_source _ y))
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff_ball.1 ((hImg.and hΦO).and htgt)
  set W := Metric.ball (e y) (min ε ε') with hW
  have hWε : W ⊆ Metric.ball (e y) ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWε' : W ⊆ Metric.ball (e y) ε' := Metric.ball_subset_ball (min_le_right _ _)
  have hycusp : regVal M y ∈ D.cusp := by rw [hy]; exact ⟨paperInY x, ⟨x, hx, rfl⟩, rfl⟩
  have hyT : y ∈ Dat.sigmaStarReg :=
    show regVal M y ∈ Dat.sigmaStar from Or.inr (mem_iUnion.2 ⟨i, hycusp⟩)
  refine isSpacelikeLipschitzAt_of_coneZeroSet (g := 1) Metric.isOpen_ball
    (Metric.mem_ball_self (lt_min hε hε')) (fun p hp => (hball' p (hWε' hp)).2)
    ((contDiffOn_chartHeight hper D.smooth g).continuousOn.mono fun p hp => hballU (hWε hp))
    hc0 hc1 (by rw [one_smul]; simpa using hinc.mono le_rfl hWε) ?_ hyT
  -- the zero set
  intro p hp
  obtain ⟨⟨hpImg, ⟨hsrc, hchart⟩, hfw, hrw, hrwR⟩, -⟩ := hball' p (hWε' hp)
  set w := Φ p with hw
  have hwsp : w ∈ E0Spear.spear D.v D.R := ⟨hfw.le, hrwR.le⟩
  have hreg : D.ψ (paperInY w) ∈ E0LM.e0RegM M := fun hS0 => by
    have := (D.mem_S0_iff hwsp).1 hS0; linarith
  set z₀ : e0RegMFlat M := (⟨D.ψ (paperInY w), hreg⟩ : E0LM.e0RegM M)
  have hz₀src : z₀ ∈ e.source := (mem_regChart_source_iff y z₀).2 hsrc
  have hez₀ : e z₀ = p := by
    rw [regChart_apply_eq]
    show E0LM.regChartM y' (D.ψ (paperInY w)) = p
    rw [hchart, E0.chartMap, locLift_unlift hx0 hpImg, chartNull, LinearEquiv.apply_symm_apply,
      smul_inv_smul]
  have hFp : chartHeight D.G g p = height D.G w := rfl
  have hspear : D.ψ (paperInY w) ∈ D.spearSet := ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
  constructor
  · rintro ⟨z, ⟨hzT, hzs⟩, hzp⟩
    have hzz : z = z₀ := e.injOn hzs hz₀src (hzp.trans hez₀.symm)
    rw [hzz] at hzT
    have hc : D.ψ (paperInY w) ∈ D.cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hzT, hspear⟩
    obtain ⟨_, ⟨x', hx', rfl⟩, hx'e⟩ := hc
    have hx'sp := D.graphSet_subset_spear hx'
    have hpw : paperInY x' = paperInY w :=
      D.inj (D.spear_sub ⟨x', hx'sp, rfl⟩) (D.spear_sub ⟨w, hwsp, rfl⟩) hx'e
    have : x' = w := paperInY.injOn (by simp) (by simp) hpw
    rw [hFp, ← this]; exact hx'.2.2
  · intro h0
    have hwg : w ∈ graphSet D.G D.R := ⟨hrw, hrwR.le, by rw [← hFp]; exact h0⟩
    have hT : z₀ ∈ Dat.sigmaStarReg :=
      show D.ψ (paperInY w) ∈ Dat.sigmaStar from
        Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, hwg, rfl⟩, rfl⟩⟩)
    exact ⟨z₀, ⟨hT, hz₀src⟩, hez₀⟩

omit [SecondCountableTopology M] in
open scoped Pointwise in
set_option maxHeartbeats 1000000 in
/-- **(G4a), rim case**: at a point `ψ(x)` of a cusp with `r(x) = R`, `Σ*` is spacelike Lipschitz.
In the frame `g₁` in which `S` is locally the graph of a `c₁`-Lipschitz `u` (`hS.reg`), `Σ*` is
the zero set of the function equal to the cusp height `chartHeight G (g₁ g)` on `{r ≤ R}` and to
the null-shift height `σ` of `S` along the developed `∂_τ` on `{r > R}` (`exists_nullShift`). The
two agree on the cylinder `r = R` (the rim `C = C*`: shifting along `∂_τ` stays on the cylinder,
where the cusp and `S` meet `τ`-lines at the same point), so the function is continuous; each is
cone-increasing, and across the cylinder a segment is cut at a crossing point (intermediate value
theorem), so the glued function is cone-increasing. -/
theorem SurgeryData.isSpacelikeLipschitzAt_cusp_rim {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M} {x : E0}
    (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R) (hxR : rad x = (Dat.D i).R)
    (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  classical
  set D := Dat.D i with hD
  set y' : E0LM.e0RegM M := y
  have hrx : 0 < rad x := hx.1
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
  have hxsp : x ∈ E0Spear.spear D.v D.R := D.graphSet_subset_spear hx
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_regChart hx0 hxW y' hy
  have hper := D.spacelike.periodic
  have hx1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    have := hx.2.2; simp only [height, heightAt] at this; linarith
  have hfx : D.v < fcoord x := by
    have h2 := D.above (rad x, Complex.arg x.2) hrx hx.2.1
    simp only [fcoord]; rw [hx1]; linarith
  have hxS : D.ψ (paperInY x) ∈ S := (D.graph x hxsp).2 (by rw [hx1, rim_value D.rim hxR])
  have hyS : y ∈ regSet M S := show regVal M y ∈ S by rw [hy]; exact hxS
  set e := chartAt (Causal.Minkowski 2) y with he
  obtain ⟨V, hpV, hVt, hVL⟩ := hS.reg y hyS
  set Sc := e '' (regSet M S ∩ e.source) ∩ (V : Set (Causal.Minkowski 2)) with hSc
  have hySc : e y ∈ Sc := ⟨⟨y, ⟨hyS, mem_chart_source _ y⟩, rfl⟩, hpV⟩
  obtain ⟨g₁, O, U', u, c₁, hc₁, hpO, hOV, hU', hu, hgr⟩ := hVL.locGraph (e y) hySc
  -- the frame `g₁` and the null direction
  set g' := g₁ * g with hg'
  set L₁ := (g₁ : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear
  set n := (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir with hn
  obtain ⟨hnc, hn0, -, -⟩ := lorentz_apply_pos g.2 isFutureCausal_tauDir tauDir_ne_zero
  set m := L₁ n with hmdef
  obtain ⟨-, -, hm, hmn⟩ := lorentz_apply_pos g₁.2 hnc hn0
  set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
  have hlocx : locLift x x = btzPaperNull pp := rfl
  have hp₀ : e y = g • nullToMink (btzPaperNull pp) := by
    rw [regChart_apply_eq, hy, (hg.self_of_nhds).2, E0.chartMap, hlocx]
  set q₀ := g₁ • e y with hq₀def
  have hq₀ : q₀ = g' • nullToMink (btzPaperNull pp) := by rw [hq₀def, hp₀, hg', mul_smul]
  have hq₀gr : q₀ ∈ Causal.Flat.graphOver U' u := by
    have : q₀ ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := Set.smul_mem_smul_set ⟨hySc, hpO⟩
    rw [hgr] at this; exact this.2
  obtain ⟨δ₁, hδ₁, σ, hσ0, hσ⟩ := exists_nullShift hU' hc₁ hu hm hmn hq₀gr.1 hq₀gr.2
  -- the cusp height in the frame
  have hQ₀ : chartNull g' q₀ = btzPaperNull pp := by rw [hq₀]; simp [chartNull]
  have hq₀U : q₀ ∈ {q : Causal.Minkowski 2 | 0 < (chartNull g' q).2.1} := by
    show 0 < (chartNull g' q₀).2.1; rw [hQ₀]; exact hrx
  obtain ⟨L, hL, hδ⟩ := D.spacelike.deriv (rad x, angle x x) hrx hxR.le
  obtain ⟨ε, hε, cI, hcI0, hcI1, hballU, hincI⟩ := exists_ball_isConeIncreasingOn (isOpen_chartPos g')
    (contDiffOn_chartHeight hper D.smooth g') hq₀U (by
      intro v hv0 hv
      rw [hq₀]
      exact fderiv_chartHeight_pos hper D.smooth g' hrx hL hδ hv0 hv)
  set FI := chartHeight D.G g' with hFI
  have hFIc : ContinuousOn FI (Metric.ball q₀ ε) :=
    (contDiffOn_chartHeight hper D.smooth g').continuousOn.mono hballU
  set Φ : Causal.Minkowski 2 → E0 := fun q => unlift (chartNull g' q) with hΦ
  have hΦc : ContinuousOn Φ (Metric.ball q₀ ε) := fun q hq =>
    ((continuousAt_unlift (ne_of_gt (hballU hq))).comp
      (contDiff_chartNull g').continuous.continuousAt).continuousWithinAt
  have hΦ₀ : Φ q₀ = x := by
    simp only [Φ, hQ₀, ← hlocx]
    have := unlift_symm_chartMap hx0 x
    rwa [E0.chartMap, LinearEquiv.symm_apply_apply] at this
  have hFI₀ : FI q₀ = 0 := by
    show height D.G (Φ q₀) = 0
    rw [hΦ₀]; exact hx.2.2
  -- the other spears
  set Oth : Set M := ⋃ j : {j : Dat.ι // j ≠ i}, (Dat.D j).spearSet with hOth
  have hOthc : IsClosed Oth := by
    haveI := Dat.finite
    exact isClosed_iUnion_of_finite fun j => Dat.isClosed j
  have hxOth : D.ψ (paperInY x) ∉ Oth := by
    rintro hm'
    obtain ⟨⟨j, hj⟩, hjm⟩ := mem_iUnion.1 hm'
    exact Set.disjoint_left.1 (Dat.disjoint hj) hjm ⟨paperInY x, ⟨x, hxsp, rfl⟩, rfl⟩
  have hψc : ContinuousAt (fun w : E0 => D.ψ (paperInY w)) x := by
    have hψq : ContinuousAt D.ψ (paperInY x) :=
      ((D.mor _ hxW).1).continuousAt (D.isOpen.mem_nhds hxW)
    exact ContinuousAt.comp (g := D.ψ) (f := fun w : E0 => paperInY w) hψq
      (paperInY.continuousAt (by rw [paperInY_source]; trivial))
  have hOx : ∀ᶠ w in 𝓝 x, (D.ψ (paperInY w) ∈ (E0LM.regChartM y').source ∧
      E0LM.regChartM y' (D.ψ (paperInY w)) = g • E0.chartMap x w) ∧
      D.v < fcoord w ∧ 0 < rad w ∧ paperInY w ∈ D.W ∧ D.ψ (paperInY w) ∉ Oth := by
    have hfc : Continuous fcoord := continuous_fst.sub (continuous_rad.div_const 2)
    refine hg.and ((hfc.continuousAt.eventually (lt_mem_nhds hfx)).and
      ((continuous_rad.continuousAt.eventually (lt_mem_nhds hrx)).and
        ((show ∀ᶠ w in 𝓝 x, paperInY w ∈ D.W from
          (paperInY.continuousAt (by rw [paperInY_source]; trivial)).preimage_mem_nhds
            (D.isOpen.mem_nhds hxW)).and
          (show ∀ᶠ w in 𝓝 x, D.ψ (paperInY w) ∉ Oth from
            hψc.preimage_mem_nhds (hOthc.isOpen_compl.mem_nhds hxOth)))))
  -- the eventual facts at `q₀`
  have hq₀ε : Metric.ball q₀ ε ∈ 𝓝 q₀ := Metric.ball_mem_nhds _ hε
  have hΦca : ContinuousAt Φ q₀ := hΦc.continuousAt hq₀ε
  have hFIca : ContinuousAt FI q₀ := hFIc.continuousAt hq₀ε
  have hImg : ∀ᶠ q in 𝓝 q₀, chartNull g' q ∈ Img x := by
    have h0 : chartNull g' q₀ ∈ Img x := by
      rw [hQ₀, ← hlocx]; exact locLift_mem_Img (mem_sector_self hx0)
    have hθc : ContinuousAt (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) (chartNull g' q₀) :=
      ((continuous_snd.comp continuous_snd).continuousAt.div
        (continuous_fst.comp continuous_snd).continuousAt (by rw [hQ₀]; exact hrx.ne')).neg
    have hev : ∀ᶠ Q in 𝓝 (chartNull g' q₀), Q ∈ Img x := by
      have h1 : ∀ᶠ Q in 𝓝 (chartNull g' q₀), 0 < Q.2.1 := isOpen_nullPos.mem_nhds h0.1
      have h2 : ∀ᶠ Q in 𝓝 (chartNull g' q₀), |-(Q.2.2 / Q.2.1) - Complex.arg x.2| < π :=
        (hθc.sub continuousAt_const).abs.eventually (gt_mem_nhds h0.2)
      filter_upwards [h1, h2] with Q h1 h2 using ⟨h1, h2⟩
    exact (contDiff_chartNull g').continuous.continuousAt.eventually hev
  have hT : Tendsto Φ (𝓝 q₀) (𝓝 x) := hΦ₀ ▸ hΦca.tendsto
  have hΦO := hT.eventually hOx
  set Φ' : Causal.Minkowski 2 → E0 := fun q => ((Φ q).1 - FI q, (Φ q).2) with hΦ'
  have hT' : Tendsto Φ' (𝓝 q₀) (𝓝 x) := by
    have h : ContinuousAt Φ' q₀ :=
      ((continuous_fst.continuousAt.comp hΦca).sub hFIca).prodMk
        (continuous_snd.continuousAt.comp hΦca)
    have h0 : Φ' q₀ = x := by simp only [Φ', hΦ₀, hFI₀, sub_zero]
    exact h0 ▸ h.tendsto
  have hΦO' := hT'.eventually hOx
  have hinvc : Continuous fun q : Causal.Minkowski 2 => g₁⁻¹ • q := continuous_const_smul _
  have hp₀' : g₁⁻¹ • q₀ = e y := by rw [hq₀def, inv_smul_smul]
  have htgt : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • q ∈ e.target := by
    refine hinvc.continuousAt.preimage_mem_nhds ?_
    rw [hp₀']; exact e.open_target.mem_nhds (e.map_source (mem_chart_source _ y))
  have hVO_open : IsOpen ((V : Set (Causal.Minkowski 2)) ∩ (O : Set (Causal.Minkowski 2))) :=
    V.isOpen.inter O.isOpen
  have hVO : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • q ∈ (V : Set (Causal.Minkowski 2)) ∩ O := by
    refine hinvc.continuousAt.preimage_mem_nhds ?_
    rw [hp₀']; exact hVO_open.mem_nhds ⟨hpV, hpO⟩
  have hVO' : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • (q - FI q • m) ∈ (V : Set (Causal.Minkowski 2)) ∩ O := by
    have hc : ContinuousAt (fun q => g₁⁻¹ • (q - FI q • m)) q₀ :=
      hinvc.continuousAt.comp (continuousAt_id.sub (hFIca.smul continuousAt_const))
    refine hc.preimage_mem_nhds ?_
    simp only [hFI₀, zero_smul, sub_zero, hp₀']
    exact hVO_open.mem_nhds ⟨hpV, hpO⟩
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff_ball.1
    ((((hImg.and hΦO).and hΦO').and htgt).and (hVO.and hVO'))
  set δ := min (min ε δ₁) ε' with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hε hδ₁) hε'
  set W' := Metric.ball q₀ δ with hW'
  have hWε : W' ⊆ Metric.ball q₀ ε :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hWδ₁ : W' ⊆ Metric.ball q₀ δ₁ :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hWε' : W' ⊆ Metric.ball q₀ ε' := Metric.ball_subset_ball (min_le_right _ _)
  have hA1 : ∀ q ∈ W', chartNull g' q ∈ Img x := fun q hq => (hball' q (hWε' hq)).1.1.1.1
  have hA2 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).1.1.1.2
  have hA3 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).1.1.2
  have hA5 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).2.1
  have hA6 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).2.2
  -- the point of `Reg M` over `q`
  have hz : ∀ q ∈ W', ∀ (hreg : D.ψ (paperInY (Φ q)) ∈ E0LM.e0RegM M),
      ((⟨D.ψ (paperInY (Φ q)), hreg⟩ : E0LM.e0RegM M) : e0RegMFlat M) ∈ e.source ∧
      e (⟨D.ψ (paperInY (Φ q)), hreg⟩ : E0LM.e0RegM M) = g₁⁻¹ • q := by
    intro q hq hreg
    have hImgq := hA1 q hq
    have hsrc := (hA2 q hq).1.1
    have hchart := (hA2 q hq).1.2
    refine ⟨(mem_regChart_source_iff y _).2 hsrc, ?_⟩
    rw [regChart_apply_eq]
    show E0LM.regChartM y' (D.ψ (paperInY (Φ q))) = _
    rw [hchart, E0.chartMap, locLift_unlift hx0 hImgq, chartNull_mul, chartNull,
      LinearEquiv.apply_symm_apply, smul_inv_smul]
  have hreg : ∀ q ∈ W', D.ψ (paperInY (Φ q)) ∈ E0LM.e0RegM M := by
    intro q hq hS0
    have hr := (hA2 q hq).2.2.1
    have hWq := (hA2 q hq).2.2.2.1
    have := (D.mem_S0_iff' hWq).1 hS0
    linarith
  -- the cylinder: `σ = FI` on `r = R`
  have hcyl : ∀ q ∈ W', rad (Φ q) = D.R → σ q = FI q := by
    intro q hq hrq
    have hImgq := hA1 q hq
    have hsrc' := (hA3 q hq).1.1
    have hchart' := (hA3 q hq).1.2
    have hf' := (hA3 q hq).2.1
    have hVO'q := hA6 q hq
    have hrw' : rad (Φ' q) = D.R := hrq
    have hw'sp : Φ' q ∈ E0Spear.spear D.v D.R := ⟨hf'.le, hrw'.le⟩
    have hw'1 : (Φ' q).1 = D.τS (Φ' q).2 := by
      show (Φ q).1 - height D.G (Φ q) = D.τS (Φ q).2
      simp only [height, heightAt]; rw [rim_value D.rim hrq]; ring
    have hw'S : D.ψ (paperInY (Φ' q)) ∈ S := (D.graph _ hw'sp).2 hw'1
    have hreg' : D.ψ (paperInY (Φ' q)) ∈ E0LM.e0RegM M := fun h => by
      have := (D.mem_S0_iff hw'sp).1 h; linarith [D.pos]
    set z' : e0RegMFlat M := (⟨_, hreg'⟩ : E0LM.e0RegM M)
    have hz'src : z' ∈ e.source := (mem_regChart_source_iff y z').2 hsrc'
    have hez'0 : g • E0.chartMap x (Φ q) = g₁⁻¹ • q := by
      rw [E0.chartMap, locLift_unlift hx0 hImgq, chartNull_mul, chartNull,
        LinearEquiv.apply_symm_apply, smul_inv_smul]
    have hez' : g₁ • e z' = q - (FI q) • m := by
      rw [regChart_apply_eq]
      show g₁ • E0LM.regChartM y' (D.ψ (paperInY (Φ' q))) = _
      rw [hchart', show Φ' q = (((Φ q).1 - (FI q), (Φ q).2) : E0) from rfl, chartMap_shift,
        isom_smul_sub_smul, hez'0, isom_smul_sub_smul, smul_inv_smul]
    have hmem : e z' ∈ Sc ∩ (O : Set (Causal.Minkowski 2)) := by
      have h := hVO'q
      rw [← hez', inv_smul_smul] at h
      exact ⟨⟨⟨z', ⟨hw'S, hz'src⟩, rfl⟩, h.1⟩, h.2⟩
    have hgm : q - (FI q) • m ∈ Causal.Flat.graphOver U' u := by
      have : g₁ • e z' ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := Set.smul_mem_smul_set hmem
      rw [hgr, hez'] at this; exact this.2
    obtain ⟨-, h1, h2⟩ := hσ q (hWδ₁ hq)
    exact nullShift_unique hc₁ hu hm hmn h1 h2 hgm.1 hgm.2
  -- the glued height
  have hA4 : ∀ q ∈ W', g₁⁻¹ • q ∈ e.target := fun q hq => (hball' q (hWε' hq)).1.2
  set F : Causal.Minkowski 2 → ℝ := fun q => if rad (Φ q) ≤ D.R then FI q else σ q with hFdef
  have hσc : ContinuousOn σ W' :=
    continuousOn_nullShift hc₁ hu hm hmn fun q hq => (hσ q (hWδ₁ hq)).2
  have hFIcW : ContinuousOn FI W' := hFIc.mono hWε
  have hrc : ContinuousOn (fun q => rad (Φ q)) W' := continuous_rad.comp_continuousOn (hΦc.mono hWε)
  have hFc : ContinuousOn F W' := by
    refine ContinuousOn.if ?_ (hFIcW.mono inter_subset_left) (hσc.mono inter_subset_left)
    rintro a ⟨ha, hfr⟩
    have hca : ContinuousAt (fun q => rad (Φ q)) a :=
      hrc.continuousAt (Metric.isOpen_ball.mem_nhds ha)
    have heq : rad (Φ a) = D.R := by
      rcases lt_trichotomy (rad (Φ a)) D.R with h | h | h
      · exfalso
        apply hfr.2
        exact mem_interior_iff_mem_nhds.2
          (mem_of_superset (hca.eventually (gt_mem_nhds h)) fun b (hb : rad (Φ b) < D.R) =>
            show b ∈ {a | rad (Φ a) ≤ D.R} from le_of_lt hb)
      · exact h
      · exfalso
        have hcl := hfr.1
        rw [mem_closure_iff_frequently] at hcl
        obtain ⟨b, hb1, hb2⟩ := (hcl.and_eventually (hca.eventually (lt_mem_nhds h))).exists
        exact absurd hb1 (not_le.2 hb2)
    exact (hcyl a ha heq).symm
  -- cone-increase
  set c : ℝ := max cI (c₁ : ℝ) with hcdef
  have hc0 : 0 ≤ c := le_max_of_le_left hcI0
  have hc1 : c < 1 := max_lt hcI1 hc₁
  have hincI' : Causal.Flat.Cla.IsConeIncreasingOn c FI W' := hincI.mono (le_max_left _ _) hWε
  have hincσ : Causal.Flat.Cla.IsConeIncreasingOn c σ W' :=
    (isConeIncreasingOn_nullShift hc₁ hu hm hmn fun q hq => (hσ q (hWδ₁ hq)).2).mono
      (le_max_right _ _) le_rfl
  have hseg : ∀ a ∈ W', ∀ b ∈ W', ∀ t ∈ Icc (0 : ℝ) 1, a + t • (b - a) ∈ W' :=
    fun a _ b _ t ht => (convex_ball q₀ δ).add_smul_sub_mem ‹_› ‹_› ht
  have hscale : ∀ a b : Causal.Minkowski 2, c * ‖b.2 - a.2‖ < b.1 - a.1 → ∀ t : ℝ, 0 < t →
      c * ‖(a + t • (b - a)).2 - a.2‖ < (a + t • (b - a)).1 - a.1 := by
    intro a b hab t ht
    have h1 : (a + t • (b - a)).2 - a.2 = t • (b.2 - a.2) := by simp
    have h2 : (a + t • (b - a)).1 - a.1 = t * (b.1 - a.1) := by simp
    rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hscale' : ∀ a b : Causal.Minkowski 2, c * ‖b.2 - a.2‖ < b.1 - a.1 → ∀ t : ℝ, t < 1 →
      c * ‖b.2 - (a + t • (b - a)).2‖ < b.1 - (a + t • (b - a)).1 := by
    intro a b hab t ht
    have h1 : b.2 - (a + t • (b - a)).2 = (1 - t) • (b.2 - a.2) := by
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, sub_smul, one_smul, smul_sub]; abel
    have h2 : b.1 - (a + t • (b - a)).1 = (1 - t) * (b.1 - a.1) := by simp; ring
    have ht' : 0 < 1 - t := by linarith
    rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    nlinarith
  have hcseg : ∀ a b : Causal.Minkowski 2,
      Continuous fun t : ℝ => a + t • (b - a) := fun a b => by fun_prop
  have hinc : Causal.Flat.Cla.IsConeIncreasingOn c F W' := by
    intro a ha b hb hab
    have hcont : ContinuousOn (fun t : ℝ => rad (Φ (a + t • (b - a)))) (Icc 0 1) :=
      hrc.comp (hcseg a b).continuousOn fun t ht => hseg a ha b hb t ht
    by_cases hAa : rad (Φ a) ≤ D.R <;> by_cases hAb : rad (Φ b) ≤ D.R
    · simp only [F, if_pos hAa, if_pos hAb]; exact hincI' a ha b hb hab
    · simp only [F, if_pos hAa, if_neg hAb]
      push Not at hAb
      obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hcont
        ⟨by simpa using hAa, by simpa using hAb.le⟩
      set mp := a + t • (b - a) with hmp
      have hmpW : mp ∈ W' := hseg a ha b hb t ht
      have ht1 : t < 1 := by
        rcases ht.2.lt_or_eq with h | h
        · exact h
        · exfalso; simp only [h, one_smul, add_sub_cancel] at hteq; linarith
      have h1 : FI a ≤ FI mp := by
        rcases ht.1.lt_or_eq with h0 | h0
        · exact (hincI' a ha mp hmpW (hscale a b hab t h0)).le
        · simp [hmp, ← h0]
      have h2 : σ mp < σ b := hincσ mp hmpW b hb (hscale' a b hab t ht1)
      rw [← hcyl mp hmpW hteq] at h1
      linarith
    · simp only [F, if_neg hAa, if_pos hAb]
      push Not at hAa
      obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc' zero_le_one hcont
        ⟨by simpa using hAb, by simpa using hAa.le⟩
      set mp := a + t • (b - a) with hmp
      have hmpW : mp ∈ W' := hseg a ha b hb t ht
      have ht0 : 0 < t := by
        rcases ht.1.lt_or_eq with h | h
        · exact h
        · exfalso; simp only [← h, zero_smul, add_zero] at hteq; linarith
      have h1 : σ a < σ mp := hincσ a ha mp hmpW (hscale a b hab t ht0)
      have h2 : FI mp ≤ FI b := by
        rcases ht.2.lt_or_eq with h1' | h1'
        · exact (hincI' mp hmpW b hb (hscale' a b hab t h1')).le
        · simp [hmp, h1']
      rw [hcyl mp hmpW hteq] at h1
      linarith
    · simp only [F, if_neg hAa, if_neg hAb]; exact hincσ a ha b hb hab
  -- the zero set
  have hycusp : regVal M y ∈ D.cusp := by rw [hy]; exact ⟨paperInY x, ⟨x, hx, rfl⟩, rfl⟩
  have hyT : y ∈ Dat.sigmaStarReg :=
    show regVal M y ∈ Dat.sigmaStar from Or.inr (mem_iUnion.2 ⟨i, hycusp⟩)
  refine isSpacelikeLipschitzAt_of_coneZeroSet' g₁ Metric.isOpen_ball (Metric.mem_ball_self hδ0)
    hA4 hFc hc0 hc1 hinc ?_ hyT
  intro q hq
  have hregq := hreg q hq
  obtain ⟨hsrcq, heq⟩ := hz q hq hregq
  set z₀ : e0RegMFlat M := (⟨D.ψ (paperInY (Φ q)), hregq⟩ : E0LM.e0RegM M) with hz₀
  have hlhs : g₁⁻¹ • q ∈ e '' (Dat.sigmaStarReg ∩ e.source) ↔
      D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar := by
    constructor
    · rintro ⟨z, ⟨hzT, hzs⟩, hzp⟩
      have := e.injOn hzs hsrcq (hzp.trans heq.symm)
      rw [this] at hzT; exact hzT
    · intro h; exact ⟨z₀, ⟨h, hsrcq⟩, heq⟩
  rw [hlhs]
  have hf := (hA2 q hq).2.1
  have hr := (hA2 q hq).2.2.1
  have hWq := (hA2 q hq).2.2.2.1
  have hOthq := (hA2 q hq).2.2.2.2
  by_cases hA : rad (Φ q) ≤ D.R
  · simp only [F, if_pos hA]
    have hwsp : Φ q ∈ E0Spear.spear D.v D.R := ⟨hf.le, hA⟩
    have hspear : D.ψ (paperInY (Φ q)) ∈ D.spearSet := ⟨_, ⟨_, hwsp, rfl⟩, rfl⟩
    have hFq : FI q = height D.G (Φ q) := rfl
    constructor
    · intro hT
      have hc : D.ψ (paperInY (Φ q)) ∈ D.cusp := by
        rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hT, hspear⟩
      obtain ⟨_, ⟨x', hx', rfl⟩, hx'e⟩ := hc
      have hx'sp := D.graphSet_subset_spear hx'
      have hpw : paperInY x' = paperInY (Φ q) :=
        D.inj (D.spear_sub ⟨x', hx'sp, rfl⟩) hWq hx'e
      have : x' = Φ q := paperInY.injOn (by simp) (by simp) hpw
      rw [hFq, ← this]; exact hx'.2.2
    · intro h0
      exact Or.inr (mem_iUnion.2 ⟨i, ⟨_, ⟨Φ q, ⟨hr, hA, by rw [← hFq]; exact h0⟩, rfl⟩, rfl⟩⟩)
  · simp only [F, if_neg hA]
    push Not at hA
    have hnot : D.ψ (paperInY (Φ q)) ∉ ⋃ j, (Dat.D j).spearSet := by
      intro hm'
      obtain ⟨j, hj⟩ := mem_iUnion.1 hm'
      by_cases hji : j = i
      · subst hji
        obtain ⟨_, ⟨w'', hw'', rfl⟩, hw''e⟩ := hj
        have h1 : paperInY w'' = paperInY (Φ q) :=
          (Dat.D j).inj ((Dat.D j).spear_sub ⟨w'', hw'', rfl⟩) hWq hw''e
        have h2 : w'' = Φ q := paperInY.injOn (by simp) (by simp) h1
        rw [h2] at hw''
        linarith [hw''.2]
      · exact hOthq (mem_iUnion.2 ⟨⟨j, hji⟩, hj⟩)
    have hsigS : D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar ↔ D.ψ (paperInY (Φ q)) ∈ S := by
      constructor
      · intro h
        have h' : D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar \ ⋃ j, (Dat.D j).spearSet := ⟨h, hnot⟩
        rw [Dat.sigmaStar_diff] at h'; exact h'.1
      · intro h
        have h' : D.ψ (paperInY (Φ q)) ∈ S \ ⋃ j, (Dat.D j).spearSet := ⟨h, hnot⟩
        rw [← Dat.sigmaStar_diff] at h'; exact h'.1
    rw [hsigS]
    have hVOq := hA5 q hq
    have hchain : D.ψ (paperInY (Φ q)) ∈ S ↔ q ∈ Causal.Flat.graphOver U' u := by
      constructor
      · intro hS'
        have hmem : g₁⁻¹ • q ∈ Sc ∩ (O : Set (Causal.Minkowski 2)) :=
          ⟨⟨⟨z₀, ⟨hS', hsrcq⟩, heq⟩, hVOq.1⟩, hVOq.2⟩
        have : g₁ • g₁⁻¹ • q ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) :=
          Set.smul_mem_smul_set hmem
        rw [hgr, smul_inv_smul] at this; exact this.2
      · intro hgq
        have : q ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := by
          rw [hgr]; exact ⟨⟨g₁⁻¹ • q, hVOq.2, smul_inv_smul _ _⟩, hgq⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem] at this
        obtain ⟨⟨z, ⟨hzS, hzs⟩, hzp⟩, -⟩ := this.1
        have := e.injOn hzs hsrcq (hzp.trans heq.symm)
        rw [this] at hzS; exact hzS
    rw [hchain]
    obtain ⟨-, h1, h2⟩ := hσ q (hWδ₁ hq)
    constructor
    · intro hgq
      exact (nullShift_unique hc₁ hu hm hmn (s := 0) (by simpa using hgq.1) (by simpa using hgq.2)
        h1 h2).symm
    · intro h0
      rw [h0, zero_smul, sub_zero] at h1 h2
      exact ⟨h1, h2⟩

omit [SecondCountableTopology M] in
/-- `SpearSurgeryDatum.eventually_regChart` for an arbitrary chart of the flat atlas of `Reg M`
(compatibility, `Causal.exists_smul_eq_of_mem_gxGroupoid`). -/
theorem SpearSurgeryDatum.eventually_atlasChart {S : Set M} (D : SpearSurgeryDatum M S) {x : E0}
    (hx : x.2 ≠ 0) (hxW : paperInY x ∈ D.W)
    {e₀ : OpenPartialHomeomorph (e0RegMFlat M) (Causal.Minkowski 2)}
    (he₀ : e₀ ∈ atlas (Causal.Minkowski 2) (e0RegMFlat M)) {z : e0RegMFlat M}
    (hz : regVal M z = D.ψ (paperInY x)) (hze : z ∈ e₀.source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ w in 𝓝 x, ∀ z' : e0RegMFlat M,
      regVal M z' = D.ψ (paperInY w) → z' ∈ e₀.source ∧ e₀ z' = g • E0.chartMap x w := by
  obtain ⟨g, hg⟩ := D.eventually_regChart hx hxW (show E0LM.e0RegM M from z) hz
  obtain ⟨h, O, hzO, hOs, heq⟩ := Causal.exists_smul_eq_of_mem_gxGroupoid
    ((Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)).compatible
      (chart_mem_atlas (Causal.Minkowski 2) z) he₀) (mem_chart_source _ z) hze
  obtain ⟨O', hO', hOO'⟩ := isOpen_induced_iff.1 O.isOpen
  have hzO' : regVal M z ∈ O' := (Set.ext_iff.1 hOO' z).2 hzO
  have hψc : ContinuousAt (fun w : E0 => D.ψ (paperInY w)) x := by
    have hψq : ContinuousAt D.ψ (paperInY x) :=
      ((D.mor _ hxW).1).continuousAt (D.isOpen.mem_nhds hxW)
    exact ContinuousAt.comp (g := D.ψ) (f := fun w : E0 => paperInY w) hψq
      (paperInY.continuousAt (by rw [paperInY_source]; trivial))
  have hev : ∀ᶠ w in 𝓝 x, D.ψ (paperInY w) ∈ O' :=
    hψc.preimage_mem_nhds (hO'.mem_nhds (by rw [← hz]; exact hzO'))
  refine ⟨h * g, ?_⟩
  filter_upwards [hg, hev] with w ⟨hsrc, hch⟩ hwO z' hz'
  have hz'O : z' ∈ O := (Set.ext_iff.1 hOO' z').1 (show regVal M z' ∈ O' by rw [hz']; exact hwO)
  refine ⟨(hOs hz'O).2, ?_⟩
  rw [heq z' hz'O, regChart_apply_eq, hz', hch, mul_smul]

open Classical in
/-- **The clamped log-radius of the `i`-th cusp**, a function on `M`: `log (min r (R/2))` in the
spear, `log (R/2)` off it (B21 Lemma 2.8's `log r` estimate, cut below `R/2` so that the function
is locally constant near the rims). -/
noncomputable def SurgeryData.logRad {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι) (z : M) : ℝ :=
  if z ∈ (Dat.D i).spearSet then Real.log (min (rad ((Dat.D i).coord z)) ((Dat.D i).R / 2))
  else Real.log ((Dat.D i).R / 2)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- On a cusp, the coordinates are in the graph. -/
theorem SpearSurgeryDatum.coord_mem_graphSet {S : Set M} (D : SpearSurgeryDatum M S) {z : M}
    (hz : z ∈ D.cusp) : D.coord z ∈ graphSet D.G D.R := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  rw [D.coord_apply (D.graphSet_subset_spear hx)]; exact hx

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- On `Σ*` the clamped log-radius is at most `log (R/2)`. -/
theorem SurgeryData.logRad_le {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι) {z : M}
    (hz : z ∈ Dat.sigmaStar) : Dat.logRad i z ≤ Real.log ((Dat.D i).R / 2) := by
  unfold SurgeryData.logRad
  split_ifs with h
  · have hc : z ∈ (Dat.D i).cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hz, h⟩
    have hr := ((Dat.D i).coord_mem_graphSet hc).1
    exact Real.log_le_log (lt_min hr (by linarith [(Dat.D i).pos])) (min_le_right _ _)
  · exact le_rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- The spear coordinates are continuous along a curve through a point of `ψ(W)`. -/
theorem SpearSurgeryDatum.continuousAt_ginv_comp {S : Set M} (D : SpearSurgeryDatum M S)
    {X : Type*} [TopologicalSpace X] {c : X → M} {t : X} (hc : ContinuousAt c t) (hct : c t ∈ D.ψ '' D.W) :
    ContinuousAt (fun s => D.ginv (c s)) t := by
  have hgmor : E0Spear.IsE0Mor D.ginv (D.ψ '' D.W) :=
    Causal.CBG.liftPropOn_invFunOn D.isOpen D.mor D.inj
  have hVo : IsOpen (D.ψ '' D.W) := D.isOpen_image D.isOpen subset_rfl
  exact ((hgmor _ hct).continuousWithinAt.continuousAt (hVo.mem_nhds hct)).comp hc

omit [SecondCountableTopology M] in
/-- **The density bound behind Lemma 2.8, read on `Σ*`**: along a curve of `Σ*` with velocity `v`
in a flat chart, the derivative of the clamped log-radius is at most `√(ds²(v))` (where the clamp
is active it is locally constant or has a local maximum; in the cusp below `R/2`, `v` is tangent
to the height's level set and `δ ≥ 1/r²`, `sq_le_minkQ_of_tangent`). -/
theorem SurgeryData.abs_deriv_logRad_le {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    {c : ℝ → e0RegMFlat M} {t : ℝ} (hc : ContinuousAt c t)
    (hcS : ∀ᶠ s in 𝓝 t, c s ∈ Dat.sigmaStarReg)
    {e₀ : OpenPartialHomeomorph (e0RegMFlat M) (Causal.Minkowski 2)}
    (he₀ : e₀ ∈ atlas (Causal.Minkowski 2) (e0RegMFlat M)) (hct : c t ∈ e₀.source)
    {v : Causal.Minkowski 2} (hv : HasDerivAt (fun s => e₀ (c s)) v t) :
    |deriv (fun s => Dat.logRad i (regVal M (c s))) t| ≤ Real.sqrt (Causal.Flat.minkQ v) := by
  set D := Dat.D i with hD
  set f : ℝ → ℝ := fun s => Dat.logRad i (regVal M (c s)) with hf
  have hcM : ContinuousAt (fun s => regVal M (c s)) t :=
    continuous_subtype_val.continuousAt.comp hc
  have hR2 : 0 < D.R / 2 := by linarith [D.pos]
  have hconst : (∀ᶠ s in 𝓝 t, f s = Real.log (D.R / 2)) → |deriv f t| ≤ Real.sqrt (Causal.Flat.minkQ v) := by
    intro h
    have h' : f =ᶠ[𝓝 t] fun _ => Real.log (D.R / 2) := h
    rw [h'.deriv_eq, deriv_const, abs_zero]; exact Real.sqrt_nonneg _
  by_cases hin : regVal M (c t) ∈ D.spearSet
  swap
  · apply hconst
    filter_upwards [hcM.preimage_mem_nhds ((Dat.isClosed i).isOpen_compl.mem_nhds hin)] with s hs
    simp only [f, SurgeryData.logRad, if_neg (show regVal M (c s) ∉ (Dat.D i).spearSet from hs)]
    rfl
  have hcSt : regVal M (c t) ∈ Dat.sigmaStar := hcS.self_of_nhds
  have hcusp : regVal M (c t) ∈ D.cusp := by
    rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hcSt, hin⟩
  set x := D.coord (regVal M (c t)) with hxdef
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  have hxg : x ∈ graphSet D.G D.R := D.coord_mem_graphSet hcusp
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  have hctW : regVal M (c t) ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp hcM hctW
  have hgx : D.ginv (regVal M (c t)) = paperInY x := by
    rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv (regVal M (c t))) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun s => paperOfY (D.ginv (regVal M (c s)))) t :=
    ContinuousAt.comp (f := fun s => D.ginv (regVal M (c s))) hpo hgc
  have hwt : paperOfY (D.ginv (regVal M (c t))) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun s => paperOfY (D.ginv (regVal M (c s)))) (𝓝 t) (𝓝 x) :=
    hwt ▸ hwc.tendsto
  have hψW : ∀ᶠ s in 𝓝 t, regVal M (c s) ∈ D.ψ '' D.W :=
    hcM.preimage_mem_nhds ((D.isOpen_image D.isOpen subset_rfl).mem_nhds hctW)
  -- in a spear, the coordinates are `paperOfY ∘ ginv`
  have hcoord : ∀ z ∈ D.spearSet, D.coord z = paperOfY (D.ginv z) := fun z hz => by
    obtain ⟨hz1, hz2⟩ := D.coord_mem hz
    have := D.coord_eq_ginv hz1
    rwa [hz2] at this
  rcases lt_trichotomy (rad x) (D.R / 2) with hlt | heq | hgt
  · -- the cusp below `R/2`: the formula
    have hrx : 0 < rad x := hxg.1
    have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
    have hfx : D.v < fcoord x := by
      have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
        have := hxg.2.2; simp only [height, heightAt] at this; linarith
      have h2 := D.above (rad x, Complex.arg x.2) hrx hxg.2.1
      simp only [fcoord]; rw [h1]; linarith
    have hper := D.spacelike.periodic
    obtain ⟨g, hg⟩ := D.eventually_atlasChart hx0 hxW he₀ hxe.symm hct
    -- the open interior of the spear
    set B : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hB
    have hBo : IsOpen B :=
      (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
        (isOpen_lt continuous_rad continuous_const)
    have hxB : x ∈ B := ⟨hfx, by linarith [D.pos]⟩
    have hBsp : B ⊆ E0Spear.spear D.v D.R := fun w hw => ⟨hw.1.le, hw.2.le⟩
    have hev : ∀ᶠ s in 𝓝 t, regVal M (c s) ∈ D.ψ '' D.W ∧
        paperOfY (D.ginv (regVal M (c s))) ∈ B ∧
        rad (paperOfY (D.ginv (regVal M (c s)))) < D.R / 2 ∧ c s ∈ Dat.sigmaStarReg ∧
        ∀ z' : e0RegMFlat M, regVal M z' = D.ψ (paperInY (paperOfY (D.ginv (regVal M (c s))))) →
          z' ∈ e₀.source ∧ e₀ z' = g • E0.chartMap x (paperOfY (D.ginv (regVal M (c s)))) :=
      hψW.and ((hTw.eventually (hBo.mem_nhds hxB)).and
        ((hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Iio).mem_nhds hlt)).and
          (hcS.and (hTw.eventually hg))))
    have hrange : ∀ᶠ s in 𝓝 t, D.ginv (regVal M (c s)) ∈ range (Sum.inr : BTZE0 → E0Y) := by
      refine hgc.preimage_mem_nhds (isOpen_range_inr.mem_nhds ?_)
      rw [hgx, paperInY_apply]; exact mem_range_self _
    set p : ℝ → Causal.Minkowski 2 := fun s => e₀ (c s) with hp
    set β : Causal.Minkowski 2 → ℝ := fun q => (chartNull g q).2.1 with hβ
    set FI := chartHeight D.G g with hFI
    have hkey : ∀ᶠ s in 𝓝 t, f s = Real.log (β (p s)) ∧ FI (p s) = 0 := by
      filter_upwards [hev, hrange] with s ⟨hsW, hsB, hsr, hsS, hsch⟩ hsr'
      set w := paperOfY (D.ginv (regVal M (c s))) with hw
      have hpw : paperInY w = D.ginv (regVal M (c s)) := by
        obtain ⟨u, hu⟩ := hsr'
        rw [hw, ← hu, paperOfY_inr, paperInY_apply, Homeomorph.symm_apply_apply]
      have hzs : regVal M (c s) = D.ψ (paperInY w) := by
        rw [hpw]; exact (Function.invFunOn_eq hsW).symm
      obtain ⟨-, hes⟩ := hsch (c s) hzs
      have hwsp : w ∈ E0Spear.spear D.v D.R := hBsp hsB
      have hsp : regVal M (c s) ∈ D.spearSet := by rw [hzs]; exact ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
      have hcw : D.coord (regVal M (c s)) = w := by rw [hzs]; exact D.coord_apply hwsp
      have hβw : β (p s) = rad w := by
        simp only [β, p, hes, chartNull, inv_smul_smul, E0.chartMap, LinearEquiv.symm_apply_apply]
        rfl
      refine ⟨?_, ?_⟩
      · show Dat.logRad i (regVal M (c s)) = _
        rw [SurgeryData.logRad, if_pos (show regVal M (c s) ∈ (Dat.D i).spearSet from hsp),
          show (Dat.D i).coord (regVal M (c s)) = w from hcw, hβw,
          min_eq_left (show rad w ≤ (Dat.D i).R / 2 from hsr.le)]
      · have hcs : regVal M (c s) ∈ D.cusp := by
          rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hsS, hsp⟩
        have hwg : w ∈ graphSet D.G D.R := by rw [← hcw]; exact D.coord_mem_graphSet hcs
        simp only [FI, p, hes, chartHeight, nullHeight, inv_smul_smul, E0.chartMap,
          LinearEquiv.symm_apply_apply, locLift]
        rw [show Complex.arg x.2 + Complex.arg (w.2 / x.2) = angle x w from rfl,
          unlift_lift (polar_angle hx0 w)]
        exact hwg.2.2
    -- the values at `t`
    obtain ⟨-, het⟩ := hg.self_of_nhds (c t) hxe.symm
    set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
    have hpt : p t = g • nullToMink (btzPaperNull pp) := by
      simp only [p, het, E0.chartMap]; rfl
    have hβt : β (p t) = rad x := by
      simp only [β, hpt, chartNull, inv_smul_smul, LinearEquiv.symm_apply_apply]; rfl
    have hβF := hasFDerivAt_chartNull_rad g (p t)
    have hβd : HasDerivAt (fun s => β (p s)) (fderiv ℝ β (p t) v) t := by
      rw [hβF.fderiv]; exact hβF.comp_hasDerivAt t hv
    have hlog : HasDerivAt (fun s => Real.log (β (p s))) (fderiv ℝ β (p t) v / β (p t)) t :=
      hβd.log (by rw [hβt]; exact hrx.ne')
    have hfd : deriv f t = fderiv ℝ β (p t) v / rad x := by
      rw [← hβt]
      exact (hlog.congr_of_eventuallyEq (hkey.mono fun s hs => hs.1)).deriv
    -- `v` is tangent to the level set of `FI`
    have hpos : 0 < (chartNull g (p t)).2.1 := by
      have : β (p t) = (chartNull g (p t)).2.1 := rfl
      rw [← this, hβt]; exact hrx
    have hFId : HasFDerivAt FI (fderiv ℝ FI (p t)) (p t) :=
      (((contDiffOn_chartHeight hper D.smooth g).differentiableOn one_ne_zero).differentiableAt
        ((isOpen_chartPos g).mem_nhds hpos)).hasFDerivAt
    have h1 : HasDerivAt (fun s => FI (p s)) (fderiv ℝ FI (p t) v) t := hFId.comp_hasDerivAt t hv
    have h0 : HasDerivAt (fun s => FI (p s)) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (hkey.mono fun s hs => hs.2)
    have htan : fderiv ℝ FI (p t) v = 0 := h1.unique h0
    obtain ⟨L, hL, hδL⟩ := hδ (rad x, angle x x) hrx
    rw [hpt] at htan
    have hb := sq_le_minkQ_of_tangent hper D.smooth g (pp := pp) hrx hL hδL htan
    rw [hfd]
    rw [← hpt] at hb
    exact Real.abs_le_sqrt hb
  · -- `r = R/2`: a local maximum
    have hft : f t = Real.log (D.R / 2) := by
      show Dat.logRad i (regVal M (c t)) = _
      rw [SurgeryData.logRad, if_pos (show regVal M (c t) ∈ (Dat.D i).spearSet from hin),
        show (Dat.D i).coord (regVal M (c t)) = x from rfl, heq, min_self]
    have hmax : IsLocalMax f t := by
      filter_upwards [hcS] with s hs
      rw [hft]
      exact Dat.logRad_le i hs
    rw [hmax.deriv_eq_zero, abs_zero]; exact Real.sqrt_nonneg _
  · -- `r > R/2`: locally constant
    apply hconst
    have hev := hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt)
    filter_upwards [hev] with s hs
    simp only [f, SurgeryData.logRad]
    split_ifs with h
    · rw [hcoord _ h, min_eq_right (le_of_lt hs)]
    · rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Where the clamp is active, `logRad` is locally constant** (off the closed spear, or in the
spear above `r = R/2`). -/
theorem SurgeryData.eventually_logRad_const {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι)
    {z₀ : M} (h : z₀ ∉ (Dat.D i).spearSet ∨
      (z₀ ∈ (Dat.D i).spearSet ∧ (Dat.D i).R / 2 < rad ((Dat.D i).coord z₀))) :
    ∀ᶠ z in 𝓝 z₀, Dat.logRad i z = Real.log ((Dat.D i).R / 2) := by
  set D := Dat.D i with hD
  rcases h with hout | ⟨hin, hgt⟩
  · filter_upwards [(Dat.isClosed i).isOpen_compl.mem_nhds hout] with z hz
    simp only [SurgeryData.logRad, if_neg (show z ∉ (Dat.D i).spearSet from hz)]
    rfl
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  set x := D.coord z₀ with hxdef
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  have hctW : z₀ ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp (c := fun z : M => z) continuousAt_id hctW
  have hgx : D.ginv z₀ = paperInY x := by rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv z₀) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun z => paperOfY (D.ginv z)) z₀ :=
    ContinuousAt.comp (f := fun z => D.ginv z) hpo hgc
  have hwt : paperOfY (D.ginv z₀) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun z => paperOfY (D.ginv z)) (𝓝 z₀) (𝓝 x) := hwt ▸ hwc.tendsto
  have hcoord : ∀ z ∈ D.spearSet, D.coord z = paperOfY (D.ginv z) := fun z hz => by
    obtain ⟨hz1, hz2⟩ := D.coord_mem hz
    have := D.coord_eq_ginv hz1
    rwa [hz2] at this
  filter_upwards [hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt)]
    with z hz
  unfold SurgeryData.logRad
  split_ifs with h
  · rw [hcoord _ h, min_eq_right (le_of_lt hz)]
  · rfl

omit [SecondCountableTopology M] in
/-- **Below the clamp, `logRad` is `log (min r (R/2))` with `r` affine in the chart** at a point of
the open spear interior off the axis. -/
theorem SurgeryData.eventually_logRad_formula {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι)
    {z₀ : e0RegMFlat M} (hin : regVal M z₀ ∈ (Dat.D i).spearSet)
    (hr0 : 0 < rad ((Dat.D i).coord (regVal M z₀)))
    (hrR : rad ((Dat.D i).coord (regVal M z₀)) < (Dat.D i).R)
    (hfv : (Dat.D i).v < fcoord ((Dat.D i).coord (regVal M z₀))) :
    ∃ g : Causal.Flat.isom 2, (∀ᶠ z in 𝓝 z₀, z ∈ (chartAt (Causal.Minkowski 2) z₀).source ∧
      Dat.logRad i (regVal M z) =
        Real.log (min (chartNull g (chartAt (Causal.Minkowski 2) z₀ z)).2.1 ((Dat.D i).R / 2))) ∧
      (chartNull g (chartAt (Causal.Minkowski 2) z₀ z₀)).2.1 = rad ((Dat.D i).coord (regVal M z₀)) := by
  set D := Dat.D i with hD
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  set x := D.coord (regVal M z₀) with hxdef
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hr0
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_atlasChart hx0 hxW (chart_mem_atlas (Causal.Minkowski 2) z₀)
    hxe.symm (mem_chart_source _ z₀)
  have hcM : ContinuousAt (fun z : e0RegMFlat M => regVal M z) z₀ :=
    continuous_subtype_val.continuousAt
  have hctW : regVal M z₀ ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp (c := fun z : e0RegMFlat M => regVal M z) hcM hctW
  have hgx : D.ginv (regVal M z₀) = paperInY x := by rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv (regVal M z₀)) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun z : e0RegMFlat M => paperOfY (D.ginv (regVal M z))) z₀ :=
    ContinuousAt.comp (f := fun z : e0RegMFlat M => D.ginv (regVal M z)) hpo hgc
  have hwt : paperOfY (D.ginv (regVal M z₀)) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun z : e0RegMFlat M => paperOfY (D.ginv (regVal M z))) (𝓝 z₀) (𝓝 x) :=
    hwt ▸ hwc.tendsto
  set B : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hB
  have hBo : IsOpen B :=
    (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
      (isOpen_lt continuous_rad continuous_const)
  have hBsp : B ⊆ E0Spear.spear D.v D.R := fun w hw => ⟨hw.1.le, hw.2.le⟩
  have hψW : ∀ᶠ z in 𝓝 z₀, regVal M z ∈ D.ψ '' D.W :=
    hcM.preimage_mem_nhds ((D.isOpen_image D.isOpen subset_rfl).mem_nhds hctW)
  have hrange : ∀ᶠ z in 𝓝 z₀, D.ginv (regVal M z) ∈ range (Sum.inr : BTZE0 → E0Y) := by
    refine hgc.preimage_mem_nhds (isOpen_range_inr.mem_nhds ?_)
    rw [hgx, paperInY_apply]; exact mem_range_self _
  have hchart : ∀ z : e0RegMFlat M, chartAt (Causal.Minkowski 2) z₀ z ∈
      {p | True} := fun _ => trivial
  have hval : ∀ w : E0, (chartNull g (g • E0.chartMap x w)).2.1 = rad w := by
    intro w; simp only [chartNull, inv_smul_smul, E0.chartMap, LinearEquiv.symm_apply_apply]; rfl
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [hψW, hrange, hTw.eventually (hBo.mem_nhds ⟨hfv, hrR⟩), hTw.eventually hg]
      with z hzW hzr hzB hzch
    set w := paperOfY (D.ginv (regVal M z)) with hw
    have hpw : paperInY w = D.ginv (regVal M z) := by
      obtain ⟨u, hu⟩ := hzr
      rw [hw, ← hu, paperOfY_inr, paperInY_apply, Homeomorph.symm_apply_apply]
    have hzs : regVal M z = D.ψ (paperInY w) := by rw [hpw]; exact (Function.invFunOn_eq hzW).symm
    obtain ⟨hsrc, hes⟩ := hzch z hzs
    have hwsp : w ∈ E0Spear.spear D.v D.R := hBsp hzB
    have hsp : regVal M z ∈ D.spearSet := by rw [hzs]; exact ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
    have hcw : D.coord (regVal M z) = w := by rw [hzs]; exact D.coord_apply hwsp
    refine ⟨hsrc, ?_⟩
    rw [SurgeryData.logRad, if_pos (show regVal M z ∈ (Dat.D i).spearSet from hsp),
      show (Dat.D i).coord (regVal M z) = w from hcw, hes, hval]
  · obtain ⟨-, het⟩ := hg.self_of_nhds z₀ hxe.symm
    rw [het, hval]

omit [SecondCountableTopology M] in
/-- **The clamped log-radius is locally Lipschitz along a path of `Σ*` Lipschitz in charts.** -/
theorem SurgeryData.exists_lipschitzOnWith_logRad {S : Set M} (Dat : SurgeryData M S) (i : Dat.ι)
    {a b : Dat.sigmaStarReg} (γ : Path a b)
    (hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ K : NNReal, LipschitzOnWith K
      (fun t => Dat.logRad i (regVal M ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M)))
      (Icc (t₀ - ε) (t₀ + ε)) := by
  set D := Dat.D i with hD
  set c : ℝ → e0RegMFlat M := fun t => ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M) with hc
  have hcc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  set f : ℝ → ℝ := fun t => Dat.logRad i (regVal M (c t)) with hf
  set z₀ := c t₀ with hz₀
  have hz₀S : regVal M z₀ ∈ Dat.sigmaStar := (γ.extend t₀).2
  by_cases hconst : regVal M z₀ ∉ D.spearSet ∨ (regVal M z₀ ∈ D.spearSet ∧ D.R / 2 < rad (D.coord (regVal M z₀)))
  · have hev := Dat.eventually_logRad_const i hconst
    have hev' : ∀ᶠ t in 𝓝 t₀, f t = Real.log (D.R / 2) :=
      ((continuous_subtype_val.comp hcc).continuousAt (x := t₀)).eventually hev
    obtain ⟨ε, hε, hI⟩ := Causal.Flat.exists_Icc_subset_of_eventually hev'
    refine ⟨ε, hε, 0, fun s hs s' hs' => ?_⟩
    show edist (f s) (f s') ≤ _
    rw [hI s hs, hI s' hs', edist_self]; exact bot_le
  push Not at hconst
  obtain ⟨hin, hle⟩ := hconst
  have hle := hle hin
  have hcusp : regVal M z₀ ∈ D.cusp := by
    rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hz₀S, hin⟩
  have hxg := D.coord_mem_graphSet hcusp
  set x := D.coord (regVal M z₀) with hxdef
  have hrx : 0 < rad x := hxg.1
  have hfv : D.v < fcoord x := by
    have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
      have := hxg.2.2; simp only [height, heightAt] at this; linarith
    have h2 := D.above (rad x, Complex.arg x.2) hrx hxg.2.1
    simp only [fcoord]; rw [h1]; linarith
  obtain ⟨g, hg, hg0⟩ := Dat.eventually_logRad_formula i hin hrx (by linarith [D.pos]) hfv
  set e₀ := chartAt (Causal.Minkowski 2) z₀ with he₀
  set β : Causal.Minkowski 2 → ℝ := fun q => (chartNull g q).2.1 with hβ
  obtain ⟨Kβ, hKβ⟩ := lipschitzWith_chartNull_rad g
  -- the lower bound on `β`
  have hβc : ContinuousAt (fun t => β (e₀ (c t))) t₀ :=
    (hKβ.continuous.continuousAt).comp ((e₀.continuousAt (mem_chart_source _ z₀)).comp
      hcc.continuousAt)
  set m := rad x / 2 with hm
  have hm0 : 0 < m := by positivity
  have hβ0 : β (e₀ (c t₀)) = rad x := hg0
  have hev : ∀ᶠ t in 𝓝 t₀, (c t ∈ e₀.source ∧ Dat.logRad i (regVal M (c t)) =
      Real.log (min (β (e₀ (c t))) (D.R / 2))) ∧ m < β (e₀ (c t)) :=
    (hcc.continuousAt.eventually hg).and (hβc.eventually (lt_mem_nhds (show m < β (e₀ (c t₀)) by rw [hβ0]; linarith)))
  obtain ⟨ε₂, hε₂, hI₂⟩ := Causal.Flat.exists_Icc_subset_of_eventually hev
  obtain ⟨ε₁, hε₁, K₁, hK₁⟩ := hL t₀
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsub₁ : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc (t₀ - ε₁) (t₀ + ε₁) :=
    Icc_subset_Icc (by linarith [min_le_left ε₁ ε₂]) (by linarith [min_le_left ε₁ ε₂])
  have hsub₂ : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc (t₀ - ε₂) (t₀ + ε₂) :=
    Icc_subset_Icc (by linarith [min_le_right ε₁ ε₂]) (by linarith [min_le_right ε₁ ε₂])
  have hR2m : m ≤ D.R / 2 := by
    have := hxg.2.1; linarith
  refine ⟨ε, hε, ⟨1 / m, by positivity⟩ * Kβ * K₁, LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_⟩
  obtain ⟨⟨-, hfs⟩, hms⟩ := hI₂ s (hsub₂ hs)
  obtain ⟨⟨-, hfs'⟩, hms'⟩ := hI₂ s' (hsub₂ hs')
  have hchart : dist (e₀ (c s)) (e₀ (c s')) ≤ K₁ * dist s s' :=
    hK₁.dist_le_mul s (hsub₁ hs) s' (hsub₁ hs')
  have hβL : dist (β (e₀ (c s))) (β (e₀ (c s'))) ≤ Kβ * dist (e₀ (c s)) (e₀ (c s')) :=
    hKβ.dist_le_mul _ _
  have hmin : |min (β (e₀ (c s))) (D.R / 2) - min (β (e₀ (c s'))) (D.R / 2)| ≤
      |β (e₀ (c s)) - β (e₀ (c s'))| := abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
  have hlog := abs_log_sub_log_le hm0 (le_min hms.le hR2m) (le_min hms'.le hR2m)
  show dist (f s) (f s') ≤ _
  rw [Real.dist_eq]
  simp only [f, hfs, hfs']
  rw [Real.dist_eq] at hβL
  push_cast
  calc |Real.log (min (β (e₀ (c s))) (D.R / 2)) - Real.log (min (β (e₀ (c s'))) (D.R / 2))|
      ≤ (1 / m) * |β (e₀ (c s)) - β (e₀ (c s'))| :=
        hlog.trans (mul_le_mul_of_nonneg_left hmin (by positivity))
    _ ≤ (1 / m) * (Kβ * (K₁ * dist s s')) := by
        refine mul_le_mul_of_nonneg_left (hβL.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hchart Kβ.2
    _ = 1 / m * Kβ * K₁ * dist s s' := by ring

omit [SecondCountableTopology M] in
/-- **The clamped log-radius is `1`-Lipschitz for the induced length of `Σ*`** (B21 Lemma 2.8's
`log r` estimate, l.799–806, on the glued surface): along every path Lipschitz in charts, its
derivative is a.e. at most the density (`abs_deriv_logRad_le`, Rademacher in a chart near each
time), and `le_localLength_of_lipschitzOnWith` integrates. -/
theorem SurgeryData.ofReal_abs_logRad_sub_le_edist {S : Set M} (Dat : SurgeryData M S)
    (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    (a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) :
    ENNReal.ofReal |Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype b : Dat.sigmaStarReg) : e0RegMFlat M)) -
      Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M))| ≤
      edist a b := by
  change _ ≤ ⨅ γ : Path (Causal.Flat.LocalLengthSpace.toSpace a)
    (Causal.Flat.LocalLengthSpace.toSpace b),
    Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ
  refine le_iInf fun γ => ?_
  by_cases hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend
  swap
  · rw [Causal.Flat.pathLength_of_not_isLocLip _ hL]; exact le_top
  rw [Causal.Flat.pathLength_of_isLocLip _ hL]
  set c : ℝ → e0RegMFlat M := fun t => ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M) with hc
  have hcc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  set f : ℝ → ℝ := fun t => Dat.logRad i (regVal M (c t)) with hf
  have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) f := by
    intro t₀ _
    obtain ⟨ε, hε, K, hK⟩ := Dat.exists_lipschitzOnWith_logRad i γ hL t₀
    exact ⟨K, Icc (t₀ - ε) (t₀ + ε),
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith)), hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hd : ∀ᵐ t, t ∈ Ioc (0 : ℝ) 1 → ENNReal.ofReal (1 * |deriv f t|) ≤
      Causal.Flat.localDensity (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend t := by
    refine ae_of_local fun t₀ => ?_
    set e₀ := chartAt (Causal.Minkowski 2) (c t₀) with he₀
    obtain ⟨ε₁, hε₁, K₁, hK₁⟩ := hL t₀
    have hsrc : ∀ᶠ s in 𝓝 t₀, c s ∈ e₀.source :=
      hcc.continuousAt.preimage_mem_nhds (e₀.open_source.mem_nhds (mem_chart_source _ _))
    obtain ⟨ε₂, hε₂, hI₂⟩ := Causal.Flat.exists_Icc_subset_of_eventually hsrc
    set ε := min ε₁ ε₂ with hεdef
    have hε : 0 < ε := lt_min hε₁ hε₂
    refine ⟨ε, hε, ?_⟩
    have hK₁' : LipschitzOnWith K₁ (fun s => e₀ (c s)) (Icc (t₀ - ε) (t₀ + ε)) :=
      hK₁.mono (Icc_subset_Icc (by linarith [min_le_left ε₁ ε₂]) (by linarith [min_le_left ε₁ ε₂]))
    filter_upwards [hK₁'.ae_differentiableWithinAt_of_mem] with u hu huI _
    have huI' : u ∈ Icc (t₀ - ε) (t₀ + ε) := Ioo_subset_Icc_self huI
    have hdiff : DifferentiableAt ℝ (fun s => e₀ (c s)) u :=
      (hu huI').differentiableAt (Icc_mem_nhds huI.1 huI.2)
    have hus : c u ∈ e₀.source := hI₂ u
      (Icc_subset_Icc (by linarith [min_le_right ε₁ ε₂]) (by linarith [min_le_right ε₁ ε₂]) huI')
    rw [one_mul, Causal.Flat.localDensity_chartSys_eq (c := γ.extend)
      γ.continuous_extend.continuousAt (chart_mem_atlas _ _) hus]
    exact ENNReal.ofReal_le_ofReal (Dat.abs_deriv_logRad_le i hδ hcc.continuousAt
      (Eventually.of_forall fun s => (γ.extend s).2) (chart_mem_atlas _ _) hus hdiff.hasDerivAt)
  have key := le_localLength_of_lipschitzOnWith (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend
    (f := f) zero_le_one zero_le_one hK hd
  simp only [f, c, Path.extend_zero, Path.extend_one, one_mul] at key
  exact key

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The graph of `G` over the annulus `ρ ≤ r ≤ R` is compact. -/
theorem SpearSurgeryDatum.isCompact_annulusGraph {S : Set M} (D : SpearSurgeryDatum M S) {ρ : ℝ}
    (hρ : 0 < ρ) : IsCompact ((fun q : ℝ × ℝ => ((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc ρ D.R ×ˢ Icc (-π) π)) := by
  refine (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn ?_
  refine ContinuousOn.prodMk ?_ (by fun_prop)
  exact D.smooth.continuousOn.mono fun q hq => hρ.trans_le hq.1.1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem SpearSurgeryDatum.annulusGraph_subset {S : Set M} (D : SpearSurgeryDatum M S) {ρ : ℝ}
    (hρ : 0 < ρ) : (fun q : ℝ × ℝ => ((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc ρ D.R ×ˢ Icc (-π) π) ⊆ graphSet D.G D.R := by
  rintro _ ⟨q, hq, rfl⟩
  have hr : rad (((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) = q.1 :=
    norm_rimPoint (hρ.le.trans hq.1.1) q.2
  have hpol : Polar (((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) q.2 := by
    show (q.1 : ℂ) * Complex.exp (q.2 * Complex.I) = _
    rw [hr]
  refine ⟨by rw [hr]; exact hρ.trans_le hq.1.1, by rw [hr]; exact hq.1.2, ?_⟩
  rw [← heightAt_eq_height D.spacelike.periodic hpol (by rw [hr]; exact hρ.trans_le hq.1.1)]
  simp only [heightAt, hr, sub_self]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem SpearSurgeryDatum.mem_annulusGraph {S : Set M} (D : SpearSurgeryDatum M S) {ρ : ℝ}
    {w : E0} (hw : w ∈ graphSet D.G D.R) (hρw : ρ ≤ rad w) :
    w ∈ (fun q : ℝ × ℝ => ((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc ρ D.R ×ˢ Icc (-π) π) := by
  refine ⟨(rad w, Complex.arg w.2), ⟨⟨hρw, hw.2.1⟩, ⟨(Complex.neg_pi_lt_arg _).le,
    Complex.arg_le_pi _⟩⟩, Prod.ext ?_ (polar_arg w).symm⟩
  have := hw.2.2; simp only [height, heightAt] at this; simp only; linarith

/-- **(G5) from the `log r` estimate** (B21 l.1093 « `Σ*` is metrically complete »): a Cauchy
sequence of `Σ*` has bounded clamped log-radii (`ofReal_abs_logRad_sub_le_edist`), so it stays
in `T = (S ∖ spears) ∪ ⋃ ψᵢ(graph of Gᵢ over ρᵢ ≤ r ≤ Rᵢ)`, which is compact (closed: the limit
points of `S ∖ spears` on a spear are on the rim, interior points of the spear being excluded by an
open neighbourhood); a subsequence converges in `M`, hence in `Σ*` with its subspace topology,
hence for the induced length (`Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm`). -/
theorem SurgeryData.completeSpace_sigmaStar_of_delta {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S)
    (hδ : ∀ (i : Dat.ι) (q : ℝ × ℝ), 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (Dat.D i).G L q ∧ 1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    (hL : Causal.Flat.IsSpacelikeLipschitz 2 Dat.sigmaStarReg) :
    CompleteSpace (Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) := by
  classical
  haveI := Dat.finite
  haveI : Fintype Dat.ι := Fintype.ofFinite _
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hcont := Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm hL
  set X := Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg
  set pt : X → M := fun a =>
    regVal M ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M) with hpt
  have hptS : ∀ a, pt a ∈ Dat.sigmaStar := fun a => (Causal.Flat.InducedLengthSpace.toSubtype a).2
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- the clamped log-radii are bounded below
  have hb : ∀ i, ∃ N, ∀ n ≥ N, Dat.logRad i (pt (u N)) - 1 < Dat.logRad i (pt (u n)) := by
    intro i
    obtain ⟨N, hN⟩ := (EMetric.cauchySeq_iff'.1 hu) 1 one_pos
    refine ⟨N, fun n hn => ?_⟩
    have h1 := Dat.ofReal_abs_logRad_sub_le_edist i (hδ i) (u N) (u n)
    have h2 : edist (u N) (u n) < 1 := by rw [edist_comm]; exact hN n hn
    have h3 := h1.trans_lt h2
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at h3
    have := abs_lt.1 h3
    simp only [pt] at this ⊢
    linarith
  choose N hN using hb
  set N₀ := Finset.univ.sup N with hN₀
  set ρ : Dat.ι → ℝ := fun i => Real.exp (Dat.logRad i (pt (u (N i))) - 1) with hρdef
  have hρ0 : ∀ i, 0 < ρ i := fun i => Real.exp_pos _
  have hρR : ∀ i, ρ i ≤ (Dat.D i).R := by
    intro i
    have h1 := Dat.logRad_le i (hptS (u (N i)))
    have h2 : ρ i ≤ Real.exp (Real.log ((Dat.D i).R / 2)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_log (by linarith [(Dat.D i).pos])] at h2
    linarith [(Dat.D i).pos]
  have hρu : ∀ i, ∀ n ≥ N₀, pt (u n) ∈ (Dat.D i).spearSet →
      ρ i ≤ rad ((Dat.D i).coord (pt (u n))) := by
    intro i n hn hin
    have hn' : N i ≤ n := (Finset.le_sup (Finset.mem_univ i)).trans hn
    have h1 := hN i n hn'
    have hc : pt (u n) ∈ (Dat.D i).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hptS _, hin⟩
    have hr0 := ((Dat.D i).coord_mem_graphSet hc).1
    have hmin0 : 0 < min (rad ((Dat.D i).coord (pt (u n)))) ((Dat.D i).R / 2) :=
      lt_min hr0 (by linarith [(Dat.D i).pos])
    have h2 : Dat.logRad i (pt (u n)) =
        Real.log (min (rad ((Dat.D i).coord (pt (u n)))) ((Dat.D i).R / 2)) := by
      rw [SurgeryData.logRad, if_pos hin]
    rw [h2] at h1
    have h3 := (Real.lt_log_iff_exp_lt hmin0).1 h1
    exact h3.le.trans (min_le_left _ _)
  -- the compact set `T`
  set K : Dat.ι → Set E0 := fun i =>
    (fun q : ℝ × ℝ => (((Dat.D i).G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc (ρ i) (Dat.D i).R ×ˢ Icc (-π) π) with hKdef
  set U := ⋃ i, (Dat.D i).spearSet with hU
  set B := ⋃ i, (Dat.D i).ψ '' (paperInY '' K i) with hB
  set T : Set M := (S \ U) ∪ B with hT
  have hψc : ∀ i, ContinuousOn (fun x : E0 => (Dat.D i).ψ (paperInY x)) (E0Spear.spear (Dat.D i).v (Dat.D i).R) := by
    intro i x hx
    have hxW : paperInY x ∈ (Dat.D i).W := (Dat.D i).spear_sub ⟨x, hx, rfl⟩
    exact (((Dat.D i).mor _ hxW).1.continuousAt ((Dat.D i).isOpen.mem_nhds hxW)).comp
      E0Spear.continuous_paperInY.continuousAt |>.continuousWithinAt
  have hBi : ∀ i, IsCompact ((Dat.D i).ψ '' (paperInY '' K i)) := by
    intro i
    rw [image_image]
    exact ((Dat.D i).isCompact_annulusGraph (hρ0 i)).image_of_continuousOn
      ((hψc i).mono (((Dat.D i).annulusGraph_subset (hρ0 i)).trans (Dat.D i).graphSet_subset_spear))
  have hBc : IsCompact B := isCompact_iUnion hBi
  have hBsub : B ⊆ Dat.sigmaStar := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hi
    exact Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, (Dat.D i).annulusGraph_subset (hρ0 i) hw, rfl⟩, rfl⟩⟩)
  have hTS : T ⊆ Dat.sigmaStar := union_subset (fun z hz => Or.inl hz) hBsub
  have hSc : IsClosed S := hS.compact.isClosed
  have hUc : IsClosed U := isClosed_iUnion_of_finite Dat.isClosed
  have hclos : closure (S \ U) ⊆ T := by
    intro z hz
    have hzS : z ∈ S := closure_minimal sdiff_subset hSc hz
    by_cases hzU : z ∈ U
    swap
    · exact Or.inl ⟨hzS, hzU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hzU
    set D := Dat.D i with hD
    obtain ⟨hxsp, hxe⟩ := D.coord_mem hi
    set x := D.coord z with hxdef
    have hx1 : x.1 = D.τS x.2 := (D.graph x hxsp).1 (by rw [hxe]; exact hzS)
    have hsh := D.shaft x.2 hxsp.2
    rcases hxsp.2.lt_or_eq with hlt | heq
    · exfalso
      set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
      have hOo : IsOpen O :=
        (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
          (isOpen_lt continuous_rad continuous_const)
      have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ => hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
      have hOo' : IsOpen (D.ψ '' (paperInY '' O)) :=
        D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW
      have hxO : x ∈ O := ⟨by simp only [fcoord]; rw [hx1]; linarith [rad_nonneg x], hlt⟩
      have hzO : z ∈ D.ψ '' (paperInY '' O) := ⟨paperInY x, ⟨x, hxO, rfl⟩, hxe⟩
      obtain ⟨z', hz'O, hz'S, hz'U⟩ := mem_closure_iff.1 hz _ hOo' hzO
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz'O
      exact hz'U (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩⟩)
    · have hxg : x ∈ graphSet D.G D.R := by
        refine ⟨by rw [heq]; exact D.pos, heq.le, ?_⟩
        simp only [height, heightAt]
        rw [rim_value D.rim heq, hx1, sub_self]
      refine Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY x, ⟨x, D.mem_annulusGraph hxg (by rw [heq]; exact hρR i), rfl⟩, hxe⟩⟩)
  have hTcl : IsClosed T := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union]
    exact union_subset hclos ((hBc.isClosed.closure_eq).le.trans subset_union_right)
  have hTc : IsCompact T :=
    (hS.compact.union hBc).of_isClosed_subset hTcl (union_subset_union sdiff_subset le_rfl)
  have hTu : ∀ n ≥ N₀, pt (u n) ∈ T := by
    intro n hn
    rcases hptS (u n) with h | h
    · exact Or.inl h
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      have hin : pt (u n) ∈ (Dat.D i).spearSet := (Dat.D i).cusp_subset_spearSet hi
      obtain ⟨-, hxe⟩ := (Dat.D i).coord_mem hin
      refine Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY _, ⟨_, (Dat.D i).mem_annulusGraph
        ((Dat.D i).coord_mem_graphSet hi) (hρu i n hn hin), rfl⟩, hxe⟩⟩)
  -- a convergent subsequence
  obtain ⟨z, hzT, φ, hφ, hlim⟩ := hTc.tendsto_subseq (x := fun k => pt (u (N₀ + k)))
    (fun k => hTu _ (Nat.le_add_right _ _))
  have hzreg : z ∈ E0LM.e0RegM M := Dat.sigmaStar_subset_regM (hTS hzT)
  set z' : e0RegMFlat M := (⟨z, hzreg⟩ : E0LM.e0RegM M) with hz'
  have hz'S : z' ∈ Dat.sigmaStarReg := hTS hzT
  set ζ : ℕ → e0RegMFlat M := fun k =>
    ((Causal.Flat.InducedLengthSpace.toSubtype (u (N₀ + φ k)) : Dat.sigmaStarReg) : e0RegMFlat M)
    with hζ
  have hind : Topology.IsInducing (regVal M) := Topology.IsInducing.subtypeVal
  have h1 : Tendsto ζ atTop (𝓝 z') := hind.tendsto_nhds_iff.2 hlim
  have hlimS : Tendsto (fun k => (Causal.Flat.InducedLengthSpace.toSubtype (u (N₀ + φ k)) :
      Dat.sigmaStarReg)) atTop (𝓝 ⟨z', hz'S⟩) := by
    rw [tendsto_subtype_rng]
    exact h1
  have hlimX : Tendsto (fun k => u (N₀ + φ k)) atTop
      (𝓝 (Causal.Flat.InducedLengthSpace.toSubtype.symm ⟨z', hz'S⟩)) :=
    (hcont.tendsto _).comp hlimS
  exact ⟨_, tendsto_nhds_of_cauchySeq_of_subseq hu
    (Filter.tendsto_atTop_mono (fun k => Nat.le_add_left (φ k) N₀) hφ.tendsto_atTop) hlimX⟩

end CuspInterior

/-! ### §5g (G3) — the sides of `Σ*` in `Reg M` (WP-46e fixer)

`Σ*` cuts `Reg M` into a **future side** `futSide` (`J⁺(S)` outside the spears, `height G ≥ 0`
inside) and a **past side** `pastSide` (`J⁻(S)` outside, `height G ≤ 0` inside): they cover
`Reg M` (`mem_sides_of_notMem_S0`), meet exactly along `Σ*` (`mem_sigmaStar_of_sides`), are
closed in `Reg M` (`closure_futSide_subset`: a frontier point of a spear in `J⁺(S)` is on the shaft
above `C = C*`, the head lying below `S`), propagate along causal curves (`futSide_of_le`,
`pastSide_of_le`: the chart reading `eventually_le_coord` and Lemma 2.7's monotone height inside a
spear; `J^±(S)` outside), and every inextensible causal curve of `Reg M` meets both
(`exists_futSide`, `exists_pastSide`: Remark 2.12 in each spear, then a compact-diamond limit
against inextensibility, a BTZ limit being inside a spear by `exists_open_of_BTZ`). A causal curve
inside `Σ*` is constant (`eq_of_forall_mem_sigmaStar`, `Σ*` acausal: `S` outside the spears,
the strictly monotone height inside). -/

section CauchyG3

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

namespace SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- A vertical segment of a spear is causal in `M`. -/
theorem le_vert {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) {τ' : ℝ} (hτ : x.1 ≤ τ') :
    (E0CBG.CE M).le ⊤ (D.ψ (paperInY x)) (D.ψ (paperInY ((τ', x.2) : E0))) := by
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  set O : TopologicalSpace.Opens E0 := ⟨paperInY ⁻¹' D.W, hPo⟩
  have hSO : E0Spear.spear D.v D.R ⊆ O := fun x hx => D.spear_sub ⟨x, hx, rfl⟩
  have hy : ((τ', x.2) : E0) ∈ E0Spear.spear D.v D.R := by
    refine ⟨?_, hx.2⟩
    have := hx.1
    simp only [fcoord, rad] at this ⊢
    linarith
  have hxx : x = ((x.1, x.2) : E0) := rfl
  have h := E0Spear.le_of_isE0Mor_paper D.isOpen D.mor (U := O) subset_rfl
    (E0Spear.le_of_le_top_of_mem_spear hSO (by rw [← hxx]; exact hx) hy
      (E0Spear.le_vertical_top (z := x.2) hτ))
  rwa [← hxx] at h

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The point of `S` over a point of the closed disc. -/
theorem graphPt_mem {z : ℂ} (hz : ‖z‖ ≤ D.R) :
    ((D.τS z, z) : E0) ∈ E0Spear.spear D.v D.R ∧ D.ψ (paperInY ((D.τS z, z) : E0)) ∈ S := by
  have hsp : ((D.τS z, z) : E0) ∈ E0Spear.spear D.v D.R := by
    refine ⟨?_, hz⟩
    have := D.shaft z hz
    simp only [fcoord, rad]
    linarith
  exact ⟨hsp, (D.graph _ hsp).2 rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- A point of the spear below the graph of `S` is in `J⁻(S)`. -/
theorem mem_Jminus_of_le_τS {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) (hτ : x.1 ≤ D.τS x.2) :
    D.ψ (paperInY x) ∈ (E0CBG.CE M).Jminus ⊤ S :=
  ⟨_, (D.graphPt_mem hx.2).2, D.le_vert hx hτ⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- A point of the spear above the graph of `S` is in `J⁺(S)`. -/
theorem mem_Jplus_of_τS_le {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) (hτ : D.τS x.2 ≤ x.1) :
    D.ψ (paperInY x) ∈ (E0CBG.CE M).Jplus ⊤ S := by
  obtain ⟨hsp, hS⟩ := D.graphPt_mem hx.2
  refine ⟨_, hS, ?_⟩
  have h := D.le_vert hsp hτ
  have hxx : x = ((x.1, x.2) : E0) := rfl
  rwa [← hxx] at h

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- On the cusp the spear coordinate `fcoord` is above the vertex level. -/
theorem v_lt_fcoord_of_mem_graphSet {x : E0} (hx : x ∈ graphSet D.G D.R) : D.v < fcoord x := by
  obtain ⟨h0, hR, hh⟩ := hx
  have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    simp only [height, heightAt] at hh; linarith
  have h2 := D.above (rad x, Complex.arg x.2) h0 hR
  simp only [fcoord]
  rw [h1]; linarith

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The chart reading of a causal curve near one of its points**: near `t`, `e s = ψ(u)` with
`u` in a given open `V` of the chart, `x ≼ u` after `t` and `u ≼ x` before. -/
theorem eventually_le_coord {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) {V : Set E0}
    (hV : IsOpen V) (hVW : paperInY '' V ⊆ D.W) {x : E0} (hxV : x ∈ V) {t : ℝ}
    (het : e t = D.ψ (paperInY x)) :
    ∀ᶠ s in 𝓝 t, ∃ u ∈ V, e s = D.ψ (paperInY u) ∧ (t ≤ s → Le x u) ∧ (s ≤ t → Le u x) := by
  have hU : IsOpen (D.ψ '' (paperInY '' V)) :=
    D.isOpen_image (E0Spear.isOpen_paperInY_image hV) hVW
  have hetU : e t ∈ D.ψ '' (paperInY '' V) := ⟨_, ⟨x, hxV, rfl⟩, het.symm⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
    (he.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hetU))
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  obtain ⟨_, ⟨u, hu, rfl⟩, hus⟩ := hball hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hseg : ∀ a b, a ≤ b → (a = t ∧ b = s ∨ a = s ∧ b = t) →
      ∀ r ∈ Icc a b, e r ∈ D.ψ '' (paperInY '' V) := by
    intro a b _ hab r hr
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> constructor <;> linarith [hr.1, hr.2]
  have hgx : D.ginv (D.ψ (paperInY x)) = paperInY x := D.ginv_apply (hVW ⟨x, hxV, rfl⟩)
  have hgu : D.ginv (D.ψ (paperInY u)) = paperInY u := D.ginv_apply (hVW ⟨u, hu, rfl⟩)
  refine ⟨u, hu, hus.symm, fun hts => ?_, fun hst => ?_⟩
  · have hIcc : (E0CBG.CE M).CausalCurveIn ⊤ (Icc t s) e :=
      ⟨⟨t, left_mem_Icc.2 hts⟩, ordConnected_Icc, fun a _ b _ => he.curve a trivial b trivial⟩
    have hle := D.le_of_causalCurve hV hVW hIcc (hseg t s hts (Or.inl ⟨rfl, rfl⟩))
      (left_mem_Icc.2 hts) (right_mem_Icc.2 hts) hts
    rw [het, ← hus, hgx, hgu, E0Spear.paperOfY_paperInY, E0Spear.paperOfY_paperInY] at hle
    exact hle
  · have hIcc : (E0CBG.CE M).CausalCurveIn ⊤ (Icc s t) e :=
      ⟨⟨s, left_mem_Icc.2 hst⟩, ordConnected_Icc, fun a _ b _ => he.curve a trivial b trivial⟩
    have hle := D.le_of_causalCurve hV hVW hIcc (hseg s t hst (Or.inr ⟨rfl, rfl⟩))
      (left_mem_Icc.2 hst) (right_mem_Icc.2 hst) hst
    rw [het, ← hus, hgx, hgu, E0Spear.paperOfY_paperInY, E0Spear.paperOfY_paperInY] at hle
    exact hle

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- A point `ψ(u)` of the chart domain is in the spear iff `u` is (`ψ` is injective on `W`). -/
theorem mem_spearSet_iff {u : E0} (hu : paperInY u ∈ D.W) :
    D.ψ (paperInY u) ∈ D.spearSet ↔ u ∈ E0Spear.spear D.v D.R := by
  constructor
  · rintro ⟨_, ⟨u', hu', rfl⟩, he⟩
    have := D.inj (D.spear_sub ⟨u', hu', rfl⟩) hu he
    have e2 : u' = u := paperInY.injOn (by simp) (by simp) this
    rw [e2] at hu'
    exact hu'
  · intro h; exact ⟨_, ⟨u, h, rfl⟩, rfl⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- On the spear, the chart inverse reads the spear coordinates. -/
theorem paperOfY_ginv {z : M} (hz : z ∈ D.spearSet) : paperOfY (D.ginv z) = D.coord z := by
  obtain ⟨hx, hxe⟩ := D.coord_mem hz
  have h := D.coord_eq_ginv hx
  rw [hxe] at h
  exact h.symm

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- The height above the cusp, read through the chart inverse, is continuous at the points of the
spear off the axis. -/
theorem continuousAt_height_ginv {y : M} (hy : y ∈ D.spearSet) (h0 : y ∉ E0CBG.S0 M) :
    ContinuousAt (fun z => height D.G (paperOfY (D.ginv z))) y := by
  obtain ⟨hx, hxe⟩ := D.coord_mem hy
  have hyW : y ∈ D.ψ '' D.W := ⟨_, D.spear_sub ⟨_, hx, rfl⟩, hxe⟩
  have hg := D.continuousAt_ginv_comp (c := fun z : M => z) continuousAt_id hyW
  have hgy : D.ginv y = paperInY (D.coord y) := by
    rw [← hxe, D.ginv_apply (D.spear_sub ⟨_, hx, rfl⟩), hxe]
  have hpo : ContinuousAt paperOfY (D.ginv y) := by
    refine paperOfY.continuousAt ?_
    rw [E0.paperOfY_source, hgy, paperInY_apply]; exact mem_range_self _
  have hh : ContinuousAt (height D.G) (D.coord y) :=
    continuousAt_height D.spacelike (D.rad_coord_pos hy h0) hx.2
  exact hh.comp_of_eq (hpo.comp hg) (D.paperOfY_ginv hy)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- A point of the spear in the closure of a set missing the spear is on its boundary (head or
shaft). -/
theorem not_interior_of_mem_closure {A : Set M} {y : M} (hy : y ∈ closure A)
    (hA : ∀ z ∈ A, z ∉ D.spearSet) (hi : y ∈ D.spearSet) :
    ¬ (D.v < fcoord (D.coord y) ∧ rad (D.coord y) < D.R) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hx, hxe⟩ := D.coord_mem hi
  set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ =>
    hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
  have hOo' : IsOpen (D.ψ '' (paperInY '' O)) :=
    D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW
  have hyO : y ∈ D.ψ '' (paperInY '' O) := ⟨paperInY _, ⟨_, ⟨h1, h2⟩, rfl⟩, hxe⟩
  obtain ⟨z', hz'O, hz'⟩ := mem_closure_iff.1 hy _ hOo' hyO
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz'O
  exact hA _ hz' ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩


omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The cusp is bounded above over an annulus `r₀ ≤ r ≤ R`. -/
theorem exists_bound_G_annulus {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ B : ℝ, ∀ x : E0, r₀ ≤ rad x → rad x ≤ D.R → D.G (rad x, Complex.arg x.2) ≤ B := by
  set A : Set ℂ := {z | r₀ ≤ ‖z‖} ∩ Metric.closedBall 0 D.R with hA
  have hAc : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) D.R).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter Metric.isClosed_closedBall)
      inter_subset_right
  set f : ℂ → ℝ := fun z => height D.G ((0 : ℝ), z) with hf
  have hfc : ContinuousOn f A := by
    intro z hz
    have hz1 : r₀ ≤ ‖z‖ := hz.1
    have hz2 : ‖z‖ ≤ D.R := by have := hz.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
    exact ((continuousAt_height D.spacelike (x := ((0 : ℝ), z)) (hr₀.trans_le hz1) hz2).comp
      (Continuous.continuousAt (by fun_prop))).continuousWithinAt
  obtain ⟨B, hB⟩ := hAc.exists_bound_of_continuousOn hfc
  refine ⟨B, fun x hx1 hx2 => ?_⟩
  have h := hB x.2 ⟨hx1, by rw [Metric.mem_closedBall, dist_zero_right]; exact hx2⟩
  rw [Real.norm_eq_abs] at h
  have e : D.G (rad x, Complex.arg x.2) = -f x.2 := by
    simp only [hf, height, heightAt, rad]; ring
  rw [e]
  exact (neg_le_abs _).trans h

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The cusp climbs to `+∞` at the axis, uniformly. -/
theorem exists_lt_G_near_axis (T₀ : ℝ) :
    ∃ ε > 0, ∀ q : ℝ × ℝ, 0 < q.1 → q.1 < ε → T₀ < D.G q := by
  have h := D.lim.eventually_gt_atTop T₀
  rw [Filter.eventually_comap] at h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
  refine ⟨ε, hε, fun q hq0 hqε => hball ?_ hq0 q rfl⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hq0]
  exact hqε


end SpearSurgeryDatum


namespace SurgeryData

variable {S : Set M} (Dat : SurgeryData M S)

/-- The part of spear `i` (off the axis) on or above the cusp `Σ*_i`. -/
def cuspUp (i : Dat.ι) : Set M :=
  {y | y ∈ (Dat.D i).spearSet ∧ 0 < rad ((Dat.D i).coord y) ∧
    0 ≤ height (Dat.D i).G ((Dat.D i).coord y)}

/-- The part of spear `i` (off the axis) on or below the cusp `Σ*_i`. -/
def cuspDown (i : Dat.ι) : Set M :=
  {y | y ∈ (Dat.D i).spearSet ∧ 0 < rad ((Dat.D i).coord y) ∧
    height (Dat.D i).G ((Dat.D i).coord y) ≤ 0}

/-- **The future side of `Σ*`**: `J⁺(S)` outside the spears, on or above the cusps inside. -/
def futSide : Set M :=
  ((E0CBG.CE M).Jplus ⊤ S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, Dat.cuspUp i

/-- **The past side of `Σ*`**: `J⁻(S)` outside the spears, on or below the cusps inside. -/
def pastSide : Set M :=
  ((E0CBG.CE M).Jminus ⊤ S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, Dat.cuspDown i

end SurgeryData

/-- The facts about a compact Cauchy surface of a globally hyperbolic `𝔼₀`-manifold used below. -/
theorem cauchy_facts (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) :
    (E0CBG.CE M).IsAcausal S ∧ IsClosed ((E0CBG.CE M).Jplus ⊤ S) ∧
      IsClosed ((E0CBG.CE M).Jminus ⊤ S) ∧
      (∀ y, y ∈ (E0CBG.CE M).Jplus ⊤ S ∪ (E0CBG.CE M).Jminus ⊤ S) ∧
      (∀ y, y ∈ (E0CBG.CE M).Jplus ⊤ S → y ∈ (E0CBG.CE M).Jminus ⊤ S → y ∈ S) := by
  have hT := E0LM.e0_tarentin (M := M)
  have hle := hGH.isClosed_le hT
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hS.cauchy.isAcausal E0LM.e0_causallyArcConnected hext
  refine ⟨hac, Causal.Causality.isClosed_Jplus_of_isCompact hle hS.compact,
    Causal.Causality.isClosed_Jminus_of_isCompact hle hS.compact,
    fun y => Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hS.cauchy y, ?_⟩
  rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hyw⟩
  have h := hac z hz w hw ((E0CBG.CE M).le_trans hzy hyw)
  subst h
  rw [hGH.1 hyw hzy]; exact hz

/-- **A BTZ point in the causal future of a point of `S` lies inside a spear of the surgery**
(on the ray above the vertex, which is in `I⁻(S)`). -/
theorem exists_open_of_BTZ (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (Dat : SurgeryData M S) {s q : M} (hsS : s ∈ S)
    (hsq : (E0CBG.CE M).le ⊤ s q) (hq0 : q ∈ E0CBG.S0 M) :
    ∃ j : Dat.ι, ∃ O : Set M, IsOpen O ∧ q ∈ O ∧ O ⊆ (Dat.D j).spearSet := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  obtain ⟨hac, -, -, -, -⟩ := cauchy_facts hGH hS
  have hs0 : s ∈ E0CBG.S0 M := hA.mem_sing_zero_of_le hq0 hsq
  obtain ⟨j, hj⟩ := mem_iUnion.1 (Dat.covers ⟨hsS, hs0⟩)
  set D := Dat.D j with hD
  -- a point of `I⁻(S)` is not in `J⁺(S)`
  have hnot : ∀ y, (E0CBG.CE M).le ⊤ s y → y ∈ (E0CBG.CE M).Iminus ⊤ S → False := by
    rintro y hsy ⟨s'', hs'', hlt⟩
    have h1 := hac s hsS s'' hs'' ((E0CBG.CE M).le_trans hsy ((E0CBG.CE M).le_of_lt hlt))
    subst h1
    have h2 := hGH.1 ((E0CBG.CE M).le_of_lt hlt) hsy
    subst h2
    exact E0Spear.not_lt_self hGH _ hlt
  have hqc : s ∈ connectedComponentIn (E0CBG.S0 M) q := hA.Jminus_subset_component hq0 hsq
  have hsc : s ∈ connectedComponentIn (E0CBG.S0 M) D.p := D.spearSet_inter_S0_subset hj hs0
  have hqcp : q ∈ connectedComponentIn (E0CBG.S0 M) D.p := by
    rw [connectedComponentIn_eq hsc, ← connectedComponentIn_eq hqc]
    exact mem_connectedComponentIn hq0
  obtain ⟨t₁, ht₁, hst₁⟩ := D.eq_ray_of_mem_S0 hj hs0
  have hps : (E0CBG.CE M).le ⊤ D.p s := by
    have h := D.ray.le le_rfl ht₁
    rw [D.ray.zero] at h
    rw [hst₁]; exact h
  have hpq : (E0CBG.CE M).le ⊤ D.p q := (E0CBG.CE M).le_trans hps hsq
  obtain ⟨γ', hγ'0, hγ'e, hγ'i, hγ'r⟩ := (E0LM.e0_globalBTZ M).line D.p D.p_mem
  obtain ⟨σ, hσ⟩ : q ∈ range γ' := hγ'r ▸ hqcp
  have hqp : q ≠ D.p := fun h => hnot q hsq (h ▸ D.p_past)
  have hσ0 : 0 ≤ σ := by
    by_contra hneg
    push Not at hneg
    have h1 : (E0CBG.CE M).le ⊤ q D.p := by
      rw [← hσ, ← hγ'0]; exact hγ'i.1.le_of_le trivial trivial hneg.le
    exact hqp (hGH.1 h1 hpq)
  obtain ⟨t₂, ht₂, hts⟩ := D.ray.exists_eq_of_line hGH hγ'0 (hγ'e hGH.1) hγ'i.1 hγ'r hσ0
  have hq : q = D.ψ (paperInY ((D.v + t₂, 0) : E0)) := by rw [← hσ, ← hts]; rfl
  have ht₂0 : 0 < t₂ := by
    refine lt_of_le_of_ne ht₂ fun h0 => hqp ?_
    rw [hq, ← h0]
    have := D.ray.zero
    simpa [E0Spear.yAxis] using this
  set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ =>
    hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
  refine ⟨j, D.ψ '' (paperInY '' O), D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW,
    ⟨paperInY _, ⟨((D.v + t₂, 0) : E0), ?_, rfl⟩, hq.symm⟩, ?_⟩
  · have h0 : rad ((D.v + t₂, 0) : E0) = 0 := by simp [rad]
    refine ⟨?_, by rw [h0]; exact D.pos⟩
    simp only [fcoord, h0]; linarith
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩

namespace SurgeryData

variable {S : Set M} (Dat : SurgeryData M S)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cuspUp_subset (i : Dat.ι) : Dat.cuspUp i ⊆ (Dat.D i).spearSet := fun _ h => h.1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cuspDown_subset (i : Dat.ι) : Dat.cuspDown i ⊆ (Dat.D i).spearSet := fun _ h => h.1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- A point of a spear is in no other spear. -/
theorem eq_of_mem_spearSet {i j : Dat.ι} {y : M} (hi : y ∈ (Dat.D i).spearSet)
    (hj : y ∈ (Dat.D j).spearSet) : i = j := by
  by_contra h
  exact Set.disjoint_left.1 (Dat.disjoint h) hi hj

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **`Σ*` is on both sides.** -/
theorem sigmaStar_subset_sides {y : M} (hy : y ∈ Dat.sigmaStar) : y ∈ Dat.futSide ∧ y ∈ Dat.pastSide := by
  have href : (E0CBG.CE M).le ⊤ y y := (E0CBG.CE M).le_refl trivial
  rcases hy with ⟨hyS, hn⟩ | hy
  · exact ⟨Or.inl ⟨⟨y, hyS, href⟩, hn⟩, Or.inl ⟨⟨y, hyS, href⟩, hn⟩⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    have hg := (Dat.D i).coord_mem_graphSet hi
    have hsp := (Dat.D i).cusp_subset_spearSet hi
    exact ⟨Or.inr (mem_iUnion.2 ⟨i, hsp, hg.1, hg.2.2.ge⟩),
      Or.inr (mem_iUnion.2 ⟨i, hsp, hg.1, hg.2.2.le⟩)⟩

/-- **The two sides meet exactly along `Σ*`.** -/
theorem mem_sigmaStar_of_sides (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {y : M} (hF : y ∈ Dat.futSide) (hP : y ∈ Dat.pastSide) :
    y ∈ Dat.sigmaStar := by
  obtain ⟨-, -, -, -, hinter⟩ := cauchy_facts hGH hS
  rcases hF with ⟨hJp, hn⟩ | hF
  · rcases hP with ⟨hJm, -⟩ | hP
    · exact Or.inl ⟨hinter y hJp hJm, hn⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hP
      exact absurd (mem_iUnion.2 ⟨i, hi.1⟩) hn
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hF
    rcases hP with ⟨-, hn⟩ | hP
    · exact absurd (mem_iUnion.2 ⟨i, hi.1⟩) hn
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hP
      have hij := Dat.eq_of_mem_spearSet hi.1 hj.1
      subst hij
      obtain ⟨hx, hxe⟩ := (Dat.D i).coord_mem hi.1
      have hg : (Dat.D i).coord y ∈ graphSet (Dat.D i).G (Dat.D i).R :=
        ⟨hi.2.1, hx.2, le_antisymm hj.2.2 hi.2.2⟩
      exact Or.inr (mem_iUnion.2 ⟨i, _, ⟨_, hg, rfl⟩, hxe⟩)

/-- **The two sides cover `Reg M`.** -/
theorem mem_sides_of_notMem_S0 (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {y : M} (hy : y ∉ E0CBG.S0 M) :
    y ∈ Dat.futSide ∨ y ∈ Dat.pastSide := by
  obtain ⟨-, -, -, hcov, -⟩ := cauchy_facts hGH hS
  by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    have hr := (Dat.D i).rad_coord_pos hi hy
    rcases le_total 0 (height (Dat.D i).G ((Dat.D i).coord y)) with h | h
    · exact Or.inl (Or.inr (mem_iUnion.2 ⟨i, hi, hr, h⟩))
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨i, hi, hr, h⟩))
  · rcases hcov y with h | h
    · exact Or.inl (Or.inl ⟨h, hK⟩)
    · exact Or.inr (Or.inl ⟨h, hK⟩)


/-- **The future side is closed in `Reg M`.** -/
theorem closure_futSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) : closure Dat.futSide ⊆ Dat.futSide ∪ E0CBG.S0 M := by
  haveI := Dat.finite
  obtain ⟨-, hJpc, -, -, hinter⟩ := cauchy_facts hGH hS
  unfold futSide
  rw [closure_union, closure_iUnion_of_finite]
  rintro y (hy | hy)
  · left
    have hyJ : y ∈ (E0CBG.CE M).Jplus ⊤ S := closure_minimal sdiff_subset hJpc hy
    by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
    swap
    · exact Or.inl ⟨hyJ, hK⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    set D := Dat.D i with hD
    obtain ⟨hx, hxe⟩ := D.coord_mem hi
    have hnb : ¬ (D.coord y).1 < D.τS (D.coord y).2 := fun hlt => by
      have hm : y ∈ (E0CBG.CE M).Jminus ⊤ S := hxe ▸ D.mem_Jminus_of_le_τS hx hlt.le
      have := (D.graph _ hx).1 (by rw [hxe]; exact hinter y hyJ hm)
      linarith
    have hbd := D.not_interior_of_mem_closure hy
      (fun z hz hzi => hz.2 (mem_iUnion.2 ⟨i, hzi⟩)) hi
    have hf : D.v < fcoord (D.coord y) := by
      by_contra hle
      push Not at hle
      apply hnb
      have h1 := D.shaft (D.coord y).2 hx.2
      have h2 : rad (D.coord y) ≤ D.R := hx.2
      simp only [fcoord] at hle
      change (D.coord y).1 < D.τS (D.coord y).2
      simp only [rad] at h2 h1 hle
      linarith
    have hR : rad (D.coord y) = D.R := le_antisymm hx.2 (not_lt.1 fun h => hbd ⟨hf, h⟩)
    refine Or.inr (mem_iUnion.2 ⟨i, hi, by rw [hR]; exact D.pos, ?_⟩)
    simp only [height, heightAt]
    rw [rim_value D.rim hR]
    push Not at hnb
    linarith
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    set D := Dat.D i with hD
    have hysp : y ∈ D.spearSet := closure_minimal (Dat.cuspUp_subset i) (Dat.isClosed i) hi
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    refine Or.inl (Or.inr (mem_iUnion.2 ⟨i, hysp, D.rad_coord_pos hysp h0, ?_⟩))
    by_contra hneg
    push Not at hneg
    have hf := D.continuousAt_height_ginv hysp h0
    have hev : ∀ᶠ z in 𝓝 y, height D.G (paperOfY (D.ginv z)) < 0 :=
      hf.eventually (gt_mem_nhds (by simp only; rw [D.paperOfY_ginv hysp]; exact hneg))
    obtain ⟨z, hzev, hzU⟩ := mem_closure_iff_nhds.1 hi _ hev
    have hz : height D.G (paperOfY (D.ginv z)) < 0 := hzev
    rw [D.paperOfY_ginv hzU.1] at hz
    linarith [hzU.2.2]

/-- **The past side is closed in `Reg M`.** -/
theorem closure_pastSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) : closure Dat.pastSide ⊆ Dat.pastSide ∪ E0CBG.S0 M := by
  haveI := Dat.finite
  obtain ⟨-, -, hJmc, -, hinter⟩ := cauchy_facts hGH hS
  unfold pastSide
  rw [closure_union, closure_iUnion_of_finite]
  rintro y (hy | hy)
  · have hyJ : y ∈ (E0CBG.CE M).Jminus ⊤ S := closure_minimal sdiff_subset hJmc hy
    by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
    swap
    · exact Or.inl (Or.inl ⟨hyJ, hK⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    set D := Dat.D i with hD
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    left
    obtain ⟨hx, hxe⟩ := D.coord_mem hi
    have hr := D.rad_coord_pos hi h0
    have hna : ¬ D.τS (D.coord y).2 < (D.coord y).1 := fun hlt => by
      have hm : y ∈ (E0CBG.CE M).Jplus ⊤ S := hxe ▸ D.mem_Jplus_of_τS_le hx hlt.le
      have := (D.graph _ hx).1 (by rw [hxe]; exact hinter y hm hyJ)
      linarith
    have hbd := D.not_interior_of_mem_closure hy
      (fun z hz hzi => hz.2 (mem_iUnion.2 ⟨i, hzi⟩)) hi
    by_cases hf : D.v < fcoord (D.coord y)
    · have hR : rad (D.coord y) = D.R := le_antisymm hx.2 (not_lt.1 fun h => hbd ⟨hf, h⟩)
      refine Or.inr (mem_iUnion.2 ⟨i, hi, hr, ?_⟩)
      simp only [height, heightAt]
      rw [rim_value D.rim hR]
      push Not at hna
      linarith
    · push Not at hf
      refine Or.inr (mem_iUnion.2 ⟨i, hi, hr, ?_⟩)
      have h2 := D.above (rad (D.coord y), Complex.arg (D.coord y).2) hr hx.2
      have h3 : rad (D.coord y) ≤ D.R := hx.2
      simp only [fcoord] at hf
      simp only [height, heightAt]
      linarith
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    set D := Dat.D i with hD
    have hysp : y ∈ D.spearSet := closure_minimal (Dat.cuspDown_subset i) (Dat.isClosed i) hi
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    refine Or.inl (Or.inr (mem_iUnion.2 ⟨i, hysp, D.rad_coord_pos hysp h0, ?_⟩))
    by_contra hneg
    push Not at hneg
    have hf := D.continuousAt_height_ginv hysp h0
    have hev : ∀ᶠ z in 𝓝 y, 0 < height D.G (paperOfY (D.ginv z)) :=
      hf.eventually (lt_mem_nhds (by simp only; rw [D.paperOfY_ginv hysp]; exact hneg))
    obtain ⟨z, hzev, hzU⟩ := mem_closure_iff_nhds.1 hi _ hev
    have hz : 0 < height D.G (paperOfY (D.ginv z)) := hzev
    rw [D.paperOfY_ginv hzU.1] at hz
    linarith [hzU.2.2]


omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- Near a point of spear `i`, no other spear. -/
theorem eventually_other (i : Dat.ι) {y : M} (hy : y ∈ (Dat.D i).spearSet) :
    ∀ᶠ z in 𝓝 y, ∀ j, z ∈ (Dat.D j).spearSet → j = i := by
  haveI := Dat.finite
  refine eventually_all.2 fun j => ?_
  by_cases hji : j = i
  · exact Eventually.of_forall fun _ _ => hji
  · have hyj : y ∉ (Dat.D j).spearSet := fun h => hji (Dat.eq_of_mem_spearSet h hy)
    filter_upwards [(Dat.isClosed j).isOpen_compl.mem_nhds hyj] with z hz hzj
    exact absurd hzj hz

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Forward propagation of the future side** along a causal curve of `Reg M`. -/
theorem eventually_futSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.futSide) : ∀ᶠ s in 𝓝 t, t ≤ s → e s ∈ Dat.futSide := by
  haveI := Dat.finite
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := isClosed_iUnion_of_finite Dat.isClosed
  have hec : Continuous e := he.continuous
  rcases ht with ⟨⟨z, hz, hzt⟩, hK⟩ | ht
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hts
    exact Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans hzt (he.le_of_le trivial trivial hts)⟩, hs⟩
  obtain ⟨i, hyi, hr, hh⟩ := mem_iUnion.1 ht
  set D := Dat.D i with hD
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  have hin : ∀ s u, e s = D.ψ (paperInY u) → Le (D.coord (e t)) u →
      u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.futSide := by
    intro s u hus hle husp
    have hcu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    refine Or.inr (mem_iUnion.2 ⟨i, ?_, ?_, ?_⟩)
    · rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    · rw [hcu]; exact hr.trans_le hle.closed.2.1
    · rw [hcu]; exact hh.trans (height_le_of_le D.spacelike hle hr husp.2)
  rcases hx.2.lt_or_eq with hlt | heq
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | rad u < D.R} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_rad continuous_const)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hlt⟩ hxe.symm]
      with s ⟨u, hu, hus, hfut, _⟩ hts
    have hle := hfut hts
    have hf := (E0.calculus_le ((E0.le_top_iff).2 hle)).2.2.2.2.1
    exact hin s u hus hle ⟨hx.1.trans hf, hu.2.le⟩
  · have hτ : D.τS (D.coord (e t)).2 ≤ (D.coord (e t)).1 := by
      have h := hh
      simp only [height, heightAt] at h
      rw [rim_value D.rim heq] at h
      linarith
    obtain ⟨z, hz, hzt⟩ : e t ∈ (E0CBG.CE M).Jplus ⊤ S := hxe ▸ D.mem_Jplus_of_τS_le hx hτ
    filter_upwards [D.eventually_le_coord he hPo (image_preimage_subset _ _)
        (D.spear_sub ⟨_, hx, rfl⟩) hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, hfut, _⟩ hoth hts
    have hle := hfut hts
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hle husp
    · refine Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans hzt (he.le_of_le trivial trivial hts)⟩, ?_⟩
      intro hK
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu).1 hj)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Backward propagation of the past side** along a causal curve of `Reg M`. -/
theorem eventually_pastSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) {t : ℝ} (ht : e t ∈ Dat.pastSide) :
    ∀ᶠ s in 𝓝 t, s ≤ t → e s ∈ Dat.pastSide := by
  haveI := Dat.finite
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := isClosed_iUnion_of_finite Dat.isClosed
  have hec : Continuous e := he.continuous
  rcases ht with ⟨⟨z, hz, hzt⟩, hK⟩ | ht
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hst
    exact Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial hst) hzt⟩, hs⟩
  obtain ⟨i, hyi, hr, hh⟩ := mem_iUnion.1 ht
  set D := Dat.D i with hD
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  have hin : ∀ s u, e s = D.ψ (paperInY u) → Le u (D.coord (e t)) →
      u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.pastSide := by
    intro s u hus hle husp
    have hcu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    have hsp : e s ∈ D.spearSet := by rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    have hru : 0 < rad u := by rw [← hcu]; exact D.rad_coord_pos hsp (he0 s)
    refine Or.inr (mem_iUnion.2 ⟨i, hsp, by rw [hcu]; exact hru, ?_⟩)
    rw [hcu]; exact (height_le_of_le D.spacelike hle hru hx.2).trans hh
  by_cases hf : D.v < fcoord (D.coord (e t))
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | D.v < fcoord u} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_const continuous_fcoord)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf⟩ hxe.symm]
      with s ⟨u, hu, hus, _, hpast⟩ hst
    have hle := hpast hst
    exact hin s u hus hle ⟨hu.2.le, hle.closed.2.1.trans hx.2⟩
  · push Not at hf
    have hτ : (D.coord (e t)).1 ≤ D.τS (D.coord (e t)).2 := by
      have h1 := D.shaft (D.coord (e t)).2 hx.2
      have h2 : rad (D.coord (e t)) ≤ D.R := hx.2
      simp only [fcoord] at hf
      simp only [rad] at h1 h2 hf
      linarith
    obtain ⟨z, hz, hzt⟩ : e t ∈ (E0CBG.CE M).Jminus ⊤ S := hxe ▸ D.mem_Jminus_of_le_τS hx hτ
    filter_upwards [D.eventually_le_coord he hPo (image_preimage_subset _ _)
        (D.spear_sub ⟨_, hx, rfl⟩) hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, _, hpast⟩ hoth hst
    have hle := hpast hst
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hle husp
    · refine Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial hst) hzt⟩, ?_⟩
      intro hK
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu).1 hj)

/-- **A causal curve of `Reg M` inside `Σ*` is locally constant.** -/
theorem eventually_eq_of_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.sigmaStar) : ∀ᶠ s in 𝓝 t, e s ∈ Dat.sigmaStar → e s = e t := by
  haveI := Dat.finite
  obtain ⟨hac, -, -, -, -⟩ := cauchy_facts hGH hS
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := isClosed_iUnion_of_finite Dat.isClosed
  have hec : Continuous e := he.continuous
  have hcmp : ∀ s, e s ∈ S → e t ∈ S → e s = e t := fun s hs ht' => by
    rcases le_total s t with h | h
    · exact hac _ hs _ ht' (he.le_of_le trivial trivial h)
    · exact (hac _ ht' _ hs (he.le_of_le trivial trivial h)).symm
  have hSout : ∀ s, e s ∈ Dat.sigmaStar → e s ∉ ⋃ i, (Dat.D i).spearSet → e s ∈ S := by
    intro s h1 h2
    have h : e s ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨h1, h2⟩
    rw [Dat.sigmaStar_diff] at h
    exact h.1
  by_cases hK : e t ∈ ⋃ i, (Dat.D i).spearSet
  swap
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hsS
    exact hcmp s (hSout s hsS hs) (hSout t ht hK)
  obtain ⟨i, hyi⟩ := mem_iUnion.1 hK
  set D := Dat.D i with hD
  have hcu : e t ∈ D.cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨ht, hyi⟩
  have hg := D.coord_mem_graphSet hcu
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hf := D.v_lt_fcoord_of_mem_graphSet hg
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  -- inside the spear, the cusp is acausal in the chart
  have hin : ∀ s u, e s = D.ψ (paperInY u) → (t ≤ s → Le (D.coord (e t)) u) →
      (s ≤ t → Le u (D.coord (e t))) → u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.sigmaStar →
      e s = e t := by
    intro s u hus hfut hpast husp hsS
    have hsp : e s ∈ D.spearSet := by rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    have hcs : e s ∈ D.cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hsS, hsp⟩
    have hgs := D.coord_mem_graphSet hcs
    have hcuu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    rw [hcuu] at hgs
    have hux : u = D.coord (e t) := by
      by_contra hne
      rcases le_total t s with h | h
      · have := height_lt_of_le D.spacelike (hfut h) hg.1 hgs.2.1 (Ne.symm hne)
        rw [hg.2.2, hgs.2.2] at this; exact lt_irrefl _ this
      · have := height_lt_of_le D.spacelike (hpast h) hgs.1 hg.2.1 hne
        rw [hg.2.2, hgs.2.2] at this; exact lt_irrefl _ this
    rw [hus, hux, hxe]
  rcases hg.2.1.lt_or_eq with hlt | heq
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ ({u | D.v < fcoord u} ∩ {u | rad u < D.R}) with hV
    have hVo : IsOpen V := hPo.inter ((isOpen_lt continuous_const continuous_fcoord).inter
      (isOpen_lt continuous_rad continuous_const))
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf, hlt⟩ hxe.symm]
      with s ⟨u, hu, hus, hfut, hpast⟩ hsS
    exact hin s u hus hfut hpast ⟨hu.2.1.le, hu.2.2.le⟩ hsS
  · have htS : e t ∈ S := by
      have h1 : (D.coord (e t)).1 = D.τS (D.coord (e t)).2 :=
        (mem_graphSet_iff_of_rim D.pos D.rim heq).1 hg
      rw [← hxe]; exact (D.graph _ hx).2 h1
    set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | D.v < fcoord u} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_const continuous_fcoord)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf⟩ hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, hfut, hpast⟩ hoth hsS
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hfut hpast husp hsS
    · refine hcmp s (hSout s hsS fun hK' => ?_) htS
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK'
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu.1).1 hj)


/-- **Every inextensible causal curve of `Reg M` meets the past side** (its spear components reach
below the cusp by Remark 2.12, the cusp climbing to `+∞` at the axis; a curve missing the spears
and the past side would have a past-inextensible tail in a compact diamond `J⁺(s) ∩ J⁻(d 0)`,
converging in `Reg M` or to a BTZ point inside a spear). -/
theorem exists_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic) (hS : IsE0C1SpacelikeCauchy M S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.pastSide := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hT := E0LM.e0_tarentin (M := M)
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  by_cases hK : ∃ s₀ i, e s₀ ∈ (Dat.D i).spearSet
  · obtain ⟨s₀, i, hs₀⟩ := hK
    set D := Dat.D i with hD
    obtain ⟨-, -, hmono, hrad, hpast, -⟩ := harc i s₀ hs₀
    have hJ : ∀ t ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} s₀,
        e t ∈ D.spearSet := fun t ht => (connectedComponentIn_subset _ _ ht).2
    rcases hpast with ⟨t, ht, hneg⟩ | hax
    · exact ⟨t, Or.inr (mem_iUnion.2 ⟨i, hJ t ht, (hrad t ht).1, hneg.le⟩)⟩
    · have hJ0 : s₀ ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} s₀ :=
        mem_connectedComponentIn ⟨trivial, hs₀⟩
      obtain ⟨ε, hε, hεG⟩ := D.exists_lt_G_near_axis (D.coord (e s₀)).1
      obtain ⟨t, ht, htr⟩ := hax (min ε (rad (D.coord (e s₀)))) (lt_min hε (hrad s₀ hJ0).1)
      have hts : t ≤ s₀ := by
        by_contra h
        push Not at h
        have := (hmono s₀ hJ0 t ht h.le).closed.2.1
        linarith [min_le_right ε (rad (D.coord (e s₀)))]
      have hτ := fst_le_of_le (hmono t ht s₀ hJ0 hts)
      have hG := hεG (rad (D.coord (e t)), Complex.arg (D.coord (e t)).2) (hrad t ht).1
        (htr.trans_le (min_le_left _ _))
      refine ⟨t, Or.inr (mem_iUnion.2 ⟨i, hJ t ht, (hrad t ht).1, ?_⟩)⟩
      simp only [height, heightAt]
      linarith
  push Not at hK
  by_contra hno
  push Not at hno
  obtain ⟨hJm, -, hSC, hC, hcaus⟩ := regM_facts hGH
  have hJp : ∀ t, e t ∈ (E0CBG.CE M).Jplus ⊤ S := fun t => by
    rcases Dat.mem_sides_of_notMem_S0 hGH hS (d t).2 with h | h
    · rcases h with ⟨h, -⟩ | h
      · exact h
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        exact absurd hi.1 (hK t i)
    · exact absurd h (hno t)
  choose σ hσS hσle using fun n : ℕ => hJp (-(n : ℝ))
  obtain ⟨s, hsS, φ, hφ, hlim⟩ := hS.compact.tendsto_subseq hσS
  have hsle : ∀ t, (E0CBG.CE M).le ⊤ s (e t) := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_ge (-t)
    have hev : ∀ᶠ k in atTop, σ (φ k) ∈ (E0CBG.CE M).Jminus ⊤ {e t} := by
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with k hk
      refine ⟨e t, rfl, (E0CBG.CE M).le_trans (hσle (φ k)) (he.le_of_le trivial trivial ?_)⟩
      have : (N : ℝ) ≤ φ k := by exact_mod_cast hk
      linarith
    obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jminus_singleton hT (e t)).mem_of_tendsto hlim hev
    exact h
  obtain ⟨q, hq⟩ := exists_tendsto_atBot_of_monotone hGH (t₀ := 0)
    (fun a b hab _ => he.le_of_le trivial trivial hab) (hGH.2 s (e 0))
    (fun t ht => Causal.Causality.mem_diamond.2 ⟨hsle t, he.le_of_le trivial trivial ht⟩)
  by_cases hq0 : q ∈ E0CBG.S0 M
  · have hsq : (E0CBG.CE M).le ⊤ s q := by
      obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT s).mem_of_tendsto hq
        (Eventually.of_forall fun t => ⟨s, rfl, hsle t⟩)
      exact h
    obtain ⟨j, O, hO, hqO, hOsub⟩ := exists_open_of_BTZ hGH hS Dat hsS hsq hq0
    obtain ⟨t, ht⟩ := (hq.eventually (hO.mem_nhds hqO)).exists
    exact hK t j (hOsub ht)
  · exact Causal.Causality.Inextensible.not_tendsto_atBot hJm hSC hC hcaus (regM_Jminus_ne hGH) hd
      ⟨q, hq0⟩ (tendsto_subtype_rng.2 hq)

/-- **Every inextensible causal curve of `Reg M` meets the future side** (a spear component missing
it ends on the shaft below `C = C*`, in `J⁻(S)`, by Remark 2.12 and Lemma 2.10's `τ → +∞` case;
a curve missing it would then lie in `J⁻(S)` and have a future-inextensible tail in a compact
diamond, converging in `Reg M`). -/
theorem exists_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic) (hS : IsE0C1SpacelikeCauchy M S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.futSide := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hT := E0LM.e0_tarentin (M := M)
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  by_contra hno
  push Not at hno
  have hJm' : ∀ t, e t ∈ (E0CBG.CE M).Jminus ⊤ S := by
    intro t
    by_cases hK : ∃ i, e t ∈ (Dat.D i).spearSet
    · obtain ⟨i, hi⟩ := hK
      set D := Dat.D i with hD
      obtain ⟨-, -, hmono, hrad, -, hfut⟩ := harc i t hi
      have hJ : ∀ t' ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} t,
          e t' ∈ D.spearSet := fun t' ht' => (connectedComponentIn_subset _ _ ht').2
      have ht0 : t ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} t :=
        mem_connectedComponentIn ⟨trivial, hi⟩
      rcases hfut with hup | ⟨b, hb, hbmax, hbR⟩
      · exfalso
        obtain ⟨B, hB⟩ := D.exists_bound_G_annulus (hrad t ht0).1
        obtain ⟨t', ht', hT'⟩ := hup (max B (D.coord (e t)).1 + 1)
        have htt' : t ≤ t' := by
          by_contra h
          push Not at h
          have := fst_le_of_le (hmono t' ht' t ht0 h.le)
          linarith [le_max_right B (D.coord (e t)).1]
        have hle := hmono t ht0 t' ht' htt'
        have hG := hB _ hle.closed.2.1 (hrad t' ht').2
        apply hno t'
        refine Or.inr (mem_iUnion.2 ⟨i, hJ t' ht', (hrad t' ht').1, ?_⟩)
        simp only [height, heightAt]
        linarith [le_max_left B (D.coord (e t)).1]
      · have hbsp := hJ b hb
        obtain ⟨hx, hxe⟩ := D.coord_mem hbsp
        have hneg : height D.G (D.coord (e b)) < 0 := by
          by_contra h
          push Not at h
          exact hno b (Or.inr (mem_iUnion.2 ⟨i, hbsp, (hrad b hb).1, h⟩))
        have hτ : (D.coord (e b)).1 ≤ D.τS (D.coord (e b)).2 := by
          simp only [height, heightAt] at hneg
          rw [rim_value D.rim hbR] at hneg
          linarith
        obtain ⟨z, hz, hbz⟩ : e b ∈ (E0CBG.CE M).Jminus ⊤ S :=
          hxe ▸ D.mem_Jminus_of_le_τS hx hτ
        exact ⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial (hbmax t ht0)) hbz⟩
    · push Not at hK
      rcases Dat.mem_sides_of_notMem_S0 hGH hS (d t).2 with h | h
      · exact absurd h (hno t)
      · rcases h with ⟨h, -⟩ | h
        · exact h
        · obtain ⟨i, hi⟩ := mem_iUnion.1 h
          exact absurd hi.1 (hK i)
  obtain ⟨-, hJp, hSC, hC, hcaus⟩ := regM_facts hGH
  choose σ hσS hσle using fun n : ℕ => hJm' (n : ℝ)
  obtain ⟨s, hsS, φ, hφ, hlim⟩ := hS.compact.tendsto_subseq hσS
  have hsle : ∀ t, (E0CBG.CE M).le ⊤ (e t) s := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_ge t
    have hev : ∀ᶠ k in atTop, σ (φ k) ∈ (E0CBG.CE M).Jplus ⊤ {e t} := by
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with k hk
      refine ⟨e t, rfl, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial ?_) (hσle (φ k))⟩
      have : (N : ℝ) ≤ φ k := by exact_mod_cast hk
      linarith
    obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT (e t)).mem_of_tendsto hlim hev
    exact h
  obtain ⟨q, hq⟩ := E0Spear.exists_tendsto_of_monotone hGH (t₀ := 0)
    (fun a b _ hab => he.le_of_le trivial trivial hab) (hGH.2 (e 0) s)
    (fun t ht => Causal.Causality.mem_diamond.2 ⟨he.le_of_le trivial trivial ht, hsle t⟩)
  have hq0 : q ∉ E0CBG.S0 M := by
    intro hq0
    have h0q : (E0CBG.CE M).le ⊤ (e 0) q := by
      obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT (e 0)).mem_of_tendsto hq
        (eventually_atTop.2 ⟨0, fun t ht => ⟨e 0, rfl, he.le_of_le trivial trivial ht⟩⟩)
      exact h
    exact (d 0).2 (hA.mem_sing_zero_of_le hq0 h0q)
  exact Causal.Causality.Inextensible.not_tendsto_atTop hJp hSC hC hcaus (regM_Jplus_ne hGH) hd
    ⟨q, hq0⟩ (tendsto_subtype_rng.2 hq)

/-- The future side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.futSide) := by
  have hc : IsClosed (Dat.futSide ∪ E0CBG.S0 M) := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union, isClosed_S0.closure_eq]
    exact union_subset (Dat.closure_futSide_subset hGH hS) subset_union_right
  have heq : e ⁻¹' Dat.futSide = e ⁻¹' (Dat.futSide ∪ E0CBG.S0 M) := by
    ext t
    simp only [mem_preimage, mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right (he0 t)⟩
  rw [heq]
  exact hc.preimage hec

/-- The past side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.pastSide) := by
  have hc : IsClosed (Dat.pastSide ∪ E0CBG.S0 M) := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union, isClosed_S0.closure_eq]
    exact union_subset (Dat.closure_pastSide_subset hGH hS) subset_union_right
  have heq : e ⁻¹' Dat.pastSide = e ⁻¹' (Dat.pastSide ∪ E0CBG.S0 M) := by
    ext t
    simp only [mem_preimage, mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right (he0 t)⟩
  rw [heq]
  exact hc.preimage hec

/-- **The future side is a future set along a causal curve of `Reg M`.** -/
theorem futSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic) (hS : IsE0C1SpacelikeCauchy M S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (ha : e a ∈ Dat.futSide) (hab : a ≤ b) : e b ∈ Dat.futSide := by
  have hcl := Dat.isClosed_preimage_futSide hGH hS he.continuous he0
  refine (IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) ha
    fun x hx => ?_) (right_mem_Icc.2 hab)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Dat.eventually_futSide he hx.1)]
    with s hs h
  exact h (le_of_lt hs)

/-- **The past side is a past set along a causal curve of `Reg M`.** -/
theorem pastSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic) (hS : IsE0C1SpacelikeCauchy M S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (hb : e b ∈ Dat.pastSide) (hab : a ≤ b) : e a ∈ Dat.pastSide := by
  set A : Set ℝ := {r | e (-r) ∈ Dat.pastSide} with hA
  have hcl : IsClosed A :=
    (Dat.isClosed_preimage_pastSide hGH hS he.continuous he0).preimage continuous_neg
  have hb' : -b ∈ A := by simp only [hA, mem_setOf_eq, neg_neg]; exact hb
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) hb'
    (b := -a) fun x hx => by
      have h := Dat.eventually_pastSide he he0 (t := -x) (by simpa [hA] using hx.1)
      have h' := (continuous_neg.tendsto x).eventually h
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h'] with r hr hr'
      exact hr' (neg_le_neg (le_of_lt hr))
  have := hsub (right_mem_Icc.2 (neg_le_neg hab))
  simpa [hA] using this

/-- **A causal curve of `Reg M` lying in `Σ*` over a segment is constant there.** -/
theorem eq_of_forall_mem_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : IsE0C1SpacelikeCauchy M S) {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ r ∈ Icc a b, e r ∈ Dat.sigmaStar) : e b = e a := by
  have hcl : IsClosed {r | e r = e a} := isClosed_eq he.continuous continuous_const
  refine (IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) rfl
    fun x hx => ?_) (right_mem_Icc.2 hab)
  have hxa : e x = e a := hx.1
  have hev := Dat.eventually_eq_of_sigmaStar hGH hS he (h x (Ico_subset_Icc_self hx.2))
  filter_upwards [Ioo_mem_nhdsGT hx.2.2, nhdsWithin_le_nhds hev] with s hs h'
  show e s = e a
  rw [← hxa]
  exact h' (h s ⟨hx.2.1.trans hs.1.le, hs.2.le⟩)


end SurgeryData

end CauchyG3

/-! ### §5d The global part of the surgery, one obstruction per declaration -/

/-- **(G2) Remark 2.12** (`rem:curve_spear`, B21 l.913–915): the component through `t₀` of the
trace of an inextensible causal curve of `Reg M` on a spear of the surgery is, in the spear's
coordinates, a spear arc (the K-3 hypotheses of Lemma 2.10), `M` globally hyperbolic (DEC-125
(d)). **Proved** (WP-44e):
`SpearSurgeryDatum.isSpearArc_of_inextensible`, read through `surgery_flatCausality_e0RegM_eq`. -/
theorem rem_curve_spear (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (Dat : SurgeryData M S) {I : Set ℝ}
    {c : ℝ → e0RegMFlat M}
    (hc : (Causal.Flat.flatCausality 2 (e0RegMFlat M)).Inextensible ⊤ I c) (i : Dat.ι) {t₀ : ℝ}
    (ht₀ : t₀ ∈ I) (hin : regVal M (c t₀) ∈ (Dat.D i).spearSet) :
    (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (regVal M (c t)))
      (connectedComponentIn {t ∈ I | regVal M (c t) ∈ (Dat.D i).spearSet} t₀) := by
  have hc' : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ I c := by
    rw [← surgery_flatCausality_e0RegM_eq]; exact hc
  exact (Dat.D i).isSpearArc_of_inextensible hGH hc' ht₀ hin

/-- **(G3) `Σ*` is a Cauchy surface of `Reg M`** (B21 l.1093: « by Remark 2.12 and Corollary 2.11
applied in each spear neighborhood, a Cauchy-surface of `M*` »), from Remark 2.12 (`hrem`, proved
as `rem_curve_spear`). **Proved** (WP-46e fixer, §5g): on a reparametrisation over `ℝ`, the curve
meets both closed sides of `Σ*` (`exists_futSide`, `exists_pastSide`), hence `Σ*` by
connectedness; two of its points on `Σ*` bound a segment lying on both sides
(`futSide_of_le`, `pastSide_of_le`), hence in `Σ*`, along which the curve is constant
(`eq_of_forall_mem_sigmaStar`). -/
theorem SurgeryData.isCauchySurface_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (Dat : SurgeryData M S)
    (hrem : ∀ (I : Set ℝ) (c : ℝ → e0RegMFlat M),
      (Causal.Flat.flatCausality 2 (e0RegMFlat M)).Inextensible ⊤ I c → ∀ (i : Dat.ι) (t₀ : ℝ),
      t₀ ∈ I → regVal M (c t₀) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (regVal M (c t)))
        (connectedComponentIn {t ∈ I | regVal M (c t) ∈ (Dat.D i).spearSet} t₀)) :
    (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg := by
  intro I c hc
  have hc' : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ I c := by
    rw [← surgery_flatCausality_e0RegM_eq]; exact hc
  obtain ⟨-, -, -, hC, hcaus⟩ := regM_facts hGH
  obtain ⟨φ, -, -, hφr, hd⟩ := hc'.reparam hC hcaus (regM_Jminus_ne hGH) (regM_Jplus_ne hGH)
  set d : ℝ → E0LM.e0RegM M := c ∘ φ with hd_def
  have hdf : (Causal.Flat.flatCausality 2 (e0RegMFlat M)).Inextensible ⊤ univ d := by
    have h := hd
    rw [← surgery_flatCausality_e0RegM_eq] at h
    exact h
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  have he0 : ∀ t, e t ∉ E0CBG.S0 M := fun t => (d t).2
  have harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀) :=
    fun i s₀ h => hrem univ d hdf i s₀ trivial h
  obtain ⟨tF, htF⟩ := Dat.exists_futSide hGH hS hd harc
  obtain ⟨tP, htP⟩ := Dat.exists_pastSide hGH hS hd harc
  obtain ⟨t, -, htF', htP'⟩ := isPreconnected_closed_iff.1 isPreconnected_univ _ _
    (Dat.isClosed_preimage_futSide hGH hS he.continuous he0)
    (Dat.isClosed_preimage_pastSide hGH hS he.continuous he0)
    (fun t _ => Dat.mem_sides_of_notMem_S0 hGH hS (he0 t)) ⟨tF, trivial, htF⟩ ⟨tP, trivial, htP⟩
  have hts : e t ∈ Dat.sigmaStar := Dat.mem_sigmaStar_of_sides hGH hS htF' htP'
  have huniq : ∀ a b, a ≤ b → e a ∈ Dat.sigmaStar → e b ∈ Dat.sigmaStar → e b = e a := by
    intro a b hab ha hb
    refine Dat.eq_of_forall_mem_sigmaStar hGH hS he hab fun r hr => ?_
    exact Dat.mem_sigmaStar_of_sides hGH hS
      (Dat.futSide_of_le hGH hS he he0 (Dat.sigmaStar_subset_sides ha).1 hr.1)
      (Dat.pastSide_of_le hGH hS he he0 (Dat.sigmaStar_subset_sides hb).2 hr.2)
  refine ⟨d t, ⟨⟨φ t, hφr ▸ mem_range_self t, rfl⟩, hts⟩, ?_⟩
  rintro y ⟨⟨t', ht', rfl⟩, hy⟩
  obtain ⟨s', rfl⟩ : t' ∈ range φ := hφr ▸ ht'
  have hy' : e s' ∈ Dat.sigmaStar := hy
  show d s' = d t
  apply Subtype.ext
  rcases le_total s' t with h | h
  · exact (huniq s' t h hy' hts).symm
  · exact huniq t s' h hts hy'

omit [SecondCountableTopology M] in
/-- **(G4a) `Σ*` is spacelike Lipschitz at the points of the cusps** (Lemma 2.7, read in the flat
charts of `Reg M`). **Proved** (WP-46e): `SurgeryData.isSpacelikeLipschitzAt_cusp_interior`
(`r < R`) and `SurgeryData.isSpacelikeLipschitzAt_cusp_rim` (`r = R`, the corner along `C = C*`). -/
theorem SurgeryData.isSpacelikeLipschitzAt_cusp {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M}
    (hy : regVal M y ∈ (Dat.D i).cusp) : IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
  rcases hx.2.1.lt_or_eq with h | h
  · exact Dat.isSpacelikeLipschitzAt_cusp_interior i hx h hxy.symm
  · exact Dat.isSpacelikeLipschitzAt_cusp_rim hS i hx h hxy.symm

omit [SecondCountableTopology M] in
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
metrically complete », no proof printed; DEC-31). **Proved** (WP-46e):
`SurgeryData.completeSpace_sigmaStar_of_delta`, through B21 Lemma 2.8's `log r` estimate on the
glued surface (`SurgeryData.ofReal_abs_logRad_sub_le_edist`). -/
theorem SurgeryData.completeSpace_sigmaStar {S : Set M} (hS : IsE0C1SpacelikeCauchy M S)
    (Dat : SurgeryData M S) :
    CompleteSpace (Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) :=
  Dat.completeSpace_sigmaStar_of_delta hS (fun i => (Dat.D i).delta)
    (Dat.isSpacelikeLipschitz_sigmaStar hS)

/-- **`Reg M` is Cauchy-complete, from a `C¹` spacelike compact Cauchy surface** (B21 Prop 2.17's
first assertion with B21 l.227's « Cauchy-compact », `𝔼₀` only, `A = {0}`, DEC-125 (e)): the
composition of (G1)–(G5) and Remark 2.12; the topology field of `IsCauchyComplete` is
`Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype` (proved, from (G4)). -/
theorem regM_isCauchyComplete_of_C1 (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) := by
  obtain ⟨Dat⟩ := exists_surgeryData hGH hS hmax
  have hL := Dat.isSpacelikeLipschitz_sigmaStar hS
  exact ⟨Dat.sigmaStarReg,
    Dat.isCauchySurface_sigmaStar hGH hS fun _ _ hc i _ ht₀ hin => rem_curve_spear hGH Dat hc i ht₀ hin,
    hL, Dat.completeSpace_sigmaStar hS, Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype hL⟩

end SurgeryData

end E0Surgery

end GX
