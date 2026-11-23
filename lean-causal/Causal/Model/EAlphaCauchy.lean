import Causal.Model.Massive
import Causal.Model.StaticCauchy
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `E_α`, `α > 0`: `{t = 0}` is a Cauchy surface with the axis kept, and there is none without

Programme target `T-loc-ealpha-cauchy` (`programme/roadmap.toml`; layer 3, localisation, model
`E_alpha`, provides `globally_hyperbolic`; no paper label): `references/sbierski/SYNTHESIS.md:100`
(Q4 #4), Hörmann 1501.00672, Ellis–Schmidt (as quoted by Hörmann), Vickers–Wilson gr-qc/9907105.
`E_α = ℝ × C_α` is `Massive α` with `massive α` (`Causal.Model.Massive`), axis `singLine α`;
**the axis removed** is `massive α` on the open set `regOpens α = ℝ × (C_α \ {apex})` (kb/0001).
Each assertion is proved as well for Hörmann's and Vickers–Wilson's 3+1 conical spacetime
`ℝ_t × C_α × ℝ_z` (`cosmicString α`), both as instances of statements about any static `ℝ × X`
with the cylinder over a closed `A ⊆ X` reached by a ray removed (`staticCausality.IsRayTo`, in
`Causal.Model.StaticCauchy`).

* **`T-loc-ealpha-cauchy/1-cauchy-axis-kept`** — `massive_globallyHyperbolic_isCauchySurface`:
  `E_α` is globally hyperbolic and `{t = 0}` is a Cauchy surface (DEC-14), as is every slice
  (`massive_isCauchySurface_slice`); `t − t₀` is a Cauchy time function; the axis is an inextensible
  causal curve, meeting `{t = t₀}` at `(t₀, apex)` (`massive_inextensible_singLine`,
  `singLine_inter_slice`). 3+1: `cosmicString_globallyHyperbolic_isCauchySurface`.
* **`T-loc-ealpha-cauchy/2-axis-removed`** — `not_isCauchySurfaceOn_regOpens_slice`: `{t = 0} ∩ reg`
  is not a Cauchy surface of `reg(E_α)`; the curve is `massive_infall 0`, falling radially into the
  axis at speed `1/2`, inextensible in `reg(E_α)`, chronal on every segment, all of it in `{t < 0}`.
  Stronger: no subset of any slice is one (`not_isCauchySurfaceOn_regOpens_of_subset_slice`);
  **`reg(E_α)` has no Cauchy surface at all** (`not_exists_isCauchySurfaceOn_regOpens`,
  Ellis–Schmidt's claim) and is not globally hyperbolic (`not_globallyHyperbolicOn_regOpens`).
  3+1: `cosmicString_not_isCauchySurfaceOn_offAxis_slice`,
  `cosmicString_not_exists_isCauchySurfaceOn_offAxis`, `cosmicString_not_globallyHyperbolicOn_offAxis`.
* **`T-loc-ealpha-cauchy/3-past-through-axis`** — `massive_Jminus_axis_inter_slice`: for
  `x = (t₀, apex)`, `J⁻(x) ∩ {t = 0} = {t = 0, r ≤ t₀}`, and the past null cone
  `(J⁻ \ I⁻)(x) ∩ {t = 0} = {t = 0, r = t₀}` (`massive_nullCone_axis_inter_slice`); for every `x`,
  `J^∓(x) ∩ {t = t₁}` is a closed ball of `C_α` (`massive_Jminus_inter_slice`,
  `massive_Jplus_inter_slice`), compact; `J⁻(x) = J⁻_reg(x) ∪ ⋃_{ξ ∈ J⁻(x) ∩ axis} J⁻(ξ)`
  (`massive_Jminus_eq_reg_union_axis`). 3+1: `r² + (z − z₀)² ≤ t₀²`
  (`cosmicString_Jminus_axis_inter_slice`), `= t₀²` on the null cone.
* **`T-loc-ealpha-cauchy/4-ladder`** — the ladder's side conditions for `massive α`
  (`massive_noCausalEndpoint`, `massive_chronalNeighbours`, `massive_causallyOpen`,
  `massive_stronglyCausalOpen`, `massive_hasTimeFunction`, `massive_curvesExtend`, …) and the
  ladder properties for `cosmicString α` (`cosmicString_*`); `causally_plain` is not instantiated
  for either.

> Thus Ellis and Schmidt concluded that “there can be no global Cauchy surfaces in these
> space-times”. (`hormann2015conical.txt:500–501`)

> We will check that ρ is an L∞ Riemann metric on R3 and that {t} × R3 is a Cauchy
> hypersurface for gα in an appropriate sense: [footnote] Namely, defined as usual by requiring
> that timelike inextendible curves meet the surface exactly once (`hormann2015conical.txt:271–277`)
> […] hence the curve γ must hit {t} × R3 at least once, and by strict monotonicity of γ0 at most
> once. (`:326–327`)

> for a point x on the axis, the past null cone Ĉ0−(x) is given in quasi-Cartesian coordinates by
> the usual Minkowskian formula. (`vickers2000generalized.txt:1217–1218`) The solution at x depends
> not just on the initial data on C0−(x) ∩ S but also on points in C0−(ξ) ∩ S with
> ξ ∈ C0−(x) ∩ Λ. (`:1317–1318`)

## Hypothesis checklist

| source | here |
|---|---|
| Hörmann: `R⁴`, `−dt² + dr² + α_H² r² dφ² + dz²`, `0 < α_H < 1` (`:23–25`) | ✓ `cosmicString α`, total angle `α = 2π α_H`; ⚠ weakened: every `α > 0` (excess angles too); and the 2+1 `E_α` |
| Hörmann: `L∞` metric, `C¹` timelike curves; Cauchy = met once by timelike inextendible curves | ⚠ reading: ETT's curves (DEC-6; `Causal.Static`'s 1-Lipschitz graphs), Cauchy surfaces met once by every inextensible **causal** curve (DEC-14), inextensibility by extension (DEC-11, DEC-13) |
| Ellis–Schmidt: the singular set deleted | ✓ the open set `ℝ × (C_α \ {apex})` with `massive α` (kb/0001) |
| Vickers–Wilson: the past null cone of an axis point | ✓ `J⁻`, `I⁻`, `J⁻ \ I⁻` on `{t = 0}` |
| target: GH and the Cauchy surface as the ladder's definitions | ✓ `Causality.GloballyHyperbolic`, `Causality.IsCauchySurface`, `IsCauchySurfaceOn` |

## SCOPE (disclosed)

* **"E_α × ℝ"** is read by the dispatch as `Massive α = ℝ_t × C_α` (ETT's 2+1 `E_α`); Hörmann's and
  Vickers–Wilson's spacetime is `E_α × ℝ_z` (3+1). Both readings are proved; the 3+1 one uses the
  `L²` product `WithLp 2 (C_α × ℝ)`, proper and geodesic (`properSpace_withLpTwo`,
  `GeodesicSpace.withLpTwo`), and Hörmann's `α_H` is `α / 2π` here.
* The Colombeau / `L∞` notions of the sources (generalized curves, Clarke's `□`-hyperbolicity) are
  not formalized; the statements here are ETT's, which keep the axis as points.
* "The axis removed" is the causality of `E_α` on `reg(E_α)` (`IsCauchySurfaceOn`,
  `GloballyHyperbolicOn`): curves and extensions inside `reg`. Since `≤_U` is defined by curves in
  `U`, this is the causality built from `reg`'s own curves.
* (3) "through axis points" is read as `x` on the axis; the formula for every `x` and the
  decomposition through the axis are given too. The decomposition does not claim its second part
  is needed (for `α < 2π` the regular past may already contain every regular point).
* **Tidied by T-loc-ealpha-tidy.** The statements about any static `ℝ × X` (slices, the ladder's
  side conditions, `J^∓ ∩ {t = t₁}`, the cylinder over a closed `A` reached by a ray removed) are
  in `Causal.Model.StaticCauchy`, which this module imports, with the same full names
  (`Causal.staticCausality.*`); the model-free `Causality.inextensible_Iio_of_tendsto_not_mem` is in
  the ETT-layer `Causal.InextensiblePiece`, same name. The `L²` projections are mathlib's
  `WithLp.dist_fst_le`, `WithLp.dist_snd_le` (this module's duplicates are gone), and
  `Causal.CBG.Pgcd`, unused, is no longer imported.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-! The model-free lemma `Causality.inextensible_Iio_of_tendsto_not_mem` is in
`Causal.InextensiblePiece`, and the statements about any static `ℝ × X` (namespace
`staticCausality`: `isCauchySurface_slice`, the ladder's side conditions, `Jminus_inter_slice`, …,
`IsRayTo`, `Jminus_eq_off_union`) are in `Causal.Model.StaticCauchy` (T-loc-ealpha-tidy, same full
names). -/

/-! ### (1)–(4) for `E_α = ℝ × C_α` -/

variable {α : ℝ} [Fact (0 < α)]

/-- `t − t₀` is a Cauchy time function of `E_α`. -/
theorem massive_isCauchyTimeFunction_sub (t₀ : ℝ) :
    (massive α).IsCauchyTimeFunction fun p => p.1 - t₀ :=
  staticCausality.isCauchyTimeFunction_sub_const t₀

/-- **Every slice `{t = t₀}` of `E_α` is a Cauchy surface.** -/
theorem massive_isCauchySurface_slice (t₀ : ℝ) :
    (massive α).IsCauchySurface {p : Massive α | p.1 = t₀} :=
  staticCausality.isCauchySurface_slice t₀

/-- **`{t = 0}` is a Cauchy surface of `E_α`.** -/
theorem massive_isCauchySurface_zero : (massive α).IsCauchySurface {p : Massive α | p.1 = 0} :=
  massive_isCauchySurface_slice 0

/-- **`E_α` is globally hyperbolic and `{t = 0}` is a Cauchy surface.** -/
theorem massive_globallyHyperbolic_isCauchySurface :
    (massive α).GloballyHyperbolic ∧ (massive α).IsCauchySurface {p : Massive α | p.1 = 0} :=
  ⟨massive_globallyHyperbolic, massive_isCauchySurface_zero⟩

/-- The axis, run over `ℝ`, is an inextensible causal curve of `E_α`. -/
theorem massive_inextensible_singLine :
    (massive α).Inextensible ⊤ univ (fun τ => ((τ, Cone.apex) : Massive α)) :=
  Causality.inextensible_of_unbounded (f := Prod.fst) (fun _ _ h => (staticCausality.le_iff.1 h).1)
    ⟨⟨0, trivial⟩, ordConnected_univ, fun _ _ _ _ =>
      (singLine_chronalCurveOn (W := ⊤) fun _ _ => trivial).causalCurveOn⟩
    (fun B => ⟨B + 1, by simp⟩) (fun B => ⟨B - 1, by simp⟩)

omit [Fact (0 < α)] in
/-- The axis meets the slice `{t = t₀}` in exactly the point `(t₀, apex)`. -/
theorem singLine_inter_slice (t₀ : ℝ) :
    singLine α ∩ {p : Massive α | p.1 = t₀} = {((t₀, Cone.apex) : Massive α)} := by
  ext p
  simp only [singLine, mem_inter_iff, mem_setOf_eq, mem_singleton_iff, Prod.ext_iff]
  tauto

/-! #### The ladder's side conditions, instantiated for `E_α` -/

theorem massive_noCausalEndpoint : (massive α).NoCausalEndpoint := staticCausality.noCausalEndpoint

theorem massive_chronalNeighbours : (massive α).ChronalNeighbours :=
  staticCausality.chronalNeighbours

theorem massive_causallyOpen : (massive α).CausallyOpen := staticCausality.causallyOpen

theorem massive_causallyOpenFuture : (massive α).CausallyOpenFuture :=
  massive_causallyOpen.future

theorem massive_stronglyCausalOpen : (massive α).StronglyCausalOpen :=
  staticCausality.stronglyCausalOpen

theorem massive_locallyPushUp : (massive α).LocallyPushUp := massive_pushUp.locallyPushUp

theorem massive_causallyCompact : (massive α).CausallyCompact :=
  massive_globallyHyperbolic.causallyCompact

theorem massive_hasTimeFunction : (massive α).HasTimeFunction := staticCausality.hasTimeFunction

theorem massive_curvesExtend : (massive α).CurvesExtend := staticCausality.curvesExtend

/-! #### The axis removed -/

omit [Fact (0 < α)] in
theorem isOpen_regPart : IsOpen (regPart α) :=
  (isClosed_eq continuous_snd continuous_const).isOpen_compl

/-- The regular part `reg(E_α)`, as an open set: `ℝ × (C_α \ {apex})`. -/
noncomputable def regOpens (α : ℝ) : Opens (Massive α) :=
  staticCausality.offOpens (isClosed_singleton (x := (Cone.apex : Cone α)))

omit [Fact (0 < α)] in
theorem coe_regOpens : (regOpens α : Set (Massive α)) = regPart α := rfl

/-- The point of radius `max u 0` on the ray of direction `0` of `C_α`. -/
noncomputable def massiveRadial (u : ℝ) : Cone α := Cone.polar (u, 0)

omit [Fact (0 < α)] in
/-- Two points of one ray are at the distance of their radii. -/
theorem dist_massiveRadial (u v : ℝ) :
    dist (massiveRadial (α := α) u) (massiveRadial v) = |max u 0 - max v 0| :=
  ConePoint.dist_same_dir (p := ConePoint.of u 0) (q := ConePoint.of v 0) rfl

omit [Fact (0 < α)] in
theorem dist_massiveRadial_le (u v : ℝ) :
    dist (massiveRadial (α := α) u) (massiveRadial v) ≤ |u - v| := by
  rw [dist_massiveRadial]; exact abs_max_sub_max_le_abs u v 0

omit [Fact (0 < α)] in
theorem rad_massiveRadial (u : ℝ) : Cone.rad (massiveRadial (α := α) u) = max u 0 :=
  Cone.rad_mk _

omit [Fact (0 < α)] in
theorem massiveRadial_eq_apex_iff {u : ℝ} : massiveRadial (α := α) u = Cone.apex ↔ u ≤ 0 := by
  rw [← Cone.rad_eq_zero, rad_massiveRadial, max_eq_right_iff]

omit [Fact (0 < α)] in
/-- The ray of direction `0` of `C_α` reaches the apex. -/
theorem massiveRadial_isRayTo :
    staticCausality.IsRayTo ({Cone.apex} : Set (Cone α)) (massiveRadial (α := α)) :=
  ⟨dist_massiveRadial_le, massiveRadial_eq_apex_iff.2 le_rfl,
    fun _ hu h => not_le.2 hu (massiveRadial_eq_apex_iff.1 h)⟩

/-- **The witness**: the curve falling radially into the axis at speed `1/2`, reaching it at time
`t₀`, is an inextensible causal curve of `reg(E_α)`, chronal on every segment, missing
`{t = t₀}`. -/
theorem massive_infall (t₀ : ℝ) :
    (massive α).Inextensible (regOpens α) (Iio t₀)
        (staticCausality.rayCurve massiveRadial fun τ => (t₀ - τ) / 2) ∧
      (∀ a < t₀, ∀ b < t₀, (massive α).ChronalCurveOn (regOpens α)
        (staticCausality.rayCurve massiveRadial fun τ => (t₀ - τ) / 2) a b) ∧
      ∀ τ < t₀, (staticCausality.rayCurve (massiveRadial (α := α))
        (fun τ => (t₀ - τ) / 2) τ).1 ≠ t₀ :=
  massiveRadial_isRayTo.infall isClosed_singleton t₀

/-- **No subset of a slice `{t = t₀}` is a Cauchy surface of `reg(E_α)`.** -/
theorem not_isCauchySurfaceOn_regOpens_of_subset_slice (t₀ : ℝ) {S : Set (Massive α)}
    (hS : S ⊆ {p | p.1 = t₀}) : ¬ (massive α).IsCauchySurfaceOn (regOpens α) S :=
  massiveRadial_isRayTo.not_isCauchySurfaceOn_of_subset_slice isClosed_singleton t₀ hS

/-- **`{t = 0} ∩ reg(E_α)` is not a Cauchy surface of `reg(E_α)`.** -/
theorem not_isCauchySurfaceOn_regOpens_slice :
    ¬ (massive α).IsCauchySurfaceOn (regOpens α) ({p : Massive α | p.1 = 0} ∩ regPart α) :=
  not_isCauchySurfaceOn_regOpens_of_subset_slice 0 inter_subset_left

/-- **`reg(E_α)` has no Cauchy surface at all** (Ellis–Schmidt). -/
theorem not_exists_isCauchySurfaceOn_regOpens :
    ¬ ∃ S : Set (Massive α), (massive α).IsCauchySurfaceOn (regOpens α) S :=
  massiveRadial_isRayTo.not_exists_isCauchySurfaceOn isClosed_singleton

/-- **`reg(E_α)` is not globally hyperbolic.** -/
theorem not_globallyHyperbolicOn_regOpens : ¬ (massive α).GloballyHyperbolicOn (regOpens α) :=
  massiveRadial_isRayTo.not_globallyHyperbolicOn isClosed_singleton

/-! #### `J⁻(x) ∩ {t = t₁}` through the axis -/

/-- `J⁻(x) ∩ {t = t₁}` is the closed ball of radius `x.1 − t₁` of `C_α` about `x.2`. -/
theorem massive_Jminus_inter_slice (x : Massive α) (t₁ : ℝ) :
    (massive α).Jminus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (x.1 - t₁) :=
  staticCausality.Jminus_inter_slice x t₁

/-- `J⁺(x) ∩ {t = t₁}` is the closed ball of radius `t₁ − x.1` of `C_α` about `x.2`. -/
theorem massive_Jplus_inter_slice (x : Massive α) (t₁ : ℝ) :
    (massive α).Jplus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (t₁ - x.1) :=
  staticCausality.Jplus_inter_slice x t₁

/-- **Through an axis point `x = (t₀, apex)`: `J⁻(x) ∩ {t = 0} = {t = 0, r ≤ t₀}`**, the disc of
radius `t₀` about the axis. -/
theorem massive_Jminus_axis_inter_slice (t₀ : ℝ) :
    (massive α).Jminus ⊤ {((t₀, Cone.apex) : Massive α)} ∩ {p | p.1 = 0} =
      {p : Massive α | p.1 = 0 ∧ Cone.rad p.2 ≤ t₀} := by
  rw [massive_Jminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_closedBall, mem_setOf_eq, Cone.rad,
    dist_comm Cone.apex p.2, sub_zero]

/-- **The past null cone of an axis point on `{t = 0}` is the circle `r = t₀`** (Vickers–Wilson's
"usual Minkowskian formula"). -/
theorem massive_nullCone_axis_inter_slice (t₀ : ℝ) :
    ((massive α).Jminus ⊤ {((t₀, Cone.apex) : Massive α)} \
        (massive α).Iminus ⊤ {((t₀, Cone.apex) : Massive α)}) ∩ {p | p.1 = 0} =
      {p : Massive α | p.1 = 0 ∧ Cone.rad p.2 = t₀} := by
  rw [staticCausality.Jminus_diff_Iminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_sphere, mem_setOf_eq, Cone.rad,
    dist_comm Cone.apex p.2, sub_zero]

/-- `J^±(x) ∩ {t = t₁}` is compact. -/
theorem isCompact_massive_Jminus_inter_slice (x : Massive α) (t₁ : ℝ) :
    IsCompact ((massive α).Jminus ⊤ {x} ∩ {p | p.1 = t₁}) ∧
      IsCompact ((massive α).Jplus ⊤ {x} ∩ {p | p.1 = t₁}) :=
  staticCausality.isCompact_Jminus_inter_slice x t₁

/-- **A causal past is the regular causal past plus the pasts of its axis points**: every
`z ≤ x` is joined to `x` in `reg(E_α)`, or through a point `ξ` of the axis with `z ≤ ξ ≤ x`. -/
theorem massive_Jminus_eq_reg_union_axis (x : Massive α) :
    (massive α).Jminus ⊤ {x} = (massive α).Jminus (regOpens α) {x} ∪
      ⋃ ξ ∈ (massive α).Jminus ⊤ {x} ∩ singLine α, (massive α).Jminus ⊤ {ξ} :=
  staticCausality.Jminus_eq_off_union isClosed_singleton x

/-! ### The 3+1 conical spacetime `ℝ_t × C_α × ℝ_z` (Hörmann, Vickers–Wilson) -/

section WithLpTwo

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The `L²` product distance. -/
theorem withLp_dist_two (f g : WithLp 2 (X × Y)) :
    dist f g = √(dist f.fst g.fst ^ 2 + dist f.snd g.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num), ENNReal.toReal_ofNat, Real.rpow_two, Real.rpow_two,
    Real.sqrt_eq_rpow]

/-- The `L²` product of two geodesic spaces is geodesic: run both geodesics at once. -/
instance GeodesicSpace.withLpTwo [GeodesicSpace X] [GeodesicSpace Y] :
    GeodesicSpace (WithLp 2 (X × Y)) where
  exists_geodesic x y := by
    obtain ⟨g₁, h₁0, h₁1, h₁⟩ := GeodesicSpace.exists_geodesic x.fst y.fst
    obtain ⟨g₂, h₂0, h₂1, h₂⟩ := GeodesicSpace.exists_geodesic x.snd y.snd
    have hx : WithLp.toLp 2 (x.fst, x.snd) = x := rfl
    have hy : WithLp.toLp 2 (y.fst, y.snd) = y := rfl
    refine ⟨fun s => WithLp.toLp 2 (g₁ s, g₂ s), ?_, ?_, fun s hs s' hs' => ?_⟩
    · show WithLp.toLp 2 (g₁ 0, g₂ 0) = x
      rw [h₁0, h₂0, hx]
    · show WithLp.toLp 2 (g₁ 1, g₂ 1) = y
      rw [h₁1, h₂1, hy]
    · rw [withLp_dist_two, withLp_dist_two]
      show √(dist (g₁ s) (g₁ s') ^ 2 + dist (g₂ s) (g₂ s') ^ 2) =
        |s - s'| * √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2)
      rw [h₁ s hs s' hs', h₂ s hs s' hs', mul_pow, mul_pow, ← mul_add,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]

/-- The `L²` product of two proper spaces is proper. -/
instance properSpace_withLpTwo [ProperSpace X] [ProperSpace Y] :
    ProperSpace (WithLp 2 (X × Y)) := by
  refine ⟨fun x R => ?_⟩
  have hK : IsCompact (WithLp.toLp 2 '' (closedBall x.fst R ×ˢ closedBall x.snd R)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      (WithLp.prod_continuous_toLp _ _ _)
  refine hK.of_isClosed_subset isClosed_closedBall fun y hy => ⟨(y.fst, y.snd), ⟨?_, ?_⟩, rfl⟩
  · rw [mem_closedBall] at hy ⊢; exact (WithLp.dist_fst_le y x).trans hy
  · rw [mem_closedBall] at hy ⊢; exact (WithLp.dist_snd_le y x).trans hy

end WithLpTwo

/-- The space of the 3+1 conical spacetime: `C_α × ℝ_z` with the `L²` product metric, the length
metric of `dr² + r² dθ² + dz²`. -/
abbrev StringSpace (α : ℝ) : Type := WithLp 2 (Cone α × ℝ)

/-- **The conical spacetime of a straight cosmic string**, `E_α × ℝ_z = ℝ_t × C_α × ℝ_z`, metric
`−dt² + dr² + r² dθ² + dz²` (Hörmann's `lα` with total angle `α = 2π α_H`). -/
abbrev CosmicString (α : ℝ) : Type := ℝ × StringSpace α

/-- Its causality: the static causality over `StringSpace α` (`defi:causal_Ealpha`'s
construction). -/
noncomputable abbrev cosmicString (α : ℝ) [Fact (0 < α)] : Causality (CosmicString α) :=
  staticCausality (StringSpace α)

/-- The axis `{r = 0}` of `StringSpace α`; the string's world-sheet is `ℝ × stringAxis α`. -/
def stringAxis (α : ℝ) : Set (StringSpace α) := {w | w.fst = Cone.apex}

omit [Fact (0 < α)] in
theorem isClosed_stringAxis : IsClosed (stringAxis α) :=
  isClosed_eq (WithLp.continuous_fst _ _ _) continuous_const

/-- The conical spacetime with the world-sheet of the string removed, as an open set. -/
noncomputable def stringOffAxis (α : ℝ) : Opens (CosmicString α) :=
  staticCausality.offOpens isClosed_stringAxis

/-- The ray of direction `0` at height `z = 0`. -/
noncomputable def stringRadial (u : ℝ) : StringSpace α := WithLp.toLp 2 (massiveRadial u, 0)

omit [Fact (0 < α)] in
theorem stringRadial_isRayTo : staticCausality.IsRayTo (stringAxis α) (stringRadial (α := α)) := by
  refine ⟨fun u v => ?_, massiveRadial_eq_apex_iff.2 le_rfl,
    fun _ hu h => not_le.2 hu (massiveRadial_eq_apex_iff.1 h)⟩
  rw [withLp_dist_two]
  show √(dist (massiveRadial (α := α) u) (massiveRadial v) ^ 2 + dist (0 : ℝ) 0 ^ 2) ≤ |u - v|
  rw [dist_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq dist_nonneg]
  exact dist_massiveRadial_le u v

/-- **The conical spacetime is globally hyperbolic and every slice is a Cauchy surface**, with the
string kept (Hörmann's "`{t} × ℝ³` is a Cauchy hypersurface"). -/
theorem cosmicString_globallyHyperbolic_isCauchySurface (t₀ : ℝ) :
    (cosmicString α).GloballyHyperbolic ∧
      (cosmicString α).IsCauchySurface {p : CosmicString α | p.1 = t₀} :=
  ⟨staticCausality.globallyHyperbolic, staticCausality.isCauchySurface_slice t₀⟩

/-- With the string removed, `{t = 0}` minus the string is not a Cauchy surface. -/
theorem cosmicString_not_isCauchySurfaceOn_offAxis_slice :
    ¬ (cosmicString α).IsCauchySurfaceOn (stringOffAxis α)
      ({p : CosmicString α | p.1 = 0} ∩ stringOffAxis α) :=
  stringRadial_isRayTo.not_isCauchySurfaceOn_of_subset_slice isClosed_stringAxis 0
    inter_subset_left

/-- **With the string removed there is no Cauchy surface at all** (Ellis–Schmidt). -/
theorem cosmicString_not_exists_isCauchySurfaceOn_offAxis :
    ¬ ∃ S : Set (CosmicString α), (cosmicString α).IsCauchySurfaceOn (stringOffAxis α) S :=
  stringRadial_isRayTo.not_exists_isCauchySurfaceOn isClosed_stringAxis

/-- With the string removed the spacetime is not globally hyperbolic. -/
theorem cosmicString_not_globallyHyperbolicOn_offAxis :
    ¬ (cosmicString α).GloballyHyperbolicOn (stringOffAxis α) :=
  stringRadial_isRayTo.not_globallyHyperbolicOn isClosed_stringAxis

/-- **Through a point `(t₀, apex, z₀)` of the string: `J⁻ ∩ {t = 0}` is the Minkowskian ball
`r² + (z − z₀)² ≤ t₀²`** (Vickers–Wilson's "usual Minkowskian formula"). -/
theorem cosmicString_Jminus_axis_inter_slice (t₀ z₀ : ℝ) :
    (cosmicString α).Jminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)} ∩
        {p | p.1 = 0} =
      {p : CosmicString α | p.1 = 0 ∧ 0 ≤ t₀ ∧ Cone.rad p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 ≤ t₀ ^ 2} := by
  rw [staticCausality.Jminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_closedBall, mem_setOf_eq, sub_zero]
  rw [withLp_dist_two]
  show p.1 = 0 ∧ √(dist p.2.fst Cone.apex ^ 2 + dist p.2.snd z₀ ^ 2) ≤ t₀ ↔
    p.1 = 0 ∧ 0 ≤ t₀ ∧ dist Cone.apex p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 ≤ t₀ ^ 2
  rw [Real.sqrt_le_iff, dist_comm p.2.fst, Real.dist_eq, sq_abs]

/-- The past null cone of a point of the string on `{t = 0}`: the sphere
`r² + (z − z₀)² = t₀²`, `t₀ ≥ 0`. -/
theorem cosmicString_nullCone_axis_inter_slice (t₀ z₀ : ℝ) :
    ((cosmicString α).Jminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)} \
        (cosmicString α).Iminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)}) ∩
        {p | p.1 = 0} =
      {p : CosmicString α | p.1 = 0 ∧ 0 ≤ t₀ ∧ Cone.rad p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 = t₀ ^ 2} := by
  rw [staticCausality.Jminus_diff_Iminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_sphere, mem_setOf_eq, sub_zero]
  rw [withLp_dist_two]
  show p.1 = 0 ∧ √(dist p.2.fst Cone.apex ^ 2 + dist p.2.snd z₀ ^ 2) = t₀ ↔
    p.1 = 0 ∧ 0 ≤ t₀ ∧ dist Cone.apex p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 = t₀ ^ 2
  rw [dist_comm p.2.fst Cone.apex, Real.dist_eq, sq_abs]
  constructor
  · rintro ⟨h1, h⟩
    have ht : 0 ≤ t₀ := h ▸ Real.sqrt_nonneg _
    exact ⟨h1, ht, (Real.sqrt_eq_iff_eq_sq (by positivity) ht).1 h⟩
  · rintro ⟨h1, ht, h⟩
    exact ⟨h1, (Real.sqrt_eq_iff_eq_sq (by positivity) ht).2 h⟩

/-- A causal past of the conical spacetime is its part off the string plus the pasts of its
points on the string. -/
theorem cosmicString_Jminus_eq_offAxis_union (x : CosmicString α) :
    (cosmicString α).Jminus ⊤ {x} = (cosmicString α).Jminus (stringOffAxis α) {x} ∪
      ⋃ ξ ∈ (cosmicString α).Jminus ⊤ {x} ∩ {p | p.2 ∈ stringAxis α},
        (cosmicString α).Jminus ⊤ {ξ} :=
  staticCausality.Jminus_eq_off_union isClosed_stringAxis x

/-! #### The ladder's properties, instantiated for the conical spacetime -/

theorem cosmicString_isCausal : (cosmicString α).IsCausal := staticCausality.isCausal
theorem cosmicString_stronglyCausal : (cosmicString α).StronglyCausal :=
  staticCausality.stronglyCausal
theorem cosmicString_stronglyCausalOpen : (cosmicString α).StronglyCausalOpen :=
  staticCausality.stronglyCausalOpen
theorem cosmicString_globallyHyperbolic : (cosmicString α).GloballyHyperbolic :=
  staticCausality.globallyHyperbolic
theorem cosmicString_pushUp : (cosmicString α).PushUp := staticCausality.pushUp
theorem cosmicString_causallyOpen : (cosmicString α).CausallyOpen := staticCausality.causallyOpen
theorem cosmicString_causallyOpenFuture : (cosmicString α).CausallyOpenFuture :=
  cosmicString_causallyOpen.future
theorem cosmicString_absolutelyMinimal : (cosmicString α).AbsolutelyMinimal :=
  staticCausality.absolutelyMinimal
theorem cosmicString_causallyArcConnected : (cosmicString α).CausallyArcConnected :=
  staticCausality.causallyArcConnected
theorem cosmicString_tarentin : (cosmicString α).Tarentin := staticCausality.tarentin
theorem cosmicString_hasTimeFunction : (cosmicString α).HasTimeFunction :=
  staticCausality.hasTimeFunction
theorem cosmicString_curvesExtend : (cosmicString α).CurvesExtend := staticCausality.curvesExtend
theorem cosmicString_noCausalEndpoint : (cosmicString α).NoCausalEndpoint :=
  staticCausality.noCausalEndpoint
theorem cosmicString_chronalNeighbours : (cosmicString α).ChronalNeighbours :=
  staticCausality.chronalNeighbours

end Causal
