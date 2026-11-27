import GXScaffold.BTZ.RegCompleteCauchy

/-!
# `GXScaffold.BTZ.LengthCompare` — the induced length of `Σ*` is the DEC-31 length of `S` on their common part, and a rim arc of a spear is at most `π R` long (btz § 5.4)

Target T-btz-length-compare. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`). Row (unmarked,
partial; this file is a tool of step (3) of `btzprop:reg_complete`'s Cauchy-completeness,
`LFSurgeryData.exists_isCompact_of_cauchySeq`, closed with it in `GXScaffold.BTZ.RegCompleteTail`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576: « the proof of
  Cauchy-completeness of Proposition prop:abs_max applies as is » (l.1571), which is B21 l.1093.

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

> Global hyperbolicity follows from Remark \ref{rem:reg_GH} and the proof of Cauchy-complete\-ness
> of Proposition \ref{prop:abs_max} applies as is. (l.1571)

## What is proved (no `sorry`; standard axioms only)

* **The comparison** (A). Both length systems read a regular point in the flat chart of `Reg M`
  at a regular point: `Causal.Flat.chartSys 2 T` for `T ⊆ Reg M`, and `GX.e0SliceSys S` for
  `S ⊆ M` (`e0SliceSys_of_mem`). So on two curves with the same points of `M`
  (`chartSys_eq_e0SliceSys`), the densities, the chart-Lipschitz property, the lengths over an
  interval and the path lengths coincide (`localDensity_chartSys_eq_e0SliceSys`,
  `locLipAt_chartSys_iff_e0SliceSys`, `localLength_chartSys_eq_e0SliceSys`,
  `pathLength_chartSys_eq_e0SliceSys`); only agreement near the time, or on the open interval, is
  asked. A path of `S` lying in `A ∩ Reg M` lifts to a path of `A` read in `Reg M` with the same
  points (`exists_liftPath`), hence of the same length:
  `edist_inducedLength_le_pathLength_e0SliceSys`; conversely a path of `T` lying in `S` lowers to
  one of `S` (`exists_lowerPath`): `edist_e0SliceSys_le_pathLength_chartSys`. For a locally finite spear family
  (`E0SpearFamily.LFSurgeryData`), `T = Σ*` (`sigmaStarReg`): `LFSurgeryData.edist_le_pathLength`.
* **The rim arcs** (B). On the rim `r = R` of a spear datum, the rim point of `z ∈ ℂ`, `‖z‖ = R`,
  is `ψ(τ_Σ(z), z)`; at the angle `φ` it is `SpearSurgeryDatum.rimPt φ`, a regular point of `S`
  on the cusp (`rimPt_mem`, `rimPt_mem_cusp`, `rimPt_mem_regM`), and every point of `S` on the
  rim is one (`eq_rimPt`). In the flat
  chart the arc `φ ↦ rimPt φ` (the rim point `ψ(τ_Σ(R e^{iφ}), R e^{iφ})`) is `g • btzPaperDev(τ(φ), R, φ + k)`, whose velocity has
  Minkowski square `R²` whatever `τ` (the printed metric `−2dτdr + dr² + r²dθ²` at `dr = 0`), so
  the arc from angle `θ₁` to `θ₂` has `S`-length exactly `R |θ₂ − θ₁|`
  (`SpearSurgeryDatum.pathLength_rimArc`), and any two rim points are joined by an arc of `S` of
  length `≤ π R` (`SpearSurgeryDatum.exists_rimPath`, `edist_rimPt_le`). For a locally finite
  family the arc lies in `Σ*` and has the same `Σ*`-length (`LFSurgeryData.edist_rimPt_le`).

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected; second countability is not used |
| the induced length of `Σ*`, of `S` | ✓ read `Causal.Flat.InducedLengthSpace 2 Σ*` (flat charts of `Reg M`) and `LocalLengthSpace (e0SliceSys S)` (DEC-31) |
| spear neighbourhoods (Lemma 2.4, 2.6(ii)) | ✓ `E0Surgery.SpearSurgeryDatum`; (B) uses only `ψ` an `E₀`-morphism, `S`'s trace the graph of `τ_Σ`, the rim `G(R,·) = τ_Σ(R e^{i·})` and `G` `C¹` |

## SCOPE (disclosed)

This file proves tools only; `LFSurgeryData.exists_isCompact_of_cauchySeq` is closed with them in
`GXScaffold.BTZ.RegCompleteTail` (T-btz-reg-complete-tail); `btzprop:reg_complete` stays partial
(`𝔼₀`-scoped).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real ENNReal NNReal unitInterval

open E0 E0Spear E0Surgery

/-! ### (A) The comparison of the two length systems on a common part -/

section Compare

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
  [HasGroupoid M e0Groupoid]

/-- **The two chart systems agree on common points**: a point `y'` of `T ⊆ Reg M` read at `x'`
is the point `y` of `S ⊆ M` read at `x`, when they are the same points of `M`. -/
theorem chartSys_eq_e0SliceSys {S : Set M} {T : Set (e0RegMFlat M)} {x y : S} {x' y' : T}
    (hx : regVal M x' = x) (hy : regVal M y' = y) :
    Causal.Flat.chartSys 2 T x' y' = e0SliceSys S x y := by
  have hx' : (x : M) ∈ E0LM.e0RegM M := hx ▸ (show E0LM.e0RegM M from (x' : e0RegMFlat M)).2
  have hy' : (y : M) ∈ E0LM.e0RegM M := hy ▸ (show E0LM.e0RegM M from (y' : e0RegMFlat M)).2
  rw [e0SliceSys_of_mem hx' hy']
  have e1 : (x' : e0RegMFlat M) = (show e0RegMFlat M from (⟨x, hx'⟩ : E0LM.e0RegM M)) :=
    Subtype.ext (p := fun z : M => z ∈ E0LM.e0RegM M) hx
  have e2 : (y' : e0RegMFlat M) = (show e0RegMFlat M from (⟨y, hy'⟩ : E0LM.e0RegM M)) :=
    Subtype.ext (p := fun z : M => z ∈ E0LM.e0RegM M) hy
  simp only [Causal.Flat.chartSys]
  rw [e1, e2]

/-- **The densities agree** at a time near which the two curves have the same points of `M`. -/
theorem localDensity_chartSys_eq_e0SliceSys {S : Set M} {T : Set (e0RegMFlat M)} {c : ℝ → S}
    {c' : ℝ → T} {t : ℝ} (h : ∀ᶠ s in 𝓝 t, regVal M (c' s) = c s) :
    Causal.Flat.localDensity (Causal.Flat.chartSys 2 T) c' t =
      Causal.Flat.localDensity (e0SliceSys S) c t := by
  have ht : regVal M (c' t) = c t := h.self_of_nhds
  have hev : (fun s => Causal.Flat.chartSys 2 T (c' t) (c' s)) =ᶠ[𝓝 t]
      fun s => e0SliceSys S (c t) (c s) := by
    filter_upwards [h] with s hs
    exact chartSys_eq_e0SliceSys ht hs
  simp only [Causal.Flat.localDensity, hev.deriv_eq]

/-- **Chart-Lipschitz agrees** at a time near which the two curves have the same points. -/
theorem locLipAt_chartSys_iff_e0SliceSys {S : Set M} {T : Set (e0RegMFlat M)} {c : ℝ → S}
    {c' : ℝ → T} {t : ℝ} (h : ∀ᶠ s in 𝓝 t, regVal M (c' s) = c s) :
    Causal.Flat.LocLipAt (Causal.Flat.chartSys 2 T) c' t ↔
      Causal.Flat.LocLipAt (e0SliceSys S) c t := by
  have ht : regVal M (c' t) = c t := h.self_of_nhds
  obtain ⟨δ, hδ, hδP⟩ := Causal.Flat.exists_Icc_subset_of_eventually h
  have key : ∀ s ∈ Icc (t - δ) (t + δ),
      Causal.Flat.chartSys 2 T (c' t) (c' s) = e0SliceSys S (c t) (c s) :=
    fun s hs => chartSys_eq_e0SliceSys ht (hδP s hs)
  constructor
  · rintro ⟨ε, hε, K, hK⟩
    refine ⟨min ε δ, lt_min hε hδ, K, Causal.Flat.lipschitzOnWith_congr_of_eqOn (fun s hs => ?_)
      (hK.mono (Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])))⟩
    exact key s ⟨by linarith [hs.1, min_le_right ε δ], by linarith [hs.2, min_le_right ε δ]⟩
  · rintro ⟨ε, hε, K, hK⟩
    refine ⟨min ε δ, lt_min hε hδ, K, Causal.Flat.lipschitzOnWith_congr_of_eqOn (fun s hs => ?_)
      (hK.mono (Icc_subset_Icc (by linarith [min_le_left ε δ]) (by linarith [min_le_left ε δ])))⟩
    exact (key s ⟨by linarith [hs.1, min_le_right ε δ], by linarith [hs.2, min_le_right ε δ]⟩).symm

/-- **The lengths over `(a, b]` agree** when the curves have the same points on `(a, b)`. -/
theorem localLength_chartSys_eq_e0SliceSys {S : Set M} {T : Set (e0RegMFlat M)} {c : ℝ → S}
    {c' : ℝ → T} {a b : ℝ} (h : ∀ s ∈ Ioo a b, regVal M (c' s) = c s) :
    Causal.Flat.localLength (Causal.Flat.chartSys 2 T) c' a b =
      Causal.Flat.localLength (e0SliceSys S) c a b := by
  unfold Causal.Flat.localLength
  rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Ioc.symm,
    MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Ioc.symm]
  exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun s hs =>
    localDensity_chartSys_eq_e0SliceSys
      (Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun r hr => h r hr)

/-- **The path lengths agree** for two paths with the same points of `M`. -/
theorem pathLength_chartSys_eq_e0SliceSys {S : Set M} {T : Set (e0RegMFlat M)} {x y : S}
    {x' y' : T} (γ : Path x y) (γ' : Path x' y') (h : ∀ t, regVal M (γ' t) = γ t) :
    Causal.Flat.pathLength (Causal.Flat.chartSys 2 T) γ' =
      Causal.Flat.pathLength (e0SliceSys S) γ := by
  have he : ∀ s, regVal M (γ'.extend s) = γ.extend s := fun s => by
    simp only [Path.extend, IccExtend]; exact h _
  have hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 T) γ'.extend ↔
      Causal.Flat.IsLocLip (e0SliceSys S) γ.extend :=
    forall_congr' fun t => locLipAt_chartSys_iff_e0SliceSys (Eventually.of_forall he)
  by_cases hc : Causal.Flat.IsLocLip (e0SliceSys S) γ.extend
  · rw [Causal.Flat.pathLength_of_isLocLip _ hc, Causal.Flat.pathLength_of_isLocLip _ (hL.2 hc)]
    exact localLength_chartSys_eq_e0SliceSys fun s _ => he s
  · rw [Causal.Flat.pathLength_of_not_isLocLip _ hc,
      Causal.Flat.pathLength_of_not_isLocLip _ (mt hL.1 hc)]

/-- `regVal` is continuous (the inclusion of `Reg M`). -/
theorem continuous_regVal : Continuous (regVal M) := continuous_subtype_val

/-- **A path of `S` lying in `A ∩ Reg M` lifts to a path of `A` read in `Reg M`.** -/
theorem exists_liftPath {S A : Set M} {x y : S} (γ : Path x y)
    (h : ∀ t, (γ t : M) ∈ A ∧ (γ t : M) ∈ E0LM.e0RegM M) {x' y' : regSet M A}
    (hx : regVal M x' = x) (hy : regVal M y' = y) :
    ∃ γ' : Path x' y', ∀ t, regVal M (γ' t) = γ t := by
  let f : I → regSet M A := fun t =>
    ⟨(show e0RegMFlat M from (⟨(γ t : M), (h t).2⟩ : E0LM.e0RegM M)), (h t).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp γ.continuous).subtype_mk _).subtype_mk _
  refine ⟨⟨⟨f, hf⟩, ?_, ?_⟩, fun t => rfl⟩
  · apply Subtype.ext; apply Subtype.ext (p := fun z : M => z ∈ E0LM.e0RegM M)
    show (γ 0 : M) = regVal M x'
    rw [γ.source, hx]
  · apply Subtype.ext; apply Subtype.ext (p := fun z : M => z ∈ E0LM.e0RegM M)
    show (γ 1 : M) = regVal M y'
    rw [γ.target, hy]

/-- **A path of `T ⊆ Reg M` lying in `S` maps to a path of `S`.** -/
theorem exists_lowerPath {S : Set M} {T : Set (e0RegMFlat M)} {x' y' : T} (γ' : Path x' y')
    (h : ∀ t, regVal M (γ' t) ∈ S) {x y : S} (hx : regVal M x' = x) (hy : regVal M y' = y) :
    ∃ γ : Path x y, ∀ t, regVal M (γ' t) = γ t := by
  let f : I → S := fun t => ⟨regVal M (γ' t), h t⟩
  have hf : Continuous f :=
    (continuous_regVal.comp (continuous_subtype_val.comp γ'.continuous)).subtype_mk _
  refine ⟨⟨⟨f, hf⟩, ?_, ?_⟩, fun t => rfl⟩
  · apply Subtype.ext; show regVal M (γ' 0) = x; rw [γ'.source, hx]
  · apply Subtype.ext; show regVal M (γ' 1) = y; rw [γ'.target, hy]

/-- **The induced length of `A ⊆ Reg M` is at most the DEC-31 length of a path of `S` lying in
`A ∩ Reg M`.** -/
theorem edist_inducedLength_le_pathLength_e0SliceSys {S A : Set M} {x y : S} (γ : Path x y)
    (h : ∀ t, (γ t : M) ∈ A ∧ (γ t : M) ∈ E0LM.e0RegM M)
    (x' y' : Causal.Flat.InducedLengthSpace 2 (regSet M A))
    (hx : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) x') = x)
    (hy : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) y') = y) :
    edist x' y' ≤ Causal.Flat.pathLength (e0SliceSys S) γ := by
  obtain ⟨γ', hγ'⟩ := exists_liftPath γ h hx hy
  rw [← pathLength_chartSys_eq_e0SliceSys γ γ' hγ']
  exact iInf_le _ γ'

/-- **The DEC-31 length of `S` is at most the induced length of a path of `T ⊆ Reg M` lying in
`S`.** -/
theorem edist_e0SliceSys_le_pathLength_chartSys {S : Set M} {T : Set (e0RegMFlat M)} {x' y' : T}
    (γ' : Path x' y') (h : ∀ t, regVal M (γ' t) ∈ S)
    (x y : Causal.Flat.LocalLengthSpace (e0SliceSys S))
    (hx : regVal M x' = (Causal.Flat.LocalLengthSpace.toSpace (φ := e0SliceSys S) x : M))
    (hy : regVal M y' = (Causal.Flat.LocalLengthSpace.toSpace (φ := e0SliceSys S) y : M)) :
    edist x y ≤ Causal.Flat.pathLength (Causal.Flat.chartSys 2 T) γ' := by
  obtain ⟨γ, hγ⟩ := exists_lowerPath γ' h hx hy
  rw [pathLength_chartSys_eq_e0SliceSys γ γ' hγ]
  exact iInf_le _ γ

end Compare

/-! ### (B) The rim arcs of a spear have `S`-length at most `π R` -/

section Rim

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

namespace E0Surgery.SpearSurgeryDatum

variable {S : Set M} (D : SpearSurgeryDatum M S)

/-- The paper coordinates `(τ_Σ(R e^{iφ}), R e^{iφ})` of the rim point of angle `φ`. -/
noncomputable def rimE0 (φ : ℝ) : E0 :=
  (rimFun D.τS D.R φ, (D.R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))

/-- **The rim point of angle `φ`**: `ψ(τ_Σ(R e^{iφ}), R e^{iφ})`, on `S ∩ {r = R}`. -/
noncomputable def rimPt (φ : ℝ) : M := D.ψ (paperInY (D.rimE0 φ))

theorem rad_rimE0 (φ : ℝ) : rad (D.rimE0 φ) = D.R := by
  simp only [rimE0, rad]
  exact norm_rimPoint D.pos.le φ

theorem rimE0_periodic : Periodic D.rimE0 (2 * π) := by
  intro φ
  simp only [rimE0]
  refine Prod.ext (rimFun_periodic D.τS D.R φ) ?_
  show (D.R : ℂ) * Complex.exp (((φ + 2 * π : ℝ) : ℂ) * Complex.I) = _
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem rimE0_mem_spear (φ : ℝ) : D.rimE0 φ ∈ E0Spear.spear D.v D.R := by
  have h := D.shaft ((D.R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (norm_rimPoint D.pos.le φ).le
  refine ⟨?_, (D.rad_rimE0 φ).le⟩
  simp only [fcoord, D.rad_rimE0]
  show D.v ≤ rimFun D.τS D.R φ - D.R / 2
  simp only [rimFun]; linarith

theorem rimE0_mem_graphSet (φ : ℝ) : D.rimE0 φ ∈ graphSet D.G D.R := by
  refine ⟨by rw [D.rad_rimE0]; exact D.pos, (D.rad_rimE0 φ).le, ?_⟩
  simp only [height, heightAt]
  rw [rim_value D.rim (D.rad_rimE0 φ)]
  simp only [rimE0, rimFun, sub_self]

/-- The rim points lie on `S`. -/
theorem rimPt_mem (φ : ℝ) : D.rimPt φ ∈ S := by
  exact (D.graph _ (D.rimE0_mem_spear φ)).2 rfl

/-- The rim points lie on the cusp `Σ*_Δ`. -/
theorem rimPt_mem_cusp (φ : ℝ) : D.rimPt φ ∈ D.cusp := by
  exact ⟨paperInY (D.rimE0 φ), ⟨D.rimE0 φ, D.rimE0_mem_graphSet φ, rfl⟩, rfl⟩

/-- **Every point of `S` on the rim `{r = R}` of the spear is a rim point.** -/
theorem eq_rimPt {x : E0} (hx : x ∈ E0Spear.spear D.v D.R) (hr : rad x = D.R)
    (hS : D.ψ (paperInY x) ∈ S) : D.ψ (paperInY x) = D.rimPt (Complex.arg x.2) := by
  have h1 : x.1 = D.τS x.2 := (D.graph x hx).1 hS
  have hz : (D.R : ℂ) * Complex.exp ((Complex.arg x.2 : ℂ) * Complex.I) = x.2 := by
    rw [← hr]; exact Complex.norm_mul_exp_arg_mul_I x.2
  have hx' : D.rimE0 (Complex.arg x.2) = x := by
    simp only [rimE0, rimFun, hz]
    exact Prod.ext h1.symm rfl
  rw [rimPt, hx']

/-- The rim function `τ(φ) = τ_Σ(R e^{iφ}) = G(R, φ)` is `C¹`. -/
theorem contDiff_rimFun : ContDiff ℝ 1 (rimFun D.τS D.R) := by
  rw [show rimFun D.τS D.R = fun φ => D.G (D.R, φ) from funext fun φ => (D.rim φ).symm]
  refine contDiff_iff_contDiffAt.2 fun φ => ?_
  have hG : ContDiffAt ℝ 1 D.G (D.R, φ) :=
    D.smooth.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds D.pos)
  exact hG.comp φ (contDiffAt_const.prodMk contDiffAt_id)

theorem continuous_rimE0 : Continuous D.rimE0 :=
  D.contDiff_rimFun.continuous.prodMk (continuous_const.mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))

/-- The rim points depend continuously on the angle. -/
theorem continuous_rimPt : Continuous D.rimPt := by
  refine continuous_iff_continuousAt.2 fun φ => ?_
  have hxW : paperInY (D.rimE0 φ) ∈ D.W := D.spear_sub ⟨D.rimE0 φ, D.rimE0_mem_spear φ, rfl⟩
  have hψ : ContinuousAt D.ψ (paperInY (D.rimE0 φ)) :=
    (D.mor _ hxW).1.continuousAt (D.isOpen.mem_nhds hxW)
  exact hψ.comp (f := ⇑paperInY ∘ D.rimE0) (x := φ)
    ((E0Spear.continuous_paperInY.comp D.continuous_rimE0).continuousAt)

/-- The rim point of angle `φ` as a point of `S`. -/
noncomputable def rimS (φ : ℝ) : S := ⟨D.rimPt φ, D.rimPt_mem φ⟩

/-- **The rim arc** from the angle `φ₁` to the angle `φ₂`, a path of `S`. -/
noncomputable def rimArc (φ₁ φ₂ : ℝ) : Path (D.rimS φ₁) (D.rimS φ₂) where
  toFun s := D.rimS (φ₁ + s * (φ₂ - φ₁))
  continuous_toFun := (D.continuous_rimPt.comp (continuous_const.add
    (continuous_subtype_val.mul continuous_const))).subtype_mk _
  source' := by simp
  target' := by simp

theorem rimArc_apply (φ₁ φ₂ : ℝ) (s : I) :
    D.rimArc φ₁ φ₂ s = D.rimS (φ₁ + s * (φ₂ - φ₁)) := by
  rfl

section Groupoid

variable [HasGroupoid M e0Groupoid]

/-- The rim points are regular. -/
theorem rimPt_mem_regM (φ : ℝ) : D.rimPt φ ∈ E0LM.e0RegM M := by
  exact fun h => (Set.eq_empty_iff_forall_notMem.1 D.cusp_inter_S0) _ ⟨D.rimPt_mem_cusp φ, h⟩

/-- **The rim in the flat chart**: near the angle `φ₀`, the flat chart of `Reg M` at the rim
point reads the rim as `g • btzPaperDev(τ(φ), R, φ + k)` (in null coordinates). -/
theorem eventually_regChart_rim (φ₀ : ℝ) :
    ∃ g : Causal.Flat.isom 2, ∃ k : ℝ, ∀ᶠ φ in 𝓝 φ₀,
      E0LM.regChartM (⟨D.rimPt φ₀, D.rimPt_mem_regM φ₀⟩ : E0LM.e0RegM M) (D.rimPt φ) =
        g • nullToMink (btzPaperNull (rimFun D.τS D.R φ, D.R, φ + k)) := by
  set x₀ := D.rimE0 φ₀ with hx₀
  have hx0 : x₀.2 ≠ 0 := by
    intro h
    have := D.rad_rimE0 φ₀
    simp only [rad, ← hx₀, h, norm_zero] at this
    exact D.pos.ne' this.symm
  have hxW : paperInY x₀ ∈ D.W := D.spear_sub ⟨x₀, D.rimE0_mem_spear φ₀, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_regChart hx0 hxW ⟨D.rimPt φ₀, D.rimPt_mem_regM φ₀⟩ rfl
  refine ⟨g, Complex.arg x₀.2 - φ₀, ?_⟩
  have h1 := (D.continuous_rimE0.tendsto φ₀).eventually hg
  have h2 : ∀ᶠ φ in 𝓝 φ₀, φ - φ₀ ∈ Ioo (-π) π := by
    have : Tendsto (fun φ => φ - φ₀) (𝓝 φ₀) (𝓝 0) := by
      simpa using (continuous_sub_right φ₀).tendsto φ₀
    exact this.eventually (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  filter_upwards [h1, h2] with φ h1 h2
  show E0LM.regChartM _ (D.ψ (paperInY (D.rimE0 φ))) = _
  rw [h1.2]
  congr 1
  have hR : (D.R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 D.pos.ne'
  have hq : (D.rimE0 φ).2 / x₀.2 = Complex.exp (((φ - φ₀ : ℝ) : ℂ) * Complex.I) := by
    simp only [hx₀, rimE0]
    rw [mul_div_mul_left _ _ hR, ← Complex.exp_sub, ← sub_mul, ← Complex.ofReal_sub]
  have hang : Complex.arg x₀.2 + Complex.arg ((D.rimE0 φ).2 / x₀.2) =
      φ + (Complex.arg x₀.2 - φ₀) := by
    rw [hq, Complex.arg_exp]
    have : (((φ - φ₀ : ℝ) : ℂ) * Complex.I).im = φ - φ₀ := by simp
    rw [this, (toIocMod_eq_self _).2 ⟨h2.1, by linarith [h2.2]⟩]
    ring
  simp only [E0.chartMap, E0.locLift, E0.lift]
  rw [D.rad_rimE0 φ, hang]
  rfl

variable [T2Space M] [ConnectedSpace M]

/-- **The density of a rim curve**: for `c = rimS ∘ f` with `f` differentiable at `t`, the
DEC-31 density of `c` at `t` is `R |f'(t)|`, whatever `τ_Σ`. -/
theorem localDensity_rim {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t) :
    Causal.Flat.localDensity (e0SliceSys S) (fun s => D.rimS (f s)) t =
      ENNReal.ofReal (D.R * |f'|) := by
  obtain ⟨g, k, hg⟩ := D.eventually_regChart_rim (f t)
  set τ := rimFun D.τS D.R with hτdef
  have hev : (fun s => e0SliceSys S (D.rimS (f t)) (D.rimS (f s))) =ᶠ[𝓝 t]
      fun s => g • nullToMink (btzPaperNull (τ (f s), D.R, f s + k)) := by
    filter_upwards [hf.continuousAt.eventually hg] with s hs
    rw [e0SliceSys_of_mem (D.rimPt_mem_regM _) (D.rimPt_mem_regM _)]
    exact hs
  have hτ : HasDerivAt τ (deriv τ (f t)) (f t) :=
    ((D.contDiff_rimFun.differentiable one_ne_zero) _).hasDerivAt
  have h1 : HasDerivAt (fun s => τ (f s)) (deriv τ (f t) * f') t := hτ.comp t hf
  have h2 : HasDerivAt (fun s => f s + k) f' t := hf.add_const k
  have hN : HasDerivAt (fun s => btzPaperNull (τ (f s), D.R, f s + k))
      ((2 * (deriv τ (f t) * f') + D.R * (2 * (f t + k) * f'), 0, -(D.R * f'))) t := by
    unfold btzPaperNull
    refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk (hasDerivAt_const _ _) ?_)
    · have h3 := ((h1.const_mul 2).add ((h2.pow 2).const_mul D.R)).sub_const D.R
      convert h3 using 1
      · funext s; simp only [Pi.add_apply, Pi.pow_apply]
      · simp only [Nat.cast_ofNat]; ring_nf
    · have h3 := (h2.const_mul D.R).neg
      refine h3.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp only [Pi.neg_apply]
  have hD := (LinearMap.toContinuousLinearMap
    (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).hasFDerivAt.comp_hasDerivAt t hN
  unfold Causal.Flat.localDensity
  rw [hev.deriv_eq, Causal.Flat.deriv_isom_comp]
  erw [hD.deriv]
  rw [Causal.Flat.minkQ_isom_linear]
  erw [minkQ_nullToMink]
  simp only [nullQ]
  have : (-(D.R * f')) ^ 2 - (2 * (deriv τ (f t) * f') + D.R * (2 * (f t + k) * f')) * 0 =
      (D.R * |f'|) ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [this, Real.sqrt_sq (mul_nonneg D.pos.le (abs_nonneg _))]

/-- **A rim curve with a Lipschitz angle is Lipschitz in the length charts.** -/
theorem isLocLip_rim {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Causal.Flat.IsLocLip (e0SliceSys S) (fun s => D.rimS (f s)) := by
  intro t
  obtain ⟨g, k, hg⟩ := D.eventually_regChart_rim (f t)
  set F : ℝ → Causal.Minkowski 2 :=
    fun φ => nullToMink (btzPaperNull (rimFun D.τS D.R φ, D.R, φ + k)) with hFdef
  have hτ := D.contDiff_rimFun
  have hB : ContDiff ℝ 1 (fun φ => btzPaperNull (rimFun D.τS D.R φ, D.R, φ + k)) := by
    unfold btzPaperNull
    fun_prop
  have hFc : ContDiff ℝ 1 F :=
    (LinearMap.toContinuousLinearMap
      (nullToMink : (ℝ × ℝ × ℝ) →ₗ[ℝ] Causal.Minkowski 2)).contDiff.comp hB
  obtain ⟨K₁, U, hU, hΨ⟩ := (hFc.contDiffAt (x := f t)).exists_lipschitzOnWith
  obtain ⟨Kg, hKg⟩ := Causal.Flat.isom_lipschitzWith g
  have hev : ∀ᶠ s in 𝓝 t, e0SliceSys S (D.rimS (f t)) (D.rimS (f s)) = g • F (f s) := by
    filter_upwards [hf.continuous.continuousAt.eventually hg] with s hs
    rw [e0SliceSys_of_mem (D.rimPt_mem_regM _) (D.rimPt_mem_regM _)]
    exact hs
  obtain ⟨δ, hδ, hδP⟩ := Causal.Flat.exists_Icc_subset_of_eventually
    ((show ∀ᶠ s in 𝓝 t, f s ∈ U from hf.continuous.continuousAt.preimage_mem_nhds hU).and hev)
  refine ⟨δ, hδ, Kg * (K₁ * K), ?_⟩
  have h1 : LipschitzOnWith (Kg * (K₁ * K)) (fun s => g • F (f s)) (Icc (t - δ) (t + δ)) :=
    hKg.comp_lipschitzOnWith (hΨ.comp hf.lipschitzOnWith fun s hs => (hδP s hs).1)
  exact Causal.Flat.lipschitzOnWith_congr_of_eqOn (fun s hs => ((hδP s hs).2).symm) h1

/-- **The rim arc from `φ₁` to `φ₂` has `S`-length `R |φ₂ − φ₁|`** (on `r = R` the printed metric
`−2dτdr + dr² + r²dθ²` is `R² dθ²`, whatever `τ_Σ`). -/
theorem pathLength_rimArc (φ₁ φ₂ : ℝ) :
    Causal.Flat.pathLength (e0SliceSys S) (D.rimArc φ₁ φ₂) =
      ENNReal.ofReal (D.R * |φ₂ - φ₁|) := by
  set Δ := φ₂ - φ₁ with hΔ
  set f : ℝ → ℝ := fun s => φ₁ + (projIcc (0 : ℝ) 1 zero_le_one s : ℝ) * Δ with hfdef
  have hext : ⇑(D.rimArc φ₁ φ₂).extend = fun s => D.rimS (f s) := rfl
  have hfL : LipschitzWith ‖Δ‖₊ f := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simp only [hfdef, Real.dist_eq, add_sub_add_left_eq_sub, ← sub_mul, abs_mul, coe_nnnorm,
      Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (abs_nonneg _)
  have hL : Causal.Flat.IsLocLip (e0SliceSys S) (D.rimArc φ₁ φ₂).extend := by
    rw [hext]; exact D.isLocLip_rim hfL
  rw [Causal.Flat.pathLength_of_isLocLip _ hL, hext]
  unfold Causal.Flat.localLength
  rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Ioc.symm]
  calc ∫⁻ s in Ioo 0 1, Causal.Flat.localDensity (e0SliceSys S) (fun s => D.rimS (f s)) s
      = ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (D.R * |Δ|) := by
        refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
        have hd : HasDerivAt f Δ s := by
          have h2 : HasDerivAt (fun r : ℝ => φ₁ + r * Δ) Δ s := by
            simpa using ((hasDerivAt_id s).mul_const Δ).const_add φ₁
          refine h2.congr_of_eventuallyEq ?_
          filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
          simp only [hfdef, projIcc_of_mem _ ⟨hr.1.le, hr.2.le⟩]
        exact D.localDensity_rim hd
    _ = ENNReal.ofReal (D.R * |Δ|) := by simp

/-- **Any two rim points are joined by an arc of `S` on the cusp, of `S`-length `≤ π R`.** -/
theorem exists_rimPath (φ₁ φ₂ : ℝ) :
    ∃ γ : Path (D.rimS φ₁) (D.rimS φ₂),
      Causal.Flat.pathLength (e0SliceSys S) γ ≤ ENNReal.ofReal (π * D.R) ∧
        ∀ t, (γ t : M) ∈ D.cusp := by
  set φ₂' := toIocMod Real.two_pi_pos (φ₁ - π) φ₂ with hφ₂'
  have hmem : φ₂' ∈ Ioc (φ₁ - π) (φ₁ - π + 2 * π) := toIocMod_mem_Ioc _ _ _
  have heq : D.rimS φ₂' = D.rimS φ₂ := by
    apply Subtype.ext
    show D.ψ (paperInY (D.rimE0 φ₂')) = D.ψ (paperInY (D.rimE0 φ₂))
    have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (φ₁ - π) φ₂
    rw [← h, ← hφ₂', (D.rimE0_periodic.zsmul _) φ₂']
  refine ⟨(D.rimArc φ₁ φ₂').cast rfl heq.symm, ?_, fun s => D.rimPt_mem_cusp _⟩
  rw [Causal.Flat.pathLength_congr_extend (e0SliceSys S) ((D.rimArc φ₁ φ₂').cast rfl heq.symm)
    (D.rimArc φ₁ φ₂') rfl, D.pathLength_rimArc]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : |φ₂' - φ₁| ≤ π := abs_le.2 ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  nlinarith [D.pos, abs_nonneg (φ₂' - φ₁)]

/-- **Two rim points are at `S`-distance `≤ π R`.** -/
theorem edist_rimPt_le (φ₁ φ₂ : ℝ) :
    edist (Causal.Flat.LocalLengthSpace.toSpace.symm (D.rimS φ₁) :
        Causal.Flat.LocalLengthSpace (e0SliceSys S))
      (Causal.Flat.LocalLengthSpace.toSpace.symm (D.rimS φ₂)) ≤ ENNReal.ofReal (π * D.R) := by
  obtain ⟨γ, hγ, -⟩ := D.exists_rimPath φ₁ φ₂
  exact (iInf_le _ γ).trans hγ

end Groupoid

end E0Surgery.SpearSurgeryDatum

end Rim

/-! ### (A) and (B) for a locally finite spear family: `Σ*` -/

section Family

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
  [HasGroupoid M e0Groupoid]

namespace E0SpearFamily.LFSurgeryData

variable {S : Set M} (Dat : LFSurgeryData M S)

/-- **The `Σ*`-distance is at most the `S`-length of a path of `S` lying in `Σ*`.** -/
theorem edist_le_pathLength {x y : S} (γ : Path x y) (h : ∀ t, (γ t : M) ∈ Dat.sigmaStar)
    (x' y' : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg)
    (hx : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) x') = x)
    (hy : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) y') = y) :
    edist x' y' ≤ Causal.Flat.pathLength (e0SliceSys S) γ := by
  exact edist_inducedLength_le_pathLength_e0SliceSys (A := Dat.sigmaStar) γ
    (fun t => ⟨h t, Dat.sigmaStar_subset_regM (h t)⟩) x' y' hx hy

/-- **Two rim points of spear `i` are at `Σ*`-distance `≤ π Rᵢ`.** -/
theorem edist_rimPt_le (i : Dat.ι) (φ₁ φ₂ : ℝ)
    (x' y' : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg)
    (hx : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) x') =
      (Dat.D i).rimPt φ₁)
    (hy : regVal M (Causal.Flat.InducedLengthSpace.toSubtype (d := 2) (M := e0RegMFlat M) y') =
      (Dat.D i).rimPt φ₂) :
    edist x' y' ≤ ENNReal.ofReal (π * (Dat.D i).R) := by
  obtain ⟨γ, hγ, hc⟩ := (Dat.D i).exists_rimPath φ₁ φ₂
  exact (Dat.edist_le_pathLength γ (fun t => Or.inr (mem_iUnion.2 ⟨i, hc t⟩)) x' y' hx hy).trans hγ

end E0SpearFamily.LFSurgeryData

end Family

end GX
