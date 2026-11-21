import EGF.SamplingCorollaries
import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# Nonsingular moves give the star inflow a density

`theo:backward_policy` — `main.tex:733` (setting `main.tex:731–732`; the presupposition
`f_in = dF_in/dλ` of `main.tex:196`; correction C-6, and C-7/C-8 for measure-preserving moves).
The label is marked in `EGF/BackwardPolicy.lean` in its corrected form of record
(`EGF.backward_policy_rnDeriv`, DEC-141); this file adds no mark. It proves the author's sentence
(2026-11-21): "the F_in domination in the context of the paper is a straightforward consequence of
the diffeomorphism decomposition of the policy", in the form of record
`F_out π = ∑ᵢ (Φᵢ)₊(αⁱ F_out) ≪ ∑ᵢ (Φᵢ)₊λ ≪ λ` as soon as `(Φᵢ)₊λ ≪ λ` for every `i`.

> where $\finit = \frac{d\Finit}{d\lambda}$, $\fterm=\frac{d\Fterm}{d\lambda}$ and
> $\finstar=\frac{d\Finstar}{d\lambda} = \frac{d(\Foutstar\ForwardPolicyStar)}{d\lambda}$.
> (`main.tex:196`)

> on a Differential manifold $\Statespace$ endowed with a background measure $\lambda$ absolutely
> continuous with respect to Lebesgue measure, we define an EGF as a Generative Flow
> $(\ForwardPolicyStar, \Foutstar)$ with $\Foutstar = \foutstar \lambda$ and
> $\ForwardPolicyStar(s\rightarrow \cdot) = \sum_{i=1}^p\forwardalpha^{i}(s)\delta_{\Phi_i(s)}$
> where $\Phi_i$ are diffeomorphisms of $\Statespace$. (`main.tex:731–732`)

> even with simple transformations, such as affine maps on tori and rotations on spheres.
> (`main.tex:238`)

> Let $(\ForwardPolicyStar,\Foutstar)$ as above, the induced Generative Flow on $\Statespace$ has
> a backward star policy given by
> $\BackwardPolicy^*(s) = \sum_{i=1}^p\backwardalpha^i(s) \delta_{\Phi_i^{-1}(s)}$,
> $\backwardalpha^i(s) = \frac{(\forwardalpha^if^*_\rightarrow)\circ \Phi_i^{-1}(s)|J_s {\Phi_i^{-1}}| }{ \finstar(s)}$,
> $\finstar = \sum_j (\forwardalpha^jf^*_\rightarrow)\circ \Phi_j^{-1}(s) |J_s {\Phi_j^{-1}}|$.
> (`main.tex:733–739`)

## What is proved

| | |
|---|---|
| `IsEGFPolicy.bind_eq_sum_map` | `μπ = ∑ᵢ (Φᵢ)₊(αⁱ μ)` for every measure `μ`, `Φᵢ` measurable (no inverse) |
| `inflow_ac_iff` | `F_in ≪ λ ⟺ ∀ i, (Φᵢ)₊(αⁱ F_out) ≪ λ` (sharp) |
| `inflow_ac_of_map_ac`, `bind_ac_of_map_ac` | `(Φᵢ)₊λ ≪ λ`, `F_out ≪ λ` ⟹ `F_in ≪ λ`, `λπ ≪ λ`; any measurable space, no σ-finiteness |
| `inflow_ac_of_bind_ac`, `bind_withDensity_ac`, `inflow_ac_forall_iff` | any kernel: `λπ ≪ λ` ⟺ every `F_out ≪ λ` has `F_out π ≪ λ` |
| `bind_ac_iff_map_ac` | positive weights: `λπ ≪ λ ⟺ ∀ i, (Φᵢ)₊λ ≪ λ` (the hypothesis is necessary) |
| `inflow_eq_withDensity_sum_rnDeriv` | `f_in = ∑ᵢ d((Φᵢ)₊(αⁱ F_out))/dλ`, the inflow density with no inverse |
| `InflowAC.of_map_ac`, `.of_bind_ac`, `.of_isEGF`, `.of_quasiMeasurePreserving`, `.of_measurePreserving` | `EGF.InflowAC` discharged |
| `InflowAC.of_map_eq_withDensity` | the hypotheses of `EGF.inflowAC_of_isEGFPolicy` imply the nonsingular ones |
| `map_ac_of_measurePreserving`, `map_ac_of_leftInverse`, `map_ac_of_differentiable`, `map_ac_of_diffeomorph`, `map_ac_diffeoEquiv` | the instances: measure-preserving maps; Haar measure and a differentiable (left) inverse; `Cⁿ` diffeomorphisms |
| `InflowAC.of_diffeomorph`, `InflowAC.of_equiv_addHaar` | the Euclidean `InflowAC`, no Jacobian |
| `backward_policy_measurePreserving`, `inflow_eq_withDensity_measurePreserving` | the four conclusions of `EGF.backward_policy` with `J ≡ 1`; `f_in = ∑ᵢ (αⁱ f_out)∘Φᵢ⁻¹` |
| `rnDeriv_map_ae_eq_one`, `coordJac_ae_eq_one` | `|J| = 1` a.e.: the `λ`-Jacobian, and the coordinate one for Haar measure |
| `not_map_ac_acMap`, `doubling_witness` | the strict counterexample violates exactly `(Φᵢ)₊λ ≪ λ`; a non-invertible move covered |

## Hypothesis checklist

| paper | here |
|---|---|
| `𝒮` a differential (Riemannian) manifold | ⚠ weakened: any measurable space |
| `λ ≪` Lebesgue (`:731`) / the volume (`:217`) | corrected (C-6, C-7): `(Φᵢ)₊λ ≪ λ` (nonsingular moves), the form of record; necessary for positive weights (`bind_ac_iff_map_ac`) |
| `Φᵢ` diffeomorphisms | ⚠ weakened: measurable maps, no inverse (`IsEGFPolicy`); homeomorphisms in `.of_isEGF` |
| `F_out = f_out λ` | ⚠ weakened: `F_out ≪ λ` (any measure for the `≪` statements, finite for the density) |
| `λ` σ-finite (target's (4)) | ⚠ weakened: not assumed in `backward_policy_measurePreserving` |
| `|J_s Φᵢ⁻¹|` an arbitrary Jacobian | ⚠ strengthened: measure-preserving moves (`|J| = 1`) in `backward_policy_measurePreserving`, `inflow_eq_withDensity_measurePreserving`, `coordJac_ae_eq_one`, `rnDeriv_map_ae_eq_one`; the general case is `EGF.backward_policy_rnDeriv` |
| `λ` finite (`main.tex:161`) | ⚠ σ-finite assumed for the density statements (`inflow_eq_withDensity_sum_rnDeriv`, `inflow_eq_withDensity_of_map_ac`), where it is needed; implied by the paper's finite `λ` |
| ergodicity (`def:egf`) | not used |

## SCOPE (disclosed)

No `sorry`. No `**` mark: `theo:backward_policy` is certified in `EGF/BackwardPolicy.lean`; this
file anchors C-6 (`inflow_ac_of_map_ac`, `InflowAC.of_map_ac`) and supports C-7/C-8 by the
measure-preserving form. Nothing about Corollary 3.10 (T-egf-loss). No torus or sphere is built
(T-egf-families, T-egf-families-sphere): `map_ac_of_measurePreserving` is their entry point. The
circle in `doubling_witness` is a non-vacuity witness for non-invertible moves, not a family.
Mathlib (`fabf563a`) has no manifold volume measure, so the Riemannian volume is not instantiated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Manifold

variable {S : Type*} [MeasurableSpace S] {p : ℕ}

/-! ## The diffeomorphism decomposition of the inflow -/

-- ported from GFNBounds.Core.EGF.IsEGFPolicy.bind_withDensity (lean/GFNBounds/Core/UniversalityBody.lean:207)
/-- **The decomposition of the push-forward by an EGF policy**: for `π(s) = ∑ᵢ αⁱ(s) δ_{Φᵢ(s)}` and
any measure `μ`, `μπ = ∑ᵢ (Φᵢ)₊(αⁱ μ)`. The maps are only measurable. Generalized from the
follow-up's `ν.withDensity f` to any `μ`. -/
theorem IsEGFPolicy.bind_eq_sum_map {π : Kernel S S} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (h : IsEGFPolicy π Φ α) (μ : Measure S) :
    μ.bind π = ∑ i, (μ.withDensity fun s => ENNReal.ofReal (α i s)).map (Φ i) := by
  ext A hA
  rw [Measure.bind_apply hA π.aemeasurable, Measure.finsetSum_apply]
  simp only [h.apply_set _ hA]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      Measurable fun s => ENNReal.ofReal (α i s) * A.indicator 1 (Φ i s) := fun i _ =>
    (ENNReal.measurable_ofReal.comp (h.measurable_weight i)).mul
      ((measurable_const.indicator hA).comp (h.measurable_map i))
  rw [lintegral_finsetSum _ hm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (h.measurable_map i) hA, withDensity_apply _ (h.measurable_map i hA),
    ← lintegral_indicator (h.measurable_map i hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : Φ i x ∈ A
  · have hx' : x ∈ Φ i ⁻¹' A := hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Pi.one_apply, mul_one]
  · have hx' : x ∉ Φ i ⁻¹' A := hx
    simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

/-- `F_in = F_out π = ∑ᵢ (Φᵢ)₊(αⁱ F_out)` (`main.tex:196`, `:747–755`). -/
theorem IsEGFPolicy.inflow_eq_sum_map {π : Kernel S S} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (h : IsEGFPolicy π Φ α) (Fout : Measure S) :
    inflow π Fout = ∑ i, (Fout.withDensity fun s => ENNReal.ofReal (α i s)).map (Φ i) :=
  h.bind_eq_sum_map Fout

/-! ## Absolute continuity of the inflow -/

/-- A finite sum of measures is `≪ ν` iff each term is. -/
theorem finsetSum_ac_iff {ι : Type*} (I : Finset ι) (μ : ι → Measure S) (ν : Measure S) :
    (∑ i ∈ I, μ i) ≪ ν ↔ ∀ i ∈ I, μ i ≪ ν := by
  constructor
  · intro h i hi A hA
    have h0 := h hA
    rw [Measure.finsetSum_apply] at h0
    exact (Finset.sum_eq_zero_iff.1 h0) i hi
  · intro h A hA
    rw [Measure.finsetSum_apply]
    exact Finset.sum_eq_zero fun i hi => h i hi hA

-- ported from GFNBounds.Core.bind_absolutelyContinuous_bind (lean/GFNBounds/Core/Kernel.lean:132)
/-- `μ ≪ ν ⟹ μπ ≪ νπ`, for any kernel. -/
theorem bind_ac_bind (π : Kernel S S) {μ ν : Measure S} (h : μ ≪ ν) : μ.bind π ≪ ν.bind π := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  have hm : Measurable fun x => π x A := π.measurable_coe hA
  rw [Measure.bind_apply hA π.aemeasurable, lintegral_eq_zero_iff hm] at hA0
  rw [Measure.bind_apply hA π.aemeasurable, lintegral_eq_zero_iff hm]
  exact h.ae_le hA0

/-- **The sharp criterion**: for an EGF policy, `F_in ≪ λ` iff `(Φᵢ)₊(αⁱ F_out) ≪ λ` for every `i`. -/
theorem inflow_ac_iff (lam : Measure S) {π : Kernel S S} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy π Φ α) (Fout : Measure S) :
    inflow π Fout ≪ lam ↔
      ∀ i, (Fout.withDensity fun s => ENNReal.ofReal (α i s)).map (Φ i) ≪ lam := by
  rw [hπ.inflow_eq_sum_map Fout, finsetSum_ac_iff]
  simp

/-- **`F_in ≪ λ` from nonsingular moves** (correction C-6): if every move is nonsingular for `λ`,
`(Φᵢ)₊λ ≪ λ`, and `F_out ≪ λ`, then `F_in = F_out π ≪ λ`. On any measurable space, for any
measures, with measurable `Φᵢ` and no inverse, no Jacobian, no σ-finiteness. -/
theorem inflow_ac_of_map_ac (lam : Measure S) {π : Kernel S S} {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam)
    {Fout : Measure S} (hout : Fout ≪ lam) : inflow π Fout ≪ lam :=
  (inflow_ac_iff lam hπ Fout).2 fun i =>
    (((withDensity_absolutelyContinuous _ _).trans hout).map (hπ.measurable_map i)).trans (hΦ i)

/-- `λπ ≪ λ` from nonsingular moves (the follow-up's clause `ν π ≪ ν`). -/
theorem bind_ac_of_map_ac (lam : Measure S) {π : Kernel S S} {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam) :
    lam.bind π ≪ lam :=
  inflow_ac_of_map_ac lam hπ hΦ Measure.AbsolutelyContinuous.rfl

-- ported from GFNBounds.Core.ILBoundFull.inflowAC_of_bind_ac (lean/GFNBounds/Core/ILBoundFull.lean:581)
-- and GFNBounds.Core.Family.bind_withDensity_ac (lean/GFNBounds/Core/FamilyUniversality.lean:373)
/-- **The second route**, for any kernel: `λπ ≪ λ` and `F_out ≪ λ` give `F_out π ≪ λ`. -/
theorem inflow_ac_of_bind_ac (lam : Measure S) (π : Kernel S S) (h : lam.bind π ≪ lam)
    {Fout : Measure S} (hout : Fout ≪ lam) : inflow π Fout ≪ lam :=
  (bind_ac_bind π hout).trans h

-- ported from GFNBounds.Core.Family.bind_withDensity_ac (lean/GFNBounds/Core/FamilyUniversality.lean:373)
/-- The follow-up's form: `λπ ≪ λ` gives `(f λ)π ≪ λ` for every density `f`. -/
theorem bind_withDensity_ac (lam : Measure S) (π : Kernel S S) (h : lam.bind π ≪ lam)
    (f : S → ℝ≥0∞) : (lam.withDensity f).bind π ≪ lam :=
  inflow_ac_of_bind_ac lam π h (withDensity_absolutelyContinuous lam f)

/-- For any kernel, `λπ ≪ λ` is exactly the condition under which every `F_out ≪ λ` has an
inflow density. -/
theorem inflow_ac_forall_iff (lam : Measure S) (π : Kernel S S) :
    (∀ Fout : Measure S, Fout ≪ lam → inflow π Fout ≪ lam) ↔ lam.bind π ≪ lam :=
  ⟨fun h => h lam Measure.AbsolutelyContinuous.rfl, fun h _ hout => inflow_ac_of_bind_ac lam π h hout⟩

/-- **Nonsingularity is necessary** when the weights are positive (e.g. the uniform policy):
`λπ ≪ λ ⟺ ∀ i, (Φᵢ)₊λ ≪ λ`. -/
theorem bind_ac_iff_map_ac (lam : Measure S) {π : Kernel S S} {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π Φ α) (hpos : ∀ i s, 0 < α i s) :
    lam.bind π ≪ lam ↔ ∀ i, lam.map (Φ i) ≪ lam := by
  refine ⟨fun h i => ?_, bind_ac_of_map_ac lam hπ⟩
  have h1 := (inflow_ac_iff lam hπ lam).1 h i
  have h2 : lam ≪ lam.withDensity fun s => ENNReal.ofReal (α i s) :=
    withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (hπ.measurable_weight i)).aemeasurable
      (Filter.Eventually.of_forall fun s => (ENNReal.ofReal_pos.2 (hpos i s)).ne')
  exact (h2.map (hπ.measurable_map i)).trans h1

-- ported from GFNBounds.Core.EGF.IsEGFPolicy.weight_le_one (lean/GFNBounds/Core/UniversalityBody.lean:233)
/-- The weights are at most `1` (`main.tex:219`: `α : 𝒮 → [0,1]ᵖ`). -/
theorem IsEGFPolicy.weight_le_one {π : Kernel S S} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (h : IsEGFPolicy π Φ α) (i : Fin p) (s : S) : α i s ≤ 1 := by
  have hle := Finset.single_le_sum (fun j _ => h.weight_nonneg j s) (Finset.mem_univ i)
  rwa [h.weight_sum s] at hle

/-- `αⁱ μ` is finite when `μ` is. -/
theorem isFiniteMeasure_withDensity_weight {π : Kernel S S} {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (h : IsEGFPolicy π Φ α) (μ : Measure S) [IsFiniteMeasure μ] (i : Fin p) :
    IsFiniteMeasure (μ.withDensity fun s => ENNReal.ofReal (α i s)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ s, ENNReal.ofReal (α i s) ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun s => ENNReal.ofReal_le_one.2 (h.weight_le_one i s)
    _ < ⊤ := by simp

/-- **The star-inflow density without an inverse**: for a σ-finite `λ`, a finite `F_out` and
`F_in ≪ λ`, `F_in = f_in λ` with `f_in = ∑ᵢ d((Φᵢ)₊(αⁱ F_out))/dλ` (`main.tex:196`, `:737`). -/
theorem inflow_eq_withDensity_sum_rnDeriv (lam : Measure S) [SigmaFinite lam] {π : Kernel S S}
    {Φ : Fin p → S → S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π Φ α) (Fout : Measure S)
    [IsFiniteMeasure Fout] (hin : inflow π Fout ≪ lam) :
    inflow π Fout = lam.withDensity
      (∑ i, ((Fout.withDensity fun s => ENNReal.ofReal (α i s)).map (Φ i)).rnDeriv lam) := by
  have hac := (inflow_ac_iff lam hπ Fout).1 hin
  have hfin : ∀ i, IsFiniteMeasure (Fout.withDensity fun s => ENNReal.ofReal (α i s)) :=
    fun i => isFiniteMeasure_withDensity_weight hπ Fout i
  conv_lhs => rw [hπ.inflow_eq_sum_map Fout]
  ext A hA
  rw [Measure.finsetSum_apply, withDensity_apply _ hA]
  simp only [Finset.sum_apply]
  rw [lintegral_finsetSum _ (fun i _ => Measure.measurable_rnDeriv _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := hfin i
  rw [Measure.setLIntegral_rnDeriv' (hac i) hA]

/-- The same under nonsingular moves and `F_out ≪ λ`. -/
theorem inflow_eq_withDensity_of_map_ac (lam : Measure S) [SigmaFinite lam] {π : Kernel S S}
    {Φ : Fin p → S → S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π Φ α)
    (hΦ : ∀ i, lam.map (Φ i) ≪ lam) (Fout : Measure S) [IsFiniteMeasure Fout]
    (hout : Fout ≪ lam) :
    inflow π Fout = lam.withDensity
      (∑ i, ((Fout.withDensity fun s => ENNReal.ofReal (α i s)).map (Φ i)).rnDeriv lam) :=
  inflow_eq_withDensity_sum_rnDeriv lam hπ Fout (inflow_ac_of_map_ac lam hπ hΦ hout)

/-! ## The presupposition `InflowAC` discharged -/

/-- **`InflowAC` for a generative flow with an EGF policy and nonsingular moves** (C-6): no
`InflowAC` hypothesis, no Jacobian, no measurable inverse. -/
theorem InflowAC.of_map_ac (lam : Measure S) (F : GenerativeFlow S) {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy F.policy Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam)
    (hout : F.outflow ≪ lam) : InflowAC lam F :=
  inflow_ac_of_map_ac lam hπ hΦ hout

/-- **`InflowAC.of_map_ac` supersedes `EGF.inflowAC_of_isEGFPolicy`**: its hypotheses
(`Φᵢ₊λ = Jᵢ λ`, `F_out = f_out λ`) give the nonsingular ones, and neither `J` nor `f_out` need be
measurable. -/
theorem InflowAC.of_map_eq_withDensity (lam : Measure S) (Φ : Fin p → S ≃ᵐ S)
    (J : Fin p → S → ℝ≥0∞) (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i)) (F : GenerativeFlow S)
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞}
    (hout : F.outflow = lam.withDensity fout) : InflowAC lam F :=
  InflowAC.of_map_ac lam F hπ (fun i => (hJ i) ▸ withDensity_absolutelyContinuous _ _)
    (hout ▸ withDensity_absolutelyContinuous _ _)

/-- `InflowAC` for any generative flow with `λπ ≪ λ`. -/
theorem InflowAC.of_bind_ac (lam : Measure S) (F : GenerativeFlow S)
    (h : lam.bind F.policy ≪ lam) (hout : F.outflow ≪ lam) : InflowAC lam F :=
  inflow_ac_of_bind_ac lam F.policy h hout

/-- **`InflowAC` for an EGF** (`EGF.IsEGF`, homeomorphic moves) with nonsingular moves. No Borel
hypothesis: the measurability of the moves is part of `IsEGFPolicy`. -/
theorem InflowAC.of_isEGF [TopologicalSpace S] (lam : Measure S) (F : GenerativeFlow S)
    {Φ : Fin p → S ≃ₜ S} {α : Fin p → S → ℝ} (hE : IsEGF F Φ α)
    (hΦ : ∀ i, lam.map (Φ i) ≪ lam) (hout : F.outflow ≪ lam) : InflowAC lam F :=
  InflowAC.of_map_ac lam F hE.policy hΦ hout

/-- `InflowAC` with the moves quasi-measure-preserving for `λ` (Mathlib's name for nonsingular). -/
theorem InflowAC.of_quasiMeasurePreserving (lam : Measure S) (F : GenerativeFlow S)
    {Φ : Fin p → S → S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy F.policy Φ α)
    (hΦ : ∀ i, Measure.QuasiMeasurePreserving (Φ i) lam lam) (hout : F.outflow ≪ lam) :
    InflowAC lam F :=
  InflowAC.of_map_ac lam F hπ (fun i => (hΦ i).absolutelyContinuous) hout

/-! ## Instances of nonsingularity -/

/-- **A measure-preserving move is nonsingular**: `Φ₊λ = λ ≪ λ`. The entry point of the torus
(affine maps, Haar measure) and sphere (rotations) families. -/
theorem map_ac_of_measurePreserving {lam : Measure S} {Φ : S → S}
    (h : MeasurePreserving Φ lam lam) : lam.map Φ ≪ lam :=
  Measure.absolutelyContinuous_of_le h.map_eq.le

/-- **`InflowAC` for measure-preserving moves** (affine `SL_d(ℤ)` moves of tori, rotations of
spheres: `main.tex:284`, `:303`). -/
theorem InflowAC.of_measurePreserving (lam : Measure S) (F : GenerativeFlow S)
    {Φ : Fin p → S → S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy F.policy Φ α)
    (hmp : ∀ i, MeasurePreserving (Φ i) lam lam) (hout : F.outflow ≪ lam) : InflowAC lam F :=
  InflowAC.of_map_ac lam F hπ (fun i => map_ac_of_measurePreserving (hmp i)) hout

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Haar measure, a differentiable left inverse**: if `g ∘ Φ = id` with `g` differentiable, then
`Φ₊μ ≪ μ` (`Φ⁻¹(A) ⊆ g(A)`, and a differentiable map sends null sets to null sets). No Jacobian. -/
theorem map_ac_of_leftInverse (μ : Measure E) [μ.IsAddHaarMeasure] {Φ g : E → E}
    (hΦ : Measurable Φ) (hg : Differentiable ℝ g) (hgΦ : Function.LeftInverse g Φ) :
    μ.map Φ ≪ μ := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [Measure.map_apply hΦ hA]
  exact measure_mono_null (show Φ ⁻¹' A ⊆ g '' A from fun x hx => ⟨Φ x, hx, hgΦ x⟩)
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hg.differentiableOn hA0)

/-- **Haar measure, a measurable bijection with differentiable inverse**: `Φ₊μ ≪ μ`. -/
theorem map_ac_of_differentiable (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E ≃ᵐ E)
    (hd : Differentiable ℝ Φ.symm) : μ.map Φ ≪ μ :=
  map_ac_of_leftInverse μ Φ.measurable hd Φ.symm_apply_apply

/-- **A `Cⁿ` diffeomorphism (`n ≥ 1`) is nonsingular for Haar measure.** -/
theorem map_ac_of_diffeomorph {n : WithTop ℕ∞} (hn : n ≠ 0) (μ : Measure E)
    [μ.IsAddHaarMeasure] (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n) : μ.map Φ ≪ μ :=
  map_ac_of_differentiable μ Φ.toHomeomorph.toMeasurableEquiv (Φ.symm.contDiff.differentiable hn)

/-- The same through `EGF.diffeoEquiv` (`EGF/BackwardPolicy.lean`), the form `backward_policy_diffeomorph`
uses. -/
theorem map_ac_diffeoEquiv {n : WithTop ℕ∞} (hn : n ≠ 0) (μ : Measure E) [μ.IsAddHaarMeasure]
    (Φ : Fin p → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n) (i : Fin p) : μ.map (diffeoEquiv Φ i) ≪ μ :=
  map_ac_of_diffeomorph hn μ (Φ i)

/-- **`InflowAC` for diffeomorphic moves and Haar measure** (the body's setting, `main.tex:225`). -/
theorem InflowAC.of_diffeomorph {n : WithTop ℕ∞} (hn : n ≠ 0) (μ : Measure E)
    [μ.IsAddHaarMeasure] (F : GenerativeFlow E) (Φ : Fin p → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n)
    {α : Fin p → E → ℝ} (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) (hout : F.outflow ≪ μ) :
    InflowAC μ F :=
  InflowAC.of_map_ac μ F hπ (fun i => map_ac_of_diffeomorph hn μ (Φ i)) hout

/-- **`InflowAC` for a background measure equivalent to Haar measure** and measurable bijections
with differentiable inverses (`EGF.map_ac_of_equiv_addHaar`). -/
theorem InflowAC.of_equiv_addHaar (μ : Measure E) [μ.IsAddHaarMeasure] {lam : Measure E}
    (h1 : lam ≪ μ) (h2 : μ ≪ lam) (F : GenerativeFlow E) (Φ : Fin p → E ≃ᵐ E)
    (hd : ∀ i, Differentiable ℝ (Φ i).symm) {α : Fin p → E → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) (hout : F.outflow ≪ lam) : InflowAC lam F :=
  InflowAC.of_map_ac lam F hπ (fun i => map_ac_of_equiv_addHaar μ h1 h2 (Φ i) (hd i)) hout

/-- For Haar measure and a measure-preserving move with differentiable inverse, the coordinate
Jacobian `|det J_s Φᵢ⁻¹|` is `1` almost everywhere: `|J| = 1`. -/
theorem coordJac_ae_eq_one (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : Fin p → E ≃ᵐ E) (i : Fin p)
    (hd : Differentiable ℝ (Φ i).symm) (hmp : MeasurePreserving (Φ i) μ μ) :
    coordJac Φ i =ᵐ[μ] 1 := by
  have h := map_eq_withDensity_abs_det μ (Φ i) hd
  rw [hmp.map_eq] at h
  have h1 : μ.withDensity (coordJac Φ i) = μ.withDensity 1 := by
    rw [withDensity_one]; exact h.symm
  exact (withDensity_eq_iff_of_sigmaFinite (measurable_coordJac Φ i).aemeasurable
    measurable_one.aemeasurable).1 h1

end Euclidean

/-! ## Measure-preserving moves: the printed formula with `|J| = 1` -/

/-- The `λ`-Jacobian of a measure-preserving move is `1`, `λ`-a.e. -/
theorem rnDeriv_map_ae_eq_one (lam : Measure S) [SigmaFinite lam] {Φ : S → S}
    (h : MeasurePreserving Φ lam lam) : (lam.map Φ).rnDeriv lam =ᵐ[lam] 1 := by
  rw [h.map_eq]; exact Measure.rnDeriv_self lam

/-- `f_in` with `J ≡ 1` is `∑ᵢ (αⁱ f_out)∘Φᵢ⁻¹` (`main.tex:737`). -/
theorem inflowDensity_one (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞) (s : S) :
    inflowDensity Φ α fout (fun _ _ => 1) s
      = ∑ i, ENNReal.ofReal (α i ((Φ i).symm s)) * fout ((Φ i).symm s) := by
  simp only [inflowDensity, inflowTerm, mul_one]

/-- `βⁱ` with `J ≡ 1` is `(αⁱ f_out)∘Φᵢ⁻¹ / f_in` (`main.tex:736`). -/
theorem backwardWeight_one (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (i : Fin p) (s : S) :
    backwardWeight Φ α fout (fun _ _ => 1) i s
      = (ENNReal.ofReal (α i ((Φ i).symm s)) * fout ((Φ i).symm s)
          / ∑ j, ENNReal.ofReal (α j ((Φ j).symm s)) * fout ((Φ j).symm s)).toReal := by
  simp only [backwardWeight, inflowDensity, inflowTerm, mul_one]

/-- **`theo:backward_policy` for measure-preserving moves** (`|J| = 1`; affine `SL_d(ℤ)` moves of
tori and rotations of spheres, `main.tex:284`, `:303`): for measure-preserving measurable bijections
`Φᵢ` of `(𝒮, λ)`, the four conclusions of `EGF.backward_policy` with `J ≡ 1`:
`F_in = f_in λ` with `f_in = ∑ᵢ (αⁱ f_out)∘Φᵢ⁻¹`, the printed `B` with `βⁱ = (αⁱ f_out)∘Φᵢ⁻¹ / f_in`
is a backward policy, Markov `F_in`-a.e., and the unique one. No σ-finiteness. -/
theorem backward_policy_measurePreserving (lam : Measure S) (F : GenerativeFlow S)
    (Φ : Fin p → S ≃ᵐ S) (hmp : ∀ i, MeasurePreserving (Φ i) lam lam) {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) :
    inflow F.policy F.outflow = lam.withDensity (inflowDensity Φ α fout fun _ _ => 1) ∧
    IsBackwardPolicy F.policy F.outflow
      (backwardKernel Φ α fout (fun _ _ => 1) hπ.measurable_weight hf fun _ => measurable_const) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow), ∑ i, backwardWeight Φ α fout (fun _ _ => 1) i s = 1) ∧
    ∀ B : Kernel S S, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel Φ α fout (fun _ _ => 1) hπ.measurable_weight hf
          (fun _ => measurable_const) s X :=
  backward_policy lam F Φ (fun _ _ => 1) (fun _ => measurable_const)
    (fun i => by rw [(hmp i).map_eq]; exact withDensity_one.symm) hπ hf hout

/-- **The printed inflow formula with `|J| = 1`**, explicitly: `F_in = (∑ᵢ (αⁱ f_out)∘Φᵢ⁻¹) λ`. -/
theorem inflow_eq_withDensity_measurePreserving (lam : Measure S) (F : GenerativeFlow S)
    (Φ : Fin p → S ≃ᵐ S) (hmp : ∀ i, MeasurePreserving (Φ i) lam lam) {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) :
    inflow F.policy F.outflow = lam.withDensity
      fun s => ∑ i, ENNReal.ofReal (α i ((Φ i).symm s)) * fout ((Φ i).symm s) := by
  rw [(backward_policy_measurePreserving lam F Φ hmp hπ hf hout).1]
  congr 1
  funext s
  exact inflowDensity_one Φ α fout s

/-! ## Witnesses -/

/-- **The hypothesis cannot be dropped**: in the strict counterexample `EGF.printed_inflow_not_ac`
(`λ = 𝟙_{[0,1)}·Lebesgue`, `Φ(x) = x + 1`, `F_out = λ`), `F_out ≪ λ` holds and the move is not
nonsingular: `Φ₊λ ≪ λ` fails, and that is the only hypothesis of `inflow_ac_of_map_ac` that does. -/
theorem not_map_ac_acMap : ¬ lamAc.map (acMap 0) ≪ lamAc := fun h =>
  printed_inflow_not_ac.2.2.2.2.1
    (inflow_ac_of_map_ac lamAc isEGFPolicy_acPolicy (fun _ => h)
      (withDensity_absolutelyContinuous _ _))

/-- The doubling map `y ↦ 2y` of the circle `AddCircle T`. -/
noncomputable def doublingMap (T : ℝ) : Fin 1 → AddCircle T → AddCircle T := fun _ y => 2 • y

/-- The policy `π(y) = δ_{2y}`. -/
noncomputable def doublingPolicy (T : ℝ) [Fact (0 < T)] : Kernel (AddCircle T) (AddCircle T) :=
  egfKernel (doublingMap T) (fun _ _ => 1) (fun _ => measurable_const_smul 2)
    fun _ => measurable_const

/-- **A non-invertible move is covered**: the doubling map of the circle is measure-preserving for
Haar measure and not injective (so `EGF.backward_policy`, which needs `𝒮 ≃ᵐ 𝒮`, does not apply),
and `inflow_ac_of_map_ac` gives `F_out π ≪ λ` for every `F_out ≪ λ`. -/
theorem doubling_witness (T : ℝ) [Fact (0 < T)] :
    IsEGFPolicy (doublingPolicy T) (doublingMap T) (fun _ _ => 1) ∧
    MeasurePreserving (doublingMap T 0) volume volume ∧ ¬ Function.Injective (doublingMap T 0) ∧
    ∀ Fout : Measure (AddCircle T), Fout ≪ volume → inflow (doublingPolicy T) Fout ≪ volume := by
  have hT : 0 < T := Fact.out
  have hπ : IsEGFPolicy (doublingPolicy T) (doublingMap T) (fun _ _ => 1) :=
    isEGFPolicy_egfKernel _ _ _ _ (fun _ _ => zero_le_one) (fun _ => by simp)
  have hmp : MeasurePreserving (doublingMap T 0) volume volume :=
    (AddCircle.ergodic_nsmul (T := T) (by norm_num : 1 < 2)).toMeasurePreserving
  refine ⟨hπ, hmp, fun hinj => ?_, fun Fout hout =>
    inflow_ac_of_map_ac volume hπ (fun _ => map_ac_of_measurePreserving hmp) hout⟩
  have h1 : doublingMap T 0 ((T / 2 : ℝ) : AddCircle T) = doublingMap T 0 0 := by
    simp only [doublingMap, smul_zero]
    rw [← AddCircle.coe_nsmul, two_nsmul, add_halves, AddCircle.coe_period]
  have h2 := hinj h1
  rw [AddCircle.coe_eq_zero_of_pos_iff T hT (half_pos hT)] at h2
  obtain ⟨n, hn⟩ := h2
  rw [nsmul_eq_mul] at hn
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, zero_mul] at hn
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
    nlinarith

end EGF
