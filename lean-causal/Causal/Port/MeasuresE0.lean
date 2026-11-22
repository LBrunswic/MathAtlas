import Causal.Port.ModelRowsE0
import Causal.Port.E0ModelRows
import Causal.SingularGeroch
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Admissible measures at the model `E₀`: `λ₃ + λ₁` in the past, `λ₃` in the future

Target `T-ett-measures-e0` (no `sorry`). Cited, **unmarked** (SCOPE (a)):
`prop:mesure_admissible` — `ETT.tex:1726`; `rem:singular_flat_spacetime_therefore` —
`ETT.tex:1508`; `rem:mesure_unilaterale` — `ETT.tex:1713`. Each is about every (strongly causal)
`E_{≥0}`-manifold or singular flat spacetime; here each is instantiated at the model `E₀`, the
first model of the library with `sing₀ ≠ ∅`, through the abstract theorems of
`Causal.SingularGeroch` and `Causal.Remarks.BTZPoints`, fed `E0.modelMeasures`.

> On $\mass{\kappa}$ with $\kappa>0$ the Lebesgue measure $\lambda_3$ of $\RR^3$ satisfies
> properties $1$, $3$ and $4$ in the past and in the future. On $\mass{0}$ it satisfies them
> in the future, whereas $\lambda_3+\lambda_1$ satisfies them in the past, $\lambda_1$ denoting the
> Lebesgue measure of $\sing(\mass{0})\simeq\RR$; [...] the singular term is exactly what property
> $3$ in the past requires along a BTZ line. Restricted to the relatively compact $\U_p$ these
> measures are finite, so property $2$ holds too, and Lemma \ref{lem:restriction_convexe} turns
> properties $3$ and $4$ of the model into properties $3$ and $4$ of $\U_p$. (`ETT.tex:1736–1743`)

> Let $M$ be a strongly causal $\mass{\geq 0}$-manifold. Then $M$ carries a measure $\mu_-$
> admissible in the past and a measure $\mu_+$ admissible in the future. (`ETT.tex:1726–1727`)

> A singular flat spacetime is therefore a differential manifold and satisfies all the
> hypotheses of Geroch's Theorem \ref{theo:geroch}. (`ETT.tex:1509–1510`)

> One cannot ask for admissibility in the past and in the future at once as soon as the spacetime
> carries a BTZ line, and property $4$ is the obstruction. (`ETT.tex:1715–1716`)

## What is proved (no `sorry`)

* **The proof's sentence on `E₀`, as printed** (l.1737–1739): `λ₃` (`volume` on `ℝ × ℂ`) satisfies
  properties 1., 3., 4. in the future (`lam3_future`), `λ₃ + λ₁` (`lam1`: Lebesgue measure on the
  axis) in the past (`lam3_add_lam1_past`). Of properties 1., 3., 4., each fails exactly one on the
  other side (both are infinite, so property 2. fails too):
  `λ₃` property 3. in the past (`lam3_past_profile`: "the singular term is exactly what property 3
  in the past requires", l.1740), `λ₃ + λ₁` property 4. in the future
  (`lam3_add_lam1_future_profile`: "property 4 is the obstruction", l.1716).
* **Finite measures**: every finite measure with the null sets of `λ₃` (resp. `λ₃ + λ₁`) is
  admissible in the future (resp. past) (`admissibleFuture_of_equiv`, `admissiblePast_of_equiv`);
  `muPlus`, `muMinus` (`Measure.toFinite`) are such.
* **The proof's local form** (l.1734–1743): every neighbourhood of every point contains a
  relatively compact causally convex open `U_p` on which `λ₃ + λ₁` and `λ₃`, restricted to `U_p`,
  are admissible in the past and in the future (`paper_measures_local`).
* **The deliverables**: `modelMeasures` (`ModelMeasures` at `E₀`, `U = E₀`), `mesure_admissible`,
  `geroch_hypotheses`, `mesure_unilaterale`, `mesure_unilaterale_sharp` (both one-sided notions
  inhabited, no measure in both). Consumers of `ModelMeasures` instantiated at `E₀`:
  `geroch_sing_i_imp_ii`, `geroch_sing_i_imp_iii` (`theo:geroch_sing`, unmarked).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:mesure_admissible`: `M` a strongly causal `E_{≥0}`-manifold | ⚠ strengthened: `M = E₀` (instance); strongly causal there (`E0.stronglyCausal`), but `mesure_admissible` uses `E0.isCausal` only |
| `rem:singular_flat_spacetime_therefore`: a singular flat spacetime, strongly causal (DEC-18) | ⚠ strengthened: `M = E₀` (`E0.singularFlatAxioms`); strong causality ✓ carried (`E0.stronglyCausal`); "a differential manifold" not formalized |
| `rem:mesure_unilaterale`: a causal `E_{≥0}`-manifold with a BTZ line | ⚠ strengthened: `M = E₀` (`E0.isCausal`, `E0.singE0_zero_nonempty`) |
| `λ₃`, the Lebesgue measure of `ℝ³` (l.1737) | ✓ `volume` on `E₀ = ℝ × ℂ` (SCOPE (d)) |
| `λ₁`, the Lebesgue measure of `sing(E₀) ≃ ℝ` (l.1739) | ✓ `lam1`, the image of `volume` under `τ ↦ (τ, 0)` |
| "restricted to the relatively compact `U_p`" (l.1741) | ✓ carried by `paper_measures_local`; ⚠ replaced in `modelMeasures`: finite measures on all of `E₀` (SCOPE (c)) |

## SCOPE (disclosed)

* **(a) Instances only, nothing marked.** The three rows are about every (strongly causal)
  `E_{≥0}`-manifold or singular flat spacetime; at every such manifold they are
  `Causal.SFAManifolds.mesure_admissible` and the rows of `Causal.Remarks.SingularRowsGeroch`
  (from `Causal.SFAManifolds.singularFlatAxioms` and
  `Causal.MeasuresManifolds.massA_modelMeasures`); they wait on OQ-34/OQ-35 (which `E₀`).
* **(b) The route, checked step by step.** The curves `r ↦ (u + r, r e^{iθ})`, `r ≥ 0`, are
  chronological (`lt_ray`); the frontier of any `≪`-past (or `≪`-future) set, open or not, meets
  each in at most one point (`frontier_ray_subsingleton_of_past`, `_of_future`); the shear
  `(τ, z) ↦ (τ − |z|, z)` preserves `λ₃` (`measurePreserving_shear`, a skew product over the
  identity of `ℂ`); a measurable subset of `ℂ` meeting each open ray from `0` at most once is null
  (`volume_eq_zero_of_ray_subsingleton`, `Complex.lintegral_comp_polarCoord_symm`). Property 4.
  in the past: `J⁻(A) ∖ K⁻(A) ⊂ (∂I⁻(A) ∖ sing₀) ∪ (sing₀ ∩ (J⁻(A) ∖ K⁻(A)))`
  (`Jminus_diff_Kminus_subset`), the second set has at most one point, `τ = sup_A f`, attained
  (`axis_inter_Jminus_diff_Kminus_subsingleton`), and it can have one
  (`axis_inter_Jminus_diff_Kminus_axis`). In the future `J⁺(A) ∖ K⁺(A) ⊂ ∂I⁺(A)`.
* **(c) Finiteness.** `ModelMeasures` asks a causally convex open `U ∋ p` with a measure on it;
  `modelMeasures` takes `U = E₀` with `muMinus`, `muPlus`, finite with the null sets of
  `λ₃ + λ₁`, `λ₃`, as `timelikeLine_modelMeasures` does. The paper's own `U_p` and its own
  restricted measures are `paper_measures_local`.
* **(d) Reading of `λ₃`**: the Lebesgue measure of `ℝ × ℂ ≅ ℝ³`. Properties 1.–4. see a measure
  only through its null sets and its positivity on open sets and axis segments, so every finite
  measure in the class is admissible (`admissible*_of_equiv`).
* **(e) Property 3. through `lem:restriction_convexe`** (l.1742–1743) needs the local form
  `pos_past_inter`, `pos_future_inter`: the mass of `J⁻(q) ∖ J⁻(p)` lies near `q` (an open set
  off the axis, an axis segment on it). Property 3. of the model alone does not give it (finding,
  `REPORT.json`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Model of record:
`Causal.Port.E0*` (strict, ported from gx `c48aa45`).
-/

namespace Causal

open Set Filter Topology MeasureTheory Complex
open scoped Real ENNReal

/-! ### Measure theory on `ℝ × ℂ`: sets meeting rays once are null -/

namespace MeasuresE0

/-- The shear `(τ, z) ↦ (τ − |z|, z)`: in its coordinates `(u, z)` the curves
`r ↦ (u + r, r e^{iθ})` become the rays `r ↦ (u, r e^{iθ})`. -/
noncomputable def shear (x : E0) : E0 := (x.1 - ‖x.2‖, x.2)

/-- The inverse shear `(u, z) ↦ (u + |z|, z)`. -/
noncomputable def unshear (x : E0) : E0 := (x.1 + ‖x.2‖, x.2)

/-- **The shear preserves `λ₃`**: on each vertical line it is a translation (Fubini–Tonelli, as a
skew product over the identity of `ℂ`). -/
theorem measurePreserving_shear :
    MeasurePreserving shear (volume : Measure E0) (volume : Measure E0) := by
  have hG : MeasurePreserving (fun p : ℂ × ℝ => (id p.1, (fun z τ => τ + -‖z‖) p.1 p.2))
      ((volume : Measure ℂ).prod (volume : Measure ℝ))
      ((volume : Measure ℂ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id volume).skew_product
      (continuous_snd.add continuous_fst.norm.neg).measurable
      (Filter.Eventually.of_forall fun z => map_add_right_eq_self volume (-‖z‖))
  have h := (Measure.measurePreserving_swap.comp hG).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℂ)))
  have hf : shear = (Prod.swap ∘ fun p : ℂ × ℝ => (id p.1, (fun z τ => τ + -‖z‖) p.1 p.2)) ∘
      Prod.swap := by
    funext x
    simp [shear, sub_eq_add_neg]
  rw [hf, Measure.volume_eq_prod]
  exact h

/-- `unshear` undoes `shear`. -/
theorem unshear_shear (x : E0) : unshear (shear x) = x := by
  simp [shear, unshear]

theorem continuous_unshear : Continuous unshear := by
  unfold unshear; fun_prop

/-- `Complex.polarCoord.symm (r, θ) = r e^{iθ}`. -/
theorem polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * cexp (p.2 * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- **A measurable subset of `ℂ` meeting every open ray from `0` in at most one point is
Lebesgue-null** (polar coordinates and Fubini–Tonelli in `(r, θ)`). -/
theorem volume_eq_zero_of_ray_subsingleton {T : Set ℂ} (hT : MeasurableSet T)
    (hray : ∀ θ : ℝ, {r : ℝ | 0 < r ∧ (r : ℂ) * cexp (θ * I) ∈ T}.Subsingleton) :
    volume T = 0 := by
  set W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ (p.1 : ℂ) * cexp (p.2 * I) ∈ T}
  have hcont : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I) := by fun_prop
  have hWm : MeasurableSet W :=
    (measurableSet_lt measurable_const measurable_fst).inter (hT.preimage hcont.measurable)
  have hW0 : (volume : Measure (ℝ × ℝ)) W = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hWm]
    have : ∀ θ : ℝ, (volume : Measure ℝ) ((fun r => (r, θ)) ⁻¹' W) = 0 := fun θ =>
      ((hray θ).anti fun r hr => hr).measure_zero _
    simp only [this, lintegral_zero]
  have hzero : ∀ p : ℝ × ℝ, p ∉ W →
      ENNReal.ofReal p.1 • T.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) = 0 := by
    intro p hp
    rcases le_or_gt p.1 0 with h | h
    · simp [ENNReal.ofReal_of_nonpos h]
    · have hnot : Complex.polarCoord.symm p ∉ T := by
        rw [polarCoord_symm_eq]; exact fun hT' => hp ⟨h, hT'⟩
      rw [Set.indicator_of_notMem hnot, smul_zero]
  have hae : ∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict polarCoord.target),
      ENNReal.ofReal p.1 • T.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) = 0 := by
    apply ae_restrict_of_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hW0] with p hp
    exact hzero p hp
  rw [← lintegral_indicator_one hT, ← Complex.lintegral_comp_polarCoord_symm,
    lintegral_congr_ae hae, lintegral_zero]

/-- The curve `r ↦ (u + r, r e^{iθ})` of `E₀`. -/
noncomputable def ray (u θ r : ℝ) : E0 := (u + r, (r : ℂ) * cexp (θ * I))

theorem norm_ofReal_mul_cexp {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖(r : ℂ) * cexp (θ * I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- **A measurable subset of `E₀` meeting every curve `r ↦ (u + r, r e^{iθ})`, `r > 0`, in at
most one point is `λ₃`-null**: shear, then Fubini–Tonelli over `u` and polar coordinates in each
slice. -/
theorem volume_eq_zero_of_shear_ray_subsingleton {S : Set E0} (hS : MeasurableSet S)
    (hray : ∀ u θ : ℝ, {r : ℝ | 0 < r ∧ ray u θ r ∈ S}.Subsingleton) :
    (volume : Measure E0) S = 0 := by
  have hS' : MeasurableSet (unshear ⁻¹' S) := hS.preimage continuous_unshear.measurable
  have h1 : (volume : Measure E0) S = volume (unshear ⁻¹' S) := by
    have h := measurePreserving_shear.measure_preimage hS'.nullMeasurableSet
    have hcomp : shear ⁻¹' (unshear ⁻¹' S) = S := by
      ext x; simp only [mem_preimage, unshear_shear]
    rw [hcomp] at h; exact h
  rw [h1, Measure.volume_eq_prod, Measure.prod_apply hS']
  have : ∀ u : ℝ, (volume : Measure ℂ) (Prod.mk u ⁻¹' (unshear ⁻¹' S)) = 0 := by
    intro u
    refine volume_eq_zero_of_ray_subsingleton (hS'.preimage measurable_prodMk_left) fun θ => ?_
    refine (hray u θ).anti fun r hr => ⟨hr.1, ?_⟩
    have h := hr.2
    simp only [mem_preimage, unshear, norm_ofReal_mul_cexp hr.1.le] at h
    exact h
  simp only [this, lintegral_zero]

end MeasuresE0

namespace E0

open MeasuresE0

/-! ### The curves `r ↦ (u + r, r e^{iθ})` are chronological -/

theorem rad_ray (u θ : ℝ) {r : ℝ} (hr : 0 ≤ r) : rad (ray u θ r) = r :=
  norm_ofReal_mul_cexp hr θ

theorem polar_ray (u θ : ℝ) {r : ℝ} (hr : 0 ≤ r) : Polar (ray u θ r) θ := by
  unfold Polar; rw [rad_ray u θ hr]; rfl

/-- **`r ↦ (u + r, r e^{iθ})` is chronological for `r ≥ 0`**, the start on the axis included:
`ClosedLt (u + r₁) r₁ (u + r₂) r₂ 0` reads `r₁ < r₂ ∧ 0 < (r₂ − r₁)²`. -/
theorem lt_ray {u θ r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h : r₁ < r₂) :
    causality.lt ⊤ (ray u θ r₁) (ray u θ r₂) := by
  have h₂ : 0 ≤ r₂ := h₁.trans h.le
  rw [E0.lt_top_iff, lt_iff_closed]
  refine ⟨θ, θ, polar_ray u θ h₁, polar_ray u θ h₂, ?_⟩
  rw [rad_ray u θ h₁, rad_ray u θ h₂]
  refine ⟨h, ?_⟩
  simp only [ray, sub_self]
  nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 h)]

/-- Below a point of the closure of a `≪`-past set on the curve, the curve is in its interior. -/
theorem ray_mem_interior_of_past {P : Set E0} (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ z y → z ∈ P)
    {u θ r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h : r₁ < r₂) (h₂ : ray u θ r₂ ∈ closure P) :
    ray u θ r₁ ∈ interior P := by
  have h₁' : r₁ < (r₁ + r₂) / 2 := by linarith
  have h₂' : (r₁ + r₂) / 2 < r₂ := by linarith
  obtain ⟨y, hyU, hyP⟩ := mem_closure_iff.1 h₂ _
    (causality.isOpen_lt_right ⊤ (ray u θ ((r₁ + r₂) / 2))) (lt_ray (by linarith) h₂')
  have hr'P : ray u θ ((r₁ + r₂) / 2) ∈ P := hP y hyP _ hyU
  exact mem_interior.2 ⟨{z | causality.lt ⊤ z (ray u θ ((r₁ + r₂) / 2))},
    fun z hz => hP _ hr'P z hz, causality.isOpen_lt_left ⊤ _, lt_ray h₁ h₁'⟩

/-- Above a point of the closure of a `≪`-future set on the curve, the curve is in its
interior. -/
theorem ray_mem_interior_of_future {P : Set E0}
    (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ y z → z ∈ P)
    {u θ r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h : r₁ < r₂) (h₂ : ray u θ r₁ ∈ closure P) :
    ray u θ r₂ ∈ interior P := by
  have h₁' : r₁ < (r₁ + r₂) / 2 := by linarith
  have h₂' : (r₁ + r₂) / 2 < r₂ := by linarith
  obtain ⟨y, hyU, hyP⟩ := mem_closure_iff.1 h₂ _
    (causality.isOpen_lt_left ⊤ (ray u θ ((r₁ + r₂) / 2))) (lt_ray h₁ h₁')
  have hr'P : ray u θ ((r₁ + r₂) / 2) ∈ P := hP y hyP _ hyU
  exact mem_interior.2 ⟨{z | causality.lt ⊤ (ray u θ ((r₁ + r₂) / 2)) z},
    fun z hz => hP _ hr'P z hz, causality.isOpen_lt_right ⊤ _, lt_ray (by linarith) h₂'⟩

/-- **The frontier of a `≪`-past set meets each curve `r ↦ (u + r, r e^{iθ})`, `r ≥ 0`, in at
most one point.** -/
theorem frontier_ray_subsingleton_of_past {P : Set E0}
    (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ z y → z ∈ P) (u θ : ℝ) :
    {r : ℝ | 0 ≤ r ∧ ray u θ r ∈ frontier P}.Subsingleton := by
  intro r hr s hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hr.2.2 (ray_mem_interior_of_past hP hr.1 h (frontier_subset_closure hs.2))
  · exact hs.2.2 (ray_mem_interior_of_past hP hs.1 h (frontier_subset_closure hr.2))

/-- **The frontier of a `≪`-future set meets each curve `r ↦ (u + r, r e^{iθ})`, `r ≥ 0`, in at
most one point.** -/
theorem frontier_ray_subsingleton_of_future {P : Set E0}
    (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ y z → z ∈ P) (u θ : ℝ) :
    {r : ℝ | 0 ≤ r ∧ ray u θ r ∈ frontier P}.Subsingleton := by
  intro r hr s hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hs.2.2 (ray_mem_interior_of_future hP hr.1 h (frontier_subset_closure hr.2))
  · exact hr.2.2 (ray_mem_interior_of_future hP hs.1 h (frontier_subset_closure hs.2))

/-- The frontier of a `≪`-past set of `E₀` is `λ₃`-null. -/
theorem volume_frontier_of_past {P : Set E0} (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ z y → z ∈ P) :
    (volume : Measure E0) (frontier P) = 0 :=
  volume_eq_zero_of_shear_ray_subsingleton isClosed_frontier.measurableSet fun u θ =>
    (frontier_ray_subsingleton_of_past hP u θ).anti fun _ hr => ⟨hr.1.le, hr.2⟩

/-- The frontier of a `≪`-future set of `E₀` is `λ₃`-null. -/
theorem volume_frontier_of_future {P : Set E0}
    (hP : ∀ y ∈ P, ∀ z, causality.lt ⊤ y z → z ∈ P) :
    (volume : Measure E0) (frontier P) = 0 :=
  volume_eq_zero_of_shear_ray_subsingleton isClosed_frontier.measurableSet fun u θ =>
    (frontier_ray_subsingleton_of_future hP u θ).anti fun _ hr => ⟨hr.1.le, hr.2⟩

/-- `∂I⁻(A)` is `λ₃`-null. -/
theorem volume_frontier_Iminus (A : Set E0) :
    (volume : Measure E0) (frontier (causality.Iminus ⊤ A)) = 0 :=
  volume_frontier_of_past fun _ ⟨a, ha, hya⟩ _ hzy => ⟨a, ha, causality.lt_trans hzy hya⟩

/-- `∂I⁺(A)` is `λ₃`-null. -/
theorem volume_frontier_Iplus (A : Set E0) :
    (volume : Measure E0) (frontier (causality.Iplus ⊤ A)) = 0 :=
  volume_frontier_of_future fun _ ⟨a, ha, hay⟩ _ hyz => ⟨a, ha, causality.lt_trans hay hyz⟩

/-- The BTZ line is `λ₃`-null. -/
theorem volume_axis : (volume : Measure E0) axis = 0 := by
  have : axis = (univ : Set ℝ) ×ˢ ({0} : Set ℂ) := by ext x; simp [axis]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]

/-! ### `λ₁`, the Lebesgue measure of the BTZ line -/

/-- **`λ₁`**: the Lebesgue measure of `sing(E₀) ≃ ℝ`, the image of Lebesgue measure under
`τ ↦ (τ, 0)`. -/
noncomputable def lam1 : Measure E0 := Measure.map (fun τ : ℝ => ((τ, (0 : ℂ)) : E0)) volume

theorem measurable_axisEmb : Measurable fun τ : ℝ => ((τ, (0 : ℂ)) : E0) :=
  (continuous_id.prodMk continuous_const).measurable

theorem lam1_apply {s : Set E0} (hs : MeasurableSet s) :
    lam1 s = volume ((fun τ : ℝ => ((τ, (0 : ℂ)) : E0)) ⁻¹' s) :=
  Measure.map_apply measurable_axisEmb hs

instance : SFinite lam1 := by unfold lam1; infer_instance

instance : IsFiniteMeasureOnCompacts lam1 := ⟨fun K hK => by
  rw [lam1_apply hK.measurableSet]
  refine lt_of_le_of_lt (measure_mono ?_) (hK.image continuous_fst).measure_lt_top
  intro τ hτ; exact ⟨_, hτ, rfl⟩⟩

instance : IsFiniteMeasureOnCompacts ((volume : Measure E0) + lam1) := ⟨fun K hK => by
  rw [Measure.add_apply]; exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩

/-- The segment `]a, b]` of the BTZ line. -/
def axisSeg (a b : ℝ) : Set E0 := {x | x ∈ axis ∧ a < x.1 ∧ x.1 ≤ b}

theorem lam1_compl_axis : lam1 axisᶜ = 0 := by
  rw [lam1_apply isClosed_axis.isOpen_compl.measurableSet]
  have : (fun τ : ℝ => ((τ, (0 : ℂ)) : E0)) ⁻¹' axisᶜ = ∅ := by
    ext τ; simp [axis]
  rw [this, measure_empty]

theorem lam1_singleton (x : E0) : lam1 {x} = 0 := by
  rw [lam1_apply (measurableSet_singleton x)]
  refine Set.Subsingleton.measure_zero ?_ _
  intro a ha b hb
  simp only [mem_preimage, mem_singleton_iff] at ha hb
  have := congrArg Prod.fst (ha.trans hb.symm)
  simpa using this

theorem lam1_axisSeg {a b : ℝ} (h : a < b) : 0 < lam1 (axisSeg a b) := by
  have hm : MeasurableSet (axisSeg a b) := isClosed_axis.measurableSet.inter
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))
  rw [lam1_apply hm]
  have : (fun τ : ℝ => ((τ, (0 : ℂ)) : E0)) ⁻¹' axisSeg a b = Ioc a b := by
    ext τ; simp [axisSeg, axis]
  rw [this, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.2 (sub_pos.2 h)

theorem volume_singleton (x : E0) : (volume : Measure E0) {x} = 0 := by
  rw [← Set.singleton_prod_singleton, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton,
    zero_mul]

theorem volume_add_lam1_singleton (x : E0) : ((volume : Measure E0) + lam1) {x} = 0 := by
  rw [Measure.add_apply, volume_singleton, lam1_singleton, add_zero]

theorem volume_add_lam1_pos {O : Set E0} (hO : IsOpen O) (hne : O.Nonempty) :
    0 < ((volume : Measure E0) + lam1) O :=
  (hO.measure_pos volume hne).trans_le (by rw [Measure.add_apply]; exact le_self_add)

theorem volume_add_lam1_axisSeg {a b : ℝ} (h : a < b) :
    0 < ((volume : Measure E0) + lam1) (axisSeg a b) :=
  (lam1_axisSeg h).trans_le (by rw [Measure.add_apply]; exact le_add_self)

/-! ### Properties 3. and 4. for a measure, from its null sets -/

/-- `I⁺(A) ⊂ K⁺(A)` in `E₀`. -/
theorem Iplus_subset_Kplus (A : Set E0) : causality.Iplus ⊤ A ⊆ causality.Kplus ⊤ A := by
  rintro y ⟨a, ha, hay⟩
  have : y ∈ causality.Kplus ⊤ {a} := by rw [Kplus_eq_Iplus]; exact ⟨a, rfl, hay⟩
  exact Causality.Kplus_mono (singleton_subset_iff.2 ha) this

/-- `I⁻(A) ⊂ K⁻(A)` in `E₀`. -/
theorem Iminus_subset_Kminus (A : Set E0) : causality.Iminus ⊤ A ⊆ causality.Kminus ⊤ A := by
  rintro y ⟨a, ha, hya⟩
  by_cases hax : a ∈ axis
  · exact absurd hya (not_lt_of_mem_axis hax ⊤ y)
  · have : y ∈ causality.Kminus ⊤ {a} := by
      rw [Kminus_eq_Iminus_of_not_mem_axis hax]; exact ⟨a, rfl, hya⟩
    exact Causality.Kminus_mono (singleton_subset_iff.2 ha) this

/-- **Property 4. in the future, the inclusion**: `J⁺(A) ∖ K⁺(A) ⊂ ∂I⁺(A)`. -/
theorem Jplus_diff_Kplus_subset_frontier (A : Set E0) :
    causality.Jplus ⊤ A \ causality.Kplus ⊤ A ⊆ frontier (causality.Iplus ⊤ A) := by
  rintro x ⟨hxJ, hxK⟩
  refine ⟨Causality.Jplus_subset_closure_Iplus_of_locZplus E0LM.e0_pushUp E0LM.e0_locZplus ⊤ A
    hxJ, ?_⟩
  rw [Causality.isOpen_Iplus.interior_eq]
  exact fun hx => hxK (Iplus_subset_Kplus A hx)

/-- A point `x` of the BTZ line lies in `K⁻(A)` as soon as `τ(x) < f(a)` for some `a ∈ A`. -/
theorem mem_Kminus_of_lt_fcoord {A : Set E0} {x a : E0} (hx : x ∈ axis) (ha : a ∈ A)
    (h : x.1 < fcoord a) : x ∈ causality.Kminus ⊤ A := by
  refine Causality.Kminus_mono (singleton_subset_iff.2 ha) ?_
  by_cases hax : a ∈ axis
  · rw [Kminus_axis_eq hax]; exact ⟨hx, by rwa [fcoord_of_axis hax] at h⟩
  · rw [Kminus_eq_Iminus_of_not_mem_axis hax]
    exact Precausality.mem_Iminus_singleton.2 (E0.lt_top_iff.2
      ((lt_axis_iff hx).2 ⟨rad_pos.2 hax, h⟩))

/-- **A point `x` of the BTZ line in `J⁻(A) ∖ K⁻(A)` has `τ(x) = max_{a ∈ A} f(a)`**: some
`a ∈ A` has `x ≤ a`, i.e. `τ(x) ≤ f(a)`, and `τ(x) < f(a)` would put `x` in `K⁻(a)`. -/
theorem isGreatest_fcoord_of_mem_axis_inter {A : Set E0} {x : E0}
    (hx : x ∈ axis ∩ (causality.Jminus ⊤ A \ causality.Kminus ⊤ A)) :
    IsGreatest (fcoord '' A) x.1 := by
  obtain ⟨hxa, ⟨a, ha, hle⟩, hxK⟩ := hx
  have h1 : x.1 ≤ fcoord a := (le_axis_iff hxa).1 (E0.le_top_iff.1 hle)
  have hup : ∀ b ∈ A, fcoord b ≤ x.1 := fun b hb =>
    not_lt.1 fun h => hxK (mem_Kminus_of_lt_fcoord hxa hb h)
  refine ⟨⟨a, ha, le_antisymm (hup a ha) h1⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hup b hb

/-- **At most one point of the BTZ line lies in `J⁻(A) ∖ K⁻(A)`**: such a point `x` has
`τ(x) = max_{a ∈ A} f(a)` (`isGreatest_fcoord_of_mem_axis_inter`). -/
theorem axis_inter_Jminus_diff_Kminus_subsingleton (A : Set E0) :
    (axis ∩ (causality.Jminus ⊤ A \ causality.Kminus ⊤ A)).Subsingleton := fun _ hx _ hx' =>
  axis_eq_of_fst_eq hx.1 hx'.1
    ((isGreatest_fcoord_of_mem_axis_inter hx).unique (isGreatest_fcoord_of_mem_axis_inter hx'))

/-- **The axis term is sharp**: at a BTZ point `p`, `sing₀ ∩ (J⁻(p) ∖ K⁻(p)) = {p}`
(`K⁻(p) = J⁻(p) ∖ {p}`), so property 4. in the past forbids an atom at `p`. -/
theorem axis_inter_Jminus_diff_Kminus_axis {p : E0} (hp : p ∈ axis) :
    axis ∩ (causality.Jminus ⊤ {p} \ causality.Kminus ⊤ {p}) = {p} := by
  rw [Kminus_axis hp]
  ext x
  simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨-, hxJ, hx⟩
    by_contra hne
    exact hx ⟨hxJ, hne⟩
  · rintro rfl
    exact ⟨hp, Precausality.mem_Jminus_singleton.2 (causality.le_refl trivial), fun h => h.2 rfl⟩

/-- **Property 4. in the past, the inclusion**:
`J⁻(A) ∖ K⁻(A) ⊂ (∂I⁻(A) ∖ sing₀) ∪ (sing₀ ∩ (J⁻(A) ∖ K⁻(A)))`. -/
theorem Jminus_diff_Kminus_subset (A : Set E0) :
    causality.Jminus ⊤ A \ causality.Kminus ⊤ A ⊆
      (frontier (causality.Iminus ⊤ A) \ axis) ∪
        (axis ∩ (causality.Jminus ⊤ A \ causality.Kminus ⊤ A)) := by
  rintro x ⟨hxJ, hxK⟩
  by_cases hx : x ∈ axis
  · exact Or.inr ⟨hx, hxJ, hxK⟩
  · refine Or.inl ⟨⟨Causality.Jminus_diff_subset_closure_Iminus_of_locZminus E0LM.e0_pushUp
      E0LM.e0_locZminus ⊤ A ⟨hxJ, hx⟩, ?_⟩, hx⟩
    rw [Causality.isOpen_Iminus.interior_eq]
    exact fun h => hxK (Iminus_subset_Kminus A h)

/-- **Property 3. in the future, inside an open set `W ∋ p`**, for every measure positive on
non-empty open sets. -/
theorem pos_future_inter {μ : Measure E0} (hμ : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    {W : Set E0} (hW : IsOpen W) {p q : E0} (hpW : p ∈ W) (hpq : causality.le ⊤ p q)
    (hne : p ≠ q) :
    0 < μ ((causality.Jplus ⊤ {p} \ causality.Jplus ⊤ {q}) ∩ W) := by
  have hp : p ∉ causality.Jplus ⊤ {q} := fun h =>
    hne (isCausal hpq (Precausality.mem_Jplus_singleton.1 h))
  have hpcl : p ∈ closure (causality.Iplus ⊤ {p}) := by
    rw [← ModelRowsE0.e0_densite_a p]
    exact Precausality.mem_Jplus_singleton.2 (causality.le_refl trivial)
  have hO : IsOpen ((causality.Jplus ⊤ {q})ᶜ ∩ W) := (isClosed_Jplus q).isOpen_compl.inter hW
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hpcl _ hO ⟨hp, hpW⟩
  refine (hμ _ (Causality.isOpen_Iplus.inter hO) ⟨y, hy2, hy1⟩).trans_le (measure_mono ?_)
  exact fun z hz => ⟨⟨Causality.Iplus_subset_Jplus hz.1, hz.2.1⟩, hz.2.2⟩

/-- **Property 3. in the future** for every measure positive on non-empty open sets. -/
theorem pos_future {μ : Measure E0} (hμ : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    {p q : E0} (hpq : causality.le ⊤ p q) (hne : p ≠ q) :
    0 < μ (causality.Jplus ⊤ {p} \ causality.Jplus ⊤ {q}) := by
  simpa using pos_future_inter hμ isOpen_univ (mem_univ p) hpq hne

/-- **Property 4. in the future** for every measure absolutely continuous w.r.t. `λ₃`. -/
theorem null_future {μ : Measure E0} (hμ : μ ≪ volume) (A : Set E0) :
    μ (causality.Jplus ⊤ A \ causality.Kplus ⊤ A) = 0 :=
  hμ (measure_mono_null (Jplus_diff_Kplus_subset_frontier A) (volume_frontier_Iplus A))

/-- **Property 3. in the past, inside an open set `W ∋ q`**, for every measure positive on
non-empty open sets and on the segments of the BTZ line. -/
theorem pos_past_inter {μ : Measure E0} (hμ : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    (hseg : ∀ a b : ℝ, a < b → 0 < μ (axisSeg a b)) {W : Set E0} (hW : IsOpen W) {p q : E0}
    (hqW : q ∈ W) (hpq : causality.le ⊤ p q) (hne : p ≠ q) :
    0 < μ ((causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p}) ∩ W) := by
  by_cases hq : q ∈ axis
  · -- on the axis: `p` lies on it below `q`, and `λ₁` sees the segment `]p, q]` near `q`
    have hp : p ∈ causality.Jminus ⊤ {q} := Precausality.mem_Jminus_singleton.2 hpq
    rw [Jminus_axis hq] at hp
    have hlt : p.1 < q.1 := lt_of_le_of_ne hp.2 fun h => hne (axis_eq_of_fst_eq hp.1 hq h)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW q hqW
    have ha : max p.1 (q.1 - δ / 2) < q.1 := max_lt hlt (by linarith)
    refine (hseg _ _ ha).trans_le (measure_mono ?_)
    rintro x ⟨hx, hx1, hx2⟩
    have hxp : p.1 < x.1 := (le_max_left _ _).trans_lt hx1
    have hxq : q.1 - δ / 2 < x.1 := (le_max_right _ _).trans_lt hx1
    refine ⟨⟨?_, ?_⟩, hball ?_⟩
    · rw [Jminus_axis hq]; exact ⟨hx, hx2⟩
    · rw [Jminus_axis hp.1]; exact fun h => (not_le.2 hxp) h.2
    · rw [Metric.mem_ball, dist_axis hq x, rad_eq_zero.2 hx, abs_of_nonpos (by linarith)]
      exact max_lt (by linarith) hδ
  · -- off the axis: `J⁻(q) = cl I⁻(q)` and `q ∉ J⁻(p)`
    have hq' : q ∉ causality.Jminus ⊤ {p} := fun h =>
      hne (isCausal hpq (Precausality.mem_Jminus_singleton.1 h))
    have hqcl : q ∈ closure (causality.Iminus ⊤ {q}) := by
      rw [← ModelRowsE0.e0_densite_b hq]
      exact Precausality.mem_Jminus_singleton.2 (causality.le_refl trivial)
    have hO : IsOpen ((causality.Jminus ⊤ {p})ᶜ ∩ W) := (isClosed_Jminus p).isOpen_compl.inter hW
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hqcl _ hO ⟨hq', hqW⟩
    refine (hμ _ (Causality.isOpen_Iminus.inter hO) ⟨y, hy2, hy1⟩).trans_le (measure_mono ?_)
    exact fun z hz => ⟨⟨Causality.Iminus_subset_Jminus hz.1, hz.2.1⟩, hz.2.2⟩

/-- **Property 3. in the past** for every measure positive on non-empty open sets and on the
segments of the BTZ line. -/
theorem pos_past {μ : Measure E0} (hμ : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    (hseg : ∀ a b : ℝ, a < b → 0 < μ (axisSeg a b)) {p q : E0} (hpq : causality.le ⊤ p q)
    (hne : p ≠ q) : 0 < μ (causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p}) := by
  simpa using pos_past_inter hμ hseg isOpen_univ (mem_univ q) hpq hne

/-- **Property 4. in the past** for every measure absolutely continuous w.r.t. `λ₃ + λ₁`. -/
theorem null_past {μ : Measure E0} (hμ : μ ≪ volume + lam1) (A : Set E0) :
    μ (causality.Jminus ⊤ A \ causality.Kminus ⊤ A) = 0 := by
  apply hμ
  refine measure_mono_null (Jminus_diff_Kminus_subset A) (measure_union_null ?_ ?_)
  · rw [Measure.add_apply, measure_mono_null sdiff_subset (volume_frontier_Iminus A),
      measure_mono_null (fun x hx => hx.2) lam1_compl_axis, add_zero]
  · rcases (axis_inter_Jminus_diff_Kminus_subsingleton A).eq_empty_or_singleton with h | ⟨x, h⟩
    · rw [h, measure_empty]
    · rw [h, volume_add_lam1_singleton]

/-! ### The paper's measures: `λ₃` in the future, `λ₃ + λ₁` in the past -/

/-- **`λ₃` satisfies properties 1., 3. and 4. in the future** (`ETT.tex:1737–1738`). -/
theorem lam3_future :
    (volume : Measure E0).Regular ∧
      (∀ ⦃p q : E0⦄, causality.le ⊤ p q → p ≠ q →
        0 < (volume : Measure E0) (causality.Jplus ⊤ {p} \ causality.Jplus ⊤ {q})) ∧
      ∀ A : Set E0, (volume : Measure E0) (causality.Jplus ⊤ A \ causality.Kplus ⊤ A) = 0 :=
  ⟨inferInstance, fun _ _ hpq hne => pos_future (fun _ hO hne' => hO.measure_pos volume hne')
    hpq hne, null_future Measure.AbsolutelyContinuous.rfl⟩

/-- **`λ₃ + λ₁` satisfies properties 1., 3. and 4. in the past** (`ETT.tex:1738–1739`). -/
theorem lam3_add_lam1_past :
    ((volume : Measure E0) + lam1).Regular ∧
      (∀ ⦃p q : E0⦄, causality.le ⊤ p q → p ≠ q →
        0 < ((volume : Measure E0) + lam1) (causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p})) ∧
      ∀ A : Set E0,
        ((volume : Measure E0) + lam1) (causality.Jminus ⊤ A \ causality.Kminus ⊤ A) = 0 :=
  ⟨inferInstance, fun _ _ hpq hne => pos_past (fun _ hO hne' => volume_add_lam1_pos hO hne')
    (fun _ _ h => volume_add_lam1_axisSeg h) hpq hne, null_past Measure.AbsolutelyContinuous.rfl⟩

/-- **"The singular term is exactly what property 3 in the past requires along a BTZ line"**
(`ETT.tex:1740–1741`): `λ₃` alone fails property 3. in the past, at two points of the axis. -/
theorem lam3_not_pos_past :
    ∃ p q : E0, causality.le ⊤ p q ∧ p ≠ q ∧
      (volume : Measure E0) (causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p}) = 0 := by
  have hq : (((1 : ℝ), (0 : ℂ)) : E0) ∈ axis := rfl
  refine ⟨((0 : ℝ), (0 : ℂ)), ((1 : ℝ), (0 : ℂ)), E0.le_top_iff.2 (le_axis rfl hq (by norm_num)),
    fun h => by simpa using congrArg Prod.fst h, ?_⟩
  exact measure_mono_null (sdiff_subset.trans (Jminus_axis_subset hq ⊤)) volume_axis

/-! ### Finite measures in the class of `λ₃`, of `λ₃ + λ₁` -/

/-- **Every finite measure with the null sets of `λ₃` is admissible in the future.** -/
theorem admissibleFuture_of_equiv {μ : Measure E0} [IsFiniteMeasure μ] (h₁ : μ ≪ volume)
    (h₂ : (volume : Measure E0) ≪ μ) : causality.AdmissibleFuture μ where
  regular := inferInstance
  finite := measure_lt_top μ univ
  pos := fun _ _ hpq hne => pos_future (fun _ hO hne' =>
    pos_iff_ne_zero.2 fun h0 => (hO.measure_pos volume hne').ne' (h₂ h0)) hpq hne
  null := null_future h₁

/-- **Every finite measure with the null sets of `λ₃ + λ₁` is admissible in the past.** -/
theorem admissiblePast_of_equiv {μ : Measure E0} [IsFiniteMeasure μ] (h₁ : μ ≪ volume + lam1)
    (h₂ : (volume : Measure E0) + lam1 ≪ μ) : causality.AdmissiblePast μ where
  regular := inferInstance
  finite := measure_lt_top μ univ
  pos := fun _ _ hpq hne => pos_past
    (fun _ hO hne' => pos_iff_ne_zero.2 fun h0 => (volume_add_lam1_pos hO hne').ne' (h₂ h0))
    (fun _ _ h => pos_iff_ne_zero.2 fun h0 => (volume_add_lam1_axisSeg h).ne' (h₂ h0)) hpq hne
  null := null_past h₁

/-- **`μ₊`**: a finite measure with the null sets of `λ₃`. -/
noncomputable def muPlus : Measure E0 := (volume : Measure E0).toFinite

/-- **`μ₋`**: a finite measure with the null sets of `λ₃ + λ₁`. -/
noncomputable def muMinus : Measure E0 := ((volume : Measure E0) + lam1).toFinite

instance : IsFiniteMeasure muPlus := by unfold muPlus; infer_instance

instance : IsFiniteMeasure muMinus := by unfold muMinus; infer_instance

/-- `μ₊` is admissible in the future. -/
theorem admissibleFuture_muPlus : causality.AdmissibleFuture muPlus :=
  admissibleFuture_of_equiv (toFinite_absolutelyContinuous _) (absolutelyContinuous_toFinite _)

/-- `μ₋` is admissible in the past. -/
theorem admissiblePast_muMinus : causality.AdmissiblePast muMinus :=
  admissiblePast_of_equiv (toFinite_absolutelyContinuous _) (absolutelyContinuous_toFinite _)

/-! ### The deliverables -/

/-- **`ModelMeasures` at `E₀`**, with `U = E₀`: `μ₋` admissible in the past, `μ₊` in the future.
The first witness of `ModelMeasures` with a BTZ point. -/
theorem modelMeasures : causality.ModelMeasures :=
  ⟨fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, muMinus,
      Causality.admissiblePastOn_top.2 admissiblePast_muMinus⟩,
    fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, muPlus,
      Causality.admissibleFutureOn_top.2 admissibleFuture_muPlus⟩⟩

/-- **`prop:mesure_admissible` at `E₀`**, through `SingularFlatAxioms.mesure_admissible`: the first
instance with `sing₀ ≠ ∅`. -/
theorem mesure_admissible :
    (∃ μ : Measure E0, causality.AdmissiblePast μ) ∧
      ∃ μ : Measure E0, causality.AdmissibleFuture μ :=
  singularFlatAxioms.mesure_admissible isCausal modelMeasures

/-- **`rem:singular_flat_spacetime_therefore` at `E₀`** (`SingularFlatAxioms.geroch_hypotheses`,
strong causality by `E0.stronglyCausal`, DEC-18): every hypothesis of `theo:geroch`, the pair of
admissible measures included. -/
theorem geroch_hypotheses :
    TopologicalSpace.MetrizableSpace E0 ∧ LocallyCompactSpace E0 ∧ causality.Tarentin ∧
      causality.CausallyArcConnected ∧ causality.StronglyCausal ∧
      (∀ p : E0, causality.Jminus ⊤ {p} ≠ {p}) ∧ (∀ p : E0, causality.Jplus ⊤ {p} ≠ {p}) ∧
      ∃ μp μm : Measure E0, causality.AdmissibleFuture μp ∧ causality.AdmissiblePast μm :=
  singularFlatAxioms.geroch_hypotheses stronglyCausal modelMeasures

/-- **`rem:mesure_unilaterale` at `E₀`** (`SingularFlatAxioms.mesure_unilaterale`): no measure on
`E₀` is admissible in the past and in the future at once. -/
theorem mesure_unilaterale (μ : Measure E0) :
    ¬ (causality.AdmissiblePast μ ∧ causality.AdmissibleFuture μ) :=
  singularFlatAxioms.mesure_unilaterale isCausal singE0_zero_nonempty μ

/-- **`rem:mesure_unilaterale` at `E₀`, non-vacuously**: each one-sided notion has an inhabitant,
and no measure has both. -/
theorem mesure_unilaterale_sharp :
    (∃ μ : Measure E0, causality.AdmissiblePast μ) ∧
      (∃ μ : Measure E0, causality.AdmissibleFuture μ) ∧
      ∀ μ : Measure E0, ¬ (causality.AdmissiblePast μ ∧ causality.AdmissibleFuture μ) :=
  ⟨⟨_, admissiblePast_muMinus⟩, ⟨_, admissibleFuture_muPlus⟩, mesure_unilaterale⟩

/-! ### Each measure fails the other side, at the property the paper names -/

/-- **`λ₃ + λ₁` fails property 4. in the future** (the computation of `rem:mesure_unilaterale`,
`ETT.tex:1719–1722`, at `E₀`): the segment `]0, 1]` of the axis lies in `J⁺(0) ∖ K⁺(0)`, since
`K⁺(0) = I⁺(0)` and the axis has empty chronological past, and `λ₁` charges it. -/
theorem lam3_add_lam1_not_null_future :
    ∃ A : Set E0,
      ((volume : Measure E0) + lam1) (causality.Jplus ⊤ A \ causality.Kplus ⊤ A) ≠ 0 := by
  have hp : (((0 : ℝ), (0 : ℂ)) : E0) ∈ axis := rfl
  refine ⟨{((0 : ℝ), (0 : ℂ))}, ?_⟩
  have hsub : axisSeg 0 1 ⊆ causality.Jplus ⊤ {((0 : ℝ), (0 : ℂ))} \
      causality.Kplus ⊤ {((0 : ℝ), (0 : ℂ))} := by
    rintro x ⟨hx, hx1, -⟩
    rw [Kplus_eq_Iplus, Jplus_axis hp, Iplus_axis hp]
    refine ⟨?_, fun h => ?_⟩
    · show (0 : ℝ) ≤ fcoord x
      rw [fcoord_of_axis hx]; exact hx1.le
    · have h1 := h.1
      rw [rad_eq_zero.2 hx] at h1
      exact lt_irrefl 0 h1
  exact ((volume_add_lam1_axisSeg one_pos).trans_le (measure_mono hsub)).ne'

/-- `μ₋` fails property 4. in the future. -/
theorem muMinus_not_null_future :
    ∃ A : Set E0, muMinus (causality.Jplus ⊤ A \ causality.Kplus ⊤ A) ≠ 0 := by
  obtain ⟨A, hA⟩ := lam3_add_lam1_not_null_future
  exact ⟨A, fun h0 => hA (absolutelyContinuous_toFinite _ h0)⟩

/-- `μ₊` fails property 3. in the past, at two points of the axis. -/
theorem muPlus_not_pos_past :
    ∃ p q : E0, causality.le ⊤ p q ∧ p ≠ q ∧
      muPlus (causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p}) = 0 := by
  obtain ⟨p, q, hpq, hne, h0⟩ := lam3_not_pos_past
  exact ⟨p, q, hpq, hne, toFinite_absolutelyContinuous _ h0⟩

/-- **`λ₃` in the past**: properties 1. and 4. hold, property 3. fails. -/
theorem lam3_past_profile :
    (volume : Measure E0).Regular ∧
      (∀ A : Set E0, (volume : Measure E0) (causality.Jminus ⊤ A \ causality.Kminus ⊤ A) = 0) ∧
      ∃ p q : E0, causality.le ⊤ p q ∧ p ≠ q ∧
        (volume : Measure E0) (causality.Jminus ⊤ {q} \ causality.Jminus ⊤ {p}) = 0 :=
  ⟨inferInstance, null_past (Measure.AbsolutelyContinuous.rfl.add_right _), lam3_not_pos_past⟩

/-- **`λ₃ + λ₁` in the future**: properties 1. and 3. hold, property 4. fails. -/
theorem lam3_add_lam1_future_profile :
    ((volume : Measure E0) + lam1).Regular ∧
      (∀ ⦃p q : E0⦄, causality.le ⊤ p q → p ≠ q →
        0 < ((volume : Measure E0) + lam1) (causality.Jplus ⊤ {p} \ causality.Jplus ⊤ {q})) ∧
      ∃ A : Set E0,
        ((volume : Measure E0) + lam1) (causality.Jplus ⊤ A \ causality.Kplus ⊤ A) ≠ 0 :=
  ⟨inferInstance, fun _ _ hpq hne => pos_future (fun _ hO hne' => volume_add_lam1_pos hO hne')
    hpq hne, lam3_add_lam1_not_null_future⟩

/-! ### Restriction to a causally convex open set (`lem:restriction_convexe`, `ETT.tex:1742`) -/

theorem muPlus_pos {O : Set E0} (hO : IsOpen O) (hne : O.Nonempty) : 0 < muPlus O :=
  pos_iff_ne_zero.2 fun h0 => (hO.measure_pos volume hne).ne' (absolutelyContinuous_toFinite _ h0)

theorem muMinus_pos {O : Set E0} (hO : IsOpen O) (hne : O.Nonempty) : 0 < muMinus O :=
  pos_iff_ne_zero.2 fun h0 => (volume_add_lam1_pos hO hne).ne' (absolutelyContinuous_toFinite _ h0)

theorem muMinus_axisSeg {a b : ℝ} (h : a < b) : 0 < muMinus (axisSeg a b) :=
  pos_iff_ne_zero.2 fun h0 => (volume_add_lam1_axisSeg h).ne' (absolutelyContinuous_toFinite _ h0)

/-- **Restriction in the past**: a measure absolutely continuous w.r.t. `λ₃ + λ₁`, positive on
non-empty open sets and on the segments of the axis, restricted to a causally convex open `V` on
which it is finite, is admissible in the past on `V`. Property 4. passes by
`lem:restriction_convexe` alone; property 3. uses the local form `pos_past_inter` (the mass of
`J⁻(q) ∖ J⁻(p)` is found inside `V`, near `q`). -/
theorem admissiblePastOn_restrict_of {μ : Measure E0} {V : TopologicalSpace.Opens E0}
    [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ volume + lam1)
    (hO : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    (hseg : ∀ a b : ℝ, a < b → 0 < μ (axisSeg a b))
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) :
    causality.AdmissiblePastOn V (μ.restrict V) := by
  have hVm : MeasurableSet (V : Set E0) := V.isOpen.measurableSet
  refine ⟨?_, inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A hA => ?_⟩
  · rw [Measure.restrict_apply' hVm, compl_inter_self, measure_empty]
  · have hpV : p ∈ V := causality.le_mem_left hpq
    have hqV : q ∈ V := causality.le_mem_right hpq
    rw [(Causality.restriction_convexe_past causallyArcConnected hV
        (singleton_subset_iff.2 hqV)).1,
      (Causality.restriction_convexe_past causallyArcConnected hV
        (singleton_subset_iff.2 hpV)).1,
      Measure.restrict_apply' hVm]
    refine (pos_past_inter hO hseg V.isOpen hqV (causality.le_mono le_top hpq) hne).trans_le
      (measure_mono ?_)
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h3⟩, fun h => h2 h.1⟩, h3⟩
  · rw [(Causality.restriction_convexe_past causallyArcConnected hV hA).1,
      (Causality.restriction_convexe_past causallyArcConnected hV hA).2.2]
    refine le_antisymm (le_trans (Measure.restrict_le_self _) ?_) zero_le
    refine (measure_mono ?_).trans (null_past h₁ A).le
    exact fun x hx => ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩

/-- **Restriction in the future**: a measure absolutely continuous w.r.t. `λ₃` and positive on
non-empty open sets, restricted to a causally convex open `V` on which it is finite, is
admissible in the future on `V`. -/
theorem admissibleFutureOn_restrict_of {μ : Measure E0} {V : TopologicalSpace.Opens E0}
    [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ volume)
    (hO : ∀ O : Set E0, IsOpen O → O.Nonempty → 0 < μ O)
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) :
    causality.AdmissibleFutureOn V (μ.restrict V) := by
  have hVm : MeasurableSet (V : Set E0) := V.isOpen.measurableSet
  refine ⟨?_, inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A hA => ?_⟩
  · rw [Measure.restrict_apply' hVm, compl_inter_self, measure_empty]
  · have hpV : p ∈ V := causality.le_mem_left hpq
    have hqV : q ∈ V := causality.le_mem_right hpq
    rw [(Causality.restriction_convexe_future causallyArcConnected hV
        (singleton_subset_iff.2 hpV)).1,
      (Causality.restriction_convexe_future causallyArcConnected hV
        (singleton_subset_iff.2 hqV)).1,
      Measure.restrict_apply' hVm]
    refine (pos_future_inter hO V.isOpen hpV (causality.le_mono le_top hpq) hne).trans_le
      (measure_mono ?_)
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h3⟩, fun h => h2 h.1⟩, h3⟩
  · rw [(Causality.restriction_convexe_future causallyArcConnected hV hA).1,
      (Causality.restriction_convexe_future causallyArcConnected hV hA).2.2]
    refine le_antisymm (le_trans (Measure.restrict_le_self _) ?_) zero_le
    refine (measure_mono ?_).trans (null_future h₁ A).le
    exact fun x hx => ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩

/-- `μ₋` restricted to a causally convex open `V` is admissible in the past on `V`. -/
theorem admissiblePastOn_restrict {V : TopologicalSpace.Opens E0}
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) :
    causality.AdmissiblePastOn V (muMinus.restrict V) :=
  admissiblePastOn_restrict_of (toFinite_absolutelyContinuous _)
    (fun _ hO hne => muMinus_pos hO hne) (fun _ _ h => muMinus_axisSeg h) hV

/-- `μ₊` restricted to a causally convex open `V` is admissible in the future on `V`. -/
theorem admissibleFutureOn_restrict {V : TopologicalSpace.Opens E0}
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) :
    causality.AdmissibleFutureOn V (muPlus.restrict V) :=
  admissibleFutureOn_restrict_of (toFinite_absolutelyContinuous _)
    (fun _ hO hne => muPlus_pos hO hne) hV

/-- A measure finite on compact sets is finite on a relatively compact set. -/
theorem isFiniteMeasure_restrict_of_isCompact_closure {μ : Measure E0}
    [IsFiniteMeasureOnCompacts μ] {V : Set E0} (hV : IsCompact (closure V)) :
    IsFiniteMeasure (μ.restrict V) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (measure_mono subset_closure).trans_lt hV.measure_lt_top

/-- **The paper's measure in the past**: `λ₃ + λ₁` restricted to a relatively compact causally
convex open `V` is admissible in the past on `V` (`ETT.tex:1741–1743`). -/
theorem lam3_add_lam1_admissiblePastOn {V : TopologicalSpace.Opens E0}
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) (hc : IsCompact (closure (V : Set E0))) :
    causality.AdmissiblePastOn V (((volume : Measure E0) + lam1).restrict V) := by
  haveI := isFiniteMeasure_restrict_of_isCompact_closure (μ := (volume : Measure E0) + lam1) hc
  exact admissiblePastOn_restrict_of Measure.AbsolutelyContinuous.rfl
    (fun _ hO hne => volume_add_lam1_pos hO hne) (fun _ _ h => volume_add_lam1_axisSeg h) hV

/-- **The paper's measure in the future**: `λ₃` restricted to a relatively compact causally convex
open `V` is admissible in the future on `V` (`ETT.tex:1741–1743`). -/
theorem lam3_admissibleFutureOn {V : TopologicalSpace.Opens E0}
    (hV : causality.CausallyConvexIn (V : Set E0) ⊤) (hc : IsCompact (closure (V : Set E0))) :
    causality.AdmissibleFutureOn V ((volume : Measure E0).restrict V) := by
  haveI := isFiniteMeasure_restrict_of_isCompact_closure (μ := (volume : Measure E0)) hc
  exact admissibleFutureOn_restrict_of Measure.AbsolutelyContinuous.rfl
    (fun _ hO hne => hO.measure_pos volume hne) hV

/-- **Hypothesis (i) of `prop:mesure_dieckmann_topo` at `E₀`, as the paper's proof gives it**
(`ETT.tex:1734–1743`): every neighbourhood `N` of every point `p` contains a relatively compact
open neighbourhood `U` of `p`, causally convex in `E₀`, on which `λ₃ + λ₁` restricted to `U` is
admissible in the past and `λ₃` restricted to `U` is admissible in the future. -/
theorem paper_measures_local (p : E0) {N : Set E0} (hN : N ∈ 𝓝 p) :
    ∃ U : TopologicalSpace.Opens E0, p ∈ U ∧ (U : Set E0) ⊆ N ∧
      IsCompact (closure (U : Set E0)) ∧ causality.CausallyConvexIn (U : Set E0) ⊤ ∧
      causality.AdmissiblePastOn U (((volume : Measure E0) + lam1).restrict U) ∧
      causality.AdmissibleFutureOn U ((volume : Measure E0).restrict U) := by
  obtain ⟨U, hpU, hUN, hU⟩ := ModelRowsE0.e0_stronglyCausalOpen p (N ∩ Metric.ball p 1)
    (inter_mem hN (Metric.ball_mem_nhds p one_pos))
  have hc : IsCompact (closure (U : Set E0)) :=
    (isCompact_closedBall p 1).of_isClosed_subset isClosed_closure
      ((closure_mono (hUN.trans inter_subset_right)).trans Metric.closure_ball_subset_closedBall)
  exact ⟨U, hpU, hUN.trans inter_subset_left, hc, hU, lam3_add_lam1_admissiblePastOn hU hc,
    lam3_admissibleFutureOn hU hc⟩

/-- **The paper's local form of hypothesis (i)** (`ETT.tex:1734–1743`) at `E₀`, with the finite
measures `μ₋`, `μ₊`: every neighbourhood of every point contains a causally convex open
neighbourhood carrying a measure admissible in the past and one admissible in the future. -/
theorem modelMeasures_local (p : E0) {N : Set E0} (hN : N ∈ 𝓝 p) :
    ∃ U : TopologicalSpace.Opens E0, p ∈ U ∧ (U : Set E0) ⊆ N ∧
      causality.CausallyConvexIn (U : Set E0) ⊤ ∧
      (∃ ν : Measure E0, causality.AdmissiblePastOn U ν) ∧
      ∃ ν : Measure E0, causality.AdmissibleFutureOn U ν := by
  obtain ⟨U, hpU, hUN, -, hU, hpast, hfut⟩ := paper_measures_local p hN
  exact ⟨U, hpU, hUN, hU, ⟨_, hpast⟩, ⟨_, hfut⟩⟩

/-! ### Consumers of `ModelMeasures` at a model with a BTZ line -/

/-- `theo:geroch_sing` (i)⇒(ii) instantiated at `E₀` (`SingularFlatAxioms.geroch_sing_i_imp_ii`,
`E0.globallyHyperbolic`): a Cauchy time function, strictly increasing along `≤`. -/
theorem geroch_sing_i_imp_ii :
    ∃ T : E0 → ℝ, causality.IsCauchyTimeFunction T ∧
      ∀ x y, causality.le ⊤ x y → x ≠ y → T x < T y :=
  singularFlatAxioms.geroch_sing_i_imp_ii modelMeasures globallyHyperbolic

/-- `theo:geroch_sing` (i)⇒(iii) instantiated at `E₀`: a Cauchy surface. -/
theorem geroch_sing_i_imp_iii : ∃ S : Set E0, causality.IsCauchySurface S :=
  singularFlatAxioms.geroch_sing_i_imp_iii modelMeasures globallyHyperbolic

end E0

end Causal
