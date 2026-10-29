import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable weighted sums of finite regular measures

No label of the paper is certified here: this file carries the measure theory used by
`prop:mesure_dieckmann_topo` (`Causal.MeasureLocal`), in the proof of `ETT.tex:1103`:

> Set $\mu := \sum_{n\in \N} 2^{-n-1} \mu_n$.
> Since each $\mu_n$ is a normalised regular Borel measure, $\mu$ is a regular Borel measure of
> finite total mass.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| each `μ_n` a regular Borel measure | ✓ carried: `BorelSpace`, `(μ i).Regular` |
| the family indexed by `ℕ` | ⚠ weakened: any countable index type |
| `μ_n(U_n) = 1`, weights `2^{-n-1}` | ⚠ weakened: any family of finite measures; the weights are produced by `exists_weights_tsum_lt` and are positive and finite |
| `M` Hausdorff (`def:category_topological_spacetimes`) | ⚠ weakened: `R1Space` |

## SCOPE (disclosed)

* **Regularity of a countable sum is not a formality.** Outer regularity is not stable under
  countable intersections of open sets, so `μ := ∑ μ_n` is not outer regular term by term. The
  proof here goes through inner regularity by *closed* sets on open sets, which is stable under
  countable sums (`innerRegularWRT_sum`, a finite union of closed sets being closed), and
  `InnerRegularWRT.weaklyRegular_of_finite` (mathlib), which turns it into outer regularity for a *finite*
  measure. The passage from compact to closed sets is where `R1Space` is used.
* The inner-regularity lemmas `innerRegularWRT_add`, `innerRegularWRT_finset_sum`,
  `innerRegularWRT_sum` are mathlib's instances for `InnerRegular` (`μ + ν`, finite sums,
  `Measure.sum`) generalised to `InnerRegularWRT p q` for a class `p` closed under binary union.
* `regular_map_subtype_val`, `map_subtype_val_compl_null`, `exists_regular_subtype_of_compl_null`
  justify reading "a regular Borel measure on the open set `U`" as "a regular measure on `M`
  carried by `U`" (`Causal.MeasureLocal`, `AdmissiblePastOn`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology MeasureTheory Measure

open scoped ENNReal NNReal

universe u v

variable {α : Type u} [MeasurableSpace α] {p q : Set α → Prop}

/-! ### Inner regularity of sums -/

/-- Inner regularity with respect to a class closed under binary union passes to `μ + ν`. -/
theorem innerRegularWRT_add {μ ν : Measure α} (hp : ∀ s t, p s → p t → p (s ∪ t))
    (hμ : μ.InnerRegularWRT p q) (hν : ν.InnerRegularWRT p q) :
    (μ + ν).InnerRegularWRT p q := by
  intro s hs r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ s) 0 with h | h
  · simp only [h, zero_add] at hr
    obtain ⟨K, Ks, hK, h'K⟩ := hν hs r hr
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases eq_or_ne (ν s) 0 with h' | h'
  · simp only [h', add_zero] at hr
    obtain ⟨K, Ks, hK, h'K⟩ := hμ hs r hr
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_lt_add_of_lt_add hr h h'
  obtain ⟨K, Ks, hK, h'K⟩ := hμ hs u hu
  obtain ⟨K', K's, hK', h'K'⟩ := hν hs v hv
  refine ⟨K ∪ K', union_subset Ks K's, hp _ _ hK hK', huv.trans_le ?_⟩
  apply (add_le_add h'K.le h'K'.le).trans
  simp only [Measure.coe_add, Pi.add_apply]
  gcongr <;> simp

/-- Inner regularity with respect to a class closed under binary union passes to finite sums. -/
theorem innerRegularWRT_finset_sum {ι : Type v} {μ : ι → Measure α}
    (hp : ∀ s t, p s → p t → p (s ∪ t)) (h : ∀ i, (μ i).InnerRegularWRT p q) (a : Finset ι) :
    (∑ i ∈ a, μ i).InnerRegularWRT p q := by
  classical
  induction a using Finset.induction with
  | empty =>
    intro s _ r hr
    simp at hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact innerRegularWRT_add hp (h a) ih

/-- Inner regularity with respect to a class closed under binary union passes to countable
sums. No finiteness is needed. -/
theorem innerRegularWRT_sum {ι : Type v} [Countable ι] {μ : ι → Measure α}
    (hp : ∀ s t, p s → p t → p (s ∪ t)) (h : ∀ i, (μ i).InnerRegularWRT p q) :
    (Measure.sum μ).InnerRegularWRT p q := by
  intro s hs r hr
  have hlim : Tendsto (fun a : Finset ι => ∑ i ∈ a, μ i s) atTop (𝓝 (Measure.sum μ s)) := by
    rw [Measure.sum_apply_of_countable]
    exact ENNReal.summable.hasSum
  obtain ⟨a, ha⟩ : ∃ a : Finset ι, r < (∑ i ∈ a, μ i) s := by
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    exact ((tendsto_order.1 hlim).1 r hr).exists
  obtain ⟨K, Ks, hK, h'K⟩ := innerRegularWRT_finset_sum hp h a hs r ha
  refine ⟨K, Ks, hK, h'K.trans_le ?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  exact (ENNReal.sum_le_tsum _).trans (Measure.le_sum_apply _ _)

/-! ### Regularity of a countable sum of finite total mass -/

/-- A countable sum of regular measures with finite total mass is regular. -/
theorem regular_sum [TopologicalSpace α] [R1Space α] [BorelSpace α] {ι : Type v} [Countable ι]
    {μ : ι → Measure α} (h : ∀ i, (μ i).Regular) (hfin : Measure.sum μ univ < ∞) :
    (Measure.sum μ).Regular := by
  haveI : IsFiniteMeasure (Measure.sum μ) := ⟨hfin⟩
  have hclosed : (Measure.sum μ).InnerRegularWRT IsClosed IsOpen :=
    innerRegularWRT_sum (fun _ _ hs ht => hs.union ht) fun i => by
      haveI := h i
      exact WeaklyRegular.innerRegular
  haveI := InnerRegularWRT.weaklyRegular_of_finite (Measure.sum μ) hclosed
  exact ⟨innerRegularWRT_sum (fun _ _ hs ht => hs.union ht) fun i => (h i).innerRegular⟩

/-! ### Weights -/

/-- For a countable family of finite masses there are positive finite weights whose weighted
sum is finite: the paper's `2^{-n-1}/μ_n(U_n)`. -/
theorem exists_weights_tsum_lt {ι : Type v} [Countable ι] (m : ι → ℝ≥0∞) (hm : ∀ i, m i ≠ ∞) :
    ∃ c : ι → ℝ≥0∞, (∀ i, c i ≠ 0) ∧ (∀ i, c i ≠ ∞) ∧ ∑' i, c i * m i < ∞ := by
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_tsum_mul_lt_of_countable one_ne_zero m hm
  refine ⟨fun i => δ i, fun i => (ENNReal.coe_pos.2 (hδ i)).ne', fun _ => ENNReal.coe_ne_top,
    ?_⟩
  simp_rw [mul_comm]
  exact hsum.trans ENNReal.one_lt_top

/-- The value of a countable weighted sum of measures on an arbitrary set. -/
theorem sum_smul_apply {ι : Type v} [Countable ι] (c : ι → ℝ≥0∞) (μ : ι → Measure α)
    (s : Set α) : Measure.sum (fun i => c i • μ i) s = ∑' i, c i * μ i s := by
  rw [Measure.sum_apply_of_countable]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- A set is null for a countable sum iff it is null for every term. -/
theorem sum_apply_eq_zero_iff {ι : Type v} [Countable ι] (μ : ι → Measure α) (s : Set α) :
    Measure.sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]

/-- A set charged by one term of a sum is charged by the sum. -/
theorem lt_sum_apply_of_lt {ι : Type v} (μ : ι → Measure α) (s : Set α) (i : ι) {r : ℝ≥0∞}
    (h : r < μ i s) : r < Measure.sum μ s :=
  h.trans_le (Measure.le_sum μ i s)

/-- A measure carried by `U` sees only the trace on `U`. -/
theorem measure_eq_inter_of_compl_null {μ : Measure α} {U : Set α} (h : μ Uᶜ = 0)
    (s : Set α) : μ s = μ (s ∩ U) :=
  (measure_inter_conull h).symm

/-! ### A measure on an open subset is a measure on the space carried by it -/

section Subtype

variable [TopologicalSpace α] [BorelSpace α] {U : Set α}

/-- The push-forward of a finite regular measure on a subset `U` is a regular measure on the
space, in an R₁ space. -/
theorem regular_map_subtype_val [R1Space α] (ν : Measure U) [IsFiniteMeasure ν]
    [ν.Regular] : (Measure.map Subtype.val ν).Regular := by
  have hm : Measurable (Subtype.val : U → α) := measurable_subtype_coe
  have hcomp : (Measure.map Subtype.val ν).InnerRegularWRT IsCompact IsOpen :=
    InnerRegularWRT.map Regular.innerRegular hm.aemeasurable
      (fun _ hV => hV.preimage continuous_subtype_val)
      (fun _ hK => hK.image continuous_subtype_val) (fun _ hV => hV.measurableSet)
  have hclosed : (Measure.map Subtype.val ν).InnerRegularWRT IsClosed IsOpen := by
    intro V hV r hr
    obtain ⟨K, hKV, hK, hrK⟩ := hcomp hV r hr
    exact ⟨closure K, hK.closure_subset_of_isOpen hV hKV, isClosed_closure,
      hrK.trans_le (measure_mono subset_closure)⟩
  haveI := InnerRegularWRT.weaklyRegular_of_finite (Measure.map Subtype.val ν) hclosed
  exact ⟨hcomp⟩

/-- The push-forward of a measure on `U` is carried by `U`. -/
theorem map_subtype_val_compl_null (hU : IsOpen U) (ν : Measure U) :
    Measure.map Subtype.val ν Uᶜ = 0 := by
  rw [Measure.map_apply measurable_subtype_coe hU.measurableSet.compl]
  have : (Subtype.val : U → α) ⁻¹' Uᶜ = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

/-- Conversely a regular measure on the space carried by an open subset `U` is the push-forward
of a regular measure on `U`. -/
theorem exists_regular_subtype_of_compl_null (hU : IsOpen U) {μ : Measure α} [μ.Regular]
    (h : μ Uᶜ = 0) : ∃ ν : Measure U, ν.Regular ∧ Measure.map Subtype.val ν = μ := by
  refine ⟨μ.comap Subtype.val, Regular.comap' μ hU.isOpenEmbedding_subtypeVal, ?_⟩
  rw [map_comap_subtype_coe hU.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h)

end Subtype

end Causal
