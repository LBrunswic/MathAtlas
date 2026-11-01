import CausalScaffold.Flat.SecondCountable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Urysohn

/-!
# `CausalScaffold.Flat.Geroch.ChartMeasure` — a finite regular measure on a flat spacetime, positive on open sets, null where every chart sees Lebesgue-null

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257);
infrastructure for `FlatAdmissibleMeasures` (`Flat/TheoremBInputs.lean`, ruling DEC-65). **No label
is marked.** Properties 1. and 2. of `defi:mesure_dieckmann` (ETT.tex:1032), positivity on
non-empty open sets (for property 3.) and the transfer of Lebesgue-nullity from the charts (for
property 4.), for one measure built from a countable atlas.

> 1. $\mu$ is a regular Borel measure on $M$; 2. $\mu(M)<+\infty$; (ETT.tex, `defi:mesure_dieckmann`)

* `exists_chart_measure`: on every flat spacetime `N` with its Borel σ-algebra there is `μ` with
  `μ.Regular`, `μ univ < ⊤`, `0 < μ O` for every non-empty open `O`, and `μ S = 0` for every
  closed `S` such that `volume (chartAt x '' (S ∩ (chartAt x).source)) = 0` for every `x : N`.

Route. `N` is second countable (`FlatSpacetime.secondCountableTopology`), so countably many open
sets `Wᵢ = eᵢ.source ∩ eᵢ ⁻¹' Vᵢ`, `eᵢ = chartAt yᵢ`, `Vᵢ ⊆ eᵢ.target` an open ball, cover `N`
(Lindelöf: `TopologicalSpace.isOpen_iUnion_countable`, indexed by a countable `T ⊆ N`). Take
`μ := Σᵢ cᵢ • Measure.map eᵢ.symm (volume.restrict Vᵢ)` with `cᵢ := 2^(-encode i) · (volume Vᵢ)⁻¹`
(`eᵢ.symm` is continuous on `Vᵢ`, so `AEMeasurable` for the restricted measure). Finite: `Σ 2⁻ⁱ`.
Positive: a non-empty open `O` meets some `Wᵢ` at `p`, and `eᵢ.target ∩ eᵢ.symm ⁻¹' O ∩ Vᵢ` is an
open subset of `Vᵢ` containing `eᵢ p` (`IsOpen.measure_pos` for `volume` on `Minkowski d`, an
add-Haar measure). Null: for `S` closed (so measurable, `map_apply_of_aemeasurable`),
`μᵢ S = cᵢ · volume (Vᵢ ∩ eᵢ.symm ⁻¹' S)` and
`Vᵢ ∩ eᵢ.symm ⁻¹' S ⊆ eᵢ '' (S ∩ eᵢ.source)`. Regular: `N` is locally compact
(`ChartedSpace.locallyCompactSpace`), T2 hence regular, second countable hence metrizable
(`metrizableSpace_of_t3_secondCountable`) and σ-compact; a finite measure is locally finite, so
`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` second countable Hausdorff | ✓ carried by `FlatSpacetime` (T2) and proved (second countable, `Flat/SecondCountable.lean`) |
| Borel σ-algebra | ✓ carried: `[MeasurableSpace N] [BorelSpace N]` |

## SCOPE (disclosed)

* The nullity clause is asked for **closed** `S` only: the integrator applies it to
  `frontier I^±(A)` and concludes for `J^±(A) ∖ K^±(A)` by `measure_mono_null`, so the outer
  measure of a non-measurable set is never needed.
* True for every `d` (at `d = 0`, `Minkowski 0 ≃ ℝ` and `volume` is Lebesgue measure on `ℝ`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-65.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology MeasureTheory

universe u

variable {d : ℕ}

/-- **A chart measure on a flat spacetime**: finite, regular, positive on non-empty open sets,
and null on every closed set whose image in every chart `chartAt x` is Lebesgue-null. -/
theorem exists_chart_measure (N : FlatSpacetime.{u} d) [MeasurableSpace N] [BorelSpace N] :
    ∃ μ : Measure N, μ.Regular ∧ μ univ < ⊤ ∧
      (∀ O : Set N, IsOpen O → O.Nonempty → 0 < μ O) ∧
      ∀ S : Set N, IsClosed S →
        (∀ x : N, volume ((chartAt (Minkowski d) x) '' (S ∩ (chartAt (Minkowski d) x).source))
          = 0) → μ S = 0 := by
  classical
  -- topology of `N`: locally compact, regular, metrizable, σ-compact
  haveI : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace (Minkowski d) N
  haveI : MetrizableSpace N := TopologicalSpace.metrizableSpace_of_t3_secondCountable N
  haveI : SigmaCompactSpace N := inferInstance
  -- (1) for each `y`, a ball `V y` around `chartAt y y` inside the chart target
  have hball : ∀ y : N, ∃ r : ℝ, 0 < r ∧
      Metric.ball (chartAt (Minkowski d) y y) r ⊆ (chartAt (Minkowski d) y).target := fun y =>
    Metric.isOpen_iff.1 (chartAt (Minkowski d) y).open_target _ (mem_chart_target _ y)
  choose r hr hrV using hball
  set e : N → OpenPartialHomeomorph N (Minkowski d) := fun y => chartAt (Minkowski d) y
    with he_def
  set V : N → Set (Minkowski d) := fun y => Metric.ball (e y y) (r y) with hV_def
  set W : N → Set N := fun y => (e y).source ∩ (e y) ⁻¹' V y with hW_def
  have hVopen : ∀ y, IsOpen (V y) := fun y => Metric.isOpen_ball
  have hVmeas : ∀ y, MeasurableSet (V y) := fun y => (hVopen y).measurableSet
  have hVt : ∀ y, V y ⊆ (e y).target := hrV
  have hVfin : ∀ y, volume (V y) ≠ ⊤ := fun y => measure_ball_lt_top.ne
  have hVpos : ∀ y, volume (V y) ≠ 0 := fun y => (Metric.measure_ball_pos volume _ (hr y)).ne'
  have hWopen : ∀ y, IsOpen (W y) := fun y =>
    (e y).continuousOn.isOpen_inter_preimage (e y).open_source (hVopen y)
  have hyW : ∀ y, y ∈ W y := fun y =>
    ⟨mem_chart_source _ y, Metric.mem_ball_self (hr y)⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
  haveI : Encodable T := hTc.toEncodable
  have hcover : ∀ p : N, ∃ t : T, p ∈ W t := by
    intro p
    have hp : p ∈ ⋃ i ∈ T, W i := by rw [hTU]; exact mem_iUnion.2 ⟨p, hyW p⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hp
    exact ⟨⟨i, hi⟩, hpi⟩
  have hae : ∀ y, AEMeasurable (e y).symm (volume.restrict (V y)) := fun y =>
    ((e y).continuousOn_symm.mono (hVt y)).aemeasurable (hVmeas y)
  -- (2) the measure
  let c : T → ENNReal := fun t => (2⁻¹ : ENNReal) ^ Encodable.encode t * (volume (V t))⁻¹
  let μ : Measure N := Measure.sum fun t : T => c t • (volume.restrict (V t)).map (e t).symm
  have hμ : ∀ s : Set N, MeasurableSet s →
      μ s = ∑' t : T, c t * volume ((e t).symm ⁻¹' s ∩ V t) := by
    intro s hs
    simp only [μ, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    congr 1; ext t
    rw [Measure.map_apply_of_aemeasurable (hae t) hs, Measure.restrict_apply' (hVmeas t)]
  have hfin : μ univ < ⊤ := by
    rw [hμ univ MeasurableSet.univ]
    have : ∀ t : T, c t * volume ((e t).symm ⁻¹' univ ∩ V t) =
        (2⁻¹ : ENNReal) ^ Encodable.encode t := by
      intro t
      simp only [preimage_univ, univ_inter, c]
      rw [mul_assoc, ENNReal.inv_mul_cancel (hVpos t) (hVfin t), mul_one]
    simp_rw [this]
    exact ENNReal.tsum_geometric_two_encode_le_two.trans_lt ENNReal.ofNat_lt_top
  haveI : IsFiniteMeasure μ := ⟨hfin⟩
  refine ⟨μ, inferInstance, hfin, ?_, ?_⟩
  · -- positivity on non-empty open sets
    intro O hO ⟨p, hpO⟩
    obtain ⟨t, hpt⟩ := hcover p
    rw [hμ O hO.measurableSet]
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum t)
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.mul_pos (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _).ne'
        (ENNReal.inv_ne_zero.2 (hVfin t))).ne'
    · have hU : IsOpen ((e t).target ∩ (e t).symm ⁻¹' O ∩ V t) :=
        ((e t).continuousOn_symm.isOpen_inter_preimage (e t).open_target hO).inter (hVopen t)
      have hpU : (e t) p ∈ (e t).target ∩ (e t).symm ⁻¹' O ∩ V t :=
        ⟨⟨(e t).map_source hpt.1, by simpa [(e t).left_inv hpt.1] using hpO⟩, hpt.2⟩
      have hpos : 0 < (volume : Measure (Minkowski d)) ((e t).target ∩ (e t).symm ⁻¹' O ∩ V t) :=
        IsOpen.measure_pos _ hU ⟨_, hpU⟩
      refine (lt_of_lt_of_le hpos (measure_mono ?_)).ne'
      intro z hz
      exact ⟨hz.1.2, hz.2⟩
  · -- nullity transferred from the charts
    intro S hS hnull
    rw [hμ S hS.measurableSet]
    refine ENNReal.tsum_eq_zero.2 fun t => ?_
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ (hnull t))
    intro z ⟨hzS, hzV⟩
    exact ⟨(e t).symm z, ⟨hzS, (e t).map_target (hVt t hzV)⟩, (e t).right_inv (hVt t hzV)⟩

end Causal.Flat
