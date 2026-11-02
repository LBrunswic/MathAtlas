import Causal.Flat.FlatSpacetime
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# `Causal.Flat.Geroch.ChartNull` — in every chart of a flat spacetime, the frontier of `I^±(A)` is Lebesgue-null

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257);
infrastructure for `FlatAdmissibleMeasures` (`Flat/TheoremBInputs.lean`, ruling DEC-65). **No label
is marked.** Property 4. of `defi:mesure_dieckmann` (ETT.tex:1032) on a flat spacetime `N` reduces
(`Causal.Flat.Geroch.Reach`) to the nullity of `frontier I^±(A)`; this file proves that
nullity **chart by chart**, from the Minkowski fact of `Causal.Flat.Geroch.ConeNull`, which
is carried here as a hypothesis `hcone` (stated verbatim as `ConeNull`'s theorem, so the
integrator passes `volume_frontier_inter_null_of_pastCone` / `…_futureCone`; this keeps the two
files independent).

> 4. for every $A \subset M$, $\mu(J^-(A)\setminus K^-(A))=0$ (resp. $\mu(J^+(A)\setminus K^+(A))=0$).
> (ETT.tex, `defi:mesure_dieckmann`)

* `volume_chart_frontier_Iminus_null`: for every `A ⊆ N` and `x : N`, with `e = chartAt x`,
  `volume (e '' (frontier I^-(A) ∩ e.source)) = 0`.
* `volume_chart_frontier_Iplus_null`: the future version.
* Helpers: `image_frontier_inter_source_subset_frontier` (model-free: a chart maps
  `frontier I ∩ source` into `frontier (e '' (I ∩ source)) ∩ target` for `I` open),
  `volume_frontier_inter_null_of_balls` (null in every ball `⊆ T` ⇒ null in `T`),
  `flatCausality_lt_top_symm_of_convex` (`≪` of `𝐌ⁿ` on a convex open `B ⊆ target` pulls back
  to `≪_⊤` of `flatCausality`).

Route. `e.target` is a countable union of open balls `Bₖ ⊆ e.target` (second countability of
`𝐌ⁿ`). Put `P := e '' (I^-(A) ∩ e.source)`. (i) `P` is past-closed inside each `Bₖ`: for
`y ∈ P ∩ Bₖ`, `z ∈ Bₖ` with `z ≪ y` in `𝐌ⁿ`, `Bₖ` convex gives `(minkowski d).lt Bₖ z y`
(`lt_iff_of_convex`, `Flat/Form.lean`); with `U := e.source ∩ e ⁻¹' Bₖ`, `chartImage e U = Bₖ`, and
`ChartIso` (`flatCausality_chartIso_chartAt`) gives `e.symm z ≪_U e.symm y`, hence `≪_⊤`
(`lt_mono le_top`), and `e.symm y ≪ a ∈ A`, so `e.symm z ∈ I^-(A)` (`lt_trans`). (ii)
`e '' (frontier I^-(A) ∩ e.source) ∩ Bₖ ⊆ frontier P ∩ Bₖ`, `e` being a homeomorphism of the open
source onto the open target. (iii) `hcone Bₖ P` and countable subadditivity.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| "the Alexandrov topology is the manifold topology" | ✓ used as: `flatCausality` agrees with `minkowski d` in every chart (`ChartIso`) |
| nullity of achronal boundaries in `𝐌ⁿ` | ✓ carried as `hcone` (proved in `Geroch.ConeNull`) |

## SCOPE (disclosed)

* Only charts `chartAt x` are treated (the integrator's measure is built from them).
* `A` arbitrary (`∅`, `univ`, unbounded): `P` may be empty or the whole target; the statement holds
  in each case.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-65.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology MeasureTheory

universe u

variable {d : ℕ}

/-- **A chart maps the frontier of an open set into the frontier of its image** (topological,
model-free): for `I` open and `e` an open partial homeomorphism,
`e '' (frontier I ∩ e.source) ⊆ frontier (e '' (I ∩ e.source)) ∩ e.target`. -/
theorem image_frontier_inter_source_subset_frontier {N X : Type*} [TopologicalSpace N]
    [TopologicalSpace X] (e : OpenPartialHomeomorph N X) {I : Set N} (hI : IsOpen I) :
    e '' (frontier I ∩ e.source) ⊆ frontier (e '' (I ∩ e.source)) ∩ e.target := by
  rintro _ ⟨w, ⟨hwf, hws⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, e.map_source hws⟩
  · have hcl : w ∈ closure (I ∩ e.source) := by
      rw [inter_comm]; exact e.open_source.inter_closure ⟨hws, hwf.1⟩
    exact ((e.continuousAt hws).continuousWithinAt).mem_closure_image hcl
  · intro hint
    obtain ⟨u, ⟨huI, hus⟩, hu⟩ := interior_subset hint
    have : u = w := e.injOn hus hws hu
    subst this
    exact hwf.2 (hI.interior_eq.symm ▸ huI)

/-- **Nullity of a frontier inside an open set from nullity inside its balls**: if
`frontier P ∩ ball c r` is null for every ball contained in the open set `T`, then
`frontier P ∩ T` is null (second countability of `𝐌ⁿ`). -/
theorem volume_frontier_inter_null_of_balls {P T : Set (Minkowski d)} (hT : IsOpen T)
    (h : ∀ (c : Minkowski d) (r : ℝ), Metric.ball c r ⊆ T →
      volume (frontier P ∩ Metric.ball c r) = 0) :
    volume (frontier P ∩ T) = 0 := by
  let ι := {p : Minkowski d × ℝ // Metric.ball p.1 p.2 ⊆ T}
  let s : ι → Set (Minkowski d) := fun i => Metric.ball i.1.1 i.1.2
  have hU : (⋃ i, s i) = T := by
    refine Subset.antisymm (iUnion_subset fun i => i.2) fun q hq => ?_
    obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT q hq
    exact mem_iUnion.2 ⟨⟨(q, ε), hεT⟩, Metric.mem_ball_self hε⟩
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable s fun _ => Metric.isOpen_ball
  rw [← hU, ← hSU, inter_iUnion₂]
  exact (measure_biUnion_null_iff hS).2 fun i _ => h _ _ i.2

/-- **On a convex open ball-like set inside a chart target, `≪` of `𝐌ⁿ` pulls back to `≪` of
`flatCausality`**: for `B ⊆ e.target` open and convex (`e = chartAt x`) and `z, y ∈ B` with
`z ≪ y` in `𝐌ⁿ`, `e.symm z ≪ e.symm y` in `N` (via `ChartIso` on `U := e.source ∩ e ⁻¹' B`,
`lt_iff_of_convex`, `lt_mono le_top`). -/
theorem flatCausality_lt_top_symm_of_convex (N : FlatSpacetime.{u} d) (x : N)
    {B : Set (Minkowski d)} (hBo : IsOpen B) (hBc : Convex ℝ B)
    (hBt : B ⊆ (chartAt (Minkowski d) x).target) {z y : Minkowski d} (hz : z ∈ B) (hy : y ∈ B)
    (h : (minkowski d).lt ⊤ z y) :
    (flatCausality d N).lt ⊤ ((chartAt (Minkowski d) x).symm z)
      ((chartAt (Minkowski d) x).symm y) := by
  set e := chartAt (Minkowski d) x
  let Bo : Opens (Minkowski d) := ⟨B, hBo⟩
  have hlt : (minkowski d).lt Bo z y := (lt_iff_of_convex (V := Bo) hBc).2 ⟨hz, hy, h⟩
  let U : Opens N := ⟨e.source ∩ e ⁻¹' B, e.continuousOn.isOpen_inter_preimage e.open_source hBo⟩
  have hUs : U ≤ chartSource e := fun _ hw => hw.1
  have hUB : chartImage e U = Bo := by
    refine SetLike.ext' ?_
    rw [coe_chartImage]
    ext p
    constructor
    · rintro ⟨w, ⟨_, _, hw⟩, rfl⟩; exact hw
    · intro hp
      have hpt := hBt hp
      refine ⟨e.symm p, ⟨e.map_target hpt, e.map_target hpt, ?_⟩, e.right_inv hpt⟩
      show e (e.symm p) ∈ B
      rw [e.right_inv hpt]; exact hp
  have hmem : ∀ q ∈ B, e.symm q ∈ U := fun q hq => by
    refine ⟨e.map_target (hBt hq), ?_⟩
    show e (e.symm q) ∈ B
    rw [e.right_inv (hBt hq)]; exact hq
  have key := ((flatCausality_chartIso_chartAt x) U hUs _ (hmem z hz) _ (hmem y hy)).2
  rw [hUB, e.right_inv (hBt hz), e.right_inv (hBt hy)] at key
  exact (flatCausality d N).lt_mono le_top (key.2 hlt)

/-- **In every chart, the frontier of `I^-(A)` is Lebesgue-null**, given the Minkowski fact
`hcone` (`Geroch.ConeNull.volume_frontier_inter_null_of_pastCone`). -/
theorem volume_chart_frontier_Iminus_null
    (hcone : ∀ {B P : Set (Minkowski d)}, IsOpen B →
      (∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖y.2 - z.2‖ < y.1 - z.1 → z ∈ P) →
      volume (frontier P ∩ B) = 0)
    (N : FlatSpacetime.{u} d) (A : Set N) (x : N) :
    volume ((chartAt (Minkowski d) x) ''
      (frontier ((flatCausality d N).Iminus ⊤ A) ∩ (chartAt (Minkowski d) x).source)) = 0 := by
  set e := chartAt (Minkowski d) x
  refine measure_mono_null
    (image_frontier_inter_source_subset_frontier e (flatCausality d N).isOpen_Iminus) ?_
  refine volume_frontier_inter_null_of_balls e.open_target fun c r hB => hcone Metric.isOpen_ball ?_
  rintro _ ⟨w, ⟨hwI, hws⟩, rfl⟩ hy z hz hzy
  have hlt := flatCausality_lt_top_symm_of_convex N x Metric.isOpen_ball (convex_ball c r) hB hz hy
    (minkowski_lt_top_iff.2 hzy)
  rw [e.left_inv hws] at hlt
  obtain ⟨a, ha, hwa⟩ := hwI
  exact ⟨e.symm z, ⟨⟨a, ha, (flatCausality d N).lt_trans hlt hwa⟩, e.map_target (hB hz)⟩,
    e.right_inv (hB hz)⟩

/-- **In every chart, the frontier of `I^+(A)` is Lebesgue-null**, given the Minkowski fact
`hcone` (`Geroch.ConeNull.volume_frontier_inter_null_of_futureCone`). -/
theorem volume_chart_frontier_Iplus_null
    (hcone : ∀ {B P : Set (Minkowski d)}, IsOpen B →
      (∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖z.2 - y.2‖ < z.1 - y.1 → z ∈ P) →
      volume (frontier P ∩ B) = 0)
    (N : FlatSpacetime.{u} d) (A : Set N) (x : N) :
    volume ((chartAt (Minkowski d) x) ''
      (frontier ((flatCausality d N).Iplus ⊤ A) ∩ (chartAt (Minkowski d) x).source)) = 0 := by
  set e := chartAt (Minkowski d) x
  refine measure_mono_null
    (image_frontier_inter_source_subset_frontier e (flatCausality d N).isOpen_Iplus) ?_
  refine volume_frontier_inter_null_of_balls e.open_target fun c r hB => hcone Metric.isOpen_ball ?_
  rintro _ ⟨w, ⟨hwI, hws⟩, rfl⟩ hy z hz hyz
  have hlt := flatCausality_lt_top_symm_of_convex N x Metric.isOpen_ball (convex_ball c r) hB hy hz
    (minkowski_lt_top_iff.2 hyz)
  rw [e.left_inv hws] at hlt
  obtain ⟨a, ha, haw⟩ := hwI
  exact ⟨e.symm z, ⟨⟨a, ha, (flatCausality d N).lt_trans haw hlt⟩, e.map_target (hB hz)⟩,
    e.right_inv (hB hz)⟩

end Causal.Flat
