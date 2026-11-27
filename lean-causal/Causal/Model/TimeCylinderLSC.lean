import Causal.Model.FlatTimeCylinder
import Causal.StronglyCausalTransport

/-!
# Every flat spacetime is locally strongly causal; the flat time cylinder separates local from global strong causality

Programme target `T-loc-time-cylinder-lsc` (`programme/roadmap.toml`; layer 3, localisation, model
`flat-gx`; no paper label: a ladder witness). The model-free transport is
`Causal.StronglyCausalTransport`; this module applies it to the flat spacetimes.

**`T-loc-time-cylinder-lsc/2-instance`** — `flatCausality_stronglyCausalOn_chartSource` (the source
of every chart of the maximal atlas onto `𝐌ⁿ` is strongly causal as a spacetime),
`flatCausality_stronglyCausalOn_of_le`, `flatCausality_locallyStronglyCausal` (every flat spacetime
is locally strongly causal); beyond the target, `locallyStronglyCausal_of_chartIso_chartAt` (any
causality whose chart at each point is an isomorphism onto `𝐌ⁿ`, with no atlas compatibility and no
absolute minimality).
**`T-loc-time-cylinder-lsc/3-separation`** — `timeCylinder_locallyStronglyCausal`;
`timeCylinder_separates_locallyStronglyCausal` (`1 ≤ d`: the conjuncts of `timeCylinder_separates`,
then `LocallyStronglyCausal`, `¬ StronglyCausal`, `¬ StronglyCausalOpen`) and
`timeCylinder_zero_separates_locallyStronglyCausal` (`d = 0`, the timelike circle: the conjuncts of
`timeCylinder_zero_separates`, then the same three).

> Every flat spacetime is locally strongly causal, so the flat time cylinder separates local from
> global strong causality. […] its instance Causal.Flat.flatCausality_locallyStronglyCausal (every
> chart of the maximal atlas onto 𝐌ⁿ, strongly causal); and
> Causal.Flat.timeCylinder_separates_locallyStronglyCausal, the conjuncts of timeCylinder_separates
> (d ≥ 1) and timeCylinder_zero_separates (the timelike circle) with LocallyStronglyCausal,
> ¬ StronglyCausal and ¬ StronglyCausalOpen (`programme/roadmap.toml`, `T-loc-time-cylinder-lsc`,
> title)

> A: locally strongly causal: a point has an open neighbourhood that the covering map carries
> isomorphically onto a small Minkowski ball (an interval of the timelike line when d = 0), on
> which the flat causality is Minkowski's, strongly causal (Causal.minkowski_stronglyCausal,
> Causal.timelikeLine_stronglyCausal). Either reading; the 3 pairs. (`programme/ladder.toml`, the
> comment of the `locally_strongly_causal` [[open]] section)

## Hypothesis checklist

| target claim | here |
|---|---|
| every chart of the maximal atlas onto `𝐌ⁿ` strongly causal | ✓ its source is strongly causal as a spacetime (`StronglyCausalOn (chartSource e)`), and so is every open set inside it |
| every flat spacetime locally strongly causal | ✓ any `(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold, every `d` (`d = 0` included); no separation axiom, no second countability, no connectedness; ⚠ weakened beyond: any causality on a `ChartedSpace (Minkowski d) M` whose chart at each point is a `ChartIso` onto `minkowski d` (`locallyStronglyCausal_of_chartIso_chartAt`; no `HasGroupoid`, no minimality) |
| the cylinder: the conjuncts of `timeCylinder_separates` (`1 ≤ d`) and `timeCylinder_zero_separates` | ✓ carried verbatim, in their order (destructured, kb/0276) |
| `LocallyStronglyCausal`, `¬ StronglyCausal`, `¬ StronglyCausalOpen` | ✓ appended, the ladder's own definitions at `timeCylinder d` |

## SCOPE (disclosed)

* **The argument is not the ladder note's.** The note goes through the covering map and a small
  Minkowski ball; the proof here needs no ball and no covering: the chart at a point is a chart
  isomorphism onto `minkowski d` (`flatCausality_chartIso_chartAt`), `minkowski d` is strongly
  causal (`minkowski_stronglyCausal`, every `d`, so the timelike line's case `d = 0` needs no
  separate argument), and a chart isomorphism carries strong causality as a spacetime
  (`ChartIso.stronglyCausalOn_iff`). The chart's whole source is strongly causal as a spacetime.
* **Either reading of `defi:causalite` (OQ-18).** `timeCylinder d` is absolutely minimal, so both
  separations hold in the gluing reading as in the library's.
* **The time cylinder's other facts** (curves extending, absolute minimality, …, `¬ IsCausal`,
  `¬ CausallyCompact`) are `Causal.Model.FlatTimeCylinder`'s, cited, not re-proved.
* **The chart's source, not a small ball.** Every chart of the maximal atlas has a source strongly
  causal as a spacetime, however large. Argued, not stated here: for the cylinder, the inverse of
  the projection on the slab `{0 < t < 1}` of `𝐌ⁿ` is a chart of the maximal atlas (its transitions
  are time translations), so the cylinder minus one slice, a dense open set, is strongly causal as
  a spacetime, while the cylinder is not.
* **Destructuring.** The two separations destructure the old ones with `obtain` (kb/0276); a
  term-mode `let ⟨…⟩` compiles to a `match` whose kernel check took 6 s at `d = 0`.
* **Imports.** `Causal.Model.FlatTimeCylinder` (a model module) and
  `Causal.StronglyCausalTransport` (ETT layer); `Causal.Flat.IsomCausal` and
  `Causal.Minkowski` come through the first. Nothing imports this module.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

namespace Flat

variable {d : ℕ}

/-! ### 2. The instance: every flat spacetime is locally strongly causal -/

/-- **Any causality for which the chart at each point is an isomorphism onto `𝐌ⁿ` is locally
strongly causal**: no compatibility of the charts, no absolute minimality (so any causality with
the chart condition, not only the flat one; argued, not stated here: the 𝐌ⁿ analogues of
`GX_maximal_not_unique`'s non-minimal causalities, whose own case on `ℝ ⊕ ℝ` is
`Causality.locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal` with
`timelikeLine_stronglyCausal`). -/
theorem locallyStronglyCausal_of_chartIso_chartAt {M : Type u} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {C : Causality M}
    (hC : ∀ x : M, ChartIso C (minkowski d) (chartAt (Minkowski d) x)) : C.LocallyStronglyCausal :=
  Causality.locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal minkowski_stronglyCausal
    fun x => ⟨chartAt (Minkowski d) x, mem_chart_source (Minkowski d) x, hC x⟩

section FlatSpacetime

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **The source of every chart of the maximal atlas onto `𝐌ⁿ` is strongly causal as a
spacetime**: the chart is an isomorphism onto `minkowski d`, which is strongly causal. -/
theorem flatCausality_stronglyCausalOn_chartSource {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M) :
    (flatCausality d M).StronglyCausalOn (chartSource e) :=
  (flatCausality_chartIso he).stronglyCausalOn_chartSource minkowski_stronglyCausal

/-- Every open set inside the source of a chart of the maximal atlas is strongly causal as a
spacetime. -/
theorem flatCausality_stronglyCausalOn_of_le {e : OpenPartialHomeomorph M (Minkowski d)}
    (he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M) {W : Opens M}
    (hW : W ≤ chartSource e) : (flatCausality d M).StronglyCausalOn W :=
  (flatCausality_stronglyCausalOn_chartSource he).mono hW

/-- **Every flat spacetime is locally strongly causal** (`locally_strongly_causal` at
`flatCausality d M`, every `d`): the source of the chart at a point is strongly causal as a
spacetime. -/
theorem flatCausality_locallyStronglyCausal : (flatCausality d M).LocallyStronglyCausal :=
  locallyStronglyCausal_of_chartIso_chartAt flatCausality_chartIso_chartAt

end FlatSpacetime

/-! ### 3. The separation -/

/-- **`locally_strongly_causal`** at the flat time cylinder, every `d`. -/
theorem timeCylinder_locallyStronglyCausal : (timeCylinder d).LocallyStronglyCausal :=
  flatCausality_locallyStronglyCausal

/-- **The flat time cylinder separates local from global strong causality** (`1 ≤ d`): the
conjuncts of `timeCylinder_separates` (an ETT spacetime, Hausdorff, second countable, connected,
with every causal curve extending, absolutely minimal, causally arc-connected, push-up, tarentin,
with chronal neighbours, causally open and causally plain, neither causal nor causally compact),
then locally strongly causal and strongly causal in neither form. Absolutely minimal, so it holds
in either reading of `defi:causalite`. -/
theorem timeCylinder_separates_locallyStronglyCausal (hd : 1 ≤ d) :
    (T2Space (TimeCylinder d) ∧ SecondCountableTopology (TimeCylinder d) ∧
      ConnectedSpace (TimeCylinder d)) ∧
    (timeCylinder d).CurvesExtend ∧ (timeCylinder d).AbsolutelyMinimal ∧
    (timeCylinder d).CausallyArcConnected ∧ (timeCylinder d).PushUp ∧
    (timeCylinder d).Tarentin ∧ (timeCylinder d).ChronalNeighbours ∧
    (timeCylinder d).CausallyOpen ∧ (timeCylinder d).CausallyPlain ∧
    ¬ (timeCylinder d).IsCausal ∧ ¬ (timeCylinder d).CausallyCompact ∧
    (timeCylinder d).LocallyStronglyCausal ∧ ¬ (timeCylinder d).StronglyCausal ∧
    ¬ (timeCylinder d).StronglyCausalOpen := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := timeCylinder_separates hd
  exact ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, timeCylinder_locallyStronglyCausal,
    timeCylinder_not_stronglyCausal, timeCylinder_not_stronglyCausalOpen⟩

/-- **The timelike circle separates local from global strong causality** (`d = 0`): the conjuncts
of `timeCylinder_zero_separates` (compact, causally compact, not causal), then locally strongly
causal and strongly causal in neither form. -/
theorem timeCylinder_zero_separates_locallyStronglyCausal :
    (T2Space (TimeCylinder 0) ∧ SecondCountableTopology (TimeCylinder 0) ∧
      ConnectedSpace (TimeCylinder 0) ∧ CompactSpace (TimeCylinder 0)) ∧
    (timeCylinder 0).CurvesExtend ∧ (timeCylinder 0).AbsolutelyMinimal ∧
    (timeCylinder 0).CausallyArcConnected ∧ (timeCylinder 0).PushUp ∧
    (timeCylinder 0).Tarentin ∧ (timeCylinder 0).ChronalNeighbours ∧
    (timeCylinder 0).CausallyOpen ∧ (timeCylinder 0).CausallyPlain ∧
    (timeCylinder 0).CausallyCompact ∧ ¬ (timeCylinder 0).IsCausal ∧
    (timeCylinder 0).LocallyStronglyCausal ∧ ¬ (timeCylinder 0).StronglyCausal ∧
    ¬ (timeCylinder 0).StronglyCausalOpen := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := timeCylinder_zero_separates
  exact ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, timeCylinder_locallyStronglyCausal,
    timeCylinder_not_stronglyCausal, timeCylinder_not_stronglyCausalOpen⟩

end Flat

end Causal
