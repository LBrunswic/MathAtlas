import Causal.Model.StaticCauchy
import Causal.ChainsCurves
import Causal.CausallyPlainLocZ

/-!
# The half-plane `ℝ × ]0, ∞[`: its ladder properties beside ¬ causally compact, in one statement

The conjuncts are not every ladder property it has: `causally_open_future`, `locally_push_up`,
`locally_causally_open`, `locally_causally_open_future` and `has_chronal_neighbour` each follow
from a conjunct in one ladder step and are not stated.

Programme target `T-loc-ealpha-tidy` (`programme/roadmap.toml`; layer 3, its optional item, the
ladder keeper's request: "a single halfPlane witness"). Nothing is marked: no statement of
`ETT.tex` is proved here. The half-plane is `staticCausality (Ioi 0)`, the static spacetime over
the half-line `]0, ∞[` (`Causal.ChainsCurves`: an open subset of 1+1 Minkowski space with the
causality of its own curves), which is not causally compact (`Causal.halfPlane_hypotheses`, through
`halfPlane_not_causallyCompleteCurves`).

* `halfPlane_separates`: the half-plane is Hausdorff, second countable and connected; it is
  tarentin, causal, causally arc-connected, strongly causal (both forms), absolutely minimal,
  push-up, has chronal neighbours, is causally open, has a time function, curves extend in it,
  and it is causally plain; and it is **not** causally compact. One witness for every ladder
  entry `P ⇏ causally_compact` that the half-plane refutes (`programme/ladder.toml`, its
  `[[fails]]` entries witnessed by `Causal.halfPlane_hypotheses`, five of which name only the
  `¬ CausallyCompact` half), and for `curves_extend ⇏ causally_compact` and
  `causally_plain ⇏ causally_compact` directly.

> A topological spacetime $M$ is \emph{causally plain} if for every open subset $\U$ of $M$ and
> every $A\subset \U$, $\mathrm{Int}\left(J^\pm_\U(A)\right)\subset \overline{I^\pm_\U(A)}$
> (`defi:causalement_plat`, `ETT.tex:284–285`)

## Hypothesis checklist

| conjunct | from |
|---|---|
| `T2Space`, `SecondCountableTopology`, `ConnectedSpace` of `ℝ × Ioi 0` | mathlib: instances, and `ConnectedSpace (Ioi 0)` from `isConnected_Ioi` |
| `Tarentin`, `IsCausal`, `CausallyArcConnected`, `StronglyCausal`, `AbsolutelyMinimal`, `¬ CausallyCompact` | `Causal.halfPlane_hypotheses` (`Causal.ChainsCurves`) |
| `PushUp` | `staticCausality.pushUp` (`Causal.Static`) |
| `ChronalNeighbours`, `CausallyOpen`, `StronglyCausalOpen`, `HasTimeFunction` | `staticCausality.*` (`Causal.Model.StaticCauchy`) |
| `CurvesExtend` | `staticCausality.curvesExtend` (`Causal.Model.CurvesExtendModels`) |
| `CausallyPlain` | the ladder edge `push_up ∧ chronal_neighbours ⇒ causally_plain` (`Causality.PushUp.causallyPlain_of_chronalNeighbours`, `Causal.CausallyPlainLocZ`), as `staticCausality.causallyPlain` (`Causal.Model.EAlphaPlain`) is proved |

## SCOPE (disclosed)

* No new mathematics: every conjunct was in Lean. The module gathers them so that a ladder entry
  names one statement holding both halves.
* **Imports.** `Causal.Model.StaticCauchy`, `Causal.ChainsCurves` and `Causal.CausallyPlainLocZ`;
  not `Causal.Model.EAlphaPlain` (which has `halfPlane_causallyPlain`), so that the half-plane's
  witness does not import `Causal.Model.Massive`. The plainness conjunct applies the same ladder
  edge to the same two inputs as `halfPlane_causallyPlain`. A model module.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set

/-- **The half-plane `ℝ × ]0, ∞[` has each ladder property below and is not causally compact**:
Hausdorff, second countable, connected; tarentin, causal, causally arc-connected, strongly causal,
absolutely minimal, push-up, chronal neighbours, causally open, strongly causal on opens, a time
function, curves extend, causally plain; and not causally compact. -/
theorem halfPlane_separates :
    (T2Space (ℝ × Ioi (0 : ℝ)) ∧ SecondCountableTopology (ℝ × Ioi (0 : ℝ)) ∧
      ConnectedSpace (ℝ × Ioi (0 : ℝ))) ∧
    (staticCausality (Ioi (0 : ℝ))).Tarentin ∧ (staticCausality (Ioi (0 : ℝ))).IsCausal ∧
    (staticCausality (Ioi (0 : ℝ))).CausallyArcConnected ∧
    (staticCausality (Ioi (0 : ℝ))).StronglyCausal ∧
    (staticCausality (Ioi (0 : ℝ))).AbsolutelyMinimal ∧
    (staticCausality (Ioi (0 : ℝ))).PushUp ∧ (staticCausality (Ioi (0 : ℝ))).ChronalNeighbours ∧
    (staticCausality (Ioi (0 : ℝ))).CausallyOpen ∧
    (staticCausality (Ioi (0 : ℝ))).StronglyCausalOpen ∧
    (staticCausality (Ioi (0 : ℝ))).HasTimeFunction ∧
    (staticCausality (Ioi (0 : ℝ))).CurvesExtend ∧
    (staticCausality (Ioi (0 : ℝ))).CausallyPlain ∧
    ¬ (staticCausality (Ioi (0 : ℝ))).CausallyCompact := by
  obtain ⟨hT, hC, hA, hS, hM, hK⟩ := halfPlane_hypotheses
  have : ConnectedSpace (Ioi (0 : ℝ)) := isConnected_iff_connectedSpace.1 isConnected_Ioi
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, hT, hC, hA, hS, hM,
    staticCausality.pushUp, staticCausality.chronalNeighbours, staticCausality.causallyOpen,
    staticCausality.stronglyCausalOpen, staticCausality.hasTimeFunction,
    staticCausality.curvesExtend,
    staticCausality.pushUp.causallyPlain_of_chronalNeighbours staticCausality.chronalNeighbours, hK⟩

end Causal
