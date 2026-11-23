import Causal.Model.EAlphaCauchy
import Causal.CausallyPlainLocZ
import Causal.ChainsCurves

/-!
# `E_α` is causally plain: every static spacetime `ℝ × X` is, hence `E_α` and the cosmic string

Programme target `T-loc-ealpha-plain` (`programme/roadmap.toml`; layer 3, localisation, model
`E_alpha`, provides `causally_plain`; DEC-168, DEC-188). No label is marked: `ETT.tex` states no
plainness of `E_α`, and `defi:causalement_plat` is the definition `Causality.CausallyPlain`
(`Causal.Properties`), the ladder's `causally_plain` (`programme/ladder.toml`), of which every
statement here is an instance.

> A topological spacetime $M$ is \emph{causally plain} if for every open subset $\U$ of $M$ and
> every $A\subset \U$, $\mathrm{Int}\left(J^\pm_\U(A)\right)\subset \overline{I^\pm_\U(A)}$
> (`defi:causalement_plat`, `ETT.tex:284–285`)

## What is here

* **`staticCausality.causallyPlain`**: the static causality of `ℝ × X`, `X` any geodesic metric
  space (complete, proper or neither), is causally plain, by the ladder edge
  `push_up ∧ chronal_neighbours ⇒ causally_plain`
  (`Causality.PushUp.causallyPlain_of_chronalNeighbours`, `Causal.CausallyPlainLocZ`) applied to
  `staticCausality.pushUp` (`Causal.Static`) and `staticCausality.chronalNeighbours`
  (`Causal.Model.StaticCauchy`). On every open subset too
  (`staticCausality.causallyPlainOn`, `Causality.CausallyPlainOn`).
* **`massive_causallyPlain`**: `E_α = ℝ × C_α`, `α > 0` (`massive α`, ETT's 2+1 form), and
  **`cosmicString_causallyPlain`**: Hörmann's 3+1 conical spacetime `E_α × ℝ_z`
  (`cosmicString α`, the formalization of record by DEC-188; Hörmann's `α_H` is `α / 2π`). With the
  axis, resp. the string, removed: `massive_causallyPlainOn_regOpens`,
  `cosmicString_causallyPlainOn_offAxis`.
* Other instances of the same lemma: `minkowski_causallyPlain` (`ℝ^{1,n}`, every `n`),
  `halfPlane_causallyPlain` (`ℝ × ]0, ∞[`, `Causal.ChainsCurves`), and
  `halfPlane_causallyPlain_not_causallyCompact`, its plainness beside the `¬ CausallyCompact`
  conjunct of `Causal.halfPlane_hypotheses`.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| target: `E_α`, `α > 0` | ✓ carried (`[Fact (0 < α)]`); `α > 2π` included |
| DEC-188: the 3+1 cosmic string of record, the 2+1 form a corollary | ✓ both, one line each |
| `X` complete or proper | not used: only `[MetricSpace X] [GeodesicSpace X]` |
| separation, countability | none asked |

## SCOPE (disclosed)

* The **model** spaces only. `E_α`-manifolds (every `E_{≥0}`-manifold under DEC-25's reading)
  are causally plain by `Causal.SFALocal.causallyPlain` (`Causal.Port.SFALocal`, absolutely
  minimal causalities with isomorphic charts), a different route (`causallyPlain_of_locZ` with
  `S = sing₀`); this module does not import it.
* No new mathematics: the lemma's two inputs were in Lean (`staticCausality.pushUp`,
  `staticCausality.chronalNeighbours`); this module only states the instances the binders and the
  ladder cite.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

/-! ### Every static spacetime `ℝ × X` -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

/-- **Every static spacetime `ℝ × X`, `X` a geodesic metric space, is causally plain**
(`defi:causalement_plat`): push-up and chronal neighbours (`push_up ∧ chronal_neighbours ⇒
causally_plain`). -/
theorem causallyPlain : (staticCausality X).CausallyPlain :=
  pushUp.causallyPlain_of_chronalNeighbours chronalNeighbours

/-- Plainness on every open subset `W` of a static spacetime (`ex:open_subset`'s reading). -/
theorem causallyPlainOn (W : Opens (ℝ × X)) : (staticCausality X).CausallyPlainOn W :=
  fun U _ A => causallyPlain U A

end staticCausality

/-! ### `E_α` and the cosmic string of record -/

variable {α : ℝ} [Fact (0 < α)]

/-- **`E_α = ℝ × C_α`, `α > 0`, is causally plain.** -/
theorem massive_causallyPlain : (massive α).CausallyPlain :=
  staticCausality.causallyPlain

/-- `E_α` with its axis removed, `reg(E_α)`, is causally plain. -/
theorem massive_causallyPlainOn_regOpens : (massive α).CausallyPlainOn (regOpens α) :=
  staticCausality.causallyPlainOn _

/-- **Hörmann's 3+1 conical spacetime `E_α × ℝ_z` (DEC-188's formalization of record) is causally
plain.** -/
theorem cosmicString_causallyPlain : (cosmicString α).CausallyPlain :=
  staticCausality.causallyPlain

/-- The conical spacetime with the string's world-sheet removed is causally plain. -/
theorem cosmicString_causallyPlainOn_offAxis :
    (cosmicString α).CausallyPlainOn (stringOffAxis α) :=
  staticCausality.causallyPlainOn _

/-! ### Other static instances -/

/-- Minkowski space `ℝ^{1,n}` is causally plain. -/
theorem minkowski_causallyPlain (n : ℕ) : (minkowski n).CausallyPlain :=
  staticCausality.causallyPlain

/-- The half-plane `ℝ × ]0, ∞[` is causally plain. -/
theorem halfPlane_causallyPlain : (staticCausality (Ioi (0 : ℝ))).CausallyPlain :=
  staticCausality.causallyPlain

/-- The half-plane is causally plain and not causally compact. -/
theorem halfPlane_causallyPlain_not_causallyCompact :
    (staticCausality (Ioi (0 : ℝ))).CausallyPlain ∧
      ¬ (staticCausality (Ioi (0 : ℝ))).CausallyCompact :=
  ⟨halfPlane_causallyPlain, halfPlane_hypotheses.2.2.2.2.2⟩

/-! ### Checks: ETT's theorems taking causal plainness apply at `E_α` as stated

`lem:passe_coherent` (`Causality.Jminus_Iminus_eq_of_mem_Zminus`) and `prop:tarentin_fort_K`
(`Causality.Kminus_eq_Iminus_of_mem_Zminus`), fed the instances above and `Z⁻ = M`
(`staticCausality.mem_Zminus`, `massive_Zminus`). Their conclusions were already known at static
spacetimes through push-up (`staticCausality.Kminus_eq_Iminus`); these lines only check that the
plainness instances have the ladder's form. -/

example (p : CosmicString α) :
    (cosmicString α).Jminus ⊤ ((cosmicString α).Iminus ⊤ {p}) = (cosmicString α).Iminus ⊤ {p} :=
  Causality.Jminus_Iminus_eq_of_mem_Zminus cosmicString_causallyPlain (staticCausality.mem_Zminus p)

example (p : CosmicString α) : (cosmicString α).Kminus ⊤ {p} = (cosmicString α).Iminus ⊤ {p} :=
  Causality.Kminus_eq_Iminus_of_mem_Zminus cosmicString_causallyPlain (staticCausality.mem_Zminus p)

example (p : Massive α) : (massive α).Kminus ⊤ {p} = (massive α).Iminus ⊤ {p} :=
  Causality.Kminus_eq_Iminus_of_mem_Zminus massive_causallyPlain
    (massive_Zminus (α := α) ▸ mem_univ p)

end Causal
