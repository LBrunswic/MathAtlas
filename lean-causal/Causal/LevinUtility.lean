import Causal.LemmaKSC
import Causal.LevinTimeFunction

/-!
# Lemma K's characterisations in second countable spacetimes, without `CurvesExtend` (Levin's theorem)

No label is marked. This module discharges the named model fact `Causality.CurvesExtend`
(`Causal/CauchyExtension.lean:82`) in `Causal.LemmaKSC`'s two characterisations of Lemma K, in
every **second countable** tarentin globally hyperbolic Hausdorff spacetime, with no measure:
the curves extend by Levin's theorem for closed preorders
(`Causality.curvesExtend_of_secondCountable`). Second countability is part of ETT's own definition
of a spacetime, so nothing is added to the paper:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:255`)

Levin's theorem itself (the order-Urysohn machinery, namespace `Causal.Levin`), local and
σ-compactness from global hyperbolicity and tarentin, the time function
`Causality.exists_timeFunction_of_secondCountable` and its corollaries
`Causality.curvesExtend_of_secondCountable` and `Causality.exists_inextensible_of_secondCountable`
were proved here until T-abs-hoist-levin, which moved them, under the same full names, into the
ETT-layer module `Causal.LevinTimeFunction`; this module imports it. It closes the gap
`Causal.LemmaKSC` (SCOPE, route (a)) left open, for globally hyperbolic spacetimes.

## What is proved

* **Lemma K's characterisations without the named hypothesis**: `Causal.LemmaKSC`'s
  `isCauchySurface_iff_local` and `isCauchySurface_iff_isOpen_strictJplus` with `hext` discharged
  under second countability (`…_of_secondCountable`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff (`ETT.tex:255`) | ✓ carried: `[SecondCountableTopology M] [T2Space M]` |
| `C.Tarentin`, `C.GloballyHyperbolic` | ✓ carried: through `curvesExtend_of_secondCountable` (`Causal.LevinTimeFunction`) they give `CurvesExtend` |
| connectedness, causal arc-connectedness, `J^±(p) ≠ {p}` | ✓ carried, where `Causal.LemmaKSC` needs them |
| admissible measures (`geroch_i_imp_ii`) | ⚠ weakened: not used — the time function is Levin's, not Geroch's |

## SCOPE (disclosed)

* **Lemma K is not settled by this module.** Where curves extend, the bare (second countable)
  Lemma K is still equivalent to the two local conditions (1′)+(2′) of
  `Causality.isCauchySurface_iff_local`; this module only removes `CurvesExtend` from the
  equivalence (`isCauchySurface_iff_local_of_secondCountable`). The tagged `sorry` of
  `CausalScaffold.LemmaKSCOpen` stays.
* The time function used is not a Cauchy time function: Barbot's form
  `exists_inextensible_univ_of_isCauchyTimeFunction` (`J = ℝ`) is not reached from it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

/-! The order-Urysohn machinery (`Levin.*`), Levin's time function
`Causality.exists_timeFunction_of_secondCountable`, `Causality.curvesExtend_of_secondCountable`
and `Causality.exists_inextensible_of_secondCountable` are in `Causal.LevinTimeFunction`
(T-abs-hoist-levin). -/

/-! ### Lemma K's characterisations without `CurvesExtend` -/

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **Lemma K's local characterisation, second countable, without `CurvesExtend`**
(`isCauchySurface_iff_local` with `hext` discharged). -/
theorem isCauchySurface_iff_local_of_secondCountable [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔
      (∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) ∧
      (∀ q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S, q ∉ S → C.Jplus ⊤ S ∪ C.Jminus ⊤ S ∈ 𝓝 q) :=
  isCauchySurface_iff_local hT hG hC hJm hJp (curvesExtend_of_secondCountable hT hG) hSc hSconn
    hloc

/-- **Lemma K, second countable, without `CurvesExtend`**: a compact connected locally Cauchy set
is a Cauchy surface iff its strict causal future and past are open
(`isCauchySurface_iff_isOpen_strictJplus` with `hext` discharged). -/
theorem isCauchySurface_iff_isOpen_strictJplus_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔ IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) :=
  isCauchySurface_iff_isOpen_strictJplus hT hG hC hJm hJp
    (curvesExtend_of_secondCountable hT hG) hSc hSconn hloc

end Causality

end Causal
