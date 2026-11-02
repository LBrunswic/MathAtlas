import Causal.LemmaKLocal
import Causal.LevinUtility
import Causal.Minkowski

/-!
# Lemma K with second countability: the two rounds-3 tracks combined

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts and never proves
(Rem 2.3 `clomax`, `GHFspace.tex:572`); it carries no paper label. Its second countable form,
`isCauchySurface_of_isLocallyCauchy_of_secondCountable` (`CausalScaffold.LemmaKSCOpen`), is a
tagged `sorry`; DEC-92 asks it to be settled. This module joins the two round-3 tracks:

* track A (`Causal.LevinUtility`): in a second countable tarentin globally hyperbolic Hausdorff
  spacetime, Levin's theorem gives a continuous time function, hence `C.CurvesExtend`
  (`curvesExtend_of_secondCountable`);
* track B (`Causal.LemmaKLocal`): where curves extend, a closed locally Cauchy `Σ` is two-sided,
  and `Σ` is a Cauchy surface iff `J^+(O^+)` and `J^-(O^-)` are open, `O^±` the open chart
  sides (`chartFutureSide`).

## What is proved

With `hext` discharged by track A, in the exact setting of the scaffold target (ETT's spacetimes:
second countable, Hausdorff; tarentin, globally hyperbolic, causally arc-connected,
`J^±(p) ≠ {p}`; `Σ` compact, connected, locally Cauchy):

* `isLocallyCauchyTwoSided_of_secondCountable`: `Σ` is two-sided (closed `Σ` suffices);
* `isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable`: **the second countable
  Lemma K is equivalent to the openness of `J^+(O^+)` and `J^-(O^-)`** — two specific open sets;
* `isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable`: Lemma K holds under
  causal openness (`J^±(V)` open for `V` open);
* `local_conditions_of_isOpen_Jplus_of_secondCountable`: (1′) and (2′) under causal openness.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `T2Space`, second countable (`ETT.tex:255`) | ✓ carried |
| `Tarentin`, `GloballyHyperbolic`, `CausallyArcConnected`, `J^±(p) ≠ {p}` | ✓ carried |
| `Σ` compact, connected, `IsLocallyCauchy` | ✓ carried |
| `C.CurvesExtend` | ✓ not assumed: proved (track A) |
| — | the characterisation is an equivalence: the openness of `J^±(O^±)` is not implied by the hypotheses here — that implication IS the open question |

## SCOPE (disclosed)

* **Verdict on DEC-92 with second countability: not settled.** No proof, no counterexample. The
  residue is exactly the causal openness of `J^+` at `O^+` and of `J^-` at `O^-`, a property of
  `≤` alone; second countability has done all it visibly can (it supplied `CurvesExtend`).
* The time function of track A is not a Cauchy time function, so it gives no splitting.
* Non-vacuity: `minkowski_curvesExtend_of_lemmaKSCLocal` (track A applies to Minkowski space) and
  `timelikeLine_isCauchySurface_zero_of_lemmaKSCLocal` (the hypotheses of
  `isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable` hold jointly on the
  timelike line with `Σ = {0}`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **Two-sidedness is automatic in a second countable spacetime.** A closed locally Cauchy set
of a second countable Hausdorff tarentin globally hyperbolic causally arc-connected spacetime is
locally Cauchy and two-sided. -/
theorem isLocallyCauchyTwoSided_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) {S : Set M}
    (hSc : IsClosed S) (hloc : C.IsLocallyCauchy S) : C.IsLocallyCauchyTwoSided S :=
  hloc.isLocallyCauchyTwoSided hT hG hC (curvesExtend_of_secondCountable hT hG) hSc

/-- **The second countable Lemma K, sharp.** In the exact setting of
`CausalScaffold.LemmaKSCOpen.isCauchySurface_of_isLocallyCauchy_of_secondCountable`, `Σ` is a
Cauchy surface iff the causal future of its chart future side and the causal past of its chart
past side are open. -/
theorem isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S ↔ IsOpen (C.Jplus ⊤ (C.chartFutureSide S)) ∧
      IsOpen (C.Jminus ⊤ (C.dual.chartFutureSide S)) :=
  isCauchySurface_iff_isOpen_Jplus_chartFutureSide hT hG hC hJm hJp
    (curvesExtend_of_secondCountable hT hG) hSc hSconn hloc

/-- **The second countable Lemma K under causal openness** (`J^±(V)` open for `V` open). -/
theorem isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus hT hG hC hJm hJp
    (curvesExtend_of_secondCountable hT hG) hOp hOm hSc hSconn hloc

/-- **(1′) and (2′) in a second countable spacetime under causal openness.** -/
theorem local_conditions_of_isOpen_Jplus_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    (∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) ∧
      (∀ q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S, q ∉ S → C.Jplus ⊤ S ∪ C.Jminus ⊤ S ∈ 𝓝 q) :=
  local_conditions_of_isOpen_Jplus hT hG hC hJm hJp (curvesExtend_of_secondCountable hT hG) hOp
    hOm hSc hSconn hloc

end Causality

/-! ### Non-vacuity -/

/-- Track A applies to Minkowski space: curves extend there, by Levin's time function. -/
theorem minkowski_curvesExtend_of_lemmaKSCLocal (n : ℕ) : (minkowski n).CurvesExtend :=
  Causality.curvesExtend_of_secondCountable minkowski_tarentin minkowski_globallyHyperbolic

/-- On the timelike line every hypothesis of
`isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable` holds with `Σ = {0}`, and
it applies. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKSCLocal :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable hT hG hC
    hJm hJp timelikeLine_isOpen_Jplus timelikeLine_isOpen_Jminus hSc hSconn hloc.isLocallyCauchy

end Causal
