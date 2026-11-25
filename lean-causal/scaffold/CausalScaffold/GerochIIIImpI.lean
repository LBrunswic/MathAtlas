import CausalScaffold.GerochEquiv
import CausalScaffold.GerochCauchy
import Causal.Remarks.SingularRowsDiamondPast
import Causal.Remarks.SingularRowsGeroch
import Causal.SingularCauchy

/-!
# `theo:geroch_sing` (iii)⇒(i) under local causal closedness (DEC-149); the counterexample excluded

`theo:geroch_sing` — `ETT.tex:1771` (proof of the equivalence l.1781–1785). **Not marked**: the
equivalence is proved here for the abstraction `SingularFlatAxioms` carrying local causal
closedness (DEC-149), and at `E_{≥0}`-manifolds with local causal closedness a named hypothesis;
the « Moreover » is elsewhere (`Causal.SingularSplitting`). `theo:geroch` — `ETT.tex:1256`: the
refutation of its printed (iii)⇒(i) does not reach the repaired form.

> Let $M$ be a singular flat spacetime. The following are equivalent: (i) $M$ is globally
> hyperbolic; (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.

> The first part is a direct consequence of Theorem \ref{theo:geroch} and of Proposition
> \ref{prop:mesure_admissible} [...]

DEC-149 (OQ-33): `SingularFlatAxioms` carries the same local closedness as DEC-148's, in charts.
`SingularFlatAxioms` is a strict structure, not edited: the field is the hypothesis
`C.LocallyCausallyClosed` (`CausalScaffold.GerochEquiv`) beside it.

## What is proved (no `sorry` in this file)

* `SingularFlatAxioms.geroch_sing_iii_imp_i_of_locallyCausallyClosed`: strongly causal (DEC-18),
  locally causally closed, a Cauchy surface ⇒ globally hyperbolic; no measure. The engine
  `Causality.globallyHyperbolic_of_isCauchySurface_of_isOpen` applies with every input
  discharged: T2, second countable, metrizable, locally compact and causally arc-connected are
  fields; `J^∓` of open sets are open (`SingularFlatAxioms.isOpen_Jminus`, `isOpen_Jplus`, BTZ
  points included); `J^±(S)` are closed (`SingularFlatAxioms.sigma_separe_of_isCausal`).
* `SingularFlatAxioms.geroch_sing_of_locallyCausallyClosed` (the equivalence, with
  `ModelMeasures`) and `geroch_sing_tfae_locallyCausallyClosed` ((i) ⇔ (ii) ∧ L ⇔ (iii) ∧ L).
* At every strongly causal, Hausdorff, second countable `E_{≥0}`-manifold:
  `SingularRowsGeroch.geroch_sing_iii_imp_i_of_locallyCausallyClosed` and
  `SingularRowsGeroch.geroch_sing_of_locallyCausallyClosed`, local causal closedness a named
  hypothesis (kb/0012).
* `chronoMinkowski_not_locallyCausallyClosed` (`n ≥ 1`): OQ-32's and OQ-33's witness is not
  locally causally closed. `chronoMinkowski_engine_hypotheses`: it has every other input of the
  engine, so local causal closedness cannot be dropped from it.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| a singular flat spacetime | ⚠ reading: `SingularFlatAxioms` (abstract); at `E_{≥0}`-manifolds `IsoChartsCoverDEC25` (DEC-25, OQ-18) |
| strongly causal (DEC-18) | ✓ carried |
| local causal closedness, in charts (DEC-149) | ✓ carried as `LocallyCausallyClosed`; ⚠ reading: stated on `M`, not chart by chart |
| the measures of `prop:mesure_admissible` | `ModelMeasures` (⚠ strengthened, as in `Causal.SingularGeroch`), for (i)⇒(ii) only; (iii)⇒(i) uses none |
| connected | ⚠ weakened: not used |

## SCOPE (disclosed)

* **Not proved: local causal closedness at an `E_{≥0}`-manifold.** It is the closedness of the
  models' causal relations on small causally convex chart domains (`lem:densite_modele`), a
  layer-3 lemma the library does not have. Once proved, `SingularRowsGeroch`'s forms here lose
  their hypothesis and `CausalScaffold.SingularRowsGerochEquiv.geroch_sing_iii_imp_i` (which
  omits it) follows.
* `CausalScaffold.SingularGeroch.geroch_sing_of_stronglyCausal` (the printed abstraction, false:
  `Causal.not_geroch_sing_of_stronglyCausal`) is not edited here.
* Model layer: imports `CausalScaffold.GerochCauchy` (Minkowski) and `Causal.SingularGeroch`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

universe u

namespace Causality

namespace SingularFlatAxioms

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {sing : ℝ → Set M}

/-- **`theo:geroch_sing` (iii)⇒(i)** for `SingularFlatAxioms` carrying local causal closedness
(DEC-149), strongly causal (DEC-18). -/
theorem geroch_sing_iii_imp_i_of_locallyCausallyClosed (h : C.SingularFlatAxioms sing)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (hS : ∃ S : Set M, C.IsCauchySurface S) : C.GloballyHyperbolic := by
  haveI := h.t2
  haveI := h.secondCountable
  haveI := h.metrizable
  haveI := h.locallyCompact
  obtain ⟨S, hS⟩ := hS
  obtain ⟨hSp, hSm, -⟩ := h.sigma_separe_of_isCausal hSC.isCausal hS
  exact globallyHyperbolic_of_isCauchySurface_of_isOpen h.causallyArcConnected hSC hL
    (fun _ hW => h.isOpen_Jminus hW) (fun _ hW => h.isOpen_Jplus hW) hS hSp hSm

/-- **`theo:geroch_sing`, the equivalence**, for `SingularFlatAxioms` carrying local causal
closedness (DEC-149), strongly causal (DEC-18), with the model measures. -/
theorem geroch_sing_of_locallyCausallyClosed [MeasurableSpace M] [BorelSpace M]
    (h : C.SingularFlatAxioms sing) (hSC : C.StronglyCausal) (hM : C.ModelMeasures)
    (hL : C.LocallyCausallyClosed) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  haveI := h.t2
  tfae_have 1 → 2 := h.geroch_sing_i_imp_ii hM
  tfae_have 2 → 3 := geroch_ii_imp_iii h.causallyArcConnected hSC h.Jminus_ne_singleton
    h.Jplus_ne_singleton
  tfae_have 3 → 1 := h.geroch_sing_iii_imp_i_of_locallyCausallyClosed hSC hL
  tfae_finish

/-- **`theo:geroch_sing`, the equivalence, with local causal closedness in the conditions**: a
globally hyperbolic singular flat spacetime is locally causally closed, so (i) ⇔ (ii) ∧ L ⇔
(iii) ∧ L with no closedness assumed. -/
theorem geroch_sing_tfae_locallyCausallyClosed [MeasurableSpace M] [BorelSpace M]
    (h : C.SingularFlatAxioms sing) (hSC : C.StronglyCausal) (hM : C.ModelMeasures) :
    List.TFAE [C.GloballyHyperbolic,
      (∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) ∧
        C.LocallyCausallyClosed,
      (∃ S : Set M, C.IsCauchySurface S) ∧ C.LocallyCausallyClosed] := by
  haveI := h.t2
  tfae_have 1 → 2 := fun hG =>
    ⟨h.geroch_sing_i_imp_ii hM hG, hG.locallyCausallyClosed h.tarentin⟩
  tfae_have 2 → 3 := fun ⟨hT, hL⟩ => ⟨geroch_ii_imp_iii h.causallyArcConnected hSC
    h.Jminus_ne_singleton h.Jplus_ne_singleton hT, hL⟩
  tfae_have 3 → 1 := fun ⟨hS, hL⟩ => h.geroch_sing_iii_imp_i_of_locallyCausallyClosed hSC hL hS
  tfae_finish

end SingularFlatAxioms

end Causality

/-! ### At every `E_{≥0}`-manifold, local causal closedness a named hypothesis -/

namespace SingularRowsGeroch

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **`theo:geroch_sing` (iii)⇒(i) at every strongly causal (DEC-18), Hausdorff, second countable
`E_{≥0}`-manifold** whose causality is locally causally closed (DEC-149, a named hypothesis). -/
theorem geroch_sing_iii_imp_i_of_locallyCausallyClosed [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (h : ∃ S : Set M, C.IsCauchySurface S) : C.GloballyHyperbolic :=
  (SFAManifolds.singularFlatAxioms hmin hC).geroch_sing_iii_imp_i_of_locallyCausallyClosed hSC hL h

/-- **`theo:geroch_sing`, the equivalence, at every strongly causal (DEC-18), Hausdorff, second
countable `E_{≥0}`-manifold** whose causality is locally causally closed (DEC-149). -/
theorem geroch_sing_of_locallyCausallyClosed [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_sing_i_imp_ii hmin hC
  tfae_have 2 → 3 := geroch_sing_ii_imp_iii hmin hC hSC
  tfae_have 3 → 1 := geroch_sing_iii_imp_i_of_locallyCausallyClosed hmin hC hSC hL
  tfae_finish

end SingularRowsGeroch

/-! ### The refutation of the printed form does not reach the repaired one -/

/-- **Chronological Minkowski space is not locally causally closed** (`n ≥ 1`): it satisfies every
other hypothesis of `geroch_sing_iii_imp_i_of_locallyCausallyClosed` (`SingularFlatAxioms` with an
empty singular locus, strong causality, a Cauchy surface) and is not globally hyperbolic. -/
theorem chronoMinkowski_not_locallyCausallyClosed {n : ℕ} (hn : 0 < n) :
    ¬ (chronoMinkowski n).LocallyCausallyClosed := by
  intro hL
  obtain ⟨-, -, hSC, -, -, -, -, -, hS, hnot⟩ := chronoMinkowski_counterexample hn
  exact hnot ((chronoMinkowski_singularFlatAxioms n).geroch_sing_iii_imp_i_of_locallyCausallyClosed
    hSC hL ⟨_, hS⟩)

/-- **Every hypothesis of the engine but local causal closedness holds on chronological Minkowski
space** (`n ≥ 1`), and its conclusion fails: local causal closedness cannot be dropped from
`Causality.globallyHyperbolic_of_isCauchySurface_of_isOpen`. -/
theorem chronoMinkowski_engine_hypotheses {n : ℕ} (hn : 0 < n) :
    (chronoMinkowski n).CausallyArcConnected ∧ (chronoMinkowski n).StronglyCausal ∧
      (∀ W : Set (Minkowski n), IsOpen W → IsOpen ((chronoMinkowski n).Jminus ⊤ W)) ∧
      (∀ W : Set (Minkowski n), IsOpen W → IsOpen ((chronoMinkowski n).Jplus ⊤ W)) ∧
      (chronoMinkowski n).IsCauchySurface {p | p.1 = 0} ∧
      IsClosed ((chronoMinkowski n).Jplus ⊤ {p | p.1 = 0}) ∧
      IsClosed ((chronoMinkowski n).Jminus ⊤ {p | p.1 = 0}) ∧
      ¬ (chronoMinkowski n).LocallyCausallyClosed ∧
      ¬ (chronoMinkowski n).GloballyHyperbolic := by
  obtain ⟨-, hC, hSC, -, -, -, -, -, hS, hnot⟩ := chronoMinkowski_counterexample hn
  have h := chronoMinkowski_singularFlatAxioms n
  obtain ⟨hSp, hSm, -⟩ := h.sigma_separe_of_isCausal hSC.isCausal hS
  exact ⟨hC, hSC, fun _ hW => h.isOpen_Jminus hW, fun _ hW => h.isOpen_Jplus hW, hS, hSp, hSm,
    chronoMinkowski_not_locallyCausallyClosed hn, hnot⟩

end Causal
