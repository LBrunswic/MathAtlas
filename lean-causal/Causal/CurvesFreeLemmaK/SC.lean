import Causal.LevinUtility
import Causal.CurvesFreeLemmaK.Reduction

/-!
# Lemma K's acausality and openness steps on a second countable spacetime, without `CurvesExtend`

Programme target `T-abs-curves-free-lemma-k` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.LevinUtility` (which imports `Causal.LemmaKSC`) and
`Causal.CurvesFreeLemmaK.Reduction`, ETT-layer; no model; no metric notion in a
statement). **No label is marked** (SCOPE). Lemma K is DEC-44's abstraction of Barbot's
Rem 2.3 `clomax` (`GHFspace.tex:572`); it carries no paper label.

`Causal.LemmaKSC` has five theorems carrying the named model fact `hext : C.CurvesExtend`
(kb/0012). Two already have their form, exactly the original less `hext` plus
`[SecondCountableTopology M]`, in `Causal.LevinUtility` (`isCauchySurface_iff_local_of_secondCountable`,
`isCauchySurface_iff_isOpen_strictJplus_of_secondCountable`: Levin's route,
`curvesExtend_of_secondCountable hT hG`). The other three have here a form **beside the
original**, of the same name suffixed `_secondCountable`: exactly the original's binders less
`hext`, with `[SecondCountableTopology M]` inserted after the original's `[T2Space M]`. `hext` is
discharged by `Causality.curvesExtend_of_t1_secondCountable C` (kb/0142).

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

## What is proved (no `sorry`)

* `isOpen_strictJplus_of_isCauchySurface_secondCountable`: the strict causal future and past of a
  compact Cauchy surface are open.
* `isAcausal_of_isLocallyCauchy_of_relOpen_secondCountable`: acausality from relative openness.
* `isAcausal_iff_of_isLocallyCauchy_secondCountable`: acausality of a compact connected locally
  Cauchy set is a local property.
* Witnesses (kb/0011) on the timelike line, `Σ = {0}`, no curve hypothesis supplied:
  `timelikeLine_isOpen_strictJplus_zero_secondCountable`, `timelikeLine_lemmaKSC_local_secondCountable`
  (the original file's witness, through Levin's form), `timelikeLine_isAcausal_zero_of_relOpen_secondCountable`
  and `timelikeLine_isAcausal_zero_iff_secondCountable`.

## Hypothesis checklist

| original (`Causal/LemmaKSC.lean:193, 250, 343`) | here |
|---|---|
| `[T2Space M]`, no countability | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| `hext : C.CurvesExtend` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable C` |
| every other binder | ✓ carried unchanged |

## SCOPE (disclosed)

* **Nothing marked.** No ledger row lists a declaration of `Causal.LemmaKSC`.
* **Beside, not replacing** (OQ-98 open), checked by elaborated binder lists (kb/0227); the two
  pre-existing forms of `Causal.LevinUtility` are re-verified there and not restated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- `isOpen_strictJplus_of_isCauchySurface` without `hext`, `M` second countable: for a compact
Cauchy surface the strict causal future and past are open. -/
theorem isOpen_strictJplus_of_isCauchySurface_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : C.IsCauchySurface S) :
    IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) :=
  isOpen_strictJplus_of_isCauchySurface hT hG hC hJm hJp (curvesExtend_of_t1_secondCountable C) hSc
    hSne hS

/-- `isAcausal_of_isLocallyCauchy_of_relOpen` without `hext`, `M` second countable. -/
theorem isAcausal_of_isLocallyCauchy_of_relOpen_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S)
    (hQ : ∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S) :
    C.IsAcausal S :=
  isAcausal_of_isLocallyCauchy_of_relOpen hT hG hC (curvesExtend_of_t1_secondCountable C) hSc hSconn
    hloc hQ

/-- `isAcausal_iff_of_isLocallyCauchy` without `hext`, `M` second countable: acausality is a local
property of a compact connected locally Cauchy set. -/
theorem isAcausal_iff_of_isLocallyCauchy_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsAcausal S ↔ ∀ w ∈ S ∩ C.strictJplus S, ∃ N ∈ 𝓝 w, S ∩ N ⊆ C.strictJplus S :=
  isAcausal_iff_of_isLocallyCauchy hT hG hC (curvesExtend_of_t1_secondCountable C) hSc hSconn hloc

end Causality

/-! ### Witnesses on the timelike line (kb/0011) -/

/-- The strict causal future and past of `{0}` on the timelike line are open, through the new
form, from a curve-free Cauchy witness. -/
theorem timelikeLine_isOpen_strictJplus_zero_secondCountable :
    IsOpen (timelikeLine.strictJplus ({0} : Set ℝ)) ∧
      IsOpen (timelikeLine.dual.strictJplus ({0} : Set ℝ)) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, -, -⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isOpen_strictJplus_of_isCauchySurface_secondCountable hT hG hC hJm hJp hSc
    (singleton_nonempty 0) timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable

/-- The local residue (1′)+(2′) on the timelike line for `Σ = {0}`, through
`isCauchySurface_iff_local_of_secondCountable` (`Causal.LevinUtility`), from a curve-free Cauchy
witness: the original's `timelikeLine_lemmaKSC_local` with no curve hypothesis supplied. -/
theorem timelikeLine_lemmaKSC_local_secondCountable :
    (∀ w ∈ ({0} : Set ℝ) ∩ timelikeLine.strictJplus {0},
        ∃ N ∈ 𝓝 w, ({0} : Set ℝ) ∩ N ⊆ timelikeLine.strictJplus {0}) ∧
      (∀ q ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ {0}, q ∉ ({0} : Set ℝ) →
        timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ {0} ∈ 𝓝 q) := by
  obtain ⟨-, hT, hG, hC, hJm, hJp, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaKSC_hypotheses
  exact (Causality.isCauchySurface_iff_local_of_secondCountable hT hG hC hJm hJp hSc hSconn
    hloc).1 timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable

/-- Acausality of `{0}` on the timelike line from relative openness, through the new form. -/
theorem timelikeLine_isAcausal_zero_of_relOpen_secondCountable :
    timelikeLine.IsAcausal ({0} : Set ℝ) := by
  obtain ⟨-, hT, hG, hC, -, -, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaKSC_hypotheses
  exact Causality.isAcausal_of_isLocallyCauchy_of_relOpen_secondCountable hT hG hC hSc hSconn hloc
    timelikeLine_lemmaKSC_local_secondCountable.1

/-- The local characterisation of acausality applied on the timelike line to `Σ = {0}`. -/
theorem timelikeLine_isAcausal_zero_iff_secondCountable :
    timelikeLine.IsAcausal ({0} : Set ℝ) ↔
      ∀ w ∈ ({0} : Set ℝ) ∩ timelikeLine.strictJplus {0},
        ∃ N ∈ 𝓝 w, ({0} : Set ℝ) ∩ N ⊆ timelikeLine.strictJplus {0} := by
  obtain ⟨-, hT, hG, hC, -, -, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaKSC_hypotheses
  exact Causality.isAcausal_iff_of_isLocallyCauchy_secondCountable hT hG hC hSc hSconn hloc

end Causal
