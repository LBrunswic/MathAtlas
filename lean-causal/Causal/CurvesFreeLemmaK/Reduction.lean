import Causal.LemmaKReduction
import Causal.CurvesFreeLemmaK.Bare

/-!
# Lemma K's exact residue on a second countable spacetime, without `CurvesExtend`

Programme target `T-abs-curves-free-lemma-k` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.LemmaKReduction` and `Causal.CurvesFreeLemmaK.Bare`, ETT-layer; no model;
no metric notion in a statement). **No label is marked** (SCOPE). Lemma K is DEC-44's
abstraction of Barbot's Rem 2.3 `clomax` (`GHFspace.tex:572`); it carries no paper label.

The one theorem of `Causal.LemmaKReduction` carrying the named model fact
`hext : C.CurvesExtend` (kb/0012), `isCauchySurface_iff_of_curvesExtend`, has here a form
**beside the original**, `isCauchySurface_iff_of_secondCountable` (the original's
`_of_curvesExtend` replaced, as in `Causal.CurvesFreeCauchy`): exactly the original's binders
less `hext`, with `[SecondCountableTopology M]` inserted after the original's `[T2Space M]`.
`hext` is discharged by `Causality.curvesExtend_of_t1_secondCountable C` (kb/0142).

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

## What is proved (no `sorry`)

* `isCauchySurface_iff_of_secondCountable`: on a connected, Hausdorff, second countable,
  tarentin, globally hyperbolic, causally arc-connected spacetime with `J^±(p) ≠ {p}`, a compact
  non-empty `Σ` is a Cauchy surface iff it is acausal and `J^+(Σ) ∪ J^-(Σ) = M`.
* Witness (kb/0011), as in the original file: `timelikeLine_reduction_hypotheses_secondCountable`,
  the criterion's hypotheses on the timelike line for `Σ = {0}`, obtained through the new form
  from a curve-free Cauchy witness, and the criterion applied
  (`timelikeLine_isCauchySurface_zero_of_reduction_secondCountable`).

## Hypothesis checklist

| original (`Causal/LemmaKReduction.lean:181`) | here |
|---|---|
| `[T2Space M]`, no countability | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| `hext : C.CurvesExtend` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable C` |
| every other binder | ✓ carried unchanged |

## SCOPE (disclosed)

* **Nothing marked.** No ledger row lists a declaration of `Causal.LemmaKReduction`.
* **Beside, not replacing** (OQ-98 open), checked by elaborated binder lists (kb/0227).
* What the new form says of the original's SCOPE: on every second countable spacetime (so on
  every ETT spacetime) the second countable Lemma K (`CausalScaffold.LemmaKSCOpen`, a tagged
  `sorry`) is *equivalent* to the two global facts (a compact connected locally Cauchy `Σ` is
  acausal, and `J^+(Σ) ∪ J^-(Σ) = M`), with no curve hypothesis left. Neither fact is proved here,
  and the bare form (`CausalScaffold.CompactCauchy`, no second countability) is untouched.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **The exact residue of the bare form, on a second countable spacetime**
(`isCauchySurface_iff_of_curvesExtend` without `hext`): a compact non-empty set is a Cauchy surface
iff it is acausal and its causal future and past cover `M`. -/
theorem isCauchySurface_iff_of_secondCountable [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) :
    C.IsCauchySurface S ↔ C.IsAcausal S ∧ ∀ q, q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S :=
  isCauchySurface_iff_of_curvesExtend hT hG hC hJm hJp (curvesExtend_of_t1_secondCountable C) hSc
    hSne

end Causality

/-! ### Witnesses on the timelike line (kb/0011) -/

/-- On the timelike line, `Σ = {0}` is acausal and its causal future and past form an open set,
through the new form, with no curve hypothesis supplied anywhere (the Cauchy property comes from
`timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable`). -/
theorem timelikeLine_reduction_hypotheses_secondCountable :
    timelikeLine.IsAcausal ({0} : Set ℝ) ∧
      IsOpen (timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∪ timelikeLine.Jminus ⊤ ({0} : Set ℝ)) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, -, -⟩ := timelikeLine_lemmaK_hypotheses
  obtain ⟨hac, hcov⟩ := (Causality.isCauchySurface_iff_of_secondCountable hT hG hC hJm hJp hSc
    (singleton_nonempty 0)).1 timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable
  refine ⟨hac, ?_⟩
  rw [eq_univ_of_forall hcov]
  exact isOpen_univ

/-- The Cauchy criterion applied on the timelike line to the curve-free hypotheses. -/
theorem timelikeLine_isCauchySurface_zero_of_reduction_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, -, -⟩ := timelikeLine_lemmaK_hypotheses
  obtain ⟨hac, hopen⟩ := timelikeLine_reduction_hypotheses_secondCountable
  exact Causality.isCauchySurface_of_isAcausal_of_isOpen hT hG hC hJm hJp hSc
    (singleton_nonempty 0) hac hopen

end Causal
