import Causal.LemmaKBare
import Causal.CurvesExtendSecondCountable

/-!
# Lemma K without a splitting, on a second countable spacetime, without `CurvesExtend`

Programme target `T-abs-curves-free-lemma-k` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.LemmaKBare` and `Causal.CurvesExtendSecondCountable`, both ETT-layer; no model;
no metric notion in a statement). **No label is marked** (SCOPE). Lemma K is DEC-44's
abstraction of a sentence Barbot asserts and never proves (Rem 2.3 `clomax`, `GHFspace.tex:572`,
the sentence at l.576–578); it carries no paper label.

Each of the eleven theorems of `Causal.LemmaKBare` carrying the named model fact
`hext : C.CurvesExtend` (kb/0012) has here a form **beside the original**, of the same name
suffixed `_secondCountable`: exactly the original's binders less `hext`, with
`[SecondCountableTopology M]` inserted after the original's `[T2Space M]` (all eleven are
already `[T2Space M]`, so `T1Space M` follows). `hext` is discharged by one term,
`Causality.curvesExtend_of_t1_secondCountable C` (kb/0142, `Causal.CurvesExtendSecondCountable`).
ETT's spacetimes are Hausdorff and second countable:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Barbot, Rem 2.3,
> `GHFspace.tex:576–578`)

## What is proved (no `sorry`)

1. The chart steps: `exists_lt_of_le_of_isCauchySurfaceOn_secondCountable`,
   `exists_lt_of_le_of_ne_of_isLocallyCauchy_secondCountable`.
2. The openness of the strict causal future: `isOpen_strictJplus_of_Zminus_secondCountable`,
   `isOpen_strictJplus_of_twoSided_secondCountable`,
   `isOpen_strictJplus_of_isCauchySplitting_secondCountable`.
3. Acausality: `isAcausal_of_isLocallyCauchy_secondCountable`.
4. **Lemma K without a splitting**, its four forms: the core
   (`isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus_secondCountable`), the chronal form
   (`isCauchySurface_of_isLocallyCauchy_of_chronal_secondCountable`), the two-sided form
   (`isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus_secondCountable`), the gx shape
   (`isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp_secondCountable`), and `CompactCauchy`'s
   proved form through the core (`isCauchySurface_of_isCauchySplitting_via_strictJplus_secondCountable`).
5. Witnesses (kb/0011), as in the original file: the chronal, two-sided and gx forms applied on
   the timelike line to `Σ = {0}`, no curve hypothesis supplied
   (`timelikeLine_isCauchySurface_zero_of_lemmaKBare{,_twoSided,_gx}_secondCountable`).

## Hypothesis checklist

Against the originals (`Causal/LemmaKBare.lean:198–562`); their own checklist against DEC-44
(`Causal/LemmaKBare.lean:65–76`) stands for every other row.

| original | here |
|---|---|
| `[T2Space M]`, no countability | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| `hext : C.CurvesExtend` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable C` |
| the openness hypotheses, push-up, `Z^±`, two-sidedness, the splitting | ⚠ carried unchanged (the original's SCOPE) |
| `Tarentin`, `GloballyHyperbolic`, `CausallyArcConnected`, `J^±(p) ≠ {p}`, connected | ✓ carried where the original has them |

## SCOPE (disclosed)

* **Nothing marked.** No ledger row lists a declaration of `Causal.LemmaKBare`; these are
  curve-free forms of Lemma K's ETT-layer family, not an anchor. They still carry the original's
  openness data, so none is DEC-44's bare form (`CausalScaffold.CompactCauchy`, a tagged `sorry`,
  untouched).
* **Beside, not replacing** (OQ-98 open): each new form is the original less `hext` plus one
  instance, checked by elaborated binder lists (kb/0227).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ## 1. The chart steps without `hext` -/

/-- `exists_lt_of_le_of_isCauchySurfaceOn` without `hext`, `M` second countable: in a causally
convex open `U` in which `S ∩ U` is Cauchy, a point `y ∈ U ∖ S` above `z ∈ S ∩ U`, strongly
tarentin in the past, is in the chronological future of a point of `S`. -/
theorem exists_lt_of_le_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hpush : C.PushUp) {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hSc : IsClosed S) (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {z y : M} (hz : z ∈ S ∩ U)
    (hy : y ∈ U) (hyS : y ∉ S) (hyZ : y ∈ C.Zminus) (hzy : C.le ⊤ z y) :
    ∃ σ ∈ S, C.lt ⊤ σ y :=
  exists_lt_of_le_of_isCauchySurfaceOn hT hG hC (curvesExtend_of_t1_secondCountable C) hpush hU
    hSc hSU hz hy hyS hyZ hzy

/-- `exists_lt_of_le_of_ne_of_isLocallyCauchy` without `hext`, `M` second countable. -/
theorem exists_lt_of_le_of_ne_of_isLocallyCauchy_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hpush : C.PushUp) (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsClosed S)
    (hloc : C.IsLocallyCauchy S) {z x : M} (hz : z ∈ S) (hzx : C.le ⊤ z x) (hne : x ≠ z) :
    ∃ σ ∈ S, C.lt ⊤ σ x :=
  exists_lt_of_le_of_ne_of_isLocallyCauchy hT hG hC (curvesExtend_of_t1_secondCountable C) hpush hZm
    hSc hloc hz hzx hne

/-! ## 2. The strict causal future is open, without `hext` -/

/-- `isOpen_strictJplus_of_Zminus` without `hext`, `M` second countable. -/
theorem isOpen_strictJplus_of_Zminus_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hpush : C.PushUp) (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsClosed S)
    (hloc : C.IsLocallyCauchy S) : IsOpen (C.strictJplus S) :=
  isOpen_strictJplus_of_Zminus hT hG hC hJm (curvesExtend_of_t1_secondCountable C) hpush hZm hSc
    hloc

/-- `isOpen_strictJplus_of_twoSided` without `hext`, `M` second countable. -/
theorem isOpen_strictJplus_of_twoSided_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hO : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    {S : Set M} (hloc : C.IsLocallyCauchyTwoSided S) : IsOpen (C.strictJplus S) :=
  isOpen_strictJplus_of_twoSided hcaus hC (curvesExtend_of_t1_secondCountable C) hO hloc

/-! ## 3. Acausality without `hext` -/

/-- `isAcausal_of_isLocallyCauchy` without `hext`, `M` second countable: a compact connected
locally Cauchy set whose strict causal future is open is acausal. -/
theorem isAcausal_of_isLocallyCauchy_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) (hQ : IsOpen (C.strictJplus S)) :
    C.IsAcausal S :=
  isAcausal_of_isLocallyCauchy hT hG hC (curvesExtend_of_t1_secondCountable C) hSc hSconn hloc hQ

/-! ## 4. Lemma K without a splitting, without `hext` -/

/-- **Lemma K without a splitting, the core, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus` without `hext`): on a connected,
Hausdorff, second countable, tarentin, globally hyperbolic, causally arc-connected spacetime with
`J^±(p) ≠ {p}`, a compact connected locally Cauchy set whose strict causal future and past are
open is a Cauchy surface. -/
theorem isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) (hQp : IsOpen (C.strictJplus S))
    (hQm : IsOpen (C.dual.strictJplus S)) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hSc hSconn hloc hQp hQm

/-- **Lemma K, the chronal form, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchy_of_chronal` without `hext`): the bare form's hypotheses plus
second countability, push-up and `Z^± = M`. -/
theorem isCauchySurface_of_isLocallyCauchy_of_chronal_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hpush : C.PushUp) (hZp : ∀ p : M, p ∈ C.Zplus)
    (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_chronal hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hpush hZp hZm hSc hSconn hloc

/-- **Lemma K, two-sided, without a splitting, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus` without `hext`). -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hOp hOm hSc hSconn hloc

/-- **Lemma K in the shape gx needs, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp` without `hext`). -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hpush : C.PushUp) (hZp : ∀ p : M, p ∈ C.Zplus)
    (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hpush hZp hOp hSc hSconn hloc

/-- `isOpen_strictJplus_of_isCauchySplitting` without `hext`, `M` second countable: under a
splitting and two-sidedness the core's openness hypotheses hold. -/
theorem isOpen_strictJplus_of_isCauchySplitting_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M}
    (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchyTwoSided S) :
    IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) :=
  isOpen_strictJplus_of_isCauchySplitting hcaus hC (curvesExtend_of_t1_secondCountable C) hψ hSc
    hSconn hloc

/-- `isCauchySurface_of_isCauchySplitting_via_strictJplus` without `hext`, `M` second countable:
`CompactCauchy`'s proved form, through the core. A twin: it states what
`Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable`
(`Causal.CurvesFreeCauchy.CompactCauchy`) states, the implicit `{S₀} {ψ}` in another position,
since its original re-proves `isCauchySurface_of_isLocallyCauchyTwoSided`. -/
theorem isCauchySurface_of_isCauchySplitting_via_strictJplus_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M} (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) :
    C.IsCauchySurface S :=
  isCauchySurface_of_isCauchySplitting_via_strictJplus hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hψ hSc hSconn hloc

end Causality

/-! ## 5. Witnesses on the timelike line (kb/0011) -/

/-- **The chronal form's new form applies with no curve hypothesis supplied**: on the timelike
line (`ℝ`, Hausdorff and second countable) with `Σ = {0}`; the original's
`timelikeLine_curvesExtend` is not asked. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hpush, hZp, hZm, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_chronal_secondCountable hT hG hC hJm hJp
    hpush hZp hZm hSc hSconn hloc

/-- The two-sided form's new form applied on the timelike line, no curve hypothesis supplied. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare_twoSided_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, -, hOp, hOm, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_twoSided_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus_secondCountable hT hG
    hC hJm hJp hOp hOm hSc hSconn hloc

/-- The gx shape's new form applied on the timelike line, no curve hypothesis supplied. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare_gx_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hpush, hZp, hOp, -, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_twoSided_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp_secondCountable hT hG hC
    hJm hJp hpush hZp hOp hSc hSconn hloc

end Causal
