import Causal.CompactCauchy
import Causal.CurvesExtendSecondCountable

/-!
# Lemma K and its steps on a second countable spacetime, without `CurvesExtend`

Programme target `T-abs-curves-free-cauchy` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.CompactCauchy` and `Causal.CurvesExtendSecondCountable`, both ETT-layer; no model;
no metric notion in a statement). **No label is marked** (SCOPE). The row served, unmarked:
Barbot `bthm:cauclo` — `GHFspace.tex:352`, through Lemma K (`Causal.CompactCauchy`, DEC-44, the
corrected Rem 2.3 `clomax`, `GHFspace.tex:571`), whose decl
`Causality.isCauchySurface_of_isLocallyCauchyTwoSided` gains a curve-free form here.

Each of the seven theorems of `Causal.CompactCauchy` carrying the named model fact
`hext : C.CurvesExtend` (kb/0012) has here a form **beside the original**, of the same name
suffixed `_secondCountable`: exactly the original's binders less `hext`, with
`[SecondCountableTopology M]` inserted after the original's `[T2Space M]` (every one of the seven
is already `[T2Space M]`, so `T1Space M` follows). `hext` is discharged by one term,
`Causality.curvesExtend_of_t1_secondCountable C` (kb/0142, `Causal.CurvesExtendSecondCountable`).
ETT's spacetimes are Hausdorff and second countable:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Barbot, Rem 2.3,
> `GHFspace.tex:576–578`)

## What is proved (no `sorry`)

1. Step 1 (`eq_of_le_of_isCauchySurfaceOn`, `mem_Jplus_or_Jminus_of_isCauchySurfaceOn`).
2. Steps 2–4 (`exists_box_of_twoSided`, `exists_graph`, `exists_sign_nhds`, `isAcausal_of_graph`).
3. **Lemma K** (`isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable`): on a connected,
   Hausdorff, second countable, tarentin, globally hyperbolic, causally arc-connected spacetime with
   `J^±(p) ≠ {p}` and a splitting `ψ`, a compact connected locally Cauchy two-sided set is a Cauchy
   surface. Named data left: the splitting `ψ` and two-sidedness (the original's SCOPE).
4. Witnesses (kb/0011): Lemma K's new form applied on the timelike line to `Σ = {0}` and to
   `Σ = {1} ≠ S₀` (`timelikeLine_isCauchySurface_zero_of_lemmaK_secondCountable`,
   `timelikeLine_isCauchySurface_one_of_lemmaK_secondCountable`), with no curve hypothesis supplied.

## Hypothesis checklist

Against Lemma K's original (`Causal/CompactCauchy.lean:738`); its own checklist against DEC-44
(`Causal/CompactCauchy.lean:49–61`) stands for every other row.

| original | here |
|---|---|
| `[T2Space M]`, no countability | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| `hext : C.CurvesExtend` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable C` |
| the splitting `ψ`, `IsCauchySplitting` (named) | ⚠ carried unchanged |
| `IsLocallyCauchyTwoSided` (strengthened from DEC-44's `IsLocallyCauchy`) | ⚠ carried unchanged |
| `Tarentin`, `GloballyHyperbolic`, `CausallyArcConnected`, `J^±(p) ≠ {p}`, connected | ✓ carried |

## SCOPE (disclosed)

* **Nothing marked.** `bthm:cauclo` is the ledger's (closed through `Causal.Flat.Classification`);
  these are additional curve-free forms of one of its decls, not an anchor. Lemma K's form here
  still carries the splitting and two-sidedness, so it is not DEC-44's bare form
  (`CausalScaffold.CompactCauchy`, a tagged `sorry`, untouched).
* **Beside, not replacing** (OQ-98 open): the originals are unchanged; each new form is the
  original less `hext` plus one instance, checked by elaborated binder lists (kb/0227).
* The Lemma K family's other modules (`Causal.LemmaK*`) are `T-abs-curves-free-lemma-k`'s.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ## 1. Step 1 without `hext` -/

/-- `eq_of_le_of_isCauchySurfaceOn` without `hext`, `M` second countable: `S ∩ U` is acausal (in
`M`'s relation) when it is a Cauchy surface of a causally convex open `U`, and `M` is causal,
Hausdorff, second countable and causally arc-connected. -/
theorem eq_of_le_of_isCauchySurfaceOn_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) {U : Opens M}
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    {z w : M} (hz : z ∈ S ∩ U) (hw : w ∈ S ∩ U) (hzw : C.le ⊤ z w) : z = w :=
  eq_of_le_of_isCauchySurfaceOn hcaus hC (curvesExtend_of_t1_secondCountable C) hU hSU hz hw hzw

/-- `mem_Jplus_or_Jminus_of_isCauchySurfaceOn` without `hext`, `M` second countable: every point
of `U` is in the causal future or past of `S ∩ U` in `U`. -/
theorem mem_Jplus_or_Jminus_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal) {U : Opens M} {S : Set M}
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {q : M} (hq : q ∈ U) :
    q ∈ C.Jplus U (S ∩ U) ∪ C.Jminus U (S ∩ U) :=
  mem_Jplus_or_Jminus_of_isCauchySurfaceOn hcaus (curvesExtend_of_t1_secondCountable C) hSU hq

/-! ## 2. Steps 2–4 without `hext` -/

variable {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M}

/-- `exists_box_of_twoSided` without `hext`, `M` second countable: the box at a point of a locally
Cauchy two-sided set, for every small window. -/
theorem exists_box_of_twoSided_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hloc : C.IsLocallyCauchyTwoSided S) {y₀ : S₀} {t₀ : ℝ} (hx : ψ (y₀, t₀) ∈ S) :
    ∃ U : Opens M, C.CausallyConvexIn (U : Set M) ⊤ ∧
      (∀ z ∈ S ∩ U, ∀ w ∈ S ∩ U, C.le ⊤ z w → z = w) ∧
      ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ V : Set S₀, IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V,
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ U) ∧
        ∃ t ∈ Ioo (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ S ∧
          ∀ t' ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t') ∈ S → t' = t :=
  exists_box_of_twoSided hcaus hC (curvesExtend_of_t1_secondCountable C) hψ hloc hx

/-- `exists_graph` without `hext`, `M` second countable: a compact connected locally Cauchy
two-sided `S` meets every line of the splitting exactly once, at the time `h y` of a continuous
`h`. -/
theorem exists_graph_secondCountable [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchyTwoSided S) :
    ∃ h : S₀ → ℝ, Continuous h ∧ ∀ y t, ψ (y, t) ∈ S ↔ t = h y :=
  exists_graph hcaus hC (curvesExtend_of_t1_secondCountable C) hψ hSc hSconn hloc

/-- `exists_sign_nhds` without `hext`, `M` second countable: around a point of `S`, a point above
(below) the graph is in the causal future (past) of the point of `S` on its line. -/
theorem exists_sign_nhds_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hloc : C.IsLocallyCauchyTwoSided S) {h : S₀ → ℝ}
    (hgraph : ∀ y t, ψ (y, t) ∈ S ↔ t = h y) {w : M} (hw : w ∈ S) :
    ∃ O : Set M, IsOpen O ∧ w ∈ O ∧ ∃ U : Opens M, O ⊆ U ∧
      (∀ z ∈ S ∩ U, ∀ z' ∈ S ∩ U, C.le ⊤ z z' → z = z') ∧
      ∀ q ∈ O, ψ ((ψ.symm q).1, h (ψ.symm q).1) ∈ S ∩ U ∧
        (h (ψ.symm q).1 ≤ (ψ.symm q).2 → C.le ⊤ (ψ ((ψ.symm q).1, h (ψ.symm q).1)) q) ∧
        ((ψ.symm q).2 ≤ h (ψ.symm q).1 → C.le ⊤ q (ψ ((ψ.symm q).1, h (ψ.symm q).1))) :=
  exists_sign_nhds hcaus hC (curvesExtend_of_t1_secondCountable C) hψ hloc hgraph hw

/-- `isAcausal_of_graph` without `hext`, `M` second countable: `S` is acausal (the O'Neill step,
Lemma 14.45 in Brunswic's proof). -/
theorem isAcausal_of_graph_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hSc : IsClosed S) (hloc : C.IsLocallyCauchyTwoSided S) {h : S₀ → ℝ}
    (hcont : Continuous h) (hgraph : ∀ y t, ψ (y, t) ∈ S ↔ t = h y) : C.IsAcausal S :=
  isAcausal_of_graph hcaus hC (curvesExtend_of_t1_secondCountable C) hψ hSc hloc hcont hgraph

/-! ## 3. Lemma K without `hext` -/

/-- **Lemma K on a second countable spacetime** (DEC-44; `bthm:cauclo`'s decl, unmarked):
`isCauchySurface_of_isLocallyCauchyTwoSided` without `hext`. On a connected, Hausdorff, second
countable, tarentin, globally hyperbolic, causally arc-connected spacetime with `J^±(p) ≠ {p}`
carrying a splitting `ψ : S₀ × ℝ ≃ₜ M` with causally monotone lines, a compact connected set which
is locally Cauchy and two-sided is a Cauchy surface. -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp (curvesExtend_of_t1_secondCountable C)
    hψ hSc hSconn hloc

end Causality

/-! ## 4. Witnesses on the timelike line (kb/0011) -/

/-- **Lemma K's new form applies with no curve hypothesis supplied**: on the timelike line (`ℝ`,
Hausdorff and second countable), `Σ = S₀ = {0}` along the splitting `ψ(0, t) = t`; the original's
`timelikeLine_curvesExtend` is not asked. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaK_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hψ, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable hT hG hC hJm hJp hψ
    hSc hSconn hloc

/-- Lemma K's new form on the timelike line with `Σ = {1} ≠ S₀ = {0}`, over the splitting along
`{0}`: the new form, like the original, does not need `Σ` to be the base of the splitting. -/
theorem timelikeLine_isCauchySurface_one_of_lemmaK_secondCountable :
    timelikeLine.IsCauchySurface ({1} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hψ, hSc, hSconn, hloc, -⟩ := timelikeLine_lemmaK_hypotheses_one
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_secondCountable hT hG hC hJm hJp hψ
    hSc hSconn hloc

end Causal
