import Causal.NestedCausalities
import Causal.LadderLocal
import Causal.GluingModels.Minimal

/-!
# The cut line: ≤-nested in the timelike line, not inextensibly nested in it at M

No label is certified here: the file is the programme target
`T-abs-cutline-inextensible-direct` (layer 1, no label of `ETT.tex`). It gives the ladder's
`[[fails]] le_nested → inextensible_nested` (`programme/ladder.toml`) a **direct** witness, in the
ladder's own predicates, in place of the indirect `Causal.not_isCauchySurface_of_nested_bare`
(which refutes the Cauchy transfer, and reaches the pair only through
`Causality.IsCauchySurfaceOn.of_nested`).

* `cutLine_separates_inextensibleNested` — **the witness**. The line cut at `1`
  (`Causal.cutLine 1`: the timelike line in which nothing lies causally before `1` but `1`
  itself), the narrower causality, and the timelike line, the wider:
  `(cutLine 1).LeNested timelikeLine` (the `from`, `le_nested`),
  `¬ (cutLine 1).InextensibleNestedOn timelikeLine ⊤` (the failure of `inextensible_nested` at
  `W = M`), the cut line causal, and both causalities glue — the cut line and the timelike line
  absolutely minimal on `M` and on every open set (both forms of DEC-167's gluing, whichever OQ-95
  rules; `timelikeLine_absolutelyMinimal`, `timelikeLine_absolutelyMinimalOn`) — so that the
  witness stands in either reading of `defi:causalite`.
* `cutLine_not_inextensibleNestedOn_top` — the failure alone: the identity over `[1, ∞)` is
  inextensible for the cut line (`cutLine_inextensible_Ici`: it starts at `1`, whose causal past is
  `{1}`) and misses `{0}`, a Cauchy surface of the timelike line
  (`timelikeLine_isCauchySurface_zero`), so it is not inextensible for the timelike line.
* `cutLine_inextensibleNested_missing` — some of what the narrower causality lacks among the
  hypotheses of the consequences that give the nesting on `M`: `1` is a past endpoint
  (`¬ (cutLine 1).NoPastEndpoint`, `J⁻_M({1}) = {1}`), a hypothesis of
  `Causality.inextensibleNestedOn_top` (which also asks closed `J^±` of points, and fails here too,
  `J⁺(0) = [0, ∞) ∖ {1}`, not stated), and the cut line is not globally hyperbolic, a hypothesis of
  `Causality.GloballyHyperbolic.inextensibleNestedOn_top` only; the wider timelike line is globally
  hyperbolic with Cauchy surface `{0}`. It lacks at least these, so it does not show that any one
  of them alone is needed.

## Hypothesis checklist

| ladder entry | here |
|---|---|
| `from = "le_nested"`: `Causality.LeNested C C'`, `C` narrower | ✓ `(cutLine 1).LeNested timelikeLine` |
| `to = "inextensible_nested"`: `Causality.InextensibleNestedOn C C' W`, `W = M` unless named | ✓ refuted at `W = ⊤` |
| space (none: `ℝ` is Hausdorff and second countable) | ✓ `ℝ`, no instance argument |
| gluing (DEC-167, both forms of OQ-95) | ✓ `AbsolutelyMinimal` and `∀ W, AbsolutelyMinimalOn W` |

## SCOPE (disclosed)

* Nothing of `ETT.tex` is marked; the file assembles strict-library results
  (`Causal.NestedCausalities`, `Causal.Geroch`, `Causal.GluingModels.Minimal`, `Causal.LadderLocal`)
  and proves one new step, `J⁻_M({1}) = {1}` for the cut line.
* Curve-nesting on every open set (`le_nested ⇒ curve_nested`, `LeNested.curveNestedOn`) is not a
  conjunct: the ladder's closure gives it, and through it the same witness refutes
  `curve_nested → inextensible_nested`.
* Whether the cut line is causally arc-connected is not settled here (it is argued to fail in
  `Causal.GluingModels.Minimal`, not proved).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

/-- **The cut line is not inextensibly nested in the timelike line at `M`**: the identity over
`[1, ∞)` is inextensible for the line cut at `1` and misses the timelike line's Cauchy surface
`{0}`. -/
theorem cutLine_not_inextensibleNestedOn_top :
    ¬ (cutLine 1).InextensibleNestedOn timelikeLine ⊤ := fun h => by
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, hx⟩, -⟩ :=
    timelikeLine_isCauchySurface_zero (Ici 1) id (h cutLine_inextensible_Ici)
  have h1 : (1 : ℝ) ≤ t := ht
  rw [mem_singleton_iff, id] at hx
  linarith

/-- In the line cut at `1`, the causal past of `1` in `M` is `{1}`. -/
theorem cutLine_one_Jminus_top : (cutLine 1).Jminus ⊤ {(1 : ℝ)} = {1} := by
  ext y
  refine ⟨fun ⟨x, hx, hyx⟩ => ?_, fun hy => ⟨1, mem_singleton 1, ?_⟩⟩
  · rw [mem_singleton_iff] at hx ⊢
    subst hx
    rcases hyx with ⟨rfl, -⟩ | ⟨-, h, -⟩
    · rfl
    · exact absurd rfl h
  · rw [mem_singleton_iff] at hy
    subst hy
    exact (cutLine 1).le_refl (mem_univ _)

/-- The line cut at `1` has a past endpoint at `1`. -/
theorem cutLine_one_not_noPastEndpoint : ¬ (cutLine 1).NoPastEndpoint := fun h =>
  (Causality.noPastEndpoint_def.1 h) 1 cutLine_one_Jminus_top

/-- **The direct witness for `le_nested ⇏ inextensible_nested`** (`programme/ladder.toml`,
`[[fails]] from = "le_nested"`, `to = "inextensible_nested"`): the line cut at `1` is ≤-nested in
the timelike line and not inextensibly nested in it at `M`; it is causal, and both causalities
glue, on `M` and on every open set (DEC-167, either form of OQ-95). -/
theorem cutLine_separates_inextensibleNested :
    (cutLine 1).LeNested timelikeLine ∧ ¬ (cutLine 1).InextensibleNestedOn timelikeLine ⊤ ∧
      (cutLine 1).IsCausal ∧ (cutLine 1).AbsolutelyMinimal ∧
      (∀ W : Opens ℝ, (cutLine 1).AbsolutelyMinimalOn W) ∧
      timelikeLine.AbsolutelyMinimal ∧ ∀ W : Opens ℝ, timelikeLine.AbsolutelyMinimalOn W :=
  ⟨cutLine_leNested 1, cutLine_not_inextensibleNestedOn_top, cutLine_isCausal 1,
    GluingModels.cutLine_minimal 1, GluingModels.cutLine_hereditary 1,
    timelikeLine_absolutelyMinimal, timelikeLine_absolutelyMinimalOn⟩

/-- **Some of what the narrower causality lacks** among the hypotheses of the nesting on `M`: a
past endpoint at `1` (against `Causality.inextensibleNestedOn_top`'s `NoPastEndpoint`) and no
global hyperbolicity (against `Causality.GloballyHyperbolic.inextensibleNestedOn_top`), while the
wider timelike line is globally hyperbolic with Cauchy surface `{0}`. It lacks at least these;
which alone is needed is not shown. -/
theorem cutLine_inextensibleNested_missing :
    ¬ (cutLine 1).GloballyHyperbolic ∧ ¬ (cutLine 1).NoPastEndpoint ∧
      timelikeLine.GloballyHyperbolic ∧ timelikeLine.IsCauchySurface ({0} : Set ℝ) :=
  ⟨cutLine_not_globallyHyperbolic 1, cutLine_one_not_noPastEndpoint,
    timelikeLine_globallyHyperbolic, timelikeLine_isCauchySurface_zero⟩

end Causal
