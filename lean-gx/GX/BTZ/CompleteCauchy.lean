import GX.BTZ.MixedDiamond
import GX.BTZ.Uniformization

/-!
# `GX.BTZ.CompleteCauchy` — the reading of « Cauchy-complete » for btz § 5.4 (a `C¹` spacelike complete Cauchy surface)

Target T-btz-reg-complete-length (a file move, no new mathematics). Paper `btz`
(`papers/btz/legacy/labeled/BTZ_1.tex`). This file certifies no label: it holds the definition
`GX.E0RegComplete.IsE0C1CompleteCauchy` (and `E0C1CauchyComplete`), moved verbatim from
`GX.BTZ.RegComplete` with their full names, so that the surgery files
(`GX.BTZ.SpearFamily`, `RegCompleteCauchy`, `RegCompleteLength`) can use the reading
without importing `RegComplete`, which now imports them to prove `btzprop:reg_complete`'s
Cauchy-completeness.

> […] a smooth spacelike Cauchy-surface which is […] metrically complete (btz l.227, the
> definition of Cauchy-complete)

## Hypothesis checklist

| paper | here |
|---|---|
| smooth spacelike Cauchy surface, metrically complete (l.227) | ⚠ read: DEC-31/119's `GX.IsE0CauchyComplete` data (`cauchy`, `reg`, `complete`, `continuous`) with « smooth » read as DEC-107 reads it for Cauchy-compact (`rim`, the `C¹` rim condition of `E0Surgery.IsE0C1SpacelikeCauchy.rim`, verbatim) — a question (OQ-142) |

## SCOPE (disclosed)

A definition and its comparison with `GX.IsE0CauchyComplete` only; nothing is assumed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0RegComplete

open E0 E0CBG E0Spear E0AbsMax

variable (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **A `C¹` spacelike complete Cauchy surface of an `𝔼₀`-manifold** (B21/btz l.227's
« Cauchy-complete »: « a smooth spacelike Cauchy-surface which is … metrically complete »): DEC-31/119's
`GX.IsE0CauchyComplete` data on `S` (spacelike Lipschitz in the flat charts of `Reg M`, complete
for the induced length extended across the BTZ lines, with metric topology finer than `M`'s),
and « smooth » read as DEC-107 reads it for Cauchy-compact: the trace of `S` on the shaft of every
spear chart meeting it along a continuous graph is a `C¹` circle
(`E0Surgery.IsE0C1SpacelikeCauchy.rim`, verbatim). -/
structure IsE0C1CompleteCauchy (S : Set M) : Prop where
  cauchy : (CE M).IsCauchySurface S
  reg : Causal.Flat.IsSpacelikeLipschitz 2 (E0Surgery.regSet M S)
  complete : CompleteSpace (Causal.Flat.LocalLengthSpace (e0SliceSys S))
  continuous : Continuous fun x : Causal.Flat.LocalLengthSpace (e0SliceSys S) =>
    ((Causal.Flat.LocalLengthSpace.toSpace x : S) : M)
  rim : ∀ (R v : ℝ) (W : Set E0Y) (ψ : E0Y → M) (τS : ℂ → ℝ), 0 < R → IsOpen W →
    E0Spear.spearY v R ⊆ W → E0Spear.IsE0Mor ψ W → InjOn ψ W →
    ContinuousOn τS (Metric.closedBall 0 R) →
    (∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS z) →
    (∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2)) →
    ContDiff ℝ 1 (E0Surgery.rimFun τS R)

/-- **Cauchy-complete `𝔼₀`-manifold** (btz l.227, read as `IsE0C1CompleteCauchy`). -/
def E0C1CauchyComplete : Prop := ∃ S : Set M, IsE0C1CompleteCauchy M S

variable {M}

omit [SecondCountableTopology M] in
/-- The reading is at least DEC-31/119's `GX.IsE0CauchyComplete`. -/
theorem IsE0C1CompleteCauchy.isE0CauchyComplete {S : Set M} (hS : IsE0C1CompleteCauchy M S) :
    IsE0CauchyComplete M :=
  ⟨S, hS.cauchy, hS.reg, hS.complete, hS.continuous⟩

end E0RegComplete

end GX
