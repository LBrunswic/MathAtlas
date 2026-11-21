import Causal.CurvesExtend
import Causal.Minkowski

/-!
# Curves extend on static spacetimes and on Minkowski space

No label is marked. The model section of `Causal.CurvesExtend`, moved here verbatim with the same
full names (T-abs-hoist-time-function), so that `Causal.CurvesExtend` imports no model: the general
theorem `Causality.curvesExtend_of_timeFunction` (any causality with a continuous time function
strictly increasing along `≤_M`) applied to the time coordinate of a static spacetime `ℝ × X`
(`Causal.Static`) and of Minkowski space (`Causal.Minkowski`). This module is a model module
(`Causal.Model.*`): a layer-1 module never imports it. Barbot's sentence it instantiates, unmarked
(Barbot's GH is not ETT's, `docs/BARBOT.md` §2):

> Moreover, it is required that any nonspacelike curve in $M$ can be extended to another one such
> that the restriction of $t$ on this extended curve is a diffeomorphism onto the entire $t(M)$.
> (`GHFspace.tex:502–504`, item [2.GH] of §2)

Where Minkowski space appears, Barbot's `𝐌ⁿ` (total dimension `n`) is the library's
`minkowski d` on `Minkowski d = ℝ × EuclideanSpace ℝ (Fin d)`, with **`n = d + 1`**.

## What is proved

* `staticCausality.fst_lt_of_le`: on `ℝ × X` the time coordinate is strictly increasing along
  `≤_M`.
* **Instances** of `CurvesExtend`: `staticCausality.curvesExtend` for `ℝ × X`, `X` **any** geodesic
  metric space (complete, proper or neither: time is the time function), and
  `minkowski_curvesExtend`; the parametrised form
  `staticCausality.exists_inextensible_graph_of_causalCurveIn` (time is the parameter of the
  inextensible curve).
* **Consequences**: Cauchy surfaces are acausal — `staticCausality.isAcausal_of_isCauchySurface`,
  `minkowski_isAcausal_of_isCauchySurface`.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| a time function `t` (Barbot l.498–500) | ✓ the time coordinate `Prod.fst`, continuous and strictly increasing along `≤_M` |
| static spacetime `ℝ × X` | ✓ `X` any geodesic metric space; completeness and properness not used |

## SCOPE (disclosed)

* Moved, not restated (T-abs-hoist-time-function, 2026-11-21): the six declarations were the
  section "Static spacetimes and Minkowski space" of `Causal.CurvesExtend`, verbatim; that module
  keeps the model-free theory (time graphs, `exists_inextensible_of_timeFunction`,
  `curvesExtend_of_timeFunction`, `Causality.HasTimeFunction`, the timelike-line witnesses). Its
  former users that name one of these six import this module.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set TopologicalSpace Topology Filter Function MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ### Static spacetimes and Minkowski space -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

/-- On a static spacetime the time coordinate is strictly increasing along `≤_M`. -/
theorem fst_lt_of_le {p q : ℝ × X} (h : (staticCausality X).le ⊤ p q) (hne : p ≠ q) :
    p.1 < q.1 := by
  have h' := le_top_iff.1 h
  refine lt_of_le_of_ne (by linarith [dist_nonneg (x := p.2) (y := q.2)]) fun e => hne ?_
  exact staticLe.eq_of_fst_eq h e

/-- **`CurvesExtend` on every static spacetime `ℝ × X`**, `X` any geodesic metric space —
complete or not. -/
theorem curvesExtend : (staticCausality X).CurvesExtend :=
  Causality.curvesExtend_of_timeFunction continuous_fst fun _ _ h hne => fst_lt_of_le h hne

/-- On a static spacetime, every causal curve over an interval lies on an inextensible curve
along which time is the parameter. -/
theorem exists_inextensible_graph_of_causalCurveIn {I : Set ℝ} {c : ℝ → ℝ × X}
    {W : Opens (ℝ × X)} (hc : (staticCausality X).CausalCurveIn W I c) :
    ∃ (J : Set ℝ) (γ : ℝ → ℝ × X), (staticCausality X).Inextensible W J γ ∧ c '' I ⊆ γ '' J ∧
      ∀ τ ∈ J, (γ τ).1 = τ :=
  Causality.exists_inextensible_of_timeFunction continuous_fst
    (fun _ _ h hne => fst_lt_of_le h hne) hc

/-- **A Cauchy surface of a static spacetime is acausal.** -/
theorem isAcausal_of_isCauchySurface {S : Set (ℝ × X)}
    (hS : (staticCausality X).IsCauchySurface S) : (staticCausality X).IsAcausal S :=
  hS.isAcausal causallyArcConnected curvesExtend

end staticCausality

/-- **`CurvesExtend` on Minkowski space** `minkowski d = ℝ^{1,d}`, Barbot's `𝐌ⁿ` with
`n = d + 1`. -/
theorem minkowski_curvesExtend (d : ℕ) : (minkowski d).CurvesExtend :=
  staticCausality.curvesExtend

/-- **A Cauchy surface of Minkowski space is acausal.** -/
theorem minkowski_isAcausal_of_isCauchySurface {d : ℕ} {S : Set (Minkowski d)}
    (hS : (minkowski d).IsCauchySurface S) : (minkowski d).IsAcausal S :=
  staticCausality.isAcausal_of_isCauchySurface hS

end Causal
