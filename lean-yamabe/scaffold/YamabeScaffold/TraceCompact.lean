import Yamabe.RellichManifold

/-!
# The compact trace into `L²(∂Σ)` on a compact manifold with boundary

Labels (NOT marked: stated with `sorry`):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the compact
  trace `W^{1,2}(Σ) → L²(∂Σ)` that its proof cites (l.720), stated on a compact Riemannian
  manifold with boundary.

> The trace operator $W^{1,2}(\Sigma)\to L^2(\partial\Sigma)$ is compact, so the traces converge
> to $c$ in $L^2(\partial\Sigma)$; [...] (l.720)

## The setting

As in `Yamabe.Trace`: `M` a compact smooth manifold with boundary modelled on
`EuclideanHalfSpace N`, `g` a smooth Riemannian metric, `μ` a locally-Lebesgue volume
(`Yamabe.Sobolev`), and `σ` a boundary measure, `Mfd.IsBoundaryMeasure N σ` (`Yamabe.Trace`).
`W^{1,2}(M)` is read through `C¹(M)`, normed by `Mfd.w12 g μ` (`Yamabe.Sobolev`). As `σ` is carried
by `∂M`, `eLpNorm (u - f) 2 σ` measures the trace of `u` on `∂M`.

## What is stated with `sorry`

`Mfd.trace_compact`, the one declaration of this file and the scaffold's one `sorry`; nothing
depends on it. Round 1 stated it in Trace.lean. T-yamabe-graduate-analysis moved it here unchanged
(statement, docstring and tagged SORRY comment word for word), so that the chain of `Yamabe.Trace`
could graduate to the strict library, and so that it sits downstream of `Mfd.rellich_kondrachov`
(`Yamabe.RellichManifold`, which this file imports), which its proof needs. The SORRY comment
predates the move: the module it names, « `YamabeScaffold.RellichManifold`, downstream of this
file », is now `Yamabe.RellichManifold`, upstream of this file. T-yamabe-trace-compact replaces the
`sorry` in place.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian with boundary | ✓ carried: `CompactSpace`, `T2Space`, smooth `g`, for every `N` with `NeZero N` (the paper's `N ≥ 3` is not asked); `μ` ⚠ read, as in `Yamabe.Sobolev` |
| the induced measure of `∂Σ` | ⚠ read: any `σ` with `IsBoundaryMeasure N σ` (a weakening: only an upper bound is asked) |
| `(u_k)` bounded in `W^{1,2}(Σ)` | ⚠ read: `u_k ∈ C¹(M)` with `w12 g μ (u k) ≤ K` |

## SCOPE (disclosed)

* The proof of lem:positivity needs only the continuity of the trace, not its compactness
  (`Yamabe.Trace`, SCOPE): `lem_positivity` (`Yamabe.Rellich`) uses only `TraceIneq`. The
  compactness the paper states at l.720 is this theorem, stated for completeness.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **The compact trace** (l.720): every sequence bounded in `W^{1,2}(M)` has a subsequence whose
traces converge in `L²(∂M)`. -/
theorem trace_compact [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ)
    (u : ℕ → M → ℝ) (hu : ∀ k, IsC1 N (u k)) (hb : ∃ K : ℝ≥0, ∀ k, w12 g μ (u k) ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : M → ℝ, MemLp f 2 σ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) 2 σ) atTop (𝓝 0) := by
  sorry -- SORRY(lem:positivity): needs `rellich_kondrachov` and the interpolation
  -- ‖u‖²_{L²(∂ℍ)} ≤ ε ‖∂_t u‖²_{L²(ℍ)} + C_ε ‖u‖²_{L²(ℍ)} (from the FTC estimate of
  -- `trace_halfLine`), localised by charts; Mathlib has neither. The scaffold proves the first
  -- (`YamabeScaffold.RellichManifold`, downstream of this file). Not used by lem_positivity.

end Mfd

end Yamabe
