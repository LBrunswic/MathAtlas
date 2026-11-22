import YamabeScaffold.Localisation

/-!
# The analytic theorems of § 6 on a compact manifold with boundary: Sobolev embedding, trace theorem, finite energy, and their bridges to the model

Labels (NOT marked: see SCOPE):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638): the Sobolev
  embedding the proof cites (l.637, `Hebey1996`), the finite energy of a `C¹` function, and
  lem:kobayashi (b) on a model reading the manifold (`Mfd.Reads.kobayashiB`).
* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the trace theorem
  of l.491 that its quotient uses, and the Sobolev embedding of l.720.

> by the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow L^{\pstar}(\Sigma)$ on compact manifolds
> with boundary \cite{Hebey1996}. (l.637)

> where the boundary norms are those of the trace of $u$, which is well defined in
> $L^{\psharp}(\partial\Sigma)$ by the trace theorem. (l.491)

## What is proved (no `sorry`, standard axioms)

* `Mfd.eLpNorm_gradNorm_lt_top`: a `C¹` function on a compact manifold has finite energy;
* `Mfd.sobolev_embedding`: `‖u‖_{L^{p*}(μ)} ≤ C (‖∇u‖_{L²(μ)} + ‖u‖_{L²(μ)})` for `u ∈ C¹(M)`;
* `Mfd.trace_embedding`: `‖u‖_{L^{p♯}(σ)} ≤ C (‖∇u‖_{L²(μ)} + ‖u‖_{L²(μ)})` for `u ∈ C¹(M)`;
* the bridges to a model reading `(M, g, μ, σ)`: `Mfd.Reads.sobolevIneq`, `Mfd.Reads.kobayashiB`,
  `Mfd.Reads.prop_nonpositive_csc` (prop:nonpositive's second sentence), `Mfd.Reads.traceIneq`.

The proofs: `gradNorm_bdd` (the metric read in a chart, `YamabeScaffold.Localisation`); a finite
smooth partition of unity subordinate to good chart neighbourhoods (`Mfd.assemble`), on each of
which `local_sobolev` and `local_trace` read the half-space inequalities of
`YamabeScaffold.HalfSpace` (the `C¹` reflection across `{z₀ = 0}`, then Mathlib's
Gagliardo–Nirenberg–Sobolev inequality and `trace_critical`) through the chart, the
comparability of `μ` with Lebesgue measure and of `σ` with `μH[N-1]`, and the comparison of `g`
with the chart's coordinates.

## Provenance of the statements

The seven statements are round 1's (T-yamabe-analysis), which stated them with `sorry` in
`YamabeScaffold.Sobolev` (the first two and three bridges) and `YamabeScaffold.Trace` (the trace
theorem and its bridge). Round 2 proved them here under primed names; the integration
(T-yamabe-integrate-r2) checked each primed type `Expr`-equal to its round-1 original (as AUDIT-2
had), then deleted the round-1 `sorry`s and gave the proofs the round-1 names, so that every use
(`YamabeScaffold.Rellich`, `YamabeScaffold.Compactness`, the curation) keeps its name and its
statement. The definitions they are stated with (`Mfd.gradNorm`, `Mfd.IsC1`, `Mfd.w12`,
`Mfd.IsLocallyLebesgue`, `Mfd.IsBoundaryMeasure`, `Mfd.Reads`) stay in `YamabeScaffold.Sobolev`
and `YamabeScaffold.Trace`, which this file imports.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian `N`-manifold with boundary, `N ≥ 3` | ✓ carried as in round 1 (OQ-93 (a)) |
| `vol_g`, the area of `∂Σ` | ⚠ read as in round 1: every `IsLocallyLebesgue` `μ`, every `IsBoundaryMeasure` `σ` (OQ-93 (a)) |
| `u ∈ W^{1,2}(Σ)` | ⚠ read as `C¹(M)` (OQ-93 (b)) |

## SCOPE (disclosed)

* Not here: `Mfd.rellich_kondrachov` (`YamabeScaffold.Rellich`) and `Mfd.trace_compact`
  (`YamabeScaffold.Trace`), the scaffold's two remaining `sorry`s; nothing in this file uses them.
* No label is marked while OQ-93 is open: the manifold theorems are proved under its readings
  (a), (b) above.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M]
variable [MeasurableSpace M]

/-- **A `C¹` function on a compact manifold has finite Dirichlet energy**: `|∇u|_g` is bounded
(`gradNorm_bdd`) and `μ` finite. -/
theorem eLpNorm_gradNorm_lt_top [BorelSpace M] [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} [IsFiniteMeasure μ] {u : M → ℝ} (hu : IsC1 N u) :
    eLpNorm (gradNorm g u) 2 μ < ⊤ := by
  obtain ⟨K, hK⟩ := gradNorm_bdd g hu
  refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := K) (ae_of_all _ fun x => ?_)) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (gradNorm_nonneg g u x)]
    exact hK x
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top _ _))
      ENNReal.ofReal_lt_top

variable [BorelSpace M]

/-- **The Sobolev embedding** `W^{1,2}(M) ↪ L^{p*}(M)` on a compact manifold with boundary
(Hebey1996; cited at l.637 and l.720): `‖u‖_{L^{p*}} ≤ C ‖u‖_{W^{1,2}}` for every `u ∈ C¹(M)`.
`local_sobolev` on good chart neighbourhoods, summed by `assemble`. -/
theorem sobolev_embedding (hN : 3 ≤ N) [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u →
      eLpNorm u (ENNReal.ofReal (pStar N)) μ ≤ C * w12 g μ u := by
  refine assemble g μ (ν := μ) ?_ (fun V => ∃ x₀ Cμ Cg, GoodChart g μ x₀ V Cμ Cg) ?_ ?_
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [two_le_pStar hN])
  · intro x₀
    obtain ⟨V, Cμ, Cg, hx, hG⟩ := exists_goodChart g hμ x₀
    exact ⟨V, hG.isOpen, hx, x₀, Cμ, Cg, hG⟩
  · rintro V ⟨x₀, Cμ, Cg, hG⟩ ρ hρ hρV hρ1
    exact local_sobolev hN hG hρ hρV hρ1

/-- **The trace theorem** (l.491): the trace `W^{1,2}(M) → L^{p♯}(∂M)` is bounded,
`‖u|_{∂M}‖_{L^{p♯}(σ)} ≤ C ‖u‖_{W^{1,2}(M)}` for every `u ∈ C¹(M)`. `local_trace` on good chart
neighbourhoods inside the neighbourhoods of `IsBoundaryMeasure`, summed by `assemble`. -/
theorem trace_embedding (hN : 3 ≤ N) [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u →
      eLpNorm u (ENNReal.ofReal (pSharp N)) σ ≤ C * w12 g μ u := by
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine assemble g μ (ν := σ) ?_ (fun V => ∃ x₀ Cμ Cg, ∃ Cσ : ℝ≥0, GoodChart g μ x₀ V Cμ Cg ∧
    Cσ ≠ 0 ∧ ∀ A ⊆ V, MeasurableSet A →
      σ A ≤ Cσ * Measure.hausdorffMeasure ((N : ℝ) - 1) (extChartAt (𝓡∂ N) x₀ '' A)) ?_ ?_
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [two_le_pSharp hN])
  · intro x₀
    obtain ⟨V, Cμ, Cg, hx, hG⟩ := exists_goodChart g hμ x₀
    obtain ⟨U, hU, C₀, hC₀⟩ := hσ.2 x₀
    refine ⟨V ∩ interior U, hG.isOpen.inter isOpen_interior,
      ⟨hx, mem_interior_iff_mem_nhds.mpr hU⟩, x₀, Cμ, Cg, max C₀ 1,
      hG.mono (hG.isOpen.inter isOpen_interior) inter_subset_left,
      (lt_of_lt_of_le one_pos (le_max_right _ _)).ne', fun A hA hAm => ?_⟩
    have hA' : A ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source := fun y hy =>
      ⟨interior_subset (hA hy).2, hG.subset_source (hA hy).1⟩
    have hle : (C₀ : ℝ≥0∞) ≤ (max C₀ 1 : ℝ≥0) := by exact_mod_cast le_max_left _ _
    exact (hC₀ A hA' hAm).trans (mul_le_mul_left hle _)
  · rintro V ⟨x₀, Cμ, Cg, Cσ, hG, hCσ, hσV⟩ ρ hρ hρV hρ1
    exact local_trace n hn hN hσ.1 hG hCσ hσV hρ hρV hρ1

/-! ## The bridges to the model (sorry-free) -/

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- The Sobolev inequality on a model reading a compact manifold with boundary, through
`sobolev_embedding`. -/
theorem sobolevIneq (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) : Mm.SobolevIneq gm := by
  obtain ⟨C, hC⟩ := sobolev_embedding hN g hμ
  refine ⟨2 * (C : ℝ) ^ 2, fun u => ?_⟩
  have hf := hr.c1 u
  have ha : eLpNorm (gradNorm g (Mm.val u)) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top g hf).ne
  have hb : eLpNorm (Mm.val u) 2 μ ≠ ⊤ := (memLp_of_isC1 hf 2).eLpNorm_ne_top
  have h := sq_le_of_le_mul_add ha hb (hC _ hf)
  unfold MeasuredModel.w12Sq
  rw [hr.dirichlet_eq u, hr.vol_eq]
  unfold normSq
  rw [ENNReal.ofReal_ofNat]
  exact h

/-- lem:kobayashi (b) on a model reading a compact manifold with boundary: the Sobolev inequality
is discharged by `sobolev_embedding`. -/
theorem kobayashiB (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) (hH : Mm.MinimalBoundary gc) : Mm.KobayashiB gc := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.kobayashiB_of_sobolev hN gc (by rw [hr.vol_eq]; exact hV) hr.hD hH
    (hr.sobolevIneq hN hμ)

/-- prop:nonpositive, second sentence, on a model reading a compact manifold with boundary, with
lem:kobayashi (b) discharged by the Sobolev embedding; `Y_[g](Σ) ≤ 0` (the first sentence) carried. -/
theorem prop_nonpositive_csc (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) (hH : Mm.MinimalBoundary gc) {c : ℝ} (hRc : ∀ x, gc.R x = c) (hY : Mm.Y gc ≤ 0) :
    (∀ x, gc.R x ≤ 0) ∧ Mm.EH gc = Mm.Y gc := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.prop_nonpositive_csc hN gc hr.hD hH hRc hY (hr.kobayashiB hN hμ hV hH)

/-- The trace theorem on a model reading a compact manifold with boundary, through
`trace_embedding`. -/
theorem traceIneq (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    [∀ j, IsFiniteMeasure (σ j)] (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) : Mm.TraceIneq gm := by
  choose C hC using fun j => trace_embedding hN g hμ (hσ j)
  refine ⟨2 * ∑ j, ((C j : ℝ)) ^ 2, fun u j => ?_⟩
  have hf := hr.c1 u
  have ha : eLpNorm (gradNorm g (Mm.val u)) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top g hf).ne
  have hb : eLpNorm (Mm.val u) 2 μ ≠ ⊤ := (memLp_of_isC1 hf 2).eLpNorm_ne_top
  have h := sq_le_of_le_mul_add ha hb (hC j _ hf)
  rw [hr.bvol_eq j, hr.tr_eq u]
  refine ⟨memLp_of_isC1 hf _, ?_⟩
  unfold MeasuredModel.w12Sq
  rw [hr.dirichlet_eq u, hr.vol_eq]
  unfold normSq
  rw [ENNReal.ofReal_ofNat]
  have hCj : ((C j : ℝ)) ^ 2 ≤ ∑ j, ((C j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((C j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hw : 0 ≤ (eLpNorm (gradNorm g (Mm.val u)) 2 μ).toReal ^ 2 +
      (eLpNorm (Mm.val u) 2 μ).toReal ^ 2 := by positivity
  nlinarith

end Reads

end Mfd

end Yamabe
