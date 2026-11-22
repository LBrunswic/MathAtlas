import YamabeScaffold.Localisation

/-!
# The analytic theorems of § 6 on a compact manifold with boundary, under primed names

Labels (NOT marked: see SCOPE):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638): the Sobolev
  embedding the proof cites (l.637, `Hebey1996`) and the finite energy of a `C¹` function.
* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the trace theorem
  of l.491 that its quotient uses, and the Sobolev embedding of l.720.

> by the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow L^{\pstar}(\Sigma)$ on compact manifolds
> with boundary \cite{Hebey1996}. (l.637)

> where the boundary norms are those of the trace of $u$, which is well defined in
> $L^{\psharp}(\partial\Sigma)$ by the trace theorem. (l.491)

## The primed names (to rewire at integration)

Each theorem here has **exactly** the statement of the round-1 theorem of the same name without
the prime (same binders, same conclusion; checked by the `example`s at the end of the file, which
compare the two types by `rfl`), so that the round-1 `sorry` can be replaced by a call:

| round 1 (`sorry`) | here (proved) |
|---|---|
| `Mfd.eLpNorm_gradNorm_lt_top` (`YamabeScaffold.Sobolev`) | `Mfd.eLpNorm_gradNorm_lt_top'` |
| `Mfd.sobolev_embedding` (`YamabeScaffold.Sobolev`) | `Mfd.sobolev_embedding'` |
| `Mfd.trace_embedding` (`YamabeScaffold.Trace`) | `Mfd.trace_embedding'` |

The proofs: `gradNorm_bdd` (the metric read in a chart, `YamabeScaffold.Localisation`); a finite
smooth partition of unity subordinate to good chart neighbourhoods (`Mfd.assemble`), on each of
which `local_sobolev` and `local_trace` read the half-space inequalities of
`YamabeScaffold.HalfSpace` (the `C¹` reflection across `{z₀ = 0}`, then Mathlib's
Gagliardo–Nirenberg–Sobolev inequality and round 1's `trace_critical`) through the chart, the
comparability of `μ` with Lebesgue measure and of `σ` with `μH[N-1]`, and the comparison of `g`
with the chart's coordinates.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian `N`-manifold with boundary, `N ≥ 3` | ✓ carried as in round 1 (OQ-93 (a)) |
| `vol_g`, the area of `∂Σ` | ⚠ read as in round 1: every `IsLocallyLebesgue` `μ`, every `IsBoundaryMeasure` `σ` (OQ-93 (a)) |
| `u ∈ W^{1,2}(Σ)` | ⚠ read as `C¹(M)` (OQ-93 (b)) |

## SCOPE (disclosed)

* Not here: `Mfd.rellich_kondrachov` and `Mfd.trace_compact` (still `sorry` in round 1's files).
  `Mfd.const_of_tendsto` is false as stated (no measurability of the limit); its corrected form
  is `Mfd.const_of_tendsto_of_aestronglyMeasurable` (`YamabeScaffold.Compactness`).

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

/-- **A `C¹` function on a compact manifold has finite Dirichlet energy** (the round-1
`eLpNorm_gradNorm_lt_top`, same statement): `|∇u|_g` is bounded (`gradNorm_bdd`) and `μ` finite. -/
theorem eLpNorm_gradNorm_lt_top' [BorelSpace M] [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} [IsFiniteMeasure μ] {u : M → ℝ} (hu : IsC1 N u) :
    eLpNorm (gradNorm g u) 2 μ < ⊤ := by
  obtain ⟨K, hK⟩ := gradNorm_bdd g hu
  refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := K) (ae_of_all _ fun x => ?_)) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (gradNorm_nonneg g u x)]
    exact hK x
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top _ _))
      ENNReal.ofReal_lt_top

variable [BorelSpace M]

/-- **The Sobolev embedding** `W^{1,2}(M) ↪ L^{p*}(M)` (the round-1 `sobolev_embedding`, same
statement). -/
theorem sobolev_embedding' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
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

/-- **The trace theorem** (the round-1 `trace_embedding`, same statement). -/
theorem trace_embedding' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
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

/-! ## The round-1 bridges to the model, rewired to the primed theorems (sorry-free) -/

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- The round-1 `Mfd.Reads.sobolevIneq`, same statement, through `sobolev_embedding'`. -/
theorem sobolevIneq' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) : Mm.SobolevIneq gm := by
  obtain ⟨C, hC⟩ := sobolev_embedding' hN g hμ
  refine ⟨2 * (C : ℝ) ^ 2, fun u => ?_⟩
  have hf := hr.c1 u
  have ha : eLpNorm (gradNorm g (Mm.val u)) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top' g hf).ne
  have hb : eLpNorm (Mm.val u) 2 μ ≠ ⊤ := (memLp_of_isC1 hf 2).eLpNorm_ne_top
  have h := sq_le_of_le_mul_add ha hb (hC _ hf)
  unfold MeasuredModel.w12Sq
  rw [hr.dirichlet_eq u, hr.vol_eq]
  unfold normSq
  rw [ENNReal.ofReal_ofNat]
  exact h

/-- The round-1 `Mfd.Reads.kobayashiB` (lem:kobayashi (b) on a model reading `M`), same
statement, sorry-free. -/
theorem kobayashiB' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) (hH : Mm.MinimalBoundary gc) : Mm.KobayashiB gc := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.kobayashiB_of_sobolev hN gc (by rw [hr.vol_eq]; exact hV) hr.hD hH
    (hr.sobolevIneq' hN hμ)

/-- The round-1 `Mfd.Reads.prop_nonpositive_csc`, same statement, sorry-free. -/
theorem prop_nonpositive_csc' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hV : μ ≠ 0) (hH : Mm.MinimalBoundary gc) {c : ℝ} (hRc : ∀ x, gc.R x = c) (hY : Mm.Y gc ≤ 0) :
    (∀ x, gc.R x ≤ 0) ∧ Mm.EH gc = Mm.Y gc := by
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.prop_nonpositive_csc hN gc hr.hD hH hRc hY (hr.kobayashiB' hN hμ hV hH)

/-- The round-1 `Mfd.Reads.traceIneq`, same statement, through `trace_embedding'`. -/
theorem traceIneq' (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [IsFiniteMeasure μ]
    [∀ j, IsFiniteMeasure (σ j)] (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) : Mm.TraceIneq gm := by
  choose C hC using fun j => trace_embedding' hN g hμ (hσ j)
  refine ⟨2 * ∑ j, ((C j : ℝ)) ^ 2, fun u j => ?_⟩
  have hf := hr.c1 u
  have ha : eLpNorm (gradNorm g (Mm.val u)) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top' g hf).ne
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

/-! ## The primed statements are the round-1 statements (checked by `rfl`) -/

universe u v

example : type_of% @eLpNorm_gradNorm_lt_top.{u} = type_of% @eLpNorm_gradNorm_lt_top'.{u} := rfl
example : type_of% @sobolev_embedding.{u} = type_of% @sobolev_embedding'.{u} := rfl
example : type_of% @trace_embedding.{u} = type_of% @trace_embedding'.{u} := rfl
example : type_of% @Reads.sobolevIneq.{u, v} = type_of% @Reads.sobolevIneq'.{u, v} := rfl
example : type_of% @Reads.kobayashiB.{u, v} = type_of% @Reads.kobayashiB'.{u, v} := rfl
example : type_of% @Reads.prop_nonpositive_csc.{u, v} = type_of% @Reads.prop_nonpositive_csc'.{u, v} :=
  rfl
example : type_of% @Reads.traceIneq.{u, v} = type_of% @Reads.traceIneq'.{u, v} := rfl

end Mfd

end Yamabe
