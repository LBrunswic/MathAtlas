import Mathlib

/-!
# The functional-analytic half of Rellich–Kondrachov: total boundedness by finite-rank approximation

Labels (NOT marked: a step of the proof, see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the
  functional-analytic half of the step « by the Rellich--Kondrachov theorem a subsequence
  converges in $L^2(\Sigma)$ » (l.720). In `L^p` (`1 ≤ p`), a set that is, for every `ε > 0`,
  within `ε` of the image of a bounded set under a finite-rank continuous linear map is totally
  bounded; hence a sequence in it has a subsequence converging in `L^p` to a `MemLp` limit, in the
  `eLpNorm` form of the conclusion of `Mfd.rellich_kondrachov` (`YamabeScaffold.RellichManifold`).

> By \eqref{eq:hoelder}, $(u_k)$ is bounded in $W^{1,2}(\Sigma)$, so by the Rellich--Kondrachov
> theorem a subsequence converges in $L^2(\Sigma)$ and weakly in $W^{1,2}(\Sigma)$ to some
> $u_\infty$ […] (l.720)

## What is proved (sorry-free, standard axioms)

* `totallyBounded_of_forall_approx` (pseudometric spaces): a set within every `ε > 0` of a
  totally bounded set is totally bounded;
* `exists_subseq_tendsto_of_totallyBounded`: in a complete space, a sequence with totally
  bounded range has a convergent subsequence;
* `totallyBounded_of_subset_submodule`, `totallyBounded_image_of_finiteDimensional_range`
  (real normed spaces): a bounded subset of a finite-dimensional subspace, and the image of a
  bounded set under a continuous linear map of finite rank, are totally bounded;
* `totallyBounded_of_approx_finiteRank` — **the criterion** of the target: a set that is, for
  every `ε > 0`, within `ε` of `T '' B`, `T` a continuous linear map of finite rank and `B`
  bounded, is totally bounded; `isCompact_closure_of_approx_finiteRank` (compact closure in a
  complete space); their `L^p` readings `totallyBounded_Lp_of_approx_finiteRank` and
  `isCompact_closure_Lp_of_approx_finiteRank`;
* `totallyBounded_of_isBounded_of_approx`, `totallyBounded_iff_isBounded_and_approx`: the
  equivalent form « bounded, and within every `ε` of a finite-dimensional subspace », which is a
  characterisation of total boundedness (the criterion is sharp, and its hypotheses are met by
  every totally bounded set);
* on functions `α → F` (`F` a real Banach space, `F = ℝ` included), with
  `coeFn_finsetSum_smul` and `dist_toLp_finsetSum_le` (finite combinations of classes):
  `exists_subseq_tendsto_eLpNorm_of_totallyBounded`,
  `exists_subseq_tendsto_eLpNorm_of_approx` (bounded in `L^p`, and for every `ε` within `ε` of
  the span of finitely many `L^p` functions) and `exists_subseq_tendsto_eLpNorm_of_approx_bdd`
  (for every `ε`, within `ε` of combinations of finitely many `L^p` functions with bounded
  coefficients): a subsequence and `f` with `MemLp f p μ` and `eLpNorm (u (φ k) - f) p μ → 0`;
  `approx_of_totallyBounded`, the converse (the function-level hypotheses hold for every
  sequence whose classes are totally bounded); for `p = 2`, `F = ℝ`,
  `exists_subseq_tendsto_eLpNorm_two`, whose conclusion is that of `Mfd.rellich_kondrachov`
  (checked out of tree by `type_of%` against round 1's statement, then in `YamabeScaffold.Rellich`;
  the theorem is now proved in `YamabeScaffold.RellichManifold`, which concludes with this one).

## Hypothesis checklist

| hypothesis (the target's, and l.720) | here |
|---|---|
| `Lp ℝ p μ`, `1 ≤ p < ∞` | ⚠ weakened: `Lp F p μ`, `F` real normed (complete for convergence), `1 ≤ p ≤ ∞` |
| `u_k` functions in `L^p` | ⚠ weakened: `AEStronglyMeasurable (u k) μ`; `MemLp` is derived |
| `(u_k)` bounded in `W^{1,2}(Σ)` (l.720) | not here: the approximation hypothesis, for the manifold half to derive |

## SCOPE (disclosed)

* This file is the functional-analytic half of `Mfd.rellich_kondrachov` only. It does not prove
  Rellich–Kondrachov on a manifold: the manifold half (the chart-level assembly of
  `Half.cell_approx` with the partition of unity of `Mfd.assemble`, the finiteness of a
  locally-Lebesgue `μ`) is the scaffold's `YamabeScaffold.RellichManifold`, which concludes with
  `exists_subseq_tendsto_eLpNorm_two`, the arbitrary-coefficient form, so the bound on the cell
  averages that the `_bdd` form asks is not needed. `lem:positivity` is not certified here, and no
  label is marked while OQ-93 is open. It imports Mathlib only.
* The approximants of the function-level theorems are finite sums `∑ i ∈ s, c i • g i` over a
  `Finset` of an arbitrary index type `β` (for the manifold half: charts × grid cells), with the
  functions `g i` in `L^p`; the `(u_k)` bound of the bounded form is in `L^p`, not in `W^{1,2}`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set Metric Bornology
open scoped ENNReal NNReal

noncomputable section

namespace Yamabe

universe u

/-! ## 1. Total boundedness by approximation, in a pseudometric space -/

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- A set that is, for every `ε > 0`, within `ε` of a totally bounded set is totally bounded. -/
theorem totallyBounded_of_forall_approx {S : Set X}
    (h : ∀ ε > (0 : ℝ), ∃ T : Set X, TotallyBounded T ∧ ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ ε) :
    TotallyBounded S := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hTt⟩ := Metric.totallyBounded_iff.1 hT (ε / 2) (half_pos hε)
  refine ⟨t, ht, fun x hx => ?_⟩
  obtain ⟨y, hyT, hxy⟩ := hST x hx
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hTt hyT)
  refine mem_iUnion₂.2 ⟨z, hz, ?_⟩
  rw [mem_ball] at hyz ⊢
  calc dist x z ≤ dist x y + dist y z := dist_triangle x y z
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hxy hyz
    _ = ε := add_halves ε

/-- In a complete space, a sequence with totally bounded range has a convergent subsequence
(its closure is compact: `TotallyBounded.closure`, `TotallyBounded.isCompact_of_isClosed`,
`IsCompact.tendsto_subseq`). -/
theorem exists_subseq_tendsto_of_totallyBounded [CompleteSpace X] {v : ℕ → X}
    (h : TotallyBounded (range v)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X, Tendsto (v ∘ φ) atTop (𝓝 f) := by
  have hK : IsCompact (closure (range v)) := h.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨f, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => subset_closure (mem_range_self n)
  exact ⟨φ, hφ, f, hlim⟩

end PseudoMetric

/-! ## 2. Finite rank, in a real normed space -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded subset of a finite-dimensional subspace is totally bounded (it lies in the image of
a closed ball of the subspace, compact since the subspace is a proper space). -/
theorem totallyBounded_of_subset_submodule {V : Submodule ℝ E} [FiniteDimensional ℝ V]
    {B : Set E} (hBV : B ⊆ V) (hB : IsBounded B) : TotallyBounded B := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  have hK : IsCompact ((Subtype.val : V → E) '' closedBall (0 : V) R) :=
    (isCompact_closedBall (0 : V) R).image continuous_subtype_val
  refine hK.totallyBounded.subset fun x hx => (mem_image _ _ _).2 ⟨⟨x, hBV hx⟩, ?_, rfl⟩
  have := hR hx
  rw [mem_closedBall, dist_zero_right] at this ⊢
  exact this

/-- The image of a bounded set under a continuous linear map of finite rank is totally
bounded. -/
theorem totallyBounded_image_of_finiteDimensional_range {Y : Type*} [SeminormedAddCommGroup Y]
    [NormedSpace ℝ Y] (T : Y →L[ℝ] E) [FiniteDimensional ℝ (LinearMap.range T.toLinearMap)]
    {B : Set Y} (hB : IsBounded B) : TotallyBounded (T '' B) := by
  refine totallyBounded_of_subset_submodule (V := LinearMap.range T.toLinearMap) ?_
    (T.lipschitz.isBounded_image hB)
  rintro _ ⟨b, -, rfl⟩
  exact LinearMap.mem_range_self T.toLinearMap b

/-- **The criterion.** A set that is, for every `ε > 0`, within `ε` of the image of a bounded set
under a continuous linear map of finite rank is totally bounded. -/
theorem totallyBounded_of_approx_finiteRank {S : Set E}
    (h : ∀ ε > (0 : ℝ), ∃ (Y : Type u) (_ : SeminormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
      (T : Y →L[ℝ] E) (B : Set Y), FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        IsBounded B ∧ ∀ x ∈ S, ∃ b ∈ B, dist x (T b) ≤ ε) :
    TotallyBounded S := by
  refine totallyBounded_of_forall_approx fun ε hε => ?_
  obtain ⟨Y, _, _, T, B, hT, hB, hS⟩ := h ε hε
  refine ⟨T '' B, totallyBounded_image_of_finiteDimensional_range T hB, fun x hx => ?_⟩
  obtain ⟨b, hb, hxb⟩ := hS x hx
  exact ⟨T b, mem_image_of_mem T hb, hxb⟩

/-- In a complete space, a set as in the criterion has compact closure. -/
theorem isCompact_closure_of_approx_finiteRank [CompleteSpace E] {S : Set E}
    (h : ∀ ε > (0 : ℝ), ∃ (Y : Type u) (_ : SeminormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
      (T : Y →L[ℝ] E) (B : Set Y), FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        IsBounded B ∧ ∀ x ∈ S, ∃ b ∈ B, dist x (T b) ≤ ε) :
    IsCompact (closure S) :=
  (totallyBounded_of_approx_finiteRank h).closure.isCompact_of_isClosed isClosed_closure

/-- The equivalent form: a **bounded** set that is, for every `ε > 0`, within `ε` of a
finite-dimensional subspace is totally bounded. -/
theorem totallyBounded_of_isBounded_of_approx {S : Set E} (hS : IsBounded S)
    (h : ∀ ε > (0 : ℝ), ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧
      ∀ x ∈ S, ∃ y ∈ V, dist x y ≤ ε) :
    TotallyBounded S := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine totallyBounded_of_forall_approx fun ε hε => ?_
  obtain ⟨V, hV, hSV⟩ := h ε hε
  refine ⟨(V : Set E) ∩ closedBall 0 (R + ε),
    totallyBounded_of_subset_submodule inter_subset_left
      (isBounded_closedBall.subset inter_subset_right), fun x hx => ?_⟩
  obtain ⟨y, hyV, hxy⟩ := hSV x hx
  refine ⟨y, ⟨hyV, ?_⟩, hxy⟩
  have hx' := hR hx
  rw [mem_closedBall, dist_zero_right] at hx' ⊢
  calc ‖y‖ ≤ ‖x‖ + dist x y := by
        rw [dist_comm, dist_eq_norm]
        have := norm_le_norm_add_norm_sub' y x
        linarith [norm_sub_rev y x]
    _ ≤ R + ε := add_le_add hx' hxy

/-- The criterion is a characterisation: a set is totally bounded iff it is bounded and, for
every `ε > 0`, within `ε` of a finite-dimensional subspace. Its hypotheses are therefore met by
every totally bounded set. -/
theorem totallyBounded_iff_isBounded_and_approx {S : Set E} :
    TotallyBounded S ↔ IsBounded S ∧ ∀ ε > (0 : ℝ), ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧
      ∀ x ∈ S, ∃ y ∈ V, dist x y ≤ ε := by
  refine ⟨fun h => ⟨h.isBounded, fun ε hε => ?_⟩,
    fun h => totallyBounded_of_isBounded_of_approx h.1 h.2⟩
  obtain ⟨t, ht, hSt⟩ := Metric.totallyBounded_iff.1 h ε hε
  refine ⟨Submodule.span ℝ t, FiniteDimensional.span_of_finite ℝ ht, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hSt hx)
  exact ⟨y, Submodule.subset_span hy, (mem_ball.1 hxy).le⟩

end Normed

/-! ## 3. In `L^p` -/

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The criterion in `L^p`** (the target's statement, for `1 ≤ p ≤ ∞` and any real normed
`F`; `F = ℝ` is the target's `Lp ℝ p μ`): a set of `Lp F p μ` that is, for every `ε > 0`, within
`ε` of the image of a bounded set under a continuous linear map of finite rank is totally
bounded. -/
theorem totallyBounded_Lp_of_approx_finiteRank {S : Set (Lp F p μ)}
    (h : ∀ ε > (0 : ℝ), ∃ (Y : Type u) (_ : SeminormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
      (T : Y →L[ℝ] Lp F p μ) (B : Set Y), FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        IsBounded B ∧ ∀ x ∈ S, ∃ b ∈ B, dist x (T b) ≤ ε) :
    TotallyBounded S :=
  totallyBounded_of_approx_finiteRank h

/-- In `Lp F p μ` with `F` complete, a set as in the criterion has compact closure. -/
theorem isCompact_closure_Lp_of_approx_finiteRank [CompleteSpace F] {S : Set (Lp F p μ)}
    (h : ∀ ε > (0 : ℝ), ∃ (Y : Type u) (_ : SeminormedAddCommGroup Y) (_ : NormedSpace ℝ Y)
      (T : Y →L[ℝ] Lp F p μ) (B : Set Y), FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        IsBounded B ∧ ∀ x ∈ S, ∃ b ∈ B, dist x (T b) ≤ ε) :
    IsCompact (closure S) :=
  isCompact_closure_of_approx_finiteRank h

omit [Fact (1 ≤ p)] in
/-- The class of a finite combination: `⇑(∑ i ∈ t, c i • G i) =ᵐ ∑ i ∈ t, c i • g i` when each
`G i` is the class of `g i`. -/
theorem coeFn_finsetSum_smul {ι : Type*} (t : Finset ι) (c : ι → ℝ) (G : ι → Lp F p μ)
    (g : ι → α → F) (hG : ∀ i ∈ t, ⇑(G i) =ᵐ[μ] g i) :
    ⇑(∑ i ∈ t, c i • G i) =ᵐ[μ] ∑ i ∈ t, c i • g i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact Lp.coeFn_zero F p μ
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := Lp.coeFn_add (c a • G a) (∑ i ∈ t, c i • G i)
    have h2 := Lp.coeFn_smul (c a) (G a)
    have h3 := hG a (Finset.mem_insert_self a t)
    have h4 := ih fun i hi => hG i (Finset.mem_insert_of_mem hi)
    filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.add_apply, hx2, Pi.smul_apply, hx3, hx4, Pi.add_apply, Pi.smul_apply]

omit [Fact (1 ≤ p)] in
/-- An `eLpNorm` bound on `v - ∑ i ∈ s, c i • g i` is a distance bound in `Lp` between the class
of `v` and the combination of the classes of the `g i`. -/
theorem dist_toLp_finsetSum_le {β : Type*} {v : α → F} (hv : MemLp v p μ) (s : Finset β)
    {g : β → α → F} (hg : ∀ i ∈ s, MemLp (g i) p μ) (c : β → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : eLpNorm (v - ∑ i ∈ s, c i • g i) p μ ≤ ENNReal.ofReal ε) :
    dist (hv.toLp v) (∑ i : s, c i • (hg i i.2).toLp (g i)) ≤ ε := by
  have hsum : ⇑(∑ i : s, c i • (hg i i.2).toLp (g i)) =ᵐ[μ] ∑ i ∈ s, c i • g i := by
    have := coeFn_finsetSum_smul (Finset.univ : Finset s) (fun i => c i)
      (fun i => (hg i i.2).toLp (g i)) (fun i => g i) (fun i _ => (hg i i.2).coeFn_toLp)
    rwa [Finset.sum_coe_sort s (fun i => c i • g i)] at this
  rw [Lp.dist_def]
  refine ENNReal.toReal_le_of_le_ofReal hε ?_
  rw [eLpNorm_congr_ae (hv.coeFn_toLp.sub hsum)]
  exact h

omit [NormedSpace ℝ F] in
/-- From a totally bounded sequence of classes to the `eLpNorm` form: a subsequence converges in
`L^p` to a `MemLp` function (a representative of the limit class). -/
theorem exists_subseq_tendsto_eLpNorm_of_totallyBounded [CompleteSpace F] (u : ℕ → α → F)
    (hu : ∀ k, MemLp (u k) p μ) (h : TotallyBounded (range fun k => (hu k).toLp (u k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : α → F, MemLp f p μ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) p μ) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, f, hf⟩ := exists_subseq_tendsto_of_totallyBounded h
  refine ⟨φ, hφ, f, Lp.memLp f, ?_⟩
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).1 hf).congr fun k => eLpNorm_congr_ae ?_
  exact (hu (φ k)).coeFn_toLp.sub EventuallyEq.rfl

/-- **The criterion on functions, bounded form.** A sequence bounded in `L^p` which is, for every
`ε > 0`, within `ε` in `L^p` of the span of finitely many `L^p` functions has a subsequence
converging in `L^p` to a `MemLp` function. -/
theorem exists_subseq_tendsto_eLpNorm_of_approx [CompleteSpace F] {β : Type*} (u : ℕ → α → F)
    (hu : ∀ k, AEStronglyMeasurable (u k) μ) (hb : ∃ K : ℝ≥0, ∀ k, eLpNorm (u k) p μ ≤ K)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset β) (g : β → α → F), (∀ i ∈ s, MemLp (g i) p μ) ∧
      ∀ k, ∃ c : β → ℝ, eLpNorm (u k - ∑ i ∈ s, c i • g i) p μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : α → F, MemLp f p μ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) p μ) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hb
  have hu' : ∀ k, MemLp (u k) p μ := fun k => ⟨hu k, (hK k).trans_lt ENNReal.coe_lt_top⟩
  refine exists_subseq_tendsto_eLpNorm_of_totallyBounded u hu' ?_
  refine totallyBounded_of_isBounded_of_approx ?_ fun ε hε => ?_
  · refine isBounded_iff_forall_norm_le.2 ⟨K, ?_⟩
    rintro _ ⟨k, rfl⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal K.coe_nonneg (by simpa using hK k)
  · obtain ⟨s, g, hg, hc⟩ := happrox ε hε
    refine ⟨Submodule.span ℝ (range fun i : s => (hg i i.2).toLp (g i)),
      FiniteDimensional.span_of_finite ℝ (finite_range _), ?_⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hck⟩ := hc k
    exact ⟨_, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)),
      dist_toLp_finsetSum_le (hu' k) s hg c hε.le hck⟩

/-- **The criterion on functions, finite-rank form** (the target's statement read on functions).
A sequence which is, for every `ε > 0`, within `ε` in `L^p` of combinations of finitely many `L^p`
functions with coefficients bounded by a constant (the image of a bounded set of coefficients
under the finite-rank map `c ↦ ∑ i ∈ s, c i • g i`) has a subsequence converging in `L^p` to a
`MemLp` function. -/
theorem exists_subseq_tendsto_eLpNorm_of_approx_bdd [CompleteSpace F] {β : Type*}
    (u : ℕ → α → F) (hu : ∀ k, AEStronglyMeasurable (u k) μ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset β) (g : β → α → F), (∀ i ∈ s, MemLp (g i) p μ) ∧
      ∃ K : ℝ, ∀ k, ∃ c : β → ℝ, (∀ i ∈ s, |c i| ≤ K) ∧
        eLpNorm (u k - ∑ i ∈ s, c i • g i) p μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : α → F, MemLp f p μ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) p μ) atTop (𝓝 0) := by
  have hu' : ∀ k, MemLp (u k) p μ := by
    intro k
    obtain ⟨s, g, hg, K, hc⟩ := happrox 1 one_pos
    obtain ⟨c, -, hck⟩ := hc k
    have hsum : MemLp (∑ i ∈ s, c i • g i) p μ :=
      memLp_finsetSum' s fun i hi => (hg i hi).const_smul (c i)
    have hd : MemLp (u k - ∑ i ∈ s, c i • g i) p μ :=
      ⟨(hu k).sub hsum.1, hck.trans_lt ENNReal.ofReal_lt_top⟩
    simpa using hd.add hsum
  refine exists_subseq_tendsto_eLpNorm_of_totallyBounded u hu' ?_
  refine totallyBounded_of_approx_finiteRank fun ε hε => ?_
  obtain ⟨s, g, hg, K, hc⟩ := happrox ε hε
  let T : (s → ℝ) →L[ℝ] Lp F p μ := LinearMap.toContinuousLinearMap
    (Fintype.linearCombination ℝ fun i : s => (hg i i.2).toLp (g i))
  refine ⟨s → ℝ, inferInstance, inferInstance, T, {c | ∀ i, |c i| ≤ K}, inferInstance, ?_, ?_⟩
  · refine (isBounded_closedBall (x := (0 : s → ℝ)) (r := |K|)).subset fun c hc => ?_
    rw [mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (abs_nonneg K)).2 fun i =>
      (Real.norm_eq_abs _).trans_le ((hc i).trans (le_abs_self K))
  · rintro _ ⟨k, rfl⟩
    obtain ⟨c, hcK, hck⟩ := hc k
    refine ⟨fun i => c i, fun i => hcK i i.2, ?_⟩
    have hT : T (fun i => c i) = ∑ i : s, c i • (hg i i.2).toLp (g i) := rfl
    rw [hT]
    exact dist_toLp_finsetSum_le (hu' k) s hg c hε.le hck

/-- The function-level hypotheses of `exists_subseq_tendsto_eLpNorm_of_approx` are met by every
sequence whose classes form a totally bounded set (index type `Lp F p μ`, the functions `g` the
representatives of a finite `ε`-net): the function-level criterion is a characterisation too, and
its hypotheses are not vacuous. -/
theorem approx_of_totallyBounded (u : ℕ → α → F) (hu : ∀ k, MemLp (u k) p μ)
    (h : TotallyBounded (range fun k => (hu k).toLp (u k))) :
    (∃ K : ℝ≥0, ∀ k, eLpNorm (u k) p μ ≤ K) ∧
      ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Lp F p μ)) (g : Lp F p μ → α → F),
        (∀ i ∈ s, MemLp (g i) p μ) ∧
          ∀ k, ∃ c : Lp F p μ → ℝ, eLpNorm (u k - ∑ i ∈ s, c i • g i) p μ ≤ ENNReal.ofReal ε := by
  classical
  refine ⟨?_, fun ε hε => ?_⟩
  · obtain ⟨R, hR⟩ := h.isBounded.subset_closedBall 0
    refine ⟨R.toNNReal, fun k => ?_⟩
    have hk := hR (mem_range_self k)
    rw [mem_closedBall, dist_zero_right, Lp.norm_toLp] at hk
    rw [← ENNReal.ofReal_toReal (hu k).2.ne]
    exact ENNReal.ofReal_le_ofReal hk
  · obtain ⟨t, ht, hSt⟩ := Metric.totallyBounded_iff.1 h ε hε
    refine ⟨ht.toFinset, fun x => ⇑x, fun i _ => Lp.memLp i, fun k => ?_⟩
    obtain ⟨y, hy, hky⟩ := mem_iUnion₂.1 (hSt (mem_range_self k))
    refine ⟨fun i => if i = y then 1 else 0, ?_⟩
    have hsum : ∑ i ∈ ht.toFinset, (if i = y then (1 : ℝ) else 0) • (⇑i : α → F) = ⇑y := by
      simp [ite_smul, hy]
    rw [hsum]
    have he : edist ((hu k).toLp (u k)) y = eLpNorm (u k - ⇑y) p μ := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hu k).coeFn_toLp.sub EventuallyEq.rfl)
    rw [← he, edist_dist]
    exact ENNReal.ofReal_le_ofReal (mem_ball.1 hky).le

end Lp

/-! ## 4. The shape of `Mfd.rellich_kondrachov` -/

/-- For `p = 2` and real functions, the conclusion is, word for word, that of
`Mfd.rellich_kondrachov` (`YamabeScaffold.RellichManifold`, whose proof ends with this theorem). -/
theorem exists_subseq_tendsto_eLpNorm_two {M β : Type*} [MeasurableSpace M] {μ : Measure M}
    (u : ℕ → M → ℝ) (hu : ∀ k, AEStronglyMeasurable (u k) μ)
    (hb : ∃ K : ℝ≥0, ∀ k, eLpNorm (u k) 2 μ ≤ K)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (s : Finset β) (g : β → M → ℝ), (∀ i ∈ s, MemLp (g i) 2 μ) ∧
      ∀ k, ∃ c : β → ℝ, eLpNorm (u k - ∑ i ∈ s, c i • g i) 2 μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : M → ℝ, MemLp f 2 μ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) 2 μ) atTop (𝓝 0) :=
  exists_subseq_tendsto_eLpNorm_of_approx u hu hb happrox

end Yamabe
