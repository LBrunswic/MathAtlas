import Causal.FlrwType
import Causal.InextensiblePiece
import Causal.Model.MinkowskiFutureOneConnected

/-!
# A past boundary chart in Minkowski space: the half-space `{t > 0}` at the origin

Programme target `T-loc-minkowski-past-boundary-chart` (`programme/roadmap.toml`; layer 3, kind
localisation, model `minkowski`, `provides = []`: the chart is not a ladder node yet). It is the
kb/0011 witness of `T-abs-flrw-type`'s predicate: the programme definition
`Causality.PastBoundaryChart` (`Causal.FlrwType`) is instantiated at the model, **without
restatement**, so `not_pastBoundaryChart_of_flrwType` applies to it as it stands. 2312.07443 is
not ledgered and has no binder, so **no label is marked**. Source: J. Sbierski, *The
C⁰-inextendibility of a class of FLRW spacetimes*, `references/sbierski/text/sbierski2023c.txt`,
the proof of Thm 1.5 (§4.1, `:1057–1144`), read with `g̃ = m` (Minkowski, so `g̃_n`, `g̃`, `g̃_w`
play no role).

> Consider the future directed timelike curve γ̃ : [0, ε0 ) → Ũ given in coordinates by s 7→ (s, 0).
> Then γ̃|(0,ε0 ) corresponds to a future directed and past inextendible timelike curve
> γ := ι−1 ◦ γ̃|(0,ε0 ) in M . (`:1059–1061`)

> Since the set I + p̃, Ũ ∩ I − γ̃(s0 ), Ũ is compactly contained in Ũ , there is an
> x0 ∈ (−ε1 , ε1 )d such that the timelike curve σ̃ : f (x0 ), ε0 ) → Ũ , given by s 7→ (s, x0 ),
> does not enter this set. (`:1137–1138`)

## What is proved (no `sorry`)

On `ℝ^{1,n}` (`Causal.minkowski n`), `n ≥ 1`, with `W = {t > 0}` (`minkowskiPosHalfSpace n`):

1. **The instance** `minkowski_pastBoundaryChart : (minkowski n).PastBoundaryChart W Ũ 0`, the data
   `minkowskiPastBoundaryChartData`: `Ũ = (−1, 1) × B(0, 1/10)` (`minkowskiChartBox n`),
   `V = W ⊓ Ũ`, `γ̃(s) = (s/2, 0)` (`minkowskiChartCurve n`), `s₀ = 1/4`, and for a compact
   `K ⊆ Ũ` the vertical line `σ(τ) = (9τ/10, x₀)` with `‖x₀‖ < 1/10` off the projection of `K`.
   One lemma per field: (iii) `minkowski_Iplus_chartBox_subset_inside`, (iv)
   `minkowski_chronalCurveOn_chartCurve`, `minkowskiChartCurve_mem`, (v)
   `isCompact_closure_minkowskiChartDiamond`, `closure_minkowskiChartDiamond_subset` (the closed
   diamond lies in `[0, 1/8] × B̄(0, 1/16)`), (vi) `minkowski_exists_avoiding_curve` (with
   `minkowski_exists_notMem_snd_image` for `x₀`).
2. **`n ≥ 1` is needed**: in `ℝ^{1,0}` no open set has a past boundary chart at any point
   (`minkowski_zero_not_pastBoundaryChart`, the argument of `timelikeLine_not_pastBoundaryChart`).
3. **(A) fails on `W`** (`minkowski_posHalfSpace_not_flrwTypeA`): `γ̃` over `(0, 1]` is
   past-inextensible and chronal on its segments in `W` (step (a),
   `ChronalCurveOn.pastInextensible_Ioc_of_start_notMem`), and its chronal future in `W` lies in
   `I⁺(0)` (`minkowski_iUnion_Iplus_chartCurve_subset`), which misses `(1, e) ∈ W`, `‖e‖ = 1`.
4. **(B) fails on `W`**, at every point: no `I⁻(x, W)` contains a Cauchy surface of `W`
   (`minkowski_posHalfSpace_not_isCauchySurfaceOn_subset_Iminus`, any `x`): the vertical line at
   `x.2 + |x.1| e`, inextensible in `W` on its maximal piece
   (`IsCauchySurfaceOn.exists_mem_connectedComponentIn`), never enters `I⁻(x, W)`; hence
   `minkowski_posHalfSpace_not_flrwTypeB`.
5. **The check** `minkowski_posHalfSpace_flrwType_check`: one conjunction, the chart ∧ `T2` ∧
   second countable ∧ `CausallyArcConnectedOn W` ∧ `FutureOneConnectedOn W` (`W` is convex) ∧
   `≤_W` antisymmetric ∧ ¬(A) ∧ ¬(B), each hypothesis of `not_pastBoundaryChart_of_flrwType` in the
   theorem's own shape. **The theorem applied without restatement**:
   `minkowski_posHalfSpace_not_flrwTypeA_and_B`, `¬((A) ∧ (B))` on `W`, by
   `not_pastBoundaryChart_of_flrwType` itself.

## Hypothesis checklist

| the target / Sbierski §4.1 | here |
|---|---|
| `ℝ^{1,n}`, `n ≥ 1` | ✓ `(hn : 0 < n)`; needed: `minkowski_zero_not_pastBoundaryChart` |
| `W = {t > 0}`, `p = 0` (`p̃` a past boundary point) | ✓ `minkowskiPosHalfSpace n`, `0` |
| the chart `Ũ` (Sbierski's `(−ε₀, ε₀) × (−ε₁, ε₁)^d`) | ✓ `(−1, 1) × B(0, 1/10)`, `ε₀ = 1`, a ball for the cube |
| (i) `p ∈ Ũ ∖ W` | ✓ |
| (ii) `V = Ũ_>` | ✓ `V = W ⊓ Ũ`, `inside_le` by `le_rfl` |
| (iii) `V` future-closed in `Ũ` ((2.4) reversed) | ✓ proved directly: `Ũ` and `V` convex, `≪` raises `t` (not through `Causal.BoundaryChartCauchy`) |
| (iv) `γ̃(s) = (s, 0)` on `[0, ε₀)` | ✓ `s ↦ (s/2, 0)` on `[0, 1]`, so `γ̃ 1 = (ε₀/2, 0)` |
| (v) `0 < s₀ < ε₀/2`, the diamond compact in `Ũ` (`:1077`) | ✓ `s₀ = 1/4`, `γ̃ s₀ = (1/8, 0)`, the closure inside `[0, 1/8] × B̄(0, 1/16)` |
| (vi) `σ̃(s) = (s, x₀)` from `f(x₀) = 0`, its end in the slab of (4.1) | ✓ `σ(τ) = (9τ/10, x₀)`; `(1/2, 0) ≪_Ũ (9/10, x₀)` since `‖x₀‖ < 1/10 < 2/5`; the field asks only that, so the end need not lie in Sbierski's slab `(19ε₀/20, ε₀)` (it does not: `9/10 < 19/20`) |

## SCOPE (disclosed)

* **The dispatch's parameters are used unchanged**: `Ũ = (−1, 1) × B(0, 1/10)`, `V = W ⊓ Ũ`,
  `γ̃(s) = (s/2, 0)`, `s₀ = 1/4`, `σ(τ) = (9τ/10, x₀)`.
* **Field (iii) is proved directly** for the half-space, by convexity
  (`Causal.Flat.lt_iff_of_convex`: on a convex open set `≪` restricts), not by
  `Iplus_subset_inside_of_boundaryChart` (`Causal.BoundaryChartCauchy`), which would need a Cauchy
  surface `S` of `W` with `V ⊆ J⁻(S, W)`.
* **Both (A) and (B) fail on `W`**, so this instance shows the predicate inhabited and the theorem
  non-vacuous, but does not separate (A) from (B): it does not show that each is needed alone.
  An instance with a chart and exactly one of (A), (B) is not attempted.
* **OQ-159** (OPEN: whether the six fields are the notion of record) is not decided: the instance
  proves the six fields, hence each weakening that row names.
* `provides = []`: no ladder node, no `causal_ladder`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Metric

variable {n : ℕ}

/-! ### The open sets and the vertical curve -/

/-- The open half-space `W = {t > 0}` of `ℝ^{1,n}`, the role of Sbierski's `ι(M)`. -/
def minkowskiPosHalfSpace (n : ℕ) : Opens (Minkowski n) :=
  ⟨{x | 0 < x.1}, isOpen_lt continuous_const continuous_fst⟩

/-- Membership in `W = {t > 0}`. -/
theorem mem_minkowskiPosHalfSpace {x : Minkowski n} :
    x ∈ minkowskiPosHalfSpace n ↔ 0 < x.1 := Iff.rfl

/-- `W = {t > 0}` is convex. -/
theorem convex_minkowskiPosHalfSpace :
    Convex ℝ (minkowskiPosHalfSpace n : Set (Minkowski n)) :=
  convex_halfSpace_gt (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).isLinear 0

/-- The chart box `(−1, 1) × B(0, 1/10)` of `ℝ^{1,n}`, the role of Sbierski's `Ũ`. -/
def minkowskiChartBox (n : ℕ) : Opens (Minkowski n) :=
  ⟨Ioo (-1) 1 ×ˢ ball 0 (1 / 10), isOpen_Ioo.prod isOpen_ball⟩

/-- Membership in `Ũ = (−1, 1) × B(0, 1/10)`. -/
theorem mem_minkowskiChartBox {x : Minkowski n} :
    x ∈ minkowskiChartBox n ↔ x.1 ∈ Ioo (-1 : ℝ) 1 ∧ ‖x.2‖ < 1 / 10 := by
  show x.1 ∈ Ioo (-1 : ℝ) 1 ∧ x.2 ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 10) ↔ _
  rw [mem_ball_zero_iff]

/-- `Ũ` is convex. -/
theorem convex_minkowskiChartBox : Convex ℝ (minkowskiChartBox n : Set (Minkowski n)) :=
  (convex_Ioo (-1 : ℝ) 1).prod (convex_ball 0 (1 / 10))

/-- The inside `V = W ⊓ Ũ` is convex. -/
theorem convex_minkowskiChartInside :
    Convex ℝ ((minkowskiPosHalfSpace n ⊓ minkowskiChartBox n : Opens (Minkowski n)) :
      Set (Minkowski n)) := by
  rw [Opens.coe_inf]
  exact convex_minkowskiPosHalfSpace.inter convex_minkowskiChartBox

/-- The vertical curve `γ̃(s) = (s/2, 0)`. -/
noncomputable def minkowskiChartCurve (n : ℕ) : ℝ → Minkowski n := fun s => (s / 2, 0)

/-- `γ̃(s) = (s/2, 0)`. -/
theorem minkowskiChartCurve_apply (s : ℝ) : minkowskiChartCurve n s = (s / 2, 0) := rfl

/-- **Field (iv)**: `γ̃ 0 = 0`. -/
theorem minkowskiChartCurve_zero : minkowskiChartCurve n 0 = 0 := by
  rw [minkowskiChartCurve_apply, zero_div]; rfl

/-! ### The six fields -/

/-- **Field (iii)**: the inside `V = W ⊓ Ũ` is future-closed in `Ũ`. Both are convex, so `≪_Ũ` and
`≪_V` are the restrictions of `≪` (`Causal.Flat.lt_iff_of_convex`), and `x ≪ y` raises the time:
`y.1 > x.1 > 0`. -/
theorem minkowski_Iplus_chartBox_subset_inside {x : Minkowski n}
    (hx : x ∈ minkowskiPosHalfSpace n ⊓ minkowskiChartBox n) :
    (minkowski n).Iplus (minkowskiChartBox n) {x} ⊆
      (minkowski n).Iplus (minkowskiPosHalfSpace n ⊓ minkowskiChartBox n) {x} := by
  intro y hy
  rw [Precausality.mem_Iplus_singleton] at hy ⊢
  obtain ⟨-, hyU, hxy⟩ := (Flat.lt_iff_of_convex convex_minkowskiChartBox).1 hy
  refine (Flat.lt_iff_of_convex convex_minkowskiChartInside).2 ⟨hx, ⟨?_, hyU⟩, hxy⟩
  have h1 := minkowski_lt_top_iff.1 hxy
  have h0 : 0 < x.1 := hx.1
  show 0 < y.1
  linarith [norm_nonneg (y.2 - x.2)]

/-- **Field (iv)**: `γ̃` is a chronal curve of `Ũ` over `[0, 1]`. -/
theorem minkowski_chronalCurveOn_chartCurve :
    (minkowski n).ChronalCurveOn (minkowskiChartBox n) (minkowskiChartCurve n) 0 1 := by
  refine minkowski_chronalCurveOn_iff.2 ⟨?_, fun s hs => ?_, fun s _ s' _ h => ?_⟩
  · exact ((continuous_id.div_const 2).prodMk continuous_const).continuousOn
  · rw [minkowskiChartCurve_apply]
    exact mem_minkowskiChartBox.2 ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, by simp⟩
  · rw [minkowskiChartCurve_apply, minkowskiChartCurve_apply, minkowski_lt_top_iff]
    simp only [sub_self, norm_zero]
    linarith

/-- **Field (iv)**: `γ̃ (0, 1] ⊆ V`. -/
theorem minkowskiChartCurve_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    minkowskiChartCurve n t ∈ minkowskiPosHalfSpace n ⊓ minkowskiChartBox n := by
  rw [minkowskiChartCurve_apply]
  exact ⟨show (0 : ℝ) < t / 2 by linarith [ht.1],
    mem_minkowskiChartBox.2 ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp⟩⟩

/-- **Field (v)**, the bound: the chart diamond from `0` to `γ̃ (1/4) = (1/8, 0)` lies in the
compact cylinder `[0, 1/8] × B̄(0, 1/16)`. -/
theorem minkowski_chartDiamond_subset :
    (minkowski n).Iplus (minkowskiChartBox n) {0} ∩
        (minkowski n).Iminus (minkowskiChartBox n) {minkowskiChartCurve n (1 / 4)} ⊆
      Icc (0 : ℝ) (1 / 8) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 16) := by
  rintro z ⟨h1, h2⟩
  rw [Precausality.mem_Iplus_singleton] at h1
  rw [Precausality.mem_Iminus_singleton] at h2
  have e1 := minkowski_lt_top_iff.1 ((minkowski n).lt_mono le_top h1)
  have e2 := minkowski_lt_top_iff.1 ((minkowski n).lt_mono le_top h2)
  rw [minkowskiChartCurve_apply] at e2
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, zero_sub, norm_neg] at e1 e2
  refine ⟨⟨by linarith [norm_nonneg z.2], by linarith [norm_nonneg z.2]⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  linarith

/-- The cylinder `[0, 1/8] × B̄(0, 1/16)` is compact. -/
theorem isCompact_minkowskiChartCylinder :
    IsCompact (Icc (0 : ℝ) (1 / 8) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 16)) :=
  isCompact_Icc.prod (isCompact_closedBall 0 _)

/-- The cylinder `[0, 1/8] × B̄(0, 1/16)` lies in `Ũ`. -/
theorem minkowskiChartCylinder_subset :
    Icc (0 : ℝ) (1 / 8) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 16) ⊆
      minkowskiChartBox n := by
  rintro z ⟨hz1, hz2⟩
  rw [mem_closedBall_zero_iff] at hz2
  exact mem_minkowskiChartBox.2 ⟨⟨by linarith [hz1.1], by linarith [hz1.2]⟩, by linarith⟩

/-- **Field (v)**: the closure of the chart diamond is compact … -/
theorem isCompact_closure_minkowskiChartDiamond :
    IsCompact (closure ((minkowski n).Iplus (minkowskiChartBox n) {0} ∩
      (minkowski n).Iminus (minkowskiChartBox n) {minkowskiChartCurve n (1 / 4)})) :=
  isCompact_minkowskiChartCylinder.of_isClosed_subset isClosed_closure
    (closure_minimal minkowski_chartDiamond_subset isCompact_minkowskiChartCylinder.isClosed)

/-- **Field (v)**: … and lies in `Ũ`. -/
theorem closure_minkowskiChartDiamond_subset :
    closure ((minkowski n).Iplus (minkowskiChartBox n) {0} ∩
      (minkowski n).Iminus (minkowskiChartBox n) {minkowskiChartCurve n (1 / 4)}) ⊆
        minkowskiChartBox n :=
  (closure_minimal minkowski_chartDiamond_subset isCompact_minkowskiChartCylinder.isClosed).trans
    minkowskiChartCylinder_subset

/-- **Field (vi)**, the choice of `x₀`: for `n ≥ 1`, a compact `K ⊆ Ũ` does not project onto the
ball `B(0, 1/10)`. Otherwise its projection, closed, would contain the closed ball, and the point
`(1/10)e` of norm `1/10` would be the space part of a point of `Ũ`. -/
theorem minkowski_exists_notMem_snd_image (hn : 0 < n) {K : Set (Minkowski n)}
    (hK : IsCompact K) (hKU : K ⊆ minkowskiChartBox n) :
    ∃ x₀ : EuclideanSpace ℝ (Fin n), ‖x₀‖ < 1 / 10 ∧ x₀ ∉ Prod.snd '' K := by
  by_contra h
  push Not at h
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 10) ⊆ Prod.snd '' K := fun x hx =>
    h x (mem_ball_zero_iff.1 hx)
  have hcl : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 10) ⊆ Prod.snd '' K := by
    rw [← closure_ball (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (1 / 10 : ℝ) ≠ 0)]
    exact closure_minimal hsub (hK.image continuous_snd).isClosed
  have hv : (1 / 10 : ℝ) • unitVec n hn ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 10) := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_unitVec, Real.norm_eq_abs]
    norm_num
  obtain ⟨z, hz, hzv⟩ := hcl hv
  have := (mem_minkowskiChartBox.1 (hKU hz)).2
  rw [hzv, norm_smul, norm_unitVec, Real.norm_eq_abs] at this
  norm_num at this

/-- **Field (vi)**: for `n ≥ 1` and a compact `K ⊆ Ũ`, the vertical line `σ(τ) = (9τ/10, x₀)`,
`x₀` off the projection of `K`, is a chronal curve of `Ũ` from `(0, x₀) ∉ W` through `V ∖ K`, and
`γ̃ 1 = (1/2, 0) ≪_Ũ (9/10, x₀)` since `‖x₀‖ < 1/10 < 9/10 − 1/2`. -/
theorem minkowski_exists_avoiding_curve (hn : 0 < n) {K : Set (Minkowski n)} (hK : IsCompact K)
    (hKU : K ⊆ minkowskiChartBox n) :
    ∃ σ : ℝ → Minkowski n, (minkowski n).ChronalCurveOn (minkowskiChartBox n) σ 0 1 ∧
      σ 0 ∉ minkowskiPosHalfSpace n ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, σ t ∈ minkowskiPosHalfSpace n ⊓ minkowskiChartBox n ∧ σ t ∉ K) ∧
      (minkowski n).lt (minkowskiChartBox n) (minkowskiChartCurve n 1) (σ 1) := by
  obtain ⟨x₀, hx₀, hx₀K⟩ := minkowski_exists_notMem_snd_image hn hK hKU
  refine ⟨fun τ => (9 * τ / 10, x₀), ?_, ?_, fun t ht => ⟨?_, ?_⟩, ?_⟩
  · refine minkowski_chronalCurveOn_iff.2 ⟨?_, fun τ hτ => ?_, fun s _ s' _ h => ?_⟩
    · exact (((continuous_const.mul continuous_id).div_const 10).prodMk
        continuous_const).continuousOn
    · exact mem_minkowskiChartBox.2 ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hx₀⟩
    · rw [minkowski_lt_top_iff]
      simp only [sub_self, norm_zero]
      linarith
  · rw [mem_minkowskiPosHalfSpace]
    norm_num
  · exact ⟨show (0 : ℝ) < 9 * t / 10 by linarith [ht.1],
      mem_minkowskiChartBox.2 ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hx₀⟩⟩
  · intro htK
    exact hx₀K ⟨_, htK, rfl⟩
  · rw [minkowskiChartCurve_apply]
    refine (Flat.lt_iff_of_convex convex_minkowskiChartBox).2
      ⟨mem_minkowskiChartBox.2 ⟨⟨by norm_num, by norm_num⟩, by simp⟩,
        mem_minkowskiChartBox.2 ⟨⟨by norm_num, by norm_num⟩, hx₀⟩, ?_⟩
    rw [minkowski_lt_top_iff]
    simp only [sub_zero]
    linarith

/-! ### The chart -/

/-- **The data of the chart**: `Ũ = (−1, 1) × B(0, 1/10)`, `V = W ⊓ Ũ`, `γ̃(s) = (s/2, 0)`,
`s₀ = 1/4`, and for `K` compact in `Ũ` the vertical line at `x₀` off the projection of `K`. -/
noncomputable def minkowskiPastBoundaryChartData (hn : 0 < n) :
    (minkowski n).PastBoundaryChartData (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0 where
  mem := mem_minkowskiChartBox.2 ⟨⟨by norm_num, by norm_num⟩, by simp⟩
  not_mem := by
    rw [mem_minkowskiPosHalfSpace]
    exact lt_irrefl 0
  inside := minkowskiPosHalfSpace n ⊓ minkowskiChartBox n
  inside_le := le_rfl
  futureClosed _ hx := minkowski_Iplus_chartBox_subset_inside hx
  curve := minkowskiChartCurve n
  chronalCurveOn := minkowski_chronalCurveOn_chartCurve
  curve_zero := minkowskiChartCurve_zero
  curve_mem _ ht := minkowskiChartCurve_mem ht
  s₀ := 1 / 4
  s₀_mem := ⟨by norm_num, by norm_num⟩
  isCompact_closure := isCompact_closure_minkowskiChartDiamond
  closure_subset := closure_minkowskiChartDiamond_subset
  avoid _ hK hKU := minkowski_exists_avoiding_curve hn hK hKU

/-- **The half-space `{t > 0}` of `ℝ^{1,n}`, `n ≥ 1`, has a past boundary chart at `0`**: the
programme definition `Causality.PastBoundaryChart` (`Causal.FlrwType`) for the model, no
restatement. The kb/0011 witness that `not_pastBoundaryChart_of_flrwType` is not vacuous. -/
theorem minkowski_pastBoundaryChart (hn : 0 < n) :
    (minkowski n).PastBoundaryChart (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0 :=
  ⟨minkowskiPastBoundaryChartData hn⟩

/-! ### `n ≥ 1` is needed -/

/-- In `ℝ^{1,0}` a point is its time. -/
theorem minkowski_zero_ext {x y : Minkowski 0} (h : x.1 = y.1) : x = y :=
  Prod.ext h (Subsingleton.elim _ _)

/-- **`n ≥ 1` is needed**: in `ℝ^{1,0}` no open set has a past boundary chart at any point (the
argument of `timelikeLine_not_pastBoundaryChart`). Take `K = γ̃ '' [0, 1]`. If `σ 0` is not later
than `γ̃ 1`, `σ` passes through `γ̃ 1` (intermediate values; a point is its time), at `0`, where
`σ 0 ∉ W ⊇ V ∋ γ̃ 1`, or later, inside `K`. Otherwise `σ 0` lies on a chronal curve of `Ũ` from
`γ̃ 1` to `σ 1`, so `γ̃ 1 ≪_Ũ σ 0`, and (iii) puts `σ 0` in `V ⊆ W`. -/
theorem minkowski_zero_not_pastBoundaryChart (W Ũ : Opens (Minkowski 0)) (p : Minkowski 0) :
    ¬ (minkowski 0).PastBoundaryChart W Ũ p := by
  rintro ⟨d⟩
  have hcont := CurveOn.continuousOn (minkowski 0).isRelFamily_lt d.chronalCurveOn
  have hK : IsCompact (d.curve '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hcont
  have hKU : d.curve '' Icc 0 1 ⊆ Ũ := by
    rintro _ ⟨t, ht, rfl⟩
    exact d.chronalCurveOn.mem t ht
  obtain ⟨σ, hσ, hσ0, hσmem, hσ1⟩ := d.avoid _ hK hKU
  have hV1 : d.curve 1 ∈ d.inside := d.curve_mem 1 ⟨zero_lt_one, le_rfl⟩
  have hσ1' := minkowski_lt_top_iff.1 ((minkowski 0).lt_mono le_top hσ1)
  have hσc := CurveOn.continuousOn (minkowski 0).isRelFamily_lt hσ
  rcases le_or_gt (σ 0).1 (d.curve 1).1 with hle | hlt
  · -- `σ` passes through `γ̃ 1`
    obtain ⟨t, ht, hσt⟩ := intermediate_value_Icc zero_le_one
      (continuous_fst.comp_continuousOn hσc)
      ⟨hle, show (d.curve 1).1 ≤ (σ 1).1 by linarith [norm_nonneg ((σ 1).2 - (d.curve 1).2)]⟩
    have heq : σ t = d.curve 1 := minkowski_zero_ext hσt
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0] at heq
      exact hσ0 (d.inside_le (heq ▸ hV1)).1
    · exact (hσmem t ⟨h0, ht.2⟩).2 (heq ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
  · -- `σ 0` lies on a chronal curve of `Ũ` from `γ̃ 1` to `σ 1`
    obtain ⟨c, hc, hc0, hc1⟩ := (minkowski_causallyArcConnected Ũ le_top _ _).2.1 hσ1
    have hcc := CurveOn.continuousOn (minkowski 0).isRelFamily_lt hc
    have hσ01 := minkowski_lt_top_iff.1
      ((minkowski 0).lt_mono le_top (hσ.lt_of_lt le_rfl zero_lt_one le_rfl))
    have hmemI : (σ 0).1 ∈ Icc ((Prod.fst ∘ c) 0) ((Prod.fst ∘ c) 1) := by
      simp only [Function.comp, hc0, hc1]
      constructor <;> linarith [norm_nonneg ((σ 1).2 - (σ 0).2)]
    obtain ⟨u, hu, hcu⟩ := intermediate_value_Icc zero_le_one
      (continuous_fst.comp_continuousOn hcc) hmemI
    have heq : c u = σ 0 := minkowski_zero_ext hcu
    have hu0 : 0 < u := by
      rcases hu.1.eq_or_lt with h | h
      · rw [← h, hc0] at heq
        rw [heq] at hlt
        exact absurd hlt (lt_irrefl _)
      · exact h
    have hrel : (minkowski 0).lt Ũ (d.curve 1) (σ 0) := by
      have := hc.lt_of_lt le_rfl hu0 hu.2
      rwa [hc0, heq] at this
    have := d.futureClosed _ hV1 (Precausality.mem_Iplus_singleton.2 hrel)
    exact hσ0 (d.inside_le
      ((minkowski 0).lt_mem_right (Precausality.mem_Iplus_singleton.1 this))).1

/-! ### (A) and (B) fail on the half-space -/

/-- The chronological future in `W` of `γ̃` over `(0, 1]` lies in the cone `I⁺(0)` of `ℝ^{1,n}`:
`0 ≪ γ̃ t` for `t > 0`, and `≪_W` implies `≪`. -/
theorem minkowski_iUnion_Iplus_chartCurve_subset :
    ⋃ t ∈ Ioc (0 : ℝ) 1, (minkowski n).Iplus (minkowskiPosHalfSpace n) {minkowskiChartCurve n t} ⊆
      (minkowski n).Iplus ⊤ {0} := by
  refine iUnion₂_subset fun t ht z hz => ?_
  rw [Precausality.mem_Iplus_singleton] at hz ⊢
  refine (minkowski n).lt_trans ?_ ((minkowski n).lt_mono le_top hz)
  rw [minkowskiChartCurve_apply, minkowski_lt_top_iff]
  simp only [Prod.snd_zero, Prod.fst_zero, sub_self, norm_zero, sub_zero]
  linarith [ht.1]

/-- **(A) of `not_pastBoundaryChart_of_flrwType` fails on `W = {t > 0}`**, `n ≥ 1`, stated in
the theorem's own shape: `γ̃` over `(0, 1]` is past-inextensible in `W` and chronal on its segments
(step (a), `ChronalCurveOn.pastInextensible_Ioc_of_start_notMem`), but its chronal future in `W`
lies in `I⁺(0)`, which misses `(1, e) ∈ W` (`‖e‖ = 1`). -/
theorem minkowski_posHalfSpace_not_flrwTypeA (hn : 0 < n) :
    ¬ ∀ (I : Set ℝ) (γ : ℝ → Minkowski n),
      (minkowski n).PastInextensible (minkowskiPosHalfSpace n) I γ →
      (∀ a ∈ I, ∀ b ∈ I, (minkowski n).ChronalCurveOn (minkowskiPosHalfSpace n) γ a b) →
      ⋃ t ∈ I, (minkowski n).Iplus (minkowskiPosHalfSpace n) {γ t} = minkowskiPosHalfSpace n := by
  intro hA
  obtain ⟨hinex, hchr⟩ := Causality.ChronalCurveOn.pastInextensible_Ioc_of_start_notMem
    (W := minkowskiPosHalfSpace n) minkowski_chronalCurveOn_chartCurve ⟨zero_lt_one, le_rfl⟩
    (fun t ht => (minkowskiChartCurve_mem ht).1)
    (by rw [minkowskiChartCurve_zero, mem_minkowskiPosHalfSpace]; exact lt_irrefl 0)
  have hmem : ((1 : ℝ), unitVec n hn) ∈ (minkowskiPosHalfSpace n : Set (Minkowski n)) :=
    (one_pos : (0 : ℝ) < 1)
  rw [← hA _ _ hinex hchr] at hmem
  have h := Precausality.mem_Iplus_singleton.1 (minkowski_iUnion_Iplus_chartCurve_subset hmem)
  rw [minkowski_lt_top_iff] at h
  simp only [Prod.snd_zero, Prod.fst_zero, sub_zero, norm_unitVec] at h
  exact lt_irrefl _ h

/-- **No `I⁻(x, W)` contains a Cauchy surface of `W = {t > 0}`**, `n ≥ 1`, for any point `x`:
the vertical line `τ ↦ (τ, y)`, `y = x.2 + |x.1| e`, is inextensible in `W` on its maximal piece,
so a Cauchy surface of `W` meets it (`IsCauchySurfaceOn.exists_mem_connectedComponentIn`), at a
time `s > 0`; a point there in `I⁻(x, W)` would have `|x.1| = ‖x.2 − y‖ < x.1 − s < x.1`. -/
theorem minkowski_posHalfSpace_not_isCauchySurfaceOn_subset_Iminus (hn : 0 < n)
    (x : Minkowski n) {S : Set (Minkowski n)}
    (hS : (minkowski n).IsCauchySurfaceOn (minkowskiPosHalfSpace n) S) :
    ¬ S ⊆ (minkowski n).Iminus (minkowskiPosHalfSpace n) {x} := by
  intro hSx
  set y : EuclideanSpace ℝ (Fin n) := x.2 + |x.1| • unitVec n hn with hy
  let ℓ : ℝ → Minkowski n := fun τ => (τ, y)
  have hℓ : Continuous ℓ := continuous_id.prodMk continuous_const
  have hcurve : ∀ a b, a ≤ b → (∀ τ ∈ Icc a b, ℓ τ ∈ minkowskiPosHalfSpace n) →
      (minkowski n).CausalCurveOn (minkowskiPosHalfSpace n) ℓ a b := by
    intro a b _ hmem
    refine (minkowski_chronalCurveOn_iff.2 ⟨hℓ.continuousOn, fun τ hτ => hmem τ hτ,
      fun s _ s' _ h => ?_⟩).causalCurveOn
    rw [minkowski_lt_top_iff]
    simp only [ℓ, sub_self, norm_zero]
    linarith
  obtain ⟨s, -, hs⟩ := hS.exists_mem_connectedComponentIn hℓ continuous_fst (fun τ => rfl)
    hcurve (t := 1) (show (0 : ℝ) < 1 from one_pos)
  have h1 := Precausality.mem_Iminus_singleton.1 (hSx hs)
  have hs0 : 0 < s := (minkowski n).lt_mem_left h1
  have h2 := minkowski_lt_top_iff.1 ((minkowski n).lt_mono le_top h1)
  have hnorm : ‖x.2 - y‖ = |x.1| := by
    rw [show x.2 - y = -(|x.1| • unitVec n hn) by rw [hy]; abel, norm_neg, norm_smul,
      norm_unitVec, Real.norm_eq_abs, abs_abs, mul_one]
  simp only [ℓ] at h2
  rw [hnorm] at h2
  linarith [le_abs_self x.1]

/-- **(B) of `not_pastBoundaryChart_of_flrwType` fails on `W = {t > 0}`**, `n ≥ 1`, in the shape
of the theorem's hypothesis (at `x = (1, 0)`; in fact at every point). -/
theorem minkowski_posHalfSpace_not_flrwTypeB (hn : 0 < n) :
    ¬ ∀ x ∈ minkowskiPosHalfSpace n, ∃ S : Set (Minkowski n),
      (minkowski n).IsCauchySurfaceOn (minkowskiPosHalfSpace n) S ∧
        S ⊆ (minkowski n).Iminus (minkowskiPosHalfSpace n) {x} := by
  intro hB
  obtain ⟨S, hS, hSx⟩ := hB ((1 : ℝ), 0) (show (0 : ℝ) < 1 from one_pos)
  exact minkowski_posHalfSpace_not_isCauchySurfaceOn_subset_Iminus hn _ hS hSx

/-! ### The check: which hypothesis the theorem needs -/

/-- **The check: which hypotheses of `not_pastBoundaryChart_of_flrwType` hold on `W = {t > 0}`.**
For `n ≥ 1`, `W` has a past boundary chart at `0`, and every hypothesis of the theorem holds except
(A) and (B), both of which fail: `T2`, second countable, causally arc-connected (open in a
causally arc-connected space), future one-connected (convex), `≤_W` antisymmetric (`≤_W` implies
`≤`, which is causal), ¬(A), ¬(B), each in the theorem's own shape. -/
theorem minkowski_posHalfSpace_flrwType_check (hn : 0 < n) :
    (minkowski n).PastBoundaryChart (minkowskiPosHalfSpace n) (minkowskiChartBox n) 0 ∧
      T2Space (Minkowski n) ∧ SecondCountableTopology (Minkowski n) ∧
      (minkowski n).CausallyArcConnectedOn (minkowskiPosHalfSpace n) ∧
      (minkowski n).FutureOneConnectedOn (minkowskiPosHalfSpace n) ∧
      (∀ ⦃x y : Minkowski n⦄, (minkowski n).le (minkowskiPosHalfSpace n) x y →
        (minkowski n).le (minkowskiPosHalfSpace n) y x → x = y) ∧
      (¬ ∀ (I : Set ℝ) (γ : ℝ → Minkowski n),
        (minkowski n).PastInextensible (minkowskiPosHalfSpace n) I γ →
        (∀ a ∈ I, ∀ b ∈ I, (minkowski n).ChronalCurveOn (minkowskiPosHalfSpace n) γ a b) →
        ⋃ t ∈ I, (minkowski n).Iplus (minkowskiPosHalfSpace n) {γ t} =
          minkowskiPosHalfSpace n) ∧
      (¬ ∀ x ∈ minkowskiPosHalfSpace n, ∃ S : Set (Minkowski n),
        (minkowski n).IsCauchySurfaceOn (minkowskiPosHalfSpace n) S ∧
          S ⊆ (minkowski n).Iminus (minkowskiPosHalfSpace n) {x}) :=
  ⟨minkowski_pastBoundaryChart hn, inferInstance, inferInstance,
    Causality.CausallyArcConnectedOn.mono minkowski_causallyArcConnected le_top,
    minkowski_futureOneConnectedOn convex_minkowskiPosHalfSpace,
    fun _ _ hxy hyx => minkowski_isCausal ((minkowski n).le_mono le_top hxy)
      ((minkowski n).le_mono le_top hyx),
    minkowski_posHalfSpace_not_flrwTypeA hn,
    minkowski_posHalfSpace_not_flrwTypeB hn⟩

/-- **The theorem applied without restatement**: on `W = {t > 0}`, `n ≥ 1`, (A) and (B) do not
both hold, by `not_pastBoundaryChart_of_flrwType` and the chart (the other hypotheses from the
check). Weaker than `minkowski_posHalfSpace_not_flrwTypeA` alone; its point is that the
abstract theorem consumes the instance as it stands. -/
theorem minkowski_posHalfSpace_not_flrwTypeA_and_B (hn : 0 < n) :
    ¬ ((∀ (I : Set ℝ) (γ : ℝ → Minkowski n),
        (minkowski n).PastInextensible (minkowskiPosHalfSpace n) I γ →
        (∀ a ∈ I, ∀ b ∈ I, (minkowski n).ChronalCurveOn (minkowskiPosHalfSpace n) γ a b) →
        ⋃ t ∈ I, (minkowski n).Iplus (minkowskiPosHalfSpace n) {γ t} =
          minkowskiPosHalfSpace n) ∧
      (∀ x ∈ minkowskiPosHalfSpace n, ∃ S : Set (Minkowski n),
        (minkowski n).IsCauchySurfaceOn (minkowskiPosHalfSpace n) S ∧
          S ⊆ (minkowski n).Iminus (minkowskiPosHalfSpace n) {x})) := by
  rintro ⟨hA, hB⟩
  obtain ⟨hchart, -, -, hcac, hfoc, hcaus, -, -⟩ := minkowski_posHalfSpace_flrwType_check hn
  exact Causality.not_pastBoundaryChart_of_flrwType hcac hfoc hcaus hA hB _ _ hchart

end Causal
