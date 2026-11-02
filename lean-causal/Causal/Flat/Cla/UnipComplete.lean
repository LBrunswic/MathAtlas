import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend
import Causal.Flat.Cla.RegularComplete

/-!
# `Causal.Flat.Cla.UnipComplete` — unipotent spacetimes are GH and Cauchy-complete

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257); line
numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. **No label is
marked**: the theorem is proved with no `sorry` beneath it (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`), but it is the paper's statement in the library's readings of
GH (ETT's, `FlatSpacetime.GH`) and of Cauchy-completeness (DEC-35, `IsCauchyComplete`), so the
row is `partial` (kb/0011, DEC-27), as for `RegularComplete`.

* `unipfam` — `GHFspace.tex:633` (§3, "Unipotent spacetimes", l.632–753), the closing claim
  l.743–744: `gh_isCauchyComplete_of_isUnipotentSpacetime`, every `IsUnipotentSpacetime M` is
  `GH M ∧ IsCauchyComplete (e + 1) M`. Serves `Classification.exists_absMax_unipotent_ltp`
  (`Flat/Classification.lean:2324`, GH and Cauchy-completeness of `M₂`) and
  `cauclo_from_embedding` (`:2447`, GH of `B` over a unipotent base).

> Let $f: I=]y_{j}, y_{j+1}[ \rightarrow {\mathbb R}$ be any (strictly) increasing function.
> (l.676–677)

> This is time now to specify the function $f$: let $y_{0}$ be any element of $I$, and
> $a: I \rightarrow ]1, +\infty[$ any smooth function such that the integrals
> $\int_{y_{j}}^{y_{0}} a(y) dy$ and $\int_{y_{0}}^{y_{j+1}} a(y) dy$ are both infinite.
> Choose $f(y) = \int_{y_{0}}^{y}a^{2}(y)dy$. We claim that for such a $f$, the metric on
> $S_{f}$ is complete (l.707–712)

> The finiteness of the first integral implies the finiteness of
> $\int_{0}^{+\infty}a(y(t))y'(t)dt$. It follows that the $y$-coordinate remains in a compact
> subintervall of $I$. (l.719–721)

> Hence, any nonspacelike geodesic intersect $S_{f}$: this is a criteria proving that $S_{f}$ is
> indeed a Cauchy hypersurface. (l.740–741)

> It follows that the quotient of $\Omega$ by $\Gamma$ is globally hyperbolic and
> Cauchy-complete. (l.743–744)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski (d + 1)` (here
`d = e`) has `d + 1` spatial dimensions, in null coordinates `(x, y, z)`, `z ∈ ℝᵈ`.

## How it is proved
* **The function `f`** (`unipF = gauge (3/2) 2 3`) is explicit:
  `f(y) = (3/2) y − [α finite]/(2(y − α)³) + [β finite]/(2(β − y)³)`, with the length gauge
  `G = gauge 1 1 1` (`G′ ≥ 1`, `G′² ≤ 2f′`, `G` unbounded at both ends) in the role of `∫ a`.
* **Cauchy** (`isCauchySurfaceOn_unipS`): Examples' `isCauchySurfaceOn_unipSlice`, for every
  inextensible causal curve of the slab, not only geodesics (`f` continuous, strictly
  increasing, unbounded at both ends).
* **Spacelike Lipschitz** (`isSpacelikeLipschitzIn_unipS`): a local chord estimate
  (`exists_spacelike_nbhd`) gives a slope `c < 1` near each point.
* **Complete** (`completeSpace_inducedLength_unipS`): along a Lipschitz curve of `S`,
  `|ΔG| ≤ length` and `c₀|Δζᵢ| ≤ length` while `|1 + yλᵢ| ≥ c₀` (`ζᵢ = zᵢ/(1 + yλᵢ)`, Barbot's `zᵢ/(y − yᵢ)` up to a constant, l.699–704);
  a Cauchy sequence has `G(y)` Cauchy, hence `y` confined to a compact subinterval, hence `ζ`
  Cauchy, and the limit is a point of `S` (the parametrisation `unipPsi`).
* **Descent** (`isCauchyComplete_of_isUnipotentSpacetime`): `RegularComplete`'s (A),
  `isCauchyComplete_of_isQuotientOf_of_invariant`, in the frame `φ` (`rC_transfer`,
  `actsAcausally_frameConj`), with `Γ` acausal (`actsAcausally_unip`) and `S` `Γ`-invariant
  (`unipAction_mem_unipSlice`).
* **GH** (`gh_of_isUnipotentSpacetime`): the slab is GH in `𝐌ⁿ` (`globallyHyperbolicOn_unipDomain`),
  `{γ | x ≤ γ y}` is finite (`unip_finite_le`), and `gh_frameConj` + the presentation's homeomorphism.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Γ` a discrete subgroup of `A ≅ ℝⁿ⁻²` | ✓ carried (`IsUnipotentSpacetime`: `Γ` acts through a ball-finite `L`) |
| `Ω` a component `y_j < y < y_{j+1}` of `Ω(A)` | ✓ carried (`IsUnipComponent ℓ α β`, `unipDomain α β`) |
| `f = ∫ a²`, `a > 1` smooth, `∫ a = ∞` at both ends (l.707–710) | one explicit `f` (the conclusion is existential in `f`) |

## SCOPE (disclosed)
* GH is ETT's (causal + compact diamonds); Cauchy-complete is DEC-35's reading (a Cauchy surface,
  spacelike Lipschitz, complete for its induced length, length topology finer than the subspace one).
* `f` is piecewise-explicit rather than `∫ a²` for a smooth `a`; the paper's `a := G′` would need
  `f′ = a²`, here only `2f′ ≥ G′²`, which is what the length estimate uses.
* Findings on the paper. (1) l.676–677's "any (strictly) increasing" `f` does not give a Cauchy
  surface (Examples' counterexample under `isCauchySurfaceOn_unipSlice`); the divergence of `f` at
  both ends is needed, and l.707–710's choice supplies it. (2) The Cauchy argument (l.731–741)
  checks causal geodesics only; it is proved here for every inextensible causal curve.
  (3) l.697–698's convention "`z_i dy/(y − y_i) = 0` if `y_i = 0`" should read `y_i = ∞`.
* `RegularComplete` (imported for (A)) had no `.olean` at the time of writing; this file was
  typechecked through a concatenation of `RegularComplete.lean` and this file
  (`lake env lean`), zero errors, zero warnings.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Causal.Flat
open Set TopologicalSpace Topology Filter Function
open scoped ENNReal NNReal unitInterval Pointwise

universe u

variable {d : ℕ}


/-! ### The gauge functions of a component `]α, β[` -/

section Gauge

variable {α β : EReal}

/-- `0` at an infinite lower end, `1` at a finite one. -/
noncomputable def gA (α : EReal) : ℝ := if α = ⊥ then 0 else 1

/-- `0` at an infinite upper end, `1` at a finite one. -/
noncomputable def gB (β : EReal) : ℝ := if β = ⊤ then 0 else 1

theorem gA_nonneg : 0 ≤ gA α := by unfold gA; split_ifs <;> norm_num
theorem gB_nonneg : 0 ≤ gB β := by unfold gB; split_ifs <;> norm_num
theorem gA_sq : gA α ^ 2 = gA α := by unfold gA; split_ifs <;> norm_num
theorem gB_sq : gB β ^ 2 = gB β := by unfold gB; split_ifs <;> norm_num

/-- The interval `]α, β[` of `ℝ`. -/
def gI (α β : EReal) : Set ℝ := {y : ℝ | α < y ∧ (y : EReal) < β}

theorem lt_of_gA_ne (hαβ : α < β) {y : ℝ} (hy : y ∈ gI α β) (h : gA α ≠ 0) : α.toReal < y := by
  have hα : α ≠ ⊥ := fun h' => h (by simp [gA, h'])
  have hα' : α ≠ ⊤ := ne_top_of_lt hαβ
  have := hy.1
  rw [← EReal.coe_toReal hα' hα] at this
  exact EReal.coe_lt_coe_iff.1 this

theorem lt_of_gB_ne (hαβ : α < β) {y : ℝ} (hy : y ∈ gI α β) (h : gB β ≠ 0) : y < β.toReal := by
  have hβ : β ≠ ⊤ := fun h' => h (by simp [gB, h'])
  have hβ' : β ≠ ⊥ := ne_bot_of_gt hαβ
  have := hy.2
  rw [← EReal.coe_toReal hβ hβ'] at this
  exact EReal.coe_lt_coe_iff.1 this

theorem mem_gI_of_gA (hA : gA α = 0) {y : ℝ} (hβ : (y : EReal) < β) :
    y ∈ gI α β := by
  have : α = ⊥ := by by_contra h; simp [gA, h] at hA
  exact ⟨by rw [this]; exact EReal.bot_lt_coe y, hβ⟩

theorem mem_gI_of_gB (hB : gB β = 0) {y : ℝ} (hα : α < y) : y ∈ gI α β := by
  have : β = ⊤ := by by_contra h; simp [gB, h] at hB
  exact ⟨hα, by rw [this]; exact EReal.coe_lt_top y⟩

theorem coe_lt_of_gB (hαβ : α < β) (hB : gB β ≠ 0) {y : ℝ} (hy : y < β.toReal) :
    (y : EReal) < β := by
  have hβ : β ≠ ⊤ := fun h' => hB (by simp [gB, h'])
  rw [← EReal.coe_toReal hβ (ne_bot_of_gt hαβ)]; exact EReal.coe_lt_coe_iff.2 hy

theorem lt_coe_of_gA (hαβ : α < β) (hA : gA α ≠ 0) {y : ℝ} (hy : α.toReal < y) :
    α < (y : EReal) := by
  have hα : α ≠ ⊥ := fun h' => hA (by simp [gA, h'])
  rw [← EReal.coe_toReal (ne_top_of_lt hαβ) hα]; exact EReal.coe_lt_coe_iff.2 hy

/-- **The gauge family** `c₀ y − gA/(c (y − a)^k) + gB/(c (b − y)^k)`: `f` is `(3/2, 2, 3)`,
`G` is `(1, 1, 1)`. -/
noncomputable def gauge (α β : EReal) (c₀ c : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  c₀ * y - gA α / (c * (y - α.toReal) ^ k) + gB β / (c * (β.toReal - y) ^ k)

/-- Its derivative. -/
noncomputable def gauge' (α β : EReal) (c₀ c : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  c₀ + k * gA α / (c * (y - α.toReal) ^ (k + 1)) + k * gB β / (c * (β.toReal - y) ^ (k + 1))

variable {c₀ c : ℝ} {k : ℕ}

theorem gauge_sub_ge (hαβ : α < β) (hc : 0 < c) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ gI α β)
    (h₂ : y₂ ∈ gI α β) (h : y₁ ≤ y₂) :
    c₀ * (y₂ - y₁) ≤ gauge α β c₀ c k y₂ - gauge α β c₀ c k y₁ := by
  have hA : gA α / (c * (y₂ - α.toReal) ^ k) ≤ gA α / (c * (y₁ - α.toReal) ^ k) := by
    by_cases hA : gA α = 0
    · simp [hA]
    have ha1 := lt_of_gA_ne hαβ h₁ hA
    refine div_le_div_of_nonneg_left gA_nonneg (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k) hc.le
  have hB : gB β / (c * (β.toReal - y₁) ^ k) ≤ gB β / (c * (β.toReal - y₂) ^ k) := by
    by_cases hB : gB β = 0
    · simp [hB]
    have hb2 := lt_of_gB_ne hαβ h₂ hB
    refine div_le_div_of_nonneg_left gB_nonneg (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k) hc.le
  simp only [gauge]
  nlinarith

theorem hasDerivAt_coef_div {ε : ℝ} {g : ℝ → ℝ} {g' y : ℝ} (hg : HasDerivAt g g' y)
    (h : ε ≠ 0 → g y ≠ 0) : HasDerivAt (fun y => ε / g y) (-(ε * g') / g y ^ 2) y := by
  by_cases hε : ε = 0
  · subst hε; simpa using hasDerivAt_const y (0 : ℝ)
  · have := (hasDerivAt_const y ε).div hg (h hε)
    have e : (0 * g y - ε * g') / g y ^ 2 = -(ε * g') / g y ^ 2 := by ring
    rw [e] at this
    exact this

theorem hasDerivAt_gauge (hαβ : α < β) (hc : 0 < c) {y : ℝ} (hy : y ∈ gI α β) :
    HasDerivAt (gauge α β c₀ c k) (gauge' α β c₀ c k y) y := by
  have h1 : HasDerivAt (fun y => c * (y - α.toReal) ^ k)
      (c * (k * (y - α.toReal) ^ (k - 1) * 1)) y :=
    (((hasDerivAt_id y).sub_const α.toReal).pow k).const_mul c
  have h2 : HasDerivAt (fun y => c * (β.toReal - y) ^ k)
      (c * (k * (β.toReal - y) ^ (k - 1) * (-1))) y :=
    (((hasDerivAt_id y).const_sub β.toReal).pow k).const_mul c
  have hA := hasDerivAt_coef_div (ε := gA α) h1 fun hA =>
    mul_ne_zero hc.ne' (pow_ne_zero _ (sub_ne_zero.2 (lt_of_gA_ne hαβ hy hA).ne'))
  have hB := hasDerivAt_coef_div (ε := gB β) h2 fun hB =>
    mul_ne_zero hc.ne' (pow_ne_zero _ (sub_ne_zero.2 (lt_of_gB_ne hαβ hy hB).ne'))
  have := (((hasDerivAt_id y).const_mul c₀).sub hA).add hB
  refine this.congr_deriv ?_
  simp only [gauge']
  have eA : k * gA α / (c * (y - α.toReal) ^ (k + 1)) =
      -(-(gA α * (c * (k * (y - α.toReal) ^ (k - 1) * 1))) / (c * (y - α.toReal) ^ k) ^ 2) := by
    by_cases hA : gA α = 0
    · simp [hA]
    have ha := sub_ne_zero.2 (lt_of_gA_ne hαβ hy hA).ne'
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have eB : k * gB β / (c * (β.toReal - y) ^ (k + 1)) =
      -(gB β * (c * (k * (β.toReal - y) ^ (k - 1) * (-1)))) / (c * (β.toReal - y) ^ k) ^ 2 := by
    by_cases hB : gB β = 0
    · simp [hB]
    have hb := sub_ne_zero.2 (lt_of_gB_ne hαβ hy hB).ne'
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      field_simp
      ring
  rw [eA, eB]; ring

theorem gauge_pieceA_mono (hαβ : α < β) (hc : 0 < c) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ gI α β)
    (h : y₁ ≤ y₂) :
    gA α / (c * (y₂ - α.toReal) ^ k) ≤ gA α / (c * (y₁ - α.toReal) ^ k) := by
  by_cases hA : gA α = 0
  · simp [hA]
  have ha1 := lt_of_gA_ne hαβ h₁ hA
  refine div_le_div_of_nonneg_left gA_nonneg (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k) hc.le

theorem gauge_pieceB_mono (hαβ : α < β) (hc : 0 < c) {y₁ y₂ : ℝ} (h₂ : y₂ ∈ gI α β)
    (h : y₁ ≤ y₂) :
    gB β / (c * (β.toReal - y₁) ^ k) ≤ gB β / (c * (β.toReal - y₂) ^ k) := by
  by_cases hB : gB β = 0
  · simp [hB]
  have hb2 := lt_of_gB_ne hαβ h₂ hB
  refine div_le_div_of_nonneg_left gB_nonneg (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k) hc.le

theorem gauge_sub_eq (y₁ y₂ : ℝ) :
    gauge α β c₀ c k y₂ - gauge α β c₀ c k y₁ = c₀ * (y₂ - y₁) +
      (gA α / (c * (y₁ - α.toReal) ^ k) - gA α / (c * (y₂ - α.toReal) ^ k)) +
      (gB β / (c * (β.toReal - y₂) ^ k) - gB β / (c * (β.toReal - y₁) ^ k)) := by
  simp only [gauge]; ring

theorem pow_le_self_of_le_one {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hk : 1 ≤ k) : δ ^ k ≤ δ := by
  calc δ ^ k ≤ δ ^ 1 := pow_le_pow_of_le_one h0 h1 hk
    _ = δ := pow_one δ

/-- **The gauge is unbounded above on `]α, β[`.** -/
theorem gauge_unbounded_above (hαβ : α < β) (hc₀ : 0 < c₀) (hc : 0 < c) (hk : 1 ≤ k) (C : ℝ) :
    ∃ y ∈ gI α β, C < gauge α β c₀ c k y := by
  obtain ⟨y₀, hy₀1, hy₀2⟩ := EReal.lt_iff_exists_real_btwn.1 hαβ
  have hy₀ : y₀ ∈ gI α β := ⟨hy₀1, hy₀2⟩
  by_cases hB : gB β = 0
  · set y := y₀ + (|C - gauge α β c₀ c k y₀| + 1) / c₀
    have hyy : y₀ ≤ y := by
      have : 0 ≤ (|C - gauge α β c₀ c k y₀| + 1) / c₀ := by positivity
      simp only [y]; linarith
    have hy : y ∈ gI α β := mem_gI_of_gB hB (hy₀1.trans_le (EReal.coe_le_coe_iff.2 hyy))
    refine ⟨y, hy, ?_⟩
    have h1 := gauge_sub_ge (c₀ := c₀) (k := k) hαβ hc hy₀ hy hyy
    have h2 : c₀ * (y - y₀) = |C - gauge α β c₀ c k y₀| + 1 := by
      simp only [y]; field_simp; ring
    linarith [le_abs_self (C - gauge α β c₀ c k y₀)]
  · have hb := lt_of_gB_ne hαβ hy₀ hB
    have hgB : gB β = 1 := by unfold gB at hB ⊢; split_ifs at hB ⊢ <;> simp_all
    set b := β.toReal
    set K := |C - gauge α β c₀ c k y₀| + gB β / (c * (b - y₀) ^ k) + 1
    have hK : 0 < K := by
      have : 0 ≤ gB β / (c * (b - y₀) ^ k) := div_nonneg gB_nonneg (by
        have : 0 < b - y₀ := by linarith
        positivity)
      positivity
    set δ := min 1 (min ((b - y₀) / 2) (1 / (c * K)))
    have hδ0 : 0 < δ := lt_min one_pos (lt_min (by linarith) (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ (b - y₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ ≤ 1 / (c * K) := (min_le_right _ _).trans (min_le_right _ _)
    set y := b - δ
    have hyy : y₀ ≤ y := by simp only [y]; linarith
    have hy : y ∈ gI α β := ⟨hy₀1.trans_le (EReal.coe_le_coe_iff.2 hyy),
      coe_lt_of_gB hαβ hB (by simp only [y]; linarith)⟩
    refine ⟨y, hy, ?_⟩
    have hsub := gauge_sub_eq (α := α) (β := β) (c₀ := c₀) (c := c) (k := k) y₀ y
    have hA := gauge_pieceA_mono (k := k) hαβ hc hy₀ hyy
    have hby : b - y = δ := by simp only [y]; ring
    rw [hby] at hsub
    have hdk : δ ^ k ≤ δ := pow_le_self_of_le_one hδ0.le hδ1 hk
    have hbig : K ≤ gB β / (c * δ ^ k) := by
      rw [hgB, le_div_iff₀ (by positivity)]
      calc K * (c * δ ^ k) ≤ K * (c * δ) := by gcongr
        _ = (c * K) * δ := by ring
        _ ≤ (c * K) * (1 / (c * K)) := by gcongr
        _ = 1 := by field_simp
    have : 0 ≤ c₀ * (y - y₀) := mul_nonneg hc₀.le (by linarith)
    simp only [K] at hbig
    linarith [le_abs_self (C - gauge α β c₀ c k y₀)]

/-- **The gauge is unbounded below on `]α, β[`.** -/
theorem gauge_unbounded_below (hαβ : α < β) (hc₀ : 0 < c₀) (hc : 0 < c) (hk : 1 ≤ k) (C : ℝ) :
    ∃ y ∈ gI α β, gauge α β c₀ c k y < C := by
  obtain ⟨y₀, hy₀1, hy₀2⟩ := EReal.lt_iff_exists_real_btwn.1 hαβ
  have hy₀ : y₀ ∈ gI α β := ⟨hy₀1, hy₀2⟩
  by_cases hA : gA α = 0
  · set y := y₀ - (|gauge α β c₀ c k y₀ - C| + 1) / c₀
    have hyy : y ≤ y₀ := by
      have : 0 ≤ (|gauge α β c₀ c k y₀ - C| + 1) / c₀ := by positivity
      simp only [y]; linarith
    have hy : y ∈ gI α β := mem_gI_of_gA hA ((EReal.coe_le_coe_iff.2 hyy).trans_lt hy₀2)
    refine ⟨y, hy, ?_⟩
    have h1 := gauge_sub_ge (c₀ := c₀) (k := k) hαβ hc hy hy₀ hyy
    have h2 : c₀ * (y₀ - y) = |gauge α β c₀ c k y₀ - C| + 1 := by
      simp only [y]; field_simp; ring
    linarith [le_abs_self (gauge α β c₀ c k y₀ - C)]
  · have ha := lt_of_gA_ne hαβ hy₀ hA
    have hgA : gA α = 1 := by unfold gA at hA ⊢; split_ifs at hA ⊢ <;> simp_all
    set a := α.toReal
    set K := |gauge α β c₀ c k y₀ - C| + gA α / (c * (y₀ - a) ^ k) + 1
    have hK : 0 < K := by
      have : 0 ≤ gA α / (c * (y₀ - a) ^ k) := div_nonneg gA_nonneg (by
        have : 0 < y₀ - a := by linarith
        positivity)
      positivity
    set δ := min 1 (min ((y₀ - a) / 2) (1 / (c * K)))
    have hδ0 : 0 < δ := lt_min one_pos (lt_min (by linarith) (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ (y₀ - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ ≤ 1 / (c * K) := (min_le_right _ _).trans (min_le_right _ _)
    set y := a + δ
    have hyy : y ≤ y₀ := by simp only [y]; linarith
    have hy : y ∈ gI α β := ⟨lt_coe_of_gA hαβ hA (by simp only [y]; linarith),
      (EReal.coe_le_coe_iff.2 hyy).trans_lt hy₀2⟩
    refine ⟨y, hy, ?_⟩
    have hsub := gauge_sub_eq (α := α) (β := β) (c₀ := c₀) (c := c) (k := k) y y₀
    have hB := gauge_pieceB_mono (k := k) hαβ hc hy₀ hyy
    have hay : y - a = δ := by simp only [y]; ring
    rw [hay] at hsub
    have hdk : δ ^ k ≤ δ := pow_le_self_of_le_one hδ0.le hδ1 hk
    have hbig : K ≤ gA α / (c * δ ^ k) := by
      rw [hgA, le_div_iff₀ (by positivity)]
      calc K * (c * δ ^ k) ≤ K * (c * δ) := by gcongr
        _ = (c * K) * δ := by ring
        _ ≤ (c * K) * (1 / (c * K)) := by gcongr
        _ = 1 := by field_simp
    have : 0 ≤ c₀ * (y₀ - y) := mul_nonneg hc₀.le (by linarith)
    simp only [K] at hbig
    linarith [le_abs_self (gauge α β c₀ c k y₀ - C)]

theorem continuousOn_gauge (hαβ : α < β) (hc : 0 < c) :
    ContinuousOn (gauge α β c₀ c k) (gI α β) := fun _ hy =>
  (hasDerivAt_gauge (c₀ := c₀) (k := k) hαβ hc hy).continuousAt.continuousWithinAt

theorem continuousOn_coef_div {ε : ℝ} {g : ℝ → ℝ} {s : Set ℝ} (hg : ContinuousOn g s)
    (h : ε ≠ 0 → ∀ y ∈ s, g y ≠ 0) : ContinuousOn (fun y => ε / g y) s := by
  by_cases hε : ε = 0
  · subst hε; simpa using continuousOn_const
  · exact continuousOn_const.div hg (h hε)

theorem continuousOn_gauge' (hαβ : α < β) (hc : 0 < c) :
    ContinuousOn (gauge' α β c₀ c k) (gI α β) := by
  refine (continuousOn_const.add ?_).add ?_
  · simp only [mul_div_assoc]
    refine continuousOn_const.mul (continuousOn_coef_div (by fun_prop) fun hA y hy =>
      mul_ne_zero hc.ne' (pow_ne_zero _ (sub_ne_zero.2 (lt_of_gA_ne hαβ hy hA).ne')))
  · simp only [mul_div_assoc]
    refine continuousOn_const.mul (continuousOn_coef_div (by fun_prop) fun hB y hy =>
      mul_ne_zero hc.ne' (pow_ne_zero _ (sub_ne_zero.2 (lt_of_gB_ne hαβ hy hB).ne')))

/-- `f := gauge (3/2) 2 3`, `G := gauge 1 1 1`: **`G'² ≤ 2 f'`**. -/
theorem gauge'_sq_le (y : ℝ) :
    gauge' α β 1 1 1 y ^ 2 ≤ 2 * gauge' α β (3 / 2) 2 3 y := by
  simp only [gauge']
  set A := gA α / (y - α.toReal) ^ 2
  set B := gB β / (β.toReal - y) ^ 2
  have eA : (1 : ℕ) * gA α / (1 * (y - α.toReal) ^ (1 + 1)) = A := by simp [A]
  have eB : (1 : ℕ) * gB β / (1 * (β.toReal - y) ^ (1 + 1)) = B := by simp [B]
  have eA' : ((3 : ℕ) : ℝ) * gA α / (2 * (y - α.toReal) ^ (3 + 1)) = 3 / 2 * A ^ 2 := by
    have e : (y - α.toReal) ^ (3 + 1) = ((y - α.toReal) ^ 2) ^ 2 := by ring
    simp only [A, div_pow, gA_sq, e]
    generalize (y - α.toReal) ^ 2 = u
    push_cast; ring
  have eB' : ((3 : ℕ) : ℝ) * gB β / (2 * (β.toReal - y) ^ (3 + 1)) = 3 / 2 * B ^ 2 := by
    have e : (β.toReal - y) ^ (3 + 1) = ((β.toReal - y) ^ 2) ^ 2 := by ring
    simp only [B, div_pow, gB_sq, e]
    generalize (β.toReal - y) ^ 2 = u
    push_cast; ring
  rw [eA, eB, eA', eB']
  nlinarith [sq_nonneg (A - 1), sq_nonneg (B - 1), sq_nonneg (A - B)]

theorem one_le_gauge' (y : ℝ) : 1 ≤ gauge' α β 1 1 1 y := by
  simp only [gauge']
  have h1 : 0 ≤ ((1 : ℕ) : ℝ) * gA α / (1 * (y - α.toReal) ^ (1 + 1)) :=
    div_nonneg (mul_nonneg (by norm_num) gA_nonneg) (by rw [one_mul]; exact pow_two_nonneg _)
  have h2 : 0 ≤ ((1 : ℕ) : ℝ) * gB β / (1 * (β.toReal - y) ^ (1 + 1)) :=
    div_nonneg (mul_nonneg (by norm_num) gB_nonneg) (by rw [one_mul]; exact pow_two_nonneg _)
  linarith

end Gauge



section Chord

variable {ℓ : Fin d → ℝ} {f : ℝ → ℝ} {α β : EReal}

theorem nullX_sub (p q : Minkowski (d + 1)) : nullX (q - p) = nullX q - nullX p := by
  simp only [nullX, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullY_sub (p q : Minkowski (d + 1)) : nullY (q - p) = nullY q - nullY p := by
  simp only [nullY, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]; ring

theorem nullZ_sub_apply (p q : Minkowski (d + 1)) (i : Fin d) :
    nullZ (q - p) i = nullZ q i - nullZ p i := by
  simp [nullZ]

/-- The coordinate `ζᵢ = zᵢ / (1 + yλᵢ)` of `S_f` (l.720–735: `zᵢ/(y − yᵢ)` up to `−λᵢ`). -/
noncomputable def zeta (ℓ : Fin d → ℝ) (i : Fin d) (p : Minkowski (d + 1)) : ℝ :=
  nullZ p i / (1 + nullY p * ℓ i)

theorem nullZ_eq_mul_zeta (hℓ : IsUnipComponent ℓ α β) {p : Minkowski (d + 1)}
    (hp : p ∈ unipDomain (d := d) α β) (i : Fin d) :
    nullZ p i = (1 + nullY p * ℓ i) * zeta ℓ i p := by
  rw [zeta, mul_div_cancel₀ _ (hℓ.2.1 _ hp.1 hp.2 i)]

/-- On `S_f`, `x = f(y) − ½ ∑ λᵢ (1 + yλᵢ) ζᵢ²`. -/
theorem nullX_eq_of_mem_unipSlice (hℓ : IsUnipComponent ℓ α β) {p : Minkowski (d + 1)}
    (hp : p ∈ unipSlice ℓ f α β) :
    nullX p = f (nullY p) - 1 / 2 * ∑ i, ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2 := by
  rw [hp.2, unipPhi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nullZ_eq_mul_zeta hℓ hp.1 i]
  have := hℓ.2.1 _ hp.1.1 hp.1.2 i
  field_simp

/-- **The chord identity of `S_f`**: for `p, q ∈ S_f`,
`|q − p|² = 2 Δy Δf + ∑ᵢ (1 + y(p)λᵢ)(1 + y(q)λᵢ) (Δζᵢ)²` (the metric `2f′ dy² + ∑ sᵢ² dζᵢ²`,
l.720–735, at the level of chords). -/
theorem minkQ_sub_of_mem_unipSlice (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipSlice ℓ f α β) (hq : q ∈ unipSlice ℓ f α β) :
    minkQ (q - p) = 2 * (nullY q - nullY p) * (f (nullY q) - f (nullY p)) +
      ∑ i, (1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) * (zeta ℓ i q - zeta ℓ i p) ^ 2 := by
  rw [minkQ_eq_null, nullX_sub, nullY_sub, EuclideanSpace.norm_sq_eq,
    nullX_eq_of_mem_unipSlice hℓ hp, nullX_eq_of_mem_unipSlice hℓ hq]
  simp only [Real.norm_eq_abs, sq_abs, nullZ_sub_apply]
  have key : ∀ i, (nullZ q i - nullZ p i) ^ 2 = (1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) *
      (zeta ℓ i q - zeta ℓ i p) ^ 2 + (nullY q - nullY p) *
      (ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 - ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2) :=
    fun i => by
      rw [nullZ_eq_mul_zeta hℓ hp.1 i, nullZ_eq_mul_zeta hℓ hq.1 i]; ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  ring

end Chord



section UnipGH

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- **The slab `Ω = {α < y < β}` is globally hyperbolic in `𝐌ⁿ`**: it is convex and causally
convex (`y` is non-increasing along `≤`), so its diamonds are those of `𝐌ⁿ`. -/
theorem globallyHyperbolicOn_unipDomain :
    (minkowski (d + 1)).GloballyHyperbolicOn (unipDomain (d := d) α β) := by
  refine ⟨fun x y hxy hyx => minkowski_isCausal ((minkowski (d + 1)).le_mono le_top hxy)
    ((minkowski (d + 1)).le_mono le_top hyx), fun p q => ?_⟩
  by_cases hpq : p ∈ unipDomain (d := d) α β ∧ q ∈ unipDomain (d := d) α β
  · have : (minkowski (d + 1)).diamond (unipDomain α β) p q =
        (minkowski (d + 1)).diamond ⊤ p q := by
      ext x
      simp only [Causality.mem_diamond, le_iff_of_convex convex_unipDomain]
      constructor
      · rintro ⟨⟨-, -, h1⟩, -, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        have hy1 := (null_le_of_le_top h1).1
        have hy2 := (null_le_of_le_top h2).1
        have hx : x ∈ unipDomain (d := d) α β :=
          ⟨hpq.2.1.trans_le (EReal.coe_le_coe_iff.2 hy2),
            (EReal.coe_le_coe_iff.2 hy1).trans_lt hpq.1.2⟩
        exact ⟨⟨hpq.1, hx, h1⟩, hx, hpq.2, h2⟩
    rw [this]
    exact minkowski_globallyHyperbolic.2 p q
  · have : (minkowski (d + 1)).diamond (unipDomain α β) p q = ∅ := by
      ext x
      simp only [Causality.mem_diamond, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact hpq ⟨(minkowski (d + 1)).le_mem_left h1, (minkowski (d + 1)).le_mem_right h2⟩
    rw [this]
    exact isCompact_empty

end UnipGH


section UnipGroup

variable {ℓ : Fin d → ℝ} {α β : EReal}

theorem norm_le_sum_abs (t : EuclideanSpace ℝ (Fin d)) : ‖t‖ ≤ ∑ i, |t i| := by
  have h : t = ∑ i, EuclideanSpace.single i (t i) := by
    ext j; simp
  calc ‖t‖ = ‖∑ i, EuclideanSpace.single i (t i)‖ := by rw [← h]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (t i)‖ := norm_sum_le _ _
    _ = ∑ i, |t i| := by simp

theorem nullZ_unipAction_apply (ℓ : Fin d → ℝ) (t : EuclideanSpace ℝ (Fin d))
    (p : Minkowski (d + 1)) (i : Fin d) :
    nullZ (unipAction ℓ t p) i = nullZ p i + t i * (1 + nullY p * ℓ i) := by
  simp [unipAction, nullZ_ofNull]

theorem unipAction_zero (ℓ : Fin d → ℝ) (p : Minkowski (d + 1)) : unipAction ℓ 0 p = p := by
  refine eq_of_null ?_ ?_ ?_
  · simp [unipAction, nullX_ofNull]
  · simp [unipAction, nullY_ofNull]
  · intro i; simp [unipAction, nullZ_ofNull]

theorem nullY_zero' : nullY (0 : Minkowski (d + 1)) = 0 := by simp [nullY]

theorem nullZ_zero' : nullZ (0 : Minkowski (d + 1)) = 0 := by ext i; simp [nullZ]

/-- The translation parameter of an element of `A` is read at the origin. -/
theorem eq_nullZ_smul_zero {γ : isom (d + 1)} {t : EuclideanSpace ℝ (Fin d)}
    (h : ∀ p, γ • p = unipAction ℓ t p) : t = nullZ (γ • (0 : Minkowski (d + 1))) := by
  ext i
  rw [h, nullZ_unipAction_apply, nullZ_zero', nullY_zero']
  simp

/-- An isometry acting as `unipAction ℓ t` is determined by `t`. -/
theorem isom_eq_of_unipAction {γ γ' : isom (d + 1)} {t : EuclideanSpace ℝ (Fin d)}
    (h : ∀ p, γ • p = unipAction ℓ t p) (h' : ∀ p, γ' • p = unipAction ℓ t p) : γ = γ' :=
  Causal.eq_of_eqOn (X := Minkowski (d + 1)) isOpen_univ univ_nonempty fun p _ => by
    simp only [h, h']

variable (Γ : Subgroup (isom (d + 1))) (L : AddSubgroup (EuclideanSpace ℝ (Fin d)))

/-- `Ω` is invariant under a group acting through `A`. -/
theorem unip_invariant (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p) :
    FlatQuotient.Invariant Γ (unipDomain (d := d) α β) :=
  ⟨fun γ p hp => by
    obtain ⟨t, -, ht⟩ := hΓ γ γ.2
    rw [ht]; exact unipAction_mem_unipDomain ℓ t hp⟩

/-- A group acting through `A` acts freely on `Ω`. -/
theorem unip_isCancelSMul (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    [FlatQuotient.Invariant Γ (unipDomain (d := d) α β)] :
    IsCancelSMul Γ (unipDomain (d := d) α β) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ p hp
  obtain ⟨t, -, ht⟩ := hΓ γ hγ
  have hpv := congrArg Subtype.val hp
  simp only [FlatQuotient.coe_smul] at hpv
  rw [ht] at hpv
  have ht0 : t = 0 := by
    ext i
    have h1 := congrArg (fun q => nullZ q i) hpv
    simp only [nullZ_unipAction_apply] at h1
    have h2 := hℓ.2.1 _ p.2.1 p.2.2 i
    have : t i * (1 + nullY (p : Minkowski (d + 1)) * ℓ i) = 0 := by linarith
    simpa [h2] using this
  subst ht0
  apply Subtype.ext
  exact isom_eq_of_unipAction (ℓ := ℓ) ht fun q => by
    rw [unipAction_zero]; exact one_smul _ q

variable [BallFinite L]

/-- Only finitely many elements have a bounded translation parameter. -/
theorem unip_finite_of_bound (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p) (R : ℝ) :
    {γ : Γ | ‖nullZ ((γ : isom (d + 1)) • (0 : Minkowski (d + 1)))‖ ≤ R}.Finite := by
  set F : Γ → EuclideanSpace ℝ (Fin d) := fun γ => nullZ ((γ : isom (d + 1)) • 0)
  have hF : InjOn F univ := by
    rintro ⟨γ, hγ⟩ - ⟨γ', hγ'⟩ - he
    obtain ⟨t, -, ht⟩ := hΓ γ hγ
    obtain ⟨t', -, ht'⟩ := hΓ γ' hγ'
    have e1 := eq_nullZ_smul_zero ht
    have e2 := eq_nullZ_smul_zero ht'
    have htt : t = t' := by rw [e1, e2]; exact he
    subst htt
    exact Subtype.ext (isom_eq_of_unipAction ht ht')
  refine ((BallFinite.finite_ball (Λ := L) R).preimage (hF.mono (subset_univ _))).subset ?_
  rintro ⟨γ, hγ⟩ hR
  obtain ⟨t, htL, ht⟩ := hΓ γ hγ
  refine ⟨?_, hR⟩
  change nullZ (γ • 0) ∈ L
  rw [← eq_nullZ_smul_zero ht]; exact htL


/-- **A group acting through `A` acts properly discontinuously on `Ω`** (`L` ball-finite):
`t (1 + yλ) = z(γp) − z(p)` is bounded on compact sets, since `1 + yλᵢ` stays away from `0`. -/
theorem unip_properlyDiscontinuousSMul (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    [FlatQuotient.Invariant Γ (unipDomain (d := d) α β)] :
    ProperlyDiscontinuousSMul Γ (unipDomain (d := d) α β) := by
  refine ⟨fun {K K'} hK hK' => ?_⟩
  have hz : ∀ i, Continuous fun q : unipDomain (d := d) α β => |nullZ (q : Minkowski (d + 1)) i| :=
    fun i => (((EuclideanSpace.proj i.succ).continuous.comp continuous_snd).comp
      continuous_subtype_val).abs
  have hs : ∀ i, Continuous fun q : unipDomain (d := d) α β =>
      |1 + nullY (q : Minkowski (d + 1)) * ℓ i| := fun i =>
    (continuous_const.add ((continuous_nullY.comp continuous_subtype_val).mul continuous_const)).abs
  choose R hR using fun i => hK.exists_bound_of_continuousOn (hz i).continuousOn
  choose R' hR' using fun i => hK'.exists_bound_of_continuousOn (hz i).continuousOn
  have hc : ∀ i, ∃ c > 0, ∀ q ∈ K, c ≤ |1 + nullY (q : Minkowski (d + 1)) * ℓ i| := fun i => by
    rcases K.eq_empty_or_nonempty with hKe | hKn
    · exact ⟨1, one_pos, by simp [hKe]⟩
    obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hKn (hs i).continuousOn
    refine ⟨|1 + nullY (q₀ : Minkowski (d + 1)) * ℓ i|,
      abs_pos.2 (hℓ.2.1 _ q₀.2.1 q₀.2.2 i), fun q hq => hmin hq⟩
  choose c hc0 hcK using hc
  refine (unip_finite_of_bound Γ L hΓ (∑ i, (R' i + R i) / c i)).subset ?_
  rintro ⟨γ, hγ⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  obtain ⟨t, -, ht⟩ := hΓ γ hγ
  change ‖nullZ (γ • (0 : Minkowski (d + 1)))‖ ≤ _
  rw [← eq_nullZ_smul_zero ht]
  refine (norm_le_sum_abs t).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := hR i k hk
  have h2 := hR' i _ hl
  simp only [Real.norm_eq_abs, abs_abs, FlatQuotient.coe_smul, ht, nullZ_unipAction_apply] at h1 h2
  have h3 := hcK i k hk
  rw [le_div_iff₀ (hc0 i)]
  have h4 : |t i| * c i ≤ |t i * (1 + nullY (k : Minkowski (d + 1)) * ℓ i)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have h5 : t i * (1 + nullY (k : Minkowski (d + 1)) * ℓ i) =
      (nullZ (k : Minkowski (d + 1)) i + t i * (1 + nullY (k : Minkowski (d + 1)) * ℓ i)) -
        nullZ (k : Minkowski (d + 1)) i := by ring
  rw [h5] at h4
  have h6 := abs_sub _ _ |>.trans (add_le_add h2 h1)
  linarith [abs_sub (nullZ (k : Minkowski (d + 1)) i + t i * (1 + nullY (k : Minkowski (d + 1)) * ℓ i))
    (nullZ (k : Minkowski (d + 1)) i)]

theorem unip_t_bound_aux {sx sy u D zx zy zq t : ℝ} (hpos : 0 < sx * sy) (hu : 0 < u)
    (hE : (sx * zq - sy * zx) ^ 2 / (sx * sy * u) ≤ 2 * D) (hzq : zq = zy + t * sy) :
    |t| ≤ (√(2 * |D| * |sx * sy| * |u|) + |sy * zx| + |sx * zy|) / |sx * sy| := by
  have hpu : 0 < sx * sy * u := mul_pos hpos hu
  rw [div_le_iff₀ hpu] at hE
  have hD : 0 ≤ D := by nlinarith [sq_nonneg (sx * zq - sy * zx)]
  have hsq : (sx * zq - sy * zx) ^ 2 ≤ 2 * |D| * |sx * sy| * |u| := by
    rw [abs_of_nonneg hD, abs_of_pos hu, abs_of_pos hpos]; linarith
  have habs := Real.abs_le_sqrt hsq
  have hti : t = ((sx * zq - sy * zx) + sy * zx - sx * zy) / (sx * sy) := by
    rw [eq_div_iff hpos.ne', hzq]; ring
  rw [hti, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  have h1 := abs_sub ((sx * zq - sy * zx) + sy * zx) (sx * zy)
  have h2 := abs_add_le (sx * zq - sy * zx) (sy * zx)
  linarith

theorem unip_t_bound_aux' {sy zx zy t : ℝ} (hsy : sy ≠ 0) (h : zy + t * sy = zx) :
    |t| ≤ (|zx| + |zy|) / |sy| := by
  have hti : t = (zx - zy) / sy := by rw [eq_div_iff hsy]; linarith
  rw [hti, abs_div]
  exact div_le_div_of_nonneg_right (abs_sub _ _) (abs_nonneg _)

/-- **Only finitely many `γ` have `x ≤ γ y`** (the hypothesis of ETT's GH of the quotient):
through the time function `T = x − Φ(y, z)` for `f = 0`, which is `A`-invariant, the third term
of `unipTime_sub` bounds `(1 + y(x)λᵢ) z(γy) − (1 + y(y)λᵢ) z(x)`, hence the parameter `t`. -/
theorem unip_finite_le (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    [FlatQuotient.Invariant Γ (unipDomain (d := d) α β)] (x y : unipDomain (d := d) α β) :
    {γ : Γ | (flatCausality (d + 1) (unipDomain (d := d) α β)).le ⊤ x (γ • y)}.Finite := by
  obtain ⟨X, hXd⟩ : ∃ X : Minkowski (d + 1), X = x := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : Minkowski (d + 1), Y = y := ⟨_, rfl⟩
  have hxΩ : X ∈ unipDomain (d := d) α β := hXd ▸ x.2
  have hyΩ : Y ∈ unipDomain (d := d) α β := hYd ▸ y.2
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = unipTime ℓ (fun _ : ℝ => (0 : ℝ)) Y -
      unipTime ℓ (fun _ : ℝ => (0 : ℝ)) X := ⟨_, rfl⟩
  refine (unip_finite_of_bound Γ L hΓ (∑ i,
    ((√(2 * |D| * |(1 + nullY X * ℓ i) * (1 + nullY Y * ℓ i)| * |nullY X - nullY Y|) +
      |(1 + nullY Y * ℓ i) * nullZ X i| + |(1 + nullY X * ℓ i) * nullZ Y i|) /
        |(1 + nullY X * ℓ i) * (1 + nullY Y * ℓ i)| +
      (|nullZ X i| + |nullZ Y i|) / |1 + nullY Y * ℓ i|))).subset ?_
  rintro ⟨γ, hγ⟩ hle
  obtain ⟨t, -, ht⟩ := hΓ γ hγ
  change ‖nullZ (γ • (0 : Minkowski (d + 1)))‖ ≤ _
  rw [← eq_nullZ_smul_zero ht]
  have hle' : (minkowski (d + 1)).le ⊤ X (unipAction ℓ t Y) := by
    have := (minkowski (d + 1)).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
    rw [hXd, hYd]
    simpa only [FlatQuotient.coe_smul, ht] using this
  have hqΩ : unipAction ℓ t Y ∈ unipDomain (d := d) α β := unipAction_mem_unipDomain ℓ t hyΩ
  have hyq : nullY (unipAction ℓ t Y) = nullY Y := nullY_unipAction ℓ t Y
  have hzq : ∀ i, nullZ (unipAction ℓ t Y) i = nullZ Y i + t i * (1 + nullY Y * ℓ i) :=
    fun i => nullZ_unipAction_apply ℓ t Y i
  refine (norm_le_sum_abs t).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨hY, -, -⟩ := null_le_of_le_top hle'
  rw [hyq] at hY
  have hB2 : 0 ≤ (|nullZ X i| + |nullZ Y i|) / |1 + nullY Y * ℓ i| := by positivity
  have hB1 : 0 ≤ (√(2 * |D| * |(1 + nullY X * ℓ i) * (1 + nullY Y * ℓ i)| * |nullY X - nullY Y|) +
      |(1 + nullY Y * ℓ i) * nullZ X i| + |(1 + nullY X * ℓ i) * nullZ Y i|) /
        |(1 + nullY X * ℓ i) * (1 + nullY Y * ℓ i)| := by positivity
  rcases hY.lt_or_eq with hlt | heq
  · -- `y(y) < y(x)`: the third term of `unipTime_sub`
    have hlt' : nullY (unipAction ℓ t Y) < nullY X := by rw [hyq]; exact hlt
    have hdec := unipTime_sub (f := fun _ : ℝ => (0 : ℝ)) hℓ hxΩ hqΩ hlt'
    have hTq := unipTime_unipAction ℓ (fun _ : ℝ => (0 : ℝ)) hℓ t hyΩ
    have hu : 0 < nullY X - nullY Y := sub_pos.2 hlt
    obtain ⟨-, hX, hZ⟩ := null_le_of_le_top hle'
    rw [hyq] at hZ hdec
    rw [hTq, ← hD] at hdec
    have hE : ∀ j, 0 ≤ ((1 + nullY X * ℓ j) * nullZ (unipAction ℓ t Y) j -
        (1 + nullY Y * ℓ j) * nullZ X j) ^ 2 /
        ((1 + nullY X * ℓ j) * (1 + nullY Y * ℓ j) * (nullY X - nullY Y)) := fun j =>
      div_nonneg (sq_nonneg _) (mul_pos (unip_mul_pos hℓ hxΩ.1 hxΩ.2 hyΩ.1 hyΩ.2 j) hu).le
    have hA : 0 ≤ (nullX (unipAction ℓ t Y) - nullX X) -
        (∑ j, (nullZ (unipAction ℓ t Y) j - nullZ X j) ^ 2) / (2 * (nullY X - nullY Y)) := by
      rw [sub_nonneg, div_le_iff₀ (by positivity)]; linarith
    have hEi := Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)
    have hEi' : ((1 + nullY X * ℓ i) * nullZ (unipAction ℓ t Y) i -
        (1 + nullY Y * ℓ i) * nullZ X i) ^ 2 /
        ((1 + nullY X * ℓ i) * (1 + nullY Y * ℓ i) * (nullY X - nullY Y)) ≤ 2 * D := by
      simp only [sub_self, add_zero] at hdec
      linarith
    have := unip_t_bound_aux (unip_mul_pos hℓ hxΩ.1 hxΩ.2 hyΩ.1 hyΩ.2 i) hu hEi' (hzq i)
    linarith
  · -- `y(y) = y(x)`: `z` is constant along the null segment
    have heq' : nullY (unipAction ℓ t Y) = nullY X := by rw [hyq]; exact heq
    obtain ⟨hz, -⟩ := unipTime_sub_of_nullY_eq (ℓ := ℓ) (f := fun _ : ℝ => (0 : ℝ)) hle' heq'
    have h1 := congrArg (fun v => v i) hz
    simp only at h1
    rw [hzq] at h1
    have := unip_t_bound_aux' (hℓ.2.1 _ hyΩ.1 hyΩ.2 i) h1
    linarith

end UnipGroup

/-! ### Transport along an `IsQuotientOf` presentation

Copies of `Classification`'s `IsLocalIsometry.of_comp_right` and
`globallyHyperbolic_of_isIsometricEmbedding_of_surjective` (that module imports this one's
consumers, so it cannot be imported). -/

section Transport

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- **Descending a local isometry along a surjective local isometry** (copy of
`Classification.IsLocalIsometry.of_comp_right`). -/
theorem unip_isLocalIsometry_of_comp_right {q : X → M} {f : M → N} (hq : IsLocalIsometry d q)
    (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) : IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

variable [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))]

/-- **GH transports along a surjective isometric embedding** (copy of `Classification`'s). -/
theorem unip_globallyHyperbolic_of_surjective {f : M → N}
    (hf : IsIsometricEmbedding d f) (hs : Surjective f)
    (hM : (flatCausality d M).GloballyHyperbolic) : (flatCausality d N).GloballyHyperbolic := by
  have hrel : ∀ x y : M, (flatCausality d M).le ⊤ x y ↔ (flatCausality d N).le ⊤ (f x) (f y) :=
    fun x y => (hf.rel_iff ⊤ ⊤ (by rw [Opens.coe_top, Opens.coe_top, image_univ, hs.range_eq])
      x y).1
  refine ⟨fun x y hxy hyx => ?_, fun p q => ?_⟩
  · obtain ⟨x, rfl⟩ := hs x
    obtain ⟨y, rfl⟩ := hs y
    exact congrArg f (hM.1 ((hrel x y).2 hxy) ((hrel y x).2 hyx))
  · obtain ⟨p, rfl⟩ := hs p
    obtain ⟨q, rfl⟩ := hs q
    have heq : (flatCausality d N).diamond ⊤ (f p) (f q) =
        f '' (flatCausality d M).diamond ⊤ p q := by
      ext z
      obtain ⟨z, rfl⟩ := hs z
      rw [Causality.mem_diamond]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨z, Causality.mem_diamond.2 ⟨(hrel p z).2 h1, (hrel z q).2 h2⟩, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hw
        rw [← hwz]
        exact ⟨(hrel p w).1 h1, (hrel w q).1 h2⟩
    rw [heq]
    exact (hM.2 p q).image hf.1.continuous

end Transport

/-- **The homeomorphism of an `IsQuotientOf` presentation is an isometric embedding.** -/
theorem unip_isIsometricEmbedding_homeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    [FlatQuotient.Invariant Γ Ω] [ProperlyDiscontinuousSMul Γ Ω] [IsCancelSMul Γ Ω]
    {π : Ω → M} (hloc : IsLocalIsometry d π) (Φ : FlatQuotient Γ Ω ≃ₜ M)
    (hΦ : ∀ x, Φ (FlatQuotient.proj Γ Ω x) = π x) : IsIsometricEmbedding d Φ :=
  ⟨unip_isLocalIsometry_of_comp_right (FlatQuotient.isLocalIsometry_proj _ _)
    (FlatQuotient.proj_surjective _ _) (by rw [show Φ ∘ _ = π from funext hΦ]; exact hloc),
    Φ.injective⟩

/-- **[3.U] Unipotent spacetimes are GH in ETT's sense** (causal, compact diamonds;
l.743–744, "the quotient of `Ω` by `Γ` is globally hyperbolic"): the slab is GH in `𝐌ⁿ`
(`globallyHyperbolicOn_unipDomain`), the action is acausal (`actsAcausally_unip`) and finitely
related (`unip_finite_le`), so `FlatQuotient.gh_toFlatSpacetime` applies in the frame `φ`
(`gh_frameConj`), and the homeomorphism of the presentation transports it to `M`. -/
theorem gh_of_isUnipotentSpacetime {M : FlatSpacetime.{u} (d + 1)} (hU : IsUnipotentSpacetime M) :
    GH M := by
  obtain ⟨φ, ℓ, α, β, L, Γ, hL, hℓ, hΓ, -, hq⟩ := hU
  haveI := hL
  haveI := unip_invariant (α := α) (β := β) Γ L hΓ
  haveI := unip_isCancelSMul Γ L hℓ hΓ
  haveI := unip_properlyDiscontinuousSMul Γ L hℓ hΓ
  have hΓ' : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p := fun γ hγ =>
    let ⟨t, _, ht⟩ := hΓ γ hγ; ⟨t, ht⟩
  have hconn := isConnected_isomImage φ _ (isConnected_unipDomain (d := d) hℓ.1)
  have hGH := gh_frameConj φ Γ (unipDomain (d := d) α β) _ rfl hconn
    (actsAcausally_unip Γ hℓ hΓ') globallyHyperbolicOn_unipDomain (unip_finite_le Γ L hℓ hΓ)
  obtain ⟨π, -, hloc, Φ, hΦ⟩ := hq.exists_homeomorph
  exact unip_globallyHyperbolic_of_surjective
    (unip_isIsometricEmbedding_homeomorph hloc Φ hΦ) Φ.surjective hGH


/-! ### The slice `S_f` for the gauge `f = gauge (3/2) 2 3` -/

section Slice

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- **The function `f`** (Barbot's `f = ∫ a²`, l.705–711, made explicit):
`f(y) = (3/2) y − [α finite]/(2 (y − α)³) + [β finite]/(2 (β − y)³)`. -/
noncomputable abbrev unipF (α β : EReal) : ℝ → ℝ := gauge α β (3 / 2) 2 3

/-- **The length gauge `G`** (Barbot's `∫ a`, l.712–720): `G' ≤ √(2 f')`, `G' ≥ 1`, `G` is
unbounded at both ends. -/
noncomputable abbrev unipG (α β : EReal) : ℝ → ℝ := gauge α β 1 1 1

/-- **The hypersurface** `S = S_f` of the component (`unipSlice` for `f = unipF`). -/
abbrev unipS (ℓ : Fin d → ℝ) (α β : EReal) : Set (Minkowski (d + 1)) :=
  unipSlice ℓ (unipF α β) α β

theorem unipF_strictMonoOn (hαβ : α < β) : StrictMonoOn (unipF α β) (gI α β) := by
  intro y₁ h₁ y₂ h₂ h
  have := gauge_sub_ge (c₀ := 3 / 2) (k := 3) hαβ (by norm_num : (0 : ℝ) < 2) h₁ h₂ h.le
  linarith

/-- The hypotheses of `isCauchySurfaceOn_unipSlice` for `f = unipF`. -/
theorem isCauchySurfaceOn_unipS (hℓ : IsUnipComponent ℓ α β) :
    (minkowski (d + 1)).IsCauchySurfaceOn (unipDomain α β) (unipS ℓ α β) :=
  isCauchySurfaceOn_unipSlice ℓ _ hℓ (unipF_strictMonoOn hℓ.1)
    (continuousOn_gauge hℓ.1 (by norm_num))
    (fun C => by
      obtain ⟨y, hy, h⟩ := gauge_unbounded_below (c₀ := 3 / 2) (c := 2) (k := 3) hℓ.1
        (by norm_num) (by norm_num) (by norm_num) C
      exact ⟨y, hy.1, hy.2, h⟩)
    (fun C => by
      obtain ⟨y, hy, h⟩ := gauge_unbounded_above (c₀ := 3 / 2) (c := 2) (k := 3) hℓ.1
        (by norm_num) (by norm_num) (by norm_num) C
      exact ⟨y, hy.1, hy.2, h⟩)

/-- **`S` is acausal in `𝐌ⁿ`** (`T = x − Φ` strictly increases along `≤` in `Ω`). -/
theorem eq_of_le_of_mem_unipS (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipS ℓ α β) (hq : q ∈ unipS ℓ α β) (h : (minkowski (d + 1)).le ⊤ p q) :
    p = q := by
  by_contra hne
  have h1 := unipTime_lt hℓ (unipF_strictMonoOn hℓ.1) hp.1 hq.1 h hne
  rw [(mem_unipSlice_iff.1 hp).2, (mem_unipSlice_iff.1 hq).2] at h1
  exact lt_irrefl _ h1

/-- **Chords of `S` are not timelike**: `|Δt| ≤ ‖Δx⃗‖`. -/
theorem abs_fst_sub_le_of_mem_unipS (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipS ℓ α β) (hq : q ∈ unipS ℓ α β) : |q.1 - p.1| ≤ ‖q.2 - p.2‖ := by
  by_contra hlt
  push Not at hlt
  rcases le_or_gt p.1 q.1 with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)] at hlt
    have hle : (minkowski (d + 1)).le ⊤ p q := minkowski_le_top_iff.2 hlt.le
    have := eq_of_le_of_mem_unipS hℓ hp hq hle
    subst this; simp at hlt
  · rw [abs_of_neg (sub_neg.2 h), neg_sub] at hlt
    have hle : (minkowski (d + 1)).le ⊤ q p := minkowski_le_top_iff.2 (by
      rw [norm_sub_rev]; exact hlt.le)
    have := eq_of_le_of_mem_unipS hℓ hq hp hle
    subst this; simp at hlt

/-- **Every time line meets `S`** (`S` is a Cauchy surface of `Ω`, and every time line meets `Ω`). -/
theorem exists_mem_unipS (hℓ : IsUnipComponent ℓ α β) (a : EuclideanSpace ℝ (Fin (d + 1))) :
    ∃ t : ℝ, ((t, a) : Minkowski (d + 1)) ∈ unipS ℓ α β := by
  obtain ⟨y₀, hy₀1, hy₀2⟩ := EReal.lt_iff_exists_real_btwn.1 hℓ.1
  set z : Minkowski (d + 1) := (a 0 - √2 * y₀, a)
  have hz : z ∈ unipDomain (d := d) α β := by
    have : nullY z = y₀ := by
      have h2 : √2 ≠ 0 := by positivity
      simp only [nullY, z]; field_simp; ring
    exact ⟨by rw [this]; exact hy₀1, by rw [this]; exact hy₀2⟩
  have hv : IsFutureCausal ((1, 0) : Minkowski (d + 1)) := ⟨zero_le_one, by simp [minkQ]⟩
  have hv0 : ((1, 0) : Minkowski (d + 1)) ≠ 0 := fun h => by
    have := congrArg Prod.fst h; simp at this
  obtain ⟨s, hs⟩ := exists_mem_line_of_isCauchySurfaceOn (isCauchySurfaceOn_unipS hℓ) hz hv hv0
  refine ⟨z.1 + s, ?_⟩
  convert hs using 1
  simp [z]

/-- **The graph function of `S`** over the spatial coordinates. -/
noncomputable def unipGraph (hℓ : IsUnipComponent ℓ α β) (a : EuclideanSpace ℝ (Fin (d + 1))) :
    ℝ :=
  (exists_mem_unipS hℓ a).choose

theorem unipGraph_mem (hℓ : IsUnipComponent ℓ α β) (a : EuclideanSpace ℝ (Fin (d + 1))) :
    ((unipGraph hℓ a, a) : Minkowski (d + 1)) ∈ unipS ℓ α β :=
  (exists_mem_unipS hℓ a).choose_spec

theorem lipschitzWith_unipGraph (hℓ : IsUnipComponent ℓ α β) :
    LipschitzWith 1 (unipGraph hℓ) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have := abs_fst_sub_le_of_mem_unipS hℓ (unipGraph_mem hℓ b) (unipGraph_mem hℓ a)
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  simpa using this

/-- **`S` is the graph of `unipGraph`.** -/
theorem mem_unipS_iff (hℓ : IsUnipComponent ℓ α β) {p : Minkowski (d + 1)} :
    p ∈ unipS ℓ α β ↔ p.1 = unipGraph hℓ p.2 := by
  constructor
  · intro hp
    have := abs_fst_sub_le_of_mem_unipS hℓ hp (unipGraph_mem hℓ p.2)
    simp only [sub_self, norm_zero, abs_nonpos_iff, sub_eq_zero] at this
    exact this.symm
  · intro h
    have := unipGraph_mem hℓ p.2
    rwa [← h] at this

end Slice

/-! ### The local chord estimate: `S` is uniformly spacelike near each point -/

section ChordEstimate

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- The Euclidean square norm in null coordinates (the null rotation is orthogonal). -/
theorem sq_add_norm_sq_eq_null (v : Minkowski (d + 1)) :
    v.1 ^ 2 + ‖v.2‖ ^ 2 = nullX v ^ 2 + nullY v ^ 2 + ∑ i, nullZ v i ^ 2 := by
  rw [norm_sq_split]
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  simp only [nullX, nullY, nullZ, div_pow]
  have e : ∀ i : Fin d, (WithLp.toLp 2 fun j : Fin d => v.2 j.succ : EuclideanSpace ℝ (Fin d)) i =
      v.2 i.succ := fun _ => rfl
  simp only [h]
  ring

theorem mul_unipF_sub_ge (hαβ : α < β) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ gI α β) (h₂ : y₂ ∈ gI α β) :
    3 / 2 * (y₂ - y₁) ^ 2 ≤ (y₂ - y₁) * (unipF α β y₂ - unipF α β y₁) := by
  rcases le_total y₁ y₂ with h | h
  · have := gauge_sub_ge (c₀ := 3 / 2) (k := 3) hαβ (by norm_num : (0 : ℝ) < 2) h₁ h₂ h
    nlinarith
  · have := gauge_sub_ge (c₀ := 3 / 2) (k := 3) hαβ (by norm_num : (0 : ℝ) < 2) h₂ h₁ h
    nlinarith

/-- **The lower chord bound**: `min(3, c²) (Δy² + |Δζ|²) ≤ |q − p|²` when `|1 + yλᵢ| ≥ c` at
both ends. -/
theorem chord_lower (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipS ℓ α β) (hq : q ∈ unipS ℓ α β) {cm : ℝ} (hcm : 0 < cm)
    (hcp : ∀ i, cm ≤ |1 + nullY p * ℓ i|) (hcq : ∀ i, cm ≤ |1 + nullY q * ℓ i|) :
    min 3 (cm ^ 2) * ((nullY q - nullY p) ^ 2 + ∑ i, (zeta ℓ i q - zeta ℓ i p) ^ 2) ≤
      minkQ (q - p) := by
  rw [minkQ_sub_of_mem_unipSlice hℓ hp hq]
  have h1 := mul_unipF_sub_ge hℓ.1 hp.1 hq.1
  have h2 : ∀ i, cm ^ 2 * (zeta ℓ i q - zeta ℓ i p) ^ 2 ≤
      (1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) * (zeta ℓ i q - zeta ℓ i p) ^ 2 := fun i => by
    have hpos := unip_mul_pos hℓ hp.1.1 hp.1.2 hq.1.1 hq.1.2 i
    have : cm ^ 2 ≤ (1 + nullY p * ℓ i) * (1 + nullY q * ℓ i) := by
      rw [← abs_of_pos hpos, abs_mul, sq]
      exact mul_le_mul (hcp i) (hcq i) hcm.le (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  rw [← Finset.mul_sum] at h3
  have hm1 : min 3 (cm ^ 2) ≤ 3 := min_le_left _ _
  have hm2 : min 3 (cm ^ 2) ≤ cm ^ 2 := min_le_right _ _
  have hS : 0 ≤ ∑ i, (zeta ℓ i q - zeta ℓ i p) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm0 : 0 ≤ min 3 (cm ^ 2) := le_min (by norm_num) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hm1 (sq_nonneg (nullY q - nullY p)),
    mul_le_mul_of_nonneg_right hm2 hS]

/-- `(a + ∑ bᵢ)² ≤ 2 (d + 1) (a² + ∑ bᵢ²)`. -/
theorem sq_add_sum_le (a : ℝ) (b : Fin d → ℝ) :
    (|a| + ∑ i, |b i|) ^ 2 ≤ 2 * (d + 1) * (a ^ 2 + ∑ i, b i ^ 2) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |b i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, sq_abs,
    nsmul_eq_mul, mul_one] at h1
  have h2 : (|a| + ∑ i, |b i|) ^ 2 ≤ 2 * a ^ 2 + 2 * (∑ i, |b i|) ^ 2 := by
    nlinarith [sq_nonneg (|a| - ∑ i, |b i|), sq_abs a]
  have hS : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [sq_nonneg a]

end ChordEstimate

section ChordUpper

variable {ℓ : Fin d → ℝ} {α β : EReal}

theorem le_sum_of_nonneg' {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) (j : Fin d) : w j ≤ ∑ i, w i :=
  Finset.single_le_sum (fun i _ => hw i) (Finset.mem_univ j)

/-- **The upper chord bound**: on a part of `S` where `f` is `B`-Lipschitz, `|1 + yλᵢ| ≤ Sᵢ`
and `|ζᵢ| ≤ Zᵢ`, the Euclidean square length of a chord is `O((|Δy| + ∑ |Δζᵢ|)²)`. -/
theorem chord_upper (hℓ : IsUnipComponent ℓ α β) {p q : Minkowski (d + 1)}
    (hp : p ∈ unipS ℓ α β) (hq : q ∈ unipS ℓ α β) {B : ℝ} (hB : 0 ≤ B)
    (hF : |unipF α β (nullY q) - unipF α β (nullY p)| ≤ B * |nullY q - nullY p|)
    {Sb Zb : Fin d → ℝ}
    (hSp : ∀ i, |1 + nullY p * ℓ i| ≤ Sb i) (hSq : ∀ i, |1 + nullY q * ℓ i| ≤ Sb i)
    (hZp : ∀ i, |zeta ℓ i p| ≤ Zb i) (hZq : ∀ i, |zeta ℓ i q| ≤ Zb i) :
    (q - p).1 ^ 2 + ‖(q - p).2‖ ^ 2 ≤
      (1 + (d + 1) * (1 + B + ∑ i, (Sb i + |ℓ i| * Zb i + |ℓ i| * Sb i * Zb i +
        ℓ i ^ 2 * Zb i ^ 2)) ^ 2) *
        (|nullY q - nullY p| + ∑ i, |zeta ℓ i q - zeta ℓ i p|) ^ 2 := by
  set Λ := 1 + B + ∑ i, (Sb i + |ℓ i| * Zb i + |ℓ i| * Sb i * Zb i + ℓ i ^ 2 * Zb i ^ 2)
  set m := |nullY q - nullY p| + ∑ i, |zeta ℓ i q - zeta ℓ i p|
  have hS0 : ∀ i, 0 ≤ Sb i := fun i => (abs_nonneg _).trans (hSp i)
  have hZ0 : ∀ i, 0 ≤ Zb i := fun i => (abs_nonneg _).trans (hZp i)
  have hw : ∀ i, 0 ≤ Sb i + |ℓ i| * Zb i + |ℓ i| * Sb i * Zb i + ℓ i ^ 2 * Zb i ^ 2 := fun i => by
    have := hS0 i; have := hZ0 i; positivity
  have hW := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i
  have hΛ1 : 1 ≤ Λ := by simp only [Λ]; linarith
  have hy_m : |nullY q - nullY p| ≤ m := by
    simp only [m]; linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      abs_nonneg (zeta ℓ i q - zeta ℓ i p)]
  have hζ_m : ∀ i, |zeta ℓ i q - zeta ℓ i p| ≤ ∑ j, |zeta ℓ j q - zeta ℓ j p| := fun i =>
    le_sum_of_nonneg' (w := fun j => |zeta ℓ j q - zeta ℓ j p|) (fun j => abs_nonneg _) i
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hy_m
  -- the coefficients are at most `Λ`
  have hcS : ∀ i, Sb i ≤ Λ := fun i => by
    have := le_sum_of_nonneg' hw i; have := hZ0 i
    simp only [Λ]; nlinarith [abs_nonneg (ℓ i), sq_nonneg (ℓ i), mul_nonneg (abs_nonneg (ℓ i)) (hZ0 i),
      mul_nonneg (mul_nonneg (abs_nonneg (ℓ i)) (hS0 i)) (hZ0 i), mul_nonneg (sq_nonneg (ℓ i))
      (sq_nonneg (Zb i))]
  have hcLZ : ∀ i, |ℓ i| * Zb i ≤ Λ := fun i => by
    have := le_sum_of_nonneg' hw i
    simp only [Λ]; nlinarith [hS0 i, mul_nonneg (mul_nonneg (abs_nonneg (ℓ i)) (hS0 i)) (hZ0 i),
      mul_nonneg (sq_nonneg (ℓ i)) (sq_nonneg (Zb i))]
  have hcLSZ : ∀ i, |ℓ i| * Sb i * Zb i ≤ Λ := fun i => by
    have := le_sum_of_nonneg' hw i
    simp only [Λ]; nlinarith [hS0 i, mul_nonneg (abs_nonneg (ℓ i)) (hZ0 i),
      mul_nonneg (sq_nonneg (ℓ i)) (sq_nonneg (Zb i))]
  have hcB : B + ∑ i, 1 / 2 * (ℓ i ^ 2 * Zb i ^ 2) ≤ Λ := by
    have : ∑ i, 1 / 2 * (ℓ i ^ 2 * Zb i ^ 2) ≤
        ∑ i, (Sb i + |ℓ i| * Zb i + |ℓ i| * Sb i * Zb i + ℓ i ^ 2 * Zb i ^ 2) :=
      Finset.sum_le_sum fun i _ => by
        nlinarith [hS0 i, mul_nonneg (abs_nonneg (ℓ i)) (hZ0 i),
          mul_nonneg (mul_nonneg (abs_nonneg (ℓ i)) (hS0 i)) (hZ0 i),
          mul_nonneg (sq_nonneg (ℓ i)) (sq_nonneg (Zb i))]
    simp only [Λ]; linarith
  -- `Δz`
  have hdz : ∀ i, |nullZ (q - p) i| ≤ Λ * m := fun i => by
    rw [nullZ_sub_apply, nullZ_eq_mul_zeta hℓ hp.1 i, nullZ_eq_mul_zeta hℓ hq.1 i]
    have e : (1 + nullY q * ℓ i) * zeta ℓ i q - (1 + nullY p * ℓ i) * zeta ℓ i p =
        (1 + nullY q * ℓ i) * (zeta ℓ i q - zeta ℓ i p) + ℓ i * (nullY q - nullY p) * zeta ℓ i p := by
      ring
    rw [e]
    calc |(1 + nullY q * ℓ i) * (zeta ℓ i q - zeta ℓ i p) + ℓ i * (nullY q - nullY p) * zeta ℓ i p|
        ≤ Sb i * |zeta ℓ i q - zeta ℓ i p| + (|ℓ i| * Zb i) * |nullY q - nullY p| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hSq i) (abs_nonneg _)
          · rw [abs_mul, abs_mul]
            have := hZp i
            have := mul_nonneg (abs_nonneg (ℓ i)) (abs_nonneg (nullY q - nullY p))
            nlinarith
      _ ≤ Λ * |zeta ℓ i q - zeta ℓ i p| + Λ * |nullY q - nullY p| := by
          gcongr
          · exact hcS i
          · exact hcLZ i
      _ ≤ Λ * m := by
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          simp only [m]; linarith [hζ_m i]
  -- `Δx`
  have ht : ∀ i, |ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 -
      ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2| ≤
      2 * (|ℓ i| * Sb i * Zb i) * |zeta ℓ i q - zeta ℓ i p| +
        ℓ i ^ 2 * Zb i ^ 2 * |nullY q - nullY p| := fun i => by
    have e : ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 - ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2 =
        ℓ i * (1 + nullY q * ℓ i) * (zeta ℓ i q + zeta ℓ i p) * (zeta ℓ i q - zeta ℓ i p) +
          ℓ i ^ 2 * zeta ℓ i p ^ 2 * (nullY q - nullY p) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_mul]
      have h1 : |zeta ℓ i q + zeta ℓ i p| ≤ 2 * Zb i := by
        have := abs_add_le (zeta ℓ i q) (zeta ℓ i p); linarith [hZp i, hZq i]
      have := mul_le_mul (hSq i) h1 (abs_nonneg _) (hS0 i)
      have := mul_le_mul_of_nonneg_left this (abs_nonneg (ℓ i))
      have := mul_le_mul_of_nonneg_right this (abs_nonneg (zeta ℓ i q - zeta ℓ i p))
      nlinarith
    · rw [abs_mul, abs_mul, abs_pow, abs_pow, sq_abs]
      have h1 : |zeta ℓ i p| ^ 2 ≤ Zb i ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hZp i) 2
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (ℓ i))
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hdx : |nullX (q - p)| ≤ Λ * m := by
    rw [nullX_sub, nullX_eq_of_mem_unipSlice hℓ hp, nullX_eq_of_mem_unipSlice hℓ hq]
    have e : unipF α β (nullY q) - 1 / 2 * ∑ i, ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 -
        (unipF α β (nullY p) - 1 / 2 * ∑ i, ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2) =
        (unipF α β (nullY q) - unipF α β (nullY p)) - 1 / 2 * ∑ i,
          (ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 - ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [e]
    have h1 := Finset.abs_sum_le_sum_abs (fun i =>
      ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 - ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2)
      Finset.univ
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => ht i
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h2
    have h3 : ∑ i, 2 * (|ℓ i| * Sb i * Zb i) * |zeta ℓ i q - zeta ℓ i p| ≤
        2 * Λ * ∑ i, |zeta ℓ i q - zeta ℓ i p| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (by linarith [hcLSZ i]) (abs_nonneg _)
    have h4 : (∑ i, ℓ i ^ 2 * Zb i ^ 2) * |nullY q - nullY p| ≤
        2 * (Λ - B) * |nullY q - nullY p| := by
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have : ∑ i, 1 / 2 * (ℓ i ^ 2 * Zb i ^ 2) = 1 / 2 * ∑ i, ℓ i ^ 2 * Zb i ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      linarith
    have h5 := abs_sub (unipF α β (nullY q) - unipF α β (nullY p))
      (1 / 2 * ∑ i, (ℓ i * (1 + nullY q * ℓ i) * zeta ℓ i q ^ 2 -
        ℓ i * (1 + nullY p * ℓ i) * zeta ℓ i p ^ 2))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h5
    have hy0 := abs_nonneg (nullY q - nullY p)
    simp only [m]
    nlinarith
  -- assembly
  rw [sq_add_norm_sq_eq_null, nullY_sub]
  have hx2 : nullX (q - p) ^ 2 ≤ (Λ * m) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdx 2
  have hy2 : (nullY q - nullY p) ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy_m 2
  have hz2 : ∑ i, nullZ (q - p) i ^ 2 ≤ ∑ _i : Fin d, (Λ * m) ^ 2 :=
    Finset.sum_le_sum fun i _ => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdz i) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hz2
  nlinarith

end ChordUpper

section Spacelike

variable {ℓ : Fin d → ℝ} {α β : EReal}

theorem isOpen_gI : IsOpen (gI α β) :=
  (isOpen_lt continuous_const continuous_coe_real_ereal).inter
    (isOpen_lt continuous_coe_real_ereal continuous_const)

theorem continuousOn_zeta (hℓ : IsUnipComponent ℓ α β) (i : Fin d) :
    ContinuousOn (zeta ℓ i) (unipDomain (d := d) α β : Set (Minkowski (d + 1))) := by
  have hz : Continuous fun p : Minkowski (d + 1) => nullZ p i :=
    (EuclideanSpace.proj i.succ).continuous.comp continuous_snd
  exact hz.continuousOn.div (continuousOn_const.add (continuous_nullY.continuousOn.mul
    continuousOn_const)) fun p hp => hℓ.2.1 _ hp.1 hp.2 i

/-- **`S` is uniformly spacelike near each point**: there are an open `O ∋ p₀` in `Ω` and
`κ ∈ ]0, 1[` with `κ ‖q − p‖²_E ≤ |q − p|²` for `p, q ∈ S ∩ O` (chord identity, lower and upper
bounds). -/
theorem exists_spacelike_nbhd (hℓ : IsUnipComponent ℓ α β) {p₀ : Minkowski (d + 1)}
    (hp₀ : p₀ ∈ unipS ℓ α β) :
    ∃ (O : Opens (Minkowski (d + 1))) (κ : ℝ), p₀ ∈ O ∧
      (O : Set (Minkowski (d + 1))) ⊆ (unipDomain (d := d) α β : Set (Minkowski (d + 1))) ∧
      0 < κ ∧ κ < 1 ∧
      ∀ p ∈ unipS ℓ α β, p ∈ O → ∀ q ∈ unipS ℓ α β, q ∈ O →
        κ * ((q - p).1 ^ 2 + ‖(q - p).2‖ ^ 2) ≤ minkQ (q - p) := by
  set y₀ := nullY p₀
  have hy₀ : y₀ ∈ gI α β := hp₀.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_gI y₀ hy₀
  set δ := ε / 2
  have hδ : 0 < δ := by positivity
  set K := Icc (y₀ - δ) (y₀ + δ)
  have hδε : δ < ε := by simp only [δ]; linarith
  have hKI : K ⊆ gI α β := fun y hy => hball (by
    obtain ⟨h1, h2⟩ := hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hKc : IsCompact K := isCompact_Icc
  have hKn : K.Nonempty := ⟨y₀, by constructor <;> linarith⟩
  -- the Lipschitz constant of `f` on `K`
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn
    ((continuousOn_gauge' (c₀ := 3 / 2) (k := 3) hℓ.1 (by norm_num : (0 : ℝ) < 2)).mono hKI)
  set B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hFL : ∀ y₁ ∈ K, ∀ y₂ ∈ K, |unipF α β y₂ - unipF α β y₁| ≤ B * |y₂ - y₁| := by
    intro y₁ h₁ y₂ h₂
    have := (convex_Icc (y₀ - δ) (y₀ + δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := unipF α β) (f' := gauge' α β (3 / 2) 2 3)
      (fun y hy => (hasDerivAt_gauge hℓ.1 (by norm_num) (hKI hy)).hasDerivWithinAt)
      (C := B) (fun y hy => (hB₀ y hy).trans (le_max_left B₀ 0)) h₁ h₂
    simpa [Real.norm_eq_abs] using this
  -- lower bounds of `|1 + yλᵢ|` on `K`
  have hmi : ∀ i, ∃ m > 0, ∀ y ∈ K, m ≤ |1 + y * ℓ i| := fun i => by
    obtain ⟨y₁, hy₁, hmin⟩ := hKc.exists_isMinOn hKn
      (Continuous.continuousOn (f := fun y : ℝ => |1 + y * ℓ i|) (by fun_prop))
    exact ⟨|1 + y₁ * ℓ i|, abs_pos.2 (hℓ.2.1 _ (hKI hy₁).1 (hKI hy₁).2 i), fun y hy => hmin hy⟩
  choose mi hmi0 hmiK using hmi
  set cm := (1 + ∑ i, 1 / mi i)⁻¹
  have hsum0 : 0 ≤ ∑ i, 1 / mi i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hmi0 i)).le
  have hcm : 0 < cm := inv_pos.2 (by linarith)
  have hcmi : ∀ i, cm ≤ mi i := fun i => by
    have h1 : 1 / mi i ≤ ∑ j, 1 / mi j :=
      le_sum_of_nonneg' (w := fun j => 1 / mi j) (fun j => (one_div_pos.2 (hmi0 j)).le) i
    rw [inv_le_comm₀ (by linarith) (hmi0 i)]
    rw [one_div] at h1; linarith
  -- upper bounds
  set Sb : Fin d → ℝ := fun i => 1 + (|y₀| + δ) * |ℓ i|
  set ζ₀ : Fin d → ℝ := fun i => zeta ℓ i p₀
  set Zb : Fin d → ℝ := fun i => |ζ₀ i| + 1
  have hSK : ∀ y ∈ K, ∀ i, |1 + y * ℓ i| ≤ Sb i := fun y hy i => by
    have hy' : |y| ≤ |y₀| + δ := by
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2, neg_abs_le y₀, le_abs_self y₀]
    calc |1 + y * ℓ i| ≤ |1| + |y * ℓ i| := abs_add_le _ _
      _ = 1 + |y| * |ℓ i| := by rw [abs_one, abs_mul]
      _ ≤ Sb i := by
          simp only [Sb]; gcongr
  -- the open set
  set g : Minkowski (d + 1) → ℝ × (Fin d → ℝ) := fun p => (nullY p, fun i => zeta ℓ i p)
  have hg : ContinuousOn g (unipDomain (d := d) α β : Set (Minkowski (d + 1))) :=
    continuous_nullY.continuousOn.prodMk (continuousOn_pi.2 fun i => continuousOn_zeta hℓ i)
  have ht : IsOpen (Metric.ball y₀ δ ×ˢ Metric.ball ζ₀ 1) :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  have hOo := hg.isOpen_inter_preimage (unipDomain (d := d) α β).isOpen ht
  set O : Opens (Minkowski (d + 1)) := ⟨_, hOo⟩
  have hO : ∀ p ∈ O, nullY p ∈ K ∧ ∀ i, |zeta ℓ i p| ≤ Zb i := by
    rintro p ⟨-, h1, h2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1
    refine ⟨⟨by linarith, by linarith⟩, fun i => ?_⟩
    have h3 := (dist_pi_lt_iff one_pos).1 (Metric.mem_ball.1 h2) i
    rw [Real.dist_eq] at h3
    have := abs_sub_abs_le_abs_sub (zeta ℓ i p) (ζ₀ i)
    simp only [Zb]; linarith
  -- the constants
  set Λ := 1 + B + ∑ i, (Sb i + |ℓ i| * Zb i + |ℓ i| * Sb i * Zb i + ℓ i ^ 2 * Zb i ^ 2)
  set μ := min 3 (cm ^ 2)
  have hμ : 0 < μ := lt_min (by norm_num) (by positivity)
  set κ := min (1 / 2) (μ / (2 * (d + 1) * (1 + (d + 1) * Λ ^ 2)))
  have hden : 0 < 2 * ((d : ℝ) + 1) * (1 + (d + 1) * Λ ^ 2) := by positivity
  refine ⟨O, κ, ⟨hp₀.1, by simp [g, ζ₀, y₀, hδ]⟩, fun p hp => hp.1,
    lt_min (by norm_num) (div_pos hμ hden), (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro p hp hpO q hq hqO
  obtain ⟨hpK, hpZ⟩ := hO p hpO
  obtain ⟨hqK, hqZ⟩ := hO q hqO
  have hlow := chord_lower hℓ hp hq hcm (fun i => (hcmi i).trans (hmiK i _ hpK))
    (fun i => (hcmi i).trans (hmiK i _ hqK))
  have hup := chord_upper hℓ hp hq hB (hFL _ hpK _ hqK) (hSK _ hpK) (hSK _ hqK) hpZ hqZ
  have hm := sq_add_sum_le (nullY q - nullY p) (fun i => zeta ℓ i q - zeta ℓ i p)
  set E := (q - p).1 ^ 2 + ‖(q - p).2‖ ^ 2
  set m := |nullY q - nullY p| + ∑ i, |zeta ℓ i q - zeta ℓ i p|
  set R := (nullY q - nullY p) ^ 2 + ∑ i, (zeta ℓ i q - zeta ℓ i p) ^ 2
  have hE0 : 0 ≤ E := by positivity
  have hR0 : 0 ≤ R := by positivity
  have h1 : E ≤ (1 + (d + 1) * Λ ^ 2) * (2 * (d + 1) * R) :=
    hup.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  have h2 : κ * E ≤ μ / (2 * (d + 1) * (1 + (d + 1) * Λ ^ 2)) * E :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hE0
  have h3 : μ / (2 * (d + 1) * (1 + (d + 1) * Λ ^ 2)) * E ≤ μ * R := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    calc μ * E ≤ μ * ((1 + (d + 1) * Λ ^ 2) * (2 * (d + 1) * R)) :=
          mul_le_mul_of_nonneg_left h1 hμ.le
      _ = μ * R * (2 * (d + 1) * (1 + (d + 1) * Λ ^ 2)) := by ring
  linarith

/-- **`S` is a spacelike Lipschitz hypersurface of every `V ⊇ Ω`** (contract (f): the slope
bound `c < 1` depends on the point). -/
theorem isSpacelikeLipschitzIn_unipS (hℓ : IsUnipComponent ℓ α β) {V : Opens (Minkowski (d + 1))}
    (hV : unipDomain (d := d) α β ≤ V) : IsSpacelikeLipschitzIn V (unipS ℓ α β) := by
  refine ⟨fun p hp => hV hp.1, fun p hp q hq hlt => ?_, fun p₀ hp₀ => ?_⟩
  · have hlt' := (minkowski (d + 1)).lt_mono le_top hlt
    have hle := (minkowski (d + 1)).le_of_lt hlt'
    have heq := eq_of_le_of_mem_unipS hℓ hp hq hle
    subst heq
    have := minkowski_lt_top_iff.1 hlt'
    simp at this
  obtain ⟨O, κ, hp₀O, hOΩ, hκ0, hκ1, hest⟩ := exists_spacelike_nbhd hℓ hp₀
  set h := unipGraph hℓ
  have hc : Continuous fun a : EuclideanSpace ℝ (Fin (d + 1)) => ((h a, a) : Minkowski (d + 1)) :=
    (lipschitzWith_unipGraph hℓ).continuous.prodMk continuous_id
  set U : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
    (fun a => ((h a, a) : Minkowski (d + 1))) ⁻¹' (O : Set (Minkowski (d + 1)))
  have hU : IsOpen U := O.isOpen.preimage hc
  have hκ' : 0 ≤ (1 - κ) / (1 + κ) := div_nonneg (by linarith) (by linarith)
  set c : ℝ≥0 := ⟨√((1 - κ) / (1 + κ)), Real.sqrt_nonneg _⟩
  have hc1 : c < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    change √((1 - κ) / (1 + κ)) < 1
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  refine ⟨1, O, U, h, c, hc1, hp₀O, fun x hx => hV (hOΩ hx), hU, ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hpa := (mem_unipS_iff hℓ).2 (show (h a, a).1 = h (h a, a).2 from rfl)
    have hpb := (mem_unipS_iff hℓ).2 (show (h b, b).1 = h (h b, b).2 from rfl)
    have := hest _ hpb hb _ hpa ha
    simp only [Prod.fst_sub, Prod.snd_sub, minkQ] at this
    rw [Real.dist_eq, dist_eq_norm]
    have h1 : (1 + κ) * (h a - h b) ^ 2 ≤ (1 - κ) * ‖a - b‖ ^ 2 := by nlinarith
    have h2 : (h a - h b) ^ 2 ≤ (1 - κ) / (1 + κ) * ‖a - b‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
    change |h a - h b| ≤ √((1 - κ) / (1 + κ)) * ‖a - b‖
    rw [← Real.sqrt_sq (norm_nonneg (a - b)), ← Real.sqrt_mul hκ', ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h2
  · rw [one_smul, one_smul]
    ext p
    simp only [mem_inter_iff, graphOver, mem_setOf_eq]
    constructor
    · rintro ⟨hpS, hpO⟩
      have hp1 := (mem_unipS_iff hℓ).1 hpS
      refine ⟨hpO, ?_, hp1⟩
      show ((h p.2, p.2) : Minkowski (d + 1)) ∈ (O : Set (Minkowski (d + 1)))
      have : ((h p.2, p.2) : Minkowski (d + 1)) = p := Prod.ext hp1.symm rfl
      rw [this]; exact hpO
    · rintro ⟨hpO, -, hp1⟩
      exact ⟨(mem_unipS_iff hℓ).2 hp1, hpO⟩

end Spacelike

/-! ### Curves of `S`: the metric `2 f′ dy² + ∑ (1 + yλᵢ)² dζᵢ²` -/

section CurveMetric

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- `nullY` as a continuous linear map. -/
noncomputable def nullYL : Minkowski (d + 1) →L[ℝ] ℝ :=
  (1 / √2) • ((EuclideanSpace.proj (0 : Fin (d + 1))).comp
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (d + 1)))) -
    ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (d + 1))))

theorem nullYL_apply (p : Minkowski (d + 1)) : nullYL p = nullY p := by
  simp [nullYL, nullY]; ring

/-- `nullX` as a continuous linear map. -/
noncomputable def nullXL : Minkowski (d + 1) →L[ℝ] ℝ :=
  (1 / √2) • ((EuclideanSpace.proj (0 : Fin (d + 1))).comp
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (d + 1)))) +
    ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin (d + 1))))

theorem nullXL_apply (p : Minkowski (d + 1)) : nullXL p = nullX p := by
  simp [nullXL, nullX]; ring

/-- `p ↦ nullZ p i` as a continuous linear map. -/
noncomputable def nullZL (i : Fin d) : Minkowski (d + 1) →L[ℝ] ℝ :=
  (EuclideanSpace.proj i.succ).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin (d + 1))))

theorem nullZL_apply (i : Fin d) (p : Minkowski (d + 1)) : nullZL i p = nullZ p i := by
  simp [nullZL, nullZ]

theorem hasDerivAt_nullY_comp {Γ : ℝ → Minkowski (d + 1)} {v : Minkowski (d + 1)} {r : ℝ}
    (h : HasDerivAt Γ v r) : HasDerivAt (fun s => nullY (Γ s)) (nullY v) r := by
  have := (nullYL (d := d)).hasFDerivAt.comp_hasDerivAt r h
  simp only [Function.comp_def, nullYL_apply] at this
  rw [← nullYL_apply]; simpa only [nullYL_apply] using this

theorem hasDerivAt_nullX_comp {Γ : ℝ → Minkowski (d + 1)} {v : Minkowski (d + 1)} {r : ℝ}
    (h : HasDerivAt Γ v r) : HasDerivAt (fun s => nullX (Γ s)) (nullX v) r := by
  have := (nullXL (d := d)).hasFDerivAt.comp_hasDerivAt r h
  simp only [Function.comp_def, nullXL_apply] at this
  rw [← nullXL_apply]; simpa only [nullXL_apply] using this

theorem hasDerivAt_nullZ_comp {Γ : ℝ → Minkowski (d + 1)} {v : Minkowski (d + 1)} {r : ℝ}
    (h : HasDerivAt Γ v r) (i : Fin d) :
    HasDerivAt (fun s => nullZ (Γ s) i) (nullZ v i) r := by
  have := (nullZL (d := d) i).hasFDerivAt.comp_hasDerivAt r h
  simp only [Function.comp_def, nullZL_apply] at this
  rw [← nullZL_apply]; simpa only [nullZL_apply] using this

end CurveMetric

section CurveMetric2

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- The derivative of `ζᵢ` along a curve. -/
noncomputable def zetaD (ℓ : Fin d → ℝ) (i : Fin d) (p v : Minkowski (d + 1)) : ℝ :=
  (nullZ v i * (1 + nullY p * ℓ i) - nullZ p i * (nullY v * ℓ i)) / (1 + nullY p * ℓ i) ^ 2

theorem hasDerivAt_s_comp {Γ : ℝ → Minkowski (d + 1)} {v : Minkowski (d + 1)} {r : ℝ}
    (h : HasDerivAt Γ v r) (c : ℝ) :
    HasDerivAt (fun s => 1 + nullY (Γ s) * c) (nullY v * c) r := by
  have := (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_nullY_comp h).mul_const c)
  rw [zero_add] at this
  exact this

theorem hasDerivAt_zeta_comp (hℓ : IsUnipComponent ℓ α β) {Γ : ℝ → Minkowski (d + 1)}
    {v : Minkowski (d + 1)} {r : ℝ} (h : HasDerivAt Γ v r) (hΓ : Γ r ∈ unipDomain (d := d) α β)
    (i : Fin d) : HasDerivAt (fun s => zeta ℓ i (Γ s)) (zetaD ℓ i (Γ r) v) r :=
  (hasDerivAt_nullZ_comp h i).div (hasDerivAt_s_comp h (ℓ i)) (hℓ.2.1 _ hΓ.1 hΓ.2 i)

/-- **The metric of `S` along a curve**: at a point where a curve `Γ` of `S` is differentiable,
`|Γ′|² = 2 f′(y) y′² + ∑ (1 + yλᵢ)² ζᵢ′²` (l.712–720). -/
theorem minkQ_deriv_of_mem_unipS (hℓ : IsUnipComponent ℓ α β) {Γ : ℝ → Minkowski (d + 1)}
    (hΓS : ∀ s, Γ s ∈ unipS ℓ α β) {r : ℝ} (hd : DifferentiableAt ℝ Γ r) :
    minkQ (deriv Γ r) = 2 * gauge' α β (3 / 2) 2 3 (nullY (Γ r)) * nullY (deriv Γ r) ^ 2 +
      ∑ i, (1 + nullY (Γ r) * ℓ i) ^ 2 * zetaD ℓ i (Γ r) (deriv Γ r) ^ 2 := by
  have h := hd.hasDerivAt
  have hΩ := (hΓS r).1
  have hY := hasDerivAt_nullY_comp h
  have hs : ∀ i, 1 + nullY (Γ r) * ℓ i ≠ 0 := fun i => hℓ.2.1 _ hΩ.1 hΩ.2 i
  have hterm : ∀ i ∈ Finset.univ, HasDerivAt
      (fun s => ℓ i * (1 + nullY (Γ s) * ℓ i) * zeta ℓ i (Γ s) ^ 2)
      (ℓ i * (nullY (deriv Γ r) * ℓ i) * zeta ℓ i (Γ r) ^ 2 +
        ℓ i * (1 + nullY (Γ r) * ℓ i) *
          (2 * zeta ℓ i (Γ r) * zetaD ℓ i (Γ r) (deriv Γ r))) r := fun i _ => by
    have h1 := (hasDerivAt_s_comp h (ℓ i)).const_mul (ℓ i)
    have h2 := (hasDerivAt_zeta_comp hℓ h hΩ i).pow 2
    have := h1.mul h2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.pow_apply]; ring
  have hsum := HasDerivAt.fun_sum hterm
  have hF := (hasDerivAt_gauge (c₀ := 3 / 2) (k := 3) hℓ.1 (by norm_num : (0 : ℝ) < 2) hΩ).comp r hY
  have hR := hF.sub (hsum.const_mul (1 / 2))
  have hfun : (fun s => nullX (Γ s)) = fun s => unipF α β (nullY (Γ s)) - 1 / 2 *
      ∑ i, ℓ i * (1 + nullY (Γ s) * ℓ i) * zeta ℓ i (Γ s) ^ 2 :=
    funext fun s => nullX_eq_of_mem_unipSlice hℓ (hΓS s)
  have hX := hasDerivAt_nullX_comp h
  rw [hfun] at hX
  have hXv := hX.unique hR
  have hZ : ∀ i, nullZ (deriv Γ r) i ^ 2 =
      (1 + nullY (Γ r) * ℓ i) ^ 2 * zetaD ℓ i (Γ r) (deriv Γ r) ^ 2 +
      nullY (deriv Γ r) * (ℓ i * (nullY (deriv Γ r) * ℓ i) * zeta ℓ i (Γ r) ^ 2 +
        ℓ i * (1 + nullY (Γ r) * ℓ i) *
          (2 * zeta ℓ i (Γ r) * zetaD ℓ i (Γ r) (deriv Γ r))) := fun i => by
    have hz := nullZ_eq_mul_zeta hℓ hΩ i
    have e : nullZ (deriv Γ r) i = (1 + nullY (Γ r) * ℓ i) * zetaD ℓ i (Γ r) (deriv Γ r) +
        nullY (deriv Γ r) * ℓ i * zeta ℓ i (Γ r) := by
      have hsi := hs i
      unfold zetaD
      rw [hz]
      field_simp
      ring
    rw [e]; ring
  rw [minkQ_eq_null, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl fun i _ => hZ i, Finset.sum_add_distrib, ← Finset.mul_sum, hXv]
  ring

end CurveMetric2

section FTC

open MeasureTheory

/-- **The fundamental theorem of calculus, as a length bound**: if `φ` is Lipschitz on `[a, b]`
and, wherever the Lipschitz curve `Γ` is differentiable inside `]a, b[`,
`|φ′| ≤ c √|Γ′|²`, then `|φ(b) − φ(a)| ≤ c ∫ₐᵇ √|Γ′|²`. -/
theorem abs_sub_le_mul_integral {φ : ℝ → ℝ} {Γ : ℝ → Minkowski (d + 1)} {K : ℝ≥0}
    (hΓ : LipschitzWith K Γ) {a b : ℝ} (hab : a ≤ b) {Kφ : ℝ≥0}
    (hφ : LipschitzOnWith Kφ φ (Icc a b)) {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ r ∈ Ioo a b, DifferentiableAt ℝ Γ r → |deriv φ r| ≤ c * √(minkQ (deriv Γ r))) :
    |φ b - φ a| ≤ c * ∫ r in a..b, √(minkQ (deriv Γ r)) := by
  have hφ' : LipschitzOnWith Kφ φ (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFTC := hφ'.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hbdΓ : ∀ r, √(minkQ (deriv Γ r)) ≤ K := fun r =>
    (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hΓ))
  have hae : ∀ᵐ r ∂(volume.restrict (Ioo a b)), |deriv φ r| ≤ c * √(minkQ (deriv Γ r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hΓ.ae_differentiableAt_real] with r hr hdr
    exact hd r hr hdr
  have hint2 : IntervalIntegrable (fun r => c * √(minkQ (deriv Γ r))) volume a b :=
    intervalIntegrable_of_bound (measurable_const.mul (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv Γ)))) (c * K) (fun r => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hbdΓ r) hc) a b
  have hint1 : IntervalIntegrable (fun r => |deriv φ r|) volume a b := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => c * K) intervalIntegrable_const
      (measurable_deriv φ).abs.aestronglyMeasurable ?_
    rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [hae] with r hr
    rw [Real.norm_eq_abs, abs_abs]
    exact hr.trans (mul_le_mul_of_nonneg_left (hbdΓ r) hc)
  have hmono := intervalIntegral.integral_mono_ae_restrict hab hint1 hint2 (by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]; exact hae)
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [← hFTC]
  exact (intervalIntegral.abs_integral_le_integral_abs hab).trans hmono

end FTC

section PathBounds

open MeasureTheory

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- The gauges are Lipschitz on every compact subinterval of `]α, β[`. -/
theorem exists_lipschitzOnWith_gauge (hαβ : α < β) {c₀ c : ℝ} {k : ℕ} (hc : 0 < c) {m M : ℝ}
    (hmM : Icc m M ⊆ gI α β) : ∃ K : ℝ≥0, LipschitzOnWith K (gauge α β c₀ c k) (Icc m M) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_gauge' (c₀ := c₀) (k := k) hαβ hc).mono hmM)
  refine ⟨Real.toNNReal B, (convex_Icc m M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun _ hy => (hasDerivAt_gauge hαβ hc (hmM hy)).hasDerivWithinAt) fun y hy => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

/-- `]α, β[` is order-connected. -/
theorem Icc_subset_gI {m M : ℝ} (hm : m ∈ gI α β) (hM : M ∈ gI α β) : Icc m M ⊆ gI α β :=
  fun _ hy => ⟨hm.1.trans_le (EReal.coe_le_coe_iff.2 hy.1),
    (EReal.coe_le_coe_iff.2 hy.2).trans_lt hM.2⟩

/-- The `y`-range of a continuous curve of `Ω` over a compact interval lies in a compact
subinterval of `]α, β[`. -/
theorem exists_Icc_nullY {Γ : ℝ → Minkowski (d + 1)} (hΓ : Continuous Γ)
    (hΓΩ : ∀ r, Γ r ∈ unipDomain (d := d) α β) (a b : ℝ) (hab : a ≤ b) :
    ∃ m M : ℝ, Icc m M ⊆ gI α β ∧ ∀ r ∈ Icc a b, nullY (Γ r) ∈ Icc m M := by
  have hc : ContinuousOn (fun r => nullY (Γ r)) (Icc a b) :=
    (continuous_nullY.comp hΓ).continuousOn
  have hne : (Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  obtain ⟨r₁, -, h₁⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨r₂, -, h₂⟩ := isCompact_Icc.exists_isMaxOn hne hc
  exact ⟨_, _, Icc_subset_gI (hΓΩ r₁) (hΓΩ r₂), fun r hr => ⟨h₁ hr, h₂ hr⟩⟩

/-- **A quotient of Lipschitz functions with denominator bounded away from `0`.** -/
theorem exists_lipschitzOnWith_div {s : Set ℝ} {u w : ℝ → ℝ} {Ku Kw : ℝ≥0}
    (hu : LipschitzOnWith Ku u s) (hw : LipschitzOnWith Kw w s) {A Bw c : ℝ} (hc : 0 < c)
    (hA : ∀ r ∈ s, |u r| ≤ A) (hB : ∀ r ∈ s, |w r| ≤ Bw) (hcw : ∀ r ∈ s, c ≤ |w r|) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun r => u r / w r) s := by
  refine ⟨Real.toNNReal ((Ku * |Bw| + |A| * Kw) / c ^ 2), LipschitzOnWith.of_dist_le_mul
    fun r hr r' hr' => ?_⟩
  have hw0 : w r ≠ 0 := fun h => by have := hcw r hr; rw [h, abs_zero] at this; linarith
  have hw0' : w r' ≠ 0 := fun h => by have := hcw r' hr'; rw [h, abs_zero] at this; linarith
  have e : u r / w r - u r' / w r' = ((u r - u r') * w r' + u r' * (w r' - w r)) / (w r * w r') := by
    field_simp; ring
  rw [Real.dist_eq, e, abs_div, abs_mul, Real.coe_toNNReal _ (by positivity)]
  have h1 := hu.dist_le_mul r hr r' hr'
  have h2 := hw.dist_le_mul r' hr' r hr
  rw [Real.dist_eq, Real.dist_eq] at h1 h2
  rw [abs_sub_comm r' r] at h2
  rw [Real.dist_eq]
  have hcc : c ^ 2 ≤ |w r| * |w r'| := by
    rw [sq]; exact mul_le_mul (hcw r hr) (hcw r' hr') hc.le (abs_nonneg _)
  have hnum : |(u r - u r') * w r' + u r' * (w r' - w r)| ≤ (Ku * |Bw| + |A| * Kw) * |r - r'| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hb := (hB r' hr').trans (le_abs_self Bw)
    have ha := (hA r' hr').trans (le_abs_self A)
    have := mul_le_mul h1 hb (abs_nonneg _) (by positivity)
    have := mul_le_mul ha h2 (abs_nonneg _) (abs_nonneg _)
    nlinarith
  rw [div_le_iff₀ (by have := (abs_pos.2 hw0); have := abs_pos.2 hw0'; positivity)]
  calc |(u r - u r') * w r' + u r' * (w r' - w r)| ≤ (Ku * |Bw| + |A| * Kw) * |r - r'| := hnum
    _ = (Ku * |Bw| + |A| * Kw) / c ^ 2 * |r - r'| * c ^ 2 := by field_simp
    _ ≤ (Ku * |Bw| + |A| * Kw) / c ^ 2 * |r - r'| * (|w r| * |w r'|) := by gcongr

end PathBounds

section PathBounds2

open MeasureTheory

variable {ℓ : Fin d → ℝ} {α β : EReal}

theorem lipschitzWith_nullY_comp {Γ : ℝ → Minkowski (d + 1)} {K : ℝ≥0} (hK : LipschitzWith K Γ) :
    ∃ K' : ℝ≥0, LipschitzWith K' fun r => nullY (Γ r) := by
  have := (nullYL (d := d)).lipschitz.comp hK
  exact ⟨_, by simpa [Function.comp_def, nullYL_apply] using this⟩

theorem lipschitzWith_nullZ_comp {Γ : ℝ → Minkowski (d + 1)} {K : ℝ≥0} (hK : LipschitzWith K Γ)
    (i : Fin d) : ∃ K' : ℝ≥0, LipschitzWith K' fun r => nullZ (Γ r) i := by
  have := (nullZL (d := d) i).lipschitz.comp hK
  exact ⟨_, by simpa [Function.comp_def, nullZL_apply] using this⟩

/-- **Lengths control the gauge**: along a Lipschitz curve of `S`,
`|G(y(b)) − G(y(a))| ≤ ∫ₐᵇ √|Γ′|²` (Barbot's `∫ a`, l.712–720). -/
theorem abs_unipG_sub_le (hℓ : IsUnipComponent ℓ α β) {Γ : ℝ → Minkowski (d + 1)} {K : ℝ≥0}
    (hK : LipschitzWith K Γ) (hΓS : ∀ s, Γ s ∈ unipS ℓ α β) {a b : ℝ} (hab : a ≤ b) :
    |unipG α β (nullY (Γ b)) - unipG α β (nullY (Γ a))| ≤
      ∫ r in a..b, √(minkQ (deriv Γ r)) := by
  obtain ⟨m, M, hmM, hY⟩ := exists_Icc_nullY hK.continuous (fun r => (hΓS r).1) a b hab
  obtain ⟨KG, hG⟩ := exists_lipschitzOnWith_gauge (c₀ := 1) (k := 1) hℓ.1 one_pos hmM
  obtain ⟨KY, hYL⟩ := lipschitzWith_nullY_comp hK
  have hφ : LipschitzOnWith (KG * KY) (fun r => unipG α β (nullY (Γ r))) (Icc a b) :=
    hG.comp hYL.lipschitzOnWith fun r hr => hY r hr
  have := abs_sub_le_mul_integral hK hab hφ zero_le_one fun r _ hd => by
    have hΩ := (hΓS r).1
    have h1 := (hasDerivAt_gauge (c₀ := 1) (k := 1) hℓ.1 one_pos hΩ).comp r
      (hasDerivAt_nullY_comp hd.hasDerivAt)
    rw [show (fun r => unipG α β (nullY (Γ r))) = gauge α β 1 1 1 ∘ fun s => nullY (Γ s) from rfl,
      h1.deriv, one_mul]
    refine Real.abs_le_sqrt ?_
    rw [minkQ_deriv_of_mem_unipS hℓ hΓS hd, mul_pow]
    have h2 := gauge'_sq_le (α := α) (β := β) (nullY (Γ r))
    have h3 : 0 ≤ ∑ i, (1 + nullY (Γ r) * ℓ i) ^ 2 * zetaD ℓ i (Γ r) (deriv Γ r) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    nlinarith [sq_nonneg (nullY (deriv Γ r))]
  linarith

/-- **Lengths control `ζ` where `1 + yλᵢ` stays away from `0`**: along a Lipschitz curve of `S`
on which `c₀ ≤ |1 + yλᵢ|` over `[0, 1]`, `c₀ |ζᵢ(1) − ζᵢ(0)| ≤ ∫₀¹ √|Γ′|²` (l.720–735). -/
theorem mul_abs_zeta_sub_le (hℓ : IsUnipComponent ℓ α β) {Γ : ℝ → Minkowski (d + 1)} {K : ℝ≥0}
    (hK : LipschitzWith K Γ) (hΓS : ∀ s, Γ s ∈ unipS ℓ α β) {c₀ : ℝ} (hc₀ : 0 < c₀) (i : Fin d)
    (hc : ∀ r ∈ Icc (0 : ℝ) 1, c₀ ≤ |1 + nullY (Γ r) * ℓ i|) :
    c₀ * |zeta ℓ i (Γ 1) - zeta ℓ i (Γ 0)| ≤ ∫ r in (0 : ℝ)..1, √(minkQ (deriv Γ r)) := by
  obtain ⟨KY, hYL⟩ := lipschitzWith_nullY_comp hK
  obtain ⟨KZ, hZL⟩ := lipschitzWith_nullZ_comp hK i
  have hwL : LipschitzWith (‖ℓ i‖₊ * KY) fun r => 1 + nullY (Γ r) * ℓ i := by
    refine LipschitzWith.of_dist_le_mul fun r r' => ?_
    rw [Real.dist_eq, show 1 + nullY (Γ r) * ℓ i - (1 + nullY (Γ r') * ℓ i) =
      ℓ i * (nullY (Γ r) - nullY (Γ r')) by ring, abs_mul, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [← Real.dist_eq]; exact hYL.dist_le_mul r r')
      (abs_nonneg _)
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hZL.continuous.continuousOn
  obtain ⟨Bw, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hwL.continuous.continuousOn
  obtain ⟨Kφ, hφ⟩ := exists_lipschitzOnWith_div hZL.lipschitzOnWith hwL.lipschitzOnWith hc₀
    (fun r hr => by simpa [Real.norm_eq_abs] using hA r hr)
    (fun r hr => by simpa [Real.norm_eq_abs] using hB r hr) hc
  have := abs_sub_le_mul_integral hK zero_le_one hφ (one_div_pos.2 hc₀).le fun r hr hd => by
    have hΩ := (hΓS r).1
    have h1 := hasDerivAt_zeta_comp hℓ hd.hasDerivAt hΩ i
    rw [show (fun r => nullZ (Γ r) i / (1 + nullY (Γ r) * ℓ i)) = fun s => zeta ℓ i (Γ s)
      from rfl, h1.deriv]
    have hs := hc r (Ioo_subset_Icc_self hr)
    have h2 : |1 + nullY (Γ r) * ℓ i| * |zetaD ℓ i (Γ r) (deriv Γ r)| ≤
        √(minkQ (deriv Γ r)) := by
      rw [← abs_mul]
      refine Real.abs_le_sqrt ?_
      rw [minkQ_deriv_of_mem_unipS hℓ hΓS hd, mul_pow]
      have h3 := Finset.single_le_sum (f := fun j =>
        (1 + nullY (Γ r) * ℓ j) ^ 2 * zetaD ℓ j (Γ r) (deriv Γ r) ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
      have h4 : 0 ≤ 2 * gauge' α β (3 / 2) 2 3 (nullY (Γ r)) * nullY (deriv Γ r) ^ 2 := by
        have := gauge'_sq_le (α := α) (β := β) (nullY (Γ r))
        have := sq_nonneg (gauge' α β 1 1 1 (nullY (Γ r)))
        have := sq_nonneg (nullY (deriv Γ r))
        nlinarith
      linarith
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc₀]
    calc |zetaD ℓ i (Γ r) (deriv Γ r)| * c₀
        ≤ |zetaD ℓ i (Γ r) (deriv Γ r)| * |1 + nullY (Γ r) * ℓ i| :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ √(minkQ (deriv Γ r)) := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc₀] at this
  have e : (fun r => nullZ (Γ r) i / (1 + nullY (Γ r) * ℓ i)) 1 -
      (fun r => nullZ (Γ r) i / (1 + nullY (Γ r) * ℓ i)) 0 = zeta ℓ i (Γ 1) - zeta ℓ i (Γ 0) := rfl
  rw [e] at this
  linarith

end PathBounds2

section Complete

open MeasureTheory

variable {ℓ : Fin d → ℝ} {α β : EReal}

theorem continuous_ofNull :
    Continuous (fun w : ℝ × ℝ × EuclideanSpace ℝ (Fin d) => ofNull (d := d) w.1 w.2.1 w.2.2) := by
  unfold ofNull
  fun_prop

theorem abs_sub_le_abs_unipG_sub (hαβ : α < β) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ gI α β)
    (h₂ : y₂ ∈ gI α β) : |y₂ - y₁| ≤ |unipG α β y₂ - unipG α β y₁| := by
  rcases le_total y₁ y₂ with h | h
  · have := gauge_sub_ge (c₀ := 1) (k := 1) hαβ one_pos h₁ h₂ h
    rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact (by linarith : y₂ - y₁ ≤ unipG α β y₂ - unipG α β y₁).trans (le_abs_self _)
  · have := gauge_sub_ge (c₀ := 1) (k := 1) hαβ one_pos h₂ h₁ h
    rw [abs_of_nonpos (sub_nonpos.2 h), abs_sub_comm]
    exact (by linarith : -(y₂ - y₁) ≤ unipG α β y₁ - unipG α β y₂).trans (le_abs_self _)

/-- **A bound on `G` confines `y` to a compact subinterval of `]α, β[`** (the divergence of
`∫ a` at both ends, l.712–720). -/
theorem exists_Icc_of_abs_unipG_le (hαβ : α < β) (g₀ C : ℝ) :
    ∃ m M : ℝ, Icc m M ⊆ gI α β ∧ ∀ y ∈ gI α β, |unipG α β y - g₀| ≤ C → y ∈ Icc m M := by
  obtain ⟨m, hm, hGm⟩ := gauge_unbounded_below (c₀ := 1) (c := 1) (k := 1) hαβ one_pos one_pos
    le_rfl (g₀ - C)
  obtain ⟨M, hM, hGM⟩ := gauge_unbounded_above (c₀ := 1) (c := 1) (k := 1) hαβ one_pos one_pos
    le_rfl (g₀ + C)
  refine ⟨m, M, Icc_subset_gI hm hM, fun y hy hG => ⟨?_, ?_⟩⟩
  · by_contra h
    push Not at h
    have := gauge_sub_ge (c₀ := 1) (k := 1) hαβ one_pos hy hm h.le
    have := (abs_le.1 hG).1
    linarith
  · by_contra h
    push Not at h
    have := gauge_sub_ge (c₀ := 1) (k := 1) hαβ one_pos hM hy h.le
    have := (abs_le.1 hG).2
    linarith

/-- `|1 + yλᵢ|` is bounded away from `0` on a compact subinterval of `]α, β[`. -/
theorem exists_pos_le_abs_one_add (hℓ : IsUnipComponent ℓ α β) {m M : ℝ}
    (hmM : Icc m M ⊆ gI α β) : ∃ c₀ > 0, ∀ y ∈ Icc m M, ∀ i, c₀ ≤ |1 + y * ℓ i| := by
  rcases (Icc m M).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, by simp [he]⟩
  have hmi : ∀ i, ∃ c > 0, ∀ y ∈ Icc m M, c ≤ |1 + y * ℓ i| := fun i => by
    obtain ⟨y₁, hy₁, hmin⟩ := isCompact_Icc.exists_isMinOn hne
      (Continuous.continuousOn (f := fun y : ℝ => |1 + y * ℓ i|) (by fun_prop))
    exact ⟨|1 + y₁ * ℓ i|, abs_pos.2 (hℓ.2.1 _ (hmM hy₁).1 (hmM hy₁).2 i), fun y hy => hmin hy⟩
  choose mi hmi0 hmiK using hmi
  have hsum0 : 0 ≤ ∑ i, 1 / mi i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hmi0 i)).le
  refine ⟨(1 + ∑ i, 1 / mi i)⁻¹, inv_pos.2 (by linarith), fun y hy i => ?_⟩
  refine le_trans ?_ (hmiK i y hy)
  have h1 : 1 / mi i ≤ ∑ j, 1 / mi j :=
    le_sum_of_nonneg' (w := fun j => 1 / mi j) (fun j => (one_div_pos.2 (hmi0 j)).le) i
  rw [inv_le_comm₀ (by linarith) (hmi0 i)]
  rw [one_div] at h1; linarith

/-- **A pair at induced distance `< L` is joined by a Lipschitz curve of `S` of length `< L`.** -/
theorem exists_curve_of_edist_lt {V : Opens (Minkowski (d + 1))}
    {x y : InducedLength (unipS ℓ α β) V} {L : ℝ} (hL : 0 < L)
    (hxy : edist x y < ENNReal.ofReal L) :
    ∃ (Γ : ℝ → Minkowski (d + 1)) (K : ℝ≥0), LipschitzWith K Γ ∧ (∀ s, Γ s ∈ unipS ℓ α β) ∧
      Γ 0 = (InducedLength.toSubtype x : Minkowski (d + 1)) ∧
      Γ 1 = (InducedLength.toSubtype y : Minkowski (d + 1)) ∧
      ∫ r in (0 : ℝ)..1, √(minkQ (deriv Γ r)) < L := by
  rw [InducedLength.edist_def, iInf_lt_iff] at hxy
  obtain ⟨γ, hγ⟩ := hxy
  by_cases hL' : IsLipschitzCurve γ.toContinuousMap
  swap
  · rw [lengthOn_of_not_isLipschitzCurve hL'] at hγ; exact absurd hγ (not_lt.2 le_top)
  obtain ⟨K, hK⟩ := hL'
  rw [lengthOn_of_isLipschitzCurve ⟨K, hK⟩, lorentzLength_eq_ofReal_integral hK zero_le_one,
    ENNReal.ofReal_lt_ofReal_iff hL] at hγ
  refine ⟨curveExtend γ.toContinuousMap, K, hK, fun s => ?_, ?_, ?_, hγ⟩
  · rw [curveExtend_path]; exact (γ.extend s).2.1
  · rw [curveExtend_path]; simp
  · rw [curveExtend_path]; simp

/-- **The two bounds for a pair at induced distance `< L`**: `|ΔG| < L`, and `c₀ |Δζᵢ| < L`
whenever `c₀ ≤ |1 + yλᵢ|` on the `G`-ball of radius `L` around the first point. -/
theorem bounds_of_edist_lt (hℓ : IsUnipComponent ℓ α β) {V : Opens (Minkowski (d + 1))}
    {x y : InducedLength (unipS ℓ α β) V} {L : ℝ} (hL : 0 < L)
    (hxy : edist x y < ENNReal.ofReal L) :
    |unipG α β (nullY (InducedLength.toSubtype y : Minkowski (d + 1))) -
        unipG α β (nullY (InducedLength.toSubtype x : Minkowski (d + 1)))| < L ∧
      ∀ c₀ > 0, ∀ i, (∀ y' ∈ gI α β,
        |unipG α β y' - unipG α β (nullY (InducedLength.toSubtype x : Minkowski (d + 1)))| ≤ L →
          c₀ ≤ |1 + y' * ℓ i|) →
        c₀ * |zeta ℓ i (InducedLength.toSubtype y : Minkowski (d + 1)) -
          zeta ℓ i (InducedLength.toSubtype x : Minkowski (d + 1))| < L := by
  obtain ⟨Γ, K, hK, hΓS, h0, h1, hlen⟩ := exists_curve_of_edist_lt hL hxy
  rw [← h0, ← h1]
  refine ⟨(abs_unipG_sub_le hℓ hK hΓS zero_le_one).trans_lt hlen, fun c₀ hc₀ i hc => ?_⟩
  refine lt_of_le_of_lt (mul_abs_zeta_sub_le hℓ hK hΓS hc₀ i fun r hr => ?_) hlen
  refine hc _ (hΓS r).1 ?_
  have hbdΓ : ∀ r, √(minkQ (deriv Γ r)) ≤ K := fun r =>
    (sqrt_minkQ_le _).trans ((norm_snd_le _).trans (norm_deriv_le_of_lipschitz hK))
  have hint : IntervalIntegrable (fun s => √(minkQ (deriv Γ s))) volume 0 1 :=
    intervalIntegrable_of_bound (Real.continuous_sqrt.measurable.comp
      (continuous_minkQ.measurable.comp (measurable_deriv Γ))) K (fun s => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hbdΓ s) 0 1
  have h2 : ∫ s in (0 : ℝ)..r, √(minkQ (deriv Γ s)) ≤ ∫ s in (0 : ℝ)..1, √(minkQ (deriv Γ s)) :=
    intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      (ae_of_all _ fun s => Real.sqrt_nonneg _) hint
  exact (abs_unipG_sub_le hℓ hK hΓS hr.1).trans (h2.trans hlen.le)

end Complete

section Complete2

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- The parametrisation `(y, ζ) ↦ S` of the slice. -/
noncomputable def unipPsi (ℓ : Fin d → ℝ) (α β : EReal) (w : ℝ × (Fin d → ℝ)) :
    Minkowski (d + 1) :=
  ofNull (unipF α β w.1 - 1 / 2 * ∑ i, ℓ i * (1 + w.1 * ℓ i) * w.2 i ^ 2) w.1
    (WithLp.toLp 2 fun i => (1 + w.1 * ℓ i) * w.2 i)

theorem eq_unipPsi (hℓ : IsUnipComponent ℓ α β) {p : Minkowski (d + 1)} (hp : p ∈ unipS ℓ α β) :
    p = unipPsi ℓ α β (nullY p, fun i => zeta ℓ i p) := by
  refine eq_of_null ?_ ?_ ?_
  · rw [unipPsi, nullX_ofNull, nullX_eq_of_mem_unipSlice hℓ hp]
  · rw [unipPsi, nullY_ofNull]
  · intro i; rw [unipPsi, nullZ_ofNull, nullZ_eq_mul_zeta hℓ hp.1 i]

theorem unipPsi_mem (hℓ : IsUnipComponent ℓ α β) {w : ℝ × (Fin d → ℝ)} (hw : w.1 ∈ gI α β) :
    unipPsi ℓ α β w ∈ unipS ℓ α β := by
  have hy : nullY (unipPsi ℓ α β w) = w.1 := by rw [unipPsi, nullY_ofNull]
  refine ⟨by rw [unipDomain]; show α < _ ∧ _ < β; rw [hy]; exact hw, ?_⟩
  rw [hy, unipPhi]
  rw [show nullX (unipPsi ℓ α β w) = _ from by rw [unipPsi, nullX_ofNull]]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hℓ.2.1 _ hw.1 hw.2 i
  rw [unipPsi, nullZ_ofNull]
  change _ = ℓ i * ((1 + w.1 * ℓ i) * w.2 i) ^ 2 / (1 + w.1 * ℓ i)
  field_simp

theorem continuousAt_unipPsi (hℓ : IsUnipComponent ℓ α β) {w : ℝ × (Fin d → ℝ)}
    (hw : w.1 ∈ gI α β) : ContinuousAt (unipPsi ℓ α β) w := by
  have hF : ContinuousAt (fun w : ℝ × (Fin d → ℝ) => unipF α β w.1) w :=
    ((continuousOn_gauge hℓ.1 (by norm_num)).continuousAt (isOpen_gI.mem_nhds hw)).comp
      continuous_fst.continuousAt
  have h1 : ContinuousAt (fun w : ℝ × (Fin d → ℝ) =>
      (unipF α β w.1 - 1 / 2 * ∑ i, ℓ i * (1 + w.1 * ℓ i) * w.2 i ^ 2, w.1,
        (WithLp.toLp 2 fun i => (1 + w.1 * ℓ i) * w.2 i : EuclideanSpace ℝ (Fin d)))) w := by
    refine hF.sub (Continuous.continuousAt ?_) |>.prodMk (continuous_fst.continuousAt.prodMk
      (Continuous.continuousAt ?_))
    · fun_prop
    · exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  exact (continuous_ofNull.continuousAt).comp (f := fun w : ℝ × (Fin d → ℝ) =>
      (unipF α β w.1 - 1 / 2 * ∑ i, ℓ i * (1 + w.1 * ℓ i) * w.2 i ^ 2, w.1,
        (WithLp.toLp 2 fun i => (1 + w.1 * ℓ i) * w.2 i : EuclideanSpace ℝ (Fin d)))) h1

end Complete2

section Complete3

variable {ℓ : Fin d → ℝ} {α β : EReal}

/-- **`S_f` is complete for its induced length** (`unipcomplet`, l.712–735). A Cauchy sequence
has `G(y)` Cauchy, hence `y` Cauchy (`G′ ≥ 1`) and confined to a compact subinterval of `]α, β[`
(`G` diverges at both ends), where `1 + yλᵢ` stays away from `0`, so `ζ` is Cauchy too; the
limit `(y*, ζ*)` parametrises a point of `S`, and the two topologies agree. -/
theorem completeSpace_inducedLength_unipS (hℓ : IsUnipComponent ℓ α β) :
    CompleteSpace (InducedLength (unipS ℓ α β) (unipDomain (d := d) α β)) := by
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  set P : ℕ → Minkowski (d + 1) := fun n => (InducedLength.toSubtype (u n) : Minkowski (d + 1))
  have hPS : ∀ n, P n ∈ unipS ℓ α β := fun n => (InducedLength.toSubtype (u n)).2.1
  rw [EMetric.cauchySeq_iff] at hu
  obtain ⟨N₀, hN₀⟩ := hu (ENNReal.ofReal 1) (by simp)
  set g₀ := unipG α β (nullY (P N₀))
  obtain ⟨m₁, M₁, hI, hconf⟩ := exists_Icc_of_abs_unipG_le hℓ.1 g₀ 2
  obtain ⟨c₀, hc₀, hc⟩ := exists_pos_le_abs_one_add hℓ hI
  have hG1 : ∀ n ≥ N₀, |unipG α β (nullY (P n)) - g₀| < 1 := fun n hn =>
    (bounds_of_edist_lt hℓ one_pos (hN₀ N₀ le_rfl n hn)).1
  have hYI : ∀ n ≥ N₀, nullY (P n) ∈ Icc m₁ M₁ := fun n hn =>
    hconf _ (hPS n).1 ((hG1 n hn).le.trans (by norm_num))
  -- `y` is Cauchy
  have hYc : CauchySeq fun n => nullY (P n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hu (ENNReal.ofReal ε) (by simpa using hε)
    refine ⟨N₁, fun m hm n hn => ?_⟩
    have h := (bounds_of_edist_lt hℓ hε (hN₁ n hn m hm)).1
    rw [Real.dist_eq]
    exact (abs_sub_le_abs_unipG_sub hℓ.1 (hPS n).1 (hPS m).1).trans_lt h
  -- `ζ` is Cauchy
  have hZc : ∀ i, CauchySeq fun n => zeta ℓ i (P n) := fun i => by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set η := min 1 (c₀ * ε)
    have hη : 0 < η := lt_min one_pos (mul_pos hc₀ hε)
    obtain ⟨N₁, hN₁⟩ := hu (ENNReal.ofReal η) (by simpa using hη)
    refine ⟨max N₀ N₁, fun m hm n hn => ?_⟩
    have h := (bounds_of_edist_lt hℓ hη (hN₁ n (le_of_max_le_right hn) m
      (le_of_max_le_right hm))).2 c₀ hc₀ i fun y' hy' hG => by
        refine hc y' (hconf y' hy' ?_) i
        have := hG1 n (le_of_max_le_left hn)
        have hη1 : η ≤ 1 := min_le_left _ _
        have := abs_sub_le (unipG α β y') (unipG α β (nullY (P n))) g₀
        linarith
    rw [Real.dist_eq]
    have hη2 : η ≤ c₀ * ε := min_le_right _ _
    have : c₀ * |zeta ℓ i (P m) - zeta ℓ i (P n)| < c₀ * ε := h.trans_le hη2
    exact lt_of_mul_lt_mul_left this hc₀.le
  obtain ⟨y₁, hy₁⟩ := cauchySeq_tendsto_of_complete hYc
  choose ζ₁ hζ₁ using fun i => cauchySeq_tendsto_of_complete (hZc i)
  have hy₁I : y₁ ∈ Icc m₁ M₁ :=
    isClosed_Icc.mem_of_tendsto hy₁ (eventually_atTop.2 ⟨N₀, hYI⟩)
  have hy₁g : y₁ ∈ gI α β := hI hy₁I
  set w₁ : ℝ × (Fin d → ℝ) := (y₁, ζ₁)
  have hw : Tendsto (fun n => ((nullY (P n), fun i => zeta ℓ i (P n)) : ℝ × (Fin d → ℝ)))
      atTop (𝓝 w₁) := hy₁.prodMk_nhds (tendsto_pi_nhds.2 hζ₁)
  have hP : Tendsto P atTop (𝓝 (unipPsi ℓ α β w₁)) := by
    have := (continuousAt_unipPsi hℓ (w := w₁) hy₁g).tendsto.comp hw
    refine this.congr fun n => ?_
    exact (eq_unipPsi hℓ (hPS n)).symm
  have hp₁ : unipPsi ℓ α β w₁ ∈ unipS ℓ α β ∩
      ((unipDomain (d := d) α β : Opens (Minkowski (d + 1))) : Set (Minkowski (d + 1))) :=
    ⟨unipPsi_mem hℓ hy₁g, (unipPsi_mem hℓ hy₁g).1⟩
  refine ⟨InducedLength.toSubtype.symm ⟨_, hp₁⟩, ?_⟩
  have hL := isSpacelikeLipschitzIn_unipS hℓ (V := unipDomain (d := d) α β) le_rfl
  have hcont := hL.toIsLipschitzHypersurfaceIn.continuous_toSubtype_symm
  have hsub : Tendsto (fun n => InducedLength.toSubtype (u n)) atTop (𝓝 ⟨_, hp₁⟩) :=
    tendsto_subtype_rng.2 hP
  exact (hcont.tendsto _).comp hsub

end Complete3

/-! ### Descent to the quotient, in the frame `φ` -/

section Descent

/-- `φ p = L(φ) p + φ 0` (copy of `RegularComplete`'s private `rC_smul_eq`). -/
theorem unip_smul_eq (φ : isom d) (p : Minkowski d) :
    φ • p = (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear.toContinuousLinearEquiv p +
      φ • (0 : Minkowski d) := by
  have := isom_sub (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d) 0 p
  rw [sub_zero] at this
  rw [isom_smul_def, isom_smul_def]
  change _ = (φ : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear p + _
  rw [← this]
  abel

/-- **[3.U] Unipotent spacetimes are Cauchy-complete** (l.743–744, "the quotient of `Ω` by `Γ`
is globally hyperbolic and Cauchy-complete"): the slice `S = S_f` (`unipS`) is a `Γ`-invariant
Cauchy surface of the slab (`unipAction_mem_unipSlice`, `isCauchySurfaceOn_unipS`), spacelike
Lipschitz (`isSpacelikeLipschitzIn_unipS`) and complete for its induced length
(`completeSpace_inducedLength_unipS`); `Γ` acts acausally (`actsAcausally_unip`); everything
is carried to the frame `φ` and descends by `RegularComplete`'s (A),
`isCauchyComplete_of_isQuotientOf_of_invariant`. -/
theorem isCauchyComplete_of_isUnipotentSpacetime {M : FlatSpacetime.{u} (d + 1)}
    (hU : IsUnipotentSpacetime M) : IsCauchyComplete (d + 1) M := by
  obtain ⟨φ, ℓ, α, β, L, Γ, hL, hℓ, hΓ, -, hq⟩ := hU
  haveI := hL
  haveI := unip_invariant (α := α) (β := β) Γ L hΓ
  haveI := unip_isCancelSMul Γ L hℓ hΓ
  have hΓ' : ∀ γ ∈ Γ, ∃ t, ∀ p : Minkowski (d + 1), γ • p = unipAction ℓ t p := fun γ hγ =>
    let ⟨t, _, ht⟩ := hΓ γ hγ; ⟨t, ht⟩
  set Ω : Opens (Minkowski (d + 1)) := unipDomain (d := d) α β with hΩdef
  set S : Set (Minkowski (d + 1)) := unipS ℓ α β with hSdef
  have hSΩ : S ⊆ Ω := fun p hp => hp.1
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ S, γ • p ∈ S := fun γ hγ p hp => by
    obtain ⟨t, ht⟩ := hΓ' γ hγ
    rw [ht]; exact unipAction_mem_unipSlice ℓ _ hℓ t hp
  have hC : (minkowski (d + 1)).IsCauchySurfaceOn Ω S := isCauchySurfaceOn_unipS hℓ
  have hLS : IsSpacelikeLipschitzIn Ω S := isSpacelikeLipschitzIn_unipS hℓ le_rfl
  obtain ⟨hc, ht⟩ := rC_complete_opens_of_inducedLength hLS
    (completeSpace_inducedLength_unipS hℓ)
  set A : Minkowski (d + 1) ≃L[ℝ] Minkowski (d + 1) :=
    (φ : Minkowski (d + 1) ≃ᵃ[ℝ] Minkowski (d + 1)).linear.toContinuousLinearEquiv with hAdef
  have hA : ∀ v, minkQ (A v) = minkQ v := fun v => minkQ_isom_linear φ v
  have hmem : ∀ p, (p ∈ Ω ∧ p ∈ S) ↔
      (A p + φ • (0 : Minkowski (d + 1)) ∈ isomImage φ Ω ∧
        A p + φ • (0 : Minkowski (d + 1)) ∈ (fun p => φ • p) '' S) := fun p => by
    rw [← unip_smul_eq, smul_mem_isomImage, (MulAction.injective φ).mem_set_image]
  obtain ⟨hc', ht'⟩ := rC_transfer A hA _ hmem hc ht
  refine isCauchyComplete_of_isQuotientOf_of_invariant hq
    (actsAcausally_frameConj φ Γ Ω (actsAcausally_unip Γ hℓ hΓ')) ?_
    (image_invariant_frameConj φ Γ hinv) (isCauchySurfaceOn_isomImage φ Ω hSΩ hC) ?_ hc' ht'
  · rintro _ ⟨p, hp, rfl⟩
    exact smul_mem_isomImage.2 (hSΩ hp)
  · rw [Set.image_smul]
    exact hLS.smul isom_strongMorphism φ

end Descent

/-- **[3.U] unipotent spacetimes are GH and Cauchy-complete** (`unipcomplet`, l.705–753). -/
theorem gh_isCauchyComplete_of_isUnipotentSpacetime {e : ℕ} {M : FlatSpacetime.{u} (e + 1)}
    (hU : IsUnipotentSpacetime M) : GH M ∧ IsCauchyComplete (e + 1) M :=
  ⟨gh_of_isUnipotentSpacetime hU, isCauchyComplete_of_isUnipotentSpacetime hU⟩

end Causal.Flat.Cla
