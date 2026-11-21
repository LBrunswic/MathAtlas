import GX.Spherical.TroyanovPolygon

/-!
# Troyanov's theorem for four angles, one above `2π`: the double of a spherical dart

Target `T-gx-troyanov-four` (`roadmap/roadmap.toml`; DEC-136, Troyanov's theorem proved, not
assumed). `papers/gx`, 0 `sorry`, standard axioms only. **No label is marked here.**

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial, not marked: the row
  needs Troyanov's theorem for `s ≥ 5` with an angle above `2π` (`T-gx-troyanov`) and the
  Thurston suspension facts (`GX.thurstonSuspensionFacts`), both outside this module. Here the
  cited theorem (`MR1005085`), in the shape of `GX.TroyanovTheorem`
  (`GXScaffold.Spherical.TroyanovAngles`, restated inline), is proved at `s = 4` with an angle
  above `2π`: **`GX.troyanovTheorem_four_of_exists_gt_two_pi`**; with
  `GX.Spherical.TroyanovPolygon`, for every angle at `s = 4` (`GX.troyanovTheorem_four`), and
  `GX.TroyanovTheorem` reduces to its case `s ≥ 5`, every `θ_i ≠ 2π`, some `θ_i > 2π`
  (`GX.troyanovTheorem_of_five_le_of_exists_gt_two_pi`).
* At `s = 4` the condition admits at most one angle above `2π`, and that angle is below `4π`
  (`GX.TroyanovAngleCondition.four_of_gt_two_pi`); the case is not vacuous and meets the cex's
  genericity (`GX.troyanovAngleCondition_four_gt_two_pi`: `(5π/2, π/2, 3π/5, 7π/10)`).
* The dart: `GX.DartParams` (a triangle `T` minus a triangle `T'` on the same base, the dart's
  sides `GX.dartN`), `GX.exists_dartParams` (the intermediate value theorem on a segment of base
  angles of `T'`), `GX.DartParams.polygon`, `GX.exists_isConeSphere_dart` (under hypotheses
  weaker than Troyanov's).
* The double of a spherical polygon, convex or not, given polar charts at its vertices:
  `GX.StarFrames` (frames at vertices of angle `α_i ∈ ]0, 2π[ ∖ {π}`, reflex vertices allowed;
  `GX.polarFold` onto a reflex sector: `GX.exists_polarFold_eq_reflex`,
  `GX.polarFold_eq_iff_of_lt_two_pi`), `GX.StarPolygon` (the data the double needs),
  `GX.StarPolygon.isConeSphere`. A union of two convex bodies with a common interior point is a
  closed disc: `GX.exists_homeomorph_union_convex`.

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. We know from
> Troyanov \cite{MR1005085}  that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> (l.1930)

## The construction

At `s = 4` put the angle above `2π` first and `α_i = θ_i / 2`: `α_0 ∈ ]π, 2π[`, and the
condition gives `α_0 + α_j + α_k ≤ 2π` for `j, k ≥ 1` and `∑ α_i > 2π`. The dart is
`T ∖ T'`: on a base `v₂ v₄` of length `L`, `T` has base angles `p = u + α_1`, `q = w + α_3` and
apex `v_2` of angle `α_2`; `T'` has base angles `u`, `w` and apex `v_0` of angle `2π − α_0`. Its
sides are `n₀ = −ν_L(u)`, `n₁ = ν_L(p)`, `n₂ = ν_R(q)`, `n₃ = −ν_R(w)` (`GX.dartN`) and the dart
is `{n₁ ≥ 0, n₂ ≥ 0} ∩ ({n₀ ≥ 0} ∪ {n₃ ≥ 0})`, a union of two convex triangles. The two
triangles agree on `L` (the spherical law of cosines, `hT`, `hT'`) at some point of the segment
of base angles `(u, w)` from `(ε/2, ε/2)` to `(ε + δ, δ)`, `ε = α_0 − π`: at the first end `T'`
degenerates to a point (`cos L = 1` for `T'`), at the second to a lune (`cos L = −1`), while `T`
stays a triangle (`GX.exists_dartParams`). The double: the dart is a closed disc in the
stereographic chart at `v_0` (`GX.exists_homeomorph_union_convex`); at each vertex `v_i` the
polar fold onto the sector of angle `α_i` (reflex at `v_0`) is a chart on a domain `F i`
(`GX.DartParams.F`: at `v_1` the triangle cut off by the great circle of `e₄₁` (`n₃ < 0`), at
`v_3` the one cut off by that of `e₁₂` (`n₀ < 0`); at `v_2` the dart off the sides through
`v_0`; at `v_0` the dart off the sides through `v_2`). A side is a genuine side
(`GX.DartParams.onSide`: `e₁₂` is the part of its great circle with `n₃ ≤ 0`), so a side met by
a chart is a side through its vertex; the comparison of the cone charts through the developing
maps is that of `GX.Spherical.TroyanovPolygon`, verbatim.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s ≥ 3` conical singularities (l.1930) | `s = 4` (the target); `s ≥ 5`, some angle `> 2π`: open |
| Troyanov's condition (l.1930) | ✓ carried: `TroyanovAngleCondition θ`, verbatim (DEC-69's) |
| the angles `θ_i` arbitrary | ⚠ restricted: at `s = 4`, some `θ_i > 2π` (the case left by `TroyanovPolygon`) |
| `Σ` ≅ sphere, conical singularities of angles `θ_i` | ✓ `GX.IsConeSphere` (OQ-37 (b)) |
| Troyanov's theorem (`MR1005085`), cited | ✓ proved in this case, not assumed (DEC-136) |

## SCOPE (disclosed)

* **(a)** `s = 4` only; `s ≥ 5` with some angle `> 2π` is not proved (the row stays partial).
* **(b)** The metric is not formalized (as in `GX.Spherical.ConeSurface`): a cone point is an
  `X_θ`-chart onto a neighbourhood of the apex of `C_θ`.
* **(c)** The surface is the doubled dart, not Troyanov's variational solution.
  `GX.exists_isConeSphere_dart` holds under hypotheses weaker than the printed condition
  (`α_0 + α_1, α_0 + α_3 < 2π`, `α_2 < π`, `χ' > 0`, `χ' < 2θ_2`, `χ' < 2θ_3`,
  `α_2 + α_3 < α_0 + α_1`); which of them are necessary for a dart is not studied.
* **(d)** `GX.TroyanovTheorem` is restated inline (its body): the scaffold `TroyanovAngles` is not
  imported. `M : Type`, as there.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.TroyanovPolygon` (`troyanovTheorem_of_exists_gt_two_pi`, `IsConeSphere.comp_equiv`,
`SphPolygon.norm_le_of_gfun_nonneg`), `GX.Spherical.TroyanovTriangle` (`frameSO3`, `polarFold`,
`isOpenMap_restrict_of_isCompact`, `symm_trans_mem_aeAtlas_of_opens`,
`isPortly_compl_singleton_sph2`, the generic lemmas of `GX.SphTriangle`),
`GX.Spherical.ConeSurface`, mathlib's `gaugeRescale` and `intermediate_value_Icc`.
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace Matrix

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

section ReflexFold

/-! ### Folding the plane onto a sector of angle up to `2π` -/

section PolarFoldReflex

theorem sin_neg_of_pi_lt_of_lt_two_pi {x : ℝ} (h1 : π < x) (h2 : x < 2 * π) :
    Real.sin x < 0 := by
  rw [← Real.sin_sub_two_pi]
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

/-- The sector form of a point `r e^{iγ}`: `sin α Re − cos α Im = r sin(α − γ)`. -/
theorem sector_of_eq_exp {α r γ : ℝ} {v : ℂ}
    (hv : v = (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I)) :
    Real.sin α * v.re - Real.cos α * v.im = r * Real.sin (α - γ) ∧ v.im = r * Real.sin γ := by
  have hre : v.re = r * Real.cos γ := by
    rw [hv, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : v.im = r * Real.sin γ := by
    rw [hv, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  refine ⟨?_, him⟩
  rw [hre, him, Real.sin_sub]; ring

variable {α : ℝ}

/-- On the positive real axis the fold angle is `0`. -/
theorem foldAngle_of_re_nonneg {h : ℂ} (h0 : h ≠ 0) (him : h.im = 0) (hre : 0 ≤ h.re) :
    foldAngle α h = 0 := by
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 = ‖h‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, him]; ring
  have e : h.re = ‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
  rw [foldAngle, e, div_self hn.ne', Real.arccos_one, mul_zero]

/-- On the negative real axis the fold angle is `α`. -/
theorem foldAngle_of_re_nonpos {h : ℂ} (h0 : h ≠ 0) (him : h.im = 0) (hre : h.re ≤ 0) :
    foldAngle α h = α := by
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 = ‖h‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, him]; ring
  have e : h.re = -‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
  rw [foldAngle, e, neg_div, div_self hn.ne', Real.arccos_neg_one, div_mul_cancel₀ _
    Real.pi_ne_zero]

/-- A fold angle `0` comes from the positive real axis. -/
theorem re_pos_of_foldAngle_eq_zero (hα0 : 0 < α) {h : ℂ} (h0 : h ≠ 0)
    (hf : foldAngle α h = 0) : h.im = 0 ∧ 0 < h.re := by
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have ha : Real.arccos (h.re / ‖h‖) = 0 := by
    unfold foldAngle at hf
    rcases mul_eq_zero.1 hf with h1 | h1
    · exact absurd h1 (div_pos hα0 Real.pi_pos).ne'
    · exact h1
  have h1 : 1 ≤ h.re / ‖h‖ := Real.arccos_eq_zero.1 ha
  rw [le_div_iff₀ hn, one_mul] at h1
  have hsq : h.re ^ 2 + h.im ^ 2 = ‖h‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hle : h.re ≤ ‖h‖ := Complex.re_le_norm h
  have hre : h.re = ‖h‖ := le_antisymm hle h1
  refine ⟨?_, by rw [hre]; exact hn⟩
  rw [hre] at hsq
  nlinarith [sq_nonneg h.im]

/-- A fold angle `α` comes from the negative real axis. -/
theorem re_neg_of_foldAngle_eq (hα0 : 0 < α) {h : ℂ} (h0 : h ≠ 0)
    (hf : foldAngle α h = α) : h.im = 0 ∧ h.re < 0 := by
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have ha : Real.arccos (h.re / ‖h‖) = π := by
    unfold foldAngle at hf
    have : α / π * Real.arccos (h.re / ‖h‖) = α / π * π := by
      rw [hf, div_mul_cancel₀ _ Real.pi_ne_zero]
    exact mul_left_cancel₀ (div_pos hα0 Real.pi_pos).ne' this
  have h1 : h.re / ‖h‖ ≤ -1 := Real.arccos_eq_pi.1 ha
  rw [div_le_iff₀ hn, neg_one_mul] at h1
  have hsq : h.re ^ 2 + h.im ^ 2 = ‖h‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hle : -‖h‖ ≤ h.re := by
    have := Complex.abs_re_le_norm h
    have := neg_abs_le h.re
    linarith
  have hre : h.re = -‖h‖ := le_antisymm h1 hle
  refine ⟨?_, by rw [hre]; linarith⟩
  rw [hre] at hsq
  nlinarith [sq_nonneg h.im]

/-- The fold angle lies in `]0, α[` off the real axis. -/
theorem foldAngle_mem_Ioo (hα0 : 0 < α) {h : ℂ} (hh : h.im ≠ 0) :
    0 < foldAngle α h ∧ foldAngle α h < α := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e]; rfl)
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 + h.im ^ 2 = ‖h‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hi2 : 0 < h.im ^ 2 := by positivity
  have h1 : -1 < h.re / ‖h‖ := by
    rw [lt_div_iff₀ hn]; nlinarith [sq_nonneg (h.re + ‖h‖)]
  have h2 : h.re / ‖h‖ < 1 := by
    rw [div_lt_iff₀ hn]; nlinarith [sq_nonneg (h.re - ‖h‖)]
  have ha0 : 0 < Real.arccos (h.re / ‖h‖) := Real.arccos_pos.2 h2
  have haπ : Real.arccos (h.re / ‖h‖) < π := by
    rw [Real.arccos_lt_pi]; exact h1
  refine ⟨mul_pos (div_pos hα0 Real.pi_pos) ha0, ?_⟩
  unfold foldAngle
  calc α / π * Real.arccos (h.re / ‖h‖) < α / π * π :=
        mul_lt_mul_of_pos_left haπ (div_pos hα0 Real.pi_pos)
    _ = α := by field_simp

/-- **The fold onto a sector of angle `α < 2π` is injective up to conjugation.** -/
theorem polarFold_eq_iff_of_lt_two_pi (hα0 : 0 < α) (hα2 : α < 2 * π) {h h' : ℂ}
    (he : polarFold α h = polarFold α h') : h' = h ∨ h' = (starRingEnd ℂ) h := by
  have hn : ‖h‖ = ‖h'‖ := by rw [← norm_polarFold (α := α) h, he, norm_polarFold]
  by_cases h0 : h = 0
  · left; rw [h0, norm_zero] at hn; rw [h0]; exact norm_eq_zero.1 hn.symm
  have h0' : h' ≠ 0 := fun e => h0 (norm_eq_zero.1 (by rw [hn, e, norm_zero]))
  have hnp : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hc : Real.cos (foldAngle α h) = Real.cos (foldAngle α h') := by
    have e1 := congrArg Complex.re he
    rw [polarFold_re, polarFold_re, hn] at e1
    exact mul_left_cancel₀ (hn ▸ hnp).ne' e1
  have hs : Real.sin (foldAngle α h) = Real.sin (foldAngle α h') := by
    have e1 := congrArg Complex.im he
    rw [polarFold_im, polarFold_im, hn] at e1
    exact mul_left_cancel₀ (hn ▸ hnp).ne' e1
  have hb : foldAngle α h = foldAngle α h' := by
    have hcos : Real.cos (foldAngle α h - foldAngle α h') = 1 := by
      rw [Real.cos_sub, hc, hs]; nlinarith [Real.sin_sq_add_cos_sq (foldAngle α h')]
    have a1 := foldAngle_nonneg hα0.le h
    have a2 := foldAngle_le hα0.le h
    have a3 := foldAngle_nonneg hα0.le h'
    have a4 := foldAngle_le hα0.le h'
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).1 hcos
    linarith
  have ha : Real.arccos (h.re / ‖h‖) = Real.arccos (h'.re / ‖h'‖) := by
    unfold foldAngle at hb
    exact mul_left_cancel₀ (div_pos hα0 Real.pi_pos).ne' hb
  have hq := Real.arccos_injOn (re_div_norm_mem h0) (re_div_norm_mem h0') ha
  have hre : h.re = h'.re := by
    rw [← hn] at hq; exact (div_left_inj' hnp.ne').1 hq
  have him : h.im ^ 2 = h'.im ^ 2 := by
    have e1 : h.re ^ 2 + h.im ^ 2 = ‖h‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have e2 : h'.re ^ 2 + h'.im ^ 2 = ‖h'‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn, hre] at e1; linarith
  rcases abs_eq_abs.1 ((sq_eq_sq_iff_abs_eq_abs _ _).1 him) with h1 | h1
  · left; exact Complex.ext hre.symm h1.symm
  · right; apply Complex.ext
    · simp [hre]
    · simp [h1]

/-- The fold of `|v| e^{iπγ/α}` is `|v| e^{iγ}`, for `γ ∈ [0, α]`. -/
theorem polarFold_norm_mul_exp (hα0 : 0 < α) (r : ℝ) (hr : 0 ≤ r) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγα : γ ≤ α) :
    polarFold α ((r : ℂ) * Complex.exp (((π / α * γ : ℝ) : ℂ) * Complex.I)) =
        (r : ℂ) * Complex.exp ((γ : ℂ) * Complex.I) ∧
      0 ≤ ((r : ℂ) * Complex.exp (((π / α * γ : ℝ) : ℂ) * Complex.I)).im := by
  set κ := π / α * γ with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (div_nonneg Real.pi_pos.le hα0.le) hγ0
  have hκπ : κ ≤ π := by
    rw [hκ, div_mul_eq_mul_div, div_le_iff₀ hα0]; nlinarith [Real.pi_pos]
  refine ⟨?_, ?_⟩
  · rcases hr.lt_or_eq with hr | hr
    · have hnh : ‖(r : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)‖ = r := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
      have hre : ((r : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)).re = r * Real.cos κ := by
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      have hf : foldAngle α ((r : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)) = γ := by
        rw [foldAngle, hnh, hre, mul_div_cancel_left₀ _ hr.ne', Real.arccos_cos hκ0 hκπ, hκ]
        field_simp
      rw [polarFold, hnh, hf]
    · subst hr; simp
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi hκ0 hκπ)

variable (hα1 : π < α) (hα2 : α < 2 * π)
include hα1 hα2

theorem sin_neg_of_reflex : Real.sin α < 0 :=
  sin_neg_of_pi_lt_of_lt_two_pi hα1 hα2

/-- **The fold onto a reflex sector** lands in `{Im ≥ 0} ∪ {sin α Re − cos α Im ≥ 0}`. -/
theorem polarFold_mem_reflex (h : ℂ) :
    0 ≤ (polarFold α h).im ∨
      0 ≤ Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im := by
  have hα0 : 0 < α := by linarith [Real.pi_pos]
  have hb0 := foldAngle_nonneg hα0.le h
  have hb1 := foldAngle_le hα0.le h
  rw [polarFold_sector_re, polarFold_im]
  rcases le_total (foldAngle α h) π with hle | hle
  · left; exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi hb0 hle)
  · right
    exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))

/-- Off the real axis, the fold lands in the open reflex sector. -/
theorem polarFold_mem_reflex_strict {h : ℂ} (hh : h.im ≠ 0) :
    0 < (polarFold α h).im ∨
      0 < Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im := by
  have hα0 : 0 < α := by linarith [Real.pi_pos]
  have h0 : h ≠ 0 := fun e => hh (by rw [e]; rfl)
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  obtain ⟨hb0, hb1⟩ := foldAngle_mem_Ioo hα0 hh
  rw [polarFold_sector_re, polarFold_im]
  rcases lt_or_ge (foldAngle α h) π with hlt | hle
  · left; exact mul_pos hn (Real.sin_pos_of_pos_of_lt_pi hb0 hlt)
  · right; exact mul_pos hn (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

/-- On the real axis, `h ≥ 0`: the side `Im = 0` of the reflex sector, where `sin α Re ≤ 0`. -/
theorem polarFold_reflex_of_re_nonneg {h : ℂ} (him : h.im = 0) (hre : 0 ≤ h.re) :
    (polarFold α h).im = 0 ∧
      Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im ≤ 0 := by
  by_cases h0 : h = 0
  · subst h0; simp
  rw [polarFold_sector_re, polarFold_im, foldAngle_of_re_nonneg h0 him hre, Real.sin_zero,
    mul_zero, sub_zero]
  exact ⟨rfl, mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
    (sin_neg_of_reflex hα1 hα2).le⟩

/-- On the real axis, `h ≤ 0`: the side `sin α Re − cos α Im = 0`, where `Im ≤ 0`. -/
theorem polarFold_reflex_of_re_nonpos {h : ℂ} (him : h.im = 0) (hre : h.re ≤ 0) :
    Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0 ∧
      (polarFold α h).im ≤ 0 := by
  by_cases h0 : h = 0
  · subst h0; simp
  rw [polarFold_sector_re, polarFold_im, foldAngle_of_re_nonpos h0 him hre, sub_self,
    Real.sin_zero, mul_zero]
  exact ⟨rfl, mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
    (sin_neg_of_reflex hα1 hα2).le⟩

/-- The side `Im = 0`, `sin α Re − cos α Im ≤ 0` of the reflex sector comes from `h > 0`. -/
theorem re_pos_of_polarFold_reflex {h : ℂ} (h0 : h ≠ 0) (hI : (polarFold α h).im = 0)
    (hB : Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im ≤ 0) :
    h.im = 0 ∧ 0 < h.re := by
  have hα0 : 0 < α := by linarith [Real.pi_pos]
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hb0 := foldAngle_nonneg hα0.le h
  have hb1 := foldAngle_le hα0.le h
  rw [polarFold_im] at hI
  rw [polarFold_sector_re] at hB
  have hs : Real.sin (foldAngle α h) = 0 := by
    rcases mul_eq_zero.1 hI with h1 | h1
    · exact absurd h1 hn.ne'
    · exact h1
  refine re_pos_of_foldAngle_eq_zero hα0 h0 ?_
  rcases hb0.lt_or_eq with hlt | heq
  · exfalso
    rcases lt_trichotomy (foldAngle α h) π with h1 | h1 | h1
    · exact absurd hs (Real.sin_pos_of_pos_of_lt_pi hlt h1).ne'
    · rw [h1] at hB
      have : Real.sin (α - π) = -Real.sin α := Real.sin_sub_pi α
      rw [this] at hB
      nlinarith [sin_neg_of_reflex hα1 hα2]
    · exact absurd hs (sin_neg_of_pi_lt_of_lt_two_pi h1 (by linarith)).ne
  · exact heq.symm

/-- The side `sin α Re − cos α Im = 0`, `Im ≤ 0` of the reflex sector comes from `h < 0`. -/
theorem re_neg_of_polarFold_reflex {h : ℂ} (h0 : h ≠ 0)
    (hB : Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0)
    (hI : (polarFold α h).im ≤ 0) : h.im = 0 ∧ h.re < 0 := by
  have hα0 : 0 < α := by linarith [Real.pi_pos]
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hb0 := foldAngle_nonneg hα0.le h
  have hb1 := foldAngle_le hα0.le h
  rw [polarFold_im] at hI
  rw [polarFold_sector_re] at hB
  have hs : Real.sin (α - foldAngle α h) = 0 := by
    rcases mul_eq_zero.1 hB with h1 | h1
    · exact absurd h1 hn.ne'
    · exact h1
  refine re_neg_of_foldAngle_eq hα0 h0 ?_
  rcases hb1.lt_or_eq with hlt | heq
  · exfalso
    have hd : 0 < α - foldAngle α h := by linarith
    rcases lt_trichotomy (α - foldAngle α h) π with h1 | h1 | h1
    · exact absurd hs (Real.sin_pos_of_pos_of_lt_pi hd h1).ne'
    · have e : foldAngle α h = α - π := by linarith
      rw [e] at hI
      have := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < α - π) (by linarith : α - π < π)
      nlinarith
    · exact absurd hs (sin_neg_of_pi_lt_of_lt_two_pi h1 (by linarith)).ne
  · exact heq

/-- **The fold onto a reflex sector is onto**, from the closed upper half-plane. -/
theorem exists_polarFold_eq_reflex {v : ℂ}
    (hv : 0 ≤ v.im ∨ 0 ≤ Real.sin α * v.re - Real.cos α * v.im) :
    ∃ h : ℂ, polarFold α h = v ∧ 0 ≤ h.im := by
  have hα0 : 0 < α := by linarith [Real.pi_pos]
  by_cases h0 : v = 0
  · exact ⟨0, by rw [h0, polarFold_zero], le_rfl⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  -- an angle `γ ∈ [0, α]` of `v`
  obtain ⟨γ, hγ0, hγα, hvγ⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ γ ≤ α ∧
      v = (‖v‖ : ℂ) * Complex.exp ((γ : ℂ) * Complex.I) := by
    rcases le_or_gt 0 v.im with hi | hi
    · exact ⟨Real.arccos (v.re / ‖v‖), Real.arccos_nonneg _,
        (Real.arccos_le_pi _).trans hα1.le, eq_norm_mul_exp_arccos hi⟩
    · have hB : 0 ≤ Real.sin α * v.re - Real.cos α * v.im := by
        rcases hv with hv | hv
        · linarith
        · exact hv
      set a := Real.arccos (v.re / ‖v‖) with ha
      have hcv : (starRingEnd ℂ) v = (‖v‖ : ℂ) * Complex.exp ((a : ℂ) * Complex.I) := by
        have := eq_norm_mul_exp_arccos (v := (starRingEnd ℂ) v) (by
          rw [Complex.conj_im]; linarith)
        rw [Complex.norm_conj, Complex.conj_re] at this
        exact this
      have hva : v = (‖v‖ : ℂ) * Complex.exp (((2 * π - a : ℝ) : ℂ) * Complex.I) := by
        have e := congrArg (starRingEnd ℂ) hcv
        rw [Complex.conj_conj, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
          Complex.conj_ofReal, Complex.conj_I] at e
        refine e.trans ?_
        congr 1
        have : (((2 * π - a : ℝ) : ℂ) * Complex.I) =
            (a : ℂ) * -Complex.I + ((1 : ℤ) : ℂ) * (2 * π * Complex.I) := by push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have ha0 : 0 ≤ a := Real.arccos_nonneg _
      have haπ : a ≤ π := Real.arccos_le_pi _
      obtain ⟨hB', him⟩ := sector_of_eq_exp (α := α) hva
      have ha0' : 0 < a := by
        by_contra hle
        have : a = 0 := le_antisymm (not_lt.1 hle) ha0
        rw [this, sub_zero, Real.sin_two_pi, mul_zero] at him
        linarith
      refine ⟨2 * π - a, by linarith, ?_, hva⟩
      by_contra hlt
      rw [not_le] at hlt
      have : Real.sin (α - (2 * π - a)) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
      nlinarith
  obtain ⟨e1, e2⟩ := polarFold_norm_mul_exp hα0 ‖v‖ (norm_nonneg _) hγ0 hγα
  exact ⟨_, e1.trans hvγ.symm, e2⟩

/-- Inside the open reflex sector, the fold is onto from the open lower half-plane. -/
theorem exists_polarFold_eq_reflex_neg {v : ℂ}
    (hv : 0 < v.im ∨ 0 < Real.sin α * v.re - Real.cos α * v.im) :
    ∃ h : ℂ, polarFold α h = v ∧ h.im < 0 := by
  obtain ⟨h, hv', hi⟩ := exists_polarFold_eq_reflex hα1 hα2
    (by rcases hv with hv | hv; exacts [Or.inl hv.le, Or.inr hv.le])
  refine ⟨(starRingEnd ℂ) h, by rw [polarFold_conj, hv'], ?_⟩
  rw [Complex.conj_im, neg_lt_zero]
  rcases hi.lt_or_eq with hi | hi
  · exact hi
  · exfalso
    rcases le_total 0 h.re with hr | hr
    · obtain ⟨e1, e2⟩ := polarFold_reflex_of_re_nonneg hα1 hα2 hi.symm hr
      rw [hv'] at e1 e2
      rcases hv with hv | hv <;> linarith
    · obtain ⟨e1, e2⟩ := polarFold_reflex_of_re_nonpos hα1 hα2 hi.symm hr
      rw [hv'] at e1 e2
      rcases hv with hv | hv <;> linarith

end PolarFoldReflex

/-- On the real axis, `h ≥ 0`, the fold is real (any `α`). -/
theorem polarFold_im_of_re_nonneg {α : ℝ} {h : ℂ} (him : h.im = 0) (hre : 0 ≤ h.re) :
    (polarFold α h).im = 0 := by
  by_cases h0 : h = 0
  · subst h0; simp
  rw [polarFold_im, foldAngle_of_re_nonneg h0 him hre, Real.sin_zero, mul_zero]

/-- On the real axis, `h ≤ 0`, the fold is on the ray of angle `α` (any `α`). -/
theorem polarFold_sector_of_re_nonpos {α : ℝ} {h : ℂ} (him : h.im = 0) (hre : h.re ≤ 0) :
    Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0 := by
  by_cases h0 : h = 0
  · subst h0; simp
  rw [polarFold_sector_re, foldAngle_of_re_nonpos h0 him hre, sub_self, Real.sin_zero, mul_zero]

end ReflexFold

section Frames

/-! ### Two linear facts -/

/-- **A vector orthogonal to `a` and `b` is a multiple of `a × b`**:
`|a × b|² x = ⟨a × b, x⟩ (a × b)`. -/
theorem cross_dot_self_smul_eq {a b x : Fin 3 → ℝ} (ha : a ⬝ᵥ x = 0) (hb : b ⬝ᵥ x = 0) :
    ((a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)) • x = ((a ⨯₃ b) ⬝ᵥ x) • (a ⨯₃ b) := by
  simp only [dotProduct, Fin.sum_univ_three] at ha hb
  ext j; fin_cases j
  · simp [cross_apply, dotProduct, Fin.sum_univ_three]
    linear_combination (a 0 * b 1 ^ 2 + a 0 * b 2 ^ 2 - a 1 * b 0 * b 1 - a 2 * b 0 * b 2) * ha +
      (-a 0 * a 1 * b 1 - a 0 * a 2 * b 2 + a 1 ^ 2 * b 0 + a 2 ^ 2 * b 0) * hb
  · simp [cross_apply, dotProduct, Fin.sum_univ_three]
    linear_combination (-a 0 * b 0 * b 1 + a 1 * b 0 ^ 2 + a 1 * b 2 ^ 2 - a 2 * b 1 * b 2) * ha +
      (a 0 ^ 2 * b 1 - a 0 * a 1 * b 0 - a 1 * a 2 * b 2 + a 2 ^ 2 * b 1) * hb
  · simp [cross_apply, dotProduct, Fin.sum_univ_three]
    linear_combination (-a 0 * b 0 * b 2 - a 1 * b 1 * b 2 + a 2 * b 0 ^ 2 + a 2 * b 1 ^ 2) * ha +
      (a 0 ^ 2 * b 2 - a 0 * a 2 * b 0 + a 1 ^ 2 * b 2 - a 1 * a 2 * b 1) * hb

/-- **Two great circles meet only at `± a × b`**: a point `x ⊥ a, b` with `⟨c, x⟩ ≤ 0 ≤ ⟨d, x⟩`
where `c` and `d` are both positive on `a × b` is `0`. -/
theorem eq_zero_of_dot_cross {a b c d x : Fin 3 → ℝ} (ha : a ⬝ᵥ x = 0) (hb : b ⬝ᵥ x = 0)
    (hc : 0 < c ⬝ᵥ (a ⨯₃ b)) (hd : 0 < d ⬝ᵥ (a ⨯₃ b)) (hcx : c ⬝ᵥ x ≤ 0) (hdx : 0 ≤ d ⬝ᵥ x) :
    x = 0 := by
  have key := cross_dot_self_smul_eq ha hb
  set N := (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)
  set μ := (a ⨯₃ b) ⬝ᵥ x
  have hN : 0 < N := by
    have h0 : a ⨯₃ b ≠ 0 := fun e => by rw [e, dotProduct_zero] at hc; exact lt_irrefl _ hc
    have : 0 ≤ N := by
      simp only [N, dotProduct, Fin.sum_univ_three]
      exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso; apply h0
      have hs : (a ⨯₃ b) 0 ^ 2 + (a ⨯₃ b) 1 ^ 2 + (a ⨯₃ b) 2 ^ 2 = 0 := by
        rw [h]; simp only [N, dotProduct, Fin.sum_univ_three]; ring
      ext j; fin_cases j <;> simp <;> nlinarith [sq_nonneg ((a ⨯₃ b) 0),
        sq_nonneg ((a ⨯₃ b) 1), sq_nonneg ((a ⨯₃ b) 2)]
  have hx : x = (μ / N) • (a ⨯₃ b) := by
    rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
  have h1 : c ⬝ᵥ x = μ / N * (c ⬝ᵥ (a ⨯₃ b)) := by rw [hx, dotProduct_smul, smul_eq_mul]
  have h2 : d ⬝ᵥ x = μ / N * (d ⬝ᵥ (a ⨯₃ b)) := by rw [hx, dotProduct_smul, smul_eq_mul]
  have hμ : μ / N = 0 := by
    rw [h1] at hcx; rw [h2] at hdx
    have e1 : μ / N ≤ 0 := by
      by_contra h; rw [not_le] at h; nlinarith
    have e2 : 0 ≤ μ / N := by
      by_contra h; rw [not_le] at h; nlinarith
    linarith
  rw [hx, hμ, zero_smul]

/-! ### Frames at the vertices of a polygon, convex or not -/

/-- **The frames at the vertices of a spherical polygon, convex or not**: angles
`α_i ∈ ]0, 2π[ ∖ {π}` and unit normals `n_k` of the sides (indexed by the same type), the
vertex `v_i` on the sides `e_{a i}` (read along the meridian `ψ = 0` of the chart at `v_i`) and
`e_{b i}` (along `ψ = α_i`), with `⟨n_{b i}, n_{a i}⟩ = −cos α_i`. For `α_i < π` this is the
frame of `GX.SphPolygon`; `α_i > π` is a reflex vertex. -/
structure StarFrames (ι : Type) where
  /-- The angles. -/
  α : ι → ℝ
  /-- The unit normals of the sides. -/
  n : ι → Fin 3 → ℝ
  /-- The side read along `ψ = 0` at a vertex. -/
  a : ι → ι
  /-- The side read along `ψ = α_i` at a vertex. -/
  b : ι → ι
  α_pos : ∀ i, 0 < α i
  α_lt : ∀ i, α i < 2 * π
  α_ne : ∀ i, α i ≠ π
  unit : ∀ k, n k ⬝ᵥ n k = 1
  gram : ∀ i, n (b i) ⬝ᵥ n (a i) = -Real.cos (α i)

namespace StarFrames

variable {ι : Type} (t : StarFrames ι)

theorem sin_ne (i : ι) : Real.sin (t.α i) ≠ 0 := by
  intro h
  rcases lt_or_gt_of_ne (t.α_ne i) with h1 | h1
  · exact (Real.sin_pos_of_pos_of_lt_pi (t.α_pos i) h1).ne' h
  · exact (sin_neg_of_pi_lt_of_lt_two_pi h1 (t.α_lt i)).ne h

/-- The second vector of the frame at `v_i`: the unit tangent of `e_{a i}` at `v_i`. -/
def m (i : ι) : Fin 3 → ℝ :=
  (Real.sin (t.α i))⁻¹ • (t.n (t.b i) + Real.cos (t.α i) • t.n (t.a i))

theorem m_dot_n (i : ι) : t.m i ⬝ᵥ t.n (t.a i) = 0 := by
  rw [m, smul_dotProduct, add_dotProduct, smul_dotProduct, t.gram, t.unit]
  simp

theorem m_dot_m (i : ι) : t.m i ⬝ᵥ t.m i = 1 := by
  have hs := t.sin_ne i
  have h1 := t.gram i
  have h2 := t.unit (t.b i)
  have h3 := t.unit (t.a i)
  rw [m]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm (t.n (t.a i)) (t.n (t.b i)), h1, h2, h3]
  have hsc := Real.sin_sq_add_cos_sq (t.α i)
  field_simp
  nlinarith

theorem n_b_eq (i : ι) :
    t.n (t.b i) = Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (t.a i) := by
  rw [m, smul_smul, mul_inv_cancel₀ (t.sin_ne i), one_smul]
  abel

/-- **The rotation `R_i` putting `v_i` at the north pole**, `e_{a i}` along `ψ = 0`. -/
def R (i : ι) : SO3 := frameSO3 (t.m i) (t.n (t.a i)) (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

/-- Its matrix. -/
def A (i : ι) : Matrix (Fin 3) (Fin 3) ℝ := frameMat (t.m i) (t.n (t.a i))

theorem A_mulVec (i : ι) (x : Fin 3 → ℝ) :
    t.A i *ᵥ x = ![(t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ x, t.m i ⬝ᵥ x, t.n (t.a i) ⬝ᵥ x] :=
  frameMat_mulVec _ _ _

theorem A_mulVec_n_a (i : ι) : t.A i *ᵥ t.n (t.a i) = ![0, 0, 1] := by
  rw [A_mulVec, t.unit, t.m_dot_n, dotProduct_comm, dot_cross_self]

theorem A_mulVec_n_b (i : ι) :
    t.A i *ᵥ t.n (t.b i) = ![0, Real.sin (t.α i), -Real.cos (t.α i)] := by
  rw [t.n_b_eq i, A_mulVec]
  have h1 : (t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ (Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (t.a i))
      = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm, dot_self_cross,
      dotProduct_comm, dot_cross_self]
    simp
  rw [h1]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, t.m_dot_m, t.m_dot_n, t.unit,
    dotProduct_comm (t.n (t.a i)) (t.m i)]
  ext j; fin_cases j <;> simp

/-- The first coordinate of `R_i c`, the pairing of `c` with `v_i`. -/
theorem A_mulVec_zero (i : ι) (c : Fin 3 → ℝ) :
    (t.A i *ᵥ c) 0 = (Real.sin (t.α i))⁻¹ * (c ⬝ᵥ t.n (t.b i) ⨯₃ t.n (t.a i)) := by
  rw [A_mulVec]
  show (t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ c = _
  rw [dotProduct_comm, m, LinearMap.map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply,
    LinearMap.map_smul, LinearMap.smul_apply, cross_self, smul_zero, add_zero, dotProduct_smul,
    smul_eq_mul]

theorem A_transpose_mul (i : ι) : (t.A i)ᵀ * t.A i = 1 :=
  frameMat_transpose_mul (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

theorem vec_R_smul (i : ι) (y : Sph2) : vec (t.R i • y) = t.A i *ᵥ vec y :=
  vec_frameSO3_smul _ _ _ y ▸ (t.A_mulVec i (vec y)).symm ▸ rfl

theorem dot_vec_R_inv_smul (i : ι) (c : Fin 3 → ℝ) (y : Sph2) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • y) = (t.A i *ᵥ c) ⬝ᵥ vec y :=
  dot_vec_frameSO3_inv_smul _ _ _ c y

theorem dot_vec_R_inv_stereoInv (i : ι) (c : Fin 3 → ℝ) (v : ℂ) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • stereoInv v) = gfun (t.A i *ᵥ c) v / (1 + ‖v‖ ^ 2) := by
  rw [dot_vec_R_inv_smul, dot_vec_stereoInv]

/-- The frame matrix preserves the pairing. -/
theorem A_dot_A (i : ι) (u v : Fin 3 → ℝ) : (t.A i *ᵥ u) ⬝ᵥ (t.A i *ᵥ v) = u ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, t.A_transpose_mul, one_mulVec]

/-- The reflection `σ_k` of `𝕊²` in the great circle of the side `e_k`. -/
def σ (k : ι) : Sph2 → Sph2 := reflSph (t.n k) (t.unit k)

theorem vec_R_σ_R_inv (i k : ι) (y : Sph2) :
    vec (t.R i • t.σ k ((t.R i)⁻¹ • y)) =
      vec y - (2 * ((t.A i *ᵥ t.n k) ⬝ᵥ vec y)) • (t.A i *ᵥ t.n k) := by
  rw [t.vec_R_smul, σ, vec_reflSph, mulVec_sub, mulVec_smul, t.dot_vec_R_inv_smul]
  congr 1
  have h := t.vec_R_smul i ((t.R i)⁻¹ • y)
  rw [smul_inv_smul] at h
  exact h.symm

/-- **The reflection in `e_{a i}` is `ρ` at `v_i`**: `R_i σ_{a i} R_i⁻¹ = ρ`. -/
theorem R_σ_a (i : ι) (y : Sph2) :
    t.R i • t.σ (t.a i) ((t.R i)⁻¹ • y) = conjSph y := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_a, vec_conjSph]
  ext j; fin_cases j <;> simp [dotProduct, Fin.sum_univ_three]; ring

/-- **The reflection in `e_{b i}` is the rotation of angle `2α_i` after `ρ` at `v_i`.** -/
theorem R_σ_b_stereoInv (i : ι) (v : ℂ) :
    t.R i • t.σ (t.b i) ((t.R i)⁻¹ • stereoInv v) =
      stereoInv (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v) := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_b, vec_stereoInv, vec_stereoInv]
  have hn : ‖Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v‖ = ‖v‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]
  rw [hn]
  have hre : (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v).re =
      Real.cos (2 * t.α i) * v.re + Real.sin (2 * t.α i) * v.im := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have him : (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v).im =
      Real.sin (2 * t.α i) * v.re - Real.cos (2 * t.α i) * v.im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre, him, Real.cos_two_mul, Real.sin_two_mul]
  have hsc := Real.sin_sq_add_cos_sq (t.α i)
  have hs2 : Real.sin (t.α i) ^ 2 = 1 - Real.cos (t.α i) ^ 2 := by linarith
  have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  ext j; fin_cases j
  · simp
  · simp only [dotProduct, Fin.sum_univ_three]
    simp
    field_simp
    linear_combination (-2 * v.re) * hsc
  · simp only [dotProduct, Fin.sum_univ_three]
    simp
    field_simp
    ring

/-- **The point with polar coordinates `h` at `v_i`**: `h = r e^{iφ}` goes to the point at
stereographic radius `r` from `v_i` in the direction of angle `α_i |φ| / π` from `e_{a i}`. -/
def xv (i : ι) (h : ℂ) : Sph2 := (t.R i)⁻¹ • stereoInv (polarFold (t.α i) h)

theorem continuous_xv (i : ι) : Continuous (t.xv i) :=
  (continuous_const_smul _).comp (continuous_stereoInv.comp continuous_polarFold)

theorem dot_xv (i k : ι) (h : ℂ) :
    t.n k ⬝ᵥ vec (t.xv i h) = gfun (t.A i *ᵥ t.n k) (polarFold (t.α i) h) / (1 + ‖h‖ ^ 2) := by
  rw [xv, t.dot_vec_R_inv_stereoInv, norm_polarFold]

theorem dot_xv' (i : ι) (c : Fin 3 → ℝ) (h : ℂ) :
    c ⬝ᵥ vec (t.xv i h) = gfun (t.A i *ᵥ c) (polarFold (t.α i) h) / (1 + ‖h‖ ^ 2) := by
  rw [xv, t.dot_vec_R_inv_stereoInv, norm_polarFold]

theorem dot_xv_a (i : ι) (h : ℂ) :
    t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 2 * (polarFold (t.α i) h).im / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_a]; simp [gfun]

theorem dot_xv_b (i : ι) (h : ℂ) :
    t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 2 * (Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im) / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_b]; simp [gfun]; ring

/-- **The vertex `v_i`.** -/
def vertex (i : ι) : Sph2 := t.xv i 0

theorem vertex_eq (i : ι) : t.vertex i = (t.R i)⁻¹ • northPole := by
  rw [vertex, xv, polarFold_zero, stereoInv_zero]

theorem dot_vertex (i : ι) (c : Fin 3 → ℝ) : c ⬝ᵥ vec (t.vertex i) = (t.A i *ᵥ c) 0 := by
  rw [vertex, dot_xv', polarFold_zero]; simp [gfun]

theorem dot_vertex_a (i : ι) : t.n (t.a i) ⬝ᵥ vec (t.vertex i) = 0 := by
  rw [dot_vertex, t.A_mulVec_n_a]; rfl

theorem dot_vertex_b (i : ι) : t.n (t.b i) ⬝ᵥ vec (t.vertex i) = 0 := by
  rw [dot_vertex, t.A_mulVec_n_b]; rfl

/-- The pairing of `c` with `v_i`, through the triple product. -/
theorem dot_vertex_eq (i : ι) (c : Fin 3 → ℝ) :
    c ⬝ᵥ vec (t.vertex i) = (Real.sin (t.α i))⁻¹ * (c ⬝ᵥ t.n (t.b i) ⨯₃ t.n (t.a i)) := by
  rw [dot_vertex, A_mulVec_zero]

/-- A point on the two sides through `v_i` is `±v_i`, read on any pairing. -/
theorem dot_eq_of_dot_a_b (i : ι) {x : Sph2} (ha : t.n (t.a i) ⬝ᵥ vec x = 0)
    (hb : t.n (t.b i) ⬝ᵥ vec x = 0) (c : Fin 3 → ℝ) :
    c ⬝ᵥ vec x = (t.A i *ᵥ vec x) 0 * (c ⬝ᵥ vec (t.vertex i)) ∧ (t.A i *ᵥ vec x) 0 ^ 2 = 1 := by
  have hm : t.m i ⬝ᵥ vec x = 0 := by
    rw [t.n_b_eq i, sub_dotProduct, smul_dotProduct, smul_dotProduct, ha, smul_eq_mul,
      smul_eq_mul, mul_zero, sub_zero] at hb
    exact (mul_eq_zero.1 hb).resolve_left (t.sin_ne i)
  have hA : t.A i *ᵥ vec x = ![(t.A i *ᵥ vec x) 0, 0, 0] := by
    have := t.A_mulVec i (vec x)
    rw [hm, ha] at this
    rw [this]; rfl
  constructor
  · rw [dot_vertex, ← t.A_dot_A i c (vec x), hA]
    simp [dotProduct, Fin.sum_univ_three]; ring
  · have h1 := t.A_dot_A i (vec x) (vec x)
    rw [vec_dot_self, hA] at h1
    simpa [dotProduct, Fin.sum_univ_three, sq] using h1

/-- A point positive on some `c` with `⟨c, v_i⟩ > 0` is not the antipode `−v_i`. -/
theorem fst_ne_of_dot_nonneg (i : ι) {c : Fin 3 → ℝ} (hc : 0 < (t.A i *ᵥ c) 0) {x : Sph2}
    (hx : 0 ≤ c ⬝ᵥ vec x) : ((t.R i • x : Sph2) : Euc3).fst ≠ -1 := by
  intro h
  have hv := vec_dot_self (t.R i • x)
  have hvec : vec (t.R i • x) = ![-1, 0, 0] := by
    rw [vec_apply] at hv ⊢
    simp only [dotProduct, Fin.sum_univ_three, h] at hv
    simp at hv
    have h1 : ((t.R i • x : Sph2) : Euc3).snd.re = 0 := by nlinarith
    have h2 : ((t.R i • x : Sph2) : Euc3).snd.im = 0 := by nlinarith
    rw [h, h1, h2]
  have e : x = (t.R i)⁻¹ • (t.R i • x) := (inv_smul_smul _ _).symm
  rw [e, t.dot_vec_R_inv_smul, hvec] at hx
  simp [dotProduct, Fin.sum_univ_three] at hx
  linarith

/-- The stereographic coordinate of `x` at `v_i`, and the pairings read through it. -/
theorem eq_xv_stereo (i : ι) {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1) :
    x = (t.R i)⁻¹ • stereoInv (stereoFun (t.R i • x)) := by
  rw [stereoInv_stereoFun _ hS, inv_smul_smul]

theorem dot_a_stereo (i : ι) {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1) :
    t.n (t.a i) ⬝ᵥ vec x = 2 * (stereoFun (t.R i • x)).im / (1 + ‖stereoFun (t.R i • x)‖ ^ 2) := by
  conv_lhs => rw [t.eq_xv_stereo i hS]
  rw [t.dot_vec_R_inv_stereoInv, t.A_mulVec_n_a]; simp [gfun]

theorem dot_b_stereo (i : ι) {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1) :
    t.n (t.b i) ⬝ᵥ vec x = 2 * (Real.sin (t.α i) * (stereoFun (t.R i • x)).re -
      Real.cos (t.α i) * (stereoFun (t.R i • x)).im) / (1 + ‖stereoFun (t.R i • x)‖ ^ 2) := by
  conv_lhs => rw [t.eq_xv_stereo i hS]
  rw [t.dot_vec_R_inv_stereoInv, t.A_mulVec_n_b]; simp [gfun]; ring

/-- **The points of a half-sphere `{⟨c, ·⟩ ≥ 0}` containing `v_i` in its interior are bounded in
the polar coordinates at `v_i`.** -/
theorem isBounded_xv (i : ι) {c : Fin 3 → ℝ} (hcu : c ⬝ᵥ c = 1) (hc : 0 < (t.A i *ᵥ c) 0) :
    Bornology.IsBounded {h | 0 ≤ c ⬝ᵥ vec (t.xv i h)} := by
  set c' := t.A i *ᵥ c
  have h1 : c' ⬝ᵥ c' = 1 := by rw [t.A_dot_A, hcu]
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / c' 0)).subset fun h hh => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh' : 0 ≤ gfun c' (polarFold (t.α i) h) := by
    have : 0 ≤ c ⬝ᵥ vec (t.xv i h) := hh
    rw [dot_xv'] at this
    have hD : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
    rwa [le_div_iff₀ hD, zero_mul] at this
  rw [← norm_polarFold (α := t.α i) h]
  exact SphPolygon.norm_le_of_gfun_nonneg h1 hc hh'

/-- **The polar coordinates at `v_i` of an open half-sphere containing `v_i` are star-shaped
about `0`.** -/
theorem starConvex_xv (i : ι) {c : Fin 3 → ℝ} (hc : 0 < (t.A i *ᵥ c) 0) :
    StarConvex ℝ 0 {h | 0 < c ⬝ᵥ vec (t.xv i h)} := by
  intro h hh a b ha hb hab
  rw [smul_zero, zero_add]
  have hh' : 0 < c ⬝ᵥ vec (t.xv i h) := hh
  show 0 < c ⬝ᵥ vec (t.xv i (b • h))
  rw [dot_xv'] at hh' ⊢
  have hD : (0 : ℝ) < 1 + ‖b • h‖ ^ 2 := by positivity
  have hD' : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  apply div_pos _ hD
  have hg := (div_pos_iff_of_pos_right hD').1 hh'
  rw [Complex.real_smul, polarFold_ofReal_mul hb]
  set c' := t.A i *ᵥ c
  set v := polarFold (t.α i) h
  have key : gfun c' ((b : ℂ) * v) =
      b * gfun c' v + c' 0 * (1 - b) + c' 0 * b * (1 - b) * ‖v‖ ^ 2 := by
    simp only [gfun, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    ring
  rw [key]
  have hb1 : b ≤ 1 := by linarith
  rcases hb.lt_or_eq with hb0 | hb0
  · have := mul_pos hb0 hg
    have := mul_nonneg (mul_nonneg hc.le hb0.le) (mul_nonneg (sub_nonneg.2 hb1) (sq_nonneg ‖v‖))
    nlinarith [mul_nonneg hc.le (sub_nonneg.2 hb1)]
  · subst hb0; simp; exact hc

/-! #### Convex vertices (`α_i < π`) -/

section Convex

variable {i : ι} (hα : t.α i < π)
include hα

theorem xv_sector (h : ℂ) :
    0 ≤ t.n (t.a i) ⬝ᵥ vec (t.xv i h) ∧ 0 ≤ t.n (t.b i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_a, dot_xv_b]
  have := polarFold_mem_sector (t.α_pos i) hα h
  exact ⟨by have := this.1; positivity, by have := this.2; positivity⟩

theorem xv_sector_strict {h : ℂ} (hh : h.im ≠ 0) :
    0 < t.n (t.a i) ⬝ᵥ vec (t.xv i h) ∧ 0 < t.n (t.b i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_a, dot_xv_b]
  have := polarFold_mem_sector_strict (t.α_pos i) hα hh
  exact ⟨by have := this.1; positivity, by have := this.2; positivity⟩

theorem xv_side_a {h : ℂ} (h0 : h ≠ 0) (hk : t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0) :
    h.im = 0 ∧ 0 < h.re := by
  rw [dot_xv_a, div_eq_zero_iff, mul_eq_zero] at hk
  have hF : (polarFold (t.α i) h).im = 0 := by
    rcases hk with (hk | hk) | hk
    · norm_num at hk
    · exact hk
    · nlinarith [sq_nonneg ‖h‖]
  exact SphTriangle.re_pos_of_polarFold_im (t.α_pos i) hα h0 hF

theorem xv_side_b {h : ℂ} (h0 : h ≠ 0) (hk : t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0) :
    h.im = 0 ∧ h.re < 0 := by
  rw [dot_xv_b, div_eq_zero_iff, mul_eq_zero] at hk
  have hF : Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im = 0 := by
    rcases hk with (hk | hk) | hk
    · norm_num at hk
    · exact hk
    · nlinarith [sq_nonneg ‖h‖]
  exact SphTriangle.re_neg_of_polarFold_sector (t.α_pos i) hα h0 hF

theorem exists_xv_eq {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1)
    (ha : 0 ≤ t.n (t.a i) ⬝ᵥ vec x) (hb : 0 ≤ t.n (t.b i) ⬝ᵥ vec x) :
    ∃ h, t.xv i h = x ∧ 0 ≤ h.im := by
  set z := stereoFun (t.R i • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [t.dot_a_stereo i hS] at ha
  rw [t.dot_b_stereo i hS] at hb
  have h1 : 0 ≤ z.im := by
    have := (div_nonneg_iff.1 ha); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
  have h2 : 0 ≤ Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
    have := (div_nonneg_iff.1 hb); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
  obtain ⟨h, hF, hi⟩ := exists_polarFold_eq (t.α_pos i) hα h1 h2
  exact ⟨h, by rw [xv, hF]; exact (t.eq_xv_stereo i hS).symm, hi⟩

theorem exists_xv_eq_neg {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1)
    (ha : 0 < t.n (t.a i) ⬝ᵥ vec x) (hb : 0 < t.n (t.b i) ⬝ᵥ vec x) :
    ∃ h, t.xv i h = x ∧ h.im < 0 := by
  set z := stereoFun (t.R i • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [t.dot_a_stereo i hS] at ha
  rw [t.dot_b_stereo i hS] at hb
  have h1 : 0 < z.im := by
    have := (div_pos_iff_of_pos_right hD).1 ha; linarith
  have h2 : 0 < Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
    have := (div_pos_iff_of_pos_right hD).1 hb; linarith
  obtain ⟨h, hF, hi⟩ := exists_polarFold_eq_neg (t.α_pos i) hα h1 h2
  exact ⟨h, by rw [xv, hF]; exact (t.eq_xv_stereo i hS).symm, hi⟩

end Convex

theorem xv_real_a (i : ι) {h : ℂ} (him : h.im = 0) (hre : 0 ≤ h.re) :
    t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0 := by
  rw [dot_xv_a, polarFold_im_of_re_nonneg him hre]; simp

theorem xv_real_b (i : ι) {h : ℂ} (him : h.im = 0) (hre : h.re ≤ 0) :
    t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0 := by
  rw [dot_xv_b, polarFold_sector_of_re_nonpos him hre]; simp

/-! #### Reflex vertices (`α_i > π`) -/

section Reflex

variable {i : ι} (hα : π < t.α i)
include hα

theorem xv_sector_reflex (h : ℂ) :
    0 ≤ t.n (t.a i) ⬝ᵥ vec (t.xv i h) ∨ 0 ≤ t.n (t.b i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_a, dot_xv_b]
  rcases polarFold_mem_reflex hα (t.α_lt i) h with h1 | h1
  · left; positivity
  · right; positivity

theorem xv_sector_reflex_strict {h : ℂ} (hh : h.im ≠ 0) :
    0 < t.n (t.a i) ⬝ᵥ vec (t.xv i h) ∨ 0 < t.n (t.b i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_a, dot_xv_b]
  rcases polarFold_mem_reflex_strict hα (t.α_lt i) hh with h1 | h1
  · left; positivity
  · right; positivity

theorem xv_real_a_reflex {h : ℂ} (him : h.im = 0) (hre : 0 ≤ h.re) :
    t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0 ∧ t.n (t.b i) ⬝ᵥ vec (t.xv i h) ≤ 0 := by
  rw [dot_xv_a, dot_xv_b]
  obtain ⟨e1, e2⟩ := polarFold_reflex_of_re_nonneg hα (t.α_lt i) him hre
  refine ⟨by rw [e1]; simp, div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)⟩

theorem xv_real_b_reflex {h : ℂ} (him : h.im = 0) (hre : h.re ≤ 0) :
    t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0 ∧ t.n (t.a i) ⬝ᵥ vec (t.xv i h) ≤ 0 := by
  rw [dot_xv_a, dot_xv_b]
  obtain ⟨e1, e2⟩ := polarFold_reflex_of_re_nonpos hα (t.α_lt i) him hre
  refine ⟨by rw [e1]; simp, div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)⟩

theorem xv_side_a_reflex {h : ℂ} (h0 : h ≠ 0) (hk : t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0)
    (hb : t.n (t.b i) ⬝ᵥ vec (t.xv i h) ≤ 0) : h.im = 0 ∧ 0 < h.re := by
  have hD : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  rw [dot_xv_a, div_eq_zero_iff, mul_eq_zero] at hk
  have hF : (polarFold (t.α i) h).im = 0 := by
    rcases hk with (hk | hk) | hk
    · norm_num at hk
    · exact hk
    · linarith
  rw [dot_xv_b, div_nonpos_iff] at hb
  have hB : Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im ≤ 0 := by
    rcases hb with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · linarith
  exact re_pos_of_polarFold_reflex hα (t.α_lt i) h0 hF hB

theorem xv_side_b_reflex {h : ℂ} (h0 : h ≠ 0) (hk : t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0)
    (ha : t.n (t.a i) ⬝ᵥ vec (t.xv i h) ≤ 0) : h.im = 0 ∧ h.re < 0 := by
  have hD : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  rw [dot_xv_b, div_eq_zero_iff, mul_eq_zero] at hk
  have hF : Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im = 0 := by
    rcases hk with (hk | hk) | hk
    · norm_num at hk
    · exact hk
    · linarith
  rw [dot_xv_a, div_nonpos_iff] at ha
  have hI : (polarFold (t.α i) h).im ≤ 0 := by
    rcases ha with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · linarith
  exact re_neg_of_polarFold_reflex hα (t.α_lt i) h0 hF hI

theorem exists_xv_eq_reflex {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1)
    (hx : 0 ≤ t.n (t.a i) ⬝ᵥ vec x ∨ 0 ≤ t.n (t.b i) ⬝ᵥ vec x) :
    ∃ h, t.xv i h = x ∧ 0 ≤ h.im := by
  set z := stereoFun (t.R i • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [t.dot_a_stereo i hS, t.dot_b_stereo i hS] at hx
  have hz : 0 ≤ z.im ∨ 0 ≤ Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
    rcases hx with hx | hx
    · left; have := (div_nonneg_iff.1 hx); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
    · right; have := (div_nonneg_iff.1 hx); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
  obtain ⟨h, hF, hi⟩ := exists_polarFold_eq_reflex hα (t.α_lt i) hz
  exact ⟨h, by rw [xv, hF]; exact (t.eq_xv_stereo i hS).symm, hi⟩

theorem exists_xv_eq_reflex_neg {x : Sph2} (hS : ((t.R i • x : Sph2) : Euc3).fst ≠ -1)
    (hx : 0 < t.n (t.a i) ⬝ᵥ vec x ∨ 0 < t.n (t.b i) ⬝ᵥ vec x) :
    ∃ h, t.xv i h = x ∧ h.im < 0 := by
  set z := stereoFun (t.R i • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [t.dot_a_stereo i hS, t.dot_b_stereo i hS] at hx
  have hz : 0 < z.im ∨ 0 < Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
    rcases hx with hx | hx
    · left; have := (div_pos_iff_of_pos_right hD).1 hx; linarith
    · right; have := (div_pos_iff_of_pos_right hD).1 hx; linarith
  obtain ⟨h, hF, hi⟩ := exists_polarFold_eq_reflex_neg hα (t.α_lt i) hz
  exact ⟨h, by rw [xv, hF]; exact (t.eq_xv_stereo i hS).symm, hi⟩

end Reflex

end StarFrames

end Frames

section GaugeUnion

open Metric Bornology

open scoped Pointwise

/-! ### A union of two convex bodies with a common interior point is a disc -/

section GaugeUnion

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The gauge of a union is the minimum of the gauges.** -/
theorem gauge_union_eq_min {A B : Set E} (hA : Absorbent ℝ A) (hB : Absorbent ℝ B) (x : E) :
    gauge (A ∪ B) x = min (gauge A x) (gauge B x) := by
  rw [gauge_def, gauge_def, gauge_def]
  have : {r ∈ Ioi (0 : ℝ) | x ∈ r • (A ∪ B)} =
      {r ∈ Ioi (0 : ℝ) | x ∈ r • A} ∪ {r ∈ Ioi (0 : ℝ) | x ∈ r • B} := by
    ext r; simp only [mem_setOf_eq, mem_union, smul_set_union]; tauto
  rw [this]
  exact csInf_union ⟨0, fun r hr => le_of_lt hr.1⟩ hA.gauge_set_nonempty
    ⟨0, fun r hr => le_of_lt hr.1⟩ hB.gauge_set_nonempty

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

/-- `gaugeRescale` is continuous as soon as the two gauges are (no convexity). -/
theorem continuous_gaugeRescale_of_continuous {s t : Set E} (hs₀ : s ∈ 𝓝 0) (ht₀ : t ∈ 𝓝 0)
    (htb : IsVonNBounded ℝ t) (hgs : Continuous (gauge s)) (hgt : Continuous (gauge t)) :
    Continuous (gaugeRescale s t) := by
  have hta : Absorbent ℝ t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((hgs.continuousAt).div (hgt.continuousAt)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

end GaugeUnion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A union of two closed bounded convex sets with a common interior point is a closed disc**:
a homeomorphism of the ambient space takes it onto the closed unit ball and its interior onto
the open unit ball (the gauge rescale, `gauge (A ∪ B) = min (gauge A) (gauge B)` being
continuous). -/
theorem exists_homeomorph_union_convex {A B : Set E} (hAc : Convex ℝ A) (hBc : Convex ℝ B)
    (hAcl : IsClosed A) (hBcl : IsClosed B) (hAb : IsBounded A) (hBb : IsBounded B) {x₀ : E}
    (hA0 : x₀ ∈ interior A) (hB0 : x₀ ∈ interior B) :
    ∃ e : E ≃ₜ E, e '' (A ∪ B) = closedBall 0 1 ∧ e '' interior (A ∪ B) = ball 0 1 := by
  set A' := -x₀ +ᵥ A
  set B' := -x₀ +ᵥ B
  have hA'c : Convex ℝ A' := hAc.vadd _
  have hB'c : Convex ℝ B' := hBc.vadd _
  have hA'0 : A' ∈ 𝓝 0 := by
    rw [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
    simpa using hA0
  have hB'0 : B' ∈ 𝓝 0 := by
    rw [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
    simpa using hB0
  have hA'cl : IsClosed A' := hAcl.vadd _
  have hB'cl : IsClosed B' := hBcl.vadd _
  have hA'b : IsBounded A' := hAb.vadd _
  have hB'b : IsBounded B' := hBb.vadd _
  set s := A' ∪ B'
  set t : Set E := ball 0 1
  have hs₀ : s ∈ 𝓝 0 := Filter.mem_of_superset hA'0 subset_union_left
  have ht₀ : t ∈ 𝓝 0 := ball_mem_nhds 0 one_pos
  have hsb : IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded _ (hA'b.union hB'b)
  have htb : IsVonNBounded ℝ t := NormedSpace.isVonNBounded_ball _ _ _
  have hsa : Absorbent ℝ s := absorbent_nhds_zero hs₀
  have hta : Absorbent ℝ t := absorbent_nhds_zero ht₀
  have hgs : gauge s = fun x => min (gauge A' x) (gauge B' x) := funext fun x =>
    gauge_union_eq_min (absorbent_nhds_zero hA'0) (absorbent_nhds_zero hB'0) x
  have hgsc : Continuous (gauge s) := by
    rw [hgs]; exact (continuous_gauge hA'c hA'0).min (continuous_gauge hB'c hB'0)
  have hgtc : Continuous (gauge t) := continuous_gauge (convex_ball 0 1) ht₀
  set e₀ : E ≃ₜ E :=
    { toEquiv := gaugeRescaleEquiv s t hsa hsb hta htb
      continuous_toFun := continuous_gaugeRescale_of_continuous hs₀ ht₀ htb hgsc hgtc
      continuous_invFun := continuous_gaugeRescale_of_continuous ht₀ hs₀ hsb hgtc hgsc }
  have he₀ : ∀ y, gauge s (e₀.symm y) = ‖y‖ := fun y => by
    show gauge s (gaugeRescale t s y) = ‖y‖
    rw [gauge_gaugeRescale t hsa hsb, gauge_unit_ball]
  have hmem : ∀ z, z ∈ s ↔ gauge s z ≤ 1 := fun z => by
    rw [hgs, min_le_iff, gauge_le_one_iff_mem_closure hA'c hA'0,
      gauge_le_one_iff_mem_closure hB'c hB'0, hA'cl.closure_eq, hB'cl.closure_eq]
    rfl
  have hint : ∀ z, z ∈ interior s ↔ gauge s z < 1 := fun z => by
    constructor
    · exact fun hz => interior_subset_gauge_lt_one s hz
    · intro hz
      rw [hgs, min_lt_iff, gauge_lt_one_iff_mem_interior hA'c hA'0,
        gauge_lt_one_iff_mem_interior hB'c hB'0] at hz
      rcases hz with hz | hz
      · exact interior_mono subset_union_left hz
      · exact interior_mono subset_union_right hz
  have h1 : e₀ '' s = closedBall 0 1 := by
    ext y
    rw [e₀.image_eq_preimage_symm, mem_preimage, hmem, he₀, mem_closedBall_zero_iff]
  have h2 : e₀ '' interior s = ball 0 1 := by
    ext y
    rw [e₀.image_eq_preimage_symm, mem_preimage, hint, he₀, mem_ball_zero_iff]
  have hcomp : ((Homeomorph.addLeft (-x₀)).trans e₀ : E → E) = e₀ ∘ (fun z => -x₀ + z) := rfl
  have himg : ∀ C : Set E, (fun z => -x₀ + z) '' C = -x₀ +ᵥ C := fun C => rfl
  refine ⟨(Homeomorph.addLeft (-x₀)).trans e₀, ?_, ?_⟩
  · rw [hcomp, image_comp, himg, vadd_set_union]
    exact h1
  · rw [hcomp, image_comp, himg, ← interior_vadd, vadd_set_union]
    exact h2

end GaugeUnion

section StarDouble

open SphTriangle (sheet sheet_sq homeoComplex_apex homeoComplex_mk_lift
  sphConeDev_lift qOf cplx_qOf qOf_snd isOpenMap_cplx_posEmb continuous_cplx_posEmb
  im_cplx_one_posEmb continuous_q_snd eventually_snd_mem sin_nonneg_of_mem sin_neg_of_mem
  sin_neg_of_mem' arg_div_mem_up arg_div_mem_down)

namespace StarFrames

variable {ι : Type} (t : StarFrames ι)

/-- The cone angle `θ_i = 2α_i` at `v_i`. -/
def θc (i : ι) : ConeAngle := ⟨2 * t.α i, by have := t.α_pos i; positivity⟩

theorem θc_ne (i : ι) : (t.θc i).1 ≠ 2 * π := by
  have := t.α_ne i
  show 2 * t.α i ≠ 2 * π
  intro h; exact this (by linarith)

theorem xv_cover (i : ι) (q : PolarHalfPlane) :
    t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) = (t.R i)⁻¹ • stereoInv ((q.1.1 : ℂ) *
      Complex.exp ((foldAngle (t.α i) (DInfty.cplx 1 (DInfty.posEmb q)) : ℂ) * Complex.I)) := by
  rw [StarFrames.xv, polarFold_cover]

/-- The upper sheet, read on the cover. -/
theorem dev_eq_up (i : ι) (q : PolarHalfPlane) (h1 : 0 ≤ q.1.2) (h2 : q.1.2 ≤ 1 / 2) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift,
    foldAngle_cover_up (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 3
  push_cast; simp [θc]

/-- The lower sheet, read on the cover. -/
theorem dev_eq_down (i : ι) (q : PolarHalfPlane) (h1 : -(1 / 2) ≤ q.1.2) (h2 : q.1.2 ≤ 0) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSph (t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift, conjSph_stereoInv,
    foldAngle_cover_down (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast; simp [θc]

/-- The lower sheet past the side `e_{b i}`, read on the cover. -/
theorem dev_eq_down_one (i : ι) (q : PolarHalfPlane) (h1 : 1 / 2 ≤ q.1.2) (h2 : q.1.2 ≤ 1) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.σ (t.b i) (t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, t.R_σ_b_stereoInv, sphConeDev_lift,
    foldAngle_cover_down (n := 1) q (by push_cast; linarith) (by push_cast; linarith)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← mul_assoc, mul_comm (Complex.exp _) (q.1.1 : ℂ), mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast; simp [θc]; ring

end StarFrames

/-! ### A polygon with charts at its vertices: the data of its double -/

/-- **A spherical polygon `P` with polar charts at its vertices**, convex or not: the data the
double needs. `P` is read in the stereographic chart at the vertex `v_o` as a closed disc
(`eK`); `inner` is its interior, `onSide k` its side `e_k` (`exists_side`: the frontier is the
union of the sides). At `v_i` the polar coordinates `x_i(h)` (`StarFrames.xv`) on
`{h : F i (x_i h)}` are the chart, `Fc i` its closure; the conditions are read off the sector at
`v_i`: `x_i(h) ∈ P` (`Fc_mem`), onto (`exists_up`, `exists_down`), a side through the chart is a
side through `v_i`, reached on the real axis (`side_eq`), the real axis is on the frontier, its
complement inside. -/
structure StarPolygon {ι : Type} (t : StarFrames ι) where
  /-- The polygon. -/
  P : Set Sph2
  /-- Its interior. -/
  inner : Sph2 → Prop
  /-- Its sides. -/
  onSide : ι → Sph2 → Prop
  /-- The domain of the chart at `v_i`. -/
  F : ι → Sph2 → Prop
  /-- Its closure. -/
  Fc : ι → Sph2 → Prop
  /-- The vertex where the polygon is read in the stereographic chart. -/
  o : ι
  /-- The homeomorphism of the plane taking the polygon onto the closed unit disc. -/
  eK : ℂ ≃ₜ ℂ
  fst_ne : ∀ x ∈ P, ((t.R o • x : Sph2) : Euc3).fst ≠ -1
  eK_image : eK '' {v | (t.R o)⁻¹ • stereoInv v ∈ P} = Metric.closedBall 0 1
  eK_interior : eK '' interior {v | (t.R o)⁻¹ • stereoInv v ∈ P} = Metric.ball 0 1
  inner_mem : ∀ x ∈ P, inner x →
    stereoFun (t.R o • x) ∈ interior {v | (t.R o)⁻¹ • stereoInv v ∈ P}
  exists_side : ∀ x ∈ P, ¬ inner x → ∃ k, onSide k x
  side_notMem : ∀ x ∈ P, ∀ k, onSide k x →
    stereoFun (t.R o • x) ∉ interior {v | (t.R o)⁻¹ • stereoInv v ∈ P}
  isOpen_F : ∀ i, IsOpen {x | F i x}
  isClosed_Fc : ∀ i, IsClosed {x | Fc i x}
  F_Fc : ∀ i x, F i x → Fc i x
  Fc_mem : ∀ i h, Fc i (t.xv i h) → t.xv i h ∈ P
  exists_up : ∀ i, ∀ x ∈ P, F i x → ∃ h, t.xv i h = x ∧ 0 ≤ h.im
  exists_down : ∀ i, ∀ x ∈ P, F i x → inner x → ∃ h, t.xv i h = x ∧ h.im < 0
  side_eq : ∀ i k h, h ≠ 0 → F i (t.xv i h) → onSide k (t.xv i h) →
    (k = t.a i ∧ h.im = 0 ∧ 0 < h.re) ∨ (k = t.b i ∧ h.im = 0 ∧ h.re < 0)
  not_inner_of_real : ∀ i h, h.im = 0 → Fc i (t.xv i h) → ¬ inner (t.xv i h)
  inner_of_im : ∀ i h, h.im ≠ 0 → F i (t.xv i h) → inner (t.xv i h)
  F_vertex : ∀ i, F i (t.vertex i)
  isBounded_Fc : ∀ i, Bornology.IsBounded {h | Fc i (t.xv i h)}
  starConvex_F : ∀ i, StarConvex ℝ 0 {h | F i (t.xv i h)}
  vertex_inj : Injective t.vertex
  cover : ∀ x ∈ P, ∃ i, F i x

namespace StarPolygon

variable {ι : Type} {t : StarFrames ι} (P : StarPolygon t)

/-! #### The model -/

/-- The polygon in the stereographic chart at `v_o`. -/
def K : Set ℂ := {v | (t.R P.o)⁻¹ • stereoInv v ∈ P.P}

/-- **The double of the polygon**, as a space: the round sphere. A point `(u, w)` lies over the
point `R_o⁻¹ stereoInv (e_K⁻¹ w)` of the polygon (`fold`), on the upper copy if `u ≥ 0`. -/
def Double {ι : Type} {t : StarFrames ι} (_P : StarPolygon t) : Type := Sph2

instance : TopologicalSpace P.Double := inferInstanceAs (TopologicalSpace Sph2)

instance : T2Space P.Double := inferInstanceAs (T2Space Sph2)

instance : LocallyConnectedSpace P.Double := inferInstanceAs (LocallyConnectedSpace Sph2)

instance : SecondCountableTopology P.Double := inferInstanceAs (SecondCountableTopology Sph2)

instance : ConnectedSpace P.Double := inferInstanceAs (ConnectedSpace Sph2)

/-- The underlying point of `𝕊²`. -/
def toSph2 (y : P.Double) : Sph2 := y

/-- A point of `𝕊²` as a point of the double. -/
def ofSph2 (y : Sph2) : P.Double := y

/-- The double is `𝕊²` as a space. -/
def homeoSph2 : P.Double ≃ₜ Sph2 := Homeomorph.refl Sph2

theorem continuous_toSph2 : Continuous P.toSph2 := continuous_id

theorem continuous_ofSph2 : Continuous P.ofSph2 := continuous_id

/-- The height of a point of the double. -/
def height (y : P.Double) : ℝ := ((P.toSph2 y : Sph2) : Euc3).fst

/-- The disc coordinate of a point of the double. -/
def disc (y : P.Double) : ℂ := ((P.toSph2 y : Sph2) : Euc3).snd

theorem height_sq_add (y : P.Double) : P.height y ^ 2 + ‖P.disc y‖ ^ 2 = 1 := by
  rw [height, disc, ← norm_polarSum_sq, norm_raySphere, one_pow]

theorem continuous_height : Continuous P.height :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.fst).comp continuous_subtype_val

theorem continuous_disc : Continuous P.disc :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.snd).comp continuous_subtype_val

/-- **The folding map of the double onto the polygon.** -/
def fold (y : P.Double) : Sph2 := (t.R P.o)⁻¹ • stereoInv (P.eK.symm (P.disc y))

theorem continuous_fold : Continuous P.fold :=
  (continuous_const_smul _).comp
    (continuous_stereoInv.comp (P.eK.symm.continuous.comp P.continuous_disc))

/-- The disc coordinate of a point of the sphere. -/
def wK (x : Sph2) : ℂ := P.eK (stereoFun (t.R P.o • x))

theorem eK_symm_disc_mem_K (y : P.Double) : P.eK.symm (P.disc y) ∈ P.K := by
  have h : P.disc y ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]
    have := P.height_sq_add y
    nlinarith [norm_nonneg (P.disc y), sq_nonneg (P.height y)]
  rw [← P.eK_image] at h
  obtain ⟨v, hv, hve⟩ := h
  rw [← hve, Homeomorph.symm_apply_apply]; exact hv

theorem fold_mem (y : P.Double) : P.fold y ∈ P.P := P.eK_symm_disc_mem_K y

theorem stereoInv_stereoFun_R {x : Sph2} (hx : x ∈ P.P) :
    stereoInv (stereoFun (t.R P.o • x)) = t.R P.o • x :=
  stereoInv_stereoFun _ (P.fst_ne x hx)

theorem stereoFun_mem_K {x : Sph2} (hx : x ∈ P.P) : stereoFun (t.R P.o • x) ∈ P.K := by
  show (t.R P.o)⁻¹ • stereoInv (stereoFun (t.R P.o • x)) ∈ P.P
  rw [P.stereoInv_stereoFun_R hx, inv_smul_smul]; exact hx

theorem wK_fold (y : P.Double) : P.wK (P.fold y) = P.disc y := by
  rw [wK, fold, smul_inv_smul, stereoFun_stereoInv, Homeomorph.apply_symm_apply]

theorem norm_wK_le {x : Sph2} (hx : x ∈ P.P) : ‖P.wK x‖ ≤ 1 := by
  have : P.wK x ∈ P.eK '' P.K := ⟨_, P.stereoFun_mem_K hx, rfl⟩
  rw [K, P.eK_image, mem_closedBall_zero_iff] at this
  exact this

theorem mem_interior_K_iff (v : ℂ) : v ∈ interior P.K ↔ ‖P.eK v‖ < 1 := by
  rw [← mem_ball_zero_iff, K, ← P.eK_interior, P.eK.injective.mem_set_image]

/-- **Interior points of the polygon have disc coordinate in the open disc.** -/
theorem norm_wK_lt {x : Sph2} (hx : x ∈ P.P) (hi : P.inner x) : ‖P.wK x‖ < 1 :=
  (P.mem_interior_K_iff _).1 (P.inner_mem x hx hi)

/-- **Points on a side have disc coordinate on the circle.** -/
theorem one_le_norm_wK {x : Sph2} (hx : x ∈ P.P) {k : ι} (hk : P.onSide k x) : 1 ≤ ‖P.wK x‖ := by
  by_contra hlt
  rw [not_le] at hlt
  exact P.side_notMem x hx k hk ((P.mem_interior_K_iff _).2 hlt)

theorem norm_wK_eq_one_iff {x : Sph2} (hx : x ∈ P.P) : ‖P.wK x‖ = 1 ↔ ¬ P.inner x := by
  constructor
  · intro h hi
    have := P.norm_wK_lt hx hi
    linarith
  · intro hi
    obtain ⟨k, hk⟩ := P.exists_side x hx hi
    exact le_antisymm (P.norm_wK_le hx) (P.one_le_norm_wK hx hk)

theorem inner_of_norm_wK_lt {x : Sph2} (hx : x ∈ P.P) (h : ‖P.wK x‖ < 1) : P.inner x := by
  by_contra hi
  rw [(P.norm_wK_eq_one_iff hx).2 hi] at h
  exact lt_irrefl _ h

/-! #### The charts at the vertices -/

/-- The domain `V_i ⊆ ℂ` of the chart at `v_i`. -/
def Vv (i : ι) : Set ℂ := {h | P.F i (t.xv i h)}

/-- Its closure `K_i`. -/
def Kv (i : ι) : Set ℂ := {h | P.Fc i (t.xv i h)}

theorem isOpen_Vv (i : ι) : IsOpen (P.Vv i) :=
  (P.isOpen_F i).preimage (t.continuous_xv i)

theorem isClosed_Kv (i : ι) : IsClosed (P.Kv i) :=
  (P.isClosed_Fc i).preimage (t.continuous_xv i)

theorem Vv_subset_Kv (i : ι) : P.Vv i ⊆ P.Kv i := fun _ hx => P.F_Fc _ _ hx

theorem xv_mem {i : ι} {h : ℂ} (hh : h ∈ P.Kv i) : t.xv i h ∈ P.P := P.Fc_mem i h hh

theorem isCompact_Kv (i : ι) : IsCompact (P.Kv i) :=
  Metric.isCompact_of_isClosed_isBounded (P.isClosed_Kv i) (P.isBounded_Fc i)

theorem zero_mem_Vv (i : ι) : (0 : ℂ) ∈ P.Vv i := P.F_vertex i

/-- The point of the double, as a vector of `ℝ ⊕ ℂ`. -/
def chartVec (i : ι) (h : ℂ) : Euc3 :=
  WithLp.toLp 2 (sheet h * √(1 - ‖P.wK (t.xv i h)‖ ^ 2), P.wK (t.xv i h))

theorem sqrt_eq_zero_of_im_eq_zero (i : ι) {h : ℂ} (hK : h ∈ P.Kv i) (hh : h.im = 0) :
    √(1 - ‖P.wK (t.xv i h)‖ ^ 2) = 0 := by
  rw [Real.sqrt_eq_zero']
  have := (P.norm_wK_eq_one_iff (P.xv_mem hK)).2 (P.not_inner_of_real i h hh hK)
  rw [this]; norm_num

theorem norm_chartVec (i : ι) {h : ℂ} (hh : h ∈ P.Kv i) : ‖P.chartVec i h‖ = 1 := by
  have hx := P.xv_mem hh
  have hle := P.norm_wK_le hx
  have hsq : ‖P.chartVec i h‖ ^ 2 = 1 := by
    rw [chartVec, norm_polarSum_sq]
    simp only [WithLp.fst, WithLp.snd]
    by_cases him : h.im = 0
    · rw [P.sqrt_eq_zero_of_im_eq_zero i hh him, mul_zero]
      have : ‖P.wK (t.xv i h)‖ = 1 := by
        have h0 := Real.sqrt_eq_zero'.1 (P.sqrt_eq_zero_of_im_eq_zero i hh him)
        nlinarith [norm_nonneg (P.wK (t.xv i h))]
      rw [this]; norm_num
    · rw [mul_pow, sheet_sq, one_mul, Real.sq_sqrt (by nlinarith [norm_nonneg (P.wK (t.xv i h))])]
      ring
  nlinarith [norm_nonneg (P.chartVec i h)]

/-- **The chart map at `v_i`**, `ℂ → Double`: `h` goes to the point over `x_i(h)`, on the sheet
of `h`. -/
def chartMap (i : ι) (h : ℂ) : P.Double :=
  if hh : ‖P.chartVec i h‖ = 1 then P.ofSph2 ⟨P.chartVec i h, mem_sphere_zero_iff_norm.2 hh⟩
  else P.ofSph2 northPole

theorem coe_chartMap (i : ι) {h : ℂ} (hh : h ∈ P.Kv i) :
    ((P.toSph2 (P.chartMap i h) : Sph2) : Euc3) = P.chartVec i h := by
  rw [chartMap, dif_pos (P.norm_chartVec i hh)]; rfl

theorem disc_chartMap (i : ι) {h : ℂ} (hh : h ∈ P.Kv i) :
    P.disc (P.chartMap i h) = P.wK (t.xv i h) := by
  rw [disc, P.coe_chartMap i hh]; rfl

theorem height_chartMap (i : ι) {h : ℂ} (hh : h ∈ P.Kv i) :
    P.height (P.chartMap i h) = sheet h * √(1 - ‖P.wK (t.xv i h)‖ ^ 2) := by
  rw [height, P.coe_chartMap i hh]; rfl

theorem fold_chartMap (i : ι) {h : ℂ} (hh : h ∈ P.Kv i) :
    P.fold (P.chartMap i h) = t.xv i h := by
  have hx := P.xv_mem hh
  rw [fold, P.disc_chartMap i hh, wK, Homeomorph.symm_apply_apply, P.stereoInv_stereoFun_R hx,
    inv_smul_smul]

/-- The open set where the chart at `v_o` of the points `x_i(h)` is defined. -/
def Ov (i : ι) : Set ℂ := {h | ((t.R P.o • t.xv i h : Sph2) : Euc3).fst ≠ -1}

theorem isOpen_Ov (i : ι) : IsOpen (P.Ov i) :=
  isOpen_ne_fun (((WithLp.prod_continuous_ofLp 2 ℝ ℂ).fst.comp continuous_subtype_val).comp
    ((continuous_const_smul _).comp (t.continuous_xv i))) continuous_const

theorem Kv_subset_Ov (i : ι) : P.Kv i ⊆ P.Ov i := fun _ hh => P.fst_ne _ (P.xv_mem hh)

theorem continuousOn_wK_xv (i : ι) : ContinuousOn (fun h => P.wK (t.xv i h)) (P.Ov i) := by
  refine P.eK.continuous.comp_continuousOn ?_
  refine continuousOn_stereoFun.comp
    ((continuous_const_smul _).comp (t.continuous_xv i)).continuousOn
    fun h hh => hh

theorem continuousOn_chartVec (i : ι) : ContinuousOn (P.chartVec i) (P.Kv i) := by
  set f : ℂ → ℝ := fun h => √(1 - ‖P.wK (t.xv i h)‖ ^ 2)
  have hf : ContinuousOn f (P.Kv i) :=
    (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
      ((continuous_norm.comp_continuousOn ((P.continuousOn_wK_xv i).mono
        (P.Kv_subset_Ov i))).pow 2)))
  have hfs : ContinuousOn (fun h => sheet h * f h) (P.Kv i) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (P.Kv i).restrict (fun h => sheet h * f h) =
        fun h : P.Kv i => if (0 : ℝ) ≤ (h : ℂ).im then f h else -f h := by
      funext h; simp only [Set.restrict, sheet]; split_ifs <;> ring
    rw [heq]
    have hfr : Continuous fun h : P.Kv i => f h := continuousOn_iff_continuous_restrict.1 hf
    refine continuous_if_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
      hfr.continuousOn hfr.neg.continuousOn fun h heq => ?_
    have h0 : f h = 0 := P.sqrt_eq_zero_of_im_eq_zero i h.2 heq.symm
    show f h = -f h
    rw [h0, neg_zero]
  exact (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp_continuousOn
    (hfs.prodMk ((P.continuousOn_wK_xv i).mono (P.Kv_subset_Ov i)))

theorem continuousOn_chartMap (i : ι) : ContinuousOn (P.chartMap i) (P.Kv i) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (P.Kv i).restrict (P.chartMap i) = fun h : P.Kv i =>
      P.ofSph2 ⟨P.chartVec i h, mem_sphere_zero_iff_norm.2 (P.norm_chartVec i h.2)⟩ := by
    funext h; simp only [Set.restrict, chartMap, dif_pos (P.norm_chartVec i h.2)]
  rw [heq]
  exact P.continuous_ofSph2.comp
    ((continuousOn_iff_continuous_restrict.1 (P.continuousOn_chartVec i)).subtype_mk _)

/-- A point of the double is determined by its height and its disc coordinate. -/
theorem ext_height_disc {y y' : P.Double} (h1 : P.height y = P.height y')
    (h2 : P.disc y = P.disc y') : y = y' := by
  have : ((P.toSph2 y : Sph2) : Euc3) = ((P.toSph2 y' : Sph2) : Euc3) := by
    have e : ∀ z : P.Double,
        ((P.toSph2 z : Sph2) : Euc3) = WithLp.toLp 2 (P.height z, P.disc z) :=
      fun z => rfl
    rw [e, e, h1, h2]
  exact Subtype.ext this

/-- **The chart map is injective on `V_i`.** -/
theorem injOn_chartMap (i : ι) : InjOn (P.chartMap i) (P.Vv i) := by
  intro h hh h' hh' he
  have hK := P.Vv_subset_Kv i hh
  have hK' := P.Vv_subset_Kv i hh'
  have hx : t.xv i h = t.xv i h' := by
    rw [← P.fold_chartMap i hK, ← P.fold_chartMap i hK', he]
  have hF : polarFold (t.α i) h = polarFold (t.α i) h' := by
    have := congrArg (fun y => stereoFun (t.R i • y)) hx
    simp only [StarFrames.xv, smul_inv_smul, stereoFun_stereoInv] at this
    exact this
  rcases polarFold_eq_iff_of_lt_two_pi (t.α_pos i) (t.α_lt i) hF with rfl | hc
  · rfl
  · have hheight := congrArg P.height he
    rw [P.height_chartMap i hK, P.height_chartMap i hK', ← hx] at hheight
    have him : h.im = 0 := by
      by_cases h0 : √(1 - ‖P.wK (t.xv i h)‖ ^ 2) = 0
      · have hT := P.xv_mem hK
        have h1 : ‖P.wK (t.xv i h)‖ = 1 := by
          have := Real.sqrt_eq_zero'.1 h0
          nlinarith [P.norm_wK_le hT, norm_nonneg (P.wK (t.xv i h))]
        have hni := (P.norm_wK_eq_one_iff hT).1 h1
        by_contra him
        exact hni (P.inner_of_im i h him hh)
      · have hs : sheet h = sheet h' := mul_right_cancel₀ h0 hheight
        rw [hc] at hs
        unfold sheet at hs
        rw [Complex.conj_im] at hs
        split_ifs at hs with h1 h2 h2 <;> linarith
    rw [hc]; exact Complex.ext rfl (by simp [him])

/-- The image of `V_i`. -/
def Uv (i : ι) : Set P.Double := {y | P.F i (P.fold y)}

theorem isOpen_Uv (i : ι) : IsOpen (P.Uv i) :=
  (P.isOpen_F i).preimage P.continuous_fold

/-- **The image of `V_i` under the chart map is `U_i`.** -/
theorem chartMap_image_Vv (i : ι) : P.chartMap i '' P.Vv i = P.Uv i := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    show P.F i (P.fold (P.chartMap i h))
    rw [P.fold_chartMap i (P.Vv_subset_Kv i hh)]; exact hh
  · intro hy
    set x := P.fold y with hxdef
    have hxT : x ∈ P.P := P.fold_mem y
    have hpre : ∃ h : ℂ, t.xv i h = x ∧ (0 ≤ P.height y → 0 ≤ h.im) ∧
        (P.height y < 0 → h.im < 0) := by
      rcases le_or_gt 0 (P.height y) with hy0 | hy0
      · obtain ⟨h, h1, h2⟩ := P.exists_up i x hxT hy
        exact ⟨h, h1, fun _ => h2, fun h' => absurd hy0 (not_le.2 h')⟩
      · have hlt : ‖P.disc y‖ < 1 := by
          have := P.height_sq_add y
          nlinarith [norm_nonneg (P.disc y)]
        have hin : P.inner x := P.inner_of_norm_wK_lt hxT (by rw [hxdef, P.wK_fold]; exact hlt)
        obtain ⟨h, h1, h2⟩ := P.exists_down i x hxT hy hin
        exact ⟨h, h1, fun h' => absurd h' (not_le.2 hy0), fun _ => h2⟩
    obtain ⟨h, hxv, hup, hdown⟩ := hpre
    have hhV : h ∈ P.Vv i := by show P.F i (t.xv i h); rw [hxv]; exact hy
    refine ⟨h, hhV, ?_⟩
    have hK := P.Vv_subset_Kv i hhV
    refine P.ext_height_disc ?_ ?_
    · rw [P.height_chartMap i hK, hxv, hxdef, P.wK_fold]
      have hsq : 1 - ‖P.disc y‖ ^ 2 = P.height y ^ 2 := by
        have := P.height_sq_add y; linarith
      rw [hsq, Real.sqrt_sq_eq_abs]
      rcases le_or_gt 0 (P.height y) with hy0 | hy0
      · rw [sheet, if_pos (hup hy0), one_mul, abs_of_nonneg hy0]
      · rw [sheet, if_neg (not_le.2 (hdown hy0)), abs_of_neg hy0]; ring
    · rw [P.disc_chartMap i hK, hxv, hxdef, P.wK_fold]

theorem chartMap_mem_Uv_of_mem_Kv {i : ι} {h : ℂ} (hh : h ∈ P.Kv i) :
    P.chartMap i h ∈ P.Uv i ↔ h ∈ P.Vv i := by
  show P.F i (P.fold (P.chartMap i h)) ↔ _
  rw [P.fold_chartMap i hh]; rfl

theorem isOpenMap_chartMap (i : ι) : IsOpenMap ((P.Vv i).restrict (P.chartMap i)) :=
  isOpenMap_restrict_of_isCompact (P.isCompact_Kv i) (P.isOpen_Vv i) (P.Vv_subset_Kv i)
    (P.continuousOn_chartMap i) (P.injOn_chartMap i)
    (by rw [P.chartMap_image_Vv]; exact P.isOpen_Uv i)
    (fun h hK hV hU => by
      rw [P.chartMap_image_Vv] at hU
      exact hV ((P.chartMap_mem_Uv_of_mem_Kv hK).1 hU))

/-- **The chart of the double at `v_i`**, source `V_i`, target `U_i`. -/
def chartPH (i : ι) : OpenPartialHomeomorph ℂ P.Double :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict ((P.injOn_chartMap i).toPartialEquiv _ _)
    ((P.continuousOn_chartMap i).mono (P.Vv_subset_Kv i)) (P.isOpenMap_chartMap i)
    (P.isOpen_Vv i)

theorem chartPH_source (i : ι) : (P.chartPH i).source = P.Vv i := rfl

theorem chartPH_target (i : ι) : (P.chartPH i).target = P.Uv i := by
  show P.chartMap i '' P.Vv i = _
  exact P.chartMap_image_Vv i

theorem chartPH_apply (i : ι) (h : ℂ) : P.chartPH i h = P.chartMap i h := rfl

/-! #### The cone charts and the comparison with the developing maps -/

/-- **The chart of the double at `v_i`, from the cone `C_{θ_i}`.** -/
def Φ (i : ι) : OpenPartialHomeomorph (SphCone (t.θc i)) P.Double :=
  (SphCone.homeoComplex (t.θc i)).toOpenPartialHomeomorph.trans (P.chartPH i)

theorem Φ_apply (i : ι) (c : SphCone (t.θc i)) :
    P.Φ i c = P.chartMap i (SphCone.homeoComplex (t.θc i) c) := rfl

theorem Φ_symm_apply (i : ι) (y : P.Double) :
    (P.Φ i).symm y = (SphCone.homeoComplex (t.θc i)).symm ((P.chartPH i).symm y) := rfl

theorem Φ_source (i : ι) :
    (P.Φ i).source = SphCone.homeoComplex (t.θc i) ⁻¹' P.Vv i := by
  rw [Φ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    univ_inter]; rfl

theorem Φ_target (i : ι) : (P.Φ i).target = P.Uv i := by
  rw [Φ, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ, chartPH_target]

/-- **Reading a cone chart through the developing map** (as `GX.SphPolygon.eventually_chart_eq`). -/
theorem eventually_chart_eq (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : P.Double}
    (hy : y ∈ ((P.Φ i).symm.trans a).source) (h0 : (P.chartPH i).symm y ≠ 0)
    {Ref : P.Double → Sph2} {g : SO3}
    (hform : ∀ᶠ q in 𝓝 (qOf _ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      g • Ref (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) :
    ∃ g' : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ i).symm.trans a) y' = g' • Ref y' := by
  set h₀ := (P.chartPH i).symm y with hh₀
  set q₀ := qOf h₀ h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hyU : y ∈ (P.chartPH i).target := by
    have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
    rw [chartPH_target]; exact this
  have hh₀V : h₀ ∈ P.Vv i := (P.chartPH i).map_target hyU
  have hy₀ : P.chartPH i h₀ = y := (P.chartPH i).right_inv hyU
  have hc : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) = (P.Φ i).symm y := by
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [homeoComplex_mk_lift, cplx_qOf, Φ_symm_apply, Homeomorph.apply_symm_apply]
  have hca : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) ∈ a.source := by rw [hc]; exact hy.2
  obtain ⟨k, hk⟩ := sphCone_chart_dev (t.θc i) (y := polarHalfPlaneLift q₀) q₀.2 ha hca
  have hk' := (continuous_polarHalfPlaneLift.continuousAt (x := q₀)).eventually hk
  have hV : ∀ᶠ q in 𝓝 q₀, DInfty.cplx 1 (DInfty.posEmb q) ∈ P.Vv i :=
    continuous_cplx_posEmb.continuousAt.eventually ((P.isOpen_Vv i).mem_nhds (by
      show DInfty.cplx 1 (DInfty.posEmb q₀) ∈ P.Vv i; rw [cplx_qOf]; exact hh₀V))
  have hall : ∀ᶠ q in 𝓝 q₀, ((P.Φ i).symm.trans a) (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))
      = (k * g) • Ref (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
    filter_upwards [hk', hV, hform] with q e1 e2 e3
    have hsym : (P.Φ i).symm (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) =
        SphCone.mk (t.θc i) (polarHalfPlaneLift q) := by
      rw [Φ_symm_apply, ← chartPH_apply, (P.chartPH i).left_inv e2]
      apply (SphCone.homeoComplex (t.θc i)).injective
      rw [Homeomorph.apply_symm_apply, homeoComplex_mk_lift]
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsym, mul_smul, ← e3]
    exact e1
  obtain ⟨S, hS, hSall⟩ := hall.exists_mem
  refine ⟨k * g, Filter.mem_of_superset
    (x := (P.chartPH i) '' ((fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∩
      P.Vv i)) ?_ ?_⟩
  · have h1 : (fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∈ 𝓝 h₀ := by
      have := isOpenMap_cplx_posEmb.image_mem_nhds hS
      rwa [cplx_qOf] at this
    have := (P.chartPH i).image_mem_nhds hh₀V (inter_mem h1 ((P.isOpen_Vv i).mem_nhds hh₀V))
    rwa [hy₀] at this
  · rintro _ ⟨_, ⟨⟨q, hq, rfl⟩, -⟩, rfl⟩
    exact hSall q hq

/-- The reference map near a point of the side `e_k`. -/
def refEdge (k : ι) (y : P.Double) : Sph2 :=
  if 0 ≤ P.height y then P.fold y else t.σ k (P.fold y)

theorem height_chartMap_nonneg (i : ι) {h : ℂ} (hK : h ∈ P.Kv i) (him : 0 ≤ h.im) :
    0 ≤ P.height (P.chartMap i h) := by
  rw [P.height_chartMap i hK, sheet, if_pos him, one_mul]; exact Real.sqrt_nonneg _

theorem sqrt_pos_of_im_ne_zero (i : ι) {h : ℂ} (hV : h ∈ P.Vv i) (him : h.im ≠ 0) :
    0 < √(1 - ‖P.wK (t.xv i h)‖ ^ 2) := by
  have hK := P.Vv_subset_Kv i hV
  have := P.norm_wK_lt (P.xv_mem hK) (P.inner_of_im i h him hV)
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg (P.wK (t.xv i h))]

theorem height_chartMap_neg (i : ι) {h : ℂ} (hV : h ∈ P.Vv i) (him : h.im < 0) :
    P.height (P.chartMap i h) < 0 := by
  rw [P.height_chartMap i (P.Vv_subset_Kv i hV), sheet, if_neg (not_le.2 him)]
  have := P.sqrt_pos_of_im_ne_zero i hV him.ne
  linarith

theorem im_pos_of_height_pos (i : ι) {h : ℂ} (hK : h ∈ P.Kv i)
    (hy : 0 < P.height (P.chartMap i h)) : 0 < h.im := by
  rw [P.height_chartMap i hK] at hy
  rcases lt_trichotomy h.im 0 with h1 | h1 | h1
  · rw [sheet, if_neg (not_le.2 h1)] at hy
    nlinarith [Real.sqrt_nonneg (1 - ‖P.wK (t.xv i h)‖ ^ 2)]
  · rw [P.sqrt_eq_zero_of_im_eq_zero i hK h1, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
  · exact h1

theorem im_neg_of_height_neg (i : ι) {h : ℂ} (hK : h ∈ P.Kv i)
    (hy : P.height (P.chartMap i h) < 0) : h.im < 0 := by
  by_contra h1
  exact absurd (P.height_chartMap_nonneg i hK (not_lt.1 h1)) (not_le.2 hy)

theorem eventually_Vv (i : ι) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ P.Vv i) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), DInfty.cplx 1 (DInfty.posEmb q) ∈ P.Vv i :=
  continuous_cplx_posEmb.continuousAt.eventually ((P.isOpen_Vv i).mem_nhds (by
    show DInfty.cplx 1 (DInfty.posEmb (qOf h₀ h0)) ∈ P.Vv i
    rw [cplx_qOf]; exact hV))

theorem hform_up (i : ι) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ P.Vv i) (him : 0 < h₀.im) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • P.fold (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  filter_upwards [P.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_up him)] with q hq hφ
  rw [P.fold_chartMap i (P.Vv_subset_Kv i hq), t.dev_eq_up i q hφ.1.le hφ.2.le]

theorem hform_down (i : ι) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ P.Vv i) (him : h₀.im < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSO3 (t.R i) • conjSph (P.fold (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) := by
  filter_upwards [P.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_down him)]
    with q hq hφ
  rw [P.fold_chartMap i (P.Vv_subset_Kv i hq), t.dev_eq_down i q hφ.1.le hφ.2.le, conjSph_smul]

theorem hform_edge_a (i : ι) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ P.Vv i) (him : h₀.im = 0)
    (hre : 0 < h₀.re) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • P.refEdge (t.a i) (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo (-(1 / 2)) (1 / 2) := by
    rw [Complex.arg_eq_zero_iff.2 ⟨hre.le, him⟩, zero_div]; constructor <;> norm_num
  filter_upwards [P.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := P.Vv_subset_Kv i hq
  rcases le_or_gt 0 q.1.2 with h1 | h1
  · have hh : 0 ≤ P.height (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine P.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ h1 hφ.2.le)
    rw [refEdge, if_pos hh, P.fold_chartMap i hK, t.dev_eq_up i q h1 hφ.2.le]
  · have hh : P.height (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine P.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem _ hφ.1 h1)
    rw [refEdge, if_neg (not_le.2 hh), P.fold_chartMap i hK, t.dev_eq_down i q hφ.1.le h1.le]
    conv_lhs => rw [← t.R_σ_a i (t.R i • t.xv i _), inv_smul_smul]

theorem hform_edge_b (i : ι) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ P.Vv i) (him : h₀.im = 0)
    (hre : h₀.re < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • P.refEdge (t.b i) (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo 0 1 := by
    rw [Complex.arg_eq_pi_iff.2 ⟨hre, him⟩]
    have hπ := Real.pi_pos
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  filter_upwards [P.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := P.Vv_subset_Kv i hq
  rcases le_or_gt q.1.2 (1 / 2) with h1 | h1
  · have hh : 0 ≤ P.height (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine P.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ hφ.1.le h1)
    rw [refEdge, if_pos hh, P.fold_chartMap i hK, t.dev_eq_up i q hφ.1.le h1]
  · have hh : P.height (P.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine P.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem' _ h1 hφ.2)
    rw [refEdge, if_neg (not_le.2 hh), P.fold_chartMap i hK, t.dev_eq_down_one i q h1.le hφ.2.le]

/-- A chart of the cone family at `v_i` never contains `v_i`. -/
theorem chartPH_symm_ne_zero (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : P.Double}
    (hy : y ∈ ((P.Φ i).symm.trans a).source) : (P.chartPH i).symm y ≠ 0 := by
  intro h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hap : (P.Φ i).symm y = SphCone.apex (t.θc i) := by
    rw [Φ_symm_apply, h0]
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [Homeomorph.apply_symm_apply, homeoComplex_apex]
  have hreg : SphCone.apex (t.θc i) ∈ Reg SO3 Sph2 (SphCone (t.θc i)) :=
    mem_support.2 ⟨a, ha, hap ▸ hy.2⟩
  exact (SphCone.apex_mem_sing_iff _).2 (t.θc_ne i) hreg

theorem mem_target_of_mem_source (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    {y : P.Double} (hy : y ∈ ((P.Φ i).symm.trans a).source) : y ∈ (P.chartPH i).target := by
  rw [OpenPartialHomeomorph.trans_source] at hy
  have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
  rw [chartPH_target]; exact this

theorem loc_up (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : P.Double}
    (hy : y ∈ ((P.Φ i).symm.trans a).source) (hpos : 0 < P.height y) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ i).symm.trans a) y' = g • P.fold y' := by
  have h0 := P.chartPH_symm_ne_zero i ha hy
  have hyU := P.mem_target_of_mem_source i hy
  have hV : (P.chartPH i).symm y ∈ P.Vv i := (P.chartPH i).map_target hyU
  have hyc : P.chartMap i ((P.chartPH i).symm y) = y := (P.chartPH i).right_inv hyU
  have him := P.im_pos_of_height_pos i (P.Vv_subset_Kv i hV) (by rw [hyc]; exact hpos)
  exact P.eventually_chart_eq i ha hy h0 (P.hform_up i h0 hV him)

theorem loc_down (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : P.Double}
    (hy : y ∈ ((P.Φ i).symm.trans a).source) (hneg : P.height y < 0) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ i).symm.trans a) y' = g • conjSph (P.fold y') := by
  have h0 := P.chartPH_symm_ne_zero i ha hy
  have hyU := P.mem_target_of_mem_source i hy
  have hV : (P.chartPH i).symm y ∈ P.Vv i := (P.chartPH i).map_target hyU
  have hyc : P.chartMap i ((P.chartPH i).symm y) = y := (P.chartPH i).right_inv hyU
  have him := P.im_neg_of_height_neg i (P.Vv_subset_Kv i hV) (by rw [hyc]; exact hneg)
  exact P.eventually_chart_eq i ha hy h0 (Ref := fun y => conjSph (P.fold y))
    (P.hform_down i h0 hV him)

/-- **Near a point of the side `e_k`, the cone charts are translates of `refEdge k`.** -/
theorem loc_edge (i : ι) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : P.Double}
    (hy : y ∈ ((P.Φ i).symm.trans a).source) {k : ι} (hk : P.onSide k (P.fold y)) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ i).symm.trans a) y' = g • P.refEdge k y' := by
  have h0 := P.chartPH_symm_ne_zero i ha hy
  have hyU := P.mem_target_of_mem_source i hy
  have hV : (P.chartPH i).symm y ∈ P.Vv i := (P.chartPH i).map_target hyU
  have hyc : P.chartMap i ((P.chartPH i).symm y) = y := (P.chartPH i).right_inv hyU
  set h₀ := (P.chartPH i).symm y
  have hfold : P.fold y = t.xv i h₀ := by rw [← hyc, P.fold_chartMap i (P.Vv_subset_Kv i hV)]
  rw [hfold] at hk
  rcases P.side_eq i k h₀ h0 hV hk with ⟨rfl, him, hre⟩ | ⟨rfl, him, hre⟩
  · exact P.eventually_chart_eq i ha hy h0 (P.hform_edge_a i h0 hV him hre)
  · exact P.eventually_chart_eq i ha hy h0 (P.hform_edge_b i h0 hV him hre)

/-- On the circle `u = 0` of the double, the fold lies on a side. -/
theorem exists_side_of_height_eq_zero {y : P.Double} (hy : P.height y = 0) :
    ∃ k, P.onSide k (P.fold y) := by
  have h1 : ‖P.disc y‖ = 1 := by
    have := P.height_sq_add y
    rw [hy] at this
    nlinarith [norm_nonneg (P.disc y)]
  rw [← P.wK_fold] at h1
  exact P.exists_side _ (P.fold_mem y) ((P.norm_wK_eq_one_iff (P.fold_mem y)).1 h1)

/-- The cone charts at `v_i`. -/
def coneAtlas (i : ι) : Set (OpenPartialHomeomorph P.Double Sph2) :=
  (fun a => (P.Φ i).symm.trans a) '' aeAtlas SO3 Sph2 (SphCone (t.θc i))

/-- **The generating atlas of the double.** -/
def atlas : Set (OpenPartialHomeomorph P.Double Sph2) := ⋃ i, P.coneAtlas i

/-- **The generating atlas is a `(SO(3), 𝕊²)`-atlas.** -/
theorem isGXAtlas_atlas : IsGXAtlas SO3 P.atlas := by
  refine isGXAtlas_of_eventually ?_
  rintro e he e' he' y ⟨hye, hye'⟩
  obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.1 he
  obtain ⟨j, b, hb, rfl⟩ := mem_iUnion.1 he'
  have key : ∀ {Ref : P.Double → Sph2},
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ i).symm.trans a) y' = g • Ref y') →
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ j).symm.trans b) y' = g • Ref y') →
      ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((P.Φ j).symm.trans b) y' = g • ((P.Φ i).symm.trans a) y' := by
    rintro Ref ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    filter_upwards [h₁, h₂] with y' e1 e2
    rw [e2, e1, mul_smul, inv_smul_smul]
  rcases lt_trichotomy 0 (P.height y) with hp | h0 | hn
  · exact key (P.loc_up i ha hye hp) (P.loc_up j hb hye' hp)
  · obtain ⟨k, hk⟩ := P.exists_side_of_height_eq_zero h0.symm
    exact key (P.loc_edge i ha hye hk) (P.loc_edge j hb hye' hk)
  · exact key (Ref := fun y => conjSph (P.fold y)) (P.loc_down i ha hye hn)
      (P.loc_down j hb hye' hn)

/-! #### The singular `(SO(3), 𝕊²)`-structure of the double, and its cone points -/

/-- **The vertex `v_i` of the double.** -/
def vertex (i : ι) : P.Double := P.chartMap i 0

theorem fold_vertex (i : ι) : P.fold (P.vertex i) = t.vertex i :=
  P.fold_chartMap i (P.Vv_subset_Kv i (P.zero_mem_Vv i))

theorem vertex_injective : Injective P.vertex := by
  intro i j hij
  apply P.vertex_inj
  rw [← P.fold_vertex, ← P.fold_vertex, hij]

theorem vertex_eq_Φ (i : ι) : P.vertex i = P.Φ i (SphCone.apex (t.θc i)) := by
  rw [Φ_apply, homeoComplex_apex]; rfl

theorem apex_mem_Φ_source (i : ι) : SphCone.apex (t.θc i) ∈ (P.Φ i).source := by
  rw [Φ_source, mem_preimage, homeoComplex_apex]; exact P.zero_mem_Vv i

/-- **Off the vertices, the double is covered by the cone charts.** -/
theorem mem_support_atlas {y : P.Double} (hy : ∀ i, y ≠ P.vertex i) : y ∈ support P.atlas := by
  obtain ⟨i, hi⟩ := P.cover (P.fold y) (P.fold_mem y)
  have hyU : y ∈ (P.chartPH i).target := by rw [chartPH_target]; exact hi
  set h := (P.chartPH i).symm y
  have hyc : P.chartMap i h = y := (P.chartPH i).right_inv hyU
  have h0 : h ≠ 0 := fun e => hy i (by rw [← hyc, e]; rfl)
  set c := (SphCone.homeoComplex (t.θc i)).symm h
  have hc : c ≠ SphCone.apex (t.θc i) := fun e => h0 (by
    have := congrArg (SphCone.homeoComplex (t.θc i)) e
    rwa [Homeomorph.apply_symm_apply, homeoComplex_apex] at this)
  have hcreg : c ∈ Reg SO3 Sph2 (SphCone (t.θc i)) := by
    by_contra hcs
    have : c ∈ Sing SO3 Sph2 (SphCone (t.θc i)) := hcs
    rw [SphCone.sing_eq _ (t.θc_ne i)] at this
    exact hc this
  obtain ⟨a, ha, hca⟩ := mem_support.1 hcreg
  refine mem_support.2 ⟨_, mem_iUnion.2 ⟨i, a, ha, rfl⟩, ?_⟩
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Φ_target]
  exact ⟨hi, hca⟩

/-- **The generating atlas is an a.e. `(SO(3), 𝕊²)`-atlas.** -/
theorem isAEAtlas_atlas [Finite ι] : IsAEAtlas SO3 P.atlas := by
  refine ⟨P.isGXAtlas_atlas, ?_⟩
  have hP : IsPortly (⋂ i, {P.vertex i}ᶜ : Set P.Double) :=
    isPortly_iInter fun i => isPortly_compl_singleton_sph2 (P.toSph2 (P.vertex i))
  refine hP.mono (fun y hy => P.mem_support_atlas fun i => ?_) (isOpen_support _)
  exact mem_iInter.1 hy i

/-- **The singular `(SO(3), 𝕊²)`-structure of the double**: the maximal a.e. atlas generated by
the cone charts. -/
instance singularGXStructure [Finite ι] : SingularGXStructure SO3 Sph2 P.Double :=
  ⟨maximalAEAtlas SO3 P.atlas, P.isAEAtlas_atlas.isMaximalAEAtlas_maximalAEAtlas⟩

theorem aeAtlas_eq [Finite ι] : aeAtlas SO3 Sph2 P.Double = maximalAEAtlas SO3 P.atlas := rfl

/-- **The singular points of the double are among its vertices.** -/
theorem sing_subset_range_vertex [Finite ι] : Sing SO3 Sph2 P.Double ⊆ range P.vertex := by
  intro y hy
  by_contra hr
  have hy' : ∀ i, y ≠ P.vertex i := fun i e => hr ⟨i, e.symm⟩
  exact hy (support_mono P.isAEAtlas_atlas.subset_maximalAEAtlas (P.mem_support_atlas hy'))

/-- The domain of `Φ_i`, an open subset of `C_{θ_i}`. -/
def ΦV (i : ι) : Opens (SphCone (t.θc i)) := ⟨(P.Φ i).source, (P.Φ i).open_source⟩

instance (i : ι) : Nonempty (P.ΦV i) := ⟨⟨_, P.apex_mem_Φ_source i⟩⟩

/-- **`Φ_i` is an a.e. `(SO(3), 𝕊²)`-morphism** on its domain. -/
theorem isAEMorphism_Φ [Finite ι] (i : ι) :
    IsAEMorphism SO3 Sph2 (fun v : P.ΦV i => P.Φ i (v : SphCone (t.θc i))) := by
  set V := P.ΦV i
  haveI : Nonempty V := ⟨⟨_, P.apex_mem_Φ_source i⟩⟩
  set ι' := V.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hιs : ι'.source = univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
  have hB := isMaximalAEAtlas_aeAtlas SO3 Sph2 V
  have hcont : Continuous fun v : V => P.Φ i (v : SphCone (t.θc i)) :=
    (P.Φ i).continuousOn.comp_continuous continuous_subtype_val fun v => v.2
  have h := isAEMorphismOf_maximalAEAtlas_of_forall hB.1 P.isAEAtlas_atlas hcont fun b hb => by
    refine ⟨(P.Φ i).symm.trans (ι'.symm.trans b),
      mem_iUnion.2 ⟨i, _, symm_trans_mem_aeAtlas_of_opens V hb, rfl⟩, fun v hv => ?_,
      fun v hv => ?_⟩
    · have hl : (P.Φ i).symm (P.Φ i (v : SphCone (t.θc i))) = v := (P.Φ i).left_inv v.2
      have hι : ι'.symm (v : SphCone (t.θc i)) = v := ι'.left_inv (by rw [hιs]; exact mem_univ _)
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨(P.Φ i).map_source v.2, ?_⟩
      rw [mem_preimage, hl, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨?_, ?_⟩
      · rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]; exact mem_range_self _
      · rw [mem_preimage, hι]; exact hv
    · have hl : (P.Φ i).symm (P.Φ i (v : SphCone (t.θc i))) = v := (P.Φ i).left_inv v.2
      have hι : ι'.symm (v : SphCone (t.θc i)) = v := ι'.left_inv (by rw [hιs]; exact mem_univ _)
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [hl, hι]
  rwa [hB.maximalAEAtlas_eq] at h

theorem isConnected_ΦV (i : ι) : IsConnected ((P.ΦV i : Set (SphCone (t.θc i)))) := by
  have hc : IsConnected (P.Vv i) :=
    ((P.starConvex_F i).isPathConnected (P.zero_mem_Vv i)).isConnected
  have : ((P.ΦV i : Set (SphCone (t.θc i)))) = (SphCone.homeoComplex (t.θc i)).symm '' P.Vv i := by
    show (P.Φ i).source = _
    rw [Φ_source, Homeomorph.image_symm]
  rw [this]
  exact hc.image _ (SphCone.homeoComplex (t.θc i)).symm.continuous.continuousOn

/-- **The `X_{θ_i}`-chart of the double at `v_i`** (`def:atlas`). -/
def coneXAChart [Finite ι] (i : ι) : XAChart SO3 Sph2 SphCone sphConeS (t.θc i) (P.vertex i) where
  U := ⟨(P.Φ i).target, (P.Φ i).open_target⟩
  V := P.ΦV i
  φ := (P.Φ i).toHomeomorphSourceTarget.symm
  mem := by rw [P.vertex_eq_Φ]; exact (P.Φ i).map_source (P.apex_mem_Φ_source i)
  isConnected_V := P.isConnected_ΦV i
  isAEMorphism := by
    refine IsAEMorphism.symm_of_homeomorph ?_
    refine isAEMorphism_of_val_comp ⟨(P.Φ i).target, (P.Φ i).open_target⟩ ?_
    exact P.isAEMorphism_Φ i
  mem_S := by
    show (P.Φ i).symm (P.vertex i) ∈ sphConeS (t.θc i)
    rw [P.vertex_eq_Φ, (P.Φ i).left_inv (P.apex_mem_Φ_source i)]
    exact mem_singleton _

/-- **The vertex `v_i` is a cone point of angle `2α_i`.** -/
theorem isConePoint_vertex [Finite ι] (i : ι) : IsConePoint (t.θc i) (P.vertex i) :=
  ⟨P.coneXAChart i⟩

end StarPolygon

/-- **The double of a polygon with polar charts at its vertices is a cone sphere** with the cone
angles `2α_i`. -/
theorem StarPolygon.isConeSphere {s : ℕ} {t : StarFrames (Fin s)} (P : StarPolygon t) :
    IsConeSphere P.Double (fun i => 2 * t.α i) P.vertex where
  homeomorphic := ⟨P.homeoSph2⟩
  injective := P.vertex_injective
  pos i := by have := t.α_pos i; positivity
  isConePoint i := P.isConePoint_vertex i
  sing_subset := P.sing_subset_range_vertex

/-- **The double of a polygon with polar charts**, in the shape of `GX.TroyanovTheorem`'s
conclusion. -/
theorem StarPolygon.exists_isConeSphere {s : ℕ} {t : StarFrames (Fin s)} (P : StarPolygon t) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M (fun i => 2 * t.α i) p :=
  ⟨P.Double, inferInstance, inferInstance, P.vertex, P.isConeSphere⟩

end StarDouble

section DartSides

/-! ### Two ways out of the interior of a set of the stereographic plane -/

/-- **A point where `G_c ≤ 0` is not interior to a set inside `{G_c ≥ 0}`**, for a unit `c`
with `c 0 ≥ 0` (as `GX.SphPolygon.notMem_interior_K`). -/
theorem notMem_interior_of_subset_gfun {c : Fin 3 → ℝ} (hc0 : 0 ≤ c 0) (hc : c ⬝ᵥ c = 1)
    {S : Set ℂ} (hS : S ⊆ {v | 0 ≤ gfun c v}) {v : ℂ} (hk : gfun c v ≤ 0) : v ∉ interior S := by
  intro hv
  have hvK : v ∈ S := interior_subset hv
  have h0 : gfun c v = 0 := le_antisymm hk (hS hvK)
  have hc1 : c 0 * c 0 + c 1 * c 1 + c 2 * c 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three] using hc
  set g : ℂ := ⟨c 1 - c 0 * v.re, c 2 - c 0 * v.im⟩
  have hg : 0 < ‖g‖ := by
    rw [norm_pos_iff]
    intro hg0
    have e1 : c 1 = c 0 * v.re := by have := congrArg Complex.re hg0; simp [g] at this; linarith
    have e2 : c 2 = c 0 * v.im := by have := congrArg Complex.im hg0; simp [g] at this; linarith
    have : gfun c v = c 0 * (1 + ‖v‖ ^ 2) := by
      simp only [gfun, e1, e2, Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h0] at this
    have hc00 : c 0 = 0 := by
      have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
      nlinarith
    rw [hc00, zero_mul] at e1 e2
    rw [hc00, e1, e2] at hc1; norm_num at hc1
  have ht : Tendsto (fun δ : ℝ => v + (-(δ : ℂ)) * g) (𝓝[>] 0) (𝓝 v) := by
    have : Continuous fun δ : ℝ => v + (-(δ : ℂ)) * g := by fun_prop
    have h := this.tendsto 0
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, h1, h2⟩ := ((ht.eventually (isOpen_interior.mem_nhds hv)).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hK : 0 ≤ gfun c (v + (-(δ : ℂ)) * g) := hS (interior_subset h1)
  rw [SphTriangle.gfun_add, h0] at hK
  have hgn : ‖g‖ ^ 2 = g.re ^ 2 + g.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hu : ‖(-(δ : ℂ)) * g‖ ^ 2 = δ ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (le_of_lt h2), mul_pow]
  rw [hu] at hK
  have hre : ((-(δ : ℂ)) * g).re = -δ * g.re := by simp
  have him : ((-(δ : ℂ)) * g).im = -δ * g.im := by simp
  rw [hre, him] at hK
  have hgre : g.re = c 1 - c 0 * v.re := rfl
  have hgim : g.im = c 2 - c 0 * v.im := rfl
  rw [← hgre, ← hgim] at hK
  have hδ : (0 : ℝ) < δ := h2
  have : 0 < δ * ‖g‖ ^ 2 := by positivity
  nlinarith [mul_nonneg hc0 (mul_nonneg (sq_nonneg δ) (sq_nonneg ‖g‖))]

/-- **A point of the notch is not interior to a set inside a reflex sector**: if
`S ⊆ {Im ≥ 0} ∪ {sin α Re − cos α Im ≥ 0}` with `α ∈ ]π, 2π[`, a point where both are `≤ 0` is
not interior to `S` (move along `−e^{iα/2}`, into the notch). -/
theorem notMem_interior_notch {α : ℝ} (hα1 : π < α) (hα2 : α < 2 * π) {S : Set ℂ}
    (hS : S ⊆ {v | 0 ≤ v.im ∨ 0 ≤ Real.sin α * v.re - Real.cos α * v.im}) {v : ℂ}
    (h1 : v.im ≤ 0) (h2 : Real.sin α * v.re - Real.cos α * v.im ≤ 0) : v ∉ interior S := by
  intro hv
  set β := α / 2
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by
    show 0 < α / 2; linarith [Real.pi_pos]) (by show α / 2 < π; linarith)
  set d : ℂ := ⟨-Real.cos β, -Real.sin β⟩
  have hdre : d.re = -Real.cos β := rfl
  have hdim : d.im = -Real.sin β := rfl
  have hB : Real.sin α * d.re - Real.cos α * d.im = -Real.sin β := by
    rw [hdre, hdim]
    have : Real.sin α * Real.cos β - Real.cos α * Real.sin β = Real.sin β := by
      rw [← Real.sin_sub]; congr 1; simp only [β]; ring
    linarith
  have ht : Tendsto (fun δ : ℝ => v + (δ : ℂ) * d) (𝓝[>] 0) (𝓝 v) := by
    have : Continuous fun δ : ℝ => v + (δ : ℂ) * d := by fun_prop
    have h := this.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hδ1, hδ2⟩ := ((ht.eventually (isOpen_interior.mem_nhds hv)).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hδ : (0 : ℝ) < δ := hδ2
  have hmem := hS (interior_subset hδ1)
  simp only [mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul] at hmem
  rw [hdre, hdim] at hmem
  have hB' : Real.sin α * (v.re + δ * -Real.cos β) - Real.cos α * (v.im + δ * -Real.sin β) =
      (Real.sin α * v.re - Real.cos α * v.im) + δ * (Real.sin α * d.re - Real.cos α * d.im) := by
    rw [hdre, hdim]; ring
  rw [hB'] at hmem
  rw [hB] at hmem
  rcases hmem with hm | hm <;> nlinarith

/-! ### The dart: its sides -/

section DartSides

/-- The inward normal of the great circle leaving `(cos ℓ, −sin ℓ, 0)` at the angle `φ` above
the equator, towards `(cos ℓ, sin ℓ, 0)`. -/
def dartNuL (ℓ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin φ * Real.sin ℓ, Real.sin φ * Real.cos ℓ, -Real.cos φ]

/-- The inward normal of the great circle leaving `(cos ℓ, sin ℓ, 0)` at the angle `φ` above
the equator, towards `(cos ℓ, −sin ℓ, 0)`. -/
def dartNuR (ℓ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin φ * Real.sin ℓ, -(Real.sin φ * Real.cos ℓ), -Real.cos φ]

theorem dartNuL_dot_self (ℓ φ : ℝ) : dartNuL ℓ φ ⬝ᵥ dartNuL ℓ φ = 1 := by
  simp [dartNuL, dotProduct, Fin.sum_univ_three]
  have h1 := Real.sin_sq_add_cos_sq ℓ
  have h2 := Real.sin_sq_add_cos_sq φ
  linear_combination Real.sin φ ^ 2 * h1 + h2

theorem dartNuR_dot_self (ℓ φ : ℝ) : dartNuR ℓ φ ⬝ᵥ dartNuR ℓ φ = 1 := by
  simp [dartNuR, dotProduct, Fin.sum_univ_three]
  have h1 := Real.sin_sq_add_cos_sq ℓ
  have h2 := Real.sin_sq_add_cos_sq φ
  linear_combination Real.sin φ ^ 2 * h1 + h2

theorem dartNuL_dot_dartNuL (ℓ φ ψ : ℝ) : dartNuL ℓ φ ⬝ᵥ dartNuL ℓ ψ = Real.cos (φ - ψ) := by
  simp [dartNuL, dotProduct, Fin.sum_univ_three, Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq ℓ
  linear_combination Real.sin φ * Real.sin ψ * h1

theorem dartNuR_dot_dartNuR (ℓ φ ψ : ℝ) : dartNuR ℓ φ ⬝ᵥ dartNuR ℓ ψ = Real.cos (φ - ψ) := by
  simp [dartNuR, dotProduct, Fin.sum_univ_three, Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq ℓ
  linear_combination Real.sin φ * Real.sin ψ * h1

theorem dartNuL_dot_dartNuR (ℓ φ ψ : ℝ) : dartNuL ℓ φ ⬝ᵥ dartNuR ℓ ψ =
    Real.cos φ * Real.cos ψ - Real.sin φ * Real.sin ψ * Real.cos (2 * ℓ) := by
  simp [dartNuL, dartNuR, dotProduct, Fin.sum_univ_three, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq ℓ
  linear_combination Real.sin φ * Real.sin ψ * this

/-- **The sides of the dart**: `n₀ = −ν_L(u)` (`e₁₂`), `n₁ = ν_L(p)` (`e₂₃`), `n₂ = ν_R(q)`
(`e₃₄`), `n₃ = −ν_R(w)` (`e₄₁`), `ν_L = dartNuL`, `ν_R = dartNuR`. -/
def dartN (ℓ u w p q : ℝ) : Fin 4 → Fin 3 → ℝ :=
  ![-dartNuL ℓ u, dartNuL ℓ p, dartNuR ℓ q, -dartNuR ℓ w]

variable (ℓ u w p q : ℝ)

/-! The triple products of the sides (the signs of the sides at the vertices). -/

theorem dartN_tp_0_1 : dartN ℓ u w p q 1 ⬝ᵥ dartN ℓ u w p q 0 ⨯₃ dartN ℓ u w p q 3 =
    -(Real.sin (2 * ℓ) * Real.sin w * Real.sin (p - u)) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_0_2 : dartN ℓ u w p q 2 ⬝ᵥ dartN ℓ u w p q 0 ⨯₃ dartN ℓ u w p q 3 =
    -(Real.sin (2 * ℓ) * Real.sin u * Real.sin (q - w)) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_1_2 : dartN ℓ u w p q 2 ⬝ᵥ dartN ℓ u w p q 1 ⨯₃ dartN ℓ u w p q 0 =
    Real.sin (p - u) * Real.sin q * Real.sin (2 * ℓ) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_1_3 : dartN ℓ u w p q 3 ⬝ᵥ dartN ℓ u w p q 1 ⨯₃ dartN ℓ u w p q 0 =
    -(Real.sin (p - u) * Real.sin w * Real.sin (2 * ℓ)) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_2_0 : dartN ℓ u w p q 0 ⬝ᵥ dartN ℓ u w p q 2 ⨯₃ dartN ℓ u w p q 1 =
    Real.sin (2 * ℓ) * Real.sin q * Real.sin (p - u) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_2_3 : dartN ℓ u w p q 3 ⬝ᵥ dartN ℓ u w p q 2 ⨯₃ dartN ℓ u w p q 1 =
    Real.sin (2 * ℓ) * Real.sin p * Real.sin (q - w) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_3_1 : dartN ℓ u w p q 1 ⬝ᵥ dartN ℓ u w p q 3 ⨯₃ dartN ℓ u w p q 2 =
    Real.sin (q - w) * Real.sin p * Real.sin (2 * ℓ) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_3_0 : dartN ℓ u w p q 0 ⬝ᵥ dartN ℓ u w p q 3 ⨯₃ dartN ℓ u w p q 2 =
    -(Real.sin (q - w) * Real.sin u * Real.sin (2 * ℓ)) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_c1 : dartN ℓ u w p q 0 ⬝ᵥ dartN ℓ u w p q 1 ⨯₃ dartN ℓ u w p q 3 =
    Real.sin (2 * ℓ) * Real.sin w * Real.sin (p - u) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_c2 : dartN ℓ u w p q 2 ⬝ᵥ dartN ℓ u w p q 1 ⨯₃ dartN ℓ u w p q 3 =
    Real.sin (2 * ℓ) * Real.sin p * Real.sin (q - w) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_c3 : dartN ℓ u w p q 3 ⬝ᵥ dartN ℓ u w p q 0 ⨯₃ dartN ℓ u w p q 2 =
    Real.sin (2 * ℓ) * Real.sin u * Real.sin (q - w) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

theorem dartN_tp_c4 : dartN ℓ u w p q 1 ⬝ᵥ dartN ℓ u w p q 0 ⨯₃ dartN ℓ u w p q 2 =
    Real.sin (2 * ℓ) * Real.sin q * Real.sin (p - u) := by
  simp only [dartN, dartNuL, dartNuR, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_two_mul,
    Real.sin_sub]
  simp; ring

end DartSides

end DartSides

section DartModel

/-! ### The dart: frames and polygon -/

/-- **The parameters of a spherical dart with angles `α_i`.** The triangle `T` with base
`v₂ v₄` of length `2ℓ` (`v₂, v₄ = (cos ℓ, ∓sin ℓ, 0)`) and base angles `p = u + α₁`,
`q = w + α₃`, minus the triangle `T'` on the same base with base angles `u`, `w`: `T` has apex
angle `α₂` (`hT`, the spherical law of cosines), `T'` apex angle `2π − α₀` (`hT'`). The dart has
the vertices `v_0` (the apex of `T'`, reflex), `v_1 = v₂`, `v_2` (the apex of `T`), `v_3 = v₄`. -/
structure DartParams where
  /-- The angles; `α 0` is the reflex one. -/
  α : Fin 4 → ℝ
  /-- Half the length of the common base. -/
  ℓ : ℝ
  /-- The base angle of `T'` at `v₂`. -/
  u : ℝ
  /-- The base angle of `T'` at `v₄`. -/
  w : ℝ
  h0 : π < α 0
  h0' : α 0 < 2 * π
  h1 : 0 < α 1
  h2 : 0 < α 2
  h3 : 0 < α 3
  h2' : α 2 < π
  hu : 0 < u
  hw : 0 < w
  hp : u + α 1 < π
  hq : w + α 3 < π
  hℓ : 0 < ℓ
  hℓ' : ℓ < π / 2
  hT' : Real.cos u * Real.cos w - Real.sin u * Real.sin w * Real.cos (2 * ℓ) = -Real.cos (α 0)
  hT : Real.cos (u + α 1) * Real.cos (w + α 3) -
    Real.sin (u + α 1) * Real.sin (w + α 3) * Real.cos (2 * ℓ) = -Real.cos (α 2)

namespace DartParams

variable (D : DartParams)

/-- The sides `e₁₂, e₂₃, e₃₄, e₄₁`. -/
def n : Fin 4 → Fin 3 → ℝ := dartN D.ℓ D.u D.w (D.u + D.α 1) (D.w + D.α 3)

theorem α1_lt : D.α 1 < π := by linarith [D.hp, D.hu]

theorem α3_lt : D.α 3 < π := by linarith [D.hq, D.hw]

theorem α_pos (i : Fin 4) : 0 < D.α i := by
  fin_cases i
  · exact lt_trans Real.pi_pos D.h0
  · exact D.h1
  · exact D.h2
  · exact D.h3

theorem α_lt (i : Fin 4) : D.α i < 2 * π := by
  have := Real.pi_pos
  fin_cases i
  · exact D.h0'
  · show D.α 1 < 2 * π; linarith [D.α1_lt]
  · show D.α 2 < 2 * π; linarith [D.h2']
  · show D.α 3 < 2 * π; linarith [D.α3_lt]

theorem α_ne (i : Fin 4) : D.α i ≠ π := by
  fin_cases i
  · exact D.h0.ne'
  · exact D.α1_lt.ne
  · exact D.h2'.ne
  · exact D.α3_lt.ne

/-- **The frames of the dart**: at `v_i` the sides `e_{a i}` and `e_{b i}`, `a = (3, 0, 1, 2)`,
`b = id`. -/
def t : StarFrames (Fin 4) where
  α := D.α
  n := D.n
  a := ![3, 0, 1, 2]
  b := id
  α_pos := D.α_pos
  α_lt := D.α_lt
  α_ne := D.α_ne
  unit k := by
    fin_cases k <;>
      simp [n, dartN, dartNuL_dot_self, dartNuR_dot_self, neg_dotProduct, dotProduct_neg]
  gram i := by
    fin_cases i
    · show (-dartNuL D.ℓ D.u) ⬝ᵥ (-dartNuR D.ℓ D.w) = -Real.cos (D.α 0)
      rw [neg_dotProduct, dotProduct_neg, neg_neg, dartNuL_dot_dartNuR]
      exact D.hT'
    · show D.n 1 ⬝ᵥ D.n 0 = -Real.cos (D.α 1)
      simp [n, dartN, dotProduct_neg, dartNuL_dot_dartNuL]
    · show dartNuR D.ℓ (D.w + D.α 3) ⬝ᵥ dartNuL D.ℓ (D.u + D.α 1) = -Real.cos (D.α 2)
      rw [dotProduct_comm, dartNuL_dot_dartNuR]
      exact D.hT
    · show D.n 3 ⬝ᵥ D.n 2 = -Real.cos (D.α 3)
      simp [n, dartN, neg_dotProduct, dartNuR_dot_dartNuR]

@[simp] theorem t_α : D.t.α = D.α := rfl

@[simp] theorem t_n : D.t.n = D.n := rfl

theorem sin_2ℓ : 0 < Real.sin (2 * D.ℓ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [D.hℓ]) (by linarith [D.hℓ'])

theorem sin_u : 0 < Real.sin D.u := Real.sin_pos_of_pos_of_lt_pi D.hu (by linarith [D.hp, D.h1])

theorem sin_w : 0 < Real.sin D.w := Real.sin_pos_of_pos_of_lt_pi D.hw (by linarith [D.hq, D.h3])

theorem sin_p : 0 < Real.sin (D.u + D.α 1) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [D.hu, D.h1]) D.hp

theorem sin_q : 0 < Real.sin (D.w + D.α 3) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [D.hw, D.h3]) D.hq

theorem sin_α1 : 0 < Real.sin (D.α 1) := Real.sin_pos_of_pos_of_lt_pi D.h1 D.α1_lt

theorem sin_α2 : 0 < Real.sin (D.α 2) := Real.sin_pos_of_pos_of_lt_pi D.h2 D.h2'

theorem sin_α3 : 0 < Real.sin (D.α 3) := Real.sin_pos_of_pos_of_lt_pi D.h3 D.α3_lt

theorem sin_α0 : Real.sin (D.α 0) < 0 := sin_neg_of_pi_lt_of_lt_two_pi D.h0 D.h0'

theorem pu : D.u + D.α 1 - D.u = D.α 1 := by ring

theorem qw : D.w + D.α 3 - D.w = D.α 3 := by ring

/-! #### The signs of the sides at the vertices -/

theorem s01 : 0 < (D.t.A 0 *ᵥ D.n 1) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 0))⁻¹ * (D.n 1 ⬝ᵥ D.n 0 ⨯₃ D.n 3)
  rw [n, dartN_tp_0_1, D.pu]
  have := mul_pos (mul_pos D.sin_2ℓ D.sin_w) D.sin_α1
  have := inv_lt_zero.2 D.sin_α0
  nlinarith

theorem s02 : 0 < (D.t.A 0 *ᵥ D.n 2) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 0))⁻¹ * (D.n 2 ⬝ᵥ D.n 0 ⨯₃ D.n 3)
  rw [n, dartN_tp_0_2, D.qw]
  have := mul_pos (mul_pos D.sin_2ℓ D.sin_u) D.sin_α3
  have := inv_lt_zero.2 D.sin_α0
  nlinarith

theorem s12 : 0 < (D.t.A 1 *ᵥ D.n 2) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 1))⁻¹ * (D.n 2 ⬝ᵥ D.n 1 ⨯₃ D.n 0)
  rw [n, dartN_tp_1_2, D.pu]
  have := mul_pos (mul_pos D.sin_α1 D.sin_q) D.sin_2ℓ
  have := inv_pos.2 D.sin_α1
  positivity

theorem s13 : (D.t.A 1 *ᵥ D.n 3) 0 < 0 := by
  rw [StarFrames.A_mulVec_zero]
  show (Real.sin (D.α 1))⁻¹ * (D.n 3 ⬝ᵥ D.n 1 ⨯₃ D.n 0) < 0
  rw [n, dartN_tp_1_3, D.pu]
  have := mul_pos (mul_pos D.sin_α1 D.sin_w) D.sin_2ℓ
  have := inv_pos.2 D.sin_α1
  nlinarith

theorem s20 : 0 < (D.t.A 2 *ᵥ D.n 0) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 2))⁻¹ * (D.n 0 ⬝ᵥ D.n 2 ⨯₃ D.n 1)
  rw [n, dartN_tp_2_0, D.pu]
  have := mul_pos (mul_pos D.sin_2ℓ D.sin_q) D.sin_α1
  have := inv_pos.2 D.sin_α2
  positivity

theorem s23 : 0 < (D.t.A 2 *ᵥ D.n 3) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 2))⁻¹ * (D.n 3 ⬝ᵥ D.n 2 ⨯₃ D.n 1)
  rw [n, dartN_tp_2_3, D.qw]
  have := mul_pos (mul_pos D.sin_2ℓ D.sin_p) D.sin_α3
  have := inv_pos.2 D.sin_α2
  positivity

theorem s31 : 0 < (D.t.A 3 *ᵥ D.n 1) 0 := by
  rw [StarFrames.A_mulVec_zero]
  show 0 < (Real.sin (D.α 3))⁻¹ * (D.n 1 ⬝ᵥ D.n 3 ⨯₃ D.n 2)
  rw [n, dartN_tp_3_1, D.qw]
  have := mul_pos (mul_pos D.sin_α3 D.sin_p) D.sin_2ℓ
  have := inv_pos.2 D.sin_α3
  positivity

theorem s30 : (D.t.A 3 *ᵥ D.n 0) 0 < 0 := by
  rw [StarFrames.A_mulVec_zero]
  show (Real.sin (D.α 3))⁻¹ * (D.n 0 ⬝ᵥ D.n 3 ⨯₃ D.n 2) < 0
  rw [n, dartN_tp_3_0, D.qw]
  have := mul_pos (mul_pos D.sin_α3 D.sin_u) D.sin_2ℓ
  have := inv_pos.2 D.sin_α3
  nlinarith

theorem neg_pos_of {c : Fin 3 → ℝ} {i : Fin 4} (h : (D.t.A i *ᵥ c) 0 < 0) :
    0 < (D.t.A i *ᵥ (-c)) 0 := by
  rw [mulVec_neg, Pi.neg_apply]; linarith

theorem unit_n (k : Fin 4) : D.n k ⬝ᵥ D.n k = 1 := D.t.unit k

theorem unit_neg (k : Fin 4) : (-D.n k) ⬝ᵥ (-D.n k) = 1 := by
  rw [neg_dotProduct, dotProduct_neg, neg_neg]; exact D.unit_n k

/-! #### The dart as a set, its interior, its sides, its charts -/

/-- **The dart** `T ∖ T'`: `{n₁ ≥ 0, n₂ ≥ 0} ∩ ({n₀ ≥ 0} ∪ {n₃ ≥ 0})`. -/
def P : Set Sph2 :=
  {x | 0 ≤ D.n 1 ⬝ᵥ vec x ∧ 0 ≤ D.n 2 ⬝ᵥ vec x ∧ (0 ≤ D.n 0 ⬝ᵥ vec x ∨ 0 ≤ D.n 3 ⬝ᵥ vec x)}

/-- Its interior. -/
def inner (x : Sph2) : Prop :=
  0 < D.n 1 ⬝ᵥ vec x ∧ 0 < D.n 2 ⬝ᵥ vec x ∧ (0 < D.n 0 ⬝ᵥ vec x ∨ 0 < D.n 3 ⬝ᵥ vec x)

/-- Its sides: `e₁₂` and `e₄₁` are the half-sides of their great circles off the other one. -/
def onSide : Fin 4 → Sph2 → Prop :=
  ![fun x => D.n 0 ⬝ᵥ vec x = 0 ∧ D.n 3 ⬝ᵥ vec x ≤ 0, fun x => D.n 1 ⬝ᵥ vec x = 0,
    fun x => D.n 2 ⬝ᵥ vec x = 0, fun x => D.n 3 ⬝ᵥ vec x = 0 ∧ D.n 0 ⬝ᵥ vec x ≤ 0]

/-- The domains of the charts at the vertices. -/
def F : Fin 4 → Sph2 → Prop :=
  ![fun x => 0 < D.n 1 ⬝ᵥ vec x ∧ 0 < D.n 2 ⬝ᵥ vec x,
    fun x => 0 < D.n 2 ⬝ᵥ vec x ∧ D.n 3 ⬝ᵥ vec x < 0,
    fun x => 0 < D.n 0 ⬝ᵥ vec x ∨ 0 < D.n 3 ⬝ᵥ vec x,
    fun x => 0 < D.n 1 ⬝ᵥ vec x ∧ D.n 0 ⬝ᵥ vec x < 0]

/-- Their closures. -/
def Fc : Fin 4 → Sph2 → Prop :=
  ![fun x => 0 ≤ D.n 1 ⬝ᵥ vec x ∧ 0 ≤ D.n 2 ⬝ᵥ vec x,
    fun x => 0 ≤ D.n 2 ⬝ᵥ vec x ∧ D.n 3 ⬝ᵥ vec x ≤ 0,
    fun x => 0 ≤ D.n 0 ⬝ᵥ vec x ∨ 0 ≤ D.n 3 ⬝ᵥ vec x,
    fun x => 0 ≤ D.n 1 ⬝ᵥ vec x ∧ D.n 0 ⬝ᵥ vec x ≤ 0]

theorem fst_ne_P {x : Sph2} (hx : x ∈ D.P) : ((D.t.R 0 • x : Sph2) : Euc3).fst ≠ -1 :=
  D.t.fst_ne_of_dot_nonneg 0 D.s01 hx.1

/-! #### The model: the dart in the stereographic chart at `v_0` -/

/-- The sides read in the chart at `v_0`. -/
def g (k : Fin 4) (v : ℂ) : ℝ := gfun (D.t.A 0 *ᵥ D.n k) v

theorem c3 : D.t.A 0 *ᵥ D.n 3 = ![0, 0, 1] := D.t.A_mulVec_n_a 0

theorem c0 : D.t.A 0 *ᵥ D.n 0 = ![0, Real.sin (D.α 0), -Real.cos (D.α 0)] := D.t.A_mulVec_n_b 0

theorem g3 (v : ℂ) : D.g 3 v = 2 * v.im := by rw [g, c3]; simp [gfun]

theorem g0 (v : ℂ) :
    D.g 0 v = 2 * (Real.sin (D.α 0) * v.re - Real.cos (D.α 0) * v.im) := by
  rw [g, c0]; simp [gfun]; ring

theorem dot_stereoInv (k : Fin 4) (v : ℂ) :
    D.n k ⬝ᵥ vec ((D.t.R 0)⁻¹ • stereoInv v) = D.g k v / (1 + ‖v‖ ^ 2) :=
  D.t.dot_vec_R_inv_stereoInv 0 (D.n k) v

theorem dot_eq_g {x : Sph2} (hS : ((D.t.R 0 • x : Sph2) : Euc3).fst ≠ -1) (k : Fin 4) :
    D.n k ⬝ᵥ vec x = D.g k (stereoFun (D.t.R 0 • x)) / (1 + ‖stereoFun (D.t.R 0 • x)‖ ^ 2) := by
  conv_lhs => rw [D.t.eq_xv_stereo 0 hS]
  exact D.dot_stereoInv k _

omit D in
theorem sign_iff {a b : ℝ} (hb : 0 < b) : (0 ≤ a / b ↔ 0 ≤ a) ∧ (0 < a / b ↔ 0 < a) ∧
    (a / b = 0 ↔ a = 0) ∧ (a / b ≤ 0 ↔ a ≤ 0) := by
  refine ⟨⟨fun h => ?_, fun h => div_nonneg h hb.le⟩, div_pos_iff_of_pos_right hb, ?_, ?_⟩
  · by_contra h'; rw [not_le] at h'; have := div_neg_of_neg_of_pos h' hb; linarith
  · rw [div_eq_zero_iff]; constructor
    · rintro (h | h); exact h; linarith
    · exact Or.inl
  · constructor
    · intro h; by_contra h'; rw [not_le] at h'; have := div_pos h' hb; linarith
    · intro h; exact div_nonpos_of_nonpos_of_nonneg h hb.le

/-- The first convex piece `A = {n₁, n₂, n₀ ≥ 0}`, in the chart. -/
def KA : Set ℂ := {v | 0 ≤ D.g 1 v ∧ 0 ≤ D.g 2 v ∧ 0 ≤ D.g 0 v}

/-- The second convex piece `B = {n₁, n₂, n₃ ≥ 0}`, in the chart. -/
def KB : Set ℂ := {v | 0 ≤ D.g 1 v ∧ 0 ≤ D.g 2 v ∧ 0 ≤ D.g 3 v}

theorem K_eq : {v | (D.t.R 0)⁻¹ • stereoInv v ∈ D.P} = D.KA ∪ D.KB := by
  ext v
  have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  simp only [mem_setOf_eq, P, D.dot_stereoInv, (sign_iff hD).1, KA, KB, mem_union]
  tauto

theorem c_zero_nonneg (k : Fin 4) : 0 ≤ (D.t.A 0 *ᵥ D.n k) 0 := by
  fin_cases k
  · show 0 ≤ (D.t.A 0 *ᵥ D.n 0) 0
    rw [D.c0]; simp
  · exact D.s01.le
  · exact D.s02.le
  · show 0 ≤ (D.t.A 0 *ᵥ D.n 3) 0
    rw [D.c3]; simp

theorem c_unit (k : Fin 4) : (D.t.A 0 *ᵥ D.n k) ⬝ᵥ (D.t.A 0 *ᵥ D.n k) = 1 := by
  rw [D.t.A_dot_A]; exact D.unit_n k

theorem convex_g (k : Fin 4) : Convex ℝ {v : ℂ | 0 ≤ D.g k v} :=
  SphTriangle.convex_gfun_nonneg (D.c_zero_nonneg k)

theorem isClosed_g (k : Fin 4) : IsClosed {v : ℂ | 0 ≤ D.g k v} :=
  isClosed_le continuous_const (continuous_gfun _)

theorem convex_KA : Convex ℝ D.KA :=
  (D.convex_g 1).inter ((D.convex_g 2).inter (D.convex_g 0))

theorem convex_KB : Convex ℝ D.KB :=
  (D.convex_g 1).inter ((D.convex_g 2).inter (D.convex_g 3))

theorem isClosed_KA : IsClosed D.KA :=
  (D.isClosed_g 1).inter ((D.isClosed_g 2).inter (D.isClosed_g 0))

theorem isClosed_KB : IsClosed D.KB :=
  (D.isClosed_g 1).inter ((D.isClosed_g 2).inter (D.isClosed_g 3))

theorem isBounded_g1 : Bornology.IsBounded {v : ℂ | 0 ≤ D.g 1 v} := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ))
    (r := 3 / (D.t.A 0 *ᵥ D.n 1) 0)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact SphPolygon.norm_le_of_gfun_nonneg (D.c_unit 1) D.s01 hv

theorem isBounded_KA : Bornology.IsBounded D.KA := D.isBounded_g1.subset fun _ hv => hv.1

theorem isBounded_KB : Bornology.IsBounded D.KB := D.isBounded_g1.subset fun _ hv => hv.1

/-- **The two pieces have a common interior point**, on the bisector of the kernel at `v_0`. -/
theorem exists_mem_interior : ∃ x₀, x₀ ∈ interior D.KA ∧ x₀ ∈ interior D.KB := by
  set β := D.α 0 / 2
  have hβ0 : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (by
    show 0 < D.α 0 / 2; linarith [D.h0, Real.pi_pos]) (by show D.α 0 / 2 < π; linarith [D.h0'])
  set f : ℝ → ℂ := fun ε => (ε : ℂ) * Complex.exp ((β : ℂ) * Complex.I)
  have hfre : ∀ ε, (f ε).re = ε * Real.cos β := fun ε => by
    simp only [f]; rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hfim : ∀ ε, (f ε).im = ε * Real.sin β := fun ε => by
    simp only [f]; rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hev : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < D.g k (f ε) := by
    intro k
    fin_cases k
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      show 0 < D.g 0 (f ε)
      rw [D.g0, hfre, hfim]
      have : Real.sin (D.α 0) * Real.cos β - Real.cos (D.α 0) * Real.sin β = Real.sin β := by
        rw [← Real.sin_sub]; congr 1; simp only [β]; ring
      nlinarith
    · have hc : 0 < D.g 1 (f 0) := by
        simp only [f, Complex.ofReal_zero, zero_mul, g, gfun, norm_zero, Complex.zero_re,
          Complex.zero_im]
        simp; exact D.s01
      exact ((((continuous_gfun _).comp (by fun_prop : Continuous f)).tendsto 0).eventually
        (lt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
    · have hc : 0 < D.g 2 (f 0) := by
        simp only [f, Complex.ofReal_zero, zero_mul, g, gfun, norm_zero, Complex.zero_re,
          Complex.zero_im]
        simp; exact D.s02
      exact ((((continuous_gfun _).comp (by fun_prop : Continuous f)).tendsto 0).eventually
        (lt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      show 0 < D.g 3 (f ε)
      rw [D.g3, hfim]; positivity
  obtain ⟨ε, hε⟩ := (Filter.eventually_all.2 hev).exists
  set U : Set ℂ := ⋂ k, {v : ℂ | 0 < D.g k v}
  have hUo : IsOpen U := isOpen_iInter_of_finite fun k => isOpen_lt continuous_const
    (continuous_gfun _)
  have hfU : f ε ∈ U := mem_iInter.2 hε
  refine ⟨f ε, interior_maximal (fun v hv => ?_) hUo hfU,
    interior_maximal (fun v hv => ?_) hUo hfU⟩
  · have := mem_iInter.1 hv
    exact ⟨(this 1).le, (this 2).le, (this 0).le⟩
  · have := mem_iInter.1 hv
    exact ⟨(this 1).le, (this 2).le, (this 3).le⟩

theorem exists_eK : ∃ e : ℂ ≃ₜ ℂ, e '' (D.KA ∪ D.KB) = Metric.closedBall 0 1 ∧
    e '' interior (D.KA ∪ D.KB) = Metric.ball 0 1 :=
  exists_homeomorph_union_convex D.convex_KA D.convex_KB D.isClosed_KA D.isClosed_KB
    D.isBounded_KA D.isBounded_KB D.exists_mem_interior.choose_spec.1
    D.exists_mem_interior.choose_spec.2

/-- The homeomorphism of the plane taking the dart onto the closed unit disc. -/
def eK : ℂ ≃ₜ ℂ := D.exists_eK.choose

theorem inner_mem {x : Sph2} (hx : x ∈ D.P) (hi : D.inner x) :
    stereoFun (D.t.R 0 • x) ∈ interior {v | (D.t.R 0)⁻¹ • stereoInv v ∈ D.P} := by
  have hS := D.fst_ne_P hx
  set z := stereoFun (D.t.R 0 • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hk := fun k => D.dot_eq_g hS k
  set U : Set ℂ := {v | 0 < D.g 1 v ∧ 0 < D.g 2 v ∧ (0 < D.g 0 v ∨ 0 < D.g 3 v)}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_gfun _)).inter
      ((isOpen_lt continuous_const (continuous_gfun _)).inter
        ((isOpen_lt continuous_const (continuous_gfun _)).union
          (isOpen_lt continuous_const (continuous_gfun _))))
  have hUK : U ⊆ {v | (D.t.R 0)⁻¹ • stereoInv v ∈ D.P} := by
    rw [D.K_eq]
    rintro v ⟨h1, h2, h3 | h3⟩
    · exact Or.inl ⟨h1.le, h2.le, h3.le⟩
    · exact Or.inr ⟨h1.le, h2.le, h3.le⟩
  refine interior_maximal hUK hUo ?_
  obtain ⟨h1, h2, h3⟩ := hi
  rw [hk, ((sign_iff hD).2.1)] at h1 h2
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h3 | h3
  · rw [hk, ((sign_iff hD).2.1)] at h3; exact Or.inl h3
  · rw [hk, ((sign_iff hD).2.1)] at h3; exact Or.inr h3

theorem exists_side {x : Sph2} (hx : x ∈ D.P) (hi : ¬ D.inner x) : ∃ k, D.onSide k x := by
  obtain ⟨h1, h2, h3⟩ := hx
  by_cases e1 : D.n 1 ⬝ᵥ vec x = 0
  · exact ⟨1, e1⟩
  by_cases e2 : D.n 2 ⬝ᵥ vec x = 0
  · exact ⟨2, e2⟩
  have p1 : 0 < D.n 1 ⬝ᵥ vec x := lt_of_le_of_ne h1 (Ne.symm e1)
  have p2 : 0 < D.n 2 ⬝ᵥ vec x := lt_of_le_of_ne h2 (Ne.symm e2)
  have h03 : D.n 0 ⬝ᵥ vec x ≤ 0 ∧ D.n 3 ⬝ᵥ vec x ≤ 0 := by
    by_contra hc
    rw [not_and_or, not_le, not_le] at hc
    exact hi ⟨p1, p2, hc⟩
  rcases h3 with h3 | h3
  · exact ⟨0, le_antisymm h03.1 h3, h03.2⟩
  · exact ⟨3, le_antisymm h03.2 h3, h03.1⟩

theorem side_notMem {x : Sph2} (hx : x ∈ D.P) {k : Fin 4} (hk : D.onSide k x) :
    stereoFun (D.t.R 0 • x) ∉ interior {v | (D.t.R 0)⁻¹ • stereoInv v ∈ D.P} := by
  have hS := D.fst_ne_P hx
  set z := stereoFun (D.t.R 0 • x)
  have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hkg := fun k => D.dot_eq_g hS k
  rw [D.K_eq]
  have hnotch : D.KA ∪ D.KB ⊆ {v | 0 ≤ v.im ∨
      0 ≤ Real.sin (D.α 0) * v.re - Real.cos (D.α 0) * v.im} := by
    rintro v (⟨-, -, hv⟩ | ⟨-, -, hv⟩)
    · rw [D.g0] at hv; right; linarith
    · rw [D.g3] at hv; left; linarith
  fin_cases k
  · obtain ⟨e0, e3⟩ : D.n 0 ⬝ᵥ vec x = 0 ∧ D.n 3 ⬝ᵥ vec x ≤ 0 := hk
    rw [hkg, (sign_iff hD).2.2.1, D.g0] at e0
    rw [hkg, (sign_iff hD).2.2.2, D.g3] at e3
    exact notMem_interior_notch D.h0 D.h0' hnotch (by linarith) (by linarith)
  · have e1 : D.n 1 ⬝ᵥ vec x = 0 := hk
    rw [hkg, (sign_iff hD).2.2.1] at e1
    exact notMem_interior_of_subset_gfun (D.c_zero_nonneg 1) (D.c_unit 1)
      (by rintro v (⟨hv, -⟩ | ⟨hv, -⟩) <;> exact hv) e1.le
  · have e2 : D.n 2 ⬝ᵥ vec x = 0 := hk
    rw [hkg, (sign_iff hD).2.2.1] at e2
    exact notMem_interior_of_subset_gfun (D.c_zero_nonneg 2) (D.c_unit 2)
      (by rintro v (⟨-, hv, -⟩ | ⟨-, hv, -⟩) <;> exact hv) e2.le
  · obtain ⟨e3, e0⟩ : D.n 3 ⬝ᵥ vec x = 0 ∧ D.n 0 ⬝ᵥ vec x ≤ 0 := hk
    rw [hkg, (sign_iff hD).2.2.1, D.g3] at e3
    rw [hkg, (sign_iff hD).2.2.2, D.g0] at e0
    exact notMem_interior_notch D.h0 D.h0' hnotch (by linarith) (by linarith)

end DartParams

end DartModel

section DartCharts

namespace DartParams

variable (D : DartParams)

/-! #### The charts of the dart at its vertices -/

theorem isOpen_F (i : Fin 4) : IsOpen {x | D.F i x} := by
  have hc : ∀ k, Continuous fun x : Sph2 => D.n k ⬝ᵥ vec x := fun k => continuous_dot_vec _
  match i with
  | 0 => exact (isOpen_lt continuous_const (hc 1)).inter (isOpen_lt continuous_const (hc 2))
  | 1 => exact (isOpen_lt continuous_const (hc 2)).inter (isOpen_lt (hc 3) continuous_const)
  | 2 => exact (isOpen_lt continuous_const (hc 0)).union (isOpen_lt continuous_const (hc 3))
  | 3 => exact (isOpen_lt continuous_const (hc 1)).inter (isOpen_lt (hc 0) continuous_const)

theorem isClosed_Fc (i : Fin 4) : IsClosed {x | D.Fc i x} := by
  have hc : ∀ k, Continuous fun x : Sph2 => D.n k ⬝ᵥ vec x := fun k => continuous_dot_vec _
  match i with
  | 0 => exact (isClosed_le continuous_const (hc 1)).inter (isClosed_le continuous_const (hc 2))
  | 1 => exact (isClosed_le continuous_const (hc 2)).inter (isClosed_le (hc 3) continuous_const)
  | 2 => exact (isClosed_le continuous_const (hc 0)).union (isClosed_le continuous_const (hc 3))
  | 3 => exact (isClosed_le continuous_const (hc 1)).inter (isClosed_le (hc 0) continuous_const)

theorem F_Fc (i : Fin 4) (x : Sph2) (h : D.F i x) : D.Fc i x := by
  match i with
  | 0 => exact ⟨h.1.le, h.2.le⟩
  | 1 => exact ⟨h.1.le, h.2.le⟩
  | 2 => exact h.imp le_of_lt le_of_lt
  | 3 => exact ⟨h.1.le, h.2.le⟩

theorem Fc_mem (i : Fin 4) (h : ℂ) (hF : D.Fc i (D.t.xv i h)) : D.t.xv i h ∈ D.P := by
  match i with
  | 0 =>
    obtain ⟨h1, h2⟩ := hF
    exact ⟨h1, h2, (D.t.xv_sector_reflex (i := 0) D.h0 h).symm⟩
  | 1 =>
    obtain ⟨h2, -⟩ := hF
    obtain ⟨ha, hb⟩ := D.t.xv_sector (i := 1) D.α1_lt h
    exact ⟨hb, h2, Or.inl ha⟩
  | 2 =>
    obtain ⟨ha, hb⟩ := D.t.xv_sector (i := 2) D.h2' h
    exact ⟨ha, hb, hF⟩
  | 3 =>
    obtain ⟨h1, -⟩ := hF
    obtain ⟨ha, hb⟩ := D.t.xv_sector (i := 3) D.α3_lt h
    exact ⟨h1, ha, Or.inr hb⟩

theorem exists_up (i : Fin 4) (x : Sph2) (hx : x ∈ D.P) (hF : D.F i x) :
    ∃ h, D.t.xv i h = x ∧ 0 ≤ h.im := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  match i with
  | 0 =>
    exact D.t.exists_xv_eq_reflex (i := 0) D.h0 (D.t.fst_ne_of_dot_nonneg 0 D.s01 hx1) hx3.symm
  | 1 =>
    have h0 : 0 ≤ D.n 0 ⬝ᵥ vec x := hx3.resolve_right (not_le.2 hF.2)
    exact D.t.exists_xv_eq (i := 1) D.α1_lt (D.t.fst_ne_of_dot_nonneg 1 D.s12 hx2) h0 hx1
  | 2 =>
    have hS : ((D.t.R 2 • x : Sph2) : Euc3).fst ≠ -1 := by
      rcases hF with h | h
      · exact D.t.fst_ne_of_dot_nonneg 2 D.s20 h.le
      · exact D.t.fst_ne_of_dot_nonneg 2 D.s23 h.le
    exact D.t.exists_xv_eq (i := 2) D.h2' hS hx1 hx2
  | 3 =>
    have h3 : 0 ≤ D.n 3 ⬝ᵥ vec x := hx3.resolve_left (not_le.2 hF.2)
    exact D.t.exists_xv_eq (i := 3) D.α3_lt (D.t.fst_ne_of_dot_nonneg 3 D.s31 hx1) hx2 h3

theorem exists_down (i : Fin 4) (x : Sph2) (hx : x ∈ D.P) (hF : D.F i x) (hi : D.inner x) :
    ∃ h, D.t.xv i h = x ∧ h.im < 0 := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hi1, hi2, hi3⟩ := hi
  match i with
  | 0 =>
    exact D.t.exists_xv_eq_reflex_neg (i := 0) D.h0 (D.t.fst_ne_of_dot_nonneg 0 D.s01 hx1)
      hi3.symm
  | 1 =>
    have h0 : 0 < D.n 0 ⬝ᵥ vec x := hi3.resolve_right (not_lt.2 hF.2.le)
    exact D.t.exists_xv_eq_neg (i := 1) D.α1_lt (D.t.fst_ne_of_dot_nonneg 1 D.s12 hx2) h0 hi1
  | 2 =>
    have hS : ((D.t.R 2 • x : Sph2) : Euc3).fst ≠ -1 := by
      rcases hF with h | h
      · exact D.t.fst_ne_of_dot_nonneg 2 D.s20 h.le
      · exact D.t.fst_ne_of_dot_nonneg 2 D.s23 h.le
    exact D.t.exists_xv_eq_neg (i := 2) D.h2' hS hi1 hi2
  | 3 =>
    have h3 : 0 < D.n 3 ⬝ᵥ vec x := hi3.resolve_left (not_lt.2 hF.2.le)
    exact D.t.exists_xv_eq_neg (i := 3) D.α3_lt (D.t.fst_ne_of_dot_nonneg 3 D.s31 hx1) hi2 h3

theorem side_eq (i k : Fin 4) (h : ℂ) (h0 : h ≠ 0) (hF : D.F i (D.t.xv i h))
    (hk : D.onSide k (D.t.xv i h)) :
    (k = D.t.a i ∧ h.im = 0 ∧ 0 < h.re) ∨ (k = D.t.b i ∧ h.im = 0 ∧ h.re < 0) := by
  match i, k with
  | 0, 0 => exact Or.inr ⟨rfl, D.t.xv_side_b_reflex (i := 0) D.h0 h0 hk.1 hk.2⟩
  | 0, 1 => exact absurd (hk : D.n 1 ⬝ᵥ vec (D.t.xv 0 h) = 0) hF.1.ne'
  | 0, 2 => exact absurd (hk : D.n 2 ⬝ᵥ vec (D.t.xv 0 h) = 0) hF.2.ne'
  | 0, 3 => exact Or.inl ⟨rfl, D.t.xv_side_a_reflex (i := 0) D.h0 h0 hk.1 hk.2⟩
  | 1, 0 => exact Or.inl ⟨rfl, D.t.xv_side_a (i := 1) D.α1_lt h0 hk.1⟩
  | 1, 1 => exact Or.inr ⟨rfl, D.t.xv_side_b (i := 1) D.α1_lt h0 hk⟩
  | 1, 2 => exact absurd (hk : D.n 2 ⬝ᵥ vec (D.t.xv 1 h) = 0) hF.1.ne'
  | 1, 3 => exact absurd hk.1 hF.2.ne
  | 2, 0 =>
    exfalso
    obtain ⟨e0, e3⟩ := hk
    rcases hF with h' | h' <;> linarith
  | 2, 1 => exact Or.inl ⟨rfl, D.t.xv_side_a (i := 2) D.h2' h0 hk⟩
  | 2, 2 => exact Or.inr ⟨rfl, D.t.xv_side_b (i := 2) D.h2' h0 hk⟩
  | 2, 3 =>
    exfalso
    obtain ⟨e3, e0⟩ := hk
    rcases hF with h' | h' <;> linarith
  | 3, 0 => exact absurd hk.1 hF.2.ne
  | 3, 1 => exact absurd (hk : D.n 1 ⬝ᵥ vec (D.t.xv 3 h) = 0) hF.1.ne'
  | 3, 2 => exact Or.inl ⟨rfl, D.t.xv_side_a (i := 3) D.α3_lt h0 hk⟩
  | 3, 3 => exact Or.inr ⟨rfl, D.t.xv_side_b (i := 3) D.α3_lt h0 hk.1⟩

theorem not_inner_of_real (i : Fin 4) (h : ℂ) (him : h.im = 0) (hF : D.Fc i (D.t.xv i h)) :
    ¬ D.inner (D.t.xv i h) := by
  match i with
  | 0 =>
    rintro ⟨-, -, hi3⟩
    rcases le_total 0 h.re with hre | hre
    · obtain ⟨e3, e0⟩ : D.n 3 ⬝ᵥ vec (D.t.xv 0 h) = 0 ∧ D.n 0 ⬝ᵥ vec (D.t.xv 0 h) ≤ 0 :=
        D.t.xv_real_a_reflex (i := 0) D.h0 him hre
      rcases hi3 with h' | h' <;> linarith
    · obtain ⟨e0, e3⟩ : D.n 0 ⬝ᵥ vec (D.t.xv 0 h) = 0 ∧ D.n 3 ⬝ᵥ vec (D.t.xv 0 h) ≤ 0 :=
        D.t.xv_real_b_reflex (i := 0) D.h0 him hre
      rcases hi3 with h' | h' <;> linarith
  | 1 =>
    rintro ⟨hi1, -, hi3⟩
    have e3 : D.n 3 ⬝ᵥ vec (D.t.xv 1 h) ≤ 0 := hF.2
    rcases le_total 0 h.re with hre | hre
    · have e0 : D.n 0 ⬝ᵥ vec (D.t.xv 1 h) = 0 := D.t.xv_real_a 1 him hre
      rcases hi3 with h' | h' <;> linarith
    · have e1 : D.n 1 ⬝ᵥ vec (D.t.xv 1 h) = 0 := D.t.xv_real_b 1 him hre
      linarith
  | 2 =>
    rintro ⟨hi1, hi2, -⟩
    rcases le_total 0 h.re with hre | hre
    · have e1 : D.n 1 ⬝ᵥ vec (D.t.xv 2 h) = 0 := D.t.xv_real_a 2 him hre
      linarith
    · have e2 : D.n 2 ⬝ᵥ vec (D.t.xv 2 h) = 0 := D.t.xv_real_b 2 him hre
      linarith
  | 3 =>
    rintro ⟨-, hi2, hi3⟩
    have e0 : D.n 0 ⬝ᵥ vec (D.t.xv 3 h) ≤ 0 := hF.2
    rcases le_total 0 h.re with hre | hre
    · have e2 : D.n 2 ⬝ᵥ vec (D.t.xv 3 h) = 0 := D.t.xv_real_a 3 him hre
      linarith
    · have e3 : D.n 3 ⬝ᵥ vec (D.t.xv 3 h) = 0 := D.t.xv_real_b 3 him hre
      rcases hi3 with h' | h' <;> linarith

theorem inner_of_im (i : Fin 4) (h : ℂ) (him : h.im ≠ 0) (hF : D.F i (D.t.xv i h)) :
    D.inner (D.t.xv i h) := by
  match i with
  | 0 => exact ⟨hF.1, hF.2, (D.t.xv_sector_reflex_strict (i := 0) D.h0 him).symm⟩
  | 1 =>
    obtain ⟨ha, hb⟩ := D.t.xv_sector_strict (i := 1) D.α1_lt him
    exact ⟨hb, hF.1, Or.inl ha⟩
  | 2 =>
    obtain ⟨ha, hb⟩ := D.t.xv_sector_strict (i := 2) D.h2' him
    exact ⟨ha, hb, hF⟩
  | 3 =>
    obtain ⟨ha, hb⟩ := D.t.xv_sector_strict (i := 3) D.α3_lt him
    exact ⟨hF.1, ha, Or.inr hb⟩

theorem F_vertex (i : Fin 4) : D.F i (D.t.vertex i) := by
  match i with
  | 0 =>
    show 0 < D.n 1 ⬝ᵥ vec (D.t.vertex 0) ∧ 0 < D.n 2 ⬝ᵥ vec (D.t.vertex 0)
    rw [D.t.dot_vertex, D.t.dot_vertex]; exact ⟨D.s01, D.s02⟩
  | 1 =>
    show 0 < D.n 2 ⬝ᵥ vec (D.t.vertex 1) ∧ D.n 3 ⬝ᵥ vec (D.t.vertex 1) < 0
    rw [D.t.dot_vertex, D.t.dot_vertex]; exact ⟨D.s12, D.s13⟩
  | 2 =>
    show 0 < D.n 0 ⬝ᵥ vec (D.t.vertex 2) ∨ 0 < D.n 3 ⬝ᵥ vec (D.t.vertex 2)
    rw [D.t.dot_vertex]; exact Or.inl D.s20
  | 3 =>
    show 0 < D.n 1 ⬝ᵥ vec (D.t.vertex 3) ∧ D.n 0 ⬝ᵥ vec (D.t.vertex 3) < 0
    rw [D.t.dot_vertex, D.t.dot_vertex]; exact ⟨D.s31, D.s30⟩

theorem isBounded_Fc (i : Fin 4) : Bornology.IsBounded {h | D.Fc i (D.t.xv i h)} := by
  match i with
  | 0 => exact (D.t.isBounded_xv 0 (D.unit_n 1) D.s01).subset fun h hh => hh.1
  | 1 => exact (D.t.isBounded_xv 1 (D.unit_n 2) D.s12).subset fun h hh => hh.1
  | 2 => exact ((D.t.isBounded_xv 2 (D.unit_n 0) D.s20).union
      (D.t.isBounded_xv 2 (D.unit_n 3) D.s23)).subset fun h hh => hh
  | 3 => exact (D.t.isBounded_xv 3 (D.unit_n 1) D.s31).subset fun h hh => hh.1

theorem starConvex_F (i : Fin 4) : StarConvex ℝ 0 {h | D.F i (D.t.xv i h)} := by
  match i with
  | 0 => exact (D.t.starConvex_xv 0 D.s01).inter (D.t.starConvex_xv 0 D.s02)
  | 1 =>
    have e : {h | D.F 1 (D.t.xv 1 h)} =
        {h | 0 < D.n 2 ⬝ᵥ vec (D.t.xv 1 h)} ∩ {h | 0 < (-D.n 3) ⬝ᵥ vec (D.t.xv 1 h)} := by
      ext h
      simp only [mem_setOf_eq, mem_inter_iff, neg_dotProduct, neg_pos]
      rfl
    rw [e]
    exact (D.t.starConvex_xv 1 D.s12).inter (D.t.starConvex_xv 1 (D.neg_pos_of D.s13))
  | 2 => exact (D.t.starConvex_xv 2 D.s20).union (D.t.starConvex_xv 2 D.s23)
  | 3 =>
    have e : {h | D.F 3 (D.t.xv 3 h)} =
        {h | 0 < D.n 1 ⬝ᵥ vec (D.t.xv 3 h)} ∩ {h | 0 < (-D.n 0) ⬝ᵥ vec (D.t.xv 3 h)} := by
      ext h
      simp only [mem_setOf_eq, mem_inter_iff, neg_dotProduct, neg_pos]
      rfl
    rw [e]
    exact (D.t.starConvex_xv 3 D.s31).inter (D.t.starConvex_xv 3 (D.neg_pos_of D.s30))

/-- The pairings of `n₀` and `n₃` with the vertices. -/
theorem vertex_pairings :
    D.n 0 ⬝ᵥ vec (D.t.vertex 0) = 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex 0) = 0 ∧
    D.n 0 ⬝ᵥ vec (D.t.vertex 1) = 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex 1) < 0 ∧
    0 < D.n 0 ⬝ᵥ vec (D.t.vertex 2) ∧ 0 < D.n 3 ⬝ᵥ vec (D.t.vertex 2) ∧
    D.n 0 ⬝ᵥ vec (D.t.vertex 3) < 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex 3) = 0 := by
  refine ⟨D.t.dot_vertex_b 0, D.t.dot_vertex_a 0, D.t.dot_vertex_a 1, ?_, ?_, ?_, ?_,
    D.t.dot_vertex_b 3⟩
  · rw [D.t.dot_vertex]; exact D.s13
  · rw [D.t.dot_vertex]; exact D.s20
  · rw [D.t.dot_vertex]; exact D.s23
  · rw [D.t.dot_vertex]; exact D.s30

theorem vertex_inj : Injective D.t.vertex := by
  obtain ⟨a0, a3, b0, b3, c0, c3, d0, d3⟩ := D.vertex_pairings
  have key : ∀ i : Fin 4,
      (D.n 0 ⬝ᵥ vec (D.t.vertex i) = 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex i) = 0 ∧ i = 0) ∨
      (D.n 0 ⬝ᵥ vec (D.t.vertex i) = 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex i) < 0 ∧ i = 1) ∨
      (0 < D.n 0 ⬝ᵥ vec (D.t.vertex i) ∧ 0 < D.n 3 ⬝ᵥ vec (D.t.vertex i) ∧ i = 2) ∨
      (D.n 0 ⬝ᵥ vec (D.t.vertex i) < 0 ∧ D.n 3 ⬝ᵥ vec (D.t.vertex i) = 0 ∧ i = 3) := by
    intro i
    match i with
    | 0 => exact Or.inl ⟨a0, a3, rfl⟩
    | 1 => exact Or.inr (Or.inl ⟨b0, b3, rfl⟩)
    | 2 => exact Or.inr (Or.inr (Or.inl ⟨c0, c3, rfl⟩))
    | 3 => exact Or.inr (Or.inr (Or.inr ⟨d0, d3, rfl⟩))
  intro i j hij
  have ki := key i
  rw [hij] at ki
  rcases ki with ⟨x0, x3, rfl⟩ | ⟨x0, x3, rfl⟩ | ⟨x0, x3, rfl⟩ | ⟨x0, x3, rfl⟩ <;>
  rcases key j with ⟨y0, y3, rfl⟩ | ⟨y0, y3, rfl⟩ | ⟨y0, y3, rfl⟩ | ⟨y0, y3, rfl⟩ <;>
  first | rfl | (exfalso; linarith)

theorem cover (x : Sph2) (hx : x ∈ D.P) : ∃ i, D.F i x := by
  by_cases h1 : 0 < D.n 1 ⬝ᵥ vec x ∧ 0 < D.n 2 ⬝ᵥ vec x
  · exact ⟨0, h1⟩
  by_cases h2 : 0 < D.n 0 ⬝ᵥ vec x ∨ 0 < D.n 3 ⬝ᵥ vec x
  · exact ⟨2, h2⟩
  obtain ⟨hx1, hx2, hx3⟩ := hx
  rw [not_or, not_lt, not_lt] at h2
  have e12 : D.n 1 ⬝ᵥ vec x = 0 ∨ D.n 2 ⬝ᵥ vec x = 0 := by
    by_cases e : D.n 1 ⬝ᵥ vec x = 0
    · exact Or.inl e
    · right
      have p1 : 0 < D.n 1 ⬝ᵥ vec x := lt_of_le_of_ne hx1 (Ne.symm e)
      have : ¬ 0 < D.n 2 ⬝ᵥ vec x := fun hp => h1 ⟨p1, hp⟩
      linarith
  have e03 : D.n 0 ⬝ᵥ vec x = 0 ∨ D.n 3 ⬝ᵥ vec x = 0 := by
    rcases hx3 with h | h
    · exact Or.inl (le_antisymm h2.1 h)
    · exact Or.inr (le_antisymm h2.2 h)
  have hx0 : vec x ≠ 0 := fun e => by
    have := vec_dot_self x; rw [e, dotProduct_zero] at this; exact zero_ne_one this
  have hsl : ∀ {a b c : ℝ}, 0 < a → 0 < b → 0 < c → 0 < a * b * c := fun ha hb hc => by
    positivity
  rcases e12 with e1 | e2 <;> rcases e03 with e0 | e3
  · -- at `v_1`
    obtain ⟨hl2, hsq⟩ := D.t.dot_eq_of_dot_a_b 1 (x := x) e0 e1 (D.n 2)
    have hl3 := (D.t.dot_eq_of_dot_a_b 1 (x := x) e0 e1 (D.n 3)).1
    set lam := (D.t.A 1 *ᵥ vec x) 0
    rw [D.t.dot_vertex] at hl2 hl3
    have hlam : lam = 1 := by
      have h0 : 0 ≤ lam := by
        by_contra h; rw [not_le] at h
        have := mul_neg_of_neg_of_pos h D.s12; linarith
      nlinarith
    rw [hlam, one_mul] at hl2 hl3
    refine ⟨1, ?_, ?_⟩
    · show 0 < D.n 2 ⬝ᵥ vec x; rw [hl2]; exact D.s12
    · show D.n 3 ⬝ᵥ vec x < 0; rw [hl3]; exact D.s13
  · exfalso
    refine hx0 (eq_zero_of_dot_cross (a := D.n 1) (b := D.n 3) (c := D.n 0) (d := D.n 2) e1 e3
      ?_ ?_ h2.1 hx2)
    · rw [n, dartN_tp_c1, D.pu]; exact hsl D.sin_2ℓ D.sin_w D.sin_α1
    · rw [n, dartN_tp_c2, D.qw]; exact hsl D.sin_2ℓ D.sin_p D.sin_α3
  · exfalso
    refine hx0 (eq_zero_of_dot_cross (a := D.n 0) (b := D.n 2) (c := D.n 3) (d := D.n 1) e0 e2
      ?_ ?_ h2.2 hx1)
    · rw [n, dartN_tp_c3, D.qw]; exact hsl D.sin_2ℓ D.sin_u D.sin_α3
    · rw [n, dartN_tp_c4, D.pu]; exact hsl D.sin_2ℓ D.sin_q D.sin_α1
  · -- at `v_3`
    obtain ⟨hl1, hsq⟩ := D.t.dot_eq_of_dot_a_b 3 (x := x) e2 e3 (D.n 1)
    have hl0 := (D.t.dot_eq_of_dot_a_b 3 (x := x) e2 e3 (D.n 0)).1
    set lam := (D.t.A 3 *ᵥ vec x) 0
    rw [D.t.dot_vertex] at hl1 hl0
    have hlam : lam = 1 := by
      have h0 : 0 ≤ lam := by
        by_contra h; rw [not_le] at h
        have := mul_neg_of_neg_of_pos h D.s31; linarith
      nlinarith
    rw [hlam, one_mul] at hl1 hl0
    refine ⟨3, ?_, ?_⟩
    · show 0 < D.n 1 ⬝ᵥ vec x; rw [hl1]; exact D.s31
    · show D.n 0 ⬝ᵥ vec x < 0; rw [hl0]; exact D.s30

/-- **The dart, with its charts**: the data of its double. -/
def polygon : StarPolygon D.t where
  P := D.P
  inner := D.inner
  onSide := D.onSide
  F := D.F
  Fc := D.Fc
  o := 0
  eK := D.eK
  fst_ne _ hx := D.fst_ne_P hx
  eK_image := by rw [D.K_eq]; exact D.exists_eK.choose_spec.1
  eK_interior := by rw [D.K_eq]; exact D.exists_eK.choose_spec.2
  inner_mem _ hx hi := D.inner_mem hx hi
  exists_side _ hx hi := D.exists_side hx hi
  side_notMem _ hx _ hk := D.side_notMem hx hk
  isOpen_F := D.isOpen_F
  isClosed_Fc := D.isClosed_Fc
  F_Fc := D.F_Fc
  Fc_mem := D.Fc_mem
  exists_up := D.exists_up
  exists_down := D.exists_down
  side_eq := D.side_eq
  not_inner_of_real := D.not_inner_of_real
  inner_of_im := D.inner_of_im
  F_vertex := D.F_vertex
  isBounded_Fc := D.isBounded_Fc
  starConvex_F := D.starConvex_F
  vertex_inj := D.vertex_inj
  cover := D.cover

/-- **The double of a dart is a cone sphere with angles `2α_i`.** -/
theorem exists_isConeSphere :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M (fun i => 2 * D.α i) p :=
  D.polygon.exists_isConeSphere

end DartParams

end DartCharts

section DartMain

/-! ### The dart exists: the intermediate value theorem on a segment -/

/-- `cos a < cos b` from `|b| < a ≤ π`. -/
theorem cos_lt_cos_of_abs_lt {a b : ℝ} (ha : a ≤ π) (hb : |b| < a) : Real.cos a < Real.cos b := by
  rw [← Real.cos_abs b]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg b) ha hb

/-- The base angle of `T'` at `v₂` along the segment. -/
def dartU (ε δ t : ℝ) : ℝ := ε / 2 + t * (ε / 2 + δ)

/-- The base angle of `T'` at `v₄` along the segment. -/
def dartW (ε δ t : ℝ) : ℝ := ε / 2 + t * (δ - ε / 2)

/-- `cos L` read off `T'` (apex angle `π − ε`). -/
def dartFu (ε u w : ℝ) : ℝ := (Real.cos u * Real.cos w - Real.cos ε) / (Real.sin u * Real.sin w)

/-- `cos L` read off `T` (apex angle `γ`, base angles `p`, `q`). -/
def dartFt (γ p q : ℝ) : ℝ := (Real.cos p * Real.cos q + Real.cos γ) / (Real.sin p * Real.sin q)

theorem dartU_bounds {ε δ a t : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (h : ε + δ + a < π)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < dartU ε δ t ∧ dartU ε δ t + a < π := by
  have h1 : 0 ≤ t * (ε / 2 + δ) := mul_nonneg ht.1 (by positivity)
  have h2 : t * (ε / 2 + δ) ≤ ε / 2 + δ := mul_le_of_le_one_left (by positivity) ht.2
  unfold dartU; constructor <;> linarith

theorem dartW_bounds {ε δ a : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (h1 : ε / 2 + a < π)
    (h2 : δ + a < π) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < dartW ε δ t ∧ dartW ε δ t + a < π := by
  have e : dartW ε δ t = (1 - t) * (ε / 2) + t * δ := by unfold dartW; ring
  have a1 : 0 ≤ (1 - t) * (ε / 2) := mul_nonneg (sub_nonneg.2 ht.2) (by positivity)
  have a2 : 0 ≤ t * δ := mul_nonneg ht.1 hδ.le
  rw [e]
  constructor
  · rcases le_or_gt t (1 / 2) with h | h
    · have : ε / 4 ≤ (1 - t) * (ε / 2) := by nlinarith
      linarith
    · have : δ / 2 < t * δ := by nlinarith
      linarith
  · have b1 : (1 - t) * (ε / 2) ≤ (1 - t) * (π - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 ht.2)
    have b2 : t * δ ≤ t * (π - a) := mul_le_mul_of_nonneg_left (by linarith) ht.1
    rcases le_or_gt t (1 / 2) with h | h
    · have b1' : (1 - t) * (ε / 2) < (1 - t) * (π - a) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      nlinarith
    · have b2' : t * δ < t * (π - a) := mul_lt_mul_of_pos_left (by linarith) (by linarith)
      nlinarith

/-- **A dart with prescribed angles exists.** With `ε = α_0 − π`, the base angles `(u, w)` of
`T'` run along the segment from `(ε/2, ε/2)` (where `T'` is infinitesimal: `cos L = 1`) to
`(ε + δ, δ)` (where `T'` is a lune: `cos L = −1`), while `T`, of base angles `(u + α_1, w + α_3)`
and apex angle `α_2`, stays a triangle; the two values of `cos L` cross. -/
theorem exists_dartParams (α : Fin 4 → ℝ) (h0 : π < α 0) (h0' : α 0 < 2 * π)
    (h1 : 0 < α 1) (h2 : 0 < α 2) (h3 : 0 < α 3) (h2' : α 2 < π)
    (h01 : α 0 + α 1 < 2 * π) (h03 : α 0 + α 3 < 2 * π) (hsum : 2 * π < α 0 + α 1 + α 2 + α 3)
    (h013 : α 0 + α 1 + α 3 < 2 * π + α 2) (h012 : α 0 + α 1 + α 2 < 2 * π + α 3)
    (h23 : α 2 + α 3 < α 0 + α 1) : ∃ D : DartParams, D.α = α := by
  have hπ := Real.pi_pos
  obtain ⟨ε, hε⟩ : ∃ ε, ε = α 0 - π := ⟨_, rfl⟩
  have hε0 : 0 < ε := by linarith
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ ε + δ + α 1 < π ∧ δ + α 3 < π ∧
      ε + 2 * δ < π := by
    have hm1 : min (min (π - ε - α 1) (π - α 3)) (π - ε) ≤ π - ε - α 1 :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hm2 : min (min (π - ε - α 1) (π - α 3)) (π - ε) ≤ π - α 3 :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hm3 : min (min (π - ε - α 1) (π - α 3)) (π - ε) ≤ π - ε := min_le_right _ _
    have hm0 : 0 < min (min (π - ε - α 1) (π - α 3)) (π - ε) :=
      lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    exact ⟨min (min (π - ε - α 1) (π - α 3)) (π - ε) / 4, by linarith, by linarith,
      by linarith, by linarith⟩
  have hW1 : ε / 2 + α 3 < π := by linarith
  have hsin : ∀ x, 0 < x → x < π → 0 < Real.sin x := fun x h1 h2 =>
    Real.sin_pos_of_pos_of_lt_pi h1 h2
  set G : ℝ → ℝ := fun t => dartFt (α 2) (dartU ε δ t + α 1) (dartW ε δ t + α 3) -
    dartFu ε (dartU ε δ t) (dartW ε δ t) with hG
  have hcont : ContinuousOn G (Icc 0 1) := by
    have cU : Continuous (dartU ε δ) := by unfold dartU; fun_prop
    have cW : Continuous (dartW ε δ) := by unfold dartW; fun_prop
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
        (Continuous.continuousOn (by fun_prop)) fun t ht => ?_
      obtain ⟨u1, u2⟩ := dartU_bounds hε0 hδ0 hδ1 ht
      obtain ⟨w1, w2⟩ := dartW_bounds hε0 hδ0 hW1 hδ2 ht
      exact (mul_pos (hsin _ (by linarith) u2) (hsin _ (by linarith) w2)).ne'
    · refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
        (Continuous.continuousOn (by fun_prop)) fun t ht => ?_
      obtain ⟨u1, u2⟩ := dartU_bounds hε0 hδ0 hδ1 ht
      obtain ⟨w1, w2⟩ := dartW_bounds hε0 hδ0 hW1 hδ2 ht
      exact (mul_pos (hsin _ u1 (by linarith)) (hsin _ w1 (by linarith))).ne'
  -- at `t = 0`
  have hu0 : dartU ε δ 0 = ε / 2 := by unfold dartU; ring
  have hw0 : dartW ε δ 0 = ε / 2 := by unfold dartW; ring
  have hFu0 : dartFu ε (ε / 2) (ε / 2) = 1 := by
    have hs : 0 < Real.sin (ε / 2) := hsin _ (by linarith) (by linarith)
    have hc : Real.cos ε = Real.cos (ε / 2) ^ 2 - Real.sin (ε / 2) ^ 2 := by
      have e1 : Real.cos ε = 2 * Real.cos (ε / 2) ^ 2 - 1 := by
        rw [← Real.cos_two_mul]; congr 1; ring
      have e2 := Real.sin_sq_add_cos_sq (ε / 2)
      linarith
    unfold dartFu
    rw [hc, div_eq_one_iff_eq (by positivity)]; ring
  have hFt0 : dartFt (α 2) (ε / 2 + α 1) (ε / 2 + α 3) < 1 := by
    have hp := hsin (ε / 2 + α 1) (by linarith) (by linarith)
    have hq := hsin (ε / 2 + α 3) (by linarith) (by linarith)
    unfold dartFt
    rw [div_lt_one (by positivity)]
    have key : Real.cos (α 2) < -Real.cos (ε / 2 + α 1 + (ε / 2 + α 3)) := by
      rw [← Real.cos_pi_sub]
      exact cos_lt_cos_of_abs_lt h2'.le (abs_lt.2 ⟨by linarith, by linarith⟩)
    rw [Real.cos_add] at key
    linarith
  have hG0 : G 0 < 0 := by
    simp only [hG, hu0, hw0, hFu0]; linarith
  -- at `t = 1`
  have hu1 : dartU ε δ 1 = ε + δ := by unfold dartU; ring
  have hw1 : dartW ε δ 1 = δ := by unfold dartW; ring
  have hFu1 : dartFu ε (ε + δ) δ = -1 := by
    have hs1 := hsin (ε + δ) (by linarith) (by linarith)
    have hs2 := hsin δ hδ0 (by linarith)
    have hc : Real.cos ε = Real.cos (ε + δ) * Real.cos δ + Real.sin (ε + δ) * Real.sin δ := by
      rw [← Real.cos_sub]; congr 1; ring
    unfold dartFu
    rw [hc, div_eq_iff (by positivity)]; ring
  have hFt1 : -1 < dartFt (α 2) (ε + δ + α 1) (δ + α 3) := by
    have hp := hsin (ε + δ + α 1) (by linarith) hδ1
    have hq := hsin (δ + α 3) (by linarith) hδ2
    unfold dartFt
    rw [lt_div_iff₀ (by positivity)]
    have key : -Real.cos (ε + δ + α 1 - (δ + α 3)) < Real.cos (α 2) := by
      rw [← Real.cos_abs, ← Real.cos_pi_sub]
      have hab := abs_nonneg (ε + δ + α 1 - (δ + α 3))
      have : |ε + δ + α 1 - (δ + α 3)| < π - α 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      exact Real.cos_lt_cos_of_nonneg_of_le_pi h2.le (by linarith) (by linarith)
    rw [Real.cos_sub] at key
    linarith
  have hG1 : 0 < G 1 := by
    simp only [hG, hu1, hw1, hFu1]; linarith
  -- the intermediate value theorem
  obtain ⟨t, ht, hGt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, G t = 0 :=
    intermediate_value_Icc zero_le_one hcont ⟨hG0.le, hG1.le⟩
  have ht0' : 0 < t := lt_of_le_of_ne ht.1 (fun e => by rw [← e] at hGt; linarith)
  have ht1' : t < 1 := lt_of_le_of_ne ht.2 (fun e => by rw [e] at hGt; linarith)
  obtain ⟨u1, u2⟩ := dartU_bounds hε0 hδ0 hδ1 ht
  obtain ⟨w1, w2⟩ := dartW_bounds hε0 hδ0 hW1 hδ2 ht
  set u := dartU ε δ t with hu
  set w := dartW ε δ t with hw
  have hsu := hsin u u1 (by linarith)
  have hsw := hsin w w1 (by linarith)
  have hsum_uw : u + w = ε + 2 * (t * δ) := by simp only [hu, hw, dartU, dartW]; ring
  have hdiff_uw : u - w = t * ε := by simp only [hu, hw, dartU, dartW]; ring
  have htd : t * δ ≤ δ := mul_le_of_le_one_left hδ0.le ht.2
  have htd' : 0 < t * δ := mul_pos ht0' hδ0
  have hte : t * ε < ε := mul_lt_of_lt_one_left hε0 ht1'
  have hte' : 0 ≤ t * ε := mul_nonneg ht.1 hε0.le
  have hC1 : dartFu ε u w < 1 := by
    unfold dartFu
    rw [div_lt_one (by positivity)]
    have : Real.cos (u + w) < Real.cos ε :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hε0.le (by rw [hsum_uw]; linarith)
        (by rw [hsum_uw]; linarith)
    rw [Real.cos_add] at this
    linarith
  have hC2 : -1 < dartFu ε u w := by
    unfold dartFu
    rw [lt_div_iff₀ (by positivity)]
    have : Real.cos ε < Real.cos (u - w) := by
      rw [hdiff_uw]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hte' (by linarith) hte
    rw [Real.cos_sub] at this
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.arccos (dartFu ε u w) := ⟨_, rfl⟩
  have hL0 : 0 < L := hL ▸ Real.arccos_pos.2 hC1
  have hLπ : L < π := hL ▸ Real.arccos_lt_pi.2 hC2
  have hcosL : Real.cos (2 * (L / 2)) = dartFu ε u w := by
    rw [show 2 * (L / 2) = L by ring, hL, Real.cos_arccos hC2.le hC1.le]
  have hFtu : dartFt (α 2) (u + α 1) (w + α 3) = dartFu ε u w := by
    have : G t = 0 := hGt
    simp only [hG] at this
    linarith
  have hp := hsin (u + α 1) (by linarith) u2
  have hq := hsin (w + α 3) (by linarith) w2
  refine ⟨DartParams.mk α (L / 2) u w h0 h0' h1 h2 h3 h2' u1 w1 u2 w2 (by linarith)
    (by linarith) ?_ ?_, rfl⟩
  · show Real.cos u * Real.cos w - Real.sin u * Real.sin w * Real.cos (2 * (L / 2)) =
      -Real.cos (α 0)
    rw [hcosL]
    unfold dartFu
    field_simp
    rw [hε, Real.cos_sub_pi]
    ring
  · show Real.cos (u + α 1) * Real.cos (w + α 3) -
      Real.sin (u + α 1) * Real.sin (w + α 3) * Real.cos (2 * (L / 2)) = -Real.cos (α 2)
    rw [hcosL, ← hFtu]
    unfold dartFt
    field_simp
    ring

/-! ### Troyanov's theorem for four angles, one above `2π` -/

/-- **The double of a spherical dart**: for `α_0 ∈ ]π, 2π[`, `α_1, α_2, α_3 > 0`, `α_2 < π`
and the inequalities below, there is a cone sphere with cone angles `2α_i`. -/
theorem exists_isConeSphere_dart (α : Fin 4 → ℝ) (h0 : π < α 0) (h0' : α 0 < 2 * π)
    (h1 : 0 < α 1) (h2 : 0 < α 2) (h3 : 0 < α 3) (h2' : α 2 < π)
    (h01 : α 0 + α 1 < 2 * π) (h03 : α 0 + α 3 < 2 * π) (hsum : 2 * π < α 0 + α 1 + α 2 + α 3)
    (h013 : α 0 + α 1 + α 3 < 2 * π + α 2) (h012 : α 0 + α 1 + α 2 < 2 * π + α 3)
    (h23 : α 2 + α 3 < α 0 + α 1) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M (fun i => 2 * α i) p := by
  obtain ⟨D, rfl⟩ := exists_dartParams α h0 h0' h1 h2 h3 h2' h01 h03 hsum h013 h012 h23
  exact D.exists_isConeSphere

/-- **At `s = 4`, Troyanov's condition allows at most one angle above `2π`, and it is below
`4π`** (the planner's `[r]`, checked): `χ' ≤ θ_j` reads `∑_{i ≠ j} θ_i ≤ 4π`. -/
theorem TroyanovAngleCondition.four_of_gt_two_pi {θ : Fin 4 → ℝ} (hθ : TroyanovAngleCondition θ)
    {k : Fin 4} (hk : 2 * π < θ k) : θ k < 4 * π ∧ ∀ j, j ≠ k → θ j < 2 * π := by
  have p0 := hθ.pos 0
  have p1 := hθ.pos 1
  have p2 := hθ.pos 2
  have p3 := hθ.pos 3
  have hj := hθ.2.2.2
  simp only [Fin.sum_univ_four] at hj
  have j0 := hj 0
  have j1 := hj 1
  have j2 := hj 2
  have j3 := hj 3
  have hπ := Real.pi_pos
  constructor
  · match k with
    | 0 => linarith
    | 1 => linarith
    | 2 => linarith
    | 3 => linarith
  · intro j hjk
    match k, j with
    | 0, 0 => exact absurd rfl hjk
    | 0, 1 => linarith
    | 0, 2 => linarith
    | 0, 3 => linarith
    | 1, 0 => linarith
    | 1, 1 => exact absurd rfl hjk
    | 1, 2 => linarith
    | 1, 3 => linarith
    | 2, 0 => linarith
    | 2, 1 => linarith
    | 2, 2 => exact absurd rfl hjk
    | 2, 3 => linarith
    | 3, 0 => linarith
    | 3, 1 => linarith
    | 3, 2 => linarith
    | 3, 3 => exact absurd rfl hjk

/-- **Troyanov's theorem at `s = 4` with an angle above `2π`**: the double of the spherical dart
with angles `θ_i / 2`, the reflex vertex at the angle above `2π`. -/
theorem troyanovTheorem_four_of_exists_gt_two_pi (θ : Fin 4 → ℝ) (hθ : TroyanovAngleCondition θ)
    (hgt : ∃ i, 2 * π < θ i) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M θ p := by
  obtain ⟨k, hk⟩ := hgt
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 k
  set θ' : Fin 4 → ℝ := θ ∘ σ with hθ'
  have hπ := Real.pi_pos
  have hsum' : ∑ i, (θ' i - 2 * π) = ∑ i, (θ i - 2 * π) :=
    Equiv.sum_comp σ (fun i => θ i - 2 * π)
  have c1 : 0 < ∑ i, (θ' i - 2 * π) + 4 * π := hsum' ▸ hθ.2.1
  have c2 : ∀ j, ∑ i, (θ' i - 2 * π) + 4 * π ≤ θ' j := fun j => hsum' ▸ hθ.2.2.2 (σ j)
  have cp : ∀ j, 0 < θ' j := fun j => hθ.pos (σ j)
  simp only [Fin.sum_univ_four] at c1 c2
  have q0 : θ' 0 = θ k := by simp only [hθ', σ, Function.comp_apply, Equiv.swap_apply_left]
  have j0 := c2 0
  have j1 := c2 1
  have j2 := c2 2
  have j3 := c2 3
  have p0 := cp 0
  have p1 := cp 1
  have p2 := cp 2
  have p3 := cp 3
  rw [q0] at j0 j1 j2 j3 c1 p0
  obtain ⟨M, _, _, p, hp⟩ := exists_isConeSphere_dart (fun i => θ' i / 2)
    (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by positivity) (by positivity) (by positivity)
    (by linarith) (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by simp only [q0]; linarith) (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by simp only [q0]; linarith)
  have hθσ : (fun i => 2 * (fun i => θ' i / 2) i) = θ ∘ σ := by
    funext i; simp only [hθ', Function.comp_apply]; ring
  rw [hθσ] at hp
  have h' := hp.comp_equiv σ.symm
  have e : θ ∘ σ ∘ σ.symm = θ := by funext i; simp
  rw [Function.comp_assoc, e] at h'
  exact ⟨M, _, _, _, h'⟩

/-- **Troyanov's theorem at `s = 4`**, every angle: with `GX.troyanovTheorem_of_le_two_pi`
(`GX.Spherical.TroyanovPolygon`) when no angle is above `2π`. -/
theorem troyanovTheorem_four (θ : Fin 4 → ℝ) (hθ : TroyanovAngleCondition θ) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M θ p := by
  by_cases h : ∃ i, 2 * π < θ i
  · exact troyanovTheorem_four_of_exists_gt_two_pi θ hθ h
  · push Not at h
    exact troyanovTheorem_of_le_two_pi θ hθ h

/-- **What remains of Troyanov's theorem**: its case `s ≥ 5`, every angle `≠ 2π`, some angle
`> 2π` (`GX.troyanovTheorem_of_exists_gt_two_pi` with the case `s = 4` closed). -/
theorem troyanovTheorem_of_five_le_of_exists_gt_two_pi
    (h : ∀ {s : ℕ}, 5 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleCondition θ → (∀ i, θ i ≠ 2 * π) →
      (∃ i, 2 * π < θ i) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p :=
  troyanovTheorem_of_exists_gt_two_pi fun {s} hs θ hθ hne hgt => by
    rcases Nat.lt_or_ge s 5 with h5 | h5
    · obtain rfl : s = 4 := by omega
      exact troyanovTheorem_four_of_exists_gt_two_pi θ hθ hgt
    · exact h h5 θ hθ hne hgt

/-- **The case is not vacuous, and meets the cex's genericity**: the pairwise distinct angles
`(5π/2, π/2, 3π/5, 7π/10)` satisfy l.1930's condition (`χ' = 3π/10`), one is above `2π`, and a
cone sphere with these angles exists. -/
theorem troyanovAngleCondition_four_gt_two_pi :
    TroyanovAngleCondition ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] ∧
      Pairwise (fun i j => ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] i ≠
        ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] j) ∧
      2 * π < ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] 0 ∧
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
        IsConeSphere M ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] p := by
  have hπ := Real.pi_pos
  have hc : TroyanovAngleCondition ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] := by
    refine ⟨by norm_num, ?_, ?_, fun j => ?_⟩
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linarith
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linarith
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      fin_cases j <;> simp <;> linarith
  have h0 : 2 * π < ![5 * π / 2, π / 2, 3 * π / 5, 7 * π / 10] 0 := by simp; linarith
  refine ⟨hc, fun i j hij => ?_, h0, troyanovTheorem_four_of_exists_gt_two_pi _ hc ⟨0, h0⟩⟩
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

end DartMain

end GX
