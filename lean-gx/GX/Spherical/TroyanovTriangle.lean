import GX.Spherical.Football
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Troyanov's theorem for three cone points: the double of a spherical triangle

Target `T-gx-troyanov-triangle` (`roadmap/roadmap.toml`; DEC-136, Troyanov's theorem proved, not
assumed). `papers/gx`, 0 `sorry`, standard axioms only. **No label is marked here.**

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial, not marked: the row
  needs Troyanov's theorem for every `s ≥ 3` and the Thurston suspension facts
  (`GX.thurstonSuspensionFacts`), both outside this module. Here the cited theorem (`MR1005085`) is
  proved for `s = 3`, in the shape of `GX.TroyanovTheorem` (`GXScaffold.Spherical.TroyanovAngles`)
  with `s := 3`: **`GX.troyanovTheorem_three`** — for `θ : Fin 3 → ℝ` with
  `TroyanovAngleCondition θ` there is a singular `(SO(3), 𝕊²)`-manifold `M` and three points with
  `IsConeSphere M θ p`. The general statement is thereby reduced to `s ≥ 4`
  (`GX.troyanovTheorem_of_four_le`).
* The arithmetic (the planner's `[r]`, checked): `GX.troyanovAngleCondition_three_iff` (for `s = 3`
  the condition is `α_0 + α_1 + α_2 > π` and `α_i + α_j ≤ π`, `α_i = θ_i / 2`),
  `GX.TroyanovAngleCondition.three_half` (`0 < α_i < π`).
* The triangle: `GX.SphTriangle` (given by the inward normals of its sides),
  `GX.exists_sphTriangle` (angles `α_i ∈ ]0, π[`, `∑ α_i > π`, `α_i + α_j < π + α_k`).
* The double: `GX.SphTriangle.TriDouble` (`𝕊²` as a space), its fold onto the triangle
  `GX.SphTriangle.fold`, the cone charts `GX.SphTriangle.Φ` (`C_{θ_i} ⊇ V_i → TriDouble`), the
  generating atlas `GX.SphTriangle.atlas` (`GX.SphTriangle.isGXAtlas_atlas`,
  `GX.SphTriangle.isAEAtlas_atlas`), the structure `GX.SphTriangle.singularGXStructure`, the
  `X_θ`-charts `GX.SphTriangle.coneXAChart`, `GX.SphTriangle.isConePoint_vertex`,
  `GX.SphTriangle.isConeSphere`.
* A remark: `GX.exists_isConeSphere_not_troyanovAngleCondition` (for `s = 3` the condition of
  l.1930 is sufficient, not necessary; the paper claims only sufficiency).

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. We know from
> Troyanov \cite{MR1005085}  that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> (l.1930)

## The construction

With `α_i = θ_i / 2`, the condition says that the `α_i` are the angles of a spherical triangle `T`
(its normals `n_k` have Gram matrix `−cos α_i` off the diagonal, positive definite since
`|cos α_0 + cos α_1 cos α_2| < sin α_1 sin α_2`). The double of `T` is `𝕊²` read as the double of
the closed unit disc along the circle `s = 0`; the disc is `T`, through the stereographic chart at
the vertex `v_0` (where `T` is convex: two half-planes and a disc) and mathlib's gauge rescaling
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`). At `v_i`, polar coordinates
folded onto the sector of angle `α_i` (`GX.polarFold`), on the sheet of the sign of `Im h`, give an
open embedding of a star-shaped `V_i ⊆ C_{θ_i} ≅ ℂ` (`GX.isOpenMap_restrict_of_isCompact`). The
developing map of `C_{θ_i}` is `R_i ∘ fold` on the upper copy, `(ρ R_i ρ) ∘ ρ ∘ fold` on the lower,
and `R_i ∘ (fold | σ_k ∘ fold)` across the side `e_k` (`R_i σ_{i+2} R_i⁻¹ = ρ`,
`R_i σ_{i+1} R_i⁻¹ = rot(2α_i) ρ`), so two cone charts differ near every common point by one
element of `SO(3)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s ≥ 3` conical singularities (l.1930) | `s = 3` exactly (`Fin 3`); `s ≥ 4` is `T-gx-troyanov` |
| Troyanov's condition (l.1930) | ✓ carried: `TroyanovAngleCondition θ`, verbatim (DEC-69's) |
| `Σ` a singular `𝕊²`-manifold homeomorphic to a sphere, conical singularities of angles `θ_i` | ✓ `GX.IsConeSphere` (the library's reading, `GX.Spherical.ConeSurface` SCOPE (a), OQ-37 (b)) |
| Troyanov's theorem (`MR1005085`), cited | ✓ proved for `s = 3`, not assumed (DEC-136) |

## SCOPE (disclosed)

* **(a)** Only `s = 3`; the row stays partial (see above).
* **(b)** For `s = 3` the condition forces `θ_i + θ_j ≤ 2π`, hence every `θ_i < 2π`: the three cone
  points are genuine (no marked regular point, unlike `GX.troyanovAngleCondition_two_pi` for
  `s = 4`).
* **(c)** The metric is not formalized (as in `GX.Spherical.ConeSurface`): a cone point is an
  `X_θ`-chart onto a neighbourhood of the apex of `C_θ`; the regular part carries the a.e.
  `(SO(3), 𝕊²)`-atlas.
* **(d)** The surface is the doubled triangle, not Troyanov's variational solution; it exists for
  more angles than the condition allows (the remark above).
* **(e)** `M : Type`, as in `GX.TroyanovTheorem`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.Football` (`polarHalfPlaneLift`, `isAEMorphismOf_maximalAEAtlas_of_forall`,
`halfTurn`), `GX.Spherical.ConeSurface` (`SphCone`, `sphCone_chart_dev`, `IsConePoint`,
`IsConeSphere`), `GX.Spherical.S3Model` (`stereoInv`, `SO3`), `GX.SingularII.Models`
(`XAChart`, `TroyanovAngleCondition`), `GX.SingularII.Tame` (open subsets).
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace Matrix

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### Troyanov's condition for three angles -/

section Angles

/-- **Troyanov's condition for `s = 3`, in the half-angles `α_i = θ_i / 2`**: since
`∑ (θ_i − 2π) + 4π = 2(α_0 + α_1 + α_2 − π)`, the condition of `RamcovGX.tex:1930` is
`α_0 + α_1 + α_2 > π` together with `α_i + α_j ≤ π` for `i ≠ j` (the bound `≤ 4π` and the
positivity of the angles follow). -/
theorem troyanovAngleCondition_three_iff (θ : Fin 3 → ℝ) :
    TroyanovAngleCondition θ ↔
      π < θ 0 / 2 + θ 1 / 2 + θ 2 / 2 ∧ θ 0 / 2 + θ 1 / 2 ≤ π ∧ θ 0 / 2 + θ 2 / 2 ≤ π ∧
        θ 1 / 2 + θ 2 / 2 ≤ π := by
  unfold TroyanovAngleCondition
  simp only [Fin.sum_univ_three]
  constructor
  · rintro ⟨-, h1, -, h3⟩
    have a := h3 0; have b := h3 1; have c := h3 2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨le_rfl, by linarith, by linarith, fun j => ?_⟩
    fin_cases j <;> simp <;> linarith

/-- For `s = 3`, the half-angles lie in `]0, π[`. -/
theorem TroyanovAngleCondition.three_half {θ : Fin 3 → ℝ} (h : TroyanovAngleCondition θ)
    (i : Fin 3) :
    0 < θ i / 2 ∧ θ i / 2 < π := by
  have h0 := (troyanovAngleCondition_three_iff θ).1 h
  have hp := h.pos
  have := hp 0; have := hp 1; have := hp 2
  fin_cases i <;> simp <;> constructor <;> linarith [Real.pi_pos]

end Angles

/-! ### Coordinates on `ℝ ⊕ ℂ = ℝ³`, and elements of `SO(3)` from matrices -/

section R3

/-- Coordinates of `ℝ ⊕ ℂ`: `(t, w) ↦ (t, Re w, Im w)`. -/
def toR3 : Euc3 ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x.fst, x.snd.re, x.snd.im]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp
  invFun v := WithLp.toLp 2 (v 0, ⟨v 1, v 2⟩)
  left_inv x := by
    show WithLp.toLp 2 (x.fst, ⟨x.snd.re, x.snd.im⟩) = x
    rfl
  right_inv v := by ext i; fin_cases i <;> rfl

theorem toR3_apply (x : Euc3) : toR3 x = ![x.fst, x.snd.re, x.snd.im] := rfl

theorem toR3_symm_apply (v : Fin 3 → ℝ) : toR3.symm v = WithLp.toLp 2 (v 0, ⟨v 1, v 2⟩) := rfl

theorem norm_sq_eq_dot (x : Euc3) : ‖x‖ ^ 2 = toR3 x ⬝ᵥ toR3 x := by
  rw [norm_polarSum_sq, Complex.sq_norm, Complex.normSq_apply, toR3_apply]
  simp [dotProduct, Fin.sum_univ_three]; ring

theorem norm_toR3_symm_sq (v : Fin 3 → ℝ) : ‖toR3.symm v‖ ^ 2 = v ⬝ᵥ v := by
  rw [norm_sq_eq_dot, LinearEquiv.apply_symm_apply]

/-- The coordinates of a point of `𝕊²`. -/
def vec (y : Sph2) : Fin 3 → ℝ := toR3 (y : Euc3)

theorem vec_dot_self (y : Sph2) : vec y ⬝ᵥ vec y = 1 := by
  rw [vec, ← norm_sq_eq_dot, norm_raySphere, one_pow]

theorem vec_injective : Injective vec := fun _ _ h =>
  Subtype.ext (toR3.injective h)

/-- A point of `𝕊²` from unit coordinates. -/
def ofVec (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) : Sph2 :=
  ⟨toR3.symm v, mem_sphere_zero_iff_norm.2 (by
    have h := norm_toR3_symm_sq v
    rw [hv] at h
    nlinarith [norm_nonneg (toR3.symm v)])⟩

@[simp] theorem vec_ofVec (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) : vec (ofVec v hv) = v :=
  LinearEquiv.apply_symm_apply _ _

/-- The linear map of `ℝ ⊕ ℂ` with matrix `A` in the coordinates `toR3`. -/
def matLin (A : Matrix (Fin 3) (Fin 3) ℝ) : Euc3 →ₗ[ℝ] Euc3 :=
  (toR3.symm : (Fin 3 → ℝ) →ₗ[ℝ] Euc3) ∘ₗ Matrix.toLin' A ∘ₗ (toR3 : Euc3 →ₗ[ℝ] (Fin 3 → ℝ))

theorem toR3_matLin (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Euc3) :
    toR3 (matLin A x) = A *ᵥ toR3 x := by
  simp [matLin]

theorem dot_mulVec_self {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (v : Fin 3 → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hA, one_mulVec]

theorem norm_matLin {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (x : Euc3) :
    ‖matLin A x‖ = ‖x‖ := by
  have h : ‖matLin A x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_dot, norm_sq_eq_dot, toR3_matLin, dot_mulVec_self hA]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **The element of `SO(3)` of an orthogonal matrix of determinant `1`**, in the coordinates
`toR3`. -/
def matSO3 (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ * A = 1) (hd : A.det = 1) : SO3 :=
  ⟨(⟨matLin A, norm_matLin hA⟩ : Euc3 →ₗᵢ[ℝ] Euc3).toLinearIsometryEquiv rfl, by
    show LinearMap.det (matLin A) = 1
    rw [matLin]
    have := LinearMap.det_conj (Matrix.toLin' A) toR3.symm
    rw [LinearEquiv.symm_symm] at this
    rw [this, LinearMap.det_toLin', hd]⟩

theorem vec_matSO3_smul {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (hd : A.det = 1)
    (y : Sph2) : vec (matSO3 A hA hd • y) = A *ᵥ vec y :=
  toR3_matLin A y

theorem vec_matSO3_inv_smul {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ * A = 1) (hd : A.det = 1)
    (y : Sph2) : vec ((matSO3 A hA hd)⁻¹ • y) = Aᵀ *ᵥ vec y := by
  have h := vec_matSO3_smul hA hd ((matSO3 A hA hd)⁻¹ • y)
  rw [smul_inv_smul] at h
  rw [h, mulVec_mulVec, hA, one_mulVec]

/-- The frame matrix with rows `v × w`, `v`, `w`. -/
def frameMat (v w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![v ⨯₃ w, v, w]

theorem frameMat_mulVec (v w x : Fin 3 → ℝ) :
    frameMat v w *ᵥ x = ![(v ⨯₃ w) ⬝ᵥ x, v ⬝ᵥ x, w ⬝ᵥ x] := by
  ext i; fin_cases i <;> rfl

theorem frameMat_mul_transpose {v w : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hvw : v ⬝ᵥ w = 0) : frameMat v w * (frameMat v w)ᵀ = 1 := by
  have hc : (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) = 1 := by
    rw [cross_dot_cross, hv, hw, hvw, dotProduct_comm w v, hvw]; ring
  have h1 : (v ⨯₃ w) ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact dot_self_cross v w
  have h2 : (v ⨯₃ w) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact dot_cross_self v w
  ext i j
  have hij : (frameMat v w * (frameMat v w)ᵀ) i j = ![v ⨯₃ w, v, w] i ⬝ᵥ ![v ⨯₃ w, v, w] j := rfl
  rw [hij, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hc, h1, h2, hv, hw, hvw, dotProduct_comm v (v ⨯₃ w),
      dotProduct_comm w (v ⨯₃ w), dotProduct_comm w v]

theorem frameMat_transpose_mul {v w : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hvw : v ⬝ᵥ w = 0) : (frameMat v w)ᵀ * frameMat v w = 1 :=
  mul_eq_one_comm.1 (frameMat_mul_transpose hv hw hvw)

theorem det_frameMat {v w : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hvw : v ⬝ᵥ w = 0) : (frameMat v w).det = 1 := by
  have h : (frameMat v w).det = Matrix.det ![v ⨯₃ w, v, w] := rfl
  rw [h, ← triple_product_eq_det, cross_dot_cross, hv, hw, hvw, dotProduct_comm w v, hvw]
  ring

/-- **The rotation taking the orthonormal frame `(v × w, v, w)` to the standard one.** -/
def frameSO3 (v w : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1) (hvw : v ⬝ᵥ w = 0) : SO3 :=
  matSO3 (frameMat v w) (frameMat_transpose_mul hv hw hvw) (det_frameMat hv hw hvw)

theorem vec_frameSO3_smul {v w : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hvw : v ⬝ᵥ w = 0) (y : Sph2) :
    vec (frameSO3 v w hv hw hvw • y) = ![(v ⨯₃ w) ⬝ᵥ vec y, v ⬝ᵥ vec y, w ⬝ᵥ vec y] := by
  rw [frameSO3, vec_matSO3_smul, frameMat_mulVec]

/-- The inverse rotation, read on a dot product: `⟨n, R⁻¹ y⟩ = ⟨R n, y⟩`. -/
theorem dot_vec_frameSO3_inv_smul {v w : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hvw : v ⬝ᵥ w = 0) (n : Fin 3 → ℝ) (y : Sph2) :
    n ⬝ᵥ vec ((frameSO3 v w hv hw hvw)⁻¹ • y) = (frameMat v w *ᵥ n) ⬝ᵥ vec y := by
  rw [frameSO3, vec_matSO3_inv_smul, dotProduct_mulVec, vecMul_transpose]

theorem vec_apply (y : Sph2) : vec y = ![(y : Euc3).fst, (y : Euc3).snd.re, (y : Euc3).snd.im] :=
  rfl

theorem continuous_vec : Continuous vec :=
  toR3.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val

/-- The coordinates of the inverse stereographic projection. -/
theorem vec_stereoInv (v : ℂ) :
    vec (stereoInv v) = ![(1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2), 2 * v.re / (1 + ‖v‖ ^ 2),
      2 * v.im / (1 + ‖v‖ ^ 2)] := by
  rw [vec_apply, stereoInv_fst, stereoInv_snd, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    smul_eq_mul]
  ext i; fin_cases i <;> simp <;> ring

/-- The pairing of a vector with a point of the stereographic plane:
`c · stereoInv v = G_c(v) / (1 + |v|²)`. -/
def gfun (c : Fin 3 → ℝ) (v : ℂ) : ℝ := c 0 * (1 - ‖v‖ ^ 2) + 2 * (c 1 * v.re + c 2 * v.im)

theorem dot_vec_stereoInv (c : Fin 3 → ℝ) (v : ℂ) :
    c ⬝ᵥ vec (stereoInv v) = gfun c v / (1 + ‖v‖ ^ 2) := by
  rw [vec_stereoInv, gfun]
  simp [dotProduct, Fin.sum_univ_three]
  field_simp
  ring

theorem continuous_dot_vec (c : Fin 3 → ℝ) : Continuous fun y : Sph2 => c ⬝ᵥ vec y :=
  continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_vec)

theorem continuous_gfun (c : Fin 3 → ℝ) : Continuous (gfun c) := by
  unfold gfun; fun_prop

end R3

/-! ### Reflections of `𝕊²` -/

section Reflections

/-- **The reflection of `𝕊²` in the plane `n^⊥`**, `x ↦ x − 2⟨n, x⟩ n`, `n` a unit vector. -/
def reflSph (n : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) (y : Sph2) : Sph2 :=
  ofVec (vec y - (2 * (n ⬝ᵥ vec y)) • n) (by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, hn, vec_dot_self, dotProduct_comm (vec y) n]
    simp only [smul_eq_mul]; ring)

theorem vec_reflSph {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (y : Sph2) :
    vec (reflSph n hn y) = vec y - (2 * (n ⬝ᵥ vec y)) • n :=
  vec_ofVec _ _

theorem continuous_reflSph {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) : Continuous (reflSph n hn) := by
  have : Continuous fun y : Sph2 => toR3.symm (vec y - (2 * (n ⬝ᵥ vec y)) • n) :=
    toR3.symm.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_vec.sub ((continuous_const.mul
        ((continuous_const.dotProduct continuous_vec))).smul continuous_const))
  exact this.subtype_mk _

/-- The isometry `(t, w) ↦ (t, w̄)` of `ℝ ⊕ ℂ`. -/
def conjIsom : Euc3 ≃ₗᵢ[ℝ] Euc3 where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × ℂ)).trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr Complex.conjLIE.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℝ (ℝ × ℂ)).symm)
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp

theorem conjIsom_apply (x : Euc3) :
    conjIsom x = WithLp.toLp 2 (x.fst, (starRingEnd ℂ) x.snd) := rfl

theorem conjIsom_conjIsom (x : Euc3) : conjIsom (conjIsom x) = x := by
  rw [conjIsom_apply, conjIsom_apply]
  show WithLp.toLp 2 (x.fst, (starRingEnd ℂ) ((starRingEnd ℂ) x.snd)) = x
  rw [Complex.conj_conj]; rfl

/-- **The reflection `ρ : (t, w) ↦ (t, w̄)` of `𝕊²`** (in the plane of the meridian `ψ = 0`). -/
def conjSph (y : Sph2) : Sph2 :=
  ⟨conjIsom y, mem_sphere_zero_iff_norm.2 (by rw [LinearIsometryEquiv.norm_map, norm_raySphere])⟩

theorem coe_conjSph (y : Sph2) : (conjSph y : Euc3) = conjIsom y := rfl

theorem conjSph_conjSph (y : Sph2) : conjSph (conjSph y) = y :=
  Subtype.ext (conjIsom_conjIsom _)

theorem continuous_conjSph : Continuous conjSph :=
  (conjIsom.continuous.comp continuous_subtype_val).subtype_mk _

theorem vec_conjSph (y : Sph2) : vec (conjSph y) = ![vec y 0, vec y 1, -vec y 2] := by
  simp [vec_apply, coe_conjSph, conjIsom_apply]

theorem conjSph_stereoInv (v : ℂ) : conjSph (stereoInv v) = stereoInv ((starRingEnd ℂ) v) := by
  apply vec_injective
  rw [vec_conjSph, vec_stereoInv, vec_stereoInv]
  simp [neg_div]

/-- **Conjugation of `SO(3)` by `ρ`**: `ρ g ρ`, of determinant `1`. -/
def conjSO3 (g : SO3) : SO3 :=
  ⟨conjIsom.trans ((g : Euc3 ≃ₗᵢ[ℝ] Euc3).trans conjIsom), by
    have e : (((conjIsom.trans ((g : Euc3 ≃ₗᵢ[ℝ] Euc3).trans conjIsom)).toLinearEquiv :
        Euc3 →ₗ[ℝ] Euc3)) = (conjIsom.toLinearEquiv : Euc3 →ₗ[ℝ] Euc3) ∘ₗ
          (((g : Euc3 ≃ₗᵢ[ℝ] Euc3).toLinearEquiv : Euc3 →ₗ[ℝ] Euc3) ∘ₗ
            (conjIsom.toLinearEquiv : Euc3 →ₗ[ℝ] Euc3)) := by
      ext x; rfl
    have hcc : (conjIsom.toLinearEquiv : Euc3 →ₗ[ℝ] Euc3) ∘ₗ
        (conjIsom.toLinearEquiv : Euc3 →ₗ[ℝ] Euc3) = LinearMap.id := by
      exact LinearMap.ext fun x => conjIsom_conjIsom x
    have h1 := congrArg LinearMap.det hcc
    rw [LinearMap.det_comp, LinearMap.det_id] at h1
    show LinearMap.det _ = 1
    rw [e, LinearMap.det_comp, LinearMap.det_comp, (mem_specialOrth.1 g.2)]
    linear_combination h1⟩

theorem conjSph_smul (g : SO3) (y : Sph2) : conjSph (g • y) = conjSO3 g • conjSph y := by
  refine Subtype.ext ?_
  show conjIsom ((g : Euc3 ≃ₗᵢ[ℝ] Euc3) y) =
    conjIsom ((g : Euc3 ≃ₗᵢ[ℝ] Euc3) (conjIsom (conjIsom (y : Euc3))))
  rw [conjIsom_conjIsom]

end Reflections

/-! ### Spherical triangles, by the normals of their sides -/

section Triangle

/-- **A spherical triangle with angles `α_i`**, given by the inward unit normals `n_k` of its
sides `e_k` (the side `e_k` is opposite the vertex `v_k`): the angle at `v_i`, between `e_{i+1}`
and `e_{i+2}`, is `α_i`, i.e. `⟨n_{i+1}, n_{i+2}⟩ = −cos α_i`, and the normals are positively
oriented. The triangle is `{x ∈ 𝕊² : ⟨n_k, x⟩ ≥ 0, k = 0, 1, 2}` (`SphTriangle.T`). -/
structure SphTriangle where
  /-- The angles. -/
  α : Fin 3 → ℝ
  /-- The inward unit normals of the sides. -/
  n : Fin 3 → Fin 3 → ℝ
  α_pos : ∀ i, 0 < α i
  α_lt_pi : ∀ i, α i < π
  unit : ∀ k, n k ⬝ᵥ n k = 1
  gram : ∀ i, n (i + 1) ⬝ᵥ n (i + 2) = -Real.cos (α i)
  det_pos : 0 < Matrix.det ![n 0, n 1, n 2]

namespace SphTriangle

variable (t : SphTriangle)

/-- The closed triangle. -/
def T : Set Sph2 := {y | ∀ k, 0 ≤ t.n k ⬝ᵥ vec y}

theorem isClosed_T : IsClosed t.T := by
  simp only [T, setOf_forall]
  exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_dot_vec _)

theorem sin_pos (i : Fin 3) : 0 < Real.sin (t.α i) :=
  Real.sin_pos_of_pos_of_lt_pi (t.α_pos i) (t.α_lt_pi i)

theorem det_cyclic (i : Fin 3) :
    t.n i ⬝ᵥ (t.n (i + 1) ⨯₃ t.n (i + 2)) = Matrix.det ![t.n 0, t.n 1, t.n 2] := by
  rw [← triple_product_eq_det]
  fin_cases i
  · rfl
  · show t.n 1 ⬝ᵥ (t.n 2 ⨯₃ t.n 0) = _
    rw [triple_product_permutation (t.n 0)]
  · show t.n 2 ⬝ᵥ (t.n 0 ⨯₃ t.n 1) = _
    rw [triple_product_permutation (t.n 0), triple_product_permutation (t.n 1)]

/-- The second vector of the frame at `v_i`: the unit tangent of `e_{i+2}` at `v_i`, inside. -/
def m (i : Fin 3) : Fin 3 → ℝ :=
  (Real.sin (t.α i))⁻¹ • (t.n (i + 1) + Real.cos (t.α i) • t.n (i + 2))

theorem m_dot_n (i : Fin 3) : t.m i ⬝ᵥ t.n (i + 2) = 0 := by
  rw [m, smul_dotProduct, add_dotProduct, smul_dotProduct, t.gram, t.unit]
  simp

theorem m_dot_m (i : Fin 3) : t.m i ⬝ᵥ t.m i = 1 := by
  have hs := t.sin_pos i
  have h1 := t.gram i
  have h2 := t.unit (i + 1)
  have h3 := t.unit (i + 2)
  rw [m]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm (t.n (i + 2)) (t.n (i + 1)), h1, h2, h3]
  have hsc := Real.sin_sq_add_cos_sq (t.α i)
  field_simp
  nlinarith

theorem n_succ_eq (i : Fin 3) :
    t.n (i + 1) = Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (i + 2) := by
  have hs := (t.sin_pos i).ne'
  rw [m, smul_smul, mul_inv_cancel₀ hs, one_smul]
  abel

/-- **The rotation `R_i` putting the vertex `v_i` at the north pole**, the side `e_{i+2}` along
the meridian `ψ = 0` and the side `e_{i+1}` along the meridian `ψ = α_i`. -/
def R (i : Fin 3) : SO3 := frameSO3 (t.m i) (t.n (i + 2)) (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

/-- Its matrix. -/
def A (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ := frameMat (t.m i) (t.n (i + 2))

theorem A_mulVec (i : Fin 3) (x : Fin 3 → ℝ) :
    t.A i *ᵥ x = ![(t.m i ⨯₃ t.n (i + 2)) ⬝ᵥ x, t.m i ⬝ᵥ x, t.n (i + 2) ⬝ᵥ x] :=
  frameMat_mulVec _ _ _

theorem A_mulVec_n_add_two (i : Fin 3) : t.A i *ᵥ t.n (i + 2) = ![0, 0, 1] := by
  rw [A_mulVec, t.unit, t.m_dot_n, dotProduct_comm, dot_cross_self]

theorem A_mulVec_n_add_one (i : Fin 3) :
    t.A i *ᵥ t.n (i + 1) = ![0, Real.sin (t.α i), -Real.cos (t.α i)] := by
  rw [t.n_succ_eq i, A_mulVec]
  have h1 : (t.m i ⨯₃ t.n (i + 2)) ⬝ᵥ (Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (i + 2))
      = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm, dot_self_cross,
      dotProduct_comm, dot_cross_self]
    simp
  rw [h1]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, t.m_dot_m, t.m_dot_n, t.unit,
    dotProduct_comm (t.n (i + 2)) (t.m i)]
  ext j; fin_cases j <;> simp

/-- The first coordinate of `R_i n_i` is positive: `⟨n_i, v_i⟩ > 0`. -/
theorem A_mulVec_n_zero_pos (i : Fin 3) : 0 < (t.A i *ᵥ t.n i) 0 := by
  rw [A_mulVec]
  show 0 < (t.m i ⨯₃ t.n (i + 2)) ⬝ᵥ t.n i
  rw [dotProduct_comm, m, LinearMap.map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply,
    LinearMap.map_smul, LinearMap.smul_apply, cross_self, smul_zero, add_zero, dotProduct_smul,
    t.det_cyclic]
  exact smul_pos (inv_pos.2 (t.sin_pos i)) t.det_pos

theorem A_transpose_mul (i : Fin 3) : (t.A i)ᵀ * t.A i = 1 :=
  frameMat_transpose_mul (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

theorem A_mul_transpose (i : Fin 3) : t.A i * (t.A i)ᵀ = 1 :=
  frameMat_mul_transpose (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

theorem vec_R_smul (i : Fin 3) (y : Sph2) : vec (t.R i • y) = t.A i *ᵥ vec y :=
  vec_frameSO3_smul _ _ _ y ▸ (t.A_mulVec i (vec y)).symm ▸ rfl

theorem dot_vec_R_inv_smul (i : Fin 3) (c : Fin 3 → ℝ) (y : Sph2) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • y) = (t.A i *ᵥ c) ⬝ᵥ vec y :=
  dot_vec_frameSO3_inv_smul _ _ _ c y

/-- The pairing with a point read in the stereographic chart at `v_i`. -/
theorem dot_vec_R_inv_stereoInv (i : Fin 3) (c : Fin 3 → ℝ) (v : ℂ) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • stereoInv v) = gfun (t.A i *ᵥ c) v / (1 + ‖v‖ ^ 2) := by
  rw [dot_vec_R_inv_smul, dot_vec_stereoInv]

/-- The reflection `σ_k` of `𝕊²` in the great circle of the side `e_k`. -/
def σ (k : Fin 3) : Sph2 → Sph2 := reflSph (t.n k) (t.unit k)

theorem vec_R_σ_R_inv (i k : Fin 3) (y : Sph2) :
    vec (t.R i • t.σ k ((t.R i)⁻¹ • y)) =
      vec y - (2 * ((t.A i *ᵥ t.n k) ⬝ᵥ vec y)) • (t.A i *ᵥ t.n k) := by
  rw [t.vec_R_smul, σ, vec_reflSph, mulVec_sub, mulVec_smul, t.dot_vec_R_inv_smul]
  congr 1
  have h := t.vec_R_smul i ((t.R i)⁻¹ • y)
  rw [smul_inv_smul] at h
  exact h.symm

/-- **The reflection in `e_{i+2}` is `ρ` at `v_i`**: `R_i σ_{i+2} R_i⁻¹ = ρ`. -/
theorem R_σ_add_two (i : Fin 3) (y : Sph2) :
    t.R i • t.σ (i + 2) ((t.R i)⁻¹ • y) = conjSph y := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_add_two, vec_conjSph]
  ext j; fin_cases j <;> simp [dotProduct, Fin.sum_univ_three]; ring

/-- **The reflection in `e_{i+1}` is the rotation of angle `2α_i` after `ρ` at `v_i`**:
`R_i σ_{i+1} R_i⁻¹ (stereoInv v) = stereoInv (e^{2iα_i} v̄)`. -/
theorem R_σ_add_one_stereoInv (i : Fin 3) (v : ℂ) :
    t.R i • t.σ (i + 1) ((t.R i)⁻¹ • stereoInv v) =
      stereoInv (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v) := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_add_one, vec_stereoInv, vec_stereoInv]
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

end SphTriangle

/-! ### Existence of the triangle from its angles -/

/-- **A spherical triangle with prescribed angles `α_i ∈ ]0, π[` exists** as soon as
`α_0 + α_1 + α_2 > π` and `α_i + α_j < π + α_k` (the conditions on the angles of a spherical
triangle: its polar triangle has sides `π − α_i`). The normals: `n_0 = (1, 0, 0)`,
`n_1 = (−cos α_2, sin α_2, 0)`, `n_2 = (−cos α_1, p, q)` with `q > 0`; `q² > 0` is
`|cos α_0 + cos α_1 cos α_2| < sin α_1 sin α_2`. -/
theorem exists_sphTriangle (α : Fin 3 → ℝ) (hpos : ∀ i, 0 < α i) (hlt : ∀ i, α i < π)
    (hsum : π < α 0 + α 1 + α 2) (h01 : α 0 + α 1 < π + α 2) (h02 : α 0 + α 2 < π + α 1)
    (h12 : α 1 + α 2 < π + α 0) : ∃ t : SphTriangle, t.α = α := by
  set c := fun i => Real.cos (α i) with hc
  set sn := fun i => Real.sin (α i) with hsn
  have hs : ∀ i, 0 < sn i := fun i => Real.sin_pos_of_pos_of_lt_pi (hpos i) (hlt i)
  have hcs : ∀ i, sn i ^ 2 + c i ^ 2 = 1 := fun i => Real.sin_sq_add_cos_sq _
  -- `|c 0 + c 1 c 2| < s 1 s 2`
  have hup : c 0 + c 1 * c 2 < sn 1 * sn 2 := by
    have h : Real.cos (α 0) < Real.cos (|α 1 + α 2 - π|) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (hlt 0).le
      rw [abs_lt]; constructor <;> linarith
    rw [Real.cos_abs, Real.cos_sub_pi, Real.cos_add] at h
    simp only [hc, hsn]; linarith
  have hlo : -(sn 1 * sn 2) < c 0 + c 1 * c 2 := by
    have h : Real.cos (π - |α 1 - α 2|) < Real.cos (α 0) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (hpos 0).le (by linarith [abs_nonneg (α 1 - α 2)])
      have : |α 1 - α 2| < π - α 0 := by rw [abs_lt]; constructor <;> linarith
      linarith
    rw [Real.cos_pi_sub, Real.cos_abs, Real.cos_sub] at h
    simp only [hc, hsn]; linarith
  set p := -(c 0 + c 1 * c 2) / sn 2 with hp
  have hq2 : 0 < 1 - c 1 ^ 2 - p ^ 2 := by
    have h1 : (c 0 + c 1 * c 2) ^ 2 < (sn 1 * sn 2) ^ 2 := by
      have := mul_pos (sub_pos.2 hup) (sub_pos.2 hlo)
      nlinarith
    have e : sn 1 ^ 2 = 1 - c 1 ^ 2 := by linarith [hcs 1]
    have h2 : 1 - c 1 ^ 2 - p ^ 2 = ((sn 1 * sn 2) ^ 2 - (c 0 + c 1 * c 2) ^ 2) / sn 2 ^ 2 := by
      have := (hs 2).ne'
      rw [hp, mul_pow, e]; field_simp
    rw [h2]; exact div_pos (by linarith) (by have := hs 2; positivity)
  set q := Real.sqrt (1 - c 1 ^ 2 - p ^ 2) with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 hq2
  have hqq : q ^ 2 = 1 - c 1 ^ 2 - p ^ 2 := Real.sq_sqrt hq2.le
  refine ⟨⟨α, ![![1, 0, 0], ![-c 2, sn 2, 0], ![-c 1, p, q]], hpos, hlt, ?_, ?_, ?_⟩, rfl⟩
  · intro k; fin_cases k <;> simp [dotProduct, Fin.sum_univ_three] <;> nlinarith [hcs 2]
  · have h2 := (hs 2).ne'
    intro i; fin_cases i
    · simp [dotProduct, Fin.sum_univ_three, hp]
      field_simp
      simp only [hc]; ring
    · simp [dotProduct, Fin.sum_univ_three, hc]
    · simp [dotProduct, Fin.sum_univ_three, hc]
  · rw [Matrix.det_fin_three]
    simp
    exact mul_pos (hs 2) hqpos

end Triangle

/-! ### Folding the plane onto a sector -/

section PolarFold

/-- The angle `(α/π) arccos(Re h / |h|) ∈ [0, α]` of the folded point. -/
def foldAngle (α : ℝ) (h : ℂ) : ℝ := α / π * Real.arccos (h.re / ‖h‖)

/-- **The folding of the plane onto the closed sector of angle `α`**: `h = r e^{iφ}`,
`φ ∈ [−π, π]`, goes to `r e^{iα|φ|/π}`. -/
def polarFold (α : ℝ) (h : ℂ) : ℂ := (‖h‖ : ℂ) * Complex.exp ((foldAngle α h : ℂ) * Complex.I)

variable {α : ℝ}

theorem foldAngle_nonneg (hα : 0 ≤ α) (h : ℂ) : 0 ≤ foldAngle α h :=
  mul_nonneg (div_nonneg hα Real.pi_pos.le) (Real.arccos_nonneg _)

theorem foldAngle_le (hα : 0 ≤ α) (h : ℂ) : foldAngle α h ≤ α := by
  unfold foldAngle
  have := Real.arccos_le_pi (h.re / ‖h‖)
  calc α / π * Real.arccos (h.re / ‖h‖) ≤ α / π * π :=
        mul_le_mul_of_nonneg_left this (div_nonneg hα Real.pi_pos.le)
    _ = α := by field_simp

theorem norm_polarFold (h : ℂ) : ‖polarFold α h‖ = ‖h‖ := by
  rw [polarFold, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]

theorem polarFold_re (h : ℂ) : (polarFold α h).re = ‖h‖ * Real.cos (foldAngle α h) := by
  rw [polarFold, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem polarFold_im (h : ℂ) : (polarFold α h).im = ‖h‖ * Real.sin (foldAngle α h) := by
  rw [polarFold, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

@[simp] theorem polarFold_zero : polarFold α 0 = 0 := by simp [polarFold]

theorem polarFold_conj (h : ℂ) : polarFold α ((starRingEnd ℂ) h) = polarFold α h := by
  simp [polarFold, foldAngle]

theorem continuous_polarFold : Continuous (polarFold α) := by
  refine continuous_iff_continuousAt.2 fun h => ?_
  by_cases h0 : h = 0
  · subst h0
    rw [ContinuousAt, polarFold_zero]
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simp_rw [norm_polarFold]
    simpa using (continuous_norm (E := ℂ)).tendsto 0
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 h0
    have hq : ContinuousAt (fun h : ℂ => h.re / ‖h‖) h :=
      Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hn
    have hf : ContinuousAt (foldAngle α) h :=
      continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp hq)
    exact (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt).mul
      (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp hf).mul continuousAt_const))

/-- Polar coordinates on the closed upper half-plane: `v = |v| e^{i arccos(Re v / |v|)}`. -/
theorem eq_norm_mul_exp_arccos {v : ℂ} (hv : 0 ≤ v.im) :
    v = (‖v‖ : ℂ) * Complex.exp ((Real.arccos (v.re / ‖v‖) : ℂ) * Complex.I) := by
  by_cases h0 : v = 0
  · simp [h0]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  have hsq : v.re ^ 2 + v.im ^ 2 = ‖v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : -1 ≤ v.re / ‖v‖ := by
    rw [le_div_iff₀ hn]; nlinarith [sq_nonneg (v.re + ‖v‖), sq_nonneg v.im]
  have h2 : v.re / ‖v‖ ≤ 1 := by
    rw [div_le_iff₀ hn]; nlinarith [sq_nonneg (v.re - ‖v‖), sq_nonneg v.im]
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_arccos h1 h2]
    field_simp
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_arccos]
    have : 1 - (v.re / ‖v‖) ^ 2 = (v.im / ‖v‖) ^ 2 := by
      field_simp; linarith
    rw [this, Real.sqrt_sq (div_nonneg hv hn.le)]
    field_simp

theorem polarFold_sector_re (h : ℂ) :
    Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im =
      ‖h‖ * Real.sin (α - foldAngle α h) := by
  rw [polarFold_re, polarFold_im, Real.sin_sub]; ring

theorem re_div_norm_mem {h : ℂ} (h0 : h ≠ 0) : -1 ≤ h.re / ‖h‖ ∧ h.re / ‖h‖ ≤ 1 := by
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 + h.im ^ 2 = ‖h‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  constructor
  · rw [le_div_iff₀ hn]; nlinarith [sq_nonneg (h.re + ‖h‖), sq_nonneg h.im]
  · rw [div_le_iff₀ hn]; nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg h.im]

variable (hα0 : 0 < α) (hαπ : α < π)
include hα0 hαπ

/-- The folded point lies in the closed sector `{Im ≥ 0} ∩ {sin α Re − cos α Im ≥ 0}`. -/
theorem polarFold_mem_sector (h : ℂ) :
    0 ≤ (polarFold α h).im ∧
      0 ≤ Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im := by
  have hb0 := foldAngle_nonneg hα0.le h
  have hb1 := foldAngle_le hα0.le h
  rw [polarFold_sector_re, polarFold_im]
  exact ⟨mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi hb0 (by linarith)),
    mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))⟩

/-- Off the real axis, the folded point lies in the open sector. -/
theorem polarFold_mem_sector_strict {h : ℂ} (hh : h.im ≠ 0) :
    0 < (polarFold α h).im ∧
      0 < Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im := by
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
  have hb0 : 0 < foldAngle α h := mul_pos (div_pos hα0 Real.pi_pos) ha0
  have hb1 : foldAngle α h < α := by
    unfold foldAngle
    calc α / π * Real.arccos (h.re / ‖h‖) < α / π * π :=
          mul_lt_mul_of_pos_left haπ (div_pos hα0 Real.pi_pos)
      _ = α := by field_simp
  rw [polarFold_sector_re, polarFold_im]
  exact ⟨mul_pos hn (Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith)),
    mul_pos hn (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))⟩

/-- On the boundary of the sector, the point comes from the real axis. -/
theorem im_eq_zero_of_polarFold {h : ℂ}
    (hb : (polarFold α h).im = 0 ∨
      Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0) : h.im = 0 := by
  by_contra hh
  have := polarFold_mem_sector_strict hα0 hαπ hh
  rcases hb with hb | hb <;> linarith [this.1, this.2]

omit hα0 hαπ in
/-- On the real axis, the folded point is on the boundary of the sector. -/
theorem polarFold_boundary {h : ℂ} (hh : h.im = 0) :
    (polarFold α h).im = 0 ∨
      Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0 := by
  by_cases h0 : h = 0
  · left; rw [h0, polarFold_zero]; rfl
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 = ‖h‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hh]; ring
  rcases le_or_gt 0 h.re with hr | hr
  · left
    have : h.re = ‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
    rw [polarFold_im, foldAngle, this, div_self hn.ne', Real.arccos_one, mul_zero, Real.sin_zero,
      mul_zero]
  · right
    have : h.re = -‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
    rw [polarFold_sector_re, foldAngle, this, neg_div, div_self hn.ne', Real.arccos_neg_one]
    field_simp
    simp

/-- **The fold is injective up to conjugation.** -/
theorem polarFold_eq_iff {h h' : ℂ} (he : polarFold α h = polarFold α h') :
    h' = h ∨ h' = (starRingEnd ℂ) h := by
  have hn : ‖h‖ = ‖h'‖ := by rw [← norm_polarFold (α := α) h, he, norm_polarFold]
  by_cases h0 : h = 0
  · left; rw [h0, norm_zero] at hn; rw [h0]; exact norm_eq_zero.1 hn.symm
  have h0' : h' ≠ 0 := fun e => h0 (norm_eq_zero.1 (by rw [hn, e, norm_zero]))
  have hnp : 0 < ‖h‖ := norm_pos_iff.2 h0
  -- the angles agree
  have hc : Real.cos (foldAngle α h) = Real.cos (foldAngle α h') := by
    have e1 := congrArg Complex.re he
    rw [polarFold_re, polarFold_re, hn] at e1
    exact mul_left_cancel₀ (hn ▸ hnp).ne' e1
  have hb : foldAngle α h = foldAngle α h' :=
    Real.injOn_cos ⟨foldAngle_nonneg hα0.le h, (foldAngle_le hα0.le h).trans hαπ.le⟩
      ⟨foldAngle_nonneg hα0.le h', (foldAngle_le hα0.le h').trans hαπ.le⟩ hc
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

/-- **The fold is onto the closed sector**, from the closed upper half-plane. -/
theorem exists_polarFold_eq {v : ℂ} (h1 : 0 ≤ v.im)
    (h2 : 0 ≤ Real.sin α * v.re - Real.cos α * v.im) : ∃ h : ℂ, polarFold α h = v ∧ 0 ≤ h.im := by
  by_cases h0 : v = 0
  · exact ⟨0, by rw [h0, polarFold_zero], le_rfl⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  set γ := Real.arccos (v.re / ‖v‖) with hγ
  have hv := eq_norm_mul_exp_arccos h1
  have hγ0 : 0 ≤ γ := Real.arccos_nonneg _
  have hγπ : γ ≤ π := Real.arccos_le_pi _
  -- `γ ≤ α`
  have hγα : γ ≤ α := by
    by_contra hlt
    rw [not_le] at hlt
    have hs : Real.sin (α - γ) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    have : Real.sin α * v.re - Real.cos α * v.im = ‖v‖ * Real.sin (α - γ) := by
      have e1 := congrArg Complex.re hv
      have e2 := congrArg Complex.im hv
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at e1
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at e2
      rw [Real.sin_sub]
      nth_rewrite 1 [e1]; nth_rewrite 1 [e2]; ring
    nlinarith
  set κ := π / α * γ with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (div_nonneg Real.pi_pos.le hα0.le) hγ0
  have hκπ : κ ≤ π := by
    rw [hκ, div_mul_eq_mul_div, div_le_iff₀ hα0]; nlinarith [Real.pi_pos]
  refine ⟨(‖v‖ : ℂ) * Complex.exp ((κ : ℂ) * Complex.I), ?_, ?_⟩
  · have hnh : ‖(‖v‖ : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)‖ = ‖v‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _)]
    have hre : ((‖v‖ : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)).re = ‖v‖ * Real.cos κ := by
      rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hf : foldAngle α ((‖v‖ : ℂ) * Complex.exp ((κ : ℂ) * Complex.I)) = γ := by
      rw [foldAngle, hnh, hre, mul_div_cancel_left₀ _ hn.ne', Real.arccos_cos hκ0 hκπ, hκ]
      field_simp
    rw [polarFold, hnh, hf]
    exact hv.symm
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi hκ0 hκπ)

/-- Inside the open sector, the fold is onto from the open lower half-plane. -/
theorem exists_polarFold_eq_neg {v : ℂ} (h1 : 0 < v.im)
    (h2 : 0 < Real.sin α * v.re - Real.cos α * v.im) : ∃ h : ℂ, polarFold α h = v ∧ h.im < 0 := by
  obtain ⟨h, hv, hi⟩ := exists_polarFold_eq hα0 hαπ h1.le h2.le
  refine ⟨(starRingEnd ℂ) h, by rw [polarFold_conj, hv], ?_⟩
  rw [Complex.conj_im, neg_lt_zero]
  rcases hi.lt_or_eq with hi | hi
  · exact hi
  · exfalso
    have := polarFold_boundary (α := α) hi.symm
    rw [hv] at this
    rcases this with h | h <;> linarith

omit hα0 hαπ in
theorem foldAngle_ofReal_mul {r : ℝ} (hr : 0 < r) (h : ℂ) :
    foldAngle α ((r : ℂ) * h) = foldAngle α h := by
  rw [foldAngle, foldAngle, Complex.re_ofReal_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le, mul_div_mul_left _ _ hr.ne']

omit hα0 hαπ in
theorem polarFold_ofReal_mul {r : ℝ} (hr : 0 ≤ r) (h : ℂ) :
    polarFold α ((r : ℂ) * h) = (r : ℂ) * polarFold α h := by
  rcases hr.lt_or_eq with hr | hr
  · rw [polarFold, polarFold, foldAngle_ofReal_mul hr, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    push_cast; ring
  · subst hr; simp

omit hα0 hαπ in
theorem cplx_one_posEmb (q : PolarHalfPlane) :
    DInfty.cplx 1 (DInfty.posEmb q) =
      (q.1.1 : ℂ) * Complex.exp (((2 * π * q.1.2 : ℝ) : ℂ) * Complex.I) := by
  simp [DInfty.cplx]

omit hα0 hαπ in
/-- The fold read on the cover, on the upper sheet `φ ∈ [n, n + 1/2]`. -/
theorem foldAngle_cover_up (q : PolarHalfPlane) {n : ℤ} (h1 : (n : ℝ) ≤ q.1.2)
    (h2 : q.1.2 ≤ n + 1 / 2) :
    foldAngle α (DInfty.cplx 1 (DInfty.posEmb q)) = 2 * α * (q.1.2 - n) := by
  rw [cplx_one_posEmb, foldAngle_ofReal_mul q.2, foldAngle, Complex.norm_exp_ofReal_mul_I,
    div_one, Complex.exp_ofReal_mul_I_re]
  have hc : Real.cos (2 * π * q.1.2) = Real.cos (2 * π * (q.1.2 - n)) := by
    rw [← Real.cos_sub_int_mul_two_pi (2 * π * q.1.2) n]; ring_nf
  rw [hc, Real.arccos_cos (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  field_simp

omit hα0 hαπ in
/-- The fold read on the cover, on the lower sheet `φ ∈ [n − 1/2, n]`. -/
theorem foldAngle_cover_down (q : PolarHalfPlane) {n : ℤ} (h1 : (n : ℝ) - 1 / 2 ≤ q.1.2)
    (h2 : q.1.2 ≤ n) : foldAngle α (DInfty.cplx 1 (DInfty.posEmb q)) = 2 * α * (n - q.1.2) := by
  rw [cplx_one_posEmb, foldAngle_ofReal_mul q.2, foldAngle, Complex.norm_exp_ofReal_mul_I,
    div_one, Complex.exp_ofReal_mul_I_re]
  have hc : Real.cos (2 * π * q.1.2) = Real.cos (2 * π * (n - q.1.2)) := by
    rw [← Real.cos_neg, ← Real.cos_sub_int_mul_two_pi (-(2 * π * q.1.2)) (-n)]; push_cast; ring_nf
  rw [hc, Real.arccos_cos (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  field_simp

omit hα0 hαπ in
theorem polarFold_cover (q : PolarHalfPlane) :
    polarFold α (DInfty.cplx 1 (DInfty.posEmb q)) =
      (q.1.1 : ℂ) *
        Complex.exp ((foldAngle α (DInfty.cplx 1 (DInfty.posEmb q)) : ℂ) * Complex.I) := by
  rw [polarFold, DInfty.norm_cplx, DInfty.posEmb_r]

end PolarFold

/-! ### The topological model: the double of the triangle is the round sphere -/

section Model

namespace SphTriangle

variable (t : SphTriangle)

/-- The three half-spheres bounding the triangle, read in the stereographic chart at `v_0`:
`⟨n_k, R_0⁻¹ stereoInv v⟩ = G_k(v) / (1 + |v|²)`, `G_k = gfun (cK k)`. -/
def cK (k : Fin 3) : Fin 3 → ℝ := t.A 0 *ᵥ t.n k

theorem cK_dot_self (k : Fin 3) : t.cK k ⬝ᵥ t.cK k = 1 := by
  rw [cK, dot_mulVec_self (t.A_transpose_mul 0), t.unit]

theorem cK_zero_nonneg (k : Fin 3) : 0 ≤ t.cK k 0 := by
  fin_cases k
  · exact (t.A_mulVec_n_zero_pos 0).le
  · have h := t.A_mulVec_n_add_one 0
    show 0 ≤ (t.A 0 *ᵥ t.n (0 + 1)) 0
    rw [h]; simp
  · have h := t.A_mulVec_n_add_two 0
    show 0 ≤ (t.A 0 *ᵥ t.n (0 + 2)) 0
    rw [h]; simp

/-- **The triangle in the stereographic chart at `v_0`**, `K = {v : G_k(v) ≥ 0, k = 0, 1, 2}`:
two half-planes through `0` (the sides at `v_0`) and a disc (the opposite side). -/
def K : Set ℂ := {v | ∀ k, 0 ≤ gfun (t.cK k) v}

theorem mem_T_iff (v : ℂ) : (t.R 0)⁻¹ • stereoInv v ∈ t.T ↔ v ∈ t.K := by
  have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  simp only [T, K, mem_setOf_eq, t.dot_vec_R_inv_stereoInv, cK]
  exact forall_congr' fun k => by rw [le_div_iff₀ hD, zero_mul]

theorem gfun_add (c : Fin 3 → ℝ) (v u : ℂ) :
    gfun c (v + u) = gfun c v + 2 * ((c 1 - c 0 * v.re) * u.re + (c 2 - c 0 * v.im) * u.im) -
      c 0 * ‖u‖ ^ 2 := by
  simp only [gfun, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem convex_gfun_nonneg {c : Fin 3 → ℝ} (hc : 0 ≤ c 0) : Convex ℝ {v : ℂ | 0 ≤ gfun c v} := by
  intro v hv w hw a b ha hb hab
  simp only [mem_setOf_eq] at hv hw ⊢
  obtain rfl : b = 1 - a := by linarith
  have key : gfun c (a • v + (1 - a) • w) = a * gfun c v + (1 - a) * gfun c w +
      c 0 * a * (1 - a) * ((v.re - w.re) ^ 2 + (v.im - w.im) ^ 2) := by
    simp only [gfun, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  rw [key]
  have := mul_nonneg (mul_nonneg (mul_nonneg hc ha) hb)
    (add_nonneg (sq_nonneg (v.re - w.re)) (sq_nonneg (v.im - w.im)))
  nlinarith [mul_nonneg ha hv, mul_nonneg hb hw]

theorem convex_K : Convex ℝ t.K := by
  have : t.K = ⋂ k, {v : ℂ | 0 ≤ gfun (t.cK k) v} := by ext v; simp [K]
  rw [this]
  exact convex_iInter fun k => convex_gfun_nonneg (t.cK_zero_nonneg k)

theorem isClosed_K : IsClosed t.K := by
  have : t.K = ⋂ k, {v : ℂ | 0 ≤ gfun (t.cK k) v} := by ext v; simp [K]
  rw [this]
  exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_gfun _)

theorem isBounded_K : Bornology.IsBounded t.K := by
  set a := t.cK 0 0
  have ha : 0 < a := t.A_mulVec_n_zero_pos 0
  have h1 := t.cK_dot_self 0
  simp only [dotProduct, Fin.sum_univ_three] at h1
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (t.cK 0 1), sq_nonneg (t.cK 0 2)]
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / a)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hv0 := hv 0
  simp only [gfun] at hv0
  have hsq : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hcs : (t.cK 0 1 * v.re + t.cK 0 2 * v.im) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (t.cK 0 1 * v.im - t.cK 0 2 * v.re), sq_nonneg (t.cK 0 1),
      sq_nonneg (t.cK 0 2), sq_nonneg v.re, sq_nonneg v.im]
  have hcs' : t.cK 0 1 * v.re + t.cK 0 2 * v.im ≤ ‖v‖ := by
    nlinarith [norm_nonneg v, sq_nonneg (t.cK 0 1 * v.re + t.cK 0 2 * v.im - ‖v‖)]
  rw [le_div_iff₀ ha]
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg v]

theorem interior_K_nonempty : (interior t.K).Nonempty := by
  set a := t.cK 0 0
  have ha : 0 < a := t.A_mulVec_n_zero_pos 0
  have h1 := t.cK_dot_self 0
  simp only [dotProduct, Fin.sum_univ_three] at h1
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (t.cK 0 1), sq_nonneg (t.cK 0 2)]
  set β := t.α 0 / 2
  set ε := a / 4
  have hε : 0 < ε := by positivity
  set v : ℂ := (ε : ℂ) * Complex.exp ((β : ℂ) * Complex.I)
  have hvre : v.re = ε * Real.cos β := by rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hvim : v.im = ε * Real.sin β := by rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hvn : ‖v‖ = ε := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hε.le]
  have hβ0 : 0 < β := by have := t.α_pos 0; positivity
  have hβπ : β < π := by have := t.α_lt_pi 0; show t.α 0 / 2 < π; linarith [Real.pi_pos]
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ
  set U : Set ℂ := ⋂ k, {v : ℂ | 0 < gfun (t.cK k) v}
  have hUo : IsOpen U :=
    isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_gfun _)
  have hUK : U ⊆ t.K := fun w hw k => (mem_iInter.1 hw k).le
  refine ⟨v, interior_maximal hUK hUo (mem_iInter.2 fun k => ?_)⟩
  show 0 < gfun (t.cK k) v
  fin_cases k
  · show 0 < gfun (t.cK 0) v
    simp only [gfun, hvre, hvim, hvn]
    have hcs : (t.cK 0 1 * Real.cos β + t.cK 0 2 * Real.sin β) ^ 2 ≤ 1 := by
      have := Real.sin_sq_add_cos_sq β
      nlinarith [sq_nonneg (t.cK 0 1 * Real.sin β - t.cK 0 2 * Real.cos β)]
    have hcs' : -1 ≤ t.cK 0 1 * Real.cos β + t.cK 0 2 * Real.sin β := by
      nlinarith [sq_nonneg (t.cK 0 1 * Real.cos β + t.cK 0 2 * Real.sin β + 1)]
    show 0 < a * (1 - ε ^ 2) + 2 * (t.cK 0 1 * (ε * Real.cos β) + t.cK 0 2 * (ε * Real.sin β))
    have hX : -ε ≤ ε * (t.cK 0 1 * Real.cos β + t.cK 0 2 * Real.sin β) := by nlinarith
    have hεa : ε = a / 4 := rfl
    have hε2 : ε ^ 2 ≤ 1 / 16 := by rw [hεa]; nlinarith
    nlinarith
  · show 0 < gfun (t.cK 1) v
    have h := t.A_mulVec_n_add_one 0
    have hc : t.cK 1 = ![0, Real.sin (t.α 0), -Real.cos (t.α 0)] := h
    rw [hc]
    simp only [gfun, hvre, hvim]
    simp
    have : Real.sin (t.α 0) * Real.cos β - Real.cos (t.α 0) * Real.sin β = Real.sin β := by
      rw [← Real.sin_sub]; congr 1; ring
    nlinarith
  · show 0 < gfun (t.cK 2) v
    have h := t.A_mulVec_n_add_two 0
    have hc : t.cK 2 = ![0, 0, 1] := h
    rw [hc]
    simp only [gfun, hvim]
    simp
    positivity

/-- The homeomorphism of the plane taking the triangle `K` onto the closed unit disc
(`gaugeRescaleHomeomorph`, through mathlib's
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`). -/
def eK : ℂ ≃ₜ ℂ :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall t.convex_K t.interior_K_nonempty
    t.isBounded_K).choose

theorem eK_spec : t.eK '' interior t.K = Metric.ball 0 1 ∧
    t.eK '' closure t.K = Metric.closedBall 0 1 ∧
    t.eK '' frontier t.K = Metric.sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall t.convex_K t.interior_K_nonempty
    t.isBounded_K).choose_spec

theorem eK_image_K : t.eK '' t.K = Metric.closedBall 0 1 := by
  rw [← t.isClosed_K.closure_eq]; exact t.eK_spec.2.1

theorem mem_interior_K_iff (v : ℂ) : v ∈ interior t.K ↔ ‖t.eK v‖ < 1 := by
  rw [← mem_ball_zero_iff, ← t.eK_spec.1, t.eK.injective.mem_set_image]

/-- The open triangle in the chart, `G_k > 0`. -/
theorem gfun_pos_mem_interior_K {v : ℂ} (hv : ∀ k, 0 < gfun (t.cK k) v) : v ∈ interior t.K := by
  set U : Set ℂ := ⋂ k, {v : ℂ | 0 < gfun (t.cK k) v}
  have hUo : IsOpen U :=
    isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_gfun _)
  have hUK : U ⊆ t.K := fun w hw k => (mem_iInter.1 hw k).le
  exact interior_maximal hUK hUo (mem_iInter.2 hv)

/-- **A point of the chart where some `G_k ≤ 0` is not interior to `K`**: if `G_k(v) = 0`, moving
from `v` against the gradient of `G_k` leaves `K` at once. -/
theorem notMem_interior_K {v : ℂ} {k : Fin 3} (hk : gfun (t.cK k) v ≤ 0) : v ∉ interior t.K := by
  intro hv
  have hvK : v ∈ t.K := interior_subset hv
  have h0 : gfun (t.cK k) v = 0 := le_antisymm hk (hvK k)
  set c := t.cK k
  have hc0 : 0 ≤ c 0 := t.cK_zero_nonneg k
  have hc1 : c 0 * c 0 + c 1 * c 1 + c 2 * c 2 = 1 := by
    have := t.cK_dot_self k; simpa [dotProduct, Fin.sum_univ_three] using this
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
  have hK := interior_subset h1 k
  rw [gfun_add, h0] at hK
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

end SphTriangle

end Model

/-! ### The double of the triangle -/

section Double

namespace SphTriangle

variable (t : SphTriangle)

/-- **The double of the triangle**, as a space: the round sphere `𝕊²` (as for the football,
`GX.Football`). A point `(s, w)` (`s ∈ ℝ`, `|w| ≤ 1`) lies over the point
`R_0⁻¹ stereoInv (e_K⁻¹ w)` of the triangle (`SphTriangle.fold`), on the upper copy if `s ≥ 0`,
on the lower copy if `s ≤ 0`: the closed unit disc is the triangle (`e_K`), and `𝕊²` is the
double of the closed disc along its boundary circle `s = 0`. -/
def TriDouble (_t : SphTriangle) : Type := Sph2

instance : TopologicalSpace (TriDouble t) := inferInstanceAs (TopologicalSpace Sph2)

instance : T2Space (TriDouble t) := inferInstanceAs (T2Space Sph2)

instance : LocallyConnectedSpace (TriDouble t) := inferInstanceAs (LocallyConnectedSpace Sph2)

instance : SecondCountableTopology (TriDouble t) := inferInstanceAs (SecondCountableTopology Sph2)

instance : ConnectedSpace (TriDouble t) := inferInstanceAs (ConnectedSpace Sph2)

/-- The underlying point of `𝕊²`. -/
def toSph2 (y : t.TriDouble) : Sph2 := y

/-- A point of `𝕊²` as a point of the double. -/
def ofSph2 (y : Sph2) : t.TriDouble := y

/-- The double is `𝕊²` as a space. -/
def homeoSph2 : t.TriDouble ≃ₜ Sph2 := Homeomorph.refl Sph2

theorem continuous_toSph2 : Continuous t.toSph2 := continuous_id

theorem continuous_ofSph2 : Continuous t.ofSph2 := continuous_id

/-- The height `s` of a point of the double: `≥ 0` on the upper copy, `≤ 0` on the lower. -/
def height (y : t.TriDouble) : ℝ := ((t.toSph2 y : Sph2) : Euc3).fst

/-- The disc coordinate `w` of a point of the double. -/
def disc (y : t.TriDouble) : ℂ := ((t.toSph2 y : Sph2) : Euc3).snd

theorem height_sq_add (y : t.TriDouble) : t.height y ^ 2 + ‖t.disc y‖ ^ 2 = 1 := by
  rw [height, disc, ← norm_polarSum_sq, norm_raySphere, one_pow]

theorem continuous_height : Continuous t.height :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.fst).comp continuous_subtype_val

theorem continuous_disc : Continuous t.disc :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.snd).comp continuous_subtype_val

/-- **The folding map of the double onto the triangle.** -/
def fold (y : t.TriDouble) : Sph2 := (t.R 0)⁻¹ • stereoInv (t.eK.symm (t.disc y))

theorem continuous_fold : Continuous t.fold :=
  (continuous_const_smul _).comp
    (continuous_stereoInv.comp (t.eK.symm.continuous.comp t.continuous_disc))

/-- The disc coordinate of a point of the sphere. -/
def wK (x : Sph2) : ℂ := t.eK (stereoFun (t.R 0 • x))

theorem eK_symm_disc_mem_K (y : t.TriDouble) : t.eK.symm (t.disc y) ∈ t.K := by
  have h : t.disc y ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]
    have := t.height_sq_add y
    nlinarith [norm_nonneg (t.disc y), sq_nonneg (t.height y)]
  rw [← t.eK_image_K] at h
  obtain ⟨v, hv, hve⟩ := h
  rw [← hve, Homeomorph.symm_apply_apply]; exact hv

theorem fold_mem_T (y : t.TriDouble) : t.fold y ∈ t.T :=
  (t.mem_T_iff _).2 (t.eK_symm_disc_mem_K y)

theorem fst_ne_of_mem_T {x : Sph2} (hx : x ∈ t.T) : ((t.R 0 • x : Sph2) : Euc3).fst ≠ -1 := by
  intro h
  have hv := vec_dot_self (t.R 0 • x)
  have hvec : vec (t.R 0 • x) = ![-1, 0, 0] := by
    rw [vec_apply] at hv ⊢
    simp only [dotProduct, Fin.sum_univ_three, h] at hv
    simp at hv
    have h1 : ((t.R 0 • x : Sph2) : Euc3).snd.re = 0 := by nlinarith
    have h2 : ((t.R 0 • x : Sph2) : Euc3).snd.im = 0 := by nlinarith
    rw [h, h1, h2]
  have h0 := hx 0
  have e : x = (t.R 0)⁻¹ • (t.R 0 • x) := (inv_smul_smul _ _).symm
  rw [e, t.dot_vec_R_inv_smul, hvec] at h0
  have := t.A_mulVec_n_zero_pos 0
  simp [dotProduct, Fin.sum_univ_three] at h0
  linarith

theorem stereoInv_stereoFun_R {x : Sph2} (hx : x ∈ t.T) :
    stereoInv (stereoFun (t.R 0 • x)) = t.R 0 • x :=
  stereoInv_stereoFun _ (t.fst_ne_of_mem_T hx)

theorem stereoFun_mem_K {x : Sph2} (hx : x ∈ t.T) : stereoFun (t.R 0 • x) ∈ t.K := by
  rw [← t.mem_T_iff, t.stereoInv_stereoFun_R hx, inv_smul_smul]; exact hx

theorem wK_fold (y : t.TriDouble) : t.wK (t.fold y) = t.disc y := by
  rw [wK, fold, smul_inv_smul, stereoFun_stereoInv, Homeomorph.apply_symm_apply]

theorem norm_wK_le {x : Sph2} (hx : x ∈ t.T) : ‖t.wK x‖ ≤ 1 := by
  have : t.wK x ∈ t.eK '' t.K := ⟨_, t.stereoFun_mem_K hx, rfl⟩
  rw [t.eK_image_K, mem_closedBall_zero_iff] at this
  exact this

/-- The pairings with the normals, in the chart at `v_0`. -/
theorem dot_vec_eq_gfun {x : Sph2} (hS : ((t.R 0 • x : Sph2) : Euc3).fst ≠ -1) (k : Fin 3) :
    t.n k ⬝ᵥ vec x = gfun (t.cK k) (stereoFun (t.R 0 • x)) /
      (1 + ‖stereoFun (t.R 0 • x)‖ ^ 2) := by
  conv_lhs => rw [← inv_smul_smul (t.R 0) x, ← stereoInv_stereoFun _ hS]
  rw [t.dot_vec_R_inv_stereoInv]; rfl

/-- **Interior points of the triangle have disc coordinate in the open disc.** -/
theorem norm_wK_lt {x : Sph2} (hx : x ∈ t.T) (hpos : ∀ k, 0 < t.n k ⬝ᵥ vec x) : ‖t.wK x‖ < 1 := by
  rw [wK, ← t.mem_interior_K_iff]
  refine t.gfun_pos_mem_interior_K fun k => ?_
  have h := hpos k
  rw [t.dot_vec_eq_gfun (t.fst_ne_of_mem_T hx)] at h
  have hD : (0 : ℝ) < 1 + ‖stereoFun (t.R 0 • x)‖ ^ 2 := by positivity
  exact (div_pos_iff_of_pos_right hD).1 h

/-- **Points outside the open triangle have disc coordinate outside the open disc.** -/
theorem one_le_norm_wK {x : Sph2} (hS : ((t.R 0 • x : Sph2) : Euc3).fst ≠ -1) {k : Fin 3}
    (hk : t.n k ⬝ᵥ vec x ≤ 0) : 1 ≤ ‖t.wK x‖ := by
  rw [wK]
  by_contra hlt
  rw [not_le, ← t.mem_interior_K_iff] at hlt
  rw [t.dot_vec_eq_gfun hS] at hk
  have hD : (0 : ℝ) < 1 + ‖stereoFun (t.R 0 • x)‖ ^ 2 := by positivity
  have hg : gfun (t.cK k) (stereoFun (t.R 0 • x)) ≤ 0 := by
    by_contra h; rw [not_le] at h; exact absurd (div_pos h hD) (not_lt.2 hk)
  exact t.notMem_interior_K hg hlt

theorem norm_wK_eq_one_iff {x : Sph2} (hx : x ∈ t.T) : ‖t.wK x‖ = 1 ↔ ∃ k, t.n k ⬝ᵥ vec x = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have := t.norm_wK_lt hx fun k => lt_of_le_of_ne (hx k) (hne k).symm
    linarith
  · rintro ⟨k, hk⟩
    exact le_antisymm (t.norm_wK_le hx) (t.one_le_norm_wK (t.fst_ne_of_mem_T hx) hk.le)

end SphTriangle

end Double

/-! ### Open embeddings from a compact neighbourhood -/

section CompactOpen

/-- **An injective continuous map on an open set `V`, extending continuously to a compact
`K ⊇ V` whose extra points avoid `f(V)`, is an open map on `V` as soon as `f(V)` is open**:
`f(U) = f(V) ∖ f(K ∖ U)` for `U ⊆ V` open, and `f(K ∖ U)` is compact. -/
theorem isOpenMap_restrict_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {K V : Set X} (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    (hf : ContinuousOn f K)
    (hinj : InjOn f V) (hopen : IsOpen (f '' V)) (hdisj : ∀ x ∈ K, x ∉ V → f x ∉ f '' V) :
    IsOpenMap (V.restrict f) := by
  intro U hU
  have hU' : IsOpen (Subtype.val '' U : Set X) := hV.isOpenMap_subtype_val U hU
  have himg : V.restrict f '' U = f '' (Subtype.val '' U) := by
    rw [image_image]; rfl
  have hUV : Subtype.val '' U ⊆ V := Subtype.coe_image_subset V U
  have heq : f '' (Subtype.val '' U) = f '' V \ f '' (K \ Subtype.val '' U) := by
    ext y
    constructor
    · rintro ⟨x, hxU, rfl⟩
      refine ⟨⟨x, hUV hxU, rfl⟩, ?_⟩
      rintro ⟨x', ⟨hx'K, hx'U⟩, hfx'⟩
      by_cases hx'V : x' ∈ V
      · exact hx'U (hinj hx'V (hUV hxU) hfx' ▸ hxU)
      · exact hdisj x' hx'K hx'V ⟨x, hUV hxU, hfx'.symm⟩
    · rintro ⟨⟨x, hxV, rfl⟩, hnot⟩
      by_contra hx
      have hxU : x ∉ Subtype.val '' U := fun h => hx ⟨x, h, rfl⟩
      exact hnot ⟨x, ⟨hVK hxV, hxU⟩, rfl⟩
  rw [himg, heq]
  exact hopen.sdiff ((hK.diff hU').image_of_continuousOn (hf.mono sdiff_subset)).isClosed

end CompactOpen

/-! ### The charts of the double at the vertices -/

section VertexCharts

namespace SphTriangle

variable (t : SphTriangle)

/-- **The point of the triangle with polar coordinates `h` at `v_i`**: `h = r e^{iφ}` goes to the
point at stereographic radius `r` from `v_i` in the direction of angle `α_i |φ| / π` from the side
`e_{i+2}`. -/
def xv (i : Fin 3) (h : ℂ) : Sph2 := (t.R i)⁻¹ • stereoInv (polarFold (t.α i) h)

theorem continuous_xv (i : Fin 3) : Continuous (t.xv i) :=
  (continuous_const_smul _).comp (continuous_stereoInv.comp continuous_polarFold)

theorem dot_xv (i k : Fin 3) (h : ℂ) :
    t.n k ⬝ᵥ vec (t.xv i h) = gfun (t.A i *ᵥ t.n k) (polarFold (t.α i) h) / (1 + ‖h‖ ^ 2) := by
  rw [xv, t.dot_vec_R_inv_stereoInv, norm_polarFold]

theorem dot_xv_add_two (i : Fin 3) (h : ℂ) :
    t.n (i + 2) ⬝ᵥ vec (t.xv i h) = 2 * (polarFold (t.α i) h).im / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_add_two]; simp [gfun]

theorem dot_xv_add_one (i : Fin 3) (h : ℂ) :
    t.n (i + 1) ⬝ᵥ vec (t.xv i h) = 2 * (Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im) / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_add_one]; simp [gfun]; ring

theorem dot_xv_add_two_nonneg (i : Fin 3) (h : ℂ) : 0 ≤ t.n (i + 2) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_add_two]
  have := (polarFold_mem_sector (t.α_pos i) (t.α_lt_pi i) h).1
  positivity

theorem dot_xv_add_one_nonneg (i : Fin 3) (h : ℂ) : 0 ≤ t.n (i + 1) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_add_one]
  have := (polarFold_mem_sector (t.α_pos i) (t.α_lt_pi i) h).2
  positivity

omit t in
theorem fin3_cases (i k : Fin 3) : k = i ∨ k = i + 1 ∨ k = i + 2 := by
  fin_cases i <;> fin_cases k <;> simp

theorem xv_mem_T_iff (i : Fin 3) (h : ℂ) : t.xv i h ∈ t.T ↔ 0 ≤ t.n i ⬝ᵥ vec (t.xv i h) := by
  refine ⟨fun hx => hx i, fun hx k => ?_⟩
  rcases fin3_cases i k with rfl | rfl | rfl
  · exact hx
  · exact t.dot_xv_add_one_nonneg i h
  · exact t.dot_xv_add_two_nonneg i h

theorem dot_xv_pos_of_im_ne_zero (i : Fin 3) {h : ℂ} (hh : h.im ≠ 0) :
    0 < t.n (i + 1) ⬝ᵥ vec (t.xv i h) ∧ 0 < t.n (i + 2) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_add_one, dot_xv_add_two]
  have := polarFold_mem_sector_strict (t.α_pos i) (t.α_lt_pi i) hh
  exact ⟨by have := this.2; positivity, by have := this.1; positivity⟩

theorem im_eq_zero_of_dot_xv (i : Fin 3) {h : ℂ}
    (hb : t.n (i + 1) ⬝ᵥ vec (t.xv i h) = 0 ∨ t.n (i + 2) ⬝ᵥ vec (t.xv i h) = 0) : h.im = 0 := by
  by_contra hh
  have := t.dot_xv_pos_of_im_ne_zero i hh
  rcases hb with hb | hb <;> linarith [this.1, this.2]

theorem dot_xv_boundary (i : Fin 3) {h : ℂ} (hh : h.im = 0) :
    t.n (i + 1) ⬝ᵥ vec (t.xv i h) = 0 ∨ t.n (i + 2) ⬝ᵥ vec (t.xv i h) = 0 := by
  rw [dot_xv_add_one, dot_xv_add_two]
  rcases polarFold_boundary (α := t.α i) hh with h1 | h1
  · right; rw [h1]; simp
  · left; rw [h1]; simp

/-- The domain `V_i ⊆ ℂ` of the chart at `v_i`: the points away from the opposite side. -/
def Vv (i : Fin 3) : Set ℂ := {h | 0 < t.n i ⬝ᵥ vec (t.xv i h)}

/-- Its compact closure `K_i`, the preimage of the triangle. -/
def Kv (i : Fin 3) : Set ℂ := {h | 0 ≤ t.n i ⬝ᵥ vec (t.xv i h)}

theorem isOpen_Vv (i : Fin 3) : IsOpen (t.Vv i) :=
  isOpen_lt continuous_const ((continuous_dot_vec _).comp (t.continuous_xv i))

theorem Vv_subset_Kv (i : Fin 3) : t.Vv i ⊆ t.Kv i := fun _ hx => by
  simp only [Vv, Kv, mem_setOf_eq] at hx ⊢; exact hx.le

theorem xv_mem_T {i : Fin 3} {h : ℂ} (hh : h ∈ t.Kv i) : t.xv i h ∈ t.T :=
  (t.xv_mem_T_iff i h).2 hh

theorem isCompact_Kv (i : Fin 3) : IsCompact (t.Kv i) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le continuous_const ((continuous_dot_vec _).comp (t.continuous_xv i))) ?_
  set c := t.A i *ᵥ t.n i
  have ha : 0 < c 0 := t.A_mulVec_n_zero_pos i
  have h1 : c ⬝ᵥ c = 1 := by rw [dot_mulVec_self (t.A_transpose_mul i), t.unit]
  simp only [dotProduct, Fin.sum_univ_three] at h1
  have ha1 : c 0 ≤ 1 := by nlinarith [sq_nonneg (c 1), sq_nonneg (c 2)]
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / c 0)).subset fun h hh => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh' : 0 ≤ gfun c (polarFold (t.α i) h) := by
    have := hh
    simp only [Kv, mem_setOf_eq, dot_xv] at this
    have hD : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
    rwa [le_div_iff₀ hD, zero_mul] at this
  set v := polarFold (t.α i) h
  have hvn : ‖v‖ = ‖h‖ := norm_polarFold h
  simp only [gfun] at hh'
  have hsq : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hcs : (c 1 * v.re + c 2 * v.im) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (c 1 * v.im - c 2 * v.re), sq_nonneg v.re, sq_nonneg v.im]
  have hcs' : c 1 * v.re + c 2 * v.im ≤ ‖v‖ := by
    nlinarith [norm_nonneg v, sq_nonneg (c 1 * v.re + c 2 * v.im - ‖v‖)]
  rw [← hvn, le_div_iff₀ ha]
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg v]

theorem xv_zero (i : Fin 3) : t.xv i 0 = (t.R i)⁻¹ • northPole := by
  rw [xv, polarFold_zero, stereoInv_zero]

theorem zero_mem_Vv (i : Fin 3) : (0 : ℂ) ∈ t.Vv i := by
  show 0 < t.n i ⬝ᵥ vec (t.xv i 0)
  rw [dot_xv, polarFold_zero]
  simp [gfun]
  exact t.A_mulVec_n_zero_pos i

/-- The `R_i`-stereographic coordinate of a point with `⟨n_i, x⟩ ≥ 0` is defined. -/
theorem fst_ne_of_dot_nonneg (i : Fin 3) {x : Sph2} (hx : 0 ≤ t.n i ⬝ᵥ vec x) :
    ((t.R i • x : Sph2) : Euc3).fst ≠ -1 := by
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
  have := t.A_mulVec_n_zero_pos i
  simp [dotProduct, Fin.sum_univ_three] at hx
  linarith

/-- The sheet of `h`: `1` on the closed upper half-plane, `−1` on the open lower one. -/
def sheet (h : ℂ) : ℝ := if 0 ≤ h.im then 1 else -1

theorem sheet_sq (h : ℂ) : sheet h ^ 2 = 1 := by
  unfold sheet; split_ifs <;> norm_num

/-- The point of the double, as a vector of `ℝ ⊕ ℂ`. -/
def chartVec (i : Fin 3) (h : ℂ) : Euc3 :=
  WithLp.toLp 2 (sheet h * √(1 - ‖t.wK (t.xv i h)‖ ^ 2), t.wK (t.xv i h))

/-- On the real axis of the chart, the point is on a side through `v_i`, so it is on the circle
`s = 0` of the double. -/
theorem sqrt_eq_zero_of_im_eq_zero (i : Fin 3) {h : ℂ}
    (hS : ((t.R 0 • t.xv i h : Sph2) : Euc3).fst ≠ -1) (hh : h.im = 0) :
    √(1 - ‖t.wK (t.xv i h)‖ ^ 2) = 0 := by
  rw [Real.sqrt_eq_zero']
  rcases t.dot_xv_boundary i hh with hb | hb
  · have := t.one_le_norm_wK hS hb.le; nlinarith
  · have := t.one_le_norm_wK hS hb.le; nlinarith

theorem norm_chartVec (i : Fin 3) {h : ℂ} (hh : h ∈ t.Kv i) : ‖t.chartVec i h‖ = 1 := by
  have hx := t.xv_mem_T hh
  have hle := t.norm_wK_le hx
  have hsq : ‖t.chartVec i h‖ ^ 2 = 1 := by
    rw [chartVec, norm_polarSum_sq]
    simp only [WithLp.fst, WithLp.snd]
    by_cases him : h.im = 0
    · rw [t.sqrt_eq_zero_of_im_eq_zero i (t.fst_ne_of_mem_T hx) him, mul_zero]
      have : ‖t.wK (t.xv i h)‖ = 1 := by
        have h0 := Real.sqrt_eq_zero'.1 (t.sqrt_eq_zero_of_im_eq_zero i (t.fst_ne_of_mem_T hx) him)
        nlinarith [norm_nonneg (t.wK (t.xv i h))]
      rw [this]; norm_num
    · rw [mul_pow, sheet_sq, one_mul, Real.sq_sqrt (by nlinarith [norm_nonneg (t.wK (t.xv i h))])]
      ring
  nlinarith [norm_nonneg (t.chartVec i h)]

/-- **The chart map at `v_i`**, `ℂ → TriDouble`: `h` goes to the point over `x_i(h)`, on the
sheet of `h` (the upper copy of the triangle for `Im h ≥ 0`). -/
def chartMap (i : Fin 3) (h : ℂ) : t.TriDouble :=
  if hh : ‖t.chartVec i h‖ = 1 then t.ofSph2 ⟨t.chartVec i h, mem_sphere_zero_iff_norm.2 hh⟩
  else t.ofSph2 northPole

theorem coe_chartMap (i : Fin 3) {h : ℂ} (hh : h ∈ t.Kv i) :
    ((t.toSph2 (t.chartMap i h) : Sph2) : Euc3) = t.chartVec i h := by
  rw [chartMap, dif_pos (t.norm_chartVec i hh)]; rfl

theorem disc_chartMap (i : Fin 3) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.disc (t.chartMap i h) = t.wK (t.xv i h) := by
  rw [disc, t.coe_chartMap i hh]; rfl

theorem height_chartMap (i : Fin 3) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.height (t.chartMap i h) = sheet h * √(1 - ‖t.wK (t.xv i h)‖ ^ 2) := by
  rw [height, t.coe_chartMap i hh]; rfl

theorem fold_chartMap (i : Fin 3) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.fold (t.chartMap i h) = t.xv i h := by
  have hx := t.xv_mem_T hh
  rw [fold, t.disc_chartMap i hh, wK, Homeomorph.symm_apply_apply, t.stereoInv_stereoFun_R hx,
    inv_smul_smul]

/-- The open set where the chart at `v_0` of the points `x_i(h)` is defined. -/
def Ov (i : Fin 3) : Set ℂ := {h | ((t.R 0 • t.xv i h : Sph2) : Euc3).fst ≠ -1}

theorem isOpen_Ov (i : Fin 3) : IsOpen (t.Ov i) :=
  isOpen_ne_fun (((WithLp.prod_continuous_ofLp 2 ℝ ℂ).fst.comp continuous_subtype_val).comp
    ((continuous_const_smul _).comp (t.continuous_xv i))) continuous_const

theorem Kv_subset_Ov (i : Fin 3) : t.Kv i ⊆ t.Ov i := fun _ hh => t.fst_ne_of_mem_T (t.xv_mem_T hh)

theorem continuousOn_wK_xv (i : Fin 3) : ContinuousOn (fun h => t.wK (t.xv i h)) (t.Ov i) := by
  refine t.eK.continuous.comp_continuousOn ?_
  refine continuousOn_stereoFun.comp
    ((continuous_const_smul _).comp (t.continuous_xv i)).continuousOn
    fun h hh => hh

theorem continuousOn_chartVec (i : Fin 3) : ContinuousOn (t.chartVec i) (t.Ov i) := by
  set f : ℂ → ℝ := fun h => √(1 - ‖t.wK (t.xv i h)‖ ^ 2)
  have hf : ContinuousOn f (t.Ov i) :=
    (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
      ((continuous_norm.comp_continuousOn (t.continuousOn_wK_xv i)).pow 2)))
  have hfs : ContinuousOn (fun h => sheet h * f h) (t.Ov i) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (t.Ov i).restrict (fun h => sheet h * f h) =
        fun h : t.Ov i => if (0 : ℝ) ≤ (h : ℂ).im then f h else -f h := by
      funext h; simp only [Set.restrict, sheet]; split_ifs <;> ring
    rw [heq]
    have hfr : Continuous fun h : t.Ov i => f h := continuousOn_iff_continuous_restrict.1 hf
    refine continuous_if_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
      hfr.continuousOn hfr.neg.continuousOn fun h heq => ?_
    have h0 : f h = 0 := t.sqrt_eq_zero_of_im_eq_zero i h.2 heq.symm
    show f h = -f h
    rw [h0, neg_zero]
  exact (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp_continuousOn (hfs.prodMk (t.continuousOn_wK_xv i))

theorem continuousOn_chartMap (i : Fin 3) : ContinuousOn (t.chartMap i) (t.Kv i) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (t.Kv i).restrict (t.chartMap i) = fun h : t.Kv i =>
      t.ofSph2 ⟨t.chartVec i h, mem_sphere_zero_iff_norm.2 (t.norm_chartVec i h.2)⟩ := by
    funext h; simp only [Set.restrict, chartMap, dif_pos (t.norm_chartVec i h.2)]
  rw [heq]
  exact t.continuous_ofSph2.comp
    ((continuousOn_iff_continuous_restrict.1 ((t.continuousOn_chartVec i).mono
      (t.Kv_subset_Ov i))).subtype_mk _)

/-- A point of the double is determined by its height and its disc coordinate. -/
theorem ext_height_disc {y y' : t.TriDouble} (h1 : t.height y = t.height y')
    (h2 : t.disc y = t.disc y') : y = y' := by
  have : ((t.toSph2 y : Sph2) : Euc3) = ((t.toSph2 y' : Sph2) : Euc3) := by
    have e : ∀ z : t.TriDouble,
        ((t.toSph2 z : Sph2) : Euc3) = WithLp.toLp 2 (t.height z, t.disc z) :=
      fun z => rfl
    rw [e, e, h1, h2]
  exact Subtype.ext this

/-- **The chart map is injective on `V_i`.** -/
theorem injOn_chartMap (i : Fin 3) : InjOn (t.chartMap i) (t.Vv i) := by
  intro h hh h' hh' he
  have hK := t.Vv_subset_Kv i hh
  have hK' := t.Vv_subset_Kv i hh'
  have hx : t.xv i h = t.xv i h' := by
    rw [← t.fold_chartMap i hK, ← t.fold_chartMap i hK', he]
  have hF : polarFold (t.α i) h = polarFold (t.α i) h' := by
    have := congrArg (fun y => stereoFun (t.R i • y)) hx
    simp only [xv, smul_inv_smul, stereoFun_stereoInv] at this
    exact this
  rcases polarFold_eq_iff (t.α_pos i) (t.α_lt_pi i) hF with rfl | hc
  · rfl
  · -- `h' = h̄`: then `h` is real
    have hheight := congrArg t.height he
    rw [t.height_chartMap i hK, t.height_chartMap i hK', ← hx] at hheight
    have him : h.im = 0 := by
      by_cases h0 : √(1 - ‖t.wK (t.xv i h)‖ ^ 2) = 0
      · have hT := t.xv_mem_T hK
        have h1 : ‖t.wK (t.xv i h)‖ = 1 := by
          have := Real.sqrt_eq_zero'.1 h0
          nlinarith [t.norm_wK_le hT, norm_nonneg (t.wK (t.xv i h))]
        obtain ⟨k, hk⟩ := (t.norm_wK_eq_one_iff hT).1 h1
        rcases fin3_cases i k with rfl | rfl | rfl
        · exact absurd hk (ne_of_gt hh)
        · exact t.im_eq_zero_of_dot_xv i (Or.inl hk)
        · exact t.im_eq_zero_of_dot_xv i (Or.inr hk)
      · have hs : sheet h = sheet h' := mul_right_cancel₀ h0 hheight
        rw [hc] at hs
        unfold sheet at hs
        rw [Complex.conj_im] at hs
        split_ifs at hs with h1 h2 h2 <;> linarith
    rw [hc]; exact Complex.ext rfl (by simp [him])

/-- The image of `V_i`: the points of the double over the triangle minus the side `e_i`. -/
def Uv (i : Fin 3) : Set t.TriDouble := {y | 0 < t.n i ⬝ᵥ vec (t.fold y)}

theorem isOpen_Uv (i : Fin 3) : IsOpen (t.Uv i) :=
  isOpen_lt continuous_const ((continuous_dot_vec _).comp t.continuous_fold)

/-- **The image of `V_i` under the chart map is `U_i`**: polar coordinates at `v_i`. -/
theorem chartMap_image_Vv (i : Fin 3) : t.chartMap i '' t.Vv i = t.Uv i := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    show 0 < t.n i ⬝ᵥ vec (t.fold (t.chartMap i h))
    rw [t.fold_chartMap i (t.Vv_subset_Kv i hh)]; exact hh
  · intro hy
    set x := t.fold y with hxdef
    have hxT : x ∈ t.T := t.fold_mem_T y
    have hS := t.fst_ne_of_dot_nonneg i (hxT i)
    set z := stereoFun (t.R i • x) with hz
    have hxz : x = (t.R i)⁻¹ • stereoInv z := by rw [hz, stereoInv_stereoFun _ hS, inv_smul_smul]
    have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have hdot : ∀ k, t.n k ⬝ᵥ vec x = gfun (t.A i *ᵥ t.n k) z / (1 + ‖z‖ ^ 2) := fun k => by
      rw [hxz, t.dot_vec_R_inv_stereoInv]
    have hz2 : t.n (i + 2) ⬝ᵥ vec x = 2 * z.im / (1 + ‖z‖ ^ 2) := by
      rw [hdot, t.A_mulVec_n_add_two]; simp [gfun]
    have hz1 : t.n (i + 1) ⬝ᵥ vec x = 2 * (Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im) /
        (1 + ‖z‖ ^ 2) := by
      rw [hdot, t.A_mulVec_n_add_one]; simp [gfun]; ring
    have hzi : 0 ≤ z.im := by
      have := hxT (i + 2); rw [hz2] at this
      have := (div_nonneg_iff.1 this); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
    have hzr : 0 ≤ Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
      have := hxT (i + 1); rw [hz1] at this
      have := (div_nonneg_iff.1 this); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
    -- the preimage `h`, on the sheet of `y`
    have hpre : ∃ h : ℂ, polarFold (t.α i) h = z ∧ (0 ≤ t.height y → 0 ≤ h.im) ∧
        (t.height y < 0 → h.im < 0) := by
      rcases le_or_gt 0 (t.height y) with hy0 | hy0
      · obtain ⟨h, h1, h2⟩ := exists_polarFold_eq (t.α_pos i) (t.α_lt_pi i) hzi hzr
        exact ⟨h, h1, fun _ => h2, fun h' => absurd hy0 (not_le.2 h')⟩
      · -- on the lower sheet the point is interior
        have hlt : ‖t.disc y‖ < 1 := by
          have := t.height_sq_add y
          nlinarith [norm_nonneg (t.disc y)]
        have hint : ∀ k, t.n k ⬝ᵥ vec x ≠ 0 := by
          intro k hk
          have := (t.norm_wK_eq_one_iff hxT).2 ⟨k, hk⟩
          rw [hxdef, t.wK_fold] at this
          linarith
        have hzi' : 0 < z.im := by
          have := lt_of_le_of_ne (hxT (i + 2)) (hint (i + 2)).symm
          rw [hz2] at this
          exact (div_pos_iff_of_pos_right hD).1 this |> fun h => by linarith
        have hzr' : 0 < Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
          have := lt_of_le_of_ne (hxT (i + 1)) (hint (i + 1)).symm
          rw [hz1] at this
          have := (div_pos_iff_of_pos_right hD).1 this
          linarith
        obtain ⟨h, h1, h2⟩ := exists_polarFold_eq_neg (t.α_pos i) (t.α_lt_pi i) hzi' hzr'
        exact ⟨h, h1, fun h' => absurd h' (not_le.2 hy0), fun _ => h2⟩
    obtain ⟨h, hF, hup, hdown⟩ := hpre
    have hxv : t.xv i h = x := by rw [xv, hF, hxz]
    have hhV : h ∈ t.Vv i := by show 0 < t.n i ⬝ᵥ vec (t.xv i h); rw [hxv]; exact hy
    refine ⟨h, hhV, ?_⟩
    have hK := t.Vv_subset_Kv i hhV
    refine t.ext_height_disc ?_ ?_
    · rw [t.height_chartMap i hK, hxv, hxdef, t.wK_fold]
      have hsq : 1 - ‖t.disc y‖ ^ 2 = t.height y ^ 2 := by
        have := t.height_sq_add y; linarith
      rw [hsq, Real.sqrt_sq_eq_abs]
      rcases le_or_gt 0 (t.height y) with hy0 | hy0
      · rw [sheet, if_pos (hup hy0), one_mul, abs_of_nonneg hy0]
      · rw [sheet, if_neg (not_le.2 (hdown hy0)), abs_of_neg hy0]; ring
    · rw [t.disc_chartMap i hK, hxv, hxdef, t.wK_fold]

theorem chartMap_mem_Uv_of_mem_Kv {i : Fin 3} {h : ℂ} (hh : h ∈ t.Kv i) :
    t.chartMap i h ∈ t.Uv i ↔ h ∈ t.Vv i := by
  show 0 < t.n i ⬝ᵥ vec (t.fold (t.chartMap i h)) ↔ _
  rw [t.fold_chartMap i hh]; rfl

theorem isOpenMap_chartMap (i : Fin 3) : IsOpenMap ((t.Vv i).restrict (t.chartMap i)) :=
  isOpenMap_restrict_of_isCompact (t.isCompact_Kv i) (t.isOpen_Vv i) (t.Vv_subset_Kv i)
    (t.continuousOn_chartMap i) (t.injOn_chartMap i)
    (by rw [t.chartMap_image_Vv]; exact t.isOpen_Uv i)
    (fun h hK hV hU => by
      rw [t.chartMap_image_Vv] at hU
      exact hV ((t.chartMap_mem_Uv_of_mem_Kv hK).1 hU))

/-- **The chart of the double at `v_i`**, an open partial homeomorphism `ℂ → TriDouble` with
source `V_i` and target `U_i` (`isOpenMap_restrict_of_isCompact`, through `K_i`). -/
def chartPH (i : Fin 3) : OpenPartialHomeomorph ℂ t.TriDouble :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict ((t.injOn_chartMap i).toPartialEquiv _ _)
    ((t.continuousOn_chartMap i).mono (t.Vv_subset_Kv i)) (t.isOpenMap_chartMap i)
    (t.isOpen_Vv i)

theorem chartPH_source (i : Fin 3) : (t.chartPH i).source = t.Vv i := rfl

theorem chartPH_target (i : Fin 3) : (t.chartPH i).target = t.Uv i := by
  show t.chartMap i '' t.Vv i = _
  exact t.chartMap_image_Vv i

theorem chartPH_apply (i : Fin 3) (h : ℂ) : t.chartPH i h = t.chartMap i h := rfl

end SphTriangle

end VertexCharts

/-! ### The cone charts and the comparison with the developing maps -/

section ConeCharts

namespace SphTriangle

variable (t : SphTriangle)

/-- The cone angle `θ_i = 2α_i` at `v_i`. -/
def θc (i : Fin 3) : ConeAngle := ⟨2 * t.α i, by have := t.α_pos i; positivity⟩

theorem θc_ne (i : Fin 3) : (t.θc i).1 ≠ 2 * π := by
  have := t.α_lt_pi i
  show 2 * t.α i ≠ 2 * π
  intro h; linarith

/-- **The chart of the double at `v_i`, from the cone `C_{θ_i}`**: an open partial homeomorphism
`C_{θ_i} → TriDouble`, the apex to `v_i`. -/
def Φ (i : Fin 3) : OpenPartialHomeomorph (SphCone (t.θc i)) t.TriDouble :=
  (SphCone.homeoComplex (t.θc i)).toOpenPartialHomeomorph.trans (t.chartPH i)

theorem Φ_apply (i : Fin 3) (c : SphCone (t.θc i)) :
    t.Φ i c = t.chartMap i (SphCone.homeoComplex (t.θc i) c) := rfl

theorem Φ_symm_apply (i : Fin 3) (y : t.TriDouble) :
    (t.Φ i).symm y = (SphCone.homeoComplex (t.θc i)).symm ((t.chartPH i).symm y) := rfl

theorem Φ_source (i : Fin 3) :
    (t.Φ i).source = SphCone.homeoComplex (t.θc i) ⁻¹' t.Vv i := by
  rw [Φ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    univ_inter]; rfl

theorem Φ_target (i : Fin 3) : (t.Φ i).target = t.Uv i := by
  rw [Φ, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ, chartPH_target]

theorem homeoComplex_apex (θ : ConeAngle) : SphCone.homeoComplex θ (SphCone.apex θ) = 0 := by
  show DInfty.cplx 1 DInfty.apex = 0
  exact DInfty.cplx_apex 1

theorem homeoComplex_mk_lift (θ : ConeAngle) (q : PolarHalfPlane) :
    SphCone.homeoComplex θ (SphCone.mk θ (polarHalfPlaneLift q)) =
      DInfty.cplx 1 (DInfty.posEmb q) :=
  rfl

theorem sphConeDev_lift (θ : ConeAngle) (q : PolarHalfPlane) :
    sphConeDev θ.1 (polarHalfPlaneLift q) =
      stereoInv ((q.1.1 : ℂ) * Complex.exp (((θ.1 * q.1.2 : ℝ) : ℂ) * Complex.I)) := by
  show stereoInv (DInfty.cplx (2 * π / θ.1) (DInfty.posEmb q)) = _
  congr 1
  simp only [DInfty.cplx, DInfty.posEmb_r, DInfty.posEmb_θ]
  have : 2 * π / (2 * π / θ.1) * q.1.2 = θ.1 * q.1.2 := by
    have := θ.2.ne'; field_simp
  rw [this]

/-- The point of the half-plane of polar coordinates `(|h|, arg h / 2π)` of `h ≠ 0`. -/
def qOf (h : ℂ) (h0 : h ≠ 0) : PolarHalfPlane :=
  ⟨(‖h‖, Complex.arg h / (2 * π)), norm_pos_iff.2 h0⟩

theorem cplx_qOf (h : ℂ) (h0 : h ≠ 0) : DInfty.cplx 1 (DInfty.posEmb (qOf h h0)) = h := by
  rw [cplx_one_posEmb]
  show (‖h‖ : ℂ) * Complex.exp (((2 * π * (Complex.arg h / (2 * π)) : ℝ) : ℂ) * Complex.I) = h
  have : 2 * π * (Complex.arg h / (2 * π)) = Complex.arg h := by field_simp
  rw [this, Complex.norm_mul_exp_arg_mul_I]

theorem qOf_snd (h : ℂ) (h0 : h ≠ 0) : (qOf h h0).1.2 = Complex.arg h / (2 * π) := rfl

theorem isOpenMap_cplx_posEmb :
    IsOpenMap fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q) :=
  (DInfty.isOpenMap_cplx one_ne_zero).comp DInfty.isOpenMap_posEmb

theorem continuous_cplx_posEmb :
    Continuous fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q) :=
  (DInfty.continuous_cplx 1).comp DInfty.continuous_posEmb

/-- **Reading a cone chart through the developing map**: if, near the polar coordinates of the
point, the developing map of `C_{θ_i}` is `g • Ref` of the image in the double, then near the point
the chart `a ∘ Φ_i⁻¹` is a translate of `Ref`. -/
theorem eventually_chart_eq (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.TriDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (h0 : (t.chartPH i).symm y ≠ 0)
    {Ref : t.TriDouble → Sph2} {g : SO3}
    (hform : ∀ᶠ q in 𝓝 (qOf _ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      g • Ref (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) :
    ∃ g' : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g' • Ref y' := by
  set h₀ := (t.chartPH i).symm y with hh₀
  set q₀ := qOf h₀ h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hyU : y ∈ (t.chartPH i).target := by
    have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
    rw [chartPH_target]; exact this
  have hh₀V : h₀ ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hy₀ : t.chartPH i h₀ = y := (t.chartPH i).right_inv hyU
  have hc : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) = (t.Φ i).symm y := by
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [homeoComplex_mk_lift, cplx_qOf, Φ_symm_apply, Homeomorph.apply_symm_apply]
  have hca : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) ∈ a.source := by rw [hc]; exact hy.2
  obtain ⟨k, hk⟩ := sphCone_chart_dev (t.θc i) (y := polarHalfPlaneLift q₀) q₀.2 ha hca
  have hk' := (continuous_polarHalfPlaneLift.continuousAt (x := q₀)).eventually hk
  have hV : ∀ᶠ q in 𝓝 q₀, DInfty.cplx 1 (DInfty.posEmb q) ∈ t.Vv i :=
    continuous_cplx_posEmb.continuousAt.eventually ((t.isOpen_Vv i).mem_nhds (by
      show DInfty.cplx 1 (DInfty.posEmb q₀) ∈ t.Vv i; rw [cplx_qOf]; exact hh₀V))
  have hall : ∀ᶠ q in 𝓝 q₀, ((t.Φ i).symm.trans a) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))
      = (k * g) • Ref (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
    filter_upwards [hk', hV, hform] with q e1 e2 e3
    have hsym : (t.Φ i).symm (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) =
        SphCone.mk (t.θc i) (polarHalfPlaneLift q) := by
      rw [Φ_symm_apply, ← chartPH_apply, (t.chartPH i).left_inv e2]
      apply (SphCone.homeoComplex (t.θc i)).injective
      rw [Homeomorph.apply_symm_apply, homeoComplex_mk_lift]
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsym, mul_smul, ← e3]
    exact e1
  -- transport along the open map `q ↦ Φ_i (polar q)`
  obtain ⟨S, hS, hSall⟩ := hall.exists_mem
  refine ⟨k * g, Filter.mem_of_superset
    (x := (t.chartPH i) '' ((fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∩
      t.Vv i)) ?_ ?_⟩
  · have h1 : (fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∈ 𝓝 h₀ := by
      have := isOpenMap_cplx_posEmb.image_mem_nhds hS
      rwa [cplx_qOf] at this
    have := (t.chartPH i).image_mem_nhds hh₀V (inter_mem h1 ((t.isOpen_Vv i).mem_nhds hh₀V))
    rwa [hy₀] at this
  · rintro _ ⟨_, ⟨⟨q, hq, rfl⟩, -⟩, rfl⟩
    exact hSall q hq

/-- The reference map near a point of the side `e_k`: the fold on the upper copy, the fold
followed by the reflection `σ_k` on the lower copy. -/
def refEdge (k : Fin 3) (y : t.TriDouble) : Sph2 :=
  if 0 ≤ t.height y then t.fold y else t.σ k (t.fold y)

theorem height_chartMap_nonneg (i : Fin 3) {h : ℂ} (hK : h ∈ t.Kv i) (him : 0 ≤ h.im) :
    0 ≤ t.height (t.chartMap i h) := by
  rw [t.height_chartMap i hK, sheet, if_pos him, one_mul]; exact Real.sqrt_nonneg _

theorem sqrt_pos_of_im_ne_zero (i : Fin 3) {h : ℂ} (hV : h ∈ t.Vv i) (him : h.im ≠ 0) :
    0 < √(1 - ‖t.wK (t.xv i h)‖ ^ 2) := by
  have hK := t.Vv_subset_Kv i hV
  have hpos : ∀ k, 0 < t.n k ⬝ᵥ vec (t.xv i h) := by
    intro k
    have h12 := t.dot_xv_pos_of_im_ne_zero i him
    rcases fin3_cases i k with rfl | rfl | rfl
    · exact hV
    · exact h12.1
    · exact h12.2
  have := t.norm_wK_lt (t.xv_mem_T hK) hpos
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg (t.wK (t.xv i h))]

theorem height_chartMap_neg (i : Fin 3) {h : ℂ} (hV : h ∈ t.Vv i) (him : h.im < 0) :
    t.height (t.chartMap i h) < 0 := by
  rw [t.height_chartMap i (t.Vv_subset_Kv i hV), sheet, if_neg (not_le.2 him)]
  have := t.sqrt_pos_of_im_ne_zero i hV him.ne
  linarith

theorem im_pos_of_height_pos (i : Fin 3) {h : ℂ} (hK : h ∈ t.Kv i)
    (hy : 0 < t.height (t.chartMap i h)) : 0 < h.im := by
  rw [t.height_chartMap i hK] at hy
  have hS := t.fst_ne_of_mem_T (t.xv_mem_T hK)
  rcases lt_trichotomy h.im 0 with h1 | h1 | h1
  · rw [sheet, if_neg (not_le.2 h1)] at hy
    nlinarith [Real.sqrt_nonneg (1 - ‖t.wK (t.xv i h)‖ ^ 2)]
  · rw [t.sqrt_eq_zero_of_im_eq_zero i hS h1, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
  · exact h1

theorem im_neg_of_height_neg (i : Fin 3) {h : ℂ} (hK : h ∈ t.Kv i)
    (hy : t.height (t.chartMap i h) < 0) : h.im < 0 := by
  by_contra h1
  exact absurd (t.height_chartMap_nonneg i hK (not_lt.1 h1)) (not_le.2 hy)

theorem im_cplx_one_posEmb (q : PolarHalfPlane) :
    (DInfty.cplx 1 (DInfty.posEmb q)).im = q.1.1 * Real.sin (2 * π * q.1.2) := by
  rw [cplx_one_posEmb, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The point of `x_i` on the cover, through `polarFold_cover`. -/
theorem xv_cover (i : Fin 3) (q : PolarHalfPlane) :
    t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) = (t.R i)⁻¹ • stereoInv ((q.1.1 : ℂ) *
      Complex.exp ((foldAngle (t.α i) (DInfty.cplx 1 (DInfty.posEmb q)) : ℂ) * Complex.I)) := by
  rw [xv, polarFold_cover]

/-- **The upper sheet, read on the cover**: for `φ ∈ [0, 1/2]`, `D(r, φ) = R_i x_i`. -/
theorem dev_eq_up (i : Fin 3) (q : PolarHalfPlane) (h1 : 0 ≤ q.1.2) (h2 : q.1.2 ≤ 1 / 2) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift,
    foldAngle_cover_up (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 3
  push_cast; simp [θc]

/-- **The lower sheet, read on the cover**: for `φ ∈ [−1/2, 0]`, `D(r, φ) = ρ R_i x_i`. -/
theorem dev_eq_down (i : Fin 3) (q : PolarHalfPlane) (h1 : -(1 / 2) ≤ q.1.2) (h2 : q.1.2 ≤ 0) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSph (t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift, conjSph_stereoInv,
    foldAngle_cover_down (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast; simp [θc]

/-- **The lower sheet past the side `e_{i+1}`, read on the cover**: for `φ ∈ [1/2, 1]`,
`D(r, φ) = R_i σ_{i+1} x_i`. -/
theorem dev_eq_down_one (i : Fin 3) (q : PolarHalfPlane) (h1 : 1 / 2 ≤ q.1.2) (h2 : q.1.2 ≤ 1) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.σ (i + 1) (t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, t.R_σ_add_one_stereoInv, sphConeDev_lift,
    foldAngle_cover_down (n := 1) q (by push_cast; linarith) (by push_cast; linarith)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← mul_assoc, mul_comm (Complex.exp _) (q.1.1 : ℂ), mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast; simp [θc]; ring

theorem continuous_q_snd : Continuous fun q : PolarHalfPlane => q.1.2 :=
  continuous_snd.comp continuous_subtype_val

theorem eventually_Vv (i : Fin 3) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), DInfty.cplx 1 (DInfty.posEmb q) ∈ t.Vv i :=
  continuous_cplx_posEmb.continuousAt.eventually ((t.isOpen_Vv i).mem_nhds (by
    show DInfty.cplx 1 (DInfty.posEmb (qOf h₀ h0)) ∈ t.Vv i
    rw [cplx_qOf]; exact hV))

theorem eventually_snd_mem {h₀ : ℂ} (h0 : h₀ ≠ 0) {a b : ℝ}
    (hab : Complex.arg h₀ / (2 * π) ∈ Ioo a b) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), q.1.2 ∈ Ioo a b :=
  continuous_q_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds hab)

theorem sin_nonneg_of_mem (φ : ℝ) (h1 : 0 ≤ φ) (h2 : φ ≤ 1 / 2) : 0 ≤ Real.sin (2 * π * φ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])

theorem sin_neg_of_mem (φ : ℝ) (h1 : -(1 / 2) < φ) (h2 : φ < 0) : Real.sin (2 * π * φ) < 0 :=
  Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

theorem sin_neg_of_mem' (φ : ℝ) (h1 : 1 / 2 < φ) (h2 : φ < 1) : Real.sin (2 * π * φ) < 0 := by
  rw [← Real.sin_sub_two_pi]
  exact Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

theorem arg_div_mem_up {h : ℂ} (him : 0 < h.im) : Complex.arg h / (2 * π) ∈ Ioo 0 (1 / 2) := by
  have h1 : 0 ≤ Complex.arg h := Complex.arg_nonneg_iff.2 him.le
  have h2 : Complex.arg h ≠ 0 := fun e => by
    rw [Complex.arg_eq_zero_iff] at e; linarith [e.2]
  have h3 : Complex.arg h < π := Complex.arg_lt_pi_iff.2 (Or.inr him.ne')
  have hπ := Real.pi_pos
  constructor
  · exact div_pos (lt_of_le_of_ne h1 (Ne.symm h2)) (by positivity)
  · rw [div_lt_iff₀ (by positivity)]; linarith

theorem arg_div_mem_down {h : ℂ} (him : h.im < 0) :
    Complex.arg h / (2 * π) ∈ Ioo (-(1 / 2)) 0 := by
  have h1 : Complex.arg h < 0 := Complex.arg_neg_iff.2 him
  have h2 := Complex.neg_pi_lt_arg h
  have hπ := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · exact div_neg_of_neg_of_pos h1 (by positivity)

/-- The upper sheet: `D = R_i ∘ fold` near a point with `Im h₀ > 0`. -/
theorem hform_up (i : Fin 3) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : 0 < h₀.im) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.fold (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_up him)] with q hq hφ
  rw [t.fold_chartMap i (t.Vv_subset_Kv i hq), t.dev_eq_up i q hφ.1.le hφ.2.le]

/-- The lower sheet: `D = (ρ R_i ρ) ∘ ρ ∘ fold` near a point with `Im h₀ < 0`. -/
theorem hform_down (i : Fin 3) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSO3 (t.R i) • conjSph (t.fold (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) := by
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_down him)]
    with q hq hφ
  rw [t.fold_chartMap i (t.Vv_subset_Kv i hq), t.dev_eq_down i q hφ.1.le hφ.2.le, conjSph_smul]

/-- The side `e_{i+2}` (`φ = 0`): `D = R_i ∘ refEdge (i+2)`. -/
theorem hform_edge_two (i : Fin 3) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im = 0)
    (hre : 0 < h₀.re) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.refEdge (i + 2) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo (-(1 / 2)) (1 / 2) := by
    rw [Complex.arg_eq_zero_iff.2 ⟨hre.le, him⟩, zero_div]; constructor <;> norm_num
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := t.Vv_subset_Kv i hq
  rcases le_or_gt 0 q.1.2 with h1 | h1
  · have hh : 0 ≤ t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine t.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ h1 hφ.2.le)
    rw [refEdge, if_pos hh, t.fold_chartMap i hK, t.dev_eq_up i q h1 hφ.2.le]
  · have hh : t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine t.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem _ hφ.1 h1)
    rw [refEdge, if_neg (not_le.2 hh), t.fold_chartMap i hK, t.dev_eq_down i q hφ.1.le h1.le]
    conv_lhs => rw [← t.R_σ_add_two i (t.R i • t.xv i _), inv_smul_smul]

/-- The side `e_{i+1}` (`φ = 1/2`): `D = R_i ∘ refEdge (i+1)`. -/
theorem hform_edge_one (i : Fin 3) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im = 0)
    (hre : h₀.re < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.refEdge (i + 1) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo 0 1 := by
    rw [Complex.arg_eq_pi_iff.2 ⟨hre, him⟩]
    have hπ := Real.pi_pos
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := t.Vv_subset_Kv i hq
  rcases le_or_gt q.1.2 (1 / 2) with h1 | h1
  · have hh : 0 ≤ t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine t.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ hφ.1.le h1)
    rw [refEdge, if_pos hh, t.fold_chartMap i hK, t.dev_eq_up i q hφ.1.le h1]
  · have hh : t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine t.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem' _ h1 hφ.2)
    rw [refEdge, if_neg (not_le.2 hh), t.fold_chartMap i hK, t.dev_eq_down_one i q h1.le hφ.2.le]

theorem re_pos_of_polarFold_im {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {h : ℂ} (h0 : h ≠ 0)
    (hF : (polarFold α h).im = 0) : h.im = 0 ∧ 0 < h.re := by
  have him := im_eq_zero_of_polarFold hα0 hαπ (Or.inl hF)
  refine ⟨him, ?_⟩
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 = ‖h‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, him]; ring
  by_contra hre
  rw [not_lt] at hre
  have e : h.re = -‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
  rw [polarFold_im, foldAngle, e, neg_div, div_self hn.ne', Real.arccos_neg_one] at hF
  have : α / π * π = α := by field_simp
  rw [this] at hF
  have := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have := mul_pos hn this
  linarith

theorem re_neg_of_polarFold_sector {α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {h : ℂ} (h0 : h ≠ 0)
    (hF : Real.sin α * (polarFold α h).re - Real.cos α * (polarFold α h).im = 0) :
    h.im = 0 ∧ h.re < 0 := by
  have him := im_eq_zero_of_polarFold hα0 hαπ (Or.inr hF)
  refine ⟨him, ?_⟩
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hsq : h.re ^ 2 = ‖h‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, him]; ring
  by_contra hre
  rw [not_lt] at hre
  have e : h.re = ‖h‖ := by nlinarith [sq_nonneg (h.re - ‖h‖), sq_nonneg (h.re + ‖h‖)]
  rw [polarFold_sector_re, foldAngle, e, div_self hn.ne', Real.arccos_one, mul_zero, sub_zero] at hF
  have := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have := mul_pos hn this
  linarith

/-- A chart of the cone family at `v_i` never contains `v_i`: the apex of `C_{θ_i}` is singular. -/
theorem chartPH_symm_ne_zero (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.TriDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) : (t.chartPH i).symm y ≠ 0 := by
  intro h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hap : (t.Φ i).symm y = SphCone.apex (t.θc i) := by
    rw [Φ_symm_apply, h0]
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [Homeomorph.apply_symm_apply, homeoComplex_apex]
  have hreg : SphCone.apex (t.θc i) ∈ Reg SO3 Sph2 (SphCone (t.θc i)) :=
    mem_support.2 ⟨a, ha, hap ▸ hy.2⟩
  exact (SphCone.apex_mem_sing_iff _).2 (t.θc_ne i) hreg

theorem mem_target_of_mem_source (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    {y : t.TriDouble} (hy : y ∈ ((t.Φ i).symm.trans a).source) : y ∈ (t.chartPH i).target := by
  rw [OpenPartialHomeomorph.trans_source] at hy
  have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
  rw [chartPH_target]; exact this

/-- **On the upper copy, the cone charts are translates of the fold.** -/
theorem loc_up (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.TriDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (hpos : 0 < t.height y) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • t.fold y' := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  have him := t.im_pos_of_height_pos i (t.Vv_subset_Kv i hV) (by rw [hyc]; exact hpos)
  exact t.eventually_chart_eq i ha hy h0 (t.hform_up i h0 hV him)

/-- **On the lower copy, the cone charts are translates of `ρ ∘ fold`.** -/
theorem loc_down (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.TriDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (hneg : t.height y < 0) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • conjSph (t.fold y') := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  have him := t.im_neg_of_height_neg i (t.Vv_subset_Kv i hV) (by rw [hyc]; exact hneg)
  exact t.eventually_chart_eq i ha hy h0 (Ref := fun y => conjSph (t.fold y))
    (t.hform_down i h0 hV him)

/-- **Near a point of the side `e_k`, the cone charts are translates of `refEdge k`.** -/
theorem loc_edge (i : Fin 3) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.TriDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) {k : Fin 3} (hk : t.n k ⬝ᵥ vec (t.fold y) = 0) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • t.refEdge k y' := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  set h₀ := (t.chartPH i).symm y
  have hfold : t.fold y = t.xv i h₀ := by rw [← hyc, t.fold_chartMap i (t.Vv_subset_Kv i hV)]
  rw [hfold] at hk
  have hD : (0 : ℝ) < 1 + ‖h₀‖ ^ 2 := by positivity
  rcases fin3_cases i k with rfl | rfl | rfl
  · exact absurd hk (ne_of_gt hV)
  · rw [dot_xv_add_one, div_eq_zero_iff, mul_eq_zero] at hk
    have hF : Real.sin (t.α i) * (polarFold (t.α i) h₀).re -
        Real.cos (t.α i) * (polarFold (t.α i) h₀).im = 0 := by
      rcases hk with (hk | hk) | hk
      · norm_num at hk
      · exact hk
      · linarith
    obtain ⟨him, hre⟩ := re_neg_of_polarFold_sector (t.α_pos i) (t.α_lt_pi i) h0 hF
    exact t.eventually_chart_eq i ha hy h0 (t.hform_edge_one i h0 hV him hre)
  · rw [dot_xv_add_two, div_eq_zero_iff, mul_eq_zero] at hk
    have hF : (polarFold (t.α i) h₀).im = 0 := by
      rcases hk with (hk | hk) | hk
      · norm_num at hk
      · exact hk
      · linarith
    obtain ⟨him, hre⟩ := re_pos_of_polarFold_im (t.α_pos i) (t.α_lt_pi i) h0 hF
    exact t.eventually_chart_eq i ha hy h0 (t.hform_edge_two i h0 hV him hre)

/-- On the circle `s = 0` of the double, the fold lies on a side. -/
theorem exists_side_of_height_eq_zero {y : t.TriDouble} (hy : t.height y = 0) :
    ∃ k, t.n k ⬝ᵥ vec (t.fold y) = 0 := by
  have h1 : ‖t.disc y‖ = 1 := by
    have := t.height_sq_add y
    rw [hy] at this
    nlinarith [norm_nonneg (t.disc y)]
  rw [← t.wK_fold] at h1
  exact (t.norm_wK_eq_one_iff (t.fold_mem_T y)).1 h1

/-- The cone charts at `v_i`. -/
def coneAtlas (i : Fin 3) : Set (OpenPartialHomeomorph t.TriDouble Sph2) :=
  (fun a => (t.Φ i).symm.trans a) '' aeAtlas SO3 Sph2 (SphCone (t.θc i))

/-- **The generating atlas of the double**: the charts of the three cones `C_{θ_i}`, read through
the charts `Φ_i`. -/
def atlas : Set (OpenPartialHomeomorph t.TriDouble Sph2) := ⋃ i, t.coneAtlas i

/-- **The generating atlas is a `(SO(3), 𝕊²)`-atlas**: near every common point, two cone charts are
translates of the same reference map (`fold` on the upper copy, `ρ ∘ fold` on the lower copy,
`refEdge k` on the side `e_k`). -/
theorem isGXAtlas_atlas : IsGXAtlas SO3 t.atlas := by
  refine isGXAtlas_of_eventually ?_
  rintro e he e' he' y ⟨hye, hye'⟩
  obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.1 he
  obtain ⟨j, b, hb, rfl⟩ := mem_iUnion.1 he'
  have key : ∀ {Ref : t.TriDouble → Sph2},
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • Ref y') →
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ j).symm.trans b) y' = g • Ref y') →
      ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ j).symm.trans b) y' = g • ((t.Φ i).symm.trans a) y' := by
    rintro Ref ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    filter_upwards [h₁, h₂] with y' e1 e2
    rw [e2, e1, mul_smul, inv_smul_smul]
  rcases lt_trichotomy 0 (t.height y) with hp | h0 | hn
  · exact key (t.loc_up i ha hye hp) (t.loc_up j hb hye' hp)
  · obtain ⟨k, hk⟩ := t.exists_side_of_height_eq_zero h0.symm
    exact key (t.loc_edge i ha hye hk) (t.loc_edge j hb hye' hk)
  · exact key (Ref := fun y => conjSph (t.fold y)) (t.loc_down i ha hye hn)
      (t.loc_down j hb hye' hn)

end SphTriangle

end ConeCharts

/-! ### Charts of an open subset, pushed forward -/

section OpensCharts

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N]

/-- **A chart of an open subset `U` (with its induced structure), pushed forward to the ambient
manifold, is a chart of the ambient maximal atlas.** -/
theorem symm_trans_mem_aeAtlas_of_opens (U : Opens N) [Nonempty U]
    {b : OpenPartialHomeomorph U X} (hb : b ∈ aeAtlas G X U) :
    (U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val).symm.trans b ∈
      aeAtlas G X N := by
  set ι := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hιs : ι.source = univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
  refine (isMaximalAEAtlas_aeAtlas G X N).mem_of_compatible fun d hd z ⟨hzc, hzd⟩ => ?_
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hzc
  set u := ι.symm z
  have hzu : (u : N) = z := ι.right_inv hzc.1
  have hub : u ∈ b.source := hzc.2
  have huReg : u ∈ regLocusOf G (aeAtlas G X U) (aeAtlas G X N) Subtype.val := by
    rw [(isAEMorphism_opensSingular_val (G := G) (X := X) U).regLocusOf_eq
      (isMaximalAEAtlas_aeAtlas G X U).1 (isMaximalAEAtlas_aeAtlas G X N).1]
    refine ⟨mem_support.2 ⟨b, hb, hub⟩, ?_⟩
    show (u : N) ∈ support (aeAtlas G X N)
    rw [hzu]; exact mem_support.2 ⟨d, hd, hzd⟩
  obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := G) _ _ _).exists_smul_eq u huReg b hb d hd hub
    (by rw [hzu]; exact hzd)
  refine ⟨g, ?_⟩
  have hmap : Filter.map Subtype.val (𝓝 u) = 𝓝 z := by
    rw [← hzu]; exact U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq u
  rw [← hmap, Filter.eventually_map]
  filter_upwards [hg] with u' hu'
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have : ι.symm (u' : N) = u' := ι.left_inv (by rw [hιs]; exact mem_univ _)
  rw [this]; exact hu'

end OpensCharts

/-! ### The singular `(SO(3), 𝕊²)`-structure of the double, and its cone points -/

section Structure

/-- **The complement of a point of `𝕊²` is portly**: `𝕊²` has stereographic charts into `ℂ` at
every point (from the south pole, or after the half-turn). -/
theorem isPortly_compl_singleton_sph2 (v : Sph2) : IsPortly ({v}ᶜ : Set Sph2) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  by_cases hv : (v : Euc3).fst = -1
  · have hv' : ((halfTurn • v : Sph2) : Euc3).fst ≠ -1 := by
      rw [coe_halfTurn_smul, flipIsom_apply]
      show -(v : Euc3).fst ≠ -1
      rw [hv]; norm_num
    exact isPortly_compl_singleton_of_chart hrank
      ((Homeomorph.smul halfTurn).toOpenPartialHomeomorph.trans stereoChart) (v := v)
      ⟨mem_univ _, hv'⟩
  · exact isPortly_compl_singleton_of_chart hrank stereoChart (v := v) hv

namespace SphTriangle

variable (t : SphTriangle)

/-- **The vertex `v_i` of the double**, the image of the apex of `C_{θ_i}`. -/
def vertex (i : Fin 3) : t.TriDouble := t.chartMap i 0

theorem fold_vertex (i : Fin 3) : t.fold (t.vertex i) = t.xv i 0 :=
  t.fold_chartMap i (t.Vv_subset_Kv i (t.zero_mem_Vv i))

theorem vertex_injective : Injective t.vertex := by
  intro i j hij
  by_contra hne
  have h1 : 0 < t.n i ⬝ᵥ vec (t.fold (t.vertex i)) := by
    rw [t.fold_vertex]; exact t.zero_mem_Vv i
  rw [hij, t.fold_vertex] at h1
  rcases fin3_cases j i with h | h | h
  · exact hne h
  · rw [h, dot_xv_add_one, polarFold_zero] at h1; simp at h1
  · rw [h, dot_xv_add_two, polarFold_zero] at h1; simp at h1

theorem vertex_eq_Φ (i : Fin 3) : t.vertex i = t.Φ i (SphCone.apex (t.θc i)) := by
  rw [Φ_apply, homeoComplex_apex]; rfl

theorem apex_mem_Φ_source (i : Fin 3) : SphCone.apex (t.θc i) ∈ (t.Φ i).source := by
  rw [Φ_source, mem_preimage, homeoComplex_apex]; exact t.zero_mem_Vv i

/-- **Off the vertices, the double is covered by the cone charts.** -/
theorem mem_support_atlas {y : t.TriDouble} (hy : ∀ i, y ≠ t.vertex i) : y ∈ support t.atlas := by
  have hT := t.fold_mem_T y
  obtain ⟨i, hi⟩ : ∃ i, 0 < t.n i ⬝ᵥ vec (t.fold y) := by
    by_contra hne
    push Not at hne
    have h0 : ∀ k, t.n k ⬝ᵥ vec (t.fold y) = 0 := fun k => le_antisymm (hne k) (hT k)
    have hmv : Matrix.of ![t.n 0, t.n 1, t.n 2] *ᵥ vec (t.fold y) = 0 := by
      ext k; fin_cases k <;> simp [Matrix.mulVec, h0]
    have := Matrix.eq_zero_of_mulVec_eq_zero (ne_of_gt t.det_pos) hmv
    have h1 := vec_dot_self (t.fold y)
    rw [this] at h1; simp at h1
  have hyU : y ∈ (t.chartPH i).target := by rw [chartPH_target]; exact hi
  set h := (t.chartPH i).symm y
  have hV : h ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i h = y := (t.chartPH i).right_inv hyU
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

/-- **The generating atlas is an a.e. `(SO(3), 𝕊²)`-atlas**: its support contains the complement
of the three vertices, portly. -/
theorem isAEAtlas_atlas : IsAEAtlas SO3 t.atlas := by
  refine ⟨t.isGXAtlas_atlas, ?_⟩
  have hP : IsPortly (({t.vertex 0}ᶜ ∩ {t.vertex 1}ᶜ) ∩ {t.vertex 2}ᶜ : Set t.TriDouble) :=
    ((GX.isPortly_compl_singleton_sph2 (t.toSph2 (t.vertex 0))).inter
      (isPortly_compl_singleton_sph2 (t.toSph2 (t.vertex 1)))).inter
      (isPortly_compl_singleton_sph2 (t.toSph2 (t.vertex 2)))
  refine hP.mono (fun y hy => t.mem_support_atlas fun i => ?_) (isOpen_support _)
  obtain ⟨⟨h0, h1⟩, h2⟩ := hy
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **The singular `(SO(3), 𝕊²)`-structure of the doubled triangle**: the maximal a.e. atlas
generated by the cone charts (`cor:maximal_atlas`). -/
instance singularGXStructure : SingularGXStructure SO3 Sph2 t.TriDouble :=
  ⟨maximalAEAtlas SO3 t.atlas, t.isAEAtlas_atlas.isMaximalAEAtlas_maximalAEAtlas⟩

theorem aeAtlas_eq : aeAtlas SO3 Sph2 t.TriDouble = maximalAEAtlas SO3 t.atlas := rfl

/-- **The singular points of the double are among its vertices.** -/
theorem sing_subset_range_vertex : Sing SO3 Sph2 t.TriDouble ⊆ range t.vertex := by
  intro y hy
  by_contra hr
  have hy' : ∀ i, y ≠ t.vertex i := fun i e => hr ⟨i, e.symm⟩
  exact hy (support_mono t.isAEAtlas_atlas.subset_maximalAEAtlas (t.mem_support_atlas hy'))

/-- The domain of `Φ_i`, an open subset of `C_{θ_i}`. -/
def ΦV (i : Fin 3) : Opens (SphCone (t.θc i)) := ⟨(t.Φ i).source, (t.Φ i).open_source⟩

instance (i : Fin 3) : Nonempty (t.ΦV i) := ⟨⟨_, t.apex_mem_Φ_source i⟩⟩

/-- **`Φ_i` is an a.e. `(SO(3), 𝕊²)`-morphism** on its domain: the charts of the domain, pushed to
`C_{θ_i}` (`symm_trans_mem_aeAtlas_of_opens`), are read through `Φ_i` as charts of the generating
atlas. -/
theorem isAEMorphism_Φ (i : Fin 3) :
    IsAEMorphism SO3 Sph2 (fun v : t.ΦV i => t.Φ i (v : SphCone (t.θc i))) := by
  set V := t.ΦV i
  haveI : Nonempty V := ⟨⟨_, t.apex_mem_Φ_source i⟩⟩
  set ι := V.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hιs : ι.source = univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
  have hB := isMaximalAEAtlas_aeAtlas SO3 Sph2 V
  have hcont : Continuous fun v : V => t.Φ i (v : SphCone (t.θc i)) :=
    (t.Φ i).continuousOn.comp_continuous continuous_subtype_val fun v => v.2
  have h := isAEMorphismOf_maximalAEAtlas_of_forall hB.1 t.isAEAtlas_atlas hcont fun b hb => by
    refine ⟨(t.Φ i).symm.trans (ι.symm.trans b),
      mem_iUnion.2 ⟨i, _, symm_trans_mem_aeAtlas_of_opens V hb, rfl⟩, fun v hv => ?_,
      fun v hv => ?_⟩
    · have hl : (t.Φ i).symm (t.Φ i (v : SphCone (t.θc i))) = v := (t.Φ i).left_inv v.2
      have hι : ι.symm (v : SphCone (t.θc i)) = v := ι.left_inv (by rw [hιs]; exact mem_univ _)
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨(t.Φ i).map_source v.2, ?_⟩
      rw [mem_preimage, hl, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨?_, ?_⟩
      · rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]; exact mem_range_self _
      · rw [mem_preimage, hι]; exact hv
    · have hl : (t.Φ i).symm (t.Φ i (v : SphCone (t.θc i))) = v := (t.Φ i).left_inv v.2
      have hι : ι.symm (v : SphCone (t.θc i)) = v := ι.left_inv (by rw [hιs]; exact mem_univ _)
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [hl, hι]
  rwa [hB.maximalAEAtlas_eq] at h

theorem starConvex_Vv (i : Fin 3) : StarConvex ℝ 0 (t.Vv i) := by
  intro h hh a b ha hb hab
  rw [smul_zero, zero_add]
  show 0 < t.n i ⬝ᵥ vec (t.xv i (b • h))
  have hh' : 0 < t.n i ⬝ᵥ vec (t.xv i h) := hh
  rw [dot_xv] at hh' ⊢
  have hD : (0 : ℝ) < 1 + ‖b • h‖ ^ 2 := by positivity
  have hD' : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  apply div_pos _ hD
  have hg := (div_pos_iff_of_pos_right hD').1 hh'
  rw [Complex.real_smul, polarFold_ofReal_mul hb]
  set c := t.A i *ᵥ t.n i
  set v := polarFold (t.α i) h
  have hc0 : 0 < c 0 := t.A_mulVec_n_zero_pos i
  have key : gfun c ((b : ℂ) * v) = b * gfun c v + c 0 * (1 - b) + c 0 * b * (1 - b) * ‖v‖ ^ 2 := by
    simp only [gfun, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    ring
  rw [key]
  have hb1 : b ≤ 1 := by linarith
  rcases hb.lt_or_eq with hb0 | hb0
  · have := mul_pos hb0 hg
    have := mul_nonneg (mul_nonneg hc0.le hb0.le) (mul_nonneg (sub_nonneg.2 hb1) (sq_nonneg ‖v‖))
    nlinarith [mul_nonneg hc0.le (sub_nonneg.2 hb1)]
  · subst hb0; simp; exact hc0

theorem isConnected_ΦV (i : Fin 3) : IsConnected ((t.ΦV i : Set (SphCone (t.θc i)))) := by
  have hc : IsConnected (t.Vv i) :=
    ((t.starConvex_Vv i).isPathConnected (t.zero_mem_Vv i)).isConnected
  have : ((t.ΦV i : Set (SphCone (t.θc i)))) = (SphCone.homeoComplex (t.θc i)).symm '' t.Vv i := by
    show (t.Φ i).source = _
    rw [Φ_source, Homeomorph.image_symm]
  rw [this]
  exact hc.image _ (SphCone.homeoComplex (t.θc i)).symm.continuous.continuousOn

/-- **The `X_{θ_i}`-chart of the double at `v_i`** (`def:atlas`): `Φ_i⁻¹` from the image of `Φ_i`
onto its domain, a connected open neighbourhood of the apex of `C_{θ_i}`. -/
def coneXAChart (i : Fin 3) : XAChart SO3 Sph2 SphCone sphConeS (t.θc i) (t.vertex i) where
  U := ⟨(t.Φ i).target, (t.Φ i).open_target⟩
  V := t.ΦV i
  φ := (t.Φ i).toHomeomorphSourceTarget.symm
  mem := by rw [t.vertex_eq_Φ]; exact (t.Φ i).map_source (t.apex_mem_Φ_source i)
  isConnected_V := t.isConnected_ΦV i
  isAEMorphism := by
    refine IsAEMorphism.symm_of_homeomorph ?_
    refine isAEMorphism_of_val_comp ⟨(t.Φ i).target, (t.Φ i).open_target⟩ ?_
    exact t.isAEMorphism_Φ i
  mem_S := by
    show (t.Φ i).symm (t.vertex i) ∈ sphConeS (t.θc i)
    rw [t.vertex_eq_Φ, (t.Φ i).left_inv (t.apex_mem_Φ_source i)]
    exact mem_singleton _

/-- **The vertex `v_i` is a cone point of angle `θ_i = 2α_i`.** -/
theorem isConePoint_vertex (i : Fin 3) : IsConePoint (t.θc i) (t.vertex i) := ⟨t.coneXAChart i⟩

/-- **The doubled triangle is a cone sphere with the three cone points `v_i` of angles `2α_i`.** -/
theorem isConeSphere : IsConeSphere t.TriDouble (fun i => 2 * t.α i) t.vertex where
  homeomorphic := ⟨t.homeoSph2⟩
  injective := t.vertex_injective
  pos i := by have := t.α_pos i; positivity
  isConePoint i := t.isConePoint_vertex i
  sing_subset := t.sing_subset_range_vertex

end SphTriangle

end Structure

/-! ### Troyanov's theorem for three cone points -/

section Main

/-- **Troyanov's theorem for `s = 3`** (`MR1005085` as cited at `RamcovGX.tex:1930`, the case of
three cone points): for angles `θ_0, θ_1, θ_2` with `0 < ∑ (θ_i − 2π) + 4π ≤ min(4π, θ_i)`
(`GX.TroyanovAngleCondition`), there is a spherical cone sphere with cone points of angles
`θ_0, θ_1, θ_2` (`GX.IsConeSphere`): the double of the spherical triangle with angles `θ_i / 2`. -/
theorem troyanovTheorem_three (θ : Fin 3 → ℝ) (h : TroyanovAngleCondition θ) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 3 → M),
      IsConeSphere M θ p := by
  have hh := (troyanovAngleCondition_three_iff θ).1 h
  have hb := h.three_half
  obtain ⟨t, ht⟩ := exists_sphTriangle (fun i => θ i / 2) (fun i => (hb i).1) (fun i => (hb i).2)
    hh.1 (by linarith [(hb 2).1]) (by linarith [(hb 1).1]) (by linarith [(hb 0).1])
  have hθ : (fun i => 2 * t.α i) = θ := by
    funext i; rw [ht]; ring
  refine ⟨t.TriDouble, inferInstance, inferInstance, t.vertex, ?_⟩
  rw [← hθ]
  exact t.isConeSphere

/-- **The case `s = 3` discharges Troyanov's theorem down to `s ≥ 4`**: Troyanov's condition forces
`s ≥ 3`, and `s = 3` is `troyanovTheorem_three`. (The conclusion is the body of
`GX.TroyanovTheorem`, `GXScaffold.Spherical.TroyanovAngles`, which this module does not import.) -/
theorem troyanovTheorem_of_four_le
    (h4 : ∀ {s : ℕ}, 4 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p := by
  intro s θ hθ
  rcases Nat.lt_or_ge s 4 with hs | hs
  · obtain rfl : s = 3 := by have := hθ.1; omega
    exact troyanovTheorem_three θ hθ
  · exact h4 hs θ hθ

/-- **For `s = 3` the condition of `RamcovGX.tex:1930` is sufficient, not necessary**: the double of
the spherical triangle with angles `(7π/10, 7π/10, π/2)` is a cone sphere with cone angles
`(7π/5, 7π/5, π)`, which violate the condition as printed at l.1930 (`∑ (θ_i − 2π) + 4π = 9π/5 > π =
θ_2`) while satisfying `TroyanovAngleCondition.subcritical`'s `0 < χ' < min(4π, 2θ_i)`. (The paper
claims only sufficiency; this is not a defect.) -/
theorem exists_isConeSphere_not_troyanovAngleCondition :
    ∃ (θ : Fin 3 → ℝ) (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M)
      (p : Fin 3 → M), IsConeSphere M θ p ∧ ¬ TroyanovAngleCondition θ := by
  have hπ := Real.pi_pos
  obtain ⟨t, ht⟩ := exists_sphTriangle ![7 * π / 10, 7 * π / 10, π / 2]
    (fun i => by fin_cases i <;> simp <;> positivity)
    (fun i => by fin_cases i <;> simp <;> linarith)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  refine ⟨fun i => 2 * t.α i, t.TriDouble, inferInstance, inferInstance, t.vertex, t.isConeSphere,
    fun h => ?_⟩
  have h2 := h.2.2.2 2
  simp only [Fin.sum_univ_three, ht] at h2
  simp at h2
  linarith

end Main

end GX
