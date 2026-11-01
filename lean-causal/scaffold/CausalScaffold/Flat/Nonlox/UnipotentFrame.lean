import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Nonlox.UnipotentFrame` — Barbot's `A` is a unipotent group of `Flat/Examples`

T. Barbot, *Globally hyperbolic flat space-times*, §9, the end of the parabolic case
(`GHFspace.tex` l.3100–3122: "Since `T̂` is symmetric, there is an orthonormal basis `e₁, …, e_{n−2}`
… `T(eᵢ) = λᵢ eᵢ`", the morphism `φ`, the choice of `w` with `⟨uᵢ | w⟩ = −μᵢ − λᵢ/2`, "after a
coordinate change, we can actually assume `μᵢ = −λᵢ/2`", "`Γ` is precisely as described in the
introduction"); Rem 9.2 `choixcoord` (l.2737–2760); the unipotent groups `A` of [3.U] (l.632–673).

* `exists_unipotent_frame_of_symm` — for a group `H ⊆ Isom(𝐌ⁿ)` acting, in the null coordinates
  `ofNull x y z` of `Flat/Examples`, by the elements `g_u` (`u ∈ L`, `L` ball-finite) of Barbot's
  `A_{T, ℓ}` (`T` symmetric, `ℓ` linear), and a slab `]ylo, yhi[` free of the poles of `1 + y T`,
  there are a frame `φ₁ ∈ Isom(𝐌ⁿ)` preserving `y`, eigenvalues `ℓ'`, a component `]α, β[ ⊇
  ]ylo, yhi[` (`IsUnipComponent`) and a ball-finite `L'` with `H = φ₁ Γ_A φ₁⁻¹`, `Γ_A` acting by
  `unipAction ℓ' t`, `t ∈ L'`.

Proof. The frame is `ψ = φ₁⁻¹ : (x, z, y) ↦ (x + ⟨w | z⟩ − (y/2)|w|², Q⁻¹(z − y w), y)` with
`⟨w | t⟩ = −ℓ t` (Rem 9.2 corrected: the null frame change `vₙ' = vₙ + w − (|w|²/2) v₀`) and `Q` an
orthonormal eigenbasis of `T` (the spectral theorem), oriented so that `det Q = 1`
(`OrthonormalBasis.adjustToOrientation`). `ψ` preserves `2xy + |z|²` and the future cone, and its
linear part has determinant `1` (the shear part by `det F_w = det F_{w/2}² ≥ 0`,
`det F_w det F_{−w} = 1` and `F_{−w} = R F_w R⁻¹` for `R : z ↦ −z`, the trick of `Examples.det_boost`).
Conjugation `ψ g_u ψ⁻¹ = unipAction ℓ' (Q⁻¹ u)` is a computation in the eigenbasis (Parseval). The
ends `α`, `β` are the nearest poles `−1/ℓ'ᵢ` below `ylo` and above `yhi` (or `±∞`).

## SCOPE (disclosed)
* The statement is the exact one dispatched; the symmetry of `T` is used on all of `ℝᵈ`.
* Nothing from `Flat/Nonloxodromic` is imported (that module imports this one); its `NolParam`
  computations (`choixcoord_nolA`, `unipAction_nolToMink`) are redone in `𝐌ⁿ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`). Barbot campaign, round 5, serving
`Causal.Flat.nonloxodromic_parabolic` ([9.A]).
-/

namespace Causal.Flat.Nonlox

open Causal.Flat Module
open scoped RealInnerProductSpace

variable {d : ℕ}

/-! ### Null coordinates as a linear equivalence -/

/-- The quadratic form `2xy + |z|²` on `(x, z, y)`. -/
noncomputable def ufrQ (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  2 * X.1 * X.2.2 + ‖X.2.1‖ ^ 2

/-- The null coordinates `p ↦ (x, z, y)` of `Flat/Examples`, as a linear equivalence. -/
noncomputable def ufrCoord : Minkowski (d + 1) ≃ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin d) × ℝ where
  toFun p := (nullX p, nullZ p, nullY p)
  map_add' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [nullX, Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring
    · ext i; simp [nullZ]
    · simp only [nullY, Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring
  map_smul' c p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [nullX, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul,
        RingHom.id_apply, Prod.smul_mk]; ring
    · ext i; simp [nullZ]
    · simp only [nullY, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul,
        RingHom.id_apply, Prod.smul_mk]; ring
  invFun X := ofNull X.1 X.2.2 X.2.1
  left_inv p := eq_of_null (nullX_ofNull _ _ _) (nullY_ofNull _ _ _)
    (fun i => by rw [nullZ_ofNull])
  right_inv X := by simp [nullX_ofNull, nullY_ofNull, nullZ_ofNull]

theorem ufrCoord_apply (p : Minkowski (d + 1)) : ufrCoord p = (nullX p, nullZ p, nullY p) := rfl

theorem ufrCoord_symm_apply (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    ufrCoord.symm X = ofNull X.1 X.2.2 X.2.1 := rfl

theorem ufr_ofNull_null (p : Minkowski (d + 1)) : ofNull (nullX p) (nullY p) (nullZ p) = p :=
  ufrCoord.left_inv p

/-! ### Isometries given in null coordinates -/

/-- The linear map of `𝐌ⁿ` read in null coordinates as `F`. -/
noncomputable def ufrLin (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1) :=
  ufrCoord.trans (F.trans ufrCoord.symm)

theorem ufrLin_apply (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) (p : Minkowski (d + 1)) :
    ufrLin F p = ofNull (F (ufrCoord p)).1 (F (ufrCoord p)).2.2 (F (ufrCoord p)).2.1 := rfl

theorem ufr_fst_ofNull (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (ofNull x y z).1 = (x - y) / √2 := rfl

/-- **A map preserving `2xy + |z|²`, the future cone and the orientation is in `SO₀(1, d + 1)`.** -/
theorem ufrLin_mem_lorentz (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) (hQ : ∀ X, ufrQ (F X) = ufrQ X)
    (hF : ∀ X, 0 ≤ X.1 - X.2.2 → ufrQ X ≤ 0 → 0 ≤ (F X).1 - (F X).2.2)
    (hdet : LinearMap.det (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] _) = 1) :
    ufrLin F ∈ lorentz (d + 1) := by
  have hm : ∀ v, minkQ (ufrLin F v) = minkQ v := fun v => by
    rw [minkQ_eq_null, minkQ_eq_null, ufrLin_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull]
    have := hQ (ufrCoord v)
    simp only [ufrQ, ufrCoord_apply] at this ⊢
    linarith
  refine ⟨hm, fun v hv => ⟨?_, by rw [hm]; exact hv.2⟩, ?_⟩
  · have hs : (0 : ℝ) < √2 := by positivity
    have h1 : 0 ≤ nullX v - nullY v := by
      have := hv.1; rw [fst_eq_null] at this
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hs))
    have h2 : ufrQ (ufrCoord v) ≤ 0 := by
      have := hv.2; rw [minkQ_eq_null] at this
      simpa [ufrQ, ufrCoord_apply] using this
    have := hF (ufrCoord v) (by simpa [ufrCoord_apply] using h1) h2
    rw [ufrLin_apply, ufr_fst_ofNull]
    exact div_nonneg this hs.le
  · rw [← hdet, ← LinearMap.det_conj (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] _)
      (ufrCoord (d := d)).symm]
    congr 1

/-- The isometry of `𝐌ⁿ` (linear, no translation part) read in null coordinates as `F`. -/
noncomputable def ufrIsom (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) (hF : ufrLin F ∈ lorentz (d + 1)) : isom (d + 1) :=
  ⟨(ufrLin F).toAffineEquiv, by rw [mem_isom_iff]; convert hF using 1; ext v <;> rfl⟩

theorem ufrIsom_smul (F : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ)) (hF : ufrLin F ∈ lorentz (d + 1)) (x y : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    ufrIsom F hF • ofNull x y z = ofNull (F (x, z, y)).1 (F (x, z, y)).2.2 (F (x, z, y)).2.1 := by
  show ufrLin F (ofNull x y z) = _
  rw [ufrLin_apply, ufrCoord_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull]

/-! ### The null frame change `vₙ ↦ vₙ + w − (|w|²/2) v₀` (Rem 9.2, corrected) -/

/-- **The frame change by `w`** (l.2737–2760, corrected): `(x, z, y) ↦ (x + ⟨w | z⟩ − (y/2)|w|²,
z − y w, y)`. -/
noncomputable def ufrShearL (w : EuclideanSpace ℝ (Fin d)) :
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) where
  toFun X := (X.1 + ⟪w, X.2.1⟫ - X.2.2 / 2 * ‖w‖ ^ 2, X.2.1 - X.2.2 • w, X.2.2)
  map_add' X X' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, inner_add_right]; ring
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
    · simp only [Prod.snd_add]
  map_smul' c X := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, smul_sub,
        mul_smul]
    · simp only [Prod.smul_snd, RingHom.id_apply]

theorem ufrShearL_apply (w : EuclideanSpace ℝ (Fin d)) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    ufrShearL w X = (X.1 + ⟪w, X.2.1⟫ - X.2.2 / 2 * ‖w‖ ^ 2, X.2.1 - X.2.2 • w, X.2.2) := rfl

theorem ufrShearL_comp (a b : EuclideanSpace ℝ (Fin d)) :
    ufrShearL a ∘ₗ ufrShearL b = ufrShearL (a + b) := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, ufrShearL_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only [inner_sub_right, inner_smul_right, inner_add_left, @norm_add_sq_real]
    rw [real_inner_comm b a]; ring
  · simp only [smul_add]; abel

theorem ufrShearL_zero : ufrShearL (0 : EuclideanSpace ℝ (Fin d)) = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp [ufrShearL_apply]

/-- The frame change, as a linear equivalence. -/
noncomputable def ufrShear (w : EuclideanSpace ℝ (Fin d)) :
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
  LinearEquiv.ofLinear (ufrShearL w) (ufrShearL (-w))
    (by rw [ufrShearL_comp, add_neg_cancel, ufrShearL_zero])
    (by rw [ufrShearL_comp, neg_add_cancel, ufrShearL_zero])

/-- The reflection `z ↦ −z`. -/
noncomputable def ufrFlip : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
  (LinearEquiv.refl ℝ ℝ).prodCongr ((LinearEquiv.neg ℝ).prodCongr (LinearEquiv.refl ℝ ℝ))

/-- **The frame change has determinant `1`**: `det F_w = det F_{w/2}² ≥ 0`, `F_{−w} = R F_w R⁻¹`
(`R : z ↦ −z`) and `F_w F_{−w} = 1` (the trick of `Examples.det_boost`). -/
theorem det_ufrShearL (w : EuclideanSpace ℝ (Fin d)) : LinearMap.det (ufrShearL w) = 1 := by
  have h1 : LinearMap.det (ufrShearL (-w)) = LinearMap.det (ufrShearL w) := by
    rw [← LinearMap.det_conj (ufrShearL w) (ufrFlip (d := d))]
    congr 1
    refine LinearMap.ext fun X => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ufrShearL_apply]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · show _ = (ufrShearL w (X.1, -X.2.1, X.2.2)).1
      simp only [ufrShearL_apply, inner_neg_left, inner_neg_right, norm_neg]
    · show _ = -(ufrShearL w (X.1, -X.2.1, X.2.2)).2.1
      simp only [ufrShearL_apply, smul_neg]; abel
  have h2 : LinearMap.det (ufrShearL w) * LinearMap.det (ufrShearL (-w)) = 1 := by
    rw [← LinearMap.det_comp, ufrShearL_comp, add_neg_cancel, ufrShearL_zero, LinearMap.det_id]
  have h3 : 0 ≤ LinearMap.det (ufrShearL w) := by
    rw [show w = (2⁻¹ : ℝ) • w + (2⁻¹ : ℝ) • w by rw [← add_smul]; norm_num, ← ufrShearL_comp,
      LinearMap.det_comp]
    exact mul_self_nonneg _
  rw [h1] at h2
  nlinarith [sq_nonneg (LinearMap.det (ufrShearL w) - 1)]

/-! ### The spectral theorem, with `det Q = 1` -/

/-- **An oriented orthonormal eigenbasis** (l.3100–3101: "Since `T̂` is symmetric, there is an
orthonormal basis `e₁, …, e_{n−2}` … `T(eᵢ) = λᵢ eᵢ`"), whose coordinate map has determinant `1`
(one vector is negated if needed, `OrthonormalBasis.adjustToOrientation`). -/
theorem ufr_exists_eigenbasis {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hsym : ∀ u u' : EuclideanSpace ℝ (Fin d), ⟪u, T u'⟫ = ⟪u', T u⟫) :
    ∃ (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (ℓ' : Fin d → ℝ),
      (∀ i, T (b i) = ℓ' i • b i) ∧
        LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1 := by
  have hT : T.IsSymmetric := fun x y => by rw [real_inner_comm, hsym]
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  set b0 := hT.eigenvectorBasis hn
  have hb0 : ∀ i, T (b0 i) = (hT.eigenvalues hn i) • b0 i := fun i => by
    rw [hT.apply_eigenvectorBasis hn i]; rfl
  set std := EuclideanSpace.basisFun (Fin d) ℝ
  obtain ⟨b, hb, hdet⟩ : ∃ b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      (∀ i, T (b i) = hT.eigenvalues hn i • b i) ∧ std.toBasis.det b = 1 := by
    rcases isEmpty_or_nonempty (Fin d) with h | h
    · exact ⟨b0, hb0, by rw [Basis.det_apply, Matrix.det_isEmpty]⟩
    · refine ⟨b0.adjustToOrientation std.toBasis.orientation, fun i => ?_, ?_⟩
      · rcases b0.adjustToOrientation_apply_eq_or_eq_neg std.toBasis.orientation i with h | h <;>
          rw [h]
        · exact hb0 i
        · rw [map_neg, hb0 i, smul_neg]
      · exact std.det_to_matrix_orthonormalBasis_of_same_orientation _
          (by rw [OrthonormalBasis.orientation_adjustToOrientation])
  refine ⟨b, _, hb, ?_⟩
  have hm : LinearMap.toMatrix std.toBasis std.toBasis
      (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = std.toBasis.toMatrix b := by
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    congr 2
  have h1 : LinearMap.det (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1 := by
    rw [← LinearMap.det_toMatrix std.toBasis, hm, ← Basis.det_apply, hdet]
  have h2 := LinearMap.det_comp (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)
    (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)
  have h3 : (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) ∘ₗ
      (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = LinearMap.id :=
    LinearMap.ext fun x => b.repr.apply_symm_apply x
  rw [h3, LinearMap.det_id, h1, mul_one] at h2
  exact h2.symm

/-! ### The frame `ψ = φ₁⁻¹` -/

/-- The rotation `z ↦ Q⁻¹ z` into the coordinates of the orthonormal basis `b`. -/
noncomputable def ufrRot (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
  (LinearEquiv.refl ℝ ℝ).prodCongr (b.repr.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ))

/-- The frame of l.3113–3122 in null coordinates: the frame change by `w`, then the eigenbasis. -/
noncomputable def ufrFrame (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) :
    (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
  (ufrShear w).trans (ufrRot b)

theorem ufrFrame_apply (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    ufrFrame b w X = (X.1 + ⟪w, X.2.1⟫ - X.2.2 / 2 * ‖w‖ ^ 2, b.repr (X.2.1 - X.2.2 • w), X.2.2) :=
  rfl

theorem ufrQ_ufrFrame (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    ufrQ (ufrFrame b w X) = ufrQ X := by
  simp only [ufrQ, ufrFrame_apply, LinearIsometryEquiv.norm_map, @norm_sub_sq_real,
    inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm X.2.1 w]; ring

theorem ufrFrame_future (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ)
    (h1 : 0 ≤ X.1 - X.2.2) (h2 : ufrQ X ≤ 0) :
    0 ≤ (ufrFrame b w X).1 - (ufrFrame b w X).2.2 := by
  obtain ⟨x, z, y⟩ := X
  simp only [ufrQ] at h1 h2
  simp only [ufrFrame_apply]
  have hZ : 0 ≤ ‖z‖ ^ 2 := by positivity
  have hW : 0 ≤ ‖w‖ ^ 2 := by positivity
  have hy : y ≤ 0 := by nlinarith
  have hx : 0 ≤ x := by nlinarith
  have hc : ⟪w, z⟫ ^ 2 ≤ ‖w‖ ^ 2 * ‖z‖ ^ 2 := by
    have h := abs_real_inner_le_norm w z
    have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [sq_abs, mul_pow] at h'
  have h3 : ⟪w, z⟫ ^ 2 ≤ ‖w‖ ^ 2 * (-2 * x * y) := by nlinarith
  have hA : 0 ≤ x - y / 2 * ‖w‖ ^ 2 := by nlinarith
  have hcA : ⟪w, z⟫ ^ 2 ≤ (x - y / 2 * ‖w‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x + y / 2 * ‖w‖ ^ 2)]
  have : 0 ≤ (x - y / 2 * ‖w‖ ^ 2) + ⟪w, z⟫ := by
    nlinarith [sq_nonneg ((x - y / 2 * ‖w‖ ^ 2) + ⟪w, z⟫),
      sq_nonneg ((x - y / 2 * ‖w‖ ^ 2) - ⟪w, z⟫)]
  linarith

theorem det_ufrFrame (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hb : LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1)
    (w : EuclideanSpace ℝ (Fin d)) :
    LinearMap.det (ufrFrame b w : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] _) = 1 := by
  have e : (ufrFrame b w : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] _) =
      LinearMap.prodMap LinearMap.id (LinearMap.prodMap
        (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
          LinearMap.id) ∘ₗ
          ufrShearL w := LinearMap.ext fun _ => rfl
  rw [e, LinearMap.det_comp, det_ufrShearL, LinearMap.det_prodMap, LinearMap.det_prodMap, hb]
  simp

/-- **The frame `ψ = φ₁⁻¹`** as an element of `Isom(𝐌ⁿ)`. -/
noncomputable def ufrPsi (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hb : LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1)
    (w : EuclideanSpace ℝ (Fin d)) : isom (d + 1) :=
  ufrIsom (ufrFrame b w) (ufrLin_mem_lorentz _ (ufrQ_ufrFrame b w) (ufrFrame_future b w)
    (det_ufrFrame b hb w))

theorem ufrPsi_smul (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hb : LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1)
    (w : EuclideanSpace ℝ (Fin d)) (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    ufrPsi b hb w • ofNull x y z = ofNull (x + ⟪w, z⟫ - y / 2 * ‖w‖ ^ 2) y (b.repr (z - y • w)) :=
  ufrIsom_smul _ _ x y z

theorem nullY_ufrPsi_smul (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (hb : LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1)
    (w : EuclideanSpace ℝ (Fin d)) (p : Minkowski (d + 1)) :
    nullY (ufrPsi b hb w • p) = nullY p := by
  rw [← ufr_ofNull_null p, ufrPsi_smul, nullY_ofNull, nullY_ofNull]

/-! ### The conjugation `ψ g_u ψ⁻¹ = unipAction ℓ' (Q⁻¹ u)` (l.3101–3122) -/

/-- Parseval in an orthonormal basis. -/
theorem ufr_sum_repr (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (a c : EuclideanSpace ℝ (Fin d)) : ∑ i, b.repr a i * b.repr c i = ⟪a, c⟫ := by
  rw [← b.repr.inner_map_map a c, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]

/-- `T` is diagonal in its eigenbasis: `Q⁻¹ T = diag(λ) Q⁻¹`. -/
theorem ufr_repr_apply {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hsym : ∀ u u' : EuclideanSpace ℝ (Fin d), ⟪u, T u'⟫ = ⟪u', T u⟫)
    {b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))} {ℓ' : Fin d → ℝ}
    (hb : ∀ i, T (b i) = ℓ' i • b i) (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    b.repr (T v) i = ℓ' i * b.repr v i := by
  rw [b.repr_apply_apply, b.repr_apply_apply, hsym, hb, real_inner_smul_right, real_inner_comm]

/-- **"`Γ` is precisely as described in the introduction"** (l.3113–3122), for one element: the
frame `ψ` conjugates `g_u ∈ A_{T, ℓ}` to `unipAction ℓ' (Q⁻¹ u)`. -/
theorem ufr_conj {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hsym : ∀ u u' : EuclideanSpace ℝ (Fin d), ⟪u, T u'⟫ = ⟪u', T u⟫)
    {ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ}
    {b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))} {ℓ' : Fin d → ℝ}
    (hb : ∀ i, T (b i) = ℓ' i • b i)
    (hdet : LinearMap.det (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1)
    {w : EuclideanSpace ℝ (Fin d)} (hw : ∀ t, ⟪w, t⟫ = -ℓ t) {g : isom (d + 1)}
    {u : EuclideanSpace ℝ (Fin d)}
    (hg : ∀ x y z, g • ofNull x y z =
      ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u))
    (p : Minkowski (d + 1)) :
    (ufrPsi b hdet w * g * (ufrPsi b hdet w)⁻¹) • p = unipAction ℓ' (b.repr u) p := by
  set ψ := ufrPsi b hdet w
  obtain ⟨q, rfl⟩ : ∃ q, p = ψ • q := ⟨ψ⁻¹ • p, (smul_inv_smul ψ p).symm⟩
  rw [mul_smul, mul_smul, inv_smul_smul, ← ufr_ofNull_null q]
  set x := nullX q
  set y := nullY q
  set z := nullZ q
  have hT := ufr_repr_apply hsym hb
  rw [hg, ufrPsi_smul, ufrPsi_smul]
  simp only [unipAction, nullX_ofNull, nullY_ofNull, nullZ_ofNull]
  have h1 : ∑ i, ℓ' i / 2 * b.repr u i ^ 2 = ⟪u, T u⟫ / 2 := by
    rw [← ufr_sum_repr b, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [hT]; ring
  have h2 : ∑ i, ℓ' i * b.repr (z - y • w) i * b.repr u i = ⟪z - y • w, T u⟫ := by
    rw [← ufr_sum_repr b]
    exact Finset.sum_congr rfl fun i _ => by rw [hT]; ring
  have h3 : ∑ i, ℓ' i ^ 2 * b.repr u i ^ 2 = ‖T u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← ufr_sum_repr b]
    exact Finset.sum_congr rfl fun i _ => by rw [hT]; ring
  congr 1
  · rw [h1, h2, h3, inner_add_right, inner_add_right, real_inner_smul_right, hw u,
      inner_sub_left, real_inner_smul_left, real_inner_comm (T u) z]
    ring
  · ext i
    simp only [map_add, map_sub, map_smul, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hT]
    ring

/-! ### The component `]α, β[` of `Ω(A)` (l.663–670) -/

/-- **The nearest poles**: if no pole `−1/ℓ'ᵢ` lies in `]ylo, yhi[`, the nearest pole below `ylo`
and the nearest pole above `yhi` (or `±∞`) bound a component of `{y | ∀ i, 1 + y ℓ'ᵢ ≠ 0}`. -/
theorem ufr_exists_component (ℓ' : Fin d → ℝ) {ylo yhi : EReal} (hlt : ylo < yhi)
    (hpole : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∀ i, 1 + y * ℓ' i ≠ 0) :
    ∃ α β : EReal, IsUnipComponent ℓ' α β ∧ α ≤ ylo ∧ yhi ≤ β := by
  classical
  set P : Fin d → ℝ := fun i => -1 / ℓ' i with hP
  have hPl : ∀ i, ℓ' i ≠ 0 → 1 + P i * ℓ' i = 0 := fun i hi => by
    simp only [hP]; field_simp; ring
  have hside : ∀ i, ℓ' i ≠ 0 → ((P i : ℝ) : EReal) ≤ ylo ∨ yhi ≤ ((P i : ℝ) : EReal) := by
    intro i hi
    by_contra h
    simp only [not_or, not_le] at h
    exact hpole (P i) h.1 h.2 i (hPl i hi)
  set fα : Fin d → EReal := fun i => if ℓ' i ≠ 0 ∧ ((P i : ℝ) : EReal) ≤ ylo then (P i : EReal)
    else ⊥ with hfα
  set fβ : Fin d → EReal := fun i => if ℓ' i ≠ 0 ∧ yhi ≤ ((P i : ℝ) : EReal) then (P i : EReal)
    else ⊤ with hfβ
  set α := Finset.univ.sup fα with hα
  set β := Finset.univ.inf fβ with hβ
  have hαlo : α ≤ ylo := Finset.sup_le fun i _ => by
    simp only [hfα]; split_ifs with h
    exacts [h.2, bot_le]
  have hβhi : yhi ≤ β := Finset.le_inf fun i _ => by
    simp only [hfβ]; split_ifs with h
    exacts [h.2, le_top]
  have hPα : ∀ i, ℓ' i ≠ 0 → ((P i : ℝ) : EReal) ≤ ylo → ((P i : ℝ) : EReal) ≤ α :=
    fun i hi h => by
      have := Finset.le_sup (f := fα) (Finset.mem_univ i)
      simp only [hfα, if_pos (And.intro hi h)] at this
      exact this
  have hPβ : ∀ i, ℓ' i ≠ 0 → yhi ≤ ((P i : ℝ) : EReal) → β ≤ ((P i : ℝ) : EReal) :=
    fun i hi h => by
      have := Finset.inf_le (f := fβ) (Finset.mem_univ i)
      simp only [hfβ, if_pos (And.intro hi h)] at this
      exact this
  refine ⟨α, β, ⟨hαlo.trans_lt (hlt.trans_le hβhi), fun y hy1 hy2 i h0 => ?_, ?_, ?_⟩, hαlo,
    hβhi⟩
  · by_cases hi : ℓ' i = 0
    · rw [hi, mul_zero, add_zero] at h0; exact one_ne_zero h0
    · have hy : y = P i := by
        simp only [hP]; field_simp; linarith
      rcases hside i hi with h | h
      · exact absurd (hPα i hi h) (not_le.2 (hy ▸ hy1))
      · exact absurd (hPβ i hi h) (not_le.2 (hy ▸ hy2))
  · rcases Finset.univ.eq_empty_or_nonempty (α := Fin d) with h | h
    · left; rw [hα, h, Finset.sup_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ h fα
      rw [hα, hi]
      simp only [hfα]
      split_ifs with hc
      · exact Or.inr ⟨i, hc.1, rfl⟩
      · exact Or.inl rfl
  · rcases Finset.univ.eq_empty_or_nonempty (α := Fin d) with h | h
    · left; rw [hβ, h, Finset.inf_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf _ h fβ
      rw [hβ, hi]
      simp only [hfβ]
      split_ifs with hc
      · exact Or.inr ⟨i, hc.1, rfl⟩
      · exact Or.inl rfl

/-! ### The theorem -/

/-- **"In summary, `Γ` is precisely as described in the introduction for the definition of unipotent
spacetimes"** (`GHFspace.tex` l.3100–3122, with Rem 9.2 l.2737–2760 corrected and [3.U]
l.632–673): a group `H` acting through the elements `g_u`, `u ∈ L`, of `A_{T, ℓ}` (`T` symmetric)
is conjugate, by a frame `φ₁` preserving `y`, to a group `Γ_A` acting by `unipAction ℓ' t`,
`t ∈ L'`, and the pole-free slab `]ylo, yhi[` lies in a component `]α, β[`. -/
theorem exists_unipotent_frame_of_symm {H : Subgroup (isom (d + 1))}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d))} (hL : BallFinite L)
    {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hsym : ∀ u u' : EuclideanSpace ℝ (Fin d), ⟪u, T u'⟫ = ⟪u', T u⟫)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ)
    (hH : ∀ g ∈ H, ∃ u ∈ L, ∀ x y z, g • ofNull x y z =
      ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u))
    (hH' : ∀ u ∈ L, ∃ g ∈ H, ∀ x y z, g • ofNull x y z =
      ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u))
    {ylo yhi : EReal} (hlt : ylo < yhi)
    (hpole : ∀ y : ℝ, ylo < y → (y : EReal) < yhi →
      ∀ t : EuclideanSpace ℝ (Fin d), t ≠ 0 → t + y • T t ≠ 0) :
    ∃ (φ₁ : isom (d + 1)) (ℓ' : Fin d → ℝ) (α β : EReal)
      (L' : AddSubgroup (EuclideanSpace ℝ (Fin d))) (ΓA : Subgroup (isom (d + 1))),
      BallFinite L' ∧ IsUnipComponent ℓ' α β ∧
      (∀ γ ∈ ΓA, ∃ t ∈ L', ∀ p, γ • p = unipAction ℓ' t p) ∧
      (∀ t ∈ L', ∃ γ ∈ ΓA, ∀ p, γ • p = unipAction ℓ' t p) ∧
      H = frameConj φ₁ ΓA ∧ (∀ p : Minkowski (d + 1), nullY (φ₁ • p) = nullY p) ∧ α ≤ ylo ∧
        yhi ≤ β := by
  obtain ⟨b, ℓ', hb, hdet⟩ := ufr_exists_eigenbasis hsym
  set w : EuclideanSpace ℝ (Fin d) :=
    (InnerProductSpace.toDual ℝ _).symm (-(LinearMap.toContinuousLinearMap ℓ))
  have hw : ∀ t, ⟪w, t⟫ = -ℓ t := fun t => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl
  set ψ := ufrPsi b hdet w
  set L' : AddSubgroup (EuclideanSpace ℝ (Fin d)) :=
    L.map (b.repr.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _).toAddMonoidHom
  have hmem : ∀ u ∈ L, b.repr u ∈ L' := fun u hu => AddSubgroup.mem_map.2 ⟨u, hu, rfl⟩
  have hpole' : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∀ i, 1 + y * ℓ' i ≠ 0 := by
    intro y h1 h2 i h0
    refine hpole y h1 h2 (b i) (b.orthonormal.ne_zero i) ?_
    rw [hb, smul_smul, show b i + (y * ℓ' i) • b i = (1 + y * ℓ' i) • b i by
      rw [add_smul, one_smul], h0, zero_smul]
  obtain ⟨α, β, hcomp, hα, hβ⟩ := ufr_exists_component ℓ' hlt hpole'
  refine ⟨ψ⁻¹, ℓ', α, β, L', frameConj ψ H, ⟨fun R => ?_⟩, hcomp, ?_, ?_, ?_, ?_, hα, hβ⟩
  · refine ((hL.finite_ball R).image b.repr).subset ?_
    rintro v ⟨hv, hR⟩
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hv
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    have : ‖b.repr u‖ = ‖u‖ := b.repr.norm_map u
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at hR
    linarith
  · intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hγ
    obtain ⟨u, hu, hgu⟩ := hH g hg
    exact ⟨b.repr u, hmem u hu, fun p => ufr_conj hsym hb hdet hw hgu p⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 ht
    obtain ⟨g, hg, hgu⟩ := hH' u hu
    exact ⟨ψ * g * ψ⁻¹, Subgroup.mem_map.2 ⟨g, hg, rfl⟩, fun p => ufr_conj hsym hb hdet hw hgu p⟩
  · ext γ
    simp only [frameConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro h
      exact ⟨ψ * γ * ψ⁻¹, ⟨γ, h, rfl⟩, by group⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simpa [mul_assoc] using hg
  · intro p
    rw [← nullY_ufrPsi_smul b hdet w (ψ⁻¹ • p), smul_inv_smul]

end Causal.Flat.Nonlox
