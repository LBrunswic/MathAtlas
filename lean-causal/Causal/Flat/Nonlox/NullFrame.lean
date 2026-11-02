import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples
import Causal.Flat.CauchyComplete

/-!
# `Causal.Flat.Nonlox.NullFrame` — a linear frame taking `v₀` to the null axis

T. Barbot, *Globally hyperbolic flat space-times*, §9 "The parabolic case" (`GHFspace.tex`
l.2621–2622: "`L(Γ)` preserves a isotropic vector `v₀`"; l.2678–2690: "Select a lightlike vector
`vₙ` … decompose every element of `M` in `x v₀ + z + y vₙ`"). Barbot's coordinates presuppose a
frame in which `v₀` is the null axis; this module supplies it: item (1) of the obstruction of
`Causal.Flat.nonloxodromic_parabolic` ([9.P]), the frame `φ` of `Flat/Nonloxodromic.lean`'s
SCOPE "Coordinates".

* `exists_isom_linear_null_frame` — for a null `v₀ ≠ 0` (and a parabolic element in
  `SO₀(1, d + 1)`, which forces `d ≥ 1`, `two_le_of_unipotent`), a **linear** isometry
  `φ ∈ Isom(𝐌ⁿ)` (zero translation part) with `L(φ) v₀ = c · ofNull 1 0 0`, `c ≠ 0`.

Proof. `d ≥ 1` from the parabolic element. Up to the sign of `c`, `v₀ = (t, x)` with
`‖x‖ = t > 0`. Two hyperplane reflections of `ℝ^{d+1}` — in `x − t e₀`, then in `e₁` — give a
rotation `Q ∈ SO(d + 1)` with `Q x = t e₀`; `(s, y) ↦ (s, Q y)` lies in `SO₀(1, d + 1)` and takes
`v₀` to `(t, t e₀) = √2 t · ofNull 1 0 0`.

## SCOPE (disclosed)
* The constant `c` is not normalised to `±1` (an `axisBoost` would do it; nothing needs it).
* The hypothesis `hpar` is used only to get `d ≥ 1`: in `𝐌²` (`d = 0`) the two null lines are
  each `SO₀(1, 1)`-invariant, so the statement would be false for `v₀ = (1, −1)` without it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Nonlox

open Causal.Flat

variable {d : ℕ}

/-- The Minkowski lift `(s, y) ↦ (s, Q y)` of a spatial linear isometry `Q`. -/
noncomputable def nfSpatial (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Minkowski d ≃ₗ[ℝ] Minkowski d :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) Q.toLinearEquiv

theorem nfSpatial_apply (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (p : Minkowski d) : nfSpatial Q p = (p.1, Q p.2) := rfl

theorem minkQ_nfSpatial (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (p : Minkowski d) : minkQ (nfSpatial Q p) = minkQ p := by
  simp only [minkQ, nfSpatial_apply, LinearIsometryEquiv.norm_map]

/-- A spatial rotation (determinant `1`) lifts into `SO₀(1, d)`. -/
theorem nfSpatial_mem_lorentz (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hQ : LinearMap.det (Q.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1) :
    nfSpatial Q ∈ lorentz d := by
  refine ⟨minkQ_nfSpatial Q, fun v hv => ⟨hv.1, (minkQ_nfSpatial Q v).symm ▸ hv.2⟩, ?_⟩
  show LinearMap.det (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    (Q.toLinearEquiv : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _)) = 1
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, hQ]

/-- A linear Lorentz map as an element of `Isom(𝐌ⁿ)` with zero translation part. -/
noncomputable def nfIsom (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (hA : A ∈ lorentz d) : isom d :=
  ⟨A.toAffineEquiv, hA⟩

theorem nfIsom_smul (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (hA : A ∈ lorentz d) (p : Minkowski d) :
    nfIsom A hA • p = A p := rfl

theorem linOf_nfIsom (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (hA : A ∈ lorentz d) :
    linOf (nfIsom A hA) = A := rfl

/-- The determinant of the reflection in the hyperplane orthogonal to `a ≠ 0` is `−1`. -/
theorem nf_det_reflection {n : ℕ} {a : EuclideanSpace ℝ (Fin n)} (ha : a ≠ 0) :
    LinearMap.det ((ℝ ∙ a)ᗮ.reflection.toLinearEquiv :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] _) = -1 := by
  have := Submodule.det_reflection (𝕜 := ℝ) (ℝ ∙ a)ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton ha, pow_one] at this
  exact this

/-- **A rotation of `ℝ^{m+1}` (`m ≥ 1`) taking `x` to `‖x‖ e₀`.** -/
theorem nf_exists_rot {m : ℕ} (hm : 1 ≤ m) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ∃ Q : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      LinearMap.det (Q.toLinearEquiv : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] _) = 1 ∧
        Q x = ‖x‖ • EuclideanSpace.single 0 1 := by
  set e : EuclideanSpace ℝ (Fin (m + 1)) := ‖x‖ • EuclideanSpace.single 0 1 with he_def
  have he : ‖x‖ = ‖e‖ := by
    simp [he_def, norm_smul]
  by_cases hxe : x = e
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact LinearMap.det_id
    · exact hxe
  · set b : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single ⟨1, by omega⟩ 1 with hb_def
    have hb : b ≠ 0 := by
      intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v ⟨1, by omega⟩) h
      simp [hb_def] at this
    have heb : e ∈ (ℝ ∙ b)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hb_def, he_def,
        EuclideanSpace.inner_single_left]
      simp
    have hxe' : x - e ≠ 0 := sub_ne_zero.2 hxe
    refine ⟨(ℝ ∙ (x - e))ᗮ.reflection.trans (ℝ ∙ b)ᗮ.reflection, ?_, ?_⟩
    · show LinearMap.det (((ℝ ∙ b)ᗮ.reflection.toLinearEquiv :
          EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] _) ∘ₗ
          ((ℝ ∙ (x - e))ᗮ.reflection.toLinearEquiv : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] _)) = 1
      rw [LinearMap.det_comp, nf_det_reflection hb, nf_det_reflection hxe']
      norm_num
    · show (ℝ ∙ b)ᗮ.reflection ((ℝ ∙ (x - e))ᗮ.reflection x) = e
      rw [Submodule.reflection_sub he]
      exact Submodule.reflection_mem_subspace_eq_self heb

/-- `(t, t e₀) = √2 t · ofNull 1 0 0`. -/
theorem nf_eq_smul_ofNull (t : ℝ) :
    ((t, t • EuclideanSpace.single 0 1) : Minkowski (d + 1)) =
      (√2 * t) • ofNull 1 0 (0 : EuclideanSpace ℝ (Fin d)) := by
  have h2 : √2 ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · simp only [ofNull, Prod.smul_fst, smul_eq_mul, sub_zero]
    field_simp
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ofNull]
      field_simp
    · simp [ofNull]

/-- The positive case: `v = (t, x)` with `‖x‖ = t > 0`. -/
theorem nf_exists_of_pos (hd : 1 ≤ d) {v : Minkowski (d + 1)} (h : ‖v.2‖ = v.1) :
    ∃ φ : isom (d + 1), (∀ p, φ • p = linOf φ p) ∧
      linOf φ v = (√2 * v.1) • ofNull 1 0 0 := by
  obtain ⟨Q, hQ, hQx⟩ := nf_exists_rot hd v.2
  refine ⟨nfIsom (nfSpatial Q) (nfSpatial_mem_lorentz Q hQ), fun p => rfl, ?_⟩
  rw [linOf_nfIsom, nfSpatial_apply, hQx, h]
  exact nf_eq_smul_ofNull v.1

/-- **A linear frame taking a null `v₀` to the null axis** (l.2621–2622, l.2678–2690). -/
theorem exists_isom_linear_null_frame {v₀ : Minkowski (d + 1)} (hv0 : v₀ ≠ 0)
    (hv : minkQ v₀ = 0) (hpar : ∃ A ∈ lorentz (d + 1), IsParabolic A) :
    ∃ φ : isom (d + 1), (∀ p, φ • p = linOf φ p) ∧
      ∃ c : ℝ, c ≠ 0 ∧ linOf φ v₀ = c • ofNull 1 0 0 := by
  obtain ⟨A, -, R, U, -, hU, -, hUu, hU1, -, -⟩ := hpar
  have h2 : 2 ≤ d + 1 :=
    two_le_of_unipotent (fun v => lorentz.minkQ_apply hU v) hUu (pOf_ne_zero hU1)
  have hd : 1 ≤ d := by omega
  have ht : v₀.1 ≠ 0 := fun h => hv0 (eq_zero_of_fst_eq_zero h hv.le)
  have hsq : ‖v₀.2‖ ^ 2 = v₀.1 ^ 2 := by unfold minkQ at hv; linarith
  have hs2 : (0 : ℝ) < √2 := by positivity
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hn : ‖(-v₀).2‖ = (-v₀).1 := by
      have := (sq_eq_sq₀ (norm_nonneg _) (by simp; linarith : (0 : ℝ) ≤ (-v₀).1)).1
        (by simpa using hsq)
      rw [Prod.snd_neg, norm_neg]; exact this
    obtain ⟨φ, hφ, hφv⟩ := nf_exists_of_pos hd hn
    refine ⟨φ, hφ, -(√2 * (-v₀).1), ?_, ?_⟩
    · have : 0 < (-v₀).1 := by simp; linarith
      exact neg_ne_zero.2 (by positivity)
    · rw [neg_smul, ← hφv, ← map_neg, neg_neg]
  · have hn : ‖v₀.2‖ = v₀.1 := (sq_eq_sq₀ (norm_nonneg _) hpos.le).1 hsq
    obtain ⟨φ, hφ, hφv⟩ := nf_exists_of_pos hd hn
    exact ⟨φ, hφ, √2 * v₀.1, by positivity, hφv⟩

end Causal.Flat.Nonlox
