import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.Bieberbach

/-!
# `CausalScaffold.Flat.Lox.MisnerBieberbach` — [10.M]: Bieberbach through the euclidean model

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case", `papers/barbot/legacy/labeled/GHFspace.tex` l.3323–3330.
**No label is marked**: [10.M] is prose; this file is one step of `loxo_elementary_misner`
(`Flat/Loxodromic.lean`, item (3) of its obstruction). Barbot's `𝐌ⁿ` is `Minkowski (d + 1)` here
(kb/0024), the transverse coordinate `z ∈ ℝᵈ`.

> \[ \gamma(x, z, y) = (e^{-a(\gamma)}x, R(\gamma)(z) + u(\gamma), e^{a(\gamma)}y) \]
> As in corollary \ref{abel}, we see that the action on $\pi_{P}^{-1}(0)$ is free
> and properly discontinuous. Once more, an appropriate use of Bieberbach's theorem
> leads to the conclusion:
> the quotient space $M(S) = \Gamma\backslash\Omega(\widetilde{S})$
> is a linear twisted product over a Misner spacetime. (l.3323–3330)

`misner_bieberbach`: let every `γ ∈ Γ₁` act in the frame `φ` by
`ofNull x y z ↦ ofNull (eᵃ x) (e⁻ᵃ y) (A z + u)`, and let `Γ₁` act properly on an `Ω` containing a
tube `{φ (ofNull (eᵇ x₀) (e⁻ᵇ y₀) z)}`. Then there are a finite-index `Γ' ≤ Γ₁`, an affine
subspace `W = z₀ + J(ℝ^{d₁})` of `ℝᵈ` (`J` a linear isometry, `d₁ ≤ d`) on which `Γ'` acts by
translations — every `γ ∈ Γ'` is `ofNull x y (z₀ + J w) ↦ ofNull (eᵃ x) (e⁻ᵃ y) (z₀ + J (w + v))`
on `ℝ² × W` — and an element of `Γ'` with `a ≠ 0` (when `Γ₁` has one).

## The route (not the paper's: finding F3)

Barbot's first sentence (l.3326–3327) is false for `Γ` itself (finding F3: a boost times an
irrational rotation of `π_P⁻¹(0)` fixes `0`); and run for `Γ₀ = ker a` alone, Bieberbach gives no
`Γ`-invariant `W`. Here Bieberbach is applied to all of `Γ₁` through its **euclidean model**
`γ ↦ ((s, z) ↦ (s + a, A z + u))` on `ℝ × ℝᵈ ≅ ℝ^{d+1}` (`EuclideanSpace ℝ (Fin (d + 1))`,
`s` the coordinate `0`): it is a homomorphism (well defined: the parameters `a, A, u` are determined
by `γ`; injectivity is not needed), its image is discrete (`IsDiscreteEucl`, from `hprop` on the compact pieces
`{φ (ofNull (eᵇ x₀) (e⁻ᵇ y₀) z) : |b| ≤ R, ‖z‖ ≤ R}` of the tube, which is equivariant with
`(b, z)`), and `bieberbachMaxConclusion_of_bieberbachI` gives a finite-index `Γ'_E` acting by
translations on a maximal `Γ_E`-invariant `𝒲`. The vector `e_s` is fixed by every linear part
`(1, A)`, so `e_s ∈ 𝒲.direction` (`mem_direction_of_fixed`), `𝒲 = ℝ × W` with
`W = {z : (0, z) ∈ 𝒲}`, and a `γ` of `Γ' = (model)⁻¹(Γ'_E)` translates `𝒲` by `(a, J v)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| the normal form (l.3323) | ✓ carried (`hnf`; proved upstream, `Lox.misner_frame`) |
| the action is free and properly discontinuous (l.3326–3327) | ⚠ replaced: properness of `Γ₁` on `Ω ⊇` tube (`hprop`, `htube`; upstream `loxo_properlyDiscontinuous`), for `Γ₁` on `ℝ × ℝᵈ` rather than on `π_P⁻¹(0)` (finding F3) |
| "an appropriate use of Bieberbach's theorem" (l.3327) | ✓ carried as the external `BieberbachI` in dimension `d + 1` (`hBieb`, DEC-36) |
| `γ₀` loxodromic (`a(γ₀) ≠ 0`) | ✓ carried (`hboost`) |

## SCOPE (disclosed)

* The conclusion is up to finite index (DEC-43 R1), as `loxo_elementary_misner`'s.
* **Proved, no `sorry`** (axioms: `propext`, `Classical.choice`, `Quot.sound`), under the
  external `BieberbachI` in dimension `d + 1` (`hBieb`, a hypothesis, never an axiom: DEC-36).
  The steps, as private `mb_` helpers: the model point `mb_pt s z = (s, z)` and the linear
  isometry `mb_lin A = (s, z) ↦ (s, A z)`; the model `mb_model a A u`; the parameters of a normal
  form are unique (`mb_NF_unique`, from `nullX`/`nullZ` of `ofNull`), so `mb_mu : Γ₁ →* Isom(ℝ^{d+1})`
  is a homomorphism; its image is discrete (`mb_isDiscrete`, from `hprop` on the compact
  `{φ (ofNull (eᵇ x₀) (e⁻ᵇ y₀) z) : |b| ≤ R, ‖z‖ ≤ R}`); an element of `Γ'_E` translates
  `𝒲 ∩ {s = 0}` in `z` (`mb_translate`); and the boost is a power `γ_b ^ m ∈ Γ'`, of parameter
  `m a ≠ 0` (`mb_NF_pow`).
* `W = z₀ + J(ℝ^{d₁})` with `J` an orthonormal parametrisation of `D = {t | (0, t) ∈ 𝒲.direction}`
  (`stdOrthonormalBasis`), `d₁ = finrank D`; `W` is the slice of Bieberbach's maximal `𝒲`, not
  claimed maximal or `Γ₁`-invariant in this statement.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Causal.Flat Set
open scoped Pointwise

/-! ### The euclidean model `ℝ × ℝᵈ ≅ ℝ^{d+1}` -/

section Model

variable {d : ℕ}

/-- The point `(s, z)` of the euclidean model `ℝ × ℝᵈ ≅ ℝ^{d+1}` (`s` the coordinate `0`). -/
private noncomputable def mb_pt (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.cons s fun i => z i)

/-- The `ℝᵈ`-part of a point of the euclidean model. -/
private noncomputable def mb_tail (p : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => p i.succ

private theorem mb_pt_apply_zero (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : mb_pt s z 0 = s := rfl

private theorem mb_tail_pt (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : mb_tail (mb_pt s z) = z := by
  ext i; rfl

private theorem mb_pt_eta (p : EuclideanSpace ℝ (Fin (d + 1))) : mb_pt (p 0) (mb_tail p) = p := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem mb_pt_add (s s' : ℝ) (z z' : EuclideanSpace ℝ (Fin d)) :
    mb_pt s z + mb_pt s' z' = mb_pt (s + s') (z + z') := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem mb_pt_smul (c s : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    c • mb_pt s z = mb_pt (c * s) (c • z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem mb_pt_zero_zero : mb_pt 0 (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem mb_tail_add (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    mb_tail (p + q) = mb_tail p + mb_tail q := by
  ext i; rfl

private theorem mb_tail_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin (d + 1))) :
    mb_tail (c • p) = c • mb_tail p := by
  ext i; rfl

private theorem mb_norm_sq (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    ‖mb_pt s z‖ ^ 2 = s ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [mb_pt, Real.norm_eq_abs, sq_abs]

private theorem mb_abs_le (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : |s| ≤ ‖mb_pt s z‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, mb_norm_sq]
  nlinarith [sq_nonneg ‖z‖]

private theorem mb_norm_le (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ‖z‖ ≤ ‖mb_pt s z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), mb_norm_sq]
  nlinarith [sq_nonneg s]

/-- `z ↦ (0, z)`, linear. -/
private noncomputable def mb_inl : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) where
  toFun z := mb_pt 0 z
  map_add' z z' := by rw [mb_pt_add, add_zero]
  map_smul' c z := by rw [RingHom.id_apply, mb_pt_smul, mul_zero]

/-- `(s, z) ↦ (s, A z)`, a linear isometry of the euclidean model. -/
private noncomputable def mb_lin (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) where
  toFun p := mb_pt (p 0) (A (mb_tail p))
  invFun p := mb_pt (p 0) (A.symm (mb_tail p))
  map_add' p q := by
    rw [mb_tail_add, map_add, mb_pt_add]
    rfl
  map_smul' c p := by
    rw [mb_tail_smul, map_smul, RingHom.id_apply, mb_pt_smul]
    rfl
  left_inv p := by
    simp only [mb_pt_apply_zero, mb_tail_pt, LinearIsometryEquiv.symm_apply_apply, mb_pt_eta]
  right_inv p := by
    simp only [mb_pt_apply_zero, mb_tail_pt, LinearIsometryEquiv.apply_symm_apply, mb_pt_eta]
  norm_map' p := by
    show ‖mb_pt (p 0) (A (mb_tail p))‖ = ‖p‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    conv_rhs => rw [← mb_pt_eta p]
    rw [mb_norm_sq, mb_norm_sq, A.norm_map]

private theorem mb_lin_apply (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : mb_lin A (mb_pt s z) = mb_pt s (A z) := by
  show mb_pt (mb_pt s z 0) (A (mb_tail (mb_pt s z))) = _
  rw [mb_pt_apply_zero, mb_tail_pt]

/-- **The euclidean model of `(a, A, u)`**: `(s, z) ↦ (s + a, A z + u)`. -/
private noncomputable def mb_model (a : ℝ)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  (mb_lin A).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ _ (mb_pt a u))

private theorem mb_model_apply (a : ℝ)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d))
    (s : ℝ) (z : EuclideanSpace ℝ (Fin d)) : mb_model a A u (mb_pt s z) = mb_pt (s + a) (A z + u) := by
  show mb_pt a u + mb_lin A (mb_pt s z) = _
  rw [mb_lin_apply, mb_pt_add, add_comm a, add_comm u]

private theorem mb_ext {f g : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
    (h : ∀ s z, f (mb_pt s z) = g (mb_pt s z)) : f = g :=
  AffineIsometryEquiv.ext fun p => by rw [← mb_pt_eta p]; exact h _ _

private theorem mb_model_one :
    mb_model 0 (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) 0 = 1 :=
  mb_ext fun s z => by
    rw [mb_model_apply, add_zero, add_zero]
    rfl

private theorem mb_model_mul (a a' : ℝ)
    (A A' : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u u' : EuclideanSpace ℝ (Fin d)) :
    mb_model a A u * mb_model a' A' u' = mb_model (a + a') (A'.trans A) (A u' + u) :=
  mb_ext fun s z => by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, mb_model_apply, mb_model_apply,
      mb_model_apply, LinearIsometryEquiv.trans_apply, map_add, add_assoc, add_assoc, add_comm a']

/-- The linear part of a model fixes `e_s = (1, 0)`. -/
private theorem mb_model_fix (a : ℝ)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) :
    (mb_model a A u).linearIsometryEquiv (mb_pt 1 0) = mb_pt 1 0 := by
  have h := (mb_model a A u).map_vadd (mb_pt 0 0) (mb_pt 1 0)
  rw [vadd_eq_add, mb_pt_add, mb_model_apply, mb_model_apply, vadd_eq_add] at h
  simp only [add_zero, map_zero, zero_add] at h
  have h2 : mb_pt (1 + a) u = mb_pt 1 0 + mb_pt a u := by rw [mb_pt_add, zero_add]
  rw [h2] at h
  exact (add_right_cancel h).symm

private theorem mb_smul_es_add (c : ℝ) (p : EuclideanSpace ℝ (Fin (d + 1))) :
    c • mb_pt 1 (0 : EuclideanSpace ℝ (Fin d)) + p = mb_pt (c + p 0) (mb_tail p) := by
  conv_lhs => rw [← mb_pt_eta p]
  rw [mb_pt_smul, mb_pt_add, smul_zero, zero_add, mul_one]

/-- The continuity of `ofNull` in its three arguments. -/
private theorem mb_continuous_ofNull :
    Continuous (fun w : ℝ × ℝ × EuclideanSpace ℝ (Fin d) => ofNull (d := d) w.1 w.2.1 w.2.2) := by
  unfold ofNull
  fun_prop

end Model

/-! ### Normal forms and their parameters -/

section NormalForm

variable {d : ℕ}

/-- `γ` is in normal form with parameters `p = (a, A, u)` in the frame `φ`. -/
private def mb_NF (φ γ : isom (d + 1))
    (p : ℝ × (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
    γ • (φ • ofNull x y z) = φ • ofNull (Real.exp p.1 * x) (Real.exp (-p.1) * y) (p.2.1 z + p.2.2)

/-- **The parameters of a normal form are unique** (`φ`, `ofNull` injective). -/
private theorem mb_NF_unique {φ γ : isom (d + 1)} {p q} (hp : mb_NF φ γ p) (hq : mb_NF φ γ q) :
    p = q := by
  have h : ∀ x y z, ofNull (Real.exp p.1 * x) (Real.exp (-p.1) * y) (p.2.1 z + p.2.2) =
      ofNull (d := d) (Real.exp q.1 * x) (Real.exp (-q.1) * y) (q.2.1 z + q.2.2) :=
    fun x y z => MulAction.injective φ ((hp x y z).symm.trans (hq x y z))
  have ha : p.1 = q.1 := by
    have := congrArg nullX (h 1 0 0)
    rw [nullX_ofNull, nullX_ofNull, mul_one, mul_one] at this
    exact Real.exp_injective this
  have hu : p.2.2 = q.2.2 := by
    have := congrArg nullZ (h 0 0 0)
    rwa [nullZ_ofNull, nullZ_ofNull, map_zero, map_zero, zero_add, zero_add] at this
  have hA : p.2.1 = q.2.1 := by
    ext1 z
    have := congrArg nullZ (h 0 0 z)
    rw [nullZ_ofNull, nullZ_ofNull, hu] at this
    exact add_right_cancel this
  exact Prod.ext ha (Prod.ext hA hu)

private theorem mb_NF_one (φ : isom (d + 1)) :
    mb_NF φ 1 (0, LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)), 0) := by
  intro x y z
  simp

private theorem mb_NF_mul {φ γ γ' : isom (d + 1)} {p q} (hp : mb_NF φ γ p) (hq : mb_NF φ γ' q) :
    mb_NF φ (γ * γ') (p.1 + q.1, q.2.1.trans p.2.1, p.2.1 q.2.2 + p.2.2) := by
  intro x y z
  rw [mul_smul, hq, hp]
  simp only [LinearIsometryEquiv.trans_apply, map_add, neg_add, Real.exp_add, mul_assoc, add_assoc]

private theorem mb_NF_pow {φ γ : isom (d + 1)} {p} (hp : mb_NF φ γ p) :
    ∀ m : ℕ, ∃ q, q.1 = m * p.1 ∧ mb_NF φ (γ ^ m) q := by
  intro m
  induction m with
  | zero =>
    exact ⟨(0, LinearIsometryEquiv.refl ℝ _, 0), by simp, by rw [pow_zero]; exact mb_NF_one φ⟩
  | succ m ih =>
    obtain ⟨q, hq1, hq⟩ := ih
    refine ⟨_, ?_, by rw [pow_succ]; exact mb_NF_mul hq hp⟩
    simp only [hq1]
    push_cast
    ring

/-- The parameters of `γ ∈ Γ₁`, chosen. -/
private noncomputable def mb_par (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p) (γ : Γ₁) :
    ℝ × (EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) :=
  Classical.choose (hnf γ γ.2)

private theorem mb_par_spec (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p) (γ : Γ₁) : mb_NF φ γ (mb_par φ hnf γ) :=
  Classical.choose_spec (hnf γ γ.2)

/-- **The euclidean model of `Γ₁`**: `γ ↦ ((s, z) ↦ (s + a, A z + u))`, a homomorphism. -/
private noncomputable def mb_mu (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p) :
    Γ₁ →* (EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) where
  toFun γ := mb_model (mb_par φ hnf γ).1 (mb_par φ hnf γ).2.1 (mb_par φ hnf γ).2.2
  map_one' := by
    rw [mb_NF_unique (mb_par_spec φ hnf 1) (mb_NF_one φ)]
    exact mb_model_one
  map_mul' γ γ' := by
    rw [mb_NF_unique (mb_par_spec φ hnf (γ * γ'))
      (mb_NF_mul (mb_par_spec φ hnf γ) (mb_par_spec φ hnf γ')), mb_model_mul]

private theorem mb_mu_apply (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p) (γ : Γ₁) :
    mb_mu φ hnf γ = mb_model (mb_par φ hnf γ).1 (mb_par φ hnf γ).2.1 (mb_par φ hnf γ).2.2 := rfl

/-- **An element of the translation part translates `𝒲` by `(a, t)`**, `(0, t) ∈ 𝒲.direction`:
in the frame, it is `ofNull x y z ↦ ofNull (eᵃ x) (e⁻ᵃ y) (t + z)` for `(0, z) ∈ 𝒲`. -/
private theorem mb_translate (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p)
    {ΓE : Subgroup (EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))}
    {𝒲 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (d + 1)))} (htr : ActsByTranslationsOn ΓE 𝒲)
    (hes : mb_pt 1 (0 : EuclideanSpace ℝ (Fin d)) ∈ 𝒲.direction) (γ : Γ₁) (hγ : mb_mu φ hnf γ ∈ ΓE) :
    ∃ t : EuclideanSpace ℝ (Fin d), mb_pt 0 t ∈ 𝒲.direction ∧
      ∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)), mb_pt 0 z ∈ 𝒲 →
        (γ : isom (d + 1)) • (φ • ofNull x y z) =
          φ • ofNull (Real.exp (mb_par φ hnf γ).1 * x) (Real.exp (-(mb_par φ hnf γ).1) * y)
            (t + z) := by
  obtain ⟨τ, hτ, hτ'⟩ := htr _ hγ
  have hmodel : ∀ z, mb_mu φ hnf γ (mb_pt 0 z) =
      mb_pt (mb_par φ hnf γ).1 ((mb_par φ hnf γ).2.1 z + (mb_par φ hnf γ).2.2) := by
    intro z
    rw [mb_mu_apply, mb_model_apply, zero_add]
  have hspec := mb_par_spec φ hnf γ
  generalize mb_par φ hnf γ = P at hspec hmodel ⊢
  have htail : ∀ z, mb_pt 0 z ∈ 𝒲 → P.2.1 z + P.2.2 = mb_tail τ + z := by
    intro z hz
    have h := hτ' _ hz
    rw [hmodel, ← mb_pt_eta τ, vadd_eq_add, mb_pt_add] at h
    have := congrArg mb_tail h
    rwa [mb_tail_pt, mb_tail_pt] at this
  have htD : mb_pt 0 (mb_tail τ) ∈ 𝒲.direction := by
    have h := 𝒲.direction.add_mem (𝒲.direction.smul_mem (-(τ 0)) hes) hτ
    rwa [mb_smul_es_add, neg_add_cancel] at h
  refine ⟨mb_tail τ, htD, fun x y z hz => ?_⟩
  rw [hspec, htail z hz]

/-- **The euclidean model of `Γ₁` is discrete**: an element moving `(0, 0)` by at most `R` moves
the tube point `φ (ofNull x₀ y₀ 0)` into the compact piece `|b| ≤ R`, `‖z‖ ≤ R` of the tube. -/
private theorem mb_isDiscrete (φ : isom (d + 1)) {Γ₁ : Subgroup (isom (d + 1))}
    (hnf : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p) {Ω : Set (Minkowski (d + 1))}
    (hprop : ∀ K ⊆ Ω, IsCompact K →
      {γ : isom (d + 1) | γ ∈ Γ₁ ∧ (γ • K ∩ K).Nonempty}.Finite)
    {x₀ y₀ : ℝ}
    (htube : ∀ (b : ℝ) (z : EuclideanSpace ℝ (Fin d)),
      φ • ofNull (Real.exp b * x₀) (Real.exp (-b) * y₀) z ∈ Ω) :
    IsDiscreteEucl (mb_mu φ hnf).range := by
  rw [isDiscreteEucl_iff_exists]
  refine ⟨mb_pt 0 0, fun R => ?_⟩
  set f : ℝ × EuclideanSpace ℝ (Fin d) → Minkowski (d + 1) :=
    fun q => φ • ofNull (Real.exp q.1 * x₀) (Real.exp (-q.1) * y₀) q.2 with hf
  set K := f '' (Icc (-R) R ×ˢ Metric.closedBall 0 R) with hKdef
  have hfc : Continuous f :=
    (continuous_const_smul φ).comp (mb_continuous_ofNull.comp
      (f := fun q : ℝ × EuclideanSpace ℝ (Fin d) => (Real.exp q.1 * x₀, Real.exp (-q.1) * y₀, q.2))
      (by fun_prop))
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall 0 R)).image hfc
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨q, -, rfl⟩
    exact htube _ _
  have hS := (hprop K hKΩ hK).preimage (f := fun γ : Γ₁ => (γ : isom (d + 1)))
    Subtype.val_injective.injOn
  refine ((hS.image (mb_mu φ hnf)).subset ?_)
  rintro g ⟨⟨γ, rfl⟩, hd⟩
  refine ⟨γ, ⟨γ.2, ?_⟩, rfl⟩
  set P := mb_par φ hnf γ with hP
  rw [mb_mu_apply, ← hP, mb_model_apply, zero_add, map_zero, zero_add, mb_pt_zero_zero,
    dist_zero_right] at hd
  have hR : 0 ≤ R := (norm_nonneg _).trans hd
  have ha : |P.1| ≤ R := (mb_abs_le _ _).trans hd
  have hu : ‖P.2.2‖ ≤ R := (mb_norm_le _ _).trans hd
  have hp₀ : f (0, 0) ∈ K := ⟨(0, 0), ⟨⟨by linarith, hR⟩, Metric.mem_closedBall_self hR⟩, rfl⟩
  refine ⟨(γ : isom (d + 1)) • f (0, 0), Set.smul_mem_smul_set hp₀, ?_⟩
  refine ⟨(P.1, P.2.2), ⟨abs_le.mp ha, mem_closedBall_zero_iff.mpr hu⟩, ?_⟩
  have hγ := mb_par_spec φ hnf γ (Real.exp 0 * x₀) (Real.exp (-0) * y₀) 0
  rw [← hP] at hγ
  show f (P.1, P.2.2) = (γ : isom (d + 1)) • f (0, 0)
  simp only [hf]
  rw [hγ]
  simp only [Real.exp_zero, neg_zero, one_mul, map_zero, zero_add]

end NormalForm

/-- **[10.M] l.3323–3330: Bieberbach for `Γ₁`, through its euclidean model** (finding F3: not for
`Γ₁` on `π_P⁻¹(0)`). A finite-index `Γ' ≤ Γ₁` acts on `ℝ² × W`, `W = z₀ + J(ℝ^{d₁})`, by Misner
maps `(x, y, w) ↦ (eᵃ x, e⁻ᵃ y, w + v)`, with an element of nonzero boost. -/
theorem misner_bieberbach {d : ℕ} (hBieb : BieberbachI (EuclideanSpace ℝ (Fin (d + 1))))
    {Γ₁ : Subgroup (isom (d + 1))} (φ : isom (d + 1))
    (hnf : ∀ γ ∈ Γ₁, ∃ (a : ℝ) (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
      (u : EuclideanSpace ℝ (Fin d)), ∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
        γ • (φ • ofNull x y z) = φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (A z + u))
    {Ω : Set (Minkowski (d + 1))}
    (hprop : ∀ K ⊆ Ω, IsCompact K →
      {γ : isom (d + 1) | γ ∈ Γ₁ ∧ (γ • K ∩ K).Nonempty}.Finite)
    {x₀ y₀ : ℝ}
    (htube : ∀ (b : ℝ) (z : EuclideanSpace ℝ (Fin d)),
      φ • ofNull (Real.exp b * x₀) (Real.exp (-b) * y₀) z ∈ Ω)
    (hboost : ∃ γ ∈ Γ₁, ∃ a : ℝ, a ≠ 0 ∧
      ∃ (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
        (u : EuclideanSpace ℝ (Fin d)), ∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
          γ • (φ • ofNull x y z) = φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (A z + u)) :
    ∃ Γ' : Subgroup (isom (d + 1)), Γ' ≤ Γ₁ ∧ Γ'.relIndex Γ₁ ≠ 0 ∧
      ∃ (d₁ : ℕ) (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
        (z₀ : EuclideanSpace ℝ (Fin d)), d₁ ≤ d ∧
        (∀ γ ∈ Γ', ∃ (a : ℝ) (v : EuclideanSpace ℝ (Fin d₁)),
          ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)),
            γ • (φ • ofNull x y (z₀ + J w)) =
              φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (z₀ + J (w + v))) ∧
        ∃ γ ∈ Γ', ∃ a : ℝ, a ≠ 0 ∧ ∃ v : EuclideanSpace ℝ (Fin d₁),
          ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin d₁)),
            γ • (φ • ofNull x y (z₀ + J w)) =
              φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (z₀ + J (w + v)) := by
  classical
  have hnf' : ∀ γ ∈ Γ₁, ∃ p, mb_NF φ γ p := fun γ hγ => by
    obtain ⟨a, A, u, h⟩ := hnf γ hγ
    exact ⟨(a, A, u), h⟩
  -- (2)–(3): the model is discrete; Bieberbach's maximal form
  obtain ⟨ΓE, hleE, -, hfiE, 𝒲, ⟨p, hp⟩, -, htr, -, hmax⟩ :=
    bieberbachMaxConclusion_of_bieberbachI hBieb (mb_isDiscrete φ hnf' hprop htube)
  -- `e_s = (1, 0)` is fixed by every linear part, so lies in the direction of `𝒲`
  have hes : mb_pt 1 (0 : EuclideanSpace ℝ (Fin d)) ∈ 𝒲.direction := by
    refine mem_direction_of_fixed ⟨p, hp⟩ htr hmax fun g hg => ?_
    obtain ⟨γ, rfl⟩ := hleE hg
    exact mb_model_fix _ _ _
  -- `W = {z | (0, z) ∈ 𝒲}`: a base point `z₀` and the direction `D`
  set z₀ := mb_tail p with hz₀def
  have hz₀ : mb_pt 0 z₀ ∈ 𝒲 := by
    have h := AffineSubspace.vadd_mem_of_mem_direction (𝒲.direction.smul_mem (-(p 0)) hes) hp
    have e : (-(p 0)) • mb_pt 1 (0 : EuclideanSpace ℝ (Fin d)) +ᵥ p = mb_pt 0 z₀ := by
      rw [vadd_eq_add, mb_smul_es_add, neg_add_cancel]
    rwa [e] at h
  set D : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := 𝒲.direction.comap mb_inl with hD
  set B := stdOrthonormalBasis ℝ D with hB
  set J : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    D.subtypeₗᵢ.comp B.repr.symm.toLinearIsometry with hJ
  have hJD : ∀ w, mb_pt 0 (J w) ∈ 𝒲.direction := fun w => (B.repr.symm w).2
  have hJv : ∀ (t : EuclideanSpace ℝ (Fin d)) (ht : t ∈ D), J (B.repr ⟨t, ht⟩) = t := by
    intro t ht
    show ((B.repr.symm (B.repr ⟨t, ht⟩) : D) : EuclideanSpace ℝ (Fin d)) = t
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hd₁ : Module.finrank ℝ D ≤ d :=
    (Submodule.finrank_le D).trans_eq (finrank_euclideanSpace_fin)
  have hW : ∀ w, mb_pt 0 (z₀ + J w) ∈ 𝒲 := by
    intro w
    have h := AffineSubspace.vadd_mem_of_mem_direction (hJD w) hz₀
    rwa [vadd_eq_add, mb_pt_add, zero_add, add_comm (J w)] at h
  -- (4): `Γ' = μ⁻¹(Γ'_E)`; an element of it translates `𝒲` by `(a, J v)`
  have key : ∀ γ : Γ₁, mb_mu φ hnf' γ ∈ ΓE → ∃ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ D)),
      ∀ (x y : ℝ) (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ D))),
        (γ : isom (d + 1)) • (φ • ofNull x y (z₀ + J w)) =
          φ • ofNull (Real.exp (mb_par φ hnf' γ).1 * x) (Real.exp (-(mb_par φ hnf' γ).1) * y)
            (z₀ + J (w + v)) := by
    intro γ hγ
    obtain ⟨t, ht, hform⟩ := mb_translate φ hnf' htr hes γ hγ
    refine ⟨B.repr ⟨t, ht⟩, fun x y w => ?_⟩
    rw [hform x y _ (hW w), map_add, hJv]
    congr 2
    abel
  set Γ' : Subgroup (isom (d + 1)) := (ΓE.comap (mb_mu φ hnf')).map Γ₁.subtype with hΓ'
  have hle : Γ' ≤ Γ₁ := Subgroup.map_subtype_le _
  have hrel : Γ'.relIndex Γ₁ ≠ 0 := by
    have hsub : Γ'.subgroupOf Γ₁ = ΓE.comap (mb_mu φ hnf') :=
      Subgroup.comap_map_eq_self_of_injective Γ₁.subtype_injective _
    show (Γ'.subgroupOf Γ₁).index ≠ 0
    rw [hsub, Subgroup.index_comap]
    exact hfiE.index_ne_zero
  have hmemΓ' : ∀ γ ∈ Γ', ∃ γ' : Γ₁, mb_mu φ hnf' γ' ∈ ΓE ∧ (γ' : isom (d + 1)) = γ := by
    rintro _ ⟨γ', hγ', rfl⟩
    exact ⟨γ', hγ', rfl⟩
  refine ⟨Γ', hle, hrel, Module.finrank ℝ D, J, z₀, hd₁, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨γ', hγ', rfl⟩ := hmemΓ' γ hγ
    obtain ⟨v, hv⟩ := key γ' hγ'
    exact ⟨_, v, hv⟩
  -- (5): a power of the boost lies in `Γ'`, with parameter `m a ≠ 0`
  · obtain ⟨γb, hγb, ab, hab, Ab, ub, hb⟩ := hboost
    obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hrel hγb
    obtain ⟨γ', hγ', hγ'eq⟩ := hmemΓ' _ hmem.1
    obtain ⟨v, hv⟩ := key γ' hγ'
    obtain ⟨q, hq1, hq⟩ := mb_NF_pow (φ := φ) (p := (ab, Ab, ub)) hb m
    rw [← hγ'eq] at hq
    have hpar : mb_par φ hnf' γ' = q := mb_NF_unique (mb_par_spec φ hnf' γ') hq
    refine ⟨γ', Subgroup.mem_map.mpr ⟨γ', hγ', rfl⟩, (mb_par φ hnf' γ').1, ?_, v, hv⟩
    rw [hpar, hq1]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') hab

end Causal.Flat.Lox
