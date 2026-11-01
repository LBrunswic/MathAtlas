import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Nonlox.UnipotentRestriction` — the dispatched [9.U] reduction is false: a counterexample in `𝐌⁵`

T. Barbot, *Globally hyperbolic flat space-times*, §9, the purely unipotent case `[9.U]`
(`GHFspace.tex` l.2865–2938 of `papers/barbot/legacy/labeled/`), served for
`Causal.Flat.nonloxodromic_parabolic` (obstruction items (3)–(6) of `Flat/Nonloxodromic`). Barbot's
`𝐌ⁿ` is `Minkowski (d + 1)` here (`n = d + 2`, `z ∈ ℝ^{n−2} = ℝᵈ`); the counterexample has `d = 3`.
`[9.U]` is cited without the mark: nothing of it is certified here.

* `UnipotentRestrictionStatement` — the dispatched statement `exists_unipotent_restriction`,
  verbatim, as a `Prop` (kb/0022); `UnipotentRestrictionConclusion` its conclusion.
* `exists_unipotent_restriction_counterexample` — a group `Γ ⊆ Isom(𝐌⁵)` and `S̃` with
  `CCAction Γ S̃`, `L(Γ)` fixing `v₀ = ofNull 1 0 0`, `y` preserved (`b ≡ 0`) and a parabolic
  element, for which the conclusion FAILS. No hypothesis is added; Bieberbach is not used.
* `not_unipotentRestrictionStatement` — hence, given `BieberbachI ℝ³` (DEC-36's external, a true
  theorem), the dispatched statement is false.

> But this observation works for any `t ∈ I`: there is some affine subspace `𝒰̄_t × {t}` …
> on which the action of `α(γ)` has the expression `α(γ)(z,t) = (z + u(γ) + tv(γ), t)` …
> It follows that the action of every `λ(γ)` on the linear space spanned by all the `𝒰̄_t` is
> unipotent; since `𝒰̄_0` is the *maximal* `λ(Γ)`-unipotent subspace, it must contain every
> `𝒰̄_t`. Hence, every `v(γ)` belongs to `𝒰̄_0`: `𝒰̄_t` does not depend on `t`. (l.2881–2892)

**The example.** `P(φ, a)`: `(x, y, z) ↦ (x − ⟨v, R z⟩ − (y/2)|v|², y, R z + y v)`, `R = R_φ` the
rotation of angle `φ` of the `(z₀, z₁)`-plane, `v = (1 − cos φ, −sin φ, a)`. These form a group,
`P(φ, a) P(φ', a') = P(φ + φ', a + a')` (it is `n_w (R_φ ∘ u_{a e₂}) n_w⁻¹`, `w = e₀`, `n_w` the null
rotation of parameter `w`). `Γ = {P(kθ, k) | k ∈ ℤ}`, `θ = 2πα`, `α ∉ ℚ`; `S̃` the hyperboloid
`{minkQ = −1, t > 0}` (`ccPrime_graph_hyperboloid`). `P(θ, 1) = P(θ, 0) P(0, 1)` is parabolic
(`P(θ, 0)` keeps the form `ξ² + y² + |z − y e₀|²`, `ξ = x + z₀ − y/2`; `P(0, 1) − id` is nilpotent
of order 3). `Γ` acts freely and properly on `S̃`: `z₂ ↦ z₂ + k y` and `y < 0` on `S̃`.
At height `t`, `λ_t(P(kθ, k))` is a screw motion of irrational angle whose axis is `t w + ℝ e₂`:
the `𝒰̄_t` DO depend on `t`. If `ι` restricted some `γ ∈ G''` with `g` of the stated normal form,
comparing the `z`-parts at `y = 0, 1` gives `J (T u) = v(γ)` and `R(γ) J (T u) = J (T u)`, i.e.
`R(γ) v(γ) = v(γ)`, which forces `cos (kθ) = 1`, so `k = 0`, so `T u = 0`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Γ` acts freely, properly on `S̃` Cauchy-complete (CC′) | ✓ carried (`CCAction`) |
| `L(Γ)` fixes `v₀`; `b ≡ 0` ([9.b], l.2867) | ✓ carried |
| some element parabolic (§9's parabolic case) | ✓ carried |
| `0 ∈ I` (l.2875) | ✓ (`I = ]−∞, 0[`; the statement's `y₀` shift is free) |

## SCOPE (disclosed)
* **Finding (l.2881–2892).** "`𝒰̄_t` does not depend on `t`", and the claim before it that `λ(γ)` is
  unipotent on the span of the `𝒰̄_t`, are false in a fixed null frame: the `𝒰̄_t` are parallel
  axes `t w + ℝe₂`, whose span (`span {w, e₂}`) the rotation does not preserve. What is true in the
  example is that `⋃_t 𝒰̄_t × {t}` is an affine subspace of `P̄₀ × Q₁`; after the `y`-preserving null
  rotation `n_w` (which fixes `v₀` and changes `v` by `(I − R) w`) the axes are vertical and the
  conclusion holds with `d₁ = 1`. The dispatched normal form `ι (ofNull x y z) = ofNull x (y + y₀)
  (z₀ + J z)` forbids that frame; a corrected statement must allow a frame `φ ∈ Isom(𝐌ⁿ)` with
  `L(φ)` fixing `v₀` and preserving `y`, or `ι (ofNull x y z) = ofNull (x − ⟨w, J z⟩ − (y/2)|w|²)
  (y + y₀) (z₀ + y w + J z)`. Whether that corrected form holds in general is not addressed here.
* The mechanism needs an irrational rotation commuting with a nonzero `v`, hence `d ≥ 3`
  (Barbot's `n ≥ 5`); nothing is claimed for `d ≤ 2`.
* `θ`'s irrationality is taken from the countability of `ℚ` (`Cardinal.not_countable_real`):
  `Mathlib.Analysis.Real.Pi.Irrational` is outside the dispatched imports.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
round 5, serving `Causal.Flat.nonloxodromic_parabolic` ([9.P]–[9.U]).
-/

namespace Causal.Flat.Nonlox

open Causal.Flat Module Submodule
open scoped RealInnerProductSpace

/-! ### Null coordinates as a linear equivalence -/

private noncomputable def ureCoord {d : ℕ} :
    Minkowski (d + 1) ≃ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin d) × ℝ where
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

private theorem ureCoord_apply {d : ℕ} (p : Minkowski (d + 1)) :
    ureCoord p = (nullX p, nullZ p, nullY p) := rfl

private theorem ureCoord_symm_apply {d : ℕ} (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    ureCoord.symm X = ofNull X.1 X.2.2 X.2.1 := rfl

/-! ### Rotations of `ℝ³` about the third axis -/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem ure_inner (a b : E3) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem ure_norm_sq (a : E3) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ure_inner]; ring

/-- The rotation of angle `φ` in the plane of the first two axes. -/
private noncomputable def ureRot (φ : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun z := WithLp.toLp 2 ![Real.cos φ * z 0 - Real.sin φ * z 1,
    Real.sin φ * z 0 + Real.cos φ * z 1, z 2]
  map_add' a b := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by
    ext i; fin_cases i <;> simp <;> ring

private theorem ureRot_apply (φ : ℝ) (z : E3) :
    ureRot φ z = WithLp.toLp 2 ![Real.cos φ * z 0 - Real.sin φ * z 1,
      Real.sin φ * z 0 + Real.cos φ * z 1, z 2] := rfl

private theorem ureRot_inner (φ : ℝ) (a b : E3) : ⟪ureRot φ a, ureRot φ b⟫ = ⟪a, b⟫ := by
  rw [ure_inner, ure_inner, ureRot_apply, ureRot_apply]
  simp
  linear_combination (a 0 * b 0 + a 1 * b 1) * Real.sin_sq_add_cos_sq φ

private theorem ureRot_norm (φ : ℝ) (a : E3) : ‖ureRot φ a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ureRot_inner]

private theorem ureRot_comp (φ φ' : ℝ) (z : E3) :
    ureRot φ (ureRot φ' z) = ureRot (φ + φ') z := by
  rw [ureRot_apply, ureRot_apply, ureRot_apply]
  ext i; fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

private theorem ureRot_zero (z : E3) : ureRot 0 z = z := by
  rw [ureRot_apply]; ext i; fin_cases i <;> simp

/-- The parabolic parameter `v(φ, a) = a e₂ + e₀ − R_φ e₀`. -/
private noncomputable def ureV (φ a : ℝ) : E3 :=
  WithLp.toLp 2 ![1 - Real.cos φ, -Real.sin φ, a]

private theorem ureV_add (φ a φ' a' : ℝ) :
    ureRot φ (ureV φ' a') + ureV φ a = ureV (φ + φ') (a + a') := by
  rw [ureRot_apply, ureV, ureV, ureV]
  ext i; fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

private theorem ureV_zero : ureV 0 0 = 0 := by
  rw [ureV]; ext i; fin_cases i <;> simp


/-! ### The two-parameter group `P(φ, a)` in null coordinates -/

/-- In null coordinates `(x, z, y)`: `(x, z, y) ↦ (x − ⟨v, R z⟩ − (y/2)|v|², R z + y v, y)`,
`R = R_φ`, `v = v(φ, a)`. -/
private noncomputable def ureN (φ a : ℝ) : (ℝ × E3 × ℝ) →ₗ[ℝ] (ℝ × E3 × ℝ) where
  toFun X := (X.1 - ⟪ureV φ a, ureRot φ X.2.1⟫ - X.2.2 / 2 * ‖ureV φ a‖ ^ 2,
    ureRot φ X.2.1 + X.2.2 • ureV φ a, X.2.2)
  map_add' X Y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, map_add, inner_add_right]; ring
    · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]; abel
    · simp
  map_smul' c X := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_smul_right, smul_eq_mul,
        RingHom.id_apply]; ring
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_smul, RingHom.id_apply,
        smul_eq_mul]
    · simp

private theorem ureN_apply (φ a : ℝ) (X : ℝ × E3 × ℝ) :
    ureN φ a X = (X.1 - ⟪ureV φ a, ureRot φ X.2.1⟫ - X.2.2 / 2 * ‖ureV φ a‖ ^ 2,
      ureRot φ X.2.1 + X.2.2 • ureV φ a, X.2.2) := rfl

private theorem ureN_comp (φ a φ' a' : ℝ) (X : ℝ × E3 × ℝ) :
    ureN φ a (ureN φ' a' X) = ureN (φ + φ') (a + a') X := by
  obtain ⟨x, z, y⟩ := X
  rw [ureN_apply, ureN_apply, ureN_apply]
  simp only
  rw [← ureV_add, ← ureRot_comp]
  set R := ureRot φ
  set R' := ureRot φ'
  set v := ureV φ a
  set v' := ureV φ' a'
  have h1 : ⟪R v' + v, R (R' z)⟫ = ⟪v', R' z⟫ + ⟪v, R (R' z)⟫ := by
    rw [inner_add_left, ureRot_inner]
  have h2 : ‖R v' + v‖ ^ 2 = ‖v'‖ ^ 2 + 2 * ⟪v, R v'⟫ + ‖v‖ ^ 2 := by
    rw [@norm_add_sq_real, ureRot_norm, real_inner_comm]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only [map_add, map_smul, inner_add_right, inner_smul_right, h1, h2]; ring
  · simp only [map_add, map_smul, smul_add]; abel

private theorem ureN_zero (X : ℝ × E3 × ℝ) : ureN 0 0 X = X := by
  obtain ⟨x, z, y⟩ := X
  rw [ureN_apply, ureV_zero, ureRot_zero]; simp

/-- The linear map of `𝐌⁵` read in null coordinates as `ureN φ a`. -/
private noncomputable def ureL (φ a : ℝ) : Minkowski (3 + 1) →ₗ[ℝ] Minkowski (3 + 1) :=
  (ureCoord (d := 3)).symm.toLinearMap ∘ₗ ureN φ a ∘ₗ (ureCoord (d := 3)).toLinearMap

private theorem ureL_apply (φ a : ℝ) (p : Minkowski (3 + 1)) :
    ureL φ a p = ofNull (nullX p - ⟪ureV φ a, ureRot φ (nullZ p)⟫ - nullY p / 2 * ‖ureV φ a‖ ^ 2)
      (nullY p) (ureRot φ (nullZ p) + nullY p • ureV φ a) := rfl

private theorem ureL_ofNull (φ a x y : ℝ) (z : E3) :
    ureL φ a (ofNull x y z) = ofNull (x - ⟪ureV φ a, ureRot φ z⟫ - y / 2 * ‖ureV φ a‖ ^ 2) y
      (ureRot φ z + y • ureV φ a) := by
  rw [ureL_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull]

private theorem ureL_comp (φ a φ' a' : ℝ) :
    ureL φ a ∘ₗ ureL φ' a' = ureL (φ + φ') (a + a') := by
  refine LinearMap.ext fun p => ?_
  simp only [ureL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    ureN_comp]

private theorem ureL_zero : ureL 0 0 = LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  simp only [ureL, LinearMap.comp_apply, LinearEquiv.coe_coe, ureN_zero,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

private noncomputable def ureE (φ a : ℝ) : Minkowski (3 + 1) ≃ₗ[ℝ] Minkowski (3 + 1) :=
  LinearEquiv.ofLinear (ureL φ a) (ureL (-φ) (-a))
    (by rw [ureL_comp, add_neg_cancel, add_neg_cancel, ureL_zero])
    (by rw [ureL_comp, neg_add_cancel, neg_add_cancel, ureL_zero])

private theorem ureE_apply (φ a : ℝ) (p : Minkowski (3 + 1)) : ureE φ a p = ureL φ a p := rfl

private theorem ureE_mul (φ a φ' a' : ℝ) : ureE φ a * ureE φ' a' = ureE (φ + φ') (a + a') :=
  LinearEquiv.ext fun p => by
    show ureL φ a (ureL φ' a' p) = _
    rw [← LinearMap.comp_apply, ureL_comp]; rfl

private theorem ureE_zero : ureE 0 0 = 1 :=
  LinearEquiv.ext fun p => by
    show ureL 0 0 p = p
    rw [ureL_zero]; rfl

private theorem minkQ_ureL (φ a : ℝ) (p : Minkowski (3 + 1)) : minkQ (ureL φ a p) = minkQ p := by
  rw [minkQ_eq_null, minkQ_eq_null, ureL_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull]
  rw [@norm_add_sq_real, norm_smul, ureRot_norm, inner_smul_right, real_inner_comm]
  rw [mul_pow, Real.norm_eq_abs, sq_abs]
  ring

private theorem ureE_mem_lorentz (φ a : ℝ) : ureE φ a ∈ lorentz (3 + 1) := by
  have hQ : ∀ v, minkQ (ureE φ a v) = minkQ v := minkQ_ureL φ a
  have hs : (0 : ℝ) < √2 := by positivity
  have he : IsFutureTimelike (ofNull 1 (-1) (0 : E3)) := by
    refine ⟨?_, ?_⟩
    · show 0 < (1 - -1) / √2; positivity
    · rw [minkQ_eq_null, nullX_ofNull, nullY_ofNull, nullZ_ofNull]; simp
  refine mem_lorentz_of_future hQ he ⟨?_, by rw [hQ]; exact he.2⟩ ?_
  · rw [ureE_apply, ureL_ofNull]
    show 0 < ((1 - ⟪ureV φ a, ureRot φ 0⟫ - -1 / 2 * ‖ureV φ a‖ ^ 2) - -1) / √2
    rw [map_zero, inner_zero_right]
    have : 0 ≤ ‖ureV φ a‖ ^ 2 := by positivity
    exact div_pos (by linarith) hs
  · refine det_eq_one_of_eq_sq (B := ureL (φ / 2) (a / 2)) hQ ?_
    rw [ureL_comp, add_halves, add_halves]; rfl

/-- The element `P(φ, a)` of `Isom(𝐌⁵)`. -/
private noncomputable def ureI (φ a : ℝ) : isom (3 + 1) :=
  ⟨(ureE φ a).toAffineEquiv, by
    rw [mem_isom_iff]; convert ureE_mem_lorentz φ a using 1; ext v <;> rfl⟩

private theorem ureI_smul (φ a : ℝ) (p : Minkowski (3 + 1)) : ureI φ a • p = ureL φ a p := rfl

private theorem linOf_ureI (φ a : ℝ) : linOf (ureI φ a) = ureE φ a :=
  LinearEquiv.ext fun _ => rfl

private theorem ureI_mul (φ a φ' a' : ℝ) : ureI φ a * ureI φ' a' = ureI (φ + φ') (a + a') :=
  Subtype.ext (AffineEquiv.ext fun p => by
    show ureL φ a (ureL φ' a' p) = ureL (φ + φ') (a + a') p
    rw [← LinearMap.comp_apply, ureL_comp])

private theorem ureI_zero : ureI 0 0 = 1 :=
  Subtype.ext (AffineEquiv.ext fun p => by
    show ureL 0 0 p = p
    rw [ureL_zero]; rfl)


/-! ### Null-coordinate algebra -/

private theorem ure_ofNull_sub {d : ℕ} (x y x' y' : ℝ) (z z' : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z - ofNull x' y' z' = ofNull (x - x') (y - y') (z - z') := by
  change ureCoord.symm (x, z, y) - ureCoord.symm (x', z', y') =
    ureCoord.symm (x - x', z - z', y - y')
  rw [← map_sub]; rfl

private theorem ure_ofNull_zero {d : ℕ} : ofNull 0 0 (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
  change ureCoord.symm ((0, 0, 0) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) = 0
  exact map_zero _

private theorem ure_ofNull_null {d : ℕ} (p : Minkowski (d + 1)) :
    ofNull (nullX p) (nullY p) (nullZ p) = p :=
  ureCoord.left_inv p

private theorem ure_nullX_add {d : ℕ} (p q : Minkowski (d + 1)) :
    nullX (p + q) = nullX p + nullX q := congrArg Prod.fst (map_add ureCoord p q)

private theorem ure_nullY_add {d : ℕ} (p q : Minkowski (d + 1)) :
    nullY (p + q) = nullY p + nullY q := congrArg (fun X => X.2.2) (map_add ureCoord p q)

private theorem ure_nullZ_add {d : ℕ} (p q : Minkowski (d + 1)) :
    nullZ (p + q) = nullZ p + nullZ q := congrArg (fun X => X.2.1) (map_add ureCoord p q)

private theorem ure_nullX_smul {d : ℕ} (c : ℝ) (p : Minkowski (d + 1)) :
    nullX (c • p) = c * nullX p := congrArg Prod.fst (map_smul ureCoord c p)

private theorem ure_nullY_smul {d : ℕ} (c : ℝ) (p : Minkowski (d + 1)) :
    nullY (c • p) = c * nullY p := congrArg (fun X => X.2.2) (map_smul ureCoord c p)

private theorem ure_nullZ_smul {d : ℕ} (c : ℝ) (p : Minkowski (d + 1)) :
    nullZ (c • p) = c • nullZ p := congrArg (fun X => X.2.1) (map_smul ureCoord c p)

/-! ### `P(φ, 0)` is elliptic, `P(0, a)` unipotent -/

/-- The invariant coordinates of `P(φ, 0)`: `ξ = x + z₀ − y/2` and `ζ = z − y e₀`. -/
private noncomputable def ureXi (p : Minkowski (3 + 1)) : ℝ := nullX p + nullZ p 0 - nullY p / 2

private noncomputable def ureE0 : E3 := WithLp.toLp 2 ![1, 0, 0]

private noncomputable def ureZeta (p : Minkowski (3 + 1)) : E3 := nullZ p - nullY p • ureE0

private theorem ureXi_add (p q : Minkowski (3 + 1)) : ureXi (p + q) = ureXi p + ureXi q := by
  simp only [ureXi, ure_nullX_add, ure_nullY_add, ure_nullZ_add, PiLp.add_apply]; ring

private theorem ureXi_smul (c : ℝ) (p : Minkowski (3 + 1)) : ureXi (c • p) = c * ureXi p := by
  simp only [ureXi, ure_nullX_smul, ure_nullY_smul, ure_nullZ_smul, PiLp.smul_apply,
    smul_eq_mul]; ring

private theorem ureZeta_add (p q : Minkowski (3 + 1)) :
    ureZeta (p + q) = ureZeta p + ureZeta q := by
  simp only [ureZeta, ure_nullY_add, ure_nullZ_add, add_smul]; abel

private theorem ureZeta_smul (c : ℝ) (p : Minkowski (3 + 1)) :
    ureZeta (c • p) = c • ureZeta p := by
  simp only [ureZeta, ure_nullY_smul, ure_nullZ_smul, smul_sub, smul_smul]

/-- The positive definite form `ξ ξ' + y y' + ⟨ζ, ζ'⟩`. -/
private noncomputable def ureForm : LinearMap.BilinForm ℝ (Minkowski (3 + 1)) :=
  LinearMap.mk₂ ℝ (fun p q => ureXi p * ureXi q + nullY p * nullY q + ⟪ureZeta p, ureZeta q⟫)
    (fun p p' q => by
      simp only [ureXi_add, ure_nullY_add, ureZeta_add, inner_add_left]; ring)
    (fun c p q => by
      simp only [ureXi_smul, ure_nullY_smul, ureZeta_smul, inner_smul_left, smul_eq_mul,
        RCLike.conj_to_real]; ring)
    (fun p q q' => by
      simp only [ureXi_add, ure_nullY_add, ureZeta_add, inner_add_right]; ring)
    (fun c p q => by
      simp only [ureXi_smul, ure_nullY_smul, ureZeta_smul, inner_smul_right, smul_eq_mul]; ring)

private theorem ureForm_apply (p q : Minkowski (3 + 1)) :
    ureForm p q = ureXi p * ureXi q + nullY p * nullY q + ⟪ureZeta p, ureZeta q⟫ := rfl

private theorem ureXi_ureL (φ : ℝ) (p : Minkowski (3 + 1)) : ureXi (ureL φ 0 p) = ureXi p := by
  simp only [ureXi, ureL_apply, nullX_ofNull, nullY_ofNull, nullZ_ofNull]
  rw [ure_inner, ure_norm_sq]
  simp [ureRot_apply, ureV]
  linear_combination (nullZ p 0 - nullY p / 2) * Real.sin_sq_add_cos_sq φ

private theorem ureZeta_ureL (φ : ℝ) (p : Minkowski (3 + 1)) :
    ureZeta (ureL φ 0 p) = ureRot φ (ureZeta p) := by
  simp only [ureZeta, ureL_apply, nullY_ofNull, nullZ_ofNull]
  rw [ureRot_apply, ureRot_apply, ureV, ureE0]
  ext i; fin_cases i <;> simp <;> ring

private theorem isElliptic_ureE (φ : ℝ) : IsElliptic (ureE φ 0) := by
  refine ⟨ureForm, fun p q => ?_, fun p hp => ?_, fun p q => ?_⟩
  · rw [ureForm_apply, ureForm_apply, real_inner_comm]; ring
  · rw [ureForm_apply, real_inner_self_eq_norm_sq]
    by_contra hle
    push Not at hle
    have h1 : ureXi p = 0 := by nlinarith [sq_nonneg (nullY p), sq_nonneg ‖ureZeta p‖]
    have h2 : nullY p = 0 := by nlinarith [sq_nonneg (ureXi p), sq_nonneg ‖ureZeta p‖]
    have h3 : ureZeta p = 0 := by
      have : ‖ureZeta p‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg (ureXi p), sq_nonneg (nullY p)]
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg (ureZeta p)])
    have hz : nullZ p = 0 := by
      have := h3; simp only [ureZeta, h2, zero_smul, sub_zero] at this; exact this
    have hx : nullX p = 0 := by
      have := h1; simp only [ureXi, h2, hz] at this; simpa using this
    apply hp
    rw [← ure_ofNull_null p, hx, h2, hz, ure_ofNull_zero]
  · rw [ureForm_apply, ureForm_apply, ureE_apply, ureE_apply, ureXi_ureL, ureXi_ureL,
      ureZeta_ureL, ureZeta_ureL, ureRot_inner, ureL_apply, ureL_apply, nullY_ofNull,
      nullY_ofNull]

private theorem ure_pOf (p : Minkowski (3 + 1)) :
    pOf (ureE 0 1) p = ofNull (-(nullZ p 2) - nullY p / 2) 0 (nullY p • ureV 0 1) := by
  rw [pOf_apply, ureE_apply, ureL_apply]
  conv_lhs => rw [show p = ofNull (nullX p) (nullY p) (nullZ p) from (ure_ofNull_null p).symm]
  rw [nullX_ofNull, nullY_ofNull, nullZ_ofNull, ure_ofNull_sub, ureRot_zero, ure_inner,
    ure_norm_sq]
  congr 1
  · simp [ureV]; ring
  · ring
  · abel

private theorem isUnipotent_ureE : IsUnipotent (ureE 0 1) := by
  refine ⟨3, LinearMap.ext fun p => ?_⟩
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, ure_pOf, ure_pOf, ure_pOf]
  simp only [nullY_ofNull, nullZ_ofNull, zero_smul, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
  simp [ure_ofNull_zero]

private theorem ureE_ne_one : ureE 0 1 ≠ 1 := by
  intro h
  have h' := LinearEquiv.congr_fun h (ofNull 0 1 0)
  rw [ureE_apply, ureL_ofNull] at h'
  change _ = ofNull 0 1 0 at h'
  have := congrArg (fun p => nullZ p 2) h'
  simp [nullZ_ofNull, ureRot_apply, ureV] at this


/-! ### The group `Γ = {P(k, k) | k ∈ ℤ}` and the hyperboloid -/

/-- A real number which is not rational (ℚ is countable, ℝ is not). -/
private theorem ure_exists_irr : ∃ α : ℝ, ∀ q : ℚ, (q : ℝ) ≠ α := by
  by_contra h
  push Not at h
  apply Cardinal.not_countable_real
  have : Set.univ = Set.range (Rat.cast : ℚ → ℝ) :=
    (Set.eq_univ_of_forall fun α => (h α)).symm
  rw [this]; exact Set.countable_range _

private noncomputable def ureα : ℝ := Classical.choose ure_exists_irr

/-- The rotation angle `θ = 2πα`, `α` irrational. -/
private noncomputable def ureθ : ℝ := 2 * Real.pi * ureα

/-- `cos (k θ) ≠ 1` for a nonzero integer `k`. -/
private theorem ure_cos_ne_one {k : ℤ} (hk : k ≠ 0) : Real.cos (k * ureθ) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have e : (n : ℝ) = k * ureα := by
    rw [ureθ] at hn
    apply mul_right_cancel₀ hpi
    linear_combination hn
  apply Classical.choose_spec ure_exists_irr ((n : ℚ) / k)
  push_cast
  rw [e, mul_div_cancel_left₀ _ hk']
  rfl

private noncomputable def ureHom : Multiplicative ℤ →* isom (3 + 1) where
  toFun k := ureI ((Multiplicative.toAdd k : ℤ) * ureθ) ((Multiplicative.toAdd k : ℤ) : ℝ)
  map_one' := by simp [ureI_zero]
  map_mul' a b := by simp [ureI_mul, add_mul]

private noncomputable def ureG : Subgroup (isom (3 + 1)) := ureHom.range

private theorem ure_mem_G {γ : isom (3 + 1)} (h : γ ∈ ureG) :
    ∃ k : ℤ, γ = ureI (k * ureθ) k := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨Multiplicative.toAdd m, rfl⟩

private theorem ureI_mem_G (k : ℤ) : ureI (k * ureθ) k ∈ ureG := ⟨Multiplicative.ofAdd k, rfl⟩

private abbrev ureSt : Set (Minkowski (3 + 1)) := graph (hyperboloid (3 + 1))

private theorem ure_mem_St {p : Minkowski (3 + 1)} : p ∈ ureSt ↔ minkQ p = -1 ∧ 0 < p.1 := by
  rw [ureSt, graph_hyperboloid]; rfl

private theorem ure_nullY_neg {p : Minkowski (3 + 1)} (hp : p ∈ ureSt) : nullY p < 0 := by
  obtain ⟨hq, ht⟩ := ure_mem_St.1 hp
  rw [minkQ_eq_null] at hq
  rw [fst_eq_null] at ht
  have hxy : nullY p < nullX p := by
    have := (div_pos_iff.1 ht).resolve_right (fun h => absurd h.2 (not_lt.2 (by positivity)))
    linarith [this.1]
  by_contra h
  push Not at h
  nlinarith [sq_nonneg ‖nullZ p‖]

private theorem ureI_mem_St (φ a : ℝ) {p : Minkowski (3 + 1)} (hp : p ∈ ureSt) :
    ureI φ a • p ∈ ureSt := by
  obtain ⟨hq, ht⟩ := ure_mem_St.1 hp
  have hf : IsFutureTimelike (ureE φ a p) :=
    lorentz.isFutureTimelike_apply (ureE_mem_lorentz φ a) ⟨ht, by rw [hq]; norm_num⟩
  exact ure_mem_St.2 ⟨(minkQ_ureL φ a p).trans hq, hf.1⟩

private theorem ure_nullZ_two (φ k : ℝ) (p : Minkowski (3 + 1)) :
    nullZ (ureI φ k • p) 2 = nullZ p 2 + k * nullY p := by
  rw [ureI_smul, ureL_apply, nullZ_ofNull]
  simp [ureRot_apply, ureV]; ring

private theorem ure_ccAction : CCAction ureG ureSt := by
  refine ⟨ccPrime_graph_hyperboloid, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨k, rfl⟩ := ure_mem_G hγ
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ureI_mem_St _ _ hp
    · intro hx
      refine ⟨ureI (-(k * ureθ)) (-k) • x, ureI_mem_St _ _ hx, ?_⟩
      rw [← mul_smul, ureI_mul, add_neg_cancel, add_neg_cancel, ureI_zero, one_smul]
  · intro γ hγ h1 x hx hfx
    obtain ⟨k, rfl⟩ := ure_mem_G hγ
    have hk : (k : ℝ) ≠ 0 := fun h => h1 (by rw [h, zero_mul, ureI_zero])
    have := congrArg (fun p => nullZ p 2) hfx
    simp only [ure_nullZ_two] at this
    have h0 : (k : ℝ) * nullY x = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact hk h
    · exact (ure_nullY_neg hx).ne h
  · intro K hKS hK
    rcases K.eq_empty_or_nonempty with he | hne
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨-, q, -, hq⟩
      rw [he] at hq; exact hq
    obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hne continuous_nullY.continuousOn
    have hc : nullY p₀ < 0 := ure_nullY_neg (hKS hp₀)
    have hcont : Continuous fun p : Minkowski (3 + 1) => nullZ p 2 :=
      (EuclideanSpace.proj (2 : Fin 3)).continuous.comp continuous_nullZ
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    set N : ℤ := ⌈2 * B / (-nullY p₀)⌉
    refine ((Set.finite_Icc (-N) N).image fun k : ℤ => ureI (k * ureθ) k).subset ?_
    rintro γ ⟨hγ, q, hq1, hq2⟩
    obtain ⟨k, rfl⟩ := ure_mem_G hγ
    obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.1 hq1
    refine ⟨k, ?_, rfl⟩
    have e := ure_nullZ_two (k * ureθ) k p
    have hb1 := hB _ hp
    have hb2 := hB _ hq2
    rw [Real.norm_eq_abs] at hb1 hb2
    have hyp : nullY p ≤ nullY p₀ := hmax hp
    have hkB : |(k : ℝ)| * (-nullY p₀) ≤ 2 * B := by
      have h1 : |(k : ℝ)| * (-nullY p₀) ≤ |(k : ℝ) * nullY p| := by
        rw [abs_mul, abs_of_neg (by linarith : nullY p < 0)]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have h2 : (k : ℝ) * nullY p = nullZ (ureI (k * ureθ) (k : ℝ) • p) 2 - nullZ p 2 := by
        rw [e]; ring
      rw [h2] at h1
      linarith [abs_sub (nullZ (ureI (k * ureθ) (k : ℝ) • p) 2) (nullZ p 2)]
    have hk : |(k : ℝ)| ≤ (N : ℝ) :=
      ((le_div_iff₀ (by linarith)).2 hkB).trans (Int.le_ceil _)
    have hk' : |k| ≤ N := by exact_mod_cast hk
    exact abs_le.1 hk'


private theorem ure_hfix : ∀ γ ∈ ureG, linOf γ (ofNull 1 0 0) = ofNull 1 0 0 := by
  intro γ hγ
  obtain ⟨k, rfl⟩ := ure_mem_G hγ
  rw [linOf_ureI, ureE_apply, ureL_ofNull]
  simp

private theorem ure_hb : ∀ γ ∈ ureG, ∀ p : Minkowski (3 + 1), nullY (γ • p) = nullY p := by
  intro γ hγ p
  obtain ⟨k, rfl⟩ := ure_mem_G hγ
  rw [ureI_smul, ureL_apply, nullY_ofNull]

private theorem ure_hpar : ∃ γ ∈ ureG, IsParabolic (linOf γ) := by
  refine ⟨ureI ureθ 1, by simpa using ureI_mem_G 1, ?_⟩
  rw [linOf_ureI]
  refine ⟨ureE ureθ 0, ureE 0 1, ureE_mem_lorentz _ 0, ureE_mem_lorentz 0 1, isElliptic_ureE _,
    isUnipotent_ureE, ureE_ne_one, ?_, ?_⟩
  · rw [ureE_mul]; norm_num
  · rw [ureE_mul, ureE_mul]; norm_num


/-! ### The dispatched statement, as a `Prop` -/

/-- The conclusion of the dispatched `exists_unipotent_restriction`, verbatim. -/
def UnipotentRestrictionConclusion (d : ℕ) (G : Subgroup (isom (d + 1)))
    (St : Set (Minkowski (d + 1))) : Prop :=
  ∃ G'' : Subgroup (isom (d + 1)), G'' ≤ G ∧ G''.relIndex G ≠ 0 ∧
    ∃ d₁ : ℕ, d₁ ≤ d ∧
    ∃ (J : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
      (z₀ : EuclideanSpace ℝ (Fin d)) (y₀ : ℝ) (ι : AffineMinkEmbedding (d₁ + 1) (d + 1)),
      (∀ x y z, ι (ofNull x y z) = ofNull x (y + y₀) (z₀ + J z)) ∧ ι.Orthochronous ∧
      ι.RestrictsIn G'' ∧
    ∃ (L : AddSubgroup (EuclideanSpace ℝ (Fin d₁)))
      (T : EuclideanSpace ℝ (Fin d₁) →ₗ[ℝ] EuclideanSpace ℝ (Fin d₁))
      (ℓ : EuclideanSpace ℝ (Fin d₁) →ₗ[ℝ] ℝ) (ylo yhi : EReal),
      BallFinite L ∧ (∃ u ∈ L, T u ≠ 0) ∧
      (∀ u ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d₁))),
        ∀ u' ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d₁))), ⟪u, T u'⟫ = ⟪u', T u⟫) ∧
      (∀ g ∈ ι.restrictGroup G'', ∃ u ∈ L, ∀ x y z, g • ofNull x y z =
        ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u)) ∧
      (∀ u ∈ L, ∃ g ∈ ι.restrictGroup G'', ∀ x y z, g • ofNull x y z =
        ofNull (x - ⟪T u, z⟫ - y / 2 * ‖T u‖ ^ 2 + (ℓ u - ⟪u, T u⟫ / 2)) y (z + u + y • T u)) ∧
      ylo < 0 ∧ 0 < yhi ∧ (ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥) ∧
      (∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∃ p, ι p ∈ St ∧ nullY p = y) ∧
      ∀ p ∈ St, ylo < ((nullY p - y₀ : ℝ) : EReal) ∧ ((nullY p - y₀ : ℝ) : EReal) < yhi

/-- **The dispatched statement `exists_unipotent_restriction`**, verbatim, as a `Prop`
(kb/0022). It is refuted by `not_unipotentRestrictionStatement` (modulo Bieberbach in `ℝ³`). -/
def UnipotentRestrictionStatement : Prop :=
  ∀ (d : ℕ), BieberbachI (EuclideanSpace ℝ (Fin d)) →
    ∀ {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}, CCAction G St →
      (∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0) →
      (∀ γ ∈ G, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p) →
      (∃ γ ∈ G, IsParabolic (linOf γ)) → UnipotentRestrictionConclusion d G St

/-! ### The refutation -/

private theorem ure_not_conclusion : ¬UnipotentRestrictionConclusion 3 ureG ureSt := by
  rintro ⟨G'', hle, -, d₁, -, J, z₀, y₀, ι, hι, -, -, L, T, ℓ, ylo, yhi, -, ⟨u, huL, hTu⟩, -, -,
    hall, -⟩
  obtain ⟨g, hg, hgf⟩ := hall u huL
  obtain ⟨γ, hγ, hres⟩ := (ι.mem_restrictGroup).1 hg
  obtain ⟨k, rfl⟩ := ure_mem_G (hle hγ)
  have key : ∀ (y : ℝ) (z : EuclideanSpace ℝ (Fin d₁)),
      z₀ + J (z + u + y • T u) = ureRot (k * ureθ) (z₀ + J z) + (y + y₀) • ureV (k * ureθ) k := by
    intro y z
    have h := hres (ofNull 0 y z)
    rw [hgf, hι, hι, ureI_smul, ureL_ofNull] at h
    have := congrArg nullZ h
    rwa [nullZ_ofNull, nullZ_ofNull] at this
  have e1 := key 0 0
  have e2 := key 1 0
  have e3 := key 0 (T u)
  simp only [map_zero, zero_add, zero_smul, add_zero, one_smul, map_add] at e1 e2 e3
  have hw1 : J (T u) = ureV (k * ureθ) k := by linear_combination (norm := module) e2 - e1
  have hw2 : ureRot (k * ureθ) (J (T u)) = J (T u) := by linear_combination (norm := module) e1 - e3
  rw [hw1] at hw2
  by_cases hk : k = 0
  · subst hk
    apply hTu
    have h0 : J (T u) = 0 := by rw [hw1]; simpa using ureV_zero
    rw [← norm_eq_zero, ← J.norm_map, h0, norm_zero]
  · have c0 := congrArg (fun w : E3 => w 0) hw2
    have c1 := congrArg (fun w : E3 => w 1) hw2
    simp [ureRot_apply, ureV] at c0 c1
    have hpy := Real.sin_sq_add_cos_sq ((k : ℝ) * ureθ)
    have h1c : 1 - Real.cos (k * ureθ) ≠ 0 := sub_ne_zero.2 (Ne.symm (ure_cos_ne_one hk))
    have hc : Real.cos (k * ureθ) * (1 - Real.cos (k * ureθ)) = 0 := by
      linear_combination (1 / 2 : ℝ) * c0 - (1 / 2 : ℝ) * hpy
    have hs : Real.sin (k * ureθ) * (1 - Real.cos (k * ureθ)) = 0 := by
      linear_combination (1 / 2 : ℝ) * c1
    have hc0 := (mul_eq_zero.1 hc).resolve_right h1c
    have hs0 := (mul_eq_zero.1 hs).resolve_right h1c
    rw [hc0, hs0] at hpy
    norm_num at hpy

/-- **The counterexample** (`𝐌⁵`, Barbot's `n = 5`, `d = 3`). `Γ = {P(k, k) | k ∈ ℤ}`, `P(φ, a)`
the linear isometry `(x, y, z) ↦ (x − ⟨v, R z⟩ − (y/2)|v|², y, R z + y v)` with `R = R_φ` the
rotation of angle `φ` of the plane `(z₀, z₁)` and `v = (1 − cos φ, −sin φ, a)`; `S̃` the
hyperboloid `{minkQ = −1, t > 0}`. All the hypotheses but Bieberbach hold, and the conclusion
fails. -/
theorem exists_unipotent_restriction_counterexample :
    ∃ (G : Subgroup (isom (3 + 1))) (St : Set (Minkowski (3 + 1))), CCAction G St ∧
      (∀ γ ∈ G, linOf γ (ofNull 1 0 0) = ofNull 1 0 0) ∧
      (∀ γ ∈ G, ∀ p : Minkowski (3 + 1), nullY (γ • p) = nullY p) ∧
      (∃ γ ∈ G, IsParabolic (linOf γ)) ∧ ¬UnipotentRestrictionConclusion 3 G St :=
  ⟨ureG, ureSt, ure_ccAction, ure_hfix, ure_hb, ure_hpar, ure_not_conclusion⟩

/-- **The dispatched statement is false** (given Bieberbach's first theorem in `ℝ³`, an external
of DEC-36 and a true theorem): its instance `d = 3` fails on
`exists_unipotent_restriction_counterexample`. -/
theorem not_unipotentRestrictionStatement (hBieb : BieberbachI (EuclideanSpace ℝ (Fin 3))) :
    ¬UnipotentRestrictionStatement := fun h => by
  obtain ⟨G, St, h1, h2, h3, h4, h5⟩ := exists_unipotent_restriction_counterexample
  exact h5 (h 3 hBieb h1 h2 h3 h4)

end Causal.Flat.Nonlox
