import Causal.Flat.Nonloxodromic
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# `Causal.Flat.Lox.SecondNullFix` — [10.M]: the second null direction `Δ₁` is fixed

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case" (`misnerr`), `papers/barbot/legacy/labeled/GHFspace.tex`
l.3260–3299. **No label is marked**: [10.M] is prose; this file proves one step of
`loxo_elementary_misner` (`Flat/Loxodromic.lean`).

> Let $\Gamma_{0}$ be the kernel of $a$: this is a discrete group of isometries of \mink.
> […] Since $\alpha(\Gamma')$ is discrete, it follows that every $v(\gamma')=0$ since we can
> choose as $\gamma$ a loxodromic element for which $a(\gamma)\neq 0$. (l.3260–3269)

> In other words, there is another isotropic direction $\Delta_{1}$ preserved by the entire
> group $L(\Gamma)$. (l.3298–3299)

`fix_second_of_frame` (in a null frame, `v₀ = ofNull 1 0 0`) and `fix_second_null` (frame-free):
if `Γ₁ ≤ Γ` (`CCAction Γ Σ`) has linear parts fixing the direction `u₀ ∈ 𝒮`, preserves a lightlike
level of `(1, u₀)` (Barbot's `b ≡ 0`), and contains a loxodromic `γ₁` whose second fixed point is
`u₁`, then **every** element of `L(Γ₁)` fixes `u₁` — no further finite-index passage.

## The proof (not the paper's)

The paper conjugates `γ' ∈ Γ₀ = ker a` by powers of a loxodromic `γ` and reads `v(γ') = 0` off
the discreteness of `α(Γ₀)`. Its formula for `α(γγ'γ⁻¹)` (l.3264–3265) omits the translation part
of `α(γ)`: when `γ` has a nonzero **screw** component (a translation along the fixed space of its
rotation `R(γ)`), `γⁿγ'γ⁻ⁿ` has translation part `n Rⁿ (I − R(γ')) u(γ) + …`, unbounded as soon as
`R(γ')` moves `u(γ)`, and the discreteness argument does not apply (finding F4, reported). Here:

1. **Slices.** `Γ₀` (in the frame: `L(γ) v₀ = v₀`) preserves the lightlike levels `{y = t}` and
   acts on each met slice by euclidean isometries `λ_t(γ)` (`Nonlox.uftHom`), a discrete faithful
   image (`Nonlox.uft_isDiscreteEucl`, `uftHom_injective`). Bieberbach I (the cited external) gives
   a finite-index `K ≤ Γ₀` acting by translations on an affine `U`, `K ≅ ℤᵏ`.
2. **Translation lengths, not translation parts.** For `x ∈ Γ₀` and `N = [Γ₀ : core K]`, the
   conjugates `hₙ = δ⁻ⁿ xᴺ δⁿ` lie in `K`; `λ_{t₀}(hₙ)` is conjugate by a euclidean isometry to
   `λ_{tₙ}(xᴺ)` with `tₙ` bounded (`δ = γ₁^{±1}` contracting the levels), so its translation vector
   on `U` is at most the displacement `‖λ_{tₙ}(xᴺ)(0)‖` (`norm_le_dist_of_translation`), bounded.
   Discreteness and faithfulness make the `hₙ` finitely many: `δᵏ` commutes with `xᴺ`, so `L(xᴺ)`
   fixes `u₁` (`eq_or_eq_of_fixed`). The screw never enters: a translation length is conjugation
   invariant, a translation part is not.
3. **Finite orbit.** `K ≅ ℤᵏ` and `S = Stab(u₁)` contains the `N`-th powers, so `K/(K ∩ S)` is a
   finitely generated torsion abelian group, finite (`Module.finite_of_fg_torsion`): the
   `L(Γ₀)`-orbit of `u₁` is finite, `L(δ)`-invariant, hence fixed by a power of `L(δ)`, hence
   `{u₁}`.
4. **All of `Γ₁`.** For `γ ∈ Γ₁`, `[γ, δ] ∈ Γ₀` fixes `u₁`, so `L(δ)` fixes `L(γ)⁻¹ u₁`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §8's setting (`S` complete, `Γ = π₁(S)`) | ⚠ strengthened (DEC-35 reading): `CCAction Γ Σ` |
| up to finite index `L(Γ)` fixes `Δ₀` (l.3237–3239) | ✓ carried, for `Γ₁` (`hf₀`) |
| `b ≡ 0` (l.3250–3257) | ✓ carried (`hlev`; proved upstream, `exists_invariant_nullLevel_of_ccAction`) |
| `γ₀` loxodromic, `Δ₁` its second direction (l.3239–3240) | ✓ carried (`hlox`, `hf₁`) |
| `α(Γ₀)` discrete (l.3267) | ⚠ replaced: discreteness of the slice actions (`uft_isDiscreteEucl`), from `CCAction` |
| Bieberbach (used implicitly through the nondiscrete part, l.3273–3287) | ✓ carried as the external `BieberbachI` (`hBieb`, DEC-36) |
| Auslander–Carrière–Dal'bo, Carrière–Dal'bo (the route through `Γ₀^{nd}` and `U`, l.3273–3287) | ⚠ weakened: not used |

## SCOPE (disclosed)

* The conclusion is stronger than the paper's "up to finite index": all of `L(Γ₁)` fixes `u₁`.
* Not covered here: the identification of a finite-index quotient with an LTP over a Misner
  spacetime (l.3302–3330), the remainder of `loxo_elementary_misner`.
* `set_option maxHeartbeats 1600000` on the private `snf_pow_fix` (Step 2, one long assembly).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The sphere-action
lemmas repeat `Flat.Lox.CommuteOnFix`'s private `cof_*` ones (not exported).
-/

namespace Causal.Flat.Lox

open Causal.Flat Causal.Flat.Nonlox Set Module
open scoped RealInnerProductSpace

variable {d : ℕ}

/-! ### The action on `𝒮` (copies of `CommuteOnFix`'s private lemmas) -/

section Sphere

private theorem snf_lorentzSphere_one (u : PenroseSphere d) :
    lorentzSphere (1 : lorentz d) u = u :=
  lorentzSphere_eq_of_eigen (c := 1) (by simp)

private theorem snf_lorentzSphere_mul (A B : lorentz d) (u : PenroseSphere d) :
    lorentzSphere (A * B) u = lorentzSphere A (lorentzSphere B u) := by
  have hA := (lorentzScale_pos A (lorentzSphere B u)).ne'
  have hB := (lorentzScale_pos B u).ne'
  have hAB := (lorentzScale_pos (A * B) u).ne'
  refine nullVec_injective_smul
    (c := (lorentzScale (A * B) u)⁻¹ * (lorentzScale A (lorentzSphere B u) * lorentzScale B u)) ?_
  rw [nullVec_lorentzSphere, nullVec_lorentzSphere A, nullVec_lorentzSphere B, map_smul,
    smul_smul, smul_smul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  congr 1
  field_simp

private theorem snf_lorentzSphere_injective (A : lorentz d) :
    Function.Injective (lorentzSphere A) := fun u u' h => by
  have := congrArg (lorentzSphere A⁻¹) h
  rwa [← snf_lorentzSphere_mul, ← snf_lorentzSphere_mul, inv_mul_cancel,
    snf_lorentzSphere_one, snf_lorentzSphere_one] at this

private theorem snf_lorentzSphere_pow (A : lorentz d) (n : ℕ) (u : PenroseSphere d) :
    lorentzSphere (A ^ n) u = (lorentzSphere A)^[n] u := by
  induction n with
  | zero => simp [snf_lorentzSphere_one]
  | succ n ih => rw [pow_succ', snf_lorentzSphere_mul, ih, Function.iterate_succ_apply']

private theorem snf_eigen_of_fixed {A : lorentz d} {u : PenroseSphere d}
    (h : lorentzSphere A u = u) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u := by
  have := nullVec_lorentzSphere A u
  rw [h] at this
  calc (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)
      = lorentzScale A u • ((lorentzScale A u)⁻¹ •
          (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) := by
        rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]
    _ = lorentzScale A u • nullVec u := by rw [← this]

private theorem snf_minkB_neg {u u' : PenroseSphere d} (h : u ≠ u') :
    minkB (nullVec u) (nullVec u') < 0 := by
  rw [minkB_nullVec_nullVec]
  have h0 : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h' => h (Subtype.ext h')
  have := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) 2
  linarith

private theorem snf_mul_eq_one {A : lorentz d} {u u' : PenroseSphere d} (hne : u ≠ u')
    {c c' : ℝ} (hc : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hc' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c' • nullVec u') : c * c' = 1 := by
  have h := lorentz.minkB_apply A.2 (nullVec u) (nullVec u')
  rw [hc, hc', minkB_smul_left, minkB_smul_right] at h
  have h0 := (snf_minkB_neg hne).ne
  have : (c * c' - 1) * minkB (nullVec u) (nullVec u') = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)

private theorem snf_fixed_unique {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = nullVec u') : u = u' := by
  by_contra h
  have e0 : minkB (nullVec u) (nullVec u) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have e0' : minkB (nullVec u') (nullVec u') = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hq : minkQ (nullVec u + nullVec u') < 0 := by
    rw [minkQ_eq_minkB, minkB_add_left, minkB_add_right, minkB_add_right, e0, e0',
      minkB_comm (nullVec u') (nullVec u)]
    linarith [snf_minkB_neg h]
  exact hne (isElliptic_of_fixed_timelike (fun v => lorentz.minkQ_apply A.2 v) hq
    (by rw [map_add, hu, hu']))

private theorem snf_same_eigen {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d} {c : ℝ}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c • nullVec u') : u = u' := by
  by_contra h
  have h1 := snf_mul_eq_one h hu hu'
  have hc := lorentz.eigen_pos_of_null A.2 (nullVec_ne_zero u) (minkQ_nullVec u) hu
  have hc1 : c = 1 := (mul_self_eq_one_iff.1 h1).resolve_right (by intro h'; linarith)
  rw [hc1, one_smul] at hu hu'
  exact h (snf_fixed_unique hne hu hu')

/-- **A non-elliptic element of `SO₀(1, d)` has at most two fixed points on `𝒮`.** -/
theorem eq_or_eq_of_fixed {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' x : PenroseSphere d}
    (huu' : u ≠ u') (hu : lorentzSphere A u = u) (hu' : lorentzSphere A u' = u')
    (hx : lorentzSphere A x = x) : x = u ∨ x = u' := by
  by_contra h
  push Not at h
  have e := snf_eigen_of_fixed hu
  have e' := snf_eigen_of_fixed hu'
  have ex := snf_eigen_of_fixed hx
  have h1 := snf_mul_eq_one h.1 ex e
  have h2 := snf_mul_eq_one h.2 ex e'
  have hs : lorentzScale A u = lorentzScale A u' :=
    mul_left_cancel₀ (lorentzScale_pos A x).ne' (h1.trans h2.symm)
  rw [hs] at e
  exact huu' (snf_same_eigen hne e e')

/-- A positive power of a loxodromic isometry has non-elliptic linear part. -/
theorem not_isElliptic_linearPart_pow {γ : isom d} (hlox : IsLoxodromic (linOf γ)) {k : ℕ}
    (hk : 0 < k) :
    ¬IsElliptic ((linearPart (γ ^ k) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
  have h := hlox.zpow_linOf (n := (k : ℤ)) (by exact_mod_cast hk.ne')
  rw [zpow_natCast, linOf_eq_linearPart] at h
  exact h.not_isElliptic

end Sphere

/-! ### Translation length bounds displacement -/

section MinDisplacement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem snf_dist_iterate_le (A : E ≃ᵃⁱ[ℝ] E) (y : E) (m : ℕ) :
    dist ((A ^ m) y) y ≤ m * dist (A y) y := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : dist ((A ^ (m + 1)) y) ((A ^ m) y) = dist (A y) y := by
      rw [pow_succ, AffineIsometryEquiv.coe_mul, Function.comp_apply, (A ^ m).dist_map]
    calc dist ((A ^ (m + 1)) y) y ≤ dist ((A ^ (m + 1)) y) ((A ^ m) y) + dist ((A ^ m) y) y :=
          dist_triangle _ _ _
      _ ≤ dist (A y) y + m * dist (A y) y := by rw [h1]; linarith
      _ = ((m + 1 : ℕ) : ℝ) * dist (A y) y := by push_cast; ring

/-- **The translation vector of an isometry on a subspace it translates is at most its
displacement anywhere**: `‖c‖ ≤ dist (A y) y` (the translation length is the minimal
displacement). -/
theorem norm_le_dist_of_translation {A : E ≃ᵃⁱ[ℝ] E} {U : AffineSubspace ℝ E} {c : E}
    (hc : c ∈ U.direction) (hU : ∀ q ∈ U, A q = c +ᵥ q) {q₀ : E} (hq₀ : q₀ ∈ U) (y : E) :
    ‖c‖ ≤ dist (A y) y := by
  by_contra hlt
  push Not at hlt
  set δ := dist (A y) y
  set D := dist y q₀
  have hpos : 0 < ‖c‖ - δ := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * D / (‖c‖ - δ))
  have hpow : (A ^ m) q₀ = (m • c) +ᵥ q₀ := pow_apply_of_translation hc hU m q₀ hq₀
  have h1 : dist ((A ^ m) q₀) q₀ = m * ‖c‖ := by
    rw [hpow, dist_vadd_left, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
  have h2 : dist ((A ^ m) q₀) q₀ ≤ dist ((A ^ m) q₀) ((A ^ m) y) + dist ((A ^ m) y) y +
      dist y q₀ := dist_triangle4 _ _ _ _
  rw [(A ^ m).dist_map, dist_comm q₀ y] at h2
  have h3 := snf_dist_iterate_le A y m
  have h4 : (m : ℝ) * (‖c‖ - δ) ≤ 2 * D := by nlinarith
  rw [div_lt_iff₀ hpos] at hm
  linarith

end MinDisplacement

/-! ### The null frame: slices and levels -/

section Frame

private theorem snf_nullZ_sub (p q : Minkowski (d + 1)) : nullZ (p - q) = nullZ p - nullZ q := by
  have := congrArg (fun X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ => X.2.1) (map_sub ufrCoord p q)
  simpa [ufrCoord_apply] using this

private theorem snf_nullZ_smul (r : ℝ) (p : Minkowski (d + 1)) : nullZ (r • p) = r • nullZ p := by
  have := congrArg (fun X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ => X.2.1) (map_smul ufrCoord r p)
  simp only [ufrCoord_apply, Prod.smul_snd, Prod.smul_fst] at this
  exact this

private theorem snf_ofNull_smul (r : ℝ) : ofNull r 0 (0 : EuclideanSpace ℝ (Fin d)) =
    r • (ofNull 1 0 0 : Minkowski (d + 1)) := by
  rw [nsl_ofNull_eq, nsl_ofNull_eq, ← map_smul]
  congr 1
  simp

private theorem snf_smul_sub (γ : isom (d + 1)) (p q : Minkowski (d + 1)) :
    γ • p - γ • q = linOf γ (p - q) := by
  rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel

private theorem snf_nullY_eq (p : Minkowski (d + 1)) : nullY p = minkB p (ofNull 1 0 0) :=
  (nsl_minkB_v₀ p).symm

/-- `nullY (L(γ) w) = c⁻¹ nullY w` when `L(γ) v₀ = c v₀`. -/
theorem nullY_linOf_of_scale {γ : isom (d + 1)} {c : ℝ} (hc : c ≠ 0)
    (hL : linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0) (w : Minkowski (d + 1)) :
    nullY (linOf γ w) = c⁻¹ * nullY w := by
  have hv : linOf γ (c⁻¹ • ofNull 1 0 0) = ofNull 1 0 0 := by
    rw [map_smul, hL, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [snf_nullY_eq, ← hv, lorentz.minkB_apply (linOf_mem γ), minkB_smul_right, ← snf_nullY_eq]

/-- **(F-c) Levels go to levels**: `y(γp) − y(γp') = c⁻¹ (y(p) − y(p'))`. -/
theorem nullY_smul_sub_of_scale {γ : isom (d + 1)} {c : ℝ} (hc : c ≠ 0)
    (hL : linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0) (p p' : Minkowski (d + 1)) :
    nullY (γ • p) - nullY (γ • p') = c⁻¹ * (nullY p - nullY p') := by
  rw [← ULTP.nullY_sub, snf_smul_sub, nullY_linOf_of_scale hc hL, ULTP.nullY_sub]

/-- **(F-a) The slice coordinate does not see `x`.** -/
theorem nullZ_smul_ofNull_indep {γ : isom (d + 1)} {c : ℝ}
    (hL : linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0) (X X' t : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    nullZ (γ • ofNull X t z) = nullZ (γ • ofNull X' t z) := by
  have h := snf_smul_sub γ (ofNull X t z) (ofNull X' t z)
  rw [nsl_ofNull_sub, sub_self, sub_self,
    snf_ofNull_smul, map_smul, hL, smul_smul] at h
  have := congrArg nullZ h
  rw [snf_nullZ_sub, snf_nullZ_smul, nullZ_ofNull, smul_zero] at this
  exact sub_eq_zero.1 this

/-- **(F-b) On a slice, `γ` is an isometry of the slice coordinate.** -/
theorem dist_nullZ_smul_ofNull {γ : isom (d + 1)} {c : ℝ} (hc : c ≠ 0)
    (hL : linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0) (X t : ℝ)
    (z z' : EuclideanSpace ℝ (Fin d)) :
    dist (nullZ (γ • ofNull X t z)) (nullZ (γ • ofNull X t z')) = dist z z' := by
  rw [dist_eq_norm, dist_eq_norm, ← snf_nullZ_sub, snf_smul_sub, nsl_ofNull_sub, sub_self,
    sub_self]
  set W := linOf γ (ofNull 0 0 (z - z'))
  have hY : nullY W = 0 := by
    rw [nullY_linOf_of_scale hc hL, nullY_ofNull, mul_zero]
  have hQ : minkQ W = ‖z - z'‖ ^ 2 := by
    rw [lorentz.minkQ_apply (linOf_mem γ), minkQ_eq_null, nullX_ofNull, nullY_ofNull,
      nullZ_ofNull]; ring
  rw [minkQ_eq_null, hY, mul_zero, zero_add] at hQ
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hQ

end Frame

/-! ### The group `Γ₀ = ker a` in the frame -/

section Group

private theorem snf_linOf_mul_apply (γ δ : isom (d + 1)) (v : Minkowski (d + 1)) :
    linOf (γ * δ) v = linOf γ (linOf δ v) := rfl

private theorem snf_linOf_inv_scale {γ : isom (d + 1)} {c : ℝ} (hc : c ≠ 0)
    (hL : linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0) :
    linOf γ⁻¹ (ofNull 1 0 0) = c⁻¹ • ofNull 1 0 0 := by
  have h1 : linOf γ⁻¹ (linOf γ (ofNull 1 0 0)) = ofNull 1 0 0 := by
    rw [← snf_linOf_mul_apply, inv_mul_cancel]; rfl
  rw [hL, map_smul] at h1
  calc linOf γ⁻¹ (ofNull 1 0 0) = c⁻¹ • (c • linOf γ⁻¹ (ofNull 1 0 0)) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • ofNull 1 0 0 := by rw [h1]

/-- **`Γ₀ = ker a`, in the frame** (l.3259): the elements of `G₁` whose linear part fixes the
null vector `v₀ = ofNull 1 0 0` (not only its direction). -/
def snfKer (G₁ : Subgroup (isom (d + 1))) : Subgroup (isom (d + 1)) where
  carrier := {γ | γ ∈ G₁ ∧ linOf γ (ofNull 1 0 0) = ofNull 1 0 0}
  mul_mem' := fun {a b} ha hb => ⟨G₁.mul_mem ha.1 hb.1, by rw [snf_linOf_mul_apply, hb.2, ha.2]⟩
  one_mem' := ⟨G₁.one_mem, rfl⟩
  inv_mem' := fun {a} ha => ⟨G₁.inv_mem ha.1, by
    have := snf_linOf_inv_scale (c := 1) one_ne_zero (by rw [one_smul]; exact ha.2)
    rwa [inv_one, one_smul] at this⟩

/-- Membership in `snfKer G₁`. -/
theorem mem_snfKer {G₁ : Subgroup (isom (d + 1))} {γ : isom (d + 1)} :
    γ ∈ snfKer G₁ ↔ γ ∈ G₁ ∧ linOf γ (ofNull 1 0 0) = ofNull 1 0 0 := Iff.rfl

/-- `Γ₀` satisfies the slice hypotheses `UftHyp` when `G₁` preserves the level `{y = s}`. -/
theorem uftHyp_snfKer {G₁ : Subgroup (isom (d + 1))} {s : ℝ}
    (hlev : ∀ γ ∈ G₁, ∀ p : Minkowski (d + 1), nullY p = s → nullY (γ • p) = s) :
    UftHyp (snfKer G₁) := by
  refine ⟨fun γ hγ => hγ.2, fun γ hγ p => ?_⟩
  have h := nullY_smul_sub_of_scale (c := 1) one_ne_zero (by rw [one_smul]; exact hγ.2) p
    (ofNull 0 s 0)
  rw [hlev γ hγ.1 _ (nullY_ofNull _ _ _), nullY_ofNull, inv_one, one_mul] at h
  linarith

/-- `Γ₀` is normal in `G₁` when `L(G₁)` scales `v₀`. -/
theorem conj_mem_snfKer {G₁ : Subgroup (isom (d + 1))}
    (hdir : ∀ γ ∈ G₁, ∃ c : ℝ, 0 < c ∧ linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0)
    {γ x : isom (d + 1)} (hγ : γ ∈ G₁) (hx : x ∈ snfKer G₁) : γ * x * γ⁻¹ ∈ snfKer G₁ := by
  obtain ⟨c, hc, hL⟩ := hdir γ hγ
  refine ⟨G₁.mul_mem (G₁.mul_mem hγ hx.1) (G₁.inv_mem hγ), ?_⟩
  rw [snf_linOf_mul_apply, snf_linOf_mul_apply, snf_linOf_inv_scale hc.ne' hL, map_smul, hx.2, map_smul,
    hL, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

end Group

/-! ### The theorem in the frame -/

section Main

private theorem snf_fix_inv {A : lorentz d} {u : PenroseSphere d} (h : lorentzSphere A u = u) :
    lorentzSphere A⁻¹ u = u := by
  have := congrArg (lorentzSphere A⁻¹) h
  rwa [← snf_lorentzSphere_mul, inv_mul_cancel, snf_lorentzSphere_one, eq_comm] at this

private theorem snf_fix_pow {A : lorentz d} {u : PenroseSphere d} (h : lorentzSphere A u = u)
    (n : ℕ) : lorentzSphere (A ^ n) u = u := by
  rw [snf_lorentzSphere_pow]; exact Function.iterate_fixed h n

set_option maxHeartbeats 1600000 in
/-- **Step 2 (translation lengths)**: for every `x ∈ Γ₀`, `L(x^N)` fixes `u₁`, where `N` is the
index of a normal finite-index subgroup `K'` of `Γ₀` acting (on the slice `t₀`) by translations on
a nonempty affine `U`. -/
private theorem snf_pow_fix {G₁ : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))}
    {s : ℝ} (hlev : ∀ γ ∈ G₁, ∀ p : Minkowski (d + 1), nullY p = s → nullY (γ • p) = s)
    (hdir : ∀ γ ∈ G₁, ∃ c : ℝ, 0 < c ∧ linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0)
    (hcc : CCAction (snfKer G₁) St) {t₀ : ℝ} (ht₀ : t₀ ∈ nullY '' St)
    {δ : isom (d + 1)} (hδ : δ ∈ G₁) (hδlox : IsLoxodromic (linOf δ)) {c : ℝ} (hc : 1 ≤ c)
    (hLδ : linOf δ (ofNull 1 0 0) = c • ofNull 1 0 0)
    {u₀ u₁ : PenroseSphere (d + 1)} (hne : u₀ ≠ u₁)
    (hf₀ : ∀ γ ∈ G₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hf₁ : lorentzSphere (linearPart δ) u₁ = u₁)
    {K' : Subgroup (snfKer G₁)} [K'.Normal]
    {U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d))} {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ U)
    (htr : ∀ y ∈ K', ∃ v ∈ U.direction, ∀ q ∈ U,
      uftHom (uftHyp_snfKer hlev) t₀ y q = v +ᵥ q)
    (x : snfKer G₁) :
    lorentzSphere (linearPart ((x : isom (d + 1)) ^ K'.index)) u₁ = u₁ := by
  have hG : UftHyp (snfKer G₁) := uftHyp_snfKer hlev
  set N := K'.index
  set g : isom (d + 1) := (x : isom (d + 1)) ^ N with hgdef
  have hg : g ∈ snfKer G₁ := (snfKer G₁).pow_mem x.2 N
  have hgG₁ : g ∈ G₁ := hg.1
  have hpowδ : ∀ n : ℕ, linOf (δ ^ n) (ofNull 1 0 0) = c ^ n • ofNull 1 0 0 := by
    intro n
    induction n with
    | zero => simp; rfl
    | succ n ih =>
      rw [pow_succ, snf_linOf_mul_apply, hLδ, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hcn : ∀ n : ℕ, c ^ n ≠ 0 := fun n => (pow_pos hcpos n).ne'
  set B := ‖(uftData g).2.1‖ + (|s| + |t₀ - s|) * ‖(uftData g).2.2.1‖
  -- the conjugates `hₙ = δ⁻ⁿ g δⁿ`
  have hmem : ∀ n : ℕ, (δ ^ n)⁻¹ * g * δ ^ n ∈ snfKer G₁ := fun n => by
    have := conj_mem_snfKer hdir (G₁.inv_mem (G₁.pow_mem hδ n)) hg
    rwa [inv_inv] at this
  have hxmem : ∀ n : ℕ, (δ ^ n)⁻¹ * (x : isom (d + 1)) * δ ^ n ∈ snfKer G₁ := fun n => by
    have := conj_mem_snfKer hdir (G₁.inv_mem (G₁.pow_mem hδ n)) x.2
    rwa [inv_inv] at this
  have hK' : ∀ n : ℕ, (⟨_, hmem n⟩ : snfKer G₁) ∈ K' := fun n => by
    have h := Subgroup.pow_index_mem K' (⟨_, hxmem n⟩ : snfKer G₁)
    convert h using 1
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow]
    rw [hgdef]
    have := conj_pow (a := (δ ^ n)⁻¹) (b := (x : isom (d + 1))) (i := N)
    rw [inv_inv] at this
    exact this.symm
  have hbound : ∀ n : ℕ, uftHom hG t₀ ⟨_, hmem n⟩ ∈
      {f | f ∈ (uftHom hG t₀).range ∧ dist (f p) p ≤ B} := by
    intro n
    refine ⟨⟨_, rfl⟩, ?_⟩
    obtain ⟨v, hv, hvq⟩ := htr _ (hK' n)
    set tₙ := nullY (δ ^ n • (ofNull 0 t₀ 0 : Minkowski (d + 1))) with htₙ
    set P := (δ ^ n)⁻¹ • (ofNull 0 tₙ 0 : Minkowski (d + 1)) with hP
    have hLn : linOf (δ ^ n)⁻¹ (ofNull 1 0 0) = (c ^ n)⁻¹ • ofNull 1 0 0 :=
      snf_linOf_inv_scale (hcn n) (hpowδ n)
    have hPy : nullY P = t₀ := by
      have h1 := nullY_smul_sub_of_scale (hcn n) (hpowδ n) P (ofNull 0 t₀ 0)
      rw [hP, smul_inv_smul, nullY_ofNull, ← htₙ, sub_self, nullY_ofNull] at h1
      have h2 := (mul_eq_zero.1 h1.symm).resolve_left (inv_ne_zero (hcn n))
      linarith
    have hPeq : P = ofNull (nullX P) t₀ (nullZ P) := by
      conv_lhs => rw [← nsl_ofNull_null P]
      rw [hPy]
    -- the displacement at `y = nullZ P`
    have hdisp : dist (uftHom hG t₀ ⟨_, hmem n⟩ (nullZ P)) (nullZ P) =
        ‖uftSlice tₙ g 0‖ := by
      rw [uftHom_apply, uftSlice_eq_nullZ hG (hmem n) t₀ (nullX P) (nullZ P), ← hPeq]
      have e1 : ((δ ^ n)⁻¹ * g * δ ^ n) • P =
          (δ ^ n)⁻¹ • (g • (ofNull 0 tₙ 0 : Minkowski (d + 1))) := by
        rw [mul_smul, mul_smul, hP, smul_inv_smul]
      rw [e1, uft_smul_ofNull hG hg tₙ 0 0, hP,
        nullZ_smul_ofNull_indep hLn 0 (nullX (g • (ofNull 0 tₙ 0 : Minkowski (d + 1)))) tₙ 0,
        dist_nullZ_smul_ofNull (inv_ne_zero (hcn n)) hLn, dist_zero_right]
    have hw : ‖uftSlice tₙ g 0‖ ≤ B := by
      rw [uftSlice_apply, map_zero, zero_add]
      have ht : |tₙ| ≤ |s| + |t₀ - s| := by
        have h1 := nullY_smul_sub_of_scale (hcn n) (hpowδ n) (ofNull 0 t₀ 0) (ofNull 0 s 0)
        rw [hlev _ (G₁.pow_mem hδ n) _ (nullY_ofNull _ _ _), nullY_ofNull, nullY_ofNull,
          ← htₙ] at h1
        have hle1 : (c ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
        have hpos : 0 < (c ^ n)⁻¹ := inv_pos.2 (pow_pos hcpos n)
        have : |tₙ - s| ≤ |t₀ - s| := by
          rw [h1, abs_mul, abs_of_pos hpos]
          exact mul_le_of_le_one_left (abs_nonneg _) hle1
        calc |tₙ| = |s + (tₙ - s)| := by ring_nf
          _ ≤ |s| + |tₙ - s| := abs_add_le _ _
          _ ≤ |s| + |t₀ - s| := by linarith
      calc ‖tₙ • (uftData g).2.2.1 + (uftData g).2.1‖
          ≤ ‖tₙ • (uftData g).2.2.1‖ + ‖(uftData g).2.1‖ := norm_add_le _ _
        _ = |tₙ| * ‖(uftData g).2.2.1‖ + ‖(uftData g).2.1‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (|s| + |t₀ - s|) * ‖(uftData g).2.2.1‖ + ‖(uftData g).2.1‖ := by
          gcongr
        _ = B := by ring
    have hvn : ‖v‖ ≤ B :=
      (norm_le_dist_of_translation hv hvq hp (nullZ P)).trans (hdisp ▸ hw)
    rw [hvq p hp, dist_vadd_left]
    exact hvn
  -- pigeonhole: two equal conjugates, so a power of `δ` commutes with `g`
  have hfin := uft_isDiscreteEucl hcc hG ht₀ p B
  obtain ⟨n, m, hnm, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => uftHom hG t₀ ⟨_, hmem n⟩) hbound
  have heq' : (δ ^ n)⁻¹ * g * δ ^ n = (δ ^ m)⁻¹ * g * δ ^ m :=
    congrArg Subtype.val (uftHom_injective hcc hG ht₀ heq)
  set k := m - n with hk
  have hkpos : 0 < k := by omega
  have hcomm : δ ^ k * g = g * δ ^ k := by
    have hm : δ ^ m = δ ^ k * δ ^ n := by rw [← pow_add]; congr 1; omega
    rw [hm] at heq'
    calc δ ^ k * g = δ ^ k * (δ ^ n * ((δ ^ n)⁻¹ * g * δ ^ n) * (δ ^ n)⁻¹) := by group
      _ = δ ^ k * (δ ^ n * ((δ ^ k * δ ^ n)⁻¹ * g * (δ ^ k * δ ^ n)) * (δ ^ n)⁻¹) := by
          rw [heq']
      _ = g * δ ^ k := by group
  -- `L(δᵏ)` fixes `L(g) u₁`
  set A := linearPart (δ ^ k)
  have hAu₁ : lorentzSphere A u₁ = u₁ := by
    show lorentzSphere (linearPart (δ ^ k)) u₁ = u₁
    rw [map_pow]; exact snf_fix_pow hf₁ k
  have hfix : lorentzSphere A (lorentzSphere (linearPart g) u₁) =
      lorentzSphere (linearPart g) u₁ := by
    rw [← snf_lorentzSphere_mul, ← map_mul, hcomm, map_mul, snf_lorentzSphere_mul, hAu₁]
  rcases eq_or_eq_of_fixed (not_isElliptic_linearPart_pow hδlox hkpos) hne
      (hf₀ _ (G₁.pow_mem hδ k)) hAu₁ hfix with h0 | h1
  · exfalso
    rw [← hf₀ g hgG₁] at h0
    exact hne (snf_lorentzSphere_injective _ h0).symm
  · exact h1

/-- The stabiliser of `u₁` in `Γ₀`, as a subgroup of the subtype. -/
private def snfStab (G₁ : Subgroup (isom (d + 1))) (u₁ : PenroseSphere (d + 1)) :
    Subgroup (snfKer G₁) where
  carrier := {x | lorentzSphere (linearPart (x : isom (d + 1))) u₁ = u₁}
  mul_mem' := fun {a b} ha hb => by
    show lorentzSphere (linearPart ((a : isom (d + 1)) * (b : isom (d + 1)))) u₁ = u₁
    rw [map_mul, snf_lorentzSphere_mul, hb, ha]
  one_mem' := by
    show lorentzSphere (linearPart (1 : isom (d + 1))) u₁ = u₁
    rw [map_one, snf_lorentzSphere_one]
  inv_mem' := fun {a} ha => by
    show lorentzSphere (linearPart ((a : isom (d + 1))⁻¹)) u₁ = u₁
    rw [map_inv]; exact snf_fix_inv ha

/-- A finitely generated free abelian `K` whose `N`-th powers lie in `S` meets `S` with finite
index (`K/(K ∩ S)` is finitely generated and torsion). -/
private theorem snf_relIndex_ne_zero {H : Type*} [Group H] {K S : Subgroup H} {r : ℕ}
    (e : Additive K ≃+ (Fin r →₀ ℤ)) {N : ℕ} (hN : N ≠ 0) (hpow : ∀ x ∈ K, x ^ N ∈ S) :
    (S.subgroupOf K).index ≠ 0 := by
  set T : AddSubgroup (Fin r →₀ ℤ) := ((S.subgroupOf K).toAddSubgroup).map e.toAddMonoidHom
  have hT : T.index = (S.subgroupOf K).index := by
    rw [← Subgroup.index_toAddSubgroup]
    exact AddSubgroup.index_map_equiv _ e
  haveI : Module.Finite ℤ ((Fin r →₀ ℤ) ⧸ T) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' T).toIntLinearMap
      (QuotientAddGroup.mk'_surjective T)
  have htors : Module.IsTorsion ℤ ((Fin r →₀ ℤ) ⧸ T) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk'_surjective T q
    have hN' : (N : ℤ) ∈ nonZeroDivisors ℤ := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN)
    refine ⟨⟨_, hN'⟩, ?_⟩
    show (N : ℤ) • (QuotientAddGroup.mk' T m) = 0
    rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
    refine ⟨N • e.symm m, ?_, by simp⟩
    show Additive.toMul (N • e.symm m) ∈ S.subgroupOf K
    rw [toMul_nsmul, Subgroup.mem_subgroupOf, SubgroupClass.coe_pow]
    exact hpow _ (Additive.toMul (e.symm m)).2
  haveI : Finite ((Fin r →₀ ℤ) ⧸ T) := Module.finite_of_fg_torsion _ htors
  rw [← hT]
  exact AddSubgroup.index_ne_zero_of_finite

/-- `Γₑ.comap f ≃* Γₑ` for an injective `f` with `Γₑ ≤ range f`. -/
private noncomputable def snf_comapEquiv {H M : Type*} [Group H] [Group M] (f : H →* M)
    (hf : Function.Injective f) {Γe : Subgroup M} (hΓe : Γe ≤ f.range) : Γe.comap f ≃* Γe :=
  ((Γe.comap f).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hΓe))

/-- **Step 1 (Bieberbach on a slice)**: a finite-index `K ≤ Γ₀`, free abelian of finite rank,
acting on the slice `t₀` by translations on a nonempty affine `U`. -/
private theorem snf_exists_K (hBieb : BieberbachI (EuclideanSpace ℝ (Fin d)))
    {G : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))} (hcc : CCAction G St)
    (hG : UftHyp G) {t₀ : ℝ} (ht₀ : t₀ ∈ nullY '' St) :
    ∃ K : Subgroup G, K.index ≠ 0 ∧ (∃ r : ℕ, Nonempty (Additive K ≃+ (Fin r →₀ ℤ))) ∧
      ∃ U : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)), ∃ p ∈ U,
        ∀ y ∈ K, ∃ v ∈ U.direction, ∀ q ∈ U, uftHom hG t₀ y q = v +ᵥ q := by
  have hdisc := uft_isDiscreteEucl hcc hG ht₀
  obtain ⟨U, ⟨p, hp⟩, -, Γe, hΓeR, hfi, htr, heff⟩ := hBieb _ hdisc
  obtain ⟨⟨e⟩, -⟩ := virtuallyFree_of_actsByTranslationsOn hdisc hΓeR ⟨p, hp⟩ htr heff
  refine ⟨Γe.comap (uftHom hG t₀), ?_, ⟨_, ⟨((snf_comapEquiv _ (uftHom_injective hcc hG ht₀)
    hΓeR).toAdditive).trans e⟩⟩, U, p, hp, fun y hy => htr _ hy⟩
  have e' : Γe.comap (uftHom hG t₀) =
      (Γe.subgroupOf (uftHom hG t₀).range).comap (uftHom hG t₀).rangeRestrict := by
    ext γ; simp [Subgroup.mem_subgroupOf]
  rw [e', Subgroup.index_comap_of_surjective _ (uftHom hG t₀).rangeRestrict_surjective]
  exact hfi.index_ne_zero

/-- The orbit of `u₁` under `L(Γ₀)` is finite when its stabiliser has finite index. -/
private theorem snf_orbit_finite {G₁ : Subgroup (isom (d + 1))} {u₁ : PenroseSphere (d + 1)}
    (hSi : (snfStab G₁ u₁).index ≠ 0) :
    (Set.range fun x : snfKer G₁ => lorentzSphere (linearPart (x : isom (d + 1))) u₁).Finite := by
  haveI : Finite (snfKer G₁ ⧸ snfStab G₁ u₁) := Subgroup.index_ne_zero_iff_finite.1 hSi
  let F : snfKer G₁ ⧸ snfStab G₁ u₁ → PenroseSphere (d + 1) :=
    Quotient.lift (fun x : snfKer G₁ => lorentzSphere (linearPart (x : isom (d + 1))) u₁)
      (fun a b hab => by
        have h : a⁻¹ * b ∈ snfStab G₁ u₁ := QuotientGroup.leftRel_apply.1 hab
        have h' : lorentzSphere (linearPart ((a⁻¹ * b : snfKer G₁) : isom (d + 1))) u₁ = u₁ := h
        have hb : (b : isom (d + 1)) = (a : isom (d + 1)) * ((a⁻¹ * b : snfKer G₁) : isom (d + 1)) := by
          simp
        show lorentzSphere (linearPart (a : isom (d + 1))) u₁ =
          lorentzSphere (linearPart (b : isom (d + 1))) u₁
        rw [hb, map_mul, snf_lorentzSphere_mul, h'])
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- **[10.M], l.3260–3299, in a null frame**: if `G₁ ≤ Γ` (`CCAction Γ Σ`) scales the null
vector `v₀ = ofNull 1 0 0`, preserves the level `{y = s}`, fixes `u₀ ∈ 𝒮`, and contains a
loxodromic `γ₁` fixing `u₁ ≠ u₀`, then every element of `L(G₁)` fixes `u₁`. Bieberbach I in
`ℝᵈ` is the cited external. -/
theorem fix_second_of_frame (hBieb : BieberbachI (EuclideanSpace ℝ (Fin d)))
    {Γ G₁ : Subgroup (isom (d + 1))} {St : Set (Minkowski (d + 1))} (hcc : CCAction Γ St)
    (hle : G₁ ≤ Γ)
    (hdir : ∀ γ ∈ G₁, ∃ c : ℝ, 0 < c ∧ linOf γ (ofNull 1 0 0) = c • ofNull 1 0 0)
    {s : ℝ} (hlev : ∀ γ ∈ G₁, ∀ p : Minkowski (d + 1), nullY p = s → nullY (γ • p) = s)
    {γ₁ : isom (d + 1)} (hγ₁ : γ₁ ∈ G₁) (hlox : IsLoxodromic (linOf γ₁))
    {u₀ u₁ : PenroseSphere (d + 1)} (hne : u₀ ≠ u₁)
    (hf₀ : ∀ γ ∈ G₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hf₁ : lorentzSphere (linearPart γ₁) u₁ = u₁) :
    ∀ γ ∈ G₁, lorentzSphere (linearPart γ) u₁ = u₁ := by
  -- `δ = γ₁^{±1}`, scaling `v₀` by `c ≥ 1`
  obtain ⟨δ, hδ, hδlox, hδf, c, hc, hLδ⟩ : ∃ δ ∈ G₁, IsLoxodromic (linOf δ) ∧
      lorentzSphere (linearPart δ) u₁ = u₁ ∧ ∃ c : ℝ, 1 ≤ c ∧
        linOf δ (ofNull 1 0 0) = c • ofNull 1 0 0 := by
    obtain ⟨c₁, hc₁, hL₁⟩ := hdir γ₁ hγ₁
    by_cases h1 : 1 ≤ c₁
    · exact ⟨γ₁, hγ₁, hlox, hf₁, c₁, h1, hL₁⟩
    · push Not at h1
      refine ⟨γ₁⁻¹, G₁.inv_mem hγ₁, ?_, ?_, c₁⁻¹, (one_le_inv₀ hc₁).2 h1.le,
        snf_linOf_inv_scale hc₁.ne' hL₁⟩
      · have := hlox.zpow_linOf (n := -1) (by norm_num)
        rwa [zpow_neg_one] at this
      · rw [map_inv]; exact snf_fix_inv hf₁
  have hδne : ¬IsElliptic ((linearPart δ : lorentz (d + 1)) :
      Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1)) := by
    have := not_isElliptic_linearPart_pow hδlox (k := 1) one_pos
    rwa [pow_one] at this
  -- `Γ₀ = ker a` and its slices
  have hG : UftHyp (snfKer G₁) := uftHyp_snfKer hlev
  have hccG : CCAction (snfKer G₁) St := hcc.mono fun γ hγ => hle hγ.1
  obtain ⟨σ, hσ⟩ := hcc.nonempty
  have ht₀ : nullY σ ∈ nullY '' St := ⟨σ, hσ, rfl⟩
  obtain ⟨K, hKi, ⟨r, ⟨eK⟩⟩, U, p, hp, htr⟩ := snf_exists_K hBieb hccG hG ht₀
  haveI : K.FiniteIndex := ⟨hKi⟩
  -- step 2: `L(xᴺ)` fixes `u₁`, `N` the index of the normal core of `K`
  have hP : ∀ x : snfKer G₁,
      lorentzSphere (linearPart ((x : isom (d + 1)) ^ K.normalCore.index)) u₁ = u₁ :=
    snf_pow_fix hlev hdir hccG ht₀ hδ hδlox hc hLδ hne hf₀ hδf (K' := K.normalCore) hp
      (fun y hy => htr _ (Subgroup.normalCore_le K hy))
  -- step 3: the stabiliser `S` of `u₁` has finite index in `Γ₀`
  have hSK : ((snfStab G₁ u₁).subgroupOf K).index ≠ 0 :=
    snf_relIndex_ne_zero eK Subgroup.FiniteIndex.index_ne_zero fun x _ => by
      show lorentzSphere (linearPart (((x ^ K.normalCore.index : snfKer G₁)) : isom (d + 1))) u₁ = u₁
      simpa only [SubgroupClass.coe_pow] using hP x
  have hSi : (snfStab G₁ u₁).index ≠ 0 := by
    have h := Subgroup.relIndex_ne_zero_trans (H := snfStab G₁ u₁) (K := K) (L := ⊤) hSK
      (by rw [Subgroup.relIndex_top_right]; exact hKi)
    rwa [Subgroup.relIndex_top_right] at h
  have hO := snf_orbit_finite hSi
  -- step 3': the orbit is `L(δ)`-invariant, so it is `{u₁}`
  have hinvO : ∀ z ∈ Set.range fun x : snfKer G₁ => lorentzSphere (linearPart (x : isom (d + 1))) u₁,
      lorentzSphere (linearPart δ) z ∈
        Set.range fun x : snfKer G₁ => lorentzSphere (linearPart (x : isom (d + 1))) u₁ := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨_, conj_mem_snfKer hdir hδ x.2⟩, ?_⟩
    show lorentzSphere (linearPart (δ * (x : isom (d + 1)) * δ⁻¹)) u₁ = _
    rw [map_mul, map_mul, snf_lorentzSphere_mul, snf_lorentzSphere_mul, map_inv,
      snf_fix_inv hδf]
  have hall0 : ∀ x : snfKer G₁, lorentzSphere (linearPart (x : isom (d + 1))) u₁ = u₁ := by
    intro x
    have hiter : ∀ j : ℕ, (lorentzSphere (linearPart δ))^[j]
        (lorentzSphere (linearPart (x : isom (d + 1))) u₁) ∈
        Set.range fun x : snfKer G₁ => lorentzSphere (linearPart (x : isom (d + 1))) u₁ := by
      intro j
      induction j with
      | zero => exact ⟨x, rfl⟩
      | succ j ih => rw [Function.iterate_succ_apply']; exact hinvO _ ih
    obtain ⟨i, j, hij, heq⟩ := hO.exists_lt_map_eq_of_forall_mem hiter
    have hfixy : lorentzSphere (linearPart (δ ^ (j - i)))
        (lorentzSphere (linearPart (x : isom (d + 1))) u₁) =
        lorentzSphere (linearPart (x : isom (d + 1))) u₁ := by
      rw [map_pow, snf_lorentzSphere_pow]
      refine (snf_lorentzSphere_injective (linearPart δ)).iterate i ?_
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
      exact heq.symm
    rcases eq_or_eq_of_fixed (not_isElliptic_linearPart_pow hδlox (by omega : 0 < j - i)) hne
        (hf₀ _ (G₁.pow_mem hδ _)) (by rw [map_pow]; exact snf_fix_pow hδf _) hfixy with h0 | h1
    · exfalso
      rw [← hf₀ _ x.2.1] at h0
      exact hne (snf_lorentzSphere_injective _ h0).symm
    · exact h1
  -- step 4: all of `G₁`, through the commutator `[γ, δ] ∈ Γ₀`
  intro γ hγ
  obtain ⟨cγ, hcγ, hLγ⟩ := hdir γ hγ
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have hcomm : γ * δ * γ⁻¹ * δ⁻¹ ∈ snfKer G₁ := by
    refine ⟨G₁.mul_mem (G₁.mul_mem (G₁.mul_mem hγ hδ) (G₁.inv_mem hγ)) (G₁.inv_mem hδ), ?_⟩
    rw [snf_linOf_mul_apply, snf_linOf_inv_scale hcpos.ne' hLδ, map_smul, snf_linOf_mul_apply,
      snf_linOf_inv_scale hcγ.ne' hLγ, map_smul, snf_linOf_mul_apply, hLδ, map_smul, hLγ, smul_smul,
      smul_smul, smul_smul]
    rw [show c⁻¹ * cγ⁻¹ * c * cγ = 1 by field_simp, one_smul]
  have hc1 := hall0 ⟨_, hcomm⟩
  have hγw : lorentzSphere (linearPart γ) (lorentzSphere (linearPart γ⁻¹) u₁) = u₁ := by
    rw [← snf_lorentzSphere_mul, ← map_mul, mul_inv_cancel, map_one, snf_lorentzSphere_one]
  have hδw : lorentzSphere (linearPart δ) (lorentzSphere (linearPart γ⁻¹) u₁) =
      lorentzSphere (linearPart γ⁻¹) u₁ := by
    have e1 : γ * δ * γ⁻¹ = (γ * δ * γ⁻¹ * δ⁻¹) * δ := by group
    have h2 : lorentzSphere (linearPart (γ * δ * γ⁻¹)) u₁ = u₁ := by
      rw [e1, map_mul, snf_lorentzSphere_mul, hδf]; exact hc1
    rw [map_mul, map_mul, snf_lorentzSphere_mul, snf_lorentzSphere_mul] at h2
    exact snf_lorentzSphere_injective _ (h2.trans hγw.symm)
  rcases eq_or_eq_of_fixed hδne hne (hf₀ δ hδ) hδf hδw with h0 | h1
  · exfalso
    rw [h0, hf₀ γ hγ] at hγw
    exact hne hγw
  · rw [h1] at hγw; exact hγw

end Main

/-- A fixed point of `A` on `𝒮` is fixed by every power of `A`. -/
theorem lorentzSphere_fix_pow {A : lorentz d} {u : PenroseSphere d} (h : lorentzSphere A u = u)
    (n : ℕ) : lorentzSphere (A ^ n) u = u :=
  snf_fix_pow h n

/-! ### The frame-free statement -/

section FrameFree

/-- `𝒮` in `𝐌²` has two points. -/
private theorem snf_sphere_one {x y z : PenroseSphere (0 + 1)} (hxy : x ≠ y) : z = x ∨ z = y := by
  have hcoord : ∀ w : PenroseSphere (0 + 1),
      (w : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨ (w : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
    intro w
    have h := norm_penroseSphere w
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
      Real.sqrt_sq_eq_abs] at h
    exact (abs_eq zero_le_one).1 h
  have hext : ∀ w w' : PenroseSphere (0 + 1),
      (w : EuclideanSpace ℝ (Fin 1)) 0 = (w' : EuclideanSpace ℝ (Fin 1)) 0 → w = w' := by
    intro w w' h
    refine Subtype.ext ?_
    ext i
    fin_cases i
    exact h
  rcases hcoord x with hx | hx <;> rcases hcoord y with hy | hy <;>
    rcases hcoord z with hz | hz
  all_goals first
    | exact absurd (hext x y (hx.trans hy.symm)) hxy
    | exact Or.inl (hext z x (hz.trans hx.symm))
    | exact Or.inr (hext z y (hz.trans hy.symm))

/-- **[10.M], l.3260–3299: the second null direction is fixed by all of `L(Γ₁)`** (Barbot's
"there is another isotropic direction `Δ₁` preserved by the entire group `L(Γ)`", for `Γ₁`). Let
`Γ₁ ≤ Γ` with `CCAction Γ Σ`, `L(Γ₁)` fixing `u₀ ∈ 𝒮`, `Γ₁` preserving the lightlike level
`{⟨(1,u₀) | ·⟩ = s₀}` (`b ≡ 0`), and `γ₁ ∈ Γ₁` loxodromic fixing `u₁ ≠ u₀`. Under Bieberbach I in
`ℝ^{d'}` (the cited external, DEC-36), every element of `L(Γ₁)` fixes `u₁`. Proof: in a null frame
(`Nonlox.nf_exists_of_pos`), `fix_second_of_frame`; in `𝐌²` (`d' = 0`) `𝒮` has two points. -/
theorem fix_second_null {d' : ℕ} (hBieb : BieberbachI (EuclideanSpace ℝ (Fin d')))
    {Γ Γ₁ : Subgroup (isom (d' + 1))} {St : Set (Minkowski (d' + 1))} (hcc : CCAction Γ St)
    (hle : Γ₁ ≤ Γ) {γ₁ : isom (d' + 1)} (hγ₁ : γ₁ ∈ Γ₁) (hlox : IsLoxodromic (linOf γ₁))
    {u₀ u₁ : PenroseSphere (d' + 1)} (hne : u₀ ≠ u₁)
    (hf₀ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hf₁ : lorentzSphere (linearPart γ₁) u₁ = u₁) {s₀ : ℝ}
    (hs₀ : ∀ γ ∈ Γ₁, ∀ p : Minkowski (d' + 1),
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀) :
    ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁ := by
  rcases Nat.eq_zero_or_pos d' with rfl | hd
  · intro γ hγ
    rcases snf_sphere_one (z := lorentzSphere (linearPart γ) u₁) hne with h0 | h1
    · exfalso
      rw [← hf₀ γ hγ] at h0
      exact hne (snf_lorentzSphere_injective _ h0).symm
    · exact h1
  -- the frame `φ`: `L(φ)(1, u₀) = √2 · v₀`
  obtain ⟨φ, hφlin, hφv⟩ := nf_exists_of_pos (d := d') hd (v := nullVec u₀) (by
    simp [nullVec])
  set c₀ : ℝ := √2 * (nullVec u₀).1 with hc₀
  have hc₀pos : 0 < c₀ := by simp [hc₀, nullVec]
  have hφinv : linOf φ⁻¹ (ofNull 1 0 0) = c₀⁻¹ • nullVec u₀ := by
    have h1 : linOf φ⁻¹ (linOf φ (nullVec u₀)) = nullVec u₀ := by
      rw [← snf_linOf_mul_apply, inv_mul_cancel]; rfl
    rw [hφv, map_smul] at h1
    calc linOf φ⁻¹ (ofNull 1 0 0) = c₀⁻¹ • (c₀ • linOf φ⁻¹ (ofNull 1 0 0)) := by
          rw [smul_smul, inv_mul_cancel₀ hc₀pos.ne', one_smul]
      _ = c₀⁻¹ • nullVec u₀ := by rw [h1]
  have hφsphere : ∀ (γ : isom (d' + 1)) (u : PenroseSphere (d' + 1)),
      lorentzSphere (linearPart (φ * γ * φ⁻¹)) (lorentzSphere (linearPart φ) u) =
        lorentzSphere (linearPart φ) (lorentzSphere (linearPart γ) u) := by
    intro γ u
    rw [map_mul, map_mul, snf_lorentzSphere_mul, snf_lorentzSphere_mul, ← snf_lorentzSphere_mul
      (linearPart φ⁻¹), ← map_mul, inv_mul_cancel, map_one, snf_lorentzSphere_one]
  -- the frame data
  have hmemconj : ∀ γ', γ' ∈ frameConj φ Γ₁ ↔ ∃ γ ∈ Γ₁, φ * γ * φ⁻¹ = γ' := by
    intro γ'
    simp only [frameConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hle' : frameConj φ Γ₁ ≤ frameConj φ Γ := Subgroup.map_mono hle
  have hdir : ∀ γ' ∈ frameConj φ Γ₁, ∃ c : ℝ, 0 < c ∧
      linOf γ' (ofNull 1 0 0) = c • ofNull 1 0 0 := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := (hmemconj γ').1 hγ'
    have e := snf_eigen_of_fixed (hf₀ γ hγ)
    rw [← linOf_eq_linearPart] at e
    refine ⟨lorentzScale (linearPart γ) u₀, lorentzScale_pos _ _, ?_⟩
    rw [snf_linOf_mul_apply, snf_linOf_mul_apply, hφinv, map_smul, e, smul_smul, map_smul, hφv,
      smul_smul]
    congr 1
    field_simp
  have hlev : ∀ γ' ∈ frameConj φ Γ₁, ∀ p : Minkowski (d' + 1), nullY p = c₀⁻¹ * s₀ →
      nullY (γ' • p) = c₀⁻¹ * s₀ := by
    have hY : ∀ q : Minkowski (d' + 1),
        nullY (φ • q) = c₀⁻¹ * minkB (nullVec u₀) q := by
      intro q
      rw [snf_nullY_eq, hφlin, show (ofNull 1 0 0 : Minkowski (d' + 1)) =
        linOf φ (c₀⁻¹ • nullVec u₀) by rw [map_smul, hφv, smul_smul, inv_mul_cancel₀ hc₀pos.ne',
          one_smul], lorentz.minkB_apply (linOf_mem φ), minkB_smul_right, minkB_comm]
    intro γ' hγ' p hp
    obtain ⟨γ, hγ, rfl⟩ := (hmemconj γ').1 hγ'
    have hp' : minkB (nullVec u₀) (φ⁻¹ • p) = s₀ := by
      have := hY (φ⁻¹ • p)
      rw [smul_inv_smul, hp] at this
      have h2 := mul_left_cancel₀ (inv_ne_zero hc₀pos.ne') this
      exact h2.symm
    rw [mul_smul, mul_smul, hY, hs₀ γ hγ _ hp']
  have hloxf : IsLoxodromic (linOf (φ * γ₁ * φ⁻¹)) := by
    rw [linOf_mul, linOf_mul, linOf_inv]
    exact hlox.conj (linOf_mem φ)
  have hfr := fix_second_of_frame hBieb (hcc.frameConj_smul φ) hle' hdir hlev
    ((hmemconj _).2 ⟨γ₁, hγ₁, rfl⟩) hloxf
    (u₀ := lorentzSphere (linearPart φ) u₀) (u₁ := lorentzSphere (linearPart φ) u₁)
    (fun h => hne (snf_lorentzSphere_injective _ h))
    (fun γ' hγ' => by
      obtain ⟨γ, hγ, rfl⟩ := (hmemconj γ').1 hγ'
      rw [hφsphere, hf₀ γ hγ])
    (by rw [hφsphere, hf₁])
  intro γ hγ
  have h := hfr _ ((hmemconj _).2 ⟨γ, hγ, rfl⟩)
  rw [hφsphere] at h
  exact snf_lorentzSphere_injective _ h

end FrameFree



end Causal.Flat.Lox
