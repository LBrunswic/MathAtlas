import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.Lox.TwoNullNormalForm
import CausalScaffold.Flat.Nonlox.NullFrame
import CausalScaffold.Flat.Nonlox.UnipotentFrame

/-!
# `CausalScaffold.Flat.Lox.MisnerFrame` — [10.M]: the two-null-vector frame and the normal form

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case", `papers/barbot/legacy/labeled/GHFspace.tex` l.3303–3323.
**No label is marked**: [10.M] is prose; this file is one step of `loxo_elementary_misner`
(`Flat/Loxodromic.lean`, the Misner identification, items (1)–(2) of its obstruction). Barbot's
`𝐌ⁿ` is `Minkowski (d + 1)` here (kb/0024): the null coordinates are `x`, `y` and `z ∈ ℝᵈ`.

> Let $P$ be the spacelike direction $\Delta_{0}^{\perp} \cap \Delta_{1}^{\perp}$, and
> $E$ the quotient space of \mink by $P$. (l.3303–3304)

> Then $\pi_{P}^{-1}(0)$ is a $\Gamma$-invariant spacelike subspace on which
> $\Gamma$ acts by isometries.
> In other words, there is a coordinate system $(x, z, y)$ on \mink such that
> the lorentzian quadratic form is $xy + \mid z \mid^{2}$ (where $\mid \mid$ is an euclidean norm)
> and such that elements of $\Gamma$ acts according to the law:
> \[ \gamma(x, z, y) = (e^{-a(\gamma)}x, R(\gamma)(z) + u(\gamma), e^{a(\gamma)}y) \]
> (l.3317–3323)

`misner_frame`: if `L(Γ₁)` fixes the two distinct points `u₀ ≠ u₁` of `𝒮` and `Γ₁` preserves the
two lightlike levels `{⟨(1,u₀)|·⟩ = s₀}` and `{⟨(1,u₁)|·⟩ = s₁}`, there is a frame `φ ∈ Isom(𝐌ⁿ)`
(origin on the spacelike `P = {⟨(1,u₀)|·⟩ = s₀} ∩ {⟨(1,u₁)|·⟩ = s₁}`, the two null lines on the
null axes `ofNull 1 0 0`, `ofNull 0 1 0`, in one of the two orders) such that
* `φ (ofNull x y z) ∈ Ω⁺({(u₀,s₀),(u₁,s₁)}) ↔ x > 0 ∧ y < 0` and
  `φ (ofNull x y z) ∈ Ω⁻({(u₀,s₀),(u₁,s₁)}) ↔ x < 0 ∧ y > 0` (whatever the order of the axes:
  in both orders the two half-spaces of `Ω⁺` read `x > 0`, `y < 0`);
* every `γ ∈ Γ₁` reads `φ⁻¹ γ φ (ofNull x y z) = ofNull (eᵃ x) (e⁻ᵃ y) (A z + u)` with `A` a
  linear isometry of `ℝᵈ` (Barbot's `R(γ)`), and `a ≠ 0` when `γ` is loxodromic.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(Γ)` fixes `Δ₀`, `Δ₁` (l.3298–3299) | ✓ carried, for `Γ₁` (`hfix₀`, `hfix₁`) |
| `Δ₀ ≠ Δ₁` | ✓ carried (`hne`) |
| `x(γ) = y(γ) = 0` (l.3315: the null levels through the origin are invariant) | ✓ carried as the invariant levels `hs₀`, `hs₁` (proved upstream, `exists_invariant_nullLevel_of_ccAction`) |
| the form `xy + ∣z∣²` (l.3320) | ⚠ reading: the library's `ofNull` coordinates, `minkQ (ofNull x y z) = 2xy + ‖z‖²` |

## SCOPE (disclosed)

* The sign of `a` is the library's (`misnerMap`: `x ↦ eᵃ x`), opposite to the paper's display
  (`x ↦ e^{-a} x`); immaterial.
* Proved, no `sorry`. The frame is built for `d ≥ 1` as `Nonlox.nf_exists_of_pos` (a spatial
  rotation taking `(1,u₀)` to `√2 · ofNull 1 0 0`) followed by the null rotation
  `Nonlox.ufrLin (ufrFrame b w)` (standard basis `b`, `w = Z/Y` read off the image of `(1,u₁)`),
  which fixes `ofNull 1 0 0` and takes that image to `Y · ofNull 0 1 0`, `Y < 0`; for `d = 0`,
  `𝒮 = {±1}` and the linear part is the identity, in whichever order `u₀`, `u₁` take `±1` (the
  second order is reduced to the first by `Set.pair_comm`). The origin is the point
  `(s₁/b)(1,u₀) + (s₀/b)(1,u₁)` of `P`, `b = ⟨(1,u₀)|(1,u₁)⟩ < 0`.
* The normal form: `L G L⁻¹` scales `x`, `y` by `e^{-a'}`, `e^{a'}` (`lorentz_normalForm_of_fix_two`)
  and kills the `z`-part of the two null axes, so it acts on `{x = y = 0}` by a linear map `A`
  preserving `‖·‖` (from `minkQ`); the translation `L(γ p₀ − p₀)` lies in `{x = y = 0}` (`hs₀`,
  `hs₁` at `p₀`); `a = −a'`, and `a ≠ 0` for a loxodromic `γ` is the dichotomy of the same lemma.
  Only the forward implications of `hs₀`, `hs₁` (at the single point `p₀`) are used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Causal.Flat Set
open scoped RealInnerProductSpace

section helpers

variable {d : ℕ}

private theorem mf_nullX_add (p q : Minkowski (d + 1)) : nullX (p + q) = nullX p + nullX q := by
  simp only [nullX, Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring

private theorem mf_nullY_add (p q : Minkowski (d + 1)) : nullY (p + q) = nullY p + nullY q := by
  simp only [nullY, Prod.fst_add, Prod.snd_add, PiLp.add_apply]; ring

private theorem mf_nullZ_add (p q : Minkowski (d + 1)) : nullZ (p + q) = nullZ p + nullZ q := by
  ext i; simp [nullZ]

private theorem mf_nullX_smul (c : ℝ) (p : Minkowski (d + 1)) : nullX (c • p) = c * nullX p := by
  simp only [nullX, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]; ring

private theorem mf_nullY_smul (c : ℝ) (p : Minkowski (d + 1)) : nullY (c • p) = c * nullY p := by
  simp only [nullY, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]; ring

private theorem mf_nullZ_smul (c : ℝ) (p : Minkowski (d + 1)) : nullZ (c • p) = c • nullZ p := by
  ext i; simp [nullZ]

private theorem mf_minkB_null (p q : Minkowski (d + 1)) :
    minkB p q = nullX p * nullY q + nullY p * nullX q + ⟪nullZ p, nullZ q⟫ := by
  have h := Causal.Flat.minkQ_add p q
  rw [minkQ_eq_null, minkQ_eq_null, minkQ_eq_null, mf_nullX_add, mf_nullY_add, mf_nullZ_add,
    norm_add_sq_real] at h
  linarith

private theorem mf_minkB_ex (p : Minkowski (d + 1)) :
    minkB (ofNull (d := d) 1 0 0) p = nullY p := by
  rw [mf_minkB_null]; simp [nullX_ofNull, nullY_ofNull, nullZ_ofNull]

private theorem mf_minkB_ey (p : Minkowski (d + 1)) :
    minkB (ofNull (d := d) 0 1 0) p = nullX p := by
  rw [mf_minkB_null]; simp [nullX_ofNull, nullY_ofNull, nullZ_ofNull]

private theorem mf_ofNull_decomp (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z = x • ofNull 1 0 0 + y • ofNull 0 1 0 + ofNull 0 0 z :=
  eq_of_null (by simp [mf_nullX_add, mf_nullX_smul, nullX_ofNull])
    (by simp [mf_nullY_add, mf_nullY_smul, nullY_ofNull])
    (fun i => by simp [mf_nullZ_add, mf_nullZ_smul, nullZ_ofNull])

private theorem mf_smul_ofNull (c x y : ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    c • ofNull x y z = ofNull (c * x) (c * y) (c • z) :=
  eq_of_null (by simp [mf_nullX_smul, nullX_ofNull]) (by simp [mf_nullY_smul, nullY_ofNull])
    (fun i => by simp [mf_nullZ_smul, nullZ_ofNull])

/-- The standard orthonormal basis has a coordinate map of determinant `1`. -/
private theorem mf_det_basisFun :
    LinearMap.det ((EuclideanSpace.basisFun (Fin d) ℝ).repr.toLinearEquiv :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = 1 := by
  have : ((EuclideanSpace.basisFun (Fin d) ℝ).repr.toLinearEquiv :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) = LinearMap.id :=
    LinearMap.ext fun v => by ext i; rfl
  rw [this, LinearMap.det_id]

/-- The frame for `d ≥ 1`. -/
private theorem mf_frame_pos (hd : 1 ≤ d) {u₀ u₁ : PenroseSphere (d + 1)} (hne : u₀ ≠ u₁) :
    ∃ L : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1), L ∈ lorentz (d + 1) ∧
      ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₁ < 0 ∧ L (nullVec u₀) = c₀ • ofNull 1 0 0 ∧
        L (nullVec u₁) = c₁ • ofNull 0 1 0 := by
  have hn : ‖(nullVec u₀).2‖ = (nullVec u₀).1 := by
    show ‖(u₀ : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1
    exact norm_eq_of_mem_sphere u₀
  obtain ⟨φ₁, -, hφ₁⟩ := Nonlox.nf_exists_of_pos hd hn
  set m := linOf φ₁ (nullVec u₁) with hm
  set X := nullX m
  set Y := nullY m
  set Z := nullZ m
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hc₀ : (0 : ℝ) < √2 * (nullVec u₀).1 := by
    show (0 : ℝ) < √2 * 1; linarith
  have hY : Y < 0 := by
    have h := lorentz.minkB_apply (linOf_mem φ₁) (nullVec u₀) (nullVec u₁)
    rw [hφ₁, minkB_smul_left, ← hm, mf_minkB_ex] at h
    have hB := lox_minkB_nullVec_neg hne
    nlinarith
  have hQ : 2 * X * Y + ‖Z‖ ^ 2 = 0 := by
    rw [← minkQ_eq_null, hm, lorentz.minkQ_apply (linOf_mem φ₁), minkQ_nullVec]
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  set w : EuclideanSpace ℝ (Fin d) := Y⁻¹ • Z
  have hF := Nonlox.ufrLin_mem_lorentz _ (Nonlox.ufrQ_ufrFrame b w) (Nonlox.ufrFrame_future b w)
    (Nonlox.det_ufrFrame b mf_det_basisFun w)
  set S := Nonlox.ufrLin (Nonlox.ufrFrame b w)
  have hSx : S (ofNull 1 0 0) = ofNull 1 0 0 := by
    simp only [S, Nonlox.ufrLin_apply, Nonlox.ufrCoord_apply, Nonlox.ufrFrame_apply,
      nullX_ofNull, nullY_ofNull, nullZ_ofNull]
    simp
  have hSm : S m = Y • ofNull 0 1 0 := by
    rw [mf_smul_ofNull]
    simp only [S, Nonlox.ufrLin_apply, Nonlox.ufrCoord_apply, Nonlox.ufrFrame_apply]
    have hY0 : Y ≠ 0 := hY.ne
    congr 1
    · have hZZ : ⟪Z, nullZ m⟫ = ‖Z‖ ^ 2 := real_inner_self_eq_norm_sq Z
      simp only [w, real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hZZ]
      field_simp
      linear_combination Y * hQ
    · ring
    · rw [smul_smul, mul_inv_cancel₀ hY0, one_smul, sub_self, map_zero, smul_zero]
  refine ⟨(linOf φ₁).trans S, ?_, √2 * (nullVec u₀).1, Y, hc₀, hY, ?_, ?_⟩
  · exact (lorentz (d + 1)).mul_mem hF (linOf_mem φ₁)
  · rw [LinearEquiv.trans_apply, hφ₁, map_smul, hSx]
  · rw [LinearEquiv.trans_apply, ← hm, hSm]

private theorem mf_ofNull_add (x y x' y' : ℝ) (z z' : EuclideanSpace ℝ (Fin d)) :
    ofNull x y z + ofNull x' y' z' = ofNull (x + x') (y + y') (z + z') :=
  eq_of_null (by simp [mf_nullX_add, nullX_ofNull]) (by simp [mf_nullY_add, nullY_ofNull])
    (fun i => by simp [mf_nullZ_add, nullZ_ofNull])

/-- In `𝐌²`, `(1, u)` for `u = 1` is `√2 · ofNull 1 0 0`. -/
private theorem mf_nullVec_one {u : PenroseSphere (0 + 1)}
    (h : (u : EuclideanSpace ℝ (Fin (0 + 1))) 0 = 1) :
    nullVec u = √2 • ofNull 1 0 (0 : EuclideanSpace ℝ (Fin 0)) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  refine eq_of_null ?_ ?_ (fun i => Fin.elim0 i)
  · rw [mf_nullX_smul, nullX_ofNull]
    show ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 + 1) / √2 = _
    rw [h, div_eq_iff hs.ne']; linarith
  · rw [mf_nullY_smul, nullY_ofNull]
    show ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 - 1) / √2 = _
    rw [h]; simp

/-- In `𝐌²`, `(1, u)` for `u = −1` is `−√2 · ofNull 0 1 0`. -/
private theorem mf_nullVec_neg_one {u : PenroseSphere (0 + 1)}
    (h : (u : EuclideanSpace ℝ (Fin (0 + 1))) 0 = -1) :
    nullVec u = (-√2) • ofNull 0 1 (0 : EuclideanSpace ℝ (Fin 0)) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  refine eq_of_null ?_ ?_ (fun i => Fin.elim0 i)
  · rw [mf_nullX_smul, nullX_ofNull]
    show ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 + 1) / √2 = _
    rw [h]; simp
  · rw [mf_nullY_smul, nullY_ofNull]
    show ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 - 1) / √2 = _
    rw [h, div_eq_iff hs.ne']; linarith

/-- In `𝐌²`, a point of `𝒮` is `±1`. -/
private theorem mf_sphere_zero (u : PenroseSphere (0 + 1)) :
    (u : EuclideanSpace ℝ (Fin (0 + 1))) 0 = 1 ∨ (u : EuclideanSpace ℝ (Fin (0 + 1))) 0 = -1 := by
  have hn := norm_eq_of_mem_sphere u
  have h2 : ‖(u : EuclideanSpace ℝ (Fin (0 + 1)))‖ ^ 2 =
      ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  rw [hn] at h2
  have : ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 - 1) *
      ((u : EuclideanSpace ℝ (Fin (0 + 1))) 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

/-- **The linear frame.** A Lorentz map sending `(1,u₀)`, `(1,u₁)` to positive multiples of the two
future null axes `ofNull 1 0 0`, `−ofNull 0 1 0`, in one of the two orders. -/
private theorem mf_frame {u₀ u₁ : PenroseSphere (d + 1)} (hne : u₀ ≠ u₁) :
    ∃ L : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1), L ∈ lorentz (d + 1) ∧
      ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₁ < 0 ∧
        ((L (nullVec u₀) = c₀ • ofNull 1 0 0 ∧ L (nullVec u₁) = c₁ • ofNull 0 1 0) ∨
          (L (nullVec u₁) = c₀ • ofNull 1 0 0 ∧ L (nullVec u₀) = c₁ • ofNull 0 1 0)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hs : (0 : ℝ) < √2 := by positivity
    have hne' : (u₀ : EuclideanSpace ℝ (Fin (0 + 1))) 0 ≠ (u₁ : EuclideanSpace ℝ (Fin (0 + 1))) 0 :=
      fun h => hne (Subtype.ext (by ext i; rw [show i = 0 from Fin.fin_one_eq_zero i]; exact h))
    refine ⟨LinearEquiv.refl ℝ _, (lorentz (0 + 1)).one_mem, √2, -√2, hs, by linarith, ?_⟩
    rcases mf_sphere_zero u₀ with h₀ | h₀ <;> rcases mf_sphere_zero u₁ with h₁ | h₁
    · exact absurd (h₀.trans h₁.symm) hne'
    · exact Or.inl ⟨mf_nullVec_one h₀, mf_nullVec_neg_one h₁⟩
    · exact Or.inr ⟨mf_nullVec_one h₁, mf_nullVec_neg_one h₀⟩
    · exact absurd (h₀.trans h₁.symm) hne'
  · obtain ⟨L, hL, c₀, c₁, h₀, h₁, e₀, e₁⟩ := mf_frame_pos hd hne
    exact ⟨L, hL, c₀, c₁, h₀, h₁, Or.inl ⟨e₀, e₁⟩⟩

/-- **The core**: from a linear frame in the first order, the frame `φ` and the normal form. -/
private theorem mf_core {Γ₁ : Subgroup (isom (d + 1))} {u₀ u₁ : PenroseSphere (d + 1)}
    (hne : u₀ ≠ u₁)
    (hfix₀ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hfix₁ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁) {s₀ s₁ : ℝ}
    (hs₀ : ∀ γ ∈ Γ₁, ∀ p : Minkowski (d + 1),
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀)
    (hs₁ : ∀ γ ∈ Γ₁, ∀ p : Minkowski (d + 1),
      minkB (nullVec u₁) p = s₁ → minkB (nullVec u₁) (γ • p) = s₁)
    (L : Minkowski (d + 1) ≃ₗ[ℝ] Minkowski (d + 1)) (hL : L ∈ lorentz (d + 1)) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 0) (hL0 : L (nullVec u₀) = c₀ • ofNull 1 0 0)
    (hL1 : L (nullVec u₁) = c₁ • ofNull 0 1 0) :
    ∃ φ : isom (d + 1),
      (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
        φ • ofNull x y z ∈ omegaPlus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d + 1) × ℝ)) ↔
          0 < x ∧ y < 0) ∧
      (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
        φ • ofNull x y z ∈ omegaMinus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d + 1) × ℝ)) ↔
          x < 0 ∧ 0 < y) ∧
      ∀ γ ∈ Γ₁, ∃ (a : ℝ) (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
        (u : EuclideanSpace ℝ (Fin d)),
        (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
          γ • (φ • ofNull x y z) = φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (A z + u)) ∧
        (IsLoxodromic (linOf γ) → a ≠ 0) := by
  have hb := lox_minkB_nullVec_neg hne
  have h00 : minkB (nullVec u₀) (nullVec u₀) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have h11 : minkB (nullVec u₁) (nullVec u₁) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  -- the origin, a point of `P`
  obtain ⟨p₀, hp₀, hp₁⟩ : ∃ p₀ : Minkowski (d + 1),
      minkB (nullVec u₀) p₀ = s₀ ∧ minkB (nullVec u₁) p₀ = s₁ := by
    refine ⟨(s₁ / minkB (nullVec u₀) (nullVec u₁)) • nullVec u₀ +
      (s₀ / minkB (nullVec u₀) (nullVec u₁)) • nullVec u₁, ?_, ?_⟩
    · rw [minkB_add_right, minkB_smul_right, minkB_smul_right, h00, mul_zero, zero_add,
        div_mul_cancel₀ _ hb.ne]
    · rw [minkB_add_right, minkB_smul_right, minkB_smul_right, h11, mul_zero, add_zero,
        minkB_comm (nullVec u₁) (nullVec u₀), div_mul_cancel₀ _ hb.ne]
  have hLi : L.symm ∈ lorentz (d + 1) := (lorentz (d + 1)).inv_mem hL
  obtain ⟨φ, hφ⟩ : ∃ φ : isom (d + 1), ∀ q, φ • q = L.symm q + p₀ := by
    refine ⟨⟨AffineEquiv.constVAdd ℝ (Minkowski (d + 1)) p₀, constVAdd_mem_isom p₀⟩ *
      Nonlox.nfIsom L.symm hLi, fun q => ?_⟩
    rw [mul_smul, Nonlox.nfIsom_smul]
    show p₀ +ᵥ L.symm q = _
    rw [vadd_eq_add]
    exact add_comm _ _
  have hB0 : ∀ q, minkB (nullVec u₀) (φ • q) = c₀ * nullY q + s₀ := fun q => by
    rw [hφ, minkB_add_right, hp₀]
    have h := lorentz.minkB_apply hL (nullVec u₀) (L.symm q)
    rw [LinearEquiv.apply_symm_apply, hL0, minkB_smul_left, mf_minkB_ex] at h
    rw [← h]
  have hB1 : ∀ q, minkB (nullVec u₁) (φ • q) = c₁ * nullX q + s₁ := fun q => by
    rw [hφ, minkB_add_right, hp₁]
    have h := lorentz.minkB_apply hL (nullVec u₁) (L.symm q)
    rw [LinearEquiv.apply_symm_apply, hL1, minkB_smul_left, mf_minkB_ey] at h
    rw [← h]
  refine ⟨φ, fun x y z => ?_, fun x y z => ?_, fun γ hγ => ?_⟩
  · rw [mem_omegaPlus]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, hB0, hB1,
      nullX_ofNull, nullY_ofNull]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rw [mem_omegaMinus]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, hB0, hB1,
      nullX_ofNull, nullY_ofNull]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  -- the normal form
  obtain ⟨a', hG0, hG1, -, hlox, -⟩ := lorentz_normalForm_of_fix_two hne (hfix₀ γ hγ) (hfix₁ γ hγ)
  rw [← linOf_eq_linearPart] at hG0 hG1 hlox
  have hG := linOf_mem γ
  have hG0' : ∀ v, minkB (nullVec u₀) (linOf γ v) = Real.exp a' * minkB (nullVec u₀) v :=
    fun v => by
      have h := lorentz.minkB_apply hG (nullVec u₀) v
      rw [hG0, minkB_smul_left] at h
      rw [← h, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hG1' : ∀ v, minkB (nullVec u₁) (linOf γ v) = Real.exp (-a') * minkB (nullVec u₁) v :=
    fun v => by
      have h := lorentz.minkB_apply hG (nullVec u₁) v
      rw [hG1, minkB_smul_left] at h
      rw [← h, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  -- the linear part `M = L G L⁻¹` read in the frame
  obtain ⟨M, hM⟩ : ∃ M : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1),
      ∀ q, M q = L (linOf γ (L.symm q)) :=
    ⟨(L : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)) ∘ₗ
      (linOf γ : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)) ∘ₗ
        (L.symm : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)), fun q => rfl⟩
  have hMQ : ∀ q, minkQ (M q) = minkQ q := fun q => by
    rw [hM, lorentz.minkQ_apply hL, lorentz.minkQ_apply hG, lorentz.minkQ_apply hLi]
  have hMY : ∀ q, nullY (M q) = Real.exp a' * nullY q := fun q => by
    have h := lorentz.minkB_apply hL (nullVec u₀) (linOf γ (L.symm q))
    rw [hL0, minkB_smul_left, mf_minkB_ex, hG0'] at h
    have h' := lorentz.minkB_apply hL (nullVec u₀) (L.symm q)
    rw [hL0, minkB_smul_left, mf_minkB_ex, LinearEquiv.apply_symm_apply] at h'
    have : c₀ * nullY (M q) = c₀ * (Real.exp a' * nullY q) := by rw [hM, h, ← h']; ring
    exact mul_left_cancel₀ hc₀.ne' this
  have hMX : ∀ q, nullX (M q) = Real.exp (-a') * nullX q := fun q => by
    have h := lorentz.minkB_apply hL (nullVec u₁) (linOf γ (L.symm q))
    rw [hL1, minkB_smul_left, mf_minkB_ey, hG1'] at h
    have h' := lorentz.minkB_apply hL (nullVec u₁) (L.symm q)
    rw [hL1, minkB_smul_left, mf_minkB_ey, LinearEquiv.apply_symm_apply] at h'
    have : c₁ * nullX (M q) = c₁ * (Real.exp (-a') * nullX q) := by rw [hM, h, ← h']; ring
    exact mul_left_cancel₀ hc₁.ne this
  have hMex : nullZ (M (ofNull 1 0 0)) = 0 := by
    have h : M (c₀ • ofNull 1 0 0) = (Real.exp (-a') * c₀) • ofNull 1 0 0 := by
      rw [← hL0, hM, LinearEquiv.symm_apply_apply, hG0, map_smul, hL0, smul_smul]
    rw [map_smul] at h
    have h2 := congrArg nullZ h
    rw [mf_nullZ_smul, mf_nullZ_smul, nullZ_ofNull, smul_zero] at h2
    exact (smul_eq_zero_iff_right hc₀.ne').1 h2
  have hMey : nullZ (M (ofNull 0 1 0)) = 0 := by
    have h : M (c₁ • ofNull 0 1 0) = (Real.exp a' * c₁) • ofNull 0 1 0 := by
      rw [← hL1, hM, LinearEquiv.symm_apply_apply, hG1, map_smul, hL1, smul_smul]
    rw [map_smul] at h
    have h2 := congrArg nullZ h
    rw [mf_nullZ_smul, mf_nullZ_smul, nullZ_ofNull, smul_zero] at h2
    exact (smul_eq_zero_iff_right hc₁.ne).1 h2
  -- the translation part `v = L(γ p₀ − p₀) ∈ P`
  set v := L (γ • p₀ - p₀) with hv_def
  have hvY : nullY v = 0 := by
    have h := lorentz.minkB_apply hL (nullVec u₀) (γ • p₀ - p₀)
    rw [hL0, minkB_smul_left, mf_minkB_ex, minkB_sub_right, hs₀ γ hγ p₀ hp₀, hp₀, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left hc₀.ne'
  have hvX : nullX v = 0 := by
    have h := lorentz.minkB_apply hL (nullVec u₁) (γ • p₀ - p₀)
    rw [hL1, minkB_smul_left, mf_minkB_ey, minkB_sub_right, hs₁ γ hγ p₀ hp₁, hp₁, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left hc₁.ne
  have hW : ∀ q, γ • (φ • q) = φ • (M q + v) := fun q => by
    rw [hφ, hφ, map_add, hM, hv_def, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      smul_eq_lin_add γ (L.symm q + p₀), smul_eq_lin_add γ p₀, map_add]
    abel
  -- the rotation `A` on `P`
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ z, A₀ z = nullZ (M (ofNull 0 0 z)) :=
    ⟨{ toFun := fun z => nullZ (M (ofNull 0 0 z))
       map_add' := fun z z' => by
         rw [← mf_nullZ_add, ← map_add, mf_ofNull_add]
         norm_num
       map_smul' := fun c z => by
         rw [RingHom.id_apply, ← mf_nullZ_smul, ← map_smul, mf_smul_ofNull, mul_zero] },
      fun z => rfl⟩
  have hA₀ : ∀ z, ‖A₀ z‖ = ‖z‖ := fun z => by
    have hq := hMQ (ofNull 0 0 z)
    rw [minkQ_eq_null, minkQ_eq_null, hMX, hMY, nullX_ofNull, nullY_ofNull, nullZ_ofNull] at hq
    have : ‖A₀ z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [hA₀def]
      linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  obtain ⟨A, hA⟩ : ∃ A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ z, A z = nullZ (M (ofNull 0 0 z)) :=
    ⟨LinearIsometry.toLinearIsometryEquiv ⟨A₀, hA₀⟩ rfl, fun z => hA₀def z⟩
  refine ⟨-a', A, nullZ v, fun x y z => ?_, fun h => neg_ne_zero.2 (hlox.1 h)⟩
  rw [hW]
  congr 1
  refine eq_of_null ?_ ?_ (fun i => ?_)
  · rw [mf_nullX_add, hMX, hvX, nullX_ofNull, nullX_ofNull, add_zero]
  · rw [mf_nullY_add, hMY, hvY, nullY_ofNull, nullY_ofNull, neg_neg, add_zero]
  · rw [mf_nullZ_add, nullZ_ofNull, mf_ofNull_decomp x y z, map_add, map_add, map_smul, map_smul,
      mf_nullZ_add, mf_nullZ_add, mf_nullZ_smul, mf_nullZ_smul, hMex, hMey, hA]
    simp

end helpers

/-- **[10.M] l.3303–3323: the frame and the normal form.** For `Γ₁ ≤ Isom(𝐌ⁿ)` whose linear parts
fix `u₀ ≠ u₁ ∈ 𝒮` and which preserves the lightlike levels `s₀` of `(1,u₀)` and `s₁` of `(1,u₁)`:
a frame `φ` in which `Ω^±({(u₀,s₀),(u₁,s₁)})` are the two Misner wedges and every `γ ∈ Γ₁` acts by
`(x, y, z) ↦ (eᵃ x, e⁻ᵃ y, A z + u)`, `a ≠ 0` for a loxodromic `γ`. -/
theorem misner_frame {d : ℕ} {Γ₁ : Subgroup (isom (d + 1))} {u₀ u₁ : PenroseSphere (d + 1)}
    (hne : u₀ ≠ u₁)
    (hfix₀ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₀ = u₀)
    (hfix₁ : ∀ γ ∈ Γ₁, lorentzSphere (linearPart γ) u₁ = u₁) {s₀ s₁ : ℝ}
    (hs₀ : ∀ γ ∈ Γ₁, ∀ p : Minkowski (d + 1),
      minkB (nullVec u₀) p = s₀ → minkB (nullVec u₀) (γ • p) = s₀)
    (hs₁ : ∀ γ ∈ Γ₁, ∀ p : Minkowski (d + 1),
      minkB (nullVec u₁) p = s₁ → minkB (nullVec u₁) (γ • p) = s₁) :
    ∃ φ : isom (d + 1),
      (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
        φ • ofNull x y z ∈ omegaPlus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d + 1) × ℝ)) ↔
          0 < x ∧ y < 0) ∧
      (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
        φ • ofNull x y z ∈ omegaMinus ({(u₀, s₀), (u₁, s₁)} : Set (PenroseSphere (d + 1) × ℝ)) ↔
          x < 0 ∧ 0 < y) ∧
      ∀ γ ∈ Γ₁, ∃ (a : ℝ) (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
        (u : EuclideanSpace ℝ (Fin d)),
        (∀ (x y : ℝ) (z : EuclideanSpace ℝ (Fin d)),
          γ • (φ • ofNull x y z) = φ • ofNull (Real.exp a * x) (Real.exp (-a) * y) (A z + u)) ∧
        (IsLoxodromic (linOf γ) → a ≠ 0) := by
  obtain ⟨L, hL, c₀, c₁, hc₀, hc₁, H⟩ := mf_frame hne
  rcases H with ⟨e₀, e₁⟩ | ⟨e₁, e₀⟩
  · exact mf_core hne hfix₀ hfix₁ hs₀ hs₁ L hL hc₀ hc₁ e₀ e₁
  · have h := mf_core hne.symm hfix₁ hfix₀ hs₁ hs₀ L hL hc₀ hc₁ e₁ e₀
    rwa [Set.pair_comm] at h

end Causal.Flat.Lox
