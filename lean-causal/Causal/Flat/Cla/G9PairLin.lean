import CausalScaffold.Flat.Lox.TwoNullNormalForm

/-!
# `CausalScaffold.Flat.Cla.G9PairLin` — linear algebra of a fixed pair of `𝒮`: the eigenvalue homomorphism, the swap's determinant, and the discreteness of the boost parameter

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), proof of
Theorem B (`bthm:cauclo`, l.353–359; proof l.3536–3548) in its elementary-loxodromic case, the
pair case of G9d (NE) (`Flat/Cla/G9.lean`, `false_of_cauchyCompact_of_fixed_pair`). **No label is
certified here**: these are the linear-algebra inputs of `Flat/Cla/G9Pair.lean`. Line numbers are
those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's `𝐌ⁿ` has total
dimension `n`; the library's `Minkowski d` has `d` spatial dimensions, so `n = d + 1`.

> Consider now the action of $L(\Gamma)$ on the hyperbolic space ${\bf H}^{n-1}$:
> since $L(\Gamma^{nd}_{0})$ is trivial, $L(\Gamma_{0})$ is a finite group. (l.3285–3286)

> In other words, there is another  isotropic direction $\Delta_{1}$
> preserved by the entire group $L(\Gamma)$. (l.3298–3299)

## What is proved (no `sorry`)

For two distinct points `u₁ ≠ u₂` of `𝒮`, `n_i = (1, u_i)`:

* `pairScale_eigen` — a Lorentz map fixing `u₁` and `u₂` on `𝒮` is `n₁ ↦ c n₁`, `n₂ ↦ c⁻¹ n₂`,
  `c = lorentzScale A u₁` (Barbot's `e^{∓a(γ)}`, l.3303–3323); `lorentzScale_mul_of_fix`: `c` is
  multiplicative on the stabiliser.
* `false_of_swap_fix_perp` — **no element of `SO₀(1, d)` exchanges the two null lines and fixes
  `P^⊥ = n₁^⊥ ∩ n₂^⊥` pointwise**: such a map is the Lorentz reflection in `s = n₁ − α n₂`, of
  determinant `−1` (`det_id_sub_smulRight`, the matrix determinant lemma).
* `sq_norm_le_minkQ_of_perp` — on `P^⊥` the sup norm of `Minkowski d` is dominated by `minkQ`.
* `norm_linToCLM_le_of_fix_pair` — Lorentz maps fixing `u₁, u₂` with `|log c| ≤ R` are bounded in
  operator norm.
* `finite_of_discrete_of_norm_le` — a norm-bounded (with inverses) subset of a discrete subgroup
  of `SO₀(1, d)` (`lorentzTopology`) is finite.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(Γ)` discrete (Def 4.18, l.1212–1214) | ✓ carried where used (`finite_of_discrete_of_norm_le`) |
| the two isotropic directions `Δ₀ ≠ Δ₁` | ✓ carried (`u₁ ≠ u₂`) |

## SCOPE (disclosed)

Pure linear algebra and the topology of `SO₀(1, d)`; the group-theoretic and causal use is in
`Flat/Cla/G9Pair.lean`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology Causal Causal.Flat

variable {d : ℕ}

section PairLin

variable {u₁ u₂ : PenroseSphere d}

/-- `⟨n₁ | n₂⟩ ≠ 0` for distinct points of `𝒮`. -/
theorem minkB_nullVec_ne_zero_of_ne (hne : u₁ ≠ u₂) : minkB (nullVec u₁) (nullVec u₂) ≠ 0 :=
  (Lox.lox_minkB_nullVec_neg hne).ne

/-- **The eigenvalues on a fixed pair**: a Lorentz map fixing `u₁ ≠ u₂ ∈ 𝒮` is `n₁ ↦ c n₁`,
`n₂ ↦ c⁻¹ n₂` with `c = lorentzScale A u₁ > 0`. -/
theorem pairScale_eigen (hne : u₁ ≠ u₂) {A : lorentz d} (h1 : lorentzSphere A u₁ = u₁)
    (h2 : lorentzSphere A u₂ = u₂) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁) = lorentzScale A u₁ • nullVec u₁ ∧
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₂) = (lorentzScale A u₁)⁻¹ • nullVec u₂ := by
  have e₁ := Lox.lox_apply_nullVec_of_fix h1
  have e₂ := Lox.lox_apply_nullVec_of_fix h2
  have hB := minkB_nullVec_ne_zero_of_ne hne
  have hc₁ := lorentzScale_pos A u₁
  have hcc : lorentzScale A u₁ * lorentzScale A u₂ = 1 := by
    have h := lorentz.minkB_apply A.2 (nullVec u₁) (nullVec u₂)
    rw [e₁, e₂, minkB_smul_left, minkB_smul_right, ← mul_assoc] at h
    have h' : (lorentzScale A u₁ * lorentzScale A u₂ - 1) * minkB (nullVec u₁) (nullVec u₂) = 0 := by
      linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact absurd h'' hB
  refine ⟨e₁, ?_⟩
  rw [e₂, eq_inv_of_mul_eq_one_right hcc]

/-- The scale on a fixed point of `𝒮` is multiplicative. -/
theorem lorentzScale_mul_of_fix {A B : lorentz d} {u : PenroseSphere d}
    (hB : lorentzSphere B u = u) : lorentzScale (A * B) u = lorentzScale A u * lorentzScale B u := by
  have e := Lox.lox_apply_nullVec_of_fix hB
  show (((A * B : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).1 = _
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, e, map_smul, Prod.smul_fst, smul_eq_mul, mul_comm]
  rfl

/-- **The matrix determinant lemma for a rank-one perturbation of the identity**:
`det (id − φ ⊗ s) = 1 − φ(s)`. -/
theorem det_id_sub_smulRight {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (s : V) : LinearMap.det (LinearMap.id - φ.smulRight s) = 1 - φ s := by
  set b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (LinearMap.id - φ.smulRight s) =
      1 + Matrix.replicateCol Unit (-(b.repr s : Fin (Module.finrank ℝ V) → ℝ)) *
        Matrix.replicateRow Unit (fun j => φ (b j)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, Matrix.mul_apply,
      mul_comm, sub_eq_add_neg, eq_comm]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : φ s = ∑ j, φ (b j) * b.repr s j := by
    calc φ s = φ (∑ j, b.repr s j • b j) := by rw [b.sum_repr]
      _ = ∑ j, φ (b j) * b.repr s j := by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  rw [hs]
  simp [dotProduct, sub_eq_add_neg]

/-- **No element of `SO₀(1, d)` exchanges the null lines of `u₁ ≠ u₂` while fixing
`P^⊥ = n₁^⊥ ∩ n₂^⊥` pointwise**: it would be the Lorentz reflection in `s = n₁ − α₁ n₂`
(`v ↦ v − 2⟨s|v⟩/⟨s|s⟩ s`), of determinant `−1`. -/
theorem false_of_swap_fix_perp (hne : u₁ ≠ u₂) {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) {α₁ α₂ : ℝ} (hα₁ : α₁ ≠ 0) (h1 : A (nullVec u₁) = α₁ • nullVec u₂)
    (h2 : A (nullVec u₂) = α₂ • nullVec u₁)
    (hperp : ∀ v, minkB v (nullVec u₁) = 0 → minkB v (nullVec u₂) = 0 → A v = v) : False := by
  set n₁ := nullVec u₁
  set n₂ := nullVec u₂
  set β := minkB n₁ n₂ with hβdef
  have hβ : β ≠ 0 := minkB_nullVec_ne_zero_of_ne hne
  have hq₁ : minkB n₁ n₁ = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hq₂ : minkB n₂ n₂ = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have h21 : minkB n₂ n₁ = β := minkB_comm _ _
  -- `α₁ α₂ = 1`
  have hαα : α₁ * α₂ = 1 := by
    have h := lorentz.minkB_apply hA n₁ n₂
    rw [h1, h2, minkB_smul_left, minkB_smul_right, h21] at h
    have h' : (α₁ * α₂ - 1) * β = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact absurd h'' hβ
  set s : Minkowski d := n₁ - α₁ • n₂ with hsdef
  have hs₁ : minkB s n₁ = -(α₁ * β) := by
    rw [hsdef, minkB_sub_left, minkB_smul_left, hq₁, h21]; ring
  have hs₂ : minkB s n₂ = β := by
    rw [hsdef, minkB_sub_left, minkB_smul_left, hq₂]; ring
  have hss : minkB s s = -(2 * α₁ * β) := by
    rw [show minkB s s = minkB s n₁ - α₁ * minkB s n₂ by
      rw [hsdef, minkB_sub_right, minkB_smul_right]]
    rw [hs₁, hs₂]; ring
  have hss0 : minkB s s ≠ 0 := by
    rw [hss]; exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero hα₁) hβ)
  set φ : Minkowski d →ₗ[ℝ] ℝ := (2 / minkB s s) • minkForm d s with hφ
  have hφapp : ∀ v, φ v = 2 / minkB s s * minkB s v := fun v => by
    simp [hφ, minkForm_apply]
  set R : Minkowski d →ₗ[ℝ] Minkowski d := LinearMap.id - φ.smulRight s with hR
  have hRapp : ∀ v, R v = v - (2 / minkB s s * minkB s v) • s := fun v => by
    simp [hR, hφapp]
  -- `A = R` on `n₁`, `n₂` and `P^⊥`, hence everywhere
  have hR1 : R n₁ = A n₁ := by
    rw [hRapp, hs₁, hss, h1, hsdef]
    have : 2 / -(2 * α₁ * β) * -(α₁ * β) = 1 := by field_simp
    rw [this, one_smul]; abel
  have hR2 : R n₂ = A n₂ := by
    rw [hRapp, hs₂, hss, h2, hsdef]
    have hα₂ : α₂ = α₁⁻¹ := eq_inv_of_mul_eq_one_right hαα
    rw [hα₂]
    have : 2 / -(2 * α₁ * β) * β = -α₁⁻¹ := by field_simp
    rw [this, smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hα₁]
    module
  have hRP : ∀ w, minkB w n₁ = 0 → minkB w n₂ = 0 → R w = A w := by
    intro w hw₁ hw₂
    have : minkB s w = 0 := by
      rw [hsdef, minkB_sub_left, minkB_smul_left, minkB_comm n₁ w, minkB_comm n₂ w, hw₁, hw₂]
      ring
    rw [hRapp, this, mul_zero, zero_smul, sub_zero, hperp w hw₁ hw₂]
  have hRA : (A : Minkowski d →ₗ[ℝ] Minkowski d) = R := by
    refine LinearMap.ext fun v => ?_
    have hv := eq_nullV_add (u := n₁) (u' := n₂) v
    have hw₁ := minkB_nullV_left (minkQ_nullVec u₁) hβ v
    have hw₂ := minkB_nullV_right (minkQ_nullVec u₂) hβ v
    show A v = R v
    rw [hv, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul, map_smul, hR1, hR2,
      hRP _ hw₁ hw₂]
  have hdet := lorentz.det_eq_one hA
  rw [hRA, hR, det_id_sub_smulRight, hφapp] at hdet
  field_simp at hdet
  linarith

/-- `|⟨v | (1, u)⟩| ≤ 2 ‖v‖` (sup norm of `ℝ × ℝᵈ`). -/
theorem abs_minkB_nullVec_right_le (v : Minkowski d) (u : PenroseSphere d) :
    |minkB v (nullVec u)| ≤ 2 * ‖v‖ := by
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have hi : |inner ℝ v.2 (u : EuclideanSpace ℝ (Fin d))| ≤ ‖v.2‖ := by
    have := abs_real_inner_le_norm v.2 (u : EuclideanSpace ℝ (Fin d))
    rwa [norm_penroseSphere, mul_one] at this
  rw [Real.norm_eq_abs] at h1
  simp only [minkB, nullVec, mul_one]
  calc |-v.1 + inner ℝ v.2 (u : EuclideanSpace ℝ (Fin d))|
      ≤ |-v.1| + |inner ℝ v.2 (u : EuclideanSpace ℝ (Fin d))| := abs_add_le _ _
    _ ≤ 2 * ‖v‖ := by rw [abs_neg]; linarith

/-- `‖(1, u)‖ = 1`. -/
theorem norm_nullVec (u : PenroseSphere d) : ‖nullVec u‖ = 1 := by
  simp [nullVec, Prod.norm_mk]

/-- **On `P^⊥ = n₁^⊥ ∩ n₂^⊥` the sup norm is dominated by `minkQ`**: `‖z‖² ≤ K² minkQ z`. From
`⟨z | n₁⟩ = ⟨z | n₂⟩ = 0`, `2 z₀ = ⟪z⃗, u₁ + u₂⟫` and `‖u₁ + u₂‖² = 4 − δ`, `δ = ‖u₁ − u₂‖² > 0`;
so `δ ‖z⃗‖² ≤ 4 minkQ z` and `|z₀| ≤ ‖z⃗‖`. -/
theorem sq_norm_le_minkQ_of_perp (hne : u₁ ≠ u₂) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ z : Minkowski d, minkB z (nullVec u₁) = 0 → minkB z (nullVec u₂) = 0 →
      ‖z‖ ^ 2 ≤ K ^ 2 * minkQ z := by
  set δ := ‖(u₁ : EuclideanSpace ℝ (Fin d)) - u₂‖ ^ 2 with hδ
  have hδpos : 0 < δ := by
    have : 0 < ‖(u₁ : EuclideanSpace ℝ (Fin d)) - u₂‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 fun e => hne (Subtype.ext e))
    positivity
  have hpar := parallelogram_law_with_norm ℝ (u₁ : EuclideanSpace ℝ (Fin d)) u₂
  rw [norm_penroseSphere, norm_penroseSphere] at hpar
  refine ⟨max 1 (4 / δ), le_max_left _ _, fun z h1 h2 => ?_⟩
  have e1 : z.1 = inner ℝ z.2 (u₁ : EuclideanSpace ℝ (Fin d)) := by
    simp only [minkB, nullVec, mul_one] at h1; linarith
  have e2 : z.1 = inner ℝ z.2 (u₂ : EuclideanSpace ℝ (Fin d)) := by
    simp only [minkB, nullVec, mul_one] at h2; linarith
  have e3 : 2 * z.1 = inner ℝ z.2 ((u₁ : EuclideanSpace ℝ (Fin d)) + u₂) := by
    rw [inner_add_right, ← e1, ← e2]; ring
  have hcs : (2 * z.1) ^ 2 ≤ ‖z.2‖ ^ 2 * ‖(u₁ : EuclideanSpace ℝ (Fin d)) + u₂‖ ^ 2 := by
    rw [e3, ← mul_pow]
    have := abs_real_inner_le_norm z.2 ((u₁ : EuclideanSpace ℝ (Fin d)) + u₂)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hsum : ‖(u₁ : EuclideanSpace ℝ (Fin d)) + u₂‖ ^ 2 = 4 - δ := by
    rw [hδ]; nlinarith [hpar]
  rw [hsum] at hcs
  have hz2 := sq_nonneg ‖z.2‖
  have hQ : δ * ‖z.2‖ ^ 2 ≤ 4 * minkQ z := by
    simp only [minkQ]; nlinarith
  have hQ0 : 0 ≤ minkQ z := by
    have : 0 ≤ δ * ‖z.2‖ ^ 2 := by positivity
    linarith
  have habs : |z.1| ≤ ‖z.2‖ := by
    refine (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [sq_abs]; nlinarith
  have hnorm : ‖z‖ = ‖z.2‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, max_eq_right habs]
  rw [hnorm]
  have hK : 4 / δ ≤ max 1 (4 / δ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ max 1 (4 / δ) := le_max_left _ _
    have h2 : 4 / δ ≤ max 1 (4 / δ) := le_max_right _ _
    nlinarith
  calc ‖z.2‖ ^ 2 ≤ 4 / δ * minkQ z := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]; linarith
    _ ≤ max 1 (4 / δ) ^ 2 * minkQ z := mul_le_mul_of_nonneg_right hK hQ0

/-- A Lorentz map fixing `u₁, u₂ ∈ 𝒮` preserves `P^⊥ = n₁^⊥ ∩ n₂^⊥`. -/
theorem minkB_apply_nullVec_eq_zero_of_fix {A : lorentz d} {u : PenroseSphere d}
    (hu : lorentzSphere A u = u) {w : Minkowski d} (hw : minkB w (nullVec u) = 0) :
    minkB ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) w) (nullVec u) = 0 := by
  have e := Lox.lox_apply_nullVec_of_fix hu
  have hc := (lorentzScale_pos A u).ne'
  have : nullVec u = (lorentzScale A u)⁻¹ • (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) := by
    rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this, minkB_smul_right, lorentz.minkB_apply A.2, hw, mul_zero]

/-- **Lorentz maps fixing `u₁, u₂` with bounded boost parameter are bounded in operator norm**:
for `|log c| ≤ R` (`c = lorentzScale A u₁`), `‖A‖ ≤ C(R)`. Decompose
`v = a n₁ + b n₂ + w`, `w ∈ P^⊥` (`eq_nullV_add`): `A v = a c n₁ + b c⁻¹ n₂ + A w` and
`‖A w‖ ≤ K ‖w‖` (`sq_norm_le_minkQ_of_perp`, `A` preserves `minkQ` and `P^⊥`). -/
theorem norm_linToCLM_le_of_fix_pair (hne : u₁ ≠ u₂) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : lorentz d, lorentzSphere A u₁ = u₁ → lorentzSphere A u₂ = u₂ →
      |Real.log (lorentzScale A u₁)| ≤ R →
        ‖linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)‖ ≤ C := by
  obtain ⟨K, hK1, hK⟩ := sq_norm_le_minkQ_of_perp hne
  set n₁ := nullVec u₁
  set n₂ := nullVec u₂
  set B := minkB n₁ n₂
  have hB : B ≠ 0 := minkB_nullVec_ne_zero_of_ne hne
  have hb : 0 < |B| := abs_pos.2 hB
  set C : ℝ := 4 * Real.exp R / |B| + K * (1 + 4 / |B|) with hCdef
  have hK0 : 0 ≤ K := by linarith
  refine ⟨C, by positivity, fun A h1 h2 hR => ?_⟩
  obtain ⟨e₁, e₂⟩ := pairScale_eigen hne h1 h2
  set c := lorentzScale A u₁
  have hc : 0 < c := lorentzScale_pos A u₁
  have hcR : c ≤ Real.exp R := by
    rw [← Real.exp_log hc]; exact Real.exp_le_exp.2 (le_of_abs_le hR)
  have hcR' : c⁻¹ ≤ Real.exp R := by
    rw [← Real.exp_log (inv_pos.2 hc), Real.log_inv]
    exact Real.exp_le_exp.2 (by have := (abs_le.1 hR).1; linarith)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [linToCLM_apply]
  set a := minkB v n₂ / B
  set b := minkB v n₁ / B
  set w := nullV n₁ n₂ v
  have hv : v = a • n₁ + b • n₂ + w := eq_nullV_add (u := n₁) (u' := n₂) v
  have hw₁ : minkB w n₁ = 0 := minkB_nullV_left (minkQ_nullVec u₁) hB v
  have hw₂ : minkB w n₂ = 0 := minkB_nullV_right (minkQ_nullVec u₂) hB v
  have ha : |a| ≤ 2 * ‖v‖ / |B| := by
    rw [abs_div]; exact div_le_div_of_nonneg_right (abs_minkB_nullVec_right_le v u₂) hb.le
  have hb' : |b| ≤ 2 * ‖v‖ / |B| := by
    rw [abs_div]; exact div_le_div_of_nonneg_right (abs_minkB_nullVec_right_le v u₁) hb.le
  have hwn : ‖w‖ ≤ ‖v‖ + |a| + |b| := by
    have : w = v - a • n₁ - b • n₂ := by rw [hv]; abel
    rw [this]
    calc ‖v - a • n₁ - b • n₂‖ ≤ ‖v - a • n₁‖ + ‖b • n₂‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + ‖a • n₁‖ + ‖b • n₂‖ := by linarith [norm_sub_le v (a • n₁)]
      _ = ‖v‖ + |a| + |b| := by
        rw [norm_smul, norm_smul, norm_nullVec, norm_nullVec, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_one, mul_one]
  have hAw₁ := minkB_apply_nullVec_eq_zero_of_fix h1 hw₁
  have hAw₂ := minkB_apply_nullVec_eq_zero_of_fix h2 hw₂
  have hAw : ‖(A : Minkowski d ≃ₗ[ℝ] Minkowski d) w‖ ≤ K * ‖w‖ := by
    have hq := hK _ hAw₁ hAw₂
    rw [lorentz.minkQ_apply A.2] at hq
    have hqw : minkQ w ≤ ‖w‖ ^ 2 := by
      have := norm_snd_le w
      simp only [minkQ]
      nlinarith [sq_nonneg w.1, norm_nonneg w.2]
    have : ‖(A : Minkowski d ≃ₗ[ℝ] Minkowski d) w‖ ^ 2 ≤ (K * ‖w‖) ^ 2 := by
      rw [mul_pow]
      exact hq.trans (mul_le_mul_of_nonneg_left hqw (sq_nonneg K))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have hAv : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v =
      (a * c) • n₁ + (b * c⁻¹) • n₂ + (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w := by
    conv_lhs => rw [hv]
    rw [map_add, map_add, map_smul, map_smul, e₁, e₂, smul_smul, smul_smul]
  rw [hAv]
  have hnv := norm_nonneg v
  calc ‖(a * c) • n₁ + (b * c⁻¹) • n₂ + (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w‖
      ≤ ‖(a * c) • n₁‖ + ‖(b * c⁻¹) • n₂‖ + ‖(A : Minkowski d ≃ₗ[ℝ] Minkowski d) w‖ :=
        norm_add₃_le
    _ = |a| * c + |b| * c⁻¹ + ‖(A : Minkowski d ≃ₗ[ℝ] Minkowski d) w‖ := by
        rw [norm_smul, norm_smul, norm_nullVec, norm_nullVec, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (inv_pos.2 hc), mul_one, mul_one]
    _ ≤ (2 * ‖v‖ / |B|) * Real.exp R + (2 * ‖v‖ / |B|) * Real.exp R + K * (‖v‖ + |a| + |b|) := by
        gcongr
        all_goals first
          | exact ha
          | exact hb'
          | exact hAw.trans (mul_le_mul_of_nonneg_left hwn hK0)
    _ ≤ (2 * ‖v‖ / |B|) * Real.exp R + (2 * ‖v‖ / |B|) * Real.exp R +
          K * (‖v‖ + 2 * ‖v‖ / |B| + 2 * ‖v‖ / |B|) := by gcongr
    _ = C * ‖v‖ := by rw [hCdef]; field_simp; ring

/-- **A norm-bounded (with inverses) subset of a discrete subgroup of `SO₀(1, d)` is finite**
(`lorentzTopology`, the operator-norm topology): `{1}` is open in `D`, so some ball
`‖A − 1‖ < ε` meets `D` in `{1}`; an infinite bounded `S` has two distinct `ε/C`-close
elements `A, A'` (total boundedness), and `A⁻¹A' ∈ D` is then `ε`-close to `1`. -/
theorem finite_of_discrete_of_norm_le {D : Subgroup (lorentz d)} (hD : DiscreteTopology D)
    {S : Set (lorentz d)} (hSD : S ⊆ D) {C : ℝ}
    (hC : ∀ A ∈ S, ‖linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)‖ ≤ C ∧
      ‖linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)‖ ≤ C) : S.Finite := by
  set f : lorentz d → (Minkowski d →L[ℝ] Minkowski d) :=
    fun A => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) with hf
  have hf1 : f 1 = 1 := linToCLM_one
  have hfmul : ∀ A B : lorentz d, f (A * B) = f A * f B := fun A B => linToCLM_mul _ _
  -- the ball of `1` meeting `D` in `{1}`
  have hopen : IsOpen ({1} : Set D) := @isOpen_discrete _ _ hD _
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.1 hopen
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 hU
  have h1U : (1 : lorentz d) ∈ U := by
    have : (1 : D) ∈ Subtype.val ⁻¹' U := by rw [hUeq]; rfl
    exact this
  have h1V : (1 : Minkowski d →L[ℝ] Minkowski d) ∈ V := by
    rw [← hVeq] at h1U
    have : f 1 ∈ V := h1U
    rwa [hf1] at this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV 1 h1V
  have key : ∀ A ∈ D, ‖f A - 1‖ < ε → A = 1 := by
    intro A hA hAε
    have hAV : f A ∈ V := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hAε)
    have hAU : A ∈ U := by rw [← hVeq]; exact hAV
    have : (⟨A, hA⟩ : D) ∈ ({1} : Set D) := by rw [← hUeq]; exact hAU
    exact congrArg Subtype.val this
  by_contra hinf
  set C' := max C 1
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hTb : TotallyBounded (f '' S) := by
    refine (isCompact_closedBall (0 : Minkowski d →L[ℝ] Minkowski d) C').totallyBounded.subset ?_
    rintro _ ⟨A, hA, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact (hC A hA).1.trans (le_max_left _ _)
  obtain ⟨t, htf, htcov⟩ := Metric.totallyBounded_iff.1 hTb (ε / (2 * C')) (by positivity)
  have hcen : ∀ A ∈ S, ∃ y ∈ t, dist (f A) y < ε / (2 * C') := fun A hA => by
    have := htcov ⟨A, hA, rfl⟩
    simp only [mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  classical
  set g : lorentz d → (Minkowski d →L[ℝ] Minkowski d) :=
    fun A => if h : A ∈ S then (hcen A h).choose else 0 with hg
  have hgS : ∀ A (h : A ∈ S), g A = (hcen A h).choose := fun A h => by simp [hg, h]
  have hmaps : MapsTo g S t := fun A hA => by rw [hgS A hA]; exact (hcen A hA).choose_spec.1
  obtain ⟨A, hA, A', hA', hne, hgg⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo hinf hmaps htf
  have hdA := (hcen A hA).choose_spec.2
  have hdA' := (hcen A' hA').choose_spec.2
  rw [← hgS A hA, hgg, hgS A' hA'] at hdA
  have hdist : ‖f A' - f A‖ < ε / C' := by
    rw [← dist_eq_norm]
    calc dist (f A') (f A) ≤ dist (f A') (hcen A' hA').choose + dist (f A) (hcen A' hA').choose :=
          dist_triangle_right _ _ _
      _ < ε / (2 * C') + ε / (2 * C') := add_lt_add hdA' hdA
      _ = ε / C' := by field_simp; ring
  have hinvA : f A⁻¹ * f A = 1 := by rw [← hfmul, inv_mul_cancel, hf1]
  have hmem : A⁻¹ * A' ∈ D := D.mul_mem (D.inv_mem (hSD hA)) (hSD hA')
  have hclose : ‖f (A⁻¹ * A') - 1‖ < ε := by
    rw [hfmul, ← hinvA, ← mul_sub]
    calc ‖f A⁻¹ * (f A' - f A)‖ ≤ ‖f A⁻¹‖ * ‖f A' - f A‖ := norm_mul_le _ _
      _ ≤ C' * ‖f A' - f A‖ := by
          gcongr; exact (hC A hA).2.trans (le_max_left _ _)
      _ < C' * (ε / C') := by gcongr
      _ = ε := by field_simp
  have := key _ hmem hclose
  exact hne (by rw [← mul_inv_cancel_left A A', this, mul_one])

/-- `lorentzScale 1 u = 1`. -/
theorem lorentzScale_one' (u : PenroseSphere d) : lorentzScale (1 : lorentz d) u = 1 := rfl

/-- The scale on a fixed point of `𝒮` inverts with the map. -/
theorem lorentzScale_inv_of_fix {A : lorentz d} {u : PenroseSphere d}
    (hA : lorentzSphere A u = u) : lorentzScale A⁻¹ u = (lorentzScale A u)⁻¹ := by
  have h := lorentzScale_mul_of_fix (A := A⁻¹) hA
  rw [inv_mul_cancel, lorentzScale_one'] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- The inverse of a map fixing `u ∈ 𝒮` fixes `u`. -/
theorem lorentzSphere_inv_of_fix {A : lorentz d} {u : PenroseSphere d}
    (hA : lorentzSphere A u = u) : lorentzSphere A⁻¹ u = u := by
  refine lorentzSphere_eq_of_eigen (c := (lorentzScale A u)⁻¹) ?_
  have e := Lox.lox_apply_nullVec_of_fix hA
  have hc := (lorentzScale_pos A u).ne'
  have : nullVec u = (lorentzScale A u)⁻¹ • (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) := by
    rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
  conv_lhs => rw [this]
  rw [map_smul]
  congr 1
  show (A⁻¹ : lorentz d).1 (A.1 (nullVec u)) = nullVec u
  rw [Subgroup.coe_inv]
  exact A.1.symm_apply_apply _

variable {Γ N : Subgroup (isom d)}

/-- **The boost parameters are discrete** (`L(Γ)` discrete): for each `R`, the linear parts of
the elements of `N` (which fix `u₁ ≠ u₂`) with `|log c| ≤ R` form a finite set
(`norm_linToCLM_le_of_fix_pair`, `finite_of_discrete_of_norm_le`). -/
theorem finite_linearPart_of_abs_log_le (hne : u₁ ≠ u₂)
    (hD : DiscreteTopology (linearImage Γ)) (hle : N ≤ Γ)
    (hfix : ∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂)
    (R : ℝ) :
    {A : lorentz d | ∃ γ ∈ N, linearPart γ = A ∧ |Real.log (lorentzScale A u₁)| ≤ R}.Finite := by
  obtain ⟨C, -, hC⟩ := norm_linToCLM_le_of_fix_pair hne R
  refine finite_of_discrete_of_norm_le (C := C) hD ?_ fun A hA => ?_
  · rintro _ ⟨γ, hγ, rfl, -⟩
    exact ⟨γ, hle hγ, rfl⟩
  · obtain ⟨γ, hγ, rfl, hR⟩ := hA
    obtain ⟨h1, h2⟩ := hfix γ hγ
    refine ⟨hC _ h1 h2 hR, hC _ (lorentzSphere_inv_of_fix h1) (lorentzSphere_inv_of_fix h2) ?_⟩
    rwa [lorentzScale_inv_of_fix h1, Real.log_inv, abs_neg]

/-- **A finite set of coset representatives**: for `N ≤ Γ` of finite index, every `γ ∈ Γ` is
`n r` with `n ∈ N` and `r` in a finite `R ⊆ Γ`. -/
theorem exists_finite_transversal_of_relIndex_ne_zero {G : Type*} [Group G] {Γ N : Subgroup G}
    (hidx : N.relIndex Γ ≠ 0) :
    ∃ R : Set G, R.Finite ∧ R ⊆ Γ ∧ ∀ γ ∈ Γ, ∃ n ∈ N, ∃ r ∈ R, γ = n * r := by
  haveI : (N.subgroupOf Γ).FiniteIndex := ⟨hidx⟩
  refine ⟨range fun q : Γ ⧸ N.subgroupOf Γ => ((q.out : Γ) : G)⁻¹, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact Γ.inv_mem (q.out : Γ).2
  intro γ hγ
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf Γ) (⟨γ, hγ⟩ : Γ)⁻¹
  refine ⟨((h : Γ) : G), Subgroup.mem_subgroupOf.1 h.2, _,
    ⟨(QuotientGroup.mk (⟨γ, hγ⟩ : Γ)⁻¹ : Γ ⧸ N.subgroupOf Γ), rfl⟩, ?_⟩
  have := congrArg (fun x : Γ => (x : G)) hh
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  dsimp only
  rw [this]; group

/-- **`N` is, up to finitely many cosets, generated by one boost and the pure translations**
(Barbot l.3285–3286: `L(Γ₀)` is finite for `Γ₀ = ker a`). If `N ≤ Γ` has finite index, fixes
`u₁ ≠ u₂ ∈ 𝒮`, `L(Γ)` is discrete, and some element of `N` has scale `c ≠ 1` on `n₁`, then the
logarithms of the scales form a cyclic subgroup `ℤ a₀` of `ℝ` (`AddSubgroup.dense_or_cyclic`; not
dense by `finite_linearPart_of_abs_log_le`), and with `γ₀` of scale `e^{a₀}`, every `γ ∈ Γ` is
`γ₀ᵏ τ g`, `τ ∈ Γ` with `L(τ) = 1`, `g` in a finite `T ⊆ Γ`. -/
theorem exists_pow_mul_translation_mul (hne : u₁ ≠ u₂)
    (hD : DiscreteTopology (linearImage Γ)) (hle : N ≤ Γ) (hidx : N.relIndex Γ ≠ 0)
    (hfix : ∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂)
    (hne1 : ∃ γ ∈ N, lorentzScale (linearPart γ) u₁ ≠ 1) :
    ∃ γ₀ ∈ N, lorentzScale (linearPart γ₀) u₁ ≠ 1 ∧ ∃ T : Set (isom d), T.Finite ∧ T ⊆ Γ ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, ∃ τ ∈ Γ, linearPart τ = 1 ∧ ∃ g ∈ T, γ = γ₀ ^ k * τ * g := by
  classical
  set sc : isom d → ℝ := fun γ => lorentzScale (linearPart γ) u₁ with hsc
  have hscpos : ∀ γ, 0 < sc γ := fun γ => lorentzScale_pos _ _
  have hscmul : ∀ γ ∈ N, ∀ δ ∈ N, sc (γ * δ) = sc γ * sc δ := fun γ _ δ hδ => by
    simp only [hsc, map_mul]; exact lorentzScale_mul_of_fix (hfix δ hδ).1
  have hscinv : ∀ γ ∈ N, sc γ⁻¹ = (sc γ)⁻¹ := fun γ hγ => by
    simp only [hsc, map_inv]; exact lorentzScale_inv_of_fix (hfix γ hγ).1
  -- the logarithm of the scale, a homomorphism on `N`
  set ψ : N →* Multiplicative ℝ :=
    { toFun := fun γ => Multiplicative.ofAdd (Real.log (sc γ))
      map_one' := by simp [hsc, lorentzScale_one']
      map_mul' := fun γ δ => by
        show Multiplicative.ofAdd (Real.log (sc ((γ : isom d) * δ))) = _
        rw [hscmul _ γ.2 _ δ.2, Real.log_mul (hscpos _).ne' (hscpos _).ne']
        rfl } with hψ
  have hψapp : ∀ γ : N, Multiplicative.toAdd (ψ γ) = Real.log (sc γ) := fun _ => rfl
  have hlogzpow : ∀ γ : N, ∀ k : ℤ, Real.log (sc ((γ : isom d) ^ k)) = k * Real.log (sc γ) :=
    fun γ k => by
      have := congrArg Multiplicative.toAdd (map_zpow ψ γ k)
      rw [toAdd_zpow, hψapp, hψapp, zsmul_eq_mul] at this
      simpa using this
  -- the subgroup of `ℝ` of logarithms
  obtain ⟨S, hmemS⟩ : ∃ S : AddSubgroup ℝ, ∀ r, r ∈ S ↔ ∃ γ ∈ N, Real.log (sc γ) = r := by
    refine ⟨{ carrier := {r | ∃ γ ∈ N, Real.log (sc γ) = r}
              zero_mem' := ⟨1, N.one_mem, by simp [hsc, lorentzScale_one']⟩
              add_mem' := ?_
              neg_mem' := ?_ }, fun _ => Iff.rfl⟩
    · rintro _ _ ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
      exact ⟨γ * δ, N.mul_mem hγ hδ, by
        rw [hscmul _ hγ _ hδ, Real.log_mul (hscpos _).ne' (hscpos _).ne']⟩
    · rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ⁻¹, N.inv_mem hγ, by rw [hscinv _ hγ, Real.log_inv]⟩
  -- `S ∩ [-1, 1]` is finite
  have hfin1 : {r | r ∈ S ∧ |r| ≤ 1}.Finite := by
    refine ((finite_linearPart_of_abs_log_le hne hD hle hfix 1).image
      fun A => Real.log (lorentzScale A u₁)).subset ?_
    rintro r ⟨hrS, hr⟩
    obtain ⟨γ, hγ, rfl⟩ := (hmemS r).1 hrS
    exact ⟨linearPart γ, ⟨γ, hγ, rfl, hr⟩, rfl⟩
  -- `S` is not dense, hence cyclic
  have hnd : ¬Dense (S : Set ℝ) := by
    intro hdense
    obtain ⟨r₀, hr₀S, hr₀⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 zero_lt_one)
    set F := {r | r ∈ S ∧ |r| ≤ 1} ∩ Ioo 0 1
    have hFf : F.Finite := hfin1.subset inter_subset_left
    have hr₀F : r₀ ∈ F := ⟨⟨hr₀S, by rw [abs_of_pos hr₀.1]; exact hr₀.2.le⟩, hr₀⟩
    obtain ⟨m, hmF, hmin⟩ := Set.exists_min_image F id hFf ⟨r₀, hr₀F⟩
    obtain ⟨r, hrS, hr⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hmF.2.1)
    have hrF : r ∈ F := ⟨⟨hrS, by rw [abs_of_pos hr.1]; linarith [hmF.2.2, hr.2]⟩,
      hr.1, by linarith [hmF.2.2, hr.2]⟩
    have := hmin r hrF
    simp only [id] at this
    linarith [hr.2]
  obtain ⟨a₀, ha₀⟩ := (AddSubgroup.dense_or_cyclic S).resolve_left hnd
  rw [← AddSubgroup.zmultiples_eq_closure] at ha₀
  have ha₀S : a₀ ∈ S := by rw [ha₀]; exact AddSubgroup.mem_zmultiples a₀
  obtain ⟨γ₀, hγ₀, ha₀γ⟩ := (hmemS a₀).1 ha₀S
  have hγ₀1 : sc γ₀ ≠ 1 := by
    intro h1
    obtain ⟨γ, hγ, hγ1⟩ := hne1
    have hmem : Real.log (sc γ) ∈ S := (hmemS _).2 ⟨γ, hγ, rfl⟩
    rw [ha₀, AddSubgroup.mem_zmultiples_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← ha₀γ, h1, Real.log_one, smul_zero] at hk
    have := Real.exp_log (hscpos γ)
    rw [← hk, Real.exp_zero] at this
    exact hγ1 this.symm
  -- the finitely many linear parts of scale `1`, with a representative in `N` for each
  obtain ⟨F₀, hF₀mem⟩ : ∃ F₀ : Set (lorentz d), ∀ A, A ∈ F₀ ↔
      ∃ γ ∈ N, linearPart γ = A ∧ |Real.log (lorentzScale A u₁)| ≤ 0 := ⟨_, fun _ => Iff.rfl⟩
  have hF₀ : F₀.Finite := (finite_linearPart_of_abs_log_le hne hD hle hfix 0).subset
    fun A hA => (hF₀mem A).1 hA
  have hδex : ∀ A ∈ F₀, ∃ δ, δ ∈ N ∧ linearPart δ = A := by
    intro A hA
    obtain ⟨γ, hγ, hA, -⟩ := (hF₀mem A).1 hA
    exact ⟨γ, hγ, hA⟩
  choose! δf hδf using hδex
  -- coset representatives of `N` in `Γ`
  obtain ⟨Rr, hRr, hRrΓ, hRrdec⟩ := exists_finite_transversal_of_relIndex_ne_zero hidx
  refine ⟨γ₀, hγ₀, hγ₀1, Set.image2 (fun A r => δf A * r) F₀ Rr, hF₀.image2 _ hRr, ?_, ?_⟩
  · rintro _ ⟨A, hA, r, hr, rfl⟩
    exact Γ.mul_mem (hle (hδf A hA).1) (hRrΓ hr)
  intro γ hγ
  obtain ⟨n, hnN, r, hr, rfl⟩ := hRrdec γ hγ
  -- `n = γ₀ᵏ ε`, `L(ε)` of scale `1`
  have hmem : Real.log (sc n) ∈ S := (hmemS _).2 ⟨n, hnN, rfl⟩
  rw [ha₀, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hγ₀k : γ₀ ^ (-k) ∈ N := N.zpow_mem hγ₀ _
  have hεN : γ₀ ^ (-k) * n ∈ N := N.mul_mem hγ₀k hnN
  have hεlog : Real.log (sc (γ₀ ^ (-k) * n)) = 0 := by
    rw [hscmul _ hγ₀k _ hnN, Real.log_mul (hscpos _).ne' (hscpos _).ne',
      hlogzpow ⟨γ₀, hγ₀⟩ (-k), ← hk, ha₀γ, zsmul_eq_mul]
    push_cast; ring
  have hεF₀ : linearPart (γ₀ ^ (-k) * n) ∈ F₀ :=
    (hF₀mem _).2 ⟨γ₀ ^ (-k) * n, hεN, rfl, le_of_eq (abs_eq_zero.2 hεlog)⟩
  obtain ⟨hδN, hδL⟩ := hδf _ hεF₀
  refine ⟨k, (γ₀ ^ (-k) * n) * (δf (linearPart (γ₀ ^ (-k) * n)))⁻¹,
    Γ.mul_mem (hle hεN) (Γ.inv_mem (hle hδN)), ?_,
    δf (linearPart (γ₀ ^ (-k) * n)) * r, ⟨_, hεF₀, r, hr, rfl⟩, ?_⟩
  · rw [map_mul (linearPart) (γ₀ ^ (-k) * n), map_inv, hδL, mul_inv_cancel]
  · group

end PairLin

end Causal.Flat.Cla
