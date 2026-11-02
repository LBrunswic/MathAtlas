import Causal.Flat.Develop
import Causal.Flat.Externals
import Causal.Flat.Bieberbach
import Causal.Flat.TwistedProduct
import Causal.Flat.Examples
import Causal.Flat.CauchyComplete

/-!
# `Causal.Flat.Nonlox.BTrivial` — [9.b] for a parabolic `γ₁ = R U`, `R ≠ id`

T. Barbot, *Globally hyperbolic flat space-times*, §9, "Triviality of `b`"
(`papers/barbot/legacy/labeled/GHFspace.tex:2765–2787`): if the linear parts of `Γ` fix the null
vector `v₀` and `Γ` contains a parabolic element `γ₁`, then every `γ ∈ Γ` preserves each null
hyperplane `{y = c}` (`b ≡ 0`). `Flat/Nonloxodromic`'s `b_trivial` proves this for a purely
unipotent `γ₁` (`R(γ₁) = id`); here `γ₁ = R U` is any parabolic element
(`nullY_smul_eq_of_isParabolic`), item (2) of the obstruction of `nonloxodromic_parabolic`.

Proof, in Barbot's coordinates `(x, z, y) ↦ ofNull x y z` (re-derived locally in
`BTrivialAux`, since `Flat/Nonloxodromic` is not imported): `γ₁` acts by
`(x, z, y) ↦ (x − ⟨v | R z⟩ − (y/2)|v|² + μ, R z + y v + u, y + b)`.

* Parabolic ⇒ `v ∉ Im (id − R)`: otherwise the linear part fixes a vector `(0, w, 1)`, and with
  `v₀` a timelike vector (`hpar_coord`).
* A conjugation by an element of `𝒜(v₀)` (Rem 9.2's frame change composed with a translation of
  `P̄₀`) moves `u, v` into `Fix R` (`E = Fix R + Im (id − R)`, `exists_fix`) and does not change
  `b`; then `v ≠ 0`.
* With `u, v ∈ Fix R`, `γ₁ᵖ` differs from the purely unipotent `(id, u, v, μ, b)ᵖ` only by
  `z ↦ Rᵖ z` on the `z`-coordinate, which costs a bounded error in `|γ₁ᵖ X − X'|²`
  (`nolQ_iterate_le`): the quartic of `b_eq_zero_model` (now with `v_f`) forces `b(γ₁) = 0`
  (`b_eq_zero_of_fix`), and the heights `y₀ ± k b(γ₀)` argument of `b_trivial_model` then forces
  `b(γ₀) = 0` for every `γ₀ ∈ Γ` (`false_of_b_ne_zero`). Neither Lemma 7.1 nor Cor 8.3 is used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Nonlox

open Set Function Submodule
open scoped RealInnerProductSpace

namespace BTrivialAux

/-! ## Barbot's coordinates (copied from `Flat/Nonloxodromic` §1) -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nol_leading_eq (u v : E) (y y' : ℝ) :
    ⟪u + y • v, u + y' • v⟫ = ‖u‖ ^ 2 + (y + y') * ⟪u, v⟫ + y * y' * ‖v‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, conj_trivial]
  rw [real_inner_comm v u]; ring

/-- `|x v₀ + z + y vₙ|² = 2xy + |z|²`. -/
noncomputable def nolQ (X : ℝ × E × ℝ) : ℝ := 2 * X.1 * X.2.2 + ‖X.2.1‖ ^ 2

/-- Its polar form. -/
noncomputable def nolB (X X' : ℝ × E × ℝ) : ℝ := X.1 * X'.2.2 + X'.1 * X.2.2 + ⟪X.2.1, X'.2.1⟫

theorem nolQ_add (X Y : ℝ × E × ℝ) : nolQ (X + Y) = nolQ X + 2 * nolB X Y + nolQ Y := by
  simp only [nolQ, nolB, Prod.fst_add, Prod.snd_add, @norm_add_sq_real]; ring

variable (E) in
/-- An element of `G(v₀)` in Barbot's coordinates `(R, u, v, μ, b)` (l.2694–2710). -/
@[ext] structure NolParam where
  R : E ≃ₗᵢ[ℝ] E
  u : E
  v : E
  μ : ℝ
  b : ℝ

namespace NolParam

/-- The action (l.2705–2709). -/
noncomputable def act (g : NolParam E) (X : ℝ × E × ℝ) : ℝ × E × ℝ :=
  (X.1 - ⟪g.v, g.R X.2.1⟫ - X.2.2 / 2 * ‖g.v‖ ^ 2 + g.μ, g.R X.2.1 + X.2.2 • g.v + g.u,
    X.2.2 + g.b)

/-- The composition law. -/
noncomputable def mul (g g' : NolParam E) : NolParam E where
  R := g'.R.trans g.R
  u := g.u + g.R g'.u + g'.b • g.v
  v := g.v + g.R g'.v
  μ := g.μ + g'.μ - ⟪g.v, g.R g'.u⟫ - g'.b / 2 * ‖g.v‖ ^ 2
  b := g.b + g'.b

theorem act_mul (g g' : NolParam E) (X : ℝ × E × ℝ) : (g.mul g').act X = g.act (g'.act X) := by
  obtain ⟨x, z, y⟩ := X
  simp only [act, mul, LinearIsometryEquiv.coe_trans, comp_apply, map_add, map_smul,
    Prod.mk.injEq]
  refine ⟨?_, by module, by ring⟩
  simp only [inner_add_left, inner_add_right, inner_smul_right, @norm_add_sq_real,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
  ring

theorem nolQ_act_sub (g : NolParam E) (X X' : ℝ × E × ℝ) :
    nolQ (g.act X - g.act X') = nolQ (X - X') := by
  obtain ⟨x, z, y⟩ := X
  obtain ⟨x', z', y'⟩ := X'
  simp only [nolQ, act, Prod.mk_sub_mk]
  have e : g.R z + y • g.v + g.u - (g.R z' + y' • g.v + g.u) = g.R (z - z') + (y - y') • g.v := by
    rw [map_sub, sub_smul]; abel
  rw [e, @norm_add_sq_real, LinearIsometryEquiv.norm_map, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inner_smul_right, map_sub, inner_sub_left, real_inner_comm g.v (g.R z),
    real_inner_comm g.v (g.R z')]
  ring

theorem act_proj₁ (g : NolParam E) (X : ℝ × E × ℝ) : (g.act X).2.2 = X.2.2 + g.b := rfl

/-- Purely unipotent elements: `R = id`. -/
def IsU (g : NolParam E) : Prop := g.R = LinearIsometryEquiv.refl ℝ E

/-- The kernel `𝒜(v₀)` of `b` on `𝒰(v₀)`. -/
def IsA (g : NolParam E) : Prop := g.IsU ∧ g.b = 0

/-- The `p`-th power of `g ∈ 𝒜(v₀)`. -/
noncomputable def powA (g : NolParam E) (p : ℕ) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, (p : ℝ) • g.u, (p : ℝ) • g.v,
    p * g.μ + p * (1 - p) / 2 * ⟪g.u, g.v⟫, 0⟩

theorem mul_powA {g : NolParam E} (hg : g.IsA) (p : ℕ) : g.mul (g.powA p) = g.powA (p + 1) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  ext x
  · simp [NolParam.mul, powA, hR]
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id, zero_smul, add_zero]
    push_cast; module
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, powA, hR, LinearIsometryEquiv.coe_refl, id, inner_smul_right,
      real_inner_comm g.u g.v]
    push_cast; ring
  · simp [NolParam.mul, powA, hg.2]

theorem iterate_act {g : NolParam E} (hg : g.IsA) (p : ℕ) (X : ℝ × E × ℝ) :
    g.act^[p] X = (g.powA p).act X := by
  induction p with
  | zero => simp [powA, act]
  | succ p ih => rw [iterate_succ_apply', ih, ← act_mul, mul_powA hg]

theorem powA_act (g : NolParam E) (p : ℕ) (X : ℝ × E × ℝ) :
    (g.powA p).act X = (X.1 + p * g.μ + p * (1 - p) / 2 * ⟪g.u, g.v⟫ - p * ⟪g.v, X.2.1⟫ -
      X.2.2 / 2 * p ^ 2 * ‖g.v‖ ^ 2, X.2.1 + (p : ℝ) • g.u + (X.2.2 * p) • g.v, X.2.2) := by
  simp only [act, powA, LinearIsometryEquiv.coe_refl, id, inner_smul_left, norm_smul,
    conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs, Prod.mk.injEq, add_zero, and_true]
  refine ⟨by ring, ?_⟩
  rw [smul_smul, mul_comm]; abel

theorem nolQ_powA_sub (g : NolParam E) (p : ℕ) (X X' : ℝ × E × ℝ) :
    nolQ ((g.powA p).act X - X') =
      (p : ℝ) ^ 2 * ⟪g.u + X.2.2 • g.v, g.u + X'.2.2 • g.v⟫ +
        p * (2 * (X.2.2 - X'.2.2) * (g.μ + ⟪g.u, g.v⟫ / 2 - ⟪g.v, X.2.1⟫) +
          2 * ⟪X.2.1 - X'.2.1, g.u + X.2.2 • g.v⟫) + nolQ (X - X') := by
  obtain ⟨x, z, y⟩ := X
  obtain ⟨x', z', y'⟩ := X'
  rw [powA_act]
  simp only [nolQ, Prod.mk_sub_mk]
  have e : z + (p : ℝ) • g.u + (y * p) • g.v - z' = (z - z') + (p : ℝ) • (g.u + y • g.v) := by
    rw [smul_add, smul_smul, mul_comm (p : ℝ) y]; abel
  rw [e, @norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right,
    ← real_inner_self_eq_norm_sq (g.u + y • g.v), nol_leading_eq, nol_leading_eq]
  ring

/-- The `p`-th power of a purely unipotent `g ∈ 𝒰(v₀)` (`b ≠ 0` allowed). -/
noncomputable def powU (g : NolParam E) (p : ℕ) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, (p : ℝ) • g.u + (g.b * p * (p - 1) / 2) • g.v, (p : ℝ) • g.v,
    p * g.μ - p * (p - 1) / 2 * ⟪g.u, g.v⟫ - g.b * ‖g.v‖ ^ 2 * ((p - 1) * p * (2 * p - 1) / 12),
    p * g.b⟩

theorem mul_powU {g : NolParam E} (hg : g.IsU) (p : ℕ) : g.mul (g.powU p) = g.powU (p + 1) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg
  ext x
  · simp [NolParam.mul, NolParam.powU, hR]
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id]
    push_cast; module
  · simp only [NolParam.mul, NolParam.powU, hR, LinearIsometryEquiv.coe_refl, id, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm g.u g.v]
    push_cast; ring
  · simp only [NolParam.mul, NolParam.powU]; push_cast; ring

theorem iterate_act_U {g : NolParam E} (hg : g.IsU) (p : ℕ) (X : ℝ × E × ℝ) :
    g.act^[p] X = (g.powU p).act X := by
  induction p with
  | zero => simp [NolParam.powU, act]
  | succ p ih => rw [iterate_succ_apply', ih, ← act_mul, mul_powU hg]

/-- The quartic: `|gᵖ X − X|² = p² (γ − b² |v|² p² / 12)` for `g ∈ 𝒰(v₀)`. -/
theorem nolQ_powU_sub (g : NolParam E) (p : ℕ) (X : ℝ × E × ℝ) :
    nolQ ((g.powU p).act X - X) = (p : ℝ) ^ 2 * ((2 * g.b * (g.μ - ⟪g.v, X.2.1⟫) -
      g.b * X.2.2 * ‖g.v‖ ^ 2 + ‖g.u + X.2.2 • g.v‖ ^ 2 + g.b ^ 2 * ‖g.v‖ ^ 2 / 12) -
        g.b ^ 2 * ‖g.v‖ ^ 2 * p ^ 2 / 12) := by
  obtain ⟨x, z, y⟩ := X
  simp only [nolQ, act, NolParam.powU, LinearIsometryEquiv.coe_refl, id, Prod.mk_sub_mk]
  have e : z + y • (p : ℝ) • g.v + ((p : ℝ) • g.u + (g.b * p * (p - 1) / 2) • g.v) - z =
      (p : ℝ) • (g.u + y • g.v) + (g.b * p * (p - 1) / 2) • g.v := by
    rw [smul_add, smul_smul, smul_smul, mul_comm y (p : ℝ)]; abel
  rw [e, @norm_add_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left, inner_smul_right,
    inner_add_left, real_inner_self_eq_norm_sq, conj_trivial]
  ring

/-- **The purely unipotent companion** `(id, u, v, μ, b)` of `g = (R, u, v, μ, b)`. -/
noncomputable def unip (g : NolParam E) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, g.u, g.v, g.μ, g.b⟩

theorem unip_isU (g : NolParam E) : g.unip.IsU := rfl

end NolParam

open NolParam

/-- A quadratic nonnegative at every natural number has nonnegative leading coefficient. -/
theorem leading_nonneg_of_forall_nat {A B C : ℝ} (h : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ 2 * A + p * B + C) :
    0 ≤ A := by
  by_contra hA
  push Not at hA
  obtain ⟨N, hN⟩ := exists_nat_gt ((|B| + |C|) / -A)
  have h1 := h (N + 1)
  push_cast at h1
  rw [div_lt_iff₀ (by linarith)] at hN
  have hB : (N + 1 : ℝ) * B ≤ (N + 1) * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) (by positivity)
  have hC : C ≤ (N + 1) * |C| := by
    nlinarith [le_abs_self C, abs_nonneg C, show (0 : ℝ) ≤ N from N.cast_nonneg]
  have hneg : (N + 1 : ℝ) * A + |B| + |C| < 0 := by nlinarith
  have : (N + 1 : ℝ) * ((N + 1) * A + |B| + |C|) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  nlinarith

/-- **A negative quartic eventually beats any constant.** -/
theorem quartic_contra {A m C : ℝ} (hm : 0 < m) (h : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ 2 * (A - m * p ^ 2) + C) :
    False := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((|A| + |C|) / m)
  have h1 := h (N + 1)
  push_cast at h1
  rw [div_lt_iff₀ hm] at hN
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  set P : ℝ := N + 1 with hP
  have hP1 : 1 ≤ P := by linarith
  have hPP : P ≤ P ^ 2 := by nlinarith
  have hmP : |A| + |C| < m * P ^ 2 := by nlinarith
  have hA : P ^ 2 * A ≤ P ^ 2 * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) (by positivity)
  have hC : C ≤ P ^ 2 * |C| := by nlinarith [le_abs_self C, abs_nonneg C]
  have hlt : P ^ 2 * (|A| + |C| - m * P ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem nol_iterate_mem {f : ℝ × E × ℝ → ℝ × E × ℝ} {St : Set (ℝ × E × ℝ)}
    (hinv : ∀ X ∈ St, f X ∈ St) (p : ℕ) {X : ℝ × E × ℝ} (hX : X ∈ St) : f^[p] X ∈ St := by
  induction p with
  | zero => exact hX
  | succ p ih => rw [iterate_succ_apply']; exact hinv _ ih

/-! ## The comparison with the purely unipotent companion -/

theorem inner_iterate_fix (R : E ≃ₗᵢ[ℝ] E) {f : E} (hf : R f = f) (n : ℕ) (z : E) :
    ⟪(⇑R)^[n] z, f⟫ = ⟪z, f⟫ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ← ih]
    calc ⟪R ((⇑R)^[n] z), f⟫ = ⟪R ((⇑R)^[n] z), R f⟫ := by rw [hf]
      _ = ⟪(⇑R)^[n] z, f⟫ := R.inner_map_map _ _

theorem norm_iterate (R : E ≃ₗᵢ[ℝ] E) (n : ℕ) (z : E) : ‖(⇑R)^[n] z‖ = ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', R.norm_map, ih]

/-- **`gᵖ` versus its purely unipotent companion** when `u, v ∈ Fix R`: they agree but on the
`z`-coordinate, where `z + φ` becomes `Rᵖ z + φ`, `φ ∈ Fix R`. -/
theorem iterate_act_comp (g : NolParam E) (hu : g.R g.u = g.u) (hv : g.R g.v = g.v) (n : ℕ)
    (X : ℝ × E × ℝ) : ∃ φ : E, g.R φ = φ ∧ (g.unip.act^[n] X).2.1 = X.2.1 + φ ∧
      g.act^[n] X = ((g.unip.act^[n] X).1, (⇑g.R)^[n] X.2.1 + φ, (g.unip.act^[n] X).2.2) := by
  induction n with
  | zero => exact ⟨0, map_zero _, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨φ, hφ, h2, h1⟩ := ih
    set W := g.unip.act^[n] X with hW
    refine ⟨φ + W.2.2 • g.v + g.u, by rw [map_add, map_add, map_smul, hφ, hv, hu], ?_, ?_⟩
    · rw [iterate_succ_apply', ← hW]
      simp only [act, unip, LinearIsometryEquiv.coe_refl, id, h2]
      abel
    · rw [iterate_succ_apply', iterate_succ_apply', ← hW, h1]
      simp only [act, unip, LinearIsometryEquiv.coe_refl, id, h2, Prod.mk.injEq, and_true]
      have hi : ⟪g.v, g.R ((⇑g.R)^[n] X.2.1 + φ)⟫ = ⟪g.v, X.2.1 + φ⟫ := by
        rw [map_add, hφ, inner_add_right, inner_add_right, ← iterate_succ_apply' (⇑g.R)]
        congr 1
        rw [real_inner_comm, inner_iterate_fix g.R hv, real_inner_comm]
      refine ⟨by rw [hi], ?_⟩
      rw [map_add, hφ, ← iterate_succ_apply' (⇑g.R)]
      abel

/-- **The bounded error**: `|gᵖ X − X'|² ≤ |gᵤᵖ X − X'|² + (|z| + |z'|)²`. -/
theorem nolQ_iterate_le (g : NolParam E) (hu : g.R g.u = g.u) (hv : g.R g.v = g.v) (n : ℕ)
    (X X' : ℝ × E × ℝ) :
    nolQ (g.act^[n] X - X') ≤ nolQ (g.unip.act^[n] X - X') + (‖X.2.1‖ + ‖X'.2.1‖) ^ 2 := by
  obtain ⟨φ, hφ, h2, h1⟩ := iterate_act_comp g hu hv n X
  set W := g.unip.act^[n] X
  have hW : W = (W.1, X.2.1 + φ, W.2.2) := by rw [← h2]
  rw [h1]
  conv_rhs => rw [hW]
  simp only [nolQ, Prod.fst_sub, Prod.snd_sub]
  have e1 : (⇑g.R)^[n] X.2.1 + φ - X'.2.1 = ((⇑g.R)^[n] X.2.1 - X'.2.1) + φ := by abel
  have e2 : X.2.1 + φ - X'.2.1 = (X.2.1 - X'.2.1) + φ := by abel
  rw [e1, e2, @norm_add_sq_real, @norm_add_sq_real, inner_sub_left, inner_sub_left,
    inner_iterate_fix g.R hφ]
  have h3 : ‖(⇑g.R)^[n] X.2.1 - X'.2.1‖ ^ 2 ≤ (‖X.2.1‖ + ‖X'.2.1‖) ^ 2 := by
    have := norm_sub_le ((⇑g.R)^[n] X.2.1) X'.2.1
    rw [norm_iterate] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [sq_nonneg ‖X.2.1 - X'.2.1‖]

/-! ## [9.b] in the model, for `u, v ∈ Fix R` -/

/-- **(i) `b(γ₁) = 0`**: the quartic of `b_eq_zero_model`, up to a bounded error. -/
theorem b_eq_zero_of_fix {St : Set (ℝ × E × ℝ)} (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X'))
    {X : ℝ × E × ℝ} (hX : X ∈ St) {g : NolParam E} (hu : g.R g.u = g.u) (hv : g.R g.v = g.v)
    (hv0 : g.v ≠ 0) (hinv : ∀ X ∈ St, g.act X ∈ St) : g.b = 0 := by
  by_contra hb
  have hm : 0 < g.b ^ 2 * ‖g.v‖ ^ 2 / 12 := by
    have := norm_pos_iff.2 hv0
    have : 0 < g.b ^ 2 := by positivity
    positivity
  refine quartic_contra hm (A := 2 * g.b * (g.μ - ⟪g.v, X.2.1⟫) - g.b * X.2.2 * ‖g.v‖ ^ 2 +
    ‖g.u + X.2.2 • g.v‖ ^ 2 + g.b ^ 2 * ‖g.v‖ ^ 2 / 12) (C := (‖X.2.1‖ + ‖X.2.1‖) ^ 2)
    fun p => ?_
  have h0 := hach _ (nol_iterate_mem hinv p hX) X hX
  have h1 := nolQ_iterate_le g hu hv p X X
  rw [iterate_act_U g.unip_isU, nolQ_powU_sub] at h1
  have e : g.unip.b ^ 2 * ‖g.unip.v‖ ^ 2 * (p : ℝ) ^ 2 / 12 =
      g.b ^ 2 * ‖g.v‖ ^ 2 / 12 * p ^ 2 := by simp only [unip]; ring
  rw [e] at h1
  simp only [unip] at h1
  linarith

/-- **The leading coefficient**, for `u, v ∈ Fix R` and `b = 0`. -/
theorem leading_nonneg_of_fix {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {g : NolParam E} (hu : g.R g.u = g.u)
    (hv : g.R g.v = g.v) (hb : g.b = 0) (hinv : ∀ X ∈ St, g.act X ∈ St) {X X' : ℝ × E × ℝ}
    (hX : X ∈ St) (hX' : X' ∈ St) : 0 ≤ ⟪g.u + X.2.2 • g.v, g.u + X'.2.2 • g.v⟫ := by
  have hA : g.unip.IsA := ⟨rfl, hb⟩
  refine leading_nonneg_of_forall_nat (B := 2 * (X.2.2 - X'.2.2) *
    (g.μ + ⟪g.u, g.v⟫ / 2 - ⟪g.v, X.2.1⟫) + 2 * ⟪X.2.1 - X'.2.1, g.u + X.2.2 • g.v⟫)
    (C := nolQ (X - X') + (‖X.2.1‖ + ‖X'.2.1‖) ^ 2) fun p => ?_
  have h0 := hach _ (nol_iterate_mem hinv p hX) X' hX'
  have h1 := nolQ_iterate_le g hu hv p X X'
  rw [iterate_act hA, nolQ_powA_sub] at h1
  simp only [unip] at h1
  linarith

/-- **(ii) `b ≡ 0`**: heights `y₀ ± k b(γ₀)` (the argument of `b_trivial_model`). -/
theorem false_of_b_ne_zero {St : Set (ℝ × E × ℝ)} (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X'))
    (hne : St.Nonempty) {g₁ : NolParam E} (hu : g₁.R g₁.u = g₁.u) (hv : g₁.R g₁.v = g₁.v)
    (hv0 : g₁.v ≠ 0) (hb₁ : g₁.b = 0) (hinv₁ : ∀ X ∈ St, g₁.act X ∈ St) {g₀ g₀' : NolParam E}
    (hb : g₀.b ≠ 0) (hb' : g₀'.b = -g₀.b) (hinv₀ : ∀ X ∈ St, g₀.act X ∈ St)
    (hinv₀' : ∀ X ∈ St, g₀'.act X ∈ St) : False := by
  obtain ⟨X₀, hX₀⟩ := hne
  have hh : ∀ (g : NolParam E) (k : ℕ) (X : ℝ × E × ℝ), (g.act^[k] X).2.2 = X.2.2 + k * g.b := by
    intro g k X
    induction k with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', act_proj₁, ih]; push_cast; ring
  have hv2 : 0 < ‖g₁.v‖ ^ 2 := by have := norm_pos_iff.2 hv0; positivity
  have hb2 : 0 < g₀.b ^ 2 := by positivity
  set y₀ := X₀.2.2
  set K := ‖g₁.u‖ ^ 2 + 2 * y₀ * ⟪g₁.u, g₁.v⟫ + y₀ ^ 2 * ‖g₁.v‖ ^ 2
  obtain ⟨k, hk⟩ := exists_nat_gt (K / (g₀.b ^ 2 * ‖g₁.v‖ ^ 2))
  have hk1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
  have := leading_nonneg_of_fix hach hu hv hb₁ hinv₁ (nol_iterate_mem hinv₀ k hX₀)
    (nol_iterate_mem hinv₀' k hX₀)
  rw [hh, hh, hb', nol_leading_eq] at this
  rw [div_lt_iff₀ (by positivity)] at hk
  have e : ‖g₁.u‖ ^ 2 + (y₀ + k * g₀.b + (y₀ + k * -g₀.b)) * ⟪g₁.u, g₁.v⟫ +
      (y₀ + k * g₀.b) * (y₀ + k * -g₀.b) * ‖g₁.v‖ ^ 2 = K - k ^ 2 * (g₀.b ^ 2 * ‖g₁.v‖ ^ 2) := by
    simp only [K]; ring
  rw [e] at this
  nlinarith [mul_pos hb2 hv2]

/-! ## Moving `u, v` into `Fix R` by a conjugation in `𝒜(v₀)` -/

/-- **`E = Fix R + Im (id − R)`** for a linear isometry `R` of a finite-dimensional `E`: every
`e` has a translate `e + (c − R c)` fixed by `R` (`Im (id − R)^⊥ ⊆ Fix R`). -/
theorem exists_fix [FiniteDimensional ℝ E] (R : E ≃ₗᵢ[ℝ] E) (e : E) :
    ∃ c : E, R (e + (c - R c)) = e + (c - R c) := by
  set K : Submodule ℝ E :=
    LinearMap.range ((LinearMap.id : E →ₗ[ℝ] E) - R.toLinearEquiv.toLinearMap)
  obtain ⟨y, hy, w, hw, rfl⟩ := K.exists_add_mem_mem_orthogonal e
  obtain ⟨c, rfl⟩ := hy
  have hw' : ∀ c' : E, ⟪c' - R c', w⟫ = 0 := fun c' =>
    (Submodule.mem_orthogonal K w).1 hw _ ⟨c', by simp⟩
  refine ⟨-c, ?_⟩
  have e1 : ((LinearMap.id : E →ₗ[ℝ] E) - R.toLinearEquiv.toLinearMap) c + w + (-c - R (-c)) =
      w := by simp; abel
  rw [e1]
  have h1 := hw' w
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖R w - w‖ ^ 2 = 0 := by
    rw [@norm_sub_sq_real, R.norm_map]; linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2))

/-- **[9.b] in the model, for any parabolic `g₁`** (`v(g₁) ∉ Im (id − R)`): conjugating by
`h = (id, s, c, 0, 0) ∈ 𝒜(v₀)` moves `u(g₁)`, `v(g₁)` into `Fix R` without changing any `b`;
then `b(g₁) = 0` (`b_eq_zero_of_fix`) and every `g₀` preserving `St` with an element of
opposite `b` has `b(g₀) = 0` (`false_of_b_ne_zero`). -/
theorem b_eq_zero_of_parabolic [FiniteDimensional ℝ E] {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) (hne : St.Nonempty) {g₁ : NolParam E}
    (hpar : ∀ c : E, g₁.v + (c - g₁.R c) ≠ 0) (hinv₁ : ∀ X ∈ St, g₁.act X ∈ St)
    {g₀ g₀' : NolParam E} (hb' : g₀'.b = -g₀.b) (hinv₀ : ∀ X ∈ St, g₀.act X ∈ St)
    (hinv₀' : ∀ X ∈ St, g₀'.act X ∈ St) : g₀.b = 0 := by
  obtain ⟨c, hc⟩ := exists_fix g₁.R g₁.v
  obtain ⟨s, hs⟩ := exists_fix g₁.R (g₁.u + g₁.b • c)
  set h : NolParam E := ⟨LinearIsometryEquiv.refl ℝ E, s, c, 0, 0⟩ with h_def
  set hi : NolParam E := ⟨LinearIsometryEquiv.refl ℝ E, -s, -c, -⟪c, s⟫, 0⟩ with hi_def
  have hih : ∀ X, hi.act (h.act X) = X := by
    rintro ⟨x, z, y⟩
    simp only [act, h_def, hi_def, LinearIsometryEquiv.coe_refl, id, Prod.mk.injEq]
    refine ⟨?_, by module, by ring⟩
    simp only [inner_add_right, inner_smul_right, inner_neg_left, norm_neg,
      real_inner_self_eq_norm_sq]
    ring
  set St' : Set (ℝ × E × ℝ) := {X | hi.act X ∈ St} with St'_def
  have hach' : ∀ X ∈ St', ∀ X' ∈ St', 0 ≤ nolQ (X - X') := fun X hX X' hX' => by
    rw [← nolQ_act_sub hi]; exact hach _ hX _ hX'
  have hconj : ∀ g : NolParam E, (∀ X ∈ St, g.act X ∈ St) →
      ∀ X ∈ St', (h.mul (g.mul hi)).act X ∈ St' := by
    intro g hg X hX
    show hi.act _ ∈ St
    rw [act_mul, act_mul, hih]; exact hg _ hX
  have hbc : ∀ g : NolParam E, (h.mul (g.mul hi)).b = g.b := fun g => by
    simp [NolParam.mul, h_def, hi_def]
  have hR : ∀ x, (h.mul (g₁.mul hi)).R x = g₁.R x := fun x => by simp [NolParam.mul, h_def, hi_def]
  have hv : (h.mul (g₁.mul hi)).v = g₁.v + (c - g₁.R c) := by
    simp [NolParam.mul, h_def, hi_def]; abel
  have hu : (h.mul (g₁.mul hi)).u = g₁.u + g₁.b • c + (s - g₁.R s) := by
    simp [NolParam.mul, h_def, hi_def]; abel
  have hu' : (h.mul (g₁.mul hi)).R (h.mul (g₁.mul hi)).u = (h.mul (g₁.mul hi)).u := by
    rw [hR, hu]; exact hs
  have hv' : (h.mul (g₁.mul hi)).R (h.mul (g₁.mul hi)).v = (h.mul (g₁.mul hi)).v := by
    rw [hR, hv]; exact hc
  have hv0 : (h.mul (g₁.mul hi)).v ≠ 0 := by rw [hv]; exact hpar c
  obtain ⟨X₀, hX₀⟩ := hne
  have hX₀' : h.act X₀ ∈ St' := by show hi.act _ ∈ St; rw [hih]; exact hX₀
  have hb₁ : (h.mul (g₁.mul hi)).b = 0 :=
    b_eq_zero_of_fix hach' hX₀' hu' hv' hv0 (hconj g₁ hinv₁)
  by_contra hb
  exact false_of_b_ne_zero hach' ⟨_, hX₀'⟩ hu' hv' hv0 hb₁ (hconj g₁ hinv₁)
    (by rw [hbc]; exact hb) (by rw [hbc, hbc, hb']) (hconj g₀ hinv₀) (hconj g₀' hinv₀')

end Model

/-! ## Barbot's coordinates in `𝐌ⁿ` (copied from `Flat/Nonloxodromic` §3) -/

section Minkowski

open NolParam

variable {d : ℕ}

/-- **Barbot's coordinates in `𝐌ⁿ`, `n = d + 2`**, through `Flat/Examples`' null coordinates:
`(x, z, y) ↦ ofNull x y z`, so `v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0` (null, `⟨v₀ | vₙ⟩ = 1`)
and `P̄₀ = {x = y = 0} ≅ ℝᵈ`. -/
noncomputable def nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) : Minkowski (d + 1) :=
  ofNull X.1 X.2.2 X.2.1

/-- The inverse chart. -/
noncomputable def minkToNol (p : Minkowski (d + 1)) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ :=
  (nullX p, nullZ p, nullY p)

theorem minkToNol_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    minkToNol (nolToMink X) = X := by
  simp [minkToNol, nolToMink, nullX_ofNull, nullY_ofNull, nullZ_ofNull]

theorem minkQ_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    minkQ (nolToMink X) = nolQ X := by
  rw [minkQ_eq_null, nolToMink, nullX_ofNull, nullY_ofNull, nullZ_ofNull, nolQ]

theorem nolToMink_sub (X X' : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    nolToMink (X - X') = nolToMink X - nolToMink X' := by
  refine Prod.ext ?_ ?_
  · simp only [nolToMink, ofNull, Prod.fst_sub, Prod.snd_sub]; ring
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nolToMink, ofNull]; ring
    · simp [nolToMink, ofNull]

theorem nolToMink_minkToNol (p : Minkowski (d + 1)) : nolToMink (minkToNol p) = p := by
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · simp only [nolToMink, minkToNol, ofNull, nullX, nullY]
    field_simp
    linear_combination (-p.1) * h
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [nolToMink, minkToNol, ofNull, nullX, nullY]
      simp only [Fin.cons_zero]
      field_simp
      linear_combination (-p.2 0) * h
    · simp [nolToMink, minkToNol, ofNull, nullZ]

/-! ### `Stab(v₀)` in Barbot's coordinates (l.2701–2713), and [9.b] in `𝐌ⁿ` -/

/-- `nolToMink` is linear. -/
noncomputable def nolToMinkₗ : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] Minkowski (d + 1) where
  toFun := nolToMink
  map_add' X X' := by
    have h := nolToMink_sub (X + X') X'
    rw [add_sub_cancel_right] at h
    rw [h, sub_add_cancel]
  map_smul' c X := by
    refine Prod.ext ?_ ?_
    · simp only [nolToMink, ofNull, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
      ring
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [nolToMink, ofNull]; ring
      · simp [nolToMink, ofNull]

/-- `minkToNol` is linear. -/
noncomputable def minkToNolₗ : Minkowski (d + 1) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) where
  toFun := minkToNol
  map_add' p q := by
    simp only [minkToNol, nullX, nullY, nullZ, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk,
      Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp; ring
    · ext i; simp
    · simp; ring
  map_smul' c p := by
    simp only [minkToNol, nullX, nullY, nullZ, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
      smul_eq_mul, RingHom.id_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simp; ring
    · ext i; simp
    · simp; ring

theorem nolQ_minkToNol (p : Minkowski (d + 1)) : nolQ (minkToNol p) = minkQ p := by
  rw [← minkQ_nolToMink, nolToMink_minkToNol]

/-- **The structure of `Stab(v₀)`** (l.2701–2713): an isometry whose linear part fixes
`v₀ = ofNull 1 0 0` acts, in Barbot's coordinates, as an element of `G(v₀)` (`NolParam`). -/
theorem exists_nolParam {γ : isom (d + 1)}
    (hfix : linOf γ (nolToMink (1, 0, 0)) = nolToMink (1, 0, 0)) :
    ∃ g : NolParam (EuclideanSpace ℝ (Fin d)), ∀ X, γ • nolToMink X = nolToMink (g.act X) := by
  set Λ : (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :=
    minkToNolₗ ∘ₗ (linOf γ : Minkowski (d + 1) →ₗ[ℝ] Minkowski (d + 1)) ∘ₗ nolToMinkₗ
  have hΛ : ∀ X, Λ X = minkToNol (linOf γ (nolToMink X)) := fun _ => rfl
  have hQ : ∀ X, nolQ (Λ X) = nolQ X := fun X => by
    rw [hΛ, nolQ_minkToNol, lorentz.minkQ_apply (linOf_mem γ), minkQ_nolToMink]
  have hB : ∀ X Y, nolB (Λ X) (Λ Y) = nolB X Y := fun X Y => by
    have h1 := hQ (X + Y)
    rw [map_add, nolQ_add, nolQ_add, hQ, hQ] at h1
    linarith
  have h100 : Λ (1, 0, 0) = (1, 0, 0) := by
    rw [hΛ, hfix, minkToNol_nolToMink]
  set c := Λ (0, 0, 1) with hc
  have hc3 : c.2.2 = 1 := by
    have := hB (0, 0, 1) (1, 0, 0)
    rw [h100] at this
    simpa [nolB] using this
  have hc1 : c.1 = -(‖c.2.1‖ ^ 2 / 2) := by
    have := hQ (0, 0, 1)
    rw [← hc] at this
    simp only [nolQ, hc3] at this
    simp at this
    linarith
  -- the `z`-part
  set R₀ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) ℝ ∘ₗ
      LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin d) × ℝ)) ∘ₗ Λ ∘ₗ
      LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin d) × ℝ) ∘ₗ
      LinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ
  have hR₀ : ∀ z, R₀ z = (Λ (0, z, 0)).2.1 := fun _ => rfl
  have hβ : ∀ z, (Λ (0, z, 0)).2.2 = 0 := fun z => by
    have := hB (0, z, 0) (1, 0, 0)
    rw [h100] at this
    simpa [nolB] using this
  have hnorm : ∀ z, ‖R₀ z‖ = ‖z‖ := fun z => by
    have := hQ (0, z, 0)
    simp only [nolQ, hβ, mul_zero, zero_add] at this
    rw [hR₀]
    have h2 : ‖(Λ (0, z, 0)).2.1‖ ^ 2 = ‖z‖ ^ 2 := by simpa using this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have ha : ∀ z, (Λ (0, z, 0)).1 = -⟪c.2.1, R₀ z⟫ := fun z => by
    have := hB (0, z, 0) (0, 0, 1)
    rw [← hc] at this
    simp only [nolB, hβ, hc3, mul_one, mul_zero, add_zero] at this
    simp at this
    rw [hR₀, real_inner_comm]
    linarith
  set R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearIsometry.toLinearIsometryEquiv ⟨R₀, hnorm⟩ rfl
  have hR : ∀ z, R z = R₀ z := fun _ => rfl
  refine ⟨⟨R, (minkToNol (trOf γ)).2.1, c.2.1, (minkToNol (trOf γ)).1,
    (minkToNol (trOf γ)).2.2⟩, fun X => ?_⟩
  obtain ⟨x, z, y⟩ := X
  have hdec : ((x, z, y) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) =
      x • (1, 0, 0) + (0, z, 0) + y • (0, 0, 1) := by
    simp
  have hΛX : Λ (x, z, y) = (x - ⟪c.2.1, R z⟫ - y / 2 * ‖c.2.1‖ ^ 2, R z + y • c.2.1, y) := by
    rw [hdec, map_add, map_add, map_smul, map_smul, h100, ← hc]
    obtain ⟨c₁, cv, c₃⟩ := c
    simp only at hc1 hc3
    have e1 := ha z
    have e2 := hβ z
    have e3 := hR₀ z
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, e1, hc1, hR]; ring
    · simp [← e3, hR]
    · simp only [Prod.snd_add, Prod.smul_snd, e2, hc3, smul_eq_mul]; simp
  rw [smul_eq_lin_add, ← nolToMink_minkToNol (linOf γ (nolToMink _) + trOf γ)]
  congr 1
  change minkToNolₗ (linOf γ (nolToMink (x, z, y)) + trOf γ) = _
  rw [map_add]
  change Λ (x, z, y) + minkToNol (trOf γ) = _
  rw [hΛX]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [NolParam.act, Prod.fst_add]
  · simp only [NolParam.act, Prod.snd_add, Prod.fst_add]
  · simp only [NolParam.act, Prod.snd_add]

/-- **Acausal sets are achronal in Barbot's coordinates**: `0 ≤ |X − X'|²` on the preimage. -/
theorem nolQ_nonneg_of_isAcausal {St : Set (Minkowski (d + 1))}
    (hac : (minkowski (d + 1)).IsAcausal St) {X X' : ℝ × EuclideanSpace ℝ (Fin d) × ℝ}
    (hX : nolToMink X ∈ St) (hX' : nolToMink X' ∈ St) : 0 ≤ nolQ (X - X') := by
  by_contra hneg
  push Not at hneg
  rw [← minkQ_nolToMink, nolToMink_sub] at hneg
  rcases isFutureTimelike_or_neg hneg with h | h
  · have hle : (minkowski (d + 1)).le ⊤ (nolToMink X') (nolToMink X) :=
      le_top_iff_minkQ.2 ⟨h.1.le, h.2.le⟩
    have := hac _ hX' _ hX hle
    rw [this, sub_self, minkQ_zero] at hneg; exact lt_irrefl _ hneg
  · rw [neg_sub] at h
    have hle : (minkowski (d + 1)).le ⊤ (nolToMink X) (nolToMink X') :=
      le_top_iff_minkQ.2 ⟨h.1.le, h.2.le⟩
    have := hac _ hX _ hX' hle
    rw [this, sub_self, minkQ_zero] at hneg; exact lt_irrefl _ hneg

/-- **Prop 9.3** (`bprop:limites`, l.2940–2989) for `S̃ ⊆ 𝐌ⁿ`, in Barbot's coordinates
(`v₀ = ofNull 1 0 0`, `vₙ = ofNull 0 1 0`): `S̃` acausal and preserved by `Γ`, whose elements
`u ∈ L` act through `𝒜(v₀)` with `v = T u`; `π₁(S̃) = nullY(S̃) ⊇ ]ylo, yhi[`, `ylo < 0 < yhi`;
some element parabolic. Then at least one extremity is finite and the inequalities hold on
`E = span L`. -/
theorem nullY_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) : nullY (nolToMink X) = X.2.2 :=
  nullY_ofNull _ _ _


theorem nolToMink_add (X Y : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    nolToMink (X + Y) = nolToMink X + nolToMink Y :=
  map_add (nolToMinkₗ (d := d)) X Y

theorem minkB_nolToMink (X Y : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    minkB (nolToMink X) (nolToMink Y) = nolB X Y := by
  have h := minkQ_add (nolToMink X) (nolToMink Y)
  rw [← nolToMink_add, minkQ_nolToMink, minkQ_nolToMink, minkQ_nolToMink, nolQ_add] at h
  linarith

/-- The linear part in Barbot's coordinates: `L(γ) X = g X − g 0`. -/
theorem linOf_nolToMink {γ : isom (d + 1)} {g : NolParam (EuclideanSpace ℝ (Fin d))}
    (hg : ∀ X, γ • nolToMink X = nolToMink (g.act X)) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    linOf γ (nolToMink X) = nolToMink (g.act X - g.act 0) := by
  have h0 : nolToMink (d := d) 0 = 0 := by
    have := nolToMink_sub (d := d) 0 0
    simpa using this
  have ht : trOf γ = nolToMink (g.act 0) := by
    have := hg 0
    rw [h0, smul_eq_lin_add, map_zero, zero_add] at this
    exact this
  rw [nolToMink_sub, ← hg, ← ht, smul_eq_lin_add, add_sub_cancel_right]

/-- **Parabolic ⇒ `v ∉ Im (id − R)`** (no fixed point of `λ(γ₁)` on the slices): otherwise the
linear part fixes `(0, −c, 1)` (where `v = R c − c`) besides `v₀`, so a timelike vector. -/
theorem hpar_coord {γ : isom (d + 1)} (hpar : IsParabolic (linOf γ))
    (hfix : linOf γ (nolToMink (1, 0, 0)) = nolToMink (1, 0, 0))
    {g : NolParam (EuclideanSpace ℝ (Fin d))} (hg : ∀ X, γ • nolToMink X = nolToMink (g.act X))
    (c : EuclideanSpace ℝ (Fin d)) : g.v + (c - g.R c) ≠ 0 := by
  intro h0
  have hv : g.v = g.R c - c := by rw [eq_neg_of_add_eq_zero_left h0, neg_sub]
  set W : ℝ × EuclideanSpace ℝ (Fin d) × ℝ := (0, -c, 1) with hW_def
  have hW : linOf γ (nolToMink W) = nolToMink W := by
    rw [linOf_nolToMink hg]
    congr 1
    simp only [hW_def, NolParam.act, Prod.fst_zero, Prod.snd_zero, map_zero, inner_zero_right,
      zero_div, zero_mul, zero_smul, Prod.mk_sub_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, by ring⟩
    · rw [hv, map_neg, inner_neg_right, inner_sub_left, @norm_sub_sq_real,
        LinearIsometryEquiv.norm_map, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
        real_inner_comm c (g.R c)]
      ring
    · rw [hv, map_neg]; module
  have hq : minkQ (nolToMink (d := d) (1, 0, 0)) = 0 := by
    rw [minkQ_nolToMink]; simp [nolQ]
  have := minkB_eq_zero_of_fixed_of_not_isElliptic (linOf_mem γ) hpar.not_isElliptic hq hfix hW
  rw [minkB_nolToMink] at this
  simp [nolB, hW_def] at this

end Minkowski

end BTrivialAux

open BTrivialAux in
/-- **[9.b] for a parabolic `γ₁ = R U`, `R ≠ id`** (`GHFspace.tex:2765–2787`, "Triviality of
`b`"): if the linear parts of `Γ` fix `v₀ = ofNull 1 0 0`, `Γ` preserves a nonempty acausal `S̃`
and contains an element `γ₁` with parabolic linear part, then every `γ ∈ Γ` preserves each null
hyperplane `{y = c}`: `b ≡ 0`. Generalises `Flat/Nonloxodromic`'s `b_trivial` (purely unipotent
`γ₁`); serves item (2) of `nonloxodromic_parabolic` ([9.P]). -/
theorem nullY_smul_eq_of_isParabolic {d : ℕ} {Γ : Subgroup (isom (d + 1))}
    {St : Set (Minkowski (d + 1))} (hac : (minkowski (d + 1)).IsAcausal St) (hne : St.Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ St, γ • p ∈ St)
    (hfix : ∀ γ ∈ Γ, linOf γ (ofNull 1 0 0) = ofNull 1 0 0)
    {γ₁ : isom (d + 1)} (hγ₁ : γ₁ ∈ Γ) (hpar : IsParabolic (linOf γ₁)) :
    ∀ γ ∈ Γ, ∀ p : Minkowski (d + 1), nullY (γ • p) = nullY p := by
  set St' := nolToMink ⁻¹' St
  have hach : ∀ X ∈ St', ∀ X' ∈ St', 0 ≤ nolQ (X - X') := fun X hX X' hX' =>
    nolQ_nonneg_of_isAcausal hac hX hX'
  obtain ⟨p₀, hp₀⟩ := hne
  have hX₀ : minkToNol p₀ ∈ St' := by
    show nolToMink _ ∈ St; rw [nolToMink_minkToNol]; exact hp₀
  have hinv' : ∀ {γ : isom (d + 1)} {g : NolParam (EuclideanSpace ℝ (Fin d))}, γ ∈ Γ →
      (∀ X, γ • nolToMink (d := d) X = nolToMink (g.act X)) → ∀ X ∈ St', g.act X ∈ St' := by
    intro γ g hγ hg X hX
    show nolToMink _ ∈ St
    rw [← hg]; exact hinv γ hγ _ hX
  obtain ⟨g₁, hg₁⟩ := exists_nolParam (hfix γ₁ hγ₁)
  have hpar' := hpar_coord hpar (hfix γ₁ hγ₁) hg₁
  intro γ hγ p
  obtain ⟨g, hg⟩ := exists_nolParam (hfix γ hγ)
  obtain ⟨g', hg'⟩ := exists_nolParam (hfix γ⁻¹ (Γ.inv_mem hγ))
  have hbb : g'.b = -g.b := by
    have h1 : g'.act (g.act (minkToNol p₀)) = minkToNol p₀ := by
      have := congrArg minkToNol (hg' (g.act (minkToNol p₀)))
      rw [minkToNol_nolToMink, ← hg, ← mul_smul, inv_mul_cancel, one_smul,
        nolToMink_minkToNol] at this
      exact this.symm
    have h2 := congrArg (fun X => X.2.2) h1
    simp only [NolParam.act_proj₁] at h2
    linarith
  have hb : g.b = 0 := b_eq_zero_of_parabolic hach ⟨_, hX₀⟩ hpar' (hinv' hγ₁ hg₁) hbb
    (hinv' hγ hg) (hinv' (Γ.inv_mem hγ) hg')
  rw [← nolToMink_minkToNol p, hg, nullY_nolToMink, NolParam.act_proj₁, hb, add_zero,
    nullY_nolToMink]

end Causal.Flat.Nonlox
