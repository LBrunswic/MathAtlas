import GX.BBS.RP1Circles

/-!
# The generic `G̃` lemmas: rotation lifts, translation numbers, fixed points and parabolic elements

Hoisted from the 3+1 research module `GXScaffold.Interaction.FunnelGTilde` by target
`T-bbs-hs-graduate` (`roadmap/roadmap.toml`), so that BBS § 3.3 (`GX.BBS.PSL2NormalForms`,
`GX.BBS.HSSingularities`) depends on strict modules only. Names, namespaces, statements
and proofs are those of `FunnelGTilde` (T-3p1-funnel-gtilde), unchanged. No ledger label, hence
no `**` mark: these are lemmas about `G̃ = GX.GTilde` itself, used by the paper `bbs`
(`papers/bbs/legacy/labeled/colI_v1.tex`, § 3.3, l.740–760) and by N9 of
`papers/bbs/NOTES-3+1.md` (§2, `:795–799`). 0 `sorry`.

* The rotation lifts `R̃(φ)` (N9 `:795–797`): `GX.slRot`, `GX.slLin_slRot`, `GX.isSLLift_slRot`;
  `GX.GTilde.rot` (`R̃(φ) t = t + φ/2π`), `GX.GTilde.rot_apply`, `GX.GTilde.toPSL_rot`,
  `GX.GTilde.rot_zero`, `GX.GTilde.rot_add`, `GX.GTilde.rot_two_pi` (`R̃(2π) = δ`),
  `GX.GTilde.continuous_rot`, `GX.GTilde.eq_conj_rot_of_lift` (the lift of a conjugated
  one-parameter rotation group is the conjugate).
* The translation number: `GX.GTilde.tau`, `GX.GTilde.angle_eq_two_pi_mul_tau`,
  `GX.GTilde.tau_conj`, `GX.GTilde.tau_rot`, `GX.GTilde.angle_rot` (`angle R̃(φ) = φ`),
  `GX.GTilde.tau_eq_zero_of_fixed`.
* Rotation lifts about any point, `R̃_c(φ)`: `GX.GTilde.IsRotLift`, `GX.GTilde.isRotLift_rot`,
  `GX.GTilde.IsRotLift.tau_eq`, `GX.GTilde.IsRotLift.angle_eq`.
* Fixed points (N9 `:799`, (S′) and its mirror): `GX.GTilde.apply_lt_delta_of_fixed`
  (`g̃ x < δ x`), `GX.GTilde.sub_one_lt_apply_of_fixed` (`x - 1 < g̃ x`); conjugation
  `GX.GTilde.le_conj_apply`.
* Parabolic elements have one fixed point: `GX.PSL2.trSq_one`, `GX.PSL2.slLin_eq_of_smul_eq`,
  `GX.PSL2.IsParabolic.eq_of_smul_eq`; in `G̃`, `GX.GTilde.IsParabolic.eq_add_int_of_fixed`,
  `GX.GTilde.IsParabolic.le_apply` (a parabolic element with a fixed point moving one point to
  the right is positive, l.754–756).
* Types: `GX.GTilde.not_isElliptic_of_toPSL_eq_one`, `GX.GTilde.IsHyperbolic.not_isElliptic`,
  `GX.GTilde.IsHyperbolic.toPSL_ne_one`, `GX.GTilde.IsParabolic.not_isElliptic`.

> **R̃_c(φ)**, for c ∈ ℍ² and φ ∈ ℝ, is the lift of the rotation about c by angle φ along the
> one-parameter rotation group. [...] Hence R̃_c(2π) = δ, and: [...]
> **(S′)** an element g̃ ∈ G̃ with a fixed point satisfies g̃x < δx for every x. (N9 l.795–799)

## Hypothesis checklist

| source | here |
|---|---|
| `R̃_c(φ)`, the lift along the one-parameter rotation group about `c` | ✓ `GX.GTilde.IsRotLift φ`, a conjugate `h R̃(φ) h⁻¹` (SCOPE (a)) |
| (S′): `g̃` has a fixed point | ✓ carried |
| parabolic: `tr² = 4`, `g ≠ 1` | ✓ gx's `GX.PSL2.IsParabolic` |

## SCOPE (disclosed)

* **(a)** `GX.GTilde.rot φ` lifts `rot(φ/2) ∈ SL(2,ℝ)`, which turns `ℝP¹ = P(ℝ²)` once around at
  `φ = 2π`. That it is the hyperbolic rotation of angle `φ` about the point of `ℍ²` fixed by
  `SO(2)` (through `PSL(2,ℝ) ≅ SO₀(1,2)`) is classical and not formalized here; a rotation about
  another point is a conjugate, and its lift along its one-parameter group is the conjugate
  (`GX.GTilde.eq_conj_rot_of_lift`).
* **(b)** The funnel statements (S), (S′) at a singularity, the relation (N), the degree and
  (F1)–(F4) stay in `GXScaffold.Interaction.FunnelGTilde`, which imports this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.BBS.RP1Circles` (T-bbs-rp1-circles, e3220f0).
-/

noncomputable section

open Set Real
open scoped MatrixGroups

namespace GX

/-! ### The rotation lifts `R̃(φ)` (N9 §2) -/

/-- The rotation matrix `rot(α) = [[cos α, -sin α], [sin α, cos α]] ∈ SL(2,ℝ)`. -/
def slRot (α : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos α, -Real.sin α; Real.sin α, Real.cos α], by
    rw [Matrix.det_fin_two_of]; linear_combination Real.cos_sq_add_sin_sq α⟩

/-- `rot(α)` acts on `ℂ = ℝ²` as multiplication by `e^{iα}`. -/
theorem slLin_slRot (α : ℝ) (z : ℂ) : slLin (slRot α) z = (Circle.exp α : ℂ) * z := by
  rw [slLin_apply, Circle.coe_exp]
  apply Complex.ext <;>
    simp [slRot, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> ring

/-- `rot(φ/2)` moves `ℝP¹` by `φ`: `t ↦ t + φ/2π` lifts it. -/
theorem isSLLift_slRot (φ : ℝ) : IsSLLift (slRot (φ / 2)) fun t => t + φ / (2 * π) := by
  refine ⟨continuous_id.add continuous_const, fun t => ?_⟩
  rw [RP1.proj_eq_mk, RP1.proj_eq_mk, RP1.sl_smul_mk _ (Circle.coe_ne_zero _), slLin_slRot,
    ← Circle.coe_mul, ← Circle.exp_add]
  congr 3
  field_simp
  ring

namespace GTilde

/-- **The rotation lift `R̃(φ)`** (N9 §2): the lift to `ℝP̃¹` of the rotation by `φ`, along the
one-parameter group `φ ↦ rot(φ/2)` from `1`; `R̃(φ) t = t + φ/2π`. -/
def rot (φ : ℝ) : GTilde := ofLift (isSLLift_slRot φ)

theorem rot_apply (φ t : ℝ) : rot φ t = t + φ / (2 * π) := rfl

theorem toPSL_rot (φ : ℝ) : toPSL (rot φ) = pslMk (slRot (φ / 2)) := toPSL_ofLift _

theorem rot_zero : rot 0 = 1 := ext' fun x => by rw [rot_apply, one_apply]; simp

theorem rot_add (φ ψ : ℝ) : rot (φ + ψ) = rot φ * rot ψ := ext' fun x => by
  rw [coe_mul_apply, rot_apply, rot_apply, rot_apply]; ring

/-- **`R̃(2π) = δ`** (N9 §2). -/
theorem rot_two_pi : rot (2 * π) = delta := ext' fun x => by
  rw [rot_apply, delta_apply, div_self (by positivity)]

theorem continuous_rot : Continuous fun p : ℝ × ℝ => rot p.1 p.2 := by
  simp_rw [rot_apply]; fun_prop

/-- **`R̃` is the lift along the one-parameter group**, and so is its conjugate: a family
`R φ ∈ G̃` lifting `h rot(φ/2) h⁻¹`, with `R 0 = 1` and `φ ↦ R φ 0` continuous, is
`h R̃(φ) h⁻¹`. -/
theorem eq_conj_rot_of_lift (h : GTilde) {R : ℝ → GTilde}
    (hR : ∀ φ, toPSL (R φ) = toPSL (h * rot φ * h⁻¹)) (hc : Continuous fun φ => R φ 0)
    (h0 : R 0 = 1) (φ : ℝ) : R φ = h * rot φ * h⁻¹ := by
  -- `R ψ = (h R̃(ψ) h⁻¹) δ^{n ψ}`
  have hker : ∀ ψ, ∃ n : ℤ, ∀ x, R ψ x = (h * rot ψ * h⁻¹) x + n := by
    intro ψ
    have hk : (h * rot ψ * h⁻¹)⁻¹ * R ψ ∈ toPSL.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hR, inv_mul_cancel]
    rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hk
    obtain ⟨n, hn⟩ := hk
    refine ⟨n, fun x => ?_⟩
    have : R ψ = (h * rot ψ * h⁻¹) * delta ^ n := by rw [hn, mul_inv_cancel_left]
    rw [this, coe_mul_apply (h * rot ψ * h⁻¹), delta_zpow_apply, map_add_int]
  -- the integer `n ψ = R ψ 0 - (h R̃(ψ) h⁻¹) 0` is continuous, hence constant
  set g : ℝ → ℝ := fun ψ => R ψ 0 - (h * rot ψ * h⁻¹) 0 with hg_def
  have hg : Continuous g := by
    refine hc.sub ?_
    show Continuous fun ψ : ℝ => h (h⁻¹ 0 + ψ / (2 * π))
    exact (GTilde.continuous h).comp (continuous_const.add (continuous_id.div_const _))
  have hgint : ∀ ψ, ∃ n : ℤ, g ψ = n := fun ψ => by
    obtain ⟨n, hn⟩ := hker ψ
    exact ⟨n, by simp only [hg_def]; rw [hn]; ring⟩
  have hg0 : g 0 = 0 := by
    simp only [hg_def]
    rw [h0, rot_zero, mul_one, mul_inv_cancel, one_apply, sub_self]
  have hhalf : ∀ ψ, g ψ ≠ 1 / 2 ∧ g ψ ≠ -1 / 2 := fun ψ => by
    obtain ⟨m, hm⟩ := hgint ψ
    constructor <;> intro h' <;> rw [hm] at h'
    · have : (2 * m : ℝ) = 1 := by linarith
      have : 2 * m = 1 := by exact_mod_cast this
      omega
    · have : (2 * m : ℝ) = -1 := by linarith
      have : 2 * m = -1 := by exact_mod_cast this
      omega
  have hgφ : g φ = 0 := by
    obtain ⟨n, hn⟩ := hgint φ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨ψ, -, hψ⟩ := intermediate_value_uIcc hg.continuousOn
        (show (-1 / 2 : ℝ) ∈ uIcc (g 0) (g φ) by
          rw [hg0, hn] at *
          have : n < 0 := by exact_mod_cast hlt
          have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
          exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by norm_num⟩))
      exact (hhalf ψ).2 hψ
    · obtain ⟨ψ, -, hψ⟩ := intermediate_value_uIcc hg.continuousOn
        (show (1 / 2 : ℝ) ∈ uIcc (g 0) (g φ) by
          rw [hg0, hn] at *
          have : 0 < n := by exact_mod_cast hlt
          have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          exact Set.mem_uIcc.2 (Or.inl ⟨by norm_num, by linarith⟩))
      exact (hhalf ψ).1 hψ
  obtain ⟨n, hn⟩ := hker φ
  have hn0 : (n : ℝ) = 0 := by
    have := hn 0
    have hgφ' : R φ 0 - (h * rot φ * h⁻¹) 0 = 0 := hgφ
    linarith
  exact ext' fun x => by rw [hn, hn0, add_zero]

/-- The translation number of an element of `G̃` (normalisation-free). -/
def tau (f : GTilde) : ℝ :=
  CircleDeg1Lift.translationNumber ((f : CircleDeg1Liftˣ) : CircleDeg1Lift)

theorem angle_eq_two_pi_mul_tau (f : GTilde) : angle f = 2 * π * tau f := rfl

theorem tau_conj (f h : GTilde) : tau (h * f * h⁻¹) = tau f := by
  have := angle_conj f h
  rw [angle_eq_two_pi_mul_tau, angle_eq_two_pi_mul_tau] at this
  exact mul_left_cancel₀ (by positivity) this

theorem tau_rot (φ : ℝ) : tau (rot φ) = φ / (2 * π) := by
  have : ((rot φ : CircleDeg1Liftˣ) : CircleDeg1Lift) =
      CircleDeg1Lift.translate (Multiplicative.ofAdd (φ / (2 * π))) :=
    CircleDeg1Lift.ext fun x => by
      rw [CircleDeg1Lift.translate_apply, add_comm]
      exact rot_apply φ x
  rw [tau, this, CircleDeg1Lift.translationNumber_translate]

/-- **`angle R̃(φ) = φ`** (OQ-113 (a): `angle δ = 2π`). -/
theorem angle_rot (φ : ℝ) : angle (rot φ) = φ := by
  rw [angle_eq_two_pi_mul_tau, tau_rot]; field_simp

/-- `f` is **a rotation lift of angle `φ`** about some point: a conjugate `h R̃(φ) h⁻¹` in `G̃`
(N9 §2, `R̃_c(φ)`; §3.4, `P̃_j′`). -/
def IsRotLift (φ : ℝ) (f : GTilde) : Prop := ∃ h : GTilde, f = h * rot φ * h⁻¹

theorem isRotLift_rot (φ : ℝ) : IsRotLift φ (rot φ) := ⟨1, by simp⟩

theorem IsRotLift.tau_eq {φ : ℝ} {f : GTilde} (hf : IsRotLift φ f) : tau f = φ / (2 * π) := by
  obtain ⟨h, rfl⟩ := hf
  rw [tau_conj, tau_rot]

theorem IsRotLift.angle_eq {φ : ℝ} {f : GTilde} (hf : IsRotLift φ f) : angle f = φ := by
  obtain ⟨h, rfl⟩ := hf
  rw [angle_conj, angle_rot]

/-- **(S′)**: an element of `G̃` with a fixed point satisfies `g̃ x < δ x` for every `x`. -/
theorem apply_lt_delta_of_fixed {f : GTilde} (hf : ∃ x₀, f x₀ = x₀) (x : ℝ) : f x < delta x := by
  -- a fixed point `u = x₀ + ⌊x - x₀⌋` with `u ≤ x < δ u`; `f` preserves `[u, δ u]`
  obtain ⟨x₀, hx₀⟩ := hf
  set n := ⌊x - x₀⌋
  have hu : f (x₀ + (n + 1 : ℤ)) = x₀ + (n + 1 : ℤ) := by rw [map_add_int, hx₀]
  push_cast at hu
  have h1 : x < x₀ + (n + 1) := by have := Int.lt_floor_add_one (x - x₀); linarith
  have h2 : (x₀ + n : ℝ) ≤ x := by have := Int.floor_le (x - x₀); linarith
  have := GTilde.strictMono f h1
  rw [hu] at this
  rw [delta_apply]; linarith

/-- The mirror bound of (S′): `δ⁻¹ x < g̃ x`. -/
theorem sub_one_lt_apply_of_fixed {f : GTilde} (hf : ∃ x₀, f x₀ = x₀) (x : ℝ) : x - 1 < f x := by
  obtain ⟨x₀, hx₀⟩ := hf
  set n := ⌊x - x₀⌋
  have hu : f (x₀ + (n : ℤ)) = x₀ + (n : ℤ) := by rw [map_add_int, hx₀]
  have h1 : x - 1 < x₀ + n := by have := Int.lt_floor_add_one (x - x₀); linarith
  have h2 : (x₀ + n : ℝ) ≤ x := by have := Int.floor_le (x - x₀); linarith
  have := (GTilde.strictMono f).monotone h2
  rw [hu] at this
  linarith

end GTilde

/-! ### Parabolic elements have one fixed point -/

namespace PSL2

theorem trSq_one : trSq (1 : PSL(2, ℝ)) = 4 := by
  rw [show (1 : PSL(2, ℝ)) = pslMk 1 from rfl, trSq_mk]
  simp
  norm_num

/-- An eigenline of `A ∈ SL(2,ℝ)` with `tr(A)² = 4` has eigenvalue `tr(A)/2`. -/
theorem slLin_eq_of_smul_eq {A : SL(2, ℝ)}
    (htr : (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 4) {z : ℂ} (hz : z ≠ 0)
    (h : A • RP1.mk z = RP1.mk z) :
    slLin A z = ((Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2 : ℝ) : ℂ) * z := by
  rw [RP1.sl_smul_mk A hz, RP1.mk_eq_mk_iff (slLin_ne_zero A hz) hz] at h
  obtain ⟨c, hc⟩ := h
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  rw [slLin_apply] at hre him
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero] at hre him
  rw [Matrix.trace_fin_two] at htr ⊢
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
    have := A.2; rw [Matrix.det_fin_two] at this; exact this
  set a := (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c' := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  set x := z.re
  set y := z.im
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hz (Complex.ext hh.1 hh.2)
  have e1 : (c * a - 1) * x + c * b * y = 0 := by linear_combination -hre
  have e2 : c * c' * x + (c * d - 1) * y = 0 := by linear_combination -him
  have hP : (c * a - 1) * (c * d - 1) - c * b * (c * c') = 0 := by
    rcases hxy with hx | hy
    · have : ((c * a - 1) * (c * d - 1) - c * b * (c * c')) * x = 0 := by
        linear_combination (c * d - 1) * e1 - c * b * e2
      exact (mul_eq_zero.1 this).resolve_right hx
    · have : ((c * a - 1) * (c * d - 1) - c * b * (c * c')) * y = 0 := by
        linear_combination (c * a - 1) * e2 - c * c' * e1
      exact (mul_eq_zero.1 this).resolve_right hy
  have hq : c ^ 2 - (a + d) * c + 1 = 0 := by linear_combination hP - c ^ 2 * hdet
  -- `tr² = 4`: the inverse eigenvalue `c` is `2 / tr`
  have hsq : (c * (a + d) - 2) ^ 2 = 0 := by linear_combination 4 * hq + c ^ 2 * htr
  have hct : c * (a + d) - 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
  apply Complex.ext
  · rw [slLin_apply]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linear_combination (-(a + d) / 2) * hre + (-(a * x + b * y) / 2) * hct
  · rw [slLin_apply]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    linear_combination (-(a + d) / 2) * him + (-(c' * x + d * y) / 2) * hct

/-- **A parabolic element of `PSL(2,ℝ)` has at most one fixed point on `ℝP¹`** (existence is
`exists_smul_eq_of_not_isElliptic`). -/
theorem IsParabolic.eq_of_smul_eq {g : PSL(2, ℝ)} (hg : IsParabolic g) {w w' : RP1}
    (hw : g • w = w) (hw' : g • w' = w') : w = w' := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  obtain ⟨htr, hne⟩ := hg
  rw [trSq_mk] at htr
  rw [← RP1.mk_rep w, pslMk_smul] at hw
  rw [← RP1.mk_rep w', pslMk_smul] at hw'
  have e := slLin_eq_of_smul_eq htr (RP1.rep_ne_zero w) hw
  have e' := slLin_eq_of_smul_eq htr (RP1.rep_ne_zero w') hw'
  by_contra hww
  apply hne
  have hz := RP1.rep_ne_zero w
  have hz' := RP1.rep_ne_zero w'
  -- the two eigenlines are distinct
  have hD : (RP1.rep w).re * (RP1.rep w').im - (RP1.rep w).im * (RP1.rep w').re ≠ 0 := by
    intro hD
    apply hww
    rw [← RP1.mk_rep w, ← RP1.mk_rep w', RP1.mk_eq_mk_iff hz hz']
    by_cases hx : (RP1.rep w).re = 0
    · have hy : (RP1.rep w).im ≠ 0 := fun hy => hz (Complex.ext hx hy)
      rw [hx] at hD
      refine ⟨(RP1.rep w').im / (RP1.rep w).im, Complex.ext ?_ ?_⟩
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hx,
          mul_zero]
        have : (RP1.rep w).im * (RP1.rep w').re = 0 := by linarith
        exact ((mul_eq_zero.1 this).resolve_left hy)
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        field_simp
    · refine ⟨(RP1.rep w').re / (RP1.rep w).re, Complex.ext ?_ ?_⟩
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        field_simp
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        field_simp
        linear_combination hD
  have ere := congrArg Complex.re e
  have eim := congrArg Complex.im e
  have ere' := congrArg Complex.re e'
  have eim' := congrArg Complex.im e'
  rw [slLin_apply] at ere eim ere' eim'
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero] at ere eim ere' eim'
  rw [Matrix.trace_fin_two] at htr ere eim ere' eim'
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
    have := A.2; rw [Matrix.det_fin_two] at this; exact this
  set a := (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c' := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  set x := (RP1.rep w).re
  set y := (RP1.rep w).im
  set x' := (RP1.rep w').re
  set y' := (RP1.rep w').im
  set D := x * y' - y * x'
  -- `A = λ I`, `λ = tr/2`
  have ha : a = (a + d) / 2 := by
    have : (a - (a + d) / 2) * D = 0 := by linear_combination y' * ere - y * ere'
    linarith [sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)]
  have hb : b = 0 := by
    have : b * D = 0 := by linear_combination x * ere' - x' * ere
    exact (mul_eq_zero.1 this).resolve_right hD
  have hc : c' = 0 := by
    have : c' * D = 0 := by linear_combination y' * eim - y * eim'
    exact (mul_eq_zero.1 this).resolve_right hD
  have hd : d = a := by linarith
  have hcen : A ∈ Subgroup.center SL(2, ℝ) := by
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨a, ?_, ?_⟩
    · simp only [Fintype.card_fin]
      rw [hb, hd] at hdet
      linear_combination hdet
    · ext i j
      fin_cases i <;> fin_cases j
      · show Matrix.scalar (Fin 2) a 0 0 = a
        simp
      · show Matrix.scalar (Fin 2) a 0 1 = b
        rw [hb]; simp
      · show Matrix.scalar (Fin 2) a 1 0 = c'
        rw [hc]; simp
      · show Matrix.scalar (Fin 2) a 1 1 = d
        rw [hd]; simp
  exact (QuotientGroup.eq_one_iff A).2 hcen

end PSL2

namespace GTilde

/-- The fixed points of a parabolic `f ∈ G̃` with a fixed point `x₀` are the `x₀ + n`. -/
theorem IsParabolic.eq_add_int_of_fixed {f : GTilde} (hf : IsParabolic f) {x₀ y : ℝ}
    (hx₀ : f x₀ = x₀) (hy : f y = y) : ∃ n : ℤ, y = x₀ + n := by
  have h1 : toPSL f • RP1.proj x₀ = RP1.proj x₀ := by rw [← proj_apply, hx₀]
  have h2 : toPSL f • RP1.proj y = RP1.proj y := by rw [← proj_apply, hy]
  exact RP1.proj_eq_proj_iff.1 (PSL2.IsParabolic.eq_of_smul_eq hf h2 h1)

/-- **A parabolic element of degree `0` moving one point to the right is positive**
(l.754–756): `x ≤ f x` for every `x`. -/
theorem IsParabolic.le_apply {f : GTilde} (hf : IsParabolic f) (hfix : ∃ x₀, f x₀ = x₀)
    (hgt : ∃ x, x < f x) (x : ℝ) : x ≤ f x := by
  obtain ⟨x₀, hx₀⟩ := hfix
  obtain ⟨x₁, hx₁⟩ := hgt
  by_contra hlt
  push Not at hlt
  -- the displacement `d y = f y - y`, `1`-periodic, vanishing exactly on `x₀ + ℤ`
  set d : ℝ → ℝ := fun y => f y - y with hd
  have hdc : Continuous d := (GTilde.continuous f).sub continuous_id
  have hper : ∀ y, d (y - ⌊y - x₀⌋) = d y := fun y => by
    simp only [hd]
    rw [show y - (⌊y - x₀⌋ : ℝ) = y + ((-⌊y - x₀⌋ : ℤ) : ℝ) by push_cast; ring, map_add_int]
    push_cast; ring
  have hmem : ∀ y, d y ≠ 0 → x₀ < y - ⌊y - x₀⌋ ∧ y - ⌊y - x₀⌋ < x₀ + 1 := fun y hy => by
    refine ⟨lt_of_le_of_ne (by have := Int.floor_le (y - x₀); linarith) fun h => ?_,
      by have := Int.lt_floor_add_one (y - x₀); linarith⟩
    apply hy
    rw [← hper y, ← h]
    simp only [hd, hx₀, sub_self]
  have hu := hmem x (by simp only [hd]; linarith)
  have hv := hmem x₁ (by simp only [hd]; linarith)
  have hdu : d (x - ⌊x - x₀⌋) < 0 := by rw [hper]; simp only [hd]; linarith
  have hdv : 0 < d (x₁ - ⌊x₁ - x₀⌋) := by rw [hper]; simp only [hd]; linarith
  -- a fixed point strictly between `x₀` and `x₀ + 1`
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hdc.continuousOn
    (show (0 : ℝ) ∈ uIcc (d (x - ⌊x - x₀⌋)) (d (x₁ - ⌊x₁ - x₀⌋)) from
      Set.mem_uIcc.2 (Or.inl ⟨hdu.le, hdv.le⟩))
  have hfz : f z = z := by simp only [hd] at hz0; linarith
  obtain ⟨n, hn⟩ := hf.eq_add_int_of_fixed hx₀ hfz
  have hz1 : x₀ < z ∧ z < x₀ + 1 := by
    rcases Set.mem_uIcc.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
      linarith [hu.1, hu.2, hv.1, hv.2]
  have h3 : (0 : ℝ) < n := by linarith
  have h4 : (n : ℝ) < 1 := by linarith
  have : 0 < n := by exact_mod_cast h3
  have : n < 1 := by exact_mod_cast h4
  omega

/-- Conjugation preserves `x ≤ f x`. -/
theorem le_conj_apply {f : GTilde} (hf : ∀ y, y ≤ f y) (h : GTilde) (x : ℝ) :
    x ≤ (h * f * h⁻¹) x := by
  rw [coe_mul_apply, coe_mul_apply]
  have := (GTilde.strictMono h).monotone (hf (h⁻¹ x))
  rwa [apply_inv_apply] at this

theorem tau_eq_zero_of_fixed {f : GTilde} {x : ℝ} (hx : f x = x) : tau f = 0 := by
  have := angle_eq_zero_of_fixed hx
  rw [angle_eq_two_pi_mul_tau] at this
  exact (mul_eq_zero.1 this).resolve_left (by positivity)

theorem not_isElliptic_of_toPSL_eq_one {f : GTilde} (hf : toPSL f = 1) : ¬ IsElliptic f := by
  intro h
  have : PSL2.trSq (toPSL f) < 4 := h
  rw [hf, PSL2.trSq_one] at this
  exact lt_irrefl _ this

theorem IsHyperbolic.not_isElliptic {f : GTilde} (hf : IsHyperbolic f) : ¬ IsElliptic f :=
  fun h => lt_asymm (show (4 : ℝ) < PSL2.trSq (toPSL f) from hf) h

theorem IsHyperbolic.toPSL_ne_one {f : GTilde} (hf : IsHyperbolic f) : toPSL f ≠ 1 := by
  intro h
  have : (4 : ℝ) < PSL2.trSq (toPSL f) := hf
  rw [h, PSL2.trSq_one] at this
  exact lt_irrefl _ this

theorem IsParabolic.not_isElliptic {f : GTilde} (hf : IsParabolic f) : ¬ IsElliptic f :=
  fun h => (show PSL2.trSq (toPSL f) < 4 from h).ne (hf.1)

end GTilde

end GX
