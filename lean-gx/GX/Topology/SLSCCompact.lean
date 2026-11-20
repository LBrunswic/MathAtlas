import GX.Branched.Galois
import GX.Topology.VanKampen

/-!
# A compact counterexample to `rem:definition_semi_locally_simply_connected`

Target T-gx-slsc-compact (DEC-135). `papers/gx`, `RamcovGX.tex:1451–1457`.

* `rem:definition_semi_locally_simply_connected` — `RamcovGX.tex:1455` (partial, as in
  `GX.Branched.Galois`, SCOPE (e): the printed "iff" is false). This file adds the COMPACT
  counterexample DEC-135 asks for, to the direction "semi-locally simply connected in itself ⇒
  semi-locally simply connected": `GX.griffiths_counterexample`,
  `GX.not_semilocallySimplyConnected_of_isSLSCInCC_univ_compact` (the harmonic archipelago
  `GX.harmonicArchipelago_counterexample` is not compact).

> The definition of semi-locally simply connected is coherent with the usual definition of
> semi-locally simply connected. Indeed a topological space $X$ is semi-locally simply connected
> if and only if it is semi-locally simply connected in itself.

**The space** `GX.GriffithsSpace ⊆ ℂ × ℝ = ℝ³` is the Griffiths twin cone: the cone with apex
`(1/2, 1)` over the right Hawaiian earring `⋃ₙ {|z - 1/n| = 1/n}` (`GX.grifConeA`), union the
cone with apex `(-1/2, 1)` over its mirror image (`GX.grifConeB`); the two cones meet only at `0`,
the earrings' common point (`GX.grifX0`). It is compact, Hausdorff, path-connected and locally
path-connected (a quotient of two squares, `GX.grifPiA`, `GX.grifPiB`) and metrizable: a Peano
continuum.

**Slsc in itself** (`GX.griffiths_isSLSCIn`, homotopy form; the literal DEC-55 form
`GX.griffiths_isSLSCInCC` follows): a point `≠ 0` has a neighbourhood inside one cone, which is
star-shaped (`GX.grif_isSLSCAt_of_ne`); at `0` (`GX.grif_isSLSCAt_x0`) a loop below the apexes
slides down the cone lines (`GX.grifR`) onto the double earring, and the finitely many circles of
index `< N` are then contracted through their cones (`GX.grifColl`), leaving a loop in the
`2/N`-ball.

**Not slsc** (`GX.griffiths_not_semilocallySimplyConnected`): the loops `∏_{n ≥ N} aₙ bₙ`
(`GX.grifOmegaK`) lie in the `2/N`-ball and are not null-homotopic
(`GX.griffiths_omega_not_homotopic`). The invariant is the *linking matrix* `Z_{ij}(δ)` of a loop
of the double earring (`GX.grifZ`: the winding of `χ_{b_j}` raised to the level of `χ_{a_i}`), a
homotopy-invariant (`GX.grifZ_homotopic`) crossed homomorphism (`GX.grifZ_trans`); modulo the
integer matrices of finite rank it is a homomorphism `GX.grifTheta`, trivial on each earring and
nontrivial on `∏ aₙ bₙ`, whose matrix is the infinite unitriangular one (`GX.grif_not_mem_FR`).
Two Seifert–van Kampen gluings, one per apex (`GX.grifD1`, `GX.grifD2`, on `GX.VanKampen.Data`
with its multiplicativity `GX.VanKampen.Data.Φ_trans`, new here), extend it to every loop of the
space.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `def:semi_locally_simple_connectedness`: `X` Hausdorff, connected, locally path-connected | ✓ carried by the witness, which is moreover compact and metrizable |
| "semi-locally simply connected in itself" | ✓ the literal DEC-55 form `GX.IsSLSCInCC univ`, and the homotopy form `GX.IsSLSCIn univ` |
| "semi-locally simply connected" | ✓ `GX.SemilocallySimplyConnected` (DEC-41), as in `GX.Branched.Galois` |

## SCOPE (disclosed)

The row stays partial: the true direction is `GX.isSLSCInCC_univ_of_semilocallySimplyConnected`
of `GX.Branched.Galois`; this file only adds a compact counterexample to the false direction,
refuting the printed "iff" also among compact (metrizable) spaces. The non-triviality of the
loops is proved from scratch by the linking-matrix invariant, not by Griffiths' original
argument; nothing is cited. Not proved, and not needed: that `π₁` is uncountable, or any
property of the space beyond those of `GX.griffiths_counterexample`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function Filter Topology unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ### The Hawaiian earrings -/

/-- `e(θ) = exp(2πiθ)`. -/
def grifE (θ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)

theorem norm_grifE (θ : ℝ) : ‖grifE θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem grifE_ne_zero (θ : ℝ) : grifE θ ≠ 0 := Complex.exp_ne_zero _

theorem continuous_grifE : Continuous grifE := by unfold grifE; fun_prop

theorem grifE_eq_exp (θ : ℝ) : grifE θ = Complex.exp ((θ : ℂ) * (2 * Real.pi * Complex.I)) := by
  unfold grifE; congr 1; push_cast; ring

theorem grifE_add_int (θ : ℝ) (k : ℤ) : grifE (θ + k) = grifE θ := by
  rw [grifE_eq_exp, grifE_eq_exp, show (((θ + k : ℝ)) : ℂ) * (2 * Real.pi * Complex.I) =
    (θ : ℂ) * (2 * Real.pi * Complex.I) + k * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem grifE_sub_int (θ : ℝ) (k : ℤ) : grifE (θ - k) = grifE θ := by
  rw [sub_eq_add_neg, show -(k : ℝ) = ((-k : ℤ) : ℝ) by push_cast; ring, grifE_add_int]

theorem grifE_int (k : ℤ) : grifE k = 1 := by
  have := grifE_add_int 0 k
  rw [zero_add] at this
  rw [this]; simp [grifE]

theorem grifE_nat (k : ℕ) : grifE k = 1 := by exact_mod_cast grifE_int k

theorem grifE_zero : grifE 0 = 1 := by simpa using grifE_nat 0

theorem grifE_one : grifE 1 = 1 := by simpa using grifE_nat 1

theorem grif_re_inv_one_sub {e : ℂ} (he : ‖e‖ = 1) (he1 : e ≠ 1) : ((1 - e)⁻¹).re = 1 / 2 := by
  have h2 : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e
    rw [he, Complex.normSq_apply] at this; nlinarith
  have hre : e.re ≠ 1 := by
    intro h
    apply he1
    have : e.im = 0 := by nlinarith
    exact Complex.ext (by simp [h]) (by simp [this])
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  have h3 : (1 - e.re) * (1 - e.re) + (0 - e.im) * (0 - e.im) = 2 * (1 - e.re) := by nlinarith
  rw [h3]
  have : (1 - e.re) ≠ 0 := sub_ne_zero.2 (Ne.symm hre)
  field_simp

theorem grif_re_le_one_of_norm {e : ℂ} (he : ‖e‖ = 1) : e.re ≤ 1 :=
  (Complex.re_le_norm e).trans he.le

/-- The point `(1 - e(θ))/n` of the circle of radius `1/n` centred at `1/n`. -/
def grifCirc (n : ℝ) (θ : ℝ) : ℂ := (1 - grifE θ) / n

theorem grifCirc_eq_zero_iff {n : ℝ} (hn : n ≠ 0) (θ : ℝ) :
    grifCirc n θ = 0 ↔ grifE θ = 1 := by
  rw [grifCirc, div_eq_zero_iff, sub_eq_zero]
  simp [hn, eq_comm]

theorem grifCirc_of_eq_one {n θ : ℝ} (h : grifE θ = 1) : grifCirc n θ = 0 := by
  simp [grifCirc, h]

theorem two_re_inv_grifCirc (n : ℝ) {θ : ℝ} (he : grifE θ ≠ 1) :
    2 * ((grifCirc n θ)⁻¹).re = n := by
  rw [grifCirc, inv_div, div_eq_mul_inv, Complex.re_ofReal_mul,
    grif_re_inv_one_sub (norm_grifE θ) he]
  ring

theorem re_grifCirc_nonneg {n : ℝ} (hn : 0 < n) (θ : ℝ) : 0 ≤ (grifCirc n θ).re := by
  rw [grifCirc, Complex.div_ofReal_re]
  have := grif_re_le_one_of_norm (norm_grifE θ)
  apply div_nonneg _ hn.le
  simp only [Complex.sub_re, Complex.one_re]; linarith

theorem grifCirc_re_eq_zero {n : ℝ} (hn : 0 < n) {θ : ℝ} (h : (grifCirc n θ).re = 0) :
    grifCirc n θ = 0 := by
  rw [grifCirc_eq_zero_iff hn.ne']
  rw [grifCirc, Complex.div_ofReal_re, div_eq_zero_iff] at h
  rcases h with h | h
  · simp only [Complex.sub_re, Complex.one_re] at h
    have hre : (grifE θ).re = 1 := by linarith
    have h2 : (grifE θ).re ^ 2 + (grifE θ).im ^ 2 = 1 := by
      have := Complex.sq_norm (grifE θ)
      rw [norm_grifE, Complex.normSq_apply] at this; nlinarith
    have : (grifE θ).im = 0 := by nlinarith
    exact Complex.ext (by simp [hre]) (by simp [this])
  · exact absurd h hn.ne'

theorem grif_norm_mul_two_re_inv_le {q : ℂ} (hq : q ≠ 0) : ‖q‖ * |2 * (q⁻¹).re| ≤ 2 := by
  have hn : 0 < ‖q‖ := norm_pos_iff.2 hq
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq, abs_mul, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ‖q‖ ^ 2), abs_two]
  calc ‖q‖ * (2 * (|q.re| / ‖q‖ ^ 2)) = 2 * (|q.re| / ‖q‖) := by field_simp
    _ ≤ 2 * 1 := by gcongr; rw [div_le_one hn]; exact Complex.abs_re_le_norm q
    _ = 2 := mul_one 2

theorem norm_grifCirc_le {n : ℝ} (hn : 0 < n) (θ : ℝ) : ‖grifCirc n θ‖ ≤ 2 / n := by
  rw [grifCirc, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  gcongr
  calc ‖1 - grifE θ‖ ≤ ‖(1 : ℂ)‖ + ‖grifE θ‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, norm_grifE]; norm_num

/-- The right earring: circles of radius `1/n` centred at `1/n`. -/
def grifHEA : Set ℂ := {q | ∃ n : ℕ, ∃ θ : ℝ, q = grifCirc (n + 1) θ}

/-- The left earring, its mirror image. -/
def grifHEB : Set ℂ := {q | -q ∈ grifHEA}

/-- The double earring. -/
def grifK : Set ℂ := grifHEA ∪ grifHEB

theorem zero_mem_grifHEA : (0 : ℂ) ∈ grifHEA :=
  ⟨0, 0, (grifCirc_of_eq_one grifE_zero).symm⟩

theorem zero_mem_grifHEB : (0 : ℂ) ∈ grifHEB := by
  simp only [grifHEB, mem_setOf_eq, neg_zero]; exact zero_mem_grifHEA

theorem zero_mem_grifK : (0 : ℂ) ∈ grifK := Or.inl zero_mem_grifHEA

theorem re_nonneg_of_mem_grifHEA {q : ℂ} (hq : q ∈ grifHEA) : 0 ≤ q.re := by
  obtain ⟨n, θ, rfl⟩ := hq
  exact re_grifCirc_nonneg (by positivity) θ

theorem re_nonpos_of_mem_grifHEB {q : ℂ} (hq : q ∈ grifHEB) : q.re ≤ 0 := by
  have := re_nonneg_of_mem_grifHEA hq
  simp only [Complex.neg_re] at this; linarith

theorem eq_zero_of_mem_grifHEA_of_re {q : ℂ} (hq : q ∈ grifHEA) (h : q.re = 0) : q = 0 := by
  obtain ⟨n, θ, rfl⟩ := hq
  exact grifCirc_re_eq_zero (by positivity) h

theorem eq_zero_of_mem_grifHEA_of_mem_grifHEB {q : ℂ} (ha : q ∈ grifHEA) (hb : q ∈ grifHEB) :
    q = 0 :=
  eq_zero_of_mem_grifHEA_of_re ha (le_antisymm (re_nonpos_of_mem_grifHEB hb)
    (re_nonneg_of_mem_grifHEA ha))

theorem norm_le_of_mem_grifK {q : ℂ} (hq : q ∈ grifK) : ‖q‖ ≤ 2 := by
  rcases hq with ⟨n, θ, rfl⟩ | ⟨n, θ, h⟩
  · exact (norm_grifCirc_le (by positivity) θ).trans
      (by rw [div_le_iff₀ (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  · rw [← norm_neg, h]
    exact (norm_grifCirc_le (by positivity) θ).trans
      (by rw [div_le_iff₀ (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-! ### Characters of the circles -/

/-- A bump, `1` at `0` and `0` at every other integer. -/
def grifBump (x : ℝ) : ℝ := max 0 (1 - 2 * |x|)

theorem continuous_grifBump : Continuous grifBump := by unfold grifBump; fun_prop

theorem grifBump_nonneg (x : ℝ) : 0 ≤ grifBump x := le_max_left _ _

theorem grifBump_le_one (x : ℝ) : grifBump x ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg x])

theorem abs_grifBump_le (x : ℝ) : |grifBump x| ≤ 1 := by
  rw [abs_of_nonneg (grifBump_nonneg x)]; exact grifBump_le_one x

theorem grifBump_zero : grifBump 0 = 1 := by simp [grifBump]

theorem grifBump_int {k : ℤ} (hk : k ≠ 0) : grifBump k = 0 := by
  have : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  exact max_eq_left (by linarith)

/-- `q ↦ q · f(q)` is continuous when `f` is continuous off `0` and bounded by `1`. -/
theorem grif_continuous_mul_bdd {f : ℂ → ℝ} (hf : ContinuousOn f {q | q ≠ 0})
    (hb : ∀ q, |f q| ≤ 1) : Continuous fun q : ℂ => q * (f q : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro q
  rcases eq_or_ne q 0 with rfl | hq
  · rw [ContinuousAt, zero_mul]
    refine squeeze_zero_norm (a := fun q : ℂ => ‖q‖) (fun q => ?_) ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (hb q)
    · simpa using (continuous_norm (E := ℂ)).tendsto 0
  · exact continuousAt_id.mul (Complex.continuous_ofReal.continuousAt.comp
      (hf.continuousAt (isOpen_ne.mem_nhds hq)))

/-- The character of the `i`-th circle of the right earring: `1 - i q` on it, `1` elsewhere. -/
def grifChiA (i : ℕ) (q : ℂ) : ℂ := 1 - (i : ℂ) * (q * (grifBump (2 * (q⁻¹).re - i) : ℂ))

/-- The character of the `j`-th circle of the left earring: `1 + j q` on it, `1` elsewhere. -/
def grifChiB (j : ℕ) (q : ℂ) : ℂ := 1 + (j : ℂ) * (q * (grifBump (-2 * (q⁻¹).re - j) : ℂ))

theorem continuous_grifChiA (i : ℕ) : Continuous (grifChiA i) := by
  have : Continuous fun q : ℂ => q * (grifBump (2 * (q⁻¹).re - i) : ℂ) :=
    grif_continuous_mul_bdd
      (continuous_grifBump.comp_continuousOn
        (((Complex.continuous_re.comp_continuousOn continuousOn_inv₀).const_smul (2 : ℝ)).sub
          continuousOn_const)) (fun q => abs_grifBump_le _)
  unfold grifChiA; fun_prop

theorem continuous_grifChiB (j : ℕ) : Continuous (grifChiB j) := by
  have : Continuous fun q : ℂ => q * (grifBump (-2 * (q⁻¹).re - j) : ℂ) :=
    grif_continuous_mul_bdd
      (continuous_grifBump.comp_continuousOn
        (((Complex.continuous_re.comp_continuousOn continuousOn_inv₀).const_smul (-2 : ℝ)).sub
          continuousOn_const)) (fun q => abs_grifBump_le _)
  unfold grifChiB; fun_prop

theorem grifChiA_zero (i : ℕ) : grifChiA i 0 = 1 := by simp [grifChiA]

theorem grifChiB_zero (j : ℕ) : grifChiB j 0 = 1 := by simp [grifChiB]

theorem grifChiA_circ {k : ℕ} (hk : 0 < k) (θ : ℝ) (i : ℕ) :
    grifChiA i (grifCirc k θ) = if i = k then grifE θ else 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases he : grifE θ = 1
  · rw [grifCirc_of_eq_one he, grifChiA_zero, he]; simp
  have h2 := two_re_inv_grifCirc k he
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, grifChiA, h2, sub_self, grifBump_zero, grifCirc]
    push_cast
    field_simp
    ring
  · rw [if_neg hik, grifChiA, h2,
      show ((k : ℝ) - i) = (((k : ℤ) - i : ℤ) : ℝ) by push_cast; ring,
      grifBump_int (by omega)]
    simp

theorem grifChiB_neg_circ {k : ℕ} (hk : 0 < k) (θ : ℝ) (j : ℕ) :
    grifChiB j (-grifCirc k θ) = if j = k then grifE θ else 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases he : grifE θ = 1
  · rw [grifCirc_of_eq_one he, neg_zero, grifChiB_zero, he]; simp
  have h2 := two_re_inv_grifCirc k he
  have h3 : -2 * ((-grifCirc k θ)⁻¹).re = k := by
    rw [inv_neg, Complex.neg_re]; linarith
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, grifChiB, h3, sub_self, grifBump_zero, grifCirc]
    push_cast
    field_simp
    ring
  · rw [if_neg hjk, grifChiB, h3,
      show ((k : ℝ) - j) = (((k : ℤ) - j : ℤ) : ℝ) by push_cast; ring,
      grifBump_int (by omega)]
    simp

theorem grifChiA_neg_circ {k : ℕ} (hk : 0 < k) (θ : ℝ) (i : ℕ) :
    grifChiA i (-grifCirc k θ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases he : grifE θ = 1
  · rw [grifCirc_of_eq_one he, neg_zero, grifChiA_zero]
  have h2 := two_re_inv_grifCirc k he
  have h3 : 2 * ((-grifCirc k θ)⁻¹).re = -k := by
    rw [inv_neg, Complex.neg_re]; linarith
  rw [grifChiA, h3, show (-(k : ℝ) - i) = ((-(k : ℤ) - i : ℤ) : ℝ) by push_cast; ring,
    grifBump_int (by omega)]
  simp

theorem grifChiB_circ {k : ℕ} (hk : 0 < k) (θ : ℝ) (j : ℕ) :
    grifChiB j (grifCirc k θ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases he : grifE θ = 1
  · rw [grifCirc_of_eq_one he, grifChiB_zero]
  have h2 := two_re_inv_grifCirc k he
  rw [grifChiB, show -2 * ((grifCirc k θ)⁻¹).re - j = ((-(k : ℤ) - j : ℤ) : ℝ) by
    push_cast; linarith, grifBump_int (by omega)]
  simp

theorem grifChiB_of_mem_grifHEA {q : ℂ} (hq : q ∈ grifHEA) (j : ℕ) : grifChiB j q = 1 := by
  obtain ⟨n, θ, rfl⟩ := hq
  exact_mod_cast grifChiB_circ (k := n + 1) n.succ_pos θ j

theorem grifChiA_of_mem_grifHEB {q : ℂ} (hq : q ∈ grifHEB) (i : ℕ) : grifChiA i q = 1 := by
  obtain ⟨n, θ, h⟩ := hq
  rw [show q = -grifCirc ((n + 1 : ℕ) : ℝ) θ by rw [← neg_neg q, h]; push_cast; rfl]
  exact grifChiA_neg_circ n.succ_pos θ i

theorem norm_grifChiA {q : ℂ} (hq : q ∈ grifK) (i : ℕ) : ‖grifChiA i q‖ = 1 := by
  rcases hq with ⟨n, θ, rfl⟩ | hq
  · rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl,
      grifChiA_circ n.succ_pos θ i]
    split_ifs
    · exact norm_grifE θ
    · exact norm_one
  · rw [grifChiA_of_mem_grifHEB hq, norm_one]

theorem norm_grifChiB {q : ℂ} (hq : q ∈ grifK) (j : ℕ) : ‖grifChiB j q‖ = 1 := by
  rcases hq with hq | ⟨n, θ, h⟩
  · rw [grifChiB_of_mem_grifHEA hq, norm_one]
  · rw [show q = -grifCirc ((n + 1 : ℕ) : ℝ) θ by rw [← neg_neg q, h]; push_cast; rfl,
      grifChiB_neg_circ n.succ_pos θ j]
    split_ifs
    · exact norm_grifE θ
    · exact norm_one

/-- On the double earring, where the `j`-th left character moves, every right one is `1`. -/
theorem grifChiA_eq_one_of_grifChiB_ne {q : ℂ} (hq : q ∈ grifK) {j : ℕ}
    (h : grifChiB j q ≠ 1) (i : ℕ) : grifChiA i q = 1 := by
  rcases hq with hq | hq
  · exact absurd (grifChiB_of_mem_grifHEA hq j) h
  · exact grifChiA_of_mem_grifHEB hq i

/-! ### Loops run block by block along the half-line -/

/-- A loop run along the half-line `[0, ∞)` (time `t ↦ t/(1-t)`), closed at `0` at time `1`. -/
def grifBlock (F : ℝ → ℂ) (t : I) : ℂ := if (t : ℝ) < 1 then F ((t : ℝ) / (1 - t)) else 0

theorem grifBlock_one (F : ℝ → ℂ) : grifBlock F 1 = 0 := by simp [grifBlock]

theorem grifBlock_zero (F : ℝ → ℂ) : grifBlock F 0 = F 0 := by simp [grifBlock]

theorem grif_s_nonneg (t : I) : 0 ≤ (t : ℝ) / (1 - t) := div_nonneg t.2.1 (by linarith [t.2.2])

theorem grif_floor_eventually {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≠ ⌊s⌋₊) :
    ∀ᶠ s' in 𝓝 s, ⌊s'⌋₊ = ⌊s⌋₊ := by
  have h1 : (⌊s⌋₊ : ℝ) < s := lt_of_le_of_ne (Nat.floor_le hs0) (Ne.symm hs)
  have h2 : s < ⌊s⌋₊ + 1 := Nat.lt_floor_add_one s
  filter_upwards [Ioo_mem_nhds h1 h2] with s' hs'
  rw [Nat.floor_eq_iff (by linarith [hs'.1, (Nat.cast_nonneg ⌊s⌋₊ : (0 : ℝ) ≤ _)])]
  exact ⟨hs'.1.le, hs'.2⟩

/-- **Continuity of a block loop.** `c · g` with `g` continuous and bounded, `|c| ≤ 1/(N + ⌊s⌋)`,
and `c` locally constant wherever `g ≠ 0`. -/
theorem continuous_grifBlock {c g : ℝ → ℂ} {B N : ℝ} (hN : 0 < N)
    (hg : Continuous g) (hgB : ∀ s, ‖g s‖ ≤ B)
    (hc : ∀ s, 0 ≤ s → ‖c s‖ ≤ 1 / (N + ⌊s⌋₊))
    (hloc : ∀ s, 0 ≤ s → g s ≠ 0 → ∀ᶠ s' in 𝓝 s, c s' = c s) :
    Continuous (grifBlock fun s => c s * g s) := by
  have hc1 : ∀ s, 0 ≤ s → ‖c s‖ ≤ 1 / N := fun s hs =>
    (hc s hs).trans (one_div_le_one_div_of_le hN (by linarith [(Nat.cast_nonneg ⌊s⌋₊ : (0:ℝ) ≤ _)]))
  rw [continuous_iff_continuousAt]
  intro t
  rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
  · have hev : grifBlock (fun s => c s * g s) =ᶠ[𝓝 t]
        fun t : I => c ((t : ℝ) / (1 - t)) * g ((t : ℝ) / (1 - t)) := by
      filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds ht]
        with t' ht'
      simp only [grifBlock, if_pos (show (t' : ℝ) < 1 from ht')]
    refine ContinuousAt.congr ?_ hev.symm
    have hsc : ContinuousAt (fun t : I => (t : ℝ) / (1 - t)) t :=
      (continuous_subtype_val.continuousAt).div
        (continuous_const.sub continuous_subtype_val).continuousAt (by linarith)
    set s₀ := (t : ℝ) / (1 - t)
    by_cases hg0 : g s₀ = 0
    · rw [ContinuousAt, hg0, mul_zero]
      refine squeeze_zero_norm (a := fun t' : I => (1 / N) * ‖g ((t' : ℝ) / (1 - t'))‖)
        (fun t' => ?_) ?_
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc1 _ (grif_s_nonneg t')) (norm_nonneg _)
      · have := ((continuous_norm.tendsto (g s₀)).comp
          ((hg.continuousAt (x := s₀)).tendsto.comp hsc)).const_mul (1 / N)
        rw [hg0, norm_zero, mul_zero] at this
        exact this
    · have hev2 : (fun t : I => c ((t : ℝ) / (1 - t)) * g ((t : ℝ) / (1 - t))) =ᶠ[𝓝 t]
          fun t : I => c s₀ * g ((t : ℝ) / (1 - t)) := by
        filter_upwards [hsc.eventually (hloc s₀ (grif_s_nonneg t) hg0)] with t' ht'
        rw [ht']
      exact ContinuousAt.congr (continuousAt_const.mul (hg.continuousAt.comp hsc)) hev2.symm
  · have ht1 : t = 1 := Subtype.ext ht
    subst ht1
    rw [ContinuousAt, grifBlock_one, tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    have hlt : ((M : ℝ) / (M + 1)) < ((1 : I) : ℝ) := by
      rw [Set.Icc.coe_one, div_lt_one (by positivity)]; linarith
    filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hlt] with t' ht'
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_cases h1 : (t' : ℝ) < 1
    · simp only [grifBlock, if_pos h1]
      have hpos : 0 < 1 - (t' : ℝ) := by linarith
      have hs : (M : ℝ) ≤ (t' : ℝ) / (1 - t') := by
        rw [le_div_iff₀ hpos]
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < M + 1)).1 ht'
        nlinarith
      have hfl : M ≤ ⌊(t' : ℝ) / (1 - t')⌋₊ := Nat.le_floor hs
      have hfl' : (M : ℝ) ≤ ⌊(t' : ℝ) / (1 - t')⌋₊ := by exact_mod_cast hfl
      have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0)
      rw [norm_mul]
      calc ‖c ((t' : ℝ) / (1 - t'))‖ * ‖g ((t' : ℝ) / (1 - t'))‖
          ≤ 1 / (N + M) * B := by
            refine mul_le_mul ((hc _ (grif_s_nonneg t')).trans ?_) (hgB _) (norm_nonneg _)
              (by positivity)
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
        _ < ε := by
            rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hε] at hM
            nlinarith
    · simp only [grifBlock, if_neg h1, norm_zero]; exact hε

/-! ### The surjections onto the earrings -/

/-- On `[n, n+1]`, the circle of radius `1/(n+1)` once. -/
def grifSigmaF (s : ℝ) : ℂ := grifCirc (⌊s⌋₊ + 1) s

theorem grifSigmaF_eq (s : ℝ) :
    grifSigmaF s = ((1 / ((⌊s⌋₊ : ℝ) + 1) : ℝ) : ℂ) * (1 - grifE s) := by
  rw [grifSigmaF, grifCirc]; push_cast; ring

theorem continuous_grifBlock_sigma : Continuous (grifBlock grifSigmaF) := by
  have e : grifSigmaF = fun s => ((1 / ((⌊s⌋₊ : ℝ) + 1) : ℝ) : ℂ) * (1 - grifE s) :=
    funext grifSigmaF_eq
  rw [e]
  refine continuous_grifBlock (B := 2) (N := 1) one_pos (continuous_const.sub continuous_grifE)
    (fun s => ?_) (fun s hs => ?_) (fun s hs hg => ?_)
  · calc ‖1 - grifE s‖ ≤ ‖(1 : ℂ)‖ + ‖grifE s‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, norm_grifE]; norm_num
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_comm]
  · have hs' : s ≠ ⌊s⌋₊ := by
      intro h; apply hg; rw [h, grifE_nat, sub_self]
    filter_upwards [grif_floor_eventually hs hs'] with s' h
    rw [h]

/-- The surjection `I → ` right earring, running its circles in turn. -/
def grifSigma : C(I, ℂ) := ⟨grifBlock grifSigmaF, continuous_grifBlock_sigma⟩

theorem grifSigma_zero : grifSigma 0 = 0 := by
  show grifBlock grifSigmaF 0 = 0
  rw [grifBlock_zero, grifSigmaF, grifCirc_of_eq_one]
  simpa using grifE_zero

theorem grifSigma_mem (t : I) : grifSigma t ∈ grifHEA := by
  show grifBlock grifSigmaF t ∈ grifHEA
  unfold grifBlock
  split_ifs
  · exact ⟨_, _, rfl⟩
  · exact zero_mem_grifHEA

theorem grifSigma_surj {q : ℂ} (hq : q ∈ grifHEA) : ∃ t, grifSigma t = q := by
  obtain ⟨n, θ, rfl⟩ := hq
  set φ := Int.fract θ
  have hφ0 : 0 ≤ φ := Int.fract_nonneg θ
  have hφ1 : φ < 1 := Int.fract_lt_one θ
  have hE : grifE (n + φ) = grifE θ := by
    rw [show (n : ℝ) + φ = θ + (((n : ℤ) - ⌊θ⌋ : ℤ) : ℝ) by
      simp only [φ, Int.fract]; push_cast; ring, grifE_add_int]
  set s : ℝ := n + φ
  have hs0 : 0 ≤ s := by positivity
  have hfl : ⌊s⌋₊ = n := by
    rw [Nat.floor_eq_iff hs0]; exact ⟨by simp [s, hφ0], by simp only [s]; linarith⟩
  refine ⟨⟨s / (1 + s), div_nonneg hs0 (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩,
    ?_⟩
  show grifBlock grifSigmaF _ = _
  have hlt : s / (1 + s) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs : s / (1 + s) / (1 - s / (1 + s)) = s := by
    field_simp; ring
  simp only [grifBlock, if_pos hlt, hs, grifSigmaF, hfl, grifCirc, hE]

theorem range_grifSigma : range grifSigma = grifHEA := by
  ext q
  exact ⟨fun ⟨t, ht⟩ => ht ▸ grifSigma_mem t, fun hq => grifSigma_surj hq⟩

theorem isCompact_grifHEA : IsCompact grifHEA := by
  rw [← range_grifSigma]; exact isCompact_range grifSigma.continuous

theorem isCompact_grifHEB : IsCompact grifHEB := by
  have : grifHEB = (fun q : ℂ => -q) '' grifHEA := by
    ext q; simp only [grifHEB, mem_setOf_eq, mem_image]
    exact ⟨fun h => ⟨-q, h, neg_neg q⟩, fun ⟨q', h, e⟩ => by rw [← e, neg_neg]; exact h⟩
  rw [this]; exact isCompact_grifHEA.image continuous_neg

theorem isCompact_grifK : IsCompact grifK := isCompact_grifHEA.union isCompact_grifHEB

/-! ### The loop `∏_{n ≥ N} a_n b_n` -/

/-- On `[n, n + 1/2]` the circle `a_{N+n}`, on `[n + 1/2, n + 1]` the circle `b_{N+n}`. -/
def grifOmegaF (N : ℕ) (s : ℝ) : ℂ :=
  (if s - ⌊s⌋₊ < 1 / 2 then 1 else -1) * grifCirc (N + ⌊s⌋₊) (2 * s)

theorem grifOmegaF_eq (N : ℕ) (s : ℝ) :
    grifOmegaF N s = (((if s - ⌊s⌋₊ < 1 / 2 then 1 else -1) / ((N : ℝ) + ⌊s⌋₊) : ℝ) : ℂ) *
      (1 - grifE (2 * s)) := by
  rw [grifOmegaF, grifCirc]; split_ifs <;> push_cast <;> ring

theorem continuous_grifBlock_omega {N : ℕ} (hN : 0 < N) :
    Continuous (grifBlock (grifOmegaF N)) := by
  have e : grifOmegaF N = fun s : ℝ => (((if s - ⌊s⌋₊ < 1 / 2 then 1 else -1) /
      ((N : ℝ) + ⌊s⌋₊) : ℝ) : ℂ) * (1 - grifE (2 * s)) := funext (grifOmegaF_eq N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [e]
  refine continuous_grifBlock (B := 2) (N := N) hN'
    (continuous_const.sub (continuous_grifE.comp (continuous_const.mul continuous_id)))
    (fun s => ?_) (fun s hs => ?_) (fun s hs hg => ?_)
  · calc ‖1 - grifE (2 * s)‖ ≤ ‖(1 : ℂ)‖ + ‖grifE (2 * s)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, norm_grifE]; norm_num
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < N + ⌊s⌋₊)]
    split_ifs <;> simp
  · have hs' : s ≠ ⌊s⌋₊ := by
      intro h; apply hg
      rw [h, show (2 : ℝ) * ⌊s⌋₊ = ((2 * ⌊s⌋₊ : ℕ) : ℝ) by push_cast; ring, grifE_nat, sub_self]
    have hhalf : s - ⌊s⌋₊ ≠ 1 / 2 := by
      intro h; apply hg
      rw [show 2 * s = ((2 * ⌊s⌋₊ + 1 : ℕ) : ℝ) by push_cast; linarith, grifE_nat, sub_self]
    have hkey : ∀ᶠ s' : ℝ in 𝓝 s, (s' - ⌊s⌋₊ < 1 / 2 ↔ s - ⌊s⌋₊ < 1 / 2) := by
      rcases lt_or_gt_of_ne hhalf with h | h
      · filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually
          (Iio_mem_nhds h)] with s' hs'
        exact ⟨fun _ => h, fun _ => hs'⟩
      · filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually
          (Ioi_mem_nhds h)] with s' hs'
        exact ⟨fun h' => absurd h' (not_lt.2 (le_of_lt hs')),
          fun h' => absurd h' (not_lt.2 (le_of_lt h))⟩
    filter_upwards [grif_floor_eventually hs hs', hkey] with s' h1 h2
    rw [h1]
    by_cases h : s - ⌊s⌋₊ < 1 / 2
    · rw [if_pos (h2.2 h), if_pos h]
    · rw [if_neg (fun h' => h (h2.1 h')), if_neg h]

theorem grifOmegaF_mem {N : ℕ} (hN : 0 < N) (s : ℝ) : grifOmegaF N s ∈ grifK := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have e : ((m + 1 : ℕ) : ℝ) + ⌊s⌋₊ = ((m + ⌊s⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [grifOmegaF]
  split_ifs
  · rw [one_mul, e]; exact Or.inl ⟨_, _, rfl⟩
  · rw [neg_one_mul, e]; refine Or.inr ?_
    simp only [grifHEB, mem_setOf_eq, neg_neg]; exact ⟨_, _, rfl⟩

theorem norm_grifOmegaF_le {N : ℕ} (hN : 0 < N) (s : ℝ) :
    ‖grifOmegaF N s‖ ≤ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [grifOmegaF, norm_mul]
  have h1 : ‖(if s - ⌊s⌋₊ < 1 / 2 then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [h1, one_mul]
  refine (norm_grifCirc_le (by positivity) _).trans ?_
  exact div_le_div_of_nonneg_left (by norm_num) hN'
    (by linarith [(Nat.cast_nonneg ⌊s⌋₊ : (0:ℝ) ≤ _)])

/-! ### The invariant of loops of the double earring -/

/-- The double earring as a space. -/
abbrev GrifK : Type := ↥grifK

/-- Its base point `0`. -/
def grifK0 : GrifK := ⟨0, zero_mem_grifK⟩

/-- `1 ∈ ℂ ∖ {0}`. -/
def grifOne : CStar := ⟨1, one_ne_zero⟩

theorem grif_ne_zero_of_norm {w : ℂ} (h : ‖w‖ = 1) : w ≠ 0 := by
  intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h

/-- The character `χ_{a_i}` of the double earring. -/
def grifChiAK (i : ℕ) : C(GrifK, CStar) :=
  ⟨fun q => ⟨grifChiA i q, grif_ne_zero_of_norm (norm_grifChiA q.2 i)⟩,
    ((continuous_grifChiA i).comp continuous_subtype_val).subtype_mk _⟩

/-- The character `χ_{b_j}` of the double earring. -/
def grifChiBK (j : ℕ) : C(GrifK, CStar) :=
  ⟨fun q => ⟨grifChiB j q, grif_ne_zero_of_norm (norm_grifChiB q.2 j)⟩,
    ((continuous_grifChiB j).comp continuous_subtype_val).subtype_mk _⟩

theorem grifChiAK_apply (i : ℕ) (q : GrifK) : (grifChiAK i q : ℂ) = grifChiA i q := rfl

theorem grifChiBK_apply (j : ℕ) (q : GrifK) : (grifChiBK j q : ℂ) = grifChiB j q := rfl

theorem grifChiAK_K0 (i : ℕ) : grifChiAK i grifK0 = cExp 0 :=
  Subtype.ext (by simp [grifChiAK_apply, grifK0, grifChiA_zero, cExp_apply])

/-- A lift through `exp`, from `0`, of a path of `ℂ ∖ {0}` from `1`. -/
def grifLog (p : C(I, CStar)) (h : (p 0 : ℂ) = 1) : C(I, ℂ) :=
  isCoveringMap_cExp.liftPath p 0 (Subtype.ext (by simp [cExp_apply, h]))

theorem grifLog_spec (p : C(I, CStar)) (h : (p 0 : ℂ) = 1) (t : I) :
    Complex.exp (grifLog p h t) = p t :=
  congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftPath_lifts p 0 _) t)

theorem grifLog_zero (p : C(I, CStar)) (h : (p 0 : ℂ) = 1) : grifLog p h 0 = 0 :=
  isCoveringMap_cExp.liftPath_zero ..

theorem grifLog_eq (p : C(I, CStar)) (h : (p 0 : ℂ) = 1) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = p t) (h0 : Γ 0 = 0) : grifLog p h = Γ :=
  ((isCoveringMap_cExp.eq_liftPath_iff' _).2 ⟨funext fun t => Subtype.ext (hΓ t), h0⟩).symm

/-- The lift through `exp`, from `0`, of `χ_{a_i} ∘ δ`. -/
def grifLiftA (δ : Path grifK0 grifK0) (i : ℕ) : C(I, ℂ) :=
  grifLog ((grifChiAK i).comp δ.toContinuousMap)
    (by
      show grifChiA i ((δ 0 : GrifK) : ℂ) = 1
      rw [δ.source, show ((grifK0 : GrifK) : ℂ) = 0 from rfl, grifChiA_zero])

theorem grifLiftA_spec (δ : Path grifK0 grifK0) (i : ℕ) (t : I) :
    Complex.exp (grifLiftA δ i t) = grifChiA i (δ t) :=
  grifLog_spec _ _ t

theorem grifLiftA_zero (δ : Path grifK0 grifK0) (i : ℕ) : grifLiftA δ i 0 = 0 :=
  grifLog_zero _ _

theorem grifLiftA_eq (δ : Path grifK0 grifK0) (i : ℕ) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = grifChiA i (δ t)) (h0 : Γ 0 = 0) : grifLiftA δ i = Γ :=
  grifLog_eq _ _ hΓ h0

/-- The integer level of a logarithm. -/
def grifLev (L : ℂ) : ℤ := round (L.im / (2 * Real.pi))

/-- `w ^ (level of L)`, and `1` where `w = 1`. -/
def grifPow (w L : ℂ) : ℂ := if w = 1 then 1 else w ^ grifLev L

theorem grifLev_int_mul_add (k : ℤ) (L : ℂ) :
    grifLev ((k : ℂ) * (2 * Real.pi * Complex.I) + L) = k + grifLev L := by
  unfold grifLev
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [show ((k : ℂ) * (2 * Real.pi * Complex.I) + L).im / (2 * Real.pi) =
    (k : ℝ) + L.im / (2 * Real.pi) by
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat]
      field_simp
      ring]
  exact round_intCast_add _ _

theorem grifLev_zero : grifLev 0 = 0 := by simp [grifLev]

theorem grifPow_ne_zero {w : ℂ} (hw : w ≠ 0) (L : ℂ) : grifPow w L ≠ 0 := by
  unfold grifPow; split_ifs
  · exact one_ne_zero
  · exact zpow_ne_zero _ hw

theorem grifPow_one (L : ℂ) : grifPow 1 L = 1 := by simp [grifPow]

theorem grif_norm_pow_sub_one_le {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) : ‖w ^ n - 1‖ ≤ n * ‖w - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖w ^ (n + 1) - 1‖ = ‖w ^ n * (w - 1) + (w ^ n - 1)‖ := by ring_nf
      _ ≤ ‖w ^ n * (w - 1)‖ + ‖w ^ n - 1‖ := norm_add_le _ _
      _ ≤ ‖w - 1‖ + n * ‖w - 1‖ := by
          rw [norm_mul, norm_pow, hw, one_pow, one_mul]; linarith
      _ = ((n + 1 : ℕ) : ℝ) * ‖w - 1‖ := by push_cast; ring

theorem grif_norm_zpow_sub_one_le {w : ℂ} (hw : ‖w‖ = 1) (k : ℤ) :
    ‖w ^ k - 1‖ ≤ |(k : ℝ)| * ‖w - 1‖ := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    simpa using grif_norm_pow_sub_one_le hw n
  · rw [zpow_neg, zpow_natCast]
    have hwn : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
    have hne : w ^ n ≠ 0 := grif_ne_zero_of_norm hwn
    calc ‖(w ^ n)⁻¹ - 1‖ = ‖(w ^ n - 1) / w ^ n‖ := by
          rw [norm_sub_rev]; congr 1; field_simp
      _ = ‖w ^ n - 1‖ := by rw [norm_div, hwn, div_one]
      _ ≤ n * ‖w - 1‖ := grif_norm_pow_sub_one_le hw n
      _ = |((-(n : ℤ) : ℤ) : ℝ)| * ‖w - 1‖ := by simp

theorem abs_grifLev_le (L : ℂ) : |(grifLev L : ℝ)| ≤ ‖L‖ / (2 * Real.pi) + 1 := by
  unfold grifLev
  have h1 := abs_sub_round (L.im / (2 * Real.pi))
  have h2 : |L.im / (2 * Real.pi)| ≤ ‖L‖ / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm L) (by positivity)
  have h3 := abs_sub_abs_le_abs_sub (round (L.im / (2 * Real.pi)) : ℝ) (L.im / (2 * Real.pi))
  rw [abs_sub_comm] at h1
  linarith

theorem grif_eq_of_exp_eq_one_of_dist {a b : ℂ} (ha : Complex.exp a = 1) (hb : Complex.exp b = 1)
    (h : dist a b < 2 * Real.pi) : a = b := by
  obtain ⟨k, rfl⟩ := Complex.exp_eq_one_iff.1 ha
  obtain ⟨m, rfl⟩ := Complex.exp_eq_one_iff.1 hb
  rw [dist_eq_norm, ← sub_mul, norm_mul, ← Int.cast_sub, Complex.norm_intCast,
    show ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]; simp] at h
  have : |((k - m : ℤ) : ℝ)| < 1 := by
    have hπ : 0 < 2 * Real.pi := by positivity
    nlinarith [abs_nonneg ((k - m : ℤ) : ℝ)]
  have : k - m = 0 := by
    rw [← Int.cast_abs] at this
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  rw [show k = m by omega]

/-- **Continuity of `grifPow`**: `w` of norm `1`, and `exp L = 1` wherever `w ≠ 1`. -/
theorem continuous_grifPow {X : Type*} [TopologicalSpace X] {w L : X → ℂ} (hw : Continuous w)
    (hL : Continuous L) (hw1 : ∀ x, ‖w x‖ = 1)
    (hint : ∀ x, w x ≠ 1 → Complex.exp (L x) = 1) :
    Continuous fun x => grifPow (w x) (L x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : w x = 1
  · have hval : grifPow (w x) (L x) = 1 := by simp [grifPow, hx]
    rw [ContinuousAt, hval, tendsto_iff_norm_sub_tendsto_zero]
    set C : ℝ := (‖L x‖ + 1) / (2 * Real.pi) + 1
    have hev : ∀ᶠ y in 𝓝 x, ‖L y‖ < ‖L x‖ + 1 :=
      (continuous_norm.comp hL).continuousAt.eventually
        (Iio_mem_nhds (by show ‖L x‖ < ‖L x‖ + 1; linarith))
    refine squeeze_zero' (g := fun y => C * ‖w y - 1‖)
      (Eventually.of_forall fun y => norm_nonneg _) ?_ ?_
    · filter_upwards [hev] with y hy
      unfold grifPow
      split_ifs with h
      · rw [sub_self, norm_zero]; positivity
      · refine (grif_norm_zpow_sub_one_le (hw1 y) _).trans ?_
        gcongr
        refine (abs_grifLev_le _).trans ?_
        have : ‖L y‖ / (2 * Real.pi) ≤ (‖L x‖ + 1) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right hy.le (by positivity)
        linarith
    · have hc : Continuous fun y => C * ‖w y - 1‖ :=
        continuous_const.mul (continuous_norm.comp (hw.sub continuous_const))
      have := hc.tendsto x
      simpa [hx] using this
  · have hev1 : ∀ᶠ y in 𝓝 x, w y ≠ 1 := hw.continuousAt.eventually_ne hx
    have hev2 : ∀ᶠ y in 𝓝 x, L y = L x := by
      filter_upwards [hev1, hL.continuousAt.eventually (Metric.ball_mem_nhds (L x)
            (by positivity : (0 : ℝ) < 2 * Real.pi))] with y hy1 hy2
      exact grif_eq_of_exp_eq_one_of_dist (hint y hy1) (hint x hx) hy2
    have hev3 : (fun y => grifPow (w y) (L y)) =ᶠ[𝓝 x] fun y => w y ^ grifLev (L x) := by
      filter_upwards [hev1, hev2] with y h1 h2
      simp [grifPow, h1, h2]
    refine ContinuousAt.congr ?_ hev3.symm
    exact hw.continuousAt.zpow₀ _ (Or.inl (grif_ne_zero_of_norm (hw1 x)))

/-- The loop `t ↦ χ_{b_j}(δ t) ^ (level of χ_{a_i} along δ at t)`. -/
def grifBeta (δ : Path grifK0 grifK0) (i j : ℕ) : Path grifOne grifOne where
  toFun t := ⟨grifPow (grifChiB j (δ t)) (grifLiftA δ i t),
    grifPow_ne_zero (grif_ne_zero_of_norm (norm_grifChiB (δ t).2 j)) _⟩
  continuous_toFun := (continuous_grifPow
    ((continuous_grifChiB j).comp (continuous_subtype_val.comp δ.continuous))
    (grifLiftA δ i).continuous (fun t => norm_grifChiB (δ t).2 j)
    (fun t ht => by
      rw [grifLiftA_spec]
      exact grifChiA_eq_one_of_grifChiB_ne (δ t).2 ht i)).subtype_mk _
  source' := Subtype.ext (by
    show grifPow (grifChiB j ((δ 0 : GrifK) : ℂ)) _ = 1
    rw [δ.source, show ((grifK0 : GrifK) : ℂ) = 0 from rfl, grifChiB_zero, grifPow_one])
  target' := Subtype.ext (by
    show grifPow (grifChiB j ((δ 1 : GrifK) : ℂ)) _ = 1
    rw [δ.target, show ((grifK0 : GrifK) : ℂ) = 0 from rfl, grifChiB_zero, grifPow_one])

theorem grifBeta_apply (δ : Path grifK0 grifK0) (i j : ℕ) (t : I) :
    (grifBeta δ i j t : ℂ) = grifPow (grifChiB j (δ t)) (grifLiftA δ i t) := rfl

/-- **The linking matrix** `Z_{ij}(δ)`: the winding of `grifBeta`. -/
def grifZ (δ : Path grifK0 grifK0) (i j : ℕ) : ℤ := cWinding (grifBeta δ i j)

/-- The winding of `δ` around `a_i`. -/
def grifWA (δ : Path grifK0 grifK0) (i : ℕ) : ℤ := cWinding (δ.map (grifChiAK i).continuous)

/-- The winding of `δ` around `b_j`. -/
def grifWB (δ : Path grifK0 grifK0) (j : ℕ) : ℤ := cWinding (δ.map (grifChiBK j).continuous)

/-! #### Concatenating lifts -/

/-- `f`, then `g` translated to start at `f 1`. -/
def grifCat (f g : C(I, ℂ)) : C(I, ℂ) :=
  ((⟨f, rfl, rfl⟩ : Path (f 0) (f 1)).trans
    (⟨⟨fun t => f 1 + (g t - g 0), by fun_prop⟩, by simp, rfl⟩ :
      Path (f 1) (f 1 + (g 1 - g 0)))).toContinuousMap

theorem grifCat_apply_le (f g : C(I, ℂ)) (t : I) (h : (t : ℝ) ≤ 1 / 2) :
    grifCat f g t = f ⟨2 * t, by constructor <;> linarith [t.2.1]⟩ := by
  simp only [grifCat, Path.coe_toContinuousMap, Path.trans_apply, dif_pos h]
  rfl

theorem grifCat_apply_gt (f g : C(I, ℂ)) (t : I) (h : 1 / 2 < (t : ℝ)) :
    grifCat f g t = f 1 + (g ⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩ - g 0) := by
  simp only [grifCat, Path.coe_toContinuousMap, Path.trans_apply, dif_neg (not_le.2 h)]
  rfl

theorem grifCat_zero (f g : C(I, ℂ)) : grifCat f g 0 = f 0 := by
  simp only [grifCat, Path.coe_toContinuousMap, Path.source]

theorem grifCat_one (f g : C(I, ℂ)) : grifCat f g 1 = f 1 + (g 1 - g 0) := by
  simp only [grifCat, Path.coe_toContinuousMap, Path.target]

theorem grif_trans_apply_le {X : Type*} [TopologicalSpace X] {a b c : X} (γ : Path a b)
    (γ' : Path b c) (t : I) (h : (t : ℝ) ≤ 1 / 2) :
    (γ.trans γ') t = γ ⟨2 * t, by constructor <;> linarith [t.2.1]⟩ := by
  rw [Path.trans_apply, dif_pos h]

theorem grif_trans_apply_gt {X : Type*} [TopologicalSpace X] {a b c : X} (γ : Path a b)
    (γ' : Path b c) (t : I) (h : 1 / 2 < (t : ℝ)) :
    (γ.trans γ') t = γ' ⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩ := by
  rw [Path.trans_apply, dif_neg (not_le.2 h)]

theorem grifCat_le (f g : C(I, ℂ)) {t u : I} (h : (t : ℝ) ≤ 1 / 2) (hu : (u : ℝ) = 2 * t) :
    grifCat f g t = f u := by
  rw [grifCat_apply_le f g t h]; exact congrArg f (Subtype.ext hu.symm)

theorem grifCat_gt (f g : C(I, ℂ)) {t u : I} (h : 1 / 2 < (t : ℝ)) (hu : (u : ℝ) = 2 * t - 1) :
    grifCat f g t = f 1 + (g u - g 0) := by
  rw [grifCat_apply_gt f g t h]; congr 2; exact congrArg g (Subtype.ext hu.symm)

theorem grif_trans_le {X : Type*} [TopologicalSpace X] {a b c : X} (γ : Path a b)
    (γ' : Path b c) {t u : I} (h : (t : ℝ) ≤ 1 / 2) (hu : (u : ℝ) = 2 * t) :
    (γ.trans γ') t = γ u := by
  rw [grif_trans_apply_le γ γ' t h]; exact congrArg γ (Subtype.ext hu.symm)

theorem grif_trans_gt {X : Type*} [TopologicalSpace X] {a b c : X} (γ : Path a b)
    (γ' : Path b c) {t u : I} (h : 1 / 2 < (t : ℝ)) (hu : (u : ℝ) = 2 * t - 1) :
    (γ.trans γ') t = γ' u := by
  rw [grif_trans_apply_gt γ γ' t h]; exact congrArg γ' (Subtype.ext hu.symm)

theorem grif_exists_double (t : I) (h : (t : ℝ) ≤ 1 / 2) : ∃ u : I, (u : ℝ) = 2 * t :=
  ⟨⟨2 * t, by constructor <;> linarith [t.2.1]⟩, rfl⟩

theorem grif_exists_double_sub (t : I) (h : 1 / 2 < (t : ℝ)) : ∃ u : I, (u : ℝ) = 2 * t - 1 :=
  ⟨⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩, rfl⟩

theorem grif_exp_int_mul (k : ℤ) : Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
  Complex.exp_int_mul_two_pi_mul_I k

theorem grifBeta_zero_val (δ : Path grifK0 grifK0) (i j : ℕ) :
    ((grifBeta δ i j 0 : CStar) : ℂ) = 1 := by
  rw [(grifBeta δ i j).source]; rfl

/-- **The linking matrix is a crossed homomorphism**: `Z(δ₁δ₂) = Z(δ₁) + Z(δ₂) + x(δ₁) y(δ₂)ᵀ`. -/
theorem grifZ_trans (δ₁ δ₂ : Path grifK0 grifK0) (i j : ℕ) :
    grifZ (δ₁.trans δ₂) i j = grifZ δ₁ i j + grifZ δ₂ i j + grifWA δ₁ i * grifWB δ₂ j := by
  set Γ₁ := grifLiftA δ₁ i
  set Γ₂ := grifLiftA δ₂ i
  set x := grifWA δ₁ i
  set y := grifWB δ₂ j
  have hx : Γ₁ 1 = (x : ℂ) * (2 * Real.pi * Complex.I) := by
    have := cWinding_spec (δ₁.map (grifChiAK i).continuous) (Γ := Γ₁)
      (fun t => grifLiftA_spec δ₁ i t)
    rwa [grifLiftA_zero, zero_add] at this
  have hL : grifLiftA (δ₁.trans δ₂) i = grifCat Γ₁ Γ₂ := by
    refine grifLiftA_eq _ _ (fun t => ?_) ?_
    · by_cases h : (t : ℝ) ≤ 1 / 2
      · obtain ⟨u, hu⟩ := grif_exists_double t h
        rw [grifCat_le _ _ h hu, grif_trans_le _ _ h hu, grifLiftA_spec]
      · obtain ⟨u, hu⟩ := grif_exists_double_sub t (not_le.1 h)
        rw [grifCat_gt _ _ (not_le.1 h) hu, grif_trans_gt _ _ (not_le.1 h) hu,
          grifLiftA_zero, sub_zero, Complex.exp_add, hx, grif_exp_int_mul, one_mul,
          grifLiftA_spec]
    · rw [grifCat_zero]; exact grifLiftA_zero δ₁ i
  set β₁ := grifBeta δ₁ i j
  set β₂ := grifBeta δ₂ i j
  set Λ₁ := grifLog β₁.toContinuousMap (grifBeta_zero_val δ₁ i j)
  set Λ₂ := grifLog β₂.toContinuousMap (grifBeta_zero_val δ₂ i j)
  have hM0 : (((grifChiBK j).comp δ₂.toContinuousMap) 0 : ℂ) = 1 := by
    show grifChiB j ((δ₂ 0 : GrifK) : ℂ) = 1
    rw [δ₂.source, show ((grifK0 : GrifK) : ℂ) = 0 from rfl, grifChiB_zero]
  set M := grifLog ((grifChiBK j).comp δ₂.toContinuousMap) hM0
  have hΛ₁ : Λ₁ 1 = (grifZ δ₁ i j : ℂ) * (2 * Real.pi * Complex.I) := by
    have := cWinding_spec β₁ (Γ := Λ₁) (fun t => grifLog_spec _ _ t)
    rwa [grifLog_zero, zero_add] at this
  have hΛ₂ : Λ₂ 1 = (grifZ δ₂ i j : ℂ) * (2 * Real.pi * Complex.I) := by
    have := cWinding_spec β₂ (Γ := Λ₂) (fun t => grifLog_spec _ _ t)
    rwa [grifLog_zero, zero_add] at this
  have hM : M 1 = (y : ℂ) * (2 * Real.pi * Complex.I) := by
    have := cWinding_spec (δ₂.map (grifChiBK j).continuous) (Γ := M)
      (fun t => grifLog_spec _ _ t)
    rwa [grifLog_zero, zero_add] at this
  set g : C(I, ℂ) := ⟨fun t => Λ₂ t + (x : ℂ) * M t, by fun_prop⟩
  have hg0 : g 0 = 0 := by
    show Λ₂ 0 + (x : ℂ) * M 0 = 0
    rw [grifLog_zero, grifLog_zero, mul_zero, add_zero]
  refine cWinding_eq _ (Γ := grifCat Λ₁ g) (fun t => ?_) ?_
  · rw [grifBeta_apply, hL]
    by_cases h : (t : ℝ) ≤ 1 / 2
    · obtain ⟨u, hu⟩ := grif_exists_double t h
      rw [grifCat_le _ _ h hu, grifCat_le _ _ h hu, grif_trans_le _ _ h hu, grifLog_spec]
      rfl
    · obtain ⟨u, hu⟩ := grif_exists_double_sub t (not_le.1 h)
      rw [grifCat_gt _ _ (not_le.1 h) hu, grifCat_gt _ _ (not_le.1 h) hu,
        grif_trans_gt _ _ (not_le.1 h) hu, hg0, sub_zero, grifLiftA_zero, sub_zero, hx]
      have e1 : Complex.exp (Λ₁ 1) = 1 := by
        rw [grifLog_spec]; show ((β₁ 1 : CStar) : ℂ) = 1; rw [β₁.target]; rfl
      have e2 : Complex.exp (Λ₂ u) = grifPow (grifChiB j (δ₂ u)) (Γ₂ u) := grifLog_spec _ _ u
      have e3 : Complex.exp (M u) = grifChiB j (δ₂ u) := grifLog_spec _ _ u
      show Complex.exp (Λ₁ 1 + (Λ₂ u + (x : ℂ) * M u)) = _
      rw [Complex.exp_add, Complex.exp_add, e1, one_mul, e2, Complex.exp_int_mul, e3]
      unfold grifPow
      by_cases hw : grifChiB j (δ₂ u) = 1
      · simp [hw]
      · rw [if_neg hw, if_neg hw, grifLev_int_mul_add, add_comm (x : ℤ),
          zpow_add₀ (grif_ne_zero_of_norm (norm_grifChiB (δ₂ u).2 j))]
  · rw [grifCat_one, grifCat_zero, grifLog_zero, hg0, sub_zero]
    show Λ₁ 1 + (Λ₂ 1 + (x : ℂ) * M 1) = _
    rw [hΛ₁, hΛ₂, hM]
    push_cast
    ring

/-- A loop of `ℂ ∖ {0}` at `1` with constant value `1` has winding number `0`. -/
theorem grif_cWinding_of_eq_one (β : Path grifOne grifOne) (h : ∀ t, (β t : ℂ) = 1) :
    cWinding β = 0 := by
  refine cWinding_eq β (Γ := ContinuousMap.const I 0) (fun t => by simp [h t]) ?_
  simp

/-- **Homotopy invariance of the linking matrix.** -/
theorem grifZ_homotopic {δ δ' : Path grifK0 grifK0} (h : δ.Homotopic δ') (i j : ℕ) :
    grifZ δ i j = grifZ δ' i j := by
  obtain ⟨F⟩ := h
  set H : C(I × I, CStar) := (grifChiAK i).comp F.toContinuousMap
  have H0 : ∀ t, H (0, t) = cExp (grifLiftA δ i t) := fun t => Subtype.ext (by
    show grifChiA i ((F (0, t) : GrifK) : ℂ) = Complex.exp (grifLiftA δ i t)
    rw [F.apply_zero, grifLiftA_spec]; rfl)
  set L := isCoveringMap_cExp.liftHomotopy H (grifLiftA δ i) H0
  have hLs : ∀ p, Complex.exp (L p) = grifChiA i (F p) := fun p =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts H _ H0) p)
  have hL0 : ∀ t, L (0, t) = grifLiftA δ i t := isCoveringMap_cExp.liftHomotopy_zero H _ H0
  have hLs0 : ∀ s, L (s, 0) = 0 := by
    have := isCoveringMap_cExp.eq_of_comp_eq (g₁ := fun s : I => L (s, 0))
      (g₂ := fun _ => (0 : ℂ)) (by fun_prop) continuous_const
      (funext fun s => Subtype.ext (by
        show Complex.exp (L (s, 0)) = Complex.exp 0
        rw [hLs, Complex.exp_zero, F.source]
        exact grifChiA_zero i)) 0 (by simp only [hL0, grifLiftA_zero])
    exact congrFun this
  have hLs1 : ∀ s, L (s, 1) = L (0, 1) := by
    have := isCoveringMap_cExp.eq_of_comp_eq (g₁ := fun s : I => L (s, 1))
      (g₂ := fun _ => L (0, 1)) (by fun_prop) continuous_const
      (funext fun s => Subtype.ext (by
        show Complex.exp (L (s, 1)) = Complex.exp (L (0, 1))
        rw [hLs, hLs, F.target, F.target])) 0 rfl
    exact congrFun this
  have hL1 : ∀ t, L (1, t) = grifLiftA δ' i t := by
    have := grifLiftA_eq δ' i (Γ := ⟨fun t => L (1, t), by fun_prop⟩)
      (fun t => by show Complex.exp (L (1, t)) = _; rw [hLs, F.apply_one]; rfl) (hLs0 1)
    intro t
    rw [this]; rfl
  have hint : ∀ p, grifChiB j (F p) ≠ 1 → Complex.exp (L p) = 1 := fun p hp => by
    rw [hLs]; exact grifChiA_eq_one_of_grifChiB_ne (F p).2 hp i
  have hcont : Continuous fun p : I × I => grifPow (grifChiB j (F p)) (L p) :=
    continuous_grifPow ((continuous_grifChiB j).comp (continuous_subtype_val.comp F.continuous))
      L.continuous (fun p => norm_grifChiB (F p).2 j) hint
  have hend : ∀ s : I, ∀ t ∈ ({0, 1} : Set I),
      grifPow (grifChiB j (F (s, t))) (L (s, t)) = 1 := by
    intro s t ht
    rcases ht with rfl | rfl
    · rw [F.source]; show grifPow (grifChiB j 0) _ = 1; rw [grifChiB_zero]; exact grifPow_one _
    · rw [F.target]; show grifPow (grifChiB j 0) _ = 1; rw [grifChiB_zero]; exact grifPow_one _
  refine cWinding_homotopic ⟨{
    toFun := fun p => ⟨grifPow (grifChiB j (F p)) (L p),
      grifPow_ne_zero (grif_ne_zero_of_norm (norm_grifChiB (F p).2 j)) _⟩
    continuous_toFun := hcont.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by
      show grifPow (grifChiB j (F (0, t))) (L (0, t)) = _
      rw [F.apply_zero, hL0]; rfl)
    map_one_left := fun t => Subtype.ext (by
      show grifPow (grifChiB j (F (1, t))) (L (1, t)) = _
      rw [F.apply_one, hL1]; rfl)
    prop' := fun s t ht => by
      refine Subtype.ext ?_
      show grifPow (grifChiB j (F (s, t))) (L (s, t)) = ((grifBeta δ i j t : CStar) : ℂ)
      rw [hend s t ht]
      rcases ht with rfl | rfl
      · rw [(grifBeta δ i j).source]; rfl
      · rw [(grifBeta δ i j).target]; rfl }⟩

/-- On a loop of the right earring the linking matrix vanishes. -/
theorem grifZ_of_HEA {δ : Path grifK0 grifK0} (hδ : ∀ t, (δ t : ℂ) ∈ grifHEA) (i j : ℕ) :
    grifZ δ i j = 0 :=
  grif_cWinding_of_eq_one _ fun t => by
    rw [grifBeta_apply, grifChiB_of_mem_grifHEA (hδ t), grifPow_one]

/-- On a loop of the left earring the linking matrix vanishes. -/
theorem grifZ_of_HEB {δ : Path grifK0 grifK0} (hδ : ∀ t, (δ t : ℂ) ∈ grifHEB) (i j : ℕ) :
    grifZ δ i j = 0 := by
  have hL : grifLiftA δ i = ContinuousMap.const I 0 :=
    grifLiftA_eq δ i (fun t => by simp [grifChiA_of_mem_grifHEB (hδ t)]) rfl
  refine grif_cWinding_of_eq_one _ fun t => ?_
  rw [grifBeta_apply, hL, ContinuousMap.const_apply]
  unfold grifPow
  split_ifs
  · rfl
  · rw [grifLev_zero, zpow_zero]

/-! #### Modulo finite rank -/

/-- The integer matrices of finite rank. -/
def grifFR : AddSubgroup (ℕ → ℕ → ℤ) :=
  AddSubgroup.closure {Z | ∃ u v : ℕ → ℤ, Z = fun i j => u i * v j}

/-- Integer matrices modulo those of finite rank. -/
abbrev GrifQ : Type := (ℕ → ℕ → ℤ) ⧸ grifFR

/-- **The invariant**: the linking matrix modulo finite rank. -/
def grifTheta (δ : Path grifK0 grifK0) : Multiplicative GrifQ :=
  Multiplicative.ofAdd (QuotientAddGroup.mk fun i j => grifZ δ i j)

theorem grifTheta_trans (δ₁ δ₂ : Path grifK0 grifK0) :
    grifTheta (δ₁.trans δ₂) = grifTheta δ₁ * grifTheta δ₂ := by
  unfold grifTheta
  rw [← ofAdd_add, ← QuotientAddGroup.mk_add]
  congr 1
  refine (QuotientAddGroup.eq).2 ((grifFR.neg_mem_iff).1 ?_)
  refine AddSubgroup.subset_closure ⟨fun i => grifWA δ₁ i, fun j => grifWB δ₂ j, ?_⟩
  funext i j
  simp only [Pi.add_apply, Pi.neg_apply, grifZ_trans]
  ring

theorem grifTheta_homotopic {δ δ' : Path grifK0 grifK0} (h : δ.Homotopic δ') :
    grifTheta δ = grifTheta δ' := by
  unfold grifTheta
  congr 2
  funext i j
  exact grifZ_homotopic h i j

theorem grifTheta_of_HEA {δ : Path grifK0 grifK0} (hδ : ∀ t, (δ t : ℂ) ∈ grifHEA) :
    grifTheta δ = 1 := by
  unfold grifTheta
  rw [show (fun i j => grifZ δ i j) = 0 from funext fun i => funext fun j => grifZ_of_HEA hδ i j]
  rfl

theorem grifTheta_of_HEB {δ : Path grifK0 grifK0} (hδ : ∀ t, (δ t : ℂ) ∈ grifHEB) :
    grifTheta δ = 1 := by
  unfold grifTheta
  rw [show (fun i j => grifZ δ i j) = 0 from funext fun i => funext fun j => grifZ_of_HEB hδ i j]
  rfl

theorem grif_mem_FR_iff_sum {Z : ℕ → ℕ → ℤ} (h : Z ∈ grifFR) :
    ∃ r : ℕ, ∃ u v : Fin r → ℕ → ℤ, Z = fun i j => ∑ k, u k i * v k j := by
  induction h using AddSubgroup.closure_induction with
  | mem Z hZ =>
    obtain ⟨u, v, rfl⟩ := hZ
    exact ⟨1, fun _ => u, fun _ => v, by funext i j; simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by funext i j; simp⟩
  | add Z₁ Z₂ _ _ h₁ h₂ =>
    obtain ⟨r₁, u₁, v₁, rfl⟩ := h₁
    obtain ⟨r₂, u₂, v₂, rfl⟩ := h₂
    refine ⟨r₁ + r₂, Fin.append u₁ u₂, Fin.append v₁ v₂, ?_⟩
    funext i j
    simp [Fin.sum_univ_add]
  | neg Z _ h =>
    obtain ⟨r, u, v, rfl⟩ := h
    exact ⟨r, fun k => -u k, v, by funext i j; simp [Finset.sum_neg_distrib]⟩

/-- **An infinite unitriangular block is not of finite rank.** -/
theorem grif_not_mem_FR {N : ℕ} {Z : ℕ → ℕ → ℤ}
    (hZ : ∀ i j, N ≤ i → N ≤ j → Z i j = if i ≤ j then 1 else 0) : Z ∉ grifFR := by
  intro h
  obtain ⟨r, u, v, hZr⟩ := grif_mem_FR_iff_sum h
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℚ := Matrix.of fun a b => (Z (N + a) (N + b) : ℚ)
  let U : Matrix (Fin (r + 1)) (Fin r) ℚ := Matrix.of fun a k => (u k (N + a) : ℚ)
  let V : Matrix (Fin r) (Fin (r + 1)) ℚ := Matrix.of fun k b => (v k (N + b) : ℚ)
  have hAUV : A = U * V := by
    ext a b
    simp only [A, U, V, Matrix.of_apply, Matrix.mul_apply, hZr]
    push_cast
    rfl
  have hrank : A.rank ≤ r := by
    rw [hAUV]; exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)
  have hval : ∀ a b : Fin (r + 1), A a b = if (a : ℕ) ≤ b then 1 else 0 := by
    intro a b
    simp only [A, Matrix.of_apply, hZ _ _ (Nat.le_add_right N a) (Nat.le_add_right N b)]
    split_ifs <;> first | rfl | omega
  have htri : A.BlockTriangular id := by
    intro a b hab
    rw [hval, if_neg]
    exact not_le.2 (by simpa using hab)
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun a _ => by rw [hval, if_pos le_rfl]
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (by rw [hdet]; exact isUnit_one)
  have := Matrix.rank_of_isUnit A hunit
  rw [Fintype.card_fin] at this
  omega

/-! #### The invariant of `∏_{n ≥ N} a_n b_n` -/

/-- The loop `∏_{n ≥ N} a_n b_n` of the double earring, `N ≥ 1`. -/
def grifOmegaK (N : ℕ) (hN : 0 < N) : Path grifK0 grifK0 where
  toFun t := ⟨grifBlock (grifOmegaF N) t, by
    unfold grifBlock; split_ifs
    · exact grifOmegaF_mem hN _
    · exact zero_mem_grifK⟩
  continuous_toFun := (continuous_grifBlock_omega hN).subtype_mk _
  source' := Subtype.ext (by
    show grifBlock (grifOmegaF N) 0 = 0
    rw [grifBlock_zero, grifOmegaF, grifCirc_of_eq_one (by simpa using grifE_zero), mul_zero])
  target' := Subtype.ext (grifBlock_one _)

theorem grifOmegaK_val {N : ℕ} (hN : 0 < N) {t : I} (ht : (t : ℝ) < 1) :
    ((grifOmegaK N hN t : GrifK) : ℂ) = grifOmegaF N ((t : ℝ) / (1 - t)) := by
  show grifBlock (grifOmegaF N) t = _
  simp only [grifBlock, if_pos ht]

theorem grifOmegaK_one {N : ℕ} (hN : 0 < N) : ((grifOmegaK N hN 1 : GrifK) : ℂ) = 0 :=
  grifBlock_one _

theorem norm_grifOmegaK_le {N : ℕ} (hN : 0 < N) (t : I) :
    ‖((grifOmegaK N hN t : GrifK) : ℂ)‖ ≤ 2 / N := by
  show ‖grifBlock (grifOmegaF N) t‖ ≤ 2 / N
  unfold grifBlock
  split_ifs
  · exact norm_grifOmegaF_le hN _
  · rw [norm_zero]; positivity

/-- `x ↦ max 0 (min 1 x)`. -/
def grifClamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem continuous_grifClamp : Continuous grifClamp := by unfold grifClamp; fun_prop

theorem grifClamp_of_nonpos {x : ℝ} (h : x ≤ 0) : grifClamp x = 0 := by
  unfold grifClamp; rw [max_eq_left]; exact (min_le_right _ _).trans h

theorem grifClamp_of_one_le {x : ℝ} (h : 1 ≤ x) : grifClamp x = 1 := by
  unfold grifClamp; rw [min_eq_left h, max_eq_right zero_le_one]

theorem grifClamp_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : grifClamp x = x := by
  unfold grifClamp; rw [min_eq_right h1, max_eq_right h0]

/-- The progress along the half-line, from `c` on: `clamp(2(s - c))`, `s = t/(1-t)`. -/
def grifProg (c : ℝ) (t : I) : ℝ :=
  if (t : ℝ) < 1 then grifClamp (2 * ((t : ℝ) / (1 - t) - c)) else 1

theorem continuous_grifProg (c : ℝ) : Continuous (grifProg c) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
  · have hev : grifProg c =ᶠ[𝓝 t] fun t : I => grifClamp (2 * ((t : ℝ) / (1 - t) - c)) := by
      filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds ht]
        with t' ht'
      simp only [grifProg, if_pos (show (t' : ℝ) < 1 from ht')]
    refine ContinuousAt.congr ?_ hev.symm
    exact continuous_grifClamp.continuousAt.comp (continuousAt_const.mul
      (((continuous_subtype_val.continuousAt).div
        (continuous_const.sub continuous_subtype_val).continuousAt (by linarith)).sub
        continuousAt_const))
  · have ht1 : t = 1 := Subtype.ext ht
    subst ht1
    set M : ℝ := max c 0 + 1
    have hM : 0 < M := by positivity
    have hlt : M / (M + 1) < ((1 : I) : ℝ) := by
      rw [Set.Icc.coe_one, div_lt_one (by positivity)]; linarith
    have hev : grifProg c =ᶠ[𝓝 1] fun _ => 1 := by
      filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hlt]
        with t' ht'
      unfold grifProg
      split_ifs with h1
      · have hpos : 0 < 1 - (t' : ℝ) := by linarith
        have hs : M ≤ (t' : ℝ) / (1 - t') := by
          rw [le_div_iff₀ hpos]
          have := (div_lt_iff₀ (by positivity : (0 : ℝ) < M + 1)).1 ht'
          nlinarith
        exact grifClamp_of_one_le (by have := le_max_left c 0; linarith)
      · rfl
    have h1 : grifProg c 1 = 1 := by simp [grifProg]
    rw [ContinuousAt, h1]
    exact tendsto_const_nhds.congr' hev.symm

theorem grifProg_zero {c : ℝ} (hc : 0 ≤ c) : grifProg c 0 = 0 := by
  simp only [grifProg, Set.Icc.coe_zero, zero_lt_one, if_true, sub_zero, div_one, zero_sub]
  exact grifClamp_of_nonpos (by linarith)

theorem grifProg_one (c : ℝ) : grifProg c 1 = 1 := by simp [grifProg]

theorem grifProg_of_lt {c : ℝ} {t : I} (ht : (t : ℝ) < 1) :
    grifProg c t = grifClamp (2 * ((t : ℝ) / (1 - t) - c)) := by
  simp [grifProg, ht]

theorem grifLev_real_mul (p : ℝ) : grifLev ((p : ℂ) * (2 * Real.pi * Complex.I)) = round p := by
  unfold grifLev
  congr 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  field_simp
  ring

theorem grif_floor_facts {s : ℝ} (hs : 0 ≤ s) : (⌊s⌋₊ : ℝ) ≤ s ∧ s < ⌊s⌋₊ + 1 :=
  ⟨Nat.floor_le hs, Nat.lt_floor_add_one s⟩

/-- The `i`-th right character along `∏ a_n b_n`, in terms of the progress. -/
theorem grifChiA_omegaF {N i : ℕ} (hN : 0 < N) (hi : N ≤ i) {s : ℝ} (hs : 0 ≤ s) :
    grifChiA i (grifOmegaF N s) = grifE (grifClamp (2 * (s - ((i - N : ℕ) : ℝ)))) := by
  obtain ⟨hn1, hn2⟩ := grif_floor_facts hs
  set n := ⌊s⌋₊ with hn
  set k := i - N with hk
  have hik : i = N + k := by omega
  have hNn : 0 < N + n := by omega
  rw [grifOmegaF, show ((N : ℝ) + ⌊s⌋₊) = ((N + n : ℕ) : ℝ) by push_cast; ring]
  split_ifs with hφ
  · rw [one_mul, grifChiA_circ hNn]
    split_ifs with h
    · have hkn : k = n := by omega
      rw [hkn, grifClamp_of_mem (by linarith) (by linarith),
        show 2 * (s - (n : ℝ)) = 2 * s - ((2 * n : ℕ) : ℤ) by push_cast; ring, grifE_sub_int]
    · rcases lt_or_gt_of_ne (show k ≠ n by omega) with hkn | hkn
      · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
        rw [grifClamp_of_one_le (by linarith), grifE_one]
      · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hkn
        rw [grifClamp_of_nonpos (by linarith), grifE_zero]
  · rw [neg_one_mul, grifChiA_neg_circ hNn]
    rcases le_or_gt k n with hkn | hkn
    · have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      rw [grifClamp_of_one_le (by rw [not_lt] at hφ; linarith), grifE_one]
    · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hkn
      rw [grifClamp_of_nonpos (by linarith), grifE_zero]

/-- The `j`-th left character along `∏ a_n b_n`, in terms of the progress. -/
theorem grifChiB_omegaF {N j : ℕ} (hN : 0 < N) (hj : N ≤ j) {s : ℝ} (hs : 0 ≤ s) :
    grifChiB j (grifOmegaF N s) =
      grifE (grifClamp (2 * (s - (((j - N : ℕ) : ℝ) + 1 / 2)))) := by
  obtain ⟨hn1, hn2⟩ := grif_floor_facts hs
  set n := ⌊s⌋₊ with hn
  set k := j - N with hk
  have hjk : j = N + k := by omega
  have hNn : 0 < N + n := by omega
  rw [grifOmegaF, show ((N : ℝ) + ⌊s⌋₊) = ((N + n : ℕ) : ℝ) by push_cast; ring]
  split_ifs with hφ
  · rw [one_mul, grifChiB_circ hNn]
    rcases lt_or_ge k n with hkn | hkn
    · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      rw [grifClamp_of_one_le (by linarith), grifE_one]
    · have : (n : ℝ) ≤ k := by exact_mod_cast hkn
      rw [grifClamp_of_nonpos (by linarith), grifE_zero]
  · rw [not_lt] at hφ
    rw [neg_one_mul, grifChiB_neg_circ hNn]
    split_ifs with h
    · have hkn : k = n := by omega
      rw [hkn, grifClamp_of_mem (by linarith) (by linarith),
        show 2 * (s - ((n : ℝ) + 1 / 2)) = 2 * s - ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
        grifE_sub_int]
    · rcases lt_or_gt_of_ne (show k ≠ n by omega) with hkn | hkn
      · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
        rw [grifClamp_of_one_le (by linarith), grifE_one]
      · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hkn
        rw [grifClamp_of_nonpos (by linarith), grifE_zero]

theorem grifLiftA_omega {N i : ℕ} (hN : 0 < N) (hi : N ≤ i) :
    grifLiftA (grifOmegaK N hN) i =
      ⟨fun t => (grifProg ((i - N : ℕ) : ℝ) t : ℂ) * (2 * Real.pi * Complex.I),
        by have := continuous_grifProg ((i - N : ℕ) : ℝ); fun_prop⟩ := by
  refine grifLiftA_eq _ _ (fun t => ?_) ?_
  · show Complex.exp ((grifProg _ t : ℂ) * (2 * Real.pi * Complex.I)) = _
    rw [← grifE_eq_exp]
    rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
    · rw [grifOmegaK_val hN ht, grifProg_of_lt ht, grifChiA_omegaF hN hi (grif_s_nonneg t)]
    · have ht1 : t = 1 := Subtype.ext ht
      subst ht1
      rw [grifOmegaK_one, grifProg_one, grifE_one, grifChiA_zero]
  · show (grifProg _ 0 : ℂ) * _ = 0
    rw [grifProg_zero (Nat.cast_nonneg _), Complex.ofReal_zero, zero_mul]

theorem grifChiB_omegaK {N j : ℕ} (hN : 0 < N) (hj : N ≤ j) (t : I) :
    grifChiB j ((grifOmegaK N hN t : GrifK) : ℂ) =
      grifE (grifProg (((j - N : ℕ) : ℝ) + 1 / 2) t) := by
  rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
  · rw [grifOmegaK_val hN ht, grifProg_of_lt ht, grifChiB_omegaF hN hj (grif_s_nonneg t)]
  · have ht1 : t = 1 := Subtype.ext ht
    subst ht1
    rw [grifOmegaK_one, grifProg_one, grifE_one, grifChiB_zero]

/-- **The linking matrix of `∏_{n ≥ N} a_n b_n`** is the unitriangular one on `[N, ∞)²`. -/
theorem grifZ_omega {N i j : ℕ} (hN : 0 < N) (hi : N ≤ i) (hj : N ≤ j) :
    grifZ (grifOmegaK N hN) i j = if i ≤ j then 1 else 0 := by
  have hβ : ∀ t, (grifBeta (grifOmegaK N hN) i j t : ℂ) =
      if i ≤ j then grifChiB j ((grifOmegaK N hN t : GrifK) : ℂ) else 1 := by
    intro t
    rw [grifBeta_apply, grifLiftA_omega hN hi]
    show grifPow _ ((grifProg _ t : ℂ) * (2 * Real.pi * Complex.I)) = _
    by_cases hw : grifChiB j ((grifOmegaK N hN t : GrifK) : ℂ) = 1
    · rw [hw, grifPow_one]; split_ifs <;> rfl
    · have ht : (t : ℝ) < 1 := by
        rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
        · exact ht
        · exfalso; apply hw
          rw [show t = 1 from Subtype.ext ht, grifOmegaK_one, grifChiB_zero]
      have hw' := hw
      rw [grifChiB_omegaK hN hj, grifProg_of_lt ht] at hw'
      set s := (t : ℝ) / (1 - t)
      have hs1 : ((j - N : ℕ) : ℝ) + 1 / 2 < s := by
        by_contra h
        exact hw' (by rw [grifClamp_of_nonpos (by linarith), grifE_zero])
      have hs2 : s < ((j - N : ℕ) : ℝ) + 1 := by
        by_contra h
        exact hw' (by rw [grifClamp_of_one_le (by linarith), grifE_one])
      unfold grifPow
      rw [if_neg hw, grifLev_real_mul, grifProg_of_lt ht]
      split_ifs with hij
      · have : ((i - N : ℕ) : ℝ) ≤ ((j - N : ℕ) : ℝ) := by exact_mod_cast (by omega : i - N ≤ j - N)
        rw [grifClamp_of_one_le (by linarith), round_one, zpow_one]
      · have : ((j - N : ℕ) : ℝ) + 1 ≤ ((i - N : ℕ) : ℝ) := by
          exact_mod_cast (by omega : j - N + 1 ≤ i - N)
        rw [grifClamp_of_nonpos (by linarith), round_zero, zpow_zero]
  unfold grifZ
  split_ifs with hij
  · refine cWinding_eq _ (Γ := ⟨fun t => (grifProg (((j - N : ℕ) : ℝ) + 1 / 2) t : ℂ) *
      (2 * Real.pi * Complex.I), by
        have := continuous_grifProg (((j - N : ℕ) : ℝ) + 1 / 2); fun_prop⟩) (fun t => ?_) ?_
    · show Complex.exp ((grifProg _ t : ℂ) * (2 * Real.pi * Complex.I)) = _
      rw [hβ t, if_pos hij, grifChiB_omegaK hN hj, grifE_eq_exp]
    · show (grifProg _ 1 : ℂ) * _ = (grifProg _ 0 : ℂ) * _ + _
      rw [grifProg_one, grifProg_zero (by positivity)]
      push_cast; ring
  · exact grif_cWinding_of_eq_one _ fun t => by rw [hβ t, if_neg hij]

/-- **`∏_{n ≥ N} a_n b_n` has a nontrivial invariant.** -/
theorem grifTheta_omega_ne_one {N : ℕ} (hN : 0 < N) : grifTheta (grifOmegaK N hN) ≠ 1 := by
  intro h
  unfold grifTheta at h
  have h' : (QuotientAddGroup.mk fun i j => grifZ (grifOmegaK N hN) i j : GrifQ) = 0 := h
  rw [QuotientAddGroup.eq_zero_iff] at h'
  exact grif_not_mem_FR (N := N) (fun i j hi hj => grifZ_omega hN hi hj) h'

/-! ### The Griffiths twin cone -/

/-- The point at height `s` of the segment from `q` (in the plane) to the apex `(1/2, 1)`. -/
def grifKapA (q : ℂ) (s : ℝ) : ℂ × ℝ := (((1 - s : ℝ) : ℂ) * q + ((s / 2 : ℝ) : ℂ), s)

/-- The point at height `s` of the segment from `q` to the apex `(-1/2, 1)`. -/
def grifKapB (q : ℂ) (s : ℝ) : ℂ × ℝ := (((1 - s : ℝ) : ℂ) * q - ((s / 2 : ℝ) : ℂ), s)

/-- The cone over the right earring, apex `(1/2, 1)`. -/
def grifConeA : Set (ℂ × ℝ) := {p | ∃ q ∈ grifHEA, ∃ s ∈ Icc (0 : ℝ) 1, p = grifKapA q s}

/-- The cone over the left earring, apex `(-1/2, 1)`. -/
def grifConeB : Set (ℂ × ℝ) := {p | ∃ q ∈ grifHEB, ∃ s ∈ Icc (0 : ℝ) 1, p = grifKapB q s}

/-- The Griffiths twin cone as a subset of `ℂ × ℝ = ℝ³`. -/
def grifSet : Set (ℂ × ℝ) := grifConeA ∪ grifConeB

/-- **The Griffiths twin cone**: the cones over two Hawaiian earrings, wedged at the earrings'
common point. -/
abbrev GriffithsSpace : Type := ↥grifSet

/-- The apex of the right cone. -/
def grifPA : ℂ × ℝ := grifKapA 0 1

/-- The apex of the left cone. -/
def grifPB : ℂ × ℝ := grifKapB 0 1

theorem grifKapA_snd (q : ℂ) (s : ℝ) : (grifKapA q s).2 = s := rfl

theorem grifKapB_snd (q : ℂ) (s : ℝ) : (grifKapB q s).2 = s := rfl

theorem grifKapA_one (q : ℂ) : grifKapA q 1 = grifPA := by simp [grifKapA, grifPA]

theorem grifKapB_one (q : ℂ) : grifKapB q 1 = grifPB := by simp [grifKapB, grifPB]

theorem grifKapA_zero (q : ℂ) : grifKapA q 0 = (q, 0) := by simp [grifKapA]

theorem grifKapB_zero (q : ℂ) : grifKapB q 0 = (q, 0) := by simp [grifKapB]

theorem re_grifKapA (q : ℂ) (s : ℝ) : (grifKapA q s).1.re = (1 - s) * q.re + s / 2 := by
  simp [grifKapA]

theorem re_grifKapB (q : ℂ) (s : ℝ) : (grifKapB q s).1.re = (1 - s) * q.re - s / 2 := by
  simp [grifKapB]

theorem grifConeA_facts {p : ℂ × ℝ} (hp : p ∈ grifConeA) :
    0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.2 / 2 ≤ p.1.re := by
  obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
  refine ⟨hs0, hs1, ?_⟩
  rw [re_grifKapA, grifKapA_snd]
  have := re_nonneg_of_mem_grifHEA hq
  nlinarith

theorem grifConeB_facts {p : ℂ × ℝ} (hp : p ∈ grifConeB) :
    0 ≤ p.2 ∧ p.2 ≤ 1 ∧ p.1.re ≤ -(p.2 / 2) := by
  obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
  refine ⟨hs0, hs1, ?_⟩
  rw [re_grifKapB, grifKapB_snd]
  have := re_nonpos_of_mem_grifHEB hq
  nlinarith

theorem grifSet_snd {p : ℂ × ℝ} (hp : p ∈ grifSet) : 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rcases hp with hp | hp
  · exact ⟨(grifConeA_facts hp).1, (grifConeA_facts hp).2.1⟩
  · exact ⟨(grifConeB_facts hp).1, (grifConeB_facts hp).2.1⟩

theorem zero_mem_grifConeA : ((0 : ℂ), (0 : ℝ)) ∈ grifConeA :=
  ⟨0, zero_mem_grifHEA, 0, ⟨le_rfl, zero_le_one⟩, by rw [grifKapA_zero]⟩

theorem zero_mem_grifConeB : ((0 : ℂ), (0 : ℝ)) ∈ grifConeB :=
  ⟨0, zero_mem_grifHEB, 0, ⟨le_rfl, zero_le_one⟩, by rw [grifKapB_zero]⟩

theorem eq_zero_of_mem_grifConeA_of_mem_grifConeB {p : ℂ × ℝ} (ha : p ∈ grifConeA)
    (hb : p ∈ grifConeB) : p = ((0 : ℂ), (0 : ℝ)) := by
  have h1 := grifConeA_facts ha
  have h2 := grifConeB_facts hb
  have hs : p.2 = 0 := by linarith
  obtain ⟨q, hq, s, -, rfl⟩ := ha
  rw [grifKapA_snd] at hs
  subst hs
  rw [grifKapA_zero] at h1 h2 ⊢
  have : q.re = 0 := by simp at h1 h2; linarith
  rw [eq_zero_of_mem_grifHEA_of_re hq this]

theorem grifPA_mem : grifPA ∈ grifConeA :=
  ⟨0, zero_mem_grifHEA, 1, ⟨zero_le_one, le_rfl⟩, rfl⟩

theorem grifPB_mem : grifPB ∈ grifConeB :=
  ⟨0, zero_mem_grifHEB, 1, ⟨zero_le_one, le_rfl⟩, rfl⟩

theorem grifPA_not_mem_grifConeB : grifPA ∉ grifConeB := fun h => by
  have := (grifConeB_facts h).2.2
  simp [grifPA, grifKapA] at this; linarith

theorem grifPB_not_mem_grifConeA : grifPB ∉ grifConeA := fun h => by
  have := (grifConeA_facts h).2.2
  simp [grifPB, grifKapB] at this; linarith

theorem eq_grifPA_of_snd {p : ℂ × ℝ} (hp : p ∈ grifConeA) (h : p.2 = 1) : p = grifPA := by
  obtain ⟨q, hq, s, -, rfl⟩ := hp
  rw [grifKapA_snd] at h; subst h; exact grifKapA_one q

theorem eq_grifPB_of_snd {p : ℂ × ℝ} (hp : p ∈ grifConeB) (h : p.2 = 1) : p = grifPB := by
  obtain ⟨q, hq, s, -, rfl⟩ := hp
  rw [grifKapB_snd] at h; subst h; exact grifKapB_one q

theorem grifConeA_eq_image :
    grifConeA = (fun x : ℂ × ℝ => grifKapA x.1 x.2) '' (grifHEA ×ˢ Icc 0 1) := by
  ext p
  constructor
  · rintro ⟨q, hq, s, hs, rfl⟩; exact ⟨(q, s), ⟨hq, hs⟩, rfl⟩
  · rintro ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩; exact ⟨q, hq, s, hs, rfl⟩

theorem grifConeB_eq_image :
    grifConeB = (fun x : ℂ × ℝ => grifKapB x.1 x.2) '' (grifHEB ×ˢ Icc 0 1) := by
  ext p
  constructor
  · rintro ⟨q, hq, s, hs, rfl⟩; exact ⟨(q, s), ⟨hq, hs⟩, rfl⟩
  · rintro ⟨⟨q, s⟩, ⟨hq, hs⟩, rfl⟩; exact ⟨q, hq, s, hs, rfl⟩

theorem continuous_grifKapA : Continuous fun x : ℂ × ℝ => grifKapA x.1 x.2 := by
  unfold grifKapA; fun_prop

theorem continuous_grifKapB : Continuous fun x : ℂ × ℝ => grifKapB x.1 x.2 := by
  unfold grifKapB; fun_prop

theorem isCompact_grifConeA : IsCompact grifConeA := by
  rw [grifConeA_eq_image]
  exact (isCompact_grifHEA.prod isCompact_Icc).image continuous_grifKapA

theorem isCompact_grifConeB : IsCompact grifConeB := by
  rw [grifConeB_eq_image]
  exact (isCompact_grifHEB.prod isCompact_Icc).image continuous_grifKapB

theorem isClosed_grifConeA : IsClosed grifConeA := isCompact_grifConeA.isClosed

theorem isClosed_grifConeB : IsClosed grifConeB := isCompact_grifConeB.isClosed

theorem isCompact_grifSet : IsCompact grifSet := isCompact_grifConeA.union isCompact_grifConeB

theorem starConvex_grifConeA : StarConvex ℝ grifPA grifConeA := by
  intro p hp a b ha hb hab
  obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
  refine ⟨q, hq, a + b * s, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  obtain rfl : a = 1 - b := by linarith
  simp only [grifPA, grifKapA, Prod.smul_mk, Prod.mk_add_mk, Complex.real_smul, smul_eq_mul]
  ext
  all_goals simp
  ring

theorem starConvex_grifConeB : StarConvex ℝ grifPB grifConeB := by
  intro p hp a b ha hb hab
  obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
  refine ⟨q, hq, a + b * s, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  obtain rfl : a = 1 - b := by linarith
  simp only [grifPB, grifKapB, Prod.smul_mk, Prod.mk_add_mk, Complex.real_smul, smul_eq_mul]
  ext
  all_goals simp
  ring

/-! #### The retraction onto the earrings along the cone lines -/

/-- The foot `q` of the cone line through `p`: `(p₁ - clamp(Re p₁, ±h/2)) / (1 - h)`. -/
def grifR (p : ℂ × ℝ) : ℂ :=
  (p.1 - ((max (-(p.2 / 2)) (min (p.2 / 2) p.1.re) : ℝ) : ℂ)) / ((1 - p.2 : ℝ) : ℂ)

theorem grifR_kapA {q : ℂ} (hq : 0 ≤ q.re) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) :
    grifR (grifKapA q s) = q := by
  have hre := re_grifKapA q s
  have h1 : min (s / 2) (grifKapA q s).1.re = s / 2 := min_eq_left (by rw [hre]; nlinarith)
  have h2 : max (-(s / 2)) (s / 2) = s / 2 := max_eq_right (by linarith)
  have hne : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  unfold grifR
  rw [grifKapA_snd, h1, h2]
  simp only [grifKapA, add_sub_cancel_right]
  exact mul_div_cancel_left₀ q hne

theorem grifR_kapB {q : ℂ} (hq : q.re ≤ 0) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) :
    grifR (grifKapB q s) = q := by
  have hre := re_grifKapB q s
  have h1 : min (s / 2) (grifKapB q s).1.re = (grifKapB q s).1.re :=
    min_eq_right (by rw [hre]; nlinarith)
  have h2 : max (-(s / 2)) (grifKapB q s).1.re = -(s / 2) :=
    max_eq_left (by rw [hre]; nlinarith)
  have hne : ((1 - s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  unfold grifR
  rw [grifKapB_snd, h1, h2]
  simp only [grifKapB, Complex.ofReal_neg, sub_neg_eq_add, sub_add_cancel]
  exact mul_div_cancel_left₀ q hne

theorem grifR_zero_height (q : ℂ) : grifR (q, 0) = q := by simp [grifR]

theorem continuousAt_grifR {p : ℂ × ℝ} (hp : p.2 ≠ 1) : ContinuousAt grifR p := by
  have h1 : Continuous fun p : ℂ × ℝ =>
      p.1 - ((max (-(p.2 / 2)) (min (p.2 / 2) p.1.re) : ℝ) : ℂ) := by fun_prop
  have h2 : Continuous fun p : ℂ × ℝ => ((1 - p.2 : ℝ) : ℂ) := by fun_prop
  exact h1.continuousAt.div h2.continuousAt
    (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 (Ne.symm hp)))

theorem grifConeA_lt {p : ℂ × ℝ} (hp : p ∈ grifConeA) (h : p.2 < 1) :
    grifR p ∈ grifHEA ∧ p = grifKapA (grifR p) p.2 := by
  obtain ⟨q, hq, s, ⟨hs0, -⟩, rfl⟩ := hp
  rw [grifKapA_snd] at h ⊢
  rw [grifR_kapA (re_nonneg_of_mem_grifHEA hq) hs0 h]
  exact ⟨hq, rfl⟩

theorem grifConeB_lt {p : ℂ × ℝ} (hp : p ∈ grifConeB) (h : p.2 < 1) :
    grifR p ∈ grifHEB ∧ p = grifKapB (grifR p) p.2 := by
  obtain ⟨q, hq, s, ⟨hs0, -⟩, rfl⟩ := hp
  rw [grifKapB_snd] at h ⊢
  rw [grifR_kapB (re_nonpos_of_mem_grifHEB hq) hs0 h]
  exact ⟨hq, rfl⟩

theorem grifR_mem {p : ℂ × ℝ} (hp : p ∈ grifSet) (h : p.2 < 1) : grifR p ∈ grifK := by
  rcases hp with hp | hp
  · exact Or.inl (grifConeA_lt hp h).1
  · exact Or.inr (grifConeB_lt hp h).1

/-- The straight segment from `p` down its cone line to the plane stays in the space. -/
theorem grif_segment_mem {p : ℂ × ℝ} (hp : p ∈ grifSet) (h : p.2 < 1) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : (1 - τ) • p + τ • (grifR p, (0 : ℝ)) ∈ grifSet := by
  rcases hp with hp | hp
  · obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
    rw [grifKapA_snd] at h
    rw [grifR_kapA (re_nonneg_of_mem_grifHEA hq) hs0 h]
    refine Or.inl ⟨q, hq, (1 - τ) * s, ⟨by nlinarith, by nlinarith⟩, ?_⟩
    simp only [grifKapA, Prod.smul_mk, Prod.mk_add_mk, Complex.real_smul, smul_eq_mul]
    ext
    all_goals simp
    ring
  · obtain ⟨q, hq, s, ⟨hs0, hs1⟩, rfl⟩ := hp
    rw [grifKapB_snd] at h
    rw [grifR_kapB (re_nonpos_of_mem_grifHEB hq) hs0 h]
    refine Or.inr ⟨q, hq, (1 - τ) * s, ⟨by nlinarith, by nlinarith⟩, ?_⟩
    simp only [grifKapB, Prod.smul_mk, Prod.mk_add_mk, Complex.real_smul, smul_eq_mul]
    ext
    all_goals simp
    ring

/-! #### Parametrizations, compactness, local path-connectedness -/

/-- The base point of the space, the earrings' common point. -/
def grifX0 : GriffithsSpace := ⟨((0 : ℂ), (0 : ℝ)), Or.inl zero_mem_grifConeA⟩

instance : CompactSpace GriffithsSpace := isCompact_iff_compactSpace.1 isCompact_grifSet

/-- `(t, s) ↦` the point at height `s` over `σ(t)` of the right cone (clamped). -/
def grifHatA (d : ℝ × ℝ) : ℂ × ℝ :=
  grifKapA (grifSigma (projIcc 0 1 zero_le_one d.1)) (projIcc 0 1 zero_le_one d.2)

/-- `(t, s) ↦` the point at height `s` over `-σ(t)` of the left cone (clamped). -/
def grifHatB (d : ℝ × ℝ) : ℂ × ℝ :=
  grifKapB (-grifSigma (projIcc 0 1 zero_le_one d.1)) (projIcc 0 1 zero_le_one d.2)

theorem grif_continuous_sigma_proj :
    Continuous fun d : ℝ × ℝ => grifSigma (projIcc 0 1 zero_le_one d.1) :=
  grifSigma.continuous.comp (continuous_projIcc.comp continuous_fst)

theorem grif_continuous_proj_snd :
    Continuous fun d : ℝ × ℝ => ((projIcc 0 1 zero_le_one d.2 : Icc (0 : ℝ) 1) : ℝ) :=
  continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)

theorem continuous_grifHatA : Continuous grifHatA :=
  continuous_grifKapA.comp (grif_continuous_sigma_proj.prodMk grif_continuous_proj_snd)

theorem continuous_grifHatB : Continuous grifHatB :=
  continuous_grifKapB.comp (grif_continuous_sigma_proj.neg.prodMk grif_continuous_proj_snd)

theorem grifHatA_mem (d : ℝ × ℝ) : grifHatA d ∈ grifConeA :=
  ⟨_, grifSigma_mem _, _, (projIcc 0 1 zero_le_one d.2).2, rfl⟩

theorem grifHatB_mem (d : ℝ × ℝ) : grifHatB d ∈ grifConeB := by
  refine ⟨_, ?_, _, (projIcc 0 1 zero_le_one d.2).2, rfl⟩
  simp only [grifHEB, mem_setOf_eq, neg_neg]; exact grifSigma_mem _

theorem grifHatA_snd {d : ℝ × ℝ} (h : d.2 ∈ Icc (0 : ℝ) 1) : (grifHatA d).2 = d.2 := by
  simp [grifHatA, grifKapA_snd, projIcc_of_mem _ h]

theorem grifHatB_snd {d : ℝ × ℝ} (h : d.2 ∈ Icc (0 : ℝ) 1) : (grifHatB d).2 = d.2 := by
  simp [grifHatB, grifKapB_snd, projIcc_of_mem _ h]

theorem grifHatA_axis {s : ℝ} (h : s ∈ Icc (0 : ℝ) 1) : grifHatA (0, s) = grifKapA 0 s := by
  simp only [grifHatA, projIcc_left, projIcc_of_mem _ h]
  congr 1
  exact grifSigma_zero

theorem grifHatB_axis {s : ℝ} (h : s ∈ Icc (0 : ℝ) 1) : grifHatB (0, s) = grifKapB 0 s := by
  simp only [grifHatB, projIcc_left, projIcc_of_mem _ h]
  congr 1
  rw [neg_eq_zero]
  exact grifSigma_zero

theorem exists_grifHatA {p : ℂ × ℝ} (hp : p ∈ grifConeA) :
    ∃ d : ℝ × ℝ, d.1 ∈ Icc (0 : ℝ) 1 ∧ d.2 = p.2 ∧ grifHatA d = p := by
  obtain ⟨q, hq, s, hs, rfl⟩ := hp
  obtain ⟨t, rfl⟩ := grifSigma_surj hq
  refine ⟨((t : ℝ), s), t.2, rfl, ?_⟩
  simp only [grifHatA, projIcc_val, projIcc_of_mem _ hs]

theorem exists_grifHatB {p : ℂ × ℝ} (hp : p ∈ grifConeB) :
    ∃ d : ℝ × ℝ, d.1 ∈ Icc (0 : ℝ) 1 ∧ d.2 = p.2 ∧ grifHatB d = p := by
  obtain ⟨q, hq, s, hs, rfl⟩ := hp
  obtain ⟨t, ht⟩ := grifSigma_surj hq
  refine ⟨((t : ℝ), s), t.2, rfl, ?_⟩
  simp only [grifHatB, projIcc_val, projIcc_of_mem _ hs, ht, neg_neg]

/-- The parametrization of the right cone, into the space. -/
def grifPiA (d : ℝ × ℝ) : GriffithsSpace := ⟨grifHatA d, Or.inl (grifHatA_mem d)⟩

/-- The parametrization of the left cone, into the space. -/
def grifPiB (d : ℝ × ℝ) : GriffithsSpace := ⟨grifHatB d, Or.inr (grifHatB_mem d)⟩

theorem continuous_grifPiA : Continuous grifPiA := continuous_grifHatA.subtype_mk _

theorem continuous_grifPiB : Continuous grifPiB := continuous_grifHatB.subtype_mk _

theorem grifPiA_zero : grifPiA (0, 0) = grifX0 :=
  Subtype.ext (by
    show grifHatA (0, 0) = ((0 : ℂ), (0 : ℝ))
    rw [grifHatA_axis ⟨le_rfl, zero_le_one⟩, grifKapA_zero])

theorem grifPiB_zero : grifPiB (0, 0) = grifX0 :=
  Subtype.ext (by
    show grifHatB (0, 0) = ((0 : ℂ), (0 : ℝ))
    rw [grifHatB_axis ⟨le_rfl, zero_le_one⟩, grifKapB_zero])

/-- Points of the image of a convex set by a parametrization are joined inside any superset. -/
theorem grif_joinedIn_of_convex {f : ℝ × ℝ → GriffithsSpace} (hf : Continuous f)
    {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) {d d' : ℝ × ℝ} (hd : d ∈ S) (hd' : d' ∈ S)
    {T : Set GriffithsSpace} (hT : f '' S ⊆ T) : JoinedIn T (f d) (f d') :=
  (((hS.isPathConnected ⟨d, hd⟩).image hf).joinedIn _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩).mono hT

instance : PathConnectedSpace GriffithsSpace := by
  rw [pathConnectedSpace_iff_univ]
  refine ⟨grifX0, trivial, fun {y} _ => ?_⟩
  have hS : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Icc 0 1)
  rcases y.2 with hy | hy
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatA hy
    have : y = grifPiA d := Subtype.ext hd.symm
    rw [this, ← grifPiA_zero]
    exact grif_joinedIn_of_convex continuous_grifPiA hS ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl,
      zero_le_one⟩⟩ ⟨hd1, hd2 ▸ grifSet_snd (Or.inl hy)⟩ (subset_univ _)
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatB hy
    have : y = grifPiB d := Subtype.ext hd.symm
    rw [this, ← grifPiB_zero]
    exact grif_joinedIn_of_convex continuous_grifPiB hS ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl,
      zero_le_one⟩⟩ ⟨hd1, hd2 ▸ grifSet_snd (Or.inr hy)⟩ (subset_univ _)

/-- The square `[0,1]²`. -/
def grifSq : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

instance : LocPathConnectedSpace GriffithsSpace := by
  haveI : LocPathConnectedSpace grifSq :=
    Convex.locPathConnectedSpace (ℝ × ℝ) ((convex_Icc 0 1).prod (convex_Icc 0 1))
  haveI : CompactSpace grifSq :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod isCompact_Icc)
  set f : grifSq ⊕ grifSq → GriffithsSpace :=
    Sum.elim (fun d => grifPiA d) (fun d => grifPiB d)
  have hf : Continuous f := (continuous_grifPiA.comp continuous_subtype_val).sumElim
    (continuous_grifPiB.comp continuous_subtype_val)
  have hsurj : Surjective f := by
    intro y
    rcases y.2 with hy | hy
    · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatA hy
      exact ⟨Sum.inl ⟨d, hd1, hd2 ▸ grifSet_snd (Or.inl hy)⟩, Subtype.ext hd⟩
    · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatB hy
      exact ⟨Sum.inr ⟨d, hd1, hd2 ▸ grifSet_snd (Or.inr hy)⟩, Subtype.ext hd⟩
  exact (IsClosedMap.isQuotientMap (hf.isClosedMap) hf hsurj).locPathConnectedSpace

/-! #### Contracting the big circles through their cones -/

theorem grif_mem_grifSet_of_mem_grifK {q : ℂ} (hq : q ∈ grifK) : (q, (0 : ℝ)) ∈ grifSet := by
  rcases hq with hq | hq
  · exact Or.inl ⟨q, hq, 0, ⟨le_rfl, zero_le_one⟩, by rw [grifKapA_zero]⟩
  · exact Or.inr ⟨q, hq, 0, ⟨le_rfl, zero_le_one⟩, by rw [grifKapB_zero]⟩

/-- A point of the double earring off `0` is on the `m`-th right or left circle. -/
theorem grif_K_classify {q : ℂ} (hq : q ∈ grifK) (h0 : q ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ θ : ℝ, grifE θ ≠ 1 ∧
      ((q = grifCirc m θ ∧ 2 * (q⁻¹).re = m) ∨ (q = -grifCirc m θ ∧ 2 * (q⁻¹).re = -m)) := by
  rcases hq with ⟨n, θ, rfl⟩ | ⟨n, θ, h⟩
  · have he : grifE θ ≠ 1 := fun he => h0 (grifCirc_of_eq_one he)
    refine ⟨n + 1, n.succ_pos, θ, he, Or.inl ⟨by push_cast; rfl, ?_⟩⟩
    rw [two_re_inv_grifCirc _ he]; push_cast; rfl
  · have hq : q = -grifCirc ((n + 1 : ℕ) : ℝ) θ := by rw [← neg_neg q, h]; push_cast; rfl
    have he : grifE θ ≠ 1 := fun he => h0 (by rw [hq, grifCirc_of_eq_one he, neg_zero])
    refine ⟨n + 1, n.succ_pos, θ, he, Or.inr ⟨hq, ?_⟩⟩
    rw [hq, inv_neg, Complex.neg_re, mul_neg, two_re_inv_grifCirc _ he]

theorem grif_two_re_inv_int {q : ℂ} (hq : q ∈ grifK) (h0 : q ≠ 0) :
    ∃ k : ℤ, 2 * (q⁻¹).re = k ∧ 1 ≤ |(k : ℝ)| := by
  obtain ⟨m, hm, θ, -, h | h⟩ := grif_K_classify hq h0
  · refine ⟨m, by rw [h.2]; push_cast; rfl, ?_⟩
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast; rw [abs_of_pos (by linarith)]; exact this
  · refine ⟨-m, by rw [h.2]; push_cast; rfl, ?_⟩
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast; rw [abs_neg, abs_of_pos (by linarith)]; exact this

/-- Off `0`, the index `2 Re(1/q)` of the circle is locally constant on the double earring. -/
theorem grif_eventually_index {q₀ : GrifK} (h0 : (q₀ : ℂ) ≠ 0) :
    ∀ᶠ q : GrifK in 𝓝 q₀, (q : ℂ) ≠ 0 ∧ 2 * ((q : ℂ)⁻¹).re = 2 * ((q₀ : ℂ)⁻¹).re := by
  have hc : ContinuousAt (fun q : GrifK => 2 * ((q : ℂ)⁻¹).re) q₀ :=
    continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
      ((continuousAt_inv₀ h0).comp continuous_subtype_val.continuousAt))
  have hne : ∀ᶠ q : GrifK in 𝓝 q₀, (q : ℂ) ≠ 0 :=
    continuous_subtype_val.continuousAt.eventually (isOpen_ne.mem_nhds h0)
  filter_upwards [hne, hc.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))]
    with q hq hd
  refine ⟨hq, ?_⟩
  obtain ⟨k, hk, -⟩ := grif_two_re_inv_int q.2 hq
  obtain ⟨k₀, hk₀, -⟩ := grif_two_re_inv_int q₀.2 h0
  rw [Real.dist_eq, hk, hk₀] at hd
  rw [hk, hk₀]
  have : |((k - k₀ : ℤ) : ℝ)| < 1 := by push_cast; linarith
  have : k - k₀ = 0 := by
    rw [← Int.cast_abs] at this
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  rw [show k = k₀ by omega]

/-- The cone over a circle, as a function of a point `v` of the unit disc (`v = 0`: the apex);
`n > 0` for the right cone, `n < 0` for the left one. -/
def grifPsi (n : ℝ) (v : ℂ) : ℂ × ℝ :=
  ((((‖v‖ : ℝ) : ℂ) + v) / (n : ℂ) + (((n / (2 * |n|)) * (1 - ‖v‖) : ℝ) : ℂ), 1 - ‖v‖)

theorem continuous_grifPsi (n : ℝ) : Continuous (grifPsi n) := by unfold grifPsi; fun_prop

/-- **The collapse of the circles of index `< N`**: on such a circle (index `n = 2 Re(1/q)`),
the contraction of the circle through its cone, from `q` at time `0` to `0` at time `1`; the
other points do not move. -/
def grifColl (N : ℕ) (q : ℂ) (τ : ℝ) : ℂ × ℝ :=
  if q ≠ 0 ∧ |2 * (q⁻¹).re| < N then
    grifPsi (2 * (q⁻¹).re) ((((1 - τ) * (2 * (q⁻¹).re) : ℝ) : ℂ) * q - 1)
  else (q, 0)

theorem grifColl_zero (N : ℕ) (τ : ℝ) : grifColl N 0 τ = ((0 : ℂ), (0 : ℝ)) := by
  simp [grifColl]

theorem grif_mul_circ {m : ℕ} (hm : 0 < m) (θ : ℝ) : (m : ℂ) * grifCirc m θ = 1 - grifE θ := by
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [grifCirc]; push_cast; field_simp

theorem grif_v_eq {m : ℕ} (hm : 0 < m) (θ τ : ℝ) :
    (((1 - τ) * m : ℝ) : ℂ) * grifCirc m θ - 1 = -((τ : ℂ) + ((1 - τ : ℝ) : ℂ) * grifE θ) := by
  rw [show (((1 - τ) * m : ℝ) : ℂ) = ((1 - τ : ℝ) : ℂ) * (m : ℂ) by push_cast; ring, mul_assoc,
    grif_mul_circ hm]
  push_cast; ring

theorem grifColl_time_zero (N : ℕ) {q : ℂ} (hq : q ∈ grifK) : grifColl N q 0 = (q, 0) := by
  unfold grifColl
  split_ifs with h
  · obtain ⟨m, hm, θ, -, hc | hc⟩ := grif_K_classify hq h.1
    · have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hv : (((1 - 0) * (m : ℝ) : ℝ) : ℂ) * grifCirc m θ - 1 = -grifE θ := by
        rw [grif_v_eq hm]; push_cast; ring
      rw [hc.2, hc.1, hv, grifPsi, norm_neg, norm_grifE]
      ext
      · simp only [sub_self, mul_zero, Complex.ofReal_zero, add_zero, Complex.ofReal_one]
        rw [grifCirc]; push_cast; ring
      · simp
    · have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hv : (((1 - 0) * -(m : ℝ) : ℝ) : ℂ) * -grifCirc m θ - 1 = -grifE θ := by
        rw [show (((1 - 0) * -(m : ℝ) : ℝ) : ℂ) * -grifCirc m θ - 1 =
          (((1 - 0) * (m : ℝ) : ℝ) : ℂ) * grifCirc m θ - 1 by push_cast; ring, grif_v_eq hm]
        push_cast; ring
      rw [hc.2, hc.1, hv, grifPsi, norm_neg, norm_grifE]
      ext
      · simp only [sub_self, mul_zero, Complex.ofReal_zero, add_zero, Complex.ofReal_one]
        rw [grifCirc]; push_cast; field_simp; ring
      · simp
  · rfl

theorem grif_abs_half {n : ℝ} (hn : n ≠ 0) : |n / (2 * |n|)| ≤ 1 := by
  rw [abs_div, abs_mul, abs_two, abs_abs, div_le_one (by positivity)]
  linarith [abs_pos.2 hn]

theorem norm_grifColl_one (N : ℕ) (hN : 0 < N) {q : ℂ} : ‖grifColl N q 1‖ ≤ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold grifColl
  split_ifs with h
  · simp [grifPsi]
    positivity
  · rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [norm_zero]; positivity
    · have h' : (N : ℝ) ≤ |2 * (q⁻¹).re| := by
        by_contra h''; exact h ⟨hq0, lt_of_not_ge h''⟩
      have := grif_norm_mul_two_re_inv_le hq0
      rw [le_div_iff₀ hN']
      nlinarith [norm_nonneg q]

theorem norm_grifColl_le (N : ℕ) {q : ℂ} (hq : q ∈ grifK) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖grifColl N q τ‖ ≤ (3 * N + 1) * ‖q‖ := by
  unfold grifColl
  split_ifs with h
  · obtain ⟨k, hk, hk1⟩ := grif_two_re_inv_int hq h.1
    set n := 2 * (q⁻¹).re
    set v : ℂ := (((1 - τ) * n : ℝ) : ℂ) * q - 1
    have hv1 : ‖v + 1‖ ≤ N * ‖q‖ := by
      simp only [v, sub_add_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ)]
      have : (1 - τ) * |n| ≤ N := by
        calc (1 - τ) * |n| ≤ 1 * |n| := by gcongr; linarith
          _ ≤ N := by linarith [h.2]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hn1 : 1 ≤ |n| := hk ▸ hk1
    have hnv : |1 - ‖v‖| ≤ ‖v + 1‖ := by
      have := abs_norm_sub_norm_le v (-1)
      rw [norm_neg, norm_one, sub_neg_eq_add, abs_sub_comm] at this
      exact this
    have h1 : ‖(((‖v‖ : ℝ) : ℂ) + v) / (n : ℂ)‖ ≤ 2 * ‖v + 1‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      calc ‖((‖v‖ : ℝ) : ℂ) + v‖ / |n| ≤ ‖((‖v‖ : ℝ) : ℂ) + v‖ :=
            div_le_self (norm_nonneg _) hn1
        _ = ‖((‖v‖ - 1 : ℝ) : ℂ) + (v + 1)‖ := by congr 1; push_cast; ring
        _ ≤ ‖((‖v‖ - 1 : ℝ) : ℂ)‖ + ‖v + 1‖ := norm_add_le _ _
        _ ≤ 2 * ‖v + 1‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; linarith
    have h2 : ‖((((n / (2 * |n|)) * (1 - ‖v‖) : ℝ)) : ℂ)‖ ≤ ‖v + 1‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hn0 : 0 < |n| := by linarith
      have : |n / (2 * |n|)| ≤ 1 := grif_abs_half (abs_pos.1 hn0)
      calc |n / (2 * |n|)| * |1 - ‖v‖| ≤ 1 * |1 - ‖v‖| := by gcongr
        _ ≤ ‖v + 1‖ := by rw [one_mul]; exact hnv
    rw [grifPsi, Prod.norm_mk]
    refine max_le ?_ ?_
    · calc ‖(((‖v‖ : ℝ) : ℂ) + v) / (n : ℂ) + ((((n / (2 * |n|)) * (1 - ‖v‖) : ℝ)) : ℂ)‖
          ≤ ‖(((‖v‖ : ℝ) : ℂ) + v) / (n : ℂ)‖ + ‖((((n / (2 * |n|)) * (1 - ‖v‖) : ℝ)) : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ 3 * ‖v + 1‖ := by linarith
        _ ≤ (3 * N + 1) * ‖q‖ := by nlinarith [norm_nonneg q]
    · rw [Real.norm_eq_abs]; nlinarith [norm_nonneg q]
  · rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    have : (0 : ℝ) ≤ 3 * N := by positivity
    nlinarith [norm_nonneg q]

theorem grif_exists_grifE {u : ℂ} (hu : ‖u‖ = 1) : ∃ θ : ℝ, grifE θ = u := by
  refine ⟨Complex.arg u / (2 * Real.pi), ?_⟩
  rw [grifE, show (2 * Real.pi * (Complex.arg u / (2 * Real.pi)) : ℝ) = Complex.arg u by
    field_simp]
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at this
  exact this

theorem norm_grif_v_le {m : ℕ} (hm : 0 < m) (θ : ℝ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖(((1 - τ) * m : ℝ) : ℂ) * grifCirc m θ - 1‖ ≤ 1 := by
  rw [grif_v_eq hm, norm_neg]
  calc ‖(τ : ℂ) + ((1 - τ : ℝ) : ℂ) * grifE θ‖
      ≤ ‖(τ : ℂ)‖ + ‖((1 - τ : ℝ) : ℂ) * grifE θ‖ := norm_add_le _ _
    _ = τ + (1 - τ) := by
        rw [norm_mul, norm_grifE, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hτ0, abs_of_nonneg (by linarith)]
    _ = 1 := by ring

theorem grif_circ_mem_HEA {m : ℕ} (hm : 0 < m) (θ : ℝ) : grifCirc m θ ∈ grifHEA :=
  ⟨m - 1, θ, by congr 1; rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hm.ne'), Nat.cast_one]; ring⟩

/-- The cone over the `m`-th right circle, parametrized by the unit disc. -/
theorem grifPsi_mem_A {m : ℕ} (hm : 0 < m) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    grifPsi m v ∈ grifConeA := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhalf : (m : ℝ) / (2 * |(m : ℝ)|) = 1 / 2 := by rw [abs_of_pos hm']; field_simp
  rcases eq_or_ne v 0 with rfl | hv0
  · refine ⟨0, zero_mem_grifHEA, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [grifPsi, norm_zero, hhalf, grifKapA]
    ext
    all_goals simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hnc : ((‖v‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
    obtain ⟨θ, hθ⟩ := grif_exists_grifE (u := -v / ((‖v‖ : ℝ) : ℂ)) (by
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
        div_self hn.ne'])
    refine ⟨grifCirc m θ, grif_circ_mem_HEA hm θ, 1 - ‖v‖, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [grifPsi, hhalf, grifKapA, grifCirc, hθ]
    ext
    · push_cast
      field_simp
      ring
    · simp

/-- The cone over the `m`-th left circle, parametrized by the unit disc. -/
theorem grifPsi_mem_B {m : ℕ} (hm : 0 < m) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    grifPsi (-(m : ℝ)) v ∈ grifConeB := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhalf : -(m : ℝ) / (2 * |-(m : ℝ)|) = -(1 / 2) := by
    rw [abs_neg, abs_of_pos hm']; field_simp
  rcases eq_or_ne v 0 with rfl | hv0
  · refine ⟨0, zero_mem_grifHEB, 1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    simp only [grifPsi, norm_zero, hhalf, grifKapB]
    ext
    all_goals simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hnc : ((‖v‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
    obtain ⟨θ, hθ⟩ := grif_exists_grifE (u := -v / ((‖v‖ : ℝ) : ℂ)) (by
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
        div_self hn.ne'])
    refine ⟨-grifCirc m θ, ?_, 1 - ‖v‖, ⟨by linarith, by linarith⟩, ?_⟩
    · simp only [grifHEB, mem_setOf_eq, neg_neg]; exact grif_circ_mem_HEA hm θ
    simp only [grifPsi, hhalf, grifKapB, grifCirc, hθ]
    ext
    · push_cast
      field_simp
      ring
    · simp

theorem grifColl_mem (N : ℕ) {q : ℂ} (hq : q ∈ grifK) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    grifColl N q τ ∈ grifSet := by
  unfold grifColl
  split_ifs with h
  · obtain ⟨m, hm, θ, -, hc | hc⟩ := grif_K_classify hq h.1
    · rw [hc.2, hc.1]
      exact Or.inl (grifPsi_mem_A hm (norm_grif_v_le hm θ hτ0 hτ1))
    · rw [hc.2, hc.1]
      have e : (((1 - τ) * -(m : ℝ) : ℝ) : ℂ) * -grifCirc m θ - 1 =
          (((1 - τ) * m : ℝ) : ℂ) * grifCirc m θ - 1 := by push_cast; ring
      rw [e]
      exact Or.inr (grifPsi_mem_B hm (norm_grif_v_le hm θ hτ0 hτ1))
  · exact grif_mem_grifSet_of_mem_grifK hq

theorem continuous_grifColl (N : ℕ) :
    Continuous fun z : GrifK × I => grifColl N (z.1 : ℂ) (z.2 : ℝ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨q₀, τ₀⟩
  by_cases h0 : (q₀ : ℂ) = 0
  · have hval : grifColl N (q₀ : ℂ) τ₀ = 0 := by rw [h0, grifColl_zero]; rfl
    rw [ContinuousAt, hval]
    refine squeeze_zero_norm (a := fun z : GrifK × I => (3 * N + 1) * ‖(z.1 : ℂ)‖)
      (fun z => norm_grifColl_le N z.1.2 z.2.2.1 z.2.2.2) ?_
    have : Tendsto (fun z : GrifK × I => (3 * N + 1) * ‖(z.1 : ℂ)‖) (𝓝 (q₀, τ₀))
        (𝓝 ((3 * N + 1) * ‖(q₀ : ℂ)‖)) :=
      (continuous_const.mul (continuous_norm.comp (continuous_subtype_val.comp
        continuous_fst))).tendsto _
    rwa [h0, norm_zero, mul_zero] at this
  · obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℝ, n₀ = 2 * ((q₀ : ℂ)⁻¹).re := ⟨_, rfl⟩
    have hev : (fun z : GrifK × I => if |n₀| < N then
        grifPsi n₀ ((((1 - (z.2 : ℝ)) * n₀ : ℝ) : ℂ) * (z.1 : ℂ) - 1) else ((z.1 : ℂ), (0 : ℝ)))
        =ᶠ[𝓝 (q₀, τ₀)] fun z : GrifK × I => grifColl N (z.1 : ℂ) (z.2 : ℝ) := by
      filter_upwards [continuous_fst.continuousAt.eventually (grif_eventually_index h0)]
        with z hz
      unfold grifColl
      rw [hz.2, ← hn₀]
      by_cases hN : |n₀| < N
      · rw [if_pos hN, if_pos (show (z.1 : ℂ) ≠ 0 ∧ |n₀| < N from ⟨hz.1, hN⟩)]
      · rw [if_neg hN, if_neg (fun h : (z.1 : ℂ) ≠ 0 ∧ |n₀| < N => hN h.2)]
    refine ContinuousAt.congr ?_ hev
    split_ifs
    · exact ((continuous_grifPsi n₀).comp (by fun_prop)).continuousAt
    · exact (by fun_prop : Continuous fun z : GrifK × I => ((z.1 : ℂ), (0 : ℝ))).continuousAt

/-! #### Semi-local simple connectedness in itself -/

/-- A loop inside a star-shaped part of the space is null-homotopic. -/
theorem grif_homotopic_refl_of_star {C : Set (ℂ × ℝ)} {c : ℂ × ℝ} (hC : StarConvex ℝ c C)
    (hc : c ∈ C) (hCG : C ⊆ grifSet) {x : GriffithsSpace} (γ : Path x x)
    (hγ : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ) ∈ C) : γ.Homotopic (Path.refl x) := by
  haveI : ContractibleSpace C := hC.contractibleSpace ⟨c, hc⟩
  have hx : (x : ℂ × ℝ) ∈ C := γ.source ▸ hγ 0
  let γC : Path (⟨x, hx⟩ : C) ⟨x, hx⟩ :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  let ι : C(C, GriffithsSpace) := ⟨fun y => ⟨y, hCG y.2⟩, continuous_subtype_val.subtype_mk _⟩
  have h := (SimplyConnectedSpace.paths_homotopic γC (Path.refl _)).map ι
  have e1 : γC.map ι.continuous = γ := Path.ext (funext fun _ => rfl)
  have e2 : (Path.refl (⟨x, hx⟩ : C)).map ι.continuous = Path.refl x :=
    Path.ext (funext fun _ => rfl)
  rw [e1, e2] at h
  exact h

/-- Semi-local simple connectedness in itself at a point with a star-shaped neighbourhood. -/
theorem grif_isSLSCAt_of_star {C : Set (ℂ × ℝ)} {c : ℂ × ℝ} (hC : StarConvex ℝ c C)
    (hc : c ∈ C) (hCG : C ⊆ grifSet) {x : GriffithsSpace} {O : Set GriffithsSpace}
    (hO : IsOpen O) (hxO : x ∈ O) (hOC : ∀ y ∈ O, (y : ℂ × ℝ) ∈ C) :
    IsSLSCAt (univ : Set GriffithsSpace) x := by
  refine ⟨pathComponentIn O x, hO.pathComponentIn x,
    (isPathConnected_pathComponentIn hxO).isConnected.isPreconnected,
    mem_pathComponentIn_self hxO, fun γ hγ => ?_⟩
  have hall : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ) ∈ C := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ.source]; exact hOC _ hxO
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ.target]; exact hOC _ hxO
    exact hOC _ (pathComponentIn_subset (hγ t h0 h1).1)
  obtain ⟨F⟩ := grif_homotopic_refl_of_star hC hc hCG γ hall
  exact ⟨fun _ _ _ => mem_univ _, fun W hW => ⟨Path.refl x,
    fun _ _ _ => ⟨mem_of_mem_nhds hW, mem_univ _⟩, F, fun _ _ _ _ => mem_univ _⟩⟩

theorem grif_isSLSCAt_of_ne {x : GriffithsSpace} (hx : x ≠ grifX0) :
    IsSLSCAt (univ : Set GriffithsSpace) x := by
  have hx' : (x : ℂ × ℝ) ≠ ((0 : ℂ), (0 : ℝ)) := fun h => hx (Subtype.ext h)
  rcases x.2 with hA | hB
  · refine grif_isSLSCAt_of_star starConvex_grifConeA grifPA_mem (subset_union_left)
      (O := {y | (y : ℂ × ℝ) ∉ grifConeB})
      (isClosed_grifConeB.isOpen_compl.preimage continuous_subtype_val)
      (fun hB => hx' (eq_zero_of_mem_grifConeA_of_mem_grifConeB hA hB)) fun y hy => ?_
    exact y.2.resolve_right hy
  · refine grif_isSLSCAt_of_star starConvex_grifConeB grifPB_mem (subset_union_right)
      (O := {y | (y : ℂ × ℝ) ∉ grifConeA})
      (isClosed_grifConeA.isOpen_compl.preimage continuous_subtype_val)
      (fun hA => hx' (eq_zero_of_mem_grifConeA_of_mem_grifConeB hA hB)) fun y hy => ?_
    exact y.2.resolve_left hy

/-- The space below the apexes is path-connected. -/
theorem grif_isPathConnected_below :
    IsPathConnected {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1} := by
  have hS : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Ico 0 1)
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1 :=
    ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_lt_one⟩⟩
  refine ⟨grifX0, by simp [grifX0], fun {y} hy => ?_⟩
  rcases y.2 with hA | hB
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatA hA
    have : y = grifPiA d := Subtype.ext hd.symm
    rw [this, ← grifPiA_zero]
    refine grif_joinedIn_of_convex continuous_grifPiA hS h00
      ⟨hd1, hd2 ▸ (grifSet_snd (Or.inl hA)).1, hd2 ▸ hy⟩ ?_
    rintro _ ⟨d', ⟨-, hd'⟩, rfl⟩
    show (grifHatA d').2 < 1
    rw [grifHatA_snd ⟨hd'.1, hd'.2.le⟩]; exact hd'.2
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatB hB
    have : y = grifPiB d := Subtype.ext hd.symm
    rw [this, ← grifPiB_zero]
    refine grif_joinedIn_of_convex continuous_grifPiB hS h00
      ⟨hd1, hd2 ▸ (grifSet_snd (Or.inr hB)).1, hd2 ▸ hy⟩ ?_
    rintro _ ⟨d', ⟨-, hd'⟩, rfl⟩
    show (grifHatB d').2 < 1
    rw [grifHatB_snd ⟨hd'.1, hd'.2.le⟩]; exact hd'.2

theorem grif_isSLSCAt_x0 : IsSLSCAt (univ : Set GriffithsSpace) grifX0 := by
  set V : Set GriffithsSpace := {y | (y : ℂ × ℝ).2 < 1}
  refine ⟨V, isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const,
    grif_isPathConnected_below.isConnected.isPreconnected, by simp [V, grifX0],
    fun γ hγ => ?_⟩
  have hall : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ).2 < 1 := fun t => by
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have : t = 0 := Subtype.ext h0.symm
      rw [this, γ.source]; simp [grifX0]
    rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have : t = 1 := Subtype.ext h1
      rw [this, γ.target]; simp [grifX0]
    exact (hγ t h0 h1).1
  have hR : ∀ t, grifR (γ t) ∈ grifK := fun t => grifR_mem (γ t).2 (hall t)
  have hRc : Continuous fun t => grifR (γ t) :=
    continuous_iff_continuousAt.2 fun t =>
      (continuousAt_grifR (ne_of_lt (hall t))).comp
        (f := fun t => ((γ t : GriffithsSpace) : ℂ × ℝ))
        (continuous_subtype_val.comp γ.continuous).continuousAt
  have hγ0 : ((γ 0 : GriffithsSpace) : ℂ × ℝ) = ((0 : ℂ), (0 : ℝ)) := by rw [γ.source]; rfl
  have hγ1 : ((γ 1 : GriffithsSpace) : ℂ × ℝ) = ((0 : ℂ), (0 : ℝ)) := by rw [γ.target]; rfl
  have hR0 : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ) = ((0 : ℂ), (0 : ℝ)) → grifR (γ t) = 0 :=
    fun t h => by rw [h, grifR_zero_height]
  have hx0 : ((grifX0 : GriffithsSpace) : ℂ × ℝ) = ((0 : ℂ), (0 : ℝ)) := rfl
  -- down the cone lines
  let γ₁ : Path grifX0 grifX0 :=
    { toFun := fun t => ⟨(grifR (γ t), (0 : ℝ)), grif_mem_grifSet_of_mem_grifK (hR t)⟩
      continuous_toFun := (hRc.prodMk continuous_const).subtype_mk _
      source' := Subtype.ext (by
        show (grifR (γ 0), (0 : ℝ)) = _
        rw [hR0 0 hγ0]; rfl)
      target' := Subtype.ext (by
        show (grifR (γ 1), (0 : ℝ)) = _
        rw [hR0 1 hγ1]; rfl) }
  have F₁ : γ.Homotopic γ₁ := ⟨{
    toFun := fun z => ⟨(1 - (z.1 : ℝ)) • ((γ z.2 : GriffithsSpace) : ℂ × ℝ) +
        (z.1 : ℝ) • (grifR (γ z.2), (0 : ℝ)),
      grif_segment_mem (γ z.2).2 (hall z.2) z.1.2.1 z.1.2.2⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      have h1 : Continuous fun z : I × I => ((γ z.2 : GriffithsSpace) : ℂ × ℝ) :=
        continuous_subtype_val.comp (γ.continuous.comp continuous_snd)
      have h2 : Continuous fun z : I × I => (grifR (γ z.2), (0 : ℝ)) :=
        (hRc.comp continuous_snd).prodMk continuous_const
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul h1).add
        ((continuous_subtype_val.comp continuous_fst).smul h2)
    map_zero_left := fun t => Subtype.ext (by simp)
    map_one_left := fun t => Subtype.ext (by simp; rfl)
    prop' := fun s t ht => by
      refine Subtype.ext ?_
      rcases ht with rfl | rfl
      · show (1 - (s : ℝ)) • ((γ 0 : GriffithsSpace) : ℂ × ℝ) + (s : ℝ) • (grifR (γ 0), (0 : ℝ))
          = ((γ 0 : GriffithsSpace) : ℂ × ℝ)
        rw [hR0 0 hγ0, hγ0]; simp
      · show (1 - (s : ℝ)) • ((γ 1 : GriffithsSpace) : ℂ × ℝ) + (s : ℝ) • (grifR (γ 1), (0 : ℝ))
          = ((γ 1 : GriffithsSpace) : ℂ × ℝ)
        rw [hR0 1 hγ1, hγ1]; simp }⟩
  refine ⟨fun _ _ _ => mem_univ _, fun W hW => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  -- the collapse of the big circles
  have hC : Continuous fun z : I × I => grifColl N (grifR (γ z.2)) (z.1 : ℝ) :=
    (continuous_grifColl N).comp
      (((hRc.comp continuous_snd).subtype_mk (fun z => hR z.2)).prodMk continuous_fst)
  let γ₂ : Path grifX0 grifX0 :=
    { toFun := fun t => ⟨grifColl N (grifR (γ t)) ((1 : I) : ℝ),
        grifColl_mem N (hR t) (1 : I).2.1 (1 : I).2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact hC.comp (f := fun t : I => ((1 : I), t)) (continuous_const.prodMk continuous_id)
      source' := Subtype.ext (by
        show grifColl N (grifR (γ 0)) ((1 : I) : ℝ) = _
        rw [hR0 0 hγ0, grifColl_zero]; rfl)
      target' := Subtype.ext (by
        show grifColl N (grifR (γ 1)) ((1 : I) : ℝ) = _
        rw [hR0 1 hγ1, grifColl_zero]; rfl) }
  have F₂ : γ₁.Homotopic γ₂ := ⟨{
    toFun := fun z => ⟨grifColl N (grifR (γ z.2)) (z.1 : ℝ),
      grifColl_mem N (hR z.2) z.1.2.1 z.1.2.2⟩
    continuous_toFun := hC.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by
      show grifColl N (grifR (γ t)) ((0 : I) : ℝ) = (grifR (γ t), (0 : ℝ))
      exact grifColl_time_zero N (hR t))
    map_one_left := fun t => rfl
    prop' := fun s t ht => by
      refine Subtype.ext ?_
      rcases ht with rfl | rfl
      · show grifColl N (grifR (γ 0)) (s : ℝ) = (grifR (γ 0), (0 : ℝ))
        rw [hR0 0 hγ0, grifColl_zero]
      · show grifColl N (grifR (γ 1)) (s : ℝ) = (grifR (γ 1), (0 : ℝ))
        rw [hR0 1 hγ1, grifColl_zero] }⟩
  refine ⟨γ₂, fun t _ _ => ⟨hball ?_, mem_univ _⟩, ?_⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    show ‖grifColl N (grifR (γ t)) ((1 : I) : ℝ) - ((0 : ℂ), (0 : ℝ))‖ < ε
    rw [show ((0 : ℂ), (0 : ℝ)) = (0 : ℂ × ℝ) from rfl, sub_zero, Set.Icc.coe_one]
    refine (norm_grifColl_one N hNpos).trans_lt ?_
    rw [div_lt_iff₀ (by exact_mod_cast hNpos)]
    rw [div_lt_iff₀ hε] at hN
    linarith
  · obtain ⟨G⟩ := F₁.trans F₂
    exact ⟨G, fun _ _ _ _ => mem_univ _⟩

/-- **The Griffiths twin cone is semi-locally simply connected in itself**, homotopy form. -/
theorem griffiths_isSLSCIn : IsSLSCIn (univ : Set GriffithsSpace) := by
  refine ⟨dense_univ, fun x => ?_⟩
  by_cases hx : x = grifX0
  · subst hx; exact grif_isSLSCAt_x0
  · exact grif_isSLSCAt_of_ne hx

/-! ### Seifert–van Kampen: multiplicativity of the glued invariant -/

namespace VanKampen

namespace Data

variable {Y : Type*} [TopologicalSpace Y] {G : Type*} [Group G] (D : Data Y G)

theorem grif_trans_extend_le {a b c : Y} (γ : Path a b) (γ' : Path b c) {r : ℝ} (h0 : 0 ≤ r)
    (h1 : r ≤ 1 / 2) : (γ.trans γ').extend r = γ.extend (2 * r) := by
  rw [Path.extend_apply _ ⟨h0, by linarith⟩, Path.extend_apply _ ⟨by linarith, by linarith⟩,
    Path.trans_apply, dif_pos h1]

theorem grif_trans_extend_ge {a b c : Y} (γ : Path a b) (γ' : Path b c) {r : ℝ}
    (h0 : 1 / 2 ≤ r) (h1 : r ≤ 1) : (γ.trans γ').extend r = γ'.extend (2 * r - 1) := by
  rw [Path.extend_apply _ ⟨by linarith, h1⟩, Path.extend_apply _ ⟨by linarith, by linarith⟩,
    Path.trans_apply]
  rcases h0.lt_or_eq with h | h
  · rw [dif_neg (not_le.2 h)]
  · subst h
    rw [dif_pos le_rfl]
    have e1 : (⟨2 * (1 / 2 : ℝ), by norm_num⟩ : I) = 1 := Subtype.ext (by norm_num)
    have e2 : (⟨2 * (1 / 2 : ℝ) - 1, by norm_num⟩ : I) = 0 := Subtype.ext (by norm_num)
    rw [e1, e2, γ.target, γ'.source]

/-- **The glued invariant is multiplicative** on concatenations of paths. -/
theorem Φ_trans {a b c : Y} (γ : Path a b) (γ' : Path b c) :
    D.Φ (γ.trans γ') = D.Φ γ * D.Φ γ' := by
  obtain ⟨N₁, h₁⟩ := D.exists_fine γ
  obtain ⟨N₂, h₂⟩ := D.exists_fine γ'
  set N := max N₁ N₂ + 1
  have hN : D.Fine γ N := h₁ N (by omega)
  have hN' : D.Fine γ' N := h₂ N (by omega)
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcast : ((N + N : ℕ) : ℝ) = 2 * N := by push_cast; ring
  have hfine : D.Fine (γ.trans γ') (N + N) := by
    refine ⟨by omega, fun j hj => ?_⟩
    rw [hcast]
    by_cases hjN : j < N
    · obtain ⟨c, hc⟩ := hN.2 j hjN
      refine ⟨c, fun r hr1 hr2 => ?_⟩
      have hj1 : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
      have hr0 : 0 ≤ r := le_trans (by positivity) hr1
      have hr12 : r ≤ 1 / 2 := hr2.trans (by rw [div_le_iff₀ (by positivity)]; linarith)
      rw [grif_trans_extend_le γ γ' hr0 hr12]
      refine hc (2 * r) ?_ ?_
      · rw [div_le_iff₀ (by positivity)] at hr1 ⊢; linarith
      · rw [le_div_iff₀ (by positivity)] at hr2 ⊢; linarith
    · obtain ⟨c, hc⟩ := hN'.2 (j - N) (by omega)
      refine ⟨c, fun r hr1 hr2 => ?_⟩
      have hjN' : (N : ℝ) ≤ j := by exact_mod_cast (not_lt.1 hjN)
      have hj1 : (j : ℝ) + 1 ≤ 2 * N := by
        have : j + 1 ≤ N + N := hj
        have : ((j + 1 : ℕ) : ℝ) ≤ ((N + N : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      have hr12 : 1 / 2 ≤ r := by
        refine le_trans ?_ hr1
        rw [le_div_iff₀ (by positivity)]; linarith
      have hr1' : r ≤ 1 := hr2.trans (by rw [div_le_one (by positivity)]; linarith)
      rw [grif_trans_extend_ge γ γ' hr12 hr1']
      have hjc : ((j - N : ℕ) : ℝ) = j - N := by rw [Nat.cast_sub (not_lt.1 hjN)]
      refine hc (2 * r - 1) ?_ ?_
      · rw [hjc, div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at hr1; linarith
      · rw [hjc, le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ (by positivity)] at hr2; linarith
  rw [D.Φ_eq hfine, D.Φ_eq hN, D.Φ_eq hN']
  unfold prodN
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < N := List.mem_range.1 hj
    refine D.ψ_congr _ _ fun t => ?_
    simp only [seg]
    rw [subpath_apply', subpath_apply', pt_val (by omega), pt_val (by omega), pt_val (by omega),
      pt_val (by omega), hcast]
    have hjr : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hj'
    have ht0 := t.2.1
    have ht1 := t.2.2
    rw [grif_trans_extend_le γ γ']
    · congr 1; push_cast; field_simp
    · push_cast; positivity
    · push_cast
      rw [show (1 - (t : ℝ)) * (j / (2 * N)) + t * ((j + 1) / (2 * N)) =
        ((1 - t) * j + t * (j + 1)) / (2 * N) by field_simp]
      rw [div_le_iff₀ (by positivity)]; nlinarith
  · congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < N := List.mem_range.1 hj
    refine D.ψ_congr _ _ fun t => ?_
    simp only [seg]
    rw [subpath_apply', subpath_apply', pt_val (by omega), pt_val (by omega), pt_val (by omega),
      pt_val (by omega), hcast]
    have hjr : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hj'
    have ht0 := t.2.1
    have ht1 := t.2.2
    rw [grif_trans_extend_ge γ γ']
    · congr 1; push_cast; field_simp; ring
    · push_cast
      rw [show (1 - (t : ℝ)) * ((N + j) / (2 * N)) + t * ((N + j + 1) / (2 * N)) =
        ((1 - t) * (N + j) + t * (N + j + 1)) / (2 * N) by field_simp]
      rw [le_div_iff₀ (by positivity)]; nlinarith
    · push_cast
      rw [show (1 - (t : ℝ)) * ((N + j) / (2 * N)) + t * ((N + j + 1) / (2 * N)) =
        ((1 - t) * (N + j) + t * (N + j + 1)) / (2 * N) by field_simp]
      rw [div_le_iff₀ (by positivity)]; nlinarith

end Data

end VanKampen

/-! ### The gluing data -/

/-- Gluing data from two open path-connected sets with path-connected intersection: the
invariant `fU` on the loops of `U`, `1` on those of `V`. -/
def grifMkData {Y : Type*} [TopologicalSpace Y] {G : Type*} [Group G] (U V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : ∀ y, y ∈ U ∨ y ∈ V) (x₀ : Y) (hx₀ : x₀ ∈ U ∩ V)
    (hUc : IsPathConnected U) (hVc : IsPathConnected V) (hW : IsPathConnected (U ∩ V))
    (fU : Path x₀ x₀ → G) (hfU : ∀ γ γ', HomotopicIn U γ γ' → fU γ = fU γ')
    (hfU' : ∀ γ γ', (∀ t, γ t ∈ U) → (∀ t, γ' t ∈ U) → fU (γ.trans γ') = fU γ * fU γ')
    (hagree : ∀ γ : Path x₀ x₀, (∀ t, γ t ∈ U) → (∀ t, γ t ∈ V) → fU γ = 1) :
    VanKampen.Data Y G where
  S b := cond b U V
  isOpen b := by cases b; exacts [hV, hU]
  cover y := by
    rcases hcov y with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  x₀ := x₀
  τ y := if hy0 : y = x₀ then (Path.refl x₀).cast rfl hy0
    else if hyW : y ∈ U ∩ V then (hW.joinedIn x₀ hx₀ y hyW).somePath
    else if hyU : y ∈ U then (hUc.joinedIn x₀ hx₀.1 y hyU).somePath
    else (hVc.joinedIn x₀ hx₀.2 y ((hcov y).resolve_left hyU)).somePath
  τ_mem b y hy t := by
    split_ifs with hy0 hyW hyU
    · subst hy0; cases b
      · exact hx₀.2
      · exact hx₀.1
    · cases b
      · exact ((hW.joinedIn x₀ hx₀ y hyW).somePath_mem t).2
      · exact ((hW.joinedIn x₀ hx₀ y hyW).somePath_mem t).1
    · cases b
      · exact absurd ⟨hyU, hy⟩ hyW
      · exact (hUc.joinedIn x₀ hx₀.1 y hyU).somePath_mem t
    · cases b
      · exact (hVc.joinedIn x₀ hx₀.2 y ((hcov y).resolve_left hyU)).somePath_mem t
      · exact absurd hy hyU
  τ_x₀ := by simp
  f b := cond b fU fun _ => 1
  f_hom b γ γ' h := by
    cases b
    · rfl
    · exact hfU γ γ' h
  f_trans b γ γ' hγ hγ' := by
    cases b
    · exact (mul_one 1).symm
    · exact hfU' γ γ' hγ hγ'
  agree γ hU' hV' := hagree γ hU' hV'

/-! ### Retracting loops below the apexes onto the double earring -/

/-- The retraction to the double earring of a path below the apexes between points over `0`. -/
def grifRP {a b : GriffithsSpace} (γ : Path a b)
    (h : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ).2 < 1) (ha : grifR (a : ℂ × ℝ) = 0)
    (hb : grifR (b : ℂ × ℝ) = 0) : Path grifK0 grifK0 where
  toFun t := ⟨grifR (γ t), grifR_mem (γ t).2 (h t)⟩
  continuous_toFun := (continuous_iff_continuousAt.2 fun t =>
      (continuousAt_grifR (ne_of_lt (h t))).comp
        (f := fun t => ((γ t : GriffithsSpace) : ℂ × ℝ))
        (continuous_subtype_val.comp γ.continuous).continuousAt).subtype_mk _
  source' := Subtype.ext (by
    show grifR ((γ 0 : GriffithsSpace) : ℂ × ℝ) = 0; rw [γ.source]; exact ha)
  target' := Subtype.ext (by
    show grifR ((γ 1 : GriffithsSpace) : ℂ × ℝ) = 0; rw [γ.target]; exact hb)

theorem grifRP_apply {a b : GriffithsSpace} (γ : Path a b) h ha hb (t : I) :
    ((grifRP γ h ha hb t : GrifK) : ℂ) = grifR ((γ t : GriffithsSpace) : ℂ × ℝ) := rfl

theorem grifRP_congr {a b a' b' : GriffithsSpace} (P : Path a b) (P' : Path a' b') hP hP' ha hb
    ha' hb' (h : ∀ t, P t = P' t) : grifRP P hP ha hb = grifRP P' hP' ha' hb' :=
  Path.ext (funext fun t => Subtype.ext (by rw [grifRP_apply, grifRP_apply, h t]))

theorem grifRP_conj {a b : GriffithsSpace} (c : Path a b) (γ : Path b b) hc hγ ha hb hL :
    grifRP ((c.trans γ).trans c.symm) hL ha ha =
      ((grifRP c hc ha hb).trans (grifRP γ hγ hb hb)).trans (grifRP c hc ha hb).symm := by
  refine Path.ext (funext fun t => Subtype.ext ?_)
  rw [grifRP_apply]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> rfl

theorem grifRP_homotopic {a b : GriffithsSpace} {γ γ' : Path a b} (F : Path.Homotopy γ γ')
    (hF : ∀ z, ((F z : GriffithsSpace) : ℂ × ℝ).2 < 1) h h' ha hb :
    (grifRP γ h ha hb).Homotopic (grifRP γ' h' ha hb) := ⟨{
  toFun := fun z => ⟨grifR (F z), grifR_mem (F z).2 (hF z)⟩
  continuous_toFun := (continuous_iff_continuousAt.2 fun z =>
      (continuousAt_grifR (ne_of_lt (hF z))).comp
        (f := fun z => ((F z : GriffithsSpace) : ℂ × ℝ))
        (continuous_subtype_val.comp F.continuous).continuousAt).subtype_mk _
  map_zero_left := fun t => Subtype.ext (by
    show grifR ((F (0, t) : GriffithsSpace) : ℂ × ℝ) = grifR ((γ t : GriffithsSpace) : ℂ × ℝ)
    rw [F.apply_zero]; rfl)
  map_one_left := fun t => Subtype.ext (by
    show grifR ((F (1, t) : GriffithsSpace) : ℂ × ℝ) = grifR ((γ' t : GriffithsSpace) : ℂ × ℝ)
    rw [F.apply_one]; rfl)
  prop' := fun s t ht => Subtype.ext (by
    rcases ht with rfl | rfl
    · show grifR ((F (s, 0) : GriffithsSpace) : ℂ × ℝ) = grifR ((γ 0 : GriffithsSpace) : ℂ × ℝ)
      rw [F.source, γ.source]
    · show grifR ((F (s, 1) : GriffithsSpace) : ℂ × ℝ) = grifR ((γ 1 : GriffithsSpace) : ℂ × ℝ)
      rw [F.target, γ.target]) }⟩

theorem grifTheta_conj (p q : Path grifK0 grifK0) :
    grifTheta ((p.trans q).trans p.symm) = grifTheta q := by
  rw [grifTheta_trans, grifTheta_trans]
  have h : grifTheta p * grifTheta p.symm = 1 := by
    rw [← grifTheta_trans, grifTheta_homotopic (Path.Homotopic.trans_symm p)]
    exact grifTheta_of_HEA fun _ => zero_mem_grifHEA
  rw [mul_comm (grifTheta p) (grifTheta q), mul_assoc, h, mul_one]

/-! ### The points and sets of the two gluings -/

/-- The apex of the left cone, in the space. -/
def grifPBG : GriffithsSpace := ⟨grifPB, Or.inr grifPB_mem⟩

/-- The point at height `1/2` on the axis of the right cone. -/
def grifQAG : GriffithsSpace :=
  ⟨grifKapA 0 (1 / 2), Or.inl ⟨0, zero_mem_grifHEA, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩⟩

/-- The point at height `1/2` on the axis of the left cone. -/
def grifQBG : GriffithsSpace :=
  ⟨grifKapB 0 (1 / 2), Or.inr ⟨0, zero_mem_grifHEB, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩⟩

theorem grifR_QA : grifR ((grifQAG : GriffithsSpace) : ℂ × ℝ) = 0 :=
  grifR_kapA (by simp) (by norm_num) (by norm_num)

theorem grifR_QB : grifR ((grifQBG : GriffithsSpace) : ℂ × ℝ) = 0 :=
  grifR_kapB (by simp) (by norm_num) (by norm_num)

theorem grifR_X0 : grifR ((grifX0 : GriffithsSpace) : ℂ × ℝ) = 0 := grifR_zero_height 0

/-- The space minus the left apex. -/
def grifU2 : Set GriffithsSpace := {y | y ≠ grifPBG}

/-- The space minus the left apex, as a space (the first gluing happens there). -/
abbrev GrifY1 : Type := ↥grifU2

theorem grif_ne_PB_of_lt {y : GriffithsSpace} (h : (y : ℂ × ℝ).2 < 1) : y ≠ grifPBG :=
  fun e => by rw [e] at h; simp [grifPBG, grifPB, grifKapB] at h

def grifQA1 : GrifY1 := ⟨grifQAG, grif_ne_PB_of_lt (by simp [grifQAG, grifKapA]; norm_num)⟩

def grifQB1 : GrifY1 := ⟨grifQBG, grif_ne_PB_of_lt (by simp [grifQBG, grifKapB]; norm_num)⟩

/-- First gluing, `U`: below the apexes. -/
def grifU1 : Set GrifY1 := {y | (((y : GriffithsSpace) : ℂ × ℝ)).2 < 1}

/-- First gluing, `V`: the right cone minus the double earring. -/
def grifV1 : Set GrifY1 :=
  {y | ((y : GriffithsSpace) : ℂ × ℝ) ∉ grifConeB ∧ 0 < ((y : GriffithsSpace) : ℂ × ℝ).2}

/-- Second gluing, `V`: the left cone minus the double earring. -/
def grifV2 : Set GriffithsSpace :=
  {y | (y : ℂ × ℝ) ∉ grifConeA ∧ 0 < (y : ℂ × ℝ).2}

theorem grif_isPathConnected_param {f : ℝ × ℝ → GriffithsSpace} (hf : Continuous f)
    {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) (hne : S.Nonempty) {T : Set GriffithsSpace}
    (h1 : f '' S ⊆ T) (h2 : T ⊆ f '' S) : IsPathConnected T := by
  rw [subset_antisymm h2 h1]; exact (hS.isPathConnected hne).image hf

theorem grif_isPathConnected_sub {T : Set GriffithsSpace} (hT : IsPathConnected T)
    (hTU : T ⊆ grifU2) : IsPathConnected {y : GrifY1 | (y : GriffithsSpace) ∈ T} := by
  obtain ⟨x, hx, hj⟩ := hT
  refine ⟨⟨x, hTU hx⟩, hx, fun {y} hy => ?_⟩
  obtain ⟨γ, hγ⟩ := hj hy
  exact ⟨pathToSub γ (fun t => hTU (hγ t)), hγ⟩

theorem grif_mem_A_of_not_B {y : GriffithsSpace} (h : (y : ℂ × ℝ) ∉ grifConeB) :
    (y : ℂ × ℝ) ∈ grifConeA := y.2.resolve_right h

theorem grif_mem_B_of_not_A {y : GriffithsSpace} (h : (y : ℂ × ℝ) ∉ grifConeA) :
    (y : ℂ × ℝ) ∈ grifConeB := y.2.resolve_left h

theorem grif_not_B_of_A {p : ℂ × ℝ} (hp : p ∈ grifConeA) (h : 0 < p.2) : p ∉ grifConeB :=
  fun hB => by rw [eq_zero_of_mem_grifConeA_of_mem_grifConeB hp hB] at h; exact lt_irrefl _ h

theorem grif_not_A_of_B {p : ℂ × ℝ} (hp : p ∈ grifConeB) (h : 0 < p.2) : p ∉ grifConeA :=
  fun hA => by rw [eq_zero_of_mem_grifConeA_of_mem_grifConeB hA hp] at h; exact lt_irrefl _ h

/-- The right cone minus the earring, between heights in `J`, is a parametrized image. -/
theorem grif_image_A {J : Set ℝ} (hJ0 : ∀ s ∈ J, 0 < s) (hJ1 : ∀ s ∈ J, s ≤ 1) :
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeB ∧ (y : ℂ × ℝ).2 ∈ J} =
      grifPiA '' (Icc (0 : ℝ) 1 ×ˢ J) := by
  ext y
  constructor
  · rintro ⟨hB, hJ⟩
    obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatA (grif_mem_A_of_not_B hB)
    exact ⟨d, ⟨hd1, hd2 ▸ hJ⟩, Subtype.ext hd⟩
  · rintro ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have hs : (grifHatA d).2 = d.2 := grifHatA_snd ⟨(hJ0 _ hd2).le, hJ1 _ hd2⟩
    refine ⟨grif_not_B_of_A (grifHatA_mem d) (hs ▸ hJ0 _ hd2), ?_⟩
    show (grifHatA d).2 ∈ J
    rw [hs]; exact hd2

/-- The left cone minus the earring, between heights in `J`, is a parametrized image. -/
theorem grif_image_B {J : Set ℝ} (hJ0 : ∀ s ∈ J, 0 < s) (hJ1 : ∀ s ∈ J, s ≤ 1) :
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeA ∧ (y : ℂ × ℝ).2 ∈ J} =
      grifPiB '' (Icc (0 : ℝ) 1 ×ˢ J) := by
  ext y
  constructor
  · rintro ⟨hA, hJ⟩
    obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatB (grif_mem_B_of_not_A hA)
    exact ⟨d, ⟨hd1, hd2 ▸ hJ⟩, Subtype.ext hd⟩
  · rintro ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have hs : (grifHatB d).2 = d.2 := grifHatB_snd ⟨(hJ0 _ hd2).le, hJ1 _ hd2⟩
    refine ⟨grif_not_A_of_B (grifHatB_mem d) (hs ▸ hJ0 _ hd2), ?_⟩
    show (grifHatB d).2 ∈ J
    rw [hs]; exact hd2

theorem grif_isPathConnected_A {J : Set ℝ} (hJ : Convex ℝ J) (hne : J.Nonempty)
    (hJ0 : ∀ s ∈ J, 0 < s) (hJ1 : ∀ s ∈ J, s ≤ 1) :
    IsPathConnected {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeB ∧ (y : ℂ × ℝ).2 ∈ J} := by
  rw [grif_image_A hJ0 hJ1]
  obtain ⟨s, hs⟩ := hne
  exact (((convex_Icc 0 1).prod hJ).isPathConnected
    (⟨(0, s), ⟨le_rfl, zero_le_one⟩, hs⟩ : (Icc (0 : ℝ) 1 ×ˢ J).Nonempty)).image continuous_grifPiA

theorem grif_isPathConnected_B {J : Set ℝ} (hJ : Convex ℝ J) (hne : J.Nonempty)
    (hJ0 : ∀ s ∈ J, 0 < s) (hJ1 : ∀ s ∈ J, s ≤ 1) :
    IsPathConnected {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeA ∧ (y : ℂ × ℝ).2 ∈ J} := by
  rw [grif_image_B hJ0 hJ1]
  obtain ⟨s, hs⟩ := hne
  exact (((convex_Icc 0 1).prod hJ).isPathConnected
    (⟨(0, s), ⟨le_rfl, zero_le_one⟩, hs⟩ : (Icc (0 : ℝ) 1 ×ˢ J).Nonempty)).image continuous_grifPiB

/-! ### The first gluing, across the right apex -/

theorem grifRP_trans {a b c : GriffithsSpace} (γ : Path a b) (γ' : Path b c) hγ hγ' h ha hb hc :
    grifRP (γ.trans γ') h ha hc = (grifRP γ hγ ha hb).trans (grifRP γ' hγ' hb hc) := by
  refine Path.ext (funext fun t => Subtype.ext ?_)
  rw [grifRP_apply]
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem grif_isOpen_U1 : IsOpen grifU1 :=
  isOpen_lt (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
    continuous_const

theorem grif_isOpen_V1 : IsOpen grifV1 :=
  (isClosed_grifConeB.isOpen_compl.inter (isOpen_lt continuous_const continuous_snd)).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

theorem grif_snd_le_one (y : GriffithsSpace) : (y : ℂ × ℝ).2 ≤ 1 := (grifSet_snd y.2).2

theorem grif_cover1 (y : GrifY1) : y ∈ grifU1 ∨ y ∈ grifV1 := by
  by_cases h : (((y : GriffithsSpace) : ℂ × ℝ)).2 < 1
  · exact Or.inl h
  · right
    have h1 : (((y : GriffithsSpace) : ℂ × ℝ)).2 = 1 :=
      le_antisymm (grif_snd_le_one _) (not_lt.1 h)
    have hA : ((y : GriffithsSpace) : ℂ × ℝ) ∈ grifConeA := by
      rcases (y : GriffithsSpace).2 with hA | hB
      · exact hA
      · exact absurd (Subtype.ext (eq_grifPB_of_snd hB h1)) y.2
    exact ⟨grif_not_B_of_A hA (by rw [h1]; exact one_pos), by rw [h1]; exact one_pos⟩

theorem grifQA_mem_A : ((grifQAG : GriffithsSpace) : ℂ × ℝ) ∈ grifConeA :=
  ⟨0, zero_mem_grifHEA, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem grifQB_mem_B : ((grifQBG : GriffithsSpace) : ℂ × ℝ) ∈ grifConeB :=
  ⟨0, zero_mem_grifHEB, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem grifQA_snd : ((grifQAG : GriffithsSpace) : ℂ × ℝ).2 = 1 / 2 := rfl

theorem grifQB_snd : ((grifQBG : GriffithsSpace) : ℂ × ℝ).2 = 1 / 2 := rfl

theorem grifQA1_mem : grifQA1 ∈ grifU1 ∩ grifV1 :=
  ⟨(by norm_num : (1 / 2 : ℝ) < 1),
    grif_not_B_of_A grifQA_mem_A (show (0 : ℝ) < 1 / 2 by norm_num),
    (by norm_num : (0 : ℝ) < 1 / 2)⟩

theorem grifQB1_mem : grifQB1 ∈ grifU1 := (by norm_num : (1 / 2 : ℝ) < 1)

theorem grif_isPathConnected_U1 : IsPathConnected grifU1 :=
  grif_isPathConnected_sub grif_isPathConnected_below fun _ hy => grif_ne_PB_of_lt hy

theorem grif_V1_eq : grifV1 = {y : GrifY1 | (y : GriffithsSpace) ∈
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeB ∧ (y : ℂ × ℝ).2 ∈ Ioc (0 : ℝ) 1}} := by
  ext y
  exact ⟨fun h => ⟨h.1, h.2, grif_snd_le_one _⟩, fun h => ⟨h.1, h.2.1⟩⟩

theorem grif_W1_eq : grifU1 ∩ grifV1 = {y : GrifY1 | (y : GriffithsSpace) ∈
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeB ∧ (y : ℂ × ℝ).2 ∈ Ioo (0 : ℝ) 1}} := by
  ext y
  exact ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩

theorem grif_isPathConnected_V1 : IsPathConnected grifV1 := by
  rw [grif_V1_eq]
  refine grif_isPathConnected_sub (grif_isPathConnected_A (convex_Ioc 0 1) ⟨1, by norm_num,
    le_rfl⟩ (fun s hs => hs.1) (fun s hs => hs.2)) fun y hy => ?_
  intro e
  rw [e] at hy
  exact hy.1 grifPB_mem

theorem grif_isPathConnected_W1 : IsPathConnected (grifU1 ∩ grifV1) := by
  rw [grif_W1_eq]
  refine grif_isPathConnected_sub (grif_isPathConnected_A (convex_Ioo 0 1) ⟨1 / 2, by norm_num,
    by norm_num⟩ (fun s hs => hs.1) (fun s hs => hs.2.le)) fun y hy => ?_
  exact grif_ne_PB_of_lt hy.2.2

/-- The invariant of the first gluing: the linking matrix of the retraction. -/
def grifF1 (γ : Path grifQA1 grifQA1) : Multiplicative GrifQ :=
  if h : ∀ t, γ t ∈ grifU1 then
    grifTheta (grifRP (γ.map continuous_subtype_val) (fun t => h t) grifR_QA grifR_QA)
  else 1

theorem grifF1_eq (γ : Path grifQA1 grifQA1) (h : ∀ t, γ t ∈ grifU1) :
    grifF1 γ = grifTheta (grifRP (γ.map continuous_subtype_val) (fun t => h t) grifR_QA
      grifR_QA) := by
  unfold grifF1; rw [dif_pos h]

theorem grifF1_hom (γ γ' : Path grifQA1 grifQA1) (hh : HomotopicIn grifU1 γ γ') :
    grifF1 γ = grifF1 γ' := by
  have h₁ := hh.mem_left
  have h₂ := hh.mem_right
  obtain ⟨F, hF⟩ := hh
  unfold grifF1
  rw [dif_pos h₁, dif_pos h₂]
  exact grifTheta_homotopic (grifRP_homotopic (F.map ⟨Subtype.val, continuous_subtype_val⟩)
    (fun z => hF z) _ _ _ _)

theorem grifF1_trans (γ γ' : Path grifQA1 grifQA1) (h₁ : ∀ t, γ t ∈ grifU1)
    (h₂ : ∀ t, γ' t ∈ grifU1) : grifF1 (γ.trans γ') = grifF1 γ * grifF1 γ' := by
  unfold grifF1
  rw [dif_pos (VanKampen.mem_trans h₁ h₂), dif_pos h₁, dif_pos h₂, ← grifTheta_trans]
  congr 1
  rw [grifRP_congr ((γ.trans γ').map continuous_subtype_val)
    ((γ.map continuous_subtype_val).trans (γ'.map continuous_subtype_val)) _
    (VanKampen.mem_trans (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1}) (fun t => h₁ t)
      (fun t => h₂ t)) grifR_QA grifR_QA grifR_QA grifR_QA (fun t => by rw [Path.map_trans])]
  exact grifRP_trans (γ.map continuous_subtype_val) (γ'.map continuous_subtype_val)
    (fun t => h₁ t) (fun t => h₂ t) _ grifR_QA grifR_QA grifR_QA

theorem grifF1_agree (γ : Path grifQA1 grifQA1) (h₁ : ∀ t, γ t ∈ grifU1)
    (h₂ : ∀ t, γ t ∈ grifV1) : grifF1 γ = 1 := by
  unfold grifF1
  rw [dif_pos h₁]
  refine grifTheta_of_HEA fun t => ?_
  rw [grifRP_apply]
  exact (grifConeA_lt (grif_mem_A_of_not_B (h₂ t).1) (h₁ t)).1

/-- **The first gluing**: `U` below the apexes, `V` the right cone minus the earring. -/
def grifD1 : VanKampen.Data GrifY1 (Multiplicative GrifQ) :=
  grifMkData grifU1 grifV1 grif_isOpen_U1 grif_isOpen_V1 grif_cover1 grifQA1 grifQA1_mem
    grif_isPathConnected_U1 grif_isPathConnected_V1 grif_isPathConnected_W1 grifF1 grifF1_hom
    grifF1_trans grifF1_agree

theorem grifD1_x₀ : grifD1.x₀ = grifQA1 := rfl

/-! ### The second gluing, across the left apex -/

theorem grif_isOpen_U2 : IsOpen grifU2 := isOpen_ne

theorem grif_isOpen_V2 : IsOpen grifV2 :=
  (isClosed_grifConeA.isOpen_compl.inter (isOpen_lt continuous_const continuous_snd)).preimage
    continuous_subtype_val

theorem grif_cover2 (y : GriffithsSpace) : y ∈ grifU2 ∨ y ∈ grifV2 := by
  by_cases h : y = grifPBG
  · subst h
    exact Or.inr ⟨grifPB_not_mem_grifConeA, by simp [grifPBG, grifPB, grifKapB]⟩
  · exact Or.inl h

theorem grifQB_mem2 : grifQBG ∈ grifU2 ∩ grifV2 :=
  ⟨grif_ne_PB_of_lt (by rw [grifQB_snd]; norm_num),
    grif_not_A_of_B grifQB_mem_B (by rw [grifQB_snd]; norm_num),
    by show 0 < ((grifQBG : GriffithsSpace) : ℂ × ℝ).2; rw [grifQB_snd]; norm_num⟩

theorem grif_isPathConnected_U2 : IsPathConnected grifU2 := by
  have hSA : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Icc 0 1)
  have hSB : Convex ℝ (Icc (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := (convex_Icc 0 1).prod (convex_Ico 0 1)
  refine ⟨grifX0, grif_ne_PB_of_lt (by simp [grifX0]), fun {y} hy => ?_⟩
  rcases y.2 with hA | hB
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatA hA
    have : y = grifPiA d := Subtype.ext hd.symm
    rw [this, ← grifPiA_zero]
    refine grif_joinedIn_of_convex continuous_grifPiA hSA ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl,
      zero_le_one⟩⟩ ⟨hd1, hd2 ▸ grifSet_snd (Or.inl hA)⟩ ?_
    rintro _ ⟨d', -, rfl⟩ e
    have : grifHatA d' = grifPB := congrArg Subtype.val e
    exact grifPB_not_mem_grifConeA (this ▸ grifHatA_mem d')
  · obtain ⟨d, hd1, hd2, hd⟩ := exists_grifHatB hB
    have hlt : (y : ℂ × ℝ).2 < 1 := lt_of_le_of_ne (grif_snd_le_one y) fun h1 =>
      hy (Subtype.ext (eq_grifPB_of_snd hB h1))
    have : y = grifPiB d := Subtype.ext hd.symm
    rw [this, ← grifPiB_zero]
    refine grif_joinedIn_of_convex continuous_grifPiB hSB ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl,
      zero_lt_one⟩⟩ ⟨hd1, hd2 ▸ (grifSet_snd (Or.inr hB)).1, hd2 ▸ hlt⟩ ?_
    rintro _ ⟨d', ⟨-, hd'⟩, rfl⟩
    refine grif_ne_PB_of_lt ?_
    show (grifHatB d').2 < 1
    rw [grifHatB_snd ⟨hd'.1, hd'.2.le⟩]; exact hd'.2

theorem grif_V2_eq : grifV2 =
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeA ∧ (y : ℂ × ℝ).2 ∈ Ioc (0 : ℝ) 1} := by
  ext y
  exact ⟨fun h => ⟨h.1, h.2, grif_snd_le_one _⟩, fun h => ⟨h.1, h.2.1⟩⟩

theorem grif_W2_eq : grifU2 ∩ grifV2 =
    {y : GriffithsSpace | (y : ℂ × ℝ) ∉ grifConeA ∧ (y : ℂ × ℝ).2 ∈ Ioo (0 : ℝ) 1} := by
  ext y
  constructor
  · rintro ⟨hne, hA, hpos⟩
    refine ⟨hA, hpos, lt_of_le_of_ne (grif_snd_le_one y) fun h1 => hne ?_⟩
    exact Subtype.ext (eq_grifPB_of_snd (grif_mem_B_of_not_A hA) h1)
  · rintro ⟨hA, hpos, hlt⟩
    exact ⟨grif_ne_PB_of_lt hlt, hA, hpos⟩

theorem grif_isPathConnected_V2 : IsPathConnected grifV2 := by
  rw [grif_V2_eq]
  exact grif_isPathConnected_B (convex_Ioc 0 1) ⟨1, by norm_num, le_rfl⟩ (fun s hs => hs.1)
    (fun s hs => hs.2)

theorem grif_isPathConnected_W2 : IsPathConnected (grifU2 ∩ grifV2) := by
  rw [grif_W2_eq]
  exact grif_isPathConnected_B (convex_Ioo 0 1) ⟨1 / 2, by norm_num, by norm_num⟩
    (fun s hs => hs.1) (fun s hs => hs.2.le)

/-- A path of the space minus the left apex, below the apexes, from `q_A` to `q_B`. -/
def grifC1 : Path grifQA1 grifQB1 :=
  (grif_isPathConnected_U1.joinedIn grifQA1 grifQA1_mem.1 grifQB1 grifQB1_mem).somePath

theorem grifC1_mem (t : I) : grifC1 t ∈ grifU1 :=
  (grif_isPathConnected_U1.joinedIn grifQA1 grifQA1_mem.1 grifQB1 grifQB1_mem).somePath_mem t

/-- `grifC1` in the space. -/
def grifC1G : Path grifQAG grifQBG where
  toFun t := (grifC1 t : GriffithsSpace)
  continuous_toFun := continuous_subtype_val.comp grifC1.continuous
  source' := congrArg Subtype.val grifC1.source
  target' := congrArg Subtype.val grifC1.target

theorem grifC1G_lt (t : I) : ((grifC1G t : GriffithsSpace) : ℂ × ℝ).2 < 1 := grifC1_mem t

/-- A loop at `q_B` avoiding the left apex, as a loop of the space minus that apex. -/
def grifSub (γ : Path grifQBG grifQBG) (h : ∀ t, γ t ∈ grifU2) : Path grifQB1 grifQB1 where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

theorem grifSub_apply (γ : Path grifQBG grifQBG) (h : ∀ t, γ t ∈ grifU2) (t : I) :
    ((grifSub γ h t : GrifY1) : GriffithsSpace) = γ t := rfl

theorem grifSub_homotopic {γ γ' : Path grifQBG grifQBG} (hh : HomotopicIn grifU2 γ γ')
    (h₁ : ∀ t, γ t ∈ grifU2) (h₂ : ∀ t, γ' t ∈ grifU2) :
    (grifSub γ h₁).Homotopic (grifSub γ' h₂) := by
  obtain ⟨F, hF⟩ := hh
  exact ⟨{
    toFun := fun z => ⟨F z, hF z⟩
    continuous_toFun := F.continuous.subtype_mk _
    map_zero_left := fun t => Subtype.ext (F.apply_zero t)
    map_one_left := fun t => Subtype.ext (F.apply_one t)
    prop' := fun s t ht => Subtype.ext (by
      rcases ht with rfl | rfl
      · exact (F.source s).trans γ.source.symm
      · exact (F.target s).trans γ.target.symm) }⟩

theorem grifSub_trans (γ γ' : Path grifQBG grifQBG) (h₁ : ∀ t, γ t ∈ grifU2)
    (h₂ : ∀ t, γ' t ∈ grifU2) (h : ∀ t, (γ.trans γ') t ∈ grifU2) :
    grifSub (γ.trans γ') h = (grifSub γ h₁).trans (grifSub γ' h₂) :=
  Path.ext (funext fun t => Subtype.ext (by
    show (γ.trans γ') t = (((grifSub γ h₁).trans (grifSub γ' h₂)) t : GriffithsSpace)
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs <;> rfl))

/-- The invariant of the second gluing: the first glued invariant, conjugated to `q_A`. -/
def grifF2 (γ : Path grifQBG grifQBG) : Multiplicative GrifQ :=
  if h : ∀ t, γ t ∈ grifU2 then grifD1.Φ ((grifC1.trans (grifSub γ h)).trans grifC1.symm)
  else 1

theorem grifF2_hom (γ γ' : Path grifQBG grifQBG) (hh : HomotopicIn grifU2 γ γ') :
    grifF2 γ = grifF2 γ' := by
  have h₁ := hh.mem_left
  have h₂ := hh.mem_right
  unfold grifF2
  rw [dif_pos h₁, dif_pos h₂]
  obtain ⟨F⟩ := ((Path.Homotopic.refl grifC1).hcomp (grifSub_homotopic hh h₁ h₂)).hcomp
    (Path.Homotopic.refl grifC1.symm)
  exact grifD1.Φ_homotopic F

theorem grifF2_trans (γ γ' : Path grifQBG grifQBG) (h₁ : ∀ t, γ t ∈ grifU2)
    (h₂ : ∀ t, γ' t ∈ grifU2) : grifF2 (γ.trans γ') = grifF2 γ * grifF2 γ' := by
  have h₁₂ := VanKampen.mem_trans h₁ h₂
  unfold grifF2
  rw [dif_pos h₁₂, dif_pos h₁, dif_pos h₂, ← grifD1.Φ_trans, grifSub_trans γ γ' h₁ h₂ h₁₂]
  have hh : ((grifC1.trans ((grifSub γ h₁).trans (grifSub γ' h₂))).trans grifC1.symm).Homotopic
      (((grifC1.trans (grifSub γ h₁)).trans grifC1.symm).trans
        ((grifC1.trans (grifSub γ' h₂)).trans grifC1.symm)) := by
    rw [← Path.Homotopic.Quotient.eq]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk grifC1.symm),
      ← Path.Homotopic.Quotient.mk_trans grifC1.symm grifC1,
      Path.Homotopic.Quotient.eq.2 (Path.Homotopic.symm_trans grifC1),
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]
  obtain ⟨F⟩ := hh
  exact grifD1.Φ_homotopic F

theorem grif_lt_of_U2_V2 {y : GriffithsSpace} (hU : y ∈ grifU2) (hV : y ∈ grifV2) :
    (y : ℂ × ℝ).2 < 1 := by
  have := (grif_W2_eq ▸ (⟨hU, hV⟩ : y ∈ grifU2 ∩ grifV2) : y ∈ {y : GriffithsSpace |
    (y : ℂ × ℝ) ∉ grifConeA ∧ (y : ℂ × ℝ).2 ∈ Ioo (0 : ℝ) 1})
  exact this.2.2

theorem grifF2_agree (γ : Path grifQBG grifQBG) (h₁ : ∀ t, γ t ∈ grifU2)
    (h₂ : ∀ t, γ t ∈ grifV2) : grifF2 γ = 1 := by
  unfold grifF2
  rw [dif_pos h₁]
  have hγU1 : ∀ t, grifSub γ h₁ t ∈ grifU1 := fun t => grif_lt_of_U2_V2 (h₁ t) (h₂ t)
  have hM : ∀ t, ((grifC1.trans (grifSub γ h₁)).trans grifC1.symm) t ∈ grifU1 :=
    VanKampen.mem_trans (VanKampen.mem_trans grifC1_mem hγU1) (VanKampen.mem_symm grifC1_mem)
  refine (grifD1.Φ_of_mem (b := true)
    (γ := ((grifC1.trans (grifSub γ h₁)).trans grifC1.symm)) hM).trans ?_
  refine (grifF1_eq ((grifC1.trans (grifSub γ h₁)).trans grifC1.symm) hM).trans ?_
  have hc : ∀ t, ((grifC1G t : GriffithsSpace) : ℂ × ℝ).2 < 1 := grifC1G_lt
  have hγ' : ∀ t, ((γ t : GriffithsSpace) : ℂ × ℝ).2 < 1 := fun t =>
    grif_lt_of_U2_V2 (h₁ t) (h₂ t)
  rw [grifRP_congr _ ((grifC1G.trans γ).trans grifC1G.symm) _ ?_ _ _ grifR_QA grifR_QA ?_]
  · rw [grifRP_conj _ _ hc hγ' grifR_QA grifR_QB, grifTheta_conj]
    refine grifTheta_of_HEB fun t => ?_
    rw [grifRP_apply]
    exact (grifConeB_lt (grif_mem_B_of_not_A (h₂ t).1) (hγ' t)).1
  · exact VanKampen.mem_trans (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1})
      (VanKampen.mem_trans (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1}) hc hγ')
      (VanKampen.mem_symm (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1}) hc)
  · intro t
    show (((grifC1.trans (grifSub γ h₁)).trans grifC1.symm) t : GriffithsSpace) = _
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> rfl

/-- **The second gluing**: `U` the space minus the left apex, `V` the left cone minus the
earring. -/
def grifD2 : VanKampen.Data GriffithsSpace (Multiplicative GrifQ) :=
  grifMkData grifU2 grifV2 grif_isOpen_U2 grif_isOpen_V2 grif_cover2 grifQBG grifQB_mem2
    grif_isPathConnected_U2 grif_isPathConnected_V2 grif_isPathConnected_W2 grifF2 grifF2_hom
    grifF2_trans grifF2_agree

/-! ### The loops `∏ aₙ bₙ` are not null-homotopic -/

/-- The double earring in the space, at height `0`. -/
def grifIotaK (q : GrifK) : GriffithsSpace :=
  ⟨((q : ℂ), (0 : ℝ)), grif_mem_grifSet_of_mem_grifK q.2⟩

theorem continuous_grifIotaK : Continuous grifIotaK :=
  (continuous_subtype_val.prodMk continuous_const).subtype_mk _

/-- **The loops `∏_{n ≥ N} aₙ bₙ` are not null-homotopic** in the Griffiths twin cone. -/
theorem griffiths_omega_not_homotopic {N : ℕ} (hN : 0 < N) :
    ¬ ((grifOmegaK N hN).map continuous_grifIotaK).Homotopic (Path.refl _) := by
  intro hω
  set ωG := (grifOmegaK N hN).map continuous_grifIotaK with hωG
  have hqB : grifQBG ∈ {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1} :=
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hx0m : grifIotaK grifK0 ∈ {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1} :=
    (one_pos : (0 : ℝ) < 1)
  obtain ⟨c2, hc2⟩ := grif_isPathConnected_below.joinedIn grifQBG hqB _ hx0m
  have hωm : ∀ t, ((ωG t : GriffithsSpace) : ℂ × ℝ).2 < 1 := fun _ => (one_pos : (0 : ℝ) < 1)
  have hLlt : ∀ t, ((((c2.trans ωG).trans c2.symm) t : GriffithsSpace) : ℂ × ℝ).2 < 1 :=
    VanKampen.mem_trans (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1})
      (VanKampen.mem_trans hc2 hωm) (VanKampen.mem_symm hc2)
  have hLU : ∀ t, ((c2.trans ωG).trans c2.symm) t ∈ grifU2 := fun t => grif_ne_PB_of_lt (hLlt t)
  have hLnull : ((c2.trans ωG).trans c2.symm).Homotopic (Path.refl grifQBG) := by
    have hq : Path.Homotopic.Quotient.mk ωG = Path.Homotopic.Quotient.mk (Path.refl _) :=
      Path.Homotopic.Quotient.eq.2 hω
    rw [← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_trans, hq, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.trans_refl, ← Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.eq.2 (Path.Homotopic.trans_symm c2)]
  obtain ⟨F⟩ := hLnull
  have e1 := grifD2.Φ_homotopic F
  have e2 : grifD2.Φ (Path.refl grifQBG) = 1 :=
    grifD2.Φ_of_mem (b := false) (fun _ => grifQB_mem2.2)
  have e3 : grifD2.Φ ((c2.trans ωG).trans c2.symm) = grifF2 ((c2.trans ωG).trans c2.symm) :=
    grifD2.Φ_of_mem (b := true) hLU
  unfold grifF2 at e3
  rw [dif_pos hLU] at e3
  have hMU : ∀ t, ((grifC1.trans (grifSub ((c2.trans ωG).trans c2.symm) hLU)).trans
      grifC1.symm) t ∈ grifU1 :=
    VanKampen.mem_trans (VanKampen.mem_trans grifC1_mem (fun t => hLlt t))
      (VanKampen.mem_symm grifC1_mem)
  have e4 := (grifD1.Φ_of_mem (b := true) hMU).trans (grifF1_eq _ hMU)
  have hc1 : ∀ t, ((grifC1G t : GriffithsSpace) : ℂ × ℝ).2 < 1 := grifC1G_lt
  have e5 : grifTheta (grifRP ((grifC1.trans (grifSub ((c2.trans ωG).trans c2.symm) hLU)).trans
      grifC1.symm |>.map continuous_subtype_val) (fun t => hMU t) grifR_QA grifR_QA) =
      grifTheta (grifOmegaK N hN) := by
    rw [grifRP_congr _ ((grifC1G.trans ((c2.trans ωG).trans c2.symm)).trans grifC1G.symm) _
      (VanKampen.mem_trans (S := {y : GriffithsSpace | (y : ℂ × ℝ).2 < 1})
        (VanKampen.mem_trans hc1 hLlt) (VanKampen.mem_symm hc1)) _ _ grifR_QA grifR_QA ?_]
    · rw [grifRP_conj _ _ hc1 hLlt grifR_QA grifR_QB, grifTheta_conj,
        grifRP_conj c2 ωG hc2 hωm grifR_QB grifR_X0, grifTheta_conj]
      congr 1
      refine Path.ext (funext fun t => Subtype.ext ?_)
      rw [grifRP_apply]
      exact grifR_zero_height _
    · intro t
      have hS : ∀ u, ((grifSub ((c2.trans ωG).trans c2.symm) hLU u : GrifY1) : GriffithsSpace) =
          ((c2.trans ωG).trans c2.symm) u := fun _ => rfl
      show (((grifC1.trans (grifSub ((c2.trans ωG).trans c2.symm) hLU)).trans grifC1.symm) t :
        GriffithsSpace) = _
      simp only [Path.trans_apply, Path.symm_apply,
        apply_dite (Subtype.val : GrifY1 → GriffithsSpace), hS]
      split_ifs <;> rfl
  exact grifTheta_omega_ne_one hN (e5.symm.trans (e4.symm.trans (e3.symm.trans (e1.trans e2))))

/-! ### The counterexample -/

/-- **Semi-locally simply connected in itself**, literal form (DEC-55). -/
theorem griffiths_isSLSCInCC : IsSLSCInCC (univ : Set GriffithsSpace) :=
  griffiths_isSLSCIn.isSLSCInCC

/-- **The Griffiths twin cone is not semi-locally simply connected**: every neighbourhood of
the earrings' common point contains a loop `∏_{n ≥ N} aₙ bₙ` which is not null-homotopic. -/
theorem griffiths_not_semilocallySimplyConnected :
    ¬ SemilocallySimplyConnected GriffithsSpace := by
  intro h
  obtain ⟨U, hU, hloop⟩ := h grifX0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hNr : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hNr
  refine griffiths_omega_not_homotopic hNpos
    (hloop ((grifOmegaK N hNpos).map continuous_grifIotaK) fun t => hball ?_)
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
  show ‖(((grifOmegaK N hNpos t : GrifK) : ℂ), (0 : ℝ)) - ((0 : ℂ), (0 : ℝ))‖ < ε
  rw [Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_mk, norm_zero,
    max_eq_left (norm_nonneg _)]
  refine (norm_grifOmegaK_le hNpos t).trans_lt ?_
  rw [div_lt_iff₀ hNr]
  rw [div_lt_iff₀ hε] at hN
  linarith

/-- **`rem:definition_semi_locally_simply_connected`, the converse is false, compactly**: the
Griffiths twin cone is compact, Hausdorff, path-connected and locally path-connected (a Peano
continuum), semi-locally simply connected in itself in the literal sense of
`def:semi_locally_simple_connectedness` (DEC-55) and in its homotopy form, and not semi-locally
simply connected. -/
theorem griffiths_counterexample :
    CompactSpace GriffithsSpace ∧ T2Space GriffithsSpace ∧ PathConnectedSpace GriffithsSpace ∧
      LocPathConnectedSpace GriffithsSpace ∧ IsSLSCInCC (univ : Set GriffithsSpace) ∧
        IsSLSCIn (univ : Set GriffithsSpace) ∧ ¬ SemilocallySimplyConnected GriffithsSpace :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, griffiths_isSLSCInCC,
    griffiths_isSLSCIn, griffiths_not_semilocallySimplyConnected⟩

/-- `rem:definition_semi_locally_simply_connected` as printed is false even for compact spaces:
"slsc in itself ⇒ slsc" fails for a compact Hausdorff connected locally path-connected `X`
(the Griffiths twin cone). -/
theorem not_semilocallySimplyConnected_of_isSLSCInCC_univ_compact :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [LocPathConnectedSpace X]
      [CompactSpace X], IsSLSCInCC (univ : Set X) → SemilocallySimplyConnected X :=
  fun h => griffiths_not_semilocallySimplyConnected (h GriffithsSpace griffiths_isSLSCInCC)

end GX
