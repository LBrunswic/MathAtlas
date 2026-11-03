import Causal.Flat.GromovBase

/-!
# `Causal.Flat.GromovUnbounded` — no loxodromic element and an unbounded orbit: a fixed null vector

The unbounded half of Gromov's classification for `SO₀(1, d)` acting on `ℍᵈ` (DEC-111): a subgroup
`G ≤ lorentz d` with no loxodromic element and an unbounded orbit of `o` fixes a nonzero null
vector. **No ledger label is certified here**: the module is a step of `Flat/GromovProof`, which
discharges the external `BenoistNoLox` of `bprop:sanloxo` (`GHFspace.tex:2573`).

> If $\Gamma$ does not contain loxodromic elements, it is elementary; i.e., up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), or its linear part
> stabilizes an isotropic vector. (l.2575–2577)

The paper's `Γ` is a subgroup of the isometry group of Minkowski space with linear part
`L(Γ) ≤ SO₀(1, n−1)`; the Lean object is the linear group `G ≤ lorentz d` itself.

The argument is uniform — no case split on parabolic elements, no finitely generated
subgroups, no discreteness, and the all-elliptic unbounded ("horocyclic") case needs nothing
separate:

1. `exists_fixed_slice_of_not_isLoxodromic`: a non-loxodromic `A` fixes a point `x` of the slice
   (a fixed timelike vector, or a null eigenvector of eigenvalue `1`, by
   `lorentz.exists_null_eigen_or_fixed_timelike` and `isLoxodromic_of_null_eigen`).
2. **`norm_orbitPt_sub_inv_sq_le`** (the one-element estimate): then
   `−⟨orbitPt A | x⟩ = −⟨orbitPt A⁻¹ | x⟩ = 1 / orbitCosh A` exactly (`⟨A o | x⟩ = ⟨o | A⁻¹x⟩`),
   and on the slice `−⟨p | x⟩ = 1 − ⟪p.2, x.2⟫ ≥ ‖p.2 − x.2‖² / 2`, so
   `‖(orbitPt A).2 − (orbitPt A⁻¹).2‖² ≤ 8 / orbitCosh A`: a far-moving non-loxodromic element
   attracts and repels towards the same point at infinity. The exact identity is
   `neg_minkB_orbitPt_of_fixed`.
3. A sequence `g n ∈ G` with `orbitCosh (g n) → ∞` has, by compactness of the slice, a
   subsequence with `orbitPt (g n) → ξ`; by 2, `orbitPt (g n)⁻¹ → ξ` too, and `ξ` is a future
   null vector with `ξ.1 = 1` (`limit_mem_sphere`).
4. For `a ∈ G`: `orbitPt (a * g n) → toSlice (a ξ)` and `orbitCosh (a * g n) → ∞` (exact formulas
   `orbitPt_mul`, `orbitCosh_mul`), while `orbitPt (a * g n)⁻¹ = toSlice ((g n)⁻¹ (a⁻¹ o)) → ξ`
   (the rank-one estimate for `(g n)⁻¹`, `(g n)⁻¹ (a⁻¹ o)).1 → ∞` since `−⟨a⁻¹o | ξ⟩ > 0`).
   By 2 applied to `a * g n ∈ G`, `toSlice (a ξ) = ξ`: `a ξ = (a ξ).1 • ξ`, and
   `(a ξ).1 ≠ 1` would make `a` loxodromic (`isLoxodromic_of_null_eigen`). So `a ξ = ξ`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| linear part `L(Γ) ≤ SO₀(1, n−1)` (l.2576) | ✓ carried: `G : Subgroup (lorentz d)` |
| no loxodromic element | ✓ carried |
| (case of the proof) an unbounded orbit | ✓ the case hypothesis `∀ M, ∃ A ∈ G, M < orbitCosh A` |
| "up to finite index, … its linear part stabilizes an isotropic vector" (l.2576–2577) | ⚠ weakened (stronger conclusion): `G` itself fixes a nonzero null vector |

## SCOPE (disclosed)

* Not Barbot's proof (Zariski closure + Benoist, l.2580–2597): Gromov's horocyclic/focal step,
  specialised to `SO₀(1, d)`, where the only loxodromic test needed is a null eigenvector of
  eigenvalue `≠ 1`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-111 (Gromov route). Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

open Filter Topology

variable {d : ℕ}

/-- **Step 1.** A non-loxodromic element of `SO₀(1, d)` fixes a point of the slice. -/
theorem exists_fixed_slice_of_not_isLoxodromic (A : lorentz d)
    (hA : ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ x ∈ slice d, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) x = x := by
  have key : ∃ u : Minkowski d, u ≠ 0 ∧ minkQ u ≤ 0 ∧
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) u = u := by
    rcases lorentz.exists_null_eigen_or_fixed_timelike A.2 with ⟨u, hu0, hq, c, hc⟩ | ⟨v, hv, hAv⟩
    · have hcpos := lorentz.eigen_pos_of_null A.2 hu0 hq hc
      by_cases hc1 : c = 1
      · exact ⟨u, hu0, hq.le, by rw [hc, hc1, one_smul]⟩
      · exact absurd (isLoxodromic_of_null_eigen A.2 hu0 hq hcpos hc1 hc) hA
    · refine ⟨v, fun h => ?_, hv.le, hAv⟩
      rw [h] at hv
      simp [minkQ] at hv
  obtain ⟨u, hu0, hq, hAu⟩ := key
  have hu1 : u.1 ≠ 0 := fun h => hu0 (eq_zero_of_fst_eq_zero h hq)
  refine ⟨toSlice u, ⟨toSlice_fst hu1, ?_⟩, ?_⟩
  · show ‖(u.1⁻¹ • u).2‖ ≤ 1
    rw [Prod.smul_snd, norm_smul, Real.norm_eq_abs, abs_inv]
    have h : ‖u.2‖ ≤ |u.1| := by
      have := sq_le_sq.1 (minkQ_le_zero_iff.1 hq); rwa [abs_norm] at this
    rw [inv_mul_le_iff₀ (abs_pos.2 hu1), mul_one]
    exact h
  · show (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (u.1⁻¹ • u) = u.1⁻¹ • u
    rw [map_smul, hAu]

/-- On the slice, `−⟨p | x⟩ ≥ ‖p.2 − x.2‖² / 2`. -/
theorem half_norm_sub_sq_le_neg_minkB {p x : Minkowski d} (hp : p ∈ slice d)
    (hx : x ∈ slice d) : ‖p.2 - x.2‖ ^ 2 / 2 ≤ -minkB p x := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hx1, hx2⟩ := hx
  simp only [minkB, hp1, hx1]
  rw [norm_sub_sq_real]
  nlinarith [norm_nonneg p.2, norm_nonneg x.2, pow_le_one₀ (n := 2) (norm_nonneg p.2) hp2,
    pow_le_one₀ (n := 2) (norm_nonneg x.2) hx2]

/-- For `B` fixing a slice point `x`: `−⟨orbitPt B | x⟩ = 1 / cosh d(o, B o)` exactly, since
`⟨B o | x⟩ = ⟨B o | B x⟩ = ⟨o | x⟩ = −x.1`. -/
theorem neg_minkB_orbitPt_of_fixed (B : lorentz d) {x : Minkowski d} (hx1 : x.1 = 1)
    (hBx : (B : Minkowski d ≃ₗ[ℝ] Minkowski d) x = x) :
    -minkB (orbitPt B) x = (orbitCosh B)⁻¹ := by
  have h : minkB ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)) x = -1 := by
    rw [show minkB ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)) x =
        minkB ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d))
          ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) x) by rw [hBx],
      minkB_lorentz_apply, minkB_comm]
    have := fst_eq_neg_minkB_timeUnit x
    linarith
  show -minkB ((orbitCosh B)⁻¹ • (B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)) x = _
  rw [minkB_smul_left, h]
  ring

/-- **Step 2, the one-element estimate.** A non-loxodromic `A` attracts and repels towards the
same point at infinity, up to `8 / cosh d(o, A o)`. -/
theorem norm_orbitPt_sub_inv_sq_le (A : lorentz d)
    (hA : ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ‖(orbitPt A).2 - (orbitPt A⁻¹).2‖ ^ 2 ≤ 8 / orbitCosh A := by
  obtain ⟨x, hx, hAx⟩ := exists_fixed_slice_of_not_isLoxodromic A hA
  have hAx' : ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) x = x := by
    have := lorentz_inv_apply_apply A x
    rwa [hAx] at this
  have h1 := neg_minkB_orbitPt_of_fixed A hx.1 hAx
  have h2 := neg_minkB_orbitPt_of_fixed A⁻¹ hx.1 hAx'
  rw [orbitCosh_inv] at h2
  have ha := half_norm_sub_sq_le_neg_minkB (orbitPt_mem_slice A) hx
  have hb := half_norm_sub_sq_le_neg_minkB (orbitPt_mem_slice A⁻¹) hx
  rw [h1] at ha
  rw [h2] at hb
  have htri := norm_sub_le_norm_sub_add_norm_sub (orbitPt A).2 x.2 (orbitPt A⁻¹).2
  rw [norm_sub_rev x.2] at htri
  have h3 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  rw [div_eq_mul_inv]
  nlinarith [sq_nonneg (‖(orbitPt A).2 - x.2‖ - ‖(orbitPt A⁻¹).2 - x.2‖)]

/-- **Step 3a.** Along `orbitCosh (g n) → ∞`, a limit of `orbitPt (g n)` is a point of the
boundary sphere. -/
theorem limit_mem_sphere {g : ℕ → lorentz d} {ξ : Minkowski d}
    (hc : Tendsto (fun n => orbitCosh (g n)) atTop atTop)
    (hξ : Tendsto (fun n => orbitPt (g n)) atTop (𝓝 ξ)) : ξ.1 = 1 ∧ ‖ξ.2‖ = 1 := by
  have hinv : Tendsto (fun n => (orbitCosh (g n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hc
  have h1 : Tendsto (fun n => ‖(orbitPt (g n)).2‖ ^ 2) atTop (𝓝 (1 - 0 ^ 2)) := by
    simp_rw [norm_orbitPt_snd_sq]
    exact tendsto_const_nhds.sub (hinv.pow 2)
  have h2 : Tendsto (fun n => ‖(orbitPt (g n)).2‖ ^ 2) atTop (𝓝 (‖ξ.2‖ ^ 2)) :=
    ((continuous_snd.norm.pow 2).tendsto ξ).comp hξ
  have h12 := tendsto_nhds_unique h2 h1
  norm_num at h12
  refine ⟨?_, ?_⟩
  · have h3 : Tendsto (fun n => (orbitPt (g n)).1) atTop (𝓝 ξ.1) :=
      (continuous_fst.tendsto ξ).comp hξ
    simp_rw [orbitPt_fst] at h3
    exact tendsto_nhds_unique h3 tendsto_const_nhds
  · rcases h12 with h | h
    · exact h
    · linarith [norm_nonneg ξ.2]

/-- A slice point with `‖ξ.2‖ = 1` is a nonzero null vector. -/
theorem minkQ_eq_zero_of_sphere {ξ : Minkowski d} (h1 : ξ.1 = 1) (h2 : ‖ξ.2‖ = 1) :
    minkQ ξ = 0 ∧ ξ ≠ 0 := by
  refine ⟨by simp [minkQ, h1, h2], fun h => ?_⟩
  rw [h] at h1
  simp at h1

/-- A point `ξ` of the boundary sphere is sent by every `a ∈ SO₀(1, d)` to a vector of positive
time component (`a ξ` is nonzero future causal). -/
theorem fst_apply_pos_of_sphere (a : lorentz d) {ξ : Minkowski d} (hξ1 : ξ.1 = 1)
    (hξ2 : ‖ξ.2‖ = 1) : 0 < ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ).1 := by
  obtain ⟨hq, hξ0⟩ := minkQ_eq_zero_of_sphere hξ1 hξ2
  have hC := lorentz.isFutureCausal_apply a.2 (v := ξ) ⟨by rw [hξ1]; exact zero_le_one, hq.le⟩
  refine lt_of_le_of_ne hC.1 fun h => hξ0 ?_
  exact (a : Minkowski d ≃ₗ[ℝ] Minkowski d).map_eq_zero_iff.1 (eq_zero_of_fst_eq_zero h.symm hC.2)

theorem continuous_lorentz_apply (a : lorentz d) :
    Continuous (a : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
  ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    Minkowski d →ₗ[ℝ] Minkowski d).continuous_of_finiteDimensional

/-- **Step 3b.** Along `orbitCosh (g n) → ∞` with non-loxodromic `g n`, the repelling points
follow the attracting ones. -/
theorem tendsto_orbitPt_inv {g : ℕ → lorentz d} {ξ : Minkowski d}
    (hg : ∀ n, ¬IsLoxodromic ((g n : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d))
    (hc : Tendsto (fun n => orbitCosh (g n)) atTop atTop)
    (hξ : Tendsto (fun n => orbitPt (g n)) atTop (𝓝 ξ)) :
    Tendsto (fun n => orbitPt (g n)⁻¹) atTop (𝓝 ξ) := by
  have hξ1 := (limit_mem_sphere hc hξ).1
  have hsq : Tendsto (fun n => Real.sqrt (8 / orbitCosh (g n))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds.div_atTop hc :
      Tendsto (fun n => (8 : ℝ) / orbitCosh (g n)) atTop (𝓝 0))
    rwa [Real.sqrt_zero] at this
  have hdiff : Tendsto (fun n => (orbitPt (g n)).2 - (orbitPt (g n)⁻¹).2) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hsq
    have := Real.abs_le_sqrt (norm_orbitPt_sub_inv_sq_le _ (hg n))
    rwa [abs_norm] at this
  have hsnd : Tendsto (fun n => (orbitPt (g n)).2) atTop (𝓝 ξ.2) :=
    (continuous_snd.tendsto ξ).comp hξ
  have h2 := hsnd.sub hdiff
  simp only [sub_sub_cancel, sub_zero] at h2
  rw [Prod.tendsto_iff]
  refine ⟨?_, h2⟩
  simp_rw [orbitPt_fst, hξ1]
  exact tendsto_const_nhds

/-- **Step 4a.** Left translation by a fixed `a` moves the attracting limit to `toSlice (a ξ)`
and keeps the displacement unbounded. -/
theorem tendsto_orbitPt_mul_left (a : lorentz d) {g : ℕ → lorentz d} {ξ : Minkowski d}
    (hc : Tendsto (fun n => orbitCosh (g n)) atTop atTop)
    (hξ : Tendsto (fun n => orbitPt (g n)) atTop (𝓝 ξ)) (hξ1 : ξ.1 = 1) (hξ2 : ‖ξ.2‖ = 1) :
    Tendsto (fun n => orbitCosh (a * g n)) atTop atTop ∧
      Tendsto (fun n => orbitPt (a * g n)) atTop
        (𝓝 (toSlice ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ))) := by
  have hpos := fst_apply_pos_of_sphere a hξ1 hξ2
  have haξ : Tendsto (fun n => (a : Minkowski d ≃ₗ[ℝ] Minkowski d) (orbitPt (g n))) atTop
      (𝓝 ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ)) :=
    ((continuous_lorentz_apply a).tendsto ξ).comp hξ
  refine ⟨?_, ?_⟩
  · simp_rw [orbitCosh_mul]
    exact hc.atTop_mul_pos hpos ((continuous_fst.tendsto _).comp haξ)
  · simp_rw [orbitPt_mul]
    exact (continuousAt_toSlice hpos.ne').tendsto.comp haξ

/-- `orbitPt A` is future timelike (`minkQ (orbitPt A) = −(orbitCosh A)⁻²`). -/
theorem isFutureTimelike_orbitPt (A : lorentz d) : IsFutureTimelike (orbitPt A) := by
  refine ⟨by rw [orbitPt_fst]; exact one_pos, ?_⟩
  have h := norm_orbitPt_snd_sq A
  have hc := inv_pos.2 (orbitCosh_pos A)
  simp only [minkQ, orbitPt_fst, h]
  nlinarith [pow_pos hc 2]

/-- `toSlice y = w + y.1⁻¹ • (y − y.1 • w)` when `y.1 ≠ 0`. -/
theorem toSlice_eq_add {y : Minkowski d} (hy : y.1 ≠ 0) (w : Minkowski d) :
    toSlice y = w + (y.1)⁻¹ • (y - y.1 • w) := by
  unfold toSlice
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hy, one_smul]
  abel

/-- **Step 4b.** Left translation by a fixed `a` does not move the repelling limit:
`orbitPt (a * g n)⁻¹ = toSlice ((g n)⁻¹ (a⁻¹ o)) → ξ`. -/
theorem tendsto_orbitPt_inv_mul_left (a : lorentz d) {g : ℕ → lorentz d} {ξ : Minkowski d}
    (hc : Tendsto (fun n => orbitCosh (g n)) atTop atTop)
    (hξ : Tendsto (fun n => orbitPt (g n)) atTop (𝓝 ξ))
    (hξ' : Tendsto (fun n => orbitPt (g n)⁻¹) atTop (𝓝 ξ)) (hξ1 : ξ.1 = 1) (hξ2 : ‖ξ.2‖ = 1) :
    Tendsto (fun n => orbitPt (a * g n)⁻¹) atTop (𝓝 ξ) := by
  obtain ⟨hq, hξ0⟩ := minkQ_eq_zero_of_sphere hξ1 hξ2
  have hξC : IsFutureCausal ξ := ⟨by rw [hξ1]; exact zero_le_one, hq.le⟩
  have hpos : 0 < -minkB ξ (orbitPt a⁻¹) :=
    neg_pos.2 (minkB_neg_of_future hξC hξ0 (isFutureTimelike_orbitPt a⁻¹))
  have hB : Continuous fun p : Minkowski d => -minkB p (orbitPt a⁻¹) := by
    unfold minkB; fun_prop
  have hlam_eq : ∀ n, ((((g n)⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)
      (orbitPt a⁻¹)).1 = orbitCosh (g n) * -minkB (orbitPt (g n)) (orbitPt a⁻¹) := by
    intro n
    rw [fst_apply_eq, inv_inv, orbitCosh_inv]
  have hlam : Tendsto (fun n => ((((g n)⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)
      (orbitPt a⁻¹)).1) atTop atTop := by
    simp_rw [hlam_eq]
    exact hc.atTop_mul_pos hpos ((hB.tendsto ξ).comp hξ)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun n =>
      (((g n)⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (orbitPt a⁻¹) -
        ((((g n)⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (orbitPt a⁻¹)).1 •
          orbitPt (g n)⁻¹) := by
    refine isBoundedUnder_of ⟨‖(orbitPt a⁻¹).2‖, fun n => ?_⟩
    refine norm_prod_le_iff.2 ⟨?_, rankOne_norm _ _⟩
    rw [rankOne_fst, norm_zero]
    exact norm_nonneg _
  have hlim := hξ'.add ((tendsto_inv_atTop_zero.comp hlam).zero_smul_isBoundedUnder_le hbdd)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hlam.eventually_gt_atTop 0] with n hn
  rw [mul_inv_rev, orbitPt_mul, toSlice_eq_add hn.ne' (orbitPt (g n)⁻¹)]
  rfl

/-- **Gromov's horocyclic/focal step for `SO₀(1, d)`, no loxodromics.** A subgroup with no
loxodromic element and an unbounded orbit of `o` fixes a nonzero null vector. -/
theorem exists_fixed_null_of_unbounded {G : Subgroup (lorentz d)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d))
    (hU : ∀ M : ℝ, ∃ A ∈ G, M < orbitCosh A) :
    ∃ v : Minkowski d, v ≠ 0 ∧ minkQ v = 0 ∧
      ∀ A ∈ G, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v := by
  choose g hgG hgc using fun n : ℕ => hU n
  have hc0 : Tendsto (fun n => orbitCosh (g n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hgc n).le) tendsto_natCast_atTop_atTop
  obtain ⟨ξ, -, φ, hφ, hξ⟩ := isCompact_slice.tendsto_subseq (fun n => orbitPt_mem_slice (g n))
  have hc : Tendsto (fun n => orbitCosh (g (φ n))) atTop atTop := hc0.comp hφ.tendsto_atTop
  have hξ' : Tendsto (fun n => orbitPt (g (φ n))) atTop (𝓝 ξ) := hξ
  have hg : ∀ n, ¬IsLoxodromic ((g (φ n) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
    fun n => hG _ (hgG _)
  obtain ⟨hξ1, hξ2⟩ := limit_mem_sphere hc hξ'
  obtain ⟨hq, hξ0⟩ := minkQ_eq_zero_of_sphere hξ1 hξ2
  have hinv := tendsto_orbitPt_inv hg hc hξ'
  refine ⟨ξ, hξ0, hq, fun a ha => ?_⟩
  obtain ⟨hca, hlim⟩ := tendsto_orbitPt_mul_left a hc hξ' hξ1 hξ2
  have hlim' := tendsto_orbitPt_inv_mul_left a hc hξ' hinv hξ1 hξ2
  have hag : ∀ n, ¬IsLoxodromic (((a * g (φ n) : lorentz d)) : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
    fun n => hG _ (G.mul_mem ha (hgG _))
  have h3 := tendsto_orbitPt_inv hag hca hlim
  have hfix : toSlice ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ) = ξ := tendsto_nhds_unique h3 hlim'
  have hpos := fst_apply_pos_of_sphere a hξ1 hξ2
  have heig : (a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ =
      ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ).1 • ξ := by
    calc (a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ
        = ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ).1 •
            toSlice ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ) := by
          unfold toSlice; rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      _ = ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ).1 • ξ := by rw [hfix]
  by_contra hne
  have h1 : ((a : Minkowski d ≃ₗ[ℝ] Minkowski d) ξ).1 ≠ 1 := fun h =>
    hne (by rw [heig, h, one_smul])
  exact hG a ha (isLoxodromic_of_null_eigen a.2 hξ0 hq hpos h1 heig)

end Causal.Flat
