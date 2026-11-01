import CausalScaffold.Flat.Externals

/-!
# Commuting elliptic elements fix a common timelike vector of an invariant timelike subspace

All-elliptic step of Barbot's Prop 10.4 (`bprop:U_timelike`, `GHFspace.tex` l.3356–3359), served
to `bprop_U_timelike` (`Flat/Loxodromic.lean`) through the upper-central-series induction: a set
`S ≤ SO₀(1, d)` of elliptic elements, each mapping a subspace `W` containing a timelike vector into
itself and pairwise commuting on `W`, fixes a common timelike vector of `W`. **No label is
marked**: this is one step of a proof, not a statement of the paper.

* `bprop:U_timelike`, `GHFspace.tex:3356–3359`, partial (the elliptic branch of the folklore, in
  its true form: a common timelike fixed vector, not a unique one; **no `sorry`**):
  `exists_fixed_timelike_of_commuteOn`.

Barbot's `𝐌ⁿ` is `Minkowski d` with `n = d + 1`.

> Now, an abelian subgroup
> of $SO_{0}(1,n-1)$ fixes a pair of isotropic directions, except
> if it consists only one elliptic elements fixing one and
> only one timelike vector $v_{0}$. (l.3356–3359)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| abelian subgroup of `SO₀(1, n−1)` | ⚠ weakened: a set `S` of elements commuting on `W` only (`hcomm`) |
| consists only of elliptic elements | ✓ carried (`hell`) |
| (whole space) | ⚠ weakened: any `S`-invariant subspace `W` with a timelike vector (`hSW`, `hWt`); `W = ⊤` is the classical case |
| conclusion "fixing one and only one timelike vector" | ⚠ as: a common timelike fixed vector in `W`; uniqueness is false in general (`S = {id}`) and not claimed |

## SCOPE (disclosed)

Uniqueness of `v₀` (l.3358) is not proved: it fails as soon as the common fixed space has
dimension `≥ 2` (e.g. `S = {id}`). The proof: an elliptic `A` preserving a submodule `F` with a
timelike vector fixes a timelike vector of `F` (`exists_fixed_timelike_mem`, the minimiser
argument of `IsElliptic.exists_fixed_timelike` run inside `F`); induction on finite `T ⊆ S`
for `W ⊓ ⋂_{A ∈ T} Fix(A)`, each `S`-invariant by commutation; a finite `T` minimising the
dimension is fixed by all of `S`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Set

variable {d : ℕ}

/-- An elliptic `A ∈ SO₀(1, d)` mapping a submodule `F` containing a timelike vector into itself
fixes a timelike vector of `F` (the minimiser argument of `IsElliptic.exists_fixed_timelike`,
restricted to `F`). -/
private theorem exists_fixed_timelike_mem {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) (h : IsElliptic A) (F : Submodule ℝ (Minkowski d))
    (hFt : ∃ w ∈ F, minkQ w < 0) (hAF : ∀ w ∈ F, A w ∈ F) :
    ∃ u ∈ F, minkQ u < 0 ∧ A u = u := by
  obtain ⟨E, hs, hpos, hE⟩ := h
  have hqc := continuous_bilin_diag E
  obtain ⟨m, hm, hcoer⟩ := exists_coercive E hpos
  have hFc : IsClosed (F : Set (Minkowski d)) := F.closed_of_finiteDimensional
  set S : Set (Minkowski d) := {v | 0 ≤ v.1 ∧ minkQ v = -1 ∧ v ∈ F} with hSdef
  obtain ⟨w, hwF, hw⟩ := hFt
  obtain ⟨w', hw'F, hw'⟩ : ∃ w' ∈ F, IsFutureTimelike w' := by
    rcases isFutureTimelike_or_neg hw with h | h
    · exact ⟨w, hwF, h⟩
    · exact ⟨-w, F.neg_mem hwF, h⟩
  set v₀ : Minkowski d := (Real.sqrt (-minkQ w'))⁻¹ • w'
  have hq' : 0 < -minkQ w' := by linarith [hw'.2]
  have hv₀ : v₀ ∈ S := by
    refine ⟨?_, ?_, F.smul_mem _ hw'F⟩
    · simp only [v₀, Prod.smul_fst, smul_eq_mul]
      have := hw'.1; positivity
    · simp only [v₀]
      have h0 : minkQ w' ≠ 0 := by linarith
      rw [minkQ_smul, inv_pow, Real.sq_sqrt hq'.le, inv_mul_eq_div, div_neg, div_self h0]
  set c := E v₀ v₀
  set K := S ∩ {v | E v v ≤ c}
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have hKeq : K = {v : Minkowski d | (0 : ℝ) ≤ v.1} ∩ {v | minkQ v = -1} ∩
          (F : Set (Minkowski d)) ∩ {v | E v v ≤ c} := by
        ext v; simp only [K, S, mem_inter_iff, mem_setOf_eq, SetLike.mem_coe, and_assoc]
      rw [hKeq]
      exact (((isClosed_le continuous_const continuous_fst).inter
        (isClosed_eq continuous_minkQ continuous_const)).inter hFc).inter
          (isClosed_le hqc continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨max 1 (c / m), fun v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : m * ‖v‖ ^ 2 ≤ c := (hcoer v).trans hv.2
      have h2 : ‖v‖ ^ 2 ≤ c / m := by rw [le_div_iff₀ hm]; linarith
      rcases le_or_gt ‖v‖ 1 with h3 | h3
      · exact h3.trans (le_max_left _ _)
      · exact (by nlinarith : ‖v‖ ≤ c / m).trans (le_max_right _ _)
  obtain ⟨u, huK, humin⟩ := hK.exists_isMinOn ⟨v₀, hv₀, show E v₀ v₀ ≤ c from le_refl _⟩
    hqc.continuousOn
  have hminS : ∀ w ∈ S, E u u ≤ E w w := fun w hw => by
    by_cases hw' : E w w ≤ c
    · exact isMinOn_iff.1 humin w ⟨hw, hw'⟩
    · push Not at hw'; exact huK.2.trans hw'.le
  have hAS : ∀ w ∈ S, A w ∈ S := fun w hw =>
    ⟨(lorentz.isFutureCausal_apply hA (v := w) ⟨hw.1, by rw [hw.2.1]; norm_num⟩).1,
      by rw [hA.1 w, hw.2.1], hAF w hw.2.2⟩
  have hS2 : ∀ w ∈ S, w.1 ^ 2 = 1 + ‖w.2‖ ^ 2 := fun w hw => by
    have := hw.2.1; simp only [minkQ] at this; linarith
  -- reverse Cauchy–Schwarz on `S`
  have hrcs : ∀ v ∈ S, ∀ w ∈ S, minkB v w ≤ -1 := by
    intro v hv w hw
    have hv2 := hS2 v hv
    have hw2 := hS2 w hw
    have hX2 : (v.1 * w.1) ^ 2 ≥ (1 + ‖v.2‖ * ‖w.2‖) ^ 2 := by
      rw [mul_pow, hv2, hw2]; nlinarith [sq_nonneg (‖v.2‖ - ‖w.2‖)]
    have hX0 : 0 ≤ v.1 * w.1 := mul_nonneg hv.1 hw.1
    have hY0 : 0 ≤ 1 + ‖v.2‖ * ‖w.2‖ := by positivity
    have hXY : 1 + ‖v.2‖ * ‖w.2‖ ≤ v.1 * w.1 := by nlinarith
    have hin := real_inner_le_norm v.2 w.2
    simp only [minkB]; linarith
  -- uniqueness of the minimiser
  have huniq : ∀ w ∈ S, E w w = E u u → w = u := by
    intro w hw hwE
    by_contra hne
    set z : Minkowski d := (1 / 2 : ℝ) • (u + w)
    have hBuw := hrcs u huK.1 w hw
    have hzQ : minkQ z ≤ -1 := by
      simp only [z, minkQ_smul, minkQ_add, huK.1.2.1, hw.2.1]; nlinarith
    set q := -minkQ z
    have hq1 : 1 ≤ q := by simp only [q]; linarith
    have hq0 : 0 < q := by linarith
    set z' : Minkowski d := (Real.sqrt q)⁻¹ • z
    have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
    have hz'S : z' ∈ S := by
      refine ⟨?_, ?_, F.smul_mem _ (F.smul_mem _ (F.add_mem huK.1.2.2 hw.2.2))⟩
      · simp only [z', z, Prod.smul_fst, Prod.fst_add, smul_eq_mul]
        have := huK.1.1; have := hw.1; positivity
      · simp only [z']
        have hz0 : minkQ z ≠ 0 := by linarith
        rw [minkQ_smul, inv_pow, hsq]
        simp only [q]; field_simp
    have hEz' : E z' z' ≤ E z z := by
      simp only [z', map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h0 : 0 ≤ E z z := by
        rcases eq_or_ne z 0 with h0 | h0
        · rw [h0]; simp
        · exact (hpos z h0).le
      have hi : (Real.sqrt q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hq1)
      have hi0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.2 hsq0.le
      calc (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * E z z) ≤ 1 * (1 * E z z) := by
            apply mul_le_mul hi _ (by positivity) zero_le_one
            exact mul_le_mul hi le_rfl h0 zero_le_one
        _ = E z z := by ring
    have hdiff := hpos (u - w) (sub_ne_zero.2 (Ne.symm hne))
    have hEz : E z z < E u u := by
      simp only [z, map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.sub_apply, smul_eq_mul] at hdiff ⊢
      rw [hs w u] at hdiff ⊢
      nlinarith
    linarith [hminS z' hz'S]
  have hAu := huniq (A u) (hAS u huK.1) (by rw [hE])
  exact ⟨u, huK.1.2.2, by rw [huK.1.2.1]; norm_num, hAu⟩

/-- `W ⊓ ⋂_{A ∈ T} Fix(A)`, the vectors of `W` fixed by every member of `T`. -/
private def commonFixIn (W : Submodule ℝ (Minkowski d)) (T : Finset (lorentz d)) :
    Submodule ℝ (Minkowski d) where
  carrier := {w | w ∈ W ∧ ∀ A ∈ T, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨W.add_mem ha hb, fun A hA => by rw [map_add, ha' A hA, hb' A hA]⟩
  zero_mem' := ⟨W.zero_mem, fun A _ => map_zero _⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨W.smul_mem c ha, fun A hA => by rw [map_smul, ha' A hA]⟩

private theorem mem_commonFixIn {W : Submodule ℝ (Minkowski d)} {T : Finset (lorentz d)}
    {w : Minkowski d} : w ∈ commonFixIn W T ↔
      w ∈ W ∧ ∀ A ∈ T, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w := Iff.rfl

/-- **Commuting elliptic elements fix a common timelike vector of an invariant timelike
subspace** (the elliptic branch of l.3356–3359, true form). A set `S ⊆ SO₀(1, d)` of elliptic
elements, each mapping `W` into itself and pairwise commuting on `W`, where `W` contains a timelike
vector, fixes a timelike vector of `W`. With `W = ⊤`: commuting elliptics fix a common point of
`ℍᵈ`. -/
theorem exists_fixed_timelike_of_commuteOn {d : ℕ} {S : Set (lorentz d)} {W : Submodule ℝ (Minkowski d)}
    (hWt : ∃ w ∈ W, minkQ w < 0)
    (hSW : ∀ A ∈ S, ∀ w ∈ W, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ W)
    (hell : ∀ A ∈ S, IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d))
    (hcomm : ∀ A ∈ S, ∀ B ∈ S, ∀ w ∈ W,
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) w) =
        (B : Minkowski d ≃ₗ[ℝ] Minkowski d) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) w)) :
    ∃ v ∈ W, minkQ v < 0 ∧ ∀ A ∈ S, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v := by
  classical
  -- each `W ⊓ ⋂_{A ∈ T} Fix(A)` is `S`-invariant, by commutation on `W`
  have hinv : ∀ T : Finset (lorentz d), (↑T : Set (lorentz d)) ⊆ S → ∀ B ∈ S,
      ∀ w ∈ commonFixIn W T, (B : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ commonFixIn W T := by
    intro T hT B hB w hw
    rw [mem_commonFixIn] at hw ⊢
    refine ⟨hSW B hB w hw.1, fun A hA => ?_⟩
    rw [hcomm A (hT hA) B hB w hw.1, hw.2 A hA]
  -- and contains a timelike vector, by induction on `T`
  have htl : ∀ T : Finset (lorentz d), (↑T : Set (lorentz d)) ⊆ S →
      ∃ v ∈ commonFixIn W T, minkQ v < 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨w, hw, hq⟩ := hWt
      exact ⟨w, mem_commonFixIn.2 ⟨hw, fun A hA => by simp at hA⟩, hq⟩
    | @insert B T hBT ih =>
      intro hT
      have hT' : (↑T : Set (lorentz d)) ⊆ S := fun x hx =>
        hT (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      have hB : B ∈ S := hT (Finset.mem_coe.2 (Finset.mem_insert_self B T))
      obtain ⟨u, huF, huq, hBu⟩ := exists_fixed_timelike_mem B.2 (hell B hB) (commonFixIn W T)
        (ih hT') (hinv T hT' B hB)
      rw [mem_commonFixIn] at huF
      refine ⟨u, mem_commonFixIn.2 ⟨huF.1, fun A hA => ?_⟩, huq⟩
      rcases Finset.mem_insert.1 hA with rfl | hA
      · exact hBu
      · exact huF.2 A hA
  -- a finite `T ⊆ S` minimising the dimension is fixed by all of `S`
  have hex : ∃ n, ∃ T : Finset (lorentz d), (↑T : Set (lorentz d)) ⊆ S ∧
      Module.finrank ℝ (commonFixIn W T) = n :=
    ⟨_, ∅, by simp, rfl⟩
  obtain ⟨T, hTS, hTn⟩ := Nat.find_spec hex
  obtain ⟨v, hvF, hvq⟩ := htl T hTS
  refine ⟨v, (mem_commonFixIn.1 hvF).1, hvq, fun B hB => ?_⟩
  have hTS' : (↑(insert B T) : Set (lorentz d)) ⊆ S := by
    rw [Finset.coe_insert]; exact Set.insert_subset hB hTS
  have hle : commonFixIn W (insert B T) ≤ commonFixIn W T := fun w hw => by
    rw [mem_commonFixIn] at hw ⊢
    exact ⟨hw.1, fun A hA => hw.2 A (Finset.mem_insert_of_mem hA)⟩
  have hmin := Nat.find_min' hex ⟨insert B T, hTS', rfl⟩
  have heq : commonFixIn W (insert B T) = commonFixIn W T :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hTn]; exact hmin)
  have hv' : v ∈ commonFixIn W (insert B T) := heq ▸ hvF
  exact (mem_commonFixIn.1 hv').2 B (Finset.mem_insert_self B T)

end Causal.Flat.Lox
