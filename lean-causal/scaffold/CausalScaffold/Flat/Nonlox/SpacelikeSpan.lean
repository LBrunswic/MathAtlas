import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Examples
import CausalScaffold.Flat.CauchyComplete

/-!
# `CausalScaffold.Flat.Nonlox.SpacelikeSpan` — the translation span is spacelike

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9.E
(`GHFspace.tex` l.2615–2617):

> According to lemma \ref{suspendre}, `M(S)` is thus a linear twisted product over a translation
> spacetime.

and §3 [3.T] (`GHFspace.tex` l.586–593): translation spacetimes are "the quotients of the entire
`𝐌ⁿ` by a group of translations by spacelike translation vectors".

Item (4) of `Causal.Flat.nonloxodromic_elliptic`'s obstruction needs the **span** of the
translation vectors to be spacelike, not merely each vector (`docs/BARBOT.md` finding (3),
`Nonloxodromic` SCOPE finding (3): spacelike vectors need not span a spacelike subspace,
`spacelike_translations_null_span`). This module proves it for any additive subgroup `Λ` of
translation vectors preserving an entire acausal graph through `p₀`:

* `exists_nat_smul_near_mem` (private) — **torus recurrence**: every `n ∈ span ℝ Λ` has
  `‖s n − λ‖ < ε` for some integer `s ≥ 1` and `λ ∈ Λ` (simultaneous Dirichlet by pigeonhole on a
  grid of `[0,1)ᵐ`; no discreteness of `Λ` is used).
* `minkQ_nonneg_of_invariant` (private) — each `τ` with `p₀, p₀ + τ ∈ Σ` has `minkQ τ ≥ 0`.
* `minkQ_pos_of_mem_span_of_invariant` — a nonzero `w ∈ span ℝ Λ` is spacelike: a timelike `w`
  recurs into the open timelike cone (homogeneity), a null `w` (or `−w`) is recurrent, against the
  hypothesis `hnull` (discharged in `Nonloxodromic` by
  `not_null_recurrent_of_isEntireAcausalGraph`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`). Written by a prover of the Barbot campaign, round 5.
-/

namespace Causal.Flat.Nonlox

open Set Submodule Filter Topology

variable {d : ℕ}

/-- Simultaneous Dirichlet approximation, by pigeonhole on the grid `(⌊M fract(a cᵢ)⌋)ᵢ`. -/
private theorem exists_nat_near_int {m : ℕ} (c : Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ k : Fin m → ℤ, ∀ i, |(s : ℝ) * c i - k i| < δ := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / δ < M := exists_nat_gt _
  have hM0 : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hMδ : 1 / (M : ℝ) < δ := by
    rw [div_lt_iff₀ hM0]; rw [div_lt_iff₀ hδ] at hM; linarith
  let f : ℕ → Fin m → Fin M := fun a i =>
    ⟨⌊Int.fract ((a : ℝ) * c i) * M⌋₊, by
      rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hM0.le)]
      exact mul_lt_of_lt_one_left hM0 (Int.fract_lt_one _)⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hclose : ∀ i, |Int.fract ((a : ℝ) * c i) - Int.fract ((b : ℝ) * c i)| < δ := by
    intro i
    have h : ⌊Int.fract ((a : ℝ) * c i) * M⌋₊ = ⌊Int.fract ((b : ℝ) * c i) * M⌋₊ :=
      congrArg (fun φ => ((φ i : Fin M) : ℕ)) hfab
    set x := Int.fract ((a : ℝ) * c i)
    set y := Int.fract ((b : ℝ) * c i)
    have hx0 : 0 ≤ x * M := mul_nonneg (Int.fract_nonneg _) hM0.le
    have hy0 : 0 ≤ y * M := mul_nonneg (Int.fract_nonneg _) hM0.le
    have h1 := Nat.floor_le hx0
    have h2 := Nat.lt_floor_add_one (x * M)
    have h3 := Nat.floor_le hy0
    have h4 := Nat.lt_floor_add_one (y * M)
    rw [h] at h1 h2
    have h5 : |x * M - y * M| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_mul, abs_mul, abs_of_pos hM0] at h5
    calc |x - y| < 1 / M := by rw [lt_div_iff₀ hM0]; exact h5
      _ < δ := hMδ
  have key : ∀ a b : ℕ, a < b →
      (∀ i, |Int.fract ((a : ℝ) * c i) - Int.fract ((b : ℝ) * c i)| < δ) →
      ∃ s : ℕ, 1 ≤ s ∧ ∃ k : Fin m → ℤ, ∀ i, |(s : ℝ) * c i - k i| < δ := by
    intro a b hlt h
    refine ⟨b - a, by omega, fun i => ⌊(b : ℝ) * c i⌋ - ⌊(a : ℝ) * c i⌋, fun i => ?_⟩
    rw [Nat.cast_sub hlt.le]
    have := h i
    rw [abs_sub_comm] at this
    unfold Int.fract at this
    push_cast
    convert this using 2; ring
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h hclose
  · exact key b a h fun i => by rw [abs_sub_comm]; exact hclose i

/-- **Torus recurrence**: every vector of the real span of an additive subgroup `Λ` comes back
`ε`-close to `Λ` along its integer multiples `s ≥ 1`. -/
private theorem exists_nat_smul_near_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : AddSubgroup E) {n : E} (hn : n ∈ span ℝ (Λ : Set E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ l ∈ Λ, ‖(s : ℝ) • n - l‖ < ε := by
  obtain ⟨m, c, g, rfl⟩ := mem_span_set'.1 hn
  set S := ∑ i, ‖(g i : E)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hδ : 0 < ε / (S + 1) := div_pos hε (by linarith)
  obtain ⟨s, hs, k, hk⟩ := exists_nat_near_int c hδ
  refine ⟨s, hs, ∑ i, k i • (g i : E),
    AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (g i).2 _, ?_⟩
  have heq : (s : ℝ) • ∑ i, c i • (g i : E) - ∑ i, k i • (g i : E) =
      ∑ i, ((s : ℝ) * c i - k i) • (g i : E) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, mul_smul, Int.cast_smul_eq_zsmul]
  rw [heq]
  calc ‖∑ i, ((s : ℝ) * c i - k i) • (g i : E)‖
      ≤ ∑ i, ‖((s : ℝ) * c i - k i) • (g i : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε / (S + 1) * ‖(g i : E)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hk i).le (norm_nonneg _)
    _ = ε / (S + 1) * S := by rw [Finset.mul_sum]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith

/-- A translation vector between two points of an entire acausal graph is `0` or spacelike. -/
private theorem minkQ_nonneg_of_invariant {St : Set (Minkowski d)}
    (hS : IsEntireAcausalGraph St) {p₀ τ : Minkowski d} (hp₀ : p₀ ∈ St)
    (hτ : p₀ + τ ∈ St) : 0 ≤ minkQ τ := by
  obtain ⟨g, hg, rfl⟩ := isEntireAcausalGraph_iff.1 hS
  have h0 : p₀.1 = g p₀.2 := hp₀
  have h1 : (p₀ + τ).1 = g (p₀ + τ).2 := hτ
  simp only [Prod.fst_add, Prod.snd_add] at h1
  by_cases h2 : τ.2 = 0
  · have h3 : τ.1 = 0 := by rw [h2, add_zero, ← h0] at h1; linarith
    simp [minkQ, h3, h2]
  · have h4 := hg (p₀.2 + τ.2) p₀.2 (by simpa using h2)
    rw [add_sub_cancel_left, ← h1, ← h0, add_sub_cancel_left] at h4
    have h5 := pow_lt_pow_left₀ h4 (abs_nonneg _) two_ne_zero
    rw [sq_abs] at h5
    rw [minkQ]; linarith

/-- **[9.E] item (4): the span of the translation vectors is spacelike.** Let `Λ` be an additive
group of translation vectors `τ` with `p₀ + τ ∈ Σ`, `Σ` an entire acausal graph through `p₀`, and
assume no future null vector is recurrent for `Σ` at `p₀` (`hnull`, which is
`not_null_recurrent_of_isEntireAcausalGraph`). Then every nonzero `w ∈ span ℝ Λ` is spacelike. -/
theorem minkQ_pos_of_mem_span_of_invariant {St : Set (Minkowski d)}
    (hS : IsEntireAcausalGraph St) {p₀ : Minkowski d} (hp₀ : p₀ ∈ St)
    (Λ : AddSubgroup (Minkowski d)) (hΛ : ∀ τ ∈ Λ, p₀ + τ ∈ St)
    (hnull : ∀ n : Minkowski d, 0 < n.1 → minkQ n = 0 →
      (∀ ε > 0, ∃ s : ℝ, 1 ≤ s ∧ ∃ τ : Minkowski d, p₀ + τ ∈ St ∧ ‖s • n - τ‖ < ε) → False) :
    ∀ w ∈ span ℝ (Λ : Set (Minkowski d)), w ≠ 0 → 0 < minkQ w := by
  have hnn : ∀ τ ∈ Λ, 0 ≤ minkQ τ := fun τ hτ => minkQ_nonneg_of_invariant hS hp₀ (hΛ τ hτ)
  intro w hw hw0
  rcases lt_trichotomy (minkQ w) 0 with hlt | heq | hgt
  · exfalso
    have hcont : Continuous fun u : Minkowski d => minkQ (w - u) :=
      continuous_minkQ.comp (continuous_const.sub continuous_id)
    have hev : ∀ᶠ u in 𝓝 (0 : Minkowski d), minkQ (w - u) < 0 :=
      hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨s, hs, l, hl, hsl⟩ := exists_nat_smul_near_mem Λ hw hr
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    set u : Minkowski d := (s : ℝ)⁻¹ • ((s : ℝ) • w - l) with hu_def
    have hu : dist u 0 < r := by
      rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs0]
      calc (s : ℝ)⁻¹ * ‖(s : ℝ) • w - l‖ ≤ ‖(s : ℝ) • w - l‖ :=
            mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (by exact_mod_cast hs))
        _ < r := hsl
    have hlw : l = (s : ℝ) • (w - u) := by
      rw [hu_def, smul_sub, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]; abel
    have h1 := hnn l hl
    rw [hlw, minkQ_smul] at h1
    have h2 := hball hu
    nlinarith [sq_pos_of_pos hs0]
  · exfalso
    have hw1 : w.1 ≠ 0 := fun h => hw0 (eq_zero_of_fst_eq_zero h heq.le)
    obtain ⟨n, hn1, hnQ, hnspan⟩ : ∃ n : Minkowski d, 0 < n.1 ∧ minkQ n = 0 ∧
        n ∈ span ℝ (Λ : Set (Minkowski d)) := by
      rcases lt_or_gt_of_ne hw1 with h | h
      · exact ⟨-w, by simpa using h, by simpa using heq, neg_mem hw⟩
      · exact ⟨w, h, heq, hw⟩
    refine hnull n hn1 hnQ fun ε hε => ?_
    obtain ⟨s, hs, l, hl, hsl⟩ := exists_nat_smul_near_mem Λ hnspan hε
    exact ⟨s, by exact_mod_cast hs, l, hΛ l hl, hsl⟩
  · exact hgt

end Causal.Flat.Nonlox
