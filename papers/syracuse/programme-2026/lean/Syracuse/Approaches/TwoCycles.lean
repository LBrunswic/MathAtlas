import Syracuse.Approaches.StdPairs

/-!
# Two-cycles at a Christoffel level: `u^{a₁} v u^{a₂} v`

The circuits `1^a d` are the `1`-cycles of Steiner; Simons' `2`-cycles have two big gaps. At any level
of the Christoffel tree, the analogue is a word `u^{a₁} v u^{a₂} v` over a standard pair `(u, v)`: two
growing runs of `u` separated by single `v`s. With `A = u^{a₁}v` and `B = u^{a₂}v`, the rotation
difference `S(AB) - S(BA) = C(A, B)` satisfies the generic identity (`core_runs`)

`C(A, B)·D(u) = C(u, v)·Y^{len v}·(X^{a₁|u|}Y^{a₂ len u} - X^{a₂|u|}Y^{a₁ len u})`,

whose right side is a `6`-smooth multiple of `D(u^{|a₁ - a₂|})` at `(2,3)`, because `C(u,v)` is
`6`-smooth (`StdPairs.core_smooth`). On a cycle, `D ∣ D(u^{a₁ - a₂})` (`dvd_of_cycle_runs`). With
Ellison this excludes the **comparable-runs regime** `a₂ < a₁ ≤ 3a₂` (`no_cycle_runs`). The regime
`a₁ > 3a₂` (one run much longer than the other) stays open.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `C(u^{a₁}v, u^{a₂}v)·D(u) = C(u,v) Y^{len v}(X^{a₁|u|}Y^{a₂ len u} - X^{a₂|u|}Y^{a₁ len u})` | `core_runs` | proved (generic) |
| on a cycle: `D ∣ D(u^{a₁ - a₂})` (standard pair, `a₂ ≤ a₁`) | `dvd_of_cycle_runs` | proved |
| no cycle (either sign) on `u^{a₁}v u^{a₂}v` with `a₂ < a₁ ≤ 3a₂` | `no_cycle_runs` | proved (conditional on `Ellison1971`, `E` not exceptional) |
| the regime `a₁ > 3a₂`; equal runs `a₁ = a₂` (a power of `u^a v`) | — | open / reduces to `StdPairs` via a power lemma (not formalized) |
-/

namespace Syracuse.TwoCycles

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- **The run identity.** -/
theorem core_runs (u v : Word) (a₁ a₂ : ℕ) :
    core X Y (bpow u a₁ ++ v) (bpow u a₂ ++ v) * D X Y u =
      core X Y u v * Y ^ v.length *
        (X ^ (a₁ * u.sum) * Y ^ (a₂ * u.length) - X ^ (a₂ * u.sum) * Y ^ (a₁ * u.length)) := by
  have h1 := D_mul_S_bpow X Y u a₁
  have h2 := D_mul_S_bpow X Y u a₂
  have e1 : D X Y (bpow u a₁) = X ^ (a₁ * u.sum) - Y ^ (a₁ * u.length) := by
    simp [D, bpow, CocycleCombine.wpow_sum, CocycleCombine.wpow_length]
  have e2 : D X Y (bpow u a₂) = X ^ (a₂ * u.sum) - Y ^ (a₂ * u.length) := by
    simp [D, bpow, CocycleCombine.wpow_sum, CocycleCombine.wpow_length]
  have s1 : (bpow u a₁).sum = a₁ * u.sum := by simp [bpow, CocycleCombine.wpow_sum]
  have s2 : (bpow u a₂).sum = a₂ * u.sum := by simp [bpow, CocycleCombine.wpow_sum]
  simp only [core, S_append, D_append, s1, s2]
  rw [e1] at h1 ⊢; rw [e2] at h2 ⊢
  linear_combination
    (Y ^ v.length * (Y ^ v.length * (X ^ (a₁ * u.sum) - Y ^ (a₁ * u.length)) +
      X ^ (a₁ * u.sum) * D X Y v)) * h2 -
    (Y ^ v.length * (Y ^ v.length * (X ^ (a₂ * u.sum) - Y ^ (a₂ * u.length)) +
      X ^ (a₂ * u.sum) * D X Y v)) * h1

end Generic

/-- **On a cycle, `D ∣ D(u^{a₁ - a₂})`** for a standard pair and `a₂ ≤ a₁`. -/
theorem dvd_of_cycle_runs {u v : Word} (hst : StdPair u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {a₁ a₂ : ℕ} (ha : a₂ ≤ a₁)
    (hw : gapWord x o ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v)) :
    Dz ((bpow u a₁ ++ v) ++ (bpow u a₂ ++ v)) ∣ Dz (bpow u (a₁ - a₂)) := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
  set A := bpow u a₁ ++ v
  set B := bpow u a₂ ++ v
  have hne : A ++ B ≠ [] := by simp [A, B, hv0]
  have hsum : (A ++ B).sum ≠ 0 := by
    have : 0 < v.sum := by
      have := CycleLiterature.length_le_sum hv
      have := List.length_pos_of_ne_nil hv0; omega
    simp [A, B]; omega
  have hcop := isCoprime_six hne hsum
  -- `D ∣ S(AB)` and `D ∣ S(BA)` (a rotation), so `D ∣ C(A, B)`
  have hS1 := dvd_S_of_rotated h hw
  have hrot : gapWord x o ~r B ++ A := hw.trans List.isRotated_append
  have hS2 := dvd_S_of_rotated h hrot
  have hDBA : Dz (B ++ A) = Dz (A ++ B) := by
    obtain ⟨n, hn⟩ := (List.isRotated_append : (A ++ B) ~r (B ++ A)); rw [← hn]; exact D_rotate _ _ _ _
  rw [hDBA] at hS2
  have hC : Dz (A ++ B) ∣ core (2 : ℤ) 3 A B := by
    have := dvd_sub hS1 hS2
    rwa [Sz, Sz, CocycleCombine.S_append_sub_S_append] at this
  -- multiply by `D(u)` and use the run identity
  have hid := core_runs (2 : ℤ) 3 u v a₁ a₂
  obtain ⟨i, j, hc⟩ := core_smooth hst
  have hdu : Dz (A ++ B) ∣ core (2 : ℤ) 3 A B * D (2 : ℤ) 3 u := dvd_mul_of_dvd_left hC _
  rw [hid, hc] at hdu
  -- the right side is `-(2^{i+1}3^j)·3^{len v}·2^{a₂|u|}3^{a₂ len u}·D(u^{a₁-a₂})`
  have hfac : (2 : ℤ) ^ (a₁ * u.sum) * 3 ^ (a₂ * u.length) - 2 ^ (a₂ * u.sum) * 3 ^ (a₁ * u.length) =
      2 ^ (a₂ * u.sum) * 3 ^ (a₂ * u.length) * Dz (bpow u (a₁ - a₂)) := by
    simp only [Dz, D, bpow, CocycleCombine.wpow_sum, CocycleCombine.wpow_length]
    obtain ⟨t, rfl⟩ : ∃ t, a₁ = a₂ + t := ⟨a₁ - a₂, by omega⟩
    rw [Nat.add_sub_cancel_left, add_mul, add_mul, pow_add, pow_add]; ring
  rw [hfac] at hdu
  have : Dz (A ++ B) ∣ 2 ^ (i + 1 + a₂ * u.sum) * 3 ^ (j + v.length + a₂ * u.length) *
      (-Dz (bpow u (a₁ - a₂))) := by
    have e : (2 : ℤ) ^ (i + 1 + a₂ * u.sum) * 3 ^ (j + v.length + a₂ * u.length) *
        (-Dz (bpow u (a₁ - a₂))) =
        -(2 ^ (i + 1) * 3 ^ j) * 3 ^ v.length *
          (2 ^ (a₂ * u.sum) * 3 ^ (a₂ * u.length) * Dz (bpow u (a₁ - a₂))) := by
      rw [pow_add, pow_add, pow_add, pow_add]; ring
    rw [e]; exact hdu
  have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hcop _ _ this
  rwa [dvd_neg] at this

/-- **No cycle on comparable runs.** For a standard pair `(u, v)` and `a₂ < a₁ ≤ 3a₂`, no cycle (of
either sign) has a gap word that is a rotation of `u^{a₁} v u^{a₂} v`, for `E` outside Ellison's
exceptions (conditional on Ellison). -/
theorem no_cycle_runs (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : StdPair u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a₁ a₂ : ℕ} (hlt : a₂ < a₁) (h3 : a₁ ≤ 3 * a₂)
    (hw : gapWord x o ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v))
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions) : False := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
  set w := (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v)
  have hdiv := dvd_of_cycle_runs hst h hlt.le hw
  have hne : w ≠ [] := by simp [w, hv0]
  have hw0 := Dz_ne_zero hne
  have ht0 : bpow u (a₁ - a₂) ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hu0 h1
  have hU0 := Dz_ne_zero ht0
  have hle : |Dz w| ≤ |Dz (bpow u (a₁ - a₂))| := by
    have := Int.natAbs_le_of_dvd_ne_zero hdiv hU0
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast this
  have hlt3 := abs_Dz_lt (pos_bpow hu (a₁ - a₂))
  have hsumt : (bpow u (a₁ - a₂)).sum = (a₁ - a₂) * u.sum := by simp [bpow, CocycleCombine.wpow_sum]
  rw [hsumt] at hlt3
  -- sizes: `E ≥ (a₁ + a₂)|u|`
  have hsw : (gapWord x o).sum = w.sum := hw.perm.sum_eq
  have hlw : (gapWord x o).length = w.length := hw.perm.length_eq
  have hDeq : Dz (gapWord x o) = Dz w := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact (D_rotate _ _ _ _).symm
  set E := w.sum
  have hEsum : E = a₁ * u.sum + v.sum + (a₂ * u.sum + v.sum) := by
    simp [E, w, bpow, CocycleCombine.wpow_sum]
  have hpos0 : 0 < w.length := List.length_pos_of_ne_nil hne
  have hE0 : 0 < E := by
    have : 0 < v.sum := by
      have := CycleLiterature.length_le_sum hv
      have := List.length_pos_of_ne_nil hv0; omega
    omega
  rw [hsw] at hx
  have hEl' := hEl E w.length hE0 hpos0 hx
  have hDr : |(2 : ℝ) ^ E - 3 ^ w.length| = ((|Dz w| : ℤ) : ℝ) := by
    simp only [Dz, D]; push_cast; rfl
  rw [hDr] at hEl'
  -- `3^{(a₁ - a₂)|u|} ≤ (2e^{-1/10})^E`
  set c : ℝ := 2 * Real.exp (-(1 : ℝ) / 10)
  have hc1 : 1 ≤ c := by
    have : Real.exp (-(1 : ℝ) / 10) ≥ 1 / 2 := by
      have := Real.add_one_le_exp (-(1 : ℝ) / 10); linarith
    simp only [c]; linarith
  have hc3 : (3 : ℝ) ≤ c ^ 2 := by
    have e1 : Real.exp (1 / 5) ≤ 4 / 3 := by
      have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
      linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
    have : c ^ 2 = 4 * Real.exp (-(1 : ℝ) / 5) := by
      simp only [c]; rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; norm_num
    rw [this]
    have hprod : Real.exp (1 / 5) * Real.exp (-(1 : ℝ) / 5) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-(1 : ℝ) / 5), Real.exp_pos (1 / 5 : ℝ)]
  have hA : (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) = c ^ E := by
    simp only [c]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
  rw [hA] at hEl'
  have hkey : (3 : ℝ) ^ ((a₁ - a₂) * u.sum) ≤ c ^ E := by
    calc (3 : ℝ) ^ ((a₁ - a₂) * u.sum) ≤ (c ^ 2) ^ ((a₁ - a₂) * u.sum) :=
          pow_le_pow_left₀ (by norm_num) hc3 _
      _ = c ^ (2 * ((a₁ - a₂) * u.sum)) := by rw [← pow_mul]
      _ ≤ c ^ E := by
          apply pow_le_pow_right₀ hc1
          rw [hEsum]
          obtain ⟨t, ht⟩ : ∃ t, a₁ = a₂ + t := ⟨a₁ - a₂, by omega⟩
          rw [ht, Nat.add_sub_cancel_left]
          have htt : t ≤ 2 * a₂ := by omega
          have h1 : t * u.sum ≤ 2 * (a₂ * u.sum) := by
            have := Nat.mul_le_mul_right u.sum htt; rwa [mul_assoc] at this
          have e : (a₂ + t) * u.sum + v.sum + (a₂ * u.sum + v.sum) =
              t * u.sum + 2 * (a₂ * u.sum) + 2 * v.sum := by ring
          rw [e]; omega
  have hlt3R : ((|Dz w| : ℤ) : ℝ) < 3 ^ ((a₁ - a₂) * u.sum) := by
    have := lt_of_le_of_lt hle hlt3
    exact_mod_cast this
  linarith

end Syracuse.TwoCycles
