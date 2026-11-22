import Syracuse.Approaches.Frontier
import Syracuse.Approaches.TwoCycles

/-!
# Re-bracketing: level-`(u,v)` two-cycles are two-run words one level down

`TwoCycles.no_cycle_runs` excluded `u^{a₁} v u^{a₂} v` only in the comparable regime
`a₂ < a₁ ≤ 3a₂`. Re-bracketing removes that restriction. For `a₁ > a₂`,

`u^{a₁} v u^{a₂} v = u^{a₁ - a₂} · (u^{a₂} v)²`,

and `(u, u^{a₂} v)` is again a standard pair (`a₂` left Stern–Brocot moves, `stdPair_left_pow`). So the
word is a two-run word over a standard pair, which `StdPairs` excludes. For `a₁ = a₂` the word is the
square `(u^a v)²`. A cycle on a rotation of `Z^g` gives a cycle on `Z` itself (`pos_cycle_of_pow`,
power reduction), and `Z = u^a v` is again a two-run word.

Result (`no_pos_two_cycle`): given Ellison and Barina, **no positive cycle has a gap word that is a
rotation of `u^{a₁} v u^{a₂} v`** for any standard pair and any `a₁, a₂ ≥ 1`. The frontier is
extended accordingly (`frontier_two_cycles`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `(u, u^k v)` is standard whenever `(u, v)` is | `stdPair_left_pow` | proved |
| `u^{m+n} = u^m u^n` | `bpow_add` | proved |
| power reduction: a positive cycle on a rotation of `Z^g` gives a positive cycle on `Z` | `pos_cycle_of_pow` | proved |
| no positive cycle on `u^{a₁} v u^{a₂} v` (standard pair, `a₁, a₂ ≥ 1`) | `no_pos_two_cycle` | proved (conditional on Ellison + Barina) |
| no positive cycle on `(u^a v^b)^g` (standard pair, `a, b, g ≥ 1`) | `no_pos_cycle_std_pair_pow` | proved (conditional on Ellison + Barina) |
-/

namespace Syracuse.Renormalize

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

lemma bpow_succ (u : Word) (k : ℕ) : bpow u (k + 1) = u ++ bpow u k := by
  simp [bpow, CocycleCombine.wpow, List.replicate_succ]

lemma bpow_add (u : Word) (m n : ℕ) : bpow u (m + n) = bpow u m ++ bpow u n := by
  simp only [bpow, CocycleCombine.wpow, List.replicate_add, List.flatten_append]

lemma bpow_two (Z : Word) : bpow Z 2 = Z ++ Z := by simp [bpow, CocycleCombine.wpow]

lemma bpow_one (Z : Word) : bpow Z 1 = Z := by simp [bpow, CocycleCombine.wpow]

/-- `k` left Stern–Brocot moves: `(u, u^k v)` is standard whenever `(u, v)` is. -/
theorem stdPair_left_pow {u v : Word} (h : StdPair u v) (k : ℕ) : StdPair u (bpow u k ++ v) := by
  induction k with
  | zero => simpa [bpow, CocycleCombine.wpow] using h
  | succ k ih => rw [bpow_succ, List.append_assoc]; exact StdPair.left ih

/-- **Power reduction.** A positive cycle whose gap word is a rotation of `Z^g` (`g ≥ 1`, `Z`
positive and nonempty) yields a positive cycle whose gap word is exactly `Z`. -/
theorem pos_cycle_of_pow {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) {Z : Word} (hZ : Z.Pos)
    (hZ0 : Z ≠ []) {g : ℕ} (hg : 1 ≤ g) (hw : gapWord x o ~r bpow Z g) :
    ∃ y : ℤ, 0 < y ∧ IsSyrCycle y Z.length ∧ gapWord y Z.length = Z := by
  have hS := dvd_S_of_rotated h hw
  have hSZ := CocycleCombine.S_wpow (2 : ℤ) 3 Z g
  have hDZ := CocycleCombine.D_wpow (2 : ℤ) 3 Z g
  have hne : bpow Z g ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hZ0 h1
  have hD0 := Dz_ne_zero hne
  have hgeo : CocycleCombine.geo (2 : ℤ) 3 Z g ≠ 0 := by
    intro h0; apply hD0; simp only [Dz, bpow] at hDZ ⊢; rw [hDZ, h0, mul_zero]
  have hdvd : Dz Z ∣ Sz Z := by
    simp only [Sz, Dz, bpow] at hS ⊢
    rw [hSZ, hDZ] at hS
    exact (mul_dvd_mul_iff_right hgeo).1 hS
  obtain ⟨hc, hgw⟩ := CycleLiterature.isSyrCycle_of_dvd hZ hZ0 hdvd
  refine ⟨Sz Z / Dz Z, ?_, hc, hgw⟩
  -- positivity: `D(Z^g) = D(Z)·geo > 0` with `geo > 0`, and `S(Z) > 0`
  have hgeo_pos : 0 < CocycleCombine.geo (2 : ℤ) 3 Z g := by
    rw [CocycleCombine.geo_eq_sum (2 : ℤ) 3]
    apply Finset.sum_pos (fun i _ => by positivity) (by simp; omega)
  have hDpos : 0 < Dz (bpow Z g) := by
    have : Dz (gapWord x o) = Dz (bpow Z g) := by
      obtain ⟨n, hn⟩ := hw; rw [← hn]; exact (D_rotate (2 : ℤ) 3 _ _).symm
    rw [← this]; exact CycleLiterature.cycle_Dz_pos h hx
  have hDZpos : 0 < Dz Z := by
    simp only [Dz, bpow] at hDpos ⊢; rw [hDZ] at hDpos
    exact pos_of_mul_pos_left hDpos hgeo_pos.le
  have hSpos : 0 < Sz Z := Program.Sz_pos hZ0
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, Int.mul_ediv_cancel_left _ hDZpos.ne']
  have : 0 < Dz Z * q := hq ▸ hSpos
  exact pos_of_mul_pos_right this hDZpos.le

/-- **No positive level-`(u,v)` two-cycle.** Given Ellison and Barina, no positive cycle has a gap
word that is a rotation of `u^{a₁} v u^{a₂} v` for a standard pair `(u, v)` and `a₁, a₂ ≥ 1`. -/
theorem no_pos_two_cycle (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    {u v : Word} (hst : StdPair u v) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    {a₁ a₂ : ℕ} (h1 : 1 ≤ a₁) (h2 : 1 ≤ a₂)
    (hw : gapWord x o ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v)) : False := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
  -- the unequal case, after possibly swapping the two blocks
  have unequal : ∀ b₁ b₂ : ℕ, b₂ < b₁ → gapWord x o ~r (bpow u b₁ ++ v) ++ (bpow u b₂ ++ v) → False := by
    intro b₁ b₂ hlt hw'
    set Z := bpow u b₂ ++ v
    have hst' : StdPair u Z := stdPair_left_pow hst b₂
    have heq : (bpow u b₁ ++ v) ++ (bpow u b₂ ++ v) = bpow u (b₁ - b₂) ++ bpow Z 2 := by
      rw [bpow_two, show b₁ = (b₁ - b₂) + b₂ by omega, bpow_add]
      simp [Z]
    rw [heq] at hw'
    exact Frontier.no_pos_cycle_std_pair hEl hB hst' h hx (by omega) (by norm_num) hw'
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · exact unequal a₂ a₁ hlt (hw.trans List.isRotated_append)
  · -- equal runs: the word is `Z²`, `Z = u^a v`
    subst heq
    set Z := bpow u a₁ ++ v
    have hZpos : Z.Pos := fun d hd => by
      simp only [Z, List.mem_append] at hd; rcases hd with hd | hd
      · exact pos_bpow hu a₁ d hd
      · exact hv d hd
    have hZ0 : Z ≠ [] := by simp [Z, hv0]
    rw [← bpow_two] at hw
    obtain ⟨y, hy, hcy, hgy⟩ := pos_cycle_of_pow h hx hZpos hZ0 (by norm_num) hw
    have hrot : gapWord y Z.length ~r bpow u a₁ ++ bpow v 1 := by
      rw [hgy, bpow_one]
    exact Frontier.no_pos_cycle_std_pair hEl hB hst hcy hy h1 le_rfl hrot
  · exact unequal a₁ a₂ hgt hw


/-- **Powers of standard two-run words.** Given Ellison and Barina, no positive cycle has a gap word
that is a rotation of `(u^a v^b)^g` (standard pair, `a, b, g ≥ 1`). -/
theorem no_pos_cycle_std_pair_pow (hEl : CycleLiterature.Ellison1971)
    (hB : CycleLiterature.Barina2025) {u v : Word} (hst : StdPair u v) {x : ℤ} {o : ℕ}
    (h : IsSyrCycle x o) (hx : 0 < x) {a b g : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hg : 1 ≤ g)
    (hw : gapWord x o ~r bpow (bpow u a ++ bpow v b) g) : False := by
  obtain ⟨hu, hv, -, hv0⟩ := hst.pos
  set Z := bpow u a ++ bpow v b
  have hZpos : Z.Pos := fun d hd => by
    simp only [Z, List.mem_append] at hd; rcases hd with hd | hd
    · exact pos_bpow hu a d hd
    · exact pos_bpow hv b d hd
  have hZ0 : Z ≠ [] := by
    intro h0
    have : bpow v b = [] := (List.append_eq_nil_iff.1 h0).2
    have := congrArg List.length this
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hv0 h1
  obtain ⟨y, hy, hcy, hgy⟩ := pos_cycle_of_pow h hx hZpos hZ0 hg hw
  exact Frontier.no_pos_cycle_std_pair hEl hB hst hcy hy ha hb (by rw [hgy])

end Syracuse.Renormalize
