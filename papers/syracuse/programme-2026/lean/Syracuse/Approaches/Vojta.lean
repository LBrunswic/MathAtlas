import Syracuse.Approaches.Program
import Syracuse.Approaches.CocycleCombine
import Mathlib.NumberTheory.Height.NumberField

/-!
# How Vojta's conjecture for blow-ups (Levin's theorem) constrains cycles

Formalization of `approaches/places-elimination` §5. For a word family with `r ≥ 2` independent run
parameters, `V(D, S)` dominates the character torus (`places-elimination` §3), so no polynomial core
exists and the elementary squeeze of `TwoRun.lean` is unavailable. The product formula then has to be
applied to the *point*. The run coordinates `t(L) = (3^{a}, 2^{da}, …)` form a `6`-smooth point of
`𝔾_mⁿ`, and on a cycle the `6`-free gcd of `F(t)` and `G(t)` equals `|D|`. That gcd is Silverman's
concrete form of the height relative to the exceptional divisor of the blow-up of `𝔾_mⁿ` along
`V(F, G)`. **Vojta's conjecture for this blow-up, restricted to `S`-unit points, is a theorem**
(Levin, *Invent. Math.* 215 (2019), Thm 1.1, via Schmidt's Subspace Theorem; it extends
Bugeaud–Corvaja–Zannier and Corvaja–Zannier).

## Scope and trust

Following the project policy, the literature theorem enters only as the hypothesis `LevinGcd f g`
(and its packaged form `LevinTheorem`), never as an axiom. The statement here is deliberately
*weaker* than Levin's:

* the points are `6`-smooth positive integers (a subset of `(ℤ[1/6]^×)ⁿ`);
* the exceptional set is a finite set of character level sets `∏ uᵢ^{kᵢ} = c` with `k ≠ 0`, `c ∈ ℚ`
  (every translate of a proper algebraic subgroup lies in one, and a level set with `c ∉ ℚ` has no
  rational point);
* the height is the sum of the coordinate heights (`≥` the max Levin uses);
* coprimality is over `ℤ`, which implies coprimality over `ℚ̄`.

The exact form of Levin's exceptional set should be re-checked against the PDF before this file is
cited as a faithful transcription.

## Coverage

| claim (places-elimination §5) | Lean name | status |
|---|---|---|
| counting function of the blow-up at `p ∤ 6` | `gcd6` | defined |
| Weil height of the run point (Mathlib) | `ht`, `ht_nat` | defined / proved |
| Levin's gcd theorem (proved case of Vojta) | `LevinGcd`, `LevinTheorem` | stated only (hypothesis) |
| cycle ⇒ `|D| ≤ gcd6(F(t), G(t))` | `abs_Dz_le_gcd6` | proved |
| Levin + lower bound ⇒ cycles in exceptional sets or `o ≤ O` | `cycles_of_levin` | proved (conditional) |
| `r = 1` is the degenerate case: a certificate bounds `gcd6` outright | `gcd6_le_of_certificate` | proved |
| the two-length family `d^a e d^b f` (`r = 2`) in run coordinates | `twoLen_D`, `twoLen_S`, `twoLen_F`, `twoLen_G` | proved |
| Levin ⇒ conditional finiteness for `d^a e d^b f` | `twoLen_cycles_of_levin` | proved (conditional) |
-/

namespace Syracuse.Vojta

open Syracuse Syracuse.CocycleCombine Syracuse.Program

/-! ## Points, heights and the counting function -/

/-- A `6`-smooth positive integer point of `𝔾_mⁿ`: every coordinate is `2^α 3^β`. -/
def IsSixSmoothPoint {n : ℕ} (u : Fin n → ℕ) : Prop := ∀ i, ∃ α β : ℕ, u i = 2 ^ α * 3 ^ β

/-- The **counting function of the blow-up at the primes `p ∤ 6`**: the `6`-free part of `gcd(m, k)`. -/
def gcd6 (m k : ℤ) : ℕ := sixFree (Int.gcd m k : ℤ)

/-- The height of a point, as the sum of Mathlib's logarithmic Weil heights of its coordinates. -/
noncomputable def ht {n : ℕ} (u : Fin n → ℕ) : ℝ := ∑ i, Height.logHeight₁ ((u i : ℕ) : ℚ)

/-- For positive coordinates the height is `Σ log uᵢ`. -/
theorem ht_nat {n : ℕ} (u : Fin n → ℕ) (hu : ∀ i, u i ≠ 0) : ht u = ∑ i, Real.log (u i) := by
  unfold ht
  refine Finset.sum_congr rfl fun i _ => ?_
  have : NeZero (u i) := ⟨hu i⟩
  exact Rat.logHeight₁_natCast (u i)

/-- Membership in the exceptional set: a nontrivial character takes a prescribed value. -/
def InExceptional {n : ℕ} (Z : Finset ((Fin n → ℤ) × ℚ)) (u : Fin n → ℕ) : Prop :=
  ∃ p ∈ Z, p.1 ≠ 0 ∧ ∏ i, ((u i : ℚ)) ^ (p.1 i) = p.2

/-- Evaluation of an integer polynomial at an integer point. -/
def evalZ {n : ℕ} (u : Fin n → ℕ) (f : MvPolynomial (Fin n) ℤ) : ℤ :=
  MvPolynomial.eval (fun i => (u i : ℤ)) f

/-- **Levin's gcd bound for `f, g`** (the `S`-unit case of Vojta's conjecture for the blow-up of
`𝔾_mⁿ` along `V(f, g)`), in the weakened form described in the module docstring. -/
def LevinGcd {n : ℕ} (f g : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (Z : Finset ((Fin n → ℤ) × ℚ)) (C : ℝ), ∀ u : Fin n → ℕ,
    IsSixSmoothPoint u → ¬ InExceptional Z u → Real.log (gcd6 (evalZ u f) (evalZ u g)) ≤ ε * ht u + C

/-- **Levin, Invent. Math. 2019, Thm 1.1**, packaged: coprime `f, g`, not both vanishing at the
origin, satisfy `LevinGcd`. Stated only. -/
def LevinTheorem : Prop :=
  ∀ (n : ℕ) (f g : MvPolynomial (Fin n) ℤ), IsRelPrime f g →
    (MvPolynomial.eval 0 f ≠ 0 ∨ MvPolynomial.eval 0 g ≠ 0) → LevinGcd f g

/-! ## On a cycle the gcd is `|D|` -/

/-- If `F = 2^i 3^j D` and `G = 2^k 3^l M S` with `D ∣ S` and `D` coprime to `6`, then
`|D| ≤ gcd6(F, G)`. This is the "all places" step: units at `2, 3`, divisibility at `p ∣ D`. -/
theorem abs_Dz_le_gcd6 {w : Word} (hne : w ≠ []) (hE : w.sum ≠ 0) (hdvd : Dz w ∣ Sz w)
    {F G M : ℤ} {i j k l : ℕ} (hF : F = 2 ^ i * 3 ^ j * Dz w) (hG : G = 2 ^ k * 3 ^ l * (M * Sz w))
    : (Dz w).natAbs ≤ gcd6 F G := by
  have hcop : IsCoprime (Dz w) 6 := isCoprime_Dz_six hne hE
  have hD0 : Dz w ≠ 0 := by
    intro h0; rw [h0] at hcop; simp [isCoprime_zero_left] at hcop
    exact absurd hcop (by decide)
  have hdF : Dz w ∣ F := hF ▸ dvd_mul_left _ _
  have hdG : Dz w ∣ G := hG ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdvd _) _
  have hgcd : Dz w ∣ (Int.gcd F G : ℤ) := Int.dvd_coe_gcd hdF hdG
  have hF0 : F ≠ 0 := by rw [hF]; exact mul_ne_zero (by positivity) hD0
  have hnat : Nat.Coprime (Dz w).natAbs 6 := by
    have := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd] using this
  have hd6 : (Dz w).natAbs ∣ gcd6 F G := by
    apply dvd_sixFree hnat
    simpa [Int.natAbs_dvd] using (Int.natAbs_dvd.mpr hgcd)
  have hpos : 0 < gcd6 F G := by
    unfold gcd6
    exact Program.sixFree_pos (by exact_mod_cast (Int.gcd_pos_of_ne_zero_left G hF0).ne')
  exact Nat.le_of_dvd hpos hd6

/-! ## The conditional theorem -/

/-- **Vojta/Levin constrains cycles in an `r`-parameter family.** Let `W L` be the words of a family
whose run coordinates `t L` are a `6`-smooth point at which `F` evaluates to `D` and `G` to `M·S`, up to
`6`-units, and whose height grows at most linearly in the length. Assume `LevinGcd F G` and a lower
bound `B` on `|2^E - 3^o|` (e.g. `Program.lowerBound_of_rhinBound`) that eventually beats
`exp(ε(κ o + κ₀) + C)` for every constant `C`. Then the cycle words of the family have bounded
length outside finitely many exceptional character level sets. -/
theorem cycles_of_levin {n r : ℕ} (F G : MvPolynomial (Fin n) ℤ) (W : (Fin r → ℕ) → Word)
    (t : (Fin r → ℕ) → Fin n → ℕ) (M : ℤ)
    (hne : ∀ L, W L ≠ []) (hE : ∀ L, (W L).sum ≠ 0)
    (hF : ∀ L, ∃ i j : ℕ, evalZ (t L) F = 2 ^ i * 3 ^ j * Dz (W L))
    (hG : ∀ L, ∃ i j : ℕ, evalZ (t L) G = 2 ^ i * 3 ^ j * (M * Sz (W L)))
    (h6 : ∀ L, IsSixSmoothPoint (t L))
    (κ κ₀ : ℝ) (hh : ∀ L, ht (t L) ≤ κ * (W L).length + κ₀)
    {B : ℕ → ℝ} (hB : LowerBound B) (ε : ℝ) (hε : 0 < ε)
    (hgrow : ∀ C : ℝ, ∃ O : ℕ, ∀ o : ℕ, O < o → Real.exp (ε * (κ * o + κ₀) + C) < B o)
    (hLev : LevinGcd F G) :
    ∃ (Z : Finset ((Fin n → ℤ) × ℚ)) (O : ℕ), ∀ L, Dz (W L) ∣ Sz (W L) →
      InExceptional Z (t L) ∨ (W L).length ≤ O := by
  obtain ⟨Z, C, hZ⟩ := hLev ε hε
  obtain ⟨O, hO⟩ := hgrow C
  refine ⟨Z, O, fun L hdvd => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hnZ, hlen⟩ := hcon
  obtain ⟨i, j, hFi⟩ := hF L
  obtain ⟨k, l, hGk⟩ := hG L
  have hle := abs_Dz_le_gcd6 (hne L) (hE L) hdvd hFi hGk
  have hlog := hZ (t L) (h6 L) hnZ
  have hlen0 : 0 < (W L).length := List.length_pos_of_ne_nil (hne L)
  have hBo := hB (W L).sum (W L).length hlen0
  have hgrowL := hO _ hlen
  -- |D| as a real number
  have hcast : (((Dz (W L)).natAbs : ℕ) : ℝ) = |(2 : ℝ) ^ (W L).sum - 3 ^ (W L).length| := by
    rw [Nat.cast_natAbs]; push_cast [Dz, D]; rfl
  have hDpos : (0 : ℝ) < ((Dz (W L)).natAbs : ℝ) := by
    have := lt_of_lt_of_le (Real.exp_pos _) (hgrowL.le.trans (hBo.trans hcast.symm.le))
    exact this
  have h1 : Real.log ((Dz (W L)).natAbs : ℝ) ≤ Real.log (gcd6 (evalZ (t L) F) (evalZ (t L) G)) :=
    Real.log_le_log hDpos (by exact_mod_cast hle)
  have h2 : ε * (κ * (W L).length + κ₀) + C < Real.log ((Dz (W L)).natAbs : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hDpos]
    exact hgrowL.trans_le (hBo.trans hcast.symm.le)
  have h3 : ε * ht (t L) ≤ ε * (κ * (W L).length + κ₀) := mul_le_mul_of_nonneg_left (hh L) hε.le
  linarith

/-- **`r = 1` is the degenerate case.** If some combination of `F` and `G` equals `2^i 3^j c` with
`c ≠ 0`, then `gcd6(F, G) ≤ sixFree c`: the gcd is bounded outright, i.e. Levin holds with `ε = 0`
and no exceptional set. This is what the resultant certificate of `TwoRun.lean` provides. -/
theorem gcd6_le_of_certificate {F G A B c : ℤ} {i j : ℕ} (hc : c ≠ 0)
    (h : A * F + B * G = 2 ^ i * 3 ^ j * c) : gcd6 F G ≤ sixFree c := by
  have hg : (Int.gcd F G : ℤ) ∣ 2 ^ i * 3 ^ j * c := by
    rw [← h]
    exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left F G) _) (dvd_mul_of_dvd_right (Int.gcd_dvd_right F G) _)
  unfold gcd6
  rw [← Program.sixFree_pow_mul i j c]
  have hc' : 2 ^ i * 3 ^ j * c ≠ 0 := mul_ne_zero (by positivity) hc
  -- sixFree is monotone along divisibility of nonzero integers
  have key : ∀ {m k : ℤ}, k ≠ 0 → m ∣ k → sixFree m ≤ sixFree k := by
    intro m k hk hmk
    unfold sixFree
    apply Nat.le_of_dvd (Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 (Int.natAbs_ne_zero.mpr hk)).ne')
    exact Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.ordCompl_dvd_ordCompl_of_dvd
        (Int.natAbs_dvd_natAbs.mpr hmk) 2) 3
  exact key hc' hg

/-! ## The two-length family `d^a e d^b f` (`r = 2`) -/

/-- The two-length word `d^a e d^b f`. -/
def twoLenWord (d e f a b : ℕ) : Word := List.replicate a d ++ [e] ++ List.replicate b d ++ [f]

section Ring

variable {R : Type*} [CommRing R] (X Y : R) (d e f a b : ℕ)

/-- `D` in run coordinates: `Q₁Q₂ v_a v_b - Y² u_a u_b`. -/
theorem twoLen_D :
    D X Y (twoLenWord d e f a b) =
      X ^ e * X ^ f * X ^ (d * a) * X ^ (d * b) - Y ^ 2 * Y ^ a * Y ^ b := by
  simp only [D, twoLenWord, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil, smul_eq_mul]
  ring

/-- `(X^d - Y)·S` in run coordinates: `P Q₁ v_a v_b + P Y u_b v_a - Q₁ Y u_b v_a - Y² u_a u_b`. -/
theorem twoLen_S :
    (X ^ d - Y) * S X Y (twoLenWord d e f a b) =
      X ^ d * X ^ e * X ^ (d * a) * X ^ (d * b) + X ^ d * Y * Y ^ b * X ^ (d * a) -
        X ^ e * Y * Y ^ b * X ^ (d * a) - Y ^ 2 * Y ^ a * Y ^ b := by
  have ha := P1 X Y d a
  have hb := P1 X Y d b
  simp only [D, List.sum_replicate, List.length_replicate, smul_eq_mul] at ha hb
  simp only [twoLenWord, S_append, S_singleton, List.sum_append, List.sum_replicate,
    List.sum_cons, List.sum_nil, List.length_replicate, List.length_cons,
    List.length_nil, smul_eq_mul]
  linear_combination (Y ^ (b + 1 + 1)) * ha + (X ^ (a * d + e) * Y) * hb

end Ring

open MvPolynomial in
/-- `F` for the two-length family: `2^{e+f} x₁x₃ - 9 x₀x₂` in the coordinates
`(x₀, x₁, x₂, x₃) = (3^a, 2^{da}, 3^b, 2^{db})`. -/
noncomputable def Ftl (e f : ℕ) : MvPolynomial (Fin 4) ℤ :=
  C (2 ^ (e + f)) * X 1 * X 3 - C 9 * X 0 * X 2

open MvPolynomial in
/-- `G` for the two-length family (`= (2^d - 3)·S` at the run point). -/
noncomputable def Gtl (d e : ℕ) : MvPolynomial (Fin 4) ℤ :=
  C (2 ^ (d + e)) * X 1 * X 3 + C (3 * 2 ^ d) * X 2 * X 1 - C (3 * 2 ^ e) * X 2 * X 1 - C 9 * X 0 * X 2

/-- The run point of `d^a e d^b f`. -/
def tl (d : ℕ) (L : Fin 2 → ℕ) : Fin 4 → ℕ := ![3 ^ L 0, 2 ^ (d * L 0), 3 ^ L 1, 2 ^ (d * L 1)]

theorem twoLen_F (d e f : ℕ) (L : Fin 2 → ℕ) :
    evalZ (tl d L) (Ftl e f) = 2 ^ 0 * 3 ^ 0 * Dz (twoLenWord d e f (L 0) (L 1)) := by
  simp only [evalZ, Ftl, tl, Dz, twoLen_D, map_sub, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  simp [Matrix.cons_val]
  ring

theorem twoLen_G (d e f : ℕ) (L : Fin 2 → ℕ) :
    evalZ (tl d L) (Gtl d e) =
      2 ^ 0 * 3 ^ 0 * ((2 ^ d - 3) * Sz (twoLenWord d e f (L 0) (L 1))) := by
  have h := twoLen_S (2 : ℤ) 3 d e f (L 0) (L 1)
  simp only [evalZ, Gtl, tl, map_sub, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp only [Sz, pow_zero, one_mul]
  rw [h]
  simp [Matrix.cons_val]
  ring

/-- **Levin ⇒ conditional finiteness for `d^a e d^b f`.** Under `LevinGcd (Ftl e f) (Gtl d e)` and a
lower bound `B` beating `exp(ε (κ o + κ₀) + C)`, the cycle words of the family have bounded length
outside finitely many exceptional character level sets. Here `κ = log 3 + d log 2`, `κ₀ = 0`. -/
theorem twoLen_cycles_of_levin (d e f : ℕ) (he : 1 ≤ e) {B : ℕ → ℝ} (hB : LowerBound B)
    (ε : ℝ) (hε : 0 < ε)
    (hgrow : ∀ C : ℝ, ∃ O : ℕ, ∀ o : ℕ, O < o →
      Real.exp (ε * ((Real.log 3 + d * Real.log 2) * o + 0) + C) < B o)
    (hLev : LevinGcd (Ftl e f) (Gtl d e)) :
    ∃ (Z : Finset ((Fin 4 → ℤ) × ℚ)) (O : ℕ), ∀ L : Fin 2 → ℕ,
      Dz (twoLenWord d e f (L 0) (L 1)) ∣ Sz (twoLenWord d e f (L 0) (L 1)) →
        InExceptional Z (tl d L) ∨ (twoLenWord d e f (L 0) (L 1)).length ≤ O := by
  refine cycles_of_levin (Ftl e f) (Gtl d e) (fun L => twoLenWord d e f (L 0) (L 1)) (tl d)
    (2 ^ d - 3) (fun L => by simp [twoLenWord]) (fun L => by
      simp only [twoLenWord, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil,
        smul_eq_mul]; omega)
    (fun L => ⟨0, 0, twoLen_F d e f L⟩) (fun L => ⟨0, 0, twoLen_G d e f L⟩) ?_
    (Real.log 3 + d * Real.log 2) 0 ?_ hB ε hε hgrow hLev
  · intro L i
    fin_cases i
    · exact ⟨0, L 0, by simp [tl]⟩
    · exact ⟨d * L 0, 0, by simp [tl]⟩
    · exact ⟨0, L 1, by simp [tl]⟩
    · exact ⟨d * L 1, 0, by simp [tl]⟩
  · intro L
    rw [ht_nat _ (fun i => by fin_cases i <;> simp [tl])]
    simp only [Fin.sum_univ_four, tl, Matrix.cons_val, twoLenWord, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    push_cast
    simp only [Real.log_pow]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    push_cast
    nlinarith [h2, h3]

end Syracuse.Vojta
