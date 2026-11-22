import Syracuse.Approaches.CocycleCombine
import Syracuse.Approaches.BoundedDefectLever

/-!
# The two-run family `d^a e₁ d^a e₂ d^a`: a resultant ceiling and full exclusion

Formalization of `approaches/places-elimination` §3–§4. The family is
`BoundedDefectLever.twoRunWord d e₁ e₂ a`. `BoundedDefectLever.TwoRunNoGo` (open, stated only)
asserts that it admits no *unit* scheme: no signed-monomial combination of rotation sums is
`a`-independent. This file shows that the question is the wrong one for exclusion. A certificate whose
coefficients are **polynomial** in the run coordinates `u = Y^a`, `v = X^{da}` gives an
`a`-independent ceiling, uniformly in `(d, e₁, e₂)`.

Write `P = X^d`, `Q₁ = X^{e₁}`, `Q₂ = X^{e₂}`. Then

* `D(w) = Q₁Q₂v³ - Y²u³` (`twoRun_D`);
* `(X^d - Y)·S(w) = G(P,Q₁,Q₂,Y,u,v)`, a cubic form in `[u:v]` (`twoRun_S`);
* `v⁵·Q₁Q₂·R* = A·D + B·G` (`certificate`), where `R* = Q₁²(P-Q₂)³ + Y·Q₂·(P-Q₁)³` is, up to the
  monomial `-Q₁Y⁴`, the resultant `Res_{[u:v]}(D, G)`.

At `(X,Y) = (2,3)`, `u` and `v` are `6`-units and `D` is coprime to `6`. So on a cycle
`D ∣ R*(2^d, 2^{e₁}, 2^{e₂}, 3)` (`twoRun_ceiling`), and this number is nonzero for every genuine
defect (`Rstar_ne_zero`: the two summands have `3`-adic valuations `≡ 0` and `≡ 1 (mod 3)`). Since
`|D|` grows geometrically in `a` (the slope `d` is an integer, so the family is never critical, and no
Baker bound is needed), every family is decided by finitely many checks (`noCycle_of_check`). The
script `approaches/places-elimination/decide_family.py` computes those checks and emits instances such
as `noCycle_1_2_3`.

The certificate is the elimination principle of `places-elimination` §3: the family has **one**
projective run coordinate `[u:v] ∈ ℙ¹` (`r = 1`), so `V(D, G)` does not dominate the character torus,
and the resultant is an equation of its image.

## Coverage

| claim (places-elimination) | Lean name | status |
|---|---|---|
| closed forms of `D`, `S` in run coordinates | `twoRun_D`, `twoRun_S` | proved |
| resultant certificate | `certificate` | proved (`ring`) |
| ceiling `D ∣ R*(2^d,2^{e₁},2^{e₂},3)` on a cycle | `twoRun_ceiling` | proved |
| `R* ≠ 0` unless `e₁ = e₂ = d` | `Rstar_ne_zero` | proved |
| geometric growth of `|D|` | `growth`, `Dz_twoRun` | proved |
| exclusion from finitely many checks | `noCycle_of_check` | proved |
| exclusion from a starting index (small genuine cycles) | `noCycle_ge_of_check` | proved |
| nine sample families, emitted by the decider | `noCycle_1_2_3`, `noCycle_3_1_2`, `cycle_3_1_2_0`, … | proved (`decide`) |
-/

namespace Syracuse.TwoRun

open Syracuse Syracuse.CocycleCombine Syracuse.BoundedDefectLever

section Ring

variable {R : Type*} [CommRing R]

/-- The resultant core `R* = Q₁²(P - Q₂)³ + Y·Q₂·(P - Q₁)³`. -/
def Rstar (P Q₁ Q₂ Y : R) : R := Q₁ ^ 2 * (P - Q₂) ^ 3 + Y * Q₂ * (P - Q₁) ^ 3

/-- `D` of the family in run coordinates. -/
def Dform (Q₁ Q₂ Y u v : R) : R := Q₁ * Q₂ * v ^ 3 - Y ^ 2 * u ^ 3

/-- `(X^d - Y)·S` of the family in run coordinates. -/
def Gform (P Q₁ Q₂ Y u v : R) : R :=
  P * Q₁ * u * v ^ 2 + P * Y * u ^ 2 * v - Q₁ * Q₂ * u * v ^ 2 + Q₁ * Q₂ * v ^ 3 -
    Q₁ * Y * u ^ 2 * v - Y ^ 2 * u ^ 3

/-- First cofactor of the certificate. -/
def Acoef (P Q₁ Q₂ Y u v : R) : R :=
  P^3*Q₁^2*v^2 + P^3*Q₁*Y*u*v + P^3*Q₂*Y*v^2 - 3*P^2*Q₁^2*Q₂*v^2 - P^2*Q₁^2*Y*u*v - 2*P^2*Q₁*Q₂*Y*u*v - 2*P^2*Q₁*Q₂*Y*v^2 - P^2*Q₁*Y^2*u^2 - P^2*Q₂*Y^2*u*v + 3*P*Q₁^2*Q₂^2*v^2 + 2*P*Q₁^2*Q₂*Y*u*v + 2*P*Q₁^2*Q₂*Y*v^2 + P*Q₁*Q₂^2*Y*u*v - P*Q₁*Q₂^2*Y*v^2 + 2*P*Q₁*Q₂*Y^2*u^2 + 2*P*Q₁*Q₂*Y^2*u*v - Q₁^3*Q₂*Y*v^2 - Q₁^2*Q₂^3*v^2 - Q₁^2*Q₂^2*Y*u*v + Q₁^2*Q₂^2*Y*v^2 - Q₁^2*Q₂*Y^2*u*v - Q₁*Q₂^2*Y^2*u^2

/-- Second cofactor of the certificate. -/
def Bcoef (P Q₁ Q₂ Y u v : R) : R :=
  -P^2*Q₁*Q₂*Y*v^2 + P^2*Q₁*Y^2*u^2 + P^2*Q₂*Y^2*u*v + P*Q₁^2*Q₂*Y*v^2 + P*Q₁*Q₂^2*Y*v^2 - 2*P*Q₁*Q₂*Y^2*u^2 - 2*P*Q₁*Q₂*Y^2*u*v - Q₁^2*Q₂^2*Y*v^2 + Q₁^2*Q₂*Y^2*u*v + Q₁*Q₂^2*Y^2*u^2

/-- **The resultant certificate**, an identity in `ℤ[P,Q₁,Q₂,Y,u,v]`. -/
theorem certificate (P Q₁ Q₂ Y u v : R) :
    v ^ 5 * (Q₁ * Q₂ * Rstar P Q₁ Q₂ Y) =
      Acoef P Q₁ Q₂ Y u v * Dform Q₁ Q₂ Y u v + Bcoef P Q₁ Q₂ Y u v * Gform P Q₁ Q₂ Y u v := by
  unfold Rstar Acoef Dform Bcoef Gform; ring

variable (X Y : R) (d e₁ e₂ a : ℕ)

/-- `D` of the two-run word in run coordinates. -/
theorem twoRun_D :
    D X Y (twoRunWord d e₁ e₂ a) = Dform (X ^ e₁) (X ^ e₂) Y (Y ^ a) (X ^ (d * a)) := by
  simp only [D, twoRunWord, Dform, List.sum_append, List.sum_replicate, List.sum_cons,
    List.sum_nil, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    smul_eq_mul]
  ring

/-- `(X^d - Y)·S` of the two-run word in run coordinates. -/
theorem twoRun_S :
    (X ^ d - Y) * S X Y (twoRunWord d e₁ e₂ a) =
      Gform (X ^ d) (X ^ e₁) (X ^ e₂) Y (Y ^ a) (X ^ (d * a)) := by
  have h := P1 X Y d a
  simp only [D, List.sum_replicate, List.length_replicate, smul_eq_mul] at h
  simp only [twoRunWord, Gform, S_append, S_singleton, List.sum_append, List.sum_replicate,
    List.sum_cons, List.sum_nil, List.length_replicate, List.length_cons,
    List.length_nil, smul_eq_mul]
  linear_combination (Y ^ (a + (1 + (a + 1))) + X ^ (a * d + e₁) * Y ^ (a + 1) +
    X ^ (a * d + e₁ + a * d + e₂)) * h

end Ring

/-! ## The ceiling at `(2, 3)` -/

/-- Shorthand for the family's word. -/
abbrev w (d e₁ e₂ a : ℕ) : Word := twoRunWord d e₁ e₂ a

/-- The integer ceiling `R*(2^d, 2^{e₁}, 2^{e₂}, 3)`. -/
def Rz (d e₁ e₂ : ℕ) : ℤ := Rstar ((2 : ℤ) ^ d) (2 ^ e₁) (2 ^ e₂) 3

/-- **The `a`-independent ceiling.** If `D ∣ S` (in particular on a cycle), then `D` divides
`R*(2^d, 2^{e₁}, 2^{e₂}, 3)`. -/
theorem twoRun_ceiling {d e₁ e₂ a : ℕ} (he : 1 ≤ e₁) (h : Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a)) :
    Dz (w d e₁ e₂ a) ∣ Rz d e₁ e₂ := by
  have hcop : IsCoprime (Dz (w d e₁ e₂ a)) 6 := by
    apply isCoprime_Dz_six
    · simp [twoRunWord]
    · simp only [twoRunWord, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil,
        smul_eq_mul]
      omega
  have hD := twoRun_D (2 : ℤ) 3 d e₁ e₂ a
  have hG := twoRun_S (2 : ℤ) 3 d e₁ e₂ a
  have hc := certificate ((2 : ℤ) ^ d) (2 ^ e₁) (2 ^ e₂) 3 (3 ^ a) (2 ^ (d * a))
  rw [← hD, ← hG] at hc
  have hdiv : Dz (w d e₁ e₂ a) ∣ 2 ^ (5 * (d * a) + e₁ + e₂) * 3 ^ 0 * Rz d e₁ e₂ := by
    have : (2 : ℤ) ^ (5 * (d * a) + e₁ + e₂) * 3 ^ 0 * Rz d e₁ e₂ =
        (2 ^ (d * a)) ^ 5 * (2 ^ e₁ * 2 ^ e₂ * Rstar ((2 : ℤ) ^ d) (2 ^ e₁) (2 ^ e₂) 3) := by
      rw [Rz]; ring
    rw [this, hc]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _)
  exact dvd_of_isCoprime_six_of_dvd hcop _ _ hdiv

/-- `2^m = 2^n` in `ℤ` forces `m = n`. -/
lemma two_pow_inj {m n : ℕ} (h : (2 : ℤ) ^ m = 2 ^ n) : m = n :=
  pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num) h

/-- **The ceiling is nonzero for every genuine defect.** `R* = 0` forces `e₁ = e₂ = d` (the pure
circuit): otherwise the two summands have `3`-adic valuations `3·v(x)` and `1 + 3·v(y)`. -/
theorem Rstar_ne_zero {d e₁ e₂ : ℕ} (h : ¬(e₁ = d ∧ e₂ = d)) : Rz d e₁ e₂ ≠ 0 := by
  intro h0
  simp only [Rz, Rstar] at h0
  set x : ℤ := 2 ^ d - 2 ^ e₂ with hx
  set y : ℤ := 2 ^ d - 2 ^ e₁ with hy
  by_cases hy0 : y = 0
  · have he₁ : e₁ = d := (two_pow_inj (by linarith : (2 : ℤ) ^ e₁ = 2 ^ d))
    rw [hy0] at h0
    have : x = 0 := by
      have h4 : ((2 : ℤ) ^ e₁) ^ 2 ≠ 0 := by positivity
      have : ((2 : ℤ) ^ e₁) ^ 2 * x ^ 3 = 0 := by linarith
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h4)
    exact h ⟨he₁, (two_pow_inj (by linarith : (2 : ℤ) ^ e₂ = 2 ^ d))⟩
  · have hx0 : x ≠ 0 := by
      intro hx0; rw [hx0] at h0
      have : (3 : ℤ) * 2 ^ e₂ * y ^ 3 = 0 := by linarith
      simp [hy0] at this
    -- natAbs both sides: 4^{e₁}|x|³ = 3·2^{e₂}|y|³
    have key : (2 ^ (2 * e₁) * x.natAbs ^ 3 : ℕ) = 3 * 2 ^ e₂ * y.natAbs ^ 3 := by
      have : ((2 : ℤ) ^ e₁) ^ 2 * x ^ 3 = -(3 * 2 ^ e₂ * y ^ 3) := by linarith
      have := congrArg Int.natAbs this
      simpa [Int.natAbs_mul, Int.natAbs_pow, pow_mul, mul_comm, mul_assoc, mul_left_comm] using this
    have hxa : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx0
    have hya : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy0
    have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have v2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have L : padicValNat 3 (2 ^ (2 * e₁) * x.natAbs ^ 3) = 3 * padicValNat 3 x.natAbs := by
      rw [padicValNat.mul (by positivity) (pow_ne_zero _ hxa), padicValNat.pow, padicValNat.pow, v2]
      ring
    have Rr : padicValNat 3 (3 * 2 ^ e₂ * y.natAbs ^ 3) = 1 + 3 * padicValNat 3 y.natAbs := by
      rw [padicValNat.mul (by positivity) (pow_ne_zero _ hya), padicValNat.mul (by norm_num)
        (by positivity), padicValNat.self (by norm_num), padicValNat.pow, padicValNat.pow, v2]
      ring
    have := congrArg (padicValNat 3) key
    rw [L, Rr] at this
    omega

/-! ## Growth of `|D|` and exclusion from finitely many checks -/

/-- `A α^a - B β^a` is nondecreasing once nonnegative, for `1 ≤ β ≤ α`, `0 ≤ A`. -/
theorem growth {A B α β c : ℤ} {a₀ : ℕ} (hβ : 1 ≤ β) (hαβ : β ≤ α) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (h0 : c < A * α ^ a₀ - B * β ^ a₀) : ∀ a, a₀ ≤ a → c < A * α ^ a - B * β ^ a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact h0
  | succ n _ ih =>
    have hαn : 0 ≤ A * α ^ n := mul_nonneg hA (pow_nonneg (by linarith) _)
    have : β * (A * α ^ n - B * β ^ n) ≤ A * α ^ (n + 1) - B * β ^ (n + 1) := by
      have := mul_le_mul_of_nonneg_right hαβ hαn
      rw [pow_succ, pow_succ]; nlinarith
    nlinarith

/-- `D` of the family as a difference of two exponentials in `a`. -/
theorem Dz_twoRun (d e₁ e₂ a : ℕ) :
    Dz (w d e₁ e₂ a) = 2 ^ (e₁ + e₂) * (2 ^ (3 * d)) ^ a - 9 * 27 ^ a := by
  have h27 : (27 : ℤ) ^ a = 3 ^ (3 * a) := by rw [pow_mul]; norm_num
  rw [Dz, twoRun_D, Dform, h27]; ring

/-- The signed size `g(a)` used for growth: `-D` when `d = 1` (the `3^o`-dominant case), `D` when
`d ≥ 2` (the `2^E`-dominant case). -/
def g (d e₁ e₂ a : ℕ) : ℤ := if d = 1 then -Dz (w d e₁ e₂ a) else Dz (w d e₁ e₂ a)

/-- **Exclusion from finitely many checks.** For a genuine defect, if `D_a ∤ S_a` for every
`a < a₀` and `g(a₀) > |R*|`, then no member of the family is a cycle word. -/
theorem noCycle_of_check {d e₁ e₂ : ℕ} (a₀ : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e₁)
    (hgen : ¬(e₁ = d ∧ e₂ = d))
    (hsmall : ∀ a < a₀, ¬ Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a))
    (hbig : |Rz d e₁ e₂| < g d e₁ e₂ a₀) :
    ∀ a, ¬ Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a) := by
  intro a hdvd
  by_cases ha : a < a₀
  · exact hsmall a ha hdvd
  have ha' : a₀ ≤ a := not_lt.mp ha
  have hgrow : |Rz d e₁ e₂| < g d e₁ e₂ a := by
    by_cases h1 : d = 1
    · subst h1
      have := growth (A := 9) (B := 2 ^ (e₁ + e₂)) (α := 27) (β := 2 ^ (3 * 1)) (c := |Rz 1 e₁ e₂|)
        (a₀ := a₀) (by norm_num) (by norm_num) (by norm_num) (abs_nonneg _)
        (by simpa [g, Dz_twoRun] using hbig) a ha'
      simpa [g, Dz_twoRun] using this
    · have h64 : (27 : ℤ) ≤ (2 : ℤ) ^ (3 * d) := by
        calc (27 : ℤ) ≤ 2 ^ (3 * 2) := by norm_num
          _ ≤ 2 ^ (3 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      have := growth (A := 2 ^ (e₁ + e₂)) (B := 9) (α := 2 ^ (3 * d)) (β := 27)
        (c := |Rz d e₁ e₂|) (a₀ := a₀) (by norm_num) h64 (by positivity) (abs_nonneg _)
        (by simpa [g, h1, Dz_twoRun] using hbig) a ha'
      simpa [g, h1, Dz_twoRun] using this
  have hR := Rstar_ne_zero hgen
  have hle : |Dz (w d e₁ e₂ a)| ≤ |Rz d e₁ e₂| :=
    Int.le_of_dvd (abs_pos.mpr hR) ((abs_dvd_abs _ _).mpr (twoRun_ceiling he hdvd))
  have : g d e₁ e₂ a ≤ |Dz (w d e₁ e₂ a)| := by
    unfold g; split_ifs
    · exact neg_le_abs _
    · exact le_abs_self _
  linarith

/-- **Exclusion from a starting index.** As `noCycle_of_check`, but only for `a ≥ a₁`: use this when
a small member is a genuine cycle (e.g. `a = 0` gives `[e₁, e₂]`, and `[1, 2]` is the `-5` cycle). -/
theorem noCycle_ge_of_check {d e₁ e₂ : ℕ} (a₁ a₀ : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e₁)
    (hgen : ¬(e₁ = d ∧ e₂ = d))
    (hsmall : ∀ a, a₁ ≤ a → a < a₀ → ¬ Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a))
    (hbig : |Rz d e₁ e₂| < g d e₁ e₂ a₀) :
    ∀ a, a₁ ≤ a → ¬ Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a) := by
  intro a ha₁ hdvd
  by_cases ha : a < a₀
  · exact hsmall a ha₁ ha hdvd
  have key := noCycle_of_check (d := d) (e₁ := e₁) (e₂ := e₂) a₀ hd he hgen
  -- reuse the large-`a` half: build the small-`a` hypothesis vacuously above `a₀`
  have hR := Rstar_ne_zero hgen
  have hgrow : |Rz d e₁ e₂| < g d e₁ e₂ a := by
    by_cases h1 : d = 1
    · subst h1
      have := growth (A := 9) (B := 2 ^ (e₁ + e₂)) (α := 27) (β := 2 ^ (3 * 1)) (c := |Rz 1 e₁ e₂|)
        (a₀ := a₀) (by norm_num) (by norm_num) (by norm_num) (abs_nonneg _)
        (by simpa [g, Dz_twoRun] using hbig) a (not_lt.mp ha)
      simpa [g, Dz_twoRun] using this
    · have h64 : (27 : ℤ) ≤ (2 : ℤ) ^ (3 * d) := by
        calc (27 : ℤ) ≤ 2 ^ (3 * 2) := by norm_num
          _ ≤ 2 ^ (3 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      have := growth (A := 2 ^ (e₁ + e₂)) (B := 9) (α := 2 ^ (3 * d)) (β := 27)
        (c := |Rz d e₁ e₂|) (a₀ := a₀) (by norm_num) h64 (by positivity) (abs_nonneg _)
        (by simpa [g, h1, Dz_twoRun] using hbig) a (not_lt.mp ha)
      simpa [g, h1, Dz_twoRun] using this
  have hle : |Dz (w d e₁ e₂ a)| ≤ |Rz d e₁ e₂| :=
    Int.le_of_dvd (abs_pos.mpr hR) ((abs_dvd_abs _ _).mpr (twoRun_ceiling he hdvd))
  have : g d e₁ e₂ a ≤ |Dz (w d e₁ e₂ a)| := by
    unfold g; split_ifs
    · exact neg_le_abs _
    · exact le_abs_self _
  clear key
  linarith

/-- The same, stated for genuine `3x+1` cycles (any sign). -/
theorem noSyrCycle_of_check {d e₁ e₂ : ℕ} (a₀ : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e₁)
    (hgen : ¬(e₁ = d ∧ e₂ = d))
    (hsmall : ∀ a < a₀, ¬ Dz (w d e₁ e₂ a) ∣ Sz (w d e₁ e₂ a))
    (hbig : |Rz d e₁ e₂| < g d e₁ e₂ a₀) (x : ℤ) (o a : ℕ) (hc : IsSyrCycle x o)
    (hw : gapWord x o = w d e₁ e₂ a) : False := by
  have := hc.cycle_equation
  rw [hw] at this
  exact noCycle_of_check a₀ hd he hgen hsmall hbig a ⟨x, by rw [← this]⟩

/-! ## Sample families (emitted verbatim by `decide_family.py tworun D E1 E2 --lean`) -/

/-- `1^a 2 1^a 3 1^a`: emitted by `decide_family.py tworun 1 2 3`
(ceiling `sixfree R* = 19`, `a₀ = 2`). -/
theorem noCycle_1_2_3 : ∀ a, ¬ Dz (w 1 2 3 a) ∣ Sz (w 1 2 3 a) :=
  noCycle_of_check 2 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `2^a 1 2^a 3 2^a`: emitted by `decide_family.py tworun 2 1 3`
(ceiling `sixfree R* = 1`, `a₀ = 1`). -/
theorem noCycle_2_1_3 : ∀ a, ¬ Dz (w 2 1 3 a) ∣ Sz (w 2 1 3 a) :=
  noCycle_of_check 1 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `1^a 3 1^a 2 1^a`: emitted by `decide_family.py tworun 1 3 2`
(ceiling `sixfree R* = 97`, `a₀ = 2`). -/
theorem noCycle_1_3_2 : ∀ a, ¬ Dz (w 1 3 2 a) ∣ Sz (w 1 3 2 a) :=
  noCycle_of_check 2 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `3^a 1 3^a 2 3^a`: emitted by `decide_family.py tworun 3 1 2`.
Cycles at `a ∈ [0]`, none for `a ≥ 1`. -/
theorem cycle_3_1_2_0 : Dz (w 3 1 2 0) ∣ Sz (w 3 1 2 0) := by decide

theorem noCycle_3_1_2 : ∀ a, 1 ≤ a → ¬ Dz (w 3 1 2 a) ∣ Sz (w 3 1 2 a) :=
  noCycle_ge_of_check 1 1 (by norm_num) (by norm_num) (by decide)
    (by intro a h1 h2; omega)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `2^a 3 2^a 1 2^a`: emitted by `decide_family.py tworun 2 3 1`
(ceiling `sixfree R* = 1`, `a₀ = 1`). -/
theorem noCycle_2_3_1 : ∀ a, ¬ Dz (w 2 3 1 a) ∣ Sz (w 2 3 1 a) :=
  noCycle_of_check 1 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `1^a 1 1^a 2 1^a`: emitted by `decide_family.py tworun 1 1 2`.
Cycles at `a ∈ [0]`, none for `a ≥ 1`. -/
theorem cycle_1_1_2_0 : Dz (w 1 1 2 0) ∣ Sz (w 1 1 2 0) := by decide

theorem noCycle_1_1_2 : ∀ a, 1 ≤ a → ¬ Dz (w 1 1 2 a) ∣ Sz (w 1 1 2 a) :=
  noCycle_ge_of_check 1 1 (by norm_num) (by norm_num) (by decide)
    (by intro a h1 h2; omega)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `2^a 1 2^a 1 2^a`: emitted by `decide_family.py tworun 2 1 1`.
Cycles at `a ∈ [0]`, none for `a ≥ 1`. -/
theorem cycle_2_1_1_0 : Dz (w 2 1 1 0) ∣ Sz (w 2 1 1 0) := by decide

theorem noCycle_2_1_1 : ∀ a, 1 ≤ a → ¬ Dz (w 2 1 1 a) ∣ Sz (w 2 1 1 a) :=
  noCycle_ge_of_check 1 2 (by norm_num) (by norm_num) (by decide)
    (by intro a h1 h2; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `1^a 4 1^a 2 1^a`: emitted by `decide_family.py tworun 1 4 2`
(ceiling `sixfree R* = 1093`, `a₀ = 3`). -/
theorem noCycle_1_4_2 : ∀ a, ¬ Dz (w 1 4 2 a) ∣ Sz (w 1 4 2 a) :=
  noCycle_of_check 3 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

/-- `3^a 2 3^a 5 3^a`: emitted by `decide_family.py tworun 3 2 5`
(ceiling `sixfree R* = 35`, `a₀ = 2`). -/
theorem noCycle_3_2_5 : ∀ a, ¬ Dz (w 3 2 5 a) ∣ Sz (w 3 2 5 a) :=
  noCycle_of_check 2 (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])

end Syracuse.TwoRun
