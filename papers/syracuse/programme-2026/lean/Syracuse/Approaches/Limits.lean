import Syracuse.Approaches.CycleGcd
import Syracuse.Approaches.CirculantMatrix
import Syracuse.Approaches.CocycleCombine
import Syracuse.Approaches.BoundedDefectLever
import Syracuse.Approaches.Program
import Syracuse.Approaches.CycleLiterature

/-!
# Limits of the cocycle approach

Machine-checked facts for the review report on what the cocycle / rotation-gcd approach can and
cannot see. Notation of `Syracuse.Basic`: `S^{(j)} = Sz (w.rotate j)`, `D = Dz w = 2^E - 3^o`,
`E = w.sum`, `o = w.length`, `G = CycleGcd.G w = gcd_j S^{(j)}`. A *positive* word has every gap
`≥ 1`.

The message of the file is that the cocycle data `(S^{(j)}, D)` of a word does not know which map
it comes from or the sign of the cycle:

* `G` is a two-term gcd `gcd(S, D)` (F1), so the rotation sums carry no information beyond one pair.
* **Every** nonempty positive word is the gap word of a positive cycle of the map `x ↦ 3x + k(w)`
  with `k(w) = D/gcd(S, D)` and starting point `a(w) = S/gcd(S, D)`. The `3x + 1` cycles are
  exactly the words with `k(w) = 1`. For example `(1, 4)` is the `3x + 23` cycle `5 → 19 → 5`, and
  the `-17` word is the `3x - 1` cycle through `17`.
* The generic identities and the floor hold verbatim at `(X, Y) = (2, 5)`, where genuine `5x + 1`
  cycles exist, and for negative `3x + 1` cycles; the bounded-defect ceiling is attained (`139`) on
  the `-17` cycle.
* What *does* exclude families is the size information of the ratio sandwich: fixed-slope runs
  `β d^L` are bounded in `L` on nontrivial positive cycles (F2).

## Coverage

| item | Lean name | status |
|---|---|---|
| F1: `G = gcd(S, D)` (nonempty, `E ≥ 1`; positive words) | `G_eq_gcd`, `G_eq_gcd_of_pos` | proved (reuses `CirculantMatrix.gcd_S_rotate`) |
| F1: link to `CirculantMatrix.gcdRot`, `Program.rotGcd`, `CocycleCombine.rotGcd` | `gcdRot_eq_G`, `program_rotGcd_eq_G`, `cocycleCombine_rotGcd_eq_G` | proved |
| generalized map `syrK k`, `gapK`, `gapWordK`, `IsCycleK`; `k = 1` is `syr` | `syrK`, `gapK`, `gapWordK`, `IsCycleK`, `syrK_one`, `gapK_one`, `gapWordK_one`, `isCycleK_one_iff` | defined / proved |
| scaled cycle equation `D a = k S`, `k = D/G`, `a = S/G` | `gSD`, `kOf`, `aOf`, `cycle_equation_k`, `stepK`, `gapWordK_of_eq` | proved |
| every positive word is a positive cycle of `3x + k(w)` with gap word `w` | `every_word_is_a_cycle`, `every_word_is_a_cycle_of_Dz_pos` | proved (full orbit theorem, any sign of `D`; `k > 0 ⟺ D > 0`: `kOf_pos_iff`) |
| `3x + 1` cycle (either sign) `⟺ \|k(w)\| = 1 ⟺ D ∣ S` | `exists_cycle_iff_natAbs_kOf`, `dvd_iff_natAbs_kOf` | proved |
| positive `3x + 1` cycle `⟺ k(w) = 1 ⟺ D > 0 ∧ D ∣ S` | `positive_cycle_iff_kOf_eq_one`, `kOf_eq_one_iff` | proved |
| `5x + 1` cycles `1→3→1` `(1,4)`, `13→33→83→13` `(1,1,5)`, `17→43→27→17` `(1,3,3)`, `D = 7, 3, 3 > 0` | `five_cycle_one`, `five_cycle_thirteen`, `five_cycle_seventeen`, `five_cycles_odd`, `five_cycles_floor` | proved (by computation) |
| negative `3x + 1` cycles `-1`, `-5`, `-17` have `D < 0` | `negative_cycles_D` | proved (reuses `CycleLiterature`) |
| `3x - 1` duality `a ↦ -a` | `syrK_neg`, `gapK_neg`, `iterate_syrK_neg`, `gapWordK_neg`, `isCycleK_neg_iff`, `isSyrCycle_iff_isCycleK_neg_one`, `gapWordK_neg_one`, `three_x_minus_one_cycles` | proved |
| examples: `-17` word has `(G, k, a) = (139, -1, 17)`; `(1,4)` has `(k, a) = (23, 5)` | `neg17_word_data`, `word14_data` | proved (by computation) |
| sign-blind floor on the `-17` cycle: `139 ∣ sixFree C`, `139 ≤ sixFree C`, `139 ≤ \|C\|` | `floor_neg17` | proved (instance of `Program.floor`) |
| bounded-defect ceiling of the `-17` cycle (`β = (2,1,1,4)`, `d = 1`): core `278`, ceiling `139 = \|D\|` | `neg17_isRotated`, `ceiling_neg17` | proved (instance of `BoundedDefectLever.ceiling`; tight) |
| q-invariance at `(2, 5)`: rotation recursion, `S_append`, floor | `rotation_recursion_two_five`, `S_append_two_five`, `floor_two_five`, `five_cycle_thirteen_rotations` | proved |
| `2E ≤ 3o ⇒ D < 0`; positive cycle `⇒ 3o < 2E` | `Dz_neg_of_two_mul_sum_le`, `three_mul_length_lt` | proved |
| F2(a) `d = 1`: `2\|β\| ≤ L + 3 len β ⇒ D < 0`; positive cycle `⇒ L + 3 len β < 2\|β\|` | `Dz_neg_one_background`, `one_background_bound` | proved |
| F2(b) `d ≥ 3`: `(d-2)L + \|β\| ≤ 2 len β`, `L ≤ len β` (from `E ≤ 2o`) | `steep_background_bound` | proved |
| F2(b) `d = 2`, nontrivial: `2^E 3^o ≤ 10^o` (minimum `≥ 3`), hence `L ≤ 3 len β` | `three_le_of_nontrivial`, `two_pow_mul_three_pow_le`, `two_background_bound` | proved; nontriviality needed (`trivial_two_background`) |
| F2 unified: nontrivial positive cycle on `β d^L` `⇒ L ≤ 2\|β\| + 3 len β` | `background_bound` | proved |
| (optional) Ellison `⇒` a family with 6-free ceiling `c` has no cycle once `E ∉` exceptions and `c² ≤ 2^E`; explicit `E ≥ 28` | `no_cycle_of_ellison`, `no_cycle_of_ellison_ge` | proved (conditional on `CycleLiterature.Ellison1971`) |
| `d = 2` with the sharper minimum `≥ 5` (would sharpen `L ≤ 3 len β` to about `L ≤ 2.1 len β`) | — | not done (the minimum `≥ 3` suffices for an explicit bound) |
| orbit points `a_j = S^{(j)}/G` named individually | — | not done (only `a_0` and the return are stated; the intermediate points are implicit in `gapWordK_of_eq`) |
-/

namespace Syracuse.Limits

open Finset

/-! ## F1. `G` is a two-term gcd -/

/-- **F1, `G` is a two-term gcd.** For a nonempty word with `E ≥ 1`, the gcd of all rotation sums
`G(w) = gcd_j S^{(j)}` equals `gcd(S(w), D(w))`. One direction is `G ∣ S` and `G ∣ D`
(`CycleGcd.G_dvd_D`); the other is the rotation collapse `CirculantMatrix.gcd_S_rotate`
(`gcd(S^{(j)}, D)` does not depend on `j`, by induction on `j` from `2^{d_j} S^{(j+1)} = 3S^{(j)} + D`
with `D` prime to `6`). -/
theorem G_eq_gcd {w : Word} (hE : 0 < w.sum) (hne : w ≠ []) :
    CycleGcd.G w = (Int.gcd (Sz w) (Dz w) : ℤ) := by
  apply Int.dvd_antisymm (CycleGcd.G_nonneg w) (Int.natCast_nonneg _)
  · have h0 := CycleGcd.G_dvd_S_rotate w 0
    rw [List.rotate_zero] at h0
    exact Int.dvd_coe_gcd h0 (CycleGcd.G_dvd_D w)
  · refine CycleGcd.dvd_G fun j _ => ?_
    rw [← CirculantMatrix.gcd_S_rotate w hE hne j]
    exact Int.gcd_dvd_left _ _

/-- A nonempty positive word has `E ≥ 1`. -/
lemma sum_pos_of_pos {w : Word} (hw : w.Pos) (hne : w ≠ []) : 0 < w.sum := by
  have := CycleLiterature.length_le_sum hw
  have := List.length_pos_of_ne_nil hne
  omega

/-- **F1 for positive words.** For a nonempty positive word, `G(w) = gcd(S(w), D(w))`. -/
theorem G_eq_gcd_of_pos {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    CycleGcd.G w = (Int.gcd (Sz w) (Dz w) : ℤ) :=
  G_eq_gcd (sum_pos_of_pos hw hne) hne

/-- **F1, connection to `CirculantMatrix`.** The natural-number gcd `gcdRot` of `CirculantMatrix`
(whose two-term form is `CirculantMatrix.gcdRot_eq`) is the same number as `CycleGcd.G`. -/
theorem gcdRot_eq_G {w : Word} (hE : 0 < w.sum) (hne : w ≠ []) :
    (CirculantMatrix.gcdRot w : ℤ) = CycleGcd.G w := by
  rw [CirculantMatrix.gcdRot_eq w hE hne, G_eq_gcd hE hne]

/-- `Program.rotGcd` is literally `CycleGcd.G`. -/
theorem program_rotGcd_eq_G (w : Word) : Program.rotGcd w = CycleGcd.G w := rfl

/-- `CocycleCombine.rotGcd` is literally `CycleGcd.G`. -/
theorem cocycleCombine_rotGcd_eq_G (w : Word) : CocycleCombine.rotGcd w = CycleGcd.G w := rfl

/-! ## Every word is a cycle of some `3x + k` map -/

/-- The number of halvings after the step `a ↦ 3a + k`: `ν₂(3a + k)`. -/
def gapK (k a : ℤ) : ℕ := padicValInt 2 (3 * a + k)

/-- The generalized accelerated map `a ↦ (3a + k) / 2^{ν₂(3a + k)}` on `ℤ`. -/
def syrK (k a : ℤ) : ℤ := (3 * a + k) / 2 ^ (padicValInt 2 (3 * a + k))

/-- `syrK k a = (3a + k) / 2^{gapK k a}`. -/
lemma syrK_eq (k a : ℤ) : syrK k a = (3 * a + k) / 2 ^ gapK k a := rfl

/-- The gap word of the first `o` steps of `syrK k` from `a`. -/
def gapWordK (k a : ℤ) : ℕ → Word
  | 0 => []
  | o + 1 => gapK k a :: gapWordK k (syrK k a) o

/-- `a` is a cycle point of period `o ≥ 1` of the odd-to-odd map `syrK k`. -/
def IsCycleK (k a : ℤ) (o : ℕ) : Prop := 0 < o ∧ Odd a ∧ (syrK k)^[o] a = a

/-- At `k = 1` the generalized map is the Syracuse map. -/
theorem syrK_one : syrK 1 = syr := rfl

/-- At `k = 1` the generalized gap is the Syracuse gap. -/
theorem gapK_one : gapK 1 = gap := rfl

/-- At `k = 1` the generalized gap word is the Syracuse gap word. -/
theorem gapWordK_one (a : ℤ) (o : ℕ) : gapWordK 1 a o = gapWord a o := by
  induction o generalizing a with
  | zero => rfl
  | succ o ih => simp only [gapWordK, gapWord, ih]; rfl

/-- At `k = 1` a `syrK`-cycle is a Syracuse cycle. -/
theorem isCycleK_one_iff {a : ℤ} {o : ℕ} : IsCycleK 1 a o ↔ IsSyrCycle a o := Iff.rfl

/-- `2^{gapK k a} · syrK k a = 3a + k`. -/
lemma two_pow_gapK_mul_syrK (k a : ℤ) : 2 ^ gapK k a * syrK k a = 3 * a + k := by
  have h : ((2 : ℕ) : ℤ) ^ padicValInt 2 (3 * a + k) ∣ 3 * a + k := padicValInt_dvd _
  push_cast at h
  rw [syrK, gapK, mul_comm]
  exact Int.ediv_mul_cancel h

/-- Reading `gapK` and `syrK` off a factorisation `3a + k = 2^m b` with `b` odd. -/
theorem gapK_syrK_of_eq {k a b : ℤ} {m : ℕ} (h : 3 * a + k = 2 ^ m * b) (hb : Odd b) :
    gapK k a = m ∧ syrK k a = b := by
  have hb0 : b ≠ 0 := by rintro rfl; exact absurd hb (by decide)
  have hg : gapK k a = m := by
    have h1 : padicValInt 2 ((2 : ℤ) ^ m) = m := by
      rw [show (2 : ℤ) ^ m = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
        padicValNat.prime_pow]
    have h2 : padicValInt 2 b = 0 := by
      refine padicValInt.eq_zero_of_not_dvd ?_
      rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]
      exact hb
    rw [gapK, h, padicValInt.mul (pow_ne_zero _ two_ne_zero) hb0, h1, h2, add_zero]
  refine ⟨hg, ?_⟩
  rw [syrK_eq, hg, h, Int.mul_ediv_cancel_left _ (pow_ne_zero _ two_ne_zero)]

/-- **One step of the scaled cycle equation.** If `D(d :: w) a = k S(d :: w)` for a positive word
and an odd `k`, then `gapK k a = d` and `syrK k a` solves the scaled cycle equation of the rotated
word `w ++ [d]`. -/
theorem stepK {k : ℤ} (hk : Odd k) {d : ℕ} {w : Word} {a : ℤ} (hw : Word.Pos (d :: w))
    (h : Dz (d :: w) * a = k * Sz (d :: w)) :
    gapK k a = d ∧ Dz (w ++ [d]) * syrK k a = k * Sz (w ++ [d]) := by
  have hpos' : Word.Pos (w ++ [d]) := fun x hx => hw x (by simp at hx ⊢; tauto)
  have hD : Odd (Dz (d :: w)) :=
    CycleLiterature.Dz_odd (by have := hw d (by simp); simp; omega)
  have hrot := rotation_recursion (2 : ℤ) 3 d w
  have hDrot : Dz (w ++ [d]) = Dz (d :: w) := by rw [← rotate_one_cons]; exact D_rotate _ _ _ 1
  have hcop : IsCoprime (Dz (d :: w)) (2 ^ d) :=
    ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).2
      (by rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact hD)).symm.pow_right
  have key : 2 ^ d * (k * Sz (w ++ [d])) = Dz (d :: w) * (3 * a + k) := by
    linear_combination k * hrot - 3 * h
  obtain ⟨b, hb⟩ : Dz (d :: w) ∣ k * Sz (w ++ [d]) :=
    hcop.dvd_of_dvd_mul_left ⟨3 * a + k, key⟩
  have hb' : 2 ^ d * b = 3 * a + k := by
    apply mul_left_cancel₀ (CycleLiterature.ne_zero_of_odd hD)
    rw [← key, hb]; ring
  have hbodd : Odd b := by
    have : Odd (k * Sz (w ++ [d])) := hk.mul (CycleLiterature.Sz_odd hpos' (by simp))
    rw [hb] at this; exact (Int.odd_mul.1 this).2
  obtain ⟨hg, hs⟩ := gapK_syrK_of_eq hb'.symm hbodd
  exact ⟨hg, by rw [hs, hDrot, hb]⟩

/-- Running the scaled cycle equation along a prefix `u` of `u ++ v`. -/
theorem gapWordK_of_eq {k : ℤ} (hk : Odd k) (u : Word) : ∀ (v : Word) (a : ℤ),
    Word.Pos (u ++ v) → Dz (u ++ v) * a = k * Sz (u ++ v) →
    gapWordK k a u.length = u ∧ Dz (v ++ u) * (syrK k)^[u.length] a = k * Sz (v ++ u) := by
  induction u with
  | nil => intro v a _ h; simpa [gapWordK] using h
  | cons d u ih =>
    intro v a hpos h
    obtain ⟨hg, hs⟩ := stepK hk (w := u ++ v) hpos h
    have hpos' : Word.Pos (u ++ (v ++ [d])) := fun x hx => hpos x (by simp at hx ⊢; tauto)
    obtain ⟨h1, h2⟩ := ih (v ++ [d]) (syrK k a) hpos' (by simpa [List.append_assoc] using hs)
    refine ⟨by simp [gapWordK, hg, h1], ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    simpa [List.append_assoc] using h2

/-- `g(w) = gcd(S(w), D(w))` as an integer (by F1 this is `G(w)`). -/
def gSD (w : Word) : ℤ := Int.gcd (Sz w) (Dz w)

/-- The additive constant `k(w) = D(w) / gcd(S, D)` of the map `3x + k(w)` that realises `w`. -/
def kOf (w : Word) : ℤ := Dz w / gSD w

/-- The cycle point `a(w) = S(w) / gcd(S, D)` that realises `w` under `3x + k(w)`. -/
def aOf (w : Word) : ℤ := Sz w / gSD w

/-- `gcd(S, D) > 0` for a nonempty word. -/
lemma gSD_pos {w : Word} (hne : w ≠ []) : 0 < gSD w := by
  unfold gSD
  exact_mod_cast Int.gcd_pos_of_ne_zero_right _ (CycleGcd.Dz_ne_zero hne)

/-- `S = gcd(S, D) · a(w)`. -/
lemma Sz_eq_gSD_mul (w : Word) : Sz w = gSD w * aOf w := by
  rw [aOf, mul_comm, gSD, Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]

/-- `D = gcd(S, D) · k(w)`. -/
lemma Dz_eq_gSD_mul (w : Word) : Dz w = gSD w * kOf w := by
  rw [kOf, mul_comm, gSD, Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)]

/-- **The cycle equation, scaled form.** `D(w) · a(w) = k(w) · S(w)` for every word. -/
theorem cycle_equation_k (w : Word) : Dz w * aOf w = kOf w * Sz w := by
  rw [Dz_eq_gSD_mul, Sz_eq_gSD_mul]; ring

/-- **Every positive word is a cycle of some `3x + k` map.** For a nonempty positive word `w`, put
`G = gcd(S, D)`, `k = D/G` and `a = S/G`. Then `a > 0` and `a`, `k` are odd, `D a = k S`, and `a`
is a cycle point of period `len w` of `syrK k` whose gap word is exactly `w`. -/
theorem every_word_is_a_cycle {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    0 < aOf w ∧ Odd (aOf w) ∧ Odd (kOf w) ∧ Dz w * aOf w = kOf w * Sz w ∧
      IsCycleK (kOf w) (aOf w) w.length ∧ gapWordK (kOf w) (aOf w) w.length = w := by
  have hg := gSD_pos hne
  have hS := Sz_eq_gSD_mul w
  have hDk := Dz_eq_gSD_mul w
  have hSodd := CycleLiterature.Sz_odd hw hne
  have hDodd : Odd (Dz w) := CycleLiterature.Dz_odd (sum_pos_of_pos hw hne)
  have haodd : Odd (aOf w) := by rw [hS] at hSodd; exact (Int.odd_mul.1 hSodd).2
  have hkodd : Odd (kOf w) := by rw [hDk] at hDodd; exact (Int.odd_mul.1 hDodd).2
  have hapos : 0 < aOf w := by
    have := CycleLiterature.Sz_pos hne
    rw [hS] at this; exact pos_of_mul_pos_right this hg.le
  have heq := cycle_equation_k w
  obtain ⟨h1, h2⟩ := gapWordK_of_eq hkodd w [] (aOf w) (by simpa using hw) (by simpa using heq)
  simp only [List.nil_append] at h2
  refine ⟨hapos, haodd, hkodd, heq, ⟨List.length_pos_of_ne_nil hne, haodd, ?_⟩, h1⟩
  exact mul_left_cancel₀ (CycleGcd.Dz_ne_zero hne) (h2.trans heq.symm)

/-- `k(w) > 0` exactly when `D(w) > 0`. -/
theorem kOf_pos_iff {w : Word} (hne : w ≠ []) : 0 < kOf w ↔ 0 < Dz w := by
  rw [Dz_eq_gSD_mul]
  exact ⟨fun h => mul_pos (gSD_pos hne) h, fun h => pos_of_mul_pos_right h (gSD_pos hne).le⟩

/-- **Every positive word with `D > 0` is a positive cycle of `3x + k` with `k > 0`.** -/
theorem every_word_is_a_cycle_of_Dz_pos {w : Word} (hw : w.Pos) (hne : w ≠ []) (hD : 0 < Dz w) :
    0 < kOf w ∧ 0 < aOf w ∧ Odd (aOf w) ∧ IsCycleK (kOf w) (aOf w) w.length ∧
      gapWordK (kOf w) (aOf w) w.length = w := by
  obtain ⟨ha, hodd, -, -, hc, hg⟩ := every_word_is_a_cycle hw hne
  exact ⟨(kOf_pos_iff hne).2 hD, ha, hodd, hc, hg⟩

/-- **`D ∣ S` iff `|k(w)| = 1`.** -/
theorem dvd_iff_natAbs_kOf {w : Word} (hne : w ≠ []) : Dz w ∣ Sz w ↔ (kOf w).natAbs = 1 := by
  have hD0 := CycleGcd.Dz_ne_zero hne
  have hg := gSD_pos hne
  constructor
  · intro h
    have hgD : gSD w = |Dz w| := by
      rw [gSD, Int.gcd_eq_natAbs_right h, Int.natCast_natAbs]
    have := Dz_eq_gSD_mul w
    rw [hgD] at this
    have h' : (Dz w).natAbs = (Dz w).natAbs * (kOf w).natAbs := by
      conv_lhs => rw [this]
      rw [Int.natAbs_mul, Int.natAbs_abs]
    have hpos : 0 < (Dz w).natAbs := Int.natAbs_pos.2 hD0
    exact Nat.mul_left_cancel hpos (h'.symm.trans (mul_one _).symm)
  · intro h
    have hD : (Dz w).natAbs = (gSD w).natAbs := by
      rw [Dz_eq_gSD_mul, Int.natAbs_mul, h, mul_one]
    rw [← Int.natAbs_dvd_natAbs, hD, Int.natAbs_dvd_natAbs, gSD]
    exact Int.gcd_dvd_left _ _

/-- **Corollary: `3x + 1` cycles are the words with `|k(w)| = 1`.** A nonempty positive word is the
gap word of a `3x + 1` cycle (of either sign) iff `|k(w)| = 1`. -/
theorem exists_cycle_iff_natAbs_kOf {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    (∃ a, IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ (kOf w).natAbs = 1 := by
  rw [CycleLiterature.exists_cycle_iff_dvd hw hne, dvd_iff_natAbs_kOf hne]

/-- **Corollary: positive `3x + 1` cycles are exactly the words with `k(w) = 1`.** A nonempty
positive word is the gap word of a positive `3x + 1` cycle iff `k(w) = 1`, i.e. iff `D > 0` and
`D ∣ S`. The cycle point is then `a(w) = S/D`. -/
theorem positive_cycle_iff_kOf_eq_one {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    (∃ a, 0 < a ∧ IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ kOf w = 1 := by
  constructor
  · rintro ⟨a, ha, hc, hgw⟩
    have hD := CycleLiterature.cycle_Dz_pos hc ha
    have hdvd := CycleLiterature.cycle_D_dvd_S hc
    rw [hgw] at hD hdvd
    have h1 := (dvd_iff_natAbs_kOf hne).1 hdvd
    have h2 := (kOf_pos_iff hne).2 hD
    omega
  · intro hk
    obtain ⟨hapos, -, -, -, hc, hgw⟩ := every_word_is_a_cycle hw hne
    rw [hk] at hc hgw
    exact ⟨aOf w, hapos, isCycleK_one_iff.1 hc, by rw [← gapWordK_one]; exact hgw⟩

/-- `k(w) = 1 ⟺ (D > 0 ∧ D ∣ S)`. -/
theorem kOf_eq_one_iff {w : Word} (hne : w ≠ []) : kOf w = 1 ↔ 0 < Dz w ∧ Dz w ∣ Sz w := by
  rw [dvd_iff_natAbs_kOf hne, ← kOf_pos_iff hne]
  omega

/-! ## The `3x - 1` duality -/

/-- `gapK (-k) (-a) = gapK k a`: negation does not change the `2`-adic valuation. -/
theorem gapK_neg (k a : ℤ) : gapK (-k) (-a) = gapK k a := by
  rw [gapK, gapK, show 3 * -a + -k = -(3 * a + k) by ring, padicValInt, padicValInt,
    Int.natAbs_neg]

/-- **Duality.** `syrK (-k) (-a) = -syrK k a`. -/
theorem syrK_neg (k a : ℤ) : syrK (-k) (-a) = -syrK k a := by
  have h : ((2 : ℕ) : ℤ) ^ padicValInt 2 (3 * a + k) ∣ 3 * a + k := padicValInt_dvd _
  push_cast at h
  rw [syrK_eq, syrK_eq, gapK_neg, show 3 * -a + -k = -(3 * a + k) by ring, gapK,
    Int.neg_ediv_of_dvd h]

/-- Iterating the duality: `(syrK (-k))^[n] (-a) = -((syrK k)^[n] a)`. -/
theorem iterate_syrK_neg (k a : ℤ) (n : ℕ) : (syrK (-k))^[n] (-a) = -((syrK k)^[n] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, syrK_neg, ih]

/-- The duality preserves gap words: `gapWordK (-k) (-a) = gapWordK k a`. -/
theorem gapWordK_neg (k a : ℤ) (o : ℕ) : gapWordK (-k) (-a) o = gapWordK k a o := by
  induction o generalizing a with
  | zero => rfl
  | succ o ih => rw [gapWordK, gapWordK, gapK_neg, syrK_neg, ih]

/-- The duality maps `syrK k`-cycles to `syrK (-k)`-cycles. -/
theorem isCycleK_neg_iff {k a : ℤ} {o : ℕ} : IsCycleK (-k) (-a) o ↔ IsCycleK k a o := by
  simp only [IsCycleK, iterate_syrK_neg, odd_neg, neg_inj]

/-- **The `3x - 1` duality.** `a ↦ -a` maps `3x + 1` cycles to `3x - 1` cycles with the same gap
word: `IsSyrCycle a o ↔ IsCycleK (-1) (-a) o`, and `gapWordK (-1) (-a) o = gapWord a o`. -/
theorem isSyrCycle_iff_isCycleK_neg_one {a : ℤ} {o : ℕ} :
    IsSyrCycle a o ↔ IsCycleK (-1) (-a) o := by
  rw [isCycleK_neg_iff, isCycleK_one_iff]

/-- The `3x - 1` dual has the same gap word. -/
theorem gapWordK_neg_one (a : ℤ) (o : ℕ) : gapWordK (-1) (-a) o = gapWord a o := by
  rw [gapWordK_neg, gapWordK_one]

/-! ## Witnesses from other maps -/

/-- **`5x + 1` cycle `1 → 3 → 1`**, word `(1, 4)`: `5·1 + 1 = 2·3`, `5·3 + 1 = 2^4·1`. It is a closed
orbit of the recurrence at `(X, Y) = (2, 5)`, with `D = 2^5 - 5^2 = 7 > 0` and `S = 7`. -/
theorem five_cycle_one :
    Follows (2 : ℤ) 5 [1, 4] 1 1 ∧ D (2 : ℤ) 5 [1, 4] = 7 ∧ S (2 : ℤ) 5 [1, 4] = 7 :=
  ⟨Follows.cons (a' := 3) (by norm_num) (Follows.cons (a' := 1) (by norm_num) (Follows.nil _)),
    by norm_num [D], by norm_num [S]⟩

/-- **`5x + 1` cycle `13 → 33 → 83 → 13`**, word `(1, 1, 5)`: `D = 2^7 - 5^3 = 3 > 0`,
`S = 39 = 3·13`. -/
theorem five_cycle_thirteen :
    Follows (2 : ℤ) 5 [1, 1, 5] 13 13 ∧ D (2 : ℤ) 5 [1, 1, 5] = 3 ∧ S (2 : ℤ) 5 [1, 1, 5] = 39 :=
  ⟨Follows.cons (a' := 33) (by norm_num) (Follows.cons (a' := 83) (by norm_num)
    (Follows.cons (a' := 13) (by norm_num) (Follows.nil _))), by norm_num [D], by norm_num [S]⟩

/-- **`5x + 1` cycle `17 → 43 → 27 → 17`**, word `(1, 3, 3)`: `5·17 + 1 = 2·43`,
`5·43 + 1 = 2^3·27`, `5·27 + 1 = 2^3·17`; `D = 2^7 - 5^3 = 3 > 0`, `S = 51 = 3·17`. -/
theorem five_cycle_seventeen :
    Follows (2 : ℤ) 5 [1, 3, 3] 17 17 ∧ D (2 : ℤ) 5 [1, 3, 3] = 3 ∧ S (2 : ℤ) 5 [1, 3, 3] = 51 :=
  ⟨Follows.cons (a' := 43) (by norm_num) (Follows.cons (a' := 27) (by norm_num)
    (Follows.cons (a' := 17) (by norm_num) (Follows.nil _))), by norm_num [D], by norm_num [S]⟩

/-- All points of the three `5x + 1` cycles are odd, so each gap is the exact `2`-adic valuation:
these are genuine cycles of the accelerated `5x + 1` map. -/
theorem five_cycles_odd : ∀ x ∈ ({1, 3, 13, 33, 83, 17, 43, 27} : Finset ℤ), Odd x := by
  decide

/-- **The `5x + 1` floor.** On each of the three `5x + 1` cycles `D(w) = 2^E - 5^o` divides every
rotation sum at `(2, 5)`: the generic floor `Follows.D_dvd_S_rotate` holds verbatim. -/
theorem five_cycles_floor (j : ℕ) :
    D (2 : ℤ) 5 [1, 4] ∣ S (2 : ℤ) 5 ([1, 4].rotate j) ∧
      D (2 : ℤ) 5 [1, 1, 5] ∣ S (2 : ℤ) 5 ([1, 1, 5].rotate j) ∧
      D (2 : ℤ) 5 [1, 3, 3] ∣ S (2 : ℤ) 5 ([1, 3, 3].rotate j) :=
  ⟨Follows.D_dvd_S_rotate _ _ five_cycle_one.1 j,
    Follows.D_dvd_S_rotate _ _ five_cycle_thirteen.1 j,
    Follows.D_dvd_S_rotate _ _ five_cycle_seventeen.1 j⟩

/-- **The `3x + 1` negative cycles have `D < 0`.** `-1` (word `(1)`, `D = -1`), `-5` (word `(1, 2)`,
`D = -1`) and `-17` (word `(1,1,1,2,1,1,4)`, `D = -139`). -/
theorem negative_cycles_D :
    (IsSyrCycle (-1) 1 ∧ gapWord (-1) 1 = [1] ∧ Dz [1] = -1) ∧
      (IsSyrCycle (-5) 2 ∧ gapWord (-5) 2 = [1, 2] ∧ Dz [1, 2] = -1) ∧
      (IsSyrCycle (-17) 7 ∧ gapWord (-17) 7 = [1, 1, 1, 2, 1, 1, 4] ∧
        Dz [1, 1, 1, 2, 1, 1, 4] = -139) :=
  ⟨⟨CycleLiterature.isSyrCycle_neg_one.1, CycleLiterature.isSyrCycle_neg_one.2, by decide⟩,
    ⟨CycleLiterature.isSyrCycle_neg_five.1, CycleLiterature.isSyrCycle_neg_five.2, by decide⟩,
    ⟨CycleLiterature.isSyrCycle_neg_seventeen.1, CycleLiterature.isSyrCycle_neg_seventeen.2,
      by decide⟩⟩

/-- **`3x - 1` cycles `1`, `5`, `17`** (the duals of the negative `3x + 1` cycles), with the same
gap words. -/
theorem three_x_minus_one_cycles :
    (IsCycleK (-1) 1 1 ∧ gapWordK (-1) 1 1 = [1]) ∧
      (IsCycleK (-1) 5 2 ∧ gapWordK (-1) 5 2 = [1, 2]) ∧
      (IsCycleK (-1) 17 7 ∧ gapWordK (-1) 17 7 = [1, 1, 1, 2, 1, 1, 4]) := by
  obtain ⟨⟨h1, w1, -⟩, ⟨h5, w5, -⟩, ⟨h17, w17, -⟩⟩ := negative_cycles_D
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa using isSyrCycle_iff_isCycleK_neg_one.1 h1
  · simpa [w1] using gapWordK_neg_one (-1) 1
  · simpa using isSyrCycle_iff_isCycleK_neg_one.1 h5
  · simpa [w5] using gapWordK_neg_one (-5) 2
  · simpa using isSyrCycle_iff_isCycleK_neg_one.1 h17
  · simpa [w17] using gapWordK_neg_one (-17) 7

/-- **The `-17` word under the "every word is a cycle" theorem**: `G = 139`, `k = -1`, `a = 17`. The
word is realised by the `3x - 1` cycle through `17`. -/
theorem neg17_word_data :
    gSD [1, 1, 1, 2, 1, 1, 4] = 139 ∧ kOf [1, 1, 1, 2, 1, 1, 4] = -1 ∧
      aOf [1, 1, 1, 2, 1, 1, 4] = 17 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The `5x + 1`-style data of `(1, 4)` at `(2, 3)`**: the word `(1, 4)` has `D = 23`, `S = 5`,
`G = 1`, so `k = 23`, `a = 5`: it is realised by the `3x + 23` cycle `5 → 19 → 5`. -/
theorem word14_data : kOf [1, 4] = 23 ∧ aOf [1, 4] = 5 ∧ IsCycleK 23 5 2 ∧ gapWordK 23 5 2 = [1, 4] := by
  have hk : kOf [1, 4] = 23 := by decide
  have ha : aOf [1, 4] = 5 := by decide
  obtain ⟨-, -, -, -, hc, hg⟩ := every_word_is_a_cycle (w := [1, 4]) (by simp [Word.Pos]) (by simp)
  rw [hk, ha] at hc hg
  exact ⟨hk, ha, hc, hg⟩

/-! ## Sign-blindness -/

/-- **The floor is sign-blind: the `-17` cycle.** Every nonzero `ℤ`-combination `C` of the rotation
sums of the `-17` cycle word `(1,1,1,2,1,1,4)` satisfies `139 ∣ sixFree C`, `139 ≤ sixFree C` and
`139 ≤ |C|`, exactly as `Program.floor` gives for a positive cycle (`|D| = 139`). -/
theorem floor_neg17 {C : ℤ} (hC : C ∈ Program.rotIdeal [1, 1, 1, 2, 1, 1, 4]) (hC0 : C ≠ 0) :
    139 ∣ sixFree C ∧ 139 ≤ sixFree C ∧ 139 ≤ |C| := by
  obtain ⟨h, hw⟩ := CycleLiterature.isSyrCycle_neg_seventeen
  have := Program.floor h (C := C) (by rw [hw]; exact hC) hC0
  rw [hw] at this
  norm_num at this
  exact this

/-- The `-17` cycle word is cyclically `β 1^3` with `β = (2, 1, 1, 4)`. -/
theorem neg17_isRotated : [1, 1, 1, 2, 1, 1, 4] ~r ([2, 1, 1, 4] ++ List.replicate 3 1) :=
  ⟨3, by decide⟩

/-- **The bounded-defect ceiling is attained by the `-17` cycle.** The lever core of
`β = (2, 1, 1, 4)` over the background `d = 1` is `S(β1) - S(1β) = 565 - 287 = 278 = 2·139`, so the
6-free ceiling is `139`, and `BoundedDefectLever.ceiling` gives `|D| = 139 ≤ 139`: the ceiling is
tight, and it cannot exclude this word, which carries a genuine (negative) cycle. -/
theorem ceiling_neg17 :
    Sz ([2, 1, 1, 4] ++ [1]) - Sz (1 :: [2, 1, 1, 4]) = 278 ∧
      sixFree (Sz ([2, 1, 1, 4] ++ [1]) - Sz (1 :: [2, 1, 1, 4])) = 139 ∧
      ((2 : ℤ) ^ (gapWord (-17) 7).sum - 3 ^ 7).natAbs = 139 ∧
      ((2 : ℤ) ^ (gapWord (-17) 7).sum - 3 ^ 7).natAbs ≤
        sixFree (Sz ([2, 1, 1, 4] ++ [1]) - Sz (1 :: [2, 1, 1, 4])) := by
  obtain ⟨h, hw⟩ := CycleLiterature.isSyrCycle_neg_seventeen
  have hcore : Sz ([2, 1, 1, 4] ++ [1]) - Sz (1 :: [2, 1, 1, 4]) = 278 := by norm_num [S]
  have hsix : sixFree (Sz ([2, 1, 1, 4] ++ [1]) - Sz (1 :: [2, 1, 1, 4])) = 139 := by
    rw [hcore, show (278 : ℤ) = 2 ^ 1 * 3 ^ 0 * 139 by norm_num, Program.sixFree_pow_mul,
      BoundedDefectLever.sixFree_eq_natAbs] <;> norm_num
  have hD : ((2 : ℤ) ^ (gapWord (-17) 7).sum - 3 ^ 7).natAbs = 139 := by rw [hw]; norm_num
  refine ⟨hcore, hsix, hD, ?_⟩
  exact BoundedDefectLever.ceiling h (β := [2, 1, 1, 4]) (d := 1) (L := 3) (by norm_num)
    (by rw [hw]; exact neg17_isRotated)
    (by rw [hcore]; norm_num)

/-- **q-invariance: the rotation recursion at `(2, 5)`.** The generic `ℤ[X,Y]` identity
`X^d S(w d) = Y S(d w) + D(d w)` holds at `(X, Y) = (2, 5)`. -/
theorem rotation_recursion_two_five (d : ℕ) (w : Word) :
    (2 : ℤ) ^ d * S 2 5 (w ++ [d]) = 5 * S 2 5 (d :: w) + D 2 5 (d :: w) :=
  rotation_recursion 2 5 d w

/-- **q-invariance: the concatenation cocycle at `(2, 5)`.** -/
theorem S_append_two_five (u v : Word) :
    S (2 : ℤ) 5 (u ++ v) = 5 ^ v.length * S 2 5 u + 2 ^ u.sum * S 2 5 v :=
  S_append 2 5 u v

/-- **q-invariance: the floor at `(2, 5)`.** On any closed orbit of the `5x + 1` recurrence,
`D = 2^E - 5^o` divides every `ℤ`-combination of rotation sums (`CocycleCombine.Follows.D_dvd_comb`
at `(2, 5)`). With `five_cycle_thirteen` this is a non-vacuous instance: `3` divides
`S^{(j)}(1,1,5) ∈ {39, 99, 249}`. -/
theorem floor_two_five {w : Word} {a : ℤ} (h : Follows (2 : ℤ) 5 w a a) (J : Finset ℕ)
    (c : ℕ → ℤ) : D (2 : ℤ) 5 w ∣ ∑ j ∈ J, c j * S 2 5 (w.rotate j) :=
  CocycleCombine.Follows.D_dvd_comb h J c

/-- The rotation sums of the `5x + 1` cycle `(1, 1, 5)` are `3·13, 3·33, 3·83`: `S^{(j)} = D a_j`. -/
theorem five_cycle_thirteen_rotations :
    S (2 : ℤ) 5 [1, 1, 5] = 3 * 13 ∧ S (2 : ℤ) 5 ([1, 1, 5].rotate 1) = 3 * 33 ∧
      S (2 : ℤ) 5 ([1, 1, 5].rotate 2) = 3 * 83 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## F2. Fixed-slope families are excluded by the ratio sandwich -/

/-- If `2E ≤ 3o` and `o ≥ 1` then `D = 2^E - 3^o < 0` (`2^{2E} ≤ 8^o < 9^o`). -/
theorem Dz_neg_of_two_mul_sum_le {w : Word} (hne : w ≠ []) (h : 2 * w.sum ≤ 3 * w.length) :
    Dz w < 0 := by
  have ho : w.length ≠ 0 := by simpa using hne
  have h1 : (2 : ℕ) ^ (2 * w.sum) ≤ 2 ^ (3 * w.length) := Nat.pow_le_pow_right (by norm_num) h
  have h2 : (2 : ℕ) ^ (3 * w.length) < 3 ^ (2 * w.length) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_lt_pow_left (by norm_num) ho
  have h3 : ((2 : ℕ) ^ w.sum) ^ 2 < (3 ^ w.length) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm w.sum, mul_comm w.length]; omega
  have h4 : (2 : ℕ) ^ w.sum < 3 ^ w.length := (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
  have h5 : ((2 ^ w.sum : ℕ) : ℤ) < ((3 ^ w.length : ℕ) : ℤ) := by exact_mod_cast h4
  push_cast at h5
  simp only [Dz, D]; linarith

/-- **A positive cycle has `3o < 2E`**, i.e. `E/o > 3/2` (from `3^o < 2^E`). -/
theorem three_mul_length_lt {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    3 * o < 2 * (gapWord a o).sum := by
  by_contra hle
  have hD := CycleLiterature.cycle_Dz_pos h ha
  have := Dz_neg_of_two_mul_sum_le (CycleLiterature.cycle_gapWord_ne_nil h)
    (by rw [gapWord_length]; omega)
  linarith

/-- Rotations preserve `E` and `o`. -/
lemma sum_length_of_isRotated {w W : Word} (hW : w ~r W) : W.sum = w.sum ∧ W.length = w.length :=
  ⟨hW.perm.sum_eq.symm, hW.perm.length_eq.symm⟩

/-- **F2(a), background `d = 1`.** If `w` is a rotation of `β 1^L` with `2·|β| ≤ L + 3·len β` (i.e.
`L ≥ 2|β| - 3 len β`) and `w ≠ []`, then `D(w) < 0`. -/
theorem Dz_neg_one_background {w β : Word} {L : ℕ} (hW : w ~r (β ++ List.replicate L 1))
    (hne : w ≠ []) (hL : 2 * β.sum ≤ L + 3 * β.length) : Dz w < 0 := by
  obtain ⟨hs, hl⟩ := sum_length_of_isRotated hW
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.length_append,
    List.length_replicate] at hs hl
  exact Dz_neg_of_two_mul_sum_le hne (by omega)

/-- **F2(a), exclusion form.** No positive cycle has a cyclic gap word `β 1^L` with
`2·|β| ≤ L + 3·len β`; equivalently every positive cycle of this shape has `L + 3·len β < 2·|β|`. -/
theorem one_background_bound {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) {β : Word} {L : ℕ}
    (hW : gapWord a o ~r (β ++ List.replicate L 1)) : L + 3 * β.length < 2 * β.sum := by
  have h1 := three_mul_length_lt h ha
  obtain ⟨hs, hl⟩ := sum_length_of_isRotated hW
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.length_append,
    List.length_replicate, gapWord_length] at hs hl
  omega

/-- The block `β` of a cyclic gap word `β d^L` of a cycle is positive and `d ≥ 1` when `L ≥ 1`. -/
lemma blocks_pos {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β : Word} {d L : ℕ}
    (hW : gapWord a o ~r (β ++ List.replicate L d)) :
    β.Pos ∧ (1 ≤ L → 1 ≤ d) := by
  have hpos : ∀ x ∈ β ++ List.replicate L d, 1 ≤ x := fun x hx =>
    gapWord_pos h.2.1 o x (hW.perm.mem_iff.2 hx)
  refine ⟨fun x hx => hpos x (List.mem_append_left _ hx), fun hL => hpos d ?_⟩
  exact List.mem_append_right _ (List.mem_replicate.2 ⟨by omega, rfl⟩)

/-- **F2(b), background `d ≥ 3`.** If a positive cycle has cyclic gap word `β d^L` with `d ≥ 3`, then
`(d - 2) L + |β| ≤ 2 len β` (from `E ≤ 2o`), hence `L ≤ len β`. -/
theorem steep_background_bound {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {β : Word} {d L : ℕ}
    (hd : 3 ≤ d) (hW : gapWord a o ~r (β ++ List.replicate L d)) :
    (d - 2) * L + β.sum ≤ 2 * β.length ∧ L ≤ β.length := by
  have h1 := CycleLiterature.cycle_sum_le h
  obtain ⟨hs, hl⟩ := sum_length_of_isRotated hW
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, List.length_append,
    List.length_replicate, gapWord_length] at hs hl
  have hβ := CycleLiterature.length_le_sum (blocks_pos h hW).1
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  have : (e + 3 - 2) * L = e * L + L := by rw [show e + 3 - 2 = e + 1 by omega]; ring
  have h2 : L * (e + 3) = e * L + 3 * L := by ring
  rw [this]
  rw [h2] at hs
  constructor <;> nlinarith

/-- The elements of a nontrivial positive cycle are `≥ 3`. -/
lemma three_le_of_nontrivial {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1)
    (k : ℕ) : 3 ≤ syr^[k] a := by
  have hpos := CycleLiterature.syr_iterate_pos ha k
  obtain ⟨m, hm⟩ := CycleLiterature.syr_iterate_odd h.2.1 k
  have hne : syr^[k] a ≠ 1 := fun he => h1 (CycleLiterature.cycle_eq_one_of_iterate_eq_one h he)
  omega

/-- **A nontrivial positive cycle has `2^E 3^o ≤ 10^o`** (right edge of the sandwich with minimum
`≥ 3`: `2^E ≤ (3 + 1/3)^o`). -/
theorem two_pow_mul_three_pow_le {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1) :
    2 ^ (gapWord a o).sum * 3 ^ o ≤ 10 ^ o := by
  have hle := CycleLiterature.cycle_two_pow_le h (m := 3) (by norm_num)
    (fun k _ => by exact_mod_cast three_le_of_nontrivial h ha h1 k)
  have e : ((3 : ℝ) + 1 / 3) ^ o * 3 ^ o = 10 ^ o := by rw [← mul_pow]; norm_num
  have : (2 : ℝ) ^ (gapWord a o).sum * 3 ^ o ≤ 10 ^ o := by
    rw [← e]; exact mul_le_mul_of_nonneg_right hle (by positivity)
  exact_mod_cast this

/-- From `6^n 12^L ≤ 10^n 10^L` follows `L ≤ 3n` (`6·12^3 = 10368 > 10^4`). -/
lemma le_three_mul_of_pow_le {n L : ℕ} (h : 6 ^ n * 12 ^ L ≤ 10 ^ n * 10 ^ L) : L ≤ 3 * n := by
  by_contra hlt
  obtain ⟨t, rfl⟩ : ∃ t, L = 3 * n + 1 + t := ⟨L - (3 * n + 1), by omega⟩
  have e1 : 6 ^ n * 12 ^ (3 * n + 1 + t) = 10368 ^ n * (12 * 12 ^ t) := by
    rw [show (10368 : ℕ) = 6 * 12 ^ 3 by norm_num, mul_pow, ← pow_mul]; ring
  have e2 : 10 ^ n * 10 ^ (3 * n + 1 + t) = 10000 ^ n * (10 * 10 ^ t) := by
    rw [show (10000 : ℕ) = 10 * 10 ^ 3 by norm_num, mul_pow, ← pow_mul]; ring
  rw [e1, e2] at h
  have h3 : 10000 ^ n ≤ 10368 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h4 : 10 ^ t ≤ 12 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have h5 : 10 * 10 ^ t < 12 * 12 ^ t := by have := Nat.one_le_pow t 10 (by norm_num); nlinarith
  have h6 : 0 < 10000 ^ n := by positivity
  exact absurd h (not_le.2 (lt_of_lt_of_le (mul_lt_mul_of_pos_left h5 h6)
    (Nat.mul_le_mul_right _ h3)))

/-- **F2(b), background `d = 2`.** If a nontrivial positive cycle has cyclic gap word `β 2^L`, then
`L ≤ 3·len β`. (Nontriviality is necessary: the trivial cycle `1 → 1` has word `2^L` for every
`L`.) -/
theorem two_background_bound {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1)
    {β : Word} {L : ℕ} (hW : gapWord a o ~r (β ++ List.replicate L 2)) : L ≤ 3 * β.length := by
  have hE := two_pow_mul_three_pow_le h ha h1
  obtain ⟨hs, hl⟩ := sum_length_of_isRotated hW
  simp only [List.sum_append, List.sum_replicate, smul_eq_mul, List.length_append,
    List.length_replicate, gapWord_length] at hs hl
  have hβ := CycleLiterature.length_le_sum (blocks_pos h hW).1
  rw [← hs, ← hl] at hE
  apply le_three_mul_of_pow_le
  calc 6 ^ β.length * 12 ^ L = (2 ^ β.length * 4 ^ L) * (3 ^ β.length * 3 ^ L) := by
        rw [show (6 : ℕ) = 2 * 3 by rfl, show (12 : ℕ) = 4 * 3 by rfl, mul_pow, mul_pow]; ring
    _ ≤ (2 ^ β.sum * 4 ^ L) * (3 ^ β.length * 3 ^ L) := by
        gcongr
    _ = 2 ^ (β.sum + L * 2) * 3 ^ (β.length + L) := by
        rw [pow_add, pow_add, mul_comm L 2, pow_mul]; norm_num
    _ ≤ 10 ^ (β.length + L) := hE
    _ = 10 ^ β.length * 10 ^ L := pow_add _ _ _

/-- The trivial cycle shows that nontriviality is needed for `d = 2`: `gapWord 1 L = 2^L`. -/
theorem trivial_two_background (L : ℕ) (hL : 0 < L) :
    IsSyrCycle 1 L ∧ gapWord 1 L ~r ([] ++ List.replicate L 2) :=
  ⟨CycleGcd.isSyrCycle_one_iter hL, by rw [CycleGcd.gapWord_one]; exact List.IsRotated.refl _⟩

/-- **F2, unified.** If a nontrivial positive cycle has cyclic gap word `β d^L` (any background `d`),
then `L ≤ 2|β| + 3·len β`: the length of a fixed-slope run is bounded by the defect block. -/
theorem background_bound {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1)
    {β : Word} {d L : ℕ} (hW : gapWord a o ~r (β ++ List.replicate L d)) :
    L ≤ 2 * β.sum + 3 * β.length := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · rcases Nat.eq_zero_or_pos L with hL | hL
      · omega
      · exact absurd ((blocks_pos h hW).2 hL) (by norm_num)
    · have := one_background_bound h ha hW; omega
    · have := two_background_bound h ha h1 hW; omega
  · have := (steep_background_bound h hd hW).2; omega

/-! ## Ellison ⇒ a lower bound that composes with a ceiling -/

/-- `2^E ≤ (2^E e^{-E/10})^2`, since `e^{E/5} ≤ 2^E`. -/
lemma two_pow_le_sq (E : ℕ) : (2 : ℝ) ^ E ≤ ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 := by
  have hl := Real.log_two_gt_d9
  have h1 : Real.exp ((E : ℝ) / 5) ≤ 2 ^ E := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos]
    exact Real.exp_le_exp.2 (by have : (0 : ℝ) ≤ E := by positivity
                                nlinarith)
  have h2 : ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 =
      2 ^ E * (2 ^ E * Real.exp (-((E : ℝ) / 5))) := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  rw [h2]
  have h3 : 1 ≤ 2 ^ E * Real.exp (-((E : ℝ) / 5)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, one_le_div (Real.exp_pos _)]; exact h1
  have h4 : (0 : ℝ) < 2 ^ E := by positivity
  nlinarith

/-- **Ellison ⇒ no cycle in a family with 6-free ceiling `c` once `E` is large.** Assume
`CycleLiterature.Ellison1971`. If every word of a family `F` has a nonzero rotation-ideal
representative with 6-free part `≤ c`, then no genuine cycle (of either sign) with gap word in `F`
has `E ∉ {1,…,11,13,14,16,19,27}` and `c² ≤ 2^E`. -/
theorem no_cycle_of_ellison (hEl : CycleLiterature.Ellison1971) (F : Word → Prop) (c : ℕ)
    (hF : ∀ w, F w → ∃ C ∈ Program.rotIdeal w, C ≠ 0 ∧ sixFree C ≤ c) {a : ℤ} {o : ℕ}
    (hx : (gapWord a o).sum ∉ CycleLiterature.ellisonExceptions)
    (hc : (c : ℝ) ^ 2 ≤ 2 ^ (gapWord a o).sum) : ¬ (IsSyrCycle a o ∧ F (gapWord a o)) := by
  rintro ⟨h, hFw⟩
  obtain ⟨C, hC, hC0, hcC⟩ := hF _ hFw
  have hfl := (Program.floor h hC hC0).2.1
  have hE1 := Program.one_le_sum_gapWord h
  have hEll := hEl (gapWord a o).sum o (by omega) h.1 hx
  have hcast : (((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs : ℝ) =
      |(2 : ℝ) ^ (gapWord a o).sum - 3 ^ o| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  have hDc : |(2 : ℝ) ^ (gapWord a o).sum - 3 ^ o| ≤ c := by
    rw [← hcast]; exact_mod_cast hfl.trans hcC
  have hsq := two_pow_le_sq (gapWord a o).sum
  set X := (2 : ℝ) ^ (gapWord a o).sum * Real.exp (-((gapWord a o).sum : ℝ) / 10)
  have hX : 0 ≤ X := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

/-- **Ellison, explicit threshold.** Under `Ellison1971`, a family with 6-free ceiling `c` has no
genuine cycle with `E ≥ 28` and `c² ≤ 2^E`, i.e. once `E > max(27, 2 log₂ c)`. -/
theorem no_cycle_of_ellison_ge (hEl : CycleLiterature.Ellison1971) (F : Word → Prop) (c : ℕ)
    (hF : ∀ w, F w → ∃ C ∈ Program.rotIdeal w, C ≠ 0 ∧ sixFree C ≤ c) {a : ℤ} {o : ℕ}
    (hE : 28 ≤ (gapWord a o).sum) (hc : c ^ 2 ≤ 2 ^ (gapWord a o).sum) :
    ¬ (IsSyrCycle a o ∧ F (gapWord a o)) := by
  refine no_cycle_of_ellison hEl F c hF ?_ (by exact_mod_cast hc)
  intro hmem
  simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

end Syracuse.Limits
