import Mathlib

/-!
# Computable list polynomials with verified division and extended Euclid

A polynomial is a dense coefficient list (`[a₀, a₁, …]` ↦ `a₀ + a₁ X + …`). Every operation is
computable by structural recursion, so the kernel can evaluate it with `decide`. Its meaning is fixed
by `toPoly : List R → R[X]`, and each operation is proved to commute with `toPoly`. Over a field,
`ldivmod` is proved to be division with remainder (`ldivmod_spec`, `ldivmod_rem_lt`), and `xgcd` an
extended Euclid returning a Bézout combination that divides both inputs (`xgcd_spec`).
-/

namespace Syracuse.R1

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- Sum of list polynomials. -/
def ladd : List R → List R → List R
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: ladd p q

/-- Scalar multiple. -/
def lsmul (c : R) : List R → List R
  | [] => []
  | a :: p => (c * a) :: lsmul c p

/-- Negation. -/
def lneg : List R → List R
  | [] => []
  | a :: p => (-a) :: lneg p

/-- Difference. -/
def lsub (p q : List R) : List R := ladd p (lneg q)

/-- Product. -/
def lmul : List R → List R → List R
  | [], _ => []
  | a :: p, q => ladd (lsmul a q) (0 :: lmul p q)

/-- The monomial `c X^k`. -/
def lmono (k : ℕ) (c : R) : List R := List.replicate k 0 ++ [c]

/-- The polynomial a coefficient list denotes. -/
noncomputable def toPoly : List R → R[X]
  | [] => 0
  | a :: p => C a + X * toPoly p

@[simp] lemma toPoly_nil : toPoly ([] : List R) = 0 := rfl

@[simp] lemma toPoly_cons (a : R) (p : List R) : toPoly (a :: p) = C a + X * toPoly p := rfl

@[simp] lemma toPoly_ladd : ∀ p q : List R, toPoly (ladd p q) = toPoly p + toPoly q
  | [], q => by simp [ladd]
  | a :: p, [] => by simp [ladd]
  | a :: p, b :: q => by simp only [ladd, toPoly_cons, toPoly_ladd p q, C_add]; ring

@[simp] lemma toPoly_lsmul (c : R) : ∀ p : List R, toPoly (lsmul c p) = C c * toPoly p
  | [] => by simp [lsmul]
  | a :: p => by simp only [lsmul, toPoly_cons, toPoly_lsmul c p, C_mul]; ring

@[simp] lemma toPoly_lneg : ∀ p : List R, toPoly (lneg p) = -toPoly p
  | [] => by simp [lneg]
  | a :: p => by simp only [lneg, toPoly_cons, toPoly_lneg p, C_neg]; ring

@[simp] lemma toPoly_lsub (p q : List R) : toPoly (lsub p q) = toPoly p - toPoly q := by
  simp [lsub, sub_eq_add_neg]

@[simp] lemma toPoly_lmul : ∀ p q : List R, toPoly (lmul p q) = toPoly p * toPoly q
  | [], q => by simp [lmul]
  | a :: p, q => by simp only [lmul, toPoly_ladd, toPoly_lsmul, toPoly_cons, toPoly_lmul p q, C_0]; ring

@[simp] lemma toPoly_lmono (k : ℕ) (c : R) : toPoly (lmono k c) = C c * X ^ k := by
  induction k with
  | zero => simp [lmono]
  | succ k ih => simp only [lmono, List.replicate_succ, List.cons_append] at ih ⊢
                 rw [toPoly_cons, ih, C_0]; ring

/-- Coefficients of `toPoly p` are the list entries. -/
lemma coeff_toPoly : ∀ (p : List R) (i : ℕ), (toPoly p).coeff i = p.getD i 0
  | [], i => by simp
  | a :: p, 0 => by simp
  | a :: p, i + 1 => by simp [coeff_toPoly p i]

lemma toPoly_map {S : Type*} [CommRing S] (f : R →+* S) :
    ∀ p : List R, toPoly (p.map f) = (toPoly p).map f
  | [] => by simp
  | a :: p => by simp [toPoly_map f p]

end CommRing

section Trim

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Remove trailing zeros. -/
def trim : List R → List R
  | [] => []
  | a :: p =>
    match trim p with
    | [] => if a = 0 then [] else [a]
    | b :: t => a :: b :: t

@[simp] lemma toPoly_trim : ∀ p : List R, toPoly (trim p) = toPoly p
  | [] => rfl
  | a :: p => by
    have ih := toPoly_trim p
    unfold trim
    split
    · rename_i h
      rw [h] at ih
      split_ifs with ha
      · simp [ha, ← ih]
      · simp [← ih]
    · rename_i b t h
      rw [h] at ih
      simp [← ih]

/-- A list is normal when it is empty or its last entry is nonzero. -/
def Normal (p : List R) : Prop := ∀ h : p ≠ [], p.getLast h ≠ 0

lemma trim_normal : ∀ p : List R, Normal (trim p)
  | [] => fun h => absurd rfl h
  | a :: p => by
    have ih := trim_normal p
    unfold trim
    split
    · split_ifs with ha
      · exact fun h => absurd rfl h
      · intro _; simpa using ha
    · rename_i b t h
      rw [h] at ih
      intro _
      have := ih (by simp)
      simpa [List.getLast_cons] using this

omit [DecidableEq R] in
lemma getD_length_sub_one (p : List R) (hp : p ≠ []) :
    p.getD (p.length - 1) 0 = p.getLast hp := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

omit [DecidableEq R] in
/-- For a normal nonempty list: nonzero, degree `length - 1`, leading coefficient the last entry. -/
lemma normal_props {p : List R} (hn : Normal p) (hp : p ≠ []) :
    toPoly p ≠ 0 ∧ (toPoly p).natDegree = p.length - 1 ∧
      (toPoly p).leadingCoeff = p.getLast hp := by
  have hc : (toPoly p).coeff (p.length - 1) ≠ 0 := by
    rw [coeff_toPoly, getD_length_sub_one p hp]; exact hn hp
  have hle : (toPoly p).natDegree ≤ p.length - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_toPoly, List.getD_eq_default]; omega
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hle hc
  refine ⟨fun h0 => hc (by simp [h0]), hdeg, ?_⟩
  rw [leadingCoeff, hdeg, coeff_toPoly, getD_length_sub_one p hp]

/-- The length of the trimmed list is `0` for the zero polynomial and `natDegree + 1` otherwise. -/
lemma trim_length (p : List R) :
    (trim p).length = if toPoly p = 0 then 0 else (toPoly p).natDegree + 1 := by
  by_cases ht : trim p = []
  · have : toPoly p = 0 := by rw [← toPoly_trim, ht]; rfl
    simp [ht, this]
  · obtain ⟨h0, hd, -⟩ := normal_props (trim_normal p) ht
    rw [toPoly_trim] at h0 hd
    simp only [h0, ↓reduceIte, hd]
    have := List.length_pos_of_ne_nil ht
    omega

lemma trim_eq_nil_iff (p : List R) : trim p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [← toPoly_trim, h]; rfl
  · intro h
    have := trim_length p
    simp only [h, ↓reduceIte] at this
    exact List.length_eq_zero_iff.mp this

lemma trim_trim (p : List R) : (trim (trim p)).length = (trim p).length := by
  rw [trim_length (trim p), toPoly_trim, trim_length p]

end Trim

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Long division by `g` (assumed normal and nonempty), with fuel. -/
def ldivmod (g : List K) : ℕ → List K → List K × List K
  | 0, f => ([], f)
  | n + 1, f =>
    let f₀ := trim f
    if f₀.length < g.length then ([], f₀) else
      let k := f₀.length - g.length
      let c := f₀.getLastD 0 / g.getLastD 1
      let r := ldivmod g n (lsub f₀ (lmul (lmono k c) g))
      (ladd r.1 (lmono k c), r.2)

/-- `f = q g + r`, for any fuel. -/
theorem ldivmod_spec (g : List K) :
    ∀ (n : ℕ) (f : List K),
      toPoly f = toPoly (ldivmod g n f).1 * toPoly g + toPoly (ldivmod g n f).2
  | 0, f => by simp [ldivmod]
  | n + 1, f => by
    simp only [ldivmod]
    split_ifs
    · simp
    · have ih := ldivmod_spec g n (lsub (trim f) (lmul (lmono ((trim f).length - g.length)
        ((trim f).getLastD 0 / g.getLastD 1)) g))
      simp only [toPoly_lsub, toPoly_lmul, toPoly_lmono, toPoly_trim] at ih
      simp only [toPoly_ladd, toPoly_lmono]
      linear_combination ih

omit [Field K] [DecidableEq K] in
lemma getLastD_eq {p : List K} (hp : p ≠ []) (d : K) : p.getLastD d = p.getLast hp := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hp]; rfl

/-- One division step strictly lowers the trimmed length. -/
lemma step_lt {g f₀ : List K} (hg : Normal g) (hg0 : g ≠ []) (hf : Normal f₀)
    (hlen : g.length ≤ f₀.length) :
    (trim (lsub f₀ (lmul (lmono (f₀.length - g.length) (f₀.getLastD 0 / g.getLastD 1)) g))).length
      < f₀.length := by
  have hf0 : f₀ ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen
    exact hg0 (List.length_eq_zero_iff.mp (by omega))
  obtain ⟨hP0, hPd, hPl⟩ := normal_props hf hf0
  obtain ⟨hG0, hGd, hGl⟩ := normal_props hg hg0
  set c := f₀.getLastD 0 / g.getLastD 1 with hc
  have hc0 : c ≠ 0 := by
    rw [hc, getLastD_eq hf0, getLastD_eq hg0]
    exact div_ne_zero (hf hf0) (hg hg0)
  set k := f₀.length - g.length
  have hQ : toPoly (lmul (lmono k c) g) = C c * X ^ k * toPoly g := by simp
  have hQ0 : C c * X ^ k * toPoly g ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hG0
  have hQd : (C c * X ^ k * toPoly g).natDegree = f₀.length - 1 := by
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hG0,
      natDegree_C_mul_X_pow _ _ hc0, hGd]
    have := List.length_pos_of_ne_nil hg0; omega
  have hQl : (C c * X ^ k * toPoly g).leadingCoeff = f₀.getLast hf0 := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, hGl, hc,
      getLastD_eq hf0, getLastD_eq hg0]
    field_simp [hg hg0]
  have hdeg : (toPoly f₀).degree = (C c * X ^ k * toPoly g).degree := by
    rw [degree_eq_natDegree hP0, degree_eq_natDegree hQ0, hPd, hQd]
  have hlt := degree_sub_lt_left hdeg hP0 (by rw [hPl, hQl])
  rw [trim_length, toPoly_lsub, hQ]
  split_ifs with h0
  · exact List.length_pos_of_ne_nil hf0
  · have := natDegree_lt_natDegree h0 hlt
    omega

/-- With enough fuel the remainder is shorter than the divisor. -/
theorem ldivmod_rem_lt {g : List K} (hg : Normal g) (hg0 : g ≠ []) :
    ∀ (n : ℕ) (f : List K), (trim f).length < n → (trim (ldivmod g n f).2).length < g.length
  | 0, f, h => absurd h (Nat.not_lt_zero _)
  | n + 1, f, h => by
    simp only [ldivmod]
    split_ifs with hl
    · simpa [trim_trim] using hl
    · apply ldivmod_rem_lt hg hg0 n
      have := step_lt hg hg0 (trim_normal f) (not_lt.mp hl)
      omega

/-- With enough fuel, an exact divisor leaves remainder `0`. -/
theorem ldivmod_exact {g f : List K} (hg : Normal g) (hg0 : g ≠ []) (n : ℕ)
    (hn : (trim f).length < n) (hd : toPoly g ∣ toPoly f) :
    toPoly f = toPoly (ldivmod g n f).1 * toPoly g := by
  have hspec := ldivmod_spec g n f
  have hr : toPoly (ldivmod g n f).2 = 0 := by
    by_contra hr0
    have hlt := ldivmod_rem_lt hg hg0 n f hn
    simp only [trim_length, hr0, ↓reduceIte] at hlt
    obtain ⟨-, hGd, -⟩ := normal_props hg hg0
    have hdr : toPoly g ∣ toPoly (ldivmod g n f).2 := by
      have : toPoly (ldivmod g n f).2 = toPoly f - toPoly (ldivmod g n f).1 * toPoly g := by
        rw [hspec]; ring
      rw [this]; exact dvd_sub hd (dvd_mul_left _ _)
    exact hr0 (eq_zero_of_dvd_of_natDegree_lt hdr (by omega))
  rw [hspec, hr, add_zero]

/-- Exact quotient `f / g` (correct when `g ∣ f`). -/
def ldiv (f g : List K) : List K := (ldivmod (trim g) ((trim f).length + 1) f).1

theorem ldiv_spec {f g : List K} (hg : toPoly g ≠ 0) (hd : toPoly g ∣ toPoly f) :
    toPoly f = toPoly (ldiv f g) * toPoly g := by
  have hg0 : trim g ≠ [] := fun h => hg ((trim_eq_nil_iff g).mp h)
  have := ldivmod_exact (trim_normal g) hg0 ((trim f).length + 1) (Nat.lt_succ_self _)
    (by rwa [toPoly_trim])
  rwa [toPoly_trim] at this

/-! ## Extended Euclid -/

/-- Triples `(r, s, t)` with `r = s F + t G`; one Euclid step per unit of fuel. -/
def xgcd : ℕ → List K × List K × List K → List K × List K × List K → List K × List K × List K
  | 0, A, _ => A
  | n + 1, A, B =>
    if trim B.1 = [] then A else
      let qr := ldivmod (trim B.1) ((trim A.1).length + 1) A.1
      xgcd n B (qr.2, lsub A.2.1 (lmul qr.1 B.2.1), lsub A.2.2 (lmul qr.1 B.2.2))

/-- The Bézout invariant. -/
def Inv (F G : K[X]) (T : List K × List K × List K) : Prop :=
  toPoly T.1 = toPoly T.2.1 * F + toPoly T.2.2 * G

theorem xgcd_spec (F G : K[X]) :
    ∀ (n : ℕ) (A B : List K × List K × List K), Inv F G A → Inv F G B →
      (∀ d : K[X], (d ∣ toPoly A.1 ∧ d ∣ toPoly B.1) ↔ (d ∣ F ∧ d ∣ G)) →
      (trim B.1).length < n →
      Inv F G (xgcd n A B) ∧ toPoly (xgcd n A B).1 ∣ F ∧ toPoly (xgcd n A B).1 ∣ G
  | 0, A, B, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, A, B, hA, hB, hCD, hn => by
    simp only [xgcd]
    split_ifs with h0
    · have hB0 : toPoly B.1 = 0 := (trim_eq_nil_iff _).mp h0
      refine ⟨hA, ?_⟩
      exact (hCD (toPoly A.1)).mp ⟨dvd_refl _, by rw [hB0]; exact dvd_zero _⟩
    · set qr := ldivmod (trim B.1) ((trim A.1).length + 1) A.1
      have hspec := ldivmod_spec (trim B.1) ((trim A.1).length + 1) A.1
      rw [toPoly_trim] at hspec
      have hlt : (trim qr.2).length < (trim B.1).length :=
        ldivmod_rem_lt (trim_normal B.1) h0 ((trim A.1).length + 1) A.1 (Nat.lt_succ_self _)
      apply xgcd_spec F G n B _ hB
      · unfold Inv at hA hB ⊢
        simp only [toPoly_lsub, toPoly_lmul]
        have : toPoly qr.2 = toPoly A.1 - toPoly qr.1 * toPoly B.1 := by
          rw [hspec]; ring
        rw [this, hA, hB]; ring
      · intro d
        rw [← hCD d]
        have hr : toPoly qr.2 = toPoly A.1 - toPoly qr.1 * toPoly B.1 := by rw [hspec]; ring
        simp only [hr]
        constructor
        · rintro ⟨hb, hr'⟩
          refine ⟨?_, hb⟩
          have : toPoly A.1 = (toPoly A.1 - toPoly qr.1 * toPoly B.1) + toPoly qr.1 * toPoly B.1 :=
            by ring
          rw [this]; exact dvd_add hr' (dvd_mul_of_dvd_right hb _)
        · rintro ⟨ha, hb⟩
          exact ⟨hb, dvd_sub ha (dvd_mul_of_dvd_right hb _)⟩
      · simp only
        omega

/-- **Extended Euclid.** `(h, u, v)` with `h = u F + v G`, `h ∣ F`, `h ∣ G`. -/
def egcd (f g : List K) : List K × List K × List K :=
  xgcd ((trim g).length + 1) (f, [1], []) (g, [], [1])

theorem egcd_spec (f g : List K) :
    toPoly (egcd f g).1 = toPoly (egcd f g).2.1 * toPoly f + toPoly (egcd f g).2.2 * toPoly g ∧
      toPoly (egcd f g).1 ∣ toPoly f ∧ toPoly (egcd f g).1 ∣ toPoly g := by
  have := xgcd_spec (toPoly f) (toPoly g) ((trim g).length + 1) (f, [1], []) (g, [], [1])
    (by simp [Inv]) (by simp [Inv]) (fun d => Iff.rfl) (Nat.lt_succ_self _)
  exact this

end Field

end Syracuse.R1
