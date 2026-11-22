import Syracuse.Basic

/-!
# The punctured-torus approach: affine generators, Property P, Markoff and Lorentzian data

Formalises the algebraic core of `approaches/punctured-torus` (`RATIONALE`, `STATUS`, `SYNTHESIS`,
`markoff-coordinates`, `lorentzian`, `brunswic-spacetime`, `spacetime-description`, `degeneration`,
`nontrivial-representation`, `properness`). The two Syracuse branches
`a : z ↦ (3z+1)/2`, `b : z ↦ z/2` are the homogeneous matrices `A = !![3,1;0,2]`, `B = !![1,0;0,2]`
(generic: `!![Y,1;0,X]`, `!![1,0;0,X]`). Letter words act on the left, first letter first, so the
matrix of a gap word is the **transpose** of `Basic`'s lower-triangular transfer matrix:
`lmat (gapLetters w) = (Mw w)ᵀ = !![3^o, S; 0, 2^E]` (`lmat_gapLetters`).

## Coverage table

| note claim (file) | Lean name | status |
|---|---|---|
| `A`, `B` realise `a`, `b` (SYNTHESIS §1) | `matA`, `matB`, `mob_matA`, `mob_matB` | proved |
| gap `d` acts as `b^{d-1}∘a`, `x ↦ (3x+1)/2^d` | `iterate_b_comp_a`, `mob_gap`, `matB_pow_mul_matA` | proved |
| word matrix = transfer matrix, transpose convention (SYNTHESIS §1) | `lmat_gapLetters(_eq)`, `lmat_append` | proved |
| period map `z ↦ (3^o/2^E) z + S/2^E` (STATUS; spacetime-description §1) | `periodMap_eq`, `mob_Mw_transpose`, `follows_iff_periodMap` | proved |
| `tr = 2^E+3^o`, `det = 2^E 3^o`, eigenvalue gap `= D` (SYNTHESIS §1; markoff §5) | `trace_Mw_transpose`, `det_Mw_transpose`, `charpoly_Mw_transpose`, `disc_Mw_transpose`, `cycle_table` | proved |
| fixed points `S/D` and `∞` | `periodMap_eq_self_iff`, `Mw_transpose_mulVec_fixed`, `Mw_transpose_mulVec_inf` | proved |
| "attracting fixed point `x₀ = S/D`" (`markoff.py` docstring) | `periodMap_iterate_sub_fixed`, `fixed_point_repelling_neg_one` | corrected (attracting iff `D > 0`; repelling for `-1`, `-5`) |
| Property P: cycle `⟺ D ∣ S ⟺ S/D ∈ ℤ` (spacetime-description §4; SYNTHESIS §4) | `follows_self_iff`, `isSyrCycle_iff`, `exists_isSyrCycle_iff_dvd`, `dvd_iff_fixedPoint_int`, `propertyP`, `IsSyrCycle.eq_fixedPoint` | proved for positive nonempty gap words; corrected (false for the class `b`, `o = 0`: `b_fixed_point`) |
| examples: cycles `ab, a, aab → 1, -1, -5`; non-cycles `abb, (1,3) → 1/5, 5/7` | `fixedPoint_ab` … `fixedPoint_13`, `cycle_one`, `cycle_neg_one`, `cycle_neg_five`, `not_cycle_abb`, `not_cycle_13`, `gapLetters_examples` | proved |
| a cycle is the vertical geodesic `Re = S/D` of `ℍ = Aff₊(ℝ)`, translation length `ℓ` (STATUS) | `isometry_periodH`, `periodH_axis` | proved (any nonempty word) |
| `ℓ = |log(2^E/3^o)| = |E log 2 - o log 3| = log(1 + D/3^o)` for `D > 0` | `transLength_eq`, `log_ratio_eq`, `transLength_eq_log_one_add` | proved |
| per-cycle `ℓ = log 4/3, log 3/2, log 8/9` (markoff §5) | `transLength_examples` | corrected (`ℓ(aab) = log(9/8)`; `log(8/9) < 0`) |
| trace coordinates `(5/√6, 3/√2, 7/(2√3))` (markoff §1) | `slA`, `slB`, `trace_coords` | proved |
| Fricke `tr[A,B] = x²+y²+z²-xyz-2` | `fricke_hom`, `fricke` | proved (all of `SL₂` over a commutative ring) |
| `tr[A,B] = +2`, level set `= 4` (markoff §1–2) | `trace_commutator`, `fricke_level` | proved |
| reducible: shared fixed point `∞` (markoff §2) | `shared_fixed_point`, `trace_commutator_of_upper` | proved (direction "common fixed point ⇒ tr = 2"; the converse not formalized) |
| `[A,B] = !![1,1/4;0,1]`, non-trivial parabolic (markoff §3) | `commutator_eq`, `commutator_parabolic` | proved |
| all traces `< 3` (sub-Markoff), `> 2` (hyperbolic) (markoff §4) | `traces_bounds` | proved |
| discriminant `-191/12`: `tr[A,B] = -2` unreachable at fixed `(x,y)` (markoff §4) | `sub_markoff_disc`, `trace_commutator_ge`, `trace_commutator_ne_neg_two` | proved (sharpened: `tr[P,Q] ≥ 95/48`) |
| Markoff minimum `3` ⇒ the generators cannot uniformise a cusped torus (markoff §4) | — | not formalized (Markoff/McShane theory not in Mathlib) |
| Stage-2 scaffolding `deform(t)`, elliptic collapse (markoff §6) | — | empirical/not formalized (numerical; the margin `tr² - 4 det = D² = 1` is `disc_Mw_transpose`) |
| Minkowski model `q = -det = ½ tr X²`, frame, `Ad ⊂ O(q)` (lorentzian; spacetime §0) | `qf`, `bil`, `qf_eq_bil`, `frame`, `qf_Ad` | proved |
| `Ad` of a cycle has eigenvalues `{2^E/3^o, 1, 3^o/2^E}`, neutral axis spacelike (lorentzian (A)) | `Ad_Gw_spectrum` | proved (explicit eigenvectors `E`, `x⁰`, `V`) |
| "`D` = Lorentzian interval in null coordinates, criticality = light cone" (lorentzian (A)) | `Ad_Gw_spectrum` | corrected (precise form: `q(x⁰) = D²/4`, `x⁰` null iff `D = 0`) |
| `Ad L(a) = (H, 3/2 E, 2/3 F)`, `Ad L(b) = (H, ½E, 2F)`, `τ(a) = ½E`, `τ(b) = 0` (spacetime §1) | `generators_lorentzian` | proved |
| `τ(γ) = (S/2^E) E`, null, a cocycle, realising the period map on `ℝE` (spacetime §1; lorentzian (B)) | `tau_Gw`, `skel_tau_mul`, `affAct_mul`, `affAct_null_line`, `isBorel_lmat` | proved |
| `τ` is a crossed homomorphism "for whichever linear part `L`" (spacetime §1) | `tau_cocycle_forces_borel` | corrected (false: the cocycle law forces `L(a)` to fix `∞`) |
| Margulis invariant `≡ 0` (lorentzian (B); spacetime §4) | `margulis_eq_zero`, `margulis_lmat` | proved |
| holonomy fixes the spacelike line `{tH + (S/D)E}` (spacetime §4) | `affAct_fixed_iff` | proved |
| puncture: `Ad[A,B]` unipotent fixing `ℝE` (brunswic-spacetime) | `Ad_commutator` | proved (the identification with an extreme BTZ line is not formalized) |
| Brunswic Thm 1 identification, `T Teich(Σ₁,₁)`, GH Cauchy-compact spacetime, future-completeness, white hole, `ℝ`-tree singularity, Fuchsian lift (brunswic-spacetime; spacetime §2–3, §5) | — | not formalized (requires Lorentzian geometry not in Mathlib) |
| Magnus class unique in `H¹(F₂, ℝ_λ)`; `S`-arithmetic building (SYNTHESIS §2–3) | — | not formalized (twisted group cohomology, Bruhat–Tits trees) |
| degeneration (Spearman `0.89`), proper cocycle (margin `1.61`), Schottky rep (`tr[A,B] = 827`) | — | empirical/not formalized (numerical searches) |
-/

namespace Syracuse.PuncturedTorus

open Matrix

section Generators

variable {R : Type*} [CommRing R] (X Y : R)

/-- Homogeneous matrix of `a : z ↦ (Y z + 1)/X` (at `(X,Y) = (2,3)`: `!![3,1;0,2]`). -/
def matA : Matrix (Fin 2) (Fin 2) R := !![Y, 1; 0, X]

/-- Homogeneous matrix of `b : z ↦ z/X` (at `(X,Y) = (2,3)`: `!![1,0;0,2]`). -/
def matB : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, X]

/-- The two letters of the free monoid on `{a, b}`. -/
inductive Letter
  | a
  | b
  deriving DecidableEq

/-- The homogeneous matrix of a letter. -/
def Letter.mat : Letter → Matrix (Fin 2) (Fin 2) R
  | .a => matA X Y
  | .b => matB X

/-- The matrix of a letter word read left to right (first letter applied first):
`lmat (c :: u) = lmat u * c.mat`. -/
def lmat : List Letter → Matrix (Fin 2) (Fin 2) R
  | [] => 1
  | c :: u => lmat u * c.mat X Y

/-- `lmat` is an anti-homomorphism of the free monoid (words act on the left). -/
theorem lmat_append (u v : List Letter) : lmat X Y (u ++ v) = lmat X Y v * lmat X Y u := by
  induction u with
  | nil => simp [lmat]
  | cons c u ih => simp [lmat, ih, Matrix.mul_assoc]

/-- `B^n = !![1, 0; 0, X^n]`. -/
theorem matB_pow (n : ℕ) : matB X ^ n = !![1, 0; 0, X ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih => rw [pow_succ, ih, matB]; simp [pow_succ]

/-- The letter word `bⁿ` has matrix `Bⁿ`. -/
theorem lmat_replicate_b (n : ℕ) : lmat X Y (List.replicate n .b) = matB X ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, lmat, ih, Letter.mat, ← pow_succ]

/-- **A gap `d ≥ 1` acts as `b^{d-1} ∘ a`**, and its matrix is the transpose of the transfer
matrix `M d = !![Y,0;1,X^d]` of `Basic`. -/
theorem matB_pow_mul_matA {d : ℕ} (hd : 1 ≤ d) :
    matB X ^ (d - 1) * matA X Y = (M X Y d)ᵀ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, matB_pow, matA, M]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ]

/-- The letter word of a gap word: the gap `d` becomes `a b^{d-1}`. -/
def gapLetters : Word → List Letter
  | [] => []
  | d :: w => (Letter.a :: List.replicate (d - 1) .b) ++ gapLetters w

/-- **Letter words vs transfer matrices.** For a positive gap word the letter-word matrix is
the transpose of `Basic`'s transfer matrix: `lmat (gapLetters w) = (Mw w)ᵀ = !![Y^o, S; 0, X^E]`. -/
theorem lmat_gapLetters {w : Word} (hw : Word.Pos w) : lmat X Y (gapLetters w) = (Mw X Y w)ᵀ := by
  induction w with
  | nil => simp [gapLetters, lmat, Mw]
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have hw' : Word.Pos w := fun e he => hw e (by simp [he])
    rw [gapLetters, lmat_append, ih hw', lmat, lmat_replicate_b, Letter.mat,
      matB_pow_mul_matA X Y hd, ← Matrix.transpose_mul]
    simp [Mw]

/-- The letter-word matrix of a positive gap word, entrywise: `!![Y^o, S(w); 0, X^E]`. -/
theorem lmat_gapLetters_eq {w : Word} (hw : Word.Pos w) :
    lmat X Y (gapLetters w) = !![Y ^ w.length, S X Y w; 0, X ^ w.sum] := by
  rw [lmat_gapLetters X Y hw, Mw_eq]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Trace of the word matrix: `tr = X^E + Y^o` (`2^E + 3^o` at `(2,3)`). -/
theorem trace_Mw_transpose (w : Word) : ((Mw X Y w)ᵀ).trace = X ^ w.sum + Y ^ w.length := by
  rw [Matrix.trace_transpose, Mw_eq, Matrix.trace_fin_two]; simp [add_comm]

/-- Determinant of the word matrix: `det = X^E Y^o` (`2^E 3^o` at `(2,3)`). -/
theorem det_Mw_transpose (w : Word) : ((Mw X Y w)ᵀ).det = X ^ w.sum * Y ^ w.length := by
  rw [Matrix.det_transpose, Mw_eq, Matrix.det_fin_two]; simp [mul_comm]

/-- **Eigenvalue gap = `D`.** The characteristic polynomial factors as `(t - Y^o)(t - X^E)`: the
eigenvalues are `Y^o` and `X^E`, whose difference is `D = X^E - Y^o`. -/
theorem charpoly_Mw_transpose [Nontrivial R] (w : Word) :
    ((Mw X Y w)ᵀ).charpoly =
      (Polynomial.X - Polynomial.C (Y ^ w.length)) * (Polynomial.X - Polynomial.C (X ^ w.sum)) := by
  rw [Matrix.charpoly_fin_two, trace_Mw_transpose, det_Mw_transpose]
  simp only [map_add, map_mul]
  ring

/-- The discriminant of the word matrix is `D²`: `tr² - 4 det = (X^E - Y^o)²`, so the two
eigenvalues differ by `|D|`. -/
theorem disc_Mw_transpose (w : Word) :
    ((Mw X Y w)ᵀ).trace ^ 2 - 4 * ((Mw X Y w)ᵀ).det = D X Y w ^ 2 := by
  rw [trace_Mw_transpose, det_Mw_transpose, D]; ring

/-- `(1,0)` (the point `∞`) is an eigenvector of eigenvalue `Y^o`. -/
theorem Mw_transpose_mulVec_inf (w : Word) :
    (Mw X Y w)ᵀ *ᵥ ![1, 0] = Y ^ w.length • ![1, 0] := by
  rw [Mw_eq]; ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `(S, D)` (the point `S/D`) is an eigenvector of eigenvalue `X^E`. -/
theorem Mw_transpose_mulVec_fixed (w : Word) :
    (Mw X Y w)ᵀ *ᵥ ![S X Y w, D X Y w] = X ^ w.sum • ![S X Y w, D X Y w] := by
  rw [Mw_eq]; ext i; fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D]; ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D]

end Generators

section Field

variable {K : Type*} [Field K] (X Y : K)

/-- The Möbius action `z ↦ (g₀₀ z + g₀₁)/(g₁₀ z + g₁₁)` of a `2 × 2` matrix. -/
def mob (G : Matrix (Fin 2) (Fin 2) K) (z : K) : K := (G 0 0 * z + G 0 1) / (G 1 0 * z + G 1 1)

/-- `A` acts as `a : z ↦ (Y z + 1)/X`. -/
theorem mob_matA (z : K) : mob (matA X Y) z = (Y * z + 1) / X := by simp [mob, matA]

/-- `B` acts as `b : z ↦ z/X`. -/
theorem mob_matB (z : K) : mob (matB X) z = z / X := by simp [mob, matB]

/-- The accelerated Syracuse step with gap `d`: `z ↦ (Y z + 1)/X^d`. -/
def stepMap (d : ℕ) (z : K) : K := (Y * z + 1) / X ^ d

/-- **A gap `d ≥ 1` is `b^{d-1} ∘ a`** as maps of the line: `(z/X)^{∘(d-1)} ∘ (Yz+1)/X`. -/
theorem iterate_b_comp_a {d : ℕ} (hd : 1 ≤ d) (z : K) :
    (fun x => x / X)^[d - 1] ((Y * z + 1) / X) = stepMap X Y d z := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, stepMap]
  clear hd
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, div_div, ← pow_succ]

/-- The matrix `b^{d-1} a` acts by the gap-`d` step. -/
theorem mob_gap {d : ℕ} (hd : 1 ≤ d) (z : K) :
    mob (matB X ^ (d - 1) * matA X Y) z = stepMap X Y d z := by
  rw [matB_pow_mul_matA X Y hd]; simp [mob, M, stepMap]

/-- The period map of a gap word: compose the gap steps, first gap first. -/
def periodMap : Word → K → K
  | [], z => z
  | d :: w, z => periodMap w (stepMap X Y d z)

variable {X}

/-- **The period map is affine:** `F_w(z) = (Y^o z + S(w)) / X^E`, i.e. at `(2,3)`
`z ↦ (3^o/2^E) z + S/2^E`. -/
theorem periodMap_eq (hX : X ≠ 0) (w : Word) (z : K) :
    periodMap X Y w z = (Y ^ w.length * z + S X Y w) / X ^ w.sum := by
  induction w generalizing z with
  | nil => simp [periodMap]
  | cons d w ih =>
    rw [periodMap, ih, stepMap]
    simp only [List.length_cons, List.sum_cons, S_cons, pow_succ, pow_add]
    field_simp
    ring

/-- The word matrix `(Mw w)ᵀ` acts by the period map. -/
theorem mob_Mw_transpose (hX : X ≠ 0) (w : Word) (z : K) :
    mob (Mw X Y w)ᵀ z = periodMap X Y w z := by
  rw [periodMap_eq Y hX, Mw_eq]; simp [mob]

/-- **Orbits are period-map values.** Over a field with `X ≠ 0`, `Follows X Y w a b` holds iff
`b = F_w(a)`. -/
theorem follows_iff_periodMap (hX : X ≠ 0) (w : Word) (a b : K) :
    Follows X Y w a b ↔ b = periodMap X Y w a := by
  induction w generalizing a with
  | nil =>
    constructor
    · rintro ⟨⟩; rfl
    · intro h; subst h; exact Follows.nil _
  | cons d w ih =>
    have hXd : X ^ d ≠ 0 := pow_ne_zero _ hX
    constructor
    · rintro (_ | ⟨hstep, hrest⟩)
      rw [periodMap, (ih _).1 hrest, stepMap, ← hstep, mul_div_cancel_left₀ _ hXd]
    · intro h
      refine Follows.cons (a' := stepMap X Y d a) ?_ ((ih _).2 h)
      rw [stepMap, mul_div_cancel₀ _ hXd]

/-- Over a field every start has an orbit along every word. -/
theorem exists_follows (hX : X ≠ 0) (w : Word) (a : K) : ∃ b, Follows X Y w a b :=
  ⟨_, (follows_iff_periodMap Y hX w a _).2 rfl⟩

/-- **The fixed point is `S/D`.** If `D(w) ≠ 0`, the period map fixes exactly `S(w)/D(w)`. -/
theorem periodMap_eq_self_iff (hX : X ≠ 0) {w : Word} (hD : D X Y w ≠ 0) (z : K) :
    periodMap X Y w z = z ↔ z = S X Y w / D X Y w := by
  rw [periodMap_eq Y hX, div_eq_iff (pow_ne_zero _ hX), eq_div_iff hD, D]
  constructor <;> intro h <;> linear_combination -h

/-- Contraction towards the fixed point: `F_w(z) - S/D = (Y^o/X^E)(z - S/D)`. So `S/D` is
attracting on the line iff `|Y^o/X^E| < 1` (at `(2,3)`: iff `D > 0`); it is repelling for the
negative cycles `-1`, `-5`. -/
theorem periodMap_sub_fixed (hX : X ≠ 0) {w : Word} (hD : D X Y w ≠ 0) (z : K) :
    periodMap X Y w z - S X Y w / D X Y w =
      Y ^ w.length / X ^ w.sum * (z - S X Y w / D X Y w) := by
  rw [periodMap_eq Y hX]
  have hD' : X ^ w.sum - Y ^ w.length ≠ 0 := hD
  simp only [D]
  field_simp
  ring

/-- Iterating the period map: `F_w^k(z) - S/D = (Y^o/X^E)^k (z - S/D)`. -/
theorem periodMap_iterate_sub_fixed (hX : X ≠ 0) {w : Word} (hD : D X Y w ≠ 0) (k : ℕ) (z : K) :
    (periodMap X Y w)^[k] z - S X Y w / D X Y w =
      (Y ^ w.length / X ^ w.sum) ^ k * (z - S X Y w / D X Y w) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, periodMap_sub_fixed Y hX hD, pow_succ]; ring

end Field


section PropertyP

/-- `S` commutes with ring homomorphisms. -/
theorem S_map {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R') (X Y : R)
    (w : Word) : f (S X Y w) = S (f X) (f Y) w := by
  induction w with
  | nil => simp
  | cons d w ih => simp [ih]

/-- `D` commutes with ring homomorphisms. -/
theorem D_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (X Y : R) (w : Word) :
    f (D X Y w) = D (f X) (f Y) w := by
  simp [D]

/-- The integer `S(w)` cast into any commutative ring is `S` at `(2,3)` there. -/
theorem Sz_cast {K : Type*} [CommRing K] (w : Word) : ((Sz w : ℤ) : K) = S (2 : K) 3 w := by
  simpa using S_map (Int.castRingHom K) 2 3 w

/-- The integer `D(w)` cast into any commutative ring is `D` at `(2,3)` there. -/
theorem Dz_cast {K : Type*} [CommRing K] (w : Word) : ((Dz w : ℤ) : K) = D (2 : K) 3 w := by
  simpa using D_map (Int.castRingHom K) 2 3 w

/-- `D` only depends on `(E, o)`. -/
theorem D_congr {R : Type*} [CommRing R] (X Y : R) {u v : Word} (hs : u.sum = v.sum)
    (hl : u.length = v.length) : D X Y u = D X Y v := by
  simp [D, hs, hl]

/-- A nonempty word has `D(w) = 2^E - 3^o ≠ 0` (parity, or `3^o > 1` when `E = 0`). -/
theorem Dz_ne_zero {w : Word} (hw : w ≠ []) : Dz w ≠ 0 := by
  have ho : 0 < w.length := List.length_pos_iff.2 hw
  simp only [Dz, D]
  rcases Nat.eq_zero_or_pos w.sum with hE | hE
  · rw [hE, pow_zero]
    have : (1 : ℤ) < 3 ^ w.length := one_lt_pow₀ (by norm_num) ho.ne'
    omega
  · intro h
    have h1 : Even ((2 : ℤ) ^ w.sum) := (even_two).pow_of_ne_zero hE.ne'
    have h2 : Odd ((3 : ℤ) ^ w.length) := Odd.pow (by decide)
    rw [sub_eq_zero.1 h] at h1
    exact (Int.not_even_iff_odd.2 h2) h1

/-- `2^d` is coprime to `D(w)` as soon as `d ≤ E`: either `d = 0`, or `E ≥ 1` and `D` is odd. -/
theorem isCoprime_two_pow_Dz {d : ℕ} {w : Word} (hd : d ≤ w.sum) :
    IsCoprime ((2 : ℤ) ^ d) (Dz w) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simpa using isCoprime_one_left
  · apply IsCoprime.pow_left
    have h1 : Even ((2 : ℤ) ^ w.sum) := (even_two).pow_of_ne_zero (by omega)
    have h2 : Odd ((3 : ℤ) ^ w.length) := Odd.pow (by decide)
    obtain ⟨k, hk⟩ : Odd (Dz w) := by simp only [Dz, D]; exact h1.sub_odd h2
    exact ⟨-k, 1, by rw [hk]; ring⟩

/-- **Integrality of closed rational orbits.** If a rational orbit along `u` from an integer `x`
can be closed up (by some `v`) and `D(u v) ≠ 0`, then the orbit along `u` is integral. The
intermediate value after a gap `d` has denominator dividing both `2^d` and `D`, which are
coprime. -/
theorem follows_int_of_rat (u : Word) :
    ∀ (v : Word) (x : ℤ) (c : ℚ), Follows (2 : ℚ) 3 u (x : ℚ) c → Follows (2 : ℚ) 3 v c (x : ℚ) →
      Dz (u ++ v) ≠ 0 → ∃ c' : ℤ, (c' : ℚ) = c ∧ Follows (2 : ℤ) 3 u x c' := by
  induction u with
  | nil =>
    intro v x c hu _ _
    cases hu
    exact ⟨x, rfl, Follows.nil x⟩
  | cons d u ih =>
    intro v x c hu hv hD
    obtain _ | ⟨hstep, hrest⟩ := hu
    rename_i x₁
    -- the rotated closed orbit through `x₁`
    have hcl : Follows (2 : ℚ) 3 (u ++ (v ++ [d])) x₁ x₁ :=
      hrest.append (hv.append (Follows.cons hstep (Follows.nil x₁)))
    have hrot : Dz (u ++ (v ++ [d])) = Dz (d :: u ++ v) :=
      D_congr _ _ (by simp; ring) (by simp; ring)
    have hcyc := hcl.cycle_equation
    rw [← Dz_cast, hrot] at hcyc
    -- `x₁` is an integer
    have hcop : IsCoprime ((2 : ℤ) ^ d) (Dz (d :: u ++ v)) :=
      isCoprime_two_pow_Dz (by simp)
    obtain ⟨p, q, hpq⟩ := hcop
    set x₁' : ℤ := p * (3 * x + 1) + q * Sz (u ++ (v ++ [d])) with hx₁'
    have hx : (x₁' : ℚ) = x₁ := by
      have hS : ((Sz (u ++ (v ++ [d])) : ℤ) : ℚ) = S (2 : ℚ) 3 (u ++ (v ++ [d])) := Sz_cast _
      have hpq' : (p : ℚ) * 2 ^ d + q * (Dz (d :: u ++ v) : ℚ) = 1 := by exact_mod_cast hpq
      push_cast [hx₁', hS]
      rw [← hstep, ← hcyc]
      linear_combination x₁ * hpq'
    have hstepZ : (2 : ℤ) ^ d * x₁' = 3 * x + 1 := by
      have : ((2 : ℤ) ^ d * x₁' : ℤ) = ((3 * x + 1 : ℤ) : ℚ) := by push_cast; rw [hx, hstep]
      exact_mod_cast this
    obtain ⟨c', hc', hf⟩ := ih (v ++ [d]) x₁' c (by rw [hx]; exact hrest)
      (by rw [hx]; exact hv.append (Follows.cons hstep (Follows.nil x₁)))
      (by rw [hrot]; exact hD)
    exact ⟨c', hc', Follows.cons hstepZ hf⟩

/-- **Closed integer orbits = the cycle equation.** For `D(w) ≠ 0`, the integer `a` has a closed
orbit along `w` in `ℤ` iff `D(w) a = S(w)`. -/
theorem follows_self_iff {w : Word} (hD : Dz w ≠ 0) (a : ℤ) :
    Follows (2 : ℤ) 3 w a a ↔ Dz w * a = Sz w := by
  refine ⟨fun h => h.cycle_equation, fun h => ?_⟩
  have hX : (2 : ℚ) ≠ 0 := two_ne_zero
  obtain ⟨b, hb⟩ := exists_follows (3 : ℚ) hX w (a : ℚ)
  have hcf := hb.closed_form
  have hDq : D (2 : ℚ) 3 w * a = S (2 : ℚ) 3 w := by
    rw [← Dz_cast, ← Sz_cast]; exact_mod_cast h
  have hba : b = a := by
    apply mul_left_cancel₀ (pow_ne_zero w.sum hX)
    rw [hcf]; simp only [D] at hDq; linear_combination -hDq
  subst hba
  obtain ⟨c', hc', hf⟩ := follows_int_of_rat w [] a a hb (Follows.nil _) (by simpa using hD)
  have : c' = a := by exact_mod_cast hc'
  rwa [this] at hf

/-- If `2^d a' = 3a + 1` with `a'` odd, then the Syracuse gap of `a` is `d` and `syr a = a'`. -/
theorem gap_syr_of_step {a a' : ℤ} {d : ℕ} (h : 2 ^ d * a' = 3 * a + 1) (ha' : Odd a') :
    gap a = d ∧ syr a = a' := by
  have ha'0 : a' ≠ 0 := by rintro rfl; exact (Int.not_even_iff_odd.2 ha') ⟨0, by simp⟩
  have hgap : gap a = d := by
    rw [gap, ← h, padicValInt.mul (pow_ne_zero _ two_ne_zero) ha'0]
    have h1 : padicValInt 2 ((2 : ℤ) ^ d) = d := by
      rw [show (2 : ℤ) ^ d = ((2 ^ d : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
        padicValNat.prime_pow]
    have h2 : padicValInt 2 a' = 0 := padicValInt.eq_zero_of_not_dvd (by
      rintro ⟨m, hm⟩
      obtain ⟨k, hk⟩ := ha'
      push_cast at hm
      omega)
    rw [h1, h2, add_zero]
  refine ⟨hgap, ?_⟩
  have := two_pow_gap_mul_syr a
  rw [hgap, ← h] at this
  exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) this

/-- The start of an integer step with gap `d ≥ 1` is odd. -/
theorem odd_of_step {a a' : ℤ} {d : ℕ} (hd : 1 ≤ d) (h : 2 ^ d * a' = 3 * a + 1) : Odd a := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [pow_succ] at h
  exact ⟨2 ^ n * a' - a - 1, by linear_combination -h⟩

/-- **Integer orbits along positive words are genuine Syracuse orbits.** If `w` is positive and
`Follows 2 3 w a b` holds in `ℤ` with `b` odd, then `a` is odd, `w` is the gap word of `a`, and
the Syracuse map carries `a` to `b` in `len w` steps. -/
theorem syr_of_follows_pos {w : Word} {a b : ℤ} (h : Follows (2 : ℤ) 3 w a b) (hw : Word.Pos w)
    (hb : Odd b) : Odd a ∧ gapWord a w.length = w ∧ syr^[w.length] a = b := by
  induction h with
  | nil a => exact ⟨hb, rfl, rfl⟩
  | @cons d w a a' b hstep _ ih =>
    have hd : 1 ≤ d := hw d (by simp)
    obtain ⟨ha', hgw, hit⟩ := ih (fun e he => hw e (by simp [he])) hb
    obtain ⟨hgap, hsyr⟩ := gap_syr_of_step hstep ha'
    refine ⟨odd_of_step hd hstep, ?_, ?_⟩
    · simp [gapWord, hgap, hsyr, hgw]
    · rw [List.length_cons, Function.iterate_succ_apply, hsyr, hit]

/-- **Property P, integer form.** For a positive nonempty gap word `w` and `a : ℤ`, `a` is a
Syracuse cycle whose gap word is `w` iff `D(w) a = S(w)`. -/
theorem isSyrCycle_iff {w : Word} (hw : Word.Pos w) (hne : w ≠ []) (a : ℤ) :
    (IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w * a = Sz w := by
  constructor
  · rintro ⟨hc, hg⟩
    have := hc.cycle_equation
    rwa [hg] at this
  · intro h
    have hf := (follows_self_iff (Dz_ne_zero hne) a).2 h
    have ha : Odd a := by
      obtain ⟨d, w', rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain _ | ⟨hstep, _⟩ := hf
      exact odd_of_step (hw d (by simp)) hstep
    obtain ⟨-, hg, hit⟩ := syr_of_follows_pos hf hw ha
    exact ⟨⟨List.length_pos_iff.2 hne, ha, hit⟩, hg⟩

/-- **Property P, divisibility form.** A positive nonempty gap word is the gap word of a Syracuse
cycle iff `D(w) ∣ S(w)`. -/
theorem exists_isSyrCycle_iff_dvd {w : Word} (hw : Word.Pos w) (hne : w ≠ []) :
    (∃ a, IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w ∣ Sz w := by
  constructor
  · rintro ⟨a, h⟩; exact ⟨a, ((isSyrCycle_iff hw hne a).1 h).symm⟩
  · rintro ⟨c, hc⟩; exact ⟨c, (isSyrCycle_iff hw hne c).2 hc.symm⟩

/-- The fixed point `x₀* = S(w)/D(w) ∈ ℚ` of the period map of `w` (the cycle value). -/
def fixedPoint (w : Word) : ℚ := Sz w / Dz w

/-- `x₀* = S/D` is the unique fixed point of the rational period map `z ↦ (3^o z + S)/2^E`. -/
theorem periodMap_eq_self_iff_fixedPoint {w : Word} (hne : w ≠ []) (z : ℚ) :
    periodMap (2 : ℚ) 3 w z = z ↔ z = fixedPoint w := by
  rw [periodMap_eq_self_iff (3 : ℚ) two_ne_zero (by rw [← Dz_cast]; exact_mod_cast Dz_ne_zero hne),
    fixedPoint, Sz_cast, Dz_cast]

/-- `D ∣ S` iff the fixed point `S/D` is an integer. -/
theorem dvd_iff_fixedPoint_int {w : Word} (hD : Dz w ≠ 0) :
    Dz w ∣ Sz w ↔ ∃ n : ℤ, (n : ℚ) = fixedPoint w := by
  have hDq : (Dz w : ℚ) ≠ 0 := by exact_mod_cast hD
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [fixedPoint, hc]; push_cast; field_simp⟩
  · rintro ⟨n, hn⟩
    rw [fixedPoint, eq_div_iff hDq] at hn
    exact ⟨n, by exact_mod_cast (by linear_combination -hn : (Sz w : ℚ) = Dz w * n)⟩

/-- **Property P** (`spacetime-description.md` §4, `SYNTHESIS.md` §4): for a positive nonempty
gap word `w`, `w` is the gap word of a Syracuse cycle `⟺ D(w) ∣ S(w) ⟺` the fixed point
`x₀* = S/D` of its period map is an integer. -/
theorem propertyP {w : Word} (hw : Word.Pos w) (hne : w ≠ []) :
    ((∃ a, IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w ∣ Sz w) ∧
      (Dz w ∣ Sz w ↔ ∃ n : ℤ, (n : ℚ) = fixedPoint w) :=
  ⟨exists_isSyrCycle_iff_dvd hw hne, dvd_iff_fixedPoint_int (Dz_ne_zero hne)⟩

/-- The value of a Syracuse cycle is the fixed point of its gap word: `a = S/D`. -/
theorem IsSyrCycle.eq_fixedPoint {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    (a : ℚ) = fixedPoint (gapWord a o) := by
  have hne : gapWord a o ≠ [] := by
    intro he; have := congrArg List.length he; simp at this; exact h.1.ne' this
  have hDq : (Dz (gapWord a o) : ℚ) ≠ 0 := by exact_mod_cast Dz_ne_zero hne
  rw [fixedPoint, eq_div_iff hDq, mul_comm]
  exact_mod_cast h.cycle_equation

/-! ### The verified examples (`spacetime-description.md` §4, `markoff-coordinates.md` §5)

The notes' letter words and gap words: `ab ↔ (2)`, `a ↔ (1)`, `aab ↔ (1,2)` (cycles through
`1`, `-1`, `-5`); `abb ↔ (3)` and the gap word `(1,3) ↔ aabb` (non-cycles, `S/D = 1/5, 5/7`). -/

/-- `x₀*(ab) = 1`. -/
theorem fixedPoint_ab : fixedPoint [2] = 1 := by norm_num [fixedPoint, Sz, Dz, S, D]
/-- `x₀*(a) = -1`. -/
theorem fixedPoint_a : fixedPoint [1] = -1 := by norm_num [fixedPoint, Sz, Dz, S, D]
/-- `x₀*(aab) = -5`. -/
theorem fixedPoint_aab : fixedPoint [1, 2] = -5 := by norm_num [fixedPoint, Sz, Dz, S, D]
/-- `x₀*(abb) = 1/5`. -/
theorem fixedPoint_abb : fixedPoint [3] = 1 / 5 := by norm_num [fixedPoint, Sz, Dz, S, D]
/-- `x₀*(1,3) = 5/7`. -/
theorem fixedPoint_13 : fixedPoint [1, 3] = 5 / 7 := by norm_num [fixedPoint, Sz, Dz, S, D]

/-- The letter words of the examples. -/
theorem gapLetters_examples :
    gapLetters [2] = [.a, .b] ∧ gapLetters [1] = [.a] ∧ gapLetters [1, 2] = [.a, .a, .b] ∧
      gapLetters [3] = [.a, .b, .b] ∧ gapLetters [1, 3] = [.a, .a, .b, .b] := by
  simp [gapLetters]

/-- `1 → 1` is a Syracuse cycle with gap word `(2)`. -/
theorem cycle_one : IsSyrCycle 1 1 ∧ gapWord 1 1 = [2] :=
  (isSyrCycle_iff (w := [2]) (by intro d hd; simp at hd; omega) (by simp) 1).2
    (by norm_num [Sz, Dz, S, D])

/-- `-1 → -1` is a Syracuse cycle with gap word `(1)`. -/
theorem cycle_neg_one : IsSyrCycle (-1) 1 ∧ gapWord (-1) 1 = [1] :=
  (isSyrCycle_iff (w := [1]) (by intro d hd; simp at hd; omega) (by simp) (-1)).2
    (by norm_num [Sz, Dz, S, D])

/-- `-5 → -7 → -5` is a Syracuse cycle with gap word `(1, 2)`. -/
theorem cycle_neg_five : IsSyrCycle (-5) 2 ∧ gapWord (-5) 2 = [1, 2] :=
  (isSyrCycle_iff (w := [1, 2]) (by intro d hd; simp at hd; omega) (by simp) (-5)).2
    (by norm_num [Sz, Dz, S, D])

/-- `(3)` (`abb`) is not the gap word of any Syracuse cycle: `S/D = 1/5`. -/
theorem not_cycle_abb : ¬ ∃ a, IsSyrCycle a 1 ∧ gapWord a 1 = [3] := by
  show ¬ ∃ a, IsSyrCycle a [3].length ∧ gapWord a [3].length = [3]
  rw [exists_isSyrCycle_iff_dvd (w := [3]) (by intro d hd; simp at hd; omega) (by simp)]
  norm_num [Sz, Dz, S, D]

/-- `(1, 3)` is not the gap word of any Syracuse cycle: `S/D = 5/7`. -/
theorem not_cycle_13 : ¬ ∃ a, IsSyrCycle a 2 ∧ gapWord a 2 = [1, 3] := by
  show ¬ ∃ a, IsSyrCycle a [1, 3].length ∧ gapWord a [1, 3].length = [1, 3]
  rw [exists_isSyrCycle_iff_dvd (w := [1, 3]) (by intro d hd; simp at hd; omega) (by simp)]
  norm_num [Sz, Dz, S, D]

/-- **The per-cycle table** (`markoff-coordinates.md` §5): `(tr, det, D)` of the integral word
matrix is `(7, 12, 1)` for `1 → 1`, `(5, 6, -1)` for `-1`, `(17, 72, -1)` for `-5 → -7`; so the
eigenvalue gap `|D|` is `1` in each case. -/
theorem cycle_table :
    (((Mw (2 : ℤ) 3 [2])ᵀ).trace = 7 ∧ ((Mw (2 : ℤ) 3 [2])ᵀ).det = 12 ∧ Dz [2] = 1) ∧
      (((Mw (2 : ℤ) 3 [1])ᵀ).trace = 5 ∧ ((Mw (2 : ℤ) 3 [1])ᵀ).det = 6 ∧ Dz [1] = -1) ∧
      (((Mw (2 : ℤ) 3 [1, 2])ᵀ).trace = 17 ∧ ((Mw (2 : ℤ) 3 [1, 2])ᵀ).det = 72 ∧
        Dz [1, 2] = -1) := by
  simp only [trace_Mw_transpose, det_Mw_transpose]
  norm_num [Dz, D]

/-- **`S/D` need not be attracting** (correcting the `markoff.py` docstring "attracting fixed point
`x₀ = S/D`"): for the cycle `-1` (gap word `(1)`, `D = -1`) the period map is
`z ↦ (3z+1)/2` and `F(z) + 1 = (3/2)(z + 1)`, so `-1` is repelling on the line. -/
theorem fixed_point_repelling_neg_one (z : ℚ) : periodMap (2 : ℚ) 3 [1] z + 1 = 3 / 2 * (z + 1) := by
  simp [periodMap, stepMap]; ring

/-- **Property P needs `o ≥ 1`** (correcting `spacetime-description.md` §4, stated for every
class): the class `b` (`o = 0`, no odd step) has `S/D = 0/1`, an integer fixed point of
`z ↦ z/2`, but is not a Syracuse cycle. -/
theorem b_fixed_point (z : ℚ) : mob (matB (2 : ℚ)) z = z ↔ z = 0 := by
  rw [mob_matB]; constructor <;> intro h <;> linarith

end PropertyP


/-! ## The hyperbolic picture: a word is a vertical geodesic of `ℍ` -/

section Hyperbolic

open UpperHalfPlane

/-- The multiplier `α(w) = 3^o/2^E > 0` of the period map of `w`. -/
noncomputable def mult (w : Word) : {x : ℝ // 0 < x} := ⟨3 ^ w.length / 2 ^ w.sum, by positivity⟩

/-- The period map `z ↦ (3^o/2^E) z + S/2^E` acting on the upper half-plane
`ℍ ≅ Aff₊(ℝ)`. -/
noncomputable def periodH (w : Word) (z : ℍ) : ℍ := ((Sz w : ℝ) / 2 ^ w.sum) +ᵥ (mult w • z)

/-- The period map on `ℍ` is a hyperbolic isometry. -/
theorem isometry_periodH (w : Word) : Isometry (periodH w) :=
  (isometry_real_vadd _).comp (isometry_pos_mul _)

/-- The period map scales heights by `α(w) = 3^o/2^E`. -/
theorem periodH_im (w : Word) (z : ℍ) : (periodH w z).im = 3 ^ w.length / 2 ^ w.sum * z.im := by
  simp [periodH, mult]

/-- On the boundary coordinate `Re z` the `ℍ`-map is the real period map. -/
theorem periodH_re (w : Word) (z : ℍ) : (periodH w z).re = periodMap (2 : ℝ) 3 w z.re := by
  rw [periodMap_eq (3 : ℝ) two_ne_zero, ← Sz_cast]
  simp [periodH, mult]
  ring

/-- The boundary fixed point `x₀* = S/D ∈ ℝ = ∂ℍ`. -/
noncomputable def fixedPointR (w : Word) : ℝ := (Sz w : ℝ) / Dz w

/-- The translation length `ℓ(w) = |log(2^E/3^o)|`. -/
noncomputable def transLength (w : Word) : ℝ := |Real.log (2 ^ w.sum / 3 ^ w.length)|

/-- **A word is a vertical geodesic** (`STATUS.md`, "Cycle = vertical geodesic"). For a nonempty
word the period map is an isometry of `ℍ` that preserves the vertical geodesic
`Re z = x₀* = S/D`, moves every point of it by exactly `ℓ = |log(2^E/3^o)|`, and moves no point of
`ℍ` by less: `ℓ` is its translation length and `Re = S/D` its axis. -/
theorem periodH_axis {w : Word} (hne : w ≠ []) :
    Isometry (periodH w) ∧
      (∀ z : ℍ, z.re = fixedPointR w → (periodH w z).re = fixedPointR w ∧
        dist z (periodH w z) = transLength w) ∧
      ∀ z : ℍ, transLength w ≤ dist z (periodH w z) := by
  have hlog : ∀ z : ℍ, dist (Real.log z.im) (Real.log (periodH w z).im) = transLength w := by
    intro z
    rw [periodH_im, Real.log_mul (by positivity) z.im_pos.ne', Real.dist_eq, transLength,
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    congr 1; ring
  refine ⟨isometry_periodH w, fun z hz => ?_, fun z => (hlog z).symm.le.trans
    (dist_log_im_le _ _)⟩
  have hre : (periodH w z).re = fixedPointR w := by
    rw [periodH_re, hz, fixedPointR, periodMap_eq_self_iff (3 : ℝ) two_ne_zero
      (by rw [← Dz_cast]; exact_mod_cast Dz_ne_zero hne), Sz_cast, Dz_cast]
  exact ⟨hre, by rw [dist_of_re_eq (hz.trans hre.symm), hlog]⟩

/-- `ℓ = |E log 2 - o log 3|`. -/
theorem transLength_eq (w : Word) :
    transLength w = |w.sum * Real.log 2 - w.length * Real.log 3| := by
  rw [transLength, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- `log(2^E/3^o) = log(1 + D/3^o)` for every word. -/
theorem log_ratio_eq (w : Word) :
    Real.log (2 ^ w.sum / 3 ^ w.length) = Real.log (1 + Dz w / 3 ^ w.length) := by
  congr 1
  rw [Dz_cast, D]
  field_simp
  ring

/-- **Length = the Baker quantity.** For `D > 0`, `ℓ = log(1 + D/3^o)`. -/
theorem transLength_eq_log_one_add {w : Word} (hD : 0 < Dz w) :
    transLength w = Real.log (1 + Dz w / 3 ^ w.length) := by
  rw [transLength, log_ratio_eq, abs_of_pos (Real.log_pos _)]
  have : (0 : ℝ) < Dz w := by exact_mod_cast hD
  have : (0 : ℝ) < Dz w / 3 ^ w.length := by positivity
  linarith

/-- The per-cycle lengths of `markoff-coordinates.md` §5: `ℓ(ab) = log(4/3)`,
`ℓ(a) = log(3/2)`, `ℓ(aab) = log(9/8)` (the note writes `log(8/9)`, which is `-0.1178`; the
length is its absolute value). -/
theorem transLength_examples :
    transLength [2] = Real.log (4 / 3) ∧ transLength [1] = Real.log (3 / 2) ∧
      transLength [1, 2] = Real.log (9 / 8) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [transLength, abs_of_pos (Real.log_pos (by norm_num))]; norm_num
  · rw [transLength, ← abs_neg, ← Real.log_inv, abs_of_pos (Real.log_pos (by norm_num))]
    norm_num
  · rw [transLength, ← abs_neg, ← Real.log_inv, abs_of_pos (Real.log_pos (by norm_num))]
    norm_num

end Hyperbolic

/-! ## Stage 1: the Syracuse holonomy on the Fricke–Markoff cubic -/

section Markoff

open Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

/-- **Fricke's trace identity, homogeneous form.** For `2 × 2` matrices over a commutative ring,
`tr(P Q adj P adj Q) = tr²P det Q + tr²Q det P + tr²(PQ) - trP trQ tr(PQ) - 2 det P det Q`. -/
theorem fricke_hom {R : Type*} [CommRing R] (P Q : Matrix (Fin 2) (Fin 2) R) :
    (P * Q * P.adjugate * Q.adjugate).trace =
      P.trace ^ 2 * Q.det + Q.trace ^ 2 * P.det + (P * Q).trace ^ 2 -
        P.trace * Q.trace * (P * Q).trace - 2 * P.det * Q.det := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- **Fricke's identity** (`markoff-coordinates.md` §1): for `P, Q ∈ SL₂`,
`tr[P,Q] = x² + y² + z² - xyz - 2` with `(x, y, z) = (tr P, tr Q, tr PQ)`. -/
theorem fricke {R : Type*} [CommRing R] (P Q : SL(2, R)) :
    ((⁅P, Q⁆ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace =
      (P : Matrix (Fin 2) (Fin 2) R).trace ^ 2 + (Q : Matrix (Fin 2) (Fin 2) R).trace ^ 2 +
        ((P : Matrix (Fin 2) (Fin 2) R) * Q).trace ^ 2 -
        (P : Matrix (Fin 2) (Fin 2) R).trace * (Q : Matrix (Fin 2) (Fin 2) R).trace *
          ((P : Matrix (Fin 2) (Fin 2) R) * Q).trace - 2 := by
  rw [commutatorElement_def, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv, fricke_hom, P.2, Q.2]
  ring

/-- Upper-triangular (reducible: common fixed point `∞`) pairs have `tr[P,Q] = 2`. -/
theorem trace_commutator_of_upper {R : Type*} [CommRing R] (P Q : SL(2, R))
    (hP : (P : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) (hQ : (Q : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ((⁅P, Q⁆ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R).trace = 2 := by
  have dP := P.2
  have dQ := Q.2
  rw [Matrix.det_fin_two, hP] at dP
  rw [Matrix.det_fin_two, hQ] at dQ
  rw [commutatorElement_def, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv,
    Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, hP, hQ]
  linear_combination (2 * (Q : Matrix (Fin 2) (Fin 2) R) 0 0 * (Q : Matrix (Fin 2) (Fin 2) R) 1 1) * dP + 2 * dQ

/-- `a`, normalised into `SL₂(ℝ)`: `A/√6`. -/
noncomputable def slA : SL(2, ℝ) :=
  ⟨(√6)⁻¹ • matA (2 : ℝ) 3, by
    rw [Matrix.det_smul, matA, Matrix.det_fin_two_of]
    simp [inv_pow, Real.sq_sqrt]; norm_num⟩

/-- `b`, normalised into `SL₂(ℝ)`: `B/√2`. -/
noncomputable def slB : SL(2, ℝ) :=
  ⟨(√2)⁻¹ • matB (2 : ℝ), by
    rw [Matrix.det_smul, matB, Matrix.det_fin_two_of]
    simp [inv_pow, Real.sq_sqrt]⟩

/-- `√6 √2 = 2√3`. -/
theorem sqrt_six_mul_sqrt_two : √6 * √2 = 2 * √3 := by
  rw [← Real.sqrt_mul (by norm_num), show (6 : ℝ) * 2 = 2 ^ 2 * 3 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- **Trace coordinates** (`markoff-coordinates.md` §1): `(tr A, tr B, tr AB) =
(5/√6, 3/√2, 7/(2√3))` for the `SL₂(ℝ)`-normalised generators. -/
theorem trace_coords :
    (slA : Matrix (Fin 2) (Fin 2) ℝ).trace = 5 / √6 ∧
      (slB : Matrix (Fin 2) (Fin 2) ℝ).trace = 3 / √2 ∧
      ((slA : Matrix (Fin 2) (Fin 2) ℝ) * slB).trace = 7 / (2 * √3) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [slA, matA, Matrix.trace_fin_two]; ring
  · simp [slB, matB, Matrix.trace_fin_two]; ring
  · simp [slA, slB, matA, matB, Matrix.trace_fin_two]
    rw [← sqrt_six_mul_sqrt_two]; field_simp; ring

/-- **The commutator is the parabolic `z ↦ z + 1/4`** (`markoff-coordinates.md` §3):
`[A, B] = !![1, 1/4; 0, 1]` (the normalisation cancels in a commutator). -/
theorem commutator_eq :
    ((⁅slA, slB⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1 / 4; 0, 1] := by
  have h6 : (√6)⁻¹ * (√6)⁻¹ = (6 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  have h2 : (√2)⁻¹ * (√2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  rw [commutatorElement_def, coe_mul, coe_mul, coe_mul, coe_inv, coe_inv]
  simp only [slA, slB, Matrix.adjugate_smul, Fintype.card_fin, matA, matB,
    Matrix.adjugate_fin_two_of, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (√2)⁻¹ ^ (2 - 1) * ((√6)⁻¹ ^ (2 - 1) * ((√2)⁻¹ * (√6)⁻¹)) = (12 : ℝ)⁻¹ by
    rw [pow_one, pow_one, show (√2)⁻¹ * ((√6)⁻¹ * ((√2)⁻¹ * (√6)⁻¹)) =
      ((√6)⁻¹ * (√6)⁻¹) * ((√2)⁻¹ * (√2)⁻¹) by ring, h6, h2]; norm_num]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- **`tr[A,B] = +2`** (reducible point). -/
theorem trace_commutator : ((⁅slA, slB⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by
  rw [commutator_eq, Matrix.trace_fin_two]; simp; norm_num

/-- **Fricke level** (`markoff-coordinates.md` §1): `x² + y² + z² - xyz = 4`, the level set
`tr[A,B] = 2` of the cubic. -/
theorem fricke_level :
    (5 / √6) ^ 2 + (3 / √2) ^ 2 + (7 / (2 * √3)) ^ 2 - 5 / √6 * (3 / √2) * (7 / (2 * √3)) =
      (4 : ℝ) := by
  have := fricke slA slB
  rw [trace_commutator, trace_coords.1, trace_coords.2.1, trace_coords.2.2] at this
  linarith

/-- **Reducibility.** `A` and `B` are upper triangular: they share the eigenvector `(1,0)`, i.e.
the fixed point `∞`; hence (by `trace_commutator_of_upper`) `tr[A,B] = 2`. -/
theorem shared_fixed_point :
    matA (2 : ℝ) 3 *ᵥ ![1, 0] = (3 : ℝ) • ![1, 0] ∧ matB (2 : ℝ) *ᵥ ![1, 0] = (1 : ℝ) • ![1, 0] ∧
      (slA : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (slB : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [matA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [matB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [slA, matA]
  · simp [slB, matB]

/-- **The commutator is a non-trivial parabolic** (unipotent, `≠ 1`). -/
theorem commutator_parabolic :
    ⁅slA, slB⁆ ≠ 1 ∧
      ((⁅slA, slB⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1 ≠ 0 ∧
      (((⁅slA, slB⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1) ^ 2 = 0 := by
  have hne : ((⁅slA, slB⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1 ≠ 0 := by
    rw [commutator_eq]; intro h
    have := congrFun (congrFun h 0) 1
    simp at this
  refine ⟨fun h => hne (by rw [h]; simp), hne, ?_⟩
  rw [commutator_eq, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sq]

/-- **All traces lie in `(2, 3)`**: the generators and `ab` are hyperbolic (`> 2`) and
**sub-Markoff** (`< 3`). -/
theorem traces_bounds :
    (2 < 5 / √6 ∧ 5 / √6 < (3 : ℝ)) ∧ (2 < 3 / √2 ∧ 3 / √2 < (3 : ℝ)) ∧
      (2 < 7 / (2 * √3) ∧ 7 / (2 * √3) < (3 : ℝ)) := by
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have p6 : 0 < √6 := by positivity
  have p2 : 0 < √2 := by positivity
  have p3 : 0 < √3 := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ p6]; nlinarith
  · rw [div_lt_iff₀ p6]; nlinarith
  · rw [lt_div_iff₀ p2]; nlinarith
  · rw [div_lt_iff₀ p2]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- The discriminant of `z ↦ z² - xy z + (x² + y²)` at the Syracuse `(x, y)` is `-191/12`. -/
theorem sub_markoff_disc :
    (5 / √6 * (3 / √2)) ^ 2 - 4 * ((5 / √6) ^ 2 + (3 / √2) ^ 2) = (-191 / 12 : ℝ) := by
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

/-- **The cusped sheet is unreachable at fixed `(x, y)`** (`markoff-coordinates.md` §4,
sharpened): every pair `P, Q ∈ SL₂(ℝ)` with the Syracuse generator traces `tr P = 5/√6`,
`tr Q = 3/√2` has `tr[P,Q] ≥ 95/48` (minimum over `z = tr PQ` of the Fricke polynomial). -/
theorem trace_commutator_ge (P Q : SL(2, ℝ))
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ).trace = 5 / √6)
    (hQ : (Q : Matrix (Fin 2) (Fin 2) ℝ).trace = 3 / √2) :
    95 / 48 ≤ ((⁅P, Q⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  rw [fricke, hP, hQ]
  set z := ((P : Matrix (Fin 2) (Fin 2) ℝ) * Q).trace
  have hx : (5 / √6) ^ 2 = (25 / 6 : ℝ) := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hy : (3 / √2) ^ 2 = (9 / 2 : ℝ) := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hxy : (5 / √6 * (3 / √2)) ^ 2 = (75 / 4 : ℝ) := by rw [mul_pow, hx, hy]; norm_num
  nlinarith [sq_nonneg (z - 5 / √6 * (3 / √2) / 2)]

/-- In particular no real pair with the Syracuse generator traces reaches the Markoff sheet
`tr[P,Q] = -2` of cusped hyperbolic once-punctured tori. -/
theorem trace_commutator_ne_neg_two (P Q : SL(2, ℝ))
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ).trace = 5 / √6)
    (hQ : (Q : Matrix (Fin 2) (Fin 2) ℝ).trace = 3 / √2) :
    ((⁅P, Q⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace ≠ -2 := by
  have := trace_commutator_ge P Q hP hQ
  intro h; rw [h] at this; norm_num at this

end Markoff


/-! ## Stage 2: the flat Lorentzian model `ℝ^{2,1} = 𝔰𝔩₂(ℝ)` -/

section Lorentzian

open scoped commutatorElement

/-- The spacelike `𝔰𝔩₂` basis vector `H = diag(1, -1)`. -/
def Hm : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The null `𝔰𝔩₂` basis vector `E` (upper nilpotent). -/
def Em : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The null `𝔰𝔩₂` basis vector `F` (lower nilpotent). -/
def Fm : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The Lorentzian quadratic form `q(X) = -det X`. -/
noncomputable def qf (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := -X.det

/-- The Lorentzian bilinear form `⟨X, Y⟩ = ½ tr(XY)`. -/
noncomputable def bil (X Y : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (X * Y).trace / 2

/-- The adjoint action `Ad g X = g X g⁻¹`. -/
noncomputable def Ad (g X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := g * X * g⁻¹

/-- On `𝔰𝔩₂`, `q(X) = -det X = ½ tr X² = ⟨X, X⟩`. -/
theorem qf_eq_bil {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.trace = 0) : qf X = bil X X := by
  rw [Matrix.trace_fin_two] at hX
  simp only [qf, bil, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have : X 1 1 = -X 0 0 := by linarith
  rw [this]; ring

/-- The frame `(H, E, F)`: `H` spacelike, `E, F` null, `⟨E, F⟩ = ½`, `⟨E, H⟩ = 0`, and `E - F`
timelike. -/
theorem frame :
    qf Hm = 1 ∧ qf Em = 0 ∧ qf Fm = 0 ∧ bil Em Fm = 1 / 2 ∧ bil Em Hm = 0 ∧ qf (Em - Fm) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [qf, bil, Hm, Em, Fm, Matrix.det_fin_two, Matrix.trace_fin_two]

/-- `Ad` is an isometry of `q` (`Ad : GL₂ → O(2,1)`). -/
theorem qf_Ad {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    qf (Ad g X) = qf X := by
  simp only [qf, Ad, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

/-- Turning a twisted commutation relation into an eigen-equation for `Ad`. -/
theorem Ad_eq_of_mul {g X : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {c : ℝ}
    (h : g * X = c • (X * g)) : Ad g X = c • X := by
  rw [Ad, h, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg), Matrix.mul_one]

/-- The cycle element `G(w) = (Mw w)ᵀ = !![3^o, S; 0, 2^E]` over `ℝ`. -/
noncomputable def Gw (w : Word) : Matrix (Fin 2) (Fin 2) ℝ := (Mw (2 : ℝ) 3 w)ᵀ

/-- `G(w) = !![3^o, S; 0, 2^E]`. -/
theorem Gw_eq (w : Word) : Gw w = !![3 ^ w.length, S (2 : ℝ) 3 w; 0, 2 ^ w.sum] := by
  rw [Gw, Mw_eq]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- `det G(w) = 2^E 3^o ≠ 0`. -/
theorem det_Gw_ne_zero (w : Word) : (Gw w).det ≠ 0 := by
  rw [Gw_eq, Matrix.det_fin_two_of]; simp

/-- The neutral vector `x⁰ = G - (tr G / 2) I` (the traceless part of `G`). -/
noncomputable def neutral (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  G - (G.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- The third eigenvector `V = !![x, -x²; 1, -x]`, `x = S/D`: the null vector at the fixed
point. -/
noncomputable def Vw (w : Word) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![S (2 : ℝ) 3 w / D (2 : ℝ) 3 w, -(S (2 : ℝ) 3 w / D (2 : ℝ) 3 w) ^ 2;
    1, -(S (2 : ℝ) 3 w / D (2 : ℝ) 3 w)]

/-- **Spectrum of `Ad` of a cycle element** (`lorentzian.md` (A)). For a nonempty word, `Ad G(w)`
has the three eigenvectors `E`, `x⁰`, `V` in `𝔰𝔩₂` (all traceless, nonzero) with eigenvalues
`3^o/2^E`, `1`, `2^E/3^o`; `E` and `V` are null, and `x⁰` is spacelike with
`q(x⁰) = D²/4` (so `x⁰` becomes null exactly at criticality `2^E = 3^o`). -/
theorem Ad_Gw_spectrum {w : Word} (hne : w ≠ []) :
    Ad (Gw w) Em = ((3 : ℝ) ^ w.length / 2 ^ w.sum) • Em ∧
      Ad (Gw w) (neutral (Gw w)) = neutral (Gw w) ∧
      Ad (Gw w) (Vw w) = ((2 : ℝ) ^ w.sum / 3 ^ w.length) • Vw w ∧
      (Em.trace = 0 ∧ (neutral (Gw w)).trace = 0 ∧ (Vw w).trace = 0) ∧
      (Em ≠ 0 ∧ neutral (Gw w) ≠ 0 ∧ Vw w ≠ 0) ∧
      (qf Em = 0 ∧ qf (Vw w) = 0 ∧ qf (neutral (Gw w)) = D (2 : ℝ) 3 w ^ 2 / 4) ∧
      (3 : ℝ) ^ w.length / 2 ^ w.sum ≠ 1 := by
  have hD : D (2 : ℝ) 3 w ≠ 0 := by rw [← Dz_cast]; exact_mod_cast Dz_ne_zero hne
  have hD' : (2 : ℝ) ^ w.sum - 3 ^ w.length ≠ 0 := hD
  have hdet := det_Gw_ne_zero w
  have h2 : (2 : ℝ) ^ w.sum ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ w.length ≠ 0 := by positivity
  have hneu : Ad (Gw w) (neutral (Gw w)) = neutral (Gw w) := by
    have := Ad_eq_of_mul (c := 1) hdet (X := neutral (Gw w)) (by
      rw [one_smul, neutral, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul])
    rwa [one_smul] at this
  refine ⟨Ad_eq_of_mul hdet ?_, hneu, Ad_eq_of_mul hdet ?_,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Gw_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp [Em]
  · rw [Gw_eq]; ext i j; fin_cases i <;> fin_cases j <;> simp [Vw, D] <;> field_simp <;> ring
  · simp [Em, Matrix.trace_fin_two]
  · simp [neutral, Matrix.trace_fin_two]
  · simp [Vw, Matrix.trace_fin_two]
  · intro h; have := congrFun (congrFun h 0) 1; simp [Em] at this
  · intro h; have := congrFun (congrFun h 0) 0
    rw [Gw_eq] at this; simp [neutral, Matrix.trace_fin_two] at this
    exact hD' (by linear_combination -2 * this)
  · intro h; have := congrFun (congrFun h 1) 0; simp [Vw] at this
  · simp [qf, Em, Matrix.det_fin_two]
  · simp [qf, Vw, Matrix.det_fin_two]; ring
  · rw [Gw_eq]; simp [qf, neutral, Matrix.det_fin_two, Matrix.trace_fin_two, D]; ring
  · rw [Ne, div_eq_one_iff_eq h2]; exact fun h => hD' (by rw [h]; ring)

/-- The `Ad`-action of a diagonal matrix: `Ad diag(p, s)` scales `X₀₁` by `p/s` and `X₁₀` by
`s/p`. -/
theorem Ad_diag {p s : ℝ} (hp : p ≠ 0) (hs : s ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Ad !![p, 0; 0, s] X = !![X 0 0, p / s * X 0 1; s / p * X 1 0, X 1 1] := by
  have hinv : (!![p, 0; 0, s] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![p⁻¹, 0; 0, s⁻¹] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i <;> fin_cases j <;> simp [hp, hs]
  rw [Ad, hinv]
  conv_lhs => rw [Matrix.eta_fin_two X]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

/-- The diagonal (multiplicative `2`–`3`) skeleton `L(G) = diag(G₀₀, G₁₁)` of an upper-triangular
`G`: the linear part of the flat holonomy. -/
def skel (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![G 0 0, 0; 0, G 1 1]

/-- The translation part `τ(G) = (G₀₁/G₁₁) E`, valued in the null line `ℝE`. -/
noncomputable def tau (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (G 0 1 / G 1 1) • Em

/-- The affine isometry `X ↦ Ad(L(G)) X + τ(G)` of `ℝ^{2,1}`. -/
noncomputable def affAct (G X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Ad (skel G) X + tau G

/-- **The linear part on the generators** (`spacetime-description.md` §1): `Ad L(a)` acts on
`(H, E, F)` as `(H, (3/2)E, (2/3)F)` and `Ad L(b)` as `(H, (1/2)E, 2F)`; and `τ(a) = ½E`,
`τ(b) = 0`. -/
theorem generators_lorentzian :
    (Ad (skel (matA (2 : ℝ) 3)) Hm = Hm ∧ Ad (skel (matA (2 : ℝ) 3)) Em = (3 / 2 : ℝ) • Em ∧
        Ad (skel (matA (2 : ℝ) 3)) Fm = (2 / 3 : ℝ) • Fm) ∧
      (Ad (skel (matB (2 : ℝ))) Hm = Hm ∧ Ad (skel (matB (2 : ℝ))) Em = (1 / 2 : ℝ) • Em ∧
        Ad (skel (matB (2 : ℝ))) Fm = (2 : ℝ) • Fm) ∧
      tau (matA (2 : ℝ) 3) = (1 / 2 : ℝ) • Em ∧ tau (matB (2 : ℝ)) = 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [skel, matA, matB, tau, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
    | (rw [Ad_diag (by norm_num) (by norm_num)]
       ext i j; fin_cases i <;> fin_cases j <;> simp [Hm, Em, Fm])
    | simp

/-- Upper-triangular with invertible diagonal: the Borel subgroup fixing `∞`. -/
def IsBorel (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop := G 1 0 = 0 ∧ G 0 0 ≠ 0 ∧ G 1 1 ≠ 0

/-- `Ad` is multiplicative. -/
theorem Ad_mul (g h X : Matrix (Fin 2) (Fin 2) ℝ) : Ad (g * h) X = Ad g (Ad h X) := by
  simp only [Ad, Matrix.mul_inv_rev, Matrix.mul_assoc]

/-- **Cocycle law** for `τ`: `L(GH) = L(G) L(H)` and `τ(GH) = τ(G) + Ad(L(G)) τ(H)`; hence
`G ↦ (L(G), τ(G))` is a homomorphism from the Borel group into `Isom(ℝ^{2,1})`. -/
theorem skel_tau_mul {G H : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsBorel G) (hH : IsBorel H) :
    skel (G * H) = skel G * skel H ∧ tau (G * H) = tau G + Ad (skel G) (tau H) := by
  obtain ⟨g10, g00, g11⟩ := hG
  obtain ⟨h10, h00, h11⟩ := hH
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [skel, Matrix.mul_apply, Fin.sum_univ_two, g10, h10]
  · rw [skel, Ad_diag g00 g11]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [tau, Em, Matrix.mul_apply, Fin.sum_univ_two, g10]
    field_simp
    ring

/-- `affAct` is multiplicative on the Borel group. -/
theorem affAct_mul {G H : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsBorel G) (hH : IsBorel H)
    (X : Matrix (Fin 2) (Fin 2) ℝ) : affAct (G * H) X = affAct G (affAct H X) := by
  obtain ⟨h1, h2⟩ := skel_tau_mul hG hH
  rw [affAct, h1, h2, Ad_mul]
  simp only [affAct, Ad, Matrix.mul_add, Matrix.add_mul]
  abel

/-- **On the null line `ℝE` the affine action is the Möbius action**: `affAct G (zE) = (G·z) E`. -/
theorem affAct_null_line {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsBorel G) (z : ℝ) :
    affAct G (z • Em) = mob G z • Em := by
  obtain ⟨g10, g00, g11⟩ := hG
  rw [affAct, skel, Ad_diag g00 g11, tau, mob, g10]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Em]
  field_simp

/-- Cycle elements are Borel. -/
theorem isBorel_Gw (w : Word) : IsBorel (Gw w) := by
  rw [Gw_eq]; refine ⟨rfl, ?_, ?_⟩ <;> simp

/-- The Borel group is closed under products. -/
theorem IsBorel.mul {G H : Matrix (Fin 2) (Fin 2) ℝ} (hG : IsBorel G) (hH : IsBorel H) :
    IsBorel (G * H) := by
  obtain ⟨g10, g00, g11⟩ := hG
  obtain ⟨h10, h00, h11⟩ := hH
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, g10, h10, g00, g11, h00, h11]

/-- Every letter word has a Borel matrix (the holonomy is reducible, fixing `∞`). -/
theorem isBorel_lmat (u : List Letter) : IsBorel (lmat (2 : ℝ) 3 u) := by
  induction u with
  | nil => exact ⟨by simp [lmat], by simp [lmat], by simp [lmat]⟩
  | cons c u ih =>
    refine ih.mul ?_
    cases c <;> refine ⟨?_, ?_, ?_⟩ <;> simp [Letter.mat, matA, matB]

/-- **The translation cocycle is `τ(γ) = (S/2^E) E`** (`spacetime-description.md` §1), it is
null, and on the null line it realises the period map: `affAct G(w) (zE) = F_w(z) E`. -/
theorem tau_Gw (w : Word) :
    tau (Gw w) = (S (2 : ℝ) 3 w / 2 ^ w.sum) • Em ∧ qf (tau (Gw w)) = 0 ∧
      ∀ z : ℝ, affAct (Gw w) (z • Em) = periodMap (2 : ℝ) 3 w z • Em := by
  refine ⟨by rw [tau, Gw_eq]; rfl, by simp [qf, tau, Em, Matrix.det_fin_two], fun z => ?_⟩
  rw [affAct_null_line (isBorel_Gw w), Gw, mob_Mw_transpose (3 : ℝ) two_ne_zero]

/-- **The Margulis invariant vanishes identically** (`lorentzian.md` (B)): for every Borel `G`,
`⟨τ(G), x⁰(L(G))⟩ = 0`, because `τ ∈ ℝE`, `x⁰(L) ∈ ℝH` and `⟨E, H⟩ = 0`. -/
theorem margulis_eq_zero (G : Matrix (Fin 2) (Fin 2) ℝ) : bil (tau G) (neutral (skel G)) = 0 := by
  simp [bil, tau, neutral, skel, Em, Matrix.trace_fin_two, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two]

/-- The Margulis invariant vanishes on every letter word, i.e. on the whole monoid image. -/
theorem margulis_lmat (u : List Letter) :
    bil (tau (lmat (2 : ℝ) 3 u)) (neutral (skel (lmat (2 : ℝ) 3 u))) = 0 :=
  margulis_eq_zero _

/-- **The literal cocycle forces a reducible base** (correcting `spacetime-description.md` §1,
"a crossed homomorphism for whichever linear part `L`"): if `τ(γ) = (S/2^E)E` satisfies the
cocycle law `τ(aa) = τ(a) + Ad(L(a)) τ(a)` for some invertible `L(a)`, then `L(a)` fixes `∞`
(`L(a)₁₀ = 0`). So no Fuchsian (irreducible) linear part carries `τ`, as `SYNTHESIS.md` §2 says. -/
theorem tau_cocycle_forces_borel {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (h : tau (Gw [1, 1]) = tau (Gw [1]) + Ad g (tau (Gw [1]))) : g 1 0 = 0 := by
  rw [(tau_Gw _).1, (tau_Gw _).1] at h
  norm_num [S] at h
  simp only [Ad, Matrix.mul_smul, Matrix.smul_mul] at h
  have h1 : (1 / 2 : ℝ) • (g * Em * g⁻¹) = (3 / 4 : ℝ) • Em := by
    rw [show (3 / 4 : ℝ) = 5 / 4 - 1 / 2 by norm_num, sub_smul, h]; abel
  have hAd : g * Em * g⁻¹ = (3 / 2 : ℝ) • Em := by
    have := congrArg ((2 : ℝ) • ·) h1
    simp only [smul_smul] at this
    norm_num at this
    exact this
  have hmul : g * Em = (3 / 2 : ℝ) • (Em * g) := by
    rw [← Matrix.smul_mul, ← hAd, Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.2 hg), Matrix.mul_one]
  have := congrFun (congrFun hmul 1) 1
  simpa [Em, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this

/-- **The fixed locus is a spacelike line at null-position `S/D`** (`spacetime-description.md`
§4). For a nonempty word, a traceless `X` is fixed by `X ↦ Ad(L(w)) X + τ(w)` iff
`X = t H + (S/D) E` for some `t`; the direction `H` is spacelike (`q(H) = 1`). -/
theorem affAct_fixed_iff {w : Word} (hne : w ≠ []) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : X.trace = 0) :
    affAct (Gw w) X = X ↔ ∃ t : ℝ, X = t • Hm + (S (2 : ℝ) 3 w / D (2 : ℝ) 3 w) • Em := by
  have hD : D (2 : ℝ) 3 w ≠ 0 := by rw [← Dz_cast]; exact_mod_cast Dz_ne_zero hne
  have hD' : (2 : ℝ) ^ w.sum - 3 ^ w.length ≠ 0 := hD
  have h2 : (2 : ℝ) ^ w.sum ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ w.length ≠ 0 := by positivity
  rw [Matrix.trace_fin_two] at hX
  have h11 : X 1 1 = -X 0 0 := by linarith
  rw [affAct, skel, tau, Gw_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [Ad_diag h3 h2]
  constructor
  · intro h
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    simp [Em] at e01 e10
    refine ⟨X 0 0, ?_⟩
    have hx10 : X 1 0 = 0 := by
      have : (2 ^ w.sum / 3 ^ w.length - 1) * X 1 0 = 0 := by linear_combination e10
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by field_simp at h; linear_combination h) hD'
      · exact h
    have hx01 : X 0 1 = S (2 : ℝ) 3 w / D (2 : ℝ) 3 w := by
      rw [eq_div_iff hD, D]
      field_simp at e01
      linear_combination -e01
    ext i j; fin_cases i <;> fin_cases j <;> simp [Hm, Em, hx10, hx01, h11]
  · rintro ⟨t, rfl⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [Hm, Em, D]
    field_simp
    ring

/-- **The puncture is an extreme-BTZ (parabolic) holonomy** (`brunswic-spacetime.md`): `Ad` of
`[A, B] = !![1, 1/4; 0, 1]` fixes the null vector `E` and is unipotent in the frame `(E, H, F)`:
`H ↦ H - ½E`, `F ↦ F + ¼H - (1/16)E`. -/
theorem Ad_commutator :
    Ad ↑⁅slA, slB⁆ Em = Em ∧ Ad ↑⁅slA, slB⁆ Hm = Hm - (1 / 2 : ℝ) • Em ∧
      Ad ↑⁅slA, slB⁆ Fm = Fm + (1 / 4 : ℝ) • Hm - (1 / 16 : ℝ) • Em := by
  rw [commutator_eq]
  have hinv : (!![1, 1 / 4; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1, -1 / 4; 0, 1] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i <;> fin_cases j <;> norm_num
  refine ⟨?_, ?_, ?_⟩ <;> rw [Ad, hinv] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Hm, Em, Fm]
  all_goals norm_num

end Lorentzian

end Syracuse.PuncturedTorus
