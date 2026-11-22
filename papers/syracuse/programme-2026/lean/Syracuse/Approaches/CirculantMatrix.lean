import Syracuse.Basic

/-!
# Circulant matrix: rotation sums as row sums of a twisted circulant

Formalisation of `approaches/circulant_matrix` (`RATIONALE`, `STATUS`, `factorization`,
`gamma_w`, `number_field`, `circuits`). Notation of `Syracuse.Basic`: `w : Word`, `E = w.sum`,
`o = w.length`, prefix sums `e w k`, rotation sums `S^{(j)} = S X Y (w.rotate j)`,
`D X Y w = X^E - Y^o`.

The rotation-sum matrix `Mrot X Y w` has entries
`M_{j,i} = X^{e_i - e_j + E·[i<j]} Y^{o-1-((i-j) mod o)}` with natural-number exponents (`xExp`,
`yExp`; the `X`-exponent is written `e_i + E·[i<j] - e_j`, which never truncates, `xExp_add`).
Its row sums are the rotation sums, and `det M = (-1)^{o+1} D^{o-1}` in every commutative ring:
the factors `X^{e_i - e_j}` cancel along every permutation (`det_Mrot_eq_det_N`), and the
word-free matrix `N` satisfies `R_{j+1} - Y R_j = D e_j` (`N_succ_sub`, `det_N`). The number-field
statements live in the étale algebra `A = ℚ[x]/(x^o - 2^E)` (`Alg w`, `xhat w`), which is the
note's field `K = ℚ(2^{E/o})` exactly when `gcd(E, o) = 1` (`circuits.md` §1).

## Coverage

| Note claim (file) | Lean name | Status |
|---|---|---|
| (⋆) `S^{(j)} = Σ_i M_{j,i}`, `S⃗ = M𝟙` (RATIONALE Step 1) | `Mrot_rowSum`, `Mrot_mulVec_one` | proved (`ℤ[X,Y]`) |
| `M` has non-negative integer exponents (RATIONALE Step 1) | `xExp_add` | proved |
| `M = Δ⁻¹CΔ`, `Δ = diag 2^{ẽ_k}`, `c_r = 2^{rE/o}3^{o-1-r}` (RATIONALE Step 2) | `Mrot_eq_conj`, `Δinv_mul_Δ` | proved (over `ℝ`) |
| `det M = det C = (-1)^{o+1}D^{o-1}` (RATIONALE 2, factorization (1b)) | `det_Mrot`, `det_circ_real` | proved (`ℤ[X,Y]`, `o ≥ 1`) |
| checks `1→1`, `-5→-7`, `(8,5) ↦ 13^4`, `(7,4) ↦ -47^3` (RATIONALE 2, STATUS) | `example`s | proved |
| `C v_ℓ = ĉ_ℓ v_ℓ`, `ĉ_ℓ = D/(2^{E/o}ω^ℓ - 3)` (RATIONALE 1, factorization (1a)) | `circ_spectrum`, `circ_mulVec_dftVec`, `eigenvalue_mul` | proved (over `ℂ`) |
| `det C = ∏_ℓ ĉ_ℓ` (factorization (1a)) | `det_circ_eq_prod` | proved |
| `∏_ℓ (3 - 2^{E/o}ω^ℓ) = 3^o - 2^E` (factorization (1b)) | `prod_three_sub` | proved |
| `det Circ(1,ρ,…,ρ^{o-1}) = (-1)^{o+1}(ρ^o-1)^{o-1}` (factorization (1c)) | `det_circ_geometric` | proved (field, `ρ ≠ 0`) |
| Identity A: `|D| = ∏_ℓ |3 - 2^{E/o}ω^ℓ|` | `identityA` | proved |
| Identity A, cosine form `|3-β| ∏_{ℓ=1}^{⌊o/2⌋}(9 - 6β cos(2πℓ/o) + β²)` | `identityA_cos_false`, `identityA_cos` | corrected: false for even `o` (`(E,o) = (4,2)`: `7 ≠ 49`); proved `D² = ∏_{ℓ<o}(9 - 6β cos(2πℓ/o) + β²)` |
| Identity A: only the real factor can be small | — | not formalized (heuristic) |
| Identity B: `det M` depends only on `(E,o)` | `det_Mrot_word_independent` | proved |
| Identity C: `adj(M)S⃗ = (-1)^{o+1}D^{o-1}𝟙`, so `gcd_j S^{(j)} ∣ D^{o-1}` | `adjugate_mulVec_S`, `dvd_D_pow_of_dvd_S` | proved |
| Identity D: Leibniz identity | `leibniz_Mrot` | proved |
| SNF of `M` / content of `M𝟙` (RATIONALE 3, factorization §3) | — | not formalized (open question) |
| `D = ∏_{m<g}(2^a - 3^bζ_g^m)`, `g = gcd(E,o)` (circuits §2) | `D_eq_prod_circuits`, `Dz_eq_prod_circuits` | proved (domain with a primitive `g`-th root; `ℂ`) |
| `x^o - 2^E = ∏_{m<g}(x^b - 2^aζ_g^m)` (circuits §2) | `X_pow_sub_eq_prod_circuits` | proved (`ℂ[x]`) |
| `D = ±N(β - 3)` (number_field §2, circuits §1) | `norm_xhat_sub_three` | proved in `A` for all `(E,o)`; `A ≅ K` for `g = 1` not formalized |
| `N_{K/ℚ}(β-3) = (-1)^b(3^b - 2^a)`, principal circuit (number_field §2, circuits §2) | `norm_principal_circuit` | proved in `ℚ[x]/(x^b - 2^a)` |
| `ĉ_0 = D/(β-3) = Σ_k 3^{o-1-k}β^k` (number_field §3, §6a) | `chat0`, `chat0_mul`, `xhat_sub_three_mul_inv` | proved |
| `det M = N(ĉ_0) = ±D^{o-1}` (number_field §3, circuits §1) | `norm_chat0`, `det_Mrot_eq_norm` | proved |
| eigenvalues are a Galois orbit (number_field §3) | — | not formalized |
| `C` is a regular representation (number_field §4) | `leftMulMatrix_chat0` | proved, integral form: `N(2^E,3)ᵀ` is the matrix of `ĉ_0·` on `A` |
| primes of `D` ↔ degree-one primes `(p, β-3)`, ideal reading (number_field §5) | — | not formalized |
| `2^{e_j}S^{(j)} = Tr_{A/ℚ}(γ_W β^j ĉ_0)` (number_field §6c, circuits §1) | `trace_identity` | proved (every `(E,o)`) |
| `γ_W = (1/o)Σ_k 2^{e_k}β^{-k}` represents `L(β^k) = 2^{e_k}` (gamma_w §1, number_field §6b) | `gammaW`, `trace_gammaW_mul_xhat_pow` | proved |
| `Tr(x̂^n) = o·2^{En/o}·[o ∣ n]` (circuits §1) | `trace_xhat_pow`, `trace_xhat_pow_lt_two_mul` | proved for `n < 2o` |
| `γ_W` in the codifferent; uniqueness of `γ_W` (number_field §6c) | — | not formalized |
| `T_j = Tr(γ_Wβ^j/(β-3)) = 2^{e_j}S^{(j)}/D` (number_field §7, gamma_w §2) | `T`, `T_eq_trace` | proved |
| `δ_j = |D|/gcd(S^{(j)}, D)` (number_field §7) | `delta_eq` | proved (`E, o ≥ 1`) |
| gcd law `gcd_j S^{(j)} = |D|/lcm_j δ_j` (number_field §7) | `gcd_law` | proved (`E, o ≥ 1`) |
| rotation collapse `gcd_j S^{(j)} = gcd(S^{(0)}, D)` (gamma_w §0) | `gcd_S_rotate`, `gcdRot_eq` | proved |
| "`v_p(S^{(j)})` independent of `j`" (STATUS rotation-collapse bullet) | `vp_not_rotation_invariant` | corrected: false (`w = (1,3,1,3)`, `D = 5²·7`, `v_5(S^{(j)}) = 3,2,3,2`); only `min(v_p(S^{(j)}), v_p(D))` is invariant (`gcd_S_rotate`) |
| cycle ⇒ every `T_j` integral (number_field §7) | `delta_eq_one_of_cycle` | proved |
| every `T_j` integral ⇒ cycle (number_field §7) | — | not formalized |
| examples `(3,3)`: gcd `11`; `(6,4)`: real circuit is a unit | `example`s | proved |
| local picture at `(p, β-3)` (gamma_w §3); `A ≅ ∏K_i`, one prime per circuit (circuits §2–3) | — | not formalized |
-/


namespace Syracuse.CirculantMatrix

open Finset Matrix

/-- The `X`-exponent `e_i - e_j + E·[i<j]` of `M_{j,i}` (never truncated, see `xExp_add`). -/
def xExp (w : Word) (j i : ℕ) : ℕ := e w i + (if i < j then w.sum else 0) - e w j

/-- The `Y`-exponent `o - 1 - ((i - j) mod o)` of `M_{j,i}`. -/
def yExp {o : ℕ} (j i : Fin o) : ℕ := o - 1 - ((i - j : Fin o) : ℕ)

/-- Prefix sums are monotone: `j ≤ i → e_j ≤ e_i`. -/
lemma e_le_e (w : Word) {j i : ℕ} (h : j ≤ i) : e w j ≤ e w i := by
  unfold e
  have := List.sum_take_add_sum_drop (w.take i) j
  rw [List.take_take, Nat.min_eq_left h] at this
  omega

/-- Every prefix sum is at most `E`. -/
lemma e_le_sum (w : Word) (j : ℕ) : e w j ≤ w.sum := by
  have := List.sum_take_add_sum_drop w j
  unfold e; omega

/-- `e_o = E`. -/
lemma e_length (w : Word) : e w w.length = w.sum := by simp [e]

/-- The exponent `xExp` is a genuine (untruncated) difference. -/
lemma xExp_add (w : Word) (j i : ℕ) :
    xExp w j i + e w j = e w i + (if i < j then w.sum else 0) := by
  unfold xExp
  split_ifs with h
  · have := e_le_sum w j; omega
  · have := e_le_e w (not_lt.1 h); omega

/-- `(i - j) mod o` for `Fin o` subtraction, as a case split. -/
lemma val_sub_fin {o : ℕ} (i j : Fin o) :
    ((i - j : Fin o) : ℕ) = if j ≤ i then (i : ℕ) - j else o + i - j := by
  split_ifs with h
  · exact Fin.sub_val_of_le h
  · exact Fin.coe_sub_iff_lt.2 (not_le.1 h)

/-- Prefix sums of a rotation. -/
lemma e_rotate (w : Word) {j k : ℕ} (hj : j ≤ w.length) (hk : k ≤ w.length) :
    e (w.rotate j) k + e w j =
      if j + k ≤ w.length then e w (j + k) else w.sum + e w (j + k - w.length) := by
  unfold e
  rw [List.rotate_eq_drop_append_take hj, List.take_append, List.sum_append,
    List.length_drop]
  have h1 := List.sum_take_add_sum_drop (w.take (j + k)) j
  rw [List.take_take, Nat.min_eq_left (by omega), ← List.take_drop] at h1
  split_ifs with h
  · rw [show k - (w.length - j) = 0 by omega, List.take_zero, List.sum_nil, add_zero]
    omega
  · rw [List.take_of_length_le (by simp; omega), List.take_take,
      Nat.min_eq_left (by omega : k - (w.length - j) ≤ j),
      show j + k - w.length = k - (w.length - j) by omega]
    have h2 := List.sum_take_add_sum_drop w j
    omega

section Semiring
variable {R : Type*} [CommSemiring R] (X Y : R)

/-- **The rotation-sum matrix** `M_{j,i} = X^{e_i - e_j + E·[i<j]} Y^{o-1-((i-j) mod o)}`. -/
def Mrot (w : Word) : Matrix (Fin w.length) (Fin w.length) R :=
  Matrix.of fun j i => X ^ xExp w j i * Y ^ yExp j i

/-- The `k`-th prefix sum of the `j`-th rotation, as an `xExp`. -/
lemma e_rotate_eq_xExp (w : Word) (j k : Fin w.length) :
    e (w.rotate j) k = xExp w j (j + k : Fin w.length) := by
  have h1 := e_rotate w (j := j) (k := k) j.2.le k.2.le
  have h2 := xExp_add w j (j + k : Fin w.length)
  have hj := j.2
  have hk := k.2
  rw [Fin.val_add] at h2 ⊢
  rcases lt_or_ge (j + k : ℕ) w.length with h | h
  · rw [Nat.mod_eq_of_lt h] at h2 ⊢
    rw [ite_eq_left h.le] at h1
    rw [ite_eq_right (by omega), add_zero] at h2
    omega
  · have hm : (j + k : ℕ) % w.length = j + k - w.length := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hm] at h2 ⊢
    rw [ite_eq_left (by omega)] at h2
    split_ifs at h1 with h3
    · have : (j : ℕ) + k = w.length := by omega
      rw [this, e_length] at h1
      rw [this, Nat.sub_self, e_zero] at h2
      rw [this, Nat.sub_self]
      omega
    · omega

/-- **Row sums are the rotation sums** (`RATIONALE.md` (⋆)): `Σ_i M_{j,i} = S(w.rotate j)`. -/
theorem Mrot_rowSum (w : Word) (j : Fin w.length) :
    ∑ i, Mrot X Y w j i = S X Y (w.rotate j) := by
  have : NeZero w.length := ⟨Fin.pos j |>.ne'⟩
  rw [S_eq_sum, List.length_rotate, ← Fin.sum_univ_eq_sum_range
    (fun k => X ^ e (w.rotate j) k * Y ^ (w.length - 1 - k))]
  rw [← Equiv.sum_comp (Equiv.addLeft j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Mrot, Matrix.of_apply, Equiv.coe_addLeft, yExp, add_sub_cancel_left,
    e_rotate_eq_xExp]

/-- `M 𝟙 = S⃗`: the vector of rotation sums is the row-sum vector of `M`. -/
theorem Mrot_mulVec_one (w : Word) :
    Mrot X Y w *ᵥ (fun _ => 1) = fun j : Fin w.length => S X Y (w.rotate j) := by
  ext j; simp [Matrix.mulVec, dotProduct, Mrot_rowSum]

end Semiring

section Ring
variable {R : Type*} [CommRing R] (X Y : R)

/-- The word-free matrix `N_{j,i} = P^{[i<j]} Y^{o-1-((i-j) mod o)}`; at `P = X^E` it has the
same determinant as `M` (`det_Mrot_eq_det_N`). -/
def N (P : R) (o : ℕ) : Matrix (Fin o) (Fin o) R :=
  Matrix.of fun j i => (if i < j then P else 1) * Y ^ yExp j i

/-- **Leibniz reduction.** The factors `X^{e_i - e_j}` cancel along every permutation, so
`det M = det N(X^E)`. -/
theorem det_Mrot_eq_det_N (w : Word) : (Mrot X Y w).det = (N Y (X ^ w.sum) w.length).det := by
  rw [Matrix.det_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hite : ∀ i : Fin w.length, (if i < σ i then X ^ w.sum else 1) =
      X ^ (if (i : ℕ) < σ i then w.sum else 0) := fun i => by
    simp only [Fin.val_fin_lt]; split_ifs <;> simp
  simp only [Mrot, N, Matrix.of_apply, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hite]
  congr 2
  have h := Finset.sum_congr rfl fun (i : Fin w.length) (_ : i ∈ univ) => xExp_add w (σ i) i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Equiv.sum_comp σ (fun i : Fin w.length => e w i)] at h
  omega

/-- The lower-bidiagonal row-operation matrix: `R_{r} ↦ R_r - Y R_{r-1}`. -/
def L (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun r k => if r = k then 1 else if (r : ℕ) = k + 1 then -Y else 0

/-- `L` is unipotent lower triangular, so `det L = 1`. -/
lemma det_L (n : ℕ) : (L Y n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [L]
  · intro r k h
    have h' : r < k := h
    simp only [L, Matrix.of_apply]
    rw [ite_eq_right (by rintro rfl; exact lt_irrefl _ h'),
      ite_eq_right (by rw [Fin.lt_def] at h'; omega)]

/-- Row `0` of `L` is `e_0`. -/
lemma L_zero_apply (n : ℕ) (k : Fin (n + 1)) : L Y n 0 k = if 0 = k then 1 else 0 := by
  have h0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
  simp only [L, Matrix.of_apply]
  split_ifs <;> first | rfl | omega

/-- Row `r+1` of `L` is `e_{r+1} - Y e_r`. -/
lemma L_succ_apply (n : ℕ) (r : Fin n) (k : Fin (n + 1)) :
    L Y n r.succ k = (if r.succ = k then 1 else 0) + (if r.castSucc = k then -Y else 0) := by
  simp only [L, Matrix.of_apply, Fin.val_succ]
  by_cases h1 : r.succ = k
  · subst h1
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by simp [Fin.ext_iff])]; simp
  · rw [ite_eq_right h1, ite_eq_right h1, zero_add]
    by_cases h2 : r.castSucc = k
    · subst h2; simp
    · rw [ite_eq_right h2, ite_eq_right]
      intro h; exact h2 (Fin.ext (by simp; omega))

/-- `L` leaves row `0` unchanged. -/
lemma L_mul_zero (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (c : Fin (n + 1)) :
    (L Y n * B) 0 c = B 0 c := by
  simp [Matrix.mul_apply, L_zero_apply]

/-- `L` replaces row `r+1` by `R_{r+1} - Y R_r`. -/
lemma L_mul_succ (n : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : Fin n)
    (c : Fin (n + 1)) : (L Y n * B) r.succ c = B r.succ c - Y * B r.castSucc c := by
  simp only [Matrix.mul_apply, L_succ_apply, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- `o - 1 - ((i - j) mod o)` as a case split on `j ≤ i`. -/
lemma yExp_eq {o : ℕ} (j i : Fin o) :
    yExp j i = if (j : ℕ) ≤ i then o - 1 - (i - j) else j - i - 1 := by
  unfold yExp
  rw [val_sub_fin]
  simp only [Fin.le_def]
  split_ifs <;> omega

/-- Row `0` of `N` is `(Y^{o-1}, …, Y, 1)`. -/
lemma N_zero (P : R) (n : ℕ) (c : Fin (n + 1)) : N Y P (n + 1) 0 c = Y ^ (n - c) := by
  simp only [N, Matrix.of_apply, yExp_eq, Fin.val_zero, Nat.zero_le, ite_true,
    Fin.not_lt_zero, ite_false, one_mul, Nat.sub_zero, Nat.add_sub_cancel]

/-- The row relation `R_{r+1} - Y R_r = (P - Y^o) e_r` of `N`. -/
lemma N_succ_sub (P : R) (n : ℕ) (r : Fin n) (c : Fin (n + 1)) :
    N Y P (n + 1) r.succ c - Y * N Y P (n + 1) r.castSucc c =
      if c = r.castSucc then P - Y ^ (n + 1) else 0 := by
  simp only [N, Matrix.of_apply, yExp_eq, Fin.lt_def, Fin.val_succ, Fin.val_castSucc,
    Fin.ext_iff]
  rcases lt_trichotomy (c : ℕ) r with h | h | h
  · simp only [show (c : ℕ) < r + 1 by omega, show ¬ ((r : ℕ) + 1 ≤ c) by omega, h,
      show ¬ ((r : ℕ) ≤ c) by omega, show (c : ℕ) ≠ r by omega, ite_true, ite_false]
    generalize ha : (r : ℕ) + 1 - c - 1 = a
    generalize hb : (r : ℕ) - c - 1 = b
    rw [show a = b + 1 by omega, pow_succ]; ring
  · simp only [h, lt_add_one, le_refl, lt_irrefl, Nat.not_succ_le_self, ite_true, ite_false]
    rw [show (r : ℕ) + 1 - r - 1 = 0 by omega, show n + 1 - 1 - (r - r) = n by omega]
    ring
  · have hc := c.2
    simp only [show ¬ ((c : ℕ) < r + 1) by omega, show (r : ℕ) + 1 ≤ c by omega,
      show ¬ ((c : ℕ) < r) by omega, show (r : ℕ) ≤ c by omega, show (c : ℕ) ≠ r by omega,
      ite_true, ite_false]
    generalize ha : n + 1 - 1 - ((c : ℕ) - (r + 1)) = a
    generalize hb : n + 1 - 1 - ((c : ℕ) - r) = b
    rw [show a = b + 1 by omega, pow_succ]; ring

/-- `det N = (-1)^{o+1} (P - Y^o)^{o-1}` for `o ≥ 1` (row reduction `R_{j+1} - Y R_j = D e_j`). -/
theorem det_N (P : R) (o : ℕ) (ho : 0 < o) :
    (N Y P o).det = (-1) ^ (o + 1) * (P - Y ^ o) ^ (o - 1) := by
  cases o with
  | zero => exact absurd ho (lt_irrefl 0)
  | succ n =>
    have hT : (N Y P (n + 1)).det = (L Y n * N Y P (n + 1)).det := by
      rw [Matrix.det_mul, det_L, one_mul]
    rw [hT, Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_succ]
    have hrest : ∀ r : Fin n, (L Y n * N Y P (n + 1)) r.succ (Fin.last n) = 0 := fun r => by
      rw [L_mul_succ, N_succ_sub, ite_eq_right]
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp only [hrest, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, L_mul_zero, N_zero,
      Fin.val_last, Nat.sub_self, pow_zero, mul_one, Fin.val_zero, Fin.succAbove_zero,
      Fin.succAbove_last]
    have hsub : (L Y n * N Y P (n + 1)).submatrix Fin.succ Fin.castSucc =
        (P - Y ^ (n + 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext r c
      simp only [Matrix.submatrix_apply, L_mul_succ, N_succ_sub, Fin.castSucc_inj,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp only [eq_comm]
    rw [hsub, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, zero_add,
      Nat.add_sub_cancel]
    ring

/-- **Determinant.** `det M = (-1)^{o+1} D^{o-1}` for every nonempty word. -/
theorem det_Mrot (w : Word) (hw : w ≠ []) :
    (Mrot X Y w).det = (-1) ^ (w.length + 1) * D X Y w ^ (w.length - 1) := by
  rw [det_Mrot_eq_det_N, det_N _ _ _ (List.length_pos_of_ne_nil hw), D]

/-- The note's test word `(E, o) = (8, 5)`: `det M = 13^4 = 28561`. -/
example : (Mrot (2 : ℤ) 3 [1, 1, 2, 2, 2]).det = 13 ^ 4 := by
  rw [det_Mrot _ _ _ (by simp)]; simp [D]

/-- **Cofactor certificate** (Identity C): `adj(M) S⃗ = (-1)^{o+1} D^{o-1} 𝟙`. -/
theorem adjugate_mulVec_S (w : Word) (hw : w ≠ []) :
    (Mrot X Y w).adjugate *ᵥ (fun j : Fin w.length => S X Y (w.rotate j)) =
      fun _ => (-1) ^ (w.length + 1) * D X Y w ^ (w.length - 1) := by
  rw [← Mrot_mulVec_one, Matrix.mulVec_mulVec, Matrix.adjugate_mul, det_Mrot X Y w hw]
  ext j; simp [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- A common divisor of all rotation sums divides `D^{o-1}` (Identity C). -/
theorem dvd_D_pow_of_dvd_S (w : Word) (hw : w ≠ []) (d : R)
    (hd : ∀ j : Fin w.length, d ∣ S X Y (w.rotate j)) : d ∣ D X Y w ^ (w.length - 1) := by
  have h0 : 0 < w.length := List.length_pos_of_ne_nil hw
  have h := congrFun (adjugate_mulVec_S X Y w hw) ⟨0, h0⟩
  rw [Matrix.mulVec, dotProduct] at h
  have : d ∣ (-1) ^ (w.length + 1) * D X Y w ^ (w.length - 1) :=
    h ▸ Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hd i) _
  rcases neg_one_pow_eq_or R (w.length + 1) with h1 | h1 <;> simpa [h1] using this

/-- **Leibniz form** (Identity D): `Σ_σ sgn σ ∏_j M_{j,σ j} = (-1)^{o+1} D^{o-1}`. -/
theorem leibniz_Mrot (w : Word) (hw : w ≠ []) :
    ∑ σ : Equiv.Perm (Fin w.length), (Equiv.Perm.sign σ : R) * ∏ j, Mrot X Y w j (σ j) =
      (-1) ^ (w.length + 1) * D X Y w ^ (w.length - 1) := by
  rw [← det_Mrot X Y w hw, ← Matrix.det_transpose, Matrix.det_apply']
  rfl

end Ring

/-! ## The real form `M = Δ⁻¹ C Δ` -/

section Real

/-- Detrended prefix sums `ẽ_k = e_k - kE/o`. -/
noncomputable def etilde (w : Word) (k : ℕ) : ℝ := e w k - k * w.sum / w.length

/-- `Δ = diag(2^{ẽ_k})`. -/
noncomputable def Δ (w : Word) : Matrix (Fin w.length) (Fin w.length) ℝ :=
  Matrix.diagonal fun k => (2 : ℝ) ^ etilde w k

/-- `Δ⁻¹ = diag(2^{-ẽ_k})`. -/
noncomputable def Δinv (w : Word) : Matrix (Fin w.length) (Fin w.length) ℝ :=
  Matrix.diagonal fun k => (2 : ℝ) ^ (-etilde w k)

/-- The circulant `C_{j,i} = c_{(i-j) mod o}` with symbol `c`. -/
def circ {K : Type*} (o : ℕ) (c : ℕ → K) : Matrix (Fin o) (Fin o) K :=
  Matrix.of fun j i => c (i - j : Fin o)

/-- The symbol `c_r = 2^{rE/o} 3^{o-1-r}`. -/
noncomputable def csym (w : Word) (r : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r : ℝ) * w.sum / w.length) * 3 ^ (w.length - 1 - r)

/-- `Δ⁻¹ Δ = 1`. -/
lemma Δinv_mul_Δ (w : Word) : Δinv w * Δ w = 1 := by
  rw [Δinv, Δ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext k
  rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]

/-- `Δ Δ⁻¹ = 1`. -/
lemma Δ_mul_Δinv (w : Word) : Δ w * Δinv w = 1 := by
  rw [Δinv, Δ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext k
  rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]

/-- **Circulant factorisation** (`RATIONALE.md` Step 2): at `(2,3)`, `M = Δ⁻¹ C Δ`. -/
theorem Mrot_eq_conj (w : Word) : Mrot (2 : ℝ) 3 w = Δinv w * circ w.length (csym w) * Δ w := by
  ext j i
  have hpos : (0 : ℝ) < w.length := by exact_mod_cast Fin.pos j
  simp only [Δinv, Δ, circ, csym, Mrot, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
    yExp]
  rw [mul_comm ((2 : ℝ) ^ _ ) (_ * _), mul_assoc, mul_assoc, mul_comm ((3 : ℝ) ^ _),
    ← mul_assoc ((2 : ℝ) ^ _), ← mul_assoc ((2 : ℝ) ^ _), ← Real.rpow_add two_pos,
    ← Real.rpow_add two_pos, ← Real.rpow_natCast]
  congr 2
  have hx := xExp_add w j i
  have hs := val_sub_fin i j
  simp only [etilde]
  split_ifs at hx hs with h1 h2 h2
  · exfalso; rw [Fin.le_def] at h2; omega
  · have : (xExp w j i : ℝ) = e w i + w.sum - e w j := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hx
    rw [this, hs, Nat.cast_sub (by omega), Nat.cast_add]
    field_simp; ring
  · have : (xExp w j i : ℝ) = e w i - e w j := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : xExp w j i + e w j = e w i)
    rw [this, hs, Nat.cast_sub (by rw [Fin.le_def] at h2; omega)]
    field_simp; ring
  · exfalso; rw [Fin.le_def] at h2; omega

/-- `det C = det M = (-1)^{o+1} (2^E - 3^o)^{o-1}` over `ℝ`. -/
theorem det_circ_real (w : Word) (hw : w ≠ []) :
    (circ w.length (csym w)).det =
      (-1) ^ (w.length + 1) * ((2 : ℝ) ^ w.sum - 3 ^ w.length) ^ (w.length - 1) := by
  have h := det_Mrot (2 : ℝ) 3 w hw
  rw [Mrot_eq_conj, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    Δ_mul_Δinv, Matrix.det_one, one_mul] at h
  rw [h, D]

end Real

/-! ## Roots of unity: Identity A, the circuit factorisation, the spectrum -/

section RootsOfUnity

/-- `x^n - y^n = ∏_{m<n} (x - ζ^m y)` in a domain with a primitive `n`-th root of unity `ζ`.
(The domain hypothesis is needed: in `ℤ/8ℤ`, `ζ = 3` is a primitive square root of `1` but
`(0 - 1)(0 - 3) = 3 ≠ 7 = 0^2 - 1^2`.) -/
theorem pow_sub_pow_eq_prod {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (x y : K) :
    x ^ n - y ^ n = ∏ m ∈ range n, (x - ζ ^ m * y) := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [hζ.pow_sub_pow_eq_prod_sub_mul x y hn]
  symm
  refine Finset.prod_bij (fun m _ => ζ ^ m) (fun m _ => ?_) (fun a ha b hb h => ?_)
    (fun η hη => ?_) (fun _ _ => rfl)
  · rw [Polynomial.mem_nthRootsFinset hn, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · exact hζ.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  · obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hη)
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩

/-- `ζ_g = e^{2πi/g}`. -/
noncomputable def zeta (g : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / g)

/-- `ζ_g` is a primitive `g`-th root of unity. -/
lemma isPrimitiveRoot_zeta {g : ℕ} (hg : 0 < g) : IsPrimitiveRoot (zeta g) g :=
  Complex.isPrimitiveRoot_exp g hg.ne'

/-- **Circuit factorisation** (`circuits.md` §2), as a `ℤ[X,Y]`-identity over any domain with a
primitive `g`-th root of unity, `g = gcd(E, o)`, `a = E/g`, `b = o/g`:
`D = X^E - Y^o = ∏_{m<g} (X^a - ζ^m Y^b)`. -/
theorem D_eq_prod_circuits {K : Type*} [CommRing K] [IsDomain K] (X Y : K) (w : Word)
    (hw : w ≠ []) {ζ : K} (hζ : IsPrimitiveRoot ζ (Nat.gcd w.sum w.length)) :
    D X Y w = ∏ m ∈ range (Nat.gcd w.sum w.length),
      (X ^ (w.sum / Nat.gcd w.sum w.length) - ζ ^ m * Y ^ (w.length / Nat.gcd w.sum w.length)) := by
  have hg : 0 < Nat.gcd w.sum w.length := Nat.gcd_pos_of_pos_right _ (List.length_pos_of_ne_nil hw)
  rw [← pow_sub_pow_eq_prod hg hζ, ← pow_mul, ← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), D]

/-- The circuit factorisation at `(2,3)` over `ℂ`: `2^E - 3^o = ∏_{m<g} (2^a - 3^b ζ_g^m)`. -/
theorem Dz_eq_prod_circuits (w : Word) (hw : w ≠ []) :
    (Dz w : ℂ) = ∏ m ∈ range (Nat.gcd w.sum w.length),
      ((2 : ℂ) ^ (w.sum / Nat.gcd w.sum w.length) -
        3 ^ (w.length / Nat.gcd w.sum w.length) * zeta (Nat.gcd w.sum w.length) ^ m) := by
  have hg : 0 < Nat.gcd w.sum w.length := Nat.gcd_pos_of_pos_right _ (List.length_pos_of_ne_nil hw)
  have := D_eq_prod_circuits (2 : ℂ) 3 w hw (isPrimitiveRoot_zeta hg)
  simp only [D] at this ⊢
  push_cast
  rw [this]
  refine Finset.prod_congr rfl fun m _ => by ring

/-- The polynomial circuit splitting `x^o - 2^E = ∏_{m<g} (x^b - 2^a ζ_g^m)` in `ℂ[x]`. -/
theorem X_pow_sub_eq_prod_circuits (E o : ℕ) (ho : 0 < o) :
    (Polynomial.X ^ o - Polynomial.C ((2 : ℂ) ^ E) : Polynomial ℂ) =
      ∏ m ∈ range (Nat.gcd E o), (Polynomial.X ^ (o / Nat.gcd E o) -
        Polynomial.C ((2 : ℂ) ^ (E / Nat.gcd E o) * zeta (Nat.gcd E o) ^ m)) := by
  have hg : 0 < Nat.gcd E o := Nat.gcd_pos_of_pos_right _ ho
  have hζ := (isPrimitiveRoot_zeta hg).map_of_injective (f := Polynomial.C) Polynomial.C_injective
  rw [show (2 : ℂ) ^ E = ((2 : ℂ) ^ (E / Nat.gcd E o)) ^ Nat.gcd E o by
      rw [← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)],
    show (Polynomial.X : Polynomial ℂ) ^ o = (Polynomial.X ^ (o / Nat.gcd E o)) ^ Nat.gcd E o by
      rw [← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)],
    Polynomial.C_pow, pow_sub_pow_eq_prod hg hζ]
  refine Finset.prod_congr rfl fun m _ => ?_
  simp only [map_mul, map_pow]; ring

end RootsOfUnity

/-! ## The spectrum of `C` over `ℂ` -/

section Spectrum

/-- `β = 2^{E/o}`. -/
noncomputable def beta (w : Word) : ℝ := (2 : ℝ) ^ ((w.sum : ℝ) / w.length)

/-- `β^o = 2^E`. -/
lemma beta_pow (w : Word) (hw : w ≠ []) : beta w ^ w.length = 2 ^ w.sum := by
  have ho : (w.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_of_ne_nil hw).ne'
  rw [beta, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), div_mul_cancel₀ _ ho,
    Real.rpow_natCast]

/-- `c_r = β^r 3^{o-1-r}`. -/
lemma csym_eq (w : Word) (r : ℕ) : csym w r = beta w ^ r * 3 ^ (w.length - 1 - r) := by
  rw [csym, beta]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring_nf

/-- The Fourier vector `v_ℓ = (ω^{ℓ k})_k`. -/
def dftVec {K : Type*} [Monoid K] (o : ℕ) (ω : K) (ℓ : ℕ) : Fin o → K := fun k => ω ^ (ℓ * k)

/-- Every circulant is diagonalised by the Fourier vectors: if `ω^o = 1` then
`C v_ℓ = ĉ_ℓ v_ℓ` with `ĉ_ℓ = Σ_{r<o} c_r ω^{rℓ}`. -/
theorem circ_mulVec_dftVec {K : Type*} [CommRing K] (o : ℕ) (c : ℕ → K) {ω : K}
    (hω : ω ^ o = 1) (ℓ : ℕ) :
    circ o c *ᵥ dftVec o ω ℓ = (∑ r ∈ range o, c r * ω ^ (r * ℓ)) • dftVec o ω ℓ := by
  ext j
  have : NeZero o := ⟨(Fin.pos j).ne'⟩
  have hmod : ∀ n, ω ^ (ℓ * (n % o)) = ω ^ (ℓ * n) := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n o]
    rw [mul_add, pow_add, show ℓ * (o * (n / o)) = o * (ℓ * (n / o)) by ring, pow_mul ω o, hω,
      one_pow, mul_one]
  simp only [Matrix.mulVec, dotProduct, circ, dftVec, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [← Equiv.sum_comp (Equiv.addLeft j), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, Fin.val_add, hmod]
  rw [mul_add, pow_add]; ring

/-- The eigenvalue telescopes: `ĉ_ℓ (β ω^ℓ - Y) = β^o - Y^o` for the symbol
`c_r = β^r Y^{o-1-r}`. -/
theorem eigenvalue_mul {K : Type*} [CommRing K] (o : ℕ) (β Y : K) {ω : K} (hω : ω ^ o = 1)
    (ℓ : ℕ) : (∑ r ∈ range o, β ^ r * Y ^ (o - 1 - r) * ω ^ (r * ℓ)) * (β * ω ^ ℓ - Y) =
      β ^ o - Y ^ o := by
  have h := geom_sum₂_mul (β * ω ^ ℓ) Y o
  rw [mul_pow, ← pow_mul, mul_comm ℓ o, pow_mul, hω, one_pow, mul_one] at h
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm ℓ r]; ring

/-- `β ω^ℓ ≠ 3`, since otherwise `2^E = 3^o`. -/
lemma beta_mul_zeta_ne_three (w : Word) (hw : w ≠ []) (ℓ : ℕ) :
    (beta w : ℂ) * zeta w.length ^ ℓ ≠ 3 := by
  have ho := List.length_pos_of_ne_nil hw
  intro h
  have h1 : ((beta w : ℂ) * zeta w.length ^ ℓ) ^ w.length = 3 ^ w.length := by rw [h]
  rw [mul_pow, ← pow_mul, mul_comm ℓ, pow_mul, (isPrimitiveRoot_zeta ho).pow_eq_one, one_pow,
    mul_one, ← Complex.ofReal_pow, beta_pow w hw] at h1
  have h2 : (2 : ℕ) ^ w.sum = 3 ^ w.length := by exact_mod_cast h1
  rcases Nat.eq_zero_or_pos w.sum with h0 | h0
  · rw [h0, pow_zero] at h2
    have := Nat.one_lt_pow ho.ne' (by norm_num : 1 < 3); omega
  · have : 2 ∣ 3 ^ w.length := h2 ▸ dvd_pow_self 2 h0.ne'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this) (by norm_num)

/-- **Spectrum** (`RATIONALE.md` 1): `C v_ℓ = ĉ_ℓ v_ℓ` with `ĉ_ℓ = D/(β ω^ℓ - 3)`,
`β = 2^{E/o}`, `ω = e^{2πi/o}`, `v_ℓ = (ω^{ℓk})_k`. -/
theorem circ_spectrum (w : Word) (hw : w ≠ []) (ℓ : ℕ) :
    (circ w.length (csym w)).map ((↑) : ℝ → ℂ) *ᵥ dftVec w.length (zeta w.length) ℓ =
      ((Dz w : ℂ) / ((beta w : ℂ) * zeta w.length ^ ℓ - 3)) •
        dftVec w.length (zeta w.length) ℓ := by
  have ho := List.length_pos_of_ne_nil hw
  have hω := (isPrimitiveRoot_zeta ho).pow_eq_one
  have hC : (circ w.length (csym w)).map ((↑) : ℝ → ℂ) =
      circ w.length (fun r => (beta w : ℂ) ^ r * 3 ^ (w.length - 1 - r)) := by
    ext j i; simp [circ, csym_eq]
  rw [hC, circ_mulVec_dftVec _ _ hω]
  congr 1
  rw [eq_div_iff (sub_ne_zero.2 (beta_mul_zeta_ne_three w hw ℓ)), eigenvalue_mul _ _ _ hω,
    ← Complex.ofReal_pow, beta_pow w hw]
  simp [D]
/-- **(1b) Root-of-unity product**: `∏_{ℓ<o} (3 - β ω^ℓ) = 3^o - 2^E`. -/
theorem prod_three_sub (w : Word) (hw : w ≠ []) :
    ∏ ℓ ∈ range w.length, ((3 : ℂ) - beta w * zeta w.length ^ ℓ) = 3 ^ w.length - 2 ^ w.sum := by
  have ho := List.length_pos_of_ne_nil hw
  rw [show (2 : ℂ) ^ w.sum = ((beta w : ℂ)) ^ w.length by
      rw [← Complex.ofReal_pow, beta_pow w hw]; push_cast; rfl,
    pow_sub_pow_eq_prod ho (isPrimitiveRoot_zeta ho)]
  exact Finset.prod_congr rfl fun ℓ _ => by ring

/-- **Identity A**: `|2^E - 3^o| = ∏_{ℓ<o} |3 - 2^{E/o} ω^ℓ|`. -/
theorem identityA (w : Word) (hw : w ≠ []) :
    |(2 : ℝ) ^ w.sum - 3 ^ w.length| =
      ∏ ℓ ∈ range w.length, ‖(3 : ℂ) - beta w * zeta w.length ^ ℓ‖ := by
  rw [← norm_prod, prod_three_sub w hw, abs_sub_comm, ← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast; rfl

/-- **(1a) Spectral determinant**: `det C = ∏_ℓ ĉ_ℓ = ∏_ℓ D/(β ω^ℓ - 3)` (the Fourier vectors
form an invertible Vandermonde matrix). -/
theorem det_circ_eq_prod (w : Word) (hw : w ≠ []) :
    ((circ w.length (csym w)).map ((↑) : ℝ → ℂ)).det =
      ∏ ℓ : Fin w.length, (Dz w : ℂ) / ((beta w : ℂ) * zeta w.length ^ (ℓ : ℕ) - 3) := by
  have ho := List.length_pos_of_ne_nil hw
  set C' := (circ w.length (csym w)).map ((↑) : ℝ → ℂ)
  set V := (Matrix.vandermonde fun ℓ : Fin w.length => zeta w.length ^ (ℓ : ℕ))ᵀ
  set c : Fin w.length → ℂ := fun ℓ => (Dz w : ℂ) / ((beta w : ℂ) * zeta w.length ^ (ℓ : ℕ) - 3)
  have key : C' * V = V * Matrix.diagonal c := by
    ext j ℓ
    have h := congrFun (circ_spectrum w hw ℓ) j
    simp only [Matrix.mulVec, dotProduct, dftVec, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [V, c, Matrix.transpose_apply, Matrix.vandermonde_apply, ← pow_mul]
    rw [h, mul_comm]
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_transpose]
    refine Matrix.det_vandermonde_ne_zero_iff.2 fun a b hab => Fin.ext ?_
    exact (isPrimitiveRoot_zeta ho).pow_inj a.2 b.2 hab
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm V.det] at h
  exact mul_right_cancel₀ hV h

end Spectrum

/-! ## The étale algebra `A = ℚ[x]/(x^o - 2^E)`: norms -/

section NumberField

open Polynomial

/-- For monic `f` over a field, `N_{K[x]/(f) / K}(x̂ - t) = (-1)^{deg f} f(t)`. -/
theorem norm_root_sub {K : Type*} [Field K] {f : K[X]} (hf : f.Monic) (t : K) :
    Algebra.norm K (AdjoinRoot.root f - algebraMap K (AdjoinRoot f) t) =
      (-1) ^ f.natDegree * f.eval t := by
  set pb := AdjoinRoot.powerBasis hf.ne_zero
  have hc : (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = f := by
    rw [_root_.charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hf]
  rw [Algebra.norm_eq_matrix_det pb.basis, map_sub, AlgHom.commutes,
    show AdjoinRoot.root f = pb.gen from rfl,
    ← neg_sub, Matrix.det_neg, Fintype.card_fin, ← AdjoinRoot.powerBasis_dim hf.ne_zero,
    ← congrArg (Polynomial.eval t) hc, Matrix.eval_charpoly, Matrix.scalar_apply,
    Matrix.algebraMap_eq_diagonal]
  rfl

/-- `N(x̂ - t) = (-1)^n (t^n - c)` in `K[x]/(x^n - c)`. -/
theorem norm_root_X_pow_sub_C_sub {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) (c t : K) :
    Algebra.norm K (AdjoinRoot.root (X ^ n - C c) - algebraMap K (AdjoinRoot (X ^ n - C c)) t) =
      (-1) ^ n * (t ^ n - c) := by
  rw [norm_root_sub (monic_X_pow_sub_C c hn.ne'), natDegree_X_pow_sub_C]; simp

/-- The étale algebra `A = ℚ[x]/(x^o - 2^E)` of a word (a field iff `gcd(E, o) = 1`). -/
abbrev Alg (w : Word) : Type := AdjoinRoot (X ^ w.length - C ((2 : ℚ) ^ w.sum))

/-- `x̂`, the class of `x` in `A`. -/
noncomputable abbrev xhat (w : Word) : Alg w := AdjoinRoot.root _

/-- `x̂^o = 2^E` in `A`. -/
lemma xhat_pow (w : Word) : xhat w ^ w.length = algebraMap ℚ (Alg w) (2 ^ w.sum) := by
  have := AdjoinRoot.eval₂_root (X ^ w.length - C ((2 : ℚ) ^ w.sum))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this
  exact sub_eq_zero.1 this

/-- `dim_ℚ A = o`. -/
lemma finrank_Alg (w : Word) (hw : w ≠ []) : Module.finrank ℚ (Alg w) = w.length := by
  rw [(AdjoinRoot.powerBasis (monic_X_pow_sub_C ((2 : ℚ) ^ w.sum)
    (List.length_pos_of_ne_nil hw).ne').ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

/-- `2^E ≠ 3^o` for `o ≥ 1`. -/
lemma two_pow_ne_three_pow {E o : ℕ} (ho : 0 < o) : 2 ^ E ≠ 3 ^ o := by
  intro h2
  rcases Nat.eq_zero_or_pos E with h0 | h0
  · rw [h0, pow_zero] at h2
    have := Nat.one_lt_pow ho.ne' (by norm_num : 1 < 3); omega
  · have : 2 ∣ 3 ^ o := h2 ▸ dvd_pow_self 2 h0.ne'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this) (by norm_num)

/-- `D ≠ 0` for every nonempty word. -/
lemma Dz_ne_zero (w : Word) (hw : w ≠ []) : Dz w ≠ 0 := by
  have := two_pow_ne_three_pow (E := w.sum) (List.length_pos_of_ne_nil hw)
  simp only [Dz, D, sub_ne_zero]; exact_mod_cast this

/-- **`D` is a norm** (`number_field.md` §2, in the étale form of `circuits.md` §1):
`N_{A/ℚ}(x̂ - 3) = (-1)^{o+1} D`. -/
theorem norm_xhat_sub_three (w : Word) (hw : w ≠ []) :
    Algebra.norm ℚ (xhat w - 3) = (-1) ^ (w.length + 1) * (Dz w : ℚ) := by
  have h := norm_root_X_pow_sub_C_sub (List.length_pos_of_ne_nil hw) ((2 : ℚ) ^ w.sum) 3
  rw [map_ofNat] at h
  rw [h, pow_succ]; simp [D]; ring

/-- `ĉ_0 = Σ_{k<o} 3^{o-1-k} x̂^k ∈ ℤ[x̂]`. -/
noncomputable def chat0 (w : Word) : Alg w :=
  ∑ k ∈ range w.length, 3 ^ (w.length - 1 - k) * xhat w ^ k

/-- `ĉ_0 (x̂ - 3) = D`, i.e. `ĉ_0 = D/(x̂ - 3)`. -/
theorem chat0_mul (w : Word) : chat0 w * (xhat w - 3) = algebraMap ℚ (Alg w) (Dz w) := by
  rw [chat0, show (∑ k ∈ range w.length, 3 ^ (w.length - 1 - k) * xhat w ^ k) =
      ∑ k ∈ range w.length, xhat w ^ k * 3 ^ (w.length - 1 - k) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, geom_sum₂_mul, xhat_pow]
  simp only [Dz, D, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, map_sub, map_pow, map_ofNat]

/-- **`det M` is a norm** (`number_field.md` §3): `N_{A/ℚ}(ĉ_0) = (-1)^{o+1} D^{o-1}`. -/
theorem norm_chat0 (w : Word) (hw : w ≠ []) :
    Algebra.norm ℚ (chat0 w) = (-1) ^ (w.length + 1) * (Dz w : ℚ) ^ (w.length - 1) := by
  have ho := List.length_pos_of_ne_nil hw
  have h := congrArg (Algebra.norm ℚ) (chat0_mul w)
  rw [map_mul, norm_xhat_sub_three w hw, Algebra.norm_algebraMap, finrank_Alg w hw] at h
  have hD : (Dz w : ℚ) ≠ 0 := by exact_mod_cast Dz_ne_zero w hw
  have hu : ((-1 : ℚ) ^ (w.length + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hD)
  rw [h]
  obtain ⟨n, hn⟩ : ∃ n, w.length = n + 1 := ⟨w.length - 1, by omega⟩
  rw [hn] at hu ⊢
  rw [Nat.add_sub_cancel]
  linear_combination (-(Dz w : ℚ) ^ (n + 1)) * hu

/-- `det M = N_{A/ℚ}(ĉ_0)` at `(2, 3)`. -/
theorem det_Mrot_eq_norm (w : Word) (hw : w ≠ []) :
    (Mrot (2 : ℚ) 3 w).det = Algebra.norm ℚ (chat0 w) := by
  rw [det_Mrot _ _ w hw, norm_chat0 w hw]; simp [D]

/-- The principal real circuit `K = ℚ[x]/(x^b - 2^a)`: `N_{K/ℚ}(x̂ - 3) = (-1)^b (3^b - 2^a)`. -/
theorem norm_principal_circuit (a b : ℕ) (hb : 0 < b) :
    Algebra.norm ℚ (AdjoinRoot.root (X ^ b - C ((2 : ℚ) ^ a)) - 3) =
      (-1) ^ b * ((3 : ℚ) ^ b - 2 ^ a) := by
  have h := norm_root_X_pow_sub_C_sub hb ((2 : ℚ) ^ a) 3
  rwa [map_ofNat] at h

end NumberField

/-! ## The gcd law (`number_field.md` §7, `gamma_w.md` §0) -/

section GcdLaw

/-- `D` is odd when `E ≥ 1`. -/
lemma not_two_dvd_Dz (w : Word) (hE : 0 < w.sum) : ¬ (2 : ℤ) ∣ Dz w := by
  intro h
  have h2 : (2 : ℤ) ∣ 3 ^ w.length := by
    have : (3 : ℤ) ^ w.length = 2 ^ w.sum - Dz w := by simp [D]
    rw [this]; exact dvd_sub (dvd_pow_self 2 hE.ne') h
  exact absurd (Int.prime_two.dvd_of_dvd_pow h2) (by norm_num)

/-- `3 ∤ D` when `o ≥ 1`. -/
lemma not_three_dvd_Dz (w : Word) (hw : w ≠ []) : ¬ (3 : ℤ) ∣ Dz w := by
  intro h
  have h3 : (3 : ℤ) ∣ 2 ^ w.sum := by
    have : (2 : ℤ) ^ w.sum = Dz w + 3 ^ w.length := by simp [D]
    rw [this]; exact dvd_add h (dvd_pow_self 3 (List.length_pos_of_ne_nil hw).ne')
  exact absurd (Int.prime_three.dvd_of_dvd_pow h3) (by norm_num)

/-- `gcd(2^k, D) = 1` when `E ≥ 1`. -/
lemma gcd_two_pow_Dz (w : Word) (hE : 0 < w.sum) (k : ℕ) : Int.gcd (2 ^ k) (Dz w) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.1
    ((Int.prime_two.coprime_iff_not_dvd.2 (not_two_dvd_Dz w hE)).pow_left)

/-- `gcd(3, D) = 1` when `o ≥ 1`. -/
lemma gcd_three_Dz (w : Word) (hw : w ≠ []) : Int.gcd 3 (Dz w) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.1 (Int.prime_three.coprime_iff_not_dvd.2 (not_three_dvd_Dz w hw))

/-- One rotation step preserves `gcd(S, D)` (since `D` is prime to `6`). -/
lemma gcd_S_rotate_one (u : Word) (hE : 0 < u.sum) (hu : u ≠ []) :
    Int.gcd (Sz (u.rotate 1)) (Dz u) = Int.gcd (Sz u) (Dz u) := by
  obtain ⟨d, u', rfl⟩ := List.exists_cons_of_ne_nil hu
  have h := rotation_recursion (2 : ℤ) 3 d u'
  rw [rotate_one_cons, ← Int.gcd_mul_right_left_of_gcd_eq_one (gcd_two_pow_Dz _ hE d), h,
    Int.gcd_add_self_left, Int.gcd_mul_right_left_of_gcd_eq_one (gcd_three_Dz _ hu)]

/-- **Rotation collapse** (`gamma_w.md` §0): `gcd(S^{(j)}, D)` does not depend on `j`. -/
theorem gcd_S_rotate (w : Word) (hE : 0 < w.sum) (hw : w ≠ []) (j : ℕ) :
    Int.gcd (Sz (w.rotate j)) (Dz w) = Int.gcd (Sz w) (Dz w) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs : (w.rotate j).sum = w.sum := (List.rotate_perm w j).sum_eq
    have hD : Dz (w.rotate j) = Dz w := D_rotate _ _ w j
    rw [← List.rotate_rotate, ← ih, ← hD]
    exact gcd_S_rotate_one _ (hs ▸ hE) (by simpa using hw)

/-- `gcd_j S^{(j)}` (as a natural number). -/
def gcdRot (w : Word) : ℕ := (range w.length).gcd fun j => (Sz (w.rotate j)).natAbs

/-- `gcd_j S^{(j)} = gcd(S^{(0)}, D)`: only one rotation matters. -/
theorem gcdRot_eq (w : Word) (hE : 0 < w.sum) (hw : w ≠ []) :
    gcdRot w = Int.gcd (Sz w) (Dz w) := by
  have ho := List.length_pos_of_ne_nil hw
  apply Nat.dvd_antisymm
  · obtain ⟨d, u', rfl⟩ := List.exists_cons_of_ne_nil hw
    have h0 : gcdRot (d :: u') ∣ (Sz ((d :: u').rotate 0)).natAbs :=
      Finset.gcd_dvd (Finset.mem_range.2 ho)
    have h1 : gcdRot (d :: u') ∣ (Sz ((d :: u').rotate (1 % (d :: u').length))).natAbs :=
      Finset.gcd_dvd (Finset.mem_range.2 (Nat.mod_lt _ ho))
    rw [List.rotate_zero] at h0
    rw [List.rotate_mod, rotate_one_cons] at h1
    have hD : (gcdRot (d :: u') : ℤ) ∣ Dz (d :: u') := by
      have h := rotation_recursion (2 : ℤ) 3 d u'
      rw [show Dz (d :: u') = 2 ^ d * Sz (u' ++ [d]) - 3 * Sz (d :: u') by
        simp only [Sz, Dz]; rw [h]; ring]
      exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd.2 h1) _)
        (dvd_mul_of_dvd_right (Int.natCast_dvd.2 h0) _)
    exact Nat.dvd_gcd h0 (Int.natCast_dvd.1 hD)
  · refine Finset.dvd_gcd fun j _ => ?_
    rw [← gcd_S_rotate w hE hw j]
    exact Nat.gcd_dvd_left _ _

/-- The trace part `T_j = 2^{e_j} S^{(j)} / D ∈ ℚ` (`number_field.md` §7). -/
noncomputable def T (w : Word) (j : ℕ) : ℚ := ((2 ^ e w j * Sz (w.rotate j) : ℤ) : ℚ) / (Dz w : ℚ)

/-- `δ_j`, the denominator of `T_j`. -/
noncomputable def delta (w : Word) (j : ℕ) : ℕ := (T w j).den

/-- `δ_j = |D| / gcd(S^{(j)}, D)` (`D` is odd, so the `2^{e_j}` is invisible). -/
theorem delta_eq (w : Word) (hE : 0 < w.sum) (hw : w ≠ []) (j : ℕ) :
    delta w j = (Dz w).natAbs / Int.gcd (Sz (w.rotate j)) (Dz w) := by
  rw [delta, T, ← Rat.divInt_eq_div, Rat.den_divInt, ite_eq_right (Dz_ne_zero w hw), Int.gcd_comm,
    Int.gcd_mul_right_left_of_gcd_eq_one (gcd_two_pow_Dz w hE _), Int.gcd_comm]

/-- **The gcd law** (`number_field.md` §7): `gcd_j S^{(j)} = |D| / lcm_j δ_j`. -/
theorem gcd_law (w : Word) (hE : 0 < w.sum) (hw : w ≠ []) :
    gcdRot w = (Dz w).natAbs / (range w.length).lcm (delta w) := by
  have ho := List.length_pos_of_ne_nil hw
  have hδ : ∀ j, delta w j = (Dz w).natAbs / Int.gcd (Sz w) (Dz w) := fun j => by
    rw [delta_eq w hE hw, gcd_S_rotate w hE hw]
  have hl : (range w.length).lcm (delta w) = (Dz w).natAbs / Int.gcd (Sz w) (Dz w) := by
    apply Nat.dvd_antisymm
    · exact Finset.lcm_dvd fun j _ => (hδ j).dvd
    · rw [← hδ 0]; exact Finset.dvd_lcm (Finset.mem_range.2 ho)
  rw [hl, Nat.div_div_self (show Int.gcd (Sz w) (Dz w) ∣ (Dz w).natAbs from Nat.gcd_dvd_right _ _)
    (Int.natAbs_ne_zero.2 (Dz_ne_zero w hw)), gcdRot_eq w hE hw]

/-- On a closed orbit every trace part is integral (`δ_j = 1`) and `gcd_j S^{(j)} = |D|`. -/
theorem delta_eq_one_of_cycle {w : Word} {a : ℤ} (h : Follows (2 : ℤ) 3 w a a) (hE : 0 < w.sum)
    (hw : w ≠ []) (j : ℕ) : delta w j = 1 := by
  rw [delta_eq w hE hw, Int.gcd_eq_natAbs_right (Follows.D_dvd_S_rotate _ _ h j),
    Nat.div_self (Int.natAbs_pos.2 (Dz_ne_zero w hw))]

/-- `D(w) = 175 = 5^2·7` for `w = (1,3,1,3)`, yet `v_5(S^{(0)}) = 3 ≠ 2 = v_5(S^{(1)})`: the
valuation `v_p(S^{(j)})` of a prime `p ∣ D` is *not* rotation-invariant; only
`min(v_p(S^{(j)}), v_p(D))` is. -/
theorem vp_not_rotation_invariant :
    Dz [1, 3, 1, 3] = 5 ^ 2 * 7 ∧ (5 : ℤ) ^ 3 ∣ Sz [1, 3, 1, 3] ∧
      ¬ (5 : ℤ) ^ 3 ∣ Sz ([1, 3, 1, 3].rotate 1) := by
  refine ⟨by simp [D], by simp [S], ?_⟩
  simp [S]

end GcdLaw

/-! ## Rotation sums as traces (`number_field.md` §6, `gamma_w.md` §1–2, `circuits.md` §1) -/

section Trace

open Polynomial

/-- The power basis `1, x̂, …, x̂^{o-1}` of `A`. -/
noncomputable def pbA (w : Word) (hw : w ≠ []) : PowerBasis ℚ (Alg w) :=
  AdjoinRoot.powerBasis (monic_X_pow_sub_C ((2 : ℚ) ^ w.sum)
    (List.length_pos_of_ne_nil hw).ne').ne_zero

/-- The power basis of `A` has `o` elements. -/
lemma pbA_dim (w : Word) (hw : w ≠ []) : (pbA w hw).dim = w.length := by
  rw [pbA, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

/-- The `i`-th power-basis element is `x̂^i`. -/
lemma pbA_basis (w : Word) (hw : w ≠ []) (i : Fin (pbA w hw).dim) :
    (pbA w hw).basis i = xhat w ^ (i : ℕ) := by
  rw [PowerBasis.coe_basis]; rfl

/-- Coordinates of `x̂^n` (`n < 2o`) in the power basis of `A`. -/
lemma repr_xhat_pow (w : Word) (hw : w ≠ []) {n : ℕ} (hn : n < 2 * w.length)
    (i : Fin (pbA w hw).dim) :
    (pbA w hw).basis.repr (xhat w ^ n) i =
      if n = i then 1 else if n = i + w.length then 2 ^ w.sum else 0 := by
  have hdim := pbA_dim w hw
  have hi := i.2
  rcases lt_or_ge n w.length with h | h
  · rw [show xhat w ^ n = (pbA w hw).basis ⟨n, by omega⟩ by rw [pbA_basis],
      (pbA w hw).basis.repr_self, Finsupp.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · have : xhat w ^ n = (2 ^ w.sum : ℚ) • (pbA w hw).basis ⟨n - w.length, by omega⟩ := by
      rw [pbA_basis, Algebra.smul_def, ← xhat_pow, ← pow_add]
      congr 1; simp only; omega
    rw [this, map_smul, (pbA w hw).basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    simp only [Fin.ext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs <;> first | rfl | omega

/-- `Tr_{A/ℚ}(x̂^m) = o·[m = 0]` for `m < o` (`circuits.md` §1 trace kernel). -/
theorem trace_xhat_pow (w : Word) (hw : w ≠ []) {m : ℕ} (hm : m < w.length) :
    Algebra.trace ℚ (Alg w) (xhat w ^ m) = if m = 0 then (w.length : ℚ) else 0 := by
  have hdim := pbA_dim w hw
  rw [Algebra.trace_eq_matrix_trace (pbA w hw).basis, Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  have : ∀ i : Fin (pbA w hw).dim,
      (pbA w hw).basis.repr (xhat w ^ m * (pbA w hw).basis i) i = if m = 0 then 1 else 0 :=
    fun i => by
      have hi := i.2
      rw [pbA_basis, ← pow_add, repr_xhat_pow w hw (by omega)]
      split_ifs <;> first | rfl | omega
  simp only [this, Finset.sum_ite_irrel, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    hdim, nsmul_eq_mul, mul_one, mul_zero]

/-- `Tr(c·y) = c·Tr(y)` for `c ∈ ℚ`. -/
lemma trace_algebraMap_mul (w : Word) (c : ℚ) (y : Alg w) :
    Algebra.trace ℚ (Alg w) (algebraMap ℚ (Alg w) c * y) = c * Algebra.trace ℚ (Alg w) y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- `Tr_{A/ℚ}(x̂^n)` for `n < 2o`: `o` at `n = 0`, `o·2^E` at `n = o`, else `0`. -/
lemma trace_xhat_pow_lt_two_mul (w : Word) (hw : w ≠ []) {n : ℕ} (hn : n < 2 * w.length) :
    Algebra.trace ℚ (Alg w) (xhat w ^ n) =
      if n = 0 then (w.length : ℚ) else if n = w.length then w.length * 2 ^ w.sum else 0 := by
  have ho := List.length_pos_of_ne_nil hw
  rcases lt_or_ge n w.length with h | h
  · rw [trace_xhat_pow w hw h, ite_eq_right (c := n = w.length) (by omega)]
  · rw [show n = w.length + (n - w.length) by omega, pow_add, xhat_pow, trace_algebraMap_mul,
      trace_xhat_pow w hw (by omega), ite_eq_right (c := w.length + (n - w.length) = 0) (by omega)]
    by_cases h' : n - w.length = 0
    · rw [ite_eq_left h', ite_eq_left (by omega)]; ring
    · rw [ite_eq_right h', ite_eq_right (by omega), mul_zero]

/-- The word element `γ_W = (1/o) Σ_k 2^{e_k} x̂^{-k} = (1/(o 2^E)) Σ_k 2^{e_k} x̂^{o-k}`
(`gamma_w.md` §1). -/
noncomputable def gammaW (w : Word) : Alg w :=
  ∑ k ∈ range w.length, algebraMap ℚ (Alg w) (2 ^ e w k / (w.length * 2 ^ w.sum)) *
    xhat w ^ (w.length - k)

/-- `γ_W` represents the word functional: `Tr(γ_W x̂^i) = 2^{e_i}` for `i < o`. -/
theorem trace_gammaW_mul_xhat_pow (w : Word) (hw : w ≠ []) {i : ℕ} (hi : i < w.length) :
    Algebra.trace ℚ (Alg w) (gammaW w * xhat w ^ i) = 2 ^ e w i := by
  have ho : (w.length : ℚ) ≠ 0 := by exact_mod_cast (List.length_pos_of_ne_nil hw).ne'
  rw [gammaW, Finset.sum_mul, map_sum, Finset.sum_eq_single i]
  · rw [mul_assoc, ← pow_add, trace_algebraMap_mul,
      trace_xhat_pow_lt_two_mul w hw (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    field_simp
  · intro k hk hki
    rw [mul_assoc, ← pow_add, trace_algebraMap_mul,
      trace_xhat_pow_lt_two_mul w hw (by simp at hk; omega)]
    rw [ite_eq_right (by simp at hk; omega), ite_eq_right (by simp at hk; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 hi) h

/-- Casting `S` at `(2,3)` from `ℤ` to `ℚ`. -/
lemma Sz_cast (w : Word) : (Sz w : ℚ) = S (2 : ℚ) 3 w := by
  induction w with
  | nil => simp
  | cons d w ih => simp [ih]

/-- **Rotation sums are traces** (`number_field.md` §6(c), in the étale algebra of
`circuits.md` §1, so for every `(E, o)`): `2^{e_j} S^{(j)} = Tr_{A/ℚ}(γ_W x̂^j ĉ_0)`. -/
theorem trace_identity (w : Word) (hw : w ≠ []) {j : ℕ} (hj : j < w.length) :
    Algebra.trace ℚ (Alg w) (gammaW w * xhat w ^ j * chat0 w) =
      2 ^ e w j * (Sz (w.rotate j) : ℚ) := by
  have hstep : ∀ r ∈ range w.length, Algebra.trace ℚ (Alg w)
      (gammaW w * xhat w ^ j * (3 ^ (w.length - 1 - r) * xhat w ^ r)) =
      3 ^ (w.length - 1 - r) * 2 ^ (e (w.rotate j) r + e w j) := fun r hr => by
    have hr := Finset.mem_range.1 hr
    have he := e_rotate w (j := j) (k := r) hj.le hr.le
    rw [show gammaW w * xhat w ^ j * (3 ^ (w.length - 1 - r) * xhat w ^ r) =
        algebraMap ℚ (Alg w) (3 ^ (w.length - 1 - r)) * (gammaW w * xhat w ^ (j + r)) by
      simp only [map_pow, map_ofNat, pow_add]; ring, trace_algebraMap_mul, he]
    congr 1
    rcases lt_or_ge (j + r) w.length with h | h
    · rw [trace_gammaW_mul_xhat_pow w hw h, ite_eq_left h.le]
    · rw [show j + r = w.length + (j + r - w.length) by omega, pow_add, xhat_pow,
        mul_left_comm, trace_algebraMap_mul, trace_gammaW_mul_xhat_pow w hw (by omega)]
      split_ifs with h'
      · rw [show w.length + (j + r - w.length) = w.length by omega, e_length,
          show j + r - w.length = 0 by omega, e_zero, pow_zero, mul_one]
      · rw [pow_add, Nat.add_sub_cancel_left]
  rw [chat0, Finset.mul_sum, map_sum, Finset.sum_congr rfl hstep, Sz_cast, S_eq_sum,
    List.length_rotate, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_add]; ring

end Trace

/-! ## Extras: word-independence, `T_j` as a trace, Identity A in cosine form -/

section Extras

/-- **Identity B** (word-independence): `det M` depends only on `(E, o)`. -/
theorem det_Mrot_word_independent {R : Type*} [CommRing R] (X Y : R) (w w' : Word)
    (hE : w.sum = w'.sum) (ho : w.length = w'.length) : (Mrot X Y w).det = (Mrot X Y w').det := by
  rw [det_Mrot_eq_det_N, det_Mrot_eq_det_N, hE, ho]

/-- `x̂ - 3` is a unit of `A` with inverse `ĉ_0 / D`. -/
theorem xhat_sub_three_mul_inv (w : Word) (hw : w ≠ []) :
    (xhat w - 3) * (algebraMap ℚ (Alg w) (Dz w : ℚ)⁻¹ * chat0 w) = 1 := by
  rw [mul_left_comm, mul_comm (xhat w - 3), chat0_mul, ← map_mul,
    inv_mul_cancel₀ (by exact_mod_cast Dz_ne_zero w hw), map_one]

/-- The trace part as in the note: `T_j = Tr_{A/ℚ}(γ_W x̂^j / (x̂ - 3))`. -/
theorem T_eq_trace (w : Word) (hw : w ≠ []) {j : ℕ} (hj : j < w.length) :
    T w j = Algebra.trace ℚ (Alg w)
      (gammaW w * xhat w ^ j * (algebraMap ℚ (Alg w) (Dz w : ℚ)⁻¹ * chat0 w)) := by
  rw [mul_left_comm, trace_algebraMap_mul, trace_identity w hw hj, T]
  push_cast; ring

/-- The note's cosine form of Identity A,
`|D| = |3 - β| ∏_{ℓ=1}^{⌊o/2⌋} (9 - 6β cos(2πℓ/o) + β²)`, is false for even `o`: at
`(E, o) = (4, 2)` (`β = 4`, `D = 7`) the right side is `1 · 49`. -/
theorem identityA_cos_false :
    |(2 : ℝ) ^ 4 - 3 ^ 2| ≠ |3 - (2 : ℝ) ^ ((4 : ℝ) / 2)| *
      ∏ ℓ ∈ Finset.Icc (1 : ℕ) (2 / 2), (9 - 6 * (2 : ℝ) ^ ((4 : ℝ) / 2) *
        Real.cos (2 * Real.pi * (ℓ : ℝ) / 2)
        + ((2 : ℝ) ^ ((4 : ℝ) / 2)) ^ 2) := by
  rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [Nat.reduceDiv, Finset.Icc_self, Finset.prod_singleton, Nat.cast_one, mul_one]
  norm_num

/-- One factor of Identity A: `|3 - β ω^ℓ|² = 9 - 6β cos(2πℓ/o) + β²`. -/
lemma norm_sq_three_sub (β : ℝ) (o ℓ : ℕ) :
    ‖(3 : ℂ) - β * zeta o ^ ℓ‖ ^ 2 = 9 - 6 * β * Real.cos (2 * Real.pi * ℓ / o) + β ^ 2 := by
  have hz : zeta o ^ ℓ = Complex.exp (((2 * Real.pi * ℓ / o : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hz, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * ℓ / o)]

/-- **Identity A, corrected cosine form**: `D² = ∏_{ℓ<o} (9 - 6β cos(2πℓ/o) + β²)`
(the `ℓ = 0` factor is `(3 - β)²`; factors `ℓ` and `o - ℓ` coincide). -/
theorem identityA_cos (w : Word) (hw : w ≠ []) :
    ((2 : ℝ) ^ w.sum - 3 ^ w.length) ^ 2 = ∏ ℓ ∈ range w.length,
      (9 - 6 * beta w * Real.cos (2 * Real.pi * ℓ / w.length) + beta w ^ 2) := by
  rw [← sq_abs, identityA w hw, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun ℓ _ => norm_sq_three_sub _ _ _

end Extras

section RegularRep

open Polynomial

/-- **The circulant is a regular representation** (`number_field.md` §4, integral form): in the
power basis of `A`, multiplication by `ĉ_0` has matrix `Nᵀ` at `(P, Y) = (2^E, 3)`. -/
theorem leftMulMatrix_chat0 (w : Word) (hw : w ≠ []) (i j : Fin (pbA w hw).dim) :
    Algebra.leftMulMatrix (pbA w hw).basis (chat0 w) i j =
      N (3 : ℚ) (2 ^ w.sum) w.length ⟨j, lt_of_lt_of_eq j.2 (pbA_dim w hw)⟩
        ⟨i, lt_of_lt_of_eq i.2 (pbA_dim w hw)⟩ := by
  have hdim := pbA_dim w hw
  have hi := i.2
  have hj := j.2
  rw [Algebra.leftMulMatrix_eq_repr_mul, chat0, Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ r ∈ range w.length, (pbA w hw).basis.repr
      (3 ^ (w.length - 1 - r) * xhat w ^ r * (pbA w hw).basis j) i =
      3 ^ (w.length - 1 - r) * (if r + j = i then 1 else if r + j = i + w.length then
        2 ^ w.sum else 0) := fun r hr => by
    have hr := Finset.mem_range.1 hr
    rw [pbA_basis, mul_assoc, ← pow_add, show (3 : Alg w) ^ (w.length - 1 - r) =
      algebraMap ℚ (Alg w) (3 ^ (w.length - 1 - r)) by simp only [map_pow, map_ofNat],
      ← Algebra.smul_def, map_smul, Finsupp.smul_apply, repr_xhat_pow w hw (by omega),
      smul_eq_mul]
  rw [Finset.sum_congr rfl hterm]
  simp only [N, Matrix.of_apply, yExp_eq, Fin.lt_def]
  rcases le_or_gt (j : ℕ) i with h | h
  · rw [Finset.sum_eq_single ((i : ℕ) - j)]
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h]; ring
    · intro r hr' hr
      have := Finset.mem_range.1 hr'
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'
  · rw [Finset.sum_eq_single ((i : ℕ) + w.length - j)]
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h,
        ite_eq_right (by omega), show w.length - 1 - (i + w.length - j) = j - i - 1 by omega]
      ring
    · intro r hr' hr
      have := Finset.mem_range.1 hr'
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'

end RegularRep

section Examples

/-- **(1c) Geometric circulant**: `det Circ(1, ρ, …, ρ^{o-1}) = (-1)^{o+1} (ρ^o - 1)^{o-1}`. -/
theorem det_circ_geometric {K : Type*} [Field K] {o : ℕ} (ho : 0 < o) {ρ : K} (hρ : ρ ≠ 0) :
    (circ o fun r => ρ ^ r).det = (-1) ^ (o + 1) * (ρ ^ o - 1) ^ (o - 1) := by
  have h : circ o (fun r => ρ ^ r) = ρ ^ (o - 1) • N ρ⁻¹ 1 o := by
    ext j i
    have hm : ((i - j : Fin o) : ℕ) ≤ o - 1 := by have := (i - j : Fin o).2; omega
    simp only [circ, N, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ite_self, one_mul, yExp]
    generalize ((i - j : Fin o) : ℕ) = m at hm ⊢
    obtain ⟨t, ht⟩ : ∃ t, o - 1 = m + t := ⟨o - 1 - m, by omega⟩
    rw [ht, Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ, one_pow,
      mul_one]
  rw [h, Matrix.det_smul, det_N _ _ _ ho, Fintype.card_fin, ← pow_mul, mul_comm (o - 1),
    pow_mul, mul_left_comm, ← mul_pow, mul_sub, mul_one, ← mul_pow, mul_inv_cancel₀ hρ, one_pow]

/-- The trivial cycle `1 → 1` (word `(2)`): `det M = 1`. -/
example : (Mrot (2 : ℤ) 3 [2]).det = 1 := by rw [det_Mrot _ _ _ (by simp)]; simp [D]

/-- The cycle `-5 → -7` (word `(1, 2)`, `D = -1`): `det M = 1`. -/
example : (Mrot (2 : ℤ) 3 [1, 2]).det = 1 := by rw [det_Mrot _ _ _ (by simp)]; simp [D]

/-- `(E, o) = (7, 4)` (`D = 47`): `det M = -47^3`. -/
example : (Mrot (2 : ℤ) 3 [1, 2, 2, 2]).det = -47 ^ 3 := by rw [det_Mrot _ _ _ (by simp)]; simp [D]

/-- `number_field.md` §7: the word `(3, 3)` has `D = 55` and `gcd_j S^{(j)} = 11`. -/
example : gcdRot [3, 3] = 11 := by
  rw [gcdRot_eq _ (by simp) (by simp)]; simp [S, D]; rfl

/-- `circuits.md` §2, `(E, o) = (6, 4)`: the principal real circuit `ℚ(√2)` has
`N(2√2 - 3) = 1` (a unit), while `D = -17`. -/
example : Algebra.norm ℚ (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((2 : ℚ) ^ 3)) - 3)
    = 1 := by
  rw [norm_principal_circuit 3 2 (by norm_num)]; norm_num

end Examples
end Syracuse.CirculantMatrix
