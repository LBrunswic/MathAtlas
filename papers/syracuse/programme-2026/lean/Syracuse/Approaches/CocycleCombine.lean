import Syracuse.Basic

/-!
# Cocycle-combine: the word cocycle, compensating combinations, and the P-pattern results

Formalization of `approaches/cocycle-combine` (RATIONALE, STATUS, PATTERNS, LEDGER,
`structure/structure.md` claims C1–C11, `reports/P1,P2,P3,P4,P9,P10,P11.md`). Notation is
`Syracuse.Basic`'s: `S X Y w`, `D X Y w = X^E - Y^o`, `Mw`, rotation sums `S X Y (w.rotate j)`
(`List.rotate` is the *left* rotation), `Sz`, `Dz` at `(2,3)`. Identities are proved for arbitrary
`X Y` in an arbitrary commutative ring (= "certified in `ℤ[X,Y]`"), then specialised.

Index conventions. The notes write `|w|` both for the gap-sum and, in `S^{|w|}` (P0, P10's
`R^{|x|}`), for a rotation by `len w` letters; here the rotation is `w.length` and the exponent is
`w.sum`. In P2, `S^{(i)}` means `S(ρᵢ)` with `ρᵢ = d^i e d^{o-1-i}` (defect at position `i`), not
`S(τ.rotate i)`.

## Coverage table

| note claim | Lean name | status |
|---|---|---|
| structure.md C1/C2 (transfer matrix, monoid hom) | `Syracuse.Mw_eq`, `Syracuse.Mw_append` | proved (Basic) |
| C3 rotation = conjugation | `Mw_conj`, `Mw_rotate_conj`, `Mw_conj_inv` | proved; corrected: the inverse form needs `X` **and** `Y` units (`det M(w) = Y^o X^E`, `det_Mw`), so `M` lands in `GL₂(R[X⁻¹,Y⁻¹])`, not `GL₂(R[Y⁻¹])` |
| §1 trace/det/eigenvalue gap | `trace_Mw`, `det_Mw` | proved; corrected sign: §1 says `D = λ₁ - λ₂` with `λ₁ = Y^o`, `λ₂ = X^E`, which is `-D`; `D = λ₂ - λ₁` (as in the C11 paragraph) |
| C4 eigenvectors | `eigvec_Y`, `eigvec_X` | proved |
| C5 `σ(uv) = σ(u) + χ(u)σ(v)` | `sigma_append`, `chi_append` (`Y : Rˣ`); cleared form `S_append` | proved |
| C6 coboundary of `c` is `c·D`; `S` defined mod `⟨D⟩` | `coboundary`, `IsSCocycle`, `isSCocycle_S`, `isSCocycle_D`, `IsSCocycle.add_mul_D` | proved |
| C7 `C(u,v) = S(uv) - S(vu) = D(u)S(v) - D(v)S(u)` | `S_append_sub_S_append`, `wedge_eq_det`, `wedge_append_right` | proved (sign as in the note) |
| C8 Plücker | `plucker` | proved |
| C9a, C9b | `C9a`, `C9b` (with `g`, `g_eq_sum`, `g_append`, `Dpv`) | proved |
| C9 "`g` equals `S` of the cyclic gap word" | `g_pv`, `Dpv_pv`, `g_false_append` | corrected: `g(pv w) = S(w)` for parity vectors of gap words (starting with `1`); in general `g(0^k v) = X^k g(v)` |
| C9 Knight: odd `G` divides a power of `2` ⇒ `|D| = 1` | `knight_edge`, `knight_cycle`, `knight_cycle_b`, `dvd_g_rotate` | proved (conditional on `1u0`, `0u1` being rotations of the cycle's parity vector = Cohn's theorem, not formalized) |
| C10 rank exactly 2 | `S_eq_linRep`, `hankel_minor_three` (`≤ 2`), `hankel_minor_two` (`= -1`), `C10_accessible`, `C10_coaccessible` | proved |
| C11 `det(tI - M(w)) = (t - X^E)(t - Y^o)` | `charpoly_Mw` | proved |
| RATIONALE compensation: `G = gcd_j S^{(j)} = |D|`, `G` odd, combinations divisible, `|D| ≤ |C|` | `rotGcd`, `IsSyrCycle.rotGcd_eq`, `IsSyrCycle.rotGcd_odd`, `IsSyrCycle.Dz_dvd_comb`, `IsSyrCycle.abs_Dz_le`, `Follows.D_dvd_comb`, `rotGcd_dvd_comb`, `rotGcd_dvd_Dz` | proved |
| P2/P4/P10 "`G` may share factors of 3, `Y`-powers are not strippable" | `isCoprime_rotGcd_six`, `isCoprime_Dz_six`, `dvd_of_isCoprime_six_of_dvd` | corrected (false): `G ∣ D` and `gcd(D,6) = 1` for every word with `o, E ≥ 1`, so `Y`-power prefactors are gcd-invisible too; P2's choice of the *last* pair is unnecessary |
| P0 `S⁰ - S^{len w} = X^{(q-1)|w|} C(w,w')`, `q`-free ceiling | `P0`, `wedge_wpow_append`, `IsSyrCycle.P0_dvd`, `IsSyrCycle.P0_ceiling` | proved |
| P1 `(X^d - Y) S(d^o) = D`, rotations equal, `G = |D|/|2^d - 3|` | `P1`, `P1_rotate`, `P1_rotGcd` | proved |
| P2 adjacent-rotation difference | `P2_adjacent`, `P2_last`, `P2_last_of_le`, `P2_isRotated` | corrected: as a polynomial identity `S(ρ_{o-2}) - S(ρ_{o-1}) = X^{(o-2)d}(X^e - X^d)`; the note's `X^{(o-1)d}(X^{e-d} - 1)` is valid only for `e ≥ d` (Laurent otherwise) |
| P2 ceiling `|2^E - 3^o| ≤ 2^{|e-d|} - 1`, independent of `a, b` | `P2_ceiling`, `dvd_increment_iff` | proved (all `a, b`, incl. `a = b = 0`) |
| P2 non-vacuity `(1,1,1,4,1,1,1)`: `|D| = 1163` vs `7` | `P2_example_Dz`, `P2_example_not_cycle` | proved |
| P2 degenerate locus `C ≡ 0 ⇔ e = d` | `P2_core_eq_zero_iff` | proved |
| P3 rotation factorisation `S(A_i^q) = S(A_i) geo_q`, `geo_q = D(A^q)/D(A)`; every combination factors through `geo_q` | `geo`, `geo_eq_sum`, `S_wpow`, `D_wpow`, `P3_rotate`, `P3_comb` | proved |
| P3 cross-length identity | `P3_cross` | proved |
| P3 "`(uv)^q`, `q ≥ 2`, is never the gap word of a genuine cycle" | `isSyrCycle_neg5_twice` | corrected (imprecise): true only for the minimal period; `IsSyrCycle (-5) 4` has word `(1,2)^2` |
| P4 recurrence, second-order annihilator, closed form | `P4_recurrence`, `P4_annihilator`, `P4_closed` | proved (closed form with cleared denominator `D(w)`) |
| P4 "the `σ_q`-combination is not `G`-divisible" (1/24) | — | empirical, not formalized |
| P9 common diagonal, circulant form | `P9_blocks`, `P9_rotate_blocks`, `flatten_rotate_isRotated` | proved |
| P9 `c(t)(bt - a) = b^q - a^q` in `R[t]/(t^q - 1)` | `P9_circulant`, `P9_circulant_quot` | proved |
| P9 `X`-degree `≥ E(q-1)` for every nonzero combination | `P9_degree` | proved (precise reading: some coordinate of the formal core vector `g ⊛ c` over `A[X]` has `X`-degree `≥ E(q-1)`); the "no `q`-uniform core" conclusion is informal |
| P9 `q = 2` core and ceiling `(2^E + 3^o) ∣ (s₂ - s₁)` | `P9_pair`, `P9_pair_ceiling` | proved |
| P9 "`q = 2` always forces `s₁ = s₂`" | `P9_escape` | corrected (false): `u₁ = (1,1,3,2,1,3)`, `u₂ = (5,1,1,1,1,2)`, `(o,E) = (6,11)`: `s₁ = 1441 ≠ 6995 = s₂`, `2777 ∣ 5554` (the note's search stopped at `(5,9)`) |
| P10 stage (i) `Δ_x = X^{(q-1)E_x} C(x, y z^p)` | `P0` with `w = x`, `w' = y ++ wpow z p` | proved |
| P10 core split, `N`, kill-the-`Y`-mode, obstruction, degenerate stratum | `P10_split`, `P10N`, `P10N_expand`, `P10_killY`, `P10_obstruction`, `P10_degenerate`, `wedge_wpow` | proved; compact form `N = X^{E_y} C(x,z) - D(z) C(x,y)` (equals the note's 8 terms) |
| P10 "no single-word combination kills both modes" | — | not formalized (not a precise statement) |
| P11 increments, `D` invariance, unit-stripped size `2^{|dᵢ - dᵢ₊₁|} - 1` | `P11_transposition`, `P11_unit_transfer`, `P11_D_eq`, `P11_increment_dvd_iff` | proved |
| P11 uncovered word `(1,1,1,2,1,1,4)`, `D = -139`, `G = 139` | `isSyrCycle_neg17`, `P11_uncovered` | proved (it is the `-17` cycle) |
| P11 "residues fill `(0,|D|/2]`", stratum tables; P1/P2/P9/P10 numeric batteries | — | empirical, not formalized |
| structure.md §5 Ellison barrier, §8 Mahler/Kronecker/Zsigmondy programme | — | literature / open, not formalized |
-/

namespace Syracuse.CocycleCombine

/-! ## §1–§2 of `structure.md`: the representation and the group actions -/

section Ring

variable {R : Type*} [CommRing R] (X Y : R)

/-- **C3, inverse-free.** Rotation is conjugation: `M(u) M(vu) = M(uv) M(u)`. -/
theorem Mw_conj (u v : Word) : Mw X Y u * Mw X Y (v ++ u) = Mw X Y (u ++ v) * Mw X Y u := by
  rw [Mw_append, Mw_append, mul_assoc]

/-- **C3 for `List.rotate`.** The `k`-th rotation is conjugate to `w` by the matrix of the
rotated-off prefix. -/
theorem Mw_rotate_conj (w : Word) (k : ℕ) :
    Mw X Y (w.take (k % w.length)) * Mw X Y (w.rotate k) =
      Mw X Y w * Mw X Y (w.take (k % w.length)) := by
  rw [List.rotate_eq_drop_append_take_mod, Mw_append, ← mul_assoc, ← Mw_append,
    List.take_append_drop]

/-- `det M(w) = Y^o X^E`. -/
theorem det_Mw (w : Word) : (Mw X Y w).det = Y ^ w.length * X ^ w.sum := by
  rw [Mw_eq, Matrix.det_fin_two_of]; ring

/-- `tr M(w) = X^E + Y^o`. -/
theorem trace_Mw (w : Word) : (Mw X Y w).trace = X ^ w.sum + Y ^ w.length := by
  rw [Mw_eq, Matrix.trace_fin_two_of]; ring

/-- **C3, inverse form.** `M(vu) = M(u)⁻¹ M(uv) M(u)` when `X` and `Y` are units (both are
needed: `det M(u) = Y^o X^E`). -/
theorem Mw_conj_inv (u v : Word) (hX : IsUnit X) (hY : IsUnit Y) :
    Mw X Y (v ++ u) = (Mw X Y u)⁻¹ * Mw X Y (u ++ v) * Mw X Y u := by
  have hdet : IsUnit (Mw X Y u).det := by
    rw [det_Mw]; exact (hY.pow _).mul (hX.pow _)
  rw [mul_assoc, ← Mw_conj, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]

/-- **C4.** `(D, -S)ᵀ` is an eigenvector of `M(w)` for the eigenvalue `Y^o`. -/
theorem eigvec_Y (w : Word) :
    (Mw X Y w).mulVec ![D X Y w, -S X Y w] = Y ^ w.length • ![D X Y w, -S X Y w] := by
  rw [Mw_eq]
  ext i; fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D]; ring

/-- **C4/C11.** `(0, 1)ᵀ` is an eigenvector of `M(w)` for the eigenvalue `X^E`. -/
theorem eigvec_X (w : Word) : (Mw X Y w).mulVec ![0, 1] = X ^ w.sum • ![0, 1] := by
  rw [Mw_eq]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **C11.** The characteristic polynomial of the monodromy is `(t - X^E)(t - Y^o)`. -/
theorem charpoly_Mw (w : Word) :
    (Mw X Y w).charpoly =
      (Polynomial.X - Polynomial.C (X ^ w.sum)) * (Polynomial.X - Polynomial.C (Y ^ w.length)) := by
  rw [Matrix.charpoly, Matrix.det_fin_two, Mw_eq]
  simp
  ring

/-! ### C5/C6: the normalised cocycle and its coboundaries -/

/-- The normalised cocycle `σ(w) = S(w)/Y^o`, over a ring in which `Y` is a unit. -/
def sigma (X : R) (Y : Rˣ) (w : Word) : R := S X (Y : R) w * ((Y⁻¹ ^ w.length : Rˣ) : R)

/-- The character `χ(w) = X^E/Y^o`. -/
def chi (X : R) (Y : Rˣ) (w : Word) : R := X ^ w.sum * ((Y⁻¹ ^ w.length : Rˣ) : R)

/-- **C5.** `σ` is a crossed homomorphism: `σ(uv) = σ(u) + χ(u) σ(v)`. -/
theorem sigma_append (X : R) (Y : Rˣ) (u v : Word) :
    sigma X Y (u ++ v) = sigma X Y u + chi X Y u * sigma X Y v := by
  simp only [sigma, chi, S_append, List.length_append, pow_add, Units.val_mul,
    Units.val_pow_eq_pow_val]
  have h : ∀ n : ℕ, (Y : R) ^ n * ((Y⁻¹ : Rˣ) : R) ^ n = 1 := fun n => by
    rw [← mul_pow, Y.mul_inv, one_pow]
  linear_combination (S X (Y : R) u * ((Y⁻¹ : Rˣ) : R) ^ u.length) * h v.length

/-- `χ` is a character of the word monoid. -/
theorem chi_append (X : R) (Y : Rˣ) (u v : Word) : chi X Y (u ++ v) = chi X Y u * chi X Y v := by
  simp only [chi, List.sum_append, List.length_append, pow_add, Units.val_mul,
    Units.val_pow_eq_pow_val]
  ring

/-- **C6.** The coboundary `w ↦ χ(w)c - c` of a constant `c`, read at the `S`-level
(times `Y^o`), is `c · D(w)`. -/
theorem coboundary (X : R) (Y : Rˣ) (c : R) (w : Word) :
    (Y : R) ^ w.length * (chi X Y w * c - c) = c * D X Y w := by
  simp only [chi, D, Units.val_pow_eq_pow_val]
  have h : (Y : R) ^ w.length * ((Y⁻¹ : Rˣ) : R) ^ w.length = 1 := by
    rw [← mul_pow, Y.mul_inv, one_pow]
  linear_combination (X ^ w.sum * c) * h

/-- An `S`-level cocycle: a function obeying the concatenation law of `S` (cleared form of C5). -/
def IsSCocycle (f : Word → R) : Prop :=
  ∀ u v : Word, f (u ++ v) = Y ^ v.length * f u + X ^ u.sum * f v

/-- `S` is an `S`-level cocycle (this is `S_append`). -/
theorem isSCocycle_S : IsSCocycle X Y (S X Y) := S_append X Y

/-- `D` is an `S`-level cocycle (Trümper's law, `D_append`). -/
theorem isSCocycle_D : IsSCocycle X Y (D X Y) := D_append X Y

/-- **C6.** `S` is defined modulo coboundaries: adding `c · D` preserves the cocycle law. -/
theorem IsSCocycle.add_mul_D {f : Word → R} (hf : IsSCocycle X Y f) (c : R) :
    IsSCocycle X Y (fun w => f w + c * D X Y w) := by
  intro u v; simp only [hf u v, D_append]; ring

/-! ## §4: the wedge core and Plücker -/

/-- The wedge core `C(u,v) = D(u)S(v) - D(v)S(u)`. -/
def wedge (u v : Word) : R := D X Y u * S X Y v - D X Y v * S X Y u

/-- `C(u,v)` is the `2 × 2` determinant `det [[D(u), D(v)], [S(u), S(v)]]`. -/
theorem wedge_eq_det (u v : Word) :
    wedge X Y u v = !![D X Y u, D X Y v; S X Y u, S X Y v].det := by
  rw [Matrix.det_fin_two_of, wedge]

/-- **C7.** `S(uv) - S(vu) = D(u)S(v) - D(v)S(u)`. -/
theorem S_append_sub_S_append (u v : Word) :
    S X Y (u ++ v) - S X Y (v ++ u) = wedge X Y u v := by
  simp only [S_append, wedge, D]; ring

/-- **C8.** The Plücker/Jacobi relation among three cores. -/
theorem plucker (u v w : Word) :
    D X Y u * wedge X Y v w + D X Y v * wedge X Y w u + D X Y w * wedge X Y u v = 0 := by
  simp only [wedge]; ring

/-- `v ↦ C(x, v)` is again an `S`-level cocycle. -/
theorem wedge_append_right (x u v : Word) :
    wedge X Y x (u ++ v) = Y ^ v.length * wedge X Y x u + X ^ u.sum * wedge X Y x v := by
  simp only [wedge, S_append, D_append]; ring

/-- `C(w,w) = 0`. -/
@[simp] lemma wedge_self (w : Word) : wedge X Y w w = 0 := by simp [wedge]

/-! ## C10: `S` is a rational series of rank exactly `2` -/

/-- **C10.** The linear representation `S(w) = λ M(w) γ`, `λ = (0,1)`, `γ = (1,0)ᵀ`. -/
theorem S_eq_linRep (w : Word) : Matrix.vecMul ![0, 1] (Mw X Y w) ⬝ᵥ ![1, 0] = S X Y w := by
  rw [Mw_eq]; simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- **C10, rank `≥ 2`.** The Hankel minor on rows/columns `{ε, (1)}` is `-1`. -/
theorem hankel_minor_two :
    !![S X Y ([] ++ []), S X Y ([] ++ [1]); S X Y ([1] ++ []), S X Y ([1] ++ [1])].det = -1 := by
  simp [Matrix.det_fin_two_of]

/-- **C10, rank `≤ 2`.** Every `3 × 3` Hankel minor `det [S(pᵢ qⱼ)]` vanishes. -/
theorem hankel_minor_three (p q : Fin 3 → Word) :
    (Matrix.of fun i j => S X Y (p i ++ q j)).det = 0 := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, S_append]; ring

/-- **C10, minimality.** The representation is accessible: the rows `λM(ε)`, `λM((1))` have
determinant `-1`. -/
theorem C10_accessible :
    (Matrix.of ![Matrix.vecMul ![0, 1] (Mw X Y []), Matrix.vecMul ![0, 1] (Mw X Y [1])]).det =
      -1 := by
  rw [Mw_eq, Mw_eq, Matrix.det_fin_two]
  simp

/-- **C10, minimality.** The representation is co-accessible: the columns `M(ε)γ`, `M((1))γ`
have determinant `1`. -/
theorem C10_coaccessible :
    (Matrix.of ![(Mw X Y []).mulVec ![1, 0], (Mw X Y [1]).mulVec ![1, 0]]).det = 1 := by
  rw [Mw_eq, Mw_eq, Matrix.det_fin_two]
  simp

/-! ## §6, C9: Knight's edge identities on parity vectors -/

/-- Knight's parity-vector numerator `g(v) = Σᵢ X^{pᵢ} Y^{x-1-i}` (`pᵢ` the 0-based positions of
the `1`s, `x` their number), by the recursion `g(1v) = Y^{#1(v)} + X g(v)`, `g(0v) = X g(v)`;
see `g_eq_sum`. -/
def g : List Bool → R
  | [] => 0
  | true :: v => Y ^ v.count true + X * g v
  | false :: v => X * g v

/-- `g(ε) = 0`. -/
@[simp] lemma g_nil : g X Y [] = 0 := rfl

/-- `g(1v) = Y^{#1(v)} + X g(v)`. -/
@[simp] lemma g_true (v : List Bool) : g X Y (true :: v) = Y ^ v.count true + X * g X Y v := rfl

/-- `g(0v) = X g(v)`. -/
@[simp] lemma g_false (v : List Bool) : g X Y (false :: v) = X * g X Y v := rfl

/-- The closed form: each `1` at position `i` contributes `X^i Y^{#1 after it}`. -/
theorem g_eq_sum (v : List Bool) :
    g X Y v = ∑ i ∈ Finset.range v.length,
      if v.getD i false then X ^ i * Y ^ (v.drop (i + 1)).count true else 0 := by
  induction v with
  | nil => simp
  | cons b v ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.drop_succ_cons, pow_succ, List.getD_cons_zero, pow_zero,
      one_mul]
    have : ∑ i ∈ Finset.range v.length,
        (if v.getD i false then X ^ i * X * Y ^ (v.drop (i + 1)).count true else 0) =
          X * g X Y v := by
      rw [ih, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [this]
    cases b <;> simp [add_comm]

/-- `D` of a parity vector of length `E` with `x` ones: `X^E - Y^x`. -/
def Dpv (v : List Bool) : R := X ^ v.length - Y ^ v.count true

/-- Concatenation law for `g`. -/
theorem g_append (u v : List Bool) :
    g X Y (u ++ v) = Y ^ v.count true * g X Y u + X ^ u.length * g X Y v := by
  induction u with
  | nil => simp
  | cons b u ih => cases b <;> simp [ih, List.count_append, pow_add, pow_succ] <;> ring

/-- **C9a.** `Y g(1u0) - g(0u1) + D = X^{E-1}(X - 1)`, `E` the parity-vector length. -/
theorem C9a (u : List Bool) :
    Y * g X Y (true :: (u ++ [false])) - g X Y (false :: (u ++ [true])) +
        Dpv X Y (true :: (u ++ [false])) =
      X ^ ((true :: (u ++ [false])).length - 1) * (X - 1) := by
  simp [g_append, Dpv, List.count_append, pow_succ]
  ring

/-- **C9b.** `g(p01) - g(p10) = X^{E-2}(X - 1)`. -/
theorem C9b (p : List Bool) :
    g X Y (p ++ [false, true]) - g X Y (p ++ [true, false]) =
      X ^ ((p ++ [false, true]).length - 2) * (X - 1) := by
  simp [g_append, pow_succ]
  ring

/-- The parity vector of a gap word: `d ↦ 1 0^{d-1}`. -/
def pv : Word → List Bool
  | [] => []
  | d :: w => true :: (List.replicate (d - 1) false ++ pv w)

/-- Leading zeros contribute a power of `X`: `g(0^n v) = X^n g(v)`. -/
@[simp] lemma g_false_append (n : ℕ) (v : List Bool) :
    g X Y (List.replicate n false ++ v) = X ^ n * g X Y v := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ]; ring

/-- The parity vector of a positive word has length `E`. -/
theorem pv_length {w : Word} (hw : w.Pos) : (pv w).length = w.sum := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have := ih fun x hx => hw x (by simp [hx])
    simp [pv, this]; omega

/-- The parity vector has `o` ones. -/
theorem pv_count (w : Word) : (pv w).count true = w.length := by
  induction w with
  | nil => rfl
  | cons d w ih => simp [pv, List.count_append, ih, List.count_replicate]

/-- **C9 bridge.** `g(pv w) = S(w)` for a positive gap word (= Trümper's link function). -/
theorem g_pv {w : Word} (hw : w.Pos) : g X Y (pv w) = S X Y w := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have := ih fun x hx => hw x (by simp [hx])
    simp only [pv, g_true, g_false_append, this, S_cons, List.count_append, pv_count,
      List.count_replicate]
    simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, zero_add]
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd]

/-- `D(pv w) = D(w)`. -/
theorem Dpv_pv {w : Word} (hw : w.Pos) : Dpv X Y (pv w) = D X Y w := by
  rw [Dpv, D, pv_length hw, pv_count]

/-- `D` of a parity vector is rotation invariant. -/
@[simp] theorem Dpv_rotate (v : List Bool) (n : ℕ) : Dpv X Y (v.rotate n) = Dpv X Y v := by
  simp [Dpv, (List.rotate_perm v n).count_eq]

/-- Rotation recursion for `g`: `X g(rot v) = g(v)` if `v` starts with `0`. -/
theorem g_rotate_one_false (v : List Bool) :
    X * g X Y ((false :: v).rotate 1) = g X Y (false :: v) := by
  simp [g_append]

/-- Rotation recursion for `g`: `X g(rot v) = Y g(v) + D(v)` if `v` starts with `1`. -/
theorem g_rotate_one_true (v : List Bool) :
    X * g X Y ((true :: v).rotate 1) = Y * g X Y (true :: v) + Dpv X Y (true :: v) := by
  simp [g_append, Dpv, pow_succ]; ring

/-! ## The P-patterns: generic identities -/

/-- The block power `w^q`. -/
def wpow (w : Word) (q : ℕ) : Word := (List.replicate q w).flatten

/-- `w^0 = ε`. -/
@[simp] lemma wpow_zero (w : Word) : wpow w 0 = [] := rfl

/-- `w^{q+1} = w w^q`. -/
lemma wpow_succ (w : Word) (q : ℕ) : wpow w (q + 1) = w ++ wpow w q := by
  simp [wpow, List.replicate_succ]

/-- `w^{q+1} = w^q w`. -/
lemma wpow_succ' (w : Word) (q : ℕ) : wpow w (q + 1) = wpow w q ++ w := by
  simp [wpow, List.replicate_succ']

/-- `len(w^q) = q len w`. -/
@[simp] lemma wpow_length (w : Word) (q : ℕ) : (wpow w q).length = q * w.length := by
  induction q with
  | zero => simp
  | succ q ih => rw [wpow_succ, List.length_append, ih]; ring

/-- `|w^q| = q |w|`. -/
@[simp] lemma wpow_sum (w : Word) (q : ℕ) : (wpow w q).sum = q * w.sum := by
  induction q with
  | zero => simp
  | succ q ih => rw [wpow_succ, List.sum_append, ih]; ring

/-- Block telescoping: `C(w, w^k v) = X^{k|w|} C(w, v)`. -/
theorem wedge_wpow_append (w v : Word) (k : ℕ) :
    wedge X Y w (wpow w k ++ v) = X ^ (k * w.sum) * wedge X Y w v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wpow_succ, List.append_assoc, wedge_append_right, ih, wedge_self]; ring

/-- **P0.** For `τ = w^{k+1} w'`, `S(τ) - S(rot_{len w} τ) = X^{k|w|} C(w, w')`. -/
theorem P0 (w w' : Word) (k : ℕ) :
    S X Y (wpow w (k + 1) ++ w') - S X Y ((wpow w (k + 1) ++ w').rotate w.length) =
      X ^ (k * w.sum) * wedge X Y w w' := by
  rw [wpow_succ, List.append_assoc, List.rotate_append_length_eq, S_append_sub_S_append,
    wedge_wpow_append]

/-- **P1.** The circuit `d^o`: `(X^d - Y) S(d^o) = D(d^o)`. -/
theorem P1 (d o : ℕ) : (X ^ d - Y) * S X Y (List.replicate o d) = D X Y (List.replicate o d) := by
  induction o with
  | zero => simp
  | succ o ih =>
    rw [List.replicate_succ, S_cons, D, List.length_cons, List.sum_cons, List.length_replicate,
      List.sum_replicate, smul_eq_mul]
    rw [D, List.length_replicate, List.sum_replicate, smul_eq_mul] at ih
    linear_combination X ^ d * ih

/-- **P1.** All rotations of `d^o` coincide. -/
theorem P1_rotate (d o j : ℕ) :
    S X Y ((List.replicate o d).rotate j) = S X Y (List.replicate o d) := by
  rw [List.rotate_replicate]

/-- The common geometric factor of P3, `geo_q(A) = Σ_{k<q} X^{k|A|} Y^{(q-1-k) len A}`
(see `geo_eq_sum`), realised as `S` at `(X, Y^{len A})` of the circuit `|A|^q`. -/
def geo (A : Word) (q : ℕ) : R := S X (Y ^ A.length) (List.replicate q A.sum)

/-- The closed form of `geo`. -/
theorem geo_eq_sum (A : Word) (q : ℕ) :
    geo X Y A q = ∑ k ∈ Finset.range q, X ^ (k * A.sum) * Y ^ ((q - 1 - k) * A.length) := by
  rw [geo, S_eq_sum, List.length_replicate]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [e, List.take_replicate, List.sum_replicate, smul_eq_mul, ← pow_mul, mul_comm A.length,
    min_eq_left (Finset.mem_range.1 hk).le]

/-- `geo_{q+1} = (Y^{len A})^q + X^{|A|} geo_q`. -/
theorem geo_succ_left (A : Word) (q : ℕ) :
    geo X Y A (q + 1) = (Y ^ A.length) ^ q + X ^ A.sum * geo X Y A q := by
  rw [geo, List.replicate_succ, S_cons, List.length_replicate, ← geo]

/-- `geo_{q+1} = X^{q|A|} + Y^{len A} geo_q`. -/
theorem geo_succ (A : Word) (q : ℕ) :
    geo X Y A (q + 1) = X ^ (q * A.sum) + Y ^ A.length * geo X Y A q := by
  rw [geo, List.replicate_succ', S_append, S_singleton, List.length_singleton, pow_one,
    List.sum_replicate, smul_eq_mul, ← geo]; ring

/-- `geo` depends only on `(|A|, len A)`, hence is rotation invariant. -/
theorem geo_rotate (A : Word) (q j : ℕ) : geo X Y (A.rotate j) q = geo X Y A q := by
  simp [geo, (List.rotate_perm A j).sum_eq]

/-- **P3.** `S(A^q) = S(A) · geo_q`. -/
theorem S_wpow (A : Word) (q : ℕ) : S X Y (wpow A q) = S X Y A * geo X Y A q := by
  induction q with
  | zero => simp [geo]
  | succ q ih =>
    rw [wpow_succ, S_append, ih, geo_succ_left, wpow_length, pow_mul']
    ring

/-- **P3.** `D(A^q) = D(A) · geo_q`, so `geo_q = D(A^q)/D(A)`. -/
theorem D_wpow (A : Word) (q : ℕ) : D X Y (wpow A q) = D X Y A * geo X Y A q := by
  have := P1 X (Y ^ A.length) A.sum q
  rw [D, List.length_replicate, List.sum_replicate, smul_eq_mul, ← pow_mul] at this
  rw [D, D, wpow_sum, wpow_length, geo, this, mul_comm A.length q]

/-- `(uv)^{k+1} = u (vu)^k v`. -/
theorem wpow_append_swap (u v : Word) (k : ℕ) :
    wpow (u ++ v) (k + 1) = u ++ wpow (v ++ u) k ++ v := by
  induction k with
  | zero => simp [wpow_succ]
  | succ k ih => rw [wpow_succ, ih, wpow_succ]; simp

/-- **P3.** The rotations of `A^q` are the `q`-th powers of the rotations of `A`. -/
theorem P3_rotate (A : Word) (q j : ℕ) (hj : j ≤ A.length) :
    (wpow A q).rotate j = wpow (A.rotate j) q := by
  obtain ⟨u, v, rfl, rfl⟩ : ∃ u v, A = u ++ v ∧ u.length = j :=
    ⟨A.take j, A.drop j, (List.take_append_drop j A).symm, by simp [hj]⟩
  rcases q with _ | k
  · simp
  · rw [List.rotate_append_length_eq, wpow_append_swap, List.append_assoc,
      List.rotate_append_length_eq, List.append_assoc, ← wpow_succ']

/-- **P3, the obstruction.** Every combination of the rotation sums of `A^q` (rotations
`j ≤ len A`, which exhaust them) factors through the common `geo_q`. -/
theorem P3_comb (A : Word) (q : ℕ) (J : Finset ℕ) (hJ : ∀ j ∈ J, j ≤ A.length) (c : ℕ → R) :
    ∑ j ∈ J, c j * S X Y ((wpow A q).rotate j) = geo X Y A q * ∑ j ∈ J, c j * S X Y (A.rotate j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [P3_rotate A q j (hJ j hj), S_wpow, geo_rotate]; ring

/-- **P3, cross-length identity** (`A = uv`, `B = vu`):
`[S(A^{k+1}) - S(B^{k+1})] - Y^{len A}[S(A^k) - S(B^k)] = X^{k|A|} C(u,v)`. -/
theorem P3_cross (u v : Word) (k : ℕ) :
    (S X Y (wpow (u ++ v) (k + 1)) - S X Y (wpow (v ++ u) (k + 1))) -
      Y ^ (u ++ v).length * (S X Y (wpow (u ++ v) k) - S X Y (wpow (v ++ u) k)) =
      X ^ (k * (u ++ v).sum) * wedge X Y u v := by
  have hg : geo X Y (v ++ u) = geo X Y (u ++ v) := by
    funext q; simp [geo, add_comm]
  rw [S_wpow, S_wpow, S_wpow, S_wpow, hg, geo_succ, ← S_append_sub_S_append]
  ring

/-- **P4, the first-order `q`-recurrence** `f(q+1) = X^{|w|} f(q) + Y^{qn + n'} S(w)` for
`f(q) = S(w^q w')`. -/
theorem P4_recurrence (w w' : Word) (q : ℕ) :
    S X Y (wpow w (q + 1) ++ w') =
      X ^ w.sum * S X Y (wpow w q ++ w') + Y ^ (q * w.length + w'.length) * S X Y w := by
  rw [wpow_succ, List.append_assoc, S_append, List.length_append, wpow_length]; ring

/-- **P4, the second-order annihilator** `(1 - Y^n σ)(1 - X^{|w|} σ) f = 0`. -/
theorem P4_annihilator (w w' : Word) (q : ℕ) :
    S X Y (wpow w (q + 2) ++ w') - (X ^ w.sum + Y ^ w.length) * S X Y (wpow w (q + 1) ++ w') +
      X ^ w.sum * Y ^ w.length * S X Y (wpow w q ++ w') = 0 := by
  rw [P4_recurrence X Y w w' (q + 1), P4_recurrence X Y w w' q]
  ring

/-- **P4, the exact closed form** (cleared denominator):
`D(w) S(w^{k+1} w') = D(w) X^{k|w|} S(ww') + S(w) Y^{n'+n} (X^{k|w|} - Y^{kn})`. -/
theorem P4_closed (w w' : Word) (k : ℕ) :
    D X Y w * S X Y (wpow w (k + 1) ++ w') =
      D X Y w * X ^ (k * w.sum) * S X Y (w ++ w') +
        S X Y w * Y ^ (w'.length + w.length) * (X ^ (k * w.sum) - Y ^ (k * w.length)) := by
  induction k with
  | zero => simp [wpow_succ]
  | succ k ih =>
    rw [P4_recurrence, mul_add, ← mul_assoc, mul_comm (D X Y w), mul_assoc, ih, D]
    ring

/-- **P2, any adjacent pair.** With `ρᵢ = d^i e d^{o-1-i}` and `o = i + m + 2`:
`S(ρᵢ) - S(ρᵢ₊₁) = X^{id}(X^e - X^d) Y^{o-2-i}`. -/
theorem P2_adjacent (d e i m : ℕ) :
    S X Y (List.replicate i d ++ e :: List.replicate (m + 1) d) -
      S X Y (List.replicate (i + 1) d ++ e :: List.replicate m d) =
      X ^ (i * d) * (X ^ e - X ^ d) * Y ^ m := by
  rw [show List.replicate (i + 1) d ++ e :: List.replicate m d =
      List.replicate i d ++ d :: e :: List.replicate m d by simp [List.replicate_succ'],
    S_append, S_append]
  simp only [List.length_cons, List.length_replicate, S_cons, List.replicate_succ,
    List.sum_replicate, smul_eq_mul]
  ring

/-- **P2, last pair** (`ρ_{o-2} = d^{n} e d`, `ρ_{o-1} = d^{n+1} e`, `n = o - 2`):
`S(ρ_{o-2}) - S(ρ_{o-1}) = X^{(o-2)d}(X^e - X^d)`, valid for all `d, e`. -/
theorem P2_last (d e n : ℕ) :
    S X Y (List.replicate n d ++ [e, d]) - S X Y (List.replicate (n + 1) d ++ [e]) =
      X ^ (n * d) * (X ^ e - X ^ d) := by
  simpa using P2_adjacent X Y d e n 0

/-- **P2, the note's form** `X^{(o-1)d}(X^{e-d} - 1)`, valid when `d ≤ e`. -/
theorem P2_last_of_le {d e : ℕ} (hde : d ≤ e) (n : ℕ) :
    S X Y (List.replicate n d ++ [e, d]) - S X Y (List.replicate (n + 1) d ++ [e]) =
      X ^ ((n + 1) * d) * (X ^ (e - d) - 1) := by
  rw [P2_last, ← Nat.add_sub_cancel' hde]
  simp only [Nat.add_sub_cancel_left, pow_add]; ring

/-- **P11, adjacent transposition** `dᵢ ↔ dᵢ₊₁` (`i = len p`, `o - 2 - i = len s`):
`S(w') - S(w) = Y^{o-2-i} X^{Pᵢ}(X^{dᵢ₊₁} - X^{dᵢ})`. -/
theorem P11_transposition (p s : Word) (α β : ℕ) :
    S X Y (p ++ β :: α :: s) - S X Y (p ++ α :: β :: s) =
      Y ^ s.length * X ^ p.sum * (X ^ β - X ^ α) := by
  simp only [S_append, S_cons, List.length_cons]; ring

/-- **P11, unit transfer** `dᵢ → dᵢ + 1, dᵢ₊₁ → dᵢ₊₁ - 1`:
`S(w') - S(w) = Y^{o-2-i} X^{Pᵢ₊₁}(X - 1)`. -/
theorem P11_unit_transfer (p s : Word) (α β : ℕ) :
    S X Y (p ++ (α + 1) :: β :: s) - S X Y (p ++ α :: (β + 1) :: s) =
      Y ^ s.length * X ^ (p.sum + α) * (X - 1) := by
  simp only [S_append, S_cons, List.length_cons]; ring

/-- **P11.** Both twists stay in the stratum: `D(w') = D(w)`. -/
theorem P11_D_eq (p s : Word) (α β : ℕ) :
    D X Y (p ++ β :: α :: s) = D X Y (p ++ α :: β :: s) ∧
      D X Y (p ++ (α + 1) :: β :: s) = D X Y (p ++ α :: (β + 1) :: s) := by
  constructor <;> simp only [D, List.sum_append, List.sum_cons, List.length_append,
    List.length_cons] <;> ring_nf

/-- **P9, `q = 2`.** For balanced blocks (`len u₁ = len u₂ = o`, `|u₁| = |u₂| = E`):
`S(u₁u₂) - S(u₂u₁) = (Y^o - X^E)(S(u₁) - S(u₂))`. -/
theorem P9_pair (u₁ u₂ : Word) (hl : u₁.length = u₂.length) (hs : u₁.sum = u₂.sum) :
    S X Y (u₁ ++ u₂) - S X Y (u₂ ++ u₁) = (Y ^ u₁.length - X ^ u₁.sum) * (S X Y u₁ - S X Y u₂) := by
  rw [S_append_sub_S_append, wedge, D, D, ← hl, ← hs]; ring

/-- `q` blocks of length `o` have total length `q o`. -/
lemma length_flatten_of_eq {o : ℕ} (us : List Word) (hus : ∀ u ∈ us, u.length = o) :
    us.flatten.length = us.length * o := by
  induction us with
  | nil => simp
  | cons u us ih =>
    rw [List.flatten_cons, List.length_append, ih fun v hv => hus v (by simp [hv]),
      hus u (by simp), List.length_cons]; ring

/-- **P9, common diagonal.** For `q` balanced blocks `uᵢ` (each of length `o`, gap-sum `E`),
`S(u₀ ⋯ u_{q-1}) = Σᵢ (Y^o)^{q-1-i} (X^E)^i S(uᵢ)`. -/
theorem P9_blocks {o E : ℕ} (us : List Word) (hus : ∀ u ∈ us, u.length = o ∧ u.sum = E) :
    S X Y us.flatten = ∑ i ∈ Finset.range us.length,
      (Y ^ o) ^ (us.length - 1 - i) * (X ^ E) ^ i * S X Y (us.getD i []) := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hu := hus u (by simp)
    rw [List.flatten_cons, S_append, ih fun v hv => hus v (by simp [hv]), List.length_cons,
      Finset.sum_range_succ', length_flatten_of_eq us fun v hv => (hus v (by simp [hv])).1, hu.2,
      Finset.mul_sum, add_comm, pow_mul']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Nat.add_sub_cancel,
      Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show us.length - (i + 1) = us.length - 1 - i by omega]; ring

/-- **P9, circulant form.** The block rotation `R^k w` has
`S(R^k w) = Σᵢ (Y^o)^{q-1-i} (X^E)^i S(u_{(i+k) mod q})`. -/
theorem P9_rotate_blocks {o E : ℕ} (us : List Word) (hus : ∀ u ∈ us, u.length = o ∧ u.sum = E)
    (k : ℕ) :
    S X Y (us.rotate k).flatten = ∑ i ∈ Finset.range us.length,
      (Y ^ o) ^ (us.length - 1 - i) * (X ^ E) ^ i * S X Y (us.getD ((i + k) % us.length) []) := by
  rw [P9_blocks X Y (us.rotate k) fun u hu => hus u ((List.mem_rotate).1 hu), List.length_rotate]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_rotate,
    List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]

/-- **P9.** The generator `c(t) = Σ_m a^{q-1-m} b^m t^m` satisfies
`c(t)(bt - a) = b^q t^q - a^q` in `R[t]`. -/
theorem P9_circulant (a b : R) (q : ℕ) :
    (∑ m ∈ Finset.range q, Polynomial.C (a ^ (q - 1 - m) * b ^ m) * Polynomial.X ^ m) *
        (Polynomial.C b * Polynomial.X - Polynomial.C a) =
      Polynomial.C (b ^ q) * Polynomial.X ^ q - Polynomial.C (a ^ q) := by
  have := geom_sum₂_mul (Polynomial.C b * Polynomial.X) (Polynomial.C a) q
  rw [mul_pow, ← Polynomial.C_pow, ← Polynomial.C_pow] at this
  rw [← this]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_pow, mul_pow]; ring

/-- **P9.** In `R[t]/(t^q - 1)`: `c(t)(bt - a) = b^q - a^q`. -/
theorem P9_circulant_quot (a b : R) (q : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ q - 1 : Polynomial R)})
      ((∑ m ∈ Finset.range q, Polynomial.C (a ^ (q - 1 - m) * b ^ m) * Polynomial.X ^ m) *
        (Polynomial.C b * Polynomial.X - Polynomial.C a)) =
    Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ q - 1 : Polynomial R)})
      (Polynomial.C (b ^ q - a ^ q)) := by
  rw [Ideal.Quotient.eq, P9_circulant, Ideal.mem_span_singleton']
  exact ⟨Polynomial.C (b ^ q), by rw [Polynomial.C_sub]; ring⟩

/-- **P9, the degree obstruction.** Model `ℤ[X,Y] = A[X]` with `A = ℤ[Y]` (any commutative `A`),
`q = n + 2` blocks, `b = X^E` (`E ≥ 1`) and `a ∈ A` (`a = Y^o`). A combination
`Σ_k g_k S(R^k w)` with coefficients `g_k ∈ A[X]` has, on the formal block sums `s_j`, the
coefficient vector `core_j = Σ_k g_k c_{(j-k) mod q}`, `c_m = a^{q-1-m} b^m`. If some `g_k ≠ 0`,
some `core_j` has `X`-degree `≥ E(q-1)`: the top term `b^{q-1}` cannot cancel. -/
theorem P9_degree {A : Type*} [CommRing A] (n E : ℕ) (hE : 1 ≤ E) (a : A)
    (g : Fin (n + 2) → Polynomial A) (hg : g ≠ 0) :
    ∃ j : Fin (n + 2), E * (n + 1) ≤
      (∑ k, g k * (Polynomial.C (a ^ (n + 1 - (j - k).val)) *
        Polynomial.X ^ (E * (j - k).val))).natDegree := by
  classical
  obtain ⟨k0, hk0⟩ : ∃ k, g k ≠ 0 := by
    by_contra h; push Not at h; exact hg (funext h)
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun k => g k ≠ 0)
    (fun k => (g k).natDegree) ⟨k0, by simpa using hk0⟩
  have hkne : g k ≠ 0 := (Finset.mem_filter.1 hk).2
  have : Nontrivial A := Polynomial.nontrivial_iff.1 ⟨⟨g k, 0, hkne⟩⟩
  have hmax' : ∀ k', (g k').natDegree ≤ (g k).natDegree := by
    intro k'
    by_cases h : g k' = 0
    · simp [h]
    · exact hmax k' (by simp [h])
  refine ⟨k + Fin.last (n + 1), ?_⟩
  set j := k + Fin.last (n + 1)
  have hjk : j - k = Fin.last (n + 1) := by simp [j]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hjk, Fin.val_last, Nat.sub_self, pow_zero,
    Polynomial.C_1, one_mul]
  have hrest : (∑ k' ∈ Finset.univ.erase k, g k' * (Polynomial.C (a ^ (n + 1 - (j - k').val)) *
      Polynomial.X ^ (E * (j - k').val))).natDegree ≤ (g k).natDegree + E * n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k' hk' => ?_
    have hne : j - k' ≠ Fin.last (n + 1) := by
      rw [← hjk]; intro h; exact (Finset.mem_erase.1 hk').1 (sub_right_injective h)
    have hlt : (j - k').val ≤ n := by
      have := Fin.val_lt_last hne
      simp at this; omega
    calc (g k' * (Polynomial.C (a ^ (n + 1 - (j - k').val)) *
          Polynomial.X ^ (E * (j - k').val))).natDegree
        ≤ (g k').natDegree + (Polynomial.C (a ^ (n + 1 - (j - k').val)) *
          Polynomial.X ^ (E * (j - k').val)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (g k).natDegree + E * n := by
          gcongr
          · exact hmax' k'
          · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.mul_le_mul_left _ hlt)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_mul_X_pow _ hkne]
  · omega
  · rw [Polynomial.natDegree_mul_X_pow _ hkne]
    calc _ ≤ (g k).natDegree + E * n := hrest
      _ < (g k).natDegree + E * (n + 1) := by nlinarith

/-- `D(z) C(x, z^p) = (X^{p|z|} - Y^{p len z}) C(x, z)`. -/
theorem wedge_wpow (x z : Word) (p : ℕ) :
    D X Y z * wedge X Y x (wpow z p) = (X ^ (p * z.sum) - Y ^ (p * z.length)) * wedge X Y x z := by
  induction p with
  | zero => simp [wedge]
  | succ p ih =>
    rw [wpow_succ', wedge_append_right, mul_add, ← mul_assoc, mul_comm (D X Y z), mul_assoc, ih]
    simp only [D, wpow_sum]
    ring

/-- The three-block numerator of P10, in compact form `N = X^{E_y} C(x,z) - D(z) C(x,y)`. -/
def P10N (x y z : Word) : R := X ^ y.sum * wedge X Y x z - D X Y z * wedge X Y x y

/-- `P10N` equals the 8-term `N` written in `reports/P10.md`. -/
theorem P10N_expand (x y z : Word) :
    P10N X Y x y z =
      X ^ (x.sum + y.sum) * S X Y z - X ^ (x.sum + z.sum) * S X Y y
      + X ^ x.sum * Y ^ z.length * S X Y y - X ^ y.sum * Y ^ x.length * S X Y z
      + X ^ z.sum * Y ^ x.length * S X Y y - X ^ z.sum * Y ^ y.length * S X Y x
      - Y ^ (x.length + z.length) * S X Y y + Y ^ (y.length + z.length) * S X Y x := by
  simp only [P10N, wedge, D]; ring

/-- **P10, the core split** (cleared denominator): for `w = x^q y z^p`, the stage-(i) core
`C_x(p) = C(x, y z^p)` satisfies `D(z) C_x(p) = X^{E_y + pE_z} C(x,z) - Y^{p o_z} N`. -/
theorem P10_split (x y z : Word) (p : ℕ) :
    D X Y z * wedge X Y x (y ++ wpow z p) =
      X ^ (y.sum + p * z.sum) * wedge X Y x z - Y ^ (p * z.length) * P10N X Y x y z := by
  rw [wedge_append_right, wpow_length, P10N, pow_add]
  linear_combination X ^ y.sum * wedge_wpow X Y x z p

/-- **P10, kill-the-`Y`-mode.** `C_x(p+1) - Y^{o_z} C_x(p) = X^{E_y + pE_z} C(x,z)`
(a relation between the cores of two *different* words). -/
theorem P10_killY (x y z : Word) (p : ℕ) :
    wedge X Y x (y ++ wpow z (p + 1)) - Y ^ z.length * wedge X Y x (y ++ wpow z p) =
      X ^ (y.sum + p * z.sum) * wedge X Y x z := by
  rw [wpow_succ', ← List.append_assoc, wedge_append_right, List.sum_append, wpow_sum]; ring

/-- **P10, obstruction.** If `C(x,z) = 0` then `N = -D(z) C(x,y)`
(= `D(x)D(z)(D(y) r - s_y)` with `r = s_x/D(x)` in the note). -/
theorem P10_obstruction (x y z : Word) (hxz : wedge X Y x z = 0) :
    P10N X Y x y z = -(D X Y z * wedge X Y x y) := by
  rw [P10N, hxz]; ring

/-- **P10, the degenerate stratum.** Over a domain with `D(z) ≠ 0`: `C(x,z) = 0` and `N = 0`
force `C(x,y) = 0` (all three blocks share one fixed point), and then `C_x(p) = 0` for all `p`. -/
theorem P10_degenerate [IsDomain R] (x y z : Word) (hD : D X Y z ≠ 0)
    (hxz : wedge X Y x z = 0) (hN : P10N X Y x y z = 0) :
    wedge X Y x y = 0 ∧ ∀ p, wedge X Y x (y ++ wpow z p) = 0 := by
  have hxy : wedge X Y x y = 0 := by
    rw [P10_obstruction X Y x y z hxz, neg_eq_zero] at hN
    exact (mul_eq_zero.1 hN).resolve_left hD
  refine ⟨hxy, fun p => ?_⟩
  have := P10_split X Y x y z p
  rw [hxz, hN, mul_zero, mul_zero, sub_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hD

end Ring

/-! ## The compensation principle -/

section Comp

variable {R : Type*} [CommRing R] {X Y : R}

/-- On a closed orbit, `D` divides every `R`-linear combination of rotation sums. -/
theorem Follows.D_dvd_comb {w : Word} {a : R} (h : Follows X Y w a a) (J : Finset ℕ)
    (c : ℕ → R) : D X Y w ∣ ∑ j ∈ J, c j * S X Y (w.rotate j) :=
  Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (Follows.D_dvd_S_rotate X Y h j) _

variable (X Y) in
/-- `D` itself is a rotation combination: `D(w) = X^{d₀} S^{(1)} - Y S^{(0)}`. -/
theorem D_eq_rotate_comb (d : ℕ) (w : Word) :
    D X Y (d :: w) = X ^ d * S X Y ((d :: w).rotate 1) - Y * S X Y (d :: w) := by
  rw [rotate_one_cons, rotation_recursion]; ring

end Comp

/-- The shift-gcd `G(w) = gcd_{j < o} S^{(j)}(w)` at `(2,3)` (normalised, so `≥ 0`). -/
def rotGcd (w : Word) : ℤ := (Finset.range w.length).gcd fun j => Sz (w.rotate j)

/-- `G` divides every rotation sum. -/
theorem rotGcd_dvd_S_rotate (w : Word) (j : ℕ) : rotGcd w ∣ Sz (w.rotate j) := by
  rcases w with _ | ⟨d, w⟩
  · simp
  · rw [← List.rotate_mod]
    exact Finset.gcd_dvd (Finset.mem_range.2 (Nat.mod_lt _ (by simp)))

/-- `G` divides every `ℤ`-linear combination of rotation sums (any word). -/
theorem rotGcd_dvd_comb (w : Word) (J : Finset ℕ) (c : ℕ → ℤ) :
    rotGcd w ∣ ∑ j ∈ J, c j * Sz (w.rotate j) :=
  Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (rotGcd_dvd_S_rotate w j) _

/-- `G ∣ D` for every word (`cycle-gcd`'s corollary of the rotation recursion). -/
theorem rotGcd_dvd_Dz (w : Word) : rotGcd w ∣ Dz w := by
  rcases w with _ | ⟨d, w'⟩
  · simp
  · rw [Dz, D_eq_rotate_comb]
    have h0 := rotGcd_dvd_S_rotate (d :: w') 0
    have h1 := rotGcd_dvd_S_rotate (d :: w') 1
    rw [List.rotate_zero] at h0
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h0 _)

/-- `G ≥ 0` (it is a normalised gcd). -/
theorem rotGcd_nonneg (w : Word) : 0 ≤ rotGcd w := by
  have := Finset.normalize_gcd (s := Finset.range w.length) (f := fun j => Sz (w.rotate j))
  rw [← Int.abs_eq_normalize] at this
  rw [rotGcd, ← this]; exact abs_nonneg _

/-- `D = 2^E - 3^o` is odd once `E ≥ 1`. -/
theorem Dz_odd {w : Word} (hE : w.sum ≠ 0) : Odd (Dz w) := by
  simp only [Dz, D]
  exact Even.sub_odd ((even_two).pow_of_ne_zero hE) (Odd.pow (by decide))

/-- `3 ∤ D = 2^E - 3^o` once `o ≥ 1`. -/
theorem not_three_dvd_Dz {w : Word} (ho : w ≠ []) : ¬ (3 : ℤ) ∣ Dz w := by
  simp only [Dz, D]
  intro h
  have h3 : (3 : ℤ) ∣ 3 ^ w.length := dvd_pow_self 3 (by simpa using ho)
  have h2 : (3 : ℤ) ∣ 2 ^ w.sum := by simpa using dvd_add h h3
  have := Int.prime_three.dvd_of_dvd_pow h2
  omega

/-- `gcd(2^E - 3^o, 6) = 1` for `o, E ≥ 1`. -/
theorem isCoprime_Dz_six {w : Word} (ho : w ≠ []) (hE : w.sum ≠ 0) : IsCoprime (Dz w) 6 := by
  have h2 : IsCoprime (Dz w) 2 := by
    obtain ⟨m, hm⟩ := Dz_odd hE
    exact ⟨1, -m, by rw [hm]; ring⟩
  have h3 : IsCoprime (Dz w) 3 :=
    ((Prime.coprime_iff_not_dvd Int.prime_three).2 (not_three_dvd_Dz ho)).symm
  simpa using h2.mul_right h3

/-- **Correction to P2/P4/P10.** The shift-gcd of *any* word with `o, E ≥ 1` is coprime to `6`,
so powers of `Y ↦ 3` are as gcd-invisible as powers of `X ↦ 2`. -/
theorem isCoprime_rotGcd_six {w : Word} (ho : w ≠ []) (hE : w.sum ≠ 0) :
    IsCoprime (rotGcd w) 6 :=
  (isCoprime_Dz_six ho hE).of_isCoprime_of_dvd_left (rotGcd_dvd_Dz w)

/-- Stripping `2`- and `3`-power prefactors from a divisibility by a number coprime to `6`. -/
theorem dvd_of_isCoprime_six_of_dvd {d c : ℤ} (hd : IsCoprime d 6) (m n : ℕ)
    (h : d ∣ 2 ^ m * 3 ^ n * c) : d ∣ c := by
  have h6 : IsCoprime d (2 * 3) := by simpa using hd
  exact ((h6.of_mul_right_left.pow_right).mul_right
    h6.of_mul_right_right.pow_right).dvd_of_dvd_mul_left h

/-- Stripping a `2`-power prefactor from a divisibility by an odd number. -/
theorem dvd_of_odd_of_dvd_two_pow_mul {d c : ℤ} (hd : Odd d) (m : ℕ) (h : d ∣ 2 ^ m * c) :
    d ∣ c := by
  obtain ⟨k, hk⟩ := hd
  have h2 : IsCoprime d 2 := ⟨1, -k, by rw [hk]; ring⟩
  exact h2.pow_right.dvd_of_dvd_mul_left h

/-- A nonzero multiple bounds the divisor: `d ∣ c`, `c ≠ 0` ⇒ `|d| ≤ |c|`. -/
theorem abs_le_of_dvd {d c : ℤ} (h : d ∣ c) (hc : c ≠ 0) : |d| ≤ |c| :=
  Int.le_of_dvd (abs_pos.2 hc) ((abs_dvd_abs d c).2 h)

/-- `2^β - 2^α = ± 2^k (2^{|β-α|} - 1)`. -/
theorem two_pow_sub_two_pow (α β : ℕ) :
    ∃ (s : ℤ) (k : ℕ), (s = 1 ∨ s = -1) ∧
      (2 : ℤ) ^ β - 2 ^ α = s * 2 ^ k * (2 ^ Int.natAbs ((β : ℤ) - α) - 1) := by
  rcases le_total α β with h | h
  · refine ⟨1, α, Or.inl rfl, ?_⟩
    rw [show Int.natAbs ((β : ℤ) - α) = β - α by omega, one_mul, mul_sub, ← pow_add,
      Nat.add_sub_cancel' h, mul_one]
  · refine ⟨-1, β, Or.inr rfl, ?_⟩
    rw [show Int.natAbs ((β : ℤ) - α) = α - β by omega]
    have : (2 : ℤ) ^ α = 2 ^ β * 2 ^ (α - β) := by rw [← pow_add, Nat.add_sub_cancel' h]
    rw [this]; ring

/-- **The unit-stripped increment** (P2/P11 "cheap arithmetic"). For `d` coprime to `6`,
`d ∣ 3^m 2^n (2^β - 2^α)` iff `d ∣ 2^{|β-α|} - 1`. -/
theorem dvd_increment_iff {d : ℤ} (hd : IsCoprime d 6) (m n α β : ℕ) :
    d ∣ 3 ^ m * 2 ^ n * (2 ^ β - 2 ^ α) ↔ d ∣ 2 ^ Int.natAbs ((β : ℤ) - α) - 1 := by
  obtain ⟨s, k, hs, hst⟩ := two_pow_sub_two_pow α β
  rw [hst]
  constructor
  · intro h
    have h' : d ∣ 2 ^ (n + k) * 3 ^ m * (s * (2 ^ Int.natAbs ((β : ℤ) - α) - 1)) := by
      rw [pow_add]; convert h using 1; ring
    have := dvd_of_isCoprime_six_of_dvd hd _ _ h'
    rcases hs with rfl | rfl
    · simpa using this
    · rwa [neg_one_mul, dvd_neg] at this
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨3 ^ m * 2 ^ n * s * 2 ^ k * c, by rw [hc]; ring⟩

/-- **P11, essential size of a transposition increment.** For `d` coprime to `6` (e.g. `D` of
any word with `o, E ≥ 1`), `d ∣ S(w') - S(w)` iff `d ∣ 2^{|dᵢ₊₁ - dᵢ|} - 1`. -/
theorem P11_increment_dvd_iff {d : ℤ} (hd : IsCoprime d 6) (p s : Word) (α β : ℕ) :
    d ∣ Sz (p ++ β :: α :: s) - Sz (p ++ α :: β :: s) ↔ d ∣ 2 ^ Int.natAbs ((β : ℤ) - α) - 1 := by
  rw [Sz, Sz, P11_transposition]
  exact dvd_increment_iff hd _ _ _ _

/-! ### Genuine cycles -/

namespace IsSyrCycle

variable {x : ℤ} {o : ℕ}

/-- A genuine cycle is a closed orbit along its gap word. -/
theorem follows (h : IsSyrCycle x o) : Follows (2 : ℤ) 3 (gapWord x o) x x := by
  have hf := follows_gapWord x o
  rwa [h.2.2] at hf

/-- A cycle's gap word is nonempty. -/
theorem ne_nil (h : IsSyrCycle x o) : gapWord x o ≠ [] := by
  rw [← List.length_pos_iff, gapWord_length]; exact h.1

/-- A cycle's gap word is positive. -/
theorem pos (h : IsSyrCycle x o) : (gapWord x o).Pos := gapWord_pos h.2.1 o

/-- `o ≤ E` for a positive word. -/
lemma length_le_sum_of_pos {w : Word} (hw : w.Pos) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons d w ih =>
    simp only [List.length_cons, List.sum_cons]
    have := ih fun y hy => hw y (by simp [hy])
    have := hw d (by simp)
    omega

/-- `E ≥ 1` on a cycle. -/
theorem sum_ne_zero (h : IsSyrCycle x o) : (gapWord x o).sum ≠ 0 := by
  have := length_le_sum_of_pos (IsSyrCycle.pos h)
  rw [gapWord_length] at this; have := h.1; omega

/-- On a genuine cycle `D` is odd. -/
theorem Dz_odd (h : IsSyrCycle x o) : Odd (Dz (gapWord x o)) :=
  CocycleCombine.Dz_odd (IsSyrCycle.sum_ne_zero h)

/-- On a genuine cycle `gcd(D, 6) = 1`. -/
theorem isCoprime_Dz_six (h : IsSyrCycle x o) : IsCoprime (Dz (gapWord x o)) 6 :=
  CocycleCombine.isCoprime_Dz_six (IsSyrCycle.ne_nil h) (IsSyrCycle.sum_ne_zero h)

/-- `D` divides every rotation sum of a cycle. -/
theorem Dz_dvd_S_rotate (h : IsSyrCycle x o) (j : ℕ) :
    Dz (gapWord x o) ∣ Sz ((gapWord x o).rotate j) :=
  Follows.D_dvd_S_rotate _ _ (IsSyrCycle.follows h) j

/-- `D` divides the rotation sum of every word cyclically equivalent to the cycle's word. -/
theorem Dz_dvd_of_isRotated (h : IsSyrCycle x o) {ρ : Word} (hρ : ρ ~r gapWord x o) :
    Dz (gapWord x o) ∣ Sz ρ := by
  obtain ⟨n, hn⟩ := hρ.symm
  rw [← hn]; exact IsSyrCycle.Dz_dvd_S_rotate h n

/-- **Exact gcd on cycles.** `G = gcd_j S^{(j)} = |D|`. -/
theorem rotGcd_eq (h : IsSyrCycle x o) : rotGcd (gapWord x o) = |Dz (gapWord x o)| := by
  refine Int.dvd_antisymm (rotGcd_nonneg _) (abs_nonneg _) ?_ ?_
  · exact (dvd_abs _ _).2 (rotGcd_dvd_Dz _)
  · exact (abs_dvd _ _).2 (Finset.dvd_gcd fun j _ => IsSyrCycle.Dz_dvd_S_rotate h j)

/-- **`G` is odd** on a genuine cycle. -/
theorem rotGcd_odd (h : IsSyrCycle x o) : Odd (rotGcd (gapWord x o)) := by
  rw [IsSyrCycle.rotGcd_eq h, odd_abs]; exact IsSyrCycle.Dz_odd h

/-- **Compensation principle.** Every `ℤ`-linear combination of the rotation sums of a genuine
cycle is divisible by `D = 2^E - 3^o`. -/
theorem Dz_dvd_comb (h : IsSyrCycle x o) (J : Finset ℕ) (c : ℕ → ℤ) :
    Dz (gapWord x o) ∣ ∑ j ∈ J, c j * Sz ((gapWord x o).rotate j) :=
  Follows.D_dvd_comb (IsSyrCycle.follows h) J c

/-- **Compensation ceiling.** A nonzero combination `C` of rotation sums bounds `|2^E - 3^o| ≤ |C|`. -/
theorem abs_Dz_le (h : IsSyrCycle x o) (J : Finset ℕ) (c : ℕ → ℤ)
    (hC : ∑ j ∈ J, c j * Sz ((gapWord x o).rotate j) ≠ 0) :
    |Dz (gapWord x o)| ≤ |∑ j ∈ J, c j * Sz ((gapWord x o).rotate j)| :=
  abs_le_of_dvd (IsSyrCycle.Dz_dvd_comb h J c) hC

/-- **P0 on cycles.** If the cycle's word is `w^{k+1} w'`, then `D ∣ C(w, w')` (the `X`-power
prefactor is dropped because `D` is odd), so `|D| ≤ |C(w,w')|` unless `C(w,w') = 0`. -/
theorem P0_dvd (h : IsSyrCycle x o) {w w' : Word} {k : ℕ}
    (hw : gapWord x o = wpow w (k + 1) ++ w') : Dz (gapWord x o) ∣ wedge (2 : ℤ) 3 w w' := by
  have h1 := IsSyrCycle.Dz_dvd_S_rotate h 0
  have h2 := IsSyrCycle.Dz_dvd_S_rotate h w.length
  rw [List.rotate_zero] at h1
  have := dvd_sub h1 h2
  rw [hw, P0] at this
  rw [← hw] at this
  exact dvd_of_odd_of_dvd_two_pow_mul (IsSyrCycle.Dz_odd h) _ this

/-- **P0 ceiling.** `|2^E - 3^o| ≤ |C(w,w')|` for a genuine cycle with word `w^{k+1} w'`, unless
`C(w,w') = 0` — a bound independent of `k`. -/
theorem P0_ceiling (h : IsSyrCycle x o) {w w' : Word} {k : ℕ}
    (hw : gapWord x o = wpow w (k + 1) ++ w') (hC : wedge (2 : ℤ) 3 w w' ≠ 0) :
    |Dz (gapWord x o)| ≤ |wedge (2 : ℤ) 3 w w'| :=
  abs_le_of_dvd (IsSyrCycle.P0_dvd h hw) hC

end IsSyrCycle

/-! ### Knight's high-cycle obstruction (C9) on genuine cycles -/

/-- At `(2,3)`, if an odd `D(v)` divides `g(v)` it divides `g` of every rotation of `v`. -/
theorem dvd_g_rotate {v : List Bool} (hodd : Odd (Dpv (2 : ℤ) 3 v)) (h : Dpv (2 : ℤ) 3 v ∣ g 2 3 v)
    (n : ℕ) : Dpv (2 : ℤ) 3 v ∣ g 2 3 (v.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate]
    rw [← Dpv_rotate (2 : ℤ) 3 v n] at hodd ih ⊢
    generalize v.rotate n = u at hodd ih ⊢
    rcases u with _ | ⟨b, u⟩
    · simp
    · apply dvd_of_odd_of_dvd_two_pow_mul hodd 1
      rw [pow_one]
      cases b
      · rw [g_rotate_one_false]; exact ih
      · rw [g_rotate_one_true]; exact dvd_add (dvd_mul_of_dvd_right ih _) dvd_rfl

/-- **Knight's edge obstruction (C9a at `X = 2`).** If the odd number `D = 2^E - 3^x` of the
parity vector `1u0` divides both `g(1u0)` and `g(0u1)`, then `|D| = 1`. -/
theorem knight_edge (u : List Bool) (h1 : Dpv (2 : ℤ) 3 (true :: (u ++ [false])) ∣ g 2 3 (true :: (u ++ [false])))
    (h2 : Dpv (2 : ℤ) 3 (true :: (u ++ [false])) ∣ g 2 3 (false :: (u ++ [true]))) :
    (Dpv (2 : ℤ) 3 (true :: (u ++ [false]))).natAbs = 1 := by
  set v := true :: (u ++ [false])
  have hc := C9a (2 : ℤ) 3 u
  have hdvd : Dpv (2 : ℤ) 3 v ∣ 2 ^ (v.length - 1) * 1 := by
    have : (2 : ℤ) ^ (v.length - 1) * 1 = 2 ^ (v.length - 1) * (2 - 1) := by norm_num
    rw [this, ← hc]
    exact dvd_add (dvd_sub (dvd_mul_of_dvd_right h1 _) h2) dvd_rfl
  have hodd : Odd (Dpv (2 : ℤ) 3 v) := by
    simp only [Dpv]
    exact Even.sub_odd ((even_two).pow_of_ne_zero (by simp [v])) (Odd.pow (by decide))
  have := dvd_of_odd_of_dvd_two_pow_mul hodd _ hdvd
  exact Int.isUnit_iff_natAbs_eq.1 (isUnit_of_dvd_one this)

/-- **Knight's theorem, cycle form.** If both `1u0` and `0u1` are rotations of the parity vector
of a genuine cycle (for the high cycle this is Cohn's reverse-equals-conjugate theorem, which is
*assumed* here), then `|2^E - 3^o| = 1`. -/
theorem knight_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (u : List Bool)
    (h1 : pv (gapWord x o) ~r true :: (u ++ [false]))
    (h2 : pv (gapWord x o) ~r false :: (u ++ [true])) : (Dz (gapWord x o)).natAbs = 1 := by
  have hp := IsSyrCycle.pos h
  set w := gapWord x o
  have hD : Dpv (2 : ℤ) 3 (pv w) = Dz w := Dpv_pv _ _ hp
  have hodd : Odd (Dpv (2 : ℤ) 3 (pv w)) := hD ▸ IsSyrCycle.Dz_odd h
  have h0 : Dpv (2 : ℤ) 3 (pv w) ∣ g 2 3 (pv w) := by
    rw [hD, g_pv _ _ hp]; simpa using IsSyrCycle.Dz_dvd_S_rotate h 0
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  have e1 := dvd_g_rotate hodd h0 n1
  have e2 := dvd_g_rotate hodd h0 n2
  rw [hn1] at e1; rw [hn2] at e2
  have hDv : Dpv (2 : ℤ) 3 (pv w) = Dpv (2 : ℤ) 3 (true :: (u ++ [false])) := by
    rw [← hn1, Dpv_rotate]
  rw [hDv] at e1 e2
  rw [← hD, hDv]
  exact knight_edge u e1 e2

/-- **C9b, cycle form.** If `p01` and `p10` are both rotations of a genuine cycle's parity vector,
then `|2^E - 3^o| = 1`. -/
theorem knight_cycle_b {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (p : List Bool)
    (h1 : pv (gapWord x o) ~r p ++ [false, true])
    (h2 : pv (gapWord x o) ~r p ++ [true, false]) : (Dz (gapWord x o)).natAbs = 1 := by
  have hp := IsSyrCycle.pos h
  set w := gapWord x o
  have hD : Dpv (2 : ℤ) 3 (pv w) = Dz w := Dpv_pv _ _ hp
  have hodd : Odd (Dz w) := IsSyrCycle.Dz_odd h
  have h0 : Dpv (2 : ℤ) 3 (pv w) ∣ g 2 3 (pv w) := by
    rw [hD, g_pv _ _ hp]; simpa using IsSyrCycle.Dz_dvd_S_rotate h 0
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  have e1 := dvd_g_rotate (hD ▸ hodd) h0 n1
  have e2 := dvd_g_rotate (hD ▸ hodd) h0 n2
  rw [hn1, hD] at e1; rw [hn2, hD] at e2
  have hc := C9b (2 : ℤ) 3 p
  have hdvd : Dz w ∣ 2 ^ ((p ++ [false, true]).length - 2) * 1 := by
    have : (2 : ℤ) ^ ((p ++ [false, true]).length - 2) * 1 =
        2 ^ ((p ++ [false, true]).length - 2) * (2 - 1) := by norm_num
    rw [this, ← hc]
    exact dvd_sub e1 e2
  exact Int.isUnit_iff_natAbs_eq.1 (isUnit_of_dvd_one (dvd_of_odd_of_dvd_two_pow_mul hodd _ hdvd))

/-! ## P1 and P2 at `(2,3)` -/

/-- **P1.** For the circuit `d^o`: `G · |2^d - 3| = |D|`, i.e. `G = |D|/|2^d - 3|`. -/
theorem P1_rotGcd (d o : ℕ) :
    rotGcd (List.replicate o d) * |(2 : ℤ) ^ d - 3| = |Dz (List.replicate o d)| := by
  have hG : rotGcd (List.replicate o d) = |Sz (List.replicate o d)| := by
    refine Int.dvd_antisymm (rotGcd_nonneg _) (abs_nonneg _) ?_ ?_
    · have := rotGcd_dvd_S_rotate (List.replicate o d) 0
      rw [List.rotate_zero] at this
      exact (dvd_abs _ _).2 this
    · refine (abs_dvd _ _).2 (Finset.dvd_gcd fun j _ => ?_)
      rw [List.rotate_replicate]
  rw [hG, ← abs_mul, mul_comm, Dz, Sz, P1]

/-- Rotations of `d^i e d^j`: any two placements of the single defect are cyclically equivalent. -/
theorem P2_isRotated {d e i j a b : ℕ} (h : i + j = a + b) :
    List.replicate i d ++ e :: List.replicate j d ~r
      List.replicate a d ++ e :: List.replicate b d := by
  have key : ∀ i j : ℕ,
      List.replicate i d ++ e :: List.replicate j d ~r e :: List.replicate (j + i) d := by
    intro i j
    refine ⟨i, ?_⟩
    have := List.rotate_append_length_eq (List.replicate i d) (e :: List.replicate j d)
    rw [List.length_replicate] at this
    rw [this, List.cons_append, ← List.replicate_add]
  have h1 := key i j
  rw [show j + i = b + a by omega] at h1
  exact h1.trans (key a b).symm

/-- **P2, degenerate locus.** At `(2,3)` the P2 core vanishes iff `e = d`. -/
theorem P2_core_eq_zero_iff (d e n : ℕ) :
    (2 : ℤ) ^ (n * d) * (2 ^ e - 2 ^ d) = 0 ↔ e = d := by
  rw [mul_eq_zero, sub_eq_zero]
  simp only [pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or]
  exact ⟨fun h => Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h), fun h => h ▸ rfl⟩

/-- **P2 ceiling.** If a genuine cycle has gap word `d^a e d^b` with `e ≠ d`, then
`|2^E - 3^o| ≤ 2^{|e-d|} - 1`, where `E = (a+b)d + e`, `o = a + b + 1` — a bound independent of
`a, b`. -/
theorem P2_ceiling {x : ℤ} {a b d e : ℕ} (h : IsSyrCycle x (a + b + 1))
    (hw : gapWord x (a + b + 1) = List.replicate a d ++ e :: List.replicate b d) (hde : e ≠ d) :
    |(2 : ℤ) ^ ((a + b) * d + e) - 3 ^ (a + b + 1)| ≤ 2 ^ Int.natAbs ((e : ℤ) - d) - 1 := by
  have hD : Dz (gapWord x (a + b + 1)) = 2 ^ ((a + b) * d + e) - 3 ^ (a + b + 1) := by
    rw [hw, Dz, D]
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul, List.sum_cons,
      List.length_append, List.length_replicate, List.length_cons]
    congr 2; ring
  have hk : 0 < Int.natAbs ((e : ℤ) - d) := by omega
  have hpos : (0 : ℤ) < 2 ^ Int.natAbs ((e : ℤ) - d) - 1 := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ Int.natAbs ((e : ℤ) - d) := pow_le_pow_right₀ (by norm_num) hk
    linarith
  rw [← hD]
  suffices hdiv : Dz (gapWord x (a + b + 1)) ∣ 2 ^ Int.natAbs ((e : ℤ) - d) - 1 from
    (abs_le_of_dvd hdiv hpos.ne').trans (abs_of_pos hpos).le
  obtain ⟨n, hn⟩ | hab : (∃ n, a + b = n + 1) ∨ a + b = 0 :=
    (Nat.eq_zero_or_pos (a + b)).elim Or.inr fun hp => Or.inl ⟨a + b - 1, by omega⟩
  · have h1 := IsSyrCycle.Dz_dvd_of_isRotated h (hw ▸ P2_isRotated (d := d) (e := e)
      (i := n) (j := 1) (a := a) (b := b) (by omega))
    have h2 := IsSyrCycle.Dz_dvd_of_isRotated h (hw ▸ P2_isRotated (d := d) (e := e)
      (i := n + 1) (j := 0) (a := a) (b := b) (by omega))
    have h3 := dvd_sub h1 h2
    simp only [List.replicate_one, List.replicate_zero] at h3
    rw [Sz, Sz, P2_last, ← one_mul ((2 : ℤ) ^ (n * d)), ← pow_zero (3 : ℤ)] at h3
    exact (dvd_increment_iff (IsSyrCycle.isCoprime_Dz_six h) _ _ _ _).1 h3
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    have h1 := IsSyrCycle.Dz_dvd_S_rotate h 0
    rw [List.rotate_zero, hw] at h1
    simp only [List.replicate_zero, List.nil_append, Sz, S_singleton] at h1
    rw [hw]
    exact h1.trans (one_dvd _)

/-- **P2 non-vacuity.** `D(1,1,1,4,1,1,1) = 2^{10} - 3^7 = -1163`. -/
theorem P2_example_Dz : Dz [1, 1, 1, 4, 1, 1, 1] = -1163 := by
  norm_num [Dz, D]

/-- **P2 non-vacuity.** The ceiling `|D| ≤ 2^3 - 1 = 7` excludes the word `(1,1,1,4,1,1,1)`:
no genuine cycle has it as gap word. -/
theorem P2_example_not_cycle (x : ℤ) : ¬ (IsSyrCycle x 7 ∧ gapWord x 7 = [1, 1, 1, 4, 1, 1, 1]) := by
  rintro ⟨h, hw⟩
  have := P2_ceiling (a := 3) (b := 3) (d := 1) (e := 4) h hw (by decide)
  norm_num at this

/-! ## P9 at `(2,3)` -/

/-- Block rotation is a letter rotation: `flatten (us.rotate k) ~r flatten us`. -/
theorem flatten_rotate_isRotated (us : List Word) (k : ℕ) : (us.rotate k).flatten ~r us.flatten := by
  rw [List.rotate_eq_drop_append_take_mod, List.flatten_append]
  conv_rhs => rw [← List.take_append_drop (k % us.length) us, List.flatten_append]
  exact List.isRotated_append

/-- **P9, `q = 2` ceiling.** On a genuine cycle whose word is a balanced pair `u₁u₂`
(`len u₁ = len u₂ = o'`, `|u₁| = |u₂| = E'`), `(2^{E'} + 3^{o'}) ∣ (S(u₂) - S(u₁))`. -/
theorem P9_pair_ceiling {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {u₁ u₂ : Word}
    (hw : gapWord x o = u₁ ++ u₂) (hl : u₁.length = u₂.length) (hs : u₁.sum = u₂.sum) :
    (2 : ℤ) ^ u₁.sum + 3 ^ u₁.length ∣ Sz u₂ - Sz u₁ := by
  have h1 := IsSyrCycle.Dz_dvd_S_rotate h 0
  have h2 := IsSyrCycle.Dz_dvd_S_rotate h u₁.length
  rw [List.rotate_zero] at h1
  have h3 := dvd_sub h1 h2
  have hodd := IsSyrCycle.Dz_odd h
  rw [hw, List.rotate_append_length_eq, Sz, Sz, P9_pair _ _ _ _ hl hs] at h3
  have hD : Dz (u₁ ++ u₂) = (2 ^ u₁.sum - 3 ^ u₁.length) * (2 ^ u₁.sum + 3 ^ u₁.length) := by
    rw [Dz, D, List.sum_append, List.length_append, ← hl, ← hs]; ring
  rw [hw, hD] at hodd
  rw [hD] at h3
  have hne : (2 : ℤ) ^ u₁.sum - 3 ^ u₁.length ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hodd; exact absurd hodd (by decide)
  rw [show ((3 : ℤ) ^ u₁.length - 2 ^ u₁.sum) * (S 2 3 u₁ - S 2 3 u₂) =
    (2 ^ u₁.sum - 3 ^ u₁.length) * (Sz u₂ - Sz u₁) by simp only [Sz]; ring] at h3
  exact (mul_dvd_mul_iff_left hne).1 h3

/-- **Correction to P9** ("`q = 2` always forces `s₁ = s₂`"): at `(o,E) = (6,11)` the balanced
blocks `u₁ = (1,1,3,2,1,3)`, `u₂ = (5,1,1,1,1,2)` have `s₁ = 1441 ≠ s₂ = 6995` and yet
`2^{11} + 3^6 = 2777` divides `s₂ - s₁ = 5554`. -/
theorem P9_escape :
    let u₁ : Word := [1, 1, 3, 2, 1, 3]
    let u₂ : Word := [5, 1, 1, 1, 1, 2]
    u₁.length = u₂.length ∧ u₁.sum = u₂.sum ∧ Sz u₁ = 1441 ∧ Sz u₂ = 6995 ∧
      (2 : ℤ) ^ u₁.sum + 3 ^ u₁.length ∣ Sz u₂ - Sz u₁ := by
  refine ⟨rfl, rfl, by norm_num [Sz], by norm_num [Sz], ?_⟩
  norm_num [Sz]

/-! ## P11 at `(2,3)`: the uncovered word is the `-17` cycle -/

/-- Reading `gap` and `syr` off an explicit factorisation `3a + 1 = 2^k m`, `m` odd. -/
theorem gap_syr_of_eq {a m : ℤ} {k : ℕ} (hm : Odd m) (h : 3 * a + 1 = 2 ^ k * m) :
    gap a = k ∧ syr a = m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hg : gap a = k := by
    rw [gap, h, padicValInt.mul (by positivity) hm0,
      show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
      padicValNat.prime_pow, padicValInt.eq_zero_of_not_dvd]
    · simp
    · intro h2; exact (Int.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 (by exact_mod_cast h2))
  refine ⟨hg, ?_⟩
  rw [syr, hg, h, Int.mul_ediv_cancel_left _ (by positivity)]

/-- The cycle `-17 → -25 → -37 → -55 → -41 → -61 → -91 → -17`, with gap word `(1,1,1,2,1,1,4)`
(`E = 11`, `o = 7`, `D = -139`). -/
theorem isSyrCycle_neg17 : IsSyrCycle (-17) 7 ∧ gapWord (-17) 7 = [1, 1, 1, 2, 1, 1, 4] := by
  obtain ⟨g1, s1⟩ := gap_syr_of_eq (a := -17) (k := 1) (m := -25) (by decide) (by norm_num)
  obtain ⟨g2, s2⟩ := gap_syr_of_eq (a := -25) (k := 1) (m := -37) (by decide) (by norm_num)
  obtain ⟨g3, s3⟩ := gap_syr_of_eq (a := -37) (k := 1) (m := -55) (by decide) (by norm_num)
  obtain ⟨g4, s4⟩ := gap_syr_of_eq (a := -55) (k := 2) (m := -41) (by decide) (by norm_num)
  obtain ⟨g5, s5⟩ := gap_syr_of_eq (a := -41) (k := 1) (m := -61) (by decide) (by norm_num)
  obtain ⟨g6, s6⟩ := gap_syr_of_eq (a := -61) (k := 1) (m := -91) (by decide) (by norm_num)
  obtain ⟨g7, s7⟩ := gap_syr_of_eq (a := -91) (k := 4) (m := -17) (by decide) (by norm_num)
  refine ⟨⟨by norm_num, by decide, ?_⟩, ?_⟩
  · simp [Function.iterate_succ_apply, s1, s2, s3, s4, s5, s6, s7]
  · simp [gapWord, g1, g2, g3, g4, g5, g6, g7, s1, s2, s3, s4, s5, s6]

/-- The cycle `-5 → -7 → -5` traversed twice: its gap word over `o = 4` is the imprimitive
`(1,2)^2 = (1,2,1,2)` (P3's "`(uv)^q`, `q ≥ 2`, is never a cycle word" holds only for the
minimal period). -/
theorem isSyrCycle_neg5_twice : IsSyrCycle (-5) 4 ∧ gapWord (-5) 4 = wpow [1, 2] 2 := by
  obtain ⟨g1, s1⟩ := gap_syr_of_eq (a := -5) (k := 1) (m := -7) (by decide) (by norm_num)
  obtain ⟨g2, s2⟩ := gap_syr_of_eq (a := -7) (k := 2) (m := -5) (by decide) (by norm_num)
  refine ⟨⟨by norm_num, by decide, ?_⟩, ?_⟩
  · simp [Function.iterate_succ_apply, s1, s2]
  · simp [gapWord, wpow, g1, g2, s1, s2]

/-- **P11, the uncovered word.** All seven rotation sums of `(1,1,1,2,1,1,4)` are divisible by
`D = 2^{11} - 3^7 = -139`, so every certificate `a D + b S(w)` vanishes mod `D` on it: it is the
gap word of the genuine cycle through `-17`, and `G = |D| = 139`. -/
theorem P11_uncovered :
    Dz [1, 1, 1, 2, 1, 1, 4] = -139 ∧ rotGcd [1, 1, 1, 2, 1, 1, 4] = 139 ∧
      ∀ j, Dz [1, 1, 1, 2, 1, 1, 4] ∣ Sz ([1, 1, 1, 2, 1, 1, 4].rotate j) := by
  obtain ⟨h, hw⟩ := isSyrCycle_neg17
  have hD : Dz [1, 1, 1, 2, 1, 1, 4] = -139 := by norm_num [Dz, D]
  refine ⟨hD, ?_, fun j => ?_⟩
  · have := IsSyrCycle.rotGcd_eq h
    rw [hw, hD] at this; simpa using this
  · have := IsSyrCycle.Dz_dvd_S_rotate h j
    rwa [hw] at this

end Syracuse.CocycleCombine
