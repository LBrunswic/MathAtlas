import Syracuse.Basic

/-!
# Zero-sum combinations: the ideal of differences, and the ring `ℤ[1/6]`

Formalizes `approaches/zero-sum-combination` (`RATIONALE.md`, `STATUS.md`, `general-theory.md`).
For `x : ι → R` (`ι` finite) the zero-sum set is
`Z(x) = {∑ αᵢ xᵢ : ∑ αᵢ = 0}` (`zeroSum`). Its value-side name is the ideal of differences
`⟨xᵢ - xⱼ⟩` (`diffIdeal`). `ℤ[1/6]` is `Localization.Away (6 : ℤ)` (`Z6`), and the `6`-free part
`φ` is Basic's `sixFree`.

## Coverage

| Note claim (file) | Lean | Status |
|---|---|---|
| `Z(x) = ⟨xᵢ - xⱼ⟩ = ⟨xᵢ - x₁⟩` (general-theory TL;DR, STATUS) | `zeroSum_eq_diffIdeal`, `zeroSum_eq_span_sub_base`, `span_sub_base_eq_diffIdeal` | proved, in any commutative ring |
| `= gcdᵢ(xᵢ - x₁) ℤ` over `ℤ` | `zeroSum_int_base`, `zeroSum_int` (gcd over all pairs), `span_finset_gcd` | proved |
| translation invariance `Z(xᵢ + c) = Z(xᵢ)` | `zeroSum_add_const` | proved |
| `gcd(xᵢ) = gcd(x₁, gcdᵢ(xᵢ - x₁))`; `⟨xᵢ⟩ = ⟨x₁⟩ + ⟨xᵢ - x₁⟩` | `gcd_eq_gcd_base_diff`, `span_range_eq_sup` | proved |
| `Z = ℤ ⇔` gcd of differences `= 1`; `Z = {0} ⇔` all `xᵢ` equal | `zeroSum_int_eq_top_iff`, `diffIdeal_eq_bot_iff` | proved |
| the `p - 1` consecutive differences generate `Z` | `span_consecutive` | proved |
| "minimal generating set is the `p - 1` consecutive differences" | `zeroSum_int` | corrected: over `ℤ`, `Z` is principal (one generator). `p - 1` is the rank of the coefficient lattice `A_{p-1}`, not the size of a minimal generating set of `Z` |
| `ℤ[1/6]` is a PID (localization of a PID) | `instIsPrincipalIdealRingZ6` | proved |
| Euclidean, with norm `φ` = the `6`-free part | `euclid` (all elements), `euclid_step` (integer representatives) | proved |
| units `= ±2^a 3^b` (`a, b ∈ ℤ`) | `isUnit_algebraMap_iff`, `isUnit_iff` (`x·6^k = ±2^a3^b`), `isUnit_two`, `isUnit_three` | proved |
| `x = ±2^a 3^b φ(x)` | `natAbs_eq_mul_sixFree`, `eq_sign_mul_sixFree`, `associated_sixFree` | proved |
| primes of `ℤ[1/6]` are exactly the `p ≥ 5` | — | not formalized |
| `D = 2^E - 3^o` is coprime to `6` | `Dz_isCoprime_six` | corrected: needs `E ≥ 1` and `o ≥ 1` (true for genuine words); `D([0]) = -2`, `D([]) = 0` |
| `D`-coprime-to-6 divisibility transfers between `ℤ` and `ℤ[1/6]` | `dvd_iff_of_isCoprime` | proved |
| `gcd_j S^{(j)} = |D|` transfers unchanged | — | not formalized (the exact-gcd theorem belongs to `cycle-gcd`; each divisibility transfers by `dvd_iff_of_isCoprime`) |
| `Z(S^{(j)}) = φ(gcd_{i,j}(S^{(i)} - S^{(j)})) ℤ[1/6]` | `zeroSum_Z6`, `zeroSum_rotations` | proved (coefficients in `ℤ[1/6]`) |
| Laurent ring `ℤ[X^{±1},Y^{±1}]` is a UFD, not a PID | — | not formalized (literature) |
| augmentation ideal / root lattice `A_{p-1}` / lattice ideal names; `lattice-and-cocycles.md` (augmentation filtration, dimension subgroups, Fox calculus, Magnus cocycle, cup product); `LITERATURE-REVIEW.md` | — | literature placement, not formalized |
-/

namespace Syracuse.ZeroSumCombination

open Syracuse

/-! ## 1. The zero-sum set in a commutative ring -/

section General

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The zero-sum combinations `Z(x) = {∑ αᵢ xᵢ : ∑ αᵢ = 0}`, coefficients in `R`. -/
def zeroSum [Fintype ι] (x : ι → R) : Set R :=
  {z | ∃ α : ι → R, ∑ i, α i = 0 ∧ ∑ i, α i * x i = z}

/-- The ideal of differences `⟨xᵢ - xⱼ⟩`. -/
def diffIdeal (x : ι → R) : Ideal R := Ideal.span (Set.range fun p : ι × ι => x p.1 - x p.2)

/-- `Z(x) = ⟨xᵢ - x_{i₀}⟩` for any base point `i₀`. -/
theorem zeroSum_eq_span_sub_base [Fintype ι] (x : ι → R) (i₀ : ι) :
    zeroSum x = (Ideal.span (Set.range fun i => x i - x i₀) : Set R) := by
  classical
  ext z
  constructor
  · rintro ⟨α, hα, rfl⟩
    have : ∑ i, α i * x i = ∑ i, α i * (x i - x i₀) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hα, zero_mul, sub_zero]
    rw [SetLike.mem_coe, this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro hz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz
    refine ⟨fun i => c i - if i = i₀ then ∑ j, c j else 0, ?_, ?_⟩
    · simp [Finset.sum_sub_distrib]
    · rw [← hc]
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, smul_eq_mul, mul_sub, Finset.sum_mul]

/-- `⟨xᵢ - x_{i₀}⟩ = ⟨xᵢ - xⱼ⟩`. -/
theorem span_sub_base_eq_diffIdeal (x : ι → R) (i₀ : ι) :
    Ideal.span (Set.range fun i => x i - x i₀) = diffIdeal x := by
  apply le_antisymm
  · exact Ideal.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨(i, i₀), rfl⟩)
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have : x i - x j = (x i - x i₀) - (x j - x i₀) := by ring
    show x i - x j ∈ _
    rw [this]
    exact Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨j, rfl⟩)

/-- **The zero-sum theorem.** `Z(x) = ⟨xᵢ - xⱼ⟩`. -/
theorem zeroSum_eq_diffIdeal [Fintype ι] [Nonempty ι] (x : ι → R) :
    zeroSum x = (diffIdeal x : Set R) := by
  rw [zeroSum_eq_span_sub_base x (Classical.arbitrary ι), span_sub_base_eq_diffIdeal]

/-- **Translation invariance.** `Z(xᵢ + c) = Z(xᵢ)`. -/
theorem zeroSum_add_const [Fintype ι] (x : ι → R) (c : R) :
    zeroSum (fun i => x i + c) = zeroSum x := by
  ext z
  simp only [zeroSum, Set.mem_ofPred_eq, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  constructor
  · rintro ⟨α, hα, rfl⟩; exact ⟨α, hα, by rw [hα, zero_mul, add_zero]⟩
  · rintro ⟨α, hα, rfl⟩; exact ⟨α, hα, by rw [hα, zero_mul, add_zero]⟩

/-- **Base point plus differences.** `⟨xᵢ⟩ = ⟨x_{i₀}⟩ + ⟨xᵢ - x_{i₀}⟩`. -/
theorem span_range_eq_sup (x : ι → R) (i₀ : ι) :
    Ideal.span (Set.range x) = Ideal.span {x i₀} ⊔ Ideal.span (Set.range fun i => x i - x i₀) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have : x i = x i₀ + (x i - x i₀) := by ring
    rw [SetLike.mem_coe, this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ rfl; exact Ideal.subset_span ⟨i₀, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ideal.subset_span ⟨i₀, rfl⟩)

/-- `Z = {0}` iff all the `xᵢ` are equal. -/
theorem diffIdeal_eq_bot_iff (x : ι → R) : diffIdeal x = ⊥ ↔ ∀ i j, x i = x j := by
  simp only [diffIdeal, Ideal.span_eq_bot, Set.mem_range, Prod.exists, forall_exists_index]
  constructor
  · intro h i j; exact sub_eq_zero.mp (h _ i j rfl)
  · rintro h _ i j rfl; rw [h i j, sub_self]

/-- The `p - 1` consecutive differences (simple roots `e_{k+1} - e_k`) already generate. -/
theorem span_consecutive {n : ℕ} (x : Fin (n + 1) → R) :
    Ideal.span (Set.range fun k : Fin n => x k.succ - x k.castSucc) = diffIdeal x := by
  rw [← span_sub_base_eq_diffIdeal x 0]
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have : x k.succ - x k.castSucc = (x k.succ - x 0) - (x k.castSucc - x 0) := by ring
    show x k.succ - x k.castSucc ∈ _
    rw [this]
    exact Ideal.sub_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ideal.subset_span ⟨_, rfl⟩)
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    induction i using Fin.induction with
    | zero => simp
    | succ k ih =>
      have : x k.succ - x 0 = (x k.succ - x k.castSucc) + (x k.castSucc - x 0) := by ring
      show x k.succ - x 0 ∈ _
      rw [this]
      exact Ideal.add_mem _ (Ideal.subset_span ⟨k, rfl⟩) ih

end General

/-! ## 2. Over `ℤ`: the generator is the gcd of the differences -/

section Int

variable {ι : Type*} [Fintype ι]

/-- In `ℤ`, the ideal spanned by finitely many integers is generated by their gcd. -/
theorem span_finset_gcd {β : Type*} (s : Finset β) (f : β → ℤ) :
    Ideal.span {s.gcd f} = Ideal.span (f '' s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.gcd_insert, span_gcd, Finset.coe_insert, Set.image_insert_eq,
      Ideal.span_insert, ih, ← Ideal.span_insert]

/-- `⟨xᵢ - xⱼ⟩ = gcd_{i,j}(xᵢ - xⱼ) ℤ`. -/
theorem diffIdeal_eq_span_gcd (x : ι → ℤ) :
    diffIdeal x = Ideal.span {Finset.univ.gcd fun p : ι × ι => x p.1 - x p.2} := by
  rw [span_finset_gcd, Finset.coe_univ, Set.image_univ, diffIdeal]

/-- **Zero-sum theorem over `ℤ`.** `Z(x) = gcd_{i,j}(xᵢ - xⱼ) ℤ`. -/
theorem zeroSum_int [Nonempty ι] (x : ι → ℤ) :
    zeroSum x = (Ideal.span {Finset.univ.gcd fun p : ι × ι => x p.1 - x p.2} : Set ℤ) := by
  rw [zeroSum_eq_diffIdeal, diffIdeal_eq_span_gcd]

/-- **Zero-sum theorem over `ℤ`, base-point form.** `Z(x) = gcdᵢ(xᵢ - x_{i₀}) ℤ`. -/
theorem zeroSum_int_base (x : ι → ℤ) (i₀ : ι) :
    zeroSum x = (Ideal.span {Finset.univ.gcd fun i => x i - x i₀} : Set ℤ) := by
  rw [zeroSum_eq_span_sub_base x i₀, span_finset_gcd, Finset.coe_univ, Set.image_univ]

/-- **gcd factorization.** `gcd(xᵢ) = gcd(x_{i₀}, gcdᵢ(xᵢ - x_{i₀}))`. -/
theorem gcd_eq_gcd_base_diff (x : ι → ℤ) (i₀ : ι) :
    Finset.univ.gcd x = gcd (x i₀) (Finset.univ.gcd fun i => x i - x i₀) := by
  rw [← Finset.normalize_gcd, ← normalize_gcd (x i₀)]
  apply normalize_eq_normalize
  · exact dvd_gcd (Finset.gcd_dvd (Finset.mem_univ _))
      (Finset.dvd_gcd fun i _ => dvd_sub (Finset.gcd_dvd (Finset.mem_univ _))
        (Finset.gcd_dvd (Finset.mem_univ _)))
  · refine Finset.dvd_gcd fun i _ => ?_
    have : x i = (x i - x i₀) + x i₀ := by ring
    rw [this]
    exact dvd_add ((gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i)))
      (gcd_dvd_left _ _)

/-- `Z = ℤ` iff the gcd of the differences is `1`. -/
theorem zeroSum_int_eq_top_iff [Nonempty ι] (x : ι → ℤ) :
    zeroSum x = Set.univ ↔ (Finset.univ.gcd fun p : ι × ι => x p.1 - x p.2) = 1 := by
  rw [zeroSum_int]
  constructor
  · intro h
    have h1 : (1 : ℤ) ∈ Ideal.span {Finset.univ.gcd fun p : ι × ι => x p.1 - x p.2} := by
      rw [← SetLike.mem_coe, h]; trivial
    rw [Ideal.mem_span_singleton] at h1
    rw [← Finset.normalize_gcd]
    exact normalize_eq_one.mpr (isUnit_of_dvd_one h1)
  · intro h; rw [h, Ideal.span_singleton_one]; rfl

end Int

/-! ## 3. The ring `ℤ[1/6]` -/

section Z6

/-- `ℤ[1/6] = ℤ[1/2, 1/3]`, the localization of `ℤ` away from `6`. -/
abbrev Z6 := Localization.Away (6 : ℤ)

/-- The powers of `6` are non-zero-divisors. -/
lemma powers_six_le : Submonoid.powers (6 : ℤ) ≤ nonZeroDivisors ℤ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num)

instance : IsDomain Z6 := IsLocalization.isDomain_localization powers_six_le

/-- `ℤ ↪ ℤ[1/6]`. -/
lemma algebraMap_injective : Function.Injective (algebraMap ℤ Z6) :=
  IsLocalization.injective Z6 powers_six_le

/-- **`ℤ[1/6]` is a PID**: every ideal is the extension of its contraction, which is principal. -/
instance instIsPrincipalIdealRingZ6 : IsPrincipalIdealRing Z6 where
  principal J := by
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.comap (algebraMap ℤ Z6) J)).principal
    refine ⟨⟨algebraMap ℤ Z6 a, ?_⟩⟩
    have := IsLocalization.map_under (Submonoid.powers (6 : ℤ)) Z6 J
    rw [← this]
    change Ideal.map _ (Ideal.comap _ J) = _
    rw [ha, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]

/-- `6` is a unit of `ℤ[1/6]`. -/
lemma isUnit_six : IsUnit (algebraMap ℤ Z6 6) := IsLocalization.Away.algebraMap_isUnit 6

/-- `2` is a unit of `ℤ[1/6]`. -/
lemma isUnit_two : IsUnit (algebraMap ℤ Z6 2) :=
  isUnit_of_mul_isUnit_left (y := algebraMap ℤ Z6 3) (by rw [← map_mul]; exact isUnit_six)

/-- `3` is a unit of `ℤ[1/6]`. -/
lemma isUnit_three : IsUnit (algebraMap ℤ Z6 3) :=
  isUnit_of_mul_isUnit_right (x := algebraMap ℤ Z6 2) (by rw [← map_mul]; exact isUnit_six)

/-- Every element of `ℤ[1/6]` is an integer times the unit `6^{-k}`. -/
theorem exists_int_mul_unit (x : Z6) :
    ∃ (z : ℤ) (k : ℕ), x * algebraMap ℤ Z6 (6 ^ k) = algebraMap ℤ Z6 z := by
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (6 : ℤ)) x
  obtain ⟨k, hk⟩ := s.2
  refine ⟨z, k, ?_⟩
  simp only
  rw [show (6 : ℤ) ^ k = s by exact hk, IsLocalization.mk'_spec]

/-- The divisors of `6^k` are the `2^a 3^b`. -/
lemma dvd_six_pow_iff (n k : ℕ) (h : n ∣ 6 ^ k) : ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
  rw [show (6 : ℕ) ^ k = 2 ^ k * 3 ^ k by rw [← mul_pow]; rfl] at h
  obtain ⟨n1, n2, h1, h2, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  exact ⟨a, b, rfl⟩

/-- **Units, integer form.** An integer is a unit of `ℤ[1/6]` iff it is `±2^a 3^b`. -/
theorem isUnit_algebraMap_iff (z : ℤ) :
    IsUnit (algebraMap ℤ Z6 z) ↔ ∃ a b : ℕ, z = 2 ^ a * 3 ^ b ∨ z = -(2 ^ a * 3 ^ b) := by
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    obtain ⟨m, k, hm⟩ := exists_int_mul_unit w
    have : algebraMap ℤ Z6 (z * m) = algebraMap ℤ Z6 (6 ^ k) := by
      rw [map_mul, ← hm, ← mul_assoc, hw, one_mul]
    have hzm := algebraMap_injective this
    have hdvd : z.natAbs ∣ 6 ^ k := by
      have := congrArg Int.natAbs hzm
      rw [Int.natAbs_mul, Int.natAbs_pow] at this
      exact ⟨m.natAbs, this.symm⟩
    obtain ⟨a, b, hab⟩ := dvd_six_pow_iff _ k hdvd
    refine ⟨a, b, ?_⟩
    rcases Int.natAbs_eq z with h | h
    · left; rw [h, hab]; push_cast; ring
    · right; rw [h, hab]; push_cast; ring
  · rintro ⟨a, b, rfl | rfl⟩
    · rw [map_mul, map_pow, map_pow]
      exact (isUnit_two.pow a).mul (isUnit_three.pow b)
    · rw [map_neg, map_mul, map_pow, map_pow]
      exact ((isUnit_two.pow a).mul (isUnit_three.pow b)).neg

/-- **Units.** `x ∈ ℤ[1/6]` is a unit iff `x · 6^k = ±2^a 3^b` for some `k, a, b`, i.e. iff
`x = ±2^{a'} 3^{b'}` with `a', b' ∈ ℤ`. -/
theorem isUnit_iff (x : Z6) :
    IsUnit x ↔ ∃ (z : ℤ) (k : ℕ), x * algebraMap ℤ Z6 (6 ^ k) = algebraMap ℤ Z6 z ∧
      ∃ a b : ℕ, z = 2 ^ a * 3 ^ b ∨ z = -(2 ^ a * 3 ^ b) := by
  obtain ⟨z, k, hz⟩ := exists_int_mul_unit x
  have h6 : IsUnit (algebraMap ℤ Z6 (6 ^ k)) := by rw [map_pow]; exact isUnit_six.pow k
  constructor
  · intro hx
    refine ⟨z, k, hz, (isUnit_algebraMap_iff z).mp ?_⟩
    rw [← hz]; exact hx.mul h6
  · rintro ⟨z', k', hz', hu⟩
    have := (isUnit_algebraMap_iff z').mpr hu
    rw [← hz'] at this
    exact isUnit_of_mul_isUnit_left this

/-- **Transfer.** For `D` coprime to `6`, `D ∣ n` in `ℤ[1/6]` iff `D ∣ n` in `ℤ`. -/
theorem dvd_iff_of_isCoprime {D n : ℤ} (hD : IsCoprime D 6) :
    algebraMap ℤ Z6 D ∣ algebraMap ℤ Z6 n ↔ D ∣ n := by
  refine ⟨fun ⟨w, hw⟩ => ?_, map_dvd _⟩
  obtain ⟨m, k, hm⟩ := exists_int_mul_unit w
  have : algebraMap ℤ Z6 (n * 6 ^ k) = algebraMap ℤ Z6 (D * m) := by
    rw [map_mul, hw, map_mul, ← hm]; ring
  have h := algebraMap_injective this
  exact (hD.pow_right (n := k)).dvd_of_dvd_mul_right ⟨m, h⟩

/-- `D = 2^E - 3^o` is coprime to `6` once `E ≥ 1` and `o ≥ 1` (e.g. any nonempty positive word). -/
theorem Dz_isCoprime_six (w : Word) (hE : 1 ≤ w.sum) (ho : 1 ≤ w.length) :
    IsCoprime (Dz w) 6 := by
  rw [show (6 : ℤ) = 2 * 3 by norm_num]
  apply IsCoprime.mul_right
  · rw [isCoprime_comm, Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible]
    intro h
    have h2 : (2 : ℤ) ∣ 2 ^ w.sum := dvd_pow_self 2 (by omega)
    have : (2 : ℤ) ∣ 3 ^ w.length := by
      have := dvd_sub h2 h; simp only [Dz, D, sub_sub_cancel] at this; exact this
    have := Int.prime_two.dvd_of_dvd_pow this
    norm_num at this
  · rw [isCoprime_comm, Irreducible.coprime_iff_not_dvd Int.prime_three.irreducible]
    intro h
    have h3 : (3 : ℤ) ∣ 3 ^ w.length := dvd_pow_self 3 (by omega)
    have : (3 : ℤ) ∣ 2 ^ w.sum := by
      have := dvd_add h h3; simp only [Dz, D, sub_add_cancel] at this; exact this
    have := Int.prime_three.dvd_of_dvd_pow this
    norm_num at this

/-- The hypothesis `E ≥ 1` is needed: `D([0]) = 1 - 3 = -2` is not coprime to `6`. -/
example : ¬ IsCoprime (Dz [0]) 6 := by
  intro h
  have : IsCoprime (-2 : ℤ) 6 := by simpa [Dz, D] using h
  rw [Int.isCoprime_iff_gcd_eq_one] at this
  norm_num at this

/-- `|z| = 2^a 3^b φ(z)`. -/
theorem natAbs_eq_mul_sixFree (z : ℤ) : ∃ a b : ℕ, z.natAbs = 2 ^ a * 3 ^ b * sixFree z := by
  refine ⟨z.natAbs.factorization 2, (ordCompl[2] z.natAbs).factorization 3, ?_⟩
  rw [mul_assoc, sixFree, Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]

/-- `z = ±2^a 3^b φ(z)`. -/
theorem eq_sign_mul_sixFree (z : ℤ) :
    ∃ (a b : ℕ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ z = ε * (2 ^ a * 3 ^ b * sixFree z : ℕ) := by
  obtain ⟨a, b, hab⟩ := natAbs_eq_mul_sixFree z
  refine ⟨a, b, ?_⟩
  rcases Int.natAbs_eq z with h | h
  · exact ⟨1, Or.inl rfl, by rw [← hab, one_mul]; exact h⟩
  · exact ⟨-1, Or.inr rfl, by rw [← hab, neg_one_mul]; exact h⟩

/-- In `ℤ[1/6]` every integer is associated to its `6`-free part: `φ` is "up to units". -/
theorem associated_sixFree (z : ℤ) :
    Associated (algebraMap ℤ Z6 z) (algebraMap ℤ Z6 (sixFree z)) := by
  obtain ⟨a, b, hab⟩ := natAbs_eq_mul_sixFree z
  have hu : IsUnit (algebraMap ℤ Z6 (2 ^ a * 3 ^ b)) :=
    (isUnit_algebraMap_iff _).mpr ⟨a, b, Or.inl rfl⟩
  have hz : z = (2 ^ a * 3 ^ b : ℤ) * (sixFree z : ℤ) ∨
      z = -((2 ^ a * 3 ^ b : ℤ) * (sixFree z : ℤ)) := by
    rcases Int.natAbs_eq z with h | h
    · left; conv_lhs => rw [h]
      rw [hab]; push_cast; ring
    · right; conv_lhs => rw [h]
      rw [hab]; push_cast; ring
  generalize sixFree z = s at hz ⊢
  rcases hz with rfl | rfl
  · rw [map_mul]
    exact associated_unit_mul_left _ _ hu
  · rw [map_neg, map_mul]
    exact (associated_unit_mul_left _ _ hu).neg_left

/-- `φ(-z) = φ(z)`. -/
theorem sixFree_neg (z : ℤ) : sixFree (-z) = sixFree z := by simp [sixFree]

/-- `φ(t) ≤ t`. -/
theorem sixFree_le (t : ℕ) : sixFree t ≤ t := by
  simp only [sixFree, Int.natAbs_natCast]
  exact (Nat.ordCompl_le _ 3).trans (Nat.ordCompl_le _ 2)

/-- `φ(z) > 0` for `z ≠ 0`. -/
theorem sixFree_pos {z : ℤ} (hz : z ≠ 0) : 0 < sixFree z := by
  simp only [sixFree]
  exact Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 (Int.natAbs_ne_zero.mpr hz)).ne'

/-- `φ(2^a 3^b t) = φ(t)`. -/
theorem sixFree_two_pow_three_pow_mul (a b t : ℕ) :
    sixFree ((2 ^ a * 3 ^ b * t : ℕ) : ℤ) = sixFree t := by
  simp only [sixFree, Int.natAbs_natCast]
  rw [mul_assoc, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two, Nat.ordCompl_mul,
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd (3 ^ b) Nat.prime_two).mpr
      (Or.inr fun h => by have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h; omega),
    Nat.ordCompl_self_pow_mul _ _ Nat.prime_three]

/-- **Euclidean step on integer representatives.** For `y ≠ 0`:
`x = q y + r` in `ℤ[1/6]` with `r ∈ ℤ` and `φ(r) < φ(y)`. -/
theorem euclid_step (x y : ℤ) (hy : y ≠ 0) :
    ∃ (q : Z6) (r : ℤ), algebraMap ℤ Z6 x = q * algebraMap ℤ Z6 y + algebraMap ℤ Z6 r ∧
      sixFree r < sixFree y := by
  obtain ⟨a, b, ε, hε, hx⟩ := eq_sign_mul_sixFree x
  obtain ⟨a', b', ε', hε', hy'⟩ := eq_sign_mul_sixFree y
  set m := sixFree x
  set n := sixFree y
  have hn : 0 < n := sixFree_pos hy
  have hv : IsUnit (algebraMap ℤ Z6 (ε' * (2 ^ a' * 3 ^ b' : ℕ))) := by
    rw [isUnit_algebraMap_iff]
    refine ⟨a', b', ?_⟩
    rcases hε' with rfl | rfl
    · left; push_cast; ring
    · right; push_cast; ring
  obtain ⟨v, hv⟩ := hv
  refine ⟨algebraMap ℤ Z6 (ε * (2 ^ a * 3 ^ b * (m / n) : ℕ)) * ↑v⁻¹,
    ε * (2 ^ a * 3 ^ b * (m % n) : ℕ), ?_, ?_⟩
  · have hyv : algebraMap ℤ Z6 y = v * algebraMap ℤ Z6 n := by
      rw [hv, ← map_mul]; congr 1; rw [hy']; push_cast; ring
    rw [hyv, ← mul_assoc, mul_assoc _ (↑v⁻¹ : Z6), Units.inv_mul, mul_one, ← map_mul, ← map_add]
    congr 1
    rw [hx]
    conv_lhs => rw [← Nat.div_add_mod m n]
    push_cast; ring
  · rcases hε with rfl | rfl
    · rw [one_mul, sixFree_two_pow_three_pow_mul]
      exact (sixFree_le _).trans_lt (Nat.mod_lt _ hn)
    · rw [neg_one_mul, sixFree_neg, sixFree_two_pow_three_pow_mul]
      exact (sixFree_le _).trans_lt (Nat.mod_lt _ hn)

/-- **`ℤ[1/6]` is Euclidean for `φ`.** For `Y ≠ 0`, `X = q Y + r` where `r` and `Y` are associated
to integers `r'`, `y'` with `φ(r') < φ(y')` (`φ` is well defined up to units). -/
theorem euclid (X Y : Z6) (hY : Y ≠ 0) :
    ∃ (q r : Z6) (r' y' : ℤ), X = q * Y + r ∧ Associated r (algebraMap ℤ Z6 r') ∧
      Associated Y (algebraMap ℤ Z6 y') ∧ sixFree r' < sixFree y' := by
  obtain ⟨x, k, hx⟩ := exists_int_mul_unit X
  obtain ⟨y, l, hy⟩ := exists_int_mul_unit Y
  obtain ⟨u, hu⟩ : IsUnit (algebraMap ℤ Z6 (6 ^ k)) := by rw [map_pow]; exact isUnit_six.pow k
  obtain ⟨w, hw⟩ : IsUnit (algebraMap ℤ Z6 (6 ^ l)) := by rw [map_pow]; exact isUnit_six.pow l
  rw [← hu] at hx
  rw [← hw] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hY (by simpa using congrArg (· * (↑w⁻¹ : Z6)) hy)
  obtain ⟨q, r, hqr, hlt⟩ := euclid_step x y hy0
  refine ⟨q * w * ↑u⁻¹, algebraMap ℤ Z6 r * ↑u⁻¹, r, y, ?_, ?_, ?_, hlt⟩
  · have : X = algebraMap ℤ Z6 x * ↑u⁻¹ := by rw [← hx, mul_assoc, Units.mul_inv, mul_one]
    rw [this, hqr, ← hy]
    ring
  · exact associated_mul_unit_left _ _ (Units.isUnit _)
  · rw [← hy]; exact associated_mul_unit_right _ _ (Units.isUnit _)

/-- **Principality in `ℤ[1/6]`.** For integers `xᵢ`, the zero-sum ideal in `ℤ[1/6]` is generated
by the `6`-free part of the gcd of the differences. -/
theorem zeroSum_Z6 {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℤ) :
    zeroSum (fun i => algebraMap ℤ Z6 (x i)) =
      (Ideal.span {algebraMap ℤ Z6
        (sixFree (Finset.univ.gcd fun p : ι × ι => x p.1 - x p.2))} : Set Z6) := by
  rw [zeroSum_eq_diffIdeal]
  congr 1
  rw [← Ideal.span_singleton_eq_span_singleton.mpr (associated_sixFree _), ← Set.image_singleton,
    ← Ideal.map_span, ← diffIdeal_eq_span_gcd, diffIdeal, diffIdeal, Ideal.map_span,
    ← Set.range_comp]
  congr 1
  ext p; simp

/-- **Rotation sums.** `Z(S^{(0)}, …, S^{(o-1)}) = φ(gcd_{i,j}(S^{(i)} - S^{(j)})) ℤ[1/6]`. -/
theorem zeroSum_rotations (w : Word) (hw : w ≠ []) :
    zeroSum (fun j : Fin w.length => algebraMap ℤ Z6 (Sz (w.rotate j))) =
      (Ideal.span {algebraMap ℤ Z6 (sixFree (Finset.univ.gcd
        fun p : Fin w.length × Fin w.length => Sz (w.rotate p.1) - Sz (w.rotate p.2)))} :
          Set Z6) := by
  have : Nonempty (Fin w.length) := ⟨⟨0, List.length_pos_iff.mpr hw⟩⟩
  exact zeroSum_Z6 _

end Z6

end Syracuse.ZeroSumCombination
