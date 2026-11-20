import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Multiplicity
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# ℤ/2ℤ-rings and their 2-adic valuation

The hypothesis of `def:ring_define` — `syracuse.tex:54` (unmarked here: this module carries the notion
of ℤ/2ℤ-ring and the valuation `ν₂` that the definition uses, the maps themselves are in
`Syracuse.Base`). The notion is introduced, unlabelled, at `syracuse.tex:50–52`:

> one notices that the definition makes sense in any interal commutative unitary ring $A$ such that
> $A/2A \simeq \ZZ/2\ZZ$.  Indeed, in such a ring, $2\neq 0$ and if $x\notin 2A$ then $3x+1\in 2A$.
> Furthermore, if $x\in 2A$, there exists $y\in A$ such that $2y=x$, and two such $y$ are equal since
> the ring is integral.

> We notice that if $\bigcap_{n\in \NN} (2A)^n \neq \{0\}$ then there exists an infinite Syracuse
> sequence in $2A$. We would like to exclude such a situation and thus assume $A$ is noetherian
> (which thus exclude this situation by Krull intersection Theorem).
> In the following, a noetherian ring $A$ such that $A/2A \simeq \ZZ/2\ZZ$ is called a
> $\ZZ/2\ZZ$-ring. In such a ring, the 2-valuation is well defined
> $\nu_2(x):= \max \{n\in \NN ~|~ x\in 2^n A\}$

## What is here

* `Syracuse.IsZ2Ring A`: a commutative ring that is a domain ("integral", l.50), noetherian (l.51–52)
  and has `A ⧸ 2A ≃+* ℤ/2ℤ` (l.52). Its parity dichotomy: every `x` is in `2A` or in `2A + 1`, never
  both (`IsZ2Ring.two_dvd_or_odd`, `IsZ2Ring.odd_iff_not_two_dvd`); the converse constructor
  `IsZ2Ring.of_parity`; the instances `ℤ`, `ℤ_[2]`, and `ZMod 2`.
* Krull (l.51): `IsZ2Ring.iInf_span_two_pow_eq_bot`, `⋂ₙ (2A)ⁿ = 0`.
* `Syracuse.nu2 x = emultiplicity 2 x : ℕ∞`, and its faithfulness to the printed `max`:
  `nu2_eq_coe_iff` (`ν₂ x = n` iff `n` is the greatest `m` with `x ∈ 2ᵐA`), `exists_isGreatest`
  (the max exists for `x ≠ 0`, the paper's "well defined"), `nu2_eq_top_iff` (`ν₂ x = ⊤` iff `x = 0`).
* `Syracuse.v2`, the `ℕ`-valued `ν₂` (Mathlib's `multiplicity`; junk value `1` at `0`), and
  `Syracuse.divPow2 x n`, the quotient `x / 2ⁿ`, unique when `2 ≠ 0` (`divPow2_unique`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| commutative unitary ring | ✓ carried (`CommRing`) |
| integral (l.50; not repeated in the definition l.52) | ✓ carried (`IsDomain`), a reading: see SCOPE |
| noetherian (l.51–52) | ✓ carried (`IsNoetherianRing`) |
| `A/2A ≃ ℤ/2ℤ` (l.52) | ✓ carried (`Nonempty (A ⧸ Ideal.span {2} ≃+* ZMod 2)`) |

## SCOPE (disclosed)

* **Reading: integral.** The definition at l.52 says "a noetherian ring", the sentence at l.50 says
  "integral commutative unitary ring". `IsZ2Ring` includes `IsDomain`. Without it, `ZMod 6` is
  noetherian with `A ⧸ 2A ≃+* ℤ/2ℤ`, but halves are not unique (`2 * 3 = 2 * 0`) and the nonzero
  element `2` has `ν₂ 2 = ⊤` (`zmod6_witness`): neither "two such y are equal" nor "ν₂ is well
  defined" survives, and `lem:ring_maps_rhs_n_` fails even though `2 ≠ 0`
  (`Syracuse.rhs_zmod6_not_injOn`, in `Syracuse.Base`). A question for the author.
* **Finding: "in such a ring, 2 ≠ 0" (l.50) is false for `A = ℤ/2ℤ` itself**, which is integral,
  noetherian and has `A/2A = A ≃ ℤ/2ℤ` (`instIsZ2RingZMod2`, `two_eq_zero_zmod2`). It is the only
  exception: in a ℤ/2ℤ-ring, `2 = 0` iff `A ≃+* ℤ/2ℤ` (`IsZ2Ring.two_eq_zero_iff`). In that ring
  halves are not unique (every `y` has `2y = 0`); and if "such a ring" in the last sentence of
  l.50 means any ℤ/2ℤ-ring (it may mean only the rings named just before it), "`4 ≠ 0`" fails
  for `ℤ/2ℤ` too.
  With `2 ≠ 0`, halves and quotients by `2ⁿ` are unique (`divPow2_unique`) and `A` has
  characteristic zero (`IsZ2Ring.charZero_of_two_ne_zero`).
* `ν₂ 0` is not defined by the paper (the set `{n | 0 ∈ 2ⁿA}` is all of `ℕ`); here `nu2 0 = ⊤`,
  and the `ℕ`-valued `v2 0 = 1` is Mathlib's junk value, never used where the paper's `ν₂` is
  meant without the hypothesis `x ≠ 0`.
* The 2-completion `A₂` and the claim `A₂ ≃ ℤ₂` (l.52) are not this module's (target
  `T-syr-rep`); note that `ZMod 2` also contradicts `A₂ ≃ ℤ₂`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

/-- **ℤ/2ℤ-ring** (`syracuse.tex:50–52`): an integral, noetherian, commutative unitary ring `A` with
`A/2A ≃ ℤ/2ℤ`. -/
class IsZ2Ring (A : Type*) [CommRing A] : Prop extends IsDomain A, IsNoetherianRing A where
  /-- `A/2A ≃ ℤ/2ℤ`. -/
  quotient_two : Nonempty ((A ⧸ Ideal.span {(2 : A)}) ≃+* ZMod 2)

section General

variable {A : Type*} [CommRing A]

/-- The quotient by `2A` is `ℤ/2ℤ` as soon as `2A` has exactly the two cosets `2A` and `2A + 1`
(no domain hypothesis). -/
theorem quotient_two_of_parity (h1 : ¬ (2 : A) ∣ 1) (h : ∀ x : A, (2 : A) ∣ x ∨ (2 : A) ∣ x - 1) :
    Nonempty ((A ⧸ Ideal.span {(2 : A)}) ≃+* ZMod 2) := by
  set I := Ideal.span {(2 : A)} with hIdef
  have hI : I ≠ ⊤ := by
    intro htop
    apply h1
    rw [← Ideal.mem_span_singleton, ← hIdef, htop]
    exact Submodule.mem_top
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : CharP (A ⧸ I) 2 := by
    rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
    rw [show ((2 : ℕ) : A ⧸ I) = Ideal.Quotient.mk I 2 by rw [Nat.cast_ofNat, map_ofNat],
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 dvd_rfl
  let φ : ZMod 2 →+* A ⧸ I := ZMod.castHom (dvd_refl 2) (A ⧸ I)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rcases h x with hx | hx
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.2 hx
    · refine ⟨1, ?_⟩
      rw [map_one, ← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton.2 hx
  exact ⟨(RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩).symm⟩

/-- An odd element is not in `2A` when `1 ∉ 2A`. -/
theorem not_two_dvd_of_odd (h1 : ¬ (2 : A) ∣ 1) {x : A} (hx : Odd x) : ¬ (2 : A) ∣ x := by
  obtain ⟨m, rfl⟩ := hx
  intro hd
  apply h1
  have := dvd_sub hd (dvd_mul_right (2 : A) m)
  simpa using this

/-- `ν₂(x) := max {n ∈ ℕ | x ∈ 2ⁿA}` (`syracuse.tex:52`), valued in `ℕ∞`; `ν₂ 0 = ⊤`. -/
noncomputable def nu2 (x : A) : ℕ∞ := emultiplicity (2 : A) x

/-- The `ℕ`-valued `ν₂` (Mathlib's `multiplicity`, junk value `1` at `x = 0`). -/
noncomputable def v2 (x : A) : ℕ := multiplicity (2 : A) x

/-- `x ∈ 2ⁿA` is `2ⁿ ∣ x`. -/
theorem mem_span_two_pow_iff {x : A} {n : ℕ} :
    x ∈ Ideal.span {(2 : A) ^ n} ↔ (2 : A) ^ n ∣ x := Ideal.mem_span_singleton

/-- The paper's `ν₂(x) = max {n | x ∈ 2ⁿA}`: `ν₂ x = n` iff `n` is that max. -/
theorem nu2_eq_coe_iff {x : A} {n : ℕ} :
    nu2 x = n ↔ IsGreatest {m : ℕ | x ∈ Ideal.span {(2 : A) ^ m}} n := by
  simp only [nu2, emultiplicity_eq_coe, IsGreatest, upperBounds, Set.mem_setOf_eq,
    mem_span_two_pow_iff]
  constructor
  · rintro ⟨hn, hn1⟩
    refine ⟨hn, fun m hm => ?_⟩
    by_contra hlt
    exact hn1 (dvd_trans (pow_dvd_pow 2 (by omega)) hm)
  · rintro ⟨hn, hmax⟩
    exact ⟨hn, fun h => by have := hmax h; omega⟩

theorem nu2_zero : nu2 (0 : A) = ⊤ := by
  exact emultiplicity_zero _

theorem pow_v2_dvd (x : A) : (2 : A) ^ v2 x ∣ x := pow_multiplicity_dvd _ _

/-- The quotient `x / 2ⁿ`: a `y` with `2ⁿ y = x` when one exists (junk `0` otherwise). -/
noncomputable def divPow2 (x : A) (n : ℕ) : A :=
  open scoped Classical in if h : (2 : A) ^ n ∣ x then h.choose else 0

theorem pow_mul_divPow2 {x : A} {n : ℕ} (h : (2 : A) ^ n ∣ x) : (2 : A) ^ n * divPow2 x n = x := by
  rw [divPow2, dif_pos h]
  exact h.choose_spec.symm

/-- "two such `y` are equal since the ring is integral" (l.50) — given `2 ≠ 0`. -/
theorem divPow2_unique [IsDomain A] (h2 : (2 : A) ≠ 0) {x y : A} {n : ℕ}
    (h : (2 : A) ^ n * y = x) : divPow2 x n = y := by
  have hd : (2 : A) ^ n ∣ x := ⟨y, h.symm⟩
  exact mul_left_cancel₀ (pow_ne_zero n h2) ((pow_mul_divPow2 hd).trans h.symm)

/-- In a domain with `2 ≠ 0` and `1 ∉ 2A`: `2ᵃ u = 2ᵇ v` with `u, v ∈ 2A + 1` forces `a = b`
and `u = v`. -/
theorem pow_two_mul_odd_inj [IsDomain A] (h2 : (2 : A) ≠ 0) (h1 : ¬ (2 : A) ∣ 1) {a b : ℕ}
    {u v : A} (hu : Odd u) (hv : Odd v) (h : (2 : A) ^ a * u = (2 : A) ^ b * v) : a = b ∧ u = v := by
  wlog hab : a ≤ b generalizing a b u v
  · obtain ⟨e1, e2⟩ := this hv hu h.symm (le_of_not_ge hab)
    exact ⟨e1.symm, e2.symm⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_assoc] at h
  have h' := mul_left_cancel₀ (pow_ne_zero a h2) h
  rcases c with _ | c
  · simp only [pow_zero, one_mul] at h'
    exact ⟨by simp, h'⟩
  · exfalso
    apply not_two_dvd_of_odd h1 hu
    rw [h']
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.succ_ne_zero c)) v

end General

namespace IsZ2Ring

variable {A : Type*} [CommRing A] [IsZ2Ring A]

/-- `1 ∉ 2A`. -/
theorem not_two_dvd_one : ¬ (2 : A) ∣ 1 := by
  obtain ⟨e⟩ := IsZ2Ring.quotient_two (A := A)
  intro h
  have h0 : Ideal.Quotient.mk (Ideal.span {(2 : A)}) 1 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 h)
  rw [map_one] at h0
  have := congrArg e h0
  rw [map_one, map_zero] at this
  exact one_ne_zero this

theorem not_isUnit_two : ¬ IsUnit (2 : A) := by
  exact fun hu => not_two_dvd_one (isUnit_iff_dvd_one.1 hu)

theorem span_two_ne_top : Ideal.span {(2 : A)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  exact not_isUnit_two

/-- Every `x` is in `2A` or `2A + 1`. -/
theorem two_dvd_or_two_dvd_sub_one (x : A) : (2 : A) ∣ x ∨ (2 : A) ∣ x - 1 := by
  obtain ⟨e⟩ := IsZ2Ring.quotient_two (A := A)
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key (e (Ideal.Quotient.mk _ x)) with h | h
  · left
    rw [← map_zero e, e.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at h
    exact h
  · right
    rw [← map_one e, e.injective.eq_iff, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at h
    exact h

/-- `2A + 1 = A ∖ 2A`. -/
theorem odd_iff_not_two_dvd {x : A} : Odd x ↔ ¬ (2 : A) ∣ x := by
  refine ⟨not_two_dvd_of_odd not_two_dvd_one, fun hx => ?_⟩
  rcases two_dvd_or_two_dvd_sub_one x with h | ⟨m, hm⟩
  · exact absurd h hx
  · exact ⟨m, by linear_combination hm⟩

theorem two_dvd_or_odd (x : A) : (2 : A) ∣ x ∨ Odd x := by
  by_cases h : (2 : A) ∣ x
  · exact Or.inl h
  · exact Or.inr (odd_iff_not_two_dvd.2 h)

/-- "if `x ∉ 2A` then `3x+1 ∈ 2A`" (l.50). -/
theorem two_dvd_three_mul_add_one {x : A} (hx : ¬ (2 : A) ∣ x) : (2 : A) ∣ 3 * x + 1 := by
  obtain ⟨m, rfl⟩ := odd_iff_not_two_dvd.2 hx
  exact ⟨3 * m + 2, by ring⟩

/-- **Krull** (l.51): `⋂ₙ (2A)ⁿ = 0`. -/
theorem iInf_span_two_pow_eq_bot : ⨅ n : ℕ, (Ideal.span {(2 : A)}) ^ n = ⊥ := by
  exact Ideal.iInf_pow_eq_bot_of_isDomain _ span_two_ne_top

/-- The 2-valuation of a nonzero element is finite. -/
theorem finiteMultiplicity_two {x : A} (hx : x ≠ 0) : FiniteMultiplicity (2 : A) x := by
  by_contra hfin
  apply hx
  have hall : ∀ n : ℕ, (2 : A) ^ n ∣ x := by
    intro n
    by_contra hn
    exact hfin ⟨n, fun h => hn (dvd_trans (pow_dvd_pow 2 (Nat.le_succ n)) h)⟩
  have hmem : x ∈ ⨅ n : ℕ, (Ideal.span {(2 : A)}) ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hall n
  rw [iInf_span_two_pow_eq_bot] at hmem
  exact (Ideal.mem_bot).1 hmem

/-- "the 2-valuation is well defined" (l.52): for `x ≠ 0` the max exists. -/
theorem exists_isGreatest {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, IsGreatest {m : ℕ | x ∈ Ideal.span {(2 : A) ^ m}} n := by
  refine ⟨v2 x, nu2_eq_coe_iff.1 ?_⟩
  exact (finiteMultiplicity_two hx).emultiplicity_eq_multiplicity

theorem nu2_eq_top_iff {x : A} : nu2 x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (emultiplicity_eq_top.1 h) (finiteMultiplicity_two hx)
  · rintro rfl
    exact nu2_zero

theorem v2_eq_nu2 {x : A} (hx : x ≠ 0) : (v2 x : ℕ∞) = nu2 x := by
  exact ((finiteMultiplicity_two hx).emultiplicity_eq_multiplicity).symm

theorem not_pow_succ_v2_dvd {x : A} (hx : x ≠ 0) : ¬ (2 : A) ^ (v2 x + 1) ∣ x := by
  exact (finiteMultiplicity_two hx).not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)

theorem le_v2_of_pow_dvd {x : A} (hx : x ≠ 0) {m : ℕ} (h : (2 : A) ^ m ∣ x) : m ≤ v2 x := by
  by_contra hlt
  exact (finiteMultiplicity_two hx).not_pow_dvd_of_multiplicity_lt (not_le.1 hlt) h

/-- In a ℤ/2ℤ-ring, `2 = 0` exactly when `A` is `ℤ/2ℤ`. -/
theorem two_eq_zero_iff : (2 : A) = 0 ↔ Nonempty (A ≃+* ZMod 2) := by
  constructor
  · intro h2
    obtain ⟨e⟩ := IsZ2Ring.quotient_two (A := A)
    have hI : Ideal.span {(2 : A)} = ⊥ := Ideal.span_singleton_eq_bot.2 h2
    exact ⟨((RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq hI.symm)).trans e⟩
  · rintro ⟨e⟩
    apply e.injective
    rw [map_ofNat, map_zero]
    decide

/-- A ℤ/2ℤ-ring with `2 ≠ 0` has characteristic zero. -/
theorem charZero_of_two_ne_zero (h2 : (2 : A) ≠ 0) : CharZero A := by
  rcases CharP.exists' A with h | ⟨q, hq, hc⟩
  · exact h
  · exfalso
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact h2 (by exact_mod_cast CharP.cast_eq_zero A 2)
    obtain ⟨m, hm⟩ := hq.out.odd_of_ne_two hq2
    have hq0 : (q : A) = 0 := CharP.cast_eq_zero A q
    rw [hm] at hq0
    push_cast at hq0
    exact not_two_dvd_one ⟨-(m : A), by linear_combination hq0⟩

/-- The constructor from the parity dichotomy. -/
theorem of_parity {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (h1 : ¬ (2 : B) ∣ 1) (h : ∀ x : B, (2 : B) ∣ x ∨ (2 : B) ∣ x - 1) : IsZ2Ring B :=
  { quotient_two := quotient_two_of_parity h1 h }

end IsZ2Ring

/-! ### Instances and witnesses -/

instance instIsZ2RingInt : IsZ2Ring ℤ := by
  refine IsZ2Ring.of_parity (by decide) (fun x => ?_)
  omega

instance instIsZ2RingPadicInt : IsZ2Ring ℤ_[2] := by
  refine IsZ2Ring.of_parity ?_ ?_
  · intro h
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) 1).2 (by exact_mod_cast h)
    simp at this
  · intro x
    have hmem := PadicInt.sub_zmodRepr_mem x
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    have hlt := PadicInt.zmodRepr_lt_p x
    have h01 : x.zmodRepr = 0 ∨ x.zmodRepr = 1 := by omega
    rcases h01 with h0 | h0
    · left
      rw [h0] at hmem
      simpa using hmem
    · right
      rw [h0] at hmem
      simpa using hmem

/-- `3` is a unit of `ℤ₂`. -/
theorem isUnit_three_padicInt : IsUnit (3 : ℤ_[2]) := by
  by_contra h
  have hmem : (3 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  apply IsZ2Ring.not_two_dvd_one (A := ℤ_[2])
  have h3 : (1 : ℤ_[2]) = 3 - 2 := by norm_num
  rw [h3]
  exact dvd_sub (by exact_mod_cast hmem) dvd_rfl

/-- `ℤ/2ℤ` is a ℤ/2ℤ-ring (the degenerate one). -/
instance instIsZ2RingZMod2 : IsZ2Ring (ZMod 2) := by
  refine IsZ2Ring.of_parity ?_ ?_
  · rintro ⟨c, hc⟩
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at hc
    exact one_ne_zero hc
  · intro x
    fin_cases x
    · exact Or.inl (dvd_zero _)
    · exact Or.inr ⟨0, by decide⟩

/-- **Finding (l.50).** "in such a ring, `2 ≠ 0`" fails for the ℤ/2ℤ-ring `ℤ/2ℤ`. -/
theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := by decide

/-- **Integrality is needed (question).** `ZMod 6` is noetherian with `A/2A ≃ ℤ/2ℤ`, but halves are
not unique and the nonzero `2` has infinite 2-valuation. -/
theorem zmod6_witness :
    IsNoetherianRing (ZMod 6) ∧ Nonempty ((ZMod 6 ⧸ Ideal.span {(2 : ZMod 6)}) ≃+* ZMod 2) ∧
      (2 : ZMod 6) * 3 = 2 * 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ≠ 0 ∧ nu2 (2 : ZMod 6) = ⊤ := by
  have hall : ∀ n : ℕ, (2 : ZMod 6) ^ n ∣ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨2 * c, ?_⟩
      calc (2 : ZMod 6) = 2 * 4 := by decide
        _ = 2 ^ n * c * 4 := by rw [← hc]
        _ = 2 ^ (n + 1) * (2 * c) := by ring
  have hpar : ∀ x : ZMod 6, (∃ c, x = 2 * c) ∨ (∃ c, x - 1 = 2 * c) := by decide
  have h1 : ¬ ∃ c : ZMod 6, (1 : ZMod 6) = 2 * c := by decide
  refine ⟨inferInstance, quotient_two_of_parity h1 hpar, by decide, by decide, by decide, ?_⟩
  exact emultiplicity_eq_top.2 (fun ⟨n, hn⟩ => hn (hall (n + 1)))

end Syracuse
