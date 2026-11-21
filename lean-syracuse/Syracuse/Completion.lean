import Syracuse.Rep
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.UniformSpace.AbstractCompletion

/-!
# Syracuse § 1: the 2-completion of a ℤ/2ℤ-ring is `ℤ₂`, and `f_A`, `T_A` extend to it

`prop:ring_both_continuous_extends` — `syracuse.tex:58` (unmarked: its `T_A` half is false as
printed, Finding 1; its `f_A` half holds in the reading of OQ-42 (c)), and the unlabelled claim
`A₂ ≃ ℤ₂` of `syracuse.tex:52` (false for `ℤ/2ℤ`, Finding 3), on which the proposition rests.

> In the following, a noetherian ring $A$ such that $A/2A \simeq \ZZ/2\ZZ$ is called a
> $\ZZ/2\ZZ$-ring. In such a ring, the 2-valuation is well defined
> $\nu_2(x):= \max \{n\in \NN ~|~ x\in 2^n A\}$, as well as the associated absolute value and the
> 2-completion of $A$ we will denote by $A_2$. Actually, one can show that for any
> $\ZZ/2\ZZ$-ring $A$, $A_2$ is naturally isomorphic to the ring of 2-adic integers $\ZZ_2$.

> The proof of the following property is left to the reader.
> **prop:ring_both_continuous_extends.** Let $A$ be a $\ZZ/2\ZZ$-ring, both $f_A$ and $T_A$ are
> continuous and extends continuously to $A_2$. Furthermore, their extension is $f_{A_2}$ and
> $T_{A_2}$ respectively.

## What is here

* **`A₂ ≃ ℤ₂` (l.52), for `2 ≠ 0`.** Every `x ∈ A` is an integer modulo `2ⁿA`, so `ℤ/2ⁿℤ ≃ A/2ⁿA`
  (`zmodEquivQuotient`); the limit is a ring hom `ι = toZ2 : A → ℤ₂`, the only one
  (`toZ2_unique`, natural: `toZ2_comp`), injective by Krull (`toZ2_injective`), preserving `ν₂`
  and the absolute value `|x| = 2^{-ν₂(x)}` (`nu2_toZ2`, `norm_toZ2`), with dense image
  (`denseRange_toZ2`) and inducing the 2-adic topology (`isInducing_toZ2`). So `(ℤ₂, ι)` is a
  completion of `A` (`completionPkg`), and the completion `A₂ = UniformSpace.Completion A` of `A`
  for its 2-adic uniformity is isomorphic to `ℤ₂`, as a ring and as a uniform space, by an
  isomorphism extending `ι` (`completion_ringEquiv`, `completion_twoAdic`), the only ring
  isomorphism `A₂ ≃ ℤ₂` (`ringEquiv_padicInt_unique`).
* **`f_A`, `T_A` continuous.** For the 2-adic topology (`IsAdic (2A)`; its balls are `x + 2ⁿA`,
  `hasBasis_nhds_two`): `f_A` is continuous in every ℤ/2ℤ-ring (`continuous_f`), `T_A` at every
  point where it is defined, `3x + 1 ≠ 0` (`continuousAt_T`, `continuousOn_T`), everywhere when
  `3 ∉ Aˣ`, e.g. `ℤ` (`continuous_T_of_not_isUnit_three`).
* **The extensions.** `f_{A₂}` is continuous and extends `f_A`, and is its only continuous
  extension (`continuous_f_completion`, `f_coe_completion`, `eq_f_completion_of_continuous`; in
  `ℤ₂`: `continuous_f_padicInt`, `f_toZ2`, `eq_f_of_continuous`). Off `−1/3`, the same for `T`:
  `T_{A₂}` is continuous on `A₂ ∖ {−1/3}`, extends `T_A`, and is its only continuous extension from
  `2A + 1` to `(2A₂ + 1) ∖ {−1/3}` (`continuousOn_T_completion`, `T_coe_completion`,
  `eqOn_T_completion_of_continuousOn_odd`; in `ℤ₂`: `continuousOn_T_padicInt`, `T_toZ2`,
  `eqOn_T_of_continuousOn_odd`). Assembled: `ring_both_continuous_extends` (`A₂` the completion)
  and `ring_both_continuous_extends_padicInt` (`A₂` modelled by `ℤ₂` through `ι`).
* **The refutations.** `not_continuousWithinAt_extension_T`, `T_int_not_extends`,
  `printed_T_extends_false`, `not_exists_continuousWithinAt_extension_T_completion` (Finding 1);
  `completion_zmod2_not_padicInt` (Finding 3); `zmod4_witness` (integrality, OQ-42 (a)).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `A` a ℤ/2ℤ-ring | ✓ carried (`IsZ2Ring`), including integrality: ⚠ a reading (OQ-42 (a)), load-bearing (SCOPE) |
| `2 ≠ 0` (claimed at l.50, false for `ℤ/2ℤ`) | ⚠ strengthened in every statement about `A₂` or `ι` (OQ-42 (b)); not needed for the continuity of `f_A`, `T_A` |
| the topology of "the associated absolute value" (l.52) | ✓ carried: any topology with `IsAdic (Ideal.span {2})`, whose balls are `x + 2ⁿA` |
| `A₂`, "the 2-completion of `A`" (l.52) | ✓ carried: `UniformSpace.Completion A` for a 2-adic uniform ring structure; also `ℤ₂` via `ι` |
| `f_A` (l.55, cases printed swapped) | ⚠ a reading: `Syracuse.f`, halve the even (OQ-42 (c)) |
| `T_A : 2A+1 → 2A+1` (l.55) | ⚠ strengthened: `3x + 1 ≠ 0` (OQ-42 (d)); `T` total with junk `0` at `−1/3` |
| "extends continuously to `A₂`" (`T_A`) | ✗ false (Finding 1); proved on `A₂ ∖ {−1/3}` |

## SCOPE (disclosed)

* **Finding 1 (`prop:ring_both_continuous_extends`, l.58): `T_A` does not extend continuously to
  `A₂`.** For `A = ℤ`, where `T_ℤ` is the paper's map on all of `2ℤ + 1`, no `g : ℤ₂ → ℤ₂` is
  continuous on `2ℤ₂ + 1` and agrees with `T_ℤ` on the odd integers (`T_int_not_extends`); the
  printed statement, for every ℤ/2ℤ-ring, is refuted (`printed_T_extends_false`). In every
  ℤ/2ℤ-ring `A` with `2 ≠ 0`, no extension is continuous at `−1/3 ∈ 2A₂ + 1` within `2A₂ + 1`
  (`not_continuousWithinAt_extension_T`, `not_exists_continuousWithinAt_extension_T_completion`):
  the odd part of `3x + 1` has no limit at `−1/3`, being `1` along `cⱼ = (4^{j+1} − 1)/3` and `5`
  along `dⱼ = (10·4^{j+1} − 1)/3`. So `T_{A₂}`, undefined at `−1/3` (OQ-42 (d)), is not
  continuous on `2A₂ + 1` whatever its value there (`not_continuousWithinAt_T_padicInt` for the
  junk value). True form: off `−1/3`, `T_{A₂}` is continuous and is the unique continuous
  extension of `T_A` (`ring_both_continuous_extends`).
* **Finding 2 (l.58, "`T_A` is continuous").** True wherever `T_A` is defined (`continuousOn_T`),
  hence on all of `2A + 1` when `3 ∉ Aˣ`, e.g. `ℤ` (`continuous_T_of_not_isUnit_three`); when
  `3 ∈ Aˣ` (`ℤ₂`) the printed `T_A` is undefined at `−1/3` (OQ-42 (d)).
* **Finding 3 (l.52): `A₂ ≃ ℤ₂` fails for `A = ℤ/2ℤ`**: its completion has `2 = 0`, for every
  uniform ring structure (`completion_zmod2_not_padicInt`). It holds for every other ℤ/2ℤ-ring
  (`completion_ringEquiv`), and "naturally" is proved: `ι` is the only ring hom `A → ℤ₂`, and the
  isomorphism is the only ring isomorphism `A₂ ≃ ℤ₂` (`ringEquiv_padicInt_unique`). The paper
  gives no proof ("one can show").
* **Integrality (OQ-42 (a)) is load-bearing for l.52.** `ZMod 4` is noetherian with
  `A/2A ≃ ℤ/2ℤ` and `2 ≠ 0`, but not a domain, and its completion has `4 = 0`, so it is not `ℤ₂`
  (`zmod4_witness`). Here integrality is used to cancel powers of `2`: in `ℤ/2ⁿℤ ≃ A/2ⁿA`
  (`two_pow_dvd_natCast_iff`), in Krull (`toZ2_injective`), in the uniqueness of halves and of the
  odd part (`f_map`, `T_map`, `continuous_f`, `continuousAt_T`).
* The `f_A` half is proved in the reading `f` of OQ-42 (c) (the printed `f_A` does not exist,
  `printed_f_not_definable`), for `2 ≠ 0` where `A₂` enters (OQ-42 (b)); for `A = ℤ/2ℤ`, `A₂` is
  not `ℤ₂` (Finding 3) and halves are not unique, and nothing is claimed.
* Reading of `A₂`: the uniform completion for the 2-adic uniformity (entourages
  `{(x, y) | x − y ∈ 2ⁿA}`, the uniformity of `|·|`), with any uniform ring structure whose topology
  is 2-adic (`completion_twoAdic` for the canonical one; the instance arguments
  `IsUniformAddGroup`, `IsTopologicalRing` hold for it). The algebraic `lim A/2ⁿA`
  (`AdicCompletion`) is not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Filter Topology

/-! ### Algebra: `A/2ⁿA ≃ ℤ/2ⁿℤ` and the natural map `ι : A → ℤ₂` -/

section Algebra

variable {A : Type*} [CommRing A] [IsZ2Ring A]

/-- Every `x ∈ A` is congruent to an integer modulo `2ⁿA` (its first `n` binary digits). -/
theorem exists_int_two_pow_dvd_sub (x : A) (n : ℕ) : ∃ m : ℤ, (2 : A) ^ n ∣ x - m := by
  induction n generalizing x with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    rcases IsZ2Ring.two_dvd_or_two_dvd_sub_one x with ⟨y, hy⟩ | ⟨y, hy⟩
    · obtain ⟨m, c, hc⟩ := ih y
      refine ⟨2 * m, c, ?_⟩
      rw [hy, pow_succ]
      push_cast
      linear_combination 2 * hc
    · obtain ⟨m, c, hc⟩ := ih y
      refine ⟨2 * m + 1, c, ?_⟩
      rw [pow_succ]
      push_cast
      linear_combination hy + 2 * hc

/-- `2ⁿ ∣ k` in `A` iff in `ℕ`, when `2 ≠ 0` (integrality cancels the `2`-part of `k`). -/
theorem two_pow_dvd_natCast_iff (h2 : (2 : A) ≠ 0) (n k : ℕ) :
    (2 : A) ^ n ∣ (k : A) ↔ 2 ^ n ∣ k := by
  constructor
  · intro h
    rcases eq_or_ne k 0 with rfl | hk
    · exact dvd_zero _
    obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
    by_cases hvn : n ≤ v
    · exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hvn) m
    · exfalso
      push Not at hvn
      obtain ⟨c, hc⟩ := h
      have hsplit : (2 : A) ^ n = 2 ^ v * 2 ^ (n - v) := by
        rw [← pow_add, Nat.add_sub_cancel' hvn.le]
      push_cast at hc
      rw [hsplit, mul_assoc] at hc
      have hc' := mul_left_cancel₀ (pow_ne_zero v h2) hc
      have hodd : Odd (m : A) := hm.natCast
      apply not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one hodd
      rw [hc']
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) c
  · intro h
    exact_mod_cast (Nat.cast_dvd_cast h : ((2 ^ n : ℕ) : A) ∣ (k : A))

/-- `A/2ⁿA` has characteristic `2ⁿ` when `2 ≠ 0`. -/
theorem charP_quotient_two_pow (h2 : (2 : A) ≠ 0) (n : ℕ) :
    CharP (A ⧸ Ideal.span {(2 : A) ^ n}) (2 ^ n) := by
  refine ⟨fun k => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, two_pow_dvd_natCast_iff h2]

/-- `ℤ/2ⁿℤ → A/2ⁿA` is onto. -/
theorem zmodEquivQuotient_surj (h2 : (2 : A) ≠ 0) (n : ℕ) :
    haveI := charP_quotient_two_pow h2 n
    Function.Surjective (ZMod.castHom (dvd_refl (2 ^ n)) (A ⧸ Ideal.span {(2 : A) ^ n})) := by
  haveI := charP_quotient_two_pow h2 n
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := exists_int_two_pow_dvd_sub x n
  refine ⟨(m : ZMod (2 ^ n)), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(2 : A) ^ n})) m, eq_comm,
    Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact hm

/-- `ℤ/2ⁿℤ ≃ A/2ⁿA` (when `2 ≠ 0`). -/
noncomputable def zmodEquivQuotient (h2 : (2 : A) ≠ 0) (n : ℕ) :
    ZMod (2 ^ n) ≃+* A ⧸ Ideal.span {(2 : A) ^ n} :=
  haveI := charP_quotient_two_pow h2 n
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl _) _)
    ⟨ZMod.castHom_injective _, zmodEquivQuotient_surj h2 n⟩

/-- The reduction `A → A/2ⁿA ≃ ℤ/2ⁿℤ`. -/
noncomputable def zmodPow (h2 : (2 : A) ≠ 0) (n : ℕ) : A →+* ZMod (2 ^ n) :=
  (zmodEquivQuotient h2 n).symm.toRingHom.comp (Ideal.Quotient.mk _)

/-- There is at most one ring hom `A → ℤ/2ⁿℤ` (every ℤ/2ℤ-ring, `ℤ/2ℤ` included). -/
theorem ringHom_zmodPow_ext {n : ℕ} (g g' : A →+* ZMod (2 ^ n)) : g = g' := by
  ext x
  obtain ⟨m, c, hc⟩ := exists_int_two_pow_dvd_sub x n
  have hx : x = (m : A) + 2 ^ n * c := by linear_combination hc
  have h0 : ((2 : ZMod (2 ^ n))) ^ n = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ n)
  rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat, h0,
    zero_mul, zero_mul, map_intCast, map_intCast]

/-- The reductions are compatible. -/
theorem zmodPow_compat (h2 : (2 : A) ≠ 0) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k₁))).comp (zmodPow h2 k₂) = zmodPow h2 k₁ :=
  ringHom_zmodPow_ext _ _

theorem zmodPow_eq_zero_iff (h2 : (2 : A) ≠ 0) {n : ℕ} {x : A} :
    zmodPow h2 n x = 0 ↔ (2 : A) ^ n ∣ x := by
  rw [zmodPow, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_eq_zero_iff _ (zmodEquivQuotient h2 n).symm.injective, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/-- **The natural map `ι : A → ℤ₂`** (`syracuse.tex:52`): the limit of `A → A/2ⁿA ≃ ℤ/2ⁿℤ`. -/
noncomputable def toZ2 (h2 : (2 : A) ≠ 0) : A →+* ℤ_[2] :=
  PadicInt.lift (zmodPow_compat h2)

theorem toZModPow_toZ2 (h2 : (2 : A) ≠ 0) (n : ℕ) (x : A) :
    PadicInt.toZModPow n (toZ2 h2 x) = zmodPow h2 n x := by
  rw [toZ2, ← RingHom.comp_apply, PadicInt.lift_spec]

omit [IsZ2Ring A] in
theorem toZModPow_eq_zero_iff {n : ℕ} {z : ℤ_[2]} :
    PadicInt.toZModPow n z = 0 ↔ (2 : ℤ_[2]) ^ n ∣ z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, Nat.cast_ofNat]

/-- `ι` preserves and reflects divisibility by `2ⁿ`. -/
theorem two_pow_dvd_toZ2_iff (h2 : (2 : A) ≠ 0) {n : ℕ} {x : A} :
    (2 : ℤ_[2]) ^ n ∣ toZ2 h2 x ↔ (2 : A) ^ n ∣ x := by
  rw [← toZModPow_eq_zero_iff, toZModPow_toZ2, zmodPow_eq_zero_iff]

/-- `ι` preserves and reflects parity. -/
theorem odd_toZ2_iff (h2 : (2 : A) ≠ 0) {x : A} : Odd (toZ2 h2 x) ↔ Odd x := by
  rw [IsZ2Ring.odd_iff_not_two_dvd, IsZ2Ring.odd_iff_not_two_dvd, not_iff_not]
  have := two_pow_dvd_toZ2_iff h2 (n := 1) (x := x)
  rwa [pow_one, pow_one] at this

/-- **"Naturally"** (l.52): `ι` is the only ring hom `A → ℤ₂`. -/
theorem toZ2_unique (h2 : (2 : A) ≠ 0) (g : A →+* ℤ_[2]) : g = toZ2 h2 :=
  (PadicInt.lift_unique (zmodPow_compat h2) g (fun _ => ringHom_zmodPow_ext _ _)).symm

/-- Naturality: `ι_B ∘ φ = ι_A` for every ring hom `φ : A → B` of ℤ/2ℤ-rings. -/
theorem toZ2_comp {B : Type*} [CommRing B] [IsZ2Ring B] (h2 : (2 : A) ≠ 0) (h2' : (2 : B) ≠ 0)
    (φ : A →+* B) : (toZ2 h2').comp φ = toZ2 h2 :=
  toZ2_unique h2 _

/-- `ι` is injective (Krull, l.51). -/
theorem toZ2_injective (h2 : (2 : A) ≠ 0) : Function.Injective (toZ2 h2) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  apply IsZ2Ring.not_pow_succ_v2_dvd hne
  rw [← two_pow_dvd_toZ2_iff h2, hx]
  exact dvd_zero _

/-- `ι` has dense image (it contains `ℤ`). -/
theorem denseRange_toZ2 (h2 : (2 : A) ≠ 0) : DenseRange (toZ2 h2) := by
  refine PadicInt.denseRange_intCast.mono ?_
  rintro _ ⟨m, rfl⟩
  exact ⟨m, map_intCast _ _⟩

/-- `ι` preserves the 2-valuation `ν₂` (l.52). -/
theorem nu2_toZ2 (h2 : (2 : A) ≠ 0) (x : A) : nu2 (toZ2 h2 x) = nu2 x := by
  rw [nu2, nu2, emultiplicity_eq_emultiplicity_iff]
  exact fun n => two_pow_dvd_toZ2_iff h2

/-- `ι` is an isometry for the paper's absolute value `|x| = 2^{-ν₂(x)}` (l.52). -/
theorem norm_toZ2 (h2 : (2 : A) ≠ 0) {x : A} (hx : x ≠ 0) :
    ‖toZ2 h2 x‖ = (2 : ℝ) ^ (-(v2 x : ℤ)) := by
  have hx' : toZ2 h2 x ≠ 0 := (map_ne_zero_iff _ (toZ2_injective h2)).2 hx
  have hval : (toZ2 h2 x).valuation = v2 x := by
    have key : ∀ n : ℕ, n ≤ (toZ2 h2 x).valuation ↔ n ≤ v2 x := by
      intro n
      rw [← PadicInt.mem_span_pow_iff_le_valuation _ hx', Ideal.mem_span_singleton,
        Nat.cast_ofNat, two_pow_dvd_toZ2_iff h2]
      exact ⟨IsZ2Ring.le_v2_of_pow_dvd hx, fun h => (pow_dvd_pow 2 h).trans (pow_v2_dvd x)⟩
    exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)
  rw [PadicInt.norm_eq_zpow_neg_valuation hx', hval]
  norm_num

end Algebra

/-! ### The 2-adic topology -/

section Topology

variable {A B : Type*} [CommRing A] [CommRing B]

/-- In the `2A`-adic topology the neighbourhoods of `x` have basis the balls `x + 2ⁿA`, i.e.
`{y | |y − x| ≤ 2⁻ⁿ}` for the paper's absolute value. -/
theorem hasBasis_nhds_two [TopologicalSpace A] (hA : IsAdic (Ideal.span {(2 : A)})) (x : A) :
    (𝓝 x).HasBasis (fun _ => True) (fun n : ℕ => {y | (2 : A) ^ n ∣ y - x}) := by
  refine (hA.hasBasis_nhds x).congr (fun _ => Iff.rfl) (fun n _ => ?_)
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨y - x, h, by ring⟩

/-- The canonical 2-adic topology (`WithIdeal`) satisfies `IsAdic`: the hypothesis is not void. -/
theorem isAdic_withIdeal :
    letI : WithIdeal A := ⟨Ideal.span {(2 : A)}⟩
    IsAdic (Ideal.span {(2 : A)}) := by
  unfold IsAdic
  rfl

theorem two_pow_dvd_iff_norm_le (z : ℤ_[2]) (n : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ z ↔ ‖z‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  have := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) z n
  rw [Ideal.mem_span_singleton] at this
  simpa using this.symm

/-- The topology of `ℤ₂` is its `2ℤ₂`-adic topology. -/
theorem isAdic_padicInt : IsAdic (Ideal.span {(2 : ℤ_[2])}) := by
  rw [isAdic_iff]
  have hset : ∀ n : ℕ, ((Ideal.span {(2 : ℤ_[2])} ^ n : Ideal ℤ_[2]) : Set ℤ_[2]) =
      Metric.ball 0 ((2 : ℝ) ^ (-(n : ℤ) + 1)) := by
    intro n
    ext z
    rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton, mem_ball_zero_iff,
      two_pow_dvd_iff_norm_le]
    have := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (p := 2) z (-(n : ℤ))
    simpa using this
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · rw [hset]
    exact Metric.isOpen_ball
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt 2 hε
    refine ⟨k, fun z hz => hball ?_⟩
    rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      two_pow_dvd_iff_norm_le] at hz
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt hz ?_
    simpa using hk

/-- Continuity at a point for 2-adic topologies, in `ε`–`δ` form. -/
theorem continuousAt_iff_two [TopologicalSpace A] [TopologicalSpace B]
    (hA : IsAdic (Ideal.span {(2 : A)})) (hB : IsAdic (Ideal.span {(2 : B)})) {g : A → B} {x : A} :
    ContinuousAt g x ↔ ∀ n : ℕ, ∃ m : ℕ, ∀ y, (2 : A) ^ m ∣ y - x → (2 : B) ^ n ∣ g y - g x := by
  rw [ContinuousAt, (hasBasis_nhds_two hA x).tendsto_iff (hasBasis_nhds_two hB (g x))]
  simp only [true_and, Set.mem_setOf_eq, forall_const]

theorem eq_of_two_pow_succ_dvd_sub_of_two_eq_zero (h2 : (2 : A) = 0) {x y : A} {m : ℕ}
    (h : (2 : A) ^ (m + 1) ∣ y - x) : y = x := by
  rw [h2, zero_pow (Nat.succ_ne_zero m), zero_dvd_iff, sub_eq_zero] at h
  exact h

theorem three_mul_add_one_map {F : Type*} [FunLike F A B] [RingHomClass F A B] (φ : F) (x : A) :
    3 * φ x + 1 = φ (3 * x + 1) := by
  rw [map_add, map_mul, map_ofNat, map_one]

/-- `2A + 1` is open in a 2-adic topology. -/
theorem isOpen_odd [TopologicalSpace A] (hA : IsAdic (Ideal.span {(2 : A)})) :
    IsOpen {w : A | Odd w} := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  refine Filter.mem_of_superset ((hasBasis_nhds_two hA w).mem_of_mem (i := 1) trivial) ?_
  rintro z ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hw
  rw [pow_one] at hc
  exact ⟨m + c, by linear_combination hc + hm⟩

end Topology

/-! ### `f_A` and `T_A` are continuous -/

section Continuity

variable {A : Type*} [CommRing A] [IsZ2Ring A] [TopologicalSpace A]

/-- **`f_A` is continuous** for the 2-adic topology, in every ℤ/2ℤ-ring (`ℤ/2ℤ` included). -/
theorem continuous_f (hA : IsAdic (Ideal.span {(2 : A)})) : Continuous (f : A → A) := by
  refine continuous_iff_continuousAt.2 fun x =>
    (continuousAt_iff_two hA hA).2 fun n => ⟨n + 1, fun y hy => ?_⟩
  by_cases h2 : (2 : A) = 0
  · rw [eq_of_two_pow_succ_dvd_sub_of_two_eq_zero h2 hy, sub_self]
    exact dvd_zero _
  obtain ⟨c, hc⟩ := hy
  rcases IsZ2Ring.two_dvd_or_odd x with hx | hx
  · have hy2 : (2 : A) ∣ y := by
      have hyx : y = x + 2 * (2 ^ n * c) := by linear_combination hc
      rw [hyx]
      exact dvd_add hx (dvd_mul_right _ _)
    have e1 := two_mul_f_of_two_dvd hx
    have e2 := two_mul_f_of_two_dvd hy2
    refine ⟨c, mul_left_cancel₀ h2 ?_⟩
    linear_combination e2 - e1 + hc
  · have hxn : ¬ (2 : A) ∣ x := IsZ2Ring.odd_iff_not_two_dvd.1 hx
    have hyn : ¬ (2 : A) ∣ y := by
      intro hy2
      apply hxn
      have hxy : x = y - 2 * (2 ^ n * c) := by linear_combination -hc
      rw [hxy]
      exact dvd_sub hy2 (dvd_mul_right _ _)
    rw [f_of_not_two_dvd hxn, f_of_not_two_dvd hyn]
    exact ⟨3 * 2 * c, by linear_combination 3 * hc⟩

/-- **`T_A` is continuous wherever it is defined** (`3x + 1 ≠ 0`), in every ℤ/2ℤ-ring: for
`y − x ∈ 2^{n+k+1}A`, `k = ν₂(3x+1)`, one has `T y − T x = 3(y − x)/2ᵏ ∈ 2^{n+1}A`. -/
theorem continuousAt_T (hA : IsAdic (Ideal.span {(2 : A)})) {x : A} (hx : 3 * x + 1 ≠ 0) :
    ContinuousAt (T : A → A) x := by
  refine (continuousAt_iff_two hA hA).2 fun n => ⟨n + v2 (3 * x + 1) + 1, fun y hy => ?_⟩
  by_cases h2 : (2 : A) = 0
  · rw [eq_of_two_pow_succ_dvd_sub_of_two_eq_zero h2 hy, sub_self]
    exact dvd_zero _
  obtain ⟨c, hc⟩ := hy
  have hTx := pow_v2_mul_T x
  have hodd : Odd (T x + 3 * 2 ^ (n + 1) * c) :=
    (T_odd hx).add_even (even_iff_two_dvd.2 ⟨3 * 2 ^ n * c, by ring⟩)
  have heq : (2 : A) ^ v2 (3 * x + 1) * (T x + 3 * 2 ^ (n + 1) * c) = 3 * y + 1 := by
    linear_combination hTx - 3 * hc
  rw [(T_unique h2 hodd heq).2]
  exact ⟨3 * 2 * c, by ring⟩

/-- `T_A` is continuous on `A ∖ {−1/3}`. -/
theorem continuousOn_T (hA : IsAdic (Ideal.span {(2 : A)})) :
    ContinuousOn (T : A → A) {x | 3 * x + 1 ≠ 0} :=
  fun _ hx => (continuousAt_T hA hx).continuousWithinAt

/-- When `3 ∉ Aˣ` (e.g. `A = ℤ`), `T_A` is continuous on all of `A`, hence on `2A + 1`. -/
theorem continuous_T_of_not_isUnit_three (hA : IsAdic (Ideal.span {(2 : A)}))
    (h3 : ¬ IsUnit (3 : A)) : Continuous (T : A → A) :=
  continuous_iff_continuousAt.2 fun x => continuousAt_T hA (three_mul_add_one_ne_zero h3 x)

end Continuity

/-! ### `f` and `T` commute with ring homs; the extensions to `ℤ₂` -/

section Extension

variable {A : Type*} [CommRing A] [IsZ2Ring A]

/-- `T x = 0` at `3x + 1 = 0` (the junk value, when `2 ≠ 0`). -/
theorem T_of_three_mul_add_one_eq_zero (h2 : (2 : A) ≠ 0) {x : A} (hx : 3 * x + 1 = 0) :
    T x = 0 := by
  rw [T, hx]
  exact divPow2_unique h2 (mul_zero _)

/-- `f` commutes with every ring hom between ℤ/2ℤ-rings with `2 ≠ 0`. -/
theorem f_map {B : Type*} [CommRing B] [IsZ2Ring B] (h2 : (2 : A) ≠ 0) (h2' : (2 : B) ≠ 0)
    (φ : A →+* B) (x : A) : f (φ x) = φ (f x) := by
  rcases IsZ2Ring.two_dvd_or_odd x with ⟨y, rfl⟩ | hx
  · have e1 : f (2 * y) = y := f_eq_of_two_mul h2 rfl
    have e2 : f (2 * φ y) = φ y := f_eq_of_two_mul h2' rfl
    rw [e1, map_mul, map_ofNat, e2]
  · have hx' : ¬ (2 : A) ∣ x := IsZ2Ring.odd_iff_not_two_dvd.1 hx
    have hφ : ¬ (2 : B) ∣ φ x := IsZ2Ring.odd_iff_not_two_dvd.1 (hx.map φ)
    rw [f_of_not_two_dvd hx', f_of_not_two_dvd hφ, map_add, map_mul, map_ofNat, map_one]

/-- `T` commutes with every ring hom between ℤ/2ℤ-rings with `2 ≠ 0` (junk values included). -/
theorem T_map {B : Type*} [CommRing B] [IsZ2Ring B] (h2 : (2 : A) ≠ 0) (h2' : (2 : B) ≠ 0)
    (φ : A →+* B) (x : A) : T (φ x) = φ (T x) := by
  by_cases hx : 3 * x + 1 = 0
  · have hφ : 3 * φ x + 1 = 0 := by
      have := congrArg φ hx
      rwa [map_add, map_mul, map_ofNat, map_one, map_zero] at this
    rw [T_of_three_mul_add_one_eq_zero h2' hφ, T_of_three_mul_add_one_eq_zero h2 hx, map_zero]
  · have h := congrArg φ (pow_v2_mul_T x)
    rw [map_mul, map_pow, map_ofNat, map_add, map_mul, map_ofNat, map_one] at h
    exact (T_unique h2' ((T_odd hx).map φ) h).2

/-- **`f_{ℤ₂}` extends `f_A`**: `f_{ℤ₂} ∘ ι = ι ∘ f_A`. -/
theorem f_toZ2 (h2 : (2 : A) ≠ 0) (x : A) : f (toZ2 h2 x) = toZ2 h2 (f x) :=
  f_map h2 two_ne_zero _ x

/-- **`T_{ℤ₂}` extends `T_A`**: `T_{ℤ₂} ∘ ι = ι ∘ T_A`. -/
theorem T_toZ2 (h2 : (2 : A) ≠ 0) (x : A) : T (toZ2 h2 x) = toZ2 h2 (T x) :=
  T_map h2 two_ne_zero _ x

/-- `f_{ℤ₂}` is continuous. -/
theorem continuous_f_padicInt : Continuous (f : ℤ_[2] → ℤ_[2]) := continuous_f isAdic_padicInt

/-- `T_{ℤ₂}` is continuous off `−1/3`. -/
theorem continuousOn_T_padicInt : ContinuousOn (T : ℤ_[2] → ℤ_[2]) {z | 3 * z + 1 ≠ 0} :=
  continuousOn_T isAdic_padicInt

/-- The continuous extension of `f_A` to `ℤ₂` is unique: it is `f_{ℤ₂}`. -/
theorem eq_f_of_continuous (h2 : (2 : A) ≠ 0) {g : ℤ_[2] → ℤ_[2]} (hg : Continuous g)
    (h : ∀ x : A, g (toZ2 h2 x) = toZ2 h2 (f x)) : g = f :=
  (denseRange_toZ2 h2).equalizer hg continuous_f_padicInt
    (funext fun x => by simp only [Function.comp_apply, h, f_toZ2])

/-- The continuous extension of `T_A` to `ℤ₂ ∖ {−1/3}` is unique: it is `T_{ℤ₂}`. -/
theorem eqOn_T_of_continuousOn (h2 : (2 : A) ≠ 0) {g : ℤ_[2] → ℤ_[2]}
    (hg : ContinuousOn g {z | 3 * z + 1 ≠ 0})
    (h : ∀ x : A, 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x)) :
    Set.EqOn g T {z | 3 * z + 1 ≠ 0} := by
  have hV : IsOpen {z : ℤ_[2] | 3 * z + 1 ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hsub : {z : ℤ_[2] | 3 * z + 1 ≠ 0} ∩ Set.range (toZ2 h2) ⊆
      toZ2 h2 '' {x | 3 * x + 1 ≠ 0} := by
    rintro _ ⟨hz, x, rfl⟩
    refine ⟨x, fun hx => hz ?_, rfl⟩
    rw [three_mul_add_one_map, hx, map_zero]
  refine Set.EqOn.of_subset_closure (s := toZ2 h2 '' {x | 3 * x + 1 ≠ 0}) ?_ hg
    continuousOn_T_padicInt ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [h x hx, T_toZ2]
  · rintro _ ⟨x, hx, rfl⟩
    show 3 * toZ2 h2 x + 1 ≠ 0
    rw [three_mul_add_one_map]
    exact (map_ne_zero_iff _ (toZ2_injective h2)).2 hx
  · exact (Dense.open_subset_closure_inter (denseRange_toZ2 h2) hV).trans (closure_mono hsub)

/-- On the paper's domain: the continuous extension of `T_A : 2A + 1 → 2A + 1` to
`(2ℤ₂ + 1) ∖ {−1/3}` is unique, and it is `T_{ℤ₂}`. -/
theorem eqOn_T_of_continuousOn_odd (h2 : (2 : A) ≠ 0) {g : ℤ_[2] → ℤ_[2]}
    (hg : ContinuousOn g {z | Odd z ∧ 3 * z + 1 ≠ 0})
    (h : ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x)) :
    Set.EqOn g T {z | Odd z ∧ 3 * z + 1 ≠ 0} := by
  have hV : IsOpen {z : ℤ_[2] | Odd z ∧ 3 * z + 1 ≠ 0} :=
    (isOpen_odd isAdic_padicInt).inter (isOpen_ne_fun (by fun_prop) continuous_const)
  have hsub : {z : ℤ_[2] | Odd z ∧ 3 * z + 1 ≠ 0} ∩ Set.range (toZ2 h2) ⊆
      toZ2 h2 '' {x | Odd x ∧ 3 * x + 1 ≠ 0} := by
    rintro _ ⟨⟨hz, hz3⟩, x, rfl⟩
    refine ⟨x, ⟨(odd_toZ2_iff h2).1 hz, fun hx => hz3 ?_⟩, rfl⟩
    rw [three_mul_add_one_map, hx, map_zero]
  refine Set.EqOn.of_subset_closure (s := toZ2 h2 '' {x | Odd x ∧ 3 * x + 1 ≠ 0}) ?_ hg
    (continuousOn_T_padicInt.mono fun _ hz => hz.2) ?_ ?_
  · rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
    rw [h x hx hx3, T_toZ2]
  · rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
    refine ⟨(odd_toZ2_iff h2).2 hx, ?_⟩
    show 3 * toZ2 h2 x + 1 ≠ 0
    rw [three_mul_add_one_map]
    exact (map_ne_zero_iff _ (toZ2_injective h2)).2 hx3
  · exact (Dense.open_subset_closure_inter (denseRange_toZ2 h2) hV).trans (closure_mono hsub)

end Extension

/-! ### Finding 1: no continuous extension of `T_A` at `−1/3` -/

section Refutation

variable {A : Type*} [CommRing A] [IsZ2Ring A]

/-- A point with `3x + 1 ∈ 2A` is odd. -/
theorem odd_of_two_dvd_three_mul_add_one {x : A} (h : (2 : A) ∣ 3 * x + 1) : Odd x := by
  rcases IsZ2Ring.two_dvd_or_odd x with hx | hx
  · exfalso
    apply IsZ2Ring.not_two_dvd_one (A := A)
    have : (1 : A) = (3 * x + 1) - 3 * x := by ring
    rw [this]
    exact dvd_sub h (dvd_mul_of_dvd_right hx 3)
  · exact hx

/-- The integers `cⱼ = (4^{j+1} − 1)/3` and `dⱼ = (10·4^{j+1} − 1)/3`. -/
theorem exists_int_three_mul_add_one (j : ℕ) :
    ∃ c d : ℤ, 3 * c + 1 = 4 ^ (j + 1) ∧ 3 * d + 1 = 10 * 4 ^ (j + 1) := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (4 : ℤ) 1 (j + 1)
  norm_num at hc
  exact ⟨c, 10 * c + 3, by linear_combination -hc, by linear_combination -10 * hc⟩

/-- **The obstruction at `−1/3`.** Let `B` be a Hausdorff ℤ/2ℤ-ring with its 2-adic topology and
`2 ≠ 0`, `φ : A → B` a ring hom and `z₀ ∈ B` with `3z₀ + 1 = 0`. No `g : B → B` continuous at `z₀`
within `2B + 1` satisfies `g ∘ φ = φ ∘ T_A` on the odd `x` with `3x + 1 ≠ 0`: along
`φ(cⱼ) → z₀` the values are `φ(T cⱼ) = 1`, along `φ(dⱼ) → z₀` they are `5`. -/
theorem not_continuousWithinAt_extension_T {B : Type*} [CommRing B] [IsZ2Ring B]
    [TopologicalSpace B] [T2Space B] (hB : IsAdic (Ideal.span {(2 : B)})) (h2 : (2 : B) ≠ 0)
    (φ : A →+* B) {z₀ : B} (hz₀ : 3 * z₀ + 1 = 0) {g : B → B}
    (hg : ContinuousWithinAt g {z | Odd z} z₀) :
    ¬ ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (φ x) = φ (T x) := by
  intro hgT
  have h2A : (2 : A) ≠ 0 := fun h => h2 (by rw [← map_ofNat φ 2, h, map_zero])
  choose c d hc hd using exists_int_three_mul_add_one
  have hcA : ∀ j, 3 * (c j : A) + 1 = 4 ^ (j + 1) := fun j => by
    have := congrArg (Int.cast : ℤ → A) (hc j)
    push_cast at this
    exact this
  have hdA : ∀ j, 3 * (d j : A) + 1 = 10 * 4 ^ (j + 1) := fun j => by
    have := congrArg (Int.cast : ℤ → A) (hd j)
    push_cast at this
    exact this
  have hTc : ∀ j, T (c j : A) = 1 := fun j =>
    (T_unique h2A (k := 2 * (j + 1)) odd_one (by rw [hcA, pow_mul]; ring)).2
  have hTd : ∀ j, T (d j : A) = 5 := fun j =>
    (T_unique h2A (k := 2 * (j + 1) + 1) ⟨2, by norm_num⟩ (by rw [hdA, pow_succ, pow_mul]; ring)).2
  have h4 : (4 : A) ≠ 0 := by
    rw [show (4 : A) = 2 * 2 by norm_num]
    exact mul_ne_zero h2A h2A
  have h5 : (5 : A) ≠ 0 := fun h =>
    not_two_dvd_of_odd IsZ2Ring.not_two_dvd_one (⟨2, by norm_num⟩ : Odd (5 : A)) (h ▸ dvd_zero 2)
  have hdvd4 : ∀ j, (2 : A) ^ (2 * (j + 1)) ∣ 4 ^ (j + 1) := fun j => by
    rw [pow_mul]
    norm_num
  -- `φ(u j) → z₀` as soon as `2^{2(j+1)} ∣ 3 u j + 1`
  have hconv : ∀ u : ℕ → A, (∀ j, (2 : A) ^ (2 * (j + 1)) ∣ 3 * u j + 1) →
      Tendsto (fun j => φ (u j)) atTop (𝓝 z₀) := by
    intro u hu
    rw [(hasBasis_nhds_two hB z₀).tendsto_right_iff]
    intro n _
    filter_upwards [eventually_ge_atTop n] with j hj
    have h1 : (2 : B) ^ (2 * (j + 1)) ∣ 3 ^ 1 * (φ (u j) - z₀) := by
      have e : (3 : B) ^ 1 * (φ (u j) - z₀) = φ (3 * u j + 1) := by
        rw [map_add, map_mul, map_ofNat, map_one]
        linear_combination -hz₀
      have := map_dvd φ (hu j)
      rw [map_pow, map_ofNat] at this
      rwa [e]
    exact (pow_dvd_pow 2 (by omega)).trans (two_pow_dvd_of_dvd_three_pow_mul h1)
  have key : ∀ (u : ℕ → A) (v : B), (∀ j, (2 : A) ^ (2 * (j + 1)) ∣ 3 * u j + 1) →
      (∀ j, Odd (u j)) → (∀ j, 3 * u j + 1 ≠ 0) → (∀ j, φ (T (u j)) = v) → g z₀ = v := by
    intro u v hu hodd hne hv
    have ht : Tendsto (fun j => φ (u j)) atTop (𝓝[{z | Odd z}] z₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hconv u hu, Eventually.of_forall fun j => (hodd j).map φ⟩
    have h' := hg.tendsto.comp ht
    have heq : (g ∘ fun j => φ (u j)) = fun _ => v :=
      funext fun j => by rw [Function.comp_apply, hgT _ (hodd j) (hne j), hv j]
    rw [heq] at h'
    exact tendsto_nhds_unique h' tendsto_const_nhds
  have e1 : g z₀ = 1 := key (fun j => (c j : A)) 1
    (fun j => by rw [hcA]; exact hdvd4 j)
    (fun j => odd_of_two_dvd_three_mul_add_one
      (by rw [hcA, pow_succ]; exact dvd_mul_of_dvd_right ⟨2, by norm_num⟩ _))
    (fun j => by rw [hcA]; exact pow_ne_zero _ h4)
    (fun j => by rw [hTc, map_one])
  have e5 : g z₀ = 5 := key (fun j => (d j : A)) 5
    (fun j => by rw [hdA]; exact dvd_mul_of_dvd_right (hdvd4 j) _)
    (fun j => odd_of_two_dvd_three_mul_add_one
      (by rw [hdA]; exact dvd_mul_of_dvd_left ⟨5, by norm_num⟩ _))
    (fun j => by
      rw [hdA, show (10 : A) = 2 * 5 by norm_num]
      exact mul_ne_zero (mul_ne_zero h2A h5) (pow_ne_zero _ h4))
    (fun j => by rw [hTd, map_ofNat])
  have h15 : (2 : B) * 2 = 0 := by linear_combination e1 - e5
  exact mul_ne_zero h2 h2 h15

omit [IsZ2Ring A] in
/-- `3 · (−1/3) + 1 = 0` in `ℤ₂`. -/
theorem three_mul_neg_inv3_add_one : 3 * (-inv3) + 1 = 0 := by
  rw [mul_neg, three_mul_inv3, neg_add_cancel]

/-- **Finding 1 in `ℤ₂`.** For every ℤ/2ℤ-ring `A` with `2 ≠ 0`, no `g : ℤ₂ → ℤ₂` continuous at
`−1/3` within `2ℤ₂ + 1` agrees with `ι ∘ T_A` on the odd `x` of `A` (with `3x + 1 ≠ 0`). -/
theorem not_exists_continuousWithinAt_extension_T (h2 : (2 : A) ≠ 0) :
    ¬ ∃ g : ℤ_[2] → ℤ_[2], ContinuousWithinAt g {z | Odd z} (-inv3) ∧
      ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x) :=
  fun ⟨_, hg, hgT⟩ => not_continuousWithinAt_extension_T isAdic_padicInt two_ne_zero (toZ2 h2)
    three_mul_neg_inv3_add_one hg hgT

omit [IsZ2Ring A] in
/-- **Finding 1 at `A = ℤ`**, where `T_ℤ` is the paper's map on all of `2ℤ + 1`: it has no
continuous extension to `2ℤ₂ + 1`. -/
theorem T_int_not_extends :
    ¬ ∃ g : ℤ_[2] → ℤ_[2], ContinuousOn g {z | Odd z} ∧
      ∀ x : ℤ, Odd x → g (x : ℤ_[2]) = ((T x : ℤ) : ℤ_[2]) :=
  fun ⟨_, hg, hgT⟩ => not_continuousWithinAt_extension_T isAdic_padicInt two_ne_zero
    (Int.castRingHom ℤ_[2]) three_mul_neg_inv3_add_one (hg _ odd_inv3.neg)
    (fun x hx _ => hgT x hx)

omit [IsZ2Ring A] in
/-- **Finding 1, the printed statement refuted.** "For every ℤ/2ℤ-ring `A` (with `2 ≠ 0`), `T_A`
extends continuously to `2A₂ + 1 = 2ℤ₂ + 1`" is false (at `A = ℤ`). Agreement is asked only where
`T_A` is defined (`3x + 1 ≠ 0`), so the negated statement is exactly the printed one (AUDIT-1). -/
theorem printed_T_extends_false :
    ¬ ∀ (B : Type) [CommRing B] [IsZ2Ring B] (h2 : (2 : B) ≠ 0),
      ∃ g : ℤ_[2] → ℤ_[2], ContinuousOn g {z | Odd z} ∧
        ∀ x : B, Odd x → 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x) := by
  intro h
  obtain ⟨g, hg, hgT⟩ := h ℤ two_ne_zero
  exact not_exists_continuousWithinAt_extension_T (A := ℤ) two_ne_zero
    ⟨g, hg _ odd_inv3.neg, fun x hx h3 => hgT x hx h3⟩

omit [IsZ2Ring A] in
/-- `T_{ℤ₂}` (with its junk value `0` at `−1/3`) is not continuous on `2ℤ₂ + 1`. -/
theorem not_continuousWithinAt_T_padicInt :
    ¬ ContinuousWithinAt (T : ℤ_[2] → ℤ_[2]) {z | Odd z} (-inv3) := fun hg =>
  not_continuousWithinAt_extension_T isAdic_padicInt two_ne_zero (RingHom.id ℤ_[2])
    three_mul_neg_inv3_add_one hg (fun _ _ _ => rfl)

end Refutation

/-! ### `A₂ ≃ ℤ₂` (l.52) -/

section Completion

variable {A : Type*} [CommRing A] [IsZ2Ring A]

/-- `ι` induces the 2-adic topology of `A`. -/
theorem isInducing_toZ2 [TopologicalSpace A] (hA : IsAdic (Ideal.span {(2 : A)}))
    (h2 : (2 : A) ≠ 0) : IsInducing (toZ2 h2) := by
  rw [isInducing_iff_nhds]
  intro x
  refine (hasBasis_nhds_two hA x).eq_of_same_basis ?_
  refine ((hasBasis_nhds_two isAdic_padicInt (toZ2 h2 x)).comap (toZ2 h2)).congr
    (fun _ => Iff.rfl) (fun n _ => ?_)
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ← map_sub, two_pow_dvd_toZ2_iff]

theorem isEmbedding_toZ2 [TopologicalSpace A] (hA : IsAdic (Ideal.span {(2 : A)}))
    (h2 : (2 : A) ≠ 0) : IsEmbedding (toZ2 h2) :=
  ⟨isInducing_toZ2 hA h2, toZ2_injective h2⟩

/-- `(ℤ₂, ι)` is a completion of `A` for its 2-adic uniformity. -/
noncomputable def completionPkg [UniformSpace A] [IsUniformAddGroup A]
    (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) : AbstractCompletion A where
  space := ℤ_[2]
  coe := toZ2 h2
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing (f := toZ2 h2)
    (isInducing_toZ2 hA h2)
  dense := denseRange_toZ2 h2

/-- **`A₂ ≃ ℤ₂` (l.52), for `2 ≠ 0`.** The completion of `A` for a 2-adic uniform ring structure
is isomorphic to `ℤ₂`, as a ring and as a uniform space, by an isomorphism extending `ι`. -/
theorem completion_ringEquiv [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    ∃ e : UniformSpace.Completion A ≃+* ℤ_[2], (∀ x : A, e x = toZ2 h2 x) ∧
      UniformContinuous e ∧ UniformContinuous e.symm := by
  have hc : Continuous (toZ2 h2) := (isInducing_toZ2 hA h2).continuous
  let E : UniformSpace.Completion A ≃ᵤ ℤ_[2] :=
    UniformSpace.Completion.cPkg.compareEquiv (completionPkg hA h2)
  let e : UniformSpace.Completion A ≃+* ℤ_[2] :=
    RingEquiv.ofBijective (UniformSpace.Completion.extensionHom (toZ2 h2) hc) E.bijective
  have heE : ∀ w, e w = E w := fun _ => rfl
  have hsymm : ∀ z, e.symm z = E.symm z := fun z => by
    apply E.injective
    rw [← heE, RingEquiv.apply_symm_apply, UniformEquiv.apply_symm_apply]
  refine ⟨e, fun x => UniformSpace.Completion.extensionHom_coe _ hc x, ?_, ?_⟩
  · exact (funext heE : ⇑e = ⇑E) ▸ E.uniformContinuous
  · exact (funext hsymm : ⇑e.symm = ⇑E.symm) ▸ E.symm.uniformContinuous

omit [IsZ2Ring A] in
/-- **"Naturally"**: there is at most one ring isomorphism onto `ℤ₂` (`ℤ₂` has no ring
endomorphism but the identity), so the isomorphism `A₂ ≃ ℤ₂` is unique. -/
theorem ringEquiv_padicInt_unique {B : Type*} [Semiring B] (e e' : B ≃+* ℤ_[2]) : e = e' := by
  have h : (e.symm.trans e').toRingHom = RingHom.id ℤ_[2] :=
    (toZ2_unique two_ne_zero _).trans (toZ2_unique two_ne_zero _).symm
  ext w
  have := congrArg (fun φ : ℤ_[2] →+* ℤ_[2] => φ (e w)) h
  simpa using this.symm

/-- `A₂ ≃ ℤ₂` for the canonical 2-adic structure of `A` (`WithIdeal`). -/
theorem completion_twoAdic (h2 : (2 : A) ≠ 0) :
    letI : WithIdeal A := ⟨Ideal.span {(2 : A)}⟩
    ∃ e : UniformSpace.Completion A ≃+* ℤ_[2], (∀ x : A, e x = toZ2 h2 x) ∧
      UniformContinuous e ∧ UniformContinuous e.symm := by
  letI : WithIdeal A := ⟨Ideal.span {(2 : A)}⟩
  exact completion_ringEquiv isAdic_withIdeal h2

omit [IsZ2Ring A] in
/-- **Finding 3 (l.52).** The ℤ/2ℤ-ring `ℤ/2ℤ` has no completion isomorphic to `ℤ₂`, for any
uniform ring structure: its completion has `2 = 0`. -/
theorem completion_zmod2_not_padicInt [UniformSpace (ZMod 2)] [IsUniformAddGroup (ZMod 2)]
    [IsTopologicalRing (ZMod 2)] : IsEmpty (UniformSpace.Completion (ZMod 2) ≃+* ℤ_[2]) := by
  refine ⟨fun e => ?_⟩
  have h : (2 : UniformSpace.Completion (ZMod 2)) = 0 := by
    have : ((2 : ZMod 2) : UniformSpace.Completion (ZMod 2)) =
        ((0 : ZMod 2) : UniformSpace.Completion (ZMod 2)) := by
      congr 1
    rwa [← map_ofNat (UniformSpace.Completion.coeRingHom (α := ZMod 2)) 2,
      ← map_zero (UniformSpace.Completion.coeRingHom (α := ZMod 2))]
  have := congrArg e h
  rw [map_ofNat, map_zero] at this
  exact two_ne_zero this

omit [IsZ2Ring A] in
/-- **Finding 3 for the 2-adic structure of `ℤ/2ℤ`.** -/
theorem completion_zmod2_twoAdic_not_padicInt :
    letI : WithIdeal (ZMod 2) := ⟨Ideal.span {(2 : ZMod 2)}⟩
    IsEmpty (UniformSpace.Completion (ZMod 2) ≃+* ℤ_[2]) := by
  letI : WithIdeal (ZMod 2) := ⟨Ideal.span {(2 : ZMod 2)}⟩
  exact completion_zmod2_not_padicInt

omit [IsZ2Ring A] in
/-- **Integrality is load-bearing for l.52 (OQ-42 (a)).** `ZMod 4` is noetherian, has
`A/2A ≃ ℤ/2ℤ` and `2 ≠ 0`, is not a domain, and no completion of it is `ℤ₂` (it has `4 = 0`). -/
theorem zmod4_witness :
    IsNoetherianRing (ZMod 4) ∧ Nonempty ((ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}) ≃+* ZMod 2) ∧
      (2 : ZMod 4) ≠ 0 ∧ ¬ IsDomain (ZMod 4) ∧
      ∀ [UniformSpace (ZMod 4)] [IsUniformAddGroup (ZMod 4)] [IsTopologicalRing (ZMod 4)],
        IsEmpty (UniformSpace.Completion (ZMod 4) ≃+* ℤ_[2]) := by
  have hpar : ∀ x : ZMod 4, (∃ c, x = 2 * c) ∨ (∃ c, x - 1 = 2 * c) := by decide
  have h1 : ¬ ∃ c : ZMod 4, (1 : ZMod 4) = 2 * c := by decide
  refine ⟨inferInstance, quotient_two_of_parity h1 hpar, by decide, fun hd => ?_, fun {_ _ _} => ?_⟩
  · have h22 : (2 : ZMod 4) * 2 = 0 := by decide
    exact (mul_ne_zero (by decide : (2 : ZMod 4) ≠ 0) (by decide : (2 : ZMod 4) ≠ 0)) h22
  · refine ⟨fun e => ?_⟩
    have h : (4 : UniformSpace.Completion (ZMod 4)) = 0 := by
      have : ((4 : ZMod 4) : UniformSpace.Completion (ZMod 4)) =
          ((0 : ZMod 4) : UniformSpace.Completion (ZMod 4)) := by
        congr 1
      rwa [← map_ofNat (UniformSpace.Completion.coeRingHom (α := ZMod 4)) 4,
        ← map_zero (UniformSpace.Completion.coeRingHom (α := ZMod 4))]
    have := congrArg e h
    rw [map_ofNat, map_zero] at this
    exact (by norm_num : (4 : ℤ_[2]) ≠ 0) this

end Completion

/-! ### The proposition in `A₂ = UniformSpace.Completion A` -/

/-- A ring isomorphic to a ℤ/2ℤ-ring is one. -/
theorem isZ2Ring_of_ringEquiv {A B : Type*} [CommRing A] [IsZ2Ring A] [CommRing B]
    (e : B ≃+* A) : IsZ2Ring B := by
  haveI : IsDomain B := MulEquiv.isDomain A e.toMulEquiv
  haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e.symm
  refine IsZ2Ring.of_parity (fun h => ?_) (fun x => ?_)
  · have h' := map_dvd e h
    rw [map_ofNat, map_one] at h'
    exact IsZ2Ring.not_two_dvd_one h'
  · rcases IsZ2Ring.two_dvd_or_two_dvd_sub_one (e x) with h | h
    · left
      have h' := map_dvd e.symm h
      rwa [map_ofNat, RingEquiv.symm_apply_apply] at h'
    · right
      have h' := map_dvd e.symm h
      rwa [map_ofNat, map_sub, map_one, RingEquiv.symm_apply_apply] at h'

section Literal

variable {A : Type*} [CommRing A] [IsZ2Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A]

open UniformSpace

/-- `A₂` is a ℤ/2ℤ-ring (so `f_{A₂}`, `T_{A₂}` are the maps of `def:ring_define`). -/
theorem isZ2Ring_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    IsZ2Ring (Completion A) := by
  obtain ⟨e, -⟩ := completion_ringEquiv hA h2
  exact isZ2Ring_of_ringEquiv e

theorem two_ne_zero_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    (2 : Completion A) ≠ 0 := by
  obtain ⟨e, -⟩ := completion_ringEquiv hA h2
  intro h
  have := congrArg e h
  rw [map_ofNat, map_zero] at this
  exact two_ne_zero this

/-- `f_{A₂}` is continuous. -/
theorem continuous_f_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    Continuous (f : Completion A → Completion A) := by
  haveI := isZ2Ring_completion hA h2
  obtain ⟨e, -, hue, hues⟩ := completion_ringEquiv hA h2
  have hf : (f : Completion A → Completion A) = e.symm ∘ f ∘ e := funext fun w => by
    have key := f_map two_ne_zero (two_ne_zero_completion hA h2) e.symm.toRingHom (e w)
    simpa using key
  rw [hf]
  exact hues.continuous.comp (continuous_f_padicInt.comp hue.continuous)

/-- `f_{A₂}` extends `f_A`. -/
theorem f_coe_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) (x : A) :
    f (x : Completion A) = ((f x : A) : Completion A) := by
  haveI := isZ2Ring_completion hA h2
  exact f_map h2 (two_ne_zero_completion hA h2) Completion.coeRingHom x

/-- `f_{A₂}` is the only continuous extension of `f_A` to `A₂`. -/
theorem eq_f_completion_of_continuous (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0)
    {g : Completion A → Completion A} (hg : Continuous g)
    (h : ∀ x : A, g (x : Completion A) = ((f x : A) : Completion A)) : g = f :=
  Completion.denseRange_coe.equalizer hg (continuous_f_completion hA h2)
    (funext fun x => by simp only [Function.comp_apply, h, f_coe_completion hA h2])

/-- `T_{A₂}` is continuous off `−1/3`. -/
theorem continuousOn_T_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    ContinuousOn (T : Completion A → Completion A) {w | 3 * w + 1 ≠ 0} := by
  haveI := isZ2Ring_completion hA h2
  obtain ⟨e, -, hue, hues⟩ := completion_ringEquiv hA h2
  have hT : (T : Completion A → Completion A) = e.symm ∘ T ∘ e := funext fun w => by
    have key := T_map two_ne_zero (two_ne_zero_completion hA h2) e.symm.toRingHom (e w)
    simpa using key
  intro w hw
  rw [hT]
  refine (hues.continuous.continuousAt.comp ((continuousAt_T isAdic_padicInt ?_).comp
    hue.continuous.continuousAt)).continuousWithinAt
  rw [three_mul_add_one_map e]
  exact (map_ne_zero_iff _ e.injective).2 hw

/-- `T_{A₂}` extends `T_A`. -/
theorem T_coe_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) (x : A) :
    T (x : Completion A) = ((T x : A) : Completion A) := by
  haveI := isZ2Ring_completion hA h2
  exact T_map h2 (two_ne_zero_completion hA h2) Completion.coeRingHom x

/-- `T_{A₂}` is the only continuous extension of `T_A` to `A₂ ∖ {−1/3}`. -/
theorem eqOn_T_completion_of_continuousOn (hA : IsAdic (Ideal.span {(2 : A)}))
    (h2 : (2 : A) ≠ 0) {g : Completion A → Completion A}
    (hg : ContinuousOn g {w | 3 * w + 1 ≠ 0})
    (h : ∀ x : A, 3 * x + 1 ≠ 0 → g (x : Completion A) = ((T x : A) : Completion A)) :
    Set.EqOn g T {w | 3 * w + 1 ≠ 0} := by
  have hcoe : ∀ x : A, 3 * (x : Completion A) + 1 = ((3 * x + 1 : A) : Completion A) :=
    fun x => three_mul_add_one_map (Completion.coeRingHom (α := A)) x
  have hV : IsOpen {w : Completion A | 3 * w + 1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hsub : {w : Completion A | 3 * w + 1 ≠ 0} ∩ Set.range ((↑) : A → Completion A) ⊆
      (↑) '' {x : A | 3 * x + 1 ≠ 0} := by
    rintro _ ⟨hw, x, rfl⟩
    refine ⟨x, fun hx => hw ?_, rfl⟩
    rw [hcoe, hx, Completion.coe_zero]
  refine Set.EqOn.of_subset_closure (s := (↑) '' {x : A | 3 * x + 1 ≠ 0}) ?_ hg
    (continuousOn_T_completion hA h2) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [h x hx, T_coe_completion hA h2]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, -⟩ := completion_ringEquiv hA h2
    show 3 * (x : Completion A) + 1 ≠ 0
    rw [hcoe]
    intro h0
    apply (map_ne_zero_iff _ (toZ2_injective h2)).2 hx
    rw [← he, h0, map_zero]
  · exact (Dense.open_subset_closure_inter Completion.denseRange_coe hV).trans (closure_mono hsub)

/-- On the paper's domain: the continuous extension of `T_A : 2A + 1 → 2A + 1` to
`(2A₂ + 1) ∖ {−1/3}` is unique, and it is `T_{A₂}`. -/
theorem eqOn_T_completion_of_continuousOn_odd (hA : IsAdic (Ideal.span {(2 : A)}))
    (h2 : (2 : A) ≠ 0) {g : Completion A → Completion A}
    (hg : ContinuousOn g {w | Odd w ∧ 3 * w + 1 ≠ 0})
    (h : ∀ x : A, Odd x → 3 * x + 1 ≠ 0 →
      g (x : Completion A) = ((T x : A) : Completion A)) :
    Set.EqOn g T {w | Odd w ∧ 3 * w + 1 ≠ 0} := by
  obtain ⟨e, he, hue, -⟩ := completion_ringEquiv hA h2
  have hcoe : ∀ x : A, 3 * (x : Completion A) + 1 = ((3 * x + 1 : A) : Completion A) :=
    fun x => three_mul_add_one_map (Completion.coeRingHom (α := A)) x
  have hodd : ∀ w : Completion A, Odd w ↔ Odd (e w) := fun w =>
    ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
  have hoddc : ∀ x : A, Odd (x : Completion A) ↔ Odd x := fun x => by
    rw [hodd, he, odd_toZ2_iff h2]
  have hO : IsOpen {w : Completion A | Odd w} := by
    have h1 : {w : Completion A | Odd w} = e ⁻¹' {z | Odd z} := by
      ext w
      exact hodd w
    rw [h1]
    exact (isOpen_odd isAdic_padicInt).preimage hue.continuous
  have hV : IsOpen {w : Completion A | Odd w ∧ 3 * w + 1 ≠ 0} :=
    hO.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  have hsub : {w : Completion A | Odd w ∧ 3 * w + 1 ≠ 0} ∩ Set.range ((↑) : A → Completion A) ⊆
      (↑) '' {x : A | Odd x ∧ 3 * x + 1 ≠ 0} := by
    rintro _ ⟨⟨hw, hw3⟩, x, rfl⟩
    refine ⟨x, ⟨(hoddc x).1 hw, fun hx => hw3 ?_⟩, rfl⟩
    rw [hcoe, hx, Completion.coe_zero]
  refine Set.EqOn.of_subset_closure (s := (↑) '' {x : A | Odd x ∧ 3 * x + 1 ≠ 0}) ?_ hg
    ((continuousOn_T_completion hA h2).mono fun _ hw => hw.2) ?_ ?_
  · rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
    rw [h x hx hx3, T_coe_completion hA h2]
  · rintro _ ⟨x, ⟨hx, hx3⟩, rfl⟩
    refine ⟨(hoddc x).2 hx, ?_⟩
    show 3 * (x : Completion A) + 1 ≠ 0
    rw [hcoe]
    intro h0
    apply (map_ne_zero_iff _ (toZ2_injective h2)).2 hx3
    rw [← he, h0, map_zero]
  · exact (Dense.open_subset_closure_inter Completion.denseRange_coe hV).trans (closure_mono hsub)

/-- `−1/3 ∈ 2A₂ + 1`. -/
theorem exists_neg_third_completion (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    ∃ w₀ : Completion A, Odd w₀ ∧ 3 * w₀ + 1 = 0 := by
  obtain ⟨e, -⟩ := completion_ringEquiv hA h2
  refine ⟨e.symm (-inv3), odd_inv3.neg.map e.symm, ?_⟩
  rw [three_mul_add_one_map e.symm, three_mul_neg_inv3_add_one, map_zero]

/-- **Finding 1 in `A₂`.** No extension of `T_A` to `A₂` is continuous at `−1/3` within
`2A₂ + 1`. -/
theorem not_exists_continuousWithinAt_extension_T_completion
    (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) {w₀ : Completion A}
    (hw₀ : 3 * w₀ + 1 = 0) :
    ¬ ∃ g : Completion A → Completion A, ContinuousWithinAt g {w | Odd w} w₀ ∧
      ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (x : Completion A) = ((T x : A) : Completion A) := by
  rintro ⟨g, hg, hgT⟩
  obtain ⟨e, he, hue, hues⟩ := completion_ringEquiv hA h2
  have he0 : 3 * e w₀ + 1 = 0 := by
    rw [three_mul_add_one_map e, hw₀, map_zero]
  have hsymm : ∀ x : A, e.symm (toZ2 h2 x) = (x : Completion A) := fun x => by
    rw [← he, RingEquiv.symm_apply_apply]
  refine not_continuousWithinAt_extension_T isAdic_padicInt two_ne_zero (toZ2 h2) he0
    (g := e ∘ g ∘ e.symm) ?_ ?_
  · have h1 : ContinuousWithinAt (g ∘ e.symm) {z : ℤ_[2] | Odd z} (e w₀) := by
      refine ContinuousWithinAt.comp (t := {w | Odd w}) ?_
        hues.continuous.continuousWithinAt (fun z hz => hz.map e.symm)
      rw [RingEquiv.symm_apply_apply]
      exact hg
    exact hue.continuous.continuousAt.comp_continuousWithinAt h1
  · intro x hx hx3
    simp only [Function.comp_apply]
    rw [hsymm, hgT x hx hx3, he]

/-- **`prop:ring_both_continuous_extends`, strongest true form** (unmarked: Finding 1), with
`A₂ = UniformSpace.Completion A`: `f_A` is continuous; `T_A` is continuous where defined; `f_A`
extends continuously to `A₂` and its only continuous extension is `f_{A₂}`; `T_{A₂}` is continuous
on `A₂ ∖ {−1/3}`, extends `T_A`, and is the only continuous extension of `T_A : 2A + 1 → 2A + 1`
to `(2A₂ + 1) ∖ {−1/3}`; and `T_A` has no extension continuous at `−1/3 ∈ 2A₂ + 1` within
`2A₂ + 1`. -/
theorem ring_both_continuous_extends (hA : IsAdic (Ideal.span {(2 : A)})) (h2 : (2 : A) ≠ 0) :
    Continuous (f : A → A) ∧ ContinuousOn (T : A → A) {x | 3 * x + 1 ≠ 0} ∧
      (Continuous (f : Completion A → Completion A) ∧
        (∀ x : A, f (x : Completion A) = ((f x : A) : Completion A)) ∧
        ∀ g : Completion A → Completion A, Continuous g →
          (∀ x : A, g (x : Completion A) = ((f x : A) : Completion A)) → g = f) ∧
      (ContinuousOn (T : Completion A → Completion A) {w | 3 * w + 1 ≠ 0} ∧
        (∀ x : A, T (x : Completion A) = ((T x : A) : Completion A)) ∧
        ∀ g : Completion A → Completion A, ContinuousOn g {w | Odd w ∧ 3 * w + 1 ≠ 0} →
          (∀ x : A, Odd x → 3 * x + 1 ≠ 0 →
            g (x : Completion A) = ((T x : A) : Completion A)) →
          Set.EqOn g T {w | Odd w ∧ 3 * w + 1 ≠ 0}) ∧
      ∃ w₀ : Completion A, Odd w₀ ∧ 3 * w₀ + 1 = 0 ∧
        ¬ ∃ g : Completion A → Completion A, ContinuousWithinAt g {w | Odd w} w₀ ∧
          ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (x : Completion A) = ((T x : A) : Completion A) := by
  have hA' : IsAdic (Ideal.span {(2 : A)}) := hA
  obtain ⟨w₀, hw₀, hw₀'⟩ := exists_neg_third_completion hA h2
  exact ⟨continuous_f hA', continuousOn_T hA',
    ⟨continuous_f_completion hA h2, f_coe_completion hA h2,
      fun _ hg h => eq_f_completion_of_continuous hA h2 hg h⟩,
    ⟨continuousOn_T_completion hA h2, T_coe_completion hA h2,
      fun _ hg h => eqOn_T_completion_of_continuousOn_odd hA h2 hg h⟩,
    w₀, hw₀, hw₀', not_exists_continuousWithinAt_extension_T_completion hA h2 hw₀'⟩

end Literal

/-- **`prop:ring_both_continuous_extends` in `ℤ₂`** (the model of `A₂` through `ι`, unmarked). -/
theorem ring_both_continuous_extends_padicInt {A : Type*} [CommRing A] [IsZ2Ring A]
    (h2 : (2 : A) ≠ 0) :
    (Continuous (f : ℤ_[2] → ℤ_[2]) ∧ (∀ x : A, f (toZ2 h2 x) = toZ2 h2 (f x)) ∧
        ∀ g : ℤ_[2] → ℤ_[2], Continuous g → (∀ x : A, g (toZ2 h2 x) = toZ2 h2 (f x)) → g = f) ∧
      (ContinuousOn (T : ℤ_[2] → ℤ_[2]) {z | 3 * z + 1 ≠ 0} ∧
        (∀ x : A, T (toZ2 h2 x) = toZ2 h2 (T x)) ∧
        ∀ g : ℤ_[2] → ℤ_[2], ContinuousOn g {z | Odd z ∧ 3 * z + 1 ≠ 0} →
          (∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x)) →
          Set.EqOn g T {z | Odd z ∧ 3 * z + 1 ≠ 0}) ∧
      ¬ ∃ g : ℤ_[2] → ℤ_[2], ContinuousWithinAt g {z | Odd z} (-inv3) ∧
        ∀ x : A, Odd x → 3 * x + 1 ≠ 0 → g (toZ2 h2 x) = toZ2 h2 (T x) :=
  ⟨⟨continuous_f_padicInt, f_toZ2 h2, fun _ hg h => eq_f_of_continuous h2 hg h⟩,
    ⟨continuousOn_T_padicInt, T_toZ2 h2, fun _ hg h => eqOn_T_of_continuousOn_odd h2 hg h⟩,
    not_exists_continuousWithinAt_extension_T h2⟩

end Syracuse
