import Syracuse.Rep
import Syracuse.IntegerBounds

/-!
# Syracuse § 2: the GCD identity of a cycle, the valuations of `A_i − A_j`, and ε-circuits

Every label is marked under DEC-183 (OQ-63), the first two in corrected form, the third in the
reading of its misprint (SCOPE):

* **`prop:have_gcd_n__l_k`** — `syracuse.tex:171` (l.171–175, proof l.176–188) — marked in corrected
  form (DEC-183, OQ-63 (a): the GCD is `|2^{p_n(x)} − 3ⁿ|`; (b): the index convention of l.62) on
  `Syracuse.have_gcd`, on every cycle of `ℤ` (the convention of l.71: `have_gcd_shift`; up to sign:
  `have_gcd_associated`; as printed for `x > 0`: `have_gcd_of_pos`). **False as printed** on every
  cycle of `x < 0`, e.g. `(−1)` (`have_gcd_printed_false`, `have_gcd_printed_false_shift`): Finding 1.
* **`lem:periodic_exists_i_a_i_`** — `syracuse.tex:207` (l.207–212) — marked in corrected form
  (DEC-183, OQ-63 (c): `n` the minimal period, the agreement on `⟦0, p−1⟧`, the bound
  `∑_{k=0}^{p−1} a_{i+k}`; OQ-43: the printed `A_u^n`) on `Syracuse.periodic_exists_corrected`, its
  three conclusions (`periodic_exists_corrected_alt` for the other reading of OQ-43). **False as
  printed**: `A_i − A_j ≠ 0` without the minimal period (`periodic_exists_printed_false`), and the
  `ν₂` conjunct even with it (`periodic_exists_nu2_printed_false`): Findings 3, 4.
* **`def:circuit`** — `syracuse.tex:213` (l.213–217) — marked in corrected form (DEC-183, OQ-63 (d):
  the orbit `(Tⁿ(x))_n` for the printed `(x)_{n∈ℕ}`, and `p ≥ εn − 1` as printed) on
  `Syracuse.IsCircuit`. Read literally the definition is degenerate: every integer is an
  `ε`-circuit for every `ε ≤ 1` (`isCircuitLiteral_of_le_one`): Finding 6.

> Our starting point is the following.
> **prop:have_gcd_n__l_k.** Let $x\in \ZZ$ and $n\in \NN^*$ such that $T^n(x)=x$. We have :
> $$ 2^{p_n(x)}-3^n = \mathrm{GCD}\left(\sum_{k=0}^{n-1}3^k 2^{p_n(x)-\sum_{i=l-k}^{l} a_i(x) } :
> l \in \lsem 0,n-1 \rsem \right) $$
> *Proof.* From Lemma \ref{lem:base},
> $$\forall l\in \lsem0,n-1\rsem,\quad\left( 2^{p_n(x)}-3^n\right)T^l(x) =
> \sum_{k=0}^{n-1}3^k 2^{p_n(x)-\sum_{i=l-k}^{l} a_i(x) }$$ thus […] And since,
> $$3\sum_{k=0}^{n-1}3^k 2^{p_n(x)-\sum_{i=-k}^{0} a_i(x) }-2^{a_1(x)}\sum_{k=0}^{n-1}3^k
> 2^{p_n(x)-\sum_{i=1-k}^{1} a_i(x) } = 3^n-2^{p_n(x)} $$ we have the result.

> **lem:periodic_exists_i_a_i_.** Let $n,p\in\NN^*$ with $p< n$ and let $a \in (\NN^*)^\ZZ$
> $n$-periodic, if there exists $i,j\in \lsem 0,n-1\rsem$, such that $$i\neq j\quad \text{and}\quad
> \forall k\in\lsem 1,p\rsem,~  a_{i+k}=a_{j+k} $$ then :
> $$ \nu_2(A_i-A_j)\geq \sum_{k=1}^p a_k \quad \text{and}\quad  \nu_3(A_{p+i}-A_{p+j})\geq p  $$
> $$A_i- A_j \neq 0 $$

> **def:circuit** ($\varepsilon$-circuit). Let $x\in \ZZ$ and $\varepsilon>0$.
> $\left(x\right)_{n\in\NN}$ is an $\varepsilon$-circuit if the sequence is $n$-periodic for some
> $n\in\NN^*$ and their exists a term $y$ in the sequence such that
> $$\forall i \in \lsem 1,p\rsem,~a_i(y)=1$$ for some $p\geq \varepsilon n-1$.
> Notice that a circuit (in the sense Steinitz) is a 1-circuit.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `x ∈ ℤ`, `n ∈ ℕ*`, `Tⁿx = x` (`prop:have_gcd_n__l_k`) | ✓ carried; ⚠ weakened to any commutative ring for the display and the Bézout step (`gcdSum_cycle`, `gcd_bezout`) |
| `a_i(x)` at `i < 0` (l.173, the sum from `l − k`) | a reading: any `n`-periodic `α : ℤ → ℕ` with `α k = a_k(x)` on `ℕ`; one exists (`aPer`) |
| the index of `a_i` (l.62 against l.71) | both: `α_k = a_k(x)` (`have_gcd`), `β_{k+1} = a_k(x)` (`have_gcd_shift`): Finding 2 |
| GCD (l.173) | the normalized GCD of `ℤ` (`Finset.gcd`, `≥ 0`); the reading "a GCD, up to sign" is `have_gcd_associated` |
| `n, p ∈ ℕ*`, `p < n` (`lem:periodic_exists_i_a_i_`) | ✓ carried in the printed forms; ⚠ weakened (unused) in the general lemmas |
| `a ∈ (ℕ*)^ℤ` `n`-periodic | ✓ carried (`∀ k, 1 ≤ a k`, `Function.Periodic a n`); ⚠ weakened where unused |
| `i, j ∈ ⟦0, n−1⟧`, `i ≠ j`, `a_{i+k} = a_{j+k}` on `⟦1, p⟧` | ✓ carried in the printed forms; ⚠ the corrected form reads the agreement on `⟦0, p−1⟧`: Finding 4 |
| (none) the minimal period of `a` is `n` | ⚠ strengthened for `A_i − A_j ≠ 0`: Finding 3 |
| `A_i = A_i^n(a)` (`def:define_n__n_`) | both readings of OQ-43: `Aun` (printed) and `AunAlt` (product to `n − 2 − k`) |
| `x ∈ ℤ`, `ε > 0` (`def:circuit`) | ✓ `x : ℤ`; ⚠ weakened: defined for every real `ε` |
| "`(x)_{n∈ℕ}`" (l.213) | a reading: the orbit `(Tⁿ(x))_n`; the literal constant sequence is degenerate (Finding 6) |

## SCOPE (disclosed)

* **Finding 1 (`prop:have_gcd_n__l_k`, l.173): false for every cycle of `x < 0`.** The GCD is
  `|2^{p_n(x)} − 3ⁿ|` on every cycle of `ℤ` (`have_gcd`), and `2^{p_n(x)} − 3ⁿ` has the sign of `x`
  (`two_pow_p_sub_three_pow_mul_pos`): the printed equality holds iff `x > 0` (`have_gcd_of_pos`,
  `have_gcd_of_neg`), and fails at the cycle `(−1)`, where `2 − 3 = −1` (`have_gcd_printed_false`).
  Read "up to sign" it holds on every cycle (`have_gcd_associated`).
* **Finding 2 (l.62 against l.71, l.178): two index conventions for `a_i`.** `def:ring_define_2`
  (l.62) has `a_0(x) = ν₂(3x+1)`; the proof of `lem:base` (l.71, l.75) writes `a_1(x) = p_1(x)` for it.
  In the convention of l.62 the `l`-th sum is `(2^{p_n} − 3ⁿ) T^{l+1}(x)`, for every `l ∈ ℕ` and in
  every commutative ring (`gcdSum_cycle`; it is the OQ-43 sum `A'^n_{l+1}`, `gcdSum_eq_AunAlt`), so the
  display of l.178 fails at `l = 0` on every cycle that is not a fixed point (`gcdSum_ne_display`),
  e.g. `(−5, −7)` (`gcd_display_printed_false`). In the convention of l.71 (`β_{k+1} = a_k(x)`) the
  display holds as printed (`gcdSum_cycle_shift`). The Bézout step of l.186 holds as printed in both
  (`gcd_bezout`, `gcd_bezout_shift`), and so do the GCD and Finding 1 (`have_gcd_shift`,
  `have_gcd_printed_false_shift`): the set of the `n` sums is the same up to a cyclic shift.
* **Finding 3 (`lem:periodic_exists_i_a_i_`, l.211): `A_i − A_j ≠ 0` needs the minimal period.**
  For `a ≡ 1`, `n = 2`, `p = 1`, `i = 0`, `j = 1` every hypothesis holds and `A_0 = A_1`, for both
  readings of OQ-43 (`periodic_exists_printed_false`, `periodic_exists_printed_false_alt`). With `n`
  the minimal period of `a` it holds for both (`Aun_sub_ne_zero_of_minimal`,
  `AunAlt_sub_ne_zero_of_minimal`).
* **Finding 4 (l.209, the `ν₂` conjunct): off by an index.** With `a = (1, 2, 2)`, `n = 3`, `p = 1`,
  `i = 0`, `j = 1`, of minimal period `3`, `ν₂(A_0 − A_1) = ν₂(−42) = 1 < 2 = a_1` (and
  `ν₂(A'_0 − A'_1) = ν₂(−14) = 1`) (`periodic_exists_nu2_printed_false`,
  `periodic_exists_nu2_printed_false_alt`); `i = 0` makes `∑_{k=1}^p a_k = ∑_{k=1}^p a_{i+k}`, so
  the bound read as `∑_{k=1}^p a_{i+k}` fails too (`periodic_exists_nu2_shifted_bound_false`,
  `_alt`). True: an agreement `a_{u+t} = a_{v+t}` for `t < q` gives
  `2^{∑_{t<q} a_{u+t} + min(a_{u+q}, a_{v+q})} ∣ A_u − A_v`, for both readings, with no periodicity
  (`two_pow_dvd_Aun_sub`, `two_pow_dvd_AunAlt_sub`). Under the printed agreement this is
  `ν₂(A_{i+1} − A_{j+1}) ≥ ∑_{k=1}^p a_{i+k}` (`periodic_exists_nu2_shift`, `_alt`); under the
  agreement on `⟦0, p−1⟧` it is `ν₂(A_i − A_j) ≥ ∑_{k=0}^{p−1} a_{i+k}`
  (`periodic_exists_corrected`, `_alt`).
* **The `ν₃` conjunct (l.209) holds as printed for the printed `A_u^n`** (`periodic_exists_nu3`),
  from the agreement on `⟦1, p−1⟧` alone (`three_pow_dvd_Aun_sub`). **Finding 5: it fails for the
  OQ-43 reading**: with `a = (1, 2, 2)`, `p = 1`, `i = 0`, `j = 1`, `A'_1 − A'_2 = 8`
  (`periodic_exists_nu3_printed_false_alt`). Under periodicity `A_u − A_v = 3 (A'_u − A'_v)`
  (`Aun_sub_eq_three_mul`, from `Aun_eq_three_mul_AunAlt`), so `ν₃` drops by one; the OQ-43 reading
  needs the agreement on `⟦0, p−1⟧` (`three_pow_dvd_AunAlt_sub`).
* **Finding 6 (`def:circuit`, l.213): "`(x)_{n∈ℕ}`" is the constant sequence.** Read literally,
  every integer is an `ε`-circuit for every `ε ≤ 1` (`isCircuitLiteral_of_le_one`), `3` included,
  whose orbit is not periodic (`not_isCircuit_three`). `IsCircuit` reads it as the orbit
  `(Tⁿ(x))_n`, with `p ≥ εn − 1` as printed (the proof of l.222 uses `p ≥ εn`). With `ε ≥ 0`, `n`
  may be taken minimal (`isCircuit_iff_minimalPeriod`). The cycle `(−1)` is an `ε`-circuit for
  every `ε`, `(1)` iff `ε ≤ 1`, `(−5, −7)` is a 1-circuit (`isCircuit_neg_one`, `isCircuit_one_iff`,
  `isCircuit_neg_five`). The remark on Steiner's circuits is commentary; the shape it describes
  (`a_1 = ⋯ = a_{n−1} = 1` at a point of the cycle) is a 1-circuit (`isCircuit_one_of_run`).
* `T`, `a`, `p` are the total maps of `Syracuse.Base`; over `ℤ` they are the paper's
  (`not_isUnit_three_int`), and a point of a cycle is odd and its orbit avoids `−1/3`
  (`cycle_avoids_neg_third`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

/-! ### Sums over windows of a periodic sequence on `ℤ` -/

/-- `∑_{i ∈ ⟦c, c+q−1⟧} f i = ∑_{t<q} f (c + t)` over `ℤ`. -/
theorem sum_Ico_int_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (c : ℤ) (q : ℕ) :
    ∑ i ∈ Ico c (c + q), f i = ∑ t ∈ range q, f (c + t) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h : Ico c (c + ((q + 1 : ℕ) : ℤ)) = insert (c + q) (Ico c (c + q)) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; push_cast; omega
    rw [h, Finset.sum_insert (by simp), add_comm]

/-- `∑_{t<k+m} α(c+t) = ∑_{t<k} α(c+t) + ∑_{t<m} α(c+k+t)`. -/
theorem sum_range_add_int (α : ℤ → ℕ) (c : ℤ) (k m : ℕ) :
    ∑ t ∈ range (k + m), α (c + t) = ∑ t ∈ range k, α (c + t) + ∑ t ∈ range m, α (c + k + t) := by
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  push_cast; ring_nf

/-- Every window of `n` consecutive terms of an `n`-periodic `α : ℤ → ℕ` has the same sum. -/
theorem sum_range_periodic {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (c : ℤ) :
    ∑ t ∈ range n, α (c + t) = ∑ t ∈ range n, α t := by
  have h1 : ∀ c : ℤ, ∑ t ∈ range n, α (c + 1 + t) = ∑ t ∈ range n, α (c + t) := by
    intro c
    have e1 := sum_range_add_int α c n 1
    have e2 := sum_range_add_int α c 1 n
    rw [add_comm n 1] at e1
    simp only [Finset.sum_range_one, Nat.cast_zero, add_zero] at e1 e2
    rw [h c] at e1
    push_cast at e2
    omega
  induction c using Int.induction_on with
  | zero => simp
  | succ k ih => rw [h1, ih]
  | pred k ih => rw [← ih, ← h1 (-(k : ℤ) - 1)]; ring_nf

/-- The `n`-periodic extension of `(a_k(x))_{k ∈ ℕ}` to `ℤ`: `i ↦ a_{i mod n}(x)`. -/
noncomputable def aPer {A : Type*} [CommRing A] (n : ℕ) (x : A) (i : ℤ) : ℕ :=
  a (i % (n : ℤ)).toNat x

/-- `aPer n x` is `n`-periodic. -/
theorem aPer_periodic {A : Type*} [CommRing A] (n : ℕ) (x : A) :
    Function.Periodic (aPer n x) n := by
  intro i
  simp [aPer]

/-- On an `n`-cycle, `aPer n x` extends `(a_k(x))_{k ∈ ℕ}`. -/
theorem aPer_natCast {A : Type*} [CommRing A] [IsZ2Ring A] {x : A} {n : ℕ} (hx : T^[n] x = x)
    (k : ℕ) : aPer n x k = a k x := by
  have hper : Function.Periodic (fun k => a k x) n :=
    (periodic_a_iff_periodic_T x n).2 (fun k => by rw [Function.iterate_add_apply, hx])
  simp only [aPer]
  rw [← Int.natCast_mod, Int.toNat_natCast]
  exact hper.map_mod_nat k

/-! ### `prop:have_gcd_n__l_k` -/

/-- The `l`-th sum of `prop:have_gcd_n__l_k` (`syracuse.tex:173`), literally:
`∑_{k=0}^{n−1} 3ᵏ 2^{P − ∑_{i=l−k}^{l} α_i}`, with `P = p_n(x)` and `α_i = a_i(x)`. -/
noncomputable def gcdSum (n P : ℕ) (α : ℤ → ℕ) (l : ℤ) : ℕ :=
  ∑ k ∈ range n, 3 ^ k * 2 ^ (P - ∑ i ∈ Icc (l - k) l, α i)

/-- The `l`-th sum is the OQ-43 sum `A'^n_{l+1}`: the exponent `P − ∑_{i=l−k}^{l} α_i` is the sum of
`α` over the other `n − 1 − k` terms of the period (no truncated subtraction). -/
theorem gcdSum_eq_AunAlt {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (l : ℤ) :
    gcdSum n (∑ t ∈ range n, α t) α l = AunAlt n (l + 1) α := by
  unfold gcdSum AunAlt
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  rw [Finset.prod_pow_eq_pow_sum]
  congr 2
  have hIcc : ∑ i ∈ Icc (l - k) l, α i = ∑ t ∈ range (k + 1), α (l - k + t) := by
    rw [show Icc (l - k) l = Ico (l - k) (l - k + ((k + 1 : ℕ) : ℤ)) by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; push_cast; omega]
    exact sum_Ico_int_eq_sum_range _ _ _
  have hsplit := sum_range_add_int α (l - k) (k + 1) (n - 1 - k)
  rw [show k + 1 + (n - 1 - k) = n by omega, sum_range_periodic h] at hsplit
  have hrest : ∑ t ∈ range (n - 1 - k), α (l - k + ((k + 1 : ℕ) : ℤ) + t) =
      ∑ t ∈ range (n - 1 - k), α (l + 1 + t) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    push_cast; ring_nf
  rw [hIcc, hsplit, hrest, Nat.add_sub_cancel_left]

/-- **The display of l.178, in the convention of l.62** (`α_k = a_k(x)`): on an `n`-cycle of any
commutative ring, the `l`-th sum is `(2^{p_n(x)} − 3ⁿ) T^{l+1}(x)`, for every `l ∈ ℕ`. -/
theorem gcdSum_cycle {A : Type*} [CommRing A] {x : A} {n : ℕ} (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (l : ℕ) :
    (gcdSum n (p n x) α l : A) = (2 ^ p n x - 3 ^ n) * T^[l + 1] x := by
  have hP : p n x = ∑ t ∈ range n, α t := by
    simp only [p, hα]
  have h1 := gcdSum_eq_AunAlt hper (l : ℤ)
  rw [← hP, show (l : ℤ) + 1 = ((l + 1 : ℕ) : ℤ) by push_cast; ring] at h1
  rw [h1, (Aun_cast_of_cycle hx α hα (l + 1)).2]

/-- **The Bézout step of l.186, as printed**, in the convention of l.62:
`3 S_0 − 2^{a_1(x)} S_1 = 3ⁿ − 2^{p_n(x)}`, with `a_1(x) = ν₂(3T(x)+1)`. -/
theorem gcd_bezout {A : Type*} [CommRing A] {x : A} {n : ℕ} (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    3 * (gcdSum n (p n x) α 0 : A) - 2 ^ a 1 x * gcdSum n (p n x) α 1 = 3 ^ n - 2 ^ p n x := by
  have h0 := gcdSum_cycle hx hper hα 0
  have h1 := gcdSum_cycle hx hper hα 1
  simp only [Nat.cast_zero, Nat.cast_one] at h0 h1
  have hs := two_pow_a_mul_T_iterate_succ x 1
  rw [h0, h1]
  linear_combination (-(2 ^ p n x - 3 ^ n : A)) * hs

/-- **Finding 2.** In the convention of l.62 the display of l.178 as printed (`T^l(x)`) fails at
`l = 0` on every cycle that is not a fixed point. -/
theorem gcdSum_ne_display {A : Type*} [CommRing A] [IsZ2Ring A] {x : A} {n : ℕ} (hn : 0 < n)
    (hx : T^[n] x = x) {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x)
    (hT : T x ≠ x) : (gcdSum n (p n x) α 0 : A) ≠ (2 ^ p n x - 3 ^ n) * T^[0] x := by
  have h0 := gcdSum_cycle hx hper hα 0
  simp only [Nat.cast_zero] at h0
  rw [h0, Function.iterate_zero, id, zero_add, Function.iterate_one]
  intro h
  exact hT (mul_left_cancel₀ (two_pow_p_sub_three_pow_ne_zero hn hx) h)

/-- `(2^{p_n(x)} − 3ⁿ) x > 0` on every cycle of `ℤ`: `2^{p_n(x)} − 3ⁿ` has the sign of `x`. -/
theorem two_pow_p_sub_three_pow_mul_pos {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    0 < ((2 : ℤ) ^ p n x - 3 ^ n) * x := by
  have h := base x n
  rw [hx] at h
  have e : ((2 : ℤ) ^ p n x - 3 ^ n) * x = ∑ k ∈ range n, (2 : ℤ) ^ p k x * 3 ^ (n - 1 - k) := by
    linear_combination h
  rw [e]
  exact Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.2 hn⟩

/-- The GCD of `n` consecutive points of an `n`-cycle of `ℤ`, each times `2^{p_n(x)} − 3ⁿ`, is
`|2^{p_n(x)} − 3ⁿ|`: `2^{p_n(x)} − 3ⁿ` divides every `f l`, and the Bézout step of l.186,
`3y − 2^{a_c(x)} T(y) = −1` at `y = T^c(x)`, makes the GCD divide it. -/
theorem gcd_eq_abs_of_cycle {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (c : ℕ)
    (f : ℕ → ℤ) (hf : ∀ l : ℕ, f l = ((2 : ℤ) ^ p n x - 3 ^ n) * T^[l + c] x) :
    (range n).gcd f = |(2 : ℤ) ^ p n x - 3 ^ n| := by
  set D : ℤ := 2 ^ p n x - 3 ^ n with hD
  set G := (range n).gcd f with hGdef
  have hG0 : 0 ≤ G := Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  have hDG : D ∣ G := Finset.dvd_gcd (fun l _ => by rw [hf]; exact dvd_mul_right _ _)
  have hGS : ∀ l : ℕ, G ∣ D * T^[l + c] x := by
    intro l
    have hmem : l % n ∈ range n := Finset.mem_range.2 (Nat.mod_lt _ hn)
    have h1 : G ∣ f (l % n) := Finset.gcd_dvd hmem
    rw [hf] at h1
    have hq : T^[n * (l / n)] x = x := by
      rw [Function.iterate_mul]; exact Function.iterate_fixed hx _
    have hT : T^[l + c] x = T^[l % n + c] x := by
      have e : l + c = (l % n + c) + n * (l / n) := by have := Nat.mod_add_div l n; omega
      rw [e, Function.iterate_add_apply, hq]
    rwa [← hT] at h1
  have hGD : G ∣ D := by
    have h0 := hGS 0
    have h1 := hGS 1
    have hs := two_pow_a_mul_T_iterate_succ x c
    have h2 : G ∣ 3 * (D * T^[0 + c] x) - 2 ^ a c x * (D * T^[1 + c] x) :=
      dvd_sub (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h1 _)
    have heq : 3 * (D * T^[0 + c] x) - 2 ^ a c x * (D * T^[1 + c] x) = -D := by
      rw [zero_add, add_comm 1 c]
      linear_combination (-D) * hs
    rw [heq] at h2
    exact (dvd_neg).1 h2
  exact Int.dvd_antisymm hG0 (abs_nonneg D) ((dvd_abs _ _).2 hGD) ((abs_dvd _ _).2 hDG)

/-- `prop:have_gcd_n__l_k`, true form: on every cycle of `ℤ`, the GCD of the `n` sums is
`|2^{p_n(x)} − 3ⁿ|`. -/
theorem have_gcd {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    (range n).gcd (fun l : ℕ => (gcdSum n (p n x) α l : ℤ)) = |(2 : ℤ) ^ p n x - 3 ^ n| :=
  gcd_eq_abs_of_cycle hn hx 1 _ (gcdSum_cycle hx hper hα)

/-- `prop:have_gcd_n__l_k` as printed, for `x > 0`. -/
theorem have_gcd_of_pos {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    (2 : ℤ) ^ p n x - 3 ^ n = (range n).gcd (fun l : ℕ => (gcdSum n (p n x) α l : ℤ)) := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  rw [have_gcd hn hx hper hα, abs_of_pos (pos_of_mul_pos_left hpos hx0.le)]

/-- For `x < 0` the GCD is `3ⁿ − 2^{p_n(x)}`, the opposite of the printed value. -/
theorem have_gcd_of_neg {x : ℤ} (hx0 : x < 0) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    (range n).gcd (fun l : ℕ => (gcdSum n (p n x) α l : ℤ)) = 3 ^ n - 2 ^ p n x := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  have hneg : (2 : ℤ) ^ p n x - 3 ^ n < 0 := by nlinarith
  rw [have_gcd hn hx hper hα, abs_of_neg hneg]
  ring

/-- `prop:have_gcd_n__l_k` read up to sign: `2^{p_n(x)} − 3ⁿ` is a GCD of the `n` sums. -/
theorem have_gcd_associated {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) :
    Associated ((2 : ℤ) ^ p n x - 3 ^ n)
      ((range n).gcd (fun l : ℕ => (gcdSum n (p n x) α l : ℤ))) := by
  rw [have_gcd hn hx hper hα]
  rcases abs_choice ((2 : ℤ) ^ p n x - 3 ^ n) with h | h
  · rw [h]
  · rw [h]; exact Associated.neg_right (Associated.refl _)

/-! The index convention of the proof of `lem:base` (l.71: `a_1(x) = p_1(x) = ν₂(3x+1)`) is
`β_{k+1} = a_k(x)`. In it the display of l.178 holds as printed, and so does the Bézout step. -/

/-- **The display of l.178, as printed**, in the convention of l.71 (`β_{k+1} = a_k(x)`): the `l`-th
sum is `(2^{p_n(x)} − 3ⁿ) T^l(x)`, for every `l ∈ ℕ`, in every commutative ring. -/
theorem gcdSum_cycle_shift {A : Type*} [CommRing A] {x : A} {n : ℕ} (hx : T^[n] x = x)
    {β : ℤ → ℕ} (hper : Function.Periodic β n) (hβ : ∀ k : ℕ, β ((k : ℤ) + 1) = a k x) (l : ℕ) :
    (gcdSum n (p n x) β l : A) = (2 ^ p n x - 3 ^ n) * T^[l] x := by
  have hα : ∀ k : ℕ, (fun i : ℤ => β (i + 1)) k = a k x := hβ
  have hP : p n x = ∑ t ∈ range n, β t := by
    rw [← sum_range_periodic hper 1]
    simp only [p]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [add_comm (1 : ℤ)]
    exact (hβ t).symm
  have h1 := gcdSum_eq_AunAlt hper (l : ℤ)
  rw [← hP] at h1
  have h2 : AunAlt n ((l : ℤ) + 1) β = AunAlt n ((l : ℕ) : ℤ) (fun i : ℤ => β (i + 1)) := by
    unfold AunAlt
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 2
    ring
  rw [h1, h2, (Aun_cast_of_cycle hx _ hα l).2]

/-- **The Bézout step of l.186, as printed**, in the convention of l.71: `β_1 = a_0(x) = ν₂(3x+1)`. -/
theorem gcd_bezout_shift {A : Type*} [CommRing A] {x : A} {n : ℕ} (hx : T^[n] x = x)
    {β : ℤ → ℕ} (hper : Function.Periodic β n) (hβ : ∀ k : ℕ, β ((k : ℤ) + 1) = a k x) :
    3 * (gcdSum n (p n x) β 0 : A) - 2 ^ β 1 * gcdSum n (p n x) β 1 = 3 ^ n - 2 ^ p n x := by
  have h0 := gcdSum_cycle_shift hx hper hβ 0
  have h1 := gcdSum_cycle_shift hx hper hβ 1
  simp only [Nat.cast_zero, Nat.cast_one] at h0 h1
  have hb : β 1 = a 0 x := by simpa using hβ 0
  have hs := two_pow_a_mul_T_iterate_succ x 0
  simp only [zero_add, Function.iterate_zero, id, Function.iterate_one] at hs
  rw [h0, h1, hb, Function.iterate_zero, id, Function.iterate_one]
  linear_combination (-(2 ^ p n x - 3 ^ n : A)) * hs

/-- `prop:have_gcd_n__l_k`, true form, in the convention of l.71: the GCD is `|2^{p_n(x)} − 3ⁿ|`. -/
theorem have_gcd_shift {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {β : ℤ → ℕ}
    (hper : Function.Periodic β n) (hβ : ∀ k : ℕ, β ((k : ℤ) + 1) = a k x) :
    (range n).gcd (fun l : ℕ => (gcdSum n (p n x) β l : ℤ)) = |(2 : ℤ) ^ p n x - 3 ^ n| :=
  gcd_eq_abs_of_cycle hn hx 0 _ (fun l => by rw [add_zero]; exact gcdSum_cycle_shift hx hper hβ l)

/-- **Finding 1.** `prop:have_gcd_n__l_k` as printed is false: the cycle `(−1)`, `n = 1`. -/
theorem have_gcd_printed_false :
    ¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) →
      (2 : ℤ) ^ p n x - 3 ^ n = (range n).gcd (fun l : ℕ => (gcdSum n (p n x) α l : ℤ)) := by
  intro h
  have h1 := h (-1) 1 one_pos (T_iterate_neg_one_int 1) (fun _ => 1) (fun _ => rfl)
    (fun k => (a_neg_one_int k).symm)
  have hG0 : 0 ≤ (range 1).gcd (fun l : ℕ => (gcdSum 1 (p 1 (-1 : ℤ)) (fun _ => 1) l : ℤ)) :=
    Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  rw [← h1, p_neg_one_int] at hG0
  norm_num at hG0

/-- **Finding 1**, in the convention of l.71: the same cycle `(−1)` refutes it. -/
theorem have_gcd_printed_false_shift :
    ¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ β : ℤ → ℕ, Function.Periodic β n →
      (∀ k : ℕ, β ((k : ℤ) + 1) = a k x) →
      (2 : ℤ) ^ p n x - 3 ^ n = (range n).gcd (fun l : ℕ => (gcdSum n (p n x) β l : ℤ)) := by
  intro h
  have h1 := h (-1) 1 one_pos (T_iterate_neg_one_int 1) (fun _ => 1) (fun _ => rfl)
    (fun k => (a_neg_one_int k).symm)
  have hG0 : 0 ≤ (range 1).gcd (fun l : ℕ => (gcdSum 1 (p 1 (-1 : ℤ)) (fun _ => 1) l : ℤ)) :=
    Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  rw [← h1, p_neg_one_int] at hG0
  norm_num at hG0

/-- **Finding 2.** In the convention of l.62 the display of l.178 as printed is false: the cycle
`(−5, −7)`, `l = 0`. -/
theorem gcd_display_printed_false :
    ¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → ∀ α : ℤ → ℕ, Function.Periodic α n →
      (∀ k : ℕ, α k = a k x) → ∀ l : ℕ, l ≤ n - 1 →
      (gcdSum n (p n x) α l : ℤ) = (2 ^ p n x - 3 ^ n) * T^[l] x := by
  intro h
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have hT : T (-5 : ℤ) ≠ -5 := cycle_neg_five.2
  have h1 := h (-5) 2 two_pos hx (aPer 2 (-5)) (aPer_periodic 2 (-5)) (aPer_natCast hx) 0
    (by norm_num)
  simp only [Nat.cast_zero] at h1
  exact gcdSum_ne_display two_pos hx (aPer_periodic 2 (-5)) (aPer_natCast hx) hT h1

/-! ### `lem:periodic_exists_i_a_i_`: general lemmas -/

/-- `A_u^n = ∑_{k<n} 3ᵏ 2^{∑_{t<n−k} a_{u+t}}`. -/
theorem Aun_eq_sum (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    Aun n u α = ∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (n - k), α (u + t)) := by
  simp only [Aun, Finset.prod_pow_eq_pow_sum]

/-- `A'^n_u = ∑_{k<n} 3ᵏ 2^{∑_{t<n−1−k} a_{u+t}}`. -/
theorem AunAlt_eq_sum (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    AunAlt n u α = ∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (n - 1 - k), α (u + t)) := by
  simp only [AunAlt, Finset.prod_pow_eq_pow_sum]

/-- The two readings of OQ-43: `A_u^n = 3 A'^n_u + 2^{∑_{t<n} a_{u+t}} − 3ⁿ`, for every `a`, `n`, `u`. -/
theorem Aun_eq_three_mul_AunAlt (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    (Aun n u α : ℤ) = 3 * AunAlt n u α + 2 ^ (∑ t ∈ range n, α (u + t)) - 3 ^ n := by
  have key : Aun n u α + 3 ^ n = 3 * AunAlt n u α + 2 ^ (∑ t ∈ range n, α (u + t)) := by
    rcases n with _ | m
    · simp [Aun, AunAlt]
    · rw [Aun_eq_sum, AunAlt_eq_sum, Finset.sum_range_succ', Finset.sum_range_succ,
        mul_add, Finset.mul_sum]
      have hc : ∀ k ∈ range m, 3 ^ (k + 1) * 2 ^ (∑ t ∈ range (m + 1 - (k + 1)), α (u + t)) =
          3 * (3 ^ k * 2 ^ (∑ t ∈ range (m + 1 - 1 - k), α (u + t))) := by
        intro k _
        rw [show m + 1 - (k + 1) = m + 1 - 1 - k by omega]
        ring
      rw [Finset.sum_congr rfl hc, show m + 1 - 1 - m = 0 by omega]
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, Nat.sub_zero, one_mul]
      ring
  have := congrArg (fun z : ℕ => (z : ℤ)) key
  push_cast at this
  linear_combination this

/-- For `n`-periodic `a`, `A_u^n − A_v^n = 3 (A'^n_u − A'^n_v)`. -/
theorem Aun_sub_eq_three_mul {α : ℤ → ℕ} {n : ℕ} (h : Function.Periodic α n) (u v : ℤ) :
    (Aun n u α : ℤ) - Aun n v α = 3 * ((AunAlt n u α : ℤ) - AunAlt n v α) := by
  rw [Aun_eq_three_mul_AunAlt, Aun_eq_three_mul_AunAlt, sum_range_periodic h u,
    sum_range_periodic h v]
  ring

/-- The 2-adic bound for any sum `∑_{k<n} 3ᵏ 2^{∑_{t<m_k} a_{u+t}}`. -/
theorem two_pow_dvd_sum_sub {α : ℤ → ℕ} {u v : ℤ} {q : ℕ}
    (h : ∀ t : ℕ, t < q → α (u + t) = α (v + t)) (n : ℕ) (m : ℕ → ℕ) :
    (2 : ℤ) ^ (∑ t ∈ range q, α (u + t) + min (α (u + q)) (α (v + q))) ∣
      ((∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (m k), α (u + t)) : ℕ) : ℤ) -
        ((∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (m k), α (v + t)) : ℕ) : ℤ) := by
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum (fun k _ => ?_)
  rw [← mul_sub]
  refine dvd_mul_of_dvd_right ?_ _
  have hq : ∑ t ∈ range q, α (u + t) = ∑ t ∈ range q, α (v + t) :=
    Finset.sum_congr rfl (fun t ht => h t (Finset.mem_range.1 ht))
  by_cases hk : m k ≤ q
  · have : ∑ t ∈ range (m k), α (u + t) = ∑ t ∈ range (m k), α (v + t) :=
      Finset.sum_congr rfl (fun t ht => h t (by have := Finset.mem_range.1 ht; omega))
    rw [this, sub_self]
    exact dvd_zero _
  · have hsu : ∑ t ∈ range q, α (u + t) + α (u + q) ≤ ∑ t ∈ range (m k), α (u + t) := by
      rw [← Finset.sum_range_succ (fun t : ℕ => α (u + t)) q]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    have hsv : ∑ t ∈ range q, α (u + t) + α (v + q) ≤ ∑ t ∈ range (m k), α (v + t) := by
      rw [hq, ← Finset.sum_range_succ (fun t : ℕ => α (v + t)) q]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    exact dvd_sub (pow_dvd_pow 2 (le_trans (by omega) hsu))
      (pow_dvd_pow 2 (le_trans (by omega) hsv))

/-- **The 2-adic bound, printed `A_u^n`**: if `a_{u+t} = a_{v+t}` for `t < q`, then
`2^{∑_{t<q} a_{u+t} + min(a_{u+q}, a_{v+q})}` divides `A_u^n − A_v^n`. No periodicity. -/
theorem two_pow_dvd_Aun_sub {α : ℤ → ℕ} {u v : ℤ} {q : ℕ}
    (h : ∀ t : ℕ, t < q → α (u + t) = α (v + t)) (n : ℕ) :
    (2 : ℤ) ^ (∑ t ∈ range q, α (u + t) + min (α (u + q)) (α (v + q))) ∣
      (Aun n u α : ℤ) - Aun n v α := by
  rw [Aun_eq_sum, Aun_eq_sum]
  exact two_pow_dvd_sum_sub h n (fun k => n - k)

/-- The 2-adic bound for the OQ-43 reading. -/
theorem two_pow_dvd_AunAlt_sub {α : ℤ → ℕ} {u v : ℤ} {q : ℕ}
    (h : ∀ t : ℕ, t < q → α (u + t) = α (v + t)) (n : ℕ) :
    (2 : ℤ) ^ (∑ t ∈ range q, α (u + t) + min (α (u + q)) (α (v + q))) ∣
      (AunAlt n u α : ℤ) - AunAlt n v α := by
  rw [AunAlt_eq_sum, AunAlt_eq_sum]
  exact two_pow_dvd_sum_sub h n (fun k => n - 1 - k)

/-- The 3-adic bound for any sum `∑_{k<n} 3ᵏ 2^{∑_{t<m_k} a_{u+t}}`: the terms `k < p` cancel. -/
theorem three_pow_dvd_sum_sub {α : ℤ → ℕ} {u v : ℤ} {p : ℕ} (n : ℕ) (m : ℕ → ℕ)
    (h : ∀ k, k < n → k < p → ∑ t ∈ range (m k), α (u + t) = ∑ t ∈ range (m k), α (v + t)) :
    (3 : ℤ) ^ p ∣ ((∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (m k), α (u + t)) : ℕ) : ℤ) -
        ((∑ k ∈ range n, 3 ^ k * 2 ^ (∑ t ∈ range (m k), α (v + t)) : ℕ) : ℤ) := by
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum (fun k hk => ?_)
  rw [← mul_sub]
  by_cases hkp : k < p
  · rw [h k (Finset.mem_range.1 hk) hkp, sub_self, mul_zero]
    exact dvd_zero _
  · exact dvd_mul_of_dvd_left (pow_dvd_pow 3 (by omega)) _

/-- **The 3-adic bound, printed `A_u^n`**: for `n`-periodic `a`, if the `p − 1` terms before `u` and
before `v` agree, `a_{u−r} = a_{v−r}` for `r ∈ ⟦1, p−1⟧`, then `3^p ∣ A_u^n − A_v^n`. -/
theorem three_pow_dvd_Aun_sub {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {u v : ℤ}
    {p : ℕ} (h : ∀ r : ℕ, 1 ≤ r → r < p → α (u - r) = α (v - r)) :
    (3 : ℤ) ^ p ∣ (Aun n u α : ℤ) - Aun n v α := by
  rw [Aun_eq_sum, Aun_eq_sum]
  refine three_pow_dvd_sum_sub n (fun k => n - k) (fun k hkn hkp => ?_)
  have hw : ∀ w : ℤ, ∑ t ∈ range n, α t =
      ∑ t ∈ range k, α (w - k + t) + ∑ t ∈ range (n - k), α (w + t) := by
    intro w
    have e := sum_range_add_int α (w - k) k (n - k)
    rw [show k + (n - k) = n by omega, sum_range_periodic hper] at e
    rw [e]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1; ring
  have hpre : ∑ t ∈ range k, α (u - k + t) = ∑ t ∈ range k, α (v - k + t) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht' := Finset.mem_range.1 ht
    have := h (k - t) (by omega) (by omega)
    rw [show u - (k : ℤ) + t = u - ((k - t : ℕ) : ℤ) by push_cast [Nat.cast_sub ht'.le]; ring,
      show v - (k : ℤ) + t = v - ((k - t : ℕ) : ℤ) by push_cast [Nat.cast_sub ht'.le]; ring]
    exact this
  have hu := hw u
  have hv := hw v
  show ∑ t ∈ range (n - k), α (u + t) = ∑ t ∈ range (n - k), α (v + t)
  omega

/-- The 3-adic bound for the OQ-43 reading needs the `p` terms before `u` and `v`. -/
theorem three_pow_dvd_AunAlt_sub {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {u v : ℤ}
    {p : ℕ} (h : ∀ r : ℕ, 1 ≤ r → r ≤ p → α (u - r) = α (v - r)) :
    (3 : ℤ) ^ p ∣ (AunAlt n u α : ℤ) - AunAlt n v α := by
  have h3 : (3 : ℤ) ^ (p + 1) ∣ (Aun n u α : ℤ) - Aun n v α :=
    three_pow_dvd_Aun_sub hper (fun r hr1 hr2 => h r hr1 (by omega))
  rw [Aun_sub_eq_three_mul hper, pow_succ', ] at h3
  exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).1 h3

/-- `A_u^n = RHS_n(q)` with `q_k = ∑_{t≤k} a_{u+t}` (`lem:ring_maps_rhs_n_`, `Syracuse.RHS`). -/
theorem Aun_cast_eq_RHS (n : ℕ) (u : ℤ) (α : ℤ → ℕ) :
    (Aun n u α : ℤ) = RHS ℤ n (fun k : Fin n => ∑ t ∈ range ((k : ℕ) + 1), α (u + t)) := by
  rw [Aun_eq_sum, RHS, Fin.sum_univ_eq_sum_range
    (fun k => (2 : ℤ) ^ (∑ t ∈ range (k + 1), α (u + t)) * 3 ^ (n - 1 - k)) n]
  push_cast
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have := Finset.mem_range.1 hk
  rw [show n - 1 - k + 1 = n - k by omega, show n - 1 - (n - 1 - k) = k by omega]
  ring

/-- `A_u^n = A_v^n` (with `a ≥ 1`) forces `a_{u+t} = a_{v+t}` for `t < n`: `lem:ring_maps_rhs_n_`. -/
theorem agree_of_Aun_eq {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ} {u v : ℤ}
    (h : (Aun n u α : ℤ) = Aun n v α) : ∀ t : ℕ, t < n → α (u + t) = α (v + t) := by
  have hmono : ∀ w : ℤ, StrictMono (fun k : Fin n => ∑ t ∈ range ((k : ℕ) + 1), α (w + t)) := by
    intro w
    have hm : StrictMono (fun k : ℕ => ∑ t ∈ range (k + 1), α (w + t)) := by
      refine strictMono_nat_of_lt_succ (fun k => ?_)
      rw [Finset.sum_range_succ _ (k + 1)]
      have := hpos (w + ((k + 1 : ℕ) : ℤ))
      omega
    exact hm.comp Fin.val_strictMono
  have hq := rhs_injOn_strictMono (A := ℤ) two_ne_zero (by decide) n (hmono u) (hmono v)
    (by rw [← Aun_cast_eq_RHS, ← Aun_cast_eq_RHS]; exact h)
  have hS : ∀ k, k ≤ n → ∑ t ∈ range k, α (u + t) = ∑ t ∈ range k, α (v + t) := by
    intro k hk
    rcases k with _ | j
    · simp
    · exact congrFun hq ⟨j, by omega⟩
  intro t ht
  have h1 := hS (t + 1) ht
  have h0 := hS t ht.le
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h1
  omega

/-- An `n`-periodic `a` with `a_{u+t} = a_{v+t}` for `t < n` has period `v − u`. -/
theorem periodic_sub_of_agree {α : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (hper : Function.Periodic α n)
    {u v : ℤ} (h : ∀ t : ℕ, t < n → α (u + t) = α (v + t)) : Function.Periodic α (v - u) := by
  intro y
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = (y - u) % (n : ℤ) :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')⟩
  have hrn : r < n := by have := Int.emod_lt_of_pos (y - u) hn'; omega
  have hdiv := Int.emod_add_mul_ediv (y - u) (n : ℤ)
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = (y - u) / (n : ℤ) := ⟨_, rfl⟩
  have hP := hper.int_mul q
  simp only [Int.cast_id] at hP
  have e1 : y = u + r + q * n := by rw [hr, hq]; linarith
  have e2 : y + (v - u) = v + r + q * n := by rw [hr, hq]; linarith
  rw [e2, hP, e1, hP]
  exact (h r hrn).symm

/-- **`A_i − A_j ≠ 0`, printed `A_u^n`**, for `a ≥ 1` of minimal period `n`, `i ≠ j` in `⟦0, n−1⟧`. -/
theorem Aun_sub_ne_zero_of_minimal {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ}
    (hper : Function.Periodic α n) (hmin : ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m)
    {i j : ℤ} (hi : 0 ≤ i) (hin : i ≤ n - 1) (hj : 0 ≤ j) (hjn : j ≤ n - 1) (hij : i ≠ j) :
    (Aun n i α : ℤ) - Aun n j α ≠ 0 := by
  intro h0
  have hn : 0 < n := by omega
  have hP := periodic_sub_of_agree hn hper (agree_of_Aun_eq hpos (sub_eq_zero.1 h0))
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply hmin (j - i).toNat (by omega) (by omega)
    rw [show (((j - i).toNat : ℕ) : ℤ) = j - i by omega]
    exact hP
  · apply hmin (i - j).toNat (by omega) (by omega)
    rw [show (((i - j).toNat : ℕ) : ℤ) = -(j - i) by omega]
    exact hP.neg

/-- `A'_i − A'_j ≠ 0` for the OQ-43 reading, under the same hypotheses. -/
theorem AunAlt_sub_ne_zero_of_minimal {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ}
    (hper : Function.Periodic α n) (hmin : ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m)
    {i j : ℤ} (hi : 0 ≤ i) (hin : i ≤ n - 1) (hj : 0 ≤ j) (hjn : j ≤ n - 1) (hij : i ≠ j) :
    (AunAlt n i α : ℤ) - AunAlt n j α ≠ 0 := by
  intro h0
  apply Aun_sub_ne_zero_of_minimal hpos hper hmin hi hin hj hjn hij
  rw [Aun_sub_eq_three_mul hper, h0, mul_zero]

/-! ### `lem:periodic_exists_i_a_i_`: the printed conjuncts, the corrected forms, the refutations -/

/-- **The `ν₃` conjunct of `lem:periodic_exists_i_a_i_`, as printed** (printed `A_u^n`):
`ν₃(A_{p+i} − A_{p+j}) ≥ p`. -/
theorem periodic_exists_nu3 {n p : ℕ} (_hn : 0 < n) (_hp : 0 < p) (_hpn : p < n) {α : ℤ → ℕ}
    (_hpos : ∀ k, 1 ≤ α k) (hper : Function.Periodic α n) {i j : ℤ} (_hi : 0 ≤ i)
    (_hin : i ≤ n - 1) (_hj : 0 ≤ j) (_hjn : j ≤ n - 1) (_hij : i ≠ j)
    (hagree : ∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) :
    (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((Aun n (p + i) α : ℤ) - Aun n (p + j) α) := by
  rw [← pow_dvd_iff_le_emultiplicity]
  refine three_pow_dvd_Aun_sub hper (fun r hr1 hrp => ?_)
  have := hagree ((p : ℤ) - r) (by omega) (by omega)
  rw [show (p : ℤ) + i - r = i + (p - r) by ring, show (p : ℤ) + j - r = j + (p - r) by ring]
  exact this

/-- `∑_{k=1}^{p} a_{i+k} = ∑_{t<p} a_{i+1+t}`. -/
theorem sum_Icc_one_int (α : ℤ → ℕ) (i : ℤ) (p : ℕ) :
    ∑ k ∈ Icc (1 : ℤ) p, α (i + k) = ∑ t ∈ range p, α (i + 1 + t) := by
  rw [show Icc (1 : ℤ) p = Ico (1 : ℤ) (1 + p) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    sum_Ico_int_eq_sum_range]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1; ring

/-- `∑_{k=0}^{p−1} a_{i+k} = ∑_{t<p} a_{i+t}`. -/
theorem sum_Icc_zero_int (α : ℤ → ℕ) (i : ℤ) (p : ℕ) :
    ∑ k ∈ Icc (0 : ℤ) (p - 1), α (i + k) = ∑ t ∈ range p, α (i + t) := by
  rw [show Icc (0 : ℤ) (p - 1) = Ico (0 : ℤ) (0 + p) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    sum_Ico_int_eq_sum_range]
  simp

/-- **The `ν₂` conjunct, index-shifted** (printed hypotheses): `ν₂(A_{i+1} − A_{j+1}) ≥ ∑_{k=1}^p a_{i+k}`. -/
theorem periodic_exists_nu2_shift {p : ℕ} {α : ℤ → ℕ} {i j : ℤ}
    (hagree : ∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) (n : ℕ) :
    ((∑ k ∈ Icc (1 : ℤ) p, α (i + k) : ℕ) : ℕ∞) ≤ nu2 ((Aun n (i + 1) α : ℤ) - Aun n (j + 1) α) := by
  rw [nu2, ← pow_dvd_iff_le_emultiplicity, sum_Icc_one_int]
  have h : ∀ t : ℕ, t < p → α (i + 1 + t) = α (j + 1 + t) := by
    intro t ht
    have := hagree (1 + t) (by omega) (by omega)
    rw [show i + 1 + t = i + (1 + t) by ring, show j + 1 + t = j + (1 + t) by ring]
    exact this
  exact (pow_dvd_pow 2 (Nat.le_add_right _ _)).trans (two_pow_dvd_Aun_sub h n)

/-- The index-shifted `ν₂` conjunct for the OQ-43 reading. -/
theorem periodic_exists_nu2_shift_alt {p : ℕ} {α : ℤ → ℕ} {i j : ℤ}
    (hagree : ∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) (n : ℕ) :
    ((∑ k ∈ Icc (1 : ℤ) p, α (i + k) : ℕ) : ℕ∞) ≤
      nu2 ((AunAlt n (i + 1) α : ℤ) - AunAlt n (j + 1) α) := by
  rw [nu2, ← pow_dvd_iff_le_emultiplicity, sum_Icc_one_int]
  have h : ∀ t : ℕ, t < p → α (i + 1 + t) = α (j + 1 + t) := by
    intro t ht
    have := hagree (1 + t) (by omega) (by omega)
    rw [show i + 1 + t = i + (1 + t) by ring, show j + 1 + t = j + (1 + t) by ring]
    exact this
  exact (pow_dvd_pow 2 (Nat.le_add_right _ _)).trans (two_pow_dvd_AunAlt_sub h n)

/-- **`lem:periodic_exists_i_a_i_`, corrected** (printed `A_u^n`): agreement on `⟦0, p−1⟧`, `n` the
minimal period; all three conclusions, with the bound `∑_{k=0}^{p−1} a_{i+k}`. -/
theorem periodic_exists_corrected {n p : ℕ} (_hn : 0 < n) (_hp : 0 < p) (_hpn : p < n)
    {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) (hper : Function.Periodic α n)
    (hmin : ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) {i j : ℤ} (hi : 0 ≤ i)
    (hin : i ≤ n - 1) (hj : 0 ≤ j) (hjn : j ≤ n - 1) (hij : i ≠ j)
    (hagree : ∀ k : ℤ, 0 ≤ k → k ≤ p - 1 → α (i + k) = α (j + k)) :
    ((∑ k ∈ Icc (0 : ℤ) (p - 1), α (i + k) : ℕ) : ℕ∞) ≤ nu2 ((Aun n i α : ℤ) - Aun n j α) ∧
      (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((Aun n (p + i) α : ℤ) - Aun n (p + j) α) ∧
      (Aun n i α : ℤ) - Aun n j α ≠ 0 := by
  refine ⟨?_, ?_, Aun_sub_ne_zero_of_minimal hpos hper hmin hi hin hj hjn hij⟩
  · rw [nu2, ← pow_dvd_iff_le_emultiplicity, sum_Icc_zero_int]
    exact (pow_dvd_pow 2 (Nat.le_add_right _ _)).trans
      (two_pow_dvd_Aun_sub (fun t ht => hagree t (by omega) (by omega)) n)
  · rw [← pow_dvd_iff_le_emultiplicity]
    refine three_pow_dvd_Aun_sub hper (fun r hr1 hrp => ?_)
    have := hagree ((p : ℤ) - r) (by omega) (by omega)
    rw [show (p : ℤ) + i - r = i + (p - r) by ring, show (p : ℤ) + j - r = j + (p - r) by ring]
    exact this

/-- `lem:periodic_exists_i_a_i_`, corrected, for the OQ-43 reading. -/
theorem periodic_exists_corrected_alt {n p : ℕ} (_hn : 0 < n) (_hp : 0 < p) (_hpn : p < n)
    {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) (hper : Function.Periodic α n)
    (hmin : ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) {i j : ℤ} (hi : 0 ≤ i)
    (hin : i ≤ n - 1) (hj : 0 ≤ j) (hjn : j ≤ n - 1) (hij : i ≠ j)
    (hagree : ∀ k : ℤ, 0 ≤ k → k ≤ p - 1 → α (i + k) = α (j + k)) :
    ((∑ k ∈ Icc (0 : ℤ) (p - 1), α (i + k) : ℕ) : ℕ∞) ≤
        nu2 ((AunAlt n i α : ℤ) - AunAlt n j α) ∧
      (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((AunAlt n (p + i) α : ℤ) - AunAlt n (p + j) α) ∧
      (AunAlt n i α : ℤ) - AunAlt n j α ≠ 0 := by
  refine ⟨?_, ?_, AunAlt_sub_ne_zero_of_minimal hpos hper hmin hi hin hj hjn hij⟩
  · rw [nu2, ← pow_dvd_iff_le_emultiplicity, sum_Icc_zero_int]
    exact (pow_dvd_pow 2 (Nat.le_add_right _ _)).trans
      (two_pow_dvd_AunAlt_sub (fun t ht => hagree t (by omega) (by omega)) n)
  · rw [← pow_dvd_iff_le_emultiplicity]
    refine three_pow_dvd_AunAlt_sub hper (fun r hr1 hrp => ?_)
    have := hagree ((p : ℤ) - r) (by omega) (by omega)
    rw [show (p : ℤ) + i - r = i + (p - r) by ring, show (p : ℤ) + j - r = j + (p - r) by ring]
    exact this

/-- **Finding 3.** `lem:periodic_exists_i_a_i_` as printed (printed `A_u^n`) is false:
`a ≡ 1`, `n = 2`, `p = 1`, `i = 0`, `j = 1`, where `A_0 = A_1`. -/
theorem periodic_exists_printed_false :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α k : ℕ) : ℕ∞) ≤ nu2 ((Aun n i α : ℤ) - Aun n j α) ∧
      (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((Aun n (p + i) α : ℤ) - Aun n (p + j) α) ∧
      (Aun n i α : ℤ) - Aun n j α ≠ 0 := by
  intro h
  have := (h 2 1 (fun _ => 1) (by norm_num) (by norm_num) (by norm_num) (fun _ => le_rfl)
    (fun _ => rfl) 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num)
    (fun _ _ _ => rfl)).2.2
  exact this (by simp [Aun])

/-- **Finding 3**, for the OQ-43 reading. -/
theorem periodic_exists_printed_false_alt :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α k : ℕ) : ℕ∞) ≤ nu2 ((AunAlt n i α : ℤ) - AunAlt n j α) ∧
      (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((AunAlt n (p + i) α : ℤ) - AunAlt n (p + j) α) ∧
      (AunAlt n i α : ℤ) - AunAlt n j α ≠ 0 := by
  intro h
  have := (h 2 1 (fun _ => 1) (by norm_num) (by norm_num) (by norm_num) (fun _ => le_rfl)
    (fun _ => rfl) 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num)
    (fun _ _ _ => rfl)).2.2
  exact this (by simp [AunAlt])

/-- The `3`-periodic sequence `(1, 2, 2)` on `ℤ`, of minimal period `3`. -/
def seq122 (i : ℤ) : ℕ := if i % 3 = 0 then 1 else 2

theorem seq122_periodic : Function.Periodic seq122 (3 : ℕ) := by
  intro i
  simp [seq122]

theorem seq122_minimal : ∀ m : ℕ, 0 < m → m < 3 → ¬ Function.Periodic seq122 m := by
  intro m hm hm3 hP
  have h0 := hP 0
  interval_cases m <;> simp [seq122] at h0

/-- `(1, 2, 2)` is in `(ℕ*)^ℤ`. -/
theorem seq122_pos : ∀ k, 1 ≤ seq122 k := by
  intro k; unfold seq122; split_ifs <;> norm_num

/-- `a_{0+k} = a_{1+k}` for `k ∈ ⟦1, 1⟧`: the hypothesis of the lemma at `p = 1`, `i = 0`, `j = 1`. -/
theorem seq122_agree : ∀ k : ℤ, 1 ≤ k → k ≤ ((1 : ℕ) : ℤ) → seq122 (0 + k) = seq122 (1 + k) := by
  intro k hk1 hk2
  obtain rfl : k = 1 := by omega
  decide

/-- `A_0, A_1, A_2` of `(1, 2, 2)`, `n = 3`: `74, 116, 92`. -/
theorem Aun_seq122 : Aun 3 0 seq122 = 74 ∧ Aun 3 1 seq122 = 116 ∧ Aun 3 2 seq122 = 92 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `A'_0, A'_1, A'_2` of `(1, 2, 2)`, `n = 3`: `23, 37, 29`. -/
theorem AunAlt_seq122 : AunAlt 3 0 seq122 = 23 ∧ AunAlt 3 1 seq122 = 37 ∧ AunAlt 3 2 seq122 = 29 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Finding 4.** The `ν₂` conjunct as printed fails even for `a` of minimal period `n`: `(1, 2, 2)`,
`p = 1`, `i = 0`, `j = 1`, `ν₂(A_0 − A_1) = ν₂(−42) = 1 < 2`. With `i = 0` the bound `∑_{k=1}^p a_k`
is `∑_{k=1}^p a_{i+k}`: both readings fail. -/
theorem periodic_exists_nu2_printed_false :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → (∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) →
      ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α k : ℕ) : ℕ∞) ≤ nu2 ((Aun n i α : ℤ) - Aun n j α) := by
  intro h
  have h1 := h 3 1 seq122 (by norm_num) (by norm_num) (by norm_num) seq122_pos seq122_periodic
    seq122_minimal 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num) seq122_agree
  have hs : ∑ k ∈ Icc (1 : ℤ) ((1 : ℕ) : ℤ), seq122 k = 2 := by decide
  rw [hs, nu2, ← pow_dvd_iff_le_emultiplicity, Aun_seq122.1, Aun_seq122.2.1] at h1
  norm_num at h1

/-- **Finding 4**, for the OQ-43 reading: `ν₂(A'_0 − A'_1) = ν₂(−14) = 1 < 2`. -/
theorem periodic_exists_nu2_printed_false_alt :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → (∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) →
      ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α k : ℕ) : ℕ∞) ≤ nu2 ((AunAlt n i α : ℤ) - AunAlt n j α) := by
  intro h
  have h1 := h 3 1 seq122 (by norm_num) (by norm_num) (by norm_num) seq122_pos seq122_periodic
    seq122_minimal 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num) seq122_agree
  have hs : ∑ k ∈ Icc (1 : ℤ) ((1 : ℕ) : ℤ), seq122 k = 2 := by decide
  rw [hs, nu2, ← pow_dvd_iff_le_emultiplicity, AunAlt_seq122.1, AunAlt_seq122.2.1] at h1
  norm_num at h1

/-- **Finding 4**, with the bound read as `∑_{k=1}^p a_{i+k}`: the same witness. -/
theorem periodic_exists_nu2_shifted_bound_false :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → (∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) →
      ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α (i + k) : ℕ) : ℕ∞) ≤ nu2 ((Aun n i α : ℤ) - Aun n j α) := by
  intro h
  have h1 := h 3 1 seq122 (by norm_num) (by norm_num) (by norm_num) seq122_pos seq122_periodic
    seq122_minimal 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num) seq122_agree
  have hs : ∑ k ∈ Icc (1 : ℤ) ((1 : ℕ) : ℤ), seq122 (0 + k) = 2 := by decide
  rw [hs, nu2, ← pow_dvd_iff_le_emultiplicity, Aun_seq122.1, Aun_seq122.2.1] at h1
  norm_num at h1

/-- **Finding 4**, with the bound `∑_{k=1}^p a_{i+k}`, for the OQ-43 reading. -/
theorem periodic_exists_nu2_shifted_bound_false_alt :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → (∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) →
      ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      ((∑ k ∈ Icc (1 : ℤ) p, α (i + k) : ℕ) : ℕ∞) ≤ nu2 ((AunAlt n i α : ℤ) - AunAlt n j α) := by
  intro h
  have h1 := h 3 1 seq122 (by norm_num) (by norm_num) (by norm_num) seq122_pos seq122_periodic
    seq122_minimal 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num) seq122_agree
  have hs : ∑ k ∈ Icc (1 : ℤ) ((1 : ℕ) : ℤ), seq122 (0 + k) = 2 := by decide
  rw [hs, nu2, ← pow_dvd_iff_le_emultiplicity, AunAlt_seq122.1, AunAlt_seq122.2.1] at h1
  norm_num at h1

/-- **Finding 5.** The `ν₃` conjunct fails for the OQ-43 reading: `(1, 2, 2)`, `p = 1`, `i = 0`,
`j = 1`, `A'_1 − A'_2 = 37 − 29 = 8`. -/
theorem periodic_exists_nu3_printed_false_alt :
    ¬ ∀ (n p : ℕ) (α : ℤ → ℕ), 0 < n → 0 < p → p < n → (∀ k, 1 ≤ α k) →
      Function.Periodic α n → (∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m) →
      ∀ i j : ℤ, 0 ≤ i → i ≤ n - 1 → 0 ≤ j → j ≤ n - 1 → i ≠ j →
      (∀ k : ℤ, 1 ≤ k → k ≤ p → α (i + k) = α (j + k)) →
      (p : ℕ∞) ≤ emultiplicity (3 : ℤ) ((AunAlt n (p + i) α : ℤ) - AunAlt n (p + j) α) := by
  intro h
  have h1 := h 3 1 seq122 (by norm_num) (by norm_num) (by norm_num) seq122_pos seq122_periodic
    seq122_minimal 0 1 le_rfl (by norm_num) zero_le_one (by norm_num) (by norm_num) seq122_agree
  rw [← pow_dvd_iff_le_emultiplicity, show ((1 : ℕ) : ℤ) + 0 = 1 by norm_num,
    show ((1 : ℕ) : ℤ) + 1 = 2 by norm_num, AunAlt_seq122.2.1, AunAlt_seq122.2.2] at h1
  norm_num at h1

/-! ### `def:circuit` -/

/-- **ε-circuit** (`def:circuit`, `syracuse.tex:213`), reading "`(x)_{n∈ℕ}`" as the orbit
`(Tⁿ(x))_{n∈ℕ}`: it is `n`-periodic for some `n ∈ ℕ*`, and some term `y` of it has `a_i(y) = 1` for
every `i ∈ ⟦1, p⟧`, for some `p ≥ εn − 1`. -/
def IsCircuit (ε : ℝ) (x : ℤ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Function.IsPeriodicPt T n x ∧
    ∃ y ∈ Set.range (fun m : ℕ => T^[m] x), ∃ p : ℕ, ε * n - 1 ≤ p ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ p → a i y = 1

/-- The literal reading of `def:circuit`: the constant sequence `(x)_{n∈ℕ}`. -/
def IsCircuitLiteral (ε : ℝ) (x : ℤ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Function.Periodic (fun _ : ℕ => x) n ∧
    ∃ y ∈ Set.range (fun _ : ℕ => x), ∃ p : ℕ, ε * n - 1 ≤ p ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ p → a i y = 1

/-- **Finding 6.** Read literally, every integer is an `ε`-circuit for every `ε ≤ 1`. -/
theorem isCircuitLiteral_of_le_one {ε : ℝ} (hε : ε ≤ 1) (x : ℤ) : IsCircuitLiteral ε x :=
  ⟨1, one_pos, fun _ => rfl, x, ⟨0, rfl⟩, 0, by push_cast; linarith,
    fun i h1 h2 => absurd (h1.trans h2) (by norm_num)⟩

/-- `T(3) = 5`. -/
theorem T_three_int : T (3 : ℤ) = 5 :=
  (T_unique (A := ℤ) two_ne_zero (x := 3) (t := 5) (k := 1) ⟨2, by norm_num⟩ (by norm_num)).2

/-- `T(5) = 1`. -/
theorem T_five_int : T (5 : ℤ) = 1 :=
  (T_unique (A := ℤ) two_ne_zero (x := 5) (t := 1) (k := 4) odd_one (by norm_num)).2

/-- `3` (orbit `3, 5, 1, 1, …`) is not periodic, hence an `ε`-circuit for no `ε`. -/
theorem not_isCircuit_three (ε : ℝ) : ¬ IsCircuit ε 3 := by
  rintro ⟨n, hn, hx, -⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have hx' : T^[0 + m + 1] (3 : ℤ) = 3 := hx
  rw [zero_add, Function.iterate_succ_apply, T_three_int] at hx'
  rcases m with _ | m
  · simp at hx'
  · rw [Function.iterate_succ_apply, T_five_int, T_iterate_one_int] at hx'
    norm_num at hx'

/-- A smaller `ε` is weaker. -/
theorem IsCircuit.mono {ε ε' : ℝ} (hε : ε' ≤ ε) {x : ℤ} (h : IsCircuit ε x) : IsCircuit ε' x := by
  obtain ⟨n, hn, hx, y, hy, p, hp, ha⟩ := h
  refine ⟨n, hn, hx, y, hy, p, ?_, ha⟩
  have := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- For `ε ≥ 0`, the period of `def:circuit` may be taken to be the minimal period. -/
theorem isCircuit_iff_minimalPeriod {ε : ℝ} (hε : 0 ≤ ε) (x : ℤ) :
    IsCircuit ε x ↔ 0 < Function.minimalPeriod T x ∧
      ∃ y ∈ Set.range (fun m : ℕ => T^[m] x), ∃ p : ℕ, ε * Function.minimalPeriod T x - 1 ≤ p ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ p → a i y = 1 := by
  constructor
  · rintro ⟨n, hn, hx, y, hy, p, hp, ha⟩
    refine ⟨hx.minimalPeriod_pos hn, y, hy, p, ?_, ha⟩
    have hle : (Function.minimalPeriod T x : ℝ) ≤ n := by exact_mod_cast hx.minimalPeriod_le hn
    have := mul_le_mul_of_nonneg_left hle hε
    linarith
  · rintro ⟨hpos, y, hy, p, hp, ha⟩
    exact ⟨_, hpos, Function.isPeriodicPt_minimalPeriod T x, y, hy, p, hp, ha⟩

/-- The cycle `(−1)` is an `ε`-circuit for every `ε`. -/
theorem isCircuit_neg_one (ε : ℝ) : IsCircuit ε (-1) := by
  refine ⟨1, one_pos, T_iterate_neg_one_int 1, -1, ⟨0, rfl⟩, ⌈ε⌉₊, ?_,
    fun i _ _ => a_neg_one_int i⟩
  have := Nat.le_ceil ε
  push_cast
  linarith

/-- The cycle `(1)` is an `ε`-circuit iff `ε ≤ 1`. -/
theorem isCircuit_one_iff (ε : ℝ) : IsCircuit ε 1 ↔ ε ≤ 1 := by
  constructor
  · rintro ⟨n, hn, -, y, ⟨m, rfl⟩, p, hp, ha⟩
    have hp0 : p = 0 := by
      by_contra hne
      have := ha 1 le_rfl (by omega)
      simp only [T_iterate_one_int, a_one_int] at this
      omega
    subst hp0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_contra hlt
    have hlt' : 1 < ε := lt_of_not_ge hlt
    push_cast at hp
    nlinarith
  · intro hε
    exact ⟨1, one_pos, T_iterate_one_int 1, 1, ⟨0, rfl⟩, 0, by push_cast; linarith,
      fun i h1 h2 => absurd (h1.trans h2) (by norm_num)⟩

/-- The cycle `(−5, −7)` is a `1`-circuit. -/
theorem isCircuit_neg_five : IsCircuit 1 (-5) := by
  have hx : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  refine ⟨2, two_pos, cycle_neg_five.1, T^[1] (-5), ⟨1, rfl⟩, 1, by norm_num, fun i h1 h2 => ?_⟩
  obtain rfl : i = 1 := by omega
  rw [a_iterate, show 1 + 1 = 2 from rfl, a, hx]
  exact ((T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩
    (by norm_num)).1).symm

/-- The remark of l.218: a cycle with a point `y` such that `a_1(y) = ⋯ = a_{n−1}(y) = 1` (Steiner's
shape) is a `1`-circuit. -/
theorem isCircuit_one_of_run {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : Function.IsPeriodicPt T n x)
    (m : ℕ) (h : ∀ i : ℕ, 1 ≤ i → i ≤ n - 1 → a i (T^[m] x) = 1) : IsCircuit 1 x := by
  refine ⟨n, hn, hx, T^[m] x, ⟨m, rfl⟩, n - 1, ?_, h⟩
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  simp

end Syracuse
