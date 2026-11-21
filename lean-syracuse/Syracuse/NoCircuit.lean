import Syracuse.TwoDescents
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Syracuse § 2, `theo:exists_no_circuit_other`: the steps of the proof on an ε-circuit

`theo:exists_no_circuit_other` — `syracuse.tex:219`. Not marked. The proof (l.221–247) stops at
an inequality that bounds `n` (l.244); it does not reach the statement. Its cited input, Matveev's
theorem, is carried as an explicit hypothesis. The steps are proved here in their true forms:
the 3-adic step (l.225–229), the identity and the bound of l.231–237, and the inequality handed to
Matveev's theorem (l.239–244). The statement itself is recorded as a `Prop` and left open (SCOPE).

> **theo:exists_no_circuit_other.** If $\varepsilon\geq 10^{-14}$, there exists no
> $\varepsilon$-circuit other than the known ones.

> *Proof.* Let $x$ a $\varepsilon$-circuit of minimal period $n\geq1$, let $i\in \NN$ and let
> $p\geq \varepsilon n$ such that $\forall k \in \lsem 1,p\rsem,~a_{i+k}(x)=1.$
> We consider $A_{p+i}(y)-A_{p+i+1}(y)$.
> On the one hand, from the previous Lemma, this difference is divisible by $3^p$, and since
> $i\neq i+1$ and $n$ is a minimal period we have $A_{p+i}(y)-A_{p+i+1}(y)\neq 0$.
> Furthermore, $2^{p_n}-3^n$ is not divisible by $3$ thus
> $$2^{p_n}-3^n \leq 3^{-p}\left|A_{p+i}(y)-A_{p+i+1}(y)\right|.$$
> Furthermore
> $$3^{-p}\left(A_{p+i}(y)-A_{p+i+1}(y)\right) = \sum_{k=1}^{n-1-p} 3^{n-1-p-k}\left(
> 2^{\sum_{j=0}^{k-1} a_{p+i}(y)}-2^{\sum_{j=0}^{k-1} a_{p+i+1}(y)} \right)$$
> $$=\sum_{k=1}^{n-1-p} 3^{n-1-p-k} 2^{\sum_{j=1}^{k-1} a_{p+i}(y)}\left(2^{a_{p+i}}-
> 2^{a_{p+i+k}(y)} \right) =\sum_{k=1}^{n-1-p} 3^{n-1-p-k} 2^{\sum_{j=1}^{k-1}
> a_{p+i}(y)}\left(2-2^{a_{p+i+k}(y)} \right)$$
> $$\leq 3^{n-p}\frac{3^{n\eta}-1}{3^\eta-1} \leq 2\log(3)3^{(1-\varepsilon+\eta)n}.$$
> On the other hand from Matveev Theorem, one has
> $$\left| 2^{p_n}-3^{n}\right|\geq \frac{2^{p_n}}{(p_ne)^C}$$
> with $C = \frac{1}{2}e2^{4.5}30^5\log(3) \simeq 3.6\cdot 10^{8}$.
> Since $2^{p_n}\geq 3^n$ and $p_n\leq n\log(3+\eta)$ we thus obtain
> $$  3^{n(\epsilon-\eta)} \leq 2 \left(\log(3+\eta)n\right)^{3.7\cdot 10^8}.$$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `x` an ε-circuit (`def:circuit`, OQ-63 (d)) | `IsCircuit ε x` (strict: the orbit, `p ≥ εn − 1`); the steps take an explicit run length `q` (the paper's `p`; `p` is `p_n` here) |
| `p ≥ εn` (l.222) against `p ≥ εn − 1` (l.216) | both: the steps hold for every `q`; `noCircuit_l244_eps` and the finiteness take `q ≥ εn − 1`, which the proof's `q ≥ εn` implies; `noCircuit_l244_of_eta` takes the proof's `q ≥ εn` |
| `n ≥ 1` the minimal period (l.222) | ⚠ strengthened: `n ≥ 2` and `T^m x ≠ x` for `0 < m < n`; at `n = 1` the step of l.227 is false (Finding 1) |
| `i ∈ ℕ`, `a_{i+k}(x) = 1` on `⟦1, p⟧` (l.222–224) | ✓ carried; ⚠ weakened to `i ∈ ℤ` |
| `x` against `y` (l.222, l.225) | one sequence `α`, `n`-periodic, `α k = a_k(x)`: `A_u(y)` read as `A_u(a(x))` |
| `A_u` (OQ-43); the index of `a_i` (OQ-63 (b)) | both readings of OQ-43: `Aun` (`3^q`) and `AunAlt` (`3^{q−1}`); one convention, `α k = a_k(x)`, the run being any `q` consecutive indices |
| `η` (l.235–244), never defined | the bound of l.235 is proved without it (`noCircuit_abs_diff_le`); the `η`-forms under the partial-sum bound of l.253 (`hgrowth`), Finding 4 |
| Matveev's theorem (l.239–241) | ⚠ strengthened: the hypothesis `NoCircuitMatveev C` (shape of `theo:matveev`) or `NoCircuitMatveevAbs C` (l.240 as printed), `C` a parameter, `0 ≤ C`; never an axiom (T-syr-cited) |
| `2^{p_n} ≥ 3ⁿ` (l.243) | not needed by the true l.244 (every cycle of `ℤ`); used, with `x > 0`, only by the `η`-form |
| `p_n ≤ n log(3 + η)` (l.243) | replaced by `p_n ≤ 2n` (`twoDesc_p_le`); with `log` natural it is false (Finding 5) |
| « the known ones » (l.219) | a parameter `K`; the reading of the four known cycles of `ℤ` is `noCircuitKnown` |

## SCOPE (disclosed)

* **Proved.** The 3-adic step of l.225–229 on every cycle of `ℤ` of least period `n ≥ 2`:
  `3^q (2^{p_n} − 3ⁿ) ∣ A_{q+i} − A_{q+i+1} ≠ 0`, so `3^q |2^{p_n} − 3ⁿ| ≤ |A_{q+i} − A_{q+i+1}|`,
  and l.229 holds as printed (`noCircuit_step`; `noCircuit_step_alt` for OQ-43). The identity of
  l.232–234 in its true form (`noCircuit_diff_eq`, `_alt`), the sign (`A_{q+i} − A_{q+i+1} < 0`), and
  the bound `3 · 2ⁿ |A_{q+i} − A_{q+i+1}| ≤ 2 · 3ⁿ (2^{p_n} − 2ⁿ)` (`noCircuit_abs_diff_le`,
  `noCircuit_upper`), sharp (`noCircuitSum_bound_sharp`; attained at `(−5, −7)`). With Matveev's
  theorem as a hypothesis, the true l.244: `3^{q+1} 2ⁿ ≤ 2 · 3ⁿ (e p_n)^C` (`noCircuit_l244`), i.e.
  `3^{n(ε − log₃(3/2))} ≤ 2 (2en)^C` (`noCircuit_l244_eps`). Hence, for `ε > log₃(3/2) ≈ 0.369`, one
  `B` bounds the least period of every ε-circuit of `ℤ` (`noCircuit_period_bounded`, `_pos`). The
  statement for that `ε` thus reduces to the ε-circuits of least period `≤ B`
  (`noCircuit_of_cited`). That theorem carries the bound as a conjunct; without it the reduction is a
  tautology. Witnesses: `(−5, −7)`,
  the cycle of `−17` (`noCircuit_nonvacuous_seq12`, `_seq17`, `noCircuit_isCircuit_neg_seventeen`).
* **Not proved: the statement** (`NoCircuitStatement K`, a `Prop`). For `10⁻¹⁴ ≤ ε ≤ log₃(3/2)` the
  steps bound nothing (`noCircuit_l244_eps_vacuous`): the bound of l.235 with `η < ε` is the
  missing step. Even above the threshold, `B` is not computed and the check of the periods `≤ B` is
  not done. The proof stops at l.244 and needs both. With the printed `p ≥ εn − 1` the statement
  contains every cycle of `ℤ` of period `n ≤ 10¹⁴` (`noCircuitStatement_period_le`).
* **Finding 1 (l.222, l.227): `n ≥ 2` is needed.** At `n = 1`, `i ≡ i + 1`: on `(−1)`, an
  `ε`-circuit for every `ε`, `A_{q+i} − A_{q+i+1} = 0` (`noCircuit_step_period_one_false`).
* **Finding 2 (l.227, OQ-43): `3^p` holds for the printed `A_u^n` only.** For OQ-43's `A'`, at the
  cycle of `−17` (`i = 6`, `q = 3`), `A'_9 − A'_{10} = −2502` and `27 ∤ −2502`
  (`noCircuit_alt_three_pow_false`). What holds is `3^{q−1}`.
* **Finding 3 (l.232–234): the display is false as printed.** Its sum stops at `n − 1 − p` with
  `3^{n−1−p−k}`; the true one stops at `n − p` with `3^{n−p−k}`, so the display misses the term
  `m = n − p`, which can be nonzero (at `−17` with `i = 6`, `q = 3` it is `−224` of the total
  `−278`). At `−17`, `3^{−3}(A_9 − A_{10}) = −278`, the display is `−110` (literal indices) or `−18`
  (indices restored) (`noCircuit_display_printed_false`).
* **Finding 4 (l.235–236): the `η` step is unproved.** Signed, the chain bounds a negative number
  (`noCircuit_upper`) and holds trivially. l.229 needs it in absolute value. There, l.235 follows
  from `2^{a_{p+i+1}+⋯+a_{p+i+m}} ≤ (3 + η)^m` (l.253) (`noCircuit_l235_of_eta`). The draft does not
  prove that bound, and from `a ≥ 1` alone nothing better than `noCircuit_abs_diff_le` follows. l.236
  fails for every `η` with `2 log 3 (3^η − 1) < 1`, for all large `n` and every `p ≤ εn`, so at
  `p = εn` (`noCircuit_l236_false`). With the natural `log` (the Lean statement's) this is
  `η < 0.341`; it is `η < 0.652` with `log₁₀` and `η < 0.250` with `log₂`. l.244 needs `η < ε`, so
  for `ε` below that threshold (`0.341`, `0.652` or `0.250`) the chain cannot run.
* **Finding 5 (l.239–244).** Under the `η` bound, l.244 holds as `3^{n(ε−η)} (3^η − 1) < (e p_n)^C`
  (`noCircuit_l244_of_eta`). « `p_n ≤ n log(3 + η)` » fails with the natural `log` on every positive
  cycle (`noCircuit_l243_natural_log_false`): its `log` is `log₂`.
* **Finding 6 (l.241): the constant.** `½ e 2^{4.5} 30⁵ log 3 > 7 · 10⁸ > 3.7 · 10⁸`. The printed
  `≃ 3.6 · 10⁸` is the value with `log₁₀ 3` (`noCircuit_matveev_constant`). `theo:matveev` has
  `d = 3.5 · 10⁶` (l.158). Here `C` is a parameter.
* **Finding 7 (l.219): « the known ones ».** Read as the cycle `(1, 4, 2)` of the abstract (l.42),
  the statement is false at `(−1)` (`noCircuitStatement_false_of_neg_one`). `(−5, −7)` and `−17` are
  `ε`-circuits too, for `ε ≤ 1` and `ε ≤ 4/7` (`isCircuit_neg_five`,
  `noCircuit_isCircuit_neg_seventeen`). The four known cycles of `ℤ` are `noCircuitKnown`.
* The stray display after the proof (l.251–257) is not formalized. Its first line is `0` as printed
  (the two exponents coincide).
* `T`, `a`, `p` are the total maps of `Syracuse.Base`, the paper's over `ℤ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset Filter

/-! ### Minimal periods, runs and the window after a run -/

/-- On a cycle of least period `n`, an `n`-periodic extension of `a(x)` has no smaller period. -/
theorem noCircuit_alpha_minimal {x : ℤ} {n : ℕ} (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x)
    {α : ℤ → ℕ} (hα : ∀ k : ℕ, α k = a k x) :
    ∀ m : ℕ, 0 < m → m < n → ¬ Function.Periodic α m := by
  intro m hm hmn hpm
  apply hmin m hm hmn
  have h1 : ∀ k, a (k + m) x = a k x := by
    intro k
    rw [← hα, ← hα]
    have := hpm (k : ℤ)
    push_cast
    exact this
  have := (periodic_a_iff_periodic_T x m).1 h1 0
  simpa using this

/-- On a cycle of least period `n ≥ 2`, a run of ascending indices is shorter than `n`. -/
theorem noCircuit_run_lt {x : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ}
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) : q < n := by
  by_contra hqn
  push Not at hqn
  apply noCircuit_alpha_minimal hmin hα 1 one_pos (by omega)
  have hall : ∀ t : ℕ, t < n → α (i + 1 + t) = 1 := fun t ht => by
    rw [show i + 1 + t = i + ((t + 1 : ℕ) : ℤ) by push_cast; ring]
    exact hrun _ (by omega) (by omega)
  have hconst : ∀ y : ℤ, α y = 1 := by
    intro y
    have hn' : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
    have e := periodic_emod hper (y - (i + 1))
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = (y - (i + 1)) % n :=
      ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')⟩
    have hrn : r < n := by have := Int.emod_lt_of_pos (y - (i + 1)) hn'; omega
    have hP := periodic_emod hper y
    -- α y = α (i + 1 + r) since y ≡ i + 1 + r mod n
    have hq := hper.int_mul ((y - (i + 1)) / n)
    simp only [Int.cast_id] at hq
    have hy : y = (i + 1 + r) + (y - (i + 1)) / n * n := by
      rw [hr]; have := Int.emod_add_mul_ediv (y - (i + 1)) n; linarith
    rw [hy, hq]
    exact hall r hrn
  intro y
  rw [hconst, hconst]

/-! ### The 3-adic step (l.225–229) -/

/-- The run gives the `3`-adic bound of `lem:periodic_exists_i_a_i_` (printed `A_u^n`): if
`a_{i+k} = 1` for `k ∈ ⟦1, q⟧`, then `3^q ∣ A_{q+i} − A_{q+i+1}`. -/
theorem noCircuit_three_pow_dvd {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {i : ℤ}
    {q : ℕ} (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (3 : ℤ) ^ q ∣ (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α := by
  refine three_pow_dvd_Aun_sub hper (fun r hr1 hrq => ?_)
  rw [show (q : ℤ) + i - r = i + ((q - r : ℕ) : ℤ) by push_cast [Nat.cast_sub hrq.le]; ring,
    show (q : ℤ) + i + 1 - r = i + ((q - r + 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hrq.le]; ring,
    hrun _ (by omega) (by omega), hrun _ (by omega) (by omega)]

/-- On a cycle of `ℤ`, `2^{p_n} − 3ⁿ` divides every printed `A_u^n`, `u ∈ ℤ`. -/
theorem noCircuit_dvd_Aun {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) (u : ℤ) :
    ((2 : ℤ) ^ p n x - 3 ^ n) ∣ (Aun n u α : ℤ) := by
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  rw [Aun_eq_three_mul_add hper u, ← hP]
  exact dvd_add (dvd_mul_of_dvd_right
    ((dvd_iff_dvd_AunAlt_of_cycle hn hx hper hα _).1 dvd_rfl u) _) dvd_rfl

/-- On a cycle of least period `n ≥ 2`, `A_u − A_{u+1} ≠ 0` for every `u ∈ ℤ`, both readings. -/
theorem noCircuit_diff_ne_zero {x : ℤ} {n : ℕ} (hn : 2 ≤ n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) (u : ℤ) :
    (Aun n u α : ℤ) - Aun n (u + 1) α ≠ 0 ∧ (AunAlt n u α : ℤ) - AunAlt n (u + 1) α ≠ 0 := by
  have hpos := one_le_of_cycle (by omega) hx hper hα
  have hamin := noCircuit_alpha_minimal hmin hα
  have hn' : (0 : ℤ) < n := by exact_mod_cast (by omega : 0 < n)
  have hu0 := Int.emod_nonneg u hn'.ne'
  have hu1 := Int.emod_lt_of_pos u hn'
  have hv0 := Int.emod_nonneg (u + 1) hn'.ne'
  have hv1 := Int.emod_lt_of_pos (u + 1) hn'
  have hne : u % (n : ℤ) ≠ (u + 1) % n := by
    intro h
    have h2 : (n : ℤ) ∣ (u + 1) - u := Int.ModEq.dvd h
    simp only [add_sub_cancel_left] at h2
    have := Int.le_of_dvd one_pos h2
    omega
  have eA := periodic_emod (Aun_periodic hper) u
  have eA1 := periodic_emod (Aun_periodic hper) (u + 1)
  have eB := periodic_emod (AunAlt_periodic hper) u
  have eB1 := periodic_emod (AunAlt_periodic hper) (u + 1)
  rw [eA, eA1, eB, eB1]
  exact ⟨Aun_sub_ne_zero_of_minimal hpos hper hamin hu0 (by omega) hv0 (by omega) hne,
    AunAlt_sub_ne_zero_of_minimal hpos hper hamin hu0 (by omega) hv0 (by omega) hne⟩

/-- **The step of l.225–229, printed `A_u^n`.** On a cycle of `ℤ` of least period `n ≥ 2` with
`a_{i+k} = 1` for `k ∈ ⟦1, q⟧`: `3^q (2^{p_n} − 3ⁿ)` divides `A_{q+i} − A_{q+i+1} ≠ 0`; hence
`3^q |2^{p_n} − 3ⁿ| ≤ |A_{q+i} − A_{q+i+1}|`, and the display of l.229 as printed. -/
theorem noCircuit_step {x : ℤ} {n : ℕ} (hn : 2 ≤ n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ}
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (3 : ℤ) ^ q * ((2 : ℤ) ^ p n x - 3 ^ n) ∣ (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α ∧
    (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α ≠ 0 ∧
    3 ^ q * |(2 : ℤ) ^ p n x - 3 ^ n| ≤ |(Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α| ∧
    (2 : ℝ) ^ p n x - 3 ^ n ≤
      |(((Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α : ℤ) : ℝ)| / 3 ^ q := by
  have hn0 : 0 < n := by omega
  have hpos := one_le_of_cycle hn0 hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  have h3 : (3 : ℤ) ^ q ∣ (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α :=
    noCircuit_three_pow_dvd hper hrun
  have hDd : ((2 : ℤ) ^ p n x - 3 ^ n) ∣ (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α :=
    dvd_sub (noCircuit_dvd_Aun hn0 hx hper hα _) (noCircuit_dvd_Aun hn0 hx hper hα _)
  have h3D : ¬ (3 : ℤ) ∣ (2 : ℤ) ^ p n x - 3 ^ n := by
    rw [hP]; exact (delta_odd_not_three_dvd hpos hn0).2
  have hco : IsCoprime ((3 : ℤ) ^ q) ((2 : ℤ) ^ p n x - 3 ^ n) :=
    IsCoprime.pow_left ((Int.prime_three.coprime_iff_not_dvd).2 h3D)
  have hdvd := hco.mul_dvd h3 hDd
  have hne := (noCircuit_diff_ne_zero hn hx hmin hper hα ((q : ℤ) + i)).1
  have hle : 3 ^ q * |(2 : ℤ) ^ p n x - 3 ^ n| ≤
      |(Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α| := by
    have := Int.le_of_dvd (abs_pos.2 hne) ((abs_dvd_abs _ _).2 hdvd)
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ q)] at this
  refine ⟨hdvd, hne, hle, ?_⟩
  have hle' : (3 : ℝ) ^ q * |(2 : ℝ) ^ p n x - 3 ^ n| ≤
      |(((Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α : ℤ) : ℝ)| := by
    exact_mod_cast hle
  rw [le_div_iff₀ (by positivity)]
  have h3q : (0 : ℝ) < 3 ^ q := by positivity
  nlinarith [le_abs_self ((2 : ℝ) ^ p n x - 3 ^ n)]

/-- The step of l.225–229 for the OQ-43 reading: the power of `3` drops by one. -/
theorem noCircuit_step_alt {x : ℤ} {n : ℕ} (hn : 2 ≤ n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (3 : ℤ) ^ (q - 1) * ((2 : ℤ) ^ p n x - 3 ^ n) ∣
      (AunAlt n (q + i) α : ℤ) - AunAlt n (q + i + 1) α ∧
    (AunAlt n (q + i) α : ℤ) - AunAlt n (q + i + 1) α ≠ 0 ∧
    3 ^ (q - 1) * |(2 : ℤ) ^ p n x - 3 ^ n| ≤
      |(AunAlt n (q + i) α : ℤ) - AunAlt n (q + i + 1) α| := by
  obtain ⟨hdvd, -, -, -⟩ := noCircuit_step hn hx hmin hper hα hrun
  have e3 : (3 : ℤ) ^ q = 3 * 3 ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Aun_sub_eq_three_mul hper, e3, mul_assoc] at hdvd
  have hdvd' := (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).1 hdvd
  have hne := (noCircuit_diff_ne_zero hn hx hmin hper hα ((q : ℤ) + i)).2
  refine ⟨hdvd', hne, ?_⟩
  have := Int.le_of_dvd (abs_pos.2 hne) ((abs_dvd_abs _ _).2 hdvd')
  rwa [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (q - 1))] at this

/-- For the OQ-43 reading, « divisible by `3^p` » (l.227) fails: at the cycle of `−17`, with the
run `a_7 = a_8 = a_9 = 1` (`i = 6`, `q = 3`), `A'_9 − A'_{10} = −2502 = −2 · 3² · 139`. -/
theorem noCircuit_alt_three_pow_false :
    (∀ k : ℕ, 1 ≤ k → k ≤ 3 → seq17 (6 + k) = 1) ∧
    (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 = -2502 ∧
    ¬ (3 : ℤ) ^ 3 ∣ (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 := by
  have e : (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 = -2502 := by
    decide
  refine ⟨fun k h1 h2 => ?_, e, ?_⟩
  · interval_cases k <;> decide
  · rw [e]; decide

/-- **At `n = 1` the step of l.227 fails**: the circuit `(−1)` has least period `1`, is an
`ε`-circuit for every `ε`, has runs of every length, and `A_{q+i} − A_{q+i+1} = 0`. -/
theorem noCircuit_step_period_one_false :
    Function.minimalPeriod T (-1 : ℤ) = 1 ∧ (∀ ε : ℝ, IsCircuit ε (-1)) ∧
    (∀ k : ℕ, (fun _ : ℤ => (1 : ℕ)) k = a k (-1 : ℤ)) ∧
    ∀ (q : ℕ) (i : ℤ), (∀ k : ℕ, 1 ≤ k → k ≤ q → (fun _ : ℤ => (1 : ℕ)) (i + k) = 1) ∧
      (Aun 1 (q + i) (fun _ => 1) : ℤ) - Aun 1 (q + i + 1) (fun _ => 1) = 0 ∧
      (AunAlt 1 (q + i) (fun _ => 1) : ℤ) - AunAlt 1 (q + i + 1) (fun _ => 1) = 0 := by
  refine ⟨Function.minimalPeriod_eq_one_iff_isFixedPt.2 T_neg_one_int.1, isCircuit_neg_one,
    fun k => (a_neg_one_int k).symm, fun q i => ⟨fun _ _ _ => rfl, ?_, ?_⟩⟩
  · simp [Aun_one]
  · simp [AunAlt]

/-! ### The identity and the bound of l.231–237 -/

/-- The sum of l.234, corrected: `∑_{m=1}^{N} 3^{N−m} 2^{β_1+⋯+β_{m−1}} (2 − 2^{β_m})`, with
`β` indexed from `0` (`β_j = a_{p+i+1+j}`, `N = n − p`). -/
def noCircuitSum (β : ℕ → ℕ) (N : ℕ) : ℤ :=
  ∑ m ∈ range N, (3 : ℤ) ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, β j) * (2 - 2 ^ β m)

/-- One more term: `S(N + 1) = 3 S(N) + 2^{β_0+⋯+β_{N−1}} (2 − 2^{β_N})`. -/
theorem noCircuitSum_succ (β : ℕ → ℕ) (N : ℕ) :
    noCircuitSum β (N + 1) = 3 * noCircuitSum β N + 2 ^ (∑ j ∈ range N, β j) * (2 - 2 ^ β N) := by
  unfold noCircuitSum
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    have := Finset.mem_range.1 hm
    rw [show N + 1 - 1 - m = (N - 1 - m) + 1 by omega, pow_succ]
    ring
  · rw [show N + 1 - 1 - N = 0 by omega, pow_zero, one_mul]

/-- Every term of the sum of l.234 is `≤ 0` when `β ≥ 1`. -/
theorem noCircuitSum_nonpos {β : ℕ → ℕ} {N : ℕ} (hβ : ∀ j, j < N → 1 ≤ β j) :
    noCircuitSum β N ≤ 0 := by
  unfold noCircuitSum
  refine Finset.sum_nonpos (fun m hm => ?_)
  have h2 : (2 : ℤ) ≤ 2 ^ β m := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ β m := pow_le_pow_right₀ (by norm_num) (hβ m (Finset.mem_range.1 hm))
  have : (0 : ℤ) ≤ 3 ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, β j) := by positivity
  nlinarith

/-- **The bound from `β ≥ 1` alone**: `3 · 2^N · (−S) ≤ 2 · 3^N (2^{β_0+⋯+β_{N−1}} − 2^N)`,
i.e. `−S ≤ 2 · 3^{N−1} (2^{∑β − N} − 1)`. Equality for `β = (B, 1, …, 1)`. -/
theorem noCircuitSum_bound {β : ℕ → ℕ} {N : ℕ} (hβ : ∀ j, j < N → 1 ≤ β j) :
    3 * 2 ^ N * (-noCircuitSum β N) ≤ 2 * 3 ^ N * (2 ^ (∑ j ∈ range N, β j) - 2 ^ N) := by
  induction N with
  | zero => simp [noCircuitSum]
  | succ N ih =>
    have ih' := ih (fun j hj => hβ j (by omega))
    have e1 : (2 : ℤ) ^ (N + 1) = 2 ^ N * 2 := pow_succ _ _
    have e2 : (3 : ℤ) ^ (N + 1) = 3 ^ N * 3 := pow_succ _ _
    have e3 : (2 : ℤ) ^ (∑ j ∈ range N, β j + β N) = 2 ^ (∑ j ∈ range N, β j) * 2 ^ β N :=
      pow_add _ _ _
    rw [noCircuitSum_succ, Finset.sum_range_succ, e1, e2, e3]
    have hY : (2 : ℤ) ≤ 2 ^ β N := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ β N := pow_le_pow_right₀ (by norm_num) (hβ N (by omega))
    have hZ : (2 : ℤ) ^ N ≤ 3 ^ N := pow_le_pow_left₀ (by norm_num) (by norm_num) N
    have hW : (0 : ℤ) ≤ 2 ^ (∑ j ∈ range N, β j) := by positivity
    have key : 0 ≤ 6 * 2 ^ (∑ j ∈ range N, β j) * (2 ^ β N - 2) * ((3 : ℤ) ^ N - 2 ^ N) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    nlinarith [ih', key]

/-- **The bound is sharp**: equality for `β = (B, 1, …, 1)`, every `N ≥ 1` and `B`. From `a ≥ 1`
and the sum `∑β` alone, nothing better than `noCircuitSum_bound` follows. -/
theorem noCircuitSum_bound_sharp (M B : ℕ) :
    3 * 2 ^ (M + 1) * (-noCircuitSum (fun j => if j = 0 then B else 1) (M + 1)) =
      2 * 3 ^ (M + 1) * (2 ^ (∑ j ∈ range (M + 1), (fun j : ℕ => if j = 0 then B else 1) j) -
        2 ^ (M + 1)) := by
  have hS : noCircuitSum (fun j => if j = 0 then B else 1) (M + 1) = 3 ^ M * (2 - 2 ^ B) := by
    unfold noCircuitSum
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm
      simp [hm]
    · intro h; simp at h
  have hsum : ∑ j ∈ range (M + 1), (fun j : ℕ => if j = 0 then B else 1) j = M + B := by
    rw [Finset.sum_range_succ']
    simp
  rw [hS, hsum]
  ring

/-- The window after the run: `∑_{j<n−q} a_{q+i+1+j} + q = ∑_{t<n} a_t`. -/
theorem noCircuit_window_sum {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {i : ℤ} {q : ℕ}
    (hqn : q ≤ n) (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    ∑ j ∈ range (n - q), α (q + i + 1 + j) + q = ∑ t ∈ range n, α t := by
  have h := sum_range_add_int α (i + 1) q (n - q)
  rw [show q + (n - q) = n by omega, sum_range_periodic hper] at h
  have hrun' : ∑ t ∈ range q, α (i + 1 + t) = ∑ t ∈ range q, 1 := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [show i + 1 + (t : ℤ) = i + ((t + 1 : ℕ) : ℤ) by push_cast; ring]
    exact hrun _ (by omega) (by have := Finset.mem_range.1 ht; omega)
  have e : ∑ t ∈ range (n - q), α (i + 1 + q + t) = ∑ j ∈ range (n - q), α (q + i + 1 + j) :=
    Finset.sum_congr rfl (fun t _ => by congr 1; ring)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hrun'
  omega

/-- **The identity of l.232–234, true form** (printed `A_u^n`): for `n`-periodic `a` with
`a_{i+k} = 1` on `⟦1, q⟧`, `1 ≤ q ≤ n`,
`A_{q+i} − A_{q+i+1} = 3^q ∑_{m=1}^{n−q} 3^{n−q−m} 2^{a_{q+i+1}+⋯+a_{q+i+m−1}} (2 − 2^{a_{q+i+m}})`. -/
theorem noCircuit_diff_eq {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {i : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hqn : q ≤ n) (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α =
      3 ^ q * noCircuitSum (fun j => α (q + i + 1 + j)) (n - q) := by
  have hrefl : ∀ w : ℤ, (Aun n w α : ℤ) = ∑ m ∈ range n,
      (3 : ℤ) ^ (n - 1 - m) * 2 ^ (∑ t ∈ range (m + 1), α (w + t)) := by
    intro w
    rw [Aun_eq_sum]
    push_cast
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have := Finset.mem_range.1 hm
    rw [show n - (n - 1 - m) = m + 1 by omega]
  have hαu : α ((q : ℤ) + i) = 1 := by rw [add_comm]; exact hrun q hq le_rfl
  have hterm : ∀ m ∈ range n,
      (3 : ℤ) ^ (n - 1 - m) * 2 ^ (∑ t ∈ range (m + 1), α ((q : ℤ) + i + t)) -
        3 ^ (n - 1 - m) * 2 ^ (∑ t ∈ range (m + 1), α ((q : ℤ) + i + 1 + t)) =
      3 ^ (n - 1 - m) * 2 ^ (∑ j ∈ range m, α ((q : ℤ) + i + 1 + j)) *
        (2 - 2 ^ α ((q : ℤ) + i + 1 + m)) := by
    intro m _
    rw [Finset.sum_range_succ' (fun t : ℕ => α ((q : ℤ) + i + t)),
      Finset.sum_range_succ (fun t : ℕ => α ((q : ℤ) + i + 1 + t))]
    have e : ∑ t ∈ range m, α ((q : ℤ) + i + ((t + 1 : ℕ) : ℤ)) =
        ∑ t ∈ range m, α ((q : ℤ) + i + 1 + t) :=
      Finset.sum_congr rfl (fun t _ => by congr 1; push_cast; ring)
    rw [e, Nat.cast_zero, add_zero, hαu, pow_add, pow_add, pow_one]
    ring
  rw [hrefl, hrefl, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm]
  set f : ℕ → ℤ := fun m => (3 : ℤ) ^ (n - 1 - m) * 2 ^ (∑ j ∈ range m, α ((q : ℤ) + i + 1 + j)) *
    (2 - 2 ^ α ((q : ℤ) + i + 1 + m)) with hf
  have hsplit : ∑ m ∈ range n, f m = ∑ m ∈ range (n - q), f m + ∑ r ∈ range q, f (n - q + r) := by
    rw [← Finset.sum_range_add, Nat.sub_add_cancel hqn]
  have hzero : ∑ r ∈ range q, f (n - q + r) = 0 := by
    refine Finset.sum_eq_zero (fun r hr => ?_)
    have hr' := Finset.mem_range.1 hr
    have hα1 : α ((q : ℤ) + i + 1 + ((n - q + r : ℕ) : ℤ)) = 1 := by
      have e1 : (q : ℤ) + i + 1 + ((n - q + r : ℕ) : ℤ) = (i + ((r + 1 : ℕ) : ℤ)) + n := by
        push_cast [Nat.cast_sub hqn]; ring
      rw [e1, hper]
      exact hrun _ (by omega) (by omega)
    simp only [hf, hα1, pow_one, sub_self, mul_zero]
  rw [hsplit, hzero, add_zero, noCircuitSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' := Finset.mem_range.1 hm
  simp only [hf]
  rw [show n - 1 - m = q + (n - q - 1 - m) by omega, pow_add]
  ring

/-- The identity for the OQ-43 reading: `3 (A'_{q+i} − A'_{q+i+1})` is the same sum. -/
theorem noCircuit_diff_eq_alt {α : ℤ → ℕ} {n : ℕ} (hper : Function.Periodic α n) {i : ℤ}
    {q : ℕ} (hq : 1 ≤ q) (hqn : q ≤ n) (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    3 * ((AunAlt n (q + i) α : ℤ) - AunAlt n (q + i + 1) α) =
      3 ^ q * noCircuitSum (fun j => α (q + i + 1 + j)) (n - q) := by
  rw [← Aun_sub_eq_three_mul hper]
  exact noCircuit_diff_eq hper hq hqn hrun

/-- **The bound of l.235, true form** (no `η`): `A_{q+i} − A_{q+i+1} ≤ 0`, and
`3 · 2ⁿ |A_{q+i} − A_{q+i+1}| ≤ 2 · 3ⁿ (2^P − 2ⁿ)`, `P = ∑_{t<n} a_t`. -/
theorem noCircuit_abs_diff_le {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ}
    (hper : Function.Periodic α n) {i : ℤ} {q : ℕ} (hq : 1 ≤ q) (hqn : q ≤ n)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α ≤ 0 ∧
    3 * 2 ^ n * |(Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α| ≤
      2 * 3 ^ n * (2 ^ (∑ t ∈ range n, α t) - 2 ^ n) := by
  have h := noCircuit_diff_eq hper hq hqn hrun
  have hβ : ∀ j, j < n - q → 1 ≤ (fun j : ℕ => α (q + i + 1 + j)) j := fun j _ => hpos _
  have hS := noCircuitSum_nonpos hβ
  have hB := noCircuitSum_bound hβ
  have hW := noCircuit_window_sum hper hqn hrun
  have h3q : (0 : ℤ) < 3 ^ q := by positivity
  refine ⟨by rw [h]; nlinarith, ?_⟩
  rw [h, abs_mul, abs_of_pos h3q, abs_of_nonpos hS, ← hW]
  have e1 : (2 : ℤ) ^ n = 2 ^ (n - q) * 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hqn]
  have e2 : (3 : ℤ) ^ n = 3 ^ (n - q) * 3 ^ q := by rw [← pow_add, Nat.sub_add_cancel hqn]
  rw [e1, e2, pow_add]
  have h0 : (0 : ℤ) ≤ 3 ^ q * 2 ^ q := by positivity
  have := mul_le_mul_of_nonneg_left hB h0
  linarith

/-- **l.225–237 on an ε-circuit, assembled** (printed `A_u^n`): the identity, the sign, the bound,
and with the step: `3^{q+1} 2ⁿ |2^{p_n} − 3ⁿ| ≤ 2 · 3ⁿ (2^{p_n} − 2ⁿ)`. -/
theorem noCircuit_upper {x : ℤ} {n : ℕ} (hn : 2 ≤ n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    q < n ∧
    (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α =
        3 ^ q * noCircuitSum (fun j => α (q + i + 1 + j)) (n - q) ∧
    (Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α < 0 ∧
    3 * 2 ^ n * |(Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α| ≤ 2 * 3 ^ n * (2 ^ p n x - 2 ^ n) ∧
    3 ^ (q + 1) * 2 ^ n * |(2 : ℤ) ^ p n x - 3 ^ n| ≤ 2 * 3 ^ n * (2 ^ p n x - 2 ^ n) := by
  have hn0 : 0 < n := by omega
  have hqn := noCircuit_run_lt hn hmin hper hα hrun
  have hpos := one_le_of_cycle hn0 hx hper hα
  have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
  obtain ⟨hle0, hB⟩ := noCircuit_abs_diff_le hpos hper hq hqn.le hrun
  obtain ⟨-, hne, hstep, -⟩ := noCircuit_step hn hx hmin hper hα hrun
  rw [← hP] at hB
  refine ⟨hqn, noCircuit_diff_eq hper hq hqn.le hrun, lt_of_le_of_ne hle0 hne, hB, ?_⟩
  have h0 : (0 : ℤ) ≤ 3 * 2 ^ n := by positivity
  calc (3 : ℤ) ^ (q + 1) * 2 ^ n * |(2 : ℤ) ^ p n x - 3 ^ n| =
        3 * 2 ^ n * (3 ^ q * |(2 : ℤ) ^ p n x - 3 ^ n|) := by ring
    _ ≤ 3 * 2 ^ n * |(Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α| :=
        mul_le_mul_of_nonneg_left hstep h0
    _ ≤ _ := hB

/-! ### Matveev's theorem as a hypothesis, and the inequality of l.239–244 -/

/-- **Matveev's theorem** in the shape of `theo:matveev` (l.156–159) and l.240, with the constant
`C` a parameter (`d = 3.5·10⁶` at l.158, `C ≈ 3.6·10⁸` at l.241): `3ⁿ < 2^P` gives
`2^P − 3ⁿ ≥ 2^P / (eP)^C`. A hypothesis, never an axiom (T-syr-cited). -/
def NoCircuitMatveev (C : ℝ) : Prop :=
  ∀ P n : ℕ, 0 < P → 0 < n → (3 : ℝ) ^ n < 2 ^ P →
    (2 : ℝ) ^ P / (Real.exp 1 * P) ^ C ≤ 2 ^ P - 3 ^ n

/-- The display of l.240 as printed, with the absolute value and no condition on the sign. -/
def NoCircuitMatveevAbs (C : ℝ) : Prop :=
  ∀ P n : ℕ, 0 < P → 0 < n → (2 : ℝ) ^ P / (Real.exp 1 * P) ^ C ≤ |(2 : ℝ) ^ P - 3 ^ n|

/-- The display of l.240 implies the shape of `theo:matveev`. -/
theorem NoCircuitMatveevAbs.matveev {C : ℝ} (h : NoCircuitMatveevAbs C) : NoCircuitMatveev C := by
  intro P n hP hn h3
  have := h P n hP hn
  rwa [abs_of_pos (by linarith)] at this

/-- **The inequality handed to Matveev's theorem, true form**: given its lower bound at
`(p_n, n)`, `3^{q+1} 2ⁿ ≤ 2 · 3ⁿ (e p_n)^C`. No `η`, and no `2^{p_n} ≥ 3ⁿ`. -/
theorem noCircuit_l244_of_lower {x : ℤ} {n : ℕ} (hn : 2 ≤ n) (hx : T^[n] x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ} (hper : Function.Periodic α n)
    (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) {C : ℝ}
    (hlow : (2 : ℝ) ^ p n x / (Real.exp 1 * p n x) ^ C ≤ |(2 : ℝ) ^ p n x - 3 ^ n|) :
    (3 : ℝ) ^ (q + 1) * 2 ^ n ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C := by
  obtain ⟨-, -, -, -, h5⟩ := noCircuit_upper hn hx hmin hper hα hq hrun
  have h5r : (3 : ℝ) ^ (q + 1) * 2 ^ n * |(2 : ℝ) ^ p n x - 3 ^ n| ≤
      2 * 3 ^ n * (2 ^ p n x - 2 ^ n) := by exact_mod_cast h5
  have hpos := one_le_of_cycle (by omega) hx hper hα
  have hPn : n ≤ p n x := by
    have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
    rw [hP]
    calc n = ∑ _t ∈ range n, 1 := by simp
      _ ≤ ∑ t ∈ range n, α t := Finset.sum_le_sum (fun t _ => hpos t)
  have hPr : (0 : ℝ) < p n x := by exact_mod_cast (by omega : 0 < p n x)
  have hE : 0 < (Real.exp 1 * p n x) ^ C := Real.rpow_pos_of_pos (by positivity) C
  have h2P : (0 : ℝ) < 2 ^ p n x := by positivity
  rw [div_le_iff₀ hE] at hlow
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h3 : (0 : ℝ) ≤ 3 ^ (q + 1) * 2 ^ n := by positivity
  have key : ((3 : ℝ) ^ (q + 1) * 2 ^ n) * 2 ^ p n x ≤
      (2 * 3 ^ n * (Real.exp 1 * p n x) ^ C) * 2 ^ p n x := by
    calc ((3 : ℝ) ^ (q + 1) * 2 ^ n) * 2 ^ p n x
        ≤ ((3 : ℝ) ^ (q + 1) * 2 ^ n) * (|(2 : ℝ) ^ p n x - 3 ^ n| *
            (Real.exp 1 * p n x) ^ C) := mul_le_mul_of_nonneg_left hlow h3
      _ = ((3 : ℝ) ^ (q + 1) * 2 ^ n * |(2 : ℝ) ^ p n x - 3 ^ n|) *
            (Real.exp 1 * p n x) ^ C := by ring
      _ ≤ (2 * 3 ^ n * (2 ^ p n x - 2 ^ n)) * (Real.exp 1 * p n x) ^ C :=
          mul_le_mul_of_nonneg_right h5r hE.le
      _ ≤ (2 * 3 ^ n * (Real.exp 1 * p n x) ^ C) * 2 ^ p n x := by
          have : (0 : ℝ) ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C := by positivity
          nlinarith
  exact le_of_mul_le_mul_right key h2P

/-- The same on every cycle of `ℤ`, from the display of l.240. -/
theorem noCircuit_l244 {C : ℝ} (hM : NoCircuitMatveevAbs C) {x : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (hx : T^[n] x = x) (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ} (hq : 1 ≤ q)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (3 : ℝ) ^ (q + 1) * 2 ^ n ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C := by
  have hpos := one_le_of_cycle (by omega) hx hper hα
  have hPn : n ≤ p n x := by
    have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
    rw [hP]
    calc n = ∑ _t ∈ range n, 1 := by simp
      _ ≤ ∑ t ∈ range n, α t := Finset.sum_le_sum (fun t _ => hpos t)
  exact noCircuit_l244_of_lower hn hx hmin hper hα hq hrun (hM _ _ (by omega) (by omega))

/-- The same for `x > 0`, from `theo:matveev`'s shape. -/
theorem noCircuit_l244_pos {C : ℝ} (hM : NoCircuitMatveev C) {x : ℤ} (hx0 : 0 < x) {n : ℕ}
    (hn : 2 ≤ n) (hx : T^[n] x = x) (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) :
    (3 : ℝ) ^ (q + 1) * 2 ^ n ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C := by
  have hpos := one_le_of_cycle (by omega) hx hper hα
  have hPn : n ≤ p n x := by
    have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
    rw [hP]
    calc n = ∑ _t ∈ range n, 1 := by simp
      _ ≤ ∑ t ∈ range n, α t := Finset.sum_le_sum (fun t _ => hpos t)
  have hsign := two_pow_p_sub_three_pow_mul_pos (by omega : 0 < n) hx
  have hD : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign hx0.le
  have hDr : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  refine noCircuit_l244_of_lower hn hx hmin hper hα hq hrun ?_
  rw [abs_of_pos (by linarith)]
  exact hM _ _ (by omega) (by omega) hDr

/-- **l.244, true form, in the paper's shape**: with `q ≥ εn − 1` (`def:circuit`; the proof's
`q ≥ εn` implies it), `3^{n(ε − log₃(3/2))} ≤ 2 (2en)^C`. The printed
`3^{n(ε−η)} ≤ 2(log(3+η) n)^{3.7·10⁸}` has `η` free; here `η = log₃(3/2) ≈ 0.369`. -/
theorem noCircuit_l244_eps {C : ℝ} (hC : 0 ≤ C) {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {q : ℕ} {ε : ℝ} (hqε : ε * n - 1 ≤ q)
    (h244 : (3 : ℝ) ^ (q + 1) * 2 ^ n ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C) :
    (3 : ℝ) ^ ((n : ℝ) * (ε - Real.logb 3 (3 / 2))) ≤ 2 * (2 * Real.exp 1 * n) ^ C := by
  have hP2 := twoDesc_p_le hn hx
  have hP2r : (p n x : ℝ) ≤ 2 * n := by exact_mod_cast hP2
  have hEle : (Real.exp 1 * p n x) ^ C ≤ (2 * Real.exp 1 * n) ^ C := by
    apply Real.rpow_le_rpow (by positivity) _ hC
    have := Real.exp_pos 1
    nlinarith
  have h3q : (3 : ℝ) ^ (ε * n) ≤ 3 ^ (q + 1) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; linarith
  have hL : (3 : ℝ) ^ Real.logb 3 (3 / 2) = 3 / 2 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have e1 : (3 : ℝ) ^ ((n : ℝ) * ε) = 3 ^ (ε * n) := by rw [mul_comm]
  have e2 : (3 : ℝ) ^ ((n : ℝ) * Real.logb 3 (3 / 2)) = (3 / 2) ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), hL, Real.rpow_natCast]
  have e : (3 : ℝ) ^ ((n : ℝ) * (ε - Real.logb 3 (3 / 2))) = 3 ^ (ε * n) * 2 ^ n / 3 ^ n := by
    rw [mul_sub, Real.rpow_sub (by norm_num), e1, e2, div_pow]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have h3n : (0 : ℝ) ≤ 2 * 3 ^ n := by positivity
  calc (3 : ℝ) ^ (ε * n) * 2 ^ n ≤ 3 ^ (q + 1) * 2 ^ n := mul_le_mul_of_nonneg_right h3q h2n
    _ ≤ 2 * 3 ^ n * (Real.exp 1 * p n x) ^ C := h244
    _ ≤ 2 * 3 ^ n * (2 * Real.exp 1 * n) ^ C := mul_le_mul_of_nonneg_left hEle h3n
    _ = 2 * (2 * Real.exp 1 * n) ^ C * 3 ^ n := by ring

/-- **Below the threshold the true l.244 bounds nothing**: for `ε ≤ log₃(3/2)` its inequality holds
for every `n ≥ 1`. -/
theorem noCircuit_l244_eps_vacuous {C : ℝ} (hC : 0 ≤ C) {ε : ℝ}
    (hε : ε ≤ Real.logb 3 (3 / 2)) {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℝ) ^ ((n : ℝ) * (ε - Real.logb 3 (3 / 2))) ≤ 2 * (2 * Real.exp 1 * n) ^ C := by
  have h1 : (3 : ℝ) ^ ((n : ℝ) * (ε - Real.logb 3 (3 / 2))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith))
  have hbase : (1 : ℝ) ≤ 2 * Real.exp 1 * n := by
    have := Real.add_one_le_exp 1
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have h2 : (1 : ℝ) ≤ (2 * Real.exp 1 * n) ^ C := Real.one_le_rpow hbase hC
  linarith

/-- Exponential beats polynomial: for `θ > 1`, only finitely many `n` have `θⁿ ≤ K (2en)^C`. -/
theorem noCircuit_eventually {θ K C : ℝ} (hθ : 1 < θ) :
    ∃ B : ℕ, ∀ n : ℕ, θ ^ n ≤ K * (2 * Real.exp 1 * n) ^ C → n ≤ B := by
  set k := ⌈C⌉₊ with hk
  set M : ℝ := max K 0 * (2 * Real.exp 1) ^ k + 1 with hM
  have hM0 : 0 < M := by positivity
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hθ).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / M))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ht
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  have hn1 : 1 ≤ n := by omega
  have h1 := hN₀ n (by omega)
  have hθn : 0 < θ ^ n := by positivity
  have h1' : M * (n : ℝ) ^ k < θ ^ n := by
    rw [div_lt_div_iff₀ hθn hM0] at h1
    linarith
  have hbase : (1 : ℝ) ≤ 2 * Real.exp 1 * n := by
    have := Real.add_one_le_exp 1
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have h2 : (2 * Real.exp 1 * n) ^ C ≤ (2 * Real.exp 1) ^ k * (n : ℝ) ^ k := by
    rw [← mul_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil C)
  have h3 : K * (2 * Real.exp 1 * n) ^ C ≤ max K 0 * ((2 * Real.exp 1) ^ k * (n : ℝ) ^ k) := by
    have hpow : 0 ≤ (2 * Real.exp 1 * n) ^ C := Real.rpow_nonneg (by positivity) C
    calc K * (2 * Real.exp 1 * n) ^ C ≤ max K 0 * (2 * Real.exp 1 * n) ^ C :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
      _ ≤ max K 0 * ((2 * Real.exp 1) ^ k * (n : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  have h4 : max K 0 * ((2 * Real.exp 1) ^ k * (n : ℝ) ^ k) < M * (n : ℝ) ^ k := by
    have : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    rw [hM]; nlinarith
  linarith

/-- The common core of the two finiteness theorems. -/
theorem noCircuit_period_bounded_of {C : ℝ} (hC : 0 ≤ C) {Q : ℤ → Prop}
    (hlow : ∀ x : ℤ, Q x → ∀ n : ℕ, 2 ≤ n → T^[n] x = x →
      (2 : ℝ) ^ p n x / (Real.exp 1 * p n x) ^ C ≤ |(2 : ℝ) ^ p n x - 3 ^ n|)
    {ε : ℝ} (hε : Real.logb 3 (3 / 2) < ε) :
    ∃ B : ℕ, ∀ x : ℤ, Q x → IsCircuit ε x → Function.minimalPeriod T x ≤ B := by
  have hL0 : 0 < Real.logb 3 (3 / 2) := Real.logb_pos (by norm_num) (by norm_num)
  have hε0 : 0 < ε := by linarith
  have hθ : 1 < (3 : ℝ) ^ (ε - Real.logb 3 (3 / 2)) := Real.one_lt_rpow (by norm_num) (by linarith)
  obtain ⟨B₀, hB₀⟩ := noCircuit_eventually (K := 2) (C := C) hθ
  refine ⟨max B₀ (max ⌈1 / ε⌉₊ 1), fun x hQ hcirc => ?_⟩
  obtain ⟨hmp, y, ⟨m, rfl⟩, q, hqε, hrunY⟩ := (isCircuit_iff_minimalPeriod hε0.le x).1 hcirc
  set n := Function.minimalPeriod T x with hndef
  have hx : T^[n] x = x := Function.iterate_minimalPeriod
  have hmin : ∀ m' : ℕ, 0 < m' → m' < n → T^[m'] x ≠ x := fun m' h1 h2 =>
    Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) h2
  by_cases hn1 : n ≤ 1
  · exact le_trans hn1 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hn : 2 ≤ n := by omega
  set α := aPer n x with hαdef
  have hper : Function.Periodic α n := aPer_periodic n x
  have hα : ∀ k : ℕ, α k = a k x := aPer_natCast hx
  have hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α ((m : ℤ) + k) = 1 := by
    intro k h1 h2
    rw [show (m : ℤ) + k = ((k + m : ℕ) : ℤ) by push_cast; ring, hα, ← a_iterate]
    exact hrunY k h1 h2
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · -- no run: εn ≤ 1
    subst hq0
    have h1 : (n : ℝ) ≤ 1 / ε := by
      rw [le_div_iff₀ hε0]; push_cast at hqε; linarith
    have h2 : n ≤ ⌈1 / ε⌉₊ := by exact_mod_cast h1.trans (Nat.le_ceil _)
    exact le_trans h2 (le_trans (le_max_left _ _) (le_max_right _ _))
  · have h244 := noCircuit_l244_of_lower hn hx hmin hper hα hq1 hrun (hlow x hQ n hn hx)
    have heps := noCircuit_l244_eps hC (by omega) hx hqε h244
    have e : (3 : ℝ) ^ ((n : ℝ) * (ε - Real.logb 3 (3 / 2))) =
        ((3 : ℝ) ^ (ε - Real.logb 3 (3 / 2))) ^ n := by
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    rw [e] at heps
    exact le_trans (hB₀ n heps) (le_max_left _ _)

/-- **What the steps give: finitely many periods for `ε > log₃(3/2) ≈ 0.369`**, on every cycle
of `ℤ`, from the display of l.240 (`ε`-circuits as printed, `p ≥ εn − 1`). -/
theorem noCircuit_period_bounded {C : ℝ} (hC : 0 ≤ C) (hM : NoCircuitMatveevAbs C) {ε : ℝ}
    (hε : Real.logb 3 (3 / 2) < ε) :
    ∃ B : ℕ, ∀ x : ℤ, IsCircuit ε x → Function.minimalPeriod T x ≤ B := by
  obtain ⟨B, hB⟩ := noCircuit_period_bounded_of (Q := fun _ => True) hC
    (fun x _ n hn hx => by
      have hpos := one_le_of_cycle (by omega) hx (aPer_periodic n x) (aPer_natCast hx)
      have hPn : n ≤ p n x := by
        have hP : p n x = ∑ t ∈ range n, aPer n x t := by simp only [p, aPer_natCast hx]
        rw [hP]
        calc n = ∑ _t ∈ range n, 1 := by simp
          _ ≤ ∑ t ∈ range n, aPer n x t := Finset.sum_le_sum (fun t _ => hpos t)
      exact hM _ _ (by omega) (by omega)) hε
  exact ⟨B, fun x hx => hB x trivial hx⟩

/-- The same for `x > 0`, from `theo:matveev`'s shape. -/
theorem noCircuit_period_bounded_pos {C : ℝ} (hC : 0 ≤ C) (hM : NoCircuitMatveev C) {ε : ℝ}
    (hε : Real.logb 3 (3 / 2) < ε) :
    ∃ B : ℕ, ∀ x : ℤ, 0 < x → IsCircuit ε x → Function.minimalPeriod T x ≤ B := by
  refine noCircuit_period_bounded_of (Q := fun x => 0 < x) hC (fun x hx0 n hn hx => ?_) hε
  have hpos := one_le_of_cycle (by omega) hx (aPer_periodic n x) (aPer_natCast hx)
  have hPn : n ≤ p n x := by
    have hP : p n x = ∑ t ∈ range n, aPer n x t := by simp only [p, aPer_natCast hx]
    rw [hP]
    calc n = ∑ _t ∈ range n, 1 := by simp
      _ ≤ ∑ t ∈ range n, aPer n x t := Finset.sum_le_sum (fun t _ => hpos t)
  have hsign := two_pow_p_sub_three_pow_mul_pos (by omega : 0 < n) hx
  have hD : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign (le_of_lt hx0)
  have hDr : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  rw [abs_of_pos (by linarith)]
  exact hM _ _ (by omega) (by omega) hDr

/-! ### The statement, recorded as a `Prop` -/

/-- The points of the four known cycles of `ℤ`: `(1)`, `(−1)`, `(−5, −7)` and that of `−17`. -/
def noCircuitKnown : Set ℤ := {1, -1, -5, -7, -17, -25, -37, -55, -41, -61, -91}

/-- `theo:exists_no_circuit_other` as printed, « the known ones » being the set `K`. -/
def NoCircuitStatement (K : Set ℤ) : Prop :=
  ∀ ε : ℝ, 1 / 10 ^ 14 ≤ ε → ∀ x : ℤ, IsCircuit ε x → x ∈ K

/-- A cycle with `εn ≤ 1` is an `ε`-circuit (`p = 0`, by the printed `p ≥ εn − 1`). -/
theorem noCircuit_isCircuit_of_le {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {ε : ℝ}
    (hε : ε * n ≤ 1) : IsCircuit ε x :=
  ⟨n, hn, hx, x, ⟨0, rfl⟩, 0, by push_cast; linarith,
    fun i h1 h2 => absurd (h1.trans h2) (by norm_num)⟩

/-- By `IsCircuit.mono`, the statement is its case `ε = 10⁻¹⁴`. -/
theorem noCircuitStatement_iff (K : Set ℤ) :
    NoCircuitStatement K ↔ ∀ x : ℤ, IsCircuit (1 / 10 ^ 14) x → x ∈ K := by
  constructor
  · intro h x hx
    exact h _ le_rfl x hx
  · intro h ε hε x hx
    exact h x (hx.mono hε)

/-- **The statement contains every cycle of period `≤ 10¹⁴`**: under it, every point of a cycle
of `ℤ` of period `n ≤ 10¹⁴` is a known one. -/
theorem noCircuitStatement_period_le {K : Set ℤ} (h : NoCircuitStatement K) {x : ℤ} {n : ℕ}
    (hn : 0 < n) (hn' : n ≤ 10 ^ 14) (hx : T^[n] x = x) : x ∈ K := by
  refine h _ le_rfl x (noCircuit_isCircuit_of_le hn hx ?_)
  have : (n : ℝ) ≤ 10 ^ 14 := by exact_mod_cast hn'
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  exact this

/-- **If « the known ones » are those of the abstract (l.42, the positive cycle `(1, 4, 2)`), the
statement is false**: for every `K` without `−1`, the fixed point `(−1)` refutes it. -/
theorem noCircuitStatement_false_of_neg_one {K : Set ℤ} (hK : (-1 : ℤ) ∉ K) :
    ¬ NoCircuitStatement K := fun h => hK (h _ le_rfl (-1) (isCircuit_neg_one _))

/-- **The reduction to a finite check, for `ε > log₃(3/2)`**: from Matveev's theorem (l.240) there
is one `B` that bounds the least period of every `ε`-circuit of `ℤ` (the first conjunct, which is
`noCircuit_period_bounded`). So, for every reading `K` of « the known ones », the statement for that
`ε` reduces to the `ε`-circuits of least period `≤ B` (the second). The content is the first
conjunct. Do not drop it: without it, `∃ B, (check up to B) → statement` holds for every `ε` and `K`
with no hypothesis (take `B` the least period of a counterexample), and is vacuous. -/
theorem noCircuit_of_cited {C : ℝ} (hC : 0 ≤ C) (hM : NoCircuitMatveevAbs C) {ε : ℝ}
    (hε : Real.logb 3 (3 / 2) < ε) :
    ∃ B : ℕ, (∀ x : ℤ, IsCircuit ε x → Function.minimalPeriod T x ≤ B) ∧
      ∀ K : Set ℤ, (∀ x : ℤ, IsCircuit ε x → Function.minimalPeriod T x ≤ B → x ∈ K) →
        ∀ x : ℤ, IsCircuit ε x → x ∈ K := by
  obtain ⟨B, hB⟩ := noCircuit_period_bounded hC hM hε
  exact ⟨B, hB, fun _ hcheck x hx => hcheck x hx (hB x hx)⟩

/-! ### Witnesses: the known circuits -/

/-- The cycle of `−17` is a `4/7`-circuit (`p = 3 ≥ 4 − 1`; in the proof's reading `3 ≥ (3/7)·7`). -/
theorem noCircuit_isCircuit_neg_seventeen : IsCircuit (4 / 7) (-17) := by
  obtain ⟨hx, ha⟩ := cycle_neg_seventeen
  refine ⟨7, by norm_num, hx, T^[6] (-17), ⟨6, rfl⟩, 3, by norm_num, fun i h1 h2 => ?_⟩
  rw [a_iterate, ← ha]
  interval_cases i <;> decide

/-- **Non-vacuity at the cycle of `−17`** (`n = 7`, `i = 6`, `q = 3`): every hypothesis of
`noCircuit_step` and `noCircuit_upper` holds, and `A_9 − A_{10} = −7506 = 3³ · 2 · (−139)`,
`2^{p_7} − 3⁷ = −139`, `3⁴ · 2⁷ · 139 ≤ 2 · 3⁷ (2^{11} − 2⁷)`. -/
theorem noCircuit_nonvacuous_seq17 :
    T^[7] (-17 : ℤ) = -17 ∧ (∀ m : ℕ, 0 < m → m < 7 → T^[m] (-17 : ℤ) ≠ -17) ∧
    Function.Periodic seq17 (7 : ℕ) ∧
    (∀ k : ℕ, seq17 k = a k (-17 : ℤ)) ∧ (∀ k : ℕ, 1 ≤ k → k ≤ 3 → seq17 (6 + k) = 1) ∧
    p 7 (-17 : ℤ) = 11 ∧
    (Aun 7 ((3 : ℕ) + 6) seq17 : ℤ) - Aun 7 ((3 : ℕ) + 6 + 1) seq17 = -7506 ∧
    noCircuitSum (fun j => seq17 ((3 : ℕ) + 6 + 1 + j)) (7 - 3) = -278 ∧
    (3 : ℤ) ^ (3 + 1) * 2 ^ 7 * |(2 : ℤ) ^ 11 - 3 ^ 7| ≤ 2 * 3 ^ 7 * (2 ^ 11 - 2 ^ 7) := by
  obtain ⟨hx, ha⟩ := cycle_neg_seventeen
  have hp17 : p 7 (-17 : ℤ) = 11 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← ha 0, ← ha 1, ← ha 2, ← ha 3, ← ha 4, ← ha 5, ← ha 6]
    decide
  refine ⟨hx, twoDesc_neg_seventeen_minimal, seq17_periodic, ha, fun k h1 h2 => ?_, hp17,
    by decide, by decide, by norm_num⟩
  interval_cases k <;> decide

/-- **Non-vacuity at the cycle `(−5, −7)`** (`n = 2`, `i = 1`, `q = 1`): every hypothesis of
`noCircuit_step` and `noCircuit_upper` holds, and `A_2 − A_3 = −6`. -/
theorem noCircuit_nonvacuous_seq12 :
    T^[2] (-5 : ℤ) = -5 ∧ (∀ m : ℕ, 0 < m → m < 2 → T^[m] (-5 : ℤ) ≠ -5) ∧
    Function.Periodic seq12 (2 : ℕ) ∧ (∀ k : ℕ, seq12 k = a k (-5 : ℤ)) ∧ (∀ k : ℕ, 1 ≤ k → k ≤ 1 → seq12 (1 + k) = 1) ∧
    (Aun 2 ((1 : ℕ) + 1) seq12 : ℤ) - Aun 2 ((1 : ℕ) + 1 + 1) seq12 = -6 ∧
    p 2 (-5 : ℤ) = 3 := by
  have hp5 : p 2 (-5 : ℤ) = 3 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← seq12_eq_a 0, ← seq12_eq_a 1]
    decide
  refine ⟨cycle_neg_five.1, fun m h1 h2 => ?_, seq12_periodic, seq12_eq_a, fun k h1 h2 => ?_,
    by decide, hp5⟩
  · obtain rfl : m = 1 := by omega
    exact cycle_neg_five.2
  · obtain rfl : k = 1 := by omega
    decide

/-- The bound of `noCircuit_abs_diff_le` is attained on a cycle: `(−5, −7)`, `i = 1`, `q = 1`,
`3 · 2² · 6 = 2 · 3² (2³ − 2²)`. -/
theorem noCircuit_bound_sharp_seq12 :
    3 * 2 ^ 2 * |(Aun 2 ((1 : ℕ) + 1) seq12 : ℤ) - Aun 2 ((1 : ℕ) + 1 + 1) seq12| =
      2 * 3 ^ 2 * (2 ^ p 2 (-5 : ℤ) - 2 ^ 2) := by
  have e : (Aun 2 ((1 : ℕ) + 1) seq12 : ℤ) - Aun 2 ((1 : ℕ) + 1 + 1) seq12 = -6 := by decide
  have hp5 : p 2 (-5 : ℤ) = 3 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← seq12_eq_a 0, ← seq12_eq_a 1]
    decide
  rw [e, hp5]
  norm_num

/-! ### Findings on the printed displays -/

/-- The display of l.232 with its indices as printed: `∑_{k=1}^{n−1−p} 3^{n−1−p−k}
(2^{k a_{p+i}} − 2^{k a_{p+i+1}})` (the inner sums over `j` have no `j`). -/
def noCircuitDisplayLit (n q : ℕ) (i : ℤ) (α : ℤ → ℕ) : ℤ :=
  ∑ k ∈ Icc 1 (n - 1 - q), (3 : ℤ) ^ (n - 1 - q - k) * (2 ^ (k * α (q + i)) - 2 ^ (k * α (q + i + 1)))

/-- The display of l.232 with the summation index restored (`a_{p+i+j}`, `a_{p+i+1+j}`). -/
def noCircuitDisplay (n q : ℕ) (i : ℤ) (α : ℤ → ℕ) : ℤ :=
  ∑ k ∈ Icc 1 (n - 1 - q), (3 : ℤ) ^ (n - 1 - q - k) *
    (2 ^ (∑ j ∈ range k, α (q + i + j)) - 2 ^ (∑ j ∈ range k, α (q + i + 1 + j)))

/-- **l.232 is false as printed, in both index readings and both readings of OQ-43**: at the
cycle of `−17` (`i = 6`, `p = 3`), `3^{−3}(A_9 − A_{10}) = −278` and `3^{−3}(A'_9 − A'_{10}) =
−2502/27`, while the display is `−110` (literal) or `−18` (indices restored). -/
theorem noCircuit_display_printed_false :
    noCircuitDisplayLit 7 3 6 seq17 = -110 ∧ noCircuitDisplay 7 3 6 seq17 = -18 ∧
    (Aun 7 ((3 : ℕ) + 6) seq17 : ℤ) - Aun 7 ((3 : ℕ) + 6 + 1) seq17 ≠
      3 ^ 3 * noCircuitDisplayLit 7 3 6 seq17 ∧
    (Aun 7 ((3 : ℕ) + 6) seq17 : ℤ) - Aun 7 ((3 : ℕ) + 6 + 1) seq17 ≠
      3 ^ 3 * noCircuitDisplay 7 3 6 seq17 ∧
    (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 ≠
      3 ^ 3 * noCircuitDisplayLit 7 3 6 seq17 ∧
    (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 ≠
      3 ^ 3 * noCircuitDisplay 7 3 6 seq17 := by
  have e1 : noCircuitDisplayLit 7 3 6 seq17 = -110 := by decide
  have e2 : noCircuitDisplay 7 3 6 seq17 = -18 := by decide
  have e3 : (Aun 7 ((3 : ℕ) + 6) seq17 : ℤ) - Aun 7 ((3 : ℕ) + 6 + 1) seq17 = -7506 := by decide
  have e4 : (AunAlt 7 ((3 : ℕ) + 6) seq17 : ℤ) - AunAlt 7 ((3 : ℕ) + 6 + 1) seq17 = -2502 := by
    decide
  rw [e1, e2, e3, e4]
  norm_num

/-- **The constant of l.241**: `½ e 2^{4.5} 30⁵ log 3 > 7 · 10⁸` with the natural logarithm (the
draft's `log` elsewhere, l.114–124), more than the `3.7 · 10⁸` of l.244; with `log₁₀ 3` it lies
in `(3.5 · 10⁸, 3.6 · 10⁸)`, the printed `≃ 3.6 · 10⁸`. -/
theorem noCircuit_matveev_constant :
    7 * 10 ^ 8 < 1 / 2 * Real.exp 1 * (2 : ℝ) ^ (9 / 2 : ℝ) * 30 ^ 5 * Real.log 3 ∧
    35 * 10 ^ 7 < 1 / 2 * Real.exp 1 * (2 : ℝ) ^ (9 / 2 : ℝ) * 30 ^ 5 * Real.logb 10 3 ∧
    1 / 2 * Real.exp 1 * (2 : ℝ) ^ (9 / 2 : ℝ) * 30 ^ 5 * Real.logb 10 3 < 36 * 10 ^ 7 := by
  have h2 : (2 : ℝ) ^ (9 / 2 : ℝ) = 16 * √2 := by
    rw [show (9 / 2 : ℝ) = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    norm_num
  have hs1 : (1.4142 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : √2 < (1.41422 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hY1 : (7.4731 * 10 ^ 8 : ℝ) < 194400000 * (Real.exp 1 * √2) := by nlinarith
  have hY2 : 194400000 * (Real.exp 1 * √2) < (7.4733 * 10 ^ 8 : ℝ) := by nlinarith
  have hl3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith)
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hb1 : (0.47 : ℝ) < Real.logb 10 3 := by
    rw [Real.logb, lt_div_iff₀ hl10]
    have h := Real.log_lt_log (by norm_num) (show (10 : ℝ) ^ 47 < 3 ^ 100 by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have hb2 : Real.logb 10 3 < (0.48 : ℝ) := by
    rw [Real.logb, div_lt_iff₀ hl10]
    have h := Real.log_lt_log (by norm_num) (show (3 : ℝ) ^ 100 < 10 ^ 48 by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  have e : ∀ L : ℝ, 1 / 2 * Real.exp 1 * (2 : ℝ) ^ (9 / 2 : ℝ) * 30 ^ 5 * L =
      194400000 * (Real.exp 1 * √2) * L := by
    intro L; rw [h2]; ring
  rw [e, e]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **l.243 « `p_n ≤ n log(3 + η)` » with the natural logarithm fails on every positive cycle**,
for `0 ≤ η ≤ 1`: there `p_n > n log₂ 3 > n log 4 ≥ n log(3 + η)`. The `log` of l.243 is `log₂`. -/
theorem noCircuit_l243_natural_log_false {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n)
    (hx : T^[n] x = x) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (n : ℝ) * Real.log (3 + η) < p n x := by
  have hsign := two_pow_p_sub_three_pow_mul_pos hn hx
  have hD : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign hx0.le
  have hDr : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  have hlog := Real.log_lt_log (by positivity) hDr
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have h4 : Real.log (3 + η) ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num), show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
    exact Real.log_le_log (by linarith) (by linarith)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : 2 * (n : ℝ) * Real.log 2 < p n x := by
    by_contra hc
    push Not at hc
    have : (p n x : ℝ) * Real.log 2 ≤ 2 * n * Real.log 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hc hl2'.le
    nlinarith
  nlinarith

/-! ### The `η`-form of l.235–236 -/

/-- **l.235 under the reading of `η` that l.253 makes explicit**: if the partial sums after the
run satisfy `2^{a_{q+i+1}+⋯+a_{q+i+m}} ≤ (3 + η)^m`, then
`3^{−q} |A_{q+i} − A_{q+i+1}| ≤ 3^{n−q} (3^{nη} − 1)/(3^η − 1)`. The draft proves no such bound. -/
theorem noCircuit_l235_of_eta {α : ℤ → ℕ} (hpos : ∀ k, 1 ≤ α k) {n : ℕ}
    (hper : Function.Periodic α n) {i : ℤ} {q : ℕ} (hq : 1 ≤ q) (hqn : q < n)
    (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) {η : ℝ} (hη : 0 < η)
    (hgrowth : ∀ m : ℕ, m ≤ n - q →
      (2 : ℝ) ^ (∑ j ∈ range m, α (q + i + 1 + j)) ≤ (3 + η) ^ m) :
    |(((Aun n (q + i) α : ℤ) - Aun n (q + i + 1) α : ℤ) : ℝ)| / 3 ^ q ≤
      3 ^ (n - q) * ((3 ^ ((n : ℝ) * η) - 1) / (3 ^ η - 1)) := by
  have h := noCircuit_diff_eq hper hq hqn.le hrun
  have hβ : ∀ j, j < n - q → 1 ≤ (fun j : ℕ => α (q + i + 1 + j)) j := fun j _ => hpos _
  have hS := noCircuitSum_nonpos hβ
  have hSr : ((noCircuitSum (fun j => α (q + i + 1 + j)) (n - q) : ℤ) : ℝ) ≤ 0 := by
    exact_mod_cast hS
  have h3q : (0 : ℝ) < 3 ^ q := by positivity
  rw [h, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, abs_mul, abs_of_pos h3q, abs_of_nonpos hSr,
    mul_div_cancel_left₀ _ h3q.ne']
  set N := n - q with hN
  set r : ℝ := (3 : ℝ) ^ η with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hη
  have hl3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (by linarith [Real.exp_one_lt_d9])
  have h3r : 3 + η ≤ 3 * r := by
    have e : r = Real.exp (Real.log 3 * η) := by rw [hr, Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 3 * η)
    nlinarith
  have hneg : -((noCircuitSum (fun j => α (q + i + 1 + j)) N : ℤ) : ℝ) =
      ∑ m ∈ range N, (3 : ℝ) ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) *
        (2 ^ α (q + i + 1 + m) - 2) := by
    unfold noCircuitSum
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hneg]
  have hterm : ∀ m ∈ range N, (3 : ℝ) ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) *
      (2 ^ α (q + i + 1 + m) - 2) ≤ 3 ^ N * r ^ (m + 1) := by
    intro m hm
    have hm' := Finset.mem_range.1 hm
    have hg := hgrowth (m + 1) (by omega)
    rw [Finset.sum_range_succ, pow_add] at hg
    have hp : (3 + η) ^ (m + 1) ≤ (3 * r) ^ (m + 1) :=
      pow_le_pow_left₀ (by linarith) h3r _
    have h3 : (0 : ℝ) ≤ 3 ^ (N - 1 - m) := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) := by positivity
    have e3 : (3 : ℝ) ^ N = 3 ^ (N - 1 - m) * 3 ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    calc (3 : ℝ) ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) *
          (2 ^ α (q + i + 1 + m) - 2)
        ≤ 3 ^ (N - 1 - m) * (2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) * 2 ^ α (q + i + 1 + m)) := by
          have : (0 : ℝ) ≤ 3 ^ (N - 1 - m) * 2 ^ (∑ j ∈ range m, α (q + i + 1 + j)) := by
            positivity
          nlinarith
      _ ≤ 3 ^ (N - 1 - m) * (3 * r) ^ (m + 1) := mul_le_mul_of_nonneg_left (hg.trans hp) h3
      _ = 3 ^ N * r ^ (m + 1) := by rw [mul_pow, e3]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hgeom : ∑ k ∈ range n, r ^ k = (r ^ n - 1) / (r - 1) := geom_sum_eq hr1.ne' n
  have hrn : (3 : ℝ) ^ ((n : ℝ) * η) = r ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hrn, ← hgeom]
  have e1 : ∑ m ∈ range N, r ^ (m + 1) = ∑ k ∈ range (N + 1), r ^ k - 1 := by
    rw [Finset.sum_range_succ']; simp
  rw [e1]
  have hsub : ∑ k ∈ range (N + 1), r ^ k ≤ ∑ k ∈ range n, r ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun k _ _ => by positivity)
  linarith

/-- The partial-sum hypothesis of `noCircuit_l235_of_eta` is satisfiable: at the cycle of `−17`
(`i = 6`, `q = 3`, window `a = (2, 1, 1, 4)`) it holds with `η = 1`. -/
theorem noCircuit_l235_nonvacuous_seq17 :
    ∀ m : ℕ, m ≤ 7 - 3 →
      (2 : ℝ) ^ (∑ j ∈ range m, seq17 ((3 : ℕ) + 6 + 1 + j)) ≤ (3 + 1) ^ m := by
  intro m hm
  have h : 2 ^ (∑ j ∈ range m, seq17 ((3 : ℕ) + 6 + 1 + j)) ≤ 4 ^ m := by
    interval_cases m <;> decide
  norm_num
  exact_mod_cast h

/-- **l.236 fails for small `η`**: if `2 log 3 (3^η − 1) < 1` (with the natural `log`, equivalently
`η < 0.341`; the threshold is `0.652` with `log₁₀` and `0.250` with `log₂`), then for all large `n`
and every `p ≤ εn` (so at the proof's `p = εn`),
`3^{n−p} (3^{nη} − 1)/(3^η − 1) > 2 log 3 · 3^{(1−ε+η)n}`. The conclusion l.244 needs `η < ε`, so
for `ε` below the threshold the chain cannot run. -/
theorem noCircuit_l236_false {η : ℝ} (hη : 0 < η)
    (hsmall : 2 * Real.log 3 * ((3 : ℝ) ^ η - 1) < 1) (ε : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, (q : ℝ) ≤ ε * n →
      2 * Real.log 3 * (3 : ℝ) ^ ((1 - ε + η) * n) <
        3 ^ ((n : ℝ) - q) * ((3 ^ ((n : ℝ) * η) - 1) / (3 ^ η - 1)) := by
  set r : ℝ := (3 : ℝ) ^ η with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hη
  set c : ℝ := 1 - 2 * Real.log 3 * (r - 1) with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_gt_atTop (1 / c))
  refine ⟨N, fun n hn q hq => ?_⟩
  have hrn := hN n hn
  have hcr : 1 < c * r ^ n := by rwa [div_lt_iff₀' hc0] at hrn
  have hc1 : c ≤ 1 := by rw [hc]; nlinarith
  have hrn1 : 1 < r ^ n := by nlinarith
  set A : ℝ := (3 : ℝ) ^ ((1 - ε) * n) with hA
  have hA0 : 0 < A := by positivity
  have e1 : (3 : ℝ) ^ ((1 - ε + η) * n) = A * r ^ n := by
    rw [show (1 - ε + η) * (n : ℝ) = (1 - ε) * n + η * n by ring, Real.rpow_add (by norm_num),
      Real.rpow_mul (by norm_num) η, Real.rpow_natCast]
  have e2 : (3 : ℝ) ^ ((n : ℝ) * η) = r ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hmono : A ≤ 3 ^ ((n : ℝ) - q) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  rw [e1, e2]
  have hfrac : 0 < (r ^ n - 1) / (r - 1) := div_pos (by linarith) (by linarith)
  have hkey : 2 * Real.log 3 * r ^ n < (r ^ n - 1) / (r - 1) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  calc 2 * Real.log 3 * (A * r ^ n) = A * (2 * Real.log 3 * r ^ n) := by ring
    _ < A * ((r ^ n - 1) / (r - 1)) := mul_lt_mul_of_pos_left hkey hA0
    _ ≤ 3 ^ ((n : ℝ) - q) * ((r ^ n - 1) / (r - 1)) := mul_le_mul_of_nonneg_right hmono hfrac.le

/-- **l.239–244 under the `η` reading** (`x > 0`, the proof's `q ≥ εn`): if the partial sums after
the run satisfy the bound of l.253, Matveev's theorem gives
`3^{n(ε−η)} (3^η − 1) < (e p_n)^C`. The paper's l.244 has `2 (log(3+η) n)^{3.7·10⁸}` on the right
and no factor `3^η − 1`. The hypothesis on the partial sums is the open step. -/
theorem noCircuit_l244_of_eta {C : ℝ} (hM : NoCircuitMatveev C) {x : ℤ} (hx0 : 0 < x) {n : ℕ}
    (hn : 2 ≤ n) (hx : T^[n] x = x) (hmin : ∀ m : ℕ, 0 < m → m < n → T^[m] x ≠ x)
    {α : ℤ → ℕ} (hper : Function.Periodic α n) (hα : ∀ k : ℕ, α k = a k x) {i : ℤ} {q : ℕ}
    (hq : 1 ≤ q) (hrun : ∀ k : ℕ, 1 ≤ k → k ≤ q → α (i + k) = 1) {ε η : ℝ} (hη : 0 < η)
    (hqε : ε * n ≤ q)
    (hgrowth : ∀ m : ℕ, m ≤ n - q →
      (2 : ℝ) ^ (∑ j ∈ range m, α (q + i + 1 + j)) ≤ (3 + η) ^ m) :
    (3 : ℝ) ^ ((n : ℝ) * (ε - η)) * ((3 : ℝ) ^ η - 1) < (Real.exp 1 * p n x) ^ C := by
  have hn0 : 0 < n := by omega
  have hqn := noCircuit_run_lt hn hmin hper hα hrun
  have hpos := one_le_of_cycle hn0 hx hper hα
  obtain ⟨-, -, -, hstep⟩ := noCircuit_step hn hx hmin hper hα hrun
  have h235 := noCircuit_l235_of_eta hpos hper hq hqn hrun hη hgrowth
  have hPn : n ≤ p n x := by
    have hP : p n x = ∑ t ∈ range n, α t := by simp only [p, hα]
    rw [hP]
    calc n = ∑ _t ∈ range n, 1 := by simp
      _ ≤ ∑ t ∈ range n, α t := Finset.sum_le_sum (fun t _ => hpos t)
  have hsign := two_pow_p_sub_three_pow_mul_pos hn0 hx
  have hD : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign hx0.le
  have hDr : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  have hlow := hM _ _ (by omega) hn0 hDr
  set r : ℝ := (3 : ℝ) ^ η with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hη
  have hrn : (3 : ℝ) ^ ((n : ℝ) * η) = r ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hrn] at h235
  set E := (Real.exp 1 * (p n x : ℝ)) ^ C with hE
  have hPr : (0 : ℝ) < p n x := by exact_mod_cast (by omega : 0 < p n x)
  have hE0 : 0 < E := Real.rpow_pos_of_pos (by positivity) C
  set A : ℝ := (3 : ℝ) ^ ((1 - ε) * n) with hA
  have hA0 : 0 < A := by positivity
  have h3nq : (3 : ℝ) ^ (n - q) ≤ A := by
    rw [← Real.rpow_natCast, Nat.cast_sub hqn.le]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hrn1 : 1 < r ^ n := one_lt_pow₀ hr1 (by omega)
  -- D ≤ 3^{n-q} (r^n − 1)/(r − 1) < A r^n / (r − 1)
  have hDup : (2 : ℝ) ^ p n x - 3 ^ n < A * r ^ n / (r - 1) := by
    have h1 := hstep.trans h235
    have h2 : (3 : ℝ) ^ (n - q) * ((r ^ n - 1) / (r - 1)) < A * r ^ n / (r - 1) := by
      rw [mul_div_assoc', div_lt_div_iff_of_pos_right (by linarith)]
      have : (0 : ℝ) < 3 ^ (n - q) := by positivity
      nlinarith
    linarith
  -- 3^n / E < D
  have hDlow : (3 : ℝ) ^ n / E < 2 ^ p n x - 3 ^ n := by
    have : (3 : ℝ) ^ n / E < 2 ^ p n x / E := div_lt_div_of_pos_right hDr hE0
    linarith
  have hkey : (3 : ℝ) ^ n * (r - 1) < A * r ^ n * E := by
    have h := hDlow.trans hDup
    rw [div_lt_div_iff₀ hE0 (by linarith)] at h
    linarith
  have e : (3 : ℝ) ^ ((n : ℝ) * (ε - η)) * (A * r ^ n) = 3 ^ n := by
    rw [hA, ← hrn, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      show (n : ℝ) * (ε - η) + ((1 - ε) * n + n * η) = (n : ℕ) by ring, Real.rpow_natCast]
  have hAR : 0 < A * r ^ n := by positivity
  have : (3 : ℝ) ^ ((n : ℝ) * (ε - η)) * (r - 1) * (A * r ^ n) < E * (A * r ^ n) := by
    calc (3 : ℝ) ^ ((n : ℝ) * (ε - η)) * (r - 1) * (A * r ^ n)
        = (3 : ℝ) ^ ((n : ℝ) * (ε - η)) * (A * r ^ n) * (r - 1) := by ring
      _ = 3 ^ n * (r - 1) := by rw [e]
      _ < A * r ^ n * E := hkey
      _ = E * (A * r ^ n) := by ring
  exact lt_of_mul_lt_mul_right this hAR.le

end Syracuse
