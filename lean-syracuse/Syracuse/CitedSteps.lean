import Syracuse.TwoDescents
import Syracuse.Steiner
import Syracuse.NoCircuit

/-!
# Syracuse § 2: finitely many cycles under a GCD bound, and the share of `a_i = 1` in a large cycle

`cor:property_defined_cycles_gcd` — `syracuse.tex:161` (proof l.166–168);
`prop:proposition` — `syracuse.tex:194` (proof l.200–206). Neither is marked. Both rest on
inputs the paper cites and does not prove: a Baker-type lower bound on `|2^p − 3ⁿ|`
(`theo:matveev`, l.156; `theo:mr`, l.145) and the computer check of l.201. Each is a hypothesis
named in the statements (`CitedStepsMatveev`, `CitedStepsMR`, `CitedStepsCheck`), never an axiom.
How they enter is T-syr-cited's question. The paper's own steps are proved (SCOPE).

> **theo:mr** [MR1074572]. Let $a,b\in \ZZ$ such that $|a\log(2)-b\log(3)|\leq e^{-a/\delta}$
> with $\delta \geq 1$ then $$a < 2^{800}\log(3)^{25}\delta^{25} $$

> **theo:matveev** (Matveev). Let $a,b\in \NN^*$ such that $2^a>3^b$. Then :
> $$2^a-3^b \geq \frac{2^a}{e^da^d} $$ where $d = 3.5\cdot 10^6$.

> **cor:property_defined_cycles_gcd.** Let $\mathcal P(\Gamma)$ a property defined on cycles
> $\Gamma$. If $$\exists \varepsilon>0,\forall \Gamma, \quad \left(\mathcal P(\Gamma)\quad\Rightarrow
> \quad \mathrm{GCD}(A_i(\Gamma)~:~ i\in \ZZ) \ll  2^{|\Gamma|(1-\varepsilon)}\right) $$ then there
> exists only finitely many cycles $\Gamma$ such that $\mathcal P(\Gamma)$.
> If furthermore, the domination is effective then the cycles can be determined effectively.
>
> *Proof.* If the property above is satisfyied, then only finitely many couple $(|\Gamma|,n)$ are
> possible. For each admissible couple $(|\Gamma|,n)$, there are only finitely many $a(\Gamma)$ of
> type $(|\Gamma|,n)$, and for each such $a(\Gamma)$ there is at most one syracuse cycle of type
> $a(\Gamma)$. Each step being effective, if the domination is effective then the determination of
> the $\mathcal P$-syracuse-cycle  is effective.

> **prop:proposition.** Let $x\in \ZZ$  and $n\in \NN^*$ such that $T^n(x)=x$.
> If $|x|>1000$ then : $$ \#\left\{i\in \lsem 1,n\rsem ~|~ a_i(x) =1\right\} \geq \alpha n $$
> with $\alpha = 2-\log_2(3)-10^{-10}> 0.415037499$
>
> *Proof.* Since the conjecture has been tested for all integers lesser than $10^{10}$ and no
> cycles have been found containing an integer bigger than $1000$, then $|x|>10^{10}$. Let
> $a=\#\left\{i\in \lsem 1,n\rsem  ~|~ a_i(x) =1\right\} $, we have $p_n\geq a+2(n-a)$. Therefore,
> from Corollary \ref{cor:bounds} we  have
> $$ \log(1+1/|x|) \geq \frac{a+2(n-a)}{n} - \log_2(3)$$ and thus :
> $$ \frac{a}{n} \geq 2-\log_2(3)-\log(1+1/|x|). $$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒫` a property of cycles `Γ` (l.161) | any `P : ℤ → ℕ → Prop` on pairs `(x, n)`, `n ≥ 1`, `Tⁿx = x`; a property of the orbit, or of the least period, is a special case |
| the sign of the cycles (OQ-63 (a)) | both: every cycle of `ℤ` from `theo:mr` (`…_mr…`); the positive cycles from `theo:matveev` (`…_matveev…`), whose printed form covers `2^a > 3^b` only (Finding 1) |
| `∃ ε > 0` | ✓ carried; `ε < 1` is not needed |
| « `≪` » (l.162) | a reading: `≤ C · 2^{|Γ|(1−ε)}` with one constant `C` for all `Γ` |
| `|Γ|` | `p_n(x) = ∑_{k<n} a_k(x)`, as T-syr-two-descents read l.323–324 |
| `GCD(A_i(Γ) : i ∈ ℤ)` | both readings of OQ-43 (`Aun`, `AunAlt`), every index convention (`α (k + c) = a_k(x)`, OQ-63 (b)); the GCD of one period, which is the GCD over `ℤ` (`citedSteps_gcd_dvd`). ⚠ weakened in `…_mr`, `…_matveev`: a bound on `|2^{p_n} − 3ⁿ|`, which is at most either GCD (`citedSteps_abs_le_gcd`) |
| « finitely many cycles » | the set of pairs `(x, n)` is finite; so are its points and its orbits |
| « effective » (l.164, l.167) | a reading: an explicit bound `B(C, ε)` on `|Γ|`, and every `𝒫`-cycle in the computable finite list `citedStepsCandidates ⌊B⌋₊` |
| the cited lower bound (l.145, l.156) | ⚠ strengthened: `CitedStepsMR` or `CitedStepsMatveev`, a hypothesis of the statement |
| `x ∈ ℤ`, `n ∈ ℕ*`, `Tⁿx = x` (`prop:proposition`) | ✓ carried |
| `|x| > 1000` | ✓ carried in the printed form; ⚠ weakened to `x ≠ 1` (`prop_proposition_ne_one`); dropped for `x < 0` (`prop_proposition_neg`) |
| the index of `a_i` in `⟦1, n⟧` (OQ-63 (b)) | both: on a cycle the count over `⟦1, n⟧` (l.62) is the count over `⟦0, n−1⟧` (l.71) (`citedStepsOnes_eq_range`) |
| the computer check (l.201) | ⚠ strengthened, for `x > 0` only: `CitedStepsCheck`, or the weaker `CitedStepsCycleCheck` it implies |
| `cor:bounds` (l.201) | its true form, `Syracuse.bounds` (OQ-54 (c) decides that row's mark, not this one) |

## SCOPE (disclosed)

* **`cor:property_defined_cycles_gcd`, what is proved.** Let `𝒫`-cycles satisfy
  `|2^{p_n} − 3ⁿ| ≤ C 2^{p_n(1−ε)}`, `ε > 0`. From `theo:mr`, every `𝒫`-cycle of `ℤ` has
  `n ≤ p_n ≤ citedStepsBoundMR C ε` and lies in `citedStepsCandidates ⌊citedStepsBoundMR C ε⌋₊`
  (`property_defined_cycles_gcd_mr_effective`). So there are finitely many
  (`property_defined_cycles_gcd_mr`). The same holds from the GCD of the printed `A_u^n` or of
  OQ-43's `A'^n_u`, in every index convention (`…_mr_aun`, `…_mr_alt`; effective:
  `…_mr_effective_aun`, `…_mr_effective_alt`). From `theo:matveev` the same holds for the
  positive cycles, with `citedStepsBoundMatveev` (`…_matveev`, `…_matveev_aun`, `…_matveev_alt`;
  effective: `…_matveev_effective`, `…_matveev_effective_aun`, `…_matveev_effective_alt`).
* **The steps of l.167, each a theorem.** (i) `n ≤ |Γ|` (`citedSteps_le_p`, every `a_k ≥ 1`), and
  `|Γ|` is bounded: `2^P / (K P^d) ≤ X ≤ C 2^{P(1−ε)}` gives
  `P ≤ C K (d+1)! / (ε log 2)^{d+1}` (`citedSteps_le_of_lower`; `citedSteps_le_of_matveev`). From
  `theo:mr`, `P ≤ max(2 log₂(2C)/ε, 2^{800} log(3)^{25} δ^{25})` with `δ = max(1, 2/(ε log 2))`
  (`citedSteps_le_of_mr`, through `|log u| ≤ 2|1 − u|`). (ii) For each `(|Γ|, n)`, the sequences
  `a ∈ ⟦1, |Γ|⟧ⁿ` are finitely many. (iii) At most one cycle per `a`: `lem:base` gives
  `x (2^{p_n} − 3ⁿ) = ∑_{k<n} 2^{p_k} 3^{n−1−k}` (`citedSteps_mul_eq_rhs`,
  `citedSteps_cycle_unique`). (iv) Together: every cycle with `p_n ≤ B` is in
  `citedStepsCandidates B`, a computable `Finset` (`mem_citedStepsCandidates`,
  `citedSteps_finite_of_le`); the kernel evaluates it (`citedStepsCandidates_decide`; `(−17, 7)`
  is one for `B = 11`, `citedStepsCandidates_neg_seventeen`). Deciding
  which candidates are `𝒫`-cycles needs `𝒫` decidable, which the paper does not say.
* **Finding 1 (l.156, l.302, l.326): `theo:matveev` as printed covers only the positive cycles.**
  It assumes `2^a > 3^b`, and on a cycle `2^{p_n} − 3ⁿ` has the sign of `x`
  (`two_pow_p_sub_three_pow_mul_pos`). Over `ℤ` the corollary needs a bound for both signs, which
  `theo:mr`'s form (l.145) gives. Whether § 2's cycles are positive is OQ-63 (a).
* **Finding 2 (l.162): the GCD enters only through `|2^{p_n} − 3ⁿ|`.** On a cycle that number
  divides every `A_u` and `A'_u` (`citedSteps_dvd_Aun`), so it is at most either GCD
  (`citedSteps_abs_le_gcd`). For OQ-43's reading the GCD is that number (`corGcdAlt_of_cycle`); for
  the printed `A_u^n` it is larger (`278` against `139` at `−17`, `citedSteps_gcd_instances`). The
  hypothesis on `|2^{p_n} − 3ⁿ|` is the weakest of all.
* **Applications** (non-vacuity). With `𝒫` = « two descending indices per period », the bound of
  T-syr-two-descents (`twoDesc_corollary_hyp`) is the hypothesis. From `theo:mr`, finitely many
  cycles of `ℤ` qualify; `(−17, 7)` is one (`citedSteps_twoDesc_finite`,
  `citedSteps_twoDesc_neg_seventeen`). With `𝒫` = « one descending index per period », the bound of
  T-syr-steiner (`steiner_corollary_hypothesis`) is the hypothesis. From `theo:matveev`, finitely
  many positive cycles qualify; `(1, 1)` is one (`citedSteps_steiner_finite`,
  `citedSteps_steiner_one`). T-syr-two-descents's hypothesis `TwoDescMatveev B` follows from either
  cited bound, at an explicit `B` (`citedSteps_twoDescMatveev_of_matveev`, `…_of_mr`). The two
  cited Props are not refuted in their elementary ranges:
  `theo:matveev`'s inequality holds for `a ≤ d` by integrality (`citedStepsMatveev_of_le`), and
  `theo:mr`'s conclusion holds for `a < 2^{775}` (`citedStepsMR_of_lt`).
* **`prop:proposition`, Finding 3: for `x < 0` it holds with no computer check and no `|x| > 1000`.**
  On a cycle `2^{p_n} − 3ⁿ` has the sign of `x`, so `p_n < n log₂ 3` for `x < 0`. With
  `p_n ≥ a + 2(n − a)` (`citedSteps_two_mul_le`) this gives `#{a_i = 1} > (2 − log₂ 3) n > α n`
  (`prop_proposition_neg`). This confirms the planner's [r]. At `−1`, at `−5` and `−7` (the two
  points of `(−5, −7)`) and at `−17` the counts are `1`, `1`, `1` and `5`, each above `α n`
  (`prop_proposition_instances`). The check of l.201
  matters for `x > 0` only. Its inference « `|x| > 10^{10}` » is valid only there: over the negative
  integers « the conjecture » is false (the cycles above).
* **`prop:proposition` for `x > 0`.** From the true form of `cor:bounds`,
  `#{a_i = 1} ≥ n (2 − log₂ 3 − log₂(1 + 1/(3 min)))` on every cycle (`prop_proposition_min`).
  With every point at least `10^{10}`, this exceeds `α n`, since
  `log₂(1 + 1/(3 · 10^{10})) < 10^{−10}` (`prop_proposition_pos_of_ge`). The check gives that bound
  for every positive cycle other than `(1)` (`citedStepsCycleCheck_of_check`). So, from the check,
  the printed statement holds (`prop_proposition_of_check`), and so does the stronger one with
  `x ≠ 1` for `|x| > 1000` (`prop_proposition_ne_one`). The hypothesis cannot be dropped for
  `x > 0`: at `x = 1` the count is `0 < α` (`prop_proposition_unbounded_false`).
* **Finding 4 (l.202–204): the proof's two slips are harmless.** It uses `cor:bounds` as printed,
  which is false (OQ-54 (c)); the true form has `log₂(1 + 1/(3 min))`. And it writes `log`, the
  natural logarithm elsewhere in the paper (l.114), where `cor:bounds` has `log₂`. The true form's
  `log₂(1 + 1/(3 min))` and the proof's natural `log(1 + 1/|x|)` are both below `10^{−10}` once every
  point exceeds `10^{10}`; the printed `log₂(1 + 1/|x|)` is not (`log₂(1 + 10^{−10}) ≈ 1.44 · 10^{−10}`),
  so the step closes with the natural log or with the true form, which is the one used here.
* **`α > 0.415037499` (l.197) holds**, from `3^{79335} < 2^{125743}` checked in the kernel
  (`citedStepsAlpha_gt`): `2 − log₂ 3 > 32927/79335`, so `α = 2 − log₂ 3 − 10^{−10} > 0.41503749911`, a
  margin of about `1.1 · 10^{−10}`.
* `T`, `a`, `p` are the total maps of `Syracuse.Base`; over `ℤ` they are the paper's
  (`not_isUnit_three_int`). `theo:mr` and `theo:matveev` are not labels of this file; their rows are
  T-syr-cited's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Syracuse

open Finset

/-! ### The cited inputs, as statements (never assumed, never axioms) -/

/-- `d = 3.5 · 10⁶` of `theo:matveev` (l.159), an integer. -/
def citedStepsD : ℕ := 3500000

/-- `theo:matveev` (l.156–159) as printed: for `a, b ∈ ℕ*` with `2^a > 3^b`,
`2^a − 3^b ≥ 2^a / (e^d a^d)`, `d = 3.5 · 10⁶`. A hypothesis of the theorems below, never an axiom. -/
def CitedStepsMatveev : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → (3 : ℝ) ^ b < 2 ^ a →
    (2 : ℝ) ^ a / (Real.exp citedStepsD * (a : ℝ) ^ citedStepsD) ≤ 2 ^ a - 3 ^ b

/-- `theo:mr` (l.145–148, cited as MR1074572) as printed: for `a, b ∈ ℤ` and `δ ≥ 1`,
`|a log 2 − b log 3| ≤ e^{−a/δ}` implies `a < 2^{800} log(3)^{25} δ^{25}`. A hypothesis, never an
axiom. -/
def CitedStepsMR : Prop :=
  ∀ (a b : ℤ) (δ : ℝ), 1 ≤ δ →
    |(a : ℝ) * Real.log 2 - b * Real.log 3| ≤ Real.exp (-(a : ℝ) / δ) →
      (a : ℝ) < 2 ^ 800 * Real.log 3 ^ 25 * δ ^ 25

/-- The computer check of l.201, first clause: « the conjecture has been tested for all integers
lesser than `10^{10}` », for `T` on the odd integers: every odd `0 < y < 10^{10}` reaches `1`. -/
def CitedStepsCheck : Prop :=
  ∀ y : ℤ, Odd y → 0 < y → y < 10 ^ 10 → ∃ k : ℕ, T^[k] y = 1

/-- What l.201 draws from the check: a positive cycle is the cycle `(1)` or lies above `10^{10}`
(`citedStepsCycleCheck_of_check`). -/
def CitedStepsCycleCheck : Prop :=
  ∀ x : ℤ, 0 < x → ∀ n : ℕ, 0 < n → T^[n] x = x → x = 1 ∨ 10 ^ 10 ≤ x

/-- `theo:matveev`'s inequality holds by integrality when `a ≤ d`: there `2^a ≤ e^d`, and
`2^a − 3^b ≥ 1`. -/
theorem citedStepsMatveev_of_le {a b : ℕ} (ha : 0 < a) (had : a ≤ citedStepsD)
    (h3 : (3 : ℝ) ^ b < 2 ^ a) :
    (2 : ℝ) ^ a / (Real.exp citedStepsD * (a : ℝ) ^ citedStepsD) ≤ 2 ^ a - 3 ^ b := by
  have hint : (1 : ℝ) ≤ 2 ^ a - 3 ^ b := by
    have h : (3 : ℤ) ^ b < 2 ^ a := by exact_mod_cast h3
    have h' : (3 : ℤ) ^ b + 1 ≤ 2 ^ a := h
    have h'' : ((3 : ℤ) ^ b + 1 : ℤ) ≤ ((2 : ℤ) ^ a : ℤ) := h'
    have : (3 : ℝ) ^ b + 1 ≤ 2 ^ a := by exact_mod_cast h''
    linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h2a : (2 : ℝ) ^ a ≤ Real.exp citedStepsD := by
    calc (2 : ℝ) ^ a ≤ Real.exp 1 ^ a := pow_le_pow_left₀ (by norm_num) he a
      _ = Real.exp a := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp citedStepsD := Real.exp_le_exp.2 (by exact_mod_cast had)
  have hpow : (1 : ℝ) ≤ (a : ℝ) ^ citedStepsD := one_le_pow₀ (by exact_mod_cast ha)
  have hden : 0 < Real.exp citedStepsD * (a : ℝ) ^ citedStepsD := by positivity
  refine le_trans ?_ hint
  rw [div_le_one hden]
  nlinarith [Real.exp_pos (citedStepsD : ℝ)]

/-- `theo:mr`'s conclusion holds whenever `a < 2^{775}`: there `2^{800} log(3)^{25} δ^{25} ≥ 2^{775}`. -/
theorem citedStepsMR_of_lt {a : ℤ} {δ : ℝ} (hδ : 1 ≤ δ) (ha : (a : ℝ) < 2 ^ 775) :
    (a : ℝ) < 2 ^ 800 * Real.log 3 ^ 25 * δ ^ 25 := by
  have hl : (1 : ℝ) / 2 ≤ Real.log 3 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at this ⊢
    linarith
  have h1 : ((1 : ℝ) / 2) ^ 25 ≤ Real.log 3 ^ 25 := pow_le_pow_left₀ (by norm_num) hl 25
  have h2 : (1 : ℝ) ≤ δ ^ 25 := one_le_pow₀ hδ
  have h3 : (2 : ℝ) ^ 775 = 2 ^ 800 * ((1 : ℝ) / 2) ^ 25 := by
    rw [div_pow, one_pow, show (800 : ℕ) = 775 + 25 from rfl, pow_add]
    field_simp
  have h4 : (0 : ℝ) ≤ 2 ^ 800 * Real.log 3 ^ 25 := by positivity
  calc (a : ℝ) < 2 ^ 775 := ha
    _ ≤ 2 ^ 800 * Real.log 3 ^ 25 := by rw [h3]; gcongr
    _ ≤ 2 ^ 800 * Real.log 3 ^ 25 * δ ^ 25 := le_mul_of_one_le_right h4 h2

/-! ### `GCD(A_i(Γ) : i ∈ ℤ)` and `|2^{p_n} − 3ⁿ|` -/

/-- Two `n`-periodic functions on `ℤ` that agree on `ℕ` are equal. -/
theorem citedSteps_periodic_ext {β : Type*} {f g : ℤ → β} {n : ℕ} (hn : 0 < n)
    (hf : Function.Periodic f n) (hg : Function.Periodic g n) (h : ∀ k : ℕ, f k = g k) :
    f = g := by
  funext i
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  rw [periodic_emod hf i, periodic_emod hg i, show i % (n : ℤ) = (((i % n).toNat : ℕ) : ℤ) from
    (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm]
  exact h _

/-- The GCD of one period of an `n`-periodic family divides every term over `ℤ`: it is the GCD over
`i ∈ ℤ` (the converse, a common divisor of all terms divides it, is `Finset.dvd_gcd`). -/
theorem citedSteps_gcd_dvd {g : ℤ → ℕ} {n : ℕ} (hn : 0 < n) (hg : Function.Periodic g n) (i : ℤ) :
    (range n).gcd (fun u : ℕ => (g u : ℤ)) ∣ (g i : ℤ) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  rw [periodic_emod hg i, show i % (n : ℤ) = (((i % n).toNat : ℕ) : ℤ) from
      (Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')).symm]
  exact Finset.gcd_dvd (f := fun u : ℕ => (g u : ℤ))
    (Finset.mem_range.2 (by have := Int.emod_lt_of_pos i hn'; omega))

/-- `2^{p_n(x)} − 3ⁿ` divides `A_u^n(α)` and `A'^n_u(α)` for every `u ∈ ℤ`, for every `n`-periodic
shift `α` of `a(x)` (both index conventions: `c = 0` is l.62, `c = 1` is l.71). -/
theorem citedSteps_dvd_Aun {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) {c : ℤ} (hα : ∀ k : ℕ, α (k + c) = a k x) (u : ℤ) :
    (2 : ℤ) ^ p n x - 3 ^ n ∣ (Aun n u α : ℤ) ∧ (2 : ℤ) ^ p n x - 3 ^ n ∣ (AunAlt n u α : ℤ) := by
  set γ : ℤ → ℕ := fun j => α (j + c) with hγdef
  have hγper : Function.Periodic γ n := fun j => by
    simp only [hγdef]; rw [show j + n + c = (j + c) + n by ring, hper]
  have hγ : ∀ k : ℕ, γ k = a k x := fun k => hα k
  have hA : Aun n u α = Aun n (u - c) γ := by
    unfold Aun
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hγdef]
    congr 2
    ring
  have hA' : AunAlt n u α = AunAlt n (u - c) γ := by
    unfold AunAlt
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hγdef]
    congr 2
    ring
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hmc : ((((u - c) % n).toNat : ℕ) : ℤ) = (u - c) % n :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')
  have e1 : Aun n (u - c) γ = Aun n (((u - c) % n).toNat : ℕ) γ := by
    rw [hmc]; exact periodic_emod (Aun_periodic hγper) (u - c)
  have e2 : AunAlt n (u - c) γ = AunAlt n (((u - c) % n).toNat : ℕ) γ := by
    rw [hmc]; exact periodic_emod (AunAlt_periodic hγper) (u - c)
  obtain ⟨h1, h2⟩ := Aun_cast_of_cycle (A := ℤ) hx γ hγ ((u - c) % n).toNat
  refine ⟨?_, ?_⟩
  · rw [hA, e1, h1]; exact dvd_mul_right _ _
  · rw [hA', e2, h2]; exact dvd_mul_right _ _

/-- On every cycle of `ℤ`, `|2^{p_n} − 3ⁿ|` is at most the GCD of the `A_i`, for both readings of
OQ-43 and every index convention. -/
theorem citedSteps_abs_le_gcd {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {α : ℤ → ℕ}
    (hper : Function.Periodic α n) {c : ℤ} (hα : ∀ k : ℕ, α (k + c) = a k x) :
    |(2 : ℤ) ^ p n x - 3 ^ n| ≤ (range n).gcd (fun u : ℕ => (Aun n u α : ℤ)) ∧
      |(2 : ℤ) ^ p n x - 3 ^ n| ≤ (range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ)) := by
  have hd := citedSteps_dvd_Aun hn hx hper hα
  have hpos : ∀ f : ℕ → ℕ, 0 < f 0 → 0 < (range n).gcd (fun u : ℕ => (f u : ℤ)) := by
    intro f hf
    have hG0 : 0 ≤ (range n).gcd (fun u : ℕ => (f u : ℤ)) :=
      Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    refine lt_of_le_of_ne hG0 (fun h => ?_)
    have := Finset.gcd_eq_zero_iff.1 h.symm 0 (Finset.mem_range.2 hn)
    simp only [Nat.cast_eq_zero] at this
    omega
  have hA0 : 0 < Aun n ((0 : ℕ) : ℤ) α := by
    unfold Aun
    exact Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.2 hn⟩
  have hA0' : 0 < AunAlt n ((0 : ℕ) : ℤ) α := by
    unfold AunAlt
    exact Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.2 hn⟩
  refine ⟨Int.le_of_dvd (hpos (fun u => Aun n u α) hA0)
      ((abs_dvd _ _).2 (Finset.dvd_gcd (fun u _ => (hd u).1))),
    Int.le_of_dvd (hpos (fun u => AunAlt n u α) hA0')
      ((abs_dvd _ _).2 (Finset.dvd_gcd (fun u _ => (hd u).2)))⟩

/-! ### Each cycle is determined by its sequence `a` (lem:base), and the candidates -/

/-- `∑_{k<n} 2^{∑_{j<k} f_j} 3^{n−1−k}`: the right side of `lem:base` for exponents `f`. -/
def citedStepsRhs (n : ℕ) (f : ℕ → ℕ) : ℤ :=
  ∑ k ∈ range n, 2 ^ (∑ j ∈ range k, f j) * 3 ^ (n - 1 - k)

/-- `q : Fin n → ℕ` read as a sequence on `ℕ` (zero from `n` on). -/
def citedStepsExt (n : ℕ) (q : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : j < n then q ⟨j, h⟩ else 0

/-- The candidates with `p_n ≤ B`: for each `n ≤ B` and each `(a_0, …, a_{n−1}) ∈ ⟦1, B⟧ⁿ`, the
pair `(x, n)` with `x = RHS / (2^{p_n} − 3ⁿ)` (`lem:base`). A computable `Finset`. -/
def citedStepsCandidates (B : ℕ) : Finset (ℤ × ℕ) :=
  (range (B + 1)).biUnion fun n =>
    (Fintype.piFinset fun _ : Fin n => Icc 1 B).image fun q =>
      (citedStepsRhs n (citedStepsExt n q) / (2 ^ (∑ j ∈ range n, citedStepsExt n q j) - 3 ^ n), n)

/-- On a cycle, `x (2^{p_n} − 3ⁿ)` is the right side of `lem:base` for `a(x)`. -/
theorem citedSteps_mul_eq_rhs {x : ℤ} {n : ℕ} (hx : T^[n] x = x) :
    x * ((2 : ℤ) ^ p n x - 3 ^ n) = citedStepsRhs n (fun k => a k x) := by
  have h := base x n
  rw [hx] at h
  show x * ((2 : ℤ) ^ p n x - 3 ^ n) = ∑ k ∈ range n, (2 : ℤ) ^ p k x * 3 ^ (n - 1 - k)
  linear_combination h

/-- **At most one cycle per sequence `a`** (l.167): two `n`-cycles with the same `a_0, …, a_{n−1}`
have the same base point. -/
theorem citedSteps_cycle_unique {x y : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    (hy : T^[n] y = y) (h : ∀ k < n, a k x = a k y) : x = y := by
  have hp : p n x = p n y := Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.1 hk))
  have hr : citedStepsRhs n (fun k => a k x) = citedStepsRhs n (fun k => a k y) := by
    unfold citedStepsRhs
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hs : ∑ j ∈ range k, a j x = ∑ j ∈ range k, a j y :=
      Finset.sum_congr rfl (fun j hj => h j (by
        have := Finset.mem_range.1 hk; have := Finset.mem_range.1 hj; omega))
    simp only [hs]
  have e1 := citedSteps_mul_eq_rhs hx
  rw [hr, ← citedSteps_mul_eq_rhs hy, hp] at e1
  exact mul_right_cancel₀ (two_pow_p_sub_three_pow_ne_zero hn hy) e1

/-- `n ≤ p_n(x)` on every cycle (`a_k ≥ 1`), and `1 ≤ a_k(x) ≤ p_n(x)` for `k < n`. -/
theorem citedSteps_le_p {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    n ≤ p n x ∧ ∀ k < n, 1 ≤ a k x ∧ a k x ≤ p n x := by
  have h1 : ∀ k : ℕ, 1 ≤ a k x := fun k => by
    have := one_le_of_cycle hn hx (aPer_periodic n x) (aPer_natCast hx) k
    rwa [aPer_natCast hx] at this
  refine ⟨?_, fun k hk => ⟨h1 k, ?_⟩⟩
  · show n ≤ ∑ k ∈ range n, a k x
    calc n = ∑ _k ∈ range n, 1 := by simp
      _ ≤ ∑ k ∈ range n, a k x := Finset.sum_le_sum (fun k _ => h1 k)
  · exact Finset.single_le_sum (f := fun k => a k x) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hk)

/-- Every cycle `(x, n)` of `ℤ` with `p_n(x) ≤ B` is a candidate. -/
theorem mem_citedStepsCandidates {x : ℤ} {n B : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    (hB : p n x ≤ B) : (x, n) ∈ citedStepsCandidates B := by
  obtain ⟨hnp, ha⟩ := citedSteps_le_p hn hx
  unfold citedStepsCandidates
  rw [Finset.mem_biUnion]
  refine ⟨n, Finset.mem_range.2 (by omega), ?_⟩
  rw [Finset.mem_image]
  refine ⟨fun j : Fin n => a (j : ℕ) x, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    exact ⟨(ha j j.2).1, (ha j j.2).2.trans hB⟩
  · have hext : ∀ j < n, citedStepsExt n (fun j : Fin n => a (j : ℕ) x) j = a j x :=
      fun j hj => by simp [citedStepsExt, hj]
    have hsum : ∑ j ∈ range n, citedStepsExt n (fun j : Fin n => a (j : ℕ) x) j = p n x :=
      Finset.sum_congr rfl (fun j hj => hext j (Finset.mem_range.1 hj))
    have hrhs : citedStepsRhs n (citedStepsExt n fun j : Fin n => a (j : ℕ) x) =
        citedStepsRhs n (fun k => a k x) := by
      unfold citedStepsRhs
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hs : ∑ j ∈ range k, citedStepsExt n (fun j : Fin n => a (j : ℕ) x) j =
          ∑ j ∈ range k, a j x :=
        Finset.sum_congr rfl (fun j hj => hext j (by
          have := Finset.mem_range.1 hk; have := Finset.mem_range.1 hj; omega))
      rw [hs]
    rw [hsum, hrhs, ← citedSteps_mul_eq_rhs hx,
      Int.mul_ediv_cancel _ (two_pow_p_sub_three_pow_ne_zero hn hx)]

/-- Finitely many cycles `(x, n)` with `p_n(x)` bounded. -/
theorem citedSteps_finite_of_le (B : ℕ) :
    {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ p q.2 q.1 ≤ B}.Finite :=
  (citedStepsCandidates B).finite_toSet.subset
    (fun _ hq => mem_citedStepsCandidates hq.1 hq.2.1 hq.2.2)

/-- The candidate list is computed by the kernel: `(1, 1)` (`p_1 = 2`), `(−1, 1)` (`p_1 = 1`) and
`(−5, 2)` (`p_2 = 3`) are found by `decide`. -/
theorem citedStepsCandidates_decide :
    ((1 : ℤ), 1) ∈ citedStepsCandidates 2 ∧ ((-1 : ℤ), 1) ∈ citedStepsCandidates 1 ∧
      ((-5 : ℤ), 2) ∈ citedStepsCandidates 3 :=
  ⟨by decide, by decide, by decide⟩

/-- `(−17, 7)` is a candidate for `B = p_7(−17) = 11`. -/
theorem citedStepsCandidates_neg_seventeen : ((-17 : ℤ), 7) ∈ citedStepsCandidates 11 := by
  obtain ⟨hx17, ha17⟩ := cycle_neg_seventeen
  have hp17 : p 7 (-17 : ℤ) = 11 := by
    simp only [p, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [← ha17 0, ← ha17 1, ← ha17 2, ← ha17 3, ← ha17 4, ← ha17 5, ← ha17 6]
    decide
  have h := mem_citedStepsCandidates (x := -17) (n := 7) (B := 11) (by norm_num) hx17 hp17.le
  exact h

/-! ### From a lower bound on `|2^P − 3ⁿ|` to a bound on `P` -/

/-- A lower bound `2^P / (K P^d)` against an upper bound `C 2^{P(1−ε)}` bounds `P` explicitly,
through `exp t ≥ t^{d+1}/(d+1)!`. -/
theorem citedSteps_le_of_lower {K C ε X : ℝ} {d P : ℕ} (hε : 0 < ε) (hP : 1 ≤ P) (hK : 0 < K)
    (hlow : (2 : ℝ) ^ P / (K * (P : ℝ) ^ d) ≤ X) (hup : X ≤ C * (2 : ℝ) ^ ((P : ℝ) * (1 - ε))) :
    (P : ℝ) ≤ C * K * (d + 1).factorial / (ε * Real.log 2) ^ (d + 1) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPd : (0 : ℝ) < (P : ℝ) ^ d := by positivity
  have hKP : 0 < K * (P : ℝ) ^ d := by positivity
  have hA : 0 < (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) := by positivity
  have h1 : (2 : ℝ) ^ P ≤ C * (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) * (K * (P : ℝ) ^ d) := by
    rw [div_le_iff₀ hKP] at hlow
    exact hlow.trans (mul_le_mul_of_nonneg_right hup hKP.le)
  have hsplit : (2 : ℝ) ^ P = (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) * (2 : ℝ) ^ ((P : ℝ) * ε) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
    congr 1
    ring
  have h2 : (2 : ℝ) ^ ((P : ℝ) * ε) ≤ C * K * (P : ℝ) ^ d := by
    rw [hsplit] at h1
    have h1' : (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) * (2 : ℝ) ^ ((P : ℝ) * ε) ≤
        (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) * (C * K * (P : ℝ) ^ d) := by
      calc _ ≤ C * (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) * (K * (P : ℝ) ^ d) := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1' hA
  have hexp : (2 : ℝ) ^ ((P : ℝ) * ε) = Real.exp ((P : ℝ) * ε * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have h3 := Real.pow_div_factorial_le_exp ((P : ℝ) * ε * Real.log 2) (by positivity) (d + 1)
  rw [← hexp] at h3
  have hfact : (0 : ℝ) < (d + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have h4 : ((P : ℝ) * ε * Real.log 2) ^ (d + 1) ≤ (d + 1).factorial * (C * K * (P : ℝ) ^ d) := by
    rw [div_le_iff₀ hfact] at h3
    calc _ ≤ _ := h3
      _ ≤ C * K * (P : ℝ) ^ d * (d + 1).factorial := mul_le_mul_of_nonneg_right h2 hfact.le
      _ = _ := by ring
  have h5 : (P : ℝ) * (ε * Real.log 2) ^ (d + 1) ≤ (d + 1).factorial * (C * K) := by
    have e : ((P : ℝ) * ε * Real.log 2) ^ (d + 1) =
        (P : ℝ) ^ d * ((P : ℝ) * (ε * Real.log 2) ^ (d + 1)) := by ring
    have e2 : ((d + 1).factorial : ℝ) * (C * K * (P : ℝ) ^ d) =
        (P : ℝ) ^ d * ((d + 1).factorial * (C * K)) := by ring
    rw [e, e2] at h4
    exact le_of_mul_le_mul_left h4 hPd
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The explicit bound on `|Γ|` from `theo:matveev`: `C e^d (d+1)! / (ε log 2)^{d+1}`. -/
noncomputable def citedStepsBoundMatveev (C ε : ℝ) : ℝ :=
  C * Real.exp citedStepsD * (citedStepsD + 1).factorial / (ε * Real.log 2) ^ (citedStepsD + 1)

/-- `δ = max(1, 2/(ε log 2))`, the `δ` handed to `theo:mr`. -/
noncomputable def citedStepsDelta (ε : ℝ) : ℝ := max 1 (2 / (ε * Real.log 2))

/-- The explicit bound on `|Γ|` from `theo:mr`: `max(2 log₂(2C)/ε, 2^{800} log(3)^{25} δ^{25})`. -/
noncomputable def citedStepsBoundMR (C ε : ℝ) : ℝ :=
  max (2 * Real.logb 2 (2 * C) / ε) (2 ^ 800 * Real.log 3 ^ 25 * citedStepsDelta ε ^ 25)

/-- From `theo:matveev`: `3ⁿ < 2^P` and `2^P − 3ⁿ ≤ C 2^{P(1−ε)}` give
`P ≤ citedStepsBoundMatveev C ε`. -/
theorem citedSteps_le_of_matveev (hM : CitedStepsMatveev) {C ε : ℝ} (hε : 0 < ε) {P N : ℕ}
    (hN : 0 < N) (h3 : (3 : ℝ) ^ N < 2 ^ P)
    (hup : (2 : ℝ) ^ P - 3 ^ N ≤ C * (2 : ℝ) ^ ((P : ℝ) * (1 - ε))) :
    (P : ℝ) ≤ citedStepsBoundMatveev C ε := by
  have hP : 1 ≤ P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · subst h0
      have : (1 : ℝ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
      norm_num at h3
      linarith
    · exact h0
  exact citedSteps_le_of_lower hε hP (Real.exp_pos _) (hM P N hP hN h3) hup

/-- `|log u| ≤ 2 |1 − u|` when `|1 − u| ≤ 1/2`. -/
theorem citedSteps_abs_log_le {u : ℝ} (hu : |1 - u| ≤ 1 / 2) : |Real.log u| ≤ 2 * |1 - u| := by
  have hu0 : 1 / 2 ≤ u := by rw [abs_le] at hu; linarith
  have hupos : 0 < u := by linarith
  rcases le_or_gt 1 u with h1 | h1
  · have hl0 : 0 ≤ Real.log u := Real.log_nonneg h1
    have := Real.log_le_sub_one_of_pos hupos
    rw [abs_of_nonneg hl0, abs_of_nonpos (by linarith : 1 - u ≤ 0)]
    linarith
  · have hl0 : Real.log u < 0 := Real.log_neg hupos h1
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hupos)
    rw [Real.log_inv] at h
    rw [abs_of_neg hl0, abs_of_pos (by linarith : 0 < 1 - u)]
    have h2 : u⁻¹ - 1 ≤ 2 * (1 - u) := by
      rw [inv_eq_one_div, div_sub_one hupos.ne', div_le_iff₀ hupos]
      nlinarith
    linarith

/-- From `theo:mr`, either sign: `|2^P − 3ⁿ| ≤ C 2^{P(1−ε)}` gives `P ≤ citedStepsBoundMR C ε`. For
`P ≥ 2 log₂(2C)/ε`, `|P log 2 − n log 3| ≤ 2^{−Pε/2} ≤ e^{−P/δ}`, and `theo:mr` applies. -/
theorem citedSteps_le_of_mr (hR : CitedStepsMR) {C ε : ℝ} (hε : 0 < ε) {P N : ℕ}
    (hup : |(2 : ℝ) ^ P - 3 ^ N| ≤ C * (2 : ℝ) ^ ((P : ℝ) * (1 - ε))) :
    (P : ℝ) ≤ citedStepsBoundMR C ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ1 : 1 ≤ citedStepsDelta ε := le_max_left _ _
  have hδ2 : 2 / (ε * Real.log 2) ≤ citedStepsDelta ε := le_max_right _ _
  unfold citedStepsBoundMR
  rcases lt_or_ge (P : ℝ) (2 * Real.logb 2 (2 * C) / ε) with hsmall | hlarge
  · exact le_max_of_le_left hsmall.le
  refine le_max_of_le_right (le_of_lt ?_)
  have hC : 2 * C ≤ (2 : ℝ) ^ ((P : ℝ) * ε / 2) := by
    rcases le_or_gt (2 * C) 0 with h | h
    · exact h.trans (by positivity)
    · have hlog : Real.logb 2 (2 * C) ≤ (P : ℝ) * ε / 2 := by
        rw [div_le_iff₀ hε] at hlarge
        linarith
      calc 2 * C = (2 : ℝ) ^ Real.logb 2 (2 * C) :=
            (Real.rpow_logb (by norm_num) (by norm_num) h).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have h2P : (0 : ℝ) < 2 ^ P := by positivity
  set s : ℝ := (2 : ℝ) ^ (-((P : ℝ) * ε / 2)) with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by have : 0 ≤ (P : ℝ) * ε / 2 := by positivity
        linarith)
  have has : (2 : ℝ) ^ ((P : ℝ) * ε / 2) * s = 1 := by
    rw [hs, ← Real.rpow_add (by norm_num)]
    simp
  have hsplit : (2 : ℝ) ^ ((P : ℝ) * (1 - ε)) = 2 ^ P * (s * s) := by
    rw [hs, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  set u : ℝ := 3 ^ N / 2 ^ P with hu
  have hupos : 0 < u := by positivity
  have hη : |1 - u| ≤ s / 2 := by
    have e : 1 - u = ((2 : ℝ) ^ P - 3 ^ N) / 2 ^ P := by
      rw [hu]
      field_simp
    rw [e, abs_div, abs_of_pos h2P, div_le_iff₀ h2P]
    rw [hsplit] at hup
    have hCs : C * s ≤ 1 / 2 := by nlinarith
    calc |(2 : ℝ) ^ P - 3 ^ N| ≤ C * (2 ^ P * (s * s)) := hup
      _ = (C * s) * (2 ^ P * s) := by ring
      _ ≤ (1 / 2) * (2 ^ P * s) := mul_le_mul_of_nonneg_right hCs (by positivity)
      _ = s / 2 * 2 ^ P := by ring
  have hlogu := citedSteps_abs_log_le (hη.trans (by linarith))
  have hlu : Real.log u = N * Real.log 3 - P * Real.log 2 := by
    rw [hu, Real.log_div (by positivity) h2P.ne', Real.log_pow, Real.log_pow]
  have hΛ : |(P : ℝ) * Real.log 2 - N * Real.log 3| ≤ s := by
    rw [abs_sub_comm, ← hlu]
    linarith
  have hsexp : s ≤ Real.exp (-(P : ℝ) / citedStepsDelta ε) := by
    rw [hs, Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.2 ?_
    have hδpos : 0 < citedStepsDelta ε := by linarith
    have hinv : 1 / citedStepsDelta ε ≤ ε * Real.log 2 / 2 := by
      rw [div_le_iff₀ hδpos]
      rw [div_le_iff₀ (by positivity)] at hδ2
      linarith
    have hP0 : (0 : ℝ) ≤ P := by positivity
    have : (P : ℝ) / citedStepsDelta ε ≤ (P : ℝ) * (ε * Real.log 2 / 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinv hP0
    rw [neg_div]
    nlinarith
  have := hR P N (citedStepsDelta ε) hδ1 (by push_cast; exact hΛ.trans hsexp)
  push_cast at this
  exact this

/-! ### `cor:property_defined_cycles_gcd` -/

/-- The corollary over `ℤ`, effective, from `theo:mr`, with the hypothesis on `|2^{p_n} − 3ⁿ|`
(at most every reading of `GCD(A_i(Γ))`): every `𝒫`-cycle has `n ≤ |Γ| ≤ citedStepsBoundMR C ε`
and is a candidate. -/
theorem property_defined_cycles_gcd_mr_effective (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < n → T^[n] x = x → P x n →
      (((|(2 : ℤ) ^ p n x - 3 ^ n| : ℤ)) : ℝ) ≤ C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMR C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMR C ε⌋₊ := by
  have hb : (p n x : ℝ) ≤ citedStepsBoundMR C ε := by
    refine citedSteps_le_of_mr hR hε (N := n) ?_
    have := h x n hn hx hPx
    push_cast at this
    exact this
  exact ⟨(citedSteps_le_p hn hx).1, hb, mem_citedStepsCandidates hn hx (Nat.le_floor hb)⟩

/-- The corollary over `ℤ`, from `theo:mr`, the hypothesis on `|2^{p_n} − 3ⁿ|`. -/
theorem property_defined_cycles_gcd_mr (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < n → T^[n] x = x → P x n →
      (((|(2 : ℤ) ^ p n x - 3 ^ n| : ℤ)) : ℝ) ≤ C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine (citedStepsCandidates ⌊citedStepsBoundMR C ε⌋₊).finite_toSet.subset ?_
  rintro ⟨x, n⟩ ⟨hn, hx, hPx⟩
  exact (property_defined_cycles_gcd_mr_effective hR P hε hC hn hx hPx).2.2

/-- **`cor:property_defined_cycles_gcd` over `ℤ`, from `theo:mr`**, the GCD of the printed
`A_u^n` (`def:define_n__n_`), in any index convention. -/
theorem property_defined_cycles_gcd_mr_aun (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (Aun n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine property_defined_cycles_gcd_mr hR P ⟨ε, hε, C, fun x n hn hx hPx => ?_⟩
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := hC x n hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).1) hb

/-- **`cor:property_defined_cycles_gcd` over `ℤ`, from `theo:mr`**, the GCD of OQ-43's `A'^n_u`. -/
theorem property_defined_cycles_gcd_mr_alt (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine property_defined_cycles_gcd_mr hR P ⟨ε, hε, C, fun x n hn hx hPx => ?_⟩
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := hC x n hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).2) hb

/-- **The effective clause over `ℤ`, from `theo:mr`**, the GCD of the printed `A_u^n`: every
`𝒫`-cycle has `|Γ| ≤ citedStepsBoundMR C ε` and is a candidate. -/
theorem property_defined_cycles_gcd_mr_effective_aun (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (Aun n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMR C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMR C ε⌋₊ := by
  refine property_defined_cycles_gcd_mr_effective hR P hε (fun x n hn hx hPx => ?_) hn hx hPx
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := h x n hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).1) hb

/-- **The effective clause over `ℤ`, from `theo:mr`**, the GCD of OQ-43's `A'^n_u`. -/
theorem property_defined_cycles_gcd_mr_effective_alt (hR : CitedStepsMR) (P : ℤ → ℕ → Prop)
    {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMR C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMR C ε⌋₊ := by
  refine property_defined_cycles_gcd_mr_effective hR P hε (fun x n hn hx hPx => ?_) hn hx hPx
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := h x n hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).2) hb

/-- The corollary on the positive cycles, effective, from `theo:matveev` (which as printed covers
`2^a > 3^b` only, i.e. `x > 0`). -/
theorem property_defined_cycles_gcd_matveev_effective (hM : CitedStepsMatveev)
    (P : ℤ → ℕ → Prop) {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      (((|(2 : ℤ) ^ p n x - 3 ^ n| : ℤ)) : ℝ) ≤ C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMatveev C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMatveev C ε⌋₊ := by
  have hsign := two_pow_p_sub_three_pow_mul_pos hn hx
  have hD : (0 : ℤ) < 2 ^ p n x - 3 ^ n := pos_of_mul_pos_left hsign hx0.le
  have h3 : (3 : ℝ) ^ n < 2 ^ p n x := by
    have : (3 : ℤ) ^ n < 2 ^ p n x := by linarith
    exact_mod_cast this
  have hb : (p n x : ℝ) ≤ citedStepsBoundMatveev C ε := by
    refine citedSteps_le_of_matveev hM hε hn h3 ?_
    have := h x n hx0 hn hx hPx
    rw [abs_of_pos hD] at this
    push_cast at this
    exact this
  exact ⟨(citedSteps_le_p hn hx).1, hb, mem_citedStepsCandidates hn hx (Nat.le_floor hb)⟩

/-- The corollary on the positive cycles, from `theo:matveev`, the hypothesis on
`|2^{p_n} − 3ⁿ|`. -/
theorem property_defined_cycles_gcd_matveev (hM : CitedStepsMatveev) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      (((|(2 : ℤ) ^ p n x - 3 ^ n| : ℤ)) : ℝ) ≤ C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.1 ∧ 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine (citedStepsCandidates ⌊citedStepsBoundMatveev C ε⌋₊).finite_toSet.subset ?_
  rintro ⟨x, n⟩ ⟨hx0, hn, hx, hPx⟩
  exact (property_defined_cycles_gcd_matveev_effective hM P hε hC hx0 hn hx hPx).2.2

/-- **`cor:property_defined_cycles_gcd` on the positive cycles, from `theo:matveev`**, the GCD of
the printed `A_u^n`, in any index convention. -/
theorem property_defined_cycles_gcd_matveev_aun (hM : CitedStepsMatveev) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (Aun n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.1 ∧ 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine property_defined_cycles_gcd_matveev hM P ⟨ε, hε, C, fun x n hx0 hn hx hPx => ?_⟩
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := hC x n hx0 hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).1) hb

/-- **`cor:property_defined_cycles_gcd` on the positive cycles, from `theo:matveev`**, the GCD of
OQ-43's `A'^n_u`. -/
theorem property_defined_cycles_gcd_matveev_alt (hM : CitedStepsMatveev) (P : ℤ → ℕ → Prop)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε))) :
    {q : ℤ × ℕ | 0 < q.1 ∧ 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ P q.1 q.2}.Finite := by
  obtain ⟨ε, hε, C, hC⟩ := h
  refine property_defined_cycles_gcd_matveev hM P ⟨ε, hε, C, fun x n hx0 hn hx hPx => ?_⟩
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := hC x n hx0 hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).2) hb

/-- **The effective clause on the positive cycles, from `theo:matveev`**, the GCD of the printed
`A_u^n`. -/
theorem property_defined_cycles_gcd_matveev_effective_aun (hM : CitedStepsMatveev)
    (P : ℤ → ℕ → Prop) {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (Aun n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMatveev C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMatveev C ε⌋₊ := by
  refine property_defined_cycles_gcd_matveev_effective hM P hε
    (fun x n hx0 hn hx hPx => ?_) hx0 hn hx hPx
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := h x n hx0 hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).1) hb

/-- **The effective clause on the positive cycles, from `theo:matveev`**, the GCD of OQ-43's
`A'^n_u`. -/
theorem property_defined_cycles_gcd_matveev_effective_alt (hM : CitedStepsMatveev)
    (P : ℤ → ℕ → Prop) {ε C : ℝ} (hε : 0 < ε)
    (h : ∀ x n, 0 < x → 0 < n → T^[n] x = x → P x n →
      ∃ α : ℤ → ℕ, Function.Periodic α n ∧ (∃ c : ℤ, ∀ k : ℕ, α (k + c) = a k x) ∧
        ((((range n).gcd (fun u : ℕ => (AunAlt n u α : ℤ))) : ℤ) : ℝ) ≤
          C * (2 : ℝ) ^ ((p n x : ℝ) * (1 - ε)))
    {x : ℤ} (hx0 : 0 < x) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) (hPx : P x n) :
    n ≤ p n x ∧ (p n x : ℝ) ≤ citedStepsBoundMatveev C ε ∧
      (x, n) ∈ citedStepsCandidates ⌊citedStepsBoundMatveev C ε⌋₊ := by
  refine property_defined_cycles_gcd_matveev_effective hM P hε
    (fun x n hx0 hn hx hPx => ?_) hx0 hn hx hPx
  obtain ⟨α, hper, ⟨c, hα⟩, hb⟩ := h x n hx0 hn hx hPx
  exact le_trans (by exact_mod_cast (citedSteps_abs_le_gcd hn hx hper hα).2) hb

/-! ### The corollary applied: § 3's two bounds, and the GCDs at the known cycles -/

/-- `aPer 7 (−17)` is the sequence `(1, 1, 1, 2, 1, 1, 4)` of the cycle of `−17`. -/
theorem citedSteps_aPer_neg_seventeen : aPer 7 (-17 : ℤ) = seq17 :=
  citedSteps_periodic_ext (by norm_num) (aPer_periodic 7 (-17)) seq17_periodic
    (fun k => by rw [aPer_natCast cycle_neg_seventeen.1, cycle_neg_seventeen.2 k])

/-- With `𝒫` = « exactly two descending indices per period », T-syr-two-descents's bound
(`twoDesc_corollary_hyp`) is the corollary's hypothesis, with `ε₀` and `C = 2`: from `theo:mr`,
finitely many cycles of `ℤ` have two descending indices per period. -/
theorem citedSteps_twoDesc_finite (hR : CitedStepsMR) :
    {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧ twoDescCount q.2 (aPer q.2 q.1) = 2}.Finite := by
  refine property_defined_cycles_gcd_mr hR (fun x n => twoDescCount n (aPer n x) = 2)
    ⟨twoDescEps, twoDescEps_pos, 2, fun x n hn hx hP => ?_⟩
  have := twoDesc_corollary_hyp.2 x n hn hx (aPer n x) (aPer_periodic n x) (aPer_natCast hx) hP
  rwa [corGcdAlt_of_cycle hn hx (aPer_periodic n x) (aPer_natCast hx)] at this

/-- The cycle of `−17` has two descending indices per period: the finite set above is not empty. -/
theorem citedSteps_twoDesc_neg_seventeen :
    ((-17 : ℤ), 7) ∈ {q : ℤ × ℕ | 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧
      twoDescCount q.2 (aPer q.2 q.1) = 2} :=
  ⟨by norm_num, cycle_neg_seventeen.1, by
    show twoDescCount 7 (aPer 7 (-17 : ℤ)) = 2
    rw [citedSteps_aPer_neg_seventeen]
    exact twoDescCount_seq17.1⟩

/-- T-syr-two-descents's hypothesis `TwoDescMatveev B` (the corollary to Matveev's theorem in the
form l.326 uses) follows from `theo:matveev` as printed, at an explicit `B`. -/
theorem citedSteps_twoDescMatveev_of_matveev (hM : CitedStepsMatveev) :
    TwoDescMatveev ⌊citedStepsBoundMatveev 2 twoDescEps⌋₊ :=
  fun _ _ hn h3 hb => Nat.le_floor (citedSteps_le_of_matveev hM twoDescEps_pos hn h3 hb)

/-- The same from `theo:mr`. -/
theorem citedSteps_twoDescMatveev_of_mr (hR : CitedStepsMR) :
    TwoDescMatveev ⌊citedStepsBoundMR 2 twoDescEps⌋₊ := by
  intro P n _ h3 hb
  refine Nat.le_floor (citedSteps_le_of_mr hR twoDescEps_pos (N := n) ?_)
  rwa [abs_of_pos (by linarith)]

/-- With `𝒫` = « exactly one descending index per period », T-syr-steiner's bound
(`steiner_corollary_hypothesis`) is the corollary's hypothesis on the positive cycles: from
`theo:matveev`, finitely many positive cycles have one descending index per period (l.302). -/
theorem citedSteps_steiner_finite (hM : CitedStepsMatveev) :
    {q : ℤ × ℕ | 0 < q.1 ∧ 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧
      ((range q.2).filter (fun i : ℕ => 1 < aPer q.2 q.1 i)).card = 1}.Finite := by
  obtain ⟨ε, hε, -, C, hC⟩ := steiner_corollary_hypothesis
  refine property_defined_cycles_gcd_matveev_alt hM
    (fun x n => ((range n).filter (fun i : ℕ => 1 < aPer n x i)).card = 1)
    ⟨ε, hε, C, fun x n hx0 hn hx hP => ⟨aPer n x, aPer_periodic n x,
      ⟨0, fun k => by rw [add_zero]; exact aPer_natCast hx k⟩,
      (hC x hx0 n hn hx (aPer n x) (aPer_periodic n x) (aPer_natCast hx) hP).1⟩⟩

/-- The cycle `(1)` has one descending index per period: the finite set above is not empty. -/
theorem citedSteps_steiner_one :
    ((1 : ℤ), 1) ∈ {q : ℤ × ℕ | 0 < q.1 ∧ 0 < q.2 ∧ T^[q.2] q.1 = q.1 ∧
      ((range q.2).filter (fun i : ℕ => 1 < aPer q.2 q.1 i)).card = 1} := by
  refine ⟨by norm_num, by norm_num, T_iterate_one_int 1, ?_⟩
  show ((range 1).filter (fun i : ℕ => 1 < aPer 1 (1 : ℤ) i)).card = 1
  rw [Finset.filter_congr (q := fun _ : ℕ => True) (fun i _ => by
    rw [aPer_natCast (T_iterate_one_int 1) i, a_one_int]; simp)]
  simp

/-- The GCDs at the cycle of `−17`: `|2^{p_7} − 3⁷| = 139`, the GCD of OQ-43's `A'_u` is `139`, that
of the printed `A_u` is `278`; the inequality of `citedSteps_abs_le_gcd` is strict for the printed
reading. -/
theorem citedSteps_gcd_instances :
    |(2 : ℤ) ^ p 7 (-17 : ℤ) - 3 ^ 7| = 139 ∧
      (range 7).gcd (fun u : ℕ => (AunAlt 7 u (aPer 7 (-17 : ℤ)) : ℤ)) = 139 ∧
      (range 7).gcd (fun u : ℕ => (Aun 7 u (aPer 7 (-17 : ℤ)) : ℤ)) = 278 := by
  obtain ⟨-, -, hD, -, -, h278⟩ := four_cycles.2.2.2
  rw [citedSteps_aPer_neg_seventeen, hD, h278]
  exact ⟨by norm_num, by decide, rfl⟩

/-! ### `prop:proposition` -/

/-- `α = 2 − log₂ 3 − 10^{−10}` (l.197). -/
noncomputable def citedStepsAlpha : ℝ := 2 - Real.logb 2 3 - 1 / 10 ^ 10

set_option exponentiation.threshold 200000 in
/-- `log₂ 3 < 125743/79335`, from `3^{79335} < 2^{125743}` in the kernel (a convergent of
`log₂ 3` from above). -/
theorem citedSteps_logb_lt : Real.logb 2 3 < 125743 / 79335 := by
  have hN : (3 : ℕ) ^ 79335 < 2 ^ 125743 := by decide
  have hpow : (3 : ℝ) ^ 79335 < 2 ^ 125743 := by exact_mod_cast hN
  have hlog := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [Real.logb, div_lt_div_iff₀ hl2 (by norm_num)]
  push_cast at hlog
  linarith

/-- `α > 0.415037499` (l.197). -/
theorem citedStepsAlpha_gt : (0.415037499 : ℝ) < citedStepsAlpha := by
  have := citedSteps_logb_lt
  unfold citedStepsAlpha
  norm_num at this ⊢
  linarith

/-- `#{i ∈ ⟦1, n⟧ | a_i(x) = 1}` (l.196), in the convention of l.62. -/
noncomputable def citedStepsOnes (n : ℕ) (x : ℤ) : ℕ :=
  ((Icc 1 n).filter (fun i => a i x = 1)).card

/-- The count is the same in the convention of l.71 (`a_1 = ν₂(3x + 1)`): on a cycle,
`#{i ∈ ⟦1, n⟧ | a_i = 1} = #{k ∈ ⟦0, n−1⟧ | a_k = 1}`. -/
theorem citedStepsOnes_eq_range {x : ℤ} {n : ℕ} (hx : T^[n] x = x) :
    citedStepsOnes n x = ((range n).filter (fun k => a k x = 1)).card := by
  have hper : ∀ k, a (k + n) x = a k x :=
    (periodic_a_iff_periodic_T x n).2 (fun k => by rw [Function.iterate_add_apply, hx])
  have han : a n x = a 0 x := by simpa using hper 0
  unfold citedStepsOnes
  rw [Finset.card_filter, Finset.card_filter,
    show Icc 1 n = Ico 1 (n + 1) by ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  have h1 := Finset.sum_range_succ (fun k => if a k x = 1 then 1 else 0) n
  have h2 := Finset.sum_range_succ' (fun k => if a k x = 1 then 1 else 0) n
  simp only [han] at h1
  have e : ∑ k ∈ range n, (if a (1 + k) x = 1 then 1 else 0) =
      ∑ k ∈ range n, (if a (k + 1) x = 1 then 1 else 0) :=
    Finset.sum_congr rfl (fun k _ => by rw [add_comm])
  rw [e]
  omega

/-- `p_n ≥ a + 2(n − a)` (l.201): `2n ≤ #{a_i = 1} + p_n` on every cycle of `ℤ`. -/
theorem citedSteps_two_mul_le {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    2 * n ≤ citedStepsOnes n x + p n x := by
  rw [citedStepsOnes_eq_range hx, Finset.card_filter]
  have h1 := (citedSteps_le_p hn hx).2
  show 2 * n ≤ ∑ k ∈ range n, (if a k x = 1 then 1 else 0) + ∑ k ∈ range n, a k x
  rw [← Finset.sum_add_distrib]
  calc 2 * n = ∑ _k ∈ range n, 2 := by simp [mul_comm]
    _ ≤ ∑ k ∈ range n, ((if a k x = 1 then 1 else 0) + a k x) :=
      Finset.sum_le_sum (fun k hk => by
        have := (h1 k (Finset.mem_range.1 hk)).1
        split_ifs with h <;> omega)

/-- **`prop:proposition` for `x < 0`, unconditional**: no computer check, no `|x| > 1000`;
`#{a_i = 1} > (2 − log₂ 3) n > α n`. -/
theorem prop_proposition_neg {x : ℤ} (hx0 : x < 0) {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) :
    (2 - Real.logb 2 3) * n < citedStepsOnes n x ∧ citedStepsAlpha * n < citedStepsOnes n x := by
  have hpos := two_pow_p_sub_three_pow_mul_pos hn hx
  have hneg : (2 : ℤ) ^ p n x - 3 ^ n < 0 := by nlinarith
  have hlt : (2 : ℝ) ^ p n x < 3 ^ n := by
    have : (2 : ℤ) ^ p n x < 3 ^ n := by linarith
    exact_mod_cast this
  have hlb := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hlt
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlb
  have h2 := citedSteps_two_mul_le hn hx
  have h2' : (2 : ℝ) * n ≤ citedStepsOnes n x + p n x := by exact_mod_cast h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (2 - Real.logb 2 3) * n < citedStepsOnes n x := by nlinarith
  refine ⟨h1, lt_of_le_of_lt ?_ h1⟩
  unfold citedStepsAlpha
  have : (0 : ℝ) < 1 / 10 ^ 10 := by norm_num
  nlinarith

/-- The step from the true `cor:bounds` (`Syracuse.bounds`), on every cycle of `ℤ*`:
`#{a_i = 1} ≥ n (2 − log₂ 3 − log₂(1 + 1/(3 min)))`. -/
theorem prop_proposition_min {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    {m : ℤ} (hm : IsLeast (Set.range fun k : ℕ => T^[k] x) m) :
    (2 - Real.logb 2 3 - Real.logb 2 (1 + 1 / (3 * (m : ℝ)))) * n ≤ citedStepsOnes n x := by
  obtain ⟨-, M, -, hM⟩ := exists_isLeast_isGreatest_of_cycle hn hx
  have hb := (bounds hn hx hm hM).2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_sub' hn'.ne', div_le_iff₀ hn'] at hb
  have h2 := citedSteps_two_mul_le hn hx
  have h2' : (2 : ℝ) * n ≤ citedStepsOnes n x + p n x := by exact_mod_cast h2
  nlinarith

/-- On a cycle, if some iterate is `1` then the cycle is `(1)`. -/
theorem citedSteps_eq_one_of_iterate {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x) {k : ℕ}
    (hk : T^[k] x = 1) : x = 1 := by
  have hq : T^[n * k] x = x := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hx _
  have e : n * k = (n * k - k) + k := by
    have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    omega
  rw [e, Function.iterate_add_apply, hk, T_iterate_one_int] at hq
  exact hq.symm

/-- `prop:proposition` on a cycle all of whose points are at least `10^{10}`:
`log₂(1 + 1/(3 min)) < 10^{−10}`. -/
theorem prop_proposition_pos_of_ge {x : ℤ} {n : ℕ} (hn : 0 < n) (hx : T^[n] x = x)
    (hge : ∀ k : ℕ, 10 ^ 10 ≤ T^[k] x) : citedStepsAlpha * n < citedStepsOnes n x := by
  obtain ⟨m, -, hm, -⟩ := exists_isLeast_isGreatest_of_cycle hn hx
  have h := prop_proposition_min hn hx hm
  obtain ⟨i, hi⟩ := hm.1
  have hm10 : (10 : ℝ) ^ 10 ≤ m := by
    have := hge i
    simp only at hi
    rw [hi] at this
    exact_mod_cast this
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) hm10
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hlog : Real.logb 2 (1 + 1 / (3 * (m : ℝ))) < 1 / 10 ^ 10 := by
    have ht : 0 < 1 / (3 * (m : ℝ)) := by positivity
    have h1 : Real.log (1 + 1 / (3 * (m : ℝ))) ≤ 1 / (3 * (m : ℝ)) := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 1 / (3 * (m : ℝ)))
      linarith
    have h2 : 1 / (3 * (m : ℝ)) ≤ 1 / (3 * 10 ^ 10) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [Real.logb, div_lt_iff₀ (by linarith)]
    have : (1 : ℝ) / (3 * 10 ^ 10) < 1 / 10 ^ 10 * (1 / 2) := by norm_num
    nlinarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold citedStepsAlpha
  nlinarith

/-- The check of l.201 gives what the proof draws from it: a positive cycle meeting `⟦1, 10^{10}⟦`
reaches `1`, so it is `(1)`. -/
theorem citedStepsCycleCheck_of_check (h : CitedStepsCheck) : CitedStepsCycleCheck := by
  intro x hx0 n hn hx
  rcases lt_or_ge x (10 ^ 10) with hlt | hge
  · obtain ⟨hodd, -⟩ := cycle_avoids_neg_third (A := ℤ) two_ne_zero hn hx
    obtain ⟨k, hk⟩ := h x hodd hx0 hlt
    exact Or.inl (citedSteps_eq_one_of_iterate hn hx hk)
  · exact Or.inr hge

/-- **`prop:proposition`, stronger than printed, from the check**: `x ≠ 1` suffices, and the
inequality is strict. For `x < 0` the check is not used. -/
theorem prop_proposition_ne_one (hC : CitedStepsCycleCheck) {x : ℤ} (hx1 : x ≠ 1) {n : ℕ}
    (hn : 0 < n) (hx : T^[n] x = x) : citedStepsAlpha * n < citedStepsOnes n x := by
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · exact (prop_proposition_neg hneg hn hx).2
  · exact absurd h0 (ne_zero_of_T_cycle_int hn hx)
  · refine prop_proposition_pos_of_ge hn hx (fun k => ?_)
    have hk0 : 0 < T^[k] x := T_iterate_pos_int hpos k
    have hkc : T^[n] (T^[k] x) = T^[k] x := by
      rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hx]
    rcases hC _ hk0 n hn hkc with h1 | h1
    · exact absurd (citedSteps_eq_one_of_iterate hn hx h1) hx1
    · exact h1

/-- **`prop:proposition` as printed, from the computer check** in the form l.201 uses. -/
theorem prop_proposition_of_cycleCheck (hC : CitedStepsCycleCheck) :
    (0.415037499 : ℝ) < citedStepsAlpha ∧
      ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → 1000 < |x| →
        citedStepsAlpha * n ≤ citedStepsOnes n x := by
  refine ⟨citedStepsAlpha_gt, fun x n hn hx habs => (prop_proposition_ne_one hC ?_ hn hx).le⟩
  rintro rfl
  norm_num at habs

/-- **`prop:proposition` as printed, from the computer check of l.201.** -/
theorem prop_proposition_of_check (hC : CitedStepsCheck) :
    (0.415037499 : ℝ) < citedStepsAlpha ∧
      ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → 1000 < |x| →
        citedStepsAlpha * n ≤ citedStepsOnes n x :=
  prop_proposition_of_cycleCheck (citedStepsCycleCheck_of_check hC)

/-- The counts at the cycles `(1)`, `(−1)`, `(−5, −7)` (both points) and `(−17, …)`:
`0`, `1`, `1`, `1`, `5`. The unconditional form for `x < 0` holds at each negative one, with
`α n` below the count. -/
theorem prop_proposition_instances :
    citedStepsOnes 1 (1 : ℤ) = 0 ∧ citedStepsOnes 1 (-1 : ℤ) = 1 ∧
      citedStepsOnes 2 (-5 : ℤ) = 1 ∧ citedStepsOnes 2 (-7 : ℤ) = 1 ∧
      citedStepsOnes 7 (-17 : ℤ) = 5 ∧
      citedStepsAlpha * 1 < citedStepsOnes 1 (-1 : ℤ) ∧
      citedStepsAlpha * 2 < citedStepsOnes 2 (-5 : ℤ) ∧
      citedStepsAlpha * 2 < citedStepsOnes 2 (-7 : ℤ) ∧
      citedStepsAlpha * 7 < citedStepsOnes 7 (-17 : ℤ) := by
  have h5 : T (-5 : ℤ) = -7 :=
    (T_unique (A := ℤ) two_ne_zero (x := -5) (t := -7) (k := 1) ⟨-4, by norm_num⟩ (by norm_num)).2
  have hx5 : T^[2] (-5 : ℤ) = -5 := cycle_neg_five.1
  have hx7 : T^[2] (-7 : ℤ) = -7 := by
    rw [← h5, ← Function.iterate_succ_apply, Function.iterate_succ_apply', hx5]
  have ha7 : ∀ k : ℕ, a k (-7 : ℤ) = seq12 ((k + 1 : ℕ) : ℤ) := fun k => by
    rw [← h5, ← Function.iterate_one T, a_iterate, seq12_eq_a]
  have hm1 := prop_proposition_neg (by norm_num : (-1 : ℤ) < 0) one_pos (T_iterate_neg_one_int 1)
  have hm5 := prop_proposition_neg (by norm_num : (-5 : ℤ) < 0) two_pos hx5
  have hm7 := prop_proposition_neg (by norm_num : (-7 : ℤ) < 0) two_pos hx7
  have hm17 := prop_proposition_neg (by norm_num : (-17 : ℤ) < 0) (by norm_num : 0 < 7)
    cycle_neg_seventeen.1
  refine ⟨?_, ?_, ?_, ?_, ?_, by simpa using hm1.2, by simpa using hm5.2, by simpa using hm7.2,
    by simpa using hm17.2⟩
  · simp [citedStepsOnes, a_one_int]
  · simp [citedStepsOnes, a_neg_one_int]
  · unfold citedStepsOnes
    rw [Finset.filter_congr (q := fun i : ℕ => seq12 (i : ℤ) = 1) (fun i _ => by
      rw [seq12_eq_a])]
    decide
  · unfold citedStepsOnes
    rw [Finset.filter_congr (q := fun i : ℕ => seq12 ((i + 1 : ℕ) : ℤ) = 1) (fun i _ => by
      rw [ha7])]
    decide
  · unfold citedStepsOnes
    rw [Finset.filter_congr (q := fun i : ℕ => seq17 (i : ℤ) = 1) (fun i _ => by
      rw [cycle_neg_seventeen.2 i])]
    decide

/-- For `x > 0` the hypothesis `|x| > 1000` cannot be dropped: at the cycle `(1)` the count is
`0 < α`. -/
theorem prop_proposition_unbounded_false :
    ¬ ∀ (x : ℤ) (n : ℕ), 0 < n → T^[n] x = x → citedStepsAlpha * n ≤ citedStepsOnes n x := by
  intro h
  have h1 := h 1 1 one_pos (T_iterate_one_int 1)
  rw [prop_proposition_instances.1] at h1
  have := citedStepsAlpha_gt
  push_cast at h1
  linarith

/-- **One Matveev hypothesis** (T-syr-cited-steps AUDIT-1): `theo:matveev` as printed here,
`CitedStepsMatveev`, is `NoCircuitMatveev` (`Syracuse.NoCircuit`) at `C = d = 3500000`, so a ruling
of T-syr-cited has one Prop to discharge for both files. -/
theorem citedStepsMatveev_iff_noCircuitMatveev :
    CitedStepsMatveev ↔ NoCircuitMatveev (citedStepsD : ℝ) := by
  have key : ∀ a : ℕ, Real.exp (citedStepsD : ℝ) * (a : ℝ) ^ citedStepsD =
      (Real.exp 1 * a) ^ (citedStepsD : ℝ) := by
    intro a
    rw [Real.rpow_natCast, mul_pow, ← Real.exp_nat_mul, mul_one]
  unfold CitedStepsMatveev NoCircuitMatveev
  simp only [key]

end Syracuse
