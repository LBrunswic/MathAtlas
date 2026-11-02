import CausalScaffold.Flat.Lox.FiniteIndexND
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The identity component of a closed subgroup of `SO₀(1, d)` is open in it

A step of Barbot's Prop 10.5 (`bprop:LU_discrete`, `GHFspace.tex` l.3367–3388 of the labelled
`papers/barbot/legacy/labeled/GHFspace.tex`), served to `bprop_LU_discrete`
(`Flat/Loxodromic.lean`): on the branch `L_U(Γ_nd) = {1}` the proof (l.3373–3377) makes the
closure of `L_U(Γ)` a group with trivial neutral component, and its discreteness then rests on the
Lie-group fact that the neutral component of a closed subgroup of `SO₀(1, d)` is open in it:
Cartan's closed-subgroup theorem in its local form. **No label is marked**: the paper uses it as
standard Lie theory.

* `bprop:LU_discrete` — `GHFspace.tex:3368` (Prop 10.5), l.3373–3377, partial (its Lie-theoretic input; **no `sorry`**):
  `Lox.exists_nhds_subset_connectedComponentIn_closure` — for every subgroup `K ≤ SO₀(1, d)` there is
  a neighbourhood `V` of `1` with `V ∩ cl K ⊆ (cl K)₀`.

> Since the action of $\Gamma$ on ${\bf M}^{n}\slash{\bf U}$ is a linear
> euclidean action, the closure of $L_{U}(\Gamma)$ in $\mbox{SO}_{0}({\bf U})$
> is the restriction to ${\bf U}$ of the closure of $L(\Gamma)$ in
> $SO_{0}(1,n-1)$. Hence, the neutral component of this
> closure is contained in $L_{U}(\Gamma_{nd})$ (l.3373–3377)

The step from "the neutral component is trivial" to "the group is discrete", left implicit there,
is the one proved here: a subgroup of `SO₀(1, d)` near `1` meets its closure only inside the
neutral component. `Flat/Loxodromic.lean` (`discreteTopology_restrictGroup_of_nonDiscretePart_bot`)
uses it without passing through the closure of `L_U(Γ)`.

## The elementary route (von Neumann – Cartan)

In a finite-dimensional real Banach algebra `𝔸`, for a closed set `S` with `1 ∈ S`, closed under
products and under `exp X ↦ exp (−X)`:

* `Lox.exp_smul_mem_of_tendsto` — if `exp Xₖ ∈ S`, `Xₖ → 0`, `Xₖ ≠ 0` and `Xₖ/‖Xₖ‖ → Y`, then
  `exp (t Y) ∈ S` for every real `t` (`exp (⌊t/‖Xₖ‖⌋ Xₖ) = (exp Xₖ)^⌊t/‖Xₖ‖⌋ → exp (t Y)`);
* `Lox.lieAlgebraOf` — `𝔥 = {Y | ∀ t, exp (t Y) ∈ S}` is a linear subspace: closure under addition is
  the Trotter step, through the derivative `Y + Z` at `0` of `s ↦ log (exp (s Y) exp (s Z))` (`log`
  the local inverse of `exp` at `0`, `HasStrictFDerivAt.localInverse`);
* `Lox.exists_nhds_exp_lieCone` — near `1`, every element of `S` is `exp X` with `X ∈ 𝔥`: write
  `c = exp H · exp M` with `(H, M) ∈ 𝔥 × 𝔪` small (inverse function theorem for
  `(H, M) ↦ exp H · exp M`, `𝔪` a complement of `𝔥`); if `M ≠ 0` along a sequence `cₖ → 1`, then
  `exp Mₖ = exp (−Hₖ) cₖ ∈ S` and a limit of `Mₖ/‖Mₖ‖` is a unit vector of `𝔥 ∩ 𝔪 = 0`.

Then `t ↦ exp (t X)`, `t ∈ ℝ`, is a path in `S` from `1` to `c`. For `SO₀(1, d)` (`lorentzTopology`)
the algebra is `End(𝐌ⁿ)` and `S` the image of `cl K`, closed because `SO₀(1, d)` is closed in
`End(𝐌ⁿ)` (`Lox.isClosed_range_lorentz_linToCLM`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (standard Lie theory) closed subgroups of the Lie group `SO₀(1, d)` | ✓ proved for every subgroup `K` of `SO₀(1, d)`: the conclusion concerns its closure; no Lie-group structure is assumed |

## SCOPE (disclosed)

* Only the local half of Cartan's theorem is proved (the neutral component is open; it is the image
  of a neighbourhood of `0` in `𝔥` under `exp`), not that `cl K` is an embedded submanifold.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
package WP-34d-Loxodromic (closer).
-/

namespace Causal.Flat.Lox
open Set Filter Topology NormedSpace

/-! ### §1 One-parameter subgroups in a closed multiplicative set -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp` is continuous (over `ℝ`; mathlib's `exp_continuous` asks for a `NormedAlgebra ℚ`). -/
theorem exp_continuous_real : Continuous (exp : 𝔸 → 𝔸) := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top ℝ 𝔸]
  exact continuousOn_exp (𝕂 := ℝ)

theorem tendsto_exp_real {α : Type*} {l : Filter α} {f : α → 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp a)) :=
  (exp_continuous_real.tendsto _).comp hf

/-- `exp (x + y) = exp x * exp y` for commuting `x`, `y` (over `ℝ`). -/
theorem exp_add_of_commute_real {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hxy
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_of_commute_real (Commute.neg_left (Commute.refl x)), neg_add_cancel, exp_zero]

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_of_commute_real (Commute.neg_right (Commute.refl x)), add_neg_cancel, exp_zero]

theorem exp_nsmul_real (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, exp_add_of_commute_real ((Commute.refl x).smul_left n), ih, pow_succ]

/-- **Integer multiples.** If `S ∋ 1` is closed under products and `exp X ∈ S → exp (−X) ∈ S`, then
`exp X ∈ S` gives `exp (m X) ∈ S` for every integer `m`. -/
theorem exp_intCast_smul_mem {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hneg : ∀ X : 𝔸, exp X ∈ S → exp (-X) ∈ S)
    {X : 𝔸} (hX : exp X ∈ S) (m : ℤ) : exp ((m : ℝ) • X) ∈ S := by
  have hnat : ∀ n : ℕ, exp ((n : ℝ) • X) ∈ S := by
    intro n
    rw [Nat.cast_smul_eq_nsmul ℝ n X, exp_nsmul_real]
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hX
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact_mod_cast hnat n
  · have := hneg _ (hnat n)
    rwa [Int.cast_neg, Int.cast_natCast, neg_smul]

/-- **A one-parameter subgroup in the limit** (von Neumann): if `exp Xₖ ∈ S` with `Xₖ → 0`,
`Xₖ ≠ 0` and `Xₖ/‖Xₖ‖ → Y`, then `exp (t Y) ∈ S` for every `t`. -/
theorem exp_smul_mem_of_tendsto {S : Set 𝔸} (hS : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hneg : ∀ X : 𝔸, exp X ∈ S → exp (-X) ∈ S)
    {X : ℕ → 𝔸} (hX0 : Tendsto X atTop (𝓝 0)) (hXne : ∀ᶠ k in atTop, X k ≠ 0)
    (hXS : ∀ᶠ k in atTop, exp (X k) ∈ S) {Y : 𝔸}
    (hY : Tendsto (fun k => ‖X k‖⁻¹ • X k) atTop (𝓝 Y)) (t : ℝ) : exp (t • Y) ∈ S := by
  set m : ℕ → ℤ := fun k => ⌊t / ‖X k‖⌋
  have hn0 : Tendsto (fun k => ‖X k‖) atTop (𝓝 0) := by simpa using hX0.norm
  have hm : Tendsto (fun k => (m k : ℝ) * ‖X k‖) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun k => t - ‖X k‖)
      (h := fun _ => t) ?_ tendsto_const_nhds ?_ ?_
    · simpa using (tendsto_const_nhds (x := t)).sub hn0
    · filter_upwards [hXne] with k hk
      have hp : 0 < ‖X k‖ := norm_pos_iff.2 hk
      have h2 := mul_lt_mul_of_pos_right (Int.sub_one_lt_floor (t / ‖X k‖)) hp
      rw [sub_mul, div_mul_cancel₀ _ hp.ne', one_mul] at h2
      exact h2.le
    · filter_upwards [hXne] with k hk
      have hp : 0 < ‖X k‖ := norm_pos_iff.2 hk
      have h2 := mul_le_mul_of_nonneg_right (Int.floor_le (t / ‖X k‖)) hp.le
      rwa [div_mul_cancel₀ _ hp.ne'] at h2
  have e : ∀ᶠ k in atTop, ((m k : ℝ) * ‖X k‖) • (‖X k‖⁻¹ • X k) = (m k : ℝ) • X k := by
    filter_upwards [hXne] with k hk
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hk), mul_one]
  have hlim : Tendsto (fun k => exp ((m k : ℝ) • X k)) atTop (𝓝 (exp (t • Y))) :=
    (tendsto_exp_real (hm.smul hY)).congr' (e.mono fun k hk => by rw [hk])
  exact hS.mem_of_tendsto hlim (hXS.mono fun k hk => exp_intCast_smul_mem h1 hmul hneg hk (m k))

/-- `exp` has the strict derivative `id` at `0`, as a continuous linear equivalence. -/
theorem hasStrictFDerivAt_exp_zero_equiv :
    HasStrictFDerivAt (exp : 𝔸 → 𝔸) ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero

variable (𝔸) in
/-- **A local logarithm**: the local inverse of `exp` at `0`. -/
noncomputable def expLog : 𝔸 → 𝔸 :=
  (hasStrictFDerivAt_exp_zero_equiv (𝔸 := 𝔸)).localInverse exp _ 0

theorem expLog_one : expLog 𝔸 1 = 0 := by
  have := (hasStrictFDerivAt_exp_zero_equiv (𝔸 := 𝔸)).localInverse_apply_image
  rwa [exp_zero] at this

theorem exp_expLog : ∀ᶠ y in 𝓝 (1 : 𝔸), exp (expLog 𝔸 y) = y := by
  have := (hasStrictFDerivAt_exp_zero_equiv (𝔸 := 𝔸)).eventually_right_inverse
  rwa [exp_zero] at this

theorem hasStrictFDerivAt_expLog :
    HasStrictFDerivAt (expLog 𝔸) (((ContinuousLinearEquiv.refl ℝ 𝔸).symm : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      1 := by
  have := (hasStrictFDerivAt_exp_zero_equiv (𝔸 := 𝔸)).to_localInverse
  rwa [exp_zero] at this

/-- The **cone** `{Y | ∀ t, exp (t Y) ∈ S}` (the Lie algebra of `S`, once it is shown linear). -/
def lieCone (S : Set 𝔸) : Set 𝔸 := {Y | ∀ t : ℝ, exp (t • Y) ∈ S}

/-- **The Trotter step**: the cone of a closed `S` is closed under addition. -/
theorem add_mem_lieCone {S : Set 𝔸} (hS : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hneg : ∀ X : 𝔸, exp X ∈ S → exp (-X) ∈ S)
    {Y Z : 𝔸} (hY : Y ∈ lieCone S) (hZ : Z ∈ lieCone S) : Y + Z ∈ lieCone S := by
  by_cases h0 : Y + Z = 0
  · intro t; rw [h0, smul_zero, exp_zero]; exact h1
  set g : ℝ → 𝔸 := fun s => exp (s • Y) * exp (s • Z) with hgdef
  have hg0 : g 0 = 1 := by simp [g]
  have hg : HasDerivAt g (Y + Z) 0 := by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0).fun_mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)
    simpa [zero_smul, exp_zero] using this
  set f : ℝ → 𝔸 := fun s => expLog 𝔸 (g s) with hfdef
  have hf : HasDerivAt f (Y + Z) 0 := by
    have hl := (hasStrictFDerivAt_expLog (𝔸 := 𝔸)).hasFDerivAt
    rw [← hg0] at hl
    have := hl.comp_hasDerivAt (0 : ℝ) hg
    simpa [Function.comp_def] using this
  have hf0 : f 0 = 0 := by simp [f, hg0, expLog_one]
  -- the sequence `sₖ = 1/(k+1) → 0⁺`
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hspos : ∀ k, 0 < s k := fun k => by positivity
  have hsne : Tendsto s atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall fun k => (hspos k).ne'⟩
  set X : ℕ → 𝔸 := fun k => f (s k)
  have hW : Tendsto (fun k => (s k)⁻¹ • X k) atTop (𝓝 (Y + Z)) := by
    have := (hasDerivAt_iff_tendsto_slope_zero.1 hf).comp hsne
    simpa [Function.comp_def, hf0, X] using this
  have hX0 : Tendsto X atTop (𝓝 0) := by
    have := hf.continuousAt.tendsto.comp hs0
    rwa [hf0] at this
  have hgs : Tendsto (fun k => g (s k)) atTop (𝓝 1) := by
    have := hg.continuousAt.tendsto.comp hs0
    rwa [hg0] at this
  have hXS : ∀ᶠ k in atTop, exp (X k) ∈ S := by
    filter_upwards [hgs.eventually exp_expLog] with k hk
    show exp (expLog 𝔸 (g (s k))) ∈ S
    rw [hk]; exact hmul _ (hY _) _ (hZ _)
  have hWne : ∀ᶠ k in atTop, (s k)⁻¹ • X k ≠ 0 := hW.eventually_ne h0
  have hXne : ∀ᶠ k in atTop, X k ≠ 0 := hWne.mono fun k hk h => hk (by rw [h, smul_zero])
  have hnorm : ∀ k, ‖(s k)⁻¹ • X k‖⁻¹ • ((s k)⁻¹ • X k) = ‖X k‖⁻¹ • X k := by
    intro k
    by_cases hk : X k = 0
    · simp [hk]
    have hsk := (hspos k)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsk), smul_smul, mul_inv, inv_inv]
    congr 1
    field_simp
  have hU : Tendsto (fun k => ‖X k‖⁻¹ • X k) atTop (𝓝 (‖Y + Z‖⁻¹ • (Y + Z))) := by
    have := (hW.norm.inv₀ (norm_ne_zero_iff.2 h0)).smul hW
    simpa only [hnorm] using this
  intro t
  have := exp_smul_mem_of_tendsto hS h1 hmul hneg hX0 hXne hXS hU (t * ‖Y + Z‖)
  rwa [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), mul_one] at this

/-- **The Lie algebra of a closed `S`**: `lieCone S` is a linear subspace. -/
def lieAlgebraOf {S : Set 𝔸} (hS : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hneg : ∀ X : 𝔸, exp X ∈ S → exp (-X) ∈ S) :
    Submodule ℝ 𝔸 where
  carrier := lieCone S
  add_mem' := add_mem_lieCone hS h1 hmul hneg
  zero_mem' := fun t => by rw [smul_zero, exp_zero]; exact h1
  smul_mem' := fun c Y hY t => by rw [smul_smul]; exact hY _

/-- **Near `1`, every element of a closed `S` is `exp X` with `X` in its Lie algebra** (the local
half of Cartan's closed-subgroup theorem, finite dimension). -/
theorem exists_nhds_exp_lieCone [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hS : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hneg : ∀ X : 𝔸, exp X ∈ S → exp (-X) ∈ S) :
    ∃ V ∈ 𝓝 (1 : 𝔸), ∀ c ∈ V, c ∈ S → ∃ X ∈ lieCone S, exp X = c := by
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  set 𝔥 := lieAlgebraOf hS h1 hmul hneg
  obtain ⟨𝔪, h𝔥𝔪⟩ := Submodule.exists_isCompl 𝔥
  -- `Φ (H, M) = exp H · exp M` and its derivative `(H, M) ↦ H + M` at `0`
  set e : (𝔥 × 𝔪) ≃L[ℝ] 𝔸 :=
    (Submodule.prodEquivOfIsCompl 𝔥 𝔪 h𝔥𝔪).toContinuousLinearEquiv
  set Φ : 𝔥 × 𝔪 → 𝔸 := fun p => exp (p.1 : 𝔸) * exp (p.2 : 𝔸) with hΦdef
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hΦ : HasStrictFDerivAt Φ (e : (𝔥 × 𝔪) →L[ℝ] 𝔸) 0 := by
    set a : (𝔥 × 𝔪) →L[ℝ] 𝔸 := 𝔥.subtypeL.comp (ContinuousLinearMap.fst ℝ 𝔥 𝔪)
    set b : (𝔥 × 𝔪) →L[ℝ] 𝔸 := 𝔪.subtypeL.comp (ContinuousLinearMap.snd ℝ 𝔥 𝔪)
    have ha : HasStrictFDerivAt (fun p : 𝔥 × 𝔪 => exp (a p)) a 0 := by
      have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸))
      rw [← map_zero a] at h
      have := h.comp (0 : 𝔥 × 𝔪) a.hasStrictFDerivAt
      have e1 : (1 : 𝔸 →L[ℝ] 𝔸).comp a = a := ContinuousLinearMap.id_comp _
      rw [e1] at this
      exact this
    have hb : HasStrictFDerivAt (fun p : 𝔥 × 𝔪 => exp (b p)) b 0 := by
      have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸))
      rw [← map_zero b] at h
      have := h.comp (0 : 𝔥 × 𝔪) b.hasStrictFDerivAt
      have e1 : (1 : 𝔸 →L[ℝ] 𝔸).comp b = b := ContinuousLinearMap.id_comp _
      rw [e1] at this
      exact this
    have := ha.fun_mul' hb
    refine this.congr_fderiv ?_
    ext p <;> simp [a, b, e, add_comm]
  set Ψ := hΦ.localInverse Φ e 0
  have hΨt : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have := hΦ.localInverse_tendsto; rwa [hΦ0] at this
  have hΦΨ : ∀ᶠ y in 𝓝 (1 : 𝔸), Φ (Ψ y) = y := by
    have := hΦ.eventually_right_inverse; rwa [hΦ0] at this
  by_contra hcon
  push Not at hcon
  -- a sequence `cₖ → 1` of elements of `S` that are no `exp X`, `X ∈ 𝔥`
  have hc : ∀ k : ℕ, ∃ c ∈ Metric.ball (1 : 𝔸) (1 / ((k : ℝ) + 1)), c ∈ S ∧
      ∀ X ∈ lieCone S, exp X ≠ c := fun k =>
    hcon _ (Metric.ball_mem_nhds _ (by positivity))
  choose c hcb hcS hcX using hc
  have hct : Tendsto c atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun k hk => (hcb k).trans ?_⟩
    refine lt_of_le_of_lt ?_ hN
    gcongr
  set p : ℕ → 𝔥 × 𝔪 := fun k => Ψ (c k)
  have hpt : Tendsto p atTop (𝓝 0) := hΨt.comp hct
  have hΦp : ∀ᶠ k in atTop, Φ (p k) = c k := hct.eventually hΦΨ
  set M : ℕ → 𝔸 := fun k => ((p k).2 : 𝔸)
  have hMt : Tendsto M atTop (𝓝 0) := by
    have h2 : Continuous fun q : 𝔥 × 𝔪 => ((q.2 : 𝔪) : 𝔸) := continuous_subtype_val.comp continuous_snd
    have := (h2.tendsto 0).comp hpt
    simpa [Function.comp_def] using this
  have hMne : ∀ᶠ k in atTop, M k ≠ 0 := by
    filter_upwards [hΦp] with k hk h0
    refine hcX k ((p k).1 : 𝔸) (p k).1.2 ?_
    rw [← hk]; show exp ((p k).1 : 𝔸) = exp ((p k).1 : 𝔸) * exp ((p k).2 : 𝔸)
    have : ((p k).2 : 𝔸) = 0 := h0
    rw [this, exp_zero, mul_one]
  have hMS : ∀ᶠ k in atTop, exp (M k) ∈ S := by
    filter_upwards [hΦp] with k hk
    have hH : exp (-((p k).1 : 𝔸)) ∈ S := by
      have := (p k).1.2 (-1); rwa [neg_one_smul] at this
    have e2 : exp (M k) = exp (-((p k).1 : 𝔸)) * c k := by
      rw [← hk]; show _ = exp (-((p k).1 : 𝔸)) * (exp ((p k).1 : 𝔸) * exp ((p k).2 : 𝔸))
      rw [← mul_assoc, exp_neg_mul_exp, one_mul]
    rw [e2]; exact hmul _ hH _ (hcS k)
  -- a limit `u` of `Mₖ/‖Mₖ‖`: a unit vector of `𝔪`, and of `𝔥`
  set u : ℕ → 𝔸 := fun k => ‖M k‖⁻¹ • M k
  have hu1 : ∀ k, u k ∈ Metric.closedBall (0 : 𝔸) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hk : M k = 0
    · simp [u, hk]
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hk)]
  obtain ⟨w, -, φ, hφ, hw⟩ := (isCompact_closedBall (0 : 𝔸) 1).tendsto_subseq hu1
  have hφt := hφ.tendsto_atTop
  have hwn : ‖w‖ = 1 := by
    have h1' : Tendsto (fun k => ‖u (φ k)‖) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hφt.eventually hMne] with k hk
      show (1 : ℝ) = ‖‖M (φ k)‖⁻¹ • M (φ k)‖
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hk)]
    exact tendsto_nhds_unique (hw.norm) h1'
  have hw𝔪 : w ∈ 𝔪 := by
    refine (Submodule.closed_of_finiteDimensional 𝔪).mem_of_tendsto hw
      (Eventually.of_forall fun k => ?_)
    exact 𝔪.smul_mem _ (p (φ k)).2.2
  have hw𝔥 : w ∈ 𝔥 := by
    intro t
    exact exp_smul_mem_of_tendsto hS h1 hmul hneg (hMt.comp hφt) (hφt.eventually hMne)
      (hφt.eventually hMS) hw t
  have : w = 0 := by
    have := h𝔥𝔪.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨hw𝔥, hw𝔪⟩)
    simpa using this
  rw [this, norm_zero] at hwn
  exact zero_ne_one hwn

end Algebra

/-! ### §2 `SO₀(1, d)` -/

section Lorentz

variable {d : ℕ}

/-- **`SO₀(1, d)` is closed in `End(𝐌ⁿ)`**: the range of `linToCLM` is cut out by the closed
conditions `Q ∘ T = Q`, `T(J⁺) ⊆ J⁺`, `det T = 1` (the last one makes `T` invertible). -/
theorem isClosed_range_lorentz_linToCLM :
    IsClosed (Set.range fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) := by
  set C : Set (Minkowski d →L[ℝ] Minkowski d) :=
    {T | (∀ v, minkQ (T v) = minkQ v) ∧ (∀ v, IsFutureCausal v → IsFutureCausal (T v)) ∧
      T.det = 1}
  have hC : IsClosed C := by
    have hev : ∀ v : Minkowski d,
        Continuous fun T : Minkowski d →L[ℝ] Minkowski d => T v := fun v =>
      (ContinuousLinearMap.apply ℝ (Minkowski d) v).continuous
    have h1 : IsClosed {T : Minkowski d →L[ℝ] Minkowski d | ∀ v, minkQ (T v) = minkQ v} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun v => isClosed_eq (continuous_minkQ.comp (hev v)) continuous_const
    have hcl : IsClosed {w : Minkowski d | IsFutureCausal w} :=
      (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_minkQ continuous_const)
    have h2 : IsClosed {T : Minkowski d →L[ℝ] Minkowski d |
        ∀ v, IsFutureCausal v → IsFutureCausal (T v)} := by
      simp only [setOf_forall]
      refine isClosed_iInter fun v => ?_
      by_cases hv : IsFutureCausal v
      · simpa [hv] using hcl.preimage (hev v)
      · simp [hv]
    have h3 : IsClosed {T : Minkowski d →L[ℝ] Minkowski d | T.det = 1} :=
      isClosed_eq ContinuousLinearMap.continuous_det continuous_const
    exact h1.inter (h2.inter h3)
  have heq : (Set.range fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) = C := by
    ext T
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨fun v => lorentz.minkQ_apply A.2 v, fun v hv => lorentz.isFutureCausal_apply A.2 hv,
        lorentz.det_eq_one A.2⟩
    · rintro ⟨hQ, hF, hdet⟩
      have hu : IsUnit (LinearMap.det (T : Minkowski d →ₗ[ℝ] Minkowski d)) := by
        have : LinearMap.det (T : Minkowski d →ₗ[ℝ] Minkowski d) = 1 := hdet
        rw [this]; exact isUnit_one
      set A := LinearMap.equivOfIsUnitDet hu
      have hA : ∀ v, A v = T v := fun v => LinearMap.equivOfIsUnitDet_apply hu v
      have hAL : (A : Minkowski d →ₗ[ℝ] Minkowski d) = (T : Minkowski d →ₗ[ℝ] Minkowski d) :=
        LinearMap.ext hA
      refine ⟨⟨A, fun v => by rw [hA]; exact hQ v, fun v hv => by rw [hA]; exact hF v hv, ?_⟩, ?_⟩
      · rw [hAL]; exact hdet
      · exact ContinuousLinearMap.ext fun v => hA v
  rw [heq]; exact hC

theorem isClosedEmbedding_lorentz_linToCLM :
    Topology.IsClosedEmbedding
      (fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) :=
  ⟨isEmbedding_lorentz_linToCLM, isClosed_range_lorentz_linToCLM⟩

/-- **The neutral component of the closure of a subgroup of `SO₀(1, d)` is a neighbourhood of `1`
in that closure** (Cartan's closed-subgroup theorem, local form): there is a neighbourhood `V` of
`1` with `V ∩ cl K ⊆ (cl K)₀`. Every element of `cl K` near `1` is joined to `1` in `cl K` by the
one-parameter group `t ↦ exp (t X)` (`exists_nhds_exp_lieCone`). -/
theorem exists_nhds_subset_connectedComponentIn_closure (K : Subgroup (lorentz d)) :
    ∃ V ∈ 𝓝 (1 : lorentz d), V ∩ closure (K : Set (lorentz d)) ⊆
      connectedComponentIn (closure (K : Set (lorentz d))) 1 := by
  haveI := lorentz_isTopologicalGroup (d := d)
  set ψ : lorentz d → (Minkowski d →L[ℝ] Minkowski d) :=
    fun A => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) with hψ
  have hψ1 : ψ 1 = 1 := linToCLM_one
  have hψmul : ∀ A B : lorentz d, ψ (A * B) = ψ A * ψ B := fun A B => linToCLM_mul _ _
  have hψinv : ∀ A : lorentz d, ψ A * ψ A⁻¹ = 1 := fun A => by
    rw [← hψmul, mul_inv_cancel, hψ1]
  set F := closure (K : Set (lorentz d))
  have hFsub : F = (K.topologicalClosure : Set (lorentz d)) := (Subgroup.topologicalClosure_coe).symm
  have hF1 : (1 : lorentz d) ∈ F := subset_closure K.one_mem
  have hFmul : ∀ A ∈ F, ∀ B ∈ F, A * B ∈ F := by
    intro A hA B hB; rw [hFsub] at hA hB ⊢; exact K.topologicalClosure.mul_mem hA hB
  have hFinv : ∀ A ∈ F, A⁻¹ ∈ F := by
    intro A hA; rw [hFsub] at hA ⊢; exact K.topologicalClosure.inv_mem hA
  set S := ψ '' F
  have hS : IsClosed S := isClosedEmbedding_lorentz_linToCLM.isClosedMap _ isClosed_closure
  have hS1 : (1 : Minkowski d →L[ℝ] Minkowski d) ∈ S := ⟨1, hF1, hψ1⟩
  have hSmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact ⟨A * B, hFmul A hA B hB, hψmul A B⟩
  have hSneg : ∀ X, exp X ∈ S → exp (-X) ∈ S := by
    rintro X ⟨A, hA, hAX⟩
    refine ⟨A⁻¹, hFinv A hA, ?_⟩
    calc ψ A⁻¹ = (exp (-X) * exp X) * ψ A⁻¹ := by rw [exp_neg_mul_exp, one_mul]
      _ = exp (-X) * (ψ A * ψ A⁻¹) := by rw [hAX, mul_assoc]
      _ = exp (-X) := by rw [hψinv, mul_one]
  obtain ⟨V', hV', hV'S⟩ := exists_nhds_exp_lieCone hS hS1 hSmul hSneg
  refine ⟨ψ ⁻¹' V', continuous_lorentz_linToCLM.continuousAt.preimage_mem_nhds
    (by show V' ∈ 𝓝 (ψ 1); rw [hψ1]; exact hV'), ?_⟩
  rintro A ⟨hAV, hAF⟩
  obtain ⟨X, hX, hXA⟩ := hV'S _ hAV ⟨A, hAF, rfl⟩
  -- the path `t ↦ exp (t X)` in `cl K`
  have hpath : ∀ t : ℝ, ∃ B ∈ F, ψ B = exp (t • X) := fun t => hX t
  choose B hBF hBψ using hpath
  have hBc : Continuous B := by
    rw [isEmbedding_lorentz_linToCLM.isInducing.continuous_iff]
    have : (fun t => ψ (B t)) = fun t => exp (t • X) := funext hBψ
    show Continuous (fun t => ψ (B t))
    rw [this]
    exact exp_continuous_real.comp (continuous_id.smul continuous_const)
  have hB0 : B 0 = 1 := isEmbedding_lorentz_linToCLM.injective (by
    show ψ (B 0) = ψ 1
    rw [hBψ, zero_smul ℝ X, exp_zero, hψ1])
  have hB1 : B 1 = A := isEmbedding_lorentz_linToCLM.injective (by
    show ψ (B 1) = ψ A
    rw [hBψ, one_smul ℝ X, hXA])
  have hsub : range B ⊆ connectedComponentIn F 1 :=
    (isPreconnected_range hBc).subset_connectedComponentIn ⟨0, hB0⟩
      (by rintro _ ⟨t, rfl⟩; exact hBF t)
  exact hsub ⟨1, hB1⟩

end Lorentz

end Causal.Flat.Lox
