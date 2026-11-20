import EGF.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The master universality theorem of Ergodic Generative Flows

**`theo:universality_true`** — `main.tex:775` (statement `main.tex:775–776`, proof `main.tex:778–804`).
Anchor: `EGF.main_universality` (DEC-133, story fragment S-egf-1).

> Let $(\Statespace,\lambda)$ be a measured Polish space and let $\ForwardPolicyStar$ be a Markov
> kernel acting on $\Statespace$. Assume that $\ForwardPolicyStar$ is ergodic on
> $(\Statespace,\lambda)$ with summable $L^2$-mixing coefficients, then for any probability
> distributions $\Finit,\Fterm \ll \lambda$ with density in $L^2(\lambda)$ and any
> $\varepsilon>0$, there exists $\foutstar\in L^2(\lambda)$ such that the generative flow
> $(\ForwardPolicyStar,\foutstar)$ from $\Finit$ to $\Fterm$ is such that
> $\delta\Finit(\Statespace)+\delta\Fterm(\Statespace)<\varepsilon$.

## What is proved

| | |
|---|---|
| **`main_universality`** | the theorem, with fewer hypotheses (no Polish, no ergodicity, no `L²` densities) and a stronger conclusion (`f_out ≥ 0` bounded) |
| `main_universality_of_tendsto` | the general form it is derived from: `∑ γₙ < ∞` replaced by `γ₀ < ∞` and `γₙ → 0` |
| `isSummablyL2Mixing_const`, `main_universality_const` | inhabitation: the resampling kernel `π(x) = λ` is summably `L²`-mixing on any probability space |
| `tvMass`, `errors_eq_tvMass` | `δF_init(𝒮) + δF_term(𝒮)` is the total variation of `F_init + F_in − F_term − F_out` |
| `tvMass_triangle`, `tvMass_bind_le`, `tvMass_add_right_le`, `tvMass_le_add_right`, `tvMass_withDensity_le` | the total-variation calculus used |
| `pushIter_*`, `bind_finset_sum`, `shift_sum` | `μ ↦ μπⁿ`: additive, homogeneous, monotone, mass-preserving |
| `tvMass_construction` | the truncated Neumann series lifted by an invariant measure: with `A = ∑_{t≤T} μ₀πᵗ`, `B = ∑_{t≤T} μ₁πᵗ ≤ R = Rπ`, the outflow `A + (R − B)` has defect `≤ ‖μ₀π^{T+1} − μ₁π^{T+1}‖_TV` |
| `lintegral_transfer_sq_le` | `∫ (φπⁿ)² dλ̂ ≤ γₙ ‖φ‖₂²` for mean-zero `φ ∈ L²(λ)` |
| `trivial_of_lamHat_univ_eq_top(_of_ne_top)`, `eq_of_trivial` | `γ₀ < ∞` and `λ̂(𝒮) = ∞` force a trivial `λ`, on which `F_init = F_term` |
| `exists_truncation` | `F ≪ λ` is TV-close to a measure with density `≤ K` and `≤ K dλ̂/dλ` |
| `exists_tvMass_pushIter_lt(_of_tendsto)` | **`γₙ → 0` gives mixing in total variation** for such densities |

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(𝒮, λ)` a measured Polish space, `λ` finite (`main.tex:155`, `:161`) | ⚠ weakened: any `MeasurableSpace S`; `[IsFiniteMeasure lam]` carried (the standing assumption of `main.tex:161`, used by the proof at `:793`) |
| `π` a Markov kernel | ✓ `[IsMarkovKernel π]` |
| `π` ergodic on `(𝒮, λ)` | ⚠ weakened: not assumed. In Walters' sense (`main.tex:211`, `:819`) it includes the invariance `λπ = λ`, which is what is genuinely dropped; ergodicity of `(π, λ̂)` itself follows from `γ₀ < ∞`, `γₙ → 0` (not formalized) |
| summable `L²`-mixing coefficients | ✓ `IsSummablyL2Mixing π lam` (`def:summably_mixing`); only `γ₀ < ∞` and `γₙ → 0` are used (`main_universality_of_tendsto`) |
| `F_init, F_term` probability measures, `≪ λ` | ✓ carried |
| densities of `F_init, F_term` in `L²(λ)` | ⚠ weakened: not assumed |
| conclusion: `∃ f_out ∈ L²(λ)`, `δF_init(𝒮) + δF_term(𝒮) < ε` | ✓ with `f_out ≥ 0` (an outflow is a non-negative measure, `main.tex:161`) and bounded; `F_out = f_out λ`; `ε : ℝ≥0∞`, any `ε > 0` |

## SCOPE (disclosed)

Nothing is assumed beyond Mathlib: no `sorry`, no named hypothesis. The statement is read through
the vocabulary of `EGF.Defs`: `δF_init`, `δF_term` are Mathlib's truncated differences of
finite measures, identified there with the negative and positive parts of the Jordan decomposition
(`initialError_eq_negPart`, `terminalError_eq_posPart`); summable `L²`-mixing is
`def:summably_mixing` in the reading of `main.tex:273` (see that file).

**The proof is not the paper's.** The paper sums the whole Neumann series `∑ₜ (F_init − F_term)πᵗ`
in `L²(λ)` and lifts it by `ηλ` (`main.tex:779–803`). Here the series is truncated at `T`, lifted by
`(T+1)Kλ̂` (an invariant measure, so the lift costs nothing), and the outflow's density is truncated
to make it bounded; the defect is then `‖μ₀π^{T+1} − μ₁π^{T+1}‖_TV` plus truncation errors, and only
`γₙ → 0` (plus `γ₀ < ∞`) is used, never the sum `∑ γₙ` (`main_universality_of_tendsto`). `F_init`, `F_term` are first replaced by
TV-close probability measures with density `≤ K` and `≤ K dλ̂/dλ`, which is what turns `L²(λ̂)`
decay into total-variation decay without any comparison between `λ` and `λ̂`.

**`λ̂` need not be finite in `def:summably_mixing`**; when it is not, `γ₀ < ∞` forces every
measurable set to be `λ`-null or `λ`-conull (`trivial_of_lamHat_univ_eq_top`), and then
`F_init = F_term`, `f_out = 0`.

## Findings on the paper (details in the REPORT)

1. The Polish structure and the `L²` densities of `F_init`, `F_term` are not needed, and
   summability of `(γₙ)` can be weakened to `γₙ → 0` with `γ₀ < ∞` (`main_universality_of_tendsto`).
   Ergodicity proper is not an extra assumption: `γ₀ < ∞`, `γₙ → 0` already force `(π, λ̂)` to be
   ergodic (not formalized); what the Lean theorem genuinely drops is the invariance of `λ` (2).
   Where `λ` is invariant (every application in the paper, `main.tex:819`, `:836`, and the
   Walters reading of (2)), the submultiplicativity argument of (3) makes `γₙ → 0` imply
   summability, so the weakening can be strict only for a non-invariant `λ`; no example is given.
2. `main.tex:793` uses `λπ = λ` (`ηλπ = ηλ`) and `main.tex:779` that `π` preserves `L²(λ)`. If
   "ergodic on `(𝒮, λ)`" is read in Walters' sense, as the paper uses the word (`main.tex:211`;
   `:819` applies the theorem after noting that each `Φᵢ` keeps `λ` invariant), it includes
   `λπ = λ` and both steps follow from the theorem's own hypothesis (`:779` by Jensen); otherwise
   they are gaps, `def:summably_mixing` giving only an invariant `λ̂ ~ λ`. The Lean theorem
   assumes neither: it lifts by `λ̂`.
3. `main.tex:789`: summable squared norms `∑ₜ ‖dεₜ/dλ‖₂² < ∞` do not by themselves make `∑ₜ εₜ`
   converge in `L²` (it would follow from `∑ₜ ‖dεₜ/dλ‖₂ < ∞`), and `|ν_∞|₂ ≤ ∑ₜ ‖dεₜ/dλ‖₂²`
   mixes norms and squares. The argument fails as written, not the conclusion: with `λ̂ = λ`
   invariant, `γₙ` is the squared norm of `Tⁿ` on the mean-zero subspace, `T` the transfer, so
   submultiplicativity gives geometric decay and absolute convergence. Under the Walters reading
   of (2), `λ` is invariant and ergodic, so `λ̂ = cλ` and the step is fully repaired; only if
   "ergodic" excludes `λπ = λ` is `λ̂ ≠ λ` a genuine gap: the proof integrates against `λ` where
   `γₙ` integrates against `λ̂`.
4. `main.tex:790`: "`− R +`" stands for `− F_term +`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-! ## The total variation of a difference of finite measures -/

/-- `(μ − ν)⁺(𝒮) + (μ − ν)⁻(𝒮)`, the total variation of the signed measure `μ − ν`. -/
noncomputable def tvMass (μ ν : Measure S) : ℝ≥0∞ := (μ - ν) Set.univ + (ν - μ) Set.univ

theorem errors_eq_tvMass (π : Kernel S S) (Fout Finit Fterm : Measure S) :
    initialError π Fout Finit Fterm Set.univ + terminalError π Fout Finit Fterm Set.univ
      = tvMass (Finit + inflow π Fout) (Fterm + Fout) := by
  unfold initialError terminalError tvMass
  rw [add_comm]

theorem tvMass_comm (μ ν : Measure S) : tvMass μ ν = tvMass ν μ := add_comm _ _

theorem sub_le_sub_add_sub (μ ν ρ : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] : μ - ρ ≤ (μ - ν) + (ν - ρ) := by
  rw [Measure.sub_le_iff_le_add]
  have h1 : μ ≤ (μ - ν) + ν := Measure.sub_le_iff_le_add.mp le_rfl
  have h2 : ν ≤ (ν - ρ) + ρ := Measure.sub_le_iff_le_add.mp le_rfl
  calc μ ≤ (μ - ν) + ν := h1
    _ ≤ (μ - ν) + ((ν - ρ) + ρ) := add_le_add le_rfl h2
    _ = (μ - ν) + (ν - ρ) + ρ := (add_assoc _ _ _).symm

theorem tvMass_triangle (μ ν ρ : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] : tvMass μ ρ ≤ tvMass μ ν + tvMass ν ρ := by
  have h1 := sub_le_sub_add_sub μ ν ρ Set.univ
  have h2 := sub_le_sub_add_sub ρ ν μ Set.univ
  simp only [Measure.add_apply] at h1 h2
  unfold tvMass
  calc (μ - ρ) Set.univ + (ρ - μ) Set.univ
      ≤ ((μ - ν) Set.univ + (ν - ρ) Set.univ) + ((ρ - ν) Set.univ + (ν - μ) Set.univ) :=
        add_le_add h1 h2
    _ = ((μ - ν) Set.univ + (ν - μ) Set.univ) + ((ν - ρ) Set.univ + (ρ - ν) Set.univ) := by
        ring

theorem sub_add_le_sub (μ ν C : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure C] : (μ + C) - (ν + C) ≤ μ - ν := by
  rw [Measure.sub_le_iff_le_add]
  have h1 : μ ≤ (μ - ν) + ν := Measure.sub_le_iff_le_add.mp le_rfl
  calc μ + C ≤ (μ - ν) + ν + C := add_le_add h1 le_rfl
    _ = (μ - ν) + (ν + C) := add_assoc _ _ _

theorem tvMass_add_right_le (μ ν C : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure C] : tvMass (μ + C) (ν + C) ≤ tvMass μ ν :=
  add_le_add (sub_add_le_sub μ ν C Set.univ) (sub_add_le_sub ν μ C Set.univ)

theorem tvMass_add_left_le (μ ν C : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure C] : tvMass (C + μ) (C + ν) ≤ tvMass μ ν := by
  rw [add_comm C μ, add_comm C ν]; exact tvMass_add_right_le μ ν C

theorem sub_le_sub_add (μ ν C : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure C] : μ - ν ≤ (μ + C) - (ν + C) := by
  rw [Measure.sub_le_iff_le_add]
  have h1 : μ + C ≤ ((μ + C) - (ν + C)) + (ν + C) := Measure.sub_le_iff_le_add.mp le_rfl
  refine Measure.le_of_add_le_add_left (μ := C) ?_
  calc C + μ = μ + C := add_comm _ _
    _ ≤ ((μ + C) - (ν + C)) + (ν + C) := h1
    _ = C + (((μ + C) - (ν + C)) + ν) := by rw [← add_assoc, add_comm]

theorem tvMass_le_add_right (μ ν C : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure C] : tvMass μ ν ≤ tvMass (μ + C) (ν + C) :=
  add_le_add (sub_le_sub_add μ ν C Set.univ) (sub_le_sub_add ν μ C Set.univ)

theorem bind_add_measure (π : Kernel S S) (μ₁ μ₂ : Measure S) :
    (μ₁ + μ₂).bind π = μ₁.bind π + μ₂.bind π := by
  ext s hs
  rw [Measure.bind_apply hs (π.aemeasurable (μ := μ₁ + μ₂)), Measure.add_apply,
    Measure.bind_apply hs (π.aemeasurable (μ := μ₁)),
    Measure.bind_apply hs (π.aemeasurable (μ := μ₂)), lintegral_add_measure]

theorem bind_mono (π : Kernel S S) {μ ν : Measure S} (h : μ ≤ ν) : μ.bind π ≤ ν.bind π := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.bind_apply hs (π.aemeasurable (μ := μ)), Measure.bind_apply hs (π.aemeasurable (μ := ν))]
  exact lintegral_mono' h le_rfl

theorem tvMass_bind_le (π : Kernel S S) [IsMarkovKernel π] (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : tvMass (μ.bind π) (ν.bind π) ≤ tvMass μ ν := by
  have key : ∀ (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (μ.bind π - ν.bind π) Set.univ ≤ (μ - ν) Set.univ := by
    intro μ ν _ _
    have h : μ.bind π - ν.bind π ≤ (μ - ν).bind π := by
      rw [Measure.sub_le_iff_le_add, ← bind_add_measure]
      exact bind_mono π (Measure.sub_le_iff_le_add.mp le_rfl)
    calc (μ.bind π - ν.bind π) Set.univ ≤ ((μ - ν).bind π) Set.univ := h _
      _ = (μ - ν) Set.univ := bind_univ π _
  exact add_le_add (key μ ν) (key ν μ)

theorem tvMass_of_le {μ ν : Measure S} [IsFiniteMeasure μ] (h : μ ≤ ν) :
    tvMass μ ν = ν Set.univ - μ Set.univ := by
  unfold tvMass
  rw [Measure.sub_eq_zero_of_le h, Measure.sub_apply MeasurableSet.univ h]
  simp

theorem tvMass_withDensity_le (lam : Measure S) {u v : S → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) :
    tvMass (lam.withDensity u) (lam.withDensity v) ≤ ∫⁻ s, ((u s - v s) + (v s - u s)) ∂lam := by
  have key : ∀ {u v : S → ℝ≥0∞}, Measurable u → Measurable v →
      (lam.withDensity u - lam.withDensity v) Set.univ ≤ ∫⁻ s, (u s - v s) ∂lam := by
    intro u v hu hv
    have h : lam.withDensity u - lam.withDensity v ≤ lam.withDensity (u - v) := by
      refine Measure.sub_le_of_le_add ?_
      rw [← withDensity_add_right _ hv]
      exact withDensity_mono (ae_of_all _ fun s => le_tsub_add)
    calc (lam.withDensity u - lam.withDensity v) Set.univ ≤ lam.withDensity (u - v) Set.univ :=
          h _
      _ = ∫⁻ s, (u s - v s) ∂lam := by
          rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; rfl
  unfold tvMass
  rw [lintegral_add_left (hu.sub hv)]
  exact add_le_add (key hu hv) (key hv hu)


@[simp] theorem pushIter_zero (π : Kernel S S) (μ : Measure S) : pushIter π 0 μ = μ := rfl

theorem pushIter_succ (π : Kernel S S) (n : ℕ) (μ : Measure S) :
    pushIter π (n + 1) μ = (pushIter π n μ).bind π :=
  Function.iterate_succ_apply' _ n μ

theorem pushIter_add (π : Kernel S S) (n : ℕ) (μ ν : Measure S) :
    pushIter π n (μ + ν) = pushIter π n μ + pushIter π n ν := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushIter_succ, pushIter_succ, pushIter_succ, ih, bind_add_measure]

theorem pushIter_smul (π : Kernel S S) (n : ℕ) (c : ℝ≥0∞) (μ : Measure S) :
    pushIter π n (c • μ) = c • pushIter π n μ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushIter_succ, pushIter_succ, ih, Measure.bind_smul]

theorem pushIter_mono (π : Kernel S S) (n : ℕ) {μ ν : Measure S} (h : μ ≤ ν) :
    pushIter π n μ ≤ pushIter π n ν := by
  induction n with
  | zero => exact h
  | succ n ih => rw [pushIter_succ, pushIter_succ]; exact bind_mono π ih

theorem pushIter_univ (π : Kernel S S) [IsMarkovKernel π] (n : ℕ) (μ : Measure S) :
    pushIter π n μ Set.univ = μ Set.univ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushIter_succ, bind_univ, ih]

instance isFiniteMeasure_pushIter (π : Kernel S S) [IsMarkovKernel π] (n : ℕ) (μ : Measure S)
    [IsFiniteMeasure μ] : IsFiniteMeasure (pushIter π n μ) :=
  ⟨by rw [pushIter_univ]; exact measure_lt_top _ _⟩

theorem pushIter_of_bind_eq (π : Kernel S S) {μ : Measure S} (h : μ.bind π = μ) (n : ℕ) :
    pushIter π n μ = μ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushIter_succ, ih, h]

theorem pushIter_zero_measure (π : Kernel S S) (n : ℕ) : pushIter π n (0 : Measure S) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pushIter_succ, ih, Measure.bind_zero_left]

theorem bind_finset_sum (π : Kernel S S) {ι : Type*} (s : Finset ι) (μ : ι → Measure S) :
    (∑ i ∈ s, μ i).bind π = ∑ i ∈ s, (μ i).bind π := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bind_add_measure, ih]

theorem shift_sum (π : Kernel S S) (T : ℕ) (μ : Measure S) :
    μ + (∑ t ∈ Finset.range (T + 1), pushIter π t μ).bind π
      = ∑ t ∈ Finset.range (T + 1), pushIter π t μ + pushIter π (T + 1) μ := by
  rw [bind_finset_sum]
  simp_rw [← pushIter_succ]
  rw [← Finset.sum_range_succ (fun t => pushIter π t μ) (T + 1),
    Finset.sum_range_succ' (fun t => pushIter π t μ) (T + 1)]
  simp [add_comm]

theorem tvMass_construction (π : Kernel S S) [IsMarkovKernel π] (μ₀ μ₁ R : Measure S)
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure R] (hR : R.bind π = R) (T : ℕ)
    (hB : ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁ ≤ R) :
    tvMass (μ₀ + (∑ t ∈ Finset.range (T + 1), pushIter π t μ₀
        + (R - ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁)).bind π)
      (μ₁ + (∑ t ∈ Finset.range (T + 1), pushIter π t μ₀
        + (R - ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁)))
    ≤ tvMass (pushIter π (T + 1) μ₀) (pushIter π (T + 1) μ₁) := by
  have h0 := shift_sum π T μ₀
  have h1 := shift_sum π T μ₁
  set A := ∑ t ∈ Finset.range (T + 1), pushIter π t μ₀ with hA
  set B := ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁ with hB'
  set p := pushIter π (T + 1) μ₀
  set q := pushIter π (T + 1) μ₁
  have hRB' : (R - B) + B = R := Measure.sub_add_cancel_of_le hB
  set D := R - B with hD
  have hRB : D.bind π + B.bind π = R := by
    rw [← bind_add_measure, hRB', hR]
  have hX : μ₀ + (A + D).bind π + (μ₁ + B.bind π) = (A + R + μ₁) + p := by
    rw [bind_add_measure]
    calc μ₀ + (A.bind π + D.bind π) + (μ₁ + B.bind π)
        = (μ₀ + A.bind π) + (D.bind π + B.bind π) + μ₁ := by abel
      _ = (A + p) + R + μ₁ := by rw [h0, hRB]
      _ = (A + R + μ₁) + p := by abel
  have hY : μ₁ + (A + D) + (μ₁ + B.bind π) = (A + R + μ₁) + q := by
    calc μ₁ + (A + D) + (μ₁ + B.bind π) = μ₁ + A + D + (μ₁ + B.bind π) := by abel
      _ = μ₁ + A + D + (B + q) := by rw [h1]
      _ = μ₁ + A + (D + B) + q := by abel
      _ = (A + R + μ₁) + q := by rw [hRB']; abel
  have hDf : IsFiniteMeasure D := by rw [hD]; infer_instance
  calc tvMass (μ₀ + (A + D).bind π) (μ₁ + (A + D))
      ≤ tvMass (μ₀ + (A + D).bind π + (μ₁ + B.bind π))
          (μ₁ + (A + D) + (μ₁ + B.bind π)) := tvMass_le_add_right _ _ _
    _ = tvMass ((A + R + μ₁) + p) ((A + R + μ₁) + q) := by rw [hX, hY]
    _ ≤ tvMass p q := tvMass_add_left_le _ _ _


/-! ## The transfer operator on densities -/

/-- `φπ⁰ = φ`, `λ`-a.e. -/
theorem transfer_zero_ae (π : Kernel S S) (lam : Measure S) [SigmaFinite lam] {φ : S → ℝ}
    (hφ : AEMeasurable φ lam) : transfer π lam 0 φ =ᵐ[lam] φ := by
  have h1 : (lam.withDensity fun x => ENNReal.ofReal (φ x)).rnDeriv lam
      =ᵐ[lam] fun x => ENNReal.ofReal (φ x) :=
    Measure.rnDeriv_withDensity₀ lam hφ.ennreal_ofReal
  have h2 : (lam.withDensity fun x => ENNReal.ofReal (-φ x)).rnDeriv lam
      =ᵐ[lam] fun x => ENNReal.ofReal (-φ x) :=
    Measure.rnDeriv_withDensity₀ lam hφ.neg.ennreal_ofReal
  filter_upwards [h1, h2] with s hs1 hs2
  simp only [transfer, pushIter_zero]
  rw [hs1, hs2, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 (φ s) with h | h
  · simp [h]
  · simp [h]

/-- **Homogeneity of `γₙ`**: for `φ ∈ L²(λ)` of mean zero, `∫ (φπⁿ)² dλ̂ ≤ γₙ ‖φ‖₂²`. -/
theorem lintegral_transfer_sq_le (π : Kernel S S) [IsMarkovKernel π] (lam lamHat : Measure S)
    [IsFiniteMeasure lam] (hac : lamHat ≪ lam) (n : ℕ) {φ : S → ℝ} (hφm : Measurable φ)
    (hφ : MemLp φ 2 lam) (hφ0 : ∫ s, φ s ∂lam = 0) :
    ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lamHat
      ≤ mixingCoeff π lam lamHat n * eLpNorm φ 2 lam ^ 2 := by
  by_cases h0 : eLpNorm φ 2 lam = 0
  · have hφ0' : φ =ᵐ[lam] 0 := (eLpNorm_eq_zero_iff hφ.1 (by norm_num)).mp h0
    have hw1 : (lam.withDensity fun x => ENNReal.ofReal (φ x)) = 0 := by
      rw [← withDensity_zero (μ := lam)]
      exact withDensity_congr_ae (hφ0'.mono fun x hx => by simp [hx])
    have hw2 : (lam.withDensity fun x => ENNReal.ofReal (-φ x)) = 0 := by
      rw [← withDensity_zero (μ := lam)]
      exact withDensity_congr_ae (hφ0'.mono fun x hx => by simp [hx])
    have htr : transfer π lam n φ = 0 := by
      funext s; simp [transfer, hw1, hw2]
    simp [htr]
  have hfin : eLpNorm φ 2 lam ≠ ∞ := hφ.2.ne
  set c := (eLpNorm φ 2 lam).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos h0 hfin
  have hcn : eLpNorm φ 2 lam = ENNReal.ofReal c := (ENNReal.ofReal_toReal hfin).symm
  set ψ : S → ℝ := fun s => c⁻¹ * φ s with hψ
  have hψm : Measurable ψ := measurable_const.mul hφm
  have hψH : ψ ∈ unitMeanZero lam := by
    refine ⟨hφ.const_mul c⁻¹, ?_, ?_⟩
    · have : ψ = c⁻¹ • φ := rfl
      rw [this, eLpNorm_const_smul, hcn, Real.enorm_eq_ofReal_abs,
        abs_of_pos (inv_pos.mpr hcpos), ← ENNReal.ofReal_mul (inv_pos.mpr hcpos).le,
        inv_mul_cancel₀ hcpos.ne', ENNReal.ofReal_one]
    · simp only [hψ, integral_const_mul, hφ0, mul_zero]
  have hle : ∫⁻ s, ENNReal.ofReal (transfer π lam n ψ s ^ 2) ∂lamHat ≤ mixingCoeff π lam lamHat n :=
    le_iSup₂ (f := fun φ (_ : φ ∈ unitMeanZero lam) =>
      ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lamHat) ψ hψH
  -- `ψ π^n = c⁻¹ (φ π^n)`
  have hφi : Integrable φ lam := hφ.integrable (by norm_num)
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (φ x)) :=
    isFiniteMeasure_withDensity_ofReal hφi.2
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (-φ x)) :=
    isFiniteMeasure_withDensity_ofReal hφi.neg.2
  set r := ENNReal.ofReal c⁻¹ with hr
  have hrtop : r ≠ ∞ := ENNReal.ofReal_ne_top
  have e1 : (fun x => ENNReal.ofReal (ψ x)) = r • fun x => ENNReal.ofReal (φ x) := by
    funext x; simp [hψ, hr, ENNReal.ofReal_mul (inv_pos.mpr hcpos).le]
  have e2 : (fun x => ENNReal.ofReal (-ψ x)) = r • fun x => ENNReal.ofReal (-φ x) := by
    funext x; simp [hψ, hr, ← ENNReal.ofReal_mul (inv_pos.mpr hcpos).le, mul_neg]
  have k1 := Measure.rnDeriv_smul_left_of_ne_top
    (pushIter π n (lam.withDensity fun x => ENNReal.ofReal (φ x))) lam hrtop
  have k2 := Measure.rnDeriv_smul_left_of_ne_top
    (pushIter π n (lam.withDensity fun x => ENNReal.ofReal (-φ x))) lam hrtop
  have htr : transfer π lam n ψ =ᵐ[lam] fun s => c⁻¹ * transfer π lam n φ s := by
    filter_upwards [k1, k2] with s hs1 hs2
    simp only [transfer]
    rw [e1, e2, withDensity_smul _ hφm.ennreal_ofReal, withDensity_smul _ hφm.neg.ennreal_ofReal,
      pushIter_smul, pushIter_smul, hs1, hs2]
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hr,
      ENNReal.toReal_ofReal (inv_pos.mpr hcpos).le]
    ring
  have hint : ∫⁻ s, ENNReal.ofReal (transfer π lam n ψ s ^ 2) ∂lamHat
      = ENNReal.ofReal (c⁻¹ ^ 2) * ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lamHat := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ((hac.ae_eq htr).mono fun s hs => ?_)
    simp only; rw [hs, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hint] at hle
  have hcc : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (c⁻¹ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow, mul_inv_cancel₀ hcpos.ne', one_pow,
      ENNReal.ofReal_one]
  calc ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lamHat
      = ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (c⁻¹ ^ 2)
          * ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lamHat) := by
        rw [← mul_assoc, hcc, one_mul]
    _ ≤ ENNReal.ofReal (c ^ 2) * mixingCoeff π lam lamHat n := by gcongr
    _ = mixingCoeff π lam lamHat n * eLpNorm φ 2 lam ^ 2 := by
        rw [mul_comm, hcn, ENNReal.ofReal_pow hcpos.le]

/-! ## An infinite invariant measure forces a trivial `λ` -/

/-- If `λ̂(𝒮) = ∞` while `γ₀ < ∞` (general form: only `γ₀ < ∞` is assumed), every measurable set
is `λ`-null or `λ`-conull. -/
theorem trivial_of_lamHat_univ_eq_top_of_ne_top (π : Kernel S S) [IsMarkovKernel π]
    (lam lamHat : Measure S) [IsFiniteMeasure lam] (hac : lamHat ≪ lam) (hγ0 : mixingCoeff π lam lamHat 0 ≠ ∞)
    (htop : lamHat Set.univ = ∞) {A : Set S} (hA : MeasurableSet A) : lam A = 0 ∨ lam Aᶜ = 0 := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hA0, hAc0⟩ := hcon
  set c₁ := (lam Aᶜ).toReal with hc₁
  set c₂ := (lam A).toReal with hc₂
  have hc₁p : 0 < c₁ := ENNReal.toReal_pos hAc0 (measure_ne_top _ _)
  have hc₂p : 0 < c₂ := ENNReal.toReal_pos hA0 (measure_ne_top _ _)
  set φ : S → ℝ := A.piecewise (fun _ => c₁) (fun _ => -c₂) with hφ
  have hφm : Measurable φ := Measurable.piecewise hA measurable_const measurable_const
  have hφb : ∀ s, |φ s| ≤ max c₁ c₂ := by
    intro s
    by_cases h : s ∈ A
    · simp [hφ, h, abs_of_pos hc₁p]
    · simp [hφ, h, abs_of_pos hc₂p]
  have hφL : MemLp φ 2 lam := MemLp.of_bound hφm.aestronglyMeasurable (max c₁ c₂)
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hφb s)
  have hφ0 : ∫ s, φ s ∂lam = 0 := by
    rw [hφ, integral_piecewise hA (integrableOn_const (measure_ne_top _ _))
      (integrableOn_const (measure_ne_top _ _))]
    simp only [integral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, measureReal_def]
    rw [← hc₁, ← hc₂]
    ring
  have hle := lintegral_transfer_sq_le π lam lamHat hac 0 hφm hφL hφ0
  have hfin : ∫⁻ s, ENNReal.ofReal (transfer π lam 0 φ s ^ 2) ∂lamHat ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hγ0 (ENNReal.pow_ne_top hφL.2.ne)) hle
  have hae : transfer π lam 0 φ =ᵐ[lamHat] φ := hac.ae_le (transfer_zero_ae π lam hφm.aemeasurable)
  set m := min c₁ c₂ ^ 2 with hm
  have hmpos : 0 < m := by positivity
  have hmle : ∀ s, m ≤ φ s ^ 2 := by
    intro s
    have h0 : 0 ≤ min c₁ c₂ := le_min hc₁p.le hc₂p.le
    by_cases h : s ∈ A
    · simp only [hφ, Set.piecewise_eq_of_mem _ _ _ h, hm]
      exact pow_le_pow_left₀ h0 (min_le_left _ _) 2
    · simp only [hφ, Set.piecewise_eq_of_notMem _ _ _ h, hm, neg_sq]
      exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
  have hlow : ENNReal.ofReal m * lamHat Set.univ
      ≤ ∫⁻ s, ENNReal.ofReal (transfer π lam 0 φ s ^ 2) ∂lamHat := by
    rw [← lintegral_const]
    exact lintegral_mono_ae (hae.mono fun s hs => by rw [hs]; exact ENNReal.ofReal_le_ofReal (hmle s))
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hmpos).ne'] at hlow
  exact hfin (top_le_iff.mp hlow)

/-- If `λ̂(𝒮) = ∞` while `γ₀ < ∞`, every measurable set is `λ`-null or `λ`-conull. -/
theorem trivial_of_lamHat_univ_eq_top (π : Kernel S S) [IsMarkovKernel π] (lam lamHat : Measure S)
    [IsFiniteMeasure lam] (hac : lamHat ≪ lam) (hsum : ∑' n, mixingCoeff π lam lamHat n ≠ ∞)
    (htop : lamHat Set.univ = ∞) {A : Set S} (hA : MeasurableSet A) : lam A = 0 ∨ lam Aᶜ = 0 :=
  trivial_of_lamHat_univ_eq_top_of_ne_top π lam lamHat hac
    (ne_top_of_le_ne_top hsum (ENNReal.le_tsum 0)) htop hA

/-- On a trivial `λ`, two probability measures `≪ λ` coincide. -/
theorem eq_of_trivial (lam : Measure S) (h : ∀ A, MeasurableSet A → lam A = 0 ∨ lam Aᶜ = 0)
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : μ ≪ lam)
    (hν : ν ≪ lam) : μ = ν := by
  ext A hA
  rcases h A hA with h0 | h0
  · rw [hμ h0, hν h0]
  · rw [(prob_compl_eq_zero_iff hA).mp (hμ h0), (prob_compl_eq_zero_iff hA).mp (hν h0)]

/-! ## Truncating the initial and terminal densities -/

/-- A probability measure `F ≪ λ` is `δ`-close in total variation to a probability measure with a
density bounded by `K` and by `K dλ̂/dλ` (truncate `dF/dλ` at `min(n, n dλ̂/dλ)`, renormalize). -/
theorem exists_truncation (lam lamHat : Measure S) [IsFiniteMeasure lam] [IsFiniteMeasure lamHat]
    (hac' : lam ≪ lamHat) (F : Measure S) [IsProbabilityMeasure F] (hF : F ≪ lam) {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∃ a : S → ℝ≥0∞, Measurable a ∧ ∃ K : ℝ≥0, (∀ s, a s ≤ K) ∧
      (∀ s, a s ≤ K * lamHat.rnDeriv lam s) ∧ ∫⁻ s, a s ∂lam = 1 ∧
      tvMass F (lam.withDensity a) < δ := by
  set f₀ := F.rnDeriv lam with hf₀
  set g := lamHat.rnDeriv lam with hg
  have hf₀m : Measurable f₀ := Measure.measurable_rnDeriv _ _
  have hgm : Measurable g := Measure.measurable_rnDeriv _ _
  have hFf : lam.withDensity f₀ = F := Measure.withDensity_rnDeriv_eq F lam hF
  have hint : ∫⁻ s, f₀ s ∂lam = 1 := by
    rw [← Measure.restrict_univ (μ := lam), ← withDensity_apply _ MeasurableSet.univ, hFf,
      measure_univ]
  set tr : ℕ → S → ℝ≥0∞ := fun n s => min (min (f₀ s) ((n : ℝ≥0∞) * g s)) n with htr
  have htrm : ∀ n, Measurable (tr n) := fun n =>
    (hf₀m.min (measurable_const.mul hgm)).min measurable_const
  have htrle : ∀ n s, tr n s ≤ f₀ s := fun n s => (min_le_left _ _).trans (min_le_left _ _)
  have hlim : ∀ᵐ s ∂lam, Tendsto (fun n => tr n s) atTop (𝓝 (f₀ s)) := by
    filter_upwards [Measure.rnDeriv_pos' hac'] with s hs
    have h1 : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * g s) atTop (𝓝 ∞) := by
      have := ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top (b := g s)
        (Or.inl ENNReal.top_ne_zero)
      rwa [ENNReal.top_mul hs.ne'] at this
    have h2 := ((tendsto_const_nhds (x := f₀ s)).min h1).min ENNReal.tendsto_nat_nhds_top
    simpa using h2
  have hmono : ∀ᵐ s ∂lam, Monotone fun n => tr n s := ae_of_all _ fun s m n hmn => by
    have : (m : ℝ≥0∞) ≤ n := by exact_mod_cast hmn
    exact min_le_min (min_le_min le_rfl (by gcongr)) this
  have hZ : Tendsto (fun n => ∫⁻ s, tr n s ∂lam) atTop (𝓝 1) := by
    rw [← hint]
    exact lintegral_tendsto_of_tendsto_of_monotone (fun n => (htrm n).aemeasurable) hmono hlim
  have hZ' : Tendsto (fun n => 1 - ∫⁻ s, tr n s ∂lam) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds hZ (Or.inl ENNReal.one_ne_top)
    simpa using this
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  obtain ⟨n, hn1, hn2⟩ := ((hZ'.eventually (gt_mem_nhds hδ2)).and
    (hZ.eventually (lt_mem_nhds (show (0 : ℝ≥0∞) < 1 from one_pos)))).exists
  set Z := ∫⁻ s, tr n s ∂lam with hZdef
  have hZle : Z ≤ 1 := hint ▸ lintegral_mono (htrle n)
  have hZ0 : Z ≠ 0 := hn2.ne'
  have hZtop : Z ≠ ∞ := (hZle.trans_lt ENNReal.one_lt_top).ne
  have hZi : Z⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hZ0
  set a : S → ℝ≥0∞ := fun s => Z⁻¹ * tr n s with ha
  have ham : Measurable a := measurable_const.mul (htrm n)
  set K : ℝ≥0 := (Z⁻¹ * n).toNNReal with hK
  have hKc : (K : ℝ≥0∞) = Z⁻¹ * n := ENNReal.coe_toNNReal (ENNReal.mul_ne_top hZi
    (ENNReal.natCast_ne_top n))
  have ha1 : ∫⁻ s, a s ∂lam = 1 := by
    rw [ha, lintegral_const_mul _ (htrm n), ← hZdef, ENNReal.inv_mul_cancel hZ0 hZtop]
  have hle1 : lam.withDensity (tr n) ≤ F :=
    hFf ▸ withDensity_mono (ae_of_all _ fun s => htrle n s)
  have hone : (1 : ℝ≥0∞) ≤ Z⁻¹ := ENNReal.one_le_inv.mpr hZle
  have hle2 : lam.withDensity (tr n) ≤ lam.withDensity a :=
    withDensity_mono (ae_of_all _ fun s => le_mul_of_one_le_left bot_le hone)
  haveI : IsFiniteMeasure (lam.withDensity (tr n)) := isFiniteMeasure_of_le F hle1
  haveI : IsFiniteMeasure (lam.withDensity a) := isFiniteMeasure_withDensity (by rw [ha1]; simp)
  have hw1 : lam.withDensity (tr n) Set.univ = Z := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hwa : lam.withDensity a Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ha1]
  refine ⟨a, ham, K, fun s => ?_, fun s => ?_, ha1, ?_⟩
  · rw [hKc]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) bot_le
  · rw [hKc, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (min_le_right _ _)) bot_le
  · calc tvMass F (lam.withDensity a)
        ≤ tvMass F (lam.withDensity (tr n)) + tvMass (lam.withDensity (tr n)) (lam.withDensity a) :=
          tvMass_triangle _ _ _
      _ = (1 - Z) + (1 - Z) := by
          rw [tvMass_comm, tvMass_of_le hle1, tvMass_of_le hle2, hw1, hwa, measure_univ]
      _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hn1 hn1
      _ = δ := ENNReal.add_halves δ

/-! ## Mixing in total variation -/

theorem ofReal_toReal_sub_toReal {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    ENNReal.ofReal (x.toReal - y.toReal) = x - y := by
  rcases le_total x y with h | h
  · rw [tsub_eq_zero_of_le h, ENNReal.ofReal_eq_zero, sub_nonpos]
    exact ENNReal.toReal_mono hy h
  · rw [← ENNReal.toReal_sub_of_le h hx, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hx)]

theorem tsub_add_tsub_eq_ofReal_abs {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    (x - y) + (y - x) = ENNReal.ofReal |x.toReal - y.toReal| := by
  rcases le_total x y with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, ← ofReal_toReal_sub_toReal hy hx, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hy h))]
  · rw [tsub_eq_zero_of_le h, add_zero, ← ofReal_toReal_sub_toReal hx hy,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hx h))]

theorem le_inv_add_mul_sq (e : ℝ≥0∞) {k : ℕ} (hk : 1 ≤ k) :
    e ≤ (k : ℝ≥0∞)⁻¹ + k * e ^ 2 := by
  by_cases he : e ≤ (k : ℝ≥0∞)⁻¹
  · exact he.trans le_self_add
  push Not at he
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkt : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have h1 : 1 ≤ (k : ℝ≥0∞) * e := by
    calc (1 : ℝ≥0∞) = k * (k : ℝ≥0∞)⁻¹ := (ENNReal.mul_inv_cancel hk0 hkt).symm
      _ ≤ k * e := by gcongr
  calc e = 1 * e := (one_mul e).symm
    _ ≤ (k * e) * e := by gcongr
    _ = k * e ^ 2 := by ring
    _ ≤ (k : ℝ≥0∞)⁻¹ + k * e ^ 2 := le_add_self

/-- **`γₙ → 0` gives mixing in total variation** (general form), for two densities of equal mass
bounded by `K` and by `K dλ̂/dλ`. -/
theorem exists_tvMass_pushIter_lt_of_tendsto (π : Kernel S S) [IsMarkovKernel π]
    (lam lamHat : Measure S) [IsFiniteMeasure lam] [IsFiniteMeasure lamHat] (hinv : lamHat.bind π = lamHat)
    (hac : lamHat ≪ lam) (hγ : Tendsto (mixingCoeff π lam lamHat) atTop (𝓝 0)) {a b : S → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (K : ℝ≥0) (haK : ∀ s, a s ≤ K) (hbK : ∀ s, b s ≤ K)
    (hag : ∀ s, a s ≤ K * lamHat.rnDeriv lam s) (hbg : ∀ s, b s ≤ K * lamHat.rnDeriv lam s)
    (hab : ∫⁻ s, a s ∂lam = ∫⁻ s, b s ∂lam) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ t, tvMass (pushIter π t (lam.withDensity a)) (pushIter π t (lam.withDensity b)) < η := by
  set g := lamHat.rnDeriv lam with hg
  have hgm : Measurable g := Measure.measurable_rnDeriv _ _
  have hlamHat : lam.withDensity g = lamHat := Measure.withDensity_rnDeriv_eq lamHat lam hac
  set Kh : Measure S := (K : ℝ≥0∞) • lamHat with hKh
  haveI : IsFiniteMeasure Kh := ⟨by
    rw [hKh, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)⟩
  have hKhinv : ∀ t, pushIter π t Kh = Kh := fun t => by
    rw [hKh, pushIter_smul, pushIter_of_bind_eq π hinv]
  have hdom : ∀ {c : S → ℝ≥0∞}, (∀ s, c s ≤ K * g s) → lam.withDensity c ≤ Kh := by
    intro c hc
    rw [hKh, ← hlamHat, ← withDensity_smul _ hgm]
    exact withDensity_mono (ae_of_all _ fun s => by simpa using hc s)
  have hKhac : Kh ≪ lam := (Measure.AbsolutelyContinuous.rfl.smul_left _).trans hac
  -- the signed density `φ = a - b`
  have hafin : ∀ s, a s ≠ ∞ := fun s => ((haK s).trans_lt ENNReal.coe_lt_top).ne
  have hbfin : ∀ s, b s ≠ ∞ := fun s => ((hbK s).trans_lt ENNReal.coe_lt_top).ne
  set φ : S → ℝ := fun s => (a s).toReal - (b s).toReal with hφdef
  have hφm : Measurable φ := ha.ennreal_toReal.sub hb.ennreal_toReal
  have hφL : MemLp φ 2 lam := by
    refine MemLp.of_bound hφm.aestronglyMeasurable K (ae_of_all _ fun s => ?_)
    have h1 : (a s).toReal ≤ K := ENNReal.toReal_le_coe_of_le_coe (haK s)
    have h2 : (b s).toReal ≤ K := ENNReal.toReal_le_coe_of_le_coe (hbK s)
    have h3 : 0 ≤ (a s).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (b s).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hKfin : ∫⁻ _, (K : ℝ≥0∞) ∂lam ≠ ∞ := by
    rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  have hafi : ∫⁻ s, a s ∂lam ≠ ∞ := ne_top_of_le_ne_top hKfin (lintegral_mono haK)
  have hbfi : ∫⁻ s, b s ∂lam ≠ ∞ := ne_top_of_le_ne_top hKfin (lintegral_mono hbK)
  have hφ0 : ∫ s, φ s ∂lam = 0 := by
    rw [hφdef, integral_sub (integrable_toReal_of_lintegral_ne_top ha.aemeasurable hafi)
      (integrable_toReal_of_lintegral_ne_top hb.aemeasurable hbfi),
      integral_toReal ha.aemeasurable (ae_of_all _ fun s => (hafin s).lt_top),
      integral_toReal hb.aemeasurable (ae_of_all _ fun s => (hbfin s).lt_top), hab, sub_self]
  have hpos : (fun x => ENNReal.ofReal (φ x)) = fun x => a x - b x :=
    funext fun x => ofReal_toReal_sub_toReal (hafin x) (hbfin x)
  have hneg : (fun x => ENNReal.ofReal (-φ x)) = fun x => b x - a x :=
    funext fun x => by
      simp only [hφdef, neg_sub]; exact ofReal_toReal_sub_toReal (hbfin x) (hafin x)
  -- the positive and negative parts, and the balance `a λ + V₀ = b λ + U₀`
  set U₀ := lam.withDensity fun x => a x - b x with hU₀
  set V₀ := lam.withDensity fun x => b x - a x with hV₀
  have hU₀le : U₀ ≤ Kh := (withDensity_mono (ae_of_all _ fun s => tsub_le_self)).trans (hdom hag)
  have hV₀le : V₀ ≤ Kh := (withDensity_mono (ae_of_all _ fun s => tsub_le_self)).trans (hdom hbg)
  haveI : IsFiniteMeasure U₀ := isFiniteMeasure_of_le Kh hU₀le
  haveI : IsFiniteMeasure V₀ := isFiniteMeasure_of_le Kh hV₀le
  haveI : IsFiniteMeasure (lam.withDensity a) := isFiniteMeasure_of_le Kh (hdom hag)
  haveI : IsFiniteMeasure (lam.withDensity b) := isFiniteMeasure_of_le Kh (hdom hbg)
  have hbal : lam.withDensity a + V₀ = lam.withDensity b + U₀ := by
    rw [hV₀, hU₀, ← withDensity_add_left ha, ← withDensity_add_left hb]
    congr 1; funext x
    simp only [Pi.add_apply]
    rcases le_total (a x) (b x) with h | h
    · rw [tsub_eq_zero_of_le h, add_zero, add_tsub_cancel_of_le h]
    · rw [tsub_eq_zero_of_le h, add_zero, add_tsub_cancel_of_le h]
  -- the pushed parts and their densities
  have hUt : ∀ t, pushIter π t U₀ ≤ Kh := fun t => (pushIter_mono π t hU₀le).trans_eq (hKhinv t)
  have hVt : ∀ t, pushIter π t V₀ ≤ Kh := fun t => (pushIter_mono π t hV₀le).trans_eq (hKhinv t)
  set u : ℕ → S → ℝ≥0∞ := fun t => (pushIter π t U₀).rnDeriv lam with hu_def
  set v : ℕ → S → ℝ≥0∞ := fun t => (pushIter π t V₀).rnDeriv lam with hv_def
  have hum : ∀ t, Measurable (u t) := fun t => Measure.measurable_rnDeriv _ _
  have hvm : ∀ t, Measurable (v t) := fun t => Measure.measurable_rnDeriv _ _
  have hu : ∀ t, lam.withDensity (u t) = pushIter π t U₀ := fun t =>
    Measure.withDensity_rnDeriv_eq _ _ ((Measure.absolutelyContinuous_of_le (hUt t)).trans hKhac)
  have hv : ∀ t, lam.withDensity (v t) = pushIter π t V₀ := fun t =>
    Measure.withDensity_rnDeriv_eq _ _ ((Measure.absolutelyContinuous_of_le (hVt t)).trans hKhac)
  have htr : ∀ t, transfer π lam t φ = fun s => (u t s).toReal - (v t s).toReal := by
    intro t; funext s; simp only [transfer, hpos, hneg, hu_def, hv_def, hU₀, hV₀]
  set e : ℕ → S → ℝ≥0∞ := fun t s => (u t s - v t s) + (v t s - u t s) with he
  have hem : ∀ t, Measurable (e t) := fun t =>
    ((hum t).sub (hvm t)).add ((hvm t).sub (hum t))
  -- step 1: the total variation is `∫ |φπᵗ| dλ`
  have hstep1 : ∀ t, tvMass (pushIter π t (lam.withDensity a)) (pushIter π t (lam.withDensity b))
      ≤ ∫⁻ s, e t s ∂lam := by
    intro t
    calc tvMass (pushIter π t (lam.withDensity a)) (pushIter π t (lam.withDensity b))
        ≤ tvMass (pushIter π t (lam.withDensity a) + pushIter π t V₀)
            (pushIter π t (lam.withDensity b) + pushIter π t V₀) := tvMass_le_add_right _ _ _
      _ = tvMass (pushIter π t (lam.withDensity b) + pushIter π t U₀)
            (pushIter π t (lam.withDensity b) + pushIter π t V₀) := by
          rw [← pushIter_add, hbal, pushIter_add]
      _ ≤ tvMass (pushIter π t U₀) (pushIter π t V₀) := tvMass_add_left_le _ _ _
      _ = tvMass (lam.withDensity (u t)) (lam.withDensity (v t)) := by rw [hu, hv]
      _ ≤ ∫⁻ s, e t s ∂lam := tvMass_withDensity_le lam (hum t) (hvm t)
  -- step 2: `∫ e² dλ̂ ≤ γₜ ‖φ‖₂²`
  set N := eLpNorm φ 2 lam ^ 2 with hN
  have hNfin : N ≠ ∞ := ENNReal.pow_ne_top hφL.2.ne
  have hstep2 : ∀ t, ∫⁻ s, e t s ^ 2 ∂lamHat ≤ mixingCoeff π lam lamHat t * N := by
    intro t
    refine le_trans (le_of_eq (lintegral_congr_ae ?_))
      (lintegral_transfer_sq_le π lam lamHat hac t hφm hφL hφ0)
    have hfin : ∀ᵐ s ∂lam, u t s < ∞ ∧ v t s < ∞ :=
      (Measure.rnDeriv_lt_top _ _).and (Measure.rnDeriv_lt_top _ _)
    have hfin' : ∀ᵐ s ∂lamHat, u t s < ∞ ∧ v t s < ∞ := hac.ae_le hfin
    refine hfin'.mono fun s hs => ?_
    rw [he, htr t]
    simp only
    rw [tsub_add_tsub_eq_ofReal_abs hs.1.ne hs.2.ne, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  -- step 3: the split along `{g < m⁻¹}`
  have hstep3 : ∀ t m k : ℕ, 1 ≤ m → 1 ≤ k → ∫⁻ s, e t s ∂lam
      ≤ 2 * K * ((m : ℝ≥0∞)⁻¹ * lam Set.univ)
        + m * ((k : ℝ≥0∞)⁻¹ * lamHat Set.univ + k * (mixingCoeff π lam lamHat t * N)) := by
    intro t m k hm hk
    have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hmt : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
    set A := {s | g s < (m : ℝ≥0∞)⁻¹} with hA
    have hAm : MeasurableSet A := measurableSet_lt hgm measurable_const
    have hpt : ∀ s, e t s ≤ A.indicator (fun s => u t s + v t s) s
        + (m * g s) * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) := by
      intro s
      by_cases hs : s ∈ A
      · rw [Set.indicator_of_mem hs]
        exact le_add_right (add_le_add tsub_le_self tsub_le_self)
      · rw [Set.indicator_of_notMem hs, zero_add]
        have hgs : (m : ℝ≥0∞)⁻¹ ≤ g s := not_lt.mp hs
        have h1 : 1 ≤ (m : ℝ≥0∞) * g s := by
          calc (1 : ℝ≥0∞) = m * (m : ℝ≥0∞)⁻¹ := (ENNReal.mul_inv_cancel hm0 hmt).symm
            _ ≤ m * g s := by gcongr
        calc e t s = 1 * e t s := (one_mul _).symm
          _ ≤ (m * g s) * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) :=
            mul_le_mul' h1 (le_inv_add_mul_sq _ hk)
    have hFm : Measurable fun s => (k : ℝ≥0∞)⁻¹ + k * e t s ^ 2 :=
      measurable_const.add (measurable_const.mul ((hem t).pow_const 2))
    have hI1 : ∫⁻ s, A.indicator (fun s => u t s + v t s) s ∂lam ≤ 2 * K * ((m : ℝ≥0∞)⁻¹ * lam Set.univ) := by
      rw [lintegral_indicator hAm, ← withDensity_apply _ hAm]
      change (lam.withDensity (u t + v t)) A ≤ _
      rw [withDensity_add_left (hum t), hu, hv]
      have hlamA : lamHat A ≤ (m : ℝ≥0∞)⁻¹ * lam Set.univ := by
        rw [← hlamHat, withDensity_apply _ hAm]
        calc ∫⁻ s in A, g s ∂lam ≤ ∫⁻ _ in A, (m : ℝ≥0∞)⁻¹ ∂lam :=
              lintegral_mono_ae ((ae_restrict_mem hAm).mono fun s hs => le_of_lt hs)
          _ = (m : ℝ≥0∞)⁻¹ * lam A := setLIntegral_const _ _
          _ ≤ (m : ℝ≥0∞)⁻¹ * lam Set.univ := by gcongr; exact Set.subset_univ _
      calc (pushIter π t U₀ + pushIter π t V₀) A ≤ (Kh + Kh) A := add_le_add (hUt t A) (hVt t A)
        _ = 2 * K * lamHat A := by
            rw [Measure.add_apply, hKh, Measure.smul_apply, smul_eq_mul]; ring
        _ ≤ 2 * K * ((m : ℝ≥0∞)⁻¹ * lam Set.univ) := by gcongr
    have hI2 : ∫⁻ s, (m * g s) * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) ∂lam
        = m * ((k : ℝ≥0∞)⁻¹ * lamHat Set.univ + k * ∫⁻ s, e t s ^ 2 ∂lamHat) := by
      have hwd : ∫⁻ s, g s * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) ∂lam
          = ∫⁻ s, ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) ∂lamHat := by
        rw [← hlamHat, lintegral_withDensity_eq_lintegral_mul lam hgm hFm]; rfl
      simp_rw [mul_assoc (m : ℝ≥0∞)]
      rw [lintegral_const_mul _ (hgm.mul hFm), hwd, lintegral_add_left measurable_const,
        lintegral_const, lintegral_const_mul _ ((hem t).pow_const 2), mul_comm _ (lamHat Set.univ)]
    calc ∫⁻ s, e t s ∂lam
        ≤ ∫⁻ s, (A.indicator (fun s => u t s + v t s) s
            + (m * g s) * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2)) ∂lam := lintegral_mono hpt
      _ = ∫⁻ s, A.indicator (fun s => u t s + v t s) s ∂lam
            + ∫⁻ s, (m * g s) * ((k : ℝ≥0∞)⁻¹ + k * e t s ^ 2) ∂lam :=
          lintegral_add_left (((hum t).add (hvm t)).indicator hAm) _
      _ ≤ 2 * K * ((m : ℝ≥0∞)⁻¹ * lam Set.univ)
            + m * ((k : ℝ≥0∞)⁻¹ * lamHat Set.univ + k * (mixingCoeff π lam lamHat t * N)) := by
          rw [hI2]
          gcongr
          exact hstep2 t
  -- step 4: the choice of `m`, `k`, `t`
  have hη3 : 0 < η / 3 := ENNReal.div_pos hη.ne' ENNReal.ofNat_ne_top
  have hC1 : 2 * (K : ℝ≥0∞) * lam Set.univ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)
      (measure_ne_top _ _)
  have hT1 : Tendsto (fun m : ℕ => 2 * (K : ℝ≥0∞) * lam Set.univ * (m : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC1)
  obtain ⟨m, hm1, hm⟩ := ((eventually_ge_atTop 1).and
    (hT1.eventually (gt_mem_nhds hη3))).exists
  have hC2 : (m : ℝ≥0∞) * lamHat Set.univ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_ne_top _ _)
  have hT2 : Tendsto (fun k : ℕ => (m : ℝ≥0∞) * lamHat Set.univ * (k : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC2)
  obtain ⟨k, hk1, hk⟩ := ((eventually_ge_atTop 1).and
    (hT2.eventually (gt_mem_nhds hη3))).exists
  have hC3 : (m : ℝ≥0∞) * k * N ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m)
      (ENNReal.natCast_ne_top k)) hNfin
  have hT3 : Tendsto (fun t => (m : ℝ≥0∞) * k * N * mixingCoeff π lam lamHat t) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hγ (Or.inr hC3)
  obtain ⟨t, ht⟩ := (hT3.eventually (gt_mem_nhds hη3)).exists
  refine ⟨t, (hstep1 t).trans_lt ((hstep3 t m k hm1 hk1).trans_lt ?_)⟩
  calc 2 * K * ((m : ℝ≥0∞)⁻¹ * lam Set.univ)
        + m * ((k : ℝ≥0∞)⁻¹ * lamHat Set.univ + k * (mixingCoeff π lam lamHat t * N))
      = 2 * K * lam Set.univ * (m : ℝ≥0∞)⁻¹ + (m * lamHat Set.univ * (k : ℝ≥0∞)⁻¹
          + m * k * N * mixingCoeff π lam lamHat t) := by ring
    _ < η / 3 + (η / 3 + η / 3) := ENNReal.add_lt_add hm (ENNReal.add_lt_add hk ht)
    _ = η := by rw [← add_assoc, ENNReal.add_thirds]

/-- **Summable `L²`-mixing gives mixing in total variation**, for two densities of equal mass
bounded by `K` and by `K dλ̂/dλ`. -/
theorem exists_tvMass_pushIter_lt (π : Kernel S S) [IsMarkovKernel π] (lam lamHat : Measure S)
    [IsFiniteMeasure lam] [IsFiniteMeasure lamHat] (hinv : lamHat.bind π = lamHat)
    (hac : lamHat ≪ lam) (hsum : ∑' n, mixingCoeff π lam lamHat n ≠ ∞) {a b : S → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (K : ℝ≥0) (haK : ∀ s, a s ≤ K) (hbK : ∀ s, b s ≤ K)
    (hag : ∀ s, a s ≤ K * lamHat.rnDeriv lam s) (hbg : ∀ s, b s ≤ K * lamHat.rnDeriv lam s)
    (hab : ∫⁻ s, a s ∂lam = ∫⁻ s, b s ∂lam) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ t, tvMass (pushIter π t (lam.withDensity a)) (pushIter π t (lam.withDensity b)) < η :=
  exists_tvMass_pushIter_lt_of_tendsto π lam lamHat hinv hac
    (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum) ha hb K haK hbK hag hbg hab hη

/-! ## The main theorem -/

/-- **The master universality theorem, general form**: summability of the mixing coefficients
(`def:summably_mixing`) is replaced by `γ₀ < ∞` and `γₙ → 0`, with the same invariant `λ̂ ~ λ`.
This is all the proof of `main_universality` uses (finding on `main.tex:775`). -/
theorem main_universality_of_tendsto (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (lamHat : Measure S) (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam)
    (hac' : lam ≪ lamHat) (hγ0 : mixingCoeff π lam lamHat 0 ≠ ∞)
    (hγ : Tendsto (mixingCoeff π lam lamHat) atTop (𝓝 0)) (Finit Fterm : Measure S)
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure Fterm] (hinit : Finit ≪ lam)
    (hterm : Fterm ≪ lam) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧ MemLp fout 2 lam ∧
      initialError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        + terminalError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        < ε := by
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'top : ε' ≠ ∞ := ((min_le_right ε 1).trans_lt ENNReal.one_lt_top).ne
  have hε'le : ε' ≤ ε := min_le_left _ _
  suffices h : ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧
      MemLp fout 2 lam ∧
      tvMass (Finit + inflow π (lam.withDensity fun s => ENNReal.ofReal (fout s)))
        (Fterm + lam.withDensity fun s => ENNReal.ofReal (fout s)) < ε' by
    obtain ⟨fout, h1, h2, h3, h4⟩ := h
    exact ⟨fout, h1, h2, h3, by rw [errors_eq_tvMass]; exact h4.trans_le hε'le⟩
  by_cases htop : lamHat Set.univ = ∞
  · -- an infinite invariant measure: `λ` is trivial and `F_init = F_term`
    have htriv := fun A hA =>
      trivial_of_lamHat_univ_eq_top_of_ne_top π lam lamHat hac hγ0 htop (A := A) hA
    have heq : Finit = Fterm := eq_of_trivial lam htriv Finit Fterm hinit hterm
    refine ⟨fun _ => 0, fun _ => le_rfl, ⟨0, fun _ => le_rfl⟩, MemLp.zero, ?_⟩
    have h0 : (lam.withDensity fun _ => ENNReal.ofReal (0 : ℝ)) = 0 := by
      simp only [ENNReal.ofReal_zero]; exact withDensity_zero
    rw [h0, heq, inflow, Measure.bind_zero_left, add_zero]
    simpa [tvMass] using hε'pos
  haveI : IsFiniteMeasure lamHat := ⟨lt_top_iff_ne_top.mpr htop⟩
  set δ := ε' / 5 with hδ
  have hδpos : 0 < δ := ENNReal.div_pos hε'pos.ne' (by norm_num)
  have h5δ : δ + δ + δ + δ + δ ≤ ε' := by
    have : δ + δ + δ + δ + δ = 5 * (ε' / 5) := by rw [hδ]; ring
    rw [this]; exact ENNReal.mul_div_le
  obtain ⟨a, ham, Ka, haK, hag, ha1, hFa⟩ := exists_truncation lam lamHat hac' Finit hinit hδpos
  obtain ⟨b, hbm, Kb, hbK, hbg, hb1, hFb⟩ := exists_truncation lam lamHat hac' Fterm hterm hδpos
  set K : ℝ≥0 := max Ka Kb with hK
  have hKa : (Ka : ℝ≥0∞) ≤ K := by exact_mod_cast le_max_left Ka Kb
  have hKb : (Kb : ℝ≥0∞) ≤ K := by exact_mod_cast le_max_right Ka Kb
  set g := lamHat.rnDeriv lam with hg
  have haK' : ∀ s, a s ≤ K := fun s => (haK s).trans hKa
  have hbK' : ∀ s, b s ≤ K := fun s => (hbK s).trans hKb
  have hag' : ∀ s, a s ≤ K * g s := fun s => (hag s).trans (by gcongr)
  have hbg' : ∀ s, b s ≤ K * g s := fun s => (hbg s).trans (by gcongr)
  have hlamHat : lam.withDensity g = lamHat := Measure.withDensity_rnDeriv_eq lamHat lam hac
  set μ₀ := lam.withDensity a with hμ₀
  set μ₁ := lam.withDensity b with hμ₁
  haveI : IsProbabilityMeasure μ₀ :=
    ⟨by rw [hμ₀, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ha1]⟩
  haveI : IsProbabilityMeasure μ₁ :=
    ⟨by rw [hμ₁, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hb1]⟩
  obtain ⟨T, hT0⟩ := exists_tvMass_pushIter_lt_of_tendsto π lam lamHat hinv hac hγ ham hbm K haK'
    hbK' hag' hbg' (ha1.trans hb1.symm) hδpos
  have hT : tvMass (pushIter π (T + 1) μ₀) (pushIter π (T + 1) μ₁) < δ := by
    rw [pushIter_succ, pushIter_succ]; exact (tvMass_bind_le π _ _).trans_lt hT0
  -- domination by `K λ̂`, preserved by the kernel
  have hdom : ∀ {c : S → ℝ≥0∞}, (∀ s, c s ≤ K * g s) → lam.withDensity c ≤ (K : ℝ≥0∞) • lamHat := by
    intro c hc
    rw [← hlamHat, ← withDensity_smul _ (Measure.measurable_rnDeriv _ _)]
    exact withDensity_mono (ae_of_all _ fun s => by simpa using hc s)
  have hpush : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • lamHat → ∀ t,
      pushIter π t μ ≤ (K : ℝ≥0∞) • lamHat := by
    intro μ hμ t
    calc pushIter π t μ ≤ pushIter π t ((K : ℝ≥0∞) • lamHat) := pushIter_mono π t hμ
      _ = (K : ℝ≥0∞) • lamHat := by rw [pushIter_smul, pushIter_of_bind_eq π hinv]
  set R : Measure S := ((T + 1 : ℕ) * (K : ℝ≥0∞)) • lamHat with hRdef
  have hR : R.bind π = R := by rw [hRdef, Measure.bind_smul, hinv]
  haveI : IsFiniteMeasure R := ⟨by
    rw [hRdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.coe_lt_top)
      (measure_lt_top _ _)⟩
  have hsumle : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • lamHat →
      ∑ t ∈ Finset.range (T + 1), pushIter π t μ ≤ R := by
    intro μ hμ
    calc ∑ t ∈ Finset.range (T + 1), pushIter π t μ
        ≤ (Finset.range (T + 1)).card • ((K : ℝ≥0∞) • lamHat) :=
          Finset.sum_le_card_nsmul _ _ _ fun t _ => hpush hμ t
      _ = R := by
          rw [Finset.card_range, hRdef, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  have hB := hsumle (hdom hbg')
  have hA := hsumle (hdom hag')
  set F := ∑ t ∈ Finset.range (T + 1), pushIter π t μ₀
    + (R - ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁) with hFdef
  have hFconstr := tvMass_construction π μ₀ μ₁ R hR T hB
  rw [← hFdef] at hFconstr
  have hFle : F ≤ R + R := add_le_add hA Measure.sub_le
  haveI : IsFiniteMeasure F := isFiniteMeasure_of_le (R + R) hFle
  have hRac : R ≪ lam := (Measure.AbsolutelyContinuous.rfl.smul_left _).trans hac
  have hFac : F ≪ lam :=
    (Measure.absolutelyContinuous_of_le hFle).trans (hRac.add_left hRac)
  -- the density of the outflow, truncated at a finite level
  set f := F.rnDeriv lam with hf
  have hFf : lam.withDensity f = F := Measure.withDensity_rnDeriv_eq F lam hFac
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hFuniv : ∫⁻ s, f s ∂lam = F Set.univ := by
    rw [← hFf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hconv : Tendsto (fun M : ℕ => ∫⁻ s, min (f s) M ∂lam) atTop (𝓝 (∫⁻ s, f s ∂lam)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun M => (hfm.min measurable_const).aemeasurable) ?_ ?_
    · exact ae_of_all _ fun s M N hMN => min_le_min le_rfl (by exact_mod_cast hMN)
    · filter_upwards [Measure.rnDeriv_lt_top F lam] with s hs
      have : Tendsto (fun M : ℕ => ((M : ℝ≥0∞))) atTop (𝓝 ∞) := ENNReal.tendsto_nat_nhds_top
      have h2 := (tendsto_const_nhds (x := f s)).min this
      simpa using h2
  have hconv' : Tendsto (fun M : ℕ => ∫⁻ s, f s ∂lam - ∫⁻ s, min (f s) M ∂lam) atTop (𝓝 0) := by
    have hfin : ∫⁻ s, f s ∂lam ≠ ∞ := by rw [hFuniv]; exact measure_ne_top _ _
    have := ENNReal.Tendsto.sub tendsto_const_nhds hconv (Or.inl hfin)
    simpa using this
  obtain ⟨M, hM⟩ := (hconv'.eventually (gt_mem_nhds hδpos)).exists
  set FM := lam.withDensity fun s => min (f s) (M : ℝ≥0∞) with hFMdef
  have hFMle : FM ≤ F := hFf ▸ withDensity_mono (ae_of_all _ fun s => min_le_left _ _)
  haveI : IsFiniteMeasure FM := isFiniteMeasure_of_le F hFMle
  have htvF : tvMass FM F < δ := by
    rw [tvMass_of_le hFMle, ← hFuniv, hFMdef, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hM
  refine ⟨fun s => (min (f s) (M : ℝ≥0∞)).toReal, fun s => ENNReal.toReal_nonneg,
    ⟨M, fun s => ?_⟩, ?_, ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg M) (by simp)
  · refine MemLp.of_bound ((hfm.min measurable_const).ennreal_toReal.aestronglyMeasurable) M
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg M) (by simp)
  · have hFM : (lam.withDensity fun s => ENNReal.ofReal ((min (f s) (M : ℝ≥0∞)).toReal)) = FM := by
      rw [hFMdef]; congr 1; funext s
      exact ENNReal.ofReal_toReal ((min_le_right _ _).trans_lt (ENNReal.natCast_lt_top M)).ne
    rw [hFM, inflow]
    have e1 : tvMass (Finit + FM.bind π) (μ₀ + FM.bind π) < δ :=
      (tvMass_add_right_le _ _ _).trans_lt hFa
    have e2 : tvMass (μ₀ + FM.bind π) (μ₀ + F.bind π) < δ :=
      ((tvMass_add_left_le _ _ _).trans (tvMass_bind_le π _ _)).trans_lt htvF
    have e3 : tvMass (μ₀ + F.bind π) (μ₁ + F) < δ := hFconstr.trans_lt hT
    have e4 : tvMass (μ₁ + F) (μ₁ + FM) < δ :=
      (tvMass_add_left_le _ _ _).trans_lt (by rw [tvMass_comm]; exact htvF)
    have e5 : tvMass (μ₁ + FM) (Fterm + FM) < δ :=
      (tvMass_add_right_le _ _ _).trans_lt (by rw [tvMass_comm]; exact hFb)
    calc tvMass (Finit + FM.bind π) (Fterm + FM)
        ≤ tvMass (Finit + FM.bind π) (μ₀ + FM.bind π) + (tvMass (μ₀ + FM.bind π) (μ₀ + F.bind π)
          + (tvMass (μ₀ + F.bind π) (μ₁ + F) + (tvMass (μ₁ + F) (μ₁ + FM)
          + tvMass (μ₁ + FM) (Fterm + FM)))) := by
          refine (tvMass_triangle _ (μ₀ + FM.bind π) _).trans (add_le_add le_rfl ?_)
          refine (tvMass_triangle _ (μ₀ + F.bind π) _).trans (add_le_add le_rfl ?_)
          refine (tvMass_triangle _ (μ₁ + F) _).trans (add_le_add le_rfl ?_)
          exact tvMass_triangle _ (μ₁ + FM) _
      _ < δ + (δ + (δ + (δ + δ))) :=
          ENNReal.add_lt_add e1 (ENNReal.add_lt_add e2 (ENNReal.add_lt_add e3
            (ENNReal.add_lt_add e4 e5)))
      _ ≤ ε' := by
          calc δ + (δ + (δ + (δ + δ))) = δ + δ + δ + δ + δ := by ring
            _ ≤ ε' := h5δ

/-- **The master universality theorem** (`theo:universality_true`, `main.tex:775`): for a Markov
kernel `π` that is summably `L²`-mixing on a finite measure space `(𝒮, λ)`, any two probability
measures `F_init, F_term ≪ λ` and any `ε > 0`, there is a non-negative bounded `f_out ∈ L²(λ)` such
that the generative flow `(π, f_out λ)` from `F_init` to `F_term` has
`δF_init(𝒮) + δF_term(𝒮) < ε`. -/
theorem main_universality (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (hmix : IsSummablyL2Mixing π lam) (Finit Fterm : Measure S)
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure Fterm] (hinit : Finit ≪ lam)
    (hterm : Fterm ≪ lam) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧ MemLp fout 2 lam ∧
      initialError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        + terminalError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        < ε := by
  obtain ⟨lamHat, hinv, hac, hac', hsum⟩ := hmix
  exact main_universality_of_tendsto lam π lamHat hinv hac hac'
    (ne_top_of_le_ne_top hsum (ENNReal.le_tsum 0)) (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum)
    Finit Fterm hinit hterm hε

/-! ## Inhabitation: the resampling kernel is summably `L²`-mixing -/

/-- Under the resampling kernel `π(x) = λ`, every iterate `n ≥ 1` sends `μ` to `μ(𝒮) λ`. -/
theorem pushIter_const_succ (lam : Measure S) [IsProbabilityMeasure lam] (n : ℕ) (μ : Measure S) :
    pushIter (Kernel.const S lam) (n + 1) μ = μ Set.univ • lam := by
  induction n with
  | zero =>
      rw [pushIter_succ, pushIter_zero]
      exact Measure.bind_const
  | succ n ih =>
      rw [pushIter_succ, ih]
      change (μ Set.univ • lam).bind (fun _ => lam) = _
      rw [Measure.bind_const, Measure.smul_apply, measure_univ (μ := lam), smul_eq_mul, mul_one]

/-- **Inhabitation of `def:summably_mixing`.** On a probability space `(𝒮, λ)` the resampling
kernel `π(x) = λ` is summably `L²`-mixing, with `λ̂ = λ`: for mean-zero `φ`, `φπⁿ = 0` for every
`n ≥ 1`, so `γₙ = 0` for `n ≥ 1` and `γ₀ = 1`. Hence `main_universality` applies to it. -/
theorem isSummablyL2Mixing_const (lam : Measure S) [IsProbabilityMeasure lam] :
    IsSummablyL2Mixing (Kernel.const S lam) lam := by
  have hinv : lam.bind (Kernel.const S lam) = lam := by
    change lam.bind (fun _ => lam) = lam
    rw [Measure.bind_const, measure_univ, one_smul]
  refine ⟨lam, hinv, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, ?_⟩
  -- `γₙ = 0` for `n ≥ 1`
  have hzero : ∀ n, mixingCoeff (Kernel.const S lam) lam lam (n + 1) = 0 := by
    intro n
    refine le_antisymm (iSup₂_le fun φ hφ => ?_) bot_le
    obtain ⟨hφL, -, hφ0⟩ := hφ
    have hφi : Integrable φ lam := hφL.integrable (by norm_num)
    have hp : ∫⁻ s, ENNReal.ofReal (φ s) ∂lam = ∫⁻ s, ENNReal.ofReal (-φ s) ∂lam := by
      have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφi
      rw [hφ0, eq_comm, sub_eq_zero] at h
      exact (ENNReal.toReal_eq_toReal_iff' hφi.lintegral_lt_top.ne
        hφi.neg.lintegral_lt_top.ne).mp h
    have htr : transfer (Kernel.const S lam) lam (n + 1) φ = 0 := by
      funext s
      simp only [transfer, pushIter_const_succ, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, hp, sub_self, Pi.zero_apply]
    simp [htr]
  -- `γ₀ ≤ 1`
  have hone : mixingCoeff (Kernel.const S lam) lam lam 0 ≤ 1 := by
    refine iSup₂_le fun φ hφ => ?_
    obtain ⟨hφL, hφn, -⟩ := hφ
    have hae := transfer_zero_ae (Kernel.const S lam) lam hφL.aemeasurable
    calc ∫⁻ s, ENNReal.ofReal (transfer (Kernel.const S lam) lam 0 φ s ^ 2) ∂lam
        = ∫⁻ s, ‖φ s‖ₑ ^ ((2 : ℝ≥0) : ℝ) ∂lam := by
          refine lintegral_congr_ae (hae.mono fun s hs => ?_)
          simp only
          rw [hs, Real.enorm_eq_ofReal_abs, NNReal.coe_ofNat, ENNReal.rpow_two,
            ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ = eLpNorm φ ((2 : ℝ≥0) : ℝ≥0∞) lam ^ ((2 : ℝ≥0) : ℝ) :=
          (eLpNorm_nnreal_pow_eq_lintegral (by norm_num)).symm
      _ = 1 := by
          rw [show ((2 : ℝ≥0) : ℝ≥0∞) = 2 from rfl, hφn, ENNReal.one_rpow]
      _ ≤ 1 := le_rfl
  rw [tsum_eq_single 0 fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn; exact hzero m]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hone

/-- **Inhabitation of `main_universality`**: on a probability space, the resampling kernel. -/
theorem main_universality_const (lam : Measure S) [IsProbabilityMeasure lam]
    (Finit Fterm : Measure S) [IsProbabilityMeasure Finit] [IsProbabilityMeasure Fterm]
    (hinit : Finit ≪ lam) (hterm : Fterm ≪ lam) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧ MemLp fout 2 lam ∧
      initialError (Kernel.const S lam) (lam.withDensity fun s => ENNReal.ofReal (fout s))
          Finit Fterm Set.univ
        + terminalError (Kernel.const S lam) (lam.withDensity fun s => ENNReal.ofReal (fout s))
          Finit Fterm Set.univ < ε :=
  main_universality lam (Kernel.const S lam) (isSummablyL2Mixing_const lam) Finit Fterm hinit
    hterm hε

end EGF
