import EGF.Sampling
import EGF.BackwardPolicy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The sampling error at inference with `F_term = κ̂ = (F_init + F_in − F_out)⁺`, and its Pinsker form

**`cor:sampling_error_control`** — `main.tex:329`

**`cor:pinsker_negative_control`** — `main.tex:374`, in its corrected form of record (DEC-141,
correction C-1): false as printed, the `δf_init` of `main.tex:362` being `≤ 0`; marked with the
negative part of `def:virtual_flows`, see SCOPE

Anchors: `EGF.sampling_error_control`; `EGF.pinsker_negative_control_density` (negative-part
reading). Both apply `EGF.main_quantitative_sampling` at `F_term := κ̂`. Pinsker is copied from
`GFNBounds.Core.ILBoundFull.pinsker` (`lean/GFNBounds/Core/ILBoundFull.lean:292`; never imported,
OQ-1) and restated for Mathlib's `klDiv` (`EGF.pinsker`).

> For a generative flow trained on the target $\target$ with $\Finit(\Statespace)=1$ and using
> $\Fterm=\widehat\target := \left(\Finit+\Finstar-\Foutstar\right)^+$ during inference, the
> sampling error is controlled by:
> $\TV\left(s_\tau \left\| \frac{\target}{\target(\Statespace )} \right.\right) \leq
> \frac{\delta}{1+\delta}+\TV\left(\frac{\widehat\target}{\widehat\target(\Statespace)} \left\|
> \frac{\target}{\target(\Statespace )} \right.\right)$,
> with $\delta :=  \left(\Finit+\Finstar-\Foutstar\right)^-(\Statespace)$. (`main.tex:329–333`)

> Let $\deltafinit=\min(0,\finit+\finstar-\foutstar)$  and
> $\ftermhat = \max(0,\finit+\finstar-\foutstar)$. (`main.tex:362`)

> Let $(\ForwardPolicyStar, \foutstar)$ be a generative flow. We train the generative flow on
> target probability distribution $\target$ with $\Finit(\Statespace)=1$. By using
> $\Fterm=\widehat\target:=  \left(\Finit+\Finstar-\Foutstar\right)^+$ during inference, the
> sampling error is bounded as follow:
> $\TV\left(s_\tau \left\| \target \right.\right) \leq  \frac{\delta}{1+\delta}
> +\sqrt{\frac{1}{2}\KL\left(\left.\frac{\widehat\target}{\widehat\target(\Statespace)} \right\|
> \target \right)}$, with $\delta :=  \int_{s\in\Statespace} \deltafinit(s)d\lambda(s)$.
> (`main.tex:375–379`)

> where $\finit = \frac{d\Finit}{d\lambda}$, $\fterm=\frac{d\Fterm}{d\lambda}$ and
> $\finstar=\frac{d\Finstar}{d\lambda} = \frac{d(\Foutstar\ForwardPolicyStar)}{d\lambda}$.
> (`main.tex:196`)

> Define the initial and terminal errors as $\delta\Finit:=(\Finit+\Finstar-\Fterm-\Foutstar)^-$
> and $\delta\Fterm:=(\Finit+\Finstar-\Fterm-\Foutstar)^+$ respectively. (`main.tex:316`)

## What is proved

With `E := F_init + F_in − F_out`:

| | |
|---|---|
| `kappaHat`, `inferenceDefect`, `*_eq_posPart`, `*_eq_negPart` | `κ̂ = E⁺`, `E⁻` (Jordan parts) |
| `virtualTerm_kappaHat`, `initialError_kappaHat` | at `F_term = κ̂`: `F̂_term = κ̂`, `δF_init = E⁻` |
| `sampling_error_control` | `cor:sampling_error_control`, plus `τ < ∞` a.s., `κ̂(𝒮) = 1 + δ` |
| `Pinsker.pinsker`, `tvDist_withDensity`, `klD_rnDeriv_eq_toReal_klDiv`, `pinsker` | Pinsker on densities (copied); `tvD = tvDist`, `klD = klDiv`; Pinsker with `klDiv` |
| `pinsker_negative_control` | the Pinsker form with `δ = E⁻(𝒮)` |
| `deltaFinitDensity(Printed)`, `InflowAC`, `integral_deltaFinitDensity(Printed)` | `δf_init` read and printed; `F_in ≪ λ`; `∫ δf_init dλ = E⁻(𝒮)`, printed `= −E⁻(𝒮)` |
| `pinsker_negative_control_density`, `_real`, `_isEGF` | the density form, in `[0, ∞]`, in `ℝ`, for an EGF |
| `printed_false_of_mem_Ioo`, `Swap.printed_pinsker_negative_control_false` | the printed form is false |

## Hypothesis checklist

| paper | here |
|---|---|
| `(π*, f*_out)` a generative flow | ✓ `EGF.GenerativeFlow` (`π` Markov, `F_out` finite, `main.tex:161`) |
| `F_init(𝒮) = 1` | ✓ `[IsProbabilityMeasure Finit]` |
| "trained on the target `κ`" (`cor:sampling_error_control`) | ⚠ weakened: `κ` any finite measure (`κ ≠ 0` dropped); the training is not read by the inequality, which holds for every flow |
| "target probability distribution `κ`" (`cor:pinsker_negative_control`) | ✓ `[IsProbabilityMeasure κ]` |
| `F_term = κ̂ := (F_init + F_in − F_out)⁺` during inference | ✓ `kappaHat` (`kappaHat_eq_posPart`); the sampler `GenerativeFlow.pathLaw F F_init κ̂` of `EGF.Sampling` (OQ-60 (b)) |
| `δ := (F_init + F_in − F_out)⁻(𝒮)` (`main.tex:333`) | ✓ `inferenceDefect … Set.univ` (`inferenceDefect_eq_negPart`), which is `δF_init(𝒮)` at `F_term = κ̂` |
| `TV` | ✓ `tvDist = ½‖·‖` (OQ-60 (a)) |
| `KL` | ✓ Mathlib's `InformationTheory.klDiv`, in `[0, ∞]`, `√(½ KL)` as `(KL/2)^{1/2}`; in `ℝ` when `KL < ∞` |
| `δ := ∫ δf_init dλ`, `δf_init = min(0, f_init + f_in − f_out)` (`main.tex:362`, `:379`) | ✗ false as printed (`printed_false_of_mem_Ioo`); corrected (DEC-141, C-1) to `max(0, −(f_init + f_in − f_out))`, the negative part of `main.tex:316`, `:333` |
| the densities `f = dF/dλ` (`main.tex:196`) | ✓ presupposed, as the paper does: `F_init ≪ λ`, `F_out ≪ λ`, `InflowAC λ F` (`F_in ≪ λ`, a named hypothesis); for an EGF `InflowAC` is proved |
| `(𝒮, λ)` Polish, `λ` finite (`main.tex:155`, `:358`) | ⚠ weakened: any measurable space, `λ` σ-finite, in the density form only |

## SCOPE (disclosed)

**`cor:sampling_error_control` is marked.** It is `EGF.main_quantitative_sampling` at
`F_term := κ̂`: there `δF_term = (E − E⁺)⁺ = 0`, so `F̂_term = κ̂`; `δF_init = E⁻`; `F̂_term(𝒮) = 1 + δ`;
and the triangle inequality adds `TV(κ̂/κ̂(𝒮) ‖ κ/κ(𝒮))`. No `λ` and no density enter. The mark
rests on OQ-60's two confirmations (the `½` of `TV`, the randomized stopping time), as that of
`theo:negative_control` does. `κ ≠ 0` is not assumed.

**The mark of `cor:pinsker_negative_control` is its corrected form.** As printed, `δf_init = min(0, ·) ≤ 0`
(`main.tex:362`), so `δ = −E⁻(𝒮) ≤ 0` (`integral_deltaFinitDensityPrinted`), and the bound fails
whenever `0 < E⁻(𝒮) < 1` at `κ = κ̂/κ̂(𝒮)`, where its right side is `−E⁻(𝒮)/(1 − E⁻(𝒮)) < 0`
(`printed_false_of_mem_Ioo`; a two-point instance, `Swap.printed_pinsker_negative_control_false`).
With `δ` the negative-part mass, as `def:virtual_flows` (`main.tex:316`) and
`cor:sampling_error_control` (`main.tex:333`) define it, the corollary is proved: in measures
(`pinsker_negative_control`) and in the paper's densities (`pinsker_negative_control_density`,
`δf_init := max(0, −(f_init + f_in − f_out))`, `∫ δf_init dλ = E⁻(𝒮)`). DEC-141 rules OQ-66: the
negative part is of record (corrections C-1, C-4), and the printed form stays above as
`PinskerNegativeControlPrinted` beside its refutation.

**Densities.** `f = dF/dλ` is Mathlib's `rnDeriv`, as `main.tex:196` defines it; the density form
presupposes `F_init, F_out, F_in ≪ λ`, as the paper does by writing their densities. `F_in ≪ λ` is the
named hypothesis `InflowAC`; for an EGF with `F_out = f_out λ` and `Φᵢ₊λ = Jᵢ λ` (OQ-55's form (c),
which contains (a) and (b)) it is `inflowAC_of_isEGFPolicy`, by `EGF.inflow_eq_withDensity`.

**Pinsker.** Mathlib (`fabf563a`) has `klDiv` and no Pinsker inequality. `Pinsker.pinsker` is
`GFNBounds.Core.ILBoundFull.pinsker` verbatim, with its helpers; `EGF.pinsker` restates it for
probability measures with `klDiv` through `tvDist_withDensity` and `klD_rnDeriv_eq_toReal_klDiv`.

No `sorry`. One named hypothesis, `InflowAC` (the paper's presupposition), in the density forms only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal

variable {S : Type*} [MeasurableSpace S]

/-! ## Inference at `κ̂` -/

/-- **The inference terminal distribution** `κ̂ := (F_init + F_in − F_out)⁺` (`main.tex:329`,
`:375`): Mathlib's truncated difference, the positive part of the signed measure
(`kappaHat_eq_posPart`). -/
noncomputable def kappaHat (π : Kernel S S) (Fout Finit : Measure S) : Measure S :=
  (Finit + inflow π Fout) - Fout

/-- **The inference defect** `(F_init + F_in − F_out)⁻` (`main.tex:333`), whose mass is the `δ` of
`cor:sampling_error_control`. -/
noncomputable def inferenceDefect (π : Kernel S S) (Fout Finit : Measure S) : Measure S :=
  Fout - (Finit + inflow π Fout)

section Inference

variable (π : Kernel S S) [IsMarkovKernel π] (Fout Finit : Measure S) [IsFiniteMeasure Fout]
  [IsFiniteMeasure Finit]

instance isFiniteMeasure_kappaHat : IsFiniteMeasure (kappaHat π Fout Finit) := by
  unfold kappaHat; infer_instance

instance isFiniteMeasure_inferenceDefect : IsFiniteMeasure (inferenceDefect π Fout Finit) := by
  unfold inferenceDefect; infer_instance

/-- `κ̂` is the positive part of `F_init + F_in − F_out` in Mathlib's Jordan decomposition. -/
theorem kappaHat_eq_posPart : kappaHat π Fout Finit = ((Finit + inflow π Fout).toSignedMeasure
    - Fout.toSignedMeasure).toJordanDecomposition.posPart := by
  rw [Measure.toJordanDecomposition_toSignedMeasure_sub]; rfl

/-- The inference defect is the negative part of `F_init + F_in − F_out`. -/
theorem inferenceDefect_eq_negPart : inferenceDefect π Fout Finit
    = ((Finit + inflow π Fout).toSignedMeasure
      - Fout.toSignedMeasure).toJordanDecomposition.negPart := by
  rw [Measure.toJordanDecomposition_toSignedMeasure_sub]; rfl

/-- At `F_term = κ̂` the terminal error vanishes: `δF_term = 0`. -/
theorem terminalError_kappaHat : terminalError π Fout Finit (kappaHat π Fout Finit) = 0 := by
  unfold terminalError kappaHat
  exact Measure.sub_eq_zero_of_le (Measure.sub_le_iff_le_add.mp le_rfl)

/-- At `F_term = κ̂`, `F̂_term = κ̂`. -/
theorem virtualTerm_kappaHat :
    virtualTerm π Fout Finit (kappaHat π Fout Finit) = kappaHat π Fout Finit := by
  rw [virtualTerm, terminalError_kappaHat, add_zero]

/-- At `F_term = κ̂`, `δF_init = (F_init + F_in − F_out)⁻`. -/
theorem initialError_kappaHat :
    initialError π Fout Finit (kappaHat π Fout Finit) = inferenceDefect π Fout Finit := by
  unfold initialError kappaHat inferenceDefect
  set A := Finit + inflow π Fout
  have h : A - Fout + Fout = Fout - A + A := by
    rw [add_comm (A - Fout), add_sub_eq_add_sub Fout A, add_comm]
  rw [h, Measure.add_sub_cancel]

end Inference

/-! ## The triangle inequality for `tvDist` -/

theorem tvDist_triangle (μ ν ρ : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] : tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  unfold tvDist
  rw [← ENNReal.add_div]
  exact ENNReal.div_le_div_right (tvMass_triangle μ ν ρ) 2

/-! ## `cor:sampling_error_control` -/

/-- **`cor:sampling_error_control`** (`main.tex:329–334`). Let `(π, F_out)` be a generative flow,
`F_init` a probability measure and `κ` a finite measure; sample with `F_term = κ̂ = (F_init + F_in −
F_out)⁺` (`GenerativeFlow.pathLaw F F_init κ̂`), and let `δ = (F_init + F_in − F_out)⁻(𝒮)`. Then

1. `τ < ∞` almost surely, and `s_τ` has a probability law;
2. `κ̂(𝒮) = 1 + δ`;
3. `TV(s_τ ‖ κ̂/κ̂(𝒮)) ≤ δ/(1 + δ)` (`theo:negative_control` at `F_term = κ̂`);
4. `TV(s_τ ‖ κ/κ(𝒮)) ≤ δ/(1 + δ) + TV(κ̂/κ̂(𝒮) ‖ κ/κ(𝒮))`, `TV` with the `½` of `main.tex:338`. -/
theorem sampling_error_control (F : GenerativeFlow S) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsFiniteMeasure κ] :
    F.pathLaw Finit (kappaHat F.policy F.outflow Finit) {ω | stopTime ω = ⊤} = 0 ∧
    IsProbabilityMeasure ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) ∧
    kappaHat F.policy F.outflow Finit Set.univ
      = 1 + inferenceDefect F.policy F.outflow Finit Set.univ ∧
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState)
        (normalize (kappaHat F.policy F.outflow Finit))
      ≤ inferenceDefect F.policy F.outflow Finit Set.univ
        / (1 + inferenceDefect F.policy F.outflow Finit Set.univ) ∧
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) (normalize κ)
      ≤ inferenceDefect F.policy F.outflow Finit Set.univ
          / (1 + inferenceDefect F.policy F.outflow Finit Set.univ)
        + tvDist (normalize (kappaHat F.policy F.outflow Finit)) (normalize κ) := by
  have hinit : Finit ≠ 0 := IsProbabilityMeasure.ne_zero Finit
  obtain ⟨htop, -, hP, hmass, hTV, -⟩ :=
    main_quantitative_sampling F (Finit := Finit) (Fterm := kappaHat F.policy F.outflow Finit) hinit
  rw [virtualTerm_kappaHat] at htop hP hmass hTV
  rw [initialError_kappaHat] at hmass hTV
  rw [measure_univ (μ := Finit)] at hmass
  rw [hmass] at hTV
  refine ⟨htop, hP, hmass, hTV, ?_⟩
  exact (tvDist_triangle _ _ _).trans (add_le_add_left hTV _)

/-! ## Pinsker's inequality on densities (port of `GFNBounds.Core.ILBoundFull.pinsker`) -/

namespace Pinsker

variable {α : Type*} [MeasurableSpace α]

/-- `u(x) = (x+1) log x − 2(x−1)` is monotone on `(0,∞)`: `u' = log x + 1/x − 1 ≥ 0`. Copied from
`GFNBounds.Core.ILBoundFull.padeAux_mono` (`lean/GFNBounds/Core/ILBoundFull.lean:126`). -/
theorem padeAux_mono :
    MonotoneOn (fun x : ℝ => (x + 1) * Real.log x - 2 * (x - 1)) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => (x + 1) * Real.log x - 2 * (x - 1))
      (Real.log x + (x + 1) * x⁻¹ - 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 := ((hasDerivAt_id' x).add_const 1).mul (Real.hasDerivAt_log hx0)
    have h2 := ((hasDerivAt_id' x).sub_const 1).const_mul 2
    refine (h1.sub h2).congr_deriv ?_
    ring
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hd x hx).deriv]
    have hx0 : (0 : ℝ) < x := hx
    have hl := Real.one_sub_inv_le_log_of_pos hx0
    have : (x + 1) * x⁻¹ = 1 + x⁻¹ := by field_simp
    rw [this]
    linarith

/-- The sign of `u(x)` is that of `x − 1`. Copied from `GFNBounds.Core.ILBoundFull.padeAux_sign`
(`ILBoundFull.lean:151`). -/
theorem padeAux_sign {x : ℝ} (hx : 0 < x) :
    0 ≤ (x - 1) * ((x + 1) * Real.log x - 2 * (x - 1)) := by
  have hm := padeAux_mono
  have h1 : (1 + 1) * Real.log 1 - 2 * ((1 : ℝ) - 1) = 0 := by simp
  rcases le_total 1 x with h | h
  · have := hm (show (1 : ℝ) ∈ Ioi 0 by norm_num) hx h
    simp only at this
    rw [h1] at this
    exact mul_nonneg (by linarith) this
  · have := hm hx (show (1 : ℝ) ∈ Ioi 0 by norm_num) h
    simp only at this
    rw [h1] at this
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) this

/-- `h(x) = (2x+4)(x log x − x + 1) − 3(x−1)²`, whose derivative is `4u(x)`. Copied from
`GFNBounds.Core.ILBoundFull.pollardAux` (`ILBoundFull.lean:166`). -/
noncomputable def pollardAux (x : ℝ) : ℝ :=
  (2 * x + 4) * (x * Real.log x - x + 1) - 3 * (x - 1) ^ 2

/-- Copied from `GFNBounds.Core.ILBoundFull.pollardAux_hasDerivAt` (`ILBoundFull.lean:169`). -/
theorem pollardAux_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt pollardAux (4 * ((x + 1) * Real.log x - 2 * (x - 1))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxl : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) x := by
    refine ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0)).congr_deriv ?_
    field_simp
  have h1 := (((hasDerivAt_id' x).const_mul 2).add_const 4).mul
    ((hxl.sub (hasDerivAt_id' x)).add_const 1)
  have h2 := (((hasDerivAt_id' x).sub_const 1).pow 2).const_mul 3
  have h3 := h1.sub h2
  unfold pollardAux
  refine h3.congr_deriv ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- Copied from `GFNBounds.Core.ILBoundFull.continuous_pollardAux` (`ILBoundFull.lean:185`). -/
theorem continuous_pollardAux : Continuous pollardAux := by
  unfold pollardAux
  have := Real.continuous_mul_log
  fun_prop

/-- **Pollard's pointwise inequality** `3(x−1)² ≤ (2x+4)(x log x − x + 1)` for `x ≥ 0`. Copied from
`GFNBounds.Core.ILBoundFull.pollard_ineq` (`ILBoundFull.lean:192`). -/
theorem pollard_ineq {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 ≤ (2 * x + 4) * (x * Real.log x - x + 1) := by
  suffices h : 0 ≤ pollardAux x by unfold pollardAux at h; linarith
  have h1 : pollardAux 1 = 0 := by simp [pollardAux]
  rcases le_total 1 x with h | h
  · have hmono : MonotoneOn pollardAux (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
        continuous_pollardAux.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Ici] at hy
        exact (pollardAux_hasDerivAt (by linarith [mem_Ioi.1 hy])).differentiableAt
          |>.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy1 : 1 < y := hy
        rw [(pollardAux_hasDerivAt (by linarith)).deriv]
        have := padeAux_sign (x := y) (by linarith)
        have hpos : 0 < y - 1 := by linarith
        have : 0 ≤ (y + 1) * Real.log y - 2 * (y - 1) := by
          by_contra hc
          have hc' := not_le.mp hc
          nlinarith
        linarith
    have := hmono (show (1 : ℝ) ∈ Ici 1 from mem_Ici.2 le_rfl) (show x ∈ Ici 1 from h) h
    linarith
  · have hanti : AntitoneOn pollardAux (Icc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
        continuous_pollardAux.continuousOn ?_ ?_
      · intro y hy
        rw [interior_Icc] at hy
        exact (pollardAux_hasDerivAt hy.1).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        rw [(pollardAux_hasDerivAt hy.1).deriv]
        have := padeAux_sign (x := y) hy.1
        have hneg : y - 1 < 0 := by linarith [hy.2]
        have : (y + 1) * Real.log y - 2 * (y - 1) ≤ 0 := by
          by_contra hc
          have hc' := not_le.mp hc
          nlinarith
        linarith
    have := hanti (show x ∈ Icc 0 1 from ⟨hx, h⟩) (show (1 : ℝ) ∈ Icc 0 1 by norm_num) h
    linarith

/-- Pollard's inequality at `x = k/g`, times `g²`: `3(k−g)² ≤ (2k+4g)(k log(k/g) − k + g)` for
`k, g ≥ 0` with `g = 0 ⇒ k = 0`. Copied from `GFNBounds.Core.ILBoundFull.pollard_two`
(`ILBoundFull.lean:238`). -/
theorem pollard_two {k g : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g) (hac : g = 0 → k = 0) :
    3 * (k - g) ^ 2 ≤ (2 * k + 4 * g) * (k * Real.log (k / g) - k + g) := by
  rcases eq_or_lt_of_le hg with h0 | h0
  · have hk' := hac h0.symm
    rw [← h0, hk']
    simp
  · have h := pollard_ineq (x := k / g) (div_nonneg hk hg)
    have hgne : g ≠ 0 := ne_of_gt h0
    have key : 3 * (k - g) ^ 2 = g ^ 2 * (3 * (k / g - 1) ^ 2) := by
      field_simp
    have key2 : (2 * k + 4 * g) * (k * Real.log (k / g) - k + g)
        = g ^ 2 * ((2 * (k / g) + 4) * (k / g * Real.log (k / g) - k / g + 1)) := by
      field_simp
    rw [key, key2]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg g)

/-- `x − y ≤ x log(x/y)` for `x, y ≥ 0` with `y = 0 ⇒ x = 0` (`log t ≤ t − 1` at `t = y/x`). Copied
from `GFNBounds.Core.sub_le_mul_log_div` (`lean/GFNBounds/Core/ILBound.lean:185`). -/
theorem sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hac : y = 0 → x = 0) :
    x - y ≤ x * Real.log (x / y) := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0]
    simp only [zero_mul, zero_sub, neg_nonpos]
    exact hy
  · have hyne : y ≠ 0 := fun h => absurd (hac h) (ne_of_gt h0)
    have hy0 : 0 < y := lt_of_le_of_ne hy (Ne.symm hyne)
    have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 h0)
    have hxy : x / y = (y / x)⁻¹ := (inv_div y x).symm
    rw [hxy, Real.log_inv]
    have hmul : x * (y / x) = y := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlog h0.le]

/-- The pointwise bound integrated in `pinsker`: for every `t > 0`,
`|k − g| ≤ c₁(t) k + c₂(t) g + (1/(2t)) k log(k/g)` (AM–GM on `(k − g)² ≤ aφ`). Copied from
`GFNBounds.Core.ILBoundFull.pinsker_pointwise` (`ILBoundFull.lean:258`). -/
theorem pinsker_pointwise {k g t : ℝ} (hk : 0 ≤ k) (hg : 0 ≤ g) (hac : g = 0 → k = 0)
    (ht : 0 < t) :
    |k - g| ≤ (2 * t / 3 - 1 / t) / 2 * k + (4 * t / 3 + 1 / t) / 2 * g
      + 1 / (2 * t) * (k * Real.log (k / g)) := by
  set a : ℝ := (2 * k + 4 * g) / 3 with ha
  set φ : ℝ := k * Real.log (k / g) - k + g with hφ
  have hφ0 : 0 ≤ φ := by
    have := sub_le_mul_log_div hk hg hac
    rw [hφ]; linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hsq : (k - g) ^ 2 ≤ a * φ := by
    have := pollard_two hk hg hac
    rw [ha, hφ]; nlinarith
  have hrhs : (2 * t / 3 - 1 / t) / 2 * k + (4 * t / 3 + 1 / t) / 2 * g
      + 1 / (2 * t) * (k * Real.log (k / g)) = (t * a + φ / t) / 2 := by
    rw [ha, hφ]; field_simp; ring
  rw [hrhs]
  have hB : 0 ≤ (t * a + φ / t) / 2 := by positivity
  refine abs_le_of_sq_le_sq ?_ hB
  have htne : t ≠ 0 := ne_of_gt ht
  have hamgm : 4 * (a * φ) ≤ (t * a + φ / t) ^ 2 := by
    have h0 : 0 ≤ (t * a - φ / t) ^ 2 := sq_nonneg _
    have hprod : (t * a) * (φ / t) = a * φ := by field_simp
    nlinarith
  nlinarith

/-- `KL(k·ν ‖ g·ν) = ∫ k log(k/g) dν`, between densities. Copied from `GFNBounds.Core.klD`
(`ILBound.lean:155`); it is Mathlib's `klDiv` by `EGF.klD_rnDeriv_eq_toReal_klDiv`. -/
noncomputable def klD (ν : Measure α) (k g : α → ℝ) : ℝ :=
  ∫ x, k x * Real.log (k x / g x) ∂ν

/-- `TV = ½ ∫ |f − g| dν`, between densities. Copied from `GFNBounds.Core.tvD`
(`lean/GFNBounds/Core/StableBound.lean:116`); it is `EGF.tvDist` by `EGF.tvDist_withDensity`. -/
noncomputable def tvD (ν : Measure α) (f g : α → ℝ) : ℝ := (1 / 2) * ∫ x, |f x - g x| ∂ν

/-- Gibbs' inequality on densities. Copied from `GFNBounds.Core.klD_nonneg` (`ILBound.lean:202`). -/
theorem klD_nonneg {ν : Measure α} {k g : α → ℝ}
    (hk : Integrable k ν) (hg : Integrable g ν)
    (hint : Integrable (fun x => k x * Real.log (k x / g x)) ν)
    (hk0 : 0 ≤ᵐ[ν] k) (hg0 : 0 ≤ᵐ[ν] g)
    (hac : ∀ᵐ x ∂ν, g x = 0 → k x = 0)
    (hmass : ∫ x, g x ∂ν ≤ ∫ x, k x ∂ν) :
    0 ≤ klD ν k g := by
  have h : ∫ x, (k x - g x) ∂ν ≤ ∫ x, k x * Real.log (k x / g x) ∂ν := by
    refine integral_mono_ae (hk.sub hg) hint ?_
    filter_upwards [hk0, hg0, hac] with x h1 h2 h3
    exact sub_le_mul_log_div h1 h2 h3
  rw [integral_sub hk hg] at h
  unfold klD
  linarith

/-- **Pinsker's inequality on densities**: for probability densities `k, g` against `ν` with
`k ≪ g` and `k log(k/g)` integrable, `tvD ν k g ≤ (1/√2) √(klD ν k g)`. Pollard's proof
(`pollard_ineq`, AM–GM in place of Cauchy–Schwarz), copied from
`GFNBounds.Core.ILBoundFull.pinsker` (`lean/GFNBounds/Core/ILBoundFull.lean:292`). -/
theorem pinsker {ν : Measure α} {k g : α → ℝ}
    (hk : Integrable k ν) (hg : Integrable g ν) (hk0 : 0 ≤ᵐ[ν] k) (hg0 : 0 ≤ᵐ[ν] g)
    (hac : ∀ᵐ x ∂ν, g x = 0 → k x = 0)
    (hint : Integrable (fun x => k x * Real.log (k x / g x)) ν)
    (hk1 : ∫ x, k x ∂ν = 1) (hg1 : ∫ x, g x ∂ν = 1) :
    tvD ν k g ≤ 1 / Real.sqrt 2 * Real.sqrt (klD ν k g) := by
  set K := klD ν k g with hK
  have hK0 : 0 ≤ K := klD_nonneg hk hg hint hk0 hg0 hac (by rw [hk1, hg1])
  -- the integrated AM–GM bound
  have hbound : ∀ t : ℝ, 0 < t → ∫ x, |k x - g x| ∂ν ≤ t + K / (2 * t) := by
    intro t ht
    have hR : Integrable (fun x => (2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x
        + 1 / (2 * t) * (k x * Real.log (k x / g x))) ν :=
      ((hk.const_mul _).add (hg.const_mul _)).add (hint.const_mul _)
    have hmono := integral_mono_ae (hk.sub hg).abs hR (by
      filter_upwards [hk0, hg0, hac] with x h1 h2 h3
      exact pinsker_pointwise h1 h2 h3 ht)
    have hval : ∫ x, ((2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x
        + 1 / (2 * t) * (k x * Real.log (k x / g x))) ∂ν
        = (2 * t / 3 - 1 / t) / 2 * 1 + (4 * t / 3 + 1 / t) / 2 * 1 + 1 / (2 * t) * K := by
      rw [integral_add (f := fun x => (2 * t / 3 - 1 / t) / 2 * k x + (4 * t / 3 + 1 / t) / 2 * g x)
          ((hk.const_mul _).add (hg.const_mul _)) (hint.const_mul _),
        integral_add (hk.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul, hk1, hg1]
      rfl
    rw [hval] at hmono
    have habs : ∫ x, |k x - g x| ∂ν = ∫ x, |(k - g) x| ∂ν := rfl
    rw [habs]
    have htne : t ≠ 0 := ne_of_gt ht
    have : (2 * t / 3 - 1 / t) / 2 * 1 + (4 * t / 3 + 1 / t) / 2 * 1 + 1 / (2 * t) * K
        = t + K / (2 * t) := by field_simp; ring
    linarith
  unfold tvD
  rcases eq_or_lt_of_le hK0 with h0 | hpos
  · -- `K = 0`: the `L¹` distance is below every `t > 0`
    rw [← h0, Real.sqrt_zero, mul_zero]
    have hle : ∫ x, |k x - g x| ∂ν ≤ 0 := by
      refine le_of_forall_pos_le_add fun t ht => ?_
      have := hbound t ht
      rw [← h0, zero_div, add_zero] at this
      linarith
    linarith
  · set t : ℝ := 1 / Real.sqrt 2 * Real.sqrt K with htdef
    have ht : 0 < t := by positivity
    have ht2 : t ^ 2 = K / 2 := by
      rw [htdef, mul_pow, Real.sq_sqrt hK0, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hKt : K / (2 * t) = t := by
      have htne : t ≠ 0 := ne_of_gt ht
      field_simp
      nlinarith
    have := hbound t ht
    rw [hKt] at this
    linarith

end Pinsker

/-! ## From densities to measures: `tvD` is `tvDist`, `klD` is `klDiv` -/

/-- **`tvD` is `tvDist`**: the total variation of two measures with integrable non-negative
densities `f, g` against `λ` is `½ ∫ |f − g| dλ`. -/
theorem tvDist_withDensity (lam : Measure S) {f g : S → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : 0 ≤ᵐ[lam] f) (hg0 : 0 ≤ᵐ[lam] g) (hfi : Integrable f lam) (hgi : Integrable g lam) :
    tvDist (lam.withDensity fun x => ENNReal.ofReal (f x))
        (lam.withDensity fun x => ENNReal.ofReal (g x))
      = ENNReal.ofReal (Pinsker.tvD lam f g) := by
  have hu : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf
  have hv : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hg
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfi.2
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hgi.2
  have key : tvMass (lam.withDensity fun x => ENNReal.ofReal (f x))
      (lam.withDensity fun x => ENNReal.ofReal (g x))
      = ENNReal.ofReal (∫ x, |f x - g x| ∂lam) := by
    unfold tvMass
    rw [← Measure.withDensity_sub hu hv, ← Measure.withDensity_sub hv hu,
      withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    simp only [Pi.sub_apply]
    rw [← lintegral_add_left (hu.sub hv),
      ofReal_integral_eq_lintegral_ofReal (f := fun x => |f x - g x|) (hfi.sub hgi).abs
        (ae_of_all _ fun _ => abs_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hf0, hg0] with x h1 h2
    rw [tsub_add_tsub_eq_ofReal_abs ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
  rw [tvDist, key, Pinsker.tvD, show (1 / 2 : ℝ) * ∫ x, |f x - g x| ∂lam
      = (∫ x, |f x - g x| ∂lam) / 2 by ring, ENNReal.ofReal_div_of_pos two_pos,
    ENNReal.ofReal_ofNat]

/-- **`klD` is Mathlib's `klDiv`**: for probability measures `μ ≪ ν`, the density divergence of
`dμ/dν` against the density `1`, both relative to `ν`, is `KL(μ ‖ ν)` (no integrability needed:
both sides are `0` when `log(dμ/dν)` is not `μ`-integrable). -/
theorem klD_rnDeriv_eq_toReal_klDiv {μ ν : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    Pinsker.klD ν (fun x => (μ.rnDeriv ν x).toReal) (fun _ => 1) = (klDiv μ ν).toReal := by
  rw [Pinsker.klD, toReal_klDiv_of_measure_eq hac (by simp), ← integral_rnDeriv_mul_log hac]
  simp

/-- **Pinsker's inequality**, for probability measures, with Mathlib's `klDiv`:
`TV(μ ‖ ν) ≤ √(½ KL(μ ‖ ν))`, in `[0, ∞]` (`√∞ = ∞`). `Pinsker.pinsker` against the reference `ν`,
with the densities `dμ/dν` and `1`. -/
theorem pinsker (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (klDiv μ ν / 2) ^ (1 / 2 : ℝ) := by
  by_cases htop : klDiv μ ν = ∞
  · rw [htop, ENNReal.top_div_of_ne_top (by norm_num), ENNReal.top_rpow_of_pos (by norm_num)]
    exact le_top
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp htop
  set k : S → ℝ := fun x => (μ.rnDeriv ν x).toReal with hk
  have hkm : Measurable k := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hμ : μ = ν.withDensity fun x => ENNReal.ofReal (k x) := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    simp [hk, ENNReal.ofReal_toReal hx]
  have hν : ν = ν.withDensity fun _ => ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]; exact withDensity_one.symm
  have hki : Integrable k ν := Measure.integrable_toReal_rnDeriv
  have hk1 : ∫ x, k x ∂ν = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac]; simp
  have hlog : Integrable (fun x => k x * Real.log (k x / 1)) ν := by
    simp only [div_one]; exact (integrable_rnDeriv_mul_log_iff hac).2 hint
  have hP := Pinsker.pinsker (ν := ν) (k := k) (g := fun _ => 1) hki (integrable_const 1)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) (ae_of_all _ fun _ => zero_le_one)
    (ae_of_all _ fun _ h => absurd h one_ne_zero) hlog hk1 (by simp)
  have hKL : Pinsker.klD ν k (fun _ => 1) = (klDiv μ ν).toReal :=
    klD_rnDeriv_eq_toReal_klDiv hac
  have hTV := tvDist_withDensity ν hkm measurable_const
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) (ae_of_all _ fun _ => zero_le_one) hki
    (integrable_const (1 : ℝ))
  rw [← hμ, ← hν] at hTV
  have hKnn : 0 ≤ (klDiv μ ν).toReal := ENNReal.toReal_nonneg
  have hRHS : (klDiv μ ν / 2) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (1 / Real.sqrt 2 * Real.sqrt (klDiv μ ν).toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal htop]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos two_pos,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_div hKnn, one_div_mul_eq_div]
  rw [hTV, hRHS]
  exact ENNReal.ofReal_le_ofReal (hP.trans_eq (by rw [hKL]))

/-! ## `cor:pinsker_negative_control`, measure form -/

/-- `cor:pinsker_negative_control` (`main.tex:374–380`) **with `δ` the negative-part mass**
`(F_init + F_in − F_out)⁻(𝒮)` of `main.tex:333` (the printed `δ` of `main.tex:379` is refuted by
`printed_false_of_mem_Ioo`): for a probability `F_init` and a target probability `κ`,
`TV(s_τ ‖ κ) ≤ δ/(1 + δ) + √(½ KL(κ̂/κ̂(𝒮) ‖ κ))`. -/
theorem pinsker_negative_control (F : GenerativeFlow S) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ inferenceDefect F.policy F.outflow Finit Set.univ
          / (1 + inferenceDefect F.policy F.outflow Finit Set.univ)
        + (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ) := by
  have hκ : normalize κ = κ := by rw [normalize, measure_univ, inv_one, one_smul]
  obtain ⟨-, -, hmass, -, hbound⟩ := sampling_error_control F (Finit := Finit) (κ := κ)
  rw [hκ] at hbound
  have hne : kappaHat F.policy F.outflow Finit ≠ 0 := by
    intro h
    have h1 : (1 : ℝ≥0∞) ≤ kappaHat F.policy F.outflow Finit Set.univ := hmass ▸ le_self_add
    rw [h] at h1
    simp at h1
  haveI : IsProbabilityMeasure (normalize (kappaHat F.policy F.outflow Finit)) :=
    ⟨normalize_univ _ hne⟩
  exact hbound.trans (add_le_add le_rfl (pinsker _ _))

/-! ## The paper's densities (`main.tex:196`, `:362`) -/

/-- The density `dμ/dλ`, as a real function (`main.tex:196`). -/
noncomputable def dens (lam μ : Measure S) (s : S) : ℝ := (μ.rnDeriv lam s).toReal

/-- `f_init + f_in − f_out`, the flow-matching defect density at `F_term = 0`. -/
noncomputable def defectDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S)
    (s : S) : ℝ :=
  dens lam Finit s + dens lam (inflow π Fout) s - dens lam Fout s

/-- **`δf_init`, read as `def:virtual_flows` reads `δF_init`**: the negative part
`max(0, −(f_init + f_in − f_out))` (`main.tex:316`, `:333`). -/
noncomputable def deltaFinitDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S)
    (s : S) : ℝ :=
  max 0 (-defectDensity lam π Fout Finit s)

/-- **`δf_init` as printed**, `min(0, f_init + f_in − f_out)` (`main.tex:362`). -/
noncomputable def deltaFinitDensityPrinted (lam : Measure S) (π : Kernel S S)
    (Fout Finit : Measure S) (s : S) : ℝ :=
  min 0 (defectDensity lam π Fout Finit s)

/-- `f̂_term = max(0, f_init + f_in − f_out)` (`main.tex:362`). -/
noncomputable def ftermHatDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S)
    (s : S) : ℝ :=
  max 0 (defectDensity lam π Fout Finit s)

/-- The presupposition of `main.tex:196`: the star inflow has a density, `F_in ≪ λ`. -/
def InflowAC (lam : Measure S) (F : GenerativeFlow S) : Prop := inflow F.policy F.outflow ≪ lam

theorem deltaFinitDensityPrinted_eq_neg (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S)
    (s : S) : deltaFinitDensityPrinted lam π Fout Finit s = -deltaFinitDensity lam π Fout Finit s := by
  unfold deltaFinitDensityPrinted deltaFinitDensity
  rw [min_def, max_def]
  split_ifs <;> linarith

theorem deltaFinitDensityPrinted_nonpos (lam : Measure S) (π : Kernel S S)
    (Fout Finit : Measure S) (s : S) : deltaFinitDensityPrinted lam π Fout Finit s ≤ 0 :=
  min_le_left _ _

/-- `ofReal (max(0, x − y)) = x − y` in `ℝ≥0∞`, for finite `x, y`. -/
theorem ofReal_max_zero_toReal_sub {x y : ℝ≥0∞} (hx : x ≠ ∞) (hy : y ≠ ∞) :
    ENNReal.ofReal (max 0 (x.toReal - y.toReal)) = x - y := by
  rcases le_total 0 (x.toReal - y.toReal) with h | h
  · rw [max_eq_right h, ofReal_toReal_sub_toReal hx hy]
  · rw [max_eq_left h, ENNReal.ofReal_zero, ← ofReal_toReal_sub_toReal hx hy,
      ENNReal.ofReal_of_nonpos h]

theorem measurable_defectDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S) :
    Measurable (defectDensity lam π Fout Finit) :=
  (((Measure.measurable_rnDeriv _ _).ennreal_toReal.add
    (Measure.measurable_rnDeriv _ _).ennreal_toReal).sub
    (Measure.measurable_rnDeriv _ _).ennreal_toReal)

theorem measurable_deltaFinitDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S) :
    Measurable (deltaFinitDensity lam π Fout Finit) :=
  measurable_const.max (measurable_defectDensity lam π Fout Finit).neg

section Densities

variable (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S) (Finit : Measure S)
  [IsFiniteMeasure Finit]

/-- Under the presuppositions of `main.tex:196`, `F_init + F_in = (f_init + f_in) λ` and
`F_out = f_out λ`, with Mathlib's `rnDeriv`. -/
theorem add_inflow_eq_withDensity (hinit : Finit ≪ lam) (hin : InflowAC lam F) :
    lam.withDensity (Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam)
      = Finit + inflow F.policy F.outflow := by
  rw [withDensity_add_left (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq _ _ hinit, Measure.withDensity_rnDeriv_eq _ _ hin]

/-- `κ̂ = f̂_term λ`. -/
theorem kappaHat_eq_withDensity (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    kappaHat F.policy F.outflow Finit
      = lam.withDensity fun s => ENNReal.ofReal (ftermHatDensity lam F.policy F.outflow Finit s) := by
  have hc : lam.withDensity (F.outflow.rnDeriv lam) = F.outflow :=
    Measure.withDensity_rnDeriv_eq _ _ hout
  haveI : IsFiniteMeasure (lam.withDensity (F.outflow.rnDeriv lam)) := by
    rw [hc]; infer_instance
  have hL : kappaHat F.policy F.outflow Finit = lam.withDensity
      ((Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam) - F.outflow.rnDeriv lam) := by
    unfold kappaHat
    have hm : Measurable (Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam) :=
      (Measure.measurable_rnDeriv _ _).add (Measure.measurable_rnDeriv _ _)
    rw [Measure.withDensity_sub (μ := lam) hm (Measure.measurable_rnDeriv _ _),
      add_inflow_eq_withDensity lam F Finit hinit hin, hc]
  rw [hL]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top Finit lam,
    Measure.rnDeriv_ne_top (inflow F.policy F.outflow) lam,
    Measure.rnDeriv_ne_top F.outflow lam] with s h1 h2 h3
  simp only [Pi.sub_apply, Pi.add_apply, ftermHatDensity, defectDensity, dens]
  rw [← ENNReal.toReal_add h1 h2, ofReal_max_zero_toReal_sub (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h3]

/-- `(F_init + F_in − F_out)⁻ = δf_init λ`. -/
theorem inferenceDefect_eq_withDensity (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    inferenceDefect F.policy F.outflow Finit
      = lam.withDensity fun s =>
          ENNReal.ofReal (deltaFinitDensity lam F.policy F.outflow Finit s) := by
  have hab := add_inflow_eq_withDensity lam F Finit hinit hin
  haveI : IsFiniteMeasure
      (lam.withDensity (Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam)) := by
    rw [hab]; infer_instance
  have hL : inferenceDefect F.policy F.outflow Finit = lam.withDensity
      (F.outflow.rnDeriv lam - (Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam)) := by
    unfold inferenceDefect
    have hm : Measurable (Finit.rnDeriv lam + (inflow F.policy F.outflow).rnDeriv lam) :=
      (Measure.measurable_rnDeriv _ _).add (Measure.measurable_rnDeriv _ _)
    rw [Measure.withDensity_sub (μ := lam) (Measure.measurable_rnDeriv _ _) hm, hab,
      Measure.withDensity_rnDeriv_eq _ _ hout]
  rw [hL]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top Finit lam,
    Measure.rnDeriv_ne_top (inflow F.policy F.outflow) lam,
    Measure.rnDeriv_ne_top F.outflow lam] with s h1 h2 h3
  simp only [Pi.sub_apply, Pi.add_apply, deltaFinitDensity, defectDensity, dens, neg_sub]
  rw [← ENNReal.toReal_add h1 h2, ofReal_max_zero_toReal_sub h3 (ENNReal.add_ne_top.2 ⟨h1, h2⟩)]

/-- `∫ δf_init dλ = (F_init + F_in − F_out)⁻(𝒮)`, in the `def:virtual_flows` reading. -/
theorem integral_deltaFinitDensity (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam
      = (inferenceDefect F.policy F.outflow Finit Set.univ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := deltaFinitDensity lam F.policy F.outflow Finit)
      (ae_of_all _ fun s => le_max_left _ _)
      (measurable_deltaFinitDensity lam F.policy F.outflow Finit).aestronglyMeasurable,
    inferenceDefect_eq_withDensity lam F Finit hinit hout hin,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- **The printed `δ` is minus the negative-part mass**: `∫ min(0, f_init + f_in − f_out) dλ =
−(F_init + F_in − F_out)⁻(𝒮) ≤ 0`. -/
theorem integral_deltaFinitDensityPrinted (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    ∫ s, deltaFinitDensityPrinted lam F.policy F.outflow Finit s ∂lam
      = -(inferenceDefect F.policy F.outflow Finit Set.univ).toReal := by
  simp_rw [deltaFinitDensityPrinted_eq_neg]
  rw [integral_neg, integral_deltaFinitDensity lam F Finit hinit hout hin]

end Densities

/-- `κ̂ ≠ 0` for a probability `F_init`: its mass is `1 + δ ≥ 1`. -/
theorem kappaHat_ne_zero (F : GenerativeFlow S) (Finit : Measure S) [IsProbabilityMeasure Finit] :
    kappaHat F.policy F.outflow Finit ≠ 0 := by
  obtain ⟨-, -, hmass, -, -⟩ := sampling_error_control F (Finit := Finit) (κ := Finit)
  intro h
  have h1 : (1 : ℝ≥0∞) ≤ kappaHat F.policy F.outflow Finit Set.univ := hmass ▸ le_self_add
  rw [h] at h1
  simp at h1

instance isProbabilityMeasure_normalize_kappaHat (F : GenerativeFlow S) (Finit : Measure S)
    [IsProbabilityMeasure Finit] :
    IsProbabilityMeasure (normalize (kappaHat F.policy F.outflow Finit)) :=
  ⟨normalize_univ _ (kappaHat_ne_zero F Finit)⟩

/-- `(x/2)^{1/2} = √(½ x)` for a finite `x ∈ [0, ∞)`. -/
theorem rpow_half_div_two {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (x / 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (1 / 2 * x.toReal)) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos two_pos,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow]
  congr 2
  ring

/-! ## `cor:pinsker_negative_control`, density form -/

/-- **`cor:pinsker_negative_control` in the paper's densities** (`main.tex:374–380`), with
`δ := ∫ δf_init dλ` and `δf_init := max(0, −(f_init + f_in − f_out))` (the negative part; printed
`min(0, ·)` at `main.tex:362`), under the presuppositions of `main.tex:196`: `F_init, F_out ≪ λ`
and `InflowAC λ F` (`F_in ≪ λ`). -/
theorem pinsker_negative_control_density (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {Finit κ : Measure S} [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ) := by
  have h := pinsker_negative_control F (Finit := Finit) (κ := κ)
  rw [integral_deltaFinitDensity lam F Finit hinit hout hin]
  have hd : inferenceDefect F.policy F.outflow Finit Set.univ ≠ ∞ := measure_ne_top _ _
  have e : ENNReal.ofReal ((inferenceDefect F.policy F.outflow Finit Set.univ).toReal
      / (1 + (inferenceDefect F.policy F.outflow Finit Set.univ).toReal))
      = inferenceDefect F.policy F.outflow Finit Set.univ
        / (1 + inferenceDefect F.policy F.outflow Finit Set.univ) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hd]
  rw [e]; exact h

/-- The density form in `ℝ`, the printed shape, when the divergence is finite. -/
theorem pinsker_negative_control_real (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {Finit κ : Measure S} [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F)
    (hKL : klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ ≠ ∞) :
    (tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ).toReal
      ≤ (∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
        + Real.sqrt (1 / 2 * (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ).toReal) := by
  have h := pinsker_negative_control_density lam F (κ := κ) hinit hout hin
  have hδ0 : 0 ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam :=
    integral_nonneg fun s => le_max_left _ _
  rw [rpow_half_div_two hKL, ← ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-! ## The printed sign is false -/

/-- **`cor:pinsker_negative_control` as printed**, with `δ := ∫ min(0, f_init + f_in − f_out) dλ`
(`main.tex:362`, `:377–379`), in `ℝ`. Its `.toReal` turns `KL = ∞` into `0`, so where `KL = ∞` this
form is stronger than the printed one; the refutation below uses it only where `KL = 0`. -/
def PinskerNegativeControlPrinted (lam : Measure S) (F : GenerativeFlow S) (Finit κ : Measure S) :
    Prop :=
  (tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ).toReal
    ≤ (∫ s, deltaFinitDensityPrinted lam F.policy F.outflow Finit s ∂lam)
        / (1 + ∫ s, deltaFinitDensityPrinted lam F.policy F.outflow Finit s ∂lam)
      + Real.sqrt (1 / 2 * (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ).toReal)

/-- **Finding: the printed form is false.** For every flow with `0 < (F_init + F_in − F_out)⁻(𝒮) < 1`
whose densities exist, at the target probability `κ := κ̂/κ̂(𝒮)` (an instance) the divergence
is `0` and the printed right side is `−E⁻(𝒮)/(1 − E⁻(𝒮)) < 0 ≤ TV`. -/
theorem printed_false_of_mem_Ioo (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S)
    {Finit : Measure S} [IsProbabilityMeasure Finit] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F)
    (hδ : 0 < inferenceDefect F.policy F.outflow Finit Set.univ)
    (hδ1 : inferenceDefect F.policy F.outflow Finit Set.univ < 1) :
    ¬ PinskerNegativeControlPrinted lam F Finit (normalize (kappaHat F.policy F.outflow Finit)) := by
  intro h
  unfold PinskerNegativeControlPrinted at h
  rw [klDiv_self, ENNReal.toReal_zero, mul_zero, Real.sqrt_zero, add_zero,
    integral_deltaFinitDensityPrinted lam F Finit hinit hout hin] at h
  have hd0 : 0 < (inferenceDefect F.policy F.outflow Finit Set.univ).toReal :=
    ENNReal.toReal_pos hδ.ne' (measure_ne_top _ _)
  have hd1 : (inferenceDefect F.policy F.outflow Finit Set.univ).toReal < 1 :=
    ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_one])
  have hneg : -(inferenceDefect F.policy F.outflow Finit Set.univ).toReal
      / (1 + -(inferenceDefect F.policy F.outflow Finit Set.univ).toReal) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by linarith)
  have := (h.trans_lt hneg)
  exact absurd this (not_lt.2 ENNReal.toReal_nonneg)

/-! ## A flow refuting the printed sign -/

namespace Swap

/-- The swap policy `b ↦ ¬b` on `Bool`, with star outflow `½ δ_false`. -/
noncomputable def flow : GenerativeFlow Bool where
  policy := Kernel.deterministic (fun b => !b) (measurable_of_countable _)
  outflow := (2⁻¹ : ℝ≥0) • Measure.dirac false
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

theorem inflow_false : inflow flow.policy flow.outflow {false} = 0 := by
  rw [inflow, Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
  simp [flow, Kernel.deterministic_apply]

/-- `δ = (F_init + F_in − F_out)⁻(𝒮) = ½` for `F_init = δ_true`. -/
theorem inferenceDefect_univ :
    inferenceDefect flow.policy flow.outflow (Measure.dirac true) Set.univ = 2⁻¹ := by
  rw [TwoPoint.measure_univ_eq, inferenceDefect,
    sub_apply_eq_zero_of_null _ _ (by simp [flow] : flow.outflow {true} = 0),
    sub_apply_of_null (A := {false}) (by rw [Measure.add_apply, inflow_false]; simp)]
  simp [flow]

theorem ac_count (μ : Measure Bool) : μ ≪ Measure.count := fun s hs => by
  rw [Measure.count_eq_zero_iff.1 hs, measure_empty]

/-- **`cor:pinsker_negative_control` as printed is false.** On `Bool` with the counting measure
`λ`, the swap policy, `F_out = ½ δ_false`, `F_init = δ_true` and the target probability
`κ = κ̂/κ̂(𝒮)`: every presupposition holds (`F_init, F_out, F_in ≪ λ`), the printed `δ` is `−½`,
the divergence is `0`, and the printed bound `δ/(1 + δ) + √(½ KL) = −1` is negative, below the
total variation. -/
theorem printed_pinsker_negative_control_false :
    InflowAC Measure.count flow ∧
    ∫ s, deltaFinitDensityPrinted Measure.count flow.policy flow.outflow (Measure.dirac true) s
      ∂Measure.count = -(1 / 2) ∧
    ∫ s, deltaFinitDensity Measure.count flow.policy flow.outflow (Measure.dirac true) s
      ∂Measure.count = 1 / 2 ∧
    klDiv (normalize (kappaHat flow.policy flow.outflow (Measure.dirac true)))
      (normalize (kappaHat flow.policy flow.outflow (Measure.dirac true))) = 0 ∧
    ¬ PinskerNegativeControlPrinted Measure.count flow (Measure.dirac true)
      (normalize (kappaHat flow.policy flow.outflow (Measure.dirac true))) := by
  refine ⟨ac_count _, ?_, ?_, klDiv_self _, printed_false_of_mem_Ioo Measure.count flow
    (ac_count _) (ac_count _) (ac_count _) ?_ ?_⟩
  · rw [integral_deltaFinitDensityPrinted Measure.count flow (Measure.dirac true) (ac_count _)
      (ac_count _) (ac_count _), inferenceDefect_univ]
    simp
  · rw [integral_deltaFinitDensity Measure.count flow (Measure.dirac true) (ac_count _)
      (ac_count _) (ac_count _), inferenceDefect_univ]
    simp
  · rw [inferenceDefect_univ]; norm_num
  · rw [inferenceDefect_univ]; exact ENNReal.inv_lt_one.2 (by norm_num)

end Swap

/-! ## For an EGF, `F_in ≪ λ` is a theorem -/

/-- **For an EGF, the presupposition `F_in ≪ λ` holds**, by `EGF.inflow_eq_withDensity`
(`main.tex:737`), when `F_out = f_out λ` (`main.tex:732`) and `Φᵢ₊λ = Jᵢ λ`. -/
theorem inflowAC_of_isEGFPolicy (lam : Measure S) {p : ℕ} (Φ : Fin p → S ≃ᵐ S)
    (J : Fin p → S → ℝ≥0∞) (hJm : ∀ i, Measurable (J i))
    (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i)) (F : GenerativeFlow S)
    {α : Fin p → S → ℝ} (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞}
    (hf : Measurable fout) (hout : F.outflow = lam.withDensity fout) : InflowAC lam F := by
  unfold InflowAC
  rw [hout, inflow_eq_withDensity lam Φ J hJm hJ hπ hf]
  exact withDensity_absolutelyContinuous _ _

/-- **`cor:pinsker_negative_control` for an EGF** (`def:egf`), in the density form, with no
named hypothesis: `F_in ≪ λ` is discharged by `inflowAC_of_isEGFPolicy`. The maps are the
homeomorphisms of `EGF.IsEGF`, measurable for the Borel σ-algebra. -/
theorem pinsker_negative_control_isEGF [TopologicalSpace S] [BorelSpace S] (lam : Measure S)
    [SigmaFinite lam] (F : GenerativeFlow S) {p : ℕ} {Φ : Fin p → S ≃ₜ S} {α : Fin p → S → ℝ}
    (hE : IsEGF F Φ α) (J : Fin p → S → ℝ≥0∞) (hJm : ∀ i, Measurable (J i))
    (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i)) {fout : S → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) {Finit κ : Measure S} [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ) := by
  have hπ : IsEGFPolicy F.policy (fun i => ((Φ i).toMeasurableEquiv : S → S)) α := by
    simpa only [Homeomorph.toMeasurableEquiv_coe] using hE.policy
  have hJ' : ∀ i, lam.map ((Φ i).toMeasurableEquiv) = lam.withDensity (J i) := by
    intro i; rw [Homeomorph.toMeasurableEquiv_coe]; exact hJ i
  have hac : F.outflow ≪ lam := by
    rw [hout]; exact withDensity_absolutelyContinuous _ _
  exact pinsker_negative_control_density lam F hinit hac
    (inflowAC_of_isEGFPolicy lam (fun i => (Φ i).toMeasurableEquiv) J hJm hJ' F hπ hf hout)

end EGF
