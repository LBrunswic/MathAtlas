import EGF.SamplingCorollaries
import EGF.InflowNonsingular

/-!
# The KL-weakFM loss, the KL decomposition, and the loss bound on the sampling error

`cor:pinsker_negative_control` — `main.tex:374` (with Eq. (15) `main.tex:362–366`, Algorithm 1
`main.tex:383–404` and the discussion `main.tex:405–425`). No mark: the label is marked in
`EGF/SamplingCorollaries.lean` in its corrected form of record (DEC-141, C-1); this file proves
its reverse direction (C-5), the loss of Eq. (15) and its control of the sampling error (C-2,
C-35), Algorithm 1's weights (C-3) and the EGF forms without `InflowAC` (C-6).

> Let $\deltafinit=\min(0,\finit+\finstar-\foutstar)$  and
> $\ftermhat = \max(0,\finit+\finstar-\foutstar)$. The KL-weakFM loss can then be defined as
> follows: $\mathcal L_{KL-wFM} (\theta) := b\mathbb E_{s\sim \nu_{\mathrm{train}}} \deltafinit( s)-
> \mathbb E_{s\sim \target}\log \ftermhat(s)$, for some training distribution of paths
> $\nu_{\mathrm{train}}$ and  $b>0$. (`main.tex:362–366`)

> Let $(\ForwardPolicyStar, \foutstar)$ be a generative flow. We train the generative flow on
> target probability distribution $\target$ with $\Finit(\Statespace)=1$. By using
> $\Fterm=\widehat\target:= \left(\Finit+\Finstar-\Foutstar\right)^+$ during inference, the
> sampling error is bounded as follow: $\TV\left(s_\tau \left\| \target \right.\right) \leq
> \frac{\delta}{1+\delta} +\sqrt{\frac{1}{2}\KL\left(\left.\frac{\widehat\target}{\widehat\target(\Statespace)}
> \right\| \target \right)}$, with $\delta := \int_{s\in\Statespace} \deltafinit(s)d\lambda(s)$.
> (`main.tex:374–380`)

> Third, more precisely, the KL term may be decomposed into
> $\KL\left(\left.\frac{\widehat\target}{\widehat\target(\Statespace)} \right\| \target \right) =
> \underbrace{-\mathbb E_{s\sim \target}\log \ftermhat(s)}_{\text{cross-entropy}} +
> \underbrace{\log \int_{s\in \Statespace} \ftermhat(s)d\lambda(s)}_{\text{normalization}}
> -  \mathcal H(\kappa)$, where $\mathcal H(\kappa)=-\mathbb E_{s\sim \kappa}
> \log\frac{d\kappa}{d\lambda}(s) $ is the entropy of $\kappa$. (`main.tex:416–420`)

> $p_t(\underline s) =\prod_{t'<t}  \left(1+(\ftermhat/\foutstar)(\underline s_{t'})\right)^{-1}$
> if $\underline s\in \mathcal B_{\rightarrow}$, $=\prod_{t'<t}
> \left(1+(\deltafinit/\finstar)(\underline s_{t'})\right)^{-1}$ if
> $\underline s\in \mathcal B_{\leftarrow}$ (`main.tex:399–400`)

## Hypothesis checklist

| paper | here |
|---|---|
| `δf_init = min(0, ·)` (`:362`) | ✗ corrected (C-1, C-2): `deltaFinitDensity = max(0, −·)`; printed kept (`klwfmLossPrinted`, `SwapM.printed_loss_tendsto_bot`) |
| `b > 0` (`:366`) | ⚠ the control holds for `b ≥ 1 + N` with `λ ≤ N ν_train` (C-35), the floor `H ≤ L` for `b ≥ N` (sufficient, not shown necessary); `SwapM.loss_lt_entropy`: `0 < b < log 2` breaks the floor |
| `ν_train` "a training distribution of paths" | ⚠ read: a measure on states, `E_{ν_train} = ∫ · dν_train` (any measure; a probability in the paper) |
| `κ` a target probability, `H(κ)` (`:405`, `:420`) | ✓ `κ ≪ λ`, `log dκ/dλ ∈ L¹(κ)` (finite entropy) |
| `L` in `(−∞, +∞]` | ✓ `klwfmLoss : EReal`, `⊤` off `LossFinite` (justified: `crossEntropy_posPart_integrable`) |
| `f = dF/dλ` (`:196`) | ✓ `F_init, F_out ≪ λ`, `InflowAC`; for an EGF, nonsingular moves (C-6) |
| `(𝒮, λ)` Polish, `λ` finite | ⚠ weakened: any measurable space, `λ` σ-finite |
| `KL(κ̂/κ̂(𝒮) ‖ κ)` at `:418` | ✗ false (`Null.printed_kl_decomposition_false_finite`); true for `KL(κ ‖ κ̂/κ̂(𝒮))` (C-5) |
| `p_t` backward, `δf_init/f_in` (`:400`) | ✗ printed sign: negative (`Swap3`); corrected: in `(0, 1]`; if `B←` holds reversed-sampler paths (a reading, OQ-83), the factor is `(f_init + δf_init)/f_in` |

## SCOPE (disclosed)

`cor:pinsker_negative_control` is not marked here (it is marked in the strict tree). No `sorry`.
Proved: Eq. (15) with the negative part and its `+∞` (`klwfmLoss`); the decomposition of
`main.tex:418` in the direction `KL(κ ‖ κ̂/κ̂(𝒮))` (`kl_decomposition`, its `+∞` case
`klDiv_eq_top_iff_crossEntropy`), the printed direction refuted with both sides finite
(`Null.printed_kl_decomposition_false_finite`); Corollary 3.10 for that direction and for the
smaller divergence (`pinsker_negative_control_rev`, `_min`); the loss floor and the loss bound on
the sampling error at `q = 1` (`loss_ge_entropy`, `loss_controls_defect`, `loss_controls_sampling`,
`_essSup`, ported from `GFNBounds.Core.il_tv_bound`, its three external inputs discharged: the
negative control by `sampling_error_control`, Pinsker by `EGF.pinsker`, the triangle inequality by
`tvDist_triangle`), inhabited (`Null.loss_controls_sampling_inhabited`, `SwapM.lossFinite`);
Algorithm 1's weights (`algBackwardFactor_mem_Ioc`, `Swap3.printed_algBackwardFactor_neg`;
the forward one is the sampler's continuation, `cont_kappaHat_ae_eq`); the finding that the
backward weight of `main.tex:400` is not the reversed sampler's (which law `B←` holds is a reading,
OQ-83; that the reversed sampler is the time reversal of the forward paths is not proved here) (`reverse_isFlowMatching_iff`,
`reverse_sampling_posterior`, `reverse_cont_ae_eq`, `algBackwardFactorReversed_eq`,
`printed_reverse_not_isFlowMatching`); the EGF forms with nonsingular moves (`*_nonsingular`).
Not proved: that the reversed sampler's path law is the time reversal of the forward one (only
flow matching, its terminal and its continuation are); Algorithm 1's Monte-Carlo estimator as an
estimator of `E_{ν_train} δf_init`; the squared penalty of `main.tex:407` (C-35).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-! ## 1. The KL-weakFM loss of Eq. (15) -/

/-- **The entropy** `H(κ) = −E_κ log dκ/dλ` (`main.tex:420`). -/
noncomputable def entropy (lam κ : Measure S) : ℝ := -∫ s, Real.log (dens lam κ s) ∂κ

-- ported from GFNBounds.Core.ILBoundFull.LossFinite (lean/GFNBounds/Core/ILBoundFull.lean:510)
/-- **The loss is finite**: `κ` does not charge `{f̂_term = 0}` (else `−E_κ log f̂_term = +∞`), the
cross-entropy integrand is `κ`-integrable, and the penalty `δf_init` is `ν_train`-integrable. -/
structure LossFinite (lam νtrain : Measure S) (F : GenerativeFlow S) (Finit κ : Measure S) :
    Prop where
  pos : ∀ᵐ s ∂κ, 0 < ftermHatDensity lam F.policy F.outflow Finit s
  ce : Integrable (fun s => Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ
  pen : Integrable (deltaFinitDensity lam F.policy F.outflow Finit) νtrain

-- ported from GFNBounds.Core.wklfmLoss (lean/GFNBounds/Core/ILBound.lean:177), at q = 1
/-- The real value of Eq. (15): `b E_{ν_train} δf_init − E_κ log f̂_term`, `δf_init` the negative
part (C-1, C-2). It is the loss where `LossFinite` holds. -/
noncomputable def klwfmLossReal (lam νtrain : Measure S) (b : ℝ) (F : GenerativeFlow S)
    (Finit κ : Measure S) : ℝ :=
  b * ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain
    - ∫ s, Real.log (ftermHatDensity lam F.policy F.outflow Finit s) ∂κ

-- ported from GFNBounds.Core.ILBoundFull.ilLoss (lean/GFNBounds/Core/ILBoundFull.lean:518)
open Classical in
/-- **The KL-weakFM loss** `L_{KL-wFM}` (Eq. (15), `main.tex:363–366`), with `δf_init` the negative
part (C-1, C-2): `klwfmLossReal` where the loss is finite, `⊤` elsewhere. The `⊤` is the paper's
own value when `b > 0` and `H(κ)` is finite (`crossEntropy_posPart_integrable`), which every
theorem below assumes. -/
noncomputable def klwfmLoss (lam νtrain : Measure S) (b : ℝ) (F : GenerativeFlow S)
    (Finit κ : Measure S) : EReal :=
  if LossFinite lam νtrain F Finit κ then ((klwfmLossReal lam νtrain b F Finit κ : ℝ) : EReal)
  else ⊤

/-- Eq. (15) **as printed**, with `δf_init = min(0, ·)` (`main.tex:362`), in `ℝ`. -/
noncomputable def klwfmLossRealPrinted (lam νtrain : Measure S) (b : ℝ) (F : GenerativeFlow S)
    (Finit κ : Measure S) : ℝ :=
  b * ∫ s, deltaFinitDensityPrinted lam F.policy F.outflow Finit s ∂νtrain
    - ∫ s, Real.log (ftermHatDensity lam F.policy F.outflow Finit s) ∂κ

open Classical in
/-- Eq. (15) **as printed**, in `[−∞, +∞]`: `+∞` where the cross-entropy is, `−∞` where only the
(non-positive) printed penalty is infinite. -/
noncomputable def klwfmLossPrinted (lam νtrain : Measure S) (b : ℝ) (F : GenerativeFlow S)
    (Finit κ : Measure S) : EReal :=
  if (∀ᵐ s ∂κ, 0 < ftermHatDensity lam F.policy F.outflow Finit s) ∧
      Integrable (fun s => Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ then
    (if Integrable (deltaFinitDensityPrinted lam F.policy F.outflow Finit) νtrain then
      ((klwfmLossRealPrinted lam νtrain b F Finit κ : ℝ) : EReal) else ⊥)
  else ⊤

theorem klwfmLoss_of_finite {lam νtrain : Measure S} {b : ℝ} {F : GenerativeFlow S}
    {Finit κ : Measure S} (h : LossFinite lam νtrain F Finit κ) :
    klwfmLoss lam νtrain b F Finit κ = ((klwfmLossReal lam νtrain b F Finit κ : ℝ) : EReal) := by
  rw [klwfmLoss, if_pos h]

theorem lossFinite_of_ne_top {lam νtrain : Measure S} {b : ℝ} {F : GenerativeFlow S}
    {Finit κ : Measure S} (h : klwfmLoss lam νtrain b F Finit κ ≠ ⊤) :
    LossFinite lam νtrain F Finit κ := by
  by_contra hc
  exact h (by rw [klwfmLoss, if_neg hc])

theorem measurable_ftermHatDensity (lam : Measure S) (π : Kernel S S) (Fout Finit : Measure S) :
    Measurable (ftermHatDensity lam π Fout Finit) :=
  measurable_const.max (measurable_defectDensity lam π Fout Finit)

theorem measurable_dens (lam μ : Measure S) : Measurable (dens lam μ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- A σ-finite `μ ≪ λ` is `(dμ/dλ) λ`, with the real density `dens`. -/
theorem eq_withDensity_dens {lam μ : Measure S} [SigmaFinite lam] [SigmaFinite μ] (hμ : μ ≪ lam) :
    μ = lam.withDensity fun s => ENNReal.ofReal (dens lam μ s) := by
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ lam hμ]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top μ lam] with x hx
  simp [dens, ENNReal.ofReal_toReal hx]

/-! ## 2. The KL decomposition of `main.tex:418`, in its true direction -/

section Decomposition

variable (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S) {Finit κ : Measure S}
  [IsProbabilityMeasure Finit]

/-- `∫ f̂_term dλ = κ̂(𝒮)`. -/
theorem integral_ftermHatDensity (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    ∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam
      = (kappaHat F.policy F.outflow Finit Set.univ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := ftermHatDensity lam F.policy F.outflow Finit)
      (ae_of_all _ fun s => le_max_left _ _)
      (measurable_ftermHatDensity lam F.policy F.outflow Finit).aestronglyMeasurable,
    kappaHat_eq_withDensity lam F Finit hinit hout hin, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

/-- **`main.tex:423`**, with the negative-part `δf_init` (C-4): `∫ f̂_term dλ = 1 + ∫ δf_init dλ`. -/
theorem integral_ftermHatDensity_eq (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    ∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam
      = 1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam := by
  obtain ⟨-, -, hmass, -, -⟩ := sampling_error_control F (Finit := Finit) (κ := Finit)
  rw [integral_ftermHatDensity lam F hinit hout hin,
    integral_deltaFinitDensity lam F Finit hinit hout hin, hmass,
    ENNReal.toReal_add ENNReal.one_ne_top (measure_ne_top _ _), ENNReal.toReal_one]

/-- `κ ≪ κ̂` iff `κ` does not charge `{f̂_term = 0}` (for `κ ≪ λ`). -/
theorem ac_kappaHat_iff (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam) (hin : InflowAC lam F)
    (hκ : κ ≪ lam) :
    κ ≪ kappaHat F.policy F.outflow Finit
      ↔ ∀ᵐ s ∂κ, 0 < ftermHatDensity lam F.policy F.outflow Finit s := by
  have hKd := kappaHat_eq_withDensity lam F Finit hinit hout hin
  have hfm := measurable_ftermHatDensity lam F.policy F.outflow Finit
  have hgm : Measurable fun s => ENNReal.ofReal (ftermHatDensity lam F.policy F.outflow Finit s) :=
    ENNReal.measurable_ofReal.comp hfm
  constructor
  · intro h
    have hA : kappaHat F.policy F.outflow Finit
        {s | ¬ 0 < ftermHatDensity lam F.policy F.outflow Finit s} = 0 := by
      rw [hKd, withDensity_apply_eq_zero' hgm.aemeasurable]
      refine measure_mono_null (fun s hs => ?_) measure_empty
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le,
        not_lt] at hs
      exact absurd hs.1 (not_lt.2 hs.2)
    exact ae_iff.2 (h hA)
  · intro hpos A hA
    rw [hKd, withDensity_apply_eq_zero' hgm.aemeasurable] at hA
    have h2 := hκ hA
    have h3 : κ {s | ¬ 0 < ftermHatDensity lam F.policy F.outflow Finit s} = 0 := ae_iff.1 hpos
    refine measure_mono_null (fun s hs => ?_) (measure_union_null h2 h3)
    by_cases hs0 : 0 < ftermHatDensity lam F.policy F.outflow Finit s
    · left
      refine ⟨?_, hs⟩
      simp only [Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hs0
    · right; exact hs0

/-- The log-likelihood ratio of `κ` against `κ̂/κ̂(𝒮)`:
`log dκ/d(κ̂/κ̂(𝒮)) = log dκ/dλ − log f̂_term + log ∫ f̂_term dλ`, `κ`-a.e. -/
theorem llr_normalize_kappaHat_ae [IsFiniteMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hκκ : κ ≪ kappaHat F.policy F.outflow Finit) :
    llr κ (normalize (kappaHat F.policy F.outflow Finit))
      =ᵐ[κ] fun s => Real.log (dens lam κ s)
        - Real.log (ftermHatDensity lam F.policy F.outflow Finit s)
        + Real.log (∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam) := by
  set K := kappaHat F.policy F.outflow Finit with hKdef
  set f := ftermHatDensity lam F.policy F.outflow Finit with hf
  have hfm : Measurable f := measurable_ftermHatDensity lam F.policy F.outflow Finit
  have hKd : K = lam.withDensity fun s => ENNReal.ofReal (f s) :=
    kappaHat_eq_withDensity lam F Finit hinit hout hin
  have hK0 : K ≠ 0 := kappaHat_ne_zero F Finit
  have hZ0 : K Set.univ ≠ 0 := fun h => hK0 (Measure.measure_univ_eq_zero.1 h)
  have hZt : K Set.univ ≠ ∞ := measure_ne_top _ _
  have hZ : ∫ s, f s ∂lam = (K Set.univ).toReal := integral_ftermHatDensity lam F hinit hout hin
  have hKl : K ≪ lam := by rw [hKd]; exact withDensity_absolutelyContinuous _ _
  have hρl : normalize K ≪ lam := Measure.smul_absolutelyContinuous.trans hKl
  have hκρ : κ ≪ normalize K := hκκ.smul_right (ENNReal.inv_ne_zero.2 hZt)
  have h1 : κ.rnDeriv (normalize K) =ᵐ[κ]
      fun x => κ.rnDeriv lam x / (normalize K).rnDeriv lam x :=
    hκρ.ae_le (Measure.rnDeriv_eq_div hκ hρl)
  have h2 : (normalize K).rnDeriv lam =ᵐ[lam] (K Set.univ)⁻¹ • K.rnDeriv lam :=
    Measure.rnDeriv_smul_left_of_ne_top K lam (ENNReal.inv_ne_top.2 hZ0)
  have h3 : K.rnDeriv lam =ᵐ[lam] fun s => ENNReal.ofReal (f s) := by
    rw [hKd]; exact Measure.rnDeriv_withDensity lam (ENNReal.measurable_ofReal.comp hfm)
  have h4 : ∀ᵐ x ∂κ, 0 < κ.rnDeriv lam x := Measure.rnDeriv_pos hκ
  have h5 : ∀ᵐ x ∂κ, κ.rnDeriv lam x < ∞ := hκ.ae_le (Measure.rnDeriv_lt_top κ lam)
  have h6 : ∀ᵐ x ∂κ, 0 < (normalize K).rnDeriv lam x := hκρ.ae_le (Measure.rnDeriv_pos hρl)
  filter_upwards [h1, hκ.ae_le h2, hκ.ae_le h3, h4, h5, h6] with x e1 e2 e3 p4 p5 p6
  have e23 : (normalize K).rnDeriv lam x = (K Set.univ)⁻¹ * ENNReal.ofReal (f x) := by
    rw [e2, Pi.smul_apply, e3, smul_eq_mul]
  rw [e23] at p6 e1
  have hf0 : 0 ≤ f x := le_max_left _ _
  have hfx : 0 < f x := by
    by_contra hc
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hc), mul_zero] at p6
    exact lt_irrefl _ p6
  have hk : 0 < (κ.rnDeriv lam x).toReal := ENNReal.toReal_pos p4.ne' p5.ne
  have hZr : 0 < (K Set.univ).toReal := ENNReal.toReal_pos hZ0 hZt
  rw [llr_def]
  simp only
  rw [e1, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hf0,
    Real.log_div hk.ne' (mul_pos (inv_pos.2 hZr) hfx).ne', Real.log_mul (inv_pos.2 hZr).ne' hfx.ne',
    Real.log_inv, hZ, dens]
  ring

-- ported from GFNBounds.Core.ILBoundFull.crossEntropy_decomposition
-- (lean/GFNBounds/Core/ILBoundFull.lean:412)
/-- **The KL decomposition of `main.tex:416–420`, in its true direction** (C-5): for a
probability `κ ≪ λ` of finite entropy with `κ ≪ κ̂` and a finite cross-entropy, Mathlib's
`KL(κ ‖ κ̂/κ̂(𝒮))` is finite and
`KL(κ ‖ κ̂/κ̂(𝒮)) = −E_κ log f̂_term + log ∫ f̂_term dλ − H(κ)`. -/
theorem kl_decomposition [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hκκ : κ ≪ kappaHat F.policy F.outflow Finit)
    (hce : Integrable (fun s => Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ) :
    klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) ≠ ∞ ∧
    (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal
      = -∫ s, Real.log (ftermHatDensity lam F.policy F.outflow Finit s) ∂κ
        + Real.log (∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam)
        - entropy lam κ := by
  have hK0 := kappaHat_ne_zero F Finit
  have hκρ : κ ≪ normalize (kappaHat F.policy F.outflow Finit) :=
    hκκ.smul_right (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
  have hllr := llr_normalize_kappaHat_ae lam F hinit hout hin hκ hκκ
  have hint : Integrable (llr κ (normalize (kappaHat F.policy F.outflow Finit))) κ :=
    ((hent.sub hce).add (integrable_const _)).congr hllr.symm
  refine ⟨klDiv_ne_top hκρ hint, ?_⟩
  have hsub : Integrable (fun s => Real.log (dens lam κ s)
      - Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ := hent.sub hce
  rw [toReal_klDiv_of_measure_eq hκρ (by rw [measure_univ, normalize_univ _ hK0]),
    integral_congr_ae hllr, integral_add hsub (integrable_const _),
    integral_sub hent hce, integral_const, entropy]
  simp only [probReal_univ, one_smul]
  ring

/-- **The `+∞` of the decomposition**: with a finite entropy, `KL(κ ‖ κ̂/κ̂(𝒮)) = ∞` exactly when
the cross-entropy is `+∞`: `κ` charges `{f̂_term = 0}` or `log f̂_term ∉ L¹(κ)`. -/
theorem klDiv_eq_top_iff_crossEntropy [IsProbabilityMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ) :
    klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) = ∞
      ↔ ¬ ((∀ᵐ s ∂κ, 0 < ftermHatDensity lam F.policy F.outflow Finit s) ∧
        Integrable (fun s => Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ) := by
  have hK0 := kappaHat_ne_zero F Finit
  constructor
  · rintro htop ⟨hpos, hce⟩
    exact (kl_decomposition lam F hinit hout hin hκ hent
      ((ac_kappaHat_iff lam F hinit hout hin hκ).2 hpos) hce).1 htop
  · intro hnot
    by_contra htop
    obtain ⟨hκρ, hint⟩ := klDiv_ne_top_iff.1 htop
    have hκκ : κ ≪ kappaHat F.policy F.outflow Finit :=
      hκρ.trans Measure.smul_absolutelyContinuous
    have hllr := llr_normalize_kappaHat_ae lam F hinit hout hin hκ hκκ
    refine hnot ⟨(ac_kappaHat_iff lam F hinit hout hin hκ).1 hκκ, ?_⟩
    refine ((hent.sub hint).add (integrable_const
      (Real.log (∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam)))).congr ?_
    filter_upwards [hllr] with s hs
    simp only [Pi.add_apply, Pi.sub_apply, hs]
    ring

/-- `f̂_term ∈ L¹(λ)`: its integral is `κ̂(𝒮) < ∞`. -/
theorem integrable_ftermHatDensity (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) : Integrable (ftermHatDensity lam F.policy F.outflow Finit) lam := by
  refine ⟨(measurable_ftermHatDensity lam F.policy F.outflow Finit).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (f := ftermHatDensity lam F.policy F.outflow Finit)
    (ae_of_all _ fun s => le_max_left _ _)]
  have h : ∫⁻ s, ENNReal.ofReal (ftermHatDensity lam F.policy F.outflow Finit s) ∂lam
      = kappaHat F.policy F.outflow Finit Set.univ := by
    rw [kappaHat_eq_withDensity lam F Finit hinit hout hin, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  rw [h]
  exact measure_lt_top _ _

-- ported from GFNBounds.Core.ILBoundFull.crossEntropy_posPart_integrable
-- (lean/GFNBounds/Core/ILBoundFull.lean:533)
/-- **Why `⊤` is the paper's value of the loss off `LossFinite`**: for `κ ≪ λ` of finite entropy,
`max(log f̂_term, 0) ∈ L¹(κ)`, so a non-integrable `log f̂_term` has `E_κ log f̂_term = −∞`, i.e. a
cross-entropy `+∞`; `κ` charging `{f̂_term = 0}` is `+∞` by `log 0 = −∞`; and a non-integrable
`δf_init ≥ 0` gives `b E_{ν_train} δf_init = +∞` for `b > 0`. -/
theorem crossEntropy_posPart_integrable [IsFiniteMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ) :
    Integrable (fun s => max (Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) 0) κ := by
  set f := ftermHatDensity lam F.policy F.outflow Finit with hfdef
  have hfm : Measurable f := measurable_ftermHatDensity lam F.policy F.outflow Finit
  have hfi : Integrable f lam := integrable_ftermHatDensity lam F hinit hout hin
  have hg : Integrable (fun s => f s / dens lam κ s) κ := by
    refine (integrable_rnDeriv_smul_iff hκ).1 ?_
    refine hfi.mono ((measurable_dens lam κ).mul (hfm.div (measurable_dens lam κ))).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    have hk0 : 0 ≤ (κ.rnDeriv lam s).toReal := ENNReal.toReal_nonneg
    have hf0 : 0 ≤ f s := le_max_left _ _
    simp only [dens]
    rw [smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0,
      abs_of_nonneg (mul_nonneg hk0 (div_nonneg hf0 hk0))]
    rcases eq_or_lt_of_le hk0 with h0 | hpos
    · rw [← h0, zero_mul]; exact hf0
    · rw [mul_div_cancel₀ _ hpos.ne']
  refine (hg.add hent.abs).mono'
    ((Real.measurable_log.comp hfm).max measurable_const).aestronglyMeasurable ?_
  filter_upwards [Measure.rnDeriv_pos hκ, hκ.ae_le (Measure.rnDeriv_lt_top κ lam)] with s h1 h2
  have hk : 0 < dens lam κ s := ENNReal.toReal_pos h1.ne' h2.ne
  have hf0 : 0 ≤ f s := le_max_left _ _
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (by positivity)
  rcases eq_or_lt_of_le hf0 with h0 | hpos
  · rw [← h0, Real.log_zero]; positivity
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hpos hk)
    rw [Real.log_div hpos.ne' hk.ne'] at hlog
    have := le_abs_self (Real.log (dens lam κ s))
    linarith

end Decomposition

/-- **The decomposition of `main.tex:418` as printed**, `KL(κ̂/κ̂(𝒮) ‖ κ)` on its left, in
`(−∞, +∞]`. -/
def KLDecompositionPrinted (lam : Measure S) (F : GenerativeFlow S) (Finit κ : Measure S) :
    Prop :=
  ((klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ : ℝ≥0∞) : EReal)
    = (((-∫ s, Real.log (ftermHatDensity lam F.policy F.outflow Finit s) ∂κ
        + Real.log (∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam)
        - entropy lam κ : ℝ)) : EReal)

/-- **Finding: the printed decomposition is false** whenever `κ̂/κ̂(𝒮)` charges a `κ`-null set
and the true one applies: its right side is then the finite `KL(κ ‖ κ̂/κ̂(𝒮))`, its left side
`KL(κ̂/κ̂(𝒮) ‖ κ) = ∞`. -/
theorem printed_kl_decomposition_false_of_not_ac (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {Finit κ : Measure S} [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hκκ : κ ≪ kappaHat F.policy F.outflow Finit)
    (hce : Integrable (fun s => Real.log (ftermHatDensity lam F.policy F.outflow Finit s)) κ)
    (hnot : ¬ normalize (kappaHat F.policy F.outflow Finit) ≪ κ) :
    -∫ s, Real.log (ftermHatDensity lam F.policy F.outflow Finit s) ∂κ
        + Real.log (∫ s, ftermHatDensity lam F.policy F.outflow Finit s ∂lam) - entropy lam κ
      = (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal ∧
    klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ = ∞ ∧
    ¬ KLDecompositionPrinted lam F Finit κ := by
  obtain ⟨-, hdec⟩ := kl_decomposition lam F hinit hout hin hκ hent hκκ hce
  have htop := klDiv_of_not_ac hnot
  refine ⟨hdec.symm, htop, fun h => ?_⟩
  unfold KLDecompositionPrinted at h
  rw [htop, EReal.coe_ennreal_top] at h
  exact EReal.coe_ne_top _ h.symm

/-- On `Bool`, the density against the counting measure is the mass of the point. -/
theorem rnDeriv_count_bool (μ : Measure Bool) [IsFiniteMeasure μ] (b : Bool) :
    μ.rnDeriv Measure.count b = μ {b} := by
  have hμ : μ = Measure.count.withDensity fun x => μ {x} := by
    rw [Measure.ext_iff_singleton]
    intro a
    rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
      Measure.count_singleton, mul_one]
  have h := Measure.rnDeriv_withDensity Measure.count (f := fun x => μ {x})
    (measurable_of_countable _)
  rw [← hμ] at h
  exact Measure.ae_count_iff.1 h b

theorem dens_count_bool (μ : Measure Bool) [IsFiniteMeasure μ] (b : Bool) :
    dens Measure.count μ b = (μ {b}).toReal := by
  rw [dens, rnDeriv_count_bool]

/-- On `Bool`, `∫ f dμ = μ{true} f(true) + μ{false} f(false)`. -/
theorem integral_bool (μ : Measure Bool) [IsFiniteMeasure μ] (f : Bool → ℝ) :
    ∫ x, f x ∂μ = (μ {true}).toReal * f true + (μ {false}).toReal * f false := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  simp [Measure.real, smul_eq_mul]

namespace Null

/-- The flow with no outflow on `Bool` (any policy: the identity): then `κ̂ = F_init`, and every
probability `κ̂` is reached. -/
noncomputable def flow : GenerativeFlow Bool where
  policy := Kernel.id
  outflow := 0
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

/-- The uniform probability on `Bool`. -/
noncomputable def unif : Measure Bool := (2⁻¹ : ℝ≥0) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure unif := by
  refine ⟨?_⟩
  simp only [unif, Measure.smul_apply, Measure.add_apply, measure_univ, ENNReal.smul_def,
    smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **The printed decomposition of `main.tex:418` is false.** On `Bool` with the counting measure,
the flow with no outflow, `F_init` uniform and `κ = δ_true`: every hypothesis of
`kl_decomposition` holds, `KL(κ ‖ κ̂/κ̂(𝒮))` is finite and equal to the printed right side, and
`KL(κ̂/κ̂(𝒮) ‖ κ) = ∞`. -/
theorem printed_kl_decomposition_false :
    Measure.dirac true ≪ kappaHat flow.policy flow.outflow unif ∧
    Integrable (fun s => Real.log (dens Measure.count (Measure.dirac true) s))
      (Measure.dirac true) ∧
    Integrable (fun s => Real.log (ftermHatDensity Measure.count flow.policy flow.outflow unif s))
      (Measure.dirac true) ∧
    klDiv (Measure.dirac true) (normalize (kappaHat flow.policy flow.outflow unif)) ≠ ∞ ∧
    klDiv (normalize (kappaHat flow.policy flow.outflow unif)) (Measure.dirac true) = ∞ ∧
    ¬ KLDecompositionPrinted Measure.count flow unif (Measure.dirac true) := by
  have hK : kappaHat flow.policy flow.outflow unif = unif := by
    simp [kappaHat, flow, inflow]
  have hnorm : normalize unif = unif := by rw [normalize, measure_univ, inv_one, one_smul]
  have hκκ : Measure.dirac true ≪ kappaHat flow.policy flow.outflow unif := by
    rw [hK]
    intro A hA
    simp only [unif, Measure.smul_apply, Measure.add_apply, ENNReal.smul_def, smul_eq_mul,
      mul_eq_zero, ENNReal.coe_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or,
      add_eq_zero] at hA
    exact hA.1
  have hnot : ¬ normalize (kappaHat flow.policy flow.outflow unif) ≪ Measure.dirac true := by
    rw [hK, hnorm]
    intro h
    have h0 := h (show Measure.dirac true ({false} : Set Bool) = 0 by simp)
    simp [unif, Measure.smul_apply, Measure.add_apply] at h0
  have hent : Integrable (fun s => Real.log (dens Measure.count (Measure.dirac true) s))
      (Measure.dirac true) := Integrable.of_finite
  have hce : Integrable
      (fun s => Real.log (ftermHatDensity Measure.count flow.policy flow.outflow unif s))
      (Measure.dirac true) := Integrable.of_finite
  have hdec := kl_decomposition Measure.count flow (Finit := unif) (κ := Measure.dirac true)
    (Swap.ac_count _) (Swap.ac_count _) (Swap.ac_count _) (Swap.ac_count _) hent hκκ hce
  obtain ⟨-, htop, hP⟩ := printed_kl_decomposition_false_of_not_ac Measure.count flow
    (Finit := unif) (κ := Measure.dirac true) (Swap.ac_count _) (Swap.ac_count _)
    (Swap.ac_count _) (Swap.ac_count _) hent hκκ hce hnot
  exact ⟨hκκ, hent, hce, hdec.1, htop, hP⟩

/-- **The loss bound is not vacuous**: on `Bool` with the counting measure, the flow with no
outflow, `F_init = κ` uniform, `ν_train = λ`, `N = 1`, `b = 2`, every hypothesis of
`loss_controls_sampling` holds and the loss is finite. -/
theorem loss_controls_sampling_inhabited :
    Measure.count ≤ ((1 : ℝ≥0) : ℝ≥0∞) • (Measure.count : Measure Bool) ∧
    Integrable (fun s => Real.log (dens Measure.count unif s)) unif ∧
    LossFinite Measure.count Measure.count flow unif unif ∧
    klwfmLoss Measure.count Measure.count 2 flow unif unif ≠ ⊤ := by
  have hd : ∀ s, ftermHatDensity Measure.count flow.policy flow.outflow unif s = 1 / 2 := by
    intro s
    rw [ftermHatDensity, defectDensity, dens_count_bool, dens_count_bool, dens_count_bool]
    cases s <;> simp [flow, inflow, unif, ENNReal.smul_def]
  have hfin : LossFinite Measure.count Measure.count flow unif unif :=
    ⟨ae_of_all _ fun s => by rw [hd]; norm_num, Integrable.of_finite, Integrable.of_finite⟩
  refine ⟨by rw [ENNReal.coe_one, one_smul], Integrable.of_finite, hfin, ?_⟩
  rw [klwfmLoss_of_finite hfin]
  exact EReal.coe_ne_top _

/-- A second probability on `Bool`, `¼ δ_true + ¾ δ_false`. -/
noncomputable def q : Measure Bool :=
  (4⁻¹ : ℝ≥0) • Measure.dirac true + (3 / 4 : ℝ≥0) • Measure.dirac false

theorem q_true : (q {true}).toReal = 1 / 4 := by simp [q]

theorem q_false : (q {false}).toReal = 3 / 4 := by simp [q]

theorem unif_apply (b : Bool) : (unif {b}).toReal = 1 / 2 := by
  cases b <;> simp [unif]

instance : IsProbabilityMeasure q := by
  refine ⟨?_⟩
  rw [TwoPoint.measure_univ_eq]
  simp only [q, Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  simp only [Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp only [Set.indicator, Set.mem_singleton_iff, Bool.false_eq_true, Bool.true_eq_false,
    if_false, mul_zero, add_zero, zero_add, Pi.one_apply]
  rw [← ENNReal.coe_add, ← ENNReal.coe_one]
  congr 1
  norm_num

/-- With no outflow, `κ̂ = F_init`. -/
theorem kappaHat_eq (μ : Measure Bool) [IsFiniteMeasure μ] :
    kappaHat flow.policy flow.outflow μ = μ := by
  simp [kappaHat, flow, inflow]

/-- With no outflow, `f̂_term = f_init`. -/
theorem ftermHat_eq (μ : Measure Bool) [IsFiniteMeasure μ] (b : Bool) :
    ftermHatDensity Measure.count flow.policy flow.outflow μ b = (μ {b}).toReal := by
  rw [ftermHatDensity, defectDensity, dens_count_bool, dens_count_bool, dens_count_bool]
  simp [flow, inflow]

/-- **The printed decomposition of `main.tex:418` is false with both divergences finite.** On
`Bool` with the counting measure and no outflow, `κ̂ = F_init` uniform and `κ = ¼ δ_true + ¾ δ_false`:
`KL(κ ‖ κ̂/κ̂(𝒮)) = ¾ log 3 − log 2` (the printed right side, by `kl_decomposition`) and
`KL(κ̂/κ̂(𝒮) ‖ κ) = log 2 − ½ log 3` (the printed left side) are both finite and differ, since
`2⁸ ≠ 3⁵`. -/
theorem printed_kl_decomposition_false_finite :
    klDiv q (normalize (kappaHat flow.policy flow.outflow unif)) ≠ ∞ ∧
    klDiv (normalize (kappaHat flow.policy flow.outflow unif)) q ≠ ∞ ∧
    (klDiv q (normalize (kappaHat flow.policy flow.outflow unif))).toReal
      = 3 / 4 * Real.log 3 - Real.log 2 ∧
    (klDiv (normalize (kappaHat flow.policy flow.outflow unif)) q).toReal
      = Real.log 2 - 1 / 2 * Real.log 3 ∧
    ¬ KLDecompositionPrinted Measure.count flow unif q := by
  have hnu : normalize unif = unif := by rw [normalize, measure_univ, inv_one, one_smul]
  have hnq : normalize q = q := by rw [normalize, measure_univ, inv_one, one_smul]
  have hqu : q ≪ kappaHat flow.policy flow.outflow unif := by
    rw [kappaHat_eq]
    intro A hA
    simp only [unif, Measure.smul_apply, Measure.add_apply, ENNReal.smul_def, smul_eq_mul,
      mul_eq_zero, ENNReal.coe_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or,
      add_eq_zero] at hA
    simp [q, hA.1, hA.2]
  have huq : unif ≪ kappaHat flow.policy flow.outflow q := by
    rw [kappaHat_eq]
    intro A hA
    simp only [q, Measure.smul_apply, Measure.add_apply, ENNReal.smul_def, smul_eq_mul,
      add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hA
    have h1 : Measure.dirac true A = 0 := hA.1.resolve_left (by norm_num)
    have h2 : Measure.dirac false A = 0 := hA.2.resolve_left (by norm_num)
    simp [unif, h1, h2]
  have d1 := kl_decomposition Measure.count flow (Finit := unif) (κ := q) (Swap.ac_count _)
    (Swap.ac_count _) (Swap.ac_count _) (Swap.ac_count _) Integrable.of_finite hqu
    Integrable.of_finite
  have d2 := kl_decomposition Measure.count flow (Finit := q) (κ := unif) (Swap.ac_count _)
    (Swap.ac_count _) (Swap.ac_count _) (Swap.ac_count _) Integrable.of_finite huq
    Integrable.of_finite
  rw [kappaHat_eq, hnq] at d2
  have l2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have l4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l34 : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; norm_num
  have r1 : -∫ s, Real.log (ftermHatDensity Measure.count flow.policy flow.outflow unif s) ∂q
      + Real.log (∫ s, ftermHatDensity Measure.count flow.policy flow.outflow unif s
        ∂Measure.count) - entropy Measure.count q = 3 / 4 * Real.log 3 - Real.log 2 := by
    rw [entropy, integral_count, Fintype.sum_bool, integral_bool, integral_bool]
    simp only [ftermHat_eq, dens_count_bool, unif_apply, q_true, q_false]
    norm_num
    rw [l4, l34, l2]
    ring
  have r2 : -∫ s, Real.log (ftermHatDensity Measure.count flow.policy flow.outflow q s) ∂unif
      + Real.log (∫ s, ftermHatDensity Measure.count flow.policy flow.outflow q s
        ∂Measure.count) - entropy Measure.count unif = Real.log 2 - 1 / 2 * Real.log 3 := by
    rw [entropy, integral_count, Fintype.sum_bool, integral_bool, integral_bool]
    simp only [ftermHat_eq, dens_count_bool, unif_apply, q_true, q_false]
    norm_num
    rw [l4, l34, l2]
    ring
  have hne : Real.log 2 - 1 / 2 * Real.log 3 ≠ 3 / 4 * Real.log 3 - Real.log 2 := by
    intro h
    have h58 : Real.log ((3 : ℝ) ^ 5) = Real.log ((2 : ℝ) ^ 8) := by
      rw [Real.log_pow, Real.log_pow]; push_cast; linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num)) (Set.mem_Ioi.2 (by norm_num)) h58
    norm_num at this
  have e1 : klDiv q (normalize (kappaHat flow.policy flow.outflow unif)) = klDiv q unif := by
    rw [kappaHat_eq, hnu]
  have e2 : klDiv (normalize (kappaHat flow.policy flow.outflow unif)) q = klDiv unif q := by
    rw [kappaHat_eq, hnu]
  refine ⟨d1.1, e2 ▸ d2.1, d1.2.trans r1, e2 ▸ d2.2.trans r2, fun h => ?_⟩
  unfold KLDecompositionPrinted at h
  have h' := congrArg EReal.toReal h
  rw [EReal.toReal_coe_ennreal, EReal.toReal_coe, r1, e2, d2.2, r2] at h'
  exact hne h'

end Null

/-! ## 3. Corollary 3.10 in both directions -/

/-- **`cor:pinsker_negative_control` with `KL(κ ‖ κ̂/κ̂(𝒮))`** (C-5), measure form:
`TV(s_τ ‖ κ) ≤ δ/(1 + δ) + √(½ KL(κ ‖ κ̂/κ̂(𝒮)))`, `δ = (F_init + F_in − F_out)⁻(𝒮)`. -/
theorem pinsker_negative_control_rev (F : GenerativeFlow S) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ inferenceDefect F.policy F.outflow Finit Set.univ
          / (1 + inferenceDefect F.policy F.outflow Finit Set.univ)
        + (klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) / 2) ^ (1 / 2 : ℝ) := by
  have hκ : normalize κ = κ := by rw [normalize, measure_univ, inv_one, one_smul]
  obtain ⟨-, -, -, -, hbound⟩ := sampling_error_control F (Finit := Finit) (κ := κ)
  rw [hκ, tvDist_comm (normalize _) κ] at hbound
  exact hbound.trans (add_le_add le_rfl (pinsker _ _))

/-- **Corollary 3.10 in both directions at once**: the smaller of the two divergences. -/
theorem pinsker_negative_control_min (F : GenerativeFlow S) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ inferenceDefect F.policy F.outflow Finit Set.univ
          / (1 + inferenceDefect F.policy F.outflow Finit Set.univ)
        + min ((klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ))
            ((klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) / 2) ^ (1 / 2 : ℝ)) := by
  have hκ : normalize κ = κ := by rw [normalize, measure_univ, inv_one, one_smul]
  obtain ⟨-, -, -, -, hbound⟩ := sampling_error_control F (Finit := Finit) (κ := κ)
  rw [hκ] at hbound
  refine hbound.trans (add_le_add le_rfl (le_min (pinsker _ _) ?_))
  rw [tvDist_comm]
  exact pinsker _ _

/-- **`cor:pinsker_negative_control` with `KL(κ ‖ κ̂/κ̂(𝒮))`, in the paper's densities**:
`δ = ∫ δf_init dλ`, `δf_init` the negative part. -/
theorem pinsker_negative_control_density_rev (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {Finit κ : Measure S} [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure κ] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) / 2) ^ (1 / 2 : ℝ) := by
  have h := pinsker_negative_control_rev F (Finit := Finit) (κ := κ)
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

/-! ## 4. The loss controls the sampling error -/

/-- `∫ f dμ ≤ N ∫ f dν` for `f ≥ 0`, `ν`-integrable, and `μ ≤ N ν`: the Hölder step at `q = 1`. -/
theorem integral_le_mul_of_le_smul {μ ν : Measure S} {N : ℝ≥0} (h : μ ≤ (N : ℝ≥0∞) • ν)
    {f : S → ℝ} (hf0 : ∀ s, 0 ≤ f s) (hfi : Integrable f ν) :
    ∫ s, f s ∂μ ≤ N * ∫ s, f s ∂ν := by
  have hfi' : Integrable f ((N : ℝ≥0∞) • ν) := hfi.smul_measure ENNReal.coe_ne_top
  calc ∫ s, f s ∂μ ≤ ∫ s, f s ∂((N : ℝ≥0∞) • ν) := integral_mono_measure h (ae_of_all _ hf0) hfi'
    _ = N * ∫ s, f s ∂ν := by rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

-- ported from GFNBounds.Core.negMass_ratio_le_min (lean/GFNBounds/Core/ILBound.lean:427)
/-- `δ/(1 + δ) ≤ min(1, δ)` for `δ ≥ 0`. -/
theorem negMass_ratio_le_min {δ : ℝ} (hδ0 : 0 ≤ δ) : δ / (1 + δ) ≤ min 1 δ := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  refine le_min ?_ ?_
  · rw [div_le_one h1]; linarith
  · rw [div_le_iff₀ h1]; nlinarith

section Loss

variable (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S) {Finit κ : Measure S}
  [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] (νtrain : Measure S) (N : ℝ≥0) (b : ℝ)

-- ported from GFNBounds.Core.loss_sub_selfEntropy_ge (lean/GFNBounds/Core/ILBound.lean:306)
/-- **The chain of the follow-up, at `q = 1`, for every `b`**: where the loss is finite and
`λ ≤ N ν_train`, `KL(κ ‖ κ̂/κ̂(𝒮))` is finite and
`KL(κ ‖ κ̂/κ̂(𝒮)) + (b − N) E_{ν_train} δf_init ≤ L − H(κ)`. -/
theorem loss_sub_entropy_ge (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hN : lam ≤ (N : ℝ≥0∞) • νtrain) (hfin : LossFinite lam νtrain F Finit κ) :
    klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) ≠ ∞ ∧
    (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal
        + (b - N) * ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain
      ≤ klwfmLossReal lam νtrain b F Finit κ - entropy lam κ := by
  obtain ⟨hpos, hce, hpen⟩ := hfin
  have hκκ := (ac_kappaHat_iff lam F hinit hout hin hκ).2 hpos
  obtain ⟨hne, hdec⟩ := kl_decomposition lam F hinit hout hin hκ hent hκκ hce
  refine ⟨hne, ?_⟩
  have hZ := integral_ftermHatDensity_eq lam F hinit hout hin
  have hδ0 : 0 ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam :=
    integral_nonneg fun s => le_max_left _ _
  have hδP : ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam
      ≤ N * ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain :=
    integral_le_mul_of_le_smul hN (fun s => le_max_left _ _) hpen
  have hlog : Real.log (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
      ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ∫ s, deltaFinitDensity lam F.policy F.outflow
      Finit s ∂lam) (by linarith)
    linarith
  rw [hZ] at hdec
  rw [hdec, klwfmLossReal]
  nlinarith

-- ported from GFNBounds.Core.loss_ge_selfEntropy (lean/GFNBounds/Core/ILBound.lean:348)
/-- **The floor of the loss**: `H(κ) ≤ L_{KL-wFM}`, in `(−∞, +∞]`, as soon as `b ≥ N`. -/
theorem loss_ge_entropy (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam) (hin : InflowAC lam F)
    (hκ : κ ≪ lam) (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hN : lam ≤ (N : ℝ≥0∞) • νtrain) (hb : (N : ℝ) ≤ b) :
    ((entropy lam κ : ℝ) : EReal) ≤ klwfmLoss lam νtrain b F Finit κ := by
  by_cases hfin : LossFinite lam νtrain F Finit κ
  · rw [klwfmLoss_of_finite hfin]
    obtain ⟨-, h⟩ := loss_sub_entropy_ge lam F νtrain N b hinit hout hin hκ hent hN hfin
    have hKL : 0 ≤ (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal :=
      ENNReal.toReal_nonneg
    have hP0 : 0 ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain :=
      integral_nonneg fun s => le_max_left _ _
    have hm := mul_nonneg (sub_nonneg.2 hb) hP0
    exact EReal.coe_le_coe_iff.2 (by linarith)
  · rw [klwfmLoss, if_neg hfin]; exact le_top

-- ported from GFNBounds.Core.klD_le_loss_sub_selfEntropy (lean/GFNBounds/Core/ILBound.lean:364)
-- and GFNBounds.Core.lqNormD_le_loss_sub_selfEntropy (lean/GFNBounds/Core/ILBound.lean:378)
/-- **The loss controls the divergence and the defect** (`b ≥ 1 + N`):
`KL(κ ‖ κ̂/κ̂(𝒮)) ≤ L − H(κ)`, `E_{ν_train} δf_init ≤ L − H(κ)` and `δ = ∫ δf_init dλ ≤ N (L − H(κ))`. -/
theorem loss_controls_defect (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hN : lam ≤ (N : ℝ≥0∞) • νtrain) (hb : 1 + (N : ℝ) ≤ b)
    (hfin : LossFinite lam νtrain F Finit κ) :
    (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal
      ≤ klwfmLossReal lam νtrain b F Finit κ - entropy lam κ ∧
    ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain
      ≤ klwfmLossReal lam νtrain b F Finit κ - entropy lam κ ∧
    ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam
      ≤ N * (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ) := by
  obtain ⟨-, h⟩ := loss_sub_entropy_ge lam F νtrain N b hinit hout hin hκ hent hN hfin
  have hKL : 0 ≤ (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal :=
    ENNReal.toReal_nonneg
  have hP0 : 0 ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain :=
    integral_nonneg fun s => le_max_left _ _
  have hm : ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain
      ≤ (b - N) * ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain := by
    nlinarith
  have hδP : ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam
      ≤ N * ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain :=
    integral_le_mul_of_le_smul hN (fun s => le_max_left _ _) hfin.pen
  have hP : ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂νtrain
      ≤ klwfmLossReal lam νtrain b F Finit κ - entropy lam κ := by linarith
  refine ⟨by nlinarith, hP, hδP.trans (mul_le_mul_of_nonneg_left hP N.coe_nonneg)⟩

-- ported from GFNBounds.Core.il_tv_bound (lean/GFNBounds/Core/ILBound.lean:443), its inputs hNC,
-- hPins, htri discharged as GFNBounds.Core.SamplingGeneral.il_first_bullet_general does
-- (lean/GFNBounds/Core/SamplingGeneralBounds.lean:709)
/-- **The loss bound on the sampling error** (C-2, C-35): for `F_init, F_out ≪ λ`, `InflowAC`, a
target probability `κ ≪ λ` of finite entropy, `λ ≤ N ν_train`, `b ≥ 1 + N` and a finite loss
`L = L_{KL-wFM}`, the sampler `s_τ` of `F` from `F_init` to `κ̂` satisfies
`TV(s_τ ‖ κ) ≤ (1/√2) √(L − H(κ)) + min(1, N (L − H(κ)))`. -/
theorem loss_controls_sampling (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hN : lam ≤ (N : ℝ≥0∞) • νtrain) (hb : 1 + (N : ℝ) ≤ b)
    (hL : klwfmLoss lam νtrain b F Finit κ ≠ ⊤) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal (1 / Real.sqrt 2
            * Real.sqrt (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ)
          + min 1 (N * (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ))) := by
  have hfin := lossFinite_of_ne_top hL
  obtain ⟨hKL1, -, hδ1⟩ := loss_controls_defect lam F νtrain N b hinit hout hin hκ hent hN hb hfin
  have hne := (loss_sub_entropy_ge lam F νtrain N b hinit hout hin hκ hent hN hfin).1
  have hδ0 : 0 ≤ ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam :=
    integral_nonneg fun s => le_max_left _ _
  have h := pinsker_negative_control_density_rev lam F (κ := κ) hinit hout hin
  rw [rpow_half_div_two hne, ← ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := (negMass_ratio_le_min hδ0).trans (min_le_min le_rfl hδ1)
  have hs : Real.sqrt (1 / 2 * (klDiv κ (normalize (kappaHat F.policy F.outflow Finit))).toReal)
      ≤ 1 / Real.sqrt 2 * Real.sqrt (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_div zero_le_one, Real.sqrt_one]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKL1) (by positivity)
  linarith

end Loss

-- ported from GFNBounds.Core.SamplingGeneral.le_essSup_rnDeriv_smul
-- (lean/GFNBounds/Core/SamplingGeneralBounds.lean:632)
/-- `λ ≤ ‖dλ/dν_train‖_∞ ν_train` for `λ ≪ ν_train`. -/
theorem le_essSup_rnDeriv_smul {μ ν : Measure S} [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    μ ≤ essSup (μ.rnDeriv ν) ν • ν := by
  calc μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq μ ν h).symm
    _ ≤ ν.withDensity (fun _ => essSup (μ.rnDeriv ν) ν) := withDensity_mono ae_le_essSup
    _ = essSup (μ.rnDeriv ν) ν • ν := withDensity_const _

/-- **The loss bound at the paper's constant** `N = ‖dλ/dν_train‖_{L^∞(ν_train)}` (C-35:
`b ≥ 1 + ‖dλ/dν_train‖_∞`). -/
theorem loss_controls_sampling_essSup (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S)
    {Finit κ νtrain : Measure S} [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ]
    [SigmaFinite νtrain] {b : ℝ} (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ) (hνT : lam ≪ νtrain)
    (hM : essSup (lam.rnDeriv νtrain) νtrain ≠ ∞)
    (hb : 1 + (essSup (lam.rnDeriv νtrain) νtrain).toReal ≤ b)
    (hL : klwfmLoss lam νtrain b F Finit κ ≠ ⊤) :
    ((entropy lam κ : ℝ) : EReal) ≤ klwfmLoss lam νtrain b F Finit κ ∧
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal (1 / Real.sqrt 2
            * Real.sqrt (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ)
          + min 1 ((essSup (lam.rnDeriv νtrain) νtrain).toReal
              * (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ))) := by
  set M := essSup (lam.rnDeriv νtrain) νtrain with hMdef
  have hN : lam ≤ ((M.toNNReal : ℝ≥0) : ℝ≥0∞) • νtrain := by
    rw [ENNReal.coe_toNNReal hM]; exact le_essSup_rnDeriv_smul hνT
  have hb' : 1 + ((M.toNNReal : ℝ≥0) : ℝ) ≤ b := hb
  refine ⟨loss_ge_entropy lam F νtrain M.toNNReal b hinit hout hin hκ hent hN (by linarith),
    loss_controls_sampling lam F νtrain M.toNNReal b hinit hout hin hκ hent hN hb' hL⟩

/-! ### The printed loss is unbounded below; the floor needs `b` large -/

namespace SwapM

/-- The swap policy on `Bool` with star outflow `m δ_false`. -/
noncomputable def flow (m : ℝ≥0) : GenerativeFlow Bool where
  policy := Kernel.deterministic (fun b => !b) (measurable_of_countable _)
  outflow := m • Measure.dirac false
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

theorem inflow_apply (m : ℝ≥0) (b : Bool) :
    inflow (flow m).policy (flow m).outflow {b} = if b then (m : ℝ≥0∞) else 0 := by
  rw [inflow, Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
  cases b <;> simp [flow, Kernel.deterministic_apply]

theorem defect_true (m : ℝ≥0) :
    defectDensity Measure.count (flow m).policy (flow m).outflow (Measure.dirac true) true
      = 1 + m := by
  rw [defectDensity, dens_count_bool, dens_count_bool, dens_count_bool, inflow_apply]
  simp [flow]

theorem defect_false (m : ℝ≥0) :
    defectDensity Measure.count (flow m).policy (flow m).outflow (Measure.dirac true) false
      = -m := by
  rw [defectDensity, dens_count_bool, dens_count_bool, dens_count_bool, inflow_apply]
  simp [flow]

theorem ftermHat_true (m : ℝ≥0) :
    ftermHatDensity Measure.count (flow m).policy (flow m).outflow (Measure.dirac true) true
      = 1 + m := by
  rw [ftermHatDensity, defect_true]; exact max_eq_right (by positivity)

theorem lossFinite (m : ℝ≥0) :
    LossFinite Measure.count Measure.count (flow m) (Measure.dirac true) (Measure.dirac true) := by
  refine ⟨?_, Integrable.of_finite, Integrable.of_finite⟩
  rw [ae_dirac_iff (measurableSet_lt measurable_const (measurable_of_countable _)), ftermHat_true]
  positivity

/-- `δ = ∫ δf_init dλ = m`. -/
theorem delta_eq (m : ℝ≥0) :
    ∫ s, deltaFinitDensity Measure.count (flow m).policy (flow m).outflow (Measure.dirac true) s
      ∂Measure.count = m := by
  rw [integral_count, Fintype.sum_bool, deltaFinitDensity, deltaFinitDensity, defect_true,
    defect_false, neg_neg, max_eq_left (by linarith [m.coe_nonneg]), max_eq_right m.coe_nonneg,
    zero_add]

theorem entropy_eq : entropy Measure.count (Measure.dirac true) = 0 := by
  rw [entropy, integral_dirac, dens_count_bool]; simp

theorem loss_eq (m : ℝ≥0) (b : ℝ) :
    klwfmLoss Measure.count Measure.count b (flow m) (Measure.dirac true) (Measure.dirac true)
      = ((b * m - Real.log (1 + m) : ℝ) : EReal) := by
  rw [klwfmLoss_of_finite (lossFinite m), klwfmLossReal, delta_eq, integral_dirac, ftermHat_true]

theorem printed_loss_eq (m : ℝ≥0) (b : ℝ) :
    klwfmLossPrinted Measure.count Measure.count b (flow m) (Measure.dirac true)
        (Measure.dirac true)
      = ((-(b * m) - Real.log (1 + m) : ℝ) : EReal) := by
  have hfin := lossFinite m
  have hpen : Integrable (deltaFinitDensityPrinted Measure.count (flow m).policy (flow m).outflow
      (Measure.dirac true)) Measure.count := Integrable.of_finite
  rw [klwfmLossPrinted, if_pos ⟨hfin.pos, hfin.ce⟩, if_pos hpen, klwfmLossRealPrinted,
    integral_count, Fintype.sum_bool, deltaFinitDensityPrinted, deltaFinitDensityPrinted,
    defect_true, defect_false, min_eq_left (by linarith [m.coe_nonneg]),
    min_eq_right (by linarith [m.coe_nonneg]), integral_dirac, ftermHat_true]
  congr 1
  ring

/-- **The printed loss rewards the defect** (C-2): on `Bool` with the counting measure,
`ν_train = λ`, the swap policy, `F_out = m δ_false`, `F_init = κ = δ_true`, the printed Eq. (15) is
`−b m − log(1 + m)`, which tends to `−∞` as `m → ∞` for every `b ≥ 0`, while
`δ = ∫ δf_init dλ = m → ∞`: minimizing it drives the defect up. The corrected loss is
`b m − log(1 + m) ≥ H(κ) = 0` for `b ≥ 1 = N` (`loss_ge_entropy`). -/
theorem printed_loss_tendsto_bot {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => klwfmLossPrinted Measure.count Measure.count b (flow n)
      (Measure.dirac true) (Measure.dirac true)) atTop (𝓝 ⊥) ∧
    Tendsto (fun n : ℕ => ∫ s, deltaFinitDensity Measure.count (flow n).policy (flow n).outflow
      (Measure.dirac true) s ∂Measure.count) atTop atTop := by
  constructor
  · simp_rw [printed_loss_eq]
    rw [EReal.tendsto_coe_nhds_bot_iff]
    have hlog : Tendsto (fun n : ℕ => Real.log (1 + ((n : ℝ≥0) : ℝ))) atTop atTop := by
      refine Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ ?_)
      simp only [NNReal.coe_natCast]
      exact tendsto_natCast_atTop_atTop
    refine Filter.tendsto_atBot_mono (fun n => ?_) (tendsto_neg_atTop_atBot.comp hlog)
    have : 0 ≤ b * ((n : ℝ≥0) : ℝ) := mul_nonneg hb (NNReal.coe_nonneg _)
    simp only [Function.comp_apply]
    linarith
  · simp_rw [delta_eq, NNReal.coe_natCast]
    exact tendsto_natCast_atTop_atTop

/-- **The floor needs `b` large** (C-35): with `N = 1` (`ν_train = λ`) and any `b < log 2`, in
particular any `b ∈ (0, log 2)` the paper allows (`main.tex:366`), the corrected loss at `m = 1` is
`b − log 2 < 0 = H(κ)`. `loss_ge_entropy` gives `H(κ) ≤ L` for `b ≥ N`. -/
theorem loss_lt_entropy {b : ℝ} (hb : b < Real.log 2) :
    klwfmLoss Measure.count Measure.count b (flow 1) (Measure.dirac true) (Measure.dirac true)
      < ((entropy Measure.count (Measure.dirac true) : ℝ) : EReal) := by
  rw [loss_eq, entropy_eq, EReal.coe_lt_coe_iff]
  norm_num
  linarith

end SwapM

/-! ## 5. Algorithm 1's weights (`main.tex:396–404`) -/

/-- The backward factor of `main.tex:400`, `(1 + δf_init/f_in)⁻¹`, with the negative-part
`δf_init` (C-3). -/
noncomputable def algBackwardFactor (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    (s : S) : ℝ :=
  (1 + deltaFinitDensity lam F.policy F.outflow Finit s / dens lam (inflow F.policy F.outflow) s)⁻¹

/-- The backward factor of `main.tex:400` as printed, with `δf_init = min(0, ·)`. -/
noncomputable def algBackwardFactorPrinted (lam : Measure S) (F : GenerativeFlow S)
    (Finit : Measure S) (s : S) : ℝ :=
  (1 + deltaFinitDensityPrinted lam F.policy F.outflow Finit s
    / dens lam (inflow F.policy F.outflow) s)⁻¹

/-- The forward factor of `main.tex:399`, `(1 + f̂_term/f_out)⁻¹`. -/
noncomputable def algForwardFactor (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    (s : S) : ℝ :=
  (1 + ftermHatDensity lam F.policy F.outflow Finit s / dens lam F.outflow s)⁻¹

/-- **With the corrected sign, the backward factor is a probability** (C-3): `(1 + δf_init/f_in)⁻¹
∈ (0, 1]` wherever `f_in > 0`. -/
theorem algBackwardFactor_mem_Ioc (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    {s : S} (hs : 0 < dens lam (inflow F.policy F.outflow) s) :
    algBackwardFactor lam F Finit s ∈ Set.Ioc 0 1 := by
  have hx : 0 ≤ deltaFinitDensity lam F.policy F.outflow Finit s
      / dens lam (inflow F.policy F.outflow) s := div_nonneg (le_max_left _ _) hs.le
  refine ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩

/-- The forward factor is a probability wherever `f_out > 0`, and there it is
`f_out/(f̂_term + f_out)`. -/
theorem algForwardFactor_eq (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    {s : S} (hs : 0 < dens lam F.outflow s) :
    algForwardFactor lam F Finit s
        = dens lam F.outflow s / (ftermHatDensity lam F.policy F.outflow Finit s
          + dens lam F.outflow s) ∧
      algForwardFactor lam F Finit s ∈ Set.Ioc 0 1 := by
  have hf0 : 0 ≤ ftermHatDensity lam F.policy F.outflow Finit s := le_max_left _ _
  have he : algForwardFactor lam F Finit s
      = dens lam F.outflow s / (ftermHatDensity lam F.policy F.outflow Finit s
        + dens lam F.outflow s) := by
    unfold algForwardFactor
    field_simp
    ring
  refine ⟨he, ?_⟩
  rw [he]
  exact ⟨div_pos hs (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

/-- Where `f_in > 0`, the backward factor is `f_in/(δf_init + f_in)`. -/
theorem algBackwardFactor_eq (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    {s : S} (hs : 0 < dens lam (inflow F.policy F.outflow) s) :
    algBackwardFactor lam F Finit s
      = dens lam (inflow F.policy F.outflow) s
        / (deltaFinitDensity lam F.policy F.outflow Finit s
          + dens lam (inflow F.policy F.outflow) s) := by
  have hd0 : 0 ≤ deltaFinitDensity lam F.policy F.outflow Finit s := le_max_left _ _
  unfold algBackwardFactor
  field_simp
  ring

/-- **The backward factor of the sampler run backwards** (`reverse_cont_ae_eq`):
`(1 + (f_init + δf_init)/f_in)⁻¹`. -/
noncomputable def algBackwardFactorReversed (lam : Measure S) (F : GenerativeFlow S)
    (Finit : Measure S) (s : S) : ℝ :=
  (1 + (dens lam Finit s + deltaFinitDensity lam F.policy F.outflow Finit s)
    / dens lam (inflow F.policy F.outflow) s)⁻¹

/-- Where `f_in > 0`, the reversed factor is `f_in/(f_init + δf_init + f_in) ∈ (0, 1]`, and it is at
most the factor of `main.tex:400`, strictly where `f_init > 0` and with equality where `f_init = 0`:
under the reading that `B←` holds reversed-sampler paths (OQ-83), the printed weights overstate
the survival of a backward path wherever the source has density. -/
theorem algBackwardFactorReversed_eq (lam : Measure S) (F : GenerativeFlow S) (Finit : Measure S)
    {s : S} (hs : 0 < dens lam (inflow F.policy F.outflow) s) :
    algBackwardFactorReversed lam F Finit s
        = dens lam (inflow F.policy F.outflow) s
          / (dens lam Finit s + deltaFinitDensity lam F.policy F.outflow Finit s
            + dens lam (inflow F.policy F.outflow) s) ∧
      algBackwardFactorReversed lam F Finit s ∈ Set.Ioc 0 1 ∧
      algBackwardFactorReversed lam F Finit s ≤ algBackwardFactor lam F Finit s ∧
      (0 < dens lam Finit s →
        algBackwardFactorReversed lam F Finit s < algBackwardFactor lam F Finit s) ∧
      (dens lam Finit s = 0 →
        algBackwardFactorReversed lam F Finit s = algBackwardFactor lam F Finit s) := by
  have hd0 : 0 ≤ deltaFinitDensity lam F.policy F.outflow Finit s := le_max_left _ _
  have hi0 : 0 ≤ dens lam Finit s := ENNReal.toReal_nonneg
  have he : algBackwardFactorReversed lam F Finit s
      = dens lam (inflow F.policy F.outflow) s
        / (dens lam Finit s + deltaFinitDensity lam F.policy F.outflow Finit s
          + dens lam (inflow F.policy F.outflow) s) := by
    unfold algBackwardFactorReversed
    field_simp
    ring
  rw [he, algBackwardFactor_eq lam F Finit hs]
  refine ⟨rfl, ⟨div_pos hs (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩,
    div_le_div_of_nonneg_left hs.le (by linarith) (by linarith),
    fun hpos => div_lt_div_of_pos_left hs (by linarith) (by linarith), fun h0 => ?_⟩
  rw [h0, zero_add]

namespace Swap3

/-- The swap policy on `Bool` with star outflow `3 δ_false + δ_true`. -/
noncomputable def flow : GenerativeFlow Bool where
  policy := Kernel.deterministic (fun b => !b) (measurable_of_countable _)
  outflow := (3 : ℝ≥0) • Measure.dirac false + Measure.dirac true
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

/-- **Finding: with the printed sign the backward factor of `main.tex:400` is negative** (C-3). On
`Bool` with the counting measure, this flow and `F_init = δ_true`, at `s = false`:
`f_in = 1`, printed `δf_init = −2`, and `(1 + δf_init/f_in)⁻¹ = −1`; the corrected factor is `1/3`. -/
theorem printed_algBackwardFactor_neg :
    dens Measure.count (inflow flow.policy flow.outflow) false = 1 ∧
    deltaFinitDensityPrinted Measure.count flow.policy flow.outflow (Measure.dirac true) false
      = -2 ∧
    algBackwardFactorPrinted Measure.count flow (Measure.dirac true) false = -1 ∧
    algBackwardFactor Measure.count flow (Measure.dirac true) false = 1 / 3 := by
  have hin : inflow flow.policy flow.outflow {false} = 1 := by
    rw [inflow, Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
    simp [flow, Kernel.deterministic_apply, lintegral_add_measure]
  have hout : flow.outflow {false} = 3 := by simp [flow]
  have hd : dens Measure.count (inflow flow.policy flow.outflow) false = 1 := by
    rw [dens_count_bool, hin, ENNReal.toReal_one]
  have hdef : defectDensity Measure.count flow.policy flow.outflow (Measure.dirac true) false
      = -2 := by
    rw [defectDensity, dens_count_bool, dens_count_bool, dens_count_bool, hin, hout]
    simp
    norm_num
  have hP : deltaFinitDensityPrinted Measure.count flow.policy flow.outflow (Measure.dirac true)
      false = -2 := by
    rw [deltaFinitDensityPrinted, hdef]; norm_num
  have hC : deltaFinitDensity Measure.count flow.policy flow.outflow (Measure.dirac true)
      false = 2 := by
    rw [deltaFinitDensity, hdef]; norm_num
  refine ⟨hd, hP, ?_, ?_⟩
  · rw [algBackwardFactorPrinted, hP, hd]; norm_num
  · rw [algBackwardFactor, hC, hd]; norm_num

end Swap3

/-- The continuation probability of a sampler in densities: for `F_out = g λ` and `F_term = t λ`,
`cont = g/(t + g)`, `(F_term + F_out)`-a.e. -/
theorem cont_ae_eq_ratio (lam : Measure S) [SigmaFinite lam] (G : GenerativeFlow S)
    (Fterm : Measure S) [IsFiniteMeasure Fterm] {g t : S → ℝ} (hg : Measurable g)
    (ht : Measurable t) (hg0 : ∀ s, 0 ≤ g s) (ht0 : ∀ s, 0 ≤ t s)
    (hG : G.outflow = lam.withDensity fun s => ENNReal.ofReal (g s))
    (hT : Fterm = lam.withDensity fun s => ENNReal.ofReal (t s)) :
    G.cont Fterm =ᵐ[G.stopBase Fterm] fun s => ENNReal.ofReal (g s / (t s + g s)) := by
  have hgm : Measurable fun s => ENNReal.ofReal (g s) := ENNReal.measurable_ofReal.comp hg
  have htm : Measurable fun s => ENNReal.ofReal (t s) := ENNReal.measurable_ofReal.comp ht
  have hB : G.stopBase Fterm
      = lam.withDensity ((fun s => ENNReal.ofReal (t s)) + fun s => ENNReal.ofReal (g s)) := by
    rw [GenerativeFlow.stopBase, hT, hG, withDensity_add_left htm]
  have hBl : G.stopBase Fterm ≪ lam := by rw [hB]; exact withDensity_absolutelyContinuous _ _
  have hGl : G.outflow ≪ lam := by rw [hG]; exact withDensity_absolutelyContinuous _ _
  have e1 := G.cont_ae_eq Fterm
  have e2 := Measure.rnDeriv_eq_div hGl hBl
  have e3 : G.outflow.rnDeriv lam =ᵐ[lam] fun s => ENNReal.ofReal (g s) := by
    rw [hG]; exact Measure.rnDeriv_withDensity lam hgm
  have e4 : (G.stopBase Fterm).rnDeriv lam
      =ᵐ[lam] (fun s => ENNReal.ofReal (t s)) + fun s => ENNReal.ofReal (g s) := by
    rw [hB]; exact Measure.rnDeriv_withDensity lam (htm.add hgm)
  filter_upwards [e1, e2, hBl.ae_le e3, hBl.ae_le e4] with s h1 h2 h3 h4
  rw [h1, h2, h3, h4, Pi.add_apply]
  rcases eq_or_lt_of_le (add_nonneg (ht0 s) (hg0 s)) with h0 | hpos
  · have hg' : g s = 0 := by linarith [ht0 s, hg0 s]
    have ht' : t s = 0 := by linarith [ht0 s, hg0 s]
    simp [hg', ht']
  · rw [← ENNReal.ofReal_add (ht0 s) (hg0 s), ENNReal.ofReal_div_of_pos hpos]

/-- **The forward factor of `main.tex:399` is the sampler's continuation probability** (C-3):
for the sampler of `F` with `F_term = κ̂`, `cont = f_out/(f̂_term + f_out)` a.e., which is
`(1 + f̂_term/f_out)⁻¹` where `f_out > 0` (`algForwardFactor_eq`); the stopping law it drives is
`GenerativeFlow.pathLaw_hazard`. -/
theorem cont_kappaHat_ae_eq (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S)
    {Finit : Measure S} [IsProbabilityMeasure Finit] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F) :
    F.cont (kappaHat F.policy F.outflow Finit)
      =ᵐ[F.stopBase (kappaHat F.policy F.outflow Finit)] fun s =>
        ENNReal.ofReal (dens lam F.outflow s
          / (ftermHatDensity lam F.policy F.outflow Finit s + dens lam F.outflow s)) := by
  exact cont_ae_eq_ratio lam F (kappaHat F.policy F.outflow Finit) (measurable_dens lam _)
    (measurable_ftermHatDensity lam F.policy F.outflow Finit) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => le_max_left _ _) (eq_withDensity_dens hout)
    (kappaHat_eq_withDensity lam F Finit hinit hout hin)

/-- **The forward weight of `main.tex:399` is the continuation probability**, `(F_term + F_out)`-a.e.:
where `f_out > 0` the sampler continues with probability `(1 + f̂_term/f_out)⁻¹`, and where `f_out = 0`
(the paper's `f̂_term/f_out = +∞`) with probability `0`. -/
theorem cont_kappaHat_ae_eq_forwardFactor (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {Finit : Measure S} [IsProbabilityMeasure Finit] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) (hin : InflowAC lam F) :
    ∀ᵐ s ∂F.stopBase (kappaHat F.policy F.outflow Finit),
      (0 < dens lam F.outflow s →
        F.cont (kappaHat F.policy F.outflow Finit) s
          = ENNReal.ofReal (algForwardFactor lam F Finit s)) ∧
      (dens lam F.outflow s = 0 → F.cont (kappaHat F.policy F.outflow Finit) s = 0) := by
  filter_upwards [cont_kappaHat_ae_eq lam F hinit hout hin] with s hs
  refine ⟨fun hpos => by rw [hs, (algForwardFactor_eq lam F Finit hpos).1], fun h0 => ?_⟩
  rw [hs, h0, zero_div, ENNReal.ofReal_zero]

/-! ### The sampler run backwards -/

/-- **The reversed flow** `(B, F_in)` of `(π, F_out)`, for a Markov kernel `B`. -/
noncomputable def GenerativeFlow.reverse (F : GenerativeFlow S) (B : Kernel S S)
    [IsMarkovKernel B] : GenerativeFlow S where
  policy := B
  outflow := inflow F.policy F.outflow
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

/-- A backward policy pushes the inflow back onto the outflow: `F_in B = F_out`. -/
theorem IsBackwardPolicy.inflow_inflow {F : GenerativeFlow S} {B : Kernel S S}
    (hB : IsBackwardPolicy F.policy F.outflow B) :
    inflow B (inflow F.policy F.outflow) = F.outflow := by
  ext X hX
  have h := hB X Set.univ hX MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  rw [inflow, Measure.bind_apply hX B.aemeasurable, h]
  simp

/-- **The reversed sampler stops at the virtual source**: the reversed flow is flow matching from
`κ̂` to `F_term` iff `F_term = F_init + δF_init`, `δF_init = (F_init + F_in − F_out)⁻`. -/
theorem reverse_isFlowMatching_iff (F : GenerativeFlow S) {B : Kernel S S} [IsMarkovKernel B]
    (hB : IsBackwardPolicy F.policy F.outflow B) {Finit T : Measure S} [IsFiniteMeasure Finit]
    [IsFiniteMeasure T] :
    (F.reverse B).IsFlowMatching (kappaHat F.policy F.outflow Finit) T
      ↔ T = Finit + inferenceDefect F.policy F.outflow Finit := by
  have hV : Finit + inferenceDefect F.policy F.outflow Finit + inflow F.policy F.outflow
      = kappaHat F.policy F.outflow Finit + F.outflow := by
    have h := isFlowMatching_virtual F.policy F.outflow Finit (kappaHat F.policy F.outflow Finit)
    unfold IsFlowMatching virtualInit at h
    rw [virtualTerm_kappaHat, initialError_kappaHat] at h
    exact h
  have hrev : (F.reverse B).IsFlowMatching (kappaHat F.policy F.outflow Finit) T
      ↔ kappaHat F.policy F.outflow Finit + F.outflow = T + inflow F.policy F.outflow := by
    unfold GenerativeFlow.IsFlowMatching IsFlowMatching GenerativeFlow.reverse
    simp only
    rw [hB.inflow_inflow]
  rw [hrev, ← hV]
  constructor
  · intro h
    have h' : inflow F.policy F.outflow + (Finit + inferenceDefect F.policy F.outflow Finit)
        = inflow F.policy F.outflow + T := by
      rw [add_comm, h, add_comm]
    exact ((Measure.add_right_inj _ _ _).1 h').symm
  · intro h; rw [h]

/-- **The sampler of `main.tex:164` run backwards** from `κ̂` along a backward policy: it stops
almost surely, and `s_τ ∼ (F_init + δF_init)/(1 + δ)`. -/
theorem reverse_sampling (F : GenerativeFlow S) {B : Kernel S S} [IsMarkovKernel B]
    (hB : IsBackwardPolicy F.policy F.outflow B) {Finit : Measure S} [IsProbabilityMeasure Finit] :
    (F.reverse B).pathLaw (kappaHat F.policy F.outflow Finit)
        (Finit + inferenceDefect F.policy F.outflow Finit) {ω | stopTime ω = ⊤} = 0 ∧
    ((F.reverse B).pathLaw (kappaHat F.policy F.outflow Finit)
        (Finit + inferenceDefect F.policy F.outflow Finit)).map sampledState
      = normalize (Finit + inferenceDefect F.policy F.outflow Finit) := by
  have hV0 : Finit + inferenceDefect F.policy F.outflow Finit ≠ 0 := by
    intro h
    have h1 : Finit Set.univ ≤ (Finit + inferenceDefect F.policy F.outflow Finit) Set.univ := by
      rw [Measure.add_apply]; exact le_self_add
    rw [h, measure_univ] at h1
    simp at h1
  obtain ⟨-, -, htop, hlaw⟩ := sampling_theorem (F.reverse B)
    (Finit := kappaHat F.policy F.outflow Finit)
    (Fterm := Finit + inferenceDefect F.policy F.outflow Finit) hV0
    ((reverse_isFlowMatching_iff F hB).2 rfl)
  exact ⟨htop, hlaw⟩

/-- **The reversed sampler exists** on a standard Borel space (the paper's Polish spaces): with
Mathlib's posterior `π†F_out` as backward policy, it is flow matching from `κ̂` to
`F_init + δF_init`, stops almost surely and samples `(F_init + δF_init)/(1 + δ)`. -/
theorem reverse_sampling_posterior [StandardBorelSpace S] [Nonempty S] (F : GenerativeFlow S)
    {Finit : Measure S} [IsProbabilityMeasure Finit] :
    (F.reverse (F.policy†F.outflow)).IsFlowMatching (kappaHat F.policy F.outflow Finit)
        (Finit + inferenceDefect F.policy F.outflow Finit) ∧
    (F.reverse (F.policy†F.outflow)).pathLaw (kappaHat F.policy F.outflow Finit)
        (Finit + inferenceDefect F.policy F.outflow Finit) {ω | stopTime ω = ⊤} = 0 ∧
    ((F.reverse (F.policy†F.outflow)).pathLaw (kappaHat F.policy F.outflow Finit)
        (Finit + inferenceDefect F.policy F.outflow Finit)).map sampledState
      = normalize (Finit + inferenceDefect F.policy F.outflow Finit) :=
  ⟨(reverse_isFlowMatching_iff F (isBackwardPolicy_posterior _ _)).2 rfl,
    reverse_sampling F (isBackwardPolicy_posterior _ _)⟩

/-- **Finding: the backward factor of the reversed sampler** (`main.tex:400`, C-3). Its
continuation probability is `f_in/(f_init + δf_init + f_in) = (1 + (f_init + δf_init)/f_in)⁻¹`, not
the printed `(1 + δf_init/f_in)⁻¹`. -/
theorem reverse_cont_ae_eq (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S)
    {B : Kernel S S} [IsMarkovKernel B] {Finit : Measure S} [IsProbabilityMeasure Finit]
    (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam) (hin : InflowAC lam F) :
    (F.reverse B).cont (Finit + inferenceDefect F.policy F.outflow Finit)
      =ᵐ[(F.reverse B).stopBase (Finit + inferenceDefect F.policy F.outflow Finit)] fun s =>
        ENNReal.ofReal (dens lam (inflow F.policy F.outflow) s
          / (dens lam Finit s + deltaFinitDensity lam F.policy F.outflow Finit s
            + dens lam (inflow F.policy F.outflow) s)) := by
  have hT : Finit + inferenceDefect F.policy F.outflow Finit = lam.withDensity fun s =>
      ENNReal.ofReal (dens lam Finit s + deltaFinitDensity lam F.policy F.outflow Finit s) := by
    rw [congrArg₂ (· + ·) (eq_withDensity_dens hinit)
      (inferenceDefect_eq_withDensity lam F Finit hinit hout hin)]
    rw [← withDensity_add_left (f := fun s => ENNReal.ofReal (dens lam Finit s))
      (ENNReal.measurable_ofReal.comp (measurable_dens lam Finit))]
    refine withDensity_congr_ae (ae_of_all _ fun s => ?_)
    simp only [Pi.add_apply]
    exact (ENNReal.ofReal_add (ENNReal.toReal_nonneg (a := Finit.rnDeriv lam s))
      (le_max_left _ _)).symm
  exact cont_ae_eq_ratio lam (F.reverse B) _ (measurable_dens lam _)
    ((measurable_dens lam Finit).add (measurable_deltaFinitDensity lam F.policy F.outflow Finit))
    (fun _ => ENNReal.toReal_nonneg)
    (fun _ => add_nonneg ENNReal.toReal_nonneg (le_max_left _ _)) (eq_withDensity_dens hin) hT

/-- **The printed backward factor is the reversed sampler toward `δF_init` alone**, whose
continuation is `f_in/(δf_init + f_in)`; that sampler is not flow matching from `κ̂` (masses
`1 + δ` and `δ`). -/
theorem printed_reverse_not_isFlowMatching (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {B : Kernel S S} [IsMarkovKernel B] {Finit : Measure S}
    [IsProbabilityMeasure Finit] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    (F.reverse B).cont (inferenceDefect F.policy F.outflow Finit)
      =ᵐ[(F.reverse B).stopBase (inferenceDefect F.policy F.outflow Finit)] (fun s =>
        ENNReal.ofReal (dens lam (inflow F.policy F.outflow) s
          / (deltaFinitDensity lam F.policy F.outflow Finit s
            + dens lam (inflow F.policy F.outflow) s))) ∧
    ¬ (F.reverse B).IsFlowMatching (kappaHat F.policy F.outflow Finit)
        (inferenceDefect F.policy F.outflow Finit) := by
  refine ⟨cont_ae_eq_ratio lam (F.reverse B) _ (measurable_dens lam _)
    (measurable_deltaFinitDensity lam F.policy F.outflow Finit)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => le_max_left _ _) (eq_withDensity_dens hin)
    (inferenceDefect_eq_withDensity lam F Finit hinit hout hin), fun h => ?_⟩
  have hm := (F.reverse B).mass_eq _ _ h
  obtain ⟨-, -, hmass, -, -⟩ := sampling_error_control F (Finit := Finit) (κ := Finit)
  rw [hmass] at hm
  have hd : inferenceDefect F.policy F.outflow Finit Set.univ ≠ ∞ := measure_ne_top _ _
  have : (1 : ℝ≥0∞) = 0 := by
    have hm' : 1 + inferenceDefect F.policy F.outflow Finit Set.univ
        = 0 + inferenceDefect F.policy F.outflow Finit Set.univ := by rw [zero_add]; exact hm
    exact (ENNReal.add_left_inj hd).1 hm'
  exact one_ne_zero this

/-- **The two backward weights as continuation probabilities**, where `f_in > 0`: the reversed
sampler (toward `F_init + δF_init`, flow matching) continues with `(1 + (f_init + δf_init)/f_in)⁻¹`;
the printed weight `(1 + δf_init/f_in)⁻¹` of `main.tex:400` is the continuation of the reversed
flow toward `δF_init` alone, which is not flow matching. -/
theorem reverse_cont_ae_eq_backwardFactor (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {B : Kernel S S} [IsMarkovKernel B] {Finit : Measure S}
    [IsProbabilityMeasure Finit] (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam)
    (hin : InflowAC lam F) :
    (∀ᵐ s ∂(F.reverse B).stopBase (Finit + inferenceDefect F.policy F.outflow Finit),
      0 < dens lam (inflow F.policy F.outflow) s →
        (F.reverse B).cont (Finit + inferenceDefect F.policy F.outflow Finit) s
          = ENNReal.ofReal (algBackwardFactorReversed lam F Finit s)) ∧
    (∀ᵐ s ∂(F.reverse B).stopBase (inferenceDefect F.policy F.outflow Finit),
      0 < dens lam (inflow F.policy F.outflow) s →
        (F.reverse B).cont (inferenceDefect F.policy F.outflow Finit) s
          = ENNReal.ofReal (algBackwardFactor lam F Finit s)) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [reverse_cont_ae_eq lam F (B := B) hinit hout hin] with s hs hpos
    rw [hs, (algBackwardFactorReversed_eq lam F Finit hpos).1]
  · filter_upwards [(printed_reverse_not_isFlowMatching lam F (B := B) hinit hout hin).1]
      with s hs hpos
    rw [hs, algBackwardFactor_eq lam F Finit hpos]

/-! ## 6. For an EGF with nonsingular moves, no `InflowAC` -/

/-- **`cor:pinsker_negative_control` for an EGF policy with nonsingular moves** (C-6): the density
form of `EGF.pinsker_negative_control_density`, `InflowAC` discharged by `InflowAC.of_map_ac`;
replaces the Jacobian hypothesis of `EGF.pinsker_negative_control_isEGF`. -/
theorem pinsker_negative_control_nonsingular (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {p : ℕ} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ) := by
  exact pinsker_negative_control_density lam F hinit hout (InflowAC.of_map_ac lam F hπ hΦ hout)

/-- The same with `KL(κ ‖ κ̂/κ̂(𝒮))` (C-5, C-6). -/
theorem pinsker_negative_control_rev_nonsingular (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {p : ℕ} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv κ (normalize (kappaHat F.policy F.outflow Finit)) / 2) ^ (1 / 2 : ℝ) := by
  exact pinsker_negative_control_density_rev lam F hinit hout
    (InflowAC.of_map_ac lam F hπ hΦ hout)

/-- **`cor:pinsker_negative_control` for an EGF** (`EGF.IsEGF`, homeomorphic moves) with
nonsingular moves: no Jacobian, no density of `F_out` beyond `F_out ≪ λ`. -/
theorem pinsker_negative_control_isEGF_nonsingular [TopologicalSpace S] (lam : Measure S)
    [SigmaFinite lam] (F : GenerativeFlow S) {p : ℕ} {Φ : Fin p → S ≃ₜ S} {α : Fin p → S → ℝ}
    (hE : IsEGF F Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam) {Finit κ : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] (hinit : Finit ≪ lam)
    (hout : F.outflow ≪ lam) :
    tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
      ≤ ENNReal.ofReal ((∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam)
          / (1 + ∫ s, deltaFinitDensity lam F.policy F.outflow Finit s ∂lam))
        + (klDiv (normalize (kappaHat F.policy F.outflow Finit)) κ / 2) ^ (1 / 2 : ℝ) := by
  exact pinsker_negative_control_density lam F hinit hout (InflowAC.of_isEGF lam F hE hΦ hout)

/-- **The loss floor and the loss bound for an EGF policy with nonsingular moves** (C-2, C-6,
C-35): `loss_ge_entropy` and `loss_controls_sampling` with `InflowAC` discharged. -/
theorem loss_controls_sampling_nonsingular (lam : Measure S) [SigmaFinite lam]
    (F : GenerativeFlow S) {p : ℕ} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy Φ α) (hΦ : ∀ i, lam.map (Φ i) ≪ lam) {Finit κ νtrain : Measure S}
    [IsProbabilityMeasure Finit] [IsProbabilityMeasure κ] {N : ℝ≥0} {b : ℝ}
    (hinit : Finit ≪ lam) (hout : F.outflow ≪ lam) (hκ : κ ≪ lam)
    (hent : Integrable (fun s => Real.log (dens lam κ s)) κ)
    (hN : lam ≤ (N : ℝ≥0∞) • νtrain) (hb : 1 + (N : ℝ) ≤ b) :
    ((entropy lam κ : ℝ) : EReal) ≤ klwfmLoss lam νtrain b F Finit κ ∧
    (klwfmLoss lam νtrain b F Finit κ ≠ ⊤ →
      tvDist ((F.pathLaw Finit (kappaHat F.policy F.outflow Finit)).map sampledState) κ
        ≤ ENNReal.ofReal (1 / Real.sqrt 2
              * Real.sqrt (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ)
            + min 1 (N * (klwfmLossReal lam νtrain b F Finit κ - entropy lam κ)))) := by
  have hin := InflowAC.of_map_ac lam F hπ hΦ hout
  exact ⟨loss_ge_entropy lam F νtrain N b hinit hout hin hκ hent hN (by linarith),
    fun hL => loss_controls_sampling lam F νtrain N b hinit hout hin hκ hent hN hb hL⟩

end EGF
