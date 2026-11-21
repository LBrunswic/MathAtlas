import EGF.UniversalityErgodic
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# The spectral-gap remark of Definition 3.3: a spectrum away from `1` is not enough; a spectral radius below `1` is, for `λ` invariant

`def:summably_mixing` — `main.tex:262` (the remark that follows it, `main.tex:271–274`). Not marked
here: the label is marked in `EGF/Defs.lean` (`EGF.IsSummablyL2Mixing`). This file reads the remark
of `main.tex:273–274` in both senses of "spectral gap": it refutes the gloss (a spectrum away from
`1`), proves the spectral-radius form for `λ` invariant, and shows that an invariance hypothesis
cannot be dropped (correction C-30). It also proves the non-mixing of the two universal policies of
C-29, which refute `main.tex:697` and `:702` read as necessity claims. See SCOPE.

> The technical summably $L^2$-mixing property informally means that iterating the Markov kernel
> $\pi$ is averaging out functions fast enough to ensure that the sum of errors is finite. In
> contrast, ergodicity alone ensures the convergence of $\varphi \pi^n$ in the much weaker Cesaro
> sense. (`main.tex:271`)

> This property is in particular satisfied if the policy $\pi$ induces a Koopman operator
> $\phi \mapsto \frac{d (\phi\lambda)\pi}{d\lambda}$ on $L^2(\Statespace)$, which has a so-called
> {\it spectral gap} \cite{conze2013ergodicity}. Informally the spectrum of the Koopman operator
> is bounded away from 1 on the subspace $\{\phi~|~\int \phi d\lambda =0\}$.
> In this case, the convergence of iterates by $\pi$ is exponential. (`main.tex:273–274`)

> Although ergodicity is easily achievable with a number of generators independent from the
> dimension (for instance on tori, one randomly initialized non-trainable translation is
> sufficient to ensure ergodicity), the technical assumption of $L^2$-mixing summability needed
> for universality is more subtle. (`main.tex:697`)

> Second, the $L^2$-mixing summability property is essential to ensure universality.
> (`main.tex:702`)

## What is proved

| | |
|---|---|
| `transfer_succ_ae`, `transfer_add_ae`, `integral_transfer`, `memLp_transfer`, `eLpNorm_transfer_le` | under `λπ = λ` the transfer `T : φ ↦ d((φλ)π)/dλ` composes, keeps the mean, contracts `L²(λ)` |
| `mixingCoeff_self_add_le`, `mixingCoeff_self_le_one` | with `λ̂ = λ`: `γ_{m+n} ≤ γ_m γ_n`, `γₙ ≤ 1` (`γₙ = ‖Tⁿ‖²` on mean-zero functions) |
| `isSummablyL2Mixing_of_mixingCoeff_lt_one`, `isSummablyL2Mixing_of_pow_contraction` | **the corrected criterion** (C-30): `λπ = λ` and `‖Tᴺ‖ < 1` on mean-zero functions for one `N` ⇒ summably `L²`-mixing |
| `hasExponentialL2Decay_of_mixingCoeff_lt_one`, `tsum_mixingCoeff_self_ne_top_iff`, `hasExponentialL2Decay_iff` | it also gives `γₙ ≤ C ρⁿ`; with `λ̂ = λ` the three are equivalent |
| `HasTwoSidedSpectralGap`, `mixingCoeff_one_lt_one_of_reversible`, `isSummablyL2Mixing_of_reversible` | reversible `π`, spectrum on mean-zero functions in `[−1 + c, 1 − c]` ⇒ `γ₁ ≤ (1 − c)/(1 + c)` |
| `SpectralGapRemarkPrinted`, `SpectralGapRemarkExponentialPrinted`, `not_spectralGapRemarkPrinted`, `not_spectralGapRemarkExponentialPrinted` | `main.tex:273–274` in the gloss reading (one-sided gap), refuted |
| `SpectralRadiusCriterionWithoutInvariance`, `not_spectralRadiusCriterionWithoutInvariance`, `Sink.*` | an invariance hypothesis cannot be dropped: `π ≡ δ_true` on two points has `T` bounded, `γ₁ = 0`, no invariant `λ̂ ~ λ` |
| `Swap.transfer_eq_neg`, `Swap.transfer_eq_pow_smul`, `Swap.integral_transfer_mul_self`, `Swap.mixingCoeff_eq`, `Swap.not_isSummablyL2Mixing`, `Swap.not_hasTwoSidedSpectralGap`, `Swap.isEGF_flow` | the swap of two points, an EGF with `α = 1/p`: `φπ = −φ` on mean-zero `φ` (spectrum `{−1}`), `γₙ = λ̂(𝒮)` for every `n`, `λ̂` |
| `not_isSummablyL2Mixing_of_map_eq`, `not_isSummablyL2Mixing_addCircle` | no automorphism preserving a σ-finite `λ` with `H ≠ ∅` is summably `L²`-mixing: `γₙ = γ₀ > 0`; no translation of the circle is |
| `Swap.universal_not_summablyMixing`, `Swap.universalFamily_not_summablyMixing`, `universal_not_summablyMixing_addCircle`, `universalFamily_not_summablyMixing_addCircle` | C-29: universal policies, and ε-universal families, without summable mixing |
| `IsSummablyL2MixingHat`, `isSummablyL2MixingHat_of_bind_eq`, `Swap.not_isSummablyL2MixingHat_of_finite` | OQ-47's other reading, variant with `H` normalized in `L²(λ̂)`: vacuous only through the non-σ-finite `λ̂ = ∞ · λ`; the swap fails it for every finite `λ̂` |

## Hypothesis checklist

| paper (`main.tex:273–274`) | here |
|---|---|
| `π` induces a Koopman operator `φ ↦ d((φλ)π)/dλ` on `L²` | ✓ `transfer π lam 1`; ⚠ strengthened: `λπ = λ`, `λ` finite (sufficient, not necessary; then `T` contracts `L²(λ)` and `λ̂ = λ`); boundedness alone is not enough (`not_spectralRadiusCriterionWithoutInvariance`) |
| "spectral gap", "spectrum … bounded away from 1 on `{∫ φ dλ = 0}`" | one-sided: refuted (`HasOneSidedSpectralGap`, `HasNoAlmostInvariantVectors`, even for `π` reversible and ergodic); ⚠ strengthened to `∃ N, γ_N < 1` (spectral radius `< 1`), or for reversible `π` to `HasTwoSidedSpectralGap` |
| conclusion: summably `L²`-mixing | ✓ `IsSummablyL2Mixing π lam`, with `λ̂ = λ` |
| conclusion: "the convergence of iterates … is exponential" | ✓ `HasExponentialL2Decay`: `γₙ ≤ C ρⁿ`, `C < ∞`, `ρ < 1` |

## SCOPE (disclosed)

No `sorry`. `def:summably_mixing` is not marked here (it is marked in `EGF/Defs.lean`); the remark
`main.tex:273–274` follows the definition. Two readings of "spectral gap", sentence by sentence.
(a) The gloss, a spectrum on mean-zero functions away from the point `1`: sentence 1 of
`main.tex:273` is false, sentence 2 is the reading's definition, `main.tex:274` is false; the swap
(spectrum `{−1}`, `γₙ = 1`) refutes both. `SpectralGapRemarkPrinted` and
`SpectralGapRemarkExponentialPrinted` encode (a) in Rayleigh form (`⟨Tφ, φ⟩ ≤ (1 − c)‖φ‖²`) and as
"no almost invariant vectors", with reversibility, ergodicity and `λπ = λ`, so their refutations
cover each weaker form. (b) Spectral radius `< 1` on mean-zero functions, the operator sense of the
Markov-chain literature cited at `main.tex:702`: sentence 1 is false only for lack of invariance
(the Sink) and true with `λπ = λ` (`isSummablyL2Mixing_of_mixingCoeff_lt_one`); sentence 2 is
inaccurate (away from the unit circle; for a reversible `π`, from `1` and `−1`); `main.tex:274` is
true (`hasExponentialL2Decay_of_mixingCoeff_lt_one`). In (b) the swap's lesson moves to
`main.tex:818`, `:833` (C-28(a)). `conze2013ergodicity` was not consulted. `γ_N` is `‖Tᴺ‖²` by
definition; Gelfand's formula (not formalized) turns spectral radius `< 1` into `∃ N, ‖Tᴺ‖ < 1`.
`λπ = λ` is sufficient, not necessary (not formalized: a resampling kernel to a `λ̂ ~ λ`, `λ̂ ≠ λ`,
with bounded density is summably mixing). The criteria take `λ̂ = λ`, where both readings of OQ-47
agree; the swap's non-mixing holds for every `λ̂` in `EGF.Defs`' reading. `IsSummablyL2MixingHat`
is one variant of OQ-47's other reading (`H` normalized in `L²(λ̂)`): it is vacuous only through the
non-σ-finite `λ̂ = ∞ · λ`, so that reading must take `λ̂` σ-finite. On `Bool` every swap-invariant
`λ̂` is a multiple of `λ` (not formalized), so the swap fails every variant for finite `λ̂`. No port:
the `Markov.*` density action of `EGF/UniversalityErgodic.lean` is imported.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-! ## The transfer under an invariant `λ` -/

/-- `‖f‖₂² = ∫ f² dμ`, in `ℝ≥0∞`. -/
theorem eLpNorm_two_sq_eq_lintegral (μ : Measure S) (f : S → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ s, ENNReal.ofReal (f s ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (2 : ℝ≥0)) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [show ((2 : ℝ≥0) : ℝ≥0∞) = 2 from rfl] at h
  rw [h]
  congr 1; funext s
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The transfer depends on `φ` only through its `λ`-a.e. class, by equality of functions. -/
theorem transfer_congr_ae (π : Kernel S S) (lam : Measure S) (n : ℕ) {φ ψ : S → ℝ}
    (h : φ =ᵐ[lam] ψ) : transfer π lam n φ = transfer π lam n ψ := by
  have h1 : lam.withDensity (fun x => ENNReal.ofReal (φ x))
      = lam.withDensity (fun x => ENNReal.ofReal (ψ x)) :=
    withDensity_congr_ae (h.mono fun x hx => by simp only [hx])
  have h2 : lam.withDensity (fun x => ENNReal.ofReal (-φ x))
      = lam.withDensity (fun x => ENNReal.ofReal (-ψ x)) :=
    withDensity_congr_ae (h.mono fun x hx => by simp only [hx])
  funext s
  simp only [transfer, h1, h2]

/-- The one-step transfer is the density action `Markov.densityAction` of `EGF.UniversalityErgodic`. -/
theorem transfer_one_eq_densityAction (π : Kernel S S) (lam : Measure S) (φ : S → ℝ) :
    transfer π lam 1 φ = Markov.densityAction π lam φ := rfl

theorem measurable_transfer (π : Kernel S S) (lam : Measure S) (n : ℕ) (φ : S → ℝ) :
    Measurable (transfer π lam n φ) := by
  unfold transfer
  exact ((Measure.measurable_rnDeriv _ _).ennreal_toReal).sub
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal)

/-- `μ ≪ λ` and `λπ = λ` give `μπⁿ ≪ λ`. -/
theorem pushIter_absolutelyContinuous (π : Kernel S S) {lam μ : Measure S}
    (hinv : lam.bind π = lam) (h : μ ≪ lam) (n : ℕ) : pushIter π n μ ≪ lam := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [pushIter_succ]
      have h' := Markov.bind_absolutelyContinuous_bind π ih
      rwa [hinv] at h'

/-- The transfer of an integrable `φ` is integrable (no invariance needed). -/
theorem integrable_transfer (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S) (n : ℕ)
    {φ : S → ℝ} (hφ : Integrable φ lam) : Integrable (transfer π lam n φ) lam := by
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (φ x)) :=
    isFiniteMeasure_withDensity_ofReal hφ.2
  haveI : IsFiniteMeasure (lam.withDensity fun x => ENNReal.ofReal (-φ x)) :=
    isFiniteMeasure_withDensity_ofReal hφ.neg.2
  exact Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv

/-- **`φπⁿ⁺¹ = (φπⁿ)π`**, `λ`-a.e., under `λπ = λ`. -/
theorem transfer_succ_ae (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (n : ℕ) {φ : S → ℝ}
    (hφ : Integrable φ lam) :
    transfer π lam (n + 1) φ =ᵐ[lam] transfer π lam 1 (transfer π lam n φ) := by
  obtain ⟨μp, hμp⟩ : ∃ μ : Measure S, μ = lam.withDensity fun x => ENNReal.ofReal (φ x) :=
    ⟨_, rfl⟩
  obtain ⟨μm, hμm⟩ : ∃ μ : Measure S, μ = lam.withDensity fun x => ENNReal.ofReal (-φ x) :=
    ⟨_, rfl⟩
  haveI : IsFiniteMeasure μp := hμp ▸ isFiniteMeasure_withDensity_ofReal hφ.2
  haveI : IsFiniteMeasure μm := hμm ▸ isFiniteMeasure_withDensity_ofReal hφ.neg.2
  have hp : pushIter π n μp ≪ lam :=
    pushIter_absolutelyContinuous π hinv (hμp ▸ withDensity_absolutelyContinuous _ _) n
  have hm : pushIter π n μm ≪ lam :=
    pushIter_absolutelyContinuous π hinv (hμm ▸ withDensity_absolutelyContinuous _ _) n
  have ha : Integrable (fun s => ((pushIter π n μp).rnDeriv lam s).toReal) lam :=
    Measure.integrable_toReal_rnDeriv
  have hb : Integrable (fun s => ((pushIter π n μm).rnDeriv lam s).toReal) lam :=
    Measure.integrable_toReal_rnDeriv
  have htr : transfer π lam n φ = fun s => ((pushIter π n μp).rnDeriv lam s).toReal
      + -((pushIter π n μm).rnDeriv lam s).toReal := by
    funext s; simp only [transfer, ← hμp, ← hμm, sub_eq_add_neg]
  have hbn : Integrable (fun s => -((pushIter π n μm).rnDeriv lam s).toReal) lam := hb.neg
  have hadd : Markov.densityAction π lam (fun s => ((pushIter π n μp).rnDeriv lam s).toReal
        + -((pushIter π n μm).rnDeriv lam s).toReal)
      =ᵐ[lam] fun s => Markov.densityAction π lam
          (fun s => ((pushIter π n μp).rnDeriv lam s).toReal) s
        + Markov.densityAction π lam (fun s => -((pushIter π n μm).rnDeriv lam s).toReal) s :=
    Markov.densityAction_add π hinv ha hbn
  have hneg := Markov.densityAction_neg π lam (fun s => ((pushIter π n μm).rnDeriv lam s).toReal)
  have hA := Markov.densityAction_toReal_rnDeriv π lam (pushIter π n μp) hp
  have hB := Markov.densityAction_toReal_rnDeriv π lam (pushIter π n μm) hm
  rw [transfer_one_eq_densityAction, htr]
  filter_upwards [hadd, hA, hB] with s h1 h2 h3
  rw [h1, hneg]
  simp only
  rw [h2, h3]
  simp only [transfer, pushIter_succ, ← hμp, ← hμm]
  ring

/-- **`φπ^{m+n} = (φπⁿ)π^m`**, `λ`-a.e., under `λπ = λ`. -/
theorem transfer_add_ae (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (m n : ℕ) {φ : S → ℝ}
    (hφ : Integrable φ lam) :
    transfer π lam (m + n) φ =ᵐ[lam] transfer π lam m (transfer π lam n φ) := by
  induction m with
  | zero =>
      rw [Nat.zero_add]
      exact (transfer_zero_ae π lam (measurable_transfer π lam n φ).aemeasurable).symm
  | succ m ih =>
      have h1 : transfer π lam (m + 1 + n) φ
          =ᵐ[lam] transfer π lam 1 (transfer π lam (m + n) φ) := by
        rw [show m + 1 + n = (m + n) + 1 by ring]
        exact transfer_succ_ae π lam hinv (m + n) hφ
      have h2 : transfer π lam 1 (transfer π lam (m + n) φ)
          = transfer π lam 1 (transfer π lam m (transfer π lam n φ)) :=
        transfer_congr_ae π lam 1 ih
      have h3 := transfer_succ_ae π lam hinv m (integrable_transfer π lam n hφ)
      rw [h2] at h1
      exact h1.trans h3.symm

/-- Under `λπ = λ` the transfer preserves the mean: `∫ φπⁿ dλ = ∫ φ dλ`. -/
theorem integral_transfer (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (n : ℕ) {φ : S → ℝ}
    (hφ : Integrable φ lam) : ∫ s, transfer π lam n φ s ∂lam = ∫ s, φ s ∂lam := by
  induction n with
  | zero => exact integral_congr_ae (transfer_zero_ae π lam hφ.aemeasurable)
  | succ n ih =>
      rw [integral_congr_ae (transfer_succ_ae π lam hinv n hφ), transfer_one_eq_densityAction,
        Markov.integral_densityAction π hinv (integrable_transfer π lam n hφ), ih]

/-- Under `λπ = λ` the transfer maps `L²(λ)` to itself. -/
theorem memLp_transfer (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (n : ℕ) {φ : S → ℝ}
    (hφ : MemLp φ 2 lam) : MemLp (transfer π lam n φ) 2 lam := by
  induction n with
  | zero => exact hφ.ae_eq (transfer_zero_ae π lam hφ.1.aemeasurable).symm
  | succ n ih =>
      have h := (Markov.isBoundedDensityAction_two π hinv).memLp _ ih
      exact h.ae_eq (transfer_succ_ae π lam hinv n (hφ.integrable (by norm_num))).symm

/-- Under `λπ = λ` the transfer is a contraction of `L²(λ)`. -/
theorem eLpNorm_transfer_le (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (n : ℕ) {φ : S → ℝ}
    (hφ : MemLp φ 2 lam) : eLpNorm (transfer π lam n φ) 2 lam ≤ eLpNorm φ 2 lam := by
  induction n with
  | zero => exact (eLpNorm_congr_ae (transfer_zero_ae π lam hφ.1.aemeasurable)).le
  | succ n ih =>
      rw [eLpNorm_congr_ae (transfer_succ_ae π lam hinv n (hφ.integrable (by norm_num)))]
      have h := (Markov.isBoundedDensityAction_two π hinv).eLpNorm_le _
        (memLp_transfer π lam hinv n hφ)
      rw [ENNReal.ofReal_one, one_mul] at h
      exact h.trans ih

/-! ## The corrected criterion (C-30): `‖Tᴺ‖ < 1` on mean-zero functions -/

/-- With `λ̂ = λ` invariant, `γₙ ≤ 1`. -/
theorem mixingCoeff_self_le_one (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (n : ℕ) :
    mixingCoeff π lam lam n ≤ 1 := by
  refine iSup₂_le fun φ hφ => ?_
  obtain ⟨hφL, hφn, -⟩ := hφ
  rw [← eLpNorm_two_sq_eq_lintegral]
  calc eLpNorm (transfer π lam n φ) 2 lam ^ 2 ≤ eLpNorm φ 2 lam ^ 2 := by
        gcongr; exact eLpNorm_transfer_le π lam hinv n hφL
    _ = 1 := by rw [hφn, one_pow]

/-- **Submultiplicativity**: with `λ̂ = λ` invariant, `γ_{m+n} ≤ γ_m γ_n` (`γₙ` is the squared
norm of `Tⁿ` on the mean-zero subspace of `L²(λ)`). -/
theorem mixingCoeff_self_add_le (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (m n : ℕ) :
    mixingCoeff π lam lam (m + n) ≤ mixingCoeff π lam lam m * mixingCoeff π lam lam n := by
  refine iSup₂_le fun φ hφ => ?_
  obtain ⟨hφL, hφn, hφ0⟩ := hφ
  have hφi : Integrable φ lam := hφL.integrable (by norm_num)
  have hψm : Measurable (transfer π lam n φ) := measurable_transfer π lam n φ
  have hψL : MemLp (transfer π lam n φ) 2 lam := memLp_transfer π lam hinv n hφL
  have hψ0 : ∫ s, transfer π lam n φ s ∂lam = 0 := by rw [integral_transfer π lam hinv n hφi, hφ0]
  have hae := transfer_add_ae π lam hinv m n hφi
  calc ∫⁻ s, ENNReal.ofReal (transfer π lam (m + n) φ s ^ 2) ∂lam
      = ∫⁻ s, ENNReal.ofReal (transfer π lam m (transfer π lam n φ) s ^ 2) ∂lam :=
        lintegral_congr_ae (hae.mono fun s hs => by simp only [hs])
    _ ≤ mixingCoeff π lam lam m * eLpNorm (transfer π lam n φ) 2 lam ^ 2 :=
        lintegral_transfer_sq_le π lam lam Measure.AbsolutelyContinuous.rfl m hψm hψL hψ0
    _ ≤ mixingCoeff π lam lam m * mixingCoeff π lam lam n := by
        gcongr
        rw [eLpNorm_two_sq_eq_lintegral]
        exact le_iSup₂ (f := fun φ (_ : φ ∈ unitMeanZero lam) =>
          ∫⁻ s, ENNReal.ofReal (transfer π lam n φ s ^ 2) ∂lam) φ ⟨hφL, hφn, hφ0⟩

/-- `γ_{r + kN} ≤ γ_N^k`. -/
theorem mixingCoeff_self_add_mul_le (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (N r k : ℕ) :
    mixingCoeff π lam lam (r + k * N) ≤ mixingCoeff π lam lam N ^ k := by
  induction k with
  | zero =>
      simp only [zero_mul, add_zero, pow_zero]
      exact mixingCoeff_self_le_one π lam hinv r
  | succ k ih =>
      calc mixingCoeff π lam lam (r + (k + 1) * N) = mixingCoeff π lam lam (N + (r + k * N)) := by
            congr 1; ring
        _ ≤ mixingCoeff π lam lam N * mixingCoeff π lam lam (r + k * N) :=
            mixingCoeff_self_add_le π lam hinv N (r + k * N)
        _ ≤ mixingCoeff π lam lam N * mixingCoeff π lam lam N ^ k := by gcongr
        _ = mixingCoeff π lam lam N ^ (k + 1) := by rw [pow_succ']

/-- `γ₀ < 1` forces `H = ∅` in effect: every `γₙ` vanishes. -/
theorem mixingCoeff_self_eq_zero_of_zero_lt_one (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam)
    (h0 : mixingCoeff π lam lam 0 < 1) (n : ℕ) : mixingCoeff π lam lam n = 0 := by
  by_contra hne
  have hle := mixingCoeff_self_add_le π lam hinv n 0
  rw [add_zero] at hle
  have hfin : mixingCoeff π lam lam n ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (mixingCoeff_self_le_one π lam hinv n)
  have hlt : mixingCoeff π lam lam n * mixingCoeff π lam lam 0 < mixingCoeff π lam lam n := by
    calc mixingCoeff π lam lam n * mixingCoeff π lam lam 0 < mixingCoeff π lam lam n * 1 :=
          (ENNReal.mul_lt_mul_iff_right hne hfin).2 h0
      _ = mixingCoeff π lam lam n := mul_one _
  exact absurd hle (not_le.2 hlt)

/-- `γₙ ≤ γ_N^{⌊n/N⌋}`. -/
theorem mixingCoeff_self_le_pow_div (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) (N n : ℕ) :
    mixingCoeff π lam lam n ≤ mixingCoeff π lam lam N ^ (n / N) := by
  have h := mixingCoeff_self_add_mul_le π lam hinv N (n % N) (n / N)
  rwa [Nat.mod_add_div' n N] at h

/-- `γ_N < 1` for one `N` makes `(γₙ)` summable. -/
theorem tsum_mixingCoeff_self_ne_top_of_lt_one (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam) {N : ℕ}
    (hN : mixingCoeff π lam lam N < 1) : ∑' n, mixingCoeff π lam lam n ≠ ∞ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp [mixingCoeff_self_eq_zero_of_zero_lt_one π lam hinv hN]
  · haveI : NeZero N := ⟨hN0.ne'⟩
    have hre : ∑' n, mixingCoeff π lam lam N ^ (n / N)
        = ∑' p : ℕ × Fin N, mixingCoeff π lam lam N ^ p.1 := by
      rw [← (Nat.divModEquiv N).tsum_eq]
      rfl
    have hsum : ∑' p : ℕ × Fin N, mixingCoeff π lam lam N ^ p.1
        = N * ∑' a : ℕ, mixingCoeff π lam lam N ^ a := by
      rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
      congr 1; funext a
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine ne_top_of_le_ne_top ?_ ((ENNReal.tsum_le_tsum
      (mixingCoeff_self_le_pow_div π lam hinv N)).trans (le_of_eq (hre.trans hsum)))
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (tsum_geometric_lt_top.2 hN).ne

/-- **The corrected criterion** (C-30, `main.tex:273`): if `λπ = λ` and `‖Tᴺ‖ < 1` on the
mean-zero subspace of `L²(λ)` for one `N` (`γ_N < 1`; by Gelfand's formula, the spectral radius
of `T` there is `< 1`), then `π` is summably `L²`-mixing, with `λ̂ = λ`. -/
theorem isSummablyL2Mixing_of_mixingCoeff_lt_one (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam) {N : ℕ}
    (hN : mixingCoeff π lam lam N < 1) : IsSummablyL2Mixing π lam :=
  ⟨lam, hinv, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl,
    tsum_mixingCoeff_self_ne_top_of_lt_one π lam hinv hN⟩

/-- The criterion in the target's form: `∫ (φπᴺ)² dλ ≤ c < 1` for every `φ ∈ H`. -/
theorem isSummablyL2Mixing_of_pow_contraction (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam) {N : ℕ} {c : ℝ≥0∞}
    (hc : c < 1)
    (h : ∀ φ ∈ unitMeanZero lam, ∫⁻ s, ENNReal.ofReal (transfer π lam N φ s ^ 2) ∂lam ≤ c) :
    IsSummablyL2Mixing π lam :=
  isSummablyL2Mixing_of_mixingCoeff_lt_one π lam hinv (N := N) ((iSup₂_le h).trans_lt hc)

/-- **Exponential `L²` decay** of the iterates on mean-zero functions, with `λ̂ = λ`:
`∫ (φπⁿ)² dλ ≤ C ρⁿ` for every `φ ∈ H`, `C < ∞`, `ρ < 1` (`main.tex:274`). -/
def HasExponentialL2Decay (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ ρ : ℝ≥0∞, ρ < 1 ∧ ∀ n, mixingCoeff π lam lam n ≤ C * ρ ^ n

/-- `γ_N < 1` for one `N` gives exponential decay (`main.tex:274`, corrected). -/
theorem hasExponentialL2Decay_of_mixingCoeff_lt_one (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam) {N : ℕ}
    (hN : mixingCoeff π lam lam N < 1) : HasExponentialL2Decay π lam := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · refine ⟨1, ENNReal.one_ne_top, 0, zero_lt_one, fun n => ?_⟩
    rw [mixingCoeff_self_eq_zero_of_zero_lt_one π lam hinv hN n]
    exact zero_le
  · set c := mixingCoeff π lam lam N with hc
    set d : ℝ≥0∞ := max c 2⁻¹ with hd
    have hd1 : d < 1 := max_lt hN (ENNReal.inv_lt_one.2 (by norm_num))
    have hd0 : d ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) (le_max_right _ _)).ne'
    have hdtop : d ≠ ∞ := (hd1.trans ENNReal.one_lt_top).ne
    set ρ : ℝ≥0∞ := d ^ ((1 : ℝ) / N) with hρ
    have hρN : ρ ^ N = d := by
      rw [hρ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ (by exact_mod_cast hN0.ne'), ENNReal.rpow_one]
    have hρ1 : ρ < 1 := ENNReal.rpow_lt_one hd1 (by positivity)
    refine ⟨d⁻¹, ENNReal.inv_ne_top.2 hd0, ρ, hρ1, fun n => ?_⟩
    have h1 : mixingCoeff π lam lam n ≤ ρ ^ (N * (n / N)) := by
      calc mixingCoeff π lam lam n ≤ c ^ (n / N) := mixingCoeff_self_le_pow_div π lam hinv N n
        _ ≤ d ^ (n / N) := by gcongr; exact le_max_left _ _
        _ = ρ ^ (N * (n / N)) := by rw [pow_mul, hρN]
    have h2 : ρ ^ (N * (n / N)) * d ≤ ρ ^ n := by
      calc ρ ^ (N * (n / N)) * d = ρ ^ (N * (n / N)) * ρ ^ N := by rw [hρN]
        _ ≤ ρ ^ (N * (n / N)) * ρ ^ (n % N) := by
            exact mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hρ1.le (Nat.mod_lt n hN0).le)
        _ = ρ ^ n := by rw [← pow_add, Nat.div_add_mod]
    calc mixingCoeff π lam lam n ≤ ρ ^ (N * (n / N)) := h1
      _ = ρ ^ (N * (n / N)) * d * d⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, mul_one]
      _ ≤ ρ ^ n * d⁻¹ := by gcongr
      _ = d⁻¹ * ρ ^ n := mul_comm _ _

/-- With `λ̂ = λ` invariant, summability of `(γₙ)` is equivalent to `γ_N < 1` for one `N`:
the corrected criterion is also necessary. -/
theorem tsum_mixingCoeff_self_ne_top_iff (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) :
    ∑' n, mixingCoeff π lam lam n ≠ ∞ ↔ ∃ N, mixingCoeff π lam lam N < 1 := by
  constructor
  · intro h
    have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
    exact ⟨N, hN⟩
  · rintro ⟨N, hN⟩
    exact tsum_mixingCoeff_self_ne_top_of_lt_one π lam hinv hN

/-- With `λ̂ = λ` invariant, exponential decay is equivalent to `γ_N < 1` for one `N`. -/
theorem hasExponentialL2Decay_iff (π : Kernel S S) [IsMarkovKernel π] (lam : Measure S)
    [IsFiniteMeasure lam] (hinv : lam.bind π = lam) :
    HasExponentialL2Decay π lam ↔ ∃ N, mixingCoeff π lam lam N < 1 := by
  constructor
  · rintro ⟨C, hC, ρ, hρ, h⟩
    have ht : Tendsto (fun n => C * ρ ^ n) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 hρ)
        (Or.inr hC)
      simpa using this
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
    exact ⟨N, (h N).trans_lt hN⟩
  · rintro ⟨N, hN⟩
    exact hasExponentialL2Decay_of_mixingCoeff_lt_one π lam hinv hN

/-! ## Measure-preserving automorphisms are never summably mixing -/

/-- The image of a measure by a deterministic kernel is its push-forward. -/
theorem bind_deterministic_eq_map {f : S → S} (hf : Measurable f) (μ : Measure S) :
    μ.bind (Kernel.deterministic f hf) = μ.map f := by
  change μ.bind (fun x => Measure.dirac (f x)) = μ.map f
  exact Measure.bind_dirac_eq_map μ hf

/-- Normalizing a non-zero mean-zero `φ ∈ L²(λ)` puts it in `H`. -/
theorem smul_mem_unitMeanZero {lam : Measure S} {φ : S → ℝ} (hφ : MemLp φ 2 lam)
    (hφ0 : ∫ s, φ s ∂lam = 0) (hne : eLpNorm φ 2 lam ≠ 0) :
    (fun s => (eLpNorm φ 2 lam).toReal⁻¹ * φ s) ∈ unitMeanZero lam := by
  have hfin : eLpNorm φ 2 lam ≠ ∞ := hφ.2.ne
  set c := (eLpNorm φ 2 lam).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hne hfin
  have hcn : eLpNorm φ 2 lam = ENNReal.ofReal c := (ENNReal.ofReal_toReal hfin).symm
  refine ⟨hφ.const_mul c⁻¹, ?_, ?_⟩
  · have : (fun s => c⁻¹ * φ s) = c⁻¹ • φ := rfl
    rw [this, eLpNorm_const_smul, hcn, Real.enorm_eq_ofReal_abs,
      abs_of_pos (inv_pos.mpr hcpos), ← ENNReal.ofReal_mul (inv_pos.mpr hcpos).le,
      inv_mul_cancel₀ hcpos.ne', ENNReal.ofReal_one]
  · simp only [integral_const_mul, hφ0, mul_zero]

/-- `(fμ) ∘ e⁻¹ = (f ∘ e⁻¹)(μ ∘ e⁻¹)` for a measurable equivalence. -/
theorem map_withDensity_measurableEquiv (e : S ≃ᵐ S) (μ : Measure S) (f : S → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun s => f (e.symm s)) := by
  ext A hA
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA, MeasurableEquiv.restrict_map, MeasureTheory.lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

/-- `(fλ)πⁿ = (f ∘ e⁻ⁿ) λ` for the deterministic kernel of an `e` preserving `λ`. -/
theorem pushIter_deterministic_withDensity (e : S ≃ᵐ S) {lam : Measure S}
    (he : lam.map e = lam) (n : ℕ) (f : S → ℝ≥0∞) :
    pushIter (Kernel.deterministic e e.measurable) n (lam.withDensity f)
      = lam.withDensity (fun s => f (e.symm^[n] s)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pushIter_succ, ih, bind_deterministic_eq_map, map_withDensity_measurableEquiv, he]
      congr 1

/-- `φπⁿ = φ ∘ e⁻ⁿ`, `λ`-a.e., for the deterministic kernel of an `e` preserving `λ`. -/
theorem transfer_deterministic_ae (e : S ≃ᵐ S) {lam : Measure S} [SigmaFinite lam]
    (he : lam.map e = lam) (n : ℕ) {φ : S → ℝ} (hφ : Measurable φ) :
    transfer (Kernel.deterministic e e.measurable) lam n φ =ᵐ[lam] fun s => φ (e.symm^[n] s) := by
  have hit : Measurable (e.symm^[n]) := e.symm.measurable.iterate n
  have h1 : (lam.withDensity fun s => ENNReal.ofReal (φ (e.symm^[n] s))).rnDeriv lam
      =ᵐ[lam] fun s => ENNReal.ofReal (φ (e.symm^[n] s)) :=
    Measure.rnDeriv_withDensity lam (hφ.comp hit).ennreal_ofReal
  have h2 : (lam.withDensity fun s => ENNReal.ofReal (-φ (e.symm^[n] s))).rnDeriv lam
      =ᵐ[lam] fun s => ENNReal.ofReal (-φ (e.symm^[n] s)) :=
    Measure.rnDeriv_withDensity lam (hφ.comp hit).neg.ennreal_ofReal
  filter_upwards [h1, h2] with s hs1 hs2
  simp only [transfer, pushIter_deterministic_withDensity e he]
  rw [hs1, hs2, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 (φ (e.symm^[n] s)) with h | h
  · simp [h]
  · simp [h]

/-- For an automorphism `e` preserving `λ` and `λ̂ ≪ λ`, `∫ (φπⁿ)² dλ̂` does not depend on `n`. -/
theorem lintegral_transfer_sq_deterministic (e : S ≃ᵐ S) {lam lamHat : Measure S}
    [SigmaFinite lam] (he : lam.map e = lam) (heHat : lamHat.map e = lamHat) (hac : lamHat ≪ lam)
    (n : ℕ) {φ : S → ℝ} (hφ : AEMeasurable φ lam) :
    ∫⁻ s, ENNReal.ofReal (transfer (Kernel.deterministic e e.measurable) lam n φ s ^ 2) ∂lamHat
      = ∫⁻ s, ENNReal.ofReal (transfer (Kernel.deterministic e e.measurable) lam 0 φ s ^ 2)
          ∂lamHat := by
  have hψm : Measurable (hφ.mk φ) := hφ.measurable_mk
  rw [transfer_congr_ae _ lam n hφ.ae_eq_mk, transfer_congr_ae _ lam 0 hφ.ae_eq_mk]
  have hn : transfer (Kernel.deterministic e e.measurable) lam n (hφ.mk φ)
      =ᵐ[lamHat] fun s => hφ.mk φ (e.symm^[n] s) :=
    hac.ae_le (transfer_deterministic_ae e he n hψm)
  have h0 : transfer (Kernel.deterministic e e.measurable) lam 0 (hφ.mk φ)
      =ᵐ[lamHat] fun s => hφ.mk φ (e.symm^[0] s) :=
    hac.ae_le (transfer_deterministic_ae e he 0 hψm)
  have hmp : MeasurePreserving e.symm lamHat lamHat :=
    ⟨e.symm.measurable, by
      calc lamHat.map e.symm = (lamHat.map e).map e.symm := by rw [heHat]
        _ = lamHat := MeasurableEquiv.map_symm_map e⟩
  calc ∫⁻ s, ENNReal.ofReal (transfer (Kernel.deterministic e e.measurable) lam n (hφ.mk φ) s ^ 2)
          ∂lamHat
      = ∫⁻ s, ENNReal.ofReal (hφ.mk φ (e.symm^[n] s) ^ 2) ∂lamHat :=
        lintegral_congr_ae (hn.mono fun s hs => by simp only [hs])
    _ = ∫⁻ s, ENNReal.ofReal (hφ.mk φ s ^ 2) ∂lamHat :=
        (hmp.iterate n).lintegral_comp (f := fun s => ENNReal.ofReal (hφ.mk φ s ^ 2))
          ((hψm.pow_const 2).ennreal_ofReal)
    _ = ∫⁻ s, ENNReal.ofReal (transfer (Kernel.deterministic e e.measurable) lam 0 (hφ.mk φ) s ^ 2)
          ∂lamHat :=
        lintegral_congr_ae (h0.mono fun s hs => by simp only [hs, Function.iterate_zero, id])

/-- For an automorphism `e` preserving `λ` and `λ̂`, `λ̂ ≪ λ`: `γₙ = γ₀` for every `n`. -/
theorem mixingCoeff_deterministic (e : S ≃ᵐ S) {lam lamHat : Measure S} [SigmaFinite lam]
    (he : lam.map e = lam) (heHat : lamHat.map e = lamHat) (hac : lamHat ≪ lam) (n : ℕ) :
    mixingCoeff (Kernel.deterministic e e.measurable) lam lamHat n
      = mixingCoeff (Kernel.deterministic e e.measurable) lam lamHat 0 := by
  unfold mixingCoeff
  exact iSup_congr fun φ => iSup_congr fun hφ =>
    lintegral_transfer_sq_deterministic e he heHat hac n hφ.1.aemeasurable

/-- `γ₀ > 0` as soon as `H` is non-empty and `λ̂ ~ λ`. -/
theorem mixingCoeff_zero_ne_zero (π : Kernel S S) {lam lamHat : Measure S} [SigmaFinite lam]
    (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat) (hH : (unitMeanZero lam).Nonempty) :
    mixingCoeff π lam lamHat 0 ≠ 0 := by
  obtain ⟨φ, hφ⟩ := hH
  intro h0
  have hle : ∫⁻ s, ENNReal.ofReal (transfer π lam 0 φ s ^ 2) ∂lamHat ≤ mixingCoeff π lam lamHat 0 :=
    le_iSup₂ (f := fun φ (_ : φ ∈ unitMeanZero lam) =>
      ∫⁻ s, ENNReal.ofReal (transfer π lam 0 φ s ^ 2) ∂lamHat) φ hφ
  rw [h0, nonpos_iff_eq_zero] at hle
  have hae : transfer π lam 0 φ =ᵐ[lamHat] φ :=
    hac.ae_le (transfer_zero_ae π lam hφ.1.aemeasurable)
  have hcongr : ∫⁻ s, ENNReal.ofReal (transfer π lam 0 φ s ^ 2) ∂lamHat
      = ∫⁻ s, ENNReal.ofReal (φ s ^ 2) ∂lamHat :=
    lintegral_congr_ae (hae.mono fun s hs => by simp only [hs])
  rw [hcongr] at hle
  have hmeas : AEMeasurable (fun s => ENNReal.ofReal (φ s ^ 2)) lamHat :=
    ((hφ.1.aemeasurable.pow_const 2).ennreal_ofReal).mono_ac hac
  rw [lintegral_eq_zero_iff' hmeas] at hle
  have hle' : (fun s => ENNReal.ofReal (φ s ^ 2)) =ᵐ[lam] 0 := hac'.ae_le hle
  have hφ0 : φ =ᵐ[lam] 0 := hle'.mono fun s hs => by
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hs
    exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hs (sq_nonneg _))
  have h := hφ.2.1
  rw [eLpNorm_congr_ae hφ0] at h
  simp at h

/-- `H` is non-empty as soon as some measurable set and its complement have positive measure. -/
theorem unitMeanZero_nonempty {lam : Measure S} [IsFiniteMeasure lam] {A : Set S}
    (hA : MeasurableSet A) (h0 : lam A ≠ 0) (h1 : lam Aᶜ ≠ 0) : (unitMeanZero lam).Nonempty := by
  classical
  set c₁ := (lam Aᶜ).toReal with hc₁
  set c₂ := (lam A).toReal with hc₂
  have hc₁p : 0 < c₁ := ENNReal.toReal_pos h1 (measure_ne_top _ _)
  have hc₂p : 0 < c₂ := ENNReal.toReal_pos h0 (measure_ne_top _ _)
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
  have hne : eLpNorm φ 2 lam ≠ 0 := by
    intro h
    have hz : φ =ᵐ[lam] 0 := (eLpNorm_eq_zero_iff hφL.1 (by norm_num)).mp h
    refine h0 (measure_mono_null (fun s hs => ?_) (ae_iff.1 hz))
    simp only [Set.mem_setOf_eq, Pi.zero_apply, hφ, Set.piecewise_eq_of_mem _ _ _ hs]
    exact hc₁p.ne'
  exact ⟨_, smul_mem_unitMeanZero hφL hφ0 hne⟩

/-- **No automorphism preserving a σ-finite `λ` is summably `L²`-mixing, as soon as `H ≠ ∅`**
(without it the claim fails: for a Dirac `λ`, `H = ∅` and every `γₙ` is `0`): for every invariant
`λ̂ ~ λ`, `γₙ = γ₀ > 0` for every `n` (the transfer is unitary). -/
theorem not_isSummablyL2Mixing_of_map_eq (e : S ≃ᵐ S) {lam : Measure S} [SigmaFinite lam]
    (he : lam.map e = lam) (hH : (unitMeanZero lam).Nonempty) :
    ¬ IsSummablyL2Mixing (Kernel.deterministic e e.measurable) lam := by
  rintro ⟨lamHat, hinv, hac, hac', hsum⟩
  have heHat : lamHat.map e = lamHat := by rw [← bind_deterministic_eq_map]; exact hinv
  have hconst : ∑' n, mixingCoeff (Kernel.deterministic e e.measurable) lam lamHat n
      = ∑' _ : ℕ, mixingCoeff (Kernel.deterministic e e.measurable) lam lamHat 0 :=
    tsum_congr fun n => mixingCoeff_deterministic e he heHat hac n
  rw [hconst] at hsum
  exact hsum (ENNReal.tsum_const_eq_top_of_ne_zero (mixingCoeff_zero_ne_zero _ hac hac' hH))

/-- **No translation of the circle is summably `L²`-mixing**, whatever its order. -/
theorem not_isSummablyL2Mixing_addCircle {T : ℝ} [Fact (0 < T)] (a : AddCircle T) :
    ¬ IsSummablyL2Mixing (Kernel.deterministic (a + ·) (measurable_const_add a))
      (volume : Measure (AddCircle T)) := by
  have hk : Kernel.deterministic (a + ·) (measurable_const_add a)
      = Kernel.deterministic (MeasurableEquiv.addLeft a) (MeasurableEquiv.addLeft a).measurable :=
    rfl
  rw [hk]
  refine not_isSummablyL2Mixing_of_map_eq _ (measurePreserving_add_left volume a).map_eq ?_
  have hT : 0 < T := Fact.out
  have hA : MeasurableSet (Metric.closedBall (0 : AddCircle T) (T / 4)) :=
    Metric.isClosed_closedBall.measurableSet
  have hvol : volume (Metric.closedBall (0 : AddCircle T) (T / 4)) = ENNReal.ofReal (T / 2) := by
    rw [AddCircle.volume_closedBall, min_eq_right (by linarith)]
    congr 1; ring
  refine unitMeanZero_nonempty hA ?_ ?_
  · rw [hvol]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · rw [measure_compl hA (measure_ne_top _ _), AddCircle.measure_univ, hvol]
    intro h
    rw [tsub_eq_zero_iff_le, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h
    linarith

/-- **C-29, the circle** (`main.tex:697`): a translation of infinite order of the circle — the
sentence's own "one randomly initialized non-trainable translation" — is a universal policy and
is not summably `L²`-mixing. -/
theorem universal_not_summablyMixing_addCircle {T : ℝ} [Fact (0 < T)] {a : AddCircle T}
    (ha : addOrderOf a = 0) :
    IsUniversalPolicy (volume : Measure (AddCircle T))
        (Kernel.deterministic (a + ·) (measurable_const_add a)) ∧
      ¬ IsSummablyL2Mixing (Kernel.deterministic (a + ·) (measurable_const_add a))
        (volume : Measure (AddCircle T)) :=
  ⟨isUniversalPolicy_addCircle ha, not_isSummablyL2Mixing_addCircle a⟩

/-- **C-29 at the family level, the circle** (`main.tex:697`, `:702`): the fixed-policy family
`{π} × L²₊(λ)` of a translation of infinite order is ε-universal (`def:universal_family` in its
corrected form of record, `EGF.IsUniversalFamilyEps`) and contains no summably `L²`-mixing policy. -/
theorem universalFamily_not_summablyMixing_addCircle {T : ℝ} [Fact (0 < T)] {a : AddCircle T}
    (ha : addOrderOf a = 0) :
    IsUniversalFamilyEps (volume : Measure (AddCircle T))
        (fixedPolicyFamily volume (Kernel.deterministic (a + ·) (measurable_const_add a))) ∧
      ∀ F ∈ fixedPolicyFamily volume (Kernel.deterministic (a + ·) (measurable_const_add a)),
        ¬ IsSummablyL2Mixing F.policy (volume : Measure (AddCircle T)) := by
  have herg : Ergodic (a + ·) (volume : Measure (AddCircle T)) :=
    (AddCircle.ergodic_add_left (a := a)).mpr ha
  obtain ⟨hinv, hke⟩ := isKernelErgodic_deterministic (measurable_const_add a) herg
  refine ⟨(isUniversalFamilyEps_fixedPolicyFamily_iff volume _ volume hinv
    Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl).2 hke, ?_⟩
  rintro F ⟨hF, -⟩
  rw [hF]
  exact not_isSummablyL2Mixing_addCircle a

/-! ## The remark as printed: a one-sided spectral gap -/

/-- **Reversibility**: the Koopman operator `T = transfer π λ 1` is self-adjoint on `L²(λ)`. -/
def IsReversibleL2 (π : Kernel S S) (lam : Measure S) : Prop :=
  ∀ φ ψ : S → ℝ, MemLp φ 2 lam → MemLp ψ 2 lam →
    ∫ s, transfer π lam 1 φ s * ψ s ∂lam = ∫ s, φ s * transfer π lam 1 ψ s ∂lam

/-- **"The spectrum of the Koopman operator is bounded away from 1 on `{∫ φ dλ = 0}`"**
(`main.tex:273`), one-sided, in Rayleigh form: `⟨Tφ, φ⟩ ≤ (1 − c)‖φ‖²` on mean-zero `φ`. For a
reversible `π` this is exactly `sup σ(T|_{H₀}) ≤ 1 − c`. -/
def HasOneSidedSpectralGap (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ φ : S → ℝ, MemLp φ 2 lam → ∫ s, φ s ∂lam = 0 →
    ∫ s, transfer π lam 1 φ s * φ s ∂lam ≤ (1 - c) * ∫ s, φ s ^ 2 ∂lam

/-- **No almost invariant vectors** (the spectral gap of a group action in the sense of
`bekka2015spectral`, here for the kernel): `‖Tφ − φ‖² ≥ c‖φ‖²` on mean-zero `φ`, i.e. `T − I`
bounded below there. -/
def HasNoAlmostInvariantVectors (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ φ : S → ℝ, MemLp φ 2 lam → ∫ s, φ s ∂lam = 0 →
    c * ∫ s, φ s ^ 2 ∂lam ≤ ∫ s, (transfer π lam 1 φ s - φ s) ^ 2 ∂lam

/-- **The remark of `main.tex:273` in the gloss reading (a)** (a spectrum away from the point `1`),
on every space and with every hypothesis the swap satisfies: a Markov kernel on a probability space, leaving `λ`
invariant, ergodic, reversible, whose Koopman operator has a one-sided spectral gap on mean-zero
functions in both forms, is summably `L²`-mixing. False: `not_spectralGapRemarkPrinted`. -/
def SpectralGapRemarkPrinted : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (lam : Measure X) (π : Kernel X X), IsProbabilityMeasure lam →
    IsMarkovKernel π → lam.bind π = lam → IsKernelErgodic π lam → IsReversibleL2 π lam →
    HasOneSidedSpectralGap π lam → HasNoAlmostInvariantVectors π lam → IsSummablyL2Mixing π lam

/-- **`main.tex:274` in the gloss reading (a)**: "in this case, the convergence of iterates by `π` is
exponential", under the hypotheses of `SpectralGapRemarkPrinted`. False:
`not_spectralGapRemarkExponentialPrinted`. In the spectral-radius reading (b) it is true for `λ`
invariant (`hasExponentialL2Decay_of_mixingCoeff_lt_one`). -/
def SpectralGapRemarkExponentialPrinted : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (lam : Measure X) (π : Kernel X X), IsProbabilityMeasure lam →
    IsMarkovKernel π → lam.bind π = lam → IsKernelErgodic π lam → IsReversibleL2 π lam →
    HasOneSidedSpectralGap π lam → HasNoAlmostInvariantVectors π lam → HasExponentialL2Decay π lam

/-! ## The corrected remark for a reversible policy: a two-sided gap -/

/-- **A two-sided spectral gap** on mean-zero functions, in Rayleigh form:
`|⟨Tφ, φ⟩| ≤ (1 − c)‖φ‖²`. For a reversible `π` this is "the spectrum of `T` on mean-zero
functions lies in `[−1 + c, 1 − c]`" (C-30's corrected text). -/
def HasTwoSidedSpectralGap (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ φ : S → ℝ, MemLp φ 2 lam → ∫ s, φ s ∂lam = 0 →
    |∫ s, transfer π lam 1 φ s * φ s ∂lam| ≤ (1 - c) * ∫ s, φ s ^ 2 ∂lam

/-- `L²` times `L²` is integrable. -/
theorem integrable_mul_of_memLp_two {μ : Measure S} {f g : S → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : Integrable (fun s => f s * g s) μ :=
  hf.integrable_mul hg

/-- **For a reversible `π` with a two-sided gap, `γ₁ < 1`**: with `λ̂ = λ` invariant and
`|⟨Tφ, φ⟩| ≤ (1 − c)‖φ‖²` on mean-zero `φ`, `‖Tφ‖² ≤ (1 − c)/(1 + c) ‖φ‖²` there (polarization:
`4⟨Tx, Tx⟩ = ⟨T(x + Tx), x + Tx⟩ − ⟨T(x − Tx), x − Tx⟩`). -/
theorem mixingCoeff_one_lt_one_of_reversible (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam)
    (hrev : IsReversibleL2 π lam) (hgap : HasTwoSidedSpectralGap π lam) :
    mixingCoeff π lam lam 1 < 1 := by
  obtain ⟨c, hc, hg⟩ := hgap
  have hk : (1 - c) / (1 + c) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine lt_of_le_of_lt (iSup₂_le fun φ hφ => ?_) (ENNReal.ofReal_lt_one.2 (max_lt hk one_pos))
  obtain ⟨hxL, hxn, hx0⟩ := hφ
  have hxi : Integrable φ lam := hxL.integrable (by norm_num)
  set y := transfer π lam 1 φ with hy
  have hyL : MemLp y 2 lam := memLp_transfer π lam hinv 1 hxL
  have hyi : Integrable y lam := hyL.integrable (by norm_num)
  have hy0 : ∫ s, y s ∂lam = 0 := by rw [hy, integral_transfer π lam hinv 1 hxi, hx0]
  set v := transfer π lam 1 y with hv
  have hvL : MemLp v 2 lam := memLp_transfer π lam hinv 1 hyL
  -- `T(x ± y) = Tx ± Ty`
  have hadd : transfer π lam 1 (fun s => φ s + y s) =ᵐ[lam] fun s => y s + v s :=
    Markov.densityAction_add π hinv hxi hyi
  have hsub : transfer π lam 1 (fun s => φ s - y s) =ᵐ[lam] fun s => y s - v s := by
    have e : (fun s => φ s - y s) = fun s => φ s + -y s := by funext s; ring
    have h1 : Markov.densityAction π lam (fun s => φ s + -y s)
        =ᵐ[lam] fun s => Markov.densityAction π lam φ s
          + Markov.densityAction π lam (fun s => -y s) s :=
      Markov.densityAction_add π hinv hxi hyi.neg
    rw [e, transfer_one_eq_densityAction]
    filter_upwards [h1] with s hs
    rw [hs, Markov.densityAction_neg]
    rfl
  -- the integrals
  have hyx := integrable_mul_of_memLp_two hyL hxL
  have hyy := integrable_mul_of_memLp_two hyL hyL
  have hvx := integrable_mul_of_memLp_two hvL hxL
  have hvy := integrable_mul_of_memLp_two hvL hyL
  have hP : ∫ s, transfer π lam 1 (fun s => φ s + y s) s * (φ s + y s) ∂lam
      = ∫ s, y s * φ s ∂lam + ∫ s, y s * y s ∂lam + (∫ s, v s * φ s ∂lam + ∫ s, v s * y s ∂lam) := by
    have e : (fun s => transfer π lam 1 (fun s => φ s + y s) s * (φ s + y s))
        =ᵐ[lam] fun s => (y s * φ s + y s * y s) + (v s * φ s + v s * y s) :=
      hadd.mono fun s hs => by beta_reduce at hs ⊢; rw [hs]; ring
    have i1 : Integrable (fun s => y s * φ s + y s * y s) lam := hyx.add hyy
    have i2 : Integrable (fun s => v s * φ s + v s * y s) lam := hvx.add hvy
    rw [integral_congr_ae e, integral_add i1 i2, integral_add hyx hyy, integral_add hvx hvy]
  have hQ : ∫ s, transfer π lam 1 (fun s => φ s - y s) s * (φ s - y s) ∂lam
      = ∫ s, y s * φ s ∂lam - ∫ s, y s * y s ∂lam - (∫ s, v s * φ s ∂lam - ∫ s, v s * y s ∂lam) := by
    have e : (fun s => transfer π lam 1 (fun s => φ s - y s) s * (φ s - y s))
        =ᵐ[lam] fun s => (y s * φ s - y s * y s) - (v s * φ s - v s * y s) :=
      hsub.mono fun s hs => by beta_reduce at hs ⊢; rw [hs]; ring
    have i1 : Integrable (fun s => y s * φ s - y s * y s) lam := hyx.sub hyy
    have i2 : Integrable (fun s => v s * φ s - v s * y s) lam := hvx.sub hvy
    rw [integral_congr_ae e, integral_sub i1 i2, integral_sub hyx hyy, integral_sub hvx hvy]
  -- reversibility: `⟨Ty, x⟩ = ⟨y, Tx⟩ = ⟨y, y⟩`
  have hrev' : ∫ s, v s * φ s ∂lam = ∫ s, y s * y s ∂lam := hrev y φ hyL hxL
  -- the gap at `x ± y`
  have hpL : MemLp (fun s => φ s + y s) 2 lam := hxL.add hyL
  have hmL : MemLp (fun s => φ s - y s) 2 lam := hxL.sub hyL
  have hp0 : ∫ s, (φ s + y s) ∂lam = 0 := by rw [integral_add hxi hyi, hx0, hy0, add_zero]
  have hm0 : ∫ s, (φ s - y s) ∂lam = 0 := by rw [integral_sub hxi hyi, hx0, hy0, sub_zero]
  have gp := hg _ hpL hp0
  have gm := hg _ hmL hm0
  beta_reduce at gp gm
  rw [hP] at gp
  rw [hQ] at gm
  -- the squares
  have hsq : ∫ s, (φ s + y s) ^ 2 ∂lam + ∫ s, (φ s - y s) ^ 2 ∂lam
      = 2 * ∫ s, φ s ^ 2 ∂lam + 2 * ∫ s, y s * y s ∂lam := by
    rw [← integral_add hpL.integrable_sq hmL.integrable_sq, ← integral_const_mul,
      ← integral_const_mul, ← integral_add (hxL.integrable_sq.const_mul 2) (hyy.const_mul 2)]
    congr 1; funext s; ring
  have hA : ∫ s, φ s ^ 2 ∂lam = 1 := by
    have h2 := eLpNorm_two_sq_eq_lintegral lam φ
    rw [hxn, one_pow, ← ofReal_integral_eq_lintegral_ofReal hxL.integrable_sq
      (ae_of_all _ fun s => sq_nonneg _)] at h2
    exact (ENNReal.ofReal_eq_one.1 h2.symm)
  have hB : ∫ s, y s ^ 2 ∂lam = ∫ s, y s * y s ∂lam := by simp only [sq]
  have hBnn : 0 ≤ ∫ s, y s * y s ∂lam := integral_nonneg fun s => mul_self_nonneg _
  have key : ∫ s, y s * y s ∂lam ≤ (1 - c) / (1 + c) := by
    rw [le_div_iff₀ (by linarith)]
    have h1 := (le_abs_self _).trans gp
    have h2 := (neg_le_abs _).trans gm
    nlinarith [hsq, hA, hrev']
  rw [← ofReal_integral_eq_lintegral_ofReal hyL.integrable_sq (ae_of_all _ fun s => sq_nonneg _),
    hB]
  exact ENNReal.ofReal_le_ofReal (key.trans (le_max_left _ _))

/-- **The corrected remark for a reversible policy** (C-30): `λπ = λ`, `T` self-adjoint on
`L²(λ)` with spectrum on mean-zero functions in `[−1 + c, 1 − c]`, gives summable `L²`-mixing
(with `λ̂ = λ`) and exponential decay. -/
theorem isSummablyL2Mixing_of_reversible (π : Kernel S S) [IsMarkovKernel π]
    (lam : Measure S) [IsFiniteMeasure lam] (hinv : lam.bind π = lam)
    (hrev : IsReversibleL2 π lam) (hgap : HasTwoSidedSpectralGap π lam) :
    IsSummablyL2Mixing π lam ∧ HasExponentialL2Decay π lam :=
  ⟨isSummablyL2Mixing_of_mixingCoeff_lt_one π lam hinv
      (mixingCoeff_one_lt_one_of_reversible π lam hinv hrev hgap),
    hasExponentialL2Decay_of_mixingCoeff_lt_one π lam hinv
      (mixingCoeff_one_lt_one_of_reversible π lam hinv hrev hgap)⟩

/-! ## The swap of two points -/

namespace Swap

/-- The swap `b ↦ ¬b` as a measurable involution of `Bool`. -/
def notEquiv : Bool ≃ᵐ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := Bool.not_not b
  right_inv b := Bool.not_not b
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem policy_eq_deterministic :
    flow.policy = Kernel.deterministic notEquiv notEquiv.measurable := rfl

/-- `∫ φ dλ = (φ(true) + φ(false))/2` for the uniform `λ` on `Bool`. -/
theorem integral_lam (φ : Bool → ℝ) : ∫ b, φ b ∂Coin.lam = (φ true + φ false) / 2 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
  simp only [measureReal_def, Coin.lam_singleton, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]
  ring

/-- On `Bool` with the uniform `λ`, an a.e. equality is an equality. -/
theorem eq_of_ae_eq {β : Type*} {f g : Bool → β} (h : f =ᵐ[Coin.lam] g) : f = g := by
  funext b
  by_contra hb
  have h0 : Coin.lam {x | ¬ f x = g x} = 0 := ae_iff.mp h
  have hle : Coin.lam {b} ≤ Coin.lam {x | ¬ f x = g x} :=
    measure_mono (Set.singleton_subset_iff.mpr hb)
  rw [h0, Coin.lam_singleton] at hle
  exact absurd hle (by norm_num)

/-- The swap preserves the uniform `λ`. -/
theorem lam_map_notEquiv : Coin.lam.map notEquiv = Coin.lam := by
  rw [← bind_deterministic_eq_map notEquiv.measurable]; exact bind_policy_lam

/-- A mean-zero function on `Bool` is odd under the swap. -/
theorem neg_of_integral_eq_zero {φ : Bool → ℝ} (hφ : ∫ b, φ b ∂Coin.lam = 0) (b : Bool) :
    φ (!b) = -φ b := by
  rw [integral_lam] at hφ
  cases b <;> simp <;> linarith

/-- **`φπⁿ = φ ∘ ¬ⁿ`** for the swap, pointwise. -/
theorem transfer_eq_comp (n : ℕ) (φ : Bool → ℝ) :
    transfer flow.policy Coin.lam n φ = fun b => φ ((fun b : Bool => !b)^[n] b) := by
  rw [policy_eq_deterministic]
  exact eq_of_ae_eq
    (transfer_deterministic_ae notEquiv lam_map_notEquiv n (measurable_of_countable φ))

/-- **`φπ = −φ` on mean-zero functions** (`main.tex:273`): the swap's Koopman operator is `−I`
there, its spectrum `{−1}`, bounded away from `1`. -/
theorem transfer_eq_neg {φ : Bool → ℝ} (hφ : ∫ b, φ b ∂Coin.lam = 0) :
    transfer flow.policy Coin.lam 1 φ = -φ := by
  rw [transfer_eq_comp 1 φ]
  funext b
  simp only [Function.iterate_one, Pi.neg_apply]
  exact neg_of_integral_eq_zero hφ b

/-- `φπⁿ = (−1)ⁿ φ` on mean-zero functions: the iterates do not converge, though their Cesàro
means do (`main.tex:271`). -/
theorem transfer_eq_pow_smul {φ : Bool → ℝ} (hφ : ∫ b, φ b ∂Coin.lam = 0) (n : ℕ) :
    transfer flow.policy Coin.lam n φ = (-1 : ℝ) ^ n • φ := by
  rw [transfer_eq_comp n φ]
  funext b
  simp only [Pi.smul_apply, smul_eq_mul]
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih (!b), neg_of_integral_eq_zero hφ b, pow_succ]
      ring

/-- `⟨φπ, φ⟩ = −‖φ‖²` on mean-zero functions. -/
theorem integral_transfer_mul_self {φ : Bool → ℝ} (hφ : ∫ b, φ b ∂Coin.lam = 0) :
    ∫ b, transfer flow.policy Coin.lam 1 φ b * φ b ∂Coin.lam = -∫ b, φ b ^ 2 ∂Coin.lam := by
  rw [transfer_eq_neg hφ]
  simp only [Pi.neg_apply, neg_mul, integral_neg, sq]

theorem isReversibleL2 : IsReversibleL2 flow.policy Coin.lam := by
  intro φ ψ _ _
  rw [transfer_eq_comp 1 φ, transfer_eq_comp 1 ψ, integral_lam, integral_lam]
  simp only [Function.iterate_one, Bool.not_true, Bool.not_false]
  ring

theorem hasOneSidedSpectralGap : HasOneSidedSpectralGap flow.policy Coin.lam := by
  refine ⟨2, two_pos, fun φ _ hφ => ?_⟩
  rw [integral_transfer_mul_self hφ]
  linarith

theorem hasNoAlmostInvariantVectors : HasNoAlmostInvariantVectors flow.policy Coin.lam := by
  refine ⟨4, by norm_num, fun φ _ hφ => le_of_eq ?_⟩
  rw [transfer_eq_neg hφ, ← integral_const_mul]
  congr 1; funext s
  simp only [Pi.neg_apply]
  ring

/-- Every `φ ∈ H` has `φ² ≡ 1` on `Bool`. -/
theorem sq_eq_one_of_mem {φ : Bool → ℝ} (hφ : φ ∈ unitMeanZero Coin.lam) (b : Bool) :
    φ b ^ 2 = 1 := by
  obtain ⟨-, hn, h0⟩ := hφ
  have hf : φ false = -φ true := by simpa using neg_of_integral_eq_zero h0 true
  have ht : φ true ^ 2 = 1 := by
    have h2 := eLpNorm_two_sq_eq_lintegral Coin.lam φ
    rw [hn, one_pow, lintegral_fintype, Fintype.sum_bool, Coin.lam_singleton,
      Coin.lam_singleton, hf, neg_sq, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one] at h2
    exact ENNReal.ofReal_eq_one.1 h2.symm
  cases b
  · rw [hf, neg_sq, ht]
  · exact ht

/-- The sign function `𝟙_{true} − 𝟙_{false}` lies in `H`. -/
theorem sign_mem_unitMeanZero :
    (fun b : Bool => if b then (1 : ℝ) else -1) ∈ unitMeanZero Coin.lam := by
  refine ⟨MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (ae_of_all _ fun b => by cases b <;> simp), ?_, ?_⟩
  · have hnorm : eLpNorm (fun b : Bool => if b then (1 : ℝ) else -1) 2 Coin.lam
        = eLpNorm (fun _ : Bool => (1 : ℝ)) 2 Coin.lam :=
      eLpNorm_congr_norm_ae (ae_of_all _ fun b => by cases b <;> simp)
    rw [hnorm, eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero _), measure_univ]
    simp
  · rw [integral_lam]; norm_num

/-- **`γₙ = λ̂(𝒮)` for every `n` and every measure `λ̂`** (`EGF.Defs`' reading): `= 1` for
`λ̂ = λ`, never summable for `λ̂ ≠ 0`. -/
theorem mixingCoeff_eq (lamHat : Measure Bool) (n : ℕ) :
    mixingCoeff flow.policy Coin.lam lamHat n = lamHat Set.univ := by
  have key : ∀ φ ∈ unitMeanZero Coin.lam, ∀ b,
      transfer flow.policy Coin.lam n φ b ^ 2 = 1 := by
    intro φ hφ b
    rw [transfer_eq_pow_smul hφ.2.2 n]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, sq_eq_one_of_mem hφ b, mul_one, ← pow_mul, mul_comm, pow_mul, neg_one_sq,
      one_pow]
  apply le_antisymm
  · refine iSup₂_le fun φ hφ => ?_
    simp only [key φ hφ, ENNReal.ofReal_one, lintegral_one, le_refl]
  · refine le_trans ?_ (le_iSup₂ (f := fun φ (_ : φ ∈ unitMeanZero Coin.lam) =>
      ∫⁻ s, ENNReal.ofReal (transfer flow.policy Coin.lam n φ s ^ 2) ∂lamHat) _
      sign_mem_unitMeanZero)
    simp only [key _ sign_mem_unitMeanZero, ENNReal.ofReal_one, lintegral_one, le_refl]

/-- **The swap is not summably `L²`-mixing**, for any `λ̂` (C-30). -/
theorem not_isSummablyL2Mixing : ¬ IsSummablyL2Mixing flow.policy Coin.lam := by
  rintro ⟨lamHat, -, -, hac', hsum⟩
  have h0 : lamHat Set.univ ≠ 0 := by
    intro h
    have h1 : Coin.lam Set.univ = 0 := hac' h
    rw [measure_univ] at h1
    exact one_ne_zero h1
  have hc : ∑' n, mixingCoeff flow.policy Coin.lam lamHat n = ∑' _ : ℕ, lamHat Set.univ :=
    tsum_congr fun n => mixingCoeff_eq lamHat n
  rw [hc] at hsum
  exact hsum (ENNReal.tsum_const_eq_top_of_ne_zero h0)

/-- **C-29, two points** (`main.tex:697`, `:702`): the swap is a universal policy and is not
summably `L²`-mixing. -/
theorem universal_not_summablyMixing :
    IsUniversalPolicy Coin.lam flow.policy ∧ ¬ IsSummablyL2Mixing flow.policy Coin.lam :=
  ⟨isUniversalPolicy_policy, not_isSummablyL2Mixing⟩

/-- **C-29 at the family level, two points**: the fixed-policy family `{swap} × L²₊(λ)` is
ε-universal and contains no summably `L²`-mixing policy. -/
theorem universalFamily_not_summablyMixing :
    IsUniversalFamilyEps Coin.lam (fixedPolicyFamily Coin.lam flow.policy) ∧
      ∀ F ∈ fixedPolicyFamily Coin.lam flow.policy, ¬ IsSummablyL2Mixing F.policy Coin.lam := by
  refine ⟨(isUniversalFamilyEps_fixedPolicyFamily_iff Coin.lam flow.policy Coin.lam
    bind_policy_lam Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl).2
    isKernelErgodic_policy, ?_⟩
  rintro F ⟨hF, -⟩
  rw [hF]
  exact not_isSummablyL2Mixing

/-- **The swap is an EGF** in the sense of `def:egf`, with one move and the uniform weight
`α = 1/p = 1`: the kernel of `equ:forward_policy` with `αⁱ = 1/p` for a group `{id, ¬}` whose action
has no almost invariant vector (`Swap.hasNoAlmostInvariantVectors`), yet without a two-sided gap
(`Swap.not_hasTwoSidedSpectralGap`) and not summably mixing. Its generating measure `δ_¬` sits on
the coset `{¬}` of the subgroup `{id}`; Bekka–Guivarc'h's aperiodicity condition is sufficient for
their equivalence of the two gaps, not necessary. -/
theorem isEGF_flow : IsEGF flow (fun _ : Fin 1 => Coin.notHomeo) (fun _ _ => 1) := by
  refine ⟨⟨fun _ => Measurable.of_discrete, fun _ => measurable_const, fun _ _ => zero_le_one,
    fun _ => by simp, fun s => ?_⟩, ?_⟩
  · rw [show flow.policy s = Measure.dirac (!s) from Kernel.deterministic_apply (measurable_of_countable _) s]
    simp [Coin.notHomeo]
  · intro x y U hU
    have hy : y ∈ U := mem_of_mem_nhds hU
    by_cases hxy : x = y
    · exact ⟨[], by simpa [hxy] using hy⟩
    · refine ⟨[0], ?_⟩
      have : Coin.notHomeo x = y := by cases x <;> cases y <;> simp_all [Coin.notHomeo]
      simpa [this] using hy

/-- The swap has no two-sided gap: its spectrum on mean-zero functions contains `−1`. -/
theorem not_hasTwoSidedSpectralGap : ¬ HasTwoSidedSpectralGap flow.policy Coin.lam := by
  rintro ⟨c, hc, h⟩
  have hφ := sign_mem_unitMeanZero
  have h1 := h _ hφ.1 hφ.2.2
  rw [integral_transfer_mul_self hφ.2.2, abs_neg,
    abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at h1
  have hpos : 0 < ∫ b, (fun b : Bool => if b then (1 : ℝ) else -1) b ^ 2 ∂Coin.lam := by
    rw [integral_lam]; norm_num
  nlinarith

/-- The swap's iterates do not decay: `γₙ = 1` for `λ̂ = λ`. -/
theorem not_hasExponentialL2Decay : ¬ HasExponentialL2Decay flow.policy Coin.lam := by
  intro h
  obtain ⟨N, hN⟩ := (hasExponentialL2Decay_iff flow.policy Coin.lam bind_policy_lam).1 h
  rw [mixingCoeff_eq, measure_univ] at hN
  exact lt_irrefl _ hN

end Swap

/-- **The remark of `main.tex:273` as printed is false** (C-30): the swap. -/
theorem not_spectralGapRemarkPrinted : ¬ SpectralGapRemarkPrinted := by
  intro h
  exact Swap.not_isSummablyL2Mixing (h Bool Coin.lam Swap.flow.policy inferInstance inferInstance
    Swap.bind_policy_lam Swap.isKernelErgodic_policy Swap.isReversibleL2
    Swap.hasOneSidedSpectralGap Swap.hasNoAlmostInvariantVectors)

/-- **`main.tex:274` as printed is false**: the swap's iterates do not decay. -/
theorem not_spectralGapRemarkExponentialPrinted : ¬ SpectralGapRemarkExponentialPrinted := by
  intro h
  exact Swap.not_hasExponentialL2Decay (h Bool Coin.lam Swap.flow.policy inferInstance
    inferInstance Swap.bind_policy_lam Swap.isKernelErgodic_policy Swap.isReversibleL2
    Swap.hasOneSidedSpectralGap Swap.hasNoAlmostInvariantVectors)

/-! ## The corrected criterion needs an invariance hypothesis -/

/-- The Koopman operator `T = transfer π λ 1` is bounded on `L²(λ)`: `‖Tφ‖₂² ≤ C ‖φ‖₂²`. -/
def HasBoundedKoopmanL2 (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ φ : S → ℝ, MemLp φ 2 lam →
    ∫⁻ s, ENNReal.ofReal (transfer π lam 1 φ s ^ 2) ∂lam ≤ C * ∫⁻ s, ENNReal.ofReal (φ s ^ 2) ∂lam

/-- **C-30's corrected criterion without the invariance of `λ`**: a Markov kernel on a
probability space whose Koopman operator is bounded on `L²(λ)` with `‖Tᴺ‖ < 1` on mean-zero
functions for some `N` is summably `L²`-mixing. False: `not_spectralRadiusCriterionWithoutInvariance`. -/
def SpectralRadiusCriterionWithoutInvariance : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (lam : Measure X) (π : Kernel X X), IsProbabilityMeasure lam →
    IsMarkovKernel π → HasBoundedKoopmanL2 π lam → (∃ N, mixingCoeff π lam lam N < 1) →
    IsSummablyL2Mixing π lam

namespace Sink

/-- The kernel sending both points of `Bool` to `true`, written `π(s) = 2·𝟙_{true} λ`. -/
noncomputable def pol : Kernel Bool Bool := Kernel.const Bool Coin.atTrue

instance : IsMarkovKernel pol := by unfold pol; infer_instance

/-- `φπ = (φ(true) + φ(false)) 𝟙_{true}`: all the mass goes to `true`. -/
theorem transfer_one_eq (φ : Bool → ℝ) :
    transfer pol Coin.lam 1 φ = fun b => if b then φ true + φ false else 0 := by
  have hd : ∀ μ : Measure Bool, pushIter pol 1 μ
      = Coin.lam.withDensity (μ Set.univ • fun b : Bool => if b then (2 : ℝ≥0∞) else 0) := by
    intro μ
    have h := pushIter_const_succ Coin.atTrue 0 μ
    simp only [zero_add] at h
    rw [pol, h, Coin.atTrue, ← withDensity_smul _ Measurable.of_discrete]
  have hr : ∀ c : ℝ≥0∞, (Coin.lam.withDensity (c • fun b : Bool => if b then (2 : ℝ≥0∞) else 0)).rnDeriv
      Coin.lam = c • fun b : Bool => if b then (2 : ℝ≥0∞) else 0 := fun c =>
    Swap.eq_of_ae_eq (Measure.rnDeriv_withDensity Coin.lam Measurable.of_discrete)
  funext b
  simp only [transfer, hd, hr, Coin.lam_withDensity_univ, Pi.smul_apply, smul_eq_mul]
  have hf1 : ∀ x : ℝ, ENNReal.ofReal x * 2⁻¹ ≠ ∞ := fun x =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 two_ne_zero)
  cases b
  · simp
  · simp only [if_true]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (hf1 _) (hf1 _),
      ENNReal.toReal_add (hf1 _) (hf1 _)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_inv,
      ENNReal.toReal_ofNat]
    rcases le_total 0 (φ true) with h1 | h1 <;> rcases le_total 0 (φ false) with h2 | h2 <;>
      simp [h1, h2] <;> ring

/-- **The iterates vanish on mean-zero functions**: `φπⁿ⁺¹ = 0` (spectral radius `0`). -/
theorem transfer_succ_eq_zero {φ : Bool → ℝ} (hφ : ∫ b, φ b ∂Coin.lam = 0) (n : ℕ) :
    transfer pol Coin.lam (n + 1) φ = 0 := by
  have hφi : Integrable φ Coin.lam := Integrable.of_finite
  have hp : ∫⁻ s, ENNReal.ofReal (φ s) ∂Coin.lam = ∫⁻ s, ENNReal.ofReal (-φ s) ∂Coin.lam := by
    have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφi
    rw [hφ, eq_comm, sub_eq_zero] at h
    exact (ENNReal.toReal_eq_toReal_iff' hφi.lintegral_lt_top.ne
      hφi.neg.lintegral_lt_top.ne).mp h
  funext s
  simp only [transfer, pol, pushIter_const_succ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hp, sub_self, Pi.zero_apply]

/-- `γₙ = 0` for `n ≥ 1`, for every `λ̂`. -/
theorem mixingCoeff_succ (lamHat : Measure Bool) (n : ℕ) :
    mixingCoeff pol Coin.lam lamHat (n + 1) = 0 := by
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) zero_le
  simp [transfer_succ_eq_zero hφ.2.2 n]

/-- The Koopman operator of `pol` is bounded on `L²(λ)`, with `C = 2`. -/
theorem hasBoundedKoopmanL2 : HasBoundedKoopmanL2 pol Coin.lam := by
  refine ⟨2, by simp, fun φ _ => ?_⟩
  rw [transfer_one_eq, lintegral_fintype, lintegral_fintype, Fintype.sum_bool, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, Coin.lam_singleton]
  have h : ENNReal.ofReal ((φ true + φ false) ^ 2)
      ≤ 2 * (ENNReal.ofReal (φ true ^ 2) + ENNReal.ofReal (φ false ^ 2)) := by
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (φ true - φ false)])
  calc ENNReal.ofReal ((φ true + φ false) ^ 2) * 2⁻¹ + ENNReal.ofReal ((0 : ℝ) ^ 2) * 2⁻¹
      = ENNReal.ofReal ((φ true + φ false) ^ 2) * 2⁻¹ := by simp
    _ ≤ 2 * (ENNReal.ofReal (φ true ^ 2) + ENNReal.ofReal (φ false ^ 2)) * 2⁻¹ := by gcongr
    _ = 2 * (ENNReal.ofReal (φ true ^ 2) * 2⁻¹ + ENNReal.ofReal (φ false ^ 2) * 2⁻¹) := by
        rw [mul_assoc, add_mul]

/-- **No invariant measure of `pol` is equivalent to `λ`**: an invariant `λ̂` is `λ̂(𝒮) δ_true`. -/
theorem not_isSummablyL2Mixing : ¬ IsSummablyL2Mixing pol Coin.lam := by
  rintro ⟨lamHat, hinv, -, hac', -⟩
  have h1 : lamHat {false} = 0 := by
    have h : (lamHat.bind pol) {false} = lamHat {false} := by rw [hinv]
    rw [← h]
    change (lamHat.bind (fun _ => Coin.atTrue)) {false} = 0
    rw [Measure.bind_const, Measure.smul_apply, Coin.atTrue, Coin.lam_withDensity_singleton]
    simp
  have h2 := hac' h1
  rw [Coin.lam_singleton] at h2
  norm_num at h2

end Sink

/-- **An invariance hypothesis cannot be dropped** from the corrected criterion (C-30; `λπ = λ` is a
sufficient one, not a necessary one): on two points,
the kernel sending everything to `true` has a bounded Koopman operator with `γ₁ = 0`, and no
invariant measure equivalent to `λ`. -/
theorem not_spectralRadiusCriterionWithoutInvariance : ¬ SpectralRadiusCriterionWithoutInvariance := by
  intro h
  exact Sink.not_isSummablyL2Mixing (h Bool Coin.lam Sink.pol inferInstance inferInstance
    Sink.hasBoundedKoopmanL2 ⟨1, by rw [Sink.mixingCoeff_succ]; exact zero_lt_one⟩)

/-! ## OQ-47's other reading, the variant with everything in `L²(λ̂)` -/

/-- **`def:summably_mixing` in one variant of OQ-47's other reading**: the transfer relative to
`λ̂`, `H` normalized in `L²(λ̂)` and of mean zero against `λ̂`, `γₙ` integrated against `λ̂` (the
variant normalizing `H` in `L²(λ)` is not formalized). -/
def IsSummablyL2MixingHat (π : Kernel S S) (lam : Measure S) : Prop :=
  ∃ lamHat : Measure S, lamHat.bind π = lamHat ∧ lamHat ≪ lam ∧ lam ≪ lamHat ∧
    ∑' n, mixingCoeff π lamHat lamHat n ≠ ∞

/-- No function has norm `1` in `L²(∞ · μ)`. -/
theorem unitMeanZero_top_smul (μ : Measure S) : unitMeanZero ((⊤ : ℝ≥0∞) • μ) = ∅ := by
  ext φ
  simp only [unitMeanZero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hn
  exfalso
  rw [eLpNorm_smul_measure_of_ne_zero (by simp : (⊤ : ℝ≥0∞) ≠ 0)] at hn
  have hpos : (0 : ℝ) < (1 / (2 : ℝ≥0∞)).toReal := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]; norm_num
  rw [ENNReal.top_rpow_of_pos hpos, smul_eq_mul] at hn
  rcases eq_or_ne (eLpNorm φ 2 μ) 0 with h0 | h0
  · rw [h0, mul_zero] at hn; exact zero_ne_one hn
  · rw [ENNReal.top_mul h0] at hn; exact ENNReal.top_ne_one hn

/-- **This variant must take `λ̂` σ-finite**: through the non-σ-finite `λ̂ = ∞ · λ`, in whose `L²`
no function has norm `1`, every kernel leaving `λ` invariant would satisfy it. -/
theorem isSummablyL2MixingHat_of_bind_eq (π : Kernel S S) (lam : Measure S)
    (hinv : lam.bind π = lam) : IsSummablyL2MixingHat π lam := by
  refine ⟨(⊤ : ℝ≥0∞) • lam, ?_, Measure.AbsolutelyContinuous.rfl.smul_left ⊤,
    Measure.absolutelyContinuous_smul (by simp), ?_⟩
  · rw [Measure.bind_smul, hinv]
  · have h0 : ∀ n, mixingCoeff π ((⊤ : ℝ≥0∞) • lam) ((⊤ : ℝ≥0∞) • lam) n = 0 := by
      intro n
      simp [mixingCoeff, unitMeanZero_top_smul]
    simp [h0]

/-- With a finite `λ̂`, the swap is not summably mixing in this variant either. -/
theorem Swap.not_isSummablyL2MixingHat_of_finite :
    ¬ ∃ lamHat : Measure Bool, IsFiniteMeasure lamHat ∧ lamHat.bind flow.policy = lamHat ∧
      lamHat ≪ Coin.lam ∧ Coin.lam ≪ lamHat ∧ ∑' n, mixingCoeff flow.policy lamHat lamHat n ≠ ∞ := by
  rintro ⟨lamHat, hfin, hinv, -, hac', hsum⟩
  have he : lamHat.map Swap.notEquiv = lamHat := by
    rw [← bind_deterministic_eq_map Swap.notEquiv.measurable]; exact hinv
  have hH : (unitMeanZero lamHat).Nonempty := by
    refine unitMeanZero_nonempty (A := {true}) (measurableSet_singleton _) ?_ ?_
    · intro h
      have h1 := hac' h
      rw [Coin.lam_singleton] at h1
      norm_num at h1
    · intro h
      have hc : ({true}ᶜ : Set Bool) = {false} := by ext b; cases b <;> simp
      have h1 := hac' h
      rw [hc, Coin.lam_singleton] at h1
      norm_num at h1
  exact not_isSummablyL2Mixing_of_map_eq Swap.notEquiv he hH
    ⟨lamHat, hinv, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, hsum⟩

end EGF
