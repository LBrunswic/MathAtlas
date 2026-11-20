import EGF.Defs
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The explicit backward policy of an Ergodic Generative Flow

`theo:backward_policy` — `main.tex:733` (statement `main.tex:733–739`, its setting
`main.tex:731–732`, proof `main.tex:740–766`; body version `main.tex:225–234`). Not marked: as
printed the statement is false in the appendix's setting (`main.tex:731–732`; findings below, whose
formal counterexamples are translations, not ergodic: the findings survive ergodicity by examples
checked by hand, see SCOPE); its corrected forms are proved
here, sorry-free, and which one becomes the formalization of record is the author's call.

> As stated in section \ref{sec:fundamentals_EGF}, on a Differential manifold $\Statespace$ endowed
> with a background measure $\lambda$ absolutely continuous with respect to Lebesgue measure, we
> define an EGF as a Generative Flow $(\ForwardPolicyStar, \Foutstar)$ with
> $\Foutstar = \foutstar \lambda$ and
> $\ForwardPolicyStar(s\rightarrow \cdot) = \sum_{i=1}^p\forwardalpha^{i}(s)\delta_{\Phi_i(s)}$
> where $\Phi_i$ are diffeomorphisms of $\Statespace$. (`main.tex:731–732`)

> Let $(\ForwardPolicyStar,\Foutstar)$ as above, the induced Generative Flow on $\Statespace$ has
> a backward star policy given by
> $\BackwardPolicy^*(s) = \sum_{i=1}^p\backwardalpha^i(s) \delta_{\Phi_i^{-1}(s)}$,
> $\backwardalpha^i(s) = \frac{(\forwardalpha^if^*_\rightarrow)\circ \Phi_i^{-1}(s)|J_s {\Phi_i^{-1}}| }{ \finstar(s)}$,
> $\finstar = \sum_j (\forwardalpha^jf^*_\rightarrow)\circ \Phi_j^{-1}(s) |J_s {\Phi_j^{-1}}|$.
> (`main.tex:733–739`)

> $\BackwardPolicyStar(s\rightarrow X) = \frac{d \Finstar \otimes \BackwardPolicyStar ( \cdot \rightarrow X)}{d\Finstar}(s)$,
> $\Finstar \otimes \BackwardPolicyStar(Y\rightarrow X) = \Foutstar \otimes \ForwardPolicyStar(X\rightarrow Y)$.
> (`main.tex:744–745`, quoted from brunswic2024theory)

> where $J_s$ denotes the Jacobian matrix at $s$. (`main.tex:230`, in the body version)

## What is proved

| | |
|---|---|
| `IsBackwardPolicy` | `F_in ⊗ B(Y → X) = F_out ⊗ π(X → Y)` (`main.tex:745`); `isBackwardPolicy_iff_ae_eq_rnDeriv` (`:744`), `_iff_compProd`; existence `isBackwardPolicy_posterior`, uniqueness `.ae_eq_apply`, `.ae_eq_posterior` |
| `inflowDensity`, `backwardWeight`, `backwardKernel` | the printed `f_in`, `βⁱ`, `B*`, for a Jacobian factor `J` |
| `backward_policy` (principal), `backward_policy_of_map_eq` | if `Φᵢ₊λ = Jᵢ λ`: `F_in = f_in λ`, `B*` is a backward policy, Markov `F_in`-a.e., and the unique one |
| `backward_policy_rnDeriv` | `Jᵢ = d(Φᵢ₊λ)/dλ`, for `Φᵢ₊λ ≪ λ` |
| `backward_policy_addHaar`, `_diffeomorph` | `ℝᵈ`, Lebesgue (Haar), `Jᵢ = |det J_s Φᵢ⁻¹|` (`coordJac`): the body's setting |
| `backward_policy_equiv_addHaar` | `λ` equivalent to Lebesgue, `Jᵢ = d(Φᵢ₊λ)/dλ` |
| `printed_backward_policy_false` | finding: `coordJac` with a finite `λ` equivalent to Lebesgue fails |
| `printed_inflow_not_ac` | finding: with `λ ≪` Lebesgue only, `F_in ≪ λ` fails, whatever `J` |

## Hypothesis checklist

| paper | here |
|---|---|
| `𝒮` a differential manifold | ⚠ weakened: any measurable space |
| `λ ≪` Lebesgue | ⚠ strengthened: `Φᵢ₊λ = Jᵢ λ`, i.e. `Φᵢ₊λ ≪ λ`, needed (`printed_inflow_not_ac`); implied by `λ` equivalent to Lebesgue (`map_ac_of_equiv_addHaar`) |
| `Φᵢ` diffeomorphisms | ⚠ weakened: measurable bijections `𝒮 ≃ᵐ 𝒮` (on `ℝᵈ`: with differentiable inverse) |
| `|J_s Φᵢ⁻¹|` | ? `Jᵢ` with `Φᵢ₊λ = Jᵢ λ` (the `λ`-Jacobian); `coordJac` on `ℝᵈ` with Haar `λ` |
| `π*(s) = ∑ αⁱ(s) δ_{Φᵢ(s)}` | ✓ `IsEGFPolicy` (`EGF.Defs`: `α` measurable, `∑ αⁱ = 1`); no ergodicity |
| `F_out = f_out λ` | ✓ `f_out` measurable, `ℝ≥0∞`-valued, `F_out` finite (a `GenerativeFlow`) |
| `B*` "given by" the formula | ✓ backward policy, Markov and unique `F_in`-a.e. (`β` is `0` where `f_in ∈ {0, ∞}`, `F_in`-null) |

## SCOPE (disclosed)

**Not marked.** (1) With `λ ≪` Lebesgue only, `F_in` need not be `≪ λ`, so `f_in` does not exist
(`printed_inflow_not_ac`, the line `f_in` of `main.tex:737`, any `J`; the formal counterexample is a
translation, not ergodic; an ergodic one, checked by hand and not formalized: `Φ = (x + 1, x − √2)`,
`α = (½, ½)`, `λ = 𝟙_[0,1)·Leb`, `f_out = 1`, with dense forward orbits and `F_in` singular to `λ`);
the proof's change of variables (`main.tex:754`) needs
`Φᵢ₊λ = |J Φᵢ⁻¹| λ`. (2) With `|J_s Φᵢ⁻¹|` the coordinate Jacobian (`main.tex:230`), the formulas
fail for a finite `λ` equivalent to Lebesgue (`printed_backward_policy_false`, on `ℝ`, a translation;
an irrational rotation of the circle gives an ergodic counterexample, by hand); they hold
for `λ` Lebesgue/Haar (`backward_policy_addHaar`) and, with the `λ`-Jacobian, for every
σ-finite quasi-invariant `λ` (`backward_policy`, `backward_policy_rnDeriv`). No manifold instance:
Mathlib (`fabf563a`) has no manifold volume measure; the measurable-space theorem covers every
manifold once `|J_s Φᵢ⁻¹|` is read relative to `λ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Manifold

variable {S : Type*} [MeasurableSpace S]

/-! ## The backward star policy (`main.tex:741–745`) -/

/-- **A backward star policy** of the generative flow `(π, F_out)` (brunswic2024theory §3.2 and
its Proposition 1, as quoted at `main.tex:741–745`): a kernel `B` with
`F_in ⊗ B(Y → X) = F_out ⊗ π(X → Y)` for all measurable `X, Y`, where `F_in = F_out π`
(`EGF.inflow`, `main.tex:743`) and `μ ⊗ κ(A → B) := ∫_{x ∈ A} κ(x)(B) dμ(x)` is the tensor of
`main.tex:158`. The Radon–Nikodym form of `main.tex:744` is `isBackwardPolicy_iff_ae_eq_rnDeriv`;
such a `B` is Markov `F_in`-a.e. (`IsBackwardPolicy.ae_apply_univ`), unique `F_in`-a.e.
(`IsBackwardPolicy.ae_eq_apply`), and exists on a standard Borel space
(`isBackwardPolicy_posterior`). -/
def IsBackwardPolicy (π : Kernel S S) (Fout : Measure S) (B : Kernel S S) : Prop :=
  ∀ X Y : Set S, MeasurableSet X → MeasurableSet Y →
    ∫⁻ y in Y, B y X ∂(inflow π Fout) = ∫⁻ x in X, π x Y ∂Fout

/-- `F_out ⊗ π(X → Y) = ((F_out|_X) π)(Y)`: the tensor, as a measure in its target. -/
theorem setLIntegral_eq_bind_restrict (π : Kernel S S) (Fout : Measure S) (X : Set S) {Y : Set S}
    (hY : MeasurableSet Y) : ∫⁻ x in X, π x Y ∂Fout = (Fout.restrict X).bind π Y := by
  rw [Measure.bind_apply hY π.aemeasurable]

/-- `(F_out|_X) π ≤ F_in`. -/
theorem bind_restrict_le_inflow (π : Kernel S S) (Fout : Measure S) (X : Set S) :
    (Fout.restrict X).bind π ≤ inflow π Fout :=
  Measure.le_iff.mpr fun Y hY => by
    rw [inflow, Measure.bind_apply hY π.aemeasurable, Measure.bind_apply hY π.aemeasurable]
    exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- **The Radon–Nikodym form** (`main.tex:744–745`): `B` is a backward policy iff, for every
measurable `X`, `B(· → X) = d(F_out ⊗ π(X → ·))/dF_in`, `F_in`-a.e. -/
theorem isBackwardPolicy_iff_ae_eq_rnDeriv (π : Kernel S S) [IsMarkovKernel π] (Fout : Measure S)
    [IsFiniteMeasure Fout] (B : Kernel S S) :
    IsBackwardPolicy π Fout B ↔ ∀ X, MeasurableSet X →
      (fun y => B y X) =ᵐ[inflow π Fout] ((Fout.restrict X).bind π).rnDeriv (inflow π Fout) := by
  have hac : ∀ X, (Fout.restrict X).bind π ≪ inflow π Fout := fun X =>
    Measure.absolutelyContinuous_of_le (bind_restrict_le_inflow π Fout X)
  constructor
  · intro h X hX
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (B.measurable_coe hX)
      (Measure.measurable_rnDeriv _ _) fun Y hY _ => ?_
    rw [h X Y hX hY, Measure.setLIntegral_rnDeriv' (hac X) hY,
      setLIntegral_eq_bind_restrict π Fout X hY]
  · intro h X Y hX hY
    rw [lintegral_congr_ae (ae_restrict_of_ae (h X hX)), Measure.setLIntegral_rnDeriv' (hac X) hY,
      setLIntegral_eq_bind_restrict π Fout X hY]

/-- In Mathlib's terms: `B` is a backward policy iff `F_in ⊗ₘ B` is the swap of `F_out ⊗ₘ π`. -/
theorem isBackwardPolicy_iff_compProd (π : Kernel S S) [IsMarkovKernel π] (Fout : Measure S)
    [IsFiniteMeasure Fout] (B : Kernel S S) [IsSFiniteKernel B] :
    IsBackwardPolicy π Fout B ↔ inflow π Fout ⊗ₘ B = (Fout ⊗ₘ π).map Prod.swap := by
  have hR : ∀ {X Y : Set S}, MeasurableSet X → MeasurableSet Y →
      (Fout ⊗ₘ π).map Prod.swap (Y ×ˢ X) = ∫⁻ x in X, π x Y ∂Fout := fun hX hY => by
    rw [Measure.map_apply measurable_swap (hY.prod hX), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hX hY]
  have hL : ∀ {X Y : Set S}, MeasurableSet X → MeasurableSet Y →
      (inflow π Fout ⊗ₘ B) (Y ×ˢ X) = ∫⁻ y in Y, B y X ∂(inflow π Fout) := fun hX hY => by
    rw [Measure.compProd_apply_prod hY hX]
  constructor
  · intro h
    refine (ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_).symm
    · rintro _ ⟨Y, hY, X, hX, rfl⟩
      rw [hR hX hY, hL hX hY, h X Y hX hY]
    · rw [← Set.univ_prod_univ, hR MeasurableSet.univ MeasurableSet.univ,
        hL MeasurableSet.univ MeasurableSet.univ, h _ _ MeasurableSet.univ MeasurableSet.univ]
  · intro h X Y hX hY
    rw [← hL hX hY, ← hR hX hY, h]

/-- **Existence** on a standard Borel space: Mathlib's posterior (Bayesian inverse) `π†F_out` is a
backward policy. -/
theorem isBackwardPolicy_posterior [StandardBorelSpace S] [Nonempty S] (π : Kernel S S)
    [IsMarkovKernel π] (Fout : Measure S) [IsFiniteMeasure Fout] :
    IsBackwardPolicy π Fout (π†Fout) :=
  (isBackwardPolicy_iff_compProd π Fout _).2 compProd_posterior_eq_map_swap

/-- **Uniqueness** on a standard Borel space: a finite backward policy is `F_in`-a.e. equal to the
posterior `π†F_out`. -/
theorem IsBackwardPolicy.ae_eq_posterior [StandardBorelSpace S] [Nonempty S] {π : Kernel S S}
    [IsMarkovKernel π] {Fout : Measure S} [IsFiniteMeasure Fout] {B : Kernel S S}
    [IsFiniteKernel B] (h : IsBackwardPolicy π Fout B) : B =ᵐ[inflow π Fout] π†Fout :=
  ae_eq_posterior_of_compProd_eq ((isBackwardPolicy_iff_compProd π Fout B).1 h)

/-- **Uniqueness, setwise**, on any measurable space: two backward policies give the same mass to
each measurable `X`, `F_in`-a.e. -/
theorem IsBackwardPolicy.ae_eq_apply {π : Kernel S S} [IsMarkovKernel π] {Fout : Measure S}
    [IsFiniteMeasure Fout] {B B' : Kernel S S} (h : IsBackwardPolicy π Fout B)
    (h' : IsBackwardPolicy π Fout B') {X : Set S} (hX : MeasurableSet X) :
    (fun y => B y X) =ᵐ[inflow π Fout] fun y => B' y X :=
  (((isBackwardPolicy_iff_ae_eq_rnDeriv π Fout B).1 h X hX).trans
    ((isBackwardPolicy_iff_ae_eq_rnDeriv π Fout B').1 h' X hX).symm)

/-- A backward policy is a Markov kernel `F_in`-a.e. -/
theorem IsBackwardPolicy.ae_apply_univ {π : Kernel S S} [IsMarkovKernel π] {Fout : Measure S}
    [IsFiniteMeasure Fout] {B : Kernel S S} (h : IsBackwardPolicy π Fout B) :
    ∀ᵐ y ∂(inflow π Fout), B y univ = 1 := by
  have h1 := (isBackwardPolicy_iff_ae_eq_rnDeriv π Fout B).1 h univ MeasurableSet.univ
  rw [Measure.restrict_univ] at h1
  filter_upwards [h1, Measure.rnDeriv_self (inflow π Fout)] with y hy hy'
  rw [hy]; exact hy'

/-! ## The printed formula (`main.tex:733–739`) -/

variable {p : ℕ}

/-- The `i`-th term `(αⁱ f_out)∘Φᵢ⁻¹(s) · |J_s Φᵢ⁻¹|` of the printed formulas (`main.tex:736–737`),
the Jacobian factor `|J_s Φᵢ⁻¹|` being the argument `J i s`. -/
noncomputable def inflowTerm (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (J : Fin p → S → ℝ≥0∞) (i : Fin p) (s : S) : ℝ≥0∞ :=
  ENNReal.ofReal (α i ((Φ i).symm s)) * fout ((Φ i).symm s) * J i s

/-- **The printed star-inflow density** `f_in(s) = ∑ⱼ (αʲ f_out)∘Φⱼ⁻¹(s) |J_s Φⱼ⁻¹|`
(`main.tex:737`; `main.tex:233` in the body). -/
noncomputable def inflowDensity (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (J : Fin p → S → ℝ≥0∞) (s : S) : ℝ≥0∞ :=
  ∑ j, inflowTerm Φ α fout J j s

/-- **The printed backward weights** `βⁱ(s) = (αⁱ f_out)∘Φᵢ⁻¹(s) |J_s Φᵢ⁻¹| / f_in(s)`
(`main.tex:736`), computed in `ℝ≥0∞` and returned in `[0, 1]`. Where `f_in(s) ∈ {0, ∞}` the printed
quotient is undefined; there it is `0`, on an `F_in`-null set (`backward_policy_of_map_eq`). -/
noncomputable def backwardWeight (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (J : Fin p → S → ℝ≥0∞) (i : Fin p) (s : S) : ℝ :=
  (inflowTerm Φ α fout J i s / inflowDensity Φ α fout J s).toReal

/-- Measurability of the printed terms, density and weights. -/
theorem measurable_inflowTerm (Φ : Fin p → S ≃ᵐ S) {α : Fin p → S → ℝ} {fout : S → ℝ≥0∞}
    {J : Fin p → S → ℝ≥0∞} (hα : ∀ i, Measurable (α i)) (hf : Measurable fout)
    (hJ : ∀ i, Measurable (J i)) (i : Fin p) : Measurable (inflowTerm Φ α fout J i) :=
  ((ENNReal.measurable_ofReal.comp ((hα i).comp (Φ i).symm.measurable)).mul
    (hf.comp (Φ i).symm.measurable)).mul (hJ i)

theorem measurable_inflowDensity (Φ : Fin p → S ≃ᵐ S) {α : Fin p → S → ℝ} {fout : S → ℝ≥0∞}
    {J : Fin p → S → ℝ≥0∞} (hα : ∀ i, Measurable (α i)) (hf : Measurable fout)
    (hJ : ∀ i, Measurable (J i)) : Measurable (inflowDensity Φ α fout J) :=
  Finset.measurable_sum _ fun i _ => measurable_inflowTerm Φ hα hf hJ i

theorem measurable_backwardWeight (Φ : Fin p → S ≃ᵐ S) {α : Fin p → S → ℝ} {fout : S → ℝ≥0∞}
    {J : Fin p → S → ℝ≥0∞} (hα : ∀ i, Measurable (α i)) (hf : Measurable fout)
    (hJ : ∀ i, Measurable (J i)) (i : Fin p) : Measurable (backwardWeight Φ α fout J i) :=
  ((measurable_inflowTerm Φ hα hf hJ i).div (measurable_inflowDensity Φ hα hf hJ)).ennreal_toReal

/-- **The printed backward policy** `B(s) = ∑ᵢ βⁱ(s) δ_{Φᵢ⁻¹(s)}` (`main.tex:735`): the
`egfKernel` of the inverse maps `Φᵢ⁻¹` with the weights `βⁱ`. -/
noncomputable def backwardKernel (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (J : Fin p → S → ℝ≥0∞) (hα : ∀ i, Measurable (α i)) (hf : Measurable fout)
    (hJ : ∀ i, Measurable (J i)) : Kernel S S :=
  egfKernel (fun i => (Φ i).symm) (backwardWeight Φ α fout J) (fun i => (Φ i).symm.measurable)
    (measurable_backwardWeight Φ hα hf hJ)

/-- `(∑ᵢ αⁱ(s) δ_{Φᵢ(s)})(X) = ∑ᵢ αⁱ(s) 𝟙_X(Φᵢ(s))`. -/
theorem egfKernel_apply_set {Φ : Fin p → S → S} {α : Fin p → S → ℝ} (hΦ : ∀ i, Measurable (Φ i))
    (hα : ∀ i, Measurable (α i)) (s : S) {X : Set S} (hX : MeasurableSet X) :
    egfKernel Φ α hΦ hα s X = ∑ i, ENNReal.ofReal (α i s) * X.indicator 1 (Φ i s) := by
  show (∑ i, ENNReal.ofReal (α i s) • Measure.dirac (Φ i s)) X = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hX, smul_eq_mul]

/-- `π(s → X) = ∑ᵢ αⁱ(s) 𝟙_X(Φᵢ(s))` (`main.tex:752–753`). -/
theorem IsEGFPolicy.apply_set {π : Kernel S S} {Φ : Fin p → S → S} {α : Fin p → S → ℝ}
    (h : IsEGFPolicy π Φ α) (s : S) {X : Set S} (hX : MeasurableSet X) :
    π s X = ∑ i, ENNReal.ofReal (α i s) * X.indicator 1 (Φ i s) := by
  rw [h.apply_eq s, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hX, smul_eq_mul]

/-- Change of variables along `Φ`, when `Φ₊λ = J λ`. -/
theorem lintegral_mul_jacobian {lam : Measure S} (Φ : S ≃ᵐ S) {J : S → ℝ≥0∞} (hJm : Measurable J)
    (hJ : lam.map Φ = lam.withDensity J) {g : S → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, J s * g s ∂lam = ∫⁻ u, g (Φ u) ∂lam := by
  rw [← lintegral_map_equiv g Φ, hJ, lintegral_withDensity_eq_lintegral_mul _ hJm hg]
  rfl

/-- **The computation of `main.tex:749–755`**: `F_out ⊗ π(X → Y)`, after the change of variables
`s = Φᵢ⁻¹(u)` that `Φᵢ₊λ = Jᵢ λ` licenses. -/
theorem setLIntegral_egf_eq (lam : Measure S) (Φ : Fin p → S ≃ᵐ S) (J : Fin p → S → ℝ≥0∞)
    (hJm : ∀ i, Measurable (J i)) (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i))
    {π : Kernel S S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π (fun i => Φ i) α)
    {fout : S → ℝ≥0∞} (hf : Measurable fout) {X Y : Set S} (hX : MeasurableSet X)
    (hY : MeasurableSet Y) :
    ∫⁻ x in X, π x Y ∂(lam.withDensity fout)
      = ∑ i, ∫⁻ s in Y, X.indicator 1 ((Φ i).symm s) * inflowTerm Φ α fout J i s ∂lam := by
  have hα := hπ.measurable_weight
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hf (π.measurable_coe hY) hX]
  simp only [Pi.mul_apply, hπ.apply_set _ hY, Finset.mul_sum]
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable fun x =>
      fout x * (ENNReal.ofReal (α i x) * Y.indicator 1 ((Φ i) x)) := fun i _ =>
    hf.mul ((ENNReal.measurable_ofReal.comp (hα i)).mul
      ((measurable_const.indicator hY).comp (Φ i).measurable))
  rw [lintegral_finsetSum _ hmeas]
  refine Finset.sum_congr rfl fun i _ => ?_
  set G : S → ℝ≥0∞ := fun s => X.indicator 1 ((Φ i).symm s) * ENNReal.ofReal (α i ((Φ i).symm s))
    * fout ((Φ i).symm s) * Y.indicator 1 s with hG
  have hGm : Measurable G :=
    (((measurable_const.indicator hX).comp (Φ i).symm.measurable).mul
      (ENNReal.measurable_ofReal.comp ((hα i).comp (Φ i).symm.measurable))).mul
      (hf.comp (Φ i).symm.measurable) |>.mul (measurable_const.indicator hY)
  have h1 : ∫⁻ x in X, fout x * (ENNReal.ofReal (α i x) * Y.indicator 1 (Φ i x)) ∂lam
      = ∫⁻ u, G (Φ i u) ∂lam := by
    rw [← lintegral_indicator hX]
    refine lintegral_congr fun u => ?_
    simp only [hG, MeasurableEquiv.symm_apply_apply]
    by_cases hu : u ∈ X <;> by_cases hv : (Φ i) u ∈ Y <;> simp [hu, hv, mul_comm]
  have h2 : ∫⁻ s in Y, X.indicator 1 ((Φ i).symm s) * inflowTerm Φ α fout J i s ∂lam
      = ∫⁻ s, J i s * G s ∂lam := by
    rw [← lintegral_indicator hY]
    refine lintegral_congr fun s => ?_
    simp only [hG, inflowTerm]
    by_cases hu : (Φ i).symm s ∈ X <;> by_cases hv : s ∈ Y <;>
      simp [hu, hv, mul_comm, mul_assoc]
  rw [h1, h2, lintegral_mul_jacobian (Φ i) (hJm i) (hJ i) hGm]


/-- **`F_in = f_in λ`** (`main.tex:737`, `:763–764`), when `Φᵢ₊λ = Jᵢ λ` for each `i`. -/
theorem inflow_eq_withDensity (lam : Measure S) (Φ : Fin p → S ≃ᵐ S) (J : Fin p → S → ℝ≥0∞)
    (hJm : ∀ i, Measurable (J i)) (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i))
    {π : Kernel S S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π (fun i => Φ i) α)
    {fout : S → ℝ≥0∞} (hf : Measurable fout) :
    inflow π (lam.withDensity fout) = lam.withDensity (inflowDensity Φ α fout J) := by
  ext Y hY
  rw [inflow, Measure.bind_apply hY π.aemeasurable, ← setLIntegral_univ,
    setLIntegral_egf_eq lam Φ J hJm hJ hπ hf MeasurableSet.univ hY, withDensity_apply _ hY]
  unfold inflowDensity
  rw [lintegral_finsetSum _ fun i _ => measurable_inflowTerm Φ hπ.measurable_weight hf hJm i]
  simp

/-- `f_in(s) βⁱ(s) = (αⁱ f_out)∘Φᵢ⁻¹(s) Jᵢ(s)` wherever `f_in(s) < ∞`. -/
theorem inflowDensity_mul_backwardWeight (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ)
    (fout : S → ℝ≥0∞) (J : Fin p → S → ℝ≥0∞) (i : Fin p) {s : S}
    (hs : inflowDensity Φ α fout J s ≠ ∞) :
    inflowDensity Φ α fout J s * ENNReal.ofReal (backwardWeight Φ α fout J i s)
      = inflowTerm Φ α fout J i s := by
  have hle : inflowTerm Φ α fout J i s ≤ inflowDensity Φ α fout J s :=
    Finset.single_le_sum (f := fun j => inflowTerm Φ α fout J j s) (fun _ _ => zero_le)
      (Finset.mem_univ i)
  by_cases h0 : inflowDensity Φ α fout J s = 0
  · rw [h0, zero_mul]; exact (le_antisymm (hle.trans h0.le) zero_le).symm
  · have hne : inflowTerm Φ α fout J i s / inflowDensity Φ α fout J s ≠ ∞ :=
      ENNReal.div_ne_top (ne_top_of_le_ne_top hs hle) h0
    rw [backwardWeight, ENNReal.ofReal_toReal hne, ENNReal.mul_div_cancel h0 hs]

/-- `∑ᵢ βⁱ(s) = 1` wherever `0 < f_in(s) < ∞`. -/
theorem sum_backwardWeight (Φ : Fin p → S ≃ᵐ S) (α : Fin p → S → ℝ) (fout : S → ℝ≥0∞)
    (J : Fin p → S → ℝ≥0∞) {s : S} (h0 : inflowDensity Φ α fout J s ≠ 0)
    (hs : inflowDensity Φ α fout J s ≠ ∞) : ∑ i, backwardWeight Φ α fout J i s = 1 := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      inflowTerm Φ α fout J i s / inflowDensity Φ α fout J s ≠ ∞ := fun i _ =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top hs (Finset.single_le_sum
      (f := fun j => inflowTerm Φ α fout J j s) (fun _ _ => zero_le) (Finset.mem_univ i))) h0
  simp only [backwardWeight]
  rw [← ENNReal.toReal_sum hne]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change (inflowDensity Φ α fout J s * (inflowDensity Φ α fout J s)⁻¹).toReal = 1
  rw [ENNReal.mul_inv_cancel h0 hs, ENNReal.toReal_one]

theorem backwardKernel_apply_set (Φ : Fin p → S ≃ᵐ S) {α : Fin p → S → ℝ} {fout : S → ℝ≥0∞}
    {J : Fin p → S → ℝ≥0∞} (hα : ∀ i, Measurable (α i)) (hf : Measurable fout)
    (hJ : ∀ i, Measurable (J i)) (s : S) {X : Set S} (hX : MeasurableSet X) :
    backwardKernel Φ α fout J hα hf hJ s X
      = ∑ i, ENNReal.ofReal (backwardWeight Φ α fout J i s) * X.indicator 1 ((Φ i).symm s) :=
  egfKernel_apply_set _ _ s hX

/-- `f_in < ∞`, `λ`-a.e.: `∫ f_in dλ = F_in(𝒮) = F_out(𝒮) < ∞`. -/
theorem ae_inflowDensity_lt_top (lam : Measure S) (Φ : Fin p → S ≃ᵐ S) (J : Fin p → S → ℝ≥0∞)
    (hJm : ∀ i, Measurable (J i)) (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i))
    {π : Kernel S S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π (fun i => Φ i) α)
    {fout : S → ℝ≥0∞} (hf : Measurable fout) [IsFiniteMeasure (lam.withDensity fout)] :
    ∀ᵐ s ∂lam, inflowDensity Φ α fout J s < ∞ := by
  haveI := hπ.isMarkovKernel
  refine ae_lt_top (measurable_inflowDensity Φ hπ.measurable_weight hf hJm) ?_
  have : ∫⁻ s, inflowDensity Φ α fout J s ∂lam = inflow π (lam.withDensity fout) univ := by
    rw [inflow_eq_withDensity lam Φ J hJm hJ hπ hf, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  rw [this]; exact measure_ne_top _ _

/-- **The printed kernel is a backward policy** (`main.tex:747–764`), when `Φᵢ₊λ = Jᵢ λ`. -/
theorem isBackwardPolicy_backwardKernel (lam : Measure S) (Φ : Fin p → S ≃ᵐ S)
    (J : Fin p → S → ℝ≥0∞) (hJm : ∀ i, Measurable (J i))
    (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i))
    {π : Kernel S S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π (fun i => Φ i) α)
    {fout : S → ℝ≥0∞} (hf : Measurable fout) [IsFiniteMeasure (lam.withDensity fout)] :
    IsBackwardPolicy π (lam.withDensity fout)
      (backwardKernel Φ α fout J hπ.measurable_weight hf hJm) := by
  have hα := hπ.measurable_weight
  have hfinm := measurable_inflowDensity Φ hα hf hJm
  have hlt := ae_inflowDensity_lt_top lam Φ J hJm hJ hπ hf
  intro X Y hX hY
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin p)), Measurable fun s =>
      X.indicator 1 ((Φ i).symm s) * inflowTerm Φ α fout J i s := fun i _ =>
    ((measurable_const.indicator hX).comp (Φ i).symm.measurable).mul
      (measurable_inflowTerm Φ hα hf hJm i)
  rw [setLIntegral_egf_eq lam Φ J hJm hJ hπ hf hX hY, inflow_eq_withDensity lam Φ J hJm hJ hπ hf,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hfinm
      ((backwardKernel Φ α fout J hα hf hJm).measurable_coe hX) hY,
    ← lintegral_finsetSum _ hmeas]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hlt] with s hs
  simp only [Pi.mul_apply, backwardKernel_apply_set Φ hα hf hJm s hX, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, inflowDensity_mul_backwardWeight Φ α fout J i hs.ne, mul_comm]

/-- `theo:backward_policy`, **general form** (unbundled): on any measurable space, for any measure
`λ`, measurable bijections `Φᵢ` and Jacobian factors `Jᵢ` with `Φᵢ₊λ = Jᵢ λ` (`Jᵢ` is the Jacobian
of `Φᵢ⁻¹` relative to `λ`; this is the change of variables of `main.tex:754`), a forward policy
`π(s) = ∑ᵢ αⁱ(s) δ_{Φᵢ(s)}` and a finite `F_out = f_out λ`:
1. `F_in = f_in λ` with the printed `f_in` (`main.tex:737`);
2. the printed `B(s) = ∑ᵢ βⁱ(s) δ_{Φᵢ⁻¹(s)}` is a backward star policy (`main.tex:735–736`);
3. its weights sum to `1`, `F_in`-a.e.: it is a policy;
4. every backward star policy agrees with it setwise, `F_in`-a.e.: it is *the* backward policy. -/
theorem backward_policy_of_map_eq (lam : Measure S) (Φ : Fin p → S ≃ᵐ S) (J : Fin p → S → ℝ≥0∞)
    (hJm : ∀ i, Measurable (J i)) (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i))
    {π : Kernel S S} {α : Fin p → S → ℝ} (hπ : IsEGFPolicy π (fun i => Φ i) α)
    {fout : S → ℝ≥0∞} (hf : Measurable fout) [IsFiniteMeasure (lam.withDensity fout)] :
    inflow π (lam.withDensity fout) = lam.withDensity (inflowDensity Φ α fout J) ∧
    IsBackwardPolicy π (lam.withDensity fout)
      (backwardKernel Φ α fout J hπ.measurable_weight hf hJm) ∧
    (∀ᵐ s ∂(inflow π (lam.withDensity fout)), ∑ i, backwardWeight Φ α fout J i s = 1) ∧
    ∀ B : Kernel S S, IsBackwardPolicy π (lam.withDensity fout) B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow π (lam.withDensity fout)]
        fun s => backwardKernel Φ α fout J hπ.measurable_weight hf hJm s X := by
  haveI := hπ.isMarkovKernel
  have hinf := inflow_eq_withDensity lam Φ J hJm hJ hπ hf
  have hBP := isBackwardPolicy_backwardKernel lam Φ J hJm hJ hπ hf
  refine ⟨hinf, hBP, ?_, fun B hB X hX => hB.ae_eq_apply hBP hX⟩
  rw [hinf, ae_withDensity_iff (measurable_inflowDensity Φ hπ.measurable_weight hf hJm)]
  filter_upwards [ae_inflowDensity_lt_top lam Φ J hJm hJ hπ hf] with s hs h0
  exact sum_backwardWeight Φ α fout J h0 hs.ne

/-! ## The theorem -/

/-- `theo:backward_policy`, **principal form**: the four conclusions of `backward_policy_of_map_eq`
for a generative flow `F` (`main.tex:161`) whose forward policy is `π(s) = ∑ᵢ αⁱ(s) δ_{Φᵢ(s)}` and
whose outflow is `F_out = f_out λ` (`main.tex:731–732`), under `Φᵢ₊λ = Jᵢ λ`. No ergodicity is
assumed (`def:egf`'s clause is not used). -/
theorem backward_policy (lam : Measure S) (F : GenerativeFlow S) (Φ : Fin p → S ≃ᵐ S)
    (J : Fin p → S → ℝ≥0∞) (hJm : ∀ i, Measurable (J i))
    (hJ : ∀ i, lam.map (Φ i) = lam.withDensity (J i)) {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) :
    inflow F.policy F.outflow = lam.withDensity (inflowDensity Φ α fout J) ∧
    IsBackwardPolicy F.policy F.outflow
      (backwardKernel Φ α fout J hπ.measurable_weight hf hJm) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow), ∑ i, backwardWeight Φ α fout J i s = 1) ∧
    ∀ B : Kernel S S, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel Φ α fout J hπ.measurable_weight hf hJm s X := by
  haveI : IsFiniteMeasure (lam.withDensity fout) := hout ▸ F.isFiniteMeasure_outflow
  rw [hout]
  exact backward_policy_of_map_eq lam Φ J hJm hJ hπ hf

/-- `theo:backward_policy` **with `|J_s Φᵢ⁻¹|` read as the Jacobian of `Φᵢ⁻¹` relative to `λ`**,
`d(Φᵢ₊λ)/dλ`, for a σ-finite `λ` quasi-invariant under the `Φᵢ` (`Φᵢ₊λ ≪ λ`). -/
theorem backward_policy_rnDeriv (lam : Measure S) [SigmaFinite lam] (F : GenerativeFlow S)
    (Φ : Fin p → S ≃ᵐ S) (hac : ∀ i, lam.map (Φ i) ≪ lam) {α : Fin p → S → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : S → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) :
    inflow F.policy F.outflow
        = lam.withDensity (inflowDensity Φ α fout fun i => (lam.map (Φ i)).rnDeriv lam) ∧
    IsBackwardPolicy F.policy F.outflow (backwardKernel Φ α fout
      (fun i => (lam.map (Φ i)).rnDeriv lam) hπ.measurable_weight hf
      fun _ => Measure.measurable_rnDeriv _ _) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow),
      ∑ i, backwardWeight Φ α fout (fun i => (lam.map (Φ i)).rnDeriv lam) i s = 1) ∧
    ∀ B : Kernel S S, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel Φ α fout (fun i => (lam.map (Φ i)).rnDeriv lam)
          hπ.measurable_weight hf (fun _ => Measure.measurable_rnDeriv _ _) s X := by
  refine backward_policy lam F Φ _ (fun _ => Measure.measurable_rnDeriv _ _) (fun i => ?_) hπ hf
    hout
  haveI : SigmaFinite (lam.map (Φ i)) := (Φ i).measurableEmbedding.sigmaFinite_map
  exact (Measure.withDensity_rnDeriv_eq _ _ (hac i)).symm

/-! ## On a finite-dimensional real vector space with a Haar (Lebesgue) measure -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The coordinate Jacobian** `|det J_s Φᵢ⁻¹|` (`main.tex:230`, `:233`): the absolute value of
the determinant of the derivative of `Φᵢ⁻¹` at `s`. -/
noncomputable def coordJac (Φ : Fin p → E ≃ᵐ E) (i : Fin p) (s : E) : ℝ≥0∞ :=
  ENNReal.ofReal |(fderiv ℝ (⇑(Φ i).symm) s).det|

theorem measurable_coordJac (Φ : Fin p → E ≃ᵐ E) (i : Fin p) : Measurable (coordJac Φ i) :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ _)))

/-- **Change of variables** (Mathlib's `map_withDensity_abs_det_fderiv_eq_addHaar`): for a Haar
measure `μ` and a measurable bijection `Φ` with differentiable inverse,
`Φ₊μ = |det D(Φ⁻¹)| μ`. -/
theorem map_eq_withDensity_abs_det (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E ≃ᵐ E)
    (hd : Differentiable ℝ Φ.symm) :
    μ.map Φ = μ.withDensity fun s => ENNReal.ofReal |(fderiv ℝ (⇑Φ.symm) s).det| := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar μ (s := univ) (f := Φ.symm)
    (f' := fderiv ℝ (⇑Φ.symm)) nullMeasurableSet_univ
    (fun x _ => (hd x).hasFDerivAt.hasFDerivWithinAt) Φ.symm.injective.injOn
  rw [Measure.restrict_univ, Set.image_univ, Φ.symm.surjective.range_eq,
    Measure.restrict_univ] at h
  conv_lhs => rw [← h]
  exact MeasurableEquiv.map_map_symm Φ

/-- `theo:backward_policy` **on `ℝᵈ` with Lebesgue measure** (the body's setting, `main.tex:225–234`),
for a Haar measure on any finite-dimensional real vector space and measurable bijections with
differentiable inverses: the formula with the coordinate Jacobian `|det J_s Φᵢ⁻¹|`. -/
theorem backward_policy_addHaar (μ : Measure E) [μ.IsAddHaarMeasure] (F : GenerativeFlow E)
    (Φ : Fin p → E ≃ᵐ E) (hd : ∀ i, Differentiable ℝ (Φ i).symm) {α : Fin p → E → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : E → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = μ.withDensity fout) :
    inflow F.policy F.outflow = μ.withDensity (inflowDensity Φ α fout (coordJac Φ)) ∧
    IsBackwardPolicy F.policy F.outflow
      (backwardKernel Φ α fout (coordJac Φ) hπ.measurable_weight hf (measurable_coordJac Φ)) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow), ∑ i, backwardWeight Φ α fout (coordJac Φ) i s = 1) ∧
    ∀ B : Kernel E E, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel Φ α fout (coordJac Φ) hπ.measurable_weight hf
          (measurable_coordJac Φ) s X :=
  backward_policy μ F Φ (coordJac Φ) (measurable_coordJac Φ)
    (fun i => map_eq_withDensity_abs_det μ (Φ i) (hd i)) hπ hf hout

/-- A measure equivalent to a Haar measure is quasi-invariant under a measurable bijection with
differentiable inverse: `Φ₊λ ≪ λ`. -/
theorem map_ac_of_equiv_addHaar (μ : Measure E) [μ.IsAddHaarMeasure] {lam : Measure E}
    (h1 : lam ≪ μ) (h2 : μ ≪ lam) (Φ : E ≃ᵐ E) (hd : Differentiable ℝ Φ.symm) :
    lam.map Φ ≪ lam := by
  have h := h1.map Φ.measurable
  rw [map_eq_withDensity_abs_det μ Φ hd] at h
  exact h.trans ((withDensity_absolutelyContinuous _ _).trans h2)

/-- `theo:backward_policy` **for a background measure equivalent to Lebesgue measure**, with
`|J_s Φᵢ⁻¹|` read as the Jacobian of `Φᵢ⁻¹` relative to `λ`, `d(Φᵢ₊λ)/dλ`. -/
theorem backward_policy_equiv_addHaar (μ : Measure E) [μ.IsAddHaarMeasure] (lam : Measure E)
    [SigmaFinite lam] (h1 : lam ≪ μ) (h2 : μ ≪ lam) (F : GenerativeFlow E) (Φ : Fin p → E ≃ᵐ E)
    (hd : ∀ i, Differentiable ℝ (Φ i).symm) {α : Fin p → E → ℝ}
    (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : E → ℝ≥0∞} (hf : Measurable fout)
    (hout : F.outflow = lam.withDensity fout) :
    inflow F.policy F.outflow
        = lam.withDensity (inflowDensity Φ α fout fun i => (lam.map (Φ i)).rnDeriv lam) ∧
    IsBackwardPolicy F.policy F.outflow (backwardKernel Φ α fout
      (fun i => (lam.map (Φ i)).rnDeriv lam) hπ.measurable_weight hf
      fun _ => Measure.measurable_rnDeriv _ _) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow),
      ∑ i, backwardWeight Φ α fout (fun i => (lam.map (Φ i)).rnDeriv lam) i s = 1) ∧
    ∀ B : Kernel E E, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel Φ α fout (fun i => (lam.map (Φ i)).rnDeriv lam)
          hπ.measurable_weight hf (fun _ => Measure.measurable_rnDeriv _ _) s X :=
  backward_policy_rnDeriv lam F Φ (fun i => map_ac_of_equiv_addHaar μ h1 h2 (Φ i) (hd i)) hπ hf
    hout

/-- The diffeomorphisms `Φᵢ` as measurable equivalences (Borel σ-algebra). -/
noncomputable def diffeoEquiv {n : WithTop ℕ∞}
    (Φ : Fin p → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n) (i : Fin p) : E ≃ᵐ E :=
  (Φ i).toHomeomorph.toMeasurableEquiv

/-- `theo:backward_policy` **for diffeomorphisms of `ℝᵈ` with Lebesgue measure** (`main.tex:225–234`,
any finite-dimensional real vector space, any Haar measure, `Cⁿ` diffeomorphisms with `n ≥ 1`). -/
theorem backward_policy_diffeomorph {n : WithTop ℕ∞} (hn : n ≠ 0) (μ : Measure E)
    [μ.IsAddHaarMeasure] (F : GenerativeFlow E) (Φ : Fin p → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E n)
    {α : Fin p → E → ℝ} (hπ : IsEGFPolicy F.policy (fun i => Φ i) α) {fout : E → ℝ≥0∞}
    (hf : Measurable fout) (hout : F.outflow = μ.withDensity fout) :
    inflow F.policy F.outflow = μ.withDensity (inflowDensity (diffeoEquiv Φ) α fout
      (coordJac (diffeoEquiv Φ))) ∧
    IsBackwardPolicy F.policy F.outflow (backwardKernel (diffeoEquiv Φ) α fout
      (coordJac (diffeoEquiv Φ)) hπ.measurable_weight hf (measurable_coordJac _)) ∧
    (∀ᵐ s ∂(inflow F.policy F.outflow),
      ∑ i, backwardWeight (diffeoEquiv Φ) α fout (coordJac (diffeoEquiv Φ)) i s = 1) ∧
    ∀ B : Kernel E E, IsBackwardPolicy F.policy F.outflow B → ∀ X, MeasurableSet X →
      (fun s => B s X) =ᵐ[inflow F.policy F.outflow]
        fun s => backwardKernel (diffeoEquiv Φ) α fout (coordJac (diffeoEquiv Φ))
          hπ.measurable_weight hf (measurable_coordJac _) s X :=
  backward_policy_addHaar μ F (diffeoEquiv Φ) (fun i => (Φ i).symm.contDiff.differentiable hn)
    hπ hf hout

end Euclidean


/-! ## Counterexample: the coordinate Jacobian is wrong for `λ ≠` Lebesgue -/

section Counterexample

/-- The translations `x ↦ x + i`, `i ∈ {0, 1}`, of `ℝ` (diffeomorphisms; `Φ₀ = id`). -/
noncomputable def cxMap : Fin 2 → ℝ ≃ᵐ ℝ := fun i => MeasurableEquiv.addRight ((i : ℕ) : ℝ)

/-- The constant policy `α = (1/2, 1/2)`. -/
noncomputable def cxWeight : Fin 2 → ℝ → ℝ := fun _ _ => 1 / 2

/-- The star outflow density `f_out = 𝟙_{[-1, 1)}`. -/
noncomputable def cxOut : ℝ → ℝ≥0∞ := (Ico (-1 : ℝ) 1).indicator 1

theorem measurable_cxOut : Measurable cxOut := measurable_const.indicator measurableSet_Ico

theorem measurable_cxWeight (i : Fin 2) : Measurable (cxWeight i) := measurable_const

/-- The forward policy `π(s) = ½ δ_s + ½ δ_{s+1}`. -/
noncomputable def cxPolicy : Kernel ℝ ℝ :=
  egfKernel (fun i => cxMap i) cxWeight (fun i => (cxMap i).measurable) measurable_cxWeight

theorem isEGFPolicy_cxPolicy : IsEGFPolicy cxPolicy (fun i => cxMap i) cxWeight :=
  isEGFPolicy_egfKernel _ _ _ _ (fun _ _ => by norm_num [cxWeight])
    (fun _ => by norm_num [cxWeight, Fin.sum_univ_two])

theorem cxMap_symm_apply (i : Fin 2) (s : ℝ) : (cxMap i).symm s = s - ((i : ℕ) : ℝ) := by
  simp [cxMap, MeasurableEquiv.symm_addRight, sub_eq_add_neg]

theorem differentiable_cxMap_symm (i : Fin 2) : Differentiable ℝ (cxMap i).symm := by
  have : ⇑(cxMap i).symm = fun s => s - ((i : ℕ) : ℝ) := funext (cxMap_symm_apply i)
  rw [this]; fun_prop

/-- The coordinate Jacobian of a translation is `1`. -/
theorem coordJac_cxMap (i : Fin 2) (s : ℝ) : coordJac cxMap i s = 1 := by
  have : ⇑(cxMap i).symm = fun s => s - ((i : ℕ) : ℝ) := funext (cxMap_symm_apply i)
  simp [coordJac, this]

theorem ofReal_cxWeight (i : Fin 2) (s : ℝ) : ENNReal.ofReal (cxWeight i s) = 2⁻¹ := by
  simp [cxWeight, ENNReal.ofReal_inv_of_pos]

theorem cxPolicy_Ico (x : ℝ) : cxPolicy x (Ico 0 1)
    = 2⁻¹ * (Ico (0 : ℝ) 1).indicator 1 x + 2⁻¹ * (Ico (-1 : ℝ) 0).indicator 1 x := by
  rw [cxPolicy, egfKernel_apply_set _ _ x measurableSet_Ico, Fin.sum_univ_two]
  simp only [ofReal_cxWeight, cxMap, MeasurableEquiv.coe_addRight, Fin.val_zero, Fin.val_one,
    Nat.cast_zero, Nat.cast_one]
  congr 2
  · simp
  · by_cases h : x ∈ Ico (-1 : ℝ) 0
    · have h' : x + 1 ∈ Ico (0 : ℝ) 1 := by
        simp only [mem_Ico] at h ⊢; constructor <;> linarith
      simp [h, h']
    · have h' : x + 1 ∉ Ico (0 : ℝ) 1 := by
        simp only [mem_Ico, not_and_or, not_le, not_lt] at h ⊢
        rcases h with h | h
        · left; linarith
        · right; linarith
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

theorem cxOut_measure (lam : Measure ℝ) : lam.withDensity cxOut = lam.restrict (Ico (-1) 1) := by
  rw [cxOut, withDensity_indicator measurableSet_Ico, withDensity_one]

theorem cx_arith {a b : ℝ≥0∞} (ha : a ≠ ∞) (h : 2⁻¹ * a + 2⁻¹ * b = a) : b = a := by
  have h2 := congrArg (fun t => 2 * t) h
  simp only [mul_add, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    one_mul, two_mul] at h2
  exact (ENNReal.add_right_inj ha).1 h2

theorem cx_inflow_Ico (lam : Measure ℝ) :
    inflow cxPolicy (lam.withDensity cxOut) (Ico 0 1)
      = 2⁻¹ * lam (Ico 0 1) + 2⁻¹ * lam (Ico (-1) 0) := by
  rw [inflow, Measure.bind_apply measurableSet_Ico cxPolicy.aemeasurable]
  simp only [cxPolicy_Ico]
  have hm : ∀ a b : ℝ, Measurable ((Ico a b).indicator (1 : ℝ → ℝ≥0∞)) := fun a b =>
    measurable_const.indicator measurableSet_Ico
  rw [lintegral_add_left ((hm 0 1).const_mul _), lintegral_const_mul _ (hm 0 1),
    lintegral_const_mul _ (hm (-1) 0),
    lintegral_indicator_one measurableSet_Ico, lintegral_indicator_one measurableSet_Ico,
    cxOut_measure, Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.2 (Ico_subset_Ico (by norm_num) le_rfl),
    inter_eq_left.2 (Ico_subset_Ico le_rfl (by norm_num))]

theorem cx_inflowTerm (i : Fin 2) {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    inflowTerm cxMap cxWeight cxOut (coordJac cxMap) i y = 2⁻¹ := by
  rw [inflowTerm, ofReal_cxWeight, coordJac_cxMap, cxMap_symm_apply, mul_one]
  have : y - ((i : ℕ) : ℝ) ∈ Ico (-1 : ℝ) 1 := by
    simp only [mem_Ico] at hy ⊢
    have hi : ((i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith
  simp [cxOut, this]

theorem cx_inflowDensity {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    inflowDensity cxMap cxWeight cxOut (coordJac cxMap) y = 1 := by
  rw [inflowDensity, Fin.sum_univ_two, cx_inflowTerm 0 hy, cx_inflowTerm 1 hy,
    ENNReal.inv_two_add_inv_two]

theorem cx_backwardKernel_Ico {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    backwardKernel cxMap cxWeight cxOut (coordJac cxMap) measurable_cxWeight measurable_cxOut
      (measurable_coordJac cxMap) y (Ico 0 1) = 2⁻¹ := by
  rw [backwardKernel_apply_set _ _ _ _ _ measurableSet_Ico, Fin.sum_univ_two]
  simp only [backwardWeight, cx_inflowTerm _ hy, cx_inflowDensity hy, div_one, cxMap_symm_apply]
  have h0 : y - ((((0 : Fin 2) : ℕ) : ℝ)) ∈ Ico (0 : ℝ) 1 := by simpa using hy
  have h1 : y - ((((1 : Fin 2) : ℕ) : ℝ)) ∉ Ico (0 : ℝ) 1 := by
    simp only [mem_Ico] at hy ⊢; simp; intro; linarith
  rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
  simp

theorem cx_withDensity_Ico (lam : Measure ℝ) :
    lam.withDensity cxOut (Ico 0 1) = lam (Ico 0 1) := by
  rw [cxOut_measure, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.2 (Ico_subset_Ico (by norm_num) le_rfl)]

/-- **Counterexample, generic form.** On `ℝ`, for any `λ` with `λ[0,1) < ∞` and
`λ[-1,0) ≠ λ[0,1)`, the printed formulas with the coordinate Jacobian `|det J_s Φᵢ⁻¹|` give neither
the star inflow nor a backward policy, for `Φ = (x ↦ x, x ↦ x + 1)`, `α = (½, ½)`,
`f_out = 𝟙_{[-1,1)}`. -/
theorem cx_printed_formula_false (lam : Measure ℝ) (ha : lam (Ico 0 1) ≠ ∞)
    (hab : lam (Ico (-1) 0) ≠ lam (Ico 0 1)) :
    inflow cxPolicy (lam.withDensity cxOut)
        ≠ lam.withDensity (inflowDensity cxMap cxWeight cxOut (coordJac cxMap)) ∧
    ¬ IsBackwardPolicy cxPolicy (lam.withDensity cxOut)
        (backwardKernel cxMap cxWeight cxOut (coordJac cxMap) measurable_cxWeight
          measurable_cxOut (measurable_coordJac cxMap)) := by
  constructor
  · intro h
    have h1 := congrArg (fun m : Measure ℝ => m (Ico 0 1)) h
    rw [cx_inflow_Ico, withDensity_apply _ measurableSet_Ico,
      setLIntegral_congr_fun measurableSet_Ico (fun y hy => cx_inflowDensity hy),
      setLIntegral_const, one_mul] at h1
    exact hab (cx_arith ha h1)
  · intro h
    have h1 := h (Ico 0 1) (Ico 0 1) measurableSet_Ico measurableSet_Ico
    have hR : EqOn (fun x => cxPolicy x (Ico 0 1)) (fun _ => 2⁻¹) (Ico 0 1) := by
      intro x hx
      have hx' : x ∉ Ico (-1 : ℝ) 0 := fun h' => by
        simp only [mem_Ico] at hx h'; linarith
      simp only [cxPolicy_Ico, Set.indicator_of_mem hx, Set.indicator_of_notMem hx',
        Pi.one_apply, mul_one, mul_zero, add_zero]
    rw [setLIntegral_congr_fun measurableSet_Ico (fun y hy => cx_backwardKernel_Ico hy),
      setLIntegral_congr_fun measurableSet_Ico hR, setLIntegral_const, setLIntegral_const,
      cx_inflow_Ico, cx_withDensity_Ico,
      ENNReal.mul_right_inj (by norm_num) (by norm_num)] at h1
    exact hab (cx_arith ha h1)

/-- **The background measure of the counterexample**: density `1` on `[-1, 0)`, `2` on `[0, 1)`
and `e^{-x²}` off `[-1, 1)`. It is finite and equivalent to Lebesgue measure. -/
noncomputable def lamCx : Measure ℝ :=
  volume.restrict (Ico (-1) 1) + volume.restrict (Ico 0 1)
    + (volume.restrict (Ico (-1) 1)ᶜ).withDensity fun x => ENNReal.ofReal (Real.exp (-1 * x ^ 2))

theorem lamCx_apply_of_subset {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ico (-1) 1) :
    lamCx A = volume A + volume (A ∩ Ico 0 1) := by
  have h3 : ((volume.restrict (Ico (-1 : ℝ) 1)ᶜ).withDensity
      fun x => ENNReal.ofReal (Real.exp (-1 * x ^ 2))) A = 0 := by
    rw [withDensity_apply _ hA, Measure.restrict_restrict hA,
      Set.disjoint_iff_inter_eq_empty.1 (disjoint_compl_right.mono_left hsub)]
    simp
  rw [lamCx, Measure.add_apply, Measure.add_apply, h3, add_zero, Measure.restrict_apply hA,
    Measure.restrict_apply hA, inter_eq_left.2 hsub]

theorem lamCx_Ico_zero_one : lamCx (Ico 0 1) = 2 := by
  rw [lamCx_apply_of_subset measurableSet_Ico (Ico_subset_Ico (by norm_num) le_rfl),
    Set.inter_self, Real.volume_Ico]
  norm_num [one_add_one_eq_two]

theorem lamCx_Ico_neg_one_zero : lamCx (Ico (-1) 0) = 1 := by
  rw [lamCx_apply_of_subset measurableSet_Ico (Ico_subset_Ico le_rfl (by norm_num)),
    Set.Ico_inter_Ico, Real.volume_Ico]
  norm_num

instance isFiniteMeasure_lamCx : IsFiniteMeasure lamCx := by
  have h1 : IsFiniteMeasure (volume.restrict (Ico (-1 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have h2 : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  have h3 : IsFiniteMeasure ((volume.restrict (Ico (-1 : ℝ) 1)ᶜ).withDensity
      fun x => ENNReal.ofReal (Real.exp (-1 * x ^ 2))) :=
    isFiniteMeasure_withDensity_ofReal
      (integrable_exp_neg_mul_sq one_pos).restrict.hasFiniteIntegral
  unfold lamCx; infer_instance

theorem lamCx_ac_volume : lamCx ≪ volume := by
  have hr : ∀ s : Set ℝ, volume.restrict s ≪ volume := fun s =>
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  exact ((hr _).add_left (hr _)).add_left ((withDensity_absolutelyContinuous _ _).trans (hr _))

theorem volume_ac_lamCx : volume ≪ lamCx := by
  rw [← Measure.restrict_add_restrict_compl (μ := volume) (measurableSet_Ico (a := (-1 : ℝ)) (b := 1))]
  refine Measure.AbsolutelyContinuous.add_left ?_ ?_
  · exact Measure.absolutelyContinuous_of_le (Measure.le_add_right (Measure.le_add_right le_rfl))
  · refine (withDensity_absolutelyContinuous' (f := fun x => ENNReal.ofReal (Real.exp (-1 * x ^ 2)))
      (by fun_prop) (Filter.Eventually.of_forall fun x => by simp [Real.exp_pos])).trans ?_
    exact Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

/-- The generative flow of the counterexample: `π(s) = ½ δ_s + ½ δ_{s+1}`, `F_out = 𝟙_{[-1,1)} λ`. -/
noncomputable def cxFlow : GenerativeFlow ℝ where
  policy := cxPolicy
  outflow := lamCx.withDensity cxOut
  isMarkovKernel_policy := isEGFPolicy_cxPolicy.isMarkovKernel
  isFiniteMeasure_outflow := by rw [cxOut_measure]; infer_instance

/-- **Finding** (`theo:backward_policy`, `main.tex:731–739`). Read with the coordinate Jacobian
`|det J_s Φᵢ⁻¹|` (the matrix of `main.tex:230`), the printed statement is false for a background
measure `λ ≪` Lebesgue: on the manifold `ℝ`, with the finite `λ = lamCx` (equivalent to Lebesgue
measure), the translations `Φ₀ = id`, `Φ₁ = (· + 1)`, `α = (½, ½)` and `f_out = 𝟙_{[-1,1)}`, the
printed `f_in` is not the density of `F_in = F_out π` and the printed kernel is not a backward
policy. -/
theorem printed_backward_policy_false :
    IsFiniteMeasure lamCx ∧ lamCx ≪ volume ∧ volume ≪ lamCx ∧
    IsEGFPolicy cxFlow.policy (fun i => cxMap i) cxWeight ∧
    cxFlow.outflow = lamCx.withDensity cxOut ∧ (∀ i, Differentiable ℝ (cxMap i).symm) ∧
    inflow cxFlow.policy cxFlow.outflow
        ≠ lamCx.withDensity (inflowDensity cxMap cxWeight cxOut (coordJac cxMap)) ∧
    ¬ IsBackwardPolicy cxFlow.policy cxFlow.outflow
        (backwardKernel cxMap cxWeight cxOut (coordJac cxMap) measurable_cxWeight
          measurable_cxOut (measurable_coordJac cxMap)) :=
  ⟨inferInstance, lamCx_ac_volume, volume_ac_lamCx, isEGFPolicy_cxPolicy, rfl,
    differentiable_cxMap_symm,
    cx_printed_formula_false lamCx (by rw [lamCx_Ico_zero_one]; simp)
      (by rw [lamCx_Ico_zero_one, lamCx_Ico_neg_one_zero]; norm_num)⟩

theorem map_cxMap_ac (i : Fin 2) : lamCx.map (cxMap i) ≪ lamCx := by
  have h := lamCx_ac_volume.map (cxMap i).measurable
  have hv : volume.map (cxMap i) = volume := by
    simp only [cxMap, MeasurableEquiv.coe_addRight]
    exact map_add_right_eq_self volume _
  rw [hv] at h
  exact h.trans volume_ac_lamCx

/-- On the same flow, the `λ`-Jacobian `d(Φᵢ₊λ)/dλ` gives the star inflow and a backward policy
(`backward_policy_rnDeriv`): the counterexample is about the reading of `|J_s Φᵢ⁻¹|`. -/
theorem cx_rnDeriv_reading :
    inflow cxFlow.policy cxFlow.outflow = lamCx.withDensity
        (inflowDensity cxMap cxWeight cxOut fun i => (lamCx.map (cxMap i)).rnDeriv lamCx) ∧
    IsBackwardPolicy cxFlow.policy cxFlow.outflow (backwardKernel cxMap cxWeight cxOut
      (fun i => (lamCx.map (cxMap i)).rnDeriv lamCx) measurable_cxWeight measurable_cxOut
      fun _ => Measure.measurable_rnDeriv _ _) :=
  let h := backward_policy_rnDeriv lamCx cxFlow cxMap map_cxMap_ac isEGFPolicy_cxPolicy
    measurable_cxOut rfl
  ⟨h.1, h.2.1⟩

/-- The same flow over Lebesgue measure: `F_out = 𝟙_{[-1,1)} · Lebesgue`. -/
noncomputable def cxFlowLeb : GenerativeFlow ℝ where
  policy := cxPolicy
  outflow := volume.withDensity cxOut
  isMarkovKernel_policy := isEGFPolicy_cxPolicy.isMarkovKernel
  isFiniteMeasure_outflow := by rw [cxOut_measure]; exact isFiniteMeasure_restrict.2 (by simp)

/-- Over Lebesgue measure the printed formula, with the coordinate Jacobian, is right
(`backward_policy_addHaar`): the hypotheses of the anchors are inhabited, and the counterexample
above is about the background measure. -/
theorem cx_lebesgue :
    inflow cxFlowLeb.policy cxFlowLeb.outflow
        = volume.withDensity (inflowDensity cxMap cxWeight cxOut (coordJac cxMap)) ∧
    IsBackwardPolicy cxFlowLeb.policy cxFlowLeb.outflow
      (backwardKernel cxMap cxWeight cxOut (coordJac cxMap) measurable_cxWeight
        measurable_cxOut (measurable_coordJac cxMap)) :=
  let h := backward_policy_addHaar volume cxFlowLeb cxMap differentiable_cxMap_symm
    isEGFPolicy_cxPolicy measurable_cxOut rfl
  ⟨h.1, h.2.1⟩

/-! ### Without quasi-invariance, `F_in` has no density -/

/-- `λ = 𝟙_{[0,1)} · Lebesgue`, finite and `≪` Lebesgue. -/
noncomputable def lamAc : Measure ℝ := volume.restrict (Ico 0 1)

/-- The single translation `x ↦ x + 1`. -/
noncomputable def acMap : Fin 1 → ℝ ≃ᵐ ℝ := fun _ => MeasurableEquiv.addRight 1

/-- The policy `α = 1`. -/
def acWeight : Fin 1 → ℝ → ℝ := fun _ _ => 1

/-- `π(s) = δ_{s+1}`. -/
noncomputable def acPolicy : Kernel ℝ ℝ :=
  egfKernel (fun i => acMap i) acWeight (fun i => (acMap i).measurable) fun _ => measurable_const

theorem isEGFPolicy_acPolicy : IsEGFPolicy acPolicy (fun i => acMap i) acWeight :=
  isEGFPolicy_egfKernel _ _ _ _ (fun _ _ => by norm_num [acWeight])
    (fun _ => by simp [acWeight])

/-- **Finding** (`theo:backward_policy`, `main.tex:731–732`). "`λ` absolutely continuous with respect to Lebesgue measure"
does not make `F_in = F_out π` absolutely continuous with respect to `λ`: for the finite
`λ = 𝟙_{[0,1)}·Lebesgue` on `ℝ`, the diffeomorphism `x ↦ x + 1` and `f_out = 1`, `F_in` charges
`[1, 2)`, a `λ`-null set. So `f_in = dF_in/dλ` does not exist and the printed formula for `f_in`
fails for every choice of the Jacobian factor `J`. -/
theorem printed_inflow_not_ac :
    IsFiniteMeasure lamAc ∧ lamAc ≪ volume ∧
    IsEGFPolicy acPolicy (fun i => acMap i) acWeight ∧ (∀ i, Differentiable ℝ (acMap i).symm) ∧
    ¬ inflow acPolicy (lamAc.withDensity 1) ≪ lamAc ∧
    ∀ J : Fin 1 → ℝ → ℝ≥0∞,
      inflow acPolicy (lamAc.withDensity 1) ≠ lamAc.withDensity (inflowDensity acMap acWeight 1 J) := by
  have hA : inflow acPolicy (lamAc.withDensity 1) (Ico 1 2) = 1 := by
    rw [withDensity_one, inflow, Measure.bind_apply measurableSet_Ico acPolicy.aemeasurable]
    have : ∀ x : ℝ, acPolicy x (Ico 1 2) = (Ico (0 : ℝ) 1).indicator 1 x := by
      intro x
      rw [acPolicy, egfKernel_apply_set _ _ x measurableSet_Ico, Fin.sum_univ_one]
      simp only [acWeight, ENNReal.ofReal_one, one_mul, acMap, MeasurableEquiv.coe_addRight]
      by_cases h : x ∈ Ico (0 : ℝ) 1
      · have h' : x + 1 ∈ Ico (1 : ℝ) 2 := by
          simp only [mem_Ico] at h ⊢; constructor <;> linarith
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h', Pi.one_apply, Pi.one_apply]
      · have h' : x + 1 ∉ Ico (1 : ℝ) 2 := by
          simp only [mem_Ico, not_and_or, not_le, not_lt] at h ⊢
          rcases h with h | h
          · left; linarith
          · right; linarith
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    simp only [this]
    rw [lintegral_indicator_one measurableSet_Ico, lamAc, Measure.restrict_apply measurableSet_Ico,
      Set.inter_self, Real.volume_Ico]
    norm_num
  have hB : lamAc (Ico 1 2) = 0 := by
    rw [lamAc, Measure.restrict_apply measurableSet_Ico, Set.Ico_inter_Ico]
    simp
  have hnac : ¬ inflow acPolicy (lamAc.withDensity 1) ≪ lamAc := fun h => by
    have := h hB
    rw [hA] at this
    exact one_ne_zero this
  refine ⟨isFiniteMeasure_restrict.2 (by simp),
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self, isEGFPolicy_acPolicy,
    fun _ => by simp [acMap, MeasurableEquiv.symm_addRight], hnac, fun J h => hnac ?_⟩
  rw [h]
  exact withDensity_absolutelyContinuous _ _

end Counterexample

end EGF
