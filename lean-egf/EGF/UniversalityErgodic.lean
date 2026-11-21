import EGF.UniversalFamily
import EGF.InflowNonsingular
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.Filter.CountableSeparatingOn
import Mathlib.Dynamics.Ergodic.AddCircleAdd

/-!
# Theorem B.1 without mixing: a fixed policy is ε-universal iff it is ergodic

`theo:universality_true` — `main.tex:775` (statement `main.tex:775–776`, proof `main.tex:778–804`).
Not marked here: the label is marked in `EGF/Universality.lean` (`EGF.main_universality`); this
file is the strengthening C-29 (`papers/egf/programme/corrections.toml`), see SCOPE.

> Let $(\Statespace,\lambda)$ be a measured Polish space and let $\ForwardPolicyStar$ be a Markov
> kernel acting on $\Statespace$. Assume that $\ForwardPolicyStar$ is ergodic on
> $(\Statespace,\lambda)$ with summable $L^2$-mixing coefficients, then for any probability distributions $\Finit,\Fterm \ll \lambda$ with density in
> $L^2(\lambda)$ and any $\varepsilon>0$, there exists $\foutstar\in L^2(\lambda)$ such that the
> generative flow $(\ForwardPolicyStar,\foutstar)$ from $\Finit$ to $\Fterm$ is such that
> $\delta\Finit(\Statespace)+\delta\Fterm(\Statespace)<\varepsilon$. (`main.tex:775–776`)

> In contrast, ergodicity alone ensures the convergence of $\varphi \pi^n$ in the much weaker
> Cesaro sense. (`main.tex:271`)

> Although ergodicity is easily achievable with a number of generators independent from the
> dimension (for instance on tori, one randomly initialized non-trainable translation is sufficient
> to ensure ergodicity), the technical assumption of $L^2$-mixing summability needed for
> universality is more subtle. (`main.tex:697`)

> Second, the $L^2$-mixing summability property is essential to ensure universality.
> (`main.tex:702`)

## What is proved

| | |
|---|---|
| `IsKernelErgodic`, `isKernelErgodic_congr` | `π(x, A) = 𝟙_A(x)` `μ`-a.e. ⇒ `A` null or conull (Walters' invariant sets); only the null sets of `μ` matter |
| `isKernelErgodic_deterministic`, `IsEGFPolicy.isKernelErgodic`, `isKernelErgodic_egfKernel_uniform` | inhabitants: an ergodic map; an EGF policy with positive weights and no common a.e.-invariant set of its moves; uniform weights `1/p` and measure-preserving moves (then also `μπ = μ`) |
| `universality_of_ergodic`, `isUniversalPolicy_of_ergodic` | **sufficiency**: `π` ergodic for a finite invariant `λ̂ ~ λ` ⇒ the conclusion of `main_universality`, verbatim, with no mixing |
| `two_le_errors_of_invariant_set`, `not_universal_of_not_ergodic`, `isKernelErgodic_of_isUniversalPolicy` | **necessity**, any Markov `π`, finite `λ`: an invariant `A`, `0 < λ(A) < λ(𝒮)`, gives `F_init, F_term` with bounded densities and defect `≥ 2` for every outflow `≪ λ` |
| `universal_iff_ergodic`, `isUniversalFamilyEps_fixedPolicyFamily_iff` | the equivalence for one policy, and for its family `{π} × L²₊(λ)` |
| `universality_of_ergodic_family`, `not_isUniversalFamilyEps_of_not_ergodic` | Theorem 3.4 with ergodicity for summable mixing (C-29, C-20), and its converse |
| `isKernelErgodic_of_tendsto`, `isKernelErgodic_of_isSummablyL2Mixing` | `γ₀ < ∞`, `γₙ → 0` (a fortiori summable mixing) imply ergodicity |
| `isUniversalPolicy_addCircle`, `Swap.isUniversalPolicy_policy` | non-mixing universal policies: one translation of infinite order of the circle; the swap of two points |
| `exists_tvMass_cesaro_lt_of_ergodic` | Cesàro mixing in total variation: `‖∑_{t<N}(μ₀ − μ₁)πᵗ‖_TV < Nη` (von Neumann) |
| `cesaroOutflow`, `tvMass_construction_cesaro`, `tvMass_smul_le` | the Cesàro-weighted Neumann outflow and its defect |
| `Markov.densityActionL2`, `Markov.norm_densityActionL2_le`, … | the density action `P h = d((hλ̂)π)/dλ̂` on `L²(λ̂)`, `‖P‖ ≤ 1` (ported from GFNBounds) |
| `Markov.ae_eq_const_of_densityAction_eq`, `Markov.tendsto_birkhoffAverage_densityActionL2` | fixed points of `P` are constant under ergodicity; Cesàro averages of `P` tend to `0` on mean-zero `L²(λ̂)` |

## Hypothesis checklist

| paper hypothesis (`main.tex:775`) | here (`universality_of_ergodic`) |
|---|---|
| `(𝒮, λ)` a measured Polish space, `λ` finite | ⚠ weakened: any `MeasurableSpace S`, `[IsFiniteMeasure lam]` |
| `π` a Markov kernel | ✓ `[IsMarkovKernel π]` |
| `π` ergodic on `(𝒮, λ)` | ✓ `IsKernelErgodic π lamHat` (equivalently `IsKernelErgodic π lam`, `isKernelErgodic_congr`), and necessary (`universal_iff_ergodic`) |
| summable `L²`-mixing coefficients | ⚠ weakened: dropped, keeping only the invariant `λ̂ ~ λ` of `def:summably_mixing`, ⚠ strengthened: `λ̂` finite (C-29's declared added hypothesis) |
| `F_init, F_term` probabilities `≪ λ`, densities in `L²(λ)` | ✓ probabilities `≪ λ`; ⚠ weakened: no `L²` densities |
| conclusion `∃ f_out ∈ L²(λ)`, `δF_init(𝒮) + δF_term(𝒮) < ε` | ✓ with `f_out ≥ 0` bounded, as in `main_universality` |

## SCOPE (disclosed)

No `sorry`; nothing is assumed beyond Mathlib. The label is not marked: its printed statement is
certified by `EGF.main_universality` (`EGF/Universality.lean`); this file proves the strengthening
C-29 (mixing replaced by ergodicity, ergodicity necessary), whose adoption is the author's. Reading
taken: "ergodic" is Walters' invariant sets for the kernel (`IsKernelErgodic`), relative to the
invariant `λ̂` of `def:summably_mixing`, which under `λ̂ ~ λ` is the same as relative to `λ`.
Necessity needs no invariant measure; sufficiency assumes the invariant `λ̂ ~ λ` finite (an
infinite `λ̂` with summable mixing forces a trivial `λ`, `EGF.trivial_of_lamHat_univ_eq_top`, but
whether finiteness can be dropped under ergodicity alone is not settled here). No theorem of this
file assumes mixing except `isKernelErgodic_of_tendsto` and `isKernelErgodic_of_isSummablyL2Mixing`,
which read `def:summably_mixing` as `EGF.Defs` does; the others do not depend on OQ-47. The
`Markov.*` block ports GFNBounds' density action (wave 0: copied, not imported; each ported
declaration names its source); four of its lemmas are original
(`ae_apply_eq_indicator_of_withDensity_invariant`, `ae_eq_const_of_densityAction_eq`,
`tendsto_birkhoffAverage_densityActionL2`, `densityAction_toReal_rnDeriv`). "Ergodic" here is
ergodicity for the finite invariant `λ̂ ~ λ`, not the topological ergodicity of `def:egf`
(`main.tex:221`, OQ-48), which does not imply it in general.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-! ## The density action of a Markov kernel on `L²(λ̂)` (ported from GFNBounds)

Verbatim copies of `GFNBounds.Core` declarations (wave 0, `kb/0001`): their docstrings are
GFNBounds' own, and "the paper" and the line citations in them refer to the GFNBounds sources
(`universality.tex`, `proofs.tex`), not to `main.tex`. `bind_add_measure` is `EGF`'s. -/

namespace Markov

variable {α : Type*} [MeasurableSpace α]

-- ported from GFNBounds.Core.integrable_of_Lp (lean/GFNBounds/Core/Flow.lean:135)
/-- An element of `L^p(ν)` is `ν`-integrable: `ν` is finite and `1 ≤ p`. -/
theorem integrable_of_Lp {ν : Measure α} [IsFiniteMeasure ν] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p ν) : Integrable (⇑f) ν :=
  (Lp.memLp f).integrable (Fact.out : (1 : ℝ≥0∞) ≤ p)

-- ported from GFNBounds.Core.bind_absolutelyContinuous_bind (lean/GFNBounds/Core/Kernel.lean:132)
/-- **A kernel push preserves domination**: `μ ≪ ν` implies `μ π⋆ ≪ ν π⋆`.

Mathlib has no lemma of this shape at `v4.31.0`, and it is the whole of what makes the density
action well defined. Nothing is asked of the kernel beyond measurability. -/
theorem bind_absolutelyContinuous_bind (κ : Kernel α α) {μ ν : Measure α} (h : μ ≪ ν) :
    μ.bind ⇑κ ≪ ν.bind ⇑κ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  have hm : Measurable fun x => κ x s := κ.measurable_coe hs
  rw [Measure.bind_apply hs (κ.aemeasurable (μ := ν)), lintegral_eq_zero_iff hm] at hs0
  rw [Measure.bind_apply hs (κ.aemeasurable (μ := μ)), lintegral_eq_zero_iff hm]
  exact h.ae_le hs0


-- ported from GFNBounds.Core.bind_withDensity_absolutelyContinuous (lean/GFNBounds/Core/Kernel.lean:151)
/-- **`(f ν) π⋆ ≪ ν`, from invariance alone.** This is the main text's "invariance makes the
density action `P⋆ f := d((f ν_B) π⋆)/dν_B` well defined on `L¹(ν_B)`"
(`universality.tex:26–27`), and it is a theorem, not a hypothesis. -/
theorem bind_withDensity_absolutelyContinuous (κ : Kernel α α) {ν : Measure α}
    (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) : (ν.withDensity f).bind ⇑κ ≪ ν := by
  have h := bind_absolutelyContinuous_bind κ (withDensity_absolutelyContinuous ν f)
  rwa [hinv] at h

-- ported from GFNBounds.Core.bind_withDensity_univ (lean/GFNBounds/Core/Kernel.lean:158)
/-- **The mass of `(f ν) π⋆` is the mass of `f ν`** — stochasticity of the kernel, and not
invariance of the measure. -/
theorem bind_withDensity_univ (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α) (f : α → ℝ≥0∞) :
    ((ν.withDensity f).bind ⇑κ) Set.univ = ∫⁻ x, f x ∂ν := by
  rw [Measure.bind_apply MeasurableSet.univ (κ.aemeasurable (μ := ν.withDensity f))]
  simp only [measure_univ]
  rw [lintegral_one, withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]

-- ported from GFNBounds.Core.isFiniteMeasure_bind_withDensity (lean/GFNBounds/Core/Kernel.lean:165)
/-- `(f ν) π⋆` is a finite measure as soon as `f` has finite `ν`-integral. -/
theorem isFiniteMeasure_bind_withDensity (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂ν ≠ ⊤) : IsFiniteMeasure ((ν.withDensity f).bind ⇑κ) :=
  ⟨by rw [bind_withDensity_univ κ ν f]; exact hf.lt_top⟩

/-! ## The density action on non-negative densities -/

-- ported from GFNBounds.Core.bindDensity (lean/GFNBounds/Core/Kernel.lean:174)
/-- **The density action `T f := d((f ν) π⋆)/dν`** of the main text (`universality.tex:26–27`),
on non-negative densities. It is well defined — that is, `(T f) ν = (f ν) π⋆` — as soon as `ν`
is `π⋆`-invariant; that is `withDensity_bindDensity`. -/
noncomputable def bindDensity (κ : Kernel α α) (ν : Measure α) (f : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  ((ν.withDensity f).bind ⇑κ).rnDeriv ν

-- ported from GFNBounds.Core.bindDensity_congr (lean/GFNBounds/Core/Kernel.lean:180)
/-- `T` depends on `f` only through its `ν`-a.e. class, and the dependence is by *equality* of
functions, not merely a.e. equality: `ν.withDensity` already forgets the null sets. This is what
makes `T` descend to `L^p(ν)` without a quotient argument. -/
theorem bindDensity_congr (κ : Kernel α α) (ν : Measure α) {f g : α → ℝ≥0∞} (h : f =ᵐ[ν] g) :
    bindDensity κ ν f = bindDensity κ ν g := by
  rw [bindDensity, bindDensity, withDensity_congr_ae h]

-- ported from GFNBounds.Core.measurable_bindDensity (lean/GFNBounds/Core/Kernel.lean:185)
/-- `T f` is measurable, with no hypothesis on `f`: a Radon–Nikodym derivative always is. -/
theorem measurable_bindDensity (κ : Kernel α α) (ν : Measure α) (f : α → ℝ≥0∞) :
    Measurable (bindDensity κ ν f) :=
  Measure.measurable_rnDeriv _ _

-- ported from GFNBounds.Core.withDensity_bindDensity (lean/GFNBounds/Core/Kernel.lean:193)
/-- **`T f` is a genuine density for `(f ν) π⋆`.** This is the well-definedness assertion of
`universality.tex:26–27`. Invariance is what it consumes, through absolute continuity; no
finiteness of `∫ f dν` is needed, the Lebesgue decomposition being available because the push of
a finite kernel is s-finite and `ν` is σ-finite. -/
theorem withDensity_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) :
    ν.withDensity (bindDensity κ ν f) = (ν.withDensity f).bind ⇑κ :=
  Measure.withDensity_rnDeriv_eq _ _ (bind_withDensity_absolutelyContinuous κ hinv f)

-- ported from GFNBounds.Core.lintegral_bindDensity (lean/GFNBounds/Core/Kernel.lean:201)
/-- **`∫ T f dν = ∫ f dν`** — the non-negative half of `hint`. It is stochasticity of `π⋆` that
is used here, each fibre `π⋆(x)` being a probability measure; invariance enters only through the
absolute continuity that makes `T f` a density at all. -/
theorem lintegral_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) (f : α → ℝ≥0∞) :
    ∫⁻ x, bindDensity κ ν f x ∂ν = ∫⁻ x, f x ∂ν := by
  calc ∫⁻ x, bindDensity κ ν f x ∂ν
      = (ν.withDensity (bindDensity κ ν f)) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = ((ν.withDensity f).bind ⇑κ) Set.univ := by rw [withDensity_bindDensity κ hinv f]
    _ = ∫⁻ x, f x ∂ν := bind_withDensity_univ κ ν f

-- ported from GFNBounds.Core.bindDensity_one (lean/GFNBounds/Core/Kernel.lean:212)
/-- **`T 𝟏 = 𝟏`** — the non-negative half of `hone`, and pure invariance: `𝟏 ν = ν`, so
`(𝟏 ν) π⋆ = ν π⋆ = ν` and `dν/dν = 𝟏`. -/
theorem bindDensity_one (κ : Kernel α α) {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) : bindDensity κ ν 1 =ᵐ[ν] 1 := by
  rw [bindDensity, withDensity_one, hinv]
  exact Measure.rnDeriv_self ν

-- ported from GFNBounds.Core.bindDensity_zero (lean/GFNBounds/Core/Kernel.lean:218)
/-- `T 0 = 0`: the zero density pushes to the zero measure. -/
theorem bindDensity_zero (κ : Kernel α α) (ν : Measure α) : bindDensity κ ν 0 =ᵐ[ν] 0 := by
  rw [bindDensity, withDensity_zero, Measure.bind_zero_left]
  exact Measure.rnDeriv_zero ν

-- ported from GFNBounds.Core.bindDensity_add (lean/GFNBounds/Core/Kernel.lean:223)
/-- **`T` is additive**, `ν`-a.e., on densities of finite integral. -/
theorem bindDensity_add (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hfi : ∫⁻ x, f x ∂ν ≠ ⊤)
    (hgi : ∫⁻ x, g x ∂ν ≠ ⊤) :
    bindDensity κ ν (f + g) =ᵐ[ν] bindDensity κ ν f + bindDensity κ ν g := by
  have hwd : ν.withDensity (f + g) = ν.withDensity f + ν.withDensity g := by
    have h1 : ν.withDensity (f + g) = ν.withDensity (hf.mk f + g) :=
      withDensity_congr_ae (hf.ae_eq_mk.add (Filter.EventuallyEq.refl _ g))
    have h2 : ν.withDensity (hf.mk f) = ν.withDensity f :=
      withDensity_congr_ae hf.ae_eq_mk.symm
    rw [h1, withDensity_add_left hf.measurable_mk g, h2]
  have hsplit : (ν.withDensity (f + g)).bind ⇑κ
      = (ν.withDensity f).bind ⇑κ + (ν.withDensity g).bind ⇑κ := by
    rw [hwd, bind_add_measure]
  haveI := isFiniteMeasure_bind_withDensity κ ν hfi
  haveI := isFiniteMeasure_bind_withDensity κ ν hgi
  rw [bindDensity, hsplit]
  exact Measure.rnDeriv_add _ _ _

-- ported from GFNBounds.Core.bindDensity_smul (lean/GFNBounds/Core/Kernel.lean:242)
/-- **`T` is positively homogeneous**, `ν`-a.e., for a finite scalar. -/
theorem bindDensity_smul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hfi : ∫⁻ x, f x ∂ν ≠ ⊤) :
    bindDensity κ ν (c • f) =ᵐ[ν] c • bindDensity κ ν f := by
  have hwd : ν.withDensity (c • f) = c • ν.withDensity f := by
    have h1 : ν.withDensity (c • f) = ν.withDensity (c • hf.mk f) :=
      withDensity_congr_ae (hf.ae_eq_mk.fun_comp (c • ·))
    have h2 : ν.withDensity (hf.mk f) = ν.withDensity f :=
      withDensity_congr_ae hf.ae_eq_mk.symm
    rw [h1, withDensity_smul c hf.measurable_mk, h2]
  have hsplit : (ν.withDensity (c • f)).bind ⇑κ = c • ((ν.withDensity f).bind ⇑κ) := by
    rw [hwd, Measure.bind_smul]
  haveI := isFiniteMeasure_bind_withDensity κ ν hfi
  rw [bindDensity, hsplit]
  exact Measure.rnDeriv_smul_left_of_ne_top _ _ hc

/-! ## The density action on signed densities -/

-- ported from GFNBounds.Core.densityAction (lean/GFNBounds/Core/Kernel.lean:264)
/-- **The density action `P⋆ f := d((f ν) π⋆)/dν` on signed densities.** A signed density is
split into its positive and negative parts, each pushed by `T = bindDensity`, and the two
densities subtracted. Nothing here supposes `f` integrable or even measurable — the statements
that need it say so. -/
noncomputable def densityAction (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) : α → ℝ :=
  fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
    - (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal

-- ported from GFNBounds.Core.densityAction_congr (lean/GFNBounds/Core/Kernel.lean:270)
/-- `P⋆` depends on `f` only through its `ν`-a.e. class, and by *equality* of functions. This is
what lets it descend to `L^p(ν)`. -/
theorem densityAction_congr (κ : Kernel α α) (ν : Measure α) {f g : α → ℝ} (h : f =ᵐ[ν] g) :
    densityAction κ ν f = densityAction κ ν g := by
  have h1 : (fun y => ENNReal.ofReal (f y)) =ᵐ[ν] fun y => ENNReal.ofReal (g y) := by
    filter_upwards [h] with x hx; rw [hx]
  have h2 : (fun y => ENNReal.ofReal (-f y)) =ᵐ[ν] fun y => ENNReal.ofReal (-g y) := by
    filter_upwards [h] with x hx; rw [hx]
  have e1 := bindDensity_congr κ ν h1
  have e2 := bindDensity_congr κ ν h2
  funext x
  simp only [densityAction, e1, e2]

-- ported from GFNBounds.Core.measurable_densityAction (lean/GFNBounds/Core/Kernel.lean:282)
/-- `P⋆ f` is measurable, with no hypothesis on `f`. -/
theorem measurable_densityAction (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) :
    Measurable (densityAction κ ν f) :=
  ((measurable_bindDensity κ ν _).ennreal_toReal).sub
    ((measurable_bindDensity κ ν _).ennreal_toReal)

-- ported from GFNBounds.Core.lintegral_ofReal_ne_top (lean/GFNBounds/Core/Kernel.lean:288)
/-- The positive part of an integrable function has finite `ν`-integral. -/
theorem lintegral_ofReal_ne_top {ν : Measure α} {f : α → ℝ} (hf : Integrable f ν) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

-- ported from GFNBounds.Core.bindDensity_ofReal_lt_top (lean/GFNBounds/Core/Kernel.lean:295)
/-- `T f⁺` has finite `ν`-integral, hence is a.e. finite. -/
theorem bindDensity_ofReal_lt_top (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x < ⊤ :=
  ae_lt_top (measurable_bindDensity κ ν _)
    (by rw [lintegral_bindDensity κ hinv]; exact lintegral_ofReal_ne_top hf)

-- ported from GFNBounds.Core.integrable_toReal_bindDensity (lean/GFNBounds/Core/Kernel.lean:302)
/-- `(T f⁺).toReal` is `ν`-integrable, with `∫ (T f⁺).toReal dν = ∫ f⁺ dν`. -/
theorem integrable_toReal_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (measurable_bindDensity κ ν _).aemeasurable
    (by rw [lintegral_bindDensity κ hinv]; exact lintegral_ofReal_ne_top hf)

-- ported from GFNBounds.Core.integral_toReal_bindDensity (lean/GFNBounds/Core/Kernel.lean:308)
theorem integral_toReal_bindDensity (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, (bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal ∂ν
      = (∫⁻ x, ENNReal.ofReal (f x) ∂ν).toReal := by
  rw [integral_toReal (measurable_bindDensity κ ν _).aemeasurable
      (bindDensity_ofReal_lt_top κ hinv hf), lintegral_bindDensity κ hinv]

-- ported from GFNBounds.Core.integral_densityAction (lean/GFNBounds/Core/Kernel.lean:320)
/-- **`hint`, in the paper's own terms**: `∫ P⋆ f dν = ∫ f dν` for every `ν`-integrable `f`.

Stochasticity of `π⋆` is what is used — each fibre `π⋆(x)` is a probability measure, so the push
`(f ν) π⋆` has the mass of `f ν`. Invariance enters only through the absolute continuity that
makes `P⋆ f` a density. -/
theorem integral_densityAction (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∫ x, densityAction κ ν f x ∂ν = ∫ x, f x ∂ν := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  simp only [densityAction]
  rw [integral_sub (integrable_toReal_bindDensity κ hinv hf)
      (integrable_toReal_bindDensity κ hinv hfn),
    integral_toReal_bindDensity κ hinv hf, integral_toReal_bindDensity κ hinv hfn]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

-- ported from GFNBounds.Core.densityAction_one (lean/GFNBounds/Core/Kernel.lean:332)
/-- **`hone`**: `P⋆ 𝟏 = 𝟏` a.e. This is pure invariance — `𝟏 ν = ν`, so `(𝟏 ν) π⋆ = ν` and its
`ν`-density is `𝟏`; the negative part is the zero density and contributes nothing. -/
theorem densityAction_one (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) : densityAction κ ν 1 =ᵐ[ν] 1 := by
  have h1 : (fun y : α => ENNReal.ofReal ((1 : α → ℝ) y)) = 1 := by
    funext y; simp
  have h0 : (fun y : α => ENNReal.ofReal (-(1 : α → ℝ) y)) = 0 := by
    funext y; simp
  filter_upwards [bindDensity_one κ (ν := ν) hinv, bindDensity_zero κ ν] with x hx1 hx0
  simp only [densityAction, h1, h0]
  rw [hx1, hx0]
  simp

/-! ## Linearity -/

-- ported from GFNBounds.Core.max_add_aux (lean/GFNBounds/Core/Kernel.lean:346)
/-- The real identity behind additivity of `P⋆`: `(u+v)⁺ + u⁻ + v⁻ = (u+v)⁻ + u⁺ + v⁺`. -/
theorem max_add_aux (u v : ℝ) :
    max (u + v) 0 + max (-u) 0 + max (-v) 0 = max (-(u + v)) 0 + max u 0 + max v 0 := by
  have h : ∀ x : ℝ, max x 0 - max (-x) 0 = x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ (0 : ℝ))]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith : (0 : ℝ) ≤ -x)]; ring
  have h1 := h (u + v)
  have h2 := h u
  have h3 := h v
  linarith

-- ported from GFNBounds.Core.ofReal_add_aux (lean/GFNBounds/Core/Kernel.lean:359)
/-- The same identity in `ℝ≥0∞`, which is where `T` consumes it. -/
theorem ofReal_add_aux (u v : ℝ) :
    ENNReal.ofReal (u + v) + ENNReal.ofReal (-u) + ENNReal.ofReal (-v)
      = ENNReal.ofReal (-(u + v)) + ENNReal.ofReal u + ENNReal.ofReal v := by
  have e : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx]
    · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
  rw [e (u + v), e (-u), e (-v), e (-(u + v)), e u, e v,
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), max_add_aux u v]

-- ported from GFNBounds.Core.lintegral_add_ne_top (lean/GFNBounds/Core/Kernel.lean:374)
/-- `∫ (u + v) dν` is finite when both summands are. -/
theorem lintegral_add_ne_top {ν : Measure α} {u v : α → ℝ≥0∞} (hu : AEMeasurable u ν)
    (hun : ∫⁻ x, u x ∂ν ≠ ⊤) (hvn : ∫⁻ x, v x ∂ν ≠ ⊤) : ∫⁻ x, (u + v) x ∂ν ≠ ⊤ := by
  simp only [Pi.add_apply]
  rw [lintegral_add_left' hu]
  exact ENNReal.add_ne_top.2 ⟨hun, hvn⟩

-- ported from GFNBounds.Core.bindDensity_add₃ (lean/GFNBounds/Core/Kernel.lean:381)
/-- `T` on a sum of three densities of finite integral. -/
theorem bindDensity_add₃ (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    {u v w : α → ℝ≥0∞} (hu : AEMeasurable u ν) (hv : AEMeasurable v ν)
    (hun : ∫⁻ x, u x ∂ν ≠ ⊤) (hvn : ∫⁻ x, v x ∂ν ≠ ⊤) (hwn : ∫⁻ x, w x ∂ν ≠ ⊤) :
    bindDensity κ ν (u + v + w)
      =ᵐ[ν] bindDensity κ ν u + bindDensity κ ν v + bindDensity κ ν w := by
  have h1 : bindDensity κ ν (u + v + w) =ᵐ[ν] bindDensity κ ν (u + v) + bindDensity κ ν w :=
    bindDensity_add κ (hu.add hv) (lintegral_add_ne_top hu hun hvn) hwn
  have h2 : bindDensity κ ν (u + v) =ᵐ[ν] bindDensity κ ν u + bindDensity κ ν v :=
    bindDensity_add κ hu hun hvn
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Pi.add_apply] at hx1 hx2 ⊢
  rw [hx1, hx2]

-- ported from GFNBounds.Core.aemeasurable_ofReal (lean/GFNBounds/Core/Kernel.lean:395)
/-- The positive part of an integrable function is `ν`-a.e. measurable as an `ℝ≥0∞` density. -/
theorem aemeasurable_ofReal {ν : Measure α} {f : α → ℝ} (hf : Integrable f ν) :
    AEMeasurable (fun y => ENNReal.ofReal (f y)) ν :=
  ENNReal.measurable_ofReal.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable

-- ported from GFNBounds.Core.densityAction_add (lean/GFNBounds/Core/Kernel.lean:404)
/-- **`P⋆` is additive**, `ν`-a.e., on `ν`-integrable densities.

The proof is the pointwise identity `(u+v)⁺ + u⁻ + v⁻ = (u+v)⁻ + u⁺ + v⁺` of `ofReal_add_aux`,
pushed through `T` — which is additive by `bindDensity_add` — and read back in `ℝ` where every
term is finite. Subtraction in `ℝ≥0∞` is never performed. -/
theorem densityAction_add (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α} [SigmaFinite ν]
    (hinv : ν.bind ⇑κ = ν) {f g : α → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) :
    densityAction κ ν (fun x => f x + g x)
      =ᵐ[ν] fun x => densityAction κ ν f x + densityAction κ ν g x := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have hgn : Integrable (fun x => -g x) ν := hg.neg
  have hs : Integrable (fun x => f x + g x) ν := hf.add hg
  have hsn : Integrable (fun x => -(f x + g x)) ν := hs.neg
  have hfun : (fun y => ENNReal.ofReal (f y + g y)) + (fun y => ENNReal.ofReal (-f y))
        + (fun y => ENNReal.ofReal (-g y))
      = (fun y => ENNReal.ofReal (-(f y + g y))) + (fun y => ENNReal.ofReal (f y))
        + (fun y => ENNReal.ofReal (g y)) := by
    funext y
    simpa only [Pi.add_apply] using ofReal_add_aux (f y) (g y)
  have hL := bindDensity_add₃ κ (aemeasurable_ofReal hs) (aemeasurable_ofReal hfn)
    (lintegral_ofReal_ne_top hs) (lintegral_ofReal_ne_top hfn) (lintegral_ofReal_ne_top hgn)
  have hR := bindDensity_add₃ κ (aemeasurable_ofReal hsn) (aemeasurable_ofReal hf)
    (lintegral_ofReal_ne_top hsn) (lintegral_ofReal_ne_top hf) (lintegral_ofReal_ne_top hg)
  rw [hfun] at hL
  filter_upwards [hL, hR, bindDensity_ofReal_lt_top κ hinv hf,
    bindDensity_ofReal_lt_top κ hinv hfn, bindDensity_ofReal_lt_top κ hinv hg,
    bindDensity_ofReal_lt_top κ hinv hgn, bindDensity_ofReal_lt_top κ hinv hs,
    bindDensity_ofReal_lt_top κ hinv hsn] with x hxL hxR hA hB hC hD hE hK
  simp only [Pi.add_apply] at hxL hxR
  have hkey : bindDensity κ ν (fun y => ENNReal.ofReal (f y + g y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-g y)) x
      = bindDensity κ ν (fun y => ENNReal.ofReal (-(f y + g y))) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (g y)) x := by
    rw [← hxL, ← hxR]
  have hreal := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hE.ne, hB.ne⟩) hD.ne,
    ENNReal.toReal_add hE.ne hB.ne,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hK.ne, hA.ne⟩) hC.ne,
    ENNReal.toReal_add hK.ne hA.ne] at hreal
  simp only [densityAction]
  linarith

-- ported from GFNBounds.Core.densityAction_neg (lean/GFNBounds/Core/Kernel.lean:444)
/-- `P⋆(-f) = -P⋆ f`, by definition: negation swaps the positive and negative parts. -/
theorem densityAction_neg (κ : Kernel α α) (ν : Measure α) (f : α → ℝ) :
    densityAction κ ν (fun x => -f x) = fun x => -densityAction κ ν f x := by
  funext x
  simp only [densityAction, neg_neg]
  ring

-- ported from GFNBounds.Core.densityAction_smul_nonneg (lean/GFNBounds/Core/Kernel.lean:451)
/-- `P⋆` is homogeneous under a non-negative scalar. -/
theorem densityAction_smul_nonneg (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] {r : ℝ} (hr : 0 ≤ r) {f : α → ℝ} (hf : Integrable f ν) :
    densityAction κ ν (fun x => r * f x) =ᵐ[ν] fun x => r * densityAction κ ν f x := by
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have e1 : (fun y => ENNReal.ofReal (r * f y))
      = ENNReal.ofReal r • fun y => ENNReal.ofReal (f y) := by
    funext y; simp [ENNReal.ofReal_mul hr, smul_eq_mul]
  have e2 : (fun y => ENNReal.ofReal (-(r * f y)))
      = ENNReal.ofReal r • fun y => ENNReal.ofReal (-f y) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hr]
    ring_nf
  have hA := bindDensity_smul κ (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    (aemeasurable_ofReal hf) (lintegral_ofReal_ne_top hf)
  have hB := bindDensity_smul κ (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    (aemeasurable_ofReal hfn) (lintegral_ofReal_ne_top hfn)
  filter_upwards [hA, hB] with x hxA hxB
  simp only [densityAction, e1, e2]
  rw [hxA, hxB]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
  ring

-- ported from GFNBounds.Core.densityAction_smul (lean/GFNBounds/Core/Kernel.lean:474)
/-- **`P⋆` is homogeneous**, `ν`-a.e., under every real scalar. -/
theorem densityAction_smul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (r : ℝ) {f : α → ℝ} (hf : Integrable f ν) :
    densityAction κ ν (fun x => r * f x) =ᵐ[ν] fun x => r * densityAction κ ν f x := by
  rcases le_total 0 r with hr | hr
  · exact densityAction_smul_nonneg κ hr hf
  · have hrn : (0 : ℝ) ≤ -r := by linarith
    have e : (fun x => r * f x) = fun x => -((-r) * f x) := by funext x; ring
    have h := densityAction_smul_nonneg κ hrn hf
    rw [e, densityAction_neg]
    filter_upwards [h] with x hx
    rw [hx]
    ring

/-! ## `P⋆` as a bounded operator on `L^p(ν)`, and the universality payoff -/

-- ported from GFNBounds.Core.IsBoundedDensityAction (lean/GFNBounds/Core/Kernel.lean:499)
/-- **The paper's boundedness hypothesis on the parameterization**, and the only hypothesis of
`theo:universality_L2_full` that this file assumes rather than derives.

`theo:universality_L2_full` asks for "a Markov kernel on `𝒮` with finite
`L^p(ν_B) → L^p(ν_B)` operator norm", and the main text is explicit that this is a requirement on
the parameterization and not a theorem: "boundedness of `‖π⋆‖_{L^p(ν_B)}` […] is not automatic"
(`universality.tex:6–9`), "the definitions above do not guarantee that `‖π⋆‖_{L^p(ν_B)}` is
finite" (`proofs.tex:36`). The two fields are the two halves of "`P⋆` is a bounded operator of
`L^p(ν_B)`": that it maps `L^p` into `L^p`, and that it does so with a bound. `C` is the operator
norm bound, carried explicitly rather than as `∃ C`. -/
structure IsBoundedDensityAction (κ : Kernel α α) (ν : Measure α) (p : ℝ≥0∞) (C : ℝ) : Prop where
  /-- The bound is non-negative. -/
  nonneg : 0 ≤ C
  /-- `P⋆` maps `L^p(ν)` into `L^p(ν)`. -/
  memLp : ∀ f : α → ℝ, MemLp f p ν → MemLp (densityAction κ ν f) p ν
  /-- `‖P⋆ f‖_{L^p(ν)} ≤ C ‖f‖_{L^p(ν)}`. -/
  eLpNorm_le : ∀ f : α → ℝ, MemLp f p ν →
    eLpNorm (densityAction κ ν f) p ν ≤ ENNReal.ofReal C * eLpNorm f p ν

-- ported from GFNBounds.Core.densityActionLM (lean/GFNBounds/Core/Kernel.lean:510)
/-- `P⋆` as a linear map on `L^p(ν)`. Linearity is `densityAction_add` and `densityAction_smul`
read on the `L^p` quotient, which is where the two a.e. identities become equalities. -/
noncomputable def densityActionLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : Lp ℝ p ν →ₗ[ℝ] Lp ℝ p ν where
  toFun F := (hb.memLp _ (Lp.memLp F)).toLp _
  map_add' F G := by
    have hae : densityAction κ ν ⇑(F + G)
        =ᵐ[ν] densityAction κ ν ⇑F + densityAction κ ν ⇑G := by
      have h1 : densityAction κ ν ⇑(F + G)
          = densityAction κ ν fun x => (F : α → ℝ) x + (G : α → ℝ) x := by
        refine densityAction_congr κ ν ?_
        filter_upwards [Lp.coeFn_add F G] with x hx
        simpa using hx
      rw [h1]
      filter_upwards [densityAction_add κ hinv (integrable_of_Lp F) (integrable_of_Lp G)]
        with x hx
      simpa using hx
    rw [← MemLp.toLp_add (hb.memLp _ (Lp.memLp F)) (hb.memLp _ (Lp.memLp G))]
    exact MemLp.toLp_congr _ _ hae
  map_smul' c F := by
    have hae : densityAction κ ν ⇑(c • F) =ᵐ[ν] c • densityAction κ ν ⇑F := by
      have h1 : densityAction κ ν ⇑(c • F)
          = densityAction κ ν fun x => c * (F : α → ℝ) x := by
        refine densityAction_congr κ ν ?_
        filter_upwards [Lp.coeFn_smul c F] with x hx
        simpa using hx
      rw [h1]
      filter_upwards [densityAction_smul κ c (integrable_of_Lp F)] with x hx
      simpa using hx
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hb.memLp _ (Lp.memLp F))]
    exact MemLp.toLp_congr _ _ hae

-- ported from GFNBounds.Core.densityActionCLM (lean/GFNBounds/Core/Kernel.lean:544)
/-- **`P⋆` as a `ContinuousLinearMap` on `L^p(ν)`**, with the paper's own operator-norm bound `C`
as the continuity constant. -/
noncomputable def densityActionCLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : Lp ℝ p ν →L[ℝ] Lp ℝ p ν :=
  (densityActionLM κ ν p hinv hb).mkContinuous C fun F => by
    have h := hb.eLpNorm_le _ (Lp.memLp F)
    have hne : ENNReal.ofReal C * eLpNorm (⇑F) p ν ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)
    calc ‖(densityActionLM κ ν p hinv hb) F‖
        = (eLpNorm (densityAction κ ν ⇑F) p ν).toReal :=
          Lp.norm_toLp _ (hb.memLp _ (Lp.memLp F))
      _ ≤ (ENNReal.ofReal C * eLpNorm (⇑F) p ν).toReal := ENNReal.toReal_mono hne h
      _ = C * ‖F‖ := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.nonneg, Lp.norm_def]

-- ported from GFNBounds.Core.norm_densityActionCLM_le (lean/GFNBounds/Core/Kernel.lean:559)
/-- `‖P⋆‖_{L^p→L^p} ≤ C`: the paper's constant bounds the operator norm, as rule 3 asks. -/
theorem norm_densityActionCLM_le (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) : ‖densityActionCLM κ ν p hinv hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hb.nonneg _

-- ported from GFNBounds.Core.coeFn_densityActionCLM (lean/GFNBounds/Core/Kernel.lean:565)
/-- The `L^p` operator applied to `F` is represented by `P⋆` applied to any representative. -/
theorem coeFn_densityActionCLM (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (p : ℝ≥0∞) [Fact (1 ≤ p)] {C : ℝ} (hinv : ν.bind ⇑κ = ν)
    (hb : IsBoundedDensityAction κ ν p C) (F : Lp ℝ p ν) :
    ⇑(densityActionCLM κ ν p hinv hb F) =ᵐ[ν] densityAction κ ν ⇑F :=
  MemLp.coeFn_toLp (hb.memLp _ (Lp.memLp F))


-- ported from GFNBounds.Core.two_mul_le_sq_add_sq_ennreal (lean/GFNBounds/Core/SigmaMixing.lean:128)
/-- `2ab ≤ a² + b²` in `ℝ≥0∞` — including at `∞`, where both sides are `∞` unless a factor on
the left vanishes. -/
theorem two_mul_le_sq_add_sq_ennreal (a b : ℝ≥0∞) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · simp
    · simp [ENNReal.top_pow two_ne_zero]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.top_pow two_ne_zero]
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast two_mul_le_add_sq a b

-- ported from GFNBounds.Core.lintegral_bindDensity_mul (lean/GFNBounds/Core/SigmaMixing.lean:142)
/-- **Duality for the density action**: `∫ (Tf)·h dλ = ∫ f(x) (∫ h dT(x)) dλ(x)`, for a
non-negative density `f` and a measurable test function `h`. It is `(Tf)λ = (fλ)T`
(`withDensity_bindDensity`) integrated against `h`. -/
theorem lintegral_bindDensity_mul (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    {h : α → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, bindDensity κ ν f x * h x ∂ν = ∫⁻ x, f x * ∫⁻ y, h y ∂κ x ∂ν := by
  have h1 : ∫⁻ x, h x ∂(ν.withDensity (bindDensity κ ν f))
      = ∫⁻ x, bindDensity κ ν f x * h x ∂ν :=
    lintegral_withDensity_eq_lintegral_mul ν (measurable_bindDensity κ ν f) hh
  rw [← h1, withDensity_bindDensity κ hinv f,
    Measure.lintegral_bind (κ.aemeasurable) hh.aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul₀ hf (hh.lintegral_kernel.aemeasurable)

-- ported from GFNBounds.Core.two_mul_lintegral_bindDensity_mul_le (lean/GFNBounds/Core/SigmaMixing.lean:155)
/-- `2 ∫ (Tf)·h dλ ≤ ∫ f² dλ + ∫ h² dλ`: `2f(x)h(y) ≤ f(x)² + h(y)²` integrated against
`λ(dx) T(x,dy)`, whose first marginal is `λ` (`T` Markov) and second `λT = λ` (invariance). -/
theorem two_mul_lintegral_bindDensity_mul_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    {h : α → ℝ≥0∞} (hh : Measurable h) :
    2 * ∫⁻ x, bindDensity κ ν f x * h x ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, h x ^ 2 ∂ν := by
  have hh2 : Measurable fun y => h y ^ 2 := hh.pow_const 2
  rw [lintegral_bindDensity_mul κ hinv hf hh, ← lintegral_const_mul' 2 _ (by norm_num)]
  calc ∫⁻ x, 2 * (f x * ∫⁻ y, h y ∂κ x) ∂ν
      = ∫⁻ x, ∫⁻ y, 2 * f x * h y ∂κ x ∂ν := by
        congr 1; funext x; rw [lintegral_const_mul _ hh, mul_assoc]
    _ ≤ ∫⁻ x, ∫⁻ y, (f x ^ 2 + h y ^ 2) ∂κ x ∂ν := by
        gcongr with x y; exact two_mul_le_sq_add_sq_ennreal _ _
    _ = ∫⁻ x, (f x ^ 2 + ∫⁻ y, h y ^ 2 ∂κ x) ∂ν := by
        congr 1; funext x
        rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, ∫⁻ y, h y ^ 2 ∂κ x ∂ν :=
        lintegral_add_right' _ hh2.lintegral_kernel.aemeasurable
    _ = ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, h x ^ 2 ∂ν := by
        rw [← Measure.lintegral_bind κ.aemeasurable hh2.aemeasurable, hinv]

-- ported from GFNBounds.Core.lintegral_bindDensity_sq_le (lean/GFNBounds/Core/SigmaMixing.lean:177)
/-- **`∫ (Tf)² dλ ≤ ∫ f² dλ`** for every non-negative density `f`, with no integrability
assumed. The truncations `min(Tf, n)` have finite square integral, which is what lets the
duality bound be cancelled; monotone convergence removes the truncation. -/
theorem lintegral_bindDensity_sq_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    ∫⁻ x, bindDensity κ ν f x ^ 2 ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν := by
  have hg : Measurable (bindDensity κ ν f) := measurable_bindDensity κ ν f
  set t : ℕ → α → ℝ≥0∞ := fun n x => min (bindDensity κ ν f x) n with ht_def
  have ht : ∀ n, Measurable (t n) := fun n => hg.min measurable_const
  have hbound : ∀ n, ∫⁻ x, t n x ^ 2 ∂ν ≤ ∫⁻ x, f x ^ 2 ∂ν := by
    intro n
    have hfin : ∫⁻ x, t n x ^ 2 ∂ν ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (n : ℝ≥0∞) ^ 2 ∂ν) ?_ (lintegral_mono fun x => ?_)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))
          (measure_ne_top _ _)
      · gcongr
        exact min_le_right _ _
    have hsq : ∫⁻ x, t n x ^ 2 ∂ν ≤ ∫⁻ x, bindDensity κ ν f x * t n x ∂ν := by
      refine lintegral_mono fun x => ?_
      rw [sq]
      gcongr
      exact min_le_left _ _
    have h2 := two_mul_lintegral_bindDensity_mul_le κ hinv hf (ht n)
    have hsum : ∫⁻ x, t n x ^ 2 ∂ν + ∫⁻ x, t n x ^ 2 ∂ν
        ≤ ∫⁻ x, f x ^ 2 ∂ν + ∫⁻ x, t n x ^ 2 ∂ν := by
      rw [← two_mul]
      exact (mul_le_mul_right hsq 2).trans h2
    exact ENNReal.le_of_add_le_add_right hfin hsum
  have hsup : ∀ x, bindDensity κ ν f x ^ 2 = ⨆ n : ℕ, t n x ^ 2 := by
    intro x
    rw [← ENNReal.iSup_pow]
    congr 1
    simp only [ht_def]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmono : Monotone fun n x => t n x ^ 2 := by
    intro n m hnm x
    simp only [ht_def]
    gcongr
  calc ∫⁻ x, bindDensity κ ν f x ^ 2 ∂ν = ∫⁻ x, ⨆ n : ℕ, t n x ^ 2 ∂ν := by
        congr 1; funext x; exact hsup x
    _ = ⨆ n : ℕ, ∫⁻ x, t n x ^ 2 ∂ν := lintegral_iSup (fun n => (ht n).pow_const 2) hmono
    _ ≤ ∫⁻ x, f x ^ 2 ∂ν := iSup_le hbound

-- ported from GFNBounds.Core.eLpNorm_bindDensity_two_le (lean/GFNBounds/Core/SigmaMixing.lean:219)
/-- `‖Tf‖_{L²(λ)} ≤ ‖f‖_{L²(λ)}` for a non-negative density, in `eLpNorm` form. -/
theorem eLpNorm_bindDensity_two_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    eLpNorm (bindDensity κ ν f) 2 ν ≤ eLpNorm f 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_bindDensity_sq_le κ hinv hf) (by norm_num)

-- ported from GFNBounds.Core.ofReal_add_ofReal_neg (lean/GFNBounds/Core/SigmaMixing.lean:228)
/-- `r⁺ + r⁻ = |r|`, in `ℝ≥0∞`. -/
theorem ofReal_add_ofReal_neg (r : ℝ) : ENNReal.ofReal r + ENNReal.ofReal (-r) = ‖r‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 r with hr | hr
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), add_zero, abs_of_nonneg hr]
  · rw [ENNReal.ofReal_of_nonpos hr, zero_add, abs_of_nonpos hr]

-- ported from GFNBounds.Core.enorm_densityAction_le (lean/GFNBounds/Core/SigmaMixing.lean:236)
/-- `|P f| ≤ T |f|`, `λ`-a.e., for an integrable signed density: `|Tf⁺ − Tf⁻| ≤ Tf⁺ + Tf⁻`, and
`T` is additive. -/
theorem enorm_densityAction_le (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [SigmaFinite ν] (hinv : ν.bind ⇑κ = ν) {f : α → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂ν, ‖densityAction κ ν f x‖ₑ ≤ bindDensity κ ν (fun y => ‖f y‖ₑ) x := by
  have hsplit : (fun y => ‖f y‖ₑ)
      = (fun y => ENNReal.ofReal (f y)) + (fun y => ENNReal.ofReal (-f y)) := by
    funext y
    simp only [_root_.Pi.add_apply, ofReal_add_ofReal_neg]
  have hfn : Integrable (fun x => -f x) ν := hf.neg
  have hadd := bindDensity_add κ (ν := ν) (aemeasurable_ofReal hf) (lintegral_ofReal_ne_top hf)
    (lintegral_ofReal_ne_top hfn)
  filter_upwards [hadd, bindDensity_ofReal_lt_top κ hinv hf,
    bindDensity_ofReal_lt_top κ hinv hfn] with x hx hA hB
  rw [hsplit, hx]
  simp only [_root_.Pi.add_apply, densityAction]
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |(bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
        - (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal|
      ≤ ENNReal.ofReal ((bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x).toReal
        + (bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x).toReal) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := ENNReal.toReal_nonneg (a := bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x)
        have h2 := ENNReal.toReal_nonneg (a := bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x)
        refine abs_sub_le_iff.2 ⟨?_, ?_⟩ <;> linarith
    _ = bindDensity κ ν (fun y => ENNReal.ofReal (f y)) x
        + bindDensity κ ν (fun y => ENNReal.ofReal (-f y)) x := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hA.ne, ENNReal.ofReal_toReal hB.ne]

-- ported from GFNBounds.Core.isBoundedDensityAction_two (lean/GFNBounds/Core/SigmaMixing.lean:268)
/-- **The density action of a Markov kernel is a contraction of `L²(λ)`** whenever `λ` is finite
and invariant: `IsBoundedDensityAction κ λ 2 1`. This is the `‖P‖ ≤ 1` that `lem:sigma_mixing`
presupposes in calling `P` an operator on `L²(λ)` (the paper's `eq:reversal_contraction`), and it
discharges the hypothesis `Core.Kernel` carries at `p = 2`. -/
theorem isBoundedDensityAction_two (κ : Kernel α α) [IsMarkovKernel κ] {ν : Measure α}
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) : IsBoundedDensityAction κ ν 2 1 := by
  have key : ∀ f : α → ℝ, MemLp f 2 ν → eLpNorm (densityAction κ ν f) 2 ν ≤ eLpNorm f 2 ν := by
    intro f hf
    have hint : Integrable f ν := hf.integrable (by norm_num)
    calc eLpNorm (densityAction κ ν f) 2 ν
        ≤ eLpNorm (bindDensity κ ν (fun y => ‖f y‖ₑ)) 2 ν := by
          refine eLpNorm_mono_enorm_ae ?_
          simpa only [enorm_eq_self] using enorm_densityAction_le κ hinv hint
      _ ≤ eLpNorm (fun y => ‖f y‖ₑ) 2 ν :=
          eLpNorm_bindDensity_two_le κ hinv hf.aestronglyMeasurable.enorm
      _ = eLpNorm f 2 ν := eLpNorm_enorm f
  refine ⟨zero_le_one, fun f hf => ⟨(measurable_densityAction κ ν f).aestronglyMeasurable,
    lt_of_le_of_lt (key f hf) hf.eLpNorm_lt_top⟩, fun f hf => ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  exact key f hf


-- ported from GFNBounds.Core.densityActionL2 (lean/GFNBounds/Core/SigmaMixing.lean:458)
/-- **The paper's `P` of `lem:sigma_mixing`**: the density action `h ↦ d((hλ)T)/dλ` of a Markov
kernel on `L²(λ)`, a bounded operator by `isBoundedDensityAction_two` rather than by
hypothesis. -/
noncomputable def densityActionL2 (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  densityActionCLM κ ν 2 hinv (isBoundedDensityAction_two κ hinv)

-- ported from GFNBounds.Core.norm_densityActionL2_le (lean/GFNBounds/Core/SigmaMixing.lean:465)
/-- `‖P‖_{L²(λ) → L²(λ)} ≤ 1`. -/
theorem norm_densityActionL2_le (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α)
    [IsFiniteMeasure ν] (hinv : ν.bind ⇑κ = ν) : ‖densityActionL2 κ ν hinv‖ ≤ 1 :=
  norm_densityActionCLM_le κ ν 2 hinv _

end Markov

variable {S : Type*} [MeasurableSpace S]

/-! ## Ergodicity of a Markov kernel -/

/-- **Ergodicity of a Markov kernel** for a measure `μ`, in Walters' sense of invariant sets
(`main.tex:211` cites `walters2000introduction`): every measurable `A` with `π(x, A) = 𝟙_A(x)` for
`μ`-a.e. `x` is `μ`-null or `μ`-conull. Invariance of `μ` is not part of the definition. -/
def IsKernelErgodic (π : Kernel S S) (μ : Measure S) : Prop :=
  ∀ A, MeasurableSet A → (∀ᵐ x ∂μ, π x A = A.indicator 1 x) → μ A = 0 ∨ μ Aᶜ = 0

/-- Ergodicity depends on `μ` only through its null sets. -/
theorem isKernelErgodic_congr {π : Kernel S S} {μ ν : Measure S} (h₁ : μ ≪ ν) (h₂ : ν ≪ μ) :
    IsKernelErgodic π μ ↔ IsKernelErgodic π ν := by
  have key : ∀ {μ ν : Measure S}, μ ≪ ν → ν ≪ μ → IsKernelErgodic π μ → IsKernelErgodic π ν := by
    intro μ ν h₁ h₂ h A hA hinv
    rcases h A hA (h₁.ae_le hinv) with h0 | h0
    · exact Or.inl (h₂ h0)
    · exact Or.inr (h₂ h0)
  exact ⟨key h₁ h₂, key h₂ h₁⟩

/-! ## Inhabitants -/

/-- **A quasi-ergodic map gives an ergodic kernel**: `x ↦ δ_{Φ x}`. -/
theorem isKernelErgodic_deterministic_of_quasiErgodic {Φ : S → S} (hΦ : Measurable Φ)
    {μ : Measure S} (h : QuasiErgodic Φ μ) : IsKernelErgodic (Kernel.deterministic Φ hΦ) μ := by
  intro A hA hinv
  have hpre : Φ ⁻¹' A =ᵐ[μ] A := by
    filter_upwards [hinv] with x hx
    rw [Kernel.deterministic_apply' hΦ _ hA] at hx
    apply propext
    change Φ x ∈ A ↔ x ∈ A
    by_cases h1 : Φ x ∈ A <;> by_cases h2 : x ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
  rcases h.ae_empty_or_univ₀ hA.nullMeasurableSet hpre with h0 | h0
  · exact Or.inl (ae_eq_empty.mp h0)
  · exact Or.inr (ae_eq_univ.mp h0)

/-- **Mathlib's `Ergodic Φ μ` gives an ergodic, `μ`-invariant kernel** `x ↦ δ_{Φ x}`. -/
theorem isKernelErgodic_deterministic {Φ : S → S} (hΦ : Measurable Φ) {μ : Measure S}
    (h : Ergodic Φ μ) :
    μ.bind (Kernel.deterministic Φ hΦ) = μ ∧ IsKernelErgodic (Kernel.deterministic Φ hΦ) μ := by
  refine ⟨?_, isKernelErgodic_deterministic_of_quasiErgodic hΦ h.quasiErgodic⟩
  change μ.bind (fun x => Measure.dirac (Φ x)) = μ
  rw [Measure.bind_dirac_eq_map _ hΦ, h.map_eq]

/-- **An EGF policy with positive weights is ergodic** as soon as every set a.e.-invariant under
all the moves is null or conull. No invariance of `μ` is needed. -/
theorem IsEGFPolicy.isKernelErgodic {π : Kernel S S} {p : ℕ} {Φ : Fin p → S → S}
    {α : Fin p → S → ℝ} (h : IsEGFPolicy π Φ α) (hpos : ∀ i s, 0 < α i s) {μ : Measure S}
    (herg : ∀ A, MeasurableSet A → (∀ i, Φ i ⁻¹' A =ᵐ[μ] A) → μ A = 0 ∨ μ Aᶜ = 0) :
    IsKernelErgodic π μ := by
  haveI := h.isMarkovKernel
  intro A hA hinv
  -- a null value of `π x B` forces every move out of `B`
  have hzero : ∀ x B, MeasurableSet B → π x B = 0 → ∀ i, Φ i x ∉ B := by
    intro x B hB h0 i hi
    rw [h.apply_set x hB, Finset.sum_eq_zero_iff] at h0
    have := h0 i (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi, Pi.one_apply, mul_one] at this
    exact (ENNReal.ofReal_pos.mpr (hpos i x)).ne' this
  refine herg A hA fun i => ?_
  filter_upwards [hinv] with x hx
  apply propext
  change Φ i x ∈ A ↔ x ∈ A
  by_cases hxA : x ∈ A
  · have hc : π x Aᶜ = 0 := by
      rw [prob_compl_eq_one_sub hA, hx, Set.indicator_of_mem hxA, Pi.one_apply, tsub_self]
    exact ⟨fun _ => hxA, fun _ => not_not.mp (hzero x Aᶜ hA.compl hc i)⟩
  · have hc : π x A = 0 := by rw [hx, Set.indicator_of_notMem hxA]
    exact ⟨fun h' => absurd h' (hzero x A hA hc i), fun h' => absurd h' hxA⟩

/-- With uniform weights `1/p` and measure-preserving moves, `μ` is invariant. -/
theorem IsEGFPolicy.bind_eq_of_uniform {π : Kernel S S} {p : ℕ} {Φ : Fin p → S → S}
    (h : IsEGFPolicy π Φ (fun _ _ => 1 / (p : ℝ))) {μ : Measure S}
    (hmp : ∀ i, MeasurePreserving (Φ i) μ μ) : μ.bind π = μ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · simp [Measure.eq_zero_of_isEmpty μ]
  have hp : p ≠ 0 := by
    rintro rfl
    have := h.weight_sum s₀
    simp at this
  rw [h.bind_eq_sum_map μ]
  have hc : ∀ i, (μ.withDensity fun _ => ENNReal.ofReal (1 / (p : ℝ))).map (Φ i)
      = ENNReal.ofReal (1 / (p : ℝ)) • μ := by
    intro i
    rw [withDensity_const, Measure.map_smul, (hmp i).map_eq]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
  have hone : (p : ℝ≥0∞) * ENNReal.ofReal (1 / (p : ℝ)) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hp), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hp) (ENNReal.natCast_ne_top p)
  rw [hone, one_smul]

/-- **The uniform EGF kernel** `π(s) = (1/p) ∑ᵢ δ_{Φᵢ(s)}` of measure-preserving moves, with no
common a.e.-invariant set other than null and conull ones, leaves `μ` invariant and is ergodic. -/
theorem isKernelErgodic_egfKernel_uniform {p : ℕ} (hp : 0 < p) (Φ : Fin p → S → S)
    (hΦ : ∀ i, Measurable (Φ i)) {μ : Measure S} (hmp : ∀ i, MeasurePreserving (Φ i) μ μ)
    (herg : ∀ A, MeasurableSet A → (∀ i, Φ i ⁻¹' A =ᵐ[μ] A) → μ A = 0 ∨ μ Aᶜ = 0) :
    μ.bind (egfKernel Φ (fun _ _ => 1 / (p : ℝ)) hΦ fun _ => measurable_const) = μ ∧
      IsKernelErgodic (egfKernel Φ (fun _ _ => 1 / (p : ℝ)) hΦ fun _ => measurable_const) μ := by
  have hpos : ∀ (i : Fin p) (s : S), 0 < 1 / (p : ℝ) := fun _ _ => by positivity
  have hpol := isEGFPolicy_egfKernel Φ (fun _ _ => 1 / (p : ℝ)) hΦ (fun _ => measurable_const)
    (fun i s => (hpos i s).le) (fun s => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
  exact ⟨hpol.bind_eq_of_uniform hmp, hpol.isKernelErgodic hpos herg⟩

/-! ## Fixed points of the density action are constant -/

namespace Markov

/-- **An invariant density gives an invariant set**: if `(fν)π = fν` and `νπ = ν` with `ν` finite,
then `E = {f > 0}` has `π(x, E) = 𝟙_E(x)` for `ν`-a.e. `x`. -/
theorem ae_apply_eq_indicator_of_withDensity_invariant (π : Kernel S S) [IsMarkovKernel π]
    (ν : Measure S) [IsFiniteMeasure ν] (hinv : ν.bind π = ν) {f : S → ℝ≥0∞} (hf : Measurable f)
    (hfi : (ν.withDensity f).bind π = ν.withDensity f) :
    ∀ᵐ x ∂ν, π x {y | 0 < f y} = {y | 0 < f y}.indicator 1 x := by
  set E := {y | 0 < f y} with hE
  have hEm : MeasurableSet E := measurableSet_lt measurable_const hf
  -- `f ν` does not charge `Eᶜ`, nor does its push
  have h1 : ν.withDensity f Eᶜ = 0 := by
    rw [withDensity_apply _ hEm.compl]
    have h0 : ∀ x ∈ Eᶜ, f x = 0 := fun x hx => by
      have hx' : ¬ 0 < f x := hx
      exact nonpos_iff_eq_zero.mp (not_lt.mp hx')
    calc ∫⁻ x in Eᶜ, f x ∂ν = ∫⁻ _ in Eᶜ, 0 ∂ν := setLIntegral_congr_fun hEm.compl h0
      _ = 0 := lintegral_zero
  have h2 : ((ν.withDensity f).bind π) Eᶜ = 0 := by rw [hfi]; exact h1
  rw [Measure.bind_apply hEm.compl π.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hf (π.measurable_coe hEm.compl)] at h2
  have h3 := (lintegral_eq_zero_iff (hf.mul (π.measurable_coe hEm.compl))).mp h2
  -- on `E`, the kernel stays in `E`
  have h4 : ∀ᵐ x ∂ν, x ∈ E → π x E = 1 := by
    filter_upwards [h3] with x hx hxE
    have hx' : f x * π x Eᶜ = 0 := hx
    have hc : π x Eᶜ = 0 := (mul_eq_zero.mp hx').resolve_left (ne_of_gt hxE)
    exact (prob_compl_eq_zero_iff hEm).mp hc
  -- on `Eᶜ`, it does not enter `E`: `∫ π(x, E) dν = ν E` by invariance
  have htot : ∫⁻ x, π x E ∂ν = ν E := by
    rw [← Measure.bind_apply hEm π.aemeasurable, hinv]
  have hE1 : ∫⁻ x in E, π x E ∂ν = ν E := by
    calc ∫⁻ x in E, π x E ∂ν = ∫⁻ _ in E, 1 ∂ν :=
          setLIntegral_congr_fun_ae hEm (h4.mono fun x hx hxE => hx hxE)
      _ = ν E := by rw [setLIntegral_const, one_mul]
  have hsplit := lintegral_add_compl (fun x => π x E) (μ := ν) hEm
  rw [hE1, htot] at hsplit
  have h5 : ∫⁻ x in Eᶜ, π x E ∂ν = 0 :=
    (ENNReal.add_right_inj (measure_ne_top ν E)).mp (hsplit.trans (add_zero _).symm)
  have h6 := (lintegral_eq_zero_iff (π.measurable_coe hEm)).mp h5
  have h6' : ∀ᵐ x ∂ν, x ∈ Eᶜ → π x E = 0 := (ae_restrict_iff' hEm.compl).mp h6
  filter_upwards [h4, h6'] with x hx4 hx6
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx, hx4 hx, Pi.one_apply]
  · rw [Set.indicator_of_notMem hx, hx6 hx]

/-- **Fixed points of the density action are constant under ergodicity**: for `ν` finite and
invariant, `π` ergodic for `ν`, an integrable `z` with `P z = z` a.e. is a.e. constant. -/
theorem ae_eq_const_of_densityAction_eq (π : Kernel S S) [IsMarkovKernel π] (ν : Measure S)
    [IsFiniteMeasure ν] (hinv : ν.bind π = ν) (herg : IsKernelErgodic π ν) {z : S → ℝ}
    (hzm : Measurable z) (hz : Integrable z ν) (hfix : densityAction π ν z =ᵐ[ν] z) :
    ∃ c : ℝ, z =ᵐ[ν] fun _ => c := by
  -- every superlevel set `{z > c}` is invariant, hence null or conull
  have key : ∀ c : ℝ, ν {x | c < z x} = 0 ∨ ν {x | c < z x}ᶜ = 0 := by
    intro c
    set w : S → ℝ := fun x => z x - c with hw
    have hwm : Measurable w := hzm.sub measurable_const
    have hwi : Integrable w ν := hz.sub (integrable_const c)
    -- `P w = w`: `P` fixes the constants
    have hone : densityAction π ν (fun _ => (1 : ℝ)) =ᵐ[ν] fun _ => (1 : ℝ) :=
      densityAction_one π hinv
    have hconst : densityAction π ν (fun _ : S => -c) =ᵐ[ν] fun _ => -c := by
      have e2 : (fun _ : S => -c) = fun x => (-c) * (fun _ : S => (1 : ℝ)) x := by
        funext x; simp
      rw [e2]
      filter_upwards [densityAction_smul π (-c) (integrable_const (1 : ℝ)), hone] with x hx h1
      rw [hx, h1]
    have hfixw : densityAction π ν w =ᵐ[ν] w := by
      have e1 : w = fun x => z x + (fun _ : S => -c) x := by
        funext x; simp [hw, sub_eq_add_neg]
      rw [e1]
      filter_upwards [densityAction_add π hinv hz (integrable_const (-c)), hfix, hconst]
        with x hx h1 h2
      rw [hx, h1, h2]
    -- the positive part `u = (z - c)⁺` is a fixed density
    set u : S → ℝ≥0∞ := fun x => ENNReal.ofReal (w x) with hu
    have hum : Measurable u := hwm.ennreal_ofReal
    have hufin : ∫⁻ x, u x ∂ν ≠ ∞ := lintegral_ofReal_ne_top hwi
    have hle : u ≤ᵐ[ν] bindDensity π ν u := by
      filter_upwards [hfixw, bindDensity_ofReal_lt_top π hinv hwi] with x hx hA
      simp only [densityAction] at hx
      show ENNReal.ofReal (w x) ≤ bindDensity π ν u x
      rw [← ENNReal.ofReal_toReal hA.ne]
      apply ENNReal.ofReal_le_ofReal
      have := ENNReal.toReal_nonneg
        (a := bindDensity π ν (fun y => ENNReal.ofReal (-w y)) x)
      linarith
    have heq : u =ᵐ[ν] bindDensity π ν u :=
      ae_eq_of_ae_le_of_lintegral_le hle hufin (measurable_bindDensity π ν u).aemeasurable
        (by rw [lintegral_bindDensity π hinv u])
    have hinvu : (ν.withDensity u).bind π = ν.withDensity u := by
      rw [← withDensity_bindDensity π hinv u]
      exact withDensity_congr_ae heq.symm
    have hset := ae_apply_eq_indicator_of_withDensity_invariant π ν hinv hum hinvu
    have hEeq : {y | 0 < u y} = {x | c < z x} := by
      ext y; simp [hu, hw, ENNReal.ofReal_pos, sub_pos]
    rw [hEeq] at hset
    exact herg _ (measurableSet_lt measurable_const hzm) hset
  -- the rational half-lines separate the points of `ℝ`
  haveI hsep : HasCountableSeparatingOn ℝ (fun U => ∃ q : ℚ, U = Set.Ioi (q : ℝ)) Set.univ := by
    refine ⟨⟨Set.range fun q : ℚ => Set.Ioi (q : ℝ), Set.countable_range _, ?_, ?_⟩⟩
    · rintro _ ⟨q, rfl⟩; exact ⟨q, rfl⟩
    · intro x _ y _ h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hlt
        have := h _ ⟨q, rfl⟩
        simp only [Set.mem_Ioi] at this
        exact absurd (this.mpr hqy) (not_lt.mpr hxq.le)
      · obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt
        have := h _ ⟨q, rfl⟩
        simp only [Set.mem_Ioi] at this
        exact absurd (this.mp hqx) (not_lt.mpr hyq.le)
  obtain ⟨a, ha⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae ν) (f := z)
    (fun U => ∃ q : ℚ, U = Set.Ioi (q : ℝ)) (by
      rintro U ⟨q, rfl⟩
      rcases key q with h0 | h0
      · right
        exact measure_eq_zero_iff_ae_notMem.mp h0
      · left
        exact mem_ae_iff.mpr h0)
  exact ⟨a, ha⟩

/-- **von Neumann's mean ergodic theorem for the density action**: for `π` ergodic with a finite
invariant `ν`, the Cesàro averages `(1/N) ∑_{n<N} Pⁿ x` of a mean-zero `x ∈ L²(ν)` tend to `0`. -/
theorem tendsto_birkhoffAverage_densityActionL2 (π : Kernel S S) [IsMarkovKernel π]
    (ν : Measure S) [IsFiniteMeasure ν] (hinv : ν.bind π = ν) (herg : IsKernelErgodic π ν)
    (x : Lp ℝ 2 ν) (hx : ∫ s, x s ∂ν = 0) :
    Tendsto (fun N => birkhoffAverage ℝ (densityActionL2 π ν hinv) _root_.id N x) atTop (𝓝 0) := by
  set P := densityActionL2 π ν hinv with hPdef
  have hlim := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection P
    (norm_densityActionL2_le π ν hinv) x
  set K := P.eqLocus (1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) with hK
  rw [Submodule.coe_orthogonalProjectionOnto_apply] at hlim
  set w : Lp ℝ 2 ν := K.starProjection x with hw
  suffices hw0 : w = 0 by rwa [hw0] at hlim
  have hwK : w ∈ K := K.starProjection_apply_mem x
  have hPw : P w = w := by simpa [hK] using hwK
  -- `w` is a fixed point, hence a constant
  have hfix : densityAction π ν ⇑w =ᵐ[ν] ⇑w := by
    have h1 := coeFn_densityActionCLM π ν 2 hinv (isBoundedDensityAction_two π hinv) w
    have h2 : (densityActionCLM π ν 2 hinv (isBoundedDensityAction_two π hinv)) w = w := hPw
    rw [h2] at h1
    exact h1.symm
  have hwm := (Lp.aestronglyMeasurable w).aemeasurable
  set w' := hwm.mk ⇑w with hw'
  have hw'e : ⇑w =ᵐ[ν] w' := hwm.ae_eq_mk
  have hfix' : densityAction π ν w' =ᵐ[ν] w' := by
    rw [← densityAction_congr π ν hw'e]
    exact hfix.trans hw'e
  obtain ⟨c, hc⟩ := ae_eq_const_of_densityAction_eq π ν hinv herg hwm.measurable_mk
    ((integrable_of_Lp w).congr hw'e) hfix'
  have hwc : ⇑w =ᵐ[ν] fun _ => c := hw'e.trans hc
  -- `⟪x, w⟫ = c ∫ x = 0` and `⟪x - w, w⟫ = 0`
  have hxw : inner ℝ x w = 0 := by
    rw [MeasureTheory.L2.inner_def]
    calc ∫ a, inner ℝ (x a) (w a) ∂ν = ∫ a, x a * c ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hwc] with a ha
          rw [ha]; simp [mul_comm]
      _ = 0 := by rw [integral_mul_const, hx, zero_mul]
  have horth : inner ℝ (x - w) w = 0 := K.starProjection_inner_eq_zero x w hwK
  rw [inner_sub_left, hxw, zero_sub, neg_eq_zero] at horth
  exact inner_self_eq_zero.mp horth

/-- The density action on the density of a finite `m ≪ ν`: `P (dm/dν) = d(mπ)/dν`. -/
theorem densityAction_toReal_rnDeriv (π : Kernel S S) [IsMarkovKernel π] (ν : Measure S)
    [SigmaFinite ν] (m : Measure S) [IsFiniteMeasure m] (hm : m ≪ ν) :
    densityAction π ν (fun s => (m.rnDeriv ν s).toReal)
      =ᵐ[ν] fun s => ((m.bind π).rnDeriv ν s).toReal := by
  have h1 : (fun y => ENNReal.ofReal ((m.rnDeriv ν y).toReal)) =ᵐ[ν] m.rnDeriv ν := by
    filter_upwards [Measure.rnDeriv_lt_top m ν] with y hy
    exact ENNReal.ofReal_toReal hy.ne
  have h2 : (fun y => ENNReal.ofReal (-(m.rnDeriv ν y).toReal)) = 0 := by
    funext y
    exact ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ENNReal.toReal_nonneg)
  have e1 : bindDensity π ν (fun y => ENNReal.ofReal ((m.rnDeriv ν y).toReal))
      = (m.bind π).rnDeriv ν := by
    rw [bindDensity_congr π ν h1, bindDensity, Measure.withDensity_rnDeriv_eq m ν hm]
  filter_upwards [bindDensity_zero π ν] with s hs
  simp only [densityAction, e1, h2]
  rw [hs]
  simp

end Markov

/-! ## Cesàro mixing in total variation -/

open Markov in
/-- **Ergodicity gives Cesàro mixing in total variation** (von Neumann), for two measures of equal
mass dominated by `K λ̂`: some `N ≥ 1` has `‖∑_{t<N} (μ₀ − μ₁)πᵗ‖_TV < N η`. -/
theorem exists_tvMass_cesaro_lt_of_ergodic (π : Kernel S S) [IsMarkovKernel π]
    (lamHat : Measure S) [IsFiniteMeasure lamHat] (hinv : lamHat.bind π = lamHat)
    (herg : IsKernelErgodic π lamHat) {μ₀ μ₁ : Measure S} (K : ℝ≥0)
    (h₀ : μ₀ ≤ (K : ℝ≥0∞) • lamHat) (h₁ : μ₁ ≤ (K : ℝ≥0∞) • lamHat)
    (hmass : μ₀ Set.univ = μ₁ Set.univ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ tvMass (∑ t ∈ Finset.range N, pushIter π t μ₀)
      (∑ t ∈ Finset.range N, pushIter π t μ₁) < N * η := by
  classical
  set ν := lamHat with hν
  haveI hKfin : IsFiniteMeasure ((K : ℝ≥0∞) • ν) := Measure.smul_finite ν ENNReal.coe_ne_top
  have hKac : (K : ℝ≥0∞) • ν ≪ ν := Measure.AbsolutelyContinuous.rfl.smul_left _
  have hpush : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • ν → ∀ t, pushIter π t μ ≤ (K : ℝ≥0∞) • ν := by
    intro μ hμ t
    calc pushIter π t μ ≤ pushIter π t ((K : ℝ≥0∞) • ν) := pushIter_mono π t hμ
      _ = (K : ℝ≥0∞) • ν := by rw [pushIter_smul, pushIter_of_bind_eq π hinv]
  haveI : IsFiniteMeasure μ₀ := isFiniteMeasure_of_le _ h₀
  haveI : IsFiniteMeasure μ₁ := isFiniteMeasure_of_le _ h₁
  have hac : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • ν → μ ≪ ν := fun hμ =>
    (Measure.absolutelyContinuous_of_le hμ).trans hKac
  have hle : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • ν → μ.rnDeriv ν ≤ᵐ[ν] fun _ => (K : ℝ≥0∞) := by
    intro μ hμ
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => ?_
    rw [setLIntegral_const]
    calc ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s := Measure.setLIntegral_rnDeriv_le s
      _ ≤ ((K : ℝ≥0∞) • ν) s := hμ s
      _ = K * ν s := by rw [Measure.smul_apply, smul_eq_mul]
  -- the signed densities `φₙ = d(μ₀πⁿ)/dν − d(μ₁πⁿ)/dν`, bounded by `K`
  set φ : ℕ → S → ℝ := fun n s => ((pushIter π n μ₀).rnDeriv ν s).toReal
    - ((pushIter π n μ₁).rnDeriv ν s).toReal with hφ
  have hφL : ∀ n, MemLp (φ n) 2 ν := by
    intro n
    refine MemLp.of_bound (((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable) K ?_
    filter_upwards [hle (hpush h₀ n), hle (hpush h₁ n)] with s h0 h1
    have a0 := ENNReal.toReal_le_coe_of_le_coe h0
    have a1 := ENNReal.toReal_le_coe_of_le_coe h1
    have b0 := ENNReal.toReal_nonneg (a := (pushIter π n μ₀).rnDeriv ν s)
    have b1 := ENNReal.toReal_nonneg (a := (pushIter π n μ₁).rnDeriv ν s)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> simp only [hφ] <;> linarith
  -- one step of the density action
  have hstep : ∀ n, densityAction π ν (φ n) =ᵐ[ν] φ (n + 1) := by
    intro n
    have hi0 : Integrable (fun s => ((pushIter π n μ₀).rnDeriv ν s).toReal) ν :=
      Measure.integrable_toReal_rnDeriv
    have hi1 : Integrable (fun s => -((pushIter π n μ₁).rnDeriv ν s).toReal) ν :=
      Measure.integrable_toReal_rnDeriv.fun_neg
    have e : φ n = fun s => ((pushIter π n μ₀).rnDeriv ν s).toReal
        + -((pushIter π n μ₁).rnDeriv ν s).toReal := by
      funext s; simp only [hφ, sub_eq_add_neg]
    rw [e]
    filter_upwards [densityAction_add π hinv hi0 hi1,
      Markov.densityAction_toReal_rnDeriv π ν (pushIter π n μ₀) (hac (hpush h₀ n)),
      Markov.densityAction_toReal_rnDeriv π ν (pushIter π n μ₁) (hac (hpush h₁ n))]
      with s hs h0 h1
    rw [hs, densityAction_neg]
    simp only [h0, h1, hφ, pushIter_succ]
    ring
  -- the iterates and the Birkhoff sums in `L²(ν)`
  set P := densityActionL2 π ν hinv with hP
  set x : Lp ℝ 2 ν := (hφL 0).toLp (φ 0) with hx
  have hiter : ∀ n, ⇑((⇑P)^[n] x) =ᵐ[ν] φ n := by
    intro n
    induction n with
    | zero => exact MemLp.coeFn_toLp (hφL 0)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h1 := coeFn_densityActionCLM π ν 2 hinv (isBoundedDensityAction_two π hinv)
        ((⇑P)^[n] x)
      rw [densityAction_congr π ν ih] at h1
      exact h1.trans (hstep n)
  have hsumL : ∀ N, ⇑(birkhoffSum (⇑P) _root_.id N x)
      =ᵐ[ν] fun s => ∑ n ∈ Finset.range N, φ n s := by
    intro N
    induction N with
    | zero =>
      rw [birkhoffSum_zero]
      filter_upwards [Lp.coeFn_zero ℝ 2 ν] with s hs
      rw [hs]; simp
    | succ N ih =>
      rw [birkhoffSum_succ]
      filter_upwards [Lp.coeFn_add (birkhoffSum (⇑P) _root_.id N x) (_root_.id ((⇑P)^[N] x)), ih,
        hiter N] with s hs h1 h2
      rw [hs, Pi.add_apply, h1, Finset.sum_range_succ]
      simp only [id_eq] at h2 ⊢
      rw [h2]
  have hmean : ∫ s, x s ∂ν = 0 := by
    rw [integral_congr_ae (MemLp.coeFn_toLp (hφL 0))]
    simp only [hφ, pushIter_zero]
    rw [integral_sub Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv,
      Measure.integral_toReal_rnDeriv (hac h₀), Measure.integral_toReal_rnDeriv (hac h₁),
      measureReal_def, measureReal_def, hmass, sub_self]
  have hlim := Markov.tendsto_birkhoffAverage_densityActionL2 π ν hinv herg x hmean
  -- the sums of measures have the summed densities
  have hW : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • ν → ∀ N, ∑ n ∈ Finset.range N, pushIter π n μ
      = ν.withDensity (fun s => ∑ n ∈ Finset.range N, (pushIter π n μ).rnDeriv ν s) := by
    intro μ hμ N
    haveI : IsFiniteMeasure μ := isFiniteMeasure_of_le _ hμ
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have e : (fun s => ∑ n ∈ Finset.range (N + 1), (pushIter π n μ).rnDeriv ν s)
          = (fun s => ∑ n ∈ Finset.range N, (pushIter π n μ).rnDeriv ν s)
            + (pushIter π N μ).rnDeriv ν := by
        funext s; simp [Finset.sum_range_succ]
      rw [e, withDensity_add_left (Finset.measurable_sum _ fun n _ => Measure.measurable_rnDeriv _ _),
        Measure.withDensity_rnDeriv_eq _ _ (hac (hpush hμ N))]
  -- total variation `≤ ‖∑_{n<N} Pⁿ x‖₁`
  have hTV : ∀ N, tvMass (∑ n ∈ Finset.range N, pushIter π n μ₀)
      (∑ n ∈ Finset.range N, pushIter π n μ₁)
      ≤ eLpNorm (⇑(birkhoffSum (⇑P) _root_.id N x)) 1 ν := by
    intro N
    rw [hW h₀ N, hW h₁ N]
    refine (tvMass_withDensity_le ν
      (Finset.measurable_sum _ fun n _ => Measure.measurable_rnDeriv _ _)
      (Finset.measurable_sum _ fun n _ => Measure.measurable_rnDeriv _ _)).trans (le_of_eq ?_)
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr_ae ?_
    have hf0 : ∀ᵐ s ∂ν, ∀ n, (pushIter π n μ₀).rnDeriv ν s < ∞ :=
      ae_all_iff.2 fun n => Measure.rnDeriv_lt_top _ _
    have hf1 : ∀ᵐ s ∂ν, ∀ n, (pushIter π n μ₁).rnDeriv ν s < ∞ :=
      ae_all_iff.2 fun n => Measure.rnDeriv_lt_top _ _
    filter_upwards [hsumL N, hf0, hf1] with s hs h0 h1
    rw [hs]
    have hD0 : ∑ n ∈ Finset.range N, (pushIter π n μ₀).rnDeriv ν s ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun n _ => (h0 n).ne
    have hD1 : ∑ n ∈ Finset.range N, (pushIter π n μ₁).rnDeriv ν s ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun n _ => (h1 n).ne
    rw [tsub_add_tsub_eq_ofReal_abs hD0 hD1, Real.enorm_eq_ofReal_abs,
      ENNReal.toReal_sum (fun n _ => (h0 n).ne), ENNReal.toReal_sum (fun n _ => (h1 n).ne),
      ← Finset.sum_sub_distrib]
  -- `‖·‖₁ ≤ ν(𝒮)^{1/2} ‖·‖₂`, and the Cesàro averages tend to `0`
  set c : ℝ≥0∞ := ν Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hc
  have hctop : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hnorm : ∀ y : Lp ℝ 2 ν, eLpNorm (⇑y) 2 ν = ENNReal.ofReal ‖y‖ := fun y => by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top y)]
  have hT : Tendsto (fun N => ENNReal.ofReal ‖birkhoffAverage ℝ (⇑P) _root_.id N x‖ * c) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun N => ‖birkhoffAverage ℝ (⇑P) _root_.id N x‖) atTop (𝓝 0) := by
      simpa using hlim.norm
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hctop)
  obtain ⟨N, hN1, hN⟩ := ((eventually_ge_atTop 1).and (hT.eventually (gt_mem_nhds hη))).exists
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hbs : birkhoffSum (⇑P) _root_.id N x = (N : ℝ) • birkhoffAverage ℝ (⇑P) _root_.id N x := by
    rw [birkhoffAverage, smul_inv_smul₀ hN0]
  refine ⟨N, hN1, ?_⟩
  calc tvMass (∑ n ∈ Finset.range N, pushIter π n μ₀) (∑ n ∈ Finset.range N, pushIter π n μ₁)
      ≤ eLpNorm (⇑(birkhoffSum (⇑P) _root_.id N x)) 1 ν := hTV N
    _ ≤ eLpNorm (⇑(birkhoffSum (⇑P) _root_.id N x)) 2 ν * c :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (Lp.aestronglyMeasurable _)
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal ‖birkhoffAverage ℝ (⇑P) _root_.id N x‖ * c) := by
        rw [hnorm, hbs, norm_smul, Real.norm_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, mul_assoc]
    _ < (N : ℝ≥0∞) * η :=
        ENNReal.mul_lt_mul_right (by exact_mod_cast (show N ≠ 0 by omega))
          (ENNReal.natCast_ne_top N) hN

/-! ## The Cesàro-weighted Neumann outflow -/

/-- `∑_{T<N} (∑_{t≤T} μ₀πᵗ + (R − ∑_{t≤T} μ₁πᵗ))`; divided by `N`, the outflow of
`universality_of_ergodic`. Its `μ₀`-part is `∑_{t<N} (N − t) μ₀πᵗ`: `N` times the Cesàro-weighted
Neumann series `∑_{t<N} (1 − t/N) μ₀πᵗ`. -/
noncomputable def cesaroOutflow (π : Kernel S S) (μ₀ μ₁ R : Measure S) (N : ℕ) : Measure S :=
  ∑ T ∈ Finset.range N, (∑ t ∈ Finset.range (T + 1), pushIter π t μ₀
    + (R - ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁))

/-- **The Cesàro construction**: with `R = Rπ` dominating every partial sum `∑_{t≤T} μ₁πᵗ`,
`T < N`, the outflow `cesaroOutflow` has defect at most the Cesàro sum
`‖∑_{T<N} (μ₀ − μ₁)π^{T+1}‖_TV`: `(I − π)∑_{t<N}(1 − t/N)πᵗ = 1 − (1/N)∑_{t=1..N} πᵗ`. -/
theorem tvMass_construction_cesaro (π : Kernel S S) [IsMarkovKernel π] (μ₀ μ₁ R : Measure S)
    [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁] [IsFiniteMeasure R] (hR : R.bind π = R) (N : ℕ)
    (hB : ∀ T ∈ Finset.range N, ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁ ≤ R) :
    tvMass ((N : ℝ≥0∞) • μ₀ + (cesaroOutflow π μ₀ μ₁ R N).bind π)
        ((N : ℝ≥0∞) • μ₁ + cesaroOutflow π μ₀ μ₁ R N)
      ≤ tvMass (∑ T ∈ Finset.range N, pushIter π (T + 1) μ₀)
        (∑ T ∈ Finset.range N, pushIter π (T + 1) μ₁) := by
  classical
  set A : ℕ → Measure S := fun T => ∑ t ∈ Finset.range (T + 1), pushIter π t μ₀ with hA
  set B : ℕ → Measure S := fun T => ∑ t ∈ Finset.range (T + 1), pushIter π t μ₁ with hB'
  -- the identities of `tvMass_construction`, for each `T < N`
  have hT : ∀ T ∈ Finset.range N,
      μ₀ + (A T + (R - B T)).bind π + (μ₁ + (B T).bind π)
          = (A T + R + μ₁) + pushIter π (T + 1) μ₀ ∧
        μ₁ + (A T + (R - B T)) + (μ₁ + (B T).bind π) = (A T + R + μ₁) + pushIter π (T + 1) μ₁ := by
    intro T hTN
    have h0 : μ₀ + (A T).bind π = A T + pushIter π (T + 1) μ₀ := shift_sum π T μ₀
    have h1 : μ₁ + (B T).bind π = B T + pushIter π (T + 1) μ₁ := shift_sum π T μ₁
    have hRB' : (R - B T) + B T = R := Measure.sub_add_cancel_of_le (hB T hTN)
    set D := R - B T with hD
    have hRB : D.bind π + (B T).bind π = R := by rw [← bind_add_measure, hRB', hR]
    set Aa := A T
    set Bb := B T
    set p := pushIter π (T + 1) μ₀
    set q := pushIter π (T + 1) μ₁
    constructor
    · rw [bind_add_measure]
      calc μ₀ + (Aa.bind π + D.bind π) + (μ₁ + Bb.bind π)
          = (μ₀ + Aa.bind π) + (D.bind π + Bb.bind π) + μ₁ := by abel
        _ = (Aa + p) + R + μ₁ := by rw [h0, hRB]
        _ = (Aa + R + μ₁) + p := by abel
    · calc μ₁ + (Aa + D) + (μ₁ + Bb.bind π) = μ₁ + Aa + D + (μ₁ + Bb.bind π) := by abel
        _ = μ₁ + Aa + D + (Bb + q) := by rw [h1]
        _ = μ₁ + Aa + (D + Bb) + q := by abel
        _ = (Aa + R + μ₁) + q := by rw [hRB']; abel
  -- summed over `T < N`
  have hX : (N : ℝ≥0∞) • μ₀ + (cesaroOutflow π μ₀ μ₁ R N).bind π
        + ∑ T ∈ Finset.range N, (μ₁ + (B T).bind π)
      = ∑ T ∈ Finset.range N, (A T + R + μ₁)
        + ∑ T ∈ Finset.range N, pushIter π (T + 1) μ₀ := by
    have h1 : (N : ℝ≥0∞) • μ₀ = ∑ T ∈ Finset.range N, μ₀ := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]
    have h2 : (cesaroOutflow π μ₀ μ₁ R N).bind π
        = ∑ T ∈ Finset.range N, (A T + (R - B T)).bind π :=
      bind_finset_sum π _ _
    rw [h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T hT' => (hT T hT').1
  have hY : (N : ℝ≥0∞) • μ₁ + cesaroOutflow π μ₀ μ₁ R N
        + ∑ T ∈ Finset.range N, (μ₁ + (B T).bind π)
      = ∑ T ∈ Finset.range N, (A T + R + μ₁)
        + ∑ T ∈ Finset.range N, pushIter π (T + 1) μ₁ := by
    have h1 : (N : ℝ≥0∞) • μ₁ = ∑ T ∈ Finset.range N, μ₁ := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]
    have h2 : cesaroOutflow π μ₀ μ₁ R N = ∑ T ∈ Finset.range N, (A T + (R - B T)) := rfl
    rw [h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T hT' => (hT T hT').2
  haveI : IsFiniteMeasure ((N : ℝ≥0∞) • μ₀) := Measure.smul_finite _ (ENNReal.natCast_ne_top N)
  haveI : IsFiniteMeasure ((N : ℝ≥0∞) • μ₁) := Measure.smul_finite _ (ENNReal.natCast_ne_top N)
  haveI : IsFiniteMeasure (cesaroOutflow π μ₀ μ₁ R N) := by unfold cesaroOutflow; infer_instance
  calc tvMass ((N : ℝ≥0∞) • μ₀ + (cesaroOutflow π μ₀ μ₁ R N).bind π)
        ((N : ℝ≥0∞) • μ₁ + cesaroOutflow π μ₀ μ₁ R N)
      ≤ tvMass ((N : ℝ≥0∞) • μ₀ + (cesaroOutflow π μ₀ μ₁ R N).bind π
          + ∑ T ∈ Finset.range N, (μ₁ + (B T).bind π))
          ((N : ℝ≥0∞) • μ₁ + cesaroOutflow π μ₀ μ₁ R N
          + ∑ T ∈ Finset.range N, (μ₁ + (B T).bind π)) := tvMass_le_add_right _ _ _
    _ = tvMass (∑ T ∈ Finset.range N, (A T + R + μ₁)
          + ∑ T ∈ Finset.range N, pushIter π (T + 1) μ₀)
          (∑ T ∈ Finset.range N, (A T + R + μ₁)
          + ∑ T ∈ Finset.range N, pushIter π (T + 1) μ₁) := by rw [hX, hY]
    _ ≤ _ := tvMass_add_left_le _ _ _

/-- The total variation scales: `‖cμ − cν‖_TV ≤ c ‖μ − ν‖_TV`. -/
theorem tvMass_smul_le (c : ℝ≥0∞) (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvMass (c • μ) (c • ν) ≤ c * tvMass μ ν := by
  have key : ∀ (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      c • μ - c • ν ≤ c • (μ - ν) := by
    intro μ ν _ _
    refine Measure.sub_le_of_le_add ?_
    have h1 : μ ≤ (μ - ν) + ν := Measure.sub_le_iff_le_add.mp le_rfl
    refine Measure.le_iff'.mpr fun s => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [← mul_add]
    have h1s : μ s ≤ (μ - ν) s + ν s := by simpa using h1 s
    gcongr
  unfold tvMass
  calc (c • μ - c • ν) Set.univ + (c • ν - c • μ) Set.univ
      ≤ (c • (μ - ν)) Set.univ + (c • (ν - μ)) Set.univ :=
        add_le_add (key μ ν Set.univ) (key ν μ Set.univ)
    _ = c * ((μ - ν) Set.univ + (ν - μ) Set.univ) := by
        simp only [Measure.smul_apply, smul_eq_mul, mul_add]

/-! ## Sufficiency -/

/-- **Theorem B.1 without mixing** (C-29, sufficiency): for a Markov kernel `π` on a finite
`(𝒮, λ)` which is ergodic for a finite invariant measure `λ̂` equivalent to `λ`, any probability
measures `F_init, F_term ≪ λ` and any `ε > 0`, there is a bounded `f_out ≥ 0` in `L²(λ)` such that
the generative flow `(π, f_out λ)` from `F_init` to `F_term` has `δF_init(𝒮) + δF_term(𝒮) < ε`.
The conclusion is that of `EGF.main_universality`, verbatim; no mixing is assumed. -/
theorem universality_of_ergodic (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (lamHat : Measure S) [IsFiniteMeasure lamHat]
    (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat)
    (herg : IsKernelErgodic π lamHat) (Finit Fterm : Measure S) [IsProbabilityMeasure Finit]
    [IsProbabilityMeasure Fterm] (hinit : Finit ≪ lam) (hterm : Fterm ≪ lam) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧ MemLp fout 2 lam ∧
      initialError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        + terminalError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        < ε := by
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  suffices h : ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧
      MemLp fout 2 lam ∧
      tvMass (Finit + inflow π (lam.withDensity fun s => ENNReal.ofReal (fout s)))
        (Fterm + lam.withDensity fun s => ENNReal.ofReal (fout s)) < ε' by
    obtain ⟨fout, h1, h2, h3, h4⟩ := h
    exact ⟨fout, h1, h2, h3, by rw [errors_eq_tvMass]; exact h4.trans_le hε'le⟩
  set δ := ε' / 5 with hδ
  have hδpos : 0 < δ := ENNReal.div_pos hε'pos.ne' (by norm_num)
  have h5δ : δ + δ + δ + δ + δ ≤ ε' := by
    have : δ + δ + δ + δ + δ = 5 * (ε' / 5) := by rw [hδ]; ring
    rw [this]; exact ENNReal.mul_div_le
  -- truncated initial and terminal densities (`EGF.exists_truncation`)
  obtain ⟨a, ham, Ka, haK, hag, ha1, hFa⟩ := exists_truncation lam lamHat hac' Finit hinit hδpos
  obtain ⟨b, hbm, Kb, hbK, hbg, hb1, hFb⟩ := exists_truncation lam lamHat hac' Fterm hterm hδpos
  set K : ℝ≥0 := max Ka Kb with hK
  have hKa : (Ka : ℝ≥0∞) ≤ K := by exact_mod_cast le_max_left Ka Kb
  have hKb : (Kb : ℝ≥0∞) ≤ K := by exact_mod_cast le_max_right Ka Kb
  set g := lamHat.rnDeriv lam with hg
  have hag' : ∀ s, a s ≤ K * g s := fun s => (hag s).trans (by gcongr)
  have hbg' : ∀ s, b s ≤ K * g s := fun s => (hbg s).trans (by gcongr)
  have hlamHat : lam.withDensity g = lamHat := Measure.withDensity_rnDeriv_eq lamHat lam hac
  set μ₀ := lam.withDensity a with hμ₀
  set μ₁ := lam.withDensity b with hμ₁
  haveI : IsProbabilityMeasure μ₀ :=
    ⟨by rw [hμ₀, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ha1]⟩
  haveI : IsProbabilityMeasure μ₁ :=
    ⟨by rw [hμ₁, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hb1]⟩
  -- domination by `K λ̂`, preserved by the kernel
  have hdom : ∀ {c : S → ℝ≥0∞}, (∀ s, c s ≤ K * g s) →
      lam.withDensity c ≤ (K : ℝ≥0∞) • lamHat := by
    intro c hc
    rw [← hlamHat, ← withDensity_smul _ (Measure.measurable_rnDeriv _ _)]
    exact withDensity_mono (ae_of_all _ fun s => by simpa using hc s)
  have hpush : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • lamHat → ∀ t,
      pushIter π t μ ≤ (K : ℝ≥0∞) • lamHat := by
    intro μ hμ t
    calc pushIter π t μ ≤ pushIter π t ((K : ℝ≥0∞) • lamHat) := pushIter_mono π t hμ
      _ = (K : ℝ≥0∞) • lamHat := by rw [pushIter_smul, pushIter_of_bind_eq π hinv]
  -- Cesàro mixing in total variation (von Neumann)
  have hmass : μ₀ Set.univ = μ₁ Set.univ := by rw [measure_univ, measure_univ]
  obtain ⟨N, hN, hNlt⟩ := exists_tvMass_cesaro_lt_of_ergodic π lamHat hinv herg K (hdom hag')
    (hdom hbg') hmass hδpos
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  -- the invariant lift `R = N K λ̂`
  set R : Measure S := ((N : ℝ≥0∞) * (K : ℝ≥0∞)) • lamHat with hRdef
  have hR : R.bind π = R := by rw [hRdef, Measure.bind_smul, hinv]
  haveI : IsFiniteMeasure R :=
    Measure.smul_finite _ (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top)
  have hRac : R ≪ lamHat := Measure.AbsolutelyContinuous.rfl.smul_left _
  have hsumle : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • lamHat → ∀ T ∈ Finset.range N,
      ∑ t ∈ Finset.range (T + 1), pushIter π t μ ≤ R := by
    intro μ hμ T hT
    calc ∑ t ∈ Finset.range (T + 1), pushIter π t μ
        ≤ (Finset.range (T + 1)).card • ((K : ℝ≥0∞) • lamHat) :=
          Finset.sum_le_card_nsmul _ _ _ fun t _ => hpush hμ t
      _ ≤ R := by
          rw [Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, hRdef]
          refine Measure.le_iff'.mpr fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          have hTN : ((T + 1 : ℕ) : ℝ≥0∞) ≤ N := by
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hT)
          gcongr
  -- the Cesàro-weighted Neumann outflow
  set G := cesaroOutflow π μ₀ μ₁ R N with hGdef
  haveI : IsFiniteMeasure G := by rw [hGdef]; unfold cesaroOutflow; infer_instance
  set F : Measure S := (N : ℝ≥0∞)⁻¹ • G with hFdef
  haveI : IsFiniteMeasure F := Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hNne)
  have hFconstr : tvMass (μ₀ + F.bind π) (μ₁ + F) < δ := by
    have h1 := tvMass_construction_cesaro π μ₀ μ₁ R hR N (hsumle (hdom hbg'))
    have hshift : ∀ μ : Measure S, ∑ T ∈ Finset.range N, pushIter π (T + 1) μ
        = (∑ T ∈ Finset.range N, pushIter π T μ).bind π := by
      intro μ; rw [bind_finset_sum]; simp_rw [pushIter_succ]
    rw [hshift, hshift] at h1
    have h2 := (h1.trans (tvMass_bind_le π _ _)).trans_lt hNlt
    haveI : IsFiniteMeasure ((N : ℝ≥0∞) • μ₀) := Measure.smul_finite _ hNtop
    haveI : IsFiniteMeasure ((N : ℝ≥0∞) • μ₁) := Measure.smul_finite _ hNtop
    have e0 : μ₀ + F.bind π = (N : ℝ≥0∞)⁻¹ • ((N : ℝ≥0∞) • μ₀ + G.bind π) := by
      rw [hFdef, smul_add, smul_smul, ENNReal.inv_mul_cancel hNne hNtop, one_smul,
        Measure.bind_smul]
    have e1 : μ₁ + F = (N : ℝ≥0∞)⁻¹ • ((N : ℝ≥0∞) • μ₁ + G) := by
      rw [hFdef, smul_add, smul_smul, ENNReal.inv_mul_cancel hNne hNtop, one_smul]
    rw [e0, e1]
    calc tvMass ((N : ℝ≥0∞)⁻¹ • ((N : ℝ≥0∞) • μ₀ + G.bind π))
          ((N : ℝ≥0∞)⁻¹ • ((N : ℝ≥0∞) • μ₁ + G))
        ≤ (N : ℝ≥0∞)⁻¹ * tvMass ((N : ℝ≥0∞) • μ₀ + G.bind π) ((N : ℝ≥0∞) • μ₁ + G) :=
          tvMass_smul_le _ _ _
      _ < (N : ℝ≥0∞)⁻¹ * ((N : ℝ≥0∞) * δ) :=
          ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hNtop) (ENNReal.inv_ne_top.mpr hNne) h2
      _ = δ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hNne hNtop, one_mul]
  -- the outflow is `≪ λ`
  have hpac : ∀ {μ : Measure S}, μ ≤ (K : ℝ≥0∞) • lamHat → ∀ T,
      ∑ t ∈ Finset.range (T + 1), pushIter π t μ ≪ lamHat := by
    intro μ hμ T
    refine (finsetSum_ac_iff _ _ _).2 fun t _ => ?_
    exact (Measure.absolutelyContinuous_of_le (hpush hμ t)).trans
      (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hGac : G ≪ lamHat := by
    rw [hGdef]; unfold cesaroOutflow
    refine (finsetSum_ac_iff _ _ _).2 fun T _ => ?_
    exact (hpac (hdom hag') T).add_left
      ((Measure.absolutelyContinuous_of_le Measure.sub_le).trans hRac)
  have hFac : F ≪ lam := (hGac.smul_left _).trans hac
  -- the density of the outflow, truncated at a finite level (as in `main_universality_of_tendsto`)
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
  have hconv' : Tendsto (fun M : ℕ => ∫⁻ s, f s ∂lam - ∫⁻ s, min (f s) M ∂lam) atTop
      (𝓝 0) := by
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
    have e3 : tvMass (μ₀ + F.bind π) (μ₁ + F) < δ := hFconstr
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

/-- `universality_of_ergodic` in the `IsUniversalPolicy` form. -/
theorem isUniversalPolicy_of_ergodic (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (lamHat : Measure S) [IsFiniteMeasure lamHat]
    (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat)
    (herg : IsKernelErgodic π lamHat) : IsUniversalPolicy lam π := by
  intro Finit Fterm h1 h2 hinit hterm ε hε
  haveI := h1
  haveI := h2
  exact universality_of_ergodic lam π lamHat hinv hac hac' herg Finit Fterm hinit hterm hε

/-! ## Necessity -/

/-- **An invariant set blocks the flow**: if `π(x, A) = 𝟙_A(x)` `λ`-a.e., `F_init` lives on `A`
and `F_term` on `Aᶜ` (both probabilities), then every finite outflow `F_out ≪ λ` has
`δF_init(𝒮) + δF_term(𝒮) ≥ 2`, since `(F_out π)(A) = F_out(A)`. -/
theorem two_le_errors_of_invariant_set (lam : Measure S) (π : Kernel S S) [IsMarkovKernel π]
    {A : Set S} (hA : MeasurableSet A) (hinvA : ∀ᵐ x ∂lam, π x A = A.indicator 1 x)
    (Finit Fterm Fout : Measure S) [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm]
    [IsFiniteMeasure Fout] (hout : Fout ≪ lam) (hiA : Finit A = 1) (hiAc : Finit Aᶜ = 0)
    (htA : Fterm A = 0) (htAc : Fterm Aᶜ = 1) :
    2 ≤ initialError π Fout Finit Fterm Set.univ + terminalError π Fout Finit Fterm Set.univ := by
  -- `π(x, Aᶜ) = 𝟙_{Aᶜ}(x)` as well
  have hinvAc : ∀ᵐ x ∂lam, π x Aᶜ = Aᶜ.indicator 1 x := by
    filter_upwards [hinvA] with x hx
    rw [prob_compl_eq_one_sub hA, hx]
    by_cases h : x ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h)]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h)]
      simp
  -- an outflow `≪ λ` is fixed on invariant sets: `(F_out π)(B) = F_out(B)`
  have hbind : ∀ {B : Set S}, MeasurableSet B → (∀ᵐ x ∂lam, π x B = B.indicator 1 x) →
      (Fout.bind π) B = Fout B := by
    intro B hB hBinv
    rw [Measure.bind_apply hB π.aemeasurable]
    calc ∫⁻ x, π x B ∂Fout = ∫⁻ x, B.indicator 1 x ∂Fout := lintegral_congr_ae (hout.ae_le hBinv)
      _ = Fout B := lintegral_indicator_one hB
  rw [errors_eq_tvMass]
  unfold tvMass
  have hinflA : (inflow π Fout) A = Fout A := hbind hA hinvA
  have hinflAc : (inflow π Fout) Aᶜ = Fout Aᶜ := hbind hA.compl hinvAc
  have h1 : 1 ≤ ((Finit + inflow π Fout) - (Fterm + Fout)) Set.univ := by
    have hle : Finit + inflow π Fout ≤ ((Finit + inflow π Fout) - (Fterm + Fout)) + (Fterm + Fout) :=
      Measure.sub_le_iff_le_add.mp le_rfl
    have := hle A
    simp only [Measure.add_apply] at this
    rw [hinflA, hiA, htA, zero_add] at this
    exact ((ENNReal.add_le_add_iff_right (measure_ne_top Fout A)).mp this).trans
      (measure_mono (Set.subset_univ A))
  have h2 : 1 ≤ ((Fterm + Fout) - (Finit + inflow π Fout)) Set.univ := by
    have hle : Fterm + Fout ≤ ((Fterm + Fout) - (Finit + inflow π Fout)) + (Finit + inflow π Fout) :=
      Measure.sub_le_iff_le_add.mp le_rfl
    have := hle Aᶜ
    simp only [Measure.add_apply] at this
    rw [hinflAc, hiAc, htAc, zero_add] at this
    exact ((ENNReal.add_le_add_iff_right (measure_ne_top Fout Aᶜ)).mp this).trans
      (measure_mono (Set.subset_univ Aᶜ))
  calc (2 : ℝ≥0∞) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ _ := add_le_add h1 h2

/-- **Necessity** (C-29): if `π` is not ergodic for `λ`, there are probability measures
`F_init, F_term ≪ λ` with bounded densities (`λ|_A/λ(A)` and `λ|_{Aᶜ}/λ(Aᶜ)` for an invariant
`A` with `0 < λ(A) < λ(𝒮)`) such that every finite outflow `F_out ≪ λ` has
`δF_init(𝒮) + δF_term(𝒮) ≥ 2`. Any Markov `π`, any finite `λ`; no invariant measure is needed. -/
theorem not_universal_of_not_ergodic (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (herg : ¬ IsKernelErgodic π lam) :
    ∃ Finit Fterm : Measure S, IsProbabilityMeasure Finit ∧ IsProbabilityMeasure Fterm ∧
      Finit ≪ lam ∧ Fterm ≪ lam ∧
      (∃ C : ℝ≥0, ∀ᵐ s ∂lam, Finit.rnDeriv lam s ≤ C) ∧
      (∃ C : ℝ≥0, ∀ᵐ s ∂lam, Fterm.rnDeriv lam s ≤ C) ∧
      ∀ Fout : Measure S, IsFiniteMeasure Fout → Fout ≪ lam →
        2 ≤ initialError π Fout Finit Fterm Set.univ + terminalError π Fout Finit Fterm Set.univ := by
  simp only [IsKernelErgodic, not_forall, not_or, exists_prop] at herg
  obtain ⟨A, hA, hinvA, hA0, hAc0⟩ := herg
  -- `λ(B ∩ ·)`-measures with constant density on `B`
  have hval : ∀ {B : Set S}, MeasurableSet B → ∀ (c : ℝ≥0∞) {C : Set S}, MeasurableSet C →
      lam.withDensity (B.indicator fun _ => c) C = c * lam (B ∩ C) := by
    intro B hB c C hC
    rw [withDensity_apply _ hC, lintegral_indicator_const hB, Measure.restrict_apply hB]
  have hprob : ∀ {B : Set S}, MeasurableSet B → lam B ≠ 0 →
      IsProbabilityMeasure (lam.withDensity (B.indicator fun _ => (lam B)⁻¹)) := by
    intro B hB hB0
    refine ⟨?_⟩
    rw [hval hB _ MeasurableSet.univ, Set.inter_univ]
    exact ENNReal.inv_mul_cancel hB0 (measure_ne_top _ _)
  have hbdd : ∀ {B : Set S}, MeasurableSet B → lam B ≠ 0 → ∃ C : ℝ≥0, ∀ᵐ s ∂lam,
      (lam.withDensity (B.indicator fun _ => (lam B)⁻¹)).rnDeriv lam s ≤ C := by
    intro B hB hB0
    refine ⟨((lam B)⁻¹).toNNReal, ?_⟩
    filter_upwards [Measure.rnDeriv_withDensity lam (measurable_const.indicator hB)] with s hs
    rw [hs, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hB0)]
    by_cases h : s ∈ B
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; exact zero_le
  have hAc : MeasurableSet Aᶜ := hA.compl
  haveI := hprob hA hA0
  haveI := hprob hAc hAc0
  refine ⟨lam.withDensity (A.indicator fun _ => (lam A)⁻¹),
    lam.withDensity (Aᶜ.indicator fun _ => (lam Aᶜ)⁻¹), inferInstance, inferInstance,
    withDensity_absolutelyContinuous _ _, withDensity_absolutelyContinuous _ _, hbdd hA hA0,
    hbdd hAc hAc0, fun Fout hFin hout => ?_⟩
  haveI := hFin
  refine two_le_errors_of_invariant_set lam π hA hinvA _ _ Fout hout ?_ ?_ ?_ ?_
  · rw [hval hA _ hA, Set.inter_self]; exact ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _)
  · rw [hval hA _ hAc, Set.inter_compl_self, measure_empty, mul_zero]
  · rw [hval hAc _ hA, Set.compl_inter_self, measure_empty, mul_zero]
  · rw [hval hAc _ hAc, Set.inter_self]; exact ENNReal.inv_mul_cancel hAc0 (measure_ne_top _ _)

/-- **A universal policy is ergodic** for `λ` (any Markov `π`, finite `λ`). -/
theorem isKernelErgodic_of_isUniversalPolicy (lam : Measure S) [IsFiniteMeasure lam]
    (π : Kernel S S) [IsMarkovKernel π] (h : IsUniversalPolicy lam π) : IsKernelErgodic π lam := by
  by_contra herg
  obtain ⟨Finit, Fterm, h1, h2, hi, ht, -, -, hall⟩ := not_universal_of_not_ergodic lam π herg
  obtain ⟨fout, -, -, hL, hlt⟩ := h Finit Fterm h1 h2 hi ht 1 one_pos
  haveI := h1
  haveI := h2
  have hfin : IsFiniteMeasure (lam.withDensity fun s => ENNReal.ofReal (fout s)) :=
    isFiniteMeasure_withDensity_ofReal (hL.integrable one_le_two).hasFiniteIntegral
  have h2le := hall _ hfin (withDensity_absolutelyContinuous _ _)
  exact absurd (h2le.trans_lt hlt) (not_lt.mpr one_le_two)

/-- **Universality iff ergodicity** (C-29): for a Markov kernel with a finite invariant measure
`λ̂` equivalent to the finite `λ`, `π` is universal iff it is ergodic for `λ̂`. -/
theorem universal_iff_ergodic (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (lamHat : Measure S) [IsFiniteMeasure lamHat]
    (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat) :
    IsUniversalPolicy lam π ↔ IsKernelErgodic π lamHat := by
  constructor
  · intro h
    exact (isKernelErgodic_congr hac' hac).mp (isKernelErgodic_of_isUniversalPolicy lam π h)
  · exact isUniversalPolicy_of_ergodic lam π lamHat hinv hac hac'

/-! ## Families (Theorem 3.4 with ergodicity) -/

/-- **Theorem 3.4 with ergodicity for summable mixing** (C-29 with C-18, C-20): on a finite
`(𝒮, λ)`, a family containing `(π, f⁺ λ)` for a kernel `π` ergodic for a finite invariant `λ̂ ~ λ`
and every `f` of a set `D` dense in the non-negative cone of `L²(λ)` is ε-universal. -/
theorem universality_of_ergodic_family (lam : Measure S) [IsFiniteMeasure lam]
    (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S) (lamHat : Measure S) [IsFiniteMeasure lamHat]
    (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat)
    (herg : IsKernelErgodic π lamHat) (D : Set (S → ℝ))
    (hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s))
    (hdense : IsDenseNonnegConeL2 lam D) : IsUniversalFamilyEps lam 𝓕 := by
  obtain ⟨f, hfD, -, -⟩ := hdense 0 MemLp.zero (fun _ => le_rfl) 1 one_pos
  obtain ⟨F, -, hFπ, -⟩ := hD f hfD
  haveI : IsMarkovKernel π := hFπ ▸ F.isMarkovKernel_policy
  exact isUniversalFamilyEps_of_policy_of_isDenseNonnegConeL2 lam 𝓕 π
    (isUniversalPolicy_of_ergodic lam π lamHat hinv hac hac' herg) D hD hdense

/-- **The converse at the family level**: a family whose members all have policy `π` and outflows
`≪ λ` is not ε-universal when `π` is not ergodic for `λ`. -/
theorem not_isUniversalFamilyEps_of_not_ergodic (lam : Measure S) [IsFiniteMeasure lam]
    (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S) [IsMarkovKernel π]
    (h𝓕 : ∀ F ∈ 𝓕, F.policy = π ∧ F.outflow ≪ lam) (herg : ¬ IsKernelErgodic π lam) :
    ¬ IsUniversalFamilyEps lam 𝓕 := by
  intro hU
  obtain ⟨Finit, Fterm, h1, h2, hi, ht, hbi, hbt, hall⟩ := not_universal_of_not_ergodic lam π herg
  obtain ⟨F, hF, hlt⟩ := hU Fterm Finit h2 h1 ht hi hbt hbi 1 one_pos
  obtain ⟨hFπ, hFac⟩ := h𝓕 F hF
  have h2le := hall F.outflow inferInstance hFac
  rw [hFπ] at hlt
  exact absurd (h2le.trans_lt hlt) (not_lt.mpr one_le_two)

/-- **The fixed-policy family `{π} × L²₊(λ)` is ε-universal iff `π` is ergodic**, for `π` with a
finite invariant `λ̂ ~ λ`. -/
theorem isUniversalFamilyEps_fixedPolicyFamily_iff (lam : Measure S) [IsFiniteMeasure lam]
    (π : Kernel S S) [IsMarkovKernel π] (lamHat : Measure S) [IsFiniteMeasure lamHat]
    (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam) (hac' : lam ≪ lamHat) :
    IsUniversalFamilyEps lam (fixedPolicyFamily lam π) ↔ IsKernelErgodic π lamHat := by
  constructor
  · intro h
    refine (isKernelErgodic_congr hac' hac).mp ?_
    by_contra herg
    refine not_isUniversalFamilyEps_of_not_ergodic lam _ π (fun F hF => ⟨hF.1, ?_⟩) herg h
    obtain ⟨-, f, -, -, hf⟩ := hF
    rw [hf]; exact withDensity_absolutelyContinuous _ _
  · intro herg
    refine universality_of_ergodic_family lam _ π lamHat hinv hac hac' herg
      {f | MemLp f 2 lam ∧ ∀ s, 0 ≤ f s} (fun f hf => ?_)
      (fun g hg hgnn η hη => ⟨g, ⟨hg, hgnn⟩, hg.1, by simpa using hη⟩)
    haveI : IsFiniteMeasure (lam.withDensity fun s => ENNReal.ofReal (f s)) :=
      isFiniteMeasure_withDensity_ofReal (hf.1.integrable one_le_two).hasFiniteIntegral
    let F : GenerativeFlow S :=
      ⟨π, lam.withDensity (fun s => ENNReal.ofReal (f s)), inferInstance, inferInstance⟩
    exact ⟨F, ⟨rfl, f, hf.1, hf.2, rfl⟩, rfl, rfl⟩

/-! ## Mixing implies ergodicity -/

/-- **`γ₀ < ∞` and `γₙ → 0` force ergodicity** of `(π, λ̂)` (the ledger's finding on
`main.tex:775`, formalized): through `main_universality_of_tendsto` and necessity. -/
theorem isKernelErgodic_of_tendsto (lam : Measure S) [IsFiniteMeasure lam] (π : Kernel S S)
    [IsMarkovKernel π] (lamHat : Measure S) (hinv : lamHat.bind π = lamHat) (hac : lamHat ≪ lam)
    (hac' : lam ≪ lamHat) (hγ0 : mixingCoeff π lam lamHat 0 ≠ ∞)
    (hγ : Tendsto (mixingCoeff π lam lamHat) atTop (𝓝 0)) : IsKernelErgodic π lamHat := by
  have hU : IsUniversalPolicy lam π := by
    intro Finit Fterm h1 h2 hinit hterm ε hε
    haveI := h1
    haveI := h2
    exact main_universality_of_tendsto lam π lamHat hinv hac hac' hγ0 hγ Finit Fterm hinit hterm hε
  exact (isKernelErgodic_congr hac' hac).mp (isKernelErgodic_of_isUniversalPolicy lam π hU)

/-- **A summably `L²`-mixing kernel is ergodic** for `λ` (hence for its `λ̂`): "ergodic" in
`main.tex:775` is implied by the mixing clause. -/
theorem isKernelErgodic_of_isSummablyL2Mixing (lam : Measure S) [IsFiniteMeasure lam]
    (π : Kernel S S) [IsMarkovKernel π] (hmix : IsSummablyL2Mixing π lam) :
    IsKernelErgodic π lam :=
  isKernelErgodic_of_isUniversalPolicy lam π (isUniversalPolicy_of_isSummablyL2Mixing lam π hmix)

/-! ## A non-mixing universal policy: a translation of the circle -/

/-- **One translation of infinite order of the circle is a universal policy** (`main.tex:697`:
"one randomly initialized non-trainable translation is sufficient to ensure ergodicity"): the
kernel `y ↦ δ_{a + y}` on `AddCircle T` with its Haar measure, `addOrderOf a = 0`. -/
theorem isUniversalPolicy_addCircle {T : ℝ} [Fact (0 < T)] {a : AddCircle T}
    (ha : addOrderOf a = 0) :
    IsUniversalPolicy (volume : Measure (AddCircle T))
      (Kernel.deterministic (a + ·) (measurable_const_add a)) := by
  have herg : Ergodic (a + ·) (volume : Measure (AddCircle T)) := (AddCircle.ergodic_add_left (a := a)).mpr ha
  obtain ⟨hinv, hke⟩ := isKernelErgodic_deterministic (measurable_const_add a) herg
  exact isUniversalPolicy_of_ergodic volume _ volume hinv Measure.AbsolutelyContinuous.rfl
    Measure.AbsolutelyContinuous.rfl hke

/-! ## A non-mixing universal policy on two points: the swap -/

namespace Swap

/-- The swap `b ↦ ¬b` (the policy of `EGF.Swap.flow`) leaves the uniform `λ` on `Bool`
invariant. -/
theorem bind_policy_lam : Coin.lam.bind flow.policy = Coin.lam := by
  change Coin.lam.bind (fun b => Measure.dirac (!b)) = Coin.lam
  rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _)]
  simp only [Coin.lam, Measure.map_smul, Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _)]
  simp only [Bool.not_true, Bool.not_false]
  rw [add_comm]

/-- The swap is ergodic for the uniform `λ`: an invariant set contains both points or neither. -/
theorem isKernelErgodic_policy : IsKernelErgodic flow.policy Coin.lam := by
  intro A hA hinv
  have hall : ∀ b : Bool, flow.policy b A = A.indicator 1 b := by
    intro b
    by_contra hb
    have h0 : Coin.lam {x | ¬ flow.policy x A = A.indicator 1 x} = 0 := ae_iff.mp hinv
    have hle : Coin.lam {b} ≤ Coin.lam {x | ¬ flow.policy x A = A.indicator 1 x} :=
      measure_mono (Set.singleton_subset_iff.mpr hb)
    rw [h0, Coin.lam_singleton] at hle
    exact absurd hle (by norm_num)
  have hswap : ∀ b : Bool, (!b) ∈ A ↔ b ∈ A := by
    intro b
    have h := hall b
    have e : flow.policy b A = A.indicator (fun _ => 1) (!b) :=
      Kernel.deterministic_apply' (measurable_of_countable _) _ hA
    rw [e] at h
    by_cases h1 : (!b) ∈ A <;> by_cases h2 : b ∈ A <;>
      simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
  by_cases ht : true ∈ A
  · right
    have hf : false ∈ A := (hswap true).mpr ht
    have hc : Aᶜ = ∅ := by
      ext b; cases b <;> simp [ht, hf]
    rw [hc, measure_empty]
  · left
    have hf : false ∉ A := fun h => ht ((hswap true).mp h)
    have hc : A = ∅ := by
      ext b; cases b <;> simp [ht, hf]
    rw [hc, measure_empty]

/-- **The swap is a universal policy** on `(Bool, uniform)` (`universality_of_ergodic`). It is an
involution (`φπ² = φ`), so its `L²`-mixing coefficients do not tend to `0` and `main_universality`
does not reach it; that `¬ IsSummablyL2Mixing` is T-egf-mixing-criteria's, not proved here. -/
theorem isUniversalPolicy_policy : IsUniversalPolicy Coin.lam flow.policy :=
  isUniversalPolicy_of_ergodic Coin.lam flow.policy Coin.lam bind_policy_lam
    Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl isKernelErgodic_policy

end Swap

end EGF
