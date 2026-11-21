import EGF.Universality
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The sampling theorem of generative flows, the virtual flows, and the quantitative sampling theorem

**`theo:sampling_theorem`** — `main.tex:178`

**`def:virtual_flows`** — `main.tex:316`

**`theo:negative_control`** — `main.tex:321`

**`theo:negative_control_appendix`** — `main.tex:844` (the same statement, proof `main.tex:852–867`)

Anchors: `EGF.sampling_theorem` (S-egf-3, the sampling theorem) and
`EGF.main_quantitative_sampling` (S-egf-3, both quantitative statements). Templates, never
imported (OQ-1, `kb/0001`): `GFNBounds.Core.SamplingGeneral` (`MFlow`, `MFlow.sampling_theorem`,
`MFlow.expectedTau_le`) and `GFNBounds.Core.SamplingGeneralBounds`
(`MFlow.negative_control_general`), ported over `EGF.GenerativeFlow` and `EGF.inflow`.

> A generative flow on $\Statespace$ is the data of a star forward policy, i.e. a Markov kernel
> $\ForwardPolicyStar:\Statespace\rightarrow \Statespace$, and a star outflow, i.e. a finite
> non-negative measure $\Foutstar$ on $\Statespace$. With unnormalized initial and terminal
> distributions $\Finit$ and $\Fterm$, it induces a Markov chain $(\underline s_t)_{g\geq 1}$
> defined by $\underline s_{1}\sim \Finit$and $\underline s_{t+1} =
> \ForwardPolicyStar(\underline s_t)$. Define the sampling time $\tau \in \mathbb N_{\geq 1}$ as
> the random variable given by […] $\mathbb P(\tau\geq 1)=1$ and $\mathbb P(\tau = t|\tau\geq t) =
> \frac{d\Fterm}{d(\Fterm+\Foutstar)}(\underline s_t)$. The sampler associated with a generative
> flow is obtained by emulating the Markov chain $(\underline s_t)_{t\geq1}$ and sampling
> $\underline s_\tau$. (`main.tex:161–165`)

> Let $\Finit$, and $\Fterm$ be unnormalized distributions with $\Fterm\neq0$ and let
> $(\ForwardPolicyStar, \Foutstar)$ be a generative flow. If the flow-matching constraint
> $\Finit + \Foutstar\ForwardPolicyStar = \Fterm + \Foutstar$ is satisfied then
> $\Finit(\Statespace)=\Fterm(\Statespace)$ and: $\mathbb E(\tau)\leq
> \frac{\Foutstar(\Statespace)}{\Finit(\Statespace)}+1,\quad \quad \underline s_\tau \sim \Fterm.$
> (`main.tex:180–187`)

> Let $(\ForwardPolicyStar,\foutstar)$ be a generative flow and let $\Finit,\Fterm$ be initial and
> terminal distributions. Define the initial and terminal errors as
> $\delta\Finit:=(\Finit+\Finstar-\Fterm-\Foutstar)^-$ and
> $\delta\Fterm:=(\Finit+\Finstar-\Fterm-\Foutstar)^+$ respectively. Define the positive and
> negative parts of a measure $\mu$ as ${\mu}^\pm$. The virtual initial and terminal distributions
> are $\Finithat := \Finit+ \delta\Finit$ and $\Ftermhat := \Fterm+ \delta\Fterm$. (`main.tex:316`)

> Let $(\ForwardPolicyStar, \foutstar)$ be a generative flow and let $\Finit$ and $\Fterm$ initial
> and terminal distributions. Assume that $\Finit\neq 0$ and consider the sample $s_\tau$ of the
> generative flow Markov chain from $\Finit$ to $\Ftermhat$ then:
> $\TV\left(s_\tau \left\| \frac{1}{\Ftermhat(\Statespace )} \Ftermhat\right.\right) \leq
> \frac{\delta\Finit(\Statespace)}{\Ftermhat(\Statespace)}$, with $\TV$  the total variation.
> (`main.tex:323–327`; `main.tex:846–850` is the same with a comma after "$\Finit\neq 0$")

> We may also rewrite $\TV\left(\frac{\widehat\target}{\widehat\target(\Statespace)} \left\|
> \frac{\target}{\target(\Statespace )} \right.\right) =\frac{1}{2}\sum_{s\in\Statespace}
> |\frac{\widehat r(s)}{\sum_{s'\in \Statespace}\widehat r(s')} - \frac{ r(s)}{\sum_{s'\in
> \Statespace} r(s')}|$ (`main.tex:338`)

## What is proved

| | |
|---|---|
| `virtualInit`, `virtualTerm`, `isFlowMatching_virtual`, `virtualInit_univ` | `F̂_init`, `F̂_term` over the strict `initialError`, `terminalError` (Jordan parts, `EGF.Defs`); any generative flow is flow matching from `F̂_init` to `F̂_term` (`main.tex:320`) |
| `GenerativeFlow.pathLaw`, `stopTime`, `sampledState` | the sampler on the path space (Ionescu-Tulcea): `Yₙ = (s_{n+1}, bₙ)`, `bₙ = [τ ≤ n + 1]` |
| `GenerativeFlow.pathLaw_spec`, `pathLaw_hazard_rnDeriv` | checks of the sampler, which the definition `pathKernel` fixes: `s₁ ∼ F_init`, a two-time `π`-transition identity, `τ ≥ 1`, the hazard `dF_term/d(F_term + F_out)(s_t)` given `s_t` |
| `occ`, `stopped`, `occupation`, `termLaw`, `sampleLaw`, `expectedTau` | the marginal calculus of `GFNBounds` (ported) |
| `lintegral_stopTime`, `pathLaw_sampledState`, `pathLaw_stopped_sampled` | `𝔼(τ) = ∑ P(τ > n)`; the law of `s_τ` is the marginal `sampleLaw` |
| `chainKernel`, `chainLaw`, `chainLaw_eq`, `chainLaw_tendsto_pathLaw` | `GFNBounds`' frozen chain, and its agreement with the path space |
| **`sampling_theorem`** | `theo:sampling_theorem`, all clauses, plus `τ < ∞` a.s. |
| `tvDist`, `tvDist_eq_iSup`, `le_add_tvDist`, `tvDist_normalize_add_le` | `TV = ½‖·‖`, the setwise supremum, the mixture estimate of `main.tex:863–866` |
| `GenerativeFlow.termLaw_split`, `negative_control_marginal` | the proof of `main.tex:852–867`, on measures |
| **`main_quantitative_sampling`** | `theo:negative_control` = `theo:negative_control_appendix`, plus termination, `𝔼(τ) < ∞`, the mass identity of `main.tex:854–855` and the setwise bound |
| `Resample.sampling_theorem_inhabited`, `TwoPoint.negative_control_sharp` | inhabitation; the bound is attained, and is false for the unhalved norm |

## Hypothesis checklist

| paper | here |
|---|---|
| `(𝒮, λ)` Polish, with a finite background measure `λ` (`main.tex:155`, `:161`) | ⚠ weakened: any measurable space; `λ` is not read by these statements |
| `F_init`, `F_term` unnormalized distributions | ✓ finite measures `[IsFiniteMeasure]` |
| `F_term ≠ 0` (`theo:sampling_theorem`) | ✓ `hterm` |
| `(π, F_out)` a generative flow | ✓ `EGF.GenerativeFlow`: `π` Markov, `F_out` finite (`main.tex:161`) |
| the flow-matching constraint | ✓ `GenerativeFlow.IsFlowMatching`, an equality of measures, `F_in = F_out π = EGF.inflow` |
| the sampler of `main.tex:163–165` | ✓ `GenerativeFlow.pathLaw` (the definition `pathKernel`: the state moves by `π` whatever the flag; a lowered flag is raised at the new state with probability `stop`); `pathLaw_spec` checks its clauses (a randomized stopping time, a confirmation question) |
| `𝔼(τ) ≤ F_out(𝒮)/F_init(𝒮) + 1` | ✓ `∫⁻ τ dP`, in `[0, ∞]` |
| `s_τ ∼ F_term` (`x ∼ μ`: the law is `μ/μ(𝒮)`, `main.tex:159`) | ✓ `τ < ∞` a.s. and `law(s_τ) = F_term/F_term(𝒮)` |
| `F_init ≠ 0` (`theo:negative_control`) | ✓ `hinit`; no flow matching is assumed |
| `δF_init`, `δF_term`, `F̂_term` | ✓ the strict `EGF.initialError`, `EGF.terminalError` (Jordan parts), `virtualTerm` |
| "`TV` the total variation" | ✓ `tvDist = ½ ‖·‖`, the `½` of `main.tex:338`; also setwise. The unhalved norm is refuted (`TwoPoint.negative_control_sharp`) |

## SCOPE (disclosed)

**The sampler** is built, not assumed: by Ionescu-Tulcea (`Kernel.trajMeasure`) on `(𝒮 × Bool)^ℕ`,
the first coordinate moving by `π` at every step (the paper's chain runs on after `τ`) and the flag
raised at the new state `y` with probability `stop y`; `τ` is one plus the index of the first raised
flag, `s_τ` the state there. The decision at time `t` reads `s_t` only, which is how a sampler
"emulating the Markov chain" draws `τ`. `stop = 1 − min(dF_out/dG, 1)`, `G = F_term + F_out`, is
the paper's `dF_term/dG` `G`-a.e. (`stop_ae_eq`); in both theorems the unstopped mass is dominated
by `G`, so the hazard holds with Mathlib's `rnDeriv` itself (`pathLaw_hazard_rnDeriv`).

**Agreement with `GFNBounds`.** `GFNBounds.Core.SamplingGeneral` models the sampler by the
marginals of a chain frozen at stopping (`chainLaw`), and reads the law of `s_τ` as the limit
`termLaw` of `P(Xₙ ∈ A × {true})`. That chain is ported (`chainKernel`, `chainLaw_eq`), and the law
of `s_τ` on the path space is that limit (`chainLaw_tendsto_pathLaw`), while `∫⁻ τ` is `GFNBounds`'
`expectedTau` (`lintegral_stopTime`): the two readings agree.

**`TV`** is `½ ‖μ − ν‖`, which for probability measures is `sup_A |μ(A) − ν(A)|`
(`tvDist_eq_iSup`; the setwise bound is also stated). `main.tex:338` fixes the `½`; the proof's
last step (`main.tex:863–866`, a mixture with weight `1 − α`) needs `TV ≤ 1`. Read without the `½`, the
theorem is false: on two points the unhalved norm is `1` against a bound `½`, which the halved
`TV` attains (`TwoPoint.negative_control_sharp`).

**The proof is the paper's** (`main.tex:852–867`): the chains from `F_init` and `δF_init` to
`F̂_term` share their kernel, their stopped laws add up to `F̂_term` (`termLaw_split`), and the
mixture estimate concludes. Termination of the chain from `F_init` (which is not flow matching),
left implicit at `main.tex:853`, is proved: its occupation is dominated by `F̂_term + F_out`.

No `sorry`; no named hypothesis.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-! ## The virtual initial and terminal flows (`def:virtual_flows`, `main.tex:316–318`) -/

/-- **The virtual initial distribution** `F̂_init := F_init + δF_init` (`main.tex:317`). -/
noncomputable def virtualInit (π : Kernel S S) (Fout Finit Fterm : Measure S) : Measure S :=
  Finit + initialError π Fout Finit Fterm

/-- **The virtual terminal distribution** `F̂_term := F_term + δF_term` (`main.tex:317`). -/
noncomputable def virtualTerm (π : Kernel S S) (Fout Finit Fterm : Measure S) : Measure S :=
  Fterm + terminalError π Fout Finit Fterm

/-- For finite measures, `μ + (ν − μ) = ν + (μ − ν)`: both are `μ ⊔ ν`. -/
theorem add_sub_eq_add_sub (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ + (ν - μ) = ν + (μ - ν) := by
  have h := Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub (μ := μ) (ν := ν)
  rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
    Measure.toSignedMeasure_add]
  have h2 : μ.toSignedMeasure
      = ν.toSignedMeasure + ((μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure) := by
    rw [← h]; abel
  rw [h2]; abel

/-- For finite measures of equal mass, `(μ − ν)⁺(𝒮) = (μ − ν)⁻(𝒮)`. -/
theorem sub_univ_eq_sub_univ {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ = ν Set.univ) : (μ - ν) Set.univ = (ν - μ) Set.univ := by
  have e := congrArg (fun m : Measure S => m Set.univ) (add_sub_eq_add_sub μ ν)
  simp only [Measure.add_apply] at e
  rw [h] at e
  exact ((ENNReal.add_right_inj (measure_ne_top ν Set.univ)).1 e).symm

/-- **Any generative flow is flow matching from `F̂_init` to `F̂_term`** (`main.tex:320`). -/
theorem isFlowMatching_virtual (π : Kernel S S) [IsMarkovKernel π] (Fout Finit Fterm : Measure S)
    [IsFiniteMeasure Fout] [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] :
    IsFlowMatching π Fout (virtualInit π Fout Finit Fterm) (virtualTerm π Fout Finit Fterm) := by
  unfold IsFlowMatching virtualInit virtualTerm initialError terminalError
  have h := add_sub_eq_add_sub (Finit + inflow π Fout) (Fterm + Fout)
  set D := (Fterm + Fout) - (Finit + inflow π Fout)
  set E := (Finit + inflow π Fout) - (Fterm + Fout)
  calc Finit + D + inflow π Fout = Finit + inflow π Fout + D := by abel
    _ = Fterm + Fout + E := h
    _ = Fterm + E + Fout := by abel

/-- `F̂_init(𝒮) = F̂_term(𝒮)`: the virtual flows have equal masses. -/
theorem virtualInit_univ (π : Kernel S S) [IsMarkovKernel π] (Fout Finit Fterm : Measure S)
    [IsFiniteMeasure Fout] [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] :
    virtualInit π Fout Finit Fterm Set.univ = virtualTerm π Fout Finit Fterm Set.univ := by
  have h := congrArg (fun m : Measure S => m Set.univ)
    (isFlowMatching_virtual π Fout Finit Fterm)
  simp only [Measure.add_apply, inflow, bind_univ] at h
  exact (ENNReal.add_left_inj (measure_ne_top Fout Set.univ)).1 h

/-- Two measures, one below the other, with the same finite total mass, are equal (template:
`GFNBounds.Core.SamplingGeneral.eq_of_le_of_univ`). -/
theorem eq_of_le_of_univ {μ ν : Measure S} [IsFiniteMeasure ν] (h : μ ≤ ν)
    (hu : μ Set.univ = ν Set.univ) : μ = ν := by
  haveI := isFiniteMeasure_of_le ν h
  exact Measure.eq_of_le_of_measure_univ_eq h hu

/-! ## The sampler, through its marginals

Template: `GFNBounds.Core.SamplingGeneral` (`lean/GFNBounds/Core/SamplingGeneral.lean`), ported
over `EGF.GenerativeFlow`: the star policy `π` and the star outflow `F_out` are the flow's, the
terminal distribution `F_term` is a parameter. -/

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Fterm : Measure S)

/-- `G := F_term + F_out`, the measure the stopping rule is a density against (the footnote of
`main.tex:164`). -/
noncomputable def stopBase : Measure S := Fterm + F.outflow

/-- The probability of moving on from `x`: `dF_out/d(F_term + F_out)(x)`, capped at `1`. -/
noncomputable def cont (x : S) : ℝ≥0∞ := min (F.outflow.rnDeriv (F.stopBase Fterm) x) 1

/-- The probability of stopping at `x`, `1 − cont(x)`; `G`-a.e. it is the paper's
`dF_term/d(F_term + F_out)(x)` (`stop_ae_eq`, `main.tex:164`). -/
noncomputable def stop (x : S) : ℝ≥0∞ := 1 - F.cont Fterm x

theorem measurable_cont : Measurable (F.cont Fterm) :=
  (Measure.measurable_rnDeriv _ _).min measurable_const

theorem measurable_stop : Measurable (F.stop Fterm) :=
  measurable_const.sub (F.measurable_cont Fterm)

theorem cont_le_one (x : S) : F.cont Fterm x ≤ 1 := min_le_right _ _

theorem cont_add_stop (x : S) : F.cont Fterm x + F.stop Fterm x = 1 :=
  add_tsub_cancel_of_le (F.cont_le_one Fterm x)

/-- One step of the unstopped sampler: `μ ↦ (cont · μ) π`. -/
noncomputable def step (μ : Measure S) : Measure S := (μ.withDensity (F.cont Fterm)).bind F.policy

/-- `occ μ₀ n (A)`: the mass not stopped by time `n` and standing in `A`
(`P(τ > n, s_{n+1} ∈ A)` from `s₁ ∼ μ₀`). -/
noncomputable def occ (μ₀ : Measure S) : ℕ → Measure S
  | 0 => μ₀
  | n + 1 => F.step Fterm (occ μ₀ n)

/-- `P(τ ≤ n, s_τ ∈ A)`. -/
noncomputable def stopped (μ₀ : Measure S) (n : ℕ) : Measure S :=
  ∑ k ∈ Finset.range n, (F.occ Fterm μ₀ k).withDensity (F.stop Fterm)

/-- The occupation measure `Q = ∑ₙ occ μ₀ n`. -/
noncomputable def occupation (μ₀ : Measure S) : Measure S := Measure.sum (F.occ Fterm μ₀)

/-- The law of the stopped state, `stop · Q`. -/
noncomputable def termLaw (μ₀ : Measure S) : Measure S :=
  (F.occupation Fterm μ₀).withDensity (F.stop Fterm)

theorem step_apply (μ : Measure S) {s : Set S} (hs : MeasurableSet s) :
    F.step Fterm μ s = ∫⁻ x, F.cont Fterm x * F.policy x s ∂μ := by
  rw [step, Measure.bind_apply hs (F.policy.aemeasurable),
    lintegral_withDensity_eq_lintegral_mul _ (F.measurable_cont Fterm)
      (F.policy.measurable_coe hs)]
  rfl

theorem step_smul (c : ℝ≥0∞) (μ : Measure S) : F.step Fterm (c • μ) = c • F.step Fterm μ := by
  rw [step, withDensity_smul_measure, Measure.bind_smul, step]

theorem occ_zero (μ₀ : Measure S) : F.occ Fterm μ₀ 0 = μ₀ := rfl

theorem occ_succ (μ₀ : Measure S) (n : ℕ) :
    F.occ Fterm μ₀ (n + 1) = F.step Fterm (F.occ Fterm μ₀ n) := rfl

/-- **Domination by any super-solution** (template: `MFlow.partial_le`). -/
theorem partial_le {μ₀ H : Measure S} (hH : μ₀ + F.step Fterm H ≤ H) :
    ∀ N : ℕ, ∑ k ∈ Finset.range N, F.occ Fterm μ₀ k ≤ H
  | 0 => by simp only [Finset.range_zero, Finset.sum_empty]; exact Measure.zero_le _
  | N + 1 => by
    have ih := partial_le hH N
    rw [Measure.le_iff] at hH ⊢
    intro s hs
    rw [Finset.sum_range_succ', Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [occ_succ, occ_zero, F.step_apply Fterm _ hs]
    rw [← lintegral_finsetSum_measure]
    calc ∫⁻ x, F.cont Fterm x * F.policy x s ∂(∑ k ∈ Finset.range N, F.occ Fterm μ₀ k) + μ₀ s
        ≤ ∫⁻ x, F.cont Fterm x * F.policy x s ∂H + μ₀ s := by gcongr
      _ = (μ₀ + F.step Fterm H) s := by rw [Measure.add_apply, F.step_apply Fterm H hs, add_comm]
      _ ≤ H s := hH s hs

theorem occupation_apply (μ₀ : Measure S) {s : Set S} (hs : MeasurableSet s) :
    F.occupation Fterm μ₀ s = ∑' n, F.occ Fterm μ₀ n s := Measure.sum_apply _ hs

/-- The occupation measure is dominated by any super-solution. -/
theorem occupation_le {μ₀ H : Measure S} (hH : μ₀ + F.step Fterm H ≤ H) :
    F.occupation Fterm μ₀ ≤ H := by
  rw [Measure.le_iff]
  intro s hs
  rw [F.occupation_apply Fterm μ₀ hs]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have h := F.partial_le Fterm hH N
  rw [Measure.le_iff] at h
  have := h s hs
  rwa [Measure.coe_finsetSum, Finset.sum_apply] at this

/-- The occupation recursion on total masses: `Q(𝒮) = μ₀(𝒮) + ∫ cont dQ`. -/
theorem occupation_univ (μ₀ : Measure S) :
    F.occupation Fterm μ₀ Set.univ = μ₀ Set.univ + ∫⁻ x, F.cont Fterm x ∂(F.occupation Fterm μ₀) := by
  rw [F.occupation_apply Fterm μ₀ MeasurableSet.univ, occupation, lintegral_sum_measure,
    tsum_eq_zero_add' ENNReal.summable]
  congr 1
  refine tsum_congr fun n => ?_
  rw [occ_succ, F.step_apply Fterm _ MeasurableSet.univ]
  simp only [measure_univ, mul_one]

theorem lintegral_cont_add_stop (μ : Measure S) :
    ∫⁻ x, F.cont Fterm x ∂μ + ∫⁻ x, F.stop Fterm x ∂μ = μ Set.univ := by
  rw [← lintegral_add_left (F.measurable_cont Fterm)]
  simp only [F.cont_add_stop, lintegral_one]

theorem termLaw_apply (μ₀ : Measure S) {s : Set S} (hs : MeasurableSet s) :
    F.termLaw Fterm μ₀ s = ∫⁻ x in s, F.stop Fterm x ∂(F.occupation Fterm μ₀) :=
  withDensity_apply _ hs

/-- **Termination, on masses**: a finite occupation stops all the initial mass. -/
theorem termLaw_univ (μ₀ : Measure S) (hQ : F.occupation Fterm μ₀ Set.univ ≠ ∞) :
    F.termLaw Fterm μ₀ Set.univ = μ₀ Set.univ := by
  rw [F.termLaw_apply Fterm μ₀ MeasurableSet.univ, Measure.restrict_univ]
  have h1 := F.occupation_univ Fterm μ₀
  have h2 := F.lintegral_cont_add_stop Fterm (F.occupation Fterm μ₀)
  have hc : ∫⁻ x, F.cont Fterm x ∂(F.occupation Fterm μ₀) ≠ ∞ := by
    refine ne_top_of_le_ne_top hQ ?_
    rw [← h2]; exact le_self_add
  rw [← h2, add_comm] at h1
  exact (ENNReal.add_left_inj hc).1 h1

theorem termLaw_mono {μ₀ H : Measure S} (hH : μ₀ + F.step Fterm H ≤ H) :
    F.termLaw Fterm μ₀ ≤ H.withDensity (F.stop Fterm) := by
  rw [Measure.le_iff]
  intro s hs
  rw [F.termLaw_apply Fterm μ₀ hs, withDensity_apply _ hs]
  exact lintegral_mono' (Measure.restrict_mono le_rfl (F.occupation_le Fterm hH)) le_rfl

theorem stopped_apply (μ₀ : Measure S) (n : ℕ) {s : Set S} (hs : MeasurableSet s) :
    F.stopped Fterm μ₀ n s = ∑ k ∈ Finset.range n, ∫⁻ x in s, F.stop Fterm x ∂(F.occ Fterm μ₀ k) := by
  rw [stopped, Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => withDensity_apply _ hs

/-- `P(τ ≤ n, s_τ ∈ A) → (stop · Q)(A)`, setwise. -/
theorem stopped_tendsto (μ₀ : Measure S) {s : Set S} (hs : MeasurableSet s) :
    Tendsto (fun n => F.stopped Fterm μ₀ n s) atTop (𝓝 (F.termLaw Fterm μ₀ s)) := by
  have : F.termLaw Fterm μ₀ s = ∑' k, ∫⁻ x in s, F.stop Fterm x ∂(F.occ Fterm μ₀ k) := by
    rw [termLaw, occupation, withDensity_sum, Measure.sum_apply _ hs]
    exact tsum_congr fun k => withDensity_apply _ hs
  rw [this]
  simp only [F.stopped_apply Fterm μ₀ _ hs]
  exact ENNReal.tendsto_nat_tsum _

/-! ### Flow matching read through the stopping rule -/

section FM

variable [IsFiniteMeasure Fterm]

instance isFiniteMeasure_stopBase : IsFiniteMeasure (F.stopBase Fterm) := by
  unfold stopBase; infer_instance

omit [IsFiniteMeasure Fterm] in
theorem outflow_ac_stopBase : F.outflow ≪ F.stopBase Fterm :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

omit [IsFiniteMeasure Fterm] in
theorem fterm_ac_stopBase : Fterm ≪ F.stopBase Fterm :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

theorem rnDeriv_sum_ae :
    ∀ᵐ x ∂F.stopBase Fterm,
      Fterm.rnDeriv (F.stopBase Fterm) x + F.outflow.rnDeriv (F.stopBase Fterm) x = 1 := by
  have h1 := Measure.rnDeriv_add Fterm F.outflow (F.stopBase Fterm)
  have h2 := Measure.rnDeriv_self (F.stopBase Fterm)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← Pi.add_apply, ← hx1]
  exact hx2

/-- `cont = dF_out/d(F_term + F_out)`, `G`-a.e. -/
theorem cont_ae_eq : F.cont Fterm =ᵐ[F.stopBase Fterm] F.outflow.rnDeriv (F.stopBase Fterm) := by
  filter_upwards [F.rnDeriv_sum_ae Fterm] with x hx
  refine min_eq_left ?_
  rw [← hx]; exact le_add_self

/-- `stop = dF_term/d(F_term + F_out)`, `G`-a.e.: **the paper's stopping probability**
(`main.tex:164`). -/
theorem stop_ae_eq : F.stop Fterm =ᵐ[F.stopBase Fterm] Fterm.rnDeriv (F.stopBase Fterm) := by
  filter_upwards [F.rnDeriv_sum_ae Fterm, F.cont_ae_eq Fterm,
    Measure.rnDeriv_lt_top F.outflow (F.stopBase Fterm)] with x hx hc hlt
  rw [stop, hc]
  exact ENNReal.sub_eq_of_eq_add hlt.ne hx.symm

theorem withDensity_cont : (F.stopBase Fterm).withDensity (F.cont Fterm) = F.outflow := by
  rw [withDensity_congr_ae (F.cont_ae_eq Fterm),
    Measure.withDensity_rnDeriv_eq _ _ (F.outflow_ac_stopBase Fterm)]

theorem withDensity_stop : (F.stopBase Fterm).withDensity (F.stop Fterm) = Fterm := by
  rw [withDensity_congr_ae (F.stop_ae_eq Fterm),
    Measure.withDensity_rnDeriv_eq _ _ (F.fterm_ac_stopBase Fterm)]

end FM

/-! ### Linearity in the initial mass -/

theorem step_add (μ μ' : Measure S) :
    F.step Fterm (μ + μ') = F.step Fterm μ + F.step Fterm μ' := by
  rw [step, withDensity_add_measure, bind_add_measure, step, step]

theorem occ_add (μ μ' : Measure S) :
    ∀ n, F.occ Fterm (μ + μ') n = F.occ Fterm μ n + F.occ Fterm μ' n
  | 0 => rfl
  | n + 1 => by rw [occ_succ, occ_add μ μ' n, step_add, occ_succ, occ_succ]

theorem occ_smul (c : ℝ≥0∞) (μ : Measure S) : ∀ n, F.occ Fterm (c • μ) n = c • F.occ Fterm μ n
  | 0 => rfl
  | n + 1 => by rw [occ_succ, occ_smul c μ n, step_smul, occ_succ]

theorem occupation_add (μ μ' : Measure S) :
    F.occupation Fterm (μ + μ') = F.occupation Fterm μ + F.occupation Fterm μ' := by
  ext s hs
  rw [Measure.add_apply, F.occupation_apply Fterm _ hs, F.occupation_apply Fterm _ hs,
    F.occupation_apply Fterm _ hs, ← ENNReal.tsum_add]
  exact tsum_congr fun n => by rw [occ_add, Measure.add_apply]

theorem occupation_smul (c : ℝ≥0∞) (μ : Measure S) :
    F.occupation Fterm (c • μ) = c • F.occupation Fterm μ := by
  ext s hs
  rw [Measure.smul_apply, F.occupation_apply Fterm _ hs, F.occupation_apply Fterm _ hs,
    smul_eq_mul, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => by rw [occ_smul, Measure.smul_apply, smul_eq_mul]

theorem termLaw_add (μ μ' : Measure S) :
    F.termLaw Fterm (μ + μ') = F.termLaw Fterm μ + F.termLaw Fterm μ' := by
  rw [termLaw, occupation_add, withDensity_add_measure, termLaw, termLaw]

theorem termLaw_smul (c : ℝ≥0∞) (μ : Measure S) :
    F.termLaw Fterm (c • μ) = c • F.termLaw Fterm μ := by
  rw [termLaw, occupation_smul, withDensity_smul_measure, termLaw]

/-- **The unnormalised sampling theorem** (template: `MFlow.termLaw_eq_fterm`): an initial
measure `μ₀` with `μ₀ + (cont · G) π = G` is carried by the sampler exactly onto `F_term`. -/
theorem termLaw_eq_fterm [IsFiniteMeasure Fterm] {μ₀ : Measure S}
    (h : μ₀ + F.step Fterm (F.stopBase Fterm) = F.stopBase Fterm) :
    F.termLaw Fterm μ₀ = Fterm := by
  have hle : F.termLaw Fterm μ₀ ≤ Fterm := by
    have := F.termLaw_mono Fterm (le_of_eq h); rwa [withDensity_stop] at this
  refine eq_of_le_of_univ hle ?_
  have hQ : F.occupation Fterm μ₀ Set.univ ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top (F.stopBase Fterm) Set.univ)
      (Measure.le_iff.1 (F.occupation_le Fterm (le_of_eq h)) _ MeasurableSet.univ)
  rw [F.termLaw_univ Fterm μ₀ hQ]
  have h1 := congrArg (fun μ : Measure S => μ Set.univ) h
  simp only [Measure.add_apply, step, withDensity_cont, bind_univ] at h1
  rw [stopBase, Measure.add_apply] at h1
  exact (ENNReal.add_left_inj (measure_ne_top F.outflow Set.univ)).1 h1

end GenerativeFlow

/-! ## The total variation distance and the mixture estimate -/

/-- `x ∼ μ` for an unnormalized `μ` means "the law of `x` is `μ/μ(𝒮)`" (`main.tex:159`). -/
noncomputable def normalize (μ : Measure S) : Measure S := (μ Set.univ)⁻¹ • μ

theorem normalize_univ (μ : Measure S) [IsFiniteMeasure μ] (h : μ ≠ 0) :
    normalize μ Set.univ = 1 := by
  rw [normalize, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (fun h' => h (Measure.measure_univ_eq_zero.1 h'))
    (measure_ne_top _ _)

instance isFiniteMeasure_normalize (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (normalize μ) := by
  by_cases h : μ = 0
  · subst h; unfold normalize; simp only [smul_zero]; infer_instance
  · exact ⟨by rw [normalize_univ μ h]; exact ENNReal.one_lt_top⟩

/-- `μ(A) − ν(A) ≤ (μ − ν)(𝒮)`. -/
theorem tsub_le_sub_univ (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set S) :
    μ A - ν A ≤ (μ - ν) Set.univ := by
  refine tsub_le_iff_right.2 ?_
  calc μ A ≤ ((μ - ν) + ν) A := Measure.le_iff'.1 (Measure.sub_le_iff_le_add.mp le_rfl) A
    _ = (μ - ν) A + ν A := Measure.add_apply _ _ _
    _ ≤ (μ - ν) Set.univ + ν A := by gcongr; exact Set.subset_univ _

/-- By Hahn, `(μ − ν)⁺(𝒮) = sup_A (μ(A) − ν(A))` for finite measures. -/
theorem sub_univ_eq_iSup (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ - ν) Set.univ = ⨆ A ∈ {A : Set S | MeasurableSet A}, (μ A - ν A) := by
  refine le_antisymm ?_ (iSup₂_le fun A _ => tsub_le_sub_univ μ ν A)
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have h0 : (μ - ν) s = 0 := Measure.sub_apply_eq_zero_of_isHahnDecomposition hs
  have h1 : (μ - ν) sᶜ = μ sᶜ - ν sᶜ := by
    rw [← Measure.restrict_apply_univ,
      Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl,
      Measure.sub_apply MeasurableSet.univ hs.ge_on_compl, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  rw [← measure_add_measure_compl hs.measurableSet, h0, zero_add, h1]
  exact le_iSup₂ (f := fun A (_ : A ∈ {A : Set S | MeasurableSet A}) => μ A - ν A) sᶜ
    hs.measurableSet.compl

/-- **The total variation distance** `TV(μ ‖ ν) := ½ ‖μ − ν‖ = ½ ((μ − ν)⁺(𝒮) + (μ − ν)⁻(𝒮))`,
with the `½` of `main.tex:338` (`TV = ½ ∑ |·|` on a finite state space); for probability measures
it is `sup_A |μ(A) − ν(A)|` (`tvDist_eq_iSup`). -/
noncomputable def tvDist (μ ν : Measure S) : ℝ≥0∞ := tvMass μ ν / 2

/-- For two finite measures of equal mass, `TV(μ ‖ ν) = (μ − ν)⁺(𝒮)`. -/
theorem tvDist_eq_sub_univ {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ = ν Set.univ) : tvDist μ ν = (μ - ν) Set.univ := by
  rw [tvDist, tvMass, ← sub_univ_eq_sub_univ h, ← two_mul, mul_comm,
    ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-- Setwise, `μ(A) ≤ ν(A) + TV(μ ‖ ν)` for two finite measures of equal mass: `TV` bounds
`sup_A |μ(A) − ν(A)|`. -/
theorem le_add_tvDist {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ = ν Set.univ) (A : Set S) : μ A ≤ ν A + tvDist μ ν := by
  rw [tvDist_eq_sub_univ h]
  calc μ A ≤ ((μ - ν) + ν) A := Measure.le_iff'.1 (Measure.sub_le_iff_le_add.mp le_rfl) A
    _ = (μ - ν) A + ν A := Measure.add_apply _ _ _
    _ ≤ (μ - ν) Set.univ + ν A := by gcongr; exact Set.subset_univ _
    _ = ν A + (μ - ν) Set.univ := add_comm _ _

/-- **`TV(μ ‖ ν) = sup_A |μ(A) − ν(A)|`** for two finite measures of equal mass: the `½`
convention is the setwise supremum. -/
theorem tvDist_eq_iSup {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ Set.univ = ν Set.univ) :
    tvDist μ ν = ⨆ A ∈ {A : Set S | MeasurableSet A}, ((μ A - ν A) ⊔ (ν A - μ A)) := by
  refine le_antisymm ?_ (iSup₂_le fun A _ => sup_le ?_ ?_)
  · rw [tvDist_eq_sub_univ h, sub_univ_eq_iSup]
    exact iSup₂_mono fun A _ => le_sup_left
  · rw [tvDist_eq_sub_univ h]; exact tsub_le_sub_univ μ ν A
  · rw [tvDist_eq_sub_univ h, sub_univ_eq_sub_univ h]; exact tsub_le_sub_univ ν μ A

theorem tvDist_comm (μ ν : Measure S) : tvDist μ ν = tvDist ν μ := by
  rw [tvDist, tvDist, tvMass_comm]

/-- **The mixture estimate of the proof of `theo:negative_control_appendix`** (`main.tex:863–866`):
if `a ≠ 0` and `b` are finite, `(a + b)/(a + b)(𝒮) − a/a(𝒮) ≤ b/(a + b)(𝒮)`, on every set. -/
theorem normalize_add_sub_normalize_le (a b : Measure S) [IsFiniteMeasure a] [IsFiniteMeasure b]
    (ha : a ≠ 0) : normalize (a + b) - normalize a ≤ ((a + b) Set.univ)⁻¹ • b := by
  have hZ : a Set.univ ≠ 0 := fun h => ha (Measure.measure_univ_eq_zero.1 h)
  have hZK : a Set.univ ≤ (a + b) Set.univ := by rw [Measure.add_apply]; exact le_self_add
  have hinv : ((a + b) Set.univ)⁻¹ ≤ (a Set.univ)⁻¹ := ENNReal.inv_le_inv.2 hZK
  refine Measure.sub_le_of_le_add ?_
  rw [normalize, smul_add, add_comm (((a + b) Set.univ)⁻¹ • b)]
  refine add_le_add ?_ le_rfl
  rw [normalize, Measure.le_iff]
  intro s _
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left hinv _

/-- The mixture estimate in total variation: `TV(a/a(𝒮) ‖ (a + b)/(a + b)(𝒮)) ≤ b(𝒮)/(a + b)(𝒮)`. -/
theorem tvDist_normalize_add_le (a b : Measure S) [IsFiniteMeasure a] [IsFiniteMeasure b]
    (ha : a ≠ 0) :
    tvDist (normalize a) (normalize (a + b)) ≤ b Set.univ / (a + b) Set.univ := by
  have hab : a + b ≠ 0 := fun h => ha (by
    have : a ≤ a + b := Measure.le_add_right le_rfl
    rw [h] at this; exact le_antisymm this (Measure.zero_le _))
  rw [tvDist_comm, tvDist_eq_sub_univ (by rw [normalize_univ _ hab, normalize_univ _ ha])]
  calc (normalize (a + b) - normalize a) Set.univ ≤ (((a + b) Set.univ)⁻¹ • b) Set.univ :=
        normalize_add_sub_normalize_le a b ha Set.univ
    _ = b Set.univ / (a + b) Set.univ := by
        rw [Measure.smul_apply, smul_eq_mul, mul_comm, div_eq_mul_inv]

/-! ## The sampler of a generative flow from `F_init` to `F_term`, through its marginals -/

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Finit Fterm : Measure S)

/-- `P(τ > n)`, from `s₁ ∼ F_init`. -/
noncomputable def tailProb (n : ℕ) : ℝ≥0∞ := F.occ Fterm (normalize Finit) n Set.univ

/-- `∑_{n ≥ 0} P(τ > n)`, which is `𝔼(τ)` on the path space (`lintegral_stopTime`); `GFNBounds`'
`MFlow.expectedTau`. -/
noncomputable def expectedTau : ℝ≥0∞ := ∑' n, F.tailProb Finit Fterm n

/-- The law of `s_τ` on `{τ < ∞}`, through the marginals: `stop · ∑ₙ occ n` from
`s₁ ∼ F_init` (equal to the law of `s_τ` on the path space, `pathLaw_sampledState`). -/
noncomputable def sampleLaw : Measure S := F.termLaw Fterm (normalize Finit)

theorem expectedTau_eq_occupation :
    F.expectedTau Finit Fterm = F.occupation Fterm (normalize Finit) Set.univ :=
  (F.occupation_apply Fterm _ MeasurableSet.univ).symm

theorem sampleLaw_eq_smul : F.sampleLaw Finit Fterm = (Finit Set.univ)⁻¹ • F.termLaw Fterm Finit := by
  rw [sampleLaw, normalize, termLaw_smul]

/-- **`F_init(𝒮) = F_term(𝒮)` under flow matching.** -/
theorem mass_eq (hFM : F.IsFlowMatching Finit Fterm) : Finit Set.univ = Fterm Set.univ := by
  have h := congrArg (fun μ : Measure S => μ Set.univ) hFM
  simp only [Measure.add_apply, inflow, bind_univ] at h
  exact (ENNReal.add_left_inj (measure_ne_top F.outflow Set.univ)).1 h

/-- Flow matching read through the stopping rule: `F_init + (cont · G) π = G`. -/
theorem finit_add_step_stopBase [IsFiniteMeasure Fterm] (hFM : F.IsFlowMatching Finit Fterm) :
    Finit + F.step Fterm (F.stopBase Fterm) = F.stopBase Fterm := by
  rw [step, withDensity_cont]; exact hFM

section Theorem

variable [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm]

omit [IsFiniteMeasure Finit] in
theorem normalize_add_step (hFM : F.IsFlowMatching Finit Fterm) :
    normalize Finit + F.step Fterm ((Finit Set.univ)⁻¹ • F.stopBase Fterm)
      = (Finit Set.univ)⁻¹ • F.stopBase Fterm := by
  rw [step_smul, normalize, ← smul_add, F.finit_add_step_stopBase Finit Fterm hFM]

omit [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] in
theorem finit_univ_ne_zero (hterm : Fterm ≠ 0) (hFM : F.IsFlowMatching Finit Fterm) :
    Finit Set.univ ≠ 0 := by
  rw [F.mass_eq Finit Fterm hFM]
  exact fun h => hterm (Measure.measure_univ_eq_zero.1 h)

/-- **`𝔼(τ) ≤ F_out(𝒮)/F_init(𝒮) + 1`**, on the marginals (template: `MFlow.expectedTau_le`). -/
theorem expectedTau_le (hterm : Fterm ≠ 0) (hFM : F.IsFlowMatching Finit Fterm) :
    F.expectedTau Finit Fterm ≤ F.outflow Set.univ / Finit Set.univ + 1 := by
  have hZ := F.finit_univ_ne_zero Finit Fterm hterm hFM
  have hZt : Finit Set.univ ≠ ∞ := measure_ne_top _ _
  rw [expectedTau_eq_occupation]
  refine (Measure.le_iff.1 (F.occupation_le Fterm (le_of_eq (F.normalize_add_step Finit Fterm hFM)))
    Set.univ MeasurableSet.univ).trans (le_of_eq ?_)
  rw [Measure.smul_apply, smul_eq_mul, stopBase, Measure.add_apply, ← F.mass_eq Finit Fterm hFM,
    mul_add, ENNReal.inv_mul_cancel hZ hZt, div_eq_mul_inv, mul_comm, add_comm]

theorem expectedTau_ne_top (hterm : Fterm ≠ 0) (hFM : F.IsFlowMatching Finit Fterm) :
    F.expectedTau Finit Fterm ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (measure_ne_top _ _)
    (F.finit_univ_ne_zero Finit Fterm hterm hFM), ENNReal.one_ne_top⟩)
    (F.expectedTau_le Finit Fterm hterm hFM)

/-- **`s_τ ∼ F_term`**, on the marginals: `stop · Q = F_term/F_term(𝒮)` (template:
`MFlow.sampleLaw_eq`). -/
theorem sampleLaw_eq (hterm : Fterm ≠ 0) (hFM : F.IsFlowMatching Finit Fterm) :
    F.sampleLaw Finit Fterm = normalize Fterm := by
  have hZ := F.finit_univ_ne_zero Finit Fterm hterm hFM
  have hmass := F.mass_eq Finit Fterm hFM
  have hle : F.sampleLaw Finit Fterm ≤ normalize Fterm := by
    have h := F.termLaw_mono Fterm (le_of_eq (F.normalize_add_step Finit Fterm hFM))
    rwa [withDensity_smul_measure, withDensity_stop, hmass] at h
  refine eq_of_le_of_univ hle ?_
  have hQ : F.occupation Fterm (normalize Finit) Set.univ ≠ ∞ := by
    rw [← expectedTau_eq_occupation]; exact F.expectedTau_ne_top Finit Fterm hterm hFM
  have hFi : Finit ≠ 0 := fun h => hZ (by rw [h]; rfl)
  rw [sampleLaw, F.termLaw_univ _ _ hQ, normalize_univ _ hFi, normalize_univ _ hterm]

end Theorem

/-! ### The quantitative form, on the marginals (template: `SamplingGeneralBounds`) -/

section Matched

variable {Finit Fterm} {δ : Measure S}
  (hmatch : Finit + δ + F.outflow.bind F.policy = Fterm + F.outflow)

include hmatch

variable [IsFiniteMeasure Fterm]

theorem matched_step : (Finit + δ) + F.step Fterm (F.stopBase Fterm) = F.stopBase Fterm := by
  rw [step, withDensity_cont]; exact hmatch

theorem finit_super : Finit + F.step Fterm (F.stopBase Fterm) ≤ F.stopBase Fterm := by
  calc Finit + F.step Fterm (F.stopBase Fterm) ≤ (Finit + δ) + F.step Fterm (F.stopBase Fterm) :=
        add_le_add_left (Measure.le_add_right le_rfl) _
    _ = F.stopBase Fterm := F.matched_step hmatch

theorem delta_super : δ + F.step Fterm (F.stopBase Fterm) ≤ F.stopBase Fterm := by
  calc δ + F.step Fterm (F.stopBase Fterm) ≤ (Finit + δ) + F.step Fterm (F.stopBase Fterm) :=
        add_le_add_left (Measure.le_add_left le_rfl) _
    _ = F.stopBase Fterm := F.matched_step hmatch

/-- **The step of `main.tex:857–862`**: the chains from `F_init` and from `δF_init` share their
kernel, and their stopped laws add up to `F̂_term`. -/
theorem termLaw_split : F.termLaw Fterm Finit + F.termLaw Fterm δ = Fterm := by
  rw [← termLaw_add]; exact F.termLaw_eq_fterm Fterm (F.matched_step hmatch)

theorem occupation_finit_ne_top : F.occupation Fterm Finit Set.univ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top (F.stopBase Fterm) Set.univ)
    (Measure.le_iff.1 (F.occupation_le Fterm (F.finit_super hmatch)) _ MeasurableSet.univ)

theorem occupation_delta_ne_top : F.occupation Fterm δ Set.univ ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top (F.stopBase Fterm) Set.univ)
    (Measure.le_iff.1 (F.occupation_le Fterm (F.delta_super hmatch)) _ MeasurableSet.univ)

theorem termLaw_finit_univ : F.termLaw Fterm Finit Set.univ = Finit Set.univ :=
  F.termLaw_univ Fterm _ (F.occupation_finit_ne_top hmatch)

theorem termLaw_delta_univ : F.termLaw Fterm δ Set.univ = δ Set.univ :=
  F.termLaw_univ Fterm _ (F.occupation_delta_ne_top hmatch)

/-- `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)` (`main.tex:854–855`). -/
theorem fterm_univ_eq : Fterm Set.univ = Finit Set.univ + δ Set.univ := by
  rw [← F.termLaw_split hmatch, Measure.add_apply, F.termLaw_finit_univ hmatch,
    F.termLaw_delta_univ hmatch]

theorem occupation_normalize_ne_top : F.occupation Fterm (normalize Finit) Set.univ ≠ ∞ := by
  rw [normalize, occupation_smul, Measure.smul_apply, smul_eq_mul]
  by_cases hZ : Finit Set.univ = 0
  · have : Finit = 0 := Measure.measure_univ_eq_zero.1 hZ
    subst this
    have h0 : F.occupation Fterm 0 = 0 := by
      ext s hs
      rw [F.occupation_apply Fterm _ hs]
      have : ∀ n, F.occ Fterm (0 : Measure S) n = 0 := fun n => by
        have := F.occ_smul Fterm 0 0 n; simpa using this
      simp [this]
    simp [h0]
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ) (F.occupation_finit_ne_top hmatch)

/-- **`theo:negative_control`, on the marginals**: `TV(s_τ ‖ F̂_term/F̂_term(𝒮)) ≤ δ(𝒮)/F̂_term(𝒮)`,
for the sampler from `F_init` to `F̂_term`, whenever `(π, F_out)` is flow matching from
`F_init + δ` to `F̂_term` (template: `MFlow.negative_control_tv`). -/
theorem negative_control_marginal [IsFiniteMeasure Finit] [IsFiniteMeasure δ] (hinit : Finit ≠ 0) :
    tvDist (F.sampleLaw Finit Fterm) (normalize Fterm) ≤ δ Set.univ / Fterm Set.univ := by
  haveI : IsFiniteMeasure (F.termLaw Fterm Finit) := isFiniteMeasure_of_le Fterm
    ((Measure.le_add_right le_rfl).trans_eq (F.termLaw_split hmatch))
  haveI : IsFiniteMeasure (F.termLaw Fterm δ) := isFiniteMeasure_of_le Fterm
    ((Measure.le_add_left le_rfl).trans_eq (F.termLaw_split hmatch))
  have hZ : Finit Set.univ ≠ 0 := fun h => hinit (Measure.measure_univ_eq_zero.1 h)
  have ha : F.termLaw Fterm Finit ≠ 0 := fun h => hZ (by
    rw [← F.termLaw_finit_univ hmatch, h]; rfl)
  have hs : F.sampleLaw Finit Fterm = normalize (F.termLaw Fterm Finit) := by
    rw [sampleLaw_eq_smul, normalize, F.termLaw_finit_univ hmatch]
  have h := tvDist_normalize_add_le (F.termLaw Fterm Finit) (F.termLaw Fterm δ) ha
  rw [F.termLaw_split hmatch, F.termLaw_delta_univ hmatch] at h
  rwa [hs]

end Matched

end GenerativeFlow

/-! ## The sampler on the path space

The paper's sampler (`main.tex:163–165`): a Markov chain `(s_t)_{t ≥ 1}`, `s₁ ∼ F_init`,
`s_{t+1} ∼ π(s_t)`, and a time `τ ∈ ℕ_{≥1}` with `P(τ = t | τ ≥ t) = dF_term/d(F_term + F_out)(s_t)`;
the sample is `s_τ`. It is built here by Ionescu-Tulcea (`ProbabilityTheory.Kernel.trajMeasure`)
as a Markov chain `Y_n = (s_{n+1}, b_n)` on `𝒮 × Bool`, `b_n = [τ ≤ n + 1]`: the first coordinate
moves by `π` whatever the flag, and a lowered flag is raised at the new state with probability
`stop`. -/

theorem measurable_eval (n : ℕ) : Measurable fun ω : ℕ → S × Bool => ω n :=
  measurable_pi_apply n

/-- The set of raised flags. -/
def raised : Set (S × Bool) := Prod.snd ⁻¹' {true}

theorem measurableSet_raised : MeasurableSet (raised : Set (S × Bool)) :=
  measurable_snd (measurableSet_singleton true)

/-- The set of lowered flags. -/
def lowered : Set (S × Bool) := Prod.snd ⁻¹' {false}

theorem measurableSet_lowered : MeasurableSet (lowered : Set (S × Bool)) :=
  measurable_snd (measurableSet_singleton false)

omit [MeasurableSpace S] in
theorem compl_lowered : (lowered : Set (S × Bool))ᶜ = raised := by
  ext z; simp [lowered, raised]

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Fterm : Measure S)

/-- The decision at a freshly visited state `y`: `(y, true)` with probability `stop y`,
`(y, false)` with probability `cont y`. -/
noncomputable def decideFun (y : S) : Measure (S × Bool) :=
  F.stop Fterm y • Measure.dirac (y, true) + F.cont Fterm y • Measure.dirac (y, false)

theorem decideFun_apply (y : S) {s : Set (S × Bool)} (hs : MeasurableSet s) :
    F.decideFun Fterm y s = F.stop Fterm y * s.indicator 1 (y, true)
      + F.cont Fterm y * s.indicator 1 (y, false) := by
  rw [decideFun, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul]

theorem measurable_decideFun : Measurable (F.decideFun Fterm) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [F.decideFun_apply Fterm _ hs]
  have h1 : Measurable fun y : S => s.indicator (1 : S × Bool → ℝ≥0∞) (y, true) :=
    (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable fun y : S => s.indicator (1 : S × Bool → ℝ≥0∞) (y, false) :=
    (measurable_one.indicator hs).comp (measurable_id.prodMk measurable_const)
  exact ((F.measurable_stop Fterm).mul h1).add ((F.measurable_cont Fterm).mul h2)

/-- The decision kernel `𝒮 → 𝒮 × Bool`. -/
noncomputable def decide : Kernel S (S × Bool) :=
  ⟨F.decideFun Fterm, F.measurable_decideFun Fterm⟩

theorem decide_apply (y : S) : F.decide Fterm y = F.decideFun Fterm y := rfl

instance isMarkovKernel_decide : IsMarkovKernel (F.decide Fterm) := by
  refine ⟨fun y => ⟨?_⟩⟩
  rw [decide_apply, F.decideFun_apply Fterm y MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [add_comm]; exact F.cont_add_stop Fterm y

/-- The frozen move after stopping: `y ↦ (y, true)`. -/
noncomputable def raiseKernel : Kernel S (S × Bool) :=
  Kernel.deterministic (fun y => (y, true)) (measurable_id.prodMk measurable_const)

/-- **The sampler's transition on `𝒮 × Bool`**: from `(x, b)` the state moves to `y ∼ π(x)`; a
raised flag stays raised, a lowered one is raised with probability `stop y`. -/
noncomputable def pathKernel : Kernel (S × Bool) (S × Bool) := by
  classical
  exact Kernel.piecewise measurableSet_raised
    ((raiseKernel ∘ₖ F.policy).comap Prod.fst measurable_fst)
    ((F.decide Fterm ∘ₖ F.policy).comap Prod.fst measurable_fst)

instance isMarkovKernel_pathKernel : IsMarkovKernel (F.pathKernel Fterm) := by
  unfold pathKernel raiseKernel; infer_instance

theorem pathKernel_true (x : S) :
    F.pathKernel Fterm (x, true) = (F.policy x).bind raiseKernel := by
  classical
  rw [pathKernel, Kernel.piecewise_apply, if_pos (by simp [raised]), Kernel.comap_apply,
    Kernel.comp_apply]

theorem pathKernel_false (x : S) :
    F.pathKernel Fterm (x, false) = (F.policy x).bind (F.decide Fterm) := by
  classical
  rw [pathKernel, Kernel.piecewise_apply, if_neg (by simp [raised]), Kernel.comap_apply,
    Kernel.comp_apply]

/-- The transition kernels of the chain, in the form of Ionescu-Tulcea: the next point depends on
the current one only. -/
noncomputable def pathKernels (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, S × Bool) (S × Bool) :=
  (F.pathKernel Fterm).comap (fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_pathKernels (n : ℕ) : IsMarkovKernel (F.pathKernels Fterm n) := by
  unfold pathKernels; infer_instance

end GenerativeFlow

namespace GenerativeFlow

section PathLaw

variable (F : GenerativeFlow S) (Finit Fterm : Measure S)

/-- **The law of the sampler's trajectory** `(Y_n)_{n ≥ 0}`, `Y_n = (s_{n+1}, b_n)`, from
`Y₀ ∼ (F_init/F_init(𝒮)) ⊗ decide` (Ionescu-Tulcea). -/
noncomputable def pathLaw : Measure (ℕ → S × Bool) :=
  Kernel.trajMeasure (X := fun _ => S × Bool) ((normalize Finit).bind (F.decide Fterm))
    (F.pathKernels Fterm)

/-- The law of `Y_n = (s_{n+1}, b_n)`. -/
noncomputable def lawAt (n : ℕ) : Measure (S × Bool) := (F.pathLaw Finit Fterm).map (fun ω => ω n)

theorem isProbabilityMeasure_start [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) :
    IsProbabilityMeasure ((normalize Finit).bind (F.decide Fterm)) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  simp only [measure_univ, lintegral_const, one_mul]
  exact normalize_univ Finit hinit

instance isProbabilityMeasure_pathLaw' [IsFiniteMeasure Finit] [NeZero Finit] :
    IsProbabilityMeasure (F.pathLaw Finit Fterm) := by
  haveI := F.isProbabilityMeasure_start Finit Fterm (NeZero.ne Finit)
  unfold pathLaw; infer_instance

theorem isProbabilityMeasure_pathLaw [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) :
    IsProbabilityMeasure (F.pathLaw Finit Fterm) := by
  haveI : NeZero Finit := ⟨hinit⟩
  infer_instance

/-- **`Y₀ ∼ (F_init/F_init(𝒮)) ⊗ decide`**: `s₁ ∼ F_init`, and the flag is raised at `s₁` with
probability `stop`. -/
theorem lawAt_zero :
    F.lawAt Finit Fterm 0 = (normalize Finit).bind (F.decide Fterm) := by
  ext B hB
  unfold lawAt pathLaw Kernel.trajMeasure
  rw [Measure.map_apply (measurable_pi_apply 0) hB,
    Measure.bind_apply (measurable_pi_apply 0 hB) (Kernel.aemeasurable _)]
  have key : ∀ x₀ : (Π _ : Finset.Iic 0, S × Bool),
      Kernel.traj (X := fun _ => S × Bool) (F.pathKernels Fterm) 0 x₀ ((fun ω => ω 0) ⁻¹' B)
        = B.indicator 1 (x₀ ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
    intro x₀
    have h := Kernel.traj_map_frestrictLe_apply (X := fun _ => S × Bool)
      (κ := F.pathKernels Fterm) 0 0 x₀
    rw [Kernel.partialTraj_self, Kernel.id_apply] at h
    have hm : MeasurableSet ((fun h : (Π _ : Finset.Iic 0, S × Bool) =>
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' B) := measurable_pi_apply _ hB
    have e : ((fun ω : ℕ → S × Bool => ω 0) ⁻¹' B)
        = Preorder.frestrictLe 0 ⁻¹' ((fun h : (Π _ : Finset.Iic 0, S × Bool) =>
          h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' B) := rfl
    rw [e, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hm, h,
      Measure.dirac_apply' _ hm]
    rfl
  simp_rw [key]
  rw [lintegral_map (f := fun a : (Π _ : Finset.Iic 0, S × Bool) =>
      B.indicator (1 : S × Bool → ℝ≥0∞) (a ⟨0, Finset.mem_Iic.2 le_rfl⟩))
    ((measurable_one.indicator hB).comp (measurable_pi_apply _)) (MeasurableEquiv.measurable _)]
  have : ∀ y : S × Bool, B.indicator (1 : S × Bool → ℝ≥0∞)
      (((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => S × Bool)).symm y)
        ⟨0, Finset.mem_Iic.2 le_rfl⟩) = B.indicator 1 y := fun y => rfl
  simp_rw [this]
  rw [lintegral_indicator_one hB]

/-- **The Markov property, on two consecutive times**:
`P(Y_n ∈ A, Y_{n+1} ∈ B) = ∫_A pathKernel(z)(B) dP_{Y_n}(z)` (from
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`). -/
theorem pathLaw_pair [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {A B : Set (S × Bool)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    F.pathLaw Finit Fterm {ω | ω n ∈ A ∧ ω (n + 1) ∈ B}
      = ∫⁻ z in A, F.pathKernel Fterm z B ∂(F.lawAt Finit Fterm n) := by
  haveI := F.isProbabilityMeasure_start Finit Fterm hinit
  have L := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ => S × Bool)
    (μ₀ := (normalize Finit).bind (F.decide Fterm)) (κ := F.pathKernels Fterm) (a := n)
  set e : (Π _ : Finset.Iic n, S × Bool) → S × Bool := fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩
    with he_def
  have he : Measurable e := measurable_pi_apply _
  have hR : MeasurableSet ((e ⁻¹' A) ×ˢ B) := (he hA).prod hB
  have h1 := congrArg (fun m => m ((e ⁻¹' A) ×ˢ B)) L
  rw [Measure.compProd_apply_prod (he hA) hB,
    Measure.map_apply ((Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply _)) hR]
    at h1
  have hset : (fun x : ℕ → S × Bool => (Preorder.frestrictLe n x, x (n + 1))) ⁻¹' ((e ⁻¹' A) ×ˢ B)
      = {ω | ω n ∈ A ∧ ω (n + 1) ∈ B} := by
    ext ω; simp [e, Preorder.frestrictLe]
  rw [hset] at h1
  unfold lawAt
  unfold pathLaw
  rw [← h1]
  have hmap : (Kernel.trajMeasure (X := fun _ => S × Bool) ((normalize Finit).bind (F.decide Fterm))
      (F.pathKernels Fterm)).map (fun ω => ω n)
      = ((Kernel.trajMeasure (X := fun _ => S × Bool) ((normalize Finit).bind (F.decide Fterm))
        (F.pathKernels Fterm)).map (Preorder.frestrictLe n)).map e := by
    rw [Measure.map_map he (Preorder.measurable_frestrictLe n)]; rfl
  rw [hmap, setLIntegral_map hA (Kernel.measurable_coe _ hB) he]
  rfl

/-- `P(Y_{n+1} ∈ B) = ∫ pathKernel(z)(B) dP_{Y_n}(z)`: Chapman–Kolmogorov. -/
theorem lawAt_succ_apply [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {B : Set (S × Bool)}
    (hB : MeasurableSet B) :
    F.lawAt Finit Fterm (n + 1) B = ∫⁻ z, F.pathKernel Fterm z B ∂(F.lawAt Finit Fterm n) := by
  have h := F.pathLaw_pair Finit Fterm hinit n MeasurableSet.univ hB
  rw [Measure.restrict_univ] at h
  rw [← h, lawAt, Measure.map_apply (measurable_eval (n + 1)) hB]
  congr 1; ext ω; simp

end PathLaw

/-! ### The transition, evaluated -/

variable (F : GenerativeFlow S) (Fterm : Measure S)

theorem decide_apply_prod (y : S) {A : Set S} (hA : MeasurableSet A) (b : Bool) :
    F.decide Fterm y (A ×ˢ {b}) = (if b then F.stop Fterm y else F.cont Fterm y) * A.indicator 1 y := by
  rw [decide_apply, F.decideFun_apply Fterm y (hA.prod (measurableSet_singleton b))]
  by_cases hy : y ∈ A <;> cases b <;> simp [hy, Set.indicator, Set.mem_prod]

theorem decide_apply_prod_univ (y : S) {A : Set S} (hA : MeasurableSet A) :
    F.decide Fterm y (A ×ˢ Set.univ) = A.indicator 1 y := by
  rw [decide_apply, F.decideFun_apply Fterm y (hA.prod MeasurableSet.univ)]
  by_cases hy : y ∈ A
  · simp only [Set.indicator, Set.mem_prod, hy, Set.mem_univ, and_self, if_true, Pi.one_apply,
      mul_one]
    rw [add_comm]; exact F.cont_add_stop Fterm y
  · simp [hy, Set.indicator]

theorem pathKernel_raised_lowered (z : S × Bool) (hz : z ∈ raised) :
    F.pathKernel Fterm z lowered = 0 := by
  obtain ⟨x, b⟩ := z
  simp only [raised, Set.mem_preimage, Set.mem_singleton_iff] at hz
  subst hz
  rw [pathKernel_true, Measure.bind_apply measurableSet_lowered (Kernel.aemeasurable _)]
  have h0 : ∀ a : S, raiseKernel a (lowered : Set (S × Bool)) = 0 := fun a => by
    rw [raiseKernel, Kernel.deterministic_apply, Measure.dirac_apply' _ measurableSet_lowered]
    simp [lowered]
  simp [h0]

theorem pathKernel_raised_prod_false (z : S × Bool) (hz : z ∈ raised) (A : Set S)
    (b : Bool) (hb : b = false) :
    F.pathKernel Fterm z (A ×ˢ {b}) = 0 := by
  subst hb
  refine le_antisymm ?_ zero_le
  calc F.pathKernel Fterm z (A ×ˢ {false}) ≤ F.pathKernel Fterm z lowered :=
        measure_mono (fun w hw => by simp [lowered] at hw ⊢; exact hw.2)
    _ = 0 := F.pathKernel_raised_lowered Fterm z hz

theorem pathKernel_false_apply (x : S) {B : Set (S × Bool)} (hB : MeasurableSet B) :
    F.pathKernel Fterm (x, false) B = ∫⁻ y, F.decide Fterm y B ∂(F.policy x) := by
  rw [pathKernel_false, Measure.bind_apply hB (Kernel.aemeasurable _)]

theorem pathKernel_apply_prod_univ (z : S × Bool) {A : Set S} (hA : MeasurableSet A) :
    F.pathKernel Fterm z (A ×ˢ Set.univ) = F.policy z.1 A := by
  obtain ⟨x, b⟩ := z
  cases b
  · rw [F.pathKernel_false_apply Fterm x (hA.prod MeasurableSet.univ)]
    simp_rw [F.decide_apply_prod_univ Fterm _ hA]
    rw [lintegral_indicator_one hA]
  · rw [pathKernel_true, Measure.bind_apply (hA.prod MeasurableSet.univ) (Kernel.aemeasurable _)]
    simp only [raiseKernel, Kernel.deterministic_apply]
    simp_rw [Measure.dirac_apply' _ (hA.prod MeasurableSet.univ)]
    have : ∀ y, (A ×ˢ (Set.univ : Set Bool)).indicator (1 : S × Bool → ℝ≥0∞) (y, true)
        = A.indicator 1 y := fun y => by by_cases hy : y ∈ A <;> simp [hy, Set.indicator]
    simp_rw [this]
    rw [lintegral_indicator_one hA]

/-! ### The law of the lowered flag -/

section Invariant

variable (Finit : Measure S)

/-- `(cont · occ n)`: the law of `s_{n+1}` on `{b_n = false}` = `{τ > n + 1}`. -/
def LoweredLaw (n : ℕ) : Prop :=
  ((F.lawAt Finit Fterm n).restrict lowered).map Prod.fst
    = (F.occ Fterm (normalize Finit) n).withDensity (F.cont Fterm)

theorem lintegral_lowered {n : ℕ} (h : F.LoweredLaw Fterm Finit n) {g : S × Bool → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z in lowered, g z ∂(F.lawAt Finit Fterm n)
      = ∫⁻ x, F.cont Fterm x * g (x, false) ∂(F.occ Fterm (normalize Finit) n) := by
  have e1 : ∫⁻ z in lowered, g z ∂(F.lawAt Finit Fterm n)
      = ∫⁻ z in lowered, g (z.1, false) ∂(F.lawAt Finit Fterm n) := by
    refine setLIntegral_congr_fun measurableSet_lowered fun z hz => ?_
    obtain ⟨x, b⟩ := z
    simp only [lowered, Set.mem_preimage, Set.mem_singleton_iff] at hz
    subst hz; rfl
  have hφ : Measurable fun x : S => g (x, false) := hg.comp (measurable_id.prodMk measurable_const)
  rw [e1, ← lintegral_map (f := fun x => g (x, false)) hφ measurable_fst]
  unfold LoweredLaw at h
  rw [h, lintegral_withDensity_eq_lintegral_mul _ (F.measurable_cont Fterm) hφ]
  rfl

theorem lintegral_vanishing {n : ℕ} {g : S × Bool → ℝ≥0∞} (hg0 : ∀ z ∈ raised, g z = 0) :
    ∫⁻ z, g z ∂(F.lawAt Finit Fterm n) = ∫⁻ z in lowered, g z ∂(F.lawAt Finit Fterm n) := by
  rw [← lintegral_add_compl g measurableSet_lowered, compl_lowered,
    setLIntegral_eq_zero measurableSet_raised (fun z hz => hg0 z hz), add_zero]

/-- `∫ (∫_A h dπ(x)) d(cont · μ)(x) = ∫_A h d(step μ)`. -/
theorem lintegral_step {μ : Measure S} {h : S → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, F.cont Fterm x * ∫⁻ y, h y ∂(F.policy x) ∂μ = ∫⁻ y, h y ∂(F.step Fterm μ) := by
  rw [step, Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (F.measurable_cont Fterm)
      (Measurable.lintegral_kernel hh)]
  rfl

theorem loweredLaw_zero : F.LoweredLaw Fterm Finit 0 := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA),
    withDensity_apply _ hA, lawAt_zero, occ_zero]
  have e : Prod.fst ⁻¹' A ∩ lowered = A ×ˢ ({false} : Set Bool) := by
    ext z; simp [lowered, Set.mem_prod]
  rw [e, Measure.bind_apply (hA.prod (measurableSet_singleton _)) (Kernel.aemeasurable _)]
  simp_rw [F.decide_apply_prod Fterm _ hA false]
  simp only [Bool.false_eq_true, if_false]
  rw [← lintegral_indicator hA]
  congr 1; ext y; by_cases hy : y ∈ A <;> simp [hy, Set.indicator]

theorem loweredLaw_succ [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) {n : ℕ}
    (h : F.LoweredLaw Fterm Finit n) : F.LoweredLaw Fterm Finit (n + 1) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA),
    withDensity_apply _ hA]
  have e : Prod.fst ⁻¹' A ∩ lowered = A ×ˢ ({false} : Set Bool) := by
    ext z; simp [lowered, Set.mem_prod]
  have hAf : MeasurableSet (A ×ˢ ({false} : Set Bool)) := hA.prod (measurableSet_singleton _)
  rw [e, F.lawAt_succ_apply Finit Fterm hinit n hAf,
    F.lintegral_vanishing Fterm Finit (fun z hz => F.pathKernel_raised_prod_false Fterm z hz A
      false rfl),
    F.lintegral_lowered Fterm Finit h (Kernel.measurable_coe _ hAf)]
  simp_rw [F.pathKernel_false_apply Fterm _ hAf, F.decide_apply_prod Fterm _ hA false]
  simp only [Bool.false_eq_true, if_false]
  rw [occ_succ, ← lintegral_indicator hA,
    ← F.lintegral_step Fterm ((F.measurable_cont Fterm).indicator hA)]
  congr 1; ext x; congr 1; congr 1; ext y
  by_cases hy : y ∈ A <;> simp [hy, Set.indicator]

theorem loweredLaw [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) :
    F.LoweredLaw Fterm Finit n := by
  induction n with
  | zero => exact F.loweredLaw_zero Fterm Finit
  | succ n ih => exact F.loweredLaw_succ Fterm Finit hinit ih

end Invariant

end GenerativeFlow

/-! ### The sampling time and the sample -/

/-- The index of the first raised flag (`τ − 1`), `⊤` if none is raised. -/
noncomputable def stopIndex (ω : ℕ → S × Bool) : ℕ∞ := by
  classical
  exact if h : ∃ n, (ω n).2 = true then (Nat.find h : ℕ∞) else ⊤

/-- **The sampling time** `τ = stopIndex + 1 ∈ ℕ_{≥1} ∪ {∞}` (`main.tex:164`). -/
noncomputable def stopTime (ω : ℕ → S × Bool) : ℕ∞ := stopIndex ω + 1

/-- **The sample** `s_τ = (Y_{τ−1})₁` (an arbitrary point on `{τ = ∞}`, a null set). -/
noncomputable def sampledState (ω : ℕ → S × Bool) : S := (ω (stopIndex ω).toNat).1

omit [MeasurableSpace S] in
theorem stopIndex_eq_coe_iff (ω : ℕ → S × Bool) (n : ℕ) :
    stopIndex ω = n ↔ (ω n).2 = true ∧ ∀ k < n, (ω k).2 = false := by
  classical
  unfold stopIndex
  split_ifs with h
  · rw [Nat.cast_inj, Nat.find_eq_iff]
    simp
  · have h' : ∀ n, (ω n).2 = false := fun n => by simpa using not_exists.1 h n
    simp only [ENat.top_ne_coe, false_iff, not_and]
    intro hn; simp [h' n] at hn

omit [MeasurableSpace S] in
theorem stopIndex_eq_zero_iff (ω : ℕ → S × Bool) : stopIndex ω = 0 ↔ (ω 0).2 = true := by
  have := stopIndex_eq_coe_iff ω 0
  simpa using this

omit [MeasurableSpace S] in
theorem stopIndex_eq_top_iff (ω : ℕ → S × Bool) :
    stopIndex ω = ⊤ ↔ ∀ n, (ω n).2 = false := by
  classical
  unfold stopIndex
  split_ifs with h
  · simp only [ENat.coe_ne_top, false_iff, not_forall]
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by simp [hn]⟩
  · simpa using not_exists.1 h

omit [MeasurableSpace S] in
theorem coe_le_stopIndex_iff (ω : ℕ → S × Bool) (n : ℕ) :
    (n : ℕ∞) ≤ stopIndex ω ↔ ∀ k < n, (ω k).2 = false := by
  constructor
  · intro h k hk
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have : stopIndex ω ≤ k := by
      classical
      unfold stopIndex
      rw [dif_pos ⟨k, hc⟩, Nat.cast_le]
      exact Nat.find_min' _ hc
    exact absurd (h.trans this) (by exact_mod_cast hk.not_ge)
  · intro h
    induction hs : stopIndex ω using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [stopIndex_eq_coe_iff] at hs
      by_contra hc
      have : m < n := by exact_mod_cast not_le.1 hc
      simp [h m this] at hs

theorem measurableSet_stopIndex_eq (n : ℕ) :
    MeasurableSet {ω : ℕ → S × Bool | stopIndex ω = n} := by
  have e : {ω : ℕ → S × Bool | stopIndex ω = n}
      = (fun ω => ω n) ⁻¹' raised ∩ ⋂ k ∈ Finset.range n, (fun ω => ω k) ⁻¹' lowered := by
    ext ω
    simp [stopIndex_eq_coe_iff, raised, lowered]
  rw [e]
  exact ((measurable_eval n) measurableSet_raised).inter
    (Finset.measurableSet_biInter _ fun k _ => (measurable_eval k) measurableSet_lowered)

theorem measurableSet_stopIndex_eq_top :
    MeasurableSet {ω : ℕ → S × Bool | stopIndex ω = ⊤} := by
  have e : {ω : ℕ → S × Bool | stopIndex ω = ⊤} = ⋂ n, (fun ω => ω n) ⁻¹' lowered := by
    ext ω
    simp [stopIndex_eq_top_iff, lowered]
  rw [e]
  exact MeasurableSet.iInter fun n => (measurable_eval n) measurableSet_lowered

theorem measurable_stopIndex : Measurable (stopIndex : (ℕ → S × Bool) → ℕ∞) := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top => exact measurableSet_stopIndex_eq_top
  | coe n => exact measurableSet_stopIndex_eq n

theorem measurable_stopTime : Measurable (stopTime : (ℕ → S × Bool) → ℕ∞) :=
  measurable_stopIndex.add_const _

theorem measurable_sampledState : Measurable (sampledState : (ℕ → S × Bool) → S) := by
  have h : Measurable fun p : (ℕ → S × Bool) × ℕ∞ => (p.1 p.2.toNat).1 :=
    measurable_from_prod_countable_left fun m => measurable_fst.comp (measurable_eval m.toNat)
  exact h.comp (measurable_id.prodMk measurable_stopIndex)

/-- Flags that, once raised, stay raised. -/
def FlagsMonotone (ω : ℕ → S × Bool) : Prop := ∀ k, (ω k).2 = true → (ω (k + 1)).2 = true

omit [MeasurableSpace S] in
theorem FlagsMonotone.raised_of_le {ω : ℕ → S × Bool} (hω : FlagsMonotone ω) {k m : ℕ}
    (hk : (ω k).2 = true) (hkm : k ≤ m) : (ω m).2 = true := by
  induction m, hkm using Nat.le_induction with
  | base => exact hk
  | succ m _ ih => exact hω m ih

omit [MeasurableSpace S] in
theorem FlagsMonotone.lowered_iff {ω : ℕ → S × Bool} (hω : FlagsMonotone ω) (n : ℕ) :
    (∀ k < n + 1, (ω k).2 = false) ↔ (ω n).2 = false := by
  constructor
  · intro h; exact h n (Nat.lt_succ_self n)
  · intro h k hk
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have := hω.raised_of_le hc (Nat.lt_succ_iff.1 hk)
    simp [this] at h

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Finit Fterm : Measure S)

/-- **A raised flag stays raised**, almost surely. -/
theorem ae_flagsMonotone [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) :
    ∀ᵐ ω ∂(F.pathLaw Finit Fterm), FlagsMonotone ω := by
  refine ae_all_iff.2 fun k => ?_
  rw [ae_iff]
  have e : {ω : ℕ → S × Bool | ¬((ω k).2 = true → (ω (k + 1)).2 = true)}
      = {ω | ω k ∈ raised ∧ ω (k + 1) ∈ lowered} := by
    ext ω; simp [raised, lowered]
  rw [e, F.pathLaw_pair Finit Fterm hinit k measurableSet_raised measurableSet_lowered]
  exact setLIntegral_eq_zero measurableSet_raised fun z hz =>
    F.pathKernel_raised_lowered Fterm z hz

/-- `P(τ = n + 1, s_{n+1} ∈ A) = ∫_A stop d(occ n)`. -/
theorem pathLaw_stopIndex_eq [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {A : Set S}
    (hA : MeasurableSet A) :
    F.pathLaw Finit Fterm {ω | stopIndex ω = n ∧ (ω n).1 ∈ A}
      = ∫⁻ x in A, F.stop Fterm x ∂(F.occ Fterm (normalize Finit) n) := by
  have hAt : MeasurableSet (A ×ˢ ({true} : Set Bool)) := hA.prod (measurableSet_singleton _)
  cases n with
  | zero =>
    have e : {ω : ℕ → S × Bool | stopIndex ω = ((0 : ℕ) : ℕ∞) ∧ (ω 0).1 ∈ A}
        = (fun ω => ω 0) ⁻¹' (A ×ˢ {true}) := by
      ext ω; simp [stopIndex_eq_zero_iff, Set.mem_prod, and_comm]
    rw [e, ← Measure.map_apply (measurable_eval 0) hAt]
    change F.lawAt Finit Fterm 0 _ = _
    rw [lawAt_zero, Measure.bind_apply hAt (Kernel.aemeasurable _), occ_zero]
    simp_rw [F.decide_apply_prod Fterm _ hA true]
    simp only [if_true]
    rw [← lintegral_indicator hA]
    congr 1; ext y; by_cases hy : y ∈ A <;> simp [hy, Set.indicator]
  | succ m =>
    have e : {ω : ℕ → S × Bool | stopIndex ω = ((m + 1 : ℕ) : ℕ∞) ∧ (ω (m + 1)).1 ∈ A}
        =ᵐ[F.pathLaw Finit Fterm] {ω | ω m ∈ lowered ∧ ω (m + 1) ∈ A ×ˢ {true}} := by
      filter_upwards [F.ae_flagsMonotone Finit Fterm hinit] with ω hω
      apply propext
      change (stopIndex ω = ((m + 1 : ℕ) : ℕ∞) ∧ (ω (m + 1)).1 ∈ A)
        ↔ (ω m ∈ lowered ∧ ω (m + 1) ∈ A ×ˢ {true})
      simp only [stopIndex_eq_coe_iff, lowered, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_prod]
      rw [hω.lowered_iff m]
      tauto
    rw [measure_congr e, F.pathLaw_pair Finit Fterm hinit m measurableSet_lowered hAt,
      F.lintegral_lowered Fterm Finit (F.loweredLaw Fterm Finit hinit m)
        (Kernel.measurable_coe _ hAt)]
    simp_rw [F.pathKernel_false_apply Fterm _ hAt, F.decide_apply_prod Fterm _ hA true]
    simp only [if_true]
    rw [occ_succ, ← lintegral_indicator hA,
      ← F.lintegral_step Fterm ((F.measurable_stop Fterm).indicator hA)]
    congr 1; ext x; congr 1; congr 1; ext y
    by_cases hy : y ∈ A <;> simp [hy, Set.indicator]

/-- `P(τ ≥ n + 1, s_{n+1} ∈ A) = occ n (A)`. -/
theorem pathLaw_le_stopIndex [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {A : Set S}
    (hA : MeasurableSet A) :
    F.pathLaw Finit Fterm {ω | (n : ℕ∞) ≤ stopIndex ω ∧ (ω n).1 ∈ A}
      = F.occ Fterm (normalize Finit) n A := by
  have hAu : MeasurableSet (A ×ˢ (Set.univ : Set Bool)) := hA.prod MeasurableSet.univ
  cases n with
  | zero =>
    have e : {ω : ℕ → S × Bool | ((0 : ℕ) : ℕ∞) ≤ stopIndex ω ∧ (ω 0).1 ∈ A}
        = (fun ω => ω 0) ⁻¹' (A ×ˢ Set.univ) := by
      ext ω; simp [Set.mem_prod]
    rw [e, ← Measure.map_apply (measurable_eval 0) hAu]
    change F.lawAt Finit Fterm 0 _ = _
    rw [lawAt_zero, Measure.bind_apply hAu (Kernel.aemeasurable _), occ_zero]
    simp_rw [F.decide_apply_prod_univ Fterm _ hA]
    rw [lintegral_indicator_one hA]
  | succ m =>
    have e : {ω : ℕ → S × Bool | ((m + 1 : ℕ) : ℕ∞) ≤ stopIndex ω ∧ (ω (m + 1)).1 ∈ A}
        =ᵐ[F.pathLaw Finit Fterm] {ω | ω m ∈ lowered ∧ ω (m + 1) ∈ A ×ˢ Set.univ} := by
      filter_upwards [F.ae_flagsMonotone Finit Fterm hinit] with ω hω
      apply propext
      change (((m + 1 : ℕ) : ℕ∞) ≤ stopIndex ω ∧ (ω (m + 1)).1 ∈ A)
        ↔ (ω m ∈ lowered ∧ ω (m + 1) ∈ A ×ˢ Set.univ)
      simp only [coe_le_stopIndex_iff, lowered, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ, and_true]
      rw [hω.lowered_iff m]
    rw [measure_congr e, F.pathLaw_pair Finit Fterm hinit m measurableSet_lowered hAu,
      F.lintegral_lowered Fterm Finit (F.loweredLaw Fterm Finit hinit m)
        (Kernel.measurable_coe _ hAu)]
    simp_rw [F.pathKernel_apply_prod_univ Fterm _ hA]
    rw [occ_succ, F.step_apply Fterm _ hA]

/-- **The hazard of `main.tex:164`**: `P(τ = t, s_t ∈ A) = ∫_A stop dP(τ ≥ t, s_t ∈ ·)` for every
`t ≥ 1` (here `t = n + 1`), the measure `A ↦ P(τ ≥ t, s_t ∈ A)` being `occ n`. -/
theorem pathLaw_hazard [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {A : Set S}
    (hA : MeasurableSet A) :
    F.pathLaw Finit Fterm {ω | stopTime ω = (n + 1 : ℕ) ∧ (ω n).1 ∈ A}
      = ∫⁻ x in A, F.stop Fterm x ∂(F.occ Fterm (normalize Finit) n) ∧
    ∀ B, MeasurableSet B →
      F.pathLaw Finit Fterm {ω | ((n + 1 : ℕ) : ℕ∞) ≤ stopTime ω ∧ (ω n).1 ∈ B}
        = F.occ Fterm (normalize Finit) n B := by
  refine ⟨?_, fun B hB => ?_⟩
  · have e : {ω : ℕ → S × Bool | stopTime ω = (n + 1 : ℕ) ∧ (ω n).1 ∈ A}
        = {ω | stopIndex ω = n ∧ (ω n).1 ∈ A} := by
      ext ω
      simp only [Set.mem_setOf_eq, stopTime, Nat.cast_add, Nat.cast_one]
      rw [(ENat.add_left_injective_of_ne_top ENat.one_ne_top).eq_iff]
    rw [e, F.pathLaw_stopIndex_eq Finit Fterm hinit n hA]
  · have e : {ω : ℕ → S × Bool | ((n + 1 : ℕ) : ℕ∞) ≤ stopTime ω ∧ (ω n).1 ∈ B}
        = {ω | (n : ℕ∞) ≤ stopIndex ω ∧ (ω n).1 ∈ B} := by
      ext ω
      simp only [Set.mem_setOf_eq, stopTime, Nat.cast_add, Nat.cast_one]
      rw [ENat.add_le_add_iff_right ENat.one_ne_top]
    rw [e, F.pathLaw_le_stopIndex Finit Fterm hinit n hB]

/-- **The first coordinate is the paper's chain** (`main.tex:163`): `s_{n+1} ∼ F_init πⁿ`. -/
theorem pathLaw_map_state [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) :
    (F.pathLaw Finit Fterm).map (fun ω => (ω n).1) = pushIter F.policy n (normalize Finit) := by
  have hfst : ∀ m, (F.pathLaw Finit Fterm).map (fun ω => (ω m).1)
      = (F.lawAt Finit Fterm m).map Prod.fst := fun m => by
    rw [lawAt, Measure.map_map measurable_fst (measurable_eval m)]; rfl
  induction n with
  | zero =>
    rw [hfst, lawAt_zero]
    ext A hA
    rw [Measure.map_apply measurable_fst hA, pushIter_zero,
      Measure.bind_apply (measurable_fst hA) (Kernel.aemeasurable _)]
    have e : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set Bool) := by ext z; simp
    simp_rw [e, F.decide_apply_prod_univ Fterm _ hA]
    rw [lintegral_indicator_one hA]
  | succ n ih =>
    rw [hfst, pushIter_succ, ← ih, hfst]
    ext A hA
    have e : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set Bool) := by ext z; simp
    rw [Measure.map_apply measurable_fst hA, e,
      F.lawAt_succ_apply Finit Fterm hinit n (hA.prod MeasurableSet.univ),
      Measure.bind_apply hA (Kernel.aemeasurable _), lintegral_map (F.policy.measurable_coe hA)
        measurable_fst]
    simp_rw [F.pathKernel_apply_prod_univ Fterm _ hA]

/-- **The Markov property of the chain** `(s_t)` (`main.tex:163`, `s_{t+1} ∼ π(s_t)` whatever the
stopping): `P(s_{n+1} ∈ A, s_{n+2} ∈ B) = ∫_A π(x)(B) dP_{s_{n+1}}(x)`. -/
theorem pathLaw_chain [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) (n : ℕ) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    F.pathLaw Finit Fterm {ω | (ω n).1 ∈ A ∧ (ω (n + 1)).1 ∈ B}
      = ∫⁻ x in A, F.policy x B ∂((F.pathLaw Finit Fterm).map (fun ω => (ω n).1)) := by
  have e : {ω : ℕ → S × Bool | (ω n).1 ∈ A ∧ (ω (n + 1)).1 ∈ B}
      = {ω | ω n ∈ A ×ˢ Set.univ ∧ ω (n + 1) ∈ B ×ˢ Set.univ} := by
    ext ω; simp [Set.mem_prod]
  rw [e, F.pathLaw_pair Finit Fterm hinit n (hA.prod MeasurableSet.univ)
    (hB.prod MeasurableSet.univ)]
  simp_rw [F.pathKernel_apply_prod_univ Fterm _ hB]
  have hm : (F.pathLaw Finit Fterm).map (fun ω => (ω n).1) = (F.lawAt Finit Fterm n).map Prod.fst := by
    rw [lawAt, Measure.map_map measurable_fst (measurable_eval n)]; rfl
  rw [hm, setLIntegral_map hA (F.policy.measurable_coe hB) measurable_fst, Set.prod_univ]

theorem termLaw_apply_tsum (μ₀ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    F.termLaw Fterm μ₀ A = ∑' n, ∫⁻ x in A, F.stop Fterm x ∂(F.occ Fterm μ₀ n) := by
  rw [termLaw, occupation, withDensity_sum, Measure.sum_apply _ hA]
  exact tsum_congr fun k => withDensity_apply _ hA

/-- **The law of `s_τ` on `{τ < ∞}` is `stop · ∑ₙ occ n`**: the path space agrees with the
marginal reading (`GFNBounds`' `chainLaw`, whose limit is `termLaw`). -/
theorem pathLaw_stopped_sampled [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) {A : Set S}
    (hA : MeasurableSet A) :
    F.pathLaw Finit Fterm {ω | stopIndex ω ≠ ⊤ ∧ sampledState ω ∈ A}
      = F.sampleLaw Finit Fterm A := by
  have e : {ω : ℕ → S × Bool | stopIndex ω ≠ ⊤ ∧ sampledState ω ∈ A}
      = ⋃ n : ℕ, {ω | stopIndex ω = n ∧ (ω n).1 ∈ A} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(stopIndex ω).toNat, ENat.coe_toNat h1 |>.symm, h2⟩
    · rintro ⟨n, h1, h2⟩
      refine ⟨by rw [h1]; exact ENat.coe_ne_top n, ?_⟩
      simp only [sampledState, h1, ENat.toNat_coe]; exact h2
  rw [e, measure_iUnion]
  · rw [sampleLaw, F.termLaw_apply_tsum Fterm _ hA]
    exact tsum_congr fun n => F.pathLaw_stopIndex_eq Finit Fterm hinit n hA
  · intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    have := hi.1.symm.trans hj.1
    exact_mod_cast this
  · exact fun n => (measurableSet_stopIndex_eq n).inter ((measurable_eval n) (measurable_fst hA))

/-- `(m : ℝ≥0∞) = ∑_{n ≥ 0} [n < m]` for `m ∈ ℕ ∪ {∞}`. -/
theorem _root_.ENat.toENNReal_eq_tsum (m : ℕ∞) :
    (m : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < m then 1 else 0 := by
  induction m using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.coe_lt_top, if_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe k =>
    rw [tsum_eq_sum (s := Finset.range k)]
    · simp only [Nat.cast_lt, ENat.toENNReal_coe]
      rw [Finset.sum_ite_of_true (fun n hn => Finset.mem_range.1 hn)]
      simp
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp only [Nat.cast_lt]
      rw [if_neg (not_lt.2 hn)]

/-- **`𝔼(τ)` on the path space is `∑_{n ≥ 0} P(τ > n)`**, the marginal `expectedTau`. -/
theorem lintegral_stopTime [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) :
    ∫⁻ ω, (stopTime ω : ℝ≥0∞) ∂(F.pathLaw Finit Fterm) = F.expectedTau Finit Fterm := by
  have hmeas : ∀ n : ℕ, MeasurableSet {ω : ℕ → S × Bool | (n : ℕ∞) < stopTime ω} := fun n =>
    measurable_stopTime (MeasurableSet.of_discrete (s := Set.Ioi (n : ℕ∞)))
  have h1 : ∀ ω : ℕ → S × Bool, (stopTime ω : ℝ≥0∞)
      = ∑' n : ℕ, {ω : ℕ → S × Bool | (n : ℕ∞) < stopTime ω}.indicator 1 ω := by
    intro ω
    rw [ENat.toENNReal_eq_tsum]
    exact tsum_congr fun n => by simp [Set.indicator]
  simp_rw [h1]
  rw [lintegral_tsum fun n => (measurable_one.indicator (hmeas n)).aemeasurable]
  simp_rw [lintegral_indicator_one (hmeas _)]
  refine tsum_congr fun n => ?_
  have e : {ω : ℕ → S × Bool | (n : ℕ∞) < stopTime ω}
      = {ω | (n : ℕ∞) ≤ stopIndex ω ∧ (ω n).1 ∈ Set.univ} := by
    ext ω
    simp only [Set.mem_setOf_eq, stopTime, Set.mem_univ, and_true]
    exact ENat.lt_add_one_iff' (ENat.coe_ne_top n)
  rw [e, F.pathLaw_le_stopIndex Finit Fterm hinit n MeasurableSet.univ]
  rfl

/-- **Termination and the law of `s_τ`**: when `𝔼(τ) < ∞`, `τ < ∞` almost surely and the law of
`s_τ` is the marginal `sampleLaw`. -/
theorem pathLaw_sampledState [IsFiniteMeasure Finit] (hinit : Finit ≠ 0)
    (hE : F.expectedTau Finit Fterm ≠ ∞) :
    F.pathLaw Finit Fterm {ω | stopTime ω = ⊤} = 0 ∧
    (F.pathLaw Finit Fterm).map sampledState = F.sampleLaw Finit Fterm := by
  haveI := F.isProbabilityMeasure_pathLaw Finit Fterm hinit
  have hQ : F.occupation Fterm (normalize Finit) Set.univ ≠ ∞ := by
    rwa [← expectedTau_eq_occupation]
  have hS : F.sampleLaw Finit Fterm Set.univ = 1 := by
    rw [sampleLaw, F.termLaw_univ Fterm _ hQ, normalize_univ _ hinit]
  have hT : {ω : ℕ → S × Bool | stopTime ω = ⊤} = {ω | stopIndex ω = ⊤} := by
    ext ω
    simp only [Set.mem_setOf_eq, stopTime]
    constructor
    · intro h
      by_contra hc
      exact absurd h (WithTop.add_ne_top.2 ⟨hc, ENat.one_ne_top⟩)
    · intro h; rw [h]; rfl
  have hcompl : {ω : ℕ → S × Bool | stopIndex ω = ⊤}ᶜ
      = {ω | stopIndex ω ≠ ⊤ ∧ sampledState ω ∈ Set.univ} := by
    ext ω; simp
  have htop : F.pathLaw Finit Fterm {ω | stopIndex ω = ⊤} = 0 := by
    rw [← prob_compl_eq_one_iff measurableSet_stopIndex_eq_top, hcompl,
      F.pathLaw_stopped_sampled Finit Fterm hinit MeasurableSet.univ, hS]
  refine ⟨hT ▸ htop, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_sampledState hA,
    ← F.pathLaw_stopped_sampled Finit Fterm hinit hA]
  refine measure_congr ?_
  have hae : ∀ᵐ ω ∂(F.pathLaw Finit Fterm), stopIndex ω ≠ ⊤ := by
    rw [ae_iff]; simpa using htop
  filter_upwards [hae] with ω hω
  apply propext
  change sampledState ω ∈ A ↔ (stopIndex ω ≠ ⊤ ∧ sampledState ω ∈ A)
  exact ⟨fun h => ⟨hω, h⟩, fun h => h.2⟩

end GenerativeFlow

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Finit Fterm : Measure S)

/-- **The hazard with the paper's own stopping probability**: where the sampler's unstopped mass
never charges a `(F_term + F_out)`-null set, `P(τ = t, s_t ∈ A) = ∫_A dF_term/d(F_term + F_out)
dP(τ ≥ t, s_t ∈ ·)` (`main.tex:164` verbatim, `t = n + 1`). -/
theorem pathLaw_hazard_rnDeriv [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] (hinit : Finit ≠ 0)
    (hdom : F.occupation Fterm (normalize Finit) ≪ Fterm + F.outflow) (n : ℕ) {A : Set S}
    (hA : MeasurableSet A) :
    F.pathLaw Finit Fterm {ω | stopTime ω = (n + 1 : ℕ) ∧ (ω n).1 ∈ A}
      = ∫⁻ x in A, Fterm.rnDeriv (Fterm + F.outflow) x ∂(F.occ Fterm (normalize Finit) n) := by
  rw [(F.pathLaw_hazard Finit Fterm hinit n hA).1]
  have hac : F.occ Fterm (normalize Finit) n ≪ F.stopBase Fterm :=
    (Measure.absolutelyContinuous_of_le (Measure.le_sum _ n)).trans hdom
  exact setLIntegral_congr_fun_ae hA ((hac.ae_eq (F.stop_ae_eq Fterm)).mono fun x hx _ => hx)

/-- Under flow matching the sampler's unstopped mass is dominated by `(F_term + F_out)/F_init(𝒮)`,
so `pathLaw_hazard_rnDeriv` applies. -/
theorem occupation_ac_of_isFlowMatching [IsFiniteMeasure Fterm]
    (hFM : F.IsFlowMatching Finit Fterm) :
    F.occupation Fterm (normalize Finit) ≪ Fterm + F.outflow :=
  (Measure.absolutelyContinuous_of_le
    (F.occupation_le Fterm (le_of_eq (F.normalize_add_step Finit Fterm hFM)))).trans
    Measure.smul_absolutelyContinuous

/-- For the sampler from `F_init` to `F̂_term` the unstopped mass is dominated by
`(F̂_term + F_out)/F_init(𝒮)`, so `pathLaw_hazard_rnDeriv` applies. -/
theorem occupation_ac_of_matched [IsFiniteMeasure Fterm] {δ : Measure S}
    (hmatch : Finit + δ + F.outflow.bind F.policy = Fterm + F.outflow) :
    F.occupation Fterm (normalize Finit) ≪ Fterm + F.outflow := by
  rw [normalize, occupation_smul]
  exact Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le (F.occupation_le Fterm (F.finit_super hmatch)))

end GenerativeFlow

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Finit Fterm : Measure S)

/-- **The path space is the paper's sampler** (`main.tex:163–165`), from `F_init ≠ 0`:

1. `s₁ ∼ F_init`;
2. a two-time `π`-transition identity: `P(s_{n+1} ∈ A, s_{n+2} ∈ B) = ∫_A π(x)(B) dP_{s_{n+1}}(x)`
   (the Markov property itself is the definition `pathKernel`, not this clause);
3. `τ ≥ 1`;
4. `P(τ = t, s_t ∈ A) = ∫_A stop dP(τ ≥ t, s_t ∈ ·)` for every `t = n + 1 ≥ 1`, `stop` being
   `G`-a.e. `dF_term/d(F_term + F_out)` (`stop_ae_eq`, and `pathLaw_hazard_rnDeriv` on the
   sampler's support). -/
theorem pathLaw_spec [IsFiniteMeasure Finit] (hinit : Finit ≠ 0) :
    (F.pathLaw Finit Fterm).map (fun ω => (ω 0).1) = normalize Finit ∧
    (∀ n A B, MeasurableSet A → MeasurableSet B →
      F.pathLaw Finit Fterm {ω | (ω n).1 ∈ A ∧ (ω (n + 1)).1 ∈ B}
        = ∫⁻ x in A, F.policy x B ∂((F.pathLaw Finit Fterm).map (fun ω => (ω n).1))) ∧
    (∀ ω : ℕ → S × Bool, 1 ≤ stopTime ω) ∧
    (∀ (n : ℕ) A, MeasurableSet A →
      F.pathLaw Finit Fterm {ω | stopTime ω = (n + 1 : ℕ) ∧ (ω n).1 ∈ A}
        = ∫⁻ x in A, F.stop Fterm x
            ∂(((F.pathLaw Finit Fterm).restrict {ω | ((n + 1 : ℕ) : ℕ∞) ≤ stopTime ω}).map
              (fun ω => (ω n).1))) := by
  refine ⟨F.pathLaw_map_state Finit Fterm hinit 0, fun n A B hA hB =>
    F.pathLaw_chain Finit Fterm hinit n hA hB, fun ω => le_add_self, fun n A hA => ?_⟩
  have hocc : ((F.pathLaw Finit Fterm).restrict {ω | ((n + 1 : ℕ) : ℕ∞) ≤ stopTime ω}).map
      (fun ω => (ω n).1) = F.occ Fterm (normalize Finit) n := by
    ext B hB
    have hm : Measurable fun ω : ℕ → S × Bool => (ω n).1 := measurable_fst.comp (measurable_eval n)
    rw [Measure.map_apply hm hB, Measure.restrict_apply (hm hB),
      ← (F.pathLaw_hazard Finit Fterm hinit n hA).2 B hB]
    congr 1; ext ω; simp [and_comm]
  rw [hocc]
  exact (F.pathLaw_hazard Finit Fterm hinit n hA).1

end GenerativeFlow

/-! ## The comparison with `GFNBounds`' frozen chain (template: `SamplingGeneral.chainKernel`)

`GFNBounds.Core.SamplingGeneral` models the sampler by the time-`n` marginals of a chain on
`𝒮 × Bool` frozen at stopping: from `(x, false)` to `(x, true)` with probability `stop x`, to
`(y, false)`, `y ∼ π(x)`, with probability `cont x`; `(x, true)` absorbing. Its law at time `n` is
`occ n ⊗ δ_false + stopped n ⊗ δ_true` (`chainLaw_eq`), so `P(X_n ∈ A × {true}) = stopped n A →
termLaw A` (`stopped_tendsto`). Ported verbatim; `GenerativeFlow.pathLaw_stopped_sampled` says that
the law of `s_τ` on the path space is that limit. -/

/-- `x ↦ (x, false)`. -/
def inF (x : S) : S × Bool := (x, false)

/-- `x ↦ (x, true)`. -/
def inT (x : S) : S × Bool := (x, true)

theorem measurable_inF : Measurable (inF : S → S × Bool) := measurable_id.prodMk measurable_const

theorem measurable_inT : Measurable (inT : S → S × Bool) := measurable_id.prodMk measurable_const

namespace GenerativeFlow

variable (F : GenerativeFlow S) (Fterm : Measure S)

/-- The frozen chain's transition law from `z = (x, b)` (template: `MFlow.kernelFun`). -/
noncomputable def frozenFun (z : S × Bool) : Measure (S × Bool) :=
  if z.2 then Measure.dirac (inT z.1)
  else F.stop Fterm z.1 • Measure.dirac (inT z.1) + F.cont Fterm z.1 • (F.policy z.1).map inF

theorem frozenFun_apply (z : S × Bool) {s : Set (S × Bool)} (hs : MeasurableSet s) :
    F.frozenFun Fterm z s = if z.2 then (inT ⁻¹' s).indicator 1 z.1
      else F.stop Fterm z.1 * (inT ⁻¹' s).indicator 1 z.1
        + F.cont Fterm z.1 * F.policy z.1 (inF ⁻¹' s) := by
  unfold frozenFun
  split_ifs
  · rw [Measure.dirac_apply' _ hs]; rfl
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
      Measure.map_apply measurable_inF hs, smul_eq_mul, smul_eq_mul]
    rfl

theorem measurable_frozenFun : Measurable (F.frozenFun Fterm) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [F.frozenFun_apply Fterm _ hs]
  have hi : Measurable fun z : S × Bool => (inT ⁻¹' s).indicator (1 : S → ℝ≥0∞) z.1 :=
    (measurable_one.indicator (measurable_inT hs)).comp measurable_fst
  refine Measurable.ite ?_ hi ?_
  · exact measurable_snd (measurableSet_singleton true)
  · exact (((F.measurable_stop Fterm).comp measurable_fst).mul hi).add
      (((F.measurable_cont Fterm).comp measurable_fst).mul
        ((F.policy.measurable_coe (measurable_inF hs)).comp measurable_fst))

/-- `GFNBounds`' frozen chain (template: `MFlow.chainKernel`). -/
noncomputable def chainKernel : Kernel (S × Bool) (S × Bool) :=
  ⟨F.frozenFun Fterm, F.measurable_frozenFun Fterm⟩

/-- The law of the frozen chain at time `n`, from `(s₁, false)`, `s₁ ∼ μ₀` (template:
`MFlow.chainLaw`). -/
noncomputable def chainLaw (μ₀ : Measure S) : ℕ → Measure (S × Bool)
  | 0 => μ₀.map inF
  | n + 1 => (chainLaw μ₀ n).bind (F.chainKernel Fterm)

theorem bind_split (A B : Measure S) :
    (A.map inF + B.map inT).bind (F.chainKernel Fterm)
      = (F.step Fterm A).map inF + (B + A.withDensity (F.stop Fterm)).map inT := by
  ext s hs
  have hK : Measurable fun z => F.chainKernel Fterm z s := (F.chainKernel Fterm).measurable_coe hs
  have hT' := measurable_inT hs
  rw [Measure.bind_apply hs (F.chainKernel Fterm).aemeasurable, lintegral_add_measure,
    lintegral_map hK measurable_inF, lintegral_map hK measurable_inT, Measure.add_apply,
    Measure.map_apply measurable_inF hs, Measure.map_apply measurable_inT hs, Measure.add_apply,
    F.step_apply Fterm A (measurable_inF hs), withDensity_apply _ hT']
  simp only [chainKernel, Kernel.coe_mk, F.frozenFun_apply Fterm _ hs, inF, inT,
    Bool.false_eq_true, if_false, if_true]
  have h1 : ∀ x, F.stop Fterm x * (inT ⁻¹' s).indicator 1 x
      = (inT ⁻¹' s).indicator (F.stop Fterm) x := by
    intro x
    by_cases hx : x ∈ inT ⁻¹' s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp only [h1]
  rw [lintegral_add_left ((F.measurable_stop Fterm).indicator hT'), lintegral_indicator hT',
    lintegral_indicator_one hT']
  ring

/-- **The frozen chain's law is the split of the marginals** (template: `MFlow.chainLaw_eq`). -/
theorem chainLaw_eq (μ₀ : Measure S) :
    ∀ n, F.chainLaw Fterm μ₀ n
      = (F.occ Fterm μ₀ n).map inF + (F.stopped Fterm μ₀ n).map inT
  | 0 => by simp [chainLaw, occ_zero, stopped]
  | n + 1 => by
    rw [chainLaw, chainLaw_eq μ₀ n, bind_split, occ_succ]
    simp only [stopped, Finset.sum_range_succ]

/-- `P(X_n ∈ A × {true}) = stopped n A` for the frozen chain (template:
`MFlow.stopped_eq_chainLaw`). -/
theorem stopped_eq_chainLaw (μ₀ : Measure S) (n : ℕ) {s : Set S} (hs : MeasurableSet s) :
    F.stopped Fterm μ₀ n s = F.chainLaw Fterm μ₀ n (s ×ˢ {true}) := by
  have hm : MeasurableSet (s ×ˢ ({true} : Set Bool)) := hs.prod (measurableSet_singleton _)
  rw [F.chainLaw_eq Fterm μ₀ n, Measure.add_apply, Measure.map_apply measurable_inF hm,
    Measure.map_apply measurable_inT hm]
  have e1 : inF ⁻¹' (s ×ˢ ({true} : Set Bool)) = ∅ := by ext x; simp [inF]
  have e2 : inT ⁻¹' (s ×ˢ ({true} : Set Bool)) = s := by ext x; simp [inT]
  rw [e1, e2, measure_empty, zero_add]

/-- **The path space agrees with `GFNBounds`' `chainLaw` reading**: for every measurable `A`, the
frozen chain's `P(X_n ∈ A × {true})` increases to `P(τ < ∞, s_τ ∈ A)` on the path space. -/
theorem chainLaw_tendsto_pathLaw (Finit : Measure S) [IsFiniteMeasure Finit] (hinit : Finit ≠ 0)
    {A : Set S} (hA : MeasurableSet A) :
    Tendsto (fun n => F.chainLaw Fterm (normalize Finit) n (A ×ˢ {true})) atTop
      (𝓝 (F.pathLaw Finit Fterm {ω | stopIndex ω ≠ ⊤ ∧ sampledState ω ∈ A})) := by
  rw [F.pathLaw_stopped_sampled Finit Fterm hinit hA, sampleLaw]
  simp_rw [← F.stopped_eq_chainLaw Fterm _ _ hA]
  exact F.stopped_tendsto Fterm _ hA

end GenerativeFlow

/-! ## `theo:sampling_theorem` -/

/-- **`theo:sampling_theorem`** (`main.tex:178–190`). Let `F_init`, `F_term` be finite measures with
`F_term ≠ 0` and `(π, F_out)` a generative flow. If `F_init + F_out π = F_term + F_out`, then
`F_init(𝒮) = F_term(𝒮)`, and for the sampler of `main.tex:163–165` (the path space
`GenerativeFlow.pathLaw`): `𝔼(τ) ≤ F_out(𝒮)/F_init(𝒮) + 1`, `τ < ∞` almost surely, and
`s_τ ∼ F_term`, i.e. the law of `s_τ` is `F_term/F_term(𝒮)`. -/
theorem sampling_theorem (F : GenerativeFlow S) {Finit Fterm : Measure S} [IsFiniteMeasure Finit]
    [IsFiniteMeasure Fterm] (hterm : Fterm ≠ 0) (hFM : F.IsFlowMatching Finit Fterm) :
    Finit Set.univ = Fterm Set.univ ∧
    ∫⁻ ω, (stopTime ω : ℝ≥0∞) ∂(F.pathLaw Finit Fterm) ≤ F.outflow Set.univ / Finit Set.univ + 1 ∧
    F.pathLaw Finit Fterm {ω | stopTime ω = ⊤} = 0 ∧
    (F.pathLaw Finit Fterm).map sampledState = normalize Fterm := by
  have hZ := F.finit_univ_ne_zero Finit Fterm hterm hFM
  have hinit : Finit ≠ 0 := fun h => hZ (by rw [h]; rfl)
  obtain ⟨h3, h4⟩ := F.pathLaw_sampledState Finit Fterm hinit
    (F.expectedTau_ne_top Finit Fterm hterm hFM)
  refine ⟨F.mass_eq Finit Fterm hFM, ?_, h3, ?_⟩
  · rw [F.lintegral_stopTime Finit Fterm hinit]; exact F.expectedTau_le Finit Fterm hterm hFM
  · rw [h4, F.sampleLaw_eq Finit Fterm hterm hFM]

/-! ## `theo:negative_control` and `theo:negative_control_appendix` -/

instance isFiniteMeasure_initialError (π : Kernel S S) [IsMarkovKernel π] (Fout Finit Fterm : Measure S)
    [IsFiniteMeasure Fout] [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] :
    IsFiniteMeasure (initialError π Fout Finit Fterm) := by
  unfold initialError; infer_instance

instance isFiniteMeasure_terminalError (π : Kernel S S) [IsMarkovKernel π]
    (Fout Finit Fterm : Measure S) [IsFiniteMeasure Fout] [IsFiniteMeasure Finit]
    [IsFiniteMeasure Fterm] : IsFiniteMeasure (terminalError π Fout Finit Fterm) := by
  unfold terminalError; infer_instance

instance isFiniteMeasure_virtualTerm (π : Kernel S S) [IsMarkovKernel π]
    (Fout Finit Fterm : Measure S) [IsFiniteMeasure Fout] [IsFiniteMeasure Finit]
    [IsFiniteMeasure Fterm] : IsFiniteMeasure (virtualTerm π Fout Finit Fterm) := by
  unfold virtualTerm; infer_instance

/-- **`theo:negative_control`** (`main.tex:321–328`) **and `theo:negative_control_appendix`**
(`main.tex:844–851`, proof `:852–867`): the quantitative sampling theorem. Let `(π, F_out)` be a
generative flow and `F_init ≠ 0`, `F_term` finite measures; flow matching is not assumed. For the
sampler of `main.tex:163–165` from `F_init` to `F̂_term = F_term + δF_term`:

1. `τ < ∞` almost surely, with `𝔼(τ) ≤ (F̂_term(𝒮) + F_out(𝒮))/F_init(𝒮)`, and `s_τ` has a
   probability law;
2. `F̂_term(𝒮) = F_init(𝒮) + δF_init(𝒮)` (`main.tex:854–855`);
3. `TV(s_τ ‖ F̂_term/F̂_term(𝒮)) ≤ δF_init(𝒮)/F̂_term(𝒮)`, `TV` with the `½` of `main.tex:338`;
4. setwise, `|P(s_τ ∈ A) − F̂_term(A)/F̂_term(𝒮)| ≤ δF_init(𝒮)/F̂_term(𝒮)` for every measurable `A`.
-/
theorem main_quantitative_sampling (F : GenerativeFlow S) {Finit Fterm : Measure S}
    [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm] (hinit : Finit ≠ 0) :
    F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm) {ω | stopTime ω = ⊤} = 0 ∧
    ∫⁻ ω, (stopTime ω : ℝ≥0∞) ∂(F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm))
      ≤ (virtualTerm F.policy F.outflow Finit Fterm Set.univ + F.outflow Set.univ)
        / Finit Set.univ ∧
    IsProbabilityMeasure
      ((F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm)).map sampledState) ∧
    virtualTerm F.policy F.outflow Finit Fterm Set.univ
      = Finit Set.univ + initialError F.policy F.outflow Finit Fterm Set.univ ∧
    tvDist ((F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm)).map sampledState)
        (normalize (virtualTerm F.policy F.outflow Finit Fterm))
      ≤ initialError F.policy F.outflow Finit Fterm Set.univ
        / virtualTerm F.policy F.outflow Finit Fterm Set.univ ∧
    ∀ A, MeasurableSet A →
      (F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm)).map sampledState A
        ≤ normalize (virtualTerm F.policy F.outflow Finit Fterm) A
          + initialError F.policy F.outflow Finit Fterm Set.univ
            / virtualTerm F.policy F.outflow Finit Fterm Set.univ ∧
      normalize (virtualTerm F.policy F.outflow Finit Fterm) A
        ≤ (F.pathLaw Finit (virtualTerm F.policy F.outflow Finit Fterm)).map sampledState A
          + initialError F.policy F.outflow Finit Fterm Set.univ
            / virtualTerm F.policy F.outflow Finit Fterm Set.univ := by
  set Fhat := virtualTerm F.policy F.outflow Finit Fterm with hFhat
  set δ := initialError F.policy F.outflow Finit Fterm with hδ
  have hmatch : Finit + δ + F.outflow.bind F.policy = Fhat + F.outflow :=
    isFlowMatching_virtual F.policy F.outflow Finit Fterm
  have hZ : Finit Set.univ ≠ 0 := fun h => hinit (Measure.measure_univ_eq_zero.1 h)
  have hE : F.expectedTau Finit Fhat ≠ ∞ := by
    rw [GenerativeFlow.expectedTau_eq_occupation]
    exact F.occupation_normalize_ne_top hmatch
  obtain ⟨htop, hlaw⟩ := F.pathLaw_sampledState Finit Fhat hinit hE
  have hS : F.sampleLaw Finit Fhat Set.univ = 1 := by
    rw [GenerativeFlow.sampleLaw, F.termLaw_univ Fhat _ (F.occupation_normalize_ne_top hmatch),
      normalize_univ _ hinit]
  have hmass := F.fterm_univ_eq hmatch
  have hFhat0 : Fhat ≠ 0 := by
    intro h
    have : Fhat Set.univ = 0 := by rw [h]; rfl
    rw [hmass] at this
    exact hZ (le_antisymm (this ▸ le_self_add) zero_le)
  have hTV := F.negative_control_marginal hmatch hinit
  haveI : IsProbabilityMeasure ((F.pathLaw Finit Fhat).map sampledState) := ⟨by rw [hlaw, hS]⟩
  have heq : (F.pathLaw Finit Fhat).map sampledState Set.univ = normalize Fhat Set.univ := by
    rw [measure_univ, normalize_univ _ hFhat0]
  refine ⟨htop, ?_, inferInstance, hmass, by rw [hlaw]; exact hTV, fun A _ => ⟨?_, ?_⟩⟩
  · rw [F.lintegral_stopTime Finit Fhat hinit, GenerativeFlow.expectedTau_eq_occupation, normalize,
      GenerativeFlow.occupation_smul, Measure.smul_apply, smul_eq_mul]
    have hle := Measure.le_iff'.1 (F.occupation_le Fhat (F.finit_super hmatch)) Set.univ
    calc (Finit Set.univ)⁻¹ * F.occupation Fhat Finit Set.univ
        ≤ (Finit Set.univ)⁻¹ * F.stopBase Fhat Set.univ := by gcongr
      _ = (Fhat Set.univ + F.outflow Set.univ) / Finit Set.univ := by
        rw [GenerativeFlow.stopBase, Measure.add_apply, div_eq_mul_inv, mul_comm]
  · refine (le_add_tvDist heq A).trans ?_
    rw [hlaw] at heq ⊢
    gcongr
  · have heq' : normalize Fhat Set.univ = (F.pathLaw Finit Fhat).map sampledState Set.univ :=
      heq.symm
    refine (le_add_tvDist heq' A).trans ?_
    rw [tvDist_comm]
    gcongr
    rw [hlaw]; exact hTV

/-! ## Inhabitation (`kb/0011`) -/

namespace Resample

variable (μ : Measure S) [IsProbabilityMeasure μ] (c : ℝ≥0)

/-- On any probability space: the i.i.d. resampling policy `π(x) = μ` and the outflow `c μ`
(template: `GFNBounds.Core.SamplingGeneral.Resample`). -/
noncomputable def flow : GenerativeFlow S where
  policy := Kernel.const S μ
  outflow := c • μ
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

/-- It is flow matching from `μ` to `μ`. -/
theorem isFlowMatching : (flow μ c).IsFlowMatching μ μ := by
  change μ + inflow (Kernel.const S μ) (c • μ) = μ + c • μ
  rw [inflow, Measure.bind_smul]
  have : μ.bind (Kernel.const S μ) = μ := by
    change μ.bind (fun _ => μ) = μ
    rw [Measure.bind_const, measure_univ, one_smul]
  rw [this]

/-- **`sampling_theorem` is inhabited on every probability space**, with a non-zero outflow when
`c ≠ 0`. -/
theorem sampling_theorem_inhabited :
    μ Set.univ = μ Set.univ ∧
    ∫⁻ ω, (stopTime ω : ℝ≥0∞) ∂((flow μ c).pathLaw μ μ)
      ≤ (flow μ c).outflow Set.univ / μ Set.univ + 1 ∧
    (flow μ c).pathLaw μ μ {ω | stopTime ω = ⊤} = 0 ∧
    ((flow μ c).pathLaw μ μ).map sampledState = normalize μ :=
  sampling_theorem (flow μ c) (IsProbabilityMeasure.ne_zero μ) (isFlowMatching μ c)

end Resample

/-! ## The `½` of the total variation, and sharpness (`main.tex:325`, `:338`)

On `𝒮 = Bool` with the identity policy, no outflow, `F_init = δ_true`, `F_term = δ_false`: then
`δF_init = δ_false`, `F̂_term = δ_false + δ_true`, the sampler stops at once, `s_τ = true`, and
`TV(s_τ ‖ F̂_term/2) = ½ = δF_init(𝒮)/F̂_term(𝒮)`: the bound of `theo:negative_control` is attained.
Without the `½`, `‖s_τ − F̂_term/2‖ = 1 > ½`: the theorem is false for the unhalved norm. -/

/-- `(μ − ν)(A) = μ(A)` where `ν(A) = 0`. -/
theorem sub_apply_of_null {μ ν : Measure S} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set S}
    (hA : ν A = 0) : (μ - ν) A = μ A := by
  refine le_antisymm (Measure.sub_le A) ?_
  calc μ A ≤ ((μ - ν) + ν) A := Measure.le_iff'.1 (Measure.sub_le_iff_le_add.mp le_rfl) A
    _ = (μ - ν) A := by rw [Measure.add_apply, hA, add_zero]

/-- `(μ − ν)(A) = 0` where `μ(A) = 0`. -/
theorem sub_apply_eq_zero_of_null (μ ν : Measure S) {A : Set S} (hA : μ A = 0) :
    (μ - ν) A = 0 :=
  le_antisymm ((Measure.sub_le (μ := μ) (ν := ν) A).trans hA.le) zero_le

namespace TwoPoint

/-- The identity policy on `Bool` with no outflow. -/
noncomputable def flow : GenerativeFlow Bool where
  policy := Kernel.id
  outflow := 0
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := inferInstance

theorem univ_eq : (Set.univ : Set Bool) = {true} ∪ {false} := by
  ext b; cases b <;> simp

theorem measure_univ_eq (μ : Measure Bool) : μ Set.univ = μ {true} + μ {false} := by
  rw [univ_eq, measure_union (by simp) (measurableSet_singleton _)]

theorem inflow_eq : inflow (Kernel.id : Kernel Bool Bool) 0 = 0 := by
  simp [inflow]

theorem initialError_eq :
    initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
      = Measure.dirac false - Measure.dirac true := by
  simp [initialError, inflow_eq, flow]

theorem terminalError_eq :
    terminalError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
      = Measure.dirac true - Measure.dirac false := by
  simp [terminalError, inflow_eq, flow]

theorem delta_univ :
    initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) Set.univ
      = 1 := by
  rw [initialError_eq, measure_univ_eq,
    sub_apply_eq_zero_of_null _ _ (by simp : Measure.dirac false {true} = 0),
    sub_apply_of_null (A := {false}) (by simp)]
  simp

theorem hat_true :
    virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) {true} = 1 := by
  rw [virtualTerm, terminalError_eq, Measure.add_apply, sub_apply_of_null (A := {true}) (by simp)]
  simp

theorem hat_false :
    virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) {false} = 1 := by
  rw [virtualTerm, terminalError_eq, Measure.add_apply,
    sub_apply_eq_zero_of_null _ _ (by simp : Measure.dirac true {false} = 0)]
  simp

theorem hat_univ :
    virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) Set.univ = 2 := by
  rw [measure_univ_eq, hat_true, hat_false]; norm_num

/-- The unstopped mass never reaches `false`. -/
theorem occ_false (H : Measure Bool) (n : ℕ) :
    flow.occ H (normalize (Measure.dirac true)) n {false} = 0 := by
  induction n with
  | zero => simp [GenerativeFlow.occ_zero, normalize]
  | succ n ih =>
    rw [GenerativeFlow.occ_succ, flow.step_apply H _ (measurableSet_singleton _)]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, flow.cont H x * flow.policy x {false} ∂(flow.occ H _ n)
        ≤ ∫⁻ x, flow.policy x {false} ∂(flow.occ H _ n) :=
          lintegral_mono fun x => by
            calc flow.cont H x * flow.policy x {false} ≤ 1 * flow.policy x {false} := by
                  gcongr; exact flow.cont_le_one H x
              _ = _ := one_mul _
      _ = flow.occ H _ n {false} := by
          simp only [flow, Kernel.id_apply]
          simp_rw [Measure.dirac_apply' _ (measurableSet_singleton false)]
          rw [lintegral_indicator_one (measurableSet_singleton false)]
      _ = 0 := ih

/-- **Sharpness of `theo:negative_control`, and the `½`.** For this flow the bound
`δF_init(𝒮)/F̂_term(𝒮) = ½` is attained by `TV(s_τ ‖ F̂_term/F̂_term(𝒮))`, and the unhalved norm
`‖s_τ − F̂_term/F̂_term(𝒮)‖ = 2 TV` exceeds it. -/
theorem negative_control_sharp :
    tvDist ((flow.pathLaw (Measure.dirac true)
        (virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false))).map
          sampledState)
        (normalize (virtualTerm flow.policy flow.outflow (Measure.dirac true)
          (Measure.dirac false)))
      = initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) Set.univ
        / virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
          Set.univ ∧
    ¬ tvMass ((flow.pathLaw (Measure.dirac true)
        (virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false))).map
          sampledState)
        (normalize (virtualTerm flow.policy flow.outflow (Measure.dirac true)
          (Measure.dirac false)))
      ≤ initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false) Set.univ
        / virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
          Set.univ := by
  set Fhat := virtualTerm flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
  set P := (flow.pathLaw (Measure.dirac true) Fhat).map sampledState
  obtain ⟨-, -, hP, -, hTV, -⟩ := main_quantitative_sampling flow (Finit := Measure.dirac true)
    (Fterm := Measure.dirac false) (Measure.dirac_ne_zero)
  have hδ : initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
      = Measure.dirac false - Measure.dirac true := initialError_eq
  have hmatch : Measure.dirac true
      + initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
      + flow.outflow.bind flow.policy = Fhat + flow.outflow :=
    isFlowMatching_virtual flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
  have hE : flow.expectedTau (Measure.dirac true) Fhat ≠ ∞ := by
    rw [GenerativeFlow.expectedTau_eq_occupation]
    exact flow.occupation_normalize_ne_top hmatch
  have hlaw := (flow.pathLaw_sampledState (Measure.dirac true) Fhat Measure.dirac_ne_zero hE).2
  have hPf : P {false} = 0 := by
    change (flow.pathLaw (Measure.dirac true) Fhat).map sampledState {false} = 0
    rw [hlaw, GenerativeFlow.sampleLaw, flow.termLaw_apply_tsum Fhat _ (measurableSet_singleton _)]
    simp only [ENNReal.tsum_eq_zero]
    intro n
    exact setLIntegral_measure_zero _ _ (occ_false Fhat n)
  have hPt : P {true} = 1 := by
    have h1 : P Set.univ = 1 := measure_univ
    rw [measure_univ_eq, hPf, add_zero] at h1
    exact h1
  have hR : ∀ b : Bool, normalize Fhat {b} = 2⁻¹ := by
    intro b
    rw [normalize, Measure.smul_apply, smul_eq_mul, hat_univ]
    cases b
    · rw [hat_false, mul_one]
    · rw [hat_true, mul_one]
  have hbound : initialError flow.policy flow.outflow (Measure.dirac true) (Measure.dirac false)
      Set.univ / Fhat Set.univ = 2⁻¹ := by
    rw [delta_univ, hat_univ, one_div]
  have hge : 1 ≤ tvMass P (normalize Fhat) := by
    unfold tvMass
    calc (1 : ℝ≥0∞) = (P {true} - normalize Fhat {true}) + (normalize Fhat {false} - P {false}) := by
          rw [hPt, hPf, hR, hR, ENNReal.one_sub_inv_two, tsub_zero, ENNReal.inv_two_add_inv_two]
      _ ≤ (P - normalize Fhat) Set.univ + (normalize Fhat - P) Set.univ :=
          add_le_add (tsub_le_sub_univ _ _ _) (tsub_le_sub_univ _ _ _)
  rw [hbound]
  rw [hbound] at hTV
  refine ⟨le_antisymm hTV ?_, fun h => ?_⟩
  · rw [tvDist, ← one_div]
    exact ENNReal.div_le_div_right hge 2
  · have := hge.trans h
    exact absurd this (by norm_num)

end TwoPoint

end EGF
