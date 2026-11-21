import EGF.Universality
import Mathlib.NumberTheory.Real.Irrational

/-!
# ε-universal families of generative flows, and Theorem 3.4 in its corrected form

**`def:universal_family`** — `main.tex:249`, in its corrected form of record, the ε-form over
probability measures (DEC-141 rules OQ-49, OQ-50; corrections C-18, C-19): `EGF.IsUniversalFamilyEps`.
The exact printed form stays `EGF.IsUniversalFamily` (`EGF/Defs.lean`).

**`theo:universality`** — `main.tex:277`, in its corrected form of record (DEC-141, correction
C-20): `EGF.universality`. As printed its density hypothesis is never satisfied
(`EGF.not_dense_L2_of_nonneg`), and the conclusion is ε-universality (see SCOPE).

> On a state space $(\Statespace,\lambda)$, a family of generative flow family is universal if for
> any two distributions $\mu,\nu\ll \lambda$ with bounded density there is a flow
> $(\foutstar,\ForwardPolicyStar)$ in the family that is flow matching for $\Finit=\nu$ and
> $\Fterm=\mu$. (`main.tex:249–252`)

> A parameterized family  of EGF is universal provided  that it contains some summably
> $L^2$-mixing $\ForwardPolicyStar$  and that the set of $\foutstar$ is dense in
> $L^2(\Statespace,\lambda)$. (`main.tex:277–278`)

> The following theorem implies Theorem \ref{theo:universality}. (`main.tex:774`)

## What is defined and proved

| | |
|---|---|
| `IsUniversalFamilyEps`, `IsUniversalFamily.isUniversalFamilyEps` | the corrected definition; the exact one implies it |
| `IsUniversalPolicy`, `isUniversalPolicy_of_isSummablyL2Mixing`, `isUniversalPolicy_const` | one policy `π` is ε-universal with bounded outflows `f λ` (the conclusion of `EGF.main_universality`) |
| `IsL1DenseBoundedNonneg`, `IsDenseNonnegConeL2`, `IsDenseL2` | the density hypotheses: `L¹` on bounded `g ≥ 0`; the non-negative cone of `L²`; all of `L²` (printed) |
| `isUniversalFamilyEps_of_policy`, `…_of_isDenseNonnegConeL2` | a family containing `(π, f λ)` for `f ∈ D`, `D` `L¹`-dense in bounded `g ≥ 0` (or `L²`-dense in the cone), `π` universal, is ε-universal |
| **`universality`**, `universality_of_isDenseL2` | `theo:universality` corrected: summably `L²`-mixing `π`, `D` dense in the non-negative cone of `L²(λ)` |
| `fixedPolicyFamily`, `isUniversalFamilyEps_fixedPolicyFamily` | `{π} × L²₊(λ)` is ε-universal |
| `le_eLpNorm_sub_neg_one`, **`not_dense_L2_of_nonneg`** | `−1` is at `L²` distance `≥ λ(𝒮)^{1/2}` from every `f ≥ 0`: the printed hypothesis is unsatisfiable |
| `UniversalityPrinted`, `universalityPrinted` | the printed theorem, as a `Prop`; it holds, vacuously |
| `UniversalityExactCone`, `Coin.*`, **`exact_universality_fails`** | the cone correction with the exact definition: false, on `Bool`, for a family of EGFs |
| `tvMass_le_errors_of_inflow_eq`, `Coin.allOutflows_reading_fails` | "the set of `f_out*`" read as all outflows: even the corrected theorem fails |

## Hypothesis checklist

| paper | here |
|---|---|
| a parameterized family of EGF | ⚠ weakened: any `Set (GenerativeFlow S)` |
| it contains a summably `L²`-mixing `π*` | ✓ `IsSummablyL2Mixing π lam`; `π` Markov because it is the policy of a member |
| "the set of `f_out*`", paired with `π*` | ✓ `D` with `(π, f λ) ∈ 𝓕` for `f ∈ D` (outflow `f⁺ λ`); the other reading is false (`Coin.allOutflows_reading_fails`), see SCOPE |
| dense in `L²(𝒮, λ)` | ⚠ weakened to dense in the non-negative cone (C-20; implied, `IsDenseL2.isDenseNonnegConeL2`); as printed, with `f_out* ≥ 0`, unsatisfiable (`not_dense_L2_of_nonneg`); approximants a.e.-strongly measurable (elements of `L²`) |
| `f_out* ≥ 0` | ⚠ weakened: `D` may contain signed functions; the outflow is `(ofReal ∘ f) λ` |
| `λ` finite (`main.tex:155`, `:161`) | ✓ `[IsFiniteMeasure lam]` in `universality`; none in `isUniversalFamilyEps_of_policy` |
| conclusion "universal" (Definition 3.2, exact) | ✗ false under the corrected hypotheses (`exact_universality_fails`); proved: ε-universality, `IsUniversalFamilyEps` (C-18, DEC-141) |

## SCOPE (disclosed)

Nothing is assumed beyond Mathlib. Both labels are marked in their corrected forms of record
(DEC-141; corrections C-18, C-19, C-20, adopted at graduation): `EGF.IsUniversalFamilyEps` for
`def:universal_family`, `EGF.universality` for `theo:universality`. The paper gives no proof of Theorem 3.4 beyond `main.tex:774`; the derivation
from Theorem B.1 is `isUniversalFamilyEps_of_policy` (the defect is 2-Lipschitz in the outflow, in
total variation) plus `L² ⇒ L¹` on a finite `λ`. Reading taken: "the set of `f_out*`"
is the set of outflows paired with the mixing `π*` (under either reading this is the form of
record: the other one is refuted, so DEC-141's standing ruling corrects it to this one); read as all outflows of the family, with any
policy, even the corrected theorem fails, for a family of EGFs (`Coin.allOutflows_reading_fails`).
`UniversalityPrinted` is stated for any family with outflow densities `f ≥ 0` a.e.; it is true
only because its hypotheses never hold on a finite `λ ≠ 0`. Read with a signed scalar head
(outflow `f⁺ λ`), "dense in `L²`" is satisfiable and implies the cone hypothesis
(`universality_of_isDenseL2`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace EGF

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {S : Type*} [MeasurableSpace S]

/-! ## ε-universal families (`def:universal_family`, corrected: C-18, C-19) -/

/-- **ε-universality** (`def:universal_family` in its corrected form, DEC-141: OQ-49 probability
measures, OQ-50 ε-universality): for any two probability measures `μ, ν ≪ λ` with bounded density
and every `ε > 0` there is a flow in the family from `F_init = ν` to `F_term = μ` with
`δF_init(𝒮) + δF_term(𝒮) < ε`. -/
def IsUniversalFamilyEps (lam : Measure S) (𝓕 : Set (GenerativeFlow S)) : Prop :=
  ∀ μ ν : Measure S, IsProbabilityMeasure μ → IsProbabilityMeasure ν → μ ≪ lam → ν ≪ lam →
    (∃ C : ℝ≥0, ∀ᵐ s ∂lam, μ.rnDeriv lam s ≤ C) → (∃ C : ℝ≥0, ∀ᵐ s ∂lam, ν.rnDeriv lam s ≤ C) →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ F ∈ 𝓕,
      initialError F.policy F.outflow ν μ Set.univ + terminalError F.policy F.outflow ν μ Set.univ
        < ε

/-- A flow-matching flow has zero defect. -/
theorem GenerativeFlow.IsFlowMatching.errors_eq_zero {F : GenerativeFlow S}
    {Finit Fterm : Measure S} (h : F.IsFlowMatching Finit Fterm) :
    initialError F.policy F.outflow Finit Fterm Set.univ
      + terminalError F.policy F.outflow Finit Fterm Set.univ = 0 := by
  have h' : Finit + inflow F.policy F.outflow = Fterm + F.outflow := h
  simp only [initialError, terminalError, h', Measure.sub_self, Measure.coe_zero, Pi.zero_apply,
    add_zero]

/-- The exact Definition 3.2 implies its ε-form. -/
theorem IsUniversalFamily.isUniversalFamilyEps {lam : Measure S} {𝓕 : Set (GenerativeFlow S)}
    (h : IsUniversalFamily lam 𝓕) : IsUniversalFamilyEps lam 𝓕 := by
  intro μ ν hμ hν hμl hνl hμb hνb ε hε
  obtain ⟨F, hF, hfm⟩ := h μ ν hμ hν hμl hνl hμb hνb
  exact ⟨F, hF, by rw [hfm.errors_eq_zero]; exact hε⟩

/-! ## A universal policy -/

/-- **A universal policy** on `(𝒮, λ)`: for all probability measures `F_init, F_term ≪ λ` and
every `ε > 0` there is a bounded `f_out ≥ 0` in `L²(λ)` such that the generative flow
`(π, f_out λ)` from `F_init` to `F_term` has `δF_init(𝒮) + δF_term(𝒮) < ε`. This is the
conclusion of `EGF.main_universality` (`theo:universality_true`), verbatim, for one policy. -/
def IsUniversalPolicy (lam : Measure S) (π : Kernel S S) : Prop :=
  ∀ Finit Fterm : Measure S, IsProbabilityMeasure Finit → IsProbabilityMeasure Fterm →
    Finit ≪ lam → Fterm ≪ lam → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ fout : S → ℝ, (∀ s, 0 ≤ fout s) ∧ (∃ C : ℝ, ∀ s, fout s ≤ C) ∧ MemLp fout 2 lam ∧
      initialError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        + terminalError π (lam.withDensity fun s => ENNReal.ofReal (fout s)) Finit Fterm Set.univ
        < ε

/-- **Theorem B.1 as a universal policy**: a summably `L²`-mixing Markov kernel on a finite
`(𝒮, λ)` is universal (`EGF.main_universality`). -/
theorem isUniversalPolicy_of_isSummablyL2Mixing (lam : Measure S) [IsFiniteMeasure lam]
    (π : Kernel S S) [IsMarkovKernel π] (hmix : IsSummablyL2Mixing π lam) :
    IsUniversalPolicy lam π := by
  intro Finit Fterm h1 h2 hinit hterm ε hε
  haveI := h1
  haveI := h2
  exact main_universality lam π hmix Finit Fterm hinit hterm hε

/-- Inhabitation: on a probability space the resampling kernel `π(x) = λ` is universal. -/
theorem isUniversalPolicy_const (lam : Measure S) [IsProbabilityMeasure lam] :
    IsUniversalPolicy lam (Kernel.const S lam) :=
  isUniversalPolicy_of_isSummablyL2Mixing lam _ (isSummablyL2Mixing_const lam)

/-! ## Density hypotheses -/

/-- Every bounded measurable `g ≥ 0` is an `L¹(λ)`-limit of a.e.-measurable elements of `D`. -/
def IsL1DenseBoundedNonneg (lam : Measure S) (D : Set (S → ℝ)) : Prop :=
  ∀ g : S → ℝ, Measurable g → (∀ s, 0 ≤ g s) → (∃ C : ℝ, ∀ s, g s ≤ C) →
    ∀ η : ℝ≥0∞, 0 < η → ∃ f ∈ D, AEMeasurable f lam ∧ eLpNorm (f - g) 1 lam < η

/-- **`D` is dense in the non-negative cone of `L²(λ)`** (C-20, DEC-141's reading of OQ-50): every
`g ∈ L²(λ)` with `g ≥ 0` is an `L²(λ)`-limit of a.e.-strongly measurable elements of `D`. -/
def IsDenseNonnegConeL2 (lam : Measure S) (D : Set (S → ℝ)) : Prop :=
  ∀ g : S → ℝ, MemLp g 2 lam → (∀ s, 0 ≤ g s) →
    ∀ η : ℝ≥0∞, 0 < η → ∃ f ∈ D, AEStronglyMeasurable f lam ∧ eLpNorm (f - g) 2 lam < η

/-- **`D` is dense in `L²(λ)`**, the hypothesis of `theo:universality` as printed
(`main.tex:277`). -/
def IsDenseL2 (lam : Measure S) (D : Set (S → ℝ)) : Prop :=
  ∀ g : S → ℝ, MemLp g 2 lam →
    ∀ η : ℝ≥0∞, 0 < η → ∃ f ∈ D, AEStronglyMeasurable f lam ∧ eLpNorm (f - g) 2 lam < η

theorem IsDenseL2.isDenseNonnegConeL2 {lam : Measure S} {D : Set (S → ℝ)} (h : IsDenseL2 lam D) :
    IsDenseNonnegConeL2 lam D :=
  fun g hg _ => h g hg

/-- On a finite `λ`, `L²` density in the non-negative cone gives `L¹` density on bounded `g ≥ 0`. -/
theorem IsDenseNonnegConeL2.isL1DenseBoundedNonneg {lam : Measure S} [IsFiniteMeasure lam]
    {D : Set (S → ℝ)} (h : IsDenseNonnegConeL2 lam D) : IsL1DenseBoundedNonneg lam D := by
  intro g hgm hgnn ⟨C, hC⟩ η hη
  have hgL : MemLp g 2 lam := MemLp.of_bound hgm.aestronglyMeasurable C
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs, abs_of_nonneg (hgnn s)]; exact hC s)
  set c : ℝ≥0∞ := lam Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) with hc
  have hctop : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hc1top : c + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hctop, ENNReal.one_ne_top⟩
  have hc10 : c + 1 ≠ 0 := by simp
  obtain ⟨f, hfD, hfm, hfg⟩ := h g hgL hgnn (η / (c + 1)) (ENNReal.div_pos hη.ne' hc1top)
  refine ⟨f, hfD, hfm.aemeasurable, ?_⟩
  calc eLpNorm (f - g) 1 lam ≤ eLpNorm (f - g) 2 lam * c :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (hfm.sub hgm.aestronglyMeasurable)
    _ ≤ eLpNorm (f - g) 2 lam * (c + 1) := by gcongr; exact le_self_add
    _ < η := (ENNReal.lt_div_iff_mul_lt (Or.inl hc10) (Or.inl hc1top)).mp hfg

/-! ## The family lemma and Theorem 3.4 corrected -/

/-- **A family containing a universal policy with `L¹`-dense outflows is ε-universal.** If `𝓕`
contains `(π, f⁺ λ)` for every `f` of a set `D` which approximates every bounded measurable
`g ≥ 0` in `L¹(λ)`, and `π` is universal, then `𝓕` is ε-universal. The defect is 2-Lipschitz in
the outflow for the total variation (`EGF.tvMass_bind_le`, `EGF.tvMass_triangle`). -/
theorem isUniversalFamilyEps_of_policy (lam : Measure S) (𝓕 : Set (GenerativeFlow S))
    (π : Kernel S S) (hπ : IsUniversalPolicy lam π) (D : Set (S → ℝ))
    (hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s))
    (hdense : IsL1DenseBoundedNonneg lam D) : IsUniversalFamilyEps lam 𝓕 := by
  intro μ ν hμ hν hμl hνl _ _ ε hε
  haveI := hμ
  haveI := hν
  set ε' := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'top : ε' ≠ ∞ := ((min_le_right ε 1).trans_lt ENNReal.one_lt_top).ne
  set δ := ε' / 3 with hδ
  have hδpos : 0 < δ := ENNReal.div_pos hε'pos.ne' (by norm_num)
  have hδtop : δ ≠ ∞ := ENNReal.div_ne_top hε'top (by norm_num)
  have h3δ : δ + (δ + δ) ≤ ε := by
    have : δ + (δ + δ) = 3 * (ε' / 3) := by rw [hδ]; ring
    rw [this]; exact ENNReal.mul_div_le.trans (min_le_left _ _)
  -- the outflow of the universal policy, made measurable
  obtain ⟨fout, hfnn, ⟨C, hfC⟩, hfL, hdef⟩ := hπ ν μ hν hμ hνl hμl δ hδpos
  set f₀ := hfL.1.aemeasurable.mk fout with hf₀
  have hf₀m : Measurable f₀ := hfL.1.aemeasurable.measurable_mk
  have hf₀e : fout =ᵐ[lam] f₀ := hfL.1.aemeasurable.ae_eq_mk
  set g : S → ℝ := fun s => max 0 (min (f₀ s) C) with hgdef
  have hgm : Measurable g := measurable_const.max (hf₀m.min measurable_const)
  have hge : fout =ᵐ[lam] g := hf₀e.mono fun s hs => by
    simp only [hgdef, ← hs, min_eq_left (hfC s), max_eq_right (hfnn s)]
  -- an element of `D` close to it in `L¹`, and its flow in the family
  obtain ⟨f, hfD, hfm, hfg⟩ := hdense g hgm (fun s => le_max_left _ _)
    ⟨max 0 C, fun s => max_le_max le_rfl (min_le_right _ _)⟩ δ hδpos
  obtain ⟨F, hF𝓕, hFπ, hFout⟩ := hD f hfD
  refine ⟨F, hF𝓕, ?_⟩
  haveI : IsMarkovKernel π := hFπ ▸ F.isMarkovKernel_policy
  set Ff := lam.withDensity fun s => ENNReal.ofReal (f s) with hFf
  set Fg := lam.withDensity fun s => ENNReal.ofReal (g s) with hFg
  haveI : IsFiniteMeasure Ff := hFout ▸ F.isFiniteMeasure_outflow
  set f₁ := hfm.mk f with hf₁
  have hf₁m : Measurable f₁ := hfm.measurable_mk
  have hf₁e : f =ᵐ[lam] f₁ := hfm.ae_eq_mk
  have hFf₁ : Ff = lam.withDensity fun s => ENNReal.ofReal (f₁ s) :=
    withDensity_congr_ae (hf₁e.mono fun s hs => by simp only [hs])
  have hL1 : ∫⁻ s, ‖f₁ s - g s‖ₑ ∂lam = eLpNorm (f - g) 1 lam := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr_ae (hf₁e.mono fun s hs => by simp [hs])
  have hpt : ∀ a b : ℝ, (ENNReal.ofReal a - ENNReal.ofReal b)
      + (ENNReal.ofReal b - ENNReal.ofReal a) ≤ ‖a - b‖ₑ := by
    intro a b
    rw [tsub_add_tsub_eq_ofReal_abs ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (abs_max_sub_max_le_abs a b 0)
  -- `Fg` is finite: its mass is at most that of `Ff` plus the `L¹` distance
  haveI : IsFiniteMeasure Fg := by
    refine isFiniteMeasure_withDensity ?_
    have hle : ∀ s, ENNReal.ofReal (g s) ≤ ENNReal.ofReal (f₁ s) + ‖f₁ s - g s‖ₑ := by
      intro s
      rw [Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal (g s) ≤ ENNReal.ofReal (f₁ s + |f₁ s - g s|) :=
            ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (f₁ s - g s)])
        _ ≤ _ := ENNReal.ofReal_add_le
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left hf₁m.ennreal_ofReal, hL1]
    have hfin : (lam.withDensity fun s => ENNReal.ofReal (f₁ s)) Set.univ ≠ ∞ := by
      rw [← hFf₁]; exact measure_ne_top _ _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hfin
    exact ENNReal.add_ne_top.2 ⟨hfin, (hfg.trans (lt_top_iff_ne_top.2 hδtop)).ne⟩
  -- the outflow moves by at most the `L¹` distance in total variation
  have htv : tvMass Ff Fg < δ := by
    rw [hFf₁]
    refine (tvMass_withDensity_le lam hf₁m.ennreal_ofReal hgm.ennreal_ofReal).trans_lt ?_
    calc ∫⁻ s, ((ENNReal.ofReal (f₁ s) - ENNReal.ofReal (g s))
          + (ENNReal.ofReal (g s) - ENNReal.ofReal (f₁ s))) ∂lam
        ≤ ∫⁻ s, ‖f₁ s - g s‖ₑ ∂lam := lintegral_mono fun s => hpt _ _
      _ < δ := hL1 ▸ hfg
  have hdef' : tvMass (ν + inflow π Fg) (μ + Fg) < δ := by
    have hFg_eq : (lam.withDensity fun s => ENNReal.ofReal (fout s)) = Fg :=
      withDensity_congr_ae (hge.mono fun s hs => by simp only [hs])
    rw [← errors_eq_tvMass, ← hFg_eq]; exact hdef
  rw [hFπ, hFout, errors_eq_tvMass]
  have e1 : tvMass (ν + inflow π Ff) (ν + inflow π Fg) < δ :=
    ((tvMass_add_left_le _ _ _).trans (tvMass_bind_le π _ _)).trans_lt htv
  have e3 : tvMass (μ + Fg) (μ + Ff) < δ :=
    (tvMass_add_left_le _ _ _).trans_lt (by rw [tvMass_comm]; exact htv)
  calc tvMass (ν + inflow π Ff) (μ + Ff)
      ≤ tvMass (ν + inflow π Ff) (ν + inflow π Fg)
        + (tvMass (ν + inflow π Fg) (μ + Fg) + tvMass (μ + Fg) (μ + Ff)) :=
        (tvMass_triangle _ (ν + inflow π Fg) _).trans
          (add_le_add le_rfl (tvMass_triangle _ (μ + Fg) _))
    _ < δ + (δ + δ) := ENNReal.add_lt_add e1 (ENNReal.add_lt_add hdef' e3)
    _ ≤ ε := h3δ

/-- **The family lemma in `L²` form**: on a finite `λ`, a family containing `(π, f⁺ λ)` for a
universal `π` and every `f` of a set `D` dense in the non-negative cone of `L²(λ)` is
ε-universal. Any proof of `IsUniversalPolicy` plugs in here; `universality` is the summably
mixing case. -/
theorem isUniversalFamilyEps_of_policy_of_isDenseNonnegConeL2 (lam : Measure S)
    [IsFiniteMeasure lam] (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S)
    (hπ : IsUniversalPolicy lam π) (D : Set (S → ℝ))
    (hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s))
    (hdense : IsDenseNonnegConeL2 lam D) : IsUniversalFamilyEps lam 𝓕 :=
  isUniversalFamilyEps_of_policy lam 𝓕 π hπ D hD hdense.isL1DenseBoundedNonneg

/-- **Theorem 3.4 (`theo:universality`) in its corrected form** (C-20, with the ε-universality of
C-18): on a finite `(𝒮, λ)`, a family of generative flows that contains `(π, f⁺ λ)` for a summably
`L²`-mixing `π` and every `f` of a set `D` dense in the non-negative cone of `L²(λ)` is
ε-universal. -/
theorem universality (lam : Measure S) [IsFiniteMeasure lam] (𝓕 : Set (GenerativeFlow S))
    (π : Kernel S S) (hmix : IsSummablyL2Mixing π lam) (D : Set (S → ℝ))
    (hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s))
    (hdense : IsDenseNonnegConeL2 lam D) : IsUniversalFamilyEps lam 𝓕 := by
  obtain ⟨f, hfD, -, -⟩ := hdense 0 MemLp.zero (fun _ => le_rfl) 1 one_pos
  obtain ⟨F, -, hFπ, -⟩ := hD f hfD
  haveI : IsMarkovKernel π := hFπ ▸ F.isMarkovKernel_policy
  exact isUniversalFamilyEps_of_policy_of_isDenseNonnegConeL2 lam 𝓕 π
    (isUniversalPolicy_of_isSummablyL2Mixing lam π hmix) D hD hdense

/-- **The printed density hypothesis, for a signed scalar head** (outflow `f⁺ λ`): density in
`L²(λ)` implies density in the non-negative cone, so `universality` covers it. -/
theorem universality_of_isDenseL2 (lam : Measure S) [IsFiniteMeasure lam]
    (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S) (hmix : IsSummablyL2Mixing π lam)
    (D : Set (S → ℝ))
    (hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s))
    (hdense : IsDenseL2 lam D) : IsUniversalFamilyEps lam 𝓕 :=
  universality lam 𝓕 π hmix D hD hdense.isDenseNonnegConeL2

/-- **The fixed-policy family** `{π} × L²₊(λ)`: the flows `(π, f λ)`, `f ≥ 0` in `L²(λ)`.
Adapted from `GFNBounds.Core.Family.fixedPolicyFamily`
(`lean/GFNBounds/Core/FamilyUniversality.lean:515`), over bundled flows. -/
def fixedPolicyFamily (lam : Measure S) (π : Kernel S S) : Set (GenerativeFlow S) :=
  {F | F.policy = π ∧ ∃ f : S → ℝ, MemLp f 2 lam ∧ (∀ s, 0 ≤ f s) ∧
    F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s)}

/-- The fixed-policy family of a summably `L²`-mixing Markov kernel is ε-universal. -/
theorem isUniversalFamilyEps_fixedPolicyFamily (lam : Measure S) [IsFiniteMeasure lam]
    (π : Kernel S S) [IsMarkovKernel π] (hmix : IsSummablyL2Mixing π lam) :
    IsUniversalFamilyEps lam (fixedPolicyFamily lam π) := by
  refine universality lam _ π hmix {f | MemLp f 2 lam ∧ ∀ s, 0 ≤ f s} (fun f hf => ?_)
    (fun g hg hgnn η hη => ⟨g, ⟨hg, hgnn⟩, hg.1, by simpa using hη⟩)
  haveI : IsFiniteMeasure (lam.withDensity fun s => ENNReal.ofReal (f s)) :=
    isFiniteMeasure_withDensity_ofReal (hf.1.integrable one_le_two).hasFiniteIntegral
  let F : GenerativeFlow S :=
    ⟨π, lam.withDensity (fun s => ENNReal.ofReal (f s)), inferInstance, inferInstance⟩
  exact ⟨F, ⟨rfl, f, hf.1, hf.2, rfl⟩, rfl, rfl⟩

/-- **An outflow fixed by the policy does not reduce the defect**: if `F_out π = F_out` then
`δF_init(𝒮) + δF_term(𝒮) ≥ ‖F_init − F_term‖_TV`. -/
theorem tvMass_le_errors_of_inflow_eq (π : Kernel S S) (Fout Finit Fterm : Measure S)
    [IsFiniteMeasure Fout] [IsFiniteMeasure Finit] [IsFiniteMeasure Fterm]
    (h : inflow π Fout = Fout) :
    tvMass Finit Fterm
      ≤ initialError π Fout Finit Fterm Set.univ + terminalError π Fout Finit Fterm Set.univ := by
  rw [errors_eq_tvMass, h]; exact tvMass_le_add_right _ _ _

/-! ## The printed hypothesis is never satisfied (C-20) -/

/-- The constant `−1` is at `L²(λ)` distance at least `λ(𝒮)^{1/2}` from every a.e.-non-negative
function (no measurability needed). -/
theorem le_eLpNorm_sub_neg_one (lam : Measure S) (hlam : lam ≠ 0) {f : S → ℝ}
    (hf : 0 ≤ᵐ[lam] f) :
    lam Set.univ ^ (1 / 2 : ℝ) ≤ eLpNorm (f - fun _ => (-1 : ℝ)) 2 lam := by
  have h1 : eLpNorm (fun _ : S => (1 : ℝ)) 2 lam = lam Set.univ ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_const _ (by norm_num) hlam]; simp
  rw [← h1]
  refine eLpNorm_mono_ae (hf.mono fun s hs => ?_)
  simp only [Pi.zero_apply] at hs
  simp only [Pi.sub_apply, norm_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **The printed hypothesis of `theo:universality` is unsatisfiable** (C-20): on a finite
`λ ≠ 0`, no set of a.e.-non-negative functions is dense in `L²(λ)`. -/
theorem not_dense_L2_of_nonneg (lam : Measure S) [IsFiniteMeasure lam] (hlam : lam ≠ 0)
    (D : Set (S → ℝ)) (hD : ∀ f ∈ D, 0 ≤ᵐ[lam] f) : ¬ IsDenseL2 lam D := by
  intro h
  have hpos : 0 < lam Set.univ ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_pos (Measure.measure_univ_pos.2 hlam) (measure_ne_top _ _)
  obtain ⟨f, hfD, -, hlt⟩ := h (fun _ => -1) (memLp_const _) _ hpos
  exact (le_eLpNorm_sub_neg_one lam hlam (hD f hfD)).not_gt hlt

/-- **`theo:universality` as printed** (`main.tex:277`), for any family of generative flows: a
summably `L²`-mixing `π` and outflow densities `f ≥ 0` (the "set of `f_out*`", paired with `π`)
dense in `L²(λ)` make the family universal in the exact sense of Definition 3.2. -/
def UniversalityPrinted (lam : Measure S) : Prop :=
  ∀ (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S) (D : Set (S → ℝ)),
    IsSummablyL2Mixing π lam →
    (∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s)) →
    (∀ f ∈ D, 0 ≤ᵐ[lam] f) → IsDenseL2 lam D → IsUniversalFamily lam 𝓕

/-- **The printed theorem holds, vacuously**: on a finite `λ ≠ 0` its density hypothesis never
holds (`not_dense_L2_of_nonneg`), and on `λ = 0` no probability measure is `≪ λ`. -/
theorem universalityPrinted (lam : Measure S) [IsFiniteMeasure lam] : UniversalityPrinted lam := by
  intro 𝓕 π D _ _ hnn hdense
  by_cases hlam : lam = 0
  · intro μ ν hμ _ hμl _ _ _
    subst hlam
    exact absurd (Measure.absolutelyContinuous_zero_iff.1 hμl) (IsProbabilityMeasure.ne_zero μ)
  · exact absurd hdense (not_dense_L2_of_nonneg lam hlam D hnn)

/-- `theo:universality` with the cone correction (C-20) but the exact Definition 3.2: false
(`exact_universality_fails`). -/
def UniversalityExactCone (lam : Measure S) : Prop :=
  ∀ (𝓕 : Set (GenerativeFlow S)) (π : Kernel S S) (D : Set (S → ℝ)),
    IsSummablyL2Mixing π lam →
    (∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
      F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s)) →
    IsDenseNonnegConeL2 lam D → IsUniversalFamily lam 𝓕

/-! ## The exact form fails: a family of EGFs on `Bool` (C-18) -/

namespace Coin

/-- The uniform probability on `Bool`. -/
noncomputable def lam : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

theorem lam_singleton (b : Bool) : lam {b} = 2⁻¹ := by
  cases b <;> simp [lam]

instance : IsProbabilityMeasure lam := by
  constructor
  simp only [lam, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The resampling kernel `π(s) = λ`, which is `½ δ_s + ½ δ_{¬s}`. -/
noncomputable def pol : Kernel Bool Bool := Kernel.const Bool lam

instance : IsMarkovKernel pol := by unfold pol; infer_instance

/-- Non-negative outflow densities with rational values. -/
def D : Set (Bool → ℝ) := {f | ∀ b, 0 ≤ f b ∧ ∃ q : ℚ, f b = q}

theorem isFiniteMeasure_lam_withDensity (f : Bool → ℝ) :
    IsFiniteMeasure (lam.withDensity fun s => ENNReal.ofReal (f s)) :=
  isFiniteMeasure_withDensity_ofReal Integrable.of_finite.hasFiniteIntegral

/-- The generative flow `(π, f⁺ λ)`. -/
noncomputable def flow (f : Bool → ℝ) : GenerativeFlow Bool where
  policy := pol
  outflow := lam.withDensity fun s => ENNReal.ofReal (f s)
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := isFiniteMeasure_lam_withDensity f

/-- The family `{(π, f λ) : f ∈ D}`. -/
def family : Set (GenerativeFlow Bool) := flow '' D

theorem mem_family (f : Bool → ℝ) (hf : f ∈ D) : ∃ F ∈ family, F.policy = pol ∧
    F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s) :=
  ⟨flow f, ⟨f, hf, rfl⟩, rfl, rfl⟩

/-- `D` is dense in the non-negative cone of `L²(λ)`. -/
theorem isDenseNonnegConeL2_D : IsDenseNonnegConeL2 lam D := by
  intro g _ hg η hη
  obtain ⟨r, -, h0r, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hr : 0 < r := ENNReal.ofReal_pos.1 h0r
  choose q hq using fun b => exists_rat_btwn (show g b < g b + r by linarith)
  refine ⟨fun b => (q b : ℝ), fun b => ⟨(hg b).trans (hq b).1.le, q b, rfl⟩,
    Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  calc eLpNorm ((fun b => (q b : ℝ)) - g) 2 lam
      ≤ lam Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal r :=
        eLpNorm_le_of_ae_bound (ae_of_all _ fun b => by
          rw [Pi.sub_apply, Real.norm_eq_abs, abs_of_pos (by linarith [(hq b).1])]
          linarith [(hq b).2])
    _ = ENNReal.ofReal r := by rw [measure_univ, ENNReal.one_rpow, one_mul]
    _ < η := hrη

/-- A probability measure with an irrational mass at `true`: `ν{true} = √2 / 2`. -/
noncomputable def nuIrr : Measure Bool :=
  lam.withDensity fun b =>
    if b then ENNReal.ofReal (Real.sqrt 2) else ENNReal.ofReal (2 - Real.sqrt 2)

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

instance : IsProbabilityMeasure nuIrr := by
  constructor
  rw [nuIrr, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_fintype,
    Fintype.sum_bool, lam_singleton, lam_singleton]
  simp only [if_true, Bool.false_eq_true, if_false]
  have h2 : Real.sqrt 2 + (2 - Real.sqrt 2) = 2 := by ring
  rw [← add_mul, ← ENNReal.ofReal_add (Real.sqrt_nonneg 2) (by linarith [sqrt_two_le_two]), h2,
    ENNReal.ofReal_ofNat, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **The family is not universal in the exact sense**: no flow of the family is flow matching
from `F_init = ν` (`ν{true} = √2/2`) to `F_term = λ`; flow matching would force
`f(true) − f(false) = 2√2 − 2`, irrational. -/
theorem not_isUniversalFamily : ¬ IsUniversalFamily lam family := by
  intro h
  set dens : Bool → ℝ≥0∞ := fun b =>
    if b then ENNReal.ofReal (Real.sqrt 2) else ENNReal.ofReal (2 - Real.sqrt 2) with hdens
  have hνac : nuIrr ≪ lam := withDensity_absolutelyContinuous _ _
  have hμb : ∃ C : ℝ≥0, ∀ᵐ s ∂lam, lam.rnDeriv lam s ≤ C :=
    ⟨1, (Measure.rnDeriv_self lam).mono fun s hs => by simp [hs]⟩
  have hνb : ∃ C : ℝ≥0, ∀ᵐ s ∂lam, nuIrr.rnDeriv lam s ≤ C := by
    refine ⟨2, (Measure.rnDeriv_withDensity lam (Measurable.of_discrete (f := dens))).mono
      fun s hs => ?_⟩
    change (lam.withDensity dens).rnDeriv lam s ≤ _
    rw [hs]
    have h2 : (((2 : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2]
    cases s
    · exact ENNReal.ofReal_le_ofReal (by linarith [Real.sqrt_nonneg 2])
    · exact ENNReal.ofReal_le_ofReal sqrt_two_le_two
  obtain ⟨F, ⟨f, hfD, rfl⟩, hfm⟩ :=
    h lam nuIrr inferInstance inferInstance Measure.AbsolutelyContinuous.rfl hνac hμb hνb
  set Fout := lam.withDensity fun s => ENNReal.ofReal (f s) with hFout
  have hfm' : nuIrr + inflow pol Fout = lam + Fout := hfm
  have hin : inflow pol Fout = Fout Set.univ • lam := by
    change Fout.bind (fun _ => lam) = _
    exact Measure.bind_const
  have hsing : ∀ (d : Bool → ℝ≥0∞) (b : Bool), (lam.withDensity d) {b} = d b * 2⁻¹ := by
    intro d b
    rw [withDensity_apply _ (measurableSet_singleton b), lintegral_singleton, lam_singleton]
  have huniv : Fout Set.univ = ENNReal.ofReal (f true) * 2⁻¹ + ENNReal.ofReal (f false) * 2⁻¹ := by
    rw [hFout, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_fintype,
      Fintype.sum_bool, lam_singleton, lam_singleton]
  have h1 := congrArg (fun m : Measure Bool => m {true}) hfm'
  simp only [Measure.add_apply, hin, Measure.smul_apply, smul_eq_mul, lam_singleton] at h1
  rw [show nuIrr = lam.withDensity dens from rfl, hsing, hFout, hsing, huniv] at h1
  simp only [hdens, if_true] at h1
  have h2 := congrArg ENNReal.toReal h1
  have ha := (hfD true).1
  have hb := (hfD false).1
  simp only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg 2),
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ne_eq, ENNReal.mul_eq_top, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, ENNReal.inv_eq_top,
    OfNat.ofNat_ne_zero, false_and, and_false, or_self, not_false_eq_true, ENNReal.inv_eq_zero,
    ENNReal.ofNat_ne_top] at h2
  obtain ⟨qa, hqa⟩ := (hfD true).2
  obtain ⟨qb, hqb⟩ := (hfD false).2
  exact irrational_sqrt_two ⟨(2 + qa - qb) / 2, by push_cast; rw [← hqa, ← hqb]; linarith⟩

/-- The family is ε-universal (`EGF.universality`, with `EGF.isSummablyL2Mixing_const`). -/
theorem isUniversalFamilyEps_family : IsUniversalFamilyEps lam family :=
  universality lam family pol (isSummablyL2Mixing_const lam) D mem_family isDenseNonnegConeL2_D

/-- The negation of `Bool`, as a homeomorphism of the discrete space. -/
def notHomeo : Bool ≃ₜ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The two moves `id` and `not`. -/
def moves : Fin 2 → Bool ≃ₜ Bool := fun i => if i = 0 then Homeomorph.refl Bool else notHomeo

/-- The moves `id`, `not` are topologically ergodic on the discrete `Bool`. -/
theorem isTopologicallyErgodic_moves : IsTopologicallyErgodic fun i => (moves i : Bool → Bool) := by
  intro x y U hU
  have hy : y ∈ U := mem_of_mem_nhds hU
  by_cases hxy : x = y
  · exact ⟨[], by simpa [hxy] using hy⟩
  · refine ⟨[1], ?_⟩
    have : (moves 1) x = y := by cases x <;> cases y <;> simp_all [moves, notHomeo]
    simpa [this] using hy

/-- The resampling kernel is the EGF policy `π(s) = ½ δ_{id s} + ½ δ_{¬s}`. -/
theorem isEGFPolicy_pol : IsEGFPolicy pol (fun i => moves i) (fun _ _ => 1 / 2) where
  measurable_map := fun _ => Measurable.of_discrete
  measurable_weight := fun _ => measurable_const
  weight_nonneg := fun _ _ => by norm_num
  weight_sum := fun _ => by rw [Fin.sum_univ_two]; norm_num
  apply_eq := fun s => by
    have h2 : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [Fin.sum_univ_two, h2]
    change lam = _
    cases s <;> simp [lam, moves, notHomeo, smul_add, add_comm]

/-- **Every flow of the family is an EGF** (`def:egf`). -/
theorem isEGF_flow (f : Bool → ℝ) : IsEGF (flow f) moves (fun _ _ => 1 / 2) :=
  ⟨isEGFPolicy_pol, isTopologicallyErgodic_moves⟩

theorem isEGF_of_mem_family {F : GenerativeFlow Bool} (hF : F ∈ family) :
    ∃ (p : ℕ) (Φ : Fin p → Bool ≃ₜ Bool) (α : Fin p → Bool → ℝ), IsEGF F Φ α := by
  obtain ⟨f, -, rfl⟩ := hF
  exact ⟨2, moves, _, isEGF_flow f⟩

/-! ### "The set of `f_out*`" read as all outflows of the family: the corrected theorem fails -/

/-- The flow `(id, f⁺ λ)`. It is an EGF with the moves `id`, `not` and `α = (1, 0)`:
`def:egf` asks nothing of `α`. -/
noncomputable def flowId (f : Bool → ℝ) : GenerativeFlow Bool where
  policy := Kernel.id
  outflow := lam.withDensity fun s => ENNReal.ofReal (f s)
  isMarkovKernel_policy := inferInstance
  isFiniteMeasure_outflow := isFiniteMeasure_lam_withDensity f

/-- The flow `(π, λ)`. -/
noncomputable def flowLam : GenerativeFlow Bool := ⟨pol, lam, inferInstance, inferInstance⟩

/-- The family `{(π, λ)} ∪ {(id, f λ) : f ∈ D}`: it contains the mixing `π`, and its outflows are
dense in the non-negative cone, but the mixing `π` carries the single outflow `λ`. -/
def familyAll : Set (GenerativeFlow Bool) := insert flowLam (flowId '' D)

theorem isEGF_of_mem_familyAll {F : GenerativeFlow Bool} (hF : F ∈ familyAll) :
    ∃ (p : ℕ) (Φ : Fin p → Bool ≃ₜ Bool) (α : Fin p → Bool → ℝ), IsEGF F Φ α := by
  rcases hF with rfl | ⟨f, -, rfl⟩
  · exact ⟨2, moves, _, isEGFPolicy_pol, isTopologicallyErgodic_moves⟩
  · refine ⟨2, moves, fun i _ => if i = 0 then 1 else 0, ⟨?_, ?_, ?_, ?_, ?_⟩,
      isTopologicallyErgodic_moves⟩
    · exact fun _ => Measurable.of_discrete
    · exact fun _ => measurable_const
    · intro i s; split_ifs <;> norm_num
    · intro s; simp
    · intro s
      change Kernel.id s = _
      rw [Kernel.id_apply, Fin.sum_univ_two]
      simp [moves]

theorem inflow_eq_outflow_of_mem_familyAll {F : GenerativeFlow Bool} (hF : F ∈ familyAll) :
    inflow F.policy F.outflow = F.outflow := by
  rcases hF with rfl | ⟨f, -, rfl⟩
  · change lam.bind (fun _ => lam) = lam
    rw [Measure.bind_const, measure_univ, one_smul]
  · have h : (⇑(Kernel.id : Kernel Bool Bool)) = Measure.dirac := funext Kernel.id_apply
    change (lam.withDensity fun s => ENNReal.ofReal (f s)).bind Kernel.id = _
    rw [h, Measure.bind_dirac]
    rfl

/-- The two point masses, as measures with densities `2·𝟙_{true}` and `2·𝟙_{false}`. -/
noncomputable def atTrue : Measure Bool := lam.withDensity fun b => if b then 2 else 0

noncomputable def atFalse : Measure Bool := lam.withDensity fun b => if b then 0 else 2

theorem lam_withDensity_singleton (d : Bool → ℝ≥0∞) (b : Bool) :
    (lam.withDensity d) {b} = d b * 2⁻¹ := by
  rw [withDensity_apply _ (measurableSet_singleton b), lintegral_singleton, lam_singleton]

theorem lam_withDensity_univ (d : Bool → ℝ≥0∞) :
    (lam.withDensity d) Set.univ = d true * 2⁻¹ + d false * 2⁻¹ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_fintype,
    Fintype.sum_bool, lam_singleton, lam_singleton]

instance : IsProbabilityMeasure atTrue :=
  ⟨by rw [atTrue, lam_withDensity_univ]; simp [ENNReal.mul_inv_cancel]⟩

instance : IsProbabilityMeasure atFalse :=
  ⟨by rw [atFalse, lam_withDensity_univ]; simp [ENNReal.mul_inv_cancel]⟩

theorem bounded_rnDeriv_two (d : Bool → ℝ≥0∞) (hd : ∀ b, d b ≤ 2) :
    ∃ C : ℝ≥0, ∀ᵐ s ∂lam, (lam.withDensity d).rnDeriv lam s ≤ C :=
  ⟨2, (Measure.rnDeriv_withDensity lam (Measurable.of_discrete (f := d))).mono fun s hs => by
    rw [hs]; simpa using hd s⟩

theorem one_le_tvMass : 1 ≤ tvMass atTrue atFalse := by
  have h : atTrue ≤ (atTrue - atFalse) + atFalse := Measure.sub_le_iff_le_add.mp le_rfl
  have h1 := h {true}
  rw [Measure.add_apply] at h1
  have hT : atTrue {true} = 1 := by
    rw [atTrue, lam_withDensity_singleton]; simp [ENNReal.mul_inv_cancel]
  have hF : atFalse {true} = 0 := by
    rw [atFalse, lam_withDensity_singleton]; simp
  calc (1 : ℝ≥0∞) = atTrue {true} := hT.symm
    _ ≤ (atTrue - atFalse) {true} + atFalse {true} := h1
    _ = (atTrue - atFalse) {true} := by rw [hF, add_zero]
    _ ≤ (atTrue - atFalse) Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ tvMass atTrue atFalse := le_self_add

/-- **Under the reading "all outflows of the family", Theorem 3.4 fails even corrected**: the
family of EGFs `familyAll` contains the summably `L²`-mixing `π`, the set of all its outflow
densities is dense in the non-negative cone of `L²(λ)`, and it is not ε-universal: every flow of
it has `F_out π = F_out`, so its defect from `δ_true` to `δ_false` is `TV(δ_true, δ_false) = 2`;
the proof needs only that it is at least `1`, against `ε = 1`. Here `λ` is the uniform probability
on `Bool`; with the counting measure (the volume of `def:egf` on a 0-manifold) this counterexample
and `exact_universality_fails` hold unchanged, the family being the same set of flows (checked by
hand, not formalized). -/
theorem allOutflows_reading_fails :
    (∃ F ∈ familyAll, F.policy = pol) ∧ IsSummablyL2Mixing pol lam ∧
      IsDenseNonnegConeL2 lam
        {f | ∃ F ∈ familyAll, F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s)} ∧
      ¬ IsUniversalFamilyEps lam familyAll := by
  refine ⟨⟨flowLam, Set.mem_insert _ _, rfl⟩, isSummablyL2Mixing_const lam,
    fun g hg hgnn η hη => ?_, fun h => ?_⟩
  · obtain ⟨f, hfD, hfm, hfg⟩ := isDenseNonnegConeL2_D g hg hgnn η hη
    exact ⟨f, ⟨flowId f, Set.mem_insert_of_mem _ ⟨f, hfD, rfl⟩, rfl⟩, hfm, hfg⟩
  · have hT : atTrue ≪ lam := withDensity_absolutelyContinuous _ _
    have hF : atFalse ≪ lam := withDensity_absolutelyContinuous _ _
    obtain ⟨F, hF𝓕, hlt⟩ := h atFalse atTrue inferInstance inferInstance hF hT
      (bounded_rnDeriv_two _ fun b => by cases b <;> simp)
      (bounded_rnDeriv_two _ fun b => by cases b <;> simp) 1 one_pos
    have hle := tvMass_le_errors_of_inflow_eq F.policy F.outflow atTrue atFalse
      (inflow_eq_outflow_of_mem_familyAll hF𝓕)
    exact absurd (one_le_tvMass.trans hle) (not_le.2 hlt)

end Coin

/-- **The exact Definition 3.2 does not follow** (C-18, `main.tex:774`): on `Bool` with the
uniform `λ`, a family of EGFs containing the summably `L²`-mixing resampling kernel and outflows
dense in the non-negative cone of `L²(λ)` (rational values) is ε-universal and not universal. -/
theorem exact_universality_fails :
    ∃ (lam : Measure Bool) (𝓕 : Set (GenerativeFlow Bool)) (π : Kernel Bool Bool)
      (D : Set (Bool → ℝ)), IsProbabilityMeasure lam ∧ IsSummablyL2Mixing π lam ∧
      (∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧
        F.outflow = lam.withDensity fun s => ENNReal.ofReal (f s)) ∧
      (∀ f ∈ D, ∀ s, 0 ≤ f s) ∧ IsDenseNonnegConeL2 lam D ∧
      (∀ F ∈ 𝓕, ∃ (p : ℕ) (Φ : Fin p → Bool ≃ₜ Bool) (α : Fin p → Bool → ℝ), IsEGF F Φ α) ∧
      IsUniversalFamilyEps lam 𝓕 ∧ ¬ IsUniversalFamily lam 𝓕 :=
  ⟨Coin.lam, Coin.family, Coin.pol, Coin.D, inferInstance, isSummablyL2Mixing_const _,
    Coin.mem_family, fun _ hf s => (hf s).1, Coin.isDenseNonnegConeL2_D,
    fun _ hF => Coin.isEGF_of_mem_family hF, Coin.isUniversalFamilyEps_family,
    Coin.not_isUniversalFamily⟩

/-- `theo:universality` with the cone correction and the exact Definition 3.2 is false. -/
theorem not_universalityExactCone : ¬ UniversalityExactCone Coin.lam := fun h =>
  Coin.not_isUniversalFamily (h Coin.family Coin.pol Coin.D (isSummablyL2Mixing_const _)
    Coin.mem_family Coin.isDenseNonnegConeL2_D)

end EGF
