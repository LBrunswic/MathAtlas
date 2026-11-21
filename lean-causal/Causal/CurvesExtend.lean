import Causal.CauchyExtension
import Causal.Geroch

/-!
# Every causal curve lies on an inextensible one, when there is a time function

No label is marked. This module discharges the model fact `Causality.CurvesExtend`
(`Causal/CauchyExtension.lean:82`: every future causal curve over a segment lies on an
inextensible causal curve over some interval), which the library carries as a named hypothesis
(kb/0012) of `IsCauchySurface.isAcausal` (`Causal/CauchyExtension.lean:110`), of lemma K
(`Causal.CompactCauchy`), of `CauchyDiamond` and of `SubExtension`. It is model-free (ETT
generality, namespace `Causal.Causality`) and imports no model (ETT layer since
T-abs-hoist-time-function: its static and Minkowski instances are in
`Causal.Model.CurvesExtendModels`); Barbot's sentence it formalizes is the prose item
[2.GH] of §2, `GHFspace.tex:498–507` (line numbers of `papers/barbot/legacy/orig/`, as
`docs/BARBOT.md` prescribes; the labelled copy runs 2 lines later here), unmarked, because the
paper's GH definition is not ETT's (`docs/BARBOT.md`, §2):

> A spacetime $M$ is \emph{globally hyperbolic\/} (abbreviation GH) if there is a proper time
> function $t: M \rightarrow \mathbb R$ such that every fiber $t^{-1}(t_{0})$ is spacelike.
> Moreover, it is required that any nonspacelike curve in $M$ can be extended to another one such
> that the restriction of $t$ on this extended curve is a diffeomorphism onto the entire $t(M)$.
> (`GHFspace.tex:498–504`)

> In other words, every fiber of $t$ is a \emph{Cauchy hypersurface,\/} meaning precisely that
> this is a hypersurface intersecting every unextendible nonspacelike curve in $M$.
> (`GHFspace.tex:504–507`)

## What is proved

* **The general theorem** (`exists_inextensible_of_timeFunction`): in **any** causality on any
  topological space carrying a continuous `T : M → ℝ` strictly increasing along `≤_M`
  (`x ≤ y`, `x ≠ y` ⇒ `T x < T y`), every future causal curve of any open `W` over any interval
  lies on an inextensible causal curve `γ` of `W` over an interval `J`, with `T ∘ γ = id` on `J`.
  Hence `CurvesExtend` (`curvesExtend_of_timeFunction`), and its relative form for every open `W`.
* **Barbot's form** (`exists_inextensible_univ_of_isCauchyTimeFunction`): if `T` is moreover a
  Cauchy time function, `M` causally arc-connected and causal with `J^±(p) ≠ {p}`, then `J = ℝ`:
  the extended curve is inextensible over `ℝ` and `T` restricted to it is the parameter, onto
  `ℝ` — the sentence of `GHFspace.tex:502–504`, `t(M) = ℝ`.
* **Globally hyperbolic spacetimes** (`GloballyHyperbolic.curvesExtend`,
  `GloballyHyperbolic.exists_inextensible_univ`), under the hypotheses of `theo:geroch`
  (i)⇒(ii) (`geroch_i_imp_ii`), whose time function is continuous and strictly increasing
  (DEC-15); witnessed jointly on the timelike line
  (`timelikeLine_curvesExtend_of_globallyHyperbolic`).
* **The ladder node `time_function`** (`Causality.HasTimeFunction`: a continuous `T` strictly
  increasing along `≤_M`, the hypothesis of the general theorem; moved here from
  `Causal.CBG.Pgcd`, same full name) and its two edges: `HasTimeFunction.curvesExtend`
  (`time_function ⇒ curves_extend`) and `HasTimeFunction.isCausal` (`time_function ⇒ is_causal`).
* **Instances**: the timelike line again (`timelikeLine_curvesExtend_of_timeFunction`); on static
  spacetimes `ℝ × X`, `X` **any** geodesic metric space, and on Minkowski space,
  `staticCausality.curvesExtend` and `minkowski_curvesExtend` are in
  `Causal.Model.CurvesExtendModels`.
* **Consequences**: Cauchy surfaces are acausal without the named hypothesis —
  `IsCauchySurface.isAcausal_of_timeFunction`, `IsCauchySurface.isAcausal_of_globallyHyperbolic`
  (and, in `Causal.Model.CurvesExtendModels`, `staticCausality.isAcausal_of_isCauchySurface`,
  `minkowski_isAcausal_of_isCauchySurface`).

## The proof: Zorn on time graphs

A naive Zorn on reparametrised extensions fails twice: chains of reparametrisations `φ` must be
composed coherently, and DEC-6's constant pieces make `φ` non-unique (kb/0017). The time function
removes both. A **time graph** (`IsTimeGraph`) is a set `K ⊆ M` on which `T` is injective and
whose inverse `T(K) → K` (`invFunOn T K`) is a causal curve: a curve with its parametrisation
*forgotten*, and canonically re-parametrised by `T`. Then:

1. the image of any causal curve is a time graph (`CausalCurveIn.isTimeGraph_image`): `T` is
   injective on it because `≤_M` is total along a curve and `T` strictly increasing; the inverse
   is a curve because collapsing the constant pieces of `c` through the continuous
   non-decreasing `T ∘ c` keeps the local relations (`CurveOn.of_comp_monotoneOn`: the window
   at a parameter is cut at the two ends `σ₁, σ₂` of its fibre);
2. time graphs ordered by **inclusion** form a poset in which the union of a chain is a time
   graph (`isTimeGraph_sUnion`): two parameters of the union lie in one member, whose curve
   agrees with the union's — the gluing needs no limit and no local argument;
3. a maximal time graph is an inextensible curve (`IsTimeGraph.inextensible_of_maximal`): the
   image of a strict extension is a time graph containing `K`, and contains the new value.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `CurvesExtend` holds (the named fact of `CauchyExtension.lean:82`) | ✓ proved, for every open `W` and every interval, not only `⊤` and segments |
| a time function `t` (Barbot l.498–500) | ⚠ reading: a continuous `T`, strictly increasing along `≤_M`; DEC-10's openness is not used. It is the only hypothesis of the general theorem: no separation, no countability, no causal arc-connectedness, no causality (implied) |
| `t` proper, fibers spacelike (l.498–502) | ⚠ weakened: not used |
| "diffeomorphism onto the entire `t(M)`" (l.503–504) | ⚠ reading: `T ∘ γ = id` on `J` (a homeomorphism onto `J`, no smoothness in ETT); `J = ℝ` when `T` is a Cauchy time function |
| global hyperbolicity (ETT's, `Causal/Properties.lean:144`) | ✓ carried in `GloballyHyperbolic.*` |
| the hypotheses of `geroch_i_imp_ii` (`T2Space`, `FirstCountableTopology`, `BorelSpace`, admissible `μ±`, tarentin, causally arc-connected, `J^±(p) ≠ {p}`) | ⚠ strengthened (Geroch hypotheses added): Barbot's GH sentence (l.498–504) has none of them; they are what ETT needs to produce the time function from GH (`theo:geroch` (i)⇒(ii)). `curvesExtend_of_timeFunction` needs none of them |

## SCOPE (disclosed)

* **The fully general statement is not proved, and is not stated.** Without a time function the
  Zorn step has no coherent parametrisation, and the transfinite chain of extensions need not
  stop. *Conjectured counterexample (not formalized):* the long ray `L` with its order causality
  (`≤_U`: `x ≤ y`, `[x, y] ⊆ U`, as on the timelike line) — locally the timelike line, so a local
  causality. A curve over a real interval has a σ-compact image, bounded in `L` because `ω₁` has
  uncountable cofinality, so it is extensible (append above its supremum, adjoining the supremum
  first if it is not attained): `L` has **no** inextensible curve, and `CurvesExtend` fails at a
  constant curve. `L` is not second countable; whether `CurvesExtend` holds in every strongly
  causal spacetime is open here; in every second countable tarentin globally hyperbolic Hausdorff
  spacetime it holds (`curvesExtend_of_secondCountable`, Levin's theorem, `Causal.LevinUtility`).
  Nothing is lost for Barbot's or gx's spacetimes: they are globally hyperbolic and
  `geroch_i_imp_ii` gives the time function.
* **Lemma K with `hext` discharged is not stated here**: `Causal.CompactCauchy` has no
  `.olean` at the time of writing (`object file … does not exist`), and this package may not
  build it. The corollary is one term:
  `isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp (curvesExtend_of_timeFunction hTc hTs) hψ hSc hSconn hloc`,
  or with `hG.curvesExtend hμp hμm hT hC hJm hJp` under the Geroch hypotheses.
* The relative form (every open `W`, every interval) is item (1) of the obstruction recorded at
  `SubExtension.lean:338` ("`CurvesExtend` relative to an open set, a Zorn-type existence"),
  given a time function; items (2)–(3) there are untouched.
* `IsTimeGraph` is stated under `[Nonempty M]`, which `invFunOn` needs; the theorems build the
  instance from the curve.
* **ETT layer** (T-abs-hoist-time-function, 2026-11-21). The section on static spacetimes and
  Minkowski space (`staticCausality.fst_lt_of_le`, `.curvesExtend`,
  `.exists_inextensible_graph_of_causalCurveIn`, `.isAcausal_of_isCauchySurface`,
  `minkowski_curvesExtend`, `minkowski_isAcausal_of_isCauchySurface`) moved verbatim, same full
  names, to the model module `Causal.Model.CurvesExtendModels`, the only reason this module
  imported `Causal.Minkowski`; the timelike-line witnesses stay (they use `Causal.Lines` and
  `Causal.Geroch` only). `Causality.HasTimeFunction` moved here verbatim from `Causal.CBG.Pgcd`
  (which imports a model), beside the theorem whose hypothesis it is, so that layer-1 modules and
  the `causal_ladder` rules can name it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set TopologicalSpace Topology Filter Function MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ### Collapsing the constant pieces of a curve -/

namespace CurveOn

variable {r : Opens M → M → M → Prop} {W : Opens M}

/-- **A curve read through a monotone change of parameter.** If `c = γ ∘ h` on `[s₁, s₂]`, with
`h` continuous and non-decreasing there, and `c` is a curve, then `γ` is a curve over
`[h s₁, h s₂]`. -/
theorem of_comp_monotoneOn (hr : IsRelFamily r) {c γ : ℝ → M} {h : ℝ → ℝ} {s₁ s₂ : ℝ}
    (hs : s₁ ≤ s₂) (hc : CurveOn r W c s₁ s₂) (hh : MonotoneOn h (Icc s₁ s₂))
    (hhc : ContinuousOn h (Icc s₁ s₂)) (hγ : ∀ s ∈ Icc s₁ s₂, γ (h s) = c s) :
    CurveOn r W γ (h s₁) (h s₂) := by
  have hivt : ∀ τ ∈ Icc (h s₁) (h s₂), ∃ s ∈ Icc s₁ s₂, h s = τ := fun τ hτ =>
    intermediate_value_Icc hs hhc hτ
  have hrefl : ∀ {x y : ℝ}, x ∈ Icc s₁ s₂ → y ∈ Icc s₁ s₂ → h x < h y → x < y :=
    fun hx hy hxy => lt_of_not_ge fun hyx => (hh hy hx hyx).not_gt hxy
  refine ⟨fun τ hτ => ?_, fun τ hτ N hN hτN => ?_⟩
  · obtain ⟨s, hs', rfl⟩ := hivt τ hτ
    rw [hγ s hs']
    exact hc.mem s hs'
  -- the fibre `F` of `τ`, a closed segment `[σ₁, σ₂]` on which `c` is constant, `= γ τ`
  set F := Icc s₁ s₂ ∩ h ⁻¹' {τ} with hF
  have hFne : F.Nonempty := by
    obtain ⟨s, hs', e⟩ := hivt τ hτ
    exact ⟨s, hs', e⟩
  have hFc : IsClosed F := hhc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hFb : BddBelow F := ⟨s₁, fun x hx => hx.1.1⟩
  have hFa : BddAbove F := ⟨s₂, fun x hx => hx.1.2⟩
  have hσ₁ : sInf F ∈ F := hFc.csInf_mem hFne hFb
  have hσ₂ : sSup F ∈ F := hFc.csSup_mem hFne hFa
  set σ₁ := sInf F
  set σ₂ := sSup F
  have e₁ : h σ₁ = τ := hσ₁.2
  have e₂ : h σ₂ = τ := hσ₂.2
  have hσ₁le : ∀ x ∈ F, σ₁ ≤ x := fun x hx => csInf_le hFb hx
  have hσ₂ge : ∀ x ∈ F, x ≤ σ₂ := fun x hx => le_csSup hFa hx
  have hcσ₁ : c σ₁ = γ τ := by rw [← hγ σ₁ hσ₁.1, e₁]
  have hcσ₂ : c σ₂ = γ τ := by rw [← hγ σ₂ hσ₂.1, e₂]
  obtain ⟨l₁, u₁, hl₁, hu₁, hrel₁⟩ := hc.rel σ₁ hσ₁.1 N hN (by rw [hcσ₁]; exact hτN)
  obtain ⟨l₂, u₂, hl₂, hu₂, hrel₂⟩ := hc.rel σ₂ hσ₂.1 N hN (by rw [hcσ₂]; exact hτN)
  -- below `τ`, the parameters near `τ` are in the window of `σ₁`
  have hleft : ∃ l < τ, ∀ s ∈ Icc s₁ s₂, l < h s → h s < τ → l₁ < s := by
    by_cases h1 : h s₁ < τ
    · have hs₁σ : s₁ < σ₁ := hrefl ⟨le_rfl, hs⟩ hσ₁.1 (by rw [e₁]; exact h1)
      have hmax : max l₁ s₁ < σ₁ := max_lt hl₁ hs₁σ
      have hp1 : max l₁ s₁ < (max l₁ s₁ + σ₁) / 2 := by linarith
      have hp2 : (max l₁ s₁ + σ₁) / 2 < σ₁ := by linarith
      have hpI : (max l₁ s₁ + σ₁) / 2 ∈ Icc s₁ s₂ :=
        ⟨(le_max_right _ _).trans hp1.le, hp2.le.trans hσ₁.1.2⟩
      have hhp : h ((max l₁ s₁ + σ₁) / 2) < τ := by
        rcases (hh hpI hσ₁.1 hp2.le).lt_or_eq with h' | h'
        · rwa [e₁] at h'
        · exact absurd (hσ₁le _ ⟨hpI, h'.trans e₁⟩) (not_le.2 hp2)
      exact ⟨_, hhp, fun s hs hls _ => ((le_max_left _ _).trans_lt hp1).trans (hrefl hpI hs hls)⟩
    · exact ⟨τ - 1, by linarith, fun s hsI _ hsτ =>
        absurd ((hh ⟨le_rfl, hs⟩ hsI hsI.1).trans_lt hsτ) h1⟩
  -- above `τ`, in the window of `σ₂`
  have hright : ∃ u, τ < u ∧ ∀ s ∈ Icc s₁ s₂, τ < h s → h s < u → s < u₂ := by
    by_cases h2 : τ < h s₂
    · have hs₂σ : σ₂ < s₂ := hrefl hσ₂.1 ⟨hs, le_rfl⟩ (by rw [e₂]; exact h2)
      have hmin : σ₂ < min u₂ s₂ := lt_min hu₂ hs₂σ
      have hq1 : (σ₂ + min u₂ s₂) / 2 < min u₂ s₂ := by linarith
      have hq2 : σ₂ < (σ₂ + min u₂ s₂) / 2 := by linarith
      have hqI : (σ₂ + min u₂ s₂) / 2 ∈ Icc s₁ s₂ :=
        ⟨hσ₂.1.1.trans hq2.le, hq1.le.trans (min_le_right _ _)⟩
      have hhq : τ < h ((σ₂ + min u₂ s₂) / 2) := by
        rcases (hh hσ₂.1 hqI hq2.le).lt_or_eq with h' | h'
        · rwa [e₂] at h'
        · exact absurd (hσ₂ge _ ⟨hqI, h'.symm.trans e₂⟩) (not_le.2 hq2)
      exact ⟨_, hhq, fun s hs _ hsu =>
        (hrefl hs hqI hsu).trans (hq1.trans_le (min_le_left _ _))⟩
    · exact ⟨τ + 1, by linarith, fun s hsI hτs _ =>
        absurd (hτs.trans_le (hh hsI ⟨hs, le_rfl⟩ hsI.2)) h2⟩
  obtain ⟨l, hlτ, hl⟩ := hleft
  obtain ⟨u, huτ, hu⟩ := hright
  refine ⟨l, u, hlτ, huτ, fun τ₁ hτ₁ τ₂ hτ₂ h1 h2 h3 => ?_⟩
  obtain ⟨t₁, ht₁, rfl⟩ := hivt τ₁ hτ₁
  obtain ⟨t₂, ht₂, rfl⟩ := hivt τ₂ hτ₂
  rw [hγ t₁ ht₁, hγ t₂ ht₂]
  have ht12 : t₁ < t₂ := hrefl ht₁ ht₂ h2
  rcases lt_or_ge (h t₂) τ with h2τ | h2τ
  · -- both below `τ`
    have h1τ : h t₁ < τ := h2.trans h2τ
    have ht₂σ : t₂ < σ₁ := hrefl ht₂ hσ₁.1 (by rw [e₁]; exact h2τ)
    exact hrel₁ t₁ ht₁ t₂ ht₂ (hl t₁ ht₁ h1 h1τ) ht12 (ht₂σ.trans hu₁)
  rcases lt_or_ge (h t₁) τ with h1τ | h1τ
  · -- `t₁` below `τ`, `t₂` at or above it
    have hA : r N (c t₁) (c σ₁) := hrel₁ t₁ ht₁ σ₁ hσ₁.1 (hl t₁ ht₁ h1 h1τ)
      (hrefl ht₁ hσ₁.1 (by rw [e₁]; exact h1τ)) hu₁
    rcases h2τ.lt_or_eq with h2τ' | h2τ'
    · have hB : r N (c σ₂) (c t₂) := hrel₂ σ₂ hσ₂.1 t₂ ht₂ hl₂
        (hrefl hσ₂.1 ht₂ (by rw [e₂]; exact h2τ')) (hu t₂ ht₂ h2τ' h3)
      rw [hcσ₁] at hA
      rw [hcσ₂] at hB
      exact hr.trans hA hB
    · have : c t₂ = c σ₁ := by rw [← hγ t₂ ht₂, ← hγ σ₁ hσ₁.1, e₁, h2τ']
      rw [this]
      exact hA
  · -- both at or above `τ`
    have h2τ' : τ < h t₂ := h1τ.trans_lt h2
    rcases h1τ.lt_or_eq with h1τ' | h1τ'
    · exact hrel₂ t₁ ht₁ t₂ ht₂ (hl₂.trans (hrefl hσ₂.1 ht₁ (by rw [e₂]; exact h1τ'))) ht12
        (hu t₂ ht₂ h2τ' h3)
    · have : c t₁ = c σ₂ := by rw [← hγ t₁ ht₁, ← hγ σ₂ hσ₂.1, e₂, h1τ']
      rw [this]
      exact hrel₂ σ₂ hσ₂.1 t₂ ht₂ hl₂ (hrefl hσ₂.1 ht₂ (by rw [e₂]; exact h2τ'))
        (hu t₂ ht₂ h2τ' h3)

end CurveOn

namespace Causality

variable {C : Causality M} {T : M → ℝ} {W : Opens M} {I : Set ℝ} {c : ℝ → M} {a b : ℝ}

/-- A future causal curve over a segment is a curve over the interval `[a, b]`. -/
theorem CausalCurveOn.causalCurveIn_Icc (hc : C.CausalCurveOn W c a b) (hab : a ≤ b) :
    C.CausalCurveIn W (Icc a b) c :=
  ⟨nonempty_Icc.2 hab, ordConnected_Icc, fun _ ha' _ hb' =>
    CurveOn.restrict hc ha'.1 hb'.2 le_rfl fun t ht => hc.mem t ⟨ha'.1.trans ht.1, ht.2.trans hb'.2⟩⟩

/-- Along a causal curve, a function strictly increasing along `≤_M` separates distinct points:
two parameters with the same value of `T` give the same point. -/
theorem CausalCurveIn.eq_of_time_eq (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hc : C.CausalCurveIn W I c) {s s' : ℝ} (hs : s ∈ I) (hs' : s' ∈ I)
    (h : T (c s) = T (c s')) : c s = c s' := by
  by_contra hne
  rcases le_total s s' with hle | hle
  · exact (hT _ _ (C.isRelFamily_le.mono le_top (hc.le_of_le hs hs' hle)) hne).ne h
  · exact (hT _ _ (C.isRelFamily_le.mono le_top (hc.le_of_le hs' hs hle)) (Ne.symm hne)).ne h.symm

/-- Along a causal curve, a function strictly increasing along `≤_M` is non-decreasing. -/
theorem CausalCurveIn.time_mono (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hc : C.CausalCurveIn W I c) {s s' : ℝ} (hs : s ∈ I) (hs' : s' ∈ I) (hle : s ≤ s') :
    T (c s) ≤ T (c s') := by
  rcases eq_or_ne (c s) (c s') with e | e
  · rw [e]
  · exact (hT _ _ (C.isRelFamily_le.mono le_top (hc.le_of_le hs hs' hle)) e).le

/-- **Reparametrisation by the time function.** If `γ (T (c s)) = c s` on `I`, then `γ` is a
causal curve over the interval `T(c(I))`. -/
theorem CausalCurveIn.timeReparam (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hc : C.CausalCurveIn W I c) {γ : ℝ → M}
    (hγ : ∀ s ∈ I, γ (T (c s)) = c s) : C.CausalCurveIn W ((fun s => T (c s)) '' I) γ := by
  have hcont : ∀ a ∈ I, ∀ b ∈ I, ContinuousOn (fun s => T (c s)) (Icc a b) := fun a ha b hb =>
    hTc.comp_continuousOn (CurveOn.continuousOn C.isRelFamily_le (hc.curve a ha b hb))
  have key : ∀ s₁ ∈ I, ∀ s₂ ∈ I, s₁ ≤ s₂ → C.CausalCurveOn W γ (T (c s₁)) (T (c s₂)) :=
    fun s₁ hs₁ s₂ hs₂ h12 =>
      CurveOn.of_comp_monotoneOn (h := fun s => T (c s)) C.isRelFamily_le h12
        (hc.curve s₁ hs₁ s₂ hs₂)
        (fun x hx y hy hxy => hc.time_mono hT (hc.ordConnected.out hs₁ hs₂ hx)
          (hc.ordConnected.out hs₁ hs₂ hy) hxy)
        (hcont s₁ hs₁ s₂ hs₂) fun s hs => hγ s (hc.ordConnected.out hs₁ hs₂ hs)
  refine ⟨hc.nonempty.image _, ⟨?_⟩, ?_⟩
  · rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ z hz
    rcases le_total s₁ s₂ with h12 | h21
    · obtain ⟨s, hs, e⟩ := intermediate_value_Icc h12 (hcont s₁ hs₁ s₂ hs₂) hz
      exact ⟨s, hc.ordConnected.out hs₁ hs₂ hs, e⟩
    · have : z = T (c s₁) := le_antisymm (hz.2.trans (hc.time_mono hT hs₂ hs₁ h21)) hz.1
      exact ⟨s₁, hs₁, this.symm⟩
  · rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    rcases le_total s₁ s₂ with h12 | h21
    · exact key s₁ hs₁ s₂ hs₂ h12
    · rcases (hc.time_mono hT hs₂ hs₁ h21).lt_or_eq with hlt | heq
      · exact CurveOn.of_lt hlt
      · show C.CausalCurveOn W γ (T (c s₁)) (T (c s₂))
        rw [← heq]
        exact key s₂ hs₂ s₂ hs₂ le_rfl

/-! ### Time graphs -/

variable [Nonempty M]

variable (C) in
/-- `K` is a **time graph** of `W` for `T`: `T` is injective on `K`, and the inverse of `T` on
`K` is a causal curve of `W` over `T(K)`. -/
def IsTimeGraph (W : Opens M) (T : M → ℝ) (K : Set M) : Prop :=
  InjOn T K ∧ C.CausalCurveIn W (T '' K) (invFunOn T K)

namespace IsTimeGraph

variable {K : Set M}

omit [TopologicalSpace M] in
/-- On `T(K)`, the inverse lands in `K` and is a right inverse of `T`. -/
theorem time_invFunOn {τ : ℝ} (hτ : τ ∈ T '' K) : invFunOn T K τ ∈ K ∧ T (invFunOn T K τ) = τ :=
  invFunOn_pos hτ

/-- On a time graph, the inverse is a left inverse of `T`. -/
theorem invFunOn_time (hK : C.IsTimeGraph W T K) {x : M} (hx : x ∈ K) :
    invFunOn T K (T x) = x :=
  hK.1 (time_invFunOn (mem_image_of_mem T hx)).1 hx (time_invFunOn (mem_image_of_mem T hx)).2

/-- A time graph is the image of its curve. -/
theorem image_invFunOn (hK : C.IsTimeGraph W T K) : invFunOn T K '' (T '' K) = K := by
  refine Subset.antisymm ?_ fun x hx => ⟨T x, mem_image_of_mem T hx, hK.invFunOn_time hx⟩
  rintro _ ⟨τ, hτ, rfl⟩
  exact (time_invFunOn hτ).1

end IsTimeGraph

/-- **The image of a causal curve is a time graph.** -/
theorem CausalCurveIn.isTimeGraph_image (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hc : C.CausalCurveIn W I c) :
    C.IsTimeGraph W T (c '' I) := by
  have hinj : InjOn T (c '' I) := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ e
    exact hc.eq_of_time_eq hT hs hs' e
  refine ⟨hinj, ?_⟩
  rw [image_image]
  refine hc.timeReparam hTc hT fun s hs => ?_
  have hex : T (c s) ∈ T '' (c '' I) := mem_image_of_mem T (mem_image_of_mem c hs)
  exact hinj (IsTimeGraph.time_invFunOn hex).1 (mem_image_of_mem c hs)
    (IsTimeGraph.time_invFunOn hex).2

/-- **The union of a chain of time graphs is a time graph**: two points of the union lie in one
member, and the curves of the members agree on their common parameters. -/
theorem isTimeGraph_sUnion {ch : Set (Set M)} (hch : IsChain (· ⊆ ·) ch) (hne : ch.Nonempty)
    (h : ∀ K ∈ ch, C.IsTimeGraph W T K) : C.IsTimeGraph W T (⋃₀ ch) := by
  have hpair : ∀ x ∈ ⋃₀ ch, ∀ y ∈ ⋃₀ ch, ∃ K ∈ ch, x ∈ K ∧ y ∈ K := by
    rintro x ⟨K₁, hK₁, hx⟩ y ⟨K₂, hK₂, hy⟩
    rcases eq_or_ne K₁ K₂ with e | e
    · exact ⟨K₂, hK₂, e ▸ hx, hy⟩
    rcases hch hK₁ hK₂ e with h12 | h21
    · exact ⟨K₂, hK₂, h12 hx, hy⟩
    · exact ⟨K₁, hK₁, hx, h21 hy⟩
  have hinj : InjOn T (⋃₀ ch) := by
    intro x hx y hy e
    obtain ⟨K, hK, hxK, hyK⟩ := hpair x hx y hy
    exact (h K hK).1 hxK hyK e
  have heq : ∀ K ∈ ch, ∀ τ ∈ T '' K, invFunOn T K τ = invFunOn T (⋃₀ ch) τ := by
    intro K hK τ hτ
    have h1 := IsTimeGraph.time_invFunOn hτ
    have h2 := IsTimeGraph.time_invFunOn (image_mono (subset_sUnion_of_mem hK) hτ)
    exact hinj (subset_sUnion_of_mem hK h1.1) h2.1 (h1.2.trans h2.2.symm)
  have hpairT : ∀ a ∈ T '' ⋃₀ ch, ∀ b ∈ T '' ⋃₀ ch, ∃ K ∈ ch, a ∈ T '' K ∧ b ∈ T '' K := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨K, hK, hxK, hyK⟩ := hpair x hx y hy
    exact ⟨K, hK, mem_image_of_mem T hxK, mem_image_of_mem T hyK⟩
  refine ⟨hinj, ⟨?_, ⟨fun a ha b hb z hz => ?_⟩, fun a ha b hb => ?_⟩⟩
  · obtain ⟨K, hK⟩ := hne
    obtain ⟨τ, hτ⟩ := (h K hK).2.nonempty
    exact ⟨τ, image_mono (subset_sUnion_of_mem hK) hτ⟩
  · obtain ⟨K, hK, haK, hbK⟩ := hpairT a ha b hb
    exact image_mono (subset_sUnion_of_mem hK) ((h K hK).2.ordConnected.out haK hbK hz)
  · obtain ⟨K, hK, haK, hbK⟩ := hpairT a ha b hb
    exact CurveOn.congr ((h K hK).2.curve a haK b hbK) fun τ hτ =>
      heq K hK τ ((h K hK).2.ordConnected.out haK hbK hτ)

/-- **A maximal time graph is an inextensible curve**: a strict extension would be a curve whose
image is a strictly larger time graph. -/
theorem IsTimeGraph.inextensible_of_maximal (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) {K : Set M}
    (hK : Maximal (fun K => C.IsTimeGraph W T K) K) : C.Inextensible W (T '' K) (invFunOn T K) := by
  refine ⟨hK.1.2, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, -, hφmaps, -, hφeq⟩, ⟨t', ht', hgrow⟩⟩
  have hsub : K ⊆ c' '' I' := fun x hx => by
    have hτ : T x ∈ T '' K := mem_image_of_mem T hx
    refine ⟨φ (T x), hφmaps hτ, ?_⟩
    rw [hφeq _ hτ]
    exact hK.1.invFunOn_time hx
  have hmem : c' t' ∈ K := hK.2 (hcurve.isTimeGraph_image hTc hT) hsub (mem_image_of_mem c' ht')
  exact hgrow (T (c' t')) (mem_image_of_mem T hmem) (hK.1.invFunOn_time hmem).symm

end Causality

/-! ### The theorem -/

namespace Causality

variable {C : Causality M} {T : M → ℝ} {W : Opens M} {I : Set ℝ} {c : ℝ → M}

/-- **Every causal curve lies on an inextensible one, parametrised by the time function** — in
any causality carrying a continuous function `T` strictly increasing along `≤_M`, for curves of
any open set `W` over any interval. The inextensible curve `γ` over `J` satisfies `T ∘ γ = id` on
`J`: it is Barbot's "the restriction of `t` on this extended curve is a diffeomorphism onto"
its image, `J`. Zorn's lemma on time graphs ordered by inclusion. -/
theorem exists_inextensible_of_timeFunction (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hc : C.CausalCurveIn W I c) :
    ∃ (J : Set ℝ) (γ : ℝ → M), C.Inextensible W J γ ∧ c '' I ⊆ γ '' J ∧ ∀ τ ∈ J, T (γ τ) = τ := by
  haveI : Nonempty M := ⟨c hc.nonempty.some⟩
  obtain ⟨K, hsub, hK⟩ := zorn_subset_nonempty {K | C.IsTimeGraph W T K}
    (fun ch hch hchain hne => ⟨⋃₀ ch, isTimeGraph_sUnion hchain hne hch,
      fun _ hs => subset_sUnion_of_mem hs⟩) (c '' I) (hc.isTimeGraph_image hTc hT)
  refine ⟨T '' K, invFunOn T K, IsTimeGraph.inextensible_of_maximal hTc hT hK, ?_,
    fun τ hτ => (IsTimeGraph.time_invFunOn hτ).2⟩
  rw [hK.1.image_invFunOn]
  exact hsub

/-- **`CurvesExtend` holds in every causality with a continuous time function strictly
increasing along `≤_M`.** -/
theorem curvesExtend_of_timeFunction (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : C.CurvesExtend := fun _ _ _ hab hc => by
  obtain ⟨J, γ, h1, h2, -⟩ := exists_inextensible_of_timeFunction hTc hT (hc.causalCurveIn_Icc hab)
  exact ⟨J, γ, h1, h2⟩

/-- **Barbot's form** (`GHFspace.tex:502–504`): with a Cauchy time function strictly increasing
along `≤_M`, in a causally arc-connected causal spacetime with `J^±(p) ≠ {p}`, every causal curve
over an interval lies on an inextensible curve over `ℝ` along which `T` is the parameter, hence
onto `ℝ`. -/
theorem exists_inextensible_univ_of_isCauchyTimeFunction (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hTC : C.IsCauchyTimeFunction T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hc : C.CausalCurveIn ⊤ I c) :
    ∃ γ : ℝ → M, C.Inextensible ⊤ univ γ ∧ c '' I ⊆ range γ ∧ ∀ τ, T (γ τ) = τ := by
  obtain ⟨J, γ, hγ, hsub, hTγ⟩ := exists_inextensible_of_timeFunction hTC.1.continuous hT hc
  obtain ⟨ψ, -, -, hψr, hinext⟩ := hγ.reparam hC hcaus hJm hJp
  obtain ⟨hbot, htop⟩ := hTC.2 _ hinext
  have hψJ : ∀ t, ψ t ∈ J := fun t => hψr ▸ mem_range_self t
  have hψT : ∀ t, (T ∘ (γ ∘ ψ)) t = ψ t := fun t => hTγ _ (hψJ t)
  have hJ : J = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨t₁, ht₁⟩ := (htop.eventually (eventually_ge_atTop x)).exists
    obtain ⟨t₂, ht₂⟩ := (hbot.eventually (eventually_le_atBot x)).exists
    rw [hψT] at ht₁ ht₂
    exact hγ.1.ordConnected.out (hψJ t₂) (hψJ t₁) ⟨ht₂, ht₁⟩
  subst hJ
  exact ⟨γ, hγ, by rwa [image_univ] at hsub, fun τ => hTγ τ trivial⟩

/-! ### Globally hyperbolic spacetimes -/

section GloballyHyperbolic

variable [T2Space M] [FirstCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {μp μm : Measure M}

/-- **`CurvesExtend` in a globally hyperbolic spacetime**, under the hypotheses of `theo:geroch`
(i)⇒(ii) (`geroch_i_imp_ii`): the time function `log(−t⁻/t⁺)` is continuous and strictly
increasing along `≤_M`. -/
theorem GloballyHyperbolic.curvesExtend (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hG : C.GloballyHyperbolic) : C.CurvesExtend := by
  obtain ⟨τ, hτ, hτs⟩ := geroch_i_imp_ii hμp hμm hT hC hJm hJp hG
  exact curvesExtend_of_timeFunction hτ.1.continuous hτs

/-- **Barbot's form in a globally hyperbolic spacetime** (`GHFspace.tex:502–504`): every causal
curve over an interval lies on an inextensible curve over `ℝ` parametrised by the Geroch time
function. -/
theorem GloballyHyperbolic.exists_inextensible_univ (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hG : C.GloballyHyperbolic) (hc : C.CausalCurveIn ⊤ I c) :
    ∃ (τ : M → ℝ) (γ : ℝ → M), C.IsCauchyTimeFunction τ ∧ C.Inextensible ⊤ univ γ ∧
      c '' I ⊆ range γ ∧ ∀ t, τ (γ t) = t := by
  obtain ⟨τ, hτ, hτs⟩ := geroch_i_imp_ii hμp hμm hT hC hJm hJp hG
  obtain ⟨γ, h1, h2, h3⟩ :=
    exists_inextensible_univ_of_isCauchyTimeFunction hC hG.1 hJm hJp hτ hτs hc
  exact ⟨τ, γ, hτ, h1, h2, h3⟩

end GloballyHyperbolic

/-! ### Consequences: Cauchy surfaces are acausal -/

/-- `IsCauchySurface.isAcausal` with `CurvesExtend` discharged by a time function. -/
theorem IsCauchySurface.isAcausal_of_timeFunction {S : Set M} (hS : C.IsCauchySurface S)
    (hC : C.CausallyArcConnected) (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : C.IsAcausal S :=
  hS.isAcausal hC (curvesExtend_of_timeFunction hTc hT)

/-- **A Cauchy surface of a globally hyperbolic spacetime is acausal**, under the hypotheses of
`theo:geroch` (i)⇒(ii). -/
theorem IsCauchySurface.isAcausal_of_globallyHyperbolic [T2Space M] [FirstCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] {μp μm : Measure M} {S : Set M}
    (hS : C.IsCauchySurface S) (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm)
    (hT : C.Tarentin) (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hG : C.GloballyHyperbolic) : C.IsAcausal S :=
  hS.isAcausal hC (hG.curvesExtend hμp hμm hT hC hJm hJp)

end Causality

/-! ### The ladder node `time_function` -/

/-- **A continuous time function strictly increasing along `≤`** (the hypothesis of
`exists_inextensible_of_timeFunction` and `curvesExtend_of_timeFunction` above, and of
`CBG.injOn_of_injOn_cauchy`, Sbierski Lemma 3.3 in the abstract setting): the ladder node
`time_function` (`programme/ladder.toml`). Over a CBG `Geometry` it is produced by the field
`timeFunction` (interface round 2, `CBG.Dev.causality_hasTimeFunction`), whose conclusion is this
body verbatim. It is neither the strict library's `Causality.IsTimeFunction`
(`defi:fonction_temps`, `Causal/Morphism.lean:832`, a strong morphism to `timelikeLine`: open,
non-decreasing, and it does not make `C` causal, `exists_isTimeFunction_not_isCausal`, kb/0058)
nor `IsCauchyTimeFunction` (`Causal/Cauchy.lean:83`), and must not be read as either: it is exactly
the hypothesis form of `curvesExtend_of_timeFunction`. Defined in `Causal.CBG.Pgcd` until
T-abs-hoist-time-function; same full name. -/
def Causality.HasTimeFunction {M : Type*} [TopologicalSpace M] (C : Causality M) : Prop :=
  ∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y

namespace Causality

variable {C : Causality M}

/-- **Curves extend where there is a time function** — the ladder edge
`time_function ⇒ curves_extend`: `curvesExtend_of_timeFunction` with its hypotheses packaged as
`HasTimeFunction`. -/
theorem HasTimeFunction.curvesExtend (h : C.HasTimeFunction) : C.CurvesExtend := by
  obtain ⟨_, hTc, hT⟩ := h
  exact curvesExtend_of_timeFunction hTc hT

/-- **A time function strictly increasing along `≤` makes the causality causal** — the ladder edge
`time_function ⇒ is_causal`: if `x ≤ y ≤ x` with `x ≠ y`, then `T x < T y < T x`. This is
`Causality.isCausal_of_exists_timeFunction` (`Causal.CausalIsoInvariance`, which takes this
body) read through `HasTimeFunction`, proved here directly so that this module need not import
that one; continuity is not used. ETT's time function (`defi:fonction_temps`) does not suffice
(`exists_isTimeFunction_not_isCausal`, the doubled line, kb/0058). -/
theorem HasTimeFunction.isCausal (h : C.HasTimeFunction) : C.IsCausal := by
  obtain ⟨T, -, hT⟩ := h
  intro x y hxy hyx
  by_contra hne
  exact lt_asymm (hT x y hxy hne) (hT y x hyx (Ne.symm hne))

end Causality

/-! ### Witnesses on the timelike line -/

/-- Sanity: the general theorem recovers the timelike line's `timelikeLine_curvesExtend`, with
the time function `id`. -/
theorem timelikeLine_curvesExtend_of_timeFunction : timelikeLine.CurvesExtend :=
  Causality.curvesExtend_of_timeFunction continuous_id fun _ _ h hne =>
    lt_of_le_of_ne (timelikeLine_le.1 h).1 hne

/-- **Witness** (kb/0011): the hypotheses of `GloballyHyperbolic.curvesExtend` are jointly
satisfiable — on the timelike line, with the Gaussian measures of `Causal.Geroch`. -/
theorem timelikeLine_curvesExtend_of_globallyHyperbolic : timelikeLine.CurvesExtend :=
  Causality.GloballyHyperbolic.curvesExtend timelikeLine_admissible_past_and_future.2
    timelikeLine_admissible_past_and_future.1 timelikeLine_tarentin
    timelikeLine_causallyArcConnected timelikeLine_Jminus_ne timelikeLine_Jplus_ne
    timelikeLine_globallyHyperbolic

end Causal
