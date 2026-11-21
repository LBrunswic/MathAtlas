import Causal.Inextensible
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The development of a translation line, model-free

Roadmap target `T-ett-line-development`; ETT layer: it imports no model (no `Causal.Port`,
`Causal.Model`, `Causal.CBG`, `Causal.SingularFlat`). **No label is marked.** It serves
`lem:past_BTZ` — `ETT.tex:1515`, its (a), as a model-free tool for the fields `BTZAxioms.line`
(`α = 0`) and `SingularFlatAxioms.massive_line` (`α > 0`) of `Causal.SingularFlat`; the fields
at every manifold are T-ett-sfa-line-e0, T-ett-sfa-massive-line and T-ett-singular-sfa.

> `lem:past_BTZ` (a). For every $\alpha\in \RR_+$, each connected component of
> $\sing_\alpha(M)$ is an inextensible causal curve; if $\alpha>0$, such a connected component is
> moreover chronal.

> Proof of (a). Let $\alpha \in \RR_+$ and let $\Delta$ be a connected component of
> $\sing_\alpha(M)$. By Property \ref{prop:GX_sing_dec} it is a connected $1$-dimensional
> submanifold; since $M$ is a differential manifold, it is parametrisable by $\RR$. Moreover it is
> locally chronal by Definition \ref{defi:causal_Ealpha} if $\alpha>0$, and locally causal by
> Definition \ref{defi:causal_E0} if $\alpha=0$. Consequently it is a chronal curve if $\alpha>0$
> and a causal curve if $\alpha=0$. Finally, $\Delta$ is inextensible, being a closed submanifold
> without boundary. (`ETT.tex:1529–1533`)

## What is here (no `sorry`)

* `IsTranslationAtlas S V τ σ J`: charts `τ i : S ∩ V i → J i ⊆ ℝ`, `J i` open, with inverses
  `σ i`, covering `S`, whose transitions are translations near every point (`τ j = τ i + k` on
  `S`). The time coordinate of the line in the charts of `E₀` and `E_κ` is one
  (`BPrimeE0.exists_eqOn_rotE0_tauShift`, `BPrimeEAlpha.prop_isom_local`).
* `exists_development` (steps (1)–(6)): `M` Hausdorff, `S` closed: through every `p ∈ S` a
  development `γ : ℝ → M` (`IsLineDevelopment`): `γ 0 = p`, continuous,
  `range γ = connectedComponentIn S p`, near each `t` equal to `σ i ∘ ψ` with `ψ` continuous and
  strictly increasing, the image of every interval about `t` a neighbourhood of `γ t` in `S`,
  no limit at `+∞` nor at `-∞`. Construction: unit-speed line arcs (`IsLineArc`), unique
  (`IsLineArc.eqOn`), the maximal one (`dev`) on the union of their domains, continued through
  every chart it meets (`dev_continue`), image clopen in `S` (`image_dev_eq`), reparametrised by
  `ℝ` (`exists_strictMono_range_eq`). No classification of 1-manifolds, no countability.
* `IsLineDevelopment.isClosedEmbedding` (step (7)): injective ⇒ closed embedding.
* `curveOn_of_local`, `causalCurveIn_univ_of_local`, `chronalCurveOn_of_local` (step (8)).
* `futureInextensible_of_not_tendsto_atTop`, `pastInextensible_of_not_tendsto_atBot`,
  `inextensible_of_not_tendsto` (step (9)): a causal curve of `W` over `ℝ` with no limit in `W`
  at `+∞` (`-∞`) is future- (past-) inextensible in `W`; no separation axiom.
* `injective_of_isCausal`: in a causal `M`, a locally injective causal curve over `ℝ` is
  injective (the bridge from `C.IsCausal` to step (7)).
* `exists_line`, `exists_chronal_line`: the exact shapes of `BTZAxioms.line` and
  `SingularFlatAxioms.massive_line`, from an atlas whose `σ i` are causal (chronal) curves over
  every segment of `J i`.
* Witnesses (kb/0011): the timelike line (`timelikeLine_line`, `timelikeLine_chronal_line`,
  `timelikeLine_id_line`: `S = ℝ`, `γ = id`); the circle `ℝ / Pℤ` (`circle_isTranslationAtlas`,
  `circle_isLineDevelopment`: `γ = (↑)`, periodic and not injective,
  `circle_periodic_not_injective`; no closed embedding `ℝ → ℝ / Pℤ` exists,
  `not_isClosedEmbedding_circle`, so (7) needs its injectivity); with `allRelated` (every two
  points of an open set related, not causal) the periodic `γ` satisfies the conclusion of
  `exists_line` and is chronal (`circle_line`).

## Hypothesis checklist (`exists_development`, `exists_line`)

| paper | here |
|---|---|
| `sing_α(M)` « a connected 1-dimensional submanifold » (`prop:GX_sing_dec`, l.1435) | ⚠ strengthened (a reading): `S` closed with a translation atlas; the translations come from the charts of `E₀`, `E_κ`, not from being a 1-submanifold |
| « since `M` is a differential manifold » | ⚠ weakened: `[T2Space M]` only; no smoothness, no countability |
| « parametrisable by `ℝ` » | ✓ continuous `γ : ℝ → M` onto the component, locally a homeomorphism onto `S`; a closed embedding when injective, in particular when `C` is causal |
| « locally causal » / « locally chronal » | ✓ carried: each `σ i` a causal (chronal) curve over every segment of `J i` |
| « inextensible, being a closed submanifold without boundary » | ✓ derived: `S` closed, no limit at `±∞`, `inextensible_of_not_tendsto` |

## SCOPE (disclosed)

* **Model-free.** The atlas is a datum; building it at the `E≥0`-manifolds (one application of
  the chart lemmas above per pair of charts) is left to the consumers.
* **Periodic parametrisations are allowed** (DEC-6). A compact component may be the image of a
  periodic `γ` (proved for the circle); it is then no closed embedding, which is why `BTZAxioms.line` asks
  one only when `M` is causal. In a causal `M` the development is injective
  (`injective_of_isCausal`), hence a closed embedding.
* **No second countability.** The component through `p` is the continuous image of `ℝ`, hence
  σ-compact, for every `S` with a translation atlas (by `exists_development`; not stated as a
  lemma).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

namespace LineDevelopment

open Set Filter Topology TopologicalSpace Function

universe u v

variable {M : Type u} [TopologicalSpace M] {ι : Type v}

/-! ### Translation atlases -/

/-- **A translation atlas of `S ⊆ M`**: for each `i`, an open `V i ⊆ M`, a chart
`τ i : S ∩ V i → J i` onto an open `J i ⊆ ℝ` with inverse `σ i`, the `V i` covering `S`, and the
transition maps translations: near every point of `S ∩ V i ∩ V j`, `τ j = τ i + k` on `S`. -/
structure IsTranslationAtlas (S : Set M) (V : ι → Set M) (τ : ι → M → ℝ) (σ : ι → ℝ → M)
    (J : ι → Set ℝ) : Prop where
  isOpen_V : ∀ i, IsOpen (V i)
  isOpen_J : ∀ i, IsOpen (J i)
  continuousOn_τ : ∀ i, ContinuousOn (τ i) (S ∩ V i)
  continuousOn_σ : ∀ i, ContinuousOn (σ i) (J i)
  mapsTo_τ : ∀ i, MapsTo (τ i) (S ∩ V i) (J i)
  mapsTo_σ : ∀ i, MapsTo (σ i) (J i) (S ∩ V i)
  σ_τ : ∀ i, ∀ x ∈ S ∩ V i, σ i (τ i x) = x
  τ_σ : ∀ i, ∀ r ∈ J i, τ i (σ i r) = r
  cover : ∀ p ∈ S, ∃ i, p ∈ V i
  trans : ∀ i j, ∀ x ∈ S ∩ V i ∩ V j, ∃ k : ℝ, ∀ᶠ y in 𝓝 x, y ∈ S → τ j y = τ i y + k

/-- **A development of `S` through `p`**: a continuous `γ : ℝ → M` with `γ 0 = p`, onto the
component of `S` through `p`, locally an increasing reparametrisation of the inverse charts, the
image of every interval about `t` a neighbourhood of `γ t` in `S`, with no limit at `±∞`. -/
structure IsLineDevelopment (S : Set M) (V : ι → Set M) (σ : ι → ℝ → M) (J : ι → Set ℝ) (p : M)
    (γ : ℝ → M) : Prop where
  zero : γ 0 = p
  continuous : Continuous γ
  range_eq : range γ = connectedComponentIn S p
  local_param : ∀ t i, γ t ∈ V i → ∃ ε > 0, ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ Continuous ψ ∧
    ∀ s ∈ Ioo (t - ε) (t + ε), ψ s ∈ J i ∧ γ s = σ i (ψ s)
  local_onto : ∀ t, ∀ ε > 0, ∃ W : Set M, IsOpen W ∧ γ t ∈ W ∧ S ∩ W ⊆ γ '' Ioo (t - ε) (t + ε)
  not_tendsto_atTop : ∀ x, ¬ Tendsto γ atTop (𝓝 x)
  not_tendsto_atBot : ∀ x, ¬ Tendsto γ atBot (𝓝 x)

/-! ### Line arcs -/

section Arcs

variable {S : Set M} {V : ι → Set M} {τ : ι → M → ℝ} {σ : ι → ℝ → M} {J : ι → Set ℝ}

/-- A **line arc** over `I`: a map with values in `S` which, in every chart at `c t`, is the
unit-speed translate `r ↦ τ⁻¹(τ (c t) + (r - t))` near `t`. -/
def IsLineArc (S : Set M) (V : ι → Set M) (τ : ι → M → ℝ) (I : Set ℝ) (c : ℝ → M) : Prop :=
  ∀ t ∈ I, c t ∈ S ∧ ∀ i, c t ∈ V i →
    ∀ᶠ r in 𝓝 t, c r ∈ S ∧ c r ∈ V i ∧ τ i (c r) = τ i (c t) + (r - t)

omit [TopologicalSpace M] in
theorem IsLineArc.mono {I I' : Set ℝ} {c : ℝ → M} (hc : IsLineArc S V τ I c) (h : I' ⊆ I) :
    IsLineArc S V τ I' c := fun t ht => hc t (h ht)

omit [TopologicalSpace M] in
theorem IsLineArc.union {I I' : Set ℝ} {c : ℝ → M} (hc : IsLineArc S V τ I c)
    (hc' : IsLineArc S V τ I' c) : IsLineArc S V τ (I ∪ I') c := fun t ht =>
  ht.elim (hc t) (hc' t)

omit [TopologicalSpace M] in
/-- A line arc over an open set depends only on its values there. -/
theorem IsLineArc.congr {I : Set ℝ} {c d : ℝ → M} (hc : IsLineArc S V τ I c) (hI : IsOpen I)
    (h : EqOn c d I) : IsLineArc S V τ I d := by
  intro t ht
  have hev : ∀ᶠ r in 𝓝 t, c r = d r :=
    Filter.mem_of_superset (hI.mem_nhds ht) fun r hr => h hr
  obtain ⟨hS, hloc⟩ := hc t ht
  refine ⟨h ht ▸ hS, fun i hi => ?_⟩
  rw [← h ht] at hi ⊢
  filter_upwards [hloc i hi, hev] with r hr hcd
  rw [← hcd]
  exact hr

omit [TopologicalSpace M] in
/-- A translate of a line arc is a line arc. -/
theorem IsLineArc.comp_add {I : Set ℝ} {c : ℝ → M} (hc : IsLineArc S V τ I c) (d : ℝ) :
    IsLineArc S V τ ((· + d) ⁻¹' I) (fun r => c (r + d)) := by
  intro t ht
  obtain ⟨hS, hloc⟩ := hc (t + d) ht
  refine ⟨hS, fun i hi => ?_⟩
  have hT : Tendsto (fun r : ℝ => r + d) (𝓝 t) (𝓝 (t + d)) := (continuous_add_const d).tendsto t
  filter_upwards [hT.eventually (hloc i hi)] with r hr
  refine ⟨hr.1, hr.2.1, ?_⟩
  rw [hr.2.2]
  ring

variable (hA : IsTranslationAtlas S V τ σ J)
include hA

/-- Near `t`, a line arc is the inverse chart at `c t`, translated. -/
theorem IsLineArc.eventually_eq_σ {I : Set ℝ} {c : ℝ → M} (hc : IsLineArc S V τ I c) {t : ℝ}
    (ht : t ∈ I) {i : ι} (hi : c t ∈ V i) :
    ∀ᶠ r in 𝓝 t, c r = σ i (τ i (c t) + (r - t)) := by
  filter_upwards [(hc t ht).2 i hi] with r hr
  rw [← hr.2.2]
  exact (hA.σ_τ i (c r) ⟨hr.1, hr.2.1⟩).symm

/-- A line arc is continuous at every point of its domain. -/
theorem IsLineArc.continuousAt {I : Set ℝ} {c : ℝ → M} (hc : IsLineArc S V τ I c) {t : ℝ}
    (ht : t ∈ I) : ContinuousAt c t := by
  obtain ⟨i, hi⟩ := hA.cover (c t) (hc t ht).1
  have hJ : τ i (c t) ∈ J i := hA.mapsTo_τ i ⟨(hc t ht).1, hi⟩
  have hσ : ContinuousAt (σ i) (τ i (c t) + (t - t)) := by
    rw [sub_self, add_zero]
    exact (hA.continuousOn_σ i).continuousAt ((hA.isOpen_J i).mem_nhds hJ)
  have hf : ContinuousAt (fun r : ℝ => τ i (c t) + (r - t)) t := by fun_prop
  have h1 : ContinuousAt (fun r => σ i (τ i (c t) + (r - t))) t :=
    ContinuousAt.comp (f := fun r : ℝ => τ i (c t) + (r - t)) hσ hf
  have hev : c =ᶠ[𝓝 t] (fun r => σ i (τ i (c t) + (r - t))) := hc.eventually_eq_σ hA ht hi
  exact h1.congr hev.symm

/-- Two line arcs through one point at one parameter agree near it. -/
theorem IsLineArc.eventuallyEq {I I' : Set ℝ} {c c' : ℝ → M} (hc : IsLineArc S V τ I c)
    (hc' : IsLineArc S V τ I' c') {t : ℝ} (ht : t ∈ I) (ht' : t ∈ I') (h : c t = c' t) :
    c =ᶠ[𝓝 t] c' := by
  obtain ⟨i, hi⟩ := hA.cover (c t) (hc t ht).1
  have hi' : c' t ∈ V i := h ▸ hi
  filter_upwards [hc.eventually_eq_σ hA ht hi, hc'.eventually_eq_σ hA ht' hi'] with r h1 h2
  rw [h1, h2, h]

/-- **Uniqueness of line arcs** (step (2)): two line arcs, equal at one parameter, agree on any
preconnected part of the intersection of their domains containing it. -/
theorem IsLineArc.eqOn [T2Space M] {I I' : Set ℝ} {c c' : ℝ → M} (hc : IsLineArc S V τ I c)
    (hc' : IsLineArc S V τ I' c') (hII' : IsPreconnected (I ∩ I')) {t₀ : ℝ}
    (ht₀ : t₀ ∈ I ∩ I') (h : c t₀ = c' t₀) : EqOn c c' (I ∩ I') := by
  set u : Set ℝ := {t | ∀ᶠ r in 𝓝 t, c r = c' r} with hu_def
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hsub : I ∩ I' ⊆ u := by
    refine hII'.subset_of_closure_inter_subset hu
      ⟨t₀, ht₀, hc.eventuallyEq hA hc' ht₀.1 ht₀.2 h⟩ ?_
    rintro t ⟨htcl, htI, htI'⟩
    haveI hne : (𝓝[u] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htcl
    have h1 : Tendsto c (𝓝[u] t) (𝓝 (c t)) :=
      (hc.continuousAt hA htI).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto c' (𝓝[u] t) (𝓝 (c' t)) :=
      (hc'.continuousAt hA htI').tendsto.mono_left nhdsWithin_le_nhds
    have h3 : c =ᶠ[𝓝[u] t] c' := eventually_nhdsWithin_of_forall fun r hr => hr.self_of_nhds
    have : c t = c' t := tendsto_nhds_unique (h1.congr' h3) h2
    exact hc.eventuallyEq hA hc' htI htI' this
  intro t ht
  exact (hsub ht).self_of_nhds

/-- An inverse chart, translated, is a line arc (step (1)). -/
theorem isLineArc_σ (i : ι) (b : ℝ) :
    IsLineArc S V τ {r | b + r ∈ J i} (fun r => σ i (b + r)) := by
  intro r hr
  have hmem : σ i (b + r) ∈ S ∩ V i := hA.mapsTo_σ i hr
  refine ⟨hmem.1, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := hA.trans i j _ ⟨hmem, hj⟩
  have hcont : ContinuousAt (fun r' => σ i (b + r')) r :=
    ((hA.continuousOn_σ i).continuousAt ((hA.isOpen_J i).mem_nhds hr)).comp
      (continuousAt_const.add continuousAt_id)
  have hJ : ∀ᶠ r' in 𝓝 r, b + r' ∈ J i :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      ((hA.isOpen_J i).mem_nhds hr)
  have hk0 : τ j (σ i (b + r)) = τ i (σ i (b + r)) + k := hk.self_of_nhds hmem.1
  filter_upwards [hJ, Tendsto.eventually hcont hk,
    hcont.preimage_mem_nhds ((hA.isOpen_V j).mem_nhds hj)] with r' h1 h2 h3
  have hm' : σ i (b + r') ∈ S ∩ V i := hA.mapsTo_σ i h1
  refine ⟨hm'.1, h3, ?_⟩
  rw [h2 hm'.1, hk0, hA.τ_σ i _ h1, hA.τ_σ i _ hr]
  ring

/-- The image of a chart about `x` is a neighbourhood of `x` in `S`. -/
theorem exists_nhds_param {x : M} {i : ι} (hx : x ∈ S ∩ V i) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ S ∩ W, ∃ r ∈ Ioo (-δ) δ, y = σ i (τ i x + r) := by
  have hmem : τ i ⁻¹' Ioo (τ i x - δ) (τ i x + δ) ∈ 𝓝[S ∩ V i] x :=
    (hA.continuousOn_τ i) x hx (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.1 hmem
  refine ⟨O ∩ V i, hO.inter (hA.isOpen_V i), ⟨hxO, hx.2⟩, fun y hy => ?_⟩
  have hy' : y ∈ S ∩ V i := ⟨hy.1, hy.2.2⟩
  have h1 : τ i y ∈ Ioo (τ i x - δ) (τ i x + δ) := hOsub ⟨hy.2.1, hy'⟩
  refine ⟨τ i y - τ i x, ⟨by linarith [h1.1], by linarith [h1.2]⟩, ?_⟩
  rw [show τ i x + (τ i y - τ i x) = τ i y by ring, hA.σ_τ i y hy']

/-- A chart about a point of `S` contains a ball about its coordinate. -/
theorem exists_Ioo_subset {x : M} {i : ι} (hx : x ∈ S ∩ V i) :
    ∃ δ > 0, Ioo (τ i x - δ) (τ i x + δ) ⊆ J i := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hA.isOpen_J i) _ (hA.mapsTo_τ i hx)
  refine ⟨δ, hδ, fun r hr => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hr.1, hr.2]

end Arcs

/-! ### The maximal arc -/

section Maximal

variable {S : Set M} {V : ι → Set M} {τ : ι → M → ℝ} {σ : ι → ℝ → M} {J : ι → Set ℝ}

variable (S V τ) in
/-- The line arcs through `p` at `0`, over open preconnected sets. -/
def arcs (p : M) : Set (Set ℝ × (ℝ → M)) :=
  {Ic | IsOpen Ic.1 ∧ IsPreconnected Ic.1 ∧ (0 : ℝ) ∈ Ic.1 ∧ Ic.2 0 = p ∧
    IsLineArc S V τ Ic.1 Ic.2}

variable (S V τ) in
/-- The domain of the maximal arc: the union of the domains of the arcs. -/
def domain (p : M) : Set ℝ := ⋃₀ (Prod.fst '' arcs S V τ p)

open Classical in
variable (S V τ) in
/-- **The maximal arc** through `p` (step (3)). -/
noncomputable def dev (p : M) (t : ℝ) : M :=
  if h : ∃ Ic ∈ arcs S V τ p, t ∈ Ic.1 then h.choose.2 t else p

omit [TopologicalSpace M] in
theorem mem_domain_iff {p : M} {t : ℝ} :
    t ∈ domain S V τ p ↔ ∃ Ic ∈ arcs S V τ p, t ∈ Ic.1 := by
  simp only [domain, mem_sUnion, mem_image]
  constructor
  · rintro ⟨_, ⟨Ic, hIc, rfl⟩, ht⟩
    exact ⟨Ic, hIc, ht⟩
  · rintro ⟨Ic, hIc, ht⟩
    exact ⟨_, ⟨Ic, hIc, rfl⟩, ht⟩

omit [TopologicalSpace M] in
theorem isOpen_domain {p : M} : IsOpen (domain S V τ p) :=
  isOpen_sUnion (by rintro _ ⟨Ic, hIc, rfl⟩; exact hIc.1)

omit [TopologicalSpace M] in
theorem isPreconnected_domain {p : M} : IsPreconnected (domain S V τ p) :=
  isPreconnected_sUnion 0 _ (by rintro _ ⟨Ic, hIc, rfl⟩; exact hIc.2.2.1)
    (by rintro _ ⟨Ic, hIc, rfl⟩; exact hIc.2.1)

omit [TopologicalSpace M] in
theorem isPreconnected_inter {I I' : Set ℝ} (hI : IsPreconnected I) (hI' : IsPreconnected I') :
    IsPreconnected (I ∩ I') :=
  isPreconnected_iff_ordConnected.2
    ((isPreconnected_iff_ordConnected.1 hI).inter (isPreconnected_iff_ordConnected.1 hI'))

variable (hA : IsTranslationAtlas S V τ σ J)
include hA

theorem dev_eq [T2Space M] {p : M} {Ic : Set ℝ × (ℝ → M)} (hIc : Ic ∈ arcs S V τ p) {t : ℝ}
    (ht : t ∈ Ic.1) : dev S V τ p t = Ic.2 t := by
  have h : ∃ Ic ∈ arcs S V τ p, t ∈ Ic.1 := ⟨Ic, hIc, ht⟩
  rw [dev, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact h1.2.2.2.2.eqOn hA hIc.2.2.2.2 (isPreconnected_inter h1.2.1 hIc.2.1)
    ⟨h1.2.2.1, hIc.2.2.1⟩ (h1.2.2.2.1.trans hIc.2.2.2.1.symm) ⟨h2, ht⟩

theorem exists_arc {p : M} (hp : p ∈ S) : (arcs S V τ p).Nonempty := by
  obtain ⟨i, hi⟩ := hA.cover p hp
  obtain ⟨δ, hδ, hball⟩ := exists_Ioo_subset hA ⟨hp, hi⟩
  refine ⟨(Ioo (-δ) δ, fun r => σ i (τ i p + r)), isOpen_Ioo, isPreconnected_Ioo,
    ⟨by linarith, hδ⟩, ?_, ?_⟩
  · simp only [add_zero]
    exact hA.σ_τ i p ⟨hp, hi⟩
  · refine (isLineArc_σ hA i (τ i p)).mono fun r hr => hball ?_
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

theorem zero_mem_domain {p : M} (hp : p ∈ S) : (0 : ℝ) ∈ domain S V τ p := by
  obtain ⟨Ic, hIc⟩ := exists_arc hA hp
  exact mem_domain_iff.2 ⟨Ic, hIc, hIc.2.2.1⟩

theorem dev_zero [T2Space M] {p : M} (hp : p ∈ S) : dev S V τ p 0 = p := by
  obtain ⟨Ic, hIc⟩ := exists_arc hA hp
  rw [dev_eq hA hIc hIc.2.2.1]
  exact hIc.2.2.2.1

theorem isLineArc_dev [T2Space M] {p : M} : IsLineArc S V τ (domain S V τ p) (dev S V τ p) := by
  intro t ht
  obtain ⟨Ic, hIc, htI⟩ := mem_domain_iff.1 ht
  exact hIc.2.2.2.2.congr hIc.1 (fun r hr => (dev_eq hA hIc hr).symm) t htI

/-- **Continuation** (steps (4)–(5)): if the maximal arc meets the parametrised neighbourhood
`σ i (b + ·)` of `(-δ, δ)` at `s`, it runs through the whole of it. -/
theorem dev_continue [T2Space M] {p : M} (hp : p ∈ S) {i : ι} {b δ : ℝ}
    (hδ : Ioo (b - δ) (b + δ) ⊆ J i) {s r₁ : ℝ} (hs : s ∈ domain S V τ p)
    (hr₁ : r₁ ∈ Ioo (-δ) δ) (hsr : dev S V τ p s = σ i (b + r₁)) {r : ℝ} (hr : r ∈ Ioo (-δ) δ) :
    s - r₁ + r ∈ domain S V τ p ∧ dev S V τ p (s - r₁ + r) = σ i (b + r) := by
  classical
  set D := domain S V τ p with hD_def
  set v : ℝ → M := fun t => σ i (b + (t + (r₁ - s))) with hv_def
  set K : Set ℝ := Ioo (s - r₁ - δ) (s - r₁ + δ) with hK_def
  have hv : IsLineArc S V τ K v := by
    refine ((isLineArc_σ hA i b).comp_add (r₁ - s)).mono ?_
    intro t ht
    show b + (t + (r₁ - s)) ∈ J i
    exact hδ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsK : s ∈ K := ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩
  have hvs : v s = dev S V τ p s := by
    rw [hsr]
    show σ i (b + (s + (r₁ - s))) = σ i (b + r₁)
    congr 1
    ring
  have hdev : IsLineArc S V τ D (dev S V τ p) := isLineArc_dev hA
  have heq : EqOn (dev S V τ p) v (D ∩ K) :=
    hdev.eqOn hA hv (isPreconnected_inter isPreconnected_domain isPreconnected_Ioo) ⟨hs, hsK⟩
      hvs.symm
  set g : ℝ → M := fun t => if t ∈ D then dev S V τ p t else v t with hg_def
  have hg : IsLineArc S V τ (D ∪ K) g := by
    refine IsLineArc.union (hdev.congr isOpen_domain fun t ht => ?_)
      (hv.congr isOpen_Ioo fun t ht => ?_)
    · simp only [hg_def, if_pos ht]
    · by_cases htD : t ∈ D
      · simp only [hg_def, if_pos htD]
        exact (heq ⟨htD, ht⟩).symm
      · simp only [hg_def, if_neg htD]
  have h0D : (0 : ℝ) ∈ D := zero_mem_domain hA hp
  have hgarc : (D ∪ K, g) ∈ arcs S V τ p := by
    refine ⟨isOpen_domain.union isOpen_Ioo,
      IsPreconnected.union s hs hsK isPreconnected_domain isPreconnected_Ioo, Or.inl h0D, ?_, hg⟩
    show g 0 = p
    simp only [hg_def, if_pos h0D]
    exact dev_zero hA hp
  have hKD : K ⊆ D := fun t ht => mem_domain_iff.2 ⟨_, hgarc, Or.inr ht⟩
  have ht : s - r₁ + r ∈ K := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨hKD ht, ?_⟩
  rw [heq ⟨hKD ht, ht⟩]
  show σ i (b + (s - r₁ + r + (r₁ - s))) = σ i (b + r)
  congr 1
  ring

/-- The image of every interval about `s` is a neighbourhood of `dev s` in `S`. -/
theorem dev_local_onto [T2Space M] {p : M} (hp : p ∈ S) {s : ℝ} (hs : s ∈ domain S V τ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set M, IsOpen W ∧ dev S V τ p s ∈ W ∧
      S ∩ W ⊆ dev S V τ p '' (Ioo (s - ε) (s + ε) ∩ domain S V τ p) := by
  set x := dev S V τ p s with hx_def
  have hxS : x ∈ S := (isLineArc_dev hA s hs).1
  obtain ⟨i, hi⟩ := hA.cover x hxS
  obtain ⟨δ₀, hδ₀, hball⟩ := exists_Ioo_subset hA ⟨hxS, hi⟩
  set δ := min δ₀ ε with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ hε
  have hδ₁ : δ ≤ δ₀ := min_le_left _ _
  have hδ₂ : δ ≤ ε := min_le_right _ _
  have hδJ : Ioo (τ i x - δ) (τ i x + δ) ⊆ J i :=
    fun r hr => hball ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨W, hW, hxW, hWsub⟩ := exists_nhds_param hA ⟨hxS, hi⟩ hδ
  refine ⟨W, hW, hxW, fun y hy => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hWsub y hy
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hx0 : dev S V τ p s = σ i (τ i x + 0) := by
    rw [add_zero]
    exact (hA.σ_τ i x ⟨hxS, hi⟩).symm
  obtain ⟨h1, h2⟩ := dev_continue hA hp hδJ hs h0 hx0 hr
  refine ⟨s - 0 + r, ⟨⟨?_, ?_⟩, h1⟩, h2⟩ <;> linarith [hr.1, hr.2]

/-- The image of the maximal arc is closed in `S`. -/
theorem mem_image_dev_of_mem_closure [T2Space M] {p : M} (hp : p ∈ S) {x : M} (hx : x ∈ S)
    (hcl : x ∈ closure (dev S V τ p '' domain S V τ p)) :
    x ∈ dev S V τ p '' domain S V τ p := by
  obtain ⟨i, hi⟩ := hA.cover x hx
  obtain ⟨δ, hδ, hδJ⟩ := exists_Ioo_subset hA ⟨hx, hi⟩
  obtain ⟨W, hW, hxW, hWsub⟩ := exists_nhds_param hA ⟨hx, hi⟩ hδ
  obtain ⟨y, hyW, ⟨s, hs, rfl⟩⟩ := mem_closure_iff.1 hcl W hW hxW
  obtain ⟨r₁, hr₁, hsr⟩ := hWsub _ ⟨(isLineArc_dev hA s hs).1, hyW⟩
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  obtain ⟨h1, h2⟩ := dev_continue hA hp hδJ hs hr₁ hsr h0
  exact ⟨_, h1, by rw [h2, add_zero, hA.σ_τ i x ⟨hx, hi⟩]⟩

/-- **No limit at the ends** (step (5)): near any point `x` of `S`, the maximal arc leaves a
neighbourhood of `x` after and before every visit. -/
theorem dev_escape [T2Space M] {p : M} (hp : p ∈ S) {x : M} (hx : x ∈ S) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ s ∈ domain S V τ p, dev S V τ p s ∈ W →
      (∃ s' ∈ domain S V τ p, s < s' ∧ dev S V τ p s' ∉ W) ∧
      (∃ s' ∈ domain S V τ p, s' < s ∧ dev S V τ p s' ∉ W) := by
  obtain ⟨i, hi⟩ := hA.cover x hx
  obtain ⟨δ, hδ, hδJ⟩ := exists_Ioo_subset hA ⟨hx, hi⟩
  obtain ⟨W, hW, hxW, hWsub⟩ := exists_nhds_param hA ⟨hx, hi⟩ (half_pos hδ)
  have hout : ∀ r ∈ Ioo (-δ) δ, σ i (τ i x + r) ∈ W → r ∈ Ioo (-(δ / 2)) (δ / 2) := by
    intro r hr hrW
    have hrJ : τ i x + r ∈ J i := hδJ ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨r₂, hr₂, h⟩ := hWsub _ ⟨(hA.mapsTo_σ i hrJ).1, hrW⟩
    have hr₂J : τ i x + r₂ ∈ J i := hδJ ⟨by linarith [hr₂.1], by linarith [hr₂.2]⟩
    have h' := congrArg (τ i) h
    rw [hA.τ_σ i _ hrJ, hA.τ_σ i _ hr₂J] at h'
    have : r = r₂ := by linarith
    exact this ▸ hr₂
  refine ⟨W, hW, hxW, fun s hs hsW => ?_⟩
  obtain ⟨r₁, hr₁, hsr⟩ := hWsub _ ⟨(isLineArc_dev hA s hs).1, hsW⟩
  have hr₁' : r₁ ∈ Ioo (-δ) δ := ⟨by linarith [hr₁.1], by linarith [hr₁.2]⟩
  constructor
  · obtain ⟨h1, h2⟩ := dev_continue hA hp hδJ hs hr₁' hsr (r := 3 * δ / 4)
      ⟨by linarith, by linarith⟩
    refine ⟨_, h1, by linarith [hr₁.2], fun hW' => ?_⟩
    rw [h2] at hW'
    have := hout _ ⟨by linarith, by linarith⟩ hW'
    linarith [this.2]
  · obtain ⟨h1, h2⟩ := dev_continue hA hp hδJ hs hr₁' hsr (r := -(3 * δ / 4))
      ⟨by linarith, by linarith⟩
    refine ⟨_, h1, by linarith [hr₁.1], fun hW' => ?_⟩
    rw [h2] at hW'
    have := hout _ ⟨by linarith, by linarith⟩ hW'
    linarith [this.1]

/-- **The image of the maximal arc is the component of `S` through `p`** (step (4)). -/
theorem image_dev_eq [T2Space M] {p : M} (hp : p ∈ S) :
    dev S V τ p '' domain S V τ p = connectedComponentIn S p := by
  set A := dev S V τ p '' domain S V τ p with hA_def
  have hAS : A ⊆ S := by
    rintro _ ⟨s, hs, rfl⟩
    exact (isLineArc_dev hA s hs).1
  have hpA : p ∈ A := ⟨0, zero_mem_domain hA hp, dev_zero hA hp⟩
  apply Subset.antisymm
  · have hcont : ContinuousOn (dev S V τ p) (domain S V τ p) := fun t ht =>
      ((isLineArc_dev hA).continuousAt hA ht).continuousWithinAt
    exact (isPreconnected_domain.image _ hcont).subset_connectedComponentIn hpA hAS
  · rw [connectedComponentIn_eq_image hp]
    rintro _ ⟨y, hy, rfl⟩
    have hclopen : IsClopen (((↑) : S → M) ⁻¹' A) := by
      constructor
      · rw [← closure_subset_iff_isClosed]
        intro z hz
        exact mem_image_dev_of_mem_closure hA hp z.2
          (continuous_subtype_val.closure_preimage_subset A hz)
      · rw [isOpen_iff_mem_nhds]
        intro z hz
        obtain ⟨s, hs, hsz⟩ := hz
        obtain ⟨W, hW, hzW, hWsub⟩ := dev_local_onto hA hp hs one_pos
        refine Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds
          (show (z : M) ∈ W from hsz ▸ hzW)) ?_
        intro w hw
        obtain ⟨t, ht, htw⟩ := hWsub ⟨w.2, hw⟩
        exact ⟨t, ht.2, htw⟩
    exact hclopen.connectedComponent_subset (show (⟨p, hp⟩ : S) ∈ _ from hpA) hy

end Maximal

/-! ### Reparametrisation by `ℝ` (step (6)) -/

/-- Every non-empty open interval of `ℝ` is the range of a continuous strictly increasing map
`ℝ → ℝ`, which can be asked to fix `0` when `0` is in the interval. -/
theorem exists_strictMono_range_eq {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    (h0 : (0 : ℝ) ∈ I) :
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ Continuous φ ∧ range φ = I ∧ φ 0 = 0 := by
  have hoc : I.OrdConnected := isPreconnected_iff_ordConnected.1 hIc
  have hne : I.Nonempty := ⟨0, h0⟩
  have hmem : ∀ x, x ∈ I ↔ (∃ y ∈ I, y < x) ∧ (∃ z ∈ I, x < z) := by
    intro x
    constructor
    · intro hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI x hx
      refine ⟨⟨x - ε / 2, hball ?_, by linarith⟩, ⟨x + ε / 2, hball ?_, by linarith⟩⟩ <;>
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] <;> constructor <;> linarith
    · rintro ⟨⟨y, hy, hyx⟩, ⟨z, hz, hxz⟩⟩
      exact hoc.out hy hz ⟨hyx.le, hxz.le⟩
  have hbelow : BddBelow I → ∀ x, (∃ y ∈ I, y < x) ↔ sInf I < x := fun hb x =>
    ⟨fun ⟨_, hy, hyx⟩ => (csInf_le hb hy).trans_lt hyx, fun h => exists_lt_of_csInf_lt hne h⟩
  have habove : BddAbove I → ∀ x, (∃ z ∈ I, x < z) ↔ x < sSup I := fun hb x =>
    ⟨fun ⟨_, hz, hxz⟩ => hxz.trans_le (le_csSup hb hz), fun h => exists_lt_of_lt_csSup hne h⟩
  obtain ⟨φ, hφm, hφc, hφr⟩ : ∃ φ : ℝ → ℝ, StrictMono φ ∧ Continuous φ ∧ range φ = I := by
    by_cases hb : BddBelow I <;> by_cases ha : BddAbove I
    · -- `I = (a, b)`
      have hab : sInf I < sSup I := by
        obtain ⟨h1, h2⟩ := (hmem 0).1 h0
        exact ((hbelow hb 0).1 h1).trans ((habove ha 0).1 h2)
      refine ⟨fun t => sInf I + (sSup I - sInf I) * Real.sigmoid t, fun s t hst => ?_,
        continuous_const.add (continuous_const.mul continuous_sigmoid), ?_⟩
      · have := Real.sigmoid_strictMono hst
        show sInf I + (sSup I - sInf I) * Real.sigmoid s < sInf I + (sSup I - sInf I) * Real.sigmoid t
        nlinarith
      · ext x
        rw [hmem x, hbelow hb, habove ha]
        constructor
        · rintro ⟨t, rfl⟩
          have h1 := Real.sigmoid_pos t
          have h2 := Real.sigmoid_lt_one t
          constructor <;> nlinarith
        · rintro ⟨h1, h2⟩
          have hy : (x - sInf I) / (sSup I - sInf I) ∈ Ioo (0 : ℝ) 1 :=
            ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
          rw [← Real.range_sigmoid] at hy
          obtain ⟨t, ht⟩ := hy
          refine ⟨t, ?_⟩
          show sInf I + (sSup I - sInf I) * Real.sigmoid t = x
          have hne' : sSup I - sInf I ≠ 0 := by linarith
          rw [ht]
          field_simp
          ring
    · -- `I = (a, ∞)`
      refine ⟨fun t => sInf I + Real.exp t, fun s t hst => ?_,
        continuous_const.add Real.continuous_exp, ?_⟩
      · show sInf I + Real.exp s < sInf I + Real.exp t
        linarith [Real.exp_strictMono hst]
      · ext x
        rw [hmem x, hbelow hb]
        have hz : ∃ z ∈ I, x < z := by simpa using not_bddAbove_iff.1 ha x
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨by linarith [Real.exp_pos t], not_bddAbove_iff.1 ha _⟩
        · rintro ⟨h1, -⟩
          refine ⟨Real.log (x - sInf I), ?_⟩
          show sInf I + Real.exp (Real.log (x - sInf I)) = x
          rw [Real.exp_log (by linarith)]
          ring
    · -- `I = (-∞, b)`
      refine ⟨fun t => sSup I - Real.exp (-t), fun s t hst => ?_,
        continuous_const.sub (Real.continuous_exp.comp continuous_neg), ?_⟩
      · show sSup I - Real.exp (-s) < sSup I - Real.exp (-t)
        linarith [Real.exp_strictMono (neg_lt_neg hst)]
      · ext x
        rw [hmem x, habove ha]
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨not_bddBelow_iff.1 hb _, by linarith [Real.exp_pos (-t)]⟩
        · rintro ⟨-, h2⟩
          refine ⟨-Real.log (sSup I - x), ?_⟩
          show sSup I - Real.exp (-(-Real.log (sSup I - x))) = x
          rw [neg_neg, Real.exp_log (by linarith)]
          ring
    · -- `I = ℝ`
      refine ⟨id, strictMono_id, continuous_id, ?_⟩
      ext x
      simp only [mem_range, id, exists_eq, true_iff]
      exact (hmem x).2 ⟨not_bddBelow_iff.1 hb x, not_bddAbove_iff.1 ha x⟩
  obtain ⟨t₀, ht₀⟩ : (0 : ℝ) ∈ range φ := hφr ▸ h0
  refine ⟨fun t => φ (t + t₀), fun s t h => hφm (by linarith), hφc.comp (continuous_add_const t₀),
    ?_, by simp [ht₀]⟩
  rw [← hφr]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - t₀, by simp⟩

/-! ### The development -/

section Development

variable {S : Set M} {V : ι → Set M} {τ : ι → M → ℝ} {σ : ι → ℝ → M} {J : ι → Set ℝ}

/-- **The development of a translation line** (steps (1)–(6)). -/
theorem exists_development [T2Space M] (hS : IsClosed S) (hA : IsTranslationAtlas S V τ σ J)
    {p : M} (hp : p ∈ S) : ∃ γ : ℝ → M, IsLineDevelopment S V σ J p γ := by
  obtain ⟨φ, hφm, hφc, hφr, hφ0⟩ := exists_strictMono_range_eq (I := domain S V τ p)
    isOpen_domain isPreconnected_domain (zero_mem_domain hA hp)
  have hc : IsLineArc S V τ (domain S V τ p) (dev S V τ p) := isLineArc_dev hA
  have hφD : ∀ t, φ t ∈ domain S V τ p := fun t => hφr ▸ mem_range_self t
  refine ⟨dev S V τ p ∘ φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.comp, hφ0, dev_zero hA hp]
  · exact continuous_iff_continuousAt.2 fun t =>
      ContinuousAt.comp (f := φ) (hc.continuousAt hA (hφD t)) hφc.continuousAt
  · rw [range_comp, hφr]
    exact image_dev_eq hA hp
  · -- local form
    intro t i hi
    have hev := (hc (φ t) (hφD t)).2 i hi
    have hev' : ∀ᶠ s in 𝓝 t, dev S V τ p (φ s) ∈ S ∧ dev S V τ p (φ s) ∈ V i ∧
        τ i (dev S V τ p (φ s)) = τ i (dev S V τ p (φ t)) + (φ s - φ t) :=
      Tendsto.eventually hφc.continuousAt hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev'
    refine ⟨ε, hε, fun s => τ i (dev S V τ p (φ t)) + (φ s - φ t), fun s s' h => ?_,
      continuous_const.add (hφc.sub continuous_const), fun s hs => ?_⟩
    · show τ i (dev S V τ p (φ t)) + (φ s - φ t) < τ i (dev S V τ p (φ t)) + (φ s' - φ t)
      linarith [hφm h]
    · have h := hball s (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1, hs.2])
      refine ⟨?_, ?_⟩
      · show τ i (dev S V τ p (φ t)) + (φ s - φ t) ∈ J i
        rw [← h.2.2]
        exact hA.mapsTo_τ i ⟨h.1, h.2.1⟩
      · show dev S V τ p (φ s) = σ i (τ i (dev S V τ p (φ t)) + (φ s - φ t))
        rw [← h.2.2, hA.σ_τ i _ ⟨h.1, h.2.1⟩]
  · -- local surjectivity onto `S`
    intro t ε hε
    have hlt1 : φ (t - ε) < φ t := hφm (by linarith)
    have hlt2 : φ t < φ (t + ε) := hφm (by linarith)
    set ε' := min (φ t - φ (t - ε)) (φ (t + ε) - φ t) with hε'_def
    have hε' : 0 < ε' := lt_min (by linarith) (by linarith)
    have hε'1 : ε' ≤ φ t - φ (t - ε) := min_le_left _ _
    have hε'2 : ε' ≤ φ (t + ε) - φ t := min_le_right _ _
    obtain ⟨W, hW, hxW, hWsub⟩ := dev_local_onto hA hp (hφD t) hε'
    refine ⟨W, hW, hxW, fun y hy => ?_⟩
    obtain ⟨r, ⟨hr, -⟩, rfl⟩ := hWsub hy
    have hr' : r ∈ Ioo (φ (t - ε)) (φ (t + ε)) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨s, hs, hsr⟩ := intermediate_value_Ioo (show t - ε ≤ t + ε by linarith)
      hφc.continuousOn hr'
    exact ⟨s, hs, by simp only [Function.comp, hsr]⟩
  · -- no limit at `+∞`
    intro x hx
    have hxS : x ∈ S := hS.mem_of_tendsto hx (Eventually.of_forall fun t => (hc _ (hφD t)).1)
    obtain ⟨W, hW, hxW, hesc⟩ := dev_escape hA hp hxS
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hx (hW.mem_nhds hxW))
    obtain ⟨⟨s', hs', hlt, hnot⟩, -⟩ := hesc (φ T) (hφD T) (hT T le_rfl)
    obtain ⟨t', rfl⟩ : s' ∈ range φ := hφr ▸ hs'
    exact hnot (hT t' (hφm.lt_iff_lt.1 hlt).le)
  · -- no limit at `-∞`
    intro x hx
    have hxS : x ∈ S := hS.mem_of_tendsto hx (Eventually.of_forall fun t => (hc _ (hφD t)).1)
    obtain ⟨W, hW, hxW, hesc⟩ := dev_escape hA hp hxS
    obtain ⟨T, hT⟩ := eventually_atBot.1 (hx (hW.mem_nhds hxW))
    obtain ⟨-, ⟨s', hs', hlt, hnot⟩⟩ := hesc (φ T) (hφD T) (hT T le_rfl)
    obtain ⟨t', rfl⟩ : s' ∈ range φ := hφr ▸ hs'
    exact hnot (hT t' (hφm.lt_iff_lt.1 hlt).le)

theorem IsLineDevelopment.mem {p : M} {γ : ℝ → M} (hγ : IsLineDevelopment S V σ J p γ) (t : ℝ) :
    γ t ∈ S :=
  connectedComponentIn_subset S p (hγ.range_eq ▸ mem_range_self t)

/-- A development is locally injective. -/
theorem IsLineDevelopment.locallyInjective (hA : IsTranslationAtlas S V τ σ J) {p : M}
    {γ : ℝ → M} (hγ : IsLineDevelopment S V σ J p γ) (t : ℝ) :
    ∃ ε > 0, InjOn γ (Ioo (t - ε) (t + ε)) := by
  obtain ⟨i, hi⟩ := hA.cover (γ t) (hγ.mem t)
  obtain ⟨ε, hε, ψ, hψm, -, hψ⟩ := hγ.local_param t i hi
  refine ⟨ε, hε, fun s hs s' hs' h => hψm.injective ?_⟩
  have h1 := congrArg (τ i) ((hψ s hs).2.symm.trans (h.trans (hψ s' hs').2))
  rwa [hA.τ_σ i _ (hψ s hs).1, hA.τ_σ i _ (hψ s' hs').1] at h1

/-- The range of a development is closed in `M` when `S` is. -/
theorem IsLineDevelopment.isClosed_range (hS : IsClosed S) {p : M} {γ : ℝ → M}
    (hγ : IsLineDevelopment S V σ J p γ) : IsClosed (range γ) := by
  rw [hγ.range_eq]
  refine isClosed_of_closure_subset ?_
  have hp : p ∈ connectedComponentIn S p := hγ.range_eq ▸ ⟨0, hγ.zero⟩
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure hp) (closure_minimal (connectedComponentIn_subset _ _) hS)

/-- **An injective development is a closed embedding** (step (7)). -/
theorem IsLineDevelopment.isClosedEmbedding (hS : IsClosed S) {p : M} {γ : ℝ → M}
    (hγ : IsLineDevelopment S V σ J p γ) (hinj : Injective γ) : IsClosedEmbedding γ := by
  refine ⟨⟨isInducing_iff_nhds.2 fun t => ?_, hinj⟩, hγ.isClosed_range hS⟩
  refine le_antisymm (hγ.continuous.tendsto t).le_comap fun U hU => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨W, hW, htW, hWsub⟩ := hγ.local_onto t ε hε
  refine mem_comap.2 ⟨W, hW.mem_nhds htW, fun s hs => hball ?_⟩
  obtain ⟨s', hs', heq⟩ := hWsub ⟨hγ.mem s, hs⟩
  rw [← hinj heq, Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs'.1, hs'.2]

end Development

/-! ### Curves are local in the parameter (step (8)) -/

theorem curveOn_of_local {r : Opens M → M → M → Prop} {W : Opens M} {c : ℝ → M} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, ∃ l u, l < t ∧ t < u ∧ CurveOn r W c l u) : CurveOn r W c a b where
  mem t ht := by
    obtain ⟨l, u, hl, hu, hc⟩ := h t ht
    exact hc.mem t ⟨hl.le, hu.le⟩
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hc⟩ := h t ht
    obtain ⟨l', u', hl', hu', hrel⟩ := hc.rel t ⟨hl.le, hu.le⟩ N hN htN
    refine ⟨max l l', min u u', max_lt hl hl', lt_min hu hu', fun s _ s' _ h1 h2 h3 => ?_⟩
    exact hrel s ⟨(le_max_left _ _).trans h1.le, (h2.trans h3).le.trans (min_le_left _ _)⟩ s'
      ⟨((le_max_left _ _).trans_lt (h1.trans h2)).le, h3.le.trans (min_le_left _ _)⟩
      ((le_max_right _ _).trans_lt h1) h2 (h3.trans_le (min_le_right _ _))

theorem causalCurveIn_univ_of_local {C : Causality M} {W : Opens M} {c : ℝ → M}
    (h : ∀ t, ∃ ε > 0, C.CausalCurveOn W c (t - ε) (t + ε)) : C.CausalCurveIn W univ c := by
  refine ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => curveOn_of_local fun t _ => ?_⟩
  obtain ⟨ε, hε, hc⟩ := h t
  exact ⟨t - ε, t + ε, by linarith, by linarith, hc⟩

theorem chronalCurveOn_of_local {C : Causality M} {W : Opens M} {c : ℝ → M}
    (h : ∀ t, ∃ ε > 0, C.ChronalCurveOn W c (t - ε) (t + ε)) (a b : ℝ) :
    C.ChronalCurveOn W c a b := by
  refine curveOn_of_local fun t _ => ?_
  obtain ⟨ε, hε, hc⟩ := h t
  exact ⟨t - ε, t + ε, by linarith, by linarith, hc⟩

/-! ### No limit at the ends gives inextensibility (step (9)) -/

theorem futureInextensible_of_not_tendsto_atTop {C : Causality M} {W : Opens M} {c : ℝ → M}
    (hc : C.CausalCurveIn W univ c) (h : ∀ x ∈ W, ¬ Tendsto c atTop (𝓝 x)) :
    C.FutureInextensible W univ c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨ψ, hψ, hψmaps, -, hψeq, hinit⟩, ⟨t', ht', hgrow⟩⟩
  have hmono : Monotone ψ := (strictMonoOn_univ.1 hψ).monotone
  -- the new parameter `t'` lies above `ψ(ℝ)`, an initial segment of `I'`
  have habove : ∀ s, ψ s < t' := by
    intro s
    by_contra hle
    obtain ⟨s₀, -, hs₀⟩ := hinit s trivial t' ht' (not_lt.1 hle)
    exact hgrow s₀ trivial (by rw [← hs₀]; exact hψeq s₀ trivial)
  have hbdd : BddAbove (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (habove s).le⟩
  set β := ⨆ s, ψ s with hβ_def
  have hβ : Tendsto ψ atTop (𝓝 β) := tendsto_atTop_ciSup hmono hbdd
  have hβt : β ≤ t' := ciSup_le fun s => (habove s).le
  have hβ0 : ψ 0 ≤ β := le_ciSup hbdd 0
  have hcont := (hcurve.curve (ψ 0) (hψmaps (mem_univ 0)) t' ht').continuousOn
    C.isRelFamily_le
  have hβmem : β ∈ Icc (ψ 0) t' := ⟨hβ0, hβt⟩
  have hev : ∀ᶠ s in atTop, ψ s ∈ Icc (ψ 0) t' :=
    eventually_atTop.2 ⟨0, fun s hs => ⟨hmono hs, (habove s).le⟩⟩
  have hlim : Tendsto c atTop (𝓝 (c' β)) := by
    have := (hcont β hβmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hβ, hev⟩)
    exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]
  exact h _ (hcurve.mem (hcurve.ordConnected.out (hψmaps (mem_univ 0)) ht' hβmem)) hlim

theorem pastInextensible_of_not_tendsto_atBot {C : Causality M} {W : Opens M} {c : ℝ → M}
    (hc : C.CausalCurveIn W univ c) (h : ∀ x ∈ W, ¬ Tendsto c atBot (𝓝 x)) :
    C.PastInextensible W univ c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨ψ, hψ, hψmaps, -, hψeq, hfin⟩, ⟨t', ht', hgrow⟩⟩
  have hmono : Monotone ψ := (strictMonoOn_univ.1 hψ).monotone
  -- the new parameter `t'` lies below `ψ(ℝ)`, a final segment of `I'`
  have hbelow : ∀ s, t' < ψ s := by
    intro s
    by_contra hle
    obtain ⟨s₀, -, hs₀⟩ := hfin s trivial t' ht' (not_lt.1 hle)
    exact hgrow s₀ trivial (by rw [← hs₀]; exact hψeq s₀ trivial)
  have hbdd : BddBelow (range ψ) := ⟨t', by rintro _ ⟨s, rfl⟩; exact (hbelow s).le⟩
  set β := ⨅ s, ψ s with hβ_def
  have hβ : Tendsto ψ atBot (𝓝 β) := tendsto_atBot_ciInf hmono hbdd
  have hβt : t' ≤ β := le_ciInf fun s => (hbelow s).le
  have hβ0 : β ≤ ψ 0 := ciInf_le hbdd 0
  have hcont := (hcurve.curve t' ht' (ψ 0) (hψmaps (mem_univ 0))).continuousOn
    C.isRelFamily_le
  have hβmem : β ∈ Icc t' (ψ 0) := ⟨hβt, hβ0⟩
  have hev : ∀ᶠ s in atBot, ψ s ∈ Icc t' (ψ 0) :=
    eventually_atBot.2 ⟨0, fun s hs => ⟨(hbelow s).le, hmono hs⟩⟩
  have hlim : Tendsto c atBot (𝓝 (c' β)) := by
    have := (hcont β hβmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hβ, hev⟩)
    exact this.congr fun s => by simp only [Function.comp, hψeq s trivial]
  exact h _ (hcurve.mem (hcurve.ordConnected.out ht' (hψmaps (mem_univ 0)) hβmem)) hlim

/-- **A causal curve over `ℝ` with no limit at `±∞` is inextensible** (step (9)): the argument
of `Causality.inextensible_of_flow` (`Causal/Splitting.lean`) with the flow removed. -/
theorem inextensible_of_not_tendsto {C : Causality M} {W : Opens M} {c : ℝ → M}
    (hc : C.CausalCurveIn W univ c) (htop : ∀ x ∈ W, ¬ Tendsto c atTop (𝓝 x))
    (hbot : ∀ x ∈ W, ¬ Tendsto c atBot (𝓝 x)) : C.Inextensible W univ c :=
  Causality.inextensible_iff.2 ⟨pastInextensible_of_not_tendsto_atBot hc hbot,
    futureInextensible_of_not_tendsto_atTop hc htop⟩

/-- In a causal spacetime, a locally injective causal curve over `ℝ` is injective. -/
theorem injective_of_isCausal {C : Causality M} {c : ℝ → M} (hcaus : C.IsCausal)
    (hc : ∀ a b, C.CausalCurveOn ⊤ c a b) (hloc : ∀ t, ∃ ε > 0, InjOn c (Ioo (t - ε) (t + ε))) :
    Injective c := by
  have key : ∀ s s', s < s' → c s ≠ c s' := by
    intro s s' hlt h
    have hconst : ∀ r ∈ Icc s s', c r = c s := by
      intro r hr
      have h1 : C.le ⊤ (c s) (c r) := (hc s s').le_of_le le_rfl hr.1 hr.2
      have h2 : C.le ⊤ (c r) (c s') := (hc s s').le_of_le hr.1 hr.2 le_rfl
      rw [← h] at h2
      exact hcaus h2 h1
    obtain ⟨ε, hε, hinj⟩ := hloc s
    have hr1 : s < min (s + ε / 2) s' := lt_min (by linarith) hlt
    have hr2 : min (s + ε / 2) s' ≤ s' := min_le_right _ _
    have hr3 : min (s + ε / 2) s' ≤ s + ε / 2 := min_le_left _ _
    have := hinj ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (hconst _ ⟨hr1.le, hr2⟩).symm
    linarith
  intro s s' h
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact absurd h (key s s' hlt)
  · exact heq
  · exact absurd h.symm (key s' s hgt)

/-! ### The fields `BTZAxioms.line` and `SingularFlatAxioms.massive_line`, abstractly -/

section Fields

variable {S : Set M} {V : ι → Set M} {τ : ι → M → ℝ} {σ : ι → ℝ → M} {J : ι → Set ℝ}

/-- A development whose inverse charts are causal curves is a causal curve over every
segment. -/
theorem IsLineDevelopment.causalCurveOn {C : Causality M} {p : M} {γ : ℝ → M}
    (hγ : IsLineDevelopment S V σ J p γ) (hA : IsTranslationAtlas S V τ σ J)
    (hσ : ∀ i a b, Icc a b ⊆ J i → C.CausalCurveOn ⊤ (σ i) a b) (a b : ℝ) :
    C.CausalCurveOn ⊤ γ a b := by
  refine curveOn_of_local fun t _ => ?_
  obtain ⟨i, hi⟩ := hA.cover (γ t) (hγ.mem t)
  obtain ⟨ε, hε, ψ, hψm, hψc, hψ⟩ := hγ.local_param t i hi
  refine ⟨t - ε / 2, t + ε / 2, by linarith, by linarith, ?_⟩
  have hsub : Icc (ψ (t - ε / 2)) (ψ (t + ε / 2)) ⊆ J i := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ :=
      intermediate_value_Icc (show t - ε / 2 ≤ t + ε / 2 by linarith) hψc.continuousOn hy
    exact (hψ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have h1 := CurveOn.comp_strictMonoOn (hσ i _ _ hsub) (hψm.strictMonoOn _) hψc.continuousOn
  exact h1.congr fun s hs => ((hψ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).2).symm

theorem IsLineDevelopment.chronalCurveOn {C : Causality M} {p : M} {γ : ℝ → M}
    (hγ : IsLineDevelopment S V σ J p γ) (hA : IsTranslationAtlas S V τ σ J)
    (hσ : ∀ i a b, Icc a b ⊆ J i → C.ChronalCurveOn ⊤ (σ i) a b) (a b : ℝ) :
    C.ChronalCurveOn ⊤ γ a b := by
  refine curveOn_of_local fun t _ => ?_
  obtain ⟨i, hi⟩ := hA.cover (γ t) (hγ.mem t)
  obtain ⟨ε, hε, ψ, hψm, hψc, hψ⟩ := hγ.local_param t i hi
  refine ⟨t - ε / 2, t + ε / 2, by linarith, by linarith, ?_⟩
  have hsub : Icc (ψ (t - ε / 2)) (ψ (t + ε / 2)) ⊆ J i := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ :=
      intermediate_value_Icc (show t - ε / 2 ≤ t + ε / 2 by linarith) hψc.continuousOn hy
    exact (hψ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have h1 := CurveOn.comp_strictMonoOn (hσ i _ _ hsub) (hψm.strictMonoOn _) hψc.continuousOn
  exact h1.congr fun s hs => ((hψ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).2).symm

/-- **The shape of `BTZAxioms.line`**: from a translation atlas of the closed set `S` whose
inverse charts are causal curves. -/
theorem exists_line [T2Space M] {C : Causality M} (hS : IsClosed S)
    (hA : IsTranslationAtlas S V τ σ J)
    (hσ : ∀ i a b, Icc a b ⊆ J i → C.CausalCurveOn ⊤ (σ i) a b) {p : M} (hp : p ∈ S) :
    ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧ C.Inextensible ⊤ univ γ ∧
      range γ = connectedComponentIn S p := by
  obtain ⟨γ, hγ⟩ := exists_development hS hA hp
  have hcurve := hγ.causalCurveOn hA hσ
  have hcin : C.CausalCurveIn ⊤ univ γ :=
    ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => hcurve a b⟩
  exact ⟨γ, hγ.zero, fun hcaus => hγ.isClosedEmbedding hS
      (injective_of_isCausal hcaus hcurve (hγ.locallyInjective hA)),
    inextensible_of_not_tendsto hcin (fun x _ => hγ.not_tendsto_atTop x)
      (fun x _ => hγ.not_tendsto_atBot x), hγ.range_eq⟩

/-- **The shape of `SingularFlatAxioms.massive_line`**: chronal inverse charts. -/
theorem exists_chronal_line [T2Space M] {C : Causality M} (hS : IsClosed S)
    (hA : IsTranslationAtlas S V τ σ J)
    (hσ : ∀ i a b, Icc a b ⊆ J i → C.ChronalCurveOn ⊤ (σ i) a b) {p : M} (hp : p ∈ S) :
    ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧ C.Inextensible ⊤ univ γ ∧
      (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧ range γ = connectedComponentIn S p := by
  obtain ⟨γ, hγ⟩ := exists_development hS hA hp
  have hchron := hγ.chronalCurveOn hA hσ
  have hcurve : ∀ a b, C.CausalCurveOn ⊤ γ a b := fun a b => (hchron a b).causalCurveOn
  have hcin : C.CausalCurveIn ⊤ univ γ :=
    ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => hcurve a b⟩
  exact ⟨γ, hγ.zero, fun hcaus => hγ.isClosedEmbedding hS
      (injective_of_isCausal hcaus hcurve (hγ.locallyInjective hA)),
    inextensible_of_not_tendsto hcin (fun x _ => hγ.not_tendsto_atTop x)
      (fun x _ => hγ.not_tendsto_atBot x), hchron, hγ.range_eq⟩

end Fields

/-! ### Witnesses -/

section Witnesses

/-- The timelike line's one-chart translation atlas. -/
theorem timeline_isTranslationAtlas :
    IsTranslationAtlas (univ : Set ℝ) (fun _ : Unit => univ) (fun _ => id) (fun _ => id)
      (fun _ => univ) :=
  ⟨fun _ => isOpen_univ, fun _ => isOpen_univ, fun _ => continuousOn_id, fun _ => continuousOn_id,
    fun _ _ _ => trivial, fun _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => ⟨0, Eventually.of_forall fun _ _ => by simp⟩⟩

/-- **The timelike line**: the hypotheses of `exists_line` hold, with `S = ℝ`. -/
theorem timelikeLine_line (p : ℝ) :
    ∃ γ : ℝ → ℝ, γ 0 = p ∧ (timelikeLine.IsCausal → IsClosedEmbedding γ) ∧
      timelikeLine.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn univ p :=
  exists_line isClosed_univ timeline_isTranslationAtlas
    (fun _ a b _ => timelikeLine_causalCurveOn_id a b) (mem_univ p)

/-- The identity is a chronal curve of the timelike line over every segment. -/
theorem timelikeLine_chronalCurveOn_id (a b : ℝ) : timelikeLine.ChronalCurveOn ⊤ id a b where
  mem _ _ := trivial
  rel t _ N _ htN := by
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    exact ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 =>
      timelikeLine_lt.2 ⟨h2, fun z hz => hsub ⟨h1.trans_le hz.1, hz.2.trans_lt h3⟩⟩⟩

/-- **The timelike line, chronal form**: the hypotheses of `exists_chronal_line` hold, with
`S = ℝ`. -/
theorem timelikeLine_chronal_line (p : ℝ) :
    ∃ γ : ℝ → ℝ, γ 0 = p ∧ (timelikeLine.IsCausal → IsClosedEmbedding γ) ∧
      timelikeLine.Inextensible ⊤ univ γ ∧ (∀ a b, timelikeLine.ChronalCurveOn ⊤ γ a b) ∧
      range γ = connectedComponentIn univ p :=
  exists_chronal_line isClosed_univ timeline_isTranslationAtlas
    (fun _ a b _ => timelikeLine_chronalCurveOn_id a b) (mem_univ p)

/-- The timelike line's development through `0` is `id`. -/
theorem timelikeLine_id_line :
    IsLineDevelopment (univ : Set ℝ) (fun _ : Unit => univ) (fun _ => id) (fun _ => univ) 0 id ∧
      IsClosedEmbedding (id : ℝ → ℝ) ∧ timelikeLine.Inextensible ⊤ univ id := by
  refine ⟨⟨rfl, continuous_id, ?_, fun t _ _ => ⟨1, one_pos, id, strictMono_id, continuous_id,
      fun _ _ => ⟨trivial, rfl⟩⟩, fun t ε hε => ⟨Ioo (t - ε) (t + ε), isOpen_Ioo,
      (show t ∈ Ioo (t - ε) (t + ε) from ⟨by linarith, by linarith⟩), fun y hy => ⟨y, hy.2, rfl⟩⟩,
      fun x => not_tendsto_nhds_of_tendsto_atTop tendsto_id x,
      fun x => not_tendsto_nhds_of_tendsto_atBot tendsto_id x⟩,
    IsClosedEmbedding.id, timelikeLine_inextensible_id⟩
  rw [range_id, connectedComponentIn_univ]
  exact (PreconnectedSpace.connectedComponent_eq_univ (0 : ℝ)).symm

variable (P : ℝ) [Fact (0 < P)]

/-- The coordinate of the chart at `a` of a point other than `a`. -/
theorem circle_mem_Ioo (a : ℝ) {x : AddCircle P} (hx : x ≠ (a : AddCircle P)) :
    (AddCircle.equivIco P a x : ℝ) ∈ Ioo a (a + P) := by
  refine (eq_left_or_mem_Ioo_of_mem_Ico (AddCircle.equivIco P a x).2).resolve_left fun h => hx ?_
  calc x = ((AddCircle.equivIco P a x : ℝ) : AddCircle P) := AddCircle.coe_equivIco.symm
    _ = a := by rw [h]

/-- `P / 2` is not `0` in `ℝ / Pℤ`. -/
theorem circle_half_ne_zero : ((P / 2 : ℝ) : AddCircle P) ≠ 0 := by
  have hP : 0 < P := Fact.out
  intro h
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0) (p := P)
    (show P / 2 ∈ Ico 0 (0 + P) from ⟨by linarith, by linarith⟩)
    (show (0 : ℝ) ∈ Ico 0 (0 + P) from ⟨le_rfl, by linarith⟩)).1 (h.trans (AddCircle.coe_zero P).symm)
  linarith

/-- The translation atlas of the circle `ℝ / Pℤ`: at each `a`, the chart `[a, a + P)`. -/
theorem circle_isTranslationAtlas :
    IsTranslationAtlas (univ : Set (AddCircle P)) (fun a : ℝ => {(a : AddCircle P)}ᶜ)
      (fun a x => (AddCircle.equivIco P a x : ℝ)) (fun _ r => (r : AddCircle P))
      (fun a => Ioo a (a + P)) := by
  have hP : 0 < P := Fact.out
  refine ⟨fun _ => isOpen_compl_singleton, fun _ => isOpen_Ioo, fun a => ?_,
    fun _ => (AddCircle.continuous_mk' P).continuousOn, fun a x hx => circle_mem_Ioo P a hx.2,
    fun a r hr => ⟨trivial, ?_⟩, fun a x _ => AddCircle.coe_equivIco,
    fun a r hr => AddCircle.equivIco_coe_of_mem (Ioo_subset_Ico_self hr), fun x _ => ?_,
    fun a b x hx => ?_⟩
  · exact continuousOn_of_forall_continuousAt fun x hx =>
      continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco P a hx.2)
  · intro h
    exact (ne_of_gt hr.1) ((AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hr)
      (left_mem_Ico.2 (by linarith))).1 h)
  · by_cases hx : x = ((0 : ℝ) : AddCircle P)
    · refine ⟨P / 2, fun h => circle_half_ne_zero P ?_⟩
      have h' : x = ((P / 2 : ℝ) : AddCircle P) := h
      rw [← h', hx, AddCircle.coe_zero P]
    · exact ⟨0, hx⟩
  · have hxa : x ≠ (a : AddCircle P) := hx.1.2
    have hxb : x ≠ (b : AddCircle P) := hx.2
    set k := (AddCircle.equivIco P b x : ℝ) - (AddCircle.equivIco P a x : ℝ) with hk_def
    refine ⟨k, ?_⟩
    have hc : ContinuousAt (fun y : AddCircle P => (AddCircle.equivIco P a y : ℝ) + k) x :=
      (continuous_subtype_val.continuousAt.comp
        (AddCircle.continuousAt_equivIco P a hxa)).add continuousAt_const
    have hval : (AddCircle.equivIco P a x : ℝ) + k = AddCircle.equivIco P b x := by
      rw [hk_def]
      ring
    have hev : ∀ᶠ y in 𝓝 x, (AddCircle.equivIco P a y : ℝ) + k ∈ Ioo b (b + P) :=
      hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hval]; exact circle_mem_Ioo P b hxb))
    have hk : ((k : ℝ) : AddCircle P) = 0 := by
      rw [hk_def, AddCircle.coe_sub, AddCircle.coe_equivIco, AddCircle.coe_equivIco, sub_self]
    filter_upwards [hev] with y hy _
    have hcoe : (((AddCircle.equivIco P a y : ℝ) + k : ℝ) : AddCircle P) = y := by
      rw [AddCircle.coe_add, hk, add_zero, AddCircle.coe_equivIco]
    show (AddCircle.equivIco P b y : ℝ) = (AddCircle.equivIco P a y : ℝ) + k
    calc (AddCircle.equivIco P b y : ℝ)
        = AddCircle.equivIco P b ((((AddCircle.equivIco P a y : ℝ) + k : ℝ) : AddCircle P)) := by
          rw [hcoe]
      _ = (AddCircle.equivIco P a y : ℝ) + k :=
          AddCircle.equivIco_coe_of_mem (Ioo_subset_Ico_self hy)

/-- Along two sequences tending to the same end, the quotient map takes the values `0` and
`P / 2`: it has no limit there. -/
theorem circle_not_tendsto {l : Filter ℝ} {f g : ℕ → ℝ} (hf : Tendsto f atTop l)
    (hg : Tendsto g atTop l) (hf0 : ∀ n, (f n : AddCircle P) = 0)
    (hg0 : ∀ n, (g n : AddCircle P) = ((P / 2 : ℝ) : AddCircle P)) (x : AddCircle P) :
    ¬ Tendsto (fun t : ℝ => (t : AddCircle P)) l (𝓝 x) := by
  intro h
  have h1 : Tendsto (fun n => (f n : AddCircle P)) atTop (𝓝 x) := h.comp hf
  have h2 : Tendsto (fun n => (g n : AddCircle P)) atTop (𝓝 x) := h.comp hg
  simp only [hf0, hg0] at h1 h2
  have e1 : x = 0 := tendsto_nhds_unique h1 tendsto_const_nhds
  have e2 : x = ((P / 2 : ℝ) : AddCircle P) := tendsto_nhds_unique h2 tendsto_const_nhds
  exact circle_half_ne_zero P (e2.symm.trans e1)

/-- **The circle**: the quotient map `ℝ → ℝ / Pℤ`, periodic, is a development of the circle. -/
theorem circle_isLineDevelopment :
    IsLineDevelopment (univ : Set (AddCircle P)) (fun a : ℝ => {(a : AddCircle P)}ᶜ)
      (fun _ r => (r : AddCircle P)) (fun a => Ioo a (a + P)) 0 (fun t => (t : AddCircle P)) := by
  have hP : 0 < P := Fact.out
  have hcont : Continuous (fun t : ℝ => (t : AddCircle P)) := AddCircle.continuous_mk' P
  have hmul : ∀ n : ℕ, (((n : ℝ) * P : ℝ) : AddCircle P) = 0 := fun n =>
    (AddCircle.coe_eq_zero_iff P).2 ⟨n, by simp [zsmul_eq_mul]⟩
  have hnmul : ∀ n : ℕ, ((-((n : ℝ) * P) : ℝ) : AddCircle P) = 0 := fun n =>
    (AddCircle.coe_eq_zero_iff P).2 ⟨-n, by simp [zsmul_eq_mul]⟩
  have htop : Tendsto (fun n : ℕ => (n : ℝ) * P) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hP
  refine ⟨AddCircle.coe_zero P, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · exact (isPreconnected_range hcont).subset_connectedComponentIn ⟨0, AddCircle.coe_zero P⟩
        (subset_univ _)
    · intro y _
      exact QuotientAddGroup.mk_surjective y
  · intro t a ht
    have hta : ((t : ℝ) : AddCircle P) ≠ (a : AddCircle P) := ht
    have hmem := circle_mem_Ioo P a hta
    set k := (AddCircle.equivIco P a (t : AddCircle P) : ℝ) - t with hk_def
    have hk : ((k : ℝ) : AddCircle P) = 0 := by
      rw [hk_def, AddCircle.coe_sub, AddCircle.coe_equivIco, sub_self]
    set ε := min ((AddCircle.equivIco P a (t : AddCircle P) : ℝ) - a)
      (a + P - (AddCircle.equivIco P a (t : AddCircle P) : ℝ)) with hε_def
    have hε : 0 < ε := lt_min (by linarith [hmem.1]) (by linarith [hmem.2])
    have hε1 : ε ≤ (AddCircle.equivIco P a (t : AddCircle P) : ℝ) - a := min_le_left _ _
    have hε2 : ε ≤ a + P - (AddCircle.equivIco P a (t : AddCircle P) : ℝ) := min_le_right _ _
    refine ⟨ε, hε, fun s => s + k, fun s s' h => add_lt_add_left h k,
      continuous_id.add continuous_const, fun s hs => ⟨?_, ?_⟩⟩
    · show s + k ∈ Ioo a (a + P)
      rw [hk_def]
      constructor <;> linarith [hs.1, hs.2]
    · show (s : AddCircle P) = ((s + k : ℝ) : AddCircle P)
      rw [AddCircle.coe_add, hk, add_zero]
  · intro t ε hε
    refine ⟨(fun s : ℝ => (s : AddCircle P)) '' Ioo (t - ε) (t + ε),
      QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo, ⟨t, ⟨by linarith, by linarith⟩, rfl⟩,
      fun y hy => hy.2⟩
  · exact circle_not_tendsto P htop (tendsto_atTop_add_const_right _ (P / 2) htop) hmul
      (fun n => by rw [AddCircle.coe_add, hmul, zero_add])
  · have hbot : Tendsto (fun n : ℕ => -((n : ℝ) * P)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp htop
    exact circle_not_tendsto P hbot (tendsto_atBot_add_const_right _ (P / 2) hbot) hnmul
      (fun n => by rw [AddCircle.coe_add, hnmul, zero_add])

/-- **No closed embedding `ℝ → ℝ / Pℤ`**: step (7) needs the injectivity. -/
theorem not_isClosedEmbedding_circle (γ : ℝ → AddCircle P) : ¬ IsClosedEmbedding γ := by
  intro h
  haveI := h.compactSpace
  exact noncompact_univ ℝ isCompact_univ

/-- The circle's development is periodic and not injective. -/
theorem circle_periodic_not_injective :
    (∀ t : ℝ, ((t + P : ℝ) : AddCircle P) = (t : AddCircle P)) ∧
      ¬ Injective (fun t : ℝ => (t : AddCircle P)) := by
  have hP : 0 < P := Fact.out
  refine ⟨fun t => AddCircle.coe_add_period P t, fun h => ?_⟩
  have := h (show ((0 : ℝ) : AddCircle P) = ((0 + P : ℝ) : AddCircle P) from
    (AddCircle.coe_add_period P 0).symm)
  linarith

/-- **The causality relating every two points** of an open set: not causal as soon as
two points differ; every continuous map is a causal curve of it. -/
def allRelated (X : Type*) [TopologicalSpace X] : Causality X where
  le U x y := x ∈ U ∧ y ∈ U
  lt U x y := x ∈ U ∧ y ∈ U
  le_mem_left h := h.1
  le_mem_right h := h.2
  lt_mem_left h := h.1
  lt_mem_right h := h.2
  le_refl hx := ⟨hx, hx⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₂.2⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₂.2⟩
  le_mono h _ _ h' := ⟨h h'.1, h h'.2⟩
  lt_mono h _ _ h' := ⟨h h'.1, h h'.2⟩
  le_of_lt h := h
  isOpen_lt_right U x := by
    by_cases hx : x ∈ U
    · simpa [hx] using U.isOpen
    · simp [hx]
  isOpen_lt_left U x := by
    by_cases hx : x ∈ U
    · simpa [hx] using U.isOpen
    · simp [hx]

/-- Every continuous map is a chronal curve of `allRelated`. -/
theorem allRelated_chronalCurveOn {X : Type*} [TopologicalSpace X] {c : ℝ → X}
    (hc : Continuous c) (a b : ℝ) : (allRelated X).ChronalCurveOn ⊤ c a b where
  mem _ _ := trivial
  rel t _ N _ htN := by
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 ((N.isOpen.preimage hc).mem_nhds htN)
    exact ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 =>
      ⟨hsub ⟨h1, h2.trans h3⟩, hsub ⟨h1.trans h2, h3⟩⟩⟩

/-- **A circle in a non-causal spacetime**: with `allRelated`, the periodic `γ = (↑)` satisfies
the conclusion of `exists_line` (and of `BTZAxioms.line` with `S₀` the circle), the closed
embedding vacuously, the causality not being causal; and it is not a closed embedding. -/
theorem circle_line :
    ¬ (allRelated (AddCircle P)).IsCausal ∧
      (fun t : ℝ => (t : AddCircle P)) 0 = 0 ∧
      ((allRelated (AddCircle P)).IsCausal → IsClosedEmbedding (fun t : ℝ => (t : AddCircle P))) ∧
      (allRelated (AddCircle P)).Inextensible ⊤ univ (fun t : ℝ => (t : AddCircle P)) ∧
      (∀ a b, (allRelated (AddCircle P)).ChronalCurveOn ⊤ (fun t : ℝ => (t : AddCircle P)) a b) ∧
      range (fun t : ℝ => (t : AddCircle P)) = connectedComponentIn univ 0 ∧
      ¬ IsClosedEmbedding (fun t : ℝ => (t : AddCircle P)) := by
  have hnc : ¬ (allRelated (AddCircle P)).IsCausal := fun h =>
    circle_half_ne_zero P (@h ((P / 2 : ℝ) : AddCircle P) 0 ⟨trivial, trivial⟩ ⟨trivial, trivial⟩)
  have hdev := circle_isLineDevelopment P
  have hchron : ∀ a b, (allRelated (AddCircle P)).ChronalCurveOn ⊤
      (fun t : ℝ => (t : AddCircle P)) a b := allRelated_chronalCurveOn hdev.continuous
  have hcin : (allRelated (AddCircle P)).CausalCurveIn ⊤ univ (fun t : ℝ => (t : AddCircle P)) :=
    ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => (hchron a b).causalCurveOn⟩
  exact ⟨hnc, AddCircle.coe_zero P, fun h => absurd h hnc,
    inextensible_of_not_tendsto hcin (fun x _ => hdev.not_tendsto_atTop x)
      (fun x _ => hdev.not_tendsto_atBot x), hchron, hdev.range_eq,
    not_isClosedEmbedding_circle P _⟩

end Witnesses

end LineDevelopment

end Causal
