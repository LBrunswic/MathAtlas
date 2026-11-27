import GX.BTZ.Surgery
import GX.BTZ.IsomE0
import GXScaffold.BTZ.MaxExtension

/-!
# btz § 2 and § 5.3: the BTZ lines of an `𝔼₀`-manifold are closed, carry an `(ℝ, ℝ)`-structure, and are second countable

Target `T-btz-line-structure` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
Neither row is marked: `𝔼₀` only (T-btz-scope), and each row has a part that is not proved here.

* `btzthm:BTZ_ext` — `BTZ_1.tex:1528` (proof l.1544–1546) — the second-countability ingredient of
  the named input `GX.BTZMax.RichardsInput`, proved, with no second countability assumed anywhere:
  `GX.BTZLine.secondCountable_line` and `GX.BTZLine.isLindelof_line` (every BTZ line, *i.e.*
  connected component of `sing₀`, of a Hausdorff `𝔼₀`-manifold is second countable and Lindelöf),
  through the `(ℝ, ℝ)`-structure `GX.BTZLine.instHasGroupoidS0` of `sing₀`. What is left of
  `RichardsInput` is « countably many lines »: `GX.BTZLine.CountableLinesInput`;
  `GX.BTZLine.richardsInput_iff_countableLines` proves the two inputs equivalent (through
  `GX.BTZLine.isLindelof_S0_iff_countable`). 0 `sorry`, standard axioms.
* `btzcor:manifold_smooth_manifold_singular` — `BTZ_1.tex:395–396` — the topological half of its
  second sentence at `𝔼₀` (where `sing = sing₀`): `GX.BTZLine.btz_line_structure` (`sing₀` is closed,
  locally flat in the paper charts, a topological `1`-manifold with an `(ℝ, ℝ)`-structure, each
  component second countable). The smooth `3`-manifold structure is not attempted.

> Consider a connected component $\Delta$ of $\sing_0(M)$. The $\mass{\geq 0}$-structure of
> $\overline M$ induces a $\left(G ,\sing(\mass{0}) \right)$-structure on $\Delta$ with $G$ the
> image of $\isom(\mass{0})$ in the group of homeomorphisms of $\sing_0(\mass{0})$. Since the
> isometries of $\mass{0}$ act by translation on $\sing_0(\mass{0})$, the singular line $\Delta$
> is actually endowed with a $(\RR,\RR)$-structure ($\RR$ acting by translation on itself).
> Finally, $\Delta$ admits a Riemannian metric and is thus second countable. (l.1546)
>
> A $\mass{\geq 0}$-manifold $M$ is smooth $3$-manifold and its singular locus is a closed
> 1-submanifold. Furthermore, for any $\alpha\in \RR_+$, $\sing_\alpha(M)$ is a closed
> 1-submanifold. (l.395–396)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope): `ChartedSpace E0Y M`, `HasGroupoid M e0Groupoid` |
| `M` Hausdorff (l.261) | ✓ carried (`T2Space M`), used: the unit-speed paths of a line are unique |
| `M` second countable (l.261) | ⚠ weakened: not assumed (the point of l.1546, where `M̄` is not yet known second countable) |
| `G` = the image of `isom(𝔼₀)` on the axis (l.1546) | ✓ the transitions of the line charts are read off `GX.E0AbsMax.e0Loop_localForm` (every element of `G` is `(τ, z) ↦ (τ + a, R z)` near the axis, `btzprop:isom`'s local form); the structure group is `Multiplicative ℝ` acting by translation, `GX.gxGroupoid` |
| « admits a Riemannian metric and is thus second countable » | ✓ replaced by the unit-speed flow of the translation structure: a component is the image of an interval of `ℝ` (`GX.BTZLine.isLindelof_connectedComponent`) |
| « closed 1-submanifold » (l.395) | ⚠ read topologically: closed, locally flat in the paper chart `E0CBG.paperChart` (`sing₀` is the axis), a topological `1`-manifold; no smooth structure |

## SCOPE (disclosed)

* (a) `𝔼₀` only; `sing_α` for `α > 0` is not treated (T-btz-scope).
* (b) The smooth structure of `btzcor:manifold_smooth_manifold_singular` (« smooth 3-manifold »,
  « 1-submanifold » in the smooth sense) is not attempted.
* (c) « countably many lines » (Richards' theorem MR143186 and the line-to-puncture injectivity,
  l.1544) is not proved: it is the named input `CountableLinesInput`, never an axiom.
* (d) The general fact proved is of independent use: in a Hausdorff `ChartedSpace ℝ X` with
  translation transitions, every connected component is Lindelöf and second countable
  (`GX.BTZLine.secondCountable_connectedComponent`; connected: `secondCountable_of_connectedSpace`).
  Proof: a unit-speed path is unique (Hausdorff, Liouville on an interval), extends along any chart,
  so the times reached from `p` form an open set `reachD p ⊆ ℝ` on which the flow is continuous and
  whose image is clopen. Neither Hausdorffness nor the translation structure can be dropped
  (uncountably many copies of `ℝ` glued along `]−∞, 0[`; the long line), but these two
  counterexamples are not formalized here.
* (e) The quoted sentence says « a connected component `Δ` of `sing₀(M)` »; the context (the
  `𝔼_{≥0}`-structure of `M̄`, the lines of `M̄ ∖ M`) reads `sing₀(M̄)`. The Lean statement is about
  any `𝔼₀`-manifold, so it covers both.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

namespace BTZLine

open Set Filter Topology Function TopologicalSpace
open E0CBG

/-! ### §1 `(ℝ, ℝ)`-manifolds: the unit-speed flow, and second countability of components -/

/-- **The groupoid of an `(ℝ, ℝ)`-structure**: `ℝ` acting on itself by translation, as a
`(G, X)`-groupoid (`Multiplicative ℝ` acts on `ℝ` by `ofAdd a • y = a + y`). -/
abbrev transGroupoid : StructureGroupoid ℝ := gxGroupoid (Multiplicative ℝ) ℝ

section Abstract

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℝ X] [HasGroupoid X transGroupoid]

/-- Two charts differ near every point of their overlap by a translation. -/
theorem exists_add_eq {e e' : OpenPartialHomeomorph X ℝ} (he : e ∈ atlas ℝ X)
    (he' : e' ∈ atlas ℝ X) {x : X} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ c : ℝ, ∀ᶠ y in 𝓝 x, e' y = e y + c := by
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid
    (HasGroupoid.compatible (G := transGroupoid) he he') hx hx'
  refine ⟨Multiplicative.toAdd g, ?_⟩
  filter_upwards [hg] with y hy
  rw [hy, add_comm]
  rfl

/-- **A unit-speed path on `J`**: read in every chart, `γ` is `r ↦ r + const` near each point. -/
def IsUnitPathOn (γ : ℝ → X) (J : Set ℝ) : Prop :=
  ∀ s ∈ J, ∀ e ∈ atlas ℝ X, γ s ∈ e.source →
    ∀ᶠ r in 𝓝[J] s, γ r ∈ e.source ∧ e (γ r) = e (γ s) + (r - s)

omit [ChartedSpace ℝ X] [HasGroupoid X transGroupoid] in
/-- Read in one chart, a unit-speed germ tends to its value. -/
theorem tendsto_of_chart {γ : ℝ → X} {J : Set ℝ} {s : ℝ} {e : OpenPartialHomeomorph X ℝ}
    (hs : γ s ∈ e.source)
    (h : ∀ᶠ r in 𝓝[J] s, γ r ∈ e.source ∧ e (γ r) = e (γ s) + (r - s)) :
    Tendsto γ (𝓝[J] s) (𝓝 (γ s)) := by
  have h1 : Tendsto (fun r : ℝ => e (γ s) + (r - s)) (𝓝[J] s) (𝓝 (e (γ s))) := by
    have := ((continuous_const.add (continuous_id.sub continuous_const)).tendsto s
      (f := fun r : ℝ => e (γ s) + (r - s)))
    simp only [sub_self, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (e.continuousAt_symm (e.map_source hs)).tendsto.comp h1
  rw [e.left_inv hs] at h2
  refine h2.congr' ?_
  filter_upwards [h] with r hr
  simp only [Function.comp_apply, ← hr.2, e.left_inv hr.1]

/-- One chart at each point suffices. -/
theorem isUnitPathOn_of_exists {γ : ℝ → X} {J : Set ℝ}
    (h : ∀ s ∈ J, ∃ e ∈ atlas ℝ X, γ s ∈ e.source ∧
      ∀ᶠ r in 𝓝[J] s, γ r ∈ e.source ∧ e (γ r) = e (γ s) + (r - s)) :
    IsUnitPathOn γ J := by
  intro s hs e' he' hs'
  obtain ⟨e, he, hse, hev⟩ := h s hs
  have ht := tendsto_of_chart hse hev
  obtain ⟨c, hc⟩ := exists_add_eq he he' hse hs'
  filter_upwards [hev, ht.eventually (e'.open_source.mem_nhds hs'), ht.eventually hc]
    with r hr1 hr2 hr3
  refine ⟨hr2, ?_⟩
  rw [hr3, hr1.2, hc.self_of_nhds]
  ring

omit [HasGroupoid X transGroupoid] in
theorem IsUnitPathOn.mono {γ : ℝ → X} {J J' : Set ℝ} (h : IsUnitPathOn γ J) (hJ : J' ⊆ J) :
    IsUnitPathOn γ J' := fun s hs e he hse =>
  (h s (hJ hs) e he hse).filter_mono (nhdsWithin_mono _ hJ)

omit [HasGroupoid X transGroupoid] in
theorem IsUnitPathOn.continuousOn {γ : ℝ → X} {J : Set ℝ} (h : IsUnitPathOn γ J) :
    ContinuousOn γ J := fun s hs =>
  tendsto_of_chart (mem_chart_source ℝ (γ s))
    (h s hs _ (chart_mem_atlas ℝ (γ s)) (mem_chart_source ℝ (γ s)))

omit [HasGroupoid X transGroupoid] in
/-- **Uniqueness of unit-speed paths** (Hausdorff, on a preconnected `J`). -/
theorem IsUnitPathOn.eqOn [T2Space X] {γ σ : ℝ → X} {J : Set ℝ} (hJ : IsPreconnected J)
    (hγ : IsUnitPathOn γ J) (hσ : IsUnitPathOn σ J) {s₀ : ℝ} (hs₀ : s₀ ∈ J)
    (h0 : γ s₀ = σ s₀) : EqOn γ σ J := by
  haveI := isPreconnected_iff_preconnectedSpace.1 hJ
  let A : Set J := {s | γ s = σ s}
  have hA : IsClopen A := by
    refine ⟨isClosed_eq hγ.continuousOn.restrict hσ.continuousOn.restrict, ?_⟩
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hs' : γ s = σ s := hs
    rw [mem_nhds_subtype_iff_nhdsWithin]
    have h1 := hγ s s.2 _ (chart_mem_atlas ℝ (γ s)) (mem_chart_source ℝ (γ s))
    have h2 := hσ s s.2 _ (chart_mem_atlas ℝ (γ s)) (hs' ▸ mem_chart_source ℝ (γ s))
    filter_upwards [h1, h2, self_mem_nhdsWithin] with r hr1 hr2 hrJ
    refine ⟨⟨r, hrJ⟩, ?_, rfl⟩
    show γ r = σ r
    refine (chartAt ℝ (γ s)).injOn hr1.1 hr2.1 ?_
    rw [hr1.2, hr2.2, hs']
  have hAu := hA.eq_univ ⟨⟨s₀, hs₀⟩, h0⟩
  intro s hs
  have : (⟨s, hs⟩ : J) ∈ A := hAu ▸ mem_univ _
  exact this

omit [HasGroupoid X transGroupoid] in
/-- **Gluing** two unit-speed paths along closed sets. -/
theorem IsUnitPathOn.union {γ σ g : ℝ → X} {J K : Set ℝ} (hJ : IsClosed J) (hK : IsClosed K)
    (hγ : IsUnitPathOn γ J) (hσ : IsUnitPathOn σ K) (hgJ : EqOn g γ J) (hgK : EqOn g σ K) :
    IsUnitPathOn g (J ∪ K) := by
  intro s _ e he hgs
  rw [nhdsWithin_union, eventually_sup]
  have key : ∀ {L : Set ℝ} {η : ℝ → X}, IsClosed L → IsUnitPathOn η L → EqOn g η L →
      ∀ᶠ r in 𝓝[L] s, g r ∈ e.source ∧ e (g r) = e (g s) + (r - s) := by
    intro L η hL hη hg
    by_cases hsL : s ∈ L
    · have hgs' : η s ∈ e.source := hg hsL ▸ hgs
      filter_upwards [hη s hsL e he hgs', self_mem_nhdsWithin] with r hr hrL
      rw [hg hrL, hg hsL]
      exact hr
    · filter_upwards [inter_mem_nhdsWithin L (hL.isOpen_compl.mem_nhds hsL)] with r hr
      exact absurd hr.1 hr.2
  exact ⟨key hJ hγ hgJ, key hK hσ hgK⟩

/-- **The chart segment** `r ↦ e⁻¹(y + (r − t))` is a unit-speed path where it stays in the
target. -/
theorem isUnitPathOn_segment {e : OpenPartialHomeomorph X ℝ} (he : e ∈ atlas ℝ X) (y t : ℝ)
    {K : Set ℝ} (hK : ∀ r ∈ K, y + (r - t) ∈ e.target) :
    IsUnitPathOn (fun r => e.symm (y + (r - t))) K := by
  refine isUnitPathOn_of_exists fun s hs => ⟨e, he, e.map_target (hK s hs), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  refine ⟨e.map_target (hK r hr), ?_⟩
  rw [e.right_inv (hK r hr), e.right_inv (hK s hs)]
  ring

/-- The set of times reached from `p` by a unit-speed path. -/
def reachD (p : X) : Set ℝ := {t | ∃ γ : ℝ → X, γ 0 = p ∧ IsUnitPathOn γ (uIcc 0 t)}

open Classical in
/-- **The unit-speed flow** from `p` (well defined by uniqueness, `flow_eq`). -/
noncomputable def flow (p : X) (t : ℝ) : X :=
  if h : t ∈ reachD p then h.choose t else p

omit [HasGroupoid X transGroupoid] in
theorem flow_eq [T2Space X] {p : X} {t : ℝ} {γ : ℝ → X} (h0 : γ 0 = p)
    (hγ : IsUnitPathOn γ (uIcc 0 t)) : flow p t = γ t := by
  have ht : t ∈ reachD p := ⟨γ, h0, hγ⟩
  rw [flow, dif_pos ht]
  obtain ⟨h0', hγ'⟩ := ht.choose_spec
  exact hγ'.eqOn isPreconnected_uIcc hγ left_mem_uIcc (h0'.trans h0.symm) right_mem_uIcc

theorem mem_uIcc_add {a u r t : ℝ} (hr : r ∈ uIcc t (t + u)) : a + (r - t) ∈ uIcc a (a + u) := by
  rw [mem_uIcc] at hr ⊢
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-- **Extension of the flow along a chart.** -/
theorem flow_extend [T2Space X] {p : X} {t : ℝ} (ht : t ∈ reachD p)
    {e : OpenPartialHomeomorph X ℝ} (he : e ∈ atlas ℝ X) (hx : flow p t ∈ e.source) {u : ℝ}
    (hu : uIcc (e (flow p t)) (e (flow p t) + u) ⊆ e.target) :
    t + u ∈ reachD p ∧ flow p (t + u) = e.symm (e (flow p t) + u) := by
  classical
  obtain ⟨γ, hγ0, hγ⟩ := ht
  have hγt : flow p t = γ t := flow_eq hγ0 hγ
  set x := flow p t with hxdef
  set σ : ℝ → X := fun r => e.symm (e x + (r - t)) with hσdef
  have hK : ∀ r ∈ uIcc t (t + u), e x + (r - t) ∈ e.target := fun r hr => hu (mem_uIcc_add hr)
  have hσ : IsUnitPathOn σ (uIcc t (t + u)) := isUnitPathOn_segment he (e x) t hK
  have hσt : σ t = γ t := by
    show e.symm (e x + (t - t)) = γ t
    rw [sub_self, add_zero, e.left_inv hx, hγt]
  have hagree : EqOn γ σ (uIcc 0 t ∩ uIcc t (t + u)) :=
    IsUnitPathOn.eqOn ((ordConnected_uIcc.inter ordConnected_uIcc).isPreconnected)
      (hγ.mono inter_subset_left) (hσ.mono inter_subset_right) ⟨right_mem_uIcc, left_mem_uIcc⟩
      hσt.symm
  set g : ℝ → X := fun r => if r ∈ uIcc 0 t then γ r else σ r with hgdef
  have hgσ : EqOn g σ (uIcc t (t + u)) := fun r hr => by
    by_cases h : r ∈ uIcc 0 t
    · simp only [hgdef, if_pos h]; exact hagree ⟨h, hr⟩
    · simp only [hgdef, if_neg h]
  have hg : IsUnitPathOn g (uIcc 0 t ∪ uIcc t (t + u)) :=
    IsUnitPathOn.union isClosed_Icc isClosed_Icc hγ hσ (fun r hr => if_pos hr) hgσ
  have hg0 : g 0 = p := by simp only [hgdef, if_pos left_mem_uIcc, hγ0]
  have hg' : IsUnitPathOn g (uIcc 0 (t + u)) := hg.mono uIcc_subset_uIcc_union_uIcc
  refine ⟨⟨g, hg0, hg'⟩, ?_⟩
  rw [flow_eq hg0 hg', hgσ right_mem_uIcc]
  simp only [hσdef, add_sub_cancel_left]

/-- Near a reached time, the flow is a chart segment. -/
theorem flow_local [T2Space X] {p : X} {t : ℝ} (ht : t ∈ reachD p) :
    ∃ ε > 0, ∀ u : ℝ, |u| < ε → t + u ∈ reachD p ∧
      flow p (t + u) = (chartAt ℝ (flow p t)).symm (chartAt ℝ (flow p t) (flow p t) + u) := by
  set e := chartAt ℝ (flow p t)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target _
    (e.map_source (mem_chart_source ℝ (flow p t)))
  refine ⟨ε, hε, fun u hu => flow_extend ht (chart_mem_atlas ℝ _) (mem_chart_source ℝ _) ?_⟩
  intro v hv
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  rw [mem_uIcc] at hv
  rw [abs_lt] at hu ⊢
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

theorem zero_mem_reachD (p : X) : (0 : ℝ) ∈ reachD p := by
  refine ⟨fun _ => p, rfl, isUnitPathOn_of_exists fun s hs => ⟨_, chart_mem_atlas ℝ p,
    mem_chart_source ℝ p, ?_⟩⟩
  rw [uIcc_self, mem_singleton_iff] at hs
  subst hs
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [uIcc_self, mem_singleton_iff] at hr
  subst hr
  exact ⟨mem_chart_source ℝ p, by ring⟩

theorem flow_zero [T2Space X] (p : X) : flow p 0 = p := by
  obtain ⟨γ, h0, hγ⟩ := zero_mem_reachD p
  rw [flow_eq h0 hγ, h0]

theorem isOpen_reachD [T2Space X] (p : X) : IsOpen (reachD p) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨ε, hε, h⟩ := flow_local ht
  refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) fun t' ht' => ?_
  rw [Metric.mem_ball, Real.dist_eq] at ht'
  have := (h (t' - t) ht').1
  rwa [add_sub_cancel] at this

theorem continuousOn_flow [T2Space X] (p : X) : ContinuousOn (flow p) (reachD p) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, h⟩ := flow_local ht
  set e := chartAt ℝ (flow p t)
  have hc : ContinuousAt (fun t' => e.symm (e (flow p t) + (t' - t))) t := by
    refine ContinuousAt.comp (f := fun t' => e (flow p t) + (t' - t)) ?_ ?_
    · simp only [sub_self, add_zero]
      exact e.continuousAt_symm (e.map_source (mem_chart_source ℝ _))
    · exact (continuous_const.add (continuous_id.sub continuous_const)).continuousAt
  have heq : (fun t' => e.symm (e (flow p t) + (t' - t))) =ᶠ[𝓝 t] flow p := by
    filter_upwards [Metric.ball_mem_nhds t hε] with t' ht'
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    have := (h (t' - t) ht').2
    rw [add_sub_cancel] at this
    exact this.symm
  have := hc.tendsto.congr' heq
  rw [sub_self, add_zero, e.left_inv (mem_chart_source ℝ _)] at this
  exact this

theorem isOpen_range_flow [T2Space X] (p : X) : IsOpen (flow p '' reachD p) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨ε, hε, h⟩ := flow_local ht
  set e := chartAt ℝ (flow p t)
  have hN : e.source ∩ e ⁻¹' Metric.ball (e (flow p t)) ε ∈ 𝓝 (flow p t) :=
    (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source ℝ _, Metric.mem_ball_self hε⟩
  refine Filter.mem_of_superset hN fun y hy => ?_
  have hu : |e y - e (flow p t)| < ε := by
    have := hy.2; rwa [mem_preimage, Metric.mem_ball, Real.dist_eq] at this
  obtain ⟨h1, h2⟩ := h _ hu
  refine ⟨_, h1, ?_⟩
  rw [h2, add_sub_cancel, e.left_inv hy.1]

theorem isClosed_range_flow [T2Space X] (p : X) : IsClosed (flow p '' reachD p) := by
  refine isClosed_of_closure_subset fun q hq => ?_
  set e := chartAt ℝ q
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target _
    (e.map_source (mem_chart_source ℝ q))
  have hN : e.source ∩ e ⁻¹' Metric.ball (e q) ε ∈ 𝓝 q :=
    (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨mem_chart_source ℝ _, Metric.mem_ball_self hε⟩
  obtain ⟨_, ⟨hyS, hyB⟩, t, ht, rfl⟩ := mem_closure_iff_nhds.1 hq _ hN
  have hyB' : |e (flow p t) - e q| < ε := by
    rwa [mem_preimage, Metric.mem_ball, Real.dist_eq] at hyB
  have hu : uIcc (e (flow p t)) (e (flow p t) + (e q - e (flow p t))) ⊆ e.target := by
    intro v hv
    apply hball
    rw [add_sub_cancel, mem_uIcc] at hv
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_lt] at hyB' ⊢
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  obtain ⟨h1, h2⟩ := flow_extend ht (chart_mem_atlas ℝ q) hyS hu
  refine ⟨_, h1, ?_⟩
  rw [h2, add_sub_cancel, e.left_inv (mem_chart_source ℝ q)]

/-- **Every connected component of a Hausdorff `(ℝ, ℝ)`-manifold is Lindelöf**: it lies in the
image of the interval `reachD p` under the continuous flow. -/
theorem isLindelof_connectedComponent [T2Space X] (p : X) : IsLindelof (connectedComponent p) := by
  have hR : IsLindelof (flow p '' reachD p) :=
    (HereditarilyLindelofSpace.isLindelof _).image_of_continuousOn (continuousOn_flow p)
  have hp : p ∈ flow p '' reachD p := ⟨0, zero_mem_reachD p, flow_zero p⟩
  exact hR.of_isClosed_subset isClosed_connectedComponent
    (IsClopen.connectedComponent_subset ⟨isClosed_range_flow p, isOpen_range_flow p⟩ hp)

omit [ChartedSpace ℝ X] [HasGroupoid X transGroupoid] in
/-- A Lindelöf set of a space in which its points have second countable open neighbourhoods is
second countable. -/
theorem secondCountable_of_isLindelof {Y : Type*} [TopologicalSpace Y] {K : Set Y}
    (hK : IsLindelof K) (U : Y → Set Y) (hUo : ∀ x ∈ K, IsOpen (U x)) (hxU : ∀ x ∈ K, x ∈ U x)
    (hU : ∀ x ∈ K, SecondCountableTopology (U x)) : SecondCountableTopology K := by
  obtain ⟨r, hr, hcov⟩ := hK.elim_countable_subcover (fun x : K => U x) (fun x => hUo x x.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU x hx⟩)
  haveI := hr.to_subtype
  let V : r → Set K := fun i => Subtype.val ⁻¹' U ((i : K) : Y)
  haveI hV : ∀ i, SecondCountableTopology (V i) := fun i => by
    haveI := hU _ (i : K).2
    have hemb : IsEmbedding (fun z : V i => (⟨((z : K) : Y), z.2⟩ : U ((i : K) : Y))) := by
      refine IsEmbedding.of_comp (g := (Subtype.val : U ((i : K) : Y) → Y)) ?_
        continuous_subtype_val
        ((IsEmbedding.subtypeVal (p := (· ∈ K))).comp (IsEmbedding.subtypeVal (p := (· ∈ V i))))
      exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact hemb.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (U := V)
    (fun i => (hUo _ (i : K).2).preimage continuous_subtype_val) ?_
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 (hcov z.2)
  exact ⟨⟨i, hi⟩, hz⟩

omit [HasGroupoid X transGroupoid] in
theorem secondCountable_chart_source (x : X) : SecondCountableTopology (chartAt ℝ x).source :=
  (chartAt ℝ x).toHomeomorphSourceTarget.secondCountableTopology

/-- **Every connected component of a Hausdorff `(ℝ, ℝ)`-manifold is second countable.** -/
theorem secondCountable_connectedComponent [T2Space X] (p : X) :
    SecondCountableTopology (connectedComponent p) :=
  secondCountable_of_isLindelof (isLindelof_connectedComponent p) (fun x => (chartAt ℝ x).source)
    (fun x _ => (chartAt ℝ x).open_source) (fun x _ => mem_chart_source ℝ x)
    (fun x _ => secondCountable_chart_source x)

/-- **A connected Hausdorff `(ℝ, ℝ)`-manifold is second countable.** -/
theorem secondCountable_of_connectedSpace [T2Space X] [ConnectedSpace X] :
    SecondCountableTopology X := by
  obtain ⟨p⟩ := (inferInstance : ConnectedSpace X).toNonempty
  have h := isLindelof_connectedComponent p
  rw [PreconnectedSpace.connectedComponent_eq_univ] at h
  haveI := secondCountable_of_isLindelof h (fun x => (chartAt ℝ x).source)
    (fun x _ => (chartAt ℝ x).open_source) (fun x _ => mem_chart_source ℝ x)
    (fun x _ => secondCountable_chart_source x)
  exact (Homeomorph.Set.univ X).symm.secondCountableTopology

end Abstract

/-! ### §2 The `(ℝ, ℝ)`-structure of `sing₀` -/

section Lines

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **`sing₀` is the axis in every paper chart.** -/
theorem paperChart_mem_axis_iff (x : M) {q : M} (hq : q ∈ (paperChart x).source) :
    paperChart x q ∈ E0.axis ↔ q ∈ S0 M := by
  rw [paperChart, OpenPartialHomeomorph.trans_source] at hq
  have hq2 : chartAt E0Y x q ∈ range Sum.inr := by
    have := hq.2; rwa [mem_preimage, E0.paperOfY_source] at this
  have hval : paperChart x q = E0.paperOfY (chartAt E0Y x q) := rfl
  rw [← E0AbsMax.chart_mem_e0SingY_iff x hq.1, ← E0.paperInY_paperOfY hq2,
    E0AbsMax.e0Loop_paperInY_mem_sing_iff, hval]
  rfl

omit [HasGroupoid M e0Groupoid] in
theorem paperChart_apply (x q : M) : paperChart x q = E0.paperOfY (chartAt E0Y x q) := rfl

omit [HasGroupoid M e0Groupoid] in
theorem mem_chart_source_of_mem_paperChart_source {x q : M} (hq : q ∈ (paperChart x).source) :
    q ∈ (chartAt E0Y x).source ∧ chartAt E0Y x q ∈ range Sum.inr := by
  rw [paperChart, OpenPartialHomeomorph.trans_source] at hq
  have := hq.2
  rw [mem_preimage, E0.paperOfY_source] at this
  exact ⟨hq.1, this⟩

theorem paperOfY_paperInY (w : E0) : E0.paperOfY (E0.paperInY w) = w := by
  rw [E0.paperInY_apply, E0.paperOfY_inr, Homeomorph.apply_symm_apply]

/-- At a BTZ point, the paper chart is `(τ, 0)`. -/
theorem paperChart_eq_pair (x : M) {q : M} (hq : q ∈ (paperChart x).source) (hS : q ∈ S0 M) :
    ((paperChart x q).1, (0 : ℂ)) = paperChart x q :=
  Prod.ext rfl ((paperChart_mem_axis_iff x hq).2 hS).symm

theorem symm_mem_S0 (x : M) {τ : ℝ} (hτ : ((τ, 0) : E0) ∈ (paperChart x).target) :
    (paperChart x).symm (τ, 0) ∈ S0 M := by
  have hs := (paperChart x).map_target hτ
  rw [← paperChart_mem_axis_iff x hs, (paperChart x).right_inv hτ]
  rfl

open Classical in
/-- The inverse of the line chart (junk value `x` off its target). -/
noncomputable def lineInv (x : S0 M) (τ : ℝ) : S0 M :=
  if h : (paperChart (x : M)).symm (τ, 0) ∈ S0 M then ⟨_, h⟩ else x

theorem val_lineInv (x : S0 M) {τ : ℝ} (hτ : ((τ, 0) : E0) ∈ (paperChart (x : M)).target) :
    (lineInv x τ : M) = (paperChart (x : M)).symm (τ, 0) := by
  rw [lineInv, dif_pos (symm_mem_S0 (x : M) hτ)]

/-- **The line chart** at a BTZ point `x`: the height `τ` of the paper chart at `x`, on `sing₀`. -/
noncomputable def lineChart (x : S0 M) : OpenPartialHomeomorph (S0 M) ℝ where
  toFun q := (paperChart (x : M) q).1
  invFun := lineInv x
  source := Subtype.val ⁻¹' (paperChart (x : M)).source
  target := {τ | ((τ, 0) : E0) ∈ (paperChart (x : M)).target}
  map_source' q hq := by
    show (((paperChart (x : M) q).1, (0 : ℂ)) : E0) ∈ (paperChart (x : M)).target
    rw [paperChart_eq_pair _ hq q.2]
    exact (paperChart _).map_source hq
  map_target' τ hτ := by
    show ((lineInv x τ : S0 M) : M) ∈ (paperChart (x : M)).source
    rw [val_lineInv x hτ]
    exact (paperChart _).map_target hτ
  left_inv' q hq := by
    have hτ : (((paperChart (x : M) q).1, (0 : ℂ)) : E0) ∈ (paperChart (x : M)).target := by
      rw [paperChart_eq_pair _ hq q.2]; exact (paperChart _).map_source hq
    apply Subtype.ext
    show (lineInv x (paperChart (x : M) q).1 : M) = q
    rw [val_lineInv x hτ, paperChart_eq_pair _ hq q.2, (paperChart _).left_inv hq]
  right_inv' τ hτ := by
    show (paperChart (x : M) (lineInv x τ : M)).1 = τ
    rw [val_lineInv x hτ, (paperChart _).right_inv hτ]
  open_source := (paperChart (x : M)).open_source.preimage continuous_subtype_val
  open_target := (paperChart (x : M)).open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun := continuous_fst.comp_continuousOn
    ((paperChart (x : M)).continuousOn.comp continuous_subtype_val.continuousOn fun _ hq => hq)
  continuousOn_invFun := by
    rw [IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun τ : ℝ => (paperChart (x : M)).symm (τ, 0)) ?_ ?_
    · exact (paperChart (x : M)).continuousOn_symm.comp
        (continuous_id.prodMk continuous_const).continuousOn fun _ hτ => hτ
    · intro τ hτ
      exact val_lineInv x hτ

theorem lineChart_apply (x q : S0 M) : lineChart x q = (paperChart (x : M) q).1 := rfl

theorem mem_lineChart_source {x q : S0 M} :
    q ∈ (lineChart x).source ↔ (q : M) ∈ (paperChart (x : M)).source := Iff.rfl

/-- `sing₀` is a topological `1`-manifold: the line charts. -/
noncomputable instance instChartedSpaceS0 : ChartedSpace ℝ (S0 M) where
  atlas := range lineChart
  chartAt := lineChart
  mem_chart_source x := (paperChart_of_mem_S0 x.2).1
  chart_mem_atlas x := mem_range_self x

/-- **The line charts differ by translations** (`btzprop:isom`'s local form,
`E0AbsMax.e0Loop_localForm`: an element of `G` is `(τ, z) ↦ (τ + a, R z)` near the axis). -/
theorem lineChart_trans (a b : S0 M) {q : S0 M} (ha : q ∈ (lineChart a).source)
    (hb : q ∈ (lineChart b).source) :
    ∃ g : Multiplicative ℝ, ∀ᶠ z in 𝓝 q, lineChart b z = g • lineChart a z := by
  have hqa : (q : M) ∈ (paperChart (a : M)).source := ha
  have hqb : (q : M) ∈ (paperChart (b : M)).source := hb
  obtain ⟨hqa1, hqa2⟩ := mem_chart_source_of_mem_paperChart_source hqa
  obtain ⟨hqb1, -⟩ := mem_chart_source_of_mem_paperChart_source hqb
  set E := (chartAt E0Y (a : M)).symm.trans (chartAt E0Y (b : M)) with hEdef
  have hE : E ∈ e0Groupoid :=
    HasGroupoid.compatible (chart_mem_atlas E0Y (a : M)) (chart_mem_atlas E0Y (b : M))
  set τq := (paperChart (a : M) q).1 with hτq
  have hcq : chartAt E0Y (a : M) q = E0.paperInY (τq, 0) := by
    rw [hτq, paperChart_eq_pair _ hqa q.2, paperChart_apply, E0.paperInY_paperOfY hqa2]
  have h0 : E0.paperInY (τq, 0) ∈ E.source := by
    rw [← hcq, hEdef, OpenPartialHomeomorph.trans_source]
    refine ⟨(chartAt E0Y (a : M)).map_source hqa1, ?_⟩
    show (chartAt E0Y (a : M)).symm (chartAt E0Y (a : M) q) ∈ (chartAt E0Y (b : M)).source
    rw [(chartAt E0Y (a : M)).left_inv hqa1]
    exact hqb1
  obtain ⟨δ, hδ, a', R, hloc⟩ := E0AbsMax.e0Loop_localForm hE h0
  refine ⟨Multiplicative.ofAdd a', ?_⟩
  have hN : ∀ᶠ z in 𝓝 (q : M), z ∈ (paperChart (a : M)).source ∧
      dist (paperChart (a : M) z) (τq, 0) < δ := by
    have hc := (paperChart (a : M)).continuousAt hqa
    have hball : Metric.ball (paperChart (a : M) q) δ ∈ 𝓝 (paperChart (a : M) q) :=
      Metric.ball_mem_nhds _ hδ
    filter_upwards [(paperChart (a : M)).open_source.mem_nhds hqa, hc.eventually hball]
      with z h1 h3
    refine ⟨h1, ?_⟩
    have h3' : dist (paperChart (a : M) z) (paperChart (a : M) q) < δ := h3
    rwa [← paperChart_eq_pair _ hqa q.2] at h3'
  have hN' : ∀ᶠ z : S0 M in 𝓝 q, (z : M) ∈ (paperChart (a : M)).source ∧
      dist (paperChart (a : M) z) (τq, 0) < δ :=
    continuous_subtype_val.continuousAt.eventually hN
  filter_upwards [hN'] with z hz
  obtain ⟨h1, h3⟩ := hz
  obtain ⟨hz1, hz2⟩ := mem_chart_source_of_mem_paperChart_source h1
  obtain ⟨-, hEz⟩ := hloc (paperChart (a : M) z) h3
  have hcz : E0.paperInY (paperChart (a : M) z) = chartAt E0Y (a : M) z :=
    E0.paperInY_paperOfY hz2
  have hEB : E (chartAt E0Y (a : M) z) = chartAt E0Y (b : M) z := by
    rw [hEdef, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (chartAt E0Y (a : M)).left_inv hz1]
  have hzax : (paperChart (a : M) z).2 = 0 := (paperChart_mem_axis_iff _ h1).2 z.2
  rw [hcz, hEB, hzax, map_zero] at hEz
  show (paperChart (b : M) z).1 = Multiplicative.ofAdd a' • (paperChart (a : M) z).1
  rw [paperChart_apply (b : M), hEz, paperOfY_paperInY]
  show (paperChart (a : M) z).1 + a' = a' + (paperChart (a : M) z).1
  ring

/-- **The `(ℝ, ℝ)`-structure of `sing₀`** (l.1546): the line charts differ by translations. -/
instance instHasGroupoidS0 : HasGroupoid (S0 M) transGroupoid where
  compatible := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact symm_trans_mem_gxGroupoid fun q hq => lineChart_trans a b hq.1 hq.2

/-- **Every BTZ line is Lindelöf.** -/
theorem isLindelof_line [T2Space M] {x : M} (hx : x ∈ S0 M) :
    IsLindelof (connectedComponentIn (S0 M) x) := by
  rw [connectedComponentIn_eq_image hx]
  exact (isLindelof_connectedComponent (⟨x, hx⟩ : S0 M)).image continuous_subtype_val

/-- **Every BTZ line is second countable** (l.1546), with no second countability assumed. -/
theorem secondCountable_line [T2Space M] {x : M} (hx : x ∈ S0 M) :
    SecondCountableTopology (connectedComponentIn (S0 M) x) :=
  secondCountable_of_isLindelof (isLindelof_line hx) (fun y => (paperChart y).source)
    (fun y _ => (paperChart y).open_source)
    (fun _ hy => (paperChart_of_mem_S0 (connectedComponentIn_subset _ _ hy)).1)
    (fun y _ => (paperChart y).toHomeomorphSourceTarget.secondCountableTopology)

/-- **Countably many lines make `sing₀` Lindelöf.** -/
theorem isLindelof_S0_of_countable [T2Space M]
    (h : (range fun x : S0 M => connectedComponentIn (S0 M) (x : M)).Countable) :
    IsLindelof (S0 M) := by
  have hU : S0 M = ⋃ L ∈ range (fun x : S0 M => connectedComponentIn (S0 M) (x : M)), L := by
    ext y
    constructor
    · intro hy
      exact mem_iUnion₂.2 ⟨_, ⟨⟨y, hy⟩, rfl⟩, mem_connectedComponentIn hy⟩
    · intro hy
      obtain ⟨L, ⟨x, rfl⟩, hyL⟩ := mem_iUnion₂.1 hy
      exact connectedComponentIn_subset _ _ hyL
  rw [hU]
  exact h.isLindelof_biUnion (f := fun L => L) (by rintro _ ⟨x, rfl⟩; exact isLindelof_line x.2)

/-- **Conversely, a Lindelöf `sing₀` has countably many lines** (the lines are open in `sing₀`,
which is locally connected as a `1`-manifold). -/
theorem countable_lines_of_isLindelof_S0 (h : IsLindelof (S0 M)) :
    (range fun x : S0 M => connectedComponentIn (S0 M) (x : M)).Countable := by
  haveI : LindelofSpace (S0 M) := isLindelof_iff_lindelofSpace.1 h
  haveI : LocallyConnectedSpace (S0 M) := ChartedSpace.locallyConnectedSpace ℝ (S0 M)
  obtain ⟨r, hr, hcov⟩ := isLindelof_univ.elim_countable_subcover
    (fun x : S0 M => connectedComponent x) (fun _ => isOpen_connectedComponent)
    (fun x _ => mem_iUnion.2 ⟨x, mem_connectedComponent⟩)
  have hsub : (range fun x : S0 M => connectedComponentIn (S0 M) (x : M)) ⊆
      (fun x : S0 M => connectedComponentIn (S0 M) (x : M)) '' r := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hcov (mem_univ y))
    refine ⟨i, hi, ?_⟩
    show connectedComponentIn (S0 M) (i : M) = connectedComponentIn (S0 M) (y : M)
    rw [connectedComponentIn_eq_image i.2, connectedComponentIn_eq_image y.2]
    show Subtype.val '' connectedComponent i = Subtype.val '' connectedComponent y
    rw [connectedComponent_eq hyi]
  exact (hr.image _).mono hsub

/-- **`sing₀` is Lindelöf iff it has countably many lines.** -/
theorem isLindelof_S0_iff_countable [T2Space M] :
    IsLindelof (S0 M) ↔ (range fun x : S0 M => connectedComponentIn (S0 M) (x : M)).Countable :=
  ⟨countable_lines_of_isLindelof_S0, isLindelof_S0_of_countable⟩

/-- **The BTZ locus of an `𝔼₀`-manifold** (`btzcor:manifold_smooth_manifold_singular`'s
topological half at `𝔼₀`, and l.1546): closed; at each of its points the paper chart is a flat
chart (`sing₀` is the axis there); the line charts form an `(ℝ, ℝ)`-structure (the instance
`instHasGroupoidS0`); and each line is second countable and Lindelöf. -/
theorem btz_line_structure [T2Space M] :
    IsClosed (S0 M) ∧
    (∀ x ∈ S0 M, x ∈ (paperChart x).source ∧
      ∀ q ∈ (paperChart x).source, (q ∈ S0 M ↔ paperChart x q ∈ E0.axis)) ∧
    HasGroupoid (S0 M) transGroupoid ∧
    (∀ x ∈ S0 M, SecondCountableTopology (connectedComponentIn (S0 M) x) ∧
      IsLindelof (connectedComponentIn (S0 M) x)) :=
  ⟨E0Surgery.isClosed_S0,
    fun x hx => ⟨(paperChart_of_mem_S0 hx).1, fun _ hq => (paperChart_mem_axis_iff x hq).symm⟩,
    inferInstance, fun _ hx => ⟨secondCountable_line hx, isLindelof_line hx⟩⟩

end Lines

/-! ### §3 What is left of `RichardsInput`: countably many lines -/

section Residual

/-- **The residual named input** (l.1544: Richards' theorem MR143186 and the line-to-puncture
injectivity): in `RichardsInput`'s setting, the BTZ lines are countably many. Carried as a
hypothesis, never an axiom; not proved here. -/
def CountableLinesInput (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M] : Prop :=
  ∀ (C : Type) [TopologicalSpace C] [T2Space C] [ConnectedSpace C] [ChartedSpace E0Y C]
    [HasGroupoid C e0Groupoid] (ι : M → C), IsBTZEmbedding ι →
    (∀ p q : C, ∃ U : Opens C, p ∈ U ∧ q ∈ U ∧ range ι ⊆ U ∧
      SecondCountableTopology U ∧ (CE C).GloballyHyperbolicOn U) →
    (range fun x : S0 C => connectedComponentIn (S0 C) (x : C)).Countable

/-- **`RichardsInput` from countably many lines**: the second countability of each line, the third
ingredient of `RichardsInput`, is proved (`isLindelof_line`). -/
theorem richardsInput_of_countableLines {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]
    (h : CountableLinesInput M) : BTZMax.RichardsInput M := by
  intro C _ _ _ _ _ ι hι hU
  exact isLindelof_S0_of_countable (h C ι hι hU)

/-- **Nothing is lost**: `RichardsInput` is equivalent to `CountableLinesInput`, so the second
countability of the lines is all that the split removes from it. -/
theorem richardsInput_iff_countableLines {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] :
    BTZMax.RichardsInput M ↔ CountableLinesInput M := by
  refine ⟨fun h => ?_, richardsInput_of_countableLines⟩
  intro C _ _ _ _ _ ι hι hU
  exact countable_lines_of_isLindelof_S0 (h C ι hι hU)

end Residual

end BTZLine

end GX
