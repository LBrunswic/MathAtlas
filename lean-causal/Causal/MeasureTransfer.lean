import Causal.SFATransfer
import Causal.MeasureLocal
import Causal.SingularGeroch

/-!
# Admissible measures through isomorphic charts (model-free)

The ETT-layer half of target `T-ett-measures-manifolds`, split from
`Causal.Remarks.MeasuresManifolds` at graduation (kb 0047): no model, no `Causal.Port.*` import.
Cited, unmarked: `prop:mesure_admissible` — `ETT.tex:1726` (the hypothesis (i) of its proof, the
measures in charts). The full names stay in `Causal.MeasuresManifolds`.

* **Local form** (`ModelMeasuresLocal`): an admissible measure on a causally convex open set inside
  every neighbourhood of every point; `ModelMeasuresLocal.modelMeasures` gives the strict
  `Causal.Causality.ModelMeasures`.
* **Through a chart isomorphism**: a measure admissible on `e(U)` comes back to one admissible on
  `U` (`ChartIso.admissiblePastOn`, `ChartIso.admissibleFutureOn`), with `K` transported
  (`mem_Kminus_of_intertwine`, `ChartIso.symm_mem_Kminus_iff`); no causal convexity is needed for
  the transfer, only `R1Space` (regularity of the measure carried back).
* **The model's set first** (`ChartIso.exists_admissiblePastOn`): `U = e⁻¹(U′)` with `U′` causally
  convex in the model is causally convex in `M` under DEC-7's `StronglyCausal`
  (`ChartIso.causallyConvexIn_source_inter_preimage`).
* **Over a cover** by isomorphic charts: `isoChartsCover_modelMeasures(Local)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| strongly causal (l.1726) | ✓ carried, DEC-7's `StronglyCausal` |
| Hausdorff (`ETT.tex:254`) | ⚠ weakened: `R1Space` |
| `U_p` relatively compact, in a chart (l.1734–1736) | ⚠ weakened: inside any neighbourhood; compactness not needed |

## SCOPE (disclosed)

* The instances at the models and at every `E_{≥0}`-manifold are in `Causal.Remarks.MeasuresManifolds`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace MeasuresManifolds

open Set Filter Topology TopologicalSpace MeasureTheory SFATransfer

universe u v w y z

/-! ### Measures in every neighbourhood: the model side -/

section Local

variable {Y : Type v} [TopologicalSpace Y] [MeasurableSpace Y]

/-- **`ModelMeasures` in local form**: every neighbourhood of every point contains an open
neighbourhood, causally convex in the whole space, carrying a measure admissible in the past, and
one carrying a measure admissible in the future. -/
structure ModelMeasuresLocal (D : Causality Y) : Prop where
  past : ∀ p : Y, ∀ N ∈ 𝓝 p, ∃ U : Opens Y, p ∈ U ∧ (U : Set Y) ⊆ N ∧
    D.CausallyConvexIn (U : Set Y) ⊤ ∧ ∃ ν : Measure Y, D.AdmissiblePastOn U ν
  future : ∀ p : Y, ∀ N ∈ 𝓝 p, ∃ U : Opens Y, p ∈ U ∧ (U : Set Y) ⊆ N ∧
    D.CausallyConvexIn (U : Set Y) ⊤ ∧ ∃ ν : Measure Y, D.AdmissibleFutureOn U ν

/-- The shape of `E0.modelMeasures_local` and `MeasuresEAlpha.modelMeasures_local`. -/
theorem ModelMeasuresLocal.of_forall {D : Causality Y}
    (h : ∀ p : Y, ∀ N ∈ 𝓝 p, ∃ U : Opens Y, p ∈ U ∧ (U : Set Y) ⊆ N ∧
      D.CausallyConvexIn (U : Set Y) ⊤ ∧ (∃ ν : Measure Y, D.AdmissiblePastOn U ν) ∧
        ∃ ν : Measure Y, D.AdmissibleFutureOn U ν) : ModelMeasuresLocal D :=
  ⟨fun p N hN => by
    obtain ⟨U, hp, hUN, hU, hpast, -⟩ := h p N hN
    exact ⟨U, hp, hUN, hU, hpast⟩,
   fun p N hN => by
    obtain ⟨U, hp, hUN, hU, -, hfut⟩ := h p N hN
    exact ⟨U, hp, hUN, hU, hfut⟩⟩

/-- The local form gives `ModelMeasures`. -/
theorem ModelMeasuresLocal.modelMeasures {D : Causality Y} (h : ModelMeasuresLocal D) :
    D.ModelMeasures :=
  ⟨fun p => by
    obtain ⟨U, hp, -, hU, hν⟩ := h.past p univ univ_mem
    exact ⟨U, hp, hU, hν⟩,
   fun p => by
    obtain ⟨U, hp, -, hU, hν⟩ := h.future p univ univ_mem
    exact ⟨U, hp, hU, hν⟩⟩

end Local

/-! ### One isomorphic chart -/

section Chart

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {C : Causality M} {D : Causality X} {e : OpenPartialHomeomorph M X}

/-- A chart isomorphism is one for the time-reversed causalities. -/
theorem ChartIso.dual (h : ChartIso C D e) : ChartIso C.dual D.dual e :=
  fun U hU x hx y hy => ⟨(h U hU y hy x hx).1, (h U hU y hy x hx).2⟩

/-- **`lem:restriction_convexe` with the convex set inside an open set**: in a causally
arc-connected spacetime, two points of a set `V` causally convex in `M`, with `V` inside an open
set `S`, are related in `S` as soon as they are related in `M`. -/
theorem le_of_causallyConvexIn_of_subset (hcac : C.CausallyArcConnected) {V : Set M}
    (hV : C.CausallyConvexIn V ⊤) {S : Opens M} (hVS : V ⊆ S) {x y : M} (hx : x ∈ V)
    (hy : y ∈ V) (hxy : C.le ⊤ x y) : C.le S x y := by
  obtain ⟨c, hc, rfl, rfl⟩ := (hcac ⊤ le_rfl _ _).1.1 hxy
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ S := fun t ht => hVS (hV.2 _ hx _ hy
    (Causality.mem_diamond.2 ⟨hc.le_of_le le_rfl ht.1 ht.2, hc.le_of_le ht.1 ht.2 le_rfl⟩))
  have hcS : C.CausalCurveOn S c 0 1 := CurveOn.restrict hc le_rfl le_rfl le_top hmem
  exact hcS.le_of_le le_rfl zero_le_one le_rfl

/-- **The model's set first**: if `V ⊆ e.source` is causally convex in `M` and `U'` is causally
convex in the model with `e⁻¹(U') ⊆ V`, then `e.source ∩ e⁻¹(U')` is causally convex in `M`. -/
theorem ChartIso.causallyConvexIn_source_inter_preimage (h : ChartIso C D e)
    (hcac : C.CausallyArcConnected) {V : Set M} (hV : C.CausallyConvexIn V ⊤)
    (hVs : V ⊆ e.source) {U' : Set X} (hU' : D.CausallyConvexIn U' ⊤)
    (hU'V : ∀ y ∈ U', e.symm y ∈ V) : C.CausallyConvexIn (e.source ∩ e ⁻¹' U') ⊤ := by
  refine ⟨fun _ _ => trivial, fun x hx z hz y hy => ?_⟩
  obtain ⟨hxy, hyz⟩ := Causality.mem_diamond.1 hy
  have hxV : x ∈ V := by have := hU'V _ hx.2; rwa [e.left_inv hx.1] at this
  have hzV : z ∈ V := by have := hU'V _ hz.2; rwa [e.left_inv hz.1] at this
  have hyV : y ∈ V := hV.2 x hxV z hzV hy
  have hys : y ∈ e.source := hVs hyV
  -- `≤_M` is `≤` of the source along `V` (causal arc-connectedness), which the chart carries
  have h1 : C.le (chartSource e) x y := le_of_causallyConvexIn_of_subset hcac hV hVs hxV hyV hxy
  have h2 : C.le (chartSource e) y z := le_of_causallyConvexIn_of_subset hcac hV hVs hyV hzV hyz
  have h1' := D.le_mono le_top ((h (chartSource e) le_rfl x hx.1 y hys).1.1 h1)
  have h2' := D.le_mono le_top ((h (chartSource e) le_rfl y hys z hz.1).1.1 h2)
  exact ⟨hys, hU'.2 _ hx.2 _ hz.2 (Causality.mem_diamond.2 ⟨h1', h2'⟩)⟩

end Chart

/-! ### `K⁻` through a bijection of open sets matching `≤` -/

section Transport

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {C : Causality M} {D : Causality X}

/-- **`K⁻` transport**: a map `f` from the open `U` onto the open `U'`, with a continuous inverse
`g`, matching `≤_U` with `≤_{U'}`, carries `K⁻_U(p)` into `K⁻_{U'}(f p)`. -/
theorem mem_Kminus_of_intertwine {U : Opens M} {U' : Opens X} {f : M → X} {g : X → M}
    (hg : ContinuousOn g U') (hfU : MapsTo f U U') (hgU : MapsTo g U' U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ U', f (g y) = y)
    (hle : ∀ x ∈ U, ∀ y ∈ U, C.le U x y ↔ D.le U' (f x) (f y)) {p w : M} (hp : p ∈ U)
    (hw : w ∈ U) (hK : w ∈ C.Kminus U {p}) : f w ∈ D.Kminus U' {f p} := by
  rw [Causality.mem_Kminus_singleton] at hK ⊢
  intro v hv
  have hfp : f p ∈ U' := hfU hp
  have hfw : f w ∈ U' := hfU hw
  -- the sequence read in `M` converges to `p`
  have hu : Tendsto (fun n => g (v n)) atTop (𝓝 p) := by
    have := ((hg.continuousAt (U'.isOpen.mem_nhds hfp)).tendsto).comp hv
    rwa [hgf p hp] at this
  obtain ⟨N, hwJ, hN⟩ := hK _ hu
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hv.eventually (U'.isOpen.mem_nhds hfp))
  have hmaps : MapsTo g (D.Jminus U' {f p}) (C.Jminus U {p}) := fun z' hz' => by
    have hz'p : D.le U' z' (f p) := Precausality.mem_Jminus_singleton.1 hz'
    have hz'U : z' ∈ U' := D.le_mem_left hz'p
    refine Precausality.mem_Jminus_singleton.2 ((hle (g z') (hgU hz'U) p hp).2 ?_)
    rwa [hfg z' hz'U]
  have ht : Tendsto g (𝓝[D.Jminus U' {f p}] (f w)) (𝓝[C.Jminus U {p}] w) := by
    have := ((hg.continuousAt (U'.isOpen.mem_nhds hfw)).continuousWithinAt
      (s := D.Jminus U' {f p})).tendsto_nhdsWithin hmaps
    rwa [hgf w hw] at this
  refine ⟨max N N₁, Precausality.mem_Jminus_singleton.2 ((hle w hw p hp).1
    (Precausality.mem_Jminus_singleton.1 hwJ)), ?_⟩
  refine mem_of_superset (inter_mem (ht hN) self_mem_nhdsWithin) ?_
  rintro z' ⟨hz'S, hz'A⟩
  refine ⟨hz'A, mem_iInter₂.2 fun n hn => ?_⟩
  have hz'U : z' ∈ U' := D.le_mem_left (Precausality.mem_Jminus_singleton.1 hz'A)
  have hvn : v n ∈ U' := hN₁ n ((le_max_right _ _).trans hn)
  have h1 : C.le U (g z') (g (v n)) :=
    Precausality.mem_Jminus_singleton.1 (mem_iInter₂.1 hz'S.2 n ((le_max_left _ _).trans hn))
  have h2 := (hle (g z') (hgU hz'U) (g (v n)) (hgU hvn)).1 h1
  rw [hfg z' hz'U, hfg (v n) hvn] at h2
  exact Precausality.mem_Jminus_singleton.2 h2

end Transport

section ChartMeasures

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {C : Causality M} {D : Causality X} {e : OpenPartialHomeomorph M X}

/-- `≤` read backwards through a chart isomorphism. -/
theorem ChartIso.symm_le_iff (h : ChartIso C D e) {U : Opens M} (hU : U ≤ chartSource e)
    {x' y' : X} (hx' : x' ∈ chartImage e U) (hy' : y' ∈ chartImage e U) :
    D.le (chartImage e U) x' y' ↔ C.le U (e.symm x') (e.symm y') := by
  obtain ⟨x, hxs, hxU, rfl, -⟩ := exists_of_mem_chartImage hx'
  obtain ⟨y, hys, hyU, rfl, -⟩ := exists_of_mem_chartImage hy'
  rw [e.left_inv hxs, e.left_inv hys]
  exact (h U hU x hxU y hyU).1.symm

/-- The chart facts used by the transport lemmas, in one place. -/
theorem chartImage_facts {U : Opens M} (hU : U ≤ chartSource e) :
    ContinuousOn e.symm (chartImage e U) ∧ ContinuousOn e U ∧
      MapsTo e U (chartImage e U) ∧ MapsTo e.symm (chartImage e U) U ∧
      (∀ x ∈ U, e.symm (e x) = x) ∧ ∀ y ∈ chartImage e U, e (e.symm y) = y := by
  have htgt : ((chartImage e U : Opens X) : Set X) ⊆ e.target := by
    rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
    exact e.map_source hz
  refine ⟨e.continuousOn_symm.mono htgt, e.continuousOn.mono hU,
    fun x hx => mem_chartImage_of_mem (hU hx) hx, fun y hy => ?_,
    fun x hx => e.left_inv (hU hx), fun y hy => e.right_inv (htgt hy)⟩
  obtain ⟨z, -, hzU, -, hz⟩ := exists_of_mem_chartImage hy
  rw [hz]
  exact hzU

/-- **`J⁻` through a chart isomorphism.** -/
theorem ChartIso.symm_mem_Jminus_iff (h : ChartIso C D e) {U : Opens M} (hU : U ≤ chartSource e)
    {A : Set M} (hA : A ⊆ U) {z' : X} (hz' : z' ∈ chartImage e U) :
    e.symm z' ∈ C.Jminus U A ↔ z' ∈ D.Jminus (chartImage e U) (e '' A) := by
  obtain ⟨x, hxs, hxU, rfl, -⟩ := exists_of_mem_chartImage hz'
  rw [e.left_inv hxs]
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact ⟨e a, mem_image_of_mem e ha, (h U hU x hxU a (hA ha)).1.1 hxa⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, hxa⟩
    exact ⟨a, ha, (h U hU x hxU a (hA ha)).1.2 hxa⟩

/-- **`K⁻` through a chart isomorphism** (the K-transport lemma). -/
theorem ChartIso.symm_mem_Kminus_iff (h : ChartIso C D e) {U : Opens M} (hU : U ≤ chartSource e)
    {A : Set M} (hA : A ⊆ U) {z' : X} (hz' : z' ∈ chartImage e U) :
    e.symm z' ∈ C.Kminus U A ↔ z' ∈ D.Kminus (chartImage e U) (e '' A) := by
  obtain ⟨hcs, hce, hmU, hmU', hli, hri⟩ := chartImage_facts (e := e) hU
  obtain ⟨x, hxs, hxU, rfl, -⟩ := exists_of_mem_chartImage hz'
  rw [e.left_inv hxs, Causality.Kminus_eq_biUnion, Causality.Kminus_eq_biUnion (A := e '' A),
    biUnion_image]
  simp only [mem_iUnion₂, exists_prop]
  refine exists_congr fun a => and_congr_right fun ha => ⟨fun hK => ?_, fun hK => ?_⟩
  · exact mem_Kminus_of_intertwine hcs hmU hmU' hli hri
      (fun x hx y hy => (h U hU x hx y hy).1) (hA ha) hxU hK
  · have := mem_Kminus_of_intertwine (C := D) (D := C) hce hmU' hmU hri hli
      (fun x' hx' y' hy' => ChartIso.symm_le_iff h hU hx' hy') (hmU (hA ha)) (hmU hxU) hK
    rwa [hli x hxU, hli a (hA ha)] at this

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace X] [BorelSpace X]

/-- **A measure admissible in the past on `e(U)` carried back to `U`** through a chart
isomorphism, `U` in the source. -/
theorem ChartIso.admissiblePastOn [R1Space M] (h : ChartIso C D e) {U : Opens M}
    (hU : U ≤ chartSource e) {μ : Measure X} (hμ : D.AdmissiblePastOn (chartImage e U) μ) :
    ∃ ν : Measure M, C.AdmissiblePastOn U ν := by
  have hUs : (U : Set M) ⊆ e.source := hU
  have himg : e '' (U : Set M) = (chartImage e U : Set X) := (coe_chartImage_of_le hU).symm
  -- the chart restricted to `U` is a homeomorphism onto `e(U)`
  let φ : (U : Set M) ≃ₜ (chartImage e U : Set X) := e.homeomorphOfImageSubsetSource hUs himg
  haveI := hμ.regular
  obtain ⟨ν', hν'reg, hν'⟩ :=
    exists_regular_subtype_of_compl_null (chartImage e U).isOpen hμ.carried
  haveI := hν'reg
  have hemb := MeasurableEmbedding.subtype_coe (chartImage e U).isOpen.measurableSet
  have hμs : ∀ s : Set X, μ s = ν' (Subtype.val ⁻¹' s) := fun s => by
    rw [← hν', hemb.map_apply]
  have hφ : ∀ s : Set (U : Set M), Measure.map φ.symm ν' s = ν' (φ.symm ⁻¹' s) := fun s =>
    MeasurableEquiv.map_apply φ.symm.toMeasurableEquiv s
  -- a trace on `U` read through `φ` is the trace on `e(U)` of the transported set
  have htr : ∀ (S : Set M) (S' : Set X), (∀ z' ∈ chartImage e U, e.symm z' ∈ S ↔ z' ∈ S') →
      φ.symm ⁻¹' (Subtype.val ⁻¹' S) = Subtype.val ⁻¹' S' := fun S S' hS => by
    ext z'
    exact hS z' z'.2
  have hAimg : ∀ A : Set M, A ⊆ U → e '' A ⊆ chartImage e U := fun A hA => by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_chartImage_of_mem (hUs (hA ha)) (hA ha)
  refine ⟨Measure.map Subtype.val (Measure.map φ.symm ν'),
    (Causality.admissiblePastOn_map_subtype_iff (C := C) _).2 ⟨Measure.Regular.map φ.symm, ?_,
      fun p q hpq hne => ?_, fun A hA => ?_⟩⟩
  · rw [hφ, preimage_univ]
    have := hμ.finite
    rwa [hμs, preimage_univ] at this
  · have hp : p ∈ U := C.le_mem_left hpq
    have hq : q ∈ U := C.le_mem_right hpq
    rw [hφ, htr _ (D.Jminus (chartImage e U) {e q} \ D.Jminus (chartImage e U) {e p})
      fun z' hz' => by
        rw [Set.mem_sdiff, Set.mem_sdiff, ChartIso.symm_mem_Jminus_iff h hU (singleton_subset_iff.2 hq) hz',
          ChartIso.symm_mem_Jminus_iff h hU (singleton_subset_iff.2 hp) hz', image_singleton,
          image_singleton], ← hμs]
    exact hμ.pos ((h U hU p hp q hq).1.1 hpq) fun heq => hne (e.injOn (hUs hp) (hUs hq) heq)
  · rw [hφ, htr _ (D.Jminus (chartImage e U) (e '' A) \ D.Kminus (chartImage e U) (e '' A))
      fun z' hz' => by
        rw [Set.mem_sdiff, Set.mem_sdiff, ChartIso.symm_mem_Jminus_iff h hU hA hz',
          ChartIso.symm_mem_Kminus_iff h hU hA hz'], ← hμs]
    exact hμ.null _ (hAimg A hA)

/-- `ChartIso.admissiblePastOn`, future. -/
theorem ChartIso.admissibleFutureOn [R1Space M] (h : ChartIso C D e) {U : Opens M}
    (hU : U ≤ chartSource e) {μ : Measure X} (hμ : D.AdmissibleFutureOn (chartImage e U) μ) :
    ∃ ν : Measure M, C.AdmissibleFutureOn U ν := by
  obtain ⟨ν, hν⟩ := ChartIso.admissiblePastOn (C := C.dual) (D := D.dual) (ChartIso.dual h) hU
    (Causality.dual_admissiblePastOn.2 hμ)
  exact ⟨ν, Causality.dual_admissiblePastOn.1 hν⟩

/-- **Hypothesis (i) of `prop:mesure_dieckmann_topo` at a point of the source, past, in every
neighbourhood**: in a causally arc-connected, strongly causal `M`, a chart isomorphism at `p` into
a model with measures in every neighbourhood of `e p` gives, inside every neighbourhood `N` of
`p`, an open neighbourhood `U ⊆ e.source` of `p`, causally convex in `M`, whose image `e(U)` is
causally convex in the model, carrying a measure admissible in the past. The model's set is
chosen first (`U = e⁻¹(U')`), so `e(U) = U'`. -/
theorem ChartIso.exists_admissiblePastOn [R1Space M] (h : ChartIso C D e)
    (hcac : C.CausallyArcConnected) (hSC : C.StronglyCausal) {p : M} (hp : p ∈ e.source)
    (hD : ∀ N ∈ 𝓝 (e p), ∃ U' : Opens X, e p ∈ U' ∧ (U' : Set X) ⊆ N ∧
      D.CausallyConvexIn (U' : Set X) ⊤ ∧ ∃ μ : Measure X, D.AdmissiblePastOn U' μ)
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ N ∧ U ≤ chartSource e ∧
      C.CausallyConvexIn (U : Set M) ⊤ ∧ D.CausallyConvexIn (chartImage e U : Set X) ⊤ ∧
      ∃ ν : Measure M, C.AdmissiblePastOn U ν := by
  -- strong causality (DEC-7): a neighbourhood `V ⊆ e.source ∩ N` of `p`, causally convex in `M`
  obtain ⟨V, hVn, hVsN, hV⟩ := hSC p (e.source ∩ N) (inter_mem (e.open_source.mem_nhds hp) hN)
  have hVs : V ⊆ e.source := hVsN.trans inter_subset_left
  have hN' : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e p) := by
    refine inter_mem (e.open_target.mem_nhds (e.map_source hp)) ?_
    apply e.continuousAt_symm (e.map_source hp)
    rw [e.left_inv hp]
    exact hVn
  -- the model's set first: `U'` causally convex in the model, inside `e(V)`
  obtain ⟨U', hpU', hU'N, hU'c, μ, hμ⟩ := hD _ hN'
  let U : Opens M := ⟨e.source ∩ e ⁻¹' U', e.isOpen_inter_preimage U'.isOpen⟩
  have hUs : U ≤ chartSource e := fun x hx => hx.1
  have hUV : (U : Set M) ⊆ V := fun x hx => by
    have := (hU'N hx.2).2
    rwa [mem_preimage, e.left_inv hx.1] at this
  have hUU' : chartImage e U = U' := by
    apply SetLike.coe_injective
    ext y
    constructor
    · rintro ⟨x, ⟨-, -, hx⟩, rfl⟩
      exact hx
    · intro hy
      have hyt : y ∈ e.target := (hU'N hy).1
      refine ⟨e.symm y, ⟨e.map_target hyt, e.map_target hyt, ?_⟩, e.right_inv hyt⟩
      show e (e.symm y) ∈ U'
      rw [e.right_inv hyt]
      exact hy
  obtain ⟨ν, hν⟩ := ChartIso.admissiblePastOn h hUs (by rw [hUU']; exact hμ)
  exact ⟨U, ⟨hp, hpU'⟩, hUV.trans (hVsN.trans inter_subset_right), hUs,
    ChartIso.causallyConvexIn_source_inter_preimage h hcac hV hVs hU'c fun y hy => (hU'N hy).2,
    by rw [hUU']; exact hU'c, ν, hν⟩

/-- `ChartIso.exists_admissiblePastOn`, future. -/
theorem ChartIso.exists_admissibleFutureOn [R1Space M] (h : ChartIso C D e)
    (hcac : C.CausallyArcConnected) (hSC : C.StronglyCausal) {p : M} (hp : p ∈ e.source)
    (hD : ∀ N ∈ 𝓝 (e p), ∃ U' : Opens X, e p ∈ U' ∧ (U' : Set X) ⊆ N ∧
      D.CausallyConvexIn (U' : Set X) ⊤ ∧ ∃ μ : Measure X, D.AdmissibleFutureOn U' μ)
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ U : Opens M, p ∈ U ∧ (U : Set M) ⊆ N ∧ U ≤ chartSource e ∧
      C.CausallyConvexIn (U : Set M) ⊤ ∧ D.CausallyConvexIn (chartImage e U : Set X) ⊤ ∧
      ∃ ν : Measure M, C.AdmissibleFutureOn U ν := by
  obtain ⟨U, hpU, hUN, hUs, hU, hU', ν, hν⟩ := ChartIso.exists_admissiblePastOn
    (C := C.dual) (D := D.dual) (ChartIso.dual h) (Causality.dual_causallyArcConnectedOn.2 hcac)
    (Causality.dual_stronglyCausal.2 hSC) hp (fun N hN => by
      obtain ⟨U', h1, h2, h3, μ, hμ⟩ := hD N hN
      exact ⟨U', h1, h2, Causality.dual_causallyConvexIn.2 h3, μ,
        Causality.dual_admissiblePastOn.2 hμ⟩) hN
  exact ⟨U, hpU, hUN, hUs, Causality.dual_causallyConvexIn.1 hU,
    Causality.dual_causallyConvexIn.1 hU', ν, Causality.dual_admissiblePastOn.1 hν⟩

end ChartMeasures

/-! ### A cover by isomorphic charts -/

section Cover

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {A : Type z} {Xα : A → Type y} [∀ a, TopologicalSpace (Xα a)]
  {C : Causality M} {DX : Causality X} {DY : ∀ a, Causality (Xα a)}
  [MeasurableSpace M] [BorelSpace M] [R1Space M] [MeasurableSpace X] [BorelSpace X]
  [∀ a, MeasurableSpace (Xα a)] [∀ a, BorelSpace (Xα a)]

/-- **`ModelMeasures` in local form through a cover by isomorphic charts**: a causally
arc-connected, strongly causal `M` with an isomorphic chart at each point, into models with
measures in every neighbourhood, has measures in every neighbourhood. -/
theorem isoChartsCover_modelMeasuresLocal (h : IsoChartsCover C DX DY)
    (hcac : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hX : ModelMeasuresLocal DX)
    (hY : ∀ a, ModelMeasuresLocal (DY a)) : ModelMeasuresLocal C := by
  refine ⟨fun p N hN => ?_, fun p N hN => ?_⟩
  · rcases h p with ⟨e, hp, he⟩ | ⟨a, e, hp, he⟩
    · obtain ⟨U, h1, h2, -, h3, -, h4⟩ :=
        ChartIso.exists_admissiblePastOn he hcac hSC hp (hX.past (e p)) hN
      exact ⟨U, h1, h2, h3, h4⟩
    · obtain ⟨U, h1, h2, -, h3, -, h4⟩ :=
        ChartIso.exists_admissiblePastOn he hcac hSC hp ((hY a).past (e p)) hN
      exact ⟨U, h1, h2, h3, h4⟩
  · rcases h p with ⟨e, hp, he⟩ | ⟨a, e, hp, he⟩
    · obtain ⟨U, h1, h2, -, h3, -, h4⟩ :=
        ChartIso.exists_admissibleFutureOn he hcac hSC hp (hX.future (e p)) hN
      exact ⟨U, h1, h2, h3, h4⟩
    · obtain ⟨U, h1, h2, -, h3, -, h4⟩ :=
        ChartIso.exists_admissibleFutureOn he hcac hSC hp ((hY a).future (e p)) hN
      exact ⟨U, h1, h2, h3, h4⟩

/-- **`ModelMeasures` through a cover by isomorphic charts** (`isoChartsCover_modelMeasuresLocal`
with `N = M`). -/
theorem isoChartsCover_modelMeasures (h : IsoChartsCover C DX DY)
    (hcac : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hX : ModelMeasuresLocal DX)
    (hY : ∀ a, ModelMeasuresLocal (DY a)) : C.ModelMeasures :=
  (isoChartsCover_modelMeasuresLocal h hcac hSC hX hY).modelMeasures

end Cover

end MeasuresManifolds

end Causal
