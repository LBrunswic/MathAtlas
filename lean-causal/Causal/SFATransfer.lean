import Causal.GXStructure
import Causal.CausallyPlainLocZ

/-!
# Model-free transfer of local causal facts through isomorphic charts

Target `T-ett-sfa-local-e0`, scope (a) (ETT layer: no model, no `Causal.Port.*`, kb/0047). Cited,
**unmarked** (SCOPE): `rem:btz_pas_tarentin` — `ETT.tex:1358`, `rem:sing_tarentin` —
`ETT.tex:1364`. This module proves the chart half of « immediate from Definitions
\ref{defi:causal_Ealpha} and \ref{defi:causal_E0} read in a chart », for any model and any
family of models; the instance at `E₀`-manifolds is `Causal.Port.SFALocalE0`.

> Every point of a $\mass{\geq 0}$-manifold is strongly tarentin in the future, and the points
> which fail to be strongly tarentin in the past are exactly the BTZ points: this is immediate
> from Definitions \ref{defi:causal_Ealpha} and \ref{defi:causal_E0} read in a chart.
> (`rem:btz_pas_tarentin`, `ETT.tex:1358–1362`)

> Every $\mass{\geq0}$-manifold is a tarentin topological spacetime. (`rem:sing_tarentin`,
> `ETT.tex:1364–1366`)

## What is proved (no `sorry` in this file)

* **One chart** `e : M ⇀ Y`, a `ChartIso C D e` (`Causal.GXStructure`), `x ∈ e.source`. The local
  model facts of `Causal.CausallyPlainLocZ` (`E0LM.LocZplus`, `LocZminus`, `LocTarentin`,
  `LocNoPast`, `LocPastIn`, in every open set of `Y`) pass to `x` in every open set `W` of `M`:
  `ChartIso.exists_lt_right` (`Z⁺`), `ChartIso.exists_lt_left` (`Z⁻`, if `e x ∉ S`),
  `ChartIso.exists_mem_openDiamond` (tarentin), `ChartIso.not_lt_left` (no chronological past in
  the open sets inside the source, if `e x ∈ S`), `ChartIso.mem_of_le_left`,
  `ChartIso.pastLocal` (the causal past in the source stays in `e⁻¹(S)`). The relations of an
  open subset of the source are those of the model (`ChartIso`); those of `W` contain them
  (`lt_mono`, `le_mono`).
* **Topology through one chart**, no causality: compact neighbourhoods
  (`exists_isCompact_nhds_of_chart`) and non-isolated points (`nhdsNE_neBot_of_chart`).
* **A cover by isomorphic charts** into `X` or into one of the `Xα a` (`IsoChartsCover`, the
  shape of `Causal.IsoChartsCoverDEC25` without the `(G,X)` data): `LocZplus C` and
  `Z⁺ = M` (`IsoChartsCover.locZplus`, `.mem_Zplus`); `LocTarentin C` and `C.Tarentin`
  (`.locTarentin`, `.tarentin`); `LocZminus C T` and `M ∖ T ⊆ Z⁻` when every point off `T` has an
  isomorphic chart sending it off the model's set (`locZminus_of_charts`, `mem_Zminus_of_charts`);
  local compactness and no isolated point (`.locallyCompactSpace`, `.nhdsNE_neBot`).
* **The empty past from absolute minimality** (`Iminus_eq_empty_of_cover`): if `C` is absolutely
  minimal and `x` has no chronological past in any member of some open cover, then
  `I⁻(x) = ∅`; then `x ∉ Z⁻` (`notMem_Zminus_of_Iminus_eq_empty`).
* **Metrizability** from Hausdorff, second countable and locally compact
  (`metrizableSpace_of_locallyCompact`, Urysohn).
* **Absolute minimality cannot be dropped from `Iminus_eq_empty_of_cover`**: `topTotal D` is `D`
  on every open set `U ≠ M` and relates every pair at `M`; a chart with source `≠ M` which is an
  isomorphism for `D` is one for it (`chartIso_topTotal`), and every point is in its `Z⁻`
  (`topTotal_mem_Zminus`). Instance at `E₀`: `SFALocalE0.e0_topTotal_separates`.

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold, « read in a chart » | ⚠ abstracted: any `M` with a cover by charts that are `ChartIso`s onto open subsets of models; the `(G,X)` structure is not used |
| the model facts (`defi:causal_Ealpha`, `defi:causal_E0`) | named hypotheses on the models, in local form (`E0LM.Loc*`); discharged for `E₀` and `E^{1,2}` in `Causal.Port.SFALocalE0` |
| « the BTZ points » | ⚠ abstracted: a set `T`, with the hypothesis that each point off `T` has an isomorphic chart sending it off the model's set `S` |
| topological spacetime: Hausdorff, second countable (`ETT.tex:254`) | not used, except by `metrizableSpace_of_locallyCompact`, which carries them |

## SCOPE (disclosed)

* **Why unmarked.** Nothing here is about `E_{≥0}`-manifolds: the theorems hold for any cover by
  isomorphic charts. The rows are instantiated for `E₀`-manifolds in
  `Causal.Port.SFALocalE0`, and stay partial there (the `E_κ` models).
* **Why not over `IsoChartsCoverDEC25` itself.** `Causal.IsoChartsCoverDEC25` is defined in
  `Causal.Remarks.MassADEC25`, which imports `Causal.Port.E0Axioms` and `Causal.Port.E0SingularFlat`,
  over `SingularGXStructure` (`Causal.Port.SingularAtlas`). An ETT-layer module cannot import it.
  `IsoChartsCover` is its shape without the `(G,X)` data; the bridge
  `SFALocalE0.isoChartsCover_of_dec25` is one line.
* **Absolute minimality is used for `I⁻(x) = ∅`.** A `ChartIso` constrains the relations of the
  open subsets of its source, hence those of `M` only when a single chart's source is all of `M`;
  otherwise, without absolute minimality, `≪_M` may add pairs no chart sees (kb/0014).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u v y z

namespace SFATransfer

/-! ### One isomorphic chart -/

section Chart

variable {M : Type u} [TopologicalSpace M] {Y : Type v} [TopologicalSpace Y]
  {C : Causality M} {D : Causality Y} {e : OpenPartialHomeomorph M Y}

/-- **`Z⁺` through a chart**: if the model has `Z⁺` in every open set, so has every point of the
source of an isomorphic chart, in every open set of `M`. -/
theorem ChartIso.exists_lt_right (h : ChartIso C D e) (hD : E0LM.LocZplus D) {x : M}
    (hx : x ∈ e.source) {W : Opens M} (hxW : x ∈ W) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ z ∈ N, C.lt W x z := by
  set W' : Opens M := W ⊓ chartSource e ⊓ ⟨interior N, isOpen_interior⟩
  have hxW' : x ∈ W' := ⟨⟨hxW, hx⟩, mem_interior_iff_mem_nhds.2 hN⟩
  have hW'e : W' ≤ chartSource e := inf_le_left.trans inf_le_right
  have hex : e x ∈ chartImage e W' := mem_chartImage_of_mem hx hxW'
  obtain ⟨z', hz', hlt⟩ :=
    hD (chartImage e W') (e x) hex _ ((chartImage e W').isOpen.mem_nhds hex)
  obtain ⟨z, -, hzW', rfl, -⟩ := exists_of_mem_chartImage hz'
  exact ⟨z, interior_subset hzW'.2,
    C.lt_mono (inf_le_left.trans inf_le_left) ((h W' hW'e x hxW' z hzW').2.2 hlt)⟩

/-- **`Z⁻` through a chart**, at a point the chart sends off the model's set `S`. -/
theorem ChartIso.exists_lt_left (h : ChartIso C D e) {S : Set Y} (hD : E0LM.LocZminus D S)
    {x : M} (hx : x ∈ e.source) (hxS : e x ∉ S) {W : Opens M} (hxW : x ∈ W) {N : Set M}
    (hN : N ∈ 𝓝 x) : ∃ z ∈ N, C.lt W z x := by
  set W' : Opens M := W ⊓ chartSource e ⊓ ⟨interior N, isOpen_interior⟩
  have hxW' : x ∈ W' := ⟨⟨hxW, hx⟩, mem_interior_iff_mem_nhds.2 hN⟩
  have hW'e : W' ≤ chartSource e := inf_le_left.trans inf_le_right
  have hex : e x ∈ chartImage e W' := mem_chartImage_of_mem hx hxW'
  obtain ⟨z', hz', hlt⟩ :=
    hD (chartImage e W') (e x) hex hxS _ ((chartImage e W').isOpen.mem_nhds hex)
  obtain ⟨z, -, hzW', rfl, -⟩ := exists_of_mem_chartImage hz'
  exact ⟨z, interior_subset hzW'.2,
    C.lt_mono (inf_le_left.trans inf_le_left) ((h W' hW'e z hzW' x hxW').2.2 hlt)⟩

/-- **Tarentin through a chart**: small open diamonds of `W` about every point of the source. -/
theorem ChartIso.exists_mem_openDiamond (h : ChartIso C D e) (hD : E0LM.LocTarentin D) {x : M}
    (hx : x ∈ e.source) {W : Opens M} (hxW : x ∈ W) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ p ∈ N, ∃ q ∈ N, x ∈ C.openDiamond W p q := by
  set W' : Opens M := W ⊓ chartSource e ⊓ ⟨interior N, isOpen_interior⟩
  have hxW' : x ∈ W' := ⟨⟨hxW, hx⟩, mem_interior_iff_mem_nhds.2 hN⟩
  have hW'e : W' ≤ chartSource e := inf_le_left.trans inf_le_right
  have hW'W : W' ≤ W := inf_le_left.trans inf_le_left
  have hex : e x ∈ chartImage e W' := mem_chartImage_of_mem hx hxW'
  obtain ⟨p', hp', q', hq', hd⟩ :=
    hD (chartImage e W') (e x) hex _ ((chartImage e W').isOpen.mem_nhds hex)
  obtain ⟨p, -, hpW', rfl, -⟩ := exists_of_mem_chartImage hp'
  obtain ⟨q, -, hqW', rfl, -⟩ := exists_of_mem_chartImage hq'
  refine ⟨p, interior_subset hpW'.2, q, interior_subset hqW'.2, ?_⟩
  refine mem_interior.2 ⟨_, ?_, e.isOpen_inter_preimage isOpen_interior, ⟨hx, hd⟩⟩
  rintro w ⟨hw, hwd⟩
  obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 (interior_subset hwd)
  obtain ⟨w', hw', hw'W', hew, -⟩ := exists_of_mem_chartImage (D.le_mem_right h1)
  obtain rfl : w' = w := e.injOn hw' hw hew
  exact Causality.mem_diamond.2 ⟨C.le_mono hW'W ((h W' hW'e p hpW' w' hw'W').1.2 h1),
    C.le_mono hW'W ((h W' hW'e w' hw'W' q hqW').1.2 h2)⟩

/-- **No chronological past through a chart**, in the open sets inside the source, at a point the
chart sends into a set of the model with no chronological past. -/
theorem ChartIso.not_lt_left (h : ChartIso C D e) {S : Set Y} (hD : E0LM.LocNoPast D S) {x : M}
    (hxS : e x ∈ S) {W : Opens M} (hW : W ≤ chartSource e) (z : M) : ¬ C.lt W z x := by
  intro hzx
  exact hD (chartImage e W) (e x) hxS (e z)
    ((h W hW z (C.lt_mem_left hzx) x (C.lt_mem_right hzx)).2.1 hzx)

/-- **The causal past stays in `e⁻¹(S)`**, in the open sets inside the source, at a point the
chart sends into a set of the model whose causal past stays in it. -/
theorem ChartIso.mem_of_le_left (h : ChartIso C D e) {S : Set Y} (hD : E0LM.LocPastIn D S)
    {x : M} (hxS : e x ∈ S) {W : Opens M} (hW : W ≤ chartSource e) {z : M} (hz : C.le W z x) :
    z ∈ e.source ∧ e z ∈ S := by
  exact ⟨hW (C.le_mem_left hz), hD (chartImage e W) (e x) hxS (e z)
    ((h W hW z (C.le_mem_left hz) x (C.le_mem_right hz)).1.1 hz)⟩

/-- **`past_local` through a chart**: if the chart reflects `T` on `e⁻¹(S)`, the causal past of
`x` in the source stays in `T`. -/
theorem ChartIso.pastLocal (h : ChartIso C D e) {S : Set Y} (hD : E0LM.LocPastIn D S)
    {T : Set M} (hT : ∀ q ∈ e.source, e q ∈ S → q ∈ T) {x : M} (hx : x ∈ e.source)
    (hxS : e x ∈ S) : ∃ U : Opens M, x ∈ U ∧ ∀ q, C.le U q x → q ∈ T := by
  refine ⟨chartSource e, hx, fun q hq => ?_⟩
  obtain ⟨hq, hqS⟩ := ChartIso.mem_of_le_left h hD hxS le_rfl hq
  exact hT q hq hqS

variable (e) in
/-- A point of the source of a chart into a locally compact space has a basis of compact
neighbourhoods. -/
theorem exists_isCompact_nhds_of_chart [LocallyCompactSpace Y] {x : M} (hx : x ∈ e.source)
    {n : Set M} (hn : n ∈ 𝓝 x) : ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s := by
  have h1 : e '' (n ∩ e.source) ∩ e.target ∈ 𝓝 (e x) :=
    inter_mem (e.image_mem_nhds hx (inter_mem hn (e.open_source.mem_nhds hx)))
      (e.open_target.mem_nhds (e.map_source hx))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds h1
  refine ⟨e.symm '' K, ?_, ?_,
    hKc.image_of_continuousOn (e.continuousOn_symm.mono fun k hk => (hKsub hk).2)⟩
  · rw [← e.symm_map_nhds_eq hx]
    exact image_mem_map hK
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨⟨w, ⟨hwn, hws⟩, rfl⟩, -⟩ := hKsub hk
    rw [e.left_inv hws]
    exact hwn

variable (e) in
/-- A point of the source of a chart whose image is not isolated is not isolated. -/
theorem nhdsNE_neBot_of_chart {x : M} (hx : x ∈ e.source) (hY : (𝓝[≠] (e x)).NeBot) :
    (𝓝[≠] x).NeBot := by
  rw [Filter.neBot_iff, Ne, ← isOpen_singleton_iff_punctured_nhds]
  intro hopen
  have h := e.isOpen_image_of_subset_source hopen (singleton_subset_iff.2 hx)
  rw [image_singleton] at h
  exact not_isOpen_singleton (e x) h

end Chart

/-! ### A cover by isomorphic charts -/

section Cover

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X]
  {A : Type z} {Xα : A → Type y} [∀ a, TopologicalSpace (Xα a)]
  {C : Causality M} {DX : Causality X} {DY : ∀ a, Causality (Xα a)}

/-- **The isomorphic charts cover `M`**: at every point some chart into `X`, or into one of the
models `Xα a`, is an isomorphism for `C`. The shape of `Causal.IsoChartsCoverDEC25` without the
`(G,X)` data (SCOPE). -/
def IsoChartsCover (C : Causality M) (DX : Causality X) (DY : ∀ a, Causality (Xα a)) : Prop :=
  ∀ x : M, (∃ e : OpenPartialHomeomorph M X, x ∈ e.source ∧ ChartIso C DX e) ∨
    ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), x ∈ e.source ∧ ChartIso C (DY a) e

/-- **`Z⁺` in every open set** of `M`, from `Z⁺` in every open set of every model. -/
theorem IsoChartsCover.locZplus (h : IsoChartsCover C DX DY) (hX : E0LM.LocZplus DX)
    (hY : ∀ a, E0LM.LocZplus (DY a)) : E0LM.LocZplus C := by
  intro W x hxW N hN
  rcases h x with ⟨e, hx, he⟩ | ⟨a, e, hx, he⟩
  · exact ChartIso.exists_lt_right he hX hx hxW hN
  · exact ChartIso.exists_lt_right he (hY a) hx hxW hN

/-- **`Z⁺ = M`**: every point is strongly tarentin in the future. -/
theorem IsoChartsCover.mem_Zplus (h : IsoChartsCover C DX DY) (hX : E0LM.LocZplus DX)
    (hY : ∀ a, E0LM.LocZplus (DY a)) (p : M) : p ∈ C.Zplus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := h.locZplus hX hY ⊤ p trivial U hU
  exact ⟨z, Precausality.mem_Iplus_singleton.2 hz, hzU⟩

/-- **Tarentin in every open set** of `M`, from tarentin in every open set of every model. -/
theorem IsoChartsCover.locTarentin (h : IsoChartsCover C DX DY) (hX : E0LM.LocTarentin DX)
    (hY : ∀ a, E0LM.LocTarentin (DY a)) : E0LM.LocTarentin C := by
  intro W x hxW N hN
  rcases h x with ⟨e, hx, he⟩ | ⟨a, e, hx, he⟩
  · exact ChartIso.exists_mem_openDiamond he hX hx hxW hN
  · exact ChartIso.exists_mem_openDiamond he (hY a) hx hxW hN

/-- **`M` is tarentin** (`def:tarentin_spacetime`). -/
theorem IsoChartsCover.tarentin (h : IsoChartsCover C DX DY) (hX : E0LM.LocTarentin DX)
    (hY : ∀ a, E0LM.LocTarentin (DY a)) : C.Tarentin := by
  intro x U hU
  exact h.locTarentin hX hY ⊤ x trivial U hU

/-- **`Z⁻` in every open set off `T`**, when every point off `T` has an isomorphic chart sending
it off the model's set. -/
theorem locZminus_of_charts {SX : Set X} {SY : ∀ a, Set (Xα a)} {T : Set M}
    (hT : ∀ x ∉ T, (∃ e : OpenPartialHomeomorph M X, x ∈ e.source ∧ ChartIso C DX e ∧ e x ∉ SX) ∨
      ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), x ∈ e.source ∧ ChartIso C (DY a) e ∧
        e x ∉ SY a)
    (hX : E0LM.LocZminus DX SX) (hY : ∀ a, E0LM.LocZminus (DY a) (SY a)) :
    E0LM.LocZminus C T := by
  intro W x hxW hxT N hN
  rcases hT x hxT with ⟨e, hx, he, hxS⟩ | ⟨a, e, hx, he, hxS⟩
  · exact ChartIso.exists_lt_left he hX hx hxS hxW hN
  · exact ChartIso.exists_lt_left he (hY a) hx hxS hxW hN

/-- **`M ∖ T ⊆ Z⁻`**: the points with an isomorphic chart sending them off the model's set are
strongly tarentin in the past. -/
theorem mem_Zminus_of_charts {SX : Set X} {SY : ∀ a, Set (Xα a)} {T : Set M}
    (hT : ∀ x ∉ T, (∃ e : OpenPartialHomeomorph M X, x ∈ e.source ∧ ChartIso C DX e ∧ e x ∉ SX) ∨
      ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), x ∈ e.source ∧ ChartIso C (DY a) e ∧
        e x ∉ SY a)
    (hX : E0LM.LocZminus DX SX) (hY : ∀ a, E0LM.LocZminus (DY a) (SY a)) {x : M} (hx : x ∉ T) :
    x ∈ C.Zminus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := locZminus_of_charts hT hX hY ⊤ x trivial hx U hU
  exact ⟨z, Precausality.mem_Iminus_singleton.2 hz, hzU⟩

/-- **Local compactness** through a cover by charts into locally compact models. -/
theorem IsoChartsCover.locallyCompactSpace [LocallyCompactSpace X]
    [∀ a, LocallyCompactSpace (Xα a)] (h : IsoChartsCover C DX DY) : LocallyCompactSpace M := by
  refine ⟨fun x n hn => ?_⟩
  rcases h x with ⟨e, hx, -⟩ | ⟨a, e, hx, -⟩
  · exact exists_isCompact_nhds_of_chart e hx hn
  · exact exists_isCompact_nhds_of_chart e hx hn

/-- **No isolated point** through a cover by charts into models without isolated points. -/
theorem IsoChartsCover.nhdsNE_neBot (hXn : ∀ x : X, (𝓝[≠] x).NeBot)
    (hYn : ∀ a (y : Xα a), (𝓝[≠] y).NeBot) (h : IsoChartsCover C DX DY) (p : M) :
    (𝓝[≠] p).NeBot := by
  rcases h p with ⟨e, hx, -⟩ | ⟨a, e, hx, -⟩
  · exact nhdsNE_neBot_of_chart e hx (hXn _)
  · exact nhdsNE_neBot_of_chart e hx (hYn a _)

end Cover

/-! ### The empty past, and metrizability -/

section Global

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **`I⁻(x) = ∅` from absolute minimality**: if `x` has no chronological past in any member of
an open cover of `M` containing it, it has none in `M`. -/
theorem Iminus_eq_empty_of_cover (hmin : C.AbsolutelyMinimal) {S : Set (Opens M)}
    (hcov : ∀ y : M, ∃ O ∈ S, y ∈ O) {x : M} (hx : ∀ O ∈ S, x ∈ O → ∀ z, ¬ C.lt O z x) :
    C.Iminus ⊤ {x} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  have hlt : C.lt ⊤ z x := Precausality.mem_Iminus_singleton.1 hz
  have ht := ((Precausality.absolutelyMinimal_iff.1 hmin) S (fun y _ => hcov y) ⊤ le_rfl z x).2 hlt
  obtain ⟨w, -, O, hO, hwx⟩ := Relation.TransGen.tail'_iff.1 ht
  exact hx O hO (C.lt_mem_right hwx).2 w (C.lt_mono inf_le_right hwx)

/-- A point with empty chronological past is not strongly tarentin in the past. -/
theorem notMem_Zminus_of_Iminus_eq_empty {x : M} (h : C.Iminus ⊤ {x} = ∅) : x ∉ C.Zminus := by
  intro hx
  obtain ⟨z, hz, -⟩ := hx univ univ_mem
  rw [h] at hz
  exact hz

/-- **Metrizability** (Urysohn): a Hausdorff, second countable, locally compact space is
metrizable. -/
theorem metrizableSpace_of_locallyCompact [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace M] : MetrizableSpace M := by
  infer_instance

end Global

/-! ### Absolute minimality cannot be dropped: `topTotal` -/

section TopTotal

variable {M : Type u} [TopologicalSpace M]

/-- **`D` with every pair related at `M`**: the relations of every open set `U ≠ M` are those of
`D`; at `U = M` every pair is causally and chronologically related. A causality with no gluing
(kb/0014). -/
def topTotal (D : Causality M) : Causality M where
  le U x y := U = ⊤ ∨ D.le U x y
  lt U x y := U = ⊤ ∨ D.lt U x y
  le_mem_left {U x y} h := by
    rcases h with rfl | h
    · trivial
    · exact D.le_mem_left h
  le_mem_right {U x y} h := by
    rcases h with rfl | h
    · trivial
    · exact D.le_mem_right h
  lt_mem_left {U x y} h := by
    rcases h with rfl | h
    · trivial
    · exact D.lt_mem_left h
  lt_mem_right {U x y} h := by
    rcases h with rfl | h
    · trivial
    · exact D.lt_mem_right h
  le_refl hx := Or.inr (D.le_refl hx)
  le_trans {U x y z} h₁ h₂ := by
    rcases h₁ with h | h₁
    · exact Or.inl h
    · rcases h₂ with h | h₂
      · exact Or.inl h
      · exact Or.inr (D.le_trans h₁ h₂)
  lt_trans {U x y z} h₁ h₂ := by
    rcases h₁ with h | h₁
    · exact Or.inl h
    · rcases h₂ with h | h₂
      · exact Or.inl h
      · exact Or.inr (D.lt_trans h₁ h₂)
  le_mono {U V} hVU {x y} h := by
    rcases h with rfl | h
    · exact Or.inl (top_le_iff.1 hVU)
    · exact Or.inr (D.le_mono hVU h)
  lt_mono {U V} hVU {x y} h := by
    rcases h with rfl | h
    · exact Or.inl (top_le_iff.1 hVU)
    · exact Or.inr (D.lt_mono hVU h)
  le_of_lt h := h.imp id D.le_of_lt
  isOpen_lt_right U x := by
    show IsOpen ({_y | U = ⊤} ∪ {y | D.lt U x y})
    exact isOpen_const.union (D.isOpen_lt_right U x)
  isOpen_lt_left U x := by
    show IsOpen ({_y | U = ⊤} ∪ {y | D.lt U y x})
    exact isOpen_const.union (D.isOpen_lt_left U x)

variable {D : Causality M} {U : Opens M} {x y : M}

theorem topTotal_le_iff (hU : U ≠ ⊤) : (topTotal D).le U x y ↔ D.le U x y := or_iff_right hU

theorem topTotal_lt_iff (hU : U ≠ ⊤) : (topTotal D).lt U x y ↔ D.lt U x y := or_iff_right hU

/-- A chart whose source is not all of `M` is an isomorphism for `topTotal D` as soon as it is one
for `D`. -/
theorem chartIso_topTotal {Y : Type v} [TopologicalSpace Y] {DY : Causality Y}
    {e : OpenPartialHomeomorph M Y} (h : ChartIso D DY e) (hs : chartSource e ≠ ⊤) :
    ChartIso (topTotal D) DY e := by
  intro V hV a ha b hb
  have hV' : V ≠ ⊤ := fun h' => hs (top_le_iff.1 (h' ▸ hV))
  rw [topTotal_le_iff hV', topTotal_lt_iff hV']
  exact h V hV a ha b hb

/-- Every point is strongly tarentin in the past for `topTotal D`. -/
theorem topTotal_mem_Zminus (D : Causality M) (p : M) : p ∈ (topTotal D).Zminus :=
  fun _ hU => ⟨p, Precausality.mem_Iminus_singleton.2 (Or.inl rfl), mem_of_mem_nhds hU⟩

/-- The identity of a space, restricted to an open set, is an isomorphism of any causality onto
itself (`Causal.chartIso_refl_restrOpen`, which is for `ℝ`, for any space). -/
theorem chartIso_restrOpen_refl (D : Causality M) {s : Set M} (hs : IsOpen s) :
    ChartIso D D ((OpenPartialHomeomorph.refl M).restrOpen s hs) := by
  intro V hV a _ b _
  have himg : chartImage ((OpenPartialHomeomorph.refl M).restrOpen s hs) V = V := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hV]
    simp
  rw [himg]
  exact ⟨Iff.rfl, Iff.rfl⟩

end TopTotal

end SFATransfer

end Causal
