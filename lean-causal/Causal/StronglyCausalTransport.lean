import Causal.DiamondConfinement

/-!
# Strong causality through a chart isomorphism, and local strong causality from charts

Programme target `T-loc-time-cylinder-lsc` (`programme/roadmap.toml`; the ETT-layer half, the
model-free transport (1)). No ETT label is marked.

* `ChartIso.causallyConvexIn_image_iff` — a chart isomorphism carries causal convexity in an open
  `W` of its source to causal convexity in the image `e(W)`, and back.
* `ChartIso.stronglyCausalOn_iff` — for `W` in the source, `W` is strongly causal as a spacetime
  iff `e(W)` is; `ChartIso.stronglyCausalOn_chartSource` (the source, from a strongly causal model)
  and `ChartIso.stronglyCausalOn_of_le`.
* `Causality.locallyStronglyCausal_of_chartIso` — a causality chart-isomorphic near each point to
  locally strongly causal ones (a model per point, in any universe) is locally strongly causal;
  `Causality.locallyStronglyCausal_of_forall_chartIso` (one model) and
  `Causality.locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal` (one strongly causal
  model, the form the flat instance uses).
* `IsCausalIso.stronglyCausalOn_iff`, `IsCausalIso.locallyStronglyCausal_iff` — the new ladder
  node `locally_strongly_causal` is invariant under causal isomorphisms, as every other
  causality-sort node is (`Causal.CausalIsoInvariance`).

> The model-free transport (a Causal.ChartIso carries StronglyCausalOn; a causality
> chart-isomorphic near each point to strongly causal ones is locally strongly causal) in a new
> ETT-layer module (`programme/roadmap.toml`, `T-loc-time-cylinder-lsc`, title)

> a point has an open neighbourhood that the chart carries isomorphically onto an open set of 𝐌ⁿ
> (an interval of the timelike line when d = 0), where Minkowski's causality is strongly causal as
> a spacetime, and a ChartIso transports causal convexity in W ≤ chartSource (J_W read through the
> chart) (the same block, `evidence`)

## Hypothesis checklist

| claim | here |
|---|---|
| a `ChartIso` carries `StronglyCausalOn` | ✓ both ways, for every open `W ≤ chartSource e` (`stronglyCausalOn_iff`) |
| the models strongly causal | ⚠ weakened: locally strongly causal suffices (`locallyStronglyCausal_of_chartIso`); strongly causal is the corollary `…_of_stronglyCausal` |
| one chart at each point | ✓ carried: `p ∈ e.source` and `ChartIso C D e`; no atlas, no compatibility of the charts, no separation axiom on `M` or on the models |

## SCOPE (disclosed)

* **No label.** The target is a ladder separation of the ETT programme; nothing of `ETT.tex` is
  certified here.
* **Layer.** One import, `Causal.DiamondConfinement` (where `StronglyCausalOn` and
  `LocallyStronglyCausal` are defined), which reaches `Causal.GXStructure` (`ChartIso`) and
  `Causal.CausalIsoInvariance` (`IsCausalIso`) through `Causal.TimelikeHomotopy`; no
  `Causal.Minkowski`, `Static`, `Flat.*`, `Model.*`, `Port.*` or `SingularFlat`, directly or
  transitively (`tools/ladder.py`'s `model_path` is `None` for that import, kb/0247).
* **Not here.** The flat instance and the separation of the time cylinder are model facts:
  `Causal.Model.TimeCylinderLSC`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u v

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]

namespace ChartIso

variable {C : Causality M} {D : Causality X} {e : OpenPartialHomeomorph M X} {W : Opens M}

/-- **Causal convexity through a chart isomorphism**: for `V ⊆ W ≤ chartSource e`, `V` is
causally convex in `W` iff `e(V)` is causally convex in `e(W)` (`J_W(a, b)` is read through the
chart as `J_{e(W)}(e a, e b)`). -/
theorem causallyConvexIn_image_iff (h : ChartIso C D e) (hW : W ≤ chartSource e) {V : Set M}
    (hV : V ⊆ W) : C.CausallyConvexIn V W ↔ D.CausallyConvexIn (e '' V) (chartImage e W) := by
  have hWs : (W : Set M) ⊆ e.source := hW
  constructor
  · rintro ⟨-, hc⟩
    refine ⟨fun _ ⟨a, ha, hae⟩ => hae ▸ mem_chartImage_of_mem (hWs (hV ha)) (hV ha), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z' hz'
    obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz'
    obtain ⟨z, -, hzW, rfl, -⟩ := exists_of_mem_chartImage (D.le_mem_right h1)
    refine ⟨z, hc a ha b hb (Causality.mem_diamond.2 ⟨?_, ?_⟩), rfl⟩
    · exact (h W hW a (hV ha) z hzW).1.2 h1
    · exact (h W hW z hzW b (hV hb)).1.2 h2
  · rintro ⟨-, hc⟩
    refine ⟨hV, fun a ha b hb z hz => ?_⟩
    obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz
    have hzW : z ∈ W := C.le_mem_right h1
    obtain ⟨v, hv, hve⟩ := hc (e a) (mem_image_of_mem e ha) (e b) (mem_image_of_mem e hb)
      (Causality.mem_diamond.2 ⟨(h W hW a (hV ha) z hzW).1.1 h1,
        (h W hW z hzW b (hV hb)).1.1 h2⟩)
    rwa [← e.injOn (hWs (hV hv)) (hWs hzW) hve]

/-- **A chart isomorphism carries strong causality as a spacetime**, both ways: for an open
`W ≤ chartSource e`, `W` is strongly causal as a spacetime iff its image `e(W)` is. -/
theorem stronglyCausalOn_iff (h : ChartIso C D e) (hW : W ≤ chartSource e) :
    C.StronglyCausalOn W ↔ D.StronglyCausalOn (chartImage e W) := by
  have hWs : (W : Set M) ⊆ e.source := hW
  constructor
  · intro hC p' hp' U' hU'
    obtain ⟨p, hps, hpW, rfl, -⟩ := exists_of_mem_chartImage hp'
    obtain ⟨V, hV, hVU, hVc⟩ := hC p hpW (e ⁻¹' U') ((e.continuousAt hps).preimage_mem_nhds hU')
    exact ⟨e '' V, e.image_mem_nhds hps hV, image_subset_iff.2 hVU,
      (h.causallyConvexIn_image_iff hW hVc.1).1 hVc⟩
  · intro hD p hpW U hU
    have hpt : e p ∈ e.target := e.map_source (hWs hpW)
    have hU' : e.symm ⁻¹' U ∈ 𝓝 (e p) := (e.continuousAt_symm hpt).preimage_mem_nhds
      (by rwa [e.left_inv (hWs hpW)])
    obtain ⟨V', hV', hV'U, hV'c⟩ :=
      hD (e p) (mem_chartImage_of_mem (hWs hpW) hpW) (e.symm ⁻¹' U) hU'
    have hV'W : ∀ y ∈ V', e.symm y ∈ W ∧ e (e.symm y) = y := fun y hy => by
      obtain ⟨z, hzs, hzW, rfl, hz⟩ := exists_of_mem_chartImage (hV'c.1 hy)
      rw [hz]
      exact ⟨hzW, rfl⟩
    have himg : e '' (e.symm '' V') = V' := by
      ext y
      constructor
      · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        rwa [(hV'W y' hy').2]
      · intro hy
        exact ⟨e.symm y, mem_image_of_mem _ hy, (hV'W y hy).2⟩
    have hsub : e.symm '' V' ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hV'W y hy).1
    refine ⟨e.symm '' V', ?_, image_subset_iff.2 hV'U,
      (h.causallyConvexIn_image_iff hW hsub).2 (by rw [himg]; exact hV'c)⟩
    have := e.symm.image_mem_nhds (x := e p) (by rwa [e.symm_source]) hV'
    rwa [e.left_inv (hWs hpW)] at this

/-- The direction used: `W ≤ chartSource e` is strongly causal as a spacetime once its image is. -/
theorem stronglyCausalOn_of_le (h : ChartIso C D e) (hW : W ≤ chartSource e)
    (hD : D.StronglyCausalOn (chartImage e W)) : C.StronglyCausalOn W :=
  (h.stronglyCausalOn_iff hW).2 hD

/-- **The source of a chart isomorphism onto a strongly causal model is strongly causal as a
spacetime.** -/
theorem stronglyCausalOn_chartSource (h : ChartIso C D e) (hD : D.StronglyCausal) :
    C.StronglyCausalOn (chartSource e) :=
  h.stronglyCausalOn_of_le le_rfl ((Causality.stronglyCausalOn_top.2 hD).mono le_top)

end ChartIso

namespace Causality

variable {C : Causality M}

/-- **Local strong causality from charts**: a causality which, near each point, is
chart-isomorphic to a locally strongly causal one (a model for each point, in any universe) is
locally strongly causal. -/
theorem locallyStronglyCausal_of_chartIso
    (h : ∀ p : M, ∃ (X : Type v) (_ : TopologicalSpace X) (D : Causality X)
      (e : OpenPartialHomeomorph M X), p ∈ e.source ∧ ChartIso C D e ∧ D.LocallyStronglyCausal) :
    C.LocallyStronglyCausal := by
  intro p
  obtain ⟨X, _, D, e, hps, he, hD⟩ := h p
  obtain ⟨W', hpW', hW'⟩ := hD (e p)
  let W : Opens M := ⟨e.source ∩ e ⁻¹' W', e.isOpen_inter_preimage W'.isOpen⟩
  have hWs : W ≤ chartSource e := fun _ hz => hz.1
  refine ⟨W, ⟨hps, hpW'⟩, he.stronglyCausalOn_of_le hWs (hW'.mono ?_)⟩
  rintro _ ⟨z, ⟨-, -, hz⟩, rfl⟩
  exact hz

/-- One model `D`, locally strongly causal, and a chart isomorphism onto it at every point. -/
theorem locallyStronglyCausal_of_forall_chartIso {D : Causality X} (hD : D.LocallyStronglyCausal)
    (h : ∀ p : M, ∃ e : OpenPartialHomeomorph M X, p ∈ e.source ∧ ChartIso C D e) :
    C.LocallyStronglyCausal :=
  locallyStronglyCausal_of_chartIso fun p => by
    obtain ⟨e, hps, he⟩ := h p
    exact ⟨X, inferInstance, D, e, hps, he, hD⟩

/-- **A causality chart-isomorphic at every point to a strongly causal model is locally strongly
causal.** -/
theorem locallyStronglyCausal_of_forall_chartIso_of_stronglyCausal {D : Causality X}
    (hD : D.StronglyCausal)
    (h : ∀ p : M, ∃ e : OpenPartialHomeomorph M X, p ∈ e.source ∧ ChartIso C D e) :
    C.LocallyStronglyCausal :=
  locallyStronglyCausal_of_forall_chartIso hD.locallyStronglyCausal h

end Causality

namespace IsCausalIso

variable {C : Causality M} {D : Causality X} {e : M ≃ₜ X}

/-- A causal isomorphism carries strong causality as a spacetime of every open set. -/
theorem stronglyCausalOn_iff (h : IsCausalIso C D e) {W : Opens M} :
    C.StronglyCausalOn W ↔ D.StronglyCausalOn (e.opensCongr W) := by
  rw [← chartImage_toOpenPartialHomeomorph]
  exact (isCausalIso_iff_chartIso.1 h).stronglyCausalOn_iff (fun _ _ => mem_univ _)

/-- **`locally_strongly_causal` is invariant under causal isomorphisms.** -/
theorem locallyStronglyCausal_iff (h : IsCausalIso C D e) :
    C.LocallyStronglyCausal ↔ D.LocallyStronglyCausal :=
  ⟨fun hC => Causality.locallyStronglyCausal_of_forall_chartIso hC fun _ =>
      ⟨e.symm.toOpenPartialHomeomorph, mem_univ _, isCausalIso_iff_chartIso.1 h.symm⟩,
    fun hD => Causality.locallyStronglyCausal_of_forall_chartIso hD fun _ =>
      ⟨e.toOpenPartialHomeomorph, mem_univ _, isCausalIso_iff_chartIso.1 h⟩⟩

end IsCausalIso

end Causal
