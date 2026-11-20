import Causal.GXSingular
import Causal.ArcConnected
import Causal.Model.Massive
import Causal.Flat.IsomCausal

/-!
# The causality of `E^{1,2}_{≥0}`-manifolds: absolutely minimal, causally arc-connected, push-up

Target `T-ett-unanchored` (2026-11-20). The three corollaries of Section 3.1 which make an
`E_{≥0}`-manifold a topological spacetime, proved from the abstracted singular `(G,X)`-structure
of `Causal.GXSingular` (`prop:GX_sing_espace_temps_topo`) by the paper's own arguments. No label
is marked: the singular atlas is abstracted (OQ-19, ruled by DEC-25 in gx's terms and not yet
reconciled here) and the `E₀` model is not in this package (DEC-134, `T-ett-port-e0`); its two
facts used here — causal arc-connectedness (`cor:model_minimal` at `κ = 0`) and push-up
(`rem:pushup` at `κ = 0`) — are hypotheses. `E^{1,2}` and `Isom(E^{1,2})` are discharged
(`minkowski_model_facts`); for `E_α`, `α > 0`, causal arc-connectedness and push-up are discharged
(`massive_model_facts`), while the second half of (b) of `prop:GX_sing_espace_temps_topo` — the
regular charts of `E_α` are isomorphisms, `hreg` — is assumed: the library builds no regular chart
of `E_α`. With no BTZ model, `massA_positive` assumes `hreg` and the atlas only. Cited,
unmarked: `cor:massA_causalite` — `ETT.tex:1396`, `cor:massA_cac` — `ETT.tex:1408`,
`cor:pushup_sing` — `ETT.tex:1419`. `prop:GX_sing_dec` (`ETT.tex:1435`) and `lem:vecteur`
(`ETT.tex:1751`) are smooth statements with no declaration here (SCOPE).

> Every $\mass{\geq 0}$-manifold carries a natural absolutely minimal causality. [Proof:] By
> Corollary \ref{cor:model_minimal} the model spaces $\mass{\kappa}$, $\kappa\geq0$, are
> absolutely minimal, and $\isom(\mass{})$ acts on $\mass{}$ by morphisms of topological
> spacetimes; $\mass{}$ is moreover locally compact Hausdorff, hence Baire. The hypotheses of
> Proposition \ref{prop:GX_sing_espace_temps_topo} are therefore satisfied [...]
> (`ETT.tex:1396–1406`)

> Every $\mass{\geq 0}$-manifold is causally arc-connected. [Proof:] The chart domains form a cover
> of $M$ by causally arc-connected open sets [...] Implication $(i)\Rightarrow(ii)$ of Proposition
> \ref{prop:cac_engendre} concludes. (`ETT.tex:1408–1417`)

> Every $\mass{\geq0}$-manifold has the push-up property. [Proof:] The chart domains form a cover
> of $M$ by open sets isomorphic [...] to open subsets of the model spaces (Corollary
> \ref{cor:massA_causalite}); each of them has the
> push-up property by Remark \ref{rem:pushup}. Moreover $M$ is causally arc-connected by Corollary
> \ref{cor:massA_cac}. Lemma \ref{lem:pushup_local} concludes. (`ETT.tex:1419–1428`)

## What is proved (no `sorry` in this file)

* Transport through a chart which is an isomorphism (`ChartIso`): curves (`ChartIso.curveOn_symm`),
  causal arc-connectedness (`ChartIso.causallyArcConnectedOn`), push-up (`ChartIso.pushUpOn`).
* `IsAtlasCausality`: every chart an isomorphism, absolutely minimal — the causality of
  `prop:GX_sing_espace_temps_topo`.
* `cor:massA_causalite`: `massA_causalite`. `cor:massA_cac`: `massA_cac`. `cor:pushup_sing`:
  `pushup_sing`. Assembly: `massA_singular`. Model facts: `minkowski_model_facts`,
  `massive_model_facts`; no BTZ model: `massA_positive`, witnessed in the regular case only
  (`massA_positive_minkowski`: `E^{1,2}` with its identity chart; no chart into an `E_κ` is built).

## Hypothesis checklist

| paper | here |
|---|---|
| `E_{≥0}`-manifold | ⚠ strengthened (reading): the abstracted singular `(G,X)`-atlas of `existsUnique_causality_singularGX` (OQ-19 / DEC-25) |
| `X = E^{1,2}` causally arc-connected, `G = Isom` acting by morphisms | ✓ discharged for `minkowski 2`, `Flat.isom 2` (`minkowski_model_facts`); a hypothesis in the abstract statements |
| `E_κ`, `κ > 0`: causally arc-connected (`cor:model_minimal`), push-up (`rem:pushup`) | ✓ discharged (`massive_model_facts`, `massA_positive`) |
| `E_κ`, `κ > 0`: (b) second half, the regular charts of `E_κ` isomorphisms | ⚠ strengthened: assumed (`hreg` of `massA_positive`); no regular chart of `E_κ` is built |
| `E_0`: the same two facts | ⚠ strengthened: hypotheses `hb`, `hpY` at the BTZ model (the `E₀` instance is owed) |
| (b) second half: the regular part's causality extends | ⚠ reading of `Causal.GXSingular`: every regular chart is a `ChartIso` |
| Baire (`cor:massA_causalite`'s proof) | ⚠ weakened: not used (OQ-10) |

## SCOPE (disclosed)

* **Finding on `cor:massA_causalite`'s proof** (`ETT.tex:1400–1405`): it checks absolute
  minimality of the models (`cor:model_minimal`) and Baire, whereas
  `prop:GX_sing_espace_temps_topo` asks causal arc-connectedness of `X` and of each `X_α` ((a),
  (b)) — the premise of `cor:model_minimal`, not its conclusion — and the second half of (b)
  (the causality of `X_α` extends that of `reg(X_α)`), which the proof does not check. Lean
  carries causal arc-connectedness and the regular charts as `ChartIso` (reading of
  `Causal.GXSingular`); Baire is not used.
* `cor:massA_cac` is proved through `lem:precausalite_restriction_minimale`
  (`LocallyCausallyArcConnected.causallyArcConnected`): the chart domains are causally
  arc-connected (transport), so `M` is locally causally arc-connected, and absolutely minimal by
  `prop:GX_sing_espace_temps_topo`. The paper's route through `prop:cac_engendre` is the same
  argument (`generated_eq_iff_causallyArcConnected`).
* "Natural" in `cor:massA_causalite` is read as: every chart an isomorphism, and the unique
  absolutely minimal such causality (`prop:GX_sing_espace_temps_topo`'s uniqueness, in its
  absolutely minimal form, OQ-18).
* `prop:GX_sing_dec` (a smooth 3-manifold, `sing_α` closed 1-submanifolds; cited, Cor. 1.7 of
  `brunswic2021cauchy`) is not stated: the library has no smooth structure on a singular
  `(G,X)`-manifold, and no submanifolds. Its topological
  consequences are the fields `t2`, `secondCountable`, `metrizable`, `locallyCompact`,
  `noIsolated`, `isClosed_sing`, `interior_sing` of `SingularFlatAxioms`.
* `lem:vecteur` (a `C¹` non-singular future causal vector field, parallel to the singular
  lines) is not stated: no differentiable structure, no tangent vectors. The flow it is used for
  is the named hypothesis `VecteurFlow` of `Causal.SingularGeroch` (`theo:geroch_sing`), with
  the `C⁰` properties the proof asserts (kb/0022).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v v' w w₁ w₃

variable {M : Type u} [TopologicalSpace M]

/-! ### Transport through a chart which is an isomorphism -/

namespace ChartIso

variable {X : Type v} [TopologicalSpace X] {C : Causality M} {D : Causality X}
  {e : OpenPartialHomeomorph M X}

/-- A curve of the model inside the image of an open set `U` of the chart source, read back through
the chart, is a curve of `U`, for any two relation families matched by the chart. -/
theorem curveOn_symm {rC : Opens M → M → M → Prop} {rD : Opens X → X → X → Prop}
    (hiso : ∀ N : Opens M, N ≤ chartSource e → ∀ x ∈ N, ∀ y ∈ N,
      (rC N x y ↔ rD (chartImage e N) (e x) (e y)))
    (hrD : IsRelFamily rD) {U : Opens M} (hU : U ≤ chartSource e) {c : ℝ → X} {a b : ℝ}
    (hc : CurveOn rD (chartImage e U) c a b) : CurveOn rC U (fun t => e.symm (c t)) a b := by
  refine ⟨fun t ht => ?_, fun t ht N hN htN => ?_⟩
  · obtain ⟨z, -, hzU, -, hsz⟩ := exists_of_mem_chartImage (hc.mem t ht)
    show e.symm (c t) ∈ U
    rw [hsz]
    exact hzU
  · obtain ⟨z, hzs, -, hez, hsz⟩ := exists_of_mem_chartImage (hc.mem t ht)
    have hzN : z ∈ N := by
      have htN' : e.symm (c t) ∈ N := htN
      rwa [hsz] at htN'
    have hctN : c t ∈ chartImage e N := by
      rw [← hez]
      exact mem_chartImage_of_mem hzs hzN
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht (chartImage e N) (chartImage_mono hN) hctN
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hr := hrel s hs s' hs' h1 h2 h3
    obtain ⟨z₁, -, hz₁N, hez₁, hsz₁⟩ := exists_of_mem_chartImage (hrD.mem_left hr)
    obtain ⟨z₂, -, hz₂N, hez₂, hsz₂⟩ := exists_of_mem_chartImage (hrD.mem_right hr)
    show rC N (e.symm (c s)) (e.symm (c s'))
    rw [hsz₁, hsz₂]
    rw [← hez₁, ← hez₂] at hr
    exact (hiso N (hN.trans hU) z₁ hz₁N z₂ hz₂N).2 hr

/-- Causal arc-connectedness passes from the model to the chart source. -/
theorem causallyArcConnectedOn (h : ChartIso C D e)
    (hD : D.CausallyArcConnectedOn (chartImage e (chartSource e))) :
    C.CausallyArcConnectedOn (chartSource e) := by
  rw [Causality.causallyArcConnectedOn_iff]
  intro U hU p q
  have hU' : chartImage e U ≤ chartImage e (chartSource e) := chartImage_mono hU
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · have hp := C.le_mem_left hpq
    have hq := C.le_mem_right hpq
    obtain ⟨c, hc, hc0, hc1⟩ :=
      ((hD (chartImage e U) hU' (e p) (e q)).1).1 (((h U hU p hp q hq).1).1 hpq)
    refine ⟨fun t => e.symm (c t),
      curveOn_symm (fun N hN x hx y hy => (h N hN x hx y hy).1) D.isRelFamily_le hU hc, ?_, ?_⟩
    · show e.symm (c 0) = p
      rw [hc0]
      exact e.left_inv (hU hp)
    · show e.symm (c 1) = q
      rw [hc1]
      exact e.left_inv (hU hq)
  · have hp := C.lt_mem_left hpq
    have hq := C.lt_mem_right hpq
    obtain ⟨c, hc, hc0, hc1⟩ :=
      ((hD (chartImage e U) hU' (e p) (e q)).2).1 (((h U hU p hp q hq).2).1 hpq)
    refine ⟨fun t => e.symm (c t),
      curveOn_symm (fun N hN x hx y hy => (h N hN x hx y hy).2) D.isRelFamily_lt hU hc, ?_, ?_⟩
    · show e.symm (c 0) = p
      rw [hc0]
      exact e.left_inv (hU hp)
    · show e.symm (c 1) = q
      rw [hc1]
      exact e.left_inv (hU hq)

/-- Push-up passes from the model to the chart source. -/
theorem pushUpOn (h : ChartIso C D e) (hD : D.PushUpOn (chartImage e (chartSource e))) :
    C.PushUpOn (chartSource e) := by
  intro U hU x y z
  have hU' : chartImage e U ≤ chartImage e (chartSource e) := chartImage_mono hU
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · have hx := C.lt_mem_left hxy
    have hy := C.lt_mem_right hxy
    have hz := C.le_mem_right hyz
    exact ((h U hU x hx z hz).2).2 (((hD _ hU' (x := e x) (y := e y) (z := e z)).1) (((h U hU x hx y hy).2).1 hxy)
      (((h U hU y hy z hz).1).1 hyz))
  · have hx := C.le_mem_left hxy
    have hy := C.le_mem_right hxy
    have hz := C.lt_mem_right hyz
    exact ((h U hU x hx z hz).2).2 (((hD _ hU' (x := e x) (y := e y) (z := e z)).2) (((h U hU x hx y hy).1).1 hxy)
      (((h U hU y hy z hz).2).1 hyz))

end ChartIso

/-- Push-up of a spacetime gives push-up of each of its open subsets. -/
theorem Causality.PushUp.pushUpOn {C : Causality M} (h : C.PushUp) (W : Opens M) :
    C.PushUpOn W :=
  fun U _ => (Causality.pushUpOn_top.2 h) U le_top

/-! ### The causality of a singular `(G,X)`-manifold -/

section Atlas

variable {X : Type v} [TopologicalSpace X] {A : Type w₁} {Y : A → Type v'}
  [∀ α, TopologicalSpace (Y α)] {I : Type w₃} {J : Type w₃}

/-- **The causality of the abstracted singular atlas** (`prop:GX_sing_espace_temps_topo`): every
chart into `X` and into a model `Y α` is an isomorphism of topological spacetimes, and the
causality is absolutely minimal. -/
def IsAtlasCausality (C : Causality M) (eX : I → OpenPartialHomeomorph M X) (β : J → A)
    (eY : ∀ j, OpenPartialHomeomorph M (Y (β j))) (DX : Causality X)
    (DY : ∀ α, Causality (Y α)) : Prop :=
  (∀ i, ChartIso C DX (eX i)) ∧ (∀ j, ChartIso C (DY (β j)) (eY j)) ∧ C.AbsolutelyMinimal

/-- `cor:massA_cac`, abstracted: for a cover by charts into causally arc-connected models, the
causality of the atlas is causally arc-connected. -/
theorem massA_cac {C : Causality M} {eX : I → OpenPartialHomeomorph M X} {β : J → A}
    {eY : ∀ j, OpenPartialHomeomorph M (Y (β j))} {DX : Causality X} {DY : ∀ α, Causality (Y α)}
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (ha : DX.CausallyArcConnected) (hb : ∀ α, (DY α).CausallyArcConnected)
    (hC : IsAtlasCausality C eX β eY DX DY) : C.CausallyArcConnected := by
  have hloc : C.LocallyCausallyArcConnected := by
    intro x N hN
    have hsrc : ∃ S : Opens M, x ∈ S ∧ C.CausallyArcConnectedOn S := by
      rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨chartSource (eX i), hi, (hC.1 i).causallyArcConnectedOn
          (Causality.CausallyArcConnectedOn.mono ha le_top)⟩
      · exact ⟨chartSource (eY j), hj, (hC.2.1 j).causallyArcConnectedOn
          (Causality.CausallyArcConnectedOn.mono (hb _) le_top)⟩
    obtain ⟨S, hxS, hS⟩ := hsrc
    exact ⟨S ⊓ ⟨interior N, isOpen_interior⟩, ⟨hxS, mem_interior_iff_mem_nhds.2 hN⟩,
      fun z hz => interior_subset hz.2, Causality.CausallyArcConnectedOn.mono hS inf_le_left⟩
  exact Causality.LocallyCausallyArcConnected.causallyArcConnected hloc hC.2.2

/-- `cor:pushup_sing`, abstracted: if moreover every model has the push-up property, so has
the causality of the atlas. -/
theorem pushup_sing {C : Causality M} {eX : I → OpenPartialHomeomorph M X} {β : J → A}
    {eY : ∀ j, OpenPartialHomeomorph M (Y (β j))} {DX : Causality X} {DY : ∀ α, Causality (Y α)}
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (ha : DX.CausallyArcConnected) (hb : ∀ α, (DY α).CausallyArcConnected)
    (hpX : DX.PushUp) (hpY : ∀ α, (DY α).PushUp)
    (hC : IsAtlasCausality C eX β eY DX DY) : C.PushUp := by
  have hcac := massA_cac hcover ha hb hC
  let O : I ⊕ J → Opens M := Sum.elim (fun i => chartSource (eX i)) fun j => chartSource (eY j)
  have hO : ∀ x : M, ∃ s, x ∈ O s := fun x => by
    rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr j, hj⟩
  refine Causality.CausallyArcConnected.pushUp hcac hO ?_
  rintro (i | j)
  · exact (hC.1 i).pushUpOn (hpX.pushUpOn _)
  · exact (hC.2.1 j).pushUpOn ((hpY _).pushUpOn _)

variable {G : Type w} [Group G] [MulAction G X] [ContinuousConstSMul G X] {K : A → Type w₁}

/-- `cor:massA_causalite`, abstracted: under the hypotheses of
`prop:GX_sing_espace_temps_topo`, the singular `(G,X)`-manifold carries a causality for which every
chart is an isomorphism, absolutely minimal, and the only absolutely minimal such one. -/
theorem massA_causalite (r : ∀ α, K α → OpenPartialHomeomorph (Y α) X)
    (eX : I → OpenPartialHomeomorph M X) (β : J → A) (eY : ∀ j, OpenPartialHomeomorph M (Y (β j)))
    (DX : Causality X) (DY : ∀ α, Causality (Y α))
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    (hb : ∀ α, (DY α).CausallyArcConnected) (hreg : ∀ α k, ChartIso (DY α) DX (r α k))
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (hXX : ∀ i i', (eX i).symm.trans (eX i') ∈ gxGroupoid G X)
    (hXY : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source → ∃ k : K (β j), ∃ g : G,
      ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eX i) ⊓ chartSource (eY j) ∧
        ∀ z ∈ O, eY j z ∈ (r (β j) k).source ∧ r (β j) k (eY j z) = g • eX i z)
    (hYY : ∀ j j', ∀ x ∈ (eY j).source, x ∈ (eY j').source →
      ∃ ψ : OpenPartialHomeomorph (Y (β j)) (Y (β j')), ChartIso (DY (β j)) (DY (β j')) ψ ∧
        ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eY j) ⊓ chartSource (eY j') ∧
          ∀ z ∈ O, eY j z ∈ ψ.source ∧ ψ (eY j z) = eY j' z) :
    ∃ C : Causality M, IsAtlasCausality C eX β eY DX DY ∧
      ∀ C' : Causality M, IsAtlasCausality C' eX β eY DX DY → C' = C := by
  obtain ⟨C, hX, hY, hmin, huniq⟩ :=
    existsUnique_causality_singularGX r eX β eY DX DY ha hG hb hreg hcover hXX hXY hYY
  exact ⟨C, ⟨hX, hY, hmin⟩, fun C' hC' => huniq C' hC'.1 hC'.2.1 hC'.2.2⟩

/-- **The three corollaries assembled** (`cor:massA_causalite`, `cor:massA_cac`,
`cor:pushup_sing`): under the hypotheses of `prop:GX_sing_espace_temps_topo` and the push-up of
the models, the causality of the atlas exists, is unique among absolutely minimal ones, is
causally arc-connected and has the push-up property. -/
theorem massA_singular (r : ∀ α, K α → OpenPartialHomeomorph (Y α) X)
    (eX : I → OpenPartialHomeomorph M X) (β : J → A) (eY : ∀ j, OpenPartialHomeomorph M (Y (β j)))
    (DX : Causality X) (DY : ∀ α, Causality (Y α))
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    (hb : ∀ α, (DY α).CausallyArcConnected) (hreg : ∀ α k, ChartIso (DY α) DX (r α k))
    (hpX : DX.PushUp) (hpY : ∀ α, (DY α).PushUp)
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (hXX : ∀ i i', (eX i).symm.trans (eX i') ∈ gxGroupoid G X)
    (hXY : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source → ∃ k : K (β j), ∃ g : G,
      ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eX i) ⊓ chartSource (eY j) ∧
        ∀ z ∈ O, eY j z ∈ (r (β j) k).source ∧ r (β j) k (eY j z) = g • eX i z)
    (hYY : ∀ j j', ∀ x ∈ (eY j).source, x ∈ (eY j').source →
      ∃ ψ : OpenPartialHomeomorph (Y (β j)) (Y (β j')), ChartIso (DY (β j)) (DY (β j')) ψ ∧
        ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eY j) ⊓ chartSource (eY j') ∧
          ∀ z ∈ O, eY j z ∈ ψ.source ∧ ψ (eY j z) = eY j' z) :
    ∃ C : Causality M, IsAtlasCausality C eX β eY DX DY ∧
      (∀ C' : Causality M, IsAtlasCausality C' eX β eY DX DY → C' = C) ∧
      C.CausallyArcConnected ∧ C.PushUp := by
  obtain ⟨C, hC, huniq⟩ :=
    massA_causalite (G := G) r eX β eY DX DY ha hG hb hreg hcover hXX hXY hYY
  exact ⟨C, hC, huniq, massA_cac hcover ha hb hC, pushup_sing hcover ha hb hpX hpY hC⟩

end Atlas

/-! ### The model facts that are in the library -/

/-- The regular model `E^{1,2}` (`minkowski 2`; every dimension here) with `G = Isom`: (a) of
`prop:GX_sing_espace_temps_topo`, and push-up (`rem:pushup`). -/
theorem minkowski_model_facts (d : ℕ) :
    (minkowski d).CausallyArcConnected ∧ (minkowski d).PushUp ∧
      ∀ g : Flat.isom d, StrongMorphism (minkowski d) (minkowski d) fun p => g • p :=
  ⟨minkowski_causallyArcConnected, minkowski_pushUp, Flat.isom_strongMorphism⟩

/-- The massive models `E_α`, `α > 0`: causally arc-connected (`cor:model_minimal`'s premise) and
push-up (`rem:pushup`). -/
theorem massive_model_facts (α : ℝ) [Fact (0 < α)] :
    (massive α).CausallyArcConnected ∧ (massive α).PushUp :=
  ⟨massive_causallyArcConnected, massive_pushUp⟩

/-- `E_κ` for `κ` in the type of positive reals, with its instance. -/
noncomputable def massiveOf (κ : {κ : ℝ // 0 < κ}) : Causality (Massive κ.1) :=
  @massive κ.1 ⟨κ.2⟩

/-- **No BTZ model: the three corollaries with `hreg` the only model hypothesis.** For a singular
`(Isom(E^{1,2}), E^{1,2}, E_{>0})`-atlas — model spaces `E_κ`, `κ > 0`, abstracted as in
`Causal.GXSingular` — the causality of the atlas exists, is unique among absolutely minimal ones,
is causally arc-connected and has the push-up property. The causal arc-connectedness and push-up
of `E^{1,2}` and of every `E_κ` are discharged; what is assumed is the model fact `hreg` (the
regular charts of `E_κ` are isomorphisms onto `E^{1,2}`: the second half of (b) of
`prop:GX_sing_espace_temps_topo`, not built in the library) and the atlas (`hXX`, `hXY`, `hYY`,
OQ-19). -/
theorem massA_positive {K : {κ : ℝ // 0 < κ} → Type}
    (r : ∀ κ, K κ → OpenPartialHomeomorph (Massive κ.1) (Minkowski 2))
    {I J : Type} (eX : I → OpenPartialHomeomorph M (Minkowski 2)) (β : J → {κ : ℝ // 0 < κ})
    (eY : ∀ j, OpenPartialHomeomorph M (Massive (β j).1))
    (hreg : ∀ κ k, ChartIso (massiveOf κ) (minkowski 2) (r κ k))
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (hXX : ∀ i i', (eX i).symm.trans (eX i') ∈ gxGroupoid (Flat.isom 2) (Minkowski 2))
    (hXY : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source → ∃ k : K (β j), ∃ g : Flat.isom 2,
      ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eX i) ⊓ chartSource (eY j) ∧
        ∀ z ∈ O, eY j z ∈ (r (β j) k).source ∧ r (β j) k (eY j z) = g • eX i z)
    (hYY : ∀ j j', ∀ x ∈ (eY j).source, x ∈ (eY j').source →
      ∃ ψ : OpenPartialHomeomorph (Massive (β j).1) (Massive (β j').1),
        ChartIso (massiveOf (β j)) (massiveOf (β j')) ψ ∧
        ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eY j) ⊓ chartSource (eY j') ∧
          ∀ z ∈ O, eY j z ∈ ψ.source ∧ ψ (eY j z) = eY j' z) :
    ∃ C : Causality M, IsAtlasCausality C eX β eY (minkowski 2) massiveOf ∧
      (∀ C' : Causality M, IsAtlasCausality C' eX β eY (minkowski 2) massiveOf → C' = C) ∧
      C.CausallyArcConnected ∧ C.PushUp :=
  massA_singular (G := Flat.isom 2) r eX β eY (minkowski 2) massiveOf
    minkowski_causallyArcConnected Flat.isom_strongMorphism
    (fun κ => @massive_causallyArcConnected κ.1 ⟨κ.2⟩) hreg minkowski_pushUp
    (fun κ => @massive_pushUp κ.1 ⟨κ.2⟩) hcover hXX hXY hYY

/-- **Witness of `massA_positive`, regular case only** (kb/0011): `E^{1,2}` with one identity chart
into `X` and no singular chart satisfies its hypotheses, and the causality it produces is
`minkowski 2`. A witness with a chart into some `E_κ` needs regular charts `reg(E_κ) → E^{1,2}`
which are isomorphisms, and the library does not build them. -/
theorem massA_positive_minkowski :
    IsAtlasCausality (minkowski 2) (fun _ : Unit => OpenPartialHomeomorph.refl (Minkowski 2))
        (Empty.elim : Empty → {κ : ℝ // 0 < κ}) (fun j => j.elim) (minkowski 2) massiveOf ∧
      ∀ C : Causality (Minkowski 2),
        IsAtlasCausality C (fun _ : Unit => OpenPartialHomeomorph.refl (Minkowski 2))
          (Empty.elim : Empty → {κ : ℝ // 0 < κ}) (fun j => j.elim) (minkowski 2) massiveOf →
        C = minkowski 2 ∧ C.CausallyArcConnected ∧ C.PushUp := by
  have hmk : IsAtlasCausality (minkowski 2)
      (fun _ : Unit => OpenPartialHomeomorph.refl (Minkowski 2))
      (Empty.elim : Empty → {κ : ℝ // 0 < κ}) (fun j => j.elim) (minkowski 2) massiveOf :=
    ⟨fun _ => chartIso_refl _, fun j => j.elim, minkowski_absolutelyMinimal⟩
  obtain ⟨C₀, -, huniq, hcac, hpush⟩ := massA_positive (K := fun _ => Empty)
    (fun _ k => k.elim) (fun _ : Unit => OpenPartialHomeomorph.refl (Minkowski 2))
    (Empty.elim : Empty → {κ : ℝ // 0 < κ}) (fun j => j.elim) (fun _ k => k.elim)
    (fun x => Or.inl ⟨(), by simp⟩)
    (fun _ _ => mem_gxGroupoid_of_eq_id (by simp) (by simp)) (fun _ j => j.elim)
    (fun j => j.elim)
  have h₀ : minkowski 2 = C₀ := huniq _ hmk
  refine ⟨hmk, fun C hC => ?_⟩
  have h₁ : C = C₀ := huniq C hC
  rw [h₁, ← h₀]
  exact ⟨rfl, minkowski_causallyArcConnected, minkowski_pushUp⟩

end Causal
