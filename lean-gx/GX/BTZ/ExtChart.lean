import GX.BTZ.Embeddings

/-!
# The chart step for BTZ-extensions: an injective `𝔼₀`-morphism off BTZ points extends over a cluster point of its graph

Target `T-btz-pgcd-dom-gh` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
**0 `sorry`, standard axioms only.** No label is marked here: this file is the base shared by
`GX.BTZ.Pgcd` (`btzprop:pgcd`, l.1376) and `GX.BTZ.PpcmHausdorff`
(`btzprop:ppcm`, the chart step of its first bullet, l.1432–1493). Its declarations were written
for T-btz-ppcm-hausdorff and moved here unchanged (same full names, namespace
`GX.PpcmHausdorff`) so that `Pgcd` can use them without an import cycle.

* `btzprop:ppcm` — `BTZ_1.tex:1415` (the chart step, l.1432–1493) —
  `GX.PpcmHausdorff.exists_ext_of_graphCluster`, with `GX.PpcmHausdorff.GraphCluster`,
  `GX.PpcmHausdorff.exists_graphCluster_shrink`, `GX.PpcmHausdorff.le_image_of_graphCluster`,
  `GX.PpcmHausdorff.lt_image_of_lt`, `GX.PpcmHausdorff.exists_ball_chart`.
* helpers: `GX.PpcmHausdorff.lt_in_of_lt`, `GX.PpcmHausdorff.ceY_lt_iff`,
  `GX.PpcmHausdorff.D_lt_of_lt`, `GX.PpcmHausdorff.lt_of_isE0Mor_paper`,
  `GX.PpcmHausdorff.exists_mem_e0Groupoid_target_inr`,
  `GX.PpcmHausdorff.trans_mem_maximalAtlas`, `GX.PpcmHausdorff.exists_chart_inr`.

> The future of a BTZ point in $\V_p$ is in the regular part of a neighborhood of some BTZ point
> of $\V_p$; Proposition $\ref{prop:isom_strong}$ applies thus $\alpha=0$ and
> $\psi_{p'} \circ \phi \circ \psi_p^{-1}$ is the restriction of an isomorphism $\gamma_p$ of
> $\mass{0}$. (l.1452–1454)

## Hypothesis checklist (`exists_ext_of_graphCluster`)

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |
| `M₂` globally hyperbolic | ✓ carried (the compact diamonds) |
| `M₁` Hausdorff, second countable; `M₂` Hausdorff (l.261) | ✓ carried |
| (none) | ⚠ strengthened: `M₁` connected (`E0AbsMax.e0_sfa_of_globalBTZ`) |

## SCOPE (disclosed)

The chart step is proved one point at a time, by B21 Lemma 2.12's shrinking diamonds in place of
the paper's `I⁺(p') = φ(I⁺(p))` (l.1442–1448); see `GX.BTZ.PpcmHausdorff`'s SCOPE.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0CBG E0Spear

namespace PpcmHausdorff

/-! ### §1 Relations carried by an `𝔼₀`-morphism defined off BTZ points -/

section Rel

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- A chronological relation from a point of an open `A ⊇ Reg M` holds inside `A` (the chronal
curve leaves its start into `I⁺`, which is regular). -/
theorem lt_in_of_lt {A : Opens M} (hA : (A : Set M)ᶜ ⊆ S0 M) {x y : M} (hx : x ∈ A)
    (hxy : (CE M).lt ⊤ x y) : (CE M).lt A x y := by
  have h := E0AbsMax.e0_sfa_of_globalBTZ M
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (h.causallyArcConnected ⊤ le_rfl x y).2.1 hxy
  have hγA : ∀ σ ∈ Icc (0 : ℝ) 1, γ σ ∈ A := by
    intro σ hσ
    rcases hσ.1.eq_or_lt with e | e
    · rw [← e, hγ0]; exact hx
    · have hl := hγ.lt_of_lt le_rfl e hσ.2
      rw [hγ0] at hl
      exact by_contra fun hn => E0AbsMax.notMem_sing_of_lt h hl (hA hn)
  have hγ' : (CE M).ChronalCurveOn A γ 0 1 :=
    Causal.CurveOn.restrict hγ le_rfl le_rfl le_top hγA
  have := hγ'.lt_of_lt le_rfl zero_lt_one le_rfl
  rwa [hγ0, hγ1] at this

end Rel

/-! ### §1b Transfer of the chronological relation of `𝔼₀` along an `𝔼₀`-morphism -/

section LtTransfer

theorem ceY_lt_iff {V : Opens E0Y} {a b : E0Y} (ha : a ∈ V) (hb : b ∈ V) :
    (CE E0Y).lt V a b ↔ E0LM.D.lt V a b := by
  have h := Causal.CBG.chartedCausality_chartIso (M := E0Y) (G := e0Groupoid)
    E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ a V
    (fun x _ => by simp [Causal.chartSource]) a ha b hb
  rw [chartAt_self_eq, chartImage_refl] at h
  exact h.2

theorem D_lt_of_lt {U : Opens E0} {x y : E0} (h : E0.causality.lt U x y) :
    E0LM.D.lt (Causal.chartImage E0.paperInY U) (E0.paperInY x) (E0.paperInY y) :=
  ((E0.chartIso_paperInY U (fun z _ => by simp [Causal.chartSource]) x
    (E0.causality.lt_mem_left h) y (E0.causality.lt_mem_right h)).2).1 h

/-- **An `𝔼₀`-morphism maps chronological relations of `𝔼₀` inside (the preimage of) its domain
to chronological relations of the target** (the `lt` twin of `le_of_isE0Mor_paper`). -/
theorem lt_of_isE0Mor_paper {N : Type} [TopologicalSpace N] [ChartedSpace E0Y N]
    [HasGroupoid N e0Groupoid] {ψ : E0Y → N} {W : Set E0Y} (hW : IsOpen W) (hψ : IsE0Mor ψ W)
    {U : Opens E0} (hU : (U : Set E0) ⊆ E0.paperInY ⁻¹' W) {x y : E0}
    (h : E0.causality.lt U x y) : (CE N).lt ⊤ (ψ (E0.paperInY x)) (ψ (E0.paperInY y)) := by
  have hD := D_lt_of_lt h
  have hV : (Causal.chartImage E0.paperInY U : Set E0Y) ⊆ W := by
    rw [Causal.coe_chartImage]
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    exact hU hz
  exact (Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨W, hW⟩) hψ).map_lt _ ⊤ hV (fun _ _ => trivial)
    ((ceY_lt_iff (E0LM.D.lt_mem_left hD) (E0LM.D.lt_mem_right hD)).2 hD)

end LtTransfer

/-! ### §1c Charts of an `𝔼₀`-manifold landing in `𝔼₀` -/

section ChartInr

attribute [local instance] btzE0Structure

/-- Every point of `Y = 𝕄 ⊕ 𝔼₀` is in the source of an element of `G` whose target lies in
`𝔼₀`: the identity of `𝔼₀` restricted to it, or, at a point of `𝕄`, a translation of `𝕄` into a
regular chart of `𝔼₀`. -/
theorem exists_mem_e0Groupoid_target_inr (y : E0Y) :
    ∃ σ ∈ e0Groupoid, y ∈ σ.source ∧ σ.target ⊆ range Sum.inr := by
  rcases y with m | x
  · -- a translation of `𝕄` into a regular chart of `𝔼₀`
    obtain ⟨x₀, hx₀⟩ : (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0).Nonempty :=
      (isPortly_reg _ _ _).dense.nonempty
    obtain ⟨c', hc', hx₀c'⟩ := mem_support.1 hx₀
    set g : Causal.Flat.isom 2 :=
      ⟨AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) (c' x₀ - m), Causal.Flat.constVAdd_mem_isom _⟩
      with hg
    have hgm : g • m = c' x₀ := by
      show (c' x₀ - m) + m = c' x₀
      abel
    set σ : OpenPartialHomeomorph E0Y E0Y := e0Inl.symm.trans
      ((Homeomorph.smul g).toOpenPartialHomeomorph.trans (c'.symm.trans e0Inr)) with hσ
    have hσsrc : ∀ y', y' ∈ σ.source ↔ y' ∈ e0Inl.symm.source ∧ g • e0Inl.symm y' ∈ c'.target := by
      intro y'
      simp [σ]
    have hσapp : ∀ y', σ y' = Sum.inr (c'.symm (g • e0Inl.symm y')) := fun y' => rfl
    have hσmem : σ ∈ e0Groupoid := by
      refine mem_e0Groupoid_of_chart_eq e0Inl_symm_mem_e0Atlas (e0InrChart_mem_e0Atlas hc')
        (fun y' hy' => ((hσsrc y').1 hy').1) ?_ g ?_
      · intro y' hy'
        have hs := σ.map_target hy'
        obtain ⟨-, h2⟩ := (hσsrc _).1 hs
        rw [← σ.right_inv hy', hσapp]
        exact mem_e0InrChart_source.2 ⟨_, c'.map_target h2, rfl⟩
      · intro y' hy'
        obtain ⟨-, h2⟩ := (hσsrc y').1 hy'
        rw [hσapp, e0InrChart_inr, c'.right_inv h2]
    refine ⟨σ, hσmem, (hσsrc _).2 ⟨by rw [e0Inl_symm_source]; exact ⟨m, rfl⟩, ?_⟩, ?_⟩
    · rw [e0Inl_symm_inl, hgm]; exact c'.map_source hx₀c'
    · intro y' hy'
      rw [← σ.right_inv hy', hσapp]
      exact ⟨_, rfl⟩
  · -- the identity of `𝔼₀`
    refine ⟨(OpenPartialHomeomorph.refl E0Y).restr (range Sum.inr),
      closedUnderRestriction' e0Groupoid.id_mem isOpen_range_inr, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_range_inr]
      exact ⟨trivial, x, rfl⟩
    · intro y' hy'
      rw [OpenPartialHomeomorph.restr_target] at hy'
      exact interior_subset hy'.2

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [HasGroupoid M e0Groupoid] in
/-- A chart of the maximal atlas followed by an element of `G` is in the maximal atlas. -/
theorem trans_mem_maximalAtlas {c : OpenPartialHomeomorph M E0Y}
    (hc : c ∈ e0Groupoid.maximalAtlas M) {σ : OpenPartialHomeomorph E0Y E0Y} (hσ : σ ∈ e0Groupoid) :
    c.trans σ ∈ e0Groupoid.maximalAtlas M := by
  intro e' he'
  obtain ⟨h1, h2⟩ := hc e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact e0Groupoid.trans (e0Groupoid.symm hσ) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact e0Groupoid.trans h2 hσ

/-- **Every point of an `𝔼₀`-manifold has a chart of the maximal atlas landing in `𝔼₀`.** -/
theorem exists_chart_inr (q : M) :
    ∃ c ∈ e0Groupoid.maximalAtlas M, q ∈ c.source ∧ c.target ⊆ range Sum.inr := by
  obtain ⟨σ, hσ, hqσ, hσt⟩ := exists_mem_e0Groupoid_target_inr (chartAt E0Y q q)
  refine ⟨(chartAt E0Y q).trans σ,
    trans_mem_maximalAtlas (e0Groupoid.chart_mem_maximalAtlas q) hσ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source E0Y q, hqσ⟩
  · intro y hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    exact hσt hy.1

end ChartInr

/-! ### §2 The chart step: `φ` extends over a chart of a point of `C` -/

section ChartStep

variable {M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]
  [T2Space M₁] [ConnectedSpace M₁] [SecondCountableTopology M₁] [HasGroupoid M₁ e0Groupoid]
  [T2Space M₂] [HasGroupoid M₂ e0Groupoid]

/-- `(p, r)` lies in the closure of the graph of `f` over `D`, in neighbourhood form. -/
def GraphCluster (D : Set M₁) (f : M₁ → M₂) (p : M₁) (r : M₂) : Prop :=
  ∀ U ∈ 𝓝 p, ∀ V ∈ 𝓝 r, ∃ u ∈ D, u ∈ U ∧ f u ∈ V

omit [T2Space M₂] in
/-- An `𝔼₀`-morphism on `D ⊇ Reg M₁` carries the chronological relation from a point of `D`. -/
theorem lt_image_of_lt {D : Opens M₁} (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) {f : M₁ → M₂}
    (hf : IsE0Mor f D) {u x : M₁} (hu : u ∈ D) (hux : (CE M₁).lt ⊤ u x) :
    (CE M₂).lt ⊤ (f u) (f x) :=
  (isEMorphismOn_of_isE0Mor (W := D) hf).map_lt D ⊤ le_rfl (fun _ _ => trivial)
    (lt_in_of_lt hD hu hux)

/-- B21 l.964–973 in the form used: for `(p, r)` in the closure of the graph of `f` over `D`,
`r ≤ f x` for every `x ≫ p` (`I⁻(x)` is a neighbourhood of `p`, and `J⁻(f x)` is closed in the
globally hyperbolic `M₂`). -/
theorem le_image_of_graphCluster (hG₂ : (CE M₂).GloballyHyperbolic) {D : Opens M₁}
    (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) {f : M₁ → M₂} (hf : IsE0Mor f D) {p : M₁} {r : M₂}
    (hr : GraphCluster D f p r) {x : M₁} (hpx : (CE M₁).lt ⊤ p x) : (CE M₂).le ⊤ r (f x) := by
  have hcl := hG₂.isClosed_Jminus_singleton (E0LM.e0_tarentin (M := M₂)) (f x)
  have hmem : r ∈ closure ((CE M₂).Jminus ⊤ {f x}) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨u, huD, hu, huV⟩ := hr _ ((CE M₁).isOpen_Iminus.mem_nhds
      (Causal.Precausality.mem_Iminus_singleton.2 hpx)) V hV
    exact ⟨f u, huV, Causal.Precausality.mem_Jminus_singleton.2 ((CE M₂).le_of_lt
      (lt_image_of_lt hD hf huD (Causal.Precausality.mem_Iminus_singleton.1 hu)))⟩
  rw [hcl.closure_eq] at hmem
  exact Causal.Precausality.mem_Jminus_singleton.1 hmem

/-- **Shrinking diamonds** (B21 l.964–978, the paper's « `I⁺(p') = φ(I⁺(p))` » in the form
used): for `(p, r)` in the closure of the graph, the decreasing images `f(bₙ)` of a chronological
sequence `bₙ ↘ p` cluster at some `q'` with `(p, q')` in the closure of the graph, and for every
neighbourhood `O` of `q'` some `b ≫ p` has `f(I⁺(p) ∩ I⁻(b)) ⊆ O`. -/
theorem exists_graphCluster_shrink (hG₂ : (CE M₂).GloballyHyperbolic) {D : Opens M₁}
    (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) {f : M₁ → M₂} (hf : IsE0Mor f D) {p : M₁} {r : M₂}
    (hr : GraphCluster D f p r) :
    ∃ q', GraphCluster D f p q' ∧ ∀ O ∈ 𝓝 q', ∃ b, (CE M₁).lt ⊤ p b ∧
      ∀ x, (CE M₁).lt ⊤ p x → (CE M₁).lt ⊤ x b → f x ∈ O := by
  have hsfa := E0AbsMax.e0_sfa_of_globalBTZ M₁
  have hT := E0LM.e0_tarentin (M := M₂)
  have hDreg : ∀ x, x ∉ S0 M₁ → x ∈ D := fun x hx => by_contra fun h => hx (hD h)
  obtain ⟨b, hpb, hbb, hblim⟩ := E0AbsMax.exists_seq_lt_tendsto (M := M₁) (p := p)
  have hbD : ∀ n, b n ∈ D := fun n => hDreg _ (E0AbsMax.notMem_sing_of_lt hsfa (hpb n))
  set y : ℕ → M₂ := fun n => f (b n) with hy
  have hyy : ∀ n, (CE M₂).le ⊤ (y (n + 1)) (y n) := fun n =>
    (CE M₂).le_of_lt (lt_image_of_lt hD hf (hbD (n + 1)) (hbb n))
  have hymono : ∀ m n, m ≤ n → (CE M₂).le ⊤ (y n) (y m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact (CE M₂).le_refl trivial
    | succ n _ ih => exact (CE M₂).le_trans (hyy n) ih
  have hry : ∀ n, (CE M₂).le ⊤ r (y n) := fun n => le_image_of_graphCluster hG₂ hD hf hr (hpb n)
  -- the cluster point `q'` of the decreasing `f(bₙ)`
  obtain ⟨q', -, hq'⟩ := (hG₂.2 r (y 0)).exists_mapClusterPt (f := atTop) (u := y)
    (by
      rw [le_principal_iff, mem_map]
      exact univ_mem' fun n =>
        Causal.Causality.mem_diamond.2 ⟨hry n, hymono 0 n (Nat.zero_le n)⟩)
  have hq'y : ∀ n, (CE M₂).le ⊤ q' (y n) := fun n =>
    Causal.Precausality.mem_Jminus_singleton.1 (mem_of_mapClusterPt_of_eventually
      (hG₂.isClosed_Jminus_singleton hT (y n)) hq'
      (eventually_atTop.2 ⟨n, fun m hm =>
        Causal.Precausality.mem_Jminus_singleton.2 (hymono n m hm)⟩))
  have hcl' : GraphCluster D f p q' := by
    intro U hU V hV
    obtain ⟨n, hn1, hn2⟩ :=
      ((mapClusterPt_iff_frequently.1 hq' V hV).and_eventually (hblim.eventually hU)).exists
    exact ⟨b n, hbD n, hn2, hn1⟩
  refine ⟨q', hcl', fun O hO => ?_⟩
  -- some diamond `J(q', f bₙ)` lies in `O`
  obtain ⟨n, hn⟩ : ∃ n, (CE M₂).diamond ⊤ q' (y n) ⊆ O := by
    set Dm : ℕ → Set M₂ := fun n => (CE M₂).diamond ⊤ q' (y n) with hDm
    have hDsub : ∀ m n, m ≤ n → Dm n ⊆ Dm m := fun m n hmn x hx =>
      Causal.Causality.mem_diamond.2 ⟨(Causal.Causality.mem_diamond.1 hx).1,
        (CE M₂).le_trans (Causal.Causality.mem_diamond.1 hx).2 (hymono m n hmn)⟩
    have hint : Dm 0 ∩ ⋂ i, (Dm i ∩ (interior O)ᶜ) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have hxi := mem_iInter.1 hx.2
      have hle : ∀ i, (CE M₂).le ⊤ x (y i) := fun i =>
        (Causal.Causality.mem_diamond.1 (hxi i).1).2
      have hxq : (CE M₂).le ⊤ x q' :=
        Causal.Precausality.mem_Jplus_singleton.1 (mem_of_mapClusterPt_of_eventually
          (hG₂.isClosed_Jplus_singleton hT x) hq'
          (Eventually.of_forall fun i => Causal.Precausality.mem_Jplus_singleton.2 (hle i)))
      have hxe : x = q' := hG₂.1 hxq (Causal.Causality.mem_diamond.1 (hxi 0).1).1
      exact (hxi 0).2 (hxe ▸ mem_interior_iff_mem_nhds.2 hO)
    obtain ⟨u, hu⟩ := (hG₂.2 q' (y 0)).elim_finite_subfamily_closed
      (fun i => Dm i ∩ (interior O)ᶜ)
      (fun i => (hG₂.2 q' (y i)).isClosed.inter isOpen_interior.isClosed_compl) hint
    refine ⟨u.sup id, fun x hx => ?_⟩
    by_contra hxO
    have hxO' : x ∉ interior O := fun h => hxO (interior_subset h)
    have hmem : x ∈ Dm 0 ∩ ⋂ i ∈ u, (Dm i ∩ (interior O)ᶜ) :=
      ⟨hDsub 0 _ (Nat.zero_le _) hx, mem_iInter₂.2 fun i hi =>
        ⟨hDsub i _ (Finset.le_sup (f := id) hi) hx, hxO'⟩⟩
    rw [hu] at hmem
    exact hmem
  refine ⟨b n, hpb n, fun x hpx hxb => hn (Causal.Causality.mem_diamond.2
    ⟨le_image_of_graphCluster hG₂ hD hf hcl' hpx, (CE M₂).le_of_lt ?_⟩)⟩
  have hxD : x ∈ D := hDreg _ (E0AbsMax.notMem_sing_of_lt hsfa hpx)
  exact lt_image_of_lt hD hf hxD hxb

omit [T2Space M₁] [ConnectedSpace M₁] [SecondCountableTopology M₁] in
/-- **The future of `p` in its chart** (« the future of a BTZ point in `𝒱_p` is in the regular
part of a neighbourhood of some BTZ point of `𝒱_p` », l.1452): in the preferred chart `κ` at a
BTZ point `p`, `κ p = (v, 0)`, a ball `B` of `𝔼₀` around `(v, 0)` is read inside a given
neighbourhood `N` of `p`, and its points `x` with `r > 0`, `τ − r/2 > v` are in `I⁺(p)`. -/
theorem exists_ball_chart {p : M₁} (hp : p ∈ S0 M₁) {N : Set M₁} (hN : N ∈ 𝓝 p) :
    ∃ (v δ : ℝ), 0 < δ ∧ chartAt E0Y p p = E0.paperInY ((v, 0) : E0) ∧
      (∀ x ∈ Metric.ball ((v, 0) : E0) δ, E0.paperInY x ∈ (chartAt E0Y p).target ∧
        (chartAt E0Y p).symm (E0.paperInY x) ∈ N) ∧
      ∀ x ∈ Metric.ball ((v, 0) : E0) δ, 0 < E0.rad x → v < E0.fcoord x →
        (CE M₁).lt ⊤ p ((chartAt E0Y p).symm (E0.paperInY x)) := by
  set κ := chartAt E0Y p with hκ
  obtain ⟨v, hv⟩ := E0AbsMax.exists_chart_axis hp
  have hpκ : p ∈ κ.source := mem_chart_source E0Y p
  have hT : IsOpen (E0.paperInY ⁻¹' (κ.target ∩ κ.symm ⁻¹' interior N)) :=
    (κ.isOpen_inter_preimage_symm isOpen_interior).preimage continuous_paperInY
  have hmem : ((v, 0) : E0) ∈ E0.paperInY ⁻¹' (κ.target ∩ κ.symm ⁻¹' interior N) := by
    show E0.paperInY ((v, 0) : E0) ∈ κ.target ∩ κ.symm ⁻¹' interior N
    rw [← hv]
    refine ⟨κ.map_source hpκ, ?_⟩
    rw [mem_preimage, κ.left_inv hpκ]
    exact mem_interior_iff_mem_nhds.2 hN
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT _ hmem
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hψ : IsE0Mor κ.symm κ.target :=
    e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart_symm hQ
  refine ⟨v, δ, hδ, hv, fun x hx => ⟨(hball hx).1, interior_subset (hball hx).2⟩,
    fun x hx hr hf => ?_⟩
  have hax : ((v, 0) : E0) ∈ E0.axis := rfl
  have hI : x ∈ E0.causality.Iplus ⟨Metric.ball ((v, 0) : E0) δ, Metric.isOpen_ball⟩
      {((v, 0) : E0)} := by
    rw [E0.Iplus_ball_axis hax]; exact ⟨hx, hr, hf⟩
  have hlt := Causal.Precausality.mem_Iplus_singleton.1 hI
  have h := lt_of_isE0Mor_paper κ.open_target hψ
    (U := ⟨Metric.ball ((v, 0) : E0) δ, Metric.isOpen_ball⟩) (fun z hz => (hball hz).1) hlt
  rwa [← hv, κ.left_inv hpκ] at h

/-- **The chart step** (`BTZ_1.tex:1432–1493`, the first bullet, one point at a time): let `f` be an
injective `𝔼₀`-morphism on an open `D ⊆ M₁` with BTZ complement, into a globally hyperbolic `M₂`.
If `(p, r)` is in the closure of the graph of `f` over `D`, then `f` extends, as an `𝔼₀`-morphism,
over `D ∪ V` for an open `V ∋ p`. At a BTZ `p ∉ D`: shrinking diamonds give `q'` and `b ≫ p` with
`f(I⁺(p) ∩ I⁻(b))` in a chart `c'` of `M₂` at `q'` landing in `𝔼₀`; `prop:isom_strong`
(`GX.e0_localUnique_sing`) on the region `{τ − r/2 > v}` of a ball of the chart `κ` at `p` gives
`e ∈ G` with `c' ∘ f ∘ κ⁻¹ = e` there; `e (κ p) = c' q'`; on a smaller ball `c'⁻¹ ∘ e ∘ κ` is an
`𝔼₀`-morphism equal to `f` (Liouville on the connected regular part, then density). This is the
lemma T-btz-pgcd-dom-gh reuses at the first missing point of a BTZ line. -/
theorem exists_ext_of_graphCluster (hG₂ : (CE M₂).GloballyHyperbolic) {D : Opens M₁}
    (hD : (D : Set M₁)ᶜ ⊆ S0 M₁) {f : M₁ → M₂} (hf : IsE0Mor f D) (hinj : InjOn f D)
    {p : M₁} {r : M₂} (hcl : GraphCluster D f p r) :
    ∃ V : Opens M₁, p ∈ V ∧ ∃ g : M₁ → M₂, IsE0Mor g (D ⊔ V : Opens M₁) ∧ EqOn g f D := by
  classical
  by_cases hpD : p ∈ D
  · refine ⟨D, hpD, f, ?_, fun _ _ => rfl⟩
    rw [sup_idem]; exact hf
  have hpS : p ∈ S0 M₁ := hD hpD
  have hsfa := E0AbsMax.e0_sfa_of_globalBTZ M₁
  have hDreg : ∀ x, x ∉ S0 M₁ → x ∈ D := fun x hx => by_contra fun h => hx (hD h)
  -- the cluster point `q'`, a chart `c'` at `q'` landing in `𝔼₀`, and `b ≫ p`
  obtain ⟨q', -, hshrink⟩ := exists_graphCluster_shrink hG₂ hD hf hcl
  obtain ⟨c', hc', hq'c', hc't⟩ := exists_chart_inr q'
  obtain ⟨b, hpb, hb⟩ := hshrink c'.source (c'.open_source.mem_nhds hq'c')
  obtain ⟨v, δ, hδ, hv, hball, hlt⟩ := exists_ball_chart hpS
    ((CE M₁).isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hpb))
  set κ := chartAt E0Y p with hκ
  have hpκ : p ∈ κ.source := mem_chart_source E0Y p
  -- the region `U₀ = B ∩ {τ − r/2 > v}` above the vertex, and `U` its image in `Y`
  set U₀ : Set E0 := Metric.ball ((v, 0) : E0) δ ∩ {x | v < E0.fcoord x} with hU₀
  have hU₀o : IsOpen U₀ :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const E0.continuous_fcoord)
  have hcv : Convex ℝ {x : E0 | v < E0.fcoord x} := by
    intro x hx y hy a c ha hc hac
    simp only [mem_setOf_eq, E0.fcoord, E0.rad] at hx hy ⊢
    have h1 : ‖(a • x + c • y).2‖ ≤ a * ‖x.2‖ + c * ‖y.2‖ := by
      rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd]
      calc _ ≤ ‖a • x.2‖ + ‖c • y.2‖ := norm_add_le _ _
        _ = a * ‖x.2‖ + c * ‖y.2‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hc]
    have h2 : (a • x + c • y).1 = a * x.1 + c * y.1 := by simp
    rw [h2]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have hc1 : c = 1 := by linarith
      subst hc1
      nlinarith
    · have e1 := mul_lt_mul_of_pos_left hx ha0
      have e2 := mul_le_mul_of_nonneg_left hy.le hc
      have e3 : a * v + c * v = v := by rw [← add_mul, hac, one_mul]
      nlinarith
  set y₀E : E0 := (v + δ / 2, 0) with hy₀E
  have hy₀E : y₀E ∈ U₀ := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · show dist (v + δ / 2) v < δ
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      · show dist (0 : ℂ) 0 < δ
        rw [dist_self]; exact hδ
    · show v < (v + δ / 2) - ‖(0 : ℂ)‖ / 2
      rw [norm_zero]; linarith
  have hU₀c : IsConnected U₀ :=
    ((convex_ball _ _).inter hcv).isConnected ⟨y₀E, hy₀E⟩
  set U : Set E0Y := E0.paperInY '' U₀ with hU
  have hUo : IsOpen U := isOpen_paperInY_image hU₀o
  have hUc : IsConnected U := hU₀c.image _ continuous_paperInY.continuousOn
  set y₀ : E0Y := E0.paperInY y₀E with hy₀
  have hy₀U : y₀ ∈ U := ⟨y₀E, hy₀E, rfl⟩
  have hy₀s : y₀ ∈ e0SingY 0 := (E0AbsMax.e0Loop_paperInY_mem_sing_iff _).2 rfl
  set R : Set E0Y := U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ e0SingY α} with hR
  -- the regular points of `U` come from points of `U₀` off the axis
  have hRx : ∀ y ∈ R, ∃ x ∈ U₀, y = E0.paperInY x ∧ 0 < E0.rad x := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, hx, rfl, ?_⟩
    have hns := hy 0 le_rfl
    rw [E0AbsMax.e0Loop_paperInY_mem_sing_iff] at hns
    exact norm_pos_iff.2 hns
  -- read in `M₁`, they are in `I⁺(p) ∩ I⁻(b)`, so in `D`, with images in the source of `c'`
  have hRκ : ∀ y ∈ R, y ∈ κ.target ∧ κ.symm y ∈ D ∧ f (κ.symm y) ∈ c'.source := by
    intro y hy
    obtain ⟨x, hx, rfl, hr⟩ := hRx y hy
    obtain ⟨hxT, hxb⟩ := hball x hx.1
    have hpx := hlt x hx.1 hr hx.2
    have hxb' : (CE M₁).lt ⊤ (κ.symm (E0.paperInY x)) b :=
      Causal.Precausality.mem_Iminus_singleton.1 hxb
    exact ⟨hxT, hDreg _ (E0AbsMax.notMem_sing_of_lt hsfa hpx), hb _ hpx hxb'⟩
  -- `F = c' ∘ f ∘ κ⁻¹` on `reg U`, and `prop:isom_strong`
  set F : E0Y → E0Y := fun y => c' (f (κ.symm y)) with hFdef
  have hloc : ∀ y ∈ R, e0Groupoid.IsLocalStructomorphWithinAt F R y := by
    intro y hy _
    obtain ⟨hyT, hyD, hyc⟩ := hRκ y hy
    have hx := hf (κ.symm y) hyD
    have h := ((StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
      e0Groupoid).liftPropWithinAt_indep_chart (e0Groupoid.chart_mem_maximalAtlas p)
      (κ.map_target hyT) hc' hyc).1 hx
    rw [κ.right_inv hyT] at h
    obtain ⟨e, he, heq, hye⟩ := h.2 (show κ.symm y ∈ (D : Set M₁) from hyD)
    exact ⟨e, he, fun z hz => heq ⟨(hRκ z hz.1).2.1, hz.2⟩, hye⟩
  have hinjF : InjOn F R := by
    intro y₁ h₁ y₂ h₂ he
    obtain ⟨t₁, d₁, c₁⟩ := hRκ y₁ h₁
    obtain ⟨t₂, d₂, c₂⟩ := hRκ y₂ h₂
    have h3 := hinj d₁ d₂ (c'.injOn c₁ c₂ he)
    exact κ.symm.injOn (by rwa [κ.symm_source]) (by rwa [κ.symm_source]) h3
  have hy₀inr : y₀ = Sum.inr (E0.toPaper.symm y₀E) := E0.paperInY_apply _
  have hmaps : MapsTo F R (connectedComponent y₀) := by
    intro y hy
    rw [hy₀inr, connectedComponent_inr_eq]
    exact hc't (c'.map_source (hRκ y hy).2.2)
  obtain ⟨e, he, hsrc, heq⟩ :=
    e0_localUnique_sing U hUo hUc y₀ hy₀U 0 le_rfl hy₀s F hloc hinjF hmaps
  have hinr_e : ∀ x : E0, E0.paperInY x ∈ e.source := fun x => by
    apply hsrc
    rw [hy₀inr, connectedComponent_inr_eq, E0.paperInY_apply]
    exact ⟨_, rfl⟩
  -- `e (κ p) = c' q'`, along the curve `t ↦ (v + t, t)`, `t ↘ 0`
  set xt : ℝ → E0 := fun t => (v + t, (t : ℂ)) with hxt
  have hxtc : Continuous xt := (continuous_const.add continuous_id).prodMk Complex.continuous_ofReal
  have hxt0 : xt 0 = ((v, 0) : E0) := by simp [hxt]
  have hxtU : ∀ t, 0 < t → t < δ → xt t ∈ U₀ ∧ 0 < E0.rad (xt t) := by
    intro t ht0 htδ
    have hr : E0.rad (xt t) = t := by
      show ‖(t : ℂ)‖ = t
      rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]
    refine ⟨⟨?_, ?_⟩, by rw [hr]; exact ht0⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      refine max_lt ?_ ?_
      · show dist (v + t) v < δ
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      · show dist (t : ℂ) 0 < δ
        rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht0.le]; exact htδ
    · show v < E0.fcoord (xt t)
      unfold E0.fcoord
      rw [hr]
      show v < v + t - t / 2
      linarith
  have hxtR : ∀ t, 0 < t → t < δ → E0.paperInY (xt t) ∈ R := by
    intro t ht0 htδ
    obtain ⟨hU', hr⟩ := hxtU t ht0 htδ
    refine ⟨⟨_, hU', rfl⟩, fun α _ hα => ?_⟩
    obtain ⟨rfl, -⟩ := e0SingY_mem hα
    rw [E0AbsMax.e0Loop_paperInY_mem_sing_iff] at hα
    exact (norm_pos_iff.1 hr) hα
  have hκp : κ p = E0.paperInY ((v, 0) : E0) := hv
  have hxl : Tendsto (fun t => E0.paperInY (xt t)) (𝓝 0) (𝓝 (κ p)) := by
    have h := (continuous_paperInY.comp hxtc).tendsto 0
    rw [comp_apply, hxt0, ← hκp] at h
    exact h
  have hwt : Tendsto (fun t => κ.symm (E0.paperInY (xt t))) (𝓝 0) (𝓝 p) := by
    have h1 := (κ.continuousAt_symm (κ.map_source hpκ)).tendsto.comp hxl
    rwa [κ.left_inv hpκ] at h1
  have hfw : Tendsto (fun t => f (κ.symm (E0.paperInY (xt t)))) (𝓝[>] 0) (𝓝 q') := by
    refine Filter.tendsto_iff_forall_eventually_mem.2 fun O hO => ?_
    obtain ⟨b', hpb', hb'⟩ := hshrink O hO
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), κ.symm (E0.paperInY (xt t)) ∈ (CE M₁).Iminus ⊤ {b'} :=
      (hwt.mono_left nhdsWithin_le_nhds).eventually ((CE M₁).isOpen_Iminus.mem_nhds
        (Causal.Precausality.mem_Iminus_singleton.2 hpb'))
    filter_upwards [hI, Ioo_mem_nhdsGT hδ] with t ht htI
    obtain ⟨hU', hr⟩ := hxtU t htI.1 htI.2
    exact hb' _ (hlt _ hU'.1 hr hU'.2) (Causal.Precausality.mem_Iminus_singleton.1 ht)
  have hepq : e (κ p) = c' q' := by
    have hl1 : Tendsto (fun t => c' (f (κ.symm (E0.paperInY (xt t))))) (𝓝[>] 0) (𝓝 (c' q')) :=
      (c'.continuousAt hq'c').tendsto.comp hfw
    have hl2 : Tendsto (fun t => e (E0.paperInY (xt t))) (𝓝[>] 0) (𝓝 (e (κ p))) := by
      have hκe : κ p ∈ e.source := by rw [hκp]; exact hinr_e _
      exact ((e.continuousAt hκe).tendsto.comp hxl).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (hl2.congr' ?_) hl1
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    exact (heq (hxtR t ht.1 ht.2)).symm
  -- a smaller ball `B'` on which `e` lands in the target of `c'`
  have hκe : κ p ∈ e.source := by rw [hκp]; exact hinr_e _
  have hec : e (κ p) ∈ c'.target := by rw [hepq]; exact c'.map_source hq'c'
  have hecont : ContinuousAt (fun x : E0 => e (E0.paperInY x)) ((v, 0) : E0) := by
    refine ContinuousAt.comp (g := e) (f := E0.paperInY) ?_ continuous_paperInY.continuousAt
    rw [← hκp]; exact e.continuousAt hκe
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.mem_nhds_iff.1
    (hecont.preimage_mem_nhds (c'.open_target.mem_nhds (by rw [← hκp]; exact hec)))
  set δ' := min δ δ₁ with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ hδ₁
  set B' : Set E0 := Metric.ball ((v, 0) : E0) δ' with hB'
  have hB'B : B' ⊆ Metric.ball ((v, 0) : E0) δ := Metric.ball_subset_ball (min_le_left _ _)
  have hB'c : ∀ x ∈ B', e (E0.paperInY x) ∈ c'.target := fun x hx =>
    hδ₁b (Metric.ball_subset_ball (min_le_right _ _) hx)
  -- `V₀ = κ⁻¹(B')`, a neighbourhood of `p`, and `g₀ = c'⁻¹ ∘ e ∘ κ` on it
  set V₀ : Set M₁ := κ.source ∩ κ ⁻¹' (E0.paperInY '' B') with hV₀
  have hV₀o : IsOpen V₀ := κ.isOpen_inter_preimage (isOpen_paperInY_image Metric.isOpen_ball)
  have hpV₀ : p ∈ V₀ := ⟨hpκ, ⟨(v, 0), Metric.mem_ball_self hδ'0, hκp.symm⟩⟩
  have hV₀e : ∀ z ∈ V₀, κ z ∈ e.source ∧ e (κ z) ∈ c'.target := by
    rintro z ⟨-, x, hx, hxz⟩
    rw [← hxz]
    exact ⟨hinr_e x, hB'c x hx⟩
  set g₀ : M₁ → M₂ := fun z => c'.symm (e (κ z)) with hg₀
  have hg₀mor : IsE0Mor g₀ V₀ := by
    refine Causal.CBG.liftPropOn_of_maximalAtlas_rep (e0Groupoid.chart_mem_maximalAtlas p) hc'
      hV₀o (fun z hz => hz.1) (fun z hz => c'.map_target (hV₀e z hz).2) ?_ he
      (fun z hz => (hV₀e z hz).1) (fun z hz => c'.right_inv (hV₀e z hz).2)
    intro z hz
    exact (ContinuousAt.comp (g := c'.symm) (f := fun w => e (κ w))
      (c'.continuousAt_symm (hV₀e z hz).2) (ContinuousAt.comp (g := e) (f := κ)
        (e.continuousAt (hV₀e z hz).1) (κ.continuousAt hz.1))).continuousWithinAt
  -- its regular part `V₀'`, preconnected
  set W' : Set E0Y := E0.paperInY '' B' ∩ e0Reg with hW'
  have hW'T : W' ⊆ κ.target := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    exact (hball x (hB'B hx)).1
  set V₀' : Set M₁ := κ.source ∩ κ ⁻¹' W' with hV₀'
  have hV₀'o : IsOpen V₀' :=
    κ.isOpen_inter_preimage ((isOpen_paperInY_image Metric.isOpen_ball).inter isOpen_e0Reg)
  have hV₀'c : IsPreconnected V₀' := by
    rw [hV₀', ← κ.symm_image_eq_source_inter_preimage hW'T]
    refine (isPreconnected_inter_e0Reg (isOpen_paperInY_image Metric.isOpen_ball)
      (((convex_ball _ _).isPreconnected).image _ continuous_paperInY.continuousOn)).image _ ?_
    exact κ.continuousOn_symm.mono hW'T
  have hV₀'V₀ : V₀' ⊆ V₀ := fun z hz => ⟨hz.1, hz.2.1⟩
  have hV₀'D : V₀' ⊆ D := by
    intro z hz
    refine hDreg z fun hzS => ?_
    have h1 : z ∈ E0LM.e0RegM M₁ := (E0LM.mem_e0RegM_iff hz.1).2 hz.2.2
    exact h1 hzS
  -- `f = g₀` on `V₀'`: they agree near the axis point above `p`, and Liouville
  set O' : Set M₁ := V₀' ∩ (κ.source ∩ κ ⁻¹' U) with hO'
  have hO'o : IsOpen O' := hV₀'o.inter (κ.isOpen_inter_preimage hUo)
  have hO'eq : EqOn f g₀ O' := by
    intro z hz
    have hzR : κ z ∈ R := ⟨hz.2.2, by rw [e0RegSet_eq]; exact hz.1.2.2⟩
    have h1 := heq hzR
    simp only [hFdef, κ.left_inv hz.1.1] at h1
    show f z = c'.symm (e (κ z))
    rw [← h1, c'.left_inv]
    have := (hRκ _ hzR).2.2
    rwa [κ.left_inv hz.1.1] at this
  have hO'ne : O'.Nonempty := by
    set t := min δ δ' / 2 with ht
    have ht0 : 0 < t := by have := lt_min hδ hδ'0; linarith
    have htδ : t < δ := by have := min_le_left δ δ'; linarith
    have htδ' : t < δ' := by have := min_le_right δ δ'; linarith
    obtain ⟨hU', -⟩ := hxtU t ht0 htδ
    have hxR := hxtR t ht0 htδ
    have hxT := (hRκ _ hxR).1
    refine ⟨κ.symm (E0.paperInY (xt t)), ⟨κ.map_target hxT, ?_⟩, κ.map_target hxT, ?_⟩
    · rw [mem_preimage, κ.right_inv hxT]
      refine ⟨⟨xt t, ?_, rfl⟩, ?_⟩
      · exact (Metric.mem_ball.2 (lt_of_le_of_lt (le_of_eq rfl)
          (show dist (xt t) ((v, 0) : E0) < δ' by
            rw [Prod.dist_eq]
            refine max_lt ?_ ?_
            · show dist (v + t) v < δ'
              rw [Real.dist_eq, abs_lt]; constructor <;> linarith
            · show dist (t : ℂ) 0 < δ'
              rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ht0.le]; exact htδ')))
      · have := hxR.2
        rwa [e0RegSet_eq] at this
    · rw [mem_preimage, κ.right_inv hxT]; exact ⟨_, hU', rfl⟩
  have hfV₀' : IsE0Mor f V₀' := Causal.CBG.liftPropOn_mono_of_le D.isOpen hV₀'o hf hV₀'D
  have hgV₀' : IsE0Mor g₀ V₀' := Causal.CBG.liftPropOn_mono_of_le hV₀o hV₀'o hg₀mor hV₀'V₀
  have hV₀'eq : EqOn f g₀ V₀' :=
    Causal.CBG.eqOn_of_liftPropOn e0_rigid hV₀'o hV₀'c hfV₀' hgV₀' hO'o inter_subset_left
      hO'ne hO'eq
  -- and on `V₀ ∩ D`, by density of the regular points
  have hV₀Deq : EqOn f g₀ (V₀ ∩ D) := by
    refine Set.EqOn.of_subset_closure (s := V₀') hV₀'eq ?_ ?_ (fun z hz => ⟨hV₀'V₀ hz, hV₀'D hz⟩) ?_
    · exact fun z hz => (hf z hz.2).continuousWithinAt.mono inter_subset_right
    · exact fun z hz => (hg₀mor z hz.1).continuousWithinAt.mono inter_subset_left
    · intro z hz
      have h1 := (E0LM.dense_e0RegM (M := M₁)).open_subset_closure_inter hV₀o hz.1
      refine closure_mono ?_ h1
      rintro w ⟨hwV, hwr⟩
      exact ⟨hwV.1, hwV.2, (E0LM.mem_e0RegM_iff hwV.1).1 hwr⟩
  -- the extension
  set V : Opens M₁ := ⟨V₀, hV₀o⟩ with hV
  set G : M₁ → M₂ := fun z => if z ∈ (D : Set M₁) then f z else g₀ z with hG
  refine ⟨V, hpV₀, G, ?_, fun z hz => if_pos hz⟩
  have hcoe : ((D ⊔ V : Opens M₁) : Set M₁) = (D : Set M₁) ∪ V₀ := Opens.coe_sup D V
  rw [hcoe]
  refine Causal.CBG.liftPropOn_of_locally (D.isOpen.union hV₀o) fun z hz => ?_
  rcases hz with hz | hz
  · exact ⟨D, D.isOpen, subset_union_left, hz,
      Causal.CBG.liftPropOn_congr_of_eqOn D.isOpen hf fun w hw => (if_pos hw).symm⟩
  · refine ⟨V₀, hV₀o, subset_union_right, hz,
      Causal.CBG.liftPropOn_congr_of_eqOn hV₀o hg₀mor fun w hw => ?_⟩
    by_cases hwD : w ∈ (D : Set M₁)
    · rw [hG]; simp only [if_pos hwD]; exact (hV₀Deq ⟨hw, hwD⟩).symm
    · rw [hG]; simp only [if_neg hwD]

end ChartStep

end PpcmHausdorff

end GX
