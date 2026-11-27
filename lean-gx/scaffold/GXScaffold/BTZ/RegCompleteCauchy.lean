import GXScaffold.BTZ.SpearFamily

/-!
# `GXScaffold.BTZ.RegCompleteCauchy` — the surgered surface `Σ*` of a locally finite spear family is a Cauchy surface of `Reg M` (btz § 5.4)

Target T-btz-reg-complete-cauchy. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`). Row
(unmarked, partial; this file is step (2) of the Cauchy-completeness of `Reg M`,
`GX.E0RegComplete.regM_isCauchyComplete_of_complete`, assembled in
`GXScaffold/BTZ/RegCompleteLength.lean`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576, which cites the surgery of
  `prop:abs_max`'s proof (l.1090–1093) with possibly infinitely many spears.

> Consider $\Sigma$ a Cauchy-surface of $M$ and $\Sigma^*$ the Cauchy-surface of $M^*$ obtained by
> applying point (ii) of Lemma \ref{lem:curve_extension} in disjoint spear neighborhoods of
> $\sing_0(M)$. Using Corollary \ref{cor:intersect} we deduce that $\Sigma^*$ is a Cauchy surface
> of $M^*$ […] (l.1574–1575)

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

## What is proved (no `sorry` in this file; standard axioms only)

* `LFSurgeryData.sigmaStar`: `Σ*` of an `LFSurgeryData` (`GXScaffold.BTZ.SpearFamily`), `S`
  outside the spears and the cusp of Lemma 2.6(ii) inside each; `sigmaStar_toSurgeryData`: for a
  finite family it is the strict `E0Surgery.SurgeryData.sigmaStar`.
* `LFSurgeryData.isCauchySurface_sigmaStar`: **`Σ*` is a Cauchy surface of `Reg M`** for every
  locally finite family, finitely or infinitely many spears, for `S` only a Cauchy surface of `M`
  (no compactness, no completeness, no smoothness). Remark 2.12 (`rem:curve_spear`) is not a
  hypothesis: it is the strict `SpearSurgeryDatum.isSpearArc_of_inextensible`, spear by spear.
* `exists_lfSurgeryData_isCauchySurface_sigmaStar`: steps (1) and (2) together.
* `LFSurgeryData.finite_spears_of_isCompact`: a compact set (e.g. a compact segment of an
  inextensible causal curve) meets only finitely many spears.

The proof is the strict one of `E0Surgery.SurgeryData.isCauchySurface_sigmaStar` (§5g of
`GX/BTZ/Surgery.lean`), with its two uses of finiteness and its two uses of compactness replaced:
* finiteness (closure of a union of spears, a neighbourhood meeting one spear only) by **local
  finiteness** (`LocallyFinite.closure_iUnion`, `LocallyFinite.isClosed_iUnion`,
  `eventually_other`);
* compactness of `S` (closedness of `J^±(S)`; a limit point `s ∈ S` of points of `S` below a
  past-trapped curve) by the **closed `J^±(S)` of a Cauchy surface of a globally hyperbolic
  `𝔼₀`-manifold** (`E0LM.sfa_isClosed_Jplus_cauchy`) and the **compactness of `J^∓(p) ∩ S`**
  (`Causal.Causality.GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface`, with the
  time function `E0LM.e0_timeFunction`): the points of `S` below `e(-n)` all lie below `e(0)`.

« Corollary cor:intersect applied in each spear » is, as in the strict proof, the monotone height
of the cusp along `≼` in each spear chart (Lemma 2.7, `height_le_of_le`, `height_lt_of_le`) with
Remark 2.12's spear arcs, read through the two closed sides of `Σ*` (`futSide`, `pastSide`); an
inextensible curve meeting infinitely many spears needs nothing more, because every step is local
along the curve and a neighbourhood meets finitely many spears (`eventually_other`).

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope), as the row: `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable |
| globally hyperbolic | ✓ `(CE M).GloballyHyperbolic` |
| `Σ` a Cauchy surface (smooth spacelike complete) | ⚠ weakened: `(CE M).IsCauchySurface S` only; the smoothness enters through the spear data (`LFSurgeryData`, built from `RimC1`) |
| disjoint spear neighbourhoods | ✓ `LFSurgeryData` (disjoint, closed, locally finite: step (1), T-btz-spear-family) |
| Cauchy-maximal | ⚠ weakened for step (2): not used (it is used by step (1), `exists_lfSurgeryData`) |

## SCOPE (disclosed)

Step (2) only. That `Σ*` is complete for its induced length with infinitely many spears (step (3))
is `GXScaffold.BTZ.RegCompleteLength` (sorry-free since T-btz-reg-complete-tail);
`btzprop:reg_complete` stays partial for its `𝔼₀` scope.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0SpearFamily

open E0 E0Spear E0Surgery

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **The facts about a (not necessarily compact) Cauchy surface of a globally hyperbolic
`𝔼₀`-manifold** that replace compactness in the surgery: `S` acausal, `J^±(S)` closed, covering
`M` and meeting in `S`, and `J^∓(p) ∩ S` compact. -/
theorem cauchy_facts_lf (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) :
    (E0CBG.CE M).IsAcausal S ∧ IsClosed ((E0CBG.CE M).Jplus ⊤ S) ∧
      IsClosed ((E0CBG.CE M).Jminus ⊤ S) ∧
      (∀ y, y ∈ (E0CBG.CE M).Jplus ⊤ S ∪ (E0CBG.CE M).Jminus ⊤ S) ∧
      (∀ y, y ∈ (E0CBG.CE M).Jplus ⊤ S → y ∈ (E0CBG.CE M).Jminus ⊤ S → y ∈ S) ∧
      (∀ p, IsCompact ((E0CBG.CE M).Jminus ⊤ {p} ∩ S)) ∧
      (∀ p, IsCompact ((E0CBG.CE M).Jplus ⊤ {p} ∩ S)) := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E0Y M
  have hT := E0LM.e0_tarentin (M := M)
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hS.isAcausal E0LM.e0_causallyArcConnected hext
  have hSp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hS
  have hSm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hS
  obtain ⟨τ, hτc, hτ⟩ := E0LM.e0_timeFunction hGH
  refine ⟨hac, hSp, hSm,
    fun y => Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hS y, ?_,
    Causal.Causality.GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface hT hGH
      E0LM.e0_causallyArcConnected hτc hτ (fun _ hW => E0LM.sfa_isOpen_Jminus hA hW) hS hac hSp hSm,
    Causal.Causality.GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface hT hGH
      E0LM.e0_causallyArcConnected hτc hτ (fun _ hW => E0LM.sfa_isOpen_Jplus hA hW) hS hac hSp hSm⟩
  rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hyw⟩
  have h := hac z hz w hw ((E0CBG.CE M).le_trans hzy hyw)
  subst h
  rw [hGH.1 hyw hzy]; exact hz

namespace LFSurgeryData

variable {S : Set M} (Dat : LFSurgeryData M S)

/-- **The surgery `Σ*`** (B21 l.1091, btz l.1574) of a locally finite family: `Σ` outside the
spears, the cusp of Lemma 2.6(ii) inside each. -/
def sigmaStar : Set M := (S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, (Dat.D i).cusp

/-- `Σ*` read in `Reg M`. -/
def sigmaStarReg : Set (e0RegMFlat M) := regSet M Dat.sigmaStar

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- For a finite family, `Σ*` is the strict one. -/
theorem sigmaStar_toSurgeryData (h : Finite Dat.ι) :
    (Dat.toSurgeryData h).sigmaStar = Dat.sigmaStar := rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **Local finiteness along a curve**: a compact set (a compact segment of a causal curve) meets
only finitely many spears. -/
theorem finite_spears_of_isCompact {K : Set M} (hK : IsCompact K) :
    {i | ((Dat.D i).spearSet ∩ K).Nonempty}.Finite :=
  Dat.locallyFinite.finite_nonempty_inter_compact hK

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is `Σ` outside the spears. -/
theorem sigmaStar_diff : Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet = S \ ⋃ i, (Dat.D i).spearSet := by
  ext y
  simp only [sigmaStar, Set.mem_sdiff, mem_union, mem_iUnion]
  constructor
  · rintro ⟨h | ⟨i, hi⟩, hn⟩
    · exact h
    · exact absurd ⟨i, (Dat.D i).cusp_subset_spearSet hi⟩ hn
  · rintro ⟨h, hn⟩
    exact ⟨Or.inl ⟨h, hn⟩, hn⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is the cusp inside each spear. -/
theorem sigmaStar_inter_spearSet (i : Dat.ι) :
    Dat.sigmaStar ∩ (Dat.D i).spearSet = (Dat.D i).cusp := by
  ext y
  simp only [sigmaStar, mem_inter_iff, mem_union, Set.mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨⟨-, hn⟩ | ⟨j, hj⟩, hi⟩
    · exact absurd ⟨i, hi⟩ hn
    · rcases eq_or_ne j i with rfl | hji
      · exact hj
      · exact absurd hi (Set.disjoint_left.1 (Dat.disjoint hji) ((Dat.D j).cusp_subset_spearSet hj))
  · intro hy
    exact ⟨Or.inr ⟨i, hy⟩, (Dat.D i).cusp_subset_spearSet hy⟩

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **`Σ*` lies in `Reg M`.** -/
theorem sigmaStar_subset_regM : Dat.sigmaStar ⊆ (E0LM.e0RegM M : Set M) := by
  intro y hy hS0
  rcases hy with ⟨hyS, hn⟩ | hy
  · exact hn (Dat.covers ⟨hyS, hS0⟩)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    have := (Dat.D i).cusp_inter_S0
    exact (Set.eq_empty_iff_forall_notMem.1 this) y ⟨hi, hS0⟩

/-- The part of spear `i` (off the axis) on or above the cusp `Σ*_i`. -/
def cuspUp (i : Dat.ι) : Set M :=
  {y | y ∈ (Dat.D i).spearSet ∧ 0 < rad ((Dat.D i).coord y) ∧
    0 ≤ height (Dat.D i).G ((Dat.D i).coord y)}

/-- The part of spear `i` (off the axis) on or below the cusp `Σ*_i`. -/
def cuspDown (i : Dat.ι) : Set M :=
  {y | y ∈ (Dat.D i).spearSet ∧ 0 < rad ((Dat.D i).coord y) ∧
    height (Dat.D i).G ((Dat.D i).coord y) ≤ 0}

/-- **The future side of `Σ*`**: `J⁺(S)` outside the spears, on or above the cusps inside. -/
def futSide : Set M :=
  ((E0CBG.CE M).Jplus ⊤ S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, Dat.cuspUp i

/-- **The past side of `Σ*`**: `J⁻(S)` outside the spears, on or below the cusps inside. -/
def pastSide : Set M :=
  ((E0CBG.CE M).Jminus ⊤ S \ ⋃ i, (Dat.D i).spearSet) ∪ ⋃ i, Dat.cuspDown i

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cuspUp_subset (i : Dat.ι) : Dat.cuspUp i ⊆ (Dat.D i).spearSet := fun _ h => h.1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cuspDown_subset (i : Dat.ι) : Dat.cuspDown i ⊆ (Dat.D i).spearSet := fun _ h => h.1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- A point of a spear is in no other spear. -/
theorem eq_of_mem_spearSet {i j : Dat.ι} {y : M} (hi : y ∈ (Dat.D i).spearSet)
    (hj : y ∈ (Dat.D j).spearSet) : i = j := by
  by_contra h
  exact Set.disjoint_left.1 (Dat.disjoint h) hi hj

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The union of the spears is closed** (local finiteness, in place of finiteness). -/
theorem isClosed_iUnion_spearSet : IsClosed (⋃ i, (Dat.D i).spearSet) :=
  Dat.locallyFinite.isClosed_iUnion Dat.isClosed

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **Near a point of spear `i`, no other spear** (local finiteness: a neighbourhood meets
finitely many spears, each closed, and only spear `i` contains the point). -/
theorem eventually_other (i : Dat.ι) {y : M} (hy : y ∈ (Dat.D i).spearSet) :
    ∀ᶠ z in 𝓝 y, ∀ j, z ∈ (Dat.D j).spearSet → j = i := by
  obtain ⟨U, hU, hfin⟩ := Dat.locallyFinite y
  have h : ∀ j ∈ {j | ((Dat.D j).spearSet ∩ U).Nonempty},
      ∀ᶠ z in 𝓝 y, z ∈ (Dat.D j).spearSet → j = i := by
    intro j _
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ _ => hji
    · have hyj : y ∉ (Dat.D j).spearSet := fun h => hji (Dat.eq_of_mem_spearSet h hy)
      filter_upwards [(Dat.isClosed j).isOpen_compl.mem_nhds hyj] with z hz hzj
      exact absurd hzj hz
  filter_upwards [(eventually_all_finite hfin).2 h, hU] with z hz hzU j hj
  exact hz j ⟨z, hj, hzU⟩ hj

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **`Σ*` is on both sides.** -/
theorem sigmaStar_subset_sides {y : M} (hy : y ∈ Dat.sigmaStar) :
    y ∈ Dat.futSide ∧ y ∈ Dat.pastSide := by
  have href : (E0CBG.CE M).le ⊤ y y := (E0CBG.CE M).le_refl trivial
  rcases hy with ⟨hyS, hn⟩ | hy
  · exact ⟨Or.inl ⟨⟨y, hyS, href⟩, hn⟩, Or.inl ⟨⟨y, hyS, href⟩, hn⟩⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    have hg := (Dat.D i).coord_mem_graphSet hi
    have hsp := (Dat.D i).cusp_subset_spearSet hi
    exact ⟨Or.inr (mem_iUnion.2 ⟨i, hsp, hg.1, hg.2.2.ge⟩),
      Or.inr (mem_iUnion.2 ⟨i, hsp, hg.1, hg.2.2.le⟩)⟩

/-- **The two sides meet exactly along `Σ*`.** -/
theorem mem_sigmaStar_of_sides (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {y : M} (hF : y ∈ Dat.futSide)
    (hP : y ∈ Dat.pastSide) : y ∈ Dat.sigmaStar := by
  obtain ⟨-, -, -, -, hinter, -, -⟩ := cauchy_facts_lf hGH hS
  rcases hF with ⟨hJp, hn⟩ | hF
  · rcases hP with ⟨hJm, -⟩ | hP
    · exact Or.inl ⟨hinter y hJp hJm, hn⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hP
      exact absurd (mem_iUnion.2 ⟨i, hi.1⟩) hn
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hF
    rcases hP with ⟨-, hn⟩ | hP
    · exact absurd (mem_iUnion.2 ⟨i, hi.1⟩) hn
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hP
      have hij := Dat.eq_of_mem_spearSet hi.1 hj.1
      subst hij
      obtain ⟨hx, hxe⟩ := (Dat.D i).coord_mem hi.1
      have hg : (Dat.D i).coord y ∈ graphSet (Dat.D i).G (Dat.D i).R :=
        ⟨hi.2.1, hx.2, le_antisymm hj.2.2 hi.2.2⟩
      exact Or.inr (mem_iUnion.2 ⟨i, _, ⟨_, hg, rfl⟩, hxe⟩)

/-- **The two sides cover `Reg M`.** -/
theorem mem_sides_of_notMem_S0 (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {y : M} (hy : y ∉ E0CBG.S0 M) :
    y ∈ Dat.futSide ∨ y ∈ Dat.pastSide := by
  obtain ⟨-, -, -, hcov, -, -, -⟩ := cauchy_facts_lf hGH hS
  by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    have hr := (Dat.D i).rad_coord_pos hi hy
    rcases le_total 0 (height (Dat.D i).G ((Dat.D i).coord y)) with h | h
    · exact Or.inl (Or.inr (mem_iUnion.2 ⟨i, hi, hr, h⟩))
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨i, hi, hr, h⟩))
  · rcases hcov y with h | h
    · exact Or.inl (Or.inl ⟨h, hK⟩)
    · exact Or.inr (Or.inl ⟨h, hK⟩)

/-- **The future side is closed in `Reg M`** (the closure of the union of the `cuspUp i` is the
union of their closures: local finiteness). -/
theorem closure_futSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) : closure Dat.futSide ⊆ Dat.futSide ∪ E0CBG.S0 M := by
  obtain ⟨-, hJpc, -, -, hinter, -, -⟩ := cauchy_facts_lf hGH hS
  have hlf : LocallyFinite fun i => Dat.cuspUp i := Dat.locallyFinite.subset Dat.cuspUp_subset
  unfold futSide
  rw [closure_union, hlf.closure_iUnion]
  rintro y (hy | hy)
  · left
    have hyJ : y ∈ (E0CBG.CE M).Jplus ⊤ S := closure_minimal sdiff_subset hJpc hy
    by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
    swap
    · exact Or.inl ⟨hyJ, hK⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    set D := Dat.D i with hD
    obtain ⟨hx, hxe⟩ := D.coord_mem hi
    have hnb : ¬ (D.coord y).1 < D.τS (D.coord y).2 := fun hlt => by
      have hm : y ∈ (E0CBG.CE M).Jminus ⊤ S := hxe ▸ D.mem_Jminus_of_le_τS hx hlt.le
      have := (D.graph _ hx).1 (by rw [hxe]; exact hinter y hyJ hm)
      linarith
    have hbd := D.not_interior_of_mem_closure hy
      (fun z hz hzi => hz.2 (mem_iUnion.2 ⟨i, hzi⟩)) hi
    have hf : D.v < fcoord (D.coord y) := by
      by_contra hle
      push Not at hle
      apply hnb
      have h1 := D.shaft (D.coord y).2 hx.2
      have h2 : rad (D.coord y) ≤ D.R := hx.2
      simp only [fcoord] at hle
      change (D.coord y).1 < D.τS (D.coord y).2
      simp only [rad] at h2 h1 hle
      linarith
    have hR : rad (D.coord y) = D.R := le_antisymm hx.2 (not_lt.1 fun h => hbd ⟨hf, h⟩)
    refine Or.inr (mem_iUnion.2 ⟨i, hi, by rw [hR]; exact D.pos, ?_⟩)
    simp only [height, heightAt]
    rw [rim_value D.rim hR]
    push Not at hnb
    linarith
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    set D := Dat.D i with hD
    have hysp : y ∈ D.spearSet := closure_minimal (Dat.cuspUp_subset i) (Dat.isClosed i) hi
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    refine Or.inl (Or.inr (mem_iUnion.2 ⟨i, hysp, D.rad_coord_pos hysp h0, ?_⟩))
    by_contra hneg
    push Not at hneg
    have hf := D.continuousAt_height_ginv hysp h0
    have hev : ∀ᶠ z in 𝓝 y, height D.G (paperOfY (D.ginv z)) < 0 :=
      hf.eventually (gt_mem_nhds (by simp only; rw [D.paperOfY_ginv hysp]; exact hneg))
    obtain ⟨z, hzev, hzU⟩ := mem_closure_iff_nhds.1 hi _ hev
    have hz : height D.G (paperOfY (D.ginv z)) < 0 := hzev
    rw [D.paperOfY_ginv hzU.1] at hz
    linarith [hzU.2.2]

/-- **The past side is closed in `Reg M`.** -/
theorem closure_pastSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) : closure Dat.pastSide ⊆ Dat.pastSide ∪ E0CBG.S0 M := by
  obtain ⟨-, -, hJmc, -, hinter, -, -⟩ := cauchy_facts_lf hGH hS
  have hlf : LocallyFinite fun i => Dat.cuspDown i := Dat.locallyFinite.subset Dat.cuspDown_subset
  unfold pastSide
  rw [closure_union, hlf.closure_iUnion]
  rintro y (hy | hy)
  · have hyJ : y ∈ (E0CBG.CE M).Jminus ⊤ S := closure_minimal sdiff_subset hJmc hy
    by_cases hK : y ∈ ⋃ i, (Dat.D i).spearSet
    swap
    · exact Or.inl (Or.inl ⟨hyJ, hK⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.1 hK
    set D := Dat.D i with hD
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    left
    obtain ⟨hx, hxe⟩ := D.coord_mem hi
    have hr := D.rad_coord_pos hi h0
    have hna : ¬ D.τS (D.coord y).2 < (D.coord y).1 := fun hlt => by
      have hm : y ∈ (E0CBG.CE M).Jplus ⊤ S := hxe ▸ D.mem_Jplus_of_τS_le hx hlt.le
      have := (D.graph _ hx).1 (by rw [hxe]; exact hinter y hm hyJ)
      linarith
    have hbd := D.not_interior_of_mem_closure hy
      (fun z hz hzi => hz.2 (mem_iUnion.2 ⟨i, hzi⟩)) hi
    by_cases hf : D.v < fcoord (D.coord y)
    · have hR : rad (D.coord y) = D.R := le_antisymm hx.2 (not_lt.1 fun h => hbd ⟨hf, h⟩)
      refine Or.inr (mem_iUnion.2 ⟨i, hi, hr, ?_⟩)
      simp only [height, heightAt]
      rw [rim_value D.rim hR]
      push Not at hna
      linarith
    · push Not at hf
      refine Or.inr (mem_iUnion.2 ⟨i, hi, hr, ?_⟩)
      have h2 := D.above (rad (D.coord y), Complex.arg (D.coord y).2) hr hx.2
      have h3 : rad (D.coord y) ≤ D.R := hx.2
      simp only [fcoord] at hf
      simp only [height, heightAt]
      linarith
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    set D := Dat.D i with hD
    have hysp : y ∈ D.spearSet := closure_minimal (Dat.cuspDown_subset i) (Dat.isClosed i) hi
    by_cases h0 : y ∈ E0CBG.S0 M
    · exact Or.inr h0
    refine Or.inl (Or.inr (mem_iUnion.2 ⟨i, hysp, D.rad_coord_pos hysp h0, ?_⟩))
    by_contra hneg
    push Not at hneg
    have hf := D.continuousAt_height_ginv hysp h0
    have hev : ∀ᶠ z in 𝓝 y, 0 < height D.G (paperOfY (D.ginv z)) :=
      hf.eventually (lt_mem_nhds (by simp only; rw [D.paperOfY_ginv hysp]; exact hneg))
    obtain ⟨z, hzev, hzU⟩ := mem_closure_iff_nhds.1 hi _ hev
    have hz : 0 < height D.G (paperOfY (D.ginv z)) := hzev
    rw [D.paperOfY_ginv hzU.1] at hz
    linarith [hzU.2.2]

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Forward propagation of the future side** along a causal curve of `Reg M`. -/
theorem eventually_futSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.futSide) : ∀ᶠ s in 𝓝 t, t ≤ s → e s ∈ Dat.futSide := by
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := Dat.isClosed_iUnion_spearSet
  have hec : Continuous e := he.continuous
  rcases ht with ⟨⟨z, hz, hzt⟩, hK⟩ | ht
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hts
    exact Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans hzt (he.le_of_le trivial trivial hts)⟩, hs⟩
  obtain ⟨i, hyi, hr, hh⟩ := mem_iUnion.1 ht
  set D := Dat.D i with hD
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  have hin : ∀ s u, e s = D.ψ (paperInY u) → Le (D.coord (e t)) u →
      u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.futSide := by
    intro s u hus hle husp
    have hcu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    refine Or.inr (mem_iUnion.2 ⟨i, ?_, ?_, ?_⟩)
    · rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    · rw [hcu]; exact hr.trans_le hle.closed.2.1
    · rw [hcu]; exact hh.trans (height_le_of_le D.spacelike hle hr husp.2)
  rcases hx.2.lt_or_eq with hlt | heq
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | rad u < D.R} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_rad continuous_const)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hlt⟩ hxe.symm]
      with s ⟨u, hu, hus, hfut, _⟩ hts
    have hle := hfut hts
    have hf := (E0.calculus_le ((E0.le_top_iff).2 hle)).2.2.2.2.1
    exact hin s u hus hle ⟨hx.1.trans hf, hu.2.le⟩
  · have hτ : D.τS (D.coord (e t)).2 ≤ (D.coord (e t)).1 := by
      have h := hh
      simp only [height, heightAt] at h
      rw [rim_value D.rim heq] at h
      linarith
    obtain ⟨z, hz, hzt⟩ : e t ∈ (E0CBG.CE M).Jplus ⊤ S := hxe ▸ D.mem_Jplus_of_τS_le hx hτ
    filter_upwards [D.eventually_le_coord he hPo (image_preimage_subset _ _)
        (D.spear_sub ⟨_, hx, rfl⟩) hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, hfut, _⟩ hoth hts
    have hle := hfut hts
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hle husp
    · refine Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans hzt (he.le_of_le trivial trivial hts)⟩, ?_⟩
      intro hK
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu).1 hj)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Backward propagation of the past side** along a causal curve of `Reg M`. -/
theorem eventually_pastSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) {t : ℝ} (ht : e t ∈ Dat.pastSide) :
    ∀ᶠ s in 𝓝 t, s ≤ t → e s ∈ Dat.pastSide := by
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := Dat.isClosed_iUnion_spearSet
  have hec : Continuous e := he.continuous
  rcases ht with ⟨⟨z, hz, hzt⟩, hK⟩ | ht
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hst
    exact Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial hst) hzt⟩, hs⟩
  obtain ⟨i, hyi, hr, hh⟩ := mem_iUnion.1 ht
  set D := Dat.D i with hD
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  have hin : ∀ s u, e s = D.ψ (paperInY u) → Le u (D.coord (e t)) →
      u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.pastSide := by
    intro s u hus hle husp
    have hcu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    have hsp : e s ∈ D.spearSet := by rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    have hru : 0 < rad u := by rw [← hcu]; exact D.rad_coord_pos hsp (he0 s)
    refine Or.inr (mem_iUnion.2 ⟨i, hsp, by rw [hcu]; exact hru, ?_⟩)
    rw [hcu]; exact (height_le_of_le D.spacelike hle hru hx.2).trans hh
  by_cases hf : D.v < fcoord (D.coord (e t))
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | D.v < fcoord u} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_const continuous_fcoord)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf⟩ hxe.symm]
      with s ⟨u, hu, hus, _, hpast⟩ hst
    have hle := hpast hst
    exact hin s u hus hle ⟨hu.2.le, hle.closed.2.1.trans hx.2⟩
  · push Not at hf
    have hτ : (D.coord (e t)).1 ≤ D.τS (D.coord (e t)).2 := by
      have h1 := D.shaft (D.coord (e t)).2 hx.2
      have h2 : rad (D.coord (e t)) ≤ D.R := hx.2
      simp only [fcoord] at hf
      simp only [rad] at h1 h2 hf
      linarith
    obtain ⟨z, hz, hzt⟩ : e t ∈ (E0CBG.CE M).Jminus ⊤ S := hxe ▸ D.mem_Jminus_of_le_τS hx hτ
    filter_upwards [D.eventually_le_coord he hPo (image_preimage_subset _ _)
        (D.spear_sub ⟨_, hx, rfl⟩) hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, _, hpast⟩ hoth hst
    have hle := hpast hst
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hle husp
    · refine Or.inl ⟨⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial hst) hzt⟩, ?_⟩
      intro hK
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu).1 hj)

/-- **A causal curve of `Reg M` inside `Σ*` is locally constant.** -/
theorem eventually_eq_of_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M}
    (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.sigmaStar) : ∀ᶠ s in 𝓝 t, e s ∈ Dat.sigmaStar → e s = e t := by
  obtain ⟨hac, -, -, -, -, -, -⟩ := cauchy_facts_lf hGH hS
  have hKc : IsClosed (⋃ i, (Dat.D i).spearSet) := Dat.isClosed_iUnion_spearSet
  have hec : Continuous e := he.continuous
  have hcmp : ∀ s, e s ∈ S → e t ∈ S → e s = e t := fun s hs ht' => by
    rcases le_total s t with h | h
    · exact hac _ hs _ ht' (he.le_of_le trivial trivial h)
    · exact (hac _ ht' _ hs (he.le_of_le trivial trivial h)).symm
  have hSout : ∀ s, e s ∈ Dat.sigmaStar → e s ∉ ⋃ i, (Dat.D i).spearSet → e s ∈ S := by
    intro s h1 h2
    have h : e s ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨h1, h2⟩
    rw [Dat.sigmaStar_diff] at h
    exact h.1
  by_cases hK : e t ∈ ⋃ i, (Dat.D i).spearSet
  swap
  · filter_upwards [hec.continuousAt.preimage_mem_nhds (hKc.isOpen_compl.mem_nhds hK)] with s hs hsS
    exact hcmp s (hSout s hsS hs) (hSout t ht hK)
  obtain ⟨i, hyi⟩ := mem_iUnion.1 hK
  set D := Dat.D i with hD
  have hcu : e t ∈ D.cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨ht, hyi⟩
  have hg := D.coord_mem_graphSet hcu
  obtain ⟨hx, hxe⟩ := D.coord_mem hyi
  have hf := D.v_lt_fcoord_of_mem_graphSet hg
  have hPo : IsOpen (paperInY ⁻¹' D.W) := D.isOpen.preimage E0Spear.continuous_paperInY
  -- inside the spear, the cusp is acausal in the chart
  have hin : ∀ s u, e s = D.ψ (paperInY u) → (t ≤ s → Le (D.coord (e t)) u) →
      (s ≤ t → Le u (D.coord (e t))) → u ∈ E0Spear.spear D.v D.R → e s ∈ Dat.sigmaStar →
      e s = e t := by
    intro s u hus hfut hpast husp hsS
    have hsp : e s ∈ D.spearSet := by rw [hus]; exact ⟨_, ⟨u, husp, rfl⟩, rfl⟩
    have hcs : e s ∈ D.cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hsS, hsp⟩
    have hgs := D.coord_mem_graphSet hcs
    have hcuu : D.coord (e s) = u := by rw [hus]; exact D.coord_apply husp
    rw [hcuu] at hgs
    have hux : u = D.coord (e t) := by
      by_contra hne
      rcases le_total t s with h | h
      · have := height_lt_of_le D.spacelike (hfut h) hg.1 hgs.2.1 (Ne.symm hne)
        rw [hg.2.2, hgs.2.2] at this; exact lt_irrefl _ this
      · have := height_lt_of_le D.spacelike (hpast h) hgs.1 hg.2.1 hne
        rw [hg.2.2, hgs.2.2] at this; exact lt_irrefl _ this
    rw [hus, hux, hxe]
  rcases hg.2.1.lt_or_eq with hlt | heq
  · set V : Set E0 := paperInY ⁻¹' D.W ∩ ({u | D.v < fcoord u} ∩ {u | rad u < D.R}) with hV
    have hVo : IsOpen V := hPo.inter ((isOpen_lt continuous_const continuous_fcoord).inter
      (isOpen_lt continuous_rad continuous_const))
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf, hlt⟩ hxe.symm]
      with s ⟨u, hu, hus, hfut, hpast⟩ hsS
    exact hin s u hus hfut hpast ⟨hu.2.1.le, hu.2.2.le⟩ hsS
  · have htS : e t ∈ S := by
      have h1 : (D.coord (e t)).1 = D.τS (D.coord (e t)).2 :=
        (mem_graphSet_iff_of_rim D.pos D.rim heq).1 hg
      rw [← hxe]; exact (D.graph _ hx).2 h1
    set V : Set E0 := paperInY ⁻¹' D.W ∩ {u | D.v < fcoord u} with hV
    have hVo : IsOpen V := hPo.inter (isOpen_lt continuous_const continuous_fcoord)
    have hVW : paperInY '' V ⊆ D.W := by rintro _ ⟨u, hu, rfl⟩; exact hu.1
    filter_upwards [D.eventually_le_coord he hVo hVW ⟨D.spear_sub ⟨_, hx, rfl⟩, hf⟩ hxe.symm,
      hec.continuousAt.preimage_mem_nhds (Dat.eventually_other i hyi)]
      with s ⟨u, hu, hus, hfut, hpast⟩ hoth hsS
    by_cases husp : u ∈ E0Spear.spear D.v D.R
    · exact hin s u hus hfut hpast husp hsS
    · refine hcmp s (hSout s hsS fun hK' => ?_) htS
      obtain ⟨j, hj⟩ := mem_iUnion.1 hK'
      have hji : j = i := hoth j hj
      subst hji
      rw [hus] at hj
      exact husp ((D.mem_spearSet_iff hu.1).1 hj)

/-- **A BTZ point in the causal future of a point of `S` lies inside a spear of the family**
(on the ray above the vertex, which is in `I⁻(S)`): the strict `E0Surgery.exists_open_of_BTZ`,
whose proof uses of the family only that it covers `S ∩ sing₀(M)`, and of `S` only that it is
acausal. -/
theorem exists_open_of_BTZ (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {s q : M} (hsS : s ∈ S)
    (hsq : (E0CBG.CE M).le ⊤ s q) (hq0 : q ∈ E0CBG.S0 M) :
    ∃ j : Dat.ι, ∃ O : Set M, IsOpen O ∧ q ∈ O ∧ O ⊆ (Dat.D j).spearSet := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  obtain ⟨hac, -, -, -, -, -, -⟩ := cauchy_facts_lf hGH hS
  have hs0 : s ∈ E0CBG.S0 M := hA.mem_sing_zero_of_le hq0 hsq
  obtain ⟨j, hj⟩ := mem_iUnion.1 (Dat.covers ⟨hsS, hs0⟩)
  set D := Dat.D j with hD
  -- a point of `I⁻(S)` is not in `J⁺(S)`
  have hnot : ∀ y, (E0CBG.CE M).le ⊤ s y → y ∈ (E0CBG.CE M).Iminus ⊤ S → False := by
    rintro y hsy ⟨s'', hs'', hlt⟩
    have h1 := hac s hsS s'' hs'' ((E0CBG.CE M).le_trans hsy ((E0CBG.CE M).le_of_lt hlt))
    subst h1
    have h2 := hGH.1 ((E0CBG.CE M).le_of_lt hlt) hsy
    subst h2
    exact E0Spear.not_lt_self hGH _ hlt
  have hqc : s ∈ connectedComponentIn (E0CBG.S0 M) q := hA.Jminus_subset_component hq0 hsq
  have hsc : s ∈ connectedComponentIn (E0CBG.S0 M) D.p := D.spearSet_inter_S0_subset hj hs0
  have hqcp : q ∈ connectedComponentIn (E0CBG.S0 M) D.p := by
    rw [connectedComponentIn_eq hsc, ← connectedComponentIn_eq hqc]
    exact mem_connectedComponentIn hq0
  obtain ⟨t₁, ht₁, hst₁⟩ := D.eq_ray_of_mem_S0 hj hs0
  have hps : (E0CBG.CE M).le ⊤ D.p s := by
    have h := D.ray.le le_rfl ht₁
    rw [D.ray.zero] at h
    rw [hst₁]; exact h
  have hpq : (E0CBG.CE M).le ⊤ D.p q := (E0CBG.CE M).le_trans hps hsq
  obtain ⟨γ', hγ'0, hγ'e, hγ'i, hγ'r⟩ := (E0LM.e0_globalBTZ M).line D.p D.p_mem
  obtain ⟨σ, hσ⟩ : q ∈ range γ' := hγ'r ▸ hqcp
  have hqp : q ≠ D.p := fun h => hnot q hsq (h ▸ D.p_past)
  have hσ0 : 0 ≤ σ := by
    by_contra hneg
    push Not at hneg
    have h1 : (E0CBG.CE M).le ⊤ q D.p := by
      rw [← hσ, ← hγ'0]; exact hγ'i.1.le_of_le trivial trivial hneg.le
    exact hqp (hGH.1 h1 hpq)
  obtain ⟨t₂, ht₂, hts⟩ := D.ray.exists_eq_of_line hGH hγ'0 (hγ'e hGH.1) hγ'i.1 hγ'r hσ0
  have hq : q = D.ψ (paperInY ((D.v + t₂, 0) : E0)) := by rw [← hσ, ← hts]; rfl
  have ht₂0 : 0 < t₂ := by
    refine lt_of_le_of_ne ht₂ fun h0 => hqp ?_
    rw [hq, ← h0]
    have := D.ray.zero
    simpa [E0Spear.yAxis] using this
  set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const continuous_fcoord).inter (isOpen_lt continuous_rad continuous_const)
  have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ =>
    hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
  refine ⟨j, D.ψ '' (paperInY '' O), D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW,
    ⟨paperInY _, ⟨((D.v + t₂, 0) : E0), ?_, rfl⟩, hq.symm⟩, ?_⟩
  · have h0 : rad ((D.v + t₂, 0) : E0) = 0 := by simp [rad]
    refine ⟨?_, by rw [h0]; exact D.pos⟩
    simp only [fcoord, h0]; linarith
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩

/-- **Every inextensible causal curve of `Reg M` meets the past side.** As in the strict
`E0Surgery.SurgeryData.exists_pastSide`, except where compactness of `S` was used: the points
`σ_n ∈ S` below `e(-n)` all lie in `J⁻(e 0) ∩ S`, which is compact for a Cauchy surface of a
globally hyperbolic `𝔼₀`-manifold (`cauchy_facts_lf`). -/
theorem exists_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.pastSide := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hT := E0LM.e0_tarentin (M := M)
  obtain ⟨-, -, -, -, -, hcompm, -⟩ := cauchy_facts_lf hGH hS
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  by_cases hK : ∃ s₀ i, e s₀ ∈ (Dat.D i).spearSet
  · obtain ⟨s₀, i, hs₀⟩ := hK
    set D := Dat.D i with hD
    obtain ⟨-, -, hmono, hrad, hpast, -⟩ := harc i s₀ hs₀
    have hJ : ∀ t ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} s₀,
        e t ∈ D.spearSet := fun t ht => (connectedComponentIn_subset _ _ ht).2
    rcases hpast with ⟨t, ht, hneg⟩ | hax
    · exact ⟨t, Or.inr (mem_iUnion.2 ⟨i, hJ t ht, (hrad t ht).1, hneg.le⟩)⟩
    · have hJ0 : s₀ ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} s₀ :=
        mem_connectedComponentIn ⟨trivial, hs₀⟩
      obtain ⟨ε, hε, hεG⟩ := D.exists_lt_G_near_axis (D.coord (e s₀)).1
      obtain ⟨t, ht, htr⟩ := hax (min ε (rad (D.coord (e s₀)))) (lt_min hε (hrad s₀ hJ0).1)
      have hts : t ≤ s₀ := by
        by_contra h
        push Not at h
        have := (hmono s₀ hJ0 t ht h.le).closed.2.1
        linarith [min_le_right ε (rad (D.coord (e s₀)))]
      have hτ := fst_le_of_le (hmono t ht s₀ hJ0 hts)
      have hG := hεG (rad (D.coord (e t)), Complex.arg (D.coord (e t)).2) (hrad t ht).1
        (htr.trans_le (min_le_left _ _))
      refine ⟨t, Or.inr (mem_iUnion.2 ⟨i, hJ t ht, (hrad t ht).1, ?_⟩)⟩
      simp only [height, heightAt]
      linarith
  push Not at hK
  by_contra hno
  push Not at hno
  obtain ⟨hJm, -, hSC, hC, hcaus⟩ := regM_facts hGH
  have hJp : ∀ t, e t ∈ (E0CBG.CE M).Jplus ⊤ S := fun t => by
    rcases Dat.mem_sides_of_notMem_S0 hGH hS (d t).2 with h | h
    · rcases h with ⟨h, -⟩ | h
      · exact h
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        exact absurd hi.1 (hK t i)
    · exact absurd h (hno t)
  choose σ hσS hσle using fun n : ℕ => hJp (-(n : ℝ))
  have hσK : ∀ n, σ n ∈ (E0CBG.CE M).Jminus ⊤ {e 0} ∩ S := fun n => by
    refine ⟨⟨e 0, rfl, (E0CBG.CE M).le_trans (hσle n) (he.le_of_le trivial trivial ?_)⟩, hσS n⟩
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  obtain ⟨s, ⟨-, hsS⟩, φ, hφ, hlim⟩ := (hcompm (e 0)).tendsto_subseq hσK
  have hsle : ∀ t, (E0CBG.CE M).le ⊤ s (e t) := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_ge (-t)
    have hev : ∀ᶠ k in atTop, σ (φ k) ∈ (E0CBG.CE M).Jminus ⊤ {e t} := by
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with k hk
      refine ⟨e t, rfl, (E0CBG.CE M).le_trans (hσle (φ k)) (he.le_of_le trivial trivial ?_)⟩
      have : (N : ℝ) ≤ φ k := by exact_mod_cast hk
      linarith
    obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jminus_singleton hT (e t)).mem_of_tendsto hlim hev
    exact h
  obtain ⟨q, hq⟩ := exists_tendsto_atBot_of_monotone hGH (t₀ := 0)
    (fun a b hab _ => he.le_of_le trivial trivial hab) (hGH.2 s (e 0))
    (fun t ht => Causal.Causality.mem_diamond.2 ⟨hsle t, he.le_of_le trivial trivial ht⟩)
  by_cases hq0 : q ∈ E0CBG.S0 M
  · have hsq : (E0CBG.CE M).le ⊤ s q := by
      obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT s).mem_of_tendsto hq
        (Eventually.of_forall fun t => ⟨s, rfl, hsle t⟩)
      exact h
    obtain ⟨j, O, hO, hqO, hOsub⟩ := Dat.exists_open_of_BTZ hGH hS hsS hsq hq0
    obtain ⟨t, ht⟩ := (hq.eventually (hO.mem_nhds hqO)).exists
    exact hK t j (hOsub ht)
  · exact Causal.Causality.Inextensible.not_tendsto_atBot hJm hSC hC hcaus (regM_Jminus_ne hGH) hd
      ⟨q, hq0⟩ (tendsto_subtype_rng.2 hq)

/-- **Every inextensible causal curve of `Reg M` meets the future side.** As in the strict
`E0Surgery.SurgeryData.exists_futSide`, with `J⁺(e 0) ∩ S` compact in place of `S` compact. -/
theorem exists_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.futSide := by
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hT := E0LM.e0_tarentin (M := M)
  obtain ⟨-, -, -, -, -, -, hcompp⟩ := cauchy_facts_lf hGH hS
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  by_contra hno
  push Not at hno
  have hJm' : ∀ t, e t ∈ (E0CBG.CE M).Jminus ⊤ S := by
    intro t
    by_cases hK : ∃ i, e t ∈ (Dat.D i).spearSet
    · obtain ⟨i, hi⟩ := hK
      set D := Dat.D i with hD
      obtain ⟨-, -, hmono, hrad, -, hfut⟩ := harc i t hi
      have hJ : ∀ t' ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} t,
          e t' ∈ D.spearSet := fun t' ht' => (connectedComponentIn_subset _ _ ht').2
      have ht0 : t ∈ connectedComponentIn {t ∈ (univ : Set ℝ) | e t ∈ D.spearSet} t :=
        mem_connectedComponentIn ⟨trivial, hi⟩
      rcases hfut with hup | ⟨b, hb, hbmax, hbR⟩
      · exfalso
        obtain ⟨B, hB⟩ := D.exists_bound_G_annulus (hrad t ht0).1
        obtain ⟨t', ht', hT'⟩ := hup (max B (D.coord (e t)).1 + 1)
        have htt' : t ≤ t' := by
          by_contra h
          push Not at h
          have := fst_le_of_le (hmono t' ht' t ht0 h.le)
          linarith [le_max_right B (D.coord (e t)).1]
        have hle := hmono t ht0 t' ht' htt'
        have hG := hB _ hle.closed.2.1 (hrad t' ht').2
        apply hno t'
        refine Or.inr (mem_iUnion.2 ⟨i, hJ t' ht', (hrad t' ht').1, ?_⟩)
        simp only [height, heightAt]
        linarith [le_max_left B (D.coord (e t)).1]
      · have hbsp := hJ b hb
        obtain ⟨hx, hxe⟩ := D.coord_mem hbsp
        have hneg : height D.G (D.coord (e b)) < 0 := by
          by_contra h
          push Not at h
          exact hno b (Or.inr (mem_iUnion.2 ⟨i, hbsp, (hrad b hb).1, h⟩))
        have hτ : (D.coord (e b)).1 ≤ D.τS (D.coord (e b)).2 := by
          simp only [height, heightAt] at hneg
          rw [rim_value D.rim hbR] at hneg
          linarith
        obtain ⟨z, hz, hbz⟩ : e b ∈ (E0CBG.CE M).Jminus ⊤ S :=
          hxe ▸ D.mem_Jminus_of_le_τS hx hτ
        exact ⟨z, hz, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial (hbmax t ht0)) hbz⟩
    · push Not at hK
      rcases Dat.mem_sides_of_notMem_S0 hGH hS (d t).2 with h | h
      · exact absurd h (hno t)
      · rcases h with ⟨h, -⟩ | h
        · exact h
        · obtain ⟨i, hi⟩ := mem_iUnion.1 h
          exact absurd hi.1 (hK i)
  obtain ⟨-, hJp, hSC, hC, hcaus⟩ := regM_facts hGH
  choose σ hσS hσle using fun n : ℕ => hJm' (n : ℝ)
  have hσK : ∀ n, σ n ∈ (E0CBG.CE M).Jplus ⊤ {e 0} ∩ S := fun n => by
    refine ⟨⟨e 0, rfl, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial ?_) (hσle n)⟩, hσS n⟩
    exact n.cast_nonneg
  obtain ⟨s, ⟨-, hsS⟩, φ, hφ, hlim⟩ := (hcompp (e 0)).tendsto_subseq hσK
  have hsle : ∀ t, (E0CBG.CE M).le ⊤ (e t) s := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_ge t
    have hev : ∀ᶠ k in atTop, σ (φ k) ∈ (E0CBG.CE M).Jplus ⊤ {e t} := by
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with k hk
      refine ⟨e t, rfl, (E0CBG.CE M).le_trans (he.le_of_le trivial trivial ?_) (hσle (φ k))⟩
      have : (N : ℝ) ≤ φ k := by exact_mod_cast hk
      linarith
    obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT (e t)).mem_of_tendsto hlim hev
    exact h
  obtain ⟨q, hq⟩ := E0Spear.exists_tendsto_of_monotone hGH (t₀ := 0)
    (fun a b _ hab => he.le_of_le trivial trivial hab) (hGH.2 (e 0) s)
    (fun t ht => Causal.Causality.mem_diamond.2 ⟨he.le_of_le trivial trivial ht, hsle t⟩)
  have hq0 : q ∉ E0CBG.S0 M := by
    intro hq0
    have h0q : (E0CBG.CE M).le ⊤ (e 0) q := by
      obtain ⟨_, rfl, h⟩ := (hGH.isClosed_Jplus_singleton hT (e 0)).mem_of_tendsto hq
        (eventually_atTop.2 ⟨0, fun t ht => ⟨e 0, rfl, he.le_of_le trivial trivial ht⟩⟩)
      exact h
    exact (d 0).2 (hA.mem_sing_zero_of_le hq0 h0q)
  exact Causal.Causality.Inextensible.not_tendsto_atTop hJp hSC hC hcaus (regM_Jplus_ne hGH) hd
    ⟨q, hq0⟩ (tendsto_subtype_rng.2 hq)

/-- The future side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.futSide) := by
  have hc : IsClosed (Dat.futSide ∪ E0CBG.S0 M) := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union, isClosed_S0.closure_eq]
    exact union_subset (Dat.closure_futSide_subset hGH hS) subset_union_right
  have heq : e ⁻¹' Dat.futSide = e ⁻¹' (Dat.futSide ∪ E0CBG.S0 M) := by
    ext t
    simp only [mem_preimage, mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right (he0 t)⟩
  rw [heq]
  exact hc.preimage hec

/-- The past side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.pastSide) := by
  have hc : IsClosed (Dat.pastSide ∪ E0CBG.S0 M) := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union, isClosed_S0.closure_eq]
    exact union_subset (Dat.closure_pastSide_subset hGH hS) subset_union_right
  have heq : e ⁻¹' Dat.pastSide = e ⁻¹' (Dat.pastSide ∪ E0CBG.S0 M) := by
    ext t
    simp only [mem_preimage, mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right (he0 t)⟩
  rw [heq]
  exact hc.preimage hec

/-- **The future side is a future set along a causal curve of `Reg M`.** -/
theorem futSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (ha : e a ∈ Dat.futSide) (hab : a ≤ b) : e b ∈ Dat.futSide := by
  have hcl := Dat.isClosed_preimage_futSide hGH hS he.continuous he0
  refine (IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) ha
    fun x hx => ?_) (right_mem_Icc.2 hab)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Dat.eventually_futSide he hx.1)]
    with s hs h
  exact h (le_of_lt hs)

/-- **The past side is a past set along a causal curve of `Reg M`.** -/
theorem pastSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (hb : e b ∈ Dat.pastSide) (hab : a ≤ b) : e a ∈ Dat.pastSide := by
  set A : Set ℝ := {r | e (-r) ∈ Dat.pastSide} with hA
  have hcl : IsClosed A :=
    (Dat.isClosed_preimage_pastSide hGH hS he.continuous he0).preimage continuous_neg
  have hb' : -b ∈ A := by simp only [hA, mem_setOf_eq, neg_neg]; exact hb
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) hb'
    (b := -a) fun x hx => by
      have h := Dat.eventually_pastSide he he0 (t := -x) (by simpa [hA] using hx.1)
      have h' := (continuous_neg.tendsto x).eventually h
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h'] with r hr hr'
      exact hr' (neg_le_neg (le_of_lt hr))
  have := hsub (right_mem_Icc.2 (neg_le_neg hab))
  simpa [hA] using this

/-- **A causal curve of `Reg M` lying in `Σ*` over a segment is constant there.** -/
theorem eq_of_forall_mem_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M}
    (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ r ∈ Icc a b, e r ∈ Dat.sigmaStar) : e b = e a := by
  have hcl : IsClosed {r | e r = e a} := isClosed_eq he.continuous continuous_const
  refine (IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) rfl
    fun x hx => ?_) (right_mem_Icc.2 hab)
  have hxa : e x = e a := hx.1
  have hev := Dat.eventually_eq_of_sigmaStar hGH hS he (h x (Ico_subset_Icc_self hx.2))
  filter_upwards [Ioo_mem_nhdsGT hx.2.2, nhdsWithin_le_nhds hev] with s hs h'
  show e s = e a
  rw [← hxa]
  exact h' (h s ⟨hx.2.1.trans hs.1.le, hs.2.le⟩)

/-- **btz l.1574–1575, step (2): `Σ*` is a Cauchy surface of `Reg M`**, for a locally finite
family of spears around the BTZ points of a Cauchy surface `S` of a globally hyperbolic
`𝔼₀`-manifold, finitely or infinitely many. Remark 2.12 (`rem:curve_spear`) in each spear is the
strict `SpearSurgeryDatum.isSpearArc_of_inextensible`; on a reparametrisation over `ℝ` the curve
meets both closed sides of `Σ*`, hence `Σ*` by connectedness, and only once (`Σ*` acausal). -/
theorem isCauchySurface_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) (Dat : LFSurgeryData M S) :
    (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg := by
  intro I c hc
  have hc' : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ I c := by
    rw [← surgery_flatCausality_e0RegM_eq]; exact hc
  obtain ⟨-, -, -, hC, hcaus⟩ := regM_facts hGH
  obtain ⟨φ, -, -, hφr, hd⟩ := hc'.reparam hC hcaus (regM_Jminus_ne hGH) (regM_Jplus_ne hGH)
  set d : ℝ → E0LM.e0RegM M := c ∘ φ with hd_def
  set e : ℝ → M := fun t => (d t : M) with he_def
  have hval := E0Spear.isEMorphismOn_of_isE0Mor (W := ⊤) (E0Spear.isE0Mor_val (E0LM.e0RegM M))
  have he : (E0CBG.CE M).CausalCurveIn ⊤ univ e :=
    hval.causalCurveIn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hd.1
  have he0 : ∀ t, e t ∉ E0CBG.S0 M := fun t => (d t).2
  have harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀) :=
    fun i s₀ h => (Dat.D i).isSpearArc_of_inextensible hGH hd (mem_univ s₀) h
  obtain ⟨tF, htF⟩ := Dat.exists_futSide hGH hS hd harc
  obtain ⟨tP, htP⟩ := Dat.exists_pastSide hGH hS hd harc
  obtain ⟨t, -, htF', htP'⟩ := isPreconnected_closed_iff.1 isPreconnected_univ _ _
    (Dat.isClosed_preimage_futSide hGH hS he.continuous he0)
    (Dat.isClosed_preimage_pastSide hGH hS he.continuous he0)
    (fun t _ => Dat.mem_sides_of_notMem_S0 hGH hS (he0 t)) ⟨tF, trivial, htF⟩ ⟨tP, trivial, htP⟩
  have hts : e t ∈ Dat.sigmaStar := Dat.mem_sigmaStar_of_sides hGH hS htF' htP'
  have huniq : ∀ a b, a ≤ b → e a ∈ Dat.sigmaStar → e b ∈ Dat.sigmaStar → e b = e a := by
    intro a b hab ha hb
    refine Dat.eq_of_forall_mem_sigmaStar hGH hS he hab fun r hr => ?_
    exact Dat.mem_sigmaStar_of_sides hGH hS
      (Dat.futSide_of_le hGH hS he he0 (Dat.sigmaStar_subset_sides ha).1 hr.1)
      (Dat.pastSide_of_le hGH hS he he0 (Dat.sigmaStar_subset_sides hb).2 hr.2)
  refine ⟨d t, ⟨⟨φ t, hφr ▸ mem_range_self t, rfl⟩, hts⟩, ?_⟩
  rintro y ⟨⟨t', ht', rfl⟩, hy⟩
  obtain ⟨s', rfl⟩ : t' ∈ range φ := hφr ▸ ht'
  have hy' : e s' ∈ Dat.sigmaStar := hy
  show d s' = d t
  apply Subtype.ext
  rcases le_total s' t with h | h
  · exact (huniq s' t h hy' hts).symm
  · exact huniq t s' h hts hy'

end LFSurgeryData

/-- **Steps (1) and (2) of the non-compact surgery**: a Cauchy surface `S` with the `C¹` rim
condition of a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold carries a countable, locally
finite family of disjoint closed spears around `S ∩ sing₀(M)` whose `Σ*` lies in `Reg M` and is a
Cauchy surface of `Reg M`. -/
theorem exists_lfSurgeryData_isCauchySurface_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    {S : Set M} (hS : (E0CBG.CE M).IsCauchySurface S) (hrim : RimC1 M S)
    (hmax : E0Spear.IsE0CauchyMaximal M) :
    ∃ Dat : LFSurgeryData M S, Dat.sigmaStar ⊆ (E0LM.e0RegM M : Set M) ∧
      (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg := by
  obtain ⟨Dat⟩ := exists_lfSurgeryData_of_rimC1 hGH hS hrim hmax
  exact ⟨Dat, Dat.sigmaStar_subset_regM, Dat.isCauchySurface_sigmaStar hGH hS⟩

/-- **Steps (1) and (2) for a `C¹` spacelike complete Cauchy surface** (the row's reading of
« Cauchy-complete », `E0RegComplete.IsE0C1CompleteCauchy`). -/
theorem exists_lfSurgeryData_isCauchySurface_sigmaStar_of_complete
    (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : E0RegComplete.IsE0C1CompleteCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    ∃ Dat : LFSurgeryData M S, Dat.sigmaStar ⊆ (E0LM.e0RegM M : Set M) ∧
      (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg :=
  exists_lfSurgeryData_isCauchySurface_sigmaStar hGH hS.cauchy
    (rimC1_of_isE0C1CompleteCauchy hS) hmax

end E0SpearFamily

end GX
