import GX.BTZ.SpearFamily

/-!
# `GX.BTZ.RegCompleteCauchy` — the surgered surface `Σ*` of a locally finite spear family is a Cauchy surface of `Reg M` (btz § 5.4)

Target T-btz-reg-complete-cauchy. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`). Row
(unmarked, partial; this file is step (2) of the Cauchy-completeness of `Reg M`,
`GX.E0RegComplete.regM_isCauchyComplete_of_complete`, assembled in
`GX/BTZ/RegCompleteLength.lean`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576, which cites the surgery of
  `prop:abs_max`'s proof (l.1090–1093) with possibly infinitely many spears.

> Consider $\Sigma$ a Cauchy-surface of $M$ and $\Sigma^*$ the Cauchy-surface of $M^*$ obtained by
> applying point (ii) of Lemma \ref{lem:curve_extension} in disjoint spear neighborhoods of
> $\sing_0(M)$. Using Corollary \ref{cor:intersect} we deduce that $\Sigma^*$ is a Cauchy surface
> of $M^*$ […] (l.1574–1575)

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

## What is proved (no `sorry` in this file; standard axioms only)

* `LFSurgeryData.sigmaStar`: `Σ*` of an `LFSurgeryData` (`GX.BTZ.SpearFamily`), `S`
  outside the spears and the cusp of Lemma 2.6(ii) inside each; `sigmaStar_toSurgeryData`: for a
  finite family it is the strict `E0Surgery.SurgeryData.sigmaStar`; `sigmaStar_toLFSpears`: it is
  `E0Surgery.LFSpears.sigmaStar` of `toLFSpears` (`rfl`), whence `sigmaStar_diff`,
  `sigmaStar_inter_spearSet` and `isClosed_iUnion_spearSet`.
* `LFSurgeryData.isCauchySurface_sigmaStar`: **`Σ*` is a Cauchy surface of `Reg M`** for every
  locally finite family, finitely or infinitely many spears, for `S` only a Cauchy surface of `M`
  (no compactness, no completeness, no smoothness). Remark 2.12 (`rem:curve_spear`) is not a
  hypothesis: it is the strict `SpearSurgeryDatum.isSpearArc_of_inextensible`, spear by spear.
* `exists_lfSurgeryData_isCauchySurface_sigmaStar`: steps (1) and (2) together.
* `LFSurgeryData.finite_spears_of_isCompact`: a compact set (e.g. a compact segment of an
  inextensible causal curve) meets only finitely many spears.

The proof is `E0Surgery.LFSpears.isCauchySurface_sigmaStar` (§5g of `GX/BTZ/Surgery.lean`),
read off through `toLFSpears` with `covers` as its `hcovers`; every lemma of the sides
(`cuspUp`, `cuspDown`, `futSide`, `pastSide`, whose definitions here are `rfl`-equal to those of
`toLFSpears`) is a one-line corollary of its `LFSpears` form, and `cauchy_facts_lf` is
`E0Surgery.cauchy_facts_of_isCauchySurface` (T-btz-g3-dedupe). Against the finite
`SurgeryData` proof, two uses of finiteness and two uses of compactness are replaced:
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
is `GX.BTZ.RegCompleteLength` (sorry-free since T-btz-reg-complete-tail);
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
      (∀ p, IsCompact ((E0CBG.CE M).Jplus ⊤ {p} ∩ S)) :=
  cauchy_facts_of_isCauchySurface hGH hS

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
/-- `Σ*` is the one of the common family `toLFSpears`. -/
theorem sigmaStar_toLFSpears : Dat.toLFSpears.sigmaStar = Dat.sigmaStar := rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is `Σ` outside the spears. -/
theorem sigmaStar_diff : Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet = S \ ⋃ i, (Dat.D i).spearSet :=
  Dat.toLFSpears.sigmaStar_diff

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `Σ*` is the cusp inside each spear. -/
theorem sigmaStar_inter_spearSet (i : Dat.ι) :
    Dat.sigmaStar ∩ (Dat.D i).spearSet = (Dat.D i).cusp :=
  Dat.toLFSpears.sigmaStar_inter_spearSet i

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
theorem cuspUp_subset (i : Dat.ι) : Dat.cuspUp i ⊆ (Dat.D i).spearSet :=
  Dat.toLFSpears.cuspUp_subset i

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
theorem cuspDown_subset (i : Dat.ι) : Dat.cuspDown i ⊆ (Dat.D i).spearSet :=
  Dat.toLFSpears.cuspDown_subset i

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- A point of a spear is in no other spear. -/
theorem eq_of_mem_spearSet {i j : Dat.ι} {y : M} (hi : y ∈ (Dat.D i).spearSet)
    (hj : y ∈ (Dat.D j).spearSet) : i = j :=
  Dat.toLFSpears.eq_of_mem_spearSet hi hj

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **The union of the spears is closed** (local finiteness, in place of finiteness). -/
theorem isClosed_iUnion_spearSet : IsClosed (⋃ i, (Dat.D i).spearSet) :=
  Dat.toLFSpears.isClosed_iUnion_spearSet

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **Near a point of spear `i`, no other spear** (local finiteness: a neighbourhood meets
finitely many spears, each closed, and only spear `i` contains the point). -/
theorem eventually_other (i : Dat.ι) {y : M} (hy : y ∈ (Dat.D i).spearSet) :
    ∀ᶠ z in 𝓝 y, ∀ j, z ∈ (Dat.D j).spearSet → j = i :=
  Dat.toLFSpears.eventually_other i hy

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- **`Σ*` is on both sides.** -/
theorem sigmaStar_subset_sides {y : M} (hy : y ∈ Dat.sigmaStar) :
    y ∈ Dat.futSide ∧ y ∈ Dat.pastSide :=
  Dat.toLFSpears.sigmaStar_subset_sides hy

/-- **The two sides meet exactly along `Σ*`.** -/
theorem mem_sigmaStar_of_sides (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {y : M} (hF : y ∈ Dat.futSide)
    (hP : y ∈ Dat.pastSide) : y ∈ Dat.sigmaStar :=
  Dat.toLFSpears.mem_sigmaStar_of_sides hGH hS hF hP

/-- **The two sides cover `Reg M`.** -/
theorem mem_sides_of_notMem_S0 (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {y : M} (hy : y ∉ E0CBG.S0 M) :
    y ∈ Dat.futSide ∨ y ∈ Dat.pastSide :=
  Dat.toLFSpears.mem_sides_of_notMem_S0 hGH hS hy

/-- **The future side is closed in `Reg M`** (the closure of the union of the `cuspUp i` is the
union of their closures: local finiteness). -/
theorem closure_futSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) : closure Dat.futSide ⊆ Dat.futSide ∪ E0CBG.S0 M :=
  Dat.toLFSpears.closure_futSide_subset hGH hS

/-- **The past side is closed in `Reg M`.** -/
theorem closure_pastSide_subset (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) : closure Dat.pastSide ⊆ Dat.pastSide ∪ E0CBG.S0 M :=
  Dat.toLFSpears.closure_pastSide_subset hGH hS

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Forward propagation of the future side** along a causal curve of `Reg M`. -/
theorem eventually_futSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.futSide) : ∀ᶠ s in 𝓝 t, t ≤ s → e s ∈ Dat.futSide :=
  Dat.toLFSpears.eventually_futSide he ht

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Backward propagation of the past side** along a causal curve of `Reg M`. -/
theorem eventually_pastSide {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) {t : ℝ} (ht : e t ∈ Dat.pastSide) :
    ∀ᶠ s in 𝓝 t, s ≤ t → e s ∈ Dat.pastSide :=
  Dat.toLFSpears.eventually_pastSide he he0 ht

/-- **A causal curve of `Reg M` inside `Σ*` is locally constant.** -/
theorem eventually_eq_of_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M}
    (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {t : ℝ} (ht : e t ∈ Dat.sigmaStar) : ∀ᶠ s in 𝓝 t, e s ∈ Dat.sigmaStar → e s = e t :=
  Dat.toLFSpears.eventually_eq_of_sigmaStar hGH hS he ht

/-- **A BTZ point in the causal future of a point of `S` lies inside a spear of the family**
(on the ray above the vertex, which is in `I⁻(S)`): `LFSpears.exists_open_of_BTZ` with `covers`,
whose proof uses of the family only that it covers `S ∩ sing₀(M)`, and of `S` only that it is
acausal. -/
theorem exists_open_of_BTZ (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {s q : M} (hsS : s ∈ S)
    (hsq : (E0CBG.CE M).le ⊤ s q) (hq0 : q ∈ E0CBG.S0 M) :
    ∃ j : Dat.ι, ∃ O : Set M, IsOpen O ∧ q ∈ O ∧ O ⊆ (Dat.D j).spearSet :=
  Dat.toLFSpears.exists_open_of_BTZ hGH hS Dat.covers hsS hsq hq0

/-- **Every inextensible causal curve of `Reg M` meets the past side** (`LFSpears.exists_pastSide`
with `covers`). As for the finite `E0Surgery.SurgeryData.exists_pastSide`, except where compactness of `S` was used: the points
`σ_n ∈ S` below `e(-n)` all lie in `J⁻(e 0) ∩ S`, which is compact for a Cauchy surface of a
globally hyperbolic `𝔼₀`-manifold (`cauchy_facts_lf`). -/
theorem exists_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.pastSide :=
  Dat.toLFSpears.exists_pastSide hGH hS Dat.covers hd harc

/-- **Every inextensible causal curve of `Reg M` meets the future side**
(`LFSpears.exists_futSide`). As for the finite `E0Surgery.SurgeryData.exists_futSide`, with `J⁺(e 0) ∩ S` compact in place of `S` compact. -/
theorem exists_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {d : ℝ → E0LM.e0RegM M} (hd : (E0CBG.CE (E0LM.e0RegM M)).Inextensible ⊤ univ d)
    (harc : ∀ (i : Dat.ι) (s₀ : ℝ), (d s₀ : M) ∈ (Dat.D i).spearSet →
      (Dat.D i).IsSpearArc (fun t => (Dat.D i).coord (d t : M))
        (connectedComponentIn {t ∈ (univ : Set ℝ) | (d t : M) ∈ (Dat.D i).spearSet} s₀)) :
    ∃ t, (d t : M) ∈ Dat.futSide :=
  Dat.toLFSpears.exists_futSide hGH hS hd harc

/-- The future side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_futSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.futSide) :=
  Dat.toLFSpears.isClosed_preimage_futSide hGH hS hec he0

/-- The past side, read along a curve of `Reg M`, is closed. -/
theorem isClosed_preimage_pastSide (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M} (hec : Continuous e)
    (he0 : ∀ t, e t ∉ E0CBG.S0 M) : IsClosed (e ⁻¹' Dat.pastSide) :=
  Dat.toLFSpears.isClosed_preimage_pastSide hGH hS hec he0

/-- **The future side is a future set along a causal curve of `Reg M`.** -/
theorem futSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (ha : e a ∈ Dat.futSide) (hab : a ≤ b) : e b ∈ Dat.futSide :=
  Dat.toLFSpears.futSide_of_le hGH hS he he0 ha hab

/-- **The past side is a past set along a causal curve of `Reg M`.** -/
theorem pastSide_of_le (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S)
    {e : ℝ → M} (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e) (he0 : ∀ t, e t ∉ E0CBG.S0 M)
    {a b : ℝ} (hb : e b ∈ Dat.pastSide) (hab : a ≤ b) : e a ∈ Dat.pastSide :=
  Dat.toLFSpears.pastSide_of_le hGH hS he he0 hb hab

/-- **A causal curve of `Reg M` lying in `Σ*` over a segment is constant there.** -/
theorem eq_of_forall_mem_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) {e : ℝ → M}
    (he : (E0CBG.CE M).CausalCurveIn ⊤ univ e)
    {a b : ℝ} (hab : a ≤ b) (h : ∀ r ∈ Icc a b, e r ∈ Dat.sigmaStar) : e b = e a :=
  Dat.toLFSpears.eq_of_forall_mem_sigmaStar hGH hS he hab h

/-- **btz l.1574–1575, step (2): `Σ*` is a Cauchy surface of `Reg M`**, for a locally finite
family of spears around the BTZ points of a Cauchy surface `S` of a globally hyperbolic
`𝔼₀`-manifold, finitely or infinitely many. Remark 2.12 (`rem:curve_spear`) in each spear is the
strict `SpearSurgeryDatum.isSpearArc_of_inextensible`; on a reparametrisation over `ℝ` the curve
meets both closed sides of `Σ*`, hence `Σ*` by connectedness, and only once (`Σ*` acausal). -/
theorem isCauchySurface_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hS : (E0CBG.CE M).IsCauchySurface S) (Dat : LFSurgeryData M S) :
    (Causal.Flat.flatCausality 2 (e0RegMFlat M)).IsCauchySurface Dat.sigmaStarReg :=
  Dat.toLFSpears.isCauchySurface_sigmaStar hGH hS Dat.covers

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
