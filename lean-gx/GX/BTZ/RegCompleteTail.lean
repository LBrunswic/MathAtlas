import GX.BTZ.LengthCompare

/-!
# `GX.BTZ.RegCompleteTail` — a Cauchy sequence of `Σ*` converges when the spear radii are summable (btz § 5.4)

Target T-btz-reg-complete-tail. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`). Row
(unmarked, partial: `𝔼₀`-scoped, T-btz-scope, and the readings OQ-142; this file is the last step
of `btzprop:reg_complete`'s Cauchy-completeness, the tail lemma
`LFSurgeryData.exists_isCompact_of_cauchySeq` of `GX/BTZ/RegCompleteLength.lean`, which is
now proved from `exists_isCompact_of_cauchySeq_of` below):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576: « the proof of
  Cauchy-completeness of Proposition prop:abs_max applies as is » (l.1571), which is B21 l.1093.

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

> Global hyperbolicity follows from Remark \ref{rem:reg_GH} and the proof of Cauchy-complete\-ness
> of Proposition \ref{prop:abs_max} applies as is. (l.1571)

## What is proved (no `sorry`; standard axioms only)

* **The core** `LFSurgeryData.core i` of the `i`-th cusp (its points with `r < R`): the spear is a
  neighbourhood of each of its points (`spearSet_mem_nhds_of_core`); a cusp point off the core is a
  rim point (`exists_rimPt_of_notMem_core`); a point of `Σ*` off every core lies on `S`
  (`mem_of_forall_notMem_core`).
* **A curve of `Σ*` lying on `S`** over `[a, b]` joins its ends in `S` within its `Σ*`-length
  (`edist_le_localLength_of_mem`, through `GX.BTZ.LengthCompare`'s comparison).
* **The surgery estimate** (`edist_le_localLength_add`, `edist_le_pathLength_add`): for a curve of
  `Σ*` with ends off every core, the `S`-distance of its ends is at most its `Σ*`-length plus
  `π Σᵢ Rᵢ` over the spears whose core it meets — spear by spear in order of first entry, the
  piece from the first entry to the last exit is replaced by a rim arc (`edist_rimPt_le`), each
  spear paid once (induction on the finite set of spears).
* **A path leaving a spear passes through a point off every core** (`exists_notMem_core_of_exit`).
* **(G5), the tail** (`exists_tendsto_of_cauchySeq_of`, `exists_isCompact_of_cauchySeq_of`): a
  Cauchy sequence of `Σ*` converges, and its tail lies in a compact set of `M`, when the radii are
  summable. Either it comes arbitrarily close, arbitrarily late, to one spear, and the `log r`
  estimate keeps the close points in a compact annulus graph; or every spear is eventually kept at
  a positive distance, the sequence is pushed off the cores to a sequence of `S ∩ Σ*`, Cauchy in
  `S` by the surgery estimate and `hsum`, hence convergent in `S` and in `M`. The facts of
  `RegCompleteLength` it uses (the compact case `tendsto_of_cauchySeq_of_isCompact`, the `log r`
  estimate `ofReal_abs_logRad_sub_le_edist`, the continuity of `Σ*` into `M`) are its hypotheses,
  discharged there, so that this file does not import it.

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected; second countability is not used here |
| Cauchy-complete | ⚠ read `IsE0C1CompleteCauchy` (OQ-142); here only its fields `complete` (the length space of `S` is complete) and `continuous` (its topology is finer than `M`'s), as hypotheses `hcomp`, `hcontS` |
| the spear neighbourhoods (B21 l.1090–1091) | ✓ `LFSurgeryData`, thinned to summable radii (`hsum`; `LFSurgeryData.exists_summable` of `RegCompleteLength` provides it, so no hypothesis is added to the proposition) |

## SCOPE (disclosed)

Nothing is assumed beyond the hypotheses above, each discharged in
`GX.BTZ.RegCompleteLength` (`LFSurgeryData.exists_isCompact_of_cauchySeq`).
`btzprop:reg_complete` stays partial: `𝔼₀`-scoped, and the readings of OQ-142 / DEC-31/35.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real ENNReal NNReal unitInterval

open E0 E0Spear E0Surgery

/-! ### Two facts on pseudo-emetric spaces -/

/-- A sequence at distance tending to `0` from a Cauchy sequence is Cauchy. -/
theorem cauchySeq_of_edist_tendsto_zero {α : Type*} [PseudoEMetricSpace α] {u x : ℕ → α}
    (hu : CauchySeq u) (h : Tendsto (fun n => edist (x n) (u n)) atTop (𝓝 0)) :
    CauchySeq x := by
  rw [EMetric.cauchySeq_iff] at hu ⊢
  intro ε hε
  have h3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top
  obtain ⟨N₁, hN₁⟩ := hu (ε / 3) h3
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h3))
  refine ⟨max N₁ N₂, fun m hm n hn => ?_⟩
  calc edist (x m) (x n) ≤ edist (x m) (u m) + edist (u m) (u n) + edist (u n) (x n) :=
        edist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        refine ENNReal.add_lt_add (ENNReal.add_lt_add (hN₂ m (le_of_max_le_right hm))
          (hN₁ m (le_of_max_le_left hm) n (le_of_max_le_left hn))) ?_
        rw [edist_comm]; exact hN₂ n (le_of_max_le_right hn)
    _ = ε := ENNReal.add_thirds ε

/-- A Cauchy sequence converges to the limit of a sequence close to one of its subsequences. -/
theorem tendsto_of_edist_subseq {α : Type*} [PseudoEMetricSpace α] {u x : ℕ → α}
    (hu : CauchySeq u) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (h : Tendsto (fun k => edist (x k) (u (φ k))) atTop (𝓝 0)) {a : α}
    (hx : Tendsto x atTop (𝓝 a)) : Tendsto u atTop (𝓝 a) := by
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hφ ?_
  rw [tendsto_iff_edist_tendsto_0] at hx ⊢
  have h2 : Tendsto (fun k => edist (x k) (u (φ k)) + edist (x k) a) atTop (𝓝 0) := by
    simpa using h.add hx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le)
    fun k => ?_
  calc edist (u (φ k)) a ≤ edist (u (φ k)) (x k) + edist (x k) a := edist_triangle _ _ _
    _ = _ := by rw [edist_comm]

namespace E0SpearFamily.LFSurgeryData

set_option linter.unusedSectionVars false

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
  [HasGroupoid M e0Groupoid]

variable {S : Set M} (Dat : LFSurgeryData M S)

/-! ### The core of a cusp, and the good points of `Σ*` -/

/-- The point of `M` under a point of `Σ*`. -/
def sPt (z : Dat.sigmaStarReg) : M := regVal M (z : e0RegMFlat M)

theorem sPt_mem (z : Dat.sigmaStarReg) : Dat.sPt z ∈ Dat.sigmaStar := z.2

theorem continuous_sPt : Continuous Dat.sPt := continuous_regVal.comp continuous_subtype_val

/-- **The core of the `i`-th cusp**: its points off the rim, `r < R`. -/
def core (i : Dat.ι) : Set M :=
  {z | z ∈ (Dat.D i).cusp ∧ rad ((Dat.D i).coord z) < (Dat.D i).R}

theorem core_subset_spearSet (i : Dat.ι) : Dat.core i ⊆ (Dat.D i).spearSet :=
  fun _ h => (Dat.D i).cusp_subset_spearSet h.1

/-- **The spear is a neighbourhood of each point of the core.** -/
theorem spearSet_mem_nhds_of_core {i : Dat.ι} {z : M} (hz : z ∈ Dat.core i) :
    (Dat.D i).spearSet ∈ 𝓝 z := by
  simp only [core, mem_setOf_eq] at hz
  obtain ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hr⟩ := hz
  set D := Dat.D i with hD
  have hxsp := D.graphSet_subset_spear hx
  rw [D.coord_apply hxsp] at hr
  have hx1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    have := hx.2.2; simp only [height, heightAt] at this; linarith
  have hfx : D.v < fcoord x := by
    have h2 := D.above (rad x, Complex.arg x.2) hx.1 hx.2.1
    simp only [fcoord]; rw [hx1]; linarith
  set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
      (isOpen_lt continuous_rad continuous_const)
  have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ =>
    hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
  have hOo' : IsOpen (D.ψ '' (paperInY '' O)) :=
    D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW
  refine Filter.mem_of_superset (hOo'.mem_nhds ⟨paperInY x, ⟨x, ⟨hfx, hr⟩, rfl⟩, rfl⟩) ?_
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩

/-- **A point of a cusp off its core is a rim point.** -/
theorem exists_rimPt_of_notMem_core {i : Dat.ι} {z : M} (hz : z ∈ (Dat.D i).cusp)
    (hn : z ∉ Dat.core i) : ∃ φ, z = (Dat.D i).rimPt φ := by
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  set D := Dat.D i with hD
  have hxsp := D.graphSet_subset_spear hx
  have hxR : rad x = D.R := by
    refine le_antisymm hx.2.1 (not_lt.1 fun h => hn ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩)
    rw [D.coord_apply hxsp]; exact h
  have hx1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    have := hx.2.2; simp only [height, heightAt] at this; linarith
  have hxS : D.ψ (paperInY x) ∈ S := (D.graph x hxsp).2 (by rw [hx1, rim_value D.rim hxR])
  exact ⟨_, D.eq_rimPt hxsp hxR hxS⟩

/-- **A point of `Σ*` off every core lies on `S`.** -/
theorem mem_of_forall_notMem_core {z : M} (hz : z ∈ Dat.sigmaStar) (hg : ∀ i, z ∉ Dat.core i) :
    z ∈ S := by
  by_cases hin : z ∈ ⋃ i, (Dat.D i).spearSet
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hin
    have hc : z ∈ (Dat.D i).cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hz, hi⟩
    obtain ⟨φ, rfl⟩ := Dat.exists_rimPt_of_notMem_core hc (hg i)
    exact (Dat.D i).rimPt_mem φ
  · have h : z ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨hz, hin⟩
    rw [Dat.sigmaStar_diff] at h; exact h.1

/-! ### A curve of `Σ*` lying on `S` is a curve of `S` of the same length -/

theorem exists_gt_of_eventually' {P : ℝ → Prop} {t b : ℝ} (htb : t < b)
    (h : ∀ᶠ s in 𝓝 t, P s) : ∃ s, t < s ∧ s ≤ b ∧ P s := by
  obtain ⟨δ, hδ, hP⟩ := Causal.Flat.exists_Icc_subset_of_eventually h
  have h1 : t < min b (t + δ) := lt_min htb (by linarith)
  exact ⟨min b (t + δ), h1, min_le_left _ _, hP _ ⟨by linarith, min_le_right _ _⟩⟩

theorem exists_lt_of_eventually' {P : ℝ → Prop} {a t : ℝ} (hat : a < t)
    (h : ∀ᶠ s in 𝓝 t, P s) : ∃ s, a ≤ s ∧ s < t ∧ P s := by
  obtain ⟨δ, hδ, hP⟩ := Causal.Flat.exists_Icc_subset_of_eventually h
  have h1 : max a (t - δ) < t := max_lt hat (by linarith)
  exact ⟨max a (t - δ), le_max_left _ _, h1, hP _ ⟨le_max_right _ _, by linarith⟩⟩

/-- **The `S`-distance between the ends of a curve of `Σ*` lying on `S` over `[a, b]` is at most
its `Σ*`-length over `[a, b]`** (the two chart systems agree on common points,
`localLength_chartSys_eq_e0SliceSys`). -/
theorem edist_le_localLength_of_mem {c : ℝ → Dat.sigmaStarReg} (hc : Continuous c)
    (hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c) {a b : ℝ}
    (hab : a ≤ b) (hS : ∀ t ∈ Icc a b, Dat.sPt (c t) ∈ S)
    (p q : Causal.Flat.LocalLengthSpace (e0SliceSys S))
    (hp : ((Causal.Flat.LocalLengthSpace.toSpace p : S) : M) = Dat.sPt (c a))
    (hq : ((Causal.Flat.LocalLengthSpace.toSpace q : S) : M) = Dat.sPt (c b)) :
    edist p q ≤ Causal.Flat.localLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c a b := by
  rcases hab.eq_or_lt with rfl | hab'
  · have : p = q := by
      apply Causal.Flat.LocalLengthSpace.toSpace.injective
      exact Subtype.ext (hp.trans hq.symm)
    rw [this, edist_self]; exact bot_le
  set pr : ℝ → ℝ := fun t => (projIcc a b hab t : ℝ) with hprdef
  have hpr : LipschitzWith 1 pr := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [hprdef, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_projIcc_sub_projIcc hab
  have hprI : ∀ t, pr t ∈ Icc a b := fun t => (projIcc a b hab t).2
  set low : ℝ → S := fun t => ⟨Dat.sPt (c (pr t)), hS _ (hprI t)⟩ with hlowdef
  have hlowc : Continuous low :=
    (Dat.continuous_sPt.comp (hc.comp (continuous_subtype_val.comp continuous_projIcc))).subtype_mk _
  have hLc : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) (c ∘ pr) :=
    fun t => (hL (pr t)).comp_lipschitz hpr
  have hLl : Causal.Flat.IsLocLip (e0SliceSys S) low := fun t =>
    (locLipAt_chartSys_iff_e0SliceSys (c := low) (c' := c ∘ pr)
      (Eventually.of_forall fun s => rfl)).1 (hLc t)
  have hlen : Causal.Flat.localLength (e0SliceSys S) low a b =
      Causal.Flat.localLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c a b := by
    rw [← localLength_chartSys_eq_e0SliceSys (c := low) (c' := c ∘ pr) (fun s _ => rfl)]
    refine Causal.Flat.localLength_congr _ fun s hs => ?_
    show c (pr s) = c s
    rw [show pr s = s by simp only [hprdef, projIcc_of_mem hab ⟨hs.1.le, hs.2.le⟩]]
  have hpra : pr a = a := by simp [hprdef]
  have hprb : pr b = b := by simp [hprdef]
  have hlowa : low a = Causal.Flat.LocalLengthSpace.toSpace p := Subtype.ext (by
    show Dat.sPt (c (pr a)) = _; rw [hpra, hp])
  have hlowb : low b = Causal.Flat.LocalLengthSpace.toSpace q := Subtype.ext (by
    show Dat.sPt (c (pr b)) = _; rw [hprb, hq])
  let β : Path (Causal.Flat.LocalLengthSpace.toSpace p) (Causal.Flat.LocalLengthSpace.toSpace q) :=
    { toFun := fun s => low (a + (s : ℝ) * (b - a))
      continuous_toFun := hlowc.comp (continuous_const.add
        (continuous_subtype_val.mul continuous_const))
      source' := by
        show low (a + ((0 : I) : ℝ) * (b - a)) = _
        rw [Set.Icc.coe_zero, zero_mul, add_zero]; exact hlowa
      target' := by
        show low (a + ((1 : I) : ℝ) * (b - a)) = _
        rw [Set.Icc.coe_one, one_mul, add_sub_cancel]; exact hlowb }
  have hext : ⇑β.extend = fun s => low ((b - a) * s + a) := by
    funext s
    show low (a + (projIcc 0 1 zero_le_one s : ℝ) * (b - a)) = low ((b - a) * s + a)
    have key : pr (a + (projIcc 0 1 zero_le_one s : ℝ) * (b - a)) = pr ((b - a) * s + a) := by
      have hba : 0 < b - a := sub_pos.2 hab'
      simp only [hprdef, coe_projIcc]
      rcases le_total s 0 with h | h
      · have h1 : max 0 (min 1 s) = 0 := by rw [min_eq_right (h.trans zero_le_one), max_eq_left h]
        have h2 : (b - a) * s + a ≤ a := by nlinarith
        rw [h1, zero_mul, add_zero, min_eq_right hab, max_self, min_eq_right (h2.trans hab),
          max_eq_left h2]
      · rcases le_total 1 s with h' | h'
        · have h1 : max 0 (min 1 s) = 1 := by rw [min_eq_left h', max_eq_right zero_le_one]
          have h2 : b ≤ (b - a) * s + a := by nlinarith
          rw [h1, one_mul, add_sub_cancel, min_self, max_eq_right hab, min_eq_left h2,
            max_eq_right hab]
        · have h1 : max 0 (min 1 s) = s := by rw [min_eq_right h', max_eq_right h]
          rw [h1, show a + s * (b - a) = (b - a) * s + a by ring]
    simp only [hlowdef, key]
  have hLβ : Causal.Flat.IsLocLip (e0SliceSys S) β.extend := by
    rw [hext]; exact fun t => (hLl ((b - a) * t + a)).comp_affine (sub_pos.2 hab')
  calc edist p q ≤ Causal.Flat.pathLength (e0SliceSys S) β := by
        rw [Causal.Flat.LocalLengthSpace.edist_def]; exact iInf_le _ β
    _ = Causal.Flat.localLength (e0SliceSys S) low a b := by
        rw [Causal.Flat.pathLength_of_isLocLip _ hLβ, hext,
          Causal.Flat.localLength_comp_affine _ _ (sub_pos.2 hab')]
        simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    _ = _ := hlen

/-! ### The surgery of a curve of `Σ*` into a curve of `S` -/

/-- **The surgery estimate** (the argument of B21 l.1093 for infinitely many spears, spear by spear
in order of first entry): for a curve `c` of `Σ*` Lipschitz in charts whose ends at `a ≤ b` are off
every core, and a finite set `F` of spears containing every spear whose core `c` meets on
`[a, b]`, the `S`-distance between the ends is at most the `Σ*`-length of `c` over `[a, b]` plus
`π Σ_{i ∈ F} Rᵢ`. From the first entry into a spear `j` of `F` to the last exit from it, `c` is
replaced by a rim arc of `j` (`edist_rimPt_le`, `≤ π R_j`); before, `c` lies on `S`
(`edist_le_localLength_of_mem`); after, it meets only the cores of `F ∖ {j}` (induction). -/
theorem edist_le_localLength_add {c : ℝ → Dat.sigmaStarReg} (hc : Continuous c)
    (hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c) (b : ℝ)
    (F : Finset Dat.ι) : ∀ a, a ≤ b → (∀ i, Dat.sPt (c a) ∉ Dat.core i) →
      (∀ i, Dat.sPt (c b) ∉ Dat.core i) →
      (∀ t ∈ Icc a b, ∀ i, Dat.sPt (c t) ∈ Dat.core i → i ∈ F) →
      ∀ p q : Causal.Flat.LocalLengthSpace (e0SliceSys S),
      ((Causal.Flat.LocalLengthSpace.toSpace p : S) : M) = Dat.sPt (c a) →
      ((Causal.Flat.LocalLengthSpace.toSpace q : S) : M) = Dat.sPt (c b) →
      edist p q ≤ Causal.Flat.localLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c a b +
        ∑ i ∈ F, ENNReal.ofReal (π * (Dat.D i).R) := by
  classical
  set f : ℝ → M := fun t => Dat.sPt (c t) with hfdef
  have hf : Continuous f := Dat.continuous_sPt.comp hc
  have hfS : ∀ t, f t ∈ Dat.sigmaStar := fun t => (c t).2
  set L := Causal.Flat.localLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) c with hLdef
  induction F using Finset.strongInduction with
  | H F ih =>
  intro a hab hga hgb hF p q hp hq
  by_cases hE : ∃ t ∈ Icc a b, ∃ i ∈ F, f t ∈ (Dat.D i).spearSet
  swap
  · push Not at hE
    refine (Dat.edist_le_localLength_of_mem hc hL hab (fun t ht =>
      Dat.mem_of_forall_notMem_core (hfS t) fun i hi =>
        hE t ht i (hF t ht i hi) (Dat.core_subset_spearSet i hi)) p q hp hq).trans le_self_add
  obtain ⟨t₀, ht₀, i₀, hi₀, h₀⟩ := hE
  -- the first entry into a spear of `F`
  set E : Set ℝ := Icc a b ∩ f ⁻¹' (⋃ i ∈ F, (Dat.D i).spearSet) with hEdef
  have hEc : IsClosed E :=
    isClosed_Icc.inter ((isClosed_biUnion_finset fun i _ => Dat.isClosed i).preimage hf)
  have hEb : BddBelow E := ⟨a, fun t ht => ht.1.1⟩
  have hEne : E.Nonempty := ⟨t₀, ht₀, mem_iUnion₂.2 ⟨i₀, hi₀, h₀⟩⟩
  set t₁ := sInf E with ht₁def
  have ht₁E : t₁ ∈ E := hEc.csInf_mem hEne hEb
  obtain ⟨j, hjF, hj⟩ := mem_iUnion₂.1 ht₁E.2
  -- the last exit from the spear `j`
  set E' : Set ℝ := Icc a b ∩ f ⁻¹' (Dat.D j).spearSet with hE'def
  have hE'c : IsClosed E' := isClosed_Icc.inter ((Dat.isClosed j).preimage hf)
  have hE'b : BddAbove E' := ⟨b, fun t ht => ht.1.2⟩
  have ht₁E' : t₁ ∈ E' := ⟨ht₁E.1, hj⟩
  set t₂ := sSup E' with ht₂def
  have ht₂E' : t₂ ∈ E' := hE'c.csSup_mem ⟨t₁, ht₁E'⟩ hE'b
  have h12 : t₁ ≤ t₂ := le_csSup hE'b ht₁E'
  -- both are off every core
  have hg₁ : ∀ i, f t₁ ∉ Dat.core i := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      rcases ht₁E.1.1.eq_or_lt with h | h
      · exact hga i (by rw [h]; exact hi)
      · have hev := hf.continuousAt.preimage_mem_nhds (Dat.spearSet_mem_nhds_of_core hi)
        obtain ⟨s, has, hst, hs⟩ := exists_lt_of_eventually' h hev
        have hsE : s ∈ E := ⟨⟨has, by linarith [ht₁E.1.2]⟩, mem_iUnion₂.2 ⟨i, hjF, hs⟩⟩
        exact absurd (csInf_le hEb hsE) (not_le.2 hst)
    · exact Set.disjoint_left.1 (Dat.disjoint hij) (Dat.core_subset_spearSet i hi) hj
  have hg₂ : ∀ i, f t₂ ∉ Dat.core i := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      rcases ht₂E'.1.2.eq_or_lt with h | h
      · exact hgb i (by rw [← h]; exact hi)
      · have hev := hf.continuousAt.preimage_mem_nhds (Dat.spearSet_mem_nhds_of_core hi)
        obtain ⟨s, hts, hsb, hs⟩ := exists_gt_of_eventually' h hev
        have hsE : s ∈ E' := ⟨⟨by linarith [ht₂E'.1.1], hsb⟩, hs⟩
        exact absurd (le_csSup hE'b hsE) (not_le.2 hts)
    · exact Set.disjoint_left.1 (Dat.disjoint hij) (Dat.core_subset_spearSet i hi) ht₂E'.2
  -- before the first entry, `c` lies on `S`
  have hS₁ : ∀ t ∈ Icc a t₁, f t ∈ S := by
    intro t ht
    rcases ht.2.eq_or_lt with h | h
    · rw [h]; exact Dat.mem_of_forall_notMem_core (hfS _) hg₁
    · refine Dat.mem_of_forall_notMem_core (hfS t) fun i hi => ?_
      have htI : t ∈ Icc a b := ⟨ht.1, by linarith [ht₁E.1.2]⟩
      have htE : t ∈ E :=
        ⟨htI, mem_iUnion₂.2 ⟨i, hF t htI i hi, Dat.core_subset_spearSet i hi⟩⟩
      exact absurd (csInf_le hEb htE) (not_le.2 h)
  have hS₁' : f t₁ ∈ S := hS₁ t₁ ⟨ht₁E.1.1, le_rfl⟩
  have hS₂' : f t₂ ∈ S := Dat.mem_of_forall_notMem_core (hfS _) hg₂
  set y₁ : Causal.Flat.LocalLengthSpace (e0SliceSys S) :=
    Causal.Flat.LocalLengthSpace.toSpace.symm ⟨f t₁, hS₁'⟩ with hy₁
  set y₂ : Causal.Flat.LocalLengthSpace (e0SliceSys S) :=
    Causal.Flat.LocalLengthSpace.toSpace.symm ⟨f t₂, hS₂'⟩ with hy₂
  have h1 : edist p y₁ ≤ L a t₁ :=
    Dat.edist_le_localLength_of_mem hc hL ht₁E.1.1 hS₁ p y₁ hp rfl
  -- from the first entry to the last exit: a rim arc
  have h2 : edist y₁ y₂ ≤ ENNReal.ofReal (π * (Dat.D j).R) := by
    have hc₁ : f t₁ ∈ (Dat.D j).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet j]; exact ⟨hfS _, hj⟩
    have hc₂ : f t₂ ∈ (Dat.D j).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet j]; exact ⟨hfS _, ht₂E'.2⟩
    obtain ⟨φ₁, hφ₁⟩ := Dat.exists_rimPt_of_notMem_core hc₁ (hg₁ j)
    obtain ⟨φ₂, hφ₂⟩ := Dat.exists_rimPt_of_notMem_core hc₂ (hg₂ j)
    have e1 : (⟨f t₁, hS₁'⟩ : S) = (Dat.D j).rimS φ₁ := Subtype.ext hφ₁
    have e2 : (⟨f t₂, hS₂'⟩ : S) = (Dat.D j).rimS φ₂ := Subtype.ext hφ₂
    rw [hy₁, hy₂, e1, e2]
    exact (Dat.D j).edist_rimPt_le φ₁ φ₂
  -- after the last exit: the cores of `F ∖ {j}` only
  have h3 : edist y₂ q ≤ L t₂ b + ∑ i ∈ F.erase j, ENNReal.ofReal (π * (Dat.D i).R) := by
    refine ih (F.erase j) (Finset.erase_ssubset hjF) t₂ ht₂E'.1.2 hg₂ hgb (fun t ht i hi => ?_)
      y₂ q rfl hq
    have htI : t ∈ Icc a b := ⟨ht₂E'.1.1.trans ht.1, ht.2⟩
    refine Finset.mem_erase.2 ⟨fun hij => ?_, hF t htI i hi⟩
    subst hij
    have htE : t ∈ E' := ⟨htI, Dat.core_subset_spearSet i hi⟩
    have htt : t = t₂ := le_antisymm (le_csSup hE'b htE) ht.1
    exact hg₂ i (by rw [← htt]; exact hi)
  have hlen : L a b = L a t₁ + L t₁ t₂ + L t₂ b := by
    rw [hLdef, Causal.Flat.localLength_add _ _ ht₁E.1.1 (h12.trans ht₂E'.1.2),
      Causal.Flat.localLength_add _ _ h12 ht₂E'.1.2, add_assoc]
  have hsum : ∑ i ∈ F, ENNReal.ofReal (π * (Dat.D i).R) = ENNReal.ofReal (π * (Dat.D j).R) +
      ∑ i ∈ F.erase j, ENNReal.ofReal (π * (Dat.D i).R) :=
    (Finset.add_sum_erase F _ hjF).symm
  calc edist p q ≤ edist p y₁ + edist y₁ y₂ + edist y₂ q := edist_triangle4 _ _ _ _
    _ ≤ L a t₁ + ENNReal.ofReal (π * (Dat.D j).R) +
        (L t₂ b + ∑ i ∈ F.erase j, ENNReal.ofReal (π * (Dat.D i).R)) :=
        add_le_add (add_le_add h1 h2) h3
    _ = (L a t₁ + L t₂ b) + (ENNReal.ofReal (π * (Dat.D j).R) +
        ∑ i ∈ F.erase j, ENNReal.ofReal (π * (Dat.D i).R)) := by ring
    _ ≤ L a b + ∑ i ∈ F, ENNReal.ofReal (π * (Dat.D i).R) := by
        rw [hlen, hsum]
        gcongr
        exact le_self_add

/-- **A path of `Σ*` leaving the spear `j` passes through a point off every core** (its last
point in the closed spear: a core point has the spear as a neighbourhood). -/
theorem exists_notMem_core_of_exit {x y : Dat.sigmaStarReg} (γ : Path x y) {j : Dat.ι}
    (hx : Dat.sPt x ∈ (Dat.D j).spearSet) (hy : Dat.sPt y ∉ (Dat.D j).spearSet) :
    ∃ t : I, ∀ i, Dat.sPt (γ t) ∉ Dat.core i := by
  set f : ℝ → M := fun t => Dat.sPt (γ.extend t) with hfdef
  have hf : Continuous f := Dat.continuous_sPt.comp γ.continuous_extend
  set E : Set ℝ := Icc 0 1 ∩ f ⁻¹' (Dat.D j).spearSet with hE
  have hEc : IsClosed E := isClosed_Icc.inter ((Dat.isClosed j).preimage hf)
  have hEb : BddAbove E := ⟨1, fun t ht => ht.1.2⟩
  have h0 : (0 : ℝ) ∈ E := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    simp only [hfdef, mem_preimage, Path.extend_zero]; exact hx
  set t₂ := sSup E with ht₂def
  have ht₂ : t₂ ∈ E := hEc.csSup_mem ⟨0, h0⟩ hEb
  have ht₂1 : t₂ < 1 := by
    refine lt_of_le_of_ne ht₂.1.2 fun h => hy ?_
    have := ht₂.2
    rw [h] at this
    simpa [hfdef] using this
  refine ⟨⟨t₂, ht₂.1⟩, fun i hi => ?_⟩
  have hi' : f t₂ ∈ Dat.core i := by
    simp only [hfdef, Path.extend_apply γ ht₂.1]; exact hi
  by_cases hij : i = j
  · subst hij
    have hev := hf.continuousAt.preimage_mem_nhds (Dat.spearSet_mem_nhds_of_core hi')
    obtain ⟨s, hts, hs1, hs⟩ := exists_gt_of_eventually' ht₂1 hev
    have hsE : s ∈ E := ⟨⟨by linarith [ht₂.1.1], hs1⟩, hs⟩
    exact absurd (le_csSup hEb hsE) (not_le.2 hts)
  · exact Set.disjoint_left.1 (Dat.disjoint hij) (Dat.core_subset_spearSet i hi') ht₂.2

/-- A path of `Σ*` meets finitely many cores (its range is compact; local finiteness). -/
theorem finite_core_of_path {x y : Dat.sigmaStarReg} (γ : Path x y) :
    {i | ∃ t : I, Dat.sPt (γ t) ∈ Dat.core i}.Finite := by
  refine (Dat.finite_spears_of_isCompact (isCompact_range
    (Dat.continuous_sPt.comp γ.continuous))).subset fun i ⟨t, ht⟩ => ?_
  exact ⟨_, Dat.core_subset_spearSet i ht, t, rfl⟩

/-- **The surgery estimate for a path** of finite `Σ*`-length with ends off every core. -/
theorem edist_le_pathLength_add {x y : Dat.sigmaStarReg} (γ : Path x y)
    (hγ : Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ ≠ ⊤)
    (hgx : ∀ i, Dat.sPt x ∉ Dat.core i) (hgy : ∀ i, Dat.sPt y ∉ Dat.core i)
    (F : Finset Dat.ι) (hF : ∀ t : I, ∀ i, Dat.sPt (γ t) ∈ Dat.core i → i ∈ F)
    (p q : Causal.Flat.LocalLengthSpace (e0SliceSys S))
    (hp : ((Causal.Flat.LocalLengthSpace.toSpace p : S) : M) = Dat.sPt x)
    (hq : ((Causal.Flat.LocalLengthSpace.toSpace q : S) : M) = Dat.sPt y) :
    edist p q ≤ Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ +
      ∑ i ∈ F, ENNReal.ofReal (π * (Dat.D i).R) := by
  have hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend := by
    by_contra h; exact hγ (Causal.Flat.pathLength_of_not_isLocLip _ h)
  rw [Causal.Flat.pathLength_of_isLocLip _ hL]
  refine Dat.edist_le_localLength_add γ.continuous_extend hL 1 F 0 zero_le_one
    (by simpa using hgx) (by simpa using hgy) (fun t ht i hi => hF ⟨t, ht⟩ i ?_) p q
    (by simpa using hp) (by simpa using hq)
  rwa [Path.extend_apply γ ht] at hi

/-! ### A Cauchy sequence of `Σ*` converges -/

/-- A distance `< r` of `Σ*` is witnessed by a path of length `< r`. -/
theorem exists_path_lt {a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg} {r : ℝ≥0∞}
    (h : edist a b < r) :
    ∃ γ : Path (Causal.Flat.InducedLengthSpace.toSubtype a)
      (Causal.Flat.InducedLengthSpace.toSubtype b),
      Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ < r :=
  iInf_lt_iff.1 h

/-- A path of `Σ*` is at least as long as the distance from its start to any of its points. -/
theorem edist_le_of_path {a : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg}
    {y : Dat.sigmaStarReg} (γ : Path (Causal.Flat.InducedLengthSpace.toSubtype a) y) (t : I) :
    edist a (Causal.Flat.InducedLengthSpace.toSubtype.symm (γ t)) ≤
      Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ :=
  Causal.Flat.LocalLengthSpace.edist_le_pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ t

/-- **A Cauchy sequence of `Σ*` converges** when the spear radii are summable, from three facts
proved in `GX.BTZ.RegCompleteLength` and taken here as hypotheses so that the file does not
import it: (`htend`) a Cauchy sequence whose tail lies in a compact set of `M` converges
(`LFSurgeryData.tendsto_of_cauchySeq_of_isCompact`), and (`hlog`) Lemma 2.8's `log r` estimate on
`Σ*`, spear by spear (`LFSurgeryData.ofReal_abs_logRad_sub_le_edist`); and of `S` only that its
length space is complete and finer than `M` (the fields `complete`, `continuous` of the reading
`IsE0C1CompleteCauchy`).

(a) If the sequence comes arbitrarily close, arbitrarily late, to one spear `j`, the `log r`
estimate keeps those close points in a compact annulus graph of the cusp `j`: a sequence close to a
subsequence lies in a compact set, so it converges (`htend`), and so does the sequence. (b)
Otherwise each spear is eventually kept at a positive distance; the sequence is pushed off the
cores (`exists_notMem_core_of_exit`) to a sequence `w` of `S ∩ Σ*` at distance tending to `0`, and
the surgery estimate (`edist_le_pathLength_add`) along short paths of `Σ*` between late terms of
`w`, which meet only the cores of spears outside any prescribed finite set, makes `w` Cauchy in
`S` (`hsum`): it converges in `S`, hence in `M`, hence lies in a compact set of `M`, and the
sequence converges (`htend`). -/
theorem exists_tendsto_of_cauchySeq_of
    (hcomp : CompleteSpace (Causal.Flat.LocalLengthSpace (e0SliceSys S)))
    (hcontS : Continuous fun x : Causal.Flat.LocalLengthSpace (e0SliceSys S) =>
      ((Causal.Flat.LocalLengthSpace.toSpace x : S) : M))
    (htend : ∀ {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg}, CauchySeq u →
      ∀ {K : Set M}, IsCompact K →
      (∀ᶠ n in atTop, Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u n)) ∈ K) →
      ∃ a, Tendsto u atTop (𝓝 a))
    (hlog : ∀ i, ∃ f : M → ℝ, (∀ z ∈ (Dat.D i).spearSet,
        f z = Real.log (min (rad ((Dat.D i).coord z)) ((Dat.D i).R / 2))) ∧
      ∀ a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg,
        ENNReal.ofReal |f (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype b)) -
          f (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype a))| ≤ edist a b)
    (hsum : Summable fun i => (Dat.D i).R)
    {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg} (hu : CauchySeq u) :
    ∃ a, Tendsto u atTop (𝓝 a) := by
  classical
  by_cases hA : ∃ j, ∀ δ > (0 : ℝ≥0∞), ∀ N, ∃ n ≥ N,
      ∃ x : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg,
      Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype x) ∈ (Dat.D j).spearSet ∧ edist x (u n) < δ
  · -- (a) arbitrarily close, arbitrarily late, to the spear `j`
    obtain ⟨j, hj⟩ := hA
    choose n hn x hx hxd using fun k : ℕ =>
      hj ((k : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)) k
    have hnt : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
    have hd : Tendsto (fun k => edist (x k) (u (n k))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ENNReal.tendsto_inv_nat_nhds_zero (fun _ => bot_le) fun k => (hxd k).le
    obtain ⟨g, hg, hgL⟩ := hlog j
    obtain ⟨N, hN⟩ := (EMetric.cauchySeq_iff'.1 hu) 1 one_pos
    set D := Dat.D j with hD
    set ρ := Real.exp (g (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u N))) - 2) with hρ
    have hρ0 : 0 < ρ := Real.exp_pos _
    set Kg : Set E0 := (fun q : ℝ × ℝ => ((D.G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc ρ D.R ×ˢ Icc (-π) π) with hKg
    have hψc : ContinuousOn (fun x : E0 => D.ψ (paperInY x)) (E0Spear.spear D.v D.R) := by
      intro x hx
      have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hx, rfl⟩
      exact ((D.mor _ hxW).1.continuousAt (D.isOpen.mem_nhds hxW)).comp
        E0Spear.continuous_paperInY.continuousAt |>.continuousWithinAt
    have hK : IsCompact (D.ψ '' (paperInY '' Kg)) := by
      rw [image_image]
      exact (D.isCompact_annulusGraph hρ0).image_of_continuousOn
        (hψc.mono ((D.annulusGraph_subset hρ0).trans D.graphSet_subset_spear))
    have hev : ∀ᶠ k in atTop,
        Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (x k)) ∈ D.ψ '' (paperInY '' Kg) := by
      filter_upwards [eventually_ge_atTop (max N 1)] with k hk
      have hk1 : 1 ≤ k := le_of_max_le_right hk
      have hkN : N ≤ n k := (le_of_max_le_left hk).trans (hn k)
      have hd1 : edist (x k) (u (n k)) < 1 := (hxd k).trans_le (by
        rw [ENNReal.inv_le_one]; exact_mod_cast hk1)
      have e1 := (hgL (u (n k)) (x k)).trans_lt (by rw [edist_comm]; exact hd1)
      have e2 := (hgL (u N) (u (n k))).trans_lt (by rw [edist_comm]; exact hN (n k) hkN)
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at e1 e2
      have a1 := abs_lt.1 e1
      have a2 := abs_lt.1 e2
      set z := Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (x k)) with hz
      have hzsp : z ∈ D.spearSet := hx k
      have hzc : z ∈ D.cusp := by
        rw [hD, ← Dat.sigmaStar_inter_spearSet j]; exact ⟨Dat.sPt_mem _, hzsp⟩
      obtain ⟨y', ⟨w, hw, hwy⟩, hwz⟩ := hzc
      have hzw : z = D.ψ (paperInY w) := by rw [← hwz, ← hwy]
      have hcw : D.coord z = w := by rw [hzw]; exact D.coord_apply (D.graphSet_subset_spear hw)
      have hgz := hg z hzsp
      rw [hcw] at hgz
      have hmin0 : 0 < min (rad w) (D.R / 2) := lt_min hw.1 (by linarith [D.pos])
      have hlt : g (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u N))) - 2 <
          Real.log (min (rad w) (D.R / 2)) := by
        rw [← hgz]; linarith
      have hρw : ρ ≤ rad w :=
        (((Real.lt_log_iff_exp_lt hmin0).1 hlt).trans_le (min_le_left _ _)).le
      exact ⟨paperInY w, ⟨w, D.mem_annulusGraph hw hρw, rfl⟩, hzw.symm⟩
    obtain ⟨a, ha⟩ := htend (cauchySeq_of_edist_tendsto_zero (hu.comp_tendsto hnt) hd) hK hev
    exact ⟨a, tendsto_of_edist_subseq hu hnt hd ha⟩
  -- (b) every spear eventually kept at a positive distance
  push Not at hA
  choose δ hδ N hN using hA
  have hout : ∀ j n, N j ≤ n →
      Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u n)) ∉ (Dat.D j).spearSet :=
    fun j n hn h => absurd (hN j n hn (u n) h) (by rw [edist_self]; exact not_le.2 (hδ j))
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff.1 hu 1 one_pos
  -- pushed off the cores
  have hw : ∀ n, ∃ z : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg,
      (∀ i, Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype z) ∉ Dat.core i) ∧
      ∃ m ≥ max n N₀, edist z (u (max n N₀)) <
        edist (u (max n N₀)) (u m) + ((max n N₀ : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    set n' := max n N₀ with hn'
    have hpos : ((n' : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
    by_cases hg : ∀ i, Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u n')) ∉ Dat.core i
    · exact ⟨u n', hg, n', le_rfl, by
        simp only [edist_self, zero_add]; exact pos_iff_ne_zero.2 hpos⟩
    · push Not at hg
      obtain ⟨j, hj⟩ := hg
      set m := max n' (N j) with hm
      have hm1 : edist (u n') (u m) < 1 :=
        hN₀ n' (le_max_right _ _) m ((le_max_right _ _).trans (le_max_left _ _))
      have hlt : edist (u n') (u m) < edist (u n') (u m) + ((n' : ℕ) : ℝ≥0∞)⁻¹ :=
        ENNReal.lt_add_right (ne_top_of_lt hm1) hpos
      obtain ⟨γ, hγ⟩ := Dat.exists_path_lt hlt
      obtain ⟨t, ht⟩ := Dat.exists_notMem_core_of_exit γ (Dat.core_subset_spearSet j hj)
        (hout j m (le_max_right _ _))
      refine ⟨Causal.Flat.InducedLengthSpace.toSubtype.symm (γ t), by simpa using ht, m,
        le_max_left _ _, ?_⟩
      rw [edist_comm]; exact (Dat.edist_le_of_path γ t).trans_lt hγ
  choose w hwg m hm hwd using hw
  have hwu : Tendsto (fun n => edist (w n) (u n)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨N₁, hN₁⟩ := EMetric.cauchySeq_iff.1 hu (ε / 2) h2
    filter_upwards [eventually_ge_atTop (max N₀ N₁),
      ENNReal.tendsto_inv_nat_nhds_zero.eventually (gt_mem_nhds h2)] with n hn hn'
    have hmax : max n N₀ = n := max_eq_left (le_of_max_le_left hn)
    have h1 := hwd n
    have hmn : n ≤ m n := (le_max_left n N₀).trans (hm n)
    rw [hmax] at h1
    refine (h1.trans (ENNReal.add_lt_add (hN₁ n (le_of_max_le_right hn) (m n)
      ((le_of_max_le_right hn).trans hmn)) hn')).le.trans (ENNReal.add_halves ε).le
  have hwC : CauchySeq w := cauchySeq_of_edist_tendsto_zero hu hwu
  -- `w` is Cauchy in `S`
  set yS : ℕ → Causal.Flat.LocalLengthSpace (e0SliceSys S) := fun n =>
    Causal.Flat.LocalLengthSpace.toSpace.symm
      ⟨Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (w n)),
        Dat.mem_of_forall_notMem_core (Dat.sPt_mem _) (hwg n)⟩ with hyS
  have hyC : CauchySeq yS := by
    rw [EMetric.cauchySeq_iff']
    intro ε hε
    have h2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨r', hr'0, hr'pos, hr'⟩ := ENNReal.lt_iff_exists_real_btwn.1 h2
    have hr'p : 0 < r' := ENNReal.ofReal_pos.1 hr'pos
    set r := r' / π with hr
    have hr0 : 0 < r := div_pos hr'p Real.pi_pos
    have hπr : π * r = r' := by rw [hr]; field_simp
    obtain ⟨G, hG⟩ := summable_iff_vanishing_norm.1 hsum r hr0
    set δ₀ := G.inf δ with hδ₀def
    have hδ₀ : 0 < δ₀ := (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun j _ => hδ j
    have h3 : (0 : ℝ≥0∞) < δ₀ / 3 := ENNReal.div_pos hδ₀.ne' ENNReal.ofNat_ne_top
    set θ := min (δ₀ / 3) (ε / 2) with hθdef
    have hθ : 0 < θ := lt_min h3 h2
    obtain ⟨N₁, hN₁⟩ := EMetric.cauchySeq_iff.1 hwC θ hθ
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hwu.eventually (gt_mem_nhds h3))
    set Nb := max (max N₁ N₂) (G.sup N) with hNb
    have hNb1 : N₁ ≤ Nb := (le_max_left _ _).trans (le_max_left _ _)
    have hNb2 : N₂ ≤ Nb := (le_max_right _ _).trans (le_max_left _ _)
    refine ⟨Nb, fun n hn => ?_⟩
    have hwd' : edist (w Nb) (w n) < θ := hN₁ Nb hNb1 n (hNb1.trans hn)
    obtain ⟨γ, hγ⟩ := Dat.exists_path_lt hwd'
    set F := (Dat.finite_core_of_path γ).toFinset with hF
    have hFG : Disjoint F G := by
      rw [Finset.disjoint_left]
      intro i hiF hiG
      obtain ⟨t, ht⟩ := (Set.Finite.mem_toFinset _).1 hiF
      set x : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg :=
        Causal.Flat.InducedLengthSpace.toSubtype.symm (γ t) with hxdef
      have hx1 : edist (w Nb) x < δ₀ / 3 :=
        (Dat.edist_le_of_path γ t).trans_lt (hγ.trans_le (min_le_left _ _))
      have hx2 : edist (w Nb) (u Nb) < δ₀ / 3 := hN₂ Nb hNb2
      have hx3 : edist x (u Nb) < δ i :=
        calc edist x (u Nb) ≤ edist x (w Nb) + edist (w Nb) (u Nb) := edist_triangle _ _ _
          _ < δ₀ / 3 + δ₀ / 3 := ENNReal.add_lt_add (by rw [edist_comm]; exact hx1) hx2
          _ ≤ δ₀ / 3 + δ₀ / 3 + δ₀ / 3 := le_self_add
          _ = δ₀ := ENNReal.add_thirds _
          _ ≤ δ i := Finset.inf_le hiG
      have hxs : Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype x) ∈ (Dat.D i).spearSet := by
        rw [hxdef, Equiv.apply_symm_apply]; exact Dat.core_subset_spearSet i ht
      exact absurd (hN i Nb ((Finset.le_sup hiG).trans (le_max_right _ _)) x hxs) (not_le.2 hx3)
    have hX := Dat.edist_le_pathLength_add γ (ne_top_of_lt hγ) (hwg Nb) (hwg n) F
      (fun t i hi => (Set.Finite.mem_toFinset _).2 ⟨t, hi⟩) (yS Nb) (yS n) rfl rfl
    have hFs : ∑ i ∈ F, ENNReal.ofReal (π * (Dat.D i).R) < ε / 2 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg Real.pi_pos.le (Dat.D i).pos.le),
        ← Finset.mul_sum]
      refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hr'
      rw [← hπr]
      refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
      have := hG F hFG
      rw [Real.norm_eq_abs] at this
      exact ((le_abs_self _).trans this.le)
    rw [edist_comm]
    calc edist (yS Nb) (yS n) ≤ _ := hX
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hγ.trans_le (min_le_right _ _)) hFs
      _ = ε := ENNReal.add_halves ε
  haveI := hcomp
  obtain ⟨yl, hyl⟩ := cauchySeq_tendsto_of_complete hyC
  have hM : Tendsto (fun n => Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (w n))) atTop
      (𝓝 ((Causal.Flat.LocalLengthSpace.toSpace yl : S) : M)) := (hcontS.tendsto yl).comp hyl
  obtain ⟨a, ha⟩ := htend hwC hM.isCompact_insert_range
    (Eventually.of_forall fun n => mem_insert_of_mem _ (mem_range_self n))
  exact ⟨a, tendsto_of_edist_subseq hu tendsto_id hwu ha⟩

/-- **The tail of a Cauchy sequence of `Σ*` lies in a compact set of `M`** (it converges,
`exists_tendsto_of_cauchySeq_of`, and `Σ*`'s length topology is finer than `M`'s, `hcontX`). -/
theorem exists_isCompact_of_cauchySeq_of
    (hcomp : CompleteSpace (Causal.Flat.LocalLengthSpace (e0SliceSys S)))
    (hcontS : Continuous fun x : Causal.Flat.LocalLengthSpace (e0SliceSys S) =>
      ((Causal.Flat.LocalLengthSpace.toSpace x : S) : M))
    (htend : ∀ {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg}, CauchySeq u →
      ∀ {K : Set M}, IsCompact K →
      (∀ᶠ n in atTop, Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u n)) ∈ K) →
      ∃ a, Tendsto u atTop (𝓝 a))
    (hcontX : Continuous fun a : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg =>
      Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype a))
    (hlog : ∀ i, ∃ f : M → ℝ, (∀ z ∈ (Dat.D i).spearSet,
        f z = Real.log (min (rad ((Dat.D i).coord z)) ((Dat.D i).R / 2))) ∧
      ∀ a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg,
        ENNReal.ofReal |f (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype b)) -
          f (Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype a))| ≤ edist a b)
    (hsum : Summable fun i => (Dat.D i).R)
    {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg} (hu : CauchySeq u) :
    ∃ K : Set M, IsCompact K ∧
      ∀ᶠ n in atTop, Dat.sPt (Causal.Flat.InducedLengthSpace.toSubtype (u n)) ∈ K := by
  obtain ⟨a, ha⟩ := Dat.exists_tendsto_of_cauchySeq_of hcomp hcontS htend hlog hsum hu
  exact ⟨_, ((hcontX.tendsto a).comp ha).isCompact_insert_range,
    Eventually.of_forall fun n => mem_insert_of_mem _ (mem_range_self n)⟩

end E0SpearFamily.LFSurgeryData

end GX
