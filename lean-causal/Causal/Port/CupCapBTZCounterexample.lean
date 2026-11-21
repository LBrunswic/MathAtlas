import Causal.Port.SFALine
import Causal.Port.E0Strong
import Causal.Port.ModelRowsE0
import Causal.SingularGeroch

/-!
# `lem:cup_cap_BTZ` as printed is false: `E₀` minus a point of its BTZ line

Target `T-ett-cupcap-btz-cex`. Cited, **unmarked** (a refutation of the printed, strongly causal
form, the finding behind DEC-19; the lemma's certificate is unchanged):
`lem:cup_cap_BTZ` — `ETT.tex:1825`.

> Let $M$ be a strongly causal singular flat spacetime, let $p\in M$ and let $(p_n)_{n\in \N}$
> be a sequence of $M$ converging to $p$. If $p \notin J^-(p_n)$ for every $n\in \N$ and if
> $p\in \sing_0(M)$, then $\bigcup_{N\in \N}\bigcap_{n\geq N} J^-(p_n)=J^-(p)\setminus \{p\}.$
> (`ETT.tex:1826–1829`)

> One proceeds in the same way as in the proof of Lemma \ref{lem:J_int}. (`ETT.tex:1832`)

## What is proved (no `sorry` in this file)

`M = E₀ ∖ {w}`, `w = (0, 0)` on the axis (`puncture`, an open set of `Causal.E0`), with the
structure pulled back along the inclusion (`opensSingularGXStructure`, DEC-25) and its natural
causality `C` (`SFALocalE0.IsE0Natural`, unique; `natCausality`). For every such `C`:

* **`not_cupCapBTZAsPrinted`**: `¬ C.CupCapBTZAsPrinted (SFALocalE0.sing M)`, the strict `Prop`
  of `Causal.SingularGeroch` itself. Packaged: `exists_counterexample` (a type `M`, `C`, `sing`
  with `SingularFlatSpacetime`, `StronglyCausal`, `StronglyCausalOpen`, `IsCausal`,
  `AbsolutelyMinimal`, `sing 0 ≠ ∅` and the printed form false) and
  `not_forall_cupCapBTZAsPrinted`.
* Its hypotheses: `e0Covered` (the inclusion is an `IsAEChart`, `isAEChart_incl`),
  `isoChartsCoverDEC25` (an `E_{≥0}`-manifold), `connectedSpace`, `singularFlatSpacetime` (from
  `SFALine.singularFlatAxioms_e0`), `stronglyCausal` (DEC-7) and `stronglyCausalOpen`,
  `isCausal`.
* The failure (`failure`): `p = (1, 0) ∈ sing₀(M)`, `p_n = (1, 1/(n+1)) → p`, `p ∉ J⁻(p_n)`;
  `z = (-1, 0)` is in `⋃_N ⋂_{n ≥ N} J⁻(p_n)` (`z ≪ p_n`, by a straight segment of developments
  that meets the axis only at `z`) and not in `J⁻(p) ∖ {p}`. Exactly, `J⁻(p) = ]w, p]`
  (`Jminus_p`), and the whole half-line below `w` lies in the left side and not in the right
  (`halfLine_subset_diff`). What fails is the closedness of `J⁺(z)` (`not_isClosed_Jplus_z`, the
  hypothesis of `cup_cap_BTZ_of_isClosed`); so `M` is not globally hyperbolic
  (`not_globallyHyperbolic`).
* **Beyond the target** (general): the inclusion of a non-empty open subset of a singular
  `(G,X)`-manifold is an `IsAEChart` (`isAEChart_subtypeCoe`); an open subset of an `E₀`-manifold
  is one (`e0Covered_opens`); every open `U` of `E₀` with its natural causality has `E₀`'s
  relations in `U` at the top (`relations_top_iff`), is strongly causal in both forms and causal
  (`stronglyCausal_opens`, `stronglyCausalOpen_opens`, `isCausal_opens`), and is a singular flat
  spacetime when connected (`singularFlatSpacetime_opens`).

## Hypothesis checklist (the witness against the printed statement)

| paper hypothesis | here |
|---|---|
| `M` a singular flat spacetime (`def:singular_spacetime`, l.1500–1505) | ✓ the library's class `SingularFlatSpacetime C (SFALocalE0.sing M)`; in the readings DEC-25, OQ-18, OQ-34/OQ-35, OQ-82, `M` is a connected `E₀`-manifold, hence `E_{≥0}`-manifold, with its natural causality |
| strongly causal (l.1826) | ✓ `StronglyCausal` (DEC-7), and the open form `StronglyCausalOpen` |
| `p ∈ sing_0(M)`, `p_n → p`, `p ∉ J⁻(p_n)` (l.1827–1828) | ✓ `p = (1, 0)`, `p_n = (1, 1/(n+1))` |
| conclusion (l.1829) | ✗ fails: the half-line below `w` |

## SCOPE (disclosed)

* **Unmarked.** This module refutes the printed form; under DEC-19 the lemma is stated for
  globally hyperbolic `M`, certificate `cupCapBTZAsPrinted_of_globallyHyperbolic`, unchanged.
* **Readings.** `not_forall_cupCapBTZAsPrinted` refutes the library's `Prop` outright. That the
  witness is a singular flat spacetime of the paper rests on the library's `E₀` (`Causal.E0`,
  OQ-34, OQ-35), DEC-25's structure, OQ-18's causality and OQ-82's group.
* **No gluing loophole** (kb/0014): `C` is the natural causality, absolutely minimal and causal.
* **Where the proof « as for `lem:J_int` » breaks** (l.1832, l.1805–1809): a causally convex
  chart at `p` does not see `z`, which is far from `p`; the step `z ≤ p_n ⇒ z ≤ p` is the
  closedness of `J⁺(z)`, a global property.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace CupCapBTZCounterexample

open Set Filter Topology TopologicalSpace

attribute [local instance] E0GX.singularGX

/-! ### The space: `E₀ ∖ {w}` -/

/-- The removed point `w = (0, 0)`, on the BTZ line. -/
def wpt : E0 := (0, 0)

/-- **The open set `E₀ ∖ {w}`.** -/
def puncture : Opens E0 := ⟨{wpt}ᶜ, isOpen_compl_singleton⟩

theorem mem_puncture {x : E0} : x ∈ puncture ↔ x ≠ wpt := Iff.rfl

/-- The BTZ point `p = (1, 0)`, above `w`. -/
def pE : E0 := (1, 0)

/-- The BTZ point `z = (-1, 0)`, below `w`. -/
def zE : E0 := (-1, 0)

/-- The regular points `p_n = (1, 1/(n+1))`, converging to `p`. -/
noncomputable def uE (n : ℕ) : E0 := (1, ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))

theorem pE_mem : pE ∈ puncture := by
  intro h
  have := congrArg Prod.fst h
  norm_num [pE, wpt] at this

theorem zE_mem : zE ∈ puncture := by
  intro h
  have := congrArg Prod.fst h
  norm_num [zE, wpt] at this

theorem uE_mem (n : ℕ) : uE n ∈ puncture := by
  intro h
  have := congrArg Prod.fst h
  norm_num [uE, wpt] at this

/-- `p` as a point of `E₀ ∖ {w}`. -/
def p : puncture := ⟨pE, pE_mem⟩

/-- `z` as a point of `E₀ ∖ {w}`. -/
def z : puncture := ⟨zE, zE_mem⟩

/-- `p_n` as points of `E₀ ∖ {w}`. -/
noncomputable def u (n : ℕ) : puncture := ⟨uE n, uE_mem n⟩

/-! ### The facts in `E₀`, relative to the open set `E₀ ∖ {w}` -/

theorem pE_mem_axis : pE ∈ E0.axis := rfl

theorem zE_mem_axis : zE ∈ E0.axis := rfl

theorem wpt_mem_axis : wpt ∈ E0.axis := rfl

theorem rad_uE (n : ℕ) : E0.rad (uE n) = 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [E0.rad, uE, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_pos (by positivity)

theorem rad_uE_pos (n : ℕ) : 0 < E0.rad (uE n) := by
  rw [rad_uE]; positivity

theorem rad_uE_le_one (n : ℕ) : E0.rad (uE n) ≤ 1 := by
  rw [rad_uE, div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **A BTZ point `x ≠ w` is chronologically below every regular `y` with `f(y) > τ(x)`, in any
open set containing `E₀ ∖ {w}`**: the straight chronological segment from a development of `x`
to one of `y` meets the axis only at `x` (its radial coordinate is `s · r(y)`), so it avoids `w`
(« a chronal curve from a BTZ point leaves the line at once »). -/
theorem lt_of_mem_axis (W : Opens E0) (hW : ∀ x : E0, x ≠ wpt → x ∈ W) {x y : E0}
    (hx : x ∈ E0.axis) (hxw : x ≠ wpt) (hy : 0 < E0.rad y) (hf : x.1 < E0.fcoord y) :
    E0.causality.lt W x y := by
  obtain ⟨θ₁, θ₂, h₁, h₂, hc⟩ := (E0.lt_axis_iff hx).2 ⟨hy, hf⟩
  refine E0.clt_of_seg h₁ h₂ hc fun s hs => hW _ fun hsw => ?_
  rcases hs.1.eq_or_lt with h0 | hpos
  · rw [← h0, E0.seg_zero, E0.unlift_lift h₁] at hsw
    exact hxw hsw
  · have hadm := E0.adm_seg (E0.adm_lift x θ₁) hc.nullCone hs.1
    have hrad := E0.rad_unlift hadm.nonneg
    rw [E0.seg_snd_fst, hsw, E0.rad_eq_zero.2 wpt_mem_axis] at hrad
    have hx0 : (E0.lift x θ₁).2.1 = 0 := E0.rad_eq_zero.2 hx
    have hy' : (E0.lift y θ₂).2.1 = E0.rad y := rfl
    rw [hx0, hy'] at hrad
    have := mul_pos hpos hy
    linarith

theorem fcoord_uE (n : ℕ) : E0.fcoord (uE n) = 1 - E0.rad (uE n) / 2 := rfl

/-- **`z ≪ p_n`** in any open set containing `E₀ ∖ {w}`. -/
theorem lt_zE_uE (W : Opens E0) (hW : ∀ x : E0, x ≠ wpt → x ∈ W) (n : ℕ) :
    E0.causality.lt W zE (uE n) := by
  refine lt_of_mem_axis W hW zE_mem_axis zE_mem (rad_uE_pos n) ?_
  rw [fcoord_uE]
  have := rad_uE_le_one n
  simp only [zE]
  linarith

/-- **No point `x` with `τ(x) ≤ τ(w) = 0` is causally below `p` in an open set avoiding `w`**:
a causal curve to the BTZ point `p` stays on the axis (`J⁻_W(p) ⊂ axis`, `E0.le_axis_iff'`), and
its time coordinate passes `0` between `τ(x) ≤ 0` and `τ(p) = 1`, so the curve passes through
`w`. -/
theorem not_le_pE_of_fst_nonpos (W : Opens E0) (hW : wpt ∉ W) {x : E0} (hx : x.1 ≤ 0) :
    ¬ E0.causality.le W x pE := by
  intro h
  obtain ⟨a, b, hab, c, hc, hca, hcb⟩ := E0.causality_le.1 h
  have hcont := hc.continuousOn E0.isRelFamily_le
  have hfst : ContinuousOn (fun t => (c t).1) (Icc a b) := continuous_fst.comp_continuousOn hcont
  have h0 : (0 : ℝ) ∈ Icc (c a).1 (c b).1 := by
    rw [hca, hcb]; exact ⟨hx, by norm_num [pE]⟩
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc hab hfst h0
  have htb : t < b := by
    rcases ht.2.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have : (c b).1 = 0 := h' ▸ hct
      rw [hcb] at this
      norm_num [pE] at this
  have hrel := hc.rel_of_lt E0.isRelFamily_le ht.1 htb le_rfl
  have hLe : E0.Le (c t) pE := hcb ▸ hrel.2.2
  have hax : c t ∈ E0.axis := ((E0.le_axis_iff' pE_mem_axis).1 hLe).1
  have hcw : c t = wpt := Prod.ext hct hax
  exact hW (hcw ▸ hc.mem t ht)

/-- **`z ≰ p`** in any open set avoiding `w`. -/
theorem not_le_zE_pE (W : Opens E0) (hW : wpt ∉ W) : ¬ E0.causality.le W zE pE :=
  not_le_pE_of_fst_nonpos W hW (by norm_num [zE])

/-- **The segment `]w, p]` of the axis is causally below `p`** in any open set containing
`E₀ ∖ {w}`: the axis segment from `x` to `p` avoids `w`. -/
theorem le_pE_of_mem_axis (W : Opens E0) (hW : ∀ x : E0, x ≠ wpt → x ∈ W) {x : E0}
    (hx : x ∈ E0.axis) (h0 : 0 < x.1) (h1 : x.1 ≤ 1) : E0.causality.le W x pE := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) (1 - x.1), E0.axisLine x t ∈ W := fun t ht => hW _ fun h => by
    have := congrArg Prod.fst h
    simp only [E0.axisLine, wpt] at this
    linarith [ht.1]
  rcases E0.curveOn_axisLine x W 0 (1 - x.1) with hc | hc
  · refine E0.causality_le.2 ⟨0, 1 - x.1, by linarith, E0.axisLine x, hc, ?_, ?_⟩
    · exact Prod.ext (by simp [E0.axisLine]) hx.symm
    · exact Prod.ext (by simp [E0.axisLine, pE]) rfl
  · exact absurd hmem hc

/-- `p ≰ p_n` in `E₀`, hence in every open set: `J⁺(p) = {f ≥ τ(p)}` and `f(p_n) < 1`. -/
theorem not_le_pE_uE (W : Opens E0) (n : ℕ) : ¬ E0.causality.le W pE (uE n) := by
  intro h
  have h' := (E0.le_axis_iff pE_mem_axis).1 (E0.le_of_le h)
  have hr := rad_uE_pos n
  simp only [E0.fcoord, pE, uE] at h' hr
  linarith

theorem tendsto_uE : Tendsto uE atTop (𝓝 pE) := by
  have h : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Complex.ofReal_zero] at h
  exact tendsto_const_nhds.prodMk_nhds h

/-! ### Open subsets: the inclusion is a chart -/

section OpensChart

variable {M : Type*} [TopologicalSpace M]

/-- The image of the whole of `U` by its inclusion is `U`. -/
theorem chartImage_subtypeCoe_top (U : Opens M) (hU : Nonempty U) :
    chartImage (U.openPartialHomeomorphSubtypeCoe hU) ⊤ = U := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, ⟨mem_univ _, trivial⟩, rfl⟩

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [SingularGXStructure G X M]

/-- **The inclusion of a non-empty open subset `U` of a singular `(G,X)`-manifold is an a.e.
isomorphism chart `U ⇀ M`** for the pulled-back structure (`opensSingularGXStructure`): one
application of `isAEChart_of_isAEMorphism_of_isLocalHomeomorph` to the a.e. morphism
`isAEMorphism_opensSingular_val`, an open embedding. -/
theorem isAEChart_subtypeCoe (U : Opens M) (hU : Nonempty U) :
    IsAEChart G X (U.openPartialHomeomorphSubtypeCoe hU) :=
  isAEChart_of_isAEMorphism_of_isLocalHomeomorph (isAEMorphism_opensSingular_val U)
    U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph rfl

end OpensChart

/-! ### Open subsets of `E₀`-manifolds and of `E₀` -/

section E0Opens

/-- **An open subset of an `E₀`-manifold is an `E₀`-manifold**, for the pulled-back structure:
compose the inclusion with the charts of `M`. -/
theorem e0Covered_opens {M : Type*} [TopologicalSpace M]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) M] (hcov : SFALocalE0.E0Covered M)
    (U : Opens M) : SFALocalE0.E0Covered U := by
  intro x hx
  rw [sing_opensSingular] at hx
  obtain ⟨e, he, hxe⟩ := hcov x hx
  refine ⟨(U.openPartialHomeomorphSubtypeCoe ⟨x⟩).trans e,
    (isAEChart_subtypeCoe U ⟨x⟩).trans he, ?_⟩
  rw [OpenPartialHomeomorph.trans_source]
  exact ⟨mem_univ _, hxe⟩

variable {U : Opens E0} {C : Causality U}

/-- **In an open subset `U` of `E₀` with its natural causality, the relations at the top are
`E₀`'s relations in the open set `U`**: the inclusion is a chart into `E₀`, so a `ChartIso`. -/
theorem relations_top_iff (hC : SFALocalE0.IsE0Natural C) (x y : U) :
    (C.le ⊤ x y ↔ E0.causality.le U x y) ∧ (C.lt ⊤ x y ↔ E0.causality.lt U x y) := by
  have h := hC.2.1 _ (isAEChart_subtypeCoe U ⟨x⟩) ⊤ (fun y _ => mem_univ y) x trivial y trivial
  rwa [chartImage_subtypeCoe_top] at h

theorem le_top_iff_opens (hC : SFALocalE0.IsE0Natural C) (x y : U) :
    C.le ⊤ x y ↔ E0.causality.le U x y :=
  (relations_top_iff hC x y).1

theorem lt_top_iff_opens (hC : SFALocalE0.IsE0Natural C) (x y : U) :
    C.lt ⊤ x y ↔ E0.causality.lt U x y :=
  (relations_top_iff hC x y).2

/-- **Every open subset of `E₀` is strongly causal** (DEC-7) for its natural causality: a
neighbourhood causally convex for `E₀` (`E0.stronglyCausal`) stays so for the smaller relations
of `U`. -/
theorem stronglyCausal_opens (hC : SFALocalE0.IsE0Natural C) : C.StronglyCausal := by
  intro x V hV
  have hV' : Subtype.val '' V ∈ 𝓝 (x : E0) := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq]
    exact image_mem_map hV
  obtain ⟨V0, hV0, hV0V, hconv⟩ := E0.stronglyCausal (x : E0) _ hV'
  refine ⟨Subtype.val ⁻¹' V0, continuous_subtype_val.continuousAt.preimage_mem_nhds hV0, ?_,
    ⟨fun _ _ => trivial, fun a ha b hb m hm => ?_⟩⟩
  · intro y hy
    obtain ⟨y', hy', hyy'⟩ := hV0V hy
    rwa [← Subtype.val_injective hyy']
  · obtain ⟨h1, h2⟩ := hm
    have h1' := (le_top_iff_opens hC _ _).1 (Precausality.mem_Jminus_singleton.1 h1)
    have h2' := (le_top_iff_opens hC _ _).1 (Precausality.mem_Jplus_singleton.1 h2)
    exact hconv.2 _ ha _ hb
      ⟨Precausality.mem_Jminus_singleton.2 (E0.causality.le_mono le_top h1'),
        Precausality.mem_Jplus_singleton.2 (E0.causality.le_mono le_top h2')⟩

/-- **Every open subset of `E₀` is strongly causal with open neighbourhoods** for its natural
causality (`ModelRowsE0.e0_stronglyCausalOpen`). -/
theorem stronglyCausalOpen_opens (hC : SFALocalE0.IsE0Natural C) : C.StronglyCausalOpen := by
  intro x V hV
  have hV' : Subtype.val '' V ∈ 𝓝 (x : E0) := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq]
    exact image_mem_map hV
  obtain ⟨V0, hxV0, hV0V, hconv⟩ := ModelRowsE0.e0_stronglyCausalOpen (x : E0) _ hV'
  refine ⟨⟨Subtype.val ⁻¹' V0, V0.isOpen.preimage continuous_subtype_val⟩, hxV0, ?_,
    ⟨fun _ _ => trivial, fun a ha b hb m hm => ?_⟩⟩
  · intro y hy
    obtain ⟨y', hy', hyy'⟩ := hV0V hy
    rwa [← Subtype.val_injective hyy']
  · obtain ⟨h1, h2⟩ := hm
    have h1' := (le_top_iff_opens hC _ _).1 (Precausality.mem_Jminus_singleton.1 h1)
    have h2' := (le_top_iff_opens hC _ _).1 (Precausality.mem_Jplus_singleton.1 h2)
    exact hconv.2 _ ha _ hb
      ⟨Precausality.mem_Jminus_singleton.2 (E0.causality.le_mono le_top h1'),
        Precausality.mem_Jplus_singleton.2 (E0.causality.le_mono le_top h2')⟩

/-- **Every open subset of `E₀` is causal** for its natural causality (`E0.isCausal`). -/
theorem isCausal_opens (hC : SFALocalE0.IsE0Natural C) : C.IsCausal := by
  intro x y hxy hyx
  have h1 := E0.causality.le_mono le_top ((le_top_iff_opens hC x y).1 hxy)
  have h2 := E0.causality.le_mono le_top ((le_top_iff_opens hC y x).1 hyx)
  exact Subtype.ext (E0.isCausal h1 h2)

/-- **Every connected open subset of `E₀` is a singular flat spacetime** for its natural
causality (`SFALine.singularFlatAxioms_e0`). -/
theorem singularFlatSpacetime_opens (hC : SFALocalE0.IsE0Natural C) (hconn : ConnectedSpace U) :
    C.SingularFlatSpacetime (SFALocalE0.sing U) :=
  { SFALine.singularFlatAxioms_e0 (e0Covered_opens SFALocalE0.nonvacuous.1 U) hC with
    connected := hconn }

end E0Opens

/-! ### `E₀ ∖ {w}` as an `E₀`-manifold -/

/-- **The inclusion `E₀ ∖ {w} → E₀` as a chart.** -/
noncomputable def incl : OpenPartialHomeomorph puncture E0 :=
  puncture.openPartialHomeomorphSubtypeCoe ⟨p⟩

/-- **The inclusion is an a.e. isomorphism chart** for the pulled-back structure
(`opensSingularGXStructure`). -/
theorem isAEChart_incl : IsAEChart (Flat.isom 2) (Minkowski 2) incl :=
  isAEChart_subtypeCoe puncture ⟨p⟩

/-- **`E₀ ∖ {w}` is an `E₀`-manifold.** -/
theorem e0Covered : SFALocalE0.E0Covered puncture :=
  e0Covered_opens SFALocalE0.nonvacuous.1 puncture

/-- `sing₀(E₀ ∖ {w})` is the punctured axis. -/
theorem mem_sing_zero_iff (x : puncture) :
    x ∈ SFALocalE0.sing puncture 0 ↔ (x : E0) ∈ E0.axis := by
  rw [SFALocalE0.sing_zero]
  exact (SFALocalE0.mem_axis_iff isAEChart_incl (mem_univ x)).symm

/-- **`E₀ ∖ {w}` is connected**: `ℝ³` minus a point. -/
theorem connectedSpace : ConnectedSpace puncture := by
  have h : 1 < Module.rank ℝ E0 := by
    rw [rank_prod', Module.rank_self, Complex.rank_real_complex]
    norm_num
  exact isConnected_iff_connectedSpace.1 (isConnected_compl_singleton_of_one_lt_rank h wpt)

/-! ### Its natural causality -/

section Natural

variable {C : Causality puncture}

/-- **The relations of `E₀ ∖ {w}` at the top are those of `E₀` in the open set `E₀ ∖ {w}`.** -/
theorem le_top_iff (hC : SFALocalE0.IsE0Natural C) (x y : puncture) :
    C.le ⊤ x y ↔ E0.causality.le puncture x y :=
  le_top_iff_opens hC x y

theorem lt_top_iff (hC : SFALocalE0.IsE0Natural C) (x y : puncture) :
    C.lt ⊤ x y ↔ E0.causality.lt puncture x y :=
  lt_top_iff_opens hC x y

theorem stronglyCausal (hC : SFALocalE0.IsE0Natural C) : C.StronglyCausal :=
  stronglyCausal_opens hC

theorem stronglyCausalOpen (hC : SFALocalE0.IsE0Natural C) : C.StronglyCausalOpen :=
  stronglyCausalOpen_opens hC

theorem isCausal (hC : SFALocalE0.IsE0Natural C) : C.IsCausal :=
  isCausal_opens hC

/-- **`E₀ ∖ {w}` is an `E_{≥0}`-manifold** (`A = ℝ₊`, the paper's « singular flat spacetime »):
an isomorphic chart at each point over the whole family, the hypothesis of `Causal.SFALocal`. Its
`sing_α` for the family is `SFALocalE0.sing` (`sing_family_eq`). -/
theorem isoChartsCoverDEC25 (hC : SFALocalE0.IsE0Natural C) :
    IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality :=
  SFALocal.isoChartsCoverDEC25_of_e0 e0Covered hC

theorem sing_family_eq : SFALocal.sing puncture = SFALocalE0.sing puncture :=
  SFALocal.sing_eq_of_e0Covered e0Covered

theorem singularFlatSpacetime (hC : SFALocalE0.IsE0Natural C) :
    C.SingularFlatSpacetime (SFALocalE0.sing puncture) :=
  singularFlatSpacetime_opens hC connectedSpace

/-- **The failure, in detail.** `p ∈ sing₀`, `p_n → p`, `p ∉ J⁻(p_n)`, and `z` lies in
`⋃_N ⋂_{n ≥ N} J⁻(p_n)` but not in `J⁻(p) ∖ {p}`. -/
theorem failure (hC : SFALocalE0.IsE0Natural C) :
    p ∈ SFALocalE0.sing puncture 0 ∧ Tendsto u atTop (𝓝 p) ∧ (∀ n, ¬ C.le ⊤ p (u n)) ∧
      z ∈ ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} ∧ z ∉ C.Jminus ⊤ {p} \ {p} := by
  refine ⟨(mem_sing_zero_iff p).2 pE_mem_axis, tendsto_subtype_rng.2 tendsto_uE,
    fun n h => not_le_pE_uE puncture n ((le_top_iff hC _ _).1 h), ?_, fun h => ?_⟩
  · refine mem_iUnion.2 ⟨0, mem_iInter₂.2 fun n _ => Precausality.mem_Jminus_singleton.2 ?_⟩
    exact (le_top_iff hC _ _).2 (E0.causality.le_of_lt (lt_zE_uE puncture (fun _ hx => hx) n))
  · exact not_le_zE_pE puncture (fun hw => mem_puncture.1 hw rfl)
      ((le_top_iff hC _ _).1 (Precausality.mem_Jminus_singleton.1 h.1))

/-- **`J⁻(p) = ]w, p]`** in `E₀ ∖ {w}`: the points of the axis with `0 < τ ≤ 1`. -/
theorem Jminus_p (hC : SFALocalE0.IsE0Natural C) :
    C.Jminus ⊤ {p} = {x : puncture | (x : E0) ∈ E0.axis ∧ 0 < (x : E0).1 ∧ (x : E0).1 ≤ 1} := by
  ext x
  rw [Precausality.mem_Jminus_singleton, le_top_iff hC]
  constructor
  · intro h
    obtain ⟨hax, h1⟩ := (E0.le_axis_iff' pE_mem_axis).1 (E0.le_of_le h)
    exact ⟨hax, lt_of_not_ge fun h0 =>
      not_le_pE_of_fst_nonpos puncture (fun hw => mem_puncture.1 hw rfl) h0 h, h1⟩
  · rintro ⟨hax, h0, h1⟩
    exact le_pE_of_mem_axis puncture (fun _ hy => hy) hax h0 h1

/-- **`⋃_N ⋂_{n ≥ N} J⁻(p_n)` contains every point of the punctured axis with `τ < 1`.** -/
theorem axis_subset_iUnion_iInter (hC : SFALocalE0.IsE0Natural C) {x : puncture}
    (hx : (x : E0) ∈ E0.axis) (h1 : (x : E0).1 < 1) :
    x ∈ ⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n} := by
  have ht : Tendsto (fun n => E0.fcoord (uE n)) atTop (𝓝 1) := by
    have := (E0.continuous_fcoord.tendsto pE).comp tendsto_uE
    have hp : E0.fcoord pE = 1 := by simp [E0.fcoord, E0.rad, pE]
    rwa [hp] at this
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 ht).1 _ h1)
  refine mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => Precausality.mem_Jminus_singleton.2 ?_⟩
  exact (le_top_iff hC _ _).2 (E0.causality.le_of_lt
    (lt_of_mem_axis puncture (fun _ hy => hy) hx (mem_puncture.1 x.2) (rad_uE_pos n) (hN n hn)))

/-- **The whole half-line of the axis below `w` is in the left side and not in the right side**
of `lem:cup_cap_BTZ` at `p` and `(p_n)`: the failure is not at one point. -/
theorem halfLine_subset_diff (hC : SFALocalE0.IsE0Natural C) {x : puncture}
    (hx : (x : E0) ∈ E0.axis) (h0 : (x : E0).1 < 0) :
    x ∈ (⋃ N : ℕ, ⋂ n ≥ N, C.Jminus ⊤ {u n}) \ (C.Jminus ⊤ {p} \ {p}) := by
  refine ⟨axis_subset_iUnion_iInter hC hx (by linarith), fun h => ?_⟩
  rw [Jminus_p hC] at h
  linarith [h.1.2.1]

/-- **`lem:cup_cap_BTZ` as printed fails at `E₀ ∖ {w}`** with its natural causality. -/
theorem not_cupCapBTZAsPrinted (hC : SFALocalE0.IsE0Natural C) :
    ¬ C.CupCapBTZAsPrinted (SFALocalE0.sing puncture) := by
  intro h
  obtain ⟨hp, hu, hpu, hz, hz'⟩ := failure hC
  rw [h (singularFlatSpacetime hC) (stronglyCausal hC) p hp u hu hpu] at hz
  exact hz' hz

/-- **`J⁺(z)` is not closed in `E₀ ∖ {w}`**: `p_n ∈ J⁺(z)`, `p_n → p` and `p ∉ J⁺(z)`. This is
the hypothesis of `Causality.cup_cap_BTZ_of_isClosed` (`hJ`) that fails, at the very `z`. -/
theorem not_isClosed_Jplus_z (hC : SFALocalE0.IsE0Natural C) : ¬ IsClosed (C.Jplus ⊤ {z}) := by
  intro h
  have hmem : ∀ n, u n ∈ C.Jplus ⊤ {z} := fun n => Precausality.mem_Jplus_singleton.2
    ((le_top_iff hC _ _).2 (E0.causality.le_of_lt (lt_zE_uE puncture (fun _ hx => hx) n)))
  have hu : Tendsto u atTop (𝓝 p) := tendsto_subtype_rng.2 tendsto_uE
  have hp := h.mem_of_tendsto hu (Eventually.of_forall hmem)
  exact not_le_zE_pE puncture (fun hw => mem_puncture.1 hw rfl)
    ((le_top_iff hC _ _).1 (Precausality.mem_Jplus_singleton.1 hp))

/-- **`E₀ ∖ {w}` is not globally hyperbolic**, as DEC-19 requires: under global hyperbolicity the
printed form holds (`Causality.cupCapBTZAsPrinted_of_globallyHyperbolic`). -/
theorem not_globallyHyperbolic (hC : SFALocalE0.IsE0Natural C) : ¬ C.GloballyHyperbolic :=
  fun hG => not_cupCapBTZAsPrinted hC (Causality.cupCapBTZAsPrinted_of_globallyHyperbolic hG)

end Natural

/-- **The natural causality of `E₀ ∖ {w}`** (unique, `SFALocalE0.existsUnique_isE0Natural`). -/
noncomputable def natCausality : Causality puncture :=
  (SFALocalE0.existsUnique_isE0Natural e0Covered).exists.choose

theorem isE0Natural_natCausality : SFALocalE0.IsE0Natural natCausality :=
  (SFALocalE0.existsUnique_isE0Natural e0Covered).exists.choose_spec

/-- **`lem:cup_cap_BTZ` as printed is false**: a strongly causal (and causal, absolutely minimal)
singular flat spacetime where it fails. -/
theorem exists_counterexample :
    ∃ (M : Type) (_ : TopologicalSpace M) (C : Causality M) (sing : ℝ → Set M),
      C.SingularFlatSpacetime sing ∧ C.StronglyCausal ∧ C.StronglyCausalOpen ∧ C.IsCausal ∧
        C.AbsolutelyMinimal ∧ (sing 0).Nonempty ∧ ¬ C.CupCapBTZAsPrinted sing := by
  have hC := isE0Natural_natCausality
  exact ⟨puncture, inferInstance, natCausality, SFALocalE0.sing puncture, singularFlatSpacetime hC,
    stronglyCausal hC, stronglyCausalOpen hC, isCausal hC, hC.2.2,
    ⟨p, (mem_sing_zero_iff p).2 pE_mem_axis⟩, not_cupCapBTZAsPrinted hC⟩

/-- **The printed lemma, quantified over every space, is refuted.** -/
theorem not_forall_cupCapBTZAsPrinted :
    ¬ ∀ (M : Type) [TopologicalSpace M] (C : Causality M) (sing : ℝ → Set M),
      C.CupCapBTZAsPrinted sing := by
  intro h
  obtain ⟨M, _, C, sing, -, -, -, -, -, -, hnot⟩ := exists_counterexample
  exact hnot (h M C sing)

end CupCapBTZCounterexample

end Causal
