import GX.BTZ.MixedDiamond
import GX.BTZ.Uniformization

/-!
# `GXScaffold.BTZ.RegComplete` — `Reg M` of a Cauchy-complete `𝔼₀`-manifold (btz § 5.4)

Target T-btz-reg-complete. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`), § 5.4
« A complement on Cauchy-completeness », l.1562–1576. Row (unmarked, partial):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576:
  `GX.E0RegComplete.prop_reg_complete` (and `prop_reg_complete'`, the existential form).

> Let $M$ be a globally hyperbolic Cauchy-complete Cauchy-maximal $\mass{\geq0}$-manifold. Then,
> the complement of the BTZ-lines $\reg_{>0}(M)$ is globally hyperbolic Cauchy-maximal and
> Cauchy-complete. (l.1566–1569)

## What is proved

* **Global hyperbolicity** of `Reg M` (l.1571, « follows from Remark rem:reg_GH »): closed,
  `gh_regM` (the strict `E0AbsMax.gh_e0RegMFlat_e0`, which uses only `M` GH).
* **Cauchy-maximality** of `Reg M` (l.1571–1575): closed, `mgh_regM`, for EVERY globally
  hyperbolic Cauchy-maximal `𝔼₀`-manifold with a Cauchy surface — neither Cauchy-completeness nor
  smoothness is used, and neither is the surgery `Σ*` (`lem:curve_extension` (ii),
  `cor:intersect`) the paper invokes. A flat Cauchy embedding `f : Reg M → N` gives the push-out
  `M̄ = (M ⊔ N)/Reg M` of `lem:extension_hausdorff` (`exists_e0Pushout_mor`: the construction of
  `E0AbsMax.exists_e0Pushout`, the case `M₂ = N` flat GH, recording that `ι₂` is an
  `𝔼₀`-morphism); `M̄` is GH (`E0MixedDiamond.globallyHyperbolic_pushout`, which does not use
  compactness); `ι₁(M)` is causally convex in `M̄` (`causallyConvexIn_range_ι₁`, the step the
  paper leaves implicit), so the image of a Cauchy surface of `M` is a Cauchy surface of `M̄`
  (`isCauchySurface_pushout`, Sbierski's union argument
  `Causal.CBG.isCauchySurfaceOn_sup_of_slice`); then `ι₁` is a Cauchy embedding, onto by
  Cauchy-maximality of `M`, and `f` is onto.
* **Cauchy-completeness** of `Reg M` (l.1571, « the proof of Cauchy-completeness of Proposition
  prop:abs_max applies as is »): `regM_isCauchyComplete_of_complete`, tagged `sorry` (SCOPE).

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope, DEC-116 (b), DEC-125 (a)(e)): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable (DEC-66); then `Reg_{>0} M = Reg M = E0LM.e0RegM M` |
| globally hyperbolic | ✓ `(CE M).GloballyHyperbolic` |
| Cauchy-complete (l.227: « a smooth spacelike Cauchy-surface Σ … metrically complete ») | ⚠ read `IsE0C1CompleteCauchy`: DEC-31/119's `GX.IsE0CauchyComplete` (spacelike Lipschitz in `Reg M`'s flat charts, complete for the induced length extended across the BTZ lines, metric topology finer than `M`'s) with « smooth » read as DEC-107 reads it for Cauchy-compact (the `C¹` rim condition of `E0Surgery.IsE0C1SpacelikeCauchy.rim`) — a question |
| Cauchy-maximal (of `M`) | ✓ `E0Spear.IsE0CauchyMaximal` (DEC-77 (c)) |
| conclusion: GH | ✓ `Causal.Flat.GH (e0RegMFlat M)` |
| conclusion: Cauchy-maximal (of `Reg M`) | ✓ read `Causal.Flat.MGH (e0RegMFlat M)`: every flat Cauchy embedding is onto (a Cauchy extension of a spacetime with no singular line has none: every singular line would cross the image of a Cauchy surface) |
| conclusion: Cauchy-complete | ⚠ read: `Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)`, a spacelike-Lipschitz complete Cauchy surface (DEC-31/35), not the « smooth » one of l.227, as in `prop_abs_max_C1` |

## SCOPE (disclosed)

One tagged `sorry`, the non-compact surgery: B21's proof of `prop:abs_max` uses that a
Cauchy-compact `M` has **finitely many** BTZ lines (l.1091, « Since M is Cauchy-compact, it admits
finitely many BTZ-lines »; `E0Surgery.SurgeryData.finite`), so it does not apply « as is » to a
Cauchy-complete `M`, which may have countably many (the BTZ points of a Cauchy surface are only
discrete, kb/0217). What is missing is a locally finite countable `SurgeryData`, the Cauchy
property of `Σ*` with infinitely many spears, and the completeness of `Σ*`, for which no uniform
estimate across the spears is printed. -/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0RegComplete

open E0 E0CBG E0Spear E0AbsMax

variable (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **A `C¹` spacelike complete Cauchy surface of an `𝔼₀`-manifold** (B21/btz l.227's
« Cauchy-complete »: « a smooth spacelike Cauchy-surface which is … metrically complete »): DEC-31/119's
`GX.IsE0CauchyComplete` data on `S` (spacelike Lipschitz in the flat charts of `Reg M`, complete
for the induced length extended across the BTZ lines, with metric topology finer than `M`'s),
and « smooth » read as DEC-107 reads it for Cauchy-compact: the trace of `S` on the shaft of every
spear chart meeting it along a continuous graph is a `C¹` circle
(`E0Surgery.IsE0C1SpacelikeCauchy.rim`, verbatim). -/
structure IsE0C1CompleteCauchy (S : Set M) : Prop where
  cauchy : (CE M).IsCauchySurface S
  reg : Causal.Flat.IsSpacelikeLipschitz 2 (E0Surgery.regSet M S)
  complete : CompleteSpace (Causal.Flat.LocalLengthSpace (e0SliceSys S))
  continuous : Continuous fun x : Causal.Flat.LocalLengthSpace (e0SliceSys S) =>
    ((Causal.Flat.LocalLengthSpace.toSpace x : S) : M)
  rim : ∀ (R v : ℝ) (W : Set E0Y) (ψ : E0Y → M) (τS : ℂ → ℝ), 0 < R → IsOpen W →
    E0Spear.spearY v R ⊆ W → E0Spear.IsE0Mor ψ W → InjOn ψ W →
    ContinuousOn τS (Metric.closedBall 0 R) →
    (∀ z : ℂ, ‖z‖ ≤ R → v + R / 2 < τS z) →
    (∀ x ∈ E0Spear.spear v R, (ψ (paperInY x) ∈ S ↔ x.1 = τS x.2)) →
    ContDiff ℝ 1 (E0Surgery.rimFun τS R)

/-- **Cauchy-complete `𝔼₀`-manifold** (btz l.227, read as `IsE0C1CompleteCauchy`). -/
def E0C1CauchyComplete : Prop := ∃ S : Set M, IsE0C1CompleteCauchy M S

variable {M}

omit [SecondCountableTopology M] in
/-- The reading is at least DEC-31/119's `GX.IsE0CauchyComplete`. -/
theorem IsE0C1CompleteCauchy.isE0CauchyComplete {S : Set M} (hS : IsE0C1CompleteCauchy M S) :
    IsE0CauchyComplete M :=
  ⟨S, hS.cauchy, hS.reg, hS.complete, hS.continuous⟩

/-- **`Reg M` is globally hyperbolic** (btz `rem:reg_GH`, l.594; l.1571). -/
theorem gh_regM (hGH : (CE M).GloballyHyperbolic) : Causal.Flat.GH (e0RegMFlat M) :=
  gh_e0RegMFlat_e0 hGH

/-- **The push-out of `lem:extension_hausdorff`, with its second leg an `𝔼₀`-morphism**: the
construction of `E0AbsMax.exists_e0Pushout` (verbatim), recording what the structure
`E0Pushout` forgets, that `ι₂ : FlatE0 N → M̄` is an `𝔼₀`-morphism (a chart of the glued atlas
on `N` is a chart of `N` followed by `inl`). -/
theorem exists_e0Pushout_mor {N : Causal.Flat.FlatSpacetime.{0} 2}
    (hN : Causal.Flat.GH N) {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    ∃ P : E0Pushout M N f, IsE0Mor (fun y : FlatE0 N => P.ι₂ y) univ := by
  haveI hT2 := lem_extension_hausdorff hN hf
  have hj₁ : IsOpenEmbedding (Subtype.val : E0LM.e0RegM M → M) :=
    (E0LM.e0RegM M).isOpen.isOpenEmbedding_subtypeVal
  have hj₂ := hf.isOpenEmbedding
  have hinj₁ : Injective (Subtype.val : E0LM.e0RegM M → M) := Subtype.val_injective
  have he : ∀ b, IsOpenEmbedding (pushEmb f b) := by
    intro b; cases b
    · exact Causal.Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
    · exact Causal.Gluing.isOpenEmbedding_ι₁ hj₁ hj₂
  have hcov : ∀ z, ∃ b, z ∈ range (pushEmb f b) := by
    intro z
    rcases Causal.Gluing.exists_ι z with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨true, x, hx⟩
    · exact ⟨false, y, hy⟩
  have hsymm : ∀ b (x : pushPiece M N b),
      (Causal.CBG.glueEmb he b).symm (pushEmb f b x) = x := fun b x =>
    Causal.CBG.glueEmb_symm_apply he b x
  have htrans : ∀ i j, ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt
      (Causal.CBG.glueTransition he i j) (pushEmb f i ⁻¹' range (pushEmb f j)) := by
    have hWo : ∀ i j, IsOpen (pushEmb f i ⁻¹' range (pushEmb f j)) := fun i j =>
      (he j).isOpen_range.preimage (he i).continuous
    intro i j
    cases i <;> cases j
    · refine Causal.CBG.liftPropOn_congr_of_eqOn (hWo false false)
        (Causal.CBG.liftPropOn_id (hWo false false)) fun x _ => ?_
      exact (hsymm false x).symm
    · -- `N → M`: `f⁻¹` on `range f`
      have hW : pushEmb f false ⁻¹' range (pushEmb f true) = (range f : Set N) := by
        ext y
        constructor
        · rintro ⟨x, hx⟩
          obtain ⟨w, -, rfl⟩ := (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 hx
          exact ⟨w, rfl⟩
        · rintro ⟨w, rfl⟩
          exact ⟨(toRegM w : M), Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M))
            (j₂ := f) (toRegM w)⟩
      show ChartedSpace.LiftPropOn _ _ (pushEmb f false ⁻¹' range (pushEmb f true))
      rw [hW]
      refine Causal.CBG.liftPropOn_congr_of_eqOn hj₂.isOpen_range (isE0Mor_regInv hf) ?_
      rintro _ ⟨w, rfl⟩
      show regInv hf (f w) = (Causal.CBG.glueEmb he true).symm (pushEmb f false (f w))
      have h1 : pushEmb f false (f w) = pushEmb f true (toRegM w : M) :=
        (Causal.Gluing.ι₁_j₁ (toRegM w)).symm
      rw [regInv_apply, h1, hsymm]
    · -- `M → N`: `f` on `Reg M`
      have hW : pushEmb f true ⁻¹' range (pushEmb f false) = (E0LM.e0RegM M : Set M) := by
        ext x
        constructor
        · rintro ⟨y, hy⟩
          obtain ⟨w, rfl, -⟩ := (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 hy.symm
          exact w.2
        · intro hx
          exact ⟨f ⟨x, hx⟩, (Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M))
            (j₂ := f) (⟨x, hx⟩ : E0LM.e0RegM M)).symm⟩
      show ChartedSpace.LiftPropOn _ _ (pushEmb f true ⁻¹' range (pushEmb f false))
      rw [hW]
      refine Causal.CBG.liftPropOn_congr_of_eqOn (E0LM.e0RegM M).isOpen
        (isE0Mor_regExt hf (Classical.arbitrary N)) ?_
      intro x hx
      show regExt f _ x = (Causal.CBG.glueEmb he false).symm (pushEmb f true x)
      have h1 : pushEmb f true x = pushEmb f false (f ⟨x, hx⟩) :=
        Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f)
          (⟨x, hx⟩ : E0LM.e0RegM M)
      rw [regExt_apply f _ x hx, h1, hsymm]
    · refine Causal.CBG.liftPropOn_congr_of_eqOn (hWo true true)
        (Causal.CBG.liftPropOn_id (hWo true true)) fun x _ => ?_
      exact (hsymm true x).symm
  letI cs : ChartedSpace E0Y (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) :=
    Causal.CBG.gluedChartedSpace E0Y he hcov
  haveI gx : HasGroupoid (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) e0Groupoid :=
    Causal.CBG.gluedChartedSpace_hasGroupoid he hcov htrans
  have hι : ∀ b, IsE0Mor (pushEmb f b) univ := Causal.CBG.liftPropOn_glue he hcov htrans
  obtain ⟨x₀, hx₀⟩ := (E0LM.dense_e0RegM (M := M)).nonempty
  haveI hconn : ConnectedSpace (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) := by
    have h1 := isPreconnected_range
      (Causal.Gluing.continuous_ι₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f))
    have h2 := isPreconnected_range
      (Causal.Gluing.continuous_ι₂ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f))
    have h12 := IsPreconnected.union
      (s := range (Causal.Gluing.ι₁ (Subtype.val : E0LM.e0RegM M → M) f))
      (t := range (Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f))
      (Causal.Gluing.ι₁ _ f x₀) ⟨x₀, rfl⟩
      ⟨f ⟨x₀, hx₀⟩, (Causal.Gluing.ι₁_j₁ (j₁ := (Subtype.val : E0LM.e0RegM M → M)) (j₂ := f)
        (⟨x₀, hx₀⟩ : E0LM.e0RegM M)).symm⟩ h1 h2
    have hU : (univ : Set (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f)) ⊆
        range (Causal.Gluing.ι₁ (Subtype.val : E0LM.e0RegM M → M) f) ∪
          range (Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f) := fun z _ =>
      (Causal.Gluing.exists_ι z).imp (fun ⟨x, hx⟩ => ⟨x, hx⟩) (fun ⟨y, hy⟩ => ⟨y, hy⟩)
    refine { isPreconnected_univ := ?_, toNonempty := ⟨Causal.Gluing.ι₁ _ f x₀⟩ }
    rw [← Set.eq_univ_of_univ_subset hU]
    exact h12
  haveI hsc : SecondCountableTopology (Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f) :=
    isQuotientMap_quot_mk.secondCountableTopology (Causal.Gluing.isOpenMap_mk hj₁ hj₂)
  refine ⟨{ carrier := Causal.Gluing (Subtype.val : E0LM.e0RegM M → M) f
            ι₁ := Causal.Gluing.ι₁ _ f
            ι₂ := Causal.Gluing.ι₂ (Subtype.val : E0LM.e0RegM M → M) f
            isE0Mor_ι₁ := hι true
            injective_ι₁ := Causal.Gluing.injective_ι₁ hinj₁ hf.2
            isOpenEmbedding_ι₂ := Causal.Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
            comm := fun w => Causal.Gluing.ι₁_j₁ w
            cover := Causal.Gluing.exists_ι
            glue := fun x y h => (Causal.Gluing.ι₁_eq_ι₂_iff hinj₁ hf.2).1 h
            sing_ι₁ := fun x => (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem
              isOpen_univ (hι true) (mem_univ x) le_rfl).symm
            sing_ι₂ := fun y h => ?_
            le_ι₂ := fun U hU y y' => ?_ }, hι false⟩
  · have h' := (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem isOpen_univ (hι false)
      (mem_univ (show FlatE0 N from y)) le_rfl).2 h
    exact h'.2 (inl_mem_e0Reg _)
  · exact (le_iff_of_isE0Mor (hι false)
      (Causal.Gluing.injective_ι₂ hinj₁ hf.2) hU y y').trans (flatE0_rel_iff N ⊤ y y').1

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **The image of a flat Cauchy embedding is causally convex**
(`Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn`: a Cauchy surface of the image which is a
Cauchy surface of `N`). -/
theorem causallyConvexIn_range_of_isFlatCauchyEmbedding {X N : Causal.Flat.FlatSpacetime.{0} 2}
    {f : X → N} (hf : Causal.Flat.IsFlatCauchyEmbedding 2 f) :
    (Causal.Flat.flatCausality 2 N).CausallyConvexIn (range f) ⊤ := by
  obtain ⟨T, hT, hTN⟩ := hf.2.exists_cauchy
  have hGN := hf.2.globallyHyperbolic_target
  have h := Causal.Causality.causallyConvexIn_of_isCauchySurfaceOn (C := Causal.Flat.flatCausality 2 N)
    (A := hf.2.rangeOpens) (B := ⊤) (fun x y hxy hyx => hGN.1 hxy hyx)
    (Causal.Flat.flatCausality_causallyArcConnected 2 N) Causal.CBG.flat_curvesExtend le_top
    (by rw [Causal.IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range _ _)
    ((hf.2.isEMorphism.isCauchySurface_iff hf.2.injective T).1 hT) hTN
  rwa [Causal.IsCauchyEmbedding.coe_rangeOpens] at h

/-- **`ι₁(M)` is causally convex in the push-out** (the step B21 leaves implicit when it says that
`M → M̄` is a Cauchy extension). A causal `p ≤ r ≤ q` with `p, q ∈ ι₁(M)` and `r ∉ ι₁(M)`: `r` is
regular (the BTZ points of `M̄` are in `ι₁(M)`), hence so is `q` (the past of a BTZ point is BTZ,
`lem:past_BTZ`); if `p` is BTZ, an earlier point `p′` of its BTZ line has `p′ ≪ r` (DEC-64's
`Iplus_of_lt`), and a regular `s ∈ ι₁(M) ∩ I⁻(r)` near `p′` replaces `p`. Then `s, r, q` lie in
`ι₂(N)`, which is causally convex (Lemma 2.13 (b)), so `f(s′) ≤ r′ ≤ f(q′)` in `N`, and `r′ ∈ f(Reg M)`
by causal convexity of the image of the Cauchy embedding `f`: `r = ι₂ (f w) = ι₁ w`. -/
theorem causallyConvexIn_range_ι₁ (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsFlatCauchyEmbedding 2 f) (P : E0Pushout M N f) :
    (CE P.carrier).CausallyConvexIn (range P.ι₁) ⊤ := by
  have hN : Causal.Flat.GH N := hf.2.globallyHyperbolic_target
  have hGP := E0MixedDiamond.globallyHyperbolic_pushout hGH hmax hN P
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨hAo, hsA, hBc⟩ := P.pieces
  have hconvN := causallyConvexIn_range_of_isFlatCauchyEmbedding hf
  -- a regular point of `ι₁(M)` is `ι₂ (f w)`
  have hreg : ∀ z, z ∈ range P.ι₁ → z ∉ S0 P.carrier → ∃ w : E0LM.e0RegM M, P.ι₂ (f w) = z := by
    rintro z ⟨x, rfl⟩ hz
    obtain ⟨y, hy⟩ : P.ι₁ x ∈ range P.ι₂ := by_contra fun h => hz (hBc h)
    obtain ⟨w, -, hw⟩ := P.glue x y hy.symm
    exact ⟨w, by rw [hw, hy]⟩
  refine ⟨fun _ _ => trivial, fun p hp q hq r hr => ?_⟩
  obtain ⟨hpr, hrq⟩ := Causal.Causality.mem_diamond.1 hr
  by_contra hrA
  have hr0 : r ∉ S0 P.carrier := fun h => hrA (hsA h)
  have hq0 : q ∉ S0 P.carrier := fun h => hr0 (hP.mem_sing_zero_of_le h hrq)
  -- a regular `s ∈ ι₁(M)` with `s ≤ r`
  obtain ⟨s, hsA', hs0, hsr⟩ : ∃ s, s ∈ range P.ι₁ ∧ s ∉ S0 P.carrier ∧
      (CE P.carrier).le ⊤ s r := by
    by_cases hp0 : p ∈ S0 P.carrier
    · obtain ⟨γ, hγ0, hγemb, hγi, hγr⟩ := hP.line p hp0
      have hp'p : (CE P.carrier).le ⊤ (γ (-1)) p := by
        rw [← hγ0]; exact hγi.1.le_of_le (mem_univ _) (mem_univ _) (by norm_num)
      have hne : γ (-1) ≠ p := by
        rw [← hγ0]; exact fun h => absurd ((hγemb hGP.1).injective h) (by norm_num)
      have hp'0 : γ (-1) ∈ S0 P.carrier := by
        have : γ (-1) ∈ range γ := mem_range_self _
        rw [hγr] at this
        exact connectedComponentIn_subset _ _ this
      have hlt := hP.lt_of_lt_of_le_of_not_mem hp'0 hp0 hp'p hne hr0 hpr
      have hO : IsOpen (range P.ι₁ ∩ (CE P.carrier).Iminus ⊤ {r}) :=
        hAo.inter (CE P.carrier).isOpen_Iminus
      have hp'O : γ (-1) ∈ range P.ι₁ ∩ (CE P.carrier).Iminus ⊤ {r} :=
        ⟨hsA hp'0, Causal.Precausality.mem_Iminus_singleton.2 hlt⟩
      obtain ⟨s, ⟨hsA', hsI⟩, hs0⟩ : ∃ s ∈ range P.ι₁ ∩ (CE P.carrier).Iminus ⊤ {r},
          s ∉ S0 P.carrier := by
        by_contra hcon
        push Not at hcon
        have hsub : range P.ι₁ ∩ (CE P.carrier).Iminus ⊤ {r} ⊆ interior (S0 P.carrier) :=
          interior_maximal hcon hO
        rw [hP.interior_sing 0 le_rfl] at hsub
        exact hsub hp'O
      exact ⟨s, hsA', hs0,
        (CE P.carrier).le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hsI)⟩
    · exact ⟨p, hp, hp0, hpr⟩
  obtain ⟨w₁, rfl⟩ := hreg s hsA' hs0
  obtain ⟨w₂, rfl⟩ := hreg q hq hq0
  obtain ⟨y, rfl⟩ : r ∈ range P.ι₂ := by_contra fun h => hr0 (hBc h)
  have h1 := (E0MixedDiamond.le_top_ι₂_iff hN P _ _).1 hsr
  have h2 := (E0MixedDiamond.le_top_ι₂_iff hN P _ _).1 hrq
  obtain ⟨w, hw⟩ := hconvN.2 _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ (Causal.Causality.mem_diamond.2 ⟨h1, h2⟩)
  exact hrA ⟨((show E0LM.e0RegM M from w) : M), by
    rw [P.comm (show E0LM.e0RegM M from w)]; exact congrArg P.ι₂ hw⟩

/-- **The Cauchy-extension step of l.1573–1575**: for a flat Cauchy embedding `f : Reg M → N`
and the push-out `M̄` of `lem:extension_hausdorff` whose leg `ι₂` is an `𝔼₀`-morphism, the image
of every Cauchy surface `S` of `M` is a Cauchy surface of `M̄`. Proved with no surgery: `M̄ =
ι₁(M) ∪ ι₂(N)`, `ι₁(S)` is Cauchy in `ι₁(M)`, `ι₂(f(T₀))` is a Cauchy surface of `ι₂(N)` inside
`ι₁(M)`, and `ι₁(S)` is acausal in `M̄` because `ι₁(M)` is causally convex
(`Causal.CBG.isCauchySurfaceOn_sup_of_slice`, Sbierski's union argument). -/
theorem isCauchySurface_pushout (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hmax : IsE0CauchyMaximal M)
    {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}
    (hf : Causal.Flat.IsFlatCauchyEmbedding 2 f) (P : E0Pushout M N f)
    (hι₂ : IsE0Mor (fun y : FlatE0 N => P.ι₂ y) univ) :
    (CE P.carrier).IsCauchySurface (P.ι₁ '' S) := by
  have hN : Causal.Flat.GH N := hf.2.globallyHyperbolic_target
  have hGP := E0MixedDiamond.globallyHyperbolic_pushout hGH hmax hN P
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨T₀, -, hT₀N⟩ := hf.2.exists_cauchy
  have hψ := isEMorphismOn_of_isE0Mor (W := ⊤) P.isE0Mor_ι₁
  have hφ := isEMorphismOn_of_isE0Mor (W := ⊤) hι₂
  have hA := (Causal.IsEMorphism.isCauchySurface_iff hψ P.injective_ι₁ S).1 hS
  have hT₀E : (CE (FlatE0 N)).IsCauchySurface (f '' T₀) := fun I c hc =>
    hT₀N I c ((Causal.Causality.inextensible_congr_causality
      fun U _ x y => (flatE0_rel_iff N U x y).1).1 hc)
  have hB := (Causal.IsEMorphism.isCauchySurface_iff hφ P.isOpenEmbedding_ι₂.injective (f '' T₀)).1 hT₀E
  have hconv := causallyConvexIn_range_ι₁ hGH hmax hf P
  have hac : (CE P.carrier).IsAcausal (P.ι₁ '' S) := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩ hle
    have hle' := Causal.Causality.le_of_causallyConvexIn hP.causallyArcConnected hconv
      (N := ⟨range P.ι₁, P.pieces.1⟩) subset_rfl ⟨s₁, rfl⟩ ⟨s₂, rfl⟩ hle
    rw [le_iff_of_isE0Mor P.isE0Mor_ι₁ P.injective_ι₁ rfl] at hle'
    rw [isAcausal_of_isCauchySurface_e0 hGH hS s₁ hs₁ s₂ hs₂ hle']
  have hΓ : (fun y : FlatE0 N => P.ι₂ y) '' (f '' T₀) ⊆ hψ.imageOpens ⊤ le_rfl := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact ⟨((show E0LM.e0RegM M from w) : M), trivial, P.comm (show E0LM.e0RegM M from w)⟩
  have h := Causal.CBG.isCauchySurfaceOn_sup_of_slice hGP.1 hac hA hB hΓ
  have htop : hψ.imageOpens ⊤ le_rfl ⊔ hφ.imageOpens ⊤ le_rfl = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rcases P.cover z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Opens.mem_sup.2 (Or.inl ⟨x, trivial, rfl⟩)
    · exact Opens.mem_sup.2 (Or.inr ⟨y, trivial, rfl⟩)
  rwa [htop] at h

/-- **`Reg M` is Cauchy-maximal** (l.1571–1575). -/
theorem mgh_regM (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.MGH (e0RegMFlat M) := by
  refine ⟨gh_regM hGH, fun N f hf => ?_⟩
  have hN : Causal.Flat.GH N := hf.2.globallyHyperbolic_target
  obtain ⟨P, hι₂⟩ := exists_e0Pushout_mor hN hf.1
  have hGP := E0MixedDiamond.globallyHyperbolic_pushout hGH hmax hN P
  have hCE : Causal.IsCauchyEmbedding (CE M) (CE P.carrier) P.ι₁ :=
    ⟨hGH, hGP, isEMorphismOn_of_isE0Mor (W := ⊤) P.isE0Mor_ι₁, P.injective_ι₁, S, hS,
      isCauchySurface_pushout hGH hS hmax hf P hι₂⟩
  have hbij := hmax P.carrier P.ι₁ hCE P.isE0Mor_ι₁
  intro y
  obtain ⟨x, hx⟩ := hbij.2 (P.ι₂ y)
  obtain ⟨w, -, hw⟩ := P.glue x y hx
  exact ⟨w, hw⟩

/-- **btz `prop:reg_complete`, its first two assertions, with no completeness hypothesis**: for
`M` a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold with a Cauchy surface, `Reg M` is globally
hyperbolic and Cauchy-maximal. -/
theorem gh_mgh_regM (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.MGH (e0RegMFlat M) :=
  ⟨gh_regM hGH, mgh_regM hGH hS hmax⟩

/-- **`Reg M` is Cauchy-complete** (l.1571). -/
theorem regM_isCauchyComplete_of_complete (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1CompleteCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) :=
  sorry -- SORRY(btzprop:reg_complete): the non-compact surgery. `E0Surgery.SurgeryData` has
  -- finitely many spears (`finite`, from compactness: B21 l.1091) and `exists_surgeryData`,
  -- `SurgeryData.isCauchySurface_sigmaStar`, `completeSpace_sigmaStar` take a compact
  -- `IsE0C1SpacelikeCauchy` surface; a complete `S` may carry countably many BTZ points (discrete
  -- and closed in `S`, kb/0217). Owed: (1) a countable, locally finite family of pairwise disjoint
  -- closed spears around `S ∩ sing₀ M`, each with `S`'s trace a C¹ circle in its shaft (Lemmas
  -- tube, add_BTZ_param); (2) `Σ*` Cauchy in `Reg M` with infinitely many spears (cor:intersect in
  -- each, plus local finiteness for an inextensible curve meeting infinitely many spears);
  -- (3) `Σ*` complete for its induced length: Lemma 2.8's `log r` estimate inside each spear and
  -- a comparison, uniform across infinitely many spears, with the DEC-31 length of `S` outside —
  -- not printed in the paper (« applies as is »).

/-- **btz `prop:reg_complete`** (`BTZ_1.tex:1566–1569`), `𝔼₀` form: for `M` a globally
hyperbolic, Cauchy-maximal `𝔼₀`-manifold with a `C¹` spacelike complete Cauchy surface `S`,
`Reg M` is globally hyperbolic, Cauchy-maximal and Cauchy-complete. -/
theorem prop_reg_complete (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : IsE0C1CompleteCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.MGH (e0RegMFlat M) ∧
      Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) :=
  ⟨gh_regM hGH, mgh_regM hGH hS.cauchy hmax, regM_isCauchyComplete_of_complete hGH hS hmax⟩

/-- **btz `prop:reg_complete`**, with « Cauchy-complete » as an existential. -/
theorem prop_reg_complete' (hGH : (CE M).GloballyHyperbolic) (hCC : E0C1CauchyComplete M)
    (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.MGH (e0RegMFlat M) ∧
      Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) := by
  obtain ⟨S, hS⟩ := hCC
  exact prop_reg_complete hGH hS hmax

end E0RegComplete

end GX
