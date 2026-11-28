import GX.BTZ.MixedDiamond
import GX.BTZ.Uniformization
import GX.BTZ.RegCompleteLength

/-!
# `GX.BTZ.RegComplete` — `Reg M` of a Cauchy-complete `𝔼₀`-manifold (btz § 5.4)

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
  `M̄ = (M ⊔ N)/Reg M` of `lem:extension_hausdorff` (`exists_e0Pushout_mor`:
  `E0AbsMax.exists_e0Pushout`, the case `M₂ = N` flat GH, with `ι₂` an `𝔼₀`-morphism,
  `E0Pushout.isE0Mor_ι₂`); `M̄` is GH (`E0MixedDiamond.globallyHyperbolic_pushout`, which does not use
  compactness); `ι₁(M)` is causally convex in `M̄` (`causallyConvexIn_range_ι₁`, the step the
  paper leaves implicit), so the image of a Cauchy surface of `M` is a Cauchy surface of `M̄`
  (`isCauchySurface_pushout`, Sbierski's union argument
  `Causal.CBG.isCauchySurfaceOn_sup_of_slice`); then `ι₁` is a Cauchy embedding, onto by
  Cauchy-maximality of `M`, and `f` is onto.
* **Cauchy-completeness** of `Reg M` (l.1571, « the proof of Cauchy-completeness of Proposition
  prop:abs_max applies as is »): `regM_isCauchyComplete_of_complete`, which is
  `E0SpearFamily.regM_isCauchyComplete_of_lf` (`GX.BTZ.RegCompleteLength`): the
  non-compact surgery with a countable locally finite family of spears (steps (1)–(2),
  `SpearFamily`, `RegCompleteCauchy`), `Σ*` spacelike Lipschitz and Lemma 2.8's `log r` estimate
  on it; sorry-free since T-btz-reg-complete-tail (`GX.BTZ.RegCompleteTail`).
* The reading `IsE0C1CompleteCauchy` / `E0C1CauchyComplete` now lives in
  `GX.BTZ.CompleteCauchy` (same full names), so that the surgery files need not import
  this one.

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

`prop_reg_complete` and `prop_reg_complete'` have no `sorry` beneath them. The step that needed
uniformity across infinitely many spears, `E0SpearFamily.LFSurgeryData.exists_isCompact_of_cauchySeq`
(the tail of a Cauchy sequence of `Σ*` lies in a compact set of `M`), is proved in
`GX.BTZ.RegCompleteTail` (summable radii, spear-by-spear surgery). B21's proof of
`prop:abs_max` uses that a Cauchy-compact `M` has **finitely many** BTZ lines (l.1091) and a
compact `S`, so it does not apply « as is » to a Cauchy-complete `M`, which may have countably
many (kb/0217); the uniformity across the spears is not printed. The row stays partial: the
`𝔼₀` scope and the readings of the checklist.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace

namespace E0RegComplete

open E0 E0CBG E0Spear E0AbsMax

variable (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

variable {M}

/-- **`Reg M` is globally hyperbolic** (btz `rem:reg_GH`, l.594; l.1571). -/
theorem gh_regM (hGH : (CE M).GloballyHyperbolic) : Causal.Flat.GH (e0RegMFlat M) :=
  gh_e0RegMFlat_e0 hGH

/-- **The push-out of `lem:extension_hausdorff`, with its second leg an `𝔼₀`-morphism**: the
strict `E0AbsMax.exists_e0Pushout`, whose structure `E0Pushout` records that
`ι₂ : FlatE0 N → M̄` is an `𝔼₀`-morphism (`E0Pushout.isE0Mor_ι₂`, T-gx-btz-cleanup). -/
theorem exists_e0Pushout_mor {N : Causal.Flat.FlatSpacetime.{0} 2}
    (hN : Causal.Flat.GH N) {f : e0RegMFlat M → N} (hf : Causal.Flat.IsIsometricEmbedding 2 f) :
    ∃ P : E0Pushout M N f, IsE0Mor (fun y : FlatE0 N => P.ι₂ y) univ :=
  let ⟨P⟩ := exists_e0Pushout hN hf
  ⟨P, P.isE0Mor_ι₂⟩

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
  E0SpearFamily.regM_isCauchyComplete_of_lf hGH hS hmax

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
