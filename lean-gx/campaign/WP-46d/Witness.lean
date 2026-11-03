import GXScaffold.BTZ.LiftGH
import GXScaffold.BTZ.Uniformization
import GXScaffold.BTZ.HeadlineBridge

/-!
# WP-46d — a concrete witness of DEC-118 (b) with BTZ points (evidence file, not a module)

`campaign/WP-46d/Witness.lean`, checked by `lake env lean`; it is NOT part of the library, so that
`GXScaffold.BTZ.LiftGH` keeps importing `GX.BTZ.Manifolds` only (no coupling to the scaffold
packages `Uniformization` (WP-41/44, via `AbsMax`) and `HeadlineBridge` (WP-46g)).

The `𝔼₀`-manifold `{τ < 0} ⊆ 𝔼₀` (`GX.e0PastHalf`, globally hyperbolic and with a BTZ line,
`GX.e0PastHalf_globallyHyperbolic`, `GX.e0PastHalf_sing_nonempty`), with the singular structure
of the bridge (`GX.E0Bridge.e0SingularGXStructure`, DEC-119), is a globally hyperbolic
`BTZ`-manifold with `sing ≠ ∅`; its chartwise maximal branched covering `\widetilde M` is
globally hyperbolic in its natural topology (`GX.exists_btzTildeData_natGloballyHyperbolic`) and
has BTZ points.
-/

namespace GX

open Set
open scoped Real

attribute [local instance] btzE0Structure

theorem e0PastHalf_tilde_natGloballyHyperbolic :
    letI := E0Bridge.e0SingularGXStructure e0PastHalf
    (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf).Nonempty ∧
    (e0ManifoldCausality e0PastHalf E0Bridge.isBTZSingModelled_e0).GloballyHyperbolic ∧
    ∃ (y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf)ᶜ : Set e0PastHalf))
      (yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0))
      (Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ) (d : BTZTildeData e0PastHalf y₀ Φ),
      d.IsChartwise ∧ d.natCausality.GloballyHyperbolic ∧
      ∃ e : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf) y₀,
        e.base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf := by
  letI := E0Bridge.e0SingularGXStructure e0PastHalf
  have hS : Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf =
      Causal.CBG.chartedSing e0SingY e0PastHalf 0 := E0Bridge.sing_e0SingularGXStructure
  have hSn : (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf).Nonempty :=
    hS ▸ e0PastHalf_sing_nonempty
  have hGH : (e0ManifoldCausality e0PastHalf E0Bridge.isBTZSingModelled_e0).GloballyHyperbolic :=
    E0Bridge.globallyHyperbolic_e0ManifoldCausality_iff.2 e0PastHalf_globallyHyperbolic
  refine ⟨hSn, hGH, ?_⟩
  haveI : Nonempty e0PastHalf := ⟨hSn.some⟩
  obtain ⟨x, hx⟩ := (E0Bridge.isPortly_e0RegM (M := e0PastHalf)).dense.nonempty
  have hx' : x ∈ (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf)ᶜ := by
    show x ∈ (Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) e0PastHalf)ᶜᶜ
    rw [compl_compl, E0Bridge.reg_e0SingularGXStructure]; exact hx
  obtain ⟨yN, Φ, hΦ⟩ := btz_exists_presentation
  obtain ⟨d, hd, hG⟩ := exists_btzTildeData_natGloballyHyperbolic E0Bridge.isBTZSingModelled_e0
    hGH ⟨x, hx'⟩ hΦ
  obtain ⟨s, hs⟩ := hSn
  obtain ⟨e, he⟩ := (maxBranched_basic (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
    e0PastHalf) BTZTildeData.semilocallySimplyConnected_reg ⟨x, hx'⟩).2.1.surjective s
  exact ⟨⟨x, hx'⟩, yN, Φ, d, hd, hG, e, he ▸ hs⟩

end GX

#print axioms GX.e0PastHalf_tilde_natGloballyHyperbolic
