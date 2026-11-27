import GXScaffold.BTZ.MaxExtension

/-!
# btz § 5.3: two Cauchy-maximal Cauchy-compact `𝔼₀`-manifolds with isomorphic regular parts are isomorphic

Target `T-btz-common-reg` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
The row is not marked: `𝔼₀`-manifolds only is the paper's own case here, but the inputs are
partial (T-btz-scope), and `M`, `N` connected is added (OQ-150 (b), DEC-125 (e)).

* `btzcor:common_reg` — `BTZ_1.tex:1274` (proof l.1277–1279) — `GX.BTZCommonReg.common_reg`
  (an isomorphism `M ≃ N`, a homeomorphism which is an `𝔼₀`-morphism both ways, extending the
  given isomorphism `Reg M ≃ Reg N`), with `GX.BTZCommonReg.isMaximal_of_isE0Maximal` (the bridge
  « `𝔼≥0`-maximal ⇒ BTZ-maximal » to `Causal.AbstractDev.IsMaximal` over `GX.BTZMax.GHExt`),
  `GX.BTZCommonReg.isMaximal_regExt` (« `M ≃ BTZext(Reg M)` ») and
  `GX.BTZCommonReg.equiv_of_isE0Maximal` (the corollary with `𝔼₀`-maximality in place of
  Cauchy-maximality and Cauchy-compactness).

> Let $M,N$ be globally hyperbolic Cauchy-maximal Cauchy-compact $\mass{0}$-manifolds:
> $$\reg(M)\simeq \reg(N) \quad \Rightarrow{} \quad M\simeq N.$$ (l.1274–1276)
>
> Since $M$ and $N$ are Cauchy-compact and Cauchy-maximal, by Proposition \ref{prop:cauchy_abs_max},
> they are $\mass{\geq0}$-maximal. In particular, $M$ and $N$ are BTZ-maximal. Furthermore, by
> Remark \ref{rem:reg_GH}, $\reg(M)$ and $\reg(N)$ are globally hyperbolic. Assuming
> $\reg(M)\simeq \reg(N)$, Theorem \ref{theo:BTZ_ext} thus gives
> $$M \simeq \BTZext(\reg(M)) \simeq \BTZext(\reg(N)) \simeq N.$$ (l.1278)

## Hypothesis checklist (`common_reg`)

| paper hypothesis | here |
|---|---|
| `M`, `N` `𝔼₀`-manifolds (Hausdorff, second countable, l.261) | ✓ carried |
| (none; l.261 does not require it) | ⚠ strengthened: `M`, `N` connected (OQ-150 (b); `prop_cauchy_abs_max_e0` and `GX.Ppcm.btz_ppcm` are for connected manifolds, DEC-125 (e)) |
| globally hyperbolic | ✓ carried |
| Cauchy-maximal | ✓ carried (`IsE0CauchyMaximal`) |
| Cauchy-compact | ✓ carried (`E0CauchyCompact`: a compact acausal Cauchy surface) |
| `reg(M) ≃ reg(N)` | ⚠ weakened: a bijective `𝔼₀`-morphism `Reg M → Reg N` (its inverse is then one, `GX.isE0Mor_inv_of_bijective`) |
| conclusion `M ≃ N` | ✓ carried, strengthened: a homeomorphism `F`, `𝔼₀`-morphism both ways, with `F ∘ val = val ∘ φ` (it extends the given isomorphism of the regular parts) |

## SCOPE (disclosed)

* **No `RichardsInput`.** The paper's route goes through the existence of `BTZext(Reg M)`
  (Theorem `theo:BTZ_ext`), which in Lean rests on the named input `GX.BTZMax.RichardsInput`.
  Here existence is not needed: `M` itself (with `Reg M ↪ M`) and `N` (with
  `Reg M ≃ Reg N ↪ N`) are two globally hyperbolic BTZ-extensions of `Reg M`, each maximal by
  `𝔼₀`-maximality (`isMaximal_of_isE0Maximal`, from `prop_cauchy_abs_max_of_cauchyCompact_e0`),
  and the uniqueness half `GX.BTZMax.equivalent_of_isMaximal`, which does not use
  `RichardsInput`, makes them equivalent.
* **Remark `rem:reg_GH`** (that `Reg M` is globally hyperbolic) is not used: `GX.BTZMax.GHExt`
  asks the extension, not the extended manifold, to be globally hyperbolic.
* **The reading of « isomorphism »** of `𝔼₀`-manifolds is a bijective `𝔼₀`-morphism
  (`IsE0Mor`, DEC-62, OQ-142 (a)); the regular parts carry the induced structure of the open sets
  `E0LM.e0RegM`. The flat-spacetime form `e0RegMFlat` is not bridged here.
* `𝔼₀` only: for `𝔼₀`-manifolds `reg = reg_{>0}`, the complement of the BTZ lines.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Function TopologicalSpace
open E0CBG E0Spear

namespace BTZCommonReg

open BTZMax

section Bridge

variable {A : Type} [TopologicalSpace A] [ChartedSpace E0Y A]

/-- **`𝔼₀`-maximal ⇒ BTZ-maximal** (`BTZ_1.tex:1278`, « In particular, M and N are BTZ-maximal »):
a globally hyperbolic BTZ-extension of a connected `A` whose carrier is `𝔼₀`-maximal is maximal in
the sense of `Causal.AbstractDev.IsMaximal` over `GHExt A`. -/
theorem isMaximal_of_isE0Maximal [ConnectedSpace A] (E : GHExt A) [ConnectedSpace E.N]
    (hE : E0AbsMax.IsE0Maximal E.N) :
    Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt A => (X.N : Type)) (extMor A) E := by
  intro Y f hf
  haveI := connectedSpace_N Y
  have hb : Bijective f := hE Y.N f Y.gh hf.1.isE0Mor hf.1.injective
  obtain ⟨g, hg, hgf, hfg⟩ := isE0Mor_inv_of_bijective hf.1.isE0Mor hb
  have hgb : Bijective g :=
    ⟨LeftInverse.injective (congrFun hfg), RightInverse.surjective (congrFun hgf)⟩
  refine ⟨g, isBTZEmbedding_of_bijective hg hgb, ?_⟩
  show g ∘ Y.ι = E.ι
  rw [← hf.2, ← comp_assoc, hgf, id_comp]

end Bridge

section Main

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

omit [T2Space M] [SecondCountableTopology M] in
/-- `Reg M` is connected when `M` is (`E0LM.isPreconnected_e0RegM`, non-empty by density). -/
theorem connectedSpace_regM : ConnectedSpace (E0LM.e0RegM M) := by
  haveI : Nonempty M := inferInstance
  exact Subtype.connectedSpace ⟨E0LM.dense_e0RegM.nonempty, E0LM.isPreconnected_e0RegM⟩

/-- `M` as a globally hyperbolic BTZ-extension of its regular part. -/
def regExt (hG : (CE M).GloballyHyperbolic) : GHExt (E0LM.e0RegM M) :=
  ⟨E0Mfd.of M, Subtype.val, isBTZEmbedding_regM, hG⟩

/-- **`M ≃ BTZext(Reg M)`** (`BTZ_1.tex:1278`): an `𝔼₀`-maximal globally hyperbolic `M` is a
maximal globally hyperbolic BTZ-extension of `Reg M`. -/
theorem isMaximal_regExt (hG : (CE M).GloballyHyperbolic) (hmax : E0AbsMax.IsE0Maximal M) :
    Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt (E0LM.e0RegM M) => (X.N : Type))
      (extMor (E0LM.e0RegM M)) (regExt hG) := by
  haveI := connectedSpace_regM (M := M)
  haveI : ConnectedSpace (regExt hG).N := ‹ConnectedSpace M›
  exact isMaximal_of_isE0Maximal _ hmax

variable {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
  [ChartedSpace E0Y N] [HasGroupoid N e0Groupoid]

/-- **btzcor:common_reg for `𝔼₀`-maximal manifolds**: two connected globally hyperbolic
`𝔼₀`-maximal `𝔼₀`-manifolds with isomorphic regular parts are isomorphic, by a homeomorphism
extending the given isomorphism. -/
theorem equiv_of_isE0Maximal (hGM : (CE M).GloballyHyperbolic) (hGN : (CE N).GloballyHyperbolic)
    (hM : E0AbsMax.IsE0Maximal M) (hN : E0AbsMax.IsE0Maximal N)
    (φ : E0LM.e0RegM M → E0LM.e0RegM N) (hφ : IsE0Mor φ univ) (hφb : Bijective φ) :
    ∃ F : M ≃ₜ N, IsE0Mor F univ ∧ IsE0Mor F.symm univ ∧
      (F : M → N) ∘ Subtype.val = Subtype.val ∘ φ := by
  haveI := connectedSpace_regM (M := M)
  let EN : GHExt (E0LM.e0RegM M) :=
    ⟨E0Mfd.of N, Subtype.val ∘ φ, isBTZEmbedding_regM.comp (isBTZEmbedding_of_bijective hφ hφb),
      hGN⟩
  haveI : ConnectedSpace EN.N := ‹ConnectedSpace N›
  have hEN := isMaximal_of_isE0Maximal EN hN
  obtain ⟨F, ⟨hF, hFc⟩, hFb⟩ := equivalent_of_isMaximal (isMaximal_regExt hGM hM) hEN
  let F' : M ≃ₜ N := (Equiv.ofBijective F hFb).toHomeomorphOfContinuousOpen
    hF.continuous (isOpenMap_of_isE0Mor hF.isE0Mor)
  obtain ⟨g, hg, hgF, hFg⟩ := isE0Mor_inv_of_bijective hF.isE0Mor hFb
  have hsymm : (F'.symm : N → M) = g := by
    funext y
    have h1 : F (F'.symm y) = y := F'.apply_symm_apply y
    calc F'.symm y = g (F (F'.symm y)) := (congrFun hgF _).symm
      _ = g y := by rw [h1]
  refine ⟨F', hF.isE0Mor, ?_, hFc⟩
  rw [hsymm]
  exact hg

/-- **`btzcor:common_reg`** (unmarked: `𝔼₀` scope with partial inputs, `M`, `N` connected added)
(`BTZ_1.tex:1274–1276`): two globally hyperbolic Cauchy-maximal Cauchy-compact `𝔼₀`-manifolds
whose regular parts are isomorphic are isomorphic — by a homeomorphism which is an `𝔼₀`-morphism
both ways and extends the given isomorphism `Reg M ≃ Reg N`. No `RichardsInput`. -/
theorem common_reg (hGM : (CE M).GloballyHyperbolic) (hGN : (CE N).GloballyHyperbolic)
    (hCM : IsE0CauchyMaximal M) (hCN : IsE0CauchyMaximal N)
    (hKM : E0AbsMax.E0CauchyCompact M) (hKN : E0AbsMax.E0CauchyCompact N)
    (φ : E0LM.e0RegM M → E0LM.e0RegM N) (hφ : IsE0Mor φ univ) (hφb : Bijective φ) :
    ∃ F : M ≃ₜ N, IsE0Mor F univ ∧ IsE0Mor F.symm univ ∧
      (F : M → N) ∘ Subtype.val = Subtype.val ∘ φ := by
  exact equiv_of_isE0Maximal hGM hGN
    ((E0AbsMax.prop_cauchy_abs_max_of_cauchyCompact_e0 hGM hKM).1 hCM)
    ((E0AbsMax.prop_cauchy_abs_max_of_cauchyCompact_e0 hGN hKN).1 hCN) φ hφ hφb

end Main

end BTZCommonReg

end GX
