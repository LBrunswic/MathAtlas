import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend

/-!
# `Causal.Flat.Cla.TameNested` — `Γ\W` tamely embeds in `Γ\Ω` for nested simply connected `W ⊆ Ω`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), Theorem A
(`bthm:caucomp`, l.338–347, reading R1, DEC-43) and the absolute-maximality step [11.i]. No label
is certified here: this module proves the tameness step that `Flat/Classification.lean`'s
`exists_finiteCover_tameEmbedding` (its missing item (3), "tameness") and
`exists_absMax_unipotent_ltp` (`B ↪ B₂` tamely, G3) both need. Line numbers are those of the
**labelled** `papers/barbot/legacy/labeled/GHFspace.tex`.

> In the following statement, a \emph{tame embedding}
> is an isometric embedding inducing an isomorphism between
> fundamental groups. (l.333–335)

> Then, according to \ref{caucomp},
> some finite covering $M'$ of $M$ tamely embeds in some
> model spacetime $M_{1}$. (l.3588–3590)

> Then, since $y_{+} \leq Y_{+}$, $M_{0}$ tamely embedds in
> the quotient $\Gamma_{0}\backslash\Omega$. (l.3666–3667)

The paper never argues the tameness: it is the statement that, for `W ⊆ Ω` two `Γ`-invariant
simply connected open sets (in its uses: `W` the developing image of the universal cover, `Ω`
convex), the map `Γ\W → Γ\Ω`, `[w] ↦ [w]`, is an isometric embedding inducing an isomorphism of
fundamental groups. This module proves it.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d =
ℝ × EuclideanSpace ℝ (Fin d)` has `d` spatial dimensions, so Barbot's `n` is `d + 1`.

## What is proved (no `sorry`)

* **`exists_isTameEmbedding_of_isQuotientOf_le`** — if `W ≤ Ω` are open sets of `𝐌ⁿ`, both
  simply connected, `M'` is a quotient of `W` by `Γ` and `B` a quotient of `Ω` by the same `Γ`
  (`IsQuotientOf`), then some `f : M' → B` is a tame embedding (`IsTameEmbedding d f`: continuous,
  an injective local isometry, bijective on `π₁` at **every** basepoint). The map is built from
  the two projections `π_W : W → M'`, `π_Ω : Ω → B` of the presentations themselves:
  `f (π_W w) = π_Ω w` (well defined and injective because both fibres are `Γ`-orbits; a local
  isometry by descending `π_Ω ∘ incl` along the surjective local isometry `π_W`). Working with
  the presentations' own projections makes `f` a local isometry **for the charts of `M'` and
  `B`**, so the "topological identification only" caveat of `IsQuotientOf.exists_homeomorph`
  (`Flat/Quotient.lean`, SCOPE) does not arise.
* **`bijective_fundamentalGroupMap_of_covers`** (general topology) — for covering maps
  `p₁ : E₁ → X₁`, `p₂ : E₂ → X₂` with simply connected total spaces, an injective continuous
  `ι : E₁ → E₂` and a continuous `f` with `f ∘ p₁ = p₂ ∘ ι`, such that every `p₂`-fibre through
  `ι e` lies in `ι(p₁-fibre of e)`, `f` is bijective on `π₁(X₁, p₁ e)`. *Injective*: lift a loop
  `ℓ` from `e` (`IsCoveringMap.liftPath`); `ι ∘` lift is the `p₂`-lift of `f ∘ ℓ`; `f ∘ ℓ` null
  ⇒ that lift is closed (`liftPath_apply_one_eq_of_homotopicRel`) ⇒ by injectivity of `ι` the
  `p₁`-lift is a loop in the simply connected `E₁` ⇒ `ℓ` null. *Surjective*: lift a loop of `X₂`
  from `ι e` to `e' = ι e₁` with `p₁ e₁ = p₁ e`; any path `c : e → e₁` in `E₁` gives a loop
  `p₁ ∘ c`, and `ι ∘ c` and the lift are homotopic rel endpoints in the simply connected `E₂`,
  so their projections are.
* `isLocalIsometry_opensInclusion` — the inclusion `W → Ω` of nested open sets of `𝐌ⁿ` is a
  local isometry (the charts of both are restrictions of the identity chart).

## Hypothesis checklist

| paper | here |
|---|---|
| `M'` (resp. `M₀`) the quotient of an open domain by `Γ` (l.3592–3594) | ✓ carried: `IsQuotientOf M' Γ W` |
| the target the quotient of a convex open domain `Ω` by the same group (l.3592–3594, l.3666–3667) | ⚠ weakened: `IsQuotientOf B Γ Ω` with `Ω` **simply connected** (convex ⇒ contractible ⇒ simply connected) |
| the domain of `M'` is the developing image of a universal cover (simply connected) | ✓ carried as `SimplyConnectedSpace W` (the developing map is injective there, `bprop:danom`) |
| `W ⊆ Ω` | ✓ carried: `W ≤ Ω` |
| `Γ` acts freely and properly discontinuously (l.1836–1838) | ⚠ weakened: not asked — `IsQuotientOf` already carries covering projections whose fibres are the orbits, and nothing else is used |
| spacetimes GH, Cauchy-complete | ⚠ weakened: not asked (tameness is topological) |

## SCOPE (disclosed)

* No `sorry` and no added hypothesis. The two consumers in `Flat/Classification.lean` still
  need their own constructions (the finite cover `M' = Γ\W` with `ProperlyDiscontinuousSMul`,
  the domain `Ω_{M₂} ⊕ U^⊥`); this module supplies only the tameness once both presentations
  share the group `Γ` and the domains are nested.
* `π₁` bijectivity is proved at every basepoint, as `IsTameEmbedding` asks; no basepoint change
  isomorphism is used.
* `isLocalIsometry_of_comp_right'` is a private copy of `Classification`'s
  `IsLocalIsometry.of_comp_right` (this module cannot import `Classification`, which it serves).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
Classification tameness step (`Flat/Classification.lean:473` item (3), `:2324` G3).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Filter Function

universe u v

variable {d : ℕ}

section Abstract

variable {E₁ E₂ X₁ X₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X₁]
  [TopologicalSpace X₂]

/-- **Bijectivity on `π₁` of a map covered by an injection of simply connected covers.** If
`p₁ : E₁ → X₁` and `p₂ : E₂ → X₂` are covering maps with simply connected total spaces,
`ι : E₁ → E₂` is continuous and injective, `f ∘ p₁ = p₂ ∘ ι`, and every point of the `p₂`-fibre
of `ι e` is `ι e₁` for some `e₁` of the `p₁`-fibre of `e`, then `f` induces a bijection
`π₁(X₁, p₁ e) → π₁(X₂, f (p₁ e))`. -/
theorem bijective_fundamentalGroupMap_of_covers {p₁ : E₁ → X₁} {p₂ : E₂ → X₂}
    (cov₁ : IsCoveringMap p₁) (cov₂ : IsCoveringMap p₂) [SimplyConnectedSpace E₁]
    [SimplyConnectedSpace E₂] (ι : C(E₁, E₂)) (hι : Injective ι) (f : C(X₁, X₂))
    (hf : ∀ e, f (p₁ e) = p₂ (ι e))
    (hfib : ∀ (e : E₁) (e' : E₂), p₂ e' = p₂ (ι e) → ∃ e₁ : E₁, ι e₁ = e' ∧ p₁ e₁ = p₁ e)
    (e : E₁) : Bijective (FundamentalGroup.map f (p₁ e)) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    obtain ⟨ℓ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a)
    have hh : Path.Homotopic (ℓ.map f.continuous) (Path.refl (f (p₁ e))) :=
      Path.Homotopic.Quotient.eq.1 ha
    have h0 : ℓ.toContinuousMap 0 = p₁ e := ℓ.source
    set L := cov₁.liftPath ℓ.toContinuousMap e h0 with hL
    have hLl : p₁ ∘ L = ℓ := cov₁.liftPath_lifts _ _ h0
    have hL0 : L 0 = e := cov₁.liftPath_zero _ _ h0
    have h0' : (f.comp ℓ.toContinuousMap) 0 = p₂ (ι e) := by
      simp [ℓ.source, hf]
    have hιL : ι.comp L = cov₂.liftPath (f.comp ℓ.toContinuousMap) (ι e) h0' := by
      rw [cov₂.eq_liftPath_iff']
      refine ⟨?_, by simp [hL0]⟩
      funext t
      have := congr_fun hLl t
      simp only [comp_apply, ContinuousMap.comp_apply] at this ⊢
      rw [← hf, this]
      rfl
    have hc0 : (ContinuousMap.const unitInterval (f (p₁ e))) 0 = p₂ (ι e) := by simp [hf]
    have hend := cov₂.liftPath_apply_one_eq_of_homotopicRel (γ₀ := f.comp ℓ.toContinuousMap)
      (γ₁ := ContinuousMap.const unitInterval (f (p₁ e))) hh (ι e) h0' hc0
    rw [← hιL, cov₂.liftPath_const] at hend
    have hL1 : L 1 = e := hι hend
    let L' : Path e e := ⟨L, hL0, hL1⟩
    have hhom : Path.Homotopic (L'.map cov₁.continuous) (Path.refl (p₁ e)) :=
      (SimplyConnectedSpace.paths_homotopic L' (Path.refl e)).map ⟨p₁, cov₁.continuous⟩
    have hLℓ : L'.map cov₁.continuous = ℓ := by
      ext t
      exact congr_fun hLl t
    rw [hLℓ] at hhom
    exact Path.Homotopic.Quotient.eq.2 hhom
  · intro a
    obtain ⟨ℓ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a)
    have h0 : ℓ.toContinuousMap 0 = p₂ (ι e) := ℓ.source.trans (hf e)
    set L := cov₂.liftPath ℓ.toContinuousMap (ι e) h0 with hL
    have hLl : p₂ ∘ L = ℓ := cov₂.liftPath_lifts _ _ h0
    have hL0 : L 0 = ι e := cov₂.liftPath_zero _ _ h0
    have hp1 : p₂ (L 1) = p₂ (ι e) := by
      have := congr_fun hLl 1
      simp only [comp_apply] at this
      rw [this, ← hf]
      exact ℓ.target
    obtain ⟨e₁, he₁, hpe₁⟩ := hfib e (L 1) hp1
    let c : Path e e₁ := PathConnectedSpace.somePath e e₁
    let loop : Path (p₁ e) (p₁ e) := (c.map cov₁.continuous).cast rfl hpe₁.symm
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop), ?_⟩
    show Path.Homotopic.Quotient.mk (loop.map f.continuous) = Path.Homotopic.Quotient.mk ℓ
    refine Path.Homotopic.Quotient.eq.2 ?_
    let P₁ : Path (ι e) (L 1) := ⟨ι.comp c.toContinuousMap, by simp, by simp [he₁]⟩
    let P₂ : Path (ι e) (L 1) := ⟨L, hL0, rfl⟩
    have H := ContinuousMap.HomotopicRel.comp_continuousMap (SimplyConnectedSpace.paths_homotopic P₁ P₂)
      ⟨p₂, cov₂.continuous⟩
    have e1 : (loop.map f.continuous).toContinuousMap =
        (ContinuousMap.comp ⟨p₂, cov₂.continuous⟩ P₁.toContinuousMap) := by
      ext t
      simp [loop, P₁, hf]
    have e2 : ℓ.toContinuousMap =
        (ContinuousMap.comp ⟨p₂, cov₂.continuous⟩ P₂.toContinuousMap) := by
      ext t
      exact (congr_fun hLl t).symm
    show (loop.map f.continuous).toContinuousMap.HomotopicRel ℓ.toContinuousMap {0, 1}
    rw [e1, e2]
    exact H

end Abstract

section Maps

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- Descending a local isometry along a surjective local isometry (a private copy of
`Classification`'s `IsLocalIsometry.of_comp_right`, which this module cannot import). -/
private theorem isLocalIsometry_of_comp_right' {q : X → M} {f : M → N}
    (hq : IsLocalIsometry d q) (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) :
    IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

end Maps

/-- The inclusion `W → Ω` of nested open subsets of `𝐌ⁿ` is a local isometry. -/
theorem isLocalIsometry_opensInclusion {W Ω : Opens (Minkowski d)} (hWΩ : W ≤ Ω) :
    IsLocalIsometry d (fun w : W => (⟨w.1, hWΩ w.2⟩ : Ω)) :=
  isLocalIsometry_iff_eventually.2 ⟨continuous_subtype_val.subtype_mk _, fun _ => ⟨1,
    Eventually.of_forall fun _ => by rw [one_smul]; rfl⟩⟩

/-- **`Γ\W` tamely embeds in `Γ\Ω`** (l.3588–3590, l.3666–3667): for nested simply connected
open sets `W ≤ Ω` of `𝐌ⁿ` presenting `M'` and `B` as quotients by the same group `Γ`, the map
`[w] ↦ [w]` is an isometric embedding bijective on every fundamental group. -/
theorem exists_isTameEmbedding_of_isQuotientOf_le {M' : FlatSpacetime.{u} d}
    {B : FlatSpacetime.{v} d} {Γ : Subgroup (isom d)} {W Ω : Opens (Minkowski d)} (hWΩ : W ≤ Ω)
    (hW : IsQuotientOf M' Γ W) (hB : IsQuotientOf B Γ Ω) (hWsc : SimplyConnectedSpace W)
    (hΩsc : SimplyConnectedSpace Ω) : ∃ f : M' → B, IsTameEmbedding d f := by
  obtain ⟨πW, hcW, hlW, hsW, hfW⟩ := hW.quot
  obtain ⟨πΩ, hcΩ, hlΩ, -, hfΩ⟩ := hB.quot
  let ι : W → Ω := fun w => ⟨w.1, hWΩ w.2⟩
  have hlι : IsLocalIsometry d ι := isLocalIsometry_opensInclusion hWΩ
  have hιinj : Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  let f : M' → B := fun x => πΩ (ι (surjInv hsW x))
  have hf : ∀ w, f (πW w) = πΩ (ι w) := by
    intro w
    obtain ⟨γ, hγ, h⟩ := (hfW _ _).1 (surjInv_eq hsW (πW w))
    exact (hfΩ _ _).2 ⟨γ, hγ, h⟩
  have hfπ : f ∘ πW = πΩ ∘ ι := funext hf
  have hlf : IsLocalIsometry d f :=
    isLocalIsometry_of_comp_right' hlW hsW (hfπ ▸ hlΩ.comp hlι)
  have hinj : Injective f := by
    intro x y hxy
    obtain ⟨w, rfl⟩ := hsW x
    obtain ⟨w', rfl⟩ := hsW y
    rw [hf, hf] at hxy
    obtain ⟨γ, hγ, h⟩ := (hfΩ _ _).1 hxy
    exact (hfW _ _).2 ⟨γ, hγ, h⟩
  refine ⟨f, hlf.continuous, ⟨hlf, hinj⟩, fun x => ?_⟩
  obtain ⟨e, rfl⟩ := hsW x
  haveI := hWsc
  haveI := hΩsc
  refine bijective_fundamentalGroupMap_of_covers hcW hcΩ ⟨ι, hlι.continuous⟩ hιinj
    ⟨f, hlf.continuous⟩ hf (fun e e' he' => ?_) e
  obtain ⟨γ, hγ, h⟩ := (hfΩ _ _).1 he'.symm
  have hmem : (e' : Minkowski d) ∈ W := by
    have h' : (γ • (e : Minkowski d)) = e' := h
    have hγe : γ • (e : Minkowski d) ∈ (W : Set (Minkowski d)) := by
      rw [← hW.inv γ hγ]
      exact ⟨e.1, e.2, rfl⟩
    rw [← h']
    exact hγe
  exact ⟨⟨e'.1, hmem⟩, rfl, ((hfW _ _).2 ⟨γ, hγ, h⟩).symm⟩

end Causal.Flat.Cla
