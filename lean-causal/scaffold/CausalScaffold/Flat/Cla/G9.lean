import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.G9` — a Cauchy-compact linear twisted product over a model is finitely covered by a model of Theorem B

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), proof of
Theorem B (`bthm:cauclo`, l.353–359; proof l.3536–3548), gap **G9** of `docs/BARBOT-THEOREMS.md`
§6. No label is certified here (`bthm:cauclo` is assembled in `Flat/Classification.lean`); this
module serves `cauclo_from_embedding`'s steps (3)–(4). Line numbers are those of the **labelled**
`papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's `𝐌ⁿ` has total dimension `n`; the library's
`Minkowski d` has `d` spatial dimensions, so `n = d + 1`.

> Up to finite coverings,
> every maximal Cauchy-compact globally hyperbolic flat spacetime is isometric
> to a translation spacetime, a Misner spacetime, or
> the twisted product of a standart spacetime (Cauchy-compact
> Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

> It follows that nontrivial linear twisted products
> destroy Cauchy-compactness, thus the ``up to linear twisted
> products'' appearing in Theorem \ref{caucomp} can be erased
> in the Cauchy-compact version \ref{cauclo}.
> As observed previously, unipotent spacetimes cannot
> be Cauchy-compact; thus, together with their finite coverings, they
> disappear in the Cauchy-compact version. (l.3542–3548)

> Unipotent spacetimes have \emph{never} closed Cauchy hypersurfaces,
> since the $\mathcal A$-invariant coordinate
> $y$ defines a submersion from
> the Cauchy hypersurface into ${\mathbb R}$. (l.744–746)

## What is proved

* `Causal.Flat.Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact` — **the dispatched statement**
  (G9): if `B` is GH and Cauchy-compact, `f : M' → B` a surjective isometric embedding, and `B` a
  linear twisted product over a model `M₁` of Theorem A (translation, Misner, unipotent or the
  central extension (b)), then some finite cover `M₁'` of `M'` is a translation spacetime, a
  Misner spacetime, or a torus product (a). It rests on **one** tagged `sorry`,
  `false_of_cauchyCompact_of_fixed_pair` (the residual case of G9d's (NE), below); G9a, G9b, G9c
  and the rest of G9d are proved.
* `fg_and_nonelementary_of_cauchyCompact` — **G9d's geometric input**, assembled: **(FG) proved**
  (`fg_of_isQuotientOf_cauchyCompact`, sorry-free: the lift of the compact Cauchy surface is
  connected by lifting the deformation of the splitting, `isPreconnected_preimage_of_splitting`,
  then an elementary Švarc–Milnor, `fg_of_isPreconnected_of_properlyDiscontinuous`); **(NE)
  reduced**, sorry-free (`not_hasGlobalFixedPoint_of_relIndex_ne_zero`: a fixed timelike vector of
  a finite-index `L(Γ')` averages to one of `L(Γ)`; a fixed point of `𝒮` has a finite orbit, fixed
  pointwise by the normal core, of one point, of three or more — a fixed timelike `n₁ + n₂` — or of
  an invariant pair) to the pair case, the module's one `sorry`.
* `isCompact_image_of_isQuotientOf` — **the obstruction to Cauchy-compactness**, sorry-free: if
  `M = Γ\Ω` is causal with a compact Cauchy surface `K`, and `F` is a continuous `Γ`-invariant
  function on `𝐌ⁿ` constant along a causal direction `v`, then `F(Ω)` is compact. This is the
  common core of Barbot's two sentences l.3542 and l.744.
* `not_cauchyCompact_of_isUnipotentSpacetime` — **G9b, "unipotent spacetimes cannot be
  Cauchy-compact"** (l.744–746, l.3546–3547), sorry-free, for a GH unipotent spacetime: the
  `A`-invariant coordinate `y` is constant along the null direction `∂ₓ`, so by the obstruction
  `y(Ω) = ]α, β[` would be compact. Barbot's "submersion" is not needed. Its mirror form
  `not_cauchyCompact_of_refl_unipotent`, through the spatial reflection `R₀`.
* `perp_eq_zero_of_cauchyCompact` — **G9a, first half, "nontrivial linear twisted products
  destroy Cauchy-compactness"** (l.3542–3543), sorry-free: for LTP data `(Γ, Ω, ι)` of a GH
  Cauchy-compact `B`, `U^⊥ = 0`.
* **G9a, second half — the frame transport**, sorry-free: with `U^⊥ = 0`, `d₁ = d`
  (`eq_of_perp`), `ι` is bijective and descends to a homeomorphism `e : M₁ ≃ B`
  (`exists_homeomorph_of_isLTPData`). `det L(ι) = ±1` (`det_lin_eq_one_or`): for `+1`, `ι` is an
  isometry (`exists_isom_of_det_one`) and `e` an isometric homeomorphism; for `−1`, `ι ∘ R₀` is one
  (`exists_isom_of_det_neg_one`), `e` is locally of type `R₀` (`IsLocalAIso`), and
  `B = (R₀ G R₀)\R₀(Ω₁)` for every presentation `M₁ = G\Ω₁` (`isQuotientOf_refl`). The translation,
  Misner and central-extension families are `R₀`-conjugation stable (`isTranslationSpacetime_refl`,
  `isMisnerSpacetime_refl`, `isCHCentralExtensionOf_refl`: `𝒩`, `E`, `L(Γ)`, its discreteness and
  fixed points, the loxodromic repulsive points, `Λ(Γ)` and `Ω^±(Λ(Γ))` are all equivariant under
  `R₀`). In `𝐌¹` the case `−1` does not occur (`det_lin_eq_one_zero`).
* **G9d, the reduction** `exists_torusProduct_cover_of_fg` (sorry-free, on the named external
  `hSel`): for family (b) with `Γ` finitely generated and every finite-index `L(Γ')` without global
  fixed point, Selberg (`exists_finiteIndex_torsionFree_linOf`) gives the torsion-free `Γ'`;
  `Γ'\Ω` is a flat spacetime finitely covering `B` (`exists_finiteCover_of_le`: the action of an
  `IsQuotientOf` presentation is free and properly discontinuous, the intermediate quotient covers,
  its fibres are images of `Γ ⧸ Γ'`), and family (b) passes to `Γ'` (`Λ(Γ') = Λ(Γ)`,
  `span 𝒩(Γ') = span 𝒩(Γ)` by powers `tᵐ ∈ Γ'`, discreteness by inclusion), so `Γ'\Ω` is (a).
* G9c, the transport along `f` (sorry-free): a bijective local isometry is a homeomorphism whose
  inverse is a local isometry (`homeomorphOfBijective`, `isLocalIsometry_homeomorphOfBijective_symm`);
  `IsQuotientOf` and the families transport along it; a finite cover composed with an isometric
  homeomorphism is a finite cover; a homeomorphism is a covering map.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` maximal (Theorem B) | ⚠ weakened: not assumed for `B` — not needed: G9a, G9b and G9d hold for any Cauchy-compact GH LTP over a model |
| `M` Cauchy-compact GH | ✓ carried, on `B` (`hGH`, `hC`) |
| `M` finitely covered by a space embedded in an LTP (Theorem A) | ✓ carried as `f` surjective (after [11.ii]) and `hltp` |
| "π₁ finitely generated" (DEC-44, for family (b) → (a)) | not assumed: **proved** from Cauchy-compactness (`fg_of_isQuotientOf_cauchyCompact`); the reduction `exists_torusProduct_cover_of_fg` carries it as `Γ.FG` |
| Selberg's lemma (DEC-36, DEC-44) | ✓ carried as the named external `hSel` |

## SCOPE (disclosed)

`false_of_cauchyCompact_of_fixed_pair` carries the one `sorry`: for a GH Cauchy-compact
`B = Γ\Ω^±(Λ(Γ))` of family (b), no finite-index `N ≤ Γ` fixes (in `L`) two distinct points of `𝒮`
whose pair `L(Γ)` preserves — the elementary-loxodromic case of (NE) (Barbot: `L(Γ)` acts
cocompactly on some `𝐇ᵏ`, `k ≥ 2`; equivalently `Γ` virtually `ℤ^{1+dim E}`, `dim E ≤ d − 2`,
cannot act cocompactly on the lifted Cauchy surface). It is a special case of (NE), hence true.
(FG) and every other case of (NE) are proved; everything downstream is proved. Copies, kept
`private`: Classification's `isCancelSMul_of_isCoveringMap` / `properlyDiscontinuousSMul_of_…`,
FiniteCover's sheet criterion, Lox.RestrictLimitSet's `repJ_eq_of_relIndex_ne_zero` (this module
may import none of them).

**Finding** (for the plan of G9d, not for the paper): "no global fixed point on `𝐇̄`" does **not**
pass to finite-index subgroups in general — in `SO₀(1, 2)` the infinite dihedral group of a boost
and a half-turn exchanging its two null directions has no global fixed point, while its index-2
cyclic subgroup fixes two points of `𝒮`. For G9d it must come from Cauchy-compactness (NE).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace Causal Causal.Flat

universe u

/-! ## G9c — transport along a bijective local isometry -/

section Transport

variable {d : ℕ} {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace Y] [ChartedSpace (Minkowski d) Y]
  [TopologicalSpace Z] [ChartedSpace (Minkowski d) Z]

omit [ChartedSpace (Minkowski d) X] [ChartedSpace (Minkowski d) Y] in
/-- **A homeomorphism is a covering map** (one sheet over `univ`). -/
theorem isCoveringMap_homeomorph (e : X ≃ₜ Y) : IsCoveringMap e := fun y =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := PUnit.{1}) ⟨inferInstance, univ, mem_univ y, isOpen_univ, isOpen_univ,
      (((Homeomorph.Set.univ X).trans e).trans (Homeomorph.Set.univ Y).symm).trans
        (Homeomorph.prodPUnit _).symm, fun _ => rfl⟩

/-- **Cancelling a local isometry on the left, for a continuous map** (as
`Classification`'s `IsLocalIsometry.of_comp_left_of_continuous`, which this module cannot
import): if `h ∘ g` and `h` are local isometries and `g` is continuous, `g` is a local isometry. -/
theorem isLocalIsometry_of_comp_left_of_continuous {g : X → Y} {h : Y → Z}
    (hh : IsLocalIsometry d h) (hgc : Continuous g) (hhg : IsLocalIsometry d (h ∘ g)) :
    IsLocalIsometry d g := by
  obtain ⟨-, hhg'⟩ := isLocalIsometry_iff_eventually.1 hhg
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hgc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhg' x
  obtain ⟨g₂, hg₂⟩ := hh' (g x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hgc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **A bijective local isometry, as a homeomorphism** (a local isometry is open). -/
noncomputable def homeomorphOfBijective {f : X → Y} (hf : IsLocalIsometry d f) (hb : Bijective f) :
    X ≃ₜ Y :=
  (IsHomeomorph.mk hf.continuous hf.isOpenMap hb).homeomorph f

@[simp] theorem coe_homeomorphOfBijective {f : X → Y} (hf : IsLocalIsometry d f)
    (hb : Bijective f) : ⇑(homeomorphOfBijective hf hb) = f := rfl

/-- **The inverse of a bijective local isometry is a local isometry.** -/
theorem isLocalIsometry_homeomorphOfBijective_symm {f : X → Y} (hf : IsLocalIsometry d f)
    (hb : Bijective f) : IsLocalIsometry d (homeomorphOfBijective hf hb).symm := by
  refine isLocalIsometry_of_comp_left_of_continuous hf (homeomorphOfBijective hf hb).symm.continuous ?_
  have : f ∘ (homeomorphOfBijective hf hb).symm = id := by
    funext y
    have := (homeomorphOfBijective hf hb).apply_symm_apply y
    rwa [coe_homeomorphOfBijective] at this
  rw [this]
  exact isLocalIsometry_id

/-- **A finite cover composed with an isometric homeomorphism is a finite cover.** -/
theorem isFiniteCover_homeomorph_comp {q : Z → X} (hq : IsFiniteCover d q) (e : X ≃ₜ Y)
    (he : IsLocalIsometry d e) : IsFiniteCover d (e ∘ q) := by
  refine ⟨hq.1.homeomorph_comp e, he.comp hq.2.1, fun y => ?_⟩
  have : (e ∘ q) ⁻¹' {y} = q ⁻¹' {e.symm y} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, comp_apply]
    exact ⟨fun h => by rw [← h, e.symm_apply_apply], fun h => by rw [h, e.apply_symm_apply]⟩
  rw [this]
  exact hq.2.2 _

/-- **The identity is a finite cover.** -/
theorem isFiniteCover_id : IsFiniteCover d (id : X → X) :=
  ⟨isCoveringMap_homeomorph (Homeomorph.refl X), isLocalIsometry_id, fun y => by
    simp⟩

/-- **`IsQuotientOf` transports along an isometric homeomorphism.** -/
theorem isQuotientOf_homeomorph {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf X Γ Ω) (e : X ≃ₜ Y) (he : IsLocalIsometry d e) : IsQuotientOf Y Γ Ω := by
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := hq.quot
  refine ⟨hq.inv, e ∘ π, hcov.homeomorph_comp e, he.comp hloc, e.surjective.comp hsurj,
    fun p q => ?_⟩
  simp only [comp_apply, e.injective.eq_iff]
  exact hfib p q

end Transport

section Families

variable {d : ℕ}

/-- **Translation spacetimes transport along an isometric homeomorphism.** -/
theorem isTranslationSpacetime_homeomorph {M N : FlatSpacetime.{u} d} (e : M ≃ₜ N)
    (he : IsLocalIsometry d e) (h : IsTranslationSpacetime M) : IsTranslationSpacetime N := by
  obtain ⟨φ, Λ, hΛ, hq⟩ := h
  exact ⟨φ, Λ, hΛ, isQuotientOf_homeomorph hq e he⟩

/-- **Misner spacetimes transport along an isometric homeomorphism.** -/
theorem isMisnerSpacetime_homeomorph {M N : FlatSpacetime.{u} (d + 1)} (e : M ≃ₜ N)
    (he : IsLocalIsometry (d + 1) e) (h : IsMisnerSpacetime M) : IsMisnerSpacetime N := by
  obtain ⟨φ, L, hL, hs, hq | hq⟩ := h
  · exact ⟨φ, L, hL, hs, Or.inl (isQuotientOf_homeomorph hq e he)⟩
  · exact ⟨φ, L, hL, hs, Or.inr (isQuotientOf_homeomorph hq e he)⟩

/-- The Misner family in every dimension (`Classification`'s `IsMisnerFamily` unfolded),
transported. -/
theorem misnerFamily_homeomorph : ∀ {d : ℕ} {M N : FlatSpacetime.{u} d} (e : M ≃ₜ N),
    IsLocalIsometry d e →
    (match d, M with
      | 0, _ => False
      | _ + 1, M => IsMisnerSpacetime M) →
    (match d, N with
      | 0, _ => False
      | _ + 1, N => IsMisnerSpacetime N)
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, _, e, he, h => isMisnerSpacetime_homeomorph e he h

end Families

/-! ## The obstruction to Cauchy-compactness, and G9b -/

section Obstruction

variable {d : ℕ}

/-- **The obstruction to Cauchy-compactness** (the common core of l.3542–3543 and l.744–746).
Let `M = Γ\Ω` be causal, with a compact Cauchy surface `K`, and `F : 𝐌ⁿ → ℝ` continuous,
`Γ`-invariant on `Ω` and constant along a nonzero future causal direction `v`. Then `F(Ω)` is
compact: it is the image of `K` under the function `F` descends to, because every `v`-line through
a point of `Ω` meets the lift of `K` (a Cauchy surface of `Ω`, `isCauchySurface_preimage`, read in
`𝐌ⁿ` through `isCauchySurfaceOn_iff`). -/
theorem isCompact_image_of_isQuotientOf {M : FlatSpacetime.{u} d}
    (hcaus : (flatCausality d M).IsCausal) {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf M Γ Ω) {K : Set M} (hK : (flatCausality d M).IsCauchySurface K)
    (hKc : IsCompact K) {F : Minkowski d → ℝ} (hF : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), F (γ • p) = F p) {v : Minkowski d}
    (hv : IsFutureCausal v) (hv0 : v ≠ 0)
    (hline : ∀ (p : Minkowski d) (s : ℝ), F (p + s • v) = F p) :
    IsCompact (F '' (Ω : Set (Minkowski d))) := by
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := hq.quot
  have hπq : IsQuotientMap π := hloc.isOpenMap.isQuotientMap hloc.continuous hsurj
  -- the function `F` descends to
  set G : M → ℝ := fun m => F (surjInv hsurj m).1 with hGdef
  have hG : ∀ x : Ω, G (π x) = F x := by
    intro x
    obtain ⟨γ, hγ, hγx⟩ := (hfib (surjInv hsurj (π x)) x).1 (surjInv_eq hsurj (π x))
    simp only [hGdef]
    rw [← hγx, hinv γ hγ _ (surjInv hsurj (π x)).2]
  have hGc : Continuous G := by
    rw [hπq.continuous_iff]
    have : G ∘ π = F ∘ Subtype.val := funext hG
    rw [this]
    exact hF.comp continuous_subtype_val
  -- the lifted Cauchy surface, read in `𝐌ⁿ`
  have hpre := isCauchySurface_preimage hcov hloc hcaus hK
  have hSΩ : Subtype.val '' (π ⁻¹' K) ⊆ (Ω : Set (Minkowski d)) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSC : (minkowski d).IsCauchySurfaceOn Ω (Subtype.val '' (π ⁻¹' K)) := by
    rw [FlatQuotient.isCauchySurfaceOn_iff Ω hSΩ, preimage_image_eq _ Subtype.val_injective]
    exact hpre
  have himg : F '' (Ω : Set (Minkowski d)) = G '' K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, x, hxK, hx⟩ := exists_mem_line_of_isCauchySurfaceOn hSC hz hv hv0
      exact ⟨π x, hxK, by rw [hG, hx, hline]⟩
    · rintro ⟨m, -, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj m
      exact ⟨x, x.2, (hG x).symm⟩
  rw [himg]
  exact hKc.image hGc

/-- **G9b: a GH unipotent spacetime is not Cauchy-compact** (l.744–746, l.3546–3547). In the
frame `φ`, the `A`-invariant coordinate `y = nullY ∘ φ⁻¹` is `Γ`-invariant
(`nullY_unipAction`) and constant along the null direction `φ_*(1, e₀)` (`∂ₓ`), so by
`isCompact_image_of_isQuotientOf` the open interval `y(Ω) = ]α, β[` would be compact, hence
clopen, hence `ℝ`. -/
theorem not_cauchyCompact_of_isUnipotentSpacetime {M : FlatSpacetime.{u} (d + 1)} (hGH : GH M)
    (hU : IsUnipotentSpacetime M) : ¬ CauchyCompact M := by
  rintro ⟨K, hK, hKc, -⟩
  obtain ⟨φ, ℓ, α, β, L, Γ, -, hcomp, hΓ, -, hq⟩ := hU
  set F : Minkowski (d + 1) → ℝ := fun p => nullY (φ⁻¹ • p) with hFdef
  set v₀ : Minkowski (d + 1) := (1, EuclideanSpace.single 0 1) with hv₀def
  have hv₀ : IsFutureCausal v₀ := ⟨zero_le_one, by simp [minkQ, v₀]⟩
  have hv₀0 : v₀ ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
  have hFc : Continuous F := continuous_nullY.comp (continuous_const_smul _)
  have hinv : ∀ γ ∈ frameConj φ Γ, ∀ p ∈ (isomImage φ (unipDomain α β) : Set (Minkowski (d + 1))),
      F (γ • p) = F p := by
    intro γ' hγ' p _
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    obtain ⟨t, -, ht⟩ := hΓ γ hγ
    simp only [hFdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul, inv_smul_smul, ht,
      nullY_unipAction]
  have hline : ∀ (p : Minkowski (d + 1)) (s : ℝ), F (p + s • linOf φ v₀) = F p := by
    intro p s
    have hp : p + s • linOf φ v₀ = φ • (φ⁻¹ • p + s • v₀) := by
      rw [isom_smul_add_smul, smul_inv_smul]
    simp only [hFdef, hp, inv_smul_smul]
    simp only [nullY, hv₀def, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst,
      PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul,
      mul_one]
    ring
  have hcpt := isCompact_image_of_isQuotientOf hGH.1 hq hK hKc hFc hinv
    (lorentz.isFutureCausal_apply (linOf_mem φ) hv₀) ((linOf φ).map_ne_zero_iff.2 hv₀0) hline
  have himg : F '' (isomImage φ (unipDomain α β) : Set (Minkowski (d + 1))) =
      {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [coe_isomImage] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simp only [hFdef, inv_smul_smul]
      exact hq
    · intro hy
      have hn : nullY ((-(√2 * y), 0) : Minkowski (d + 1)) = y := by
        simp only [nullY, PiLp.zero_apply, zero_sub, neg_neg]
        field_simp
      refine ⟨φ • ((-(√2 * y), 0) : Minkowski (d + 1)), ?_, ?_⟩
      · rw [SetLike.mem_coe, smul_mem_isomImage]
        show α < (nullY _ : EReal) ∧ (nullY _ : EReal) < β
        rw [hn]
        exact hy
      · simp only [hFdef, inv_smul_smul]
        exact hn
  rw [himg] at hcpt
  have hopen : IsOpen {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} :=
    (isOpen_lt continuous_const continuous_coe_real_ereal).inter
      (isOpen_lt continuous_coe_real_ereal continuous_const)
  obtain ⟨y₀, hy₀⟩ := EReal.lt_iff_exists_real_btwn.1 hcomp.1
  rcases isClopen_iff.1 ⟨hcpt.isClosed, hopen⟩ with h | h
  · have hmem : y₀ ∈ {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} := hy₀
    rw [h] at hmem
    exact hmem
  · rw [h] at hcpt
    exact noncompact_univ ℝ hcpt

/-- The unipotent family in every dimension (`Classification`'s `IsUnipotentFamily` unfolded) is
never Cauchy-compact when GH. -/
theorem not_cauchyCompact_of_unipotentFamily : ∀ {d : ℕ} {M : FlatSpacetime.{u} d}, GH M →
    (match d, M with
      | 0, _ => False
      | _ + 1, M => IsUnipotentSpacetime M) → ¬ CauchyCompact M
  | 0, _, _, h => h.elim
  | _ + 1, _, hGH, h => not_cauchyCompact_of_isUnipotentSpacetime hGH h

/-- The `U^⊥`-component of `ι x + w` is `w`, for `w ∈ U^⊥`. -/
theorem split_snd_apply_add {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (x : Minkowski d₁)
    {w : Minkowski d} (hw : w ∈ ι.perp) : ((ι.split (ι x + w)).2 : Minkowski d) = w := by
  show ι x + w - ι (ι.retract (ι x + w)) = w
  rw [ι.retract_apply_add x hw, add_sub_cancel_left]

/-- **G9a, first half: a nontrivial linear twisted product is never Cauchy-compact**
(l.3542–3543, "nontrivial linear twisted products destroy Cauchy-compactness"). For LTP data
`(Γ, Ω, ι)` of a GH Cauchy-compact `B`, `U^⊥ = 0`. The function `F p = minkQ(P_{U^⊥} p)` (the
squared euclidean norm of the `U^⊥`-component of the splitting) is `Γ`-invariant
(`Restricts.split_smul`, `L(γ)` preserving `minkQ`), constant along the timelike `ι_*(1, 0)`, and
unbounded on `Ω` as soon as some `w ∈ U^⊥` is nonzero (`Ω + U^⊥ = Ω`: `F(ι(q p) + c w) = c² Q(w)`),
against `isCompact_image_of_isQuotientOf`. -/
theorem perp_eq_zero_of_cauchyCompact {B : FlatSpacetime.{u} d} (hGH : GH B)
    (hC : CauchyCompact B) {d₁ : ℕ} {M₁ : Type*} [TopologicalSpace M₁]
    [ChartedSpace (Minkowski d₁) M₁] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    {ι : AffineMinkEmbedding d₁ d} (hd : IsLTPData B M₁ Γ Ω ι) :
    ∀ w ∈ ι.perp, w = 0 := by
  obtain ⟨K, hK, hKc, -⟩ := hC
  set F : Minkowski d → ℝ := fun p => minkQ ((ι.split p).2 : Minkowski d) with hFdef
  have hFc : Continuous F :=
    continuous_minkQ.comp (continuous_subtype_val.comp (continuous_snd.comp ι.split.continuous))
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), F (γ • p) = F p := by
    intro γ hγ p _
    obtain ⟨g, hg⟩ := hd.restricts γ hγ
    simp only [hFdef, hg.split_smul]
    exact lorentz.minkQ_apply γ.2 _
  set v : Minkowski d := ι.lin (1, 0) with hvdef
  have hv : IsFutureCausal v := ⟨hd.orthochronous.le, by rw [hvdef, ι.minkQ_lin_timeVec]; norm_num⟩
  have hv0 : v ≠ 0 := fun h => by
    have h1 : 0 < v.1 := hd.orthochronous
    rw [h] at h1
    exact lt_irrefl _ h1
  have hline : ∀ (p : Minkowski d) (s : ℝ), F (p + s • v) = F p := by
    intro p s
    have hw := ι.sub_apply_retract_mem_perp p
    have hp : p + s • v = ι (ι.retract p + s • ((1, 0) : Minkowski d₁)) + (p - ι (ι.retract p)) := by
      rw [ι.apply_add, map_smul, hvdef]; abel
    simp only [hFdef]
    rw [hp, split_snd_apply_add ι _ hw]
    rfl
  have hcpt := isCompact_image_of_isQuotientOf hGH.1 hd.quotient hK hKc hFc hinv hv hv0 hline
  obtain ⟨R, hR⟩ := hcpt.bddAbove
  intro w hw
  by_contra hne
  have hQ := ι.minkQ_pos_of_mem_perp hw hne
  obtain ⟨π, -, -, hsurj, -⟩ := hd.quotient.quot
  obtain ⟨⟨p, hp⟩, -⟩ := hsurj (Classical.arbitrary B)
  set c : ℝ := max 1 ((|R| + 1) / minkQ w) with hcdef
  have hq0 : ι (ι.retract p) + c • w ∈ (Ω : Set (Minkowski d)) := by
    have h1 := hd.perp_invariant _ (ι.neg_mem_perp (ι.sub_apply_retract_mem_perp p)) p hp
    rw [show p + -(p - ι (ι.retract p)) = ι (ι.retract p) by abel] at h1
    exact hd.perp_invariant _ (ι.smul_mem_perp c hw) _ h1
  have hval : F (ι (ι.retract p) + c • w) = c ^ 2 * minkQ w := by
    simp only [hFdef]
    rw [split_snd_apply_add ι _ (ι.smul_mem_perp c hw), minkQ_smul]
  have hle := hR ⟨_, hq0, rfl⟩
  rw [hval] at hle
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc2 : (|R| + 1) / minkQ w ≤ c := le_max_right _ _
  have hc3 : |R| + 1 ≤ c * minkQ w := (div_le_iff₀ hQ).1 hc2
  have hc4 : c * minkQ w ≤ c ^ 2 * minkQ w := by
    have : c * minkQ w * 1 ≤ c * minkQ w * c :=
      mul_le_mul_of_nonneg_left hc1 (mul_nonneg (by linarith) hQ.le)
    nlinarith
  linarith [le_abs_self R]

end Obstruction

section Reflection

variable {n : ℕ}

/-- The reflection of `ℝ^{n+1}` in its first coordinate. -/
noncomputable def coordRefl (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 fun i => if i = 0 then -x i else x i
  map_add' x y := by
    ext i; simp only [PiLp.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem coordRefl_apply (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    coordRefl n x i = if i = 0 then -x i else x i := rfl

@[simp] theorem coordRefl_apply_zero (x : EuclideanSpace ℝ (Fin (n + 1))) :
    coordRefl n x 0 = -x 0 := by rw [coordRefl_apply, if_pos rfl]

@[simp] theorem coordRefl_apply_succ (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    coordRefl n x i.succ = x i.succ := by rw [coordRefl_apply, if_neg (Fin.succ_ne_zero i)]

@[simp] theorem coordRefl_coordRefl (x : EuclideanSpace ℝ (Fin (n + 1))) :
    coordRefl n (coordRefl n x) = x := by
  ext i; rw [coordRefl_apply, coordRefl_apply]; split_ifs <;> simp_all

theorem norm_coordRefl (x : EuclideanSpace ℝ (Fin (n + 1))) : ‖coordRefl n x‖ = ‖x‖ := by
  have h := norm_sq_split (coordRefl n x)
  rw [coordRefl_apply_zero] at h
  simp only [coordRefl_apply_succ] at h
  rw [neg_sq, ← norm_sq_split] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem det_coordRefl : LinearMap.det (coordRefl n) = -1 := by
  classical
  set b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (coordRefl n) =
      Matrix.diagonal (fun i => if i = 0 then -1 else 1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [b, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordRefl_apply]
    by_cases hij : i = j
    · subst hij; split_ifs <;> simp_all
    · rw [if_neg hij]; split_ifs <;> simp [Ne.symm hij]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

/-- **The spatial reflection `R₀ : (t, x) ↦ (t, x')`, `x'₀ = −x₀`**, of `𝐌^{n+2}`. -/
noncomputable def spaceReflL (n : ℕ) : Minkowski (n + 1) →ₗ[ℝ] Minkowski (n + 1) :=
  LinearMap.prodMap LinearMap.id (coordRefl n)

@[simp] theorem spaceReflL_apply (p : Minkowski (n + 1)) :
    spaceReflL n p = (p.1, coordRefl n p.2) := rfl

theorem spaceReflL_spaceReflL (p : Minkowski (n + 1)) : spaceReflL n (spaceReflL n p) = p := by
  simp

/-- `R₀` as a linear involution. -/
noncomputable def spaceRefl (n : ℕ) : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1) :=
  LinearEquiv.ofInvolutive (spaceReflL n) spaceReflL_spaceReflL

@[simp] theorem spaceRefl_apply (p : Minkowski (n + 1)) :
    spaceRefl n p = (p.1, coordRefl n p.2) := rfl

@[simp] theorem spaceRefl_spaceRefl (p : Minkowski (n + 1)) : spaceRefl n (spaceRefl n p) = p := by
  simp

theorem spaceRefl_symm : (spaceRefl n).symm = spaceRefl n :=
  LinearEquiv.ext fun p => by
    rw [LinearEquiv.symm_apply_eq, spaceRefl_spaceRefl]

theorem minkQ_spaceRefl (p : Minkowski (n + 1)) : minkQ (spaceRefl n p) = minkQ p := by
  simp [minkQ, norm_coordRefl]

theorem det_spaceRefl : LinearMap.det (spaceRefl n : Minkowski (n + 1) →ₗ[ℝ] _) = -1 := by
  show LinearMap.det (spaceReflL n) = -1
  rw [spaceReflL, LinearMap.det_prodMap, LinearMap.det_id, det_coordRefl, one_mul]

theorem continuous_spaceRefl : Continuous (spaceRefl n) := by
  have : (spaceRefl n : Minkowski (n + 1) → Minkowski (n + 1)) = fun p => (p.1, coordRefl n p.2) :=
    funext spaceRefl_apply
  rw [this]
  exact continuous_fst.prodMk ((LinearMap.continuous_of_finiteDimensional (coordRefl n)).comp
    continuous_snd)

theorem norm_spaceRefl (p : Minkowski (n + 1)) : ‖spaceRefl n p‖ = ‖p‖ := by
  simp [Prod.norm_def, norm_coordRefl]

/-- **`R₀ L R₀ ∈ SO₀(1, n+1)`** for `L ∈ SO₀(1, n+1)`. -/
theorem conj_spaceRefl_mem_lorentz {L : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)}
    (hL : L ∈ lorentz (n + 1)) :
    (spaceRefl n).trans (L.trans (spaceRefl n)) ∈ lorentz (n + 1) := by
  refine mem_lorentz_of (fun v => ?_) ?_ ?_
  · simp only [LinearEquiv.trans_apply]
    rw [minkQ_spaceRefl, lorentz.minkQ_apply hL, minkQ_spaceRefl]
  · have h1 : spaceRefl n (timeUnit (n + 1)) = timeUnit (n + 1) := by
      simp [timeUnit]
    have h2 := lorentz.isFutureTimelike_apply hL (v := timeUnit (n + 1)) ⟨by simp [timeUnit],
      by simp⟩
    simp only [LinearEquiv.trans_apply, h1, spaceRefl_apply]
    exact h2.1
  · rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.det_comp, LinearMap.det_comp,
      det_spaceRefl, lorentz.det_eq_one hL]
    norm_num

/-- `R₀` as an affine equivalence. -/
noncomputable abbrev reflAff (n : ℕ) : Minkowski (n + 1) ≃ᵃ[ℝ] Minkowski (n + 1) :=
  (spaceRefl n).toAffineEquiv

theorem reflConj_mem (g : isom (n + 1)) :
    (reflAff n).trans ((g : Minkowski (n + 1) ≃ᵃ[ℝ] Minkowski (n + 1)).trans (reflAff n)) ∈
      isom (n + 1) := by
  rw [mem_isom_iff]
  exact conj_spaceRefl_mem_lorentz g.2

/-- **Conjugation by `R₀`**, `g ↦ R₀ g R₀`, an automorphism of `Isom(𝐌ⁿ)`. -/
noncomputable def reflConj (n : ℕ) : isom (n + 1) →* isom (n + 1) where
  toFun g := ⟨_, reflConj_mem g⟩
  map_one' := Subtype.ext (AffineEquiv.ext fun p => by
    show spaceRefl n (spaceRefl n p) = p
    exact spaceRefl_spaceRefl p)
  map_mul' a b := Subtype.ext (AffineEquiv.ext fun p => by
    show spaceRefl n ((a : Minkowski (n + 1) ≃ᵃ[ℝ] _) ((b : Minkowski (n + 1) ≃ᵃ[ℝ] _)
        (spaceRefl n p))) =
      spaceRefl n ((a : Minkowski (n + 1) ≃ᵃ[ℝ] _) (spaceRefl n (spaceRefl n
        ((b : Minkowski (n + 1) ≃ᵃ[ℝ] _) (spaceRefl n p)))))
    rw [spaceRefl_spaceRefl])

theorem reflConj_smul (g : isom (n + 1)) (p : Minkowski (n + 1)) :
    reflConj n g • p = spaceRefl n (g • spaceRefl n p) := rfl

@[simp] theorem reflConj_reflConj (g : isom (n + 1)) : reflConj n (reflConj n g) = g :=
  Subtype.ext (AffineEquiv.ext fun p => by
    show spaceRefl n (spaceRefl n (g • spaceRefl n (spaceRefl n p))) = g • p
    rw [spaceRefl_spaceRefl, spaceRefl_spaceRefl])

theorem linOf_reflConj (g : isom (n + 1)) (v : Minkowski (n + 1)) :
    linOf (reflConj n g) v = spaceRefl n (linOf g (spaceRefl n v)) := rfl

theorem reflConj_smul_spaceRefl (g : isom (n + 1)) (p : Minkowski (n + 1)) :
    reflConj n g • spaceRefl n p = spaceRefl n (g • p) := by
  rw [reflConj_smul, spaceRefl_spaceRefl]

/-- `R₀⁻¹(Ω) = R₀(Ω)`, as an open set. -/
def reflOpens (Ω : Opens (Minkowski (n + 1))) : Opens (Minkowski (n + 1)) :=
  ⟨spaceRefl n ⁻¹' Ω, Ω.isOpen.preimage continuous_spaceRefl⟩

@[simp] theorem mem_reflOpens {Ω : Opens (Minkowski (n + 1))} {p : Minkowski (n + 1)} :
    p ∈ reflOpens Ω ↔ spaceRefl n p ∈ Ω := Iff.rfl

end Reflection

/-! ### Local maps of a given affine type -/

section LocalType

variable {d : ℕ} {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace Y] [ChartedSpace (Minkowski d) Y]
  [TopologicalSpace Z] [ChartedSpace (Minkowski d) Z]

variable (d) in
/-- `f` is **locally of type `A`**: read in charts, near every point, `f` is `g ∘ A` for some
`g ∈ Isom(𝐌ⁿ)`. For `A = id` this is `IsLocalIsometry`; for `A = R₀` an orientation-reversing
local isometry. -/
def IsLocalAIso (A : Minkowski d → Minkowski d) (f : X → Y) : Prop :=
  Continuous f ∧ ∀ x : X, ∃ g : isom d, ∀ᶠ y in 𝓝 x,
    chartAt (Minkowski d) (f x) (f y) = g • A (chartAt (Minkowski d) x y)

theorem isLocalAIso_id_iff {f : X → Y} : IsLocalAIso d id f ↔ IsLocalIsometry d f :=
  isLocalIsometry_iff_eventually.symm

theorem IsLocalAIso.congr_left {A A' : Minkowski d → Minkowski d} {g₀ : isom d}
    (hA : ∀ p, A p = g₀ • A' p) {f : X → Y} (hf : IsLocalAIso d A f) : IsLocalAIso d A' f := by
  refine ⟨hf.1, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf.2 x
  exact ⟨g * g₀, hg.mono fun y hy => by rw [hy, hA, mul_smul]⟩

theorem IsLocalAIso.comp_isLocalIsometry {A : Minkowski d → Minkowski d}
    (hA : ∀ g : isom d, ∃ g' : isom d, ∀ p, A (g • p) = g' • A p) {f : Y → Z} {h : X → Y}
    (hf : IsLocalAIso d A f) (hh : IsLocalIsometry d h) : IsLocalAIso d A (f ∘ h) := by
  obtain ⟨hhc, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine ⟨hf.1.comp hhc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hh' x
  obtain ⟨g, hg⟩ := hf.2 (h x)
  obtain ⟨g₁', hg₁'⟩ := hA g₁
  refine ⟨g * g₁', ?_⟩
  filter_upwards [hhc.continuousAt.eventually hg, hg₁] with y h1 h2
  simp only [comp_apply, h1, h2, hg₁', mul_smul]

theorem IsLocalIsometry.comp_isLocalAIso {A : Minkowski d → Minkowski d} {f : X → Y} {h : Y → Z}
    (hh : IsLocalIsometry d h) (hf : IsLocalAIso d A f) : IsLocalAIso d A (h ∘ f) := by
  obtain ⟨hhc, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine ⟨hhc.comp hf.1, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf.2 x
  obtain ⟨g', hg'⟩ := hh' (f x)
  refine ⟨g' * g, ?_⟩
  filter_upwards [hf.1.continuousAt.eventually hg', hg] with y h1 h2
  simp only [comp_apply, h1, h2, mul_smul]

theorem IsLocalAIso.comp {A A' : Minkowski d → Minkowski d}
    (hA : ∀ g : isom d, ∃ g' : isom d, ∀ p, A (g • p) = g' • A p) {f : Y → Z} {h : X → Y}
    (hf : IsLocalAIso d A f) (hh : IsLocalAIso d A' h) : IsLocalAIso d (A ∘ A') (f ∘ h) := by
  refine ⟨hf.1.comp hh.1, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hh.2 x
  obtain ⟨g, hg⟩ := hf.2 (h x)
  obtain ⟨g₁', hg₁'⟩ := hA g₁
  refine ⟨g * g₁', ?_⟩
  filter_upwards [hh.1.continuousAt.eventually hg, hg₁] with y h1 h2
  simp only [comp_apply, h1, h2, hg₁', mul_smul]

/-- Descending a local map of type `A` along a surjective local isometry. -/
theorem IsLocalAIso.of_comp_right {A : Minkowski d → Minkowski d}
    (hA : ∀ g : isom d, ∃ g' : isom d, ∀ p, A (g • p) = g' • A p) {q : X → Y} {f : Y → Z}
    (hq : IsLocalIsometry d q) (hqs : Surjective q) (hfq : IsLocalAIso d A (f ∘ q)) :
    IsLocalAIso d A f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq.2 z
  obtain ⟨g₂, hg₂⟩ := hq' z
  obtain ⟨g₃, hg₃⟩ := hA g₂⁻¹
  refine ⟨g₁ * g₃, ?_⟩
  have hS : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₃) • A (chartAt (Minkowski d) (q z) (q w))} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, ← hg₃, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hS] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

end LocalType

/-! ### A trivial linear twisted product: `U^⊥ = 0` -/

section TrivialLTP

variable {d₁ d : ℕ}

theorem apply_retract_eq_of_perp (ι : AffineMinkEmbedding d₁ d) (hperp : ∀ w ∈ ι.perp, w = 0)
    (p : Minkowski d) : ι (ι.retract p) = p :=
  (sub_eq_zero.1 (hperp _ (ι.sub_apply_retract_mem_perp p))).symm

theorem surjective_of_perp (ι : AffineMinkEmbedding d₁ d) (hperp : ∀ w ∈ ι.perp, w = 0) :
    Surjective ι := fun p => ⟨_, apply_retract_eq_of_perp ι hperp p⟩

theorem lin_surjective_of_surjective (ι : AffineMinkEmbedding d₁ d) (hs : Surjective ι) :
    Surjective ι.lin := fun w => by
  obtain ⟨x, hx⟩ := hs (w + ι 0)
  refine ⟨x, ?_⟩
  have := ι.apply_sub 0 x
  rw [sub_zero] at this
  rw [← this, hx, add_sub_cancel_right]

/-- **A trivial LTP has `d₁ = d`**: `ι.lin` is then a linear isomorphism. -/
theorem eq_of_perp (ι : AffineMinkEmbedding d₁ d) (hperp : ∀ w ∈ ι.perp, w = 0) : d₁ = d := by
  have e := LinearEquiv.ofBijective ι.lin
    ⟨ι.lin_injective, lin_surjective_of_surjective ι (surjective_of_perp ι hperp)⟩
  have := e.finrank_eq
  rw [finrank_minkowski, finrank_minkowski] at this
  omega

/-- `ι`, bijective, as an affine equivalence. -/
noncomputable def affOfSurjective (ι : AffineMinkEmbedding d d) (hs : Surjective ι) :
    Minkowski d ≃ᵃ[ℝ] Minkowski d :=
  AffineEquiv.ofBijective (φ := ι.toAffineMap) ⟨ι.injective, hs⟩

theorem affOfSurjective_apply (ι : AffineMinkEmbedding d d) (hs : Surjective ι)
    (p : Minkowski d) : affOfSurjective ι hs p = ι p := rfl

theorem affOfSurjective_linear_apply (ι : AffineMinkEmbedding d d) (hs : Surjective ι)
    (v : Minkowski d) : (affOfSurjective ι hs).linear v = ι.lin v := rfl

theorem det_lin_eq_one_or (ι : AffineMinkEmbedding d d) :
    LinearMap.det ι.lin = 1 ∨ LinearMap.det ι.lin = -1 := by
  have h := det_sq_of_minkQ (A := ι.lin) ι.minkQ_linear
  exact eq_or_eq_neg_of_sq_eq_sq _ 1 (by rw [h]; norm_num)

/-- **A bijective orthochronous `ι` of determinant `1` is an isometry.** -/
theorem exists_isom_of_det_one (ι : AffineMinkEmbedding d d) (hι : ι.Orthochronous)
    (hs : Surjective ι) (hdet : LinearMap.det ι.lin = 1) : ∃ g₀ : isom d, ∀ p, ι p = g₀ • p := by
  refine ⟨⟨affOfSurjective ι hs, ?_⟩, fun p => rfl⟩
  rw [mem_isom_iff]
  refine mem_lorentz_of (fun v => ι.minkQ_linear v) hι ?_
  exact hdet

/-- In `𝐌¹` (no spatial direction) an orthochronous linear isometry is the identity, so its
determinant is `1`. -/
theorem det_lin_eq_one_zero (ι : AffineMinkEmbedding 0 0) (hι : ι.Orthochronous) :
    LinearMap.det ι.lin = 1 := by
  have hv : ∀ v : Minkowski 0, v = v.1 • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 0))) := fun v =>
    Prod.ext (by simp) (Subsingleton.elim _ _)
  set c := (ι.lin ((1 : ℝ), 0)).1 with hc
  have h1 : ι.lin ((1 : ℝ), 0) = c • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 0))) := by
    rw [hv (ι.lin _)]
  have hQ := ι.minkQ_lin ((1 : ℝ), 0)
  rw [h1] at hQ
  simp [minkQ] at hQ
  have hc1 : c = 1 := by
    have hc0 : 0 < c := hι
    rcases hQ with h | h
    · exact h
    · linarith
  have hid : ι.lin = LinearMap.id := LinearMap.ext fun v => by
    rw [hv v, map_smul, h1, hc1, one_smul]; rfl
  rw [hid, LinearMap.det_id]

/-- **A bijective orthochronous `ι` of determinant `−1` is an isometry after `R₀`.** -/
theorem exists_isom_of_det_neg_one {n : ℕ} (ι : AffineMinkEmbedding (n + 1) (n + 1))
    (hι : ι.Orthochronous) (hs : Surjective ι) (hdet : LinearMap.det ι.lin = -1) :
    ∃ g₀ : isom (n + 1), ∀ p, ι p = g₀ • spaceRefl n p := by
  refine ⟨⟨(reflAff n).trans (affOfSurjective ι hs), ?_⟩, fun p => ?_⟩
  · rw [mem_isom_iff]
    refine mem_lorentz_of (fun v => ?_) ?_ ?_
    · show minkQ (ι.lin (spaceRefl n v)) = minkQ v
      rw [ι.minkQ_lin, minkQ_spaceRefl]
    · show 0 < (ι.lin (spaceRefl n (timeUnit (n + 1)))).1
      have : spaceRefl n (timeUnit (n + 1)) = timeUnit (n + 1) := by simp [timeUnit]
      rw [this]
      exact hι
    · show LinearMap.det (ι.lin ∘ₗ (spaceRefl n : Minkowski (n + 1) →ₗ[ℝ] _)) = 1
      rw [LinearMap.det_comp, hdet, det_spaceRefl]
      norm_num
  · show ι p = ι (spaceRefl n (spaceRefl n p))
    rw [spaceRefl_spaceRefl]

variable {B M₁ : Type*} [TopologicalSpace B] [ChartedSpace (Minkowski d) B]
  [TopologicalSpace M₁] [ChartedSpace (Minkowski d) M₁]

/-- **G9a, the identification `M₁ ≅ B` of a trivial LTP**: for LTP data `(Γ, Ω, ι)` with `ι`
bijective, `π₁(x) ↦ π(ι x)` descends to a homeomorphism `e : M₁ ≃ B`, which is locally of type
`A` whenever `ι = g₀ ∘ A` with `A` normalising `Isom(𝐌ⁿ)`. -/
theorem exists_homeomorph_of_isLTPData {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    {ι : AffineMinkEmbedding d d} (hd : IsLTPData B M₁ Γ Ω ι) (hs : Surjective ι) :
    ∃ e : M₁ ≃ₜ B, ∀ A : Minkowski d → Minkowski d,
      (∀ g : isom d, ∃ g' : isom d, ∀ p, A (g • p) = g' • A p) →
      (∃ g₀ : isom d, ∀ p, ι p = g₀ • A p) → IsLocalAIso d A e := by
  obtain ⟨π₁, -, hloc₁, hsurj₁, hfib₁⟩ := hd.quotient_base.quot
  obtain ⟨π, -, hloc, hπs, hfib⟩ := hd.quotient.quot
  set j : ι.preimageOpens Ω → Ω := fun x => ⟨ι x, x.2⟩ with hjdef
  have hjc : Continuous j := (ι.continuous.comp continuous_subtype_val).subtype_mk _
  let s₁ : M₁ → ι.preimageOpens Ω := Function.surjInv hsurj₁
  have hs₁ : ∀ m, π₁ (s₁ m) = m := Function.surjInv_eq hsurj₁
  let e : M₁ → B := fun m => π (j (s₁ m))
  have he : ∀ x, e (π₁ x) = π (j x) := by
    intro x
    obtain ⟨g, ⟨γ, hγ, hgγ⟩, hgx⟩ := (hfib₁ (s₁ (π₁ x)) x).1 (hs₁ _)
    refine (hfib _ _).2 ⟨γ, hγ, ?_⟩
    show γ • ι (s₁ (π₁ x) : Minkowski d) = ι x
    rw [← hgγ, hgx]
  have hinj : Injective e := by
    intro m m' hmm
    obtain ⟨x, rfl⟩ := hsurj₁ m
    obtain ⟨x', rfl⟩ := hsurj₁ m'
    rw [he, he] at hmm
    obtain ⟨γ, hγ, hγx⟩ := (hfib _ _).1 hmm
    obtain ⟨g, hg⟩ := hd.restricts γ hγ
    refine (hfib₁ x x').2 ⟨g, ⟨γ, hγ, hg⟩, ι.injective ?_⟩
    rw [hg]
    exact hγx
  have hsurj : Surjective e := by
    intro b
    obtain ⟨p, rfl⟩ := hπs b
    obtain ⟨x, hx⟩ := hs p
    have hxm : x ∈ ι.preimageOpens Ω := by
      rw [AffineMinkEmbedding.mem_preimageOpens, hx]; exact p.2
    refine ⟨π₁ ⟨x, hxm⟩, ?_⟩
    rw [he]
    exact congrArg π (Subtype.ext hx)
  have heπ : e ∘ π₁ = π ∘ j := funext he
  have hq₁ : IsQuotientMap π₁ := hloc₁.isOpenMap.isQuotientMap hloc₁.continuous hsurj₁
  have hec : Continuous e := hq₁.continuous_iff.2 (heπ ▸ hloc.continuous.comp hjc)
  -- `j` is open: it is the restriction of the homeomorphism `ι`
  set ιh : Minkowski d ≃ₜ Minkowski d :=
    (affOfSurjective ι hs).toHomeomorphOfFiniteDimensional with hιh
  have hjo : IsOpenMap j := by
    intro U hU
    have : j '' U = Subtype.val ⁻¹' (ιh '' (Subtype.val '' U)) := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, hp⟩
        exact ⟨x, hx, Subtype.ext hp⟩
    rw [this]
    exact (ιh.isOpenMap _ ((ι.preimageOpens Ω).isOpen.isOpenMap_subtype_val _ hU)).preimage
      continuous_subtype_val
  have heo : IsOpenMap e := by
    intro O hO
    have : e '' O = π '' (j '' (π₁ ⁻¹' O)) := by
      ext b
      constructor
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨x, rfl⟩ := hsurj₁ m
        exact ⟨j x, ⟨x, hm, rfl⟩, (he x).symm⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨π₁ x, hx, he x⟩
    rw [this]
    exact hloc.isOpenMap _ (hjo _ (hO.preimage hloc₁.continuous))
  refine ⟨(IsHomeomorph.mk hec heo ⟨hinj, hsurj⟩).homeomorph e, fun A hA ⟨g₀, hg₀⟩ => ?_⟩
  have hj : IsLocalAIso d A j := by
    refine ⟨hjc, fun x => ⟨g₀, Eventually.of_forall fun y => ?_⟩⟩
    show ι y = g₀ • A y
    exact hg₀ y
  have h1 : IsLocalAIso d A (e ∘ π₁) := by
    rw [heπ]; exact IsLocalIsometry.comp_isLocalAIso hloc hj
  exact IsLocalAIso.of_comp_right hA hloc₁ hsurj₁ h1

end TrivialLTP

/-! ### Transport of a quotient presentation along an orientation-reversing identification -/

section ReflTransport

/-- `R₀ : R₀(Ω) ≃ Ω`. -/
noncomputable def reflOpensHomeo {n : ℕ} (Ω : Opens (Minkowski (n + 1))) : reflOpens Ω ≃ₜ Ω where
  toFun p := ⟨spaceRefl n p, p.2⟩
  invFun q := ⟨spaceRefl n q, by
    show spaceRefl n (spaceRefl n q) ∈ Ω
    rw [spaceRefl_spaceRefl]; exact q.2⟩
  left_inv p := Subtype.ext (spaceRefl_spaceRefl (p : Minkowski (n + 1)))
  right_inv q := Subtype.ext (spaceRefl_spaceRefl (q : Minkowski (n + 1)))
  continuous_toFun := (continuous_spaceRefl.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_spaceRefl.comp continuous_subtype_val).subtype_mk _


variable {n : ℕ} {M₁ B : Type*} [TopologicalSpace M₁] [ChartedSpace (Minkowski (n + 1)) M₁]
  [TopologicalSpace B] [ChartedSpace (Minkowski (n + 1)) B]

theorem spaceRefl_normalizes (g : isom (n + 1)) :
    ∃ g' : isom (n + 1), ∀ p, spaceRefl n (g • p) = g' • spaceRefl n p :=
  ⟨reflConj n g, fun p => (reflConj_smul_spaceRefl g p).symm⟩

/-- **`Γ\Ω` read through an orientation-reversing identification**: if `e : M₁ ≃ B` is locally
`g ∘ R₀` and `M₁ = G\Ω₁`, then `B = (R₀ G R₀)\R₀(Ω₁)`. -/
theorem isQuotientOf_refl (e : M₁ ≃ₜ B) (he : IsLocalAIso (n + 1) (spaceRefl n) e)
    {G : Subgroup (isom (n + 1))} {Ω₁ : Opens (Minkowski (n + 1))} (hq : IsQuotientOf M₁ G Ω₁) :
    IsQuotientOf B (G.map (reflConj n)) (reflOpens Ω₁) := by
  obtain ⟨π₁, hcov, hloc, hsurj, hfib⟩ := hq.quot
  have hinv := hq.invariant
  set k := reflOpensHomeo (n := n) Ω₁
  have hk : IsLocalAIso (n + 1) (spaceRefl n) k :=
    ⟨k.continuous, fun x => ⟨1, Eventually.of_forall fun y => by
      rw [one_smul]; rfl⟩⟩
  refine ⟨(FlatQuotient.invariant_iff _ _).1 ⟨fun γ p hp => ?_⟩, e ∘ (π₁ ∘ k),
    (hcov.comp_homeomorph k).homeomorph_comp e, ?_, e.surjective.comp (hsurj.comp k.surjective),
    fun p q => ?_⟩
  · obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1 γ.2
    show spaceRefl n ((γ : isom (n + 1)) • p) ∈ Ω₁
    rw [← hgγ, reflConj_smul, spaceRefl_spaceRefl]
    exact hinv.smul_mem ⟨g, hg⟩ _ hp
  · have h1 := (he.comp_isLocalIsometry spaceRefl_normalizes hloc).comp spaceRefl_normalizes hk
    refine isLocalAIso_id_iff.1 (h1.congr_left (g₀ := 1) fun p => ?_)
    simp
  · simp only [comp_apply, e.injective.eq_iff]
    rw [hfib]
    constructor
    · rintro ⟨g, hg, hgpq⟩
      refine ⟨reflConj n g, Subgroup.mem_map_of_mem _ hg, ?_⟩
      rw [reflConj_smul]
      have : (g • spaceRefl n (p : Minkowski (n + 1))) = spaceRefl n q := hgpq
      rw [this, spaceRefl_spaceRefl]
    · rintro ⟨γ, hγ, hγpq⟩
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hγ
      refine ⟨g, hg, ?_⟩
      show g • spaceRefl n (p : Minkowski (n + 1)) = spaceRefl n q
      rw [← hγpq, reflConj_smul, spaceRefl_spaceRefl]

end ReflTransport

/-! ### The families under an isometric homeomorphism and under `R₀` -/

section FamilyTransport

/-- **Unipotent spacetimes transport along an isometric homeomorphism.** -/
theorem isUnipotentSpacetime_homeomorph {d : ℕ} {M N : FlatSpacetime.{u} (d + 1)} (e : M ≃ₜ N)
    (he : IsLocalIsometry (d + 1) e) (h : IsUnipotentSpacetime M) : IsUnipotentSpacetime N := by
  obtain ⟨φ, ℓ, α, β, L, Γ, h1, h2, h3, h4, hq⟩ := h
  exact ⟨φ, ℓ, α, β, L, Γ, h1, h2, h3, h4, isQuotientOf_homeomorph hq e he⟩

/-- The unipotent family in every dimension, transported. -/
theorem unipotentFamily_homeomorph : ∀ {d : ℕ} {M N : FlatSpacetime.{u} d} (e : M ≃ₜ N),
    IsLocalIsometry d e →
    (match d, M with
      | 0, _ => False
      | _ + 1, M => IsUnipotentSpacetime M) →
    (match d, N with
      | 0, _ => False
      | _ + 1, N => IsUnipotentSpacetime N)
  | 0, _, _, _, _, h => h.elim
  | _ + 1, _, _, e, he, h => isUnipotentSpacetime_homeomorph e he h

/-- **Family (b) transports along an isometric homeomorphism** (same group, same domain). -/
theorem isCHCentralExtension_homeomorph {d : ℕ} {M N : FlatSpacetime.{u} d} (e : M ≃ₜ N)
    (he : IsLocalIsometry d e) (h : IsCHCentralExtension M) : IsCHCentralExtension N := by
  obtain ⟨Γ, E, h1, h2, h3, h4, h5, h6, ⟨hq, hE⟩ | ⟨hq, hE⟩⟩ := h
  · exact ⟨Γ, E, h1, h2, h3, h4, h5, h6, Or.inl ⟨isQuotientOf_homeomorph hq e he, hE⟩⟩
  · exact ⟨Γ, E, h1, h2, h3, h4, h5, h6, Or.inr ⟨isQuotientOf_homeomorph hq e he, hE⟩⟩

variable {n : ℕ}

theorem reflConj_horizTranslation (v : Multiplicative (EuclideanSpace ℝ (Fin (n + 1)))) :
    reflConj n (horizTranslation (n + 1) v) =
      horizTranslation (n + 1) (Multiplicative.ofAdd (coordRefl n (Multiplicative.toAdd v))) := by
  refine Subtype.ext (AffineEquiv.ext fun p => ?_)
  show spaceRefl n (horizTranslation (n + 1) v • spaceRefl n p) =
    horizTranslation (n + 1) (Multiplicative.ofAdd (coordRefl n (Multiplicative.toAdd v))) • p
  rw [horizTranslation_smul, horizTranslation_smul, map_add, spaceRefl_spaceRefl]
  simp

theorem map_reflConj_frameConj (φ : isom (n + 1)) (H : Subgroup (isom (n + 1))) :
    (frameConj φ H).map (reflConj n) = frameConj (reflConj n φ) (H.map (reflConj n)) := by
  rw [frameConj, frameConj, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.coe_comp, comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

theorem map_reflConj_horizGroup (Λ : AddSubgroup (EuclideanSpace ℝ (Fin (n + 1)))) :
    (horizGroup Λ).map (reflConj n) = horizGroup (Λ.map (coordRefl n).toAddMonoidHom) := by
  ext γ
  simp only [Subgroup.mem_map, mem_horizGroup, AddSubgroup.mem_map]
  constructor
  · rintro ⟨g, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨coordRefl n v, ⟨v, hv, rfl⟩, (reflConj_horizTranslation _).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, reflConj_horizTranslation _⟩

theorem ballFinite_map_coordRefl {Λ : AddSubgroup (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΛ : BallFinite Λ) : BallFinite (Λ.map (coordRefl n).toAddMonoidHom) :=
  ⟨fun R => ((hΛ.finite_ball R).image (coordRefl n)).subset (by
    rintro _ ⟨⟨v, hv, rfl⟩, hR⟩
    exact ⟨v, ⟨hv, by rwa [LinearMap.toAddMonoidHom_coe, norm_coordRefl] at hR⟩, rfl⟩)⟩

theorem reflOpens_top : reflOpens (⊤ : Opens (Minkowski (n + 1))) = ⊤ := Opens.ext rfl

theorem reflOpens_isomImage (φ : isom (n + 1)) (W : Opens (Minkowski (n + 1))) :
    reflOpens (isomImage φ W) = isomImage (reflConj n φ) (reflOpens W) := by
  ext p
  simp only [mem_reflOpens, SetLike.mem_coe, coe_isomImage, mem_image]
  constructor
  · rintro ⟨q, hq, hqp⟩
    refine ⟨spaceRefl n q, by simpa using hq, ?_⟩
    rw [reflConj_smul_spaceRefl, show φ • q = spaceRefl n p from hqp, spaceRefl_spaceRefl]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨spaceRefl n q, hq, by rw [reflConj_smul, spaceRefl_spaceRefl]⟩

/-- **Translation spacetimes transport along a local identification of type `R₀`.** -/
theorem isTranslationSpacetime_refl {M N : FlatSpacetime.{u} (n + 1)} (e : M ≃ₜ N)
    (he : IsLocalAIso (n + 1) (spaceRefl n) e) (h : IsTranslationSpacetime M) :
    IsTranslationSpacetime N := by
  obtain ⟨φ, Λ, hΛ, hq⟩ := h
  have h2 := isQuotientOf_refl e he hq
  rw [map_reflConj_frameConj, map_reflConj_horizGroup, reflOpens_top] at h2
  exact ⟨_, _, ballFinite_map_coordRefl hΛ, h2⟩

theorem reflConj_misnerMap (x : ℝ × EuclideanSpace ℝ (Fin n)) :
    reflConj n (misnerMap x) = misnerMap (-x.1, x.2) := by
  refine Subtype.ext (AffineEquiv.ext fun p => ?_)
  show spaceRefl n (misnerMap x • spaceRefl n p) = misnerMap (-x.1, x.2) • p
  rw [misnerMap_smul, misnerMap_smul, map_add]
  refine Prod.ext ?_ ?_
  · simp [axisBoost_apply, axisBoostL, Real.cosh_neg, Real.sinh_neg]
  · ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [axisBoost_apply, axisBoostL, Real.cosh_neg, Real.sinh_neg, coordRefl_apply]
      ring
    · simp [axisBoost_apply, axisBoostL, coordRefl_apply, Fin.succ_ne_zero]

/-- `(s, w) ↦ (−s, w)`. -/
noncomputable def negFst (n : ℕ) : ℝ × EuclideanSpace ℝ (Fin n) →+ ℝ × EuclideanSpace ℝ (Fin n) :=
  (LinearMap.prodMap (-LinearMap.id) LinearMap.id :
    ℝ × EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin n)).toAddMonoidHom

@[simp] theorem negFst_apply (x : ℝ × EuclideanSpace ℝ (Fin n)) : negFst n x = (-x.1, x.2) := rfl

theorem map_reflConj_misnerGroup (L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin n))) :
    (misnerGroup L).map (reflConj n) = misnerGroup (L.map (negFst n)) := by
  ext γ
  simp only [Subgroup.mem_map, mem_misnerGroup, AddSubgroup.mem_map]
  constructor
  · rintro ⟨g, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (reflConj_misnerMap x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, reflConj_misnerMap x⟩

theorem ballFinite_map_negFst {L : AddSubgroup (ℝ × EuclideanSpace ℝ (Fin n))}
    (hL : BallFinite L) : BallFinite (L.map (negFst n)) :=
  ⟨fun R => ((hL.finite_ball R).image (negFst n)).subset (by
    rintro _ ⟨⟨x, hx, rfl⟩, hR⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    simpa [Prod.norm_def] using hR)⟩

theorem nullX_spaceRefl (p : Minkowski (n + 1)) : nullX (spaceRefl n p) = -nullY p := by
  simp [nullX, nullY, coordRefl_apply]; ring

theorem nullY_spaceRefl (p : Minkowski (n + 1)) : nullY (spaceRefl n p) = -nullX p := by
  simp [nullX, nullY, coordRefl_apply]; ring

theorem reflOpens_misnerWedge : reflOpens (misnerWedge n) = misnerWedge n := by
  ext p
  show spaceRefl n p ∈ omegaPlus (misnerΛ n) ↔ p ∈ omegaPlus (misnerΛ n)
  rw [mem_omegaPlus_misnerΛ, mem_omegaPlus_misnerΛ, nullX_spaceRefl, nullY_spaceRefl]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem reflOpens_misnerWedgePast : reflOpens (misnerWedgePast n) = misnerWedgePast n := by
  ext p
  show nullX (spaceRefl n p) < 0 ∧ 0 < nullY (spaceRefl n p) ↔ nullX p < 0 ∧ 0 < nullY p
  rw [nullX_spaceRefl, nullY_spaceRefl]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Misner spacetimes transport along a local identification of type `R₀`.** -/
theorem isMisnerSpacetime_refl {M N : FlatSpacetime.{u} (n + 1)} (e : M ≃ₜ N)
    (he : IsLocalAIso (n + 1) (spaceRefl n) e) (h : IsMisnerSpacetime M) :
    IsMisnerSpacetime N := by
  obtain ⟨φ, L, hL, ⟨x, hx, hx1⟩, hq | hq⟩ := h
  · have h2 := isQuotientOf_refl e he hq
    rw [map_reflConj_frameConj, map_reflConj_misnerGroup, reflOpens_isomImage,
      reflOpens_misnerWedge] at h2
    exact ⟨_, _, ballFinite_map_negFst hL, ⟨_, ⟨x, hx, rfl⟩, by simpa using hx1⟩, Or.inl h2⟩
  · have h2 := isQuotientOf_refl e he hq
    rw [map_reflConj_frameConj, map_reflConj_misnerGroup, reflOpens_isomImage,
      reflOpens_misnerWedgePast] at h2
    exact ⟨_, _, ballFinite_map_negFst hL, ⟨_, ⟨x, hx, rfl⟩, by simpa using hx1⟩, Or.inr h2⟩

/-- **G9b through `R₀`**: a GH spacetime `N` identified with a unipotent spacetime by a local
identification of type `R₀` is not Cauchy-compact. The proof of
`not_cauchyCompact_of_isUnipotentSpacetime`, run on the presentation `(R₀ Γ R₀)\R₀(Ω)` of
`isQuotientOf_refl`, with the coordinate `y ∘ φ⁻¹ ∘ R₀`. -/
theorem not_cauchyCompact_of_refl_unipotent {M N : FlatSpacetime.{u} (n + 1)} (hGH : GH N)
    (e : M ≃ₜ N) (he : IsLocalAIso (n + 1) (spaceRefl n) e) (hU : IsUnipotentSpacetime M) :
    ¬ CauchyCompact N := by
  rintro ⟨K, hK, hKc, -⟩
  obtain ⟨φ, ℓ, α, β, L, Γ, -, hcomp, hΓ, -, hq⟩ := hU
  have hq' := isQuotientOf_refl e he hq
  set F : Minkowski (n + 1) → ℝ := fun p => nullY (φ⁻¹ • spaceRefl n p) with hFdef
  set v₀ : Minkowski (n + 1) := (1, EuclideanSpace.single 0 1) with hv₀def
  have hv₀ : IsFutureCausal v₀ := ⟨zero_le_one, by simp [minkQ, v₀]⟩
  have hv₀0 : v₀ ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
  have hFc : Continuous F := continuous_nullY.comp ((continuous_const_smul _).comp
    continuous_spaceRefl)
  have hinv : ∀ γ ∈ (frameConj φ Γ).map (reflConj n),
      ∀ p ∈ (reflOpens (isomImage φ (unipDomain α β)) : Set (Minkowski (n + 1))),
      F (γ • p) = F p := by
    intro γ'' hγ'' p _
    obtain ⟨γ', hγ', rfl⟩ := Subgroup.mem_map.1 hγ''
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    obtain ⟨t, -, ht⟩ := hΓ γ hγ
    simp only [hFdef, reflConj_smul, spaceRefl_spaceRefl, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_smul, inv_smul_smul, ht, nullY_unipAction]
  set v : Minkowski (n + 1) := spaceRefl n (linOf φ v₀) with hvdef
  have hline : ∀ (p : Minkowski (n + 1)) (s : ℝ), F (p + s • v) = F p := by
    intro p s
    have hp : spaceRefl n (p + s • v) = φ • (φ⁻¹ • spaceRefl n p + s • v₀) := by
      rw [isom_smul_add_smul, smul_inv_smul, map_add, map_smul, hvdef, spaceRefl_spaceRefl]
    simp only [hFdef, hp, inv_smul_smul]
    simp only [nullY, hv₀def, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst,
      PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul,
      mul_one]
    ring
  have hφv := lorentz.isFutureCausal_apply (linOf_mem φ) hv₀
  have hv : IsFutureCausal v := ⟨by simpa [hvdef] using hφv.1, by
    rw [hvdef, minkQ_spaceRefl]; exact hφv.2⟩
  have hv0 : v ≠ 0 := fun h => by
    have : linOf φ v₀ = 0 := by
      rw [← spaceRefl_spaceRefl (linOf φ v₀), ← hvdef, h, map_zero]
    exact (linOf φ).map_ne_zero_iff.2 hv₀0 this
  have hcpt := isCompact_image_of_isQuotientOf hGH.1 hq' hK hKc hFc hinv hv hv0 hline
  have himg : F '' (reflOpens (isomImage φ (unipDomain α β)) : Set (Minkowski (n + 1))) =
      {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' : spaceRefl n p ∈ (isomImage φ (unipDomain α β) : Set (Minkowski (n + 1))) := hp
      rw [coe_isomImage] at hp'
      obtain ⟨q, hq, hqp⟩ := hp'
      simp only [hFdef, ← show φ • q = spaceRefl n p from hqp, inv_smul_smul]
      exact hq
    · intro hy
      have hn : nullY ((-(√2 * y), 0) : Minkowski (n + 1)) = y := by
        simp only [nullY, PiLp.zero_apply, zero_sub, neg_neg]
        field_simp
      refine ⟨spaceRefl n (φ • ((-(√2 * y), 0) : Minkowski (n + 1))), ?_, ?_⟩
      · show spaceRefl n (spaceRefl n _) ∈ isomImage φ (unipDomain α β)
        rw [spaceRefl_spaceRefl, smul_mem_isomImage]
        show α < (nullY _ : EReal) ∧ (nullY _ : EReal) < β
        rw [hn]
        exact hy
      · simp only [hFdef, spaceRefl_spaceRefl, inv_smul_smul]
        exact hn
  rw [himg] at hcpt
  have hopen : IsOpen {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} :=
    (isOpen_lt continuous_const continuous_coe_real_ereal).inter
      (isOpen_lt continuous_coe_real_ereal continuous_const)
  obtain ⟨y₀, hy₀⟩ := EReal.lt_iff_exists_real_btwn.1 hcomp.1
  rcases isClopen_iff.1 ⟨hcpt.isClosed, hopen⟩ with h | h
  · have hmem : y₀ ∈ {y : ℝ | α < (y : EReal) ∧ (y : EReal) < β} := hy₀
    rw [h] at hmem
    exact hmem
  · rw [h] at hcpt
    exact noncompact_univ ℝ hcpt

end FamilyTransport

/-! ### Family (b) under `R₀` -/

section CHRefl

variable {n : ℕ}

theorem minkB_spaceRefl (v w : Minkowski (n + 1)) :
    minkB (spaceRefl n v) (spaceRefl n w) = minkB v w :=
  minkB_map_of_minkQ (A := (spaceRefl n : Minkowski (n + 1) →ₗ[ℝ] _)) minkQ_spaceRefl v w

theorem trOf_reflConj (γ : isom (n + 1)) : trOf (reflConj n γ) = spaceRefl n (trOf γ) := by
  have h1 := smul_eq_lin_add (reflConj n γ) 0
  have h2 := smul_eq_lin_add γ 0
  rw [map_zero, zero_add] at h1 h2
  rw [← h1, ← h2, reflConj_smul, map_zero]

theorem linOf_reflConj_eq_one_iff (γ : isom (n + 1)) : linOf (reflConj n γ) = 1 ↔ linOf γ = 1 := by
  constructor
  · intro h
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun A : Minkowski (n + 1) ≃ₗ[ℝ] _ => spaceRefl n (A (spaceRefl n v))) h
    simpa [linOf_reflConj] using this
  · intro h
    refine LinearEquiv.ext fun v => ?_
    rw [linOf_reflConj, h]
    simp

theorem mem_kerTranslations_map_reflConj {Γ : Subgroup (isom (n + 1))} {v : Minkowski (n + 1)} :
    v ∈ kerTranslations (Γ.map (reflConj n)) ↔ spaceRefl n v ∈ kerTranslations Γ := by
  constructor
  · rintro ⟨γ', hγ', hL, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    exact ⟨γ, hγ, (linOf_reflConj_eq_one_iff γ).1 hL, by rw [trOf_reflConj, spaceRefl_spaceRefl]⟩
  · rintro ⟨γ, hγ, hL, hv⟩
    refine ⟨reflConj n γ, Subgroup.mem_map_of_mem _ hγ, (linOf_reflConj_eq_one_iff γ).2 hL, ?_⟩
    rw [trOf_reflConj, hv, spaceRefl_spaceRefl]

theorem kerTranslations_map_reflConj (Γ : Subgroup (isom (n + 1))) :
    kerTranslations (Γ.map (reflConj n)) = spaceRefl n '' kerTranslations Γ := by
  ext v
  rw [mem_kerTranslations_map_reflConj]
  constructor
  · intro h; exact ⟨_, h, spaceRefl_spaceRefl v⟩
  · rintro ⟨w, hw, rfl⟩; rwa [spaceRefl_spaceRefl]

/-- Conjugation by `R₀` on `SO₀(1, n+1)`. -/
noncomputable def reflLin (A : lorentz (n + 1)) : lorentz (n + 1) :=
  ⟨(spaceRefl n).trans ((A : Minkowski (n + 1) ≃ₗ[ℝ] _).trans (spaceRefl n)),
    conj_spaceRefl_mem_lorentz A.2⟩

theorem reflLin_apply (A : lorentz (n + 1)) (v : Minkowski (n + 1)) :
    (reflLin A : Minkowski (n + 1) ≃ₗ[ℝ] _) v = spaceRefl n ((A : Minkowski (n + 1) ≃ₗ[ℝ] _)
      (spaceRefl n v)) := rfl

@[simp] theorem reflLin_reflLin (A : lorentz (n + 1)) : reflLin (reflLin A) = A :=
  Subtype.ext (LinearEquiv.ext fun v => by simp [reflLin_apply])

theorem linearPart_reflConj (γ : isom (n + 1)) :
    linearPart (reflConj n γ) = reflLin (linearPart γ) := rfl

theorem continuous_reflLin : Continuous (reflLin (n := n)) := by
  rw [isEmbedding_lorentz_linToCLM.isInducing.continuous_iff]
  set Rc : Minkowski (n + 1) →L[ℝ] Minkowski (n + 1) := linToCLM (spaceRefl n) with hRc
  have : (fun A : lorentz (n + 1) =>
      linToCLM ((reflLin A : lorentz (n + 1)) : Minkowski (n + 1) ≃ₗ[ℝ] _)) =
      fun A : lorentz (n + 1) => Rc.comp ((linToCLM (A : Minkowski (n + 1) ≃ₗ[ℝ] _)).comp Rc) := by
    funext A
    exact ContinuousLinearMap.ext fun v => rfl
  show Continuous (fun A : lorentz (n + 1) =>
    linToCLM ((reflLin A : lorentz (n + 1)) : Minkowski (n + 1) ≃ₗ[ℝ] _))
  rw [this]
  exact continuous_const.clm_comp (continuous_lorentz_linToCLM.clm_comp continuous_const)

theorem mem_linearImage_map_reflConj {Γ : Subgroup (isom (n + 1))} {A : lorentz (n + 1)} :
    A ∈ linearImage (Γ.map (reflConj n)) ↔ reflLin A ∈ linearImage Γ := by
  constructor
  · rintro ⟨γ', hγ', rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    exact ⟨γ, hγ, by rw [linearPart_reflConj, reflLin_reflLin]⟩
  · rintro ⟨γ, hγ, hA⟩
    refine ⟨reflConj n γ, Subgroup.mem_map_of_mem _ hγ, ?_⟩
    rw [linearPart_reflConj, hA, reflLin_reflLin]

theorem discreteTopology_linearImage_map_reflConj {Γ : Subgroup (isom (n + 1))}
    (h : DiscreteTopology (linearImage Γ)) :
    DiscreteTopology (linearImage (Γ.map (reflConj n))) := by
  let f : linearImage (Γ.map (reflConj n)) → linearImage Γ := fun A =>
    ⟨reflLin A, mem_linearImage_map_reflConj.1 A.2⟩
  have hf : Continuous f := (continuous_reflLin.comp continuous_subtype_val).subtype_mk _
  have hfi : Injective f := fun A B hAB => by
    have := congrArg (fun C : linearImage Γ => reflLin (C : lorentz (n + 1))) hAB
    simp only [f, reflLin_reflLin] at this
    exact Subtype.ext this
  exact DiscreteTopology.of_continuous_injective hf hfi

/-- The reflection of the Penrose sphere. -/
noncomputable def sphereRefl (u : PenroseSphere (n + 1)) : PenroseSphere (n + 1) :=
  ⟨coordRefl n u, by
    rw [mem_sphere_zero_iff_norm, norm_coordRefl, norm_penroseSphere]⟩

theorem nullVec_sphereRefl (u : PenroseSphere (n + 1)) :
    nullVec (sphereRefl u) = spaceRefl n (nullVec u) := rfl

@[simp] theorem sphereRefl_sphereRefl (u : PenroseSphere (n + 1)) :
    sphereRefl (sphereRefl u) = u := Subtype.ext (coordRefl_coordRefl _)

theorem not_hasGlobalFixedPoint_map_reflConj {Γ : Subgroup (isom (n + 1))}
    (h : ¬HasGlobalFixedPoint (linearImage Γ)) :
    ¬HasGlobalFixedPoint (linearImage (Γ.map (reflConj n))) := by
  rintro (⟨v, hv, hfix⟩ | ⟨u, hfix⟩)
  · refine h (Or.inl ⟨spaceRefl n v, by rw [minkQ_spaceRefl]; exact hv, fun A hA => ?_⟩)
    have h1 := hfix (reflLin A) (mem_linearImage_map_reflConj.2 (by rwa [reflLin_reflLin]))
    rw [reflLin_apply] at h1
    have := congrArg (spaceRefl n) h1
    rwa [spaceRefl_spaceRefl] at this
  · refine h (Or.inr ⟨sphereRefl u, fun A hA => ?_⟩)
    have h1 := hfix (reflLin A) (mem_linearImage_map_reflConj.2 (by rwa [reflLin_reflLin]))
    have h2 := nullVec_lorentzSphere (reflLin A) u
    rw [h1, reflLin_apply] at h2
    refine lorentzSphere_eq_of_eigen (c := lorentzScale (reflLin A) u) ?_
    rw [nullVec_sphereRefl]
    have h3 := congrArg (spaceRefl n) h2
    rw [map_smul, spaceRefl_spaceRefl] at h3
    rw [eq_inv_smul_iff₀ (lorentzScale_pos _ u).ne'] at h3
    exact h3.symm

/-- `A ↦ R₀ A R₀` on linear automorphisms. -/
noncomputable def reflEquiv (A : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)) :
    Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1) :=
  (spaceRefl n).trans (A.trans (spaceRefl n))

theorem reflEquiv_apply (A : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)) (v : Minkowski (n + 1)) :
    reflEquiv A v = spaceRefl n (A (spaceRefl n v)) := rfl

theorem reflEquiv_mul (A B : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)) :
    reflEquiv (A * B) = reflEquiv A * reflEquiv B :=
  LinearEquiv.ext fun v => by simp [reflEquiv_apply]

theorem isElliptic_reflEquiv {A : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)} (h : IsElliptic A) :
    IsElliptic (reflEquiv A) := by
  obtain ⟨E, hs, hp, hi⟩ := h
  set Rl : Minkowski (n + 1) →ₗ[ℝ] Minkowski (n + 1) := (spaceRefl n).toLinearMap
  refine ⟨E.compl₁₂ Rl Rl, fun v w => ?_, fun v hv => ?_, fun v w => ?_⟩
  · simp only [LinearMap.compl₁₂_apply]; exact hs _ _
  · simp only [LinearMap.compl₁₂_apply]
    refine hp _ fun h0 => hv ?_
    have := congrArg (spaceRefl n) h0
    rwa [show Rl v = spaceRefl n v from rfl, spaceRefl_spaceRefl, map_zero] at this
  · simp only [LinearMap.compl₁₂_apply, Rl, LinearEquiv.coe_coe, reflEquiv_apply,
      spaceRefl_spaceRefl]
    exact hi _ _

theorem isHyperbolic_reflEquiv {A : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)}
    (h : IsHyperbolic A) : IsHyperbolic (reflEquiv A) := by
  obtain ⟨e₀, e₁, ζ, hζ, h0, h1, h01, ha, hb, hc⟩ := h
  refine ⟨spaceRefl n e₀, spaceRefl n e₁, ζ, hζ, by rw [minkQ_spaceRefl, h0],
    by rw [minkQ_spaceRefl, h1], by rw [minkB_spaceRefl, h01], ?_, ?_, fun w hw0 hw1 => ?_⟩
  · rw [reflEquiv_apply, spaceRefl_spaceRefl, ha, map_add, map_smul, map_smul]
  · rw [reflEquiv_apply, spaceRefl_spaceRefl, hb, map_add, map_smul, map_smul]
  · have h0' : minkB e₀ (spaceRefl n w) = 0 := by
      rw [← minkB_spaceRefl, spaceRefl_spaceRefl]; exact hw0
    have h1' : minkB e₁ (spaceRefl n w) = 0 := by
      rw [← minkB_spaceRefl, spaceRefl_spaceRefl]; exact hw1
    rw [reflEquiv_apply, hc _ h0' h1', spaceRefl_spaceRefl]

theorem isLoxodromic_reflEquiv {A : Minkowski (n + 1) ≃ₗ[ℝ] Minkowski (n + 1)}
    (h : IsLoxodromic A) : IsLoxodromic (reflEquiv A) := by
  obtain ⟨Re, H, hRe, hH, hell, hhyp, hA, hcomm⟩ := h
  refine ⟨reflEquiv Re, reflEquiv H, conj_spaceRefl_mem_lorentz hRe,
    conj_spaceRefl_mem_lorentz hH, isElliptic_reflEquiv hell, isHyperbolic_reflEquiv hhyp, ?_, ?_⟩
  · rw [hA, reflEquiv_mul]
  · rw [← reflEquiv_mul, ← reflEquiv_mul, hcomm]

theorem linOf_reflConj_eq (γ : isom (n + 1)) : linOf (reflConj n γ) = reflEquiv (linOf γ) :=
  LinearEquiv.ext fun _ => rfl

theorem minkB_nullVec_sphereRefl (u : PenroseSphere (n + 1)) (p : Minkowski (n + 1)) :
    minkB (nullVec (sphereRefl u)) p = minkB (nullVec u) (spaceRefl n p) := by
  rw [nullVec_sphereRefl, ← minkB_spaceRefl, spaceRefl_spaceRefl]

/-- The reflection of `𝒥 = 𝒮 × ℝ`. -/
noncomputable def penroseRefl (w : PenroseSphere (n + 1) × ℝ) : PenroseSphere (n + 1) × ℝ :=
  (sphereRefl w.1, w.2)

@[simp] theorem penroseRefl_penroseRefl (w : PenroseSphere (n + 1) × ℝ) :
    penroseRefl (penroseRefl w) = w := by
  simp [penroseRefl]

theorem isRepulsiveFixedJ_reflConj {γ : isom (n + 1)} {w : PenroseSphere (n + 1) × ℝ}
    (h : IsRepulsiveFixedJ γ w) : IsRepulsiveFixedJ (reflConj n γ) (penroseRefl w) := by
  obtain ⟨hlox, l, hl0, hl1, hn, hp⟩ := h
  refine ⟨by rw [linOf_reflConj_eq]; exact isLoxodromic_reflEquiv hlox, l, hl0, hl1, ?_,
    fun p => ?_⟩
  · show linOf (reflConj n γ) (nullVec (sphereRefl w.1)) = l • nullVec (sphereRefl w.1)
    rw [linOf_reflConj, nullVec_sphereRefl, spaceRefl_spaceRefl, hn, map_smul]
  · show minkB (nullVec (sphereRefl w.1)) (reflConj n γ • p) - w.2 =
      l⁻¹ * (minkB (nullVec (sphereRefl w.1)) p - w.2)
    rw [minkB_nullVec_sphereRefl, minkB_nullVec_sphereRefl, reflConj_smul, spaceRefl_spaceRefl,
      hp]

theorem loxRepSet_map_reflConj (Γ : Subgroup (isom (n + 1))) :
    loxRepSet (Γ.map (reflConj n)) = penroseRefl '' loxRepSet Γ := by
  ext w
  constructor
  · rintro ⟨γ', hγ', hw⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    have := isRepulsiveFixedJ_reflConj hw
    rw [reflConj_reflConj] at this
    exact ⟨_, ⟨γ, hγ, this⟩, penroseRefl_penroseRefl w⟩
  · rintro ⟨w, ⟨γ, hγ, hw⟩, rfl⟩
    exact ⟨_, Subgroup.mem_map_of_mem _ hγ, isRepulsiveFixedJ_reflConj hw⟩

theorem continuous_penroseRefl : Continuous (penroseRefl (n := n)) :=
  ((((LinearMap.continuous_of_finiteDimensional (coordRefl n)).comp
    continuous_subtype_val).subtype_mk _).comp continuous_fst).prodMk continuous_snd

/-- `penroseRefl` as a homeomorphism. -/
noncomputable def penroseReflHomeo :
    (PenroseSphere (n + 1) × ℝ) ≃ₜ (PenroseSphere (n + 1) × ℝ) where
  toFun := penroseRefl
  invFun := penroseRefl
  left_inv := penroseRefl_penroseRefl
  right_inv := penroseRefl_penroseRefl
  continuous_toFun := continuous_penroseRefl
  continuous_invFun := continuous_penroseRefl

theorem limitSetJ_map_reflConj (Γ : Subgroup (isom (n + 1))) :
    limitSetJ (Γ.map (reflConj n)) = penroseRefl '' limitSetJ Γ := by
  rw [limitSetJ, limitSetJ, loxRepSet_map_reflConj]
  exact (penroseReflHomeo.image_closure (loxRepSet Γ)).symm

theorem omegaPlus_image_penroseRefl (Λ : Set (PenroseSphere (n + 1) × ℝ)) :
    omegaPlus (penroseRefl '' Λ) = spaceRefl n ⁻¹' omegaPlus Λ := by
  ext p
  simp only [mem_preimage, mem_omegaPlus, forall_mem_image]
  exact forall₂_congr fun w _ => by
    rw [show (penroseRefl w).1 = sphereRefl w.1 from rfl, minkB_nullVec_sphereRefl]; rfl

theorem omegaMinus_image_penroseRefl (Λ : Set (PenroseSphere (n + 1) × ℝ)) :
    omegaMinus (penroseRefl '' Λ) = spaceRefl n ⁻¹' omegaMinus Λ := by
  ext p
  simp only [mem_preimage, mem_omegaMinus, forall_mem_image]
  exact forall₂_congr fun w _ => by
    rw [show (penroseRefl w).1 = sphereRefl w.1 from rfl, minkB_nullVec_sphereRefl]; rfl

/-- **Family (b) transports along a local identification of type `R₀`**, with the group
`R₀ Γ R₀`. -/
theorem isCHCentralExtensionOf_refl {M N : FlatSpacetime.{u} (n + 1)} (e : M ≃ₜ N)
    (he : IsLocalAIso (n + 1) (spaceRefl n) e) {Γ : Subgroup (isom (n + 1))}
    (h : IsCHCentralExtensionOf M Γ) : IsCHCentralExtensionOf N (Γ.map (reflConj n)) := by
  obtain ⟨E, hsp, hspan, hball, hfixE, hdisc, hnf, hcase⟩ := h
  set Rl : Minkowski (n + 1) →ₗ[ℝ] Minkowski (n + 1) := (spaceRefl n).toLinearMap with hRl
  have hP : omegaPlus (limitSetJ (Γ.map (reflConj n))) =
      spaceRefl n ⁻¹' omegaPlus (limitSetJ Γ) := by
    rw [limitSetJ_map_reflConj, omegaPlus_image_penroseRefl]
  have hM : omegaMinus (limitSetJ (Γ.map (reflConj n))) =
      spaceRefl n ⁻¹' omegaMinus (limitSetJ Γ) := by
    rw [limitSetJ_map_reflConj, omegaMinus_image_penroseRefl]
  refine ⟨E.map Rl, ?_, ?_, fun R => ?_, ?_, discreteTopology_linearImage_map_reflConj hdisc,
    not_hasGlobalFixedPoint_map_reflConj hnf, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ hv0
    have hw0 : w ≠ 0 := fun h0 => hv0 (by rw [h0, map_zero])
    simp only [hRl, LinearEquiv.coe_coe]
    rw [minkQ_spaceRefl]
    exact hsp w hw hw0
  · rw [kerTranslations_map_reflConj, ← hspan]
    exact Submodule.span_image Rl
  · refine ((hball R).image (spaceRefl n)).subset ?_
    rintro v ⟨hv, hvR⟩
    refine ⟨spaceRefl n v, ⟨mem_kerTranslations_map_reflConj.1 hv, ?_⟩, spaceRefl_spaceRefl v⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_spaceRefl]
    rwa [Metric.mem_closedBall, dist_zero_right] at hvR
  · intro γ' hγ' v hv
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
    obtain ⟨w, hw, rfl⟩ := hv
    simp only [hRl, LinearEquiv.coe_coe]
    rw [linOf_reflConj, spaceRefl_spaceRefl, hfixE γ hγ w hw]
  · rcases hcase with ⟨hq, hE⟩ | ⟨hq, hE⟩
    · refine Or.inl ⟨?_, ?_⟩
      · have h2 := isQuotientOf_refl e he hq
        have hO : reflOpens (limitOpensPlus Γ) = limitOpensPlus (Γ.map (reflConj n)) :=
          Opens.ext (by
            show spaceRefl n ⁻¹' omegaPlus (limitSetJ Γ) =
              omegaPlus (limitSetJ (Γ.map (reflConj n)))
            rw [hP])
        rwa [hO] at h2
      · rintro _ ⟨w, hw, rfl⟩ p hp
        rw [hP] at hp ⊢
        simp only [mem_preimage, hRl, LinearEquiv.coe_coe, map_add, spaceRefl_spaceRefl] at hp ⊢
        exact hE w hw _ hp
    · refine Or.inr ⟨?_, ?_⟩
      · have h2 := isQuotientOf_refl e he hq
        have hO : reflOpens (limitOpensMinus Γ) = limitOpensMinus (Γ.map (reflConj n)) :=
          Opens.ext (by
            show spaceRefl n ⁻¹' omegaMinus (limitSetJ Γ) =
              omegaMinus (limitSetJ (Γ.map (reflConj n)))
            rw [hM])
        rwa [hO] at h2
      · rintro _ ⟨w, hw, rfl⟩ p hp
        rw [hM] at hp ⊢
        simp only [mem_preimage, hRl, LinearEquiv.coe_coe, map_add, spaceRefl_spaceRefl] at hp ⊢
        exact hE w hw _ hp

end CHRefl

/-! ### G9d: the finite-index reduction of family (b) → (a) -/

section G9dReduction

variable {d : ℕ}

/-- A covering map is injective near each point (copy of `Classification`'s). -/
private theorem exists_injOn_of_isCoveringMap' {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {π : X → Y} (h : IsCoveringMap π) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn π U := by
  obtain ⟨e, hx, he⟩ := h.isLocalHomeomorph x
  exact ⟨e.source, e.open_source, hx, fun a ha b hb hab => by
    rw [he] at hab; exact e.injOn ha hb hab⟩

/-- **A covering presentation acts freely** (copy of `Classification`'s
`isCancelSMul_of_isCoveringMap`, which this module cannot import). -/
private theorem isCancelSMul_of_isCoveringMap' {X : Type*} [TopologicalSpace X]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X}
    (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) : IsCancelSMul Γ Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ p hp
  obtain ⟨U, hUo, hpU, hinj⟩ := exists_injOn_of_isCoveringMap' hcov p
  have hc : Continuous fun q : Ω => γ • q := continuous_const_smul γ
  have hU' : IsOpen (U ∩ (fun q : Ω => γ • q) ⁻¹' U) := hUo.inter (hUo.preimage hc)
  have hfix : ∀ q ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U, γ • q = q := by
    rintro q ⟨hq1, hq2⟩
    exact hinj hq2 hq1 ((hfib q (γ • q)).2 ⟨γ, γ.2, rfl⟩).symm
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hU'
  have hpU' : p ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U :=
    ⟨hpU, by simp only [mem_preimage, hp]; exact hpU⟩
  rw [← hV] at hpU'
  have hpV : (p : Minkowski d) ∈ V ∩ Ω := ⟨hpU', p.2⟩
  apply Subtype.ext
  refine Causal.eq_of_eqOn (hVo.inter Ω.isOpen) ⟨_, hpV⟩ fun x hx => ?_
  have hx' : (⟨x, hx.2⟩ : Ω) ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U := by rw [← hV]; exact hx.1
  have := congrArg Subtype.val (hfix _ hx')
  simpa using this

/-- **A covering presentation acts properly discontinuously** (copy of `Classification`'s
`properlyDiscontinuousSMul_of_isCoveringMap`). -/
private theorem properlyDiscontinuousSMul_of_isCoveringMap' {X : Type*} [TopologicalSpace X]
    [T2Space X] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω]
    {π : Ω → X} (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) :
    ProperlyDiscontinuousSMul Γ Ω := by
  haveI := isCancelSMul_of_isCoveringMap' hcov hfib
  refine ⟨fun {K L} hK hL => ?_⟩
  by_contra hinf
  set T := {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}
  let e := Set.Infinite.natEmbedding T hinf
  have hmem : ∀ n, ∃ k ∈ K, ((e n : Γ)) • k ∈ L := fun n => by
    obtain ⟨_, ⟨k, hk, rfl⟩, hl⟩ := (e n).2
    exact ⟨k, hk, hl⟩
  choose k hkK hkL using hmem
  obtain ⟨a, -, φ, hφ, ha⟩ := hK.tendsto_subseq hkK
  obtain ⟨b, -, ψ, hψ, hb⟩ := hL.tendsto_subseq (fun n => hkL (φ n))
  set c : ℕ → Ω := fun n => k (φ (ψ n))
  set γn : ℕ → Γ := fun n => (e (φ (ψ n)) : Γ)
  have hc : Tendsto c atTop (𝓝 a) := ha.comp hψ.tendsto_atTop
  have hb' : Tendsto (fun n => γn n • c n) atTop (𝓝 b) := hb
  have hπ : ∀ n, π (γn n • c n) = π (c n) := fun n =>
    ((hfib (c n) (γn n • c n)).2 ⟨_, (γn n).2, rfl⟩).symm
  have h1 : Tendsto (fun n => π (c n)) atTop (𝓝 (π a)) := (hcov.continuous.tendsto a).comp hc
  have h2 : Tendsto (fun n => π (c n)) atTop (𝓝 (π b)) := by
    have := (hcov.continuous.tendsto b).comp hb'
    simpa only [comp_def, hπ] using this
  obtain ⟨γ, hγ, hγab⟩ := (hfib a b).1 (tendsto_nhds_unique h1 h2)
  set g : Γ := ⟨γ, hγ⟩
  have hga : g • a = b := Subtype.ext hγab
  obtain ⟨U, hUo, hbU, hinj⟩ := exists_injOn_of_isCoveringMap' hcov b
  have h3 : Tendsto (fun n => g • c n) atTop (𝓝 b) := by
    have := ((continuous_const_smul g).tendsto a).comp hc
    rwa [hga] at this
  have hev : ∀ᶠ n in atTop, γn n = g := by
    filter_upwards [h3.eventually (hUo.mem_nhds hbU), hb'.eventually (hUo.mem_nhds hbU)] with n
      hu1 hu2
    have hπ' : π (γn n • c n) = π (g • c n) := by
      rw [hπ, ((hfib (c n) (g • c n)).2 ⟨_, g.2, rfl⟩)]
    exact IsCancelSMul.right_cancel _ _ _ (hinj hu2 hu1 hπ')
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hEq : e (φ (ψ N)) = e (φ (ψ (N + 1))) :=
    Subtype.ext ((hN N le_rfl).trans (hN (N + 1) (by omega)).symm)
  have := hψ.injective (hφ.injective (e.injective hEq))
  omega

/-! ### The covering criterion for an intermediate quotient -/

section SheetsG9

variable {Γ G : Subgroup (isom d)} {W : Opens (Minkowski d)} [FlatQuotient.Invariant Γ W]
  [FlatQuotient.Invariant G W]

variable (Γ) in
/-- The sheet `[g V] ⊆ Γ\W` of a set `V ⊆ W` and `g ∈ G`. -/
private noncomputable def sheet (V : Set W) (g : G) : Set (FlatQuotient Γ W) :=
  FlatQuotient.proj Γ W '' ((fun a : W => g⁻¹ • a) ⁻¹' V)

/-- An element of `Γ`, read in `G`, acts on `W` as it does in `Γ`. -/
private theorem smul_coe_eq (hle : Γ ≤ G) (γ : Γ) (a : W) :
    γ • a = (⟨γ, hle γ.2⟩ : G) • a := rfl

/-- Left translation by `Γ` does not move a sheet (one inclusion). -/
private theorem sheet_mul_subset (hle : Γ ≤ G) (V : Set W) (γ : Γ) (g : G) :
    sheet Γ V (⟨γ, hle γ.2⟩ * g) ⊆ sheet Γ V g := by
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨γ⁻¹ • c, ?_, ?_⟩
  · show g⁻¹ • (γ⁻¹ • c) ∈ V
    have : g⁻¹ • (γ⁻¹ • c) = (⟨γ, hle γ.2⟩ * g)⁻¹ • c := by
      rw [smul_coe_eq hle, mul_inv_rev, mul_smul]
      rfl
    rw [this]
    exact hc
  · exact (FlatQuotient.proj_eq_proj_iff.2 ⟨γ⁻¹, rfl⟩).symm.symm

/-- Left translation by `Γ` does not move a sheet. -/
private theorem sheet_mul (hle : Γ ≤ G) (V : Set W) (γ : Γ) (g : G) :
    sheet Γ V (⟨γ, hle γ.2⟩ * g) = sheet Γ V g := by
  refine (sheet_mul_subset hle V γ g).antisymm ?_
  have := sheet_mul_subset hle V γ⁻¹ (⟨γ, hle γ.2⟩ * g)
  rwa [← mul_assoc, show (⟨((γ⁻¹ : Γ) : isom d), hle (γ⁻¹).2⟩ : G) * ⟨γ, hle γ.2⟩ = 1 from
    Subtype.ext (by simp), one_mul] at this

/-- **Two sheets which meet are equal**, when `π` is injective on `V` with fibres the
`G`-orbits and `G` acts freely. -/
private theorem sheet_eq_of_meet (hle : Γ ≤ G) {Y : Type*} {π : W → Y}
    (hπg : ∀ (g : G) (a : W), π (g • a) = π a) (hfree : ∀ (g : G) (a : W), g • a = a → g = 1)
    {V : Set W} (hVi : InjOn π V) {g g' : G} {a b : W} (ha : g⁻¹ • a ∈ V) (hb : g'⁻¹ • b ∈ V)
    (hba : FlatQuotient.proj Γ W b = FlatQuotient.proj Γ W a) :
    sheet Γ V g = sheet Γ V g' := by
  obtain ⟨γ, hγ⟩ := FlatQuotient.proj_eq_proj_iff.1 hba
  have hab : g'⁻¹ • b = g⁻¹ • a := by
    refine hVi hb ha ?_
    rw [hπg, hπg, ← hγ, smul_coe_eq hle, hπg]
  have hfix : (g'⁻¹ * ⟨γ, hle γ.2⟩ * g : G) • (g⁻¹ • a) = g⁻¹ • a := by
    rw [mul_smul, mul_smul, smul_inv_smul, ← smul_coe_eq hle, hγ, hab]
  have hg' : g' = ⟨γ, hle γ.2⟩ * g := by
    have := hfree _ _ hfix
    rwa [mul_assoc, inv_mul_eq_one] at this
  rw [hg', sheet_mul hle]

end SheetsG9

/-- **An intermediate quotient covers.** If `π : W → Y` is continuous, open, onto, locally
injective, with fibres the orbits of a group `G` acting freely on `W`, then for `Γ ≤ G` the
induced `p : Γ\W → Y` is a covering map: over `U = π(V)`, `V` a neighbourhood on which `π` is
injective, the sheets are the sets `[g V]`, `g ∈ G`, two of which are equal or disjoint
(freeness, `sheet_eq_of_meet`), each mapped bijectively onto `U`. -/
private theorem isCoveringMap_of_factor {Γ G : Subgroup (isom d)} (hle : Γ ≤ G)
    {W : Opens (Minkowski d)} [FlatQuotient.Invariant Γ W] [FlatQuotient.Invariant G W]
    {Y : Type*} [TopologicalSpace Y] {π : W → Y} (hπc : Continuous π) (hπo : IsOpenMap π)
    (hπs : Surjective π) (hfib : ∀ a b : W, π a = π b ↔ ∃ g : G, g • a = b)
    (hfree : ∀ (g : G) (a : W), g • a = a → g = 1)
    (hloc : ∀ w : W, ∃ V : Set W, IsOpen V ∧ w ∈ V ∧ InjOn π V)
    {p : FlatQuotient Γ W → Y} (hp : ∀ a, p (FlatQuotient.proj Γ W a) = π a) :
    IsCoveringMap p := by
  have hπg : ∀ (g : G) (a : W), π (g • a) = π a := fun g a => ((hfib a (g • a)).2 ⟨g, rfl⟩).symm
  have hpπ : p ∘ FlatQuotient.proj Γ W = π := funext hp
  have hpc : Continuous p :=
    ((FlatQuotient.isOpenMap_proj Γ W).isQuotientMap (FlatQuotient.continuous_proj Γ W)
      (FlatQuotient.proj_surjective Γ W)).continuous_iff.2 (hpπ ▸ hπc)
  have hpo : IsOpenMap p := by
    intro O hO
    have : p '' O = π '' (FlatQuotient.proj Γ W ⁻¹' O) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := FlatQuotient.proj_surjective Γ W x
        exact ⟨a, hx, (hp a).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ha, hp a⟩
    rw [this]
    exact hπo _ (hO.preimage (FlatQuotient.continuous_proj Γ W))
  intro y
  obtain ⟨w, rfl⟩ := hπs y
  obtain ⟨V, hVo, hwV, hVi⟩ := hloc w
  refine isEvenlyCovered_of_sheets hpc hpo (hπo V hVo) ⟨w, hwV, rfl⟩
    (ι := {T : Set (FlatQuotient Γ W) // ∃ g : G, T = sheet Γ V g}) (fun T => T.1)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨_, g, rfl⟩
    exact FlatQuotient.isOpenMap_proj Γ W _ (hVo.preimage (continuous_const_smul _))
  · rintro ⟨_, g, rfl⟩ _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [hp] at hab
    have h1 : g⁻¹ • a = g⁻¹ • b := hVi ha hb (by rw [hπg, hπg, hab])
    rw [smul_left_cancel_iff] at h1
    rw [h1]
  · rintro ⟨_, g, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨FlatQuotient.proj Γ W (g • v), ⟨g • v, ?_, rfl⟩, ?_⟩
    · show g⁻¹ • g • v ∈ V
      rw [inv_smul_smul]
      exact hv
    · rw [hp, hπg]
  · rintro ⟨_, g, rfl⟩ ⟨_, g', rfl⟩ hne
    rw [Function.onFun, disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact hne (Subtype.ext (sheet_eq_of_meet hle hπg hfree hVi ha hb hba))
  · intro x hx
    obtain ⟨b, hbx⟩ := FlatQuotient.proj_surjective Γ W x
    obtain ⟨v, hv, hvb⟩ := hx
    rw [← hbx, hp] at hvb
    rw [← hbx]
    obtain ⟨g, hg⟩ := (hfib v b).1 hvb
    refine mem_iUnion.2 ⟨⟨sheet Γ V g, g, rfl⟩, b, ?_, rfl⟩
    show g⁻¹ • b ∈ V
    rw [← hg, inv_smul_smul]
    exact hv

/-- **Finite-index subgroups of a quotient presentation give finite covers**: if `B = Γ\Ω` with
`Ω` connected and `Γ' ≤ Γ` of finite index, then `M₁' = Γ'\Ω` is a flat spacetime finitely
covering `B` (`q [p] = π p`; fibres covered by the image of the finite `Γ ⧸ Γ'`). -/
theorem exists_finiteCover_of_le {B : FlatSpacetime.{0} d} {Γ Γ' : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} (hq : IsQuotientOf B Γ Ω) (hΩ : IsConnected (Ω : Set (Minkowski d)))
    (hle : Γ' ≤ Γ) (hidx : Γ'.relIndex Γ ≠ 0) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → B), IsFiniteCover d q ∧ IsQuotientOf M₁' Γ' Ω := by
  haveI hinv : FlatQuotient.Invariant Γ Ω := hq.invariant
  obtain ⟨π, hcov, hloc, hπs, hfib⟩ := hq.quot
  haveI hcanc : IsCancelSMul Γ Ω := isCancelSMul_of_isCoveringMap' hcov hfib
  haveI hprop : ProperlyDiscontinuousSMul Γ Ω :=
    properlyDiscontinuousSMul_of_isCoveringMap' hcov hfib
  haveI : FlatQuotient.Invariant Γ' Ω := ⟨fun γ p hp => hinv.smul_mem ⟨γ, hle γ.2⟩ p hp⟩
  haveI : IsCancelSMul Γ' Ω := by
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro γ p h
    have := (isCancelSMul_iff_eq_one_of_smul_eq.1 hcanc) ⟨γ, hle γ.2⟩ p h
    exact Subtype.ext (congrArg (fun g : Γ => (g : isom d)) this)
  haveI : ProperlyDiscontinuousSMul Γ' Ω := ⟨fun {K L} hK hL => by
    have hF := hprop.finite_disjoint_inter_image hK hL
    refine (hF.preimage (Subgroup.inclusion_injective hle).injOn).subset ?_
    intro γ hγ
    exact hγ⟩
  have hfib' : ∀ a b : Ω, π a = π b ↔ ∃ g : Γ, g • a = b := by
    intro a b
    rw [hfib]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨g, h⟩; exact ⟨g, g.2, congrArg Subtype.val h⟩
  have hfree : ∀ (g : Γ) (a : Ω), g • a = a → g = 1 :=
    fun g a h => (isCancelSMul_iff_eq_one_of_smul_eq.1 hcanc) g a h
  have hπinj : ∀ w : Ω, ∃ V : Set Ω, IsOpen V ∧ w ∈ V ∧ InjOn π V :=
    exists_injOn_of_isCoveringMap' hcov
  have hπG : ∀ (g : Γ) (a : Ω), π (g • a) = π a := fun g a => ((hfib' a (g • a)).2 ⟨g, rfl⟩).symm
  have hrel : ∀ a b : Ω, (MulAction.orbitRel Γ' Ω) a b → π a = π b := by
    intro a b hab
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    rw [← hγ, smul_coe_eq hle, hπG]
  let p : FlatQuotient Γ' Ω → B := Quotient.lift π hrel
  have hp : ∀ a, p (FlatQuotient.proj Γ' Ω a) = π a := fun _ => rfl
  have hpcov : IsCoveringMap p := isCoveringMap_of_factor hle hcov.continuous hloc.isOpenMap hπs
    hfib' hfree hπinj hp
  have hplocal : IsLocalIsometry d p :=
    isLocalAIso_id_iff.1 (IsLocalAIso.of_comp_right (A := id) (fun g => ⟨g, fun _ => rfl⟩)
      (FlatQuotient.isLocalIsometry_proj Γ' Ω) (FlatQuotient.proj_surjective Γ' Ω)
      (isLocalAIso_id_iff.2 (show IsLocalIsometry d (p ∘ FlatQuotient.proj Γ' Ω) from hloc)))
  have hfin : ∀ y : B, (p ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨w₀, rfl⟩ := hπs y
    haveI : (Γ'.subgroupOf Γ).FiniteIndex := ⟨hidx⟩
    refine (Set.finite_range fun q : Γ ⧸ Γ'.subgroupOf Γ =>
      FlatQuotient.proj Γ' Ω (q.out⁻¹ • w₀)).subset ?_
    intro x hx
    obtain ⟨a, rfl⟩ := FlatQuotient.proj_surjective Γ' Ω x
    have hx' : π a = π w₀ := hx
    obtain ⟨g, hg⟩ := (hfib' w₀ a).1 hx'.symm
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ'.subgroupOf Γ) g⁻¹
    refine ⟨(g⁻¹ : Γ), ?_⟩
    show FlatQuotient.proj Γ' Ω ((QuotientGroup.mk (s := Γ'.subgroupOf Γ) g⁻¹).out⁻¹ • w₀) =
      FlatQuotient.proj Γ' Ω a
    rw [hh, mul_inv_rev, inv_inv, ← hg, FlatQuotient.proj_eq_proj_iff']
    refine ⟨((h : Γ) : isom d), Subgroup.mem_subgroupOf.1 h.2, ?_⟩
    simp only [FlatQuotient.coe_smul, mul_smul, Subgroup.coe_inv, smul_inv_smul]
  exact ⟨FlatQuotient.toFlatSpacetime Γ' Ω hΩ, p, ⟨hpcov, hplocal, hfin⟩,
    FlatQuotient.isQuotientOf_toFlatSpacetime Γ' Ω hΩ⟩

theorem smul_pow_of_translation {t : isom d} {v : Minkowski d} (ht : ∀ x, t • x = x + v) :
    ∀ (m : ℕ) (x : Minkowski d), (t ^ m) • x = x + (m : ℝ) • v
  | 0, x => by simp
  | m + 1, x => by
    rw [pow_succ, mul_smul, ht, smul_pow_of_translation ht m, Nat.cast_succ, add_smul, one_smul]
    abel

theorem mem_kerTranslations_of_smul {Γ : Subgroup (isom d)} {γ : isom d} (hγ : γ ∈ Γ)
    {v : Minkowski d} (h : ∀ x, γ • x = x + v) : v ∈ kerTranslations Γ := by
  have h0 : trOf γ = v := by
    have := smul_eq_lin_add γ 0
    rw [map_zero, zero_add, h, zero_add] at this
    exact this.symm
  refine ⟨γ, hγ, LinearEquiv.ext fun w => ?_, h0⟩
  have := smul_eq_lin_add γ w
  rw [h, h0] at this
  exact (add_right_cancel this).symm

theorem kerTranslations_mono {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ) :
    kerTranslations Γ' ⊆ kerTranslations Γ := fun _ ⟨γ, hγ, hL, hv⟩ => ⟨γ, hle hγ, hL, hv⟩

/-- **`span 𝒩(Γ') = span 𝒩(Γ)` for `Γ' ≤ Γ` of finite index** (l.3418–3419): a translation
`t ∈ ker L ∩ Γ` has a power `tᵐ ∈ Γ'`, `m > 0`, the translation by `m v`. -/
theorem span_kerTranslations_of_le {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) :
    Submodule.span ℝ (kerTranslations Γ') = Submodule.span ℝ (kerTranslations Γ) := by
  refine le_antisymm (Submodule.span_mono (kerTranslations_mono hle))
    (Submodule.span_le.2 fun v hv => ?_)
  obtain ⟨t, ht, hL, rfl⟩ := hv
  have htx : ∀ x, t • x = x + trOf t := fun x => by rw [smul_eq_lin_add, hL]; rfl
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx ht
  have h1 : (m : ℝ) • trOf t ∈ kerTranslations Γ' :=
    mem_kerTranslations_of_smul hmem.1 (smul_pow_of_translation htx m)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have : trOf t = (m : ℝ)⁻¹ • ((m : ℝ) • trOf t) := by
    rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem discreteTopology_linearImage_of_le {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (h : DiscreteTopology (linearImage Γ)) : DiscreteTopology (linearImage Γ') := by
  let f : linearImage Γ' → linearImage Γ := fun A => ⟨A, Subgroup.map_mono hle A.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hfi : Injective f := fun A B hAB =>
    Subtype.ext (congrArg (fun C : linearImage Γ => (C : lorentz d)) hAB)
  exact DiscreteTopology.of_continuous_injective hf hfi

/-- **[10.G], l.3418–3419: a finite-index `Γ' ≤ Γ` has the same repulsive points in `𝒥`** (a
copy of `Flat.Lox.RestrictLimitSet`'s `repJ_eq_of_relIndex_ne_zero`, which this module may not
import: a power `γᵏ ∈ Γ'` of a loxodromic `γ` is loxodromic, eigenvalue `λᵏ`). -/
private theorem loxRepSet_eq_of_relIndex_ne_zero' {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) : loxRepSet Γ' = loxRepSet Γ := by
  apply Subset.antisymm
  · rintro w ⟨γ, hγ, h⟩
    exact ⟨γ, hle hγ, h⟩
  · rintro w ⟨γ, hγ, -, l, hl0, hl1, hn, hf⟩
    obtain ⟨k, hk, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx hγ
    have hpow : ∀ m : ℕ, linOf (γ ^ m) (nullVec w.1) = l ^ m • nullVec w.1 ∧
        ∀ p : Minkowski d, minkB (nullVec w.1) ((γ ^ m) • p) - w.2 =
          (l ^ m)⁻¹ * (minkB (nullVec w.1) p - w.2) := by
      intro m
      induction m with
      | zero =>
        refine ⟨by simp; rfl, fun p => by simp⟩
      | succ m ih =>
        refine ⟨?_, fun p => ?_⟩
        · rw [pow_succ, show linOf (γ ^ m * γ) = linOf (γ ^ m) * linOf γ from rfl,
            LinearEquiv.mul_apply, hn, map_smul, ih.1, smul_smul, pow_succ, mul_comm]
        · rw [pow_succ, mul_smul, ih.2, hf, pow_succ, mul_inv]; ring
    have hlk0 : 0 < l ^ k := pow_pos hl0 k
    have hlk1 : l ^ k < 1 := pow_lt_one₀ hl0.le hl1 hk.ne'
    exact ⟨γ ^ k, hmem.1, isLoxodromic_of_null_eigen (linOf_mem _) (nullVec_ne_zero _)
      (minkQ_nullVec _) hlk0 hlk1.ne (hpow k).1, l ^ k, hlk0, hlk1, (hpow k).1, (hpow k).2⟩

/-- **G9d, the reduction**: a central extension `B = Γ\Ω^±(Λ(Γ))` (family (b)) with `Γ` finitely
generated and every finite-index subgroup of `L(Γ)` without global fixed point is finitely covered
by a torus product (a): Selberg (`exists_finiteIndex_torsionFree_linOf`) gives the torsion-free
finite-index `Γ'`, `Γ'\Ω` covers `B` (`exists_finiteCover_of_le`), and family (b) passes to `Γ'`
(`loxRepSet_eq_of_relIndex_ne_zero'`, `span_kerTranslations_of_le`). -/
theorem exists_torusProduct_cover_of_fg (hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} {Γ : Subgroup (isom d)} (hB : IsCHCentralExtensionOf B Γ)
    (hfg : Γ.FG)
    (hnf : ∀ Γ' : Subgroup (isom d), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 →
      ¬HasGlobalFixedPoint (linearImage Γ')) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → B), IsFiniteCover d q ∧ IsCHTorusProduct M₁' := by
  obtain ⟨Γ', hle, hidx, htf⟩ := exists_finiteIndex_torsionFree_linOf hSel hfg
  obtain ⟨E, hsp, hspan, hball, hfixE, hdisc, -, hcase⟩ := hB
  have hJ : limitSetJ Γ' = limitSetJ Γ := by
    rw [limitSetJ, limitSetJ, loxRepSet_eq_of_relIndex_ne_zero' hle hidx]
  have hO : limitOpensPlus Γ' = limitOpensPlus Γ ∧ limitOpensMinus Γ' = limitOpensMinus Γ :=
    ⟨Opens.ext (by simp only [limitOpensPlus, hJ]), Opens.ext (by simp only [limitOpensMinus, hJ])⟩
  have hcore : IsSpacelikeSubmodule E ∧ Submodule.span ℝ (kerTranslations Γ') = E ∧
      (∀ R : ℝ, (kerTranslations Γ' ∩ Metric.closedBall 0 R).Finite) ∧
      (∀ γ ∈ Γ', ∀ v ∈ E, linOf γ v = v) ∧
      DiscreteTopology (linearImage Γ') ∧ ¬HasGlobalFixedPoint (linearImage Γ') :=
    ⟨hsp, by rw [span_kerTranslations_of_le hle hidx, hspan],
      fun R => (hball R).subset (inter_subset_inter_left _ (kerTranslations_mono hle)),
      fun γ hγ => hfixE γ (hle hγ), discreteTopology_linearImage_of_le hle hdisc,
      hnf Γ' hle hidx⟩
  rcases hcase with ⟨hq, hE⟩ | ⟨hq, hE⟩
  · have hne : (limitOpensPlus Γ : Set (Minkowski d)).Nonempty := by
      obtain ⟨π, -, -, hπs, -⟩ := hq.quot
      obtain ⟨p, -⟩ := hπs (Classical.arbitrary B)
      exact ⟨p, p.2⟩
    have hconn : IsConnected (limitOpensPlus Γ : Set (Minkowski d)) :=
      ⟨hne, (convex_omegaPlus _).isPreconnected⟩
    obtain ⟨M₁', q, hq', hM⟩ := exists_finiteCover_of_le hq hconn hle hidx
    refine ⟨M₁', q, hq', Γ', ⟨E, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1,
      hcore.2.2.2.2.1, hcore.2.2.2.2.2, Or.inl ⟨by rw [hO.1]; exact hM, ?_⟩⟩, htf⟩
    rw [hJ]; exact hE
  · have hne : (limitOpensMinus Γ : Set (Minkowski d)).Nonempty := by
      obtain ⟨π, -, -, hπs, -⟩ := hq.quot
      obtain ⟨p, -⟩ := hπs (Classical.arbitrary B)
      exact ⟨p, p.2⟩
    have hconn : IsConnected (limitOpensMinus Γ : Set (Minkowski d)) :=
      ⟨hne, (convex_omegaMinus _).isPreconnected⟩
    obtain ⟨M₁', q, hq', hM⟩ := exists_finiteCover_of_le hq hconn hle hidx
    refine ⟨M₁', q, hq', Γ', ⟨E, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1,
      hcore.2.2.2.2.1, hcore.2.2.2.2.2, Or.inr ⟨by rw [hO.2]; exact hM, ?_⟩⟩, htf⟩
    rw [hJ]; exact hE

end G9dReduction

/-! ## G9d — the geometric input: finite generation and the reduction of (NE) -/

section G9dInput

variable {d : ℕ}

open scoped unitInterval

/-- **The lift of a split Cauchy surface along a covering is connected** (G9d (FG), the
connectedness that the obstruction asked for): if `ψ : S × ℝ ≃ₜ X` with `ψ(x, 0) = x` and
`π : E → X` is a covering with `E` connected, then `π⁻¹(S)` is preconnected. The deformation
`(t, e) ↦ ψ(σ(πe), (1 − t) τ(πe))` of `π` lifts (`IsCoveringMap.liftHomotopy`); its end map
`E → π⁻¹(S)` is onto, being the identity on `π⁻¹(S)` (uniqueness of lifts). -/
theorem isPreconnected_preimage_of_splitting {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [ConnectedSpace E] {π : E → X} (hπ : IsCoveringMap π) {S : Set X}
    (ψ : S × ℝ ≃ₜ X) (hψ : ∀ x : S, ψ (x, 0) = x) : IsPreconnected (π ⁻¹' S) := by
  have hc : Continuous π := hπ.continuous
  let H : C(I × E, X) :=
    ⟨fun te => ψ ((ψ.symm (π te.2)).1, (1 - (te.1 : ℝ)) * (ψ.symm (π te.2)).2), by fun_prop⟩
  have H0 : ∀ a, H (0, a) = π (ContinuousMap.id E a) := fun a => by
    simp [H]
  set L := hπ.liftHomotopy H (ContinuousMap.id E) H0 with hL
  have hlift : ∀ te, π (L te) = H te := fun te => congr_fun (hπ.liftHomotopy_lifts H _ H0) te
  have h1 : ∀ e, L (1, e) ∈ π ⁻¹' S := fun e => by
    rw [mem_preimage, hlift]
    simp only [H, ContinuousMap.coe_mk, Icc.coe_one, sub_self, zero_mul, hψ]
    exact Subtype.coe_prop _
  have h2 : ∀ e ∈ π ⁻¹' S, L (1, e) = e := by
    intro e he
    have hsy : ψ.symm (π e) = (⟨π e, he⟩, 0) := by
      rw [Homeomorph.symm_apply_eq, hψ]
    have hconst : ∀ t : I, H (t, e) = π e := fun t => by
      simp only [H, ContinuousMap.coe_mk, hsy, mul_zero, hψ]
    have := hπ.eq_of_comp_eq (g₁ := fun t : I => L (t, e)) (g₂ := fun _ => e)
      (L.continuous.comp (Continuous.prodMk_left e)) continuous_const
      (funext fun t => by simp only [comp_apply, hlift, hconst]) 0
      (hπ.liftHomotopy_zero H _ H0 e)
    exact congr_fun this 1
  have hrange : π ⁻¹' S = range fun e => L (1, e) := by
    ext e
    exact ⟨fun he => ⟨e, h2 e he⟩, by rintro ⟨e', rfl⟩; exact h1 e'⟩
  rw [hrange]
  exact isPreconnected_range (L.continuous.comp (Continuous.prodMk_right 1))

/-- **An elementary Švarc–Milnor lemma** (G9d (FG)): if `Γ` acts properly discontinuously on `T`,
`K ⊆ T` is preconnected and `Γ`-invariant, and an open `V` inside a compact `C` meets `K` and
meets every orbit of a point of `K`, then the finite set `{γ | γC ∩ C ≠ ∅}` generates `Γ`. The
translates `γV` with `γ` in the generated subgroup, and those with `γ` outside it, are disjoint
open sets covering `K`. -/
theorem fg_of_isPreconnected_of_properlyDiscontinuous {G : Type*} [Group G] {Γ : Subgroup G}
    {T : Type*} [TopologicalSpace T] [MulAction Γ T] [ContinuousConstSMul Γ T]
    [ProperlyDiscontinuousSMul Γ T] {K : Set T} (hK : IsPreconnected K)
    (hinv : ∀ γ : Γ, ∀ x ∈ K, γ • x ∈ K) {C V : Set T} (hC : IsCompact C) (hV : IsOpen V)
    (hVC : V ⊆ C) (hcov : ∀ x ∈ K, ∃ γ : Γ, γ • x ∈ V) (hne : (K ∩ V).Nonempty) : Γ.FG := by
  set T0 : Set Γ := {γ : Γ | ((γ • ·) '' C ∩ C).Nonempty} with hT0
  have hT0f : T0.Finite := ProperlyDiscontinuousSMul.finite_disjoint_inter_image hC hC
  set S0 : Set G := Subtype.val '' T0 with hS0
  set P : Γ → Prop := fun γ => (γ : G) ∈ Subgroup.closure S0 with hP
  have hT0P : ∀ γ : Γ, ∀ x ∈ V, γ • x ∈ V → P γ := fun γ x hx hγx =>
    Subgroup.subset_closure ⟨γ, ⟨γ • x, ⟨x, hVC hx, rfl⟩, hVC hγx⟩, rfl⟩
  have hPmul : ∀ γ δ : Γ, P γ → P δ → P (γ * δ) := fun γ δ h1 h2 => by
    simp only [hP, Subgroup.coe_mul]; exact Subgroup.mul_mem _ h1 h2
  have hPinv : ∀ γ : Γ, P γ → P γ⁻¹ := fun γ h => by
    simp only [hP, Subgroup.coe_inv]; exact Subgroup.inv_mem _ h
  set U1 : Set T := ⋃ γ ∈ {γ : Γ | P γ}, (fun x => γ⁻¹ • x) ⁻¹' V
  set U2 : Set T := ⋃ γ ∈ {γ : Γ | ¬ P γ}, (fun x => γ⁻¹ • x) ⁻¹' V
  have hU1 : IsOpen U1 := isOpen_biUnion fun γ _ => hV.preimage (continuous_const_smul _)
  have hU2 : IsOpen U2 := isOpen_biUnion fun γ _ => hV.preimage (continuous_const_smul _)
  have hdisj : Disjoint U1 U2 := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [U1, U2, mem_iUnion, mem_preimage, mem_setOf_eq, exists_prop] at hx1 hx2
    obtain ⟨γ, hγ, hγx⟩ := hx1
    obtain ⟨δ, hδ, hδx⟩ := hx2
    have h : P (δ⁻¹ * γ) := hT0P _ _ hγx (by rwa [mul_smul, smul_inv_smul])
    apply hδ
    have := hPmul _ _ hγ (hPinv _ h)
    simpa using this
  have hsub : K ⊆ U1 ∪ U2 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x hx
    by_cases h : P γ⁻¹
    · exact Or.inl (mem_biUnion (x := γ⁻¹) h (by simpa using hγ))
    · exact Or.inr (mem_biUnion (x := γ⁻¹) h (by simpa using hγ))
  obtain ⟨x₀, hx₀K, hx₀V⟩ := hne
  have hKU1 : K ⊆ U1 := hK.subset_left_of_subset_union hU1 hU2 hdisj hsub
    ⟨x₀, hx₀K, mem_biUnion (x := 1) (by simp [hP]) (by simpa using hx₀V)⟩
  have hall : ∀ γ : Γ, P γ := by
    intro γ
    have := hKU1 (hinv γ x₀ hx₀K)
    simp only [U1, mem_iUnion, mem_preimage, mem_setOf_eq, exists_prop] at this
    obtain ⟨δ, hδ, hδx⟩ := this
    have h : P (δ⁻¹ * γ) := hT0P _ _ hx₀V (by rwa [mul_smul])
    simpa using hPmul _ _ hδ h
  rw [Subgroup.fg_iff]
  refine ⟨S0, le_antisymm ?_ fun g hg => hall ⟨g, hg⟩, hT0f.image _⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨γ, -, rfl⟩
  exact γ.2
/-- **G9d (FG): the group of a Cauchy-compact quotient is finitely generated**: if `B = Γ\Ω` is
causal and Cauchy-compact and `Ω` is connected, then `Γ` is finitely generated. The lift `π⁻¹(K)`
of the compact Cauchy surface is connected (`isPreconnected_preimage_of_splitting`, along the
splitting `K × ℝ ≃ₜ B` of the chronal causal flow of every flat spacetime), and finitely many
relatively compact charts of `Ω` cover `K` (`fg_of_isPreconnected_of_properlyDiscontinuous`). -/
theorem fg_of_isQuotientOf_cauchyCompact {B : FlatSpacetime.{u} d}
    (hcaus : (flatCausality d B).IsCausal) (hC : CauchyCompact B) {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} (hq : IsQuotientOf B Γ Ω)
    (hΩ : IsConnected (Ω : Set (Minkowski d))) : Γ.FG := by
  haveI := hq.invariant
  haveI : ConnectedSpace Ω := isConnected_iff_connectedSpace.1 hΩ
  obtain ⟨S, hS, hSc, hac⟩ := hC
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := hq.quot
  haveI : ProperlyDiscontinuousSMul Γ Ω := properlyDiscontinuousSMul_of_isCoveringMap' hcov hfib
  have hflow : (flatCausality d B).HasChronalCausalFlow := flat_hasChronalCausalFlow
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting hflow hcaus hS hac
  have hK : IsPreconnected (π ⁻¹' S) := isPreconnected_preimage_of_splitting hcov ψ hψ.zero
  -- a compact `C` and an open `V ⊆ C` of `Ω` with `S ⊆ π V`
  have hnhds : ∀ e : Ω, ∃ C : Set Ω, IsCompact C ∧ C ∈ 𝓝 e := fun e => exists_compact_mem_nhds e
  choose Cf hCf hCn using hnhds
  have hopen : IsOpenMap π := hloc.isOpenMap
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun e : Ω => π '' interior (Cf e))
    (fun e => hopen _ isOpen_interior) (fun s _ => by
      obtain ⟨e, rfl⟩ := hsurj s
      exact mem_iUnion.2 ⟨e, e, mem_interior_iff_mem_nhds.2 (hCn e), rfl⟩)
  set V : Set Ω := ⋃ e ∈ t, interior (Cf e)
  set C : Set Ω := ⋃ e ∈ t, Cf e
  have hVo : IsOpen V := isOpen_biUnion fun _ _ => isOpen_interior
  have hCc : IsCompact C := t.isCompact_biUnion fun e _ => hCf e
  have hVC : V ⊆ C := biUnion_mono subset_rfl fun _ _ => interior_subset
  have hSV : ∀ s ∈ S, ∃ v ∈ V, π v = s := by
    intro s hs
    obtain ⟨e, he, v, hv, rfl⟩ := mem_iUnion₂.1 (ht hs)
    exact ⟨v, mem_biUnion he hv, rfl⟩
  refine fg_of_isPreconnected_of_properlyDiscontinuous hK ?_ hCc hVo hVC ?_ ?_
  · intro γ x hx
    rw [mem_preimage, ((hfib x (γ • x)).2 ⟨γ, γ.2, rfl⟩).symm]
    exact hx
  · intro x hx
    obtain ⟨v, hv, hvx⟩ := hSV (π x) hx
    obtain ⟨γ, hγ, hγv⟩ := (hfib v x).1 hvx
    refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_⟩
    have : (⟨γ, hγ⟩ : Γ) • v = x := Subtype.ext hγv
    rw [← this, inv_smul_smul]
    exact hv
  · obtain ⟨m⟩ : Nonempty B := inferInstance
    obtain ⟨v, hv, hvs⟩ := hSV _ (ψ.symm m).1.2
    exact ⟨v, by rw [mem_preimage, hvs]; exact (ψ.symm m).1.2, hv⟩

/-- A function on `Γ` that is right `H`-invariant, `H` of finite index in `Γ`, takes finitely many
values on `Γ` (one per coset). -/
theorem finite_image_of_relIndex_ne_zero {G X : Type*} [Group G] {Γ H : Subgroup G}
    (hH : H.relIndex Γ ≠ 0) (f : G → X) (hf : ∀ γ ∈ Γ, ∀ h ∈ H, f (γ * h) = f γ) :
    (f '' (Γ : Set G)).Finite := by
  haveI : (H.subgroupOf Γ).FiniteIndex := ⟨hH⟩
  refine (Set.finite_range fun q : Γ ⧸ H.subgroupOf Γ => f (q.out : G)).subset ?_
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf Γ) (⟨γ, hγ⟩ : Γ)
  refine ⟨(⟨γ, hγ⟩ : Γ), ?_⟩
  simp only [hh, Subgroup.coe_mul]
  exact hf γ hγ _ (Subgroup.mem_subgroupOf.1 h.2)

/-- `L(γδ) = L(γ) L(δ)`, applied. -/
private theorem linearPart_mul_apply (γ δ : isom d) (v : Minkowski d) :
    (linearPart (γ * δ) : Minkowski d ≃ₗ[ℝ] Minkowski d) v =
      (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d)
        ((linearPart δ : Minkowski d ≃ₗ[ℝ] Minkowski d) v) := by
  rw [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]

/-- The action on `𝒮` is an action: `[A B] = [A] ∘ [B]` (copy of `Lox.CentralFix`'s private one). -/
private theorem lorentzSphere_mul' (A B : lorentz d) (u : PenroseSphere d) :
    lorentzSphere (A * B) u = lorentzSphere A (lorentzSphere B u) := by
  have hA := (lorentzScale_pos A (lorentzSphere B u)).ne'
  have hB := (lorentzScale_pos B u).ne'
  have hAB := (lorentzScale_pos (A * B) u).ne'
  refine nullVec_injective_smul
    (c := (lorentzScale (A * B) u)⁻¹ * (lorentzScale A (lorentzSphere B u) * lorentzScale B u)) ?_
  rw [nullVec_lorentzSphere, nullVec_lorentzSphere A, nullVec_lorentzSphere B, map_smul,
    smul_smul, smul_smul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  congr 1
  field_simp

/-- **G9d (NE), timelike case**: if a finite-index subgroup `Γ'` of `Γ` has linear parts fixing
a timelike vector, `L(Γ)` has a global fixed point: the sum of the finite `L(Γ)`-orbit of the
future one of `±v` is future timelike (`isFutureTimelike_add`) and `L(Γ)`-fixed. -/
theorem hasGlobalFixedPoint_of_fixed_timelike {Γ Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0)
    {v : Minkowski d} (hv : minkQ v < 0)
    (hfix : ∀ γ ∈ Γ', (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v) :
    HasGlobalFixedPoint (linearImage Γ) := by
  obtain ⟨w, hw, hfw⟩ : ∃ w, IsFutureTimelike w ∧
      ∀ γ ∈ Γ', (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w := by
    rcases isFutureTimelike_or_neg hv with h | h
    · exact ⟨v, h, hfix⟩
    · exact ⟨-v, h, fun γ hγ => by rw [map_neg, hfix γ hγ]⟩
  set f : isom d → Minkowski d := fun γ => (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) w
  have hO : (f '' (Γ : Set (isom d))).Finite := finite_image_of_relIndex_ne_zero hidx f
    (fun γ _ h hh => by simp only [f, linearPart_mul_apply, hfw h hh])
  set O := hO.toFinset
  have hOmem : ∀ x, x ∈ O ↔ ∃ γ ∈ Γ, f γ = x := fun x => by simp [O]
  have hOne : O.Nonempty := ⟨f 1, (hOmem _).2 ⟨1, Γ.one_mem, rfl⟩⟩
  have hft : IsFutureTimelike (∑ x ∈ O, x) := by
    refine Finset.sum_induction_nonempty _ IsFutureTimelike
      (fun a b ha hb => isFutureTimelike_add ha ⟨hb.1.le, hb.2.le⟩) hOne ?_
    intro x hx
    obtain ⟨γ, -, rfl⟩ := (hOmem x).1 hx
    exact lorentz.isFutureTimelike_apply (linearPart γ).2 hw
  refine Or.inl ⟨∑ x ∈ O, x, hft.2, ?_⟩
  rintro _ ⟨γ, hγ, rfl⟩
  set A := (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d)
  have himg : O.image A = O := by
    ext x
    simp only [Finset.mem_image, hOmem]
    constructor
    · rintro ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩
      exact ⟨γ * δ, Γ.mul_mem hγ hδ, by simp only [f, A, linearPart_mul_apply]⟩
    · rintro ⟨δ, hδ, rfl⟩
      refine ⟨f (γ⁻¹ * δ), ⟨γ⁻¹ * δ, Γ.mul_mem (Γ.inv_mem hγ) hδ, rfl⟩, ?_⟩
      simp only [f, A, ← linearPart_mul_apply, mul_inv_cancel_left]
  rw [map_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun x _ y _ h => A.injective h)]

/-- **Three fixed points of `𝒮` give a fixed timelike vector**: a Lorentz map fixing three
distinct points of `𝒮` has eigenvalues `cᵢ cⱼ = 1` on their null lines (`⟨nᵢ | nⱼ⟩ ≠ 0` is
preserved), so all `cᵢ = 1` and `n₁ + n₂` is fixed. -/
theorem fixes_add_of_three_fixed {A : lorentz d} {u₁ u₂ u₃ : PenroseSphere d} (h12 : u₁ ≠ u₂)
    (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) (h1 : lorentzSphere A u₁ = u₁)
    (h2 : lorentzSphere A u₂ = u₂) (h3 : lorentzSphere A u₃ = u₃) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁ + nullVec u₂) = nullVec u₁ + nullVec u₂ := by
  have heig : ∀ {u}, lorentzSphere A u = u →
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u := by
    intro u hu
    have := nullVec_lorentzSphere A u
    rw [hu] at this
    calc (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)
        = lorentzScale A u • ((lorentzScale A u)⁻¹ •
            (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) := by
          rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]
      _ = lorentzScale A u • nullVec u := by rw [← this]
  have hprod : ∀ {u u'}, u ≠ u' → lorentzSphere A u = u → lorentzSphere A u' = u' →
      lorentzScale A u * lorentzScale A u' = 1 := by
    intro u u' hne hu hu'
    have hB := lorentz.minkB_apply A.2 (nullVec u) (nullVec u')
    rw [heig hu, heig hu', minkB_smul_left, minkB_smul_right] at hB
    have hne0 : minkB (nullVec u) (nullVec u') ≠ 0 := by
      rw [minkB_nullVec_nullVec]
      have : 0 < ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 fun h => hne (Subtype.ext h))
      have := pow_pos this 2
      intro h; linarith
    have : (lorentzScale A u * lorentzScale A u' - 1) * minkB (nullVec u) (nullVec u') = 0 := by
      linear_combination hB
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hne0
  have p12 := hprod h12 h1 h2
  have p13 := hprod h13 h1 h3
  have p23 := hprod h23 h2 h3
  have c1 := lorentzScale_pos A u₁
  have c2 := lorentzScale_pos A u₂
  have c3 := lorentzScale_pos A u₃
  have e23 : lorentzScale A u₂ = lorentzScale A u₃ := by
    have : lorentzScale A u₁ * (lorentzScale A u₂ - lorentzScale A u₃) = 0 := by
      linear_combination p12 - p13
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have e2 : lorentzScale A u₂ = 1 := by
    rw [← e23] at p23
    nlinarith
  have e1 : lorentzScale A u₁ = 1 := by rw [e2, mul_one] at p12; exact p12
  rw [map_add, heig h1, heig h2, e1, e2, one_smul, one_smul]

/-- The sum of the null vectors of two distinct points of `𝒮` is timelike (parallelogram law). -/
theorem minkQ_nullVec_add_neg {u₁ u₂ : PenroseSphere d} (h : u₁ ≠ u₂) :
    minkQ (nullVec u₁ + nullVec u₂) < 0 := by
  have hpar := parallelogram_law_with_norm ℝ (u₁ : EuclideanSpace ℝ (Fin d)) u₂
  rw [norm_penroseSphere, norm_penroseSphere] at hpar
  have hpos : 0 < ‖(u₁ : EuclideanSpace ℝ (Fin d)) - u₂‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun e => h (Subtype.ext e))
  have := mul_pos hpos hpos
  simp only [minkQ, nullVec, Prod.fst_add, Prod.snd_add]
  nlinarith


/-- **G9d (NE), the reduction to an invariant pair**: if `L(Γ)` has no global fixed point, a
finite-index subgroup `Γ'` acquires one only if some finite-index `N ≤ Γ` (the normal core of
`Γ'`) has linear parts fixing two distinct points `u₁ ≠ u₂` of `𝒮` whose pair `L(Γ)` preserves
(`hpair` rules that out). A fixed timelike vector of `L(Γ')` is excluded by
`hasGlobalFixedPoint_of_fixed_timelike`; a fixed `u ∈ 𝒮` has a finite `L(Γ)`-orbit fixed
pointwise by the normal core `N`, which is one point (a global fixed point), at least three
(`fixes_add_of_three_fixed`: a timelike vector fixed by `N`), or the pair. -/
theorem not_hasGlobalFixedPoint_of_relIndex_ne_zero {Γ : Subgroup (isom d)}
    (hnf : ¬HasGlobalFixedPoint (linearImage Γ))
    (hpair : ∀ N : Subgroup (isom d), N ≤ Γ → N.relIndex Γ ≠ 0 →
      ∀ u₁ u₂ : PenroseSphere d, u₁ ≠ u₂ →
      (∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂) →
      (∀ γ ∈ Γ, ∀ u ∈ ({u₁, u₂} : Set (PenroseSphere d)),
        lorentzSphere (linearPart γ) u ∈ ({u₁, u₂} : Set (PenroseSphere d))) → False)
    {Γ' : Subgroup (isom d)} (hidx : Γ'.relIndex Γ ≠ 0) :
    ¬HasGlobalFixedPoint (linearImage Γ') := by
  rintro (⟨v, hv, hfix⟩ | ⟨u, hfix⟩)
  · exact hnf (hasGlobalFixedPoint_of_fixed_timelike hidx hv fun γ hγ => hfix _ ⟨γ, hγ, rfl⟩)
  haveI : (Γ'.subgroupOf Γ).FiniteIndex := ⟨hidx⟩
  set K := (Γ'.subgroupOf Γ).normalCore with hK
  set N := K.map Γ.subtype with hN
  have hNle : N ≤ Γ := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hNidx : N.relIndex Γ ≠ 0 := by
    have : N.subgroupOf Γ = K := Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective K
    rw [Subgroup.relIndex, this]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hfixu : ∀ γ ∈ Γ', lorentzSphere (linearPart γ) u = u := fun γ hγ => hfix _ ⟨γ, hγ, rfl⟩
  set f : isom d → PenroseSphere d := fun γ => lorentzSphere (linearPart γ) u with hf
  have hfmul : ∀ γ δ, f (γ * δ) = lorentzSphere (linearPart γ) (f δ) := fun γ δ => by
    simp only [f, map_mul, lorentzSphere_mul']
  have hf1 : f 1 = u := by
    simp only [f, map_one]
    exact lorentzSphere_eq_of_eigen (c := 1) (by simp)
  have hNfix : ∀ n ∈ N, ∀ γ ∈ Γ, lorentzSphere (linearPart n) (f γ) = f γ := by
    rintro _ ⟨k, hk, rfl⟩ γ hγ
    have hc := hk (⟨γ, hγ⟩ : Γ)⁻¹
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hc
    rw [Subgroup.coe_subtype, ← hfmul]
    have : (k : isom d) * γ = γ * (γ⁻¹ * k * γ) := by group
    rw [this, hfmul, show f (γ⁻¹ * k * γ) = u from hfixu _ hc]
  by_cases hall : ∀ γ ∈ Γ, f γ = u
  · exact hnf (Or.inr ⟨u, by rintro _ ⟨γ, hγ, rfl⟩; exact hall γ hγ⟩)
  push Not at hall
  obtain ⟨γ₁, hγ₁, hx⟩ := hall
  by_cases h3 : ∃ γ ∈ Γ, f γ ≠ u ∧ f γ ≠ f γ₁
  · obtain ⟨γ₂, hγ₂, hyu, hyx⟩ := h3
    refine hnf (hasGlobalFixedPoint_of_fixed_timelike hNidx
      (minkQ_nullVec_add_neg (Ne.symm hx)) fun n hn => ?_)
    have h1 := hNfix n hn 1 Γ.one_mem
    rw [hf1] at h1
    exact fixes_add_of_three_fixed (Ne.symm hx) (Ne.symm hyu) (Ne.symm hyx) h1
      (hNfix n hn γ₁ hγ₁) (hNfix n hn γ₂ hγ₂)
  push Not at h3
  refine hpair N hNle hNidx u (f γ₁) (Ne.symm hx) (fun n hn => ?_) ?_
  · have h1 := hNfix n hn 1 Γ.one_mem
    rw [hf1] at h1
    exact ⟨h1, hNfix n hn γ₁ hγ₁⟩
  · have hmem : ∀ γ ∈ Γ, f γ ∈ ({u, f γ₁} : Set (PenroseSphere d)) := fun γ hγ => by
      by_cases h : f γ = u
      · exact Or.inl h
      · exact Or.inr (h3 γ hγ h)
    rintro γ hγ w (rfl | rfl)
    · exact hmem γ hγ
    · rw [← hfmul]; exact hmem _ (Γ.mul_mem hγ hγ₁)

end G9dInput

/-! ## G9 -/

section G9

variable {d : ℕ}

/-- **G9d (NE), the residual case: a finite-index subgroup fixing an `L(Γ)`-invariant pair of
`𝒮`** (DEC-44; l.3454–3456; l.3536–3548). For a GH Cauchy-compact central extension
`B = Γ\Ω^±(Λ(Γ))` (family (b)), no finite-index `N ≤ Γ` has linear parts fixing two distinct
points `u₁ ≠ u₂` of `𝒮` whose pair `L(Γ)` preserves. **The one `sorry` of this module.** It is a
special case of (NE), so it is true (Barbot: `L(Γ)` acts cocompactly on some `𝐇ᵏ`, `k ≥ 2`); every
other case of (NE) is reduced to it (`not_hasGlobalFixedPoint_of_relIndex_ne_zero`). -/
theorem false_of_cauchyCompact_of_fixed_pair {B : FlatSpacetime.{0} d} (_hGH : GH B)
    (_hC : CauchyCompact B) {Γ : Subgroup (isom d)} (_hB : IsCHCentralExtensionOf B Γ)
    {N : Subgroup (isom d)} (_hle : N ≤ Γ) (_hidx : N.relIndex Γ ≠ 0) {u₁ u₂ : PenroseSphere d}
    (_hne : u₁ ≠ u₂)
    (_hfix : ∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂)
    (_hpair : ∀ γ ∈ Γ, ∀ u ∈ ({u₁, u₂} : Set (PenroseSphere d)),
      lorentzSphere (linearPart γ) u ∈ ({u₁, u₂} : Set (PenroseSphere d))) : False := by
  sorry -- SORRY(bthm:cauclo, G9d-NE pair): the elementary-loxodromic configuration must contradict Cauchy-compactness, and the library has no argument for it. Setting: `N` normal of finite index in `Γ` (Barbot's elementary case [10.M] with a swap: `L(Γ)` preserves `{u₁, u₂}`, some element exchanges them since `L(Γ)` has no global fixed point), `L(γ) nᵢ = λ(γ)^{±1} nᵢ` on `N` with some `λ ≠ 1` (else `n₁ + n₂` is fixed, `hasGlobalFixedPoint_of_fixed_timelike`), `L(N)` virtually cyclic (discrete in `SO₀(1,1) × O(P^⊥)`, `P = span(n₁, n₂)`), `E ⊆ P^⊥`, `E ≠ P^⊥` (the swap reverses `P^⊥`'s orientation and fixes `E`). Then `Γ` is virtually `ℤ^{1 + dim E}` with `1 + dim E ≤ d − 1 + 1 = d` and equality impossible, so it cannot act cocompactly on the lifted Cauchy surface `≅ ℝᵈ` — Barbot's route is that `K` compact makes `L(Γ)` act cocompactly on a totally geodesic `𝐇ᵏ`, `k ≥ 2`. Missing: (i) `Λ(Γ) ⊆ {u₁, u₂} × ℝ` from the repulsive points of the loxodromics of `Γ` (powers in `N`), so `Ω` is a wedge `W × A` over the codimension-2 spacelike `A`; (ii) an invariant of the action on `Ω` that is constant along a causal line and has non-compact image — the `P^⊥`-coordinate alone fails when `N` acts cocompactly on `A` (a boost composed with a translation along `A`), and the mixed coordinate `y − log(−⟨p − c, n₁⟩)/log λ` is continuous on `Ω` only and needs a common centre `c`; `isCompact_image_of_isQuotientOf` asks for `F` continuous on `𝐌ⁿ`; (iii) or a cohomological-dimension / growth argument (a free cocompact action of a virtually `ℤᵐ` group on a contractible `d`-manifold forces `m = d`), not in mathlib

/-- **G9d, the geometric input** (DEC-44; l.3454–3456; l.3536–3548): for a GH Cauchy-compact
central extension `B = Γ\Ω^±(Λ(Γ))` (family (b)), `Γ` is finitely generated and no finite-index
subgroup of `L(Γ)` has a global fixed point on `𝐇̄`. (FG) is proved
(`fg_of_isQuotientOf_cauchyCompact`); (NE) is reduced (`not_hasGlobalFixedPoint_of_relIndex_ne_zero`)
to the residual pair case `false_of_cauchyCompact_of_fixed_pair`, **the one `sorry` of this
module**, which this theorem reaches. The second conjunct is not a consequence of family (b) alone
(module SCOPE, finding). -/
theorem fg_and_nonelementary_of_cauchyCompact {B : FlatSpacetime.{0} d} (_hGH : GH B)
    (_hC : CauchyCompact B) {Γ : Subgroup (isom d)} (_hB : IsCHCentralExtensionOf B Γ) :
    Γ.FG ∧ ∀ Γ' : Subgroup (isom d), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 →
      ¬HasGlobalFixedPoint (linearImage Γ') := by
  obtain ⟨E, -, -, -, -, -, hnf, hcase⟩ := id _hB
  refine ⟨?_, fun Γ' _ hidx => not_hasGlobalFixedPoint_of_relIndex_ne_zero hnf
    (fun N hle hNidx u₁ u₂ hne hfix hpair =>
      false_of_cauchyCompact_of_fixed_pair _hGH _hC _hB hle hNidx hne hfix hpair) hidx⟩
  rcases hcase with ⟨hq, -⟩ | ⟨hq, -⟩
  · obtain ⟨π, -, -, hπs, -⟩ := hq.quot
    obtain ⟨p, -⟩ := hπs (Classical.arbitrary B)
    exact fg_of_isQuotientOf_cauchyCompact _hGH.1 _hC hq ⟨⟨p, p.2⟩, (convex_omegaPlus _).isPreconnected⟩
  · obtain ⟨π, -, -, hπs, -⟩ := hq.quot
    obtain ⟨p, -⟩ := hπs (Classical.arbitrary B)
    exact fg_of_isQuotientOf_cauchyCompact _hGH.1 _hC hq ⟨⟨p, p.2⟩, (convex_omegaMinus _).isPreconnected⟩

/-- **G9d, family (b) → (a) under Cauchy-compactness** (DEC-44; l.3454–3456; Theorem B's
"Cauchy-hyperbolic × torus", l.355–359): a GH Cauchy-compact central extension `B` over a
Cauchy-hyperbolic spacetime is finitely covered by a torus product. The reduction
`exists_torusProduct_cover_of_fg` (Selberg, the finite cover `Γ'\Ω → B`, family (b) for `Γ'`) on
the input `fg_and_nonelementary_of_cauchyCompact`. -/
theorem exists_torusProduct_cover_of_isCHCentralExtension (hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} (hGH : GH B) (hC : CauchyCompact B)
    (hB : IsCHCentralExtension B) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → B), IsFiniteCover d q ∧ IsCHTorusProduct M₁' := by
  obtain ⟨Γ, hΓ⟩ := hB
  obtain ⟨hfg, hnf⟩ := fg_and_nonelementary_of_cauchyCompact hGH hC hΓ
  exact exists_torusProduct_cover_of_fg hSel hΓ hfg hnf

/-- **The base-level core, G9a's frame transport + G9d** (l.3536–3548; DEC-44): a GH
Cauchy-compact linear twisted product `B`, with data `(Γ, Ω, ι)` and **trivial** `U^⊥`, over a
model `M₁` of Theorem A, is itself a translation, Misner or unipotent spacetime, or is finitely
covered by a torus product (a). With `U^⊥ = 0`, `d₁ = d` (`eq_of_perp`), `ι` is bijective and
`π₁(x) ↦ π(ι x)` is a homeomorphism `e : M₁ ≃ B` (`exists_homeomorph_of_isLTPData`). If
`det L(ι) = 1`, `ι ∈ Isom(𝐌ⁿ)` and `e` is an isometry, along which every family transports. If
`det L(ι) = −1` (`ι` reverses the spatial orientation of `U`), `ι ∘ R₀ ∈ Isom(𝐌ⁿ)` for the spatial
reflection `R₀`, `e` is locally of type `R₀`, and `B = (R₀ G R₀)\R₀(Ω₁)` for every presentation
`G\Ω₁` of `M₁` (`isQuotientOf_refl`): the translation, Misner and central-extension families are
`R₀`-conjugation stable (`isTranslationSpacetime_refl`, `isMisnerSpacetime_refl`,
`isCHCentralExtensionOf_refl`), and a unipotent `M₁` makes `B` non-Cauchy-compact
(`not_cauchyCompact_of_refl_unipotent`). Family (b) is then G9d,
`exists_torusProduct_cover_of_isCHCentralExtension`. -/
theorem exists_family_of_isLTPData_of_perp (hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} (hGH : GH B) (hC : CauchyCompact B) {d₁ : ℕ}
    {M₁ : FlatSpacetime.{0} d₁} {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    {ι : AffineMinkEmbedding d₁ d} (hd : IsLTPData B M₁ Γ Ω ι) (hperp : ∀ w ∈ ι.perp, w = 0)
    (hfam : IsTranslationSpacetime M₁ ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsMisnerSpacetime M) ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsUnipotentSpacetime M) ∨
      IsCHCentralExtension M₁) :
    IsTranslationSpacetime B ∨
      (match d, B with
        | 0, _ => False
        | _ + 1, M => IsMisnerSpacetime M) ∨
      (match d, B with
        | 0, _ => False
        | _ + 1, M => IsUnipotentSpacetime M) ∨
      ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → B), IsFiniteCover d q ∧ IsCHTorusProduct M₁' := by
  obtain rfl := eq_of_perp ι hperp
  have hs := surjective_of_perp ι hperp
  obtain ⟨e, he⟩ := exists_homeomorph_of_isLTPData hd hs
  rcases det_lin_eq_one_or ι with hdet | hdet
  · obtain ⟨g₀, hg₀⟩ := exists_isom_of_det_one ι hd.orthochronous hs hdet
    have hLI : IsLocalIsometry d₁ e :=
      isLocalAIso_id_iff.1 (he id (fun g => ⟨g, fun _ => rfl⟩) ⟨g₀, hg₀⟩)
    rcases hfam with hT | hM | hU | hCH
    · exact Or.inl (isTranslationSpacetime_homeomorph e hLI hT)
    · refine Or.inr (Or.inl ?_)
      have h2 := misnerFamily_homeomorph e hLI (by cases d₁ <;> exact hM)
      cases d₁ <;> exact h2
    · refine Or.inr (Or.inr (Or.inl ?_))
      have h2 := unipotentFamily_homeomorph e hLI (by cases d₁ <;> exact hU)
      cases d₁ <;> exact h2
    · exact Or.inr (Or.inr (Or.inr (exists_torusProduct_cover_of_isCHCentralExtension hSel hGH hC
        (isCHCentralExtension_homeomorph e hLI hCH))))
  · cases d₁ with
    | zero => exact absurd (hdet.symm.trans (det_lin_eq_one_zero ι hd.orthochronous)) (by norm_num)
    | succ n =>
      obtain ⟨g₀, hg₀⟩ := exists_isom_of_det_neg_one ι hd.orthochronous hs hdet
      have hR : IsLocalAIso (n + 1) (spaceRefl n) e := he _ spaceRefl_normalizes ⟨g₀, hg₀⟩
      rcases hfam with hT | hM | hU | ⟨Γ₁, hCH⟩
      · exact Or.inl (isTranslationSpacetime_refl e hR hT)
      · exact Or.inr (Or.inl (isMisnerSpacetime_refl e hR hM))
      · exact absurd hC (not_cauchyCompact_of_refl_unipotent hGH e hR hU)
      · exact Or.inr (Or.inr (Or.inr (exists_torusProduct_cover_of_isCHCentralExtension hSel hGH
          hC ⟨_, isCHCentralExtensionOf_refl e hR hCH⟩)))

/-- **G9a + G9d** (l.3536–3548; DEC-44): a GH Cauchy-compact linear twisted product `B` over a
model `M₁` of Theorem A is itself a translation, Misner or unipotent spacetime, or is finitely
covered by a torus product (a). The LTP is trivial by `perp_eq_zero_of_cauchyCompact`; the rest is
`exists_family_of_isLTPData_of_perp` (whose family-(b) branch is G9d's `sorry`). -/
theorem exists_family_of_isLTPOver_cauchyCompact (hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} (hGH : GH B) (hC : CauchyCompact B) {d₁ : ℕ}
    {M₁ : FlatSpacetime.{0} d₁}
    (hfam : IsTranslationSpacetime M₁ ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsMisnerSpacetime M) ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsUnipotentSpacetime M) ∨
      IsCHCentralExtension M₁)
    (hltp : IsLTPOver B M₁) :
    IsTranslationSpacetime B ∨
      (match d, B with
        | 0, _ => False
        | _ + 1, M => IsMisnerSpacetime M) ∨
      (match d, B with
        | 0, _ => False
        | _ + 1, M => IsUnipotentSpacetime M) ∨
      ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → B), IsFiniteCover d q ∧ IsCHTorusProduct M₁' := by
  obtain ⟨Γ, Ω, ι, hd⟩ := hltp
  have h := exists_family_of_isLTPData_of_perp hSel hGH hC hd
    (perp_eq_zero_of_cauchyCompact hGH hC hd) (by cases d₁ <;> exact hfam)
  cases d <;> exact h

/-- **G9** (l.3536–3548, steps (3)–(4) of `Classification`'s `cauclo_from_embedding`): if `B` is
GH and Cauchy-compact, `f : M' → B` a surjective isometric embedding, and `B` a linear twisted
product over a model `M₁` of Theorem A, then some finite cover `M₁'` of `M'` is a translation
spacetime, a Misner spacetime, or a torus product (a). Proof: the base-level core
(`exists_family_of_isLTPOver_cauchyCompact`: G9a proved, G9d's one `sorry`), G9b
(`not_cauchyCompact_of_isUnipotentSpacetime`) to exclude the unipotent output, and G9c: `f` is an
isometric homeomorphism, along whose inverse the families, `IsQuotientOf` and finite covers
transport (`M₁' = M'`, `q = id` for the translation and Misner outputs). -/
theorem exists_modelB_cover_of_isLTPOver_cauchyCompact (hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} (hGH : GH B) (hC : CauchyCompact B) {M' : FlatSpacetime.{0} d}
    {f : M' → B} (hf : IsIsometricEmbedding d f) (hfs : Surjective f) {d₁ : ℕ}
    {M₁ : FlatSpacetime.{0} d₁}
    (hfam : IsTranslationSpacetime M₁ ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsMisnerSpacetime M) ∨
      (match d₁, M₁ with
        | 0, _ => False
        | _ + 1, M => IsUnipotentSpacetime M) ∨
      IsCHCentralExtension M₁)
    (hltp : IsLTPOver B M₁) :
    ∃ (M₁' : FlatSpacetime.{0} d) (q : M₁' → M'), IsFiniteCover d q ∧
      (IsTranslationSpacetime M₁' ∨
        (match d, M₁' with
          | 0, _ => False
          | _ + 1, M => IsMisnerSpacetime M) ∨
        IsCHTorusProduct M₁') := by
  have hb : Bijective f := ⟨hf.2, hfs⟩
  have he : IsLocalIsometry d (homeomorphOfBijective hf.1 hb).symm :=
    isLocalIsometry_homeomorphOfBijective_symm hf.1 hb
  rcases exists_family_of_isLTPOver_cauchyCompact hSel hGH hC
      (by cases d₁ <;> exact hfam) hltp with hT | hM | hU | ⟨M₁', q, hq, hCH⟩
  · exact ⟨M', id, isFiniteCover_id,
      Or.inl (isTranslationSpacetime_homeomorph (homeomorphOfBijective hf.1 hb).symm he hT)⟩
  · refine ⟨M', id, isFiniteCover_id, Or.inr (Or.inl ?_)⟩
    have h2 := misnerFamily_homeomorph (homeomorphOfBijective hf.1 hb).symm he
      (by cases d <;> exact hM)
    cases d <;> exact h2
  · exact (not_cauchyCompact_of_unipotentFamily hGH (by cases d <;> exact hU) hC).elim
  · exact ⟨M₁', (homeomorphOfBijective hf.1 hb).symm ∘ q,
      isFiniteCover_homeomorph_comp hq _ he, Or.inr (Or.inr hCH)⟩

end G9

end Causal.Flat.Cla
