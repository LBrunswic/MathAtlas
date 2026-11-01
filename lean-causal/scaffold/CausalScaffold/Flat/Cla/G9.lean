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
  Misner spacetime, or a torus product (a). It rests on **one** tagged `sorry`, in
  `exists_family_of_isLTPData_of_perp` (G9a's frame transport + G9d, below); everything else is
  proved.
* `isCompact_image_of_isQuotientOf` — **the obstruction to Cauchy-compactness**, sorry-free: if
  `M = Γ\Ω` is causal with a compact Cauchy surface `K`, and `F` is a continuous `Γ`-invariant
  function on `𝐌ⁿ` constant along a causal direction `v`, then `F(Ω)` is compact. (Every
  `v`-line through `z ∈ Ω` meets the lifted Cauchy surface, `F(z)` is a value of the descended
  function on `K`.) This is the common core of Barbot's two sentences l.3542 and l.744.
* `not_cauchyCompact_of_isUnipotentSpacetime` — **G9b, "unipotent spacetimes cannot be
  Cauchy-compact"** (l.744–746, l.3546–3547), sorry-free, for a GH unipotent spacetime: the
  `A`-invariant coordinate `y` is constant along the null direction `∂ₓ`, so by the obstruction
  `y(Ω) = ]α, β[` would be compact. Barbot's "submersion" is not needed.
* `perp_eq_zero_of_cauchyCompact` — **G9a, first half, "nontrivial linear twisted products
  destroy Cauchy-compactness"** (l.3542–3543), sorry-free: for LTP data `(Γ, Ω, ι)` of a GH
  Cauchy-compact `B`, `U^⊥ = 0`. The obstruction with `F = minkQ ∘ P_{U^⊥}` (Γ-invariant by
  `Restricts.split_smul`, constant along `ι_*(1,0)`, unbounded by `Ω + U^⊥ = Ω`).
* G9c, the transport along `f` (sorry-free): a bijective local isometry is a homeomorphism whose
  inverse is a local isometry (`homeomorphOfBijective`, `isLocalIsometry_homeomorphOfBijective_symm`);
  `IsQuotientOf`, the translation and Misner families transport along it; a finite cover composed
  with an isometric homeomorphism is a finite cover; a homeomorphism is a covering map.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` maximal (Theorem B) | ⚠ weakened: not assumed for `B` — not needed: G9a, G9b and G9d hold for any Cauchy-compact GH LTP over a model |
| `M` Cauchy-compact GH | ✓ carried, on `B` (`hGH`, `hC`) |
| `M` finitely covered by a space embedded in an LTP (Theorem A) | ✓ carried as `f` surjective (after [11.ii]) and `hltp` |
| "π₁ finitely generated" (DEC-44, for family (b) → (a)) | not assumed: it is to be derived from Cauchy-compactness (G9d, in the `sorry`) |
| Selberg's lemma (DEC-36, DEC-44) | ✓ carried as the named external `hSel` |

## SCOPE (disclosed)

`exists_family_of_isLTPData_of_perp` carries the one `sorry`. Its two missing pieces:

* **G9a, second half** (l.3542–3543): with `U^⊥ = 0` (proved, `perp_eq_zero_of_cauchyCompact`),
  `d₁ = d`, `ι` is an affine isomorphism, and `B = Γ\Ω` should be put in the family of
  `M₁ = Γ_U\ι⁻¹Ω`: missing the frame transport along `ι` (with a spatial reflection when `ι`
  reverses spatial orientation; `horizGroup`/`misnerGroup`/`unipAction` conjugation-stable,
  `limitOpensPlus`, `limitSetJ`, `kerTranslations` equivariant under conjugation) — not in the
  library.
* **G9d** (family (b) → (a), DEC-44): `Γ` finitely generated from Cauchy-compactness (an
  elementary Švarc–Milnor on the lifted Cauchy surface), Selberg on `L(Γ)`, the finite-index
  `Γ' = Γ ∩ L⁻¹(H)`, the transfer of `IsCHCentralExtensionOf` to `Γ'` (in particular
  `limitSetJ Γ' = limitSetJ Γ`), and the quotient `Γ'\Ω` as a finite cover of `B` — none in the
  library.

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

/-! ## G9 -/

section G9

variable {d : ℕ}

/-- **The base-level core, G9a's frame transport + G9d** (l.3536–3548; DEC-44): a GH
Cauchy-compact linear twisted product `B`, with data `(Γ, Ω, ι)` and **trivial** `U^⊥`, over a
model `M₁` of Theorem A, is itself a translation, Misner or unipotent spacetime, or is finitely
covered by a torus product (a). -/
theorem exists_family_of_isLTPData_of_perp (_hSel : SelbergLemma (Minkowski d))
    {B : FlatSpacetime.{0} d} (_hGH : GH B) (_hC : CauchyCompact B) {d₁ : ℕ}
    {M₁ : FlatSpacetime.{0} d₁} {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    {ι : AffineMinkEmbedding d₁ d} (_hd : IsLTPData B M₁ Γ Ω ι) (_hperp : ∀ w ∈ ι.perp, w = 0)
    (_hfam : IsTranslationSpacetime M₁ ∨
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
  sorry -- SORRY(bthm:cauclo, G9a+G9d): two pieces, neither in the library; the nontrivial-LTP half of G9a is proved here (`perp_eq_zero_of_cauchyCompact`). (G9a, frame transport, l.3542–3543) with `U^⊥ = 0` (`_hperp`; so `d₁ = d` and `ι` an affine isomorphism) `B = Γ\Ω` and `M₁ = Γ_U\ι⁻¹Ω`: missing the transport of each family of `M₁` to `B` along `ι` — compose the frame `φ` with `ι` (as an element of `isom d`; when `ι` reverses spatial orientation, a spatial reflection `r` is needed, with `horizGroup`, `misnerGroup`, `unipAction`'s group and the wedges/slabs `r`-conjugation stable), `restrictGroup` read back as `Γ` through `ι`, and for family (b) the equivariance of `kerTranslations`, `limitSetJ`, `limitOpensPlus/Minus`, `linearImage` and `HasGlobalFixedPoint` under conjugation by an affine isomorphism. (G9d, DEC-44) for `B = Γ\Ω^±(Λ(Γ))` of family (b): `Γ` finitely generated because it acts properly discontinuously and cocompactly on the connected locally compact lift of the compact Cauchy surface (elementary Švarc–Milnor; or `π₁` of a compact manifold) — missing; then `fg_map_of_fg` and `_hSel` give `H ≤ L(Γ)` torsion-free of finite index, `Γ' = Γ ∩ L⁻¹H`; missing: `IsCHCentralExtensionOf` for `Γ'` (`kerTranslations Γ'` a finite-index sublattice of `kerTranslations Γ`, still spanning `E` and ball-finite; `limitSetJ Γ' = limitSetJ Γ`, the loxodromic fixed points being those of `γᵏ ∈ Γ'`; discreteness and absence of a global fixed point of `L(Γ')` by finite index), and `Γ'\Ω` (`FlatQuotient.toFlatSpacetime`) as a finite cover of `B` with fibres `Γ/Γ'` (the covering map `Γ'\Ω → Γ\Ω` is not in the library)

/-- **G9a + G9d** (l.3536–3548; DEC-44): a GH Cauchy-compact linear twisted product `B` over a
model `M₁` of Theorem A is itself a translation, Misner or unipotent spacetime, or is finitely
covered by a torus product (a). The LTP is trivial by `perp_eq_zero_of_cauchyCompact`; the rest is
`exists_family_of_isLTPData_of_perp`. -/
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
(`exists_family_of_isLTPOver_cauchyCompact`, one `sorry`, G9a + G9d), G9b
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
