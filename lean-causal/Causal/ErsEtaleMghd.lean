import Causal.ErsEtaleGluing
import Causal.TwoPiece
import Causal.PushoutCausal
import Causal.GluingGeneric.Generated
import Causal.GXStructure
import Causal.CExtConnexeSecondCountable
import Causal.ErsSecondCountable
import Causal.Ers464SecondCountable
import Causal.Ers482Solution

/-!
# Two developments glued along a common development: a development over the background, étale

Programme target `T-abs-ers-etale-mghd` (`programme/roadmap.toml`; layer 1: ETT-layer imports only,
no model, no metric, `uses = [is_causal, causally_arc_connected, absolutely_minimal, curve_nested]`). The causal
half of Eperon–Reall–Sbierski, arXiv 1802.03020, §4.2 (`papers/ers-predictability`,
`legacy/labeled/ghd_02_19.tex`); its topological half is `Causal.ErsEtaleGluing`. **No label is
marked.** Read for information (unmarked, SCOPE): `ersthm:ThmNonUniqueness` — `ghd_02_19.tex:560`
(`ers_theorem_3_45_etale`), `erscor:CorDisCon` — `ghd_02_19.tex:921`
(`ers_corollary_4_68_etale`); the Born–Infeld rows `ersthm:diffeo_theorem` (`:298`),
`erslem:nec_cond` (`:304`), `erslem:lemma_sing` (`:319`), `erslem:sep_lemma` (`:380`),
`ersthm:global_theorem` (`:401`) are layer 3 and are not closed here.

On `E = U₁ ⊔_A U₂` (`Causal.EtaleGluing`, the gluing of the subtypes along `A`) the **glued
causality** `EtaleGluing.gluedCausality` is `Causal.Gluing.causality` of `C₁` on `U₁` and `C₂` on
`U₂`, read as spacetimes of their own (`(Cᵢ.restrict Uᵢ).toSubtype`). The assertions:

* `0-subtype` — `Causality.isEMorphism_restrict_toSubtype_val`,
  `Causality.isCauchySurfaceOn_iff_restrict_toSubtype` (an open set and its Cauchy surfaces, as a
  spacetime of its own), `Causality.causallyConvexIn_and_le_iff_of_agreeOn` (a common development
  is causally convex in both and the two relations agree between its points).
* `1-compatible` — `EtaleGluing.compatibleAlong_iff_agreeOn`: `Gluing.CompatibleAlong` of the two
  pieces **is** `AgreeOn C₁ C₂ A` (`≤` and `≪` agree on the open subsets of `A`);
  `CausalityFollowsLt`, the `≪` twin of `CausalityFollows`, and `CausalityFollows.agreeOn`.
* `2-two-piece` — `EtaleGluing.twoPiece` (`Causal.Causality.TwoPiece` over the sheets
  `sheet₁ = ι₁(U₁)`, `sheet₂ = ι₂(U₂)`), `isCausal_gluedCausality`.
* `3-cauchy` — `EtaleGluing.isEtaleDevelopment`: `E` Hausdorff, `π` étale, the glued causality
  two-piece and causal, the lifted `S` (`EtaleGluing.lift`) a Cauchy surface of `E` over `S`.
* `4-developments` — `ers_etale_development` (two developments `Causal.IsDevelopment`, a common
  development `IsCommonDevelopment`, closed in `U₁ ∩ U₂`; the glued causality restricts to
  `cau uᵢ`, the glued solution is `uᵢ` on each sheet), `ers_etale_development_component` (`A` the
  component through `S`), `ers_theorem_3_45_etale`, `ers_corollary_4_68_etale`.
* `5-injectivity` — `EtaleGluing.eqOn_inter_of_injective_proj` (injectivity gives agreement),
  `EtaleGluing.isOpenEmbedding_proj_of_isCauchySurfaceOn_inf`,
  `Causality.isPreconnected_inter_of_isCauchySurfaceOn_sup`, `ers_isPreconnected_inter_of_eqOn`
  and `ers_isOpenEmbedding_proj_of_eqOn` (agreement gives a connected overlap, hence injectivity,
  in ERS's subluminal setting, `S` connected and `m`-acausal); `ers_coe_eq_inter_of_eqOn`
  (moved here from `Causal.ErsEtaleMghdWitnesses` by T-abs-ers-overlap-sharp), the sharp form of
  `ers_isOpenEmbedding_proj_of_eqOn`, which is its corollary: there the common development is the
  whole overlap, `A = U₁ ∩ U₂`.
* `6-witness` — `EtaleGluing.timelikeLine_etale_witness`, `timelikeLine_isEtaleDevelopment`,
  `timelikeLine_ers_etale_witness`: the timelike line, `]-2, 1[ ⊔_{]-1, 1[} ]-1, 2[`, `S = {0}`;
  and `Causal.ErsEtaleMghdWitnesses` (T-abs-ers-etale-mghd-witnesses):
  `ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale` (4.68 étale asks only `(U₁, u₁)` a
  development, and no connected `S`), `…_twoPoint`, `timelikeLine_ers_theorem_3_45_etale_twoPoint`,
  `timelikeLine_ers_isPreconnected_inter_of_eqOn`, `timelikeLine_ers_isOpenEmbedding_proj_of_eqOn`.

> However, in the case that $u_1$ and $u_2$ are two globally hyperbolic developments of a
> quasilinear wave equation on a fixed background such that $U_1 \cap U_2$ is disconnected,
> glueing them together along the MCGHD (which equals the connected component of $U_1 \cap U_2$
> which contains the initial data hypersurface), would yield a solution which is no longer defined
> on a subset of $\R^{d+1}$, but instead on a manifold which projects down on
> $U_1 \cup U_2 \subseteq \R^{d+1}$ and contains the other connected components of
> $U_1 \cap U_2$ twice. (`:852`)

> Note that if $U_1 \cap U_2$ is disconnected, the same argument shows that the domain $W$ of the
> MCGHD equals the connected component of $U_1 \cap U_2$ that contains $S$. (`:850`)

> Given two globally hyperbolic developments $u_1$ and $u_2$ for the Einstein equations one
> constructs a bigger one in which both are contained (and thus proves global uniqueness) by
> glueing $u_1$ and $u_2$ together along the MCGHD of $u_1$ and $u_2$. (`:852`)

## Hypothesis checklist

| source (ERS `:852`, the target's statement) | here |
|---|---|
| background `ℝ^{d+1}` | ⚠ weakened: `M` Hausdorff and second countable; locally connected only for the component form |
| `(U₁, u₁)`, `(U₂, u₂)` GHDs of `S` | ⚠ read: `IsDevelopment` (`S` Cauchy in `Uᵢ` for `cau uᵢ`; GH not asked, as `Causal.ErsMughd`); `sol` is not used |
| the MCGHD `A`: open, `A ⊆ U₁ ∩ U₂`, `S ⊆ A`, `u₁ = u₂` on `A`, `S` Cauchy in `A` | ✓ carried: `IsCommonDevelopment` (for `cau u₁`; for `cau u₂` by agreement); any such `A`, not the maximal one |
| `A` the component of `U₁ ∩ U₂` through `S` (`:850`) | ⚠ read: `A` closed in `U₁ ∩ U₂` (`hclosed`, the half of `:850` that makes `E` Hausdorff); the component itself in `ers_etale_development_component`; that the MCGHD is it is Thm 4.64's |
| the metrics of `u₁`, `u₂` coincide on `A` | ⚠ abstract: `AgreeOn` (`≤`, `≪` on the open subsets of `A`), equivalent to `Gluing.CompatibleAlong` of the pieces; in the development forms from `CausalityFollows` and the new declared hypothesis `CausalityFollowsLt` (its `≪` twin, defined here) |
| `g(uᵢ)` time-oriented Lorentzian, GH | ⚠ named: `≤_{Uᵢ}` antisymmetric (`is_causal` on `Uᵢ`), `cau uᵢ` causally arc-connected on `Uᵢ` |
| absolute minimality of the pieces (target) | ⚠ weakened: derived from causal arc-connectedness (`CausallyArcConnectedOn.absolutelyMinimalOn`) |
| "a manifold": `E` smooth, the solution on `E` | its causal topology: Hausdorff, étale, two-piece, causal, `S` lifted Cauchy; no smooth structure, no PDE (layer 3) |

## SCOPE (disclosed)

* **A new declared hypothesis**, `CausalityFollowsLt` (defined in this module; `CausalityFollows` is `Causal.ErsMughd`'s): if `u = v` on `W`, the causalities of `u` and `v` have the same `≪_V` on every open `V ≤ W`. `CausalityFollows` covers `≤` only, and `≪`-agreement is needed for `Gluing.CompatibleAlong`; ERS's (4.61) supplies both. OQ-157 is related and stays open.
* **No label is marked.** The target states the programme's form, not a paper statement. Thm
  3.45's statement (two Born–Infeld GHDs exist) and Lemmas 3.22–3.35 are layer 3
  (`T-loc-born-infeld-causal`); `ers_theorem_3_45_etale` reads its conclusion on the gluing.
  `ers_corollary_4_68_etale` takes `A` closed in `U₁ ∩ U₂` as a hypothesis, ERS's Thm 4.64 content.
* **Global hyperbolicity of `E` is not concluded** (`TwoPiece.globallyHyperbolic` stays in
  `Causal.CBG.Ppcm` with the piece charts); "development" is read with `S` Cauchy, as
  `IsDevelopment` reads it.
* **Agreement and injectivity are kept apart.** Injectivity of `π` gives agreement on all of
  `U₁ ∩ U₂` (`eqOn_inter_of_injective_proj`). The converse is proved only under hypotheses: `S`
  connected and Cauchy in `U₁ ∩ U₂`, or ERS's subluminal setting with `S` connected and
  `m`-acausal (`ers_isPreconnected_inter_of_eqOn`, the claim `Causal.ErsMughd`'s SCOPE argues,
  and `ers_isOpenEmbedding_proj_of_eqOn`, through Rem 4.78). Without them it is not decided here;
  ERS's non-achronal `S` (`:930`) suggests it fails (not formalized: a model). Under the open
  embedding's hypotheses the common development is the whole overlap, `A = U₁ ∩ U₂`
  (`ers_coe_eq_inter_of_eqOn`, the sharp form, of which `ers_isOpenEmbedding_proj_of_eqOn` is the
  corollary): the gluing there is the trivial one, and neither theorem says anything of gluing
  along a proper common development.
* **Witness.** On the timelike line every development of `{0}` is an interval (it is connected,
  `isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`), so `U₁ ∩ U₂` is connected and `π`
  is injective (argued, not stated): the witness has a proper two-piece overlap but no doubled
  point. A doubled point needs a disconnected overlap, which no two developments of `{0}` on the
  line have; ERS's are two Born–Infeld developments in `1 + 1` dimensions (Thm 3.45, layer 3).
  What blocks a doubled point is the connectedness of `S`, not the line: with `S = {0, 3}` the
  étale development has one (`ErsEtaleWitness.timelikeLine_ers_theorem_3_45_etale_twoPoint`,
  `Causal.ErsEtaleMghdWitnesses`); with `S` preconnected, `real_eqOn_inter_of_isDevelopment`
  excludes it on `ℝ`.
* **Imports.** ETT layer only (`tools/ladder.py` `model_path` `None`); the closure contains
  `Causal.CBG.CausalConvex`, `.Injective`, `.FamilyGluing`, `.SubExtensionAbstract` (ETT-layer,
  through `Causal.CExtConnexeSecondCountable` and `Causal.GluingGeneric.Generated`), whose
  `Causality.le_of_causallyConvexIn_of_le` is used; no `Causal.CBG.*` is imported directly.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace
open scoped Interval

universe u v

variable {M : Type u} [TopologicalSpace M]

/-! ## 0. An open subset as a spacetime of its own: the inclusion and its Cauchy surfaces -/

namespace Causality

/-- **The inclusion of an open set, with the restricted causality, is an injective abstract
`𝕄≥0`-morphism**: a strong morphism (`restrict_inclusionStrong`) and a local isomorphism (on
`⊤`, the image of an open `V'` is `imageOpens V'`). -/
theorem isEMorphism_restrict_toSubtype_val (C : Causality M) (U : Opens M) :
    IsEMorphism ((C.restrict U).toSubtype) C Subtype.val := by
  refine isEMorphism_iff.2 ⟨(LocalCausality.inclusionStrong_iff _ C).1
    (C.restrict_inclusionStrong U), U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph,
    fun _ => ⟨⊤, trivial, Subtype.val_injective.injOn, fun V' _ W hW y _ z _ => ?_⟩⟩
  obtain rfl : imageOpens V' = W := SetLike.coe_injective hW.symm
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **Cauchy surfaces of an open set are those of the open set as a spacetime of its own.** -/
theorem isCauchySurfaceOn_iff_restrict_toSubtype (C : Causality M) {U : Opens M} {S : Set M}
    (hS : S ⊆ U) :
    C.IsCauchySurfaceOn U S ↔ ((C.restrict U).toSubtype).IsCauchySurface (Subtype.val ⁻¹' S) := by
  have h := IsEMorphismOn.isCauchySurfaceOn_image_iff (isEMorphism_restrict_toSubtype_val C U)
    Subtype.val_injective.injOn (V := ⊤) le_rfl (U := U)
    (by rw [Opens.coe_top, image_univ, Subtype.range_coe]) (subset_univ (Subtype.val ⁻¹' S))
  rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.2 hS] at h
  exact h.symm

/-- **A common development is causally convex in both developments, and their relations agree
between its points**: `A ≤ U₁ ⊓ U₂` open, `C₁`, `C₂` agreeing on the open subsets of `A`, `S ⊆ A`
a Cauchy surface of `A`, `U₁`, `U₂` (for `C₁`, `C₁`, `C₂`), `≤` antisymmetric and causally
arc-connected on `U₁`, `U₂`. Convexity is
`Causality.causallyConvexIn_of_isCauchySurfaceOn_of_secondCountable`; then a `≤_{U₁}`-relation
between points of `A` is one of `A` (`le_of_causallyConvexIn_of_le`), hence of `C₂`. -/
theorem causallyConvexIn_and_le_iff_of_agreeOn [T2Space M] [SecondCountableTopology M]
    {C₁ C₂ : Causality M} {U₁ U₂ A : Opens M} (hC : AgreeOn C₁ C₂ A) (hAU₁ : A ≤ U₁)
    (hAU₂ : A ≤ U₂) (hanti₁ : ∀ ⦃x y : M⦄, C₁.le U₁ x y → C₁.le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, C₂.le U₂ x y → C₂.le U₂ y x → x = y)
    (harc₁ : C₁.CausallyArcConnectedOn U₁) (harc₂ : C₂.CausallyArcConnectedOn U₂) {S : Set M}
    (hSA : S ⊆ A) (hS : C₁.IsCauchySurfaceOn A S) (hS₁ : C₁.IsCauchySurfaceOn U₁ S)
    (hS₂ : C₂.IsCauchySurfaceOn U₂ S) :
    C₁.CausallyConvexIn (A : Set M) U₁ ∧ C₂.CausallyConvexIn (A : Set M) U₂ ∧
      ∀ a ∈ A, ∀ b ∈ A, (C₁.le U₁ a b ↔ C₂.le U₂ a b) := by
  have hS' : C₂.IsCauchySurfaceOn A S :=
    isCauchySurfaceOn_of_agree (fun V hV x y => (hC V hV x y).1) hS
  have hc₁ := causallyConvexIn_of_isCauchySurfaceOn_of_secondCountable hanti₁ harc₁ hAU₁ hSA hS hS₁
  have hc₂ := causallyConvexIn_of_isCauchySurfaceOn_of_secondCountable hanti₂ harc₂ hAU₂ hSA hS' hS₂
  refine ⟨hc₁, hc₂, fun a ha b hb => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact C₂.le_mono hAU₂
      ((hC A le_rfl a b).1.1 (le_of_causallyConvexIn_of_le harc₁ hc₁ subset_rfl hAU₁ ha hb h))
  · exact C₁.le_mono hAU₁
      ((hC A le_rfl a b).1.2 (le_of_causallyConvexIn_of_le harc₂ hc₂ subset_rfl hAU₂ ha hb h))

/-- **One causality with `S` Cauchy in `U₁`, in `U₂` and in `U₁ ⊔ U₂`: the overlap is connected**
when `S` is and `≤` is antisymmetric on the union. Through `x ∈ U₁ ∩ U₂` runs an inextensible
causal curve `γ` of the union; its components through `x` in `U₁` and in `U₂` are inextensible
there, so meet `S`, at the one point where `γ` meets `S`; one of the two arcs from `x` lies in the
other, or `x` lies between two parameters over that point and is it (antisymmetry). Either way
an arc from `x` to `S` lies in `U₁ ∩ U₂` (`isPreconnected_of_segments`). -/
theorem isPreconnected_inter_of_isCauchySurfaceOn_sup [T2Space M] [SecondCountableTopology M]
    {C : Causality M} {U₁ U₂ : Opens M} {S : Set M}
    (hanti : ∀ ⦃x y : M⦄, C.le (U₁ ⊔ U₂) x y → C.le (U₁ ⊔ U₂) y x → x = y)
    (hSc : IsPreconnected S) (hSU : S ⊆ (U₁ : Set M) ∩ U₂) (h₁ : C.IsCauchySurfaceOn U₁ S)
    (h₂ : C.IsCauchySurfaceOn U₂ S) (hsup : C.IsCauchySurfaceOn (U₁ ⊔ U₂) S) :
    IsPreconnected ((U₁ : Set M) ∩ U₂) := by
  refine isPreconnected_of_segments hSc hSU fun x hx => ?_
  obtain ⟨I, γ, hγ, t₀, ht₀, rfl⟩ := inextensibleThrough_of_t1_secondCountable C (U₁ ⊔ U₂) x
    ((le_sup_left : U₁ ≤ U₁ ⊔ U₂) hx.1)
  have key : ∀ σ ∈ I, γ σ ∈ S → [[t₀, σ]] ⊆ γ ⁻¹' ((U₁ : Set M) ∩ U₂) →
      ∃ (c : ℝ → M) (a b : ℝ), ContinuousOn c [[a, b]] ∧ c a = γ t₀ ∧ c b ∈ S ∧
        c '' [[a, b]] ⊆ (U₁ : Set M) ∩ U₂ := fun σ hσ hσS hseg =>
    ⟨γ, t₀, σ, hγ.1.continuousOn_uIcc ht₀ hσ, rfl, hσS, fun _ ⟨u, hu, e⟩ => e ▸ hseg hu⟩
  have hJ₁ := inextensible_ordConnectedComponent_of_le hanti le_sup_left hγ ht₀ hx.1
  have hJ₂ := inextensible_ordConnectedComponent_of_le hanti le_sup_right hγ ht₀ hx.2
  obtain ⟨_, ⟨⟨σ₁, hσ₁J, rfl⟩, hσ₁S⟩, -⟩ := h₁ _ γ hJ₁
  obtain ⟨_, ⟨⟨σ₂, hσ₂J, rfl⟩, hσ₂S⟩, -⟩ := h₂ _ γ hJ₂
  have hσ₁ : σ₁ ∈ I := (ordConnectedComponent_subset hσ₁J).1
  have hσ₂ : σ₂ ∈ I := (ordConnectedComponent_subset hσ₂J).1
  have seg₁ : [[t₀, σ₁]] ⊆ γ ⁻¹' U₁ := fun u hu =>
    (ordConnectedComponent_subset ((inferInstance : OrdConnected
      (ordConnectedComponent (I ∩ γ ⁻¹' U₁) t₀)).uIcc_subset
        (self_mem_ordConnectedComponent.2 ⟨ht₀, hx.1⟩) hσ₁J hu)).2
  have seg₂ : [[t₀, σ₂]] ⊆ γ ⁻¹' U₂ := fun u hu =>
    (ordConnectedComponent_subset ((inferInstance : OrdConnected
      (ordConnectedComponent (I ∩ γ ⁻¹' U₂) t₀)).uIcc_subset
        (self_mem_ordConnectedComponent.2 ⟨ht₀, hx.2⟩) hσ₂J hu)).2
  have heq : γ σ₁ = γ σ₂ :=
    (hsup I γ hγ).unique ⟨⟨σ₁, hσ₁, rfl⟩, hσ₁S⟩ ⟨⟨σ₂, hσ₂, rfl⟩, hσ₂S⟩
  by_cases hA : σ₁ ∈ [[t₀, σ₂]]
  · exact key σ₁ hσ₁ hσ₁S fun u hu => ⟨seg₁ hu, seg₂ (uIcc_subset_uIcc left_mem_uIcc hA hu)⟩
  by_cases hB : σ₂ ∈ [[t₀, σ₁]]
  · exact key σ₂ hσ₂ hσ₂S fun u hu => ⟨seg₁ (uIcc_subset_uIcc left_mem_uIcc hB hu), seg₂ hu⟩
  have hS₀ : γ t₀ ∈ S := by
    rcases le_total σ₁ σ₂ with h | h
    · have h1 : σ₁ < t₀ := lt_of_not_ge fun h' => hA (mem_uIcc.2 (Or.inl ⟨h', h⟩))
      have h2 : t₀ < σ₂ := lt_of_not_ge fun h' => hB (mem_uIcc.2 (Or.inr ⟨h, h'⟩))
      have l₁ := hγ.1.le_of_le hσ₁ ht₀ h1.le
      have l₂ := hγ.1.le_of_le ht₀ hσ₂ h2.le
      rw [← heq] at l₂
      rw [← hanti l₁ l₂]
      exact hσ₁S
    · have h1 : σ₂ < t₀ := lt_of_not_ge fun h' => hB (mem_uIcc.2 (Or.inl ⟨h', h⟩))
      have h2 : t₀ < σ₁ := lt_of_not_ge fun h' => hA (mem_uIcc.2 (Or.inr ⟨h, h'⟩))
      have l₁ := hγ.1.le_of_le hσ₂ ht₀ h1.le
      have l₂ := hγ.1.le_of_le ht₀ hσ₁ h2.le
      rw [heq] at l₂
      rw [← hanti l₁ l₂]
      exact hσ₂S
  refine key t₀ ht₀ hS₀ fun u hu => ?_
  rw [uIcc_self, mem_singleton_iff] at hu
  rw [mem_preimage, hu]
  exact hx

end Causality

/-! ## 1. The glued causality on `U₁ ⊔_A U₂` -/

namespace EtaleGluing

variable {U₁ U₂ A : Opens M} (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂)

/-- The sheet `ι₁(U₁)` of `E = U₁ ⊔_A U₂`, an open set. -/
abbrev sheet₁ : Opens (EtaleGluing h₁ h₂) :=
  Gluing.O₁ (isOpenEmbedding_inclusion h₁ A.isOpen) (isOpenEmbedding_inclusion h₂ A.isOpen)

/-- The sheet `ι₂(U₂)` of `E = U₁ ⊔_A U₂`, an open set. -/
abbrev sheet₂ : Opens (EtaleGluing h₁ h₂) :=
  Gluing.O₂ (isOpenEmbedding_inclusion h₁ A.isOpen) (isOpenEmbedding_inclusion h₂ A.isOpen)

/-- **The glued causality** of `C₁` on `U₁` and `C₂` on `U₂`: `Causal.Gluing.causality` of the
two open subsets read as spacetimes of their own (`(Cᵢ.restrict Uᵢ).toSubtype`), the causality
generated by the two pieces (`theo:causalite_engendre`). -/
def gluedCausality (C₁ C₂ : Causality M) : Causality (EtaleGluing h₁ h₂) :=
  Gluing.causality (isOpenEmbedding_inclusion h₁ A.isOpen) (isOpenEmbedding_inclusion h₂ A.isOpen)
    ((C₁.restrict U₁).toSubtype) ((C₂.restrict U₂).toSubtype)

/-- **The lifted surface**: `S` read in the first sheet, `ι₁(S ∩ U₁)`. -/
def lift (S : Set M) : Set (EtaleGluing h₁ h₂) :=
  Gluing.ι₁ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' S)

variable {h₁ h₂}

/-- A point of the first sheet lies in the second iff it lies over `A`. -/
theorem ι₁_mem_sheet₂_iff {x : (U₁ : Set M)} :
    Gluing.ι₁ (inclusion h₁) (inclusion h₂) x ∈ sheet₂ h₁ h₂ ↔ (x : M) ∈ A := by
  constructor
  · rintro ⟨y, hy⟩
    exact (ι₁_eq_ι₂_iff.1 hy.symm).2
  · intro hx
    exact ⟨⟨x, h₂ hx⟩, ((ι₁_eq_ι₂_iff (h₁ := h₁) (h₂ := h₂) (x := x) (y := ⟨x, h₂ hx⟩)).2
      ⟨rfl, hx⟩).symm⟩

/-- A point of the second sheet lies in the first iff it lies over `A`. -/
theorem ι₂_mem_sheet₁_iff {y : (U₂ : Set M)} :
    Gluing.ι₂ (inclusion h₁) (inclusion h₂) y ∈ sheet₁ h₁ h₂ ↔ (y : M) ∈ A := by
  constructor
  · rintro ⟨x, hx⟩
    have h := ι₁_eq_ι₂_iff.1 hx
    rw [← h.1]
    exact h.2
  · intro hy
    exact ⟨⟨y, h₁ hy⟩, (ι₁_eq_ι₂_iff (h₁ := h₁) (h₂ := h₂) (x := ⟨y, h₁ hy⟩) (y := y)).2
      ⟨rfl, hy⟩⟩

/-- Over a surface inside `A` the two sheets give the same lift. -/
theorem lift_eq_image_ι₂ {S : Set M} (hS : S ⊆ A) :
    lift h₁ h₂ S = Gluing.ι₂ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxA : (x : M) ∈ A := hS hx
    exact ⟨⟨x, h₂ hxA⟩, hx, ((ι₁_eq_ι₂_iff (h₁ := h₁) (h₂ := h₂) (x := x)
      (y := ⟨x, h₂ hxA⟩)).2 ⟨rfl, hxA⟩).symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hyA : (y : M) ∈ A := hS hy
    exact ⟨⟨y, h₁ hyA⟩, hy, (ι₁_eq_ι₂_iff (h₁ := h₁) (h₂ := h₂) (x := ⟨y, h₁ hyA⟩)
      (y := y)).2 ⟨rfl, hyA⟩⟩

/-- The lift projects onto `S ∩ U₁`. -/
theorem proj_image_lift (S : Set M) : proj h₁ h₂ '' lift h₁ h₂ S = S ∩ U₁ := by
  rw [lift, ← image_comp, proj_comp_ι₁, image_preimage_eq_inter_range, Subtype.range_coe]

variable {C₁ C₂ : Causality M}

/-- **The compatibility of the two pieces along `A` is the agreement of `C₁` and `C₂` on the open
subsets of `A`** (`Causal.AgreeOn`). With `Gluing.exists_isGluingCausality_iff`, this is the
weakest hypothesis under which a causality of `E` restricts to `C₁` on `U₁` and `C₂` on `U₂`. -/
theorem compatibleAlong_iff_agreeOn :
    Gluing.CompatibleAlong (inclusion h₁) (inclusion h₂) ((C₁.restrict U₁).toSubtype)
      ((C₂.restrict U₂).toSubtype) ↔ AgreeOn C₁ C₂ A := by
  constructor
  · intro hc V hV x y
    by_cases hxy : x ∈ V ∧ y ∈ V
    · obtain ⟨hx, hy⟩ := hxy
      let V₁ : Opens (U₁ : Set M) :=
        ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩
      let V₂ : Opens (U₂ : Set M) :=
        ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩
      have hV₁ : (V₁ : Set (U₁ : Set M)) ⊆ range (inclusion h₁) := fun z hz => by
        rw [range_inclusion]; exact hV hz
      have hV₂ : (V₂ : Set (U₂ : Set M)) ⊆ range (inclusion h₂) := fun z hz => by
        rw [range_inclusion]; exact hV hz
      have e₁ : imageOpens V₁ = V := (imageOpens_eq_inf (U := V) rfl).trans
        (inf_eq_left.2 fun z hz => h₁ (hV hz))
      have e₂ : imageOpens V₂ = V := (imageOpens_eq_inf (U := V) rfl).trans
        (inf_eq_left.2 fun z hz => h₂ (hV hz))
      have key := hc V₁ V₂ hV₁ hV₂ rfl ⟨x, hV hx⟩ ⟨y, hV hy⟩
      change (C₁.le (imageOpens V₁) x y ↔ C₂.le (imageOpens V₂) x y) ∧
        (C₁.lt (imageOpens V₁) x y ↔ C₂.lt (imageOpens V₂) x y) at key
      rwa [e₁, e₂] at key
    · rw [not_and_or] at hxy
      rcases hxy with hx | hy
      · exact ⟨iff_of_false (fun h => hx (C₁.le_mem_left h)) (fun h => hx (C₂.le_mem_left h)),
          iff_of_false (fun h => hx (C₁.lt_mem_left h)) (fun h => hx (C₂.lt_mem_left h))⟩
      · exact ⟨iff_of_false (fun h => hy (C₁.le_mem_right h)) (fun h => hy (C₂.le_mem_right h)),
          iff_of_false (fun h => hy (C₁.lt_mem_right h)) (fun h => hy (C₂.lt_mem_right h))⟩
  · intro hC V₁ V₂ hV₁ hV₂ hpre u u'
    have hsub : ∀ {z : M}, z ∈ (imageOpens V₁ : Set M) → z ∈ (imageOpens V₂ : Set M) ∧ z ∈ A := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := hV₁ hx
      have hw : w ∈ inclusion h₂ ⁻¹' (V₂ : Set (U₂ : Set M)) := hpre ▸ hx
      exact ⟨⟨inclusion h₂ w, hw, rfl⟩, w.2⟩
    have hsub' : ∀ {z : M}, z ∈ (imageOpens V₂ : Set M) → z ∈ (imageOpens V₁ : Set M) := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, rfl⟩ := hV₂ hy
      have hw : w ∈ inclusion h₁ ⁻¹' (V₁ : Set (U₁ : Set M)) := hpre.symm ▸ hy
      exact ⟨inclusion h₁ w, hw, rfl⟩
    have e : imageOpens V₁ = imageOpens V₂ :=
      SetLike.coe_injective (Subset.antisymm (fun _ hz => (hsub hz).1) fun _ hz => hsub' hz)
    have hle : imageOpens V₁ ≤ A := fun _ hz => (hsub hz).2
    change (C₁.le (imageOpens V₁) u u' ↔ C₂.le (imageOpens V₂) u u') ∧
      (C₁.lt (imageOpens V₁) u u' ↔ C₂.lt (imageOpens V₂) u u')
    rw [← e]
    exact hC _ hle u u'


/-- On the first sheet the glued relation is `≤_{U₁}` of `C₁`. -/
theorem gluedCausality_le_sheet₁_iff (hC : AgreeOn C₁ C₂ A) {x y : (U₁ : Set M)} :
    (gluedCausality h₁ h₂ C₁ C₂).le (sheet₁ h₁ h₂) (Gluing.ι₁ (inclusion h₁) (inclusion h₂) x)
      (Gluing.ι₁ (inclusion h₁) (inclusion h₂) y) ↔ C₁.le U₁ x y := by
  have hpre : preimageOpens (Gluing.continuous_ι₁ (j₁ := inclusion h₁) (j₂ := inclusion h₂))
      (sheet₁ h₁ h₂) = ⊤ := top_unique fun z _ => ⟨z, rfl⟩
  refine (Gluing.causality_le_ι₁ (compatibleAlong_iff_agreeOn.2 hC) le_rfl).trans ?_
  rw [hpre]
  change C₁.le (imageOpens ⊤) x y ↔ _
  rw [GluingGeneric.imageOpens_top]

/-- On the second sheet the glued relation is `≤_{U₂}` of `C₂`. -/
theorem gluedCausality_le_sheet₂_iff (hC : AgreeOn C₁ C₂ A) {x y : (U₂ : Set M)} :
    (gluedCausality h₁ h₂ C₁ C₂).le (sheet₂ h₁ h₂) (Gluing.ι₂ (inclusion h₁) (inclusion h₂) x)
      (Gluing.ι₂ (inclusion h₁) (inclusion h₂) y) ↔ C₂.le U₂ x y := by
  have hpre : preimageOpens (Gluing.continuous_ι₂ (j₁ := inclusion h₁) (j₂ := inclusion h₂))
      (sheet₂ h₁ h₂) = ⊤ := top_unique fun z _ => ⟨z, rfl⟩
  refine (Gluing.causality_le_ι₂ (compatibleAlong_iff_agreeOn.2 hC) le_rfl).trans ?_
  rw [hpre]
  change C₂.le (imageOpens ⊤) x y ↔ _
  rw [GluingGeneric.imageOpens_top]

/-! ## 2. The gluing is a two-piece spacetime -/

/-- **The gluing of two open sets along a common development is a two-piece spacetime**
(`Causal.Causality.TwoPiece`) over the two sheets. -/
theorem twoPiece [T2Space M] [SecondCountableTopology M] (hC : AgreeOn C₁ C₂ A)
    (hanti₁ : ∀ ⦃x y : M⦄, C₁.le U₁ x y → C₁.le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, C₂.le U₂ x y → C₂.le U₂ y x → x = y)
    (harc₁ : C₁.CausallyArcConnectedOn U₁) (harc₂ : C₂.CausallyArcConnectedOn U₂) {S : Set M}
    (hSA : S ⊆ A) (hS : C₁.IsCauchySurfaceOn A S) (hS₁ : C₁.IsCauchySurfaceOn U₁ S)
    (hS₂ : C₂.IsCauchySurfaceOn U₂ S) :
    (gluedCausality h₁ h₂ C₁ C₂).TwoPiece (sheet₁ h₁ h₂) (sheet₂ h₁ h₂) := by
  obtain ⟨hc₁, hc₂, hagree⟩ := Causality.causallyConvexIn_and_le_iff_of_agreeOn hC
    (fun _ hz => h₁ hz) (fun _ hz => h₂ hz) hanti₁ hanti₂ harc₁ harc₂ hSA hS hS₁ hS₂
  refine ⟨fun z => ?_, ?_, ?_, ?_, ?_⟩
  · rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  · refine Gluing.causality_absolutelyMinimalOn_all _ _ (fun V => ?_) (fun V => ?_) ⊤
    · exact (Causality.restrict_toSubtype_absolutelyMinimalOn_iff C₁ U₁ V).2
        (harc₁.mono (imageOpens_le V)).absolutelyMinimalOn
    · exact (Causality.restrict_toSubtype_absolutelyMinimalOn_iff C₂ U₂ V).2
        (harc₂.mono (imageOpens_le V)).absolutelyMinimalOn
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ : x ∈ range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_left hxy
    obtain ⟨b, rfl⟩ : y ∈ range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hxy
    obtain ⟨c, rfl⟩ : z ∈ range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hyz
    rw [ι₁_mem_sheet₂_iff] at hx hz ⊢
    rw [gluedCausality_le_sheet₁_iff hC] at hxy hyz
    exact hc₁.2 a hx c hz (Causality.mem_diamond.2 ⟨hxy, hyz⟩)
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ : x ∈ range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_left hxy
    obtain ⟨b, rfl⟩ : y ∈ range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hxy
    obtain ⟨c, rfl⟩ : z ∈ range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hyz
    rw [ι₂_mem_sheet₁_iff] at hx hz ⊢
    rw [gluedCausality_le_sheet₂_iff hC] at hxy hyz
    exact hc₂.2 a hx c hz (Causality.mem_diamond.2 ⟨hxy, hyz⟩)
  · rintro _ _ ⟨a, rfl⟩ hx₂ ⟨b, rfl⟩ hy₂
    have ha := ι₁_mem_sheet₂_iff.1 hx₂
    have hb := ι₁_mem_sheet₂_iff.1 hy₂
    have ea : Gluing.ι₁ (inclusion h₁) (inclusion h₂) a =
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨a, h₂ ha⟩ := ι₁_eq_ι₂_iff.2 ⟨rfl, ha⟩
    have eb : Gluing.ι₁ (inclusion h₁) (inclusion h₂) b =
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨b, h₂ hb⟩ := ι₁_eq_ι₂_iff.2 ⟨rfl, hb⟩
    rw [gluedCausality_le_sheet₁_iff hC, ea, eb, gluedCausality_le_sheet₂_iff hC]
    exact hagree a ha b hb

/-- **The gluing is causal** when the two pieces are. -/
theorem isCausal_gluedCausality [T2Space M] [SecondCountableTopology M] (hC : AgreeOn C₁ C₂ A)
    (hanti₁ : ∀ ⦃x y : M⦄, C₁.le U₁ x y → C₁.le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, C₂.le U₂ x y → C₂.le U₂ y x → x = y)
    (harc₁ : C₁.CausallyArcConnectedOn U₁) (harc₂ : C₂.CausallyArcConnectedOn U₂) {S : Set M}
    (hSA : S ⊆ A) (hS : C₁.IsCauchySurfaceOn A S) (hS₁ : C₁.IsCauchySurfaceOn U₁ S)
    (hS₂ : C₂.IsCauchySurfaceOn U₂ S) : (gluedCausality h₁ h₂ C₁ C₂).IsCausal := by
  refine (twoPiece hC hanti₁ hanti₂ harc₁ harc₂ hSA hS hS₁ hS₂).isCausal (fun x y hxy hyx => ?_)
    (fun x y hxy hyx => ?_)
  · obtain ⟨a, rfl⟩ : x ∈ range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_left hxy
    obtain ⟨b, rfl⟩ : y ∈ range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hxy
    rw [gluedCausality_le_sheet₁_iff hC] at hxy hyx
    exact congrArg _ (Subtype.ext (hanti₁ hxy hyx))
  · obtain ⟨a, rfl⟩ : x ∈ range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_left hxy
    obtain ⟨b, rfl⟩ : y ∈ range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
      (gluedCausality h₁ h₂ C₁ C₂).le_mem_right hxy
    rw [gluedCausality_le_sheet₂_iff hC] at hxy hyx
    exact congrArg _ (Subtype.ext (hanti₂ hxy hyx))

/-! ## 3. The lifted surface is a Cauchy surface of the gluing -/

/-- **The étale gluing of two open sets along a common development** (ERS §4.2, `:852`, causal
half): on a Hausdorff, second countable `M`, with `A` closed in `U₁ ∩ U₂`, the gluing `E` is
Hausdorff, its glued causality is causal and two-piece, and the lifted `S` is a Cauchy surface of
`E`; `π` is a local homeomorphism carrying the lift onto `S`. -/
theorem isEtaleDevelopment [T2Space M] [SecondCountableTopology M] (hC : AgreeOn C₁ C₂ A)
    (hanti₁ : ∀ ⦃x y : M⦄, C₁.le U₁ x y → C₁.le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, C₂.le U₂ x y → C₂.le U₂ y x → x = y)
    (harc₁ : C₁.CausallyArcConnectedOn U₁) (harc₂ : C₂.CausallyArcConnectedOn U₂) {S : Set M}
    (hSA : S ⊆ A) (hS : C₁.IsCauchySurfaceOn A S) (hS₁ : C₁.IsCauchySurfaceOn U₁ S)
    (hS₂ : C₂.IsCauchySurfaceOn U₂ S) (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A) :
    T2Space (EtaleGluing h₁ h₂) ∧ IsLocalHomeomorph (proj h₁ h₂) ∧
      (gluedCausality h₁ h₂ C₁ C₂).TwoPiece (sheet₁ h₁ h₂) (sheet₂ h₁ h₂) ∧
      (gluedCausality h₁ h₂ C₁ C₂).IsCausal ∧
      (gluedCausality h₁ h₂ C₁ C₂).IsCauchySurface (lift h₁ h₂ S) ∧
      proj h₁ h₂ '' lift h₁ h₂ S = S := by
  haveI hT2 : T2Space (EtaleGluing h₁ h₂) := (t2Space_iff A.isOpen).2 hclosed
  have hTP := twoPiece (h₁ := h₁) (h₂ := h₂) hC hanti₁ hanti₂ harc₁ harc₂ hSA hS hS₁ hS₂
  have hcaus := isCausal_gluedCausality (h₁ := h₁) (h₂ := h₂) hC hanti₁ hanti₂ harc₁ harc₂ hSA hS
    hS₁ hS₂
  have hcompat := (compatibleAlong_iff_agreeOn (h₁ := h₁) (h₂ := h₂)).2 hC
  have hSU₁ : S ⊆ U₁ := hSA.trans h₁
  have hSU₂ : S ⊆ U₂ := hSA.trans h₂
  have hE₁ : IsEMorphism ((C₁.restrict U₁).toSubtype) (gluedCausality h₁ h₂ C₁ C₂)
      (Gluing.ι₁ (inclusion h₁) (inclusion h₂)) :=
    isEMorphism_iff.2 ⟨Gluing.strongMorphism_ι₁ hcompat, Gluing.localIsomorphism_ι₁ hcompat⟩
  have hE₂ : IsEMorphism ((C₂.restrict U₂).toSubtype) (gluedCausality h₁ h₂ C₁ C₂)
      (Gluing.ι₂ (inclusion h₁) (inclusion h₂)) :=
    isEMorphism_iff.2 ⟨Gluing.strongMorphism_ι₂ hcompat, Gluing.localIsomorphism_ι₂ hcompat⟩
  have hc₁ : (gluedCausality h₁ h₂ C₁ C₂).IsCauchySurfaceOn (sheet₁ h₁ h₂) (lift h₁ h₂ S) :=
    (IsEMorphismOn.isCauchySurfaceOn_image_iff hE₁
      (Gluing.injective_ι₁ (inclusion_injective h₁) (inclusion_injective h₂)).injOn le_rfl
      (U := sheet₁ h₁ h₂) (by rw [Opens.coe_top, image_univ]; rfl) (subset_univ _)).1
      ((C₁.isCauchySurfaceOn_iff_restrict_toSubtype hSU₁).1 hS₁)
  have hc₂ : (gluedCausality h₁ h₂ C₁ C₂).IsCauchySurfaceOn (sheet₂ h₁ h₂) (lift h₁ h₂ S) := by
    rw [lift_eq_image_ι₂ hSA]
    exact (IsEMorphismOn.isCauchySurfaceOn_image_iff hE₂
      (Gluing.injective_ι₂ (inclusion_injective h₁) (inclusion_injective h₂)).injOn le_rfl
      (U := sheet₂ h₁ h₂) (by rw [Opens.coe_top, image_univ]; rfl) (subset_univ _)).1
      ((C₂.isCauchySurfaceOn_iff_restrict_toSubtype hSU₂).1 hS₂)
  have hac : ∀ x ∈ lift h₁ h₂ S, ∀ y ∈ lift h₁ h₂ S,
      (gluedCausality h₁ h₂ C₁ C₂).le (sheet₁ h₁ h₂) x y → x = y := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    rw [gluedCausality_le_sheet₁_iff hC] at h
    exact congrArg _ (Subtype.ext (hS₁.isAcausalOn_of_t1_secondCountable harc₁ _ ha _ hb h))
  refine ⟨hT2, isLocalHomeomorph_proj U₁.isOpen U₂.isOpen A.isOpen, hTP, hcaus,
    hTP.isCauchySurface hcaus (fun _ ⟨x, _, hx⟩ => hx ▸ ⟨x, rfl⟩) hc₁ hc₂ hac, ?_⟩
  rw [proj_image_lift, inter_eq_left.2 hSU₁]

/-! ## 4. Injectivity and agreement are two statements -/

/-- **Injectivity gives agreement**: if `π` is injective, two functions agreeing on `A` agree on
all of `U₁ ∩ U₂` (`injective_proj_iff`: then `U₁ ∩ U₂ ⊆ A`). -/
theorem eqOn_inter_of_injective_proj {β : Type v} {u₁ u₂ : M → β} (hu : EqOn u₁ u₂ A)
    (hinj : Injective (proj h₁ h₂)) : EqOn u₁ u₂ ((U₁ : Set M) ∩ U₂) :=
  fun _ hx => hu (injective_proj_iff.1 hinj hx)

/-- **A connected `S` Cauchy in the overlap gives injectivity**: then `U₁ ∩ U₂` is connected
(`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`), so the Hausdorff gluing along the
non-empty open `A ⊇ S` is all of it (`eq_inter_of_t2Space`) and `π` is an open embedding. -/
theorem isOpenEmbedding_proj_of_isCauchySurfaceOn_inf [T2Space M] [SecondCountableTopology M]
    {C : Causality M} {S : Set M} (hSc : IsPreconnected S) (hSne : S.Nonempty) (hSA : S ⊆ A)
    (hS : C.IsCauchySurfaceOn (U₁ ⊓ U₂) S) (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A) :
    IsOpenEmbedding (proj h₁ h₂) := by
  haveI : T2Space (EtaleGluing h₁ h₂) := (t2Space_iff A.isOpen).2 hclosed
  have hc : IsPreconnected ((U₁ : Set M) ∩ U₂) :=
    Causality.isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable (W := U₁ ⊓ U₂) hSc
      (fun _ hx => show _ ∈ (U₁ : Set M) ∩ U₂ from ⟨h₁ (hSA hx), h₂ (hSA hx)⟩) hS
  obtain ⟨s, hs⟩ := hSne
  have he := eq_inter_of_t2Space (h₁ := h₁) (h₂ := h₂) A.isOpen ⟨s, hSA hs⟩ hc
  exact isOpenEmbedding_proj U₁.isOpen U₂.isOpen A.isOpen fun _ hx => by rw [he]; exact hx

end EtaleGluing

/-! ## 5. Developments of one initial value problem -/

section Developments

variable {β : Type v}

/-- **The chronological relation follows the solution**: the `≪` twin of `CausalityFollows`
(`Causal.ErsMughd`): if `u = v` on `W`, the causalities of `u` and `v` have the same `≪_V` on
every open `V ≤ W`. Supplier: as `CausalityFollows`, `g(u, du)` depends on `u`, `du` only. -/
def CausalityFollowsLt (cau : (M → β) → Causality M) : Prop :=
  ∀ ⦃u v : M → β⦄ ⦃W : Opens M⦄, EqOn u v W → ∀ V : Opens M, V ≤ W → ∀ x y,
    (cau u).lt V x y ↔ (cau v).lt V x y

/-- `CausalityFollows` and its `≪` twin make the causalities of two solutions agree where the
solutions do. -/
theorem CausalityFollows.agreeOn {cau : (M → β) → Causality M} (h : CausalityFollows cau)
    (h' : CausalityFollowsLt cau) {u v : M → β} {W : Opens M} (huv : EqOn u v W) :
    AgreeOn (cau u) (cau v) W :=
  fun V hV x y => ⟨h huv V hV x y, h' huv V hV x y⟩

variable {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M} {S : Set M}
  {U₁ U₂ A : Opens M} {u₁ u₂ : M → β}

open EtaleGluing

/-- **Two developments glued along a common development form a development over the background in
the étale sense** (ERS 1802.03020 §4.2, `ghd_02_19.tex:852`, the causal half). `(U₁, u₁)`,
`(U₂, u₂)` developments of `S`; `A` a common development of `S` (ERS's CGHD: `A ≤ U₁ ⊓ U₂`,
`S ⊆ A`, `u₁ = u₂` on `A`, `S` Cauchy in `A`), closed in `U₁ ∩ U₂` as ERS's MCGHD is (`:850`);
the causality follows the solution, for `≤` and `≪`; each piece antisymmetric and causally
arc-connected. Then on `E = U₁ ⊔_A U₂` the glued causality of `cau u₁` on `U₁` and `cau u₂` on
`U₂` exists and restricts to them (`IsGluingCausality`); `E` is Hausdorff and étale over `M`;
the glued causality is two-piece and causal; the lifted `S` is a Cauchy surface of `E` over `S`;
the glued solution `ũ` is `u₁` on the first sheet, `u₂` on the second; and `E` is second
countable. -/
theorem ers_etale_development [T2Space M] [SecondCountableTopology M]
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (hfollow : CausalityFollows cau) (hfollowLt : CausalityFollowsLt cau)
    (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂)
    (hA : (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) A)
    (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A)
    (hanti₁ : ∀ ⦃x y : M⦄, (cau u₁).le U₁ x y → (cau u₁).le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, (cau u₂).le U₂ x y → (cau u₂).le U₂ y x → x = y)
    (harc₁ : (cau u₁).CausallyArcConnectedOn U₁) (harc₂ : (cau u₂).CausallyArcConnectedOn U₂) :
    Gluing.IsGluingCausality (isOpenEmbedding_inclusion h₁ A.isOpen)
        (isOpenEmbedding_inclusion h₂ A.isOpen) (gluedCausality h₁ h₂ (cau u₁) (cau u₂))
        (((cau u₁).restrict U₁).toSubtype) (((cau u₂).restrict U₂).toSubtype) ∧
      T2Space (EtaleGluing h₁ h₂) ∧ IsLocalHomeomorph (proj h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).TwoPiece (sheet₁ h₁ h₂) (sheet₂ h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCausal ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCauchySurface (lift h₁ h₂ S) ∧
      proj h₁ h₂ '' lift h₁ h₂ S = S ∧
      glue h₁ h₂ u₁ u₂ hA.agree ∘ Gluing.ι₁ (inclusion h₁) (inclusion h₂) = u₁ ∘ Subtype.val ∧
      glue h₁ h₂ u₁ u₂ hA.agree ∘ Gluing.ι₂ (inclusion h₁) (inclusion h₂) = u₂ ∘ Subtype.val ∧
      SecondCountableTopology (EtaleGluing h₁ h₂) := by
  have hC : AgreeOn (cau u₁) (cau u₂) A := hfollow.agreeOn hfollowLt hA.agree
  obtain ⟨hT2, hloc, hTP, hcaus, hcauchy, hproj⟩ := isEtaleDevelopment (h₁ := h₁) (h₂ := h₂) hC
    hanti₁ hanti₂ harc₁ harc₂ hA.subset hA.cauchy hd₁.cauchy hd₂.cauchy hclosed
  exact ⟨Gluing.isGluingCausality_causality ((compatibleAlong_iff_agreeOn (h₁ := h₁)
    (h₂ := h₂)).2 hC), hT2, hloc, hTP, hcaus, hcauchy, hproj, rfl, rfl,
    secondCountableTopology A.isOpen⟩

/-- **ERS Thm 3.45 read on the étale development** (`ersthm:ThmNonUniqueness`, `:560`, unmarked):
under `ers_etale_development`'s hypotheses, a point `x ∈ U₁ ∩ U₂` with `u₁ x ≠ u₂ x` lies off
`A` and is doubled in the étale development `E` (Hausdorff, causal, with `S` lifted to a Cauchy
surface): `π` is not injective, and the glued solution lives on no subset of `M`. -/
theorem ers_theorem_3_45_etale [T2Space M] [SecondCountableTopology M]
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (hfollow : CausalityFollows cau) (hfollowLt : CausalityFollowsLt cau)
    (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂)
    (hA : (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) A)
    (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A)
    (hanti₁ : ∀ ⦃x y : M⦄, (cau u₁).le U₁ x y → (cau u₁).le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, (cau u₂).le U₂ x y → (cau u₂).le U₂ y x → x = y)
    (harc₁ : (cau u₁).CausallyArcConnectedOn U₁) (harc₂ : (cau u₂).CausallyArcConnectedOn U₂)
    {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) (hne : u₁ x ≠ u₂ x) :
    T2Space (EtaleGluing h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).TwoPiece (sheet₁ h₁ h₂) (sheet₂ h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCausal ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCauchySurface (lift h₁ h₂ S) ∧
      x ∉ A ∧
      Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩ ≠
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩ ∧
      ¬ Injective (proj h₁ h₂) ∧ ¬ ∃ v : M → β, glue h₁ h₂ u₁ u₂ hA.agree = v ∘ proj h₁ h₂ := by
  obtain ⟨-, hT2, -, hTP, hcaus, hcauchy, -⟩ := ers_etale_development hd₁ hd₂ hfollow hfollowLt
    h₁ h₂ hA hclosed hanti₁ hanti₂ harc₁ harc₂
  obtain ⟨hxA, hne', hinj, hdesc⟩ := not_injective_and_not_descends (h₁ := h₁) (h₂ := h₂)
    (hu := hA.agree) hx₁ hx₂ hne
  exact ⟨hT2, hTP, hcaus, hcauchy, hxA, hne', hinj, hdesc⟩

/-- **ERS Cor 4.68 read on the étale development** (`erscor:CorDisCon`, `:921`, unmarked): if
`(U₁, u₁)` is a development and `A` a common development closed in `U₁ ∩ U₂`, a point of
`U₁ ∩ U₂` where `u₁ ≠ u₂` makes `U₁ ∩ U₂` disconnected (`not_isPreconnected_inter`: the gluing
is Hausdorff; `A ⊇ S` is non-empty because `S` is a Cauchy surface of `U₁ ∋ x`). That `A` may be
taken to be ERS's MCGHD, closed in `U₁ ∩ U₂`, is Thm 4.64's content, not proved here. -/
theorem ers_corollary_4_68_etale [T2Space M] [SecondCountableTopology M]
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂)
    (hA : (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) A)
    (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A) {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (hne : u₁ x ≠ u₂ x) : ¬ IsPreconnected ((U₁ : Set M) ∩ U₂) := by
  haveI : T2Space (EtaleGluing h₁ h₂) := (t2Space_iff A.isOpen).2 hclosed
  obtain ⟨I, c, hc, -⟩ := Causality.inextensibleThrough_of_t1_secondCountable (cau u₁) U₁ x hx₁
  obtain ⟨s, ⟨-, hs⟩, -⟩ := hd₁.cauchy I c hc
  exact not_isPreconnected_inter (h₁ := h₁) (h₂ := h₂) A.isOpen ⟨s, hA.subset hs⟩ hA.agree hx₁
    hx₂ hne

/-- The component of `U₁ ∩ U₂` through `x` (`Causal.componentOpens`, ERS's MCGHD at `:850` when
it is the component through `S`) lies in `U₁`. -/
theorem componentOpens_inf_subset_left [LocallyConnectedSpace M] (U₁ U₂ : Opens M) (x : M) :
    (componentOpens (U₁ ⊓ U₂) x : Set M) ⊆ U₁ :=
  fun _ hz => (componentOpens_le _ x hz).1

/-- The component of `U₁ ∩ U₂` through `x` lies in `U₂`. -/
theorem componentOpens_inf_subset_right [LocallyConnectedSpace M] (U₁ U₂ : Opens M) (x : M) :
    (componentOpens (U₁ ⊓ U₂) x : Set M) ⊆ U₂ :=
  fun _ hz => (componentOpens_le _ x hz).2

/-- **`ers_etale_development` along the component of `U₁ ∩ U₂` through a point of `S`** (ERS
`:850`–`:852`): with `M` locally connected and `S` connected, the component `A` contains `S`, and
the gluing along it is Hausdorff (`t2Space_connectedComponentIn`), so `A` closed in `U₁ ∩ U₂` is
not asked. `u₁ = u₂` on `A` and `S` Cauchy in `A` stay hypotheses: that the MCGHD is this
component is Thm 4.64's content. `h₁`, `h₂` always hold (`componentOpens_inf_subset_left`,
`_right`); they name the gluing. -/
theorem ers_etale_development_component [T2Space M] [SecondCountableTopology M]
    [LocallyConnectedSpace M]
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (hfollow : CausalityFollows cau) (hfollowLt : CausalityFollowsLt cau)
    (hSc : IsPreconnected S) {x₀ : M} (hx₀ : x₀ ∈ S)
    (h₁ : (componentOpens (U₁ ⊓ U₂) x₀ : Set M) ⊆ U₁)
    (h₂ : (componentOpens (U₁ ⊓ U₂) x₀ : Set M) ⊆ U₂)
    (hagree : EqOn u₁ u₂ (componentOpens (U₁ ⊓ U₂) x₀ : Set M))
    (hcauchy : (cau u₁).IsCauchySurfaceOn (componentOpens (U₁ ⊓ U₂) x₀) S)
    (hanti₁ : ∀ ⦃x y : M⦄, (cau u₁).le U₁ x y → (cau u₁).le U₁ y x → x = y)
    (hanti₂ : ∀ ⦃x y : M⦄, (cau u₂).le U₂ x y → (cau u₂).le U₂ y x → x = y)
    (harc₁ : (cau u₁).CausallyArcConnectedOn U₁) (harc₂ : (cau u₂).CausallyArcConnectedOn U₂) :
    T2Space (EtaleGluing h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).TwoPiece (sheet₁ h₁ h₂) (sheet₂ h₁ h₂) ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCausal ∧
      (gluedCausality h₁ h₂ (cau u₁) (cau u₂)).IsCauchySurface (lift h₁ h₂ S) := by
  have hSF : S ⊆ (U₁ : Set M) ∩ U₂ := fun z hz => ⟨hd₁.subset hz, hd₂.subset hz⟩
  have hSA : S ⊆ (componentOpens (U₁ ⊓ U₂) x₀ : Set M) := hSc.subset_connectedComponentIn hx₀ hSF
  have hT2 : T2Space (EtaleGluing h₁ h₂) :=
    t2Space_connectedComponentIn U₁.isOpen U₂.isOpen (hSF hx₀)
  have hclosed := (t2Space_iff (componentOpens (U₁ ⊓ U₂) x₀).isOpen).1 hT2
  obtain ⟨-, hT2', -, hTP, hcaus, hcauchy', -⟩ := ers_etale_development hd₁ hd₂ hfollow hfollowLt
    h₁ h₂ ⟨componentOpens_le _ _, hSA, hagree, hcauchy⟩ hclosed hanti₁ hanti₂ harc₁ harc₂
  exact ⟨hT2', hTP, hcaus, hcauchy'⟩

/-- **Two developments agreeing on their overlap have a connected overlap, in ERS's subluminal
setting** (the claim argued in `Causal.ErsMughd`'s SCOPE, "two GHDs agreeing on their overlap
have a connected overlap"): `hsub`, `harc` as in `ers_remark_4_78`, `Cm` causal, `S` connected and
`Cm`-acausal. The glued solution `v` is a development of `U₁ ⊔ U₂` (`ers_remark_4_78`), `≤` of
`cau v` is antisymmetric there (subluminality), and `S` is Cauchy in `U₁`, `U₂` for `cau v`
(`CausalityFollows`), whence `isPreconnected_inter_of_isCauchySurfaceOn_sup`. -/
theorem ers_isPreconnected_inter_of_eqOn [T2Space M] [SecondCountableTopology M]
    {Cm : Causality M} (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S) (hSc : IsPreconnected S)
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (hagree : EqOn u₁ u₂ ((U₁ : Set M) ∩ U₂)) : IsPreconnected ((U₁ : Set M) ∩ U₂) := by
  classical
  set v : M → β := fun x => if x ∈ U₁ then u₁ x else u₂ x
  have hv₁ : EqOn v u₁ U₁ := fun x hx => if_pos hx
  have hv₂ : EqOn v u₂ U₂ := fun x hx => by
    by_cases h : x ∈ U₁
    · show (if x ∈ U₁ then u₁ x else u₂ x) = u₂ x
      rw [if_pos h]
      exact hagree ⟨h, hx⟩
    · show (if x ∈ U₁ then u₁ x else u₂ x) = u₂ x
      rw [if_neg h]
  let 𝒟 : Set (Opens M × (M → β)) := {(U₁, u₁), (U₂, u₂)}
  have hdev : ∀ d ∈ 𝒟, IsDevelopment sol cau S d.1 d.2 := by
    rintro d (rfl | rfl)
    exacts [hd₁, hd₂]
  have hvd : ∀ d ∈ 𝒟, EqOn v d.2 d.1 := by
    rintro d (rfl | rfl)
    exacts [hv₁, hv₂]
  have hsSup : sSup (Prod.fst '' 𝒟) = U₁ ⊔ U₂ := by
    rw [image_pair, sSup_pair]
  have hdv := ers_remark_4_78 hloc hglue hfollow hsub harc hm hmacausal ⟨_, Or.inl rfl⟩ hdev hvd
  rw [hsSup] at hdv
  have hanti := Causality.antisymm_of_curveNestedOn (harc _ _ hdv.solves) (hsub _ _ hdv.solves) hm
  have hc₁ : (cau v).IsCauchySurfaceOn U₁ S :=
    Causality.isCauchySurfaceOn_of_agree (fun V hV x y => hfollow hv₁.symm V hV x y) hd₁.cauchy
  have hc₂ : (cau v).IsCauchySurfaceOn U₂ S :=
    Causality.isCauchySurfaceOn_of_agree (fun V hV x y => hfollow hv₂.symm V hV x y) hd₂.cauchy
  exact Causality.isPreconnected_inter_of_isCauchySurfaceOn_sup hanti hSc
    (fun z hz => ⟨hd₁.subset hz, hd₂.subset hz⟩) hc₁ hc₂ hdv.cauchy

/-- **The hypotheses of `ers_isOpenEmbedding_proj_of_eqOn` force `A = U₁ ∩ U₂`**, on every
background: the overlap is connected (`ers_isPreconnected_inter_of_eqOn`), and `A` is a non-empty
open subset of it, closed in it (`hclosed`). So the gluing of that theorem is always the trivial
one, along the whole overlap. -/
theorem ers_coe_eq_inter_of_eqOn [T2Space M] [SecondCountableTopology M]
    {Cm : Causality M} (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S) (hSc : IsPreconnected S)
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂) (hSA : S ⊆ A)
    (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A) (hagree : EqOn u₁ u₂ ((U₁ : Set M) ∩ U₂)) :
    (A : Set M) = (U₁ : Set M) ∩ U₂ := by
  have hconn := ers_isPreconnected_inter_of_eqOn hloc hglue hfollow hsub harc hm hmacausal hSc
    hd₁ hd₂ hagree
  haveI : T2Space (EtaleGluing h₁ h₂) := (EtaleGluing.t2Space_iff A.isOpen).2 hclosed
  refine Subset.antisymm (subset_inter h₁ h₂) fun x hx => ?_
  obtain ⟨I, c, hc, -⟩ := Causality.inextensibleThrough_of_t1_secondCountable (cau u₁) U₁ x hx.1
  obtain ⟨s, ⟨-, hs⟩, -⟩ := hd₁.cauchy I c hc
  rw [EtaleGluing.eq_inter_of_t2Space (h₁ := h₁) (h₂ := h₂) A.isOpen ⟨s, hSA hs⟩ hconn]
  exact hx

/-- **Agreement gives injectivity in ERS's subluminal setting** (reported for
`T-abs-ers-etale-mghd`): under `ers_isPreconnected_inter_of_eqOn`'s hypotheses, two developments
agreeing on all of `U₁ ∩ U₂` have a connected overlap, so the Hausdorff gluing along any open
`A ⊇ S` closed in `U₁ ∩ U₂` is `U₁ ∪ U₂`: `π` is an open embedding. It is the corollary of the
sharp form just above, `ers_coe_eq_inter_of_eqOn`: its hypotheses force `A = U₁ ∩ U₂`, and
`isOpenEmbedding_proj` applies. So "any open `A`" ranges over one set: it says nothing of gluing
along a proper common development (ERS `:852`); beyond `ers_isPreconnected_inter_of_eqOn` its
content is `eq_inter_of_t2Space`. -/
theorem ers_isOpenEmbedding_proj_of_eqOn [T2Space M] [SecondCountableTopology M]
    {Cm : Causality M} (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U)
    (hm : Cm.IsCausal) (hmacausal : Cm.IsAcausal S) (hSc : IsPreconnected S)
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (h₁ : (A : Set M) ⊆ U₁) (h₂ : (A : Set M) ⊆ U₂) (hSA : S ⊆ A)
    (hclosed : (U₁ : Set M) ∩ U₂ ∩ closure A ⊆ A) (hagree : EqOn u₁ u₂ ((U₁ : Set M) ∩ U₂)) :
    IsOpenEmbedding (proj h₁ h₂) :=
  isOpenEmbedding_proj U₁.isOpen U₂.isOpen A.isOpen (ers_coe_eq_inter_of_eqOn hloc hglue hfollow
    hsub harc hm hmacausal hSc hd₁ hd₂ h₁ h₂ hSA hclosed hagree).superset

end Developments

/-! ## 6. Witness (kb/0011): the timelike line, `S = {0}` -/

namespace EtaleGluing

/-- `]-2, 1[`, the first development domain of the witness. -/
def lineU₁ : Opens ℝ := ⟨Ioo (-2) 1, isOpen_Ioo⟩

/-- `]-1, 2[`, the second development domain of the witness. -/
def lineU₂ : Opens ℝ := ⟨Ioo (-1) 2, isOpen_Ioo⟩

/-- `]-1, 1[`, the common development of the witness. -/
def lineA : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩

theorem lineA_subset₁ : (lineA : Set ℝ) ⊆ lineU₁ :=
  fun x (hx : x ∈ Ioo (-1 : ℝ) 1) => show x ∈ Ioo (-2 : ℝ) 1 from ⟨by linarith [hx.1], hx.2⟩

theorem lineA_subset₂ : (lineA : Set ℝ) ⊆ lineU₂ :=
  fun x (hx : x ∈ Ioo (-1 : ℝ) 1) => show x ∈ Ioo (-1 : ℝ) 2 from ⟨hx.1, by linarith [hx.2]⟩

/-- `-3/2`, a point of the first sheet off the overlap. -/
noncomputable def lineP₁ : (lineU₁ : Set ℝ) :=
  ⟨-3 / 2, show (-3 / 2 : ℝ) ∈ Ioo (-2 : ℝ) 1 by norm_num⟩

/-- `3/2`, a point of the second sheet off the overlap. -/
noncomputable def lineP₂ : (lineU₂ : Set ℝ) :=
  ⟨3 / 2, show (3 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num⟩

/-- **The hypotheses of `isEtaleDevelopment` hold jointly on the timelike line** with
`U₁ = ]-2, 1[`, `U₂ = ]-1, 2[`, `A = ]-1, 1[`, `S = {0}`, and the gluing is a proper two-piece
spacetime: `ι₁(-3/2)` is off the second sheet, `ι₂(3/2)` off the first, and the glued causality
relates them across the overlap. -/
theorem timelikeLine_etale_witness :
    AgreeOn timelikeLine timelikeLine lineA ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le lineU₁ x y → timelikeLine.le lineU₁ y x → x = y) ∧
      (∀ ⦃x y : ℝ⦄, timelikeLine.le lineU₂ x y → timelikeLine.le lineU₂ y x → x = y) ∧
      timelikeLine.CausallyArcConnectedOn lineU₁ ∧ timelikeLine.CausallyArcConnectedOn lineU₂ ∧
      ({0} : Set ℝ) ⊆ lineA ∧ timelikeLine.IsCauchySurfaceOn lineA {0} ∧
      timelikeLine.IsCauchySurfaceOn lineU₁ {0} ∧ timelikeLine.IsCauchySurfaceOn lineU₂ {0} ∧
      (lineU₁ : Set ℝ) ∩ lineU₂ ∩ closure lineA ⊆ lineA ∧
      Gluing.ι₁ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₁ ∉
        sheet₂ lineA_subset₁ lineA_subset₂ ∧
      Gluing.ι₂ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₂ ∉
        sheet₁ lineA_subset₁ lineA_subset₂ ∧
      (gluedCausality lineA_subset₁ lineA_subset₂ timelikeLine timelikeLine).le ⊤
        (Gluing.ι₁ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₁)
        (Gluing.ι₂ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₂) := by
  have hC : AgreeOn timelikeLine timelikeLine lineA := fun _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩
  have hanti : ∀ U : Opens ℝ, ∀ ⦃x y : ℝ⦄, timelikeLine.le U x y → timelikeLine.le U y x →
      x = y := fun _ _ _ h h' => le_antisymm (timelikeLine_le.1 h).1 (timelikeLine_le.1 h').1
  have h0A : (0 : ℝ) ∈ (lineA : Set ℝ) := show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num
  refine ⟨hC, hanti _, hanti _,
    Causality.CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top,
    Causality.CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top,
    singleton_subset_iff.2 h0A,
    timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by norm_num) (by norm_num) rfl,
    timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by norm_num) (by norm_num) rfl,
    timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by norm_num) (by norm_num) rfl,
    fun z hz => show z ∈ Ioo (-1 : ℝ) 1 from ⟨hz.1.2.1, hz.1.1.2⟩, ?_, ?_, ?_⟩
  · rw [ι₁_mem_sheet₂_iff]
    show ¬ ((-3 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1)
    norm_num
  · rw [ι₂_mem_sheet₁_iff]
    show ¬ ((3 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1)
    norm_num
  · set D := gluedCausality lineA_subset₁ lineA_subset₂ timelikeLine timelikeLine
    have e : Gluing.ι₁ (inclusion lineA_subset₁) (inclusion lineA_subset₂)
        ⟨0, lineA_subset₁ h0A⟩ =
        Gluing.ι₂ (inclusion lineA_subset₁) (inclusion lineA_subset₂) ⟨0, lineA_subset₂ h0A⟩ :=
      ι₁_eq_ι₂_iff.2 ⟨rfl, h0A⟩
    have hl : D.le (sheet₁ lineA_subset₁ lineA_subset₂)
        (Gluing.ι₁ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₁)
        (Gluing.ι₁ (inclusion lineA_subset₁) (inclusion lineA_subset₂) ⟨0, lineA_subset₁ h0A⟩) := by
      refine (gluedCausality_le_sheet₁_iff hC).2 (timelikeLine_le.2 ⟨?_, fun w hw => ?_⟩)
      · show (-3 / 2 : ℝ) ≤ 0
        norm_num
      · have hw' : (-3 / 2 : ℝ) ≤ w ∧ w ≤ 0 := hw
        exact show w ∈ Ioo (-2 : ℝ) 1 from ⟨by linarith [hw'.1], by linarith [hw'.2]⟩
    have hr : D.le (sheet₂ lineA_subset₁ lineA_subset₂)
        (Gluing.ι₂ (inclusion lineA_subset₁) (inclusion lineA_subset₂) ⟨0, lineA_subset₂ h0A⟩)
        (Gluing.ι₂ (inclusion lineA_subset₁) (inclusion lineA_subset₂) lineP₂) := by
      refine (gluedCausality_le_sheet₂_iff hC).2 (timelikeLine_le.2 ⟨?_, fun w hw => ?_⟩)
      · show (0 : ℝ) ≤ 3 / 2
        norm_num
      · have hw' : (0 : ℝ) ≤ w ∧ w ≤ 3 / 2 := hw
        exact show w ∈ Ioo (-1 : ℝ) 2 from ⟨by linarith [hw'.1], by linarith [hw'.2]⟩
    rw [e] at hl
    exact D.le_trans (D.le_mono le_top hl) (D.le_mono le_top hr)

/-- `isEtaleDevelopment` at the witness: `E = ]-2, 1[ ⊔_{]-1,1[} ]-1, 2[` is Hausdorff, étale over
`ℝ`, two-piece and causal, with `{0}` lifted to a Cauchy surface. -/
theorem timelikeLine_isEtaleDevelopment :
    T2Space (EtaleGluing lineA_subset₁ lineA_subset₂) ∧
      IsLocalHomeomorph (proj lineA_subset₁ lineA_subset₂) ∧
      (gluedCausality lineA_subset₁ lineA_subset₂ timelikeLine timelikeLine).TwoPiece
        (sheet₁ lineA_subset₁ lineA_subset₂) (sheet₂ lineA_subset₁ lineA_subset₂) ∧
      (gluedCausality lineA_subset₁ lineA_subset₂ timelikeLine timelikeLine).IsCausal ∧
      (gluedCausality lineA_subset₁ lineA_subset₂ timelikeLine timelikeLine).IsCauchySurface
        (lift lineA_subset₁ lineA_subset₂ {0}) ∧
      proj lineA_subset₁ lineA_subset₂ '' lift lineA_subset₁ lineA_subset₂ {0} = {0} := by
  obtain ⟨hC, ha₁, ha₂, hc₁, hc₂, hSA, hS, hS₁, hS₂, hcl, -⟩ := timelikeLine_etale_witness
  exact isEtaleDevelopment hC ha₁ ha₂ hc₁ hc₂ hSA hS hS₁ hS₂ hcl

/-- **The hypotheses of `ers_etale_development` hold jointly on the timelike line**: the problem
whose every function solves everywhere, its causality the timelike line whatever the solution,
`u₁ = u₂ = 0`, the domains of `timelikeLine_etale_witness`. -/
theorem timelikeLine_ers_etale_witness :
    IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} lineU₁ 0 ∧
      IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} lineU₂ 0 ∧
      CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) ∧
      CausalityFollowsLt (fun _ : ℝ → ℝ => timelikeLine) ∧
      timelikeLine.IsCommonDevelopment {0} lineU₁ lineU₂ (fun V => EqOn (0 : ℝ → ℝ) 0 V) lineA := by
  obtain ⟨-, -, -, -, -, hSA, hS, hS₁, hS₂, -⟩ := timelikeLine_etale_witness
  exact ⟨⟨trivial, hSA.trans lineA_subset₁, hS₁⟩, ⟨trivial, hSA.trans lineA_subset₂, hS₂⟩,
    fun _ _ _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl,
    ⟨fun _ hz => ⟨lineA_subset₁ hz, lineA_subset₂ hz⟩, hSA, eqOn_refl _ _, hS⟩⟩

end EtaleGluing

end Causal
