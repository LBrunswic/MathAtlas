import Causal.GluingHausdorff
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Data.Set.Card

/-!
# The Einstein-style gluing of two open sets along an open subset is étale over their union

Programme target `T-abs-ers-etale-gluing` (`programme/roadmap.toml`; layer 1, pure topology, no
causality, no metric, `uses = []`). It is the topological half of `T-abs-ers-etale-mghd`. Source:
Eperon–Reall–Sbierski, arXiv 1802.03020, §4.2 (`papers/ers-predictability`,
`legacy/labeled/ghd_02_19.tex`). **No label is marked**. The six binder rows that name
`T-abs-ers-etale-mghd` (`ersthm:diffeo_theorem`, `erslem:nec_cond`, `erslem:lemma_sing`,
`erslem:sep_lemma`, `ersthm:global_theorem`, `ersthm:ThmNonUniqueness`) are not closed here.

For `U₁ U₂ A : Set M` with `A ⊆ U₁ ∩ U₂`, `EtaleGluing h₁ h₂` is `Causal.Gluing` of the two
inclusions `A → U₁`, `A → U₂` (`E = U₁ ⊔_A U₂`), and `EtaleGluing.proj` is
`π := Gluing.desc` of the two coercions to `M`. The assertions:

* `1-etale` — `proj_comp_ι₁`, `proj_comp_ι₂`, `range_proj` (`range π = U₁ ∪ U₂`),
  `isLocalHomeomorph_proj` (`U₁`, `U₂`, `A` open), and its corestriction
  `isLocalHomeomorph_codRestrict_proj`, a surjective local homeomorphism onto `U₁ ∪ U₂`;
  `secondCountableTopology` (`E` second countable when `M` is).
* `2-injective` — `injective_proj_iff` (`π` injective iff `U₁ ∩ U₂ ⊆ A`, no topology),
  `isOpenEmbedding_proj` and `exists_homeomorph` (then `E ≃ₜ U₁ ∪ U₂` over `M`). The fibres:
  `preimage_proj_singleton_of_mem_inter` (over `x ∈ U₁ ∩ U₂` it is `{ι₁ x, ι₂ x}`), two points
  over `U₁ ∩ U₂ ∖ A` (`ι₁_ne_ι₂`, `encard_preimage_proj_singleton_of_notMem`), one point over the
  rest of `U₁ ∪ U₂` (`preimage_proj_singleton_of_mem`), none off it. "Contains the other
  components twice": `preimage_proj_eq_union`, `disjoint_image_ι₁_image_ι₂`.
* `3-hausdorff` — `isCorrespondingBoundaryPair_of_mem` and `subset_of_t2Space` (any `M`: a point
  of `U₁ ∩ U₂ ∩ closure A ∖ A` gives a corresponding pair, so `E` Hausdorff forces
  `U₁ ∩ U₂ ∩ closure A ⊆ A`); with `M` Hausdorff, `isCorrespondingBoundaryPair_iff` (the
  corresponding boundary pairs are exactly these `(x, x)`), `t2Space_iff`
  (`T2Space E ↔ U₁ ∩ U₂ ∩ closure A ⊆ A`), `t2Space_iff_isClosed` (`A` closed in `U₁ ∩ U₂`),
  `t2Space_iff_eq_connectedComponentIn` (for a connected `A`: Hausdorff iff `A` is a connected
  component of `U₁ ∩ U₂`), `t2Space_connectedComponentIn` (ERS's MCGHD, a component of
  `U₁ ∩ U₂` in a locally connected `M`, `:850`), `eq_inter_of_t2Space` (any `M`: Hausdorff, `A`
  non-empty, `U₁ ∩ U₂` connected force `A = U₁ ∩ U₂`).
* `4-descent` — `glue` (the glued function `ũ` of `u₁`, `u₂` agreeing on `A`), `glue_comp_ι₁`,
  `glue_comp_ι₂`, `continuous_glue`, `exists_glue_eq_comp_proj_iff`
  (`(∃ v, ũ = v ∘ π) ↔ EqOn u₁ u₂ (U₁ ∩ U₂)`), `glue_eq_ite_comp_proj` (the `v`: `u₁` on `U₁`,
  `u₂` off it, which is `Causal.glueSolutions ⟨U₁, _⟩ u₁ u₂` by `rfl`), Thm 3.45's reading
  `not_injective_and_not_descends`, and Cor 4.68's shape `not_isPreconnected_inter`.
* `5-witnesses` on `ℝ`: `punctured_witness` (`U₁ = U₂ = ℝ ∖ {0}`, `A = (0, ∞)`, a component:
  Hausdorff, `π` not injective, `ũ` of `0` and `1_{(-∞,0)}` does not descend, `ũ` of `0` and `0`
  does; `punctured_not_isPreconnected`), `branching_witness` (`U₁ = U₂ = ℝ`, `A = (0, ∞)`: not
  Hausdorff, `(0, 0)` corresponding).

> Note that if $U_1 \cap U_2$ is disconnected, the same argument shows that the domain $W$ of the
> MCGHD equals the connected component of $U_1 \cap U_2$ that contains $S$. (`:850`)

> However, in the case that $u_1$ and $u_2$ are two globally hyperbolic developments of a
> quasilinear wave equation on a fixed background such that $U_1 \cap U_2$ is disconnected,
> glueing them together along the MCGHD (which equals the connected component of $U_1 \cap U_2$
> which contains the initial data hypersurface), would yield a solution which is no longer defined
> on a subset of $\R^{d+1}$, but instead on a manifold which projects down on
> $U_1 \cup U_2 \subseteq \R^{d+1}$ and contains the other connected components of
> $U_1 \cap U_2$ twice. (`:852`)

> For the equation \eqref{Eqc1} there exist two GHDs $\Phi_a : U_a \to \R$ and
> $\Phi_b : U_b \to \R$ of the same initial data posed on $\{x^0=0\}$ such that there exists an
> $x \in U_a \cap U_b$ with $\Phi_a(x) \neq \Phi_b(x)$. (Thm 3.45, `:560`)

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| `U₁`, `U₂` open in `ℝ^{d+1}` | ⚠ weakened: `U₁ U₂ : Set M`, any space `M`; `IsOpen U₁`, `IsOpen U₂` only for `1-etale`, `2-injective`'s open embedding and the component's openness (`t2Space_connectedComponentIn`) |
| the MCGHD `A` open, `A ⊆ U₁ ∩ U₂` | ✓ carried: `A ⊆ U₁`, `A ⊆ U₂`; `IsOpen A` where the topology of the gluing is used |
| `A` the component of `U₁ ∩ U₂` containing `S` (`:850`) | ⚠ weakened: any open `A`; the component is one case (`t2Space_connectedComponentIn`) |
| `ℝ^{d+1}` Hausdorff, locally connected | ⚠ weakened: `[T2Space M]` only for the converse half of `3-hausdorff` (`subset_of_t2Space` has none), `[LocallyConnectedSpace M]` only for the component to be open |
| `u₁ = u₂` on the MCGHD | ✓ carried: `EqOn u₁ u₂ A`; `u₁`, `u₂ : M → β`, any `β`, no regularity (`continuous_glue` asks continuity on `U₁`, `U₂`) |
| "a manifold": `E` a smooth manifold, `ũ` a solution | its topology proved: `E` Hausdorff (`t2Space_connectedComponentIn`), second countable (`secondCountableTopology`), étale over `U₁ ∪ U₂` (`isLocalHomeomorph_proj`); not formalized: the smooth structure (the charts `π` pulled back) and the PDE (layer 3) |

## SCOPE (disclosed)

* **Subtypes.** `E` is a new space, so the gluing is of the subtypes `↥A → ↥U₁`, `↥A → ↥U₂`
  (`Causal.Gluing` as `Causal.CBG.PairGluing` does); no causality is involved, so the convention
  of `kb/0001` (relations indexed by open sets of `M`) has nothing to index here.
* **What is new.** `Causal.Pushout` and `Causal.GluingHausdorff` give the gluing of any open
  embeddings, its universal property and its Hausdorff criterion. New here: the projection to the
  ambient space and its étale property, the injectivity criterion and the fibres, the computation
  of the corresponding boundary pairs of two open subsets of one Hausdorff space, the component
  form, and the descent criterion of a glued function.
* **What stays for `T-abs-ers-etale-mghd`.** The causal half: the glued causality on `E`, that
  the lifted `S` is a Cauchy surface of `E`, that the MCGHD is the component of `U₁ ∩ U₂`
  containing `S` (ERS's argument, `:850`, Thm 4.64), and Lemma 3.32's separation of preimages
  (layer 3). Nothing here reads `A` as an MCGHD: `A` is any open subset.
* **"No longer defined on a subset" (`:852`).** Two different things fail here. The *space* `E`
  is not a subset of `M` as soon as `U₁ ∩ U₂ ⊄ A` (`injective_proj_iff`), whatever `u₁`, `u₂`.
  The *function* `ũ` fails to live on a subset of `M` exactly when `u₁ ≠ u₂` somewhere on
  `U₁ ∩ U₂` (`exists_glue_eq_comp_proj_iff`). The first can hold without the second
  (`punctured_witness`, last conjunct).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function

universe u v

variable {M : Type u} {U₁ U₂ A : Set M}

/-- The Einstein-style gluing `E = U₁ ⊔_A U₂` of `U₁` and `U₂` along `A ⊆ U₁ ∩ U₂`: the gluing
(`Causal.Gluing`) of the two inclusions `A → U₁`, `A → U₂`. -/
abbrev EtaleGluing (h₁ : A ⊆ U₁) (h₂ : A ⊆ U₂) : Type u :=
  Gluing (inclusion h₁) (inclusion h₂)

namespace EtaleGluing

/-- The projection `π : U₁ ⊔_A U₂ → M`: the two coercions descend. -/
def proj (h₁ : A ⊆ U₁) (h₂ : A ⊆ U₂) : EtaleGluing h₁ h₂ → M :=
  Gluing.desc (Subtype.val : U₁ → M) (Subtype.val : U₂ → M) fun _ => rfl

/-- The glued function `ũ` of two functions agreeing on `A`. -/
def glue {β : Type v} (h₁ : A ⊆ U₁) (h₂ : A ⊆ U₂) (u₁ u₂ : M → β) (hu : EqOn u₁ u₂ A) :
    EtaleGluing h₁ h₂ → β :=
  Gluing.desc (fun x : U₁ => u₁ x) (fun y : U₂ => u₂ y) fun w => hu w.2

variable {h₁ : A ⊆ U₁} {h₂ : A ⊆ U₂}

/-! ### Assertion 1: the projection -/

@[simp] theorem proj_ι₁ (x : U₁) :
    proj h₁ h₂ (Gluing.ι₁ (inclusion h₁) (inclusion h₂) x) = x := rfl

@[simp] theorem proj_ι₂ (y : U₂) :
    proj h₁ h₂ (Gluing.ι₂ (inclusion h₁) (inclusion h₂) y) = y := rfl

/-- `π ∘ ι₁` is the coercion of `U₁`. -/
theorem proj_comp_ι₁ :
    proj h₁ h₂ ∘ Gluing.ι₁ (inclusion h₁) (inclusion h₂) = Subtype.val := rfl

/-- `π ∘ ι₂` is the coercion of `U₂`. -/
theorem proj_comp_ι₂ :
    proj h₁ h₂ ∘ Gluing.ι₂ (inclusion h₁) (inclusion h₂) = Subtype.val := rfl

/-- `π` projects onto `U₁ ∪ U₂`. -/
theorem range_proj : range (proj h₁ h₂) = U₁ ∪ U₂ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases Gluing.exists_ι z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl y.2
    · exact Or.inr y.2
  · rintro (hx | hx)
    · exact ⟨Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx⟩, rfl⟩
    · exact ⟨Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx⟩, rfl⟩

/-- The two inclusions `A → U_i` agree on `A` and are injective: the identification is
`ι₁ x = ι₂ y ↔ x = y ∈ A`. -/
theorem ι₁_eq_ι₂_iff {x : U₁} {y : U₂} :
    Gluing.ι₁ (inclusion h₁) (inclusion h₂) x = Gluing.ι₂ (inclusion h₁) (inclusion h₂) y ↔
      (x : M) = y ∧ (x : M) ∈ A := by
  rw [Gluing.ι₁_eq_ι₂_iff (inclusion_injective h₁) (inclusion_injective h₂)]
  constructor
  · rintro ⟨w, rfl, rfl⟩
    exact ⟨rfl, w.2⟩
  · rintro ⟨hxy, hxA⟩
    exact ⟨⟨x, hxA⟩, Subtype.ext rfl, Subtype.ext hxy⟩

section Topology

variable [TopologicalSpace M]

/-- The inclusion of an open `A` in `U ⊇ A` is an open embedding. -/
theorem isOpenEmbedding_inclusion {U : Set M} (h : A ⊆ U) (hA : IsOpen A) :
    IsOpenEmbedding (inclusion h) :=
  IsOpenEmbedding.inclusion h (hA.preimage continuous_subtype_val)

theorem continuous_proj : Continuous (proj h₁ h₂) :=
  Gluing.continuous_desc continuous_subtype_val continuous_subtype_val

/-- **`π` is a local homeomorphism** (`1-etale`): each point lies in the open range of `ι₁` or of
`ι₂`, on which `π` is the open embedding of `U₁` or `U₂`. -/
theorem isLocalHomeomorph_proj (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hA : IsOpen A) :
    IsLocalHomeomorph (proj h₁ h₂) := by
  have hj₁ := isOpenEmbedding_inclusion h₁ hA
  have hj₂ := isOpenEmbedding_inclusion h₂ hA
  have k₁ : IsLocalHomeomorphOn (proj h₁ h₂)
      (Gluing.ι₁ (inclusion h₁) (inclusion h₂) '' univ) :=
    IsLocalHomeomorphOn.of_comp_right (f := Gluing.ι₁ (inclusion h₁) (inclusion h₂))
      hU₁.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (Gluing.isOpenEmbedding_ι₁ hj₁ hj₂).isLocalHomeomorph.isLocalHomeomorphOn
  have k₂ : IsLocalHomeomorphOn (proj h₁ h₂)
      (Gluing.ι₂ (inclusion h₁) (inclusion h₂) '' univ) :=
    IsLocalHomeomorphOn.of_comp_right (f := Gluing.ι₂ (inclusion h₁) (inclusion h₂))
      hU₂.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (Gluing.isOpenEmbedding_ι₂ hj₁ hj₂).isLocalHomeomorph.isLocalHomeomorphOn
  intro z
  rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact k₁ _ (mem_image_of_mem _ (mem_univ x))
  · exact k₂ _ (mem_image_of_mem _ (mem_univ y))

/-- `π` corestricted to `U₁ ∪ U₂` is a surjective local homeomorphism: `E` "projects down on
`U₁ ∪ U₂`" (`:852`). -/
theorem isLocalHomeomorph_codRestrict_proj (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hA : IsOpen A) :
    IsLocalHomeomorph (codRestrict (proj h₁ h₂) (U₁ ∪ U₂) fun z => range_proj ▸ mem_range_self z) ∧
      Surjective (codRestrict (proj h₁ h₂) (U₁ ∪ U₂) fun z => range_proj ▸ mem_range_self z) := by
  refine ⟨IsLocalHomeomorph.of_comp (g := (Subtype.val : ↥(U₁ ∪ U₂) → M))
    (isLocalHomeomorph_proj hU₁ hU₂ hA)
    (hU₁.union hU₂).isOpenEmbedding_subtypeVal.isLocalHomeomorph
    (continuous_proj.codRestrict _), ?_⟩
  rintro ⟨x, hx⟩
  rw [← range_proj (h₁ := h₁) (h₂ := h₂)] at hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, Subtype.ext hz⟩

/-- With `M` second countable, so is `E`: it is covered by the two open ranges of `ι₁`, `ι₂`,
homeomorphic to `U₁`, `U₂`. With `isLocalHomeomorph_proj` and `t2Space_iff`, this is the
topology of ERS's "manifold" (`:852`). -/
theorem secondCountableTopology [SecondCountableTopology M] (hA : IsOpen A) :
    SecondCountableTopology (EtaleGluing h₁ h₂) := by
  have hj₁ := isOpenEmbedding_inclusion h₁ hA
  have hj₂ := isOpenEmbedding_inclusion h₂ hA
  have e₁ := Gluing.isOpenEmbedding_ι₁ hj₁ hj₂
  have e₂ := Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
  let V : Bool → Set (EtaleGluing h₁ h₂) := fun b =>
    cond b (range (Gluing.ι₁ (inclusion h₁) (inclusion h₂)))
      (range (Gluing.ι₂ (inclusion h₁) (inclusion h₂)))
  haveI : ∀ b, SecondCountableTopology (V b) := by
    intro b
    cases b
    · exact e₂.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
    · exact e₁.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := V) (fun b => ?_) ?_
  · cases b
    · exact e₂.isOpen_range
    · exact e₁.isOpen_range
  · refine eq_univ_of_forall fun z => ?_
    rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact mem_iUnion.2 ⟨true, mem_range_self x⟩
    · exact mem_iUnion.2 ⟨false, mem_range_self y⟩

end Topology

/-! ### Assertion 2: injectivity and the fibres -/

/-- Two points of `E` over one point `x` are equal when `x ∈ U₁ ∩ U₂` forces `x ∈ A`. -/
theorem eq_of_proj_eq {z z' : EtaleGluing h₁ h₂} (h : proj h₁ h₂ z = proj h₁ h₂ z')
    (hA : proj h₁ h₂ z ∈ U₁ ∩ U₂ → proj h₁ h₂ z ∈ A) : z = z' := by
  rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases Gluing.exists_ι z' with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact congrArg _ (Subtype.ext h)
  · have e : (x : M) = y := h
    have hx₂ : (x : M) ∈ U₂ := by rw [e]; exact y.2
    exact ι₁_eq_ι₂_iff.2 ⟨e, hA ⟨x.2, hx₂⟩⟩
  · have e : (x : M) = y := h
    have hy₁ : (x : M) ∈ U₁ := by rw [e]; exact y.2
    have hyA : (y : M) ∈ A := by rw [← e]; exact hA ⟨hy₁, x.2⟩
    exact (ι₁_eq_ι₂_iff.2 ⟨e.symm, hyA⟩).symm
  · exact congrArg _ (Subtype.ext h)

/-- **`π` is injective iff `U₁ ∩ U₂ ⊆ A`** (`2-injective`). No topology. -/
theorem injective_proj_iff : Injective (proj h₁ h₂) ↔ U₁ ∩ U₂ ⊆ A := by
  constructor
  · rintro hinj x ⟨hx₁, hx₂⟩
    have e : Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩ =
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩ := hinj rfl
    exact (ι₁_eq_ι₂_iff.1 e).2
  · exact fun hsub _ _ h => eq_of_proj_eq h fun hx => hsub hx

/-- Over a point of `U₁ ∩ U₂ ∖ A` the two sheets do not meet. -/
theorem ι₁_ne_ι₂ {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) (hxA : x ∉ A) :
    Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩ ≠
      Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩ :=
  fun h => hxA (ι₁_eq_ι₂_iff.1 h).2

/-- The fibre of `π` over `x ∈ U₁ ∩ U₂` is `{ι₁ x, ι₂ x}` (two points iff `x ∉ A`). -/
theorem preimage_proj_singleton_of_mem_inter {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    proj h₁ h₂ ⁻¹' {x} =
      {Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩,
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  constructor
  · intro hz
    rcases Gluing.exists_ι z with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl (congrArg _ (Subtype.ext hz))
    · exact Or.inr (congrArg _ (Subtype.ext hz))
  · rintro (rfl | rfl) <;> rfl

/-- The fibre over `x ∈ U₁ ∩ U₂ ∖ A` has two points. -/
theorem encard_preimage_proj_singleton_of_notMem {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (hxA : x ∉ A) : (proj h₁ h₂ ⁻¹' {x}).encard = 2 := by
  rw [preimage_proj_singleton_of_mem_inter hx₁ hx₂, encard_pair (ι₁_ne_ι₂ hx₁ hx₂ hxA)]

/-- Over the rest of `U₁ ∪ U₂` the fibre is one point. -/
theorem preimage_proj_singleton_of_mem {x : M} (hx : x ∈ U₁ ∪ U₂) (hx' : x ∉ (U₁ ∩ U₂) \ A) :
    ∃ z, proj h₁ h₂ ⁻¹' {x} = {z} := by
  rw [← range_proj (h₁ := h₁) (h₂ := h₂)] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨z, Subsingleton.eq_singleton_of_mem (fun a ha b hb => ?_) rfl⟩
  have ha' : proj h₁ h₂ a = proj h₁ h₂ z := ha
  have hb' : proj h₁ h₂ b = proj h₁ h₂ z := hb
  refine eq_of_proj_eq (ha'.trans hb'.symm) fun hm => ?_
  rw [ha'] at hm ⊢
  by_contra hA
  exact hx' ⟨hm, hA⟩

/-- Off `U₁ ∪ U₂` the fibre is empty. -/
theorem preimage_proj_singleton_of_notMem_union {x : M} (hx : x ∉ U₁ ∪ U₂) :
    proj h₁ h₂ ⁻¹' {x} = ∅ := by
  rw [← range_proj (h₁ := h₁) (h₂ := h₂)] at hx
  exact eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz⟩

/-- The preimage of any `B ⊆ M` is the union of its two sheets. -/
theorem preimage_proj_eq_union (B : Set M) :
    proj h₁ h₂ ⁻¹' B =
      Gluing.ι₁ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' B) ∪
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' B) := by
  ext z
  constructor
  · intro hz
    rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x, hz, rfl⟩
    · exact Or.inr ⟨y, hz, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hx
    · exact hy

/-- **A set off `A` is contained twice** (`:852`): its two sheets are disjoint. -/
theorem disjoint_image_ι₁_image_ι₂ {B : Set M} (hB : Disjoint B A) :
    Disjoint (Gluing.ι₁ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' B))
      (Gluing.ι₂ (inclusion h₁) (inclusion h₂) '' (Subtype.val ⁻¹' B)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, -, he⟩
  exact hB.ne_of_mem hx (ι₁_eq_ι₂_iff.1 he.symm).2 rfl

section Topology

variable [TopologicalSpace M]

/-- When `U₁ ∩ U₂ ⊆ A`, `π` is an open embedding. -/
theorem isOpenEmbedding_proj (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hA : IsOpen A)
    (h : U₁ ∩ U₂ ⊆ A) : IsOpenEmbedding (proj h₁ h₂) :=
  (isLocalHomeomorph_proj hU₁ hU₂ hA).isOpenEmbedding_of_injective (injective_proj_iff.2 h)

/-- When `U₁ ∩ U₂ ⊆ A`, `E` is `U₁ ∪ U₂`, over `M`. -/
theorem exists_homeomorph (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hA : IsOpen A)
    (h : U₁ ∩ U₂ ⊆ A) :
    ∃ e : EtaleGluing h₁ h₂ ≃ₜ ↥(U₁ ∪ U₂), ∀ z, (e z : M) = proj h₁ h₂ z := by
  have he := isOpenEmbedding_proj (h₁ := h₁) (h₂ := h₂) hU₁ hU₂ hA h
  exact ⟨he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_proj), fun _ => rfl⟩

/-! ### Assertion 3: when the gluing is Hausdorff -/

/-- A point `x ∈ U₁ ∩ U₂` of `closure A ∖ A` gives the corresponding boundary pair `(x, x)`.
No separation axiom, no openness. -/
theorem isCorrespondingBoundaryPair_of_mem {x : U₁} {y : U₂} (hxy : (x : M) = y)
    (hx : (x : M) ∈ closure A \ A) :
    Gluing.IsCorrespondingBoundaryPair (inclusion h₁) (inclusion h₂) x y := by
  obtain ⟨hcl, hxA⟩ := hx
  refine Gluing.isCorrespondingBoundaryPair_of_mem_closure_graph ?_ ?_ ?_
  · rintro ⟨w, rfl⟩
    exact hxA w.2
  · rintro ⟨w, hw⟩
    apply hxA
    rw [hxy, ← hw]
    exact w.2
  · rw [← Gluing.forall_nhds_iff_mem_closure_graph]
    intro V hV V' hV'
    rw [nhds_subtype, mem_comap] at hV hV'
    obtain ⟨t, ht, htV⟩ := hV
    obtain ⟨t', ht', htV'⟩ := hV'
    rw [← hxy] at ht'
    obtain ⟨a, ⟨hat, hat'⟩, haA⟩ := mem_closure_iff_nhds.1 hcl _ (inter_mem ht ht')
    exact ⟨⟨a, haA⟩, htV hat, htV' hat'⟩

/-- **If `E` is Hausdorff, `A` is closed in `U₁ ∩ U₂`**, for any space `M`: the two points over
`x ∈ U₁ ∩ U₂ ∩ closure A ∖ A` are distinct and not separated. -/
theorem subset_of_t2Space (hA : IsOpen A) [T2Space (EtaleGluing h₁ h₂)] :
    U₁ ∩ U₂ ∩ closure A ⊆ A := by
  rintro x ⟨⟨hx₁, hx₂⟩, hxc⟩
  by_contra hxA
  obtain ⟨hne, hns⟩ := (isCorrespondingBoundaryPair_of_mem (h₁ := h₁) (h₂ := h₂)
    (x := ⟨x, hx₁⟩) (y := ⟨x, hx₂⟩) rfl ⟨hxc, hxA⟩).not_separated
    (isOpenEmbedding_inclusion h₁ hA) (isOpenEmbedding_inclusion h₂ hA)
  exact hns (disjoint_nhds_nhds.2 hne)

/-- **The corresponding boundary pairs** of two subsets of a Hausdorff space glued along an open
`A`: the pairs `(x, x)` with `x ∈ U₁ ∩ U₂ ∩ closure A ∖ A`. -/
theorem isCorrespondingBoundaryPair_iff [T2Space M] (hA : IsOpen A) {x : U₁} {y : U₂} :
    Gluing.IsCorrespondingBoundaryPair (inclusion h₁) (inclusion h₂) x y ↔
      (x : M) = y ∧ (x : M) ∈ closure A \ A := by
  have hj₁ := isOpenEmbedding_inclusion h₁ hA
  constructor
  · rintro ⟨hx, -, hc⟩
    rw [hj₁.isOpen_range.frontier_eq, range_inclusion] at hx
    rw [Gluing.forall_nhds_iff_mem_closure_graph] at hc
    have hmap : MapsTo (fun p : U₁ × U₂ => ((p.1 : M), (p.2 : M)))
        (Gluing.graph (inclusion h₁) (inclusion h₂)) {q : M × M | q.1 = q.2 ∧ q.1 ∈ closure A} := by
      rintro _ ⟨w, rfl⟩
      exact ⟨rfl, subset_closure w.2⟩
    have hcl : IsClosed {q : M × M | q.1 = q.2 ∧ q.1 ∈ closure A} :=
      (isClosed_eq continuous_fst continuous_snd).inter (isClosed_closure.preimage continuous_fst)
    have hxy := hcl.closure_subset (map_mem_closure (by fun_prop) hc hmap)
    exact ⟨hxy.1, hxy.2, hx.2⟩
  · exact fun ⟨hxy, hx⟩ => isCorrespondingBoundaryPair_of_mem hxy hx

/-- **`E` is Hausdorff iff `U₁ ∩ U₂ ∩ closure A ⊆ A`** (`3-hausdorff`). -/
theorem t2Space_iff [T2Space M] (hA : IsOpen A) :
    T2Space (EtaleGluing h₁ h₂) ↔ U₁ ∩ U₂ ∩ closure A ⊆ A := by
  rw [Gluing.t2Space_iff_forall_not_isCorrespondingBoundaryPair
    (isOpenEmbedding_inclusion h₁ hA) (isOpenEmbedding_inclusion h₂ hA)]
  simp only [isCorrespondingBoundaryPair_iff hA]
  constructor
  · rintro h x ⟨⟨hx₁, hx₂⟩, hxc⟩
    by_contra hxA
    exact h ⟨x, hx₁⟩ ⟨x, hx₂⟩ ⟨rfl, hxc, hxA⟩
  · rintro h x y ⟨hxy, hxc, hxA⟩
    have hy : (x : M) ∈ U₂ := by rw [hxy]; exact y.2
    exact hxA (h ⟨⟨x.2, hy⟩, hxc⟩)

/-- `E` is Hausdorff iff `A` is closed in `U₁ ∩ U₂`. -/
theorem t2Space_iff_isClosed [T2Space M] (hA : IsOpen A) :
    T2Space (EtaleGluing h₁ h₂) ↔ IsClosed ((Subtype.val : ↥(U₁ ∩ U₂) → M) ⁻¹' A) := by
  rw [t2Space_iff hA, isClosed_preimage_val, inter_eq_right.2 (subset_inter h₁ h₂)]

/-- **For a connected `A`, `E` is Hausdorff iff `A` is a connected component of `U₁ ∩ U₂`.**
No local connectedness. -/
theorem t2Space_iff_eq_connectedComponentIn [T2Space M] (hA : IsOpen A) (hc : IsPreconnected A)
    {x : M} (hx : x ∈ A) :
    T2Space (EtaleGluing h₁ h₂) ↔ connectedComponentIn (U₁ ∩ U₂) x = A := by
  have hxF : x ∈ U₁ ∩ U₂ := ⟨h₁ hx, h₂ hx⟩
  rw [t2Space_iff hA]
  constructor
  · intro h
    refine Subset.antisymm ?_ (hc.subset_connectedComponentIn hx (subset_inter h₁ h₂))
    exact isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hA
      ⟨x, mem_connectedComponentIn hxF, hx⟩
      fun y ⟨hyc, hyK⟩ => h ⟨connectedComponentIn_subset _ _ hyK, hyc⟩
  · rintro he y ⟨hyF, hyc⟩
    have hp : IsPreconnected (insert y A) :=
      hc.subset_closure (subset_insert _ _) (insert_subset hyc subset_closure)
    have hsub := hp.subset_connectedComponentIn (mem_insert_of_mem _ hx)
      (insert_subset hyF (subset_inter h₁ h₂))
    rw [he] at hsub
    exact hsub (mem_insert _ _)

/-- **ERS's MCGHD** (`:850`): in a Hausdorff, locally connected `M`, gluing two open sets along a
connected component of their intersection gives a Hausdorff space. -/
theorem t2Space_connectedComponentIn [T2Space M] [LocallyConnectedSpace M] (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂) {x : M} (hx : x ∈ U₁ ∩ U₂) {h₁ : connectedComponentIn (U₁ ∩ U₂) x ⊆ U₁}
    {h₂ : connectedComponentIn (U₁ ∩ U₂) x ⊆ U₂} : T2Space (EtaleGluing h₁ h₂) := by
  exact (t2Space_iff_eq_connectedComponentIn (hU₁.inter hU₂).connectedComponentIn
    isPreconnected_connectedComponentIn (mem_connectedComponentIn hx)).2 rfl

/-- **A Hausdorff gluing along a non-empty `A` over a connected `U₁ ∩ U₂` is `U₁ ∪ U₂`**: then
`A = U₁ ∩ U₂`, so `π` is injective. Any space `M`. -/
theorem eq_inter_of_t2Space (hA : IsOpen A) [T2Space (EtaleGluing h₁ h₂)] (hne : A.Nonempty)
    (hc : IsPreconnected (U₁ ∩ U₂)) : A = U₁ ∩ U₂ := by
  refine Subset.antisymm (subset_inter h₁ h₂) ?_
  obtain ⟨a, ha⟩ := hne
  exact hc.subset_of_closure_inter_subset hA ⟨a, ⟨h₁ ha, h₂ ha⟩, ha⟩
    fun y ⟨hyc, hyF⟩ => subset_of_t2Space hA ⟨hyF, hyc⟩

end Topology

/-! ### Assertion 4: the glued function and its descent -/

section Descent

variable {β : Type v} {u₁ u₂ : M → β} {hu : EqOn u₁ u₂ A}

@[simp] theorem glue_ι₁ (x : U₁) :
    glue h₁ h₂ u₁ u₂ hu (Gluing.ι₁ (inclusion h₁) (inclusion h₂) x) = u₁ x := rfl

@[simp] theorem glue_ι₂ (y : U₂) :
    glue h₁ h₂ u₁ u₂ hu (Gluing.ι₂ (inclusion h₁) (inclusion h₂) y) = u₂ y := rfl

/-- `ũ ∘ ι₁ = u₁ ∘ coe`. -/
theorem glue_comp_ι₁ :
    glue h₁ h₂ u₁ u₂ hu ∘ Gluing.ι₁ (inclusion h₁) (inclusion h₂) = u₁ ∘ Subtype.val := rfl

/-- `ũ ∘ ι₂ = u₂ ∘ coe`. -/
theorem glue_comp_ι₂ :
    glue h₁ h₂ u₁ u₂ hu ∘ Gluing.ι₂ (inclusion h₁) (inclusion h₂) = u₂ ∘ Subtype.val := rfl

/-- The glued function is continuous when `u₁` is on `U₁` and `u₂` on `U₂`. -/
theorem continuous_glue [TopologicalSpace M] [TopologicalSpace β] (hc₁ : ContinuousOn u₁ U₁)
    (hc₂ : ContinuousOn u₂ U₂) : Continuous (glue h₁ h₂ u₁ u₂ hu) := by
  exact Gluing.continuous_desc (continuousOn_iff_continuous_restrict.1 hc₁)
    (continuousOn_iff_continuous_restrict.1 hc₂)

open Classical in
/-- The factor: `u₁` on `U₁`, `u₂` off it. It is `Causal.glueSolutions ⟨U₁, hU₁⟩ u₁ u₂`
(`Causal.Ers482Solution`) by `rfl`, checked in the campaign's probe. -/
theorem glue_eq_ite_comp_proj (h : EqOn u₁ u₂ (U₁ ∩ U₂)) :
    glue h₁ h₂ u₁ u₂ hu = (fun x => if x ∈ U₁ then u₁ x else u₂ x) ∘ proj h₁ h₂ := by
  funext z
  rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact (if_pos x.2).symm
  · show u₂ y = if (y : M) ∈ U₁ then u₁ y else u₂ y
    split_ifs with hy
    · exact (h ⟨hy, y.2⟩).symm
    · rfl

/-- **The glued function factors through `π` iff `u₁ = u₂` on all of `U₁ ∩ U₂`**
(`4-descent`). -/
theorem exists_glue_eq_comp_proj_iff :
    (∃ v : M → β, glue h₁ h₂ u₁ u₂ hu = v ∘ proj h₁ h₂) ↔ EqOn u₁ u₂ (U₁ ∩ U₂) := by
  refine ⟨fun ⟨v, hv⟩ x ⟨hx₁, hx₂⟩ => ?_, fun h => ⟨_, glue_eq_ite_comp_proj h⟩⟩
  have e₁ := congrFun hv (Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩)
  have e₂ := congrFun hv (Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩)
  exact e₁.trans e₂.symm

/-- **Thm 3.45's conclusion read on the gluing**: a point `x ∈ U₁ ∩ U₂` with `u₁ x ≠ u₂ x` is not
in `A`, is covered twice, so `π` is not injective, and the glued function lives on no subset of
`M`. -/
theorem not_injective_and_not_descends {x : M} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (hne : u₁ x ≠ u₂ x) :
    x ∉ A ∧
      Gluing.ι₁ (inclusion h₁) (inclusion h₂) ⟨x, hx₁⟩ ≠
        Gluing.ι₂ (inclusion h₁) (inclusion h₂) ⟨x, hx₂⟩ ∧
      ¬ Injective (proj h₁ h₂) ∧ ¬ ∃ v : M → β, glue h₁ h₂ u₁ u₂ hu = v ∘ proj h₁ h₂ := by
  have hxA : x ∉ A := fun hxA => hne (hu hxA)
  exact ⟨hxA, ι₁_ne_ι₂ hx₁ hx₂ hxA, fun hinj => hxA (injective_proj_iff.1 hinj ⟨hx₁, hx₂⟩),
    fun hv => hne (exists_glue_eq_comp_proj_iff.1 hv ⟨hx₁, hx₂⟩)⟩

/-- **Cor 4.68's shape on the gluing** (`erscor:CorDisCon`, `:921`): if the gluing along a
non-empty open `A` is Hausdorff and `u₁ x ≠ u₂ x` at some `x ∈ U₁ ∩ U₂`, then `U₁ ∩ U₂` is not
connected. Any space `M`; that the MCGHD gives a Hausdorff gluing is the causal half. -/
theorem not_isPreconnected_inter [TopologicalSpace M] (hA : IsOpen A)
    [T2Space (EtaleGluing h₁ h₂)] (hne : A.Nonempty) (hagree : EqOn u₁ u₂ A) {x : M}
    (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) (hux : u₁ x ≠ u₂ x) : ¬ IsPreconnected (U₁ ∩ U₂) := fun hc => by
  have hx : x ∈ A := (eq_inter_of_t2Space hA hne hc).symm ▸ ⟨hx₁, hx₂⟩
  exact hux (hagree hx)

end Descent

/-! ### Assertion 5: witnesses on `ℝ` -/

/-- `(0, ∞) ⊆ ℝ ∖ {0}`. -/
theorem Ioi_subset_compl_zero : Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun _ ht => ne_of_gt ht

/-- Two copies of `ℝ ∖ {0}` glued along `(0, ∞)`: the negative half-line is doubled. -/
abbrev Punctured : Type := EtaleGluing Ioi_subset_compl_zero Ioi_subset_compl_zero

/-- `0` and `1_{(-∞, 0)}` agree on `(0, ∞)`. -/
theorem eqOn_zero_indicator : EqOn (0 : ℝ → ℝ) ((Iio (0 : ℝ)).indicator 1) (Ioi 0) := by
  intro t ht
  have ht' : t ∉ Iio 0 := fun h => lt_asymm (mem_Ioi.1 ht) (mem_Iio.1 h)
  rw [Pi.zero_apply, indicator_of_notMem ht']

/-- **First witness**: `U₁ = U₂ = ℝ ∖ {0}`, `A = (0, ∞)`, a connected component of
`U₁ ∩ U₂`. The gluing is Hausdorff and étale, `π` is not injective, and the glued function of
`0` and `1_{(-∞, 0)}` does not descend; that of `0` and `0` does, though `π` is not injective. -/
theorem punctured_witness :
    connectedComponentIn (({0}ᶜ : Set ℝ) ∩ {0}ᶜ) 1 = Ioi 0 ∧ T2Space Punctured ∧
      IsLocalHomeomorph (proj Ioi_subset_compl_zero Ioi_subset_compl_zero) ∧
      ¬ Injective (proj Ioi_subset_compl_zero Ioi_subset_compl_zero) ∧
      ¬ (∃ v : ℝ → ℝ, glue Ioi_subset_compl_zero Ioi_subset_compl_zero 0 ((Iio (0 : ℝ)).indicator 1)
          eqOn_zero_indicator = v ∘ proj Ioi_subset_compl_zero Ioi_subset_compl_zero) ∧
      ∃ v : ℝ → ℝ, glue Ioi_subset_compl_zero Ioi_subset_compl_zero 0 0 (eqOn_refl _ _) =
        v ∘ proj Ioi_subset_compl_zero Ioi_subset_compl_zero := by
  have hT : T2Space Punctured := by
    rw [t2Space_iff isOpen_Ioi, closure_Ioi]
    rintro t ⟨⟨ht, -⟩, ht'⟩
    exact lt_of_le_of_ne ht' (Ne.symm ht)
  have hm : (-1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by norm_num
  have hne : (0 : ℝ → ℝ) (-1) ≠ (Iio (0 : ℝ)).indicator 1 (-1) := by
    rw [indicator_of_mem (show (-1 : ℝ) ∈ Iio 0 by norm_num)]
    norm_num
  obtain ⟨-, -, hinj, hdesc⟩ := not_injective_and_not_descends (hu := eqOn_zero_indicator) hm hm hne
  exact ⟨(t2Space_iff_eq_connectedComponentIn isOpen_Ioi isPreconnected_Ioi
      (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos)).1 hT, hT,
    isLocalHomeomorph_proj isOpen_compl_singleton isOpen_compl_singleton isOpen_Ioi, hinj, hdesc,
    exists_glue_eq_comp_proj_iff.2 (eqOn_refl _ _)⟩

/-- `not_isPreconnected_inter` at the first witness: `ℝ ∖ {0}` is not connected, read off the
Hausdorff gluing and the point `-1` where `0 ≠ 1_{(-∞, 0)}`. -/
theorem punctured_not_isPreconnected : ¬ IsPreconnected (({0}ᶜ : Set ℝ) ∩ {0}ᶜ) := by
  obtain ⟨-, hT, -⟩ := punctured_witness
  have hm : (-1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by norm_num
  have hne : (0 : ℝ → ℝ) (-1) ≠ (Iio (0 : ℝ)).indicator 1 (-1) := by
    rw [indicator_of_mem (show (-1 : ℝ) ∈ Iio 0 by norm_num)]
    norm_num
  exact not_isPreconnected_inter (h₁ := Ioi_subset_compl_zero) (h₂ := Ioi_subset_compl_zero)
    isOpen_Ioi ⟨1, mem_Ioi.2 one_pos⟩ eqOn_zero_indicator hm hm hne

/-- Two copies of `ℝ` glued along `(0, ∞)`. -/
abbrev Branching : Type := EtaleGluing (subset_univ (Ioi (0 : ℝ))) (subset_univ (Ioi (0 : ℝ)))

/-- **Second witness**: `U₁ = U₂ = ℝ`, `A = (0, ∞)`. The gluing is étale but not Hausdorff:
`0 ∈ closure A ∖ A`, and `(0, 0)` is a corresponding boundary pair (the mechanism of
`Causal.Gluing.lineTwoOrigins_not_t2Space`); `¬ T2Space` through the hypothesis-free
`subset_of_t2Space`. -/
theorem branching_witness :
    IsLocalHomeomorph (proj (subset_univ (Ioi (0 : ℝ))) (subset_univ (Ioi (0 : ℝ)))) ∧
      Gluing.IsCorrespondingBoundaryPair (inclusion (subset_univ (Ioi (0 : ℝ))))
        (inclusion (subset_univ (Ioi (0 : ℝ)))) ⟨0, trivial⟩ ⟨0, trivial⟩ ∧
      ¬ T2Space Branching := by
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) \ Ioi 0 := by
    rw [closure_Ioi]
    exact ⟨mem_Ici.2 le_rfl, fun h => lt_irrefl (0 : ℝ) h⟩
  refine ⟨isLocalHomeomorph_proj isOpen_univ isOpen_univ isOpen_Ioi,
    (isCorrespondingBoundaryPair_iff isOpen_Ioi).2 ⟨rfl, h0⟩, fun hT => ?_⟩
  exact h0.2 (subset_of_t2Space (h₁ := subset_univ (Ioi (0 : ℝ)))
    (h₂ := subset_univ (Ioi (0 : ℝ))) isOpen_Ioi ⟨⟨trivial, trivial⟩, h0.1⟩)

end EtaleGluing

end Causal
