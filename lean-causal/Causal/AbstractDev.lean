import Mathlib.Topology.Sets.Opens
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Ordinal.Family

/-!
# Maximal developments by Zorn's lemma, abstractly (Chruściel Thm 2.2)

Programme target `T-abs-maximal-zorn` (`programme/roadmap.toml`; layer 1); this module was split
out of `Causal.MaximalZorn` by `T-tac-curves-fact-rule`, under the same full names and with the
same statements. It imports Mathlib only: no `Causal` module, no model, no metric. A module that
needs the abstract Zorn argument alone (`Causal.CurvesExtendSecondCountable`) imports it here,
without `Causal.MaximalZorn`'s developments on a fixed background, whose `Causal.ErsMughd` imports
`Causal.Ladder.Rules`. Source: Chruściel, *On maximal globally hyperbolic vacuum space-times*,
arXiv 1112.5779, §2, Theorem 2.2 and its proof (archived: `references/sbierski/pdf/
chrusciel2013maximal.pdf`, text `references/sbierski/text/chrusciel2013maximal.txt:242–365`).
Chruściel is not ledgered. **No label is marked.** The ERS remark this serves,
`ersrem:note_two_ghds_constructed` (`ghd_02_19.tex:731`), is cited, unmarked, by
`Causal.MaximalZorn`, whose `exists_isMaximalDevelopment` applies `exists_isMaximal_of_chainsInherit`.

> Theorem 2.2 Let S be a n-dimensional manifold and let (M, g, i) be a Lorentzian
> (n + 1)-dimensional W-manifold (M, g) with a W–compatible embedding i : S → M. Suppose that the
> property W is chain-inheriting, and that the only isometry of a W-manifold (M, g) which is the
> identity on a W-compatible hypersurface is the identity map. (2.1) Then there exists a
> Lorentzian W-manifold (M̃, g̃, ı̃) with a W-compatible embedding ı̃ : S → M̃ and a C¹ isometric
> embedding Φ : M → M̃ satisfying ı̃ = Φ ∘ i such that M̃ is inextendible in the class of
> Lorentzian W-manifolds with a W-compatible embedding of S. (text l. 262–275; `M̃` is the
> extraction's `Me`)

> The property W will be said to be chain-inheriting if both the manifold M of (2.2) and the
> associated embedding ı̄ of S have the property W whenever all the manifolds M̃ in the union there
> and the embeddings ı̃ do. (l. 242–246) — where for p ∈ M̃ and q ∈ M̃₁ we set p ∼ q iff q = Φ(p),
> where Φ : M̃ → M̃₁ is the isometric C¹ embedding such that Φ ∘ ı̃ = ı̃₁. (l. 355–356)

> The C¹-differentiability threshold for S and M cannot be weakened in the proof below, since we
> are using the Whitney embedding theorem to turn the collection of manifolds into a set.
> (Remark 2.3.1, l. 277–278)

## What is proved

* **Abstract developments** (`Causal.AbstractDev`): a type `D` of developments, carriers
  `carrier : D → Type u`, morphisms `mor X Y f` composing (`MorphismsCompose`); the extension
  preorder `Extends`; Chruściel's (2.1) `RigidEndomorphisms`; `UniqueMorphisms`; the size bound
  `SizeBound.{v}`; chain inheritance `ChainsInherit.{v}` (every non-empty coherent chain,
  `IsCoherentChain`, of at most `v`-many developments has an upper bound, `IsCocone`).
* **`exists_isMaximal`**: size bound + chain inheritance ⇒ every development maps into a maximal
  one (every extension of it maps back), **without rigidity**: Zorn on *towers* (coherent chains
  with their morphisms, `Tower`, `IsTower`), not on developments. **`chrusciel_theorem_2_2`**: with
  (2.1), the maximal one is inextensible (every morphism out is an isomorphism,
  `IsMaximal.isInextensible`, Chruściel's antisymmetry argument; bijective,
  `IsInextensible.bijective`). Chruściel's own route under unique morphisms:
  `exists_upperBound_of_uniqueMorphisms` ((2.2)), `exists_isMaximal_of_uniqueMorphisms`.
  Zorn with chains split by cofinality, no coherence: `exists_isMaximal_of_sequences`. The size
  bound is free in the universe of `D`: `exists_isMaximal_of_chainsInherit`.
* **Each hypothesis is needed**: (2.1) does not make morphisms unique (`twoMor_rigid_not_unique`);
  without the size bound (the ordinals of a universe, `ordinalMor_separates`,
  `not_sizeBound_ordinalMor`), without chain inheritance (`natMor_separates`) or without rigidity
  for inextensibility (`allMor_separates`) the conclusion fails.

Users: `Causal.MaximalZorn` (the developments of `Causal.ErsMughd` as such a class, ERS Remark
3.56) and `Causal.CurvesExtendSecondCountable` (Zorn on towers of tail-free causal curves).

## Hypothesis checklist

| Chruściel Thm 2.2 | here |
|---|---|
| W-manifolds with a W-compatible embedding of S, isometric C¹ embeddings Φ, Φ ∘ ı = ı' | ✓ abstract: `D`, `carrier`, `mor` with `MorphismsCompose` |
| chain-inheriting: the union (2.2) of a chain is a W-manifold | ✓ `ChainsInherit.{v}`; ⚠ read: on *coherent* chains (their embeddings chosen), what (2.2)'s "the isometric C¹ embedding Φ" presupposes; non-empty chains only |
| rigidity (2.1) | ⚠ weakened: not used for existence (`exists_isMaximal`); used, and needed (`allMor_separates`), for inextensibility |
| the collection is a set (C¹, Whitney; Remark 2.3.1) | ✓ `SizeBound.{v}`: a `v`-small set of representatives up to isomorphism; needed (`ordinalMor_separates`); free for `v` the universe of `D` (`sizeBound_self`) |
| M̃ inextendible in the class, Φ : M → M̃ | ✓ `IsInextensible` (every morphism out an isomorphism) and the morphism `X → Z` |

## SCOPE (disclosed)

* **Rigidity is not needed for existence.** Chruściel uses (2.1) for the antisymmetry of `≺`.
  Zorn on towers needs no antisymmetry: a maximal tower's upper bound `Z` is maximal, for an
  extension `Y` of `Z` outside the tower would extend it. (2.1) is what makes "maximal" mean
  "inextendible". In (2.2) "the isometric C¹ embedding Φ" is unique by more than (2.1)
  (`twoMor_rigid_not_unique`); in Chruściel's classes it presumably follows from the local
  rigidity of isometries (the shape of `Causal.IsRigid`; not checked here). Under
  `UniqueMorphisms` his proof is `exists_isMaximal_of_uniqueMorphisms`.
* **The size bound is a universe.** In type theory "the collection is a set" becomes: the chains
  `ChainsInherit.{v}` bounds have at most `v` members, and `SizeBound.{v}` gives `v`-small
  representatives (`Causal.CBG.SmallDev.exists_iso` is the CBG instance, `v = u`).
* **Beside the Zorn-free CBG** (`Causal.CBG.Maximal.cbg`, not imported: `Causal.CBG.Geometry`
  imports `Causal.SingularFlat`). `CBG.Dev 𝔊 s₀` with `Dev.IsMorphism` has this shape, rigidity A1
  makes morphisms unique, `Dev.IsETTMaximal` is `IsInextensible` read by bijectivity. `cbg` is
  stronger (a universal, hence unique, development) and Zorn-free, through the Hausdorff gluing of
  every pair (Sbierski's corresponding points); Zorn needs only the union of a chain and gives no
  uniqueness, which is all a subluminal equation allows (ERS Thm 3.45).
* The ordinals (`Mathlib.SetTheory.Ordinal.Family`) are imported for `ordinalMor_separates` only;
  `Mathlib.Topology.Sets.Opens` for the namespaces of the `open` line the moved text was elaborated
  under in `Causal.MaximalZorn`, kept as it was.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

namespace AbstractDev

/-- **A coherent chain of developments** indexed by `ι`, totally preordered by `r` (Chruściel's
chain `A`, `1112.5779` p. 5, with its embeddings chosen): a development `X i` for each index and a
morphism `φ h : X i → X j` for each `h : r i j`, the identity on `r i i`, composing along
`r i j`, `r j k`. -/
structure IsCoherentChain {D : Type*} {carrier : D → Type*}
    (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) {ι : Type*} (r : ι → ι → Prop) (X : ι → D)
    (φ : ∀ ⦃i j : ι⦄, r i j → carrier (X i) → carrier (X j)) : Prop where
  refl : ∀ i, r i i
  trans : ∀ ⦃i j k⦄, r i j → r j k → r i k
  total : ∀ i j, r i j ∨ r j i
  isMor : ∀ ⦃i j⦄ (h : r i j), mor (X i) (X j) (φ h)
  map_refl : ∀ i (h : r i i), φ h = id
  map_comp : ∀ ⦃i j k⦄ (hij : r i j) (hjk : r j k) (hik : r i k), φ hjk ∘ φ hij = φ hik

/-- **An upper bound of a coherent chain** (Chruściel's `M` of (2.2) with the maps
`p ↦ [p]∼`): a development `Z` and morphisms `g i : X i → Z` commuting with the chain. -/
def IsCocone {D : Type*} {carrier : D → Type*}
    (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) {ι : Type*} (r : ι → ι → Prop) (X : ι → D)
    (φ : ∀ ⦃i j : ι⦄, r i j → carrier (X i) → carrier (X j)) (Z : D)
    (g : ∀ i, carrier (X i) → carrier Z) : Prop :=
  (∀ i, mor (X i) Z (g i)) ∧ ∀ ⦃i j⦄ (h : r i j), g j ∘ φ h = g i

-- `v` first: `ChainsInherit.{v}` and `SizeBound.{v}` name the bound on the size of chains.
universe v u w

variable {D : Type w} {carrier : D → Type u}

/-- **Chain inheritance** (Chruściel 1112.5779, p. 4: "the property W will be said to be
chain-inheriting if both the manifold M of (2.2) and the associated embedding ı̄ of S have the
property W"): every non-empty coherent chain of at most `v`-many developments has an upper bound. -/
def ChainsInherit (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) : Prop :=
  ∀ (ι : Type w) [Small.{v} ι] [Nonempty ι] (r : ι → ι → Prop) (X : ι → D)
    (φ : ∀ ⦃i j : ι⦄, r i j → carrier (X i) → carrier (X j)), IsCoherentChain mor r X φ →
    ∃ (Z : D) (g : ∀ i, carrier (X i) → carrier Z), IsCocone mor r X φ Z g

/-- **The size bound** (Chruściel 1112.5779 p. 5, "every manifold has a representative which is
an element of A∞"; `Causal.CBG.SmallDev.exists_iso`): a `v`-small set `R` of developments such that
every development is isomorphic to a member of `R`. -/
def SizeBound (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) : Prop :=
  ∃ R : Set D, Small.{v} R ∧ ∀ X : D, ∃ Y ∈ R, ∃ (f : carrier X → carrier Y)
    (g : carrier Y → carrier X), mor X Y f ∧ mor Y X g ∧ g ∘ f = id ∧ f ∘ g = id

/-- **Morphisms of developments compose** (Chruściel: isometric `C¹` embeddings `Φ` with
`Φ ∘ ı = ı'`; `Causal.CBG.Dev.IsMorphism`): the identity is a morphism, and so is a composite. -/
structure MorphismsCompose (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) : Prop where
  isMor_id : ∀ X, mor X X id
  isMor_comp : ∀ ⦃X Y Z : D⦄ ⦃f : carrier X → carrier Y⦄ ⦃g : carrier Y → carrier Z⦄,
    mor X Y f → mor Y Z g → mor X Z (g ∘ f)

variable (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop)

/-- **The extension preorder** (Chruściel's `≺`, p. 5): `Y` extends `X` when a morphism
`X → Y` exists. -/
def Extends (X Y : D) : Prop := ∃ f : carrier X → carrier Y, mor X Y f

/-- **An isomorphism of developments**: a morphism with a two-sided inverse morphism. -/
def IsIso {X Y : D} (f : carrier X → carrier Y) : Prop :=
  mor X Y f ∧ ∃ g : carrier Y → carrier X, mor Y X g ∧ g ∘ f = id ∧ f ∘ g = id

/-- **Rigidity, Chruściel's (2.1)**: "the only isometry of a W-manifold (M, g) which is the
identity on a W-compatible hypersurface is the identity map" — every endomorphism of a
development is the identity. -/
def RigidEndomorphisms : Prop := ∀ (X : D) (f : carrier X → carrier X), mor X X f → f = id

/-- **Unique extensions**: between two developments there is at most one morphism (the form
Chruściel's (2.2) uses, "the isometric C¹ embedding Φ"; `Causal.CBG`'s rigidity A1). -/
def UniqueMorphisms : Prop :=
  ∀ (X Y : D) (f g : carrier X → carrier Y), mor X Y f → mor X Y g → f = g

/-- **Maximal for the extension preorder**: every development extending `Z` maps back into `Z`. -/
def IsMaximal (Z : D) : Prop := ∀ (Y : D) (f : carrier Z → carrier Y), mor Z Y f → Extends mor Y Z

/-- **Inextensible in the class** (Chruściel's conclusion, "M̃ is inextendible in the class";
`Causal.CBG.Dev.IsETTMaximal` up to bijectivity): every morphism out of `Z` is an isomorphism. -/
def IsInextensible (Z : D) : Prop :=
  ∀ (Y : D) (f : carrier Z → carrier Y), mor Z Y f → IsIso mor f

variable {mor}

/-! ### Towers: Zorn on coherent chains -/

/-- **A tower's data**: a set of developments `S`, a relation `r` (a total preorder on `S`) and
the chosen morphisms `F X Y f` ("`f` is the morphism `X → Y` of the tower"). The proof device of
`exists_isMaximal`: Zorn is applied to towers, not to developments, so that the chain it yields
comes with coherent morphisms (no rigidity needed). -/
structure Tower (carrier : D → Type u) where
  /-- The developments of the tower. -/
  S : Set D
  /-- The order of the tower. -/
  r : D → D → Prop
  /-- The chosen morphisms. -/
  F : ∀ X Y : D, (carrier X → carrier Y) → Prop

/-- The order of towers: inclusion of the three components. -/
def Tower.LE (t t' : Tower carrier) : Prop :=
  t.S ⊆ t'.S ∧ (∀ X Y, t.r X Y → t'.r X Y) ∧ ∀ X Y f, t.F X Y f → t'.F X Y f

theorem Tower.LE.refl (t : Tower carrier) : t.LE t :=
  ⟨subset_rfl, fun _ _ h => h, fun _ _ _ h => h⟩

theorem Tower.LE.trans {t t' t'' : Tower carrier} (h : t.LE t') (h' : t'.LE t'') : t.LE t'' :=
  ⟨h.1.trans h'.1, fun X Y hr => h'.2.1 X Y (h.2.1 X Y hr),
    fun X Y f hF => h'.2.2 X Y f (h.2.2 X Y f hF)⟩

/-- **A tower inside `R`**: `r` a total preorder on `S ⊆ R`, and for each `r X Y` exactly one
chosen morphism, the identity on `X X`, composing. -/
structure IsTower (mor : ∀ X Y : D, (carrier X → carrier Y) → Prop) (R : Set D)
    (t : Tower carrier) : Prop where
  subset : t.S ⊆ R
  rel_mem : ∀ ⦃X Y⦄, t.r X Y → X ∈ t.S ∧ Y ∈ t.S
  refl : ∀ X ∈ t.S, t.r X X
  trans : ∀ ⦃X Y Z⦄, t.r X Y → t.r Y Z → t.r X Z
  total : ∀ X ∈ t.S, ∀ Y ∈ t.S, t.r X Y ∨ t.r Y X
  map_rel : ∀ ⦃X Y f⦄, t.F X Y f → t.r X Y
  map_mor : ∀ ⦃X Y f⦄, t.F X Y f → mor X Y f
  map_exists : ∀ ⦃X Y⦄, t.r X Y → ∃ f, t.F X Y f
  map_unique : ∀ ⦃X Y f g⦄, t.F X Y f → t.F X Y g → f = g
  map_id : ∀ X ∈ t.S, t.F X X id
  map_comp : ∀ ⦃X Y Z f g⦄, t.F X Y f → t.F Y Z g → t.F X Z (g ∘ f)

/-- The union of a set of towers. -/
def Tower.sUnion (c : Set (Tower carrier)) : Tower carrier where
  S := ⋃ t ∈ c, t.S
  r X Y := ∃ t ∈ c, t.r X Y
  F X Y f := ∃ t ∈ c, t.F X Y f

theorem Tower.le_sUnion {c : Set (Tower carrier)} {t : Tower carrier} (ht : t ∈ c) :
    t.LE (Tower.sUnion c) :=
  ⟨fun _ hX => mem_biUnion ht hX, fun _ _ h => ⟨t, ht, h⟩, fun _ _ _ h => ⟨t, ht, h⟩⟩

/-- The one-development tower. -/
def Tower.singleton (X : D) : Tower carrier where
  S := {X}
  r A B := A = X ∧ B = X
  F A B f := A = X ∧ B = X ∧ HEq f (@id (carrier A))

theorem isTower_singleton {R : Set D} (hcomp : MorphismsCompose mor) {X : D} (hX : X ∈ R) :
    IsTower mor R (Tower.singleton X) where
  subset A hA := by rw [mem_singleton_iff.1 hA]; exact hX
  rel_mem A B h := ⟨h.1, h.2⟩
  refl A hA := ⟨hA, hA⟩
  trans A B C h h' := ⟨h.1, h'.2⟩
  total A hA B hB := Or.inl ⟨hA, hB⟩
  map_rel A B f h := ⟨h.1, h.2.1⟩
  map_mor A B f h := by
    obtain ⟨hA, hB, hf⟩ := h
    subst hA hB
    obtain rfl := eq_of_heq hf
    exact hcomp.isMor_id _
  map_exists A B h := by
    obtain ⟨hA, hB⟩ := h
    subst hA hB
    exact ⟨id, rfl, rfl, HEq.rfl⟩
  map_unique A B f f' h h' := eq_of_heq (h.2.2.trans h'.2.2.symm)
  map_id A hA := ⟨hA, hA, HEq.rfl⟩
  map_comp A B C f f' h h' := by
    obtain ⟨hA, hB, hf⟩ := h
    obtain ⟨-, hC, hf'⟩ := h'
    subst hA hB hC
    obtain rfl := eq_of_heq hf
    obtain rfl := eq_of_heq hf'
    exact ⟨rfl, rfl, HEq.rfl⟩

/-- **A directed union of towers is a tower** (Chruściel's (2.2) at the level of towers: two
data of the union lie in one member). -/
theorem isTower_sUnion {R : Set D} {c : Set (Tower carrier)} (hc : ∀ t ∈ c, IsTower mor R t)
    (hdir : ∀ t ∈ c, ∀ t' ∈ c, ∃ t'' ∈ c, t.LE t'' ∧ t'.LE t'') :
    IsTower mor R (Tower.sUnion c) := by
  have hS : ∀ {X : D}, X ∈ (Tower.sUnion c).S ↔ ∃ t ∈ c, X ∈ t.S := fun {X} => by
    simp only [Tower.sUnion, mem_iUnion₂, exists_prop]
  refine
    { subset := ?_, rel_mem := ?_, refl := ?_, trans := ?_, total := ?_, map_rel := ?_,
      map_mor := ?_, map_exists := ?_, map_unique := ?_, map_id := ?_, map_comp := ?_ }
  · intro X hX
    obtain ⟨t, ht, hX⟩ := hS.1 hX
    exact (hc t ht).subset hX
  · rintro X Y ⟨t, ht, h⟩
    exact ⟨hS.2 ⟨t, ht, ((hc t ht).rel_mem h).1⟩, hS.2 ⟨t, ht, ((hc t ht).rel_mem h).2⟩⟩
  · intro X hX
    obtain ⟨t, ht, hX⟩ := hS.1 hX
    exact ⟨t, ht, (hc t ht).refl X hX⟩
  · rintro X Y Z ⟨t₁, h₁, a⟩ ⟨t₂, h₂, b⟩
    obtain ⟨t, ht, l₁, l₂⟩ := hdir t₁ h₁ t₂ h₂
    exact ⟨t, ht, (hc t ht).trans (l₁.2.1 _ _ a) (l₂.2.1 _ _ b)⟩
  · intro X hX Y hY
    obtain ⟨t₁, h₁, hX⟩ := hS.1 hX
    obtain ⟨t₂, h₂, hY⟩ := hS.1 hY
    obtain ⟨t, ht, l₁, l₂⟩ := hdir t₁ h₁ t₂ h₂
    exact ((hc t ht).total X (l₁.1 hX) Y (l₂.1 hY)).imp (fun h => ⟨t, ht, h⟩)
      (fun h => ⟨t, ht, h⟩)
  · rintro X Y f ⟨t, ht, h⟩
    exact ⟨t, ht, (hc t ht).map_rel h⟩
  · rintro X Y f ⟨t, ht, h⟩
    exact (hc t ht).map_mor h
  · rintro X Y ⟨t, ht, h⟩
    obtain ⟨f, hf⟩ := (hc t ht).map_exists h
    exact ⟨f, t, ht, hf⟩
  · rintro X Y f g ⟨t₁, h₁, a⟩ ⟨t₂, h₂, b⟩
    obtain ⟨t, ht, l₁, l₂⟩ := hdir t₁ h₁ t₂ h₂
    exact (hc t ht).map_unique (l₁.2.2 _ _ _ a) (l₂.2.2 _ _ _ b)
  · intro X hX
    obtain ⟨t, ht, hX⟩ := hS.1 hX
    exact ⟨t, ht, (hc t ht).map_id X hX⟩
  · rintro X Y Z f g ⟨t₁, h₁, a⟩ ⟨t₂, h₂, b⟩
    obtain ⟨t, ht, l₁, l₂⟩ := hdir t₁ h₁ t₂ h₂
    exact ⟨t, ht, (hc t ht).map_comp (l₁.2.2 _ _ _ a) (l₂.2.2 _ _ _ b)⟩

/-- **The chain of a tower has an upper bound** (chain inheritance applied to the tower indexed by
its own developments, `v`-small as a subset of `R`). -/
theorem IsTower.exists_cocone {R : Set D} [Small.{v} R] {t : Tower carrier}
    (ht : IsTower mor R t) (hne : t.S.Nonempty) (hchain : ChainsInherit.{v} mor) :
    ∃ (Z : D) (g : ∀ X : t.S, carrier X → carrier Z), (∀ X : t.S, mor X Z (g X)) ∧
      ∀ (X Y : t.S) (f : carrier X → carrier Y), t.F X Y f → g Y ∘ f = g X := by
  haveI : Small.{v} t.S := small_subset ht.subset
  haveI : Nonempty t.S := hne.to_subtype
  let φ : ∀ ⦃X Y : t.S⦄, t.r X Y → carrier X → carrier Y :=
    fun _ _ h => (ht.map_exists h).choose
  have hφ : ∀ ⦃X Y : t.S⦄ (h : t.r X Y), t.F X Y (φ h) :=
    fun _ _ h => (ht.map_exists h).choose_spec
  have hcoh : IsCoherentChain mor (fun X Y : t.S => t.r X Y) (fun X : t.S => (X : D)) φ :=
    { refl := fun X => ht.refl X X.2
      trans := fun _ _ _ h h' => ht.trans h h'
      total := fun X Y => ht.total X X.2 Y Y.2
      isMor := fun _ _ h => ht.map_mor (hφ h)
      map_refl := fun X h => ht.map_unique (hφ h) (ht.map_id X X.2)
      map_comp := fun _ _ _ hXY hYZ hXZ =>
        ht.map_unique (ht.map_comp (hφ hXY) (hφ hYZ)) (hφ hXZ) }
  obtain ⟨Z, g, hg, hgc⟩ :=
    hchain t.S (fun X Y : t.S => t.r X Y) (fun X : t.S => (X : D)) φ hcoh
  refine ⟨Z, g, hg, fun X Y f hf => ?_⟩
  rw [ht.map_unique hf (hφ (ht.map_rel hf))]
  exact hgc (ht.map_rel hf)

/-- **A tower extends by a development above an upper bound of its chain**, when that development
is not in it. -/
theorem IsTower.extend {R : Set D} {t : Tower carrier} (hcomp : MorphismsCompose mor)
    (ht : IsTower mor R t) {Z : D} {g : ∀ X : t.S, carrier X → carrier Z}
    (hg : ∀ X : t.S, mor X Z (g X))
    (hgc : ∀ (X Y : t.S) (f : carrier X → carrier Y), t.F X Y f → g Y ∘ f = g X)
    {Y : D} (hYR : Y ∈ R) (hY : Y ∉ t.S) {k : carrier Z → carrier Y} (hk : mor Z Y k) :
    ∃ t' : Tower carrier, IsTower mor R t' ∧ t.LE t' ∧ Y ∈ t'.S := by
  have hFS : ∀ ⦃A B f⦄, t.F A B f → A ∈ t.S ∧ B ∈ t.S :=
    fun _ _ _ h => ht.rel_mem (ht.map_rel h)
  refine ⟨⟨insert Y t.S, fun A B => t.r A B ∨ (A ∈ insert Y t.S ∧ B = Y),
    fun A B f => t.F A B f ∨ (B = Y ∧ ((∃ hA : A ∈ t.S, HEq f (k ∘ g ⟨A, hA⟩)) ∨
      (A = Y ∧ HEq f (@id (carrier A)))))⟩, ?_,
    ⟨subset_insert _ _, fun _ _ h => Or.inl h, fun _ _ _ h => Or.inl h⟩, mem_insert _ _⟩
  refine
    { subset := insert_subset hYR ht.subset, rel_mem := ?_, refl := ?_, trans := ?_,
      total := ?_, map_rel := ?_, map_mor := ?_, map_exists := ?_, map_unique := ?_,
      map_id := ?_, map_comp := ?_ }
  · rintro A B (h | ⟨hA, hB⟩)
    · exact ⟨subset_insert _ _ (ht.rel_mem h).1, subset_insert _ _ (ht.rel_mem h).2⟩
    · exact ⟨hA, mem_insert_iff.2 (Or.inl hB)⟩
  · intro A hA
    rcases hA with hA | hA
    · exact Or.inr ⟨mem_insert_iff.2 (Or.inl hA), hA⟩
    · exact Or.inl (ht.refl A hA)
  · rintro A B C (h | ⟨hA, hB⟩) (h' | ⟨-, hC⟩)
    · exact Or.inl (ht.trans h h')
    · exact Or.inr ⟨subset_insert _ _ (ht.rel_mem h).1, hC⟩
    · exact absurd (hB ▸ (ht.rel_mem h').1) hY
    · exact Or.inr ⟨hA, hC⟩
  · intro A hA B hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact Or.inl (Or.inr ⟨mem_insert_iff.2 (Or.inl hA), hB⟩)
    · exact Or.inr (Or.inr ⟨subset_insert _ _ hB, hA⟩)
    · exact Or.inl (Or.inr ⟨subset_insert _ _ hA, hB⟩)
    · exact (ht.total A hA B hB).imp Or.inl Or.inl
  · rintro A B f (h | ⟨hB, ⟨hA, -⟩ | ⟨hA, -⟩⟩)
    · exact Or.inl (ht.map_rel h)
    · exact Or.inr ⟨subset_insert _ _ hA, hB⟩
    · exact Or.inr ⟨mem_insert_iff.2 (Or.inl hA), hB⟩
  · rintro A B f (h | ⟨hB, ⟨hA, hf⟩ | ⟨hA, hf⟩⟩)
    · exact ht.map_mor h
    · subst hB
      obtain rfl := eq_of_heq hf
      exact hcomp.isMor_comp (hg ⟨A, hA⟩) hk
    · subst hB hA
      obtain rfl := eq_of_heq hf
      exact hcomp.isMor_id _
  · rintro A B (h | ⟨hA, hB⟩)
    · obtain ⟨f, hf⟩ := ht.map_exists h
      exact ⟨f, Or.inl hf⟩
    · subst hB
      rcases hA with hA | hA
      · subst hA
        exact ⟨id, Or.inr ⟨rfl, Or.inr ⟨rfl, HEq.rfl⟩⟩⟩
      · exact ⟨k ∘ g ⟨A, hA⟩, Or.inr ⟨rfl, Or.inl ⟨hA, HEq.rfl⟩⟩⟩
  · rintro A B f f' (h | ⟨hB, hf⟩) (h' | ⟨hB', hf'⟩)
    · exact ht.map_unique h h'
    · exact absurd (hB' ▸ (hFS h).2) hY
    · exact absurd (hB ▸ (hFS h').2) hY
    · subst hB
      rcases hf with ⟨hA, hf⟩ | ⟨hA, hf⟩ <;> rcases hf' with ⟨hA', hf'⟩ | ⟨hA', hf'⟩
      · exact eq_of_heq (hf.trans hf'.symm)
      · exact absurd (hA' ▸ hA) hY
      · exact absurd (hA ▸ hA') hY
      · exact eq_of_heq (hf.trans hf'.symm)
  · intro A hA
    rcases hA with hA | hA
    · subst hA
      exact Or.inr ⟨rfl, Or.inr ⟨rfl, HEq.rfl⟩⟩
    · exact Or.inl (ht.map_id A hA)
  · rintro A B C f f' (h | ⟨hB, hf⟩) (h' | ⟨hC, hf'⟩)
    · exact Or.inl (ht.map_comp h h')
    · subst hC
      rcases hf' with ⟨hB', hf'⟩ | ⟨hB', -⟩
      · have hA := (hFS h).1
        refine Or.inr ⟨rfl, Or.inl ⟨hA, heq_of_eq ?_⟩⟩
        obtain rfl := eq_of_heq hf'
        rw [Function.comp_assoc, hgc ⟨A, hA⟩ ⟨B, hB'⟩ f h]
      · exact absurd (hB' ▸ (hFS h).2) hY
    · exact absurd (hB ▸ (hFS h').1) hY
    · subst hB hC
      rcases hf' with ⟨hB', -⟩ | ⟨-, hf'⟩
      · exact absurd hB' hY
      · obtain rfl := eq_of_heq hf'
        exact Or.inr ⟨rfl, hf⟩

/-! ### Chruściel's Theorem 2.2 -/

/-- **Every development extends to a maximal one** — Chruściel 1112.5779 Thm 2.2's existence, with
rigidity dropped: a size bound and chain inheritance suffice, by Zorn on towers. -/
theorem exists_isMaximal (hcomp : MorphismsCompose mor) (hsize : SizeBound.{v} mor)
    (hchain : ChainsInherit.{v} mor) (X : D) :
    ∃ (Z : D) (f : carrier X → carrier Z), mor X Z f ∧ IsMaximal mor Z := by
  obtain ⟨R, hR, hrep⟩ := hsize
  obtain ⟨X₀, hX₀R, e₀, -, he₀, -, -, -⟩ := hrep X
  have hchains : ∀ c : Set {t : Tower carrier // IsTower mor R t ∧ X₀ ∈ t.S},
      IsChain (fun a b => a.1.LE b.1) c → ∃ ub : {t : Tower carrier // IsTower mor R t ∧ X₀ ∈ t.S},
        ∀ a ∈ c, a.1.LE ub.1 := by
    intro c hc
    rcases c.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
    · exact ⟨⟨Tower.singleton X₀, isTower_singleton hcomp hX₀R, mem_singleton _⟩,
        fun a ha => absurd ha (notMem_empty a)⟩
    · refine ⟨⟨Tower.sUnion (Subtype.val '' c), isTower_sUnion ?_ ?_, ?_⟩,
        fun a ha => Tower.le_sUnion (mem_image_of_mem _ ha)⟩
      · rintro _ ⟨a, -, rfl⟩
        exact a.2.1
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        by_cases hab : a = b
        · subst hab
          exact ⟨a.1, mem_image_of_mem _ ha, Tower.LE.refl _, Tower.LE.refl _⟩
        · rcases hc ha hb hab with h | h
          · exact ⟨b.1, mem_image_of_mem _ hb, h, Tower.LE.refl _⟩
          · exact ⟨a.1, mem_image_of_mem _ ha, Tower.LE.refl _, h⟩
      · exact mem_biUnion (mem_image_of_mem _ ha₀) a₀.2.2
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchains (fun h h' => Tower.LE.trans h h')
  haveI : Small.{v} R := hR
  obtain ⟨Z, g, hg, hgc⟩ := m.2.1.exists_cocone ⟨X₀, m.2.2⟩ hchain
  obtain ⟨Z', -, e, -, he, -, -, -⟩ := hrep Z
  refine ⟨Z', e ∘ g ⟨X₀, m.2.2⟩ ∘ e₀, hcomp.isMor_comp (hcomp.isMor_comp he₀ (hg _)) he, ?_⟩
  intro Y h hh
  obtain ⟨Y', hY'R, eY, -, heY, -, -, -⟩ := hrep Y
  by_cases hY' : Y' ∈ m.1.S
  · exact ⟨e ∘ g ⟨Y', hY'⟩ ∘ eY, hcomp.isMor_comp (hcomp.isMor_comp heY (hg _)) he⟩
  · exfalso
    obtain ⟨t', ht', hle, hYt'⟩ := m.2.1.extend hcomp hg hgc hY'R hY' (k := eY ∘ h ∘ e)
      (hcomp.isMor_comp (hcomp.isMor_comp he hh) heY)
    exact hY' ((hm ⟨t', ht', hle.1 m.2.2⟩ hle).1 hYt')

/-- **Rigidity makes a maximal development inextensible** (Chruściel's antisymmetry argument,
p. 5: "Φ̃₁ ∘ Φ̃ is an isometry of (M̃, g̃) which is the identity on ı̃(S). By (2.1) the map
Φ̃₁ ∘ Φ̃ is the identity on M̃, thus Φ̃ ∘ Φ̃₁ is the identity on M̃₁ as well"). -/
theorem IsMaximal.isInextensible (hcomp : MorphismsCompose mor) (hrig : RigidEndomorphisms mor)
    {Z : D} (hZ : IsMaximal mor Z) : IsInextensible mor Z := by
  intro Y f hf
  obtain ⟨g, hg⟩ := hZ Y f hf
  exact ⟨hf, g, hg, hrig Z _ (hcomp.isMor_comp hf hg), hrig Y _ (hcomp.isMor_comp hg hf)⟩

/-- **Chruściel 1112.5779 Theorem 2.2, abstractly**: under rigidity (2.1), a size bound and chain
inheritance, every development extends to one inextensible in the class. -/
theorem chrusciel_theorem_2_2 (hcomp : MorphismsCompose mor) (hrig : RigidEndomorphisms mor)
    (hsize : SizeBound.{v} mor) (hchain : ChainsInherit.{v} mor) (X : D) :
    ∃ (Z : D) (f : carrier X → carrier Z), mor X Z f ∧ IsInextensible mor Z := by
  obtain ⟨Z, f, hf, hZ⟩ := exists_isMaximal hcomp hsize hchain X
  exact ⟨Z, f, hf, hZ.isInextensible hcomp hrig⟩

/-! ### Chruściel's own route: unique morphisms -/

/-- Unique morphisms give rigid endomorphisms (the identity is a morphism). -/
theorem UniqueMorphisms.rigidEndomorphisms (hcomp : MorphismsCompose mor)
    (h : UniqueMorphisms mor) : RigidEndomorphisms mor :=
  fun X f hf => h X X f id hf (hcomp.isMor_id X)

/-- **Chruściel's (2.2) as written** ("p ∼ q iff q = Φ(p), where Φ : M̃ → M̃₁ is the isometric C¹
embedding such that Φ ∘ ı̃ = ı̃₁"): when morphisms are unique, the morphisms of a chain of the
extension preorder are forced, hence coherent, and the chain has an upper bound. -/
theorem exists_upperBound_of_uniqueMorphisms (hcomp : MorphismsCompose mor)
    (huniq : UniqueMorphisms mor) (hchain : ChainsInherit.{w} mor) {c : Set D}
    (hc : IsChain (Extends mor) c) (hne : c.Nonempty) : ∃ Z : D, ∀ X ∈ c, Extends mor X Z := by
  haveI : Nonempty c := hne.to_subtype
  have htot : ∀ X Y : c, Extends mor X Y ∨ Extends mor Y X := fun X Y => by
    by_cases h : X = Y
    · subst h
      exact Or.inl ⟨id, hcomp.isMor_id _⟩
    · exact hc X.2 Y.2 fun h' => h (Subtype.ext h')
  let φ : ∀ ⦃X Y : c⦄, Extends mor X Y → carrier X → carrier Y := fun _ _ h => h.choose
  have hφ : ∀ ⦃X Y : c⦄ (h : Extends mor X Y), mor X Y (φ h) := fun _ _ h => h.choose_spec
  obtain ⟨Z, g, hg, -⟩ := hchain c (fun X Y : c => Extends mor X Y) (fun X : c => (X : D)) φ
    { refl := fun _ => ⟨id, hcomp.isMor_id _⟩
      trans := fun _ _ _ ⟨f, hf⟩ ⟨f', hf'⟩ => ⟨f' ∘ f, hcomp.isMor_comp hf hf'⟩
      total := htot
      isMor := hφ
      map_refl := fun _ h => huniq _ _ _ _ (hφ h) (hcomp.isMor_id _)
      map_comp := fun _ _ _ hXY hYZ hXZ =>
        huniq _ _ _ _ (hcomp.isMor_comp (hφ hXY) (hφ hYZ)) (hφ hXZ) }
  exact ⟨Z, fun X hX => ⟨g ⟨X, hX⟩, hg ⟨X, hX⟩⟩⟩

/-- **Chruściel's proof of Theorem 2.2** (p. 5, "The Kuratowski–Zorn Lemma shows that M_W(M, g, i)
has maximal elements"): with unique morphisms, Zorn on the extension preorder itself. -/
theorem exists_isMaximal_of_uniqueMorphisms (hcomp : MorphismsCompose mor)
    (huniq : UniqueMorphisms mor) (hchain : ChainsInherit.{w} mor) (X : D) :
    ∃ (Z : D) (f : carrier X → carrier Z), mor X Z f ∧ IsMaximal mor Z := by
  have htrans : ∀ {a b c : {Y : D // Extends mor X Y}}, Extends mor a.1 b.1 →
      Extends mor b.1 c.1 → Extends mor a.1 c.1 :=
    fun ⟨f, hf⟩ ⟨f', hf'⟩ => ⟨f' ∘ f, hcomp.isMor_comp hf hf'⟩
  have hbound : ∀ c : Set {Y : D // Extends mor X Y},
      IsChain (fun a b => Extends mor a.1 b.1) c →
        ∃ ub : {Y : D // Extends mor X Y}, ∀ a ∈ c, Extends mor a.1 ub.1 := by
    intro c hc
    rcases c.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
    · exact ⟨⟨X, id, hcomp.isMor_id X⟩, fun a ha => absurd ha (notMem_empty a)⟩
    · have hc' : IsChain (Extends mor) (Subtype.val '' c) := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        exact hc ha hb fun h => hab (congrArg Subtype.val h)
      obtain ⟨Z, hZ⟩ := exists_upperBound_of_uniqueMorphisms hcomp huniq hchain hc'
        (Set.Nonempty.image Subtype.val ⟨a₀, ha₀⟩)
      obtain ⟨f₀, hf₀⟩ := a₀.2
      obtain ⟨g₀, hg₀⟩ := hZ a₀.1 (mem_image_of_mem _ ha₀)
      exact ⟨⟨Z, g₀ ∘ f₀, hcomp.isMor_comp hf₀ hg₀⟩, fun a ha => hZ a.1 (mem_image_of_mem _ ha)⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound htrans
  obtain ⟨f, hf⟩ := m.2
  exact ⟨m.1, f, hf, fun Y g hg => hm ⟨Y, g ∘ f, hcomp.isMor_comp hf hg⟩ ⟨g, hg⟩⟩

/-- **Zorn on the extension preorder, chains split by cofinality** (the chain step shared with
`T-abs-curves-extend-second-countable`): if every sequence of extensions has an upper bound, and
every chain with no countable cofinal sequence has one, every development extends to a maximal
one. No coherence and no rigidity is asked: a chain of countable cofinality is bounded through a
cofinal increasing sequence, whose morphisms compose. -/
theorem exists_isMaximal_of_sequences (hcomp : MorphismsCompose mor)
    (hseq : ∀ X : ℕ → D, (∀ n, Extends mor (X n) (X (n + 1))) → ∃ Z, ∀ n, Extends mor (X n) Z)
    (hunc : ∀ c : Set D, IsChain (Extends mor) c → c.Nonempty →
      (¬ ∃ s : ℕ → D, (∀ n, s n ∈ c) ∧ ∀ x ∈ c, ∃ n, Extends mor x (s n)) →
        ∃ Z, ∀ x ∈ c, Extends mor x Z)
    (X : D) : ∃ (Z : D) (f : carrier X → carrier Z), mor X Z f ∧ IsMaximal mor Z := by
  classical
  have htrans : ∀ {a b c : D}, Extends mor a b → Extends mor b c → Extends mor a c :=
    fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g ∘ f, hcomp.isMor_comp hf hg⟩
  have hrefl : ∀ a : D, Extends mor a a := fun a => ⟨id, hcomp.isMor_id a⟩
  have hbound : ∀ c : Set {Y : D // Extends mor X Y},
      IsChain (fun a b => Extends mor a.1 b.1) c →
        ∃ ub : {Y : D // Extends mor X Y}, ∀ a ∈ c, Extends mor a.1 ub.1 := by
    intro c hc
    rcases c.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
    · exact ⟨⟨X, hrefl X⟩, fun a ha => absurd ha (notMem_empty a)⟩
    have hc' : IsChain (Extends mor) (Subtype.val '' c) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hc ha hb fun h => hab (congrArg Subtype.val h)
    suffices h : ∃ Z, ∀ x ∈ Subtype.val '' c, Extends mor x Z by
      obtain ⟨Z, hZ⟩ := h
      exact ⟨⟨Z, htrans a₀.2 (hZ _ (mem_image_of_mem _ ha₀))⟩,
        fun a ha => hZ _ (mem_image_of_mem _ ha)⟩
    by_cases hcof : ∃ s : ℕ → D, (∀ n, s n ∈ Subtype.val '' c) ∧
        ∀ x ∈ Subtype.val '' c, ∃ n, Extends mor x (s n)
    · obtain ⟨s, hs, hcofs⟩ := hcof
      let b : ℕ → D := fun n => Nat.rec (motive := fun _ => D) (s 0)
        (fun n bn => if Extends mor bn (s (n + 1)) then s (n + 1) else bn) n
      have hb : ∀ n, b n ∈ Subtype.val '' c ∧ Extends mor (s n) (b n) := by
        intro n
        induction n with
        | zero => exact ⟨hs 0, hrefl _⟩
        | succ n ih =>
          show (if Extends mor (b n) (s (n + 1)) then s (n + 1) else b n) ∈ Subtype.val '' c ∧
            Extends mor (s (n + 1)) (if Extends mor (b n) (s (n + 1)) then s (n + 1) else b n)
          by_cases h : Extends mor (b n) (s (n + 1))
          · rw [if_pos h]
            exact ⟨hs _, hrefl _⟩
          · rw [if_neg h]
            refine ⟨ih.1, ?_⟩
            rcases eq_or_ne (b n) (s (n + 1)) with he | he
            · rw [he]
              exact hrefl _
            · exact (hc' ih.1 (hs _) he).resolve_left h
      have hbs : ∀ n, Extends mor (b n) (b (n + 1)) := by
        intro n
        show Extends mor (b n) (if Extends mor (b n) (s (n + 1)) then s (n + 1) else b n)
        by_cases h : Extends mor (b n) (s (n + 1))
        · rw [if_pos h]
          exact h
        · rw [if_neg h]
          exact hrefl _
      obtain ⟨Z, hZ⟩ := hseq b hbs
      exact ⟨Z, fun x hx => let ⟨n, hn⟩ := hcofs x hx; htrans hn (htrans (hb n).2 (hZ n))⟩
    · exact hunc _ hc' (Set.Nonempty.image _ ⟨a₀, ha₀⟩) hcof
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hbound htrans
  obtain ⟨f, hf⟩ := m.2
  exact ⟨m.1, f, hf, fun Y g hg => hm ⟨Y, g ∘ f, hcomp.isMor_comp hf hg⟩ ⟨g, hg⟩⟩

/-- Without a bound on their number, the developments themselves are the set of representatives:
`SizeBound.{w}` always holds for developments in `Type w`. -/
theorem sizeBound_self (hcomp : MorphismsCompose mor) : SizeBound.{w} mor :=
  ⟨univ, inferInstance, fun X => ⟨X, mem_univ X, id, id, hcomp.isMor_id X, hcomp.isMor_id X,
    rfl, rfl⟩⟩

/-- **Chain inheritance alone**, for chains of any size in the universe of the developments,
gives maximal developments. -/
theorem exists_isMaximal_of_chainsInherit (hcomp : MorphismsCompose mor)
    (hchain : ChainsInherit.{w} mor) (X : D) :
    ∃ (Z : D) (f : carrier X → carrier Z), mor X Z f ∧ IsMaximal mor Z :=
  exists_isMaximal hcomp (sizeBound_self hcomp) hchain X

/-- An inextensible development is maximal, and every morphism out of it is bijective
(`Causal.CBG.Dev.IsETTMaximal`'s form). -/
theorem IsInextensible.isMaximal {Z : D} (h : IsInextensible mor Z) : IsMaximal mor Z :=
  fun Y f hf => let ⟨_, g, hg, _⟩ := h Y f hf; ⟨g, hg⟩

theorem IsInextensible.bijective {Z Y : D} (h : IsInextensible mor Z) {f : carrier Z → carrier Y}
    (hf : mor Z Y f) : Bijective f := by
  obtain ⟨-, g, -, hgf, hfg⟩ := h Y f hf
  exact ⟨LeftInverse.injective (congrFun hgf), RightInverse.surjective (congrFun hfg)⟩

/-! ### The hypotheses are needed -/

/-- Two developments `false`, `true` with carriers `Bool`: the identity on each, and every map
from `false` to `true`. -/
def twoMor (X Y : Bool) (f : Bool → Bool) : Prop := (X = Y → f = id) ∧ (X = true → Y = true)

/-- **Rigidity (2.1) does not make extensions unique**: `twoMor` has rigid endomorphisms and two
morphisms `false → true`. So Chruściel's "the isometric C¹ embedding Φ" in (2.2) uses more than
(2.1) (in his classes, the local rigidity of isometries); `exists_isMaximal` needs neither. -/
theorem twoMor_rigid_not_unique :
    MorphismsCompose (carrier := fun _ : Bool => Bool) twoMor ∧
      RigidEndomorphisms (carrier := fun _ : Bool => Bool) twoMor ∧
      ¬ UniqueMorphisms (carrier := fun _ : Bool => Bool) twoMor := by
  refine ⟨⟨fun X => ⟨fun _ => rfl, id⟩, ?_⟩, fun X f hf => hf.1 rfl, fun h => ?_⟩
  · rintro X Y Z f g ⟨hf₁, hf₂⟩ ⟨hg₁, hg₂⟩
    refine ⟨fun hXZ => ?_, fun hX => hg₂ (hf₂ hX)⟩
    subst hXZ
    by_cases hXY : X = Y
    · subst hXY
      rw [hf₁ rfl, hg₁ rfl]
      rfl
    · exfalso
      cases X <;> cases Y <;> simp_all
  · have := congrFun (h false true id not ⟨fun h => absurd h (by decide), fun _ => rfl⟩
      ⟨fun h => absurd h (by decide), fun _ => rfl⟩) true
    exact absurd this (by decide)

/-- The ordinals of a universe, a morphism `a → b` for `a ≤ b`. -/
def ordinalMor (a b : Ordinal.{v}) (_ : Unit → Unit) : Prop := a ≤ b

/-- **The size bound cannot be dropped**: on the ordinals of `Type v`, morphisms compose and are
unique, every chain of at most `v`-many ordinals has an upper bound, and no ordinal is maximal. So
`SizeBound.{v}` fails there (`not_sizeBound_ordinalMor`); this is the proper class of Chruściel's
Remark 2.3.1, as a universe. -/
theorem ordinalMor_separates :
    MorphismsCompose (carrier := fun _ : Ordinal.{v} => Unit) ordinalMor ∧
      UniqueMorphisms (carrier := fun _ : Ordinal.{v} => Unit) ordinalMor ∧
      ChainsInherit.{v} (carrier := fun _ : Ordinal.{v} => Unit) ordinalMor ∧
      ∀ a, ¬ IsMaximal (carrier := fun _ : Ordinal.{v} => Unit) ordinalMor a := by
  refine ⟨⟨fun a => le_refl a, fun a b c _ _ hab hbc => le_trans hab hbc⟩,
    fun _ _ f g _ _ => Subsingleton.elim f g, ?_, fun a ha => ?_⟩
  · intro ι _ _ r X φ _
    obtain ⟨b, hb⟩ := Ordinal.bddAbove_of_small (s := range X)
    exact ⟨b, fun _ => id, fun i => hb (mem_range_self i), fun _ _ _ => Subsingleton.elim _ _⟩
  · obtain ⟨_, h⟩ := ha (Order.succ a) id (Order.le_succ a)
    exact absurd h (not_le.2 (Order.lt_succ a))

theorem not_sizeBound_ordinalMor :
    ¬ SizeBound.{v} (carrier := fun _ : Ordinal.{v} => Unit) ordinalMor := by
  intro hsize
  obtain ⟨hcomp, -, hchain, hmax⟩ := ordinalMor_separates.{v}
  obtain ⟨Z, -, -, hZ⟩ := exists_isMaximal hcomp hsize hchain (0 : Ordinal.{v})
  exact hmax Z hZ

/-- The natural numbers, a morphism `m → n` for `m ≤ n`. -/
def natMor (m n : ℕ) (_ : Unit → Unit) : Prop := m ≤ n

/-- **Chain inheritance cannot be dropped**: on `ℕ`, morphisms compose and are unique, the size
bound holds, and no development is maximal. -/
theorem natMor_separates :
    MorphismsCompose (carrier := fun _ : ℕ => Unit) natMor ∧
      UniqueMorphisms (carrier := fun _ : ℕ => Unit) natMor ∧
      SizeBound.{0} (carrier := fun _ : ℕ => Unit) natMor ∧
      ∀ n, ¬ IsMaximal (carrier := fun _ : ℕ => Unit) natMor n := by
  refine ⟨⟨fun a => le_refl a, fun a b c _ _ hab hbc => le_trans hab hbc⟩,
    fun _ _ f g _ _ => Subsingleton.elim f g, ⟨univ, inferInstance, fun n =>
      ⟨n, mem_univ n, id, id, le_refl n, le_refl n, rfl, rfl⟩⟩, fun n hn => ?_⟩
  obtain ⟨_, h⟩ := hn (n + 1) id (Nat.le_succ n)
  exact Nat.not_succ_le_self n h

/-- One development with carrier `Bool`, every map a morphism. -/
def allMor (_ _ : Unit) (_ : Bool → Bool) : Prop := True

/-- **Rigidity cannot be dropped from inextensibility**: with every self-map of `Bool` a morphism,
the size bound and chain inheritance hold and the one development is maximal, but the constant map
is a morphism out of it which is not an isomorphism. -/
theorem allMor_separates :
    MorphismsCompose (carrier := fun _ : Unit => Bool) allMor ∧
      SizeBound.{0} (carrier := fun _ : Unit => Bool) allMor ∧
      ChainsInherit.{0} (carrier := fun _ : Unit => Bool) allMor ∧
      IsMaximal (carrier := fun _ : Unit => Bool) allMor () ∧
      ¬ IsInextensible (carrier := fun _ : Unit => Bool) allMor () := by
  refine ⟨⟨fun _ => trivial, fun _ _ _ _ _ _ _ => trivial⟩, ⟨univ, inferInstance, fun X =>
    ⟨X, mem_univ X, id, id, trivial, trivial, rfl, rfl⟩⟩, ?_, fun _ _ _ => ⟨id, trivial⟩,
    fun h => ?_⟩
  · intro ι _ _ r X φ _
    exact ⟨(), fun _ _ => true, fun _ => trivial, fun _ _ _ => rfl⟩
  · obtain ⟨-, g, -, hgf, -⟩ := h () (fun _ => true) trivial
    have h₁ := congrFun hgf true
    have h₂ := congrFun hgf false
    simp only [Function.comp_apply, id_eq] at h₁ h₂
    exact absurd (h₁.symm.trans h₂) (by decide)

end AbstractDev

end Causal
