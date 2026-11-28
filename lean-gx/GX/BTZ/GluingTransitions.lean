import Causal.CBG.FromModel
import Causal.Pushout

/-!
# Gluing two charted spaces along open embeddings whose transitions extend to morphisms

Target `T-btz-gluing-dedupe` (`roadmap/roadmap.toml`): a clean-up, no paper label. The four-case
transition proof of the glued atlas `Causal.CBG.gluedChartedSpace` over two pieces (the identities
on the diagonal, a forward map on the glued part of the first piece, a backward map on the glued
part of the second) was written twice, in `GX.Ppcm.trans_emb` (`GX.BTZ.Ppcm`, btz § 5.2's
`M₁ ∨ M₂`) and in the `htrans` of `GX.E0AbsMax.exists_e0Pushout` (`GX.BTZ.AbsMax`, B21 Prop 2.17's
push-out `(M ⊔ N)/Reg M`). It is stated once here and both follow from it.

* `GX.GluingTrans.liftPropOn_glueTransition_of_ext` — for any family of open embeddings
  `e i : M i → Z`, the canonical transition `glueTransition he i j` is a `G`-morphism on
  `e i ⁻¹' range (e j)` as soon as **some** `G`-morphism `F` there satisfies `e j ∘ F = e i`.
* `GX.GluingTrans.preimage_range_true`, `GX.GluingTrans.preimage_range_false` — for two pieces
  `e true`, `e false` forming a push-out of `j₁ : U → X true`, `j₂ : U → X false` (the square
  commutes, `e true x = e false y` only along `U`), the glued parts are `range j₁` and `range j₂`.
* `GX.GluingTrans.liftPropOn_glueTransition_pair` — **the gluing lemma**: for such a push-out,
  every transition of the glued atlas is a `G`-morphism as soon as `j₂ ∘ j₁⁻¹` extends to a
  `G`-morphism `F` on `range j₁` and `j₁ ∘ j₂⁻¹` to a `G`-morphism `F'` on `range j₂`.

The push-out is stated by its two properties (`hcomm`, `hglue`) rather than on
`Causal.Gluing j₁ j₂` itself, so that pieces whose types are only definitionally those of the
gluing (`FlatE0 N` for `N` in `GX.E0AbsMax.pushPiece`) instantiate it without a cast; for
`Causal.Gluing` they are `Causal.Gluing.ι₁_j₁` and `Causal.Gluing.ι₁_eq_ι₂_iff`.

## Hypothesis checklist (`liftPropOn_glueTransition_pair`)

| hypothesis | here |
|---|---|
| `e true`, `e false` open embeddings | ✓ carried (`he`) |
| the square commutes on `U` | ✓ carried (`hcomm`) |
| the pieces meet only along `U` | ✓ carried (`hglue`) |
| a `G`-morphism extending `j₂ ∘ j₁⁻¹`, and one extending `j₁ ∘ j₂⁻¹` | ✓ carried (`hF`, `hF'`) |
| `G` closed under restriction | ✓ carried (as for every sheaf law of `Causal.CBG.FromModel`) |

## SCOPE (disclosed)

Nothing is left unproved; 0 `sorry`. The lemma is stated for an arbitrary structure groupoid `G`;
its two uses in this library take `G = e0Groupoid`. `GX.BTZMax.trans_inj` (`GX.BTZ.MaxExtension`,
the union of a chain) is the indexed form of the same argument and could be rewritten on
`liftPropOn_glueTransition_of_ext`; it was outside this target's files.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function Topology ChartedSpace

namespace GX.GluingTrans

section Family

variable {Y : Type*} [TopologicalSpace Y] {G : StructureGroupoid Y} [ClosedUnderRestriction G]
  {Z : Type*} [TopologicalSpace Z] {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, Nonempty (M i)] [∀ i, ChartedSpace Y (M i)] {e : ∀ i, M i → Z}

/-- **A transition of the glued atlas is a morphism when it extends to one**: if a `G`-morphism
`F : M i → M j` on the glued part `e i ⁻¹' range (e j)` satisfies `e j (F x) = e i x` there, the
canonical transition `glueTransition he i j` is a `G`-morphism on it (it agrees with `F`). -/
theorem liftPropOn_glueTransition_of_ext (he : ∀ i, IsOpenEmbedding (e i)) {i j : ι}
    {F : M i → M j} (hF : LiftPropOn G.IsLocalStructomorphWithinAt F (e i ⁻¹' range (e j)))
    (hFe : ∀ x ∈ e i ⁻¹' range (e j), e j (F x) = e i x) :
    LiftPropOn G.IsLocalStructomorphWithinAt (Causal.CBG.glueTransition he i j)
      (e i ⁻¹' range (e j)) :=
  Causal.CBG.liftPropOn_congr_of_eqOn ((he j).isOpen_range.preimage (he i).continuous) hF
    fun x hx => by
      show F x = (Causal.CBG.glueEmb he j).symm (e i x)
      rw [← hFe x hx, Causal.CBG.glueEmb_symm_apply]

/-- The diagonal transitions of a glued atlas are morphisms (they are the identity). -/
theorem liftPropOn_glueTransition_self (he : ∀ i, IsOpenEmbedding (e i)) (i : ι) :
    LiftPropOn G.IsLocalStructomorphWithinAt (Causal.CBG.glueTransition he i i)
      (e i ⁻¹' range (e i)) :=
  liftPropOn_glueTransition_of_ext he
    (Causal.CBG.liftPropOn_id ((he i).isOpen_range.preimage (he i).continuous))
    fun _ _ => rfl

end Family

section Pair

variable {X : Bool → Type*} {Z U : Type*} {e : ∀ b, X b → Z}
  {j₁ : U → X true} {j₂ : U → X false}

/-- The part of the first piece glued to the second is `range j₁`. -/
theorem preimage_range_true (hcomm : ∀ u, e true (j₁ u) = e false (j₂ u))
    (hglue : ∀ x y, e true x = e false y → ∃ u, j₁ u = x ∧ j₂ u = y) :
    e true ⁻¹' range (e false) = range j₁ := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl, -⟩ := hglue x y hy.symm
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨j₂ u, (hcomm u).symm⟩

/-- The part of the second piece glued to the first is `range j₂`. -/
theorem preimage_range_false (hcomm : ∀ u, e true (j₁ u) = e false (j₂ u))
    (hglue : ∀ x y, e true x = e false y → ∃ u, j₁ u = x ∧ j₂ u = y) :
    e false ⁻¹' range (e true) = range j₂ := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, -, rfl⟩ := hglue x y hx
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨j₁ u, hcomm u⟩

variable {Y : Type*} [TopologicalSpace Y] {G : StructureGroupoid Y} [ClosedUnderRestriction G]
  [TopologicalSpace Z] [∀ b, TopologicalSpace (X b)] [∀ b, Nonempty (X b)]
  [∀ b, ChartedSpace Y (X b)]

/-- **Gluing two charted spaces along an open embedding whose transitions extend to morphisms**:
for two open embeddings `e true : X true → Z`, `e false : X false → Z` forming a push-out of
`j₁ : U → X true` and `j₂ : U → X false` (`hcomm`, `hglue`), every transition of the glued atlas
is a `G`-morphism on its domain, as soon as `j₂ ∘ j₁⁻¹` extends to a `G`-morphism `F` on
`range j₁` and `j₁ ∘ j₂⁻¹` to a `G`-morphism `F'` on `range j₂`. With
`Causal.CBG.gluedChartedSpace_hasGroupoid` the glued atlas is then in `G`, and with
`Causal.CBG.liftPropOn_glue` both `e b` are `G`-morphisms. -/
theorem liftPropOn_glueTransition_pair (he : ∀ b, IsOpenEmbedding (e b))
    (hcomm : ∀ u, e true (j₁ u) = e false (j₂ u))
    (hglue : ∀ x y, e true x = e false y → ∃ u, j₁ u = x ∧ j₂ u = y)
    {F : X true → X false} (hF : LiftPropOn G.IsLocalStructomorphWithinAt F (range j₁))
    (hFj : ∀ u, F (j₁ u) = j₂ u)
    {F' : X false → X true} (hF' : LiftPropOn G.IsLocalStructomorphWithinAt F' (range j₂))
    (hF'j : ∀ u, F' (j₂ u) = j₁ u) (b c : Bool) :
    LiftPropOn G.IsLocalStructomorphWithinAt (Causal.CBG.glueTransition he b c)
      (e b ⁻¹' range (e c)) := by
  cases b <;> cases c
  · exact liftPropOn_glueTransition_self he false
  · refine liftPropOn_glueTransition_of_ext he (F := F') ?_ ?_
    · rwa [preimage_range_false hcomm hglue]
    · rw [preimage_range_false hcomm hglue]
      rintro _ ⟨u, rfl⟩
      rw [hF'j, hcomm]
  · refine liftPropOn_glueTransition_of_ext he (F := F) ?_ ?_
    · rwa [preimage_range_true hcomm hglue]
    · rw [preimage_range_true hcomm hglue]
      rintro _ ⟨u, rfl⟩
      rw [hFj, hcomm]
  · exact liftPropOn_glueTransition_self he true

end Pair

end GX.GluingTrans
