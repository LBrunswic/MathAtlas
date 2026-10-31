import GX.Spread.Completion

/-!
# Branched coverings: definition, path-lifting characterisation, restrictions (§3.2)

The primer on branched coverings of `papers/gx` (`RamcovGX.tex:955–1090`), with Fox's extension
property for complete spreads built (DEC-23). `lem:path_covering` and `lem:portly_first_countable`
(`RamcovGX.tex:967`, `974`) are `GX.path_covering`, `GX.portly_first_countable` (strict library).

* **`def:branched_covering`** — `RamcovGX.tex:988`: `GX.IsBranchedCovering`, `GX.branchingLocus`,
  `GX.IsPossiblyBranchedOver`, `GX.fiber`; inhabited by `GX.isBranchedCovering_id`.
* **`rem:branching_locii_branched_covering`** — `RamcovGX.tex:998`:
  `GX.IsBranchedCovering.branching_locii`.
* **`rem:ordinary_part_branched_covering`** — `RamcovGX.tex:1000` ("covering" = surjective
  covering map, DEC-40): `GX.IsBranchedCovering.ordinary_part`.
* **`lem:portly_preimage_branched`** — `RamcovGX.tex:1003`: `GX.IsBranchedCovering.isPortly_preimage`.
* **`lem:complete_path_carac`** — `RamcovGX.tex:1014`: `GX.complete_path_carac` (items (iii),
  (iv): `GX.HomotopyLiftExtends`, `GX.PathLiftExtends`). Fox's "corollary of the extension
  theorem" is proved, not assumed: `GX.exists_extend_of_isCompleteSpread` (homotopies),
  `GX.exists_extend_path_of_isCompleteSpread` (paths); the converse core
  `GX.isCompleteSpread_of_pathLiftExtends` (path lifting in the Fox completion of
  `GX.Spread.Completion`); lifting on `[0,1)` through a covering `GX.exists_partial_lift`.
* **`lem:branched_covering_restriction`** — `RamcovGX.tex:1041`: `GX.branched_covering_restriction`
  (surjectivity part `GX.IsBranchedCovering.image_connectedComponentIn`).
* **`cor:spread_connected_image`** — `RamcovGX.tex:1053`: `GX.spread_connected_image`.
* **`cor:subcovering_portly`** — `RamcovGX.tex:1062`: `GX.subcovering_portly`.
* **`lem:subcovering_general`** — `RamcovGX.tex:1069`: `GX.subcovering_general` (with
  `GX.IsSpread.restrict_of_locallyConnectedSpace`, `GX.subset_ordY_restrict`).

> A branched covering is a complete surjective spread $X\rightarrow Y$, with $X$ and $Y$
> connected, whose ordinary locii in $X$ and $Y$ are portly subsets of $X$ and $Y$ respectively.
> […] We say that $X\rightarrow Y$ is branched over $Y\setminus \ord(Y)$. The latter is the
> branching locus of $X\rightarrow Y$ and for $S\subset Y$, we say that $X\rightarrow Y$ is
> possibly branched over $S$ if $S$ contains its branching locus.
>
> The branching locii of a branched covering are skeletal thus closed with empty interior.
>
> The ordinary part $\ord(X)\rightarrow \ord(Y)$ of a branched covering $X\rightarrow Y$ is a
> covering.
>
> If $X\xrightarrow{p} Y$ is a branched covering, then the preimage of portly subset of $Y$ is
> portly in $X$.
>
> Let $X\xrightarrow{p} Y$ be a spread with $X$ connected which induces a covering
> $X_1\rightarrow Y_1$ for some $X_1$ and $Y_1$ portly subsets of $X$ and $Y$ respectively. Then
> the following are equivalent: (i) $X\rightarrow Y$ is a branched covering; (ii)
> $X\rightarrow Y$ is a complete spread (iii) for every Hausdorff locally connected topological
> space $Q$ and every homotopy $H:Q\times [0,1]\rightarrow Y$ such that
> $H(Q\times [0,1[)\subset Y_1$, every partial lift $\hat H : Q \times [0,1[ \rightarrow X_1$ of
> $H$ extends continuously to some lift $Q \times [0,1] \rightarrow X$ of $H$; (iv) for every
> path $\gamma:[0,1]\rightarrow Y$ such that $\gamma([0,1[) \subset Y_1$, every partial lift
> $\hat \gamma : [0,1[ \rightarrow X_1$ extends continuously to some lift $[0,1] \rightarrow X$
> of $\gamma$.
>
> Let $X\xrightarrow{p} Y$ be a branched covering, let $\U$ be some open connected subset of $Y$
> and let $\V$ be a connected component of $p^{-1}(\U)$. Then $\V\xrightarrow{p} \U$ is a
> branched covering.
>
> Let $X\xrightarrow{p} Y$ be a branched covering. Then $p$ is open, furthermore for every
> connected open $\U\subset Y$ and every connected component $\V$ of $p^{-1}(\U)$ the map
> $\V\xrightarrow{p} \U$ is surjective.
>
> Let $X\xrightarrow{p} Y$ be a branched covering, let $\U$ be some portly subset of $Y$ then
> $p^{-1}(\U)\xrightarrow{p}\U$ is a branched covering.
>
> Let $X\xrightarrow{p} Y$ be a branched covering, let $Y_1\subset Y$ containing a portly subset
> of $Y$ then $p^{-1}(Y_1)\xrightarrow{~p~}Y_1$ is a branched covering.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §3 standing: all spaces Hausdorff, locally path-connected, first countable | ⚠ weakened: each theorem carries what its proof uses (below) |
| `def`, `rem:branching_locii…`, `rem:ordinary_part…`, `lem:portly_preimage_branched` | ⚠ weakened: no separation or countability hypothesis |
| `lem:complete_path_carac`: `X` connected; `X₁ → Y₁` a covering, `X₁`, `Y₁` portly | ✓ carried (`ConnectedSpace X`; `MapsTo`, `IsCoveringMap`, surjective — DEC-40) |
| `lem:complete_path_carac`: `X`, `Y` Hausdorff, locally path-connected | ✓ carried |
| `lem:complete_path_carac`: `X` first countable | ⚠ weakened: not used |
| `lem:complete_path_carac`: `Y` first countable | ✓ carried |
| `lem:complete_path_carac` (iii): `Q` Hausdorff, locally connected | ✓ carried in `HomotopyLiftExtends`; Fox's property itself does not use Hausdorff |
| `lem:branched_covering_restriction`: `U` open connected | ⚠ weakened: preconnected (`V ≠ ∅` gives `U ≠ ∅`) |
| `lem:branched_covering_restriction`, `cor:subcovering_portly`: `X`, `Y` T2, loc. path-conn. | ✓ carried; `Y` first countable carried, `X` first countable not used |
| `cor:spread_connected_image`: standing hypotheses | ⚠ weakened: none on `X`; `Y` T1, locally path-connected, first countable |
| `lem:subcovering_general`: standing hypotheses | ✓ carried: `X`, `Y` T2, locally path-connected, first countable |

## SCOPE (disclosed)

* A partial lift on `[0,1)` is a function `I → X` continuous on `{t | t < 1}` (its value at `1` is
  irrelevant); on `Q × [0,1)`, continuous on `{z | z.2 < 1}`. "Extends continuously to some lift"
  is a continuous `g` with `p ∘ g = γ` agreeing with the partial lift before time `1`.
* (iii) quantifies over `Q : Type w` for a fixed universe `w` (the statement is universe
  polymorphic in `w`).
* "`V` a connected component of `p⁻¹(U)`" is `GX.IsCompOf p U V`; the restricted map is
  `MapsTo.restrict`, the `MapsTo` proof being an argument (it follows from `IsCompOf`,
  `GX.IsCompOf.mapsTo`). `p⁻¹(U) → U` is `Set.restrictPreimage`.
* The paper's proof of (iv) ⇒ (ii) embeds `X` in its completion `X̄`; a completion in the paper's
  sense need not exist (`theo:Fox_completion_functor`, `GX.Spread.Completion`). The proof
  here uses Fox's space of ends and only needs the image of `X₁ = p⁻¹(Y₁)` to be portly in it,
  which holds because it is `base⁻¹(Y₁)`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### The definition -/

/-- `def:branched_covering`. A branched covering is a complete surjective spread `p : X → Y`,
with `X` and `Y` connected, whose ordinary loci in `X` and in `Y` are portly. -/
structure IsBranchedCovering (p : X → Y) : Prop where
  isSpread : IsSpread p
  isComplete : IsCompleteSpread p
  surjective : Surjective p
  connectedSpace_source : ConnectedSpace X
  connectedSpace_target : ConnectedSpace Y
  isPortly_ordX : IsPortly (ordX p)
  isPortly_ordY : IsPortly (ordY p)

/-- `def:branched_covering`. The branching locus `Y ∖ ord(Y)`. -/
def branchingLocus (p : X → Y) : Set Y := (ordY p)ᶜ

/-- `def:branched_covering`. `p` is *possibly branched over* `S` if `S` contains its branching
locus. -/
def IsPossiblyBranchedOver (p : X → Y) (S : Set Y) : Prop := branchingLocus p ⊆ S

/-- `def:branched_covering`. The fiber above `a`. -/
def fiber (p : X → Y) (a : Y) : Set X := p ⁻¹' {a}

/-- A connected component of `p⁻¹(U)` maps into `U`. -/
theorem IsCompOf.mapsTo {p : X → Y} {U : Set Y} {V : Set X} (hV : IsCompOf p U V) :
    MapsTo p V U :=
  hV.subset

/-- The identity of a connected, locally connected space is a branched covering (unbranched). -/
theorem isBranchedCovering_id [ConnectedSpace Y] [LocallyConnectedSpace Y] :
    IsBranchedCovering (id : Y → Y) := by
  have hord : ordY (id : Y → Y) = univ := by
    refine eq_univ_of_forall fun y => ⟨univ, isOpen_univ, mem_univ y, ⟨y, mem_univ y⟩, ?_⟩
    intro x _
    exact ⟨Homeomorph.setCongr (isPreconnected_univ.connectedComponentIn (mem_univ x)), fun _ => rfl⟩
  have hp : IsPortly (ordY (id : Y → Y)) := by rw [hord]; exact isPortly_univ
  exact ⟨isSpread_id, isCompleteSpread_id, surjective_id, inferInstance, inferInstance, hp, hp⟩

/-- `rem:branching_locii_branched_covering`. -/
theorem IsBranchedCovering.branching_locii {p : X → Y} (hp : IsBranchedCovering p) :
    IsSkeletal (ordY p)ᶜ ∧ IsSkeletal (ordX p)ᶜ ∧ IsClosed (ordY p)ᶜ ∧ IsClosed (ordX p)ᶜ ∧
      interior (ordY p)ᶜ = ∅ ∧ interior (ordX p)ᶜ = ∅ := by
  have h1 : IsSkeletal (ordY p)ᶜ := isSkeletal_compl_iff.2 hp.isPortly_ordY
  have h2 : IsSkeletal (ordX p)ᶜ := isSkeletal_compl_iff.2 hp.isPortly_ordX
  exact ⟨h1, h2, h1.isClosed, h2.isClosed, h1.interior_eq_empty, h2.interior_eq_empty⟩

/-- `rem:ordinary_part_branched_covering`. -/
theorem IsBranchedCovering.ordinary_part {p : X → Y} (hp : IsBranchedCovering p) :
    IsCoveringMap ((ordY p).restrictPreimage p) ∧
      Surjective ((ordY p).restrictPreimage p) ∧ IsConnected (ordX p) ∧ IsConnected (ordY p) := by
  haveI := hp.isSpread.locallyConnectedSpace
  haveI := hp.connectedSpace_source
  haveI := hp.connectedSpace_target
  exact ⟨isCoveringMap_restrict_ordX hp.isSpread.continuous, surjective_restrict_ordX,
    hp.isPortly_ordX.isConnected, hp.isPortly_ordY.isConnected⟩

/-- `lem:portly_preimage_branched`. -/
theorem IsBranchedCovering.isPortly_preimage {p : X → Y} (hp : IsBranchedCovering p) {U : Set Y}
    (hU : IsPortly U) : IsPortly (p ⁻¹' U) := by
  haveI := hp.isSpread.locallyConnectedSpace
  have hc := hp.isSpread.continuous
  haveI : LocallyConnectedSpace (p ⁻¹' ordY p) := (isOpen_ordX hc).locallyConnectedSpace
  have hf : IsLocalHomeomorph (Subtype.val ∘ (ordY p).restrictPreimage p) :=
    (isOpen_ordY.isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
      (isCoveringMap_restrict_ordX hc).isLocalHomeomorph
  have h1 : IsPortly (((↑) : ordX p → X) ⁻¹' (p ⁻¹' U)) := hU.preimage_of_isLocalHomeomorph hf
  have h2 := h1.trans hp.isPortly_ordX
  rw [Subtype.image_preimage_coe] at h2
  exact h2.mono inter_subset_right (hU.isOpen.preimage hc)

/-! ### Lifting conditions -/

/-- Item (iv) of `lem:complete_path_carac`. -/
def PathLiftExtends (p : X → Y) (X₁ : Set X) (Y₁ : Set Y) : Prop :=
  ∀ γ : C(I, Y), (∀ t : I, t < 1 → γ t ∈ Y₁) → ∀ f : I → X, ContinuousOn f {t | t < 1} →
    (∀ t : I, t < 1 → f t ∈ X₁) → (∀ t : I, t < 1 → p (f t) = γ t) →
    ∃ g : C(I, X), (∀ t, p (g t) = γ t) ∧ ∀ t : I, t < 1 → g t = f t

universe w in
/-- Item (iii) of `lem:complete_path_carac`. -/
def HomotopyLiftExtends (p : X → Y) (X₁ : Set X) (Y₁ : Set Y) : Prop :=
  ∀ (Q : Type w) [TopologicalSpace Q] [T2Space Q] [LocallyConnectedSpace Q] (H : C(Q × I, Y)),
    (∀ z : Q × I, z.2 < 1 → H z ∈ Y₁) → ∀ F : Q × I → X, ContinuousOn F {z | z.2 < 1} →
    (∀ z : Q × I, z.2 < 1 → F z ∈ X₁) → (∀ z : Q × I, z.2 < 1 → p (F z) = H z) →
    ∃ G : C(Q × I, X), (∀ z, p (G z) = H z) ∧ ∀ z : Q × I, z.2 < 1 → G z = F z

/-! ### Facts about the unit interval -/

theorem dense_setOf_lt_one : Dense {t : I | t < 1} := by
  intro x
  have h : (Iio (1 : I)).Nonempty := ⟨0, mem_Iio.2 zero_lt_one⟩
  rw [show {t : I | t < 1} = Iio 1 from rfl, closure_Iio' h]
  exact le_one x

theorem eq_one_of_not_lt_one {t : I} (h : ¬ t < 1) : t = 1 :=
  le_antisymm (le_one t) (not_lt.1 h)

/-! ### Fox's extension property of complete spreads ("corollary of the extension theorem") -/

section Fox

variable {Q : Type*} [TopologicalSpace Q]

/-- Data witnessing that `H` maps a neighbourhood `N × (l, 1]` of `(q, 1)` into `U`, with `N` open
and preconnected. -/
def FoxGood (H : C(Q × I, Y)) (q : Q) (U : Set Y) (N : Set Q) (l : I) : Prop :=
  IsOpen N ∧ IsPreconnected N ∧ q ∈ N ∧ l < 1 ∧ ∀ q' ∈ N, ∀ t : I, l < t → H (q', t) ∈ U

theorem foxGood_exists [LocallyConnectedSpace Q] (H : C(Q × I, Y)) (q : Q) {U : Set Y}
    (hU : IsOpen U) (hq : H (q, 1) ∈ U) : ∃ N l, FoxGood H q U N l := by
  have hmem : H ⁻¹' U ∈ 𝓝 (q, (1 : I)) := (hU.preimage H.continuous).mem_nhds hq
  obtain ⟨N₀, hN₀, T, hT, hNT⟩ := mem_nhds_prod_iff.1 hmem
  obtain ⟨l, hl, hlT⟩ := exists_Ioc_subset_of_mem_nhds hT ⟨0, zero_lt_one⟩
  obtain ⟨O, hON, hO, hqO⟩ := mem_nhds_iff.1 hN₀
  exact ⟨connectedComponentIn O q, l, hO.connectedComponentIn,
    isPreconnected_connectedComponentIn, mem_connectedComponentIn hqO, hl,
    fun q' hq' t ht => hNT ⟨hON (connectedComponentIn_subset _ _ hq'), hlT ⟨ht, le_one t⟩⟩⟩

variable {p : X → Y} {H : C(Q × I, Y)} {F : Q × I → X}

/-- All points of a tail `F(N × (l, 1))` lie in one component of `p⁻¹(U)`. -/
theorem foxGood_tail (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) {q : Q} {U : Set Y} {N : Set Q} {l : I}
    (hg : FoxGood H q U N l) {q₁ q₂ : Q} (h₁ : q₁ ∈ N) (h₂ : q₂ ∈ N) {t₁ t₂ : I} (ht₁ : l < t₁)
    (ht₁' : t₁ < 1) (ht₂ : l < t₂) (ht₂' : t₂ < 1) :
    F (q₁, t₁) ∈ connectedComponentIn (p ⁻¹' U) (F (q₂, t₂)) := by
  have hS : IsPreconnected (F '' (N ×ˢ Ioo l 1)) :=
    (hg.2.1.prod isPreconnected_Ioo).image _ (hF.mono fun z hz => hz.2.2)
  have hSU : F '' (N ×ˢ Ioo l 1) ⊆ p ⁻¹' U := by
    rintro _ ⟨z, hz, rfl⟩
    show p (F z) ∈ U
    rw [hFH z hz.2.2]
    exact hg.2.2.2.2 z.1 hz.1 z.2 hz.2.1
  exact hS.subset_connectedComponentIn ⟨(q₂, t₂), ⟨h₂, ht₂, ht₂'⟩, rfl⟩ hSU
    ⟨(q₁, t₁), ⟨h₁, ht₁, ht₁'⟩, rfl⟩

theorem foxTime_exists [LocallyConnectedSpace Q] (H : C(Q × I, Y)) (q : Q) {U : Set Y}
    (hU : IsCNbhd (H (q, 1)) U) : ∃ t : I, t < 1 ∧ ∃ N l, FoxGood H q U N l ∧ l < t := by
  obtain ⟨N, l, hg⟩ := foxGood_exists H q hU.1 hU.2.2
  obtain ⟨t, hlt, ht1⟩ := exists_between hg.2.2.2.1
  exact ⟨t, ht1, N, l, hg, hlt⟩

/-- A time `t < 1` at which the component of `F(q, t)` in `p⁻¹(U)` is the one chosen by the end. -/
def foxTime [LocallyConnectedSpace Q] (H : C(Q × I, Y)) (q : Q) {U : Set Y}
    (hU : IsCNbhd (H (q, 1)) U) : I :=
  (foxTime_exists H q hU).choose

theorem foxTime_spec [LocallyConnectedSpace Q] (H : C(Q × I, Y)) (q : Q) {U : Set Y}
    (hU : IsCNbhd (H (q, 1)) U) :
    foxTime H q hU < 1 ∧ ∃ N l, FoxGood H q U N l ∧ l < foxTime H q hU :=
  (foxTime_exists H q hU).choose_spec

/-- The key property: every point of a good tail lies in the chosen component. -/
theorem mem_foxComp [LocallyConnectedSpace Q] (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) {q : Q} {U : Set Y} {N : Set Q} {l : I}
    (hg : FoxGood H q U N l) (hU : IsCNbhd (H (q, 1)) U) {q' : Q} (hq' : q' ∈ N) {t' : I}
    (ht' : l < t') (ht'1 : t' < 1) :
    F (q', t') ∈ connectedComponentIn (p ⁻¹' U) (F (q, foxTime H q hU)) := by
  obtain ⟨hτ1, N', l', hg', hl'τ⟩ := foxTime_spec H q hU
  set τ := foxTime H q hU
  have hm1 : max t' τ < 1 := max_lt ht'1 hτ1
  have h1 : F (q', t') ∈ connectedComponentIn (p ⁻¹' U) (F (q, max t' τ)) :=
    foxGood_tail hF hFH hg hq' hg.2.2.1 ht' ht'1 (lt_of_lt_of_le ht' (le_max_left _ _)) hm1
  have h2 : F (q, max t' τ) ∈ connectedComponentIn (p ⁻¹' U) (F (q, τ)) :=
    foxGood_tail hF hFH hg' hg'.2.2.1 hg'.2.2.1 (lt_of_lt_of_le hl'τ (le_max_right _ _)) hm1
      hl'τ hτ1
  rw [connectedComponentIn_eq h2]
  exact h1

/-- The end of `p` at `H(q, 1)` determined by the partial lift `F`. -/
def foxEnd [LocallyConnectedSpace Q] (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) (q : Q) : SpreadEnd p where
  base := H (q, 1)
  toFun U := if hU : IsCNbhd (H (q, 1)) U then
      connectedComponentIn (p ⁻¹' U) (F (q, foxTime H q hU)) else ∅
  isCompOf U hU := by
    rw [dif_pos hU]
    obtain ⟨hτ1, N, l, hg, hlτ⟩ := foxTime_spec H q hU
    refine isCompOf_connectedComponentIn ?_
    rw [hFH _ hτ1]
    exact hg.2.2.2.2 q hg.2.2.1 _ hlτ
  mono U V hU hV hUV := by
    rw [dif_pos hU, dif_pos hV]
    obtain ⟨hτU, NU, lU, hgU, hlU⟩ := foxTime_spec H q hU
    obtain ⟨hτV, NV, lV, hgV, hlV⟩ := foxTime_spec H q hV
    set m := max (foxTime H q hU) (foxTime H q hV)
    have hm1 : m < 1 := max_lt hτU hτV
    have h1 := mem_foxComp hF hFH hgU hU hgU.2.2.1 (lt_of_lt_of_le hlU (le_max_left _ _)) hm1
    have h2 := mem_foxComp hF hFH hgV hV hgV.2.2.1 (lt_of_lt_of_le hlV (le_max_right _ _)) hm1
    rw [connectedComponentIn_eq h1, connectedComponentIn_eq h2]
    exact connectedComponentIn_mono _ (preimage_mono hUV)
  eq_empty U hU := dif_neg hU

theorem foxEnd_apply [LocallyConnectedSpace Q] (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) (q : Q) {U : Set Y}
    (hU : IsCNbhd (H (q, 1)) U) :
    foxEnd hF hFH q U = connectedComponentIn (p ⁻¹' U) (F (q, foxTime H q hU)) :=
  dif_pos hU

theorem mem_foxEnd [LocallyConnectedSpace Q] (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) {q : Q} {U : Set Y} {N : Set Q} {l : I}
    (hg : FoxGood H q U N l) (hU : IsCNbhd (H (q, 1)) U) {q' : Q} (hq' : q' ∈ N) {t' : I}
    (ht' : l < t') (ht'1 : t' < 1) : F (q', t') ∈ foxEnd hF hFH q U := by
  rw [foxEnd_apply hF hFH q hU]
  exact mem_foxComp hF hFH hg hU hq' ht' ht'1

/-- **Fox's extension property** ("corollary of the extension theorem", `MR0123298`), the
homotopy form used in `lem:complete_path_carac` (ii) ⇒ (iii): for a complete spread `p` over a
T1 locally connected base and a locally connected `Q`, every partial lift `F` on `Q × [0,1)` of a
homotopy `H : Q × [0,1] → Y` extends continuously to a lift on `Q × [0,1]`. -/
theorem exists_extend_of_isCompleteSpread [LocallyConnectedSpace Q] [T1Space Y]
    [LocallyConnectedSpace Y] (hp : IsSpread p) (hc : IsCompleteSpread p) (H : C(Q × I, Y))
    (F : Q × I → X) (hF : ContinuousOn F {z | z.2 < 1})
    (hFH : ∀ z : Q × I, z.2 < 1 → p (F z) = H z) :
    ∃ G : C(Q × I, X), (∀ z, p (G z) = H z) ∧ ∀ z : Q × I, z.2 < 1 → G z = F z := by
  set e : Q → SpreadEnd p := foxEnd hF hFH with he
  have hx : ∀ q, ∃ x, ∀ U, IsCNbhd (e q).base U → x ∈ e q U := fun q =>
    isCompleteSpread_iff.1 hc (e q)
  choose x hx using hx
  have hpx : ∀ q, p (x q) = H (q, 1) := fun q =>
    eq_of_forall_isCNbhd fun U hU => (e q).subset_preimage hU (hx q U hU)
  set G : Q × I → X := fun z => if z.2 < 1 then F z else x z.1 with hGdef
  have hG : ∀ z, p (G z) = H z := by
    rintro ⟨q, t⟩
    by_cases ht : t < 1
    · simp only [hGdef, if_pos ht]; exact hFH _ ht
    · obtain rfl := eq_one_of_not_lt_one ht
      simp only [hGdef, if_neg ht]; exact hpx q
  refine ⟨⟨G, ?_⟩, hG, fun z hz => if_pos hz⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨q, t⟩
  by_cases ht : t < 1
  · have ho : IsOpen {z : Q × I | z.2 < 1} := isOpen_lt continuous_snd continuous_const
    have hev : G =ᶠ[𝓝 (q, t)] F := eventually_of_mem (ho.mem_nhds ht) fun w hw => if_pos hw
    exact (hF.continuousAt (ho.mem_nhds ht)).congr hev.symm
  obtain rfl := eq_one_of_not_lt_one ht
  rw [ContinuousAt, (nhds_basis_opens (G (q, 1))).tendsto_right_iff]
  rintro O ⟨hxO, hO⟩
  have hGq : G (q, 1) = x q := if_neg (lt_irrefl _)
  rw [hGq] at hxO
  obtain ⟨U₀, hU₀, hxU₀, hsub⟩ := (isSpread_iff.1 hp).2.2 (x q) O hO hxO
  rw [hpx q] at hxU₀
  set U := connectedComponentIn U₀ (H (q, 1))
  have hU : IsCNbhd (H (q, 1)) U :=
    ⟨hU₀.connectedComponentIn, isPreconnected_connectedComponentIn, mem_connectedComponentIn hxU₀⟩
  have heU : e q U ⊆ O := by
    rw [((e q).isCompOf U hU).eq_of_mem (hx q U hU)]
    exact (connectedComponentIn_mono _ (preimage_mono (connectedComponentIn_subset _ _))).trans hsub
  obtain ⟨N, l, hg⟩ := foxGood_exists H q hU.1 hU.2.2
  have hnhds : N ×ˢ Ioi l ∈ 𝓝 (q, (1 : I)) :=
    prod_mem_nhds (hg.1.mem_nhds hg.2.2.1) (isOpen_Ioi.mem_nhds hg.2.2.2.1)
  filter_upwards [hnhds]
  rintro ⟨q', t'⟩ ⟨hq', ht'⟩
  apply heU
  by_cases ht1 : t' < 1
  · show (if t' < 1 then F (q', t') else x q') ∈ e q U
    rw [if_pos ht1]
    exact mem_foxEnd hF hFH hg hU hq' ht' ht1
  · show (if t' < 1 then F (q', t') else x q') ∈ e q U
    rw [if_neg ht1]
    have hU' : IsCNbhd (H (q', 1)) U := ⟨hU.1, hU.2.1, hg.2.2.2.2 q' hq' 1 hg.2.2.2.1⟩
    have hg' : FoxGood H q' U N l := ⟨hg.1, hg.2.1, hq', hg.2.2.2.1, hg.2.2.2.2⟩
    obtain ⟨t'', hlt, ht''⟩ := exists_between hg.2.2.2.1
    have h1 : F (q', t'') ∈ e q U := mem_foxEnd hF hFH hg hU hq' hlt ht''
    have h2 : F (q', t'') ∈ e q' U := mem_foxEnd hF hFH hg' hU' hq' hlt ht''
    have := ((e q').isCompOf U hU').eq_of_meets ((e q).isCompOf U hU) ⟨_, h2, h1⟩
    rw [← this]
    exact hx q' U hU'

end Fox

/-- Fox's extension property, path form (`lem:complete_path_carac` (ii) ⇒ (iv)): for a complete
spread over a T1 locally connected base, every partial lift on `[0,1)` of a path extends
continuously to a lift on `[0,1]`. -/
theorem exists_extend_path_of_isCompleteSpread [T1Space Y] [LocallyConnectedSpace Y]
    {p : X → Y} (hp : IsSpread p) (hc : IsCompleteSpread p) (γ : C(I, Y)) (f : I → X)
    (hf : ContinuousOn f {t | t < 1}) (hfγ : ∀ t : I, t < 1 → p (f t) = γ t) :
    ∃ g : C(I, X), (∀ t, p (g t) = γ t) ∧ ∀ t : I, t < 1 → g t = f t := by
  obtain ⟨G, hG, hGF⟩ := exists_extend_of_isCompleteSpread (Q := Unit) hp hc
    (γ.comp ⟨Prod.snd, continuous_snd⟩) (fun z => f z.2)
    (hf.comp continuous_snd.continuousOn fun z hz => hz) (fun z hz => hfγ z.2 hz)
  exact ⟨G.comp ⟨fun t => ((), t), by fun_prop⟩, fun t => hG _, fun t ht => hGF _ ht⟩

/-! ### Lifting paths on `[0,1)` through a covering -/

/-- A path whose restriction to `[0,1)` lies in `s`, over which `p` restricts to a covering map,
lifts on `[0,1)` from any point over its origin. -/
theorem exists_partial_lift {p : X → Y} {s : Set Y} (cov : IsCoveringMap (s.restrictPreimage p))
    (γ : C(I, Y)) (hγ : ∀ t : I, t < 1 → γ t ∈ s) {e : X} (he : p e ∈ s) (h0 : p e = γ 0) :
    ∃ f : I → X, ContinuousOn f {t | t < 1} ∧ f 0 = e ∧
      ∀ t : I, t < 1 → f t ∈ p ⁻¹' s ∧ p (f t) = γ t := by
  set A : Set I := {t | t < 1}
  let H : C(I × A, s) := ⟨fun z => ⟨γ (z.1 * z.2), hγ _ (lt_of_le_of_lt mul_le_right z.2.2)⟩,
    (γ.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
  have H_0 : ∀ a, H (0, a) = s.restrictPreimage p (ContinuousMap.const A (⟨e, he⟩ : p ⁻¹' s) a) :=
    fun a => Subtype.ext (by simp [H, h0])
  set Γ := cov.liftHomotopy H _ H_0
  have hΓ : ∀ z, p (Γ z) = γ (z.1 * z.2) := fun z =>
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H _ H_0) z)
  set f : I → X := fun t => if h : t < 1 then (Γ (1, ⟨t, h⟩) : X) else e with hfdef
  have hfA : ∀ (t : I) (h : t < 1), f t = Γ (1, ⟨t, h⟩) := fun t h => dif_pos h
  have h00 : (0 : I) < 1 := zero_lt_one
  refine ⟨f, ?_, ?_, fun t ht => ⟨by rw [hfA t ht]; exact (Γ _).2, by rw [hfA t ht, hΓ]; simp⟩⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : A.restrict f = fun a => (Γ (1, a) : X) := funext fun a => hfA a a.2
    rw [this]
    exact continuous_subtype_val.comp (Γ.continuous.comp (continuous_const.prodMk continuous_id))
  · rw [hfA 0 h00]
    have hconst : (fun t : I => Γ (t, ⟨0, h00⟩)) = fun _ => (⟨e, he⟩ : p ⁻¹' s) := by
      refine cov.eq_of_comp_eq (Γ.continuous.comp (continuous_id.prodMk continuous_const))
        continuous_const (funext fun t => Subtype.ext ?_) 0 ?_
      · show p (Γ (t, ⟨0, h00⟩)) = p e
        rw [hΓ]; simp [h0]
      · exact cov.liftHomotopy_zero H _ H_0 _
    exact congrArg Subtype.val (congrFun hconst 1)

/-! ### The path criterion for completeness -/

/-- The core of `lem:complete_path_carac` (iv) ⇒ (ii): a spread with preconnected locally
path-connected T0 source, over a T2 locally connected first countable base, which is ordinary
over an open `Y₁` with portly preimage and has the path-extension property (iv) over `Y₁`, is
complete. The proof is the paper's: path lifting in the Fox completion. -/
theorem isCompleteSpread_of_pathLiftExtends [T0Space X] [LocPathConnectedSpace X]
    [PreconnectedSpace X] [T2Space Y] [LocallyConnectedSpace Y] [FirstCountableTopology Y]
    {p : X → Y} (hp : IsSpread p) {Y₁ : Set Y} (hY₁ : IsOpen Y₁) (hY₁ord : Y₁ ⊆ ordY p)
    (hX₁ : IsPortly (p ⁻¹' Y₁)) (h : PathLiftExtends p (p ⁻¹' Y₁) Y₁) : IsCompleteSpread p := by
  haveI := SpreadEnd.locPathConnectedSpace hp
  set ι := SpreadEnd.ofPoint p
  have hιc : Continuous ι := SpreadEnd.continuous_ofPoint hp
  have hιe : IsEmbedding ι := SpreadEnd.isEmbedding_ofPoint hp
  haveI : PreconnectedSpace (SpreadEnd p) := ⟨by
    have := (isPreconnected_range hιc).closure
    rwa [SpreadEnd.denseRange_ofPoint.closure_range] at this⟩
  set P := ι '' (p ⁻¹' Y₁) with hPdef
  have hP : P = SpreadEnd.base ⁻¹' Y₁ := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro he
      obtain ⟨U, hU, heU, -, hcov⟩ := hY₁ord he
      obtain ⟨x, hx⟩ := e.exists_mem_of_isEvenlyCoveredSet hU heU hcov
      have hxe := (SpreadEnd.eq_ofPoint_iff e x).2 hx
      refine ⟨x, ?_, hxe⟩
      have hb : p x = e.base := congrArg SpreadEnd.base hxe
      show p x ∈ Y₁
      rw [hb]; exact he
  have hPp : IsPortly P := by
    refine ⟨hP ▸ hY₁.preimage SpreadEnd.continuous_base,
      SpreadEnd.denseRange_ofPoint.dense_image hιc hX₁.dense, fun O hO hOc => ?_⟩
    have h1 : IsPreconnected (ι ⁻¹' O) := by
      rw [← hιe.isInducing.isPreconnected_image, image_preimage_eq_inter_range]
      exact SpreadEnd.isLocallyConnectedIn_range_ofPoint hp O hO hOc
    have h2 := hX₁.locallyConnectedIn _ (hO.preimage hιc) h1
    have h3 := h2.image ι hιc.continuousOn
    rw [inter_comm, image_inter_preimage, ← hPdef, inter_comm] at h3
    exact h3
  rw [isCompleteSpread_iff]
  intro e
  haveI : Nonempty (SpreadEnd p) := ⟨e⟩
  obtain ⟨_, x₀, hx₀, rfl⟩ := hPp.dense.nonempty
  haveI : Nonempty X := ⟨x₀⟩
  obtain ⟨γh, hγh⟩ := path_covering hPp (b := e) ⟨x₀, hx₀, rfl⟩
  set γ : C(I, Y) := ⟨fun t => (γh t).base, SpreadEnd.continuous_base.comp γh.continuous⟩
  set f : I → X := fun t => Function.invFun ι (γh t)
  have hιf : ∀ t : I, t < 1 → ι (f t) = γh t := fun t ht => by
    obtain ⟨y, -, hy⟩ := hγh t ht
    exact Function.invFun_eq ⟨y, hy⟩
  have hf : ContinuousOn f {t | t < 1} := by
    rw [hιe.isInducing.continuousOn_iff]
    exact γh.continuous.continuousOn.congr fun t ht => hιf t ht
  have hpf : ∀ t : I, t < 1 → p (f t) = γ t := fun t ht => by
    show p (f t) = (γh t).base
    rw [← hιf t ht, SpreadEnd.ofPoint_base]
  have hγ : ∀ t : I, t < 1 → γ t ∈ Y₁ := fun t ht => by
    have := hγh t ht
    rw [hP] at this
    exact this
  obtain ⟨g, -, hgf⟩ := h γ hγ f hf (fun t ht => by
    show p (f t) ∈ Y₁
    rw [hpf t ht]; exact hγ t ht) hpf
  have hext : (fun t => ι (g t)) = γh :=
    Continuous.ext_on dense_setOf_lt_one (hιc.comp g.continuous) γh.continuous fun t ht => by
      show ι (g t) = γh t
      rw [hgf t ht, hιf t ht]
  refine ⟨g 1, (SpreadEnd.eq_ofPoint_iff e (g 1)).1 ?_⟩
  exact (congrFun hext 1).trans γh.target

/-! ### `lem:complete_path_carac` -/

universe w in
/-- **`lem:complete_path_carac`** (`RamcovGX.tex:1014`). Let `p : X → Y` be a spread with `X`
connected, inducing a covering `X₁ → Y₁` (a surjective covering map, DEC-40) for portly `X₁ ⊆ X`
and `Y₁ ⊆ Y`. Then the following are equivalent: (i) `p` is a branched covering; (ii) `p` is a
complete spread; (iii) partial lifts on `Q × [0,1)` of homotopies extend (`Q` Hausdorff, locally
connected); (iv) partial lifts on `[0,1)` of paths extend. -/
theorem complete_path_carac [T2Space X] [LocPathConnectedSpace X] [ConnectedSpace X]
    [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] {p : X → Y}
    (hp : IsSpread p) {X₁ : Set X} {Y₁ : Set Y} (hX₁ : IsPortly X₁) (hY₁ : IsPortly Y₁)
    (hmaps : MapsTo p X₁ Y₁) (hcov : IsCoveringMap (hmaps.restrict p X₁ Y₁))
    (hsurj : Surjective (hmaps.restrict p X₁ Y₁)) :
    List.TFAE [IsBranchedCovering p, IsCompleteSpread p, HomotopyLiftExtends.{w} p X₁ Y₁,
      PathLiftExtends p X₁ Y₁] := by
  obtain ⟨hY₁ord, hX₁ord, hpre⟩ :=
    spread_partial_covering hp.continuous hX₁ hY₁.isOpen hmaps hcov hsurj
  tfae_have 1 → 2 := fun h => h.isComplete
  tfae_have 2 → 3 := by
    intro hc Q _ _ _ H _ F hF _ hFH
    exact exists_extend_of_isCompleteSpread hp hc H F hF hFH
  tfae_have 3 → 4 := by
    intro h γ hγ f hf hfX hfγ
    obtain ⟨G, hG, hGF⟩ := h PUnit.{w + 1} (γ.comp ⟨Prod.snd, continuous_snd⟩)
      (fun z hz => hγ z.2 hz) (fun z => f z.2) (hf.comp continuous_snd.continuousOn fun z hz => hz)
      (fun z hz => hfX z.2 hz) (fun z hz => hfγ z.2 hz)
    exact ⟨G.comp ⟨fun t => (PUnit.unit, t), by fun_prop⟩, fun t => hG _, fun t ht => hGF _ ht⟩
  tfae_have 4 → 1 := by
    intro h
    have hX₁' : IsPortly (p ⁻¹' Y₁) := by rw [hpre]; exact hX₁
    have h' : PathLiftExtends p (p ⁻¹' Y₁) Y₁ := by rw [hpre]; exact h
    have hc : IsCompleteSpread p := isCompleteSpread_of_pathLiftExtends hp hY₁.isOpen hY₁ord hX₁' h'
    obtain ⟨x₀, hx₀⟩ := hX₁.dense.nonempty
    have hrange : Dense (range p) := hY₁.dense.mono (hY₁ord.trans ordY_subset_range)
    haveI : PreconnectedSpace Y := ⟨by
      have := (isPreconnected_range hp.continuous).closure
      rwa [hrange.closure_eq] at this⟩
    haveI : ConnectedSpace Y := ⟨⟨p x₀⟩⟩
    have hsurjp : Surjective p := by
      intro y
      obtain ⟨γ, hγ⟩ := path_covering hY₁ (b := y) (hmaps hx₀)
      obtain ⟨f, hf, -, hfs⟩ := exists_partial_lift (isCoveringMap_restrict_ordX hp.continuous)
        γ (fun t ht => hY₁ord (hγ t ht)) (hY₁ord (hmaps hx₀)) γ.source.symm
      obtain ⟨g, hg, -⟩ := h γ (fun t ht => hγ t ht) f hf (fun t ht => by
        rw [← hpre]; show p (f t) ∈ Y₁; rw [(hfs t ht).2]; exact hγ t ht)
        (fun t ht => (hfs t ht).2)
      exact ⟨g 1, by rw [hg]; exact γ.target⟩
    exact ⟨hp, hc, hsurjp, inferInstance, inferInstance,
      hX₁.mono hX₁ord (isOpen_ordX hp.continuous), hY₁.mono hY₁ord isOpen_ordY⟩
  tfae_finish

/-! ### Restrictions of spreads and of evenly covered sets -/

/-- The (co)restriction of a spread to any locally connected `A ⊆ X` is a spread (the strict
library's `IsSpread.restrict` asks `A` open). -/
theorem IsSpread.restrict_of_locallyConnectedSpace {p : X → Y} (hp : IsSpread p) {A : Set X}
    {B : Set Y} [LocallyConnectedSpace A] (h : MapsTo p A B) : IsSpread (h.restrict p A B) := by
  have hc : Continuous (h.restrict p A B) := hp.continuous.restrict h
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hc, ?_⟩
  intro x O hO hxO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
  obtain ⟨W, hW, hxW, hWO⟩ := (isSpread_iff.1 hp).2.2 x O' hO' hxO
  have hxW' : x ∈ h.restrict p A B ⁻¹' ((↑) ⁻¹' W) := hxW
  refine ⟨(↑) ⁻¹' W, hW.preimage continuous_subtype_val, hxW', ?_⟩
  intro z hz
  have hsub : (↑) '' connectedComponentIn (h.restrict p A B ⁻¹' ((↑) ⁻¹' W)) x ⊆
      connectedComponentIn (p ⁻¹' W) (x : X) := by
    refine (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxW', rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact (connectedComponentIn_subset (h.restrict p A B ⁻¹' ((↑) ⁻¹' W)) x hw :)
  exact hWO (hsub ⟨z, hz, rfl⟩)

/-- Over a sheet `C ≅ W` with `W` open, `p` maps relatively open subsets of `C` to open sets. -/
theorem isOpen_image_inter_of_homeomorph {p : X → Y} {C : Set X} {W : Set Y} (hW : IsOpen W)
    (e : C ≃ₜ W) (he : ∀ z, (e z : Y) = p z) {O : Set X} (hO : IsOpen O) :
    IsOpen (p '' (O ∩ C)) := by
  have : p '' (O ∩ C) = (↑) '' (e '' ((↑) ⁻¹' O)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxO, hxC⟩, rfl⟩
      exact ⟨e ⟨x, hxC⟩, ⟨⟨x, hxC⟩, hxO, rfl⟩, he _⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨hz, z.2⟩, (he z).symm⟩
  rw [this]
  exact hW.isOpenMap_subtype_val _ (e.isOpenMap _ (hO.preimage continuous_subtype_val))

/-- An open preconnected subset of an open evenly covered set is evenly covered. -/
theorem IsEvenlyCoveredSet.mono_of_isPreconnected [LocallyConnectedSpace X] {p : X → Y}
    (hp : Continuous p) {W W' : Set Y} (hcov : IsEvenlyCoveredSet p W) (hW : IsOpen W)
    (hW' : IsOpen W') (hW'c : IsPreconnected W') (hWW' : W' ⊆ W) :
    IsEvenlyCoveredSet p W' := by
  intro x hx
  obtain ⟨e, he⟩ := hcov x (hWW' hx)
  have hC'C : connectedComponentIn (p ⁻¹' W') x ⊆ connectedComponentIn (p ⁻¹' W) x :=
    connectedComponentIn_mono _ (preimage_mono hWW')
  have hset : connectedComponentIn (p ⁻¹' W) x ∩ p ⁻¹' W' = (↑) '' (e ⁻¹' ((↑) ⁻¹' W')) := by
    ext z
    constructor
    · rintro ⟨hzC, hzW'⟩
      refine ⟨⟨z, hzC⟩, ?_, rfl⟩
      show ((e ⟨z, hzC⟩ : W) : Y) ∈ W'
      rw [he]; exact hzW'
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      show p z ∈ W'
      rw [← he]; exact hz
  have hpre : IsPreconnected (connectedComponentIn (p ⁻¹' W) x ∩ p ⁻¹' W') := by
    have hA : IsPreconnected ((↑) ⁻¹' W' : Set W) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.2 hWW']
      exact hW'c
    rw [hset, ← e.image_symm]
    exact (hA.image _ e.symm.continuous.continuousOn).image _ continuous_subtype_val.continuousOn
  have hCC' : connectedComponentIn (p ⁻¹' W) x ∩ p ⁻¹' W' ⊆ connectedComponentIn (p ⁻¹' W') x :=
    hpre.subset_connectedComponentIn ⟨mem_connectedComponentIn (hWW' hx), hx⟩ inter_subset_right
  have hinjC : InjOn p (connectedComponentIn (p ⁻¹' W) x) := hcov.injOn (hWW' hx)
  refine exists_homeomorph_of_sheet hp (hW'.preimage hp).connectedComponentIn (hinjC.mono hC'C)
    ?_ ?_
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact connectedComponentIn_subset (p ⁻¹' W') x hz
    · intro y hy
      refine ⟨e.symm ⟨y, hWW' hy⟩, hCC' ⟨(e.symm _).2, ?_⟩, ?_⟩
      · show p _ ∈ W'
        rw [← he, e.apply_symm_apply]; exact hy
      · rw [← he, e.apply_symm_apply]
  · intro O hOC' hO
    have : p '' O = p '' (O ∩ connectedComponentIn (p ⁻¹' W) x) := by
      rw [inter_eq_left.2 (hOC'.trans hC'C)]
    rw [this]
    exact isOpen_image_inter_of_homeomorph hW e he hO

/-- An open evenly covered set `W` stays evenly covered for the (co)restriction to a locally
connected `A`, provided the components of `p⁻¹(W)` meeting `A` lie in `A`. -/
theorem IsEvenlyCoveredSet.restrict {p : X → Y} (hp : Continuous p) {A : Set X} {B : Set Y}
    [LocallyConnectedSpace A] (h : MapsTo p A B) {W : Set Y} (hW : IsOpen W)
    (hcov : IsEvenlyCoveredSet p W)
    (hsat : ∀ a : A, p a ∈ W → connectedComponentIn (p ⁻¹' W) a ⊆ A) :
    IsEvenlyCoveredSet (h.restrict p A B) ((↑) ⁻¹' W) := by
  have hq : Continuous (h.restrict p A B) := hp.restrict h
  intro a ha
  have ha' : p a ∈ W := ha
  obtain ⟨e, he⟩ := hcov a ha'
  have himgsub : (↑) '' connectedComponentIn (h.restrict p A B ⁻¹' ((↑) ⁻¹' W)) a ⊆
      connectedComponentIn (p ⁻¹' W) (a : X) :=
    (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponentIn ha, rfl⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact (connectedComponentIn_subset _ _ hz :))
  have hCA : connectedComponentIn (p ⁻¹' W) (a : X) ⊆ A := hsat a ha'
  have hCsub : ∀ x ∈ connectedComponentIn (p ⁻¹' W) (a : X),
      ∃ z ∈ connectedComponentIn (h.restrict p A B ⁻¹' ((↑) ⁻¹' W)) a, (z : X) = x := by
    have hpre : IsPreconnected (((↑) : A → X) ⁻¹' connectedComponentIn (p ⁻¹' W) (a : X)) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.2 hCA]
      exact isPreconnected_connectedComponentIn
    have hsub := hpre.subset_connectedComponentIn (mem_connectedComponentIn ha')
      (fun z hz => connectedComponentIn_subset (p ⁻¹' W) (a : X) hz)
    intro x hx
    exact ⟨⟨x, hCA hx⟩, hsub hx, rfl⟩
  have hinj : InjOn p (connectedComponentIn (p ⁻¹' W) (a : X)) := hcov.injOn ha'
  refine exists_homeomorph_of_sheet hq
    ((hW.preimage continuous_subtype_val).preimage hq).connectedComponentIn ?_ ?_ ?_
  · intro z₁ hz₁ z₂ hz₂ hz
    exact Subtype.ext (hinj (himgsub ⟨z₁, hz₁, rfl⟩) (himgsub ⟨z₂, hz₂, rfl⟩)
      (congrArg Subtype.val hz))
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset (h.restrict p A B ⁻¹' ((↑) ⁻¹' W)) a hz
    · intro b hb
      obtain ⟨z, hz, hzx⟩ := hCsub _ (e.symm ⟨b, hb⟩).2
      refine ⟨z, hz, Subtype.ext ?_⟩
      show p z = b
      rw [hzx, ← he, e.apply_symm_apply]
  · intro O hOCA hO
    obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
    have himg : (↑) '' (h.restrict p A B '' ((↑) ⁻¹' O')) =
        p '' (O' ∩ connectedComponentIn (p ⁻¹' W) (a : X)) := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, ⟨hz, himgsub ⟨z, hOCA hz, rfl⟩⟩, rfl⟩
      · rintro ⟨x, ⟨hxO, hxC⟩, rfl⟩
        obtain ⟨z, -, rfl⟩ := hCsub x hxC
        exact ⟨h.restrict p A B z, ⟨z, hxO, rfl⟩, rfl⟩
    have hopen := isOpen_image_inter_of_homeomorph hW e he hO'
    rw [← himg] at hopen
    rw [← preimage_image_eq (h.restrict p A B '' ((↑) ⁻¹' O')) Subtype.val_injective]
    exact hopen.preimage continuous_subtype_val

/-- Ordinary points of `p` in an open `O ⊆ Y` stay ordinary for the (co)restriction to a locally
connected `A`, when `A` is saturated for the components of preimages of subsets of `O` and the
restriction is onto over `O`. -/
theorem subset_ordY_restrict [LocallyConnectedSpace X] [LocallyConnectedSpace Y] {p : X → Y}
    (hp : Continuous p) {A : Set X} {B : Set Y} [LocallyConnectedSpace A] (h : MapsTo p A B)
    {O : Set Y} (hO : IsOpen O)
    (hsat : ∀ W : Set Y, W ⊆ O → ∀ a : A, p a ∈ W → connectedComponentIn (p ⁻¹' W) a ⊆ A)
    (hsurj : ∀ b : B, (b : Y) ∈ O → ∃ a, h.restrict p A B a = b) :
    ((↑) : B → Y) ⁻¹' (O ∩ ordY p) ⊆ ordY (h.restrict p A B) := by
  rintro b ⟨hbO, W, hW, hbW, -, hcov⟩
  have hW'o : IsOpen (connectedComponentIn (W ∩ O) (b : Y)) := (hW.inter hO).connectedComponentIn
  have hbW' : (b : Y) ∈ connectedComponentIn (W ∩ O) (b : Y) := mem_connectedComponentIn ⟨hbW, hbO⟩
  have hW'sub : connectedComponentIn (W ∩ O) (b : Y) ⊆ W ∩ O := connectedComponentIn_subset _ _
  have hcov' := hcov.mono_of_isPreconnected hp hW hW'o isPreconnected_connectedComponentIn
    (hW'sub.trans inter_subset_left)
  obtain ⟨a, ha⟩ := hsurj b hbO
  refine ⟨((↑) : B → Y) ⁻¹' connectedComponentIn (W ∩ O) (b : Y),
    hW'o.preimage continuous_subtype_val, hbW', ⟨a, show ((h.restrict p A B a : B) : Y) ∈ _ by
      rw [ha]; exact hbW'⟩, ?_⟩
  exact hcov'.restrict hp h hW'o fun a' ha' => hsat _ (hW'sub.trans inter_subset_right) a' ha'

/-- The path-extension property passes to (co)restrictions `A → B` of a complete spread, when
lifts over `B` starting in `A` stay in `A`. -/
theorem pathLiftExtends_restrict [T1Space Y] [LocallyConnectedSpace Y] {p : X → Y}
    (hp : IsSpread p) (hc : IsCompleteSpread p) {A : Set X} {B : Set Y} (h : MapsTo p A B)
    (hA : ∀ g : C(I, X), (∀ t, p (g t) ∈ B) → g 0 ∈ A → ∀ t, g t ∈ A) (A₁ : Set A)
    (B₁ : Set B) : PathLiftExtends (h.restrict p A B) A₁ B₁ := by
  intro γ _ f hf _ hfγ
  obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp hc
    (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ) (fun t => (f t : X))
    (continuous_subtype_val.comp_continuousOn hf) (fun t ht => congrArg Subtype.val (hfγ t ht))
  have hgA : ∀ t, g t ∈ A := hA g (fun t => by rw [hg]; exact (γ t).2)
    (by rw [hgf 0 zero_lt_one]; exact (f 0).2)
  exact ⟨⟨fun t => ⟨g t, hgA t⟩, g.continuous.subtype_mk _⟩, fun t => Subtype.ext (hg t),
    fun t ht => Subtype.ext (hgf t ht)⟩

/-- A portly set meets an open set in a set portly in it. -/
theorem IsPortly.preimage_val_of_isOpen {P O : Set X} (hP : IsPortly P) (hO : IsOpen O) :
    IsPortly (((↑) : O → X) ⁻¹' P) := by
  have h : ((↑) : O → X) ⁻¹' P = (↑) ⁻¹' (P ∩ O) := by
    ext z; exact ⟨fun hz => ⟨hz, z.2⟩, fun hz => hz.1⟩
  rw [h, isPortly_subtype_iff hO inter_subset_right]
  refine ⟨hP.isOpen.inter hO, ?_, fun W hW hWO hWc => ?_⟩
  · rw [inter_comm]; exact hP.dense.open_subset_closure_inter hO
  · have : W ∩ (P ∩ O) = W ∩ P := by
      ext y; exact ⟨fun hy => ⟨hy.1, hy.2.1⟩, fun hy => ⟨hy.1, hy.2, hWO hy.1⟩⟩
    rw [this]
    exact hP.locallyConnectedIn W hW hWc

/-- In a connected space, a set containing a portly subset is connected. -/
theorem IsPortly.connectedSpace_of_subset [ConnectedSpace X] {P S : Set X} (hP : IsPortly P)
    (hPS : P ⊆ S) : ConnectedSpace S :=
  isConnected_iff_connectedSpace.1 (hP.isConnected.subset_closure hPS
    (by rw [hP.dense.closure_eq]; exact subset_univ _))

/-! ### Restrictions of branched coverings -/

/-- The surjectivity half of `lem:branched_covering_restriction`: a component of the preimage of
an open connected `U` maps onto `U`. -/
theorem IsBranchedCovering.image_connectedComponentIn [T1Space Y] [LocPathConnectedSpace Y]
    [FirstCountableTopology Y] {p : X → Y} (hp : IsBranchedCovering p) {U : Set Y}
    (hU : IsOpen U) (hUc : IsPreconnected U) {x : X} (hx : p x ∈ U) :
    p '' connectedComponentIn (p ⁻¹' U) x = U := by
  haveI := hp.isSpread.locallyConnectedSpace
  have hpc := hp.isSpread.continuous
  have hVo : IsOpen (connectedComponentIn (p ⁻¹' U) x) := (hU.preimage hpc).connectedComponentIn
  refine Subset.antisymm (image_subset_iff.2 (connectedComponentIn_subset _ _)) fun u hu => ?_
  obtain ⟨x', hx'V, hx'o⟩ := hp.isPortly_ordX.dense.inter_open_nonempty _ hVo
    ⟨x, mem_connectedComponentIn hx⟩
  have hx'U : p x' ∈ U := connectedComponentIn_subset (p ⁻¹' U) x hx'V
  obtain ⟨γ, hγU, hγo⟩ := exists_path_of_isPortly_of_isOpen hp.isPortly_ordY hU hUc hx'o hx'U hu
  obtain ⟨f, hf, hf0, hfs⟩ := exists_partial_lift (isCoveringMap_restrict_ordX hpc) γ
    (fun t ht => hγo t ht) hx'o γ.source.symm
  obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp.isSpread hp.isComplete γ f hf
    (fun t ht => (hfs t ht).2)
  have hg0 : g 0 = x' := by rw [hgf 0 zero_lt_one, hf0]
  have hV' : connectedComponentIn (p ⁻¹' U) x = connectedComponentIn (p ⁻¹' U) x' :=
    connectedComponentIn_eq hx'V
  have hgV : range g ⊆ connectedComponentIn (p ⁻¹' U) x := by
    rw [hV']
    refine (isPreconnected_range g.continuous).subset_connectedComponentIn ⟨0, hg0⟩ ?_
    rintro _ ⟨t, rfl⟩
    show p (g t) ∈ U
    rw [hg]; exact hγU t
  exact ⟨g 1, hgV ⟨1, rfl⟩, by rw [hg]; exact γ.target⟩

/-- **`lem:branched_covering_restriction`** (`RamcovGX.tex:1041`). Let `p : X → Y` be a branched
covering, `U ⊆ Y` open connected and `V` a connected component of `p⁻¹(U)`. Then `V → U` is a
branched covering. -/
theorem branched_covering_restriction [T2Space X] [LocPathConnectedSpace X] [T2Space Y]
    [LocPathConnectedSpace Y] [FirstCountableTopology Y] {p : X → Y} (hp : IsBranchedCovering p)
    {U : Set Y} (hU : IsOpen U) (hUc : IsPreconnected U) {V : Set X} (hV : IsCompOf p U V)
    (h : MapsTo p V U) : IsBranchedCovering (h.restrict p V U) := by
  obtain ⟨x, hx, rfl⟩ := hV
  have hpc := hp.isSpread.continuous
  have hVo : IsOpen (connectedComponentIn (p ⁻¹' U) x) := (hU.preimage hpc).connectedComponentIn
  haveI : LocPathConnectedSpace (connectedComponentIn (p ⁻¹' U) x) := hVo.locPathConnectedSpace
  haveI : LocPathConnectedSpace U := hU.locPathConnectedSpace
  have hxV : x ∈ connectedComponentIn (p ⁻¹' U) x := mem_connectedComponentIn hx
  haveI : ConnectedSpace (connectedComponentIn (p ⁻¹' U) x) :=
    isConnected_iff_connectedSpace.1 ⟨⟨x, hxV⟩, isPreconnected_connectedComponentIn⟩
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.1 ⟨⟨p x, hx⟩, hUc⟩
  have hsat : ∀ S : Set X, IsPreconnected S → S ⊆ p ⁻¹' U →
      (S ∩ connectedComponentIn (p ⁻¹' U) x).Nonempty → S ⊆ connectedComponentIn (p ⁻¹' U) x :=
    fun S hS hSU hSV => (isCompOf_connectedComponentIn hx).subset_of_meets hS hSU hSV
  have hsurj : Surjective (h.restrict p _ U) := by
    rintro ⟨u, hu⟩
    have hu' : u ∈ p '' connectedComponentIn (p ⁻¹' U) x := by
      rw [hp.image_connectedComponentIn hU hUc hx]; exact hu
    obtain ⟨v, hv, rfl⟩ := hu'
    exact ⟨⟨v, hv⟩, rfl⟩
  have hsp : IsSpread (h.restrict p _ U) := hp.isSpread.restrict hVo h
  have hord : ((↑) : U → Y) ⁻¹' ordY p ⊆ ordY (h.restrict p _ U) := by
    have := subset_ordY_restrict hpc h hU (fun W hWU a ha => hsat _
      isPreconnected_connectedComponentIn ((connectedComponentIn_subset _ _).trans
        (preimage_mono hWU)) ⟨a, mem_connectedComponentIn ha, a.2⟩) (fun b _ => hsurj b)
    intro b hb
    exact this ⟨b.2, hb⟩
  have hYp : IsPortly (((↑) : U → Y) ⁻¹' ordY p) := hp.isPortly_ordY.preimage_val_of_isOpen hU
  have hXp : IsPortly (((↑) : connectedComponentIn (p ⁻¹' U) x → X) ⁻¹' ordX p) :=
    hp.isPortly_ordX.preimage_val_of_isOpen hVo
  have hordX : ((↑) : connectedComponentIn (p ⁻¹' U) x → X) ⁻¹' ordX p ⊆
      ordX (h.restrict p _ U) := fun v hv => hord hv
  have hcq : IsCompleteSpread (h.restrict p _ U) :=
    isCompleteSpread_of_pathLiftExtends hsp hYp.isOpen hord hXp
      (pathLiftExtends_restrict hp.isSpread hp.isComplete h (fun g hg hg0 t => hsat _
        (isPreconnected_range g.continuous) (by rintro _ ⟨s, rfl⟩; exact hg s)
        ⟨g 0, ⟨0, rfl⟩, hg0⟩ ⟨t, rfl⟩) _ _)
  exact ⟨hsp, hcq, hsurj, inferInstance, inferInstance,
    hXp.mono hordX (isOpen_ordX hsp.continuous), hYp.mono hord isOpen_ordY⟩

/-- **`cor:spread_connected_image`** (`RamcovGX.tex:1053`). A branched covering is open, and maps
every component of the preimage of a connected open `U` onto `U`. -/
theorem spread_connected_image [T1Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y]
    {p : X → Y} (hp : IsBranchedCovering p) :
    IsOpenMap p ∧ ∀ U : Set Y, IsOpen U → IsPreconnected U → ∀ V : Set X, IsCompOf p U V →
      p '' V = U := by
  refine ⟨fun O hO => ?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hxO, rfl⟩
    obtain ⟨U₀, hU₀, hxU₀, hsub⟩ := (isSpread_iff.1 hp.isSpread).2.2 x O hO hxO
    have hU : IsOpen (connectedComponentIn U₀ (p x)) := hU₀.connectedComponentIn
    have hxU : p x ∈ connectedComponentIn U₀ (p x) := mem_connectedComponentIn hxU₀
    have h1 := hp.image_connectedComponentIn hU isPreconnected_connectedComponentIn hxU
    refine mem_of_superset (hU.mem_nhds hxU) ?_
    rw [← h1]
    exact image_mono ((connectedComponentIn_mono _
      (preimage_mono (connectedComponentIn_subset _ _))).trans hsub)
  · rintro U hU hUc _ ⟨x, hx, rfl⟩
    exact hp.image_connectedComponentIn hU hUc hx

/-- **`cor:subcovering_portly`** (`RamcovGX.tex:1062`). The restriction of a branched covering
over a portly subset of the base is a branched covering. -/
theorem subcovering_portly [T2Space X] [LocPathConnectedSpace X] [T2Space Y]
    [LocPathConnectedSpace Y] [FirstCountableTopology Y] {p : X → Y} (hp : IsBranchedCovering p)
    {U : Set Y} (hU : IsPortly U) : IsBranchedCovering (U.restrictPreimage p) := by
  haveI := hp.connectedSpace_source
  haveI := hp.connectedSpace_target
  have hpre := hp.isPortly_preimage hU
  obtain ⟨x, hx⟩ := hpre.dense.nonempty
  have hV : IsCompOf p U (p ⁻¹' U) := ⟨x, hx, (hpre.isPreconnected.connectedComponentIn hx).symm⟩
  exact branched_covering_restriction hp hU.isOpen hU.isPreconnected hV (mapsTo_preimage p U)

/-- **`lem:subcovering_general`** (`RamcovGX.tex:1069`). The restriction of a branched covering
over a subset `Y₁ ⊆ Y` containing a portly subset of `Y` is a branched covering. -/
theorem subcovering_general [T2Space X] [LocPathConnectedSpace X] [FirstCountableTopology X]
    [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] {p : X → Y}
    (hp : IsBranchedCovering p) {Y₁ U : Set Y} (hU : IsPortly U) (hUY : U ⊆ Y₁) :
    IsBranchedCovering (Y₁.restrictPreimage p) := by
  haveI := hp.connectedSpace_source
  haveI := hp.connectedSpace_target
  have hpc := hp.isSpread.continuous
  have hÛ := hp.isPortly_preimage hU
  have hÛX : p ⁻¹' U ⊆ p ⁻¹' Y₁ := preimage_mono hUY
  obtain ⟨-, hX₁l, -⟩ := portly_first_countable hÛ hÛX
  obtain ⟨-, hY₁l, -⟩ := portly_first_countable hU hUY
  have h : MapsTo p (p ⁻¹' Y₁) Y₁ := mapsTo_preimage p Y₁
  have hsp : IsSpread (h.restrict p _ Y₁) := hp.isSpread.restrict_of_locallyConnectedSpace h
  have hsurj : Surjective (h.restrict p _ Y₁) := fun b => by
    obtain ⟨x, hx⟩ := hp.surjective b
    exact ⟨⟨x, show p x ∈ Y₁ by rw [hx]; exact b.2⟩, Subtype.ext hx⟩
  have hord : ((↑) : Y₁ → Y) ⁻¹' (U ∩ ordY p) ⊆ ordY (h.restrict p _ Y₁) :=
    subset_ordY_restrict hpc h hU.isOpen (fun W hWU _ _ => (connectedComponentIn_subset _ _).trans
      (preimage_mono (hWU.trans hUY))) (fun b _ => hsurj b)
  have hYp : IsPortly (((↑) : Y₁ → Y) ⁻¹' (U ∩ ordY p)) :=
    (hU.inter hp.isPortly_ordY).subtype (inter_subset_left.trans hUY)
  have hXp : IsPortly (((↑) : p ⁻¹' Y₁ → X) ⁻¹' (p ⁻¹' U ∩ ordX p)) :=
    (hÛ.inter hp.isPortly_ordX).subtype (inter_subset_left.trans hÛX)
  have hordX : ((↑) : p ⁻¹' Y₁ → X) ⁻¹' (p ⁻¹' U ∩ ordX p) ⊆ ordX (h.restrict p _ Y₁) :=
    fun x hx => hord hx
  haveI : ConnectedSpace (p ⁻¹' Y₁) := hÛ.connectedSpace_of_subset hÛX
  have hcq : IsCompleteSpread (h.restrict p _ Y₁) :=
    isCompleteSpread_of_pathLiftExtends hsp hYp.isOpen hord hXp
      (pathLiftExtends_restrict hp.isSpread hp.isComplete h (fun g hg _ t => hg t) _ _)
  exact ⟨hsp, hcq, hsurj, inferInstance, hU.connectedSpace_of_subset hUY,
    hXp.mono hordX (isOpen_ordX hsp.continuous), hYp.mono hord isOpen_ordY⟩

end GX
