import Mathlib

/-!
# Portly and skeletal subsets, the closure properties, and the path-covering lemma

The point-set layer of `papers/gx` (Section 2.1 and the two lemmata opening Section 3.3).

* **`def:portly_skeletal_subset`** — `RamcovGX.tex:364` (with "locally connected in `X`",
  `RamcovGX.tex:362`): `GX.IsLocallyConnectedIn`, `GX.IsPortly`, `GX.IsSkeletal`.
* `ex:following_example_skeletal_itemize` — `RamcovGX.tex:367`: in `GXScaffold.Topology.PortlyExamples`
  (partial; two tagged `sorry`s).
* **`lem:path_covering`** — `RamcovGX.tex:967`: `GX.path_covering` (relative form
  `GX.exists_path_of_isPortly_of_isOpen`), built on an infinite concatenation of paths
  `GX.Path.exists_infConcat`.
* **`lem:portly_first_countable`** — `RamcovGX.tex:974`: `GX.portly_first_countable`.
* The unlabelled closure properties `RamcovGX.tex:383–390`, all proved: `GX.IsPortly.inter`,
  `GX.isPortly_biInter_finset`, `GX.isPortly_iInter` (finite intersections); `GX.IsPortly.mono`,
  `GX.IsPortly.union`, `GX.isPortly_iUnion` (open supersets, unions); `GX.IsPortly.subtype`
  (portly in a subspace); `GX.IsPortly.trans`, `GX.IsPortly.of_subtype` (transitivity);
  `GX.isPortly_iUnion_of_local` (locality); `GX.IsPortly.preimage_of_isLocalHomeomorph`
  (local homeomorphisms); `GX.IsPortly.image_of_isOpenMap` (continuous open surjections).

> Recall that for $X$ a topological space, a subset $\U\subset X$ is locally connected in $X$
> if for all open connected $\W\subset X$, the intersection $\W\cap \U$ is connected. Note in
> particular that if $X$ is connected then $\U$ is connected.
>
> Let $X$ be a Hausdorff locally connected topological space, a subset $\U$ of $X$ is portly
> (in $X$) if $\U$ is open dense and locally connected in $X$. A subset $S\subset X$ is skeletal
> if its complement in $X$ is portly.
>
> Consider a locally connected Hausdorff topological space $X$. finite intersections of portly
> subsets are portly; if $\U\subset \V$, $\U$ is portly in $X$ and $\V$ is open then $\V$ is
> portly (hence unions of portly subsets are portly); if $\U\subset \V$ and $\U$ is portly in
> $X$ then $\U$ is portly in $\V$; if $\U$ is portly in $\V$ and $\V$ is portly in $X$ then $\U$
> is portly in $X$; locally portly subsets are portly […]; if $X\xrightarrow{f} Y$ is a local
> homeomorphism and $\U\subset Y$ is portly in $Y$ then $f^{-1}(\U)$ is portly in $X$. if
> $X\xrightarrow{f} Y$ is a continuous open surjective and $\U\subset X$ is portly in $X$ then
> $f(\U)$ is portly in $Y$.
>
> Let $X$ be a connected first countable, locally path-connected, Hausdorff topological space and
> let $\U\subset X$ be a portly subset. For all $a\in \U$ and all $b\in X$, there exists a path
> $\gamma: [0,1]\rightarrow X$ from $a$ to $b$ such that $\gamma([0,1[)\subset \U$.
>
> Let $X$ be a connected first countable, locally path-connected Hausdorff topological space and
> let $X_1$ a subset containing a portly subset. Then, $X_1$ is first countable, locally path
> connect Hausdorff.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `def`: `X` Hausdorff, locally connected | ⚠ weakened: the predicates need no hypothesis; each theorem carries what it uses |
| closure properties: `X` Hausdorff | ⚠ weakened: never used |
| closure properties: `X` locally connected | ✓ carried where used (subspace, locality, maps); `Y` not needed for the two map items |
| `lem:path_covering`: `X` connected | ⚠ weakened to `PreconnectedSpace` |
| `lem:path_covering`: first countable, locally path-connected | ✓ carried |
| `lem:path_covering`: Hausdorff | ⚠ weakened: not used |
| `lem:portly_first_countable`: `X` connected | ⚠ weakened: not used |
| `lem:portly_first_countable`: first countable, loc. path-conn., Hausdorff | ✓ carried |

## SCOPE (disclosed)

* "Locally connected in `X`" is read with `IsPreconnected` (the empty set is preconnected); for
  an open dense `U` this is equivalent to the `IsConnected` reading
  (`GX.isLocallyConnectedIn_iff_isConnected`), so `IsPortly` is the paper's notion.
* "Portly in `V`" for `V ⊆ X` is portliness of the preimage in the subspace `V`.
* The examples of skeletal sets, with their readings, are in `GXScaffold.Topology.PortlyExamples`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace GX

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `RamcovGX.tex:362`. A subset `U ⊆ X` is *locally connected in `X`* if for every open
connected `W ⊆ X` the intersection `W ∩ U` is connected. Read with `IsPreconnected` (the empty
set is preconnected); for an open dense `U` this agrees with the `IsConnected` reading, see
`isLocallyConnectedIn_iff_isConnected`. -/
def IsLocallyConnectedIn (U : Set X) : Prop :=
  ∀ W : Set X, IsOpen W → IsPreconnected W → IsPreconnected (W ∩ U)

/-- `def:portly_skeletal_subset`. A subset is *portly* if it is open, dense and locally
connected in the ambient space. -/
structure IsPortly (U : Set X) : Prop where
  isOpen : IsOpen U
  dense : Dense U
  locallyConnectedIn : IsLocallyConnectedIn U

/-- `def:portly_skeletal_subset`. A subset is *skeletal* if its complement is portly. -/
def IsSkeletal (S : Set X) : Prop :=
  IsPortly Sᶜ

/-! ### Two connectedness lemmas -/

/-- Local preconnectedness: a dense subset `S` of a preconnected `W` is preconnected as soon as
every point of `W` has an open neighbourhood `N` with `N ∩ S` preconnected. -/
theorem isPreconnected_of_local {W S : Set X} (hW : IsPreconnected W) (hSW : S ⊆ W)
    (hWS : W ⊆ closure S)
    (hloc : ∀ x ∈ W, ∃ N, IsOpen N ∧ x ∈ N ∧ IsPreconnected (N ∩ S)) :
    IsPreconnected S := by
  intro u v hu hv hSuv ⟨p, hpS, hpu⟩ ⟨q, hqS, hqv⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  choose! N hNo hxN hNc using hloc
  have key : ∀ x ∈ W, N x ∩ S ⊆ u ∨ N x ∩ S ⊆ v := fun x hx =>
    isPreconnected_iff_subset_of_disjoint.1 (hNc x hx) u v hu hv
      (inter_subset_right.trans hSuv)
      (by rw [← subset_empty_iff, ← hne]; exact inter_subset_inter_left _ inter_subset_right)
  set u' := ⋃ x ∈ {x | x ∈ W ∧ N x ∩ S ⊆ u}, N x
  set v' := ⋃ x ∈ {x | x ∈ W ∧ N x ∩ S ⊆ v}, N x
  have hu' : IsOpen u' := isOpen_biUnion fun x hx => hNo x hx.1
  have hv' : IsOpen v' := isOpen_biUnion fun x hx => hNo x hx.1
  have hWuv : W ⊆ u' ∪ v' := by
    intro x hx
    rcases key x hx with h | h
    · exact Or.inl (mem_biUnion ⟨hx, h⟩ (hxN x hx))
    · exact Or.inr (mem_biUnion ⟨hx, h⟩ (hxN x hx))
  have hp : (W ∩ u').Nonempty := by
    refine ⟨p, hSW hpS, mem_biUnion ⟨hSW hpS, ?_⟩ (hxN p (hSW hpS))⟩
    rcases key p (hSW hpS) with h | h
    · exact h
    · exact absurd (hne ▸ (⟨hpS, hpu, h ⟨hxN p (hSW hpS), hpS⟩⟩ : p ∈ S ∩ (u ∩ v)))
        (notMem_empty p)
  have hq : (W ∩ v').Nonempty := by
    refine ⟨q, hSW hqS, mem_biUnion ⟨hSW hqS, ?_⟩ (hxN q (hSW hqS))⟩
    rcases key q (hSW hqS) with h | h
    · exact absurd (hne ▸ (⟨hqS, h ⟨hxN q (hSW hqS), hqS⟩, hqv⟩ : q ∈ S ∩ (u ∩ v)))
        (notMem_empty q)
    · exact h
  obtain ⟨z, hzW, hzu, hzv⟩ := hW u' v' hu' hv' hWuv hp hq
  simp only [u', v', mem_iUnion, mem_setOf_eq, exists_prop] at hzu hzv
  obtain ⟨x, ⟨hxW, hxu⟩, hzx⟩ := hzu
  obtain ⟨y, ⟨hyW, hyv⟩, hzy⟩ := hzv
  obtain ⟨w, ⟨hwx, hwy⟩, hwS⟩ :=
    mem_closure_iff.1 (hWS hzW) _ ((hNo x hxW).inter (hNo y hyW)) ⟨hzx, hzy⟩
  have : w ∈ S ∩ (u ∩ v) := ⟨hwS, hxu ⟨hwx, hwS⟩, hyv ⟨hwy, hwS⟩⟩
  rw [hne] at this
  exact this

/-- If `U` is locally connected in a locally connected `X`, `O` is open and `T ⊆ O` is a
preconnected set containing `O ∩ U`, then `O ∩ U` is preconnected. -/
theorem IsLocallyConnectedIn.isPreconnected_of_subset [LocallyConnectedSpace X] {U O T : Set X}
    (hU : IsLocallyConnectedIn U) (hO : IsOpen O) (hT : IsPreconnected T) (hTO : T ⊆ O)
    (hOT : O ∩ U ⊆ T) : IsPreconnected (O ∩ U) := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [subset_empty_iff.1 hOT]; exact isPreconnected_empty
  have hTC : T ⊆ connectedComponentIn O x := hT.subset_connectedComponentIn hx hTO
  have heq : O ∩ U = connectedComponentIn O x ∩ U := by
    apply Subset.antisymm
    · exact fun y hy => ⟨hTC (hOT hy), hy.2⟩
    · exact inter_subset_inter_left _ (connectedComponentIn_subset O x)
  rw [heq]
  exact hU _ hO.connectedComponentIn isPreconnected_connectedComponentIn

/-! ### Basic facts -/

/-- For an open dense `U`, the `IsPreconnected` reading of "locally connected in `X`" agrees with
the `IsConnected` one (`W` open connected implies `W ∩ U` connected); only density is used. -/
theorem isLocallyConnectedIn_iff_isConnected {U : Set X} (hUd : Dense U) :
    IsLocallyConnectedIn U ↔ ∀ W : Set X, IsOpen W → IsConnected W → IsConnected (W ∩ U) := by
  constructor
  · intro h W hW hWc
    exact ⟨hUd.inter_open_nonempty W hW hWc.nonempty |>.mono (by rw [inter_comm]),
      h W hW hWc.isPreconnected⟩
  · intro h W hW hWc
    rcases W.eq_empty_or_nonempty with rfl | hne
    · rw [empty_inter]; exact isPreconnected_empty
    · exact (h W hW ⟨hne, hWc⟩).isPreconnected

/-- `rem:branching_locii_branched_covering` (first half): a skeletal set is closed. -/
theorem IsSkeletal.isClosed {S : Set X} (hS : IsSkeletal S) : IsClosed S :=
  isOpen_compl_iff.1 hS.isOpen

/-- A skeletal set has empty interior. -/
theorem IsSkeletal.interior_eq_empty {S : Set X} (hS : IsSkeletal S) : interior S = ∅ :=
  interior_eq_empty_iff_dense_compl.2 hS.dense

theorem isSkeletal_iff {S : Set X} : IsSkeletal S ↔ IsPortly Sᶜ := Iff.rfl

theorem isSkeletal_compl_iff {U : Set X} : IsSkeletal Uᶜ ↔ IsPortly U := by
  rw [IsSkeletal, compl_compl]

/-- If `X` is preconnected, a portly subset is preconnected (`RamcovGX.tex:362`, "if `X` is
connected then `U` is connected"). -/
theorem IsPortly.isPreconnected [PreconnectedSpace X] {U : Set X} (hU : IsPortly U) :
    IsPreconnected U := by
  simpa using hU.locallyConnectedIn univ isOpen_univ isPreconnected_univ

theorem IsPortly.isConnected [ConnectedSpace X] {U : Set X} (hU : IsPortly U) :
    IsConnected U :=
  ⟨hU.dense.nonempty, hU.isPreconnected⟩

theorem IsPortly.isPreconnected_inter {U W : Set X} (hU : IsPortly U) (hW : IsOpen W)
    (hWc : IsPreconnected W) : IsPreconnected (W ∩ U) :=
  hU.locallyConnectedIn W hW hWc

theorem IsPortly.isConnected_inter {U W : Set X} (hU : IsPortly U) (hW : IsOpen W)
    (hWc : IsConnected W) : IsConnected (W ∩ U) :=
  ⟨(hU.dense.inter_open_nonempty W hW hWc.nonempty).mono (by rw [inter_comm]),
    hU.locallyConnectedIn W hW hWc.isPreconnected⟩

/-- The whole space is portly. -/
theorem isPortly_univ : IsPortly (univ : Set X) :=
  ⟨isOpen_univ, dense_univ, fun W _ hW => by simpa using hW⟩

/-- The empty set is skeletal. -/
theorem isSkeletal_empty : IsSkeletal (∅ : Set X) := by
  rw [IsSkeletal, compl_empty]; exact isPortly_univ

/-! ### The closure properties of `RamcovGX.tex:383–390` -/

/-- `RamcovGX.tex:383`: the intersection of two portly subsets is portly. -/
theorem IsPortly.inter {U V : Set X} (hU : IsPortly U) (hV : IsPortly V) : IsPortly (U ∩ V) :=
  ⟨hU.isOpen.inter hV.isOpen, hU.dense.inter_of_isOpen_left hV.dense hU.isOpen,
    fun W hW hWc => by
      rw [← inter_assoc]
      exact hV.locallyConnectedIn _ (hW.inter hU.isOpen) (hU.locallyConnectedIn W hW hWc)⟩

/-- `RamcovGX.tex:383`: finite intersections of portly subsets are portly. -/
theorem isPortly_biInter_finset {ι : Type*} {s : Finset ι} {U : ι → Set X}
    (hU : ∀ i ∈ s, IsPortly (U i)) : IsPortly (⋂ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPortly_univ : IsPortly (univ : Set X))
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (hU i (Finset.mem_insert_self i s)).inter
      (ih fun j hj => hU j (Finset.mem_insert_of_mem hj))

/-- `RamcovGX.tex:383`: finite intersections of portly subsets are portly. -/
theorem isPortly_iInter {ι : Type*} [Finite ι] {U : ι → Set X} (hU : ∀ i, IsPortly (U i)) :
    IsPortly (⋂ i, U i) := by
  cases nonempty_fintype ι
  simpa using isPortly_biInter_finset (s := Finset.univ) (U := U) (fun i _ => hU i)

/-- `RamcovGX.tex:383`, skeletal form: finite unions of skeletal subsets are skeletal. -/
theorem IsSkeletal.union {S T : Set X} (hS : IsSkeletal S) (hT : IsSkeletal T) :
    IsSkeletal (S ∪ T) := by
  rw [IsSkeletal, compl_union]; exact hS.inter hT

/-- `RamcovGX.tex:384`: an open superset of a portly subset is portly. -/
theorem IsPortly.mono {U V : Set X} (hU : IsPortly U) (hUV : U ⊆ V) (hV : IsOpen V) :
    IsPortly V := by
  refine ⟨hV, hU.dense.mono hUV, fun W hW hWc => ?_⟩
  refine (hU.locallyConnectedIn W hW hWc).subset_closure (inter_subset_inter_right _ hUV) ?_
  intro x hx
  exact hW.inter_closure ⟨hx.1, hU.dense x⟩

/-- `RamcovGX.tex:384`, skeletal form: a closed subset of a skeletal subset is skeletal. -/
theorem IsSkeletal.anti {S T : Set X} (hS : IsSkeletal S) (hTS : T ⊆ S) (hT : IsClosed T) :
    IsSkeletal T :=
  IsPortly.mono hS (compl_subset_compl.2 hTS) hT.isOpen_compl

/-- `RamcovGX.tex:384`: the union of two portly subsets is portly. -/
theorem IsPortly.union {U V : Set X} (hU : IsPortly U) (hV : IsPortly V) : IsPortly (U ∪ V) :=
  hU.mono subset_union_left (hU.isOpen.union hV.isOpen)

/-- `RamcovGX.tex:384`: a nonempty union of portly subsets is portly. -/
theorem isPortly_iUnion {ι : Sort*} [Nonempty ι] {U : ι → Set X} (hU : ∀ i, IsPortly (U i)) :
    IsPortly (⋃ i, U i) :=
  let i := Classical.arbitrary ι
  (hU i).mono (subset_iUnion U i) (isOpen_iUnion fun j => (hU j).isOpen)

/-- `RamcovGX.tex:385`: if `U ⊆ V` and `U` is portly in a locally connected `X`, then `U` is
portly in `V` (for an arbitrary subset `V`, with the subspace topology). -/
theorem IsPortly.subtype [LocallyConnectedSpace X] {U V : Set X} (hU : IsPortly U) (hUV : U ⊆ V) :
    IsPortly (((↑) : V → X) ⁻¹' U) := by
  refine ⟨hU.isOpen.preimage continuous_subtype_val, ?_, ?_⟩
  · intro x
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, inter_eq_right.2 hUV, hU.dense.closure_eq]
    exact mem_univ _
  · intro W hW hWc
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hW
    have hT : IsPreconnected (((↑) : V → X) '' (((↑) : V → X) ⁻¹' O)) :=
      hWc.image _ continuous_subtype_val.continuousOn
    have hTO : ((↑) : V → X) '' (((↑) : V → X) ⁻¹' O) ⊆ O := image_preimage_subset _ _
    have hOT : O ∩ U ⊆ ((↑) : V → X) '' (((↑) : V → X) ⁻¹' O) := fun y hy =>
      ⟨⟨y, hUV hy.2⟩, hy.1, rfl⟩
    have h := hU.locallyConnectedIn.isPreconnected_of_subset hO hT hTO hOT
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_inter_preimage,
      Subtype.image_preimage_coe]
    convert h using 1
    ext y
    constructor
    · rintro ⟨⟨_, hyO⟩, hyU⟩; exact ⟨hyO, hyU⟩
    · rintro ⟨hyO, hyU⟩; exact ⟨⟨hUV hyU, hyO⟩, hyU⟩

/-- `RamcovGX.tex:386`: if `U` is portly in `V` and `V` is portly in `X`, then `U` is portly in
`X`. -/
theorem IsPortly.trans {V : Set X} {U : Set V} (hU : IsPortly U) (hV : IsPortly V) :
    IsPortly (((↑) : V → X) '' U) := by
  refine ⟨hV.isOpen.isOpenMap_subtype_val _ hU.isOpen,
    hV.dense.denseRange_val.dense_image continuous_subtype_val hU.dense, fun W hW hWc => ?_⟩
  have hW' : IsPreconnected (((↑) : V → X) ⁻¹' W) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_comm]
    exact hV.locallyConnectedIn W hW hWc
  have h := hU.locallyConnectedIn _ (hW.preimage continuous_subtype_val) hW'
  rw [← image_preimage_inter]
  exact h.image _ continuous_subtype_val.continuousOn

/-- `RamcovGX.tex:386`, for subsets of `X`: if `U ⊆ V`, `U` is portly in `V` and `V` is portly in
`X`, then `U` is portly in `X`. -/
theorem IsPortly.of_subtype {U V : Set X} (hU : IsPortly (((↑) : V → X) ⁻¹' U)) (hUV : U ⊆ V)
    (hV : IsPortly V) : IsPortly U := by
  have := hU.trans hV
  rwa [Subtype.image_preimage_coe, inter_eq_right.2 hUV] at this

/-- Portliness in an open subset `O`, read intrinsically in `X`. -/
theorem isPortly_subtype_iff {U O : Set X} (hO : IsOpen O) (hUO : U ⊆ O) :
    IsPortly (((↑) : O → X) ⁻¹' U) ↔
      IsOpen U ∧ O ⊆ closure U ∧
        ∀ W : Set X, IsOpen W → W ⊆ O → IsPreconnected W → IsPreconnected (W ∩ U) := by
  have himg : ((↑) : O → X) '' (((↑) : O → X) ⁻¹' U) = U := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hUO]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨himg ▸ hO.isOpenMap_subtype_val _ h1, fun x hx => ?_, fun W hW hWO hWc => ?_⟩
    · have := h2 ⟨x, hx⟩
      rwa [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, himg] at this
    · have hW' : IsPreconnected (((↑) : O → X) ⁻¹' W) := by
        rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
          inter_eq_right.2 hWO]
        exact hWc
      have h := h3 _ (hW.preimage continuous_subtype_val) hW'
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_inter_preimage,
        Subtype.image_preimage_coe, inter_eq_right.2 hWO] at h
      exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1.preimage continuous_subtype_val, fun x => ?_, fun W hW hWc => ?_⟩
    · rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, himg]
      exact h2 x.2
    · obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
      have hc : IsPreconnected (W' ∩ O) := by
        rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
          inter_comm] at hWc
        exact hWc
      have h := h3 (W' ∩ O) (hW'.inter hO) inter_subset_right hc
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_inter_preimage,
        Subtype.image_preimage_coe]
      convert h using 1
      ext y
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨b, a⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨⟨b, a⟩, c⟩⟩

/-- `RamcovGX.tex:388`: locally portly subsets are portly. If `(U i)` are open, and each
`V i ⊆ U i` is portly in `U i`, then `⋃ V i` is portly in `⋃ U i`. -/
theorem isPortly_iUnion_of_local [LocallyConnectedSpace X] {ι : Sort*} {U V : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hVU : ∀ i, V i ⊆ U i)
    (hV : ∀ i, IsPortly (((↑) : U i → X) ⁻¹' V i)) :
    IsPortly (((↑) : (⋃ i, U i : Set X) → X) ⁻¹' ⋃ i, V i) := by
  have hV' := fun i => (isPortly_subtype_iff (hU i) (hVU i)).1 (hV i)
  rw [isPortly_subtype_iff (isOpen_iUnion hU) (iUnion_mono hVU)]
  refine ⟨isOpen_iUnion fun i => (hV' i).1, ?_, fun W hW hWO hWc => ?_⟩
  · exact iUnion_subset fun i => (hV' i).2.1.trans (closure_mono (subset_iUnion V i))
  · have hcl : W ⊆ closure (W ∩ ⋃ i, V i) := fun x hx => hW.inter_closure
      ⟨hx, (iUnion_subset fun i => (hV' i).2.1.trans (closure_mono (subset_iUnion V i)))
        (hWO hx)⟩
    refine isPreconnected_of_local hWc inter_subset_left hcl fun x hx => ?_
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hWO hx)
    set N := connectedComponentIn (W ∩ U i) x
    have hNo : IsOpen N := (hW.inter (hU i)).connectedComponentIn
    have hNW : N ⊆ W ∩ U i := connectedComponentIn_subset _ _
    refine ⟨N, hNo, mem_connectedComponentIn ⟨hx, hxi⟩, ?_⟩
    have h1 : IsPreconnected (N ∩ V i) :=
      (hV' i).2.2 N hNo (hNW.trans inter_subset_right) isPreconnected_connectedComponentIn
    refine h1.subset_closure ?_ ?_
    · exact fun y hy => ⟨hy.1, hNW hy.1 |>.1, mem_iUnion.2 ⟨i, hy.2⟩⟩
    · exact fun y hy => hNo.inter_closure ⟨hy.1, (hV' i).2.1 (hNW hy.1).2⟩

/-- `RamcovGX.tex:389`: the preimage of a portly subset under a local homeomorphism is portly.
Only the source needs to be locally connected. -/
theorem IsPortly.preimage_of_isLocalHomeomorph [LocallyConnectedSpace X] {f : X → Y}
    (hf : IsLocalHomeomorph f) {U : Set Y} (hU : IsPortly U) : IsPortly (f ⁻¹' U) := by
  refine ⟨hU.isOpen.preimage hf.continuous, hU.dense.preimage hf.isOpenMap,
    fun W hW hWc => ?_⟩
  have hcl : W ⊆ closure (W ∩ f ⁻¹' U) := fun x hx =>
    hW.inter_closure ⟨hx, hU.dense.preimage hf.isOpenMap x⟩
  refine isPreconnected_of_local hWc inter_subset_left hcl fun x hx => ?_
  obtain ⟨e, hxe, rfl⟩ := hf x
  set N := connectedComponentIn (W ∩ e.source) x
  have hNo : IsOpen N := (hW.inter e.open_source).connectedComponentIn
  have hNW : N ⊆ W ∩ e.source := connectedComponentIn_subset _ _
  refine ⟨N, hNo, mem_connectedComponentIn ⟨hx, hxe⟩, ?_⟩
  have hNs : N ⊆ e.source := hNW.trans inter_subset_right
  have heN : IsOpen (e '' N) := e.isOpen_image_of_subset_source hNo hNs
  have hNc : IsPreconnected (e '' N) :=
    isPreconnected_connectedComponentIn.image _ (e.continuousOn.mono hNs)
  have h1 := hU.locallyConnectedIn _ heN hNc
  have h2 : IsPreconnected (e.symm '' (e '' N ∩ U)) :=
    h1.image _ (e.continuousOn_symm.mono
      (inter_subset_left.trans (e.mapsTo.mono_left hNs).image_subset))
  convert h2 using 1
  rw [← image_inter_preimage]
  refine Eq.trans ?_ (e.toPartialEquiv.symm_image_image_of_subset_source
    (inter_subset_left.trans hNs : N ∩ e ⁻¹' U ⊆ e.source)).symm
  ext y
  exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, (hNW a).1, c⟩⟩

/-- `RamcovGX.tex:390`: the image of a portly subset under a continuous open surjection is
portly. Only the source needs to be locally connected. -/
theorem IsPortly.image_of_isOpenMap [LocallyConnectedSpace X] {f : X → Y} (hfc : Continuous f)
    (hfo : IsOpenMap f) (hfs : Function.Surjective f) {U : Set X} (hU : IsPortly U) :
    IsPortly (f '' U) := by
  have hd : Dense (f '' U) := hfs.denseRange.dense_image hfc hU.dense
  refine ⟨hfo U hU.isOpen, hd, fun W hW hWc => ?_⟩
  have hcl : W ⊆ closure (W ∩ f '' U) := fun x hx => hW.inter_closure ⟨hx, hd x⟩
  refine isPreconnected_of_local hWc inter_subset_left hcl fun y hy => ?_
  obtain ⟨x, rfl⟩ := hfs y
  set C := connectedComponentIn (f ⁻¹' W) x
  have hCo : IsOpen C := (hW.preimage hfc).connectedComponentIn
  have hCW : C ⊆ f ⁻¹' W := connectedComponentIn_subset _ _
  refine ⟨f '' C, hfo C hCo, ⟨x, mem_connectedComponentIn hy, rfl⟩, ?_⟩
  have h1 : IsPreconnected (f '' (C ∩ U)) :=
    (hU.locallyConnectedIn C hCo isPreconnected_connectedComponentIn).image _ hfc.continuousOn
  refine h1.subset_closure ?_ ?_
  · rintro _ ⟨z, ⟨hzC, hzU⟩, rfl⟩
    exact ⟨⟨z, hzC, rfl⟩, hCW hzC, ⟨z, hzU, rfl⟩⟩
  · rintro _ ⟨⟨z, hzC, rfl⟩, -, -⟩
    exact image_closure_subset_closure_image hfc ⟨z, hCo.inter_closure ⟨hzC, hU.dense z⟩, rfl⟩

/-! ### Infinite concatenation of paths -/

/-- The family `n ↦ [n, n+1]` of closed intervals of `ℝ` is locally finite. -/
theorem locallyFinite_Icc_nat : LocallyFinite fun n : ℕ => Icc (n : ℝ) (n + 1) := by
  intro x
  refine ⟨Iio (x + 1), Iio_mem_nhds (by linarith), ?_⟩
  refine (Set.finite_lt_nat ⌈x + 1⌉₊).subset fun n hn => ?_
  obtain ⟨y, ⟨hny, -⟩, hyx⟩ := hn
  simp only [mem_setOf_eq]
  exact Nat.lt_ceil.2 (lt_of_le_of_lt hny hyx)

/-- The infinite concatenation of a sequence of paths `φ n : c n ⇝ c (n+1)` along the real
half-line: on `[n, n+1]` it runs `φ n`. -/
def infConcatReal {c : ℕ → X} (φ : ∀ n, Path (c n) (c (n + 1))) (s : ℝ) : X :=
  (φ ⌊s⌋₊).extend (s - ⌊s⌋₊)

theorem infConcatReal_eqOn {c : ℕ → X} (φ : ∀ n, Path (c n) (c (n + 1))) (n : ℕ) :
    EqOn (infConcatReal φ) (fun s => (φ n).extend (s - n)) (Icc (n : ℝ) (n + 1)) := by
  intro s ⟨h1, h2⟩
  rcases h2.lt_or_eq with h2 | h2
  · have : ⌊s⌋₊ = n := by
      rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
      exact ⟨h1, h2⟩
    subst this
    rfl
  · subst h2
    have : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by exact_mod_cast Nat.floor_natCast (n + 1)
    simp only [infConcatReal, this, Nat.cast_add, Nat.cast_one, sub_self, Path.extend_zero]
    rw [show (n : ℝ) + 1 - n = 1 by ring, Path.extend_one]

theorem continuousOn_infConcatReal {c : ℕ → X} (φ : ∀ n, Path (c n) (c (n + 1))) :
    ContinuousOn (infConcatReal φ) (Ici 0) := by
  have hcov : Ici (0 : ℝ) = ⋃ n : ℕ, Icc (n : ℝ) (n + 1) := by
    ext s
    simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro hs
      exact ⟨⌊s⌋₊, Nat.floor_le hs, (Nat.lt_floor_add_one s).le⟩
    · rintro ⟨n, hn, -⟩
      exact le_trans (Nat.cast_nonneg n) hn
  rw [hcov]
  refine locallyFinite_Icc_nat.continuousOn_iUnion (fun n => isClosed_Icc) fun n => ?_
  refine ContinuousOn.congr ?_ (infConcatReal_eqOn φ n)
  exact ((φ n).continuous_extend.comp (continuous_id.sub continuous_const)).continuousOn

theorem infConcatReal_mem {c : ℕ → X} (φ : ∀ n, Path (c n) (c (n + 1))) (s : ℝ) :
    ∃ n t, infConcatReal φ s = φ n t ∧ (0 ≤ s → (s : ℝ) < n + 1) ∧ ((n : ℝ) ≤ s ∨ n = 0) := by
  refine ⟨⌊s⌋₊, projIcc 0 1 zero_le_one (s - ⌊s⌋₊), rfl, fun hs => Nat.lt_floor_add_one s, ?_⟩
  rcases le_or_gt 0 s with hs | hs
  · exact Or.inl (Nat.floor_le hs)
  · exact Or.inr (Nat.floor_eq_zero.2 (by linarith))

/-- **Infinite concatenation of paths.** Given paths `φ n : c n ⇝ c (n+1)` whose images shrink to
`b` (every neighbourhood of `b` contains the images of all but finitely many of them), there is
a path `γ : c 0 ⇝ b` every point of which before time `1` is a point of one of the `φ n`. -/
theorem Path.exists_infConcat {c : ℕ → X} (φ : ∀ n, Path (c n) (c (n + 1))) {b : X}
    (hφ : ∀ N ∈ 𝓝 b, ∀ᶠ n in atTop, ∀ t, φ n t ∈ N) :
    ∃ γ : Path (c 0) b, ∀ t : unitInterval, (t : ℝ) < 1 → ∃ n s, γ t = φ n s := by
  set H : ℝ → X := fun s => infConcatReal φ (max 0 s)
  have hH : Continuous H :=
    (continuousOn_infConcatReal φ).comp_continuous (continuous_const.max continuous_id)
      fun s => mem_Ici.2 (le_max_left _ _)
  set g : unitInterval → ℝ := fun t => (t : ℝ) / (1 - t)
  set γ : unitInterval → X := fun t => if (t : ℝ) < 1 then H (g t) else b
  have hγ0 : γ 0 = c 0 := by
    simp [γ, H, g, infConcatReal]
  have hγ1 : γ 1 = b := by simp [γ]
  have hγt : ∀ t : unitInterval, (t : ℝ) < 1 → ∃ n s, γ t = φ n s := by
    intro t ht
    obtain ⟨n, s, h, -⟩ := infConcatReal_mem φ (max 0 (g t))
    exact ⟨n, s, by simp only [γ, if_pos ht]; exact h⟩
  have hcont : Continuous γ := by
    rw [continuous_iff_continuousAt]
    intro t
    rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
    · have hev : γ =ᶠ[𝓝 t] fun t => H (g t) := by
        filter_upwards [(isOpen_lt continuous_subtype_val continuous_const).mem_nhds ht]
          with t' ht'
        simp only [γ, if_pos (show (t' : ℝ) < 1 from ht')]
      refine ContinuousAt.congr ?_ hev.symm
      refine hH.continuousAt.comp ?_
      exact (continuous_subtype_val.continuousAt).div
        (continuous_const.sub continuous_subtype_val).continuousAt (by linarith)
    · have ht1 : t = 1 := Subtype.ext ht
      subst ht1
      rw [ContinuousAt, hγ1]
      intro N hN
      rw [mem_map]
      obtain ⟨k, hk⟩ := eventually_atTop.1 (hφ N hN)
      have hbN : b ∈ N := mem_of_mem_nhds hN
      have hlt : ((k : ℝ) / (k + 1)) < ((1 : unitInterval) : ℝ) := by
        rw [Set.Icc.coe_one, div_lt_one (by positivity)]; linarith
      filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hlt]
        with t' ht'
      show γ t' ∈ N
      by_cases h1 : (t' : ℝ) < 1
      · simp only [γ, if_pos h1, H]
        obtain ⟨n, s, h, hlt', hle⟩ := infConcatReal_mem φ (max 0 (g t'))
        rw [h]
        have hpos : 0 < 1 - (t' : ℝ) := by linarith
        have hgk : (k : ℝ) ≤ g t' := by
          simp only [g]
          rw [le_div_iff₀ hpos]
          have := (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 1)).1 ht'
          nlinarith
        have hg0 : 0 ≤ g t' := div_nonneg t'.2.1 hpos.le
        have hkn : k ≤ n := by
          have h' := hlt' (le_max_left _ _)
          rw [max_eq_right hg0] at h'
          have : (k : ℝ) < n + 1 := by linarith
          exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
        exact hk n hkn s
      · simp only [γ, if_neg h1]; exact hbN
  exact ⟨⟨⟨γ, hcont⟩, hγ0, hγ1⟩, hγt⟩

/-! ### `lem:path_covering` and `lem:portly_first_countable` -/

/-- `lem:path_covering`, relative form: inside a preconnected open `O`, any `a ∈ U ∩ O` and
`b ∈ O` are joined by a path in `O` which lies in `U` before time `1`. -/
theorem exists_path_of_isPortly_of_isOpen [FirstCountableTopology X] [LocPathConnectedSpace X]
    {U O : Set X} (hU : IsPortly U) (hO : IsOpen O) (hOc : IsPreconnected O) {a b : X}
    (ha : a ∈ U) (haO : a ∈ O) (hb : b ∈ O) :
    ∃ γ : Path a b, (∀ t, γ t ∈ O) ∧ ∀ t : unitInterval, (t : ℝ) < 1 → γ t ∈ U := by
  obtain ⟨x, hx⟩ := (𝓝 b).exists_antitone_basis
  set V : ℕ → Set X := fun n => pathComponentIn (interior (x n) ∩ O) b
  have hbx : ∀ n, b ∈ interior (x n) ∩ O := fun n =>
    ⟨mem_interior_iff_mem_nhds.2 (hx.mem n), hb⟩
  have hVo : ∀ n, IsOpen (V n) := fun n => (isOpen_interior.inter hO).pathComponentIn b
  have hbV : ∀ n, b ∈ V n := fun n => mem_pathComponentIn_self (hbx n)
  have hVsub : ∀ n, V n ⊆ x n ∩ O := fun n =>
    pathComponentIn_subset.trans (inter_subset_inter_left _ interior_subset)
  have hVanti : Antitone V := fun m n hmn =>
    pathComponentIn_mono (inter_subset_inter_left _ (interior_mono (hx.antitone hmn)))
  have hVc : ∀ n, IsPreconnected (V n) := fun n =>
    (isPathConnected_pathComponentIn (hbx n)).isConnected.isPreconnected
  -- points of `U` approaching `b`
  have hb' : ∀ n, (V n ∩ U).Nonempty := fun n =>
    hU.dense.inter_open_nonempty _ (hVo n) ⟨b, hbV n⟩
  choose p hp using hb'
  -- the path-connected pieces
  have hpc : ∀ n, IsPathConnected (V n ∩ U) := fun n =>
    ((hVo n).inter hU.isOpen).isConnected_iff_isPathConnected.1
      ⟨⟨p n, hp n⟩, hU.locallyConnectedIn _ (hVo n) (hVc n)⟩
  have hOU : IsPathConnected (O ∩ U) :=
    (hO.inter hU.isOpen).isConnected_iff_isPathConnected.1
      ⟨⟨a, haO, ha⟩, hU.locallyConnectedIn _ hO hOc⟩
  set c : ℕ → X := fun n => Nat.casesOn n a fun m => p m
  have j0 : JoinedIn (O ∩ U) a (p 0) :=
    hOU.joinedIn a ⟨haO, ha⟩ (p 0) ⟨(hVsub 0 (hp 0).1).2, (hp 0).2⟩
  have js : ∀ n, JoinedIn (V n ∩ U) (p n) (p (n + 1)) := fun n =>
    (hpc n).joinedIn _ (hp n) _ ⟨hVanti (Nat.le_succ n) (hp (n + 1)).1, (hp (n + 1)).2⟩
  let φ : ∀ n, Path (c n) (c (n + 1)) := fun n =>
    match n with
    | 0 => j0.somePath
    | n + 1 => (js n).somePath
  have hφOU : ∀ n t, φ n t ∈ O ∩ U := by
    intro n t
    match n with
    | 0 => exact j0.somePath_mem t
    | n + 1 =>
      have := (js n).somePath_mem t
      exact ⟨(hVsub n this.1).2, this.2⟩
  have hφV : ∀ n t, φ (n + 1) t ∈ V n := fun n t => ((js n).somePath_mem t).1
  have hlim : ∀ N ∈ 𝓝 b, ∀ᶠ n in atTop, ∀ t, φ n t ∈ N := by
    intro N hN
    obtain ⟨k, -, hk⟩ := hx.toHasBasis.mem_iff.1 hN
    refine eventually_atTop.2 ⟨k + 1, fun n hn t => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hk ((hVsub k (hVanti (by omega) (hφV m t))).1)
  obtain ⟨γ, hγ⟩ := Path.exists_infConcat φ hlim
  refine ⟨γ, fun t => ?_, fun t ht => ?_⟩
  · rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
    · obtain ⟨n, s, h⟩ := hγ t ht
      rw [h]; exact (hφOU n s).1
    · rw [show t = 1 from Subtype.ext ht, γ.target]; exact hb
  · obtain ⟨n, s, h⟩ := hγ t ht
    rw [h]; exact (hφOU n s).2

/-- **`lem:path_covering`** (`RamcovGX.tex:967`). Let `X` be connected, first countable and
locally path-connected, and `U ⊆ X` portly. For all `a ∈ U` and `b ∈ X` there is a path
`γ : a ⇝ b` with `γ([0,1)) ⊆ U`. (Hausdorff is not used; preconnected suffices.) -/
theorem path_covering [PreconnectedSpace X] [FirstCountableTopology X] [LocPathConnectedSpace X]
    {U : Set X} (hU : IsPortly U) {a b : X} (ha : a ∈ U) :
    ∃ γ : Path a b, ∀ t : unitInterval, (t : ℝ) < 1 → γ t ∈ U := by
  obtain ⟨γ, -, hγ⟩ :=
    exists_path_of_isPortly_of_isOpen hU isOpen_univ isPreconnected_univ ha (mem_univ a)
      (mem_univ b)
  exact ⟨γ, hγ⟩

/-- In a first countable, locally path-connected space, an open connected set `V` meets every
set `X₁` containing a portly subset in a path-connected set. -/
theorem isPathConnected_inter_of_isPortly [FirstCountableTopology X] [LocPathConnectedSpace X]
    {U X₁ V : Set X} (hU : IsPortly U) (hUX : U ⊆ X₁) (hV : IsOpen V) (hVc : IsConnected V) :
    IsPathConnected (V ∩ X₁) := by
  obtain ⟨c, hcV, hcU⟩ := hU.dense.inter_open_nonempty V hV hVc.nonempty
  refine ⟨c, ⟨hcV, hUX hcU⟩, fun y hy => ?_⟩
  obtain ⟨γ, hγV, hγU⟩ :=
    exists_path_of_isPortly_of_isOpen hU hV hVc.isPreconnected hcU hcV hy.1
  refine ⟨γ, fun t => ⟨hγV t, ?_⟩⟩
  rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
  · exact hUX (hγU t ht)
  · rw [show t = 1 from Subtype.ext ht, γ.target]; exact hy.2

/-- **`lem:portly_first_countable`** (`RamcovGX.tex:974`). Let `X` be first countable, locally
path-connected and Hausdorff and let `X₁ ⊆ X` contain a portly subset. Then `X₁` is first
countable, locally path-connected and Hausdorff. (Connectedness of `X` is not used.) -/
theorem portly_first_countable [FirstCountableTopology X] [LocPathConnectedSpace X] [T2Space X]
    {U X₁ : Set X} (hU : IsPortly U) (hUX : U ⊆ X₁) :
    FirstCountableTopology X₁ ∧ LocPathConnectedSpace X₁ ∧ T2Space X₁ := by
  refine ⟨inferInstance, ?_, inferInstance⟩
  refine LocPathConnectedSpace.of_bases
    (p := fun x : X₁ => fun V : Set X => IsOpen V ∧ (x : X) ∈ V ∧ IsConnected V)
    (s := fun _ V => ((↑) : X₁ → X) ⁻¹' V) (fun x => ?_) (fun x V hV => ?_)
  · rw [nhds_subtype]
    exact (LocallyConnectedSpace.open_connected_basis (x : X)).comap _
  · have h := (isPathConnected_inter_of_isPortly hU hUX hV.1 hV.2.2).preimage_coe
      (inter_subset_right : V ∩ X₁ ⊆ X₁)
    rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at h

end GX
