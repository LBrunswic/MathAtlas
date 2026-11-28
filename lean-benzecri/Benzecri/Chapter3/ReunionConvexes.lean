import Benzecri.Chapter3.ProprietesIII
import Benzecri.Chapter3.HyperplanSeparant

/-!
# Chapter 3 § 5, Theorem 1 — a compact convex `V ⊆ W`: I(V, W) ⇔ II(V, W) ⇔ III(V, W)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal p. 280; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (to be checked by the author). Target
T-bz-c3-reunion-convexes. `I(V, W)` is `Benzecri.ProprieteI` (Déf. 1), `II(V, W)` is
`Benzecri.ProprieteII` (Prop. 8), « le support de $V$ » is `affineSpan ℝ V`, « variété d'appui »
is `Benzecri.IsVarieteAppui` (Déf. 3). The space is a finite-dimensional real Hausdorff
topological vector space (its topology is then the canonical one).

* `bzthm:c3s5t1_reunion_convexes_affine` — `benzecri1960_ch3.tex:1381` (Theorem 1, l.1381–1392;
  no proof printed beyond the lead-in « Des propositions 7, 8 et 4 résulte le », l.1378–1379) —
  `Benzecri.reunion_convexes_affine` (TFAE of I, II, III, with `[Nontrivial E]`),
  `Benzecri.reunion_convexes_affine_of_ne` (no `Nontrivial`, for `V ≠ W`); the parts
  `Benzecri.proprieteIII_of_proprieteI` (I ⇒ III, in every dimension: `V` closed suffices),
  `Benzecri.proprieteI_of_proprieteIIIlarge` (III ⇒ I for every reading of « demi-espace de L »,
  no topology), `Benzecri.proprieteI_iff_proprieteIII` (I ⇔ III, every dimension, `E = 0`
  included). New definitions `Benzecri.DemiEspaceFermeDe` (instance
  `demiEspaceFermeDe_demiPlan`), `Benzecri.ProprieteIII` (instance
  `demiDisqueEuclide_proprietes`), `Benzecri.DemiEspaceDe` and `Benzecri.ProprieteIIIlarge`
  (instances `demiEspaceDe_demiPlan`, `demiDisqueEuclide_proprieteIIIlarge`). Imprecise in
  dimension 0: `Benzecri.reunion_convexes_dimZero`. The reading « H = L admitted » is needed:
  `Benzecri.sommet_carre_sans_demiEspace`. Instance: `Benzecri.demiDisqueEuclide_proprietes` (a
  closed half of the closed disc: I, II and III).

> **Théorème 1.** Soit $W$ un convexe compact dans un espace vectoriel de dimension finie, $V$
> une partie non vide compacte convexe de $W$; alors les trois propriétés ci-dessous sont
> équivalentes :
> I$(V, W)$;
> II$(V, W)$;
> III$(V, W)$ : le support de $V$ est une variété d'appui $L$ de $W$, et $V$ est
> l'intersection de $W$ avec un demi-espace $H$ de $L$ (éventuellement, $H\cap W$ peut être
> égal à $L\cap W$).

## The proof formalized

The printed lead-in names Props. 7, 8 and 4. I ⇔ II is Prop. 8 (`proprietes_I_II`, and
`proprietes_I_II_of_ne` when `V ≠ W`; local convexity of a finite-dimensional Hausdorff TVS is
`locallyConvexSpace_of_finiteDimensional`). I ⇒ III: the support `L` of `V` is a variété d'appui
(Prop. 2, `isVarieteAppui_affineSpan_of_proprieteI`) and `I(V, L ∩ W)` (Prop. 4,
`proprieteI_iff_isVarieteAppui`); if `V = L ∩ W`, `H = L`; otherwise Prop. 7 in `L ∩ W`, whose
support is `L` (`exists_separe_fort`, the strong form of `hyperplan_separant`, with « fermé » from
compactness through `fermeLineaire_of_isClosed'`), gives a linear form `f`, non-constant on `L`,
with `V ⊆ {f ≤ c}` and `L ∩ W − V ⊆ {c < f}`, so `V = W ∩ (L ∩ {f ≤ c})`. III ⇒ I: `V ⊆ L ∩ W`,
`L ∩ W − V = L ∩ W ∩ {f > c}` (or `∅`) is convex, then Prop. 4 `⇐`
(`proprieteI_of_isVarieteAppui`, i.e. Prop. 3 with `C = V`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $W$ un convexe compact » | ✓ carried: `IsCompact W`, `Convex ℝ W`; I ⇔ III uses convexity of `W` only |
| « un espace vectoriel de dimension finie » | ✓ carried: `[FiniteDimensional ℝ E]`, `E` a Hausdorff TVS (`[IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]`); I ⇔ III holds in every dimension |
| « $V$ une partie non vide compacte convexe de $W$ » | ✓ carried: `V.Nonempty`, `IsCompact V`, `Convex ℝ V`, `V ⊆ W`; I ⇒ III uses `V` closed only |
| (unprinted) `E ≠ 0` | ⚠ strengthened: `[Nontrivial E]` in `reunion_convexes_affine` (only for the implications into II); not needed when `V ≠ W` (`reunion_convexes_affine_of_ne`); necessary: `reunion_convexes_dimZero` |
| « un demi-espace $H$ de $L$ (éventuellement, $H\cap W$ peut être égal à $L\cap W$) » | reading: a closed half-space `L ∩ {f ≤ c}` of `L` (`f` linear, non-constant on `L`) **or `L` itself** (`ProprieteIII`); III ⇒ I is proved for every reading (open or closed, degenerate or not: `ProprieteIIIlarge`) |

## SCOPE (disclosed)

* The label is **not marked**, for two reasons, both degenerate cases:
  (i) In `E = 0`, `V = W = {0}` satisfies every printed hypothesis and I, III, but not II
  (there is no open half-space, `reunion_convexes_dimZero`): Theorem 1 is imprecise there, exactly
  as Prop. 8 is (OQ-165 (d)); it holds in full for `E ≠ 0`, and for every `E` when `V ≠ W`.
  (ii) « un demi-espace $H$ de $L$ » is read as « a closed half-space of `L`, or `L` itself ».
  Under the strict reading (a proper half-space only), I ⇒ III fails when `V` is a point: the
  vertex `(0, 0)` of the square has I (`sommet_carre_proprietes`), its support is a point, which
  has no half-space (`sommet_carre_sans_demiEspace`). The printed parenthesis « $H\cap W$ peut
  être égal à $L\cap W$ » is the case `V = L ∩ W`; when `dim L ≥ 1` a proper closed half-space
  containing the compact `L ∩ W` exists, so the reading changes the statement only for `dim L = 0`.
* The half-spaces of `L` are traces `L ∩ {f ≤ c}` of linear forms of `E`; in finite dimension
  every linear form is continuous, and every affine form on `L` is such a trace.
* « le support de $V$ est une variété d'appui $L$ » is read with `L := affineSpan ℝ V`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A *closed half-space* of the affine subspace `L`: `L ∩ {f ≤ c}` for a linear form `f` not
constant on `L`. -/
def DemiEspaceFermeDe (L : AffineSubspace ℝ E) (H : Set E) : Prop :=
  ∃ f : E →ₗ[ℝ] ℝ, (∃ x ∈ L, ∃ y ∈ L, f x ≠ f y) ∧ ∃ c : ℝ, H = (L : Set E) ∩ {x | f x ≤ c}

/-- **`III(V, W)`**, in the reading « a closed half-space `H` of `L`, or `H = L` »: the support
`L` of `V` is a variété d'appui of `W` and `V = H ∩ W`. -/
def ProprieteIII (V W : Set E) : Prop :=
  IsVarieteAppui W (affineSpan ℝ V) ∧ ∃ H : Set E,
    (DemiEspaceFermeDe (affineSpan ℝ V) H ∨ H = affineSpan ℝ V) ∧ V = H ∩ W

/-- The widest reading of « un demi-espace $H$ de $L$ »: `L ∩ {f ≤ c}` or `L ∩ {f < c}` for any
linear form `f` (constant forms included, so `L` and `∅` are admitted). -/
def DemiEspaceDe (L : AffineSubspace ℝ E) (H : Set E) : Prop :=
  ∃ f : E →ₗ[ℝ] ℝ, ∃ c : ℝ,
    H = (L : Set E) ∩ {x | f x ≤ c} ∨ H = (L : Set E) ∩ {x | f x < c}

/-- `III(V, W)` in the widest reading (`DemiEspaceDe`). -/
def ProprieteIIIlarge (V W : Set E) : Prop :=
  IsVarieteAppui W (affineSpan ℝ V) ∧ ∃ H : Set E, DemiEspaceDe (affineSpan ℝ V) H ∧ V = H ∩ W

theorem DemiEspaceFermeDe.demiEspaceDe {L : AffineSubspace ℝ E} {H : Set E}
    (h : DemiEspaceFermeDe L H) : DemiEspaceDe L H := by
  obtain ⟨f, -, c, rfl⟩ := h
  exact ⟨f, c, Or.inl rfl⟩

theorem ProprieteIII.large {V W : Set E} (h : ProprieteIII V W) : ProprieteIIIlarge V W := by
  obtain ⟨hL, H, hH | rfl, hV⟩ := h
  · exact ⟨hL, H, hH.demiEspaceDe, hV⟩
  · refine ⟨hL, _, ⟨0, 0, Or.inl ?_⟩, hV⟩
    ext x; simp

/-- **Theorem 1, III ⇒ I**, for every reading of « demi-espace de L », no topology. -/
theorem proprieteI_of_proprieteIIIlarge {V W : Set E} (hW : Convex ℝ W)
    (h : ProprieteIIIlarge V W) : ProprieteI V W := by
  obtain ⟨hL, H, ⟨f, c, hH⟩, hV⟩ := h
  have hHL : H ⊆ (affineSpan ℝ V : Set E) := by
    rcases hH with rfl | rfl <;> exact inter_subset_left
  refine proprieteI_of_isVarieteAppui hW hL ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' := hV ▸ hx
    exact ⟨hHL hx'.1, hx'.2⟩
  · rcases hH with rfl | rfl
    · rw [hV]
      exact ((affineSpan ℝ V).convex.inter (convex_halfSpace_le f.isLinear c)).inter hW
    · rw [hV]
      exact ((affineSpan ℝ V).convex.inter (convex_halfSpace_lt f.isLinear c)).inter hW
  · rcases hH with hH | hH
    · have e : ((affineSpan ℝ V : Set E) ∩ W) \ V =
          ((affineSpan ℝ V : Set E) ∩ W) ∩ {x | c < f x} := by
        ext x
        constructor
        · rintro ⟨⟨hxL, hxW⟩, hxV⟩
          refine ⟨⟨hxL, hxW⟩, show c < f x from lt_of_not_ge fun hle => hxV ?_⟩
          rw [hV, hH]; exact ⟨⟨hxL, hle⟩, hxW⟩
        · rintro ⟨⟨hxL, hxW⟩, hlt⟩
          refine ⟨⟨hxL, hxW⟩, fun hxV => ?_⟩
          rw [hV, hH] at hxV
          exact absurd (show f x ≤ c from hxV.1.2) (not_le.2 hlt)
      rw [e]
      exact ((affineSpan ℝ V).convex.inter hW).inter (convex_halfSpace_gt f.isLinear c)
    · have e : ((affineSpan ℝ V : Set E) ∩ W) \ V =
          ((affineSpan ℝ V : Set E) ∩ W) ∩ {x | c ≤ f x} := by
        ext x
        constructor
        · rintro ⟨⟨hxL, hxW⟩, hxV⟩
          refine ⟨⟨hxL, hxW⟩, show c ≤ f x from le_of_not_gt fun hlt => hxV ?_⟩
          rw [hV, hH]; exact ⟨⟨hxL, hlt⟩, hxW⟩
        · rintro ⟨⟨hxL, hxW⟩, hle⟩
          refine ⟨⟨hxL, hxW⟩, fun hxV => ?_⟩
          rw [hV, hH] at hxV
          exact absurd (show f x < c from hxV.1.2) (not_lt.2 hle)
      rw [e]
      exact ((affineSpan ℝ V).convex.inter hW).inter (convex_halfSpace_ge f.isLinear c)

theorem proprieteI_of_proprieteIII {V W : Set E} (hW : Convex ℝ W) (h : ProprieteIII V W) :
    ProprieteI V W :=
  proprieteI_of_proprieteIIIlarge hW h.large

end Defs

section Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

omit [T2Space E] in
/-- **Theorem 1, I ⇒ III**, in every dimension (`V` closed suffices). -/
theorem proprieteIII_of_proprieteI {V W : Set E} (hW : Convex ℝ W) (hV : IsClosed V)
    (hne : V.Nonempty) (hI : ProprieteI V W) : ProprieteIII V W := by
  have hL := isVarieteAppui_affineSpan_of_proprieteI hW hne hI
  obtain ⟨-, hI'⟩ := (proprieteI_iff_isVarieteAppui hW hI.2.1 hI.1 hne).1 hI
  refine ⟨hL, ?_⟩
  set W' : Set E := (affineSpan ℝ V : Set E) ∩ W with hW'
  by_cases hVW : V = W'
  · refine ⟨_, Or.inr rfl, ?_⟩
    exact hVW
  have hU : (W' \ V).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    exact hVW (hI'.1.antisymm h)
  obtain ⟨f, c, -, hfV, hfU, -, -⟩ := exists_separe_fort ((affineSpan ℝ V).convex.inter hW)
    hI'.2.1 hI'.2.2 (fermeLineaire_of_isClosed' hV) hI'.1 inter_subset_left hU
  obtain ⟨v, hv⟩ := hne
  obtain ⟨u, hu⟩ := hU
  refine ⟨_, Or.inl ⟨f, ⟨v, subset_affineSpan ℝ V hv, u, hu.1.1,
    ne_of_lt (lt_of_le_of_lt (hfV v hv) (hfU u hu))⟩, c, rfl⟩, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨⟨subset_affineSpan ℝ V hx, hfV x hx⟩, hI.1 hx⟩
  · rintro ⟨⟨hxL, hxc⟩, hxW⟩
    by_contra hxV
    exact absurd hxc (not_le.2 (hfU x ⟨⟨hxL, hxW⟩, hxV⟩))

omit [T2Space E] in
/-- **Theorem 1, I ⇔ III**, in every dimension, `E = 0` included. -/
theorem proprieteI_iff_proprieteIII {V W : Set E} (hW : Convex ℝ W) (hV : IsClosed V)
    (hne : V.Nonempty) : ProprieteI V W ↔ ProprieteIII V W :=
  ⟨proprieteIII_of_proprieteI hW hV hne, proprieteI_of_proprieteIII hW⟩

/-- A finite-dimensional real Hausdorff TVS is locally convex (its topology is the canonical
one). -/
theorem locallyConvexSpace_of_finiteDimensional [FiniteDimensional ℝ E] :
    LocallyConvexSpace ℝ E := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  have h := LocallyConvexSpace.induced (t := inferInstance) (e.toLinearEquiv.toLinearMap)
  have heq : (inferInstance : TopologicalSpace E) = TopologicalSpace.induced e inferInstance :=
    e.toHomeomorph.isInducing.eq_induced
  convert h
  exact heq

variable [FiniteDimensional ℝ E]

/-- **Ch. 3 § 5, Theorem 1**, for `E ≠ 0`: I(V, W), II(V, W), III(V, W) are equivalent. -/
theorem reunion_convexes_affine [Nontrivial E] {V W : Set E} (hW : IsCompact W)
    (hWc : Convex ℝ W) (hV : IsCompact V) (hVc : Convex ℝ V) (hne : V.Nonempty) (hVW : V ⊆ W) :
    List.TFAE [ProprieteI V W, ProprieteII V W, ProprieteIII V W] := by
  haveI := locallyConvexSpace_of_finiteDimensional (E := E)
  have h12 := proprietes_I_II hW hWc hV hVc hne hVW
  have h13 := proprieteI_iff_proprieteIII hWc hV.isClosed hne (W := W)
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_finish

/-- **Ch. 3 § 5, Theorem 1**, for `V ≠ W`, in every finite-dimensional space. -/
theorem reunion_convexes_affine_of_ne {V W : Set E} (hW : IsCompact W)
    (hWc : Convex ℝ W) (hV : IsCompact V) (hVc : Convex ℝ V) (hne : V.Nonempty) (hVW : V ⊆ W)
    (hVW' : V ≠ W) :
    List.TFAE [ProprieteI V W, ProprieteII V W, ProprieteIII V W] := by
  haveI := locallyConvexSpace_of_finiteDimensional (E := E)
  have h12 := proprietes_I_II_of_ne hW hWc hV hVc hne hVW hVW'
  have h13 := proprieteI_iff_proprieteIII hWc hV.isClosed hne (W := W)
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_finish

end Topology

/-! ### Dimension zero, and the reading of « demi-espace de L » -/

/-- In `ℝ⁰ = Fin 0 → ℝ`, `V = W = {0}` satisfies every hypothesis of Theorem 1, I and III, but
not II. Theorem 1 is imprecise there. -/
theorem reunion_convexes_dimZero :
    IsCompact (univ : Set (Fin 0 → ℝ)) ∧ Convex ℝ (univ : Set (Fin 0 → ℝ)) ∧
      (univ : Set (Fin 0 → ℝ)).Nonempty ∧
      ProprieteI (univ : Set (Fin 0 → ℝ)) univ ∧ ProprieteIII (univ : Set (Fin 0 → ℝ)) univ ∧
      ¬ ProprieteII (univ : Set (Fin 0 → ℝ)) univ := by
  have hI : ProprieteI (univ : Set (Fin 0 → ℝ)) univ :=
    ⟨subset_rfl, convex_univ, by rw [sdiff_self]; exact convex_empty⟩
  exact ⟨isCompact_univ, convex_univ, univ_nonempty, hI,
    proprieteIII_of_proprieteI convex_univ isClosed_univ univ_nonempty hI,
    proprieteII_subsingleton_false _ _⟩

/-- The vertex `(0, 0)` of the square: `I` holds, but its support, a point, has no closed
half-space; `III` holds only with `H = L`. -/
theorem sommet_carre_sans_demiEspace :
    ProprieteI {((0 : ℝ), (0 : ℝ))} square ∧
      ¬ ∃ H : Set (ℝ × ℝ), DemiEspaceFermeDe (affineSpan ℝ {((0 : ℝ), (0 : ℝ))}) H := by
  refine ⟨sommet_carre_proprietes.1, ?_⟩
  rintro ⟨H, f, ⟨x, hx, y, hy, hxy⟩, -⟩
  rw [AffineSubspace.mem_affineSpan_singleton] at hx hy
  subst hx; subst hy
  exact hxy rfl

/-! ### Instances -/

/-- The closed unit disc of the Euclidean plane. -/
noncomputable abbrev disqueEuclide : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 1

/-- Its closed left half. -/
noncomputable abbrev demiDisqueEuclide : Set (EuclideanSpace ℝ (Fin 2)) :=
  disqueEuclide ∩ {x | x 0 ≤ 0}

/-- **Instance of `DemiEspaceFermeDe`**: the closed half-plane `{x | x 0 ≤ 0}` of the plane. -/
theorem demiEspaceFermeDe_demiPlan :
    DemiEspaceFermeDe (⊤ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) {x | x 0 ≤ 0} := by
  refine ⟨(EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap,
    ⟨0, trivial, EuclideanSpace.single 0 1, trivial, ?_⟩, 0, ?_⟩
  · simp
  · ext x; simp

/-- **Theorem 1, instance**: a closed half of the closed disc has I, II and III. -/
theorem demiDisqueEuclide_proprietes :
    ProprieteI demiDisqueEuclide disqueEuclide ∧ ProprieteII demiDisqueEuclide disqueEuclide ∧
      ProprieteIII demiDisqueEuclide disqueEuclide := by
  have hI : ProprieteI demiDisqueEuclide disqueEuclide := by
    refine ⟨inter_subset_left, (convex_closedBall _ _).inter
      (convex_halfSpace_le (EuclideanSpace.proj (0 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap.isLinear 0), ?_⟩
    have e : disqueEuclide \ demiDisqueEuclide = disqueEuclide ∩ {x | 0 < x 0} := by
      ext x
      simp only [demiDisqueEuclide, mem_sdiff, mem_inter_iff, mem_setOf_eq, not_and, not_le]
      tauto
    rw [e]
    exact (convex_closedBall _ _).inter (convex_halfSpace_gt (EuclideanSpace.proj (0 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap.isLinear 0)
  have hne : demiDisqueEuclide.Nonempty := ⟨0, by simp [demiDisqueEuclide, disqueEuclide]⟩
  have hc : IsCompact demiDisqueEuclide :=
    (isCompact_closedBall _ _).inter_right (isClosed_le (EuclideanSpace.proj (0 : Fin 2)).continuous
      continuous_const)
  have h := reunion_convexes_affine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (convex_closedBall _ _) hc hI.2.1 hne hI.1
  exact ⟨hI, (h.out 0 1).1 hI, (h.out 0 2).1 hI⟩

/-- **Instance of `DemiEspaceDe`**: the closed half-plane `{x | x 0 ≤ 0}` of the plane. -/
theorem demiEspaceDe_demiPlan :
    DemiEspaceDe (⊤ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) {x | x 0 ≤ 0} :=
  demiEspaceFermeDe_demiPlan.demiEspaceDe

/-- **Instance of `ProprieteIIIlarge`**: a closed half of the closed disc. -/
theorem demiDisqueEuclide_proprieteIIIlarge :
    ProprieteIIIlarge demiDisqueEuclide disqueEuclide :=
  demiDisqueEuclide_proprietes.2.2.large

end Benzecri
