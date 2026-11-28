import Benzecri.Chapter3.Facettes

/-!
# Chapter 3 § 1 — variétés d'appui of a convex set, Prop. 5 (finite dimension), the Remark, Prop. 6

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 1, journal p. 261; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (checked against the scan, PDF p. 34).
Target T-bz-c3-appui. « variété linéaire » is `AffineSubspace ℝ E`, « support » is `affineSpan`,
as in `Benzecri.Chapter3.Facettes`.

* **`bzdef:c3s1d3_variete_appui`** — `benzecri1960_ch3.tex:186` (Déf. 3, l.186–190; the
  α-form l.192–193; the commentary l.195–196) — `Benzecri.IsVarieteAppui`, the α-form
  `isVarieteAppui_iff_alphaW`, Bourbaki's form `isVarieteAppui_iff_openSegment`, the whole space
  `isVarieteAppui_top_iff`, a facette's support `isVarieteAppui_affineSpan_facette`, « la
  réciproque n'est pas vraie » in finite dimension `antidiag_appui_not_support`. Instance: `lineY0_isVarieteAppui`, `diag_not_isVarieteAppui`.
* **`bzprop:c3s1p5_appui_facette_dim_finie`** — `benzecri1960_ch3.tex:210` (Prop. 5,
  l.210–213, proof l.215–219) — `exists_facette_support_inter_eq` (the paper's hypothesis),
  `exists_facette_support_inter_eq_of_finiteDimensional` (only `L ∩ W` finite-dimensional).
* **`bzrem:c3s1r2_support_interieur_fermeture`** — `benzecri1960_ch3.tex:221` (Remarque,
  l.221–227) — 1° `remarque_facette_interieur` (and topology-free `exists_facette_support_eq`),
  2° `remarque_fermeture_compacte`, `inter_eq_closure_facette`.
* **`bzprop:c3s1p6_alpha_induit`** — `benzecri1960_ch3.tex:229` (Prop. 6, l.229–234, proof
  l.236–241) — `alphaW_inter_iff`, `alphaW_induit`; the proof's consequence
  `facetteOf_inter_eq`.

> **Définition 3.** Une variété linéaire $S$ est dite *variété d'appui* de $W$ si $S\cap W$ est
> non vide et saturé pour la relation d'équivalence $F_W$ (cette définition équivaut à celle de
> Bourbaki, *Espaces vectoriels topologiques*, chap. II, p. 83).
>
> D'après la proposition 3, il est équivalent de dire que $A\in S\cap W$ et $A\,\alpha\,B$
> impliquent $B\in S\cap W$.
>
> L'espace tout entier est une variété d'appui, le support d'une facette est une variété
> d'appui; la réciproque n'est pas vraie : on trouve facilement, dans un espace de dimension
> finie, un convexe $W$ et une variété d'appui $S$ telle que $S\cap W$ ait un support distinct
> de $S$; […]
>
> **Proposition 5.** Si $W$ est un convexe dont le support $E$ est de dimension finie, pour
> toute variété d'appui $L$ à $W$ il existe une facette $F$ dont le support $S$ est tel que
> $S\cap W=L\cap W$.
>
> **Remarque.** 1° $E$ est le support d'une facette de $W$ qui n'est autre que son intérieur;
> 2° Si $W$ est un convexe compact de dimension finie, $L\cap W$ n'est autre que la fermeture
> compacte $E$ de $F$. [sic: read $\bar F$]
>
> **Proposition 6.** Soit $L$ une variété linéaire, $W$ un convexe $W'=W\cap L=\emptyset$
> [sic: read $\neq\emptyset$]. Alors la relation $\alpha(W')$ est induite par la relation
> $\alpha(W)$. […] si $L$ est une variété d'appui à $W$, la facette d'un point $M\in L\cap W$,
> relativement au convexe $W$ n'est autre que sa facette relativement au convexe $L\cap W$.

## The proofs formalized

Déf. 3's α-form: the facette of `A ∈ S ∩ W` lies in `S` (saturation), hence so does its support,
and Prop. 2 puts every `B` with `A α B` in that support. Prop. 5 does not go through a « point
interne » of `S ∩ W`: among the points of `L ∩ W` take one, `A₀`, whose facette has a support of
maximal dimension (finite dimension bounds it); for `P ∈ L ∩ W` the midpoint `B` of `A₀ P` has
`B α A₀`, so the support of `B`'s facette contains that of `A₀`'s, with the same dimension, hence
equals it, and `B α P` puts `P` in it (Prop. 2). The Remark's 1° is Prop. 5 for `L = E`, with
the facette identified with the intrinsic interior by `interieur_of_fw` (one direction) and an
extension argument (the other). 2°: for `A ∈ F` and `P ∈ L ∩ W`, the half-open segment `[A, P)`
lies in `F`, so `P ∈ F̄`; `L ∩ W = S ∩ W` is closed because `S` has finite dimension. Prop. 6 is
`alphaW_iff_extend`: `A + ε(A − B)` lies in `L` when `A, B` do.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « une variété linéaire $S$ » | ✓ carried: `S : AffineSubspace ℝ E` |
| « $S\cap W$ non vide et saturé pour $F_W$ » | ✓ carried: `((S : Set E) ∩ W).Nonempty` and `A ∈ S ∩ W → FW W A B → B ∈ S ∩ W` |
| « un convexe $W$ » | ✓ carried: `Convex ℝ W` (Déf. 3 itself is defined for every `W`) |
| Prop. 5: « le support $E$ est de dimension finie » | ✓ carried: `FiniteDimensional ℝ (affineSpan ℝ W).direction`; ⚠ weakened in the second form (only `L ∩ W`) |
| Remark 1°: the topology of $E$ | ✓ carried: any Hausdorff topological vector space structure on the ambient space (its trace on the finite-dimensional support is the canonical one); « son intérieur » is `intrinsicInterior ℝ W` |
| Remark 2°: « $W$ compact de dimension finie » | ✓ carried: `IsCompact W` and finite-dimensional support; ⚠ weakened in `inter_eq_closure_facette` (`IsClosed W`) |
| Prop. 6: « $W'=W\cap L\neq\emptyset$ » | ⚠ weakened: `alphaW_inter_iff` holds without it; `alphaW_induit` carries it as printed (corrected) |

## SCOPE (disclosed)

* Prop. 6 is printed « $W'=W\cap L=\emptyset$ », flagged `[sic]` in the transcription: the
  reading « $\neq\emptyset$ » is formalized (`alphaW_induit`), and the statement needs no
  non-emptiness at all (`alphaW_inter_iff`). « induite » is read: for `A, B ∈ W ∩ L`,
  `A α(W′) B ↔ A α(W) B`.
* The Remark's 2° prints « la fermeture compacte $E$ de $F$ », flagged `[sic]`: read $\bar F$,
  the closure of the facette `F` of Prop. 5. Its 1° is read for `W ≠ ∅` (Prop. 5's context: a
  variété d'appui exists only then; for `W = ∅` there is no facette at all).
* Déf. 3's « cette définition équivaut à celle de Bourbaki » is formalized against Bourbaki's
  definition as we read it (`V ∩ W ≠ ∅`, and an open segment of `W` meeting `V` has both ends in
  `V`): `isVarieteAppui_iff_openSegment`. The Bourbaki text is not in the hub; the reading is a
  question.
* The infinite-dimensional ℵ₀-simplex example of the commentary (l.196–207) is not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 3 and its commentary -/

/-- **Déf. 3.** `S` is a *variété d'appui* of `W`: `S ∩ W` is non-empty and saturated for `F_W`. -/
def IsVarieteAppui (W : Set E) (S : AffineSubspace ℝ E) : Prop :=
  ((S : Set E) ∩ W).Nonempty ∧
    ∀ ⦃A B : E⦄, A ∈ (S : Set E) ∩ W → FW W A B → B ∈ (S : Set E) ∩ W

/-- **Déf. 3, α-form** (l.192–193): « $A\in S\cap W$ et $A\,\alpha\,B$ impliquent
$B\in S\cap W$ ». -/
theorem isVarieteAppui_iff_alphaW {W : Set E} (hW : Convex ℝ W) {S : AffineSubspace ℝ E} :
    IsVarieteAppui W S ↔ ((S : Set E) ∩ W).Nonempty ∧
      ∀ ⦃A B : E⦄, A ∈ (S : Set E) ∩ W → AlphaW W A B → B ∈ (S : Set E) ∩ W := by
  refine ⟨fun ⟨hne, hsat⟩ => ⟨hne, fun A B hA hAB => ?_⟩,
    fun ⟨hne, h⟩ => ⟨hne, fun A B hA hAB => h hA hAB.1⟩⟩
  have hFS : affineSpan ℝ (facetteOf W A) ≤ S := by
    rw [affineSpan_le]
    intro C hC
    exact (hsat hA hC).1
  exact ⟨hFS ((alphaW_iff_mem_support hW (isFacette_facetteOf hA.2) (mem_facetteOf_self hA.2)
    hAB.mem_right).1 hAB), hAB.mem_right⟩

/-- **Déf. 3, Bourbaki's form**: `S ∩ W ≠ ∅`, and an open segment of `W` meeting `S` has both
ends in `S`. -/
theorem isVarieteAppui_iff_openSegment {W : Set E} (hW : Convex ℝ W) {S : AffineSubspace ℝ E} :
    IsVarieteAppui W S ↔ ((S : Set E) ∩ W).Nonempty ∧
      ∀ x ∈ W, ∀ y ∈ W, (openSegment ℝ x y ∩ S).Nonempty → x ∈ S ∧ y ∈ S := by
  rw [isVarieteAppui_iff_alphaW hW]
  refine ⟨fun ⟨hne, h⟩ => ⟨hne, fun x hx y hy ⟨z, hz, hzS⟩ => ?_⟩,
    fun ⟨hne, h⟩ => ⟨hne, fun A B hA hAB => ?_⟩⟩
  · have hzW : z ∈ W := hW.segment_subset hx hy (openSegment_subset_segment _ _ _ hz)
    have hzx : AlphaW W z x :=
      Or.inl ⟨y, hW.segment_subset hy hx, by rwa [openSegment_symm]⟩
    have hzy : AlphaW W z y := Or.inl ⟨x, hW.segment_subset hx hy, hz⟩
    exact ⟨(h ⟨hzS, hzW⟩ hzx).1, (h ⟨hzS, hzW⟩ hzy).1⟩
  · obtain ⟨A', hs, hA'⟩ := alphaW_iff_openSegment.1 hAB
    exact ⟨(h A' (hs (left_mem_segment _ _ _)) B (hs (right_mem_segment _ _ _))
      ⟨A, hA', hA.1⟩).2, hAB.mem_right⟩

/-- « L'espace tout entier est une variété d'appui » (for `W ≠ ∅`, and only then). -/
theorem isVarieteAppui_top_iff {W : Set E} : IsVarieteAppui W ⊤ ↔ W.Nonempty := by
  simp only [IsVarieteAppui, AffineSubspace.top_coe, univ_inter]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ hAB => hAB.1.mem_right⟩⟩

/-- « le support d'une facette est une variété d'appui ». -/
theorem isVarieteAppui_affineSpan_facette {W : Set E} (hW : Convex ℝ W) {F : Set E}
    (hF : IsFacette W F) : IsVarieteAppui W (affineSpan ℝ F) := by
  obtain ⟨C, hC⟩ := hF.nonempty
  refine ⟨⟨C, subset_affineSpan ℝ F hC, hF.subset hC⟩, fun A B hA hAB => ?_⟩
  have hCA : AlphaW W C A := (alphaW_iff_mem_support hW hF hC hA.2).2 hA.1
  have hCB : AlphaW W C B := alphaW_trans hW hCA hAB.1
  exact ⟨(alphaW_iff_mem_support hW hF hC hCB.mem_right).1 hCB, hCB.mem_right⟩

/-! ### Prop. 6 -/

/-- **Prop. 6** (no non-emptiness needed): `α(W ∩ L)` is the trace of `α(W)` on `W ∩ L`. -/
theorem alphaW_inter_iff {W : Set E} (hW : Convex ℝ W) (L : AffineSubspace ℝ E) {A B : E} :
    AlphaW (W ∩ L) A B ↔ A ∈ L ∧ B ∈ L ∧ AlphaW W A B := by
  have hWL : Convex ℝ (W ∩ L) := hW.inter L.convex
  rw [alphaW_iff_extend hWL, alphaW_iff_extend hW]
  constructor
  · rintro ⟨hA, hB, ε, hε, hP⟩
    exact ⟨hA.2, hB.2, hA.1, hB.1, ε, hε, hP.1⟩
  · rintro ⟨hAL, hBL, hA, hB, ε, hε, hP⟩
    refine ⟨⟨hA, hAL⟩, ⟨hB, hBL⟩, ε, hε, hP, ?_⟩
    have := AffineSubspace.smul_vsub_vadd_mem L ε hAL hBL hAL
    simpa [vsub_eq_sub, vadd_eq_add, add_comm] using this

/-- **Prop. 6** as printed (with the `[sic]` read « $W'=W\cap L\neq\emptyset$ »). -/
theorem alphaW_induit {W : Set E} (hW : Convex ℝ W) (L : AffineSubspace ℝ E)
    (_hne : (W ∩ L).Nonempty) :
    ∀ A ∈ W ∩ L, ∀ B ∈ W ∩ L, (AlphaW (W ∩ L) A B ↔ AlphaW W A B) := by
  intro A hA B hB
  rw [alphaW_inter_iff hW L]
  exact ⟨fun h => h.2.2, fun h => ⟨hA.2, hB.2, h⟩⟩

/-- The consequence drawn in Prop. 6's proof: for `L` a variété d'appui, the facette of
`M ∈ L ∩ W` relative to `W` is its facette relative to `L ∩ W`. -/
theorem facetteOf_inter_eq {W : Set E} (hW : Convex ℝ W) {L : AffineSubspace ℝ E}
    (hL : IsVarieteAppui W L) {M : E} (hM : M ∈ W ∩ L) :
    facetteOf (W ∩ L) M = facetteOf W M := by
  ext B
  simp only [facetteOf, mem_setOf_eq, FW, alphaW_inter_iff hW L]
  constructor
  · rintro ⟨⟨-, -, h1⟩, -, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hB := hL.2 ⟨hM.2, hM.1⟩ ⟨h1, h2⟩
    exact ⟨⟨hM.2, hB.1, h1⟩, hB.1, hM.2, h2⟩

/-! ### Prop. 5 -/

/-- **Prop. 5**, under the weaker hypothesis that `L ∩ W` has a finite-dimensional support:
some facette `F` has support `S = affineSpan (L ∩ W)` and `S ∩ W = L ∩ W`. -/
theorem exists_facette_support_inter_eq_of_finiteDimensional {W : Set E} (hW : Convex ℝ W)
    {L : AffineSubspace ℝ E} (hL : IsVarieteAppui W L)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ ((L : Set E) ∩ W)).direction) :
    ∃ F, IsFacette W F ∧ affineSpan ℝ F = affineSpan ℝ ((L : Set E) ∩ W) ∧
      (affineSpan ℝ F : Set E) ∩ W = (L : Set E) ∩ W := by
  classical
  set T : Set E := (L : Set E) ∩ W with hT
  set S := affineSpan ℝ T with hS
  have hsub : ∀ A ∈ T, facetteOf W A ⊆ T := fun A hA C hC => hL.2 hA hC
  have hle : ∀ A ∈ T, affineSpan ℝ (facetteOf W A) ≤ S := fun A hA =>
    affineSpan_mono ℝ (hsub A hA)
  have hfinA : ∀ A ∈ T, FiniteDimensional ℝ (affineSpan ℝ (facetteOf W A)).direction :=
    fun A hA => Submodule.finiteDimensional_of_le (AffineSubspace.direction_le (hle A hA))
  let D : E → ℕ := fun A => Module.finrank ℝ (affineSpan ℝ (facetteOf W A)).direction
  have hbdd : BddAbove (D '' T) := ⟨Module.finrank ℝ S.direction, by
    rintro _ ⟨A, hA, rfl⟩
    exact Submodule.finrank_mono (AffineSubspace.direction_le (hle A hA))⟩
  obtain ⟨A₀, hA₀, hA₀max⟩ := Nat.sSup_mem (hL.1.image D) hbdd
  have hmax : ∀ A ∈ T, D A ≤ D A₀ := fun A hA => hA₀max ▸ le_csSup hbdd ⟨A, hA, rfl⟩
  have hA₀W : A₀ ∈ W := hA₀.2
  have hTF : T ⊆ affineSpan ℝ (facetteOf W A₀) := by
    intro P hP
    set B : E := (1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • P with hBdef
    have hBW : B ∈ W := hW hA₀W hP.2 (by norm_num) (by norm_num) (by norm_num)
    have hBL : B ∈ L := by
      have h := AffineSubspace.smul_vsub_vadd_mem L (1 / 2 : ℝ) hP.1 hA₀.1 hA₀.1
      have e : (1 / 2 : ℝ) • (P -ᵥ A₀) +ᵥ A₀ = B := by
        rw [vsub_eq_sub, vadd_eq_add, hBdef]; module
      rwa [e] at h
    have hBT : B ∈ T := ⟨hBL, hBW⟩
    have hBA : AlphaW W B A₀ := alphaW_midpoint hW hA₀W hP.2
    have hBP : AlphaW W B P := by
      have := alphaW_midpoint hW hP.2 hA₀W
      rwa [add_comm] at this
    have hle' : affineSpan ℝ (facetteOf W A₀) ≤ affineSpan ℝ (facetteOf W B) :=
      (facetteLE_iff_support_le hW (isFacette_facetteOf hBW) (isFacette_facetteOf hA₀W)).1
        ((facetteLE_facetteOf_iff hW hBW hA₀W).2 hBA)
    haveI := hfinA B hBT
    have hdir : (affineSpan ℝ (facetteOf W A₀)).direction =
        (affineSpan ℝ (facetteOf W B)).direction :=
      Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle')
        (le_antisymm (Submodule.finrank_mono (AffineSubspace.direction_le hle')) (hmax B hBT))
    have heq := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ⟨A₀, subset_affineSpan ℝ _ (mem_facetteOf_self hA₀W)⟩ hle'
    rw [heq]
    exact (alphaW_iff_mem_support hW (isFacette_facetteOf hBW) (mem_facetteOf_self hBW) hP.2).1
      hBP
  have hspan : affineSpan ℝ (facetteOf W A₀) = S :=
    le_antisymm (hle A₀ hA₀) (affineSpan_le.2 hTF)
  refine ⟨facetteOf W A₀, isFacette_facetteOf hA₀W, hspan, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxW⟩
    exact (isVarieteAppui_iff_alphaW hW).1 hL |>.2 hA₀
      ((alphaW_iff_mem_support hW (isFacette_facetteOf hA₀W) (mem_facetteOf_self hA₀W) hxW).2 hx)
  · intro hx
    exact ⟨hTF hx, hx.2⟩

/-- **Prop. 5.** If the support of the convex `W` is finite-dimensional, for every variété
d'appui `L` some facette `F` has a support `S` with `S ∩ W = L ∩ W`. -/
theorem exists_facette_support_inter_eq {W : Set E} (hW : Convex ℝ W)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ W).direction)
    {L : AffineSubspace ℝ E} (hL : IsVarieteAppui W L) :
    ∃ F, IsFacette W F ∧ (affineSpan ℝ F : Set E) ∩ W = (L : Set E) ∩ W := by
  haveI : FiniteDimensional ℝ (affineSpan ℝ ((L : Set E) ∩ W)).direction :=
    Submodule.finiteDimensional_of_le
      (AffineSubspace.direction_le (affineSpan_mono ℝ inter_subset_right))
  obtain ⟨F, hF, -, hFL⟩ := exists_facette_support_inter_eq_of_finiteDimensional hW hL this
  exact ⟨F, hF, hFL⟩

/-- **Remark 1°**, topology-free: the support of `W` is the support of a facette of `W`. -/
theorem exists_facette_support_eq {W : Set E} (hW : Convex ℝ W) (hne : W.Nonempty)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ W).direction) :
    ∃ F, IsFacette W F ∧ affineSpan ℝ F = affineSpan ℝ W := by
  have hL : IsVarieteAppui W ⊤ := isVarieteAppui_top_iff.2 hne
  have hfin' : FiniteDimensional ℝ (affineSpan ℝ (((⊤ : AffineSubspace ℝ E) : Set E) ∩ W)).direction := by
    rwa [AffineSubspace.top_coe, univ_inter]
  obtain ⟨F, hF, hspan, -⟩ := exists_facette_support_inter_eq_of_finiteDimensional hW hL hfin'
  rw [AffineSubspace.top_coe, univ_inter] at hspan
  exact ⟨F, hF, hspan⟩

/-! ### The Remark, topological -/

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

/-- **Remark 1°.** The support of `W` is the support of a facette of `W`, which is the
(intrinsic) interior of `W`. -/
theorem remarque_facette_interieur {W : Set E} (hW : Convex ℝ W) (hne : W.Nonempty)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ W).direction) :
    ∃ F, IsFacette W F ∧ affineSpan ℝ F = affineSpan ℝ W ∧ F = intrinsicInterior ℝ W := by
  classical
  obtain ⟨F, hF, hspan⟩ := exists_facette_support_eq hW hne hfin
  refine ⟨F, hF, hspan, Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hxW := hF.subset hx
    haveI : FiniteDimensional ℝ (affineSpan ℝ F).direction := hspan ▸ hfin
    obtain ⟨t, htF, htspan, hind⟩ := exists_affineIndependent ℝ E F
    have htfin : t.Finite := by
      haveI : Nonempty (affineSpan ℝ F) := ⟨⟨x, subset_affineSpan ℝ F hx⟩⟩
      let f : t → affineSpan ℝ F := fun p => ⟨p, subset_affineSpan ℝ F (htF p.2)⟩
      have hf : AffineIndependent ℝ f :=
        AffineIndependent.of_comp (affineSpan ℝ F).subtype (by exact hind)
      exact finite_set_of_fin_dim_affineIndependent ℝ hf
    have hts : (insert x t).Finite := htfin.insert x
    set tf := hts.toFinset with htf
    let A : Fin tf.card → E := fun i => (tf.equivFin.symm i : E)
    have hrange : range A = insert x t := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact hts.mem_toFinset.1 (tf.equivFin.symm i).2
      · intro hy
        exact ⟨tf.equivFin ⟨y, hts.mem_toFinset.2 hy⟩, by simp [A]⟩
    have hAF : ∀ i, A i ∈ F := by
      intro i
      have : A i ∈ insert x t := hrange ▸ mem_range_self i
      rcases this with h | h
      · rw [h]; exact hx
      · exact htF h
    have hpair : ∀ i j, FW W (A i) (A j) := by
      intro i j
      have hi := hAF i
      have hj := hAF j
      rw [hF.eq_facetteOf hW hx] at hi hj
      exact FW.trans hW (FW.symm hi) hj
    have hspanA : affineSpan ℝ (range A) = affineSpan ℝ W := by
      have hxt : x ∈ affineSpan ℝ t := by rw [htspan]; exact subset_affineSpan ℝ F hx
      rw [hrange, affineSpan_insert_eq_affineSpan ℝ hxt, htspan, hspan]
    set i₀ : Fin tf.card := tf.equivFin ⟨x, hts.mem_toFinset.2 (mem_insert x t)⟩
    have hAi₀ : A i₀ = x := by simp [A, i₀]
    have hN := interieur_of_fw hW A hpair i₀
    rw [hspanA, hAi₀] at hN
    have hxS : x ∈ affineSpan ℝ W := hspan ▸ subset_affineSpan ℝ F hx
    exact mem_intrinsicInterior.2 ⟨⟨x, hxS⟩,
      mem_interior_iff_mem_nhds.2 (preimage_coe_mem_nhds_subtype.2 hN), rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hx
    have hN : W ∈ 𝓝[(affineSpan ℝ W : Set E)] (y : E) :=
      preimage_coe_mem_nhds_subtype.1 (mem_interior_iff_mem_nhds.1 hy)
    have hyS : (y : E) ∈ affineSpan ℝ W := y.2
    have hyW : (y : E) ∈ W := mem_of_mem_nhdsWithin hyS hN
    obtain ⟨C, hC⟩ := hF.nonempty
    have hCW := hF.subset hC
    have hCS : C ∈ affineSpan ℝ W := subset_affineSpan ℝ W hCW
    let f : ℝ → E := fun t => (y : E) + t • ((y : E) - C)
    have hf : Tendsto f (𝓝 0) (𝓝[(affineSpan ℝ W : Set E)] (y : E)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => ?_⟩
      · have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
        simpa [f] using hc.tendsto 0
      · have := AffineSubspace.smul_vsub_vadd_mem _ t hyS hCS hyS
        simpa [f, vsub_eq_sub, vadd_eq_add, add_comm] using this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ W ∧ t ∈ Ioi 0 :=
      ((hf.eventually hN).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨t, ht, htpos⟩ := hev.exists
    have hyC : AlphaW W y C := (alphaW_iff_extend hW).2 ⟨hyW, hCW, t, htpos, ht⟩
    have hCy : AlphaW W C y := (alphaW_iff_mem_support hW hF hC hyW).2 (by rw [hspan]; exact hyS)
    rw [hF.eq_facetteOf hW hC]
    exact ⟨hCy, hyC⟩

/-- **Remark 2°**, for `W` closed (compactness is not needed): if a facette `F` has a support `S`
with `S ∩ W = L ∩ W`, then `L ∩ W = F̄`. -/
theorem inter_eq_closure_facette {W : Set E} (hW : Convex ℝ W) (hWc : IsClosed W)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ W).direction) {L : AffineSubspace ℝ E}
    {F : Set E} (hF : IsFacette W F)
    (hFL : (affineSpan ℝ F : Set E) ∩ W = (L : Set E) ∩ W) :
    (L : Set E) ∩ W = closure F := by
  obtain ⟨A, hA⟩ := hF.nonempty
  have hAW := hF.subset hA
  haveI : FiniteDimensional ℝ (affineSpan ℝ F).direction :=
    Submodule.finiteDimensional_of_le (AffineSubspace.direction_le (affineSpan_mono ℝ hF.subset))
  have hSclosed : IsClosed (affineSpan ℝ F : Set E) :=
    (AffineSubspace.isClosed_direction_iff _).1 (Submodule.closed_of_finiteDimensional _)
  rw [← hFL]
  apply Subset.antisymm
  · intro P hP
    have hPF : ∀ t ∈ Ioo (0 : ℝ) 1, A + t • (P - A) ∈ F := by
      intro t ht
      rw [hF.eq_facetteOf hW hA]
      have hQW : A + t • (P - A) ∈ W := hW.add_smul_sub_mem hAW hP.2 ⟨ht.1.le, ht.2.le⟩
      have hQS : A + t • (P - A) ∈ affineSpan ℝ F := by
        have h := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ F) t hP.1
          (subset_affineSpan ℝ F hA) (subset_affineSpan ℝ F hA)
        have e : t • (P -ᵥ A) +ᵥ A = A + t • (P - A) := by
          rw [vsub_eq_sub, vadd_eq_add]; abel
        rwa [e] at h
      refine ⟨(alphaW_iff_mem_support hW hF hA hQW).2 hQS,
        (alphaW_iff_extend hW).2 ⟨hQW, hAW, 1 - t, by linarith [ht.2], ?_⟩⟩
      have hs : t * (2 - t) ∈ Icc (0 : ℝ) 1 :=
        ⟨by nlinarith [ht.1, ht.2], by nlinarith [sq_nonneg (1 - t)]⟩
      have := hW.add_smul_sub_mem hAW hP.2 hs
      convert this using 1
      module
    have hlim : Tendsto (fun t : ℝ => A + t • (P - A)) (𝓝[<] 1) (𝓝 P) := by
      have hc : Continuous (fun t : ℝ => A + t • (P - A)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using this
    exact mem_closure_of_tendsto hlim
      (Filter.mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) hPF)
  · exact closure_minimal (fun x hx => ⟨subset_affineSpan ℝ F hx, hF.subset hx⟩)
      (hSclosed.inter hWc)

/-- **Remark 2°.** For `W` compact convex of finite dimension and `L` a variété d'appui, the
facette `F` of Prop. 5 satisfies `L ∩ W = F̄`, and `F̄` is compact. -/
theorem remarque_fermeture_compacte {W : Set E} (hW : Convex ℝ W) (hWc : IsCompact W)
    (hfin : FiniteDimensional ℝ (affineSpan ℝ W).direction) {L : AffineSubspace ℝ E}
    (hL : IsVarieteAppui W L) :
    ∃ F, IsFacette W F ∧ (affineSpan ℝ F : Set E) ∩ W = (L : Set E) ∩ W ∧
      (L : Set E) ∩ W = closure F ∧ IsCompact (closure F) := by
  obtain ⟨F, hF, hFL⟩ := exists_facette_support_inter_eq hW hfin hL
  have heq := inter_eq_closure_facette hW hWc.isClosed hfin hF hFL
  refine ⟨F, hF, hFL, heq, hWc.of_isClosed_subset isClosed_closure ?_⟩
  rw [← heq]
  exact inter_subset_right

end Topology

/-! ### The instance: the closed square `[0, 1]²` -/

/-- The closed unit square. -/
def square : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- The line `y = 0`. -/
def lineY0 : AffineSubspace ℝ (ℝ × ℝ) :=
  AffineSubspace.mk' 0 (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))

/-- The diagonal `y = x`. -/
def diag : AffineSubspace ℝ (ℝ × ℝ) :=
  AffineSubspace.mk' 0 (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ))

/-- The anti-diagonal `x + y = 0`. -/
def antidiag : AffineSubspace ℝ (ℝ × ℝ) :=
  AffineSubspace.mk' 0 (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ))

theorem convex_square : Convex ℝ square := (convex_Icc 0 1).prod (convex_Icc 0 1)

theorem mem_square {p : ℝ × ℝ} : p ∈ square ↔ (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) := by
  exact Iff.rfl

theorem mem_lineY0 {p : ℝ × ℝ} : p ∈ lineY0 ↔ p.2 = 0 := by
  simp [lineY0, AffineSubspace.mem_mk']

theorem mem_diag {p : ℝ × ℝ} : p ∈ diag ↔ p.1 - p.2 = 0 := by
  simp [diag, AffineSubspace.mem_mk']

theorem mem_antidiag {p : ℝ × ℝ} : p ∈ antidiag ↔ p.1 + p.2 = 0 := by
  simp [antidiag, AffineSubspace.mem_mk']

/-- Instance: the line `y = 0` is a variété d'appui of `[0, 1]²`. -/
theorem lineY0_isVarieteAppui : IsVarieteAppui square lineY0 := by
  rw [isVarieteAppui_iff_alphaW convex_square]
  refine ⟨⟨0, by simp [mem_lineY0], by simp [mem_square]⟩, fun A B hA hAB => ?_⟩
  obtain ⟨-, hB, ε, hε, hP⟩ := (alphaW_iff_extend convex_square).1 hAB
  have hA2 : A.2 = 0 := mem_lineY0.1 hA.1
  have hB' := mem_square.1 hB
  have hP' := mem_square.1 hP
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul, hA2] at hP'
  refine ⟨mem_lineY0.2 ?_, hB⟩
  nlinarith [hP'.2.1, hB'.2.1]

/-- Instance: the diagonal `y = x` is not a variété d'appui of `[0, 1]²`. -/
theorem diag_not_isVarieteAppui : ¬ IsVarieteAppui square diag := by
  rw [isVarieteAppui_iff_alphaW convex_square]
  rintro ⟨-, h⟩
  have hA : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ (diag : Set (ℝ × ℝ)) ∩ square :=
    ⟨mem_diag.2 (by norm_num), mem_square.2 (by norm_num)⟩
  have hAB : AlphaW square ((1 / 2 : ℝ), (1 / 2 : ℝ)) ((1 / 2 : ℝ), (0 : ℝ)) := by
    refine (alphaW_iff_extend convex_square).2 ⟨hA.2, mem_square.2 (by norm_num), 1, one_pos, ?_⟩
    refine mem_square.2 ?_
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    norm_num
  have := mem_diag.1 (h hA hAB).1
  norm_num at this

/-- « la réciproque n'est pas vraie », in finite dimension: the anti-diagonal `x + y = 0` is a
variété d'appui of `[0, 1]²` (it meets it in `{0}`) and is the support of no facette. -/
theorem antidiag_appui_not_support :
    IsVarieteAppui square antidiag ∧ ¬ ∃ F, IsFacette square F ∧ affineSpan ℝ F = antidiag := by
  have hzero : ∀ p ∈ (antidiag : Set (ℝ × ℝ)) ∩ square, p = 0 := by
    rintro p ⟨h1, h2⟩
    have h1' := mem_antidiag.1 h1
    have h2' := mem_square.1 h2
    ext
    · simp only [Prod.fst_zero]; linarith [h2'.1.1, h2'.2.1]
    · simp only [Prod.snd_zero]; linarith [h2'.1.1, h2'.2.1]
  constructor
  · rw [isVarieteAppui_iff_alphaW convex_square]
    refine ⟨⟨0, by simp [mem_antidiag], by simp [mem_square]⟩, fun A B hA hAB => ?_⟩
    obtain ⟨-, hB, ε, hε, hP⟩ := (alphaW_iff_extend convex_square).1 hAB
    have hA0 := hzero A hA
    have hB' := mem_square.1 hB
    have hP' := mem_square.1 hP
    simp only [hA0, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hP'
    refine ⟨mem_antidiag.2 ?_, hB⟩
    nlinarith [hP'.1.1, hP'.2.1, hB'.1.1, hB'.2.1]
  · rintro ⟨F, hF, hspan⟩
    have hFsub : F ⊆ {(0 : ℝ × ℝ)} := by
      intro x hx
      have hxS : x ∈ antidiag := hspan ▸ subset_affineSpan ℝ F hx
      exact hzero x ⟨hxS, hF.subset hx⟩
    have hmem : ((1 : ℝ), (-1 : ℝ)) ∈ affineSpan ℝ F := by
      rw [hspan]; exact mem_antidiag.2 (by norm_num)
    have := affineSpan_mono ℝ hFsub hmem
    rw [AffineSubspace.mem_affineSpan_singleton] at this
    have := congrArg Prod.fst this
    norm_num at this

end Benzecri
