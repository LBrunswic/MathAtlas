import Benzecri.Chapter3.BooleProjectif
import Benzecri.Chapter3.Sature
import Benzecri.Chapter3.FacetteDuale

/-!
# Chapter 3 § 2 (sphere) — Théorème 3 and its Corollary off the corrected domain: the open quarter, and closed `w`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal pp. 267–268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR). Target
T-bz-c3-boole-projectif-domaines, which settles the two cases `Chapter3/BooleProjectif.lean`
leaves open (its SCOPE, OQ-168). It decides nothing; no label is marked.

* `bzthm:c3s2t3_algebre_boole_projective` — `benzecri1960_ch3.tex:570` (Théorème 3,
  l.570–576), NOT marked (OQ-168 OPEN).
  (1) **Open `w`, a line in `F(w)`: refuted.** Relative to the open quarter `quartS` of `S(2)`
  (convex, open, support `S(2)`, noyau `∅`) no distributive lattice, a fortiori no Boolean
  algebra, has the inclusion of distinguished subvarieties as its order:
  `BooleProjectifDomainesInstance.not_distribLattice_quartS`,
  `BooleProjectifDomainesInstance.not_theoreme3_ouvert` (lattice core
  `BooleProjectifDomainesInstance.not_distrib_lines`). So openness alone does not suffice,
  as line-freeness alone does not (`BooleProjectifInstance.not_theoreme3`).
  (2) **Closed `w`: holds, degenerately.** For `w` closed, convex, of support `S(E)` (any real
  topological vector space), the conjugate pairs are `(S(E), ∅)` and `(∅, S(E))` only
  (`Sphere.estConjugueS_iff_of_isClosed`), the distinguished subvarieties are `∅` and `S(E)`
  (`Sphere.estDistingueS_iff_of_isClosed`), and Théorème 3 holds for the two-element algebra
  (`Sphere.theoreme3_ferme`, `Sphere.algebreBooleS_ferme`).
* `bzcor:c3s2t3c_algebre_parties_projective` — `benzecri1960_ch3.tex:579` (Corollaire,
  l.579–590), NOT marked (OQ-168 OPEN). For closed `w` it holds with the single simple
  subvariety `S(E)`, cardinal `1` (`Sphere.simplesS_eq_of_isClosed`,
  `Sphere.corollaire_algebre_parties_projective_ferme`).

Instances: the open quarter is (1) itself; for (2) the closed positive simplex
`FacetteDualeInstance.simplexS n` of `S(n)` (convex, closed, support `S(n)`, noyau `∅`, no line
in `F`: `BooleProjectifDomainesInstance.simplexS_hyps`) has `S(n)` as its only simple
distinguished subvariety (`simplexS_simplesS`), against the `n + 1` of the open simplex
(`BooleProjectifInstance.simplexO_simplesS_ncard`): `simplexS_contraste`.

> **Théorème 3.** Soit $w$ un convexe de $S(E)$ de support $S(E)$, de noyau vide; l'ensemble
> des sous-variétés distinguées relativement à $w$ peut être considéré comme une algèbre de
> Boole dont l'élément (1) est $S(E)$ et l'élément (0) la partie vide. On prend comme
> complémentaire la conjuguée, comme inf l'intersection, comme sup l'enveloppe convexe.
>
> **Corollaire.** Si $E$ est de dimension finie $(n+1)$, l'algèbre de Boole des sous-variétés
> distinguées relarivement à $w$ n'est autre que l'algèbre des parties d'un ensemble fini dont
> le cardinal est compris entre $1$ et $(n+1)$. [$1$ correspond au cas où il n'existe pas de
> décomposition non triviale, $(n+1)$ au cas du $n$-simplexe ouvert de la sphère à $n$
> dimensions $S(E)$].
>
> Toute sous-variété distinguée est obtenue d'une façon et d'une seule comme enveloppe convexe
> d'une famille de sous-variétés distinguées simples, c'est-à-dire minimales parmi celles
> distinctes de la partie vide.

## The proofs formalized

*(1) The open quarter.* The lines `x = s(span (Bt 0) − O)`, `y = s(span (Bt 1) − O)`,
`z = s(span (Bt 2) − O)` of the great circle `z = 0` are distinguished
(`BooleProjectifInstance.quart_distingue_Bt`). In a lattice ordered by inclusion, `x ⊓ y` lies
below two distinct lines, so its subspace is `0`; likewise `x ⊓ z`, so `(x ⊓ y) ⊔ (x ⊓ z)` is
below `x ⊓ y` and has subspace `0`. `y ⊔ z` contains both lines, hence the plane `z = 0` and `x`:
`x ⊓ (y ⊔ z) = x ≠ 0`. Distributivity fails.

*(2) Closed `w`.* By `estConjugueS_iff` a nontrivial conjugate pair is `F(w) = A + A′`
(`ConeDec`). For `a ∈ A`, `a′ ∈ A′`, `a + t a′ ∈ F(w)` for `t > 0`, so `a ∈ F(w)` since `w` is
closed (`mem_F_of_forall_add_smul`): `a = b + b′`, `b ∈ A`, `b′ ∈ A′`, and `b′ = a − b ∈ L ∩ L′ = 0`,
against `O ∉ A′`. Only the two conventional pairs remain, `(span F(w), 0) = (E, 0)` and `(0, E)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Th. 3: `w` convexe, support `S(E)`, noyau vide | (1) ✓ all hold for `quartS`, plus `w` open; (2) ✓ `IsConvexPart w`, `supportK w = univ`; noyau not used (dropped: stronger) |
| Th. 3: `E` any real vector space | (2) ⚠ `E` a real topological vector space (`IsTopologicalAddGroup`, `ContinuousSMul ℝ E`), the topology of « fermé »; no finite dimension |
| (2): `w` closed | ⚠ added: this is the alternative domain OQ-168 names (« corps convexe » read as `IsClosed` only) |
| Th. 3: (1) `S(E)`, (0) `∅`, complément la conjuguée, inf `∩`, sup l'enveloppe convexe | (2) ✓ all stated in `theoreme3_ferme`, the complement THE conjugate (exists, unique) |
| Cor.: `dim E = n + 1` | (2) ✓ `Module.finrank ℝ E = n + 1` |
| Cor.: cardinal entre `1` et `n + 1` | (2) ✓ exactly `1` |

## SCOPE (disclosed)

* **Nothing is marked**: OQ-168 is OPEN, and neither domain here is the printed one. (1) is a
  refutation of the printed Th. 3 inside the open case, named `not_theoreme3_ouvert` (it
  refutes even the first clause of `theoreme3`'s conclusion, the order by inclusion, so it also
  refutes `theoreme3` with its line-free hypothesis dropped). (2) proves Th. 3 and its
  Corollary for closed `w`, where they degenerate.
* **Reading.** « corps convexe » (OQ-168's alternative) is read only as `IsClosed w`; the noyau
  hypothesis is not used, and neither compactness nor finite dimension (except for the
  Corollary's `dim E = n + 1`). Other readings are `BooleProjectif.lean`'s: « sous-variété
  distinguée » = `s(L − O)` with `EstDistingueS`, Déf. 5's two-summand form with its convention.
* The closed simplex is `FacetteDualeInstance.simplexS`; `TriangleInstance.simplexS`
  (`PointsExtremaux.lean`) is the same definition (T-bz-c3-dedupe-simplexe will merge them).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function Filter Topology
open scoped Pointwise

namespace Benzecri

namespace Sphere

section Ferme

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- For `w` closed, `F(w)` has no cone decomposition `A + A′`. -/
theorem not_coneDec_of_isClosed {w : Set (Sphere E)} (hc : IsClosed w)
    {L L' : Submodule ℝ E} {A A' : Set E} : ¬ ConeDec (F w) L L' A A' := by
  intro h
  obtain ⟨a, ha⟩ := h.ne
  obtain ⟨a', ha'⟩ := h.ne'
  have ha0 : a ≠ 0 := fun e => h.zero (e ▸ ha)
  have hmem : a ∈ F w := mem_F_of_forall_add_smul hc ha0 (Y := a') fun t ht =>
    h.sum ▸ ⟨a, ha, t • a', h.pos' t ht a' ha', rfl⟩
  rw [h.sum] at hmem
  obtain ⟨b, hb, b', hb', hbb⟩ := hmem
  have hb'L : b' ∈ L ⊓ L' := by
    refine Submodule.mem_inf.2 ⟨?_, h.subset' hb'⟩
    simp only at hbb
    have e : b' = a - b := by rw [← hbb, add_sub_cancel_left]
    rw [e]
    exact L.sub_mem (h.subset ha) (h.subset hb)
  rw [h.disj, Submodule.mem_bot] at hb'L
  exact h.zero' (hb'L ▸ hb')

/-- **Déf. 6 for `w` closed**: the conjugate pairs are the two conventional ones. -/
theorem estConjugueS_iff_of_isClosed {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hc : IsClosed w) (hsupp : supportK w = univ) {L L' : Submodule ℝ E} :
    EstConjugueS w L L' ↔ (L = ⊤ ∧ L' = ⊥) ∨ (L = ⊥ ∧ L' = ⊤) := by
  rw [estConjugueS_iff hw, span_F_eq_top_of_supportK hsupp]
  constructor
  · rintro (h | h | ⟨A, A', h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact (not_coneDec_of_isClosed hc h).elim
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- For `w` closed, the distinguished subvarieties are `∅` and `S(E)`. -/
theorem estDistingueS_iff_of_isClosed {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hc : IsClosed w) (hsupp : supportK w = univ) {L : Submodule ℝ E} :
    EstDistingueS w L ↔ L = ⊥ ∨ L = ⊤ := by
  constructor
  · rintro ⟨L', h⟩
    rcases (estConjugueS_iff_of_isClosed hw hc hsupp).1 h with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · rintro (rfl | rfl)
    · exact ⟨⊤, (estConjugueS_iff_of_isClosed hw hc hsupp).2 (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ⟨⊥, (estConjugueS_iff_of_isClosed hw hc hsupp).2 (Or.inl ⟨rfl, rfl⟩)⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem botTop_sup {L D : Submodule ℝ E} (hL : L = ⊥ ∨ L = ⊤) (hD : D = ⊥ ∨ D = ⊤) :
    L ⊔ D = ⊥ ∨ L ⊔ D = ⊤ := by
  rcases hL with rfl | rfl <;> rcases hD with rfl | rfl <;> simp

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem botTop_inf {L D : Submodule ℝ E} (hL : L = ⊥ ∨ L = ⊤) (hD : D = ⊥ ∨ D = ⊤) :
    L ⊓ D = ⊥ ∨ L ⊓ D = ⊤ := by
  rcases hL with rfl | rfl <;> rcases hD with rfl | rfl <;> simp

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The complement of Théorème 3 for `w` closed: `∅ ↦ S(E)`, `S(E) ↦ ∅`. -/
noncomputable def complFerme (L : Submodule ℝ E) : Submodule ℝ E :=
  open Classical in if L = ⊥ then ⊤ else ⊥

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem complFerme_bot : complFerme (⊥ : Submodule ℝ E) = ⊤ := by
  simp [complFerme]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem complFerme_of_ne {L : Submodule ℝ E} (h : L ≠ ⊥) : complFerme L = ⊥ := by
  simp [complFerme, h]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem botTop_complFerme {L : Submodule ℝ E} (hL : L = ⊥ ∨ L = ⊤) :
    (L = ⊤ ∧ complFerme L = ⊥) ∨ (L = ⊥ ∧ complFerme L = ⊤) := by
  by_cases h : L = ⊥
  · exact Or.inr ⟨h, h ▸ complFerme_bot⟩
  · exact Or.inl ⟨hL.resolve_left h, complFerme_of_ne h⟩

/-- **Théorème 3**, the structure, for `w` closed: the two-element (or, for `E = 0`, one-element)
Boolean algebra `{∅, S(E)}`. -/
@[implicit_reducible]
noncomputable def algebreBooleS_ferme {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hc : IsClosed w) (hsupp : supportK w = univ) : BooleanAlgebra (DistinguesS w) :=
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_of_isClosed hw hc hsupp (L := L)
  letI : Lattice (DistinguesS w) :=
    Subtype.lattice (fun L D hL hD => (hiff _).2 (botTop_sup ((hiff L).1 hL) ((hiff D).1 hD)))
      (fun L D hL hD => (hiff _).2 (botTop_inf ((hiff L).1 hL) ((hiff D).1 hD)))
  letI : DistribLattice (DistinguesS w) :=
    DistribLattice.ofInfSupLe fun a b c => by
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨c, hc⟩ := c
      show a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c
      rcases (hiff a).1 ha with rfl | rfl <;> rcases (hiff b).1 hb with rfl | rfl <;>
        rcases (hiff c).1 hc with rfl | rfl <;> simp
  letI : BoundedOrder (DistinguesS w) :=
    Subtype.boundedOrder ((hiff _).2 (Or.inl rfl)) ((hiff _).2 (Or.inr rfl))
  { (inferInstance : DistribLattice (DistinguesS w)),
    (inferInstance : BoundedOrder (DistinguesS w)) with
    compl := fun x => ⟨complFerme x.1, by
      rcases botTop_complFerme ((hiff _).1 x.2) with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;>
        exact (hiff _).2 (by simp)⟩
    inf_compl_le_bot := fun x => by
      show x.1 ⊓ complFerme x.1 ≤ ⊥
      rcases botTop_complFerme ((hiff _).1 x.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, h1] <;> simp
    top_le_sup_compl := fun x => by
      show ⊤ ≤ x.1 ⊔ complFerme x.1
      rcases botTop_complFerme ((hiff _).1 x.2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, h1] <;> simp }

/-- **Théorème 3** (l.570) for `w` closed (the alternative domain of OQ-168, « corps convexe »
read as `IsClosed`; the noyau is not used): the distinguished subvarieties form a Boolean
algebra whose `1` is `S(E)`, whose `0` is `∅`, with complement THE conjugate (it exists and is
unique), inf the intersection and sup the convex hull. It is degenerate: its elements are `∅`
and `S(E)` (`estDistingueS_iff_of_isClosed`). -/
theorem theoreme3_ferme {w : Set (Sphere E)} (hw : IsConvexPart w) (hc : IsClosed w)
    (hsupp : supportK w = univ) :
    ∃ B : BooleanAlgebra (DistinguesS w),
      (∀ x y : DistinguesS w, B.le x y ↔ linearSubvariety x.1 ⊆ linearSubvariety y.1) ∧
      linearSubvariety (B.top : DistinguesS w).1 = univ ∧
      linearSubvariety (B.bot : DistinguesS w).1 = ∅ ∧
      (∀ x : DistinguesS w, EstConjugueS w x.1 (B.compl x).1) ∧
      (∀ (x : DistinguesS w) (L' : Submodule ℝ E), EstConjugueS w x.1 L' → L' = (B.compl x).1) ∧
      (∀ x y : DistinguesS w,
        linearSubvariety (B.inf x y).1 = linearSubvariety x.1 ∩ linearSubvariety y.1) ∧
      (∀ x y : DistinguesS w, IsLeast
        {k | IsConvexPart k ∧ linearSubvariety x.1 ∪ linearSubvariety y.1 ⊆ k}
        (linearSubvariety (B.sup x y).1)) := by
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_of_isClosed hw hc hsupp (L := L)
  have hcj := fun L L' : Submodule ℝ E => estConjugueS_iff_of_isClosed hw hc hsupp (L := L)
    (L' := L')
  refine ⟨algebreBooleS_ferme hw hc hsupp, fun x y => linearSubvariety_subset_iff.symm,
    linearSubvariety_top_eq, linearSubvariety_bot, fun x => ?_, fun x L' h => ?_,
    fun x y => (linearSubvariety_inter _ _).symm, fun x y => isLeast_linearSubvariety_sup _ _⟩
  · exact (hcj _ _).2 (botTop_complFerme ((hiff _).1 x.2))
  · show L' = complFerme x.1
    rcases (hcj _ _).1 h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · by_cases h2 : x.1 = ⊥
      · rw [h2, complFerme_bot]; exact h2.symm.trans h1
      · exact (complFerme_of_ne h2).symm
    · rw [h1, complFerme_bot]

/-- For `w` closed in a nontrivial `E`, `S(E)` is the only simple distinguished subvariety. -/
theorem simplesS_eq_of_isClosed [Nontrivial E] {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hc : IsClosed w) (hsupp : supportK w = univ) : simplesS w = {⊤} := by
  ext M
  simp only [simplesS, EstSimpleS, mem_setOf_eq, mem_singleton_iff,
    estDistingueS_iff_of_isClosed hw hc hsupp]
  constructor
  · rintro ⟨h, hne, -⟩
    exact h.resolve_left hne
  · rintro rfl
    exact ⟨Or.inr rfl, top_ne_bot, fun N hN hN0 _ => hN.resolve_left hN0⟩

theorem set_singleton_cases {α : Type*} {a : α} (T : Set ({a} : Set α)) : T = ∅ ∨ T = univ :=
  (eq_empty_or_nonempty T).imp_right Set.Nonempty.eq_univ

theorem sSup_image_singleton_cases {α : Type*} [CompleteLattice α] {a : α}
    (T : Set ({a} : Set α)) :
    (T = ∅ ∧ sSup (Subtype.val '' T) = ⊥) ∨ (T = univ ∧ sSup (Subtype.val '' T) = a) := by
  rcases set_singleton_cases T with rfl | rfl
  · exact Or.inl ⟨rfl, by simp⟩
  · exact Or.inr ⟨rfl, by simp⟩

/-- **Corollaire** of Théorème 3 (l.579) for `w` closed: if `E` has dimension `n + 1`, the
distinguished subvarieties are, as a Boolean algebra, the subsets of the set of simple ones,
which is `{S(E)}`, of cardinal `1`, by `T ↦` the convex hull of `T`; every distinguished
subvariety is, in one and only one way, the convex hull of a family of simple ones. -/
theorem corollaire_algebre_parties_projective_ferme {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hc : IsClosed w) (hsupp : supportK w = univ) {n : ℕ} (hE : Module.finrank ℝ E = n + 1) :
    (simplesS w).Finite ∧ 1 ≤ (simplesS w).ncard ∧ (simplesS w).ncard ≤ n + 1 ∧
      (∃ e : Set (simplesS w) ≃o DistinguesS w, ∀ T,
        linearSubvariety (e T).1 = linearSubvariety (sSup (Subtype.val '' T))) ∧
      (∀ T ⊆ simplesS w, EstDistingueS w (sSup T)) ∧
      (∀ L : Submodule ℝ E, EstDistingueS w L → ∃! T : Set (Submodule ℝ E), T ⊆ simplesS w ∧
        IsLeast {k | IsConvexPart k ∧ ∀ D ∈ T, linearSubvariety D ⊆ k} (linearSubvariety L)) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_of_isClosed hw hc hsupp (L := L)
  have hS := simplesS_eq_of_isClosed hw hc hsupp
  have htb : (⊤ : Submodule ℝ E) ≠ ⊥ := top_ne_bot
  -- the order isomorphism on `{⊤}`
  let f : Set ({⊤} : Set (Submodule ℝ E)) → DistinguesS w := fun T =>
    ⟨sSup (Subtype.val '' T), (hiff _).2 (by
      rcases sSup_image_singleton_cases T with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h])⟩
  have hf : ∀ T, (f T).1 = sSup (Subtype.val '' T) := fun _ => rfl
  let e0 : Set ({⊤} : Set (Submodule ℝ E)) ≃o DistinguesS w :=
    { toFun := f
      invFun := fun x => {_y | x.1 = ⊤}
      left_inv := fun T => by
        rcases sSup_image_singleton_cases T with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · ext y; simp [hf, htb.symm]
        · ext y; simp [hf]
      right_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        apply Subtype.ext
        rcases (hiff x).1 hx with rfl | rfl
        · show sSup (Subtype.val '' {_y | (⊥ : Submodule ℝ E) = ⊤}) = ⊥
          simp [htb.symm]
        · show sSup (Subtype.val '' {_y | (⊤ : Submodule ℝ E) = ⊤}) = ⊤
          simp
      map_rel_iff' := fun {T T'} => by
        show (f T).1 ≤ (f T').1 ↔ T ≤ T'
        rw [hf, hf]
        rcases sSup_image_singleton_cases T with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
          rcases sSup_image_singleton_cases T' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
          simp [htb] }
  obtain ⟨e', he'⟩ := exists_orderIso_transport hS rfl sSup e0 hf
  refine ⟨hS ▸ finite_singleton _, by rw [hS, ncard_singleton], by rw [hS, ncard_singleton]; omega,
    ⟨e', fun T => by rw [he']⟩, fun T hT => (hiff _).2 ?_, fun L hL => ?_⟩
  · rw [hS] at hT
    rcases subset_singleton_iff_eq.1 hT with rfl | rfl <;> simp
  · rw [hS]
    rcases (hiff L).1 hL with rfl | rfl
    · refine ⟨∅, ⟨empty_subset _, (isLeast_iff_eq_sSup _ _).2 sSup_empty⟩, ?_⟩
      rintro T ⟨hT, hTL⟩
      have h := (isLeast_iff_eq_sSup _ _).1 hTL
      rcases subset_singleton_iff_eq.1 hT with rfl | rfl
      · rfl
      · simp at h
    · refine ⟨{⊤}, ⟨subset_rfl, (isLeast_iff_eq_sSup _ _).2 sSup_singleton⟩, ?_⟩
      rintro T ⟨hT, hTL⟩
      have h := (isLeast_iff_eq_sSup _ _).1 hTL
      rcases subset_singleton_iff_eq.1 hT with rfl | rfl
      · exact absurd (by simpa using h.symm) htb
      · rfl

end Ferme

end Sphere

/-! ### Instances: the open quarter (1) and the closed simplex (2) -/

namespace BooleProjectifDomainesInstance

open Sphere BooleProjectifInstance

/-! #### (1) The open quarter: no distributive lattice ordered by inclusion -/

theorem Bt_subset (t : ℝ) : Bt t ⊆ (zeS 2 ⊓ hypS 0 1 t : Submodule ℝ V3) := fun _ hv =>
  Submodule.mem_inf.2 ⟨mem_zeS.2 hv.1.1, mem_hypS.2 hv.1.2⟩

/-- Two distinct lines `span (Bt t)`, `span (Bt r)` of the circle `z = 0` meet at `O` only. -/
theorem span_Bt_inf {t r : ℝ} (htr : t ≠ r) :
    Submodule.span ℝ (Bt t) ⊓ Submodule.span ℝ (Bt r) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have h1 := Submodule.mem_inf.1 (Submodule.span_le.2 (Bt_subset t) hv.1)
  have h2 := Submodule.mem_inf.1 (Submodule.span_le.2 (Bt_subset r) hv.2)
  rw [mem_zeS, mem_hypS] at h1 h2
  have h3 : (t - r) * v 1 = 0 := by linarith [h1.2, h2.2]
  have hv1 : v 1 = 0 := (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 htr)
  refine (Submodule.mem_bot ℝ).2 (eq_zero_of_coords ?_ hv1 h1.1)
  rw [h1.2, hv1, mul_zero]

theorem e2_mem_Bt0 : (![0, 1, 0] : V3) ∈ Bt 0 := by simp [Bt, hyp, ze, po]

theorem span_Bt0_ne_bot : Submodule.span ℝ (Bt 0) ≠ ⊥ := by
  intro h
  have := Submodule.subset_span (R := ℝ) e2_mem_Bt0
  rw [h, SetLike.mem_coe, Submodule.mem_bot] at this
  simpa using congrFun this 1

/-- The line `x = 0` of the circle `z = 0` lies in the plane spanned by the lines `x = y` and
`x = 2y`. -/
theorem span_Bt0_le : Submodule.span ℝ (Bt 0) ≤ Submodule.span ℝ (Bt 1) ⊔ Submodule.span ℝ (Bt 2) := by
  rw [Submodule.span_le]
  intro v hv
  have h1 : (![1, 1, 0] : V3) ∈ Bt 1 := by simp [Bt, hyp, ze, po]
  have h2 : (![2, 1, 0] : V3) ∈ Bt 2 := by simp [Bt, hyp, ze, po]
  have hv0 : v 0 = 0 := by simpa [hyp] using hv.1.2
  have hv2 : v 2 = 0 := hv.1.1
  have e : v = (2 * v 1) • (![1, 1, 0] : V3) - v 1 • (![2, 1, 0] : V3) := by
    ext i; fin_cases i <;> simp [hv0, hv2] <;> ring
  rw [SetLike.mem_coe, e]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (Submodule.mem_sup_left (Submodule.subset_span h1)))
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.subset_span h2)))

/-- The lattice core of `not_distribLattice_quartS`: in a distributive lattice ordered through
`f` by inclusion of subspaces, three elements sent to the lines `x = 0`, `x = y`, `x = 2y` of the
plane `z = 0` cannot exist. -/
theorem not_distrib_lines {α : Type*} [DistribLattice α] (f : α → Submodule ℝ V3)
    (hle : ∀ x y : α, x ≤ y ↔ f x ≤ f y) (x y z : α) (hx : f x = Submodule.span ℝ (Bt 0))
    (hy : f y = Submodule.span ℝ (Bt 1)) (hz : f z = Submodule.span ℝ (Bt 2)) : False := by
  have hxy : f (x ⊓ y) = ⊥ := eq_bot_iff.2 ((span_Bt_inf (by norm_num : (0 : ℝ) ≠ 1)) ▸
    hx ▸ hy ▸ le_inf ((hle _ _).1 inf_le_left) ((hle _ _).1 inf_le_right))
  have hxz : f (x ⊓ z) = ⊥ := eq_bot_iff.2 ((span_Bt_inf (by norm_num : (0 : ℝ) ≠ 2)) ▸
    hx ▸ hz ▸ le_inf ((hle _ _).1 inf_le_left) ((hle _ _).1 inf_le_right))
  have hyz : x ≤ y ⊔ z := (hle _ _).2 (hx ▸ span_Bt0_le.trans
    (sup_le (hy ▸ (hle _ _).1 le_sup_left) (hz ▸ (hle _ _).1 le_sup_right)))
  have hx' : x ≤ x ⊓ y :=
    calc x = x ⊓ (y ⊔ z) := (inf_eq_left.2 hyz).symm
      _ = x ⊓ y ⊔ x ⊓ z := inf_sup_left x y z
      _ ≤ x ⊓ y := sup_le le_rfl ((hle _ _).2 (hxz ▸ bot_le))
  exact span_Bt0_ne_bot (eq_bot_iff.2 (hx ▸ hxy ▸ (hle _ _).1 hx'))

/-- **No distributive lattice on the distinguished subvarieties of the open quarter is ordered by
inclusion**: the three distinguished lines `x = 0`, `x = y`, `x = 2y` of the plane `z = 0` break
distributivity. -/
theorem not_distribLattice_quartS :
    ¬ ∃ B : DistribLattice (DistinguesS quartS),
      ∀ x y : DistinguesS quartS, B.le x y ↔ linearSubvariety x.1 ⊆ linearSubvariety y.1 :=
  fun ⟨B, hB⟩ => @not_distrib_lines _ B Subtype.val
    (fun x y => (hB x y).trans linearSubvariety_subset_iff) ⟨_, quart_distingue_Bt 0⟩
    ⟨_, quart_distingue_Bt 1⟩ ⟨_, quart_distingue_Bt 2⟩ rfl rfl rfl

/-- **Théorème 3 is false as printed for an open `w`**: the open quarter `w₁` of `S(2)` is
convex, open, of support `S(2)` and of empty noyau, and no Boolean algebra on its distinguished
subvarieties is ordered by inclusion (`theoreme3`'s first clause; « inf l'intersection » and
« sup l'enveloppe convexe » then cannot both hold). -/
theorem not_theoreme3_ouvert :
    ∃ w : Set (S 2), IsConvexPart w ∧ IsOpen w ∧ supportK w = univ ∧ noyau w = ∅ ∧
      ¬ ∃ B : BooleanAlgebra (DistinguesS w),
        ∀ x y : DistinguesS w, B.le x y ↔ linearSubvariety x.1 ⊆ linearSubvariety y.1 :=
  ⟨quartS, isConvexPart_quartS, isOpen_quartS, supportK_quartS, noyau_quartS,
    fun ⟨B, hB⟩ => not_distribLattice_quartS ⟨B.toDistribLattice, hB⟩⟩

/-! #### (2) The closed simplex: Théorème 3 and its Corollary hold degenerately -/

section Simplexe

variable {n : ℕ}

theorem F_simplexS : F (FacetteDualeInstance.simplexS n) = FacetteDualeInstance.orthant n \ {0} :=
  F_ofCone FacetteDualeInstance.isPosCone_orthant

theorem isClosed_simplexS : IsClosed (FacetteDualeInstance.simplexS n) := by
  rw [← isOpen_compl_iff, isOpen_iff_F, F_compl, F_simplexS]
  have hcl : IsClosed (FacetteDualeInstance.orthant n) := by
    simp only [FacetteDualeInstance.orthant, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  convert hcl.isOpen_compl using 1
  ext v
  have h0 : (0 : Fin (n + 1) → ℝ) ∈ FacetteDualeInstance.orthant n := fun i => le_rfl
  simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff, not_and, not_not]
  constructor
  · rintro ⟨hv, h⟩ hC
    exact hv (h hC)
  · intro hC
    exact ⟨fun hv => hC (hv ▸ h0), fun h => absurd h hC⟩

theorem supportK_simplexS : supportK (FacetteDualeInstance.simplexS n) = univ := by
  have hsub : orthO n ⊆ F (FacetteDualeInstance.simplexS n) := by
    rw [F_simplexS]
    intro v hv
    exact ⟨fun i => (hv i).le, fun h => by simpa [mem_singleton_iff.1 h] using hv 0⟩
  have h := Submodule.span_mono (R := ℝ) hsub
  rw [span_orthO] at h
  rw [supportK, top_le_iff.1 h, linearSubvariety_top_eq]

theorem noyau_simplexS : noyau (FacetteDualeInstance.simplexS n) = ∅ := by
  rw [noyau_eq FacetteDualeInstance.isConvexPart_simplexS]
  refine eq_empty_of_forall_notMem fun m ⟨h, h'⟩ => ?_
  induction m using ind with
  | h M hM =>
  rw [neg_mk, mk_mem_iff_mem_F, F_simplexS] at h'
  rw [mk_mem_iff_mem_F, F_simplexS] at h
  refine h.2 (mem_singleton_iff.2 (funext fun i => le_antisymm ?_ (h.1 i)))
  have := h'.1 i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  linarith

theorem not_contientDroite_simplexS : ¬ ContientDroite (F (FacetteDualeInstance.simplexS n)) := by
  rintro ⟨x, v, hv, h⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hmem := h (-(|x i| + 1) / v i)
  rw [F_simplexS] at hmem
  have := hmem.1 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
  rw [div_mul_cancel₀ _ hi] at this
  linarith [le_abs_self (x i)]

/-- **The closed positive simplex of `S(n)`** satisfies the printed hypotheses of Théorème 3
(convex, of support `S(n)`, of empty noyau), is closed, and `F` contains no line. -/
theorem simplexS_hyps : IsConvexPart (FacetteDualeInstance.simplexS n) ∧
    IsClosed (FacetteDualeInstance.simplexS n) ∧ supportK (FacetteDualeInstance.simplexS n) = univ ∧
    noyau (FacetteDualeInstance.simplexS n) = ∅ ∧
    ¬ ContientDroite (F (FacetteDualeInstance.simplexS n)) :=
  ⟨FacetteDualeInstance.isConvexPart_simplexS, isClosed_simplexS, supportK_simplexS,
    noyau_simplexS, not_contientDroite_simplexS⟩

theorem simplexS_distingue_iff {L : Submodule ℝ (Fin (n + 1) → ℝ)} :
    EstDistingueS (FacetteDualeInstance.simplexS n) L ↔ L = ⊥ ∨ L = ⊤ :=
  estDistingueS_iff_of_isClosed FacetteDualeInstance.isConvexPart_simplexS isClosed_simplexS
    supportK_simplexS

/-- The closed simplex has `S(n)` as its only simple distinguished subvariety. -/
theorem simplexS_simplesS : simplesS (FacetteDualeInstance.simplexS n) = {⊤} ∧
    (simplesS (FacetteDualeInstance.simplexS n)).ncard = 1 := by
  have h := simplesS_eq_of_isClosed FacetteDualeInstance.isConvexPart_simplexS
    isClosed_simplexS (supportK_simplexS (n := n))
  exact ⟨h, by rw [h, ncard_singleton]⟩

/-- **The contrast in `S(2)`**: the open triangle has `3` simple distinguished subvarieties, the
closed triangle `1`. -/
theorem simplexS_contraste : (simplesS (simplexO 2)).ncard = 3 ∧
    (simplesS (FacetteDualeInstance.simplexS 2)).ncard = 1 :=
  ⟨simplexO_simplesS_ncard, simplexS_simplesS.2⟩

end Simplexe

end BooleProjectifDomainesInstance

end Benzecri
