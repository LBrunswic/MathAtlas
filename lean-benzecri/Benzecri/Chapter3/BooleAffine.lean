import Benzecri.Chapter3.Conjugues
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Atoms
import Mathlib.Data.Set.Card

/-!
# Chapter 3 § 2 — Théorème 2 and its Corollaire: the Boolean algebra of distinguished subspaces

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 267; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR; checked here
against the page image). Target T-bz-c3-boole-affine. Any real vector space `E` for Théorème 2.

* `bzthm:c3s2t2_algebre_boole_affine` — `benzecri1960_ch3.tex:526` (Théorème 2, l.526–532,
  no proof printed beyond « De là on déduit aussitôt le », l.524), NOT marked (« le conjugué »
  depends on OQ-163, see SCOPE): `Benzecri.theoreme2`, the
  structure `Benzecri.algebreBoole` on `Benzecri.Distingues W`; closure and De Morgan:
  `estDistingue_inf`, `conjugue_inf`, `estDistingue_sup`, `conjugue_sup`; distributivity
  `inf_sup_le_of_estDistingue`; « le conjugué » under the three readings of Déf. 4 (OQ-163):
  `conjugue_le_of_sontConjugues`, `conjugue_eq_of_disjoint`, `conjugue_eq_of_isSommeConvexes`,
  `demiDroite_complement_conjugue`.
* `bzcor:c3s2t2c_algebre_parties_affine` — `benzecri1960_ch3.tex:535` (Corollaire, l.535–542, no
  proof printed), NOT marked: the printed lower bound `1` fails at `n = 0` (« imprecise », see
  SCOPE): `Benzecri.corollaire_algebre_parties` (the corrected statement: `≤ n`, and `≥ 1` when
  `n ≥ 1`), `Benzecri.isoParties` (the Boolean algebra is the algebra of parts of the set
  `Benzecri.simples W` of simple distinguished subspaces, `T ↦ ∑ T`), `EstSimple`,
  `simples_finite_ncard_le`, `eq_sSup_simples_le`, `le_sSup_iff_mem_of_estSimple`,
  `exists_estSimple_le`; at `n = 0`: `simples_eq_empty_of_finrank_eq_zero`,
  `cube_zero_corollaire`.

Instances: the cube `[−1,1]ⁿ` (« `n` au cube »): `cube_simples` (the `n` coordinate axes),
`cube_simples_ncard`, `cube_algebreBoole`, `cube_isoParties`; the closed unit ball of a nonzero
real inner product space (« `1` correspond à la sphère »): `boule_hyps`, `boule_simples` (`{E}`),
`boule_simples_ncard`; dimension `0`: `cube_zero_corollaire`.

> De là on déduit aussitôt le
>
> **Théorème 2.** Soit $W$ un convexe de $E$ contenant l'origine, engendrant $E$ et ne contenant
> aucune droite : l'ensemble des sous-espaces distingués relativement à $W$ peut être considéré
> comme une algèbre de Boole, dont l'élément $1$ est $E$ et l'élément $0$ l'origine (considéré
> comme sous-espace de dimension $0$); on prend comme complémentaire le conjugué; comme inf
> l'intersection, comme sup le produit.
>
> **Corollaire.** Si $E$ est de dimension finie $n$, l'algèbre de Boole des sous-espaces
> distingués relativement à $W$ n'est autre que l'algèbre des parties d'un ensemble fini dont le
> cardinal est compris entre $1$ et $n$ ($1$ correspond à la sphère, $n$ au cube).
>
> Tout sous-espace distingué est obtenu d'une façon et d'une seule comme somme d'une famille de
> sous-espaces distingués simples [c'est-à-dire minimaux parmi ceux différents de $0$].

## The proof formalized

With `P_L` the projection on `L` along its conjugate `L'` (`conjugue W L`): `P_L` preserves
every distinguished `D` (`projection_mem_of_mem`, from Théorème 1's proof). Hence `L ∩ D` is
distinguished with conjugate `L' + D'`: `x = P_D P_L x + (P_{D'} P_L x + P_{L'} x)`, and for
`x ∈ L ∩ D ∩ W`, `y ∈ (L' + D') ∩ W`, `x + y = (x + P_L y) + P_{L'} y` with `P_L y ∈ D'`. The
sum `L + D` is distinguished with conjugate `L' ∩ D'` (the same applied to `L'`, `D'`, and
`L'' = L`, `prop3_2_involution`). Distributivity: for `x = d + f ∈ L ∩ (D + F)`,
`x = P_L d + P_L f`. A distributive bounded lattice with complements is a Boolean algebra. The
Corollaire: finrank is strictly monotone and additive on disjoint distinguished subspaces, so two
different simple ones meet at `0`, a finite family of `k` simple ones has a sum of dimension
`≥ k` (at most `n` simple ones), and every distinguished `L` is the sum of the simple ones it
contains (else `L ∩ (∑)'` contains a simple one, `exists_estSimple_le`, by minimal finrank).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E` (real vector space) | ✓ carried: any real vector space, any dimension (Théorème 2) |
| `W` convexe, contenant l'origine, engendrant `E`, sans droite | ✓ carried (`Convex ℝ W`, `0 ∈ W`, `Submodule.span ℝ W = ⊤`, `¬ ContientDroite W`) |
| « sous-espaces distingués » (Déf. 3) | ✓ `EstDistingue W` (supplementary `L'`, `W = L ∩ W + L' ∩ W`) |
| « l'élément `1` est `E`, `0` l'origine » | ✓ `⊤`, `⊥` |
| « complémentaire le conjugué » | ⚠ read (OQ-163): `conjugue W` (Prop. 3 2°); readings of Déf. 4, see SCOPE |
| « inf l'intersection, sup le produit » | ✓ `⊓`; « produit » read as the sum `L ⊔ D`, see SCOPE |
| Cor.: `E` de dimension finie `n` | ✓ `FiniteDimensional ℝ E`, `n = Module.finrank ℝ E`; the standing hypotheses on `W` of Théorème 2 carried |
| Cor.: cardinal « compris entre `1` et `n` » | ⚠ strengthened: `1 ≤` only under `0 < n` (false at `n = 0`, `cube_zero_corollaire`) |
| Cor.: « simples [minimaux parmi ceux différents de `0`] » | ✓ `EstSimple W` |
| Cor.: the Boolean algebra of Théorème 2 (its complement, « le conjugué ») | ⚠ read (OQ-163), as for Théorème 2; the isomorphism `isoParties` is an order isomorphism and does not depend on it |

## SCOPE (disclosed)

* « comme sup le produit » (l.531, so printed in the scan) is read as the sum `L + D` (`⊔`), the
  Corollaire's « somme d'une famille ». This needs no ruling: once the inf is the
  intersection, the order is inclusion and the sup of a Boolean algebra on this order is forced
  to be the least distinguished subspace containing `L` and `D`, which is `L ⊔ D`
  (`estDistingue_sup`); `theoreme2` states the order and every operation.
* « le conjugué » (OQ-163, Déf. 4 OPEN). Théorème 2's elements are Déf. 3's distinguished
  subspaces, whose conjugate in Prop. 3 2° is supplementary and unique (`conjugue W`), and this
  is the complement. Under (b) it is the conjugate. Under (c) (Déf. 1's sum) it is the only
  distinguished conjugate (`conjugue_eq_of_isSommeConvexes`). Under (a) (as printed, no
  supplementarity) it is the least distinguished conjugate (`conjugue_le_of_sontConjugues`) and
  the only conjugate meeting `L` at `0` (`conjugue_eq_of_disjoint`), so the only conjugate which
  can be a Boolean complement; not every (a)-conjugate is the complement
  (`demiDroite_complement_conjugue`: `ℝ` is (a)-conjugate to itself relative to `[0, ∞[`).
  The row is therefore NOT marked until OQ-163 is ruled: under (b) or (c) it closes with no
  Lean change; under (a) the statement of record is with « the conjugate meeting `L` only at
  `0` » (`conjugue_eq_of_disjoint`) or « the least distinguished conjugate »
  (`conjugue_le_of_sontConjugues`).
* Corollaire, « imprecise »: at `n = 0` (`E = 0`) there is one distinguished subspace and no
  simple one, so the algebra is that of the parts of the empty set, cardinal `0`, not `≥ 1`
  (`cube_zero_corollaire`, `simples_eq_empty_of_finrank_eq_zero`). The corrected statement
  `corollaire_algebre_parties` carries `0 < n → 1 ≤ card`. Unmarked.
* « l'algèbre des parties d'un ensemble fini » is formalized as an order isomorphism
  `Set (simples W) ≃o Distingues W` (an order isomorphism of Boolean algebras preserves every
  Boolean operation), with the finite set the set of simple distinguished subspaces; « famille »
  is read as a set (no repetition), which the uniqueness requires.
* « `1` correspond à la sphère » is read as the closed unit ball (the convex body bounded by the
  sphere) of a nonzero Euclidean space, and as an example, not as « cardinal `1` iff ball ».

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function
open scoped Pointwise

namespace Benzecri

section BooleAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The set of the subspaces distinguished relative to `W` (Déf. 3), as a type. -/
abbrev Distingues (W : Set E) : Type _ := {L : Submodule ℝ E // EstDistingue W L}

/-- Closure under `⊓`, with the conjugate of `L ⊓ D` the sum of the conjugates. -/
theorem estDistingue_inf {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L D : Submodule ℝ E}
    (hL : EstDistingue W L) (hD : EstDistingue W D) :
    IsCompl (L ⊓ D) (conjugue W L ⊔ conjugue W D) ∧
      SontConjugues W (L ⊓ D) (conjugue W L ⊔ conjugue W D) := by
  obtain ⟨hLc, hcL⟩ := conjugue_spec hL
  obtain ⟨hDc, hcD⟩ := conjugue_spec hD
  set L' := conjugue W L
  set D' := conjugue W D
  -- `P_L` preserves `D` and `D'`, `P_D` preserves `L`
  have hPLD : ∀ x ∈ D, L.projection L' hLc x ∈ D := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hLc hcL hDc hcD hx
  have hPLD' : ∀ x ∈ D', L.projection L' hLc x ∈ D' := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hLc hcL hDc.symm hcD.symm hx
  have hPDL : ∀ x ∈ L, D.projection D' hDc x ∈ L := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hDc hcD hLc hcL hx
  have hQDL : ∀ x ∈ L, D'.projection D hDc.symm x ∈ L := fun x hx =>
    projection_mem_of_mem hW h0 hspan hd hDc.symm hcD.symm hLc hcL hx
  -- `P_L` maps `L' ⊔ D'` into `D'`
  have hPsup : ∀ y ∈ L' ⊔ D', L.projection L' hLc y ∈ D' := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, Submodule.projection_apply_of_mem_right hLc ha, zero_add]
    exact hPLD' b hb
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hxL := (Submodule.mem_inf.1 hx).1
    have hxD := (Submodule.mem_inf.1 hx).2
    have e : L.projection L' hLc x = x := Submodule.projection_apply_of_mem_left hLc hxL
    have hx' : x ∈ D' := e ▸ hPsup x hy
    exact (Submodule.disjoint_def.1 hDc.disjoint) x hxD hx'
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e1 := Submodule.projection_add_projection_eq_self hLc x
    have e2 := Submodule.projection_add_projection_eq_self hDc (L.projection L' hLc x)
    have hmem : D.projection D' hDc (L.projection L' hLc x) ∈ L ⊓ D :=
      Submodule.mem_inf.2 ⟨hPDL _ (Submodule.projection_apply_mem _ _),
        Submodule.projection_apply_mem _ _⟩
    have hrest : D'.projection D hDc.symm (L.projection L' hLc x) +
        L'.projection L hLc.symm x ∈ L' ⊔ D' :=
      (L' ⊔ D').add_mem (Submodule.mem_sup_right (Submodule.projection_apply_mem _ _))
        (Submodule.mem_sup_left (Submodule.projection_apply_mem _ _))
    have : x = D.projection D' hDc (L.projection L' hLc x) +
        (D'.projection D hDc.symm (L.projection L' hLc x) + L'.projection L hLc.symm x) := by
      rw [← add_assoc, e2, e1]
    rw [this]
    exact Submodule.add_mem_sup hmem hrest
  · unfold SontConjugues
    ext w
    constructor
    · intro hw
      have hPw := projection_mem_inter hLc hcL hw
      have hQw := projection_mem_inter hLc.symm hcL.symm hw
      have hDP := projection_mem_inter hDc hcD hPw.2
      have hD'P := projection_mem_inter hDc.symm hcD.symm hPw.2
      have e1 := Submodule.projection_add_projection_eq_self hLc w
      have e2 := Submodule.projection_add_projection_eq_self hDc (L.projection L' hLc w)
      refine Set.mem_add.2 ⟨D.projection D' hDc (L.projection L' hLc w),
        ⟨Submodule.mem_inf.2 ⟨hPDL _ hPw.1, hDP.1⟩, hDP.2⟩,
        D'.projection D hDc.symm (L.projection L' hLc w) + L'.projection L hLc.symm w,
        ⟨(L' ⊔ D').add_mem (Submodule.mem_sup_right hD'P.1) (Submodule.mem_sup_left hQw.1), ?_⟩,
        ?_⟩
      · rw [hcL]
        exact Set.add_mem_add ⟨hQDL _ hPw.1, hD'P.2⟩ hQw
      · rw [← add_assoc, e2, e1]
    · intro hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.1 hw
      have hxL := (Submodule.mem_inf.1 hx.1).1
      have hxD := (Submodule.mem_inf.1 hx.1).2
      have hPy := projection_mem_inter hLc hcL hy.2
      have hQy := projection_mem_inter hLc.symm hcL.symm hy.2
      have hPyD' : L.projection L' hLc y ∈ D' := hPsup y hy.1
      have hxP : x + L.projection L' hLc y ∈ W := by
        rw [hcD]; exact Set.add_mem_add ⟨hxD, hx.2⟩ ⟨hPyD', hPy.2⟩
      have e1 := Submodule.projection_add_projection_eq_self hLc y
      have : x + y = (x + L.projection L' hLc y) + L'.projection L hLc.symm y := by
        rw [add_assoc, e1]
      rw [this, hcL]
      exact Set.add_mem_add ⟨L.add_mem hxL hPy.1, hxP⟩ hQy

/-- The conjugate of `L ⊓ D` is `L' ⊔ D'`. -/
theorem conjugue_inf {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L D : Submodule ℝ E}
    (hL : EstDistingue W L) (hD : EstDistingue W D) :
    conjugue W (L ⊓ D) = conjugue W L ⊔ conjugue W D := by
  obtain ⟨h1, h2⟩ := estDistingue_inf hW h0 hspan hd hL hD
  exact conjugue_eq hW h0 hspan hd h1 h2

/-- Closure under `⊔` (« comme sup le produit », read as the sum `L + D`), with the conjugate
of `L ⊔ D` the intersection of the conjugates. -/
theorem estDistingue_sup {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L D : Submodule ℝ E}
    (hL : EstDistingue W L) (hD : EstDistingue W D) :
    IsCompl (L ⊔ D) (conjugue W L ⊓ conjugue W D) ∧
      SontConjugues W (L ⊔ D) (conjugue W L ⊓ conjugue W D) := by
  obtain ⟨h1, h2⟩ := estDistingue_inf hW h0 hspan hd (estDistingue_conjugue hL)
    (estDistingue_conjugue hD)
  rw [conjugue_conjugue hW h0 hspan hd hL, conjugue_conjugue hW h0 hspan hd hD] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

theorem conjugue_sup {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L D : Submodule ℝ E}
    (hL : EstDistingue W L) (hD : EstDistingue W D) :
    conjugue W (L ⊔ D) = conjugue W L ⊓ conjugue W D := by
  obtain ⟨h1, h2⟩ := estDistingue_sup hW h0 hspan hd hL hD
  exact conjugue_eq hW h0 hspan hd h1 h2

/-- Distributivity on the distinguished subspaces: `L ⊓ (D ⊔ F) ≤ L ⊓ D ⊔ L ⊓ F` (the
projection on `L` along its conjugate preserves `D` and `F`). -/
theorem inf_sup_le_of_estDistingue {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L D F : Submodule ℝ E}
    (hL : EstDistingue W L) (hD : EstDistingue W D) (hF : EstDistingue W F) :
    L ⊓ (D ⊔ F) ≤ L ⊓ D ⊔ L ⊓ F := by
  obtain ⟨hLc, hcL⟩ := conjugue_spec hL
  obtain ⟨hDc, hcD⟩ := conjugue_spec hD
  obtain ⟨hFc, hcF⟩ := conjugue_spec hF
  intro x hx
  obtain ⟨hxL, hxDF⟩ := Submodule.mem_inf.1 hx
  obtain ⟨d, hdD, f, hfF, rfl⟩ := Submodule.mem_sup.1 hxDF
  rw [← Submodule.projection_apply_of_mem_left hLc hxL, map_add]
  exact Submodule.add_mem_sup
    (Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem _ _,
      projection_mem_of_mem hW h0 hspan hd hLc hcL hDc hcD hdD⟩)
    (Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem _ _,
      projection_mem_of_mem hW h0 hspan hd hLc hcL hFc hcF hfF⟩)

/-- **Théorème 2**, the structure: the distinguished subspaces, ordered by inclusion, with `⊓`
the intersection, `⊔` the sum, `⊤ = E`, `⊥ = 0` and the complement the conjugate
(`conjugueDistingue`, Prop. 3 2°). -/
@[implicit_reducible]
noncomputable def algebreBoole {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    BooleanAlgebra (Distingues W) :=
  letI : Lattice (Distingues W) :=
    Subtype.lattice (fun _ _ hL hD => ⟨_, (estDistingue_sup hW h0 hspan hd hL hD).1,
        (estDistingue_sup hW h0 hspan hd hL hD).2⟩)
      (fun _ _ hL hD => ⟨_, (estDistingue_inf hW h0 hspan hd hL hD).1,
        (estDistingue_inf hW h0 hspan hd hL hD).2⟩)
  letI : DistribLattice (Distingues W) :=
    DistribLattice.ofInfSupLe fun a b c => inf_sup_le_of_estDistingue hW h0 hspan hd a.2 b.2 c.2
  letI : BoundedOrder (Distingues W) := Subtype.boundedOrder (estDistingue_bot h0) (estDistingue_top h0)
  { (inferInstance : DistribLattice (Distingues W)),
    (inferInstance : BoundedOrder (Distingues W)) with
    compl := conjugueDistingue W
    inf_compl_le_bot := fun x => (conjugue_spec x.2).1.disjoint.le_bot
    top_le_sup_compl := fun x => (conjugue_spec x.2).1.codisjoint.top_le }

/-- **Théorème 2** (l.526): « l'ensemble des sous-espaces distingués relativement à `W` peut être
considéré comme une algèbre de Boole, dont l'élément `1` est `E` et l'élément `0` l'origine; on
prend comme complémentaire le conjugué; comme inf l'intersection, comme sup le produit ». -/
theorem theoreme2 {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    ∃ B : BooleanAlgebra (Distingues W),
      (∀ x y : Distingues W, B.le x y ↔ x.1 ≤ y.1) ∧
      (B.top : Distingues W).1 = ⊤ ∧ (B.bot : Distingues W).1 = ⊥ ∧
      (∀ x : Distingues W, (B.compl x).1 = conjugue W x.1) ∧
      (∀ x y : Distingues W, (B.inf x y).1 = x.1 ⊓ y.1) ∧
      (∀ x y : Distingues W, (B.sup x y).1 = x.1 ⊔ y.1) :=
  ⟨algebreBoole hW h0 hspan hd, fun _ _ => Iff.rfl, rfl, rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

/-! ### « le conjugué » under the readings of Déf. 4 (OQ-163) -/

/-- Reading (a): the complement `conjugue W L` is the least distinguished subspace conjugate
(as printed, no supplementarity) to `L`. -/
theorem conjugue_le_of_sontConjugues {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L M : Submodule ℝ E}
    (hL : EstDistingue W L) (hM : EstDistingue W M) (hc : SontConjugues W L M) :
    conjugue W L ≤ M := by
  obtain ⟨hLc, hcL⟩ := conjugue_spec hL
  obtain ⟨hMc, hcM⟩ := conjugue_spec hM
  rw [← span_inter_eq_of_conjugues hLc hcL hspan, Submodule.span_le]
  rintro y ⟨hyL', hyW⟩
  have hy := hyW
  rw [hc, Set.mem_add] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  have e : (conjugue W L).projection L hLc.symm (a + b) = a + b :=
    Submodule.projection_apply_of_mem_left hLc.symm hyL'
  rw [map_add, Submodule.projection_apply_of_mem_right hLc.symm ha.1, zero_add] at e
  rw [← e]
  exact projection_mem_of_mem hW h0 hspan hd hLc.symm hcL.symm hMc hcM hb.1

/-- Reading (a): the complement is the only subspace conjugate to `L` meeting `L` at `0`. -/
theorem conjugue_eq_of_disjoint {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L M : Submodule ℝ E}
    (hc : SontConjugues W L M) (hLM : Disjoint L M) :
    conjugue W L = M := by
  refine conjugue_eq hW h0 hspan hd ⟨hLM, ?_⟩ hc
  rw [codisjoint_iff, eq_top_iff, ← hspan, Submodule.span_le]
  intro w hw
  rw [hc, Set.mem_add] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  exact Submodule.add_mem_sup ha.1 hb.1

/-- Reading (c): a distinguished subspace conjugate to `L` in Déf. 1's sense is the complement. -/
theorem conjugue_eq_of_isSommeConvexes {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L M : Submodule ℝ E}
    (hL : EstDistingue W L) (hM : EstDistingue W M)
    (hc : IsSommeConvexes W ![(L : Set E) ∩ W, (M : Set E) ∩ W]) :
    conjugue W L = M := by
  have hc' : SontConjugues W L M := IsSommeConvexes.sontConjugues hc
  refine le_antisymm (conjugue_le_of_sontConjugues hW h0 hspan hd hL hM hc') ?_
  obtain ⟨hLc, hcL⟩ := conjugue_spec hL
  obtain ⟨hMc, hcM⟩ := conjugue_spec hM
  have hle := conjugue_le_of_sontConjugues hW h0 hspan hd hL hM hc'
  obtain ⟨-, hbij⟩ := (isSommeConvexes_iff_bijOn _ _).1 hc
  rw [← span_inter_eq_of_conjugues hMc.symm hcM.symm hspan, Submodule.span_le]
  rintro y ⟨hyM, hyW⟩
  have hP := projection_mem_inter hLc hcL hyW
  have hQ := projection_mem_inter hLc.symm hcL.symm hyW
  have h1 : ![L.projection (conjugue W L) hLc y, (conjugue W L).projection L hLc.symm y] ∈
      Set.univ.pi ![(L : Set E) ∩ W, (M : Set E) ∩ W] := by
    intro i _
    fin_cases i
    · simpa using hP
    · simpa using (⟨hle hQ.1, hQ.2⟩ : _ ∈ (M : Set E) ∩ W)
  have h2 : ![0, y] ∈ Set.univ.pi ![(L : Set E) ∩ W, (M : Set E) ∩ W] := by
    intro i _
    fin_cases i
    · simpa using (⟨L.zero_mem, h0⟩ : (0 : E) ∈ (L : Set E) ∩ W)
    · simpa using (⟨hyM, hyW⟩ : y ∈ (M : Set E) ∩ W)
  have e := hbij.injOn h1 h2 (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
    exact Submodule.projection_add_projection_eq_self hLc y)
  have e0 := congrFun e 0
  simp only [Matrix.cons_val_zero] at e0
  have := Submodule.projection_add_projection_eq_self hLc y
  rw [e0, zero_add] at this
  rw [← this]
  exact Submodule.projection_apply_mem _ _

/-! ### The Corollaire -/

/-- A *simple* distinguished subspace: minimal among the distinguished subspaces `≠ 0`. -/
def EstSimple (W : Set E) (L : Submodule ℝ E) : Prop :=
  EstDistingue W L ∧ L ≠ ⊥ ∧ ∀ M : Submodule ℝ E, EstDistingue W M → M ≠ ⊥ → M ≤ L → M = L

/-- The set of the simple distinguished subspaces. -/
def simples (W : Set E) : Set (Submodule ℝ E) := {L | EstSimple W L}

/-- Two different simple distinguished subspaces meet at `0`. -/
theorem inf_eq_bot_of_estSimple {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {s t : Submodule ℝ E}
    (hs : EstSimple W s) (ht : EstSimple W t) (hst : s ≠ t) : s ⊓ t = ⊥ := by
  by_contra hne
  obtain ⟨h1, h2⟩ := estDistingue_inf hW h0 hspan hd hs.1 ht.1
  have hst' : EstDistingue W (s ⊓ t) := ⟨_, h1, h2⟩
  have e1 := hs.2.2 _ hst' hne inf_le_left
  have e2 := ht.2.2 _ hst' hne inf_le_right
  exact hst (e1.symm.trans e2)

/-- The sum of a finite family of distinguished subspaces is distinguished. -/
theorem estDistingue_sSup {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {T : Set (Submodule ℝ E)}
    (hT : T.Finite) (hTd : ∀ L ∈ T, EstDistingue W L) : EstDistingue W (sSup T) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => rw [sSup_empty]; exact estDistingue_bot h0
  | @insert a T ha hT ih =>
    rw [sSup_insert]
    have h1 := hTd a (Set.mem_insert _ _)
    have h2 := ih fun L hL => hTd L (Set.mem_insert_of_mem _ hL)
    exact ⟨_, (estDistingue_sup hW h0 hspan hd h1 h2).1, (estDistingue_sup hW h0 hspan hd h1 h2).2⟩

/-- If `L` meets each member of a finite family of distinguished subspaces at `0`, it meets their
sum at `0` (distributivity, `inf_sup_le_of_estDistingue`). -/
theorem inf_sSup_eq_bot {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L : Submodule ℝ E}
    (hL : EstDistingue W L) {T : Set (Submodule ℝ E)} (hT : T.Finite)
    (hTd : ∀ t ∈ T, EstDistingue W t) (hLT : ∀ t ∈ T, L ⊓ t = ⊥) : L ⊓ sSup T = ⊥ := by
  induction T, hT using Set.Finite.induction_on with
  | empty => rw [sSup_empty, inf_bot_eq]
  | @insert a T ha hT ih =>
    rw [sSup_insert]
    have h1 := hTd a (Set.mem_insert _ _)
    have h2 := estDistingue_sSup hW h0 hspan hd hT fun t ht => hTd t (Set.mem_insert_of_mem _ ht)
    refine le_bot_iff.1 ((inf_sup_le_of_estDistingue hW h0 hspan hd hL h1 h2).trans ?_)
    rw [hLT a (Set.mem_insert _ _), ih (fun t ht => hTd t (Set.mem_insert_of_mem _ ht))
      (fun t ht => hLT t (Set.mem_insert_of_mem _ ht)), sup_bot_eq]


/-- A simple distinguished subspace lies in the sum of a finite family of simple distinguished
subspaces only if it belongs to the family. -/
theorem le_sSup_iff_mem_of_estSimple {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {T : Set (Submodule ℝ E)}
    (hT : T.Finite) (hTs : T ⊆ simples W) {s : Submodule ℝ E} (hs : EstSimple W s) :
    s ≤ sSup T ↔ s ∈ T := by
  refine ⟨fun hle => ?_, fun hs' => le_sSup hs'⟩
  by_contra hsT
  have hbot : s ⊓ sSup T = ⊥ := inf_sSup_eq_bot hW h0 hspan hd hs.1 hT
    (fun t ht => (hTs ht).1) fun t ht =>
      inf_eq_bot_of_estSimple hW h0 hspan hd hs (hTs ht) fun e => hsT (e ▸ ht)
  rw [inf_eq_left.2 hle] at hbot
  exact hs.2.1 hbot

variable [FiniteDimensional ℝ E]

/-- In finite dimension, every distinguished subspace `≠ 0` contains a simple one. -/
theorem exists_estSimple_le {W : Set E} {L : Submodule ℝ E} (hL : EstDistingue W L)
    (hL0 : L ≠ ⊥) : ∃ s, EstSimple W s ∧ s ≤ L := by
  obtain ⟨M, ⟨hM, hM0, hML⟩, hmin⟩ :=
    (measure fun M : Submodule ℝ E => Module.finrank ℝ M).wf.has_min
      {M | EstDistingue W M ∧ M ≠ ⊥ ∧ M ≤ L} ⟨L, hL, hL0, le_rfl⟩
  refine ⟨M, ⟨hM, hM0, fun N hN hN0 hNM => ?_⟩, hML⟩
  have := hmin N ⟨hN, hN0, hNM.trans hML⟩
  exact Submodule.eq_of_le_of_finrank_le hNM (not_lt.1 this)

/-- A finite family of `k` simple distinguished subspaces has a sum of dimension `≥ k`. -/
theorem ncard_le_finrank_sSup {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {T : Set (Submodule ℝ E)}
    (hT : T.Finite) (hTs : T ⊆ simples W) :
    T.ncard ≤ Module.finrank ℝ (sSup T : Submodule ℝ E) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert a T ha hT ih =>
    have haS : EstSimple W a := hTs (Set.mem_insert _ _)
    have hTs' : T ⊆ simples W := fun t ht => hTs (Set.mem_insert_of_mem _ ht)
    have hbot : a ⊓ sSup T = ⊥ := inf_sSup_eq_bot hW h0 hspan hd haS.1 hT
      (fun t ht => (hTs' ht).1) fun t ht =>
        inf_eq_bot_of_estSimple hW h0 hspan hd haS (hTs' ht) fun e => ha (e ▸ ht)
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq a (sSup T)
    rw [hbot, finrank_bot, add_zero] at hfr
    have ha1 : 1 ≤ Module.finrank ℝ a :=
      Nat.one_le_iff_ne_zero.2 fun h => haS.2.1 (Submodule.finrank_eq_zero.1 h)
    rw [Set.ncard_insert_of_notMem ha hT, sSup_insert, hfr]
    have := ih hTs'
    omega

/-- In dimension `n`, there are at most `n` simple distinguished subspaces. -/
theorem simples_finite_ncard_le {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    (simples W).Finite ∧ (simples W).ncard ≤ Module.finrank ℝ E := by
  have hfin : (simples W).Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (Module.finrank ℝ E + 1)
    have h1 := ncard_le_finrank_sSup hW h0 hspan hd t.finite_toSet hts
    rw [Set.ncard_coe_finset, htc] at h1
    have h2 := Submodule.finrank_le (sSup (t : Set (Submodule ℝ E)))
    omega
  exact ⟨hfin, (ncard_le_finrank_sSup hW h0 hspan hd hfin le_rfl).trans (Submodule.finrank_le _)⟩

/-- Every distinguished subspace is the sum of the simple ones it contains. -/
theorem eq_sSup_simples_le {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L : Submodule ℝ E}
    (hL : EstDistingue W L) : sSup {s | s ∈ simples W ∧ s ≤ L} = L := by
  have hfin := (simples_finite_ncard_le hW h0 hspan hd).1
  set T := {s | s ∈ simples W ∧ s ≤ L}
  have hTf : T.Finite := hfin.subset fun s hs => hs.1
  have hM := estDistingue_sSup hW h0 hspan hd hTf fun s hs => hs.1.1
  have hML : sSup T ≤ L := sSup_le fun s hs => hs.2
  obtain ⟨hMc, hcM⟩ := conjugue_spec hM
  have hN : EstDistingue W (L ⊓ conjugue W (sSup T)) :=
    ⟨_, (estDistingue_inf hW h0 hspan hd hL (estDistingue_conjugue hM)).1,
      (estDistingue_inf hW h0 hspan hd hL (estDistingue_conjugue hM)).2⟩
  by_cases hN0 : L ⊓ conjugue W (sSup T) = ⊥
  · refine le_antisymm hML ?_
    have h := inf_sup_le_of_estDistingue hW h0 hspan hd hL hM (estDistingue_conjugue hM)
    rw [hMc.sup_eq_top, inf_top_eq, hN0, sup_bot_eq] at h
    exact h.trans inf_le_right
  · exfalso
    obtain ⟨s, hs, hsN⟩ := exists_estSimple_le hN hN0
    have hsT : s ∈ T := ⟨hs, hsN.trans inf_le_left⟩
    have h1 : s ≤ sSup T := le_sSup hsT
    have h2 : s ≤ conjugue W (sSup T) := hsN.trans inf_le_right
    exact hs.2.1 (le_bot_iff.1 (hMc.disjoint.le_bot.trans' (le_inf h1 h2)))

/-- The sum of a set of simple distinguished subspaces, as a distinguished subspace. -/
theorem estDistingue_sSup_simples {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {T : Set (Submodule ℝ E)}
    (hT : T ⊆ simples W) : EstDistingue W (sSup T) :=
  estDistingue_sSup hW h0 hspan hd ((simples_finite_ncard_le hW h0 hspan hd).1.subset hT)
    fun _ hs => (hT hs).1

/-- Sums of sets of simple distinguished subspaces are ordered as the sets. -/
theorem sSup_le_sSup_iff_of_simples {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {T T' : Set (Submodule ℝ E)}
    (hT : T ⊆ simples W) (hT' : T' ⊆ simples W) : sSup T ≤ sSup T' ↔ T ⊆ T' := by
  refine ⟨fun h s hs => ?_, sSup_le_sSup⟩
  exact (le_sSup_iff_mem_of_estSimple hW h0 hspan hd
    ((simples_finite_ncard_le hW h0 hspan hd).1.subset hT') hT' (hT hs)).1 ((le_sSup hs).trans h)

/-- **Corollaire**, the isomorphism: the subsets of the set of simple distinguished subspaces,
ordered by inclusion, are isomorphic to the distinguished subspaces, ordered by inclusion, by
`T ↦ ∑ T` (an order isomorphism of Boolean algebras is a Boolean algebra isomorphism). -/
noncomputable def isoParties {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    Set (simples W) ≃o Distingues W :=
  have hle : ∀ T T' : Set (simples W),
      (⟨sSup (Subtype.val '' T), estDistingue_sSup_simples hW h0 hspan hd
        (Subtype.coe_image_subset _ T)⟩ : Distingues W) ≤
        ⟨sSup (Subtype.val '' T'), estDistingue_sSup_simples hW h0 hspan hd
          (Subtype.coe_image_subset _ T')⟩ ↔ T ⊆ T' := fun T T' => by
    rw [Subtype.mk_le_mk, sSup_le_sSup_iff_of_simples hW h0 hspan hd
      (Subtype.coe_image_subset _ T) (Subtype.coe_image_subset _ T'),
      Set.image_subset_image_iff Subtype.val_injective]
  { toFun := fun T => ⟨sSup (Subtype.val '' T), estDistingue_sSup_simples hW h0 hspan hd
        (Subtype.coe_image_subset _ T)⟩
    invFun := fun L => {s | s.1 ≤ L.1}
    left_inv := fun T => by
      refine Set.Subset.antisymm (fun s hs => ?_) fun s hs =>
        show s.1 ≤ sSup (Subtype.val '' T) from le_sSup ⟨s, hs, rfl⟩
      have := (le_sSup_iff_mem_of_estSimple hW h0 hspan hd
        ((simples_finite_ncard_le hW h0 hspan hd).1.subset (Subtype.coe_image_subset _ T))
        (Subtype.coe_image_subset _ T) s.2).1 hs
      obtain ⟨t, ht, e⟩ := this
      exact Subtype.val_injective e ▸ ht
    right_inv := fun L => by
      refine Subtype.ext ?_
      have e : Subtype.val '' {s : simples W | s.1 ≤ L.1} = {s | s ∈ simples W ∧ s ≤ L.1} := by
        ext s
        exact ⟨fun ⟨t, ht, e⟩ => e ▸ ⟨t.2, ht⟩, fun h => ⟨⟨s, h.1⟩, h.2, rfl⟩⟩
      change sSup (Subtype.val '' {s : simples W | s.1 ≤ L.1}) = L.1
      rw [e]
      exact eq_sSup_simples_le hW h0 hspan hd L.2
    map_rel_iff' := fun {T T'} => hle T T' }

theorem isoParties_apply {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) (T : Set (simples W)) :
    (isoParties hW h0 hspan hd T).1 = sSup (Subtype.val '' T) :=
  rfl

/-- **Corollaire** (l.535), corrected at `n = 0`: if `E` has finite dimension `n`, the
distinguished subspaces are, as a Boolean algebra, the subsets of the finite set of simple
distinguished subspaces, whose cardinal is at most `n`, and at least `1` when `n ≥ 1`; every
distinguished subspace is, in one and only one way, the sum of a family of simple ones. -/
theorem corollaire_algebre_parties {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    (simples W).Finite ∧ (simples W).ncard ≤ Module.finrank ℝ E ∧
      (0 < Module.finrank ℝ E → 1 ≤ (simples W).ncard) ∧
      (∃ e : Set (simples W) ≃o Distingues W, ∀ T, (e T).1 = sSup (Subtype.val '' T)) ∧
      (∀ T ⊆ simples W, EstDistingue W (sSup T)) ∧
      (∀ L : Submodule ℝ E, EstDistingue W L →
        ∃! T : Set (Submodule ℝ E), T ⊆ simples W ∧ sSup T = L) := by
  obtain ⟨hfin, hcard⟩ := simples_finite_ncard_le hW h0 hspan hd
  refine ⟨hfin, hcard, fun hpos => ?_, ⟨isoParties hW h0 hspan hd,
    isoParties_apply hW h0 hspan hd⟩, fun T hT => estDistingue_sSup_simples hW h0 hspan hd hT,
    fun L hL => ⟨{s | s ∈ simples W ∧ s ≤ L}, ⟨fun s hs => hs.1, eq_sSup_simples_le hW h0 hspan hd hL⟩,
      fun T ⟨hT, hTL⟩ => ?_⟩⟩
  · have htop : (⊤ : Submodule ℝ E) ≠ ⊥ := fun h => by
      have := finrank_top ℝ E
      rw [h, finrank_bot] at this
      omega
    obtain ⟨s, hs, -⟩ := exists_estSimple_le (estDistingue_top h0) htop
    exact (Set.ncard_pos hfin).2 ⟨s, hs⟩
  · ext s
    refine ⟨fun hs => ⟨hT hs, hTL ▸ le_sSup hs⟩, fun ⟨hs, hsL⟩ => ?_⟩
    exact (le_sSup_iff_mem_of_estSimple hW h0 hspan hd (hfin.subset hT) hT hs).1 (hTL ▸ hsL)

/-- At `n = 0` the printed lower bound `1` fails: there is no simple distinguished subspace
(and a single distinguished subspace, `0 = E`). -/
theorem simples_eq_empty_of_finrank_eq_zero {W : Set E} (hE : Module.finrank ℝ E = 0) :
    simples W = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun L hL => hL.2.1 ?_
  exact Submodule.finrank_eq_zero.1 (Nat.le_zero.1 (hE ▸ Submodule.finrank_le L))

end BooleAffine

/-! ### Instances: the cube (cardinal `n`), the ball (cardinal `1`), dimension `0` -/

theorem mem_coord_iff {n : ℕ} (S : Set (Fin n)) (x : Fin n → ℝ) :
    x ∈ coord S ↔ ∀ j, j ∉ S → x j = 0 := by
  simp only [coord, Submodule.mem_pi, Submodule.mem_bot, Set.mem_compl_iff]

/-- In the cube `[−1, 1]ⁿ` the coordinate axis `ℝ eᵢ` is a simple distinguished subspace. -/
theorem cube_estSimple_coord {n : ℕ} (i : Fin n) : EstSimple (cube n) (coord {i}) := by
  refine ⟨(cube_coord_distingue {i}).1, ?_, fun M _ hM0 hMi => ?_⟩
  · intro h
    have : Pi.single i (1 : ℝ) ∈ coord ({i} : Set (Fin n)) := by
      rw [mem_coord_iff]; intro j hj
      exact Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hj) _
    rw [h, Submodule.mem_bot] at this
    have := congrFun this i
    simp at this
  · refine le_antisymm hMi fun w hw => ?_
    obtain ⟨v, hvM, hv0⟩ := (Submodule.ne_bot_iff M).1 hM0
    have hvi := (mem_coord_iff _ _).1 (hMi hvM)
    have hwi := (mem_coord_iff _ _).1 hw
    have hvi0 : v i ≠ 0 := by
      intro h; apply hv0; funext j
      by_cases hj : j = i
      · subst hj; exact h
      · exact hvi j hj
    have : w = (w i / v i) • v := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [div_mul_cancel₀ _ hvi0]
      · simp [hvi j hj, hwi j hj]
    rw [this]
    exact M.smul_mem _ hvM

/-- **The cube** (« `n` au cube »): the simple distinguished subspaces of `[−1, 1]ⁿ` are the `n`
coordinate axes. -/
theorem cube_simples (n : ℕ) : simples (cube n) = Set.range fun i : Fin n => coord {i} := by
  obtain ⟨hc, h0, hspan, hd⟩ := cube_hyps n
  have hd' : ¬ ContientDroite (cube n) := fun h => hd h.contientDemiDroite
  refine Set.Subset.antisymm (fun s hs => ?_) ?_
  · have hT : (Set.range fun i : Fin n => coord ({i} : Set (Fin n))) ⊆ simples (cube n) := by
      rintro _ ⟨i, rfl⟩; exact cube_estSimple_coord i
    have htop : sSup (Set.range fun i : Fin n => coord ({i} : Set (Fin n))) = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : Pi.single i (x i) ∈ coord ({i} : Set (Fin n)) := by
        rw [mem_coord_iff]; intro j hj
        exact Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hj) _
      have hle : coord ({i} : Set (Fin n)) ≤
          sSup (Set.range fun i : Fin n => coord ({i} : Set (Fin n))) := le_sSup ⟨i, rfl⟩
      exact hle hi
    exact (le_sSup_iff_mem_of_estSimple hc h0 hspan hd' (Set.finite_range _) hT hs).1
      (htop ▸ le_top)
  · rintro _ ⟨i, rfl⟩; exact cube_estSimple_coord i

theorem cube_simples_ncard (n : ℕ) : (simples (cube n)).ncard = n := by
  rw [cube_simples, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro i j h
  have h' : coord ({i} : Set (Fin n)) = coord {j} := h
  have : Pi.single i (1 : ℝ) ∈ coord ({j} : Set (Fin n)) := by
    rw [← h', mem_coord_iff]; intro k hk
    exact Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hk) _
  by_contra hij
  have := (mem_coord_iff _ _).1 this i (Set.mem_singleton_iff.not.2 hij)
  simp at this

/-- The instance at `n = 0`, where the printed lower bound `1` fails: `[−1, 1]⁰` satisfies the
hypotheses of Théorème 2, has no simple distinguished subspace, and a single distinguished
subspace, so its Boolean algebra is the algebra of parts of no set of cardinal `≥ 1`. -/
theorem cube_zero_corollaire :
    Convex ℝ (cube 0) ∧ (0 : Fin 0 → ℝ) ∈ cube 0 ∧ Submodule.span ℝ (cube 0) = ⊤ ∧
      ¬ ContientDroite (cube 0) ∧ simples (cube 0) = ∅ ∧ Subsingleton (Distingues (cube 0)) ∧
      ∀ (X : Type) [Nonempty X], IsEmpty (Set X ≃o Distingues (cube 0)) := by
  obtain ⟨hc, h0, hspan, hd⟩ := cube_hyps 0
  have hsub : Subsingleton (Distingues (cube 0)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Submodule ℝ (Fin 0 → ℝ)) _ _)⟩
  refine ⟨hc, h0, hspan, fun h => hd h.contientDemiDroite,
    simples_eq_empty_of_finrank_eq_zero (by simp), hsub, fun X _ => ⟨fun e => ?_⟩⟩
  have h := e.injective (Subsingleton.elim (e ∅) (e Set.univ))
  exact Set.empty_ne_univ h

/-- Théorème 2 on the cube: the Boolean algebra of the distinguished subspaces of `[−1, 1]ⁿ`,
and its isomorphism with the parts of the `n` axes. -/
@[implicit_reducible]
noncomputable def cube_algebreBoole (n : ℕ) : BooleanAlgebra (Distingues (cube n)) :=
  algebreBoole (cube_hyps n).1 (cube_hyps n).2.1 (cube_hyps n).2.2.1
    fun h => (cube_hyps n).2.2.2 h.contientDemiDroite

noncomputable def cube_isoParties (n : ℕ) : Set (simples (cube n)) ≃o Distingues (cube n) :=
  isoParties (cube_hyps n).1 (cube_hyps n).2.1 (cube_hyps n).2.2.1
    fun h => (cube_hyps n).2.2.2 h.contientDemiDroite

/-- Reading (a) of Déf. 4 (OQ-163), « le conjugué » taken as *any* conjugate: relative to the
half-line `[0, ∞[ ⊂ ℝ` (convex, containing `0`, spanning, with no line), `ℝ` is distinguished and
conjugate to itself as printed, while its complement in the Boolean algebra is `0`. So the
complement is a conjugate, the one meeting `L` at `0` (`conjugue_eq_of_disjoint`), not every
conjugate. -/
theorem demiDroite_complement_conjugue :
    EstDistingue (Set.Ici (0 : ℝ)) ⊤ ∧ SontConjugues (Set.Ici (0 : ℝ)) ⊤ ⊤ ∧
      conjugue (Set.Ici (0 : ℝ)) ⊤ = ⊥ ∧ (⊥ : Submodule ℝ ℝ) ≠ ⊤ := by
  obtain ⟨hc, -, hd, hspan⟩ := demiDroite_conjugues_non_supplementaires
  have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.self_mem_Ici
  have htop := estDistingue_top (W := Set.Ici (0 : ℝ)) h0
  obtain ⟨M, hM, hcM⟩ := htop
  have hM0 : M = ⊥ := eq_bot_of_isCompl_top hM.symm
  subst hM0
  refine ⟨⟨⊥, hM, hcM⟩, hc, conjugue_eq (convex_Ici 0) h0 hspan hd hM hcM, ?_⟩
  intro h
  have : (1 : ℝ) ∈ (⊥ : Submodule ℝ ℝ) := h ▸ Submodule.mem_top
  simp at this

section Boule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed unit ball satisfies the hypotheses of Théorème 2. -/
theorem boule_hyps : Convex ℝ (Metric.closedBall (0 : E) 1) ∧
    (0 : E) ∈ Metric.closedBall (0 : E) 1 ∧ Submodule.span ℝ (Metric.closedBall (0 : E) 1) = ⊤ ∧
    ¬ ContientDroite (Metric.closedBall (0 : E) 1) := by
  refine ⟨convex_closedBall 0 1, Metric.mem_closedBall_self zero_le_one, ?_,
    fun h => not_contientDemiDroite_of_isBounded Metric.isBounded_closedBall h.contientDemiDroite⟩
  refine eq_top_iff.2 fun x _ => ?_
  by_cases hx : x = 0
  · rw [hx]; exact Submodule.zero_mem _
  · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hx', one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx']

/-- **The ball** (« `1` correspond à la sphère »): the only simple distinguished subspace of the
closed unit ball of a nonzero real inner product space is `E`. -/
theorem boule_simples [Nontrivial E] : simples (Metric.closedBall (0 : E) 1) = {⊤} := by
  ext L
  simp only [simples, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hL, hL0, -⟩
    exact ((boule_estDistingue_iff L).1 hL).resolve_left hL0
  · rintro rfl
    refine ⟨(boule_estDistingue_iff ⊤).2 (Or.inr rfl), top_ne_bot, fun M hM hM0 _ => ?_⟩
    exact ((boule_estDistingue_iff M).1 hM).resolve_left hM0

theorem boule_simples_ncard [Nontrivial E] : (simples (Metric.closedBall (0 : E) 1)).ncard = 1 := by
  rw [boule_simples, Set.ncard_singleton]

end Boule

end Benzecri
