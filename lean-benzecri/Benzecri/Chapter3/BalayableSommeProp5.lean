import Benzecri.Chapter3.BalayableSommeProduit

/-!
# Chapter 3 § 2, Proposition 5: `w` is sweepable (resp. homogeneous) iff every `vᵢ` is

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-balayable-somme-prop5.

* `bzprop:c3s2p5_balayable_somme` — `benzecri1960_ch3.tex:613` (Prop. 5, l.613–621), NOT marked
  (it inherits Prop. 4's added hypothesis `¬ ContientDroite (F w)`, OQ-168, and the reading of
  « avec les notations de la proposition 4 », OQ-171): `Benzecri.Sphere.prop5_balayable_somme`,
  PROVED with no `sorry`: for every enumeration `l` of the simple distinguished subvarieties and
  every choice of bases `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}`, with `Bᵢ = s(bᵢ(F(vᵢ)))` open in `S(nᵢ)`,
  `w` is homogeneous iff every `Bᵢ` is, and `w` is sweepable iff every `Bᵢ` is.
  The general transport along a projective isomorphism is `Benzecri.IsProjIso.isHomogeneous_iff`
  and `Benzecri.IsProjIso.isBalayable_iff`. The instance is the open simplex
  (`BooleProjectifInstance.simplexO_prop5`, and `simplexO_isHomogeneous`: the open simplex is
  homogeneous, by the ⇐ direction, every `Bᵢ` being a point of `S(0)`).

> **Proposition 5.** Avec les notations de la proposition 4, $w$ est balayable (resp. homogène)
> si et seulement si les $v_i$ le sont.
>
> *Démonstration.* Cette proposition résulte de la précédente et de la proposition 4 du
> chapitre 1, paragraphe 3.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « avec les notations de la proposition 4 »: `w` ouvert, convexe, de noyau vide | ✓ carried |
| (not printed) `F(w)` contains no line | ⚠ ADDED (OQ-168), inherited from `prop4_produit`; without it Prop. 4 is false (`not_prop4_simplesS_finite`) |
| (not printed) `w ≠ ∅` | ⚠ reading: `w.Nonempty` |
| « les $v_i$ » | reading: `Bᵢ = s(bᵢ(F(vᵢ))) ⊆ S(nᵢ)`, for EVERY enumeration `l` and EVERY bases `bᵢ` (bases exist, `exists_bases_simplesS`) |
| « balayable (resp. homogène) » | Déf. 15: `IsBalayable`, `IsHomogeneous` of `w` (an `Opens` of `S(m)`) and of each `Bᵢ` |

## SCOPE (disclosed)

* **⇒** (the printed proof's route): through `prop4_produit` (`Ψ : PiBase ≃ₜ w`, every
  automorphism of `w` compatible once transported), the group of compatible automorphisms of
  `F⁻¹(F(B₀) × … × F(B_q))` is transitive (resp. sweeps with the compact `Ψ⁻¹(K)`), and
  Ch. 1 § 3 Prop. 4 (`homogeneous_of_compatible_pi`, `balayable_of_compatible_pi`) applies,
  each `Bᵢ` being nonempty (`Produit.nonempty_cset`).
* **⇐**: a step the printed proof does not cite — Ch. 1 § 3 **Prop. 3** (`isHomogeneous_piBase`,
  `isBalayable_piBase`), then the transport along `Ψ` (`IsProjIso.isHomogeneous_iff`,
  `IsProjIso.isBalayable_iff`, by conjugation `Ψ ∘ g ∘ Ψ⁻¹`).
* Not marked: OQ-168 (added hypothesis), OQ-171 (the reading of Prop. 4's notations), as for
  `prop4_produit`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function
open scoped Pointwise

namespace Benzecri

attribute [local instance] t2Space_RnO

section Transport

variable {k k' : ℕ} {X Y : Type*} [TopologicalSpace X] [ChartedSpace (S k) X]
  [TopologicalSpace Y] [ChartedSpace (S k') Y]

/-- **Conjugation along a projective isomorphism**: `Ψ ∘ g ∘ Ψ⁻¹` is an automorphism of `Y`. -/
theorem IsProjIso.conj {Ψ : X ≃ₜ Y} (hΨ : IsProjIso k k' Ψ) (g : GXAut (GSR k) (S k) X) :
    ∃ g' : GXAut (GSR k') (S k') Y, ∀ x, g' • Ψ x = Ψ (g • x) := by
  have h : IsProjIso k' k' ((Ψ.symm.trans g.toHomeomorph).trans Ψ) :=
    (hΨ.symm.trans ⟨rfl, g.isGXMorphism⟩).trans hΨ
  refine ⟨h.toAut, fun x => ?_⟩
  rw [IsProjIso.toAut_smul]
  simp [GXAut.smul_def]

/-- A homogeneous manifold stays homogeneous along a projective isomorphism. -/
theorem IsProjIso.isHomogeneous {Ψ : X ≃ₜ Y} (hΨ : IsProjIso k k' Ψ)
    (h : IsHomogeneous (GSR k) (S k) X) : IsHomogeneous (GSR k') (S k') Y := by
  refine ⟨fun y y' => ?_⟩
  obtain ⟨g, hg⟩ := h.exists_smul_eq (Ψ.symm y) (Ψ.symm y')
  obtain ⟨g', hg'⟩ := hΨ.conj g
  refine ⟨g', ?_⟩
  rw [← Ψ.apply_symm_apply y, hg', hg, Ψ.apply_symm_apply]

/-- A sweepable manifold stays sweepable along a projective isomorphism. -/
theorem IsProjIso.isBalayable {Ψ : X ≃ₜ Y} (hΨ : IsProjIso k k' Ψ)
    (h : IsBalayable (GSR k) (S k) X) : IsBalayable (GSR k') (S k') Y := by
  obtain ⟨K, hK, hU⟩ := h
  refine ⟨Ψ '' K, hK.image Ψ.continuous, eq_univ_of_forall fun y => ?_⟩
  have hy : Ψ.symm y ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR k) (S k) X)), g • K := hU ▸ mem_univ _
  obtain ⟨g, -, x, hx, hxy⟩ := mem_iUnion₂.1 hy
  obtain ⟨g', hg'⟩ := hΨ.conj g
  refine mem_iUnion₂.2 ⟨g', Subgroup.mem_top _, Ψ x, ⟨x, hx, rfl⟩, ?_⟩
  show g' • Ψ x = y
  rw [hg']
  have hxy' : g • x = Ψ.symm y := hxy
  rw [hxy', Ψ.apply_symm_apply]

/-- **Homogeneity is a projective invariant.** -/
theorem IsProjIso.isHomogeneous_iff {Ψ : X ≃ₜ Y} (hΨ : IsProjIso k k' Ψ) :
    IsHomogeneous (GSR k) (S k) X ↔ IsHomogeneous (GSR k') (S k') Y :=
  ⟨hΨ.isHomogeneous, hΨ.symm.isHomogeneous⟩

/-- **Sweepability is a projective invariant.** -/
theorem IsProjIso.isBalayable_iff {Ψ : X ≃ₜ Y} (hΨ : IsProjIso k k' Ψ) :
    IsBalayable (GSR k) (S k) X ↔ IsBalayable (GSR k') (S k') Y :=
  ⟨hΨ.isBalayable, hΨ.symm.isBalayable⟩

end Transport

namespace Sphere
open Produit PiCone

section General

universe u

variable {m q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)] [∀ i, Nonempty (B i)] {W : Type*} [TopologicalSpace W]
  [ChartedSpace (S m) W]

/-- **Prop. 5's proof, abstractly**: if `W` is projectively isomorphic to
`F⁻¹(F(B₀) × … × F(B_q))` by a `Ψ` under which every automorphism of `W` is compatible (the
conclusion of Prop. 4), then `W` is sweepable (resp. homogeneous) iff every `Bᵢ` is: ⇒ by Ch. 1
§ 3 Prop. 4, ⇐ by Ch. 1 § 3 Prop. 3 and the transport along `Ψ`. -/
theorem prop5_of_compatible (Ψ : PiBase n B ≃ₜ W) (hΨ : IsProjIso (pdim n) m Ψ)
    (hcomp : ∀ f : GXAut (GSR m) (S m) W,
      ∃ h : IsProjIso (pdim n) (pdim n) ((Ψ.trans f.toHomeomorph).trans Ψ.symm),
        IsCompatiblePi h.toAut) :
    (IsBalayable (GSR m) (S m) W ↔ ∀ i, IsBalayable (GSR (n i)) (S (n i)) (B i)) ∧
      (IsHomogeneous (GSR m) (S m) W ↔ ∀ i, IsHomogeneous (GSR (n i)) (S (n i)) (B i)) := by
  have key : ∀ f : GXAut (GSR m) (S m) W, ∃ c ∈ compatibleSubgroup n B,
      ∀ x, c • x = Ψ.symm (f • Ψ x) := fun f =>
    (hcomp f).elim fun h hc => ⟨h.toAut, hc, fun x => by rw [IsProjIso.toAut_smul]; rfl⟩
  refine ⟨⟨fun hW => ?_, fun h => hΨ.isBalayable (isBalayable_piBase h)⟩,
    ⟨fun hW => ?_, fun h => hΨ.isHomogeneous (isHomogeneous_piBase h)⟩⟩
  · obtain ⟨K, hK, hU⟩ := hW
    refine balayable_of_compatible_pi ⟨Ψ.symm '' K, hK.image Ψ.symm.continuous,
      eq_univ_of_forall fun x => ?_⟩
    have hx : Ψ x ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR m) (S m) W)), g • K := hU ▸ mem_univ _
    obtain ⟨f, -, y, hy, hyx⟩ := mem_iUnion₂.1 hx
    obtain ⟨c, hc, hcx⟩ := key f
    refine mem_iUnion₂.2 ⟨c, hc, Ψ.symm y, ⟨y, hy, rfl⟩, ?_⟩
    show c • Ψ.symm y = x
    have hyx' : f • y = Ψ x := hyx
    rw [hcx, Ψ.apply_symm_apply, hyx', Ψ.symm_apply_apply]
  · refine homogeneous_of_compatible_pi ⟨fun x x' => ?_⟩
    obtain ⟨f, hf⟩ := hW.exists_smul_eq (Ψ x) (Ψ x')
    obtain ⟨c, hc, hcx⟩ := key f
    refine ⟨⟨c, hc⟩, ?_⟩
    show c • x = x'
    rw [hcx, hf, Ψ.symm_apply_apply]

end General

variable {m : ℕ}

/-- **Prop. 5** (`bzprop:c3s2p5_balayable_somme`, NOT marked: OQ-168, OQ-171): in the notation of
Prop. 4 (`prop4_produit`), for every enumeration `l` of the simple distinguished subvarieties and
every bases `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}`, `w` is homogeneous iff every `Bᵢ = s(bᵢ(F(vᵢ)))` is, and
sweepable iff every `Bᵢ` is. -/
theorem prop5_balayable_somme {w : Set (S m)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hne : w.Nonempty) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) {q : ℕ}
    (l : Fin (q + 1) ≃ simplesS w) (n : Fin (q + 1) → ℕ)
    (b : ∀ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ)) :
    ∃ hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS w (l i))) : Set (S (n i))),
      (IsBalayable (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) ↔
        ∀ i, IsBalayable (GSR (n i)) (S (n i))
          (⟨_, hB i⟩ : TopologicalSpace.Opens (S (n i)))) ∧
      (IsHomogeneous (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) ↔
        ∀ i, IsHomogeneous (GSR (n i)) (S (n i))
          (⟨_, hB i⟩ : TopologicalSpace.Opens (S (n i)))) := by
  have H : Hyps4 w := ⟨hw, hopen, hne, hn, hd⟩
  refine (prop4_produit hw hopen hne hn hd l n b).elim fun hB hΨ => ⟨hB, ?_⟩
  haveI : ∀ i, Nonempty (⟨_, hB i⟩ : TopologicalSpace.Opens (S (n i))) := fun i =>
    (nonempty_cset (l := l) (b := b) H i).to_subtype
  exact hΨ.elim fun Ψ h => prop5_of_compatible Ψ h.1 h.2

end Sphere

section PointS0

/-- A convex cone of `ℝ¹` avoiding `O` lies in one half-line: its image in `S(0)` has at most one
point. -/
theorem subsingleton_ofCone_S0 {C : Set (Fin 1 → ℝ)} (hC : Convex ℝ C)
    (h0 : (0 : Fin 1 → ℝ) ∉ C) : (Sphere.ofCone C : Set (S 0)).Subsingleton := by
  intro x hx y hy
  obtain ⟨u, hu, huC, rfl⟩ := Sphere.mem_ofCone.1 hx
  obtain ⟨v, hv, hvC, rfl⟩ := Sphere.mem_ofCone.1 hy
  have hfun : ∀ z : Fin 1 → ℝ, z = fun _ => z 0 := fun z => funext fun i => by
    rw [Subsingleton.elim i 0]
  have ha : u 0 ≠ 0 := fun h => hu (by rw [hfun u, h]; rfl)
  have hb : v 0 ≠ 0 := fun h => hv (by rw [hfun v, h]; rfl)
  rcases lt_or_gt_of_ne (mul_ne_zero ha hb) with hab | hab
  · exfalso
    have hba : v 0 - u 0 ≠ 0 := by
      intro h
      have : v 0 = u 0 := by linarith
      rw [this] at hab
      nlinarith [mul_self_pos.2 ha]
    have hs : 0 ≤ v 0 / (v 0 - u 0) := by
      rcases lt_or_gt_of_ne ha with h1 | h1
      · have : 0 < v 0 := by nlinarith
        exact div_nonneg this.le (by linarith)
      · have : v 0 < 0 := by nlinarith
        exact div_nonneg_of_nonpos this.le (by linarith)
    have ht : 0 ≤ -u 0 / (v 0 - u 0) := by
      rcases lt_or_gt_of_ne ha with h1 | h1
      · have : 0 < v 0 := by nlinarith
        exact div_nonneg (by linarith) (by linarith)
      · have : v 0 < 0 := by nlinarith
        exact div_nonneg_of_nonpos (by linarith) (by linarith)
    have hst : v 0 / (v 0 - u 0) + -u 0 / (v 0 - u 0) = 1 := by
      field_simp
      ring
    have hmem := hC huC hvC hs ht hst
    apply h0
    convert hmem using 1
    funext i
    rw [Subsingleton.elim i 0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · refine (Sphere.mk_eq_mk_iff_exists_pos hu hv).2 ⟨v 0 / u 0, ?_, ?_⟩
    · rcases lt_or_gt_of_ne ha with h1 | h1
      · exact div_pos_of_neg_of_neg (by nlinarith) h1
      · exact div_pos (by nlinarith) h1
    · funext i
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

/-- **An open subset of `S(0)` image of a convex cone avoiding `O` is homogeneous** (it is a point
or empty; the dimension is passed as an equation so that it can be a variable). -/
theorem isHomogeneous_ofCone_S0 {k : ℕ} (hk : k = 0) {C : Set (Fin (k + 1) → ℝ)}
    (hC : Convex ℝ C) (h0 : (0 : Fin (k + 1) → ℝ) ∉ C)
    (hB : IsOpen (Sphere.ofCone C : Set (S k))) :
    IsHomogeneous (GSR k) (S k) (⟨_, hB⟩ : TopologicalSpace.Opens (S k)) := by
  subst hk
  haveI : Subsingleton (⟨_, hB⟩ : TopologicalSpace.Opens (S 0)) :=
    (subsingleton_ofCone_S0 hC h0).coe_sort
  exact ⟨fun x y => ⟨1, by rw [one_smul]; exact Subsingleton.elim _ _⟩⟩

end PointS0

namespace BooleProjectifInstance

open Sphere Produit

/-- **The instance of `prop5_balayable_somme`: the open `n`-simplex** of `S(n)` (`p = n + 1`)
with bases from `exists_bases_simplesS` satisfies its hypotheses and its conclusion. -/
theorem simplexO_prop5 {n : ℕ} :
    ∃ (l : Fin (n + 1) ≃ simplesS (simplexO n)) (k : Fin (n + 1) → ℕ)
      (b : ∀ i, (l i : Submodule ℝ (Fin (n + 1) → ℝ)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
      (hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS (simplexO n) (l i))) :
        Set (S (k i)))),
      (IsBalayable (GSR n) (S n)
          (⟨simplexO n, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S n)) ↔
        ∀ i, IsBalayable (GSR (k i)) (S (k i)) (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) ∧
      (IsHomogeneous (GSR n) (S n)
          (⟨simplexO n, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S n)) ↔
        ∀ i, IsHomogeneous (GSR (k i)) (S (k i)) (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := n)
  refine (simplexO_prop4 (n := n)).elim fun l _ => ?_
  refine (exists_bases_simplesS l).elim fun k hk => hk.elim fun b => ?_
  exact ⟨l, k, b, prop5_balayable_somme h1 h2 h3 h4 h5 l k b⟩

/-- **Prop. 5 ⇐ at work: the open `n`-simplex is homogeneous.** Its `n + 1` simple
distinguished subvarieties are lines (`Σ (kᵢ + 1) = n + 1`, `Produit.pdim_eq`), so each `Bᵢ` is a
point of `S(0)`, trivially homogeneous. -/
theorem simplexO_isHomogeneous {n : ℕ} :
    IsHomogeneous (GSR n) (S n) (⟨simplexO n, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S n)) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := n)
  have H : Hyps4 (simplexO n) := ⟨h1, h2, h3, h4, h5⟩
  refine (simplexO_prop4 (n := n)).elim fun l _ => ?_
  refine (exists_bases_simplesS l).elim fun k hk => hk.elim fun b => ?_
  have hk0 : ∀ i, k i = 0 := by
    have hp := pdim_eq (l := l) (n := k) (b := b) H
    have hs : ∑ i, k i = 0 := by
      simp only [pdim] at hp
      omega
    intro i
    exact (Finset.sum_eq_zero_iff.1 hs) i (Finset.mem_univ i)
  obtain ⟨hB, -, hhom⟩ := prop5_balayable_somme h1 h2 h3 h4 h5 l k b
  refine hhom.2 fun i => isHomogeneous_ofCone_S0 (hk0 i) ?_ (zero_notMem_cset H i) (hB i)
  exact ((H.convex_sommande _).linear_preimage (Submodule.subtype _)).linear_image
    (b i).toLinearMap

end BooleProjectifInstance

end Benzecri
