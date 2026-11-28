import Benzecri.Chapter3.BooleAffine
import Benzecri.Chapter3.DualiteSn

/-!
# Chapter 3 § 2 (sphere) — Déf. 5, Déf. 6, Théorème 3 and its Corollary: sums of convex parts of S(E), distinguished subvarieties, their Boolean algebra

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal pp. 267–268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR; checked here
against the page images, PDF pp. 40–41). Target T-bz-c3-boole-projectif.

* **`bzdef:c3s2d5_somme_sphere`** — `benzecri1960_ch3.tex:548` (Déf. 5, l.548–558): the general
  form `Benzecri.Sphere.EstSommeS` (the `F(vᵢ)` convex, `F(w)` their sum in Déf. 1's sense,
  `IsSommeConvexes`), the two-summand form with the convention `Benzecri.Sphere.EstSomme2`
  (`joint`, the union of the open segments), and « En particulier » proved:
  `estSomme2_iff_estSommeS` (with `F_joint`, `convex_F_of_joint`); the convention is not a case
  of the general form, `eq_empty_of_estSommeS_vide`.
* `bzdef:c3s2d6_distingue_projectif` — `benzecri1960_ch3.tex:560` (Déf. 6, l.560–567), NOT
  marked: `EstConjugueS`, `EstDistingueS`, on the cone `estConjugueS_iff` (`ConeDec`). The
  claim « La donnée du sous-espace distingué `l` détermine complètement `l′` » is FALSE as
  printed (`BooleProjectifInstance.not_conjugue_unique`, the open quarter of `S(2)`); proved
  when `F(w)` contains no line, `conjugue_unique`.
* `bzthm:c3s2t3_algebre_boole_projective` — `benzecri1960_ch3.tex:570` (Théorème 3,
  l.570–576), NOT marked: FALSE as printed (`BooleProjectifInstance.not_theoreme3`, even with
  no line in `F(w)`); proved for `w` open with no line in `F(w)`, `E` finite-dimensional:
  `theoreme3` (`algebreBooleS`, `DistinguesS`), through the transfer to the affine Théorème 2
  on the closed cone `K̄ = closure (insert O F(w))`: `estConjugueS_iff_affine`,
  `estDistingueS_iff_affine`, `not_contientDroite_closure`; « sup l'enveloppe convexe »:
  `isLeast_linearSubvariety_sup`.
* `bzcor:c3s2t3c_algebre_parties_projective` — `benzecri1960_ch3.tex:579` (Corollaire,
  l.579–590), NOT marked: FALSE as printed
  (`BooleProjectifInstance.not_corollaire_algebre_parties`, the open quarter: infinitely many
  distinguished subvarieties); proved under the hypotheses of `theoreme3`:
  `corollaire_algebre_parties_projective` (`EstSimpleS`, `simplesS`,
  `isLeast_linearSubvariety_sSup`, `isLeast_iff_eq_sSup`).

Instances: the open `n`-simplex of `S(n)` satisfies every hypothesis of `theoreme3`
(`BooleProjectifInstance.simplexO_hyps`) and has `n + 1` simple distinguished subvarieties
(`simplexO_simplesS_ncard`, « `(n+1)` au cas du `n`-simplexe ouvert »); the open round cap of
`S(2)` has exactly one, `S(2)` (`capS_simplesS`, « `1` correspond au cas où il n'existe pas de
décomposition non triviale »). Counterexamples: the open quarter `quartS` (Déf. 6's claim, the
Corollary) and the half-open quarter `w2` (Théorème 3).

> **Définition 5.** Soient $w$ un convexe de $S(E)$, de noyau vide, $\{v_i\}$ une famille
> finie de convexes de $S(E)$; $w$ est dit *somme* des convexes $v_i$ si les $F(v_i)$ sont
> convexes et si $F(w)$ est somme des convexes $F(v_i)$.
>
> En particulier, soient $w$, $v_1$, $v_2$ trois convexes non vides de $S(E)$. Soit $l_1$,
> $l_2$ les supports de $v_1$, $v_2$, c'est-à-dire les plus petites variétés linéaires
> contenant $v_1$ et $v_2$ respectivement. $w$ est somme de $v_1$ et $v_2$ si $l_1\cap l_2$ est
> vide et si $w$ est réunion de l'ensemble de tous les segments ouverts joignant un point de
> $v_1$ à un point de $v_2$. On convient que $w$ est somme de $w$ et du convexe vide.
>
> **Définition 6.** Soit $w$ un convexe de $S(E)$ dont le support est $S(E)$ et le noyau
> $\emptyset$. Un sous-espace $l$ est *distingué relativement à $w$* s'il existe un sous-espace
> $l'$ tel que $w$ soit somme de deux convexes $v$ et $v'$ de supports $l$ et $l'$.
>
> La donnée du sous-espace distingué $l$ détermine complètement le sous-espace distingué $l'$;
> $l$ et $l'$ sont dits coujugués relativement à $w$.
>
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
>
> Pour justifier la définition 6 et démontrer le théorème 3 et son corollaire, il suffit de se
> reporter aux énoncés correspondants formulés dans le cas affin.

## The proof formalized

*Déf. 5.* `F(⋃ )m₁, m₂() = (F(v₁) + F(v₂)) − O` (`F_joint`). For `w` convex and `v₂ ≠ ∅`, a
pair `m, −m` in `v₁` would put the representative `N` of a point of `v₂` in `F(w)`, hence in
`F(v₁) + F(v₂)`, against `l₁ ∩ l₂ = ∅`; so `F(v₁)` is convex (`convex_F_of_joint`). Disjoint
spans give unique decompositions, and conversely for convex cones (`span_inf_eq_bot_of_unique`).

*Déf. 6 on the cone* (`estConjugueS_iff`): `(L, L′)` is conjugate iff it is `(span F(w), 0)`,
`(0, span F(w))` (the convention), or `F(w) = A + A′` with `A`, `A′` nonempty convex cones not
containing `O`, spanning `L`, `L′` with `L ∩ L′ = 0` (`ConeDec`).

*Uniqueness* (`le_of_coneDec`): with `F(w) = A + A′ = B + B″`, `P` the projection on `L` along
`L″`, `a + P b′ − P b″ ∈ A` for `a ∈ A`, `b′, b″ ∈ A′`; taking `b′ = s a′` gives `a + t P a′ ∈ A`
for every real `t`, so `a + a′ + t P a′ ∈ F(w)`: a line, unless `P a′ = 0`, i.e. `L′ ≤ L″`.

*The transfer* (`estConjugueS_iff_affine`, the paper's « se reporter au cas affin »), for `w`
open in finite dimension with no line in `F(w)`: `(L, L′)` is conjugate iff it is a
supplementary conjugate pair (Déf. 3/4) of the closed cone `K̄`. (⇒) `A ⊆ K̄` (`a + s a′ → a`), so
`P_L` maps `K̄` into `K̄`. (⇐) `A = P_L F(w)`; `O ∉ A`, else `F(w)` open gives `±ε l ∈ K̄`, a line
(`projection_ne_zero`); `A + A′ ⊆ F(w)`: `(c, c′) ↦ P_L c + P_{L′} c′` is an open map with image
in `K̄`, hence in `interior K̄ = interior K` (`Convex.interior_closure_eq_interior_of_nonempty_interior`).
`K̄` has no line (`not_contientDroite_closure`: a line of `K̄` has its direction `±v` in `K̄`, so
`c + s v ∈ interior K̄` for `c ∈ F(w)`). Théorème 2 and its Corollary (`Benzecri.theoreme2`'s
construction, `corollaire_algebre_parties`) then apply to `K̄`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 5: `w` convexe de noyau vide, `vᵢ` convexes | ✓ carried where used: `IsConvexPart w`, `IsConvexPart vᵢ` (the noyau is not needed for « En particulier ») |
| Déf. 5: « trois convexes non vides » | ✓ carried: `v₁.Nonempty`, `v₂.Nonempty` |
| Déf. 5: supports « plus petites variétés linéaires contenant » | ✓ `supportK` (least: `supportK_subset`) |
| Déf. 6: `w` convexe, support `S(E)`, noyau `∅` | ✓ carried: `IsConvexPart w`, `supportK w = univ` (noyau: used only through the added hypothesis) |
| Déf. 6, « détermine complètement `l′` » | ✗ false as printed (`not_conjugue_unique`); ⚠ strengthened: `¬ ContientDroite (F w)` added (`conjugue_unique`) |
| Th. 3: `w` convexe, support `S(E)`, noyau vide | ✓ carried |
| Th. 3: `E` any real vector space | ⚠ strengthened: `E` finite-dimensional normed (the topology of « ouvert ») |
| Th. 3 | ✗ false as printed (`not_theoreme3`); ⚠ strengthened: `w` open, `¬ ContientDroite (F w)` added |
| Th. 3: (1) `S(E)`, (0) `∅`, complément la conjuguée, inf `∩`, sup l'enveloppe convexe | ✓ all stated in `theoreme3` (the complement is THE conjugate: exists and unique) |
| Cor.: `dim E = n + 1` | ✓ `Module.finrank ℝ E = n + 1` |
| Cor. | ✗ false as printed (`not_corollaire_algebre_parties`); ⚠ strengthened: the hypotheses of `theoreme3` |
| Cor.: cardinal entre `1` et `n + 1`; instances `1`, `n + 1` | ✓ `corollaire_algebre_parties_projective`; `capS_simplesS`, `simplexO_simplesS_ncard` |
| « il suffit de se reporter au cas affin » (cited) | ✓ formalized: the transfer `estConjugueS_iff_affine` to Théorème 2 on `K̄` |

## SCOPE (disclosed)

* **Readings.** « sous-espace `l` » (Déf. 6) and « sous-variétés » (Th. 3) are the linear
  subvarieties `s(L − O)`, indexed by the subspace `L` (`linearSubvariety_injective`); « `w` soit
  somme de deux convexes `v` et `v′` » is Déf. 5's two-summand form WITH its convention (else
  `∅` and `S(E)`, Th. 3's (0) and (1), are not distinguished); « sup l'enveloppe convexe » is the
  least convex part of `S(E)` (Chapter 1's convex parts, linear subvarieties included)
  containing `l ∪ d`; « simples » are minimal among the distinguished `≠ ∅`; « famille » a set.
* **Déf. 6's claim is false as printed**: relative to the open quarter `{y > 0, z > 0}` of
  `S(2)` the great circle `z = 0` is distinguished with conjugates `{±e₃}` and `{±(e₁ + e₃)}`.
  The failure is a line in `F(w)` (`x ↦ (x, 1, 1)`), which noyau `∅` does not exclude. Under
  `¬ ContientDroite (F w)` the claim is proved for every real `E` (`conjugue_unique`).
* **Théorème 3 is false as printed, and with `F(w)` line-free**: relative to
  `w₂ = {x ≥ 0, y > 0, z > 0}` the circles `z = 0` (conjugate `{±e₃}`) and `y = 0` (conjugate
  `{±e₂}`) are distinguished, and their intersection `{±e₁}` is not; `w₂` is not open. A
  refutation of Th. 3 for an open `w` is NOT formalized (the open quarter refutes Déf. 6's
  uniqueness claim and the Corollary, not Th. 3 in Lean). The corrected statement adds `w` open
  and `F(w)` line-free (`theoreme3`); `w₂` shows that line-freeness alone does not suffice, and
  whether openness alone suffices is not settled here. It is proved for `E` finite-dimensional,
  where « open » has its meaning; Props. 4–5, which use Th. 3, are about open `w` of `S(n)`.
* **The Corollary is false as printed**: relative to the open quarter the pairs `{±(t e₁ + e₂)}`,
  `t ∈ ℝ`, are all distinguished. Under the hypotheses of `theoreme3` it is proved; the bound
  `1 ≤` holds since `n + 1 ≥ 1` (OQ-165 (b)'s `n = 0` failure of the affine Corollary does not
  recur).
* **The transfer is through the closed cone `K̄`, not through `insert O F(w)`**: the open
  simplex's axes are distinguished but not affine-distinguished for `insert O F(w)`
  (`simplexO_kPrime_not_estDistingue`), and `insert O F(w)` may contain lines when the noyau is
  empty (the open quarter).
* OQ-163 / OQ-165 (a) do not arise: Déf. 6's conjugates are supplementary by construction and,
  under the corrected hypotheses, unique (`conjugue_unique`); Théorème 3's complement is that
  conjugate. The marks of Th. 3 and the Corollary wait on the author's choice of the corrected
  statement of record: `w` open and line-free (proved here), or another one, e.g. `w` closed
  (Benzécri's « corps convexes »), neither proved nor refuted here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function Filter Topology
open scoped Pointwise

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 5 -/

/-- The union of all the open segments joining a point of `v₁` to a point of `v₂`. -/
def joint (v₁ v₂ : Set (Sphere E)) : Set (Sphere E) := ⋃ m₁ ∈ v₁, ⋃ m₂ ∈ v₂, openSeg m₁ m₂

/-- **Déf. 5** (general form): `w` is the *sum* of the finite family `v i` if the `F(v i)` are
convex and `F(w)` is the sum (Déf. 1, `IsSommeConvexes`) of the convex sets `F(v i)`. (The
standing hypotheses on `w`, convex with empty noyau, are carried by the theorems.) -/
def EstSommeS {I : Type*} [Fintype I] (w : Set (Sphere E)) (v : I → Set (Sphere E)) : Prop :=
  (∀ i, Convex ℝ (F (v i))) ∧ IsSommeConvexes (F w) (fun i => F (v i))

/-- **Déf. 5** (two summands, « En particulier »), with the convention « `w` est somme de `w` et
du convexe vide » (in either order): `l₁ ∩ l₂ = ∅` for the supports `lᵢ` of the nonempty `vᵢ`,
and `w` is the union of the open segments joining a point of `v₁` to a point of `v₂`. -/
def EstSomme2 (w v₁ v₂ : Set (Sphere E)) : Prop :=
  (v₁ = w ∧ v₂ = ∅) ∨ (v₁ = ∅ ∧ v₂ = w) ∨
    (v₁.Nonempty ∧ v₂.Nonempty ∧ supportK v₁ ∩ supportK v₂ = ∅ ∧ w = joint v₁ v₂)

/-! ### Déf. 6 -/

/-- **Déf. 6**: `l = s(L − O)` and `l′ = s(L′ − O)` are *conjugate* relative to `w`: `w` is the
sum (Déf. 5, two summands) of two convex parts `v`, `v′` of supports `l`, `l′`. -/
def EstConjugueS (w : Set (Sphere E)) (L L' : Submodule ℝ E) : Prop :=
  ∃ v v' : Set (Sphere E), IsConvexPart v ∧ IsConvexPart v' ∧
    supportK v = linearSubvariety L ∧ supportK v' = linearSubvariety L' ∧ EstSomme2 w v v'

/-- **Déf. 6**: the linear subvariety `s(L − O)` is *distinguished* relative to `w`. -/
def EstDistingueS (w : Set (Sphere E)) (L : Submodule ℝ E) : Prop :=
  ∃ L' : Submodule ℝ E, EstConjugueS w L L'

/-! ### Elementary lemmas -/

theorem add_mem_of_cone {A : Set E} (hA : Convex ℝ A) (hpos : IsPosCone A) {x y : E}
    (hx : x ∈ A) (hy : y ∈ A) : x + y ∈ A := by
  have h := hA hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have := hpos 2 (by norm_num) _ h
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at this

theorem convex_insert_zero_of_cone {A : Set E} (hA : Convex ℝ A) (hpos : IsPosCone A) :
    Convex ℝ (insert (0 : E) A) := by
  intro x hx y hy a b ha hb hab
  rcases mem_insert_iff.1 hx with rfl | hx <;> rcases mem_insert_iff.1 hy with rfl | hy
  · simp
  · rcases hb.lt_or_eq with hb | rfl
    · exact mem_insert_of_mem _ (by simpa using hpos b hb _ hy)
    · simp
  · rcases ha.lt_or_eq with ha | rfl
    · exact mem_insert_of_mem _ (by simpa using hpos a ha _ hx)
    · simp
  · exact mem_insert_of_mem _ (hA hx hy ha hb hab)

theorem F_ofCone_of_zero_notMem {A : Set E} (hpos : IsPosCone A) (h0 : (0 : E) ∉ A) :
    F (ofCone A) = A := by
  rw [F_ofCone hpos, sdiff_singleton_eq_self h0]

theorem isConvexPart_ofCone_of_cone {A : Set E} (hA : Convex ℝ A) (hpos : IsPosCone A) :
    IsConvexPart (ofCone A) := by
  unfold IsConvexPart
  rw [F_ofCone hpos, insert_sdiff_singleton]
  exact convex_insert_zero_of_cone hA hpos

theorem supportK_ofCone {A : Set E} (hpos : IsPosCone A) (h0 : (0 : E) ∉ A) :
    supportK (ofCone A) = linearSubvariety (Submodule.span ℝ A) := by
  rw [supportK, F_ofCone_of_zero_notMem hpos h0]

theorem supportK_empty : supportK (∅ : Set (Sphere E)) = linearSubvariety ⊥ := by
  rw [supportK, F_empty, Submodule.span_empty]

theorem linearSubvariety_inter (L M : Submodule ℝ E) :
    linearSubvariety L ∩ linearSubvariety M = linearSubvariety (L ⊓ M) := by
  apply F_injective
  rw [F_inter, F_linearSubvariety, F_linearSubvariety, F_linearSubvariety]
  ext x
  simp only [mem_inter_iff, Set.mem_sdiff, SetLike.mem_coe, Submodule.mem_inf]
  tauto

theorem linearSubvariety_subset_iff {L M : Submodule ℝ E} :
    linearSubvariety L ⊆ linearSubvariety M ↔ L ≤ M := by
  refine ⟨fun h => ?_, fun h => ofCone_subset_ofCone (SetLike.coe_subset_coe.2 h)⟩
  rw [← span_F_linearSubvariety L, ← span_F_linearSubvariety M]
  exact Submodule.span_mono (F_mono h)

theorem linearSubvariety_eq_empty_iff {L : Submodule ℝ E} :
    linearSubvariety L = ∅ ↔ L = ⊥ := by
  rw [← linearSubvariety_bot, linearSubvariety_injective.eq_iff]

theorem linearSubvariety_top_eq : linearSubvariety (⊤ : Submodule ℝ E) = univ := by
  apply F_injective
  rw [F_linearSubvariety, F_univ]
  ext v; simp

theorem nonempty_F {v : Set (Sphere E)} (hv : v.Nonempty) : (F v).Nonempty := by
  obtain ⟨x, hx⟩ := hv
  induction x using ind with
  | h X hX => exact ⟨X, hX, hx⟩

/-- The projection on `L` along `L'` of `x + y`, `x ∈ L`, `y ∈ L'`, is `x`. -/
theorem projection_add_of_mem {L L' : Submodule ℝ E} (h : IsCompl L L') {x y : E} (hx : x ∈ L)
    (hy : y ∈ L') : L.projection L' h (x + y) = x := by
  rw [map_add, Submodule.projection_apply_of_mem_left h hx,
    Submodule.projection_apply_of_mem_right h hy, add_zero]

/-- `0 ∉ A + A'` for `A ⊆ L`, `A' ⊆ L'`, `L ∩ L' = 0`, `0 ∉ A`. -/
theorem zero_notMem_add {A A' : Set E} {L L' : Submodule ℝ E} (hA : A ⊆ L) (hA' : A' ⊆ L')
    (hLL : L ⊓ L' = ⊥) (h0 : (0 : E) ∉ A) : (0 : E) ∉ A + A' := by
  rintro ⟨a, ha, a', ha', e⟩
  have hmem : a ∈ L ⊓ L' := by
    refine Submodule.mem_inf.2 ⟨hA ha, ?_⟩
    rw [eq_neg_of_add_eq_zero_left e]
    exact L'.neg_mem (hA' ha')
  rw [hLL, Submodule.mem_bot] at hmem
  exact h0 (hmem ▸ ha)

/-- `F` of the union of the open segments: `F(⋃ )m₁, m₂() = (F(v₁) + F(v₂)) − {O}`. -/
theorem F_joint (v₁ v₂ : Set (Sphere E)) : F (joint v₁ v₂) = (F v₁ + F v₂) \ {0} := by
  ext v
  constructor
  · rintro ⟨hv, hmem⟩
    simp only [joint, mem_iUnion] at hmem
    obtain ⟨m₁, hm₁, m₂, hm₂, h⟩ := hmem
    induction m₁ using ind with
    | h M₁ hM₁ =>
    induction m₂ using ind with
    | h M₂ hM₂ =>
    rw [openSeg_mk, openSegOf, mem_ofCone] at h
    obtain ⟨u, hu, ⟨a, b, ha, hb, _, rfl⟩, e⟩ := h
    obtain ⟨c, hc, rfl⟩ := (mk_eq_mk_iff_exists_pos hu hv).1 e
    refine ⟨⟨(c * a) • M₁, smul_mem_F ⟨hM₁, hm₁⟩ (mul_pos hc ha), (c * b) • M₂,
      smul_mem_F ⟨hM₂, hm₂⟩ (mul_pos hc hb), ?_⟩, hv⟩
    simp only [smul_add, smul_smul]
  · rintro ⟨⟨x, hx, y, hy, rfl⟩, hv⟩
    have hv' : x + y ≠ 0 := hv
    refine ⟨hv', ?_⟩
    simp only [joint, mem_iUnion]
    refine ⟨mk x hx.1, hx.2, mk y hy.1, hy.2, ?_⟩
    rw [openSeg_mk, openSegOf, mem_ofCone]
    have hne : (1 / 2 : ℝ) • (x + y) ≠ 0 := smul_ne_zero (by norm_num) hv'
    refine ⟨(1 / 2 : ℝ) • (x + y), hne, ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
      by rw [smul_add]⟩, mk_smul hv' (by norm_num) hne⟩

theorem supportK_inter_eq_empty_iff {v₁ v₂ : Set (Sphere E)} :
    supportK v₁ ∩ supportK v₂ = ∅ ↔
      Submodule.span ℝ (F v₁) ⊓ Submodule.span ℝ (F v₂) = ⊥ := by
  rw [supportK, supportK, linearSubvariety_inter, linearSubvariety_eq_empty_iff]

/-- With `v₂ ≠ ∅` and `F(w) = (F(v₁) + F(v₂)) − O` over disjoint supports, `w` convex forces
`F(v₁)` convex (`v₁` has no pair of diametrically opposite points). -/
theorem convex_F_of_joint {w v₁ v₂ : Set (Sphere E)} (hw : IsConvexPart w)
    (hv₁ : IsConvexPart v₁) (hne : (F v₂).Nonempty)
    (hdisj : Submodule.span ℝ (F v₁) ⊓ Submodule.span ℝ (F v₂) = ⊥)
    (hF : F w = (F v₁ + F v₂) \ {0}) : Convex ℝ (F v₁) := by
  refine isStrictConvexPart_iff_convex_F.1 ⟨hv₁, fun m hm hm' => ?_⟩
  induction m using ind with
  | h M hM =>
  rw [neg_mk] at hm'
  have hMF : M ∈ F v₁ := ⟨hM, hm⟩
  have hMF' : -M ∈ F v₁ := ⟨neg_ne_zero.2 hM, hm'⟩
  obtain ⟨N, hN⟩ := hne
  have h0 : (0 : E) ∉ F v₁ + F v₂ :=
    zero_notMem_add (fun _ hx => Submodule.subset_span hx) (fun _ hx => Submodule.subset_span hx)
      hdisj (zero_notMem_F _)
  have h1 : M + N ∈ insert (0 : E) (F w) := by
    refine mem_insert_of_mem _ ?_
    rw [hF]
    exact ⟨⟨M, hMF, N, hN, rfl⟩, fun h => h0 (h ▸ ⟨M, hMF, N, hN, rfl⟩)⟩
  have h2 : -M + N ∈ insert (0 : E) (F w) := by
    refine mem_insert_of_mem _ ?_
    rw [hF]
    exact ⟨⟨-M, hMF', N, hN, rfl⟩, fun h => h0 (h ▸ ⟨-M, hMF', N, hN, rfl⟩)⟩
  have h3 := hw h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have e : (1 / 2 : ℝ) • (M + N) + (1 / 2 : ℝ) • (-M + N) = N := by module
  rw [e] at h3
  have hN0 : N ≠ 0 := hN.1
  have hNw : N ∈ F w := (mem_insert_iff.1 h3).resolve_left hN0
  rw [hF] at hNw
  obtain ⟨⟨x, hx, y, hy, hxy⟩, -⟩ := hNw
  have hmem : x ∈ Submodule.span ℝ (F v₁) ⊓ Submodule.span ℝ (F v₂) := by
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span hx, ?_⟩
    rw [show x = N - y by rw [← hxy]; simp]
    exact Submodule.sub_mem _ (Submodule.subset_span hN) (Submodule.subset_span hy)
  rw [hdisj, Submodule.mem_bot] at hmem
  exact zero_notMem_F _ (hmem ▸ hx)

/-- For `z` in `insert O A`, `p ∈ A`, `r > 0`: `r z + p ∈ A`. -/
theorem smul_add_mem_of_cone {A : Set E} (hA : Convex ℝ A) (hpos : IsPosCone A) {z p : E}
    (hz : z ∈ insert (0 : E) A) (hp : p ∈ A) {r : ℝ} (hr : 0 < r) : r • z + p ∈ A := by
  rcases mem_insert_iff.1 hz with rfl | hz
  · simpa using hp
  · exact add_mem_of_cone hA hpos (hpos r hr _ hz) hp

/-- For nonempty convex cones, uniqueness of the decomposition `a + b` forces the spans to meet
at `0`. -/
theorem span_inf_eq_bot_of_unique {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hpA : IsPosCone A) (hpB : IsPosCone B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hu : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, a + b = a' + b' → a = a') :
    Submodule.span ℝ A ⊓ Submodule.span ℝ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Submodule.mem_inf.1 hx
  rw [← Submodule.span_insert_zero] at hxA hxB
  obtain ⟨r, hr, a₁, ha₁, a₂, ha₂, rfl⟩ :=
    exists_smul_sub_of_mem_span (convex_insert_zero_of_cone hA hpA) (mem_insert _ _) hxA
  obtain ⟨s, hs, b₁, hb₁, b₂, hb₂, e⟩ :=
    exists_smul_sub_of_mem_span (convex_insert_zero_of_cone hB hpB) (mem_insert _ _) hxB
  obtain ⟨p, hp⟩ := hneA
  obtain ⟨q, hq⟩ := hneB
  have := hu _ (smul_add_mem_of_cone hA hpA ha₁ hp hr) _ (smul_add_mem_of_cone hA hpA ha₂ hp hr)
    _ (smul_add_mem_of_cone hB hpB hb₂ hq hs) _ (smul_add_mem_of_cone hB hpB hb₁ hq hs) (by
      have e' : r • a₁ - r • a₂ = s • b₁ - s • b₂ := by rw [← smul_sub, ← smul_sub, e]
      rw [← sub_eq_zero] at e' ⊢
      rw [← e']
      abel)
  rw [Submodule.mem_bot, smul_sub, sub_eq_zero]
  exact add_right_cancel this

omit [Module ℝ E] in
/-- Déf. 1 for two summands. -/
theorem bijOn_sum_two_iff {W : Set E} {V : Fin 2 → Set E} :
    Set.BijOn (fun x : Fin 2 → E => ∑ i, x i) (Set.univ.pi V) W ↔
      W = V 0 + V 1 ∧ ∀ a ∈ V 0, ∀ a' ∈ V 0, ∀ b ∈ V 1, ∀ b' ∈ V 1, a + b = a' + b' →
        a = a' ∧ b = b' := by
  constructor
  · intro h
    refine ⟨?_, fun a ha a' ha' b hb b' hb' e => ?_⟩
    · rw [← h.image_eq]
      ext z
      simp only [Set.mem_image, Set.mem_add, Fin.sum_univ_two]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x 0, hx 0 trivial, x 1, hx 1 trivial, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        refine ⟨![a, b], fun i _ => ?_, by simp⟩
        fin_cases i
        · simpa using ha
        · simpa using hb
    · have hm : ∀ {a b : E}, a ∈ V 0 → b ∈ V 1 → ![a, b] ∈ Set.univ.pi V := by
        intro a b ha hb i _
        fin_cases i
        · simpa using ha
        · simpa using hb
      have := h.injOn (hm ha hb) (hm ha' hb') (by simpa [Fin.sum_univ_two] using e)
      exact ⟨by simpa using congrFun this 0, by simpa using congrFun this 1⟩
  · rintro ⟨hW, hu⟩
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
    · show ∑ i, x i ∈ W
      rw [hW, Fin.sum_univ_two]
      exact ⟨x 0, hx 0 trivial, x 1, hx 1 trivial, rfl⟩
    · simp only [Fin.sum_univ_two] at hxy
      obtain ⟨e0, e1⟩ := hu _ (hx 0 trivial) _ (hy 0 trivial) _ (hx 1 trivial) _ (hy 1 trivial) hxy
      ext i
      fin_cases i
      · exact e0
      · exact e1
    · rw [hW] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      refine ⟨![a, b], fun i _ => ?_, by simp⟩
      fin_cases i
      · simpa using ha
      · simpa using hb

/-- Disjoint spans give unique decompositions. -/
theorem unique_of_span_inf_eq_bot {A B : Set E}
    (h : Submodule.span ℝ A ⊓ Submodule.span ℝ B = ⊥) {a a' b b' : E} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (e : a + b = a' + b') : a = a' ∧ b = b' := by
  have hmem : a - a' ∈ Submodule.span ℝ A ⊓ Submodule.span ℝ B := by
    refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (Submodule.subset_span ha)
      (Submodule.subset_span ha'), ?_⟩
    rw [show a - a' = b' - b by rw [sub_eq_sub_iff_add_eq_add, e, add_comm]]
    exact Submodule.sub_mem _ (Submodule.subset_span hb') (Submodule.subset_span hb)
  rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
  subst hmem
  exact ⟨rfl, add_left_cancel e⟩

/-- **Déf. 5, « En particulier »**: for nonempty convex parts `v₁`, `v₂` and `w` convex, the
two-summand form (`l₁ ∩ l₂ = ∅` and `w` the union of the open segments) is the general form
of Déf. 5 for the family `{v₁, v₂}`. -/
theorem estSomme2_iff_estSommeS {w v₁ v₂ : Set (Sphere E)} (hw : IsConvexPart w)
    (hv₁ : IsConvexPart v₁) (hv₂ : IsConvexPart v₂) (h₁ : v₁.Nonempty) (h₂ : v₂.Nonempty) :
    EstSomme2 w v₁ v₂ ↔ EstSommeS w ![v₁, v₂] := by
  have hV : (fun i => F (![v₁, v₂] i)) = ![F v₁, F v₂] := by
    ext i : 1; fin_cases i <;> rfl
  unfold EstSommeS
  rw [isSommeConvexes_iff_bijOn, hV, bijOn_sum_two_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · rintro (⟨-, rfl⟩ | ⟨rfl, -⟩ | ⟨-, -, hdisj, hj⟩)
    · exact absurd h₂ Set.not_nonempty_empty
    · exact absurd h₁ Set.not_nonempty_empty
    rw [supportK_inter_eq_empty_iff] at hdisj
    have hF : F w = (F v₁ + F v₂) \ {0} := by rw [hj, F_joint]
    have hc₁ := convex_F_of_joint hw hv₁ (nonempty_F h₂) hdisj hF
    have hc₂ := convex_F_of_joint hw hv₂ (nonempty_F h₁) (by rwa [inf_comm])
      (by rw [hF, add_comm])
    have h0 : (0 : E) ∉ F v₁ + F v₂ :=
      zero_notMem_add (fun _ hx => Submodule.subset_span hx)
        (fun _ hx => Submodule.subset_span hx) hdisj (zero_notMem_F _)
    refine ⟨fun i => ?_, fun i => ?_, ?_, fun a ha a' ha' b hb b' hb' e =>
      unique_of_span_inf_eq_bot hdisj ha ha' hb hb' e⟩
    · fin_cases i
      · exact hc₁
      · exact hc₂
    · fin_cases i
      · exact hc₁
      · exact hc₂
    · rw [hF, sdiff_singleton_eq_self h0]
  · rintro ⟨hc, -, hW, hu⟩
    have hc₁ : Convex ℝ (F v₁) := by simpa using hc 0
    have hc₂ : Convex ℝ (F v₂) := by simpa using hc 1
    have hdisj := span_inf_eq_bot_of_unique hc₁ hc₂ (isPosCone_F _) (isPosCone_F _)
      (nonempty_F h₁) (nonempty_F h₂) fun a ha a' ha' b hb b' hb' e =>
        (hu a ha a' ha' b hb b' hb' e).1
    refine Or.inr (Or.inr ⟨h₁, h₂, supportK_inter_eq_empty_iff.2 hdisj, ?_⟩)
    apply F_injective
    rw [F_joint, ← hW, sdiff_singleton_eq_self (zero_notMem_F _)]

/-- Déf. 5's general form does not contain the convention: `w` is the sum of `w` and of the
empty convex in the sense of Déf. 1 only if `w = ∅` (Déf. 1's sum with an empty summand is
empty); « On convient que » is an extension of the definition. -/
theorem eq_empty_of_estSommeS_vide {w : Set (Sphere E)} (h : EstSommeS w ![w, ∅]) : w = ∅ := by
  obtain ⟨-, -, -, hbij, -⟩ := h
  apply F_injective
  rw [F_empty, ← hbij.image_eq]
  refine eq_empty_of_forall_notMem fun x ⟨y, hy, _⟩ => ?_
  have := hy 1 trivial
  simp at this


/-! ### Déf. 6 on the cone `F(w)` -/

/-- The cone form of a nontrivial conjugate pair `(L, L')`: `F(w) = A + A'` with `A`, `A'`
nonempty convex cones not containing `O`, spanning `L` and `L'`, and `L ∩ L' = 0`. -/
structure ConeDec (C : Set E) (L L' : Submodule ℝ E) (A A' : Set E) : Prop where
  convex : Convex ℝ A
  convex' : Convex ℝ A'
  pos : IsPosCone A
  pos' : IsPosCone A'
  zero : (0 : E) ∉ A
  zero' : (0 : E) ∉ A'
  ne : A.Nonempty
  ne' : A'.Nonempty
  span : Submodule.span ℝ A = L
  span' : Submodule.span ℝ A' = L'
  disj : L ⊓ L' = ⊥
  sum : C = A + A'

theorem ConeDec.subset {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') : A ⊆ L := fun _ hx => h.span ▸ Submodule.subset_span hx

theorem ConeDec.subset' {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') : A' ⊆ L' := fun _ hx => h.span' ▸ Submodule.subset_span hx

theorem ConeDec.ne_bot {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') : L ≠ ⊥ := by
  intro hL
  obtain ⟨a, ha⟩ := h.ne
  have := h.subset ha
  rw [hL, SetLike.mem_coe, Submodule.mem_bot] at this
  exact h.zero (this ▸ ha)

theorem ConeDec.ne_bot' {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') : L' ≠ ⊥ := by
  intro hL
  obtain ⟨a, ha⟩ := h.ne'
  have := h.subset' ha
  rw [hL, SetLike.mem_coe, Submodule.mem_bot] at this
  exact h.zero' (this ▸ ha)

/-- With `span F(w) = E`, the subspaces of a cone decomposition are supplementary. -/
theorem ConeDec.isCompl {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') (hC : Submodule.span ℝ C = ⊤) : IsCompl L L' := by
  refine ⟨disjoint_iff.2 h.disj, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  rw [← hC, Submodule.span_le, h.sum]
  rintro _ ⟨a, ha, a', ha', rfl⟩
  exact Submodule.add_mem_sup (h.subset ha) (h.subset' ha')

/-- The projections of a point of `C = A + A'` lie in `A` and `A'`. -/
theorem ConeDec.projection_mem {C : Set E} {L L' : Submodule ℝ E} {A A' : Set E}
    (h : ConeDec C L L' A A') (hc : IsCompl L L') {x : E} (hx : x ∈ C) :
    L.projection L' hc x ∈ A ∧ L'.projection L hc.symm x ∈ A' := by
  rw [h.sum] at hx
  obtain ⟨a, ha, a', ha', rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [projection_add_of_mem hc (h.subset ha) (h.subset' ha')]; exact ha
  · show L'.projection L hc.symm (a + a') ∈ A'
    rw [add_comm, projection_add_of_mem hc.symm (h.subset' ha') (h.subset ha)]; exact ha'

/-- **Déf. 6 on the cone**: `(L, L')` is a conjugate pair relative to the convex `w` iff it is
one of the two trivial pairs of the convention « `w` est somme de `w` et du convexe vide », or
`F(w)` is the sum `A + A'` of a `ConeDec`. -/
theorem estConjugueS_iff {w : Set (Sphere E)} (hw : IsConvexPart w) {L L' : Submodule ℝ E} :
    EstConjugueS w L L' ↔ (L = Submodule.span ℝ (F w) ∧ L' = ⊥) ∨
      (L = ⊥ ∧ L' = Submodule.span ℝ (F w)) ∨ ∃ A A' : Set E, ConeDec (F w) L L' A A' := by
  constructor
  · rintro ⟨v, v', hv, hv', hs, hs', hsum⟩
    rcases hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h₁, h₂, hdisj, hj⟩
    · rw [supportK_empty] at hs'
      exact Or.inl ⟨(linearSubvariety_injective hs).symm, (linearSubvariety_injective hs').symm⟩
    · rw [supportK_empty] at hs
      exact Or.inr (Or.inl ⟨(linearSubvariety_injective hs).symm,
        (linearSubvariety_injective hs').symm⟩)
    · have hdisj' := supportK_inter_eq_empty_iff.1 hdisj
      have hF : F w = (F v + F v') \ {0} := by rw [hj, F_joint]
      have hS := (estSomme2_iff_estSommeS hw hv hv' h₁ h₂).1
        (Or.inr (Or.inr ⟨h₁, h₂, hdisj, hj⟩))
      have hc₁ : Convex ℝ (F v) := by simpa using hS.1 0
      have hc₂ : Convex ℝ (F v') := by simpa using hS.1 1
      have hL : Submodule.span ℝ (F v) = L := linearSubvariety_injective hs
      have hL' : Submodule.span ℝ (F v') = L' := linearSubvariety_injective hs'
      have h0 : (0 : E) ∉ F v + F v' :=
        zero_notMem_add (fun _ hx => Submodule.subset_span hx)
          (fun _ hx => Submodule.subset_span hx) hdisj' (zero_notMem_F _)
      refine Or.inr (Or.inr ⟨F v, F v', hc₁, hc₂, isPosCone_F _, isPosCone_F _, zero_notMem_F _,
        zero_notMem_F _, nonempty_F h₁, nonempty_F h₂, hL, hL', hL ▸ hL' ▸ hdisj', ?_⟩)
      rw [hF, sdiff_singleton_eq_self h0]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨A, A', h⟩)
    · refine ⟨w, ∅, hw, ?_, rfl, supportK_empty, Or.inl ⟨rfl, rfl⟩⟩
      unfold IsConvexPart; rw [F_empty, insert_empty_eq]; exact convex_singleton 0
    · refine ⟨∅, w, ?_, hw, supportK_empty, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      unfold IsConvexPart; rw [F_empty, insert_empty_eq]; exact convex_singleton 0
    · refine ⟨ofCone A, ofCone A', isConvexPart_ofCone_of_cone h.convex h.pos,
        isConvexPart_ofCone_of_cone h.convex' h.pos', by rw [supportK_ofCone h.pos h.zero, h.span],
        by rw [supportK_ofCone h.pos' h.zero', h.span'], Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)⟩
      · obtain ⟨a, ha⟩ := h.ne
        exact ⟨_, mk_mem_ofCone (fun e => h.zero (e ▸ ha)) ha⟩
      · obtain ⟨a, ha⟩ := h.ne'
        exact ⟨_, mk_mem_ofCone (fun e => h.zero' (e ▸ ha)) ha⟩
      · rw [supportK_ofCone h.pos h.zero, supportK_ofCone h.pos' h.zero', h.span, h.span',
          linearSubvariety_inter, h.disj, linearSubvariety_bot]
      · apply F_injective
        rw [F_joint, F_ofCone_of_zero_notMem h.pos h.zero, F_ofCone_of_zero_notMem h.pos' h.zero',
          ← h.sum, sdiff_singleton_eq_self (zero_notMem_F _)]

theorem span_F_eq_top_of_supportK {w : Set (Sphere E)} (hsupp : supportK w = univ) :
    Submodule.span ℝ (F w) = ⊤ :=
  linearSubvariety_injective (hsupp.trans linearSubvariety_top_eq.symm)

/-- The heart of the uniqueness: for two nontrivial conjugates `L'`, `L''` of `L`, `L' ≤ L''`
unless `F(w)` contains a line. -/
theorem le_of_coneDec {C : Set E} (hC : Submodule.span ℝ C = ⊤) (hd : ¬ ContientDroite C)
    {L L' L'' : Submodule ℝ E} {A A' B B'' : Set E} (h₁ : ConeDec C L L' A A')
    (h₂ : ConeDec C L L'' B B'') : L' ≤ L'' := by
  have hc₁ := h₁.isCompl hC
  have hc₂ := h₂.isCompl hC
  set P := L.projection L'' hc₂
  set Q := L.projection L' hc₁
  obtain ⟨a, ha⟩ := h₁.ne
  -- for `b', b'' ∈ A'`, `a + P b' - P b'' ∈ A`
  have key : ∀ b' ∈ A', ∀ b'' ∈ A', a + P b' - P b'' ∈ A := by
    intro b' hb' b'' hb''
    have hc1 : a + b' ∈ C := h₁.sum ▸ ⟨a, ha, b', hb', rfl⟩
    have hc2 : a + b'' ∈ C := h₁.sum ▸ ⟨a, ha, b'', hb'', rfl⟩
    have hβ := (h₂.projection_mem hc₂ hc1).1
    have hγ := (h₂.projection_mem hc₂ hc2).2
    have hsum : P (a + b') + L''.projection L hc₂.symm (a + b'') ∈ C :=
      h₂.sum ▸ ⟨_, hβ, _, hγ, rfl⟩
    have hPa : P a = a := Submodule.projection_apply_of_mem_left hc₂ (h₁.subset ha)
    have e1 : P (a + b') = a + P b' := by rw [map_add, hPa]
    have e2 : L''.projection L hc₂.symm (a + b'') = b'' - P b'' := by
      have := Submodule.projection_add_projection_eq_self hc₂ (a + b'')
      rw [map_add, hPa] at this
      rw [eq_sub_of_add_eq' this]; abel
    rw [e1, e2] at hsum
    have hQ := (h₁.projection_mem hc₁ hsum).1
    have hmemL : a + P b' - P b'' ∈ L :=
      L.sub_mem (L.add_mem (h₁.subset ha) (Submodule.projection_apply_mem _ _))
        (Submodule.projection_apply_mem _ _)
    have e3 : a + P b' + (b'' - P b'') = (a + P b' - P b'') + b'' := by abel
    rw [e3, projection_add_of_mem hc₁ hmemL (h₁.subset' hb'')] at hQ
    exact hQ
  -- hence `a + t • P a' ∈ A` for every real `t`
  have hline : ∀ a' ∈ A', ∀ t : ℝ, a + t • P a' ∈ A := by
    intro a' ha' t
    rcases le_or_gt 0 t with ht | ht
    · have := key ((t + 1) • a') (h₁.pos' _ (by linarith) _ ha') a' ha'
      rw [map_smul] at this
      convert this using 1; module
    · have := key a' ha' ((1 - t) • a') (h₁.pos' _ (by linarith) _ ha')
      rw [map_smul] at this
      convert this using 1; module
  rw [← h₁.span', Submodule.span_le]
  intro a' ha'
  by_contra hne
  have hP : P a' ≠ 0 := fun e => hne ((Submodule.projection_apply_eq_zero_iff hc₂).1 e)
  exact hd ⟨a + a', P a', hP, fun t => by
    rw [h₁.sum, add_right_comm]
    exact ⟨_, hline a' ha' t, a', ha', rfl⟩⟩

/-- **Déf. 6, « La donnée du sous-espace distingué `l` détermine complètement `l′` »**, under
the added hypothesis that `F(w)` contains no line (see SCOPE: false without it,
`not_conjugue_unique`). -/
theorem conjugue_unique {w : Set (Sphere E)} (hw : IsConvexPart w) (hsupp : supportK w = univ)
    (hd : ¬ ContientDroite (F w)) {L L' L'' : Submodule ℝ E} (h' : EstConjugueS w L L')
    (h'' : EstConjugueS w L L'') : L' = L'' := by
  have hC := span_F_eq_top_of_supportK hsupp
  rw [estConjugueS_iff hw, hC] at h' h''
  rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨A, A', h₁⟩ <;>
    rcases h'' with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨B, B'', h₂⟩
  · rfl
  · exact e.symm
  · exact ((h₂.isCompl hC).disjoint.eq_bot_of_ge le_top).symm
  · exact e.symm
  · rfl
  · exact absurd rfl h₂.ne_bot
  · exact (h₁.isCompl hC).disjoint.eq_bot_of_ge (e ▸ le_top)
  · exact absurd e h₁.ne_bot
  · exact le_antisymm (le_of_coneDec hC hd h₁ h₂) (le_of_coneDec hC hd h₂ h₁)

/-- A builder for `ConeDec`, the subspaces being the spans, disjointness read off two subspaces
containing `A` and `A'`. -/
theorem coneDec_mk {C A A' : Set E} (hA : Convex ℝ A) (hA' : Convex ℝ A') (hp : IsPosCone A)
    (hp' : IsPosCone A') (h0 : (0 : E) ∉ A) (h0' : (0 : E) ∉ A') (hne : A.Nonempty)
    (hne' : A'.Nonempty) {K K' : Submodule ℝ E} (hK : A ⊆ K) (hK' : A' ⊆ K') (hKK : K ⊓ K' = ⊥)
    (hsum : C = A + A') :
    ConeDec C (Submodule.span ℝ A) (Submodule.span ℝ A') A A' :=
  ⟨hA, hA', hp, hp', h0, h0', hne, hne', rfl, rfl, eq_bot_iff.2 (hKK ▸ inf_le_inf
    (Submodule.span_le.2 hK) (Submodule.span_le.2 hK')), hsum⟩

/-- A cone `C` absorbing the whole space along `u ∈ C` spans it. -/
theorem span_eq_top_of_absorbing {C : Set E} (hp : IsPosCone C) {u : E} (hu : u ∈ C)
    (h : ∀ x : E, ∃ c : ℝ, 0 < c ∧ x + c • u ∈ C) : Submodule.span ℝ C = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨c, hc, hx⟩ := h x
  rw [show x = (x + c • u) - c • u by abel]
  exact Submodule.sub_mem _ (Submodule.subset_span hx) (Submodule.subset_span (hp c hc u hu))

/-! ### The distinguished subvarieties as a type; convex hulls of linear subvarieties -/

/-- The set of the subspaces `L` whose subvariety `s(L − O)` is distinguished, as a type. -/
abbrev DistinguesS (w : Set (Sphere E)) : Type _ := {L : Submodule ℝ E // EstDistingueS w L}

/-- A *simple* distinguished subvariety: minimal among the distinguished subvarieties `≠ ∅`. -/
def EstSimpleS (w : Set (Sphere E)) (L : Submodule ℝ E) : Prop :=
  EstDistingueS w L ∧ L ≠ ⊥ ∧ ∀ M : Submodule ℝ E, EstDistingueS w M → M ≠ ⊥ → M ≤ L → M = L

/-- The set of the simple distinguished subvarieties. -/
def simplesS (w : Set (Sphere E)) : Set (Submodule ℝ E) := {L | EstSimpleS w L}

/-- **« l'enveloppe convexe »**: the least convex part of `S(E)` containing the subvarieties
`s(L − O)`, `L ∈ T`, is `s(∑ T − O)`. -/
theorem isLeast_linearSubvariety_sSup (T : Set (Submodule ℝ E)) :
    IsLeast {k | IsConvexPart k ∧ ∀ L ∈ T, linearSubvariety L ⊆ k}
      (linearSubvariety (sSup T)) := by
  refine ⟨⟨isConvexPart_linearSubvariety _, fun L hL => linearSubvariety_subset_iff.2
    (le_sSup hL)⟩, fun k ⟨hk, hsub⟩ => ?_⟩
  have hmem : ∀ x ∈ sSup T, x ∈ kPrime k := by
    intro x hx
    rw [sSup_eq_iSup'] at hx
    refine Submodule.iSup_induction (fun L : T => (L : Submodule ℝ E)) (motive := (· ∈ kPrime k))
      hx (fun L y hy => ?_) (zero_mem_kPrime k) (fun _ _ => add_mem_kPrime hk)
    by_cases hy0 : y = 0
    · rw [hy0]; exact zero_mem_kPrime k
    · exact mem_insert_of_mem _ ⟨hy0, hsub L.1 L.2 ((mk_mem_linearSubvariety hy0).2 hy)⟩
  intro m hm
  induction m using ind with
  | h v hv =>
  exact ((mem_kPrime_of_ne hv).1 (hmem v ((mk_mem_linearSubvariety hv).1 hm))).2

/-- **« comme sup l'enveloppe convexe »**: the convex hull of `s(L − O) ∪ s(D − O)` is
`s(L + D − O)`. -/
theorem isLeast_linearSubvariety_sup (L D : Submodule ℝ E) :
    IsLeast {k | IsConvexPart k ∧ linearSubvariety L ∪ linearSubvariety D ⊆ k}
      (linearSubvariety (L ⊔ D)) := by
  have h := isLeast_linearSubvariety_sSup ({L, D} : Set (Submodule ℝ E))
  rw [sSup_pair] at h
  convert h using 3 with k
  simp [union_subset_iff]

/-- The convex hull of the `s(D − O)`, `D ∈ T`, is `s(L − O)` iff `L = ∑ T`. -/
theorem isLeast_iff_eq_sSup (T : Set (Submodule ℝ E)) (L : Submodule ℝ E) :
    IsLeast {k | IsConvexPart k ∧ ∀ D ∈ T, linearSubvariety D ⊆ k} (linearSubvariety L) ↔
      sSup T = L := by
  constructor
  · intro h
    exact linearSubvariety_injective ((isLeast_linearSubvariety_sSup T).unique h)
  · rintro rfl
    exact isLeast_linearSubvariety_sSup T


section Ouvert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The closed cone `K̄ = closure (insert O F(w))` -/

theorem smul_mem_closure_kPrime {w : Set (Sphere E)} {x : E} (hx : x ∈ closure (kPrime w))
    {c : ℝ} (hc : 0 ≤ c) : c • x ∈ closure (kPrime w) :=
  map_mem_closure (continuous_const_smul c) hx fun _ hy => smul_mem_kPrime hy hc

theorem add_mem_closure_kPrime {w : Set (Sphere E)} (hw : IsConvexPart w) {x y : E}
    (hx : x ∈ closure (kPrime w)) (hy : y ∈ closure (kPrime w)) :
    x + y ∈ closure (kPrime w) := by
  have h := (convex_kPrime hw).closure hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have := smul_mem_closure_kPrime h (by norm_num : (0 : ℝ) ≤ 2)
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at this

theorem zero_mem_closure_kPrime (w : Set (Sphere E)) : (0 : E) ∈ closure (kPrime w) :=
  subset_closure (zero_mem_kPrime w)

theorem span_closure_kPrime {w : Set (Sphere E)} (hsupp : supportK w = univ) :
    Submodule.span ℝ (closure (kPrime w)) = ⊤ :=
  eq_top_iff.2 ((span_F_eq_top_of_supportK hsupp).symm.le.trans
    (Submodule.span_mono ((subset_insert _ _).trans subset_closure)))

/-- For `w` open with empty noyau and no line in `F(w)`, the closed cone `K̄` contains no line. -/
theorem not_contientDroite_closure {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) : ¬ ContientDroite (closure (kPrime w)) := by
  rintro ⟨x, v, hv, h⟩
  -- the direction of a line of `K̄` lies in `K̄`
  have hdir : ∀ u : E, (∀ t : ℝ, x + t • u ∈ closure (kPrime w)) → u ∈ closure (kPrime w) := by
    intro u hu
    have ht : Tendsto (fun t : ℝ => t⁻¹ • x + u) atTop (𝓝 u) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const x
      simpa using this.add_const u
    refine isClosed_closure.mem_of_tendsto ht ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
    have := smul_mem_closure_kPrime (hu t) (inv_nonneg.2 ht0.le)
    rwa [smul_add, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul] at this
  have hv1 := hdir v h
  have hv2 := hdir (-v) fun t => by simpa [neg_smul, smul_neg] using h (-t)
  have hsv : ∀ s : ℝ, s • v ∈ closure (kPrime w) := by
    intro s
    rcases le_total 0 s with hs | hs
    · exact smul_mem_closure_kPrime hv1 hs
    · have := smul_mem_closure_kPrime hv2 (neg_nonneg.2 hs)
      rwa [smul_neg, neg_smul, neg_neg] at this
  rcases (F w).eq_empty_or_nonempty with hF | ⟨c, hc⟩
  · have h0 : closure (kPrime w) = {0} := by
      rw [kPrime, hF, insert_empty_eq, closure_singleton]
    have e0 := h 0
    have e1 := h 1
    rw [h0, mem_singleton_iff] at e0 e1
    rw [zero_smul, add_zero] at e0
    rw [e0, zero_add, one_smul] at e1
    exact hv e1
  have hFo : IsOpen (F w) := isOpen_iff_F.1 hopen
  have hcK : c ∈ interior (kPrime w) :=
    interior_maximal (subset_insert _ _) hFo hc
  have hint : interior (closure (kPrime w)) = interior (kPrime w) :=
    (convex_kPrime hw).interior_closure_eq_interior_of_nonempty_interior ⟨c, hcK⟩
  have hline : ∀ s : ℝ, c + s • v ∈ kPrime w := by
    intro s
    have hc' : c ∈ interior (closure (kPrime w)) := hint ▸ hcK
    have hy : c + (2 * s) • v ∈ closure (closure (kPrime w)) := by
      rw [closure_closure]
      exact add_mem_closure_kPrime hw (subset_closure (subset_insert _ _ hc)) (hsv _)
    have hseg := (convex_kPrime hw).closure.openSegment_interior_closure_subset_interior hc' hy
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    rw [hint] at hseg
    have e : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • (c + (2 * s) • v) = c + s • v := by module
    rw [e] at hseg
    exact interior_subset hseg
  by_cases hz : ∃ s₀ : ℝ, c + s₀ • v = 0
  · obtain ⟨s₀, hs₀⟩ := hz
    have hmem : ∀ r : ℝ, r ≠ 0 → r • v ∈ F w := by
      intro r hr
      have e : c + (s₀ + r) • v = r • v := by
        rw [add_smul, ← add_assoc, hs₀, zero_add]
      have h1 := hline (s₀ + r)
      rw [e] at h1
      exact (mem_kPrime_of_ne (smul_ne_zero hr hv)).1 h1
    have hp : v ∈ F w := by simpa using hmem 1 one_ne_zero
    have hm : -v ∈ F w := by simpa using hmem (-1) (by norm_num)
    have : mk v hv ∈ noyau w := by
      rw [noyau_eq hw]
      refine ⟨hp.2, ?_⟩
      rw [neg_mk]
      exact hm.2
    rw [hn] at this
    exact this
  · push Not at hz
    exact hd ⟨c, v, hv, fun s => (mem_kPrime_of_ne (hz s)).1 (hline s)⟩

/-- `(E, 0)` is a conjugate pair relative to any `W ∋ 0`. -/
theorem sontConjugues_top_bot {F' : Type*} [AddCommGroup F'] [Module ℝ F'] {W : Set F'}
    (h0 : (0 : F') ∈ W) : SontConjugues W ⊤ ⊥ := by
  ext x
  constructor
  · intro hx
    exact ⟨x, ⟨trivial, hx⟩, 0, ⟨(⊥ : Submodule ℝ F').zero_mem, h0⟩, add_zero x⟩
  · rintro ⟨a, ⟨-, ha⟩, b, ⟨hb, -⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot] at hb
    simpa [hb] using ha

/-- A point `a` with `a + s a' ∈ F(w)` for all `s > 0` lies in `K̄`. -/
theorem mem_closure_kPrime_of_add {w : Set (Sphere E)} {a a' : E}
    (h : ∀ s : ℝ, 0 < s → a + s • a' ∈ F w) : a ∈ closure (kPrime w) := by
  have ht : Tendsto (fun s : ℝ => a + s • a') (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun s : ℝ => a + s • a') (𝓝 0) (𝓝 (a + (0 : ℝ) • a')) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact subset_insert _ _ (h s hs)

variable [FiniteDimensional ℝ E]

/-- A projection mapping `K = insert O F(w)` into `K̄` maps `K̄` into `K̄`. -/
theorem projection_mapsTo_closure {w : Set (Sphere E)} {L L' : Submodule ℝ E} (hc : IsCompl L L')
    (h : ∀ x ∈ kPrime w, L.projection L' hc x ∈ closure (kPrime w)) {x : E}
    (hx : x ∈ closure (kPrime w)) : L.projection L' hc x ∈ closure (kPrime w) := by
  have := map_mem_closure (LinearMap.continuous_of_finiteDimensional (L.projection L' hc)) hx h
  rwa [closure_closure] at this

omit [FiniteDimensional ℝ E] in
/-- In an open `F(w)` whose closed cone `K̄` contains no line, a projection on `L ≠ 0`
preserving `K̄` vanishes at no point of `F(w)`. -/
theorem projection_ne_zero {w : Set (Sphere E)} (hopen : IsOpen w)
    (hdK : ¬ ContientDroite (closure (kPrime w))) {L L' : Submodule ℝ E} (hc : IsCompl L L')
    (hmaps : ∀ x ∈ closure (kPrime w), L.projection L' hc x ∈ closure (kPrime w))
    (hL : L ≠ ⊥) {c : E} (hcw : c ∈ F w) : L.projection L' hc c ≠ 0 := by
  intro hP
  obtain ⟨l, hlL, hl⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  have hFo : IsOpen (F w) := isOpen_iff_F.1 hopen
  have hcont : Continuous fun s : ℝ => c + s • l := continuous_const.add
    (continuous_id.smul continuous_const)
  have hnhds : (fun s : ℝ => c + s • l) ⁻¹' F w ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hFo.mem_nhds hcw)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hmem : ∀ e : ℝ, |e| < ε → e • l ∈ closure (kPrime w) := by
    intro e he
    have h1 : c + e • l ∈ F w := hball (by simpa [Real.dist_eq] using he)
    have := hmaps _ (subset_closure (subset_insert _ _ h1))
    rwa [map_add, hP, zero_add, map_smul, Submodule.projection_apply_of_mem_left hc hlL] at this
  have hε2 : |ε / 2| < ε := by rw [abs_of_pos (by positivity)]; linarith
  have hε2' : |-(ε / 2)| < ε := by rwa [abs_neg]
  refine hdK ⟨0, l, hl, fun t => ?_⟩
  rw [zero_add]
  rcases le_total 0 t with ht | ht
  · have := smul_mem_closure_kPrime (hmem _ hε2) (div_nonneg ht (by positivity : (0 : ℝ) ≤ ε / 2))
    rwa [smul_smul, div_mul_cancel₀ _ (by positivity : ε / 2 ≠ 0)] at this
  · have := smul_mem_closure_kPrime (hmem _ hε2')
      (div_nonneg (neg_nonneg.2 ht) (by positivity : (0 : ℝ) ≤ ε / 2))
    rwa [smul_smul, div_mul_eq_mul_div, neg_mul_neg, mul_div_assoc,
      div_self (by positivity : ε / 2 ≠ 0), mul_one] at this

/-- **The transfer to the affine case** (« il suffit de se reporter aux énoncés correspondants
formulés dans le cas affin »): for `w` open, `(L, L')` is a conjugate pair of Déf. 6 iff it is a
pair of supplementary conjugate subspaces (Déf. 3, 4) of the closed cone `K̄`. -/
theorem estConjugueS_iff_affine {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hdK : ¬ ContientDroite (closure (kPrime w)))
    {L L' : Submodule ℝ E} :
    EstConjugueS w L L' ↔ IsCompl L L' ∧ SontConjugues (closure (kPrime w)) L L' := by
  have hC := span_F_eq_top_of_supportK hsupp
  rw [estConjugueS_iff hw, hC]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨A, A', h⟩)
    · exact ⟨isCompl_top_bot, sontConjugues_top_bot (zero_mem_closure_kPrime w)⟩
    · exact ⟨isCompl_bot_top, (sontConjugues_top_bot (zero_mem_closure_kPrime w)).symm⟩
    have hc := h.isCompl hC
    have hAK : ∀ a ∈ A, a ∈ closure (kPrime w) := by
      intro a ha
      obtain ⟨a', ha'⟩ := h.ne'
      exact mem_closure_kPrime_of_add fun s hs => by
        rw [h.sum]; exact ⟨a, ha, s • a', h.pos' s hs a' ha', rfl⟩
    have hAK' : ∀ a ∈ A', a ∈ closure (kPrime w) := by
      intro a' ha'
      obtain ⟨a, ha⟩ := h.ne
      exact mem_closure_kPrime_of_add fun s hs => by
        rw [h.sum]; exact ⟨s • a, h.pos s hs a ha, a', ha', add_comm _ _⟩
    have hm1 : ∀ x ∈ closure (kPrime w), L.projection L' hc x ∈ closure (kPrime w) := by
      refine fun x hx => projection_mapsTo_closure hc (fun y hy => ?_) hx
      rcases mem_insert_iff.1 hy with rfl | hy
      · rw [map_zero]; exact zero_mem_closure_kPrime w
      · exact hAK _ (h.projection_mem hc hy).1
    have hm2 : ∀ x ∈ closure (kPrime w), L'.projection L hc.symm x ∈ closure (kPrime w) := by
      refine fun x hx => projection_mapsTo_closure hc.symm (fun y hy => ?_) hx
      rcases mem_insert_iff.1 hy with rfl | hy
      · rw [map_zero]; exact zero_mem_closure_kPrime w
      · exact hAK' _ (h.projection_mem hc hy).2
    refine ⟨hc, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨_, ⟨Submodule.projection_apply_mem _ _, hm1 x hx⟩, _,
        ⟨Submodule.projection_apply_mem _ _, hm2 x hx⟩,
        Submodule.projection_add_projection_eq_self hc x⟩
    · rintro ⟨a, ⟨-, ha⟩, b, ⟨-, hb⟩, rfl⟩
      exact add_mem_closure_kPrime hw ha hb
  · rintro ⟨hc, hconj⟩
    by_cases hL : L = ⊥
    · subst hL
      exact Or.inr (Or.inl ⟨rfl, eq_top_of_isCompl_bot hc.symm⟩)
    by_cases hL' : L' = ⊥
    · subst hL'
      exact Or.inl ⟨eq_top_of_isCompl_bot hc, rfl⟩
    refine Or.inr (Or.inr ⟨L.projection L' hc '' F w, L'.projection L hc.symm '' F w, ?_⟩)
    have hm1 : ∀ x ∈ closure (kPrime w), L.projection L' hc x ∈ closure (kPrime w) :=
      fun x hx => (projection_mem_inter hc hconj hx).2
    have hm2 : ∀ x ∈ closure (kPrime w), L'.projection L hc.symm x ∈ closure (kPrime w) :=
      fun x hx => (projection_mem_inter hc.symm hconj.symm hx).2
    have hz1 := fun c (hcw : c ∈ F w) => projection_ne_zero hopen hdK hc hm1 hL hcw
    have hz2 := fun c (hcw : c ∈ F w) => projection_ne_zero hopen hdK hc.symm hm2 hL' hcw
    -- `F(w)` is convex: `w` has no pair of opposite points
    have hconv : Convex ℝ (F w) := by
      refine isStrictConvexPart_iff_convex_F.1 ⟨hw, fun m hm hm' => ?_⟩
      induction m using ind with
      | h M hM =>
      rw [neg_mk] at hm'
      have h1 : M ∈ kPrime w := subset_insert _ _ ⟨hM, hm⟩
      have h2 : -M ∈ kPrime w := subset_insert _ _ ⟨neg_ne_zero.2 hM, hm'⟩
      refine hdK ⟨0, M, hM, fun t => subset_closure ?_⟩
      rw [zero_add]
      rcases le_total 0 t with ht | ht
      · exact smul_mem_kPrime h1 ht
      · have := smul_mem_kPrime h2 (neg_nonneg.2 ht)
        rwa [smul_neg, neg_smul, neg_neg] at this
    have hne : (F w).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hF
      rw [hF, Submodule.span_empty] at hC
      exact hL (eq_bot_iff.2 (hC ▸ le_top))
    have hpos : ∀ (P : E →ₗ[ℝ] E), IsPosCone (P '' F w) := by
      rintro P c hc' _ ⟨x, hx, rfl⟩
      exact ⟨c • x, smul_mem_F hx hc', map_smul P c x⟩
    obtain ⟨c₀, hc₀⟩ := hne
    have hFo : IsOpen (F w) := isOpen_iff_F.1 hopen
    have hint : interior (closure (kPrime w)) = interior (kPrime w) :=
      (convex_kPrime hw).interior_closure_eq_interior_of_nonempty_interior
        ⟨c₀, interior_maximal (subset_insert _ _) hFo hc₀⟩
    refine ⟨hconv.linear_image _, hconv.linear_image _, hpos _, hpos _,
      fun ⟨c, hcw, e⟩ => hz1 c hcw e, fun ⟨c, hcw, e⟩ => hz2 c hcw e, ⟨_, c₀, hc₀, rfl⟩,
      ⟨_, c₀, hc₀, rfl⟩, ?_, ?_, hc.inf_eq_bot, ?_⟩
    · rw [Submodule.span_image, hC, Submodule.map_top, Submodule.range_projection]
    · rw [Submodule.span_image, hC, Submodule.map_top, Submodule.range_projection]
    ext x
    constructor
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x, hx, rfl⟩, Submodule.projection_add_projection_eq_self hc x⟩
    · rintro ⟨_, ⟨c, hcw, rfl⟩, _, ⟨c', hc'w, rfl⟩, rfl⟩
      set T : E × E →ₗ[ℝ] E := (L.projection L' hc).comp (LinearMap.fst ℝ E E) +
        (L'.projection L hc.symm).comp (LinearMap.snd ℝ E E) with hT
      have hTs : Function.Surjective T := fun y =>
        ⟨(y, y), by simp [hT, Submodule.projection_add_projection_eq_self hc y]⟩
      have hU : IsOpen (T '' (F w ×ˢ F w)) :=
        LinearMap.isOpenMap_of_finiteDimensional T hTs _ (hFo.prod hFo)
      have hUK : T '' (F w ×ˢ F w) ⊆ closure (kPrime w) := by
        rintro _ ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩
        exact add_mem_closure_kPrime hw (hm1 _ (subset_closure (subset_insert _ _ hy)))
          (hm2 _ (subset_closure (subset_insert _ _ hy')))
      have hmem : T (c, c') ∈ kPrime w := by
        have := interior_maximal hUK hU ⟨(c, c'), ⟨hcw, hc'w⟩, rfl⟩
        rw [hint] at this
        exact interior_subset this
      have hTc : T (c, c') = L.projection L' hc c + L'.projection L hc.symm c' := by simp [hT]
      rw [hTc] at hmem
      refine (mem_kPrime_of_ne fun h0 => hz1 c hcw ?_).1 hmem
      have hm : L.projection L' hc c ∈ L ⊓ L' := by
        refine Submodule.mem_inf.2 ⟨Submodule.projection_apply_mem _ _, ?_⟩
        rw [eq_neg_of_add_eq_zero_left h0]
        exact L'.neg_mem (Submodule.projection_apply_mem _ _)
      rwa [hc.inf_eq_bot, Submodule.mem_bot] at hm

/-- Déf. 6 for `w` open: the distinguished subvarieties are the distinguished subspaces (Déf. 3)
of the closed cone `K̄`. -/
theorem estDistingueS_iff_affine {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hdK : ¬ ContientDroite (closure (kPrime w)))
    {L : Submodule ℝ E} : EstDistingueS w L ↔ EstDistingue (closure (kPrime w)) L :=
  ⟨fun ⟨L', h⟩ => ⟨L', (estConjugueS_iff_affine hw hopen hsupp hdK).1 h⟩,
    fun ⟨L', h1, h2⟩ => ⟨L', (estConjugueS_iff_affine hw hopen hsupp hdK).2 ⟨h1, h2⟩⟩⟩

/-- **Théorème 3**, the structure, for `w` open: the distinguished subvarieties, ordered by
inclusion, with `⊓` the intersection, `⊔` the convex hull, `⊤ = S(E)`, `⊥ = ∅` and the
complement the conjugate. -/
@[implicit_reducible]
noncomputable def algebreBooleS {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) :
    BooleanAlgebra (DistinguesS w) :=
  have hdK := not_contientDroite_closure hw hopen hn hd
  have hW := (convex_kPrime hw).closure
  have h0 := zero_mem_closure_kPrime w
  have hspan := span_closure_kPrime hsupp
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_affine hw hopen hsupp hdK (L := L)
  letI : Lattice (DistinguesS w) :=
    Subtype.lattice (fun L D hL hD => (hiff _).2 ⟨_,
        (estDistingue_sup hW h0 hspan hdK ((hiff L).1 hL) ((hiff D).1 hD)).1,
        (estDistingue_sup hW h0 hspan hdK ((hiff L).1 hL) ((hiff D).1 hD)).2⟩)
      (fun L D hL hD => (hiff _).2 ⟨_,
        (estDistingue_inf hW h0 hspan hdK ((hiff L).1 hL) ((hiff D).1 hD)).1,
        (estDistingue_inf hW h0 hspan hdK ((hiff L).1 hL) ((hiff D).1 hD)).2⟩)
  letI : DistribLattice (DistinguesS w) :=
    DistribLattice.ofInfSupLe fun a b c => inf_sup_le_of_estDistingue hW h0 hspan hdK
      ((hiff _).1 a.2) ((hiff _).1 b.2) ((hiff _).1 c.2)
  letI : BoundedOrder (DistinguesS w) :=
    Subtype.boundedOrder ((hiff _).2 (estDistingue_bot h0)) ((hiff _).2 (estDistingue_top h0))
  { (inferInstance : DistribLattice (DistinguesS w)),
    (inferInstance : BoundedOrder (DistinguesS w)) with
    compl := fun x => ⟨conjugue (closure (kPrime w)) x.1,
      (hiff _).2 (estDistingue_conjugue ((hiff _).1 x.2))⟩
    inf_compl_le_bot := fun x => (conjugue_spec ((hiff _).1 x.2)).1.disjoint.le_bot
    top_le_sup_compl := fun x => (conjugue_spec ((hiff _).1 x.2)).1.codisjoint.top_le }

/-- **Théorème 3** (l.570), for `w` open and `F(w)` containing no line (the corrected
statement, see SCOPE: false as printed, `not_theoreme3`): the distinguished subvarieties form a
Boolean algebra whose `1` is `S(E)`, whose `0` is `∅`, with complement THE conjugate (it exists
and is unique), inf the intersection and sup the convex hull. -/
theorem theoreme3 {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) :
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
  have hdK := not_contientDroite_closure hw hopen hn hd
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_affine hw hopen hsupp hdK (L := L)
  have hcomp : ∀ x : DistinguesS w,
      EstConjugueS w x.1 ((algebreBooleS hw hopen hsupp hn hd).compl x).1 := fun x =>
    (estConjugueS_iff_affine hw hopen hsupp hdK).2 (conjugue_spec ((hiff _).1 x.2))
  exact ⟨algebreBooleS hw hopen hsupp hn hd, fun x y => linearSubvariety_subset_iff.symm,
    linearSubvariety_top_eq, linearSubvariety_bot, hcomp,
    fun x L' h => conjugue_unique hw hsupp hd h (hcomp x),
    fun x y => (linearSubvariety_inter _ _).symm,
    fun x y => isLeast_linearSubvariety_sup _ _⟩

theorem simplesS_eq {w : Set (Sphere E)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hsupp : supportK w = univ) (hdK : ¬ ContientDroite (closure (kPrime w))) :
    simplesS w = simples (closure (kPrime w)) := by
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_affine hw hopen hsupp hdK (L := L)
  ext L
  simp only [simplesS, simples, EstSimpleS, EstSimple, mem_setOf_eq, hiff]

/-- Transport of an order isomorphism along equal sets and equivalent predicates. -/
theorem exists_orderIso_transport {α : Type*} [Preorder α] {S S' : Set α} {P P' : α → Prop} (hS : S = S')
    (hP : P = P') (f : Set α → α) (e : Set S' ≃o {x // P' x})
    (he : ∀ T, (e T).1 = f (Subtype.val '' T)) :
    ∃ e' : Set S ≃o {x // P x}, ∀ T, (e' T).1 = f (Subtype.val '' T) := by
  subst hS; subst hP; exact ⟨e, he⟩

/-- **Corollaire** of Théorème 3 (l.579), for `w` open and `F(w)` containing no line (the
corrected statement, see SCOPE: false as printed, `not_corollaire_algebre_parties`): if `E` has
dimension `n + 1`, the distinguished subvarieties are, as a Boolean algebra, the subsets of the
finite set of simple ones, of cardinal between `1` and `n + 1`, by `T ↦` the convex hull of
`T`; every distinguished subvariety is, in one and only one way, the convex hull of a family
of simple ones. -/
theorem corollaire_algebre_parties_projective {w : Set (Sphere E)} (hw : IsConvexPart w)
    (hopen : IsOpen w) (hsupp : supportK w = univ) (hn : noyau w = ∅)
    (hd : ¬ ContientDroite (F w)) {n : ℕ} (hE : Module.finrank ℝ E = n + 1) :
    (simplesS w).Finite ∧ 1 ≤ (simplesS w).ncard ∧ (simplesS w).ncard ≤ n + 1 ∧
      (∃ e : Set (simplesS w) ≃o DistinguesS w, ∀ T,
        linearSubvariety (e T).1 = linearSubvariety (sSup (Subtype.val '' T))) ∧
      (∀ T ⊆ simplesS w, EstDistingueS w (sSup T)) ∧
      (∀ L : Submodule ℝ E, EstDistingueS w L → ∃! T : Set (Submodule ℝ E), T ⊆ simplesS w ∧
        IsLeast {k | IsConvexPart k ∧ ∀ D ∈ T, linearSubvariety D ⊆ k} (linearSubvariety L)) := by
  have hdK := not_contientDroite_closure hw hopen hn hd
  have hiff := fun L : Submodule ℝ E => estDistingueS_iff_affine hw hopen hsupp hdK (L := L)
  have hS := simplesS_eq hw hopen hsupp hdK
  obtain ⟨hfin, hcard, hpos, ⟨e, he⟩, hsum, huniq⟩ := corollaire_algebre_parties
    (convex_kPrime hw).closure (zero_mem_closure_kPrime w) (span_closure_kPrime hsupp) hdK
  rw [hE] at hcard hpos
  have hP : (fun L => EstDistingueS w L) = (fun L => EstDistingue (closure (kPrime w)) L) :=
    funext fun L => propext (hiff L)
  obtain ⟨e', he'⟩ := exists_orderIso_transport hS hP sSup e he
  refine ⟨hS ▸ hfin, hS ▸ hpos (Nat.succ_pos n), hS ▸ hcard, ⟨e', fun T => by rw [he']⟩,
    fun T hT => (hiff _).2 (hsum T (hS ▸ hT)), fun L hL => ?_⟩
  obtain ⟨T, ⟨hT, hTL⟩, hTu⟩ := huniq L ((hiff L).1 hL)
  refine ⟨T, ⟨hS ▸ hT, (isLeast_iff_eq_sSup T L).2 hTL⟩, fun T' ⟨hT', hT'L⟩ => ?_⟩
  exact hTu T' ⟨hS ▸ hT', (isLeast_iff_eq_sSup T' L).1 hT'L⟩

end Ouvert

end Sphere

/-! ### Instances and counterexamples in `S(2)` -/

namespace BooleProjectifInstance

open Sphere

abbrev V3 : Type := Fin 3 → ℝ

/-- `{v | v i = t v j}`. -/
def hyp (i j : Fin 3) (t : ℝ) : Set V3 := {v | v i = t * v j}
/-- `{v | v i = 0}`. -/
def ze (i : Fin 3) : Set V3 := {v | v i = 0}
/-- `{v | 0 < v i}`. -/
def po (i : Fin 3) : Set V3 := {v | 0 < v i}
/-- `{v | 0 ≤ v i}`. -/
def nn (i : Fin 3) : Set V3 := {v | 0 ≤ v i}

theorem combo_pos {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < a * x + b * y := by
  rcases ha.lt_or_eq with ha | rfl
  · nlinarith [mul_pos ha hx, mul_nonneg hb hy.le]
  · rw [zero_add] at hab; subst hab; simpa

theorem convex_hyp (i j : Fin 3) (t : ℝ) : Convex ℝ (hyp i j t) := by
  intro x hx y hy a b _ _ _
  simp only [hyp, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [hx, hy]; ring

theorem convex_ze (i : Fin 3) : Convex ℝ (ze i) := by
  intro x hx y hy a b _ _ _
  simp only [ze, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [hx, hy]; ring

theorem convex_po (i : Fin 3) : Convex ℝ (po i) := by
  intro x hx y hy a b ha hb hab
  simp only [po, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  exact combo_pos hx hy ha hb hab

theorem convex_nn (i : Fin 3) : Convex ℝ (nn i) := by
  intro x hx y hy a b ha hb _
  simp only [nn, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  positivity

theorem pos_inter {A B : Set V3} (hA : IsPosCone A) (hB : IsPosCone B) :
    IsPosCone (A ∩ B) := fun c hc v hv => ⟨hA c hc v hv.1, hB c hc v hv.2⟩

theorem pos_hyp (i j : Fin 3) (t : ℝ) : IsPosCone (hyp i j t) := fun c _ v hv => by
  simp only [hyp, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
  rw [hv]; ring

theorem pos_ze (i : Fin 3) : IsPosCone (ze i) := fun c _ v hv => by
  simp only [ze, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
  rw [hv, mul_zero]

theorem pos_po (i : Fin 3) : IsPosCone (po i) := fun c hc v hv => by
  simp only [po, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
  exact mul_pos hc hv

theorem pos_nn (i : Fin 3) : IsPosCone (nn i) := fun c hc v hv => by
  simp only [nn, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
  exact mul_nonneg hc.le hv

theorem zero_notMem_po {A : Set V3} (i : Fin 3) : (0 : V3) ∉ A ∩ po i := fun h => by
  simp [po] at h

/-- The subspace `{v | v i = t v j}`. -/
def hypS (i j : Fin 3) (t : ℝ) : Submodule ℝ V3 :=
  LinearMap.ker (LinearMap.proj i - t • LinearMap.proj j)

theorem mem_hypS {i j : Fin 3} {t : ℝ} {v : V3} : v ∈ hypS i j t ↔ v i = t * v j := by
  simp [hypS, sub_eq_zero]

theorem hyp_subset (i j : Fin 3) (t : ℝ) : hyp i j t ⊆ hypS i j t := fun _ hv => mem_hypS.2 hv

theorem ze_subset (i : Fin 3) : ze i ⊆ hypS i i 0 := fun v hv => mem_hypS.2 (by
  simp only [ze, mem_setOf_eq] at hv; rw [hv, zero_mul])

theorem eq_zero_of_coords {v : V3} (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 0) : v = 0 := by
  ext i; fin_cases i <;> simpa

/-- `{v | v i = 0}` as a subspace. -/
abbrev zeS (i : Fin 3) : Submodule ℝ V3 := hypS i i 0

theorem mem_zeS {i : Fin 3} {v : V3} : v ∈ zeS i ↔ v i = 0 := by
  rw [mem_hypS, zero_mul]

/-! #### The open quarter `w₁ = {y > 0, z > 0}` of `S(2)` -/

/-- The cone of the open quarter of `S(2)`. -/
def quart : Set V3 := po 1 ∩ po 2

/-- **The open quarter** `w₁ = s({y > 0, z > 0})` of `S(2)`: open, convex, of support `S(2)`, of
empty noyau. -/
def quartS : Set (S 2) := ofCone quart

theorem pos_quart : IsPosCone quart := pos_inter (pos_po 1) (pos_po 2)

theorem F_quartS : F quartS = quart := F_ofCone_of_zero_notMem pos_quart (zero_notMem_po 2)

theorem isConvexPart_quartS : IsConvexPart quartS :=
  isConvexPart_ofCone_of_cone ((convex_po 1).inter (convex_po 2)) pos_quart

theorem isOpen_quartS : IsOpen quartS := by
  rw [isOpen_iff_F, F_quartS]
  exact (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_lt continuous_const (continuous_apply 2))

theorem span_quart : Submodule.span ℝ quart = ⊤ := by
  refine span_eq_top_of_absorbing pos_quart (u := ![0, 1, 1]) ⟨by simp [po], by simp [po]⟩
    fun x => ⟨|x 1| + |x 2| + 1, by positivity, ?_, ?_⟩
  · simp only [po, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_one]
    linarith [neg_abs_le (x 1), abs_nonneg (x 2)]
  · simp only [po, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one]
    linarith [neg_abs_le (x 2), abs_nonneg (x 1)]

theorem supportK_quartS : supportK quartS = univ := by
  rw [supportK, F_quartS, span_quart, linearSubvariety_top_eq]

theorem noyau_quartS : noyau quartS = ∅ := by
  rw [noyau_eq isConvexPart_quartS]
  refine eq_empty_of_forall_notMem fun m ⟨h, h'⟩ => ?_
  induction m using ind with
  | h M hM =>
  rw [neg_mk, mk_mem_iff_mem_F, F_quartS] at h'
  rw [mk_mem_iff_mem_F, F_quartS] at h
  have := h.1; have := h'.1
  simp only [po, mem_setOf_eq, Pi.neg_apply] at *
  linarith

/-- The open half-plane `{z = 0, y > 0}` (the open half-circle of `z = 0`). -/
def A0 : Set V3 := ze 2 ∩ po 1
/-- The ray of `e₃`. -/
def A3 : Set V3 := (ze 0 ∩ ze 1) ∩ po 2
/-- The ray of `e₁ + e₃`. -/
def A4 : Set V3 := (hyp 0 2 1 ∩ ze 1) ∩ po 2

theorem coneDec_A0_A3 : ConeDec quart (Submodule.span ℝ A0) (Submodule.span ℝ A3) A0 A3 := by
  refine coneDec_mk ((convex_ze 2).inter (convex_po 1))
    (((convex_ze 0).inter (convex_ze 1)).inter (convex_po 2)) (pos_inter (pos_ze 2) (pos_po 1))
    (pos_inter (pos_inter (pos_ze 0) (pos_ze 1)) (pos_po 2)) (zero_notMem_po 1) (zero_notMem_po 2)
    ⟨![0, 1, 0], by simp [A0, ze, po]⟩ ⟨![0, 0, 1], by simp [A3, ze, po]⟩
    (K := zeS 2) (K' := zeS 0 ⊓ zeS 1) (fun v hv => mem_zeS.2 hv.1)
    (fun v hv => Submodule.mem_inf.2 ⟨mem_zeS.2 hv.1.1, mem_zeS.2 hv.1.2⟩) ?_ ?_
  · rw [eq_bot_iff]
    intro v hv
    simp only [Submodule.mem_inf, mem_zeS] at hv
    exact (Submodule.mem_bot ℝ).2 (eq_zero_of_coords hv.2.1 hv.2.2 hv.1)
  · ext v
    simp only [quart, A0, A3, ze, po, mem_inter_iff, mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨![v 0, v 1, 0], ⟨by simp, by simpa⟩, ![0, 0, v 2], ⟨⟨by simp, by simp⟩, by simpa⟩,
        ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨a, ⟨ha2, ha1⟩, b, ⟨⟨hb0, hb1⟩, hb2⟩, rfl⟩
      simp only [Pi.add_apply]
      constructor <;> linarith

theorem coneDec_A0_A4 : ConeDec quart (Submodule.span ℝ A0) (Submodule.span ℝ A4) A0 A4 := by
  refine coneDec_mk ((convex_ze 2).inter (convex_po 1))
    (((convex_hyp 0 2 1).inter (convex_ze 1)).inter (convex_po 2))
    (pos_inter (pos_ze 2) (pos_po 1)) (pos_inter (pos_inter (pos_hyp 0 2 1) (pos_ze 1)) (pos_po 2))
    (zero_notMem_po 1) (zero_notMem_po 2)
    ⟨![0, 1, 0], by simp [A0, ze, po]⟩ ⟨![1, 0, 1], by simp [A4, hyp, ze, po]⟩
    (K := zeS 2) (K' := hypS 0 2 1 ⊓ zeS 1) (fun v hv => mem_zeS.2 hv.1)
    (fun v hv => Submodule.mem_inf.2 ⟨mem_hypS.2 hv.1.1, mem_zeS.2 hv.1.2⟩) ?_ ?_
  · rw [eq_bot_iff]
    intro v hv
    simp only [Submodule.mem_inf, mem_hypS, zero_mul, one_mul] at hv
    exact (Submodule.mem_bot ℝ).2 (eq_zero_of_coords (by rw [hv.2.1, hv.1]) hv.2.2 hv.1)
  · ext v
    simp only [quart, A0, A4, hyp, ze, po, mem_inter_iff, mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨![v 0 - v 2, v 1, 0], ⟨by simp, by simpa⟩, ![v 2, 0, v 2],
        ⟨⟨by simp, by simp⟩, by simpa⟩, ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨a, ⟨ha2, ha1⟩, b, ⟨⟨hb0, hb1⟩, hb2⟩, rfl⟩
      simp only [Pi.add_apply]
      constructor <;> linarith

theorem quart_conjugue_A3 :
    EstConjugueS quartS (Submodule.span ℝ A0) (Submodule.span ℝ A3) :=
  (estConjugueS_iff isConvexPart_quartS).2
    (Or.inr (Or.inr ⟨A0, A3, F_quartS ▸ coneDec_A0_A3⟩))

theorem quart_conjugue_A4 :
    EstConjugueS quartS (Submodule.span ℝ A0) (Submodule.span ℝ A4) :=
  (estConjugueS_iff isConvexPart_quartS).2
    (Or.inr (Or.inr ⟨A0, A4, F_quartS ▸ coneDec_A0_A4⟩))

theorem span_A3_ne_span_A4 : Submodule.span ℝ A3 ≠ Submodule.span ℝ A4 := by
  intro h
  have h3 : (![0, 0, 1] : V3) ∈ Submodule.span ℝ A4 :=
    h ▸ Submodule.subset_span (by simp [A3, ze, po])
  have := Submodule.span_le.2 (fun v hv => mem_hypS.2 hv.1.1 : A4 ⊆ hypS 0 2 1) h3
  simp [mem_hypS] at this

/-- **Déf. 6's claim « La donnée du sous-espace distingué `l` détermine complètement le
sous-espace distingué `l′` » is false as printed**: relative to the open quarter `w₁` of `S(2)`
(convex, open, of support `S(2)`, of empty noyau), the great circle `z = 0` is distinguished
with two different conjugates, the pair `{±e₃}` and the pair `{±(e₁ + e₃)}`. -/
theorem not_conjugue_unique :
    ∃ w : Set (S 2), IsConvexPart w ∧ IsOpen w ∧ supportK w = univ ∧ noyau w = ∅ ∧
      ∃ L L' L'' : Submodule ℝ V3, EstConjugueS w L L' ∧ EstConjugueS w L L'' ∧ L' ≠ L'' :=
  ⟨quartS, isConvexPart_quartS, isOpen_quartS, supportK_quartS, noyau_quartS, _, _, _,
    quart_conjugue_A3, quart_conjugue_A4, span_A3_ne_span_A4⟩

/-- The ray of `t e₁ + e₂`. -/
def Bt (t : ℝ) : Set V3 := (ze 2 ∩ hyp 0 1 t) ∩ po 1
/-- The open half-plane `{y = 0, z > 0}`. -/
def B' : Set V3 := ze 1 ∩ po 2

theorem coneDec_Bt (t : ℝ) :
    ConeDec quart (Submodule.span ℝ (Bt t)) (Submodule.span ℝ B') (Bt t) B' := by
  refine coneDec_mk (((convex_ze 2).inter (convex_hyp 0 1 t)).inter (convex_po 1))
    ((convex_ze 1).inter (convex_po 2))
    (pos_inter (pos_inter (pos_ze 2) (pos_hyp 0 1 t)) (pos_po 1)) (pos_inter (pos_ze 1) (pos_po 2))
    (zero_notMem_po 1) (zero_notMem_po 2)
    ⟨![t, 1, 0], by simp [Bt, hyp, ze, po]⟩ ⟨![0, 0, 1], by simp [B', ze, po]⟩
    (K := zeS 2 ⊓ hypS 0 1 t) (K' := zeS 1)
    (fun v hv => Submodule.mem_inf.2 ⟨mem_zeS.2 hv.1.1, mem_hypS.2 hv.1.2⟩)
    (fun v hv => mem_zeS.2 hv.1) ?_ ?_
  · rw [eq_bot_iff]
    intro v hv
    simp only [Submodule.mem_inf, mem_hypS, zero_mul] at hv
    exact (Submodule.mem_bot ℝ).2 (eq_zero_of_coords (by rw [hv.1.2, hv.2, mul_zero]) hv.2 hv.1.1)
  · ext v
    simp only [quart, Bt, B', hyp, ze, po, mem_inter_iff, mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨![t * v 1, v 1, 0], ⟨⟨by simp, by simp⟩, by simpa⟩, ![v 0 - t * v 1, 0, v 2],
        ⟨by simp, by simpa⟩, ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨a, ⟨⟨ha2, ha0⟩, ha1⟩, b, ⟨hb1, hb2⟩, rfl⟩
      simp only [Pi.add_apply]
      constructor <;> linarith

theorem quart_distingue_Bt (t : ℝ) : EstDistingueS quartS (Submodule.span ℝ (Bt t)) :=
  ⟨_, (estConjugueS_iff isConvexPart_quartS).2
    (Or.inr (Or.inr ⟨Bt t, B', F_quartS ▸ coneDec_Bt t⟩))⟩

theorem span_Bt_injective : Function.Injective fun t : ℝ => Submodule.span ℝ (Bt t) := by
  intro t r h
  have ht : (![t, 1, 0] : V3) ∈ Submodule.span ℝ (Bt r) :=
    (show Submodule.span ℝ (Bt t) = Submodule.span ℝ (Bt r) from h) ▸
      Submodule.subset_span (by simp [Bt, hyp, ze, po])
  have := Submodule.span_le.2 (fun v hv => mem_hypS.2 hv.1.2 : Bt r ⊆ hypS 0 1 r) ht
  simpa [mem_hypS] using this

/-- Relative to the open quarter `w₁`, there are infinitely many distinguished subvarieties (the
pairs `{±(t e₁ + e₂)}`, `t ∈ ℝ`, each conjugate to the great circle `y = 0`). -/
theorem quart_distingues_infinite : {L : Submodule ℝ V3 | EstDistingueS quartS L}.Infinite :=
  Set.infinite_of_injective_forall_mem span_Bt_injective quart_distingue_Bt

/-- **The Corollary of Théorème 3 is false as printed**: `E = ℝ³` has dimension `n + 1 = 3`, the
open quarter `w₁` of `S(2)` is convex, open, of support `S(2)` and of empty noyau, and its
distinguished subvarieties are not the algebra of parts of any finite set (there are
infinitely many of them). -/
theorem not_corollaire_algebre_parties :
    ∃ w : Set (S 2), IsConvexPart w ∧ IsOpen w ∧ supportK w = univ ∧ noyau w = ∅ ∧
      ∀ (α : Type) [Finite α], IsEmpty (Set α ≃ {L : Submodule ℝ V3 // EstDistingueS w L}) := by
  refine ⟨quartS, isConvexPart_quartS, isOpen_quartS, supportK_quartS, noyau_quartS,
    fun α _ => ⟨fun e => ?_⟩⟩
  haveI : Finite {L : Submodule ℝ V3 // EstDistingueS quartS L} := Finite.of_equiv _ e
  exact quart_distingues_infinite (Set.finite_coe_iff.1 this)

/-! #### The half-open quarter `w₂ = {x ≥ 0, y > 0, z > 0}` of `S(2)`: Théorème 3 fails -/

/-- The cone of `w₂`. -/
def C2 : Set V3 := (nn 0 ∩ po 1) ∩ po 2

/-- **The convex `w₂ = s({x ≥ 0, y > 0, z > 0})` of `S(2)`**: convex, of support `S(2)`, of empty
noyau, and `F(w₂)` contains no line; not open. -/
def w2 : Set (S 2) := ofCone C2

theorem pos_C2 : IsPosCone C2 := pos_inter (pos_inter (pos_nn 0) (pos_po 1)) (pos_po 2)

theorem F_w2 : F w2 = C2 := F_ofCone_of_zero_notMem pos_C2 (zero_notMem_po 2)

theorem isConvexPart_w2 : IsConvexPart w2 :=
  isConvexPart_ofCone_of_cone (((convex_nn 0).inter (convex_po 1)).inter (convex_po 2)) pos_C2

theorem span_C2 : Submodule.span ℝ C2 = ⊤ := by
  refine span_eq_top_of_absorbing pos_C2 (u := ![1, 1, 1]) ⟨⟨by simp [nn], by simp [po]⟩,
    by simp [po]⟩ fun x => ⟨|x 0| + |x 1| + |x 2| + 1, by positivity, ⟨?_, ?_⟩, ?_⟩
  · simp only [nn, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_zero, mul_one]
    linarith [neg_abs_le (x 0), abs_nonneg (x 1), abs_nonneg (x 2)]
  · simp only [po, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_one]
    linarith [neg_abs_le (x 1), abs_nonneg (x 0), abs_nonneg (x 2)]
  · simp only [po, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one]
    linarith [neg_abs_le (x 2), abs_nonneg (x 1), abs_nonneg (x 0)]

theorem supportK_w2 : supportK w2 = univ := by
  rw [supportK, F_w2, span_C2, linearSubvariety_top_eq]

theorem noyau_w2 : noyau w2 = ∅ := by
  rw [noyau_eq isConvexPart_w2]
  refine eq_empty_of_forall_notMem fun m ⟨h, h'⟩ => ?_
  induction m using ind with
  | h M hM =>
  rw [neg_mk, mk_mem_iff_mem_F, F_w2] at h'
  rw [mk_mem_iff_mem_F, F_w2] at h
  have := h.2; have := h'.2
  simp only [po, mem_setOf_eq, Pi.neg_apply] at *
  linarith

/-- `F(w₂)` contains no line (so the added hypothesis of `conjugue_unique` holds). -/
theorem not_contientDroite_C2 : ¬ ContientDroite C2 := by
  rintro ⟨x, v, hv, h⟩
  apply hv
  have key : ∀ i : Fin 3, (∀ t : ℝ, 0 ≤ x i + t * v i) → v i = 0 := by
    intro i hi
    by_contra hvi
    have := hi (-(|x i| + 1) / v i)
    rw [div_mul_cancel₀ _ hvi] at this
    linarith [le_abs_self (x i)]
  refine eq_zero_of_coords (key 0 fun t => (h t).1.1) (key 1 fun t => ((h t).1.2).le)
    (key 2 fun t => ((h t).2).le)

/-- The half-open half-plane `{z = 0, x ≥ 0, y > 0}`. -/
def A1 : Set V3 := (ze 2 ∩ nn 0) ∩ po 1
/-- The half-open half-plane `{y = 0, x ≥ 0, z > 0}`. -/
def A2 : Set V3 := (ze 1 ∩ nn 0) ∩ po 2
/-- The ray of `e₂`. -/
def A5 : Set V3 := (ze 0 ∩ ze 2) ∩ po 1

theorem coneDec_A1_A3 : ConeDec C2 (Submodule.span ℝ A1) (Submodule.span ℝ A3) A1 A3 := by
  refine coneDec_mk (((convex_ze 2).inter (convex_nn 0)).inter (convex_po 1))
    (((convex_ze 0).inter (convex_ze 1)).inter (convex_po 2))
    (pos_inter (pos_inter (pos_ze 2) (pos_nn 0)) (pos_po 1))
    (pos_inter (pos_inter (pos_ze 0) (pos_ze 1)) (pos_po 2)) (zero_notMem_po 1) (zero_notMem_po 2)
    ⟨![0, 1, 0], by simp [A1, ze, nn, po]⟩ ⟨![0, 0, 1], by simp [A3, ze, po]⟩
    (K := zeS 2) (K' := zeS 0 ⊓ zeS 1) (fun v hv => mem_zeS.2 hv.1.1)
    (fun v hv => Submodule.mem_inf.2 ⟨mem_zeS.2 hv.1.1, mem_zeS.2 hv.1.2⟩) ?_ ?_
  · rw [eq_bot_iff]
    intro v hv
    simp only [Submodule.mem_inf, mem_hypS, zero_mul] at hv
    exact (Submodule.mem_bot ℝ).2 (eq_zero_of_coords hv.2.1 hv.2.2 hv.1)
  · ext v
    simp only [C2, A1, A3, ze, nn, po, mem_inter_iff, mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨![v 0, v 1, 0], ⟨⟨by simp, by simpa⟩, by simpa⟩, ![0, 0, v 2],
        ⟨⟨by simp, by simp⟩, by simpa⟩, ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨a, ⟨⟨ha2, ha0⟩, ha1⟩, b, ⟨⟨hb0, hb1⟩, hb2⟩, rfl⟩
      simp only [Pi.add_apply]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith

theorem coneDec_A2_A5 : ConeDec C2 (Submodule.span ℝ A2) (Submodule.span ℝ A5) A2 A5 := by
  refine coneDec_mk (((convex_ze 1).inter (convex_nn 0)).inter (convex_po 2))
    (((convex_ze 0).inter (convex_ze 2)).inter (convex_po 1))
    (pos_inter (pos_inter (pos_ze 1) (pos_nn 0)) (pos_po 2))
    (pos_inter (pos_inter (pos_ze 0) (pos_ze 2)) (pos_po 1)) (zero_notMem_po 2) (zero_notMem_po 1)
    ⟨![0, 0, 1], by simp [A2, ze, nn, po]⟩ ⟨![0, 1, 0], by simp [A5, ze, po]⟩
    (K := zeS 1) (K' := zeS 0 ⊓ zeS 2) (fun v hv => mem_zeS.2 hv.1.1)
    (fun v hv => Submodule.mem_inf.2 ⟨mem_zeS.2 hv.1.1, mem_zeS.2 hv.1.2⟩) ?_ ?_
  · rw [eq_bot_iff]
    intro v hv
    simp only [Submodule.mem_inf, mem_hypS, zero_mul] at hv
    exact (Submodule.mem_bot ℝ).2 (eq_zero_of_coords hv.2.1 hv.1 hv.2.2)
  · ext v
    simp only [C2, A2, A5, ze, nn, po, mem_inter_iff, mem_setOf_eq, Set.mem_add]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨![v 0, 0, v 2], ⟨⟨by simp, by simpa⟩, by simpa⟩, ![0, v 1, 0],
        ⟨⟨by simp, by simp⟩, by simpa⟩, ?_⟩
      ext i; fin_cases i <;> simp
    · rintro ⟨a, ⟨⟨ha1, ha0⟩, ha2⟩, b, ⟨⟨hb0, hb2⟩, hb1⟩, rfl⟩
      simp only [Pi.add_apply]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith

theorem w2_distingue_A1 : EstDistingueS w2 (Submodule.span ℝ A1) :=
  ⟨_, (estConjugueS_iff isConvexPart_w2).2 (Or.inr (Or.inr ⟨A1, A3, F_w2 ▸ coneDec_A1_A3⟩))⟩

theorem w2_distingue_A2 : EstDistingueS w2 (Submodule.span ℝ A2) :=
  ⟨_, (estConjugueS_iff isConvexPart_w2).2 (Or.inr (Or.inr ⟨A2, A5, F_w2 ▸ coneDec_A2_A5⟩))⟩

theorem e0_mem_inf : (![1, 0, 0] : V3) ∈ Submodule.span ℝ A1 ⊓ Submodule.span ℝ A2 := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : (![1, 1, 0] : V3) ∈ A1 := by simp [A1, ze, nn, po]
    have h2 : (![0, 1, 0] : V3) ∈ A1 := by simp [A1, ze, nn, po]
    have := Submodule.sub_mem _ (Submodule.subset_span (R := ℝ) h1) (Submodule.subset_span h2)
    convert this using 1
    ext i; fin_cases i <;> simp
  · have h1 : (![1, 0, 1] : V3) ∈ A2 := by simp [A2, ze, nn, po]
    have h2 : (![0, 0, 1] : V3) ∈ A2 := by simp [A2, ze, nn, po]
    have := Submodule.sub_mem _ (Submodule.subset_span (R := ℝ) h1) (Submodule.subset_span h2)
    convert this using 1
    ext i; fin_cases i <;> simp

theorem inf_le_zeS : Submodule.span ℝ A1 ⊓ Submodule.span ℝ A2 ≤ zeS 1 ⊓ zeS 2 :=
  le_inf (inf_le_right.trans (Submodule.span_le.2 fun _ hv => mem_zeS.2 hv.1.1))
    (inf_le_left.trans (Submodule.span_le.2 fun _ hv => mem_zeS.2 hv.1.1))

/-- The intersection of the two distinguished great circles `z = 0` and `y = 0` relative to
`w₂`, the pair `{±e₁}`, is not distinguished. -/
theorem w2_not_distingue_inf :
    ¬ EstDistingueS w2 (Submodule.span ℝ A1 ⊓ Submodule.span ℝ A2) := by
  set M := Submodule.span ℝ A1 ⊓ Submodule.span ℝ A2
  rintro ⟨L', h⟩
  rw [estConjugueS_iff isConvexPart_w2, F_w2, span_C2] at h
  have hM1 : ∀ v ∈ M, v 1 = 0 := fun v hv => mem_zeS.1 (Submodule.mem_inf.1 (inf_le_zeS hv)).1
  have hM2 : ∀ v ∈ M, v 2 = 0 := fun v hv => mem_zeS.1 (Submodule.mem_inf.1 (inf_le_zeS hv)).2
  rcases h with ⟨hM, -⟩ | ⟨hM, -⟩ | ⟨A, A', h⟩
  · have := hM1 ![0, 1, 0] (hM ▸ Submodule.mem_top)
    simp at this
  · have := e0_mem_inf
    rw [show Submodule.span ℝ A1 ⊓ Submodule.span ℝ A2 = M from rfl, hM, Submodule.mem_bot] at this
    have := congrFun this 0
    simp at this
  · have hc0 : (![0, 1, 1] : V3) ∈ C2 := by simp [C2, nn, po]
    rw [h.sum] at hc0
    obtain ⟨a, ha, a', ha', e⟩ := hc0
    have haM := h.subset ha
    have h1 := hM1 a haM
    have h2 := hM2 a haM
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    have e2 := congrFun e 2
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
    rcases lt_trichotomy (a 0) 0 with hs | hs | hs
    · -- `a' ∈ C₂`, so `a' = b + b'` and `b ∈ M ∩ L' = 0`
      have ha'C : a' ∈ C2 := ⟨⟨by simp only [nn, mem_setOf_eq]; linarith, by
        simp only [po, mem_setOf_eq]; linarith⟩, by simp only [po, mem_setOf_eq]; linarith⟩
      rw [h.sum] at ha'C
      obtain ⟨b, hb, b', hb', e'⟩ := ha'C
      have hbM : b ∈ M ⊓ L' := Submodule.mem_inf.2 ⟨h.subset hb, by
        rw [show b = a' - b' by rw [← e']; simp]
        exact L'.sub_mem (h.subset' ha') (h.subset' hb')⟩
      rw [h.disj, Submodule.mem_bot] at hbM
      exact h.zero (hbM ▸ hb)
    · exact h.zero (eq_zero_of_coords hs h1 h2 ▸ ha)
    · have hx : (1 / 2 : ℝ) • a + a' ∈ C2 := h.sum ▸ ⟨_, h.pos _ (by norm_num) _ ha, a', ha', rfl⟩
      have := hx.1.1
      simp only [nn, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith

/-- **Théorème 3 is false as printed**, even with the hypothesis that `F(w)` contains no line:
relative to the convex `w₂` of `S(2)` (support `S(2)`, empty noyau, no line in `F(w₂)`), the
great circles `z = 0` and `y = 0` are distinguished, and their intersection `{±e₁}` is not, so
the distinguished subvarieties are not closed under « inf l'intersection ». -/
theorem not_theoreme3 :
    ∃ w : Set (S 2), IsConvexPart w ∧ supportK w = univ ∧ noyau w = ∅ ∧
      ¬ ContientDroite (F w) ∧ ∃ L D : Submodule ℝ V3, EstDistingueS w L ∧ EstDistingueS w D ∧
        ¬ EstDistingueS w (L ⊓ D) ∧ linearSubvariety (L ⊓ D) = linearSubvariety L ∩ linearSubvariety D :=
  ⟨w2, isConvexPart_w2, supportK_w2, noyau_w2, F_w2 ▸ not_contientDroite_C2, _, _,
    w2_distingue_A1, w2_distingue_A2, w2_not_distingue_inf, (linearSubvariety_inter _ _).symm⟩

/-! #### The open `n`-simplex of `S(n)`: `n + 1` simple distinguished subvarieties -/

section Simplexe

variable {n : ℕ}

/-- The open positive orthant of `ℝⁿ⁺¹`. -/
def orthO (n : ℕ) : Set (Fin (n + 1) → ℝ) := {v | ∀ i, 0 < v i}

/-- **The open `n`-simplex** `s(orthO − O)` of `S(n)`. -/
def simplexO (n : ℕ) : Set (S n) := ofCone (orthO n)

theorem pos_orthO : IsPosCone (orthO n) := fun _ hc _ hv i => by
  simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hc (hv i)

theorem zero_notMem_orthO : (0 : Fin (n + 1) → ℝ) ∉ orthO n := fun h => by
  simpa using h 0

theorem F_simplexO : F (simplexO n) = orthO n := F_ofCone_of_zero_notMem pos_orthO zero_notMem_orthO

theorem convex_orthO : Convex ℝ (orthO n) := fun x hx y hy a b ha hb hab i => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact combo_pos (hx i) (hy i) ha hb hab

theorem isConvexPart_simplexO : IsConvexPart (simplexO n) :=
  isConvexPart_ofCone_of_cone convex_orthO pos_orthO

theorem isOpen_simplexO : IsOpen (simplexO n) := by
  rw [isOpen_iff_F, F_simplexO, orthO, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem span_orthO : Submodule.span ℝ (orthO n) = ⊤ := by
  refine span_eq_top_of_absorbing pos_orthO (u := fun _ => 1)
    (fun _ => one_pos) fun x => ⟨‖x‖ + 1, by positivity, fun i => ?_⟩
  have := norm_le_pi_norm x i
  rw [Real.norm_eq_abs] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  linarith [neg_abs_le (x i)]

theorem supportK_simplexO : supportK (simplexO n) = univ := by
  rw [supportK, F_simplexO, span_orthO, linearSubvariety_top_eq]

theorem noyau_simplexO : noyau (simplexO n) = ∅ := by
  rw [noyau_eq isConvexPart_simplexO]
  refine eq_empty_of_forall_notMem fun m ⟨h, h'⟩ => ?_
  induction m using ind with
  | h M hM =>
  rw [neg_mk, mk_mem_iff_mem_F, F_simplexO] at h'
  rw [mk_mem_iff_mem_F, F_simplexO] at h
  have := h 0; have := h' 0
  simp only [Pi.neg_apply] at *
  linarith

theorem not_contientDroite_orthO : ¬ ContientDroite (orthO n) := by
  rintro ⟨x, v, hv, h⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have := h (-(|x i| + 1) / v i) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
  rw [div_mul_cancel₀ _ hi] at this
  linarith [le_abs_self (x i)]

/-- **The hypotheses of `theoreme3` hold for the open `n`-simplex**: convex, open, of support
`S(n)`, of empty noyau, `F` containing no line. -/
theorem simplexO_hyps : IsConvexPart (simplexO n) ∧ IsOpen (simplexO n) ∧
    supportK (simplexO n) = univ ∧ noyau (simplexO n) = ∅ ∧ ¬ ContientDroite (F (simplexO n)) :=
  ⟨isConvexPart_simplexO, isOpen_simplexO, supportK_simplexO, noyau_simplexO,
    F_simplexO ▸ not_contientDroite_orthO⟩

/-- The open ray of `eᵢ`. -/
def rayO (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) := {v | (∀ j, j ≠ i → v j = 0) ∧ 0 < v i}
/-- The open face `{vᵢ = 0, vⱼ > 0 (j ≠ i)}`. -/
def faceO (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) := {v | v i = 0 ∧ ∀ j, j ≠ i → 0 < v j}

/-- The axis `ℝ eᵢ` as `{v | vⱼ = 0 (j ≠ i)}`. -/
def axeS (i : Fin (n + 1)) : Submodule ℝ (Fin (n + 1) → ℝ) where
  carrier := {v | ∀ j, j ≠ i → v j = 0}
  add_mem' hx hy j hj := by simp [hx j hj, hy j hj]
  zero_mem' j _ := rfl
  smul_mem' c x hx j hj := by simp [hx j hj]

theorem coneDec_rayO (i : Fin (n + 1)) (hi : ∃ j, j ≠ i) :
    ConeDec (orthO n) (Submodule.span ℝ (rayO i)) (Submodule.span ℝ (faceO i)) (rayO i)
      (faceO i) := by
  refine coneDec_mk (K := axeS i) (K' := LinearMap.ker (LinearMap.proj i)) ?_ ?_ ?_ ?_ ?_ ?_
    ⟨Pi.single i 1, fun j hj => by simp [hj], by simp⟩
    ⟨fun j => if j = i then 0 else 1, by simp, fun j hj => by simp [hj]⟩
    (fun v hv => hv.1) (fun v hv => by simpa using hv.1) ?_ ?_
  · intro x hx y hy a b ha hb hab
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [hx.1 j hj, hy.1 j hj]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact combo_pos hx.2 hy.2 ha hb hab
  · intro x hx y hy a b ha hb hab
    refine ⟨?_, fun j hj => ?_⟩
    · simp [hx.1, hy.1]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact combo_pos (hx.2 j hj) (hy.2 j hj) ha hb hab
  · intro c hc v hv
    exact ⟨fun j hj => by simp [hv.1 j hj], by simpa using mul_pos hc hv.2⟩
  · intro c hc v hv
    exact ⟨by simp [hv.1], fun j hj => by simpa using mul_pos hc (hv.2 j hj)⟩
  · exact fun h => by simpa using h.2
  · intro h
    obtain ⟨j, hj⟩ := hi
    simpa using h.2 j hj
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    rw [Submodule.mem_bot]
    ext j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · exact h1 j hj
  · ext v
    constructor
    · intro hv
      refine ⟨Pi.single i (v i), ⟨fun j hj => by simp [hj], by simpa using hv i⟩,
        Function.update v i 0, ⟨by simp, fun j hj => by simpa [hj] using hv j⟩, ?_⟩
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · rintro ⟨a, ha, b, hb, rfl⟩ j
      simp only [Pi.add_apply]
      by_cases hj : j = i
      · subst hj; rw [hb.1]; linarith [ha.2]
      · rw [ha.1 j hj]; linarith [hb.2 j hj]


theorem span_rayO_le (i : Fin (n + 1)) :
    Submodule.span ℝ (rayO i) ≤ Submodule.span ℝ {Pi.single i (1 : ℝ)} := by
  rw [Submodule.span_le]
  intro v hv
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  refine ⟨v i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, hv.1 j hj]

theorem single_mem_span_rayO (i : Fin (n + 1)) :
    Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (rayO i) :=
  Submodule.subset_span ⟨fun j hj => by simp [hj], by simp⟩

theorem span_rayO_eq (i : Fin (n + 1)) :
    Submodule.span ℝ (rayO i) = Submodule.span ℝ {Pi.single i (1 : ℝ)} :=
  le_antisymm (span_rayO_le i) (Submodule.span_le.2 (by
    simpa using single_mem_span_rayO i))

theorem simplexO_distingue (i : Fin (n + 1)) :
    EstDistingueS (simplexO n) (Submodule.span ℝ (rayO i)) := by
  by_cases hi : ∃ j, j ≠ i
  · exact ⟨_, (estConjugueS_iff isConvexPart_simplexO).2
      (Or.inr (Or.inr ⟨_, _, F_simplexO ▸ coneDec_rayO i hi⟩))⟩
  · push Not at hi
    refine ⟨⊥, (estConjugueS_iff isConvexPart_simplexO).2 (Or.inl ⟨?_, rfl⟩)⟩
    rw [F_simplexO, span_orthO, span_rayO_eq, eq_top_iff]
    intro v _
    rw [Submodule.mem_span_singleton]
    refine ⟨v i, ?_⟩
    ext j
    rw [hi j]
    simp

/-- The axis `ℝ eᵢ` is a simple distinguished subvariety of the open simplex. -/
theorem simplexO_estSimpleS (i : Fin (n + 1)) :
    EstSimpleS (simplexO n) (Submodule.span ℝ (rayO i)) := by
  have hne : (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) ≠ 0 := fun h => by
    simpa using congrFun h i
  refine ⟨simplexO_distingue i, fun h => hne ?_, fun M _ hM hle => ?_⟩
  · have := single_mem_span_rayO i
    rwa [h, Submodule.mem_bot] at this
  · rw [span_rayO_eq] at hle ⊢
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [finrank_span_singleton hne]
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hne] at h1
    have h2 : Module.finrank ℝ M ≠ 0 := fun h0 => hM (Submodule.finrank_eq_zero.1 h0)
    omega

theorem span_rayO_injective : Function.Injective fun i : Fin (n + 1) =>
    Submodule.span ℝ (rayO i) := by
  intro i j h
  by_contra hij
  have hi : Pi.single i (1 : ℝ) ∈ Submodule.span ℝ (rayO j) :=
    (show Submodule.span ℝ (rayO i) = Submodule.span ℝ (rayO j) from h) ▸ single_mem_span_rayO i
  have := (Submodule.span_le.2 (show rayO j ⊆ (axeS j : Set (Fin (n + 1) → ℝ)) from
    fun v hv => hv.1)) hi i hij
  simp at this

/-- **The open `n`-simplex** (« `(n+1)` au cas du `n`-simplexe ouvert de la sphère à `n`
dimensions »): it has exactly `n + 1` simple distinguished subvarieties. -/
theorem simplexO_simplesS_ncard : (simplesS (simplexO n)).ncard = n + 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := simplexO_hyps (n := n)
  obtain ⟨hfin, -, hle, -⟩ := corollaire_algebre_parties_projective h1 h2 h3 h4 h5
    (Module.finrank_fin_fun ℝ)
  refine le_antisymm hle ?_
  have hsub : Set.range (fun i : Fin (n + 1) => Submodule.span ℝ (rayO i)) ⊆
      simplesS (simplexO n) := by
    rintro _ ⟨i, rfl⟩; exact simplexO_estSimpleS i
  have := Set.ncard_le_ncard hsub hfin
  rwa [Set.ncard_range_of_injective span_rayO_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this

/-- **The transfer is not through `insert O F(w)`**: for `n ≥ 1`, the axis `ℝ eᵢ`, distinguished
relative to the open simplex (`simplexO_distingue`), is not a distinguished subspace (Déf. 3)
of the cone `insert O F(w)` (which meets `ℝ eᵢ` at `O` only); the affine statement applies to the
closed cone `K̄` instead (`estConjugueS_iff_affine`). -/
theorem simplexO_kPrime_not_estDistingue (hn : 1 ≤ n) (i : Fin (n + 1)) :
    ¬ EstDistingue (kPrime (simplexO n)) (Submodule.span ℝ (rayO i)) := by
  rintro ⟨L', hc, hconj⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ i := by
    by_cases h : i = 0
    · exact ⟨⟨1, by omega⟩, fun e => by subst h; simp [Fin.ext_iff] at e⟩
    · exact ⟨0, fun e => h e.symm⟩
  have hK : kPrime (simplexO n) ⊆ L' := by
    intro x hx
    rw [hconj] at hx
    obtain ⟨a, ⟨haL, haK⟩, b, ⟨hbL, -⟩, rfl⟩ := hx
    have ha0 : a = 0 := by
      rcases mem_insert_iff.1 haK with h | h
      · exact h
      · rw [F_simplexO] at h
        exfalso
        rw [SetLike.mem_coe, span_rayO_eq, Submodule.mem_span_singleton] at haL
        obtain ⟨c, rfl⟩ := haL
        have := h j
        simp [hj] at this
    show a + b ∈ L'
    rw [ha0, zero_add]; exact hbL
  have htop : L' = ⊤ := by
    rw [eq_top_iff, ← span_orthO, Submodule.span_le]
    exact fun x hx => hK (mem_insert_of_mem _ (F_simplexO (n := n) ▸ hx))
  rw [htop] at hc
  have hbot := hc.disjoint.eq_bot_of_le le_top
  have := single_mem_span_rayO (n := n) i
  rw [hbot, Submodule.mem_bot] at this
  simpa using congrFun this i

end Simplexe

/-! #### The open round cap of `S(2)`: a single simple distinguished subvariety -/

/-- The open round cone `{v₂ > 0, v₀² + v₁² < v₂²}`. -/
def rond : Set V3 := {v | 0 < v 2 ∧ v 0 ^ 2 + v 1 ^ 2 < v 2 ^ 2}

/-- **The open round cap** `s(rond − O)` of `S(2)`. -/
def capS : Set (S 2) := ofCone rond

theorem pos_rond : IsPosCone rond := fun c hc v hv => by
  simp only [rond, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
  refine ⟨mul_pos hc hv.1, ?_⟩
  have hc2 : 0 < c ^ 2 := by positivity
  nlinarith [hv.2]

theorem zero_notMem_rond : (0 : V3) ∉ rond := fun h => by simp [rond] at h

theorem F_capS : F capS = rond := F_ofCone_of_zero_notMem pos_rond zero_notMem_rond

theorem convex_rond : Convex ℝ rond := by
  intro x hx y hy a b ha hb hab
  simp only [rond, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  obtain ⟨hx2, hx⟩ := hx
  obtain ⟨hy2, hy⟩ := hy
  have h1 : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have h2 : (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) < (x 2 * y 2) ^ 2 := by
    rw [mul_pow]
    exact mul_lt_mul'' hx hy (by positivity) (by positivity)
  have h3 : x 0 * y 0 + x 1 * y 1 < x 2 * y 2 :=
    lt_of_abs_lt (abs_lt_of_sq_lt_sq (h1.trans_lt h2) (by positivity))
  refine ⟨combo_pos hx2 hy2 ha hb hab, ?_⟩
  rcases ha.lt_or_eq with ha' | rfl
  · nlinarith [mul_pos ha' ha', mul_nonneg hb hb, mul_nonneg ha'.le hb, mul_pos ha' ha',
      mul_le_mul_of_nonneg_left hy.le (mul_nonneg hb hb), mul_lt_mul_of_pos_left hx (mul_pos ha' ha'),
      mul_le_mul_of_nonneg_left h3.le (mul_nonneg ha'.le hb)]
  · rw [zero_add] at hab; subst hab; simpa using hy

theorem isConvexPart_capS : IsConvexPart capS := isConvexPart_ofCone_of_cone convex_rond pos_rond

theorem isOpen_capS : IsOpen capS := by
  rw [isOpen_iff_F, F_capS]
  exact (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
      ((continuous_apply 2).pow 2))

theorem span_rond : Submodule.span ℝ rond = ⊤ := by
  refine span_eq_top_of_absorbing pos_rond (u := ![0, 0, 1]) ⟨by simp, by simp⟩
    fun x => ⟨|x 0| + |x 1| + |x 2| + 1, by positivity, ?_⟩
  simp only [rond, mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, mul_zero, add_zero, mul_one]
  have h0 := sq_abs (x 0)
  have h1 := sq_abs (x 1)
  have a0 := abs_nonneg (x 0)
  have a1 := abs_nonneg (x 1)
  have a2 := neg_abs_le (x 2)
  refine ⟨by linarith, ?_⟩
  nlinarith

theorem supportK_capS : supportK capS = univ := by
  rw [supportK, F_capS, span_rond, linearSubvariety_top_eq]

theorem noyau_capS : noyau capS = ∅ := by
  rw [noyau_eq isConvexPart_capS]
  refine eq_empty_of_forall_notMem fun m ⟨h, h'⟩ => ?_
  induction m using ind with
  | h M hM =>
  rw [neg_mk, mk_mem_iff_mem_F, F_capS] at h'
  rw [mk_mem_iff_mem_F, F_capS] at h
  have := h.1; have := h'.1
  simp only [Pi.neg_apply] at *
  linarith

theorem not_contientDroite_rond : ¬ ContientDroite rond := by
  rintro ⟨x, v, hv, h⟩
  have hv2 : v 2 = 0 := by
    by_contra hv2
    have := (h (-(|x 2| + 1) / v 2)).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [div_mul_cancel₀ _ hv2] at this
    linarith [le_abs_self (x 2)]
  have hb : ∀ t : ℝ, (x 0 + t * v 0) ^ 2 + (x 1 + t * v 1) ^ 2 < x 2 ^ 2 := fun t => by
    have := (h t).2
    simpa [hv2] using this
  have big : ∀ a b : ℝ, 0 ≤ a → |x 2| + 1 ≤ b → b ^ 2 + a < x 2 ^ 2 → False := by
    intro a b ha hb hlt
    have := sq_abs (x 2)
    nlinarith [abs_nonneg (x 2)]
  have key0 : v 0 = 0 := by
    by_contra hvi
    have h' := hb ((|x 0| + |x 2| + 1) / v 0)
    rw [div_mul_cancel₀ _ hvi] at h'
    exact big _ (x 0 + (|x 0| + |x 2| + 1)) (sq_nonneg _) (by linarith [neg_abs_le (x 0)]) h'
  have key1 : v 1 = 0 := by
    by_contra hvi
    have h' := hb ((|x 1| + |x 2| + 1) / v 1)
    rw [div_mul_cancel₀ _ hvi, add_comm] at h'
    exact big _ (x 1 + (|x 1| + |x 2| + 1)) (sq_nonneg _) (by linarith [neg_abs_le (x 1)]) h'
  exact hv (eq_zero_of_coords key0 key1 hv2)

/-- A point `a` with `a + s a' ∈ C` for all `s > 0` lies in the closure of `C`. -/
theorem mem_closure_of_add_smul {C : Set V3} {a a' : V3} (h : ∀ s : ℝ, 0 < s → a + s • a' ∈ C) :
    a ∈ closure C := by
  have ht : Tendsto (fun s : ℝ => a + s • a') (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun s : ℝ => a + s • a') (𝓝 0) (𝓝 (a + (0 : ℝ) • a')) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact h s hs

/-- In a cone decomposition of the round cone, the points of `A'` lie on the surface. -/
theorem coneDec_rond_surface {L L' : Submodule ℝ V3} {A A' : Set V3}
    (h : ConeDec rond L L' A A') {y : V3} (hy : y ∈ A') :
    0 < y 2 ∧ y 0 ^ 2 + y 1 ^ 2 = y 2 ^ 2 := by
  have hc := h.isCompl span_rond
  obtain ⟨a, ha⟩ := h.ne
  have hcl : y ∈ closure rond := mem_closure_of_add_smul fun s hs => by
    rw [h.sum]; exact ⟨s • a, h.pos s hs a ha, y, hy, add_comm _ _⟩
  have hS : closure rond ⊆ {v : V3 | 0 ≤ v 2 ∧ v 0 ^ 2 + v 1 ^ 2 ≤ v 2 ^ 2} := by
    refine closure_minimal (fun v hv => ⟨hv.1.le, hv.2.le⟩) ?_
    exact (isClosed_le continuous_const (continuous_apply 2)).inter
      (isClosed_le (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
        ((continuous_apply 2).pow 2))
  obtain ⟨h2, hle⟩ := hS hcl
  have hnot : y ∉ rond := by
    intro hyC
    have := (h.projection_mem hc hyC).1
    rw [Submodule.projection_apply_of_mem_right hc (h.subset' hy)] at this
    exact h.zero this
  have hy0 : y ≠ 0 := fun e => h.zero' (e ▸ hy)
  rcases h2.lt_or_eq with h2 | h2
  · refine ⟨h2, le_antisymm hle ?_⟩
    by_contra hlt
    exact hnot ⟨h2, lt_of_not_ge hlt⟩
  · exfalso
    rw [← h2] at hle
    have e0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have e1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact hy0 (eq_zero_of_coords e0 e1 h2.symm)

/-- In a cone decomposition of the round cone, the second subspace has dimension `≤ 1`
(the surface of the cone contains no plane sector: strict convexity). -/
theorem coneDec_rond_finrank {L L' : Submodule ℝ V3} {A A' : Set V3}
    (h : ConeDec rond L L' A A') : Module.finrank ℝ L' ≤ 1 := by
  obtain ⟨p, hp⟩ := h.ne'
  have hp0 : p ≠ 0 := fun e => h.zero' (e ▸ hp)
  by_cases hall : ∀ q ∈ A', q ∈ Submodule.span ℝ {p}
  · rw [← h.span']
    calc Module.finrank ℝ (Submodule.span ℝ A') ≤ Module.finrank ℝ (Submodule.span ℝ {p}) :=
          Submodule.finrank_mono (Submodule.span_le.2 hall)
      _ = 1 := finrank_span_singleton hp0
  · exfalso
    push Not at hall
    obtain ⟨q, hq, hqp⟩ := hall
    obtain ⟨hp2, hps⟩ := coneDec_rond_surface h hp
    obtain ⟨hq2, hqs⟩ := coneDec_rond_surface h hq
    obtain ⟨-, hpqs⟩ := coneDec_rond_surface h (add_mem_of_cone h.convex' h.pos' hp hq)
    simp only [Pi.add_apply] at hpqs
    have hz : (p 0 * q 2 - q 0 * p 2) ^ 2 + (p 1 * q 2 - q 1 * p 2) ^ 2 = 0 := by
      linear_combination (q 2 ^ 2 + p 2 * q 2) * hps + (p 2 ^ 2 + p 2 * q 2) * hqs -
        (p 2 * q 2) * hpqs
    have s0 := sq_nonneg (p 0 * q 2 - q 0 * p 2)
    have s1 := sq_nonneg (p 1 * q 2 - q 1 * p 2)
    have z0 : p 0 * q 2 - q 0 * p 2 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith)
    have z1 : p 1 * q 2 - q 1 * p 2 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith)
    apply hqp
    rw [Submodule.mem_span_singleton]
    refine ⟨q 2 / p 2, ?_⟩
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; field_simp; linarith
    · simp only [Fin.mk_one, Fin.isValue]; field_simp; linarith
    · simp only [Fin.reduceFinMk, Fin.isValue]; field_simp

/-- The round cone has no nontrivial cone decomposition. -/
theorem not_coneDec_rond {L L' : Submodule ℝ V3} {A A' : Set V3} (h : ConeDec rond L L' A A') :
    False := by
  have hc := h.isCompl span_rond
  have h' : ConeDec rond L' L A' A := ⟨h.convex', h.convex, h.pos', h.pos, h.zero', h.zero, h.ne',
    h.ne, h.span', h.span, by rw [inf_comm]; exact h.disj, by rw [h.sum, add_comm]⟩
  have h1 := coneDec_rond_finrank h
  have h2 := coneDec_rond_finrank h'
  have := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at this
  omega

theorem capS_distingue_iff {M : Submodule ℝ V3} : EstDistingueS capS M ↔ M = ⊥ ∨ M = ⊤ := by
  constructor
  · rintro ⟨L', h⟩
    rw [estConjugueS_iff isConvexPart_capS, F_capS, span_rond] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨A, A', h⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact (not_coneDec_rond h).elim
  · rintro (rfl | rfl)
    · exact ⟨⊤, (estConjugueS_iff isConvexPart_capS).2
        (Or.inr (Or.inl ⟨rfl, by rw [F_capS, span_rond]⟩))⟩
    · exact ⟨⊥, (estConjugueS_iff isConvexPart_capS).2
        (Or.inl ⟨by rw [F_capS, span_rond], rfl⟩)⟩

/-- **The open round cap** (« `1` correspond au cas où il n'existe pas de décomposition non
triviale »): it satisfies the hypotheses of `theoreme3`, its distinguished subvarieties are `∅`
and `S(2)`, and `S(2)` is its only simple one. -/
theorem capS_simplesS : (IsConvexPart capS ∧ IsOpen capS ∧ supportK capS = univ ∧
    noyau capS = ∅ ∧ ¬ ContientDroite (F capS)) ∧ simplesS capS = {⊤} ∧
    (simplesS capS).ncard = 1 := by
  have hS : simplesS capS = {⊤} := by
    ext M
    simp only [simplesS, EstSimpleS, mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hM, hne, -⟩
      exact (capS_distingue_iff.1 hM).resolve_left hne
    · rintro rfl
      refine ⟨capS_distingue_iff.2 (Or.inr rfl), ?_, fun N hN hN0 _ =>
        (capS_distingue_iff.1 hN).resolve_left hN0⟩
      intro h
      have : (![0, 0, 1] : V3) ∈ (⊥ : Submodule ℝ V3) := h ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at this
      simpa using congrFun this 2
  exact ⟨⟨isConvexPart_capS, isOpen_capS, supportK_capS, noyau_capS,
    F_capS ▸ not_contientDroite_rond⟩, hS, by rw [hS, Set.ncard_singleton]⟩

end BooleProjectifInstance

end Benzecri
