import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-!
# `Benzecri.Chapter3.Sommes` — sums of convex sets (Chapter 3 § 2, Déf. 1, Remarques 1–3, Prop. 1)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal pp. 262–264; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR; Remarque 2
checked here against the page image of p. 264). Target T-bz-c3-sommes.

* **`bzdef:c3s2d1_somme_convexes`** — `benzecri1960_ch3.tex:299` (Déf. 1, l.299–309):
  `Benzecri.IsSommeConvexes`, over `Benzecri.IsIsoConvexes` (« isomorphisme … pour les structures
  affines »: a bijection which, with its inverse, preserves convex combinations); proved to be
  exactly « `p` bijective from `∏ V_i` onto `W` » (`isSommeConvexes_iff_bijOn`); the components
  `Benzecri.composante` (`IsSommeConvexes.composante_spec`). Instances: `[0,1]²` is the sum of its
  two sides (`exemple_carre_somme`); the closed unit disc of `ℝ²` is the sum of no two segments
  (`disque_non_somme_segments`), not even their Minkowski sum (`disque_ne_somme_segments`).
* `bzrem:c3s2r1_somme_classes` — `benzecri1960_ch3.tex:312` (Remarque 1, l.312–320), NOT marked:
  `KE`, `KModE` (= `K(E)/E`), `classe`, `SommeClasses`; first assertion `remarque1_somme_unique`
  (as printed); second `remarque1_famille` (needs `n ≥ 1`: `not_remarque1_famille_fin_zero`);
  « une infinité de façons si n ≠ 1 » `remarque1_infinite` (needs two indices, `E ≠ 0`, `W'`
  nonempty: `not_remarque1_infinite_vide`, `not_remarque1_famille_fin_zero`); instances
  `exemple_carre_classes`, `exemple_carre_infinite`.
* **`bzprop:c3s2p1_decomposition_origine`** — `benzecri1960_ch3.tex:324` (Prop. 1, l.324–338):
  `prop1_decomposition_origine`, any finite index set (`n = 0` included), no added hypothesis.
* `bzrem:c3s2r2_somme_infinie` — `benzecri1960_ch3.tex:348` (Remarque 2, l.348–356), NOT marked (a
  reading): `IsSommeInfinie` (the sum is a bijection from the finitely supported families onto
  `W`), the literal wording `IsSommeInfinieTexte`; `isSommeInfinie_iff_texte` (the reading = the
  wording + « every finite sum of components lies in `W` »),
  `isSommeInfinieTexte_not_isSommeConvexes` (the wording alone disagrees with Déf. 1 for a finite
  `I`), `isSommeInfinie_iff_isSommeConvexes` (the reading agrees with Déf. 1 for a finite `I`).
* **`bzrem:c3s2r3_somme_directe`** — `benzecri1960_ch3.tex:359` (Remarque 3, l.359–363):
  `remarque3` (Déf. 1, any subspace `W`: `iSupIndep ∧ ⨆ = W`), `remarque3_somme_directe`
  (`W = E`: Mathlib's `DirectSum.IsInternal`), `remarque3_infinie`,
  `remarque3_somme_directe_infinie`, `remarque3_somme_directe_texte` (any `I`, in the reading and
  in the literal wording of Remarque 2).

> **Déf. 1.** Soient $E$ un espace vectoriel, $W$ un convexe de $E$, $V_i$ ($i\in I$) une famille
> finie de convexes de $E$, $p$ l'application de $\prod_{i\in I}V_i$ dans $E$ défini par
> $p(\{x_i\}_{i\in I})=\sum_{i\in I}x_i$, $W$ est dit *somme des convexes $V_i$* si $p$ est un
> isomorphisme de $\prod_{i\in I}V_i$ sur $W$ (pour les structures affines). […] Si $x\in W$,
> $x_i\in V_i$, $x=\sum x_i$, nous dirons que $x_i$ est la *composante* de $x$ dans $V_i$
>
> **Remarque.** $E$ opère par translation sur l'ensemble $K(E)$ des parties convexes de $E$; on
> peut définir le quotient $K(E)/E$; nous dirons qu'une classe $w\in K(E)/E$ est somme de $n$
> classes $v_i$ si l'on peut trouver $W$, $V_i$ de classes $w$, $v_i$ tels que $W$ soit la somme
> des $V_i$ : dans ce cas, à tout système de $n$ convexes $V'_i$ de classes $v_i$ correspond un
> convexe et un seul $W'$ de classe $w$, qui en est la somme; à tout convexe $W'$ de classe $w$, on
> peut (et ce d'une infinité de façons si $n\neq 1$) faire correspondre une famille de $n$
> convexes $V'_i$ de classe $v_i$ dont $W'$ soit la somme.
>
> **Proposition 1.** Soient $w$, $v_i\in K(E)/E$; $\sum_{i=1}^{n}v_i=w$ et $W$ de classe $w$
> contenant l'origine de $E$; alors il existe un système et un seul de $n$ convexes $V_i$ de classes
> $v_i$ contenant chacun l'origine, et tels que $W=\sum_{i=1}^{n}V_i$.
>
> **Remarque.** Pour $I$ infini, on peut encore définir la notion de convexe $W$ somme d'une
> famillle de convexes $V_i$ ($i\in I$) : on supposera que $W$ et les $V_i$ contiennent l'origine,
> et l'on dira que $W=\sum_{i\in I}V_i$ si tout $x\in W$ s'écrit d'une façon et d'une seule comme
> une somme finie, $x=\sum_{i\in N\subset I}x_i$ $(x\neq 0)$ (où $N$ désigne une partie finie de
> $I$). La composante de $x$ dans $V_j$ ($j\notin N$) est $0$.
>
> **Remarque.** Soient $W=E$, $V_i=E_i$ sous-espace vectoriel de $E$, $W=\sum V_i$ au sens
> ci-dessus défini : alors on a $E=\sum E_i$, somme directe des $E_i$, *pour les sous-espaces
> vectoriels la notion de somme de convexes coïncide avec celle de somme directe ordinaire*.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E` un espace vectoriel (real, Benzécri's standing setting) | ✓ carried: any real vector space, any dimension, no topology |
| Déf. 1: `W`, `V_i` convexes, `I` finie | ✓ carried (`Fintype I`, any `I`, `I = ∅` included) |
| Déf. 1: « isomorphisme … (pour les structures affines) » | ✓ carried in the reading `IsIsoConvexes` (see questions); proved equivalent to bijectivity, so any reading between « bijection » and « affine bijection with affine inverse » gives the same notion |
| Rem. 1: `K(E)` the convex parts, `E` acting by translation | ✓ carried: `KE E = {s // Convex ℝ s}` (the empty part included), `AddAction E (KE E)`, `KModE E` its orbit quotient |
| Rem. 1, second assertion: none on `n` | ⚠ strengthened: `[Nonempty I]` (`n ≥ 1`); false for `n = 0` (`not_remarque1_famille_fin_zero`) |
| Rem. 1, « infinité de façons si n ≠ 1 » | ⚠ strengthened: two distinct indices (`n ≥ 2`), `Nontrivial E`, `W'` nonempty; false for `n = 0` and for empty convexes (counterexamples above), and for `E = 0` (argued: `K(0)` has two elements) |
| Prop. 1: `∑ v_i = w`, `W` of class `w`, `0 ∈ W` | ✓ carried, nothing added, any finite `I` |
| Rem. 2: `W`, `V_i` contain the origin | ✓ carried |
| Rem. 3: `W = E`, `V_i = E_i` subspaces | ⚠ weakened: any subspace `W` (`remarque3`, `remarque3_infinie`); `W = E` gives `DirectSum.IsInternal` |

## SCOPE (disclosed)

* Remarque 2 is a definition whose wording (« tout x ∈ W s'écrit d'une façon et d'une seule comme
  une somme finie … (x ≠ 0) », checked on the scan) omits that every finite sum of components lies
  in `W`; read literally it disagrees with Déf. 1 for a finite `I`
  (`isSommeInfinieTexte_not_isSommeConvexes`: `W = [0,1]`, `V = [0,2]`). The reading taken,
  `IsSommeInfinie`, is the wording plus that condition (`isSommeInfinie_iff_texte`, no other
  difference, the case `x = 0` included) and agrees with Déf. 1 when `I` is finite. Uniqueness of
  « une somme finie » is read as uniqueness of the finitely supported family (the components off
  `N` are `0`, as the last sentence says). « (x ≠ 0) » might instead say that the terms `x_i` are
  nonzero; the counterexample `W = [0,1]`, `V = [0,2]` (one index, the term `x` itself nonzero for
  `x ≠ 0`) meets that reading of the wording too, so the finding holds under both. Remarque 3 holds
  in both readings.
* Remarque 1 is proved in its strongest true form; its printed form fails only in degenerate cases
  (`n = 0`, empty convexes, `E = 0`), which the two `not_` theorems exhibit (the `E = 0` case is
  argued, not formalized).
* Prop. 1's printed proof asserts without argument that the translates `V'_i − x'_i` are the only
  systems through the origin; `subset_of_translate_somme` supplies the argument (a midpoint
  comparison of two decompositions of `y/2`), with no hypothesis beyond the statement's.
* `[sic]`s of the transcription (« x'_i ∈ V_i », « v_t », « famillle ») are misprints: read as the
  comments say.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function
open scoped Pointwise

namespace Benzecri

section Sommes

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Déf. 1 -/

/-- An isomorphism of convex sets « pour les structures affines » (Déf. 1): a bijection `f` of `A`
onto `B` such that `f` and its inverse `invFunOn f A` preserve convex combinations of two points
(the affine structure of a convex set). -/
def IsIsoConvexes {F G : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (A : Set F) (B : Set G) (f : F → G) : Prop :=
  Set.BijOn f A B ∧
  (∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) = (1 - t) • f x + t • f y) ∧
  (∀ u ∈ B, ∀ v ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      invFunOn f A ((1 - t) • u + t • v) =
        (1 - t) • invFunOn f A u + t • invFunOn f A v)

/-- **Déf. 1.** `W` is the sum of the convex sets `V i` (`I` finite): `W` and the `V i` are convex
and `p : ∏ V_i → W`, `p({x_i}) = ∑ x_i`, is an isomorphism for the affine structures. -/
def IsSommeConvexes {I : Type*} [Fintype I] (W : Set E) (V : I → Set E) : Prop :=
  Convex ℝ W ∧ (∀ i, Convex ℝ (V i)) ∧
    IsIsoConvexes (Set.univ.pi V) W (fun x : I → E => ∑ i, x i)

/-- A linear map which is a bijection of a convex set onto a set is an isomorphism for the
affine structures. -/
theorem isIsoConvexes_of_linear {F G : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup G]
    [Module ℝ G] {A : Set F} {B : Set G} (f : F →ₗ[ℝ] G) (hA : Convex ℝ A)
    (h : Set.BijOn f A B) : IsIsoConvexes A B f := by
  refine ⟨h, fun x _ y _ t _ _ => by simp [map_add, map_smul], ?_⟩
  intro u hu v hv t ht0 ht1
  have hu' := h.surjOn hu
  have hv' := h.surjOn hv
  have hz : (1 - t) • invFunOn f A u + t • invFunOn f A v ∈ A :=
    hA (invFunOn_mem hu') (invFunOn_mem hv') (by linarith) ht0 (by ring)
  have hfz : f ((1 - t) • invFunOn f A u + t • invFunOn f A v) = (1 - t) • u + t • v := by
    simp only [map_add, map_smul, invFunOn_eq hu', invFunOn_eq hv']
  have hw : (1 - t) • u + t • v ∈ f '' A := ⟨_, hz, hfz⟩
  exact h.injOn (invFunOn_mem hw) hz ((invFunOn_eq hw).trans hfz.symm)

/-- The map `p` of Déf. 1, `p({x_i}) = ∑ x_i`, as a linear map. -/
def sommeP (I : Type*) [Fintype I] (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (I → E) →ₗ[ℝ] E where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

theorem sommeP_apply {I : Type*} [Fintype I] (x : I → E) : sommeP I E x = ∑ i, x i := rfl

/-- Déf. 1 unfolded: `W` is the sum of the `V i` iff the `V i` are convex and `p` is a bijection
of `∏ V_i` onto `W` (the convexity of `W` and the affinity of `p` and of its inverse follow). -/
theorem isSommeConvexes_iff_bijOn {I : Type*} [Fintype I] (W : Set E) (V : I → Set E) :
    IsSommeConvexes W V ↔
      (∀ i, Convex ℝ (V i)) ∧ Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi V) W := by
  constructor
  · rintro ⟨-, hV, h, -⟩
    exact ⟨hV, h⟩
  · rintro ⟨hV, h⟩
    have hpi : Convex ℝ (Set.univ.pi V) := convex_pi fun i _ => hV i
    refine ⟨?_, hV, isIsoConvexes_of_linear (sommeP I E) hpi h⟩
    rw [← h.image_eq]
    exact hpi.linear_image (sommeP I E)

/-- Déf. 1: the component of `x` in `V i`. -/
noncomputable def composante {I : Type*} [Fintype I] (V : I → Set E) (x : E) (i : I) : E :=
  invFunOn (fun y : I → E => ∑ j, y j) (Set.univ.pi V) x i

theorem IsSommeConvexes.composante_spec {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (h : IsSommeConvexes W V) {x : E} (hx : x ∈ W) :
    (∀ i, composante V x i ∈ V i) ∧ ∑ i, composante V x i = x ∧
      ∀ y : I → E, (∀ i, y i ∈ V i) → ∑ i, y i = x → y = composante V x := by
  obtain ⟨-, h⟩ := (isSommeConvexes_iff_bijOn W V).1 h
  have hx' := h.surjOn hx
  have hm : invFunOn (fun y : I → E => ∑ j, y j) (Set.univ.pi V) x ∈ Set.univ.pi V :=
    invFunOn_mem hx'
  have he : ∑ j, invFunOn (fun y : I → E => ∑ j, y j) (Set.univ.pi V) x j = x :=
    invFunOn_eq hx'
  refine ⟨fun i => hm i trivial, he, fun y hy hyx => ?_⟩
  exact h.injOn (fun i _ => hy i) hm (hyx.trans he.symm)

/-! ### Remarque 1: classes modulo translation -/

/-- `K(E)`, the set of convex parts of `E` (Remarque 1; the empty part included). -/
def KE (E : Type*) [AddCommGroup E] [Module ℝ E] : Type _ := {s : Set E // Convex ℝ s}

instance : AddAction E (KE E) where
  vadd a s := ⟨a +ᵥ s.1, s.2.vadd a⟩
  zero_vadd s := Subtype.ext (zero_vadd E s.1)
  add_vadd a b s := Subtype.ext (add_vadd a b s.1)

theorem KE.coe_vadd (a : E) (s : KE E) : (a +ᵥ s).1 = a +ᵥ s.1 := rfl

/-- `K(E)/E`, the quotient of `K(E)` by the translations of `E` (Remarque 1). -/
abbrev KModE (E : Type*) [AddCommGroup E] [Module ℝ E] : Type _ :=
  Quotient (AddAction.orbitRel E (KE E))

/-- The class of a convex part. -/
def classe (s : KE E) : KModE E := Quotient.mk _ s

theorem classe_eq_iff (s t : KE E) : classe s = classe t ↔ ∃ a : E, a +ᵥ s.1 = t.1 := by
  unfold classe
  rw [Quotient.eq, AddAction.orbitRel_apply]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    rw [← ha]
    show -a +ᵥ (a +ᵥ t.1) = t.1
    exact neg_vadd_vadd a t.1
  · rintro ⟨a, ha⟩
    refine ⟨-a, Subtype.ext ?_⟩
    show -a +ᵥ t.1 = s.1
    rw [← ha]
    exact neg_vadd_vadd a s.1

theorem classe_vadd (a : E) (s : KE E) : classe (a +ᵥ s) = classe s :=
  (classe_eq_iff _ _).2 ⟨-a, neg_vadd_vadd a s.1⟩

omit [Module ℝ E] in
theorem mem_vadd_iff_sub_mem {a x : E} {s : Set E} : x ∈ a +ᵥ s ↔ x - a ∈ s := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]

omit [Module ℝ E] in
/-- Translating each `V i` by `a i` translates their sum by `∑ a i`. -/
theorem bijOn_vadd {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (h : Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi V) W) (a : I → E) :
    Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi fun i => a i +ᵥ V i)
      ((∑ i, a i) +ᵥ W) := by
  have hmem : ∀ x : I → E, x ∈ Set.univ.pi (fun i => a i +ᵥ V i) ↔ x - a ∈ Set.univ.pi V := by
    intro x
    simp only [Set.mem_univ_pi, mem_vadd_iff_sub_mem, Pi.sub_apply]
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · rw [mem_vadd_iff_sub_mem, ← Finset.sum_sub_distrib]
    exact h.mapsTo ((hmem x).1 hx)
  · have hxy' : ∑ i, x i = ∑ i, y i := hxy
    have := h.injOn ((hmem x).1 hx) ((hmem y).1 hy)
      (by simp only [Pi.sub_apply, Finset.sum_sub_distrib]; rw [hxy'])
    simpa using this
  · rw [mem_vadd_iff_sub_mem] at hz
    obtain ⟨x, hx, hxz⟩ := h.surjOn hz
    refine ⟨x + a, (hmem _).2 (by simpa using hx), ?_⟩
    have hxz' : ∑ i, x i = z - ∑ i, a i := hxz
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hxz']
    abel

/-- Remarque 1: the class `w` is the sum of the classes `v i` if there are `W`, `V i` of classes
`w`, `v i` with `W` the sum of the `V i` (Déf. 1). -/
def SommeClasses {I : Type*} [Fintype I] (w : KModE E) (v : I → KModE E) : Prop :=
  ∃ W : KE E, ∃ V : I → KE E, classe W = w ∧ (∀ i, classe (V i) = v i) ∧
    IsSommeConvexes W.1 (fun i => (V i).1)

/-- Remarque 1, first assertion: to every system `V'` of classes `v i` corresponds one and only one
`W'` of class `w` which is its sum. As printed. -/
theorem remarque1_somme_unique {I : Type*} [Fintype I] {w : KModE E} {v : I → KModE E}
    (h : SommeClasses w v) (V' : I → KE E) (hV' : ∀ i, classe (V' i) = v i) :
    ∃! W' : KE E, classe W' = w ∧ IsSommeConvexes W'.1 (fun i => (V' i).1) := by
  obtain ⟨W, V, hWw, hVv, hS⟩ := h
  rw [isSommeConvexes_iff_bijOn] at hS
  have : ∀ i, ∃ a : E, a +ᵥ (V i).1 = (V' i).1 :=
    fun i => (classe_eq_iff _ _).1 ((hVv i).trans (hV' i).symm)
  choose a ha using this
  refine ⟨(∑ i, a i) +ᵥ W, ⟨by rw [classe_vadd, hWw], ?_⟩, ?_⟩
  · rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun i => (V' i).2, ?_⟩
    have hb := bijOn_vadd hS.2 a
    have e : (fun i => a i +ᵥ (V i).1) = fun i => (V' i).1 := funext ha
    rw [e] at hb
    exact hb
  · rintro W'' ⟨-, hW''⟩
    rw [isSommeConvexes_iff_bijOn] at hW''
    apply Subtype.ext
    have hb := bijOn_vadd hS.2 a
    have e : (fun i => a i +ᵥ (V i).1) = fun i => (V' i).1 := funext ha
    rw [e] at hb
    rw [← hW''.2.image_eq, hb.image_eq]
    rfl

/-- Remarque 1, second assertion: every `W'` of class `w` is the sum of a family of classes `v i`.
Needs `n ≥ 1` (`[Nonempty I]`): see `not_remarque1_famille_fin_zero`. -/
theorem remarque1_famille {I : Type*} [Fintype I] [Nonempty I] {w : KModE E} {v : I → KModE E}
    (h : SommeClasses w v) (W' : KE E) (hW' : classe W' = w) :
    ∃ V' : I → KE E, (∀ i, classe (V' i) = v i) ∧ IsSommeConvexes W'.1 (fun i => (V' i).1) := by
  classical
  obtain ⟨W, V, hWw, hVv, hS⟩ := h
  rw [isSommeConvexes_iff_bijOn] at hS
  obtain ⟨b, hb⟩ := (classe_eq_iff W W').1 (hWw.trans hW'.symm)
  obtain ⟨i₀⟩ := ‹Nonempty I›
  let a : I → E := Pi.single i₀ b
  have hsum : ∑ i, a i = b := Fintype.sum_pi_single' i₀ b
  refine ⟨fun i => a i +ᵥ V i, fun i => by rw [classe_vadd, hVv], ?_⟩
  rw [isSommeConvexes_iff_bijOn]
  refine ⟨fun i => (a i +ᵥ V i).2, ?_⟩
  have := bijOn_vadd hS.2 a
  rw [hsum, hb] at this
  exact this

/-- Remarque 1, « d'une infinité de façons si n ≠ 1 »: with two distinct indices, `E ≠ 0` and
`W'` nonempty, the families of classes `v i` with sum `W'` form an infinite set. -/
theorem remarque1_infinite {I : Type*} [Fintype I] [Nontrivial E] {w : KModE E}
    {v : I → KModE E} (h : SommeClasses w v) (W' : KE E) (hW' : classe W' = w)
    (hne : W'.1.Nonempty) {i j : I} (hij : i ≠ j) :
    {V' : I → KE E | (∀ k, classe (V' k) = v k) ∧
      IsSommeConvexes W'.1 (fun k => (V' k).1)}.Infinite := by
  classical
  haveI : Nonempty I := ⟨i⟩
  obtain ⟨V', hV'v, hV'S⟩ := remarque1_famille h W' hW'
  rw [isSommeConvexes_iff_bijOn] at hV'S
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  obtain ⟨x₀, hx₀, -⟩ := hV'S.2.surjOn hne.some_mem
  let d : ℝ → I → E := fun t => Pi.single i (t • u) - Pi.single j (t • u)
  have hd : ∀ t, ∑ k, d t k = 0 := fun t => by
    simp only [d, Pi.sub_apply, Finset.sum_sub_distrib, Fintype.sum_pi_single', sub_self]
  have hdi : ∀ t, d t i = t • u := fun t => by
    simp [d, Pi.single_eq_of_ne hij]
  have hdj : ∀ t, d t j = -(t • u) := fun t => by
    simp [d, Pi.single_eq_of_ne (Ne.symm hij)]
  refine Set.infinite_of_injective_forall_mem (f := fun t k => d t k +ᵥ V' k) ?_ ?_
  · intro t s hts
    have hi : d t i +ᵥ (V' i).1 = d s i +ᵥ (V' i).1 := congrArg (fun F => (F i).1) hts
    have hj : d t j +ᵥ (V' j).1 = d s j +ᵥ (V' j).1 := congrArg (fun F => (F j).1) hts
    rw [hdi, hdi] at hi
    rw [hdj, hdj] at hj
    set δ : E := (t - s) • u with hδ
    have hiδ : δ +ᵥ (V' i).1 = (V' i).1 := by
      have := congrArg (fun S => (-(s • u)) +ᵥ S) hi
      simp only [vadd_vadd] at this
      rw [hδ, sub_smul, sub_eq_neg_add, this, neg_add_cancel, zero_vadd]
    have hjδ : -δ +ᵥ (V' j).1 = (V' j).1 := by
      have := congrArg (fun S => (s • u) +ᵥ S) hj
      simp only [vadd_vadd] at this
      rw [hδ, sub_smul, neg_sub, sub_eq_add_neg, this, add_neg_cancel, zero_vadd]
    let x' : I → E := x₀ + Pi.single i δ - Pi.single j δ
    have hx' : x' ∈ Set.univ.pi fun k => (V' k).1 := by
      intro k _
      by_cases hki : k = i
      · subst hki
        simp only [x', Pi.sub_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
          sub_zero]
        rw [← hiδ, mem_vadd_iff_sub_mem, add_sub_cancel_right]
        exact hx₀ k trivial
      · by_cases hkj : k = j
        · subst hkj
          simp only [x', Pi.sub_apply, Pi.add_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hki, add_zero]
          rw [← hjδ, mem_vadd_iff_sub_mem, sub_neg_eq_add, sub_add_cancel]
          exact hx₀ k trivial
        · simp only [x', Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hki,
            Pi.single_eq_of_ne hkj, add_zero, sub_zero]
          exact hx₀ k trivial
    have hsum : ∑ k, x' k = ∑ k, x₀ k := by
      simp only [x', Pi.sub_apply, Pi.add_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Fintype.sum_pi_single', add_sub_cancel_right]
    have := congrFun (hV'S.2.injOn hx' hx₀ hsum) i
    simp only [x', Pi.sub_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      sub_zero, add_eq_left] at this
    rw [hδ, smul_eq_zero] at this
    rcases this with h1 | h1
    · linarith [sub_eq_zero.1 h1]
    · exact absurd h1 hu
  · intro t
    refine ⟨fun k => by rw [classe_vadd, hV'v], ?_⟩
    rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun k => (d t k +ᵥ V' k).2, ?_⟩
    have := bijOn_vadd hV'S.2 (d t)
    rw [hd, zero_vadd] at this
    exact this

/-! ### The printed form of Remarque 1 in the degenerate cases -/

/-- A convex part as an element of `K(E)`. -/
def KE.mk (s : Set E) (hs : Convex ℝ s) : KE E := ⟨s, hs⟩

/-- **Counterexample, `n = 0`.** The empty family of classes has the class of a point as its sum
(`{0}` is the sum of the empty family), but the convex `{1}`, of that class, is the sum of no
family indexed by `Fin 0`: the second assertion of Remarque 1 needs `n ≥ 1`. -/
theorem not_remarque1_famille_fin_zero :
    SommeClasses (classe (KE.mk ({0} : Set ℝ) (convex_singleton 0)))
        (Fin.elim0 : Fin 0 → KModE ℝ) ∧
      classe (KE.mk ({1} : Set ℝ) (convex_singleton 1)) =
        classe (KE.mk ({0} : Set ℝ) (convex_singleton 0)) ∧
      ¬ ∃ V' : Fin 0 → KE ℝ, IsSommeConvexes ({1} : Set ℝ) (fun i => (V' i).1) := by
  refine ⟨⟨KE.mk {0} (convex_singleton 0), Fin.elim0, rfl, fun i => i.elim0, ?_⟩, ?_, ?_⟩
  · rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun i => i.elim0, ?_⟩
    refine ⟨fun x _ => by simp [KE.mk], fun x _ y _ _ => funext fun i => i.elim0, fun z hz => ?_⟩
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (Set.mem_singleton_iff.1 hz).symm
  · exact (classe_eq_iff _ _).2 ⟨-1, by simp [KE.mk]⟩
  · rintro ⟨V', hV'⟩
    rw [isSommeConvexes_iff_bijOn] at hV'
    have := hV'.2.mapsTo (x := Fin.elim0) (fun i => i.elim0)
    simp at this

/-- **Counterexample, empty convexes.** With `n = 2`, `E = ℝ` and `V₁ = V₂ = ∅`, the class of `∅`
is the sum of the two classes of `∅`, and the convex `∅` is the sum of exactly ONE family of those
classes: the « infinité de façons » of Remarque 1 needs nonempty convexes. -/
theorem not_remarque1_infinite_vide :
    SommeClasses (classe (KE.mk (∅ : Set ℝ) convex_empty))
        (fun _ : Fin 2 => classe (KE.mk (∅ : Set ℝ) convex_empty)) ∧
      {V' : Fin 2 → KE ℝ | (∀ k, classe (V' k) = classe (KE.mk (∅ : Set ℝ) convex_empty)) ∧
        IsSommeConvexes (∅ : Set ℝ) (fun k => (V' k).1)}.Subsingleton := by
  refine ⟨⟨KE.mk ∅ convex_empty, fun _ => KE.mk ∅ convex_empty, rfl, fun _ => rfl, ?_⟩, ?_⟩
  · rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun _ => convex_empty, ?_⟩
    rw [Set.univ_pi_eq_empty (i := (0 : Fin 2)) rfl]
    exact Set.bijOn_empty _
  · have hE : ∀ V' : Fin 2 → KE ℝ,
        (∀ k, classe (V' k) = classe (KE.mk (∅ : Set ℝ) convex_empty)) →
          V' = fun _ => KE.mk ∅ convex_empty := by
      intro V' hV'
      funext k
      obtain ⟨a, ha⟩ := (classe_eq_iff _ _).1 (hV' k)
      apply Subtype.ext
      rw [← neg_vadd_vadd a (V' k).1, ha]
      simp [KE.mk]
    rintro V₁ ⟨h₁, -⟩ V₂ ⟨h₂, -⟩
    rw [hE V₁ h₁, hE V₂ h₂]

/-! ### Proposition 1 -/

/-- The heart of Prop. 1's uniqueness: if `W = ∑ V_i` with `0 ∈ V_i` convex, and the translates
`U_i = a_i + V_i` also contain `0` and have all their sums in `W`, then `U_i ⊆ V_i`. -/
theorem subset_of_translate_somme {I : Type*} [Fintype I] {W : Set E} {V U : I → Set E}
    (hVc : ∀ i, Convex ℝ (V i)) (h0V : ∀ i, (0 : E) ∈ V i)
    (hV : Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi V) W)
    (hU : Set.MapsTo (fun x : I → E => ∑ i, x i) (Set.univ.pi U) W)
    (a : I → E) (hUa : ∀ i, U i = a i +ᵥ V i) (h0U : ∀ i, (0 : E) ∈ U i) (i : I) :
    U i ⊆ V i := by
  classical
  intro u hu
  rw [hUa, mem_vadd_iff_sub_mem] at hu
  set y := u - a i with hy_def
  have hna : ∀ k, -a k ∈ V k := by
    intro k
    have := h0U k
    rw [hUa, mem_vadd_iff_sub_mem, zero_sub] at this
    exact this
  -- the point `single i y + a` of `∏ U_k`
  have hxa : (Pi.single i y + a : I → E) ∈ Set.univ.pi U := by
    intro k _
    rw [hUa, mem_vadd_iff_sub_mem, Pi.add_apply, add_sub_cancel_right]
    by_cases hk : k = i
    · subst hk; simpa using hu
    · rw [Pi.single_eq_of_ne hk]; exact h0V k
  obtain ⟨z, hz, hzs⟩ := hV.surjOn (hU hxa)
  have hzs' : ∑ k, z k = y + ∑ k, a k := by
    have : ∑ k, z k = ∑ k, (Pi.single i y + a : I → E) k := hzs
    rw [this]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single']
  -- two decompositions of `y / 2`
  let m : I → E := fun k => (1 / 2 : ℝ) • z k + (1 / 2 : ℝ) • (-a k)
  let m' : I → E := Pi.single i ((1 / 2 : ℝ) • y)
  have hm : m ∈ Set.univ.pi V := fun k _ =>
    hVc k (hz k trivial) (hna k) (by norm_num) (by norm_num) (by norm_num)
  have hm' : m' ∈ Set.univ.pi V := by
    intro k _
    by_cases hk : k = i
    · subst hk
      simp only [m', Pi.single_eq_same]
      exact (hVc k).smul_mem_of_zero_mem (h0V k) hu ⟨by norm_num, by norm_num⟩
    · simp only [m', Pi.single_eq_of_ne hk]; exact h0V k
  have hsum : ∑ k, m k = ∑ k, m' k := by
    simp only [m, m', Finset.sum_add_distrib, ← Finset.smul_sum, Fintype.sum_pi_single',
      Finset.sum_neg_distrib, hzs']
    module
  have hmm := congrFun (hV.injOn hm hm' hsum) i
  simp only [m, m', Pi.single_eq_same] at hmm
  have hzi : z i = u := by
    have h2 : z i = y + a i := by
      have := congrArg (fun e => (2 : ℝ) • e) hmm
      simp only [smul_add, smul_smul, smul_neg] at this
      norm_num at this
      rw [← this]; abel
    rw [h2, hy_def, sub_add_cancel]
  rw [← hzi]
  exact hz i trivial

/-- **Prop. 1.** If `∑ v_i = w` and `W` of class `w` contains the origin, there is one and only one
system of convex sets `V i` of classes `v i`, each containing the origin, with `W = ∑ V_i`. -/
theorem prop1_decomposition_origine {I : Type*} [Fintype I] {w : KModE E} {v : I → KModE E}
    (h : SommeClasses w v) (W : KE E) (hW : classe W = w) (h0 : (0 : E) ∈ W.1) :
    ∃! V : I → KE E, (∀ i, classe (V i) = v i) ∧ (∀ i, (0 : E) ∈ (V i).1) ∧
      IsSommeConvexes W.1 (fun i => (V i).1) := by
  obtain ⟨W₀, V₀, hW₀, hV₀, hS⟩ := h
  rw [isSommeConvexes_iff_bijOn] at hS
  obtain ⟨c, hc⟩ := (classe_eq_iff W₀ W).1 (hW₀.trans hW.symm)
  have hm : -c ∈ W₀.1 := by
    have h0' : (0 : E) ∈ c +ᵥ W₀.1 := hc ▸ h0
    rw [mem_vadd_iff_sub_mem, zero_sub] at h0'
    exact h0'
  obtain ⟨x₀, hx₀, hx₀s⟩ := hS.2.surjOn hm
  have hx₀s' : ∑ i, x₀ i = -c := hx₀s
  refine ⟨fun i => (-x₀ i) +ᵥ V₀ i, ⟨fun i => by rw [classe_vadd, hV₀], fun i => ?_, ?_⟩, ?_⟩
  · show (0 : E) ∈ -x₀ i +ᵥ (V₀ i).1
    rw [mem_vadd_iff_sub_mem, zero_sub, neg_neg]
    exact hx₀ i trivial
  · rw [isSommeConvexes_iff_bijOn]
    refine ⟨fun i => ((-x₀ i) +ᵥ V₀ i).2, ?_⟩
    have := bijOn_vadd hS.2 (fun i => -x₀ i)
    rw [Finset.sum_neg_distrib, hx₀s', neg_neg, hc] at this
    exact this
  · rintro U ⟨hUv, hU0, hUS⟩
    rw [isSommeConvexes_iff_bijOn] at hUS
    -- the system just built
    set V : I → KE E := fun i => (-x₀ i) +ᵥ V₀ i with hV_def
    have hV0 : ∀ i, (0 : E) ∈ (V i).1 := by
      intro i
      show (0 : E) ∈ -x₀ i +ᵥ (V₀ i).1
      rw [mem_vadd_iff_sub_mem, zero_sub, neg_neg]
      exact hx₀ i trivial
    have hVS : Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi fun i => (V i).1) W.1 := by
      have := bijOn_vadd hS.2 (fun i => -x₀ i)
      rw [Finset.sum_neg_distrib, hx₀s', neg_neg, hc] at this
      exact this
    have hcl : ∀ i, ∃ a : E, a +ᵥ (V i).1 = (U i).1 := fun i =>
      (classe_eq_iff _ _).1 (by rw [hV_def, classe_vadd, hV₀, hUv])
    choose a ha using hcl
    funext i
    apply Subtype.ext
    apply Set.Subset.antisymm
    · exact subset_of_translate_somme (fun i => (V i).2) hV0 hVS hUS.2.mapsTo a
        (fun i => (ha i).symm) hU0 i
    · refine subset_of_translate_somme (fun i => (U i).2) hU0 hUS.2 hVS.mapsTo (fun i => -a i)
        (fun i => ?_) hV0 i
      rw [← ha i, neg_vadd_vadd]

/-! ### Remarque 2: infinite sums -/

/-- The sum of a finitely supported family. -/
noncomputable def sommeF (I : Type*) (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (I →₀ E) →ₗ[ℝ] E :=
  Finsupp.lsum ℝ (fun _ : I => (LinearMap.id : E →ₗ[ℝ] E))

/-- Remarque 2 in the reading taken: `W` and the `V i` convex and containing the origin, and the
sum is a bijection from the finitely supported families with components in the `V i` onto `W`. -/
def IsSommeInfinie {I : Type*} (W : Set E) (V : I → Set E) : Prop :=
  Convex ℝ W ∧ (∀ i, Convex ℝ (V i)) ∧ (0 : E) ∈ W ∧ (∀ i, (0 : E) ∈ V i) ∧
    Set.BijOn (sommeF I E) {f : I →₀ E | ∀ i, f i ∈ V i} W

/-- Remarque 2 as worded: every `x ∈ W`, `x ≠ 0`, is in one and only one way a finite sum of
components `x_i ∈ V_i` (a finitely supported family, the components off its support being `0`). -/
def IsSommeInfinieTexte {I : Type*} (W : Set E) (V : I → Set E) : Prop :=
  Convex ℝ W ∧ (∀ i, Convex ℝ (V i)) ∧ (0 : E) ∈ W ∧ (∀ i, (0 : E) ∈ V i) ∧
    ∀ x ∈ W, x ≠ 0 → ∃! f : I →₀ E, (∀ i, f i ∈ V i) ∧ sommeF I E f = x

theorem sommeF_apply {I : Type*} (f : I →₀ E) : sommeF I E f = f.sum fun _ v => v := by
  rw [sommeF, Finsupp.lsum_apply]
  rfl

theorem sommeF_apply_fintype {I : Type*} [Fintype I] (f : I →₀ E) :
    sommeF I E f = ∑ i, f i := by
  rw [sommeF_apply, Finsupp.sum_fintype _ _ (fun _ => rfl)]

theorem IsSommeInfinie.texte {I : Type*} {W : Set E} {V : I → Set E}
    (h : IsSommeInfinie W V) : IsSommeInfinieTexte W V := by
  obtain ⟨hW, hV, h0W, h0V, hB⟩ := h
  refine ⟨hW, hV, h0W, h0V, fun x hx _ => ?_⟩
  obtain ⟨f, hf, hfx⟩ := hB.surjOn hx
  exact ⟨f, ⟨hf, hfx⟩, fun g ⟨hg, hgx⟩ => hB.injOn hg hf (hgx.trans hfx.symm)⟩

theorem isSommeInfinie_iff_texte {I : Type*} {W : Set E} {V : I → Set E} :
    IsSommeInfinie W V ↔ IsSommeInfinieTexte W V ∧
      ∀ f : I →₀ E, (∀ i, f i ∈ V i) → sommeF I E f ∈ W := by
  classical
  constructor
  · intro h
    exact ⟨h.texte, fun f hf => h.2.2.2.2.mapsTo hf⟩
  · rintro ⟨⟨hW, hV, h0W, h0V, hT⟩, hmaps⟩
    refine ⟨hW, hV, h0W, h0V, fun f hf => hmaps f hf, fun f hf g hg hfg => ?_, fun x hx => ?_⟩
    · have hf' : ∀ i, f i ∈ V i := hf
      have hg' : ∀ i, g i ∈ V i := hg
      have hfg' : sommeF I E f = sommeF I E g := hfg
      by_cases hx0 : sommeF I E f = 0
      · by_cases hex : ∃ y ∈ W, y ≠ 0
        · obtain ⟨y, hy, hy0⟩ := hex
          obtain ⟨k, ⟨hk, hky⟩, -⟩ := hT y hy hy0
          have hy2 : (1 / 2 : ℝ) • y ∈ W :=
            hW.smul_mem_of_zero_mem h0W hy ⟨by norm_num, by norm_num⟩
          have hy20 : (1 / 2 : ℝ) • y ≠ 0 := smul_ne_zero (by norm_num) hy0
          obtain ⟨m, -, hm⟩ := hT _ hy2 hy20
          have hmf : ((1 / 2 : ℝ) • k + (1 / 2 : ℝ) • f) = m := by
            refine hm _ ⟨fun i => ?_, ?_⟩
            · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply]
              exact hV i (hk i) (hf' i) (by norm_num) (by norm_num) (by norm_num)
            · rw [map_add, map_smul, map_smul, hky, hx0, smul_zero, add_zero]
          have hmg : ((1 / 2 : ℝ) • k + (1 / 2 : ℝ) • g) = m := by
            refine hm _ ⟨fun i => ?_, ?_⟩
            · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply]
              exact hV i (hk i) (hg' i) (by norm_num) (by norm_num) (by norm_num)
            · rw [map_add, map_smul, map_smul, hky, ← hfg', hx0, smul_zero, add_zero]
          exact smul_right_injective (I →₀ E) (by norm_num : (1 / 2 : ℝ) ≠ 0)
            (add_left_cancel (hmf.trans hmg.symm))
        · push Not at hex
          have hzero : ∀ h : I →₀ E, (∀ i, h i ∈ V i) → h = 0 := by
            intro h hh
            ext i
            have hs : ∀ j, (Finsupp.single i (h i)) j ∈ V j := by
              intro j
              by_cases hj : j = i
              · subst hj; simpa using hh j
              · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]; exact h0V j
            have := hex _ (hmaps _ hs)
            rw [sommeF_apply, Finsupp.sum_single_index rfl] at this
            simpa using this
          rw [hzero f hf', hzero g hg']
      · exact (hT _ (hmaps f hf') hx0).unique ⟨hf', rfl⟩ ⟨hg', hfg'.symm⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, fun i => by simpa using h0V i, by rw [map_zero, hx0]⟩
      · obtain ⟨f, ⟨hf, hfx⟩, -⟩ := hT x hx hx0
        exact ⟨f, hf, hfx⟩

theorem isSommeInfinie_iff_isSommeConvexes {I : Type*} [Fintype I] (W : Set E) (V : I → Set E) :
    IsSommeInfinie W V ↔ IsSommeConvexes W V ∧ (0 : E) ∈ W ∧ ∀ i, (0 : E) ∈ V i := by
  have key : Set.BijOn (sommeF I E) {f : I →₀ E | ∀ i, f i ∈ V i} W ↔
      Set.BijOn (fun x : I → E => ∑ i, x i) (Set.univ.pi V) W := by
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
      · have := h.mapsTo (x := Finsupp.equivFunOnFinite.symm x) (fun i => hx i trivial)
        rwa [sommeF_apply_fintype] at this
      · have := h.injOn (x₁ := Finsupp.equivFunOnFinite.symm x)
          (x₂ := Finsupp.equivFunOnFinite.symm y) (fun i => hx i trivial) (fun i => hy i trivial)
          (by rw [sommeF_apply_fintype, sommeF_apply_fintype]; exact hxy)
        exact Finsupp.equivFunOnFinite.symm.injective this
      · obtain ⟨f, hf, hfz⟩ := h.surjOn hz
        exact ⟨⇑f, fun i _ => hf i, by rw [← hfz, sommeF_apply_fintype]⟩
    · intro h
      refine ⟨fun f hf => ?_, fun f hf g hg hfg => ?_, fun z hz => ?_⟩
      · rw [sommeF_apply_fintype]
        exact h.mapsTo (x := ⇑f) (fun i _ => hf i)
      · have hfg' : ∑ i, f i = ∑ i, g i := by
          rw [← sommeF_apply_fintype, ← sommeF_apply_fintype]; exact hfg
        exact DFunLike.coe_injective (h.injOn (x₁ := ⇑f) (x₂ := ⇑g) (fun i _ => hf i)
          (fun i _ => hg i) hfg')
      · obtain ⟨x, hx, hxz⟩ := h.surjOn hz
        refine ⟨Finsupp.equivFunOnFinite.symm x, fun i => hx i trivial, ?_⟩
        rw [sommeF_apply_fintype]
        exact hxz
  rw [isSommeConvexes_iff_bijOn, ← key]
  constructor
  · rintro ⟨-, hV, h0W, h0V, hB⟩
    exact ⟨⟨hV, hB⟩, h0W, h0V⟩
  · rintro ⟨⟨hV, hB⟩, h0W, h0V⟩
    have hW : Convex ℝ W := ((isSommeConvexes_iff_bijOn W V).2 ⟨hV, key.1 hB⟩).1
    exact ⟨hW, hV, h0W, h0V, hB⟩

/-- Remarque 2 as worded is weaker than Déf. 1 for a finite `I`: `W = [0,1]`, `V = [0,2]` (one
index) meets the wording, but `p` sends `2 ∈ V` outside `W`. -/
theorem isSommeInfinieTexte_not_isSommeConvexes :
    IsSommeInfinieTexte (Set.Icc (0 : ℝ) 1) ![Set.Icc (0 : ℝ) 2] ∧
      ¬ IsSommeConvexes (Set.Icc (0 : ℝ) 1) ![Set.Icc (0 : ℝ) 2] := by
  refine ⟨⟨convex_Icc 0 1, fun i => by fin_cases i; exact convex_Icc 0 2,
    ⟨le_refl 0, zero_le_one⟩, fun i => by fin_cases i; simp, fun x hx _ => ?_⟩, ?_⟩
  · refine ⟨Finsupp.single 0 x, ⟨fun i => ?_, ?_⟩, fun f ⟨_, hfx⟩ => ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Finsupp.single_eq_same, Matrix.cons_val_zero,
        Set.mem_Icc]
      exact ⟨hx.1, by linarith [hx.2]⟩
    · rw [sommeF_apply, Finsupp.sum_single_index rfl]
    · rw [sommeF_apply_fintype, Fin.sum_univ_one] at hfx
      apply Finsupp.ext
      intro i
      fin_cases i
      simp [hfx]
  · intro h
    rw [isSommeConvexes_iff_bijOn] at h
    have := h.2.mapsTo (x := ![2]) (fun i _ => by fin_cases i; simp)
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, Set.mem_Icc] at this
    linarith [this.2]

/-! ### Remarque 3: subspaces -/

/-- Independent subspaces: a finitely supported family with components in the `E i` and sum `0`
is zero. -/
theorem eq_zero_of_iSupIndep {I : Type*} {Ei : I → Submodule ℝ E} (hind : iSupIndep Ei)
    (f : I →₀ E) (hf : ∀ i, f i ∈ Ei i) (h0 : sommeF I E f = 0) : f = 0 := by
  classical
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [sommeF_apply, ← Finsupp.add_sum_erase' f i _ (fun _ => rfl)] at h0
  have hmem : ((f.erase i).sum fun _ v => v) ∈ ⨆ (j) (_ : j ≠ i), Ei j := by
    apply Submodule.finsuppSum_mem
    intro c hc
    have hci : c ≠ i := by
      rintro rfl
      simp at hc
    rw [Finsupp.erase_ne hci]
    exact (le_iSup₂ (f := fun j (_ : j ≠ i) => Ei j) c hci) (hf c)
  have hfi : f i ∈ ⨆ (j) (_ : j ≠ i), Ei j := by
    rw [eq_neg_of_add_eq_zero_left h0]
    exact neg_mem hmem
  exact (Submodule.disjoint_def.1 (iSupIndep_def.1 hind i)) _ (hf i) hfi

/-- Injectivity of the sum on families with components in the `E i` gives independence. -/
theorem iSupIndep_of_injOn {I : Type*} {Ei : I → Submodule ℝ E}
    (h : Set.InjOn (sommeF I E) {f : I →₀ E | ∀ i, f i ∈ (Ei i : Set E)}) : iSupIndep Ei := by
  classical
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨f, hf, hfx⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun j => ⨆ (_ : j ≠ i), Ei j) x).1 hx'
  have hfi : f i = 0 := by
    have := hf i
    simpa using this
  have hf' : ∀ j, f j ∈ (Ei j : Set E) := by
    intro j
    by_cases hj : j = i
    · rw [hj, hfi]; exact (Ei i).zero_mem
    · have := hf j
      simpa [hj] using this
  have hs : ∀ j, (Finsupp.single i x) j ∈ (Ei j : Set E) := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hx
    · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]; exact (Ei j).zero_mem
  have := h hs hf' (by rw [sommeF_apply, sommeF_apply, Finsupp.sum_single_index rfl, hfx])
  have := congrArg (fun g : I →₀ E => g i) this
  simpa [hfi] using this

/-- Remarque 3 for the sums of Remarque 2 (any `I`): subspaces `E i` have sum the subspace `W`
iff they are independent with supremum `W`. -/
theorem remarque3_infinie {I : Type*} (W : Submodule ℝ E) (Ei : I → Submodule ℝ E) :
    IsSommeInfinie (W : Set E) (fun i => (Ei i : Set E)) ↔ iSupIndep Ei ∧ ⨆ i, Ei i = W := by
  constructor
  · rintro ⟨-, -, -, -, hB⟩
    refine ⟨iSupIndep_of_injOn hB.injOn, ?_⟩
    ext x
    rw [Submodule.mem_iSup_iff_exists_finsupp]
    constructor
    · rintro ⟨f, hf, rfl⟩
      have := hB.mapsTo (x := f) hf
      rwa [sommeF_apply] at this
    · intro hx
      obtain ⟨f, hf, hfx⟩ := hB.surjOn (show x ∈ (W : Set E) from hx)
      exact ⟨f, hf, by rw [← hfx, sommeF_apply]⟩
  · rintro ⟨hind, hsup⟩
    have hmem : ∀ x, x ∈ (W : Set E) ↔
        ∃ f : I →₀ E, (∀ i, f i ∈ Ei i) ∧ sommeF I E f = x := by
      intro x
      rw [SetLike.mem_coe, ← hsup, Submodule.mem_iSup_iff_exists_finsupp]
      simp only [sommeF_apply]
    refine ⟨W.convex, fun i => (Ei i).convex, W.zero_mem, fun i => (Ei i).zero_mem, ?_, ?_, ?_⟩
    · intro f hf
      exact (hmem _).2 ⟨f, hf, rfl⟩
    · intro f hf g hg hfg
      have hf' : ∀ i, f i ∈ Ei i := hf
      have hg' : ∀ i, g i ∈ Ei i := hg
      have := eq_zero_of_iSupIndep hind (f - g)
        (fun i => by simpa using sub_mem (hf' i) (hg' i))
        (by rw [map_sub]; exact sub_eq_zero.2 hfg)
      exact sub_eq_zero.1 this
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := (hmem x).1 hx
      exact ⟨f, hf, hfx⟩

/-- **Remarque 3** (Déf. 1, `I` finite): subspaces `E i` have sum the subspace `W` iff they are
independent with supremum `W`, i.e. `W` is their ordinary direct sum. -/
theorem remarque3 {I : Type*} [Fintype I] (W : Submodule ℝ E) (Ei : I → Submodule ℝ E) :
    IsSommeConvexes (W : Set E) (fun i => (Ei i : Set E)) ↔ iSupIndep Ei ∧ ⨆ i, Ei i = W := by
  rw [← remarque3_infinie, isSommeInfinie_iff_isSommeConvexes]
  exact ⟨fun h => ⟨h, W.zero_mem, fun i => (Ei i).zero_mem⟩, fun h => h.1⟩

/-- **Remarque 3** with `W = E`: `E = ∑ E_i` (Déf. 1) iff `E` is the internal direct sum of the
`E_i` (Mathlib's `DirectSum.IsInternal`). -/
theorem remarque3_somme_directe {I : Type*} [Fintype I] [DecidableEq I]
    (Ei : I → Submodule ℝ E) :
    IsSommeConvexes (Set.univ : Set E) (fun i => (Ei i : Set E)) ↔ DirectSum.IsInternal Ei := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, ← remarque3 ⊤ Ei,
    Submodule.top_coe]

/-- Remarque 3 with `W = E` for the sums of Remarque 2 (any `I`). -/
theorem remarque3_somme_directe_infinie {I : Type*} [DecidableEq I] (Ei : I → Submodule ℝ E) :
    IsSommeInfinie (Set.univ : Set E) (fun i => (Ei i : Set E)) ↔ DirectSum.IsInternal Ei := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, ← remarque3_infinie ⊤ Ei,
    Submodule.top_coe]

/-- Remarque 3 with `W = E`, in the LITERAL wording of Remarque 2 as well: no reading of
Remarque 2 is needed for Remarque 3. -/
theorem remarque3_somme_directe_texte {I : Type*} [DecidableEq I] (Ei : I → Submodule ℝ E) :
    IsSommeInfinieTexte (Set.univ : Set E) (fun i => (Ei i : Set E)) ↔
      DirectSum.IsInternal Ei := by
  rw [← remarque3_somme_directe_infinie, isSommeInfinie_iff_texte]
  exact ⟨fun h => ⟨h, fun _ _ => Set.mem_univ _⟩, fun h => h.1⟩

end Sommes

/-! ### The instance -/

/-- The closed unit disc of `ℝ²` (Euclidean). -/
def disque : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- The instance of the block: `[0,1]² = [0,1] × {0} + {0} × [0,1]` (Déf. 1). -/
theorem exemple_carre_somme :
    IsSommeConvexes (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
      ![Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}, {(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1] := by
  rw [isSommeConvexes_iff_bijOn]
  refine ⟨fun i => ?_, fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · fin_cases i
    · exact (convex_Icc 0 1).prod (convex_singleton 0)
    · exact (convex_singleton 0).prod (convex_Icc 0 1)
  · have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_prod,
      Set.mem_Icc, Set.mem_singleton_iff] at h0 h1
    simp only [Fin.sum_univ_two, Fin.isValue, Set.mem_prod, Prod.fst_add, Prod.snd_add,
      Set.mem_Icc, h0.2, h1.1, add_zero, zero_add]
    exact ⟨h0.1, h1.2⟩
  · have hx0 := hx 0 trivial
    have hx1 := hx 1 trivial
    have hy0 := hy 0 trivial
    have hy1 := hy 1 trivial
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_prod,
      Set.mem_Icc, Set.mem_singleton_iff] at hx0 hx1 hy0 hy1
    have hxy' : x 0 + x 1 = y 0 + y 1 := by simpa [Fin.sum_univ_two] using hxy
    have e1 := congrArg Prod.fst hxy'
    have e2 := congrArg Prod.snd hxy'
    simp only [Prod.fst_add, Prod.snd_add] at e1 e2
    funext k
    fin_cases k
    · exact Prod.ext (by simp only [Fin.zero_eta, Fin.isValue]; linarith [hx1.1, hy1.1])
        (by simp only [Fin.zero_eta, Fin.isValue]; rw [hx0.2, hy0.2])
    · exact Prod.ext (by simp only [Fin.mk_one, Fin.isValue]; rw [hx1.1, hy1.1])
        (by simp only [Fin.mk_one, Fin.isValue]; linarith [hx0.2, hy0.2])
  · simp only [Set.mem_prod, Set.mem_Icc] at hz
    refine ⟨![(z.1, 0), (0, z.2)], fun i _ => ?_, ?_⟩
    · fin_cases i
      · simp [hz.1.1, hz.1.2]
      · simp [hz.2.1, hz.2.2]
    · simp [Fin.sum_univ_two]

/-- Strict convexity of the disc: a point of an open segment between two distinct points of the
disc lies in the open disc. -/
theorem disque_strict {u v q : ℝ × ℝ} (hu : u ∈ disque) (hv : v ∈ disque) (huv : u ≠ v)
    (hq : q ∈ openSegment ℝ u v) : q.1 ^ 2 + q.2 ^ 2 < 1 := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hq
  simp only [disque, Set.mem_setOf_eq] at hu hv
  have hd : 0 < (u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2 := by
    rcases lt_or_eq_of_le (add_nonneg (sq_nonneg (u.1 - v.1)) (sq_nonneg (u.2 - v.2))) with
      h | h
    · exact h
    · exfalso
      apply huv
      have h1 : (u.1 - v.1) ^ 2 = 0 := by nlinarith [sq_nonneg (u.1 - v.1), sq_nonneg (u.2 - v.2)]
      have h2 : (u.2 - v.2) ^ 2 = 0 := by nlinarith [sq_nonneg (u.1 - v.1), sq_nonneg (u.2 - v.2)]
      exact Prod.ext (by nlinarith [pow_eq_zero_iff (n := 2) (a := u.1 - v.1) two_ne_zero |>.1 h1])
        (by nlinarith [pow_eq_zero_iff (n := 2) (a := u.2 - v.2) two_ne_zero |>.1 h2])
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have key : (α * u.1 + (1 - α) * v.1) ^ 2 + (α * u.2 + (1 - α) * v.2) ^ 2 =
      α * (u.1 ^ 2 + u.2 ^ 2) + (1 - α) * (v.1 ^ 2 + v.2 ^ 2) -
        α * (1 - α) * ((u.1 - v.1) ^ 2 + (u.2 - v.2) ^ 2) := by ring
  rw [key]
  nlinarith [mul_pos hα hβ, mul_pos (mul_pos hα hβ) hd]

/-- The core of the disc example: if every point of the disc is `y₀ + y₁` with `y₀ ∈ [a, b]`,
`y₁ ∈ [c, d]`, and every such sum lies in the disc, contradiction. -/
theorem disque_not_somme_core (a b c d : ℝ × ℝ)
    (hsurj : ∀ q ∈ disque, ∃ y₀ ∈ segment ℝ a b, ∃ y₁ ∈ segment ℝ c d, y₀ + y₁ = q)
    (hmaps : ∀ y₀ ∈ segment ℝ a b, ∀ y₁ ∈ segment ℝ c d, y₀ + y₁ ∈ disque) : False := by
  -- every point of the unit circle is one of the four corners `a + c, a + d, b + c, b + d`
  have hcorner : ∀ q : ℝ × ℝ, q.1 ^ 2 + q.2 ^ 2 = 1 →
      q ∈ ({a + c, a + d, b + c, b + d} : Set (ℝ × ℝ)) := by
    intro q hq
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := hsurj q (by simp [disque, hq])
    have h0 : y₀ = a ∨ y₀ = b := by
      by_contra hne
      push Not at hne
      have hop := mem_openSegment_of_ne_left_right hne.1.symm hne.2.symm hy₀
      have hab : a ≠ b := by
        rintro rfl
        rw [openSegment_same] at hop
        exact hne.1 hop
      obtain ⟨α, β, hα, hβ, hαβ, hy⟩ := hop
      have hq' : y₀ + y₁ ∈ openSegment ℝ (a + y₁) (b + y₁) := by
        refine ⟨α, β, hα, hβ, hαβ, ?_⟩
        rw [← hy, smul_add, smul_add]
        have : y₁ = α • y₁ + β • y₁ := by rw [← add_smul, hαβ, one_smul]
        conv_rhs => rw [this]
        abel
      have := disque_strict (hmaps a (left_mem_segment ℝ a b) y₁ hy₁)
        (hmaps b (right_mem_segment ℝ a b) y₁ hy₁) (fun h => hab (add_right_cancel h)) hq'
      linarith
    have h1 : y₁ = c ∨ y₁ = d := by
      by_contra hne
      push Not at hne
      have hop := mem_openSegment_of_ne_left_right hne.1.symm hne.2.symm hy₁
      have hcd : c ≠ d := by
        rintro rfl
        rw [openSegment_same] at hop
        exact hne.1 hop
      obtain ⟨α, β, hα, hβ, hαβ, hy⟩ := hop
      have hq' : y₀ + y₁ ∈ openSegment ℝ (y₀ + c) (y₀ + d) := by
        refine ⟨α, β, hα, hβ, hαβ, ?_⟩
        rw [← hy, smul_add, smul_add]
        have : y₀ = α • y₀ + β • y₀ := by rw [← add_smul, hαβ, one_smul]
        conv_rhs => rw [this]
        abel
      have := disque_strict (hmaps y₀ hy₀ c (left_mem_segment ℝ c d))
        (hmaps y₀ hy₀ d (right_mem_segment ℝ c d)) (fun h => hcd (add_left_cancel h)) hq'
      linarith
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp
  -- so `[0, 1]` would be finite
  have hfin : (Set.Icc (0 : ℝ) 1).Finite := by
    refine ((Set.toFinite ({a + c, a + d, b + c, b + d} : Set (ℝ × ℝ))).image Prod.fst).subset ?_
    intro r hr
    refine ⟨(r, Real.sqrt (1 - r ^ 2)), hcorner _ ?_, rfl⟩
    simp only
    rw [Real.sq_sqrt (by nlinarith [hr.1, hr.2])]
    ring
  exact Set.Icc_infinite (zero_lt_one' ℝ) hfin

/-- The disc of `ℝ²` is not the Minkowski sum of two segments. -/
theorem disque_ne_somme_segments (a b c d : ℝ × ℝ) :
    disque ≠ segment ℝ a b + segment ℝ c d := by
  intro h
  refine disque_not_somme_core a b c d (fun q hq => ?_) (fun y₀ hy₀ y₁ hy₁ => ?_)
  · rw [h] at hq
    obtain ⟨y₀, hy₀, y₁, hy₁, e⟩ := Set.mem_add.1 hq
    exact ⟨y₀, hy₀, y₁, hy₁, e⟩
  · rw [h]
    exact Set.add_mem_add hy₀ hy₁

/-- The instance of the block: the closed unit disc of `ℝ²` is not a sum of two segments
(Déf. 1). -/
theorem disque_non_somme_segments (a b c d : ℝ × ℝ) :
    ¬ IsSommeConvexes disque ![segment ℝ a b, segment ℝ c d] := by
  intro h
  rw [isSommeConvexes_iff_bijOn] at h
  refine disque_not_somme_core a b c d (fun q hq => ?_) (fun y₀ hy₀ y₁ hy₁ => ?_)
  · obtain ⟨x, hx, hxq⟩ := h.2.surjOn hq
    refine ⟨x 0, hx 0 trivial, x 1, hx 1 trivial, ?_⟩
    rw [← hxq]
    simp [Fin.sum_univ_two]
  · have := h.2.mapsTo (x := ![y₀, y₁]) (fun i _ => by fin_cases i <;> simpa)
    simpa [Fin.sum_univ_two] using this

/-- The square as a sum of classes (Remarque 1): the class of `[0,1]²` is the sum of the classes
of the two sides. -/
theorem exemple_carre_classes :
    SommeClasses (classe (KE.mk (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
        ((convex_Icc 0 1).prod (convex_Icc 0 1))))
      ![classe (KE.mk (Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) ((convex_Icc 0 1).prod (convex_singleton 0))),
        classe (KE.mk ({(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1) ((convex_singleton 0).prod (convex_Icc 0 1)))]
    := by
  refine ⟨_, ![KE.mk (Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) ((convex_Icc 0 1).prod (convex_singleton 0)),
    KE.mk ({(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1) ((convex_singleton 0).prod (convex_Icc 0 1))], rfl,
    fun i => by fin_cases i <;> rfl, ?_⟩
  have h := exemple_carre_somme
  have e : (fun i => (![KE.mk (Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)})
      ((convex_Icc 0 1).prod (convex_singleton 0)),
      KE.mk ({(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1) ((convex_singleton 0).prod (convex_Icc 0 1))] i).1) =
      ![Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}, {(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1] := by
    funext i; fin_cases i <;> rfl
  rw [e]
  exact h

/-- Remarque 1's « infinité de façons » is met on the square: `[0,1]²` is the sum of infinitely
many families of translates of its two sides. -/
theorem exemple_carre_infinite :
    {V' : Fin 2 → KE (ℝ × ℝ) | (∀ k, classe (V' k) =
        ![classe (KE.mk (Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)})
          ((convex_Icc 0 1).prod (convex_singleton 0))),
          classe (KE.mk ({(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1)
          ((convex_singleton 0).prod (convex_Icc 0 1)))] k) ∧
      IsSommeConvexes (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (fun k => (V' k).1)}.Infinite :=
  remarque1_infinite exemple_carre_classes _ rfl ⟨(0, 0), ⟨⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩⟩⟩ (i := 0) (j := 1) (by decide)

end Benzecri
