import Benzecri.Chapter3.Sommes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Chapter 3 § 2 — subspaces fibring a convex set (Déf. 2–4, Remarque 4, Prop. 3)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal pp. 264–265; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-fibres. Any real vector space `E`, any dimension, no topology.

* **`bzdef:c3s2d2_fibre`** — `benzecri1960_ch3.tex:383` (Déf. 2, l.383–387): `Benzecri.Fibre`.
* **`bzdef:c3s2d3_fibre_cylindriquement`** — `benzecri1960_ch3.tex:389` (Déf. 3, l.389–394):
  `Benzecri.FibreCylindriquement`, its synonym `Benzecri.EstDistingue`; « supplémentaire » is
  `IsCompl`; the bridge to Déf. 1, `sontConjugues_iff_isSommeConvexes`,
  `fibreCylindriquement_iff_isSommeConvexes` (with `L`, `L'` supplementary the Minkowski sum
  `W = L ∩ W + L' ∩ W` is `IsSommeConvexes W ![L ∩ W, L' ∩ W]`); Déf. 3 ⇒ Déf. 2
  (`FibreCylindriquement.fibre`); `0` and `E` are distinguished (`estDistingue_bot`,
  `estDistingue_top`).
* **`bzrem:c3s2r4_fibre_translate`** — `benzecri1960_ch3.tex:396` (Remarque 4, l.396–399):
  `remarque4_fibre_translate` (with the standing hypotheses), from `remarque4_fibre`,
  `remarque4_fibreCylindriquement`, `convex_vadd_span`.
* **`bzprop:c3s2p3_fibre_cylindriquement`** — `benzecri1960_ch3.tex:401` (Prop. 3, l.401–411,
  proof l.422–450): `prop3_fibre_cylindriquement` (both parts), from `prop3_1` (1°, no spanning
  hypothesis needed), `prop3_2` (2°, `∃!`), `prop3_2_involution` (the involution `conjugueDistingue`
  on the distinguished subspaces), `conjugue`, `conjugue_eq`, `conjugue_conjugue`; the two
  lemmas of the printed proof `eq_zero_of_vadd_subset`, `eq_zero_of_vadd_eq`.
* **`bzdef:c3s2d4_conjugues`** — `benzecri1960_ch3.tex:415` (Déf. 4, l.415–418):
  `Benzecri.SontConjugues`, as printed (no supplementarity; see SCOPE and
  `demiDroite_conjugues_non_supplementaires`).

Instances: the cube `[−1,1]ⁿ` (`cube_coord_distingue`; `[−1,1]³`: `cube3_coord_distingue`) —
every coordinate subspace is distinguished, its conjugate the complementary coordinate subspace,
the only one; the closed unit ball of a real inner product space — only `0` and `E` are
distinguished (`boule_estDistingue_iff`), only `0` and `E` fibre it (`boule_fibre_iff`); the strip
`ℝ × [0,1]` (contains lines) — the horizontal axis has two conjugates (`bande_deux_conjugues`);
the cone `{|x| ≤ y}` (no line, half-lines) — fibred by the vertical axis, not cylindrically
(`cone_fibre_non_cylindrique`); the point `{0} ⊂ ℝ²` (not spanning) — two conjugates
(`point_deux_conjugues`).

> **Définition 2.** Soient $E$ un espace vectoriel, $W$ un convexe de $E$ contenant l'origine; on
> dit qu'un sous-espace vectoriel $L$ de $E$ *fibre* $W$ si l'intersection de tout translaté $L'$
> de $L$ avec $W$ est, soit $\emptyset$, soit un translaté de $L\cap W$.
>
> **Définition 3.** Soit $W$ un convexe de $E$, engendrant $E$, et contenant l'origine; on dit
> qu'un sous-espace $L$ de $E$ *fibre $W$ cylindriquement*, ou encore que $L$ est *distingué
> relativement à $W$*, s'il existe un sous-espace $L'$ de $E$, supplémentaire de $L$, et tel que
> $W=L\cap W+L'\cap W$.
>
> **Remarque.** Si $L$ fibre $W$ (resp. fibre cylindriquement $W$), $L$ fibre (resp. fibre
> cylindriquement) tout translaté de $W$ contenant l'origine.
>
> **Proposition 3.** 1° Si $W$ ne contient aucune demi-droite, tout sous-espace $L$ qui fibre $W$
> le fibre cylindriquement; 2° Si $W$ ne contient aucune droite, à tout $L$ qui fibre
> cylindriquement $W$ correspond un $L'$ et un seul qui soit supplémentaire de $L$ et tel que
> $W=L\cap W+L'\cap W$. La correspondance entre $L$ et $L'$ est une involution sur l'ensemble
> des sous-espaces distingués relativement à $W$.
>
> **Définition 4.** On dit que deux sous-espaces $L$ et $L'$ sont *conjugués* relativement au
> convexe $W$ si $W=L\cap W+L'\cap W$.

## The proof formalized

1°: `U = L ∩ W`, `U' = {b | b + U ⊆ W}` (« les homologues de l'origine dans tous les translatés
de `U` contenus dans `W` »); with no half-line, `t + U ⊆ U` forces `t = 0`
(`eq_zero_of_vadd_subset`), so the translate of `U` in a fibre is unique, every `w ∈ W` is
`b + u` uniquely, `U'` is convex, and `span U'` meets `L` at `0` (`exists_smul_sub_of_mem_span`:
an element of the span of a convex `C ∋ 0` is `r (c₁ − c₂)`); `L'` is `span U'` plus a
supplementary of `L ⊔ span U'`. The printed proof asserts that the support of `U'` is
supplementary to « le support `L` de `U` »; the formalized proof needs neither that `U` spans
`L` nor that `W` spans `E`. 2°: the fibre of `W = U + L' ∩ W` through `y ∈ L' ∩ W` is `y + U`
(`inter_vadd_eq_of_conjugues`); with no line, `t + U = U` forces `t = 0` (`eq_zero_of_vadd_eq`),
so two conjugates have the same `L' ∩ W`, whose span is `L'` when `W` spans `E`
(`span_inter_eq_of_conjugues`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E` un espace vectoriel (real) | ✓ carried: any real vector space, any dimension |
| Déf. 2: `W` convexe contenant l'origine | ✓ carried by the theorems (the predicate `Fibre` is Déf. 2's condition alone) |
| Déf. 3: `W` convexe, engendrant `E`, contenant l'origine | ✓ carried by the theorems that use them; « engendrant » is `Submodule.span ℝ W = ⊤` |
| Déf. 3: `L'` supplémentaire de `L` | ✓ `IsCompl L L'` |
| Rem. 4: « tout translaté de `W` contenant l'origine » | ✓ `0 ∈ c +ᵥ W`; the standing hypotheses pass to `c +ᵥ W` (`remarque4_fibre_translate`) |
| Prop. 3 1°: `W` (Déf. 3's) with no half-line, `L` fibring `W` | ⚠ weakened: `W` convex, `0 ∈ W`, no half-line; spanning not used |
| Prop. 3 2°: `W` (Déf. 3's) with no line | ✓ carried: convex, `0 ∈ W`, spanning, no line; spanning is used (`point_deux_conjugues`), no line is used (`bande_deux_conjugues`) |
| « demi-droite », « droite » | `ContientDemiDroite` (closed half-line `x + ℝ₊ v`, `v ≠ 0`; the open one is equivalent, `contientDemiDroite_iff_ouverte`), `ContientDroite` |

## SCOPE (disclosed)

* Déf. 4 is formalized as printed: `W = L ∩ W + L' ∩ W`, a Minkowski sum, with no supplementarity.
  So printed, it admits non-supplementary pairs even for `W` convex, spanning, without lines:
  `ℝ` is conjugate to itself relative to `[0, ∞[` (`demiDroite_conjugues_non_supplementaires`).
  What « Cette proposition légitimera la » and the later uses (Théorème 1's « couples de
  sous-espaces distingués conjugués », Théorème 2's « on prend comme complémentaire le
  conjugué ») point to is the supplementary pair `IsCompl L L' ∧ SontConjugues W L L'`, the pair
  of Prop. 3 2°; both are available (a question in the REPORT).
* The `[sic]` « `U(W)` » (l.448) is read « `U(w)` », as the comment says.
* Prop. 3 1° is proved with no spanning hypothesis (stronger than the statement).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function
open scoped Pointwise

namespace Benzecri

section Fibres

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Half-lines and lines -/

/-- `W` contains a (closed) half-line `{x + t v | t ≥ 0}`, `v ≠ 0`. -/
def ContientDemiDroite (W : Set E) : Prop :=
  ∃ x v : E, v ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → x + t • v ∈ W

/-- `W` contains a line `{x + t v | t ∈ ℝ}`, `v ≠ 0`. -/
def ContientDroite (W : Set E) : Prop :=
  ∃ x v : E, v ≠ 0 ∧ ∀ t : ℝ, x + t • v ∈ W

/-! ### Déf. 2, 3, 4 -/

/-- **Déf. 2.** The subspace `L` *fibres* `W`: the intersection of every translate `a + L` of `L`
with `W` is either empty or a translate of `L ∩ W`. (The standing hypotheses of Déf. 2, `W`
convex containing the origin, are carried by the theorems.) -/
def Fibre (W : Set E) (L : Submodule ℝ E) : Prop :=
  ∀ a : E, (a +ᵥ (L : Set E)) ∩ W = ∅ ∨ ∃ b : E, (a +ᵥ (L : Set E)) ∩ W = b +ᵥ ((L : Set E) ∩ W)

/-- **Déf. 4.** `L` and `L'` are *conjugate* relative to `W`: `W = L ∩ W + L' ∩ W` (a Minkowski
sum, as printed; no supplementarity is printed in Déf. 4). -/
def SontConjugues (W : Set E) (L L' : Submodule ℝ E) : Prop :=
  W = (L : Set E) ∩ W + (L' : Set E) ∩ W

/-- **Déf. 3.** `L` *fibres `W` cylindrically*: there is a subspace `L'` supplementary to `L`
(`IsCompl L L'`) with `W = L ∩ W + L' ∩ W`. (The standing hypotheses of Déf. 3, `W` convex,
spanning `E`, containing the origin, are carried by the theorems.) -/
def FibreCylindriquement (W : Set E) (L : Submodule ℝ E) : Prop :=
  ∃ L' : Submodule ℝ E, IsCompl L L' ∧ SontConjugues W L L'

/-- **Déf. 3.** « `L` est distingué relativement à `W` », a synonym of `FibreCylindriquement`. -/
abbrev EstDistingue (W : Set E) (L : Submodule ℝ E) : Prop := FibreCylindriquement W L

/-! ### Elementary lemmas -/

/-- Déf. 4 is symmetric in `L`, `L'`. -/
theorem SontConjugues.symm {W : Set E} {L L' : Submodule ℝ E} (h : SontConjugues W L L') :
    SontConjugues W L' L := by
  unfold SontConjugues
  conv_lhs => rw [h]
  exact add_comm _ _

theorem contientDemiDroite_iff_ouverte (W : Set E) :
    ContientDemiDroite W ↔ ∃ x v : E, v ≠ 0 ∧ ∀ t : ℝ, 0 < t → x + t • v ∈ W := by
  constructor
  · rintro ⟨x, v, hv, h⟩
    exact ⟨x, v, hv, fun t ht => h t ht.le⟩
  · rintro ⟨x, v, hv, h⟩
    refine ⟨x + v, v, hv, fun t ht => ?_⟩
    have := h (1 + t) (by linarith)
    rwa [add_smul, one_smul, ← add_assoc] at this

theorem ContientDroite.contientDemiDroite {W : Set E} (h : ContientDroite W) :
    ContientDemiDroite W := by
  obtain ⟨x, v, hv, h⟩ := h
  exact ⟨x, v, hv, fun t _ => h t⟩

theorem vadd_submodule_eq {L : Submodule ℝ E} {a b : E} (h : a - b ∈ L) :
    a +ᵥ (L : Set E) = b +ᵥ (L : Set E) := by
  ext x
  simp only [mem_vadd_iff_sub_mem, SetLike.mem_coe]
  constructor
  · intro hx
    have := L.add_mem hx h
    rwa [sub_add_sub_cancel] at this
  · intro hx
    have := L.sub_mem hx h
    rwa [sub_sub_sub_cancel_right] at this

theorem eq_of_add_eq_add {L L' : Submodule ℝ E} (h : Disjoint L L') {x y x' y' : E}
    (hx : x ∈ L) (hy : y ∈ L) (hx' : x' ∈ L') (hy' : y' ∈ L') (he : x + x' = y + y') :
    x = y ∧ x' = y' := by
  have h1 : x - y ∈ L := L.sub_mem hx hy
  have h2 : x - y ∈ L' := by
    have : x - y = y' - x' := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm y' y, ← he, add_comm]
    rw [this]; exact L'.sub_mem hy' hx'
  have h0 := Submodule.disjoint_def.1 h _ h1 h2
  refine ⟨sub_eq_zero.1 h0, ?_⟩
  have : x' = (x + x') - x := by abel
  rw [this, he, sub_eq_zero.1 h0]; abel

/-- If a translate `t + C` of a convex set `C` lies in `C`, then `C` contains the half-line
`x + ℝ₊ t` through each of its points. -/
theorem add_smul_mem_of_vadd_subset {C : Set E} (hC : Convex ℝ C) {x t : E} (hx : x ∈ C)
    (ht : t +ᵥ C ⊆ C) {s : ℝ} (hs : 0 ≤ s) : x + s • t ∈ C := by
  have hn : ∀ n : ℕ, x + (n : ℝ) • t ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have := ht (Set.vadd_mem_vadd_set (a := t) ih)
      rw [vadd_eq_add] at this
      convert this using 1
      push_cast
      rw [add_smul, one_smul]; abel
  set n : ℕ := ⌈s⌉₊ + 1 with hndef
  have hnpos : (0 : ℝ) < n := by rw [hndef]; positivity
  have hsn : s ≤ n := by
    rw [hndef]; push_cast; linarith [Nat.le_ceil s]
  have hmem : s / n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs hnpos.le, (div_le_one hnpos).2 hsn⟩
  have := hC.add_smul_mem hx (hn n) hmem
  rwa [smul_smul, div_mul_cancel₀ s hnpos.ne'] at this

/-- The first lemma of the proof of Prop. 3: « si un convexe `C` ne contient aucune demi-droite,
il n'existe pas de translation `t` autre que la translation nulle, qui transforme `C` en un convexe
`t(C) ⊂ C` » (`C` nonempty). -/
theorem eq_zero_of_vadd_subset {C : Set E} (hC : Convex ℝ C) {x t : E} (hx : x ∈ C)
    (hd : ¬ ContientDemiDroite C) (ht : t +ᵥ C ⊆ C) : t = 0 := by
  by_contra htne
  exact hd ⟨x, t, htne, fun s hs => add_smul_mem_of_vadd_subset hC hx ht hs⟩

/-- The second lemma of the proof of Prop. 3: « si un convexe `C` ne contient aucune droite, il
n'existe pas de translation `t` non nulle qui transforme `C` en un convexe `t(C) = C` »
(`C` nonempty). -/
theorem eq_zero_of_vadd_eq {C : Set E} (hC : Convex ℝ C) {x t : E} (hx : x ∈ C)
    (hd : ¬ ContientDroite C) (ht : t +ᵥ C = C) : t = 0 := by
  have ht' : (-t) +ᵥ C ⊆ C := by
    conv_lhs => rw [← ht]
    rw [vadd_vadd, neg_add_cancel, zero_vadd]
  by_contra htne
  refine hd ⟨x, t, htne, fun s => ?_⟩
  rcases le_total 0 s with hs | hs
  · exact add_smul_mem_of_vadd_subset hC hx ht.subset hs
  · have := add_smul_mem_of_vadd_subset hC hx ht' (neg_nonneg.2 hs)
    rwa [neg_smul_neg] at this

/-- An element of the span of a convex set `C ∋ 0` is `r (c₁ − c₂)`, `r > 0`, `c₁, c₂ ∈ C`. -/
theorem exists_smul_sub_of_mem_span {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {x : E}
    (hx : x ∈ Submodule.span ℝ C) :
    ∃ r : ℝ, 0 < r ∧ ∃ c₁ ∈ C, ∃ c₂ ∈ C, x = r • (c₁ - c₂) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, y, hy, 0, h0, by simp⟩
  | zero => exact ⟨1, one_pos, 0, h0, 0, h0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, c₁, hc₁, c₂, hc₂, rfl⟩ := hy
    obtain ⟨s, hs, d₁, hd₁, d₂, hd₂, rfl⟩ := hz
    have hrs : 0 < r + s := add_pos hr hs
    have ha : 0 ≤ r / (r + s) := div_nonneg hr.le hrs.le
    have hb : 0 ≤ s / (r + s) := div_nonneg hs.le hrs.le
    have hab : r / (r + s) + s / (r + s) = 1 := by field_simp
    refine ⟨r + s, hrs, (r / (r + s)) • c₁ + (s / (r + s)) • d₁, hC hc₁ hd₁ ha hb hab,
      (r / (r + s)) • c₂ + (s / (r + s)) • d₂, hC hc₂ hd₂ ha hb hab, ?_⟩
    have e1 : (r + s) * (r / (r + s)) = r := by field_simp
    have e2 : (r + s) * (s / (r + s)) = s := by field_simp
    simp only [smul_sub, smul_add, smul_smul, e1, e2]
    abel
  | smul a y _ hy =>
    obtain ⟨r, hr, c₁, hc₁, c₂, hc₂, rfl⟩ := hy
    rcases lt_trichotomy a 0 with ha | ha | ha
    · refine ⟨-a * r, mul_pos (neg_pos.2 ha) hr, c₂, hc₂, c₁, hc₁, ?_⟩
      rw [smul_smul, ← neg_sub c₁ c₂, smul_neg, ← neg_smul]; ring_nf
    · exact ⟨1, one_pos, 0, h0, 0, h0, by simp [ha]⟩
    · exact ⟨a * r, mul_pos ha hr, c₁, hc₁, c₂, hc₂, by rw [smul_smul]⟩

/-! ### The bridge to Déf. 1 -/

/-- Déf. 1 gives Déf. 4's Minkowski sum (no supplementarity needed). -/
theorem IsSommeConvexes.sontConjugues {W : Set E} {L L' : Submodule ℝ E}
    (h : IsSommeConvexes W ![(L : Set E) ∩ W, (L' : Set E) ∩ W]) : SontConjugues W L L' := by
  obtain ⟨-, h⟩ := (isSommeConvexes_iff_bijOn _ _).1 h
  unfold SontConjugues
  conv_lhs => rw [← h.image_eq]
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

/-- With `L`, `L'` supplementary, Déf. 3/4's Minkowski sum `W = L ∩ W + L' ∩ W` is a sum in
Déf. 1's sense. -/
theorem sontConjugues_iff_isSommeConvexes {W : Set E} (hW : Convex ℝ W) {L L' : Submodule ℝ E}
    (h : IsCompl L L') :
    SontConjugues W L L' ↔ IsSommeConvexes W ![(L : Set E) ∩ W, (L' : Set E) ∩ W] := by
  refine ⟨fun hc => ?_, IsSommeConvexes.sontConjugues⟩
  rw [isSommeConvexes_iff_bijOn]
  refine ⟨fun i => ?_, fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
  · fin_cases i
    · exact L.convex.inter hW
    · exact L'.convex.inter hW
  · have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simp only [Fin.sum_univ_two]
    rw [hc]
    exact Set.add_mem_add (by simpa using h0) (by simpa using h1)
  · have hx0 : x 0 ∈ (L : Set E) ∩ W := by simpa using hx 0 trivial
    have hx1 : x 1 ∈ (L' : Set E) ∩ W := by simpa using hx 1 trivial
    have hy0 : y 0 ∈ (L : Set E) ∩ W := by simpa using hy 0 trivial
    have hy1 : y 1 ∈ (L' : Set E) ∩ W := by simpa using hy 1 trivial
    have hxy' : x 0 + x 1 = y 0 + y 1 := by simpa [Fin.sum_univ_two] using hxy
    obtain ⟨e0, e1⟩ := eq_of_add_eq_add h.disjoint hx0.1 hy0.1 hx1.1 hy1.1 hxy'
    funext k
    fin_cases k
    · exact e0
    · exact e1
  · rw [hc] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    refine ⟨![a, b], fun i _ => ?_, by simp [Fin.sum_univ_two]⟩
    fin_cases i
    · simpa using ha
    · simpa using hb

/-- Déf. 3 through Déf. 1. -/
theorem fibreCylindriquement_iff_isSommeConvexes {W : Set E} (hW : Convex ℝ W)
    {L : Submodule ℝ E} :
    FibreCylindriquement W L ↔ ∃ L' : Submodule ℝ E, IsCompl L L' ∧
      IsSommeConvexes W ![(L : Set E) ∩ W, (L' : Set E) ∩ W] := by
  constructor
  · rintro ⟨L', h, hc⟩
    exact ⟨L', h, (sontConjugues_iff_isSommeConvexes hW h).1 hc⟩
  · rintro ⟨L', h, hc⟩
    exact ⟨L', h, (sontConjugues_iff_isSommeConvexes hW h).2 hc⟩

/-! ### Structure of a cylindrical decomposition -/

/-- The fibre of `W = L ∩ W + L' ∩ W` through a point `y` of `L' ∩ W` is `y + L ∩ W`. -/
theorem inter_vadd_eq_of_conjugues {W : Set E} {L L' : Submodule ℝ E} (h : Disjoint L L')
    (hW : SontConjugues W L L') {y : E} (hy : y ∈ (L' : Set E) ∩ W) :
    (y +ᵥ (L : Set E)) ∩ W = y +ᵥ ((L : Set E) ∩ W) := by
  ext x
  constructor
  · rintro ⟨hxL, hxW⟩
    rw [mem_vadd_iff_sub_mem] at hxL
    have hxW' := hxW
    rw [hW, Set.mem_add] at hxW'
    obtain ⟨u, hu, z, hz, hx⟩ := hxW'
    have he : u + z = (x - y) + y := by rw [hx]; abel
    obtain ⟨e1, -⟩ := eq_of_add_eq_add h hu.1 hxL hz.1 hy.1 he
    rw [mem_vadd_iff_sub_mem]
    exact ⟨hxL, e1 ▸ hu.2⟩
  · intro hx
    rw [mem_vadd_iff_sub_mem] at hx
    refine ⟨by rw [mem_vadd_iff_sub_mem]; exact hx.1, ?_⟩
    rw [hW]
    have := Set.add_mem_add hx hy
    rwa [sub_add_cancel] at this

/-- A subspace fibring `W` cylindrically fibres it (Déf. 3 ⇒ Déf. 2), with no hypothesis. -/
theorem FibreCylindriquement.fibre {W : Set E} {L : Submodule ℝ E}
    (h : FibreCylindriquement W L) : Fibre W L := by
  obtain ⟨L', h, hc⟩ := h
  intro a
  by_cases hne : ((a +ᵥ (L : Set E)) ∩ W).Nonempty
  · obtain ⟨x, hxa, hxW⟩ := hne
    rw [hc, Set.mem_add] at hxW
    obtain ⟨u, hu, z, hz, rfl⟩ := hxW
    rw [mem_vadd_iff_sub_mem] at hxa
    have haz : a - z ∈ L := by
      have := L.sub_mem hu.1 hxa
      convert this using 1; abel
    right
    exact ⟨z, by rw [vadd_submodule_eq haz, inter_vadd_eq_of_conjugues h.disjoint hc hz]⟩
  · left
    exact Set.not_nonempty_iff_eq_empty.1 hne

/-- In `W = L ∩ W + L' ∩ W` with `L`, `L'` supplementary and `W` spanning `E`, the support
of `L' ∩ W` is `L'`. -/
theorem span_inter_eq_of_conjugues {W : Set E} {L L' : Submodule ℝ E} (h : IsCompl L L')
    (hW : SontConjugues W L L') (hspan : Submodule.span ℝ W = ⊤) :
    Submodule.span ℝ ((L' : Set E) ∩ W) = L' := by
  apply le_antisymm
  · exact Submodule.span_le.2 Set.inter_subset_left
  · intro x hx
    have hle : Submodule.span ℝ W ≤
        Submodule.span ℝ ((L : Set E) ∩ W) ⊔ Submodule.span ℝ ((L' : Set E) ∩ W) := by
      refine Submodule.span_le.2 fun w hw => ?_
      rw [hW, Set.mem_add] at hw
      obtain ⟨u, hu, u', hu', rfl⟩ := hw
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span hu))
        (Submodule.mem_sup_right (Submodule.subset_span hu'))
    have hx' : x ∈ Submodule.span ℝ ((L : Set E) ∩ W) ⊔ Submodule.span ℝ ((L' : Set E) ∩ W) :=
      hle (hspan ▸ Submodule.mem_top)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
    have haL : a ∈ L := Submodule.span_le.2 Set.inter_subset_left ha
    have hbL : b ∈ L' := Submodule.span_le.2 Set.inter_subset_left hb
    have he : a + b = 0 + x := by rw [hab, zero_add]
    obtain ⟨-, e2⟩ := eq_of_add_eq_add h.disjoint haL L.zero_mem hbL hx he
    exact e2 ▸ hb

/-- `0` and `E` are distinguished relative to any `W ∋ 0`. -/
theorem estDistingue_bot {W : Set E} (h0 : (0 : E) ∈ W) : EstDistingue W ⊥ := by
  refine ⟨⊤, isCompl_bot_top, ?_⟩
  ext x
  simp only [Submodule.bot_coe, Submodule.top_coe, Set.univ_inter, Set.mem_add,
    Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro hx; exact ⟨0, ⟨rfl, h0⟩, x, hx, zero_add x⟩
  · rintro ⟨a, ⟨rfl, -⟩, b, hb, rfl⟩; rwa [zero_add]

theorem estDistingue_top {W : Set E} (h0 : (0 : E) ∈ W) : EstDistingue W ⊤ := by
  refine ⟨⊥, isCompl_top_bot, ?_⟩
  ext x
  simp only [Submodule.bot_coe, Submodule.top_coe, Set.univ_inter, Set.mem_add,
    Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · intro hx; exact ⟨x, hx, 0, ⟨rfl, h0⟩, add_zero x⟩
  · rintro ⟨a, ha, b, ⟨rfl, -⟩, rfl⟩; rwa [add_zero]

/-! ### Remarque 4 -/

/-- The translate `c + W` of a convex set spanning `E` and containing `0` is convex and spans
`E` (the standing hypotheses of Déf. 2 and 3 pass to the translates containing the origin). -/
theorem convex_vadd_span {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (c : E) :
    Convex ℝ (c +ᵥ W) ∧ Submodule.span ℝ (c +ᵥ W) = ⊤ := by
  refine ⟨hW.vadd c, eq_top_iff.2 ?_⟩
  rw [← hspan]
  refine Submodule.span_le.2 fun w hw => ?_
  have h1 : c + w ∈ c +ᵥ W := Set.vadd_mem_vadd_set hw
  have h2 : c + 0 ∈ c +ᵥ W := Set.vadd_mem_vadd_set h0
  have := Submodule.sub_mem _ (Submodule.subset_span (R := ℝ) h1) (Submodule.subset_span h2)
  simpa using this

/-- **Remarque 4**, for Déf. 2: if `L` fibres `W`, `L` fibres every translate of `W` containing
the origin. -/
theorem remarque4_fibre {W : Set E} {L : Submodule ℝ E} (hL : Fibre W L) {c : E}
    (hc : (0 : E) ∈ c +ᵥ W) : Fibre (c +ᵥ W) L := by
  have key : ∀ a : E, (a +ᵥ (L : Set E)) ∩ (c +ᵥ W) = c +ᵥ (((a - c) +ᵥ (L : Set E)) ∩ W) := by
    intro a
    ext x
    simp only [Set.mem_inter_iff, mem_vadd_iff_sub_mem, sub_sub_sub_cancel_right]
  rw [mem_vadd_iff_sub_mem] at hc
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : E, (((0 : E) - c) +ᵥ (L : Set E)) ∩ W = b₀ +ᵥ ((L : Set E) ∩ W) := by
    rcases hL (0 - c) with he | hb
    · exfalso
      have : (0 : E) - c ∈ (((0 : E) - c) +ᵥ (L : Set E)) ∩ W :=
        ⟨by rw [mem_vadd_iff_sub_mem, sub_self]; exact L.zero_mem, hc⟩
      rw [he] at this; exact this
    · exact hb
  have hL0 : (L : Set E) ∩ (c +ᵥ W) = (c + b₀) +ᵥ ((L : Set E) ∩ W) := by
    rw [← zero_vadd E (L : Set E), key 0, hb₀, vadd_vadd, zero_vadd]
  intro a
  rcases hL (a - c) with he | ⟨b, hb⟩
  · left; rw [key a, he, Set.vadd_set_empty]
  · right
    refine ⟨b - b₀, ?_⟩
    rw [key a, hb, hL0, vadd_vadd, vadd_vadd]
    congr 1; abel

/-- **Remarque 4**, for Déf. 3: if `L` fibres `W` cylindrically, `L` fibres cylindrically every
translate of `W` containing the origin. -/
theorem remarque4_fibreCylindriquement {W : Set E} {L : Submodule ℝ E}
    (hL : FibreCylindriquement W L) {c : E} (hc : (0 : E) ∈ c +ᵥ W) :
    FibreCylindriquement (c +ᵥ W) L := by
  obtain ⟨L', h, hcW⟩ := hL
  refine ⟨L', h, ?_⟩
  rw [mem_vadd_iff_sub_mem] at hc
  have hc' := hc
  rw [hcW, Set.mem_add] at hc'
  obtain ⟨u₀, hu₀, u₀', hu₀', hsum⟩ := hc'
  have hcc : c = -(u₀ + u₀') := by rw [hsum]; abel
  subst hcc
  have hd := h.disjoint
  ext x
  constructor
  · intro hx
    rw [mem_vadd_iff_sub_mem, hcW, Set.mem_add] at hx
    obtain ⟨u, hu, u', hu', hx⟩ := hx
    refine ⟨u - u₀, ⟨L.sub_mem hu.1 hu₀.1, ?_⟩, u' - u₀', ⟨L'.sub_mem hu'.1 hu₀'.1, ?_⟩, ?_⟩
    · rw [mem_vadd_iff_sub_mem, hcW]
      have := Set.add_mem_add hu hu₀'
      convert this using 1; abel
    · rw [mem_vadd_iff_sub_mem, hcW]
      have := Set.add_mem_add hu₀ hu'
      convert this using 1; abel
    · have : x = (u + u') + -(u₀ + u₀') := by rw [hx]; abel
      rw [this]; abel_nf
  · intro hx
    rw [Set.mem_add] at hx
    obtain ⟨p, ⟨hpL, hpW⟩, q, ⟨hqL, hqW⟩, rfl⟩ := hx
    rw [mem_vadd_iff_sub_mem, hcW, Set.mem_add] at hpW hqW
    obtain ⟨a, ha, a', ha', hpa⟩ := hpW
    obtain ⟨b, hb, b', hb', hqb⟩ := hqW
    have e1 : a + a' = (p + u₀) + u₀' := by rw [hpa]; abel
    obtain ⟨ea, -⟩ := eq_of_add_eq_add hd ha.1 (L.add_mem hpL hu₀.1) ha'.1 hu₀'.1 e1
    have e2 : b + b' = u₀ + (q + u₀') := by rw [hqb]; abel
    obtain ⟨-, eb⟩ := eq_of_add_eq_add hd hb.1 hu₀.1 hb'.1 (L'.add_mem hqL hu₀'.1) e2
    rw [mem_vadd_iff_sub_mem, hcW]
    have := Set.add_mem_add ha hb'
    rw [ea, eb] at this
    convert this using 1; abel

/-- **Remarque 4**, assembled with the standing hypotheses: for `W` convex containing `0` and a
translate `c + W` containing `0`, if `L` fibres `W` then `c + W` is convex and fibred by `L`; if
moreover `W` spans `E` and `L` fibres `W` cylindrically, then `c + W` spans `E` and is fibred
cylindrically by `L`. -/
theorem remarque4_fibre_translate {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    {L : Submodule ℝ E} {c : E} (hc : (0 : E) ∈ c +ᵥ W) :
    (Fibre W L → Convex ℝ (c +ᵥ W) ∧ Fibre (c +ᵥ W) L) ∧
    (Submodule.span ℝ W = ⊤ → FibreCylindriquement W L →
      Convex ℝ (c +ᵥ W) ∧ Submodule.span ℝ (c +ᵥ W) = ⊤ ∧ FibreCylindriquement (c +ᵥ W) L) :=
  ⟨fun hL => ⟨hW.vadd c, remarque4_fibre hL hc⟩, fun hspan hL =>
    ⟨hW.vadd c, (convex_vadd_span hW h0 hspan c).2, remarque4_fibreCylindriquement hL hc⟩⟩

/-! ### Prop. 3 -/

/-- **Prop. 3, 1°.** If the convex set `W ∋ 0` contains no half-line, every subspace `L` which
fibres `W` fibres it cylindrically. (No spanning hypothesis is needed.) -/
theorem prop3_1 {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hd : ¬ ContientDemiDroite W) {L : Submodule ℝ E} (hL : Fibre W L) :
    FibreCylindriquement W L := by
  set U : Set E := (L : Set E) ∩ W with hUdef
  have hUc : Convex ℝ U := L.convex.inter hW
  have h0U : (0 : E) ∈ U := ⟨L.zero_mem, h0⟩
  have hdU : ¬ ContientDemiDroite U := fun ⟨x, v, hv, h⟩ =>
    hd ⟨x, v, hv, fun t ht => (h t ht).2⟩
  -- a translate of `U` inside another one is that one
  have key : ∀ b b' : E, b' +ᵥ U ⊆ b +ᵥ U → b' = b := by
    intro b b' h
    have hsub : (b' - b) +ᵥ U ⊆ U := by
      rintro x ⟨y, hy, rfl⟩
      have := h (Set.vadd_mem_vadd_set (a := b') hy)
      rw [mem_vadd_iff_sub_mem] at this
      convert this using 1
      simp only [vadd_eq_add]; abel
    exact sub_eq_zero.1 (eq_zero_of_vadd_subset hUc h0U hdU hsub)
  -- `U'`: the homologues of the origin in the translates of `U` contained in `W`
  set U' : Set E := {b | b +ᵥ U ⊆ W} with hU'def
  have hbW : ∀ b ∈ U', b ∈ W := fun b hb => by
    have := hb (Set.vadd_mem_vadd_set (a := b) h0U)
    simpa using this
  have h0U' : (0 : E) ∈ U' := by
    show (0 : E) +ᵥ U ⊆ W
    rw [zero_vadd]; exact Set.inter_subset_right
  have hU'c : Convex ℝ U' := by
    intro b₁ hb₁ b₂ hb₂ α β hα hβ hαβ
    rintro x ⟨u, hu, rfl⟩
    have := hW (hb₁ (Set.vadd_mem_vadd_set (a := b₁) hu))
      (hb₂ (Set.vadd_mem_vadd_set (a := b₂) hu)) hα hβ hαβ
    convert this using 1
    simp only [vadd_eq_add, smul_add]
    rw [show α • b₁ + β • b₂ + u = α • b₁ + β • b₂ + (α + β) • u by rw [hαβ, one_smul],
      add_smul]
    abel
  -- the fibre through a point of `U'`
  have fib : ∀ b ∈ U', (b +ᵥ (L : Set E)) ∩ W = b +ᵥ U := by
    intro b hb
    rcases hL b with he | ⟨c, hc⟩
    · exfalso
      have : b ∈ (b +ᵥ (L : Set E)) ∩ W :=
        ⟨by rw [mem_vadd_iff_sub_mem, sub_self]; exact L.zero_mem, hbW b hb⟩
      rw [he] at this; exact this
    · have hsub : b +ᵥ U ⊆ c +ᵥ U := by
        rw [← hc]
        rintro x ⟨y, hy, rfl⟩
        refine ⟨?_, hb (Set.vadd_mem_vadd_set hy)⟩
        rw [mem_vadd_iff_sub_mem]; simp only [vadd_eq_add, add_sub_cancel_left]; exact hy.1
      rw [hc, key c b hsub]
  -- every point of `W` is `b + u`
  have dec : ∀ w ∈ W, ∃ b ∈ U', ∃ u ∈ U, w = b + u := by
    intro w hw
    rcases hL w with he | ⟨c, hc⟩
    · exfalso
      have : w ∈ (w +ᵥ (L : Set E)) ∩ W :=
        ⟨by rw [mem_vadd_iff_sub_mem, sub_self]; exact L.zero_mem, hw⟩
      rw [he] at this; exact this
    · have hw' : w ∈ c +ᵥ U := by
        rw [← hc]
        exact ⟨by rw [mem_vadd_iff_sub_mem, sub_self]; exact L.zero_mem, hw⟩
      have hcU' : c ∈ U' := by
        intro x hx; rw [← hc] at hx; exact hx.2
      obtain ⟨u, hu, rfl⟩ := hw'
      exact ⟨c, hcU', u, hu, rfl⟩
  -- uniqueness of the decomposition
  have uniq : ∀ b₁ ∈ U', ∀ b₂ ∈ U', b₁ - b₂ ∈ L → b₁ = b₂ := by
    intro b₁ h₁ b₂ h₂ h₁₂
    have e := fib b₁ h₁
    rw [vadd_submodule_eq h₁₂, fib b₂ h₂] at e
    exact key b₂ b₁ e.symm.le
  -- the support of `U'` meets `L` at `0`
  set S : Submodule ℝ E := Submodule.span ℝ U' with hSdef
  have hLS : ∀ x ∈ L, x ∈ S → x = 0 := by
    intro x hxL hxS
    obtain ⟨r, hr, c₁, hc₁, c₂, hc₂, rfl⟩ := exists_smul_sub_of_mem_span hU'c h0U' hxS
    have h12 : c₁ - c₂ ∈ L := by
      have := L.smul_mem r⁻¹ hxL
      rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this
    rw [uniq c₁ hc₁ c₂ hc₂ h12, sub_self, smul_zero]
  -- a supplementary of `L` containing `S`
  obtain ⟨M, hM⟩ := Submodule.exists_isCompl (L ⊔ S)
  have hdisj : Disjoint L (S ⊔ M) := by
    rw [Submodule.disjoint_def]
    intro x hxL hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hz' : z ∈ L ⊔ S := by
      have : z = (y + z) - y := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxL) (Submodule.mem_sup_right hy)
    have hz0 : z = 0 := Submodule.disjoint_def.1 hM.disjoint z hz' hz
    subst hz0
    rw [add_zero] at hxL ⊢
    exact hLS y hxL hy
  have hcod : Codisjoint L (S ⊔ M) := by
    rw [codisjoint_iff, ← sup_assoc]; exact codisjoint_iff.1 hM.codisjoint
  refine ⟨S ⊔ M, ⟨hdisj, hcod⟩, ?_⟩
  have hSL' : ∀ b ∈ U', b ∈ S ⊔ M := fun b hb =>
    Submodule.mem_sup_left (Submodule.subset_span hb)
  ext w
  constructor
  · intro hw
    obtain ⟨b, hb, u, hu, rfl⟩ := dec w hw
    rw [Set.mem_add]
    exact ⟨u, hu, b, ⟨hSL' b hb, hbW b hb⟩, add_comm u b⟩
  · intro hw
    rw [Set.mem_add] at hw
    obtain ⟨x, hx, y, ⟨hyL', hyW⟩, rfl⟩ := hw
    obtain ⟨b, hb, u, hu, rfl⟩ := dec y hyW
    have hu0 : u = 0 := by
      refine Submodule.disjoint_def.1 hdisj u hu.1 ?_
      have : u = (b + u) - b := by abel
      rw [this]; exact Submodule.sub_mem _ hyL' (hSL' b hb)
    subst hu0
    rw [add_zero, add_comm]
    exact hb (Set.vadd_mem_vadd_set hx)

/-- **Prop. 3, 2°**, uniqueness: if the convex set `W ∋ 0`, spanning `E`, contains no line, to
every `L` fibring `W` cylindrically corresponds one and only one `L'` supplementary to `L` with
`W = L ∩ W + L' ∩ W`. -/
theorem prop3_2 {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L : Submodule ℝ E}
    (hL : FibreCylindriquement W L) :
    ∃! L' : Submodule ℝ E, IsCompl L L' ∧ SontConjugues W L L' := by
  obtain ⟨L₀, h₀⟩ := hL
  refine ⟨L₀, h₀, ?_⟩
  have hUc : Convex ℝ ((L : Set E) ∩ W) := L.convex.inter hW
  have h0U : (0 : E) ∈ (L : Set E) ∩ W := ⟨L.zero_mem, h0⟩
  have hdU : ¬ ContientDroite ((L : Set E) ∩ W) := fun ⟨x, v, hv, h⟩ =>
    hd ⟨x, v, hv, fun t => (h t).2⟩
  have sub : ∀ L₁ L₂ : Submodule ℝ E, IsCompl L L₁ → SontConjugues W L L₁ → IsCompl L L₂ →
      SontConjugues W L L₂ → (L₁ : Set E) ∩ W ⊆ L₂ := by
    intro L₁ L₂ h₁ c₁ h₂ c₂ y hy
    have hyW := hy.2
    rw [c₂, Set.mem_add] at hyW
    obtain ⟨u, hu, z, hz, hyz⟩ := hyW
    have F₁ := inter_vadd_eq_of_conjugues h₁.disjoint c₁ hy
    have F₂ := inter_vadd_eq_of_conjugues h₂.disjoint c₂ hz
    have hyz' : y - z ∈ L := by rw [← hyz, add_sub_cancel_right]; exact hu.1
    rw [vadd_submodule_eq hyz', F₂] at F₁
    have ht : (-z + y) +ᵥ ((L : Set E) ∩ W) = (L : Set E) ∩ W := by
      rw [← vadd_vadd, ← F₁, vadd_vadd, neg_add_cancel, zero_vadd]
    have := eq_zero_of_vadd_eq hUc h0U hdU ht
    rw [neg_add_eq_zero] at this
    rw [← this]; exact hz.1
  rintro L₁ ⟨h₁, c₁⟩
  have e : (L₁ : Set E) ∩ W = (L₀ : Set E) ∩ W :=
    Set.Subset.antisymm (fun y hy => ⟨sub L₁ L₀ h₁ c₁ h₀.1 h₀.2 hy, hy.2⟩)
      (fun y hy => ⟨sub L₀ L₁ h₀.1 h₀.2 h₁ c₁ hy, hy.2⟩)
  rw [← span_inter_eq_of_conjugues h₁ c₁ hspan, ← span_inter_eq_of_conjugues h₀.1 h₀.2 hspan, e]

open Classical in
/-- The conjugate `L'` of a distinguished subspace `L` (Déf. 4, Prop. 3 2°): a supplementary
`L'` with `W = L ∩ W + L' ∩ W`, chosen; unique when `W` spans `E` and contains no line. -/
noncomputable def conjugue (W : Set E) (L : Submodule ℝ E) : Submodule ℝ E :=
  if h : FibreCylindriquement W L then h.choose else ⊥

theorem conjugue_spec {W : Set E} {L : Submodule ℝ E} (h : FibreCylindriquement W L) :
    IsCompl L (conjugue W L) ∧ SontConjugues W L (conjugue W L) := by
  unfold conjugue
  rw [dif_pos h]
  exact h.choose_spec

/-- The conjugate of a distinguished subspace is distinguished (no hypothesis). -/
theorem estDistingue_conjugue {W : Set E} {L : Submodule ℝ E} (h : EstDistingue W L) :
    EstDistingue W (conjugue W L) := by
  exact ⟨L, (conjugue_spec h).1.symm, (conjugue_spec h).2.symm⟩

theorem conjugue_eq {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L L' : Submodule ℝ E}
    (h : IsCompl L L') (hc : SontConjugues W L L') : conjugue W L = L' := by
  have hL : FibreCylindriquement W L := ⟨L', h, hc⟩
  exact (prop3_2 hW h0 hspan hd hL).unique (conjugue_spec hL) ⟨h, hc⟩

theorem conjugue_conjugue {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) {L : Submodule ℝ E}
    (h : EstDistingue W L) : conjugue W (conjugue W L) = L := by
  exact conjugue_eq hW h0 hspan hd (conjugue_spec h).1.symm (conjugue_spec h).2.symm

/-- The correspondence `L ↦ L'` on the distinguished subspaces. -/
noncomputable def conjugueDistingue (W : Set E) :
    {L : Submodule ℝ E // EstDistingue W L} → {L : Submodule ℝ E // EstDistingue W L} :=
  fun L => ⟨conjugue W L.1, estDistingue_conjugue L.2⟩

/-- **Prop. 3, 2°**, last sentence: « la correspondance entre `L` et `L'` est une involution sur
l'ensemble des sous-espaces distingués relativement à `W` ». -/
theorem prop3_2_involution {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hspan : Submodule.span ℝ W = ⊤) (hd : ¬ ContientDroite W) :
    Function.Involutive (conjugueDistingue W) := by
  rintro ⟨L, hL⟩
  exact Subtype.ext (conjugue_conjugue hW h0 hspan hd hL)

/-- **Prop. 3**, both parts assembled. -/
theorem prop3_fibre_cylindriquement {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W) :
    (¬ ContientDemiDroite W → ∀ L : Submodule ℝ E, Fibre W L → FibreCylindriquement W L) ∧
    (Submodule.span ℝ W = ⊤ → ¬ ContientDroite W →
      (∀ L : Submodule ℝ E, FibreCylindriquement W L →
        ∃! L' : Submodule ℝ E, IsCompl L L' ∧ SontConjugues W L L') ∧
      Function.Involutive (conjugueDistingue W)) := by
  exact ⟨fun hd L hL => prop3_1 hW h0 hd hL, fun hspan hd =>
    ⟨fun L hL => prop3_2 hW h0 hspan hd hL, prop3_2_involution hW h0 hspan hd⟩⟩

end Fibres

/-! ### Instances -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded set contains no half-line. -/
theorem not_contientDemiDroite_of_isBounded {W : Set E} (hW : Bornology.IsBounded W) :
    ¬ ContientDemiDroite W := by
  rintro ⟨x, v, hv, h⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hW
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hx : ‖x‖ ≤ C := by simpa using hC _ (h 0 le_rfl)
  have hC0 : 0 ≤ C := (norm_nonneg x).trans hx
  set t : ℝ := (C + ‖x‖ + 1) / ‖v‖ with htdef
  have ht : 0 ≤ t := div_nonneg (by positivity) hvpos.le
  have h1 := hC _ (h t ht)
  have h2 : ‖t • v‖ = C + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht, htdef, div_mul_cancel₀ _ hvpos.ne']
  have h3 : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    have := norm_sub_le (x + t • v) x
    rwa [add_sub_cancel_left] at this
  linarith

end Normed

/-- The cube `[−1, 1]ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.Icc (-1) 1

/-- The coordinate subspace `ℝ^S` of `ℝⁿ`: the vectors vanishing off `S`. -/
def coord {n : ℕ} (S : Set (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.pi Sᶜ fun _ => ⊥

theorem isCompl_coord {n : ℕ} (S : Set (Fin n)) : IsCompl (coord S) (coord Sᶜ) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    simp only [coord, Submodule.mem_pi, Submodule.mem_bot, Set.mem_compl_iff, not_not] at hx hx'
    funext i
    by_cases hi : i ∈ S
    · exact hx' i hi
    · exact hx i hi
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (fun i => if i ∈ S then x i else 0) + (fun i => if i ∈ S then 0 else x i) := by
      funext i; by_cases hi : i ∈ S <;> simp [hi]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · simp only [coord, Submodule.mem_pi, Submodule.mem_bot, Set.mem_compl_iff]
      intro i hi; simp [hi]
    · simp only [coord, Submodule.mem_pi, Submodule.mem_bot, Set.mem_compl_iff, not_not]
      intro i hi; simp [hi]

theorem cube_sontConjugues {n : ℕ} (S : Set (Fin n)) :
    SontConjugues (cube n) (coord S) (coord Sᶜ) := by
  classical
  ext x
  simp only [cube, Set.mem_add, Set.mem_inter_iff, SetLike.mem_coe, coord, Submodule.mem_pi,
    Submodule.mem_bot, Set.mem_compl_iff, not_not, Set.mem_Icc, Pi.le_def, Pi.neg_apply,
    Pi.one_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => if i ∈ S then x i else 0, ⟨fun i hi => by simp [hi], fun i => ?_, fun i => ?_⟩,
      fun i => if i ∈ S then 0 else x i, ⟨fun i hi => by simp [hi], fun i => ?_, fun i => ?_⟩, ?_⟩
    · by_cases hi : i ∈ S <;> simp [hi, h1 i]
    · by_cases hi : i ∈ S <;> simp [hi, h2 i]
    · by_cases hi : i ∈ S <;> simp [hi, h1 i]
    · by_cases hi : i ∈ S <;> simp [hi, h2 i]
    · funext i; by_cases hi : i ∈ S <;> simp [hi]
  · rintro ⟨a, ⟨ha, ha1, ha2⟩, b, ⟨hb, hb1, hb2⟩, rfl⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ S
    · simp [hb i hi, ha1 i]
    · simp [ha i hi, hb1 i]
    · simp [hb i hi, ha2 i]
    · simp [ha i hi, hb2 i]

theorem cube_hyps (n : ℕ) : Convex ℝ (cube n) ∧ (0 : Fin n → ℝ) ∈ cube n ∧
    Submodule.span ℝ (cube n) = ⊤ ∧ ¬ ContientDemiDroite (cube n) := by
  refine ⟨convex_Icc _ _, ?_, ?_, not_contientDemiDroite_of_isBounded (Metric.isBounded_Icc _ _)⟩
  · simp only [cube, Set.mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply, Pi.zero_apply]
    exact ⟨fun _ => by norm_num, fun _ => by norm_num⟩
  · rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    simp only [cube, Set.mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply, Pi.basisFun_apply]
    refine ⟨fun j => ?_, fun j => ?_⟩ <;> by_cases hj : j = i <;> simp [hj]

/-- The instance: in the cube `[−1, 1]ⁿ` every coordinate subspace is distinguished, and its
conjugate is the complementary coordinate subspace, the only supplementary one with
`W = L ∩ W + L' ∩ W`. -/
theorem cube_coord_distingue {n : ℕ} (S : Set (Fin n)) :
    EstDistingue (cube n) (coord S) ∧ conjugue (cube n) (coord S) = coord Sᶜ ∧
    ∀ L' : Submodule ℝ (Fin n → ℝ), IsCompl (coord S) L' →
      SontConjugues (cube n) (coord S) L' → L' = coord Sᶜ := by
  obtain ⟨hc, h0, hspan, hd⟩ := cube_hyps n
  have hd' : ¬ ContientDroite (cube n) := fun h => hd h.contientDemiDroite
  refine ⟨⟨coord Sᶜ, isCompl_coord S, cube_sontConjugues S⟩,
    conjugue_eq hc h0 hspan hd' (isCompl_coord S) (cube_sontConjugues S), ?_⟩
  intro L' h hL'
  exact (prop3_2 hc h0 hspan hd' ⟨coord Sᶜ, isCompl_coord S, cube_sontConjugues S⟩).unique
    ⟨h, hL'⟩ ⟨isCompl_coord S, cube_sontConjugues S⟩

/-- The cube `[−1, 1]³` of the block. -/
theorem cube3_coord_distingue (S : Set (Fin 3)) :
    EstDistingue (cube 3) (coord S) ∧ conjugue (cube 3) (coord S) = coord Sᶜ :=
  ⟨(cube_coord_distingue S).1, (cube_coord_distingue S).2.1⟩

section Boule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The instance: in the closed unit ball of a real inner product space, the only distinguished
subspaces are `0` and `E`. -/
theorem boule_estDistingue_iff (L : Submodule ℝ E) :
    EstDistingue (Metric.closedBall (0 : E) 1) L ↔ L = ⊥ ∨ L = ⊤ := by
  constructor
  · rintro ⟨L', h, hc⟩
    by_contra hne
    rw [not_or] at hne
    obtain ⟨u, huL, hu⟩ := (Submodule.ne_bot_iff L).1 hne.1
    have hL' : L' ≠ ⊥ := by
      rintro rfl
      exact hne.2 (by simpa using codisjoint_iff.1 h.codisjoint)
    obtain ⟨v, hvL, hv⟩ := (Submodule.ne_bot_iff L').1 hL'
    set a : E := ‖u‖⁻¹ • u
    set b : E := ‖v‖⁻¹ • v
    have ha : ‖a‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu)]
    have hb : ‖b‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    have haW : a ∈ (L : Set E) ∩ Metric.closedBall 0 1 :=
      ⟨L.smul_mem _ huL, by rw [mem_closedBall_zero_iff, ha]⟩
    have hbW : b ∈ (L' : Set E) ∩ Metric.closedBall 0 1 :=
      ⟨L'.smul_mem _ hvL, by rw [mem_closedBall_zero_iff, hb]⟩
    have hbW' : -b ∈ (L' : Set E) ∩ Metric.closedBall 0 1 :=
      ⟨L'.neg_mem hbW.1, by rw [mem_closedBall_zero_iff, norm_neg, hb]⟩
    have h1 : a + b ∈ Metric.closedBall (0 : E) 1 := by rw [hc]; exact Set.add_mem_add haW hbW
    have h2 : a + -b ∈ Metric.closedBall (0 : E) 1 := by rw [hc]; exact Set.add_mem_add haW hbW'
    rw [mem_closedBall_zero_iff] at h1 h2
    rw [← sub_eq_add_neg] at h2
    have hp1 := norm_add_sq_real a b
    have hp2 := norm_sub_sq_real a b
    rw [ha, hb] at hp1 hp2
    nlinarith [norm_nonneg (a + b), norm_nonneg (a - b)]
  · rintro (rfl | rfl)
    · exact estDistingue_bot (Metric.mem_closedBall_self zero_le_one)
    · exact estDistingue_top (Metric.mem_closedBall_self zero_le_one)

/-- In the closed unit ball, the only subspaces which fibre it are `0` and `E` (through
Prop. 3 1°: the ball contains no half-line). -/
theorem boule_fibre_iff (L : Submodule ℝ E) :
    Fibre (Metric.closedBall (0 : E) 1) L ↔ L = ⊥ ∨ L = ⊤ := by
  rw [← boule_estDistingue_iff]
  refine ⟨fun h => prop3_1 (convex_closedBall 0 1) (Metric.mem_closedBall_self zero_le_one)
    (not_contientDemiDroite_of_isBounded Metric.isBounded_closedBall) h,
    FibreCylindriquement.fibre⟩

end Boule

/-- The strip `ℝ × [0, 1]`. -/
def bande : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ Set.Icc 0 1

/-- The instance for Prop. 3 2°'s hypothesis: the strip `ℝ × [0, 1]` (convex, containing `0`,
spanning `ℝ²`, containing a line) has the horizontal axis distinguished with two different
conjugates, the vertical axis and the diagonal. -/
theorem bande_deux_conjugues :
    Convex ℝ bande ∧ ((0 : ℝ × ℝ) ∈ bande) ∧ Submodule.span ℝ bande = ⊤ ∧ ContientDroite bande ∧
    IsCompl (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)) (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) ∧
    SontConjugues bande (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) ∧
    IsCompl (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)) ∧
    SontConjugues bande (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)) ∧
    LinearMap.ker (LinearMap.fst ℝ ℝ ℝ) ≠
      LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) := by
  refine ⟨convex_univ.prod (convex_Icc 0 1), ⟨Set.mem_univ _, by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h10 : ((1 : ℝ), (0 : ℝ)) ∈ bande := ⟨Set.mem_univ _, by simp⟩
    have h01 : ((0 : ℝ), (1 : ℝ)) ∈ bande := ⟨Set.mem_univ _, by simp⟩
    have hx : x = x.1 • ((1 : ℝ), (0 : ℝ)) + x.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span h10))
      (Submodule.smul_mem _ _ (Submodule.subset_span h01))
  · exact ⟨0, (1, 0), by simp, fun t => ⟨Set.mem_univ _, by simp⟩⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      simp only [LinearMap.mem_ker, LinearMap.snd_apply, LinearMap.fst_apply] at hx hx'
      exact Prod.ext hx' hx
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
      rw [hx]
      exact Submodule.add_mem_sup (by simp) (by simp)
  · ext x
    simp only [bande, Set.mem_add, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.snd_apply, LinearMap.fst_apply, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨(x.1, 0), ⟨rfl, by norm_num⟩, (0, x.2), ⟨rfl, h0, h1⟩, by ext <;> simp⟩
    · rintro ⟨a, ⟨ha, -⟩, b, ⟨-, hb0, hb1⟩, rfl⟩
      simp only [Prod.snd_add, ha, zero_add]
      exact ⟨hb0, hb1⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      simp only [LinearMap.mem_ker, LinearMap.snd_apply, LinearMap.sub_apply,
        LinearMap.fst_apply] at hx hx'
      exact Prod.ext (by rw [Prod.fst_zero]; linarith) hx
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x = (x.1 - x.2, 0) + (x.2, x.2) := by ext <;> simp
      rw [hx]
      exact Submodule.add_mem_sup (by simp) (by simp)
  · ext x
    simp only [bande, Set.mem_add, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.sub_apply, Set.mem_prod,
      Set.mem_univ, true_and, Set.mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨(x.1 - x.2, 0), ⟨rfl, by norm_num⟩, (x.2, x.2), ⟨sub_self _, h0, h1⟩,
        by ext <;> simp⟩
    · rintro ⟨a, ⟨ha, -⟩, b, ⟨-, hb0, hb1⟩, rfl⟩
      simp only [Prod.snd_add, ha, zero_add]
      exact ⟨hb0, hb1⟩
  · intro h
    have h01 : ((0 : ℝ), (1 : ℝ)) ∈ LinearMap.ker (LinearMap.fst ℝ ℝ ℝ) := by simp
    rw [h] at h01
    simp at h01

/-- Déf. 4 as printed does not force supplementarity: `[0, ∞[ = [0, ∞[ + [0, ∞[`, so `ℝ` is
conjugate to itself relative to the half-line `[0, ∞[ ⊂ ℝ` (convex, containing `0`, spanning
`ℝ`, containing no line). -/
theorem demiDroite_conjugues_non_supplementaires :
    SontConjugues (Set.Ici (0 : ℝ)) ⊤ ⊤ ∧ ¬ IsCompl (⊤ : Submodule ℝ ℝ) ⊤ ∧
    ¬ ContientDroite (Set.Ici (0 : ℝ)) ∧ Submodule.span ℝ (Set.Ici (0 : ℝ)) = ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Submodule.top_coe, Set.univ_inter, Set.mem_add, Set.mem_Ici]
    constructor
    · intro hx; exact ⟨x, hx, 0, le_rfl, add_zero x⟩
    · rintro ⟨a, ha, b, hb, rfl⟩; exact add_nonneg ha hb
  · intro h
    have h1 : (1 : ℝ) ∈ (⊥ : Submodule ℝ ℝ) := disjoint_self.1 h.disjoint ▸ Submodule.mem_top
    simp at h1
  · rintro ⟨x, v, hv, h⟩
    have := h (-(|x| + 1) / v)
    rw [Set.mem_Ici, smul_eq_mul, div_mul_cancel₀ _ hv] at this
    linarith [le_abs_self x]
  · rw [eq_top_iff]
    intro x _
    have : x = x • (1 : ℝ) := by simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The cone `{|x| ≤ y}` of `ℝ²` (convex, containing `0`, spanning, containing no line but
half-lines) is fibred by the vertical axis, not cylindrically: Prop. 3 1°'s hypothesis is used. -/
theorem cone_fibre_non_cylindrique :
    Convex ℝ {p : ℝ × ℝ | |p.1| ≤ p.2} ∧ ¬ ContientDroite {p : ℝ × ℝ | |p.1| ≤ p.2} ∧
    Fibre {p : ℝ × ℝ | |p.1| ≤ p.2} (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) ∧
    ¬ FibreCylindriquement {p : ℝ × ℝ | |p.1| ≤ p.2} (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    calc |a * x.1 + b * y.1| ≤ |a * x.1| + |b * y.1| := abs_add_le _ _
      _ = a * |x.1| + b * |y.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * x.2 + b * y.2 := by nlinarith
  · rintro ⟨x, v, hv, h⟩
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at h
    have hv2 : v.2 = 0 := by
      by_contra h2
      have := h (-(|x.2| + 1) / v.2)
      rw [div_mul_cancel₀ _ h2] at this
      linarith [abs_nonneg (x.1 + -(|x.2| + 1) / v.2 * v.1), le_abs_self x.2]
    have hv1 : v.1 = 0 := by
      by_contra h1
      have := h ((|x.1| + |x.2| + 1) / v.1)
      rw [div_mul_cancel₀ _ h1, hv2, mul_zero, add_zero] at this
      have h3 : x.1 + (|x.1| + |x.2| + 1) ≤ |x.1 + (|x.1| + |x.2| + 1)| := le_abs_self _
      linarith [neg_abs_le x.1, le_abs_self x.2]
    exact hv (Prod.ext hv1 hv2)
  · intro a
    right
    refine ⟨(a.1, |a.1|), ?_⟩
    ext x
    simp only [Set.mem_inter_iff, mem_vadd_iff_sub_mem, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.fst_apply, Prod.fst_sub, Prod.snd_sub, Set.mem_setOf_eq, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1] at h2 ⊢
      simp only [sub_self, abs_zero, sub_nonneg, true_and]
      exact h2
    · rintro ⟨h1, h2⟩
      rw [h1, sub_self, abs_zero, sub_nonneg] at h2
      rw [h1]
      exact ⟨rfl, h2⟩
  · rintro ⟨L', h, hc⟩
    have hp : ((1 : ℝ), (1 : ℝ)) ∈ {p : ℝ × ℝ | |p.1| ≤ p.2} := by simp
    have hm : ((-1 : ℝ), (1 : ℝ)) ∈ {p : ℝ × ℝ | |p.1| ≤ p.2} := by simp
    rw [hc, Set.mem_add] at hp hm
    obtain ⟨p, ⟨hpL, -⟩, q, ⟨hqL, hqW⟩, hpq⟩ := hp
    obtain ⟨p', ⟨hpL', -⟩, q', ⟨hqL', hqW'⟩, hpq'⟩ := hm
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.fst_apply] at hpL hpL'
    have hq1 : q.1 = 1 := by
      have := congrArg Prod.fst hpq; simp only [Prod.fst_add] at this; linarith
    have hq1' : q'.1 = -1 := by
      have := congrArg Prod.fst hpq'; simp only [Prod.fst_add] at this; linarith
    have hs : q + q' ∈ LinearMap.ker (LinearMap.fst ℝ ℝ ℝ) := by
      simp only [LinearMap.mem_ker, LinearMap.fst_apply, Prod.fst_add, hq1, hq1']; norm_num
    have h0 := Submodule.disjoint_def.1 h.disjoint _ hs (L'.add_mem hqL hqL')
    have h2 : q.2 + q'.2 = 0 := by have := congrArg Prod.snd h0; simpa using this
    simp only [Set.mem_setOf_eq, hq1, hq1', abs_one, abs_neg] at hqW hqW'
    linarith

/-- Prop. 3 2° uses that `W` spans `E` (Déf. 3's standing hypothesis): the point `{0}` of `ℝ²`
(convex, containing no line, not spanning) has the horizontal axis distinguished with two
different conjugates. -/
theorem point_deux_conjugues :
    ¬ ContientDroite ({0} : Set (ℝ × ℝ)) ∧
    IsCompl (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)) (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) ∧
    SontConjugues {0} (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)) ∧
    IsCompl (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)) ∧
    SontConjugues {0} (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ))
      (LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)) ∧
    LinearMap.ker (LinearMap.fst ℝ ℝ ℝ) ≠
      LinearMap.ker (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) := by
  obtain ⟨-, -, -, -, h1, -, h2, -, hne⟩ := bande_deux_conjugues
  have hpt : ∀ L L' : Submodule ℝ (ℝ × ℝ), SontConjugues {0} L L' := by
    intro L L'
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_add, Set.mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro rfl; exact ⟨0, ⟨L.zero_mem, rfl⟩, 0, ⟨L'.zero_mem, rfl⟩, add_zero 0⟩
    · rintro ⟨a, ⟨-, rfl⟩, b, ⟨-, rfl⟩, rfl⟩; exact add_zero 0
  refine ⟨?_, h1, hpt _ _, h2, hpt _ _, hne⟩
  rintro ⟨x, v, hv, h⟩
  have e0 := h 0
  have e1 := h 1
  simp only [Set.mem_singleton_iff, zero_smul, add_zero, one_smul] at e0 e1
  rw [e0, zero_add] at e1
  exact hv e1

end Benzecri
