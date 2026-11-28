import Benzecri.Chapter3.Appui
import Benzecri.Chapter3.ProprieteI
import Benzecri.Chapter3.Fibres

/-!
# Chapter 3 § 5, Props. 2–4 — property I and variétés d'appui

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 5, journal p. 277; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex`. Target T-bz-c3-propriete-i-appui.
« variété linéaire » is `AffineSubspace ℝ E`, « la variété linéaire engendrée par $V$ » and « le
support $L$ de $V$ » are `affineSpan ℝ V`, Déf. 3 (variété d'appui) is `Benzecri.IsVarieteAppui`
(`Benzecri.Chapter3.Appui`), Déf. 1 (`I(V, W)`) is `Benzecri.ProprieteI`
(`Benzecri.Chapter3.ProprieteI`).

* **`bzprop:c3s5p2_support_appui`** — `benzecri1960_ch3.tex:1183` (Prop. 2, l.1183–1186, proof
  l.1188–1201) — `Benzecri.isVarieteAppui_affineSpan_of_proprieteI`; the proof's first step
  `Benzecri.exists_alphaW_of_mem_affineSpan`. Instance: `Benzecri.bordCarre_isVarieteAppui`.
* **`bzprop:c3s5p3_complementaire_appui`** — `benzecri1960_ch3.tex:1203` (Prop. 3, l.1203–1206,
  proof l.1208–1214) — `Benzecri.convex_inter_compl_of_isVarieteAppui`,
  `Benzecri.convex_inter_compl_union_of_isVarieteAppui`, both together
  `Benzecri.complementaire_appui`. Instance: `Benzecri.carre_moins_lineY0_union_origine`.
* **`bzprop:c3s5p4_propriete_I_appui`** — `benzecri1960_ch3.tex:1217` (Prop. 4, l.1217–1221,
  no proof printed) — `Benzecri.proprieteI_iff_isVarieteAppui`; its converse half needs no
  non-emptiness, `Benzecri.proprieteI_of_isVarieteAppui`. Instance:
  `Benzecri.bordCarre_appui_proprieteI`.

> **Proposition 2.** Soient $W$ un convexe dans un espace vectoriel, $V$ une partie convexe non
> vide de $W$ telle que $I(V, W)$; la variété linéaire $L$ engendrée par $V$ est une variété
> d'appui de $W$.
>
> **Proposition 3.** Soit $L$ une variété d'appui de $W$ : $\complement L\cap W$ est convexe.
> Soit $C$ une partie convexe de $L\cap W$ : $\bigl(W\cap\complement L\bigr)\cup C$ est convexe.
>
> **Proposition 4.** Soit $V$ une partie convexe non vide de $W$ convexe : il est équivalent de
> dire que $V$ possède la propriété $I$ relativement à $W$, ou de dire que le support $L$ de $V$
> est une variété d'appui de $W$ et que $V$ possède la propriété $I$ relativement à $L\cap W$.

## The proofs formalized

Prop. 2, first step (l.1188–1192): for `B ∈ L ∩ W` there is `A ∈ V` with `A α B`. The paper
takes `A` interior to the convex hull of finitely many points of `V` spanning `B`; here, with
`A₀ ∈ V`, `B − A₀ = r (x − y)` with `x, y ∈ V`, `r > 0` (the span of a convex set containing
`0`, `exists_smul_sub_of_mem_span`), and `A = (A₀ + x)/2` works with `ε = 1/(2r + 2)`:
`A + ε(A − B)` is a convex combination of `A₀, x, y`. No topology and no finite dimension are
needed. Second step (l.1194–1201), as printed: reduce to `A ∈ V` by transitivity of α; for
`B ∉ V` the point `A′ = A + δ(A − B)` lies in `V`, since otherwise `)A′, B( ⊆ W − V` would
contain `A`; so `B` is on the line `A A′` of `L`. Prop. 3 is the printed proof: an open segment
from a point of `(W − L) ∪ C` to a point of `W − L` misses `L` (Déf. 3 in Bourbaki's form,
`isVarieteAppui_iff_openSegment`). Prop. 4 (no proof printed): `⇒` is Prop. 2 and
`(L ∩ W) − V = L ∩ (W − V)`; `⇐` is Prop. 3 with `C = (L ∩ W) − V`, since
`W − V = (W − L) ∪ ((L ∩ W) − V)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Prop. 2: « $W$ un convexe dans un espace vectoriel » | ✓ carried: `Convex ℝ W`, `E` any real vector space |
| Prop. 2: « $V$ une partie convexe non vide de $W$ » | ✓ carried: `V.Nonempty`; `V ⊆ W` and `Convex ℝ V` are inside `ProprieteI V W` |
| Prop. 2: « $I(V, W)$ » | ✓ carried: `ProprieteI V W` |
| Prop. 3: « $L$ une variété d'appui de $W$ » | ✓ carried: `IsVarieteAppui W L`, with `Convex ℝ W` (the setting of Déf. 3 and of § 5) |
| Prop. 3: « $C$ une partie convexe de $L\cap W$ » | ✓ carried: `C ⊆ L ∩ W`, `Convex ℝ C` |
| Prop. 4: « $V$ une partie convexe non vide de $W$ convexe » | ✓ carried; ⚠ weakened for `⇐` (`proprieteI_of_isVarieteAppui`: no non-emptiness, no separate `V ⊆ W`) |

## SCOPE (disclosed)

* Prop. 3 is stated for convex `W`: Déf. 3 (§ 1) defines variétés d'appui of a convex, and § 5
  works with convex `W` throughout. Without convexity `W − L` need not be convex (`W = {−1, 0, 1}`,
  `L = {0}`, an
  observation not formalized here); this is the setting, not an added hypothesis.
* « $\complement L\cap W$ » and « $W\cap\complement L$ » are read as the same set
  `W ∩ (L : Set E)ᶜ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### Prop. 2 -/

/-- A point of the support of a convex `V` is reached from a point `A` of `V` along a direction
that extends beyond `A` inside `V`. -/
theorem exists_extend_mem_of_mem_affineSpan {V : Set E} (hV : Convex ℝ V) (hne : V.Nonempty)
    {B : E} (hB : B ∈ affineSpan ℝ V) :
    ∃ A ∈ V, ∃ ε : ℝ, 0 < ε ∧ A + ε • (A - B) ∈ V := by
  obtain ⟨A₀, hA₀⟩ := hne
  have hdir : B - A₀ ∈ (affineSpan ℝ V).direction :=
    AffineSubspace.vsub_mem_direction hB (subset_affineSpan ℝ V hA₀)
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hA₀] at hdir
  have hCconv : Convex ℝ ((· -ᵥ A₀) '' V) := by
    have : ((· -ᵥ A₀) '' V) = (fun x => -A₀ + x) '' V := by
      ext z; simp [vsub_eq_sub, sub_eq_neg_add]
    rw [this]; exact hV.translate _
  have h0 : (0 : E) ∈ ((· -ᵥ A₀) '' V) := ⟨A₀, hA₀, vsub_self _⟩
  obtain ⟨r, hr, _, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hBr⟩ :=
    exists_smul_sub_of_mem_span hCconv h0 hdir
  simp only [vsub_eq_sub, sub_sub_sub_cancel_right] at hBr
  have hB' : B = A₀ + r • (x - y) := by rw [← hBr]; abel
  set ε : ℝ := 1 / (2 * r + 2) with hε
  have hεpos : 0 < ε := by positivity
  have hεd : ε * (2 * r + 2) = 1 := by rw [hε]; field_simp
  refine ⟨(1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • x, hV hA₀ hx (by norm_num) (by norm_num) (by norm_num),
    ε, hεpos, ?_⟩
  have hmem := hV.sum_mem (t := Finset.univ) (w := ![(1 - ε) / 2, (1 + ε) / 2 - ε * r, ε * r])
    (z := ![A₀, x, y]) (by
      intro i _
      fin_cases i <;> simp <;> nlinarith)
    (by simp [Fin.sum_univ_three]; ring) (by
      intro i _
      fin_cases i <;> simpa)
  simp only [Fin.sum_univ_three] at hmem
  convert hmem using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [hB']
  module

/-- **Prop. 2, first step** (l.1188–1192): for `B ∈ L ∩ W`, `L` the support of `V ⊆ W`, some
`A ∈ V` has `A α(W) B`. -/
theorem exists_alphaW_of_mem_affineSpan {V W : Set E} (hW : Convex ℝ W) (hV : Convex ℝ V)
    (hVW : V ⊆ W) (hne : V.Nonempty) {B : E} (hB : B ∈ affineSpan ℝ V) (hBW : B ∈ W) :
    ∃ A ∈ V, AlphaW W A B := by
  obtain ⟨A, hA, ε, hε, hP⟩ := exists_extend_mem_of_mem_affineSpan hV hne hB
  exact ⟨A, hA, (alphaW_iff_extend hW).2 ⟨hVW hA, hBW, ε, hε, hVW hP⟩⟩

/-- **Prop. 2.** If `W` is convex, `V` non-empty and `I(V, W)`, the support of `V` is a
variété d'appui of `W`. -/
theorem isVarieteAppui_affineSpan_of_proprieteI {V W : Set E} (hW : Convex ℝ W)
    (hne : V.Nonempty) (hI : ProprieteI V W) : IsVarieteAppui W (affineSpan ℝ V) := by
  obtain ⟨hVW, hV, hWV⟩ := hI
  rw [isVarieteAppui_iff_alphaW hW]
  obtain ⟨A₀, hA₀⟩ := hne
  refine ⟨⟨A₀, subset_affineSpan ℝ V hA₀, hVW hA₀⟩, fun A B hA hAB => ?_⟩
  have hBW : B ∈ W := hAB.mem_right
  refine ⟨?_, hBW⟩
  obtain ⟨A₁, hA₁, h₁⟩ := exists_alphaW_of_mem_affineSpan hW hV hVW ⟨A₀, hA₀⟩ hA.1 hA.2
  have h₁B : AlphaW W A₁ B := alphaW_trans hW h₁ hAB
  by_cases hBV : B ∈ V
  · exact subset_affineSpan ℝ V hBV
  obtain ⟨-, -, δ, hδ, hP⟩ := (alphaW_iff_extend hW).1 h₁B
  set P : E := A₁ + δ • (A₁ - B) with hPdef
  have hPV : P ∈ V := by
    by_contra hPV
    have hseg : A₁ ∈ openSegment ℝ P B := by
      refine ⟨1 / (1 + δ), δ / (1 + δ), by positivity, by positivity, by field_simp, ?_⟩
      have h1 : P + δ • B = (1 + δ) • A₁ := by rw [hPdef]; module
      rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, one_smul, ← smul_add, h1,
        inv_smul_smul₀ (by positivity)]
    have := hWV.openSegment_subset ⟨hP, hPV⟩ ⟨hBW, hBV⟩ hseg
    exact this.2 hA₁
  have key : (-(1 / δ)) • (P -ᵥ A₁) +ᵥ A₁ = B := by
    rw [vsub_eq_sub, vadd_eq_add, hPdef, add_sub_cancel_left, smul_smul,
      show -(1 / δ) * δ = -1 by field_simp]
    module
  rw [← key]
  exact AffineSubspace.smul_vsub_vadd_mem _ _ (subset_affineSpan ℝ V hPV)
    (subset_affineSpan ℝ V hA₁) (subset_affineSpan ℝ V hA₁)

/-! ### Prop. 3 -/

/-- **Prop. 3**, second sentence: `(W ∩ ∁L) ∪ C` is convex for every convex `C ⊆ L ∩ W`. -/
theorem convex_inter_compl_union_of_isVarieteAppui {W : Set E} (hW : Convex ℝ W)
    {L : AffineSubspace ℝ E} (hL : IsVarieteAppui W L) {C : Set E}
    (hCsub : C ⊆ (L : Set E) ∩ W) (hC : Convex ℝ C) :
    Convex ℝ ((W ∩ (L : Set E)ᶜ) ∪ C) := by
  set S : Set E := (W ∩ (L : Set E)ᶜ) ∪ C with hS
  have hSW : S ⊆ W := union_subset inter_subset_left (fun x hx => (hCsub hx).2)
  -- the printed proof: `)A, B( ∩ L = ∅` for `A ∈ S`, `B ∈ W − L`
  have key : ∀ x ∈ S, ∀ y ∈ W ∩ (L : Set E)ᶜ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ S := by
    intro x hx y hy a b ha hb hab
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab
      rw [zero_smul, one_smul, zero_add]
      exact Or.inl hy
    rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab
      rw [zero_smul, one_smul, add_zero]
      exact hx
    have hzW : a • x + b • y ∈ W := hW (hSW hx) hy.1 ha hb hab
    refine Or.inl ⟨hzW, fun hzL => ?_⟩
    have := ((isVarieteAppui_iff_openSegment hW).1 hL).2 x (hSW hx) y hy.1
      ⟨a • x + b • y, ⟨a, b, ha', hb', hab, rfl⟩, hzL⟩
    exact hy.2 this.2
  intro x hx y hy a b ha hb hab
  rcases hy with hy | hyC
  · exact key x hx y hy a b ha hb hab
  rcases hx with hx | hxC
  · rw [add_comm]
    exact key y (Or.inr hyC) x hx b a hb ha (by rw [add_comm]; exact hab)
  · exact Or.inr (hC hxC hyC ha hb hab)

/-- **Prop. 3**, first sentence: `∁L ∩ W` is convex. -/
theorem convex_inter_compl_of_isVarieteAppui {W : Set E} (hW : Convex ℝ W)
    {L : AffineSubspace ℝ E} (hL : IsVarieteAppui W L) : Convex ℝ (W ∩ (L : Set E)ᶜ) := by
  have := convex_inter_compl_union_of_isVarieteAppui hW hL (empty_subset _) convex_empty
  rwa [union_empty] at this

/-- **Prop. 3**, both sentences. -/
theorem complementaire_appui {W : Set E} (hW : Convex ℝ W) {L : AffineSubspace ℝ E}
    (hL : IsVarieteAppui W L) :
    Convex ℝ (W ∩ (L : Set E)ᶜ) ∧
      ∀ C : Set E, C ⊆ (L : Set E) ∩ W → Convex ℝ C → Convex ℝ ((W ∩ (L : Set E)ᶜ) ∪ C) := by
  exact ⟨convex_inter_compl_of_isVarieteAppui hW hL,
    fun _ hCsub hC => convex_inter_compl_union_of_isVarieteAppui hW hL hCsub hC⟩

/-! ### Prop. 4 -/

/-- **Prop. 4, `⇐`**, with no non-emptiness: if the support `L` of `V` is a variété d'appui of
`W` and `I(V, L ∩ W)`, then `I(V, W)`. -/
theorem proprieteI_of_isVarieteAppui {V W : Set E} (hW : Convex ℝ W)
    (hL : IsVarieteAppui W (affineSpan ℝ V))
    (hI : ProprieteI V ((affineSpan ℝ V : Set E) ∩ W)) : ProprieteI V W := by
  obtain ⟨hVLW, hV, hD⟩ := hI
  refine ⟨fun x hx => (hVLW hx).2, hV, ?_⟩
  have heq : W \ V = (W ∩ (affineSpan ℝ V : Set E)ᶜ) ∪ (((affineSpan ℝ V : Set E) ∩ W) \ V) := by
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨hxW, hxV⟩
      by_cases hxL : x ∈ affineSpan ℝ V
      · exact Or.inr ⟨⟨hxL, hxW⟩, hxV⟩
      · exact Or.inl ⟨hxW, hxL⟩
    · rintro (⟨hxW, hxL⟩ | ⟨⟨-, hxW⟩, hxV⟩)
      · exact ⟨hxW, fun hxV => hxL (subset_affineSpan ℝ V hxV)⟩
      · exact ⟨hxW, hxV⟩
  rw [heq]
  exact convex_inter_compl_union_of_isVarieteAppui hW hL sdiff_subset hD

/-- **Prop. 4.** For `V` a non-empty convex part of a convex `W`: `I(V, W)` iff the support `L`
of `V` is a variété d'appui of `W` and `I(V, L ∩ W)`. -/
theorem proprieteI_iff_isVarieteAppui {V W : Set E} (hW : Convex ℝ W) (_hV : Convex ℝ V)
    (_hVW : V ⊆ W) (hne : V.Nonempty) :
    ProprieteI V W ↔
      IsVarieteAppui W (affineSpan ℝ V) ∧ ProprieteI V ((affineSpan ℝ V : Set E) ∩ W) := by
  refine ⟨fun hI => ⟨isVarieteAppui_affineSpan_of_proprieteI hW hne hI, ?_⟩,
    fun h => proprieteI_of_isVarieteAppui hW h.1 h.2⟩
  obtain ⟨hVW, hV, hD⟩ := hI
  refine ⟨fun x hx => ⟨subset_affineSpan ℝ V hx, hVW hx⟩, hV, ?_⟩
  have heq : ((affineSpan ℝ V : Set E) ∩ W) \ V = (affineSpan ℝ V : Set E) ∩ (W \ V) := by
    ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
  rw [heq]
  exact (affineSpan ℝ V).convex.inter hD

/-! ### Instances: an edge of the closed square -/

/-- **Prop. 2, instance.** The support of the edge `[0,1] × {0}` of the square `[0,1]²` is a
variété d'appui of the square. -/
theorem bordCarre_isVarieteAppui :
    IsVarieteAppui (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (affineSpan ℝ (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ))) := by
  exact isVarieteAppui_affineSpan_of_proprieteI ((convex_Icc 0 1).prod (convex_Icc 0 1))
    ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, rfl⟩ proprieteI_segment_carre

/-- **Prop. 4, instance.** For the edge `V = [0,1] × {0}` of the square `W`, the right-hand side
of Prop. 4. -/
theorem bordCarre_appui_proprieteI :
    IsVarieteAppui (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
        (affineSpan ℝ (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ))) ∧
      ProprieteI (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ))
        ((affineSpan ℝ (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) : Set (ℝ × ℝ)) ∩
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  exact (proprieteI_iff_isVarieteAppui ((convex_Icc 0 1).prod (convex_Icc 0 1))
    proprieteI_segment_carre.2.1 proprieteI_segment_carre.1
    ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, rfl⟩).1 proprieteI_segment_carre

/-- **Prop. 3, instance.** The square minus the line `y = 0`, with the corner `(0, 0)` added
back, is convex. -/
theorem carre_moins_lineY0_union_origine :
    Convex ℝ ((square ∩ (lineY0 : Set (ℝ × ℝ))ᶜ) ∪ {((0 : ℝ), (0 : ℝ))}) := by
  refine convex_inter_compl_union_of_isVarieteAppui convex_square lineY0_isVarieteAppui ?_
    (convex_singleton _)
  rw [singleton_subset_iff]
  exact ⟨mem_lineY0.2 rfl, mem_square.2 ⟨⟨le_rfl, zero_le_one⟩, le_rfl, zero_le_one⟩⟩

end Benzecri
