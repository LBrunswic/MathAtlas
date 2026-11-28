import Benzecri.Chapter3.Facettes
import Benzecri.Chapter3.Sommes

/-!
# Chapter 3 § 2, Prop. 2 — in a sum `W = ∑ V_i`, `x α(W) y` iff `x_i α(V_i) y_i` for every `i`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 264; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-alpha-somme.

* **`bzprop:c3s2p2_alpha_somme`** — `benzecri1960_ch3.tex:365` (Prop. 2, l.365–370, proof
  l.375–377) — `Benzecri.alphaW_somme_iff` (Déf. 1's finite sum `IsSommeConvexes`, any
  decompositions `x = ∑ x_i`, `y = ∑ y_i` with `x_i, y_i ∈ V_i`), its form through the
  components `Benzecri.alphaW_iff_composante`; also, for Remarque 2's infinite sums in the
  reading taken by T-bz-c3-sommes, `Benzecri.alphaW_sommeInfinie_iff` (not the anchor).
  Instance: `Benzecri.exemple_carre_alpha` — in `[0,1]² = [0,1]×{0} + {0}×[0,1]`
  (`exemple_carre_somme`) the centre α a vertex, componentwise, and not conversely.

> **Proposition 2.** Soit
> $$ W=\sum_{i\in I}V_i\qquad\Bigl(x, y\in W;\ x_i.\ y_i\in V_i;\ x=\sum x_i,\ y=\sum y_i\Bigr). $$
> on a $x\,\alpha(W)\,y$ (*cf.* déf. 1) si et seulement si l'on a pour tout $i$ :
> $x_i\,\alpha(V_i)\,y_i$.
>
> *Démonstration.* La démonstration est évidente à partir des définitions.

## The proof formalized

Through `alphaW_iff_extend` (`A α(W) B` iff `A, B ∈ W` and `A + ε(A − B) ∈ W`, `ε > 0`).
« Si »: with `ε_i` for each `i`, the single `δ = 1 / (1 + ∑ 1/ε_i)` is `≤ ε_i`, so by convexity of
`V_i` each `x_i + δ(x_i − y_i) ∈ V_i`, and their sum `x + δ(x − y)` is in `W`. « Seulement si »:
decompose `z = x + ε(x − y) = ∑ z_i`; then `x = (1/(1+ε)) z + (ε/(1+ε)) y` is also the sum of
`(1/(1+ε)) z_i + (ε/(1+ε)) y_i ∈ V_i`, so by uniqueness of the decomposition that is `x_i`, i.e.
`z_i = x_i + ε(x_i − y_i) ∈ V_i`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $W=\sum_{i\in I}V_i$ » (Déf. 1, $I$ finite) | ✓ carried: `IsSommeConvexes W V`, `[Fintype I]` (the `V_i` and `W` convex are part of Déf. 1) |
| « $x, y\in W$ » | ✓ carried: implied by `x = ∑ x_i`, `y = ∑ y_i` with `x_i, y_i ∈ V_i` (`alphaW_iff_composante` takes `x, y ∈ W`) |
| « $x_i, y_i\in V_i$; $x=\sum x_i$, $y=\sum y_i$ » ([sic] « x_i. y_i ») | ✓ carried: arbitrary families `x y : I → E` with `x i, y i ∈ V i`; the sums are `∑ i, x i`, `∑ i, y i` |
| « cf. déf. 1 » (the relation α) | ✓ read as § 1 Déf. 1, `Benzecri.AlphaW` (OQ-160 (b)) |
| $I$ infinite (Remarque 2) | optional form `alphaW_sommeInfinie_iff` under `IsSommeInfinie` (finitely supported families), in T-bz-c3-sommes's reading of Remarque 2 |

## SCOPE (disclosed)

* No hypothesis added; the statement of record is the finite one, `alphaW_somme_iff`.
* The infinite form rests on the reading of Remarque 2 taken by T-bz-c3-sommes
  (`IsSommeInfinie`: the sum is a bijection from the finitely supported families onto `W`); it
  is proved but is not the anchor.
* « cf. déf. 1 » printed in § 2, where Déf. 1 is the sum of convex sets, is read as § 1 Déf. 1
  (OQ-160 (b), OPEN); the only relation the statement can mean.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function

namespace Benzecri

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- In a convex `V`, if `a + ε(a − b) ∈ V` then `a + δ(a − b) ∈ V` for `0 ≤ δ ≤ ε`. -/
theorem add_smul_sub_mem_of_le {V : Set E} (hV : Convex ℝ V) {a b : E} {ε δ : ℝ} (hε : 0 < ε)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ε) (ha : a ∈ V) (hext : a + ε • (a - b) ∈ V) :
    a + δ • (a - b) ∈ V := by
  have := hV.add_smul_mem ha (y := ε • (a - b)) (by simpa using hext)
    (t := δ / ε) ⟨div_nonneg hδ0 hε.le, (div_le_one hε).2 hδ⟩
  rwa [smul_smul, div_mul_cancel₀ _ hε.ne'] at this

/-- `x = (1/(1+ε)) (x + ε(x − y)) + (ε/(1+ε)) y`. -/
theorem combi_extend_eq {X Y : E} {ε : ℝ} (hε : 0 < ε) :
    (1 / (1 + ε)) • (X + ε • (X - Y)) + (ε / (1 + ε)) • Y = X := by
  have hD : (1 + ε) ≠ 0 := by positivity
  have hab : 1 / (1 + ε) + 1 / (1 + ε) * ε = 1 := by field_simp
  have hb : 1 / (1 + ε) * ε = ε / (1 + ε) := by field_simp
  generalize 1 / (1 + ε) = a at hab hb ⊢
  rw [← hb]
  calc a • (X + ε • (X - Y)) + (a * ε) • Y = (a + a * ε) • X := by module
    _ = X := by rw [hab, one_smul]

/-- Conversely, `x = (1/(1+ε)) z + (ε/(1+ε)) y` forces `z = x + ε(x − y)`. -/
theorem eq_extend_of_combi {X Y Z : E} {ε : ℝ} (hε : 0 < ε)
    (h : (1 / (1 + ε)) • Z + (ε / (1 + ε)) • Y = X) : Z = X + ε • (X - Y) := by
  have hD : (1 + ε) ≠ 0 := by positivity
  have h2 := congrArg (fun v => (1 + ε) • v) h
  simp only [smul_add, smul_smul] at h2
  rw [mul_one_div_cancel hD, mul_div_cancel₀ _ hD, one_smul] at h2
  rw [eq_sub_of_add_eq h2]
  module

/-- **Ch. 3 § 2, Prop. 2** (`I` finite, Déf. 1): if `W = ∑ V_i`, `x_i, y_i ∈ V_i`, then
`(∑ x_i) α(W) (∑ y_i)` iff `x_i α(V_i) y_i` for every `i`. -/
theorem alphaW_somme_iff {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (h : IsSommeConvexes W V) {x y : I → E} (hx : ∀ i, x i ∈ V i) (hy : ∀ i, y i ∈ V i) :
    AlphaW W (∑ i, x i) (∑ i, y i) ↔ ∀ i, AlphaW (V i) (x i) (y i) := by
  obtain ⟨hW, hV, -⟩ := id h
  obtain ⟨-, hB⟩ := (isSommeConvexes_iff_bijOn W V).1 h
  have hxW : ∑ i, x i ∈ W := hB.mapsTo (fun i _ => hx i)
  have hyW : ∑ i, y i ∈ W := hB.mapsTo (fun i _ => hy i)
  constructor
  · intro hα
    obtain ⟨-, -, ε, hε, hz⟩ := (alphaW_iff_extend hW).1 hα
    obtain ⟨z, hzV, hzs⟩ := hB.surjOn hz
    simp only at hzs
    set w : I → E := fun i => (1 / (1 + ε)) • z i + (ε / (1 + ε)) • y i with hw
    have hwV : ∀ i, w i ∈ V i := fun i =>
      hV i (hzV i trivial) (hy i) (by positivity) (by positivity) (by field_simp)
    have hws : ∑ i, w i = ∑ i, x i := by
      simp only [hw, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [hzs]
      exact combi_extend_eq hε
    have hwx : w = x := hB.injOn (fun i _ => hwV i) (fun i _ => hx i) hws
    intro i
    refine (alphaW_iff_extend (hV i)).2 ⟨hx i, hy i, ε, hε, ?_⟩
    have := congrFun hwx i
    rw [← eq_extend_of_combi hε this]
    exact hzV i trivial
  · intro hα
    have hε : ∀ i, ∃ ε : ℝ, 0 < ε ∧ x i + ε • (x i - y i) ∈ V i := fun i =>
      ((alphaW_iff_extend (hV i)).1 (hα i)).2.2
    choose ε hεpos hεmem using hε
    set δ : ℝ := 1 / (1 + ∑ i, 1 / ε i) with hδ
    have hS : 0 ≤ ∑ i, 1 / ε i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hεpos i)).le
    have hδpos : 0 < δ := by positivity
    have hδle : ∀ i, δ ≤ ε i := by
      intro i
      have h1 : 1 / ε i ≤ ∑ j, 1 / ε j :=
        Finset.single_le_sum (f := fun j => 1 / ε j)
          (fun j _ => (one_div_pos.2 (hεpos j)).le) (Finset.mem_univ i)
      rw [hδ, div_le_iff₀ (by positivity)]
      have := hεpos i
      have h2 : ε i * (1 / ε i) = 1 := mul_one_div_cancel this.ne'
      nlinarith
    refine (alphaW_iff_extend hW).2 ⟨hxW, hyW, δ, hδpos, ?_⟩
    have hm := hB.mapsTo (x := fun i => x i + δ • (x i - y i)) (fun i _ =>
      add_smul_sub_mem_of_le (hV i) (hεpos i) hδpos.le (hδle i) (hx i) (hεmem i))
    convert hm using 1
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib]

/-- **Ch. 3 § 2, Prop. 2** through the components: for `x, y ∈ W = ∑ V_i`,
`x α(W) y` iff `x_i α(V_i) y_i` for every `i`, `x_i`, `y_i` the components of `x`, `y`. -/
theorem alphaW_iff_composante {I : Type*} [Fintype I] {W : Set E} {V : I → Set E}
    (h : IsSommeConvexes W V) {x y : E} (hx : x ∈ W) (hy : y ∈ W) :
    AlphaW W x y ↔ ∀ i, AlphaW (V i) (composante V x i) (composante V y i) := by
  have hx' := h.composante_spec hx
  have hy' := h.composante_spec hy
  rw [show AlphaW W x y ↔ AlphaW W (∑ i, composante V x i) (∑ i, composante V y i) by
    rw [hx'.2.1, hy'.2.1]]
  exact alphaW_somme_iff h hx'.1 hy'.1

/-- Prop. 2 for an infinite sum (Remarque 2, in the reading `IsSommeInfinie`): with finitely
supported families `f, g` of components, `(∑ f) α(W) (∑ g)` iff `f_i α(V_i) g_i` for every `i`.
Not the anchor. -/
theorem alphaW_sommeInfinie_iff {I : Type*} {W : Set E} {V : I → Set E}
    (h : IsSommeInfinie W V) {f g : I →₀ E} (hf : ∀ i, f i ∈ V i) (hg : ∀ i, g i ∈ V i) :
    AlphaW W (sommeF I E f) (sommeF I E g) ↔ ∀ i, AlphaW (V i) (f i) (g i) := by
  classical
  obtain ⟨hW, hV, -, -, hB⟩ := h
  have hfW : sommeF I E f ∈ W := hB.mapsTo (x := f) hf
  have hgW : sommeF I E g ∈ W := hB.mapsTo (x := g) hg
  constructor
  · intro hα
    obtain ⟨-, -, ε, hε, hz⟩ := (alphaW_iff_extend hW).1 hα
    obtain ⟨z, hzV, hzs⟩ := hB.surjOn hz
    have hzV' : ∀ i, z i ∈ V i := hzV
    set w : I →₀ E := (1 / (1 + ε)) • z + (ε / (1 + ε)) • g with hw
    have hwi : ∀ i, w i = (1 / (1 + ε)) • z i + (ε / (1 + ε)) • g i := fun i => by
      simp [hw]
    have hwV : ∀ i, w i ∈ V i := fun i => by
      rw [hwi]
      exact hV i (hzV' i) (hg i) (by positivity) (by positivity) (by field_simp)
    have hws : sommeF I E w = sommeF I E f := by
      rw [hw, map_add, map_smul, map_smul, hzs]
      exact combi_extend_eq hε
    have hwf : w = f := hB.injOn (x₁ := w) (x₂ := f) hwV hf hws
    intro i
    refine (alphaW_iff_extend (hV i)).2 ⟨hf i, hg i, ε, hε, ?_⟩
    have := (hwi i).symm.trans (DFunLike.congr_fun hwf i)
    rw [← eq_extend_of_combi hε this]
    exact hzV' i
  · intro hα
    have hε : ∀ i, ∃ ε : ℝ, 0 < ε ∧ f i + ε • (f i - g i) ∈ V i := fun i =>
      ((alphaW_iff_extend (hV i)).1 (hα i)).2.2
    choose ε hεpos hεmem using hε
    set S := (f - g).support
    set δ : ℝ := 1 / (1 + ∑ i ∈ S, 1 / ε i) with hδ
    have hS : 0 ≤ ∑ i ∈ S, 1 / ε i := Finset.sum_nonneg fun i _ => (one_div_pos.2 (hεpos i)).le
    have hδpos : 0 < δ := by positivity
    have hmem : ∀ i, f i + δ • (f i - g i) ∈ V i := by
      intro i
      by_cases hi : i ∈ S
      · have h1 : 1 / ε i ≤ ∑ j ∈ S, 1 / ε j :=
          Finset.single_le_sum (f := fun j => 1 / ε j)
            (fun j _ => (one_div_pos.2 (hεpos j)).le) hi
        have hle : δ ≤ ε i := by
          rw [hδ, div_le_iff₀ (by positivity)]
          have := hεpos i
          have h2 : ε i * (1 / ε i) = 1 := mul_one_div_cancel this.ne'
          nlinarith
        exact add_smul_sub_mem_of_le (hV i) (hεpos i) hδpos.le hle (hf i) (hεmem i)
      · have : f i - g i = 0 := by
          simpa [S, Finsupp.mem_support_iff] using hi
        rw [this, smul_zero, add_zero]
        exact hf i
    refine (alphaW_iff_extend hW).2 ⟨hfW, hgW, δ, hδpos, ?_⟩
    have hm := hB.mapsTo (x := f + δ • (f - g)) (fun i => by
      simpa using hmem i)
    convert hm using 1
    rw [map_add, map_smul, map_sub]

end Benzecri

/-- The instance: in `[0,1]² = [0,1]×{0} + {0}×[0,1]` (`exemple_carre_somme`), the centre
`(1/2, 1/2)` α the vertex `(0, 0)`, componentwise (`(1/2, 0) α (0, 0)` in the first side,
`(0, 1/2) α (0, 0)` in the second), and the vertex is not α the centre (already not in the first
side), both read off Prop. 2. -/
theorem Benzecri.exemple_carre_alpha :
    let V : Fin 2 → Set (ℝ × ℝ) := ![Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}, {(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1]
    let W : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
    (∀ i, Benzecri.AlphaW (V i) (![((1 : ℝ) / 2, 0), (0, (1 : ℝ) / 2)] i) (![(0, 0), (0, 0)] i)) ∧
      Benzecri.AlphaW W ((1 : ℝ) / 2, (1 : ℝ) / 2) (0, 0) ∧
      ¬ Benzecri.AlphaW (V 0) (0, 0) ((1 : ℝ) / 2, 0) ∧
      ¬ Benzecri.AlphaW W (0, 0) ((1 : ℝ) / 2, (1 : ℝ) / 2) := by
  intro V W
  have hS := Benzecri.exemple_carre_somme
  have hconv : ∀ i, Convex ℝ (V i) := hS.2.1
  set x : Fin 2 → ℝ × ℝ := ![((1 : ℝ) / 2, 0), (0, (1 : ℝ) / 2)] with hxdef
  set y : Fin 2 → ℝ × ℝ := ![(0, 0), (0, 0)] with hydef
  have hx : ∀ i, x i ∈ V i := by
    intro i; fin_cases i <;> norm_num [x, V]
  have hy : ∀ i, y i ∈ V i := by
    intro i; fin_cases i <;> norm_num [y, V]
  have hsx : ∑ i, x i = ((1 : ℝ) / 2, (1 : ℝ) / 2) := by simp [x, Fin.sum_univ_two]
  have hsy : ∑ i, y i = (0, 0) := by simp [y, Fin.sum_univ_two]
  have hcomp : ∀ i, Benzecri.AlphaW (V i) (x i) (y i) := by
    intro i
    refine (Benzecri.alphaW_iff_extend (hconv i)).2 ⟨hx i, hy i, 1, one_pos, ?_⟩
    fin_cases i <;> norm_num [x, y, V]
  have hneg0 : ¬ Benzecri.AlphaW (V 0) (y 0) (x 0) := by
    rw [Benzecri.alphaW_iff_extend (hconv 0)]
    rintro ⟨-, -, ε, hε, hm⟩
    simp [x, y, V] at hm
    linarith [hm.1]
  refine ⟨hcomp, ?_, hneg0, ?_⟩
  · rw [← hsx, ← hsy]
    exact (Benzecri.alphaW_somme_iff hS hx hy).2 hcomp
  · rw [← hsx, ← hsy, Benzecri.alphaW_somme_iff hS hy hx]
    exact fun h => hneg0 (h 0)
