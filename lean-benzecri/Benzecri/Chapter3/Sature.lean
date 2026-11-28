import Benzecri.Chapter3.FacettesSphere
import Benzecri.Chapter2.Hemisphere

/-!
# Chapter 3 § 6, Déf. 1, Prop. 1 and its Corollary — prolonging a convex beyond an open hemisphere, the saturated prolongation

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 6, journal pp. 281–282; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (to be checked by the author). Target
T-bz-c3-sature. Setting: `S(E)` for a real topological vector space `E`
(`[IsTopologicalAddGroup E] [ContinuousSMul ℝ E]`, plus `[T1Space E]` for the closedness of the
saturated convex), and `S(n)` (`Benzecri.S n`) for the Corollary; the closed hemisphere
`H = closedHemisphere l` of a linear form `l`, `H̊ = openHemisphere l`,
`h = linearSubvariety (ker l)`; « convexe » is `Sphere.IsConvexPart` (Ch. 1 Déf. 8), the noyau is
`Sphere.noyau` (§ 1 Déf. 5); « l'enveloppe convexe de `A` » is the least convex part containing
`A` (`IsLeast {k | IsConvexPart k ∧ A ⊆ k}`), which on `S(n)` is `Benzecri.enveloppeConvexe A`
(`isLeast_iff_eq_enveloppeConvexe`).

* **`bzdef:c3s6d1_prolonge`** — `benzecri1960_ch3.tex:1424` (l.1424–1430) —
  `Benzecri.Prolonge` (on any `S(E)`) and its claim
  `Benzecri.inter_closedHemisphere_eq_of_prolonge` (« $W\cap H=V\cap H$ », on any `S(E)`, for
  every linear form `l`, without `W ⊆ H`). Instance: `prolonge_self`.
* **`bzprop:c3s6p1_sature`** — `benzecri1960_ch3.tex:1432` (l.1432–1439, proof l.1444–1499) —
  `Benzecri.prop1_sature` (on any `S(E)`, `l` continuous) and `Benzecri.prop1_sature_Sn` (on
  `S(n)`, with `enveloppeConvexe`); parts: `Benzecri.sature` (the union of all prolongations),
  `Benzecri.isGreatest_sature` (convexity of `W` only), `Benzecri.isClosed_sature`,
  `Benzecri.noyau_sature_nonempty_iff_isLeast` / `Benzecri.noyau_sature_nonempty_iff` (an
  equivalence), `Benzecri.apex_unique` / `Benzecri.apex_unique_Sn`; 1° as printed:
  `Benzecri.prolonge_enveloppeConvexe_union`. Instances: `arcY_hypotheses`, `noyau_sature_arcY`
  (noyau of `V` empty), `ptY_hypotheses` (the exception: noyau of `V` nonempty).
* **`bzcor:c3s6p1c_sature_corps_convexe`** — `benzecri1960_ch3.tex:1502` (l.1502–1506, no proof
  printed) — `Benzecri.sature_corps_convexe` (as printed) and
  `Benzecri.sature_corps_convexe_of_ne_zero` (hypothesis weakened to apexes in `H̊`). Instance:
  `arcY_corps_convexe`.

> **Définition.** Soit $W$ un convexe contenu dans un hémisphère fermé $H$ de $S(E)$; on dit qu'un
> convexe $V$ *prolonge* $W$ au-delà de $\mathring{H}$ si si $V\cap\mathring{H}=W\cap\mathring{H}$.
> Si $\mathring{H}\cap W\neq\emptyset$ et si $V$ et $W$ sont fermés, on a de plus :
> $W\cap H=V\cap H$.
>
> **Proposition 1.** Soit $W$ un convexe fermé de noyau vide (*cf.* § 2, déf. 4), et soit $H$ un
> hémisphère fermé de frontière $h$, tel que $W\subset H$, $W\cap\mathring{H}\neq\emptyset$; alors
> il existe un plus grand convexe $V$ prolongeant $W$ au-delà de $\mathring{H}$; $V$ est appelé
> *saturé de $W$ au-delà* de $\mathring{H}$. Le noyau de $V$ est vide, sauf si $W$ est l'enveloppe
> convexe d'un point de $\mathring{H}$ et de $W\cap h$; ce point de $\mathring{H}$ est alors unique.
>
> **Corollaire.** Soit $W$ un corps convexe de $S(n)$, $H$ un hémisphère fermé de frontière $h$
> contenant $W$; si $W$ n'est pas l'enveloppe convexe d'un point et de $W\cap h$, le saturé de $W$
> au-delà de $\mathring{H}$ est un corps convexe.

## The proofs formalized

Everything is read on the cones `F(k) ∪ {O}` (`IsConvexPart.cone`). 1° (the family is directed):
the rays of `F(V′) ∪ {O} + F(V″) ∪ {O}` form a convex part containing `V′ ∪ V″`
(`prolonge_join`); a point `a + b` of it with `l(a + b) > 0` has `l a > 0` or `l b > 0`, say
`l a`, so `a ∈ W ⊆ V″` and `a + b ∈ F(V″)` (`add_mem_F_of_prolonge`): Benzécri's argument with
the segments `(v′, v″)` replaced by sums. On `S(n)` the hull `enveloppeConvexe (V′ ∪ V″)` lies
inside, which is 1° as printed. 3° is done without Zorn: the union of *all* prolongations is a
prolongation, because two of its points lie in one prolongation (the join of the two they come
from); it is then the greatest (`isGreatest_sature`). 2° and the closedness of `V`: `closure V`
prolongs `W` (`H̊` open since `l` is continuous, `W` closed). The Déf.'s claim: a point `x` of
`W ∩ h` is the limit of the points `x + t w` (`t → 0⁺`, `w` a representative of a point of
`W ∩ H̊`), which lie in `W ∩ H̊ ⊆ V`, and `V` is closed (`inter_closedHemisphere_subset`);
symmetrically for `V ∩ h`. 4°: a pair `±v` in `V` with `l v = 0` would lie in `W` (the trace
lemma), against `noyau W = ∅`; so one of them, `v`, is in `H̊`, and every `x ∈ F(W)` is
`(l x / l v) v + b` with `b = x − (l x / l v) v` in the cone of `V`, in `ker l`, hence in `W ∩ h`:
`W` is the hull of `v` and `W ∩ h`. The converse (not printed, proved so that « sauf si » holds in
both readings): if `W` is the hull of `p ∈ H̊` and `W ∩ h`, the rays of
`{s(−p) + w | s ≥ 0, w ∈ F(W) ∪ {O}}` prolong `W`, so `±p ∈ V`. Uniqueness of the apex is the
printed argument in cones: `q = s p + b`, `p = s′ q + b′`, `s s′ = 1`, `s′ b + b′ = 0` with both
in the salient cone of `W`. The Corollary: `W` meets `H̊` (an interior point `x` of `W` with
`l x = 0` is the limit of `x + t u`, `l u > 0`, `inter_openHemisphere_nonempty`); Prop. 1 then
gives a closed `V ⊇ W` of empty noyau, compact in the compact `S(n)`. When `l = 0` the printed
hypothesis fails (`W` is the hull of any of its points and `W ∩ h = W`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf.: « $W$ un convexe contenu dans un hémisphère fermé $H$ de $S(E)$ » | context only: `Prolonge l W V` is defined for every `W`, `l`, on any `S(E)` |
| Déf.: « un convexe $V$ » | ✓ carried: `Prolonge` contains `IsConvexPart V` |
| Déf. claim: « $W$ convexe », « $\mathring{H}\cap W\neq\emptyset$ », « $V$ et $W$ fermés » | ✓ carried; ⚠ weakened: `W ⊆ H` is not used, `l` is any linear form |
| Déf. claim: the topology of `S(E)` | the quotient topology of a topological vector space `E` (`IsTopologicalAddGroup`, `ContinuousSMul`); the paper's finest locally convex topology is one |
| Prop. 1: « $W$ un convexe fermé » | ✓ carried: `IsConvexPart W`, `IsClosed W`; the greatest `V` exists for any convex `W` (`isGreatest_sature`) |
| Prop. 1: « de noyau vide (cf. § 2, déf. 4) » | ✓ carried: `noyau W = ∅` (§ 1 Déf. 5, see SCOPE); used for the noyau of `V` and the apex only |
| Prop. 1: « $H$ un hémisphère fermé de frontière $h$ » | ✓ carried: `closedHemisphere l`, `h = linearSubvariety (ker l)`; `l ≠ 0` follows from `W ∩ H̊ ≠ ∅`; `l` continuous (the equation of every closed hemisphere is, `IsClosedHemisphere.exists_eq`), used only for « $V$ fermé » |
| Prop. 1: « $W\subset H$ », « $W\cap\mathring{H}\neq\emptyset$ » | ✓ carried |
| Prop. 1: `E` | `T₁` added for « $V$ fermé » (`isClosed_sature`, `prop1_sature`): the paper's `E` is Hausdorff |
| Cor.: « $W$ un corps convexe de $S(n)$ » | ✓ carried: `IsCorpsConvexeS n W` |
| Cor.: « $H$ … contenant $W$ » | ✓ carried: `W ⊆ closedHemisphere l`, any `l` |
| Cor.: « $W$ n'est pas l'enveloppe convexe d'un point et de $W\cap h$ » | ✓ carried, `∀ p`, in `sature_corps_convexe`; ⚠ weakened to `∀ p ∈ H̊` (with `l ≠ 0`) in `sature_corps_convexe_of_ne_zero` |

## SCOPE (disclosed)

* « cf. § 2, déf. 4 » is a misprinted reference (`% [sic]` in the transcription, OQ-160 (b)): the
  noyau is § 1 Déf. 5, `Sphere.noyau`; the statement does not depend on the ruling.
* « hémisphère fermé $H$ » is `closedHemisphere l`; every closed hemisphere of `S(E)` in the sense
  of Ch. 1 Déf. 5 (DEC-114) is one with `l` continuous and non-zero
  (`IsClosedHemisphere.exists_eq`); `H̊` is the open hemisphere `openHemisphere l` it is the
  closure of, and its frontier `h` is `linearSubvariety (ker l)` (`frontier_openHemisphere`).
* « $V$ est appelé saturé » is `sature l W`, defined as the union of all prolongations; under
  Prop. 1's hypotheses (convexity of `W` suffices) it is the greatest one, and it is closed.
* « Le noyau de $V$ est vide, sauf si $W$ est l'enveloppe convexe … » is proved as an
  equivalence, so it holds whether « sauf si » is read « only if » or « if and only if ».
* « l'enveloppe convexe d'un point de $\mathring{H}$ et de $W\cap h$ » is the least convex part
  containing `{p} ∪ (W ∩ h)`; on `S(n)`, `enveloppeConvexe ({p} ∪ (W ∩ h))`, not redefined.
* Instances: `arcY` is the closed arc `{y ≥ |x|}` of `S(1)` with `H = {y ≥ 0}` (the segment
  `[−1, 1]` of the chart `y = 1`, inside `H̊`, the generic case: it is a convex body, and the
  noyau of its saturated convex is empty); `ptY` is the point `(0, 1)` (the exception: the hull of
  itself and of `W ∩ h = ∅`; the noyau of its saturated convex is nonempty). The planner's
  half-disc of `S(2)` and cone over a segment of `h` are not formalized; these one-dimensional
  instances exercise the same alternatives.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

open Sphere

/-! ### The definition (Déf. 1) and the algebraic part of Prop. 1, on any `S(E)` -/

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Déf. 1** (`bzdef:c3s6d1_prolonge`): a convex part `V` of `S(E)` *prolongs* `W` beyond the
open hemisphere `H̊ = openHemisphere l` when `V ∩ H̊ = W ∩ H̊`. -/
def Prolonge (l : Module.Dual ℝ E) (W V : Set (Sphere E)) : Prop :=
  IsConvexPart V ∧ V ∩ openHemisphere l = W ∩ openHemisphere l

/-- A convex part prolongs itself. -/
theorem prolonge_self {l : Module.Dual ℝ E} {W : Set (Sphere E)} (hW : IsConvexPart W) :
    Prolonge l W W :=
  ⟨hW, rfl⟩

/-- The intersection of two convex parts is a convex part. -/
theorem isConvexPart_inter_sature {A B : Set (Sphere E)} (hA : IsConvexPart A)
    (hB : IsConvexPart B) : IsConvexPart (A ∩ B) := by
  rw [isConvexPart_iff_isSegConvex] at hA hB ⊢
  intro m hm m' hm' hne
  exact subset_inter (hA m hm.1 m' hm'.1 hne) (hB m hm.2 m' hm'.2 hne)

theorem openHemisphere_subset_closedHemisphere' (l : Module.Dual ℝ E) :
    openHemisphere l ⊆ closedHemisphere l := by
  intro x hx
  obtain ⟨X, hX, rfl⟩ := exists_isRep x
  exact (mk_mem_closedHemisphere hX).2 ((mk_mem_openHemisphere hX).1 hx).le

/-- The rays of a convex cone containing `O` form a convex part. -/
theorem isConvexPart_ofCone {C : Set E} (hC : IsPosCone C) (h0 : (0 : E) ∈ C)
    (hc : Convex ℝ C) : IsConvexPart (ofCone C) := by
  unfold IsConvexPart
  rw [F_ofCone hC, insert_sdiff_singleton, insert_eq_of_mem h0]
  exact hc

/-- The cone `{s P + b | s ≥ 0, b ∈ F(B) ∪ {O}}` spanned by `P` and a convex part `B`. -/
theorem smulAddCone_props (P : E) {B : Set (Sphere E)} (hB : IsConvexPart B) :
    IsPosCone {z : E | ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F B), z = s • P + b} ∧
      (0 : E) ∈ {z : E | ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F B), z = s • P + b} ∧
      Convex ℝ {z : E | ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F B), z = s • P + b} := by
  refine ⟨?_, ⟨0, le_rfl, 0, mem_insert _ _, by simp⟩, ?_⟩
  · rintro c hc _ ⟨s, hs, b, hb, rfl⟩
    exact ⟨c * s, by positivity, c • b, hB.cone.smul_mem hc hb, by rw [smul_add, smul_smul]⟩
  · rintro x ⟨s₁, hs₁, b₁, hb₁, rfl⟩ y ⟨s₂, hs₂, b₂, hb₂, rfl⟩ a b ha hb hab
    exact ⟨a * s₁ + b * s₂, by positivity, a • b₁ + b • b₂, hB hb₁ hb₂ ha hb hab, by module⟩

/-- If `W` is the convex hull of `mk P` and a convex part `B` (the least convex part containing
them), every point of the cone of `W` is `s P + b`, `s ≥ 0`, `b` in the cone of `B`. -/
theorem exists_smul_add_of_isLeast {W B : Set (Sphere E)} (hB : IsConvexPart B) {P : E}
    (hP : P ≠ 0) (hWp : IsLeast {k | IsConvexPart k ∧ {mk P hP} ∪ B ⊆ k} W) {w : E}
    (hw : w ∈ insert (0 : E) (F W)) :
    ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F B), w = s • P + b := by
  obtain ⟨hTpos, hT0, hTc⟩ := smulAddCone_props P hB
  rcases mem_insert_iff.1 hw with rfl | hw
  · exact ⟨0, le_rfl, 0, mem_insert _ _, by simp⟩
  have hsub : W ⊆ ofCone {z : E | ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F B), z = s • P + b} := by
    refine hWp.2 ⟨isConvexPart_ofCone hTpos hT0 hTc, union_subset ?_ ?_⟩
    · exact singleton_subset_iff.2 (mk_mem_ofCone hP ⟨1, zero_le_one, 0, mem_insert _ _, by simp⟩)
    · intro x hx
      obtain ⟨X, hX, rfl⟩ := exists_isRep x
      exact mk_mem_ofCone hX ⟨0, le_rfl, X, mem_insert_of_mem _ ⟨hX, hx⟩, by simp⟩
  have := F_mono hsub hw
  rw [F_ofCone hTpos] at this
  exact this.1

/-- Helper of 1°: if `a` (with `l a > 0`) and `b` lie in the cones of two prolongations, then
`a + b ∈ F(W)` as soon as `l (a + b) > 0`. -/
theorem add_mem_F_of_prolonge {l : Module.Dual ℝ E} {W V₁ V₂ : Set (Sphere E)}
    (h₁ : Prolonge l W V₁) (h₂ : Prolonge l W V₂) {a b : E} (ha : a ∈ insert (0 : E) (F V₁))
    (hb : b ∈ insert (0 : E) (F V₂)) (hla : 0 < l a) (hz : 0 < l (a + b)) : a + b ∈ F W := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero] at hla; exact lt_irrefl _ hla
  have hz0 : a + b ≠ 0 := fun h => by rw [h, map_zero] at hz; exact lt_irrefl _ hz
  obtain ⟨_, haV⟩ := (mem_insert_iff.1 ha).resolve_left ha0
  have haW : mk a ha0 ∈ V₂ ∩ openHemisphere l := by
    rw [h₂.2, ← h₁.2]; exact ⟨haV, (mk_mem_openHemisphere ha0).2 hla⟩
  have hsum : a + b ∈ h₂.1.cone := h₂.1.cone.add_mem (mem_insert_of_mem _ ⟨ha0, haW.1⟩) hb
  obtain ⟨_, hzV⟩ := (mem_insert_iff.1 hsum).resolve_left hz0
  have : mk (a + b) hz0 ∈ V₂ ∩ openHemisphere l := ⟨hzV, (mk_mem_openHemisphere hz0).2 hz⟩
  rw [h₂.2] at this
  exact ⟨hz0, this.1⟩

/-- **Prop. 1, 1°, on any `S(E)`**: the rays of `F(V′) ∪ {O} + F(V″) ∪ {O}` (the convex hull of
`V′ ∪ V″`) form a prolongation containing `V′` and `V″`. -/
theorem prolonge_join {l : Module.Dual ℝ E} {W V₁ V₂ : Set (Sphere E)}
    (h₁ : Prolonge l W V₁) (h₂ : Prolonge l W V₂) :
    Prolonge l W (ofCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂))) ∧
      V₁ ⊆ ofCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂)) ∧
      V₂ ⊆ ofCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂)) := by
  have hCpos : IsPosCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂)) := by
    intro c hc z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    exact Set.mem_add.2 ⟨c • a, h₁.1.cone.smul_mem hc ha, c • b, h₂.1.cone.smul_mem hc hb,
      (smul_add c a b).symm⟩
  have h0 : (0 : E) ∈ insert (0 : E) (F V₁) + insert (0 : E) (F V₂) :=
    Set.mem_add.2 ⟨0, mem_insert _ _, 0, mem_insert _ _, add_zero 0⟩
  have hsub1 : V₁ ⊆ ofCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂)) := by
    intro x hx
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    exact mk_mem_ofCone hX (Set.mem_add.2 ⟨X, mem_insert_of_mem _ ⟨hX, hx⟩, 0, mem_insert _ _,
      add_zero X⟩)
  have hsub2 : V₂ ⊆ ofCone (insert (0 : E) (F V₁) + insert (0 : E) (F V₂)) := by
    intro x hx
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    exact mk_mem_ofCone hX (Set.mem_add.2 ⟨0, mem_insert _ _, X, mem_insert_of_mem _ ⟨hX, hx⟩,
      zero_add X⟩)
  refine ⟨⟨isConvexPart_ofCone hCpos h0 (Convex.add h₁.1 h₂.1), Subset.antisymm ?_ ?_⟩,
    hsub1, hsub2⟩
  · rintro x ⟨hx, hxH⟩
    obtain ⟨z, hz0, hz, rfl⟩ := mem_ofCone.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hz
    have hpos := (mk_mem_openHemisphere hz0).1 hxH
    refine ⟨?_, hxH⟩
    rw [mk_mem_iff_mem_F]
    by_cases hla : 0 < l a
    · exact add_mem_F_of_prolonge h₁ h₂ ha hb hla hpos
    · have hlb : 0 < l b := by rw [map_add] at hpos; linarith [not_lt.1 hla]
      rw [add_comm a b] at hpos ⊢
      exact add_mem_F_of_prolonge h₂ h₁ hb ha hlb hpos
  · intro x hx
    rw [← h₁.2] at hx
    exact ⟨hsub1 hx.1, hx.2⟩

/-- **« le saturé de $W$ au-delà de $\mathring{H}$ »**: the union of all convex parts prolonging
`W` beyond `H̊`. -/
def sature (l : Module.Dual ℝ E) (W : Set (Sphere E)) : Set (Sphere E) :=
  ⋃₀ {V | Prolonge l W V}

/-- **Prop. 1, 1° and 3°, on any `S(E)`**: for a convex `W`, `sature l W` is the greatest convex
part prolonging `W` beyond `H̊`. -/
theorem isGreatest_sature {l : Module.Dual ℝ E} {W : Set (Sphere E)} (hW : IsConvexPart W) :
    IsGreatest {V | Prolonge l W V} (sature l W) := by
  refine ⟨⟨?_, ?_⟩, fun V hV => subset_sUnion_of_mem hV⟩
  · rw [isConvexPart_iff_isSegConvex]
    rintro m ⟨V₁, h₁, hm⟩ m' ⟨V₂, h₂, hm'⟩ hne
    obtain ⟨h3, hs1, hs2⟩ := prolonge_join h₁ h₂
    exact ((isConvexPart_iff_isSegConvex.1 h3.1) m (hs1 hm) m' (hs2 hm') hne).trans
      (subset_sUnion_of_mem h3)
  · ext x
    constructor
    · rintro ⟨⟨V, hV, hxV⟩, hxH⟩
      have : x ∈ V ∩ openHemisphere l := ⟨hxV, hxH⟩
      rwa [hV.2] at this
    · rintro ⟨hxW, hxH⟩
      exact ⟨⟨W, prolonge_self hW, hxW⟩, hxH⟩

/-- **Prop. 1, « ce point de $\mathring{H}$ est alors unique »**, on any `S(E)` (needs only
`noyau W = ∅`); « l'enveloppe convexe » is the least convex part containing the set. -/
theorem apex_unique {l : Module.Dual ℝ E} {W : Set (Sphere E)} (hnoy : noyau W = ∅)
    {p q : Sphere E} (hp : p ∈ openHemisphere l) (hq : q ∈ openHemisphere l)
    (hWp : IsLeast {k | IsConvexPart k ∧ {p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W)
    (hWq : IsLeast {k | IsConvexPart k ∧ {q} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W) :
    p = q := by
  have hW : IsConvexPart W := hWp.1.1
  have hB : IsConvexPart (W ∩ linearSubvariety (LinearMap.ker l)) :=
    isConvexPart_inter_sature hW (isConvexPart_linearSubvariety _)
  obtain ⟨P, hP, rfl⟩ := exists_isRep p
  obtain ⟨Q, hQ, rfl⟩ := exists_isRep q
  have hlP : 0 < l P := (mk_mem_openHemisphere hP).1 hp
  have hlQ : 0 < l Q := (mk_mem_openHemisphere hQ).1 hq
  have hpW : mk P hP ∈ W := hWp.1.2 (Or.inl rfl)
  have hqW : mk Q hQ ∈ W := hWq.1.2 (Or.inl rfl)
  have hker : ∀ b ∈ insert (0 : E) (F (W ∩ linearSubvariety (LinearMap.ker l))),
      l b = 0 ∧ b ∈ hW.cone := by
    intro b hb
    rcases mem_insert_iff.1 hb with rfl | ⟨hb0, hbB⟩
    · exact ⟨map_zero l, mem_insert _ _⟩
    · exact ⟨(mk_mem_linearSubvariety hb0).1 hbB.2, mem_insert_of_mem _ ⟨hb0, hbB.1⟩⟩
  obtain ⟨s, hs, b, hb, hQe⟩ :=
    exists_smul_add_of_isLeast hB hP hWp (mem_insert_of_mem _ ⟨hQ, hqW⟩)
  obtain ⟨s', hs', b', hb', hPe⟩ :=
    exists_smul_add_of_isLeast hB hQ hWq (mem_insert_of_mem _ ⟨hP, hpW⟩)
  obtain ⟨hlb, hbW⟩ := hker b hb
  obtain ⟨hlb', hb'W⟩ := hker b' hb'
  have e1 : l Q = s * l P := by rw [hQe, map_add, map_smul, hlb, smul_eq_mul, add_zero]
  have e2 : l P = s' * l Q := by rw [hPe, map_add, map_smul, hlb', smul_eq_mul, add_zero]
  have hss : s' * s = 1 := by
    have h : l P = (s' * s) * l P := by rw [mul_assoc, ← e1, ← e2]
    field_simp at h
    nlinarith [h]
  have hs'pos : 0 < s' := by
    rcases hs'.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hss; exact absurd hss zero_ne_one
  have key : s' • b + b' = 0 := by
    calc s' • b + b' = (s' • (s • P + b) + b') - (s' * s) • P := by module
      _ = 0 := by rw [← hQe, ← hPe, hss, one_smul, sub_self]
  have hb'0 : b' = 0 := by
    by_contra hb'0
    have hnb' : -b' ∈ hW.cone := by
      have : -b' = s' • b := (add_eq_zero_iff_eq_neg.1 key).symm
      rw [this]; exact hW.cone.smul_mem hs'pos hbW
    have h1 : mk b' hb'0 ∈ W := ((mem_insert_iff.1 hb'W).resolve_left hb'0).2
    have h2 : -mk b' hb'0 ∈ W := by
      rw [neg_mk]; exact ((mem_insert_iff.1 hnb').resolve_left (neg_ne_zero.2 hb'0)).2
    have : mk b' hb'0 ∈ noyau W := by rw [noyau_eq hW]; exact ⟨h1, h2⟩
    rw [hnoy] at this; exact this
  rw [hb'0, add_zero] at hPe
  exact ((mk_eq_mk_iff_exists_pos hQ hP).2 ⟨s', hs'pos, hPe.symm⟩).symm

/-! ### The topological part, on any `S(E)` -/

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A closed part contains the limit `X` of `X + t Y`, `t → 0⁺`. -/
theorem mem_F_of_forall_add_smul {B : Set (Sphere E)} (hB : IsClosed B) {X Y : E} (hX : X ≠ 0)
    (h : ∀ t : ℝ, 0 < t → X + t • Y ∈ F B) : X ∈ F B := by
  have ht : Tendsto (fun t : ℝ => X + t • Y) (𝓝[>] 0) (𝓝 X) := by
    have : Continuous fun t : ℝ => X + t • Y :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hcl : X ∈ closure (F B) :=
    mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun t ht => h t ht)
  have e := F_closure B
  rw [hB.closure_eq] at e
  rw [e]
  exact ⟨hcl, hX⟩

/-- The trace lemma: if `A` is convex and meets `H̊`, and `A ∩ H̊ ⊆ B` with `B` closed, then
`A ∩ H ⊆ B`. -/
theorem inter_closedHemisphere_subset {l : Module.Dual ℝ E} {A B : Set (Sphere E)}
    (hA : IsConvexPart A) (hB : IsClosed B) (hAB : A ∩ openHemisphere l ⊆ B)
    (hne : (A ∩ openHemisphere l).Nonempty) : A ∩ closedHemisphere l ⊆ B := by
  rintro x ⟨hxA, hxH⟩
  obtain ⟨w, hwA, hwH⟩ := hne
  obtain ⟨X, hX, rfl⟩ := exists_isRep x
  obtain ⟨Y, hY, rfl⟩ := exists_isRep w
  rw [mk_mem_closedHemisphere] at hxH
  rw [mk_mem_openHemisphere] at hwH
  rcases hxH.lt_or_eq with hpos | hzero
  · exact hAB ⟨hxA, (mk_mem_openHemisphere hX).2 hpos⟩
  rw [mk_mem_iff_mem_F]
  refine mem_F_of_forall_add_smul hB hX (Y := Y) fun t ht => ?_
  have hsum : X + t • Y ∈ hA.cone :=
    hA.cone.add_mem (mem_insert_of_mem _ ⟨hX, hxA⟩)
      (hA.cone.smul_mem ht (mem_insert_of_mem _ ⟨hY, hwA⟩))
  have hl : 0 < l (X + t • Y) := by
    rw [map_add, map_smul, ← hzero, zero_add, smul_eq_mul]; exact mul_pos ht hwH
  have hne0 : X + t • Y ≠ 0 := fun h => by rw [h, map_zero] at hl; exact lt_irrefl _ hl
  obtain ⟨_, hmk⟩ := (mem_insert_iff.1 hsum).resolve_left hne0
  exact ⟨hne0, hAB ⟨hmk, (mk_mem_openHemisphere _).2 hl⟩⟩

/-- **Déf. 1, « Si $\mathring{H}\cap W\neq\emptyset$ et si $V$ et $W$ sont fermés, on a de plus :
$W\cap H=V\cap H$ »**, on any `S(E)` (`E` a topological vector space), for every linear
form `l`. -/
theorem inter_closedHemisphere_eq_of_prolonge {l : Module.Dual ℝ E} {W V : Set (Sphere E)}
    (hW : IsConvexPart W) (hV : Prolonge l W V) (hne : (openHemisphere l ∩ W).Nonempty)
    (hWc : IsClosed W) (hVc : IsClosed V) :
    W ∩ closedHemisphere l = V ∩ closedHemisphere l := by
  have h1 : W ∩ openHemisphere l ⊆ V := by rw [← hV.2]; exact inter_subset_left
  have h2 : V ∩ openHemisphere l ⊆ W := by rw [hV.2]; exact inter_subset_left
  have hne' : (W ∩ openHemisphere l).Nonempty := by rwa [inter_comm]
  have hne'' : (V ∩ openHemisphere l).Nonempty := by rwa [hV.2]
  apply Subset.antisymm
  · exact fun x hx => ⟨inter_closedHemisphere_subset hW hVc h1 hne' hx, hx.2⟩
  · exact fun x hx => ⟨inter_closedHemisphere_subset hV.1 hWc h2 hne'' hx, hx.2⟩

/-- **Prop. 1, « Le noyau de $V$ est vide, sauf si $W$ est l'enveloppe convexe d'un point de
$\mathring{H}$ et de $W\cap h$ »**, on any `S(E)`, as an equivalence; « l'enveloppe convexe » is
the least convex part containing the set. -/
theorem noyau_sature_nonempty_iff_isLeast {l : Module.Dual ℝ E}
    {W : Set (Sphere E)} (hW : IsConvexPart W) (hWc : IsClosed W) (hnoy : noyau W = ∅)
    (hWH : W ⊆ closedHemisphere l) (hne : (W ∩ openHemisphere l).Nonempty) :
    (noyau (sature l W)).Nonempty ↔ ∃ p ∈ openHemisphere l,
      IsLeast {k | IsConvexPart k ∧ {p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W := by
  have hg := isGreatest_sature (l := l) hW
  have hV := hg.1.1
  have hWV : W ⊆ sature l W := hg.2 (prolonge_self hW)
  have hB : IsConvexPart (W ∩ linearSubvariety (LinearMap.ker l)) :=
    isConvexPart_inter_sature hW (isConvexPart_linearSubvariety _)
  constructor
  · -- 4°
    rintro ⟨m, hm⟩
    rw [noyau_eq hV] at hm
    obtain ⟨hmV, hm'V⟩ := hm
    have hVW : sature l W ∩ closedHemisphere l ⊆ W :=
      inter_closedHemisphere_subset hV hWc (by rw [hg.1.2]; exact inter_subset_left)
        (by rw [hg.1.2]; exact hne)
    obtain ⟨v, hvH, hvV, hv'V⟩ : ∃ v : Sphere E, v ∈ openHemisphere l ∧ v ∈ sature l W ∧
        -v ∈ sature l W := by
      obtain ⟨M, hM, rfl⟩ := exists_isRep m
      rcases lt_trichotomy (l M) 0 with hneg | hzero | hpos
      · refine ⟨-mk M hM, ?_, hm'V, by rwa [neg_neg]⟩
        rw [neg_mk, mk_mem_openHemisphere, map_neg]; linarith
      · exfalso
        have h1 : mk M hM ∈ W := hVW ⟨hmV, (mk_mem_closedHemisphere hM).2 hzero.ge⟩
        have h2 : -mk M hM ∈ W := hVW ⟨hm'V, by
          rw [neg_mk, mk_mem_closedHemisphere, map_neg, hzero, neg_zero]⟩
        have : mk M hM ∈ noyau W := by rw [noyau_eq hW]; exact ⟨h1, h2⟩
        rw [hnoy] at this; exact this
      · exact ⟨mk M hM, (mk_mem_openHemisphere hM).2 hpos, hmV, hm'V⟩
    obtain ⟨P, hP, rfl⟩ := exists_isRep v
    have hlP : 0 < l P := (mk_mem_openHemisphere hP).1 hvH
    have hvW : mk P hP ∈ W := hVW ⟨hvV, openHemisphere_subset_closedHemisphere' l hvH⟩
    refine ⟨mk P hP, hvH, ⟨hW, union_subset (singleton_subset_iff.2 hvW) inter_subset_left⟩, ?_⟩
    rintro k ⟨hk, hAk⟩ x hx
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    have hlX : 0 ≤ l X := (mk_mem_closedHemisphere hX).1 (hWH hx)
    rcases hlX.lt_or_eq with hXpos | hX0
    · set c := l X / l P with hc
      have hcpos : 0 < c := div_pos hXpos hlP
      have hnegP : -P ∈ hV.cone :=
        mem_insert_of_mem _ ⟨neg_ne_zero.2 hP, by rw [← neg_mk]; exact hv'V⟩
      have hb : X + c • -P ∈ hV.cone :=
        hV.cone.add_mem (mem_insert_of_mem _ ⟨hX, hWV hx⟩) (hV.cone.smul_mem hcpos hnegP)
      have hlb : l (X + c • -P) = 0 := by
        rw [map_add, map_smul, map_neg, smul_eq_mul, hc]; field_simp; ring
      have hPk : c • P ∈ hk.cone :=
        hk.cone.smul_mem hcpos (mem_insert_of_mem _ ⟨hP, hAk (Or.inl rfl)⟩)
      have hXeq : X = (X + c • -P) + c • P := by module
      have hbk : X + c • -P ∈ hk.cone := by
        by_cases hb0 : X + c • -P = 0
        · rw [hb0]; exact mem_insert _ _
        obtain ⟨_, hbV⟩ := (mem_insert_iff.1 hb).resolve_left hb0
        have hbW : mk _ hb0 ∈ W := hVW ⟨hbV, (mk_mem_closedHemisphere hb0).2 hlb.ge⟩
        exact mem_insert_of_mem _ ⟨hb0, hAk (Or.inr ⟨hbW, (mk_mem_linearSubvariety hb0).2 hlb⟩)⟩
      have hXk : X ∈ hk.cone := by rw [hXeq]; exact hk.cone.add_mem hbk hPk
      exact ((mem_insert_iff.1 hXk).resolve_left hX).2
    · exact hAk (Or.inr ⟨hx, (mk_mem_linearSubvariety hX).2 hX0.symm⟩)
  · -- the converse
    rintro ⟨p, hpH, hWp⟩
    obtain ⟨P, hP, rfl⟩ := exists_isRep p
    have hlP : 0 < l P := (mk_mem_openHemisphere hP).1 hpH
    have hpW : mk P hP ∈ W := hWp.1.2 (Or.inl rfl)
    have hP' : -P ≠ 0 := neg_ne_zero.2 hP
    obtain ⟨hTpos, hT0, hTc⟩ := smulAddCone_props (-P) hW
    have hpro : Prolonge l W
        (ofCone {z : E | ∃ s : ℝ, 0 ≤ s ∧ ∃ b ∈ insert (0 : E) (F W), z = s • -P + b}) := by
      refine ⟨isConvexPart_ofCone hTpos hT0 hTc, Subset.antisymm ?_ ?_⟩
      · rintro x ⟨hx, hxH⟩
        obtain ⟨z, hz0, ⟨c, hc, w, hw, rfl⟩, rfl⟩ := mem_ofCone.1 hx
        obtain ⟨s, hs, b, hb, rfl⟩ := exists_smul_add_of_isLeast hB hP hWp hw
        have hlb : l b = 0 := by
          rcases mem_insert_iff.1 hb with rfl | ⟨hb0, hbB⟩
          · exact map_zero l
          · exact (mk_mem_linearSubvariety hb0).1 hbB.2
        have hpos := (mk_mem_openHemisphere hz0).1 hxH
        rw [map_add, map_add, map_smul, map_smul, map_neg, hlb, smul_eq_mul, smul_eq_mul] at hpos
        have hsc : 0 < s - c := by nlinarith
        have hbW : b ∈ hW.cone := by
          rcases mem_insert_iff.1 hb with rfl | ⟨hb0, hbB⟩
          · exact mem_insert _ _
          · exact mem_insert_of_mem _ ⟨hb0, hbB.1⟩
        have hzW : c • -P + (s • P + b) ∈ hW.cone := by
          have e : c • -P + (s • P + b) = (s - c) • P + b := by module
          rw [e]
          exact hW.cone.add_mem (hW.cone.smul_mem hsc (mem_insert_of_mem _ ⟨hP, hpW⟩)) hbW
        exact ⟨((mem_insert_iff.1 hzW).resolve_left hz0).2, hxH⟩
      · rintro x ⟨hx, hxH⟩
        obtain ⟨X, hX, rfl⟩ := exists_isRep x
        exact ⟨mk_mem_ofCone hX ⟨0, le_rfl, X, mem_insert_of_mem _ ⟨hX, hx⟩, by simp⟩, hxH⟩
    have hnegV : mk (-P) hP' ∈ sature l W :=
      hg.2 hpro (mk_mem_ofCone hP' ⟨1, zero_le_one, 0, mem_insert _ _, by simp⟩)
    refine ⟨mk P hP, ?_⟩
    rw [noyau_eq hV]
    exact ⟨hWV hpW, by rw [neg_mk]; exact hnegV⟩

variable [T1Space E]

/-- **Prop. 1, 2° and 3°, « et $V$ est fermé »**, for a continuous `l` (the equation of a closed
hemisphere is continuous, `IsClosedHemisphere.exists_eq`). -/
theorem isClosed_sature {l : Module.Dual ℝ E} (hl : Continuous l) {W : Set (Sphere E)}
    (hW : IsConvexPart W) (hWc : IsClosed W) : IsClosed (sature l W) := by
  have hg := isGreatest_sature (l := l) hW
  have hO : IsOpen (openHemisphere l) :=
    isOpen_ofCone (isPosCone_pos l) (isOpen_lt continuous_const hl)
  have hcl : Prolonge l W (closure (sature l W)) := by
    refine ⟨hg.1.1.closure, Subset.antisymm ?_ ?_⟩
    · rintro x ⟨hx, hxH⟩
      have h1 : x ∈ closure (openHemisphere l ∩ sature l W) := hO.inter_closure ⟨hxH, hx⟩
      rw [inter_comm, hg.1.2, inter_comm] at h1
      exact ⟨hWc.closure_subset (closure_mono inter_subset_right h1), hxH⟩
    · rw [← hg.1.2]
      exact inter_subset_inter_left _ subset_closure
  exact closure_subset_iff_isClosed.1 (hg.2 hcl)

/-- **Prop. 1** (`bzprop:c3s6p1_sature`), on any `S(E)`, assembled: there is a greatest convex `V`
prolonging `W` beyond `H̊` (`sature l W`, closed); its noyau is empty unless (and only if) `W` is
the convex hull of a point of `H̊` and `W ∩ h`; that point is then unique. -/
theorem prop1_sature {l : Module.Dual ℝ E} (hl : Continuous l) {W : Set (Sphere E)}
    (hW : IsConvexPart W) (hWc : IsClosed W) (hnoy : noyau W = ∅)
    (hWH : W ⊆ closedHemisphere l) (hne : (W ∩ openHemisphere l).Nonempty) :
    (∃ V, IsGreatest {V | Prolonge l W V} V) ∧
      IsGreatest {V | Prolonge l W V} (sature l W) ∧ IsClosed (sature l W) ∧
      ((noyau (sature l W)).Nonempty ↔ ∃ p ∈ openHemisphere l,
        IsLeast {k | IsConvexPart k ∧ {p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W) ∧
      ∀ p ∈ openHemisphere l, ∀ q ∈ openHemisphere l,
        IsLeast {k | IsConvexPart k ∧ {p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W →
        IsLeast {k | IsConvexPart k ∧ {q} ∪ (W ∩ linearSubvariety (LinearMap.ker l)) ⊆ k} W →
        p = q :=
  ⟨⟨_, isGreatest_sature hW⟩, isGreatest_sature hW, isClosed_sature hl hW hWc,
    noyau_sature_nonempty_iff_isLeast hW hWc hnoy hWH hne,
    fun _ hp _ hq hWp hWq => apex_unique hnoy hp hq hWp hWq⟩

end General

/-! ### On `S(n)`, with `enveloppeConvexe` -/

variable {n : ℕ}

local notation "Eₙ" => (Fin (n + 1) → ℝ)

/-- On `S(n)`, « $W$ est l'enveloppe convexe de $A$ » in the least-convex-part sense is
`W = enveloppeConvexe A`. -/
theorem isLeast_iff_eq_enveloppeConvexe (A : Set (S n)) {W : Set (S n)} :
    IsLeast {k | IsConvexPart k ∧ A ⊆ k} W ↔ W = enveloppeConvexe A := by
  obtain ⟨h1, h2, h3⟩ := enveloppeConvexe_isLeast A
  have h : IsLeast {k | IsConvexPart k ∧ A ⊆ k} (enveloppeConvexe A) :=
    ⟨⟨h1, h2⟩, fun k hk => h3 k hk.1 hk.2⟩
  exact ⟨fun hW => hW.unique h, fun hW => hW ▸ h⟩

/-- **Prop. 1, 1° as printed** (« l'enveloppe convexe $V'''$ de $V'$ et $V''$ prolonge $W$ au-delà
de $\mathring{H}$ »), on `S(n)`. -/
theorem prolonge_enveloppeConvexe_union {l : Module.Dual ℝ Eₙ} {W V₁ V₂ : Set (S n)}
    (h₁ : Prolonge l W V₁) (h₂ : Prolonge l W V₂) :
    Prolonge l W (enveloppeConvexe (V₁ ∪ V₂)) := by
  obtain ⟨h3, hs1, hs2⟩ := prolonge_join h₁ h₂
  have hsub := (enveloppeConvexe_isLeast (V₁ ∪ V₂)).2.2 _ h3.1 (union_subset hs1 hs2)
  refine ⟨(enveloppeConvexe_isLeast _).1, Subset.antisymm ?_ ?_⟩
  · rw [← h3.2]; exact inter_subset_inter_left _ hsub
  · intro x hx
    rw [← h₁.2] at hx
    exact ⟨subset_enveloppeConvexe _ (Or.inl hx.1), hx.2⟩

/-- **Prop. 1, the noyau of `V`, on `S(n)`**, with `enveloppeConvexe`. -/
theorem noyau_sature_nonempty_iff {l : Module.Dual ℝ Eₙ} {W : Set (S n)} (hW : IsConvexPart W)
    (hWc : IsClosed W) (hnoy : noyau W = ∅) (hWH : W ⊆ closedHemisphere l)
    (hne : (W ∩ openHemisphere l).Nonempty) :
    (noyau (sature l W)).Nonempty ↔ ∃ p ∈ openHemisphere l,
      W = enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l))) := by
  rw [noyau_sature_nonempty_iff_isLeast hW hWc hnoy hWH hne]
  exact exists_congr fun p => and_congr_right fun _ => isLeast_iff_eq_enveloppeConvexe _

/-- **Prop. 1, uniqueness of the apex, on `S(n)`**, with `enveloppeConvexe`. -/
theorem apex_unique_Sn {l : Module.Dual ℝ Eₙ} {W : Set (S n)} (hnoy : noyau W = ∅)
    {p q : S n} (hp : p ∈ openHemisphere l) (hq : q ∈ openHemisphere l)
    (hWp : W = enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l))))
    (hWq : W = enveloppeConvexe ({q} ∪ (W ∩ linearSubvariety (LinearMap.ker l)))) : p = q :=
  apex_unique hnoy hp hq ((isLeast_iff_eq_enveloppeConvexe _).2 hWp)
    ((isLeast_iff_eq_enveloppeConvexe _).2 hWq)

/-- **Prop. 1 on `S(n)`**, with `enveloppeConvexe` (the Corollary's setting). -/
theorem prop1_sature_Sn {l : Module.Dual ℝ Eₙ} {W : Set (S n)} (hW : IsConvexPart W)
    (hWc : IsClosed W) (hnoy : noyau W = ∅) (hWH : W ⊆ closedHemisphere l)
    (hne : (W ∩ openHemisphere l).Nonempty) :
    (∃ V, IsGreatest {V | Prolonge l W V} V) ∧
      IsGreatest {V | Prolonge l W V} (sature l W) ∧ IsClosed (sature l W) ∧
      ((noyau (sature l W)).Nonempty ↔ ∃ p ∈ openHemisphere l,
        W = enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)))) ∧
      ∀ p ∈ openHemisphere l, ∀ q ∈ openHemisphere l,
        W = enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l))) →
        W = enveloppeConvexe ({q} ∪ (W ∩ linearSubvariety (LinearMap.ker l))) → p = q :=
  ⟨⟨_, isGreatest_sature hW⟩, isGreatest_sature hW,
    isClosed_sature l.continuous_of_finiteDimensional hW hWc,
    noyau_sature_nonempty_iff hW hWc hnoy hWH hne,
    fun _ hp _ hq hWp hWq => apex_unique_Sn hnoy hp hq hWp hWq⟩

/-! ### The Corollary -/

/-- A part of `H` with nonempty interior meets `H̊` (for `l ≠ 0`). -/
theorem inter_openHemisphere_nonempty {l : Module.Dual ℝ Eₙ} (hl : l ≠ 0) {W : Set (S n)}
    (hWH : W ⊆ closedHemisphere l) (hint : (interior W).Nonempty) :
    (W ∩ openHemisphere l).Nonempty := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨X, hX, rfl⟩ := exists_isRep x
  have hlX : 0 ≤ l X := (mk_mem_closedHemisphere hX).1 (hWH (interior_subset hx))
  rcases hlX.lt_or_eq with hpos | hzero
  · exact ⟨mk X hX, interior_subset hx, (mk_mem_openHemisphere hX).2 hpos⟩
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
  have hFo : IsOpen (F (interior W)) := isOpen_iff_F.1 isOpen_interior
  have hXF : X ∈ F (interior W) := ⟨hX, hx⟩
  have ht : Tendsto (fun t : ℝ => X + t • u) (𝓝[>] 0) (𝓝 X) := by
    have : Continuous fun t : ℝ => X + t • u := continuous_const.add (continuous_id.smul continuous_const)
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨t, htF, ht0⟩ := ((ht.eventually (hFo.mem_nhds hXF)).and self_mem_nhdsWithin).exists
  obtain ⟨hne0, hmk⟩ := htF
  refine ⟨mk _ hne0, interior_subset hmk, (mk_mem_openHemisphere hne0).2 ?_⟩
  rw [map_add, map_smul, ← hzero, zero_add, smul_eq_mul]
  exact mul_pos ht0 hu

/-- **Corollary, with the hypothesis weakened** to apexes in `H̊` (and `l ≠ 0`, which the printed
hypothesis implies): the saturated convex of a convex body is a convex body. -/
theorem sature_corps_convexe_of_ne_zero {l : Module.Dual ℝ Eₙ} (hl : l ≠ 0) {W : Set (S n)}
    (hW : IsCorpsConvexeS n W) (hWH : W ⊆ closedHemisphere l)
    (hap : ∀ p ∈ openHemisphere l,
      W ≠ enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)))) :
    IsCorpsConvexeS n (sature l W) := by
  obtain ⟨hstrict, hcomp, hint⟩ := hW
  obtain ⟨hWconv, hnoy⟩ := isStrictConvexPart_iff_noyau_eq_empty.1 hstrict
  have hWc : IsClosed W := hcomp.isClosed
  have hne := inter_openHemisphere_nonempty hl hWH hint
  have hg := isGreatest_sature (l := l) hWconv
  refine ⟨isStrictConvexPart_iff_noyau_eq_empty.2 ⟨hg.1.1, ?_⟩,
    (isClosed_sature l.continuous_of_finiteDimensional hWconv hWc).isCompact,
    hint.mono (interior_mono (hg.2 (prolonge_self hWconv)))⟩
  by_contra h
  obtain ⟨p, hp, hWp⟩ := (noyau_sature_nonempty_iff hWconv hWc hnoy hWH hne).1
    (nonempty_iff_ne_empty.2 h)
  exact hap p hp hWp

/-- **Corollary** (`bzcor:c3s6p1c_sature_corps_convexe`), as printed: if `W` is a convex body of
`S(n)` in the closed hemisphere `H` and is not the convex hull of a point and `W ∩ h`, its
saturated convex beyond `H̊` is a convex body. -/
theorem sature_corps_convexe {l : Module.Dual ℝ Eₙ} {W : Set (S n)}
    (hW : IsCorpsConvexeS n W) (hWH : W ⊆ closedHemisphere l)
    (hap : ∀ p : S n, W ≠ enveloppeConvexe ({p} ∪ (W ∩ linearSubvariety (LinearMap.ker l)))) :
    IsCorpsConvexeS n (sature l W) := by
  by_cases hl : l = 0
  · exfalso
    subst hl
    obtain ⟨p, hp⟩ := hW.2.2.mono interior_subset
    have hWconv := (isStrictConvexPart_iff_noyau_eq_empty.1 hW.1).1
    have hh : W ∩ linearSubvariety (LinearMap.ker (0 : Module.Dual ℝ Eₙ)) = W := by
      refine inter_eq_left.2 fun x _ => ?_
      obtain ⟨X, hX, rfl⟩ := exists_isRep x
      exact (mk_mem_linearSubvariety hX).2 (by simp)
    apply hap p
    rw [hh, union_eq_right.2 (singleton_subset_iff.2 hp)]
    exact Subset.antisymm (subset_enveloppeConvexe W)
      ((enveloppeConvexe_isLeast W).2.2 W hWconv subset_rfl)
  · exact sature_corps_convexe_of_ne_zero hl hW hWH fun p _ => hap p

/-! ### Instances -/

/-- The hull of a convex part is itself. -/
theorem enveloppeConvexe_eq_self {k : Set (S n)} (hk : IsConvexPart k) : enveloppeConvexe k = k :=
  Subset.antisymm ((enveloppeConvexe_isLeast k).2.2 k hk subset_rfl) (subset_enveloppeConvexe k)

/-- A closed hemisphere of `S(n)` is closed: its complement is the open hemisphere of `-l`. -/
theorem isClosed_closedHemisphere' (l : Module.Dual ℝ Eₙ) : IsClosed (closedHemisphere l) := by
  have e : (closedHemisphere l)ᶜ = openHemisphere (-l) := by
    ext x
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    rw [mem_compl_iff, mk_mem_closedHemisphere, mk_mem_openHemisphere, LinearMap.neg_apply,
      neg_pos, not_le]
  rw [← isOpen_compl_iff, e]
  exact isOpen_ofCone (isPosCone_pos _)
    (isOpen_lt continuous_const (-l).continuous_of_finiteDimensional)

section Instance

/-- The form `y` on `ℝ²` (`H = {y ≥ 0}`, `h` the pair `±(1, 0)`). -/
def formY : Module.Dual ℝ (Fin 2 → ℝ) := LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

/-- The form `y − x`. -/
def formYmX : Module.Dual ℝ (Fin 2 → ℝ) :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 - LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0

/-- The form `y + x`. -/
def formYpX : Module.Dual ℝ (Fin 2 → ℝ) :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 + LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0

/-- **The instance of Prop. 1 (generic case)**: the closed arc `{y ≥ |x|}` of `S(1)`, i.e. the
closed segment `[−1, 1]` of the affine chart `y = 1` (the 1-dimensional disc); it lies in
`H̊ = {y > 0}` and does not meet `h`. -/
def arcY : Set (S 1) := closedHemisphere formYmX ∩ closedHemisphere formYpX

theorem mem_arcY {X : Fin 2 → ℝ} (hX : X ≠ 0) : mk X hX ∈ arcY ↔ X 0 ≤ X 1 ∧ -X 0 ≤ X 1 := by
  simp only [arcY, mem_inter_iff, mk_mem_closedHemisphere, formYmX, formYpX,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem ne_zero_of_mem_arcY_ker {X : Fin 2 → ℝ} (h1 : X 0 ≤ X 1) (h2 : -X 0 ≤ X 1)
    (h3 : X 1 ≤ 0) : X = 0 := by
  have hy : X 1 = 0 := by linarith
  have hx : X 0 = 0 := by linarith
  ext i; fin_cases i <;> simp [hx, hy]

/-- Prop. 1's hypotheses hold for `arcY` and `H = {y ≥ 0}`. -/
theorem arcY_hypotheses :
    IsConvexPart arcY ∧ IsClosed arcY ∧ noyau arcY = ∅ ∧ arcY ⊆ closedHemisphere formY ∧
      (arcY ∩ openHemisphere formY).Nonempty := by
  have hconv : IsConvexPart arcY :=
    isConvexPart_inter_sature (isConvexPart_closedHemisphere _) (isConvexPart_closedHemisphere _)
  refine ⟨hconv, (isClosed_closedHemisphere' _).inter (isClosed_closedHemisphere' _), ?_, ?_, ?_⟩
  · rw [noyau_eq hconv, eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx'⟩
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    rw [neg_mk, mem_arcY] at hx'
    rw [mem_arcY] at hx
    simp only [Pi.neg_apply, neg_neg] at hx'
    exact hX (ne_zero_of_mem_arcY_ker hx.1 hx.2 (by linarith [hx'.1, hx'.2]))
  · intro x hx
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    rw [mem_arcY] at hx
    rw [mk_mem_closedHemisphere, formY, LinearMap.proj_apply]
    linarith [hx.1, hx.2]
  · have h0 : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
    refine ⟨mk _ h0, (mem_arcY h0).2 (by simp), ?_⟩
    rw [mk_mem_openHemisphere, formY, LinearMap.proj_apply]
    simp

/-- `arcY` is not the hull of a point and of `arcY ∩ h` (which is empty): it has two points. -/
theorem arcY_ne_enveloppeConvexe (p : S 1) :
    arcY ≠ enveloppeConvexe ({p} ∪ (arcY ∩ linearSubvariety (LinearMap.ker formY))) := by
  have hB : arcY ∩ linearSubvariety (LinearMap.ker formY) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxh⟩
    obtain ⟨X, hX, rfl⟩ := exists_isRep x
    rw [mem_arcY] at hx
    rw [mk_mem_linearSubvariety, LinearMap.mem_ker, formY, LinearMap.proj_apply] at hxh
    exact hX (ne_zero_of_mem_arcY_ker hx.1 hx.2 hxh.le)
  rw [hB, union_empty, enveloppeConvexe_eq_self (isConvexPart_singleton_pt p)]
  intro h
  have hP : (![1, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
  have hQ : (![-1, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
  have h1 : mk _ hP ∈ ({p} : Set (S 1)) := h ▸ (mem_arcY hP).2 (by simp)
  have h2 : mk _ hQ ∈ ({p} : Set (S 1)) := h ▸ (mem_arcY hQ).2 (by norm_num)
  rw [mem_singleton_iff] at h1 h2
  obtain ⟨c, hc, hcPQ⟩ := (mk_eq_mk_iff_exists_pos hP hQ).1 (h1.trans h2.symm)
  have e0 := congrFun hcPQ 0
  simp at e0
  linarith

/-- **Instance of Prop. 1 (generic case)**: the saturated convex of `arcY` beyond `{y > 0}` has
empty noyau. -/
theorem noyau_sature_arcY : noyau (sature formY arcY) = ∅ := by
  obtain ⟨hW, hWc, hnoy, hWH, hne⟩ := arcY_hypotheses
  by_contra h
  obtain ⟨p, -, hp⟩ := (noyau_sature_nonempty_iff hW hWc hnoy hWH hne).1
    (nonempty_iff_ne_empty.2 h)
  exact arcY_ne_enveloppeConvexe p hp

/-- **Instance of the Corollary**: `arcY` is a convex body of `S(1)`, and so is its saturated
convex beyond `{y > 0}`. -/
theorem arcY_corps_convexe :
    IsCorpsConvexeS 1 arcY ∧ IsCorpsConvexeS 1 (sature formY arcY) := by
  obtain ⟨hW, hWc, hnoy, hWH, hne⟩ := arcY_hypotheses
  have hbody : IsCorpsConvexeS 1 arcY := by
    refine ⟨isStrictConvexPart_iff_noyau_eq_empty.2 ⟨hW, hnoy⟩, hWc.isCompact, ?_⟩
    have hO : IsOpen (openHemisphere formYmX ∩ openHemisphere formYpX) :=
      (isOpen_ofCone (isPosCone_pos _)
        (isOpen_lt continuous_const formYmX.continuous_of_finiteDimensional)).inter
      (isOpen_ofCone (isPosCone_pos _)
        (isOpen_lt continuous_const formYpX.continuous_of_finiteDimensional))
    have hsub : openHemisphere formYmX ∩ openHemisphere formYpX ⊆ arcY :=
      inter_subset_inter (openHemisphere_subset_closedHemisphere' _)
        (openHemisphere_subset_closedHemisphere' _)
    have h0 : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
    refine ⟨mk _ h0, interior_maximal hsub hO ⟨?_, ?_⟩⟩ <;>
      simp [mk_mem_openHemisphere, formYmX, formYpX]
  exact ⟨hbody, sature_corps_convexe hbody hWH arcY_ne_enveloppeConvexe⟩

/-- **The instance of Prop. 1 (exceptional case)**: the point `(0, 1)` of `H̊ = {y > 0}`, the
convex hull of itself and of `W ∩ h = ∅`. -/
def ptY : Set (S 1) := {Sphere.mk (![0, 1] : Fin 2 → ℝ) (fun h => by simpa using congrFun h 1)}

/-- Prop. 1's hypotheses hold for `ptY`, and the noyau of its saturated convex is nonempty. -/
theorem ptY_hypotheses :
    IsConvexPart ptY ∧ IsClosed ptY ∧ noyau ptY = ∅ ∧ ptY ⊆ closedHemisphere formY ∧
      (ptY ∩ openHemisphere formY).Nonempty ∧ (noyau (sature formY ptY)).Nonempty := by
  have hconv : IsConvexPart ptY := isConvexPart_singleton_pt _
  have hH : ptY ⊆ openHemisphere formY := by
    intro x hx
    rw [ptY, mem_singleton_iff] at hx
    rw [hx, mk_mem_openHemisphere, formY, LinearMap.proj_apply]; simp
  have hnoy : noyau ptY = ∅ := by
    rw [noyau_eq hconv, eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hx'⟩
    rw [ptY, mem_singleton_iff] at hx hx'
    rw [hx] at hx'
    exact Sphere.neg_ne_self _ hx'
  have hp : _ ∈ ptY := mem_singleton _
  have hne : (ptY ∩ openHemisphere formY).Nonempty := ⟨_, hp, hH hp⟩
  refine ⟨hconv, isClosed_singleton, hnoy, hH.trans (openHemisphere_subset_closedHemisphere' _),
    hne, ?_⟩
  refine (noyau_sature_nonempty_iff hconv isClosed_singleton hnoy
    (hH.trans (openHemisphere_subset_closedHemisphere' _)) hne).2 ⟨_, hH hp, ?_⟩
  have e : ({Sphere.mk (![0, 1] : Fin 2 → ℝ) (fun h => by simpa using congrFun h 1)} : Set (S 1)) ∪
      (ptY ∩ linearSubvariety (LinearMap.ker formY)) = ptY :=
    union_eq_left.2 inter_subset_left
  rw [e, enveloppeConvexe_eq_self hconv]

end Instance

end Benzecri
