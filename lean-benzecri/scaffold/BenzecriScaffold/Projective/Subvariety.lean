import BenzecriScaffold.Projective.Sphere
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# `BenzecriScaffold.Projective.Subvariety` — linear subvarieties, hemispheres, `S(E)/l` (Déf. 4, 5, 10)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 234–235; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45e (wave 1, layer L1).

* **`bzdef:c1s1d4_sous_variete_lineaire`** — `benzecri1960_ch1.tex:186` (Déf. 4, l.186–200: the
  definition l.186–189 and its Exemples l.191–200, which DEC-114 rules part of the row, p. 234):
  `Benzecri.Sphere.linearSubvariety L = s(L - {O})`, with `F(s(L - {O})) = L - {O}`. The Exemples: a
  line `ℝv` gives two diametrically opposite points (`linearSubvariety_span_singleton`,
  `mk_ne_neg_mk`); `IsLine`, `IsHyperplane` (printed « S(T) », read `S(E)` per the `[sic]`); the
  half-lines (« demi-droites », `Benzecri.Sphere.halfLine`): two opposite points `m, -m` of a line `D`
  divide it into two half-lines — `D - {m, -m}` is the disjoint union of two nonempty connected
  half-lines and is not connected (`Benzecri.Sphere.IsLine.diff_eq_halfLines`, finite dimension;
  `linearSubvariety_pair_diff`, `disjoint_halfLine_neg`, `isConnected_halfLine`,
  `not_isPreconnected_linearSubvariety_pair_diff` in any real topological vector space).
* **`bzdef:c1s1d5_hemisphere`** — `benzecri1960_ch1.tex:202` (Déf. 5, l.202–212, p. 234), and the
  converse paragraph after it (l.215–220, p. 235). **Marked under DEC-120** (marks resting on ruled
  readings are accepted): every printed assertion is proved, under the reading of DEC-114 that the
  equation is nonzero (`l ≠ 0`, forced by « l'hyperplan fermé $h$ »; equivalently `H ≠ ∅`) — a
  reading, not a finding; see SCOPE. `Benzecri.Sphere.IsOpenHemisphere`
  (as printed), `Benzecri.Sphere.openHemisphere l`; the equation is unique up to `ℝ⁺`
  (`openHemisphere_eq_iff`, every `l`, `l'`); **for `H` itself**, open with `F(H) = l⁻¹(ℝ⁺)` and
  `l ≠ 0`: `l` is continuous (`continuous_of_isOpen_of_F_eq`), the frontier of `H` is the closed
  hyperplane `h` with `F(h) ∪ {O} = l⁻¹(O)` and its closure is `H ∪ h`
  (`isOpenHemisphere_frontier_closure`); the converse paragraph: a closed hyperplane has a
  continuous equation and its complement is the union of the two disjoint open hemispheres of
  equations `l`, `-l`, of frontier `h` (`closedHyperplane_converse`, `continuous_of_F_union_eq`), the
  equation being defined up to a nonzero factor (`hyperplane_eq_iff`).
* **`bzdef:c1s1d10_quotient`** — `benzecri1960_ch1.tex:260` (Déf. 10, l.260–266, p. 235).
  **Marked under DEC-114 and DEC-120**: it rests on Déf. 8's convex parts, whose « F(k) + {O} » is
  ruled `F(k) ∪ {O}` (OQ-24, DEC-120), and on DEC-114's saturated reading of the analogy.
  `Benzecri.Sphere.quotient L := Sphere (E ⧸ L)`; **the convex parts of `S(E)` containing `l`
  correspond bijectively to the convex parts of `S(E)/l`** (`Benzecri.Sphere.convexQuotientEquiv`, an
  order isomorphism, no hypothesis on `E` or `L`), in the `∪` reading of Déf. 8
  (`Sphere.IsConvexPart`); the « De même que » analogy is read for `L`-saturated convex sets of `E`
  (`convexSaturatedEquiv`), the reading of DEC-114.

> **Déf. 4.** Soit $L$ un sous-espace vectoriel de $E$; $s(L-\{O\})$ sera appelé *sous-variété
> linéaire* de $S(E)$.
>
> **Déf. 5.** On dit qu'une partie ouverte $H$ de $S(E)$ est un *hémisphère ouvert* de $S(E)$ s'il
> existe une forme linéaire $l\in E^*$ telle que $F(H)=l^{-1}(\R^+)$. La forme linéaire $l$ est
> définie à un multiplicateur positif près. On l'appelle *équation* de l'hémisphère $H$.
> La frontière de $H$ est l'hyperplan fermé $h$ défini par $F(h)\cup\{O\}=l^{-1}(O)$.
> La fermeture $H\cup h$ de $H$ est appelée *hémisphère fermé*.
>
> Réciproquement, soit $h$ un hyperplan fermé de $S(E)$; $\complement h$ est réunion de deux
> hémisphères ouverts disjoints de frontière $h$ […] $l$ est défini à un multiplicateur non nul
> près. $\complement h$ est réunion de deux hémisphères ouverts d'équations $l$ et $-l$.
>
> **Déf. 10.** Soient $L$ un sous-espace vectoriel d'un espace vectoriel $E$ et $l$ l'image de
> $L-\{O\}$ dans $S(E)$ par $s$; la sphère $S(E/L)$ sera aussi notée $S(E)/l$ et appelée quotient
> de $S(E)$ par $l$. De même que les convexes de $E$ contenant $L$ s'identifient aux convexes de
> $E/L$, les convexes de $S(E)$ contenant $l$ s'identifient aux convexes de $S(E)/l$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| Déf. 4: `L` a subspace of `E` | ✓ carried (`Submodule ℝ E`, any `E`) |
| Déf. 4, Exemples: half-lines of a line | ✓ carried; the division into two connected half-lines needs a continuous form vanishing at `m` and not on the line, automatic in finite dimension (`IsLine.diff_eq_halfLines`; in general `not_isPreconnected_linearSubvariety_pair_diff` takes the form) |
| Déf. 5: `H` open, `l ∈ E^*` | ✓ carried as printed in `IsOpenHemisphere` (`l : Module.Dual ℝ E`) |
| Déf. 5: `l ≠ 0` (reading, DEC-114, forced by « l'hyperplan fermé $h$ ») | ⚠ reading: carried as `l ≠ 0` (⟺ `H ≠ ∅`, `openHemisphere_nonempty_iff`) in the frontier and closure statements |
| Déf. 5, frontier and closure | ✓ carried for `H` itself: `l` continuous is DERIVED from `H` open and `l ≠ 0` (`continuous_of_isOpen_of_F_eq`), for `E` a real topological vector space with `{O}` closed |
| Déf. 5, uniqueness of the equation | ✓ carried, no hypothesis (`l = 0` included) |
| converse: `h` a closed hyperplane, `l` continuous with `F(h) ∪ {O} = l⁻¹(O)` | ✓ carried: a continuous `l ≠ 0` is derived from `h` closed (`closedHyperplane_converse`), and every such `l` is continuous (`continuous_of_F_union_eq`) |
| Déf. 10: `L` any subspace, `E` any vector space | ✓ carried |
| Déf. 10: « convexes » of `S(E)` | reading (OQ-24 RULED, DEC-120): Déf. 8's first form `Convex ℝ (F(k) ∪ {O})` (printed « F(k) + {O} »), `Sphere.IsConvexPart` |

## SCOPE (disclosed)

* **Reading (Déf. 5, DEC-114), not a finding.** The equation is nonzero: « La frontière de $H$ est
  l'hyperplan fermé $h$ » presupposes `l ≠ 0` (a hyperplane is `s(L - {O})` with `L` of codimension
  1, which `l⁻¹(O)` is iff `l ≠ 0`). The literal first sentence admits `l = 0` and `H = ∅`
  (`isOpenHemisphere_empty`, `frontier_openHemisphere_zero` record it). With the reading, every
  printed assertion of Déf. 5 and of the converse paragraph is proved; the row is marked because
  DEC-120 accepts marks resting on ruled readings (Déf. 5 under `l ≠ 0`).
* **Reading (Déf. 10, DEC-114), not a finding.** The « De même que » analogy « les convexes de $E$
  contenant $L$ s'identifient aux convexes de $E/L$ » is read for the `L`-saturated convex sets of `E`
  (`C + L ⊆ C`: the open, the closed and the conical ones), for which it holds
  (`convexSaturatedEquiv`); literally, for arbitrary convex sets, it fails
  (`not_injective_convex_image_quotient`, a remark). The statement about `S(E)` holds as printed for
  every convex part (`convexQuotientEquiv`), because `F(k) ∪ {O}` is a convex cone and a convex cone
  containing `L` is `L`-saturated.
* **Déf. 8: OQ-24 is RULED (DEC-120).** « $F(k)+\{O\}$ » is `F(k) ∪ {O}`; under the Minkowski
  reading `F(k) + {O} = F(k)` no convex part could contain an antipodal pair, so Déf. 9 would be
  vacuous and no convex part would contain `l` for `L ≠ 0`. `Sphere.IsConvexPart` is that first
  form only; the segment form of Déf. 8, and Déf. 8's mark, are the `Projective/Convex` module's
  (wave 2). Déf. 10 is marked, resting on DEC-114 (saturated reading of the analogy) and DEC-120
  (OQ-24).
* The topology of `S(E)/l` and the partial map `S(E) - l → S(E)/l` are not built.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Stability under the positive homotheties. -/
def IsPosCone (C : Set E) : Prop := ∀ c : ℝ, 0 < c → ∀ v ∈ C, c • v ∈ C

theorem isPosCone_F (A : Set (Sphere E)) : IsPosCone (F A) := fun _ hc _ hv => smul_mem_F hv hc

theorem isPosCone_submodule (L : Submodule ℝ E) : IsPosCone (L : Set E) :=
  fun c _ _ hv => L.smul_mem c hv

theorem ofCone_subset_ofCone {C D : Set E} (h : C ⊆ D) : ofCone C ⊆ ofCone D :=
  image_mono (preimage_mono h)

theorem ofCone_eq_ofCone_iff {C D : Set E} (hC : IsPosCone C) (hD : IsPosCone D) :
    ofCone C = ofCone D ↔ C \ {0} = D \ {0} := by
  constructor
  · intro h; rw [← F_ofCone hC, ← F_ofCone hD, h]
  · intro h
    ext x
    induction x using ind with
    | h v hv =>
      rw [mk_mem_ofCone_iff hC, mk_mem_ofCone_iff hD]
      have := congrArg (v ∈ ·) h
      simpa [hv] using this

/-! ### Déf. 4 — linear subvarieties -/

/-- **A linear subvariety** of `S(E)` (Déf. 4, `bzdef:c1s1d4_sous_variete_lineaire`, p. 234):
`s(L - {O})` for a subspace `L ⊆ E`. -/
def linearSubvariety (L : Submodule ℝ E) : Set (Sphere E) := ofCone (L : Set E)

theorem F_linearSubvariety (L : Submodule ℝ E) : F (linearSubvariety L) = (L : Set E) \ {0} :=
  F_ofCone (isPosCone_submodule L)

theorem mk_mem_linearSubvariety {L : Submodule ℝ E} {v : E} (hv : v ≠ 0) :
    mk v hv ∈ linearSubvariety L ↔ v ∈ L :=
  mk_mem_ofCone_iff (isPosCone_submodule L) hv

/-- A linear subvariety is stable under the antipodal map. -/
theorem neg_mem_linearSubvariety {L : Submodule ℝ E} {x : Sphere E}
    (hx : x ∈ linearSubvariety L) : -x ∈ linearSubvariety L := by
  induction x using ind with
  | h v hv =>
    rw [neg_mk, mk_mem_linearSubvariety]
    exact L.neg_mem ((mk_mem_linearSubvariety hv).1 hx)

/-- **Example (p. 234):** for `L = ℝv` of dimension 1, `s(L - {O})` is formed of two points,
diametrically opposite. -/
theorem linearSubvariety_span_singleton {v : E} (hv : v ≠ 0) :
    linearSubvariety (ℝ ∙ v) = {mk v hv, -mk v hv} := by
  ext x
  induction x using ind with
  | h w hw =>
    rw [mk_mem_linearSubvariety, Submodule.mem_span_singleton, mem_insert_iff,
      mem_singleton_iff, neg_mk, mk_eq_mk_iff_exists_pos, mk_eq_mk_iff_exists_pos]
    constructor
    · rintro ⟨a, rfl⟩
      have ha : a ≠ 0 := by rintro rfl; simp at hw
      rcases ha.lt_or_gt with h | h
      · exact Or.inr ⟨-a⁻¹, by simpa using h, by
          rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_smul, one_smul]⟩
      · exact Or.inl ⟨a⁻¹, inv_pos.2 h, by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]⟩
    · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
      · exact ⟨c⁻¹, by rw [← h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
      · exact ⟨-c⁻¹, by rw [neg_smul, ← smul_neg, ← h, smul_smul, inv_mul_cancel₀ hc.ne',
          one_smul]⟩

/-- The two points of a 1-dimensional linear subvariety are distinct. -/
theorem mk_ne_neg_mk {v : E} (hv : v ≠ 0) : mk v hv ≠ -mk v hv :=
  fun h => Sphere.neg_ne_self _ h.symm

/-- A *line* (« droite », p. 234): `s(L - {O})` with `dim L = 2`. -/
def IsLine (A : Set (Sphere E)) : Prop :=
  ∃ L : Submodule ℝ E, Module.finrank ℝ L = 2 ∧ A = linearSubvariety L

/-- A *hyperplane* (p. 234, printed « de $S(T)$ », read `S(E)`): `s(L - {O})` with `L` of
codimension 1. -/
def IsHyperplane (A : Set (Sphere E)) : Prop :=
  ∃ L : Submodule ℝ E, Module.finrank ℝ (E ⧸ L) = 1 ∧ A = linearSubvariety L

/-- A subspace of codimension 1 is the kernel of a nonzero linear form. -/
theorem exists_dual_ker_eq {L : Submodule ℝ E} (hL : Module.finrank ℝ (E ⧸ L) = 1) :
    ∃ l : Module.Dual ℝ E, l ≠ 0 ∧ LinearMap.ker l = L := by
  haveI : Module.Finite ℝ (E ⧸ L) := Module.finite_of_finrank_eq_succ hL
  let e : (E ⧸ L) ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq _ _ (by rw [hL, Module.finrank_self])
  refine ⟨(e : (E ⧸ L) →ₗ[ℝ] ℝ).comp L.mkQ, ?_, ?_⟩
  · intro h
    obtain ⟨v, hv⟩ := L.mkQ_surjective (e.symm 1)
    have := LinearMap.congr_fun h v
    simp [hv] at this
  · rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

/-- The hyperplane of a nonzero form has codimension 1. -/
theorem isHyperplane_linearSubvariety_ker {l : Module.Dual ℝ E} (hl : l ≠ 0) :
    IsHyperplane (linearSubvariety (LinearMap.ker l)) := by
  obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
    by_contra! h; exact hl (LinearMap.ext h)
  have hsurj : Function.Surjective l := fun c => ⟨(c / l u) • u, by
    simp [div_mul_cancel₀ c hu]⟩
  refine ⟨LinearMap.ker l, ?_, rfl⟩
  rw [(l.quotKerEquivOfSurjective hsurj).finrank_eq, Module.finrank_self]

/-! ### Déf. 5 — open hemispheres -/

/-- The open hemisphere of equation `l`: `s(l⁻¹(ℝ⁺))`. -/
def openHemisphere (l : Module.Dual ℝ E) : Set (Sphere E) := ofCone {v | 0 < l v}

/-- The closed hemisphere of equation `l`: `s(l⁻¹([0, ∞)) - {O})`. -/
def closedHemisphere (l : Module.Dual ℝ E) : Set (Sphere E) := ofCone {v | 0 ≤ l v}

theorem isPosCone_pos (l : Module.Dual ℝ E) : IsPosCone {v : E | 0 < l v} :=
  fun c hc v hv => by simp only [mem_setOf_eq, map_smul, smul_eq_mul] at hv ⊢; positivity

theorem isPosCone_nonneg (l : Module.Dual ℝ E) : IsPosCone {v : E | 0 ≤ l v} :=
  fun c hc v hv => by simp only [mem_setOf_eq, map_smul, smul_eq_mul] at hv ⊢; positivity

theorem mk_mem_openHemisphere {l : Module.Dual ℝ E} {v : E} (hv : v ≠ 0) :
    mk v hv ∈ openHemisphere l ↔ 0 < l v :=
  mk_mem_ofCone_iff (isPosCone_pos l) hv

theorem mk_mem_closedHemisphere {l : Module.Dual ℝ E} {v : E} (hv : v ≠ 0) :
    mk v hv ∈ closedHemisphere l ↔ 0 ≤ l v :=
  mk_mem_ofCone_iff (isPosCone_nonneg l) hv

/-- `F(H) = l⁻¹(ℝ⁺)` for the open hemisphere of equation `l`. -/
theorem F_openHemisphere (l : Module.Dual ℝ E) : F (openHemisphere l) = l ⁻¹' Ioi 0 := by
  rw [openHemisphere, F_ofCone (isPosCone_pos l)]
  ext v
  simp only [mem_sdiff, mem_setOf_eq, mem_singleton_iff, mem_preimage, mem_Ioi,
    and_iff_left_iff_imp]
  rintro h rfl
  simp at h

/-- **Déf. 5 as printed** (`bzdef:c1s1d5_hemisphere`, p. 234): `H` is open and `F(H) = l⁻¹(ℝ⁺)`
for some linear form `l ∈ E^*` (« son équation »). The reading of DEC-114 adds `l ≠ 0` (equivalently
`H ≠ ∅`, `openHemisphere_nonempty_iff`), carried by the theorems on the frontier and the closure. -/
def IsOpenHemisphere [TopologicalSpace E] (H : Set (Sphere E)) : Prop :=
  IsOpen H ∧ ∃ l : Module.Dual ℝ E, F H = l ⁻¹' Ioi 0

theorem isOpenHemisphere_iff_exists_eq [TopologicalSpace E] {H : Set (Sphere E)} :
    IsOpenHemisphere H ↔ IsOpen H ∧ ∃ l : Module.Dual ℝ E, H = openHemisphere l := by
  refine and_congr_right fun _ => exists_congr fun l => ?_
  rw [← F_openHemisphere]
  exact F_injective.eq_iff

/-- **The equation of an open hemisphere is defined up to a positive multiplier** (Déf. 5,
« La forme linéaire $l$ est définie à un multiplicateur positif près »), for all `l, l'`
(including `l = 0`). -/
theorem openHemisphere_eq_iff (l l' : Module.Dual ℝ E) :
    openHemisphere l = openHemisphere l' ↔ ∃ c : ℝ, 0 < c ∧ l' = c • l := by
  constructor
  · intro h
    have hpos : ∀ v, 0 < l v ↔ 0 < l' v := by
      intro v
      have := congrArg (v ∈ ·) ((F_openHemisphere l).symm.trans
        ((congrArg F h).trans (F_openHemisphere l')))
      simpa using this
    have hker : ∀ v, l v = 0 → l' v = 0 := by
      intro v hv
      have h1 : ¬ 0 < l' v := by rw [← hpos]; simp [hv]
      have h2 : ¬ 0 < l' (-v) := by rw [← hpos]; simp [hv]
      simp only [not_lt] at h1 h2
      have := l'.map_neg v
      linarith
    by_cases hl : l = 0
    · subst hl
      refine ⟨1, one_pos, ?_⟩
      ext v
      simp only [LinearMap.zero_apply, one_smul] at hpos ⊢
      have h1 := (hpos v).not.1 (lt_irrefl 0)
      have h2 := (hpos (-v)).not.1 (lt_irrefl 0)
      simp only [not_lt] at h1 h2
      have := l'.map_neg v
      linarith
    · obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
        by_contra! h; exact hl (LinearMap.ext h)
      set u' := (l u)⁻¹ • u with hu'
      have hlu' : l u' = 1 := by simp [hu', inv_mul_cancel₀ hu]
      refine ⟨l' u', (hpos u').1 (by rw [hlu']; exact one_pos), ?_⟩
      ext v
      have : l (v - l v • u') = 0 := by simp [hlu']
      have := hker _ this
      simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
      simp [this, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    rw [openHemisphere, openHemisphere]
    congr 1
    ext v
    simp only [mem_setOf_eq, LinearMap.smul_apply, smul_eq_mul]
    exact ⟨fun h => mul_pos hc h, fun h => pos_of_mul_pos_right h hc.le⟩

/-- **Remark (Déf. 5, literal reading):** with the zero form, the empty set is an open hemisphere as
printed. The reading of DEC-114 (`l ≠ 0`) excludes it. -/
theorem isOpenHemisphere_empty [TopologicalSpace E] : IsOpenHemisphere (∅ : Set (Sphere E)) :=
  ⟨isOpen_empty, 0, by ext v; simp⟩

/-- **Remark (Déf. 5, literal reading):** the frontier of the open hemisphere of equation `0` is
empty, while the set `h` with `F(h) ∪ {O} = 0⁻¹(O) = E` is all of `S(E)`, not a hyperplane. This is
why « l'hyperplan fermé $h$ » forces `l ≠ 0` (DEC-114). -/
theorem frontier_openHemisphere_zero [TopologicalSpace E] [Nontrivial E] :
    frontier (openHemisphere (0 : Module.Dual ℝ E)) = ∅ ∧
      linearSubvariety (LinearMap.ker (0 : Module.Dual ℝ E)) = univ ∧
      (univ : Set (Sphere E)).Nonempty := by
  have h0 : openHemisphere (0 : Module.Dual ℝ E) = ∅ := by
    apply F_injective; rw [F_openHemisphere]; ext v; simp
  refine ⟨by rw [h0, frontier_empty], ?_, ?_⟩
  · rw [LinearMap.ker_zero]
    apply F_injective
    rw [F_linearSubvariety, F_univ]
    simp [compl_eq_univ_sdiff]
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact ⟨mk v hv, trivial⟩

/-! #### Déf. 5 under the reading `l ≠ 0` (DEC-114) -/

theorem exists_pos_of_ne_zero {l : Module.Dual ℝ E} (hl : l ≠ 0) : ∃ u, 0 < l u := by
  obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
    by_contra! h; exact hl (LinearMap.ext h)
  rcases hu.lt_or_gt with h | h
  · exact ⟨-u, by simpa using h⟩
  · exact ⟨u, h⟩

/-- An open hemisphere is nonempty iff its equation is nonzero. -/
theorem openHemisphere_nonempty_iff (l : Module.Dual ℝ E) :
    (openHemisphere l).Nonempty ↔ l ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    induction x using ind with
    | h v hv => rw [mk_mem_openHemisphere] at hx; simp at hx
  · intro hl
    obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    exact ⟨mk u hu0, (mk_mem_openHemisphere hu0).2 hu⟩

/-- The closed hemisphere is `H ∪ h` (Déf. 5, « La fermeture $H\cup h$ de $H$ »). -/
theorem closedHemisphere_eq_union (l : Module.Dual ℝ E) :
    closedHemisphere l = openHemisphere l ∪ linearSubvariety (LinearMap.ker l) := by
  ext x
  induction x using ind with
  | h v hv =>
    rw [mem_union, mk_mem_closedHemisphere, mk_mem_openHemisphere, mk_mem_linearSubvariety,
      LinearMap.mem_ker, le_iff_lt_or_eq, eq_comm]

/-- `F(h) ∪ {O} = l⁻¹(O)` for the hyperplane `h = s(ker l - {O})`. -/
theorem F_linearSubvariety_ker_union (l : Module.Dual ℝ E) :
    F (linearSubvariety (LinearMap.ker l)) ∪ {0} = l ⁻¹' {0} := by
  rw [F_linearSubvariety]
  ext v
  by_cases h : v = 0 <;> simp [h]

theorem eq_openHemisphere_of_F_eq {H : Set (Sphere E)} {l : Module.Dual ℝ E}
    (hF : F H = l ⁻¹' Ioi 0) : H = openHemisphere l :=
  F_injective (hF.trans (F_openHemisphere l).symm)


/-- `h = s(ker l - {O})` from its equation `F(h) ∪ {O} = l⁻¹(O)`. -/
theorem eq_linearSubvariety_ker_of_F_union {h : Set (Sphere E)} {l : Module.Dual ℝ E}
    (hl : F h ∪ {0} = l ⁻¹' {0}) : h = linearSubvariety (LinearMap.ker l) := by
  apply F_injective
  rw [F_linearSubvariety]
  ext v
  by_cases hv : v = 0
  · simp [hv, zero_notMem_F]
  · have := congrArg (v ∈ ·) hl
    simp only [mem_union, mem_singleton_iff, hv, or_false, mem_preimage, eq_iff_iff] at this
    simp [this, hv]

/-- A hyperplane is not all of `S(E)`. -/
theorem IsHyperplane.ne_univ {h : Set (Sphere E)} (hh : IsHyperplane h) : h ≠ univ := by
  obtain ⟨L, hL, rfl⟩ := hh
  obtain ⟨l, hl0, hker⟩ := exists_dual_ker_eq hL
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl0
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  intro h
  have := (mk_mem_linearSubvariety (L := L) hu0).1 (h ▸ mem_univ _)
  rw [← hker, LinearMap.mem_ker] at this
  exact hu.ne' this

section Continuous

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The open hemisphere of a continuous form is open. -/
theorem isOpen_openHemisphere (l : E →L[ℝ] ℝ) : IsOpen (openHemisphere (l : Module.Dual ℝ E)) :=
  isOpen_ofCone (isPosCone_pos _) (isOpen_lt continuous_const l.continuous)

/-- In finite dimension, Déf. 5 as printed is « `H` is the open hemisphere of some `l` ». -/
theorem isOpenHemisphere_iff [T2Space E] [FiniteDimensional ℝ E] {H : Set (Sphere E)} :
    IsOpenHemisphere H ↔ ∃ l : Module.Dual ℝ E, H = openHemisphere l := by
  rw [isOpenHemisphere_iff_exists_eq]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨l, rfl⟩
    refine ⟨?_, l, rfl⟩
    exact isOpen_openHemisphere ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

omit [T1Space E] in
/-- `closure {l > 0} = {l ≥ 0}` in `E`, for a continuous nonzero form. -/
theorem closure_pos_eq_nonneg {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    closure {v : E | 0 < l v} = {v | 0 ≤ l v} := by
  apply Subset.antisymm
  · exact closure_minimal (fun v (hv : 0 < l v) => (le_of_lt hv : 0 ≤ l v))
      (isClosed_le continuous_const l.continuous)
  · intro v hv
    obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
      by_contra! h; exact hl (ContinuousLinearMap.ext h)
    obtain ⟨w, hw⟩ : ∃ w, 0 < l w := by
      rcases hu.lt_or_gt with h | h
      · exact ⟨-u, by simpa using h⟩
      · exact ⟨u, h⟩
    have ht : Filter.Tendsto (fun t : ℝ => v + t • w) (𝓝[>] 0) (𝓝 v) := by
      have : Continuous fun t : ℝ => v + t • w :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
    simp only [map_add, map_smul, smul_eq_mul]
    have := mul_pos htpos hw
    linarith [show (0 : ℝ) ≤ l v from hv]

/-- **The closure of an open hemisphere** is the closed hemisphere (Déf. 5, « La fermeture
$H\cup h$ de $H$ »), for a continuous `l ≠ 0`. -/
theorem closure_openHemisphere {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    closure (openHemisphere (l : Module.Dual ℝ E)) = closedHemisphere (l : Module.Dual ℝ E) := by
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hs := (isOpenMap_s (E := E)).preimage_closure_eq_closure_preimage continuous_s
    (openHemisphere (l : Module.Dual ℝ E))
  have hv := hopen.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val {v : E | 0 < l v}
  apply F_injective
  ext v
  by_cases h0 : v = 0
  · subst h0; simp [zero_notMem_F]
  · rw [← mk_mem_iff_mem_F h0, ← mk_mem_iff_mem_F h0, mk_mem_closedHemisphere]
    have := congrArg (⟨v, h0⟩ ∈ ·) hs
    simp only [mem_preimage, s_apply] at this
    rw [this, s_preimage_eq, F_openHemisphere]
    have hv' := congrArg (⟨v, h0⟩ ∈ ·) hv
    simp only [mem_preimage] at hv'
    change ⟨v, h0⟩ ∈ closure (Subtype.val ⁻¹' {v : E | 0 < l v}) ↔ _
    refine (Iff.of_eq hv').symm.trans ?_
    rw [closure_pos_eq_nonneg hl]
    rfl

/-- **The frontier of an open hemisphere** is the closed hyperplane `h` with
`F(h) ∪ {O} = l⁻¹(O)` (Déf. 5), for a continuous `l ≠ 0`. -/
theorem frontier_openHemisphere {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    frontier (openHemisphere (l : Module.Dual ℝ E)) =
      linearSubvariety (LinearMap.ker (l : Module.Dual ℝ E)) := by
  rw [frontier, closure_openHemisphere hl, (isOpen_openHemisphere l).interior_eq]
  ext x
  induction x using ind with
  | h v hv =>
    rw [mem_sdiff, mk_mem_closedHemisphere, mk_mem_openHemisphere, mk_mem_linearSubvariety,
      LinearMap.mem_ker]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.1 h2) h1
    · intro h; simp [h]

theorem F_frontier_openHemisphere {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    F (frontier (openHemisphere (l : Module.Dual ℝ E))) ∪ {0} = l ⁻¹' {0} := by
  rw [frontier_openHemisphere hl, F_linearSubvariety]
  ext v
  by_cases h : v = 0 <;> simp [h]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The frontier hyperplane is closed. -/
theorem isClosed_linearSubvariety_ker (l : E →L[ℝ] ℝ) :
    IsClosed (linearSubvariety (LinearMap.ker (l : Module.Dual ℝ E))) := by
  have : linearSubvariety (LinearMap.ker (l : Module.Dual ℝ E)) =
      (openHemisphere (l : Module.Dual ℝ E) ∪ openHemisphere (-(l : Module.Dual ℝ E)))ᶜ := by
    ext x
    induction x using ind with
    | h v hv =>
      simp only [mem_compl_iff, mem_union, mk_mem_openHemisphere, mk_mem_linearSubvariety,
        LinearMap.mem_ker, LinearMap.neg_apply, Left.neg_pos_iff, not_or, not_lt]
      constructor
      · intro h; simp [h]
      · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  rw [this]
  exact ((isOpen_openHemisphere l).union (isOpen_openHemisphere (-l))).isClosed_compl

/-- The open hemisphere of equation `-l` has the same frontier `h` (p. 235, « deux hémisphères
ouverts disjoints de frontière $h$ »). -/
theorem frontier_openHemisphere_neg {l : E →L[ℝ] ℝ} (hl : l ≠ 0) :
    frontier (openHemisphere (-(l : Module.Dual ℝ E))) =
      linearSubvariety (LinearMap.ker (l : Module.Dual ℝ E)) := by
  have := frontier_openHemisphere (l := -l) (neg_ne_zero.2 hl)
  simpa [LinearMap.ker_neg] using this

end Continuous

/-- **The converse paragraph** (p. 235): the complement of the hyperplane `h = s(ker l - {O})` is
the union of the open hemispheres of equations `l` and `-l`, ... -/
theorem compl_hyperplane (l : Module.Dual ℝ E) :
    (linearSubvariety (LinearMap.ker l))ᶜ = openHemisphere l ∪ openHemisphere (-l) := by
  ext x
  induction x using ind with
  | h v hv =>
    simp only [mem_compl_iff, mem_union, mk_mem_openHemisphere, mk_mem_linearSubvariety,
      LinearMap.mem_ker, LinearMap.neg_apply, Left.neg_pos_iff]
    constructor
    · intro h; rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h) hk <;> rw [hk] at h <;> exact lt_irrefl 0 h

/-- ... which are disjoint. -/
theorem disjoint_openHemisphere_neg (l : Module.Dual ℝ E) :
    Disjoint (openHemisphere l) (openHemisphere (-l)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  induction x using ind with
  | h v hv =>
    rw [mk_mem_openHemisphere] at hx hx'
    simp only [LinearMap.neg_apply, Left.neg_pos_iff] at hx'
    linarith

/-- The equation of a hyperplane is defined up to a nonzero multiplier (p. 235, « $l$ est défini à
un multiplicateur non nul près »). -/
theorem hyperplane_eq_iff {l l' : Module.Dual ℝ E} (hl : l ≠ 0) (hl' : l' ≠ 0) :
    linearSubvariety (LinearMap.ker l) = linearSubvariety (LinearMap.ker l') ↔
      ∃ c : ℝ, c ≠ 0 ∧ l' = c • l := by
  constructor
  · intro h
    rw [linearSubvariety, linearSubvariety,
      ofCone_eq_ofCone_iff (isPosCone_submodule _) (isPosCone_submodule _)] at h
    have hker : ∀ v, l v = 0 → l' v = 0 := by
      intro v hv
      by_cases h0 : v = 0
      · simp [h0]
      · have := congrArg (v ∈ ·) h
        simp only [mem_sdiff, SetLike.mem_coe, LinearMap.mem_ker, mem_singleton_iff, h0,
          not_false_eq_true, and_true, eq_iff_iff] at this
        exact this.1 hv
    obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
      by_contra! h; exact hl (LinearMap.ext h)
    set u' := (l u)⁻¹ • u with hu'
    have hlu' : l u' = 1 := by simp [hu', inv_mul_cancel₀ hu]
    have hl'eq : l' = l' u' • l := by
      ext v
      have : l (v - l v • u') = 0 := by simp [hlu']
      have := hker _ this
      simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
      simp [this, mul_comm]
    refine ⟨l' u', fun h0 => hl' ?_, hl'eq⟩
    rw [hl'eq, h0, zero_smul]
  · rintro ⟨c, hc, rfl⟩
    congr 1
    ext v
    simp [hc]

/-! #### Déf. 5 for `H` itself, and the converse paragraph with a continuous equation -/

section ContinuousEquation

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T1Space E]

/-- **The equation of a nonempty open hemisphere is continuous**: if `H` is open and
`F(H) = l⁻¹(ℝ⁺)` with `l ≠ 0` (equivalently `H ≠ ∅`), then `l` is continuous (`l` does not vanish on
the nonempty open cone `F(H)`). -/
theorem continuous_of_isOpen_of_F_eq {H : Set (Sphere E)} (hH : IsOpen H) {l : Module.Dual ℝ E}
    (hF : F H = l ⁻¹' Ioi 0) (hl : l ≠ 0) : Continuous l := by
  have hFo : IsOpen (F H) := isOpen_iff_F.1 hH
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
  refine l.continuous_of_nonzero_on_open (F H) hFo ⟨u, by rw [hF]; exact hu⟩ fun v hv => ?_
  rw [hF] at hv
  exact (ne_of_lt hv).symm

/-- **The equation of a closed hyperplane is continuous** (p. 235): if `h = s(ker l - {O})` is
closed, `l ≠ 0`, then `l` is continuous (`l` does not vanish on the nonempty open cone `F(∁h)`). -/
theorem continuous_of_isClosed_linearSubvariety_ker {l : Module.Dual ℝ E} (hl : l ≠ 0)
    (hc : IsClosed (linearSubvariety (LinearMap.ker l))) : Continuous l := by
  have hFo : IsOpen (F (linearSubvariety (LinearMap.ker l))ᶜ) := isOpen_iff_F.1 hc.isOpen_compl
  have hmem : ∀ v, v ∈ F (linearSubvariety (LinearMap.ker l))ᶜ ↔ l v ≠ 0 := by
    intro v
    rw [F_compl, F_linearSubvariety]
    by_cases h : v = 0 <;> simp [h]
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
  exact l.continuous_of_nonzero_on_open _ hFo ⟨u, (hmem u).2 hu.ne'⟩ fun v hv => (hmem v).1 hv


/-- **Déf. 5 for the open hemisphere `H` itself** (the reading of DEC-114: `l ≠ 0`, forced by
« l'hyperplan fermé $h$ », equivalently `H ≠ ∅`). If `H` is open, `F(H) = l⁻¹(ℝ⁺)` and `l ≠ 0`,
then, with `h = s(ker l - {O})`: `h` is a closed hyperplane, `F(h) ∪ {O} = l⁻¹(O)`, the frontier of
`H` is `h`, and the closure of `H` is `H ∪ h`. No continuity is assumed: it is derived
(`continuous_of_isOpen_of_F_eq`). -/
theorem isOpenHemisphere_frontier_closure {H : Set (Sphere E)} (hH : IsOpen H)
    {l : Module.Dual ℝ E} (hF : F H = l ⁻¹' Ioi 0) (hl : l ≠ 0) :
    IsHyperplane (linearSubvariety (LinearMap.ker l)) ∧
      IsClosed (linearSubvariety (LinearMap.ker l)) ∧
      F (linearSubvariety (LinearMap.ker l)) ∪ {0} = l ⁻¹' {0} ∧
      frontier H = linearSubvariety (LinearMap.ker l) ∧
      closure H = H ∪ linearSubvariety (LinearMap.ker l) := by
  let L : E →L[ℝ] ℝ := ⟨l, continuous_of_isOpen_of_F_eq hH hF hl⟩
  have hLl : (L : Module.Dual ℝ E) = l := rfl
  have hL : L ≠ 0 := fun h0 => hl (by rw [← hLl, h0]; rfl)
  have hHe := eq_openHemisphere_of_F_eq hF
  refine ⟨isHyperplane_linearSubvariety_ker hl, hLl ▸ isClosed_linearSubvariety_ker L,
    F_linearSubvariety_ker_union l, ?_, ?_⟩
  · rw [hHe, ← hLl]; exact frontier_openHemisphere hL
  · rw [hHe, ← hLl, closure_openHemisphere hL, closedHemisphere_eq_union]

/-- **The converse paragraph** (p. 235, « Réciproquement, soit $h$ un hyperplan fermé de $S(E)$ »):
a closed hyperplane `h` has a CONTINUOUS equation `l ≠ 0`, `F(h) ∪ {O} = l⁻¹(O)`; `∁h` is the union
of the two disjoint open hemispheres of equations `l` and `-l`, both of frontier `h`. -/
theorem closedHyperplane_converse {h : Set (Sphere E)} (hh : IsHyperplane h) (hc : IsClosed h) :
    ∃ l : E →L[ℝ] ℝ, (l : Module.Dual ℝ E) ≠ 0 ∧ F h ∪ {0} = l ⁻¹' {0} ∧
      hᶜ = openHemisphere (l : Module.Dual ℝ E) ∪ openHemisphere (-(l : Module.Dual ℝ E)) ∧
      Disjoint (openHemisphere (l : Module.Dual ℝ E)) (openHemisphere (-(l : Module.Dual ℝ E))) ∧
      IsOpenHemisphere (openHemisphere (l : Module.Dual ℝ E)) ∧
      IsOpenHemisphere (openHemisphere (-(l : Module.Dual ℝ E))) ∧
      frontier (openHemisphere (l : Module.Dual ℝ E)) = h ∧
      frontier (openHemisphere (-(l : Module.Dual ℝ E))) = h := by
  obtain ⟨L, hL, rfl⟩ := hh
  obtain ⟨l, hl0, hker⟩ := exists_dual_ker_eq hL
  subst hker
  let l' : E →L[ℝ] ℝ := ⟨l, continuous_of_isClosed_linearSubvariety_ker hl0 hc⟩
  have hl'l : (l' : Module.Dual ℝ E) = l := rfl
  have hl' : l' ≠ 0 := fun h0 => hl0 (by rw [← hl'l, h0]; rfl)
  refine ⟨l', hl0, F_linearSubvariety_ker_union l, compl_hyperplane l,
    disjoint_openHemisphere_neg l, ⟨isOpen_openHemisphere l', l, F_openHemisphere l⟩,
    ⟨isOpen_openHemisphere (-l'), -l, F_openHemisphere (-l)⟩, frontier_openHemisphere hl',
    frontier_openHemisphere_neg hl'⟩

/-- **Every equation of a closed hyperplane is continuous and nonzero** (p. 235, « désignons par $l$
une forme linéaire continue sur $E$ telle que $F(h)\cup\{O\}=l^{-1}(O)$ »). -/
theorem continuous_of_F_union_eq {h : Set (Sphere E)} (hh : IsHyperplane h) (hc : IsClosed h)
    {l : Module.Dual ℝ E} (hl : F h ∪ {0} = l ⁻¹' {0}) : l ≠ 0 ∧ Continuous l := by
  have he := eq_linearSubvariety_ker_of_F_union hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hh.ne_univ
    rw [he, LinearMap.ker_zero]
    apply F_injective
    rw [F_linearSubvariety, F_univ]
    simp [compl_eq_univ_sdiff]
  exact ⟨hl0, continuous_of_isClosed_linearSubvariety_ker hl0 (he ▸ hc)⟩

end ContinuousEquation

/-! ### Déf. 4, Exemples — the half-lines of a line -/

/-- The cone of a half-line: `{a v + b w | a ∈ ℝ, b > 0}`. -/
def halfLineCone (v w : E) : Set E := {u | ∃ a b : ℝ, 0 < b ∧ a • v + b • w = u}

theorem isPosCone_halfLineCone (v w : E) : IsPosCone (halfLineCone v w) := by
  rintro c hc _ ⟨a, b, hb, rfl⟩
  exact ⟨c * a, c * b, mul_pos hc hb, by rw [smul_add, smul_smul, smul_smul]⟩

/-- **A half-line** (« demi-droite », Déf. 4, Exemples, p. 234): for `v, w` independent, the rays
of `{a v + b w | a ∈ ℝ, b > 0}` — the half of the line `s(span {v, w} - {O})` on the side of `w`,
bounded by the diametrically opposite points `s(v)` and `s(-v)`. -/
def halfLine (v w : E) : Set (Sphere E) := ofCone (halfLineCone v w)

theorem mk_mem_halfLine {v w u : E} (hu : u ≠ 0) :
    mk u hu ∈ halfLine v w ↔ ∃ a b : ℝ, 0 < b ∧ a • v + b • w = u :=
  mk_mem_ofCone_iff (isPosCone_halfLineCone v w) hu

variable {v w : E}

theorem ne_zero_of_linearIndependent (hvw : LinearIndependent ℝ ![v, w]) {a b : ℝ} (hb : b ≠ 0) :
    a • v + b • w ≠ 0 := fun h => hb ((LinearIndependent.pair_iff.1 hvw a b h).2)

theorem mk_w_mem_halfLine (hvw : LinearIndependent ℝ ![v, w]) :
    mk w (hvw.ne_zero 1) ∈ halfLine v w :=
  (mk_mem_halfLine _).2 ⟨0, 1, one_pos, by simp⟩

theorem halfLine_nonempty (hvw : LinearIndependent ℝ ![v, w]) : (halfLine v w).Nonempty :=
  ⟨_, mk_w_mem_halfLine hvw⟩

theorem linearIndependent_neg_right (hvw : LinearIndependent ℝ ![v, w]) :
    LinearIndependent ℝ ![v, -w] := by
  rw [LinearIndependent.pair_iff] at hvw ⊢
  intro s t h
  have := hvw s (-t) (by rw [neg_smul, ← smul_neg]; exact h)
  exact ⟨this.1, neg_eq_zero.1 this.2⟩

/-- The two half-lines `halfLine v w`, `halfLine v (-w)` are disjoint. -/
theorem disjoint_halfLine_neg (hvw : LinearIndependent ℝ ![v, w]) :
    Disjoint (halfLine v w) (halfLine v (-w)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  induction x using ind with
  | h u hu =>
    obtain ⟨a, b, hb, rfl⟩ := (mk_mem_halfLine hu).1 hx
    obtain ⟨a', b', hb', h⟩ := (mk_mem_halfLine hu).1 hx'
    have := (LinearIndependent.pair_iff.1 hvw (a' - a) (-b' - b) (by
      rw [sub_smul, sub_smul, neg_smul]
      rw [smul_neg] at h
      linear_combination (norm := module) h)).2
    linarith

/-- **« Deux points diamétralement opposés divisent une droite en deux demi-droites »**: the line
`s(span {v, w} - {O})` minus the opposite points `s(v)`, `s(-v)` is the union of the half-lines
`halfLine v w` and `halfLine v (-w)`. -/
theorem linearSubvariety_pair_diff (hvw : LinearIndependent ℝ ![v, w]) :
    linearSubvariety (Submodule.span ℝ {v, w}) \ {mk v (hvw.ne_zero 0), -mk v (hvw.ne_zero 0)} =
      halfLine v w ∪ halfLine v (-w) := by
  have hv : v ≠ 0 := hvw.ne_zero 0
  ext x
  induction x using ind with
  | h u hu =>
    rw [mem_sdiff, mk_mem_linearSubvariety, Submodule.mem_span_pair, mem_union, mk_mem_halfLine,
      mk_mem_halfLine, mem_insert_iff, mem_singleton_iff, neg_mk, mk_eq_mk_iff_exists_pos,
      mk_eq_mk_iff_exists_pos]
    constructor
    · rintro ⟨⟨a, b, rfl⟩, hne⟩
      rcases lt_trichotomy b 0 with hb | rfl | hb
      · exact Or.inr ⟨a, -b, neg_pos.2 hb, by rw [smul_neg, neg_smul, neg_neg]⟩
      · exfalso
        simp only [zero_smul, add_zero] at hu hne
        have ha : a ≠ 0 := by rintro rfl; simp at hu
        rcases ha.lt_or_gt with h | h
        · exact hne (Or.inr ⟨-a⁻¹, neg_pos.2 (inv_lt_zero.2 h), by
            rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_smul, one_smul]⟩)
        · exact hne (Or.inl ⟨a⁻¹, inv_pos.2 h, by
            rw [smul_smul, inv_mul_cancel₀ ha, one_smul]⟩)
      · exact Or.inl ⟨a, b, hb, rfl⟩
    · have key : ∀ a b : ℝ, b ≠ 0 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ,
          c • (a • v + b • w) ≠ ε • v := by
        intro a b hb c hc ε h
        have := (LinearIndependent.pair_iff.1 hvw (c * a - ε) (c * b) (by
          rw [sub_smul, ← smul_smul, ← smul_smul, ← h]; module)).2
        exact (mul_ne_zero hc.ne' hb) this
      rintro (⟨a, b, hb, rfl⟩ | ⟨a, b, hb, rfl⟩)
      · refine ⟨⟨a, b, rfl⟩, ?_⟩
        rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · exact key a b hb.ne' c hc 1 (by rw [h, one_smul])
        · exact key a b hb.ne' c hc (-1) (by rw [h, neg_one_smul])
      · refine ⟨⟨a, -b, by rw [neg_smul, smul_neg]⟩, ?_⟩
        have hab : a • v + b • -w = a • v + (-b) • w := by rw [smul_neg, neg_smul]
        rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · rw [hab] at h
          exact key a (-b) (neg_ne_zero.2 hb.ne') c hc 1 (by rw [h, one_smul])
        · rw [hab] at h
          exact key a (-b) (neg_ne_zero.2 hb.ne') c hc (-1) (by rw [h, neg_one_smul])

theorem halfLine_subset_linearSubvariety (v w : E) :
    halfLine v w ⊆ linearSubvariety (Submodule.span ℝ {v, w}) := by
  apply ofCone_subset_ofCone
  rintro _ ⟨a, b, -, rfl⟩
  exact Submodule.mem_span_pair.2 ⟨a, b, rfl⟩

/-- Every line through a point `m` is `s(span {v, w} - {O})` with `m = s(v)` and `v, w`
independent. -/
theorem IsLine.exists_pair {D : Set (Sphere E)} (hD : IsLine D) {m : Sphere E} (hm : m ∈ D) :
    ∃ (v w : E) (hvw : LinearIndependent ℝ ![v, w]), m = mk v (hvw.ne_zero 0) ∧
      D = linearSubvariety (Submodule.span ℝ {v, w}) := by
  obtain ⟨L, hL, rfl⟩ := hD
  induction m using ind with
  | h v hv =>
  have hvL : v ∈ L := (mk_mem_linearSubvariety hv).1 hm
  haveI : Module.Finite ℝ L := Module.finite_of_finrank_pos (by rw [hL]; norm_num)
  have hlt : ℝ ∙ v ≠ L := by
    intro h
    have := finrank_span_singleton (K := ℝ) hv
    rw [h, hL] at this
    norm_num at this
  obtain ⟨w, hwL, hw⟩ : ∃ w ∈ L, w ∉ ℝ ∙ v := by
    by_contra! h
    exact hlt (le_antisymm ((Submodule.span_singleton_le_iff_mem v L).2 hvL) h)
  have hvw : LinearIndependent ℝ ![v, w] := by
    rw [LinearIndependent.pair_iff' hv]
    intro a ha
    exact hw (Submodule.mem_span_singleton.2 ⟨a, ha⟩)
  refine ⟨v, w, hvw, rfl, ?_⟩
  congr 1
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    exacts [hvL, hwL]
  · have := finrank_span_eq_card hvw
    rw [Matrix.range_cons_cons_empty] at this
    rw [this, hL]
    simp

/-- A half-line is the trace on its line of an open hemisphere whose frontier passes through the two
opposite points: `halfLine v w = D ∩ H` for any `l` with `l v = 0 < l w`. -/
theorem halfLine_eq_inter_openHemisphere (v w : E) {l : Module.Dual ℝ E} (hlv : l v = 0)
    (hlw : 0 < l w) :
    halfLine v w = linearSubvariety (Submodule.span ℝ {v, w}) ∩ openHemisphere l := by
  ext x
  induction x using ind with
  | h u hu =>
    rw [mem_inter_iff, mk_mem_halfLine, mk_mem_linearSubvariety, Submodule.mem_span_pair,
      mk_mem_openHemisphere]
    constructor
    · rintro ⟨a, b, hb, rfl⟩
      refine ⟨⟨a, b, rfl⟩, ?_⟩
      simp only [map_add, map_smul, hlv, smul_eq_mul, mul_zero, zero_add]
      exact mul_pos hb hlw
    · rintro ⟨⟨a, b, rfl⟩, h⟩
      simp only [map_add, map_smul, hlv, smul_eq_mul, mul_zero, zero_add] at h
      exact ⟨a, b, pos_of_mul_pos_left h hlw.le, rfl⟩

/-- For `v, w` independent there is a linear form `l` with `l v = 0 < l w`. -/
theorem exists_dual_pair (hvw : LinearIndependent ℝ ![v, w]) :
    ∃ l : Module.Dual ℝ E, l v = 0 ∧ 0 < l w := by
  have hw : w ∉ ℝ ∙ v := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    exact (LinearIndependent.pair_iff' (hvw.ne_zero 0)).1 hvw a ha
  obtain ⟨l, hlw, hle⟩ := Submodule.exists_le_ker_of_notMem hw
  have hlv : l v = 0 := hle (Submodule.mem_span_singleton_self v)
  rcases hlw.lt_or_gt with h | h
  · exact ⟨-l, by simp [hlv], by simpa using h⟩
  · exact ⟨l, hlv, h⟩

section Topology

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- A half-line is connected (the image of the half-plane `{b > 0}`). -/
theorem isConnected_halfLine (hvw : LinearIndependent ℝ ![v, w]) :
    IsConnected (halfLine v w) := by
  let P : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hP : IsConnected P := by
    refine ⟨⟨(0, 1), by simp [P]⟩, ?_⟩
    exact (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear 0).isPreconnected
  haveI : ConnectedSpace P := isConnected_iff_connectedSpace.1 hP
  let f : P → Sphere E := fun p => mk (p.1.1 • v + p.1.2 • w)
    (ne_zero_of_linearIndependent hvw p.2.ne')
  have hf : Continuous f := continuous_mk_comp
    (((continuous_fst.comp continuous_subtype_val).smul continuous_const).add
      ((continuous_snd.comp continuous_subtype_val).smul continuous_const)) _
  have : halfLine v w = range f := by
    ext x
    induction x using ind with
    | h u hu =>
      rw [mk_mem_halfLine]
      constructor
      · rintro ⟨a, b, hb, rfl⟩
        exact ⟨⟨(a, b), hb⟩, rfl⟩
      · rintro ⟨⟨⟨a, b⟩, hb⟩, h⟩
        obtain ⟨c, hc, hcu⟩ := (mk_eq_mk_iff_exists_pos _ hu).1 h
        exact ⟨c * a, c * b, mul_pos hc hb, by rw [← hcu, smul_add, smul_smul, smul_smul]⟩
  rw [this]
  exact isConnected_range hf

end Topology

/-- **The two half-lines are separated**: for a continuous form `l` with `l v = 0 < l w`, the line
minus the opposite points `s(v)`, `s(-v)` is not connected — its two half-lines are cut out by the
disjoint open hemispheres of equations `l` and `-l`. -/
theorem not_isPreconnected_linearSubvariety_pair_diff {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [T1Space E] {v w : E} (hvw : LinearIndependent ℝ ![v, w])
    (l : E →L[ℝ] ℝ) (hlv : l v = 0) (hlw : 0 < l w) :
    ¬ IsPreconnected (linearSubvariety (Submodule.span ℝ {v, w}) \
      {mk v (hvw.ne_zero 0), -mk v (hvw.ne_zero 0)}) := by
  rw [linearSubvariety_pair_diff hvw]
  intro h
  have h₁ := halfLine_eq_inter_openHemisphere v w (l := (l : Module.Dual ℝ E)) hlv hlw
  have h₂ := halfLine_eq_inter_openHemisphere v (-w) (l := -(l : Module.Dual ℝ E))
    (by simp [hlv]) (by simpa using hlw)
  obtain ⟨x, hx, hx₁, hx₂⟩ := h (openHemisphere (l : Module.Dual ℝ E))
    (openHemisphere (-(l : Module.Dual ℝ E))) (isOpen_openHemisphere l)
    (isOpen_openHemisphere (-l))
    (by
      rintro x (hx | hx)
      · exact Or.inl (h₁ ▸ hx).2
      · exact Or.inr (h₂ ▸ hx).2)
    ⟨_, Or.inl (mk_w_mem_halfLine hvw), (h₁ ▸ mk_w_mem_halfLine hvw).2⟩
    ⟨_, Or.inr (mk_w_mem_halfLine (linearIndependent_neg_right hvw)),
      (h₂ ▸ mk_w_mem_halfLine (linearIndependent_neg_right hvw)).2⟩
  exact Set.disjoint_left.1 (disjoint_openHemisphere_neg (l : Module.Dual ℝ E)) hx₁ hx₂

/-- **« Deux points diamétralement opposés divisent une droite en deux demi-droites »** (Déf. 4,
Exemples, p. 234), in finite dimension: for a line `D` of `S(E)` and `m ∈ D`, `D - {m, -m}` is the
disjoint union of the two half-lines `halfLine v w` and `halfLine v (-w)` (`m = s(v)`), each
nonempty and connected, and `D - {m, -m}` is not connected. -/
theorem IsLine.diff_eq_halfLines {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    {D : Set (Sphere E)} (hD : IsLine D) {m : Sphere E} (hm : m ∈ D) :
    ∃ (v w : E) (hvw : LinearIndependent ℝ ![v, w]), m = mk v (hvw.ne_zero 0) ∧
      D = linearSubvariety (Submodule.span ℝ {v, w}) ∧
      D \ {m, -m} = halfLine v w ∪ halfLine v (-w) ∧
      Disjoint (halfLine v w) (halfLine v (-w)) ∧
      IsConnected (halfLine v w) ∧ IsConnected (halfLine v (-w)) ∧
      ¬ IsPreconnected (D \ {m, -m}) := by
  obtain ⟨v, w, hvw, rfl, rfl⟩ := hD.exists_pair hm
  obtain ⟨l, hlv, hlw⟩ := exists_dual_pair hvw
  refine ⟨v, w, hvw, rfl, rfl, linearSubvariety_pair_diff hvw, disjoint_halfLine_neg hvw,
    isConnected_halfLine hvw, isConnected_halfLine (linearIndependent_neg_right hvw), ?_⟩
  exact not_isPreconnected_linearSubvariety_pair_diff hvw
    ⟨l, LinearMap.continuous_of_finiteDimensional l⟩ hlv hlw


/-! ### Déf. 10 — the quotient `S(E)/l` -/

/-- **Déf. 8, first printed form, in the reading `F(k) ∪ {O}`** (« On appelle partie convexe
$k\subset S(E)$ une partie $k$ telle que $F(k)+\{O\}$ soit un convexe de $E$ »). This is the reading
under **OQ-24, RULED by DEC-120**: the `+` is a union (a convex cone with apex `O`), not a Minkowski
sum (which would make Déf. 9 vacuous). Déf. 8 is certified in `Projective/Convex` (wave 2), with the
segment form; used here to state Déf. 10. -/
def IsConvexPart (k : Set (Sphere E)) : Prop := Convex ℝ (insert 0 (F k))

/-- **`S(E)/l`** (Déf. 10, `bzdef:c1s1d10_quotient`, p. 235): the sphere `S(E/L)`. -/
abbrev quotient (L : Submodule ℝ E) : Type _ := Sphere (E ⧸ L)

/-- The part of `S(E)` corresponding to a part `k'` of `S(E)/l`: `s(q⁻¹(F(k') ∪ {O}) - {O})`. -/
def quotientPreimage (L : Submodule ℝ E) (k' : Set (quotient L)) : Set (Sphere E) :=
  ofCone (L.mkQ ⁻¹' insert 0 (F k'))

/-- The part of `S(E)/l` corresponding to a part `k` of `S(E)`: `s(q(F(k)) - {O})`. -/
def quotientImage (L : Submodule ℝ E) (k : Set (Sphere E)) : Set (quotient L) :=
  ofCone (L.mkQ '' F k)

theorem isPosCone_insert_zero {C : Set E} (hC : IsPosCone C) : IsPosCone (insert 0 C) := by
  rintro c hc v (rfl | hv)
  · simp
  · exact Or.inr (hC c hc v hv)

theorem isPosCone_preimage {E' : Type*} [AddCommGroup E'] [Module ℝ E'] (f : E →ₗ[ℝ] E')
    {C : Set E'} (hC : IsPosCone C) : IsPosCone (f ⁻¹' C) :=
  fun c hc v hv => by simpa [mem_preimage, map_smul] using hC c hc _ hv

theorem isPosCone_image {E' : Type*} [AddCommGroup E'] [Module ℝ E'] (f : E →ₗ[ℝ] E')
    {C : Set E} (hC : IsPosCone C) : IsPosCone (f '' C) := by
  rintro c hc _ ⟨v, hv, rfl⟩
  exact ⟨c • v, hC c hc v hv, map_smul f c v⟩

theorem insert_zero_F_ofCone {C : Set E} (hC : IsPosCone C) :
    insert 0 (F (ofCone C)) = insert 0 C := by
  rw [F_ofCone hC]
  ext v
  by_cases h : v = 0 <;> simp [h]

theorem linearSubvariety_subset_quotientPreimage (L : Submodule ℝ E) (k' : Set (quotient L)) :
    linearSubvariety L ⊆ quotientPreimage L k' := by
  apply ofCone_subset_ofCone
  intro v hv
  simp [(Submodule.Quotient.mk_eq_zero L).2 hv]

theorem isConvexPart_quotientPreimage (L : Submodule ℝ E) {k' : Set (quotient L)}
    (hk' : IsConvexPart k') : IsConvexPart (quotientPreimage L k') := by
  unfold IsConvexPart quotientPreimage
  rw [insert_zero_F_ofCone (isPosCone_preimage _ (isPosCone_insert_zero (isPosCone_F k')))]
  have : insert (0 : E) (L.mkQ ⁻¹' insert 0 (F k')) = L.mkQ ⁻¹' insert 0 (F k') := by
    apply insert_eq_of_mem; simp
  rw [this]
  exact hk'.linear_preimage L.mkQ

theorem isConvexPart_quotientImage (L : Submodule ℝ E) {k : Set (Sphere E)}
    (hk : IsConvexPart k) : IsConvexPart (quotientImage L k) := by
  unfold IsConvexPart quotientImage
  rw [insert_zero_F_ofCone (isPosCone_image _ (isPosCone_F k))]
  have : insert (0 : E ⧸ L) (L.mkQ '' F k) = L.mkQ '' insert 0 (F k) := by
    rw [image_insert_eq, map_zero]
  rw [this]
  exact hk.linear_image L.mkQ

theorem quotientImage_quotientPreimage (L : Submodule ℝ E) (k' : Set (quotient L)) :
    quotientImage L (quotientPreimage L k') = k' := by
  conv_rhs => rw [← ofCone_F k']
  unfold quotientImage quotientPreimage
  rw [ofCone_eq_ofCone_iff (isPosCone_image _ (isPosCone_F _)) (isPosCone_F k'),
    F_ofCone (isPosCone_preimage _ (isPosCone_insert_zero (isPosCone_F k')))]
  ext w
  simp only [mem_sdiff, mem_image, mem_preimage, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨v, ⟨h | h, -⟩, rfl⟩, hw⟩
    · exact absurd h hw
    · exact ⟨h, hw⟩
  · rintro ⟨hw, hw0⟩
    obtain ⟨v, rfl⟩ := L.mkQ_surjective w
    refine ⟨⟨v, ⟨Or.inr hw, fun h => hw0 (by simp [h])⟩, rfl⟩, hw0⟩

/-- A convex part containing `l`: its cone `F(k) ∪ {O}` is `L`-saturated. -/
theorem add_mem_F_of_isConvexPart {L : Submodule ℝ E} {k : Set (Sphere E)} (hk : IsConvexPart k)
    (hl : linearSubvariety L ⊆ k) {u m : E} (hu : u ∈ F k) (hm : m ∈ L) (hum : u + m ≠ 0) :
    u + m ∈ F k := by
  by_cases hm0 : m = 0
  · simpa [hm0] using hu
  have hmF : m ∈ F k := F_mono hl (by rw [F_linearSubvariety]; exact ⟨hm, hm0⟩)
  have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • m ∈ insert 0 (F k) :=
    hk (mem_insert_of_mem _ hu) (mem_insert_of_mem _ hmF) (by norm_num) (by norm_num)
      (by norm_num)
  have hne : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • m ≠ 0 := by
    rw [← smul_add]; exact smul_ne_zero (by norm_num) hum
  have := smul_mem_F ((mem_insert_iff.1 hmid).resolve_left hne) (two_pos (α := ℝ))
  rwa [← smul_add, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] at this

theorem quotientPreimage_quotientImage {L : Submodule ℝ E} {k : Set (Sphere E)}
    (hk : IsConvexPart k) (hl : linearSubvariety L ⊆ k) :
    quotientPreimage L (quotientImage L k) = k := by
  conv_rhs => rw [← ofCone_F k]
  unfold quotientImage quotientPreimage
  rw [ofCone_eq_ofCone_iff (isPosCone_preimage _ (isPosCone_insert_zero (isPosCone_F _)))
    (isPosCone_F k), F_ofCone (isPosCone_image _ (isPosCone_F k))]
  ext v
  simp only [mem_sdiff, mem_preimage, mem_insert_iff, mem_image, mem_singleton_iff]
  constructor
  · rintro ⟨h | ⟨⟨u, hu, huv⟩, -⟩, hv⟩
    · -- `v ∈ L - {O}`
      refine ⟨F_mono hl ?_, hv⟩
      rw [F_linearSubvariety]
      exact ⟨(Submodule.Quotient.mk_eq_zero L).1 h, hv⟩
    · -- `v = u + (v - u)` with `v - u ∈ L`
      have hm : v - u ∈ L := by
        rw [← Submodule.Quotient.eq]; exact huv.symm
      have := add_mem_F_of_isConvexPart hk hl hu hm (by simpa using hv)
      exact ⟨by simpa using this, hv⟩
  · rintro ⟨hv, hv0⟩
    refine ⟨?_, hv0⟩
    by_cases hq : L.mkQ v = 0
    · exact Or.inl hq
    · exact Or.inr ⟨⟨v, hv, rfl⟩, hq⟩

theorem quotientImage_mono (L : Submodule ℝ E) {k₁ k₂ : Set (Sphere E)} (h : k₁ ⊆ k₂) :
    quotientImage L k₁ ⊆ quotientImage L k₂ :=
  ofCone_subset_ofCone (image_mono (F_mono h))

theorem quotientPreimage_mono (L : Submodule ℝ E) {k₁ k₂ : Set (quotient L)} (h : k₁ ⊆ k₂) :
    quotientPreimage L k₁ ⊆ quotientPreimage L k₂ :=
  ofCone_subset_ofCone (preimage_mono (insert_subset_insert (F_mono h)))

/-- **Déf. 10 — the convex parts of `S(E)` containing `l` are identified with the convex parts of
`S(E)/l`** (« les convexes de $S(E)$ contenant $l$ s'identifient aux convexes de $S(E)/l$ »): an
order isomorphism `k ↦ s(q(F(k)) - {O})`, with inverse `k' ↦ s(q⁻¹(F(k') ∪ {O}) - {O})`, for every
real vector space `E` and subspace `L`. (Convexity in the reading `F(k) ∪ {O}` of Déf. 8, ruled by
DEC-120 on OQ-24.) -/
def convexQuotientEquiv (L : Submodule ℝ E) :
    {k : Set (Sphere E) // IsConvexPart k ∧ linearSubvariety L ⊆ k} ≃o
      {k' : Set (quotient L) // IsConvexPart k'} :=
  Equiv.toOrderIso
    { toFun := fun k => ⟨quotientImage L k.1, isConvexPart_quotientImage L k.2.1⟩
      invFun := fun k' => ⟨quotientPreimage L k'.1, isConvexPart_quotientPreimage L k'.2,
        linearSubvariety_subset_quotientPreimage L k'.1⟩
      left_inv := fun k => Subtype.ext (quotientPreimage_quotientImage k.2.1 k.2.2)
      right_inv := fun k' => Subtype.ext (quotientImage_quotientPreimage L k'.1) }
    (fun _ _ h => quotientImage_mono L h) (fun _ _ h => quotientPreimage_mono L h)

@[simp] theorem convexQuotientEquiv_apply (L : Submodule ℝ E)
    (k : {k : Set (Sphere E) // IsConvexPart k ∧ linearSubvariety L ⊆ k}) :
    (convexQuotientEquiv L k : Set (quotient L)) = quotientImage L k := rfl

/-! #### The « De même que » analogy of Déf. 10 (reading of DEC-114) -/

/-- **The « De même que » analogy of Déf. 10, in the reading of DEC-114**: « les convexes de $E$
contenant $L$ s'identifient aux convexes de $E/L$ », read for the `L`-saturated convex sets of `E`
(`C + L ⊆ C`: the open, the closed, the conical ones), which correspond to the convex sets of
`E/L` by `C ↦ q(C)` and `D ↦ q⁻¹(D)`. -/
def convexSaturatedEquiv (L : Submodule ℝ E) :
    {C : Set E // Convex ℝ C ∧ ∀ v ∈ C, ∀ m ∈ L, v + m ∈ C} ≃ {D : Set (E ⧸ L) // Convex ℝ D} where
  toFun C := ⟨L.mkQ '' C.1, C.2.1.linear_image _⟩
  invFun D := ⟨L.mkQ ⁻¹' D.1, D.2.linear_preimage _, fun v hv m hm => by
    simpa [(Submodule.Quotient.mk_eq_zero L).2 hm] using hv⟩
  left_inv C := by
    apply Subtype.ext
    apply Subset.antisymm
    · rintro v ⟨u, hu, huv⟩
      have hm : v - u ∈ L := by rw [← Submodule.Quotient.eq]; exact huv.symm
      simpa using C.2.2 u hu _ hm
    · exact subset_preimage_image _ _
  right_inv D := Subtype.ext (image_preimage_eq _ L.mkQ_surjective)

/-- **Remark on the literal analogy (Déf. 10, l.265)**, why DEC-114 reads it for `L`-saturated sets:
for arbitrary convex sets « les convexes de $E$ contenant $L$ s'identifient aux convexes de $E/L$ »
fails — in `ℝ²` with `L = {x = 0}`, the strip `0 ≤ x ≤ 1` and the strip with the line `x = 1`
reduced to `(1, 0)` are distinct convex sets containing `L` with the same image in `E/L`. The
statement about `S(E)` is unaffected (`convexQuotientEquiv`). -/
theorem not_injective_convex_image_quotient :
    ∃ (L : Submodule ℝ (ℝ × ℝ)) (C₁ C₂ : Set (ℝ × ℝ)), Convex ℝ C₁ ∧ Convex ℝ C₂ ∧
      (L : Set (ℝ × ℝ)) ⊆ C₁ ∧ (L : Set (ℝ × ℝ)) ⊆ C₂ ∧ L.mkQ '' C₁ = L.mkQ '' C₂ ∧ C₁ ≠ C₂ := by
  let L : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)
  have hL : ∀ p : ℝ × ℝ, p ∈ L ↔ p.1 = 0 := fun p => by simp [L]
  let C₁ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1}
  let C₂ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ (p.1 = 1 → p.2 = 0)}
  refine ⟨L, C₁, C₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb s t hs ht hst
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    simp only [C₁, mem_setOf_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    constructor
    · nlinarith [mul_nonneg hs ha0, mul_nonneg ht hb0]
    · nlinarith [mul_nonneg hs (sub_nonneg.2 ha1), mul_nonneg ht (sub_nonneg.2 hb1)]
  · intro a ha b hb s t hs ht hst
    obtain ⟨ha0, ha1, ha2⟩ := ha
    obtain ⟨hb0, hb1, hb2⟩ := hb
    simp only [C₂, mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul]
    refine ⟨by nlinarith [mul_nonneg hs ha0, mul_nonneg ht hb0],
      by nlinarith [mul_nonneg hs (sub_nonneg.2 ha1), mul_nonneg ht (sub_nonneg.2 hb1)],
      fun h1 => ?_⟩
    have p1 := mul_nonneg hs (sub_nonneg.2 ha1)
    have p2 := mul_nonneg ht (sub_nonneg.2 hb1)
    have e1 : s * (1 - a.1) = 0 := by nlinarith
    have e2 : t * (1 - b.1) = 0 := by nlinarith
    have f1 : s * a.2 = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · rw [h, zero_mul]
      · rw [ha2 (by linarith), mul_zero]
    have f2 : t * b.2 = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · rw [h, zero_mul]
      · rw [hb2 (by linarith), mul_zero]
    linarith
  · intro p hp
    rw [SetLike.mem_coe, hL] at hp
    simp [C₁, hp]
  · intro p hp
    rw [SetLike.mem_coe, hL] at hp
    simp [C₂, hp]
  · apply Subset.antisymm
    · rintro _ ⟨p, ⟨hp0, hp1⟩, rfl⟩
      refine ⟨(p.1, 0), ⟨hp0, hp1, fun _ => rfl⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hL]
      simp
    · rintro _ ⟨p, ⟨hp0, hp1, -⟩, rfl⟩
      exact ⟨p, ⟨hp0, hp1⟩, rfl⟩
  · intro h
    have : ((1 : ℝ), (1 : ℝ)) ∈ C₂ := h ▸ (show ((1 : ℝ), (1 : ℝ)) ∈ C₁ by simp [C₁])
    simp [C₂] at this

end Sphere

end Benzecri
