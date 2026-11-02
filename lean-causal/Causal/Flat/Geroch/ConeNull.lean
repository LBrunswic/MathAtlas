import Causal.Minkowski
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# `Causal.Flat.Geroch.ConeNull` — the frontier of a locally past-closed set is Lebesgue-null

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257);
infrastructure for `FlatAdmissibleMeasures` (`Flat/TheoremBInputs.lean`, ruling DEC-65). **No label
is marked**: this file is a fact of measure theory on `𝐌ⁿ = ℝ × ℝᵈ` (`Minkowski d`), used by the
integrator `Causal.Flat.GerochFlat` to prove property 4. of `defi:mesure_dieckmann`
(ETT.tex:1032) on every GH flat spacetime.

> 4. for every $A \subset M$, $\mu(J^-(A)\setminus K^-(A))=0$ (resp. $\mu(J^+(A)\setminus K^+(A))=0$).
> (ETT.tex, `defi:mesure_dieckmann`)

* `volume_frontier_inter_null_of_pastCone`: if `B` is open and `P` is **past-closed inside `B`**
  (`y ∈ P ∩ B`, `z ∈ B`, `‖y.2 − z.2‖ < y.1 − z.1` ⇒ `z ∈ P`), then `frontier P ∩ B` is
  Lebesgue-null.
* `volume_frontier_inter_null_of_futureCone`: the future version (`‖z.2 − y.2‖ < z.1 − y.1`).
* Helpers: `volume_eq_zero_of_section_subsingleton` (Fubini–Tonelli step) and
  `frontier_inter_section_subsingleton_of_pastCone` / `…_of_futureCone` (the section argument).

Route (no Lipschitz graph needed): for a fixed space point `x`, the vertical section
`{t | (t, x) ∈ frontier P ∩ B}` has at most one point — if `t < s` are both in it, `(s, x)` is a
limit of points `y ∈ P ∩ B`, one of them with `‖y.2 − x‖ < y.1 − t`, and then the open set
`B ∩ {z | ‖y.2 − z.2‖ < y.1 − z.1}` contains `(t, x)` and lies in `P`, so `(t, x) ∈ interior P`,
against `(t, x) ∈ frontier P`. A subsingleton of `ℝ` is null, and `frontier P ∩ B` is measurable
(closed ∩ open), so `Measure.prod_apply_symm` (Fubini–Tonelli on `volume = volume.prod volume`)
gives `0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (Hawking–Ellis 6.3.1: an achronal boundary is a Lipschitz hypersurface, hence null) | ⚠ replaced: only the vertical sections are used; the statement is local to an open `B` |
| `μ` absolutely continuous w.r.t. Lebesgue | ✓ carried: the statement is for `volume` itself |

## SCOPE (disclosed)

* Stated for an arbitrary open `B` (no convexity): the cone condition is the explicit inequality,
  not the causality of `B`; convexity is the integrator's business (`Form.lt_iff_of_convex`).
* True for every `d`, `d = 0` included (`EuclideanSpace ℝ (Fin 0)` is a point, `volume` its Dirac
  mass); `P = ∅` and `P = univ` give an empty frontier.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-65.
-/

namespace Causal.Flat

open Set MeasureTheory

variable {d : ℕ}

/-- **A measurable set with subsingleton vertical sections is Lebesgue-null**: if `S` is
measurable and every vertical section `{t | (t, x) ∈ S}` has at most one point, then
`volume S = 0` (Fubini–Tonelli on `volume = volume.prod volume`, a point of `ℝ` being null). -/
theorem volume_eq_zero_of_section_subsingleton {S : Set (Minkowski d)} (hS : MeasurableSet S)
    (hsec : ∀ x : EuclideanSpace ℝ (Fin d), {t : ℝ | (t, x) ∈ S}.Subsingleton) :
    volume S = 0 := by
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  have : ∀ x : EuclideanSpace ℝ (Fin d),
      (volume : Measure ℝ) ((fun t : ℝ => (t, x)) ⁻¹' S) = 0 := fun x => (hsec x).measure_zero _
  simp only [this, lintegral_zero]

/-- **Past cone: two points of one vertical section of `frontier P ∩ B` are impossible**: if
`t < s` and `(t, x)`, `(s, x)` both lie in `frontier P ∩ B`, then `(t, x) ∈ interior P`. -/
theorem frontier_inter_section_subsingleton_of_pastCone {B P : Set (Minkowski d)}
    (hB : IsOpen B) (hP : ∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖y.2 - z.2‖ < y.1 - z.1 → z ∈ P)
    (x : EuclideanSpace ℝ (Fin d)) : {t : ℝ | (t, x) ∈ frontier P ∩ B}.Subsingleton := by
  have key : ∀ t s : ℝ, t < s → (t, x) ∈ frontier P ∩ B → (s, x) ∈ frontier P ∩ B → False := by
    intro t s hts ht hs
    have hU : IsOpen {y : Minkowski d | y ∈ B ∧ ‖y.2 - x‖ < y.1 - t} :=
      hB.inter (isOpen_lt (f := fun y : Minkowski d => ‖y.2 - x‖) (g := fun y => y.1 - t)
        (by fun_prop) (by fun_prop))
    have hsU : ((s, x) : Minkowski d) ∈ {y : Minkowski d | y ∈ B ∧ ‖y.2 - x‖ < y.1 - t} :=
      ⟨hs.2, by simpa using hts⟩
    obtain ⟨y, ⟨hyB, hyt⟩, hyP⟩ := mem_closure_iff.1 (frontier_subset_closure hs.1) _ hU hsU
    have hO : IsOpen (B ∩ {z : Minkowski d | ‖y.2 - z.2‖ < y.1 - z.1}) :=
      hB.inter (isOpen_lt (by fun_prop) (by fun_prop))
    have hOP : B ∩ {z : Minkowski d | ‖y.2 - z.2‖ < y.1 - z.1} ⊆ P :=
      fun z hz => hP y hyP hyB z hz.1 hz.2
    have htO : ((t, x) : Minkowski d) ∈ B ∩ {z : Minkowski d | ‖y.2 - z.2‖ < y.1 - z.1} :=
      ⟨ht.2, hyt⟩
    exact ht.1.2 (interior_maximal hOP hO htO)
  intro t ht s hs
  rcases lt_trichotomy t s with h | h | h
  · exact (key t s h ht hs).elim
  · exact h
  · exact (key s t h hs ht).elim

/-- **Future cone: two points of one vertical section of `frontier P ∩ B` are impossible**: if
`t < s` and `(t, x)`, `(s, x)` both lie in `frontier P ∩ B`, then `(s, x) ∈ interior P`. -/
theorem frontier_inter_section_subsingleton_of_futureCone {B P : Set (Minkowski d)}
    (hB : IsOpen B) (hP : ∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖z.2 - y.2‖ < z.1 - y.1 → z ∈ P)
    (x : EuclideanSpace ℝ (Fin d)) : {t : ℝ | (t, x) ∈ frontier P ∩ B}.Subsingleton := by
  have key : ∀ t s : ℝ, t < s → (t, x) ∈ frontier P ∩ B → (s, x) ∈ frontier P ∩ B → False := by
    intro t s hts ht hs
    have hU : IsOpen {y : Minkowski d | y ∈ B ∧ ‖x - y.2‖ < s - y.1} :=
      hB.inter (isOpen_lt (f := fun y : Minkowski d => ‖x - y.2‖) (g := fun y => s - y.1)
        (by fun_prop) (by fun_prop))
    have htU : ((t, x) : Minkowski d) ∈ {y : Minkowski d | y ∈ B ∧ ‖x - y.2‖ < s - y.1} :=
      ⟨ht.2, by simpa using hts⟩
    obtain ⟨y, ⟨hyB, hys⟩, hyP⟩ := mem_closure_iff.1 (frontier_subset_closure ht.1) _ hU htU
    have hO : IsOpen (B ∩ {z : Minkowski d | ‖z.2 - y.2‖ < z.1 - y.1}) :=
      hB.inter (isOpen_lt (by fun_prop) (by fun_prop))
    have hOP : B ∩ {z : Minkowski d | ‖z.2 - y.2‖ < z.1 - y.1} ⊆ P :=
      fun z hz => hP y hyP hyB z hz.1 hz.2
    have hsO : ((s, x) : Minkowski d) ∈ B ∩ {z : Minkowski d | ‖z.2 - y.2‖ < z.1 - y.1} :=
      ⟨hs.2, hys⟩
    exact hs.1.2 (interior_maximal hOP hO hsO)
  intro t ht s hs
  rcases lt_trichotomy t s with h | h | h
  · exact (key t s h ht hs).elim
  · exact h
  · exact (key s t h hs ht).elim

/-- **The frontier of a set past-closed inside an open set `B` is Lebesgue-null inside `B`**:
`y ∈ P ∩ B`, `z ∈ B` and `‖y.2 − z.2‖ < y.1 − z.1` (`z ≪ y` in `𝐌ⁿ`) imply `z ∈ P`. -/
theorem volume_frontier_inter_null_of_pastCone {B P : Set (Minkowski d)} (hB : IsOpen B)
    (hP : ∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖y.2 - z.2‖ < y.1 - z.1 → z ∈ P) :
    volume (frontier P ∩ B) = 0 :=
  volume_eq_zero_of_section_subsingleton (isClosed_frontier.measurableSet.inter hB.measurableSet)
    (frontier_inter_section_subsingleton_of_pastCone hB hP)

/-- **The frontier of a set future-closed inside an open set `B` is Lebesgue-null inside `B`**:
`y ∈ P ∩ B`, `z ∈ B` and `‖z.2 − y.2‖ < z.1 − y.1` (`y ≪ z` in `𝐌ⁿ`) imply `z ∈ P`. -/
theorem volume_frontier_inter_null_of_futureCone {B P : Set (Minkowski d)} (hB : IsOpen B)
    (hP : ∀ y ∈ P, y ∈ B → ∀ z ∈ B, ‖z.2 - y.2‖ < z.1 - y.1 → z ∈ P) :
    volume (frontier P ∩ B) = 0 :=
  volume_eq_zero_of_section_subsingleton (isClosed_frontier.measurableSet.inter hB.measurableSet)
    (frontier_inter_section_subsingleton_of_futureCone hB hP)

end Causal.Flat
