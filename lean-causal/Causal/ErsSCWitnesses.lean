import Causal.Ers464SecondCountable
import Causal.Ers464WithoutArc
import Causal.ErsSecondCountable
import Causal.ErsMughd
import Causal.InextensibleNestedBasics
import Causal.CBG.CausalConvex
import Causal.CExtConnexeCauchy.Basic
import Causal.ErsWitnesses

/-!
# Non-vacuity witnesses for the second countable ERS union lemmas and Theorems 4.79, 4.80

Programme target `T-abs-ers-sc-witnesses` (`programme/roadmap.toml`; layer 1: ETT-layer imports
only, no model, no metric notion). Witnesses only (kb/0011): each `timelikeLine_…` theorem below inhabits
every hypothesis of one second countable form on the timelike line and states the form's
conclusion on that data (the other declarations are its helpers). **No label is marked**: the forms are unmarked in their own modules, and a witness
certifies no statement of the paper. The forms belong to these rows of Eperon–Reall–Sbierski,
arXiv 1802.03020 (`papers/ers-predictability/legacy/labeled/ghd_02_19.tex`):

* `ersprop:PropLocUniqueness` — `ghd_02_19.tex:836`: the union lemmas of
  `Causal.Ers464SecondCountable` §1, `eq_of_mem_of_t1_secondCountable`,
  `IsCauchySurfaceOn.of_subset_of_t1_secondCountable`, `isCauchySurfaceOn_sSup_of_secondCountable`,
  `globallyHyperbolicOn_sSup_of_pieces_secondCountable`; witnesses in §2.
* `ersthm:ThmMUGHD` — `ghd_02_19.tex:1055`: `ers_theorem_4_79_secondCountable`.
* `ersthm:consider_subluminal_quasilinear_wave` — `ghd_02_19.tex:1066`:
  `ers_theorem_4_80_secondCountable`.
* "any m-GHD is a UGHD" — `ghd_02_19.tex:1053`: `IsMDevelopment.isUniqueDevelopment_secondCountable`
  and, beyond the target's list, its `_noArc` form (`Causal.Ers464WithoutArc`, which records it
  as having no witness); witnesses in §3.

> We now set V = ⋃_{p∈S} DS_p. It is immediate that u1 and u2 agree on this set and that V is
> globally hyperbolic with Cauchy hypersurface S. (`ghd_02_19.tex:843`)

> We note that any m-GHD is a UGHD by Corollary 4.73. […] Given initial data on a connected
> hypersurface S that is acausal with respect to the Minkowski metric there exists a UGHD
> u : U → R with the property that the domain of any other UGHD is contained in U.
> (`:1053, 1057`) […] there exists a unique m-MGHD, i.e., a m-GHD u_max : U_max → R with the
> property that for any other m-GHD u : U → R of the same initial data we have U ⊆ U_max and
> u_max|_U = u. (`:1068`)

## Hypothesis checklist

Against the forms, not the paper (the forms' checklists stand for the paper).

| form's hypothesis | witnessed by |
|---|---|
| union lemmas: `B`, `S` Cauchy in `B` | `B = ]-1, 1[ ∪ ]2, 4[` (`twoIntervals`), `S = {0, 3}`: two points, `B` disconnected (`isCauchySurfaceOn_twoIntervals`, by `isCauchySurfaceOn_sSup_of_isAcausalOn`) |
| `hanti`, `hG`, `hC` on `B` | the timelike line's `≤_B` goes up; `timelikeLine_globallyHyperbolicOn B`; `timelikeLine_causallyArcConnected` |
| `𝒟 ≤ B`, each `D ∈ 𝒟` with a Cauchy `S' ⊆ S`, `S ⊆ ⋃ 𝒟` | `pieces`: the intervals `]a - r, a + r[`, `a ∈ {0, 3}`, `0 < r < 1/2`, Cauchy surface `{a}`; infinitely many, and `⋃ 𝒟 ∉ 𝒟` |
| `eq_of_mem`: a causal curve meeting `S` at two parameters | the constant curve `0` over `[0, 1]`, `s = 0 ≠ t = 1`; the conclusion is also stated for every causal curve of every `W ≤ B` |
| `of_subset`: `S' ⊊ S` Cauchy in `W ≤ B` | `W = ]-1, 1[`, `S' = {0}`; and `W = ]2, 4[`, `S' = {3}` |
| 4.79, 4.80, the m-GHD: `sol`, `cau`, `Cm`, `S` | `sol U u := u = id on U` (`idSol`), for **every** open `U`; `cau u` and `Cm` the timelike line; `S = {0}` |
| `hsub`, `harc`, `hinext` | `LeNested.refl`; `timelikeLine_causallyArcConnected`; `InextensibleNestedOn.refl` |
| `hex`, `hDm` | `(ℝ, id)`; `W = U` |
| `hG`, `hT`, `hK` on each m-development | on every open set of the line |
| `hloc`, `hglue`, `hfollow`, `hm`, `hmacausal`, `hS` (4.79, 4.80, the m-GHD) | proved in `ErsSCWitness.mughdData`, whose statement is exactly the forms' 17 hypotheses |
| `hlocal`, `hstay`, `hstep` for each pair | `U₁ ∩ U₂` (`isCommonDevelopment_inf`, kb/0245's `isCauchySurfaceOn_inf_of_secondCountable`); a development is preconnected (`isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable`) |

## SCOPE (disclosed)

* **Witnesses only**: no form is added or changed.
* **Non-trivial where cheap.** The union family is infinite and its union is not a member, `S`
  has two points and `B` is disconnected, so `eq_of_mem` and `of_subset` are not instances of a
  singleton. For 4.79/4.80 the development domains are not one (`ℝ` and `]-1, 1[` both are, with
  `id` and the clamp), unlike `timelikeLine_ers_theorem_4_79_4_80`. The m-GHD witness has
  `U₁ = ]-1, 1[`, `u₁` the clamp. The conclusion of `eq_of_mem` on its inhabitant is `0 = 0`:
  any inhabitant has `c s = c t`, which is the lemma.
* **One causality.** `cau u` and `Cm` are the timelike line for every `u`: no witness separates
  the PDE's causality from Minkowski's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

namespace ErsSCWitness

open Causality

/-! ## 1. The timelike line on its open sets -/

/-- On the timelike line, `{a}` is a Cauchy surface of `]a - r, a + r[` (`r > 0`): the range of
`x ↦ a + c·arctan x`, `c = r/(π/2)` (`timelikeLine_isCauchySurfaceOn_range`). -/
theorem isCauchySurfaceOn_Ioo_center {a r : ℝ} (hr : 0 < r) {U : Opens ℝ}
    (hU : (U : Set ℝ) = Ioo (a - r) (a + r)) : timelikeLine.IsCauchySurfaceOn U {a} := by
  have hπ : 0 < Real.pi / 2 := by positivity
  set c := r / (Real.pi / 2) with hc_def
  have hc : 0 < c := div_pos hr hπ
  have harctan : IsOpenMap Real.arctan :=
    isOpen_Ioo.isOpenMap_subtype_val.comp Real.tanOrderIso.symm.toHomeomorph.isOpenMap
  have hgo : IsOpenMap (fun x => a + c * Real.arctan x) :=
    (Homeomorph.addLeft a).isOpenMap.comp
      ((Homeomorph.mulLeft₀ c hc.ne').isOpenMap.comp harctan)
  have hrange : range (fun x => a + c * Real.arctan x) = Ioo (a - r) (a + r) := by
    rw [range_comp' (fun y => a + y) (fun x => c * Real.arctan x),
      range_comp' (c * ·) Real.arctan, Real.range_arctan, image_mul_left_Ioo hc,
      image_const_add_Ioo]
    have : c * (Real.pi / 2) = r := by rw [hc_def]; field_simp
    rw [mul_neg, this, sub_eq_add_neg]
  have h := timelikeLine_isCauchySurfaceOn_range (g := fun x => a + c * Real.arctan x)
    ((Real.arctan_strictMono.const_mul hc).const_add a)
    (continuous_const.add (continuous_const.mul Real.continuous_arctan)) hgo
    (hU.trans hrange.symm)
  simpa [Real.arctan_zero] using h

/-- The timelike line is tarentin on every open set: `Causal.timelikeLine_tarentinOn`
(`Causal.ErsWitnesses`), cited here rather than proved twice (kb/0248). -/
theorem tarentinOn (U : Opens ℝ) : timelikeLine.TarentinOn U := timelikeLine_tarentinOn U

/-! ## 2. The union lemmas: `B = ]-1, 1[ ∪ ]2, 4[`, `S = {0, 3}` -/

/-- The ambient open set of the union witnesses: two disjoint intervals. -/
def twoIntervals : Opens ℝ := ⟨Ioo (-1) 1 ∪ Ioo 2 4, isOpen_Ioo.union isOpen_Ioo⟩

/-- The second component of `twoIntervals` (the first is `ersWitnessIoo`). -/
def ioo24 : Opens ℝ := ⟨Ioo 2 4, isOpen_Ioo⟩

/-- The pieces: every interval `]a - r, a + r[` with `a ∈ {0, 3}` and `0 < r < 1/2`. -/
def pieces : Set (Opens ℝ) :=
  {D | ∃ a ∈ ({0, 3} : Set ℝ), ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ (D : Set ℝ) = Ioo (a - r) (a + r)}

/-- `≤` of the timelike line in `twoIntervals` is antisymmetric (it goes up). -/
theorem antisymm_twoIntervals :
    ∀ ⦃x y : ℝ⦄, timelikeLine.le twoIntervals x y → timelikeLine.le twoIntervals y x → x = y :=
  fun _ _ h₁ h₂ => le_antisymm h₁.1 h₂.1

/-- `{0, 3}` is acausal in `twoIntervals`: `[0, 3]` leaves it at `3/2`. -/
theorem isAcausalOn_twoIntervals : timelikeLine.IsAcausalOn twoIntervals ({0, 3} : Set ℝ) := by
  rintro x (rfl | rfl) y (rfl | rfl) h
  · rfl
  · exfalso
    have h' : (3 / 2 : ℝ) ∈ Ioo (-1) 1 ∪ Ioo 2 4 :=
      h.2 ⟨by norm_num, by norm_num⟩
    rcases h' with h' | h'
    · linarith [h'.2]
    · linarith [h'.1]
  · exfalso; linarith [h.1]
  · rfl

/-- `{0, 3}` is a Cauchy surface of `]-1, 1[ ∪ ]2, 4[`: `{0}` of the first component, `{3}` of
the second, joined by `isCauchySurfaceOn_sSup_of_isAcausalOn` with `twoIntervals` as ambient. -/
theorem isCauchySurfaceOn_twoIntervals :
    timelikeLine.IsCauchySurfaceOn twoIntervals ({0, 3} : Set ℝ) := by
  have heq : sSup ({ersWitnessIoo, ioo24} : Set (Opens ℝ)) = twoIntervals := by
    rw [sSup_pair]
    ext x
    simp [twoIntervals, ersWitnessIoo, ioo24]
  have h := isCauchySurfaceOn_sSup_of_isAcausalOn (C := timelikeLine) (B := twoIntervals)
    (𝒟 := {ersWitnessIoo, ioo24}) (S := {0, 3}) antisymm_twoIntervals isAcausalOn_twoIntervals
    ?_ ?_
  · rwa [heq] at h
  · rintro D (rfl | rfl) x hx
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro D (rfl | rfl)
    · exact ⟨{0}, by simp, timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl⟩
    · exact ⟨{3}, by simp, isCauchySurfaceOn_Ioo_center one_pos
        (show Ioo (2 : ℝ) 4 = Ioo (3 - 1) (3 + 1) by norm_num)⟩

/-- Every piece lies in `twoIntervals`. -/
theorem pieces_le : ∀ D ∈ pieces, D ≤ twoIntervals := by
  rintro D ⟨a, ha, r, hr, hr2, hD⟩ x hx
  rw [← SetLike.mem_coe, hD] at hx
  obtain ⟨h1, h2⟩ := hx
  rcases ha with rfl | rfl
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

/-- The piece `]a - r, a + r[` has the Cauchy surface `{a} ⊆ {0, 3}`. -/
theorem pieces_cauchy :
    ∀ D ∈ pieces, ∃ S' ⊆ ({0, 3} : Set ℝ), timelikeLine.IsCauchySurfaceOn D S' := by
  rintro D ⟨a, ha, r, hr, -, hD⟩
  exact ⟨{a}, singleton_subset_iff.2 ha, isCauchySurfaceOn_Ioo_center hr hD⟩

/-- `0` and `3` lie in the union of the pieces (in `]-1/4, 1/4[` and `]11/4, 13/4[`). -/
theorem subset_sSup_pieces : ({0, 3} : Set ℝ) ⊆ (sSup pieces : Opens ℝ) := by
  rintro x (rfl | rfl)
  · refine Opens.mem_sSup.2 ⟨⟨Ioo (0 - 1 / 4) (0 + 1 / 4), isOpen_Ioo⟩,
      ⟨0, Or.inl rfl, 1 / 4, by norm_num, by norm_num, rfl⟩, ?_⟩
    show (0 : ℝ) ∈ Ioo (0 - 1 / 4) (0 + 1 / 4)
    constructor <;> norm_num
  · refine Opens.mem_sSup.2 ⟨⟨Ioo (3 - 1 / 4) (3 + 1 / 4), isOpen_Ioo⟩,
      ⟨3, Or.inr rfl, 1 / 4, by norm_num, by norm_num, rfl⟩, ?_⟩
    show (3 : ℝ) ∈ Ioo (3 - 1 / 4) (3 + 1 / 4)
    constructor <;> norm_num

/-- The union of the pieces is not a piece: it contains `0` and `3`, no piece contains both. -/
theorem sSup_pieces_notMem : sSup pieces ∉ pieces := by
  rintro ⟨a, ha, r, hr, hr2, hD⟩
  have h0 : (0 : ℝ) ∈ ((sSup pieces : Opens ℝ) : Set ℝ) := subset_sSup_pieces (Or.inl rfl)
  have h3 : (3 : ℝ) ∈ ((sSup pieces : Opens ℝ) : Set ℝ) := subset_sSup_pieces (Or.inr rfl)
  rw [hD] at h0 h3
  rcases ha with rfl | rfl
  · linarith [h3.2]
  · linarith [h0.1]

end ErsSCWitness

open ErsSCWitness Causality

/-- **Witness for `eq_of_mem_of_t1_secondCountable`**: `S = {0, 3}` Cauchy in
`B = ]-1, 1[ ∪ ]2, 4[`; the constant curve `0` over `[0, 1]` meets `S` at the parameters `0 ≠ 1`;
and for every causal curve of every `W ≤ B`, two parameters at which it meets `S` have one image
point. -/
theorem timelikeLine_eq_of_mem_of_t1_secondCountable :
    timelikeLine.IsCauchySurfaceOn twoIntervals ({0, 3} : Set ℝ) ∧
      (∃ (I : Set ℝ) (c : ℝ → ℝ) (s t : ℝ), timelikeLine.CausalCurveIn twoIntervals I c ∧
        s ∈ I ∧ t ∈ I ∧ s ≠ t ∧ c s ∈ ({0, 3} : Set ℝ) ∧ c t ∈ ({0, 3} : Set ℝ) ∧ c s = c t) ∧
      ∀ W ≤ twoIntervals, ∀ (I : Set ℝ) (c : ℝ → ℝ), timelikeLine.CausalCurveIn W I c →
        ∀ s ∈ I, ∀ t ∈ I, c s ∈ ({0, 3} : Set ℝ) → c t ∈ ({0, 3} : Set ℝ) → c s = c t := by
  have hB := isCauchySurfaceOn_twoIntervals
  refine ⟨hB, ?_, fun W hW I c hc s hs t ht hsS htS =>
    eq_of_mem_of_t1_secondCountable hW hB hc hs ht hsS htS⟩
  have h0 : (0 : ℝ) ∈ twoIntervals := Or.inl ⟨by norm_num, by norm_num⟩
  have hc : timelikeLine.CausalCurveIn twoIntervals (Icc 0 1) (fun _ => (0 : ℝ)) :=
    ⟨⟨0, by norm_num, by norm_num⟩, ordConnected_Icc, fun _ _ _ _ => causalCurveOn_const h0⟩
  refine ⟨Icc 0 1, fun _ => 0, 0, 1, hc, ⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩,
    zero_ne_one, Or.inl rfl, Or.inl rfl, ?_⟩
  exact eq_of_mem_of_t1_secondCountable le_rfl hB hc ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ (Or.inl rfl) (Or.inl rfl)

/-- **Witness for `IsCauchySurfaceOn.of_subset_of_t1_secondCountable`**: in
`B = ]-1, 1[ ∪ ]2, 4[` with `S = {0, 3}` Cauchy, the pieces `{0}` of `]-1, 1[` and `{3}` of
`]2, 4[` are proper subsets of `S`, and `S` is a Cauchy surface of each component. -/
theorem timelikeLine_isCauchySurfaceOn_of_subset_of_t1_secondCountable :
    (timelikeLine.IsCauchySurfaceOn twoIntervals ({0, 3} : Set ℝ) ∧
      timelikeLine.IsCauchySurfaceOn ersWitnessIoo ({0} : Set ℝ) ∧
      ({0} : Set ℝ) ⊂ {0, 3} ∧ ersWitnessIoo ≤ twoIntervals ∧
      timelikeLine.IsCauchySurfaceOn ioo24 ({3} : Set ℝ) ∧
      ({3} : Set ℝ) ⊂ {0, 3} ∧ ioo24 ≤ twoIntervals) ∧
    timelikeLine.IsCauchySurfaceOn ersWitnessIoo ({0, 3} : Set ℝ) ∧
      timelikeLine.IsCauchySurfaceOn ioo24 ({0, 3} : Set ℝ) := by
  have hB := isCauchySurfaceOn_twoIntervals
  have h₁ : timelikeLine.IsCauchySurfaceOn ersWitnessIoo ({0} : Set ℝ) :=
    timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl
  have h₂ : timelikeLine.IsCauchySurfaceOn ioo24 ({3} : Set ℝ) :=
    isCauchySurfaceOn_Ioo_center one_pos (show Ioo (2 : ℝ) 4 = Ioo (3 - 1) (3 + 1) by norm_num)
  have hs₁ : ({0} : Set ℝ) ⊂ {0, 3} := by
    refine ssubset_iff_subset_ne.2 ⟨by simp, fun h => ?_⟩
    have : (3 : ℝ) ∈ ({0} : Set ℝ) := h ▸ (Or.inr rfl : (3 : ℝ) ∈ ({0, 3} : Set ℝ))
    norm_num at this
  have hs₂ : ({3} : Set ℝ) ⊂ {0, 3} := by
    refine ssubset_iff_subset_ne.2 ⟨by simp, fun h => ?_⟩
    have : (0 : ℝ) ∈ ({3} : Set ℝ) := h ▸ (Or.inl rfl : (0 : ℝ) ∈ ({0, 3} : Set ℝ))
    norm_num at this
  have hle₁ : ersWitnessIoo ≤ twoIntervals := fun x hx => Or.inl hx
  have hle₂ : ioo24 ≤ twoIntervals := fun x hx => Or.inr hx
  exact ⟨⟨hB, h₁, hs₁, hle₁, h₂, hs₂, hle₂⟩,
    h₁.of_subset_of_t1_secondCountable hs₁.subset hle₁ hB,
    h₂.of_subset_of_t1_secondCountable hs₂.subset hle₂ hB⟩

/-- **Witness for `isCauchySurfaceOn_sSup_of_secondCountable`**: `B = ]-1, 1[ ∪ ]2, 4[`,
`S = {0, 3}`, `𝒟` the intervals `]a - r, a + r[` (`a ∈ S`, `0 < r < 1/2`), whose union is not a
member; `S` is a Cauchy surface of `⋃ 𝒟`. -/
theorem timelikeLine_isCauchySurfaceOn_sSup_of_secondCountable :
    ((∀ ⦃x y : ℝ⦄, timelikeLine.le twoIntervals x y → timelikeLine.le twoIntervals y x → x = y) ∧
      timelikeLine.IsCauchySurfaceOn twoIntervals ({0, 3} : Set ℝ) ∧
      (∀ D ∈ pieces, D ≤ twoIntervals) ∧
      (∀ D ∈ pieces, ∃ S' ⊆ ({0, 3} : Set ℝ), timelikeLine.IsCauchySurfaceOn D S') ∧
      sSup pieces ∉ pieces) ∧
    timelikeLine.IsCauchySurfaceOn (sSup pieces) ({0, 3} : Set ℝ) := by
  exact ⟨⟨antisymm_twoIntervals, isCauchySurfaceOn_twoIntervals, pieces_le, pieces_cauchy,
      sSup_pieces_notMem⟩,
    isCauchySurfaceOn_sSup_of_secondCountable antisymm_twoIntervals isCauchySurfaceOn_twoIntervals
      pieces_le pieces_cauchy⟩

/-- **Witness for `globallyHyperbolicOn_sSup_of_pieces_secondCountable`**: the data of
`timelikeLine_isCauchySurfaceOn_sSup_of_secondCountable`, with `B` causally arc-connected and
globally hyperbolic and `S ⊆ ⋃ 𝒟`; `⋃ 𝒟` has `S` as Cauchy surface, is causally convex in `B`
and globally hyperbolic. -/
theorem timelikeLine_globallyHyperbolicOn_sSup_of_pieces_secondCountable :
    (timelikeLine.CausallyArcConnectedOn twoIntervals ∧
      timelikeLine.GloballyHyperbolicOn twoIntervals ∧
      timelikeLine.IsCauchySurfaceOn twoIntervals ({0, 3} : Set ℝ) ∧
      (∀ D ∈ pieces, D ≤ twoIntervals) ∧
      (∀ D ∈ pieces, ∃ S' ⊆ ({0, 3} : Set ℝ), timelikeLine.IsCauchySurfaceOn D S') ∧
      ({0, 3} : Set ℝ) ⊆ (sSup pieces : Opens ℝ) ∧ sSup pieces ∉ pieces) ∧
    timelikeLine.IsCauchySurfaceOn (sSup pieces) ({0, 3} : Set ℝ) ∧
      timelikeLine.CausallyConvexIn ((sSup pieces : Opens ℝ) : Set ℝ) twoIntervals ∧
      timelikeLine.GloballyHyperbolicOn (sSup pieces) := by
  have hC : timelikeLine.CausallyArcConnectedOn twoIntervals := fun V _ =>
    timelikeLine_causallyArcConnected V le_top
  have hG : timelikeLine.GloballyHyperbolicOn twoIntervals :=
    timelikeLine_globallyHyperbolicOn twoIntervals
  exact ⟨⟨hC, hG, isCauchySurfaceOn_twoIntervals, pieces_le, pieces_cauchy, subset_sSup_pieces,
      sSup_pieces_notMem⟩,
    globallyHyperbolicOn_sSup_of_pieces_secondCountable hC hG isCauchySurfaceOn_twoIntervals
      pieces_le pieces_cauchy subset_sSup_pieces⟩

/-! ## 3. Theorems 4.79, 4.80 and the m-GHD's uniqueness: the solutions `id` on every open set -/

namespace ErsSCWitness

/-- The initial value problem of the witness: `u` solves on `U` iff `u = id` on `U`, for every
open `U`. -/
def idSol : Opens ℝ → (ℝ → ℝ) → Prop := fun U u => EqOn u id U

/-- The clamp to `[-1, 1]`: a solution on `]-1, 1[`, where it is `id`; not on `ℝ`
(`clamp 2 = 1`). -/
def clamp : ℝ → ℝ := fun x => max (-1) (min x 1)

variable {U₁ U₂ : Opens ℝ} {u₁ u₂ : ℝ → ℝ}

/-- A development of `idSol` is preconnected: `{0}` is, and is Cauchy in it. -/
theorem isPreconnected_of_isDevelopment
    (h : IsDevelopment idSol (fun _ => timelikeLine) {0} U₁ u₁) :
    IsPreconnected (U₁ : Set ℝ) := by
  exact isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable isPreconnected_singleton
    h.subset h.cauchy

/-- Two developments of `idSol` have `U₁ ∩ U₂` as a common development (kb/0245). -/
theorem isCommonDevelopment_inf (h₁ : IsDevelopment idSol (fun _ => timelikeLine) {0} U₁ u₁)
    (h₂ : IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂) :
    timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) (U₁ ⊓ U₂) := by
  refine ⟨le_rfl, fun x hx => Opens.mem_inf.2 ⟨h₁.subset hx, h₂.subset hx⟩, fun x hx => ?_,
    isCauchySurfaceOn_inf_of_secondCountable timelikeLine_isCausal timelikeLine_isCauchySurface_zero
      h₁.cauchy h₂.cauchy⟩
  obtain ⟨hx₁, hx₂⟩ := Opens.mem_inf.1 hx
  exact (h₁.solves hx₁).trans (h₂.solves hx₂).symm

/-- `FrontierStaysIn` for a development `U₂`: the slab between `0` and a point of `U₁ ∩ U₂` is an
interval, in `U₁` by the relation and in `U₂` by preconnectedness. -/
theorem frontierStaysIn (U₁ : Opens ℝ) (h₂ : IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂)
    (V : Opens ℝ) : timelikeLine.FrontierStaysIn U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ) := by
  have hconn := isPreconnected_of_isDevelopment h₂
  have h0 : (0 : ℝ) ∈ (U₂ : Set ℝ) := h₂.subset rfl
  rintro q ⟨-, hqL⟩
  have hq₂ : q ∈ (U₂ : Set ℝ) := (Opens.mem_inf.1 hqL).2
  refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
  · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
    rw [Precausality.mem_Jminus_singleton] at hzq
    exact Opens.mem_inf.2 ⟨h0z.2 (right_mem_Icc.2 h0z.1),
      hconn.Icc_subset h0 hq₂ ⟨h0z.1, hzq.1⟩⟩
  · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
    rw [Precausality.mem_Jplus_singleton] at hqz
    exact Opens.mem_inf.2 ⟨hz0.2 (left_mem_Icc.2 hz0.1),
      hconn.Icc_subset hq₂ h0 ⟨hqz.1, hz0.1⟩⟩

/-- `SliceRestart` for two developments: a frontier point of `V` in `U₁ ∩ U₂` is not in `V`, so
the common development `U₁ ∩ U₂` is strictly larger. -/
theorem sliceRestart (h₁ : IsDevelopment idSol (fun _ => timelikeLine) {0} U₁ u₁)
    (h₂ : IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂) (V : Opens ℝ)
    (hV : timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V) :
    timelikeLine.SliceRestart U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ)
      (fun _ => ∃ V', timelikeLine.IsCommonDevelopment {0} U₁ U₂
        (fun V : Opens ℝ => EqOn u₁ u₂ V) V' ∧ V < V') := by
  rintro p ⟨hpf, hpL⟩ -
  refine ⟨U₁ ⊓ U₂, isCommonDevelopment_inf h₁ h₂, lt_of_le_of_ne hV.le fun hVeq => ?_⟩
  rw [V.isOpen.frontier_eq] at hpf
  exact hpf.2 (by rw [hVeq]; exact hpL)

/-- **The hypotheses of `ers_theorem_4_79_secondCountable` and `ers_theorem_4_80_secondCountable`**
on the timelike line: `sol = idSol`, `cau u` and `Cm` the timelike line, `S = {0}`. -/
theorem mughdData :
    SolutionLocal idSol ∧ SolutionsGlue idSol ∧
      CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) ∧
      (∀ U u, idSol U u → CurveNestedOn timelikeLine timelikeLine U) ∧
      (∀ U u, idSol U u → timelikeLine.CausallyArcConnectedOn U) ∧
      (∀ U u, idSol U u → InextensibleNestedOn timelikeLine timelikeLine U) ∧
      timelikeLine.IsCausal ∧ timelikeLine.IsAcausal ({0} : Set ℝ) ∧
      IsPreconnected ({0} : Set ℝ) ∧
      (∃ U u, IsDevelopment idSol (fun _ => timelikeLine) {0} U u) ∧
      (∀ U u, IsDevelopment idSol (fun _ => timelikeLine) {0} U u →
        ∃ W : Opens ℝ, W ≤ U ∧ {0} ⊆ (W : Set ℝ) ∧ timelikeLine.IsCauchySurfaceOn W {0} ∧
          idSol W u) ∧
      (∀ U u, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U u →
        timelikeLine.GloballyHyperbolicOn U) ∧
      (∀ U u, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U u →
        timelikeLine.TarentinOn U) ∧
      (∀ U u, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U u →
        timelikeLine.CompactSlabs U {0}) ∧
      (∀ U₁ u₁ U₂ u₂, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
        IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂ →
        ∃ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V) ∧
      (∀ U₁ u₁ U₂ u₂, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
        IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂ →
        ∀ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V →
        timelikeLine.FrontierStaysIn U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ)) ∧
      (∀ U₁ u₁ U₂ u₂, IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U₁ u₁ →
        IsDevelopment idSol (fun _ => timelikeLine) {0} U₂ u₂ →
        ∀ V, timelikeLine.IsCommonDevelopment {0} U₁ U₂ (fun V : Opens ℝ => EqOn u₁ u₂ V) V →
        timelikeLine.SliceRestart U₁ {0} V ((U₁ ⊓ U₂ : Opens ℝ) : Set ℝ)
          (fun _ => ∃ V', timelikeLine.IsCommonDevelopment {0} U₁ U₂
            (fun V : Opens ℝ => EqOn u₁ u₂ V) V' ∧ V < V')) := by
  have hGH := timelikeLine_globallyHyperbolic
  have hm : timelikeLine.IsCausal := by causal_ladder
  refine ⟨fun U u v huv hu x hx => (huv hx).symm.trans (hu hx),
    fun 𝒰 v _ h => agreementGlues_eqOn v id 𝒰 h,
    fun _ _ _ _ _ _ _ _ => Iff.rfl,
    fun U _ _ => (LeNested.refl _).curveNestedOn U,
    fun _ _ _ V _ => timelikeLine_causallyArcConnected V le_top,
    fun U _ _ => InextensibleNestedOn.refl _ U,
    hm,
    fun x hx y hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm,
    isPreconnected_singleton,
    ⟨⊤, id, ⟨fun _ _ => rfl, fun _ _ => trivial, timelikeLine_isCauchySurface_zero⟩⟩,
    fun U u h => ⟨U, le_rfl, h.subset, h.cauchy, h.solves⟩,
    fun U _ _ => timelikeLine_globallyHyperbolicOn U,
    fun U _ _ => tarentinOn U,
    fun U _ _ => (timelikeLine_globallyHyperbolicOn U).compactSlabs_singleton 0,
    fun _ _ _ _ h₁ h₂ => ⟨_, isCommonDevelopment_inf h₁.1 h₂⟩,
    fun U₁ _ _ _ _ h₂ V _ => frontierStaysIn U₁ h₂ V,
    fun _ _ _ _ h₁ h₂ V hV => sliceRestart h₁.1 h₂ V hV⟩

/-- **The development domains are not one**: `(ℝ, id)` and `(]-1, 1[, clamp)` are both
m-developments of `idSol`, and `]-1, 1[ ≠ ℝ`. -/
theorem two_mDevelopments :
    IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ⊤ id ∧
      IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ersWitnessIoo clamp ∧
      ersWitnessIoo ≠ ⊤ := by
  have hclamp : idSol ersWitnessIoo clamp := fun x hx => by
    obtain ⟨h1, h2⟩ := hx
    simp [clamp, min_eq_left h2.le, max_eq_right h1.le]
  have hI : timelikeLine.IsCauchySurfaceOn ersWitnessIoo ({0} : Set ℝ) :=
    timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl
  refine ⟨⟨⟨fun _ _ => rfl, fun _ _ => trivial, timelikeLine_isCauchySurface_zero⟩,
      timelikeLine_isCauchySurface_zero⟩,
    ⟨⟨hclamp, fun x hx => show x ∈ Ioo (-1 : ℝ) 1 by
      rw [mem_singleton_iff.1 hx]; constructor <;> norm_num, hI⟩, hI⟩, fun h => ?_⟩
  have h2 : (2 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) := trivial
  rw [← h] at h2
  exact absurd (show (2 : ℝ) ∈ Ioo (-1) 1 from h2).2 (by norm_num)

end ErsSCWitness

/-- **Witness for `ers_theorem_4_79_secondCountable` and `ers_theorem_4_80_secondCountable`**:
on the hypotheses `ErsSCWitness.mughdData` (solutions `id` on every open set of the timelike
line, `S = {0}`), which have at least two m-development domains, `ℝ` and `]-1, 1[`
(`ErsSCWitness.two_mDevelopments`), the MUGHD and the m-MGHD exist. -/
theorem timelikeLine_ers_theorem_4_79_4_80_secondCountable :
    (IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ⊤ id ∧
      IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ersWitnessIoo clamp ∧
      ersWitnessIoo ≠ ⊤) ∧
    (∃ U u, IsMaximalUniqueDevelopment idSol (fun _ => timelikeLine) {0} U u) ∧
      ∃ U u, IsMaximalMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} U u := by
  refine ⟨two_mDevelopments, ?_⟩
  obtain ⟨hloc, hglue, hfollow, hsub, harc, hinext, hm, hmacausal, hS, hex, hDm, hG, hT, hK,
    hlocal, hstay, hstep⟩ := mughdData
  exact ⟨ers_theorem_4_79_secondCountable hloc hglue hfollow hsub harc hinext hm hmacausal hS hex
      hDm hG hT hK hlocal hstay hstep,
    ers_theorem_4_80_secondCountable hloc hglue hfollow hsub harc hinext hm hmacausal hS hex hDm
      hG hT hK hlocal hstay hstep⟩

/-- **Witness for `IsMDevelopment.isUniqueDevelopment_secondCountable`**: `(]-1, 1[, clamp)` is an
m-development of `idSol` (every hypothesis on it from `ErsSCWitness.mughdData`), and a unique
development. -/
theorem timelikeLine_isUniqueDevelopment_secondCountable :
    IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ersWitnessIoo clamp ∧
      IsUniqueDevelopment idSol (fun _ => timelikeLine) {0} ersWitnessIoo clamp := by
  obtain ⟨-, -, -, hsub, harc, -, hm, hmacausal, hS, -, -, hG, hT, hK, hlocal, hstay, hstep⟩ :=
    mughdData
  have h := two_mDevelopments.2.1
  exact ⟨h, h.isUniqueDevelopment_secondCountable hsub harc hm hmacausal hS (hG _ _ h) (hT _ _ h)
    (hK _ _ h) (fun U₂ u₂ h₂ => hlocal _ _ U₂ u₂ h h₂) (fun U₂ u₂ h₂ => hstay _ _ U₂ u₂ h h₂)
    (fun U₂ u₂ h₂ => hstep _ _ U₂ u₂ h h₂)⟩

/-- **Witness for `IsMDevelopment.isUniqueDevelopment_secondCountable_noArc`**
(`Causal.Ers464WithoutArc`, beyond the target's list): the same data, without `harc`. -/
theorem timelikeLine_isUniqueDevelopment_secondCountable_noArc :
    IsMDevelopment idSol (fun _ => timelikeLine) timelikeLine {0} ersWitnessIoo clamp ∧
      IsUniqueDevelopment idSol (fun _ => timelikeLine) {0} ersWitnessIoo clamp := by
  obtain ⟨-, -, -, hsub, -, -, hm, hmacausal, hS, -, -, hG, hT, hK, hlocal, hstay, hstep⟩ :=
    mughdData
  have h := two_mDevelopments.2.1
  exact ⟨h, h.isUniqueDevelopment_secondCountable_noArc hsub hm hmacausal hS (hG _ _ h) (hT _ _ h)
    (hK _ _ h) (fun U₂ u₂ h₂ => hlocal _ _ U₂ u₂ h h₂) (fun U₂ u₂ h₂ => hstay _ _ U₂ u₂ h h₂)
    (fun U₂ u₂ h₂ => hstep _ _ U₂ u₂ h h₂)⟩

end Causal
