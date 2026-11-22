import Causal.PushUp
import Causal.Measure
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Measure remarks: `K^±(p)` is open in `J^±(p)`, and the one-sidedness of admissible measures

`rem:K_borelien` — `ETT.tex:829`. `rem:mesure_unilaterale_ptr` — `ETT.tex:1045`.

Neither is marked; see SCOPE.

> `rem:K_borelien`. Definition `defi:futur_continue` presents $K^\pm(p)$ as an intersection over
> the \emph{uncountable} family of sequences converging to $p$, so its measurability is not
> immediate --- yet inner regularity is applied to it in Proposition `prop:cont_ext_cont`. Lemma
> `lem:K_facile` settles the point: if $M$ is tarentin, one may choose a single sequence $(p_n)$
> with $p\in \ring J^+(p_n)$, and then $K^-(p)$ is a countable union of sets open in
> $J^\pm(p)$, hence a Borel subset of $M$.

> `rem:mesure_unilaterale_ptr`. The one-sided formulation is not a stylistic choice. As soon as a
> spacetime carries the analogue of a BTZ line --- a causal chain along which chronological pasts
> are empty --- no measure on it is admissible in the past and in the future at once, property
> $4$ being the obstruction; the computation is carried out in Remark `rem:mesure_unilaterale`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `rem:K_borelien`: `M` tarentin | ✓ carried |
| — `M` second countable (`def:category_topological_spacetimes`) | ⚠ weakened: `FirstCountableTopology M` |
| — "hence a Borel subset of `M`" | ⚠ strengthened: `J^-(p)` Borel (`measurableSet_Kminus`); carried with no added hypothesis on a tarentin globally hyperbolic Hausdorff spacetime, the setting of `prop:cont_ext_cont` (`measurableSet_K_of_globallyHyperbolic`) |
| `rem:mesure_unilaterale_ptr`: a causal chain `p < q` along which chronological pasts are empty | ✓ carried: `hline` (`J^-(q) ∖ J^-(p) ⊂ J^+(p)`) and `hempty` |
| — (used by `rem:mesure_unilaterale`, not named in this remark) | ⚠ strengthened: `K^+(p) ⊂ I^+(p)` (`prop:K_calcul` (b)), or push-up and `p ∈ Z^+(M)` |

## SCOPE (disclosed)

* **`rem:K_borelien`.** The single sequence and the countable union are proved
  (`exists_seq_mem_interior_Jplus`, `lem:K_facile`); the union is moreover itself open in
  `J^-(p)`: `K^-(p) = J^-(p) ∩ O` with `O` open (`Kminus_eq_inter_isOpen`). "Hence Borel" needs
  `J^-(p)` Borel: a relatively open subset of a set which is not Borel need not be Borel. Where
  the remark is used, `J^-(p)` is closed (`prop:GH_Jferme`). The library's `prop:cont_ext_cont`
  does not use the remark at all (see `Causal/Measure.lean`).
* **`rem:mesure_unilaterale_ptr` is false in the generality stated.** The lightlike line is a
  causal chain along which every chronological past is empty, and the standard Gaussian measure
  is admissible on it in the past and in the future at once
  (`lightlikeLine_admissible_past_and_future`). What the computation of `rem:mesure_unilaterale`
  also uses is `K^+(p) = I^+(p)` at the lower end `p` of the segment, which holds at a BTZ point
  (`prop:K_calcul` (b)) and fails on the lightlike line, where `K^+(p) = ]p, +∞[` and
  `I^+(p) = ∅` (`lightlikeLine_chain`). With it, the obstruction is proved
  (`not_admissiblePast_and_admissibleFuture`, `…_of_pushUp`).
  Its hypotheses are satisfied on the pointed line at `p = 0`, `q = 1`
  (`pointedLineMR_obstruction_hypotheses`, `pointedLineMR_not_admissible`); the `_of_pushUp`
  form has no witness here, one needing dimension at least 2; it has one at `E₀`
  (`Causal.SingularRowsGeroch.nonvacuous_e0_chain`; also `Causal.E0.mesure_unilaterale`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {p q : M}

/-! ### `rem:K_borelien` -/

/-- At a point of a tarentin spacetime with a countable basis of neighbourhoods, there is a
sequence `p_n → p` with `p ∈ Int J^+(p_n)` for every `n`. -/
theorem exists_seq_mem_interior_Jplus [FirstCountableTopology M] (hT : C.Tarentin) (p : M) :
    ∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧ ∀ n, p ∈ interior (C.Jplus ⊤ {u n}) := by
  obtain ⟨B, hB⟩ := (𝓝 p).exists_antitone_basis
  have h : ∀ n, ∃ a, a ∈ B n ∧ p ∈ interior (C.Jplus ⊤ {a}) := by
    intro n
    obtain ⟨a, ha, b, -, hx⟩ := hT p (B n) (hB.mem n)
    exact ⟨a, ha, interior_mono diamond_subset_Jplus hx⟩
  choose v hvB hv using h
  exact ⟨v, hB.tendsto hvB, hv⟩

/-- `rem:K_borelien`, the topological content: on a tarentin spacetime with a countable basis of
neighbourhoods, `K^-(p)` is open in `J^-(p)`. -/
theorem Kminus_eq_inter_isOpen [FirstCountableTopology M] (hT : C.Tarentin) (p : M) :
    ∃ O : Set M, IsOpen O ∧ C.Kminus ⊤ {p} = C.Jminus ⊤ {p} ∩ O := by
  obtain ⟨v, hv, hint⟩ := exists_seq_mem_interior_Jplus hT p
  refine ⟨⋃ N : ℕ, openHull (C.Jminus ⊤ {p}) (⋂ n ≥ N, C.Jminus ⊤ {v n}),
    isOpen_iUnion fun _ => isOpen_openHull, ?_⟩
  rw [Kminus_eq_of_tendsto hv hint, inter_iUnion]
  simp_rw [interiorWithin_eq]

theorem Kplus_eq_inter_isOpen [FirstCountableTopology M] (hT : C.Tarentin) (p : M) :
    ∃ O : Set M, IsOpen O ∧ C.Kplus ⊤ {p} = C.Jplus ⊤ {p} ∩ O :=
  Kminus_eq_inter_isOpen (C := C.dual) (dual_tarentin.2 hT) p

variable [MeasurableSpace M]

/-- `rem:K_borelien`: `K^-(p)` is Borel as soon as `J^-(p)` is. -/
theorem measurableSet_Kminus [OpensMeasurableSpace M] [FirstCountableTopology M]
    (hT : C.Tarentin) (hJ : MeasurableSet (C.Jminus ⊤ {p})) :
    MeasurableSet (C.Kminus ⊤ {p}) := by
  obtain ⟨O, hO, hK⟩ := Kminus_eq_inter_isOpen hT p
  rw [hK]
  exact hJ.inter hO.measurableSet

theorem measurableSet_Kplus [OpensMeasurableSpace M] [FirstCountableTopology M]
    (hT : C.Tarentin) (hJ : MeasurableSet (C.Jplus ⊤ {p})) :
    MeasurableSet (C.Kplus ⊤ {p}) :=
  measurableSet_Kminus (C := C.dual) (dual_tarentin.2 hT) hJ

/-- `rem:K_borelien` in the setting of `prop:cont_ext_cont`: on a tarentin globally hyperbolic
Hausdorff spacetime with a countable basis of neighbourhoods, `K^±(p)` is Borel. -/
theorem measurableSet_K_of_globallyHyperbolic [OpensMeasurableSpace M] [T2Space M]
    [FirstCountableTopology M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (p : M) :
    MeasurableSet (C.Kminus ⊤ {p}) ∧ MeasurableSet (C.Kplus ⊤ {p}) :=
  ⟨measurableSet_Kminus hT (hG.isClosed_Jminus_singleton hT p).measurableSet,
    measurableSet_Kplus hT (hG.isClosed_Jplus_singleton hT p).measurableSet⟩

/-! ### `rem:mesure_unilaterale_ptr` -/

/-- `rem:mesure_unilaterale_ptr`, the obstruction. -/
theorem not_admissiblePast_and_admissibleFuture {μ : Measure M} (hpq : C.le ⊤ p q)
    (hne : p ≠ q) (hline : C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p})
    (hempty : ∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅)
    (hK : C.Kplus ⊤ {p} ⊆ C.Iplus ⊤ {p}) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) := by
  rintro ⟨h1, h2⟩
  have hsub : C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p} \ C.Kplus ⊤ {p} := by
    intro r hr
    refine ⟨hline hr, fun hrK => ?_⟩
    have hpr : C.lt ⊤ p r := by simpa using hK hrK
    have : p ∈ C.Iminus ⊤ {r} := by simpa using hpr
    rw [hempty r hr] at this
    exact this
  exact (h1.pos hpq hne).ne' (measure_mono_null hsub (h2.null {p}))

/-- `rem:mesure_unilaterale_ptr`, with `K^+(p) = I^+(p)` obtained from push-up at a point
strongly tarentin in the future. Not witnessed in this file: `p ∈ Z^+(M)` forces chronological-future points near `p` off the
chain, so a witness needs dimension at least 2 (`pointedLineMR_obstruction_hypotheses` witnesses
the general form only). The witness is at `E₀`: `Causal.SingularRowsGeroch.nonvacuous_e0_chain`. -/
theorem not_admissiblePast_and_admissibleFuture_of_pushUp [FirstCountableTopology M]
    {μ : Measure M} (hP : C.PushUp) (hZ : p ∈ C.Zplus) (hpq : C.le ⊤ p q) (hne : p ≠ q)
    (hline : C.Jminus ⊤ {q} \ C.Jminus ⊤ {p} ⊆ C.Jplus ⊤ {p})
    (hempty : ∀ r ∈ C.Jminus ⊤ {q} \ C.Jminus ⊤ {p}, C.Iminus ⊤ {r} = ∅) :
    ¬ (C.AdmissiblePast μ ∧ C.AdmissibleFuture μ) :=
  not_admissiblePast_and_admissibleFuture hpq hne hline hempty
    (PushUp.Kplus_eq_Iplus hP hZ).subset

end Causality

/-! ### The lightlike line: a causal chain with empty chronological pasts carrying a measure
admissible in the past and in the future -/

section Lightlike

open Causality

theorem lightlikeLine_Jminus_diff_Kminus_subsingleton (A : Set ℝ) :
    (lightlikeLine.Jminus ⊤ A \ lightlikeLine.Kminus ⊤ A).Subsingleton := by
  have key : ∀ y ∈ lightlikeLine.Jminus ⊤ A \ lightlikeLine.Kminus ⊤ A,
      y ∈ A ∧ ∀ a ∈ A, a ≤ y := by
    rintro y ⟨⟨a, ha, hya⟩, hyK⟩
    have hall : ∀ a ∈ A, a ≤ y := by
      intro a ha
      by_contra h
      apply hyK
      rw [Kminus_eq_biUnion]
      refine mem_iUnion₂.2 ⟨a, ha, ?_⟩
      rw [(lightlikeLine_K a).1]
      exact not_le.1 h
    have hya' : y ≤ a := lightlikeLine_le_top.1 hya
    have hy : y = a := le_antisymm hya' (hall a ha)
    exact ⟨by rw [hy]; exact ha, hall⟩
  intro y hy y' hy'
  obtain ⟨hyA, hy⟩ := key y hy
  obtain ⟨hy'A, hy'⟩ := key y' hy'
  exact le_antisymm (hy' y hyA) (hy y' hy'A)

theorem lightlikeLine_Jplus_diff_Kplus_subsingleton (A : Set ℝ) :
    (lightlikeLine.Jplus ⊤ A \ lightlikeLine.Kplus ⊤ A).Subsingleton := by
  have key : ∀ y ∈ lightlikeLine.Jplus ⊤ A \ lightlikeLine.Kplus ⊤ A,
      y ∈ A ∧ ∀ a ∈ A, y ≤ a := by
    rintro y ⟨⟨a, ha, hay⟩, hyK⟩
    have hall : ∀ a ∈ A, y ≤ a := by
      intro a ha
      by_contra h
      apply hyK
      rw [Kplus_eq_biUnion]
      refine mem_iUnion₂.2 ⟨a, ha, ?_⟩
      rw [(lightlikeLine_K a).2]
      exact not_le.1 h
    have hay' : a ≤ y := lightlikeLine_le_top.1 hay
    have hy : y = a := le_antisymm (hall a ha) hay'
    exact ⟨by rw [hy]; exact ha, hall⟩
  intro y hy y' hy'
  obtain ⟨hyA, hy⟩ := key y hy
  obtain ⟨hy'A, hy'⟩ := key y' hy'
  exact le_antisymm (hy y' hy'A) (hy' y hyA)

theorem gaussianReal_Ioo_pos {a b : ℝ} (hab : a < b) :
    0 < ProbabilityTheory.gaussianReal 0 1 (Ioo a b) := by
  refine pos_iff_ne_zero.2 fun h => ?_
  have h0 := ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- The lightlike line satisfies the two hypotheses `rem:mesure_unilaterale_ptr` names for every
`p < q`, and not the third one the computation of `rem:mesure_unilaterale` uses. -/
theorem lightlikeLine_chain {p q : ℝ} (hpq : p < q) :
    lightlikeLine.Jminus ⊤ {q} \ lightlikeLine.Jminus ⊤ {p} ⊆ lightlikeLine.Jplus ⊤ {p} ∧
    (∀ r, lightlikeLine.Iminus ⊤ {r} = ∅) ∧
    ¬ lightlikeLine.Kplus ⊤ {p} ⊆ lightlikeLine.Iplus ⊤ {p} := by
  refine ⟨fun r hr => ?_, fun r => ?_, fun h => ?_⟩
  · have hrp : ¬ r ≤ p := fun h => hr.2 (by simpa using h)
    simpa using (not_le.1 hrp).le
  · ext x
    simp
  · have : q ∈ lightlikeLine.Kplus ⊤ {p} := by rw [(lightlikeLine_K p).2]; exact hpq
    have h' := h this
    simp at h'

/-- The lightlike line carries a measure admissible in the past and in the future at once:
the standard Gaussian measure. It is a causal chain along which chronological pasts are empty,
so the hypothesis `rem:mesure_unilaterale_ptr` names is not, by itself, an obstruction. -/
theorem lightlikeLine_admissible_past_and_future :
    lightlikeLine.AdmissiblePast (ProbabilityTheory.gaussianReal 0 1) ∧
      lightlikeLine.AdmissibleFuture (ProbabilityTheory.gaussianReal 0 1) := by
  haveI := ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine ⟨⟨inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · have hlt : p < q := lt_of_le_of_ne (lightlikeLine_le_top.1 hpq) hne
    refine (gaussianReal_Ioo_pos hlt).trans_le (measure_mono fun x hx => ⟨?_, ?_⟩)
    · simpa using hx.2.le
    · intro h
      have : x ≤ p := by simpa using h
      exact absurd hx.1 (not_lt.2 this)
  · exact (lightlikeLine_Jminus_diff_Kminus_subsingleton A).countable.measure_zero _
  · have hlt : p < q := lt_of_le_of_ne (lightlikeLine_le_top.1 hpq) hne
    refine (gaussianReal_Ioo_pos hlt).trans_le (measure_mono fun x hx => ⟨?_, ?_⟩)
    · simpa using hx.1.le
    · intro h
      have : q ≤ x := by simpa using h
      exact absurd hx.2 (not_lt.2 this)
  · exact (lightlikeLine_Jplus_diff_Kplus_subsingleton A).countable.measure_zero _

end Lightlike


/-! ### The hypotheses of the obstruction are satisfiable: the pointed line -/

section Pointed

open Causality

/-- The **pointed line** (rebuilt here from WP-2's `pointedLine`, under a distinct name): only
`0` has a future, `0 ≤_U y` for `y > 0` with `[0,y] ⊂ U`; no chronology. -/
def pointedLineMR : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (x = 0 ∧ 0 < y ∧ Icc 0 y ⊆ (U : Set ℝ))
  lt _ _ _ := False
  le_mem_left h := h.elim (fun h => h.2) fun h => by
    rw [h.1]; exact h.2.2 (left_mem_Icc.2 h.2.1.le)
  le_mem_right h := h.elim (fun h => h.1 ▸ h.2) fun h => h.2.2 (right_mem_Icc.2 h.2.1.le)
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | h₁
    · exact h₂
    · rcases h₂ with ⟨rfl, -⟩ | ⟨rfl, h, -⟩
      · exact Or.inr h₁
      · exact absurd h₁.2.1 (lt_irrefl 0)
  lt_trans h _ := h
  le_mono h _ _ h' := h'.elim (fun h' => Or.inl ⟨h'.1, h h'.2⟩)
    fun h' => Or.inr ⟨h'.1, h'.2.1, fun _ hz => h (h'.2.2 hz)⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

/-- On the pointed line `K^+(0) = ∅` (the argument of WP-2's `pointedLine_Kplus_zero`). -/
theorem pointedLineMR_Kplus_zero : pointedLineMR.Kplus ⊤ {0} = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
  have hut : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := Causality.mem_Kplus_singleton.1 hy u hut
  have hmem := interiorWithin_subset hN
  simp only [mem_inter_iff, mem_iInter] at hmem
  have hpos : ∀ n, u n ≠ 0 := fun n => by simp only [hu]; positivity
  have key : ∀ n ≥ N, u n = y := fun n hn => by
    have := hmem.2 n hn
    simp only [Precausality.mem_Jplus_singleton] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (hpos n)
  have h1 := key N le_rfl
  have h2 := key (N + 1) (Nat.le_succ N)
  have : u N = u (N + 1) := h1.trans h2.symm
  simp only [hu, Nat.cast_add, Nat.cast_one] at this
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [div_eq_div_iff hN0.ne' (by positivity)] at this
  linarith

/-- The hypotheses of `not_admissiblePast_and_admissibleFuture` are satisfiable: the pointed
line at `p = 0`, `q = 1`, where `J^-(1) ∖ J^-(0) = {1} ⊂ J^+(0)`, `I^- = ∅` and
`K^+(0) = ∅ = I^+(0)`. The obstruction is therefore not vacuous: no measure on the pointed line
is admissible in the past and in the future at once (`pointedLineMR_not_admissible`).

The `_of_pushUp` form (`not_admissiblePast_and_admissibleFuture_of_pushUp`) has no witness
here (its witness is at `E₀`, `Causal.SingularRowsGeroch.nonvacuous_e0_chain`): the pointed line has push-up (vacuously) but `0 ∉ Z^+` since `I^+(0) = ∅`. A witness
needs `p ∈ Z^+(M)`, i.e. points `r ≫ p` arbitrarily close to `p`, which therefore have
`p ∈ I^-(r) ≠ ∅` and must lie off the chain `]p, q]`: a second direction besides the chain, as
in the 3-dimensional BTZ model. None is built here; at `E₀` it is
`Causal.SingularRowsGeroch.nonvacuous_e0_chain`. -/
theorem pointedLineMR_obstruction_hypotheses :
    pointedLineMR.le ⊤ 0 1 ∧ (0 : ℝ) ≠ 1 ∧
    pointedLineMR.Jminus ⊤ {1} \ pointedLineMR.Jminus ⊤ {0} ⊆ pointedLineMR.Jplus ⊤ {0} ∧
    (∀ r ∈ pointedLineMR.Jminus ⊤ {1} \ pointedLineMR.Jminus ⊤ {0},
      pointedLineMR.Iminus ⊤ {r} = ∅) ∧
    pointedLineMR.Kplus ⊤ {0} ⊆ pointedLineMR.Iplus ⊤ {0} := by
  refine ⟨Or.inr ⟨rfl, one_pos, fun _ _ => trivial⟩, zero_ne_one, ?_, fun r _ => ?_, ?_⟩
  · rintro r ⟨hr1, hr0⟩
    simp only [Precausality.mem_Jminus_singleton] at hr1 hr0
    simp only [Precausality.mem_Jplus_singleton]
    rcases hr1 with ⟨rfl, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inr ⟨rfl, one_pos, fun _ _ => trivial⟩
    · exact absurd (Or.inl ⟨rfl, trivial⟩) hr0
  · ext x
    simp [pointedLineMR, Precausality.mem_Iminus]
  · rw [pointedLineMR_Kplus_zero]
    exact empty_subset _

/-- The obstruction applied: no measure on the pointed line is admissible in the past and in the
future at once. -/
theorem pointedLineMR_not_admissible (μ : Measure ℝ) :
    ¬ (pointedLineMR.AdmissiblePast μ ∧ pointedLineMR.AdmissibleFuture μ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pointedLineMR_obstruction_hypotheses
  exact not_admissiblePast_and_admissibleFuture h1 h2 h3 h4 h5

end Pointed

end Causal
