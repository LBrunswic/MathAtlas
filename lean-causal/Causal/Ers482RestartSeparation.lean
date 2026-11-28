import Causal.Ers482Solution

/-!
# ERS Thm 4.82's uniform restart is not implied by its conclusion

Programme target `T-abs-ers-4-82-restart-separation` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, no model, no metric, no PDE). Source: Eperon–Reall–Sbierski, arXiv 1802.03020,
`papers/ers-predictability` (`legacy/labeled/ghd_02_19.tex`). **No label is marked**: this file
separates two hypotheses of the Lean forms of `ersthm:ThmNotBlocking` (`ghd_02_19.tex:1100`, proof
1114–1139); it proves nothing the paper states.

The uniform forms of record `ers_theorem_4_82_solution_of_restarts` and
`ers_theorem_4_82_solution_of_restarts_isCausal` (`Causal.Ers482Solution`) ask the geometric
restart `GluedRestartAt` of **every** pair of developments (`hrestart`). Their paper's-shape twin
`ers_theorem_4_82_solution` asks it of the maximal `U₁` alone, and there it is equivalent to the
conclusion given the rest (`ers_theorem_4_82_solution_hstep_iff`). Here, at one problem, every
hypothesis of both uniform forms except `hrestart` holds, their conclusion holds, and `hrestart`
fails, at a non-maximal pair: `Causal.Ers482Separation.restart_separation`. So the conclusion
(with the rest) does not imply the uniform restart.

> Then u1 : U1 → R is the unique MGHD, i.e., any other GHD u : U → R satisfies U ⊆ U1 and thus
> also u1|U = u. (`ghd_02_19.tex:1106`)

> We can now define u3 : U3 → R, U3 := U1 ∪ DΣV, u3(x) := u1(x) for x ∈ U1 and u3(x) := u2(x)
> for x ∈ DΣV. […] It is easy to see that u3 : U3 → R is a GHD the domain of which contains that
> of the MGHD u1 : U1 → R. This is a contradiction. (`ghd_02_19.tex:1138`)

## The model

* `M = ℝ`, `S = {0}`, `s₀ = 0`; the problem `Ers482Witness.sol82` (`u` solves on `U` iff
  `U ⊆ ]-1, 1[` and `u = id` on `U`); `U₁ = ]-1, 1[`, `u₁ = id`.
* The markers `mark a` (`x` on `]-a, a[`, `7` off it).
* A **solution-dependent causality** `cauSep`: the timelike line at `id` and at every
  `mark a`, `a ∈ ]0, 1]`; the spacelike line at every other function.
* A development `(U, u)` has `cauSep u = timelikeLine` (`cauSep_eq_of_isDevelopment`): for the
  spacelike line an inextensible curve through `x ∈ U ∖ {0}` is constant and misses `{0}`
  (`spacelikeLine_subset_of_isCauchySurfaceOn`). So every side condition of the forms is the
  timelike line's.
* The failing pair: `U₀ = ]-1/2, 1/10[` with `mark (1/2)`, `U₂ = ]-1/5, 1/5[` with
  `mark (1/5)`, both developments, neither maximal, `U₂ ⊄ U₀`. The component of `U₀ ∩ U₂`
  through `0` is `A = ]-1/5, 1/10[`; `p = 1/10` is a frontier point of `A` in `U₂`, spacelike in
  `U₂`; at `V = U₂` (`V ∩ U₀ ⊆ A`) the glued function (`x` on `]-1/2, 1/5[`, `7` off it) is
  neither `id` nor a marker, its causality is the spacelike line, and no open `O` has `{0}`
  Cauchy in `U₀ ∪ O ∋ -1/4` (`not_gluedRestartAt_pair`).

## Hypothesis checklist

| hypothesis of `_of_restarts` / `_of_restarts_isCausal` | here |
|---|---|
| `hloc`, `hglue`, `hres` | ✓ `sol82_local`, `sol82_glue`, `sol82_restricts` |
| `hs₀`, `hmax` (`]-1, 1[`, `id`) | ✓ |
| `honesided` | ✓ `Ers482Witness.honesided82` |
| `hconn`, `hsplit` | ✓ any causality, `S` Cauchy on second countable `ℝ` |
| `hG`, `hT`, `hcaus`, `hJm`, `hJp`, `hK` | ✓ through `cauSep_eq_of_isDevelopment` |
| `hSclosed` | ✓ `closure_singleton`: `{0}` is closed whatever the causality |
| `hagree` | ✓ every solution is `id` on its domain |
| `hrestart` | ✗ fails at `(]-1/2, 1/10[, mark (1/2))`, `(]-1/5, 1/5[, mark (1/5))`, `p = 1/10` |
| conclusion | ✓ every development lies in `]-1, 1[` and is `id` there |

## SCOPE (disclosed)

* **`CausalityFollows` fails** (`not_causalityFollows_cauSep`): `mark (1/5)` and the glued
  function agree on `]-1/5, 1/5[`, where `0 ≤ 1/10` for the first causality and not for the
  second. The forms do not assume it (`Causal.Ers482Solution`, "The reading": the restart names
  the glued solution's causality itself), so the separation is one of the forms as stated. With
  `CausalityFollows` the conclusion makes the glued solution `u₁` on `U₀ ∪ U₂`, and the uniform
  restart a statement about `cau u₁` alone. Whether a separation survives it is not proved
  either way here. Argued, not proved: on `ℝ` with `S = {0}` none does. The developments are
  intervals, the curves of a causal development are monotone, and so an interval between two
  Cauchy intervals is Cauchy, which gives `O = ]p - ε, p + ε[`.
* **The paper's shape applies to the model** (`hstep_solution`): the fixed-`U₁` restart of
  `ers_theorem_4_82_solution` holds at `]-1, 1[`, vacuously (every development lies in it,
  `ers_theorem_4_82_solution_hstep_of_le`). So on this model the fixed-`U₁` forms give the
  conclusion and the uniform forms do not apply.
* The failure does not depend on `V` or `O`: for every open `O`, `{0}` is not a Cauchy surface
  of `U₀ ∪ O` for the glued causality. `u₀ = id` gives the same glued function. `p = -1/5` is
  not in `U₂`, so `1/10` is the only frontier point the restart reads.
* `restart_separation_forms` is the mechanical check that the conjuncts of
  `restart_separation` are the binders of the two forms: both, applied to them, typecheck.
* No `sorry` in this file. The three assertions are stated at the same data, in one theorem.
  `Metric.isOpen_iff` and `Real.dist_eq` appear in one proof only, for a neighbourhood of `0`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

/-- **A Cauchy surface of an open set for the spacelike line contains it**: through `x ∈ U` runs
an inextensible causal curve of `U` (`Causality.inextensibleThrough_of_t1_secondCountable`),
constant since `≤_U` is equality (`CausalCurveIn.le_of_le`), so it meets `S` at `x`. -/
theorem spacelikeLine_subset_of_isCauchySurfaceOn {U : Opens ℝ} {S : Set ℝ}
    (h : spacelikeLine.IsCauchySurfaceOn U S) : (U : Set ℝ) ⊆ S := by
  intro x hx
  obtain ⟨I, c, hc, s, hs, hcs⟩ :=
    Causality.inextensibleThrough_of_t1_secondCountable spacelikeLine U x hx
  obtain ⟨y, ⟨⟨t, ht, rfl⟩, hyS⟩, -⟩ := h I c hc
  have hst : c s = c t := by
    rcases le_total s t with h' | h'
    · exact (spacelikeLine_le.1 (hc.1.le_of_le hs ht h')).1
    · exact (spacelikeLine_le.1 (hc.1.le_of_le ht hs h')).1.symm
  rw [← hcs, hst]
  exact hyS

namespace Ers482Separation

open Causality Ers482Witness

/-! ## 1. The model -/

open Classical in
/-- **The marker** `mark a`: `x` on `]-a, a[`, `7` off it. -/
noncomputable def mark (a : ℝ) : ℝ → ℝ := fun x => if x ∈ Ioo (-a) a then x else 7

open Classical in
/-- **The solution-dependent causality**: the timelike line at `id` and at the markers
`mark a`, `a ∈ ]0, 1]`; the spacelike line at every other function. -/
noncomputable def cauSep : (ℝ → ℝ) → Causality ℝ := fun u =>
  if u = id ∨ ∃ a ∈ Ioc (0 : ℝ) 1, u = mark a then timelikeLine else spacelikeLine

/-- `U₀ = ]-1/2, 1/10[`. -/
def dom₀ : Opens ℝ := ⟨Ioo (-(1 / 2)) (1 / 10), isOpen_Ioo⟩

/-- `U₂ = ]-1/5, 1/5[`. -/
def dom₂ : Opens ℝ := ⟨Ioo (-(1 / 5)) (1 / 5), isOpen_Ioo⟩

/-- The glued function of the pair (ERS's `u₃`): `mark (1/2)` on `U₀`, `mark (1/5)` off it. -/
noncomputable def glue₀₂ : ℝ → ℝ := glueSolutions dom₀ (mark (1 / 2)) (mark (1 / 5))

/-- Membership in `U₀`. -/
theorem mem_dom₀ {x : ℝ} : x ∈ dom₀ ↔ x ∈ Ioo (-(1 / 2) : ℝ) (1 / 10) := Iff.rfl

/-- Membership in `U₂`. -/
theorem mem_dom₂ {x : ℝ} : x ∈ dom₂ ↔ x ∈ Ioo (-(1 / 5) : ℝ) (1 / 5) := Iff.rfl

/-- A marker is `x` on `]-a, a[`. -/
theorem mark_of_mem {a x : ℝ} (hx : x ∈ Ioo (-a) a) : mark a x = x := by
  classical
  simp only [mark]
  exact if_pos hx

/-- A marker is `7` off `]-a, a[`. -/
theorem mark_of_notMem {a x : ℝ} (hx : x ∉ Ioo (-a) a) : mark a x = 7 := by
  classical
  simp only [mark]
  exact if_neg hx

/-- The causality at `id` is the timelike line. -/
theorem cauSep_id : cauSep id = timelikeLine :=
  if_pos (Or.inl rfl)

/-- The causality at a marker `mark a`, `a ∈ ]0, 1]`, is the timelike line. -/
theorem cauSep_mark {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) : cauSep (mark a) = timelikeLine :=
  if_pos (Or.inr ⟨a, ha, rfl⟩)

/-- The causality at any other function is the spacelike line. -/
theorem cauSep_of_not {u : ℝ → ℝ} (hu : ¬ (u = id ∨ ∃ a ∈ Ioc (0 : ℝ) 1, u = mark a)) :
    cauSep u = spacelikeLine :=
  if_neg hu

/-- **Every development has the timelike line as causality**: for the spacelike line `{0}` would
contain the open `U ∋ 0` (`spacelikeLine_subset_of_isCauchySurfaceOn`). -/
theorem cauSep_eq_of_isDevelopment {U : Opens ℝ} {u : ℝ → ℝ}
    (h : IsDevelopment sol82 cauSep {0} U u) : cauSep u = timelikeLine := by
  by_cases hu : u = id ∨ ∃ a ∈ Ioc (0 : ℝ) 1, u = mark a
  · rcases hu with rfl | ⟨a, ha, rfl⟩
    · exact cauSep_id
    · exact cauSep_mark ha
  · exfalso
    have hc := h.cauchy
    rw [cauSep_of_not hu] at hc
    have hsub := spacelikeLine_subset_of_isCauchySurfaceOn hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 U.isOpen 0 (h.subset (mem_singleton 0))
    have hmem : ε / 2 ∈ (U : Set ℝ) := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith)
    have h0 := hsub hmem
    rw [mem_singleton_iff] at h0
    linarith

/-- The glued function is `x` on `U₀`. -/
theorem glue₀₂_of_mem {x : ℝ} (hx : x ∈ Ioo (-(1 / 2) : ℝ) (1 / 10)) : glue₀₂ x = x := by
  have h := eqOn_glueSolutions_left dom₀ (mark (1 / 2)) (mark (1 / 5))
    (show x ∈ (dom₀ : Set ℝ) from hx)
  rw [glue₀₂, h]
  exact mark_of_mem ⟨hx.1, by linarith [hx.2]⟩

/-- The glued function is `mark (1/5)` off `U₀`. -/
theorem glue₀₂_of_notMem {x : ℝ} (hx : x ∉ Ioo (-(1 / 2) : ℝ) (1 / 10)) :
    glue₀₂ x = mark (1 / 5) x := by
  classical
  simp only [glue₀₂, glueSolutions]
  exact if_neg hx

/-- **The glued function's causality is the spacelike line**: it is `x` on `]-1/2, 1/5[` and `7`
off it, so not `id` (at `1/2`) and not a marker (`mark a (-3/10) = -3/10` forces `a > 3/10`, and
then `mark a (1/4) = 1/4 ≠ 7`). -/
theorem cauSep_glue₀₂ : cauSep glue₀₂ = spacelikeLine := by
  refine cauSep_of_not ?_
  rintro (h | ⟨a, -, h⟩)
  · have h1 := congrFun h (1 / 2)
    rw [glue₀₂_of_notMem (fun hx => by norm_num at hx),
      mark_of_notMem (fun hx => by norm_num at hx)] at h1
    norm_num at h1
  · have h1 := congrFun h (-(3 / 10))
    rw [glue₀₂_of_mem ⟨by norm_num, by norm_num⟩] at h1
    have ha : (3 / 10 : ℝ) < a := by
      by_contra hna
      rw [mark_of_notMem (fun hx => hna (by linarith [hx.1]))] at h1
      norm_num at h1
    have h2 := congrFun h (1 / 4)
    rw [glue₀₂_of_notMem (fun hx => by norm_num at hx),
      mark_of_notMem (fun hx => by norm_num at hx), mark_of_mem ⟨by linarith, by linarith⟩] at h2
    norm_num at h2

/-! ## 2. The developments of the model -/

/-- `(]-1, 1[, id)` is a development. -/
theorem isDevelopment_ersWitnessIoo_sep : IsDevelopment sol82 cauSep {0} ersWitnessIoo id :=
  ⟨⟨fun _ hx => hx, fun _ _ => rfl⟩,
    singleton_subset_iff.2 (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num),
    by rw [cauSep_id]; exact timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl⟩

/-- **`(]-1, 1[, id)` is a maximal development**: every development lies in `]-1, 1[`. -/
theorem isMaximalDevelopment_ersWitnessIoo_sep :
    IsMaximalDevelopment sol82 cauSep {0} ersWitnessIoo id :=
  ⟨isDevelopment_ersWitnessIoo_sep, fun _ _ h _ => h.solves.1⟩

/-- `(]-1/2, 1/10[, mark (1/2))` is a development
(`timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos`). -/
theorem isDevelopment_dom₀ : IsDevelopment sol82 cauSep {0} dom₀ (mark (1 / 2)) :=
  ⟨⟨fun x hx => ⟨by linarith [(mem_dom₀.1 hx).1], by linarith [(mem_dom₀.1 hx).2]⟩,
      fun x hx => mark_of_mem ⟨(mem_dom₀.1 hx).1, by linarith [(mem_dom₀.1 hx).2]⟩⟩,
    singleton_subset_iff.2 (mem_dom₀.2 ⟨by norm_num, by norm_num⟩),
    by
      rw [cauSep_mark ⟨by norm_num, by norm_num⟩]
      exact timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by norm_num) (by norm_num) rfl⟩

/-- `(]-1/5, 1/5[, mark (1/5))` is a development. -/
theorem isDevelopment_dom₂ : IsDevelopment sol82 cauSep {0} dom₂ (mark (1 / 5)) :=
  ⟨⟨fun x hx => ⟨by linarith [(mem_dom₂.1 hx).1], by linarith [(mem_dom₂.1 hx).2]⟩,
      fun x hx => mark_of_mem (mem_dom₂.1 hx)⟩,
    singleton_subset_iff.2 (mem_dom₂.2 ⟨by norm_num, by norm_num⟩),
    by
      rw [cauSep_mark ⟨by norm_num, by norm_num⟩]
      exact timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by norm_num) (by norm_num) rfl⟩

/-- The timelike line's global hyperbolicity, on every development of the model. -/
theorem hG_sep : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cauSep {0} U u →
    (cauSep u).GloballyHyperbolicOn U := fun U _ h => by
  rw [cauSep_eq_of_isDevelopment h]; exact timelikeLine_globallyHyperbolicOn U

/-- The timelike line's tarentin property, on every development of the model. -/
theorem hT_sep : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cauSep {0} U u →
    (cauSep u).TarentinOn U := fun U _ h => by
  rw [cauSep_eq_of_isDevelopment h]; exact timelikeLine_tarentinOn U

/-- A development of the model is preconnected (any causality: `S = {0}` Cauchy on `ℝ`). -/
theorem hconn_sep : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cauSep {0} U u →
    IsPreconnected (U : Set ℝ) := fun _ _ h =>
  isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable isPreconnected_singleton h.subset
    h.cauchy

/-! ## 3. The failing pair -/

/-- The component of `U₀ ∩ U₂` through `0` is `]-1/5, 1/10[`. -/
theorem component₀₂ :
    connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0 = Ioo (-(1 / 5)) (1 / 10) := by
  have h : (dom₀ : Set ℝ) ∩ dom₂ = Ioo (-(1 / 5)) (1 / 10) := by
    ext x
    show x ∈ Ioo (-(1 / 2) : ℝ) (1 / 10) ∩ Ioo (-(1 / 5)) (1 / 5) ↔ _
    simp only [mem_inter_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨-, h2⟩, h3, -⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1, by linarith⟩
  rw [h]
  exact isPreconnected_Ioo.connectedComponentIn ⟨by norm_num, by norm_num⟩

/-- Its frontier is `{-1/5, 1/10}`. -/
theorem frontier_component₀₂ :
    frontier (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) = {-(1 / 5), 1 / 10} := by
  rw [component₀₂, frontier_Ioo (by norm_num)]

/-- **The failing pair.** `(]-1/2, 1/10[, mark (1/2))` and `(]-1/5, 1/5[, mark (1/5))` are
developments, neither maximal, `U₂ ⊄ U₀`; `p = 1/10` is a frontier point in `U₂` of the component
`A` of `U₀ ∩ U₂` through `0`, spacelike in `U₂` relative to `{0}` (the future form); the geometric
restart fails at `p` (at `V = U₂`, where `V ∩ U₀ ⊆ A`: the glued causality is the spacelike line,
and `U₀ ∪ O ∋ -1/4` for every `O`), so the slice restart of the pair fails. -/
theorem not_gluedRestartAt_pair :
    IsDevelopment sol82 cauSep {0} dom₀ (mark (1 / 2)) ∧
    IsDevelopment sol82 cauSep {0} dom₂ (mark (1 / 5)) ∧
    ¬ IsMaximalDevelopment sol82 cauSep {0} dom₀ (mark (1 / 2)) ∧
    ¬ IsMaximalDevelopment sol82 cauSep {0} dom₂ (mark (1 / 5)) ∧
    ¬ dom₂ ≤ dom₀ ∧
    (1 / 10 : ℝ) ∈ frontier (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) ∩ dom₂ ∧
    (cauSep (mark (1 / 5))).IsSpacelikeBoundaryPoint dom₂ {0}
      (frontier (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0)) (1 / 10) ∧
    ¬ GluedRestartAt cauSep {0} dom₀ dom₂ (mark (1 / 2)) (mark (1 / 5))
      (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) (1 / 10) ∧
    ¬ (cauSep (mark (1 / 5))).SliceRestart dom₂ {0}
      (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) dom₂
      (GluedRestartAt cauSep {0} dom₀ dom₂ (mark (1 / 2)) (mark (1 / 5))
        (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0)) := by
  have hp : (1 / 10 : ℝ) ∈ frontier (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) ∩ dom₂ :=
    ⟨by rw [frontier_component₀₂]; exact Or.inr rfl, mem_dom₂.2 ⟨by norm_num, by norm_num⟩⟩
  have hsp : (cauSep (mark (1 / 5))).IsSpacelikeBoundaryPoint dom₂ {0}
      (frontier (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0)) (1 / 10) := by
    rw [cauSep_mark ⟨by norm_num, by norm_num⟩, frontier_component₀₂]
    have hsub : ∀ {x y : ℝ}, -(1 / 5) < x → y < 1 / 5 → Icc x y ⊆ (dom₂ : Set ℝ) :=
      fun hx hy => Icc_subset_Ioo hx hy
    refine Or.inl ?_
    ext z
    simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
      mem_singleton_iff, exists_eq_left, mem_insert_iff, timelikeLine_le]
    constructor
    · rintro ⟨⟨-, hz | hz⟩, h0z, -⟩
      · rw [hz] at h0z; norm_num at h0z
      · exact hz
    · rintro rfl
      exact ⟨⟨⟨le_rfl, hsub (by norm_num) (by norm_num)⟩, Or.inr rfl⟩, by norm_num,
        hsub (by norm_num) (by norm_num)⟩
  have hng : ¬ GluedRestartAt cauSep {0} dom₀ dom₂ (mark (1 / 2)) (mark (1 / 5))
      (connectedComponentIn ((dom₀ : Set ℝ) ∩ dom₂) 0) (1 / 10) := by
    intro h
    obtain ⟨O, -, -, hO⟩ := h dom₂ (dom₂.isOpen.mem_nhds hp.2) subset_rfl (fun x hx => by
      rw [component₀₂]
      exact ⟨(mem_dom₂.1 hx.1).1, (mem_dom₀.1 hx.2).2⟩)
    have hO' : spacelikeLine.IsCauchySurfaceOn (dom₀ ⊔ O) {0} := by
      have h' := cauSep_glue₀₂
      rw [glue₀₂] at h'
      rw [h'] at hO
      exact hO
    have hmem : (-(1 / 4) : ℝ) ∈ ((dom₀ ⊔ O : Opens ℝ) : Set ℝ) :=
      (le_sup_left : dom₀ ≤ dom₀ ⊔ O) (mem_dom₀.2 ⟨by norm_num, by norm_num⟩)
    have h0 := spacelikeLine_subset_of_isCauchySurfaceOn hO' hmem
    rw [mem_singleton_iff] at h0
    norm_num at h0
  have hhalf : (1 / 2 : ℝ) ∈ ersWitnessIoo := show (1 / 2 : ℝ) ∈ Ioo (-1) 1 by
    constructor <;> norm_num
  refine ⟨isDevelopment_dom₀, isDevelopment_dom₂, fun h => ?_, fun h => ?_, fun h => ?_, hp, hsp,
    hng, fun h => hng (h _ hp hsp)⟩
  · have := h.2 ersWitnessIoo id isDevelopment_ersWitnessIoo_sep
      ⟨isDevelopment_dom₀.solves.1, isDevelopment_dom₀.solves.2⟩ hhalf
    norm_num [mem_dom₀] at this
  · have := h.2 ersWitnessIoo id isDevelopment_ersWitnessIoo_sep
      ⟨isDevelopment_dom₂.solves.1, isDevelopment_dom₂.solves.2⟩ hhalf
    norm_num [mem_dom₂] at this
  · have := h (mem_dom₂.2 (show (3 / 20 : ℝ) ∈ Ioo (-(1 / 5)) (1 / 5) by
      constructor <;> norm_num))
    norm_num [mem_dom₀] at this

/-! ## 4. The separation -/

/-- **ERS Thm 4.82's uniform restart is not implied by the conclusion** (`ersthm:ThmNotBlocking`,
unmarked): at `sol82`, `cauSep`, `S = {0}`, `s₀ = 0`, `U₁ = ]-1, 1[`, `u₁ = id`, every hypothesis
of `ers_theorem_4_82_solution_of_restarts` and `ers_theorem_4_82_solution_of_restarts_isCausal`
but `hrestart` holds (in the order: `hloc`, `hglue`, `hres`, `hs₀`, `hmax`, `honesided`,
`hconn`, `hG`, `hT`, `hcaus`, `hsplit`, `hJm`, `hJp`, `hK`, `hSclosed`, `hagree`), their
conclusion holds, and `hrestart` fails (at the pair of `not_gluedRestartAt_pair`). -/
theorem restart_separation :
    SolutionLocal sol82 ∧ SolutionsGlue sol82 ∧ SolutionRestricts sol82 ∧
    (0 : ℝ) ∈ ({0} : Set ℝ) ∧
    IsMaximalDevelopment sol82 cauSep {0} ersWitnessIoo id ∧
    OneSidedBoundary ersWitnessIoo (closure ({0} : Set ℝ)) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → IsPreconnected (U : Set ℝ)) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → (cauSep u).GloballyHyperbolicOn U) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → (cauSep u).TarentinOn U) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u →
      ∀ ⦃x y : ℝ⦄, (cauSep u).le U x y → (cauSep u).le U y x → x = y) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → (cauSep u).SplitBy U {0}) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u →
      ∀ x ∈ U, closure ((cauSep u).Jminus U {x}) ∩ U ⊆ (cauSep u).Jminus U {x}) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u →
      ∀ x ∈ U, closure ((cauSep u).Jplus U {x}) ∩ U ⊆ (cauSep u).Jplus U {x}) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → (cauSep u).CompactSlabs U {0}) ∧
    (∀ U u, IsDevelopment sol82 cauSep {0} U u → closure ({0} : Set ℝ) ∩ U ⊆ {0}) ∧
    (∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ →
      EqOn id u₂ (connectedComponentIn ((ersWitnessIoo : Set ℝ) ∩ U₂) 0)) ∧
    (∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂) ∧
    ¬ (∀ U₀ u₀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₀ u₀ →
        IsDevelopment sol82 cauSep {0} U₂ u₂ →
        (cauSep u₂).SliceRestart U₂ {0} (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0) U₂
          (GluedRestartAt cauSep {0} U₀ U₂ u₀ u₂
            (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0))) := by
  obtain ⟨h₀, h₂, -, -, -, -, -, -, hfail⟩ := not_gluedRestartAt_pair
  exact ⟨sol82_local, sol82_glue, sol82_restricts, mem_singleton 0,
    isMaximalDevelopment_ersWitnessIoo_sep, honesided82, hconn_sep, hG_sep, hT_sep,
    fun U u h => (hG_sep U u h).1,
    fun _ _ h => splitBy_of_t1_secondCountable h.cauchy,
    fun U u h => (hG_sep U u h).closure_Jminus_inter_subset (hT_sep U u h),
    fun U u h => (hG_sep U u h).closure_Jplus_inter_subset (hT_sep U u h),
    fun U u h => (hG_sep U u h).compactSlabs_singleton 0,
    fun _ _ _ => by rw [closure_singleton]; exact inter_subset_left,
    fun _ _ h₂ _ hx => (h₂.solves.2 (connectedComponentIn_subset _ _ hx).2).symm,
    fun _ _ h => ⟨h.solves.1, fun _ hx => (h.solves.2 hx).symm⟩,
    fun h => hfail (h _ _ _ _ h₀ h₂)⟩

/-- **The conjuncts are the forms' binders**: the two uniform forms, applied to the first
sixteen conjuncts of `restart_separation`, typecheck, and take `hrestart` (written as in the
last conjunct) to the conclusion. A mechanical check, not a new fact. -/
theorem restart_separation_forms :
    ((∀ U₀ u₀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₀ u₀ →
        IsDevelopment sol82 cauSep {0} U₂ u₂ →
        (cauSep u₂).SliceRestart U₂ {0} (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0) U₂
          (GluedRestartAt cauSep {0} U₀ U₂ u₀ u₂
            (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0))) →
      ∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂) ∧
    ((∀ U₀ u₀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₀ u₀ →
        IsDevelopment sol82 cauSep {0} U₂ u₂ →
        (cauSep u₂).SliceRestart U₂ {0} (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0) U₂
          (GluedRestartAt cauSep {0} U₀ U₂ u₀ u₂
            (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0))) →
      ∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂) := by
  obtain ⟨hloc, hglue, hres, hs₀, hmax, honesided, hconn, hG, hT, hcaus, hsplit, hJm, hJp, hK,
    hSclosed, hagree, -, -⟩ := restart_separation
  exact ⟨ers_theorem_4_82_solution_of_restarts hloc hglue hres hs₀ hmax honesided hconn hG hT
      hsplit hK hSclosed hagree,
    ers_theorem_4_82_solution_of_restarts_isCausal hloc hglue hres hs₀ hmax honesided hconn hcaus
      hsplit hJm hJp hK hSclosed hagree⟩

/-- **The paper's shape applies to the model**: the fixed-`U₁` restart of
`ers_theorem_4_82_solution` at `]-1, 1[` holds (vacuously, every development lying in `]-1, 1[`:
`ers_theorem_4_82_solution_hstep_of_le`), so that form, unlike the uniform ones, applies here. -/
theorem hstep_solution :
    ∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ →
      (cauSep u₂).SliceRestart U₂ {0} (connectedComponentIn ((ersWitnessIoo : Set ℝ) ∩ U₂) 0)
        U₂ (GluedRestartAt cauSep {0} ersWitnessIoo U₂ id u₂
          (connectedComponentIn ((ersWitnessIoo : Set ℝ) ∩ U₂) 0)) :=
  ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn_sep fun _ _ h => h.solves.1

/-- **`ers_theorem_4_82_solution` at the model**: every hypothesis discharged, its `hstep` by
`hstep_solution`. -/
theorem cauSep_ers_theorem_4_82_solution :
    ∀ U₂ u₂, IsDevelopment sol82 cauSep {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ := by
  obtain ⟨hloc, hglue, hres, hs₀, hmax, honesided, hconn, -, -, hcaus, hsplit, hJm, hJp, hK,
    hSclosed, hagree, -, -⟩ := restart_separation
  exact ers_theorem_4_82_solution hloc hglue hres hs₀ hmax honesided hconn hcaus hsplit hJm hJp hK
    hSclosed hagree hstep_solution

/-- **Disclosed: the model's causality does not follow the solution.** `mark (1/5)` and the glued
function agree on `]-1/5, 1/5[`, where `0 ≤ 1/10` for the timelike line and not for the spacelike
line. -/
theorem not_causalityFollows_cauSep : ¬ CausalityFollows cauSep := by
  intro h
  have heq : EqOn (mark (1 / 5)) glue₀₂ dom₂ := fun x hx => by
    rw [mark_of_mem (mem_dom₂.1 hx)]
    by_cases hx₀ : x ∈ Ioo (-(1 / 2) : ℝ) (1 / 10)
    · exact (glue₀₂_of_mem hx₀).symm
    · rw [glue₀₂_of_notMem hx₀, mark_of_mem (mem_dom₂.1 hx)]
  have hiff := h heq dom₂ le_rfl 0 (1 / 10)
  rw [cauSep_mark ⟨by norm_num, by norm_num⟩, cauSep_glue₀₂, timelikeLine_le,
    spacelikeLine_le] at hiff
  have := (hiff.1 ⟨by norm_num, Icc_subset_Ioo (by norm_num) (by norm_num)⟩).1
  norm_num at this

end Ers482Separation

end Causal
