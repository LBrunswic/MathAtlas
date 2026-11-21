import Causal.Model.EAlphaCauchy
import Causal.SingularGeroch
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Admissible measures at the models `E_κ`, `κ > 0`: one finite measure in the class of `λ₃`, admissible in the past and in the future

Target `T-ett-measures-ealpha` (no `sorry`). Cited, **unmarked** (SCOPE (a)):
`prop:mesure_admissible` — `ETT.tex:1726`. The proposition is about every strongly causal
`E_{≥0}`-manifold; here the model half of its proof, hypothesis (i) at `E_κ = ℝ × C_κ`, `κ > 0`
(`massive κ`), is proved, and `ModelMeasures` is discharged at `E_κ`.

> On $\mass{\kappa}$ with $\kappa>0$ the Lebesgue measure $\lambda_3$ of $\RR^3$ satisfies
> properties $1$, $3$ and $4$ in the past and in the future. (`ETT.tex:1736–1737`)

> Restricted to the relatively compact $\U_p$ these measures are finite, so property $2$ holds too,
> and Lemma \ref{lem:restriction_convexe} turns properties $3$ and $4$ of the model into properties
> $3$ and $4$ of $\U_p$. (`ETT.tex:1741–1743`)

> Let $M$ be a strongly causal $\mass{\geq 0}$-manifold. Then $M$ carries a measure $\mu_-$
> admissible in the past and a measure $\mu_+$ admissible in the future. (`ETT.tex:1726–1727`)

> One cannot ask for admissibility in the past and in the future at once as soon as the spacetime
> carries a BTZ line, and property $4$ is the obstruction. (`ETT.tex:1715–1716`)

## What is proved (no `sorry`)

* **Every static `ℝ × X`** (`staticCausality X`, `X` a geodesic metric space):
  `MinkowskiMeasure`'s reduction verbatim (`static_mesure_dieckmann_of`); the local form of
  property 3. (`static_pos_past_inter`, `static_pos_future_inter`: `(J⁻(q) ∖ J⁻(p)) ∩ W` contains a
  non-empty open set for every open `W ∋ q`); **null frontiers** by `ConeNull`'s vertical sections:
  for `ν` any s-finite measure on `X`, the frontier of any `≪`-past or `≪`-future set, open or not,
  is `dt ⊗ ν`-null (`static_prod_frontier_of_past`, `_of_future`); the class result
  (`static_admissible_of_equiv`: `X` σ-compact, `ν` positive on open sets, every finite `μ` with
  the null sets of `dt ⊗ ν` is admissible in the past and in the future); restriction to a causally
  convex open set (`static_admissiblePastOn_restrict_of`, `…FutureOn…`); existence
  (`static_exists_admissible_past_future`), cross-checked on `ℝ^{1,n}`
  (`minkowski_exists_admissible_past_future`).
* **At `E_κ`**: the Borel σ-algebra of `C_κ`; `coneMeasure κ`, the image of `dr ⊗ dθ` on
  `]0, ∞[ × ℝ/κℤ` under `Cone.polar` (s-finite, positive on open sets, finite on compact sets,
  null at the apex); `lam3 κ = dt ⊗ coneMeasure κ`. **The sentence `ETT.tex:1736–1737` as
  printed**: `λ₃` satisfies 1., 3., 4. in the past (`lam3_past`) and in the future
  (`lam3_future`); 2. fails (`lam3_univ`), hence the paper's restriction. Every finite measure
  with the null sets of `λ₃` is admissible in the past and in the future (`admissible_of_equiv`);
  `muE κ = (lam3 κ).toFinite` is one, so **one measure does both**
  (`exists_admissible_past_future`, against `rem:mesure_unilaterale` at `E₀`); `modelMeasures`
  (`U = E_κ`) and `mesure_admissible`.
* **The restricted form** (`ETT.tex:1741–1743`), through the local form of property 3.
  (`pos_past_inter`, `pos_future_inter`): `admissiblePastOn_restrict_of`,
  `admissibleFutureOn_restrict_of`, `admissibleOn_restrict` (`μ_κ` on every causally convex open
  set), `lam3_admissibleOn` (`λ₃` on every relatively compact one), `paper_measures_local` (such a
  `U_p` in every neighbourhood), `modelMeasures_local`.
* **Readings and the planner's route** (SCOPE (b), (c)): `lam3Riem_equiv`,
  `admissible_of_equiv_riem`; `map_polar_apex_pos`, `not_absolutelyContinuous_map_polar`,
  `exists_admissible_charging_singLine`. Non-vacuity at `κ = π`, `κ = 4π`: `nonvacuous`,
  `nonvacuous_local`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` a strongly causal `E_{≥0}`-manifold (l.1726) | ⚠ strengthened: `M = E_κ`, `κ > 0` (instance); strongly causal there (`massive_stronglyCausal`), used only in its open form by `paper_measures_local`; `modelMeasures`, `mesure_admissible` use nothing |
| `λ₃`, "the Lebesgue measure of `ℝ³`" (l.1737) | read: `dt ⊗ dr dθ` in cylindrical coordinates (SCOPE (c)); every finite measure in its class is admissible |
| properties 1., 3., 4. "in the past and in the future" (l.1737) | ✓ carried (`lam3_past`, `lam3_future`), for one measure |
| `μ₋`, `μ₊` (l.1727) | ✓ carried, stronger: one finite measure for both (`exists_admissible_past_future`) |
| "relatively compact `U_p`, causally convex" (l.1734–1735, 1741) | ✓ carried (`lam3_admissibleOn`, `paper_measures_local`); `modelMeasures` takes `U = E_κ` with the finite `μ_κ` |
| `lem:restriction_convexe` for 3. and 4. (l.1742–1743) | ✓ for 4.; 3. through its local form (SCOPE (d)) |

## SCOPE (disclosed)

* **(a) Instance only, nothing marked.** `prop:mesure_admissible` is about every strongly causal
  `E_{≥0}`-manifold; it waits on `ModelMeasures` for every such manifold (T-ett-measures-manifolds,
  which restricts these measures through charts) and on T-ett-singular-sfa.
* **(b) The planner's route.** (1) The reduction is verbatim. (2) The vertical-section argument
  needs neither `P` open nor `ν` related to Lebesgue measure: `dt ⊗ ν`, `ν` s-finite, and only
  `dist(x, y.2) < y.1 − t ⇒ (t, x) ≪ y` with `I⁻(y)` open. (3) A Gaussian in `r` over all of
  `ℝ`, pushed by `Cone.polar` (onto, so `Continuous.isOpenPosMeasure_map` applies), charges the
  apex (`map_polar_apex_pos`), so its product charges the singular line and is **not** in the
  class of `λ₃` (`not_absolutelyContinuous_map_polar`); it is admissible nonetheless
  (`exists_admissible_charging_singLine`). Restricted to `r > 0`, `polar` is no longer onto its
  support and that lemma does not apply; `coneMeasure_pos` argues directly. `Measure.toFinite`
  replaces the Gaussian weights.
* **(c) Reading of `λ₃`.** `E_κ`, `κ ≠ 2π`, has no Cartesian coordinates. Read: `dt dr dθ`. The
  Riemannian volume `dt ⊗ r dr dθ` has the same null sets (`lam3Riem_equiv`), and so has (by hand,
  not formalized) the pull-back of Lebesgue measure by `(t, r, θ) ↦ (t, r e^{2πiθ/κ})`, which is
  `(2π/κ) dt ⊗ r dr dθ`. Properties 1.–4. see a measure through its null sets, its positivity
  on open sets and (for `U_p`) its finiteness on compact sets, so the reading is harmless.
* **(d) Property 3. through `lem:restriction_convexe`** needs the local form
  (`static_pos_past_inter`): as at `E₀` (`E0.pos_past_inter`), the mass of `J⁻(q) ∖ J⁻(p)` must lie
  inside `U_p`, near `q`.
* **(e) Instances.** `MeasurableSpace (Cone κ)` is the Borel σ-algebra, declared here
  (`instMeasurableSpaceCone`); no other module declares one.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Templates:
`Causal.MinkowskiMeasure`, `Causal.Flat.Geroch.ConeNull`, `Causal.Port.MeasuresE0`.
-/

namespace Causal

open Set Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace MeasuresEAlpha

/-! ### Static spacetimes `ℝ × X` -/

section Static

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

/-- **The reduction of `minkowski_mesure_dieckmann_of`, for every static `ℝ × X`**, with the same
proof: a finite regular measure, positive on non-empty open sets, which does not charge the
frontier of any `I⁻(A)` or `I⁺(A)`, is admissible in the past and in the future. -/
theorem static_mesure_dieckmann_of [MeasurableSpace X] {μ : Measure (ℝ × X)} (hreg : μ.Regular)
    (hfin : μ univ < ⊤) (hpos : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ A : Set (ℝ × X), μ (frontier ((staticCausality X).Iminus ⊤ A)) = 0 ∧
      μ (frontier ((staticCausality X).Iplus ⊤ A)) = 0) :
    (staticCausality X).AdmissiblePast μ ∧ (staticCausality X).AdmissibleFuture μ := by
  refine ⟨⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jminus_diff hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (staticCausality.Jminus_diff_Kminus_subset_frontier A) (hnull A).1
  · obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jplus_diff hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (staticCausality.Jplus_diff_Kplus_subset_frontier A) (hnull A).2

/-- **Property 3. in the past, local form**: for `p ≤ q`, `p ≠ q`, the set `J⁻(q) ∖ J⁻(p)` contains
a non-empty open set inside every open `W ∋ q` (`q ∈ cl I⁻(q)`, `J⁻(p)` closed, `q ∉ J⁻(p)`). -/
theorem static_exists_isOpen_subset_Jminus_diff_inter {p q : ℝ × X}
    (hpq : (staticCausality X).le ⊤ p q) (hne : p ≠ q) {W : Set (ℝ × X)} (hW : IsOpen W)
    (hqW : q ∈ W) : ∃ O : Set (ℝ × X), IsOpen O ∧ O.Nonempty ∧
      O ⊆ ((staticCausality X).Jminus ⊤ {q} \ (staticCausality X).Jminus ⊤ {p}) ∩ W := by
  have hq : q ∉ (staticCausality X).Jminus ⊤ {p} := fun h =>
    hne (staticCausality.isCausal hpq (by simpa using h))
  have hcl : q ∈ closure ((staticCausality X).Iminus ⊤ {q}) := by
    rw [staticCausality.closure_Iminus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
  have hO : IsOpen (((staticCausality X).Jminus ⊤ {p})ᶜ ∩ W) :=
    (staticCausality.isClosed_Jminus_top p).isOpen_compl.inter hW
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ hO ⟨hq, hqW⟩
  exact ⟨_, Causality.isOpen_Iminus.inter hO, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨⟨Causality.Iminus_subset_Jminus hw.1, hw.2.1⟩, hw.2.2⟩⟩

/-- **Property 3. in the future, local form**: `J⁺(p) ∖ J⁺(q)` contains a non-empty open set
inside every open `W ∋ p`. -/
theorem static_exists_isOpen_subset_Jplus_diff_inter {p q : ℝ × X}
    (hpq : (staticCausality X).le ⊤ p q) (hne : p ≠ q) {W : Set (ℝ × X)} (hW : IsOpen W)
    (hpW : p ∈ W) : ∃ O : Set (ℝ × X), IsOpen O ∧ O.Nonempty ∧
      O ⊆ ((staticCausality X).Jplus ⊤ {p} \ (staticCausality X).Jplus ⊤ {q}) ∩ W := by
  have hp : p ∉ (staticCausality X).Jplus ⊤ {q} := fun h =>
    hne (staticCausality.isCausal hpq (by simpa using h))
  have hcl : p ∈ closure ((staticCausality X).Iplus ⊤ {p}) := by
    rw [staticCausality.closure_Iplus]; simpa using (staticCausality X).le_refl (U := ⊤) trivial
  have hO : IsOpen (((staticCausality X).Jplus ⊤ {q})ᶜ ∩ W) :=
    (staticCausality.isClosed_Jplus_top q).isOpen_compl.inter hW
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ hO ⟨hp, hpW⟩
  exact ⟨_, Causality.isOpen_Iplus.inter hO, ⟨z, hz2, hz1⟩,
    fun w hw => ⟨⟨Causality.Iplus_subset_Jplus hw.1, hw.2.1⟩, hw.2.2⟩⟩

/-- **Property 3. in the past, local form, for a measure**: positive on non-empty open sets, it
charges `(J⁻(q) ∖ J⁻(p)) ∩ W` for every open `W ∋ q` (the analogue of `E0.pos_past_inter`). -/
theorem static_pos_past_inter [MeasurableSpace X] {μ : Measure (ℝ × X)}
    (hμ : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O) {W : Set (ℝ × X)} (hW : IsOpen W)
    {p q : ℝ × X} (hqW : q ∈ W) (hpq : (staticCausality X).le ⊤ p q) (hne : p ≠ q) :
    0 < μ (((staticCausality X).Jminus ⊤ {q} \ (staticCausality X).Jminus ⊤ {p}) ∩ W) := by
  obtain ⟨O, hO, hne', hsub⟩ := static_exists_isOpen_subset_Jminus_diff_inter hpq hne hW hqW
  exact (hμ O hO hne').trans_le (measure_mono hsub)

/-- **Property 3. in the future, local form, for a measure** (the analogue of
`E0.pos_future_inter`). -/
theorem static_pos_future_inter [MeasurableSpace X] {μ : Measure (ℝ × X)}
    (hμ : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O) {W : Set (ℝ × X)} (hW : IsOpen W)
    {p q : ℝ × X} (hpW : p ∈ W) (hpq : (staticCausality X).le ⊤ p q) (hne : p ≠ q) :
    0 < μ (((staticCausality X).Jplus ⊤ {p} \ (staticCausality X).Jplus ⊤ {q}) ∩ W) := by
  obtain ⟨O, hO, hne', hsub⟩ := static_exists_isOpen_subset_Jplus_diff_inter hpq hne hW hpW
  exact (hμ O hO hne').trans_le (measure_mono hsub)

/-- **Each vertical line `t ↦ (t, x)` meets the frontier of a `≪`-past set at most once**: if
`t < s` both lie on it, some `y ∈ P` near `(s, x)` has `(t, x) ≪ y`, and `I⁻(y) ⊆ P` puts `(t, x)`
in the interior of `P`. -/
theorem static_frontier_section_subsingleton_of_past {P : Set (ℝ × X)}
    (hP : ∀ y ∈ P, ∀ z, (staticCausality X).lt ⊤ z y → z ∈ P) (x : X) :
    {t : ℝ | (t, x) ∈ frontier P}.Subsingleton := by
  have key : ∀ t s : ℝ, t < s → (t, x) ∈ frontier P → (s, x) ∈ frontier P → False := by
    intro t s hts ht hs
    have hU : IsOpen {y : ℝ × X | dist y.2 x < y.1 - t} :=
      isOpen_lt (continuous_snd.dist continuous_const) (continuous_fst.sub continuous_const)
    have hsU : ((s, x) : ℝ × X) ∈ {y : ℝ × X | dist y.2 x < y.1 - t} := by simpa using hts
    obtain ⟨y, hyt, hyP⟩ := mem_closure_iff.1 (frontier_subset_closure hs) _ hU hsU
    have hlt : (staticCausality X).lt ⊤ ((t, x) : ℝ × X) y := by
      rw [staticCausality.lt_top_iff, dist_comm]; exact hyt
    exact ht.2 (interior_maximal (fun z hz => hP y hyP z hz)
      ((staticCausality X).isOpen_lt_left ⊤ y) hlt)
  intro t ht s hs
  rcases lt_trichotomy t s with h | h | h
  · exact (key t s h ht hs).elim
  · exact h
  · exact (key s t h hs ht).elim

/-- **Each vertical line meets the frontier of a `≪`-future set at most once.** -/
theorem static_frontier_section_subsingleton_of_future {P : Set (ℝ × X)}
    (hP : ∀ y ∈ P, ∀ z, (staticCausality X).lt ⊤ y z → z ∈ P) (x : X) :
    {t : ℝ | (t, x) ∈ frontier P}.Subsingleton := by
  have key : ∀ t s : ℝ, t < s → (t, x) ∈ frontier P → (s, x) ∈ frontier P → False := by
    intro t s hts ht hs
    have hU : IsOpen {y : ℝ × X | dist y.2 x < s - y.1} :=
      isOpen_lt (continuous_snd.dist continuous_const) (continuous_const.sub continuous_fst)
    have htU : ((t, x) : ℝ × X) ∈ {y : ℝ × X | dist y.2 x < s - y.1} := by simpa using hts
    obtain ⟨y, hys, hyP⟩ := mem_closure_iff.1 (frontier_subset_closure ht) _ hU htU
    have hlt : (staticCausality X).lt ⊤ y ((s, x) : ℝ × X) := by
      rw [staticCausality.lt_top_iff]; exact hys
    exact hs.2 (interior_maximal (fun z hz => hP y hyP z hz)
      ((staticCausality X).isOpen_lt_right ⊤ y) hlt)
  intro t ht s hs
  rcases lt_trichotomy t s with h | h | h
  · exact (key t s h ht hs).elim
  · exact h
  · exact (key s t h hs ht).elim

/-- **A measurable set with subsingleton vertical sections is `dt ⊗ ν`-null** (Fubini–Tonelli,
a point of `ℝ` being null), for every s-finite `ν`. -/
theorem prod_eq_zero_of_section_subsingleton {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] {S : Set (ℝ × Y)} (hS : MeasurableSet S)
    (hsec : ∀ y : Y, {t : ℝ | (t, y) ∈ S}.Subsingleton) :
    ((volume : Measure ℝ).prod ν) S = 0 := by
  rw [Measure.prod_apply_symm hS]
  have : ∀ y : Y, (volume : Measure ℝ) ((fun t : ℝ => (t, y)) ⁻¹' S) = 0 := fun y =>
    (hsec y).measure_zero _
  simp only [this, lintegral_zero]

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **The frontier of a `≪`-past set is `dt ⊗ ν`-null**, for every s-finite `ν` on `X`. -/
theorem static_prod_frontier_of_past (ν : Measure X) [SFinite ν] {P : Set (ℝ × X)}
    (hP : ∀ y ∈ P, ∀ z, (staticCausality X).lt ⊤ z y → z ∈ P) :
    ((volume : Measure ℝ).prod ν) (frontier P) = 0 :=
  prod_eq_zero_of_section_subsingleton ν isClosed_frontier.measurableSet
    (static_frontier_section_subsingleton_of_past hP)

/-- **The frontier of a `≪`-future set is `dt ⊗ ν`-null.** -/
theorem static_prod_frontier_of_future (ν : Measure X) [SFinite ν] {P : Set (ℝ × X)}
    (hP : ∀ y ∈ P, ∀ z, (staticCausality X).lt ⊤ y z → z ∈ P) :
    ((volume : Measure ℝ).prod ν) (frontier P) = 0 :=
  prod_eq_zero_of_section_subsingleton ν isClosed_frontier.measurableSet
    (static_frontier_section_subsingleton_of_future hP)

/-- `∂I⁻(A)` is `dt ⊗ ν`-null. -/
theorem static_prod_frontier_Iminus (ν : Measure X) [SFinite ν] (A : Set (ℝ × X)) :
    ((volume : Measure ℝ).prod ν) (frontier ((staticCausality X).Iminus ⊤ A)) = 0 :=
  static_prod_frontier_of_past ν fun _ ⟨a, ha, hya⟩ _ hzy =>
    ⟨a, ha, (staticCausality X).lt_trans hzy hya⟩

/-- `∂I⁺(A)` is `dt ⊗ ν`-null. -/
theorem static_prod_frontier_Iplus (ν : Measure X) [SFinite ν] (A : Set (ℝ × X)) :
    ((volume : Measure ℝ).prod ν) (frontier ((staticCausality X).Iplus ⊤ A)) = 0 :=
  static_prod_frontier_of_future ν fun _ ⟨a, ha, hay⟩ _ hyz =>
    ⟨a, ha, (staticCausality X).lt_trans hay hyz⟩

end Static

section StaticBorel

variable {X : Type*} [MetricSpace X] [GeodesicSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- **The class result on a static `ℝ × X`**: for `ν` s-finite and positive on open sets, every
finite measure with the null sets of `dt ⊗ ν` is admissible in the past and in the future. -/
theorem static_admissible_of_equiv (ν : Measure X) [SFinite ν] [ν.IsOpenPosMeasure]
    {μ : Measure (ℝ × X)} [IsFiniteMeasure μ] (h₁ : μ ≪ (volume : Measure ℝ).prod ν)
    (h₂ : (volume : Measure ℝ).prod ν ≪ μ) :
    (staticCausality X).AdmissiblePast μ ∧ (staticCausality X).AdmissibleFuture μ := by
  have hpos : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O := fun O hO hne =>
    pos_iff_ne_zero.2 fun h0 => (hO.measure_pos ((volume : Measure ℝ).prod ν) hne).ne' (h₂ h0)
  exact static_mesure_dieckmann_of inferInstance (measure_lt_top μ univ) hpos fun A =>
    ⟨h₁ (static_prod_frontier_Iminus ν A), h₁ (static_prod_frontier_Iplus ν A)⟩

/-- **Restriction in the past**: a measure absolutely continuous w.r.t. `dt ⊗ ν` and positive on
non-empty open sets, restricted to a causally convex open `V` on which it is finite, is admissible
in the past on `V`; property 3. through `static_pos_past_inter`, property 4. through
`lem:restriction_convexe`. -/
theorem static_admissiblePastOn_restrict_of (ν : Measure X) [SFinite ν] {μ : Measure (ℝ × X)}
    {V : Opens (ℝ × X)} [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ (volume : Measure ℝ).prod ν)
    (hO : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O)
    (hV : (staticCausality X).CausallyConvexIn (V : Set (ℝ × X)) ⊤) :
    (staticCausality X).AdmissiblePastOn V (μ.restrict V) := by
  have hVm : MeasurableSet (V : Set (ℝ × X)) := V.isOpen.measurableSet
  have hcac := (staticCausality.causallyArcConnected (X := X))
  refine ⟨?_, inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A hA => ?_⟩
  · rw [Measure.restrict_apply' hVm, compl_inter_self, measure_empty]
  · have hpV : p ∈ V := (staticCausality X).le_mem_left hpq
    have hqV : q ∈ V := (staticCausality X).le_mem_right hpq
    rw [(Causality.restriction_convexe_past hcac hV (singleton_subset_iff.2 hqV)).1,
      (Causality.restriction_convexe_past hcac hV (singleton_subset_iff.2 hpV)).1,
      Measure.restrict_apply' hVm]
    refine (static_pos_past_inter hO V.isOpen hqV ((staticCausality X).le_mono le_top hpq)
      hne).trans_le (measure_mono ?_)
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h3⟩, fun h => h2 h.1⟩, h3⟩
  · rw [(Causality.restriction_convexe_past hcac hV hA).1,
      (Causality.restriction_convexe_past hcac hV hA).2.2]
    refine le_antisymm (le_trans (Measure.restrict_le_self _) ?_) zero_le
    refine (measure_mono ?_).trans (h₁ (measure_mono_null
      (staticCausality.Jminus_diff_Kminus_subset_frontier A) (static_prod_frontier_Iminus ν A))).le
    exact fun x hx => ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩

/-- **Restriction in the future** (as `static_admissiblePastOn_restrict_of`). -/
theorem static_admissibleFutureOn_restrict_of (ν : Measure X) [SFinite ν] {μ : Measure (ℝ × X)}
    {V : Opens (ℝ × X)} [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ (volume : Measure ℝ).prod ν)
    (hO : ∀ O : Set (ℝ × X), IsOpen O → O.Nonempty → 0 < μ O)
    (hV : (staticCausality X).CausallyConvexIn (V : Set (ℝ × X)) ⊤) :
    (staticCausality X).AdmissibleFutureOn V (μ.restrict V) := by
  have hVm : MeasurableSet (V : Set (ℝ × X)) := V.isOpen.measurableSet
  have hcac := (staticCausality.causallyArcConnected (X := X))
  refine ⟨?_, inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A hA => ?_⟩
  · rw [Measure.restrict_apply' hVm, compl_inter_self, measure_empty]
  · have hpV : p ∈ V := (staticCausality X).le_mem_left hpq
    have hqV : q ∈ V := (staticCausality X).le_mem_right hpq
    rw [(Causality.restriction_convexe_future hcac hV (singleton_subset_iff.2 hpV)).1,
      (Causality.restriction_convexe_future hcac hV (singleton_subset_iff.2 hqV)).1,
      Measure.restrict_apply' hVm]
    refine (static_pos_future_inter hO V.isOpen hpV ((staticCausality X).le_mono le_top hpq)
      hne).trans_le (measure_mono ?_)
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h3⟩, fun h => h2 h.1⟩, h3⟩
  · rw [(Causality.restriction_convexe_future hcac hV hA).1,
      (Causality.restriction_convexe_future hcac hV hA).2.2]
    refine le_antisymm (le_trans (Measure.restrict_le_self _) ?_) zero_le
    refine (measure_mono ?_).trans (h₁ (measure_mono_null
      (staticCausality.Jplus_diff_Kplus_subset_frontier A) (static_prod_frontier_Iplus ν A))).le
    exact fun x hx => ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩

/-- **One measure admissible in the past and in the future on a static `ℝ × X`**, as soon as `X`
carries an s-finite measure positive on non-empty open sets: `(dt ⊗ ν).toFinite`. -/
theorem static_exists_admissible_past_future (ν : Measure X) [SFinite ν] [ν.IsOpenPosMeasure] :
    ∃ μ : Measure (ℝ × X),
      (staticCausality X).AdmissiblePast μ ∧ (staticCausality X).AdmissibleFuture μ :=
  ⟨_, static_admissible_of_equiv ν (toFinite_absolutelyContinuous _)
    (absolutelyContinuous_toFinite _)⟩

end StaticBorel

/-- **Cross-check on `ℝ^{1,n}`**: the static theorem with `ν` the Lebesgue measure of `ℝⁿ` gives
`prop:mesure_dieckmann_Lorentz` on Minkowski space (`minkowski_mesure_dieckmann`) a second time,
without `Causal.Flat`. -/
theorem minkowski_exists_admissible_past_future (n : ℕ) :
    ∃ μ : Measure (Minkowski n), (minkowski n).AdmissiblePast μ ∧ (minkowski n).AdmissibleFuture μ :=
  static_exists_admissible_past_future (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-! ### The flat cone `C_κ`: Borel sets and the coordinate measure `dr dθ` -/

/-- The Borel σ-algebra of the cone. -/
noncomputable instance instMeasurableSpaceCone (κ : ℝ) : MeasurableSpace (Cone κ) := borel (Cone κ)

instance instBorelSpaceCone (κ : ℝ) : BorelSpace (Cone κ) := ⟨rfl⟩

variable {κ : ℝ} [Fact (0 < κ)]

/-- **The coordinate measure `dr dθ` of `C_κ`**: the image under `Cone.polar` of Lebesgue measure
on `]0, ∞[` times the Haar measure of `ℝ/κℤ` (total mass `κ`). -/
noncomputable def coneMeasure (κ : ℝ) [Fact (0 < κ)] : Measure (Cone κ) :=
  Measure.map Cone.polar
    (((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure (AddCircle κ)))

instance instSFiniteConeMeasure : SFinite (coneMeasure κ) := by
  unfold coneMeasure; infer_instance

/-- `coneMeasure κ` is positive on non-empty open sets: every one contains `polar (r, θ)` with
`r > 0` near each of its points. -/
theorem coneMeasure_pos {O : Set (Cone κ)} (hO : IsOpen O) (hne : O.Nonempty) :
    0 < coneMeasure κ O := by
  have hpolar : Measurable (Cone.polar (α := κ)) := Cone.continuous_polar.measurable
  have hW : IsOpen (Cone.polar ⁻¹' O ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set (AddCircle κ)))) :=
    (hO.preimage Cone.continuous_polar).inter (isOpen_Ioi.prod isOpen_univ)
  rw [coneMeasure, Measure.map_apply hpolar hO.measurableSet, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (hO.preimage Cone.continuous_polar).measurableSet]
  refine hW.measure_pos _ ?_
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x hx
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  have hr := p.r_nonneg
  refine ⟨(p.r + ε / 2, p.θ), hball ?_, ?_, mem_univ _⟩
  · rw [Metric.mem_ball]
    change dist (Cone.mk (ConePoint.of (p.r + ε / 2) p.θ)) (Cone.mk p) < ε
    rw [Cone.dist_mk, ConePoint.dist_same_dir (p := ConePoint.of (p.r + ε / 2) p.θ) (q := p) rfl,
      ConePoint.of_r (by linarith),
      show p.r + ε / 2 - p.r = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith
  · change 0 < p.r + ε / 2
    linarith

instance instIsOpenPosMeasureConeMeasure : (coneMeasure κ).IsOpenPosMeasure :=
  ⟨fun _ hO hne => (coneMeasure_pos hO hne).ne'⟩

/-- `coneMeasure κ` is finite on the balls about the apex (at most `R · κ`). -/
theorem coneMeasure_closedBall (R : ℝ) : coneMeasure κ (Metric.closedBall Cone.apex R) < ⊤ := by
  have hpolar : Measurable (Cone.polar (α := κ)) := Cone.continuous_polar.measurable
  have hm : MeasurableSet (Cone.polar ⁻¹' Metric.closedBall (Cone.apex : Cone κ) R) :=
    hpolar Metric.isClosed_closedBall.measurableSet
  rw [coneMeasure, Measure.map_apply hpolar Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hm]
  refine (measure_mono (t := Ioc 0 R ×ˢ (univ : Set (AddCircle κ))) ?_).trans_lt ?_
  · rintro ⟨u, θ⟩ ⟨hb, hu, -⟩
    have hu' : (0 : ℝ) < u := hu
    refine ⟨⟨hu', ?_⟩, mem_univ _⟩
    have hrad : Cone.rad (Cone.polar (u, θ)) = u := by
      change Cone.rad (Cone.mk (ConePoint.of u θ)) = u
      rw [Cone.rad_mk, ConePoint.of_r hu'.le]
    rw [mem_preimage, Metric.mem_closedBall, dist_comm] at hb
    have hb' : Cone.rad (Cone.polar (u, θ)) ≤ R := hb
    linarith
  · rw [Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

instance instIsFiniteMeasureOnCompactsConeMeasure : IsFiniteMeasureOnCompacts (coneMeasure κ) :=
  ⟨fun K hK => by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall Cone.apex
    exact (measure_mono hR).trans_lt (coneMeasure_closedBall R)⟩

/-- `coneMeasure κ` does not charge the apex. -/
theorem coneMeasure_apex : coneMeasure κ {Cone.apex} = 0 := by
  have hpolar : Measurable (Cone.polar (α := κ)) := Cone.continuous_polar.measurable
  rw [coneMeasure, Measure.map_apply hpolar (measurableSet_singleton _),
    Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (hpolar (measurableSet_singleton _))]
  refine measure_mono_null (fun x hx => ?_) measure_empty
  obtain ⟨hx1, hx2, -⟩ := hx
  have hx2' : (0 : ℝ) < x.1 := hx2
  have h1 : Cone.rad (Cone.polar x) = 0 := Cone.rad_eq_zero.2 hx1
  change Cone.rad (Cone.mk (ConePoint.of x.1 x.2)) = 0 at h1
  rw [Cone.rad_mk, ConePoint.of_r hx2'.le] at h1
  exact absurd h1 hx2'.ne'

/-! ### `λ₃` on `E_κ` -/

/-- **`λ₃` on `E_κ`**: `dt ⊗ dr dθ`, Lebesgue measure in the cylindrical coordinates. -/
noncomputable def lam3 (κ : ℝ) [Fact (0 < κ)] : Measure (Massive κ) :=
  (volume : Measure ℝ).prod (coneMeasure κ)

instance instSFiniteLam3 : SFinite (lam3 κ) := by unfold lam3; infer_instance

instance instIsOpenPosMeasureLam3 : (lam3 κ).IsOpenPosMeasure := by unfold lam3; infer_instance

instance instIsFiniteMeasureOnCompactsLam3 : IsFiniteMeasureOnCompacts (lam3 κ) := by
  unfold lam3; infer_instance

instance instIsLocallyFiniteMeasureLam3 : IsLocallyFiniteMeasure (lam3 κ) := by
  unfold lam3; infer_instance

omit [Fact (0 < κ)] in
/-- The singular line is `ℝ × {apex}`. -/
theorem singLine_eq_prod : singLine κ = (univ : Set ℝ) ×ˢ ({Cone.apex} : Set (Cone κ)) := by
  ext p; simp [singLine]

/-- **`λ₃` does not charge the singular line.** -/
theorem lam3_singLine : lam3 κ (singLine κ) = 0 := by
  rw [singLine_eq_prod, lam3, Measure.prod_prod, coneMeasure_apex, mul_zero]

/-- `λ₃` is positive on non-empty open sets. -/
theorem lam3_pos {O : Set (Massive κ)} (hO : IsOpen O) (hne : O.Nonempty) : 0 < lam3 κ O :=
  hO.measure_pos _ hne

/-- **`λ₃` is infinite**: property 2. fails, hence the paper's restriction to a relatively
compact `U_p` (`ETT.tex:1741`). -/
theorem lam3_univ : lam3 κ univ = ⊤ := by
  rw [lam3, ← univ_prod_univ, Measure.prod_prod, Real.volume_univ]
  exact ENNReal.top_mul (coneMeasure_pos isOpen_univ ⟨Cone.apex, mem_univ _⟩).ne'

/-- `∂I⁻(A)` is `λ₃`-null. -/
theorem lam3_frontier_Iminus (A : Set (Massive κ)) :
    lam3 κ (frontier ((massive κ).Iminus ⊤ A)) = 0 :=
  static_prod_frontier_Iminus (coneMeasure κ) A

/-- `∂I⁺(A)` is `λ₃`-null. -/
theorem lam3_frontier_Iplus (A : Set (Massive κ)) :
    lam3 κ (frontier ((massive κ).Iplus ⊤ A)) = 0 :=
  static_prod_frontier_Iplus (coneMeasure κ) A

/-- **`λ₃` satisfies properties 1., 3. and 4. in the past** (`ETT.tex:1736–1737`). -/
theorem lam3_past :
    (lam3 κ).Regular ∧
      (∀ ⦃p q : Massive κ⦄, (massive κ).le ⊤ p q → p ≠ q →
        0 < lam3 κ ((massive κ).Jminus ⊤ {q} \ (massive κ).Jminus ⊤ {p})) ∧
      ∀ A : Set (Massive κ), lam3 κ ((massive κ).Jminus ⊤ A \ (massive κ).Kminus ⊤ A) = 0 :=
  ⟨inferInstance, fun _ _ hpq hne => by
    obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jminus_diff hpq hne
    exact (lam3_pos hO hne').trans_le (measure_mono hsub),
   fun A => measure_mono_null (staticCausality.Jminus_diff_Kminus_subset_frontier A)
    (lam3_frontier_Iminus A)⟩

/-- **`λ₃` satisfies properties 1., 3. and 4. in the future** (`ETT.tex:1736–1737`). -/
theorem lam3_future :
    (lam3 κ).Regular ∧
      (∀ ⦃p q : Massive κ⦄, (massive κ).le ⊤ p q → p ≠ q →
        0 < lam3 κ ((massive κ).Jplus ⊤ {p} \ (massive κ).Jplus ⊤ {q})) ∧
      ∀ A : Set (Massive κ), lam3 κ ((massive κ).Jplus ⊤ A \ (massive κ).Kplus ⊤ A) = 0 :=
  ⟨inferInstance, fun _ _ hpq hne => by
    obtain ⟨O, hO, hne', hsub⟩ := staticCausality.exists_isOpen_subset_Jplus_diff hpq hne
    exact (lam3_pos hO hne').trans_le (measure_mono hsub),
   fun A => measure_mono_null (staticCausality.Jplus_diff_Kplus_subset_frontier A)
    (lam3_frontier_Iplus A)⟩

/-- **Every finite measure with the null sets of `λ₃` is admissible in the past and in the
future.** -/
theorem admissible_of_equiv {μ : Measure (Massive κ)} [IsFiniteMeasure μ] (h₁ : μ ≪ lam3 κ)
    (h₂ : lam3 κ ≪ μ) : (massive κ).AdmissiblePast μ ∧ (massive κ).AdmissibleFuture μ :=
  static_admissible_of_equiv (coneMeasure κ) h₁ h₂

/-- **`μ_κ`**: a finite measure with the null sets of `λ₃`. -/
noncomputable def muE (κ : ℝ) [Fact (0 < κ)] : Measure (Massive κ) := (lam3 κ).toFinite

instance instIsFiniteMeasureMuE : IsFiniteMeasure (muE κ) := by unfold muE; infer_instance

/-- `μ_κ` is admissible in the past and in the future. -/
theorem admissible_muE : (massive κ).AdmissiblePast (muE κ) ∧ (massive κ).AdmissibleFuture (muE κ) :=
  admissible_of_equiv (toFinite_absolutelyContinuous _) (absolutelyContinuous_toFinite _)

/-- **One measure on `E_κ` admissible in the past and in the future at once.** -/
theorem exists_admissible_past_future :
    ∃ μ : Measure (Massive κ), (massive κ).AdmissiblePast μ ∧ (massive κ).AdmissibleFuture μ :=
  ⟨muE κ, admissible_muE⟩

/-- **`ModelMeasures` at `E_κ`**, with `U = E_κ` and the one measure `μ_κ` on both sides. -/
theorem modelMeasures : (massive κ).ModelMeasures :=
  ⟨fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, muE κ,
      Causality.admissiblePastOn_top.2 admissible_muE.1⟩,
    fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, muE κ,
      Causality.admissibleFutureOn_top.2 admissible_muE.2⟩⟩

/-- **`prop:mesure_admissible`'s conclusion at `E_κ`** (instance; the label is not marked). -/
theorem mesure_admissible :
    (∃ μ : Measure (Massive κ), (massive κ).AdmissiblePast μ) ∧
      ∃ μ : Measure (Massive κ), (massive κ).AdmissibleFuture μ :=
  ⟨⟨_, admissible_muE.1⟩, ⟨_, admissible_muE.2⟩⟩

/-! ### Restriction to a causally convex open set -/

/-- **Property 3. in the past at `E_κ`, inside an open set `W ∋ q`**, for every measure positive on
non-empty open sets (`E0.pos_past_inter` at `E₀`). -/
theorem pos_past_inter {μ : Measure (Massive κ)}
    (hμ : ∀ O : Set (Massive κ), IsOpen O → O.Nonempty → 0 < μ O) {W : Set (Massive κ)}
    (hW : IsOpen W) {p q : Massive κ} (hqW : q ∈ W) (hpq : (massive κ).le ⊤ p q) (hne : p ≠ q) :
    0 < μ (((massive κ).Jminus ⊤ {q} \ (massive κ).Jminus ⊤ {p}) ∩ W) :=
  static_pos_past_inter hμ hW hqW hpq hne

/-- **Property 3. in the future at `E_κ`, inside an open set `W ∋ p`** (`E0.pos_future_inter`). -/
theorem pos_future_inter {μ : Measure (Massive κ)}
    (hμ : ∀ O : Set (Massive κ), IsOpen O → O.Nonempty → 0 < μ O) {W : Set (Massive κ)}
    (hW : IsOpen W) {p q : Massive κ} (hpW : p ∈ W) (hpq : (massive κ).le ⊤ p q) (hne : p ≠ q) :
    0 < μ (((massive κ).Jplus ⊤ {p} \ (massive κ).Jplus ⊤ {q}) ∩ W) :=
  static_pos_future_inter hμ hW hpW hpq hne

/-- **Restriction in the past at `E_κ`** (`E0.admissiblePastOn_restrict_of` at `E₀`). -/
theorem admissiblePastOn_restrict_of {μ : Measure (Massive κ)} {V : Opens (Massive κ)}
    [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ lam3 κ)
    (hO : ∀ O : Set (Massive κ), IsOpen O → O.Nonempty → 0 < μ O)
    (hV : (massive κ).CausallyConvexIn (V : Set (Massive κ)) ⊤) :
    (massive κ).AdmissiblePastOn V (μ.restrict V) :=
  static_admissiblePastOn_restrict_of (coneMeasure κ) h₁ hO hV

/-- **Restriction in the future at `E_κ`** (`E0.admissibleFutureOn_restrict_of` at `E₀`). -/
theorem admissibleFutureOn_restrict_of {μ : Measure (Massive κ)} {V : Opens (Massive κ)}
    [IsFiniteMeasure (μ.restrict V)] (h₁ : μ ≪ lam3 κ)
    (hO : ∀ O : Set (Massive κ), IsOpen O → O.Nonempty → 0 < μ O)
    (hV : (massive κ).CausallyConvexIn (V : Set (Massive κ)) ⊤) :
    (massive κ).AdmissibleFutureOn V (μ.restrict V) :=
  static_admissibleFutureOn_restrict_of (coneMeasure κ) h₁ hO hV

/-- **`μ_κ` restricted to any causally convex open `V`** is admissible on `V` in the past and in
the future. -/
theorem admissibleOn_restrict {V : Opens (Massive κ)}
    (hV : (massive κ).CausallyConvexIn (V : Set (Massive κ)) ⊤) :
    (massive κ).AdmissiblePastOn V ((muE κ).restrict V) ∧
      (massive κ).AdmissibleFutureOn V ((muE κ).restrict V) := by
  have hpos : ∀ O : Set (Massive κ), IsOpen O → O.Nonempty → 0 < muE κ O := fun _ hO hne =>
    pos_iff_ne_zero.2 fun h0 => (lam3_pos hO hne).ne' (absolutelyContinuous_toFinite _ h0)
  exact ⟨admissiblePastOn_restrict_of (toFinite_absolutelyContinuous _) hpos hV,
    admissibleFutureOn_restrict_of (toFinite_absolutelyContinuous _) hpos hV⟩

/-- **The paper's measure**: `λ₃` restricted to a relatively compact causally convex open `V`. -/
theorem lam3_admissibleOn {V : Opens (Massive κ)}
    (hV : (massive κ).CausallyConvexIn (V : Set (Massive κ)) ⊤)
    (hc : IsCompact (closure (V : Set (Massive κ)))) :
    (massive κ).AdmissiblePastOn V ((lam3 κ).restrict V) ∧
      (massive κ).AdmissibleFutureOn V ((lam3 κ).restrict V) := by
  haveI : IsFiniteMeasure ((lam3 κ).restrict V) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hc.measure_lt_top⟩
  exact ⟨admissiblePastOn_restrict_of Measure.AbsolutelyContinuous.rfl
      (fun _ hO hne => lam3_pos hO hne) hV,
    admissibleFutureOn_restrict_of Measure.AbsolutelyContinuous.rfl
      (fun _ hO hne => lam3_pos hO hne) hV⟩

/-- **Hypothesis (i) of `prop:mesure_dieckmann_topo` at `E_κ`, as the paper's proof gives it**
(`ETT.tex:1734–1743`): every neighbourhood `N` of every point `p` contains a relatively compact
open neighbourhood `U` of `p`, causally convex in `E_κ`, on which `λ₃` restricted to `U` is
admissible in the past and in the future. -/
theorem paper_measures_local (p : Massive κ) {N : Set (Massive κ)} (hN : N ∈ 𝓝 p) :
    ∃ U : Opens (Massive κ), p ∈ U ∧ (U : Set (Massive κ)) ⊆ N ∧
      IsCompact (closure (U : Set (Massive κ))) ∧
      (massive κ).CausallyConvexIn (U : Set (Massive κ)) ⊤ ∧
      (massive κ).AdmissiblePastOn U ((lam3 κ).restrict U) ∧
      (massive κ).AdmissibleFutureOn U ((lam3 κ).restrict U) := by
  obtain ⟨U, hpU, hUN, hU⟩ := massive_stronglyCausalOpen p (N ∩ Metric.ball p 1)
    (inter_mem hN (Metric.ball_mem_nhds p one_pos))
  have hc : IsCompact (closure (U : Set (Massive κ))) :=
    (isCompact_closedBall p 1).of_isClosed_subset isClosed_closure
      ((closure_mono (hUN.trans inter_subset_right)).trans Metric.closure_ball_subset_closedBall)
  exact ⟨U, hpU, hUN.trans inter_subset_left, hc, hU, lam3_admissibleOn hU hc⟩

/-- **The paper's local form of hypothesis (i)** at `E_κ`: every neighbourhood of every point
contains a causally convex open neighbourhood carrying a measure admissible in the past and one
admissible in the future (here one measure, `λ₃` restricted, does both). -/
theorem modelMeasures_local (p : Massive κ) {N : Set (Massive κ)} (hN : N ∈ 𝓝 p) :
    ∃ U : Opens (Massive κ), p ∈ U ∧ (U : Set (Massive κ)) ⊆ N ∧
      (massive κ).CausallyConvexIn (U : Set (Massive κ)) ⊤ ∧
      (∃ ν : Measure (Massive κ), (massive κ).AdmissiblePastOn U ν) ∧
      ∃ ν : Measure (Massive κ), (massive κ).AdmissibleFutureOn U ν := by
  obtain ⟨U, hpU, hUN, -, hU, hpast, hfut⟩ := paper_measures_local p hN
  exact ⟨U, hpU, hUN, hU, ⟨_, hpast⟩, ⟨_, hfut⟩⟩

/-! ### The Riemannian reading `dt ⊗ r dr dθ` -/

/-- The area measure `r dr dθ` of `C_κ`. -/
noncomputable def coneArea (κ : ℝ) [Fact (0 < κ)] : Measure (Cone κ) :=
  Measure.map Cone.polar
    ((((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun r => ENNReal.ofReal r).prod
      (volume : Measure (AddCircle κ)))

instance instSFiniteConeArea : SFinite (coneArea κ) := by unfold coneArea; infer_instance

/-- The Riemannian volume `dt ⊗ r dr dθ` of `E_κ`. -/
noncomputable def lam3Riem (κ : ℝ) [Fact (0 < κ)] : Measure (Massive κ) :=
  (volume : Measure ℝ).prod (coneArea κ)

/-- **`dt ⊗ r dr dθ` and `dt ⊗ dr dθ` have the same null sets** (`r > 0` almost everywhere). -/
theorem lam3Riem_equiv : lam3Riem κ ≪ lam3 κ ∧ lam3 κ ≪ lam3Riem κ := by
  have hpolar : Measurable (Cone.polar (α := κ)) := Cone.continuous_polar.measurable
  set ρ := (volume : Measure ℝ).restrict (Ioi 0)
  have h1 : ρ.withDensity (fun r => ENNReal.ofReal r) ≪ ρ := withDensity_absolutelyContinuous _ _
  have h2 : ρ ≪ ρ.withDensity (fun r => ENNReal.ofReal r) :=
    withDensity_absolutelyContinuous' ENNReal.measurable_ofReal.aemeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact (ENNReal.ofReal_pos.2 hr).ne')
  have hc1 : coneArea κ ≪ coneMeasure κ :=
    (h1.prod (Measure.AbsolutelyContinuous.refl (volume : Measure (AddCircle κ)))).map hpolar
  have hc2 : coneMeasure κ ≪ coneArea κ :=
    (h2.prod (Measure.AbsolutelyContinuous.refl (volume : Measure (AddCircle κ)))).map hpolar
  exact ⟨(Measure.AbsolutelyContinuous.refl (volume : Measure ℝ)).prod hc1,
    (Measure.AbsolutelyContinuous.refl (volume : Measure ℝ)).prod hc2⟩

/-- **The Riemannian reading changes nothing**: every finite measure with the null sets of
`dt ⊗ r dr dθ` is admissible in the past and in the future. -/
theorem admissible_of_equiv_riem {μ : Measure (Massive κ)} [IsFiniteMeasure μ]
    (h₁ : μ ≪ lam3Riem κ) (h₂ : lam3Riem κ ≪ μ) :
    (massive κ).AdmissiblePast μ ∧ (massive κ).AdmissibleFuture μ :=
  admissible_of_equiv (h₁.trans lam3Riem_equiv.1) (lam3Riem_equiv.2.trans h₂)

/-! ### The planner's measure: admissible, not in the class of `λ₃` -/

omit [Fact (0 < κ)] in
/-- `Cone.polar` is onto. -/
theorem polar_surjective : Function.Surjective (Cone.polar (α := κ)) := fun x => by
  obtain ⟨p, rfl⟩ := Cone.mk_surjective x
  exact ⟨(p.r, p.θ), Cone.polar_rad_θ p⟩

/-- **`polar` of a measure positive on open sets charges the apex**: `polar` sends the half-plane
`{r ≤ 0}` to the apex, so for `m` on `ℝ` positive on open sets (a Gaussian in `r`, say) the image of
`m ⊗ dθ` gives the apex the mass `m(]-∞, 0]) · κ > 0`. -/
theorem map_polar_apex_pos (m : Measure ℝ) [m.IsOpenPosMeasure] [SFinite m] :
    0 < Measure.map Cone.polar (m.prod (volume : Measure (AddCircle κ))) {Cone.apex} := by
  have hpolar : Measurable (Cone.polar (α := κ)) := Cone.continuous_polar.measurable
  rw [Measure.map_apply hpolar (measurableSet_singleton _)]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Iio (0 : ℝ) ×ˢ (univ : Set (AddCircle κ))) ?_)
  · rw [Measure.prod_prod]
    exact ENNReal.mul_pos (isOpen_Iio.measure_pos m ⟨-1, by norm_num⟩).ne'
      (isOpen_univ.measure_pos _ univ_nonempty).ne'
  · rintro ⟨u, θ⟩ ⟨hu, -⟩
    have hu' : u < 0 := hu
    exact Cone.mk_eq_apex (max_eq_right hu'.le)

/-- **The planner's measure is not in the class of `λ₃`**: `dt ⊗ polar_*(m ⊗ dθ)`, `m` positive on
open sets, charges the singular line, which `λ₃` does not. -/
theorem not_absolutelyContinuous_map_polar (m : Measure ℝ) [m.IsOpenPosMeasure] [SFinite m] :
    ¬ ((volume : Measure ℝ).prod
      (Measure.map Cone.polar (m.prod (volume : Measure (AddCircle κ)))) ≪ lam3 κ) := by
  intro h
  have h0 := h lam3_singLine
  rw [singLine_eq_prod, Measure.prod_prod, Real.volume_univ,
    ENNReal.top_mul (map_polar_apex_pos m).ne'] at h0
  exact ENNReal.top_ne_zero h0

/-- **It is admissible nonetheless**: there is a measure on `E_κ` admissible in the past and in the
future which charges the singular line (`(dt ⊗ polar_*(dr ⊗ dθ)).toFinite`, `r` over all of `ℝ`).
Properties 1.–4. do not pin down the class of `λ₃`. -/
theorem exists_admissible_charging_singLine :
    ∃ μ : Measure (Massive κ), (massive κ).AdmissiblePast μ ∧ (massive κ).AdmissibleFuture μ ∧
      0 < μ (singLine κ) := by
  set ν : Measure (Cone κ) :=
    Measure.map Cone.polar ((volume : Measure ℝ).prod (volume : Measure (AddCircle κ)))
  haveI : ν.IsOpenPosMeasure := Cone.continuous_polar.isOpenPosMeasure_map polar_surjective
  have hpos : (0 : ℝ≥0∞) < ((volume : Measure ℝ).prod ν) (singLine κ) := by
    rw [singLine_eq_prod, Measure.prod_prod, Real.volume_univ,
      ENNReal.top_mul (map_polar_apex_pos (volume : Measure ℝ)).ne']
    exact ENNReal.zero_lt_top
  refine ⟨((volume : Measure ℝ).prod ν).toFinite, static_admissible_of_equiv ν
    (toFinite_absolutelyContinuous _) (absolutelyContinuous_toFinite _) |>.1,
    static_admissible_of_equiv ν (toFinite_absolutelyContinuous _)
      (absolutelyContinuous_toFinite _) |>.2, ?_⟩
  exact pos_iff_ne_zero.2 fun h0 => hpos.ne' (toFinite_apply_eq_zero_iff.1 h0)

/-! ### Non-vacuity: `κ = π`, `κ = 4π` -/

/-- `π > 0`, an instance local to this file. -/
theorem fact_pi_pos : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- `4π > 0`, an instance local to this file. -/
theorem fact_four_pi_pos : Fact (0 < 4 * Real.pi) := ⟨by positivity⟩

attribute [local instance] fact_pi_pos fact_four_pi_pos

/-- **Non-vacuity at `κ = π` (deficit) and `κ = 4π` (excess)**: the singular line is not empty,
`λ₃` does not charge it, and one measure is admissible in the past and in the future. -/
theorem nonvacuous :
    (singLine Real.pi).Nonempty ∧ lam3 Real.pi (singLine Real.pi) = 0 ∧
      (∃ μ : Measure (Massive Real.pi), (massive Real.pi).AdmissiblePast μ ∧
        (massive Real.pi).AdmissibleFuture μ) ∧
      (singLine (4 * Real.pi)).Nonempty ∧ lam3 (4 * Real.pi) (singLine (4 * Real.pi)) = 0 ∧
      ∃ μ : Measure (Massive (4 * Real.pi)), (massive (4 * Real.pi)).AdmissiblePast μ ∧
        (massive (4 * Real.pi)).AdmissibleFuture μ :=
  ⟨⟨(0, Cone.apex), rfl⟩, lam3_singLine, exists_admissible_past_future,
    ⟨(0, Cone.apex), rfl⟩, lam3_singLine, exists_admissible_past_future⟩

/-- **Non-vacuity of the restricted form at an axis point**, `κ = π` and `κ = 4π`: `(0, apex)` has
a relatively compact causally convex open neighbourhood on which `λ₃` restricted is admissible in the
past and in the future, and `ModelMeasures` holds. -/
theorem nonvacuous_local :
    (massive Real.pi).ModelMeasures ∧
      (∃ U : Opens (Massive Real.pi), ((0, Cone.apex) : Massive Real.pi) ∈ U ∧
        IsCompact (closure (U : Set (Massive Real.pi))) ∧
        (massive Real.pi).CausallyConvexIn (U : Set (Massive Real.pi)) ⊤ ∧
        (massive Real.pi).AdmissiblePastOn U ((lam3 Real.pi).restrict U) ∧
        (massive Real.pi).AdmissibleFutureOn U ((lam3 Real.pi).restrict U)) ∧
      (massive (4 * Real.pi)).ModelMeasures ∧
      ∃ U : Opens (Massive (4 * Real.pi)), ((0, Cone.apex) : Massive (4 * Real.pi)) ∈ U ∧
        IsCompact (closure (U : Set (Massive (4 * Real.pi)))) ∧
        (massive (4 * Real.pi)).CausallyConvexIn (U : Set (Massive (4 * Real.pi))) ⊤ ∧
        (massive (4 * Real.pi)).AdmissiblePastOn U ((lam3 (4 * Real.pi)).restrict U) ∧
        (massive (4 * Real.pi)).AdmissibleFutureOn U ((lam3 (4 * Real.pi)).restrict U) := by
  obtain ⟨U, hU, -, hrest⟩ := paper_measures_local ((0, Cone.apex) : Massive Real.pi) univ_mem
  obtain ⟨U', hU', -, hrest'⟩ :=
    paper_measures_local ((0, Cone.apex) : Massive (4 * Real.pi)) univ_mem
  exact ⟨modelMeasures, ⟨U, hU, hrest⟩, modelMeasures, ⟨U', hU', hrest'⟩⟩

end MeasuresEAlpha

end Causal
