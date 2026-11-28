import Causal.Flat.CBG
import Causal.Flat.Examples
import Causal.Flat.SecondCountable
import Causal.Model.MinkowskiFutureOneConnected
import Causal.ChronalNeighbourBridge
import Causal.CausallyPlainLocZ
import Causal.TimelikeHomotopy
import Causal.Ladder.Rules

/-!
# The spatially compact flat cylinder `ℤe₁\𝐌^{1+1}`: every causality node but future one-connectedness

Programme target `T-abs-not-future-one-connected` (`programme/roadmap.toml`; layer 3, kind
localisation, model `flat-gx`; no paper label: a ladder witness). The cylinder is `SpaceCylinder`,
the quotient `FlatQuotient (FlatQuotient.spaceGroup 0) ⊤` of `𝐌^{1+1} = Minkowski 1` by the group
`ℤe₁` of spacelike translations (the circle has length 1); its causality `spaceCylinder` is
`flatCausality 1 SpaceCylinder`, the flat causality of its `(Isom(𝐌^{1+1}), 𝐌^{1+1})`-atlas. Each
ladder property is stated as an instance of the ladder's definition, so the abstract theorems apply
as they stand.

**`T-abs-not-future-one-connected/1-topology`** — `spaceCylinder_t2Space`,
`SpaceCylinder.instConnectedSpace`, `SpaceCylinder.instSecondCountableTopology`.
**`T-abs-not-future-one-connected/2-gh`** — `finite_le_spaceGroup` (the finiteness hypothesis of
`FlatQuotient.globallyHyperbolic_quotient`, proved), `spaceCylinder_globallyHyperbolic`.
**`T-abs-not-future-one-connected/3-local`** — `spaceCylinder_pushUp`,
`spaceCylinder_absolutelyMinimal` (on every open set: `spaceCylinder_absolutelyMinimalOn`),
`spaceCylinder_causallyArcConnected`, `spaceCylinder_chronalNeighbours` (through
`spaceCylinder_Zplus`, `spaceCylinder_Zminus`), `spaceCylinder_causallyOpen`,
`spaceCylinder_causallyPlain`; beside them `spaceCylinder_tarentin`, `spaceCylinder_curvesExtend`,
`spaceCylinder_hasTimeFunction`.
**`T-abs-not-future-one-connected/4-winding`** — the bridge
`Causality.ChronalHomotopyOn.homotopicRel` (a chronal homotopy is a homotopy of paths rel
`{0, 1}`; in `Causal.TimelikeHomotopy` since T-abs-sc-open-hoist), the winding curves
`windCurve k` (`windCurve_chronalCurveOn`, `|k| < 3`), `windCurve_not_chronallyHomotopicOn`
(winding numbers `m ≠ n`, in every open set), and `spaceCylinder_not_futureOneConnected`.
**`T-abs-not-future-one-connected/5-separation`** — `spaceCylinder_separates`: T2, second
countable, connected; the seven provided nodes, the twelve of their ladder closure, absolute
minimality on every open set, and `¬ FutureOneConnected`.

> The spatially compact flat cylinder ℤe₁\𝐌^{1+1} separates future_one_connected: one conjoined
> theorem with T2, second countable and connected, GloballyHyperbolic, PushUp, CausallyOpen,
> AbsolutelyMinimal, CausallyArcConnected, CausallyPlain, ChronalNeighbours and
> ¬ FutureOneConnected (two chronal curves winding differently around the circle), the separation
> of the 19 pairs X → future_one_connected (`programme/roadmap.toml`, the target's title)

> with the circle of length 1, γ_k(s) = [(3s, ks)], k = 0, 1, are future chronal curves (timelike
> segments, |k| < 3) from [(0, 0)] to [(3, 0)]; a homotopy with fixed endpoints would lift to
> 𝐌^{1+1} from (0, 0), and its end point, a path in the discrete fibre over [(3, 0)], would join
> (3, 0) to (3, 1). (`programme/ladder.toml`, the comment opening the `[[open]]` section of
> `future_one_connected`)

> We say that $(M,g)$ is *future one-connected* if, and only if, for all $p, q \in M$, any two
> future directed timelike curves from $p$ to $q$ are timelike homotopic with fixed endpoints.
> (Sbierski 1507.00601 Def 2.13 (2), `InexSchwarzschild2.tex:384`)

## Hypothesis checklist

| target claim | here |
|---|---|
| T2, second countable, connected | ✓ `FlatQuotient.t2Space`, `flat_secondCountableTopology_spaceGroup`, `FlatQuotient.connectedSpace` |
| the seven `provides` | ✓ each the ladder's definition at `spaceCylinder` |
| GH through `globallyHyperbolic_quotient`, its `hfin` | ✓ `hfin` proved (`finite_le_spaceGroup`): `x ≤ y + n e₁` forces `|n| ≤ |Δx| + Δt` |
| `¬ FutureOneConnected`, by winding | ✓ the evidence's curves `γ₀, γ₁`, and more: any two winding numbers `m ≠ n` |
| the other twelve causality nodes (the evidence's closure) | ✓ conjuncts, by `causal_ladder` |

## SCOPE (disclosed)

* **Either reading of `defi:causalite` (OQ-18).** `spaceCylinder` is absolutely minimal on every
  open set (`flatCausality_absolutelyMinimalOn`, a conjunct), so the separation holds in the
  gluing reading as well as in the library's.
* **The winding argument as stated.** `γ_k(s) = [(3s, ks)]` (`windCurve k`, lift `windLift k`) is a
  future chronal curve of `⊤` over `[0, 1]` when `|k| < 3`: its lift is a timelike segment of
  `minkowski 1` (`minkowski_chronalCurveOn_iff`), and `𝐌^{1+1} → ℤe₁\𝐌^{1+1}` is an abstract
  morphism (`isEMorphism_spaceCylinderMk`, a local isometry). A chronal homotopy is a homotopy of
  paths rel `{0, 1}` (`ChronalHomotopyOn.homotopicRel`, which reads only the joint continuity on
  `[0, 1]²` and the fixed endpoints, not chronality), and the lifts from `(0, 0)` of the two
  curves end at `(3, m)` and `(3, n)`, while `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`
  makes them end at one point. So the curves are not even homotopic rel endpoints as paths, and
  not chronally homotopic in any open set `W` (`windCurve_not_chronallyHomotopicOn`).
* **The closure.** `causal_ladder` proves the twelve nodes beyond the seven (each one call, kb/0225),
  under `T2Space` and `SecondCountableTopology` (strong causality and the time function from
  `globally_hyperbolic ∧ tarentin`, `curves_extend` the fact). The time function is Geroch's, not
  the time coordinate (which is one too, argued in the ladder note; not stated).
* **Moved out** (T-abs-sc-open-hoist; kb/0061). The two model-free lemmas first proved here are
  in their ETT-layer homes, byte for byte under the same full names:
  `Causal.IsEMorphismOn.chronalCurveOn_comp` (the `≪` twin of `IsEMorphismOn.causalCurveOn_comp`)
  in `Causal.CauchyExtension`, and `Causal.Causality.ChronalHomotopyOn.homotopicRel` (Mathlib
  homotopies only) in `Causal.TimelikeHomotopy`. This module reaches both through its imports.
  `isLocalIsometry_mk_top`, which stays, is for every `d`.
* **Imports.** Directly: `Causal.Flat.CBG`, `Causal.Flat.Examples`, `Causal.Flat.SecondCountable`,
  `Causal.Model.MinkowskiFutureOneConnected`, `Causal.ChronalNeighbourBridge`,
  `Causal.CausallyPlainLocZ`, `Causal.TimelikeHomotopy`, `Causal.Ladder.Rules`; no `Causal.Port.*`
  directly, and transitively the generic `(G, X)` ports only (kb/0078), no `Causal.Port.E0*`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

namespace Flat

open FlatQuotient

/-- **The spatially compact flat cylinder** `ℤe₁\𝐌^{1+1}`: the quotient of `𝐌^{1+1} = Minkowski 1`
by the group `ℤe₁` of spacelike translations (`FlatQuotient.spaceGroup 0`), which acts freely,
properly discontinuously and acausally (`Causal.Flat.Quotient`). Topologically `S¹ × ℝ`, the
circle spacelike, of length 1. -/
abbrev SpaceCylinder : Type := FlatQuotient (spaceGroup 0) ⊤

/-- **The causality of the spatially compact flat cylinder**: the flat causality of its
`(Isom(𝐌^{1+1}), 𝐌^{1+1})`-atlas, for which the projection is a local isomorphism. -/
noncomputable abbrev spaceCylinder : Causality SpaceCylinder := flatCausality 1 SpaceCylinder

/-! ### 1. Topology -/

/-- **The cylinder is Hausdorff** (`FlatQuotient.t2Space`, a properly discontinuous action). -/
theorem spaceCylinder_t2Space : T2Space SpaceCylinder := FlatQuotient.t2Space _ _

/-- **The cylinder is connected**, as `𝐌^{1+1}` is. -/
instance SpaceCylinder.instConnectedSpace : ConnectedSpace SpaceCylinder :=
  FlatQuotient.connectedSpace _ _ FlatQuotient.isConnected_top

/-- **The cylinder is second countable** (DEC-49, `flat_secondCountableTopology_spaceGroup`). -/
instance SpaceCylinder.instSecondCountableTopology : SecondCountableTopology SpaceCylinder :=
  flat_secondCountableTopology_spaceGroup

/-! ### 2. Global hyperbolicity -/

/-- **Only finitely many `γ ∈ ℤe₁` have `x ≤ γ y`** (the hypothesis `hfin` of
`FlatQuotient.globallyHyperbolic_quotient`): `x ≤ y + n e₁` forces
`|n| ≤ |y₁ − x₁| + (y₀ − x₀)`. -/
theorem finite_le_spaceGroup (x y : (⊤ : Opens (Minkowski 1))) :
    {γ : spaceGroup 0 | (flatCausality 1 (⊤ : Opens (Minkowski 1))).le ⊤ x (γ • y)}.Finite := by
  set N : ℤ := ⌈|(y : Minkowski 1).2 0 - (x : Minkowski 1).2 0| +
    ((y : Minkowski 1).1 - (x : Minkowski 1).1)⌉
  refine ((Set.finite_Icc (-N) N).image fun m : ℤ =>
    (⟨spaceTranslation 0 (Multiplicative.ofAdd m), m, rfl⟩ : spaceGroup 0)).subset ?_
  rintro ⟨_, n, rfl⟩ hle
  have hle' := minkowski_le_top_iff.1 ((flat_le_top_subtype_iff ⊤ _ _).1 hle)
  have hc : |((Multiplicative.toAdd n : ℤ) : ℝ) + (y : Minkowski 1).2 0 - (x : Minkowski 1).2 0| ≤
      ((y : Minkowski 1).1 - (x : Minkowski 1).1) := by
    have h1 := PiLp.norm_apply_le (((spaceTranslation 0 n • (y : Minkowski 1))).2 -
      (x : Minkowski 1).2) 0
    have h2 : ((spaceTranslation 0 n • (y : Minkowski 1))).2 0 =
        ((Multiplicative.toAdd n : ℤ) : ℝ) + (y : Minkowski 1).2 0 :=
      coord_spaceTranslation_smul n _
    have h3 : (spaceTranslation 0 n • (y : Minkowski 1)).1 = (y : Minkowski 1).1 :=
      fst_spaceTranslation_smul n _
    simp only [coe_smul] at hle'
    rw [h3] at hle'
    rw [PiLp.sub_apply, h2, Real.norm_eq_abs] at h1
    linarith
  refine ⟨Multiplicative.toAdd n, ?_, rfl⟩
  have hN : |(y : Minkowski 1).2 0 - (x : Minkowski 1).2 0| +
      ((y : Minkowski 1).1 - (x : Minkowski 1).1) ≤ (N : ℝ) := Int.le_ceil _
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  have habs : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self ((y : Minkowski 1).2 0 - (x : Minkowski 1).2 0),
      neg_abs_le ((y : Minkowski 1).2 0 - (x : Minkowski 1).2 0)]
  have habs' : |Multiplicative.toAdd n| ≤ N := by exact_mod_cast habs
  exact ⟨by linarith [neg_abs_le (Multiplicative.toAdd n)], (le_abs_self _).trans habs'⟩

/-- **`globally_hyperbolic`** (ETT's: causal, compact diamonds), through
`FlatQuotient.globallyHyperbolic_quotient`: the action is acausal (`actsAcausally_spaceGroup`),
`𝐌^{1+1}` is GH, and `finite_le_spaceGroup`. -/
theorem spaceCylinder_globallyHyperbolic : spaceCylinder.GloballyHyperbolic :=
  globallyHyperbolic_quotient (spaceGroup 0) ⊤ actsAcausally_spaceGroup
    (globallyHyperbolic_subtype ⊤ ((minkowski 1).globallyHyperbolicOn_top.2
      minkowski_globallyHyperbolic)) finite_le_spaceGroup

/-! ### 3. The local nodes -/

/-- The singular flat bundle with empty singular set (`CBG.flat_singularFlatAxioms`): push-up,
absolute minimality, causal arc-connectedness, tarentin, `Z^± = M`. -/
theorem spaceCylinder_singularFlatAxioms :
    spaceCylinder.SingularFlatAxioms
      (CBG.chartedSing (fun _ => (∅ : Set (Minkowski 1))) SpaceCylinder) :=
  CBG.flat_singularFlatAxioms

/-- **`push_up`**. -/
theorem spaceCylinder_pushUp : spaceCylinder.PushUp := spaceCylinder_singularFlatAxioms.pushUp

/-- **`absolutely_minimal`** (`flatCausality_absolutelyMinimal`). -/
theorem spaceCylinder_absolutelyMinimal : spaceCylinder.AbsolutelyMinimal :=
  flatCausality_absolutelyMinimal

/-- Absolutely minimal on every open set (`flatCausality_absolutelyMinimalOn`): the gluing
reading of `defi:causalite` (OQ-18, DEC-167). -/
theorem spaceCylinder_absolutelyMinimalOn (W : Opens SpaceCylinder) :
    spaceCylinder.AbsolutelyMinimalOn W :=
  flatCausality_absolutelyMinimalOn W

/-- **`causally_arc_connected`**. -/
theorem spaceCylinder_causallyArcConnected : spaceCylinder.CausallyArcConnected :=
  spaceCylinder_singularFlatAxioms.causallyArcConnected

/-- **`tarentin`**. -/
theorem spaceCylinder_tarentin : spaceCylinder.Tarentin :=
  spaceCylinder_singularFlatAxioms.tarentin

/-- Every point is strongly tarentin in the future. -/
theorem spaceCylinder_Zplus : spaceCylinder.Zplus = univ :=
  eq_univ_of_forall spaceCylinder_singularFlatAxioms.mem_Zplus

/-- Every point is strongly tarentin in the past (the singular set is empty). -/
theorem spaceCylinder_Zminus : spaceCylinder.Zminus = univ :=
  eq_univ_of_forall fun p => (spaceCylinder_singularFlatAxioms.mem_Zminus_iff p).2 (by simp)

/-- **`chronal_neighbours`**, from `Z^± = M` under absolute minimality on a T1 space
(`AbsolutelyMinimal.chronalNeighbours_iff_Z`). -/
theorem spaceCylinder_chronalNeighbours : spaceCylinder.ChronalNeighbours :=
  (Causality.AbsolutelyMinimal.chronalNeighbours_iff_Z spaceCylinder_absolutelyMinimal).2
    ⟨spaceCylinder_Zplus, spaceCylinder_Zminus⟩

/-- **`causally_open`** (two-sided, DEC-8), by `causal_ladder` from push-up and chronal neighbours
(`PushUp.causallyOpen_of_chronalNeighbours`). -/
theorem spaceCylinder_causallyOpen : spaceCylinder.CausallyOpen := by
  have h1 := spaceCylinder_pushUp
  have h2 := spaceCylinder_chronalNeighbours
  causal_ladder

/-- **`causally_plain`**, from push-up and chronal neighbours
(`PushUp.causallyPlain_of_chronalNeighbours`, kb/0077). -/
theorem spaceCylinder_causallyPlain : spaceCylinder.CausallyPlain :=
  Causality.PushUp.causallyPlain_of_chronalNeighbours spaceCylinder_pushUp
    spaceCylinder_chronalNeighbours

/-- **`curves_extend`** (`CBG.flat_curvesExtend`: T2 and second countable). -/
theorem spaceCylinder_curvesExtend : spaceCylinder.CurvesExtend := CBG.flat_curvesExtend

/-- **`time_function`**, by `causal_ladder` (`globally_hyperbolic ∧ tarentin ⇒ time_function`, T2,
second countable: Geroch's time function). -/
theorem spaceCylinder_hasTimeFunction : spaceCylinder.HasTimeFunction := by
  have h1 := spaceCylinder_globallyHyperbolic
  have h2 := spaceCylinder_tarentin
  causal_ladder

/-! ### 4. Not future one-connected: two curves winding differently around the circle -/

/-- The inclusion `𝐌ⁿ → ⊤`, a point to itself in the subtype `⊤`, is a local isometry. -/
theorem isLocalIsometry_mk_top {d : ℕ} :
    IsLocalIsometry d (fun p : Minkowski d => (⟨p, trivial⟩ : (⊤ : Opens (Minkowski d)))) :=
  isLocalIsometry_iff_eventually.2 ⟨continuous_id.subtype_mk _, fun _ => ⟨1,
    Filter.Eventually.of_forall fun _ => by rw [one_smul]; rfl⟩⟩

/-- The covering map `𝐌^{1+1} → ℤe₁\𝐌^{1+1}`, read on `𝐌^{1+1}` itself: `p ↦ [p]`. -/
noncomputable def spaceCylinderMk (p : Minkowski 1) : SpaceCylinder :=
  proj (spaceGroup 0) ⊤ ⟨p, trivial⟩

/-- `p ↦ [p]` is an abstract morphism of `minkowski 1` into the cylinder (a local isometry). -/
theorem isEMorphism_spaceCylinderMk :
    IsEMorphism (minkowski 1) spaceCylinder spaceCylinderMk := by
  have h := ((isLocalIsometry_proj (spaceGroup 0) ⊤).comp
    (isLocalIsometry_mk_top (d := 1))).isEMorphism
  rw [flatCausality_self] at h
  exact h

/-- Points differing by `n e₁`, `n ∈ ℤ`, have the same class. -/
theorem spaceCylinderMk_add_int (p : Minkowski 1) (n : ℤ) :
    spaceCylinderMk (p + ((0 : ℝ), (n : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) =
      spaceCylinderMk p := by
  refine proj_eq_proj_iff'.2 ⟨spaceTranslation 0 (Multiplicative.ofAdd (-n)), ⟨_, rfl⟩, ?_⟩
  show spaceTranslation 0 (Multiplicative.ofAdd (-n)) •
      (p + ((0 : ℝ), (n : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) = p
  have hv : ((n : ℝ) • spaceVec 0 : Minkowski (0 + 1)) =
      ((0 : ℝ), (n : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    simp [spaceVec, Prod.smul_mk]
  rw [spaceTranslation_smul, toAdd_ofAdd, Int.cast_neg, neg_smul, hv]
  abel

/-- The lift of the `k`-th winding curve, `s ↦ (3s, ks)` (time first). -/
noncomputable def windLift (k s : ℝ) : Minkowski 1 :=
  s • ((3 : ℝ), k • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

/-- **The `k`-th winding curve** of the cylinder, `γ_k(s) = [(3s, ks)]`. -/
noncomputable def windCurve (k s : ℝ) : SpaceCylinder := spaceCylinderMk (windLift k s)

theorem continuous_windLift (k : ℝ) : Continuous (windLift k) :=
  continuous_id.smul continuous_const

theorem windLift_zero (k : ℝ) : windLift k 0 = 0 := by simp [windLift]

/-- Along the lift, a later point is in the chronological future, for `|k| < 3`. -/
theorem windLift_lt {k : ℝ} (hk : |k| < 3) {s s' : ℝ} (hss' : s < s') :
    (minkowski 1).lt ⊤ (windLift k s) (windLift k s') := by
  rw [minkowski_lt_top_iff]
  have h2 : (windLift k s').2 - (windLift k s).2 =
      (s' - s) • (k • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    simp only [windLift, Prod.smul_snd, sub_smul]
  have h1 : (windLift k s').1 - (windLift k s).1 = (s' - s) * 3 := by
    simp only [windLift, Prod.smul_fst, smul_eq_mul]; ring
  have hpos : 0 < s' - s := sub_pos.2 hss'
  rw [h1, h2, norm_smul, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_of_nonneg hpos.le, Real.norm_eq_abs]
  exact mul_lt_mul_of_pos_left hk hpos

/-- **The `k`-th winding curve is a future chronal curve** of the cylinder over `[0, 1]`, for
`|k| < 3`: its lift is a timelike segment of `𝐌^{1+1}`. -/
theorem windCurve_chronalCurveOn {k : ℝ} (hk : |k| < 3) :
    spaceCylinder.ChronalCurveOn ⊤ (windCurve k) 0 1 := by
  have hc : (minkowski 1).ChronalCurveOn ⊤ (windLift k) 0 1 :=
    minkowski_chronalCurveOn_iff.2 ⟨(continuous_windLift k).continuousOn, fun _ _ => trivial,
      fun _ _ _ _ h => windLift_lt hk h⟩
  exact isEMorphism_spaceCylinderMk.chronalCurveOn_comp le_rfl (U := ⊤) (fun _ _ => trivial) hc

/-- Every winding curve starts at `[(0, 0)]`. -/
theorem windCurve_zero (k : ℝ) : windCurve k 0 = windCurve 0 0 := by
  simp only [windCurve, windLift_zero]

/-- A winding curve with an integer winding number ends at `[(3, 0)]`. -/
theorem windCurve_one_int (n : ℤ) : windCurve n 1 = windCurve 0 1 := by
  have h : windLift n 1 = windLift 0 1 +
      ((0 : ℝ), (n : ℝ) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    simp [windLift]
  rw [windCurve, h, spaceCylinderMk_add_int]
  rfl

/-- **Winding curves with different winding numbers are not chronally homotopic**, in any open
set `W`: a chronal homotopy is a homotopy of paths rel `{0, 1}`, and the lifts from `(0, 0)` end at
`(3, m)` and `(3, n)`. -/
theorem windCurve_not_chronallyHomotopicOn {m n : ℤ} (hmn : m ≠ n) (W : Opens SpaceCylinder) :
    ¬ spaceCylinder.ChronallyHomotopicOn W (windCurve m) (windCurve n) := by
  rintro ⟨Γ, hΓ⟩
  let f : ℝ → C(unitInterval, SpaceCylinder) := fun k =>
    ⟨fun s => windCurve k s, (continuous_proj _ _).comp
      (((continuous_windLift k).comp continuous_subtype_val).subtype_mk _)⟩
  let L : ℝ → C(unitInterval, (⊤ : Opens (Minkowski 1))) := fun k =>
    ⟨fun s => ⟨windLift k s, trivial⟩,
      ((continuous_windLift k).comp continuous_subtype_val).subtype_mk _⟩
  have hrel := hΓ.homotopicRel (f m) (f n) (fun _ => rfl) (fun _ => rfl)
  have cov := isCoveringMap_proj (spaceGroup 0) ⊤
  have h0 : ∀ k : ℝ, f k 0 = proj (spaceGroup 0) ⊤ ⟨0, trivial⟩ := fun k => by
    show spaceCylinderMk (windLift k 0) = _
    rw [windLift_zero]; rfl
  have hend := cov.liftPath_apply_one_eq_of_homotopicRel hrel ⟨0, trivial⟩ (h0 m) (h0 n)
  have hL : ∀ k : ℝ, L k = cov.liftPath (f k) ⟨0, trivial⟩ (h0 k) := fun k =>
    (cov.eq_liftPath_iff' _).2 ⟨rfl, Subtype.ext (windLift_zero k)⟩
  rw [← hL m, ← hL n] at hend
  have h2 := congrArg (fun q : (⊤ : Opens (Minkowski 1)) => (q : Minkowski 1).2 0) hend
  simp only [L, windLift, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul, PiLp.smul_apply,
    PiLp.single_apply, if_true, smul_eq_mul, mul_one] at h2
  exact hmn (by exact_mod_cast h2)

/-- **`ℤe₁\𝐌^{1+1}` is not future one-connected** (the ETT node `Causality.FutureOneConnected`):
`γ₀(s) = [(3s, 0)]` and `γ₁(s) = [(3s, s)]` are future chronal curves from `[(0, 0)]` to
`[(3, 0)]`, not chronally homotopic with fixed endpoints. -/
theorem spaceCylinder_not_futureOneConnected : ¬ spaceCylinder.FutureOneConnected := by
  intro hfoc
  have hk0 : |((0 : ℤ) : ℝ)| < 3 := by norm_num
  have hk1 : |((1 : ℤ) : ℝ)| < 3 := by norm_num
  have h0 : windCurve ((0 : ℤ) : ℝ) 1 = windCurve ((0 : ℤ) : ℝ) 1 := rfl
  exact windCurve_not_chronallyHomotopicOn (m := 0) (n := 1) (by norm_num) ⊤
    (hfoc _ _ _ _ (windCurve_chronalCurveOn hk0) rfl h0 (windCurve_chronalCurveOn hk1)
      ((windCurve_zero _).trans (windCurve_zero _).symm)
      ((windCurve_one_int 1).trans (windCurve_one_int 0).symm))

/-! ### 5. The separation -/

/-- **The spatially compact flat cylinder separates `future_one_connected`**: an ETT spacetime
(Hausdorff, second countable, connected) that is globally hyperbolic, push-up, causally open,
absolutely minimal, causally arc-connected, causally plain, with chronal neighbours (the seven
provided nodes); causally compact, causally open in the future, with every causal curve
extending, a chronal neighbour at every point, causal, locally causally open (both forms), locally
push-up, strongly causal (both forms), tarentin, with a time function (the twelve nodes of their
closure); absolutely minimal on every open set (either reading of `defi:causalite`); and not
future one-connected. -/
theorem spaceCylinder_separates :
    (T2Space SpaceCylinder ∧ SecondCountableTopology SpaceCylinder ∧
      ConnectedSpace SpaceCylinder) ∧
    spaceCylinder.GloballyHyperbolic ∧ spaceCylinder.PushUp ∧ spaceCylinder.CausallyOpen ∧
    spaceCylinder.AbsolutelyMinimal ∧ spaceCylinder.CausallyArcConnected ∧
    spaceCylinder.CausallyPlain ∧ spaceCylinder.ChronalNeighbours ∧
    spaceCylinder.CausallyCompact ∧ spaceCylinder.CausallyOpenFuture ∧
    spaceCylinder.CurvesExtend ∧ spaceCylinder.HasChronalNeighbourEverywhere ∧
    spaceCylinder.IsCausal ∧ spaceCylinder.LocallyCausallyOpen ∧
    spaceCylinder.LocallyCausallyOpenFuture ∧ spaceCylinder.LocallyPushUp ∧
    spaceCylinder.StronglyCausal ∧ spaceCylinder.StronglyCausalOpen ∧
    spaceCylinder.Tarentin ∧ spaceCylinder.HasTimeFunction ∧
    (∀ W : Opens SpaceCylinder, spaceCylinder.AbsolutelyMinimalOn W) ∧
    ¬ spaceCylinder.FutureOneConnected := by
  have h1 := spaceCylinder_globallyHyperbolic
  have h2 := spaceCylinder_pushUp
  have h3 := spaceCylinder_causallyOpen
  have h4 := spaceCylinder_absolutelyMinimal
  have h5 := spaceCylinder_causallyArcConnected
  have h6 := spaceCylinder_causallyPlain
  have h7 := spaceCylinder_chronalNeighbours
  have h8 := spaceCylinder_tarentin
  exact ⟨⟨spaceCylinder_t2Space, inferInstance, inferInstance⟩, h1, h2, h3, h4, h5, h6, h7,
    by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder,
    by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder, by causal_ladder,
    by causal_ladder, by causal_ladder, spaceCylinder_absolutelyMinimalOn,
    spaceCylinder_not_futureOneConnected⟩

end Flat

end Causal
