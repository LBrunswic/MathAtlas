import Causal.Flat.CBG
import Causal.Flat.Quotient
import Causal.Flat.SecondCountable
import Causal.ChronalNeighbourBridge
import Causal.CausallyPlainLocZ
import Causal.Ladder.Rules

/-!
# The flat time cylinder `ℤe₀\𝐌ⁿ`: every local ladder property, not causal, not causally compact

Programme target `T-loc-flat-time-cylinder` (`programme/roadmap.toml`; layer 3, localisation, model
`flat-gx`; no paper label: a ladder witness). The cylinder is `TimeCylinder d`, the quotient
`FlatQuotient (FlatQuotient.timeGroup d) ⊤` of `𝐌ⁿ = Minkowski d` (`d` space dimensions, Barbot's
`n = d + 1`, kb/0024) by the group of time translations `ℤ e₀`; its causality `timeCylinder d` is
`flatCausality d (TimeCylinder d)`, the absolutely minimal causality making every chart of the
maximal atlas an isomorphism onto `minkowski d` (`flat_existsUnique_causality`). Each ladder property
is stated as an instance of the ladder's definition, so the abstract theorems apply as they stand.

**`T-loc-flat-time-cylinder/1-topology`** — `timeCylinder_t2Space`,
`TimeCylinder.instSecondCountableTopology`, `TimeCylinder.instConnectedSpace`.
**`T-loc-flat-time-cylinder/2-ladder`** — `timeCylinder_curvesExtend`,
`timeCylinder_absolutelyMinimal`, `timeCylinder_causallyArcConnected`, `timeCylinder_pushUp`,
`timeCylinder_tarentin`, `timeCylinder_chronalNeighbours` (through `timeCylinder_Zplus`,
`timeCylinder_Zminus`), `timeCylinder_causallyOpen`; beyond `provides`,
`timeCylinder_causallyPlain`; the bundle `timeCylinder_singularFlatAxioms`.
**`T-loc-flat-time-cylinder/3-not-causal`** — `timeCylinder_not_isCausal`; in fact `≪_M` relates
every pair (`timeCylinder_lt_top`, `timeCylinder_le_top`); hence `timeCylinder_not_stronglyCausal`,
`timeCylinder_not_stronglyCausalOpen`, `timeCylinder_not_hasTimeFunction`,
`timeCylinder_not_globallyHyperbolic`.
**`T-loc-flat-time-cylinder/4-not-causally-compact`** — every diamond is the cylinder
(`timeCylinder_diamond`), so causal compactness is compactness
(`timeCylinder_causallyCompact_iff_compactSpace`), which holds iff `d = 0`
(`timeCylinder_not_compactSpace`, `TimeCylinder.instCompactSpaceZero`,
`timeCylinder_causallyCompact_iff`): `timeCylinder_not_causallyCompact` for `1 ≤ d`.
**`T-loc-flat-time-cylinder/5-separation`** — `timeCylinder_separates` (`1 ≤ d`: the seven provided
properties and causal plainness, `¬ IsCausal`, `¬ CausallyCompact`, with T2, second countability and
connectedness), and beyond the target `timeCylinder_zero_separates` (`d = 0`, the timelike circle:
the same properties, causally compact and not causal).

> The flat time cylinder ℤe₀\𝐌ⁿ (d ≥ 1 space dimensions) as a separating spacetime: Hausdorff,
> second countable, connected; absolutely minimal, causally arc-connected, push-up, tarentin, with
> chronal neighbours, causally open, every causal curve extending (CurvesExtend); not causal and not
> causally compact (`programme/roadmap.toml`, `T-loc-flat-time-cylinder`, title)

> not causally compact, argued: a lift of any q lies in the future cone of a lift of p, so J(p, q)
> is the whole cylinder, not compact when d ≥ 1 (the same block, `evidence`)

> A topological spacetime is causal if the relation $\leq_M$ is an order relation on $M$.
> (`def:causal_spacetime`, `ETT.tex:653–655`)

> $M$ is causally compact if the diamond $J(p,q)$ is compact for all $p,q\in M$.
> (`def:causally_compact`, `ETT.tex:350–352`)

## Hypothesis checklist

| target claim | here |
|---|---|
| Hausdorff, second countable, connected | ✓ `FlatQuotient.t2Space`, `flat_secondCountableTopology` (DEC-49), `FlatQuotient.connectedSpace` |
| the seven `provides` | ✓ each the ladder's definition at `timeCylinder d`, every `d` |
| not causal (`not_isCausal_timeGroup`) | ✓ and stronger: `x ≪_M y` for all `x, y` |
| not causally compact, `d ≥ 1` | ✓ the evidence's argument, as stated; `1 ≤ d` is necessary (`d = 0`: causally compact) |
| causal plainness (optional) | ✓ by `PushUp.causallyPlain_of_chronalNeighbours` |

## SCOPE (disclosed)

* **Either reading of `defi:causalite` (OQ-18).** `timeCylinder d` is absolutely minimal (every flat
  causality is, `flatCausality_absolutelyMinimal`), so every separation here holds in the gluing
  reading as well as in the library's.
* **The evidence's argument is correct as stated.** For `x = [a]`, `y = [b]` take `n : ℤ` with
  `‖b₂ − a₂‖ < n + b₁ − a₁`: `a ≪ n e₀ + b` in `𝐌ⁿ`, and the projection, a strong morphism
  (`strongMorphism_proj`), carries it to `x ≪_M y`. So `J(p, q)` is the cylinder for all `p, q`, and
  causal compactness is compactness of the cylinder. For `1 ≤ d` the spatial norm `‖a₂‖`,
  invariant under `ℤ e₀`, descends to a continuous unbounded function (`TimeCylinder.spaceNorm`).
  For `d = 0` the cylinder is `ℝ/ℤ`, the image of `[0, 1]`, compact: `d ≥ 1` cannot be dropped.
* **Causal plainness** comes from push-up and chronal neighbours (kb/0077), not from
  `SingularFlatAxioms.causallyPlain`, which asks strong causality: the cylinder is not strongly
  causal (`timeCylinder_not_stronglyCausal`, through `StronglyCausal.isCausal`, T1).
* **`causal_ladder`** proves causal openness (the rule `push_up ∧ chronal_neighbours ⇒
  causally_open`). Chronal neighbours come from `Z⁺ = Z⁻ = M` by
  `AbsolutelyMinimal.chronalNeighbours_iff_Z` (T1), not a ladder rule; plainness is not yet a rule.
* **Imports.** Directly: `Causal.Flat.CBG`, `Causal.Flat.Quotient`, `Causal.Flat.SecondCountable`,
  `Causal.ChronalNeighbourBridge`, `Causal.CausallyPlainLocZ`, `Causal.Ladder.Rules`; no
  `Causal.Port.*`. Transitively the generic `(G, X)` ports `Causal.Port.GXBasic`,
  `.UniversalCover`, `.Developing` (through `Causal.Flat.Developing`, which second countability and
  the flat ladder facts rest on), no `Causal.Port.E0*`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

namespace Flat

open FlatQuotient

variable {d : ℕ}

variable (d) in
/-- **The flat time cylinder** `ℤe₀\𝐌ⁿ`: the quotient of `𝐌ⁿ = Minkowski d` (`d` space
dimensions) by the group `ℤ e₀` of time translations (`FlatQuotient.timeGroup`), which acts freely
and properly discontinuously (instances of `Causal.Flat.Quotient`). Topologically `S¹ × ℝᵈ`. -/
abbrev TimeCylinder : Type := FlatQuotient (timeGroup d) ⊤

variable (d) in
/-- **The causality of the flat time cylinder**: the flat causality of its `(Isom(𝐌ⁿ), 𝐌ⁿ)`-atlas,
for which the projection `𝐌ⁿ → ℤe₀\𝐌ⁿ` is a local isomorphism. -/
noncomputable abbrev timeCylinder : Causality (TimeCylinder d) := flatCausality d (TimeCylinder d)

/-! ### 1. Topology -/

/-- **The cylinder is Hausdorff** (`FlatQuotient.t2Space`, a properly discontinuous action). -/
theorem timeCylinder_t2Space : T2Space (TimeCylinder d) := FlatQuotient.t2Space _ _

/-- **The cylinder is connected**, as `𝐌ⁿ` is. -/
instance TimeCylinder.instConnectedSpace : ConnectedSpace (TimeCylinder d) :=
  FlatQuotient.connectedSpace _ _ FlatQuotient.isConnected_top

/-- **The cylinder is second countable** (DEC-49: every connected Hausdorff
`(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold is, `flat_secondCountableTopology`). -/
instance TimeCylinder.instSecondCountableTopology : SecondCountableTopology (TimeCylinder d) :=
  flat_secondCountableTopology (d := d) _

/-! ### 2. The ladder properties it provides -/

/-- **`curves_extend`**: every causal curve over a segment lies on an inextensible one
(`CBG.flat_curvesExtend`: T2 and second countable). -/
theorem timeCylinder_curvesExtend : (timeCylinder d).CurvesExtend := CBG.flat_curvesExtend

/-- The singular flat bundle with empty singular set (`CBG.flat_singularFlatAxioms`): push-up,
absolute minimality, causal arc-connectedness, tarentin, `Z^± = M`. -/
theorem timeCylinder_singularFlatAxioms :
    (timeCylinder d).SingularFlatAxioms
      (CBG.chartedSing (fun _ => (∅ : Set (Minkowski d))) (TimeCylinder d)) :=
  CBG.flat_singularFlatAxioms

/-- **`absolutely_minimal`** (`flatCausality_absolutelyMinimal`). -/
theorem timeCylinder_absolutelyMinimal : (timeCylinder d).AbsolutelyMinimal :=
  flatCausality_absolutelyMinimal

/-- **`causally_arc_connected`**. -/
theorem timeCylinder_causallyArcConnected : (timeCylinder d).CausallyArcConnected :=
  timeCylinder_singularFlatAxioms.causallyArcConnected

/-- **`push_up`**. -/
theorem timeCylinder_pushUp : (timeCylinder d).PushUp := timeCylinder_singularFlatAxioms.pushUp

/-- **`tarentin`**. -/
theorem timeCylinder_tarentin : (timeCylinder d).Tarentin :=
  timeCylinder_singularFlatAxioms.tarentin

/-- Every point is strongly tarentin in the future. -/
theorem timeCylinder_Zplus : (timeCylinder d).Zplus = univ :=
  eq_univ_of_forall timeCylinder_singularFlatAxioms.mem_Zplus

/-- Every point is strongly tarentin in the past (the singular set is empty). -/
theorem timeCylinder_Zminus : (timeCylinder d).Zminus = univ :=
  eq_univ_of_forall fun p => (timeCylinder_singularFlatAxioms.mem_Zminus_iff p).2 (by simp)

/-- **`chronal_neighbours`**, from `Z^± = M` under absolute minimality on a T1 space
(`AbsolutelyMinimal.chronalNeighbours_iff_Z`). -/
theorem timeCylinder_chronalNeighbours : (timeCylinder d).ChronalNeighbours :=
  (Causality.AbsolutelyMinimal.chronalNeighbours_iff_Z timeCylinder_absolutelyMinimal).2
    ⟨timeCylinder_Zplus, timeCylinder_Zminus⟩

/-- **`causally_open`** (two-sided, DEC-8), by `causal_ladder` from push-up and chronal neighbours
(`PushUp.causallyOpen_of_chronalNeighbours`). -/
theorem timeCylinder_causallyOpen : (timeCylinder d).CausallyOpen := by
  have h1 := timeCylinder_pushUp (d := d)
  have h2 := timeCylinder_chronalNeighbours (d := d)
  causal_ladder

/-- **`causally_plain`** (beyond `provides`), from push-up and chronal neighbours
(`PushUp.causallyPlain_of_chronalNeighbours`, kb/0077). -/
theorem timeCylinder_causallyPlain : (timeCylinder d).CausallyPlain :=
  Causality.PushUp.causallyPlain_of_chronalNeighbours timeCylinder_pushUp
    timeCylinder_chronalNeighbours

/-! ### 3. Not causal: every two points are chronologically related -/

/-- The causality of the subtype `⊤` of `𝐌ⁿ` at `⊤` is `minkowski d`'s (a re-derivation of the
private `le_top_subtype_iff` of `Causal.Flat.Quotient`, with `≪`). -/
private theorem top_rel_iff (x y : (⊤ : Opens (Minkowski d))) :
    ((flatCausality d (⊤ : Opens (Minkowski d))).le ⊤ x y ↔
      (minkowski d).le ⊤ (x : Minkowski d) y) ∧
    ((flatCausality d (⊤ : Opens (Minkowski d))).lt ⊤ x y ↔
      (minkowski d).lt ⊤ (x : Minkowski d) y) := by
  have h := (isIsometricEmbedding_subtype_val (d := d) (⊤ : Opens (Minkowski d))).rel_iff ⊤ ⊤
    (by ext z; simp) x y
  rw [flatCausality_self (d := d)] at h
  exact h

/-- A time translate of a point has the same class. -/
theorem timeCylinder_proj_shift (a : (⊤ : Opens (Minkowski d))) (n : ℤ) :
    proj (timeGroup d) ⊤ ⟨((n : ℝ) • timeVec d) + a, trivial⟩ = proj (timeGroup d) ⊤ a :=
  proj_eq_proj_iff'.2 ⟨timeTranslation d (Multiplicative.ofAdd (-n)), ⟨_, rfl⟩, by
    rw [timeTranslation_smul]
    simp only [toAdd_ofAdd, Int.cast_neg, neg_smul]
    abel⟩

/-- **Every point precedes every point chronologically**: for `x = [a]`, `y = [b]`, a lift
`n e₀ + b` of `y` lies in the chronological future of `a` in `𝐌ⁿ` for `n` large, and the projection
is a strong morphism. -/
theorem timeCylinder_lt_top (x y : TimeCylinder d) : (timeCylinder d).lt ⊤ x y := by
  obtain ⟨a, rfl⟩ := proj_surjective (timeGroup d) ⊤ x
  obtain ⟨b, rfl⟩ := proj_surjective (timeGroup d) ⊤ y
  obtain ⟨n, hn⟩ := exists_int_gt (‖(b : Minkowski d).2 - (a : Minkowski d).2‖ -
    ((b : Minkowski d).1 - (a : Minkowski d).1))
  have hab : (flatCausality d (⊤ : Opens (Minkowski d))).lt ⊤ a
      ⟨((n : ℝ) • timeVec d) + b, trivial⟩ := by
    rw [(top_rel_iff _ _).2, minkowski_lt_top_iff]
    simp only [timeVec, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, Prod.snd_add,
      Prod.smul_snd, smul_zero, zero_add]
    linarith
  have h := (strongMorphism_proj (timeGroup d) ⊤).lt_of_mapsTo (U := ⊤) (V := ⊤)
    (fun _ _ => trivial) hab
  rwa [timeCylinder_proj_shift] at h

/-- Every point precedes every point causally. -/
theorem timeCylinder_le_top (x y : TimeCylinder d) : (timeCylinder d).le ⊤ x y :=
  (timeCylinder d).le_of_lt (timeCylinder_lt_top x y)

/-- **Not causal** (`FlatQuotient.not_isCausal_timeGroup`). -/
theorem timeCylinder_not_isCausal : ¬ (timeCylinder d).IsCausal := not_isCausal_timeGroup

/-- Not strongly causal (strong causality implies causality on a T1 space). -/
theorem timeCylinder_not_stronglyCausal : ¬ (timeCylinder d).StronglyCausal :=
  fun h => timeCylinder_not_isCausal h.isCausal

/-- Not strongly causal with open convex neighbourhoods. -/
theorem timeCylinder_not_stronglyCausalOpen : ¬ (timeCylinder d).StronglyCausalOpen :=
  fun h => timeCylinder_not_stronglyCausal h.stronglyCausal

/-- No continuous function strictly increasing along `≤`. -/
theorem timeCylinder_not_hasTimeFunction : ¬ (timeCylinder d).HasTimeFunction :=
  fun h => timeCylinder_not_isCausal h.isCausal

/-- Not globally hyperbolic. -/
theorem timeCylinder_not_globallyHyperbolic : ¬ (timeCylinder d).GloballyHyperbolic :=
  fun h => timeCylinder_not_isCausal h.isCausal

/-! ### 4. Not causally compact when `d ≥ 1` -/

/-- **Every diamond is the whole cylinder.** -/
theorem timeCylinder_diamond (p q : TimeCylinder d) : (timeCylinder d).diamond ⊤ p q = univ :=
  eq_univ_of_forall fun x =>
    ⟨⟨q, rfl, timeCylinder_le_top x q⟩, ⟨p, rfl, timeCylinder_le_top p x⟩⟩

/-- Causal compactness of the cylinder is its compactness. -/
theorem timeCylinder_causallyCompact_iff_compactSpace :
    (timeCylinder d).CausallyCompact ↔ CompactSpace (TimeCylinder d) := by
  constructor
  · intro h
    obtain ⟨p⟩ : Nonempty (TimeCylinder d) := ⟨proj (timeGroup d) ⊤ ⟨0, trivial⟩⟩
    exact ⟨timeCylinder_diamond p p ▸ h p p⟩
  · intro h p q
    rw [timeCylinder_diamond]
    exact isCompact_univ

/-- The norm of the spatial part, a function on the cylinder (time translations fix it). -/
noncomputable def TimeCylinder.spaceNorm : TimeCylinder d → ℝ :=
  Quotient.lift (fun a : (⊤ : Opens (Minkowski d)) => ‖(a : Minkowski d).2‖) (by
    rintro a b ⟨⟨_, n, rfl⟩, rfl⟩
    show ‖((timeTranslation d n • (b : Minkowski d))).2‖ = _
    rw [timeTranslation_smul]
    simp [timeVec])

theorem TimeCylinder.continuous_spaceNorm : Continuous (TimeCylinder.spaceNorm (d := d)) :=
  Continuous.quotient_lift (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)) _

/-- **For `d ≥ 1` the cylinder is not compact**: the spatial norm is continuous and unbounded. -/
theorem timeCylinder_not_compactSpace (hd : 1 ≤ d) : ¬ CompactSpace (TimeCylinder d) := by
  intro h
  obtain ⟨R, hR⟩ := (isCompact_range (TimeCylinder.continuous_spaceNorm (d := d))).bddAbove
  have hmem := hR ⟨proj (timeGroup d) ⊤
    ⟨(0, EuclideanSpace.single (⟨0, hd⟩ : Fin d) (|R| + 1)), trivial⟩, rfl⟩
  have : TimeCylinder.spaceNorm (proj (timeGroup d) ⊤
      ⟨(0, EuclideanSpace.single (⟨0, hd⟩ : Fin d) (|R| + 1)), trivial⟩) = |R| + 1 := by
    show ‖EuclideanSpace.single (⟨0, hd⟩ : Fin d) (|R| + 1)‖ = _
    simp only [PiLp.norm_single, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  rw [this] at hmem
  linarith [le_abs_self R]

/-- **For `d = 0` the cylinder is the timelike circle `ℝ/ℤ`, compact**: the image of the slab
`[0, 1] × 𝐑⁰`. -/
instance TimeCylinder.instCompactSpaceZero : CompactSpace (TimeCylinder 0) := by
  have hsub : (univ : Set (EuclideanSpace ℝ (Fin 0))).Subsingleton := fun x _ y _ => by
    ext i; exact i.elim0
  have hK : IsCompact (Subtype.val ⁻¹' (Icc (0 : ℝ) 1 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 0))))
      : Set (⊤ : Opens (Minkowski 0))) :=
    (isClosed_univ.isClosedEmbedding_subtypeVal (s := univ)).isCompact_preimage
      (isCompact_Icc.prod hsub.isCompact)
  refine ⟨?_⟩
  have himg : proj (timeGroup 0) ⊤ '' (Subtype.val ⁻¹' (Icc (0 : ℝ) 1 ×ˢ univ)) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨a, rfl⟩ := proj_surjective (timeGroup 0) ⊤ x
    refine ⟨⟨((-⌊(a : Minkowski 0).1⌋ : ℤ) : ℝ) • timeVec 0 + a, trivial⟩, ⟨?_, trivial⟩,
      timeCylinder_proj_shift a _⟩
    simp only [timeVec, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, Int.cast_neg]
    exact ⟨by linarith [Int.floor_le (a : Minkowski 0).1],
      by linarith [Int.lt_floor_add_one (a : Minkowski 0).1]⟩
  rw [← himg]
  exact hK.image (continuous_proj _ _)

/-- **Not causally compact when `d ≥ 1`** (the evidence's argument): `J(p, q)` is the cylinder,
which is not compact. -/
theorem timeCylinder_not_causallyCompact (hd : 1 ≤ d) : ¬ (timeCylinder d).CausallyCompact :=
  fun h => timeCylinder_not_compactSpace hd (timeCylinder_causallyCompact_iff_compactSpace.1 h)

/-- **`d ≥ 1` is necessary**: the cylinder is causally compact exactly when `d = 0`. -/
theorem timeCylinder_causallyCompact_iff : (timeCylinder d).CausallyCompact ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    exact timeCylinder_not_causallyCompact (Nat.one_le_iff_ne_zero.2 hd) h
  · rintro rfl
    exact timeCylinder_causallyCompact_iff_compactSpace.2 inferInstance

/-! ### 5. The separation -/

/-- **The flat time cylinder separates** (`d ≥ 1`): an ETT spacetime (Hausdorff, second
countable; connected) with every causal curve extending, absolutely minimal, causally
arc-connected, push-up, tarentin, with chronal neighbours, causally open and causally plain, which
is neither causal nor causally compact. Absolutely minimal, so the separation holds in either
reading of `defi:causalite`. -/
theorem timeCylinder_separates (hd : 1 ≤ d) :
    (T2Space (TimeCylinder d) ∧ SecondCountableTopology (TimeCylinder d) ∧
      ConnectedSpace (TimeCylinder d)) ∧
    (timeCylinder d).CurvesExtend ∧ (timeCylinder d).AbsolutelyMinimal ∧
    (timeCylinder d).CausallyArcConnected ∧ (timeCylinder d).PushUp ∧
    (timeCylinder d).Tarentin ∧ (timeCylinder d).ChronalNeighbours ∧
    (timeCylinder d).CausallyOpen ∧ (timeCylinder d).CausallyPlain ∧
    ¬ (timeCylinder d).IsCausal ∧ ¬ (timeCylinder d).CausallyCompact :=
  ⟨⟨timeCylinder_t2Space, inferInstance, inferInstance⟩, timeCylinder_curvesExtend,
    timeCylinder_absolutelyMinimal, timeCylinder_causallyArcConnected, timeCylinder_pushUp,
    timeCylinder_tarentin, timeCylinder_chronalNeighbours, timeCylinder_causallyOpen,
    timeCylinder_causallyPlain, timeCylinder_not_isCausal, timeCylinder_not_causallyCompact hd⟩

/-- **The timelike circle separates** (`d = 0`, beyond the target): the same properties, and
causally compact (indeed compact), but not causal. -/
theorem timeCylinder_zero_separates :
    (T2Space (TimeCylinder 0) ∧ SecondCountableTopology (TimeCylinder 0) ∧
      ConnectedSpace (TimeCylinder 0) ∧ CompactSpace (TimeCylinder 0)) ∧
    (timeCylinder 0).CurvesExtend ∧ (timeCylinder 0).AbsolutelyMinimal ∧
    (timeCylinder 0).CausallyArcConnected ∧ (timeCylinder 0).PushUp ∧
    (timeCylinder 0).Tarentin ∧ (timeCylinder 0).ChronalNeighbours ∧
    (timeCylinder 0).CausallyOpen ∧ (timeCylinder 0).CausallyPlain ∧
    (timeCylinder 0).CausallyCompact ∧ ¬ (timeCylinder 0).IsCausal :=
  ⟨⟨timeCylinder_t2Space, inferInstance, inferInstance, inferInstance⟩, timeCylinder_curvesExtend,
    timeCylinder_absolutelyMinimal, timeCylinder_causallyArcConnected, timeCylinder_pushUp,
    timeCylinder_tarentin, timeCylinder_chronalNeighbours, timeCylinder_causallyOpen,
    timeCylinder_causallyPlain, timeCylinder_causallyCompact_iff.2 rfl,
    timeCylinder_not_isCausal⟩

end Flat

end Causal
