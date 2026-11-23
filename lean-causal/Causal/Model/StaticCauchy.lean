import Causal.CurvesExtend
import Causal.Model.CurvesExtendModels
import Causal.LadderLocal
import Causal.InextensiblePiece

/-!
# Static spacetimes `ℝ × X`: every slice is a Cauchy surface, the ladder's side conditions, and a removed cylinder reached by a ray

Programme target `T-loc-ealpha-tidy` (`programme/roadmap.toml`; layer 3, localisation, a tidy: no
new statement). Nothing is marked: the module proves no statement of `ETT.tex`. It holds the
statements of `Causal.Model.EAlphaCauchy` (T-loc-ealpha-cauchy) that are about **any** static
spacetime `ℝ × X` over a geodesic metric space (`staticCausality X`, `Causal.Static`,
`defi:causal_Ealpha`'s construction), moved here so that they are usable without
`Causal.Model.Massive`: by `E_α` (`massive α`), by the 3+1 conical spacetime (`cosmicString α`),
by Minkowski space and by the half-plane `staticCausality (Ioi 0)` of the ladder's `[[fails]]`
entries alike.

> Let $M$ be a topological spacetime. A Cauchy surface in $M$ is a subset $S\subset M$ such that
> every causal curve of $M$ meets $S$ exactly once. (`def:cauchy_surface`, `ETT.tex:999–1000`)

DEC-14 reads "causal curve" there as "inextensible causal curve".

## What is here (no `sorry`), namespace `Causal.staticCausality`

* Slices: `isCauchyTimeFunction_sub_const` (`t − t₀` is a Cauchy time function, `X` complete) and
  `isCauchySurface_slice` (every slice `{t = t₀}` is a Cauchy surface, `theo:geroch` (ii)⇒(iii));
* the ladder's side conditions: `noCausalEndpoint`, `chronalNeighbours`, `causallyOpen`,
  `stronglyCausalOpen`, `hasTimeFunction` (with `staticCausality.curvesExtend`, which
  `Causal.Model.CurvesExtendModels` holds and this module imports);
* `J^∓(x)`, `I⁻(x)` and the past null cone on a slice are balls and spheres of `X`
  (`Jminus_inter_slice`, `Jplus_inter_slice`, `Iminus_inter_slice`,
  `Jminus_diff_Iminus_inter_slice`), compact when `X` is proper (`isCompact_Jminus_inter_slice`);
* the timelike cylinder over a closed `A ⊆ X` removed (`offOpens`, kb/0001), a ray reaching `A`
  (`IsRayTo`, `rayCurve`): the ray curve running into `A` is inextensible
  (`IsRayTo.inextensible`, through `Causality.inextensible_Iio_of_tendsto_not_mem`,
  `Causal.InextensiblePiece`), no subset of a slice is a Cauchy surface of `ℝ × (X \ A)`
  (`IsRayTo.not_isCauchySurfaceOn_of_subset_slice`), it has none at all
  (`IsRayTo.not_exists_isCauchySurfaceOn`) and is not globally hyperbolic
  (`IsRayTo.not_globallyHyperbolicOn`); a causal past is its part off `A` plus the pasts of its
  points over `A` (`Jminus_eq_off_union`). kb/0055.

## Hypothesis checklist

| statement | hypotheses on `X` |
|---|---|
| every statement | `[MetricSpace X] [GeodesicSpace X]` (`staticCausality X` needs the second) |
| `isCauchyTimeFunction_sub_const`, `isCauchySurface_slice` | `[CompleteSpace X]` |
| `isCompact_Jminus_inter_slice` | `[ProperSpace X]` |
| `IsRayTo.*` | `A` closed, `r` a 1-Lipschitz ray with `r 0 ∈ A`, `r u ∉ A` for `u > 0` (`IsRayTo.continuous`: no `GeodesicSpace`) |
| `offOpens`, `mem_offOpens`, `Jminus_eq_off_union` | `A` closed (`mem_offOpens`: no `GeodesicSpace`) |
| `noCausalEndpoint`, `chronalNeighbours`, `causallyOpen`, `stronglyCausalOpen`, `hasTimeFunction`, the slice formulas | none more |

## SCOPE (disclosed)

* **A verbatim move.** HEAD `29b547f` `Causal/Model/EAlphaCauchy.lean` l.156–488 (the section
  header `### Static spacetimes …`, `namespace staticCausality` … `end staticCausality`) is
  l.78–410 here, byte for byte, under the same prelude (`namespace Causal`,
  `open Set TopologicalSpace Topology Filter Metric`) and the same `variable` line, so every full
  name, statement and universe parameter is the one it was (kb/0063, kb/0255).
  `Causal.Model.EAlphaCauchy` imports this module and instantiates it at `massive α` and
  `cosmicString α`.
* **Imports.** `Causal.CurvesExtend` (`HasTimeFunction`, Geroch through `Causal.Geroch`),
  `Causal.Model.CurvesExtendModels` (`Causal.Static` through `Causal.Minkowski`, and
  `staticCausality.curvesExtend`), `Causal.LadderLocal` (`NoCausalEndpoint`, `ChronalNeighbours`,
  `PushUp.causallyOpen_of_chronalNeighbours`) and `Causal.InextensiblePiece`
  (`inextensible_Iio_of_tendsto_not_mem`, the one new import): the imports `Causal.Model.EAlphaCauchy`
  had before this split (commit `29b547f`) without `Causal.Model.Massive`, `Causal.CBG.Pgcd` and
  `Mathlib.Analysis.Normed.Lp.ProdLp`, plus `Causal.InextensiblePiece`. A model
  module (`Causal.Model.*`, and `Causal.Static` below it): a layer-1 module never imports it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The moved text was
written by T-loc-ealpha-cauchy.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-! ### Static spacetimes `ℝ × X`: slices, the ladder's side conditions -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

/-- `t − t₀` is a Cauchy time function of `ℝ × X`, `X` complete. -/
theorem isCauchyTimeFunction_sub_const [CompleteSpace X] (t₀ : ℝ) :
    (staticCausality X).IsCauchyTimeFunction fun p => p.1 - t₀ :=
  isCauchyTimeFunction_sub (X := X) (fun _ => t₀) (fun _ _ => by simp) (B := |t₀|)
    (fun _ => le_rfl)

/-- **Every slice `{t = t₀}` of a static spacetime over a complete geodesic space is a Cauchy
surface** (DEC-14: met exactly once by every inextensible causal curve), by `theo:geroch`'s
(ii)⇒(iii) with the strictly increasing Cauchy time function `t − t₀`. -/
theorem isCauchySurface_slice [CompleteSpace X] (t₀ : ℝ) :
    (staticCausality X).IsCauchySurface {p : ℝ × X | p.1 = t₀} := by
  have h := (isCauchyTimeFunction_sub_const (X := X) t₀).isCauchySurface
    causallyArcConnected stronglyCausal Jminus_ne_singleton Jplus_ne_singleton
    fun x y hxy hne => by
      have := fst_lt_of_le hxy hne
      show x.1 - t₀ < y.1 - t₀
      linarith
  have hset : ((fun p : ℝ × X => p.1 - t₀) ⁻¹' {0}) = {p | p.1 = t₀} := by
    ext p; simp [sub_eq_zero]
  rwa [hset] at h

theorem noCausalEndpoint : (staticCausality X).NoCausalEndpoint :=
  ⟨Jminus_ne_singleton, Jplus_ne_singleton⟩

/-- Chronal neighbours in every open set: `(t ∓ ε, x) ≪_V (t, x)`, `ε` small. -/
theorem chronalNeighbours : (staticCausality X).ChronalNeighbours := by
  refine ⟨fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    have hpv : dist ((v.1 - ρ / 4, v.2) : ℝ × X) v = ρ / 4 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, show v.1 - ρ / 4 - v.1 = -(ρ / 4) by ring,
        abs_neg, abs_of_pos (by linarith), max_eq_left (by linarith)]
    refine ⟨(v.1 - ρ / 4, v.2), hball (by rw [mem_ball]; linarith),
      staticLt_of_ball (ρ := ρ / 2) (fun z hz => hball ?_) ?_ ?_⟩
    · rw [mem_ball]; linarith [dist_triangle z ((v.1 - ρ / 4, v.2) : ℝ × X) v]
    · simp only [dist_self]; linarith
    · simp only; linarith
  · obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    have hpv : dist ((v.1 + ρ / 4, v.2) : ℝ × X) v = ρ / 4 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, show v.1 + ρ / 4 - v.1 = ρ / 4 by ring,
        abs_of_pos (by linarith), max_eq_left (by linarith)]
    refine ⟨(v.1 + ρ / 4, v.2), hball (by rw [mem_ball]; linarith),
      staticLt_of_ball (ρ := ρ) (fun z hz => hball hz) ?_ ?_⟩
    · simp only [dist_self]; linarith
    · simp only; linarith

theorem causallyOpen : (staticCausality X).CausallyOpen :=
  pushUp.causallyOpen_of_chronalNeighbours chronalNeighbours

theorem stronglyCausalOpen : (staticCausality X).StronglyCausalOpen :=
  stronglyCausal.stronglyCausalOpen tarentin causallyOpen

theorem hasTimeFunction : (staticCausality X).HasTimeFunction :=
  ⟨Prod.fst, continuous_fst, fun _ _ h hne => fst_lt_of_le h hne⟩

/-! ### `J^∓(x) ∩ {t = t₁}` -/

/-- `J⁻(x) ∩ {t = t₁}` is the closed ball of radius `x.1 − t₁` of `X` about `x.2`. -/
theorem Jminus_inter_slice (x : ℝ × X) (t₁ : ℝ) :
    (staticCausality X).Jminus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (x.1 - t₁) := by
  ext p
  simp only [mem_inter_iff, mem_Jminus_top, mem_setOf_eq, mem_prod, mem_singleton_iff,
    mem_closedBall]
  constructor
  · rintro ⟨h, h1⟩; exact ⟨h1, by rwa [h1] at h⟩
  · rintro ⟨h1, h⟩; exact ⟨by rwa [h1], h1⟩

/-- `J⁺(x) ∩ {t = t₁}` is the closed ball of radius `t₁ − x.1` of `X` about `x.2`. -/
theorem Jplus_inter_slice (x : ℝ × X) (t₁ : ℝ) :
    (staticCausality X).Jplus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (t₁ - x.1) := by
  ext p
  simp only [mem_inter_iff, mem_Jplus_top, mem_setOf_eq, mem_prod, mem_singleton_iff,
    mem_closedBall, dist_comm x.2 p.2]
  constructor
  · rintro ⟨h, h1⟩; exact ⟨h1, by rwa [h1] at h⟩
  · rintro ⟨h1, h⟩; exact ⟨by rwa [h1], h1⟩

/-- `I⁻(x) ∩ {t = t₁}` is the open ball of radius `x.1 − t₁` of `X` about `x.2`. -/
theorem Iminus_inter_slice (x : ℝ × X) (t₁ : ℝ) :
    (staticCausality X).Iminus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ ball x.2 (x.1 - t₁) := by
  ext p
  simp only [mem_inter_iff, mem_Iminus_top, mem_setOf_eq, mem_prod, mem_singleton_iff, mem_ball]
  constructor
  · rintro ⟨h, h1⟩; exact ⟨h1, by rwa [h1] at h⟩
  · rintro ⟨h1, h⟩; exact ⟨by rwa [h1], h1⟩

/-- **The past null cone on a slice**: `(J⁻(x) \ I⁻(x)) ∩ {t = t₁}` is the sphere of radius
`x.1 − t₁` of `X` about `x.2`. -/
theorem Jminus_diff_Iminus_inter_slice (x : ℝ × X) (t₁ : ℝ) :
    ((staticCausality X).Jminus ⊤ {x} \ (staticCausality X).Iminus ⊤ {x}) ∩ {p | p.1 = t₁} =
      {t₁} ×ˢ sphere x.2 (x.1 - t₁) := by
  ext p
  simp only [mem_inter_iff, Set.mem_sdiff, mem_Jminus_top, mem_Iminus_top, mem_setOf_eq, mem_prod,
    mem_singleton_iff, mem_sphere, not_lt]
  constructor
  · rintro ⟨⟨h, h'⟩, h1⟩; rw [h1] at h h'; exact ⟨h1, le_antisymm h h'⟩
  · rintro ⟨h1, h⟩; rw [h1]; exact ⟨⟨h.le, h.ge⟩, rfl⟩

theorem isCompact_Jminus_inter_slice [ProperSpace X] (x : ℝ × X) (t₁ : ℝ) :
    IsCompact ((staticCausality X).Jminus ⊤ {x} ∩ {p | p.1 = t₁}) ∧
      IsCompact ((staticCausality X).Jplus ⊤ {x} ∩ {p | p.1 = t₁}) := by
  refine ⟨?_, ?_⟩
  · rw [Jminus_inter_slice]; exact isCompact_singleton.prod (isCompact_closedBall _ _)
  · rw [Jplus_inter_slice]; exact isCompact_singleton.prod (isCompact_closedBall _ _)

/-! ### The timelike cylinder `ℝ × A` over a closed set `A ⊆ X` removed -/

/-- The open set `ℝ × (X \ A)`, `A` closed: the static spacetime with the cylinder over `A`
removed, seen as a spacetime through the open set (kb/0001). -/
def offOpens {A : Set X} (hA : IsClosed A) : Opens (ℝ × X) :=
  ⟨{p | p.2 ∉ A}, hA.isOpen_compl.preimage continuous_snd⟩

omit [GeodesicSpace X] in
theorem mem_offOpens {A : Set X} {hA : IsClosed A} {p : ℝ × X} : p ∈ offOpens hA ↔ p.2 ∉ A :=
  Iff.rfl

/-- `r` is a **ray reaching `A`**: `1`-Lipschitz, with `r 0 ∈ A` and `r u ∉ A` for `u > 0`. In
`C_α`, the ray of direction `0` reaching the apex. -/
structure IsRayTo (A : Set X) (r : ℝ → X) : Prop where
  lip : ∀ u v, dist (r u) (r v) ≤ |u - v|
  mem_zero : r 0 ∈ A
  not_mem : ∀ u, 0 < u → r u ∉ A

/-- The graph `τ ↦ (τ, r(ρ τ))`. -/
def rayCurve (r : ℝ → X) (ρ : ℝ → ℝ) : ℝ → ℝ × X := fun τ => (τ, r (ρ τ))

namespace IsRayTo

variable {A : Set X} {r : ℝ → X} (hr : IsRayTo A r) (hA : IsClosed A)
include hr

omit [GeodesicSpace X] in
theorem continuous : Continuous r :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun u v => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]; exact hr.lip u v)

include hA in
/-- A ray curve with `ρ` 1-Lipschitz and positive on `]-∞, b[` is a causal curve of
`ℝ × (X \ A)` over `]-∞, b[`. -/
theorem causalCurveIn {b : ℝ} {ρ : ℝ → ℝ}
    (hlip : ∀ τ < b, ∀ τ' < b, |ρ τ - ρ τ'| ≤ |τ - τ'|) (hpos : ∀ τ < b, 0 < ρ τ) :
    (staticCausality X).CausalCurveIn (offOpens hA) (Iio b) (rayCurve r ρ) := by
  refine ⟨⟨b - 1, by simp⟩, ordConnected_Iio, fun a _ a' ha' => ?_⟩
  rcases le_or_gt a a' with h | h
  · refine causalCurveOn_graph ⟨fun τ hτ τ' hτ' => ?_, fun τ hτ => ?_⟩
    · rw [one_mul]
      exact (hr.lip _ _).trans (hlip τ (hτ.2.trans_lt ha') τ' (hτ'.2.trans_lt ha'))
    · exact hr.not_mem _ (hpos τ (hτ.2.trans_lt ha'))
  · exact CurveOn.of_lt h

include hA in
/-- **A ray curve running into `A` at time `b` is inextensible in `ℝ × (X \ A)`.** -/
theorem inextensible {b : ℝ} {ρ : ℝ → ℝ}
    (hlip : ∀ τ < b, ∀ τ' < b, |ρ τ - ρ τ'| ≤ |τ - τ'|) (hpos : ∀ τ < b, 0 < ρ τ)
    (hlim : Tendsto ρ (𝓝[<] b) (𝓝 0)) :
    (staticCausality X).Inextensible (offOpens hA) (Iio b) (rayCurve r ρ) := by
  have h2 : Tendsto (fun τ => r (ρ τ)) (𝓝[<] b) (𝓝 (r 0)) :=
    (hr.continuous.tendsto 0).comp hlim
  refine Causality.inextensible_Iio_of_tendsto_not_mem (hr.causalCurveIn hA hlip hpos)
    (P := (b, r 0)) (fun h => h hr.mem_zero)
    ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).prodMk_nhds h2) (f := Prod.fst)
    (fun _ _ h => (le_iff.1 h).1) fun B => ⟨min B b - 1, ?_, ?_⟩
  · linarith [min_le_right B b]
  · show min B b - 1 < B
    linarith [min_le_left B b]

include hA in
/-- **The witness**: the timelike curve falling along the ray into `A` at speed `1/2`, reaching
it at time `t₀`, is an inextensible causal curve of `ℝ × (X \ A)`, chronal on every segment, and
never meets `{t = t₀}`. -/
theorem infall (t₀ : ℝ) :
    (staticCausality X).Inextensible (offOpens hA) (Iio t₀)
        (rayCurve r fun τ => (t₀ - τ) / 2) ∧
      (∀ a < t₀, ∀ b < t₀,
        (staticCausality X).ChronalCurveOn (offOpens hA) (rayCurve r fun τ => (t₀ - τ) / 2) a b) ∧
      ∀ τ < t₀, (rayCurve r (fun τ => (t₀ - τ) / 2) τ).1 ≠ t₀ := by
  have hlip : ∀ τ < t₀, ∀ τ' < t₀, |(t₀ - τ) / 2 - (t₀ - τ') / 2| ≤ |τ - τ'| := by
    intro τ _ τ' _
    rw [show (t₀ - τ) / 2 - (t₀ - τ') / 2 = -(τ - τ') / 2 by ring, abs_div, abs_neg, abs_two]
    linarith [abs_nonneg (τ - τ')]
  refine ⟨hr.inextensible hA hlip (fun τ hτ => by linarith) ?_, fun a _ a' ha' => ?_,
    fun τ hτ => ne_of_lt hτ⟩
  · have : Tendsto (fun τ : ℝ => (t₀ - τ) / 2) (𝓝 t₀) (𝓝 ((t₀ - t₀) / 2)) :=
      ((continuous_const.sub continuous_id).div_const 2).tendsto t₀
    rw [sub_self, zero_div] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · rcases le_or_gt a a' with h | h
    · refine chronalCurveOn_graph (L := 1 / 2) (by norm_num)
        ⟨fun τ _ τ' _ => (hr.lip _ _).trans ?_, fun τ hτ => ?_⟩
      · rw [show (t₀ - τ) / 2 - (t₀ - τ') / 2 = -(τ - τ') / 2 by ring, abs_div, abs_neg, abs_two]
        linarith
      · exact hr.not_mem _ (by have := hτ.2.trans_lt ha'; linarith)
    · exact CurveOn.of_lt h

include hA in
/-- **No subset of a slice `{t = t₀}` is a Cauchy surface of `ℝ × (X \ A)`.** -/
theorem not_isCauchySurfaceOn_of_subset_slice (t₀ : ℝ) {S : Set (ℝ × X)}
    (hS : S ⊆ {p | p.1 = t₀}) : ¬ (staticCausality X).IsCauchySurfaceOn (offOpens hA) S := by
  intro h
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hxS⟩, -⟩ := h _ _ (hr.infall hA t₀).1
  exact (hr.infall hA t₀).2.2 τ hτ (hS hxS)

include hA in
/-- **`ℝ × (X \ A)` has no Cauchy surface at all.** If `S` were one, the incoming null ray
reaching `A` at time `0` meets `S` at time `τ₂ < 0`, the one reaching `A` at time `3τ₂` meets it at
time `τ₁ < 3τ₂`; the curve running along the second to its point of `S`, then out along the
outgoing null ray until it hits the first, then along the first into `A`, is inextensible and meets
`S` twice. -/
theorem not_exists_isCauchySurfaceOn :
    ¬ ∃ S : Set (ℝ × X), (staticCausality X).IsCauchySurfaceOn (offOpens hA) S := by
  rintro ⟨S, hS⟩
  -- the incoming null ray reaching `A` at time `b`
  have hray : ∀ b : ℝ,
      (staticCausality X).Inextensible (offOpens hA) (Iio b) (rayCurve r fun τ => b - τ) := by
    intro b
    refine hr.inextensible hA (fun τ _ τ' _ => le_of_eq ?_)
      (fun τ hτ => by linarith [show τ < b from hτ]) ?_
    · rw [show b - τ - (b - τ') = -(τ - τ') by ring, abs_neg]
    · have : Tendsto (fun τ : ℝ => b - τ) (𝓝 b) (𝓝 (b - b)) :=
        (continuous_const.sub continuous_id).tendsto b
      rw [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
  -- `P₂`: the ray reaching `A` at time `0` meets `S` at time `τ₂ < 0`
  obtain ⟨_, ⟨⟨τ₂, hτ₂, rfl⟩, h₂S⟩, -⟩ := hS _ _ (hray 0)
  have hτ₂' : τ₂ < 0 := hτ₂
  -- `P₁`: the ray reaching `A` at time `3 τ₂` meets `S` at time `τ₁ < 3 τ₂`
  obtain ⟨_, ⟨⟨τ₁, hτ₁, rfl⟩, h₁S⟩, -⟩ := hS _ _ (hray (3 * τ₂))
  have hτ₁' : τ₁ < 3 * τ₂ := hτ₁
  -- along the second ray to `P₁`, out along an outgoing null ray, in along the first ray
  -- through `P₂` into `A`
  set ρ : ℝ → ℝ := fun τ => min (max (3 * τ₂ - τ) (τ - (2 * τ₁ - 3 * τ₂))) (-τ) with hρ
  have hlip : ∀ τ < (0 : ℝ), ∀ τ' < (0 : ℝ), |ρ τ - ρ τ'| ≤ |τ - τ'| := by
    intro τ _ τ' _
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ((abs_max_sub_max_le_max _ _ _ _).trans
      (max_le (le_of_eq ?_) (le_of_eq ?_))) (le_of_eq ?_))
    · rw [show 3 * τ₂ - τ - (3 * τ₂ - τ') = -(τ - τ') by ring, abs_neg]
    · rw [show τ - (2 * τ₁ - 3 * τ₂) - (τ' - (2 * τ₁ - 3 * τ₂)) = τ - τ' by ring]
    · rw [show -τ - -τ' = -(τ - τ') by ring, abs_neg]
  have hpos : ∀ τ < (0 : ℝ), 0 < ρ τ := by
    intro τ hτ
    refine lt_min (lt_max_iff.2 ?_) (by linarith)
    by_cases h : τ < 3 * τ₂
    · left; linarith
    · right; linarith
  have hlim : Tendsto ρ (𝓝[<] 0) (𝓝 0) := by
    have hneg : Tendsto (fun τ : ℝ => -τ) (𝓝[<] 0) (𝓝 0) := by
      have : Tendsto (fun τ : ℝ => -τ) (𝓝 0) (𝓝 (-0)) := continuous_neg.tendsto 0
      rw [neg_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hneg ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with τ hτ using (hpos τ hτ).le
    · filter_upwards with τ using min_le_right _ _
  obtain ⟨_, -, huniq⟩ := hS _ _ (hr.inextensible hA hlip hpos hlim)
  have e₁ : ρ τ₁ = 3 * τ₂ - τ₁ := by
    show min (max (3 * τ₂ - τ₁) (τ₁ - (2 * τ₁ - 3 * τ₂))) (-τ₁) = 3 * τ₂ - τ₁
    rw [show τ₁ - (2 * τ₁ - 3 * τ₂) = 3 * τ₂ - τ₁ by ring, max_self, min_eq_left (by linarith)]
  have e₂ : ρ τ₂ = 0 - τ₂ := by
    show min (max (3 * τ₂ - τ₂) (τ₂ - (2 * τ₁ - 3 * τ₂))) (-τ₂) = 0 - τ₂
    rw [zero_sub]
    exact min_eq_right (le_max_of_le_right (by linarith))
  have m₁ : rayCurve r ρ τ₁ ∈ rayCurve r ρ '' Iio 0 ∩ S := by
    refine ⟨⟨τ₁, show τ₁ < 0 by linarith, rfl⟩, ?_⟩
    show ((τ₁, r (ρ τ₁)) : ℝ × X) ∈ S
    rw [e₁]; exact h₁S
  have m₂ : rayCurve r ρ τ₂ ∈ rayCurve r ρ '' Iio 0 ∩ S := by
    refine ⟨⟨τ₂, hτ₂, rfl⟩, ?_⟩
    show ((τ₂, r (ρ τ₂)) : ℝ × X) ∈ S
    rw [e₂]; exact h₂S
  have := congrArg Prod.fst ((huniq _ m₁).trans (huniq _ m₂).symm)
  simp only [rayCurve] at this
  linarith

include hA in
/-- **`ℝ × (X \ A)` is not globally hyperbolic**: the diamond from `(−2, r 1)` to `(2, r 1)`
contains `(0, r s)` for every `s ∈ ]0, 1[` and not their limit `(0, r 0)`. -/
theorem not_globallyHyperbolicOn : ¬ (staticCausality X).GloballyHyperbolicOn (offOpens hA) := by
  rintro ⟨-, hcpt⟩
  have hK := (hcpt ((-2 : ℝ), r 1) ((2 : ℝ), r 1)).isClosed
  have hmem : ∀ s ∈ Ioo (0 : ℝ) 1, ((0 : ℝ), r s) ∈
      (staticCausality X).diamond (offOpens hA) ((-2 : ℝ), r 1) ((2 : ℝ), r 1) := by
    intro s hs
    have hγ : ∀ a b, StaticCurve 1 (offOpens hA : Set (ℝ × X))
        (fun τ => r (s + (1 - s) * |τ| / 2)) a b := fun a b =>
      ⟨fun τ _ τ' _ => (hr.lip _ _).trans (by
          rw [show s + (1 - s) * |τ| / 2 - (s + (1 - s) * |τ'| / 2) =
              (1 - s) / 2 * (|τ| - |τ'|) by ring, abs_mul,
            abs_of_pos (by linarith [hs.2] : (0 : ℝ) < (1 - s) / 2)]
          have h1 := abs_abs_sub_abs_le_abs_sub τ τ'
          nlinarith [abs_nonneg (τ - τ'), abs_nonneg (|τ| - |τ'|), hs.1, hs.2]),
       fun τ _ => hr.not_mem _ (by have := abs_nonneg τ; nlinarith [hs.1, hs.2])⟩
    have e₂ : s + (1 - s) * |(-2 : ℝ)| / 2 = 1 := by rw [abs_neg, abs_two]; ring
    have e₂' : s + (1 - s) * |(2 : ℝ)| / 2 = 1 := by rw [abs_two]; ring
    have e₀ : s + (1 - s) * |(0 : ℝ)| / 2 = s := by simp
    rw [Causality.mem_diamond]
    exact ⟨⟨by norm_num, _, by simp only [e₂], by simp only [e₀], hγ _ _⟩,
      ⟨by norm_num, _, by simp only [e₀], by simp only [e₂'], hγ _ _⟩⟩
  have hlim : Tendsto (fun s : ℝ => ((0 : ℝ), r s)) (𝓝[>] 0) (𝓝 ((0 : ℝ), r 0)) :=
    tendsto_const_nhds.prodMk_nhds
      ((hr.continuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
  have h0 := hK.mem_of_tendsto hlim
    (by filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs using hmem s hs)
  have h1 : ((0 : ℝ), r 0) ∈ offOpens hA :=
    (staticCausality X).le_mem_right (Causality.mem_diamond.1 h0).1
  exact h1 hr.mem_zero

end IsRayTo

/-- **A causal past is its part off `A` plus the pasts of its points over `A`**: every `z ≤ x` is
joined to `x` in `ℝ × (X \ A)`, or through a point `ξ ∈ ℝ × A` with `z ≤ ξ ≤ x`. -/
theorem Jminus_eq_off_union {A : Set X} (hA : IsClosed A) (x : ℝ × X) :
    (staticCausality X).Jminus ⊤ {x} = (staticCausality X).Jminus (offOpens hA) {x} ∪
      ⋃ ξ ∈ (staticCausality X).Jminus ⊤ {x} ∩ {p | p.2 ∈ A}, (staticCausality X).Jminus ⊤ {ξ} := by
  ext z
  simp only [mem_union, mem_iUnion, Precausality.mem_Jminus_singleton, mem_inter_iff,
    exists_prop]
  constructor
  · intro h
    obtain ⟨h1, γ, hγz, hγx, hγ⟩ := le_iff.1 h
    by_cases hax : ∃ τ ∈ Icc z.1 x.1, γ τ ∈ A
    · obtain ⟨τ, hτ, hγτ⟩ := hax
      exact Or.inr ⟨(τ, γ τ), ⟨⟨hτ.2, γ, rfl, hγx, hγ.restrict hτ.1 le_rfl⟩, hγτ⟩,
        ⟨hτ.1, γ, hγz, rfl, hγ.restrict le_rfl hτ.2⟩⟩
    · exact Or.inl ⟨h1, γ, hγz, hγx, hγ.lip, fun τ hτ hτA => hax ⟨τ, hτ, hτA⟩⟩
  · rintro (h | ⟨ξ, ⟨hξx, -⟩, hzξ⟩)
    · exact (staticCausality X).le_mono le_top h
    · exact (staticCausality X).le_trans hzξ hξx

end staticCausality

end Causal
