import Causal.Model.Massive
import Causal.CurvesExtend
import Causal.LadderLocal
import Causal.CBG.Pgcd
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `E_α`, `α > 0`: `{t = 0}` is a Cauchy surface with the axis kept, and there is none without

Programme target `T-loc-ealpha-cauchy` (`programme/roadmap.toml`; layer 3, localisation, model
`E_alpha`, provides `globally_hyperbolic`; no paper label): `references/sbierski/SYNTHESIS.md:100`
(Q4 #4), Hörmann 1501.00672, Ellis–Schmidt (as quoted by Hörmann), Vickers–Wilson gr-qc/9907105.
`E_α = ℝ × C_α` is `Massive α` with `massive α` (`Causal.Model.Massive`), axis `singLine α`;
**the axis removed** is `massive α` on the open set `regOpens α = ℝ × (C_α \ {apex})` (kb/0001).
Each assertion is proved as well for Hörmann's and Vickers–Wilson's 3+1 conical spacetime
`ℝ_t × C_α × ℝ_z` (`cosmicString α`), both as instances of statements about any static `ℝ × X`
with the cylinder over a closed `A ⊆ X` reached by a ray removed (`staticCausality.IsRayTo`).

* **`T-loc-ealpha-cauchy/1-cauchy-axis-kept`** — `massive_globallyHyperbolic_isCauchySurface`:
  `E_α` is globally hyperbolic and `{t = 0}` is a Cauchy surface (DEC-14), as is every slice
  (`massive_isCauchySurface_slice`); `t − t₀` is a Cauchy time function; the axis is an inextensible
  causal curve, meeting `{t = t₀}` at `(t₀, apex)` (`massive_inextensible_singLine`,
  `singLine_inter_slice`). 3+1: `cosmicString_globallyHyperbolic_isCauchySurface`.
* **`T-loc-ealpha-cauchy/2-axis-removed`** — `not_isCauchySurfaceOn_regOpens_slice`: `{t = 0} ∩ reg`
  is not a Cauchy surface of `reg(E_α)`; the curve is `massive_infall 0`, falling radially into the
  axis at speed `1/2`, inextensible in `reg(E_α)`, chronal on every segment, all of it in `{t < 0}`.
  Stronger: no subset of any slice is one (`not_isCauchySurfaceOn_regOpens_of_subset_slice`);
  **`reg(E_α)` has no Cauchy surface at all** (`not_exists_isCauchySurfaceOn_regOpens`,
  Ellis–Schmidt's claim) and is not globally hyperbolic (`not_globallyHyperbolicOn_regOpens`).
  3+1: `cosmicString_not_isCauchySurfaceOn_offAxis_slice`,
  `cosmicString_not_exists_isCauchySurfaceOn_offAxis`, `cosmicString_not_globallyHyperbolicOn_offAxis`.
* **`T-loc-ealpha-cauchy/3-past-through-axis`** — `massive_Jminus_axis_inter_slice`: for
  `x = (t₀, apex)`, `J⁻(x) ∩ {t = 0} = {t = 0, r ≤ t₀}`, and the past null cone
  `(J⁻ \ I⁻)(x) ∩ {t = 0} = {t = 0, r = t₀}` (`massive_nullCone_axis_inter_slice`); for every `x`,
  `J^∓(x) ∩ {t = t₁}` is a closed ball of `C_α` (`massive_Jminus_inter_slice`,
  `massive_Jplus_inter_slice`), compact; `J⁻(x) = J⁻_reg(x) ∪ ⋃_{ξ ∈ J⁻(x) ∩ axis} J⁻(ξ)`
  (`massive_Jminus_eq_reg_union_axis`). 3+1: `r² + (z − z₀)² ≤ t₀²`
  (`cosmicString_Jminus_axis_inter_slice`), `= t₀²` on the null cone.
* **`T-loc-ealpha-cauchy/4-ladder`** — the ladder's side conditions for `massive α`
  (`massive_noCausalEndpoint`, `massive_chronalNeighbours`, `massive_causallyOpen`,
  `massive_stronglyCausalOpen`, `massive_hasTimeFunction`, `massive_curvesExtend`, …) and the
  ladder properties for `cosmicString α` (`cosmicString_*`); `causally_plain` is not instantiated
  for either.

> Thus Ellis and Schmidt concluded that “there can be no global Cauchy surfaces in these
> space-times”. (`hormann2015conical.txt:500–501`)

> We will check that ρ is an L∞ Riemann metric on R3 and that {t} × R3 is a Cauchy
> hypersurface for gα in an appropriate sense: [footnote] Namely, defined as usual by requiring
> that timelike inextendible curves meet the surface exactly once (`hormann2015conical.txt:271–277`)
> […] hence the curve γ must hit {t} × R3 at least once, and by strict monotonicity of γ0 at most
> once. (`:326–327`)

> for a point x on the axis, the past null cone Ĉ0−(x) is given in quasi-Cartesian coordinates by
> the usual Minkowskian formula. (`vickers2000generalized.txt:1217–1218`) The solution at x depends
> not just on the initial data on C0−(x) ∩ S but also on points in C0−(ξ) ∩ S with
> ξ ∈ C0−(x) ∩ Λ. (`:1317–1318`)

## Hypothesis checklist

| source | here |
|---|---|
| Hörmann: `R⁴`, `−dt² + dr² + α_H² r² dφ² + dz²`, `0 < α_H < 1` (`:23–25`) | ✓ `cosmicString α`, total angle `α = 2π α_H`; ⚠ weakened: every `α > 0` (excess angles too); and the 2+1 `E_α` |
| Hörmann: `L∞` metric, `C¹` timelike curves; Cauchy = met once by timelike inextendible curves | ⚠ reading: ETT's curves (DEC-6; `Causal.Static`'s 1-Lipschitz graphs), Cauchy surfaces met once by every inextensible **causal** curve (DEC-14), inextensibility by extension (DEC-11, DEC-13) |
| Ellis–Schmidt: the singular set deleted | ✓ the open set `ℝ × (C_α \ {apex})` with `massive α` (kb/0001) |
| Vickers–Wilson: the past null cone of an axis point | ✓ `J⁻`, `I⁻`, `J⁻ \ I⁻` on `{t = 0}` |
| target: GH and the Cauchy surface as the ladder's definitions | ✓ `Causality.GloballyHyperbolic`, `Causality.IsCauchySurface`, `IsCauchySurfaceOn` |

## SCOPE (disclosed)

* **"E_α × ℝ"** is read by the dispatch as `Massive α = ℝ_t × C_α` (ETT's 2+1 `E_α`); Hörmann's and
  Vickers–Wilson's spacetime is `E_α × ℝ_z` (3+1). Both readings are proved; the 3+1 one uses the
  `L²` product `WithLp 2 (C_α × ℝ)`, proper and geodesic (`properSpace_withLpTwo`,
  `GeodesicSpace.withLpTwo`), and Hörmann's `α_H` is `α / 2π` here.
* The Colombeau / `L∞` notions of the sources (generalized curves, Clarke's `□`-hyperbolicity) are
  not formalized; the statements here are ETT's, which keep the axis as points.
* "The axis removed" is the causality of `E_α` on `reg(E_α)` (`IsCauchySurfaceOn`,
  `GloballyHyperbolicOn`): curves and extensions inside `reg`. Since `≤_U` is defined by curves in
  `U`, this is the causality built from `reg`'s own curves.
* (3) "through axis points" is read as `x` on the axis; the formula for every `x` and the
  decomposition through the axis are given too. The decomposition does not claim its second part
  is needed (for `α < 2π` the regular past may already contain every regular point).
* `Causality.inextensible_Iio_of_tendsto_not_mem` is model-free (an ETT-layer candidate, kb/0047).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Metric

/-! ### A model-free lemma: a causal curve of `W` running out of `W` in finite time -/

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-- A causal curve of the open set `W` over `]-∞, b[` which tends, at its future end, to a point
`P ∉ W`, and along which a function non-decreasing for `≤_W` is unbounded below, is inextensible
in `W`. A strict extension adds a value before the curve (excluded by `f`), between two of its
values (then it is one of them), or after it: then the new curve passes through the limit of the
old one at the supremum of the reparametrised domain, which is `P ∉ W`. -/
theorem inextensible_Iio_of_tendsto_not_mem [T2Space M] {W : Opens M} {b : ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W (Iio b) c) {P : M} (hP : P ∉ W)
    (hlim : Tendsto c (𝓝[<] b) (𝓝 P)) {f : M → ℝ} (hf : ∀ x y, C.le W x y → f x ≤ f y)
    (hbot : ∀ B, ∃ s < b, f (c s) < B) : C.Inextensible W (Iio b) c := by
  refine ⟨hc, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, hφmono, hφmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩
  have hb1 : b - 1 ∈ Iio b := by simp
  by_cases h1 : ∃ s ∈ Iio b, t' ≤ φ s
  · by_cases h2 : ∃ s ∈ Iio b, φ s ≤ t'
    · -- the new value lies between two old ones: it is an old one
      obtain ⟨s₁, hs₁, h₁⟩ := h1
      obtain ⟨s₂, hs₂, h₂⟩ := h2
      obtain ⟨s, hs, hseq⟩ := hφoc.out (mem_image_of_mem φ hs₂) (mem_image_of_mem φ hs₁) ⟨h₂, h₁⟩
      exact hgrow s hs (by rw [← hseq, hφeq s hs])
    · -- the new value comes before the whole curve: `f` is unbounded below along it
      simp only [not_exists, not_and, not_le] at h2
      obtain ⟨s, hs, hfs⟩ := hbot (f (c' t'))
      have := hf _ _ (hcurve.le_of_le ht' (hφmaps hs) (h2 s hs).le)
      rw [hφeq s hs] at this
      linarith
  · -- the new value comes after the whole curve: the new curve passes through the limit `P`
    simp only [not_exists, not_and, not_le] at h1
    have hne : (φ '' Iio b).Nonempty := ⟨_, mem_image_of_mem φ hb1⟩
    have hbdd : BddAbove (φ '' Iio b) := ⟨t', by rintro _ ⟨s, hs, rfl⟩; exact (h1 s hs).le⟩
    have hσt : sSup (φ '' Iio b) ≤ t' :=
      csSup_le hne (by rintro _ ⟨s, hs, rfl⟩; exact (h1 s hs).le)
    have ha : φ (b - 1) ∈ I' := hφmaps hb1
    have hle : ∀ s ∈ Iio b, φ s ≤ sSup (φ '' Iio b) := fun s hs =>
      le_csSup hbdd (mem_image_of_mem φ hs)
    have hσI : sSup (φ '' Iio b) ∈ I' := hcurve.ordConnected.out ha ht' ⟨hle _ hb1, hσt⟩
    have hφlim : Tendsto φ (𝓝[<] b)
        (𝓝[Icc (φ (b - 1)) (sSup (φ '' Iio b))] (sSup (φ '' Iio b))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · refine tendsto_order.2 ⟨fun a ha' => ?_, fun a ha' => ?_⟩
        · obtain ⟨_, ⟨s₀, hs₀, rfl⟩, has₀⟩ := exists_lt_of_lt_csSup hne ha'
          filter_upwards [Ioo_mem_nhdsLT (show s₀ < b from hs₀)] with s hs
          exact has₀.trans (hφmono hs₀ hs.2 hs.1)
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact (hle s hs).trans_lt ha'
      · filter_upwards [Ioo_mem_nhdsLT (show b - 1 < b by linarith)] with s hs
        exact ⟨(hφmono hb1 hs.2 hs.1).le, hle s hs.2⟩
    have hcont : ContinuousWithinAt c' (Icc (φ (b - 1)) (sSup (φ '' Iio b)))
        (sSup (φ '' Iio b)) :=
      CurveOn.continuousOn C.isRelFamily_le (hcurve.curve _ ha _ hσI) _ ⟨hle _ hb1, le_rfl⟩
    have hlim' : Tendsto c (𝓝[<] b) (𝓝 (c' (sSup (φ '' Iio b)))) := by
      refine (hcont.tendsto.comp hφlim).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs using hφeq s hs
    have hP' := tendsto_nhds_unique hlim' hlim
    exact hP (hP' ▸ hcurve.mem hσI)

end Causality

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

/-! ### (1)–(4) for `E_α = ℝ × C_α` -/

variable {α : ℝ} [Fact (0 < α)]

/-- `t − t₀` is a Cauchy time function of `E_α`. -/
theorem massive_isCauchyTimeFunction_sub (t₀ : ℝ) :
    (massive α).IsCauchyTimeFunction fun p => p.1 - t₀ :=
  staticCausality.isCauchyTimeFunction_sub_const t₀

/-- **Every slice `{t = t₀}` of `E_α` is a Cauchy surface.** -/
theorem massive_isCauchySurface_slice (t₀ : ℝ) :
    (massive α).IsCauchySurface {p : Massive α | p.1 = t₀} :=
  staticCausality.isCauchySurface_slice t₀

/-- **`{t = 0}` is a Cauchy surface of `E_α`.** -/
theorem massive_isCauchySurface_zero : (massive α).IsCauchySurface {p : Massive α | p.1 = 0} :=
  massive_isCauchySurface_slice 0

/-- **`E_α` is globally hyperbolic and `{t = 0}` is a Cauchy surface.** -/
theorem massive_globallyHyperbolic_isCauchySurface :
    (massive α).GloballyHyperbolic ∧ (massive α).IsCauchySurface {p : Massive α | p.1 = 0} :=
  ⟨massive_globallyHyperbolic, massive_isCauchySurface_zero⟩

/-- The axis, run over `ℝ`, is an inextensible causal curve of `E_α`. -/
theorem massive_inextensible_singLine :
    (massive α).Inextensible ⊤ univ (fun τ => ((τ, Cone.apex) : Massive α)) :=
  Causality.inextensible_of_unbounded (f := Prod.fst) (fun _ _ h => (staticCausality.le_iff.1 h).1)
    ⟨⟨0, trivial⟩, ordConnected_univ, fun _ _ _ _ =>
      (singLine_chronalCurveOn (W := ⊤) fun _ _ => trivial).causalCurveOn⟩
    (fun B => ⟨B + 1, by simp⟩) (fun B => ⟨B - 1, by simp⟩)

omit [Fact (0 < α)] in
/-- The axis meets the slice `{t = t₀}` in exactly the point `(t₀, apex)`. -/
theorem singLine_inter_slice (t₀ : ℝ) :
    singLine α ∩ {p : Massive α | p.1 = t₀} = {((t₀, Cone.apex) : Massive α)} := by
  ext p
  simp only [singLine, mem_inter_iff, mem_setOf_eq, mem_singleton_iff, Prod.ext_iff]
  tauto

/-! #### The ladder's side conditions, instantiated for `E_α` -/

theorem massive_noCausalEndpoint : (massive α).NoCausalEndpoint := staticCausality.noCausalEndpoint

theorem massive_chronalNeighbours : (massive α).ChronalNeighbours :=
  staticCausality.chronalNeighbours

theorem massive_causallyOpen : (massive α).CausallyOpen := staticCausality.causallyOpen

theorem massive_causallyOpenFuture : (massive α).CausallyOpenFuture :=
  massive_causallyOpen.future

theorem massive_stronglyCausalOpen : (massive α).StronglyCausalOpen :=
  staticCausality.stronglyCausalOpen

theorem massive_locallyPushUp : (massive α).LocallyPushUp := massive_pushUp.locallyPushUp

theorem massive_causallyCompact : (massive α).CausallyCompact :=
  massive_globallyHyperbolic.causallyCompact

theorem massive_hasTimeFunction : (massive α).HasTimeFunction := staticCausality.hasTimeFunction

theorem massive_curvesExtend : (massive α).CurvesExtend := staticCausality.curvesExtend

/-! #### The axis removed -/

omit [Fact (0 < α)] in
theorem isOpen_regPart : IsOpen (regPart α) :=
  (isClosed_eq continuous_snd continuous_const).isOpen_compl

/-- The regular part `reg(E_α)`, as an open set: `ℝ × (C_α \ {apex})`. -/
noncomputable def regOpens (α : ℝ) : Opens (Massive α) :=
  staticCausality.offOpens (isClosed_singleton (x := (Cone.apex : Cone α)))

omit [Fact (0 < α)] in
theorem coe_regOpens : (regOpens α : Set (Massive α)) = regPart α := rfl

/-- The point of radius `max u 0` on the ray of direction `0` of `C_α`. -/
noncomputable def massiveRadial (u : ℝ) : Cone α := Cone.polar (u, 0)

omit [Fact (0 < α)] in
/-- Two points of one ray are at the distance of their radii. -/
theorem dist_massiveRadial (u v : ℝ) :
    dist (massiveRadial (α := α) u) (massiveRadial v) = |max u 0 - max v 0| :=
  ConePoint.dist_same_dir (p := ConePoint.of u 0) (q := ConePoint.of v 0) rfl

omit [Fact (0 < α)] in
theorem dist_massiveRadial_le (u v : ℝ) :
    dist (massiveRadial (α := α) u) (massiveRadial v) ≤ |u - v| := by
  rw [dist_massiveRadial]; exact abs_max_sub_max_le_abs u v 0

omit [Fact (0 < α)] in
theorem rad_massiveRadial (u : ℝ) : Cone.rad (massiveRadial (α := α) u) = max u 0 :=
  Cone.rad_mk _

omit [Fact (0 < α)] in
theorem massiveRadial_eq_apex_iff {u : ℝ} : massiveRadial (α := α) u = Cone.apex ↔ u ≤ 0 := by
  rw [← Cone.rad_eq_zero, rad_massiveRadial, max_eq_right_iff]

omit [Fact (0 < α)] in
/-- The ray of direction `0` of `C_α` reaches the apex. -/
theorem massiveRadial_isRayTo :
    staticCausality.IsRayTo ({Cone.apex} : Set (Cone α)) (massiveRadial (α := α)) :=
  ⟨dist_massiveRadial_le, massiveRadial_eq_apex_iff.2 le_rfl,
    fun _ hu h => not_le.2 hu (massiveRadial_eq_apex_iff.1 h)⟩

/-- **The witness**: the curve falling radially into the axis at speed `1/2`, reaching it at time
`t₀`, is an inextensible causal curve of `reg(E_α)`, chronal on every segment, missing
`{t = t₀}`. -/
theorem massive_infall (t₀ : ℝ) :
    (massive α).Inextensible (regOpens α) (Iio t₀)
        (staticCausality.rayCurve massiveRadial fun τ => (t₀ - τ) / 2) ∧
      (∀ a < t₀, ∀ b < t₀, (massive α).ChronalCurveOn (regOpens α)
        (staticCausality.rayCurve massiveRadial fun τ => (t₀ - τ) / 2) a b) ∧
      ∀ τ < t₀, (staticCausality.rayCurve (massiveRadial (α := α))
        (fun τ => (t₀ - τ) / 2) τ).1 ≠ t₀ :=
  massiveRadial_isRayTo.infall isClosed_singleton t₀

/-- **No subset of a slice `{t = t₀}` is a Cauchy surface of `reg(E_α)`.** -/
theorem not_isCauchySurfaceOn_regOpens_of_subset_slice (t₀ : ℝ) {S : Set (Massive α)}
    (hS : S ⊆ {p | p.1 = t₀}) : ¬ (massive α).IsCauchySurfaceOn (regOpens α) S :=
  massiveRadial_isRayTo.not_isCauchySurfaceOn_of_subset_slice isClosed_singleton t₀ hS

/-- **`{t = 0} ∩ reg(E_α)` is not a Cauchy surface of `reg(E_α)`.** -/
theorem not_isCauchySurfaceOn_regOpens_slice :
    ¬ (massive α).IsCauchySurfaceOn (regOpens α) ({p : Massive α | p.1 = 0} ∩ regPart α) :=
  not_isCauchySurfaceOn_regOpens_of_subset_slice 0 inter_subset_left

/-- **`reg(E_α)` has no Cauchy surface at all** (Ellis–Schmidt). -/
theorem not_exists_isCauchySurfaceOn_regOpens :
    ¬ ∃ S : Set (Massive α), (massive α).IsCauchySurfaceOn (regOpens α) S :=
  massiveRadial_isRayTo.not_exists_isCauchySurfaceOn isClosed_singleton

/-- **`reg(E_α)` is not globally hyperbolic.** -/
theorem not_globallyHyperbolicOn_regOpens : ¬ (massive α).GloballyHyperbolicOn (regOpens α) :=
  massiveRadial_isRayTo.not_globallyHyperbolicOn isClosed_singleton

/-! #### `J⁻(x) ∩ {t = t₁}` through the axis -/

/-- `J⁻(x) ∩ {t = t₁}` is the closed ball of radius `x.1 − t₁` of `C_α` about `x.2`. -/
theorem massive_Jminus_inter_slice (x : Massive α) (t₁ : ℝ) :
    (massive α).Jminus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (x.1 - t₁) :=
  staticCausality.Jminus_inter_slice x t₁

/-- `J⁺(x) ∩ {t = t₁}` is the closed ball of radius `t₁ − x.1` of `C_α` about `x.2`. -/
theorem massive_Jplus_inter_slice (x : Massive α) (t₁ : ℝ) :
    (massive α).Jplus ⊤ {x} ∩ {p | p.1 = t₁} = {t₁} ×ˢ closedBall x.2 (t₁ - x.1) :=
  staticCausality.Jplus_inter_slice x t₁

/-- **Through an axis point `x = (t₀, apex)`: `J⁻(x) ∩ {t = 0} = {t = 0, r ≤ t₀}`**, the disc of
radius `t₀` about the axis. -/
theorem massive_Jminus_axis_inter_slice (t₀ : ℝ) :
    (massive α).Jminus ⊤ {((t₀, Cone.apex) : Massive α)} ∩ {p | p.1 = 0} =
      {p : Massive α | p.1 = 0 ∧ Cone.rad p.2 ≤ t₀} := by
  rw [massive_Jminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_closedBall, mem_setOf_eq, Cone.rad,
    dist_comm Cone.apex p.2, sub_zero]

/-- **The past null cone of an axis point on `{t = 0}` is the circle `r = t₀`** (Vickers–Wilson's
"usual Minkowskian formula"). -/
theorem massive_nullCone_axis_inter_slice (t₀ : ℝ) :
    ((massive α).Jminus ⊤ {((t₀, Cone.apex) : Massive α)} \
        (massive α).Iminus ⊤ {((t₀, Cone.apex) : Massive α)}) ∩ {p | p.1 = 0} =
      {p : Massive α | p.1 = 0 ∧ Cone.rad p.2 = t₀} := by
  rw [staticCausality.Jminus_diff_Iminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_sphere, mem_setOf_eq, Cone.rad,
    dist_comm Cone.apex p.2, sub_zero]

/-- `J^±(x) ∩ {t = t₁}` is compact. -/
theorem isCompact_massive_Jminus_inter_slice (x : Massive α) (t₁ : ℝ) :
    IsCompact ((massive α).Jminus ⊤ {x} ∩ {p | p.1 = t₁}) ∧
      IsCompact ((massive α).Jplus ⊤ {x} ∩ {p | p.1 = t₁}) :=
  staticCausality.isCompact_Jminus_inter_slice x t₁

/-- **A causal past is the regular causal past plus the pasts of its axis points**: every
`z ≤ x` is joined to `x` in `reg(E_α)`, or through a point `ξ` of the axis with `z ≤ ξ ≤ x`. -/
theorem massive_Jminus_eq_reg_union_axis (x : Massive α) :
    (massive α).Jminus ⊤ {x} = (massive α).Jminus (regOpens α) {x} ∪
      ⋃ ξ ∈ (massive α).Jminus ⊤ {x} ∩ singLine α, (massive α).Jminus ⊤ {ξ} :=
  staticCausality.Jminus_eq_off_union isClosed_singleton x

/-! ### The 3+1 conical spacetime `ℝ_t × C_α × ℝ_z` (Hörmann, Vickers–Wilson) -/

section WithLpTwo

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The `L²` product distance. -/
theorem withLp_dist_two (f g : WithLp 2 (X × Y)) :
    dist f g = √(dist f.fst g.fst ^ 2 + dist f.snd g.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num), ENNReal.toReal_ofNat, Real.rpow_two, Real.rpow_two,
    Real.sqrt_eq_rpow]

theorem withLp_dist_fst_le (f g : WithLp 2 (X × Y)) : dist f.fst g.fst ≤ dist f g := by
  rw [withLp_dist_two]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (dist f.snd g.snd)]))

theorem withLp_dist_snd_le (f g : WithLp 2 (X × Y)) : dist f.snd g.snd ≤ dist f g := by
  rw [withLp_dist_two]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (dist f.fst g.fst)]))

/-- The `L²` product of two geodesic spaces is geodesic: run both geodesics at once. -/
instance GeodesicSpace.withLpTwo [GeodesicSpace X] [GeodesicSpace Y] :
    GeodesicSpace (WithLp 2 (X × Y)) where
  exists_geodesic x y := by
    obtain ⟨g₁, h₁0, h₁1, h₁⟩ := GeodesicSpace.exists_geodesic x.fst y.fst
    obtain ⟨g₂, h₂0, h₂1, h₂⟩ := GeodesicSpace.exists_geodesic x.snd y.snd
    have hx : WithLp.toLp 2 (x.fst, x.snd) = x := rfl
    have hy : WithLp.toLp 2 (y.fst, y.snd) = y := rfl
    refine ⟨fun s => WithLp.toLp 2 (g₁ s, g₂ s), ?_, ?_, fun s hs s' hs' => ?_⟩
    · show WithLp.toLp 2 (g₁ 0, g₂ 0) = x
      rw [h₁0, h₂0, hx]
    · show WithLp.toLp 2 (g₁ 1, g₂ 1) = y
      rw [h₁1, h₂1, hy]
    · rw [withLp_dist_two, withLp_dist_two]
      show √(dist (g₁ s) (g₁ s') ^ 2 + dist (g₂ s) (g₂ s') ^ 2) =
        |s - s'| * √(dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2)
      rw [h₁ s hs s' hs', h₂ s hs s' hs', mul_pow, mul_pow, ← mul_add,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]

/-- The `L²` product of two proper spaces is proper. -/
instance properSpace_withLpTwo [ProperSpace X] [ProperSpace Y] :
    ProperSpace (WithLp 2 (X × Y)) := by
  refine ⟨fun x R => ?_⟩
  have hK : IsCompact (WithLp.toLp 2 '' (closedBall x.fst R ×ˢ closedBall x.snd R)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      (WithLp.prod_continuous_toLp _ _ _)
  refine hK.of_isClosed_subset isClosed_closedBall fun y hy => ⟨(y.fst, y.snd), ⟨?_, ?_⟩, rfl⟩
  · rw [mem_closedBall] at hy ⊢; exact (withLp_dist_fst_le y x).trans hy
  · rw [mem_closedBall] at hy ⊢; exact (withLp_dist_snd_le y x).trans hy

end WithLpTwo

/-- The space of the 3+1 conical spacetime: `C_α × ℝ_z` with the `L²` product metric, the length
metric of `dr² + r² dθ² + dz²`. -/
abbrev StringSpace (α : ℝ) : Type := WithLp 2 (Cone α × ℝ)

/-- **The conical spacetime of a straight cosmic string**, `E_α × ℝ_z = ℝ_t × C_α × ℝ_z`, metric
`−dt² + dr² + r² dθ² + dz²` (Hörmann's `lα` with total angle `α = 2π α_H`). -/
abbrev CosmicString (α : ℝ) : Type := ℝ × StringSpace α

/-- Its causality: the static causality over `StringSpace α` (`defi:causal_Ealpha`'s
construction). -/
noncomputable abbrev cosmicString (α : ℝ) [Fact (0 < α)] : Causality (CosmicString α) :=
  staticCausality (StringSpace α)

/-- The axis `{r = 0}` of `StringSpace α`; the string's world-sheet is `ℝ × stringAxis α`. -/
def stringAxis (α : ℝ) : Set (StringSpace α) := {w | w.fst = Cone.apex}

omit [Fact (0 < α)] in
theorem isClosed_stringAxis : IsClosed (stringAxis α) :=
  isClosed_eq (WithLp.continuous_fst _ _ _) continuous_const

/-- The conical spacetime with the world-sheet of the string removed, as an open set. -/
noncomputable def stringOffAxis (α : ℝ) : Opens (CosmicString α) :=
  staticCausality.offOpens isClosed_stringAxis

/-- The ray of direction `0` at height `z = 0`. -/
noncomputable def stringRadial (u : ℝ) : StringSpace α := WithLp.toLp 2 (massiveRadial u, 0)

omit [Fact (0 < α)] in
theorem stringRadial_isRayTo : staticCausality.IsRayTo (stringAxis α) (stringRadial (α := α)) := by
  refine ⟨fun u v => ?_, massiveRadial_eq_apex_iff.2 le_rfl,
    fun _ hu h => not_le.2 hu (massiveRadial_eq_apex_iff.1 h)⟩
  rw [withLp_dist_two]
  show √(dist (massiveRadial (α := α) u) (massiveRadial v) ^ 2 + dist (0 : ℝ) 0 ^ 2) ≤ |u - v|
  rw [dist_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq dist_nonneg]
  exact dist_massiveRadial_le u v

/-- **The conical spacetime is globally hyperbolic and every slice is a Cauchy surface**, with the
string kept (Hörmann's "`{t} × ℝ³` is a Cauchy hypersurface"). -/
theorem cosmicString_globallyHyperbolic_isCauchySurface (t₀ : ℝ) :
    (cosmicString α).GloballyHyperbolic ∧
      (cosmicString α).IsCauchySurface {p : CosmicString α | p.1 = t₀} :=
  ⟨staticCausality.globallyHyperbolic, staticCausality.isCauchySurface_slice t₀⟩

/-- With the string removed, `{t = 0}` minus the string is not a Cauchy surface. -/
theorem cosmicString_not_isCauchySurfaceOn_offAxis_slice :
    ¬ (cosmicString α).IsCauchySurfaceOn (stringOffAxis α)
      ({p : CosmicString α | p.1 = 0} ∩ stringOffAxis α) :=
  stringRadial_isRayTo.not_isCauchySurfaceOn_of_subset_slice isClosed_stringAxis 0
    inter_subset_left

/-- **With the string removed there is no Cauchy surface at all** (Ellis–Schmidt). -/
theorem cosmicString_not_exists_isCauchySurfaceOn_offAxis :
    ¬ ∃ S : Set (CosmicString α), (cosmicString α).IsCauchySurfaceOn (stringOffAxis α) S :=
  stringRadial_isRayTo.not_exists_isCauchySurfaceOn isClosed_stringAxis

/-- With the string removed the spacetime is not globally hyperbolic. -/
theorem cosmicString_not_globallyHyperbolicOn_offAxis :
    ¬ (cosmicString α).GloballyHyperbolicOn (stringOffAxis α) :=
  stringRadial_isRayTo.not_globallyHyperbolicOn isClosed_stringAxis

/-- **Through a point `(t₀, apex, z₀)` of the string: `J⁻ ∩ {t = 0}` is the Minkowskian ball
`r² + (z − z₀)² ≤ t₀²`** (Vickers–Wilson's "usual Minkowskian formula"). -/
theorem cosmicString_Jminus_axis_inter_slice (t₀ z₀ : ℝ) :
    (cosmicString α).Jminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)} ∩
        {p | p.1 = 0} =
      {p : CosmicString α | p.1 = 0 ∧ 0 ≤ t₀ ∧ Cone.rad p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 ≤ t₀ ^ 2} := by
  rw [staticCausality.Jminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_closedBall, mem_setOf_eq, sub_zero]
  rw [withLp_dist_two]
  show p.1 = 0 ∧ √(dist p.2.fst Cone.apex ^ 2 + dist p.2.snd z₀ ^ 2) ≤ t₀ ↔
    p.1 = 0 ∧ 0 ≤ t₀ ∧ dist Cone.apex p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 ≤ t₀ ^ 2
  rw [Real.sqrt_le_iff, dist_comm p.2.fst, Real.dist_eq, sq_abs]

/-- The past null cone of a point of the string on `{t = 0}`: the sphere
`r² + (z − z₀)² = t₀²`, `t₀ ≥ 0`. -/
theorem cosmicString_nullCone_axis_inter_slice (t₀ z₀ : ℝ) :
    ((cosmicString α).Jminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)} \
        (cosmicString α).Iminus ⊤ {((t₀, WithLp.toLp 2 (Cone.apex, z₀)) : CosmicString α)}) ∩
        {p | p.1 = 0} =
      {p : CosmicString α | p.1 = 0 ∧ 0 ≤ t₀ ∧ Cone.rad p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 = t₀ ^ 2} := by
  rw [staticCausality.Jminus_diff_Iminus_inter_slice]
  ext p
  simp only [mem_prod, mem_singleton_iff, mem_sphere, mem_setOf_eq, sub_zero]
  rw [withLp_dist_two]
  show p.1 = 0 ∧ √(dist p.2.fst Cone.apex ^ 2 + dist p.2.snd z₀ ^ 2) = t₀ ↔
    p.1 = 0 ∧ 0 ≤ t₀ ∧ dist Cone.apex p.2.fst ^ 2 + (p.2.snd - z₀) ^ 2 = t₀ ^ 2
  rw [dist_comm p.2.fst Cone.apex, Real.dist_eq, sq_abs]
  constructor
  · rintro ⟨h1, h⟩
    have ht : 0 ≤ t₀ := h ▸ Real.sqrt_nonneg _
    exact ⟨h1, ht, (Real.sqrt_eq_iff_eq_sq (by positivity) ht).1 h⟩
  · rintro ⟨h1, ht, h⟩
    exact ⟨h1, (Real.sqrt_eq_iff_eq_sq (by positivity) ht).2 h⟩

/-- A causal past of the conical spacetime is its part off the string plus the pasts of its
points on the string. -/
theorem cosmicString_Jminus_eq_offAxis_union (x : CosmicString α) :
    (cosmicString α).Jminus ⊤ {x} = (cosmicString α).Jminus (stringOffAxis α) {x} ∪
      ⋃ ξ ∈ (cosmicString α).Jminus ⊤ {x} ∩ {p | p.2 ∈ stringAxis α},
        (cosmicString α).Jminus ⊤ {ξ} :=
  staticCausality.Jminus_eq_off_union isClosed_stringAxis x

/-! #### The ladder's properties, instantiated for the conical spacetime -/

theorem cosmicString_isCausal : (cosmicString α).IsCausal := staticCausality.isCausal
theorem cosmicString_stronglyCausal : (cosmicString α).StronglyCausal :=
  staticCausality.stronglyCausal
theorem cosmicString_stronglyCausalOpen : (cosmicString α).StronglyCausalOpen :=
  staticCausality.stronglyCausalOpen
theorem cosmicString_globallyHyperbolic : (cosmicString α).GloballyHyperbolic :=
  staticCausality.globallyHyperbolic
theorem cosmicString_pushUp : (cosmicString α).PushUp := staticCausality.pushUp
theorem cosmicString_causallyOpen : (cosmicString α).CausallyOpen := staticCausality.causallyOpen
theorem cosmicString_causallyOpenFuture : (cosmicString α).CausallyOpenFuture :=
  cosmicString_causallyOpen.future
theorem cosmicString_absolutelyMinimal : (cosmicString α).AbsolutelyMinimal :=
  staticCausality.absolutelyMinimal
theorem cosmicString_causallyArcConnected : (cosmicString α).CausallyArcConnected :=
  staticCausality.causallyArcConnected
theorem cosmicString_tarentin : (cosmicString α).Tarentin := staticCausality.tarentin
theorem cosmicString_hasTimeFunction : (cosmicString α).HasTimeFunction :=
  staticCausality.hasTimeFunction
theorem cosmicString_curvesExtend : (cosmicString α).CurvesExtend := staticCausality.curvesExtend
theorem cosmicString_noCausalEndpoint : (cosmicString α).NoCausalEndpoint :=
  staticCausality.noCausalEndpoint
theorem cosmicString_chronalNeighbours : (cosmicString α).ChronalNeighbours :=
  staticCausality.chronalNeighbours

end Causal
