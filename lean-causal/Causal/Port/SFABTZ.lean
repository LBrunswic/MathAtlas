import Causal.Port.SFALocal

/-!
# `SingularFlatAxioms`' BTZ fields `singularPastAt` and `Iplus_of_lt` at every `E_{≥0}`-manifold

Target `T-ett-sfa-btz-e0`. Cited, **unmarked** (SCOPE): `defi:causal_E0` — `ETT.tex:1344`. For a
singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25) and every absolutely minimal causality `C` with an
isomorphic chart at each point over the family `E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`,
the hypotheses of `Causal.SFALocal`), the two fields of `Causal.Causality.BTZAxioms` that are global
statements on `M`: at every BTZ point `p ∈ sing₀(M)`, `p` is approached from below along `sing₀(M)`
(`Causal.Causality.SingularPastAt`), and for `p < p′` on the BTZ points the regular part of `J⁺(p′)`
lies in `I⁺(p)` (DEC-64's corrected form of l.1352–1355). Their `E₀`-manifold forms are
corollaries (`SFALocal.sing_eq_of_e0Covered`, `SFALocal.isoChartsCoverDEC25_of_e0`).

> For $\alpha=0$ the singular line is lightlike: locally causal, but not locally chronal. More
> precisely \cite[Section~1.2]{brunswic2021cauchy}, for a singular point $p\in \sing(\mass{0})$,
> $$I^-(p)=\emptyset \qquad\text{and}\qquad J^-(p)=\{\r=0,~\tau\leq \tau(p)\},$$
> that is, the causal past of $p$ is exactly the singular half-line below $p$. In particular a BTZ
> point is strongly tarentin in the future but not in the past, and a $\mass{\geq0}$-manifold with at
> least one extreme BTZ white hole is not past distinguishing.
>
> Dually, the chronological future of a BTZ point $p$ is
> $$I^+(p)=\reg\left(J^+(p)\right)=J^+(p)\setminus \sing_0\left(\mass{0}\right):$$
> every non-BTZ point of the causal future of $p$ lies in its chronological future.
> (`ETT.tex:1344–1356`; l.1351, in the source: "quoted from \cite{thesis}, where it is asserted
> without proof -- verify")

## What is proved (no `sorry` in this file)

* **`E₀` in a ball centred on the axis** (`le_ballOpens_iff`, `lt_ballOpens_iff`): in the ball
  `B(a, δ)`, `a` on the axis, `≤_B` and `≪_B` are `E₀`'s global `Le`, `Lt` (balls on the axis are
  order-convex, `E0.mem_ball_of_le_of_le`). Through a chart isomorphism the same holds on the part
  of the source over the ball (`ballSource`, `le_ballSource_iff`, `lt_ballSource_iff`); hence the
  local forms of the model facts used: axis points in the order of `τ` (`le_of_axis`), and
  `y ∈ Int J⁺(u)` for `u` over the axis with `f(y) > τ(u)` (`mem_interior_Jplus`).
* **At a BTZ point of `M`** (`exists_chart`): a chart into `E₀` that is a `ChartIso`, with a ball
  about the image in its target; `sing₀(M)` read in it as the axis (`mem_sing_zero_iff`). `M` is T1
  and first countable (`t1Space_of_isoChartsCover`, `firstCountableTopology_of_isoChartsCover`).
* **`J⁻(p) ⊆ sing₀(M)`** at a BTZ point, inside the component of `p` (`mem_sing_zero_of_le`,
  `Jminus_subset_component`): causal arc-connectedness and `Causality.mem_of_causalCurveOn`, no
  induction on chains.
* **A causal curve at a BTZ point**: it leaves `x` up the axis of a chart at `x`
  (`exists_above`), and reaches `q` from below along the axis of a chart at `q`
  (`exists_below`); the BTZ points of a chart ball at `x` below `u` lie in `J⁻(u)`
  (`exists_open_inter_sing_subset`); axis sequences (`exists_axis_seq`).
* **The two fields**: `singularPastAt`, `Iplus_of_lt` (DEC-64), for every `E_{≥0}`-manifold, `M`
  causal or not. Assembled: `btzAxioms_but_line`, `btzAxioms_of_line` (`BTZAxioms (sing₀ M)` from
  the field `line`), `singularFlatAxioms_iff_lines` (T2, second countable: `SingularFlatAxioms`
  iff `line` and `massive_line`). `E₀`-manifolds: `singularPastAt_e0`, `Iplus_of_lt_e0`,
  `singularFlatAxioms_iff_line_e0` (iff `line`).
* **Corollaries beyond the target**, unmarked: `K_calcul` (`prop:K_calcul` at every
  `E_{≥0}`-manifold) and `K_monotone` (`prop:K_monotone` at every causal one), from
  `Causality.K_calcul`, `Causality.K_monotone`; neither needs `line`.
* **Witness** (kb/0011): `nonvacuous_e0`, at `M = E₀` (`sing₀ = axis ≠ ∅`), the two fields coming
  out of this file's theorems.

## Hypothesis checklist

| paper | here |
|---|---|
| a BTZ point of an `E_{≥0}`-manifold (the fields are used at `M`: `prop:K_calcul` l.1565–1573, `prop:K_densite_sing` l.1663–1669) | ⚠ read (DEC-25): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `p ∈ SFALocal.sing M 0` (an `X_A`-chart into `E₀` sends `p` to the axis) |
| its causality (`defi:causal_Ealpha`, l.1339–1340) | ⚠ read (OQ-18): absolutely minimal with an isomorphic chart at each point (`IsoChartsCoverDEC25`); minimality enters through causal arc-connectedness and push-up |
| Hausdorff, second countable (`ETT.tex:254`) | ⚠ weakened: not used by the fields; T1 and first countability come from the charts; carried only by `singularFlatAxioms_iff_lines`, `singularFlatAxioms_iff_line_e0` |
| `J⁻(p) = {r = 0, τ ≤ τ(p)}` (l.1347) | ⚠ read at `M`: `SingularPastAt p` (field `singularPastAt`), and `J⁻(p) ⊆` the component of `sing₀(M)` through `p` |
| `I⁺(p) = J⁺(p) ∖ sing₀` (l.1353–1355) | ✗ false (DEC-64, `E0.not_btzIplusAsPrinted`); ⚠ re-scoped, DEC-64: `Iplus_of_lt` proved |
| `E₀` (l.1330), `Isom(𝔼^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** The label is a statement about the model `E₀`, whose readings are open
  (OQ-34/OQ-35), its last sentence is false as printed (DEC-64), and at `M` the causality is
  read (OQ-18) and the group too (OQ-82). This module proves the library's two global BTZ fields at
  `M`, not the label; `Causal.E0.causal_E0` is the model form.
* **One chart at a time.** No transition between two charts is used (in particular not
  `BPrimeE0.exists_eqOn_rotE0_tauShift`): each step reads one chart into `E₀`, at `x`, at `p` or at
  the last BTZ point `q` of a curve; past `q` only push-up in `M` is used.
* **Not here**: the fields `line` and `massive_line` (`lem:past_BTZ` (a); T-ett-sfa-line-e0).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Port.SFALocal` only.
-/
namespace Causal

open Set Filter Topology TopologicalSpace

universe u

namespace SFABTZ

/-! ### `E₀`: a ball centred on the axis computes the relations of `E₀` -/

section Ball

/-- A ball of `E₀`, as an open set. -/
def ballOpens (a : E0) (δ : ℝ) : Opens E0 := ⟨Metric.ball a δ, Metric.isOpen_ball⟩

/-- **In a ball of `E₀` centred on the axis, `≤` is `E₀`'s global `Le`**: the straight segment
of a pair of developments stays in the ball, which is order-convex. -/
theorem le_ballOpens_iff {a : E0} (ha : a ∈ E0.axis) {δ : ℝ} {y z : E0}
    (hy : y ∈ Metric.ball a δ) (hz : z ∈ Metric.ball a δ) :
    E0.causality.le (ballOpens a δ) y z ↔ E0.Le y z := by
  refine ⟨fun h => E0.le_of_le h, fun ⟨θ₁, θ₂, h₁, h₂, hc⟩ => ?_⟩
  refine E0.cle_of_seg h₁ h₂ hc fun s hs => ?_
  have hends := E0.le_seg_ends (E0.adm_lift y θ₁) hc hs
  rw [E0.unlift_lift h₁, E0.unlift_lift h₂] at hends
  exact E0.mem_ball_of_le_of_le ha hends.1 hends.2 hy hz

/-- **In a ball of `E₀` centred on the axis, `≪` is `E₀`'s global `Lt`.** -/
theorem lt_ballOpens_iff {a : E0} (ha : a ∈ E0.axis) {δ : ℝ} {y z : E0}
    (hy : y ∈ Metric.ball a δ) (hz : z ∈ Metric.ball a δ) :
    E0.causality.lt (ballOpens a δ) y z ↔ E0.Lt y z := by
  refine ⟨fun h => E0.lt_of_lt h, fun ⟨θ₁, θ₂, h₁, h₂, hc⟩ => ?_⟩
  refine E0.clt_of_seg h₁ h₂ hc fun s hs => ?_
  have hends := E0.le_seg_ends (E0.adm_lift y θ₁) hc.nullCone hs
  rw [E0.unlift_lift h₁, E0.unlift_lift h₂] at hends
  exact E0.mem_ball_of_le_of_le ha hends.1 hends.2 hy hz

end Ball

/-! ### Separation from the charts -/

section T1

variable {M : Type u} [TopologicalSpace M]

/-- A point in the source of a chart into a T1 space is separated from every other point. -/
theorem exists_open_of_chart {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (e : OpenPartialHomeomorph M Y) {x y : M} (hx : x ∈ e.source) (hxy : x ≠ y) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ y ∉ U := by
  by_cases hy : y ∈ e.source
  · exact ⟨e.source ∩ e ⁻¹' {e y}ᶜ, e.isOpen_inter_preimage isOpen_compl_singleton,
      ⟨hx, fun h => hxy (e.injOn hx hy h)⟩, fun h => h.2 rfl⟩
  · exact ⟨e.source, e.open_source, hx, hy⟩

/-- The models of the family are T1. -/
theorem massAModel_t1Space : ∀ o, T1Space (MassAModel o)
  | none => inferInstanceAs (T1Space E0)
  | some κ => inferInstanceAs (T1Space (Massive κ.1))

/-- The models of the family are first countable. -/
theorem massAModel_firstCountableTopology : ∀ o, FirstCountableTopology (MassAModel o)
  | none => inferInstanceAs (FirstCountableTopology E0)
  | some κ => inferInstanceAs (FirstCountableTopology (Massive κ.1))

/-- A point in the source of a chart into a first countable space has a countably generated
neighbourhood filter. -/
theorem isCountablyGenerated_nhds_of_chart {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y] (e : OpenPartialHomeomorph M Y) {x : M} (hx : x ∈ e.source) :
    (𝓝 x).IsCountablyGenerated := by
  rw [← e.symm_map_nhds_eq hx]
  infer_instance

end T1

/-! ### Charts into `E₀`: the part of the source over a ball -/

section BallSource

variable {M : Type u} [TopologicalSpace M]

/-- The part of a chart's source that it sends into the ball `B(a, δ)` of `E₀`. -/
def ballSource (e : OpenPartialHomeomorph M E0) (a : E0) (δ : ℝ) : Opens M :=
  ⟨e.source ∩ e ⁻¹' Metric.ball a δ, e.isOpen_inter_preimage Metric.isOpen_ball⟩

variable {e : OpenPartialHomeomorph M E0} {a : E0} {δ : ℝ} {C : Causality M}

theorem mem_ballSource {y : M} : y ∈ ballSource e a δ ↔ y ∈ e.source ∧ e y ∈ Metric.ball a δ :=
  Iff.rfl

theorem ballSource_le_chartSource : ballSource e a δ ≤ chartSource e := fun _ h => h.1

theorem chartImage_ballSource (h : Metric.ball a δ ⊆ e.target) :
    chartImage e (ballSource e a δ) = ballOpens a δ := by
  apply SetLike.coe_injective
  rw [coe_chartImage_of_le ballSource_le_chartSource]
  ext w
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact hy
  · intro hw
    refine ⟨e.symm w, ⟨e.map_target (h hw), ?_⟩, e.right_inv (h hw)⟩
    show e (e.symm w) ∈ Metric.ball a δ
    rw [e.right_inv (h hw)]
    exact hw

/-- **Through a chart isomorphism into `E₀`, `≤` over a ball centred on the axis is `E₀`'s
`Le` of the images.** -/
theorem le_ballSource_iff (hiso : ChartIso C E0.causality e) (ha : a ∈ E0.axis)
    (hB : Metric.ball a δ ⊆ e.target) {y z : M} (hy : y ∈ ballSource e a δ)
    (hz : z ∈ ballSource e a δ) :
    C.le (ballSource e a δ) y z ↔ E0.Le (e y) (e z) := by
  rw [(hiso _ ballSource_le_chartSource y hy z hz).1, chartImage_ballSource hB]
  exact le_ballOpens_iff ha hy.2 hz.2

/-- **Through a chart isomorphism into `E₀`, `≪` over a ball centred on the axis is `E₀`'s
`Lt` of the images.** -/
theorem lt_ballSource_iff (hiso : ChartIso C E0.causality e) (ha : a ∈ E0.axis)
    (hB : Metric.ball a δ ⊆ e.target) {y z : M} (hy : y ∈ ballSource e a δ)
    (hz : z ∈ ballSource e a δ) :
    C.lt (ballSource e a δ) y z ↔ E0.Lt (e y) (e z) := by
  rw [(hiso _ ballSource_le_chartSource y hy z hz).2, chartImage_ballSource hB]
  exact lt_ballOpens_iff ha hy.2 hz.2

/-- Two points over the axis of a ball, in the order of `τ`, are causally related in `M`. -/
theorem le_of_axis (hiso : ChartIso C E0.causality e) (ha : a ∈ E0.axis)
    (hB : Metric.ball a δ ⊆ e.target) {y z : M} (hy : y ∈ ballSource e a δ)
    (hz : z ∈ ballSource e a δ) (hya : e y ∈ E0.axis) (hza : e z ∈ E0.axis)
    (h : (e y).1 ≤ (e z).1) : C.le ⊤ y z :=
  C.le_mono le_top ((le_ballSource_iff hiso ha hB hy hz).2 (E0.le_axis hya hza h))

/-- **`y ∈ Int J⁺(u)` for `u` over the axis of a ball and `f(y) > τ(u)`**, the local form at a
ball of `p ∈ Int J⁺(u)` for `u` below `p` on the axis. -/
theorem mem_interior_Jplus (hiso : ChartIso C E0.causality e) (ha : a ∈ E0.axis)
    (hB : Metric.ball a δ ⊆ e.target) {u y : M} (hu : u ∈ ballSource e a δ)
    (hua : e u ∈ E0.axis) (hy : y ∈ ballSource e a δ) (h : (e u).1 < E0.fcoord (e y)) :
    y ∈ interior (C.Jplus ⊤ {u}) := by
  refine interior_maximal (t := e.source ∩ e ⁻¹' (Metric.ball a δ ∩ {w | (e u).1 < E0.fcoord w}))
    ?_ (e.isOpen_inter_preimage (Metric.isOpen_ball.inter (E0.isOpen_fcoord_gt _)))
    ⟨hy.1, hy.2, h⟩
  rintro w ⟨hw, hwB, hwf⟩
  have hwV : w ∈ ballSource e a δ := ⟨hw, hwB⟩
  exact Precausality.mem_Jplus_singleton.2 (C.le_mono le_top
    ((le_ballSource_iff hiso ha hB hu hwV).2 ((E0.le_axis_iff hua).2 hwf.le)))

/-- **The axis below a BTZ point, in a chart**: points `u_n` over the axis, `τ(u_n) ↑ τ(p)`,
non-decreasing for `≤`, each `≤ p`, `≠ p`, with `p ∈ Int J⁺(u_n)`, and above every point over the
axis of the ball with `τ ≤ τ(u_0)`. -/
theorem exists_axis_seq (hiso : ChartIso C E0.causality e) {p : M} (hpe : p ∈ e.source)
    (hpa : e p ∈ E0.axis) (hδ : 0 < δ) (hB : Metric.ball (e p) δ ⊆ e.target) {η : ℝ}
    (hη : 0 < η) (hηδ : η < δ) :
    ∃ u : ℕ → M, Tendsto u atTop (𝓝 p) ∧ (∀ m n, m ≤ n → C.le ⊤ (u m) (u n)) ∧
      (∀ n, p ∈ interior (C.Jplus ⊤ {u n})) ∧ (∀ n, C.le ⊤ (u n) p ∧ u n ≠ p) ∧
      (∀ w ∈ ballSource e (e p) δ, e w ∈ E0.axis → (e w).1 ≤ (e p).1 - η → C.le ⊤ w (u 0)) := by
  have hp0 : (e p).2 = 0 := hpa
  set t : ℕ → ℝ := fun n => (e p).1 - η / ((n : ℝ) + 1) with ht
  have htn : ∀ n, t n = (e p).1 - η / ((n : ℝ) + 1) := fun n => rfl
  have hpos : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hd : ∀ n : ℕ, 0 < η / ((n : ℝ) + 1) := fun n => div_pos hη (hpos n)
  have hdη : ∀ n : ℕ, η / ((n : ℝ) + 1) ≤ η := fun n =>
    div_le_self hη.le (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hball : ∀ n, ((t n, 0) : E0) ∈ Metric.ball (e p) δ := by
    intro n
    rw [Metric.mem_ball, Prod.dist_eq, hp0, dist_self, Real.dist_eq]
    refine max_lt ?_ hδ
    rw [htn, show (e p).1 - η / ((n : ℝ) + 1) - (e p).1 = -(η / ((n : ℝ) + 1)) by ring, abs_neg,
      abs_of_pos (hd n)]
    exact (hdη n).trans_lt hηδ
  set u : ℕ → M := fun n => e.symm (t n, 0) with hu
  have hut : ∀ n, e (u n) = (t n, 0) := fun n => e.right_inv (hB (hball n))
  have huV : ∀ n, u n ∈ ballSource e (e p) δ := fun n =>
    ⟨e.map_target (hB (hball n)), by show e (u n) ∈ Metric.ball (e p) δ; rw [hut n]; exact hball n⟩
  have hua : ∀ n, e (u n) ∈ E0.axis := fun n => by rw [hut n]; rfl
  have hpV : p ∈ ballSource e (e p) δ := ⟨hpe, Metric.mem_ball_self hδ⟩
  have hτ : ∀ n, (e (u n)).1 = t n := fun n => by rw [hut n]
  refine ⟨u, ?_, fun m n hmn => ?_, fun n => ?_, fun n => ⟨?_, fun h => ?_⟩, fun w hw hwa hwτ => ?_⟩
  · have h1 : Tendsto t atTop (𝓝 (e p).1) := by
      have h0 : Tendsto (fun n : ℕ => η * (1 / ((n : ℝ) + 1))) atTop (𝓝 (η * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at h0
      have h2 := (tendsto_const_nhds (x := (e p).1)).sub h0
      rw [sub_zero] at h2
      refine h2.congr fun n => ?_
      rw [htn]; ring
    have h3 : Tendsto (fun n => ((t n, (0 : ℂ)) : E0)) atTop (𝓝 (e p)) := by
      have := h1.prodMk_nhds (tendsto_const_nhds (x := (0 : ℂ)))
      rwa [show (((e p).1, (0 : ℂ)) : E0) = e p from Prod.ext rfl hp0.symm] at this
    have h4 := ((e.continuousAt_symm (e.map_source hpe)).tendsto).comp h3
    rwa [e.left_inv hpe] at h4
  · refine le_of_axis hiso hpa hB (huV m) (huV n) (hua m) (hua n) ?_
    rw [hτ, hτ, htn, htn]
    have : η / ((n : ℝ) + 1) ≤ η / ((m : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left hη.le (hpos m)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  · refine mem_interior_Jplus hiso hpa hB (huV n) (hua n) hpV ?_
    rw [E0.fcoord_of_axis hpa, hτ, htn]
    linarith [hd n]
  · refine le_of_axis hiso hpa hB (huV n) hpV (hua n) hpa ?_
    rw [hτ, htn]
    linarith [hd n]
  · have h1 : (e (u n)).1 = (e p).1 := by rw [h]
    rw [hτ, htn] at h1
    linarith [hd n]
  · refine le_of_axis hiso hpa hB hw (huV 0) hwa (hua 0) ?_
    rw [hτ, htn, Nat.cast_zero, zero_add, div_one]
    exact hwτ

end BallSource

/-! ### `E_{≥0}`-manifolds: charts at a BTZ point -/

section Manifold

attribute [local instance] E0GX.singularGX

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]

variable {e : OpenPartialHomeomorph M E0} {a : E0} {δ : ℝ} {C : Causality M}

/-- **`sing₀(M)` read in an `X_A`-chart into `E₀`**: a point of the source is a BTZ point iff
the chart sends it to the axis. -/
theorem mem_sing_zero_iff (he : IsAEChart (Flat.isom 2) (Minkowski 2) e) {y : M}
    (hy : y ∈ e.source) : y ∈ SFALocal.sing M 0 ↔ e y ∈ E0.axis := by
  constructor
  · exact fun h => (SFALocalE0.mem_axis_iff he hy).2 (SFALocal.sing_subset 0 h)
  · intro h
    rw [SFALocal.sing_zero_eq]
    exact ⟨e, he, hy, h⟩

/-- **A chart at a BTZ point**: into `E₀`, an `X_A`-chart and a `ChartIso`, with a ball about the
image, on the axis, inside its target (`SFALocal.exists_chartIso_e0`). -/
theorem exists_chart (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    {p : M} (hp : p ∈ SFALocal.sing M 0) :
    ∃ e : OpenPartialHomeomorph M E0, IsAEChart (Flat.isom 2) (Minkowski 2) e ∧
      ChartIso C E0.causality e ∧ p ∈ e.source ∧ e p ∈ E0.axis ∧
      ∃ δ > 0, Metric.ball (e p) δ ⊆ e.target := by
  obtain ⟨e, he, hpe, hiso⟩ := SFALocal.exists_chartIso_e0 hC hp
  obtain ⟨δ, hδ, hB⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hpe)
  exact ⟨e, he, hiso, hpe, (mem_sing_zero_iff he hpe).1 hp, δ, hδ, hB⟩

/-- **An `E_{≥0}`-manifold is T1**: every point lies in a chart into a T1 space. -/
theorem t1Space_of_isoChartsCover
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) : T1Space M := by
  rw [t1Space_iff_exists_open]
  intro x y hxy
  rcases hC x with ⟨e, -, hxe, -⟩ | ⟨o, e, -, hxe, -⟩
  · exact exists_open_of_chart e hxe hxy
  · haveI := massAModel_t1Space o
    exact exists_open_of_chart e hxe hxy

/-- **An `E_{≥0}`-manifold is first countable**: every point lies in a chart into a metric
space. -/
theorem firstCountableTopology_of_isoChartsCover
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    FirstCountableTopology M := by
  refine ⟨fun x => ?_⟩
  rcases hC x with ⟨e, -, hxe, -⟩ | ⟨o, e, -, hxe, -⟩
  · exact isCountablyGenerated_nhds_of_chart e hxe
  · haveI := massAModel_firstCountableTopology o
    exact isCountablyGenerated_nhds_of_chart e hxe

/-- **`J⁻(p) ⊂ sing₀(M)` at a BTZ point `p`** (the planner's step (a)): along a causal curve
to `p` the parameters mapped into `sing₀(M)` form an initial segment
(`Causality.mem_of_causalCurveOn`, from `past_local` and the closedness of `sing₀(M)`), so no
induction on chains is needed. -/
theorem mem_sing_zero_of_le (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p q : M}
    (hp : p ∈ SFALocal.sing M 0) (hqp : C.le ⊤ q p) : q ∈ SFALocal.sing M 0 := by
  obtain ⟨c, hc, rfl, rfl⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl q p).1.1 hqp
  exact Causality.mem_of_causalCurveOn
    (SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) 0 le_rfl)
    (SFALocal.pastLocal hC) hc le_rfl zero_le_one le_rfl hp

/-- `J⁻(p)` lies in the connected component of `sing₀(M)` through the BTZ point `p`. -/
theorem Jminus_subset_component (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {p q : M}
    (hp : p ∈ SFALocal.sing M 0) (hqp : C.le ⊤ q p) :
    q ∈ connectedComponentIn (SFALocal.sing M 0) p := by
  obtain ⟨c, hc, rfl, rfl⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl q p).1.1 hqp
  have hsub : c '' Icc 0 1 ⊆ SFALocal.sing M 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact Causality.mem_of_causalCurveOn
      (SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) 0 le_rfl)
      (SFALocal.pastLocal hC) hc ht.1 ht.2 le_rfl hp
  have hpre : IsPreconnected (c '' Icc 0 1) :=
    isPreconnected_Icc.image c (hc.continuousOn C.isRelFamily_le)
  exact hpre.subset_connectedComponentIn ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩ hsub
    ⟨0, left_mem_Icc.2 zero_le_one, rfl⟩

/-- **A causal curve reaches a BTZ point from below along the axis**: if `z ≤ q`, `z ≠ q`, `q`
over the axis of a chart isomorphism into `E₀`, there is `w` over the axis of the ball about
`e q`, strictly below `q` in `τ`, with `z ≤ w ≤ q`. The first parameter at which a curve from `z`
reaches `q` (T1). -/
theorem exists_below (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hiso : ChartIso C E0.causality e) {q : M} (hq : q ∈ e.source) (hqa : e q ∈ E0.axis)
    (hδ : 0 < δ) (hB : Metric.ball (e q) δ ⊆ e.target) {z : M} (hzq : C.le ⊤ z q)
    (hne : z ≠ q) :
    ∃ w ∈ ballSource e (e q) δ, C.le ⊤ z w ∧ C.le ⊤ w q ∧ e w ∈ E0.axis ∧ (e w).1 < (e q).1 := by
  haveI := t1Space_of_isoChartsCover hC
  obtain ⟨c, hc, hc0, hc1⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl z q).1.1 hzq
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
  -- the first parameter at which the curve reaches `q`
  set F : Set ℝ := Icc 0 1 ∩ c ⁻¹' {q} with hF
  have hFc : IsClosed F := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have h1F : (1 : ℝ) ∈ F := ⟨right_mem_Icc.2 zero_le_one, hc1⟩
  have hbdd : BddBelow F := ⟨0, fun t ht => ht.1.1⟩
  have hs₂ : sInf F ∈ F := hFc.csInf_mem ⟨1, h1F⟩ hbdd
  set s₂ := sInf F with hs₂def
  have hcs₂ : c s₂ = q := hs₂.2
  have hs₂pos : 0 < s₂ := by
    rcases hs₂.1.1.eq_or_lt with h | h
    · exact absurd (by rw [← hc0, h, hcs₂]) hne
    · exact h
  have hqV : q ∈ ballSource e (e q) δ := ⟨hq, Metric.mem_ball_self hδ⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel s₂ hs₂.1 (ballSource e (e q) δ) le_top
    (by rw [hcs₂]; exact hqV)
  set m : ℝ := max l 0 with hm
  have hm1 : m < s₂ := max_lt hl hs₂pos
  set s : ℝ := (m + s₂) / 2 with hs
  have hms : m < s := by rw [hs]; linarith
  have hss₂ : s < s₂ := by rw [hs]; linarith
  have hls : l < s := lt_of_le_of_lt (le_max_left _ _) hms
  have hs0 : 0 ≤ s := (le_max_right _ _).trans hms.le
  have hs1 : s ≤ 1 := hss₂.le.trans hs₂.1.2
  have hle : C.le (ballSource e (e q) δ) (c s) q := by
    have h := hrel s ⟨hs0, hs1⟩ s₂ hs₂.1 hls hss₂ hu
    rwa [hcs₂] at h
  have hcsV : c s ∈ ballSource e (e q) δ := C.le_mem_left hle
  have hLe := (le_ballSource_iff hiso hqa hB hcsV hqV).1 hle
  obtain ⟨hax, hτ⟩ := (E0.le_axis_iff' hqa).1 hLe
  have hcsq : c s ≠ q := fun h => absurd (csInf_le hbdd ⟨⟨hs0, hs1⟩, h⟩) (not_le.2 hss₂)
  have hτlt : (e (c s)).1 < (e q).1 := lt_of_le_of_ne hτ fun h =>
    hcsq (e.injOn hcsV.1 hq (E0.axis_eq_of_fst_eq hax hqa h))
  refine ⟨c s, hcsV, ?_, C.le_mono le_top hle, hax, hτlt⟩
  rw [← hc0]
  exact hc.le_of_le le_rfl hs0 hs1

/-- **A causal curve leaves a BTZ point up the axis**: if `x ≤ p`, `x ≠ p`, `p` a BTZ point,
`x` over the axis of a chart isomorphism into `E₀`, there is `u ≠ p` over the axis of the ball
about `e x`, strictly above `x` in `τ`, with `x ≤ u ≤ p`. The last parameter at which a curve
from `x` to `p` is at `x`, and a parameter before it first reaches `p` (T1); the curve lies in
`sing₀(M)`. -/
theorem exists_above (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (he : IsAEChart (Flat.isom 2) (Minkowski 2) e) (hiso : ChartIso C E0.causality e) {x : M}
    (hx : x ∈ e.source) (hxa : e x ∈ E0.axis) (hδ : 0 < δ) (hB : Metric.ball (e x) δ ⊆ e.target)
    {p : M} (hp : p ∈ SFALocal.sing M 0) (hxp : C.le ⊤ x p) (hne : x ≠ p) :
    ∃ u ∈ ballSource e (e x) δ, C.le ⊤ x u ∧ C.le ⊤ u p ∧ u ≠ p ∧ e u ∈ E0.axis ∧
      (e x).1 < (e u).1 := by
  haveI := t1Space_of_isoChartsCover hC
  obtain ⟨c, hc, hc0, hc1⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl x p).1.1 hxp
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
  -- the last parameter at which the curve is at `x`
  set F : Set ℝ := Icc 0 1 ∩ c ⁻¹' {x} with hF
  have hFc : IsClosed F := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have h0F : (0 : ℝ) ∈ F := ⟨left_mem_Icc.2 zero_le_one, hc0⟩
  have hbdd : BddAbove F := ⟨1, fun t ht => ht.1.2⟩
  have ht₁ : sSup F ∈ F := hFc.csSup_mem ⟨0, h0F⟩ hbdd
  set t₁ := sSup F with ht₁def
  have hct₁ : c t₁ = x := ht₁.2
  have ht₁1 : t₁ < 1 := by
    rcases ht₁.1.2.eq_or_lt with h | h
    · exact absurd (by rw [← hct₁, h, hc1]) hne
    · exact h
  -- the first parameter after `t₁` at which the curve is at `p`
  set G : Set ℝ := Icc t₁ 1 ∩ c ⁻¹' {p} with hG
  have hGc : IsClosed G :=
    (hcont.mono (Icc_subset_Icc ht₁.1.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have h1G : (1 : ℝ) ∈ G := ⟨⟨ht₁1.le, le_rfl⟩, hc1⟩
  have hbddG : BddBelow G := ⟨t₁, fun t ht => ht.1.1⟩
  have ht₂ : sInf G ∈ G := hGc.csInf_mem ⟨1, h1G⟩ hbddG
  set t₂ := sInf G with ht₂def
  have hct₂ : c t₂ = p := ht₂.2
  have ht₁₂ : t₁ < t₂ := by
    rcases ht₂.1.1.eq_or_lt with h | h
    · exact absurd (by rw [← hct₁, h, hct₂]) hne
    · exact h
  have hxV : x ∈ ballSource e (e x) δ := ⟨hx, Metric.mem_ball_self hδ⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t₁ ht₁.1 (ballSource e (e x) δ) le_top
    (by rw [hct₁]; exact hxV)
  set m : ℝ := min u t₂ with hm
  have hm1 : t₁ < m := lt_min hu ht₁₂
  set t : ℝ := (t₁ + m) / 2 with ht
  have ht₁t : t₁ < t := by rw [ht]; linarith
  have htm : t < m := by rw [ht]; linarith
  have htu : t < u := htm.trans_le (min_le_left _ _)
  have htt₂ : t < t₂ := htm.trans_le (min_le_right _ _)
  have ht0 : 0 ≤ t := ht₁.1.1.trans ht₁t.le
  have ht1 : t ≤ 1 := htt₂.le.trans ht₂.1.2
  have hle : C.le (ballSource e (e x) δ) x (c t) := by
    have h := hrel t₁ ht₁.1 t ⟨ht0, ht1⟩ hl ht₁t htu
    rwa [hct₁] at h
  have hctV : c t ∈ ballSource e (e x) δ := C.le_mem_right hle
  have hctS : c t ∈ SFALocal.sing M 0 := Causality.mem_of_causalCurveOn
    (SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) 0 le_rfl)
    (SFALocal.pastLocal hC) hc ht0 ht1 le_rfl (by rw [hc1]; exact hp)
  have hax : e (c t) ∈ E0.axis := (mem_sing_zero_iff he hctV.1).1 hctS
  have hLe := (le_ballSource_iff hiso hxa hB hxV hctV).1 hle
  have hτ : (e x).1 ≤ (e (c t)).1 := by
    have := (E0.le_axis_iff hxa).1 hLe
    rwa [E0.fcoord_of_axis hax] at this
  have hctx : c t ≠ x := fun h => absurd (le_csSup hbdd ⟨⟨ht0, ht1⟩, h⟩) (not_le.2 ht₁t)
  have hctp : c t ≠ p := fun h => absurd (csInf_le hbddG ⟨⟨ht₁t.le, ht1⟩, h⟩) (not_le.2 htt₂)
  have hτlt : (e x).1 < (e (c t)).1 := lt_of_le_of_ne hτ fun h =>
    hctx (e.injOn hctV.1 hx (E0.axis_eq_of_fst_eq hax hxa h.symm))
  refine ⟨c t, hctV, C.le_mono le_top hle, ?_, hctp, hax, hτlt⟩
  rw [← hc1]
  exact hc.le_of_le ht0 ht1 le_rfl

/-- **The BTZ points near `x` below `u` lie in `J⁻(u)`**: for `u` over the axis of the ball
about `e x`, above `x`, the ball of radius `τ(u) − τ(x)` gives an open `N ∋ x` with
`N ∩ sing₀(M) ⊆ J⁻(u)`. -/
theorem exists_open_inter_sing_subset (he : IsAEChart (Flat.isom 2) (Minkowski 2) e)
    (hiso : ChartIso C E0.causality e) {x : M} (hxa : e x ∈ E0.axis)
    (hB : Metric.ball (e x) δ ⊆ e.target) {u : M} (hu : u ∈ ballSource e (e x) δ)
    (hua : e u ∈ E0.axis) (hxu : (e x).1 < (e u).1) (hx : x ∈ e.source) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ∩ SFALocal.sing M 0 ⊆ C.Jminus ⊤ {u} := by
  set ε : ℝ := (e u).1 - (e x).1 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεδ : ε < δ := by
    have h1 : |(e u).1 - (e x).1| ≤ dist (e u) (e x) := by
      rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
    have h2 : dist (e u) (e x) < δ := hu.2
    have h3 : (e u).1 - (e x).1 ≤ |(e u).1 - (e x).1| := le_abs_self _
    rw [hε]; linarith
  refine ⟨ballSource e (e x) ε, (ballSource e (e x) ε).isOpen, ⟨hx, Metric.mem_ball_self hε0⟩,
    fun z ⟨hzN, hzS⟩ => ?_⟩
  have hzV : z ∈ ballSource e (e x) δ := ⟨hzN.1, Metric.ball_subset_ball hεδ.le hzN.2⟩
  have hza : e z ∈ E0.axis := (mem_sing_zero_iff he hzN.1).1 hzS
  have hτ : (e z).1 < (e u).1 := by
    have h1 : |(e z).1 - (e x).1| ≤ dist (e z) (e x) := by
      rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
    have h2 : dist (e z) (e x) < ε := hzN.2
    have h3 : (e z).1 - (e x).1 ≤ |(e z).1 - (e x).1| := le_abs_self _
    rw [hε] at h2; linarith
  exact Precausality.mem_Jminus_singleton.2
    (le_of_axis hiso hxa hB hzV hu hza hua hτ.le)

/-! ### The two fields -/

/-- **`BTZAxioms.singularPastAt` at every `E_{≥0}`-manifold.** -/
theorem singularPastAt (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ p ∈ SFALocal.sing M 0, C.SingularPastAt p := by
  intro p hp
  obtain ⟨e, -, hiso, hpe, hpa, δ, hδ, hB⟩ := exists_chart hC hp
  refine ⟨?_, fun x hxp hxne => ?_⟩
  · obtain ⟨u, hu, -, -, hup, -⟩ :=
      exists_axis_seq hiso hpe hpa hδ hB (half_pos hδ) (half_lt_self hδ)
    exact ⟨u, hu, hup⟩
  · have hxS := mem_sing_zero_of_le hmin hC hp hxp
    obtain ⟨ex, hex, hisox, hxe, hxa, δx, hδx, hBx⟩ := exists_chart hC hxS
    obtain ⟨u₀, hu₀V, -, hu₀p, hu₀ne, hu₀a, hτ₀⟩ :=
      exists_above hmin hC hex hisox hxe hxa hδx hBx hp hxp hxne
    obtain ⟨N, hN, hxN, hNsub⟩ :=
      exists_open_inter_sing_subset hex hisox hxa hBx hu₀V hu₀a hτ₀ hxe
    obtain ⟨w, hwV, hu₀w, -, hwa, hwτ⟩ := exists_below hmin hC hiso hpe hpa hδ hB hu₀p hu₀ne
    have hη : 0 < (e p).1 - (e w).1 := by linarith
    have hηδ : (e p).1 - (e w).1 < δ := by
      have h1 : |(e w).1 - (e p).1| ≤ dist (e w) (e p) := by
        rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
      have h2 : dist (e w) (e p) < δ := hwV.2
      have h3 : (e p).1 - (e w).1 ≤ |(e w).1 - (e p).1| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith
    obtain ⟨u, hu, hmono, hint, -, hw⟩ := exists_axis_seq hiso hpe hpa hδ hB hη hηδ
    have hwu : C.le ⊤ w (u 0) := hw w hwV hwa (by linarith)
    refine ⟨u, hu, hmono, hint, Precausality.mem_Jminus_singleton.2 hxp,
      mem_nhdsWithin.2 ⟨N, hN, hxN, fun z ⟨hzN, hzJ⟩ => ?_⟩⟩
    have hzp : C.le ⊤ z p := Precausality.mem_Jminus_singleton.1 hzJ
    have hzu₀ : C.le ⊤ z u₀ :=
      Precausality.mem_Jminus_singleton.1 (hNsub ⟨hzN, mem_sing_zero_of_le hmin hC hp hzp⟩)
    exact Precausality.mem_Jminus_singleton.2 (C.le_trans (C.le_trans hzu₀ hu₀w) hwu)

/-- **`BTZAxioms.Iplus_of_lt` (DEC-64) at every `E_{≥0}`-manifold.** -/
theorem Iplus_of_lt (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    ∀ p ∈ SFALocal.sing M 0, ∀ p' ∈ SFALocal.sing M 0, C.le ⊤ p p' → p ≠ p' →
      C.Jplus ⊤ {p'} \ SFALocal.sing M 0 ⊆ C.Iplus ⊤ {p} := by
  intro p hp p' hp' hpp' hne y ⟨hy, hyS⟩
  have hp'y : C.le ⊤ p' y := Precausality.mem_Jplus_singleton.1 hy
  obtain ⟨c, hc, hc0, hc1⟩ := (SFALocal.causallyArcConnected hmin hC ⊤ le_rfl p' y).1.1 hp'y
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn C.isRelFamily_le
  have hSc := SFALocal.isClosed_sing (SFALocal.massACovered_of_isoChartsCover hC) 0 le_rfl
  -- the last parameter at which the curve is at a BTZ point
  set F : Set ℝ := Icc 0 1 ∩ c ⁻¹' SFALocal.sing M 0 with hF
  have hFc : IsClosed F := hcont.preimage_isClosed_of_isClosed isClosed_Icc hSc
  have h0F : (0 : ℝ) ∈ F := ⟨left_mem_Icc.2 zero_le_one, by rw [mem_preimage, hc0]; exact hp'⟩
  have hbdd : BddAbove F := ⟨1, fun t ht => ht.1.2⟩
  have ht₀ : sSup F ∈ F := hFc.csSup_mem ⟨0, h0F⟩ hbdd
  set t₀ := sSup F with ht₀def
  have hqS : c t₀ ∈ SFALocal.sing M 0 := ht₀.2
  have ht₀1 : t₀ < 1 := by
    rcases ht₀.1.2.eq_or_lt with h | h
    · exact absurd (by rw [← hc1, ← h]; exact hqS) hyS
    · exact h
  have hp'q : C.le ⊤ p' (c t₀) := by
    rw [← hc0]; exact hc.le_of_le le_rfl ht₀.1.1 ht₀.1.2
  obtain ⟨e, he, hiso, hqe, hqa, δ, hδ, hB⟩ := exists_chart hC hqS
  have hqV : c t₀ ∈ ballSource e (e (c t₀)) δ := ⟨hqe, Metric.mem_ball_self hδ⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t₀ ht₀.1 (ballSource e (e (c t₀)) δ) le_top hqV
  have hm : t₀ < min u 1 := lt_min hu ht₀1
  set t : ℝ := (t₀ + min u 1) / 2 with ht
  have ht₀t : t₀ < t := by rw [ht]; linarith
  have htm : t < min u 1 := by rw [ht]; linarith
  have htu : t < u := htm.trans_le (min_le_left _ _)
  have ht1 : t ≤ 1 := htm.le.trans (min_le_right _ _)
  have ht0 : 0 ≤ t := ht₀.1.1.trans ht₀t.le
  have hle : C.le (ballSource e (e (c t₀)) δ) (c t₀) (c t) :=
    hrel t₀ ht₀.1 t ⟨ht0, ht1⟩ hl ht₀t htu
  have hctV : c t ∈ ballSource e (e (c t₀)) δ := C.le_mem_right hle
  have hctS : c t ∉ SFALocal.sing M 0 := fun h =>
    absurd (le_csSup hbdd ⟨⟨ht0, ht1⟩, h⟩) (not_le.2 ht₀t)
  have hcta : e (c t) ∉ E0.axis := fun h => hctS ((mem_sing_zero_iff he hctV.1).2 h)
  have hf : (e (c t₀)).1 ≤ E0.fcoord (e (c t)) :=
    (E0.le_axis_iff hqa).1 ((le_ballSource_iff hiso hqa hB hqV hctV).1 hle)
  -- a point strictly below `c t₀` in the past of which is `p`
  obtain ⟨z, hpz, hzq, hzne⟩ : ∃ z, C.le ⊤ p z ∧ C.le ⊤ z (c t₀) ∧ z ≠ c t₀ := by
    by_cases hpq : p = c t₀
    · exact ⟨p', hpp', hp'q, fun h => hne (hpq.trans h.symm)⟩
    · exact ⟨p, C.le_refl trivial, C.le_trans hpp' hp'q, hpq⟩
  obtain ⟨w, hwV, hzw, -, hwa, hwτ⟩ := exists_below hmin hC hiso hqe hqa hδ hB hzq hzne
  have hlt : C.lt ⊤ w (c t) := C.lt_mono le_top ((lt_ballSource_iff hiso hqa hB hwV hctV).2
    ((E0.lt_axis_iff hwa).2 ⟨E0.rad_pos.2 hcta, by linarith⟩))
  have hP := SFALocal.pushUp hmin hC
  have h1 : C.lt ⊤ p (c t) := Causality.PushUp.lt_of_le_of_lt hP (C.le_trans hpz hzw) hlt
  have h2 : C.le ⊤ (c t) y := by rw [← hc1]; exact hc.le_of_le ht0 ht1 le_rfl
  exact Precausality.mem_Iplus_singleton.2 (Causality.PushUp.lt_of_lt_of_le hP h1 h2)

/-- Every field of `BTZAxioms` but `line`, at every `E_{≥0}`-manifold. -/
theorem btzAxioms_but_line (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p ∈ SFALocal.sing M 0, C.SingularPastAt p) ∧
      (∀ p ∈ SFALocal.sing M 0, C.Iminus ⊤ {p} = ∅) ∧
      (∀ p ∈ SFALocal.sing M 0, ∀ p' ∈ SFALocal.sing M 0, C.le ⊤ p p' → p ≠ p' →
        C.Jplus ⊤ {p'} \ SFALocal.sing M 0 ⊆ C.Iplus ⊤ {p}) ∧
      (∀ p ∈ SFALocal.sing M 0, ∃ U : Opens M, p ∈ U ∧ ∀ q, C.le U q p → q ∈ SFALocal.sing M 0) :=
  ⟨singularPastAt hmin hC, SFALocal.Iminus_eq_empty hmin hC, Iplus_of_lt hmin hC,
    SFALocal.pastLocal hC⟩

/-- **`BTZAxioms` at every `E_{≥0}`-manifold from the field `line` alone.** -/
theorem btzAxioms_of_line (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hline : ∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
      C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p) :
    C.BTZAxioms (SFALocal.sing M 0) where
  singularPastAt := singularPastAt hmin hC
  Iminus_eq_empty := SFALocal.Iminus_eq_empty hmin hC
  Iplus_of_lt := Iplus_of_lt hmin hC
  past_local := SFALocal.pastLocal hC
  line := hline

/-- **`SingularFlatAxioms` at a Hausdorff, second countable `E_{≥0}`-manifold is exactly the two
line fields** `line` and `massive_line`. -/
theorem singularFlatAxioms_iff_lines [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.SingularFlatAxioms (SFALocal.sing M) ↔
      (∀ p ∈ SFALocal.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocal.sing M 0) p) ∧
      (∀ α : ℝ, 0 < α → ∀ p ∈ SFALocal.sing M α, ∃ γ : ℝ → M, γ 0 = p ∧
        (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ (∀ a b, C.ChronalCurveOn ⊤ γ a b) ∧
        range γ = connectedComponentIn (SFALocal.sing M α) p) := by
  rw [SFALocal.singularFlatAxioms_iff hmin hC]
  exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨singularPastAt hmin hC, Iplus_of_lt hmin hC, h⟩⟩

/-! ### Corollaries beyond the target: `prop:K_calcul` and `prop:K_monotone` without `line` -/

/-- **`prop:K_calcul` at every `E_{≥0}`-manifold** (unmarked): its three assertions, (c) at a
causal one, from `Causality.K_calcul` (`Causal.PushUp`), which asks push-up, `Z⁺ = M`,
`M ∖ sing₀(M) ⊆ Z⁻` and `SingularPastAt` at the points of `sing₀(M)`. -/
theorem K_calcul (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p ∉ SFALocal.sing M 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p}) ∧
      (∀ p ∈ SFALocal.sing M 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p}) ∧
      (C.IsCausal → ∀ p ∈ SFALocal.sing M 0, C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p}) := by
  haveI := firstCountableTopology_of_isoChartsCover hC
  exact Causality.K_calcul (SFALocal.pushUp hmin hC) (SFALocal.mem_Zplus hC)
    (fun _ hp => SFALocal.mem_Zminus_of_notMem hC hp) (singularPastAt hmin hC)

/-- **`prop:K_monotone` at every causal `E_{≥0}`-manifold** (unmarked), from
`Causality.K_monotone` (`Causal.PushUp`): its BTZ hypotheses are `mem_sing_zero_of_le` and
`Iplus_of_lt`. -/
theorem K_monotone (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {p q : M} (hqp : C.le ⊤ q p) :
    C.Kminus ⊤ {q} ⊆ C.Kminus ⊤ {p} ∧ C.Kplus ⊤ {p} ⊆ C.Kplus ⊤ {q} := by
  haveI := firstCountableTopology_of_isoChartsCover hC
  refine Causality.K_monotone hc (SFALocal.pushUp hmin hC) (SFALocal.mem_Zplus hC)
    (fun _ hp => SFALocal.mem_Zminus_of_notMem hC hp) (singularPastAt hmin hC)
    (fun _ hp _ hqp => mem_sing_zero_of_le hmin hC hp hqp) ?_ hqp
  intro x hx x' hx' y hy hxx' hne hx'y
  exact Precausality.mem_Iplus_singleton.1
    (Iplus_of_lt hmin hC x hx x' hx' hxx' hne ⟨Precausality.mem_Jplus_singleton.2 hx'y, hy⟩)

/-! ### `E₀`-manifolds: a corollary -/

/-- `singularPastAt` at every `E₀`-manifold with its natural causality. -/
theorem singularPastAt_e0 (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    ∀ p ∈ SFALocalE0.sing M 0, C.SingularPastAt p := by
  rw [← SFALocal.sing_eq_of_e0Covered hcov]
  exact singularPastAt hC.2.2 (SFALocal.isoChartsCoverDEC25_of_e0 hcov hC)

/-- `Iplus_of_lt` at every `E₀`-manifold with its natural causality. -/
theorem Iplus_of_lt_e0 (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    ∀ p ∈ SFALocalE0.sing M 0, ∀ p' ∈ SFALocalE0.sing M 0, C.le ⊤ p p' → p ≠ p' →
      C.Jplus ⊤ {p'} \ SFALocalE0.sing M 0 ⊆ C.Iplus ⊤ {p} := by
  rw [← SFALocal.sing_eq_of_e0Covered hcov]
  exact Iplus_of_lt hC.2.2 (SFALocal.isoChartsCoverDEC25_of_e0 hcov hC)

/-- **`SingularFlatAxioms` at a Hausdorff, second countable `E₀`-manifold is exactly the field
`line`.** -/
theorem singularFlatAxioms_iff_line_e0 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocalE0.E0Covered M) (hC : SFALocalE0.IsE0Natural C) :
    C.SingularFlatAxioms (SFALocalE0.sing M) ↔
      ∀ p ∈ SFALocalE0.sing M 0, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
        C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn (SFALocalE0.sing M 0) p := by
  rw [SFALocalE0.singularFlatAxioms_iff hcov hC]
  exact ⟨fun h => h.2.2, fun h => ⟨singularPastAt_e0 hcov hC, Iplus_of_lt_e0 hcov hC, h⟩⟩

end Manifold

/-! ### Witness: `E₀` -/

section Witness

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity at `E₀`** (kb/0011): the hypotheses hold with a BTZ point, and the two fields
come out of this file's theorems (not of `E0.btzAxioms`). -/
theorem nonvacuous_e0 :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (SFALocal.sing E0 0).Nonempty ∧
      (∀ p ∈ SFALocal.sing E0 0, E0.causality.SingularPastAt p) ∧
      (∀ p ∈ SFALocal.sing E0 0, ∀ p' ∈ SFALocal.sing E0 0, E0.causality.le ⊤ p p' → p ≠ p' →
        E0.causality.Jplus ⊤ {p'} \ SFALocal.sing E0 0 ⊆ E0.causality.Iplus ⊤ {p}) := by
  obtain ⟨hmin, hC, -, hne⟩ := SFALocal.nonvacuous_e0
  exact ⟨hmin, hC, hne, singularPastAt hmin hC, Iplus_of_lt hmin hC⟩

end Witness

end SFABTZ

end Causal
