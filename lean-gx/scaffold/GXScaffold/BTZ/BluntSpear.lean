import GX.BTZ.AbsMax
import GX.BTZ.SectorAtlas

/-!
# `GXScaffold.BTZ.BluntSpear` — blunt spear neighbourhoods in the flat case (btz § 3.1)

Target T-btz-blunt-spear. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`), § 3.1. Rows
(unmarked, partial — E₀-scoped, T-btz-scope; readings below):

* `btzdef:blunt_spear_neighborhood` — `BTZ_1.tex:621–629`: `GX.E0BluntSpear.IsBluntSpearNbhd`,
  with `bspear`, `bspearY`, `bspearHead`, `bspearShaft`, the printed « interior dense and locally
  connected in `U` » (`IsBluntSpearNbhd.subset_closure_interior`,
  `IsBluntSpearNbhd.locallyConnectedSpace_interior`), « the regular part of a unique spear »
  (`bspear_eq_iff`, `bspear_eq_spear_diff_axis`), non-vacuity `isBluntSpearNbhd_model`.
* `btzlem:blunt_spear_neighborhood` — `BTZ_1.tex:693–701`, proof « essentially the same » as
  l.719–742's: `GX.E0BluntSpear.lem_blunt_spear` (flat `M`, paper form; rests on one tagged
  `sorry`, the inextensibility of the in-falling regular null rays, `flat_infall_noLimit`; the
  vertical rays are done, `flat_vertical_noLimit`, T-btz-blunt-vertical-ray) and the core
  `GX.E0BluntSpear.lem_blunt_spear_of_inextensible` (any GH `𝔼₀`-manifold, the two
  inextensibility facts as hypotheses, 0 `sorry`).

> \begin{defou}[Blunt spear neighborhood] Let $M^*$ be a $\mass{>0}$-manifold. A blunt spear
> neighborhood of radius $R>0$ in $M^*$ is a subset $\U$ whose interior is dense and locally
> connected in $\U$ such that there exists a singular $\mass{}$-isomorphism
> $\phi: \U^*\rightarrow \V^*\subset \mass{0}$ with
> $\V^*:= \reg(J^+(p) \cap \{\r\leq R\})\subset \reg(\mass{0})$ for some $p \in \sing(\mass{0})$.
> Such a $\V^*$ is the regular part of a unique spear $\V$ in $\mass{0}$, the head and the shaft
> of $\V^*$ are respectively the head and the shaft of $\V$. \end{defou} (l.621–629)
>
> \begin{lemou} Let $M$ be a globally hyperbolic $\mass{>0}$-manifold, let $\Sigma$ be
> Cauchy-surface of $M$ and let $\phi_0: \mathcal S_0\rightarrow \mass{0}$ be a blunt spear
> neighborhood in $M$. Then, there exists a blunt spear neighborhood
> $\phi:\mathcal S \rightarrow \Reg(\mass{0})$ such that
> $\mathcal S\subset \mathcal S_0$, $\phi = \phi_{0|\mathcal S}$ and
> $\inf(\phi(\S))=\inf(\phi(\S_0))$; $\Sigma\cap \mathcal S$ lie in the shaft of $\mathcal S$
> and $\phi(\Sigma\cap \mathcal S)\subset \Reg(\mass{0})$ is the graph of a smooth function
> $\tau_\Sigma: \mathbb D_R^*\rightarrow \RR_+^*$. \end{lemou} (l.693–701)
>
> We only prove Lemma \ref{lem:add_BTZ_param} since the proof of Lemma
> \ref{lem:blunt_spear_neighborhood} is essentially the same. (l.721)

## Hypothesis checklist

| paper | here |
|---|---|
| `M*`, `M` an `𝔼_{>0}`-manifold | ⚠ `𝔼₀` scope (T-btz-scope): no massive particle, so `M` is **flat**: a `Causal.Flat.FlatSpacetime 2` `N` read as the `𝔼₀`-manifold `E0AbsMax.FlatE0 N` (`M* = Reg M` of an `𝔼₀`-manifold is `e0RegMFlat M`); the core is stated for every GH `𝔼₀`-manifold |
| « singular `𝔼`-isomorphism `φ : U* → V*` » | ⚠ read as for spears (DEC-116 (c)): `ψ = φ⁻¹` an injective `𝔼₀`-morphism on an open `W ⊇ V*` of `Y`, `U = ψ(V*)`; `U* = U` (`M*` has no BTZ point) |
| `p ∈ sing(𝔼₀)` | ✓ the vertex `(v, 0)`, `v` free |
| « interior dense and locally connected in `U` » | ✓ proved from the chart (`subset_closure_interior`, `locallyConnectedSpace_interior`) |
| « regular part of a unique spear » | ✓ `bspear_eq_spear_diff_axis`, `bspear_eq_iff` |
| Lemma: `M` GH, `Σ` Cauchy | ✓ `Causal.Flat.GH N`, `(flatCausality 2 N).IsCauchySurface Σ` (core: `(CE X)`) |
| `φ₀ : 𝒮₀ → 𝔼₀` given, `𝒮 ⊂ 𝒮₀`, `φ = φ₀|𝒮` | ✓ the given chart `(v, W, ψ)` of `𝒮₀ = ψ(bspearY v R)` is a hypothesis; `𝒮 = ψ(bspearY v R′)` with the same `ψ`, `R′ ≤ R` |
| `inf φ(𝒮) = inf φ(𝒮₀)` | ✓ read as the causal infimum in `𝔼₀`: both are the vertex (`isLowerBound_vertex`, `le_vertex_of_lowerBound`); the two sets have the same lower bounds (`lowerBounds_bspear_iff`, in the conclusion) |
| « `Σ ∩ 𝒮` in the shaft » | ✓ read as for `lem:add_BTZ_param` (DEC-116 (c)): `Σ ∩ 𝒮 ⊆ {τ > v + R′/2}` |
| `τ_Σ` « smooth » `𝔻*_R → ℝ₊*` | ⚠ `C⁰` on the punctured closed disc (DEC-125 (c)'s reading of the twin `lem:add_BTZ_param`; `Σ` is a topological Cauchy surface), « positive » = `> v + R′/2` |
| (core only) the regular null rays of `𝒮₀` are inextensible in `M` | ⚠ **added** as hypotheses of the core: `hvert` (every vertical ray `t ↦ ψ(t, z)`, `0 < ‖z‖ ≤ R`, has no future endpoint) and `hfall` (every in-falling ray `s ↦ ψ(a + s/2, s u)`, `a > v`, has no past endpoint as `s → 0⁺`); in the flat case `hvert` is **proved** (`flat_vertical_noLimit`) and `hfall` is the tagged `sorry` `flat_infall_noLimit` (SCOPE) |

## SCOPE (disclosed)

* The core `lem_blunt_spear_of_inextensible` is sorry-free; its auxiliaries `bvertical_meets`,
  `binfall_meets`, `continuousOn_tauS_blunt`, `exists_tendsto_of_antitone`, `le_of_mem_bspear`
  are too. The paper's « essentially the same »
  proof does not carry over verbatim: for a spear (`lem:add_BTZ_param`) the vertex `p` lies in
  `I⁻(Σ)`, here it is not a point of `M`. The core replaces it by a comparison in `𝔼₀`
  (`le_of_small_rad`: a point of radius `r₁` lies below every point of radius `r₂ ≥ 2r₁` whose
  `f`-level is `4π²r₁` higher) against one point of `Σ` found on a far in-falling null ray or
  above it (inside `lem_blunt_spear_of_inextensible`, by `binfall_meets` or `bvertical_meets`); every point of the shrunk spear below the level `v + R′/2` is
  then in `J⁻(Σ) ∖ Σ`.
* Of the two inputs it needs in the flat case, the first is proved: a vertical null ray
  `t ↦ φ⁻¹(t, z)` has no future endpoint in `N` (`flat_vertical_noLimit`: rigidity at a regular
  limit point, `E0.exists_eqOn_sectorSmulInl` of `GX.BTZ.SectorAtlas`, then the developed
  ray is unbounded). The second is a tagged `sorry`: an in-falling null ray
  `s ↦ φ⁻¹(a + s/2, s u)`, `s → 0⁺`, has no past endpoint in `N` (`flat_infall_noLimit`); its
  developed ray converges, so it needs that the parabolic holonomy around the missing axis cannot
  be killed by a Minkowski chart at the limit point.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal (imports
`Causal.*` through `GX.BTZ.AbsMax`, DEC-33).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0BluntSpear

open E0 E0CBG E0Spear

/-! ### §1 Blunt spears in the model `𝔼₀` -/

section Model

/-- **The regular part of the spear** `reg(J⁺((v,0)) ∩ {r ≤ R}) = {f ≥ v, 0 < r ≤ R}`
(btz l.627). -/
def bspear (v R : ℝ) : Set E0 := {x | v ≤ fcoord x ∧ 0 < rad x ∧ rad x ≤ R}

/-- The head of a blunt spear: the regular part of the head of the spear (l.630). -/
def bspearHead (v R : ℝ) : Set E0 := spearHead v R \ axis

/-- The shaft of a blunt spear: the shaft of the spear (l.630; it misses the axis for `R > 0`). -/
def bspearShaft (v R : ℝ) : Set E0 := spearShaft v R \ axis

/-- The blunt spear in the model space `Y`. -/
noncomputable def bspearY (v R : ℝ) : Set E0Y := paperInY '' bspear v R

theorem mem_bspear {v R : ℝ} {x : E0} :
    x ∈ bspear v R ↔ v ≤ fcoord x ∧ 0 < rad x ∧ rad x ≤ R := Iff.rfl

/-- **A blunt spear is the regular part of a spear** (l.627, l.629). -/
theorem bspear_eq_spear_diff_axis (v R : ℝ) : bspear v R = spear v R \ axis := by
  ext x
  simp only [bspear, spear, Set.mem_sdiff, mem_setOf_eq]
  rw [← rad_pos]
  tauto

/-- **The spear of a blunt spear is unique** (l.629): `(v, R)` is determined by `bspear v R`. -/
theorem bspear_eq_iff {v v' R R' : ℝ} (hR : 0 < R) (hR' : 0 < R') :
    bspear v R = bspear v' R' ↔ v = v' ∧ R = R' := by
  have key : ∀ {v v' R R' : ℝ}, 0 < R → bspear v R = bspear v' R' → v' ≤ v ∧ R ≤ R' := by
    intro v v' R R' hR h
    have hrad : rad ((v + R / 2, (R : ℂ)) : E0) = R := by
      simp only [rad, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hP : ((v + R / 2, (R : ℂ)) : E0) ∈ bspear v R := by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [fcoord, hrad] <;> linarith
    rw [h] at hP
    obtain ⟨h1, -, h3⟩ := hP
    simp only [fcoord, hrad] at h1 h3
    exact ⟨by linarith, h3⟩
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := key hR h
    obtain ⟨h3, h4⟩ := key hR' h.symm
    exact ⟨le_antisymm h3 h1, le_antisymm h2 h4⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem bspear_mono {v R R' : ℝ} (h : R' ≤ R) : bspear v R' ⊆ bspear v R :=
  fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans h⟩

theorem bspear_subset_spear (v R : ℝ) : bspear v R ⊆ spear v R := fun _ hx => ⟨hx.1, hx.2.2⟩

/-- **The vertex is a lower bound of the blunt spear** (`inf φ(𝒮)`, l.698). -/
theorem isLowerBound_vertex {v R : ℝ} {x : E0} (hx : x ∈ bspear v R) : Le (vertex v) x :=
  (le_axis_iff (vertex_mem_axis v)).2 hx.1

/-- **The vertex is the greatest lower bound of the blunt spear** (`inf φ(𝒮)`, l.698): every
lower bound of `bspear v R` (`R > 0`) lies below the vertex. -/
theorem le_vertex_of_lowerBound {v R : ℝ} (hR : 0 < R) {y : E0}
    (hy : ∀ x ∈ bspear v R, Le y x) : Le y (vertex v) := by
  have hs : ∀ s : ℝ, 0 < s → s ≤ R → y.1 ≤ v + s / 2 ∧ rad y ≤ s := by
    intro s hs hsR
    have hrad : rad ((v + s / 2, (s : ℂ)) : E0) = s := by
      simp only [rad, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hmem : ((v + s / 2, (s : ℂ)) : E0) ∈ bspear v R := by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [fcoord, hrad] <;> linarith
    obtain ⟨h1, h2, -⟩ := (hy _ hmem).closed
    exact ⟨h1, by rw [hrad] at h2; exact h2⟩
  have hax : y ∈ axis := by
    rw [← rad_eq_zero]
    by_contra hne
    have hpos : 0 < rad y := lt_of_le_of_ne (rad_nonneg y) (Ne.symm hne)
    have := (hs (min (rad y / 2) R) (lt_min (by linarith) hR) (min_le_right _ _)).2
    linarith [min_le_left (rad y / 2) R]
  refine le_axis hax (vertex_mem_axis v) ?_
  show y.1 ≤ v
  by_contra hlt
  push Not at hlt
  have := (hs (min (y.1 - v) R) (lt_min (by linarith) hR) (min_le_right _ _)).1
  linarith [min_le_left (y.1 - v) R]

/-- **Shrinking the radius keeps the infimum** (`inf φ(𝒮) = inf φ(𝒮₀)`, l.698): `bspear v R′` and
`bspear v R` have the same lower bounds for `≼`, namely the points below the vertex. -/
theorem lowerBounds_bspear_iff {v R R' : ℝ} (hR' : 0 < R') (hR'R : R' ≤ R) (y : E0) :
    (∀ x ∈ bspear v R', Le y x) ↔ ∀ x ∈ bspear v R, Le y x := by
  constructor
  · intro h x hx
    exact (le_vertex_of_lowerBound hR' h).trans (isLowerBound_vertex hx)
  · intro h x hx
    exact h x (bspear_mono hR'R hx)

/-- **A blunt spear is causally convex in `𝔼₀`, and avoids the axis along `≤`**: a causal relation
between two of its points is realised inside every open set containing it. -/
theorem le_of_le_top_of_mem_bspear {v R : ℝ} {U : Opens E0} (hU : bspear v R ⊆ U) {x y : E0}
    (hx : x ∈ bspear v R) (hy : y ∈ bspear v R) (h : causality.le ⊤ x y) :
    causality.le U x y := by
  obtain ⟨c, hc, hc0, hc1⟩ := (E0.causallyArcConnected ⊤ le_rfl x y).1.1 h
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, c s ∈ U := fun s hs => by
    have h1 : causality.le ⊤ x (c s) := by rw [← hc0]; exact hc.le_of_le le_rfl hs.1 hs.2
    have h2 : causality.le ⊤ (c s) y := by rw [← hc1]; exact hc.le_of_le hs.1 hs.2 le_rfl
    exact hU ⟨hx.1.trans (calculus_le h1).2.2.2.2.1, hx.2.1.trans_le (calculus_le h1).2.2.2.1,
      ((calculus_le h2).2.2.2.1).trans hy.2.2⟩
  exact (E0.causallyArcConnected U le_top x y).1.2
    ⟨c, Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem, hc0, hc1⟩

/-- **The comparison in `𝔼₀`**: a point of radius `r₁ ≤ r₂/2` lies below every point of radius
`r₂` whose `f`-level is at least `4π² r₁` higher, whatever the angles. -/
theorem le_of_small_rad {x y : E0} (hr : rad x ≤ rad y / 2)
    (hf : 4 * π ^ 2 * rad x ≤ fcoord y - fcoord x) : Le x y := by
  refine le_iff_closed.2 ⟨Complex.arg x.2, Complex.arg y.2, polar_arg x, polar_arg y, ?_⟩
  have h1 := rad_nonneg x
  have h2 := rad_nonneg y
  have hδ : (Complex.arg y.2 - Complex.arg x.2) ^ 2 ≤ 4 * π ^ 2 := by
    have h := abs_arg_sub_arg_le y.2 x.2
    have : (Complex.arg y.2 - Complex.arg x.2) ^ 2 = |Complex.arg y.2 - Complex.arg x.2| ^ 2 :=
      (sq_abs _).symm
    rw [this]
    have h0 := abs_nonneg (Complex.arg y.2 - Complex.arg x.2)
    nlinarith
  simp only [fcoord] at hf
  have hpi : 0 ≤ 4 * π ^ 2 := by positivity
  have hfx : 0 ≤ 4 * π ^ 2 * rad x := mul_nonneg hpi h1
  refine ⟨by linarith, by linarith, ?_⟩
  have hA : 0 ≤ rad x * rad y := mul_nonneg h1 h2
  have e1 : rad x * rad y * (Complex.arg y.2 - Complex.arg x.2) ^ 2 ≤
      rad x * rad y * (4 * π ^ 2) := mul_le_mul_of_nonneg_left hδ hA
  have e2 : rad y / 2 * (2 * (4 * π ^ 2 * rad x)) ≤
      (rad y - rad x) * (2 * (y.1 - x.1) - (rad y - rad x)) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  nlinarith

/-- **The in-falling null rays** `s ↦ (a + s/2, s u)` (`‖u‖ = 1`, `f = a` constant) are future
causal in `s`. -/
theorem le_infall {a s s' : ℝ} {u : ℂ} (hu : ‖u‖ = 1) (hs : 0 ≤ s) (hss : s ≤ s') :
    Le ((a + s / 2, (s : ℂ) * u) : E0) (a + s' / 2, (s' : ℂ) * u) := by
  have hs' : 0 ≤ s' := hs.trans hss
  have hr : ∀ t : ℝ, 0 ≤ t → rad ((a + t / 2, (t : ℂ) * u) : E0) = t := fun t ht => by
    simp only [rad, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one]
  have hu' : Complex.exp (Complex.arg u * Complex.I) = u := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rwa [hu, Complex.ofReal_one, one_mul] at this
  have hpol : ∀ t : ℝ, 0 ≤ t → Polar ((a + t / 2, (t : ℂ) * u) : E0) (Complex.arg u) := by
    intro t ht
    show (t : ℂ) * u = (rad ((a + t / 2, (t : ℂ) * u) : E0) : ℂ) * Complex.exp (Complex.arg u * Complex.I)
    rw [hr t ht, hu']
  refine le_iff_closed.2 ⟨_, _, hpol s hs, hpol s' hs', ?_⟩
  rw [hr s hs, hr s' hs']
  refine ⟨by simp only; linarith, hss, ?_⟩
  simp only [sub_self]
  nlinarith

end Model

/-! ### §2 Blunt spear neighbourhoods in an `𝔼₀`-manifold -/

section Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X] [HasGroupoid X e0Groupoid]

/-- **A blunt spear neighbourhood of radius `R`** (btz Def `def:blunt_spear_neighborhood`,
l.621–631): a subset `U = ψ(V*)` of `X`, `V* = bspear v R` the regular part of the spear of
vertex `(v, 0)`, for an injective `𝔼₀`-morphism `ψ` defined on an open neighbourhood `W` of `V*`
in `Y` (the paper's `φ : U* → V*` is `ψ⁻¹`, read as for spears, DEC-116 (c)). -/
structure IsBluntSpearNbhd (R : ℝ) (U : Set X) : Prop where
  pos : 0 < R
  chart : ∃ (v : ℝ) (W : Set E0Y) (ψ : E0Y → X), IsOpen W ∧ bspearY v R ⊆ W ∧ IsE0Mor ψ W ∧
    InjOn ψ W ∧ U = ψ '' bspearY v R

/-- **Non-vacuity**: in the model, `bspearY v R` is a blunt spear neighbourhood (`ψ = id`). -/
theorem isBluntSpearNbhd_model (v : ℝ) {R : ℝ} (hR : 0 < R) :
    IsBluntSpearNbhd (X := E0Y) R (bspearY v R) :=
  ⟨hR, v, univ, id, isOpen_univ, subset_univ _, Causal.CBG.liftPropOn_id isOpen_univ,
    injOn_id _, (image_id _).symm⟩

/-- **The interior of a blunt spear neighbourhood is dense in it** (l.624). -/
theorem IsBluntSpearNbhd.subset_closure_interior {R : ℝ} {U : Set X}
    (h : IsBluntSpearNbhd R U) : U ⊆ closure (interior U) := by
  obtain ⟨v, W, ψ, hW, hsub, hψ, -, rfl⟩ := h.chart
  set O : Set E0 := {x | v < fcoord x ∧ 0 < rad x ∧ rad x < R} with hOdef
  have hOo : IsOpen O := (isOpen_lt continuous_const continuous_fcoord).inter
    ((isOpen_lt continuous_const continuous_rad).inter (isOpen_lt continuous_rad continuous_const))
  have hOS : O ⊆ bspear v R := fun x hx => ⟨hx.1.le, hx.2.1, hx.2.2.le⟩
  have hPW : paperInY '' O ⊆ W := fun _ hy => hsub (image_mono hOS hy)
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨W, hW⟩) hψ
  have hopen := hE.isOpen_image ⟨_, isOpen_paperInY_image hOo⟩ hPW
  have hint : ψ '' (paperInY '' O) ⊆ interior (ψ '' bspearY v R) :=
    interior_maximal (image_mono (image_mono hOS)) hopen
  -- every point of the blunt spear is a limit of points of `O`
  have hcl : bspear v R ⊆ closure O := by
    intro x hx
    let c : ℝ → E0 := fun ε => (x.1 + ε, ((1 - ε : ℝ) : ℂ) * x.2)
    have hc : Continuous c := (continuous_const.add continuous_id).prodMk
      ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const)
    have hc0 : c 0 = x := by simp [c]
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ε ∈ O := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      have hrc : rad (c ε) = (1 - ε) * rad x := by
        simp only [c, rad, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by linarith [hε.2])]
      have hx1 := hx.1
      simp only [fcoord] at hx1
      refine ⟨?_, ?_, ?_⟩
      · simp only [fcoord, hrc]; nlinarith [hε.1, hε.2, hx.2.1]
      · rw [hrc]; exact mul_pos (by linarith [hε.2]) hx.2.1
      · rw [hrc]; nlinarith [hε.1, hε.2, hx.2.1, hx.2.2]
    have ht : Tendsto c (𝓝[>] 0) (𝓝 x) := by
      rw [← hc0]; exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto ht hev
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  set P : Set E0 := paperInY ⁻¹' W with hP
  have hPo : IsOpen P := hW.preimage continuous_paperInY
  have hxP : x ∈ P := hsub ⟨x, hx, rfl⟩
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hfc : ContinuousAt (ψ ∘ paperInY) x :=
    (hψc.continuousAt (hW.mem_nhds hxP)).comp continuous_paperInY.continuousAt
  have hx' : x ∈ closure (P ∩ O) := hPo.inter_closure ⟨hxP, hcl hx⟩
  have := hfc.continuousWithinAt.mem_closure_image hx'
  have hsub' : (ψ ∘ paperInY) '' (P ∩ O) ⊆ interior (ψ '' bspearY v R) := by
    rintro _ ⟨y, hy, rfl⟩; exact hint ⟨_, ⟨y, hy.2, rfl⟩, rfl⟩
  exact closure_mono hsub' this

omit [HasGroupoid X e0Groupoid] in
/-- **The interior of a blunt spear neighbourhood is locally connected** (l.624). -/
theorem IsBluntSpearNbhd.locallyConnectedSpace_interior {R : ℝ} {U : Set X}
    (_h : IsBluntSpearNbhd R U) : LocallyConnectedSpace (interior U) := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace E0Y X
  exact isOpen_interior.locallyConnectedSpace

/-- **Transfer**: relations of `𝔼₀` between two points of a blunt spear are relations in `X`. -/
theorem le_of_mem_bspear {v R : ℝ} {W : Set E0Y} {ψ : E0Y → X} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {x y : E0} (hx : x ∈ bspear v R)
    (hy : y ∈ bspear v R) (h : Le x y) : (CE X).le ⊤ (ψ (paperInY x)) (ψ (paperInY y)) := by
  have hPo : IsOpen (paperInY ⁻¹' W) := hW.preimage continuous_paperInY
  set O : Opens E0 := ⟨paperInY ⁻¹' W, hPo⟩
  have hSO : bspear v R ⊆ O := fun x hx => hsub ⟨x, hx, rfl⟩
  exact le_of_isE0Mor_paper hW hψ (U := O) subset_rfl
    (le_of_le_top_of_mem_bspear hSO hx hy ((E0.le_top_iff).2 h))

theorem mem_bspear_vertical {v R t : ℝ} {z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ ≤ R)
    (ht : v + ‖z‖ / 2 ≤ t) : ((t, z) : E0) ∈ bspear v R :=
  ⟨by simp only [fcoord, rad]; linarith, hz0, hz⟩

theorem rad_infall {a s : ℝ} {u : ℂ} (hu : ‖u‖ = 1) (hs : 0 ≤ s) :
    rad ((a + s / 2, (s : ℂ) * u) : E0) = s := by
  simp only [rad, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, hu, mul_one]

theorem mem_bspear_infall {v R a s : ℝ} {u : ℂ} (hu : ‖u‖ = 1) (ha : v ≤ a) (hs : 0 < s)
    (hsR : s ≤ R) : ((a + s / 2, (s : ℂ) * u) : E0) ∈ bspear v R := by
  have hr := rad_infall (a := a) hu hs.le
  refine ⟨?_, ?_, ?_⟩ <;> simp only [fcoord, hr] <;> linarith

end Manifold

/-! ### §3 The core of `lem:blunt_spear_neighborhood` -/

section Core

variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
  [ConnectedSpace X] [ChartedSpace E0Y X] [HasGroupoid X e0Groupoid]

omit [SecondCountableTopology X] [ConnectedSpace X] in
/-- **A past-monotone curve eventually in a compact set converges** (the dual of
`E0Spear.exists_tendsto_of_monotone`). -/
theorem exists_tendsto_of_antitone (hGH : (CE X).GloballyHyperbolic)
    {γ : ℝ → X} {t₀ : ℝ} (hmono : ∀ s t, t₀ ≤ s → s ≤ t → (CE X).le ⊤ (γ t) (γ s))
    {K : Set X} (hK : IsCompact K) (hKγ : ∀ t, t₀ ≤ t → γ t ∈ K) :
    ∃ q, Tendsto γ atTop (𝓝 q) := by
  have hT := E0LM.e0_tarentin (M := X)
  have hev : ∀ᶠ t in atTop, γ t ∈ K := eventually_atTop.2 ⟨t₀, hKγ⟩
  obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (le_principal_iff.2 hev)
  have hbelow : ∀ q', MapClusterPt q' atTop γ → ∀ s, t₀ ≤ s → (CE X).le ⊤ q' (γ s) := by
    intro q' hq' s hs
    have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jminus_singleton hT (γ s)) hq'
      (eventually_atTop.2 ⟨s, fun t ht => by simpa using hmono s t hs ht⟩)
    simpa using this
  have huniq : ∀ q', MapClusterPt q' atTop γ → q' = q := by
    intro q' hq'
    have h1 : (CE X).le ⊤ q q' := by
      have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jplus_singleton hT q) hq'
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using hbelow q hq t ht⟩)
      simpa using this
    have h2 : (CE X).le ⊤ q' q := by
      have := mem_of_mapClusterPt_of_eventually (hGH.isClosed_Jplus_singleton hT q') hq
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using hbelow q' hq' t ht⟩)
      simpa using this
    exact hGH.1 h2 h1
  exact ⟨q, hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx⟩

/-- **A vertical null ray of a blunt spear starting in `J⁻(Σ)` meets `Σ`** (the existence half of
« `Φ(Σ ∩ 𝒮′)` is exactly the graph of `τ_Σ` », l.738, for the blunt spear): were it in
`J⁻(Σ)` forever, it would be a future-monotone curve in the compact `J⁻(Σ) ∩ J⁺(γ t₀)`, hence
convergent, against `hvert`; so it reaches `J⁺(Σ)` and, by connectedness, `Σ`. -/
theorem bvertical_meets (hGH : (CE X).GloballyHyperbolic) {Sig : Set X}
    (hSig : (CE X).IsCauchySurface Sig) {v R : ℝ} {W : Set E0Y} {ψ : E0Y → X} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ ≤ R)
    (hvert : ∀ q : X, ¬ Tendsto (fun t : ℝ => ψ (paperInY (t, z))) atTop (𝓝 q))
    {t₀ : ℝ} (ht₀ : v + ‖z‖ / 2 ≤ t₀) (hstart : ψ (paperInY (t₀, z)) ∈ (CE X).Jminus ⊤ Sig) :
    ∃ t, t₀ ≤ t ∧ ψ (paperInY (t, z)) ∈ Sig := by
  have hLM := E0LM.e0_globalBTZ X
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
  set γ : ℝ → X := fun t => ψ (paperInY (t, z)) with hγ
  have hmem : ∀ t, t₀ ≤ t → ((t, z) : E0) ∈ bspear v R := fun t ht =>
    mem_bspear_vertical hz0 hz (ht₀.trans ht)
  have hmono : ∀ s t, t₀ ≤ s → s ≤ t → (CE X).le ⊤ (γ s) (γ t) := fun s t hs hst =>
    le_of_mem_bspear hW hsub hψ (hmem s hs) (hmem t (hs.trans hst))
      ((E0.le_top_iff).1 (le_vertical_top hst))
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hγc : ContinuousOn γ (Ici t₀) :=
    hψc.comp (continuous_paperInY.comp (continuous_id.prodMk continuous_const)).continuousOn
      fun t ht => hsub ⟨_, hmem t ht, rfl⟩
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hSig
  have hJm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hSig
  obtain ⟨t₁, ht₁, ht₁S⟩ : ∃ t₁, t₀ ≤ t₁ ∧ γ t₁ ∈ (CE X).Jplus ⊤ Sig := by
    by_contra hcon
    push Not at hcon
    have hin : ∀ t, t₀ ≤ t → γ t ∈ (CE X).Jminus ⊤ Sig ∩ (CE X).Jplus ⊤ {γ t₀} := fun t ht =>
      ⟨((Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig (γ t)).resolve_left
        (hcon t ht)), by simpa using hmono t₀ t le_rfl ht⟩
    have hK := E0LM.sfa_isCompact_Jminus_inter_Jplus hA hGH hTc hT hSig (γ t₀)
    obtain ⟨q, hq⟩ := exists_tendsto_of_monotone hGH hmono hK hin
    exact hvert q hq
  have hpre : IsPreconnected (γ '' Icc t₀ t₁) :=
    isPreconnected_Icc.image γ (hγc.mono fun t ht => ht.1)
  obtain ⟨_, ⟨t, ht, rfl⟩, hγt⟩ := isPreconnected_closed_iff.1 hpre _ _ hJp hJm
    (fun _ ⟨t, _, ht⟩ => ht ▸ Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig _)
    ⟨γ t₁, ⟨t₁, ⟨ht₁, le_rfl⟩, rfl⟩, ht₁S⟩ ⟨γ t₀, ⟨t₀, ⟨le_rfl, ht₁⟩, rfl⟩, hstart⟩
  refine ⟨t, ht.1, ?_⟩
  rw [← Causal.Causality.Jplus_inter_Jminus_eq hGH.1 hac]
  exact hγt

/-- **An in-falling null ray of a blunt spear ending in `J⁺(Σ)` meets `Σ`**: were it in `J⁺(Σ)` all
the way down to the (missing) axis, it would be a past-monotone curve in the compact
`J⁺(Σ) ∩ J⁻(γ s₁)`, hence convergent as `s → 0⁺`, against `hfall`. -/
theorem binfall_meets (hGH : (CE X).GloballyHyperbolic) {Sig : Set X}
    (hSig : (CE X).IsCauchySurface Sig) {v R : ℝ} {W : Set E0Y} {ψ : E0Y → X} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {a : ℝ} (ha : v ≤ a) {u : ℂ} (hu : ‖u‖ = 1)
    (hfall : ∀ q : X,
      ¬ Tendsto (fun s : ℝ => ψ (paperInY (a + s / 2, (s : ℂ) * u))) (𝓝[>] 0) (𝓝 q))
    {s₁ : ℝ} (hs₁ : 0 < s₁) (hs₁R : s₁ ≤ R)
    (hend : ψ (paperInY (a + s₁ / 2, (s₁ : ℂ) * u)) ∈ (CE X).Jplus ⊤ Sig) :
    ∃ s, 0 < s ∧ s ≤ s₁ ∧ ψ (paperInY (a + s / 2, (s : ℂ) * u)) ∈ Sig := by
  have hLM := E0LM.e0_globalBTZ X
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  obtain ⟨T, hTc, hT⟩ := E0LM.e0_timeFunction hGH
  set γ : ℝ → X := fun s => ψ (paperInY (a + s / 2, (s : ℂ) * u)) with hγ
  have hmem : ∀ s, 0 < s → s ≤ s₁ → ((a + s / 2, (s : ℂ) * u) : E0) ∈ bspear v R :=
    fun s hs hss => mem_bspear_infall hu ha hs (hss.trans hs₁R)
  have hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ s₁ → (CE X).le ⊤ (γ s) (γ s') :=
    fun s s' hs hss hs' => le_of_mem_bspear hW hsub hψ (hmem s hs (hss.trans hs'))
      (hmem s' (hs.trans_le hss) hs') (le_infall hu hs.le hss)
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hSig
  have hJm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hSig
  obtain ⟨s₀, hs₀, hs₀₁, hs₀S⟩ : ∃ s₀, 0 < s₀ ∧ s₀ ≤ s₁ ∧ γ s₀ ∈ (CE X).Jminus ⊤ Sig := by
    by_contra hcon
    push Not at hcon
    have hin : ∀ s, 0 < s → s ≤ s₁ → γ s ∈ (CE X).Jplus ⊤ Sig ∩ (CE X).Jminus ⊤ {γ s₁} :=
      fun s hs hss => ⟨((Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig
        (γ s)).resolve_right (hcon s hs hss)), by simpa using hmono s s₁ hs hss le_rfl⟩
    have hK := E0LM.sfa_isCompact_Jplus_inter_Jminus hA hGH hTc hT hSig (γ s₁)
    set δ : ℝ → X := fun t => γ t⁻¹ with hδ
    have hδmono : ∀ s t, s₁⁻¹ ≤ s → s ≤ t → (CE X).le ⊤ (δ t) (δ s) := by
      intro s t hs hst
      have hs0 : 0 < s := (inv_pos.2 hs₁).trans_le hs
      exact hmono t⁻¹ s⁻¹ (inv_pos.2 (hs0.trans_le hst)) (inv_anti₀ hs0 hst)
        (inv_le_of_inv_le₀ hs₁ hs)
    have hδK : ∀ t, s₁⁻¹ ≤ t → δ t ∈ (CE X).Jplus ⊤ Sig ∩ (CE X).Jminus ⊤ {γ s₁} := by
      intro t ht
      have ht0 : 0 < t := (inv_pos.2 hs₁).trans_le ht
      exact hin t⁻¹ (inv_pos.2 ht0) (inv_le_of_inv_le₀ hs₁ ht)
    obtain ⟨q, hq⟩ := exists_tendsto_of_antitone hGH hδmono hK hδK
    refine hfall q ?_
    have := hq.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun s => ?_
    simp only [comp_apply, hδ, inv_inv]
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hγc : ContinuousOn γ (Icc s₀ s₁) := by
    refine hψc.comp (continuous_paperInY.comp ((continuous_const.add
      (continuous_id.div_const 2)).prodMk (Complex.continuous_ofReal.mul continuous_const))).continuousOn
      fun s hs => hsub ⟨_, hmem s (hs₀.trans_le hs.1) hs.2, rfl⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, hγs⟩ := isPreconnected_closed_iff.1 (isPreconnected_Icc.image γ hγc)
    _ _ hJp hJm
    (fun _ ⟨t, _, ht⟩ => ht ▸ Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig _)
    ⟨γ s₁, ⟨s₁, ⟨hs₀₁, le_rfl⟩, rfl⟩, hend⟩ ⟨γ s₀, ⟨s₀, ⟨le_rfl, hs₀₁⟩, rfl⟩, hs₀S⟩
  refine ⟨s, hs₀.trans_le hs.1, hs.2, ?_⟩
  rw [← Causal.Causality.Jplus_inter_Jminus_eq hGH.1 hac]
  exact hγs

/-- **The graph function `τ_Σ` is continuous on the punctured closed disc** (the blunt form of
`E0Spear.continuousOn_tauS`, same argument). -/
theorem continuousOn_tauS_blunt (hGH : (CE X).GloballyHyperbolic) {Sig : Set X}
    (hSig : (CE X).IsCauchySurface Sig) {R' v : ℝ} {W : Set E0Y} {ψ : E0Y → X} (hW : IsOpen W)
    (hsub : bspearY v R' ⊆ W) (hψ : IsE0Mor ψ W) {τS : ℂ → ℝ}
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + R' / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) :
    ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R'} := by
  have hLM := E0LM.e0_globalBTZ X
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid hLM
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  have hJp := E0LM.sfa_isClosed_Jplus_cauchy hA hGH hext hSig
  have hJm := E0LM.sfa_isClosed_Jminus_cauchy hA hGH hext hSig
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  set D : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R'} with hD
  set t₀ : ℝ := v + R' / 2 with ht₀
  have hmem : ∀ (t : ℝ) (z : ℂ), z ∈ D → t₀ ≤ t → ((t, z) : E0) ∈ bspear v R' :=
    fun t z hz ht => mem_bspear_vertical hz.1 hz.2 (by linarith [hz.2])
  have hmono : ∀ z ∈ D, ∀ s t, t₀ ≤ s → s ≤ t →
      (CE X).le ⊤ (ψ (paperInY ((s, z) : E0))) (ψ (paperInY ((t, z) : E0))) :=
    fun z hz s t hs hst => le_of_mem_bspear hW hsub hψ (hmem s z hz hs)
      (hmem t z hz (hs.trans hst)) ((E0.le_top_iff).1 (le_vertical_top hst))
  have hcont : ∀ t, t₀ ≤ t → ContinuousOn (fun z : ℂ => ψ (paperInY ((t, z) : E0))) D :=
    fun t ht => hψc.comp
      (continuous_paperInY.comp (continuous_const.prodMk continuous_id)).continuousOn
      fun z hz => hsub ⟨_, hmem t z hz ht, rfl⟩
  have hS : ∀ z ∈ D, ψ (paperInY ((τS z, z) : E0)) ∈ Sig := fun z hz =>
    (hgraph _ (hmem _ z hz (hpos z hz.1 hz.2).le)).2 rfl
  have hJJ : (CE X).Jplus ⊤ Sig ∩ (CE X).Jminus ⊤ Sig = Sig :=
    Causal.Causality.Jplus_inter_Jminus_eq hGH.1 hac
  intro z hz
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_cases hat : a < t₀
    · exact eventually_nhdsWithin_of_forall fun z' hz'' => hat.trans (hpos z' hz''.1 hz''.2)
    push Not at hat
    have hnot : ψ (paperInY ((a, z) : E0)) ∉ (CE X).Jplus ⊤ Sig := by
      intro h
      have hJ : ψ (paperInY ((a, z) : E0)) ∈ (CE X).Jminus ⊤ Sig :=
        ⟨_, hS z hz, hmono z hz a (τS z) hat ha.le⟩
      have hin : ψ (paperInY ((a, z) : E0)) ∈ Sig := by rw [← hJJ]; exact ⟨h, hJ⟩
      have h1 : a = τS z := (hgraph _ (hmem a z hz hat)).1 hin
      linarith
    filter_upwards [hcont a hat z hz (hJp.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
      with z' h1 h2
    by_contra hle
    push Not at hle
    exact h1 ⟨_, hS z' h2, hmono z' h2 (τS z') a (hpos z' h2.1 h2.2).le hle⟩
  · have hbt : t₀ ≤ b := ((hpos z hz.1 hz.2).trans hb).le
    have hnot : ψ (paperInY ((b, z) : E0)) ∉ (CE X).Jminus ⊤ Sig := by
      intro h
      have hJ : ψ (paperInY ((b, z) : E0)) ∈ (CE X).Jplus ⊤ Sig :=
        ⟨_, hS z hz, hmono z hz (τS z) b (hpos z hz.1 hz.2).le hb.le⟩
      have hin : ψ (paperInY ((b, z) : E0)) ∈ Sig := by rw [← hJJ]; exact ⟨hJ, h⟩
      have h1 : b = τS z := (hgraph _ (hmem b z hz hbt)).1 hin
      linarith
    filter_upwards [hcont b hbt z hz (hJm.isOpen_compl.mem_nhds hnot), self_mem_nhdsWithin]
      with z' h1 h2
    by_contra hle
    push Not at hle
    exact h1 ⟨_, hS z' h2, hmono z' h2 b (τS z') hbt hle⟩

/-- **B21/btz Lemma `lem:blunt_spear_neighborhood`, core** (`BTZ_1.tex:693–701`): in a globally
hyperbolic `𝔼₀`-manifold `X` with a Cauchy surface `Σ`, a blunt spear chart `ψ` whose vertical
null rays have no future endpoint (`hvert`) and whose in-falling null rays have no past endpoint
(`hfall`) can be shrunk to a radius `R′ ≤ R`, same `ψ` and same vertex, so that `Σ` meets the
shrunk blunt spear only in its shaft region `τ > v + R′/2`, exactly along the graph of a
continuous `τ_Σ` over the punctured closed disc `𝔻*_{R′}`. -/
theorem lem_blunt_spear_of_inextensible (hGH : (CE X).GloballyHyperbolic) {Sig : Set X}
    (hSig : (CE X).IsCauchySurface Sig) {v R : ℝ} {W : Set E0Y} {ψ : E0Y → X} (hR : 0 < R)
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W)
    (hvert : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → ∀ q : X,
      ¬ Tendsto (fun t : ℝ => ψ (paperInY (t, z))) atTop (𝓝 q))
    (hfall : ∀ a : ℝ, v < a → ∀ u : ℂ, ‖u‖ = 1 → ∀ q : X,
      ¬ Tendsto (fun s : ℝ => ψ (paperInY (a + s / 2, (s : ℂ) * u))) (𝓝[>] 0) (𝓝 q)) :
    ∃ R', 0 < R' ∧ R' ≤ R ∧ IsBluntSpearNbhd R' (ψ '' bspearY v R') ∧
      ψ '' bspearY v R' ⊆ ψ '' bspearY v R ∧
      (∀ x ∈ bspear v R', ψ (paperInY x) ∈ Sig → v + R' / 2 < x.1) ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R'} ∧
        (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ bspear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
  have hext := E0LM.e0_curvesExtend hGH
  have hac := hSig.isAcausal E0LM.e0_causallyArcConnected hext
  have hpi : 0 < 4 * π ^ 2 := by positivity
  -- one point `ξ₂` of `Σ` in the blunt spear, at an `f`-level `≥ a⋆` far above the vertex
  set a : ℝ := v + R / 2 + 4 * π ^ 2 * R with ha
  have hva' : v < a := by nlinarith
  have hva : v ≤ a := hva'.le
  have hu : ‖(1 : ℂ)‖ = 1 := norm_one
  obtain ⟨ξ₂, hξ₂, hξ₂S, hξ₂f⟩ : ∃ ξ₂ ∈ bspear v R, ψ (paperInY ξ₂) ∈ Sig ∧ a ≤ fcoord ξ₂ := by
    by_cases he : ψ (paperInY (a + R / 2, (R : ℂ) * 1)) ∈ (CE X).Jplus ⊤ Sig
    · obtain ⟨s, hs, hsR, hsS⟩ := binfall_meets hGH hSig hW hsub hψ hva hu
        (hfall a hva' 1 hu) hR le_rfl he
      refine ⟨_, mem_bspear_infall hu hva hs hsR, hsS, ?_⟩
      simp only [fcoord, rad_infall hu hs.le]; linarith
    · have hJ : ψ (paperInY (a + R / 2, (R : ℂ) * 1)) ∈ (CE X).Jminus ⊤ Sig :=
        (Causal.Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hSig _).resolve_left he
      have hz : ‖(R : ℂ) * 1‖ = R := by
        rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      obtain ⟨t, ht, htS⟩ := bvertical_meets hGH hSig hW hsub hψ (by rw [hz]; exact hR)
        hz.le (hvert _ (by rw [hz]; exact hR) hz.le) (by rw [hz]; linarith) hJ
      refine ⟨_, mem_bspear_vertical (by rw [hz]; exact hR) hz.le (by rw [hz]; linarith),
        htS, ?_⟩
      simp only [fcoord, rad, hz]; linarith
  set r₂ : ℝ := rad ξ₂ with hr₂
  have hr₂0 : 0 < r₂ := hξ₂.2.1
  have hr₂R : r₂ ≤ R := hξ₂.2.2
  set R' : ℝ := r₂ / 2 with hR'
  have hR'0 : 0 < R' := by positivity
  have hR'R : R' ≤ R := by linarith
  have hbR : bspear v R' ⊆ bspear v R := bspear_mono hR'R
  -- below the level `v + R′/2`, the shrunk blunt spear is in `J⁻(Σ) ∖ Σ`
  have hlow : ∀ x ∈ bspear v R', x.1 ≤ v + R' / 2 →
      ψ (paperInY x) ∈ (CE X).Jminus ⊤ Sig ∧ ψ (paperInY x) ∉ Sig := by
    intro x hx hxτ
    have hle : Le x ξ₂ := by
      refine le_of_small_rad (by rw [← hr₂]; exact hx.2.2) ?_
      have h1 : fcoord x ≤ v + R / 2 := by
        simp only [fcoord]; linarith [hx.2.1, rad_nonneg x]
      have h2 : 4 * π ^ 2 * rad x ≤ 4 * π ^ 2 * R :=
        mul_le_mul_of_nonneg_left (hx.2.2.trans hR'R) hpi.le
      linarith
    have hleX := le_of_mem_bspear hW hsub hψ (hbR hx) hξ₂ hle
    refine ⟨⟨_, hξ₂S, hleX⟩, fun hxS => ?_⟩
    have heq := hac _ hxS _ hξ₂S hleX
    have h2 := hinj (hsub ⟨_, hbR hx, rfl⟩) (hsub ⟨_, hξ₂, rfl⟩) heq
    have h3 : x = ξ₂ := paperInY.injOn (by simp) (by simp) h2
    have h4 : fcoord x ≤ v + R / 2 := by
      simp only [fcoord]; linarith [hx.2.1, rad_nonneg x]
    rw [h3] at h4
    have : 0 < 4 * π ^ 2 * R := mul_pos hpi hR
    linarith
  -- the shaft
  have hshaft : ∀ x ∈ bspear v R', ψ (paperInY x) ∈ Sig → v + R' / 2 < x.1 := by
    intro x hx hxS
    by_contra hτ
    push Not at hτ
    exact (hlow x hx hτ).2 hxS
  -- every vertical line meets `Σ`, exactly once
  have hmeet : ∀ z : ℂ, 0 < ‖z‖ ∧ ‖z‖ ≤ R' →
      ∃ τ : ℝ, ((τ, z) : E0) ∈ bspear v R' ∧ ψ (paperInY (τ, z)) ∈ Sig := by
    rintro z ⟨hz0, hz⟩
    have hst : ((v + R' / 2, z) : E0) ∈ bspear v R' := mem_bspear_vertical hz0 hz (by linarith)
    obtain ⟨t, ht, htS⟩ := bvertical_meets hGH hSig hW ((image_mono hbR).trans hsub) hψ hz0 hz
      (hvert z hz0 (hz.trans hR'R)) (by linarith) (hlow _ hst le_rfl).1
    exact ⟨t, mem_bspear_vertical hz0 hz (by linarith), htS⟩
  have huniq : ∀ x ∈ bspear v R', ∀ y ∈ bspear v R', x.2 = y.2 → ψ (paperInY x) ∈ Sig →
      ψ (paperInY y) ∈ Sig → x = y := by
    rintro ⟨τ₁, z⟩ hx ⟨τ₂, z'⟩ hy hzz hxS hyS
    simp only at hzz
    subst hzz
    have key : ∀ a b : ℝ, ((a, z) : E0) ∈ bspear v R' → ((b, z) : E0) ∈ bspear v R' → a ≤ b →
        ψ (paperInY (a, z)) ∈ Sig → ψ (paperInY (b, z)) ∈ Sig → a = b := by
      intro a b ha hb hab haS hbS
      have hle := le_of_mem_bspear hW hsub hψ (hbR ha) (hbR hb)
        ((E0.le_top_iff).1 (le_vertical_top hab))
      have heq := hac _ haS _ hbS hle
      have h2 := hinj (hsub ⟨_, hbR ha, rfl⟩) (hsub ⟨_, hbR hb, rfl⟩) heq
      have h3 := paperInY.injOn (by simp) (by simp) h2
      exact (Prod.mk.injEq _ _ _ _ ▸ h3).1
    rcases le_total τ₁ τ₂ with h | h
    · rw [key τ₁ τ₂ hx hy h hxS hyS]
    · rw [key τ₂ τ₁ hy hx h hyS hxS]
  classical
  let τS : ℂ → ℝ := fun z => if h : 0 < ‖z‖ ∧ ‖z‖ ≤ R' then (hmeet z h).choose else v + R'
  have hτS : ∀ z (hz : 0 < ‖z‖ ∧ ‖z‖ ≤ R'), ((τS z, z) : E0) ∈ bspear v R' ∧
      ψ (paperInY (τS z, z)) ∈ Sig := fun z hz => by
    simp only [τS, dif_pos hz]; exact (hmeet z hz).choose_spec
  have hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + R' / 2 < τS z := fun z hz0 hz =>
    hshaft _ (hτS z ⟨hz0, hz⟩).1 (hτS z ⟨hz0, hz⟩).2
  have hgraph : ∀ x ∈ bspear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
    intro x hx
    have hz : 0 < ‖x.2‖ ∧ ‖x.2‖ ≤ R' := ⟨hx.2.1, hx.2.2⟩
    constructor
    · intro hxS
      have := huniq x hx _ (hτS x.2 hz).1 rfl hxS (hτS x.2 hz).2
      rw [this]
    · intro hx1
      have : x = (τS x.2, x.2) := Prod.ext hx1 rfl
      rw [this]; exact (hτS x.2 hz).2
  have hsub' : bspearY v R' ⊆ W := (image_mono hbR).trans hsub
  exact ⟨R', hR'0, hR'R, ⟨hR'0, v, W, ψ, hW, hsub', hψ, hinj, rfl⟩,
    image_mono (image_mono hbR), hshaft, τS,
    continuousOn_tauS_blunt hGH hSig hW hsub' hψ hpos hgraph, hpos, hgraph⟩

end Core

/-! ### §4 The flat case: `lem:blunt_spear_neighborhood` as printed (`𝔼₀` scope) -/

section Flat

open E0AbsMax

variable {N : Causal.Flat.FlatSpacetime.{0} 2}

/-- **The charted causality of `FlatE0 N` is the flat causality of `N`.** -/
theorem ce_flatE0_eq (N : Causal.Flat.FlatSpacetime.{0} 2) :
    (CE (FlatE0 N) : Causal.Causality N) = Causal.Flat.flatCausality 2 N := by
  refine Causal.Causality.ext ?_ ?_
  · funext V x y; exact propext (flatE0_rel_iff N V x y).1
  · funext V x y; exact propext (flatE0_rel_iff N V x y).2

/-- **The vertical null rays of a blunt spear chart have no future endpoint** in a flat `N`.
At a limit point `q`, `f = κ ∘ ψ` (`κ` the chart of `N` at `q`, followed by `inl`) is a local
`G`-structomorphism on the connected component `U`, around the tail of the ray, of
`W ∩ ψ⁻¹(dom κ) ∩` the slit sector of the ray; by rigidity (`E0.exists_eqOn_sectorSmulInl`, built on
`E0.sectorChartBTZ_mem_aeAtlas` and `e0_eqOn_of_eqOn_open`) it is `inl ∘ (g • ·) ∘` the sector chart
on all of `U`. So along the tail `κ(ψ(t, z)) = g • D(t, ‖z‖, θ)`, whose time component
`t + ½‖z‖θ²` (after `g⁻¹`) tends to `+∞`, against its convergence to `g⁻¹ • κ q`. Injectivity of
`ψ` is not used. -/
theorem flat_vertical_noLimit {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) (_hinj : InjOn ψ W) {z : ℂ} (hz0 : 0 < ‖z‖)
    (hz : ‖z‖ ≤ R) (q : FlatE0 N) :
    ¬ Tendsto (fun t : ℝ => ψ (paperInY (t, z))) atTop (𝓝 q) := by
  intro hlim
  have hz' : z ≠ 0 := norm_pos_iff.1 hz0
  set y : E0 := (0, z) with hydef
  have hy : y.2 ≠ 0 := hz'
  set ray : ℝ → E0Y := fun t => paperInY ((t, z) : E0) with hray
  have hrayc : Continuous ray := continuous_paperInY.comp (continuous_id.prodMk continuous_const)
  have hsec : ∀ t : ℝ, ((t, z) : E0) ∈ sector y := fun t => by
    show z / z ∈ Complex.slitPlane
    rw [div_self hz']; exact Complex.one_mem_slitPlane
  set κ := chartAt E0Y q with hκ
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  set P : Set E0Y := paperInY '' sector y with hP
  have hPo : IsOpen P := isOpen_paperInY_image (isOpen_sector y)
  set V : Set E0Y := (W ∩ P) ∩ ψ ⁻¹' κ.source with hV
  have hVo : IsOpen V :=
    (hψc.mono inter_subset_left).isOpen_inter_preimage (hW.inter hPo) κ.open_source
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hlim.eventually (κ.open_source.mem_nhds (mem_chart_source E0Y q)))
  set T' := max T (v + ‖z‖ / 2) with hT'
  have htail : ∀ t, T' ≤ t → ray t ∈ V := fun t ht =>
    ⟨⟨hsub ⟨_, mem_bspear_vertical hz0 hz ((le_max_right _ _).trans ht), rfl⟩, ⟨_, hsec t, rfl⟩⟩,
      hT t ((le_max_left _ _).trans ht)⟩
  set U := connectedComponentIn V (ray T') with hU
  have hUo : IsOpen U := hVo.connectedComponentIn
  have hUV : U ⊆ V := connectedComponentIn_subset _ _
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have htailU : ∀ t, T' ≤ t → ray t ∈ U := by
    have hpre : IsPreconnected (ray '' Ici T') := isPreconnected_Ici.image _ hrayc.continuousOn
    have hsub' := hpre.subset_connectedComponentIn (x := ray T') ⟨T', self_mem_Ici, rfl⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact htail t ht)
    exact fun t ht => hsub' ⟨t, ht, rfl⟩
  set f : E0Y → E0Y := κ ∘ ψ with hf
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hψU : IsE0Mor ψ U :=
    Causal.CBG.liftPropOn_mono_of_le hW hUo hψ (fun y hy => (hUV hy).1.1)
  have hfU : IsE0Mor f U :=
    Causal.CBG.liftPropOn_comp hUo κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hψU
      (fun y hy => (hUV hy).2)
  have hfS : ∀ x ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U x := by
    intro x hx
    have h := (hfU x hx).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      preimage_id_eq] at h
    exact h
  have hfinl : ∀ x ∈ U, f x ∈ range Sum.inl := fun x _ => ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := exists_eqOn_sectorSmulInl hy hUo hUc ⟨ray T', htailU T' le_rfl⟩
    (fun x hx => (hUV hx).1.2) hfS hfinl
  set κN := chartAt (Causal.Minkowski 2) (show N from q) with hκN
  have hval : ∀ t, T' ≤ t →
      κN (ψ (ray t)) = g • btzPaperDev (t, ‖z‖, angle y ((0, z) : E0)) := by
    intro t ht
    have h := hg (htailU t ht)
    rw [sectorSmulInl_apply, sectorChartY_paperInY] at h
    exact Sum.inl_injective h
  have hconv : Tendsto (fun t => κN (ψ (ray t))) atTop (𝓝 (κN q)) :=
    ((chartAt (Causal.Minkowski 2) (show N from q)).continuousAt
      (mem_chart_source _ (show N from q))).tendsto.comp hlim
  have h2 : Tendsto (fun t => (g⁻¹ • κN (ψ (ray t))).1) atTop (𝓝 ((g⁻¹ • κN q).1)) :=
    (continuous_fst.tendsto _).comp (((continuous_const_smul g⁻¹).tendsto _).comp hconv)
  have h3 : Tendsto (fun t => (g⁻¹ • κN (ψ (ray t))).1) atTop atTop := by
    refine (tendsto_atTop_add_const_right _ (1 / 2 * ‖z‖ * (angle y ((0, z) : E0)) ^ 2)
      tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop T'] with t ht
    rw [hval t ht, inv_smul_smul]
    rfl
  exact not_tendsto_nhds_of_tendsto_atTop h3 _ h2

/-- **The in-falling null rays of a blunt spear chart have no past endpoint** in a flat `N`. -/
theorem flat_infall_noLimit {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) {a : ℝ} (ha : v < a)
    {u : ℂ} (hu : ‖u‖ = 1) (q : FlatE0 N) :
    ¬ Tendsto (fun s : ℝ => ψ (paperInY (a + s / 2, (s : ℂ) * u))) (𝓝[>] 0) (𝓝 q) := by
  sorry -- SORRY(btzlem:blunt_spear_neighborhood): parabolic holonomy at a regular limit point

/-- **btz Lemma `lem:blunt_spear_neighborhood`** (`BTZ_1.tex:693–701`), flat case (`𝔼₀` scope:
`M` has no massive particle, so it is a flat spacetime `N`): for a globally hyperbolic `N`, a
Cauchy surface `Σ` and **the given** blunt spear chart `φ₀ = ψ⁻¹` of `𝒮₀ = ψ(bspearY v R)` (the
data `v, W, ψ` of `IsBluntSpearNbhd.chart`, taken as hypotheses, so the conclusion is about
`φ₀` itself), there is `R′ ≤ R` such that `𝒮 = ψ(bspearY v R′) ⊆ 𝒮₀` is a blunt spear
neighbourhood with chart the restriction of `φ₀` (`φ = φ₀|𝒮`) and the same vertex, the same
lower bounds (`inf φ(𝒮) = inf φ(𝒮₀)`, `lowerBounds_bspear_iff`), `Σ ∩ 𝒮` in the shaft region,
and `ψ⁻¹(Σ ∩ 𝒮)` the graph of a continuous `τ_Σ > v + R′/2` over the punctured closed disc. -/
theorem lem_blunt_spear (hGH : Causal.Flat.GH N) {Sig : Set N}
    (hSig : (Causal.Flat.flatCausality 2 N).IsCauchySurface Sig) {v R : ℝ} {W : Set E0Y}
    {ψ : E0Y → FlatE0 N} (hR : 0 < R) (hW : IsOpen W) (hsub : bspearY v R ⊆ W)
    (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) :
    ∃ R', 0 < R' ∧ R' ≤ R ∧ IsBluntSpearNbhd R' (ψ '' bspearY v R') ∧
      ψ '' bspearY v R' ⊆ ψ '' bspearY v R ∧
      (∀ y : E0, (∀ x ∈ bspear v R', Le y x) ↔ ∀ x ∈ bspear v R, Le y x) ∧
      (∀ x ∈ bspear v R', ψ (paperInY x) ∈ Sig → v + R' / 2 < x.1) ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R'} ∧
        (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        ∀ x ∈ bspear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2) := by
  have hGH' : (CE (FlatE0 N)).GloballyHyperbolic := by
    have h := ce_flatE0_eq N
    unfold Causal.Flat.GH at hGH
    rw [← h] at hGH
    exact hGH
  have hSig' : (CE (FlatE0 N)).IsCauchySurface Sig := by
    have h := ce_flatE0_eq N
    rw [← h] at hSig
    exact hSig
  obtain ⟨R', hR'0, hR'R, hS, hSS, hshaft, τS, hc, hpos, hgraph⟩ :=
    lem_blunt_spear_of_inextensible hGH' hSig' hR hW hsub hψ hinj
      (fun z hz0 hz q => flat_vertical_noLimit hW hsub hψ hinj hz0 hz q)
      (fun a ha u hu q => flat_infall_noLimit hW hsub hψ hinj ha hu q)
  exact ⟨R', hR'0, hR'R, hS, hSS, lowerBounds_bspear_iff hR'0 hR'R, hshaft, τS, hc, hpos, hgraph⟩

end Flat

end E0BluntSpear

end GX
