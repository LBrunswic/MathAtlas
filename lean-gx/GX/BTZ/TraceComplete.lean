import GX.BTZ.TraceDev
import GX.BTZ.AxisNoLimit

/-!
# The trace of a complete spacelike-Lipschitz surface on a blunt spear chart goes to `+∞`

`btzthm:BTZ_Cauchy-completness` — `BTZ_1.tex:1582` (theorem), Step 1 of its proof, the second half
of l.1601, read in the flat setting of `GX.E0BluntSpear.lem_blunt_spear` (`BTZ_1.tex:693–701`) and
of `GX.E0TraceDev.trace_tendsto_atTop`. Unmarked: a step of the proof, not the theorem.
Target T-btz-trace-complete.

> By Lemma \ref{lem:blunt_spear_neighborhood}, one can reduce the size of $\S$ in such a way
> $\phi(\Sigma_0\cap \S)$ is the graph of a some function $\tau_0:\mathbb D_R^*\rightarrow \RR$
> in $\mass{0}$ with $\tau_0$. Since $\Sigma_0$ is complete, by Lemma \ref{lem:surface_complete}
> $ \lim_{(\r,\theta)\rightarrow 0}\tau_0(\r,\theta) = +\infty$. (l.1601)

* `GX.E0TraceComplete.trace_tendsto_atTop_of_complete` — for a flat `N`, a blunt spear chart
  `ψ : E0Y → FlatE0 N` on `W ⊇ bspearY v R` (`IsE0Mor ψ W`, `0 < R`), `Σ ⊆ N` spacelike Lipschitz
  whose induced length space is complete and finer than `N` (the last two fields of
  `Causal.Flat.IsCauchyComplete`), and `τ_Σ` continuous on `{0 < ‖z‖ ≤ R}`, above the shaft, with
  `ψ(paperInY x) ∈ Σ ↔ x.1 = τ_Σ x.2` on `bspear v R`: `τ_Σ(r e^{iθ}) → +∞` as `r → 0⁺`.
* `GX.E0TraceComplete.trace_tendsto_atTop_of_isCauchyComplete` — the target's form: the setting of
  `trace_tendsto_atTop` with `0 < R″ < R`, its `hcomp` replaced by those two fields.
* Tools: `exists_traceSig` (the strip maps continuously into `Σ`, and the induced length of the
  image of a path is its pulled length, through `trace_chart_local` and the strict
  `Causal.Flat.pathLength_pulled_eq_of_local`); `pathLength_seg_unif` (the straight piece's bound
  as a path length); `brokenLine`, `continuous_brokenLine`.

Proof (the route of the target, (2)). With `R″ = R/2`, if `τ_Σ` stays below `A` near the axis,
`lem_surface_complete_two_unif`'s broken line `u n` (radius halving, `τ < A`) has pieces of pulled
length `T n` with `∑ T n < ∞` (`UnifSpacelike` from `trace_spacelikeDevelopment_openStrip`). Its
image in `Σ` has the same lengths, so its vertices are Cauchy in `InducedLengthSpace 2 Σ`, with a
limit `a`; every point of the `n`-th piece is within `T n` of a vertex, so the whole broken line
converges to `a` in the induced length, hence in `N` by the continuity field. Read in `𝔼₀` it is a
continuous curve of the blunt spear with radius `→ 0` converging in `N`, against
`GX.E0AxisNoLimit.flat_curve_noLimit`.

## Hypothesis checklist

| hypothesis (the target's setting) | here |
|---|---|
| `N` flat, `ψ`, `IsOpen W`, `bspearY v R ⊆ W`, `IsE0Mor ψ W` | ✓ carried |
| `InjOn ψ W` | ⚠ weakened: not used |
| `Σ` spacelike Lipschitz | ✓ carried; `Σ` Cauchy not used |
| `τ_Σ` continuous on `{0 < ‖z‖ ≤ R}`, `v + ‖z‖/2 < τ_Σ z`, graph equivalence on `bspear v R` | ✓ carried (the setting of `trace_tendsto_atTop`) |
| `0 < R″ < R` | ⚠ weakened: `0 < R` suffices (`_of_complete`); the `R″` form is a corollary |
| « `Σ₀` complete » | ✓ `CompleteSpace (InducedLengthSpace 2 Σ)` and continuity of `toSubtype` into `N`, the last two fields of `IsCauchyComplete` (OQ-152 (b), the reading `CauchySpear` takes) |

## Instance (non-vacuity), checked by hand, not as a Lean term (kb/0011: not cheap)

`N` the flat regular part `{r > 0}` of `𝔼₀` (the instance the T-btz-axis-nolimit audit names for
`flat_curve_noLimit`: `W` the regular points of `paperInY`'s image, `ψ` the identification),
`v = 0`, `R = 1`, `R″ = 1/2`, `τ_Σ z = 1/‖z‖`, `Σ = {τ = 1/r}`. Every hypothesis: `τ_Σ` is
continuous on `0 < ‖z‖`; `hpos` is `‖z‖/2 < 1/‖z‖`, i.e. `‖z‖² < 2`, true for `‖z‖ ≤ 1`; the graph
equivalence holds because `ψ ∘ paperInY` is injective off the axis and `rad x > 0` on `bspear`.
The metric read off `btzPaperDev` (`minkQ` of a velocity is `−2τ′r′ + r′² + r²θ′²`, `hX` of
`edist_le_seg_unif`) is, on `Σ` (`τ′ = −r′/r²`), `(1 + 2/r²) dr² + r² dθ²`: positive definite, so
`Σ` is a smooth spacelike surface, locally a graph of slope `< 1` (spacelike Lipschitz). With
`ρ′ = √(1 + 2/r²)`, `ρ(r) → −∞` at `0` (`ρ′ ≥ √2/r`) and `→ +∞` at `∞` (`ρ′ ≥ 1`), and the induced
distance is at least `|Δρ|`; so a Cauchy sequence stays in an annulus `r₁ ≤ r ≤ r₂`, compact, on
which the induced and subspace topologies agree (the metric is uniformly comparable to
`dr² + dθ²`): it converges. The same comparison gives the continuity of `toSubtype`. The
conclusion holds there (`1/r → +∞`), as it must.

## SCOPE (disclosed)

* A step of the proof of `btzthm:BTZ_Cauchy-completness`, not the theorem; `𝔼₀` only
  (T-btz-scope). The proof uses reading (a) of OQ-158 only through
  `trace_spacelikeDevelopment_openStrip` (`Ω = openStrip R`); the statement does not mention it.
* Completeness of the pulled length of the trace itself (`hcomp` of `trace_tendsto_atTop`) is not
  proved, and not needed.
* 0 `sorry`; standard axioms only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; imports
`GX.BTZ.TraceDev` and `GX.BTZ.AxisNoLimit` (graduated with this file, T-btz-trace-graduate).
`pathLength_seg_unif` repeats the proof of `E0Surgery.edist_le_seg_unif`
(`GX/BTZ/C1SpacelikeDevLip.lean:144`). Written by T-btz-trace-complete (2026-11-28).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace MeasureTheory
open scoped Real ENNReal NNReal

namespace E0TraceComplete

open E0 E0CBG E0Spear E0BluntSpear E0Surgery E0AbsMax E0TraceDev BTZIsom

variable {N : Causal.Flat.FlatSpacetime.{0} 2}

/-- The point `(τ_Σ(r e^{iθ}), r e^{iθ})` of `𝔼₀` over the strip point `(r, θ)`. -/
noncomputable def tracePt (τS : ℂ → ℝ) (p : ℝ × ℝ) : E0 :=
  (traceFun τS p, (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))

/-- The trace point lies in the open part of the blunt spear, at radius `r`. -/
theorem tracePt_mem {v R : ℝ} {τS : ℂ → ℝ}
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z) {p : ℝ × ℝ}
    (hp : p ∈ stripSet R) : v < fcoord (tracePt τS p) ∧ rad (tracePt τS p) = p.1 := by
  have hn := norm_polar hp.1.le p.2
  have hrad : rad (tracePt τS p) = p.1 := hn
  refine ⟨?_, hrad⟩
  have h := hpos _ (by rw [hn]; exact hp.1) (by rw [hn]; exact hp.2)
  rw [hn] at h
  simp only [fcoord, hrad]
  simp only [tracePt, traceFun]
  linarith

/-- The trace point lies in the blunt spear. -/
theorem tracePt_mem_bspear {v R : ℝ} {τS : ℂ → ℝ}
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z) {p : ℝ × ℝ}
    (hp : p ∈ stripSet R) : tracePt τS p ∈ bspear v R := by
  obtain ⟨h1, h2⟩ := tracePt_mem hpos hp
  exact ⟨h1.le, h2 ▸ hp.1, h2 ▸ hp.2⟩

/-- The trace point is continuous on the strip. -/
theorem continuousOn_tracePt {R : ℝ} {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R}) :
    ContinuousOn (tracePt τS) (stripSet R) := by
  have h1 : ContinuousOn (traceFun τS) (stripSet R) := by
    refine hc.comp (by fun_prop) fun p hp => ?_
    rw [mem_setOf_eq, norm_polar hp.1.le]
    exact hp
  exact h1.prodMk (by fun_prop)

/-- **The chart of `N` along the trace** (`flatE0_regChart`, `graphDev_eq_shift_sectorChartY`):
near each point `q` of the strip `(0, R′] × ℝ`, `R′ < R`, the development of the trace is an
isometry of `𝐌³` composed with the chart of `N` at the point of `Σ` over `q`. -/
theorem trace_chart_local {v R R' : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z) (hR'R : R' < R)
    (q : Strip R') :
    ∃ k : Causal.Flat.isom 2, ∀ᶠ q' in 𝓝 q, graphDev (traceFun τS) R' q' =
      k • chartAt (Causal.Minkowski 2) (show N from ψ (paperInY (tracePt τS q.1)))
        (show N from ψ (paperInY (tracePt τS q'.1))) := by
  rcases q with ⟨⟨r0, θ0⟩, hr0, hr0R'⟩
  simp only at hr0 hr0R'
  have hgc : Continuous fun q : Strip R' => traceFun τS q.1 :=
    continuous_traceFun (hc.mono fun z hz => ⟨hz.1, hz.2.trans hR'R.le⟩)
  set x0 : E0 := tracePt τS (r0, θ0) with hx0
  have hy : x0.2 ≠ 0 := by
    intro h; have := congrArg norm h; rw [norm_zero] at this
    rw [show x0.2 = (r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I) from rfl,
      norm_polar hr0.le θ0] at this
    exact hr0.ne' this
  set B : Set E0 := {x | v < fcoord x ∧ 0 < rad x ∧ rad x < R} with hB
  have hradc : Continuous rad := continuous_norm.comp continuous_snd
  have hBo : IsOpen B :=
    ((isOpen_lt continuous_const (continuous_fst.sub (hradc.div_const 2))).inter
      ((isOpen_lt continuous_const hradc).inter (isOpen_lt hradc continuous_const)))
  have hBsub : B ⊆ bspear v R := fun x hx => ⟨hx.1.le, hx.2.1, hx.2.2.le⟩
  have hx0B : x0 ∈ B := by
    obtain ⟨h1, h2⟩ := tracePt_mem hpos (R := R) (p := (r0, θ0))
      ⟨hr0, hr0R'.trans hR'R.le⟩
    exact ⟨h1, by rw [h2]; exact hr0, by rw [h2]; exact lt_of_le_of_lt hr0R' hR'R⟩
  have hx0W : paperInY x0 ∈ W := hsub ⟨x0, hBsub hx0B, rfl⟩
  obtain ⟨U1, h, hU1o, hx0U1, -, -, hU1eq⟩ :=
    flatE0_regChart (hW.inter (isOpen_paperInY_image hBo))
      (Causal.CBG.liftPropOn_mono_of_le hW (hW.inter (isOpen_paperInY_image hBo)) hψ
        (fun y hy => hy.1)) hy
      ⟨hx0W, x0, hx0B, rfl⟩ ⟨x0, mem_sector_self hy, rfl⟩
  refine ⟨gShift 0 (θ0 - Complex.arg x0.2) * h⁻¹, ?_⟩
  have hΦc : Continuous fun q : Strip R' => tracePt τS q.1 := hgc.prodMk (by fun_prop)
  have hopen : IsOpen {q : Strip R' | |q.1.2 - θ0| < π ∧ paperInY (tracePt τS q.1) ∈ U1} :=
    (isOpen_lt ((continuous_snd.comp continuous_subtype_val).sub continuous_const).abs
      continuous_const).inter (hU1o.preimage (continuous_paperInY.comp hΦc))
  have hmem : (⟨(r0, θ0), hr0, hr0R'⟩ : Strip R') ∈
      {q : Strip R' | |q.1.2 - θ0| < π ∧ paperInY (tracePt τS q.1) ∈ U1} := by
    refine ⟨?_, hx0U1⟩
    show |θ0 - θ0| < π
    rw [sub_self, abs_zero]; exact Real.pi_pos
  filter_upwards [hopen.mem_nhds hmem] with q' hq'
  obtain ⟨hθ, hu⟩ := hq'
  rw [graphDev_eq_shift_sectorChartY hr0 rfl hy q' hθ]
  have e := hU1eq _ hu
  change _ = _ • chartAt (Causal.Minkowski 2) (show N from ψ (paperInY x0))
    (show N from ψ (paperInY (tracePt τS q'.1)))
  rw [e, mul_smul, inv_smul_smul]
  rfl

/-- **The length comparison**: over `(0, R′] × ℝ`, `R′ < R`, the map from the strip to `Σ` along
the trace is continuous, and sends every path to a path of `Σ` of the same induced length as its
pulled length under `graphDev (traceFun τS) R′`. -/
theorem exists_traceSig {v R R' : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) (hR'R : R' < R) :
    ∃ (Φ : Strip R' → Sig) (hΦ : Continuous Φ),
      (∀ q, (Φ q : N) = ψ (paperInY (tracePt τS q.1))) ∧
      ∀ {a b : Strip R'} (γ : Path a b),
        Causal.Flat.pathLength (Causal.Flat.chartSys 2 Sig) (γ.map hΦ) =
          Causal.Flat.pathLength (fun (_ : Strip R') z => graphDev (traceFun τS) R' z) γ := by
  have hstrip : ∀ q : Strip R', (q.1 : ℝ × ℝ) ∈ stripSet R := fun q => ⟨q.2.1, q.2.2.trans hR'R.le⟩
  have hmemS : ∀ q : Strip R', (show N from ψ (paperInY (tracePt τS q.1))) ∈ Sig := fun q =>
    (hgraph _ (tracePt_mem_bspear hpos (hstrip q))).2 rfl
  set Φ : Strip R' → Sig := fun q => ⟨_, hmemS q⟩ with hΦ
  have hΦc' : Continuous fun q : Strip R' => tracePt τS q.1 :=
    (continuousOn_tracePt hc).comp_continuous continuous_subtype_val hstrip
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hΦc : Continuous Φ := by
    refine Continuous.subtype_mk ?_ _
    exact hψc.comp_continuous (continuous_paperInY.comp hΦc') fun q =>
      hsub ⟨_, tracePt_mem_bspear hpos (hstrip q), rfl⟩
  refine ⟨Φ, hΦc, fun q => rfl, fun γ => ?_⟩
  exact (Causal.Flat.pathLength_pulled_eq_of_local _ _ hΦc
    (fun q => trace_chart_local hW hsub hψ hc hpos hR'R q) γ).symm

/-- **The length of a straight piece, as a path length** (`edist_le_seg_unif`, whose proof is
repeated verbatim, stopped one step earlier): the straight segment of the strip from `x′` to `y′`,
with `r_{y′} − r_{x′} ≥ r_{y′}/2` and `|θ_{y′} − θ_{x′}| ≤ π`, has pulled length at most
`(1 + 2π²)(r_{y′} − r_{x′}) − (g(y′) − g(x′))`. The bound on the path, not only on the distance,
is what bounds the distance to every point of the segment (`edist_le_pathLength`). -/
theorem pathLength_seg_unif {g : ℝ × ℝ → ℝ} {R : ℝ} (hU : UnifSpacelike g R) (x' y' : Strip R)
    (hab : (y' : ℝ × ℝ).1 / 2 ≤ (y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1)
    (hθ : |(y' : ℝ × ℝ).2 - (x' : ℝ × ℝ).2| ≤ π) :
    0 ≤ (1 + 2 * π ^ 2) * ((y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1) - (g y' - g x') ∧
    Causal.Flat.pathLength (fun (_ : Strip R) z => graphDev g R z) (stripSegment x' y') ≤
      ENNReal.ofReal ((1 + 2 * π ^ 2) * ((y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1) -
        (g y' - g x')) := by
  set V : ℝ × ℝ := (y' : ℝ × ℝ) - x' with hV
  set pt : ℝ → ℝ × ℝ := fun s => (x' : ℝ × ℝ) + s • V with hpt
  have hptm : ∀ s ∈ Icc (0 : ℝ) 1, pt s ∈ stripSet R := fun s hs =>
    stripSegment_mem x' y' ⟨s, hs⟩
  have hptd : ∀ s, HasDerivAt pt V s := fun s => by
    have := ((hasDerivAt_id s).smul_const V).const_add (x' : ℝ × ℝ)
    simp only [id, one_smul] at this
    exact this
  have hptL : LipschitzWith ‖V‖₊ pt := LipschitzWith.of_dist_le_mul fun s t => by
    simp only [hpt]
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, coe_nnnorm,
      Real.dist_eq, mul_comm]
  -- step (1) along the segment: `τ = g ∘ pt` is Lipschitz on `[0, 1]`
  set τ : ℝ → ℝ := fun s => g (pt s) with hτ
  have hτloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) τ := by
    intro t ht
    obtain ⟨K, T, hT, hKT⟩ := locallyLipschitzOn_of_unif hU (hptm t ht)
    have hcont : Tendsto pt (𝓝[Icc (0 : ℝ) 1] t) (𝓝[stripSet R] (pt t)) :=
      hptL.continuous.continuousWithinAt.tendsto_nhdsWithin hptm
    exact ⟨K * ‖V‖₊, Icc 0 1 ∩ pt ⁻¹' T, inter_mem self_mem_nhdsWithin (hcont hT),
      hKT.comp hptL.lipschitzOnWith (fun s hs => hs.2)⟩
  obtain ⟨Kτ, hKτ⟩ := hτloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  set q : ℝ → ℝ := fun s => (projIcc (0 : ℝ) 1 zero_le_one s : ℝ) with hq
  have hqL : LipschitzWith 1 q := by
    have := (LipschitzWith.subtype_val _).comp (LipschitzWith.projIcc (zero_le_one' ℝ))
    rw [mul_one] at this
    exact this
  have hqI : ∀ s, q s ∈ Icc (0 : ℝ) 1 := fun s => (projIcc 0 1 zero_le_one s).2
  have hqq : ∀ s, q (q s) = q s := fun s => by simp only [hq, projIcc_val]
  set τe : ℝ → ℝ := fun s => τ (q s) with hτe
  have hτeL : LipschitzWith Kτ τe := by
    have := lipschitzOnWith_univ.1 (hKτ.comp hqL.lipschitzOnWith (fun s _ => hqI s))
    rw [mul_one] at this
    exact this
  -- the developed segment is Lipschitz
  set σ := stripSegment x' y' with hσ
  set c3 : ℝ → ℝ × ℝ × ℝ := fun s => (τe s, (pt (q s)).1, (pt (q s)).2) with hc3
  have hpqL : LipschitzWith (‖V‖₊ * 1) fun s => pt (q s) := hptL.comp hqL
  have hc3L := hτeL.prodMk ((LipschitzWith.prod_fst.comp hpqL).prodMk
    (LipschitzWith.prod_snd.comp hpqL))
  have hc3m : ∀ s, c3 s ∈ c3 '' Icc 0 1 := fun s => ⟨q s, hqI s, by simp only [hc3, hτe, hqq]⟩
  obtain ⟨KD, hKD⟩ := (contDiff_btzPaperDev.locallyLipschitz.locallyLipschitzOn
    (s := c3 '' Icc 0 1)).exists_lipschitzOnWith_of_compact
      (isCompact_Icc.image hc3L.continuous)
  have hΓL : LipschitzWith _ fun s => graphDev g R (σ.extend s) :=
    lipschitzOnWith_univ.1 (hKD.comp hc3L.lipschitzOnWith (fun s _ => hc3m s))
  have hloc : Causal.Flat.IsLocLip (fun (_ : Strip R) z => graphDev g R z) σ.extend :=
    (Causal.Flat.isLocLip_pulled_iff _ _).2 ⟨_, hΓL⟩
  -- the pointwise bound, almost everywhere
  have hu : 0 < V.1 := by
    have := y'.2.1
    simp only [hV, Prod.fst_sub]; linarith
  have hab' : (y' : ℝ × ℝ).1 / 2 ≤ V.1 := by simpa [hV] using hab
  have hθ' : |V.2| ≤ π := by simpa [hV] using hθ
  set f : ℝ → ℝ := fun t => (1 + 2 * π ^ 2) * V.1 - deriv τe t with hf
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      Causal.Flat.localDensity (fun (_ : Strip R) z => graphDev g R z) σ.extend t ≤
        ENNReal.ofReal (f t) ∧ 0 ≤ f t := by
    have h1 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ∈ Ioo (0 : ℝ) 1 := by
      rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [h1, ae_restrict_of_ae hτeL.ae_differentiableAt_real] with t ht hdt
    have hqt : ∀ᶠ s in 𝓝 t, q s = s := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      simp only [hq, projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩]
    have hpq : HasDerivAt (fun s => pt (q s)) V t :=
      (hptd t).congr_of_eventuallyEq (by filter_upwards [hqt] with s hs; rw [hs])
    set τ' := deriv τe t with hτ'
    have hc3d : HasDerivAt c3 ((τ', V.1, V.2) : ℝ × ℝ × ℝ) t :=
      hdt.hasDerivAt.prodMk
        (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hpq).prodMk
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hpq))
    have hΓd : HasDerivAt (fun s => graphDev g R (σ.extend s))
        (fderiv ℝ btzPaperDev (c3 t) (τ', V.1, V.2)) t :=
      (differentiableAt_btzPaperDev (c3 t)).hasFDerivAt.comp_hasDerivAt t hc3d
    have hqt' : q t = t := hqt.self_of_nhds
    have hX : Causal.Flat.minkQ (fderiv ℝ btzPaperDev (c3 t) (τ', V.1, V.2)) =
        -2 * τ' * V.1 + V.1 ^ 2 + (pt t).1 ^ 2 * V.2 ^ 2 := by
      rw [btzPaperDev_pullback]; simp only [hc3, hqt']
    have hX0 : 0 ≤ Causal.Flat.minkQ (fderiv ℝ btzPaperDev (c3 t) (τ', V.1, V.2)) := by
      refine minkQ_nonneg_of_hasDerivAt hΓd ?_
      obtain ⟨W, hW, κ, hκ, hWκ⟩ := hU (σ.extend t)
      filter_upwards [σ.continuous_extend.continuousAt.eventually_mem hW] with s hs
      exact le_trans (by positivity) (hWκ _ hs _ (mem_of_mem_nhds hW))
    have hden : Causal.Flat.localDensity (fun (_ : Strip R) z => graphDev g R z) σ.extend t =
        ENNReal.ofReal (Real.sqrt (-2 * τ' * V.1 + V.1 ^ 2 + (pt t).1 ^ 2 * V.2 ^ 2)) := by
      unfold Causal.Flat.localDensity
      rw [hΓd.deriv, hX]
    have hm := hptm t (Ioo_subset_Icc_self ht)
    have hrb : (pt t).1 ≤ (y' : ℝ × ℝ).1 := by
      have e1 : (pt t).1 = (x' : ℝ × ℝ).1 + t * V.1 := by simp [hpt]
      have e2 : V.1 = (y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1 := by simp [hV]
      have : t * V.1 ≤ V.1 := by nlinarith [ht.2, hu]
      rw [e1]; linarith
    have hq : graphQuad (τ' / V.1) 0 (pt t).1 V.1 V.2 =
        -2 * τ' * V.1 + V.1 ^ 2 + (pt t).1 ^ 2 * V.2 ^ 2 := by
      unfold graphQuad; field_simp; ring
    have key := sqrt_graphQuad_le_seg hu hab' hm.1 hrb hθ' (by rw [hq, ← hX]; exact hX0)
    rw [hq] at key
    have e : (1 + 2 * π ^ 2) * V.1 - (V.1 * (τ' / V.1) + V.2 * 0) = f t := by
      simp only [hf, ← hτ']; field_simp; ring
    rw [e] at key
    refine ⟨?_, (Real.sqrt_nonneg _).trans key⟩
    rw [hden]; exact ENNReal.ofReal_le_ofReal key
  -- integrate `τ'`
  have hac : AbsolutelyContinuousOnInterval τe 0 1 :=
    (hτeL.lipschitzOnWith (s := uIcc 0 1)).absolutelyContinuousOnInterval
  have hint : IntervalIntegrable (deriv τe) volume 0 1 := hac.intervalIntegrable_deriv
  have hftc : ∫ t in (0 : ℝ)..1, deriv τe t = τe 1 - τe 0 := hac.integral_deriv_eq_sub
  have hτe1 : τe 1 = g y' := by
    simp only [hτe, hτ, hq, projIcc_right, hpt, hV, one_smul, add_sub_cancel]
  have hτe0 : τe 0 = g x' := by
    simp only [hτe, hτ, hq, projIcc_left, hpt, zero_smul, add_zero]
  set T := (1 + 2 * π ^ 2) * V.1 - (g y' - g x') with hT
  have hIi : IntegrableOn f (Ioc 0 1) :=
    (integrableOn_const (by simp)).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint)
  have hTi : ∫ t in Ioc (0 : ℝ) 1, f t = T := by
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_sub
      intervalIntegrable_const hint, hftc, hτe1, hτe0]
    simp [hT]
  have hTe : (1 + 2 * π ^ 2) * ((y' : ℝ × ℝ).1 - (x' : ℝ × ℝ).1) - (g y' - g x') = T := by
    simp [hT, hV]
  rw [hTe]
  refine ⟨?_, ?_⟩
  · rw [← hTi]
    exact MeasureTheory.integral_nonneg_of_ae (hae.mono fun t h => h.2)
  rw [Causal.Flat.pathLength_of_isLocLip _ hloc, ← hTi,
    ofReal_integral_eq_lintegral_ofReal hIi (hae.mono fun t h => h.2)]
  unfold Causal.Flat.localLength
  exact MeasureTheory.lintegral_mono_ae (hae.mono fun t h => h.1)

/-! ### The broken line -/

/-- **The broken line** through `u 0, u 1, …`: over `[n, n + 1]` the segment from `u n` to
`u (n + 1)`. -/
noncomputable def brokenLine (u : ℕ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  u ⌊t⌋₊ + (t - ⌊t⌋₊) • (u (⌊t⌋₊ + 1) - u ⌊t⌋₊)

/-- The `m`-th piece of the broken line, on `[m, m + 1]` (and on `(-∞, 1]` for `m = 0`). -/
theorem brokenLine_eq (u : ℕ → ℝ × ℝ) {m : ℕ} {t : ℝ} (h1 : (m : ℝ) ≤ t ∨ m = 0)
    (h2 : t ≤ m + 1) : brokenLine u t = u m + (t - m) • (u (m + 1) - u m) := by
  rcases h2.lt_or_eq with h2 | h2
  · have hf : ⌊t⌋₊ = m := by
      rcases h1 with h1 | rfl
      · exact (Nat.floor_eq_iff ((Nat.cast_nonneg m).trans h1)).2 ⟨h1, h2⟩
      · exact Nat.floor_eq_zero.2 (by simpa using h2)
    simp only [brokenLine, hf]
  · subst h2
    have hf : ⌊(m : ℝ) + 1⌋₊ = m + 1 := by rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp only [brokenLine, hf]
    push_cast
    rw [sub_self, zero_smul, add_zero, add_sub_cancel_left, one_smul, add_sub_cancel]

/-- **The broken line is continuous.** -/
theorem continuous_brokenLine (u : ℕ → ℝ × ℝ) : Continuous (brokenLine u) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have haff : ∀ m : ℕ, Continuous fun t : ℝ => u m + (t - m) • (u (m + 1) - u m) :=
    fun m => by fun_prop
  set n := ⌊t0⌋₊ with hn
  have hlt : t0 < n + 1 := Nat.lt_floor_add_one t0
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · by_cases hn0 : n = 0
    · refine (haff 0).continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ self_mem_Iic
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact brokenLine_eq u (Or.inr rfl) (by rw [hn0] at hlt; push_cast at hlt ⊢; linarith [ht.out])
    · have h0 : 0 ≤ t0 := by
        by_contra h; exact hn0 (Nat.floor_eq_zero.2 (by linarith))
      have hnt : (n : ℝ) ≤ t0 := Nat.floor_le h0
      rcases hnt.lt_or_eq with hnt | hnt
      · refine (haff n).continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ self_mem_Iic
        filter_upwards [Icc_mem_nhdsLE hnt] with t ht
        exact brokenLine_eq u (Or.inl ht.1) (by linarith [ht.2])
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        have hmn : (m : ℝ) + 1 = n := by rw [hm]; push_cast; ring
        refine (haff m).continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ self_mem_Iic
        filter_upwards [Icc_mem_nhdsLE (show (m : ℝ) < t0 by linarith)] with t ht
        exact brokenLine_eq u (Or.inl ht.1) (by linarith [ht.2])
  · refine (haff n).continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ self_mem_Ici
    filter_upwards [Icc_mem_nhdsGE hlt] with t ht
    refine brokenLine_eq u ?_ ht.2
    by_cases h0 : 0 ≤ t0
    · exact Or.inl ((Nat.floor_le h0).trans ht.1)
    · exact Or.inr (Nat.floor_eq_zero.2 (by linarith))

/-- **l.1601, second half** (`« Since Σ₀ is complete, by Lemma lem:surface_complete
lim τ₀ = +∞ »`), with `Σ`'s completeness the Lipschitz one of `Causal.Flat.IsCauchyComplete`. -/
theorem trace_tendsto_atTop_of_complete {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hR : 0 < R) (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2))
    (hcomp : CompleteSpace (Causal.Flat.InducedLengthSpace 2 Sig))
    (htop : Continuous fun x : Causal.Flat.InducedLengthSpace 2 Sig =>
      (Causal.Flat.InducedLengthSpace.toSubtype x : N)) :
    Tendsto (traceFun τS) (comap Prod.fst (𝓝[>] 0)) atTop := by
  set R'' := R / 2 with hR''def
  have hR'' : 0 < R'' := half_pos hR
  have hR''R : R'' < R := half_lt_self hR
  set g := traceFun τS with hg
  obtain ⟨Φ, hΦc, hΦeq, hΦlen⟩ := exists_traceSig hW hsub hψ hc hpos hgraph hR''R
  have hU : UnifSpacelike g R'' :=
    unifSpacelike_of_graphDevOn (Ω := openStrip R) (fun p hp => ⟨hp.1, hp.2.trans_lt hR''R⟩)
      (trace_spacelikeDevelopment_openStrip hW hsub hψ hSig hc hpos hgraph)
  have hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ) := traceFun_periodic τS
  rw [tendsto_atTop]
  intro A
  by_contra hA
  rw [Filter.not_eventually] at hA
  -- the sequence of `lem_surface_complete_two_unif` (l.828–834), over `(0, R″] × ℝ`
  have hfreq : ∀ ε : ℝ, ∃ p : ℝ × ℝ, 0 < ε → 0 < p.1 ∧ p.1 < ε ∧ g p < A := by
    intro ε
    by_cases hε : 0 < ε
    · have hmem : {p : ℝ × ℝ | p.1 ∈ Ioo 0 ε} ∈ comap Prod.fst (𝓝[>] (0 : ℝ)) :=
        preimage_mem_comap (Ioo_mem_nhdsGT hε)
      obtain ⟨p, hp1, hp2⟩ := (hA.and_eventually hmem).exists
      exact ⟨p, fun _ => ⟨hp2.1, hp2.2, not_le.1 hp1⟩⟩
    · exact ⟨0, fun h => absurd h hε⟩
  choose P hP using hfreq
  set step : ℝ × ℝ → ℝ × ℝ := fun q =>
    ((P (q.1 / 2)).1, q.2 + toIcoMod Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2)) with hstep
  set u : ℕ → ℝ × ℝ := fun n => step^[n] (P R'') with hu
  have husucc : ∀ n, u (n + 1) = step (u n) := fun n => Function.iterate_succ_apply' _ _ _
  have hstep_g : ∀ q : ℝ × ℝ, g (step q) = g (P (q.1 / 2)) := by
    intro q
    have e : q.2 + toIcoMod Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2) =
        (P (q.1 / 2)).2 + ((-toIcoDiv Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2) : ℤ) : ℝ) *
          (2 * π) := by
      rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]; push_cast; ring
    simp only [hstep]
    rw [e, periodic_int hper]
  have hstep_θ : ∀ q : ℝ × ℝ, |(step q).2 - q.2| ≤ π := by
    intro q
    have h := toIcoMod_mem_Ico Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2)
    simp only [hstep, add_sub_cancel_left]
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hinv : ∀ n, 0 < (u n).1 ∧ (u n).1 < R'' ∧ g (u n) < A := by
    intro n
    induction n with
    | zero => exact hP R'' hR''
    | succ n ih =>
      rw [husucc]
      obtain ⟨h1, h2, h3⟩ := hP ((u n).1 / 2) (half_pos ih.1)
      refine ⟨h1, by linarith [ih.2.1], ?_⟩
      rw [hstep_g]; exact h3
  have hhalf : ∀ n, (u (n + 1)).1 < (u n).1 / 2 := by
    intro n; rw [husucc]; exact (hP ((u n).1 / 2) (half_pos (hinv n).1)).2.1
  set w : ℕ → Strip R'' := fun n => ⟨u n, (hinv n).1, (hinv n).2.1.le⟩ with hw
  set T : ℕ → ℝ := fun n => (1 + 2 * π ^ 2) * ((u n).1 - (u (n + 1)).1) - (g (u n) - g (u (n + 1)))
    with hT
  have hseg : ∀ n, 0 ≤ T n ∧
      Causal.Flat.pathLength (fun (_ : Strip R'') z => graphDev g R'' z)
        (stripSegment (w (n + 1)) (w n)) ≤ ENNReal.ofReal (T n) := by
    intro n
    exact pathLength_seg_unif hU (w (n + 1)) (w n)
      (by show (u n).1 / 2 ≤ (u n).1 - (u (n + 1)).1; linarith [hhalf n])
      (by show |(u n).2 - (u (n + 1)).2| ≤ π; rw [husucc, abs_sub_comm]; exact hstep_θ (u n))
  -- the broken line has finite length (l.842–846, telescoping)
  have hsum : Summable T := by
    refine summable_of_sum_range_le (c := (1 + 2 * π ^ 2) * R'' - g (u 0) + A)
      (fun n => (hseg n).1) fun N => ?_
    have e : ∑ i ∈ Finset.range N, T i =
        ((1 + 2 * π ^ 2) * (u 0).1 - g (u 0)) - ((1 + 2 * π ^ 2) * (u N).1 - g (u N)) := by
      rw [← Finset.sum_range_sub' (fun i => (1 + 2 * π ^ 2) * (u i).1 - g (u i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hT]; ring
    rw [e]
    have := hinv N
    have h0 := hinv 0
    have hpi : 0 ≤ 1 + 2 * π ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h0.2.1.le hpi,
      mul_pos (by positivity : (0:ℝ) < 1 + 2 * π ^ 2) this.1]
  -- its image in `Σ`, in the induced length
  set P' : Strip R'' → Causal.Flat.InducedLengthSpace 2 Sig := fun q =>
    Causal.Flat.InducedLengthSpace.toSubtype.symm (Φ q) with hP'
  have hptL : ∀ {a b : Strip R''} (γ : Path a b) (s : unitInterval), edist (P' a) (P' (γ s)) ≤
      Causal.Flat.pathLength (fun (_ : Strip R'') z => graphDev g R'' z) γ := by
    intro a b γ s
    have h := Causal.Flat.LocalLengthSpace.edist_le_pathLength (Causal.Flat.chartSys 2 Sig)
      (γ.map hΦc) s
    rw [hΦlen] at h
    exact h
  have hcs : CauchySeq fun n => P' (w n) := by
    refine cauchySeq_of_edist_le_of_tsum_ne_top (fun n => ENNReal.ofReal (T n)) (fun n => ?_) ?_
    · rw [edist_comm]
      have h := hptL (stripSegment (w (n + 1)) (w n)) 1
      rw [Path.target] at h
      exact h.trans (hseg n).2
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hseg n).1) hsum]
      exact ENNReal.ofReal_ne_top
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  -- the broken line through the `u n`, and its convergence in `Σ`
  set c := brokenLine u with hc'
  have hcmem : ∀ t, 0 ≤ t → 0 < (c t).1 ∧ (c t).1 ≤ (u ⌊t⌋₊).1 := by
    intro t ht
    have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
    have h2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have e : (c t).1 = (u ⌊t⌋₊).1 + (t - ⌊t⌋₊) * ((u (⌊t⌋₊ + 1)).1 - (u ⌊t⌋₊).1) := by
      simp [hc', brokenLine]
    have := hinv ⌊t⌋₊
    have := hinv (⌊t⌋₊ + 1)
    have := hhalf ⌊t⌋₊
    rw [e]; constructor <;> nlinarith
  have hcR : ∀ t, 0 ≤ t → c t ∈ stripSet R'' := fun t ht =>
    ⟨(hcmem t ht).1, (hcmem t ht).2.trans (hinv _).2.1.le⟩
  set qc : ℝ → Strip R'' := fun t => ⟨c (max t 0), hcR _ (le_max_right t 0)⟩ with hqc
  set F : ℝ → ℕ := fun t => ⌊max t 0⌋₊ with hF'
  have hF : Tendsto F atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_atTop_mono (fun t => le_max_left t 0) tendsto_id)
  have hbound : ∀ t, edist (P' (qc t)) a ≤
      ENNReal.ofReal (T (F t)) + edist (P' (w (F t + 1))) a := by
    intro t
    have ht' : 0 ≤ max t 0 := le_max_right t 0
    have h1 : (F t : ℝ) ≤ max t 0 := Nat.floor_le ht'
    have h2 : max t 0 < F t + 1 := Nat.lt_floor_add_one _
    set s : unitInterval := ⟨F t + 1 - max t 0, by linarith, by linarith⟩ with hs
    have hq : stripSegment (w (F t + 1)) (w (F t)) s = qc t := by
      apply Subtype.ext
      show u (F t + 1) + ((F t : ℝ) + 1 - max t 0) • (u (F t) - u (F t + 1)) = c (max t 0)
      simp only [hc', brokenLine, hF']
      module
    calc edist (P' (qc t)) a ≤ edist (P' (qc t)) (P' (w (F t + 1))) +
          edist (P' (w (F t + 1))) a := edist_triangle _ _ _
      _ ≤ _ := by
        gcongr
        rw [edist_comm, ← hq]
        exact (hptL _ s).trans (hseg (F t)).2
  have hP'lim : Tendsto (fun t => P' (qc t)) atTop (𝓝 a) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hT0 : Tendsto (fun n => ENNReal.ofReal (T n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal hsum.tendsto_atTop_zero
    have hw0 : Tendsto (fun n => edist (P' (w (n + 1))) a) atTop (𝓝 0) :=
      (tendsto_iff_edist_tendsto_0.1 ha).comp (tendsto_add_atTop_nat 1)
    have hB : Tendsto (fun n => ENNReal.ofReal (T n) + edist (P' (w (n + 1))) a) atTop
        (𝓝 0) := by
      simpa using hT0.add hw0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hB.comp hF)
      (fun t => zero_le) hbound
  set aN : N := (Causal.Flat.InducedLengthSpace.toSubtype a : N) with haN
  have hN : Tendsto (fun s : ℝ => (show N from ψ (paperInY (tracePt τS (c (max s⁻¹ 0))))))
      (𝓝[>] 0) (𝓝 aN) := by
    have h := ((htop.tendsto a).comp hP'lim).comp tendsto_inv_nhdsGT_zero
    refine h.congr fun s => ?_
    exact hΦeq (qc s⁻¹)
  -- the broken line meets the hypotheses of `flat_curve_noLimit`: contradiction
  have hcR' : ∀ s : ℝ, c (max s⁻¹ 0) ∈ stripSet R := fun s =>
    ⟨(hcR _ (le_max_right _ _)).1, (hcR _ (le_max_right _ _)).2.trans hR''R.le⟩
  have hgeom : ∀ n, (u n).1 ≤ R'' * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using (hinv 0).2.1.le
    | succ n ih => rw [pow_succ]; nlinarith [hhalf n]
  have hto0 : Tendsto (fun n => R'' * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul R''
  refine E0AxisNoLimit.flat_curve_noLimit (γ := fun s => tracePt τS (c (max s⁻¹ 0))) hR hW hsub
    hψ one_pos ?_ (fun s _ => ?_) (fun s _ => (tracePt_mem hpos (hcR' s)).1.le) ?_
    (show FlatE0 N from aN) hN
  · have hinvc : ContinuousOn (fun s : ℝ => s⁻¹) (Ioo 0 1) :=
      continuousOn_inv₀.mono fun s hs => by simpa using hs.1.ne'
    exact (continuousOn_tracePt hc).comp ((continuous_brokenLine u).comp_continuousOn
      ((continuous_id.max continuous_const).comp_continuousOn hinvc)) fun s _ => hcR' s
  · rw [(tracePt_mem hpos (hcR' s)).2]; exact (hcR _ (le_max_right _ _)).1
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hto0.comp (hF.comp tendsto_inv_nhdsGT_zero)) (fun s => norm_nonneg _) fun s => ?_
    show rad (tracePt τS (c (max s⁻¹ 0))) ≤ R'' * (1 / 2) ^ F s⁻¹
    rw [(tracePt_mem hpos (hcR' s)).2]
    exact (hcmem _ (le_max_right _ _)).2.trans (hgeom _)

/-- **The target's form** (T-btz-trace-complete): `trace_tendsto_atTop` with `hcomp` replaced by
the last two fields of `Causal.Flat.IsCauchyComplete` for `Σ`. -/
theorem trace_tendsto_atTop_of_isCauchyComplete {v R R'' : ℝ} {W : Set E0Y}
    {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2))
    (hR'' : 0 < R'') (hR''R : R'' < R)
    (hcomp : CompleteSpace (Causal.Flat.InducedLengthSpace 2 Sig))
    (htop : Continuous fun x : Causal.Flat.InducedLengthSpace 2 Sig =>
      (Causal.Flat.InducedLengthSpace.toSubtype x : N)) :
    Tendsto (traceFun τS) (comap Prod.fst (𝓝[>] 0)) atTop :=
  trace_tendsto_atTop_of_complete (hR''.trans hR''R) hW hsub hψ hSig hc hpos hgraph hcomp htop

end E0TraceComplete

end GX
