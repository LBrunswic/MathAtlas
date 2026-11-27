import GXScaffold.BTZ.RegCompleteCauchy
import GXScaffold.BTZ.RegCompleteTail

/-!
# `GXScaffold.BTZ.RegCompleteLength` — `Σ*` of a locally finite spear family: spacelike Lipschitz, Lemma 2.8's `log r` estimate, and completeness (btz § 5.4)

Targets T-btz-reg-complete-length and T-btz-reg-complete-tail. Paper `btz`
(`papers/btz/legacy/labeled/BTZ_1.tex`). Row (unmarked, partial: `𝔼₀`-scoped and the readings
below; this file is step (3) of `btzprop:reg_complete`'s Cauchy-completeness, and
`GX.E0RegComplete.regM_isCauchyComplete_of_complete` in `GXScaffold/BTZ/RegComplete.lean` is
`regM_isCauchyComplete_of_lf`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576: « the proof of
  Cauchy-completeness of Proposition prop:abs_max applies as is » (l.1571), which is B21 l.1093.

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

> Global hyperbolicity follows from Remark \ref{rem:reg_GH} and the proof of Cauchy-complete\-ness
> of Proposition \ref{prop:abs_max} applies as is. (l.1571)

## What is proved (no `sorry`; standard axioms only)

* `LFSurgeryData.isSpacelikeLipschitz_sigmaStar` (G4): `Σ*` of a locally finite family is
  spacelike Lipschitz in the flat charts of `Reg M`, from `S` spacelike Lipschitz only. The strict
  `SurgeryData.isSpacelikeLipschitzAt_cusp_interior` / `_rim` proofs, verbatim: their one use of
  finiteness (the union of the other spears is closed) is local finiteness, and of the compact
  `IsE0C1SpacelikeCauchy` they use only `reg`.
* `LFSurgeryData.ofReal_abs_logRad_sub_le_edist`: Lemma 2.8's `log r` estimate (B21 l.799–806) on
  `Σ*`, spear by spear — the clamped log-radius of each cusp is `1`-Lipschitz for the induced
  length (the strict proof, verbatim; it uses one spear).
* `LFSurgeryData.tendsto_of_cauchySeq_of_isCompact`: a Cauchy sequence of `Σ*` whose tail lies in
  a compact set of `M` converges (the strict compact proof localised to the finitely many spears
  the compact set meets).
* `LFSurgeryData.exists_summable`: the spears can be thinned to summable radii.
* `LFSurgeryData.exists_isCompact_of_cauchySeq`: the tail of a Cauchy sequence of `Σ*` lies in a
  compact set of `M`, for spears of summable radii (`GXScaffold.BTZ.RegCompleteTail`'s
  `exists_isCompact_of_cauchySeq_of`, the rim-arc surgery, with this file's compact case and
  `log r` estimate).
* `LFSurgeryData.completeSpace_sigmaStar` (G5) and `regM_isCauchyComplete_of_lf`: `Σ*` is complete
  and `Reg M` is Cauchy-complete (`Causal.Flat.IsCauchyComplete 2`).

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifold | ⚠ `𝔼₀` only (T-btz-scope): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid`, T2, connected, second countable |
| globally hyperbolic | ✓ `(CE M).GloballyHyperbolic` |
| Cauchy-maximal | ✓ `E0Spear.IsE0CauchyMaximal M` (for the spear data, step (1)) |
| Cauchy-complete | ⚠ read `E0RegComplete.IsE0C1CompleteCauchy M S` (OQ-142); G4 uses only `reg`, the compact part only that `S` is a closed Cauchy surface, the tail (`exists_isCompact_of_cauchySeq`) `complete` and `continuous` |
| conclusion: Cauchy-complete | ⚠ read `Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M)` (DEC-31/35) |

## SCOPE (disclosed)

No `sorry`. The paper prints nothing for the infinitely many spears (l.1571, « applies as is »:
B21's proof of `prop:abs_max` has finitely many spears and a compact `S`); the tail is proved in
`GXScaffold.BTZ.RegCompleteTail` by thinning the spears to summable radii and replacing, spear by
spear, each excursion of a path of `Σ*` into a cusp by a rim arc of length `≤ π R`.
`btzprop:reg_complete` stays partial: `𝔼₀`-scoped, and the readings above.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0SpearFamily

open E0 E0Spear E0Surgery

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-! ### (G4) `Σ*` is spacelike Lipschitz in the flat charts of `Reg M`

The strict `E0Surgery.SurgeryData.isSpacelikeLipschitzAt_cusp_interior` and `_rim`, verbatim, over
a locally finite family: the one use of finiteness (the union of the other spears is closed) is
local finiteness, and of the compact surface `IsE0C1SpacelikeCauchy` only its field `reg` is used. -/

omit [SecondCountableTopology M] in
open scoped Pointwise in
/-- **(G4a), interior case**: at a point `ψ(x)` of a cusp with `r(x) < R`, `Σ*` is spacelike
Lipschitz. Near `ψ(x)` the flat chart of `Reg M` is `g • chartMap x ∘ ψ⁻¹`
(`SpearSurgeryDatum.eventually_regChart`), `Σ*` is the cusp, and its chart picture is the zero
set of the height `chartHeight G g`, `C¹` with derivative positive on the future causal cone at
the point (Lemma 2.7, `fderiv_chartHeight_pos`), hence cone-increasing on a ball
(`exists_ball_isConeIncreasingOn`). -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp_interior {S : Set M} (Dat : LFSurgeryData M S)
    (i : Dat.ι) {y : e0RegMFlat M} {x : E0} (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R)
    (hxR : rad x < (Dat.D i).R) (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  set D := Dat.D i with hD
  set y' : E0LM.e0RegM M := y
  have hrx : 0 < rad x := hx.1
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
  have hxsp : x ∈ E0Spear.spear D.v D.R := D.graphSet_subset_spear hx
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_regChart hx0 hxW y' hy
  have hper := D.spacelike.periodic
  -- `x` is in the open interior of the spear
  have hfx : D.v < fcoord x := by
    have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
      have := hx.2.2; simp only [height, heightAt] at this; linarith
    have h2 := D.above (rad x, Complex.arg x.2) hrx hx.2.1
    simp only [fcoord]; rw [h1]; linarith
  have hOx : ∀ᶠ w in 𝓝 x, (D.ψ (paperInY w) ∈ (E0LM.regChartM y').source ∧
      E0LM.regChartM y' (D.ψ (paperInY w)) = g • E0.chartMap x w) ∧
      D.v < fcoord w ∧ 0 < rad w ∧ rad w < D.R := by
    have hfc : Continuous fcoord := continuous_fst.sub (continuous_rad.div_const 2)
    exact hg.and ((hfc.continuousAt.eventually (lt_mem_nhds hfx)).and
      ((continuous_rad.continuousAt.eventually (lt_mem_nhds hrx)).and
        (continuous_rad.continuousAt.eventually (gt_mem_nhds hxR))))
  -- the chart picture
  set e := chartAt (Causal.Minkowski 2) y with he
  set F := chartHeight D.G g with hF
  set U := {p : Causal.Minkowski 2 | 0 < (chartNull g p).2.1} with hU
  set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
  have hlocx : locLift x x = btzPaperNull pp := rfl
  have hp₀ : e y = g • nullToMink (btzPaperNull pp) := by
    rw [regChart_apply_eq, hy, (hg.self_of_nhds).2, E0.chartMap, hlocx]
  have hQ₀ : chartNull g (e y) = btzPaperNull pp := by rw [hp₀]; simp [chartNull]
  have hp₀U : e y ∈ U := by
    show 0 < (chartNull g (e y)).2.1
    rw [hQ₀]; exact hrx
  have hxR' : rad x ≤ D.R := hx.2.1
  obtain ⟨L, hL, hδ⟩ := D.spacelike.deriv (rad x, angle x x) hrx hxR'
  obtain ⟨ε, hε, c, hc0, hc1, hballU, hinc⟩ := exists_ball_isConeIncreasingOn (isOpen_chartPos g)
    (contDiffOn_chartHeight hper D.smooth g) hp₀U (by
      intro v hv0 hv
      rw [hp₀]
      exact fderiv_chartHeight_pos hper D.smooth g hrx hL hδ hv0 hv)
  -- the eventual facts at `e y`
  set Φ : Causal.Minkowski 2 → E0 := fun p => unlift (chartNull g p) with hΦ
  have hΦc : ContinuousAt Φ (e y) :=
    (continuousAt_unlift (by rw [hQ₀]; exact hrx.ne')).comp (contDiff_chartNull g).continuous.continuousAt
  have hΦ₀ : Φ (e y) = x := by
    simp only [Φ, hQ₀, ← hlocx]
    have := unlift_symm_chartMap hx0 x
    rwa [E0.chartMap, LinearEquiv.symm_apply_apply] at this
  have hImg : ∀ᶠ p in 𝓝 (e y), chartNull g p ∈ Img x := by
    have h0 : chartNull g (e y) ∈ Img x := by rw [hQ₀, ← hlocx]; exact locLift_mem_Img (mem_sector_self hx0)
    have hθc : ContinuousAt (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) (chartNull g (e y)) :=
      ((continuous_snd.comp continuous_snd).continuousAt.div
        (continuous_fst.comp continuous_snd).continuousAt (by rw [hQ₀]; exact hrx.ne')).neg
    have hev : ∀ᶠ Q in 𝓝 (chartNull g (e y)), Q ∈ Img x := by
      have h1 : ∀ᶠ Q in 𝓝 (chartNull g (e y)), 0 < Q.2.1 :=
        isOpen_nullPos.mem_nhds h0.1
      have h2 : ∀ᶠ Q in 𝓝 (chartNull g (e y)), |-(Q.2.2 / Q.2.1) - Complex.arg x.2| < π :=
        (hθc.sub continuousAt_const).abs.eventually (gt_mem_nhds h0.2)
      filter_upwards [h1, h2] with Q h1 h2 using ⟨h1, h2⟩
    exact (contDiff_chartNull g).continuous.continuousAt.eventually hev
  have hT : Tendsto Φ (𝓝 (e y)) (𝓝 x) := hΦ₀ ▸ hΦc.tendsto
  have hΦO := hT.eventually hOx
  have htgt : ∀ᶠ p in 𝓝 (e y), p ∈ e.target := e.open_target.mem_nhds (e.map_source (mem_chart_source _ y))
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff_ball.1 ((hImg.and hΦO).and htgt)
  set W := Metric.ball (e y) (min ε ε') with hW
  have hWε : W ⊆ Metric.ball (e y) ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWε' : W ⊆ Metric.ball (e y) ε' := Metric.ball_subset_ball (min_le_right _ _)
  have hycusp : regVal M y ∈ D.cusp := by rw [hy]; exact ⟨paperInY x, ⟨x, hx, rfl⟩, rfl⟩
  have hyT : y ∈ Dat.sigmaStarReg :=
    show regVal M y ∈ Dat.sigmaStar from Or.inr (mem_iUnion.2 ⟨i, hycusp⟩)
  refine isSpacelikeLipschitzAt_of_coneZeroSet (g := 1) Metric.isOpen_ball
    (Metric.mem_ball_self (lt_min hε hε')) (fun p hp => (hball' p (hWε' hp)).2)
    ((contDiffOn_chartHeight hper D.smooth g).continuousOn.mono fun p hp => hballU (hWε hp))
    hc0 hc1 (by rw [one_smul]; simpa using hinc.mono le_rfl hWε) ?_ hyT
  -- the zero set
  intro p hp
  obtain ⟨⟨hpImg, ⟨hsrc, hchart⟩, hfw, hrw, hrwR⟩, -⟩ := hball' p (hWε' hp)
  set w := Φ p with hw
  have hwsp : w ∈ E0Spear.spear D.v D.R := ⟨hfw.le, hrwR.le⟩
  have hreg : D.ψ (paperInY w) ∈ E0LM.e0RegM M := fun hS0 => by
    have := (D.mem_S0_iff hwsp).1 hS0; linarith
  set z₀ : e0RegMFlat M := (⟨D.ψ (paperInY w), hreg⟩ : E0LM.e0RegM M)
  have hz₀src : z₀ ∈ e.source := (mem_regChart_source_iff y z₀).2 hsrc
  have hez₀ : e z₀ = p := by
    rw [regChart_apply_eq]
    show E0LM.regChartM y' (D.ψ (paperInY w)) = p
    rw [hchart, E0.chartMap, locLift_unlift hx0 hpImg, chartNull, LinearEquiv.apply_symm_apply,
      smul_inv_smul]
  have hFp : chartHeight D.G g p = height D.G w := rfl
  have hspear : D.ψ (paperInY w) ∈ D.spearSet := ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
  constructor
  · rintro ⟨z, ⟨hzT, hzs⟩, hzp⟩
    have hzz : z = z₀ := e.injOn hzs hz₀src (hzp.trans hez₀.symm)
    rw [hzz] at hzT
    have hc : D.ψ (paperInY w) ∈ D.cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hzT, hspear⟩
    obtain ⟨_, ⟨x', hx', rfl⟩, hx'e⟩ := hc
    have hx'sp := D.graphSet_subset_spear hx'
    have hpw : paperInY x' = paperInY w :=
      D.inj (D.spear_sub ⟨x', hx'sp, rfl⟩) (D.spear_sub ⟨w, hwsp, rfl⟩) hx'e
    have : x' = w := paperInY.injOn (by simp) (by simp) hpw
    rw [hFp, ← this]; exact hx'.2.2
  · intro h0
    have hwg : w ∈ graphSet D.G D.R := ⟨hrw, hrwR.le, by rw [← hFp]; exact h0⟩
    have hT : z₀ ∈ Dat.sigmaStarReg :=
      show D.ψ (paperInY w) ∈ Dat.sigmaStar from
        Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, hwg, rfl⟩, rfl⟩⟩)
    exact ⟨z₀, ⟨hT, hz₀src⟩, hez₀⟩

omit [SecondCountableTopology M] in
open scoped Pointwise in
set_option maxHeartbeats 1000000 in
/-- **(G4a), rim case**: at a point `ψ(x)` of a cusp with `r(x) = R`, `Σ*` is spacelike Lipschitz.
In the frame `g₁` in which `S` is locally the graph of a `c₁`-Lipschitz `u` (`hSreg`), `Σ*` is
the zero set of the function equal to the cusp height `chartHeight G (g₁ g)` on `{r ≤ R}` and to
the null-shift height `σ` of `S` along the developed `∂_τ` on `{r > R}` (`exists_nullShift`). The
two agree on the cylinder `r = R` (the rim `C = C*`: shifting along `∂_τ` stays on the cylinder,
where the cusp and `S` meet `τ`-lines at the same point), so the function is continuous; each is
cone-increasing, and across the cylinder a segment is cut at a crossing point (intermediate value
theorem), so the glued function is cone-increasing. -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp_rim {S : Set M} (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M} {x : E0}
    (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R) (hxR : rad x = (Dat.D i).R)
    (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  classical
  set D := Dat.D i with hD
  set y' : E0LM.e0RegM M := y
  have hrx : 0 < rad x := hx.1
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
  have hxsp : x ∈ E0Spear.spear D.v D.R := D.graphSet_subset_spear hx
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_regChart hx0 hxW y' hy
  have hper := D.spacelike.periodic
  have hx1 : x.1 = D.G (rad x, Complex.arg x.2) := by
    have := hx.2.2; simp only [height, heightAt] at this; linarith
  have hfx : D.v < fcoord x := by
    have h2 := D.above (rad x, Complex.arg x.2) hrx hx.2.1
    simp only [fcoord]; rw [hx1]; linarith
  have hxS : D.ψ (paperInY x) ∈ S := (D.graph x hxsp).2 (by rw [hx1, rim_value D.rim hxR])
  have hyS : y ∈ regSet M S := show regVal M y ∈ S by rw [hy]; exact hxS
  set e := chartAt (Causal.Minkowski 2) y with he
  obtain ⟨V, hpV, hVt, hVL⟩ := hSreg y hyS
  set Sc := e '' (regSet M S ∩ e.source) ∩ (V : Set (Causal.Minkowski 2)) with hSc
  have hySc : e y ∈ Sc := ⟨⟨y, ⟨hyS, mem_chart_source _ y⟩, rfl⟩, hpV⟩
  obtain ⟨g₁, O, U', u, c₁, hc₁, hpO, hOV, hU', hu, hgr⟩ := hVL.locGraph (e y) hySc
  -- the frame `g₁` and the null direction
  set g' := g₁ * g with hg'
  set L₁ := (g₁ : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear
  set n := (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear tauDir with hn
  obtain ⟨hnc, hn0, -, -⟩ := lorentz_apply_pos g.2 isFutureCausal_tauDir tauDir_ne_zero
  set m := L₁ n with hmdef
  obtain ⟨-, -, hm, hmn⟩ := lorentz_apply_pos g₁.2 hnc hn0
  set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
  have hlocx : locLift x x = btzPaperNull pp := rfl
  have hp₀ : e y = g • nullToMink (btzPaperNull pp) := by
    rw [regChart_apply_eq, hy, (hg.self_of_nhds).2, E0.chartMap, hlocx]
  set q₀ := g₁ • e y with hq₀def
  have hq₀ : q₀ = g' • nullToMink (btzPaperNull pp) := by rw [hq₀def, hp₀, hg', mul_smul]
  have hq₀gr : q₀ ∈ Causal.Flat.graphOver U' u := by
    have : q₀ ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := Set.smul_mem_smul_set ⟨hySc, hpO⟩
    rw [hgr] at this; exact this.2
  obtain ⟨δ₁, hδ₁, σ, hσ0, hσ⟩ := exists_nullShift hU' hc₁ hu hm hmn hq₀gr.1 hq₀gr.2
  -- the cusp height in the frame
  have hQ₀ : chartNull g' q₀ = btzPaperNull pp := by rw [hq₀]; simp [chartNull]
  have hq₀U : q₀ ∈ {q : Causal.Minkowski 2 | 0 < (chartNull g' q).2.1} := by
    show 0 < (chartNull g' q₀).2.1; rw [hQ₀]; exact hrx
  obtain ⟨L, hL, hδ⟩ := D.spacelike.deriv (rad x, angle x x) hrx hxR.le
  obtain ⟨ε, hε, cI, hcI0, hcI1, hballU, hincI⟩ := exists_ball_isConeIncreasingOn (isOpen_chartPos g')
    (contDiffOn_chartHeight hper D.smooth g') hq₀U (by
      intro v hv0 hv
      rw [hq₀]
      exact fderiv_chartHeight_pos hper D.smooth g' hrx hL hδ hv0 hv)
  set FI := chartHeight D.G g' with hFI
  have hFIc : ContinuousOn FI (Metric.ball q₀ ε) :=
    (contDiffOn_chartHeight hper D.smooth g').continuousOn.mono hballU
  set Φ : Causal.Minkowski 2 → E0 := fun q => unlift (chartNull g' q) with hΦ
  have hΦc : ContinuousOn Φ (Metric.ball q₀ ε) := fun q hq =>
    ((continuousAt_unlift (ne_of_gt (hballU hq))).comp
      (contDiff_chartNull g').continuous.continuousAt).continuousWithinAt
  have hΦ₀ : Φ q₀ = x := by
    simp only [Φ, hQ₀, ← hlocx]
    have := unlift_symm_chartMap hx0 x
    rwa [E0.chartMap, LinearEquiv.symm_apply_apply] at this
  have hFI₀ : FI q₀ = 0 := by
    show height D.G (Φ q₀) = 0
    rw [hΦ₀]; exact hx.2.2
  -- the other spears
  set Oth : Set M := ⋃ j : {j : Dat.ι // j ≠ i}, (Dat.D j).spearSet with hOth
  have hOthc : IsClosed Oth := by
    exact (Dat.locallyFinite.comp_injective Subtype.val_injective).isClosed_iUnion
      fun j => Dat.isClosed j
  have hxOth : D.ψ (paperInY x) ∉ Oth := by
    rintro hm'
    obtain ⟨⟨j, hj⟩, hjm⟩ := mem_iUnion.1 hm'
    exact Set.disjoint_left.1 (Dat.disjoint hj) hjm ⟨paperInY x, ⟨x, hxsp, rfl⟩, rfl⟩
  have hψc : ContinuousAt (fun w : E0 => D.ψ (paperInY w)) x := by
    have hψq : ContinuousAt D.ψ (paperInY x) :=
      ((D.mor _ hxW).1).continuousAt (D.isOpen.mem_nhds hxW)
    exact ContinuousAt.comp (g := D.ψ) (f := fun w : E0 => paperInY w) hψq
      (paperInY.continuousAt (by rw [paperInY_source]; trivial))
  have hOx : ∀ᶠ w in 𝓝 x, (D.ψ (paperInY w) ∈ (E0LM.regChartM y').source ∧
      E0LM.regChartM y' (D.ψ (paperInY w)) = g • E0.chartMap x w) ∧
      D.v < fcoord w ∧ 0 < rad w ∧ paperInY w ∈ D.W ∧ D.ψ (paperInY w) ∉ Oth := by
    have hfc : Continuous fcoord := continuous_fst.sub (continuous_rad.div_const 2)
    refine hg.and ((hfc.continuousAt.eventually (lt_mem_nhds hfx)).and
      ((continuous_rad.continuousAt.eventually (lt_mem_nhds hrx)).and
        ((show ∀ᶠ w in 𝓝 x, paperInY w ∈ D.W from
          (paperInY.continuousAt (by rw [paperInY_source]; trivial)).preimage_mem_nhds
            (D.isOpen.mem_nhds hxW)).and
          (show ∀ᶠ w in 𝓝 x, D.ψ (paperInY w) ∉ Oth from
            hψc.preimage_mem_nhds (hOthc.isOpen_compl.mem_nhds hxOth)))))
  -- the eventual facts at `q₀`
  have hq₀ε : Metric.ball q₀ ε ∈ 𝓝 q₀ := Metric.ball_mem_nhds _ hε
  have hΦca : ContinuousAt Φ q₀ := hΦc.continuousAt hq₀ε
  have hFIca : ContinuousAt FI q₀ := hFIc.continuousAt hq₀ε
  have hImg : ∀ᶠ q in 𝓝 q₀, chartNull g' q ∈ Img x := by
    have h0 : chartNull g' q₀ ∈ Img x := by
      rw [hQ₀, ← hlocx]; exact locLift_mem_Img (mem_sector_self hx0)
    have hθc : ContinuousAt (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) (chartNull g' q₀) :=
      ((continuous_snd.comp continuous_snd).continuousAt.div
        (continuous_fst.comp continuous_snd).continuousAt (by rw [hQ₀]; exact hrx.ne')).neg
    have hev : ∀ᶠ Q in 𝓝 (chartNull g' q₀), Q ∈ Img x := by
      have h1 : ∀ᶠ Q in 𝓝 (chartNull g' q₀), 0 < Q.2.1 := isOpen_nullPos.mem_nhds h0.1
      have h2 : ∀ᶠ Q in 𝓝 (chartNull g' q₀), |-(Q.2.2 / Q.2.1) - Complex.arg x.2| < π :=
        (hθc.sub continuousAt_const).abs.eventually (gt_mem_nhds h0.2)
      filter_upwards [h1, h2] with Q h1 h2 using ⟨h1, h2⟩
    exact (contDiff_chartNull g').continuous.continuousAt.eventually hev
  have hT : Tendsto Φ (𝓝 q₀) (𝓝 x) := hΦ₀ ▸ hΦca.tendsto
  have hΦO := hT.eventually hOx
  set Φ' : Causal.Minkowski 2 → E0 := fun q => ((Φ q).1 - FI q, (Φ q).2) with hΦ'
  have hT' : Tendsto Φ' (𝓝 q₀) (𝓝 x) := by
    have h : ContinuousAt Φ' q₀ :=
      ((continuous_fst.continuousAt.comp hΦca).sub hFIca).prodMk
        (continuous_snd.continuousAt.comp hΦca)
    have h0 : Φ' q₀ = x := by simp only [Φ', hΦ₀, hFI₀, sub_zero]
    exact h0 ▸ h.tendsto
  have hΦO' := hT'.eventually hOx
  have hinvc : Continuous fun q : Causal.Minkowski 2 => g₁⁻¹ • q := continuous_const_smul _
  have hp₀' : g₁⁻¹ • q₀ = e y := by rw [hq₀def, inv_smul_smul]
  have htgt : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • q ∈ e.target := by
    refine hinvc.continuousAt.preimage_mem_nhds ?_
    rw [hp₀']; exact e.open_target.mem_nhds (e.map_source (mem_chart_source _ y))
  have hVO_open : IsOpen ((V : Set (Causal.Minkowski 2)) ∩ (O : Set (Causal.Minkowski 2))) :=
    V.isOpen.inter O.isOpen
  have hVO : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • q ∈ (V : Set (Causal.Minkowski 2)) ∩ O := by
    refine hinvc.continuousAt.preimage_mem_nhds ?_
    rw [hp₀']; exact hVO_open.mem_nhds ⟨hpV, hpO⟩
  have hVO' : ∀ᶠ q in 𝓝 q₀, g₁⁻¹ • (q - FI q • m) ∈ (V : Set (Causal.Minkowski 2)) ∩ O := by
    have hc : ContinuousAt (fun q => g₁⁻¹ • (q - FI q • m)) q₀ :=
      hinvc.continuousAt.comp (continuousAt_id.sub (hFIca.smul continuousAt_const))
    refine hc.preimage_mem_nhds ?_
    simp only [hFI₀, zero_smul, sub_zero, hp₀']
    exact hVO_open.mem_nhds ⟨hpV, hpO⟩
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff_ball.1
    ((((hImg.and hΦO).and hΦO').and htgt).and (hVO.and hVO'))
  set δ := min (min ε δ₁) ε' with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hε hδ₁) hε'
  set W' := Metric.ball q₀ δ with hW'
  have hWε : W' ⊆ Metric.ball q₀ ε :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hWδ₁ : W' ⊆ Metric.ball q₀ δ₁ :=
    Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hWε' : W' ⊆ Metric.ball q₀ ε' := Metric.ball_subset_ball (min_le_right _ _)
  have hA1 : ∀ q ∈ W', chartNull g' q ∈ Img x := fun q hq => (hball' q (hWε' hq)).1.1.1.1
  have hA2 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).1.1.1.2
  have hA3 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).1.1.2
  have hA5 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).2.1
  have hA6 := fun q (hq : q ∈ W') => (hball' q (hWε' hq)).2.2
  -- the point of `Reg M` over `q`
  have hz : ∀ q ∈ W', ∀ (hreg : D.ψ (paperInY (Φ q)) ∈ E0LM.e0RegM M),
      ((⟨D.ψ (paperInY (Φ q)), hreg⟩ : E0LM.e0RegM M) : e0RegMFlat M) ∈ e.source ∧
      e (⟨D.ψ (paperInY (Φ q)), hreg⟩ : E0LM.e0RegM M) = g₁⁻¹ • q := by
    intro q hq hreg
    have hImgq := hA1 q hq
    have hsrc := (hA2 q hq).1.1
    have hchart := (hA2 q hq).1.2
    refine ⟨(mem_regChart_source_iff y _).2 hsrc, ?_⟩
    rw [regChart_apply_eq]
    show E0LM.regChartM y' (D.ψ (paperInY (Φ q))) = _
    rw [hchart, E0.chartMap, locLift_unlift hx0 hImgq, chartNull_mul, chartNull,
      LinearEquiv.apply_symm_apply, smul_inv_smul]
  have hreg : ∀ q ∈ W', D.ψ (paperInY (Φ q)) ∈ E0LM.e0RegM M := by
    intro q hq hS0
    have hr := (hA2 q hq).2.2.1
    have hWq := (hA2 q hq).2.2.2.1
    have := (D.mem_S0_iff' hWq).1 hS0
    linarith
  -- the cylinder: `σ = FI` on `r = R`
  have hcyl : ∀ q ∈ W', rad (Φ q) = D.R → σ q = FI q := by
    intro q hq hrq
    have hImgq := hA1 q hq
    have hsrc' := (hA3 q hq).1.1
    have hchart' := (hA3 q hq).1.2
    have hf' := (hA3 q hq).2.1
    have hVO'q := hA6 q hq
    have hrw' : rad (Φ' q) = D.R := hrq
    have hw'sp : Φ' q ∈ E0Spear.spear D.v D.R := ⟨hf'.le, hrw'.le⟩
    have hw'1 : (Φ' q).1 = D.τS (Φ' q).2 := by
      show (Φ q).1 - height D.G (Φ q) = D.τS (Φ q).2
      simp only [height, heightAt]; rw [rim_value D.rim hrq]; ring
    have hw'S : D.ψ (paperInY (Φ' q)) ∈ S := (D.graph _ hw'sp).2 hw'1
    have hreg' : D.ψ (paperInY (Φ' q)) ∈ E0LM.e0RegM M := fun h => by
      have := (D.mem_S0_iff hw'sp).1 h; linarith [D.pos]
    set z' : e0RegMFlat M := (⟨_, hreg'⟩ : E0LM.e0RegM M)
    have hz'src : z' ∈ e.source := (mem_regChart_source_iff y z').2 hsrc'
    have hez'0 : g • E0.chartMap x (Φ q) = g₁⁻¹ • q := by
      rw [E0.chartMap, locLift_unlift hx0 hImgq, chartNull_mul, chartNull,
        LinearEquiv.apply_symm_apply, smul_inv_smul]
    have hez' : g₁ • e z' = q - (FI q) • m := by
      rw [regChart_apply_eq]
      show g₁ • E0LM.regChartM y' (D.ψ (paperInY (Φ' q))) = _
      rw [hchart', show Φ' q = (((Φ q).1 - (FI q), (Φ q).2) : E0) from rfl, chartMap_shift,
        isom_smul_sub_smul, hez'0, isom_smul_sub_smul, smul_inv_smul]
    have hmem : e z' ∈ Sc ∩ (O : Set (Causal.Minkowski 2)) := by
      have h := hVO'q
      rw [← hez', inv_smul_smul] at h
      exact ⟨⟨⟨z', ⟨hw'S, hz'src⟩, rfl⟩, h.1⟩, h.2⟩
    have hgm : q - (FI q) • m ∈ Causal.Flat.graphOver U' u := by
      have : g₁ • e z' ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := Set.smul_mem_smul_set hmem
      rw [hgr, hez'] at this; exact this.2
    obtain ⟨-, h1, h2⟩ := hσ q (hWδ₁ hq)
    exact nullShift_unique hc₁ hu hm hmn h1 h2 hgm.1 hgm.2
  -- the glued height
  have hA4 : ∀ q ∈ W', g₁⁻¹ • q ∈ e.target := fun q hq => (hball' q (hWε' hq)).1.2
  set F : Causal.Minkowski 2 → ℝ := fun q => if rad (Φ q) ≤ D.R then FI q else σ q with hFdef
  have hσc : ContinuousOn σ W' :=
    continuousOn_nullShift hc₁ hu hm hmn fun q hq => (hσ q (hWδ₁ hq)).2
  have hFIcW : ContinuousOn FI W' := hFIc.mono hWε
  have hrc : ContinuousOn (fun q => rad (Φ q)) W' := continuous_rad.comp_continuousOn (hΦc.mono hWε)
  have hFc : ContinuousOn F W' := by
    refine ContinuousOn.if ?_ (hFIcW.mono inter_subset_left) (hσc.mono inter_subset_left)
    rintro a ⟨ha, hfr⟩
    have hca : ContinuousAt (fun q => rad (Φ q)) a :=
      hrc.continuousAt (Metric.isOpen_ball.mem_nhds ha)
    have heq : rad (Φ a) = D.R := by
      rcases lt_trichotomy (rad (Φ a)) D.R with h | h | h
      · exfalso
        apply hfr.2
        exact mem_interior_iff_mem_nhds.2
          (mem_of_superset (hca.eventually (gt_mem_nhds h)) fun b (hb : rad (Φ b) < D.R) =>
            show b ∈ {a | rad (Φ a) ≤ D.R} from le_of_lt hb)
      · exact h
      · exfalso
        have hcl := hfr.1
        rw [mem_closure_iff_frequently] at hcl
        obtain ⟨b, hb1, hb2⟩ := (hcl.and_eventually (hca.eventually (lt_mem_nhds h))).exists
        exact absurd hb1 (not_le.2 hb2)
    exact (hcyl a ha heq).symm
  -- cone-increase
  set c : ℝ := max cI (c₁ : ℝ) with hcdef
  have hc0 : 0 ≤ c := le_max_of_le_left hcI0
  have hc1 : c < 1 := max_lt hcI1 hc₁
  have hincI' : Causal.Flat.Cla.IsConeIncreasingOn c FI W' := hincI.mono (le_max_left _ _) hWε
  have hincσ : Causal.Flat.Cla.IsConeIncreasingOn c σ W' :=
    (isConeIncreasingOn_nullShift hc₁ hu hm hmn fun q hq => (hσ q (hWδ₁ hq)).2).mono
      (le_max_right _ _) le_rfl
  have hseg : ∀ a ∈ W', ∀ b ∈ W', ∀ t ∈ Icc (0 : ℝ) 1, a + t • (b - a) ∈ W' :=
    fun a _ b _ t ht => (convex_ball q₀ δ).add_smul_sub_mem ‹_› ‹_› ht
  have hscale : ∀ a b : Causal.Minkowski 2, c * ‖b.2 - a.2‖ < b.1 - a.1 → ∀ t : ℝ, 0 < t →
      c * ‖(a + t • (b - a)).2 - a.2‖ < (a + t • (b - a)).1 - a.1 := by
    intro a b hab t ht
    have h1 : (a + t • (b - a)).2 - a.2 = t • (b.2 - a.2) := by simp
    have h2 : (a + t • (b - a)).1 - a.1 = t * (b.1 - a.1) := by simp
    rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hscale' : ∀ a b : Causal.Minkowski 2, c * ‖b.2 - a.2‖ < b.1 - a.1 → ∀ t : ℝ, t < 1 →
      c * ‖b.2 - (a + t • (b - a)).2‖ < b.1 - (a + t • (b - a)).1 := by
    intro a b hab t ht
    have h1 : b.2 - (a + t • (b - a)).2 = (1 - t) • (b.2 - a.2) := by
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, sub_smul, one_smul, smul_sub]; abel
    have h2 : b.1 - (a + t • (b - a)).1 = (1 - t) * (b.1 - a.1) := by simp; ring
    have ht' : 0 < 1 - t := by linarith
    rw [h1, h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    nlinarith
  have hcseg : ∀ a b : Causal.Minkowski 2,
      Continuous fun t : ℝ => a + t • (b - a) := fun a b => by fun_prop
  have hinc : Causal.Flat.Cla.IsConeIncreasingOn c F W' := by
    intro a ha b hb hab
    have hcont : ContinuousOn (fun t : ℝ => rad (Φ (a + t • (b - a)))) (Icc 0 1) :=
      hrc.comp (hcseg a b).continuousOn fun t ht => hseg a ha b hb t ht
    by_cases hAa : rad (Φ a) ≤ D.R <;> by_cases hAb : rad (Φ b) ≤ D.R
    · simp only [F, if_pos hAa, if_pos hAb]; exact hincI' a ha b hb hab
    · simp only [F, if_pos hAa, if_neg hAb]
      push Not at hAb
      obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hcont
        ⟨by simpa using hAa, by simpa using hAb.le⟩
      set mp := a + t • (b - a) with hmp
      have hmpW : mp ∈ W' := hseg a ha b hb t ht
      have ht1 : t < 1 := by
        rcases ht.2.lt_or_eq with h | h
        · exact h
        · exfalso; simp only [h, one_smul, add_sub_cancel] at hteq; linarith
      have h1 : FI a ≤ FI mp := by
        rcases ht.1.lt_or_eq with h0 | h0
        · exact (hincI' a ha mp hmpW (hscale a b hab t h0)).le
        · simp [hmp, ← h0]
      have h2 : σ mp < σ b := hincσ mp hmpW b hb (hscale' a b hab t ht1)
      rw [← hcyl mp hmpW hteq] at h1
      linarith
    · simp only [F, if_neg hAa, if_pos hAb]
      push Not at hAa
      obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc' zero_le_one hcont
        ⟨by simpa using hAb, by simpa using hAa.le⟩
      set mp := a + t • (b - a) with hmp
      have hmpW : mp ∈ W' := hseg a ha b hb t ht
      have ht0 : 0 < t := by
        rcases ht.1.lt_or_eq with h | h
        · exact h
        · exfalso; simp only [← h, zero_smul, add_zero] at hteq; linarith
      have h1 : σ a < σ mp := hincσ a ha mp hmpW (hscale a b hab t ht0)
      have h2 : FI mp ≤ FI b := by
        rcases ht.2.lt_or_eq with h1' | h1'
        · exact (hincI' mp hmpW b hb (hscale' a b hab t h1')).le
        · simp [hmp, h1']
      rw [hcyl mp hmpW hteq] at h1
      linarith
    · simp only [F, if_neg hAa, if_neg hAb]; exact hincσ a ha b hb hab
  -- the zero set
  have hycusp : regVal M y ∈ D.cusp := by rw [hy]; exact ⟨paperInY x, ⟨x, hx, rfl⟩, rfl⟩
  have hyT : y ∈ Dat.sigmaStarReg :=
    show regVal M y ∈ Dat.sigmaStar from Or.inr (mem_iUnion.2 ⟨i, hycusp⟩)
  refine isSpacelikeLipschitzAt_of_coneZeroSet' g₁ Metric.isOpen_ball (Metric.mem_ball_self hδ0)
    hA4 hFc hc0 hc1 hinc ?_ hyT
  intro q hq
  have hregq := hreg q hq
  obtain ⟨hsrcq, heq⟩ := hz q hq hregq
  set z₀ : e0RegMFlat M := (⟨D.ψ (paperInY (Φ q)), hregq⟩ : E0LM.e0RegM M) with hz₀
  have hlhs : g₁⁻¹ • q ∈ e '' (Dat.sigmaStarReg ∩ e.source) ↔
      D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar := by
    constructor
    · rintro ⟨z, ⟨hzT, hzs⟩, hzp⟩
      have := e.injOn hzs hsrcq (hzp.trans heq.symm)
      rw [this] at hzT; exact hzT
    · intro h; exact ⟨z₀, ⟨h, hsrcq⟩, heq⟩
  rw [hlhs]
  have hf := (hA2 q hq).2.1
  have hr := (hA2 q hq).2.2.1
  have hWq := (hA2 q hq).2.2.2.1
  have hOthq := (hA2 q hq).2.2.2.2
  by_cases hA : rad (Φ q) ≤ D.R
  · simp only [F, if_pos hA]
    have hwsp : Φ q ∈ E0Spear.spear D.v D.R := ⟨hf.le, hA⟩
    have hspear : D.ψ (paperInY (Φ q)) ∈ D.spearSet := ⟨_, ⟨_, hwsp, rfl⟩, rfl⟩
    have hFq : FI q = height D.G (Φ q) := rfl
    constructor
    · intro hT
      have hc : D.ψ (paperInY (Φ q)) ∈ D.cusp := by
        rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hT, hspear⟩
      obtain ⟨_, ⟨x', hx', rfl⟩, hx'e⟩ := hc
      have hx'sp := D.graphSet_subset_spear hx'
      have hpw : paperInY x' = paperInY (Φ q) :=
        D.inj (D.spear_sub ⟨x', hx'sp, rfl⟩) hWq hx'e
      have : x' = Φ q := paperInY.injOn (by simp) (by simp) hpw
      rw [hFq, ← this]; exact hx'.2.2
    · intro h0
      exact Or.inr (mem_iUnion.2 ⟨i, ⟨_, ⟨Φ q, ⟨hr, hA, by rw [← hFq]; exact h0⟩, rfl⟩, rfl⟩⟩)
  · simp only [F, if_neg hA]
    push Not at hA
    have hnot : D.ψ (paperInY (Φ q)) ∉ ⋃ j, (Dat.D j).spearSet := by
      intro hm'
      obtain ⟨j, hj⟩ := mem_iUnion.1 hm'
      by_cases hji : j = i
      · subst hji
        obtain ⟨_, ⟨w'', hw'', rfl⟩, hw''e⟩ := hj
        have h1 : paperInY w'' = paperInY (Φ q) :=
          (Dat.D j).inj ((Dat.D j).spear_sub ⟨w'', hw'', rfl⟩) hWq hw''e
        have h2 : w'' = Φ q := paperInY.injOn (by simp) (by simp) h1
        rw [h2] at hw''
        linarith [hw''.2]
      · exact hOthq (mem_iUnion.2 ⟨⟨j, hji⟩, hj⟩)
    have hsigS : D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar ↔ D.ψ (paperInY (Φ q)) ∈ S := by
      constructor
      · intro h
        have h' : D.ψ (paperInY (Φ q)) ∈ Dat.sigmaStar \ ⋃ j, (Dat.D j).spearSet := ⟨h, hnot⟩
        rw [Dat.sigmaStar_diff] at h'; exact h'.1
      · intro h
        have h' : D.ψ (paperInY (Φ q)) ∈ S \ ⋃ j, (Dat.D j).spearSet := ⟨h, hnot⟩
        rw [← Dat.sigmaStar_diff] at h'; exact h'.1
    rw [hsigS]
    have hVOq := hA5 q hq
    have hchain : D.ψ (paperInY (Φ q)) ∈ S ↔ q ∈ Causal.Flat.graphOver U' u := by
      constructor
      · intro hS'
        have hmem : g₁⁻¹ • q ∈ Sc ∩ (O : Set (Causal.Minkowski 2)) :=
          ⟨⟨⟨z₀, ⟨hS', hsrcq⟩, heq⟩, hVOq.1⟩, hVOq.2⟩
        have : g₁ • g₁⁻¹ • q ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) :=
          Set.smul_mem_smul_set hmem
        rw [hgr, smul_inv_smul] at this; exact this.2
      · intro hgq
        have : q ∈ g₁ • (Sc ∩ (O : Set (Causal.Minkowski 2))) := by
          rw [hgr]; exact ⟨⟨g₁⁻¹ • q, hVOq.2, smul_inv_smul _ _⟩, hgq⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem] at this
        obtain ⟨⟨z, ⟨hzS, hzs⟩, hzp⟩, -⟩ := this.1
        have := e.injOn hzs hsrcq (hzp.trans heq.symm)
        rw [this] at hzS; exact hzS
    rw [hchain]
    obtain ⟨-, h1, h2⟩ := hσ q (hWδ₁ hq)
    constructor
    · intro hgq
      exact (nullShift_unique hc₁ hu hm hmn (s := 0) (by simpa using hgq.1) (by simpa using hgq.2)
        h1 h2).symm
    · intro h0
      rw [h0, zero_smul, sub_zero] at h1 h2
      exact ⟨h1, h2⟩

omit [SecondCountableTopology M] in
/-- **(G4a) for a locally finite family**: `Σ*` is spacelike Lipschitz at the points of the cusps. -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp {S : Set M}
    (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M}
    (hy : regVal M y ∈ (Dat.D i).cusp) : IsSpacelikeLipschitzAt Dat.sigmaStarReg y := by
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
  rcases hx.2.1.lt_or_eq with h | h
  · exact Dat.isSpacelikeLipschitzAt_cusp_interior i hx h hxy.symm
  · exact Dat.isSpacelikeLipschitzAt_cusp_rim hSreg i hx h hxy.symm

omit [SecondCountableTopology M] in
/-- **(G4) for a locally finite family**: `Σ*` is spacelike Lipschitz in the flat charts of
`Reg M`; outside the (closed, by local finiteness) union of the spears it is `S`. -/
theorem LFSurgeryData.isSpacelikeLipschitz_sigmaStar {S : Set M}
    (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) : Causal.Flat.IsSpacelikeLipschitz 2 Dat.sigmaStarReg := by
  intro y hy
  by_cases hin : regVal M y ∈ ⋃ i, (Dat.D i).spearSet
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hin
    have hc : regVal M y ∈ (Dat.D i).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hy, hi⟩
    exact Dat.isSpacelikeLipschitzAt_cusp hSreg i hc
  · have hcl : IsClosed (⋃ i, (Dat.D i).spearSet) := Dat.isClosed_iUnion_spearSet
    set O : Set (e0RegMFlat M) := regSet M (⋃ i, (Dat.D i).spearSet)ᶜ
    have hO : IsOpen O := hcl.isOpen_compl.preimage continuous_subtype_val
    have hyS : y ∈ regSet M S := by
      have h : regVal M y ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨hy, hin⟩
      rw [Dat.sigmaStar_diff] at h
      exact h.1
    refine IsSpacelikeLipschitzAt.congr (hSreg y hyS) hO hin ?_
    ext z
    simp only [LFSurgeryData.sigmaStarReg, regSet, O, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hz, hzO⟩
      have h : regVal M z ∈ Dat.sigmaStar \ ⋃ i, (Dat.D i).spearSet := ⟨hz, hzO⟩
      rw [Dat.sigmaStar_diff] at h
      exact ⟨h.1, hzO⟩
    · rintro ⟨hz, hzO⟩
      have h : regVal M z ∈ S \ ⋃ i, (Dat.D i).spearSet := ⟨hz, hzO⟩
      rw [← Dat.sigmaStar_diff] at h
      exact ⟨h.1, hzO⟩

/-! ### Lemma 2.8's `log r` estimate on `Σ*`, spear by spear

The strict `E0Surgery.SurgeryData.logRad` and its estimate, verbatim, over a locally finite family
(they use one spear and `sigmaStar_inter_spearSet` only). -/

open Classical in
/-- **The clamped log-radius of the `i`-th cusp**, a function on `M`: `log (min r (R/2))` in the
spear, `log (R/2)` off it (B21 Lemma 2.8's `log r` estimate, cut below `R/2` so that the function
is locally constant near the rims). -/
noncomputable def LFSurgeryData.logRad {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι) (z : M) : ℝ :=
  if z ∈ (Dat.D i).spearSet then Real.log (min (rad ((Dat.D i).coord z)) ((Dat.D i).R / 2))
  else Real.log ((Dat.D i).R / 2)


omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- On `Σ*` the clamped log-radius is at most `log (R/2)`. -/
theorem LFSurgeryData.logRad_le {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι) {z : M}
    (hz : z ∈ Dat.sigmaStar) : Dat.logRad i z ≤ Real.log ((Dat.D i).R / 2) := by
  unfold LFSurgeryData.logRad
  split_ifs with h
  · have hc : z ∈ (Dat.D i).cusp := by rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hz, h⟩
    have hr := ((Dat.D i).coord_mem_graphSet hc).1
    exact Real.log_le_log (lt_min hr (by linarith [(Dat.D i).pos])) (min_le_right _ _)
  · exact le_rfl


omit [SecondCountableTopology M] in
/-- **The density bound behind Lemma 2.8, read on `Σ*`**: along a curve of `Σ*` with velocity `v`
in a flat chart, the derivative of the clamped log-radius is at most `√(ds²(v))` (where the clamp
is active it is locally constant or has a local maximum; in the cusp below `R/2`, `v` is tangent
to the height's level set and `δ ≥ 1/r²`, `sq_le_minkQ_of_tangent`). -/
theorem LFSurgeryData.abs_deriv_logRad_le {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    {c : ℝ → e0RegMFlat M} {t : ℝ} (hc : ContinuousAt c t)
    (hcS : ∀ᶠ s in 𝓝 t, c s ∈ Dat.sigmaStarReg)
    {e₀ : OpenPartialHomeomorph (e0RegMFlat M) (Causal.Minkowski 2)}
    (he₀ : e₀ ∈ atlas (Causal.Minkowski 2) (e0RegMFlat M)) (hct : c t ∈ e₀.source)
    {v : Causal.Minkowski 2} (hv : HasDerivAt (fun s => e₀ (c s)) v t) :
    |deriv (fun s => Dat.logRad i (regVal M (c s))) t| ≤ Real.sqrt (Causal.Flat.minkQ v) := by
  set D := Dat.D i with hD
  set f : ℝ → ℝ := fun s => Dat.logRad i (regVal M (c s)) with hf
  have hcM : ContinuousAt (fun s => regVal M (c s)) t :=
    continuous_subtype_val.continuousAt.comp hc
  have hR2 : 0 < D.R / 2 := by linarith [D.pos]
  have hconst : (∀ᶠ s in 𝓝 t, f s = Real.log (D.R / 2)) → |deriv f t| ≤ Real.sqrt (Causal.Flat.minkQ v) := by
    intro h
    have h' : f =ᶠ[𝓝 t] fun _ => Real.log (D.R / 2) := h
    rw [h'.deriv_eq, deriv_const, abs_zero]; exact Real.sqrt_nonneg _
  by_cases hin : regVal M (c t) ∈ D.spearSet
  swap
  · apply hconst
    filter_upwards [hcM.preimage_mem_nhds ((Dat.isClosed i).isOpen_compl.mem_nhds hin)] with s hs
    simp only [f, LFSurgeryData.logRad, if_neg (show regVal M (c s) ∉ (Dat.D i).spearSet from hs)]
    rfl
  have hcSt : regVal M (c t) ∈ Dat.sigmaStar := hcS.self_of_nhds
  have hcusp : regVal M (c t) ∈ D.cusp := by
    rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hcSt, hin⟩
  set x := D.coord (regVal M (c t)) with hxdef
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  have hxg : x ∈ graphSet D.G D.R := D.coord_mem_graphSet hcusp
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  have hctW : regVal M (c t) ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp hcM hctW
  have hgx : D.ginv (regVal M (c t)) = paperInY x := by
    rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv (regVal M (c t))) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun s => paperOfY (D.ginv (regVal M (c s)))) t :=
    ContinuousAt.comp (f := fun s => D.ginv (regVal M (c s))) hpo hgc
  have hwt : paperOfY (D.ginv (regVal M (c t))) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun s => paperOfY (D.ginv (regVal M (c s)))) (𝓝 t) (𝓝 x) :=
    hwt ▸ hwc.tendsto
  have hψW : ∀ᶠ s in 𝓝 t, regVal M (c s) ∈ D.ψ '' D.W :=
    hcM.preimage_mem_nhds ((D.isOpen_image D.isOpen subset_rfl).mem_nhds hctW)
  -- in a spear, the coordinates are `paperOfY ∘ ginv`
  have hcoord : ∀ z ∈ D.spearSet, D.coord z = paperOfY (D.ginv z) := fun z hz => by
    obtain ⟨hz1, hz2⟩ := D.coord_mem hz
    have := D.coord_eq_ginv hz1
    rwa [hz2] at this
  rcases lt_trichotomy (rad x) (D.R / 2) with hlt | heq | hgt
  · -- the cusp below `R/2`: the formula
    have hrx : 0 < rad x := hxg.1
    have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hrx
    have hfx : D.v < fcoord x := by
      have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
        have := hxg.2.2; simp only [height, heightAt] at this; linarith
      have h2 := D.above (rad x, Complex.arg x.2) hrx hxg.2.1
      simp only [fcoord]; rw [h1]; linarith
    have hper := D.spacelike.periodic
    obtain ⟨g, hg⟩ := D.eventually_atlasChart hx0 hxW he₀ hxe.symm hct
    -- the open interior of the spear
    set B : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hB
    have hBo : IsOpen B :=
      (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
        (isOpen_lt continuous_rad continuous_const)
    have hxB : x ∈ B := ⟨hfx, by linarith [D.pos]⟩
    have hBsp : B ⊆ E0Spear.spear D.v D.R := fun w hw => ⟨hw.1.le, hw.2.le⟩
    have hev : ∀ᶠ s in 𝓝 t, regVal M (c s) ∈ D.ψ '' D.W ∧
        paperOfY (D.ginv (regVal M (c s))) ∈ B ∧
        rad (paperOfY (D.ginv (regVal M (c s)))) < D.R / 2 ∧ c s ∈ Dat.sigmaStarReg ∧
        ∀ z' : e0RegMFlat M, regVal M z' = D.ψ (paperInY (paperOfY (D.ginv (regVal M (c s))))) →
          z' ∈ e₀.source ∧ e₀ z' = g • E0.chartMap x (paperOfY (D.ginv (regVal M (c s)))) :=
      hψW.and ((hTw.eventually (hBo.mem_nhds hxB)).and
        ((hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Iio).mem_nhds hlt)).and
          (hcS.and (hTw.eventually hg))))
    have hrange : ∀ᶠ s in 𝓝 t, D.ginv (regVal M (c s)) ∈ range (Sum.inr : BTZE0 → E0Y) := by
      refine hgc.preimage_mem_nhds (isOpen_range_inr.mem_nhds ?_)
      rw [hgx, paperInY_apply]; exact mem_range_self _
    set p : ℝ → Causal.Minkowski 2 := fun s => e₀ (c s) with hp
    set β : Causal.Minkowski 2 → ℝ := fun q => (chartNull g q).2.1 with hβ
    set FI := chartHeight D.G g with hFI
    have hkey : ∀ᶠ s in 𝓝 t, f s = Real.log (β (p s)) ∧ FI (p s) = 0 := by
      filter_upwards [hev, hrange] with s ⟨hsW, hsB, hsr, hsS, hsch⟩ hsr'
      set w := paperOfY (D.ginv (regVal M (c s))) with hw
      have hpw : paperInY w = D.ginv (regVal M (c s)) := by
        obtain ⟨u, hu⟩ := hsr'
        rw [hw, ← hu, paperOfY_inr, paperInY_apply, Homeomorph.symm_apply_apply]
      have hzs : regVal M (c s) = D.ψ (paperInY w) := by
        rw [hpw]; exact (Function.invFunOn_eq hsW).symm
      obtain ⟨-, hes⟩ := hsch (c s) hzs
      have hwsp : w ∈ E0Spear.spear D.v D.R := hBsp hsB
      have hsp : regVal M (c s) ∈ D.spearSet := by rw [hzs]; exact ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
      have hcw : D.coord (regVal M (c s)) = w := by rw [hzs]; exact D.coord_apply hwsp
      have hβw : β (p s) = rad w := by
        simp only [β, p, hes, chartNull, inv_smul_smul, E0.chartMap, LinearEquiv.symm_apply_apply]
        rfl
      refine ⟨?_, ?_⟩
      · show Dat.logRad i (regVal M (c s)) = _
        rw [LFSurgeryData.logRad, if_pos (show regVal M (c s) ∈ (Dat.D i).spearSet from hsp),
          show (Dat.D i).coord (regVal M (c s)) = w from hcw, hβw,
          min_eq_left (show rad w ≤ (Dat.D i).R / 2 from hsr.le)]
      · have hcs : regVal M (c s) ∈ D.cusp := by
          rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hsS, hsp⟩
        have hwg : w ∈ graphSet D.G D.R := by rw [← hcw]; exact D.coord_mem_graphSet hcs
        simp only [FI, p, hes, chartHeight, nullHeight, inv_smul_smul, E0.chartMap,
          LinearEquiv.symm_apply_apply, locLift]
        rw [show Complex.arg x.2 + Complex.arg (w.2 / x.2) = angle x w from rfl,
          unlift_lift (polar_angle hx0 w)]
        exact hwg.2.2
    -- the values at `t`
    obtain ⟨-, het⟩ := hg.self_of_nhds (c t) hxe.symm
    set pp : ℝ × ℝ × ℝ := (x.1, rad x, angle x x) with hpp
    have hpt : p t = g • nullToMink (btzPaperNull pp) := by
      simp only [p, het, E0.chartMap]; rfl
    have hβt : β (p t) = rad x := by
      simp only [β, hpt, chartNull, inv_smul_smul, LinearEquiv.symm_apply_apply]; rfl
    have hβF := hasFDerivAt_chartNull_rad g (p t)
    have hβd : HasDerivAt (fun s => β (p s)) (fderiv ℝ β (p t) v) t := by
      rw [hβF.fderiv]; exact hβF.comp_hasDerivAt t hv
    have hlog : HasDerivAt (fun s => Real.log (β (p s))) (fderiv ℝ β (p t) v / β (p t)) t :=
      hβd.log (by rw [hβt]; exact hrx.ne')
    have hfd : deriv f t = fderiv ℝ β (p t) v / rad x := by
      rw [← hβt]
      exact (hlog.congr_of_eventuallyEq (hkey.mono fun s hs => hs.1)).deriv
    -- `v` is tangent to the level set of `FI`
    have hpos : 0 < (chartNull g (p t)).2.1 := by
      have : β (p t) = (chartNull g (p t)).2.1 := rfl
      rw [← this, hβt]; exact hrx
    have hFId : HasFDerivAt FI (fderiv ℝ FI (p t)) (p t) :=
      (((contDiffOn_chartHeight hper D.smooth g).differentiableOn one_ne_zero).differentiableAt
        ((isOpen_chartPos g).mem_nhds hpos)).hasFDerivAt
    have h1 : HasDerivAt (fun s => FI (p s)) (fderiv ℝ FI (p t) v) t := hFId.comp_hasDerivAt t hv
    have h0 : HasDerivAt (fun s => FI (p s)) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (hkey.mono fun s hs => hs.2)
    have htan : fderiv ℝ FI (p t) v = 0 := h1.unique h0
    obtain ⟨L, hL, hδL⟩ := hδ (rad x, angle x x) hrx
    rw [hpt] at htan
    have hb := sq_le_minkQ_of_tangent hper D.smooth g (pp := pp) hrx hL hδL htan
    rw [hfd]
    rw [← hpt] at hb
    exact Real.abs_le_sqrt hb
  · -- `r = R/2`: a local maximum
    have hft : f t = Real.log (D.R / 2) := by
      show Dat.logRad i (regVal M (c t)) = _
      rw [LFSurgeryData.logRad, if_pos (show regVal M (c t) ∈ (Dat.D i).spearSet from hin),
        show (Dat.D i).coord (regVal M (c t)) = x from rfl, heq, min_self]
    have hmax : IsLocalMax f t := by
      filter_upwards [hcS] with s hs
      rw [hft]
      exact Dat.logRad_le i hs
    rw [hmax.deriv_eq_zero, abs_zero]; exact Real.sqrt_nonneg _
  · -- `r > R/2`: locally constant
    apply hconst
    have hev := hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt)
    filter_upwards [hev] with s hs
    simp only [f, LFSurgeryData.logRad]
    split_ifs with h
    · rw [hcoord _ h, min_eq_right (le_of_lt hs)]
    · rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- **Where the clamp is active, `logRad` is locally constant** (off the closed spear, or in the
spear above `r = R/2`). -/
theorem LFSurgeryData.eventually_logRad_const {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {z₀ : M} (h : z₀ ∉ (Dat.D i).spearSet ∨
      (z₀ ∈ (Dat.D i).spearSet ∧ (Dat.D i).R / 2 < rad ((Dat.D i).coord z₀))) :
    ∀ᶠ z in 𝓝 z₀, Dat.logRad i z = Real.log ((Dat.D i).R / 2) := by
  set D := Dat.D i with hD
  rcases h with hout | ⟨hin, hgt⟩
  · filter_upwards [(Dat.isClosed i).isOpen_compl.mem_nhds hout] with z hz
    simp only [LFSurgeryData.logRad, if_neg (show z ∉ (Dat.D i).spearSet from hz)]
    rfl
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  set x := D.coord z₀ with hxdef
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  have hctW : z₀ ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp (c := fun z : M => z) continuousAt_id hctW
  have hgx : D.ginv z₀ = paperInY x := by rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv z₀) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun z => paperOfY (D.ginv z)) z₀ :=
    ContinuousAt.comp (f := fun z => D.ginv z) hpo hgc
  have hwt : paperOfY (D.ginv z₀) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun z => paperOfY (D.ginv z)) (𝓝 z₀) (𝓝 x) := hwt ▸ hwc.tendsto
  have hcoord : ∀ z ∈ D.spearSet, D.coord z = paperOfY (D.ginv z) := fun z hz => by
    obtain ⟨hz1, hz2⟩ := D.coord_mem hz
    have := D.coord_eq_ginv hz1
    rwa [hz2] at this
  filter_upwards [hTw.eventually ((continuous_rad.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt)]
    with z hz
  unfold LFSurgeryData.logRad
  split_ifs with h
  · rw [hcoord _ h, min_eq_right (le_of_lt hz)]
  · rfl

omit [SecondCountableTopology M] in
/-- **Below the clamp, `logRad` is `log (min r (R/2))` with `r` affine in the chart** at a point of
the open spear interior off the axis. -/
theorem LFSurgeryData.eventually_logRad_formula {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {z₀ : e0RegMFlat M} (hin : regVal M z₀ ∈ (Dat.D i).spearSet)
    (hr0 : 0 < rad ((Dat.D i).coord (regVal M z₀)))
    (hrR : rad ((Dat.D i).coord (regVal M z₀)) < (Dat.D i).R)
    (hfv : (Dat.D i).v < fcoord ((Dat.D i).coord (regVal M z₀))) :
    ∃ g : Causal.Flat.isom 2, (∀ᶠ z in 𝓝 z₀, z ∈ (chartAt (Causal.Minkowski 2) z₀).source ∧
      Dat.logRad i (regVal M z) =
        Real.log (min (chartNull g (chartAt (Causal.Minkowski 2) z₀ z)).2.1 ((Dat.D i).R / 2))) ∧
      (chartNull g (chartAt (Causal.Minkowski 2) z₀ z₀)).2.1 = rad ((Dat.D i).coord (regVal M z₀)) := by
  set D := Dat.D i with hD
  obtain ⟨hxsp, hxe⟩ := D.coord_mem hin
  set x := D.coord (regVal M z₀) with hxdef
  have hx0 : x.2 ≠ 0 := fun h => by simp [rad, h] at hr0
  have hxW : paperInY x ∈ D.W := D.spear_sub ⟨x, hxsp, rfl⟩
  obtain ⟨g, hg⟩ := D.eventually_atlasChart hx0 hxW (chart_mem_atlas (Causal.Minkowski 2) z₀)
    hxe.symm (mem_chart_source _ z₀)
  have hcM : ContinuousAt (fun z : e0RegMFlat M => regVal M z) z₀ :=
    continuous_subtype_val.continuousAt
  have hctW : regVal M z₀ ∈ D.ψ '' D.W := ⟨paperInY x, hxW, hxe⟩
  have hgc := D.continuousAt_ginv_comp (c := fun z : e0RegMFlat M => regVal M z) hcM hctW
  have hgx : D.ginv (regVal M z₀) = paperInY x := by rw [← hxe]; exact D.ginv_apply hxW
  have hpo : ContinuousAt paperOfY (D.ginv (regVal M z₀)) := by
    refine paperOfY.continuousAt ?_
    rw [paperOfY_source, hgx, paperInY_apply]; exact mem_range_self _
  have hwc : ContinuousAt (fun z : e0RegMFlat M => paperOfY (D.ginv (regVal M z))) z₀ :=
    ContinuousAt.comp (f := fun z : e0RegMFlat M => D.ginv (regVal M z)) hpo hgc
  have hwt : paperOfY (D.ginv (regVal M z₀)) = x := by rw [hgx, E0Spear.paperOfY_paperInY]
  have hTw : Tendsto (fun z : e0RegMFlat M => paperOfY (D.ginv (regVal M z))) (𝓝 z₀) (𝓝 x) :=
    hwt ▸ hwc.tendsto
  set B : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hB
  have hBo : IsOpen B :=
    (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
      (isOpen_lt continuous_rad continuous_const)
  have hBsp : B ⊆ E0Spear.spear D.v D.R := fun w hw => ⟨hw.1.le, hw.2.le⟩
  have hψW : ∀ᶠ z in 𝓝 z₀, regVal M z ∈ D.ψ '' D.W :=
    hcM.preimage_mem_nhds ((D.isOpen_image D.isOpen subset_rfl).mem_nhds hctW)
  have hrange : ∀ᶠ z in 𝓝 z₀, D.ginv (regVal M z) ∈ range (Sum.inr : BTZE0 → E0Y) := by
    refine hgc.preimage_mem_nhds (isOpen_range_inr.mem_nhds ?_)
    rw [hgx, paperInY_apply]; exact mem_range_self _
  have hchart : ∀ z : e0RegMFlat M, chartAt (Causal.Minkowski 2) z₀ z ∈
      {p | True} := fun _ => trivial
  have hval : ∀ w : E0, (chartNull g (g • E0.chartMap x w)).2.1 = rad w := by
    intro w; simp only [chartNull, inv_smul_smul, E0.chartMap, LinearEquiv.symm_apply_apply]; rfl
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [hψW, hrange, hTw.eventually (hBo.mem_nhds ⟨hfv, hrR⟩), hTw.eventually hg]
      with z hzW hzr hzB hzch
    set w := paperOfY (D.ginv (regVal M z)) with hw
    have hpw : paperInY w = D.ginv (regVal M z) := by
      obtain ⟨u, hu⟩ := hzr
      rw [hw, ← hu, paperOfY_inr, paperInY_apply, Homeomorph.symm_apply_apply]
    have hzs : regVal M z = D.ψ (paperInY w) := by rw [hpw]; exact (Function.invFunOn_eq hzW).symm
    obtain ⟨hsrc, hes⟩ := hzch z hzs
    have hwsp : w ∈ E0Spear.spear D.v D.R := hBsp hzB
    have hsp : regVal M z ∈ D.spearSet := by rw [hzs]; exact ⟨paperInY w, ⟨w, hwsp, rfl⟩, rfl⟩
    have hcw : D.coord (regVal M z) = w := by rw [hzs]; exact D.coord_apply hwsp
    refine ⟨hsrc, ?_⟩
    rw [LFSurgeryData.logRad, if_pos (show regVal M z ∈ (Dat.D i).spearSet from hsp),
      show (Dat.D i).coord (regVal M z) = w from hcw, hes, hval]
  · obtain ⟨-, het⟩ := hg.self_of_nhds z₀ hxe.symm
    rw [het, hval]

omit [SecondCountableTopology M] in
/-- **The clamped log-radius is locally Lipschitz along a path of `Σ*` Lipschitz in charts.** -/
theorem LFSurgeryData.exists_lipschitzOnWith_logRad {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {a b : Dat.sigmaStarReg} (γ : Path a b)
    (hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ K : NNReal, LipschitzOnWith K
      (fun t => Dat.logRad i (regVal M ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M)))
      (Icc (t₀ - ε) (t₀ + ε)) := by
  set D := Dat.D i with hD
  set c : ℝ → e0RegMFlat M := fun t => ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M) with hc
  have hcc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  set f : ℝ → ℝ := fun t => Dat.logRad i (regVal M (c t)) with hf
  set z₀ := c t₀ with hz₀
  have hz₀S : regVal M z₀ ∈ Dat.sigmaStar := (γ.extend t₀).2
  by_cases hconst : regVal M z₀ ∉ D.spearSet ∨ (regVal M z₀ ∈ D.spearSet ∧ D.R / 2 < rad (D.coord (regVal M z₀)))
  · have hev := Dat.eventually_logRad_const i hconst
    have hev' : ∀ᶠ t in 𝓝 t₀, f t = Real.log (D.R / 2) :=
      ((continuous_subtype_val.comp hcc).continuousAt (x := t₀)).eventually hev
    obtain ⟨ε, hε, hI⟩ := Causal.Flat.exists_Icc_subset_of_eventually hev'
    refine ⟨ε, hε, 0, fun s hs s' hs' => ?_⟩
    show edist (f s) (f s') ≤ _
    rw [hI s hs, hI s' hs', edist_self]; exact bot_le
  push Not at hconst
  obtain ⟨hin, hle⟩ := hconst
  have hle := hle hin
  have hcusp : regVal M z₀ ∈ D.cusp := by
    rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hz₀S, hin⟩
  have hxg := D.coord_mem_graphSet hcusp
  set x := D.coord (regVal M z₀) with hxdef
  have hrx : 0 < rad x := hxg.1
  have hfv : D.v < fcoord x := by
    have h1 : x.1 = D.G (rad x, Complex.arg x.2) := by
      have := hxg.2.2; simp only [height, heightAt] at this; linarith
    have h2 := D.above (rad x, Complex.arg x.2) hrx hxg.2.1
    simp only [fcoord]; rw [h1]; linarith
  obtain ⟨g, hg, hg0⟩ := Dat.eventually_logRad_formula i hin hrx (by linarith [D.pos]) hfv
  set e₀ := chartAt (Causal.Minkowski 2) z₀ with he₀
  set β : Causal.Minkowski 2 → ℝ := fun q => (chartNull g q).2.1 with hβ
  obtain ⟨Kβ, hKβ⟩ := lipschitzWith_chartNull_rad g
  -- the lower bound on `β`
  have hβc : ContinuousAt (fun t => β (e₀ (c t))) t₀ :=
    (hKβ.continuous.continuousAt).comp ((e₀.continuousAt (mem_chart_source _ z₀)).comp
      hcc.continuousAt)
  set m := rad x / 2 with hm
  have hm0 : 0 < m := by positivity
  have hβ0 : β (e₀ (c t₀)) = rad x := hg0
  have hev : ∀ᶠ t in 𝓝 t₀, (c t ∈ e₀.source ∧ Dat.logRad i (regVal M (c t)) =
      Real.log (min (β (e₀ (c t))) (D.R / 2))) ∧ m < β (e₀ (c t)) :=
    (hcc.continuousAt.eventually hg).and (hβc.eventually (lt_mem_nhds (show m < β (e₀ (c t₀)) by rw [hβ0]; linarith)))
  obtain ⟨ε₂, hε₂, hI₂⟩ := Causal.Flat.exists_Icc_subset_of_eventually hev
  obtain ⟨ε₁, hε₁, K₁, hK₁⟩ := hL t₀
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsub₁ : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc (t₀ - ε₁) (t₀ + ε₁) :=
    Icc_subset_Icc (by linarith [min_le_left ε₁ ε₂]) (by linarith [min_le_left ε₁ ε₂])
  have hsub₂ : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc (t₀ - ε₂) (t₀ + ε₂) :=
    Icc_subset_Icc (by linarith [min_le_right ε₁ ε₂]) (by linarith [min_le_right ε₁ ε₂])
  have hR2m : m ≤ D.R / 2 := by
    have := hxg.2.1; linarith
  refine ⟨ε, hε, ⟨1 / m, by positivity⟩ * Kβ * K₁, LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_⟩
  obtain ⟨⟨-, hfs⟩, hms⟩ := hI₂ s (hsub₂ hs)
  obtain ⟨⟨-, hfs'⟩, hms'⟩ := hI₂ s' (hsub₂ hs')
  have hchart : dist (e₀ (c s)) (e₀ (c s')) ≤ K₁ * dist s s' :=
    hK₁.dist_le_mul s (hsub₁ hs) s' (hsub₁ hs')
  have hβL : dist (β (e₀ (c s))) (β (e₀ (c s'))) ≤ Kβ * dist (e₀ (c s)) (e₀ (c s')) :=
    hKβ.dist_le_mul _ _
  have hmin : |min (β (e₀ (c s))) (D.R / 2) - min (β (e₀ (c s'))) (D.R / 2)| ≤
      |β (e₀ (c s)) - β (e₀ (c s'))| := abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
  have hlog := abs_log_sub_log_le hm0 (le_min hms.le hR2m) (le_min hms'.le hR2m)
  show dist (f s) (f s') ≤ _
  rw [Real.dist_eq]
  simp only [f, hfs, hfs']
  rw [Real.dist_eq] at hβL
  push_cast
  calc |Real.log (min (β (e₀ (c s))) (D.R / 2)) - Real.log (min (β (e₀ (c s'))) (D.R / 2))|
      ≤ (1 / m) * |β (e₀ (c s)) - β (e₀ (c s'))| :=
        hlog.trans (mul_le_mul_of_nonneg_left hmin (by positivity))
    _ ≤ (1 / m) * (Kβ * (K₁ * dist s s')) := by
        refine mul_le_mul_of_nonneg_left (hβL.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hchart Kβ.2
    _ = 1 / m * Kβ * K₁ * dist s s' := by ring

omit [SecondCountableTopology M] in
/-- **The clamped log-radius is `1`-Lipschitz for the induced length of `Σ*`** (B21 Lemma 2.8's
`log r` estimate, l.799–806, on the glued surface): along every path Lipschitz in charts, its
derivative is a.e. at most the density (`abs_deriv_logRad_le`, Rademacher in a chart near each
time), and `le_localLength_of_lipschitzOnWith` integrates. -/
theorem LFSurgeryData.ofReal_abs_logRad_sub_le_edist {S : Set M} (Dat : LFSurgeryData M S)
    (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    (a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) :
    ENNReal.ofReal |Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype b : Dat.sigmaStarReg) : e0RegMFlat M)) -
      Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M))| ≤
      edist a b := by
  change _ ≤ ⨅ γ : Path (Causal.Flat.LocalLengthSpace.toSpace a)
    (Causal.Flat.LocalLengthSpace.toSpace b),
    Causal.Flat.pathLength (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ
  refine le_iInf fun γ => ?_
  by_cases hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend
  swap
  · rw [Causal.Flat.pathLength_of_not_isLocLip _ hL]; exact le_top
  rw [Causal.Flat.pathLength_of_isLocLip _ hL]
  set c : ℝ → e0RegMFlat M := fun t => ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M) with hc
  have hcc : Continuous c := continuous_subtype_val.comp γ.continuous_extend
  set f : ℝ → ℝ := fun t => Dat.logRad i (regVal M (c t)) with hf
  have hloc : LocallyLipschitzOn (Icc (0 : ℝ) 1) f := by
    intro t₀ _
    obtain ⟨ε, hε, K, hK⟩ := Dat.exists_lipschitzOnWith_logRad i γ hL t₀
    exact ⟨K, Icc (t₀ - ε) (t₀ + ε),
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith)), hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hd : ∀ᵐ t, t ∈ Ioc (0 : ℝ) 1 → ENNReal.ofReal (1 * |deriv f t|) ≤
      Causal.Flat.localDensity (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend t := by
    refine ae_of_local fun t₀ => ?_
    set e₀ := chartAt (Causal.Minkowski 2) (c t₀) with he₀
    obtain ⟨ε₁, hε₁, K₁, hK₁⟩ := hL t₀
    have hsrc : ∀ᶠ s in 𝓝 t₀, c s ∈ e₀.source :=
      hcc.continuousAt.preimage_mem_nhds (e₀.open_source.mem_nhds (mem_chart_source _ _))
    obtain ⟨ε₂, hε₂, hI₂⟩ := Causal.Flat.exists_Icc_subset_of_eventually hsrc
    set ε := min ε₁ ε₂ with hεdef
    have hε : 0 < ε := lt_min hε₁ hε₂
    refine ⟨ε, hε, ?_⟩
    have hK₁' : LipschitzOnWith K₁ (fun s => e₀ (c s)) (Icc (t₀ - ε) (t₀ + ε)) :=
      hK₁.mono (Icc_subset_Icc (by linarith [min_le_left ε₁ ε₂]) (by linarith [min_le_left ε₁ ε₂]))
    filter_upwards [hK₁'.ae_differentiableWithinAt_of_mem] with u hu huI _
    have huI' : u ∈ Icc (t₀ - ε) (t₀ + ε) := Ioo_subset_Icc_self huI
    have hdiff : DifferentiableAt ℝ (fun s => e₀ (c s)) u :=
      (hu huI').differentiableAt (Icc_mem_nhds huI.1 huI.2)
    have hus : c u ∈ e₀.source := hI₂ u
      (Icc_subset_Icc (by linarith [min_le_right ε₁ ε₂]) (by linarith [min_le_right ε₁ ε₂]) huI')
    rw [one_mul, Causal.Flat.localDensity_chartSys_eq (c := γ.extend)
      γ.continuous_extend.continuousAt (chart_mem_atlas _ _) hus]
    exact ENNReal.ofReal_le_ofReal (Dat.abs_deriv_logRad_le i hδ hcc.continuousAt
      (Eventually.of_forall fun s => (γ.extend s).2) (chart_mem_atlas _ _) hus hdiff.hasDerivAt)
  have key := le_localLength_of_lipschitzOnWith (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend
    (f := f) zero_le_one zero_le_one hK hd
  simp only [f, c, Path.extend_zero, Path.extend_one, one_mul] at key
  exact key


/-! ### (G5) completeness -/

/-- The point of `M` under a point of the length space of `Σ*`. -/
noncomputable def LFSurgeryData.lenPt {S : Set M} (Dat : LFSurgeryData M S)
    (a : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) : M :=
  regVal M ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M)

/-- A Cauchy surface of a globally hyperbolic `𝔼₀`-manifold is closed (`S = J⁺(S) ∩ J⁻(S)`). -/
theorem isClosed_of_isCauchySurface (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) : IsClosed S := by
  obtain ⟨-, hp, hm, -, hpm, -, -⟩ := cauchy_facts_lf hGH hS
  have h : S = (E0CBG.CE M).Jplus ⊤ S ∩ (E0CBG.CE M).Jminus ⊤ S :=
    Subset.antisymm (fun y hy => ⟨⟨y, hy, (E0CBG.CE M).le_refl (show y ∈ (⊤ : Opens M) from trivial)⟩,
      ⟨y, hy, (E0CBG.CE M).le_refl (show y ∈ (⊤ : Opens M) from trivial)⟩⟩)
      fun y hy => hpm y hy.1 hy.2
  rw [h]; exact hp.inter hm

/-- **(G5), the compact part** (the strict `E0Surgery.SurgeryData.completeSpace_sigmaStar_of_delta`,
localised to a compact set): a Cauchy sequence of `Σ*` whose tail lies in a compact set `K` of `M`
converges. `K` meets finitely many spears (local finiteness); in each of them the clamped
log-radius of the tail is bounded below (Lemma 2.8, `ofReal_abs_logRad_sub_le_edist`), so the
tail stays in `T = ((S ∖ spears) ∩ K) ∪ ⋃ᵢ ψᵢ(graph of Gᵢ over ρᵢ ≤ r ≤ Rᵢ)`, `i` over those
spears, which is compact; a subsequence converges in `M`, hence in `Σ*`, hence for the induced
length (`Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm`). -/
theorem LFSurgeryData.tendsto_of_cauchySeq_of_isCompact {S : Set M} (hSc : IsClosed S)
    (Dat : LFSurgeryData M S) (hL : Causal.Flat.IsSpacelikeLipschitz 2 Dat.sigmaStarReg)
    {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg} (hu : CauchySeq u)
    {K : Set M} (hK : IsCompact K) (hKu : ∀ᶠ n in atTop, Dat.lenPt (u n) ∈ K) :
    ∃ a, Tendsto u atTop (𝓝 a) := by
  classical
  have hA := E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)
  haveI := hA.metrizable
  have hcont := Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype_symm hL
  set pt : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg → M := Dat.lenPt with hpt
  have hptS : ∀ a, pt a ∈ Dat.sigmaStar := fun a => (Causal.Flat.InducedLengthSpace.toSubtype a).2
  obtain ⟨NK, hNK⟩ := eventually_atTop.1 hKu
  set F : Set Dat.ι := {i | ((Dat.D i).spearSet ∩ K).Nonempty} with hFdef
  have hF : F.Finite := Dat.finite_spears_of_isCompact hK
  -- the clamped log-radii are bounded below
  have hb : ∀ i, ∃ N, ∀ n ≥ N, Dat.logRad i (pt (u N)) - 1 < Dat.logRad i (pt (u n)) := by
    intro i
    obtain ⟨N, hN⟩ := (EMetric.cauchySeq_iff'.1 hu) 1 one_pos
    refine ⟨N, fun n hn => ?_⟩
    have h1 := Dat.ofReal_abs_logRad_sub_le_edist i (Dat.D i).delta (u N) (u n)
    have h2 : edist (u N) (u n) < 1 := by rw [edist_comm]; exact hN n hn
    have h3 := h1.trans_lt h2
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at h3
    have := abs_lt.1 h3
    simp only [pt, LFSurgeryData.lenPt] at this ⊢
    linarith
  choose N hN using hb
  set N₀ := max NK (hF.toFinset.sup N) with hN₀
  set ρ : Dat.ι → ℝ := fun i => Real.exp (Dat.logRad i (pt (u (N i))) - 1) with hρdef
  have hρ0 : ∀ i, 0 < ρ i := fun i => Real.exp_pos _
  have hρR : ∀ i, ρ i ≤ (Dat.D i).R := by
    intro i
    have h1 := Dat.logRad_le i (hptS (u (N i)))
    have h2 : ρ i ≤ Real.exp (Real.log ((Dat.D i).R / 2)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_log (by linarith [(Dat.D i).pos])] at h2
    linarith [(Dat.D i).pos]
  have hρu : ∀ i ∈ F, ∀ n ≥ N₀, pt (u n) ∈ (Dat.D i).spearSet →
      ρ i ≤ rad ((Dat.D i).coord (pt (u n))) := by
    intro i hiF n hn hin
    have hn' : N i ≤ n :=
      ((Finset.le_sup (hF.mem_toFinset.2 hiF)).trans (le_max_right _ _)).trans hn
    have h1 := hN i n hn'
    have hc : pt (u n) ∈ (Dat.D i).cusp := by
      rw [← Dat.sigmaStar_inter_spearSet i]; exact ⟨hptS _, hin⟩
    have hr0 := ((Dat.D i).coord_mem_graphSet hc).1
    have hmin0 : 0 < min (rad ((Dat.D i).coord (pt (u n)))) ((Dat.D i).R / 2) :=
      lt_min hr0 (by linarith [(Dat.D i).pos])
    have h2 : Dat.logRad i (pt (u n)) =
        Real.log (min (rad ((Dat.D i).coord (pt (u n)))) ((Dat.D i).R / 2)) := by
      rw [LFSurgeryData.logRad, if_pos hin]
    rw [h2] at h1
    have h3 := (Real.lt_log_iff_exp_lt hmin0).1 h1
    exact h3.le.trans (min_le_left _ _)
  -- the compact set `T`
  set Kg : Dat.ι → Set E0 := fun i =>
    (fun q : ℝ × ℝ => (((Dat.D i).G q, (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) : E0)) ''
      (Icc (ρ i) (Dat.D i).R ×ˢ Icc (-π) π) with hKgdef
  set U := ⋃ i, (Dat.D i).spearSet with hU
  set B := ⋃ i ∈ F, (Dat.D i).ψ '' (paperInY '' Kg i) with hB
  set T : Set M := ((S \ U) ∩ K) ∪ B with hT
  have hψc : ∀ i, ContinuousOn (fun x : E0 => (Dat.D i).ψ (paperInY x))
      (E0Spear.spear (Dat.D i).v (Dat.D i).R) := by
    intro i x hx
    have hxW : paperInY x ∈ (Dat.D i).W := (Dat.D i).spear_sub ⟨x, hx, rfl⟩
    exact (((Dat.D i).mor _ hxW).1.continuousAt ((Dat.D i).isOpen.mem_nhds hxW)).comp
      E0Spear.continuous_paperInY.continuousAt |>.continuousWithinAt
  have hBi : ∀ i, IsCompact ((Dat.D i).ψ '' (paperInY '' Kg i)) := by
    intro i
    rw [image_image]
    exact ((Dat.D i).isCompact_annulusGraph (hρ0 i)).image_of_continuousOn
      ((hψc i).mono (((Dat.D i).annulusGraph_subset (hρ0 i)).trans (Dat.D i).graphSet_subset_spear))
  have hBc : IsCompact B := hF.isCompact_biUnion fun i _ => hBi i
  have hBsub : B ⊆ Dat.sigmaStar := by
    intro z hz
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 hz
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hi
    exact Or.inr (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, (Dat.D i).annulusGraph_subset (hρ0 i) hw, rfl⟩, rfl⟩⟩)
  have hTS : T ⊆ Dat.sigmaStar := union_subset (fun z hz => Or.inl hz.1) hBsub
  have hclos : closure ((S \ U) ∩ K) ⊆ T := by
    intro z hz
    have hz' : z ∈ closure (S \ U) := closure_mono inter_subset_left hz
    have hzS : z ∈ S := closure_minimal (sdiff_subset.trans subset_rfl) hSc hz'
    have hzK : z ∈ K := closure_minimal inter_subset_right hK.isClosed hz
    by_cases hzU : z ∈ U
    swap
    · exact Or.inl ⟨⟨hzS, hzU⟩, hzK⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hzU
    have hiF : i ∈ F := ⟨z, hi, hzK⟩
    set D := Dat.D i with hD
    obtain ⟨hxsp, hxe⟩ := D.coord_mem hi
    set x := D.coord z with hxdef
    have hx1 : x.1 = D.τS x.2 := (D.graph x hxsp).1 (by rw [hxe]; exact hzS)
    have hsh := D.shaft x.2 hxsp.2
    rcases hxsp.2.lt_or_eq with hlt | heq
    · exfalso
      set O : Set E0 := {w | D.v < fcoord w ∧ rad w < D.R} with hO
      have hOo : IsOpen O :=
        (isOpen_lt continuous_const (continuous_fst.sub (continuous_rad.div_const 2))).inter
          (isOpen_lt continuous_rad continuous_const)
      have hOW : paperInY '' O ⊆ D.W := fun _ ⟨w, hw, hwe⟩ =>
        hwe ▸ D.spear_sub ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩
      have hOo' : IsOpen (D.ψ '' (paperInY '' O)) :=
        D.isOpen_image (E0Spear.isOpen_paperInY_image hOo) hOW
      have hxO : x ∈ O := ⟨by simp only [fcoord]; rw [hx1]; linarith [rad_nonneg x], hlt⟩
      have hzO : z ∈ D.ψ '' (paperInY '' O) := ⟨paperInY x, ⟨x, hxO, rfl⟩, hxe⟩
      obtain ⟨z', hz'O, hz'S, hz'U⟩ := mem_closure_iff.1 hz' _ hOo' hzO
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz'O
      exact hz'U (mem_iUnion.2 ⟨i, ⟨paperInY w, ⟨w, ⟨hw.1.le, hw.2.le⟩, rfl⟩, rfl⟩⟩)
    · have hxg : x ∈ graphSet D.G D.R := by
        refine ⟨by rw [heq]; exact D.pos, heq.le, ?_⟩
        simp only [height, heightAt]
        rw [rim_value D.rim heq, hx1, sub_self]
      exact Or.inr (mem_iUnion₂.2 ⟨i, hiF, ⟨paperInY x,
        ⟨x, D.mem_annulusGraph hxg (by rw [heq]; exact hρR i), rfl⟩, hxe⟩⟩)
  have hTcl : IsClosed T := by
    refine isClosed_of_closure_subset ?_
    rw [closure_union]
    exact union_subset hclos ((hBc.isClosed.closure_eq).le.trans subset_union_right)
  have hTc : IsCompact T :=
    (hK.union hBc).of_isClosed_subset hTcl (union_subset_union inter_subset_right le_rfl)
  have hTu : ∀ n ≥ N₀, pt (u n) ∈ T := by
    intro n hn
    have hnK : pt (u n) ∈ K := hNK n ((le_max_left _ _).trans hn)
    rcases hptS (u n) with h | h
    · exact Or.inl ⟨h, hnK⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      have hin : pt (u n) ∈ (Dat.D i).spearSet := (Dat.D i).cusp_subset_spearSet hi
      have hiF : i ∈ F := ⟨_, hin, hnK⟩
      obtain ⟨-, hxe⟩ := (Dat.D i).coord_mem hin
      exact Or.inr (mem_iUnion₂.2 ⟨i, hiF, ⟨paperInY _, ⟨_, (Dat.D i).mem_annulusGraph
        ((Dat.D i).coord_mem_graphSet hi) (hρu i hiF n hn hin), rfl⟩, hxe⟩⟩)
  -- a convergent subsequence
  obtain ⟨z, hzT, φ, hφ, hlim⟩ := hTc.tendsto_subseq (x := fun k => pt (u (N₀ + k)))
    (fun k => hTu _ (Nat.le_add_right _ _))
  have hzreg : z ∈ E0LM.e0RegM M := Dat.sigmaStar_subset_regM (hTS hzT)
  set z' : e0RegMFlat M := (⟨z, hzreg⟩ : E0LM.e0RegM M) with hz'
  have hz'S : z' ∈ Dat.sigmaStarReg := hTS hzT
  set ζ : ℕ → e0RegMFlat M := fun k =>
    ((Causal.Flat.InducedLengthSpace.toSubtype (u (N₀ + φ k)) : Dat.sigmaStarReg) : e0RegMFlat M)
    with hζ
  have hind : Topology.IsInducing (regVal M) := Topology.IsInducing.subtypeVal
  have h1 : Tendsto ζ atTop (𝓝 z') := hind.tendsto_nhds_iff.2 hlim
  have hlimS : Tendsto (fun k => (Causal.Flat.InducedLengthSpace.toSubtype (u (N₀ + φ k)) :
      Dat.sigmaStarReg)) atTop (𝓝 ⟨z', hz'S⟩) := by
    rw [tendsto_subtype_rng]
    exact h1
  have hlimX : Tendsto (fun k => u (N₀ + φ k)) atTop
      (𝓝 (Causal.Flat.InducedLengthSpace.toSubtype.symm ⟨z', hz'S⟩)) :=
    (hcont.tendsto _).comp hlimS
  exact ⟨_, tendsto_nhds_of_cauchySeq_of_subseq hu
    (Filter.tendsto_atTop_mono (fun k => Nat.le_add_left (φ k) N₀) hφ.tendsto_atTop) hlimX⟩

/-- **(G5), the bounded part**: the tail of a Cauchy sequence of `Σ*` lies in a compact set of `M`
(`exists_isCompact_of_cauchySeq_of` of `GXScaffold.BTZ.RegCompleteTail`, its hypotheses discharged
by the compact case `tendsto_of_cauchySeq_of_isCompact`, the `log r` estimate
`ofReal_abs_logRad_sub_le_edist` and the continuity of `Σ*` into `M`). -/
theorem LFSurgeryData.exists_isCompact_of_cauchySeq (hGH : (E0CBG.CE M).GloballyHyperbolic)
    {S : Set M} (hS : E0RegComplete.IsE0C1CompleteCauchy M S) (Dat : LFSurgeryData M S)
    (hsum : Summable fun i => (Dat.D i).R)
    {u : ℕ → Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg} (hu : CauchySeq u) :
    ∃ K : Set M, IsCompact K ∧ ∀ᶠ n in atTop, Dat.lenPt (u n) ∈ K := by
  have hL := Dat.isSpacelikeLipschitz_sigmaStar hS.reg
  exact Dat.exists_isCompact_of_cauchySeq_of hS.complete hS.continuous
    (fun {_} hv {_} hK hKv => Dat.tendsto_of_cauchySeq_of_isCompact
      (isClosed_of_isCauchySurface hGH hS.cauchy) hL hv hK hKv)
    (continuous_regVal.comp (Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype hL))
    (fun i => ⟨Dat.logRad i, fun z hz => by rw [LFSurgeryData.logRad, if_pos hz],
      fun a b => Dat.ofReal_abs_logRad_sub_le_edist i (Dat.D i).delta a b⟩)
    hsum hu

/-- **(G5) `Σ*` is complete for its induced length.** -/
theorem LFSurgeryData.completeSpace_sigmaStar (hGH : (E0CBG.CE M).GloballyHyperbolic)
    {S : Set M} (hS : E0RegComplete.IsE0C1CompleteCauchy M S) (Dat : LFSurgeryData M S)
    (hsum : Summable fun i => (Dat.D i).R) :
    CompleteSpace (Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) := by
  have hL := Dat.isSpacelikeLipschitz_sigmaStar hS.reg
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨K, hK, hKu⟩ := Dat.exists_isCompact_of_cauchySeq hGH hS hsum hu
  exact Dat.tendsto_of_cauchySeq_of_isCompact (isClosed_of_isCauchySurface hGH hS.cauchy) hL hu hK hKu

/-- **Thinning a locally finite family to summable radii.** -/
theorem LFSurgeryData.exists_summable (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hrim : RimC1 M S) (Dat : LFSurgeryData M S) :
    ∃ Dat' : LFSurgeryData M S, Summable fun i => (Dat'.D i).R := by
  haveI := Dat.countable
  haveI : Encodable Dat.ι := Encodable.ofCountable _
  obtain ⟨w, hw0, c, hwc, -⟩ := posSumOfEncodable one_pos Dat.ι
  have hsh : ∀ i, ∃ D' : SpearSurgeryDatum M S, D'.p = (Dat.D i).p ∧ D'.ψ = (Dat.D i).ψ ∧
      D'.v = (Dat.D i).v ∧ D'.R = min (w i) (Dat.D i).R := fun i =>
    (Dat.D i).exists_shrink hrim (lt_min (hw0 i) (Dat.D i).pos) (min_le_right _ _)
  choose D hDp hDψ hDv hDR using hsh
  have hsub : ∀ i, (D i).spearSet ⊆ (Dat.D i).spearSet := fun i => by
    show (D i).ψ '' E0Spear.spearY (D i).v (D i).R ⊆ _
    rw [hDψ, hDv, hDR]
    exact image_mono (image_mono (E0Spear.spear_mono le_rfl (min_le_right _ _)))
  refine ⟨⟨Dat.ι, Dat.countable, D, Dat.pt, fun i => ?_,
    fun i j hij => (Dat.disjoint hij).mono (hsub i) (hsub j),
    fun i => isClosed_image_spearY hGH (D i).isOpen (D i).spear_sub (D i).mor (D i).inj,
    Dat.locallyFinite.subset hsub, fun i => hrim (D i).R (D i).v (D i).W (D i).ψ
    (D i).τS (D i).pos (D i).isOpen (D i).spear_sub (D i).mor (D i).inj (D i).continuousOn
    (D i).shaft (D i).graph⟩, ?_⟩
  · obtain ⟨t, ht, h⟩ := Dat.pt_ray i
    exact ⟨t, ht, by rw [hDψ, hDv]; exact h⟩
  · refine Summable.of_nonneg_of_le (fun i => (D i).pos.le) (fun i => ?_) hwc.summable
    show (D i).R ≤ w i
    rw [hDR]; exact min_le_left _ _

/-- **`Reg M` is Cauchy-complete** (btz `prop:reg_complete`, l.1571). -/
theorem regM_isCauchyComplete_of_lf (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : E0RegComplete.IsE0C1CompleteCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M) :
    Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) := by
  obtain ⟨Dat₀⟩ := exists_lfSurgeryData hGH hS hmax
  obtain ⟨Dat, hsum⟩ := Dat₀.exists_summable hGH hS.rim
  have hL := Dat.isSpacelikeLipschitz_sigmaStar hS.reg
  exact ⟨Dat.sigmaStarReg, Dat.isCauchySurface_sigmaStar hGH hS.cauchy, hL,
    Dat.completeSpace_sigmaStar hGH hS hsum,
    Causal.Flat.Cla.continuous_inducedLengthSpace_toSubtype hL⟩

end E0SpearFamily

end GX
