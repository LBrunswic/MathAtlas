import GX.BTZ.RegCompleteCauchy
import GX.BTZ.RegCompleteTail

/-!
# `GX.BTZ.RegCompleteLength` — `Σ*` of a locally finite spear family: spacelike Lipschitz, Lemma 2.8's `log r` estimate, and completeness (btz § 5.4)

Targets T-btz-reg-complete-length and T-btz-reg-complete-tail. Paper `btz`
(`papers/btz/legacy/labeled/BTZ_1.tex`). Row (unmarked, partial: `𝔼₀`-scoped and the readings
below; this file is step (3) of `btzprop:reg_complete`'s Cauchy-completeness, and
`GX.E0RegComplete.regM_isCauchyComplete_of_complete` in `GX/BTZ/RegComplete.lean` is
`regM_isCauchyComplete_of_lf`):

* `btzprop:reg_complete` — `BTZ_1.tex:1566–1569`, proof l.1570–1576: « the proof of
  Cauchy-completeness of Proposition prop:abs_max applies as is » (l.1571), which is B21 l.1093.

> The surface $\Sigma^*$ is metrically complete and, by Remark \ref{rem:curve_spear} and Corollary
> \ref{cor:intersect} applied to the in each spear neighborhood, a Cauchy-surface of $M^*$. (l.1093)

> Global hyperbolicity follows from Remark \ref{rem:reg_GH} and the proof of Cauchy-complete\-ness
> of Proposition \ref{prop:abs_max} applies as is. (l.1571)

## What is proved (no `sorry`; standard axioms only)

* `LFSurgeryData.isSpacelikeLipschitz_sigmaStar` (G4): `Σ*` of a locally finite family is
  spacelike Lipschitz in the flat charts of `Reg M`, from `S` spacelike Lipschitz only. Read off
  `E0Surgery.LFSpears.isSpacelikeLipschitz_sigmaStar` (`GX.BTZ.Surgery`, where (G4a) at the cusps
  is stated once for a locally finite family and the finite `SurgeryData` derives it too) through
  `LFSurgeryData.toLFSpears`.
* `LFSurgeryData.ofReal_abs_logRad_sub_le_edist`: Lemma 2.8's `log r` estimate (B21 l.799–806) on
  `Σ*`, spear by spear — the clamped log-radius of each cusp is `1`-Lipschitz for the induced
  length; read off `E0Surgery.LFSpears.ofReal_abs_logRad_sub_le_edist` likewise
  (`logRad_toLFSpears` is `rfl`).
* `LFSurgeryData.tendsto_of_cauchySeq_of_isCompact`: a Cauchy sequence of `Σ*` whose tail lies in
  a compact set of `M` converges (the strict compact proof localised to the finitely many spears
  the compact set meets).
* `LFSurgeryData.exists_summable`: the spears can be thinned to summable radii.
* `isClosed_of_isCauchySurface`: a Cauchy surface of `M` is closed, the general
  `E0LM.sfa_isClosed_cauchy` (`GX.BTZ.LocalModel`) for `CE M`.
* `LFSurgeryData.exists_isCompact_of_cauchySeq`: the tail of a Cauchy sequence of `Σ*` lies in a
  compact set of `M`, for spears of summable radii (`GX.BTZ.RegCompleteTail`'s
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
`GX.BTZ.RegCompleteTail` by thinning the spears to summable radii and replacing, spear by
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

/-! ### (G4) and Lemma 2.8's `log r` estimate, read off `E0Surgery.LFSpears`

`Σ*` is spacelike Lipschitz at the cusps and the clamped log-radius is `1`-Lipschitz for the
induced length: stated once in the strict `GX.BTZ.Surgery` over `E0Surgery.LFSpears` (a locally
finite family of disjoint closed spears), read here through `LFSurgeryData.toLFSpears`
(`sigmaStar_toLFSpears` is `rfl`), as the finite `SurgeryData` reads them through
`SurgeryData.toLFSpears`. -/

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.isSpacelikeLipschitzAt_cusp_interior` for the locally finite family. -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp_interior {S : Set M} (Dat : LFSurgeryData M S)
    (i : Dat.ι) {y : e0RegMFlat M} {x : E0} (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R)
    (hxR : rad x < (Dat.D i).R) (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y :=
  Dat.toLFSpears.isSpacelikeLipschitzAt_cusp_interior i hx hxR hy

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.isSpacelikeLipschitzAt_cusp_rim` for the locally finite family. -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp_rim {S : Set M} (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M} {x : E0}
    (hx : x ∈ graphSet (Dat.D i).G (Dat.D i).R) (hxR : rad x = (Dat.D i).R)
    (hy : regVal M y = (Dat.D i).ψ (paperInY x)) :
    IsSpacelikeLipschitzAt Dat.sigmaStarReg y :=
  Dat.toLFSpears.isSpacelikeLipschitzAt_cusp_rim hSreg i hx hxR hy

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.isSpacelikeLipschitzAt_cusp` for the locally finite family. -/
theorem LFSurgeryData.isSpacelikeLipschitzAt_cusp {S : Set M}
    (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) (i : Dat.ι) {y : e0RegMFlat M}
    (hy : regVal M y ∈ (Dat.D i).cusp) : IsSpacelikeLipschitzAt Dat.sigmaStarReg y :=
  Dat.toLFSpears.isSpacelikeLipschitzAt_cusp hSreg i hy

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.isSpacelikeLipschitz_sigmaStar` for the locally finite family. -/
theorem LFSurgeryData.isSpacelikeLipschitz_sigmaStar {S : Set M}
    (hSreg : Causal.Flat.IsSpacelikeLipschitz 2 (regSet M S))
    (Dat : LFSurgeryData M S) : Causal.Flat.IsSpacelikeLipschitz 2 Dat.sigmaStarReg :=
  Dat.toLFSpears.isSpacelikeLipschitz_sigmaStar hSreg

open Classical in
/-- **The clamped log-radius of the `i`-th cusp** of the locally finite family (the body of
`E0Surgery.LFSpears.logRad`): `log (min r (R/2))` in the spear, `log (R/2)` off it. -/
noncomputable def LFSurgeryData.logRad {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι) (z : M) : ℝ :=
  if z ∈ (Dat.D i).spearSet then Real.log (min (rad ((Dat.D i).coord z)) ((Dat.D i).R / 2))
  else Real.log ((Dat.D i).R / 2)

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- The clamped log-radius is the one of `toLFSpears`. -/
theorem LFSurgeryData.logRad_toLFSpears {S : Set M} (Dat : LFSurgeryData M S) :
    Dat.toLFSpears.logRad = Dat.logRad := rfl

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] [HasGroupoid M e0Groupoid] in
/-- `E0Surgery.LFSpears.logRad_le` for the locally finite family. -/
theorem LFSurgeryData.logRad_le {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι) {z : M}
    (hz : z ∈ Dat.sigmaStar) : Dat.logRad i z ≤ Real.log ((Dat.D i).R / 2) :=
  Dat.toLFSpears.logRad_le i hz

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.abs_deriv_logRad_le` for the locally finite family. -/
theorem LFSurgeryData.abs_deriv_logRad_le {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    {c : ℝ → e0RegMFlat M} {t : ℝ} (hc : ContinuousAt c t)
    (hcS : ∀ᶠ s in 𝓝 t, c s ∈ Dat.sigmaStarReg)
    {e₀ : OpenPartialHomeomorph (e0RegMFlat M) (Causal.Minkowski 2)}
    (he₀ : e₀ ∈ atlas (Causal.Minkowski 2) (e0RegMFlat M)) (hct : c t ∈ e₀.source)
    {v : Causal.Minkowski 2} (hv : HasDerivAt (fun s => e₀ (c s)) v t) :
    |deriv (fun s => Dat.logRad i (regVal M (c s))) t| ≤ Real.sqrt (Causal.Flat.minkQ v) :=
  Dat.toLFSpears.abs_deriv_logRad_le i hδ hc hcS he₀ hct hv

omit [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.eventually_logRad_const` for the locally finite family. -/
theorem LFSurgeryData.eventually_logRad_const {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {z₀ : M} (h : z₀ ∉ (Dat.D i).spearSet ∨
      (z₀ ∈ (Dat.D i).spearSet ∧ (Dat.D i).R / 2 < rad ((Dat.D i).coord z₀))) :
    ∀ᶠ z in 𝓝 z₀, Dat.logRad i z = Real.log ((Dat.D i).R / 2) :=
  Dat.toLFSpears.eventually_logRad_const i h

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.eventually_logRad_formula` for the locally finite family. -/
theorem LFSurgeryData.eventually_logRad_formula {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {z₀ : e0RegMFlat M} (hin : regVal M z₀ ∈ (Dat.D i).spearSet)
    (hr0 : 0 < rad ((Dat.D i).coord (regVal M z₀)))
    (hrR : rad ((Dat.D i).coord (regVal M z₀)) < (Dat.D i).R)
    (hfv : (Dat.D i).v < fcoord ((Dat.D i).coord (regVal M z₀))) :
    ∃ g : Causal.Flat.isom 2, (∀ᶠ z in 𝓝 z₀, z ∈ (chartAt (Causal.Minkowski 2) z₀).source ∧
      Dat.logRad i (regVal M z) =
        Real.log (min (chartNull g (chartAt (Causal.Minkowski 2) z₀ z)).2.1 ((Dat.D i).R / 2))) ∧
      (chartNull g (chartAt (Causal.Minkowski 2) z₀ z₀)).2.1 = rad ((Dat.D i).coord (regVal M z₀)) :=
  Dat.toLFSpears.eventually_logRad_formula i hin hr0 hrR hfv

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.exists_lipschitzOnWith_logRad` for the locally finite family. -/
theorem LFSurgeryData.exists_lipschitzOnWith_logRad {S : Set M} (Dat : LFSurgeryData M S) (i : Dat.ι)
    {a b : Dat.sigmaStarReg} (γ : Path a b)
    (hL : Causal.Flat.IsLocLip (Causal.Flat.chartSys 2 Dat.sigmaStarReg) γ.extend) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ K : NNReal, LipschitzOnWith K
      (fun t => Dat.logRad i (regVal M ((γ.extend t : Dat.sigmaStarReg) : e0RegMFlat M)))
      (Icc (t₀ - ε) (t₀ + ε)) :=
  Dat.toLFSpears.exists_lipschitzOnWith_logRad i γ hL t₀

omit [SecondCountableTopology M] in
/-- `E0Surgery.LFSpears.ofReal_abs_logRad_sub_le_edist` for the locally finite family. -/
theorem LFSurgeryData.ofReal_abs_logRad_sub_le_edist {S : Set M} (Dat : LFSurgeryData M S)
    (i : Dat.ι)
    (hδ : ∀ q : ℝ × ℝ, 0 < q.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (Dat.D i).G L q ∧
      1 / q.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) q.1)
    (a b : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) :
    ENNReal.ofReal |Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype b : Dat.sigmaStarReg) : e0RegMFlat M)) -
      Dat.logRad i (regVal M
        ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M))| ≤
      edist a b :=
  Dat.toLFSpears.ofReal_abs_logRad_sub_le_edist i hδ a b

/-! ### (G5) completeness -/

/-- The point of `M` under a point of the length space of `Σ*`. -/
noncomputable def LFSurgeryData.lenPt {S : Set M} (Dat : LFSurgeryData M S)
    (a : Causal.Flat.InducedLengthSpace 2 Dat.sigmaStarReg) : M :=
  regVal M ((Causal.Flat.InducedLengthSpace.toSubtype a : Dat.sigmaStarReg) : e0RegMFlat M)

/-- A Cauchy surface of a globally hyperbolic `𝔼₀`-manifold is closed (`S = J⁺(S) ∩ J⁻(S)`): the
general `E0LM.sfa_isClosed_cauchy` (`GX.BTZ.LocalModel`), for `CE M`. -/
theorem isClosed_of_isCauchySurface (hGH : (E0CBG.CE M).GloballyHyperbolic) {S : Set M}
    (hS : (E0CBG.CE M).IsCauchySurface S) : IsClosed S :=
  E0LM.sfa_isClosed_cauchy
    (E0LM.e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (E0LM.e0_globalBTZ M)) hGH
    (E0LM.e0_curvesExtend hGH) hS

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
(`exists_isCompact_of_cauchySeq_of` of `GX.BTZ.RegCompleteTail`, its hypotheses discharged
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
