import GXScaffold.BTZ.C1SpacelikeDev

/-!
# btz Lemma 2.8(ii) for graphs spacelike Lipschitz across the rim

`btzlem:surface_complete` — `BTZ_1.tex:781` (statement l.781–792; proof of (ii) l.823–850).
Item (ii) only, in a spacelike-Lipschitz reading that can be met, for `𝔼₀` (unmarked: see SCOPE).

> \begin{lemou} Let $\Sigma^*$ be the graph of some piecewise smooth map
> $\tau_\Sigma: \mathbb D_R^*\rightarrow \RR$ with $R>0$; then: […]
> \item If $\Sigma$ is spacelike and complete then,
> $$ \lim_{(\r,\theta) \rightarrow 0}\tau_\Sigma(\r,\theta) = +\infty$$ (l.781–790)

The strict `GX.E0Surgery.lem_surface_complete_two_lip` assumes
`Causal.Flat.SpacelikeDevelopment (graphDev g R)`, which never holds for `R > 0`
(`GX.E0Surgery.spacelikeDevelopment_graphDev_iff`, `GXScaffold.BTZ.C1SpacelikeDev`: the rim `r = R`
is a boundary). Its proof uses that hypothesis only through two consequences, both meaningful at
the rim:

* `UnifSpacelike g R`: near each point of the strip the development is uniformly spacelike,
  `κ ‖ΔF‖² ≤ minkQ ΔF` (`SpacelikeDevelopment.exists_uniform_nhds`);
* the pulled-length topology is finer than the strip's
  (`Causal.Flat.SpacelikeDevelopment.continuous_toSpace`).

`lem_surface_complete_two_unif` is the strict proof, verbatim, over these two hypotheses.
`lem_surface_complete_two_lipOn` is the reading the strict theorem meant: the development is a
spacelike development over an open set `Ω ⊇ (0, R] × ℝ` (`Σ` extends a little across its rim as a
spacelike Lipschitz surface); both consequences then hold on the strip (`unifSpacelike_of_graphDevOn`,
the uniform estimate restricts; `continuous_toSpace_of_graphDevOn`, the pulled distance of the strip
dominates that of `Ω`, since a path of the strip is a path of `Ω` of the same length). It is
**not vacuous**: Lemma 2.6(ii)'s cusp meets every hypothesis with `Ω = {r > 0}`
(`cusp_lipOn_hyps`). A `C¹` graph with `δ > 0` on an open `Ω ⊇ (0, R] × ℝ` is a case
(`lem_surface_complete_two_of_open`, through `spacelikeDevelopment_graphDevOn`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `τ_Σ : 𝔻_R^* → ℝ`, `R > 0` | ✓ `g : ℝ × ℝ → ℝ`, `2π`-periodic in `θ`, `0 < R`, the strict reading |
| « piecewise smooth » | ⚠ weakened: none (`lipOn`); `C¹` on an open neighbourhood of the strip (`of_open`) |
| « spacelike » | ⚠ read: `SpacelikeDevelopment (graphDevOn g Ω)` for an open `Ω ⊇ (0, R] × ℝ` (spacelike Lipschitz across the rim); or, weaker, `UnifSpacelike g R` with the topology hypothesis (`unif`) |
| « complete » | ✓ `CompleteSpace (Causal.Flat.PulledLength (graphDev g R))`, the strict reading |
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |

## SCOPE (disclosed)

* Item (ii) only. The row stays `partial` on T-btz-scope and on the reading of « spacelike » for a
  surface with boundary: the paper's `Σ` over `𝔻_R^*` has the rim circle `r = R` as boundary, and
  the readings here ask `Σ` to extend across it (`lipOn`) or ask the two local facts directly
  (`unif`).
* The strict `lem_surface_complete_two` (`C¹` on the closed strip only) is NOT derived from
  these: a `C¹` graph on `(0, R] × ℝ` need not extend across the rim as a spacelike graph without a
  Whitney-type extension, which is not built; `lem_surface_complete_two_of_open` covers the graphs
  that are `C¹` with `δ > 0` on an open neighbourhood of the strip.
* 0 `sorry`; standard axioms only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; imports
`GXScaffold.BTZ.C1SpacelikeDev` (hence the strict `GX.BTZ.SurfaceCompleteLip`). Written by
T-btz-c1-spacelike-development (2026-11-28).
-/

namespace GX

open Set Filter Topology Function MeasureTheory
open scoped Real NNReal

namespace E0Surgery

variable {g : ℝ × ℝ → ℝ} {R : ℝ}

/-- **The development is uniformly spacelike near each point of the strip**: the consequence of
`SpacelikeDevelopment` (`SpacelikeDevelopment.exists_uniform_nhds`) that the proof of Lemma 2.8(ii)
uses, meaningful at the rim. -/
def UnifSpacelike (g : ℝ × ℝ → ℝ) (R : ℝ) : Prop :=
  ∀ x : Strip R, ∃ W ∈ 𝓝 x, ∃ κ > (0 : ℝ), ∀ a ∈ W, ∀ b ∈ W,
    κ * ‖graphDev g R a - graphDev g R b‖ ^ 2 ≤
      Causal.Flat.minkQ (graphDev g R a - graphDev g R b)

/-- **Step (1), uniform form**: a graph whose development is uniformly spacelike near each point of
the strip is locally Lipschitz on the strip (`locallyLipschitzOn_of_spacelikeDevelopment` with
`UnifSpacelike` in place of `SpacelikeDevelopment`). -/
theorem locallyLipschitzOn_of_unif (hU : UnifSpacelike g R) :
    LocallyLipschitzOn (stripSet R) g := by
  intro p hp
  set x : Strip R := ⟨p, hp⟩
  obtain ⟨W, hW, κ, hκ, hWκ⟩ := hU x
  have hW' : Subtype.val '' W ∈ 𝓝[stripSet R] p :=
    mem_nhds_subtype_iff_nhdsWithin (s := stripSet R) (a := x).1 hW
  obtain ⟨K2, T2, hT2, hK2⟩ :=
    (show ContDiff ℝ 1 (fun q : ℝ × ℝ => q.1 * q.2) by fun_prop).locallyLipschitz p
  obtain ⟨K3, T3, hT3, hK3⟩ :=
    (show ContDiff ℝ 1 (fun q : ℝ × ℝ => 1 / 2 * q.1 * q.2 ^ 2) by fun_prop).locallyLipschitz p
  set C : ℝ := (1 + 3 / κ) * (1 + K2) + K3 with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C.toNNReal, Subtype.val '' W ∩ T2 ∩ T3,
    inter_mem (inter_mem hW' (mem_nhdsWithin_of_mem_nhds hT2)) (mem_nhdsWithin_of_mem_nhds hT3),
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  obtain ⟨⟨⟨a', ha'W, rfl⟩, ha2⟩, ha3⟩ := ha
  obtain ⟨⟨⟨b', hb'W, rfl⟩, hb2⟩, hb3⟩ := hb
  have hk := hWκ a' ha'W b' hb'W
  set z := graphDev g R a' - graphDev g R b' with hz
  have hz1 : |z.1| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le z
  have hzQ : Causal.Flat.minkQ z = -2 * z.1 * ((a' : ℝ × ℝ).1 - (b' : ℝ × ℝ).1) +
      ((a' : ℝ × ℝ).1 - (b' : ℝ × ℝ).1) ^ 2 +
      ((a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 - (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2) ^ 2 :=
    minkQ_btzPaperDev_sub (graphMap g a') (graphMap g b')
  have hzf : z.1 = (g a' - g b') + (1 / 2 * (a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 ^ 2 -
      1 / 2 * (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2 ^ 2) :=
    fst_btzPaperDev_sub (graphMap g a') (graphMap g b')
  have hk' : κ * z.1 ^ 2 ≤ -2 * z.1 * ((a' : ℝ × ℝ).1 - (b' : ℝ × ℝ).1) +
      ((a' : ℝ × ℝ).1 - (b' : ℝ × ℝ).1) ^ 2 +
      ((a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 - (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2) ^ 2 := by
    rw [← hzQ]
    refine le_trans ?_ hk
    have : z.1 ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz1 2
    exact mul_le_mul_of_nonneg_left this hκ.le
  have ht := abs_le_of_uniform hκ hk'
  set dab := dist (a' : ℝ × ℝ) (b' : ℝ × ℝ) with hdab
  have hr : |(a' : ℝ × ℝ).1 - (b' : ℝ × ℝ).1| ≤ dab := by
    rw [← Real.dist_eq, hdab, Prod.dist_eq]; exact le_max_left _ _
  have h2 : |(a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 - (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2| ≤ K2 * dab := by
    have := hK2.dist_le_mul _ ha2 _ hb2; rwa [Real.dist_eq] at this
  have h3 : |1 / 2 * (a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 ^ 2 -
      1 / 2 * (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2 ^ 2| ≤ K3 * dab := by
    have := hK3.dist_le_mul _ ha3 _ hb3; rwa [Real.dist_eq] at this
  have hd0 : 0 ≤ dab := dist_nonneg
  have hgab : g a' - g b' = z.1 - (1 / 2 * (a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 ^ 2 -
      1 / 2 * (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2 ^ 2) := by rw [hzf]; ring
  rw [Real.dist_eq, Real.coe_toNNReal _ hC0, hgab]
  refine (abs_sub _ _).trans ?_
  have hκ3 : 0 ≤ 1 + 3 / κ := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add hr h2) hκ3
  calc |z.1| + |1 / 2 * (a' : ℝ × ℝ).1 * (a' : ℝ × ℝ).2 ^ 2 -
        1 / 2 * (b' : ℝ × ℝ).1 * (b' : ℝ × ℝ).2 ^ 2|
      ≤ (1 + 3 / κ) * (dab + K2 * dab) + K3 * dab := add_le_add (ht.trans this) h3
    _ = C * dab := by rw [hC]; ring


/-- **The length of a straight piece, uniform form** (`edist_le_seg_lip` with `UnifSpacelike`;
B21 l.842–848; the strict `edist_le_seg`
without `C¹`): from `a` to `b` with `r_b − r_a ≥ r_b/2` and `|θ_b − θ_a| ≤ π`, the pulled distance
is at most `(1 + 2π²)(r_b − r_a) − (τ(b) − τ(a))`, which is nonnegative. -/
theorem edist_le_seg_unif (hU : UnifSpacelike g R)
    (a b : Causal.Flat.PulledLength (graphDev g R))
    (hab : (Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 / 2 ≤
      (Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1)
    (hθ : |(Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).2 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).2| ≤ π) :
    0 ≤ (1 + 2 * π ^ 2) * ((Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1) -
        (g (Causal.Flat.PulledLength.toSpace (graphDev g R) b) -
          g (Causal.Flat.PulledLength.toSpace (graphDev g R) a)) ∧
    edist a b ≤ ENNReal.ofReal ((1 + 2 * π ^ 2) *
      ((Causal.Flat.PulledLength.toSpace (graphDev g R) b : ℝ × ℝ).1 -
        (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1) -
        (g (Causal.Flat.PulledLength.toSpace (graphDev g R) b) -
          g (Causal.Flat.PulledLength.toSpace (graphDev g R) a))) := by
  set x' := Causal.Flat.PulledLength.toSpace (graphDev g R) a
  set y' := Causal.Flat.PulledLength.toSpace (graphDev g R) b
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
  change ⨅ γ : Path x' y', Causal.Flat.pathLength _ γ ≤ _
  refine (iInf_le _ σ).trans ?_
  rw [Causal.Flat.pathLength_of_isLocLip _ hloc, ← hTi,
    ofReal_integral_eq_lintegral_ofReal hIi (hae.mono fun t h => h.2)]
  unfold Causal.Flat.localLength
  exact MeasureTheory.lintegral_mono_ae (hae.mono fun t h => h.1)

/-- **B21 Lemma 2.8(ii), uniform form** (`btzlem:surface_complete`, l.786–790, proof
l.823–850): a `2π`-periodic `g` on the strip whose development is uniformly spacelike near each
point, whose pulled-length topology is finer than the strip's, and whose pulled length is complete,
goes to `+∞` at the axis. The proof of `lem_surface_complete_two_lip`, verbatim, with the two
consequences of `SpacelikeDevelopment` it uses as hypotheses. -/
theorem lem_surface_complete_two_unif {g : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ))
    (hU : UnifSpacelike g R) (hTop : Continuous ⇑(Causal.Flat.PulledLength.toSpace (graphDev g R)))
    (hcomp : CompleteSpace (Causal.Flat.PulledLength (graphDev g R))) :
    Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop := by
  rw [tendsto_atTop]
  intro A
  by_contra hA
  rw [Filter.not_eventually] at hA
  have hfreq : ∀ ε : ℝ, ∃ p : ℝ × ℝ, 0 < ε → 0 < p.1 ∧ p.1 < ε ∧ g p < A := by
    intro ε
    by_cases hε : 0 < ε
    · have hmem : {p : ℝ × ℝ | p.1 ∈ Ioo 0 ε} ∈ comap Prod.fst (𝓝[>] (0 : ℝ)) :=
        preimage_mem_comap (Ioo_mem_nhdsGT hε)
      obtain ⟨p, hp1, hp2⟩ := (hA.and_eventually hmem).exists
      exact ⟨p, fun _ => ⟨hp2.1, hp2.2, not_le.1 hp1⟩⟩
    · exact ⟨0, fun h => absurd h hε⟩
  choose P hP using hfreq
  -- the sequence, realigned (l.828–834)
  set step : ℝ × ℝ → ℝ × ℝ := fun q =>
    ((P (q.1 / 2)).1, q.2 + toIcoMod Real.two_pi_pos (-π) ((P (q.1 / 2)).2 - q.2)) with hstep
  set u : ℕ → ℝ × ℝ := fun n => step^[n] (P R) with hu
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
  have hinv : ∀ n, 0 < (u n).1 ∧ (u n).1 < R ∧ g (u n) < A := by
    intro n
    induction n with
    | zero => exact hP R hR
    | succ n ih =>
      rw [husucc]
      obtain ⟨h1, h2, h3⟩ := hP ((u n).1 / 2) (half_pos ih.1)
      refine ⟨h1, by linarith [ih.2.1], ?_⟩
      rw [hstep_g]; exact h3
  have hhalf : ∀ n, (u (n + 1)).1 < (u n).1 / 2 := by
    intro n; rw [husucc]; exact (hP ((u n).1 / 2) (half_pos (hinv n).1)).2.1
  -- the points of the pulled length
  set w : ℕ → Causal.Flat.PulledLength (graphDev g R) := fun n =>
    (Causal.Flat.PulledLength.toSpace (graphDev g R)).symm ⟨u n, (hinv n).1, (hinv n).2.1.le⟩
    with hw
  have hwc : ∀ n, (Causal.Flat.PulledLength.toSpace (graphDev g R) (w n) : ℝ × ℝ) = u n :=
    fun n => rfl
  set T : ℕ → ℝ := fun n => (1 + 2 * π ^ 2) * ((u n).1 - (u (n + 1)).1) - (g (u n) - g (u (n + 1)))
    with hT
  have hseg : ∀ n, 0 ≤ T n ∧ edist (w (n + 1)) (w n) ≤ ENNReal.ofReal (T n) := by
    intro n
    have h := edist_le_seg_unif hU (w (n + 1)) (w n)
      (by rw [hwc, hwc]; linarith [hhalf n])
      (by rw [hwc, hwc, husucc, abs_sub_comm]; exact hstep_θ (u n))
    rw [hwc, hwc] at h
    exact h
  -- the broken line has finite length (l.842–846, telescoping)
  have hsum : Summable T := by
    refine summable_of_sum_range_le (c := (1 + 2 * π ^ 2) * R - g (u 0) + A)
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
  have hcs : CauchySeq w := by
    refine cauchySeq_of_edist_le_of_tsum_ne_top (fun n => ENNReal.ofReal (T n))
      (fun n => by rw [edist_comm]; exact (hseg n).2) ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hseg n).1) hsum]
    exact ENNReal.ofReal_ne_top
  -- completeness: a limit, at positive radius; the pulled topology is finer than the strip's
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  have hlim : Tendsto (fun n => (u n).1) atTop
      (𝓝 (Causal.Flat.PulledLength.toSpace (graphDev g R) a : ℝ × ℝ).1) :=
    ((continuous_fst.comp continuous_subtype_val).comp
      hTop).continuousAt.tendsto.comp ha
  have hgeom : ∀ n, (u n).1 ≤ R * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simpa using (hinv 0).2.1.le
    | succ n ih => rw [pow_succ]; nlinarith [hhalf n]
  have hto0 : Tendsto (fun n => R * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul R
  have hu0 : Tendsto (fun n => (u n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => (hinv n).1.le) hgeom
  have heq := tendsto_nhds_unique hlim hu0
  exact absurd heq (Causal.Flat.PulledLength.toSpace (graphDev g R) a).2.1.ne'


/-! ### From a spacelike development over an open neighbourhood of the strip -/

/-- The strip inside `Ω`. -/
def stripIncl {Ω : Set (ℝ × ℝ)} (hsub : stripSet R ⊆ Ω) (x : Strip R) : Ω := ⟨x.1, hsub x.2⟩

theorem continuous_stripIncl {Ω : Set (ℝ × ℝ)} (hsub : stripSet R ⊆ Ω) :
    Continuous (stripIncl hsub) :=
  continuous_subtype_val.subtype_mk _

theorem unifSpacelike_of_graphDevOn {Ω : Set (ℝ × ℝ)} (hsub : stripSet R ⊆ Ω)
    (hF : Causal.Flat.SpacelikeDevelopment (graphDevOn g Ω)) : UnifSpacelike g R := by
  intro x
  obtain ⟨W, hW, κ, hκ, hWκ⟩ := SpacelikeDevelopment.exists_uniform_nhds hF (stripIncl hsub x)
  have key : ∀ a : Strip R, graphDevOn g Ω (stripIncl hsub a) = graphDev g R a := fun _ => rfl
  refine ⟨stripIncl hsub ⁻¹' W, (continuous_stripIncl hsub).continuousAt.preimage_mem_nhds hW, κ,
    hκ, fun a ha b hb => ?_⟩
  have h := hWκ _ ha _ hb
  rwa [key, key] at h

/-- **The pulled distance of the strip dominates that of `Ω`**: a path of the strip is a path of
`Ω` with the same developed curve. -/
theorem edist_stripIncl_le {Ω : Set (ℝ × ℝ)} (hsub : stripSet R ⊆ Ω)
    (a b : Causal.Flat.PulledLength (graphDev g R)) :
    edist ((Causal.Flat.PulledLength.toSpace (graphDevOn g Ω)).symm
        (stripIncl hsub (Causal.Flat.PulledLength.toSpace (graphDev g R) a)))
      ((Causal.Flat.PulledLength.toSpace (graphDevOn g Ω)).symm
        (stripIncl hsub (Causal.Flat.PulledLength.toSpace (graphDev g R) b))) ≤ edist a b := by
  change ⨅ γ : Path _ _, Causal.Flat.pathLength _ γ ≤
    ⨅ γ : Path (Causal.Flat.PulledLength.toSpace (graphDev g R) a)
      (Causal.Flat.PulledLength.toSpace (graphDev g R) b), Causal.Flat.pathLength _ γ
  exact le_iInf fun γ => (iInf_le _ (γ.map (continuous_stripIncl hsub))).trans_eq rfl

theorem continuous_toSpace_of_graphDevOn {Ω : Set (ℝ × ℝ)} (hsub : stripSet R ⊆ Ω)
    (hF : Causal.Flat.SpacelikeDevelopment (graphDevOn g Ω)) :
    Continuous ⇑(Causal.Flat.PulledLength.toSpace (graphDev g R)) := by
  set j : Causal.Flat.PulledLength (graphDev g R) → Causal.Flat.PulledLength (graphDevOn g Ω) :=
    fun a => (Causal.Flat.PulledLength.toSpace (graphDevOn g Ω)).symm
      (stripIncl hsub (Causal.Flat.PulledLength.toSpace (graphDev g R) a)) with hj
  have hjL : LipschitzWith 1 j :=
    LipschitzWith.of_edist_le fun a b => edist_stripIncl_le hsub a b
  have hc : Continuous fun a => ((Causal.Flat.PulledLength.toSpace (graphDevOn g Ω) (j a) : Ω) :
      ℝ × ℝ) :=
    continuous_subtype_val.comp (hF.continuous_toSpace.comp hjL.continuous)
  exact hc.subtype_mk _

/-- **B21 Lemma 2.8(ii), for a graph spacelike Lipschitz across its rim** (`btzlem:surface_complete`,
l.786–790, proof l.823–850): a `2π`-periodic `g` whose development is a spacelike development over
an open `Ω ⊇ (0, R] × ℝ`, with complete pulled length over the strip, goes to `+∞` at the axis. -/
theorem lem_surface_complete_two_lipOn {Ω : Set (ℝ × ℝ)} (hR : 0 < R)
    (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) (hsub : stripSet R ⊆ Ω)
    (hF : Causal.Flat.SpacelikeDevelopment (graphDevOn g Ω))
    (hcomp : CompleteSpace (Causal.Flat.PulledLength (graphDev g R))) :
    Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop :=
  lem_surface_complete_two_unif hR hper (unifSpacelike_of_graphDevOn hsub hF)
    (continuous_toSpace_of_graphDevOn hsub hF) hcomp

/-- **The `C¹` case on an open neighbourhood of the strip**: `g` `C¹` with `δ > 0` (Lemma 2.7) on
an open `Ω ⊆ {r > 0}` containing `(0, R] × ℝ`, periodic, complete: `g → +∞` at the axis. -/
theorem lem_surface_complete_two_of_open {Ω : Set (ℝ × ℝ)} (hR : 0 < R)
    (hper : ∀ r θ, g (r, θ + 2 * π) = g (r, θ)) (hΩ : IsOpen Ω) (hsub : stripSet R ⊆ Ω)
    (hpos : ∀ p ∈ Ω, 0 < p.1) (hC1 : ContDiffOn ℝ 1 g Ω)
    (hδ : ∀ p ∈ Ω, ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.1)
    (hcomp : CompleteSpace (Causal.Flat.PulledLength (graphDev g R))) :
    Tendsto g (comap Prod.fst (𝓝[>] 0)) atTop :=
  lem_surface_complete_two_lipOn hR hper hsub (spacelikeDevelopment_graphDevOn hΩ hpos hC1 hδ) hcomp

/-- **Non-vacuity**: Lemma 2.6(ii)'s cusp meets every hypothesis of `lem_surface_complete_two_lipOn`
(with `Ω = {r > 0}`), and its conclusion. -/
theorem cusp_lipOn_hyps {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) (hR : 0 < R) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ (∀ r θ, τ (r, θ + 2 * π) = τ (r, θ)) ∧
      stripSet R ⊆ {p : ℝ × ℝ | 0 < p.1} ∧
      Causal.Flat.SpacelikeDevelopment (graphDevOn τ {p | 0 < p.1}) ∧
      CompleteSpace (Causal.Flat.PulledLength (graphDev τ R)) ∧
      Tendsto τ (comap Prod.fst (𝓝[>] 0)) atTop := by
  obtain ⟨τ, hrim, hsg, hF, hcomp, -, -⟩ := cusp_spacelikeDevelopment hn hτ hper hpos hR
  have hsub : stripSet R ⊆ {p : ℝ × ℝ | 0 < p.1} := fun p hp => hp.1
  exact ⟨τ, hrim, hsg.periodic, hsub, hF, hcomp,
    lem_surface_complete_two_lipOn hR hsg.periodic hsub hF hcomp⟩

end E0Surgery

end GX
