import GX.BTZ.SurfaceCompleteLip

/-!
# btz Lemma 2.8: when a graph over the strip has a spacelike development

`btzlem:surface_complete` — `BTZ_1.tex:781` (statement l.781–792; proof of (ii) l.823–850), the
bridge between its strict form `GX.E0Surgery.lem_surface_complete_two` (`C¹`, `δ > 0`) and its
Lipschitz form `GX.E0Surgery.lem_surface_complete_two_lip` (hypothesis
`Causal.Flat.SpacelikeDevelopment (graphDev g R)`). Unmarked: see SCOPE.

> \begin{lemou} Let $\Sigma^*$ be the graph of some piecewise smooth map
> $\tau_\Sigma: \mathbb D_R^*\rightarrow \RR$ with $R>0$; then: […]
> \item If $\Sigma$ is spacelike and complete then,
> $$ \lim_{(\r,\theta) \rightarrow 0}\tau_\Sigma(\r,\theta) = +\infty$$ (l.781–790)

**The bridge asked for is false, for every `g`.** `graphDev g R` is defined on the strip
`(0, R] × ℝ`, which contains its rim `r = R`; a `SpacelikeDevelopment` is locally an embedding
onto a spacelike Lipschitz hypersurface *without boundary* (`IsSpacelikeLipschitzIn`: near each
point, the set *is* a full graph over an open set of `ℝ²`). At a rim point this cannot hold, and the
proof needs no regularity at all: the `r`-coordinate of the development, `rCoordL = t − x`, is
`≤ R` on the image and `= R` at a rim point, while it is constant along the null direction `∂_τ`
of the development; the null line through a point just outside, `r = R + ε`, meets the local
graph near the rim point (`exists_nullShift`), at a point of `r`-coordinate `R + ε > R`
(`IsSpacelikeLipschitzIn.exists_lt_of_null`). Hence

* `spacelikeDevelopment_graphDev_iff`: `SpacelikeDevelopment (graphDev g R) ↔ R ≤ 0`, for every
  `g` — so the hypothesis of `lem_surface_complete_two_lip` never holds for `R > 0`, and that
  theorem is vacuous; the strict `lem_surface_complete_two` cannot be derived from it, and
  Lemma 2.6(ii)'s cusp is not an instance of it (`cusp_spacelikeDevelopment`, last conjunct).

**The strongest true form** is the bridge off the rim: over any open `Ω ⊆ {r > 0}` on which `g` is
`C¹` with `δ > 0` (Lemma 2.7), the development `graphDevOn g Ω` is a `SpacelikeDevelopment`
(`spacelikeDevelopment_graphDevOn`): its image near each point is the zero set of the height
`nullHeightExpl g` read in null coordinates, `C¹` with derivative positive on the closed future
cone (Lemma 2.7 in null coordinates, `fderiv_nullHeightExpl_pos`), hence cone-increasing on a ball
(`exists_ball_isConeIncreasingOn`), whose zero set is spacelike Lipschitz
(`Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet`); the embedding is read off
`rCoordL` and `yCoordL`. In particular a `C¹` `IsSpacelikeGraph g R` has a spacelike development
over the open strip `0 < r < R` (`spacelikeDevelopment_openStrip`), and Lemma 2.6(ii)'s cusp has one
over the whole half-plane `r > 0` (`cusp_spacelikeDevelopment`). The corrected Lipschitz form of
Lemma 2.8(ii), with the development spacelike over an open set containing the strip, is
`GXScaffold.BTZ.C1SpacelikeDevLip`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `τ_Σ : 𝔻_R^* → ℝ`, `R > 0` | ✓ `g : ℝ × ℝ → ℝ` in `(r, θ)`, as in the strict row; the refutation needs `R > 0` only |
| « piecewise smooth » | ⚠ read: `C¹` on an open `Ω ⊆ {r > 0}` (the bridge); none (the refutation) |
| « spacelike » | ✓ Lemma 2.7, `δ > 0` at every point of `Ω` (the strict `IsSpacelikeGraph`'s pointwise form) |
| « complete » | not used here (the bridge is local) |

## SCOPE (disclosed)

* This file proves no item of Lemma 2.8; it settles the bridge between two of its readings.
  The row stays `partial` on T-btz-scope (`𝔼₀` only) and on the reading of « spacelike ».
* The bridge as dispatched (`C¹ IsSpacelikeGraph g R → SpacelikeDevelopment (graphDev g R)`) is
  refuted, not proved: the rim `r = R` of the strip is a boundary, and a `SpacelikeDevelopment` has
  none. A reading of « spacelike » for a surface with boundary must be a different notion (an
  extension across the rim, as `C1SpacelikeDevLip` takes).
* 0 `sorry`; standard axioms only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; imports the strict
`GX.BTZ.SurfaceCompleteLip` only. Written by T-btz-c1-spacelike-development (2026-11-28).
-/

namespace GX

open Set Filter Topology Function
open scoped Real NNReal Pointwise

namespace E0Surgery

open E0

/-! ### A spacelike Lipschitz hypersurface has no boundary in a null-invariant direction -/

section NoMax

variable {d : ℕ}

/-- **A linear functional constant along a future causal direction has no maximum on a spacelike
Lipschitz hypersurface.** If `ℓ N = 0` for a nonzero future causal `N` and `ℓ e > 0`, then for each
point `q₀` of `S` some point of `S` has `ℓ > ℓ q₀`: the line `q₀ + ε e − s N` meets the local graph
of `S` at `q₀` (`exists_nullShift`), close to `q₀` for `ε` small (`continuousOn_nullShift`). -/
theorem IsSpacelikeLipschitzIn.exists_lt_of_null {V : TopologicalSpace.Opens (Causal.Minkowski d)}
    {S : Set (Causal.Minkowski d)} (hS : Causal.Flat.IsSpacelikeLipschitzIn V S)
    {q₀ : Causal.Minkowski d} (hq₀ : q₀ ∈ S) (ℓ : Causal.Minkowski d →L[ℝ] ℝ)
    {N : Causal.Minkowski d} (hN : Causal.Flat.IsFutureCausal N) (hN0 : N ≠ 0) (hℓN : ℓ N = 0)
    {e : Causal.Minkowski d} (he : 0 < ℓ e) : ∃ q ∈ S, ℓ q₀ < ℓ q := by
  obtain ⟨g₀, O, U', f, c, hc, hq₀O, -, hU', hf, hgr⟩ := hS.locGraph q₀ hq₀
  set A := ((g₀ : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d)) with hA
  set m := A.linear N with hm
  have hmc : Causal.Flat.IsFutureCausal m := Causal.Flat.lorentz.isFutureCausal_apply g₀.2 hN
  have hm0 : m ≠ 0 := fun h => hN0 (A.linear.injective (by rw [map_zero]; exact h))
  have hmQ : ‖m.2‖ ^ 2 ≤ m.1 ^ 2 := by
    have := hmc.2; simp only [Causal.Flat.minkQ] at this; linarith
  have hmn : ‖m.2‖ ≤ m.1 := (pow_le_pow_iff_left₀ (norm_nonneg _) hmc.1 two_ne_zero).1 hmQ
  have hm1 : 0 < m.1 := by
    rcases hmc.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 : ‖m.2‖ = 0 := le_antisymm (h ▸ hmn) (norm_nonneg _)
      exact hm0 (Prod.ext h.symm (norm_eq_zero.1 h2))
  -- the graph point over `g₀ • q₀`
  set p₀ := g₀ • q₀ with hp₀
  have hp₀g : p₀ ∈ g₀ • (O : Set (Causal.Minkowski d)) ∩ Causal.Flat.graphOver U' f := by
    rw [← hgr]; exact Set.smul_mem_smul_set ⟨hq₀, hq₀O⟩
  obtain ⟨δ, hδ, σ, hσ0, hσ⟩ := exists_nullShift hU' hc hf hm1 hmn hp₀g.2.1 hp₀g.2.2
  have hσc : ContinuousOn σ (Metric.ball p₀ δ) :=
    continuousOn_nullShift hc hf hm1 hmn fun q hq => (hσ q hq).2
  set ψ : Causal.Minkowski d → Causal.Minkowski d := fun q => q - σ q • m with hψ
  have hψc : ContinuousAt ψ p₀ :=
    continuousAt_id.sub ((hσc.continuousAt (Metric.ball_mem_nhds p₀ hδ)).smul continuousAt_const)
  have hψ0 : ψ p₀ = p₀ := by simp [hψ, hσ0]
  set φ : ℝ → Causal.Minkowski d := fun ε => g₀ • (q₀ + ε • e) with hφ
  have hφc : Continuous φ :=
    (continuous_const_smul g₀).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hφ0 : φ 0 = p₀ := by simp [hφ, hp₀]
  have hgO : IsOpen (g₀ • (O : Set (Causal.Minkowski d))) := by
    rw [← Set.image_smul]; exact (Causal.Flat.isom.toHomeomorph g₀).isOpenMap _ O.isOpen
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), φ ε ∈ Metric.ball p₀ δ ∧ ψ (φ ε) ∈ g₀ • (O : Set _) := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), φ ε ∈ Metric.ball p₀ δ :=
      hφc.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact Metric.ball_mem_nhds p₀ hδ)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ (φ ε) ∈ g₀ • (O : Set _) := by
      have hc' : ContinuousAt (ψ ∘ φ) 0 := by
        refine ContinuousAt.comp (g := ψ) ?_ hφc.continuousAt
        rw [hφ0]; exact hψc
      refine hc'.preimage_mem_nhds (hgO.mem_nhds ?_)
      simp only [comp_apply, hφ0, hψ0]; exact hp₀g.1
    exact h1.and h2
  obtain ⟨ε, ⟨hεb, hεO⟩, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hmem : ψ (φ ε) ∈ g₀ • (S ∩ (O : Set _)) := by
    rw [hgr]; exact ⟨hεO, (hσ _ hεb).2.1, (hσ _ hεb).2.2⟩
  obtain ⟨s, ⟨hsS, -⟩, hs⟩ := hmem
  -- `ψ (φ ε) = g₀ • (q₀ + ε e − σ N)`
  have hshift : g₀ • (q₀ + ε • e - σ (φ ε) • N) = ψ (φ ε) := by
    have hgen : ∀ (x : Causal.Minkowski d) (t : ℝ), A (x - t • N) = A x - t • m := by
      intro x t
      have h := Causal.Flat.isom_sub A (x - t • N) x
      rw [sub_sub_cancel, map_smul] at h
      rw [hm, ← h]; abel
    show A (q₀ + ε • e - σ (φ ε) • N) = φ ε - σ (φ ε) • m
    rw [hgen]; rfl
  rw [← hshift] at hs
  have hs' : s = q₀ + ε • e - σ (φ ε) • N := smul_left_cancel g₀ hs
  refine ⟨s, hsS, ?_⟩
  rw [hs', map_sub, map_add, map_smul, map_smul, hℓN, smul_zero, sub_zero, smul_eq_mul]
  have := mul_pos (hε : (0:ℝ) < ε) he
  linarith

end NoMax

/-! ### The refutation at the rim -/

/-- The developed `∂_τ`, `D(τ + s, r, θ) = D(τ, r, θ) + s n` (`btzPaperDev_add_tau`). -/
noncomputable def tauDirDev : Causal.Minkowski 2 := btzPaperDev (1, 0, 0)

theorem btzPaperDev_add_tau (τ r θ s : ℝ) :
    btzPaperDev (τ + s, r, θ) = btzPaperDev (τ, r, θ) + s • tauDirDev := by
  simp only [tauDirDev, btzPaperDev]
  refine Prod.ext (by simp; ring) ?_
  ext i; fin_cases i <;> (simp; try ring)

theorem tauDirDev_eq : tauDirDev = nullToMink (2, 0, 0) := by
  rw [tauDirDev, btzPaperDev_eq_nullToMink]; simp [btzPaperNull]

theorem isFutureCausal_tauDirDev : Causal.Flat.IsFutureCausal tauDirDev := by
  rw [tauDirDev_eq, ← nullCone_iff_isFutureCausal]
  exact ⟨by norm_num, le_rfl, by norm_num⟩

theorem tauDirDev_ne_zero : tauDirDev ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  simp [tauDirDev, btzPaperDev] at this

theorem rCoordL_tauDirDev : rCoordL tauDirDev = 0 := by
  rw [tauDirDev, rCoordL_btzPaperDev]

/-- **No development of a graph over the strip `(0, R] × ℝ`, `R > 0`, is a spacelike
development**: at the rim point `(R, 0)`, `rCoordL` is maximal on the image of any neighbourhood,
which `IsSpacelikeLipschitzIn.exists_lt_of_null` forbids. No hypothesis on `g`. -/
theorem spacelikeDevelopment_graphDev_iff (g : ℝ × ℝ → ℝ) (R : ℝ) :
    Causal.Flat.SpacelikeDevelopment (graphDev g R) ↔ R ≤ 0 := by
  constructor
  · intro hF
    by_contra hR
    push Not at hR
    set x : Strip R := ⟨(R, 0), hR, le_rfl⟩
    obtain ⟨U, V, hxU, -, hT⟩ := hF.locally x
    have he : 0 < rCoordL (btzPaperDev (0, 1, 0)) := by rw [rCoordL_btzPaperDev]; norm_num
    obtain ⟨q, ⟨z, -, rfl⟩, hq⟩ := IsSpacelikeLipschitzIn.exists_lt_of_null hT ⟨x, hxU, rfl⟩
      rCoordL isFutureCausal_tauDirDev tauDirDev_ne_zero rCoordL_tauDirDev he
    simp only [graphDev, graphMap, rCoordL_btzPaperDev] at hq
    exact absurd (z : Strip R).2.2 (not_le.2 hq)
  · intro hR
    have hE : ∀ x : Strip R, False := fun x => absurd (x.2.1.trans_le x.2.2) (not_lt.2 hR)
    exact ⟨continuous_iff_continuousAt.2 fun x => (hE x).elim, fun x => (hE x).elim⟩

/-- `lem_surface_complete_two_lip`'s hypotheses are never met: with `R > 0` there is no `g` whose
development over the strip is a spacelike development. -/
theorem lem_surface_complete_two_lip_hyp_false {g : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 < R) :
    ¬ Causal.Flat.SpacelikeDevelopment (graphDev g R) := by
  rw [spacelikeDevelopment_graphDev_iff]; exact not_le.2 hR

/-! ### The bridge off the rim -/

/-- **The development of a graph over a set `Ω`** of the `(r, θ)`-plane. -/
noncomputable def graphDevOn (g : ℝ × ℝ → ℝ) (Ω : Set (ℝ × ℝ)) (p : Ω) : Causal.Minkowski 2 :=
  btzPaperDev (graphMap g p.1)

/-- The domain of `nullHeightExpl g` over `Ω`: the null coordinates `(a, b, c)` with `b > 0` and
`(b, −c/b) ∈ Ω`. -/
def nullDom (Ω : Set (ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  {Q | 0 < Q.2.1 ∧ ((Q.2.1, -(Q.2.2 / Q.2.1)) : ℝ × ℝ) ∈ Ω}

theorem contDiffOn_nullHeightExpl_on {G : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)}
    (hG : ContDiffOn ℝ 1 G Ω) : ContDiffOn ℝ 1 (nullHeightExpl G) (nullDom Ω) := by
  have hb : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.2.1) (nullDom Ω) :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hc : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.2.2) (nullDom Ω) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have ha : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => Q.1) (nullDom Ω) := contDiff_fst.contDiffOn
  have hne : ∀ Q ∈ nullDom Ω, Q.2.1 ≠ 0 := fun Q hQ => ne_of_gt hQ.1
  have hθ : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => -(Q.2.2 / Q.2.1)) (nullDom Ω) :=
    (hc.div hb hne).neg
  have hpair : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => ((Q.2.1, -(Q.2.2 / Q.2.1)) : ℝ × ℝ))
      (nullDom Ω) := hb.prodMk hθ
  have hGc : ContDiffOn ℝ 1 (fun Q : ℝ × ℝ × ℝ => G (Q.2.1, -(Q.2.2 / Q.2.1))) (nullDom Ω) :=
    hG.comp hpair fun Q hQ => hQ.2
  exact ((((ha.sub ((hc.pow 2).div hb hne)).add hb).div_const 2).sub hGc)

theorem isOpen_nullDom {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (nullDom Ω) := by
  have hcont : ContinuousOn (fun Q : ℝ × ℝ × ℝ => ((Q.2.1, -(Q.2.2 / Q.2.1)) : ℝ × ℝ))
      {Q : ℝ × ℝ × ℝ | 0 < Q.2.1} :=
    (continuous_fst.comp continuous_snd).continuousOn.prodMk
      (((continuous_snd.comp continuous_snd).continuousOn.div
        (continuous_fst.comp continuous_snd).continuousOn fun Q hQ => ne_of_gt hQ).neg)
  exact hcont.isOpen_inter_preimage isOpen_nullPos hΩ

/-- The height vanishes on the developed graph. -/
theorem nullHeightExpl_btzPaperNull (G : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    nullHeightExpl G (btzPaperNull (G p, p.1, p.2)) = 0 := by
  have hp0 : p.1 ≠ 0 := ne_of_gt hp
  have e : -(-(p.1 * p.2) / p.1) = p.2 := by field_simp
  simp only [nullHeightExpl, btzPaperNull, e]
  field_simp
  ring

theorem btzPaperNull_mem_nullDom {G : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {p : ℝ × ℝ} (hp : 0 < p.1)
    (hpΩ : p ∈ Ω) : btzPaperNull (G p, p.1, p.2) ∈ nullDom Ω := by
  have hp0 : p.1 ≠ 0 := ne_of_gt hp
  have e : -(-(p.1 * p.2) / p.1) = p.2 := by field_simp
  refine ⟨hp, ?_⟩
  simp only [btzPaperNull, e]
  exact hpΩ

/-- On the zero set of the height, the point is the developed graph point. -/
theorem eq_btzPaperNull_of_nullHeightExpl {G : ℝ × ℝ → ℝ} {Q : ℝ × ℝ × ℝ} (hQ : 0 < Q.2.1)
    (h0 : nullHeightExpl G Q = 0) :
    btzPaperNull (G (Q.2.1, -(Q.2.2 / Q.2.1)), Q.2.1, -(Q.2.2 / Q.2.1)) = Q := by
  have hb : Q.2.1 ≠ 0 := ne_of_gt hQ
  simp only [nullHeightExpl] at h0
  have hG : G (Q.2.1, -(Q.2.2 / Q.2.1)) = (Q.1 - Q.2.2 ^ 2 / Q.2.1 + Q.2.1) / 2 := by linarith
  simp only [btzPaperNull, hG]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · simp only; field_simp; ring
  · simp only; field_simp

/-- **Lemma 2.7 in null coordinates, local form** (`fderiv_nullHeight_pos` without periodicity
and with `G` differentiable at the one point): the derivative of `nullHeightExpl G` at
`btzPaperNull p` is positive on every nonzero vector of the closed future cone. -/
theorem fderiv_nullHeightExpl_pos {G : ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ} (hr : 0 < p.2.1)
    {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt G L (p.2.1, p.2.2))
    (hδ : 0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.2.1)
    (hd : DifferentiableAt ℝ (nullHeightExpl G) (btzPaperNull p)) {V : ℝ × ℝ × ℝ}
    (hV : NullCone V) (hV0 : V ≠ 0) : 0 < fderiv ℝ (nullHeightExpl G) (btzPaperNull p) V := by
  obtain ⟨L', hL', hL'h⟩ := hasFDerivAt_btzPaperNull p
  set h : ℝ × ℝ × ℝ → ℝ := fun q => q.1 - G (q.2.1, q.2.2)
  have hh : HasFDerivAt h ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
      L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_fst.sub (hL.comp p hasFDerivAt_snd)
  have hev : (nullHeightExpl G ∘ btzPaperNull) =ᶠ[𝓝 p] h := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hr]
      with q hq
    rw [comp_apply]
    simp only [nullHeightExpl, h, btzPaperNull]
    have hq0 : q.2.1 ≠ 0 := ne_of_gt hq
    congr 1
    · field_simp; ring
    · congr 2; field_simp
  have hcomp := hd.hasFDerivAt.comp p hL'
  have heq := (hcomp.congr_of_eventuallyEq hev.symm).unique hh
  set r := p.2.1
  set θ := p.2.2
  set wr := V.2.1
  set wθ := -(V.2.2 + V.2.1 * θ) / r
  set wτ := (V.1 - V.2.1 * θ ^ 2 - 2 * r * θ * wθ + V.2.1) / 2
  have hw : L' (wτ, wr, wθ) = V := by
    rw [hL'h]
    have hr0 : r ≠ 0 := ne_of_gt hr
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only [wτ, wθ, wr]; field_simp; ring
    · simp only [wθ, wr]; field_simp; ring
  have hval : fderiv ℝ (nullHeightExpl G) (btzPaperNull p) V =
      wτ - (wr * L (1, 0) + wθ * L (0, 1)) := by
    have := congrArg (fun T : ℝ × ℝ × ℝ →L[ℝ] ℝ => T (wτ, wr, wθ)) heq
    simp only [ContinuousLinearMap.comp_apply, hw] at this
    rw [this, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', clm_apply_pair]
  rw [hval]
  obtain ⟨ha, hb, hc⟩ := hV
  refine covector_pos hr hδ hb ?_ ?_
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hid : -2 * wτ * wr + wr ^ 2 + r ^ 2 * wθ ^ 2 = V.2.2 ^ 2 - V.1 * V.2.1 := by
      simp only [wτ, wθ, wr]; field_simp; ring
    rw [hid]; linarith
  · intro h1 h2
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hb0 : V.2.1 = 0 := h1
    have hc0 : V.2.2 = 0 := by
      have : -(V.2.2 + V.2.1 * θ) / r = 0 := h2
      rw [hb0] at this; field_simp at this; linarith
    have ha0 : V.1 ≠ 0 := fun ha0 => hV0 (Prod.ext ha0 (Prod.ext hb0 hc0))
    have : wτ = V.1 / 2 := by simp only [wτ, wθ, hb0, hc0]; ring
    rw [this]; exact half_pos (lt_of_le_of_ne ha (Ne.symm ha0))

/-- **The bridge, off the rim**: over an open `Ω ⊆ {r > 0}` on which `g` is `C¹` with `δ > 0`
(Lemma 2.7), the development of the graph is a spacelike development. -/
theorem spacelikeDevelopment_graphDevOn {g : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hpos : ∀ p ∈ Ω, 0 < p.1) (hC1 : ContDiffOn ℝ 1 g Ω)
    (hδ : ∀ p ∈ Ω, ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt g L p ∧
      0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.1) :
    Causal.Flat.SpacelikeDevelopment (graphDevOn g Ω) := by
  have hgc : Continuous fun z : Ω => g z.1 :=
    continuousOn_iff_continuous_restrict.1 hC1.continuousOn
  have hFc : Continuous (graphDevOn g Ω) :=
    contDiff_btzPaperDev.continuous.comp (hgc.prodMk (continuous_subtype_val.fst.prodMk
      continuous_subtype_val.snd))
  refine ⟨hFc, fun x => ?_⟩
  set p : ℝ × ℝ := x.1 with hpdef
  have hr : 0 < p.1 := hpos p x.2
  set F := graphDevOn g Ω with hF
  set h : Causal.Minkowski 2 → ℝ := fun v => nullHeightExpl g (nullToMink.symm v) with hh
  set D : Set (ℝ × ℝ × ℝ) := nullDom Ω ∩ {Q | p.1 / 2 < Q.2.1} with hD
  have hDo : IsOpen D := (isOpen_nullDom hΩ).inter
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd))
  set W : Set (Causal.Minkowski 2) := nullToMink.symm ⁻¹' D with hW
  have hWo : IsOpen W := hDo.preimage nullToMinkHomeomorph.symm.continuous
  have hFnull : ∀ z : Ω, nullToMink.symm (F z) = btzPaperNull (g z.1, z.1.1, z.1.2) := by
    intro z
    simp only [hF, graphDevOn, graphMap, btzPaperDev_eq_nullToMink, LinearEquiv.symm_apply_apply]
  set Q₀ := btzPaperNull (g p, p.1, p.2) with hQ₀
  have hQ₀D : Q₀ ∈ D := ⟨btzPaperNull_mem_nullDom hr x.2, by
    show p.1 / 2 < p.1; linarith⟩
  have hp₀W : F x ∈ W := by show nullToMink.symm (F x) ∈ D; rw [hFnull]; exact hQ₀D
  have hhC : ContDiffOn ℝ 1 h W := by
    have h1 : ContDiffOn ℝ 1 (nullHeightExpl g) D :=
      (contDiffOn_nullHeightExpl_on hC1).mono fun Q (hQ : Q ∈ D) => hQ.1
    exact h1.comp (LinearMap.toContinuousLinearMap
        (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)).contDiff.contDiffOn
      fun v (hv : v ∈ W) => (hv : nullToMink.symm v ∈ D)
  -- Lemma 2.7: the derivative is positive on the future cone
  obtain ⟨L, hL, hδL⟩ := hδ p x.2
  have hd : DifferentiableAt ℝ (nullHeightExpl g) Q₀ :=
    ((contDiffOn_nullHeightExpl_on hC1).differentiableOn one_ne_zero).differentiableAt
      ((isOpen_nullDom hΩ).mem_nhds hQ₀D.1)
  have hderpos : ∀ v : Causal.Minkowski 2, v ≠ 0 → Causal.Flat.IsFutureCausal v →
      0 < fderiv ℝ h (F x) v := by
    intro v hv0 hv
    set Nl := LinearMap.toContinuousLinearMap
      (nullToMink.symm : Causal.Minkowski 2 →ₗ[ℝ] ℝ × ℝ × ℝ)
    have hFx : Nl (F x) = Q₀ := hFnull x
    have hH : HasFDerivAt h ((fderiv ℝ (nullHeightExpl g) Q₀).comp Nl) (F x) := by
      have := (hFx ▸ hd).hasFDerivAt.comp (F x) Nl.hasFDerivAt
      rw [hFx] at this
      exact this
    rw [hH.fderiv, ContinuousLinearMap.comp_apply]
    have hpQ : (p.1, p.2) = p := rfl
    refine fderiv_nullHeightExpl_pos (G := g) (p := (g p, p.1, p.2)) hr (by exact hL) hδL hd ?_ ?_
    · rw [nullCone_iff_isFutureCausal]
      simpa [Nl] using hv
    · intro h0
      apply hv0
      have : nullToMink (Nl v) = nullToMink 0 := by rw [h0]
      simpa [Nl] using this
  obtain ⟨ε, hε, c, hc0, hc1, hballW, hinc⟩ :=
    exists_ball_isConeIncreasingOn hWo hhC hp₀W hderpos
  have hh0 : h (F x) = 0 := by
    simp only [hh, hFnull]; exact nullHeightExpl_btzPaperNull g hr
  obtain ⟨V, hpV, hVb, hV⟩ := Causal.Flat.Cla.exists_isSpacelikeLipschitzIn_zeroSet
    Metric.isOpen_ball (hhC.continuousOn.mono hballW) hc0 hc1 hinc
    (Metric.mem_ball_self hε) hh0
  -- the neighbourhood and the image
  set U : TopologicalSpace.Opens Ω := ⟨F ⁻¹' V, V.isOpen.preimage hFc⟩ with hU
  have hVW : ∀ q ∈ (V : Set (Causal.Minkowski 2)), q ∈ W := fun q hq => hballW (hVb hq)
  have himg : F '' (U : Set Ω) = {q | q ∈ (V : Set (Causal.Minkowski 2)) ∧ h q = 0} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hz, ?_⟩
      simp only [hh, hFnull]; exact nullHeightExpl_btzPaperNull g (hpos _ z.2)
    · rintro ⟨hqV, hq0⟩
      have hqD : nullToMink.symm q ∈ D := hVW q hqV
      set Q := nullToMink.symm q
      have hQb : 0 < Q.2.1 := hqD.1.1
      refine ⟨⟨(Q.2.1, -(Q.2.2 / Q.2.1)), hqD.1.2⟩, ?_, ?_⟩
      · show F _ ∈ V
        have : F ⟨(Q.2.1, -(Q.2.2 / Q.2.1)), hqD.1.2⟩ = q := by
          rw [← nullToMink.apply_symm_apply q]
          simp only [hF, graphDevOn, graphMap, btzPaperDev_eq_nullToMink]
          rw [eq_btzPaperNull_of_nullHeightExpl hQb hq0]
        rw [this]; exact hqV
      · rw [← nullToMink.apply_symm_apply q]
        simp only [hF, graphDevOn, graphMap, btzPaperDev_eq_nullToMink]
        rw [eq_btzPaperNull_of_nullHeightExpl hQb hq0]
  refine ⟨U, V, hpV, ?_, by rw [himg]; exact hV⟩
  -- the embedding, read off the null coordinates `b` and `−c/b`
  set ψ : Causal.Minkowski 2 → ℝ × ℝ := fun v =>
    ((nullToMink.symm v).2.1, -((nullToMink.symm v).2.2 / max (nullToMink.symm v).2.1 (p.1 / 2)))
    with hψ
  have hNc : Continuous fun v : Causal.Minkowski 2 => nullToMink.symm v :=
    nullToMinkHomeomorph.symm.continuous
  have hψc : Continuous ψ := by
    have hb : Continuous fun v : Causal.Minkowski 2 => (nullToMink.symm v).2.1 :=
      continuous_fst.comp (continuous_snd.comp hNc)
    have hc' : Continuous fun v : Causal.Minkowski 2 => (nullToMink.symm v).2.2 :=
      continuous_snd.comp (continuous_snd.comp hNc)
    refine hb.prodMk (hc'.div (hb.max continuous_const) fun v => ?_).neg
    exact ne_of_gt (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  have hres : Continuous ((U : Set Ω).restrict F) := hFc.comp continuous_subtype_val
  refine IsEmbedding.of_comp hres hψc ?_
  have heq : ψ ∘ (U : Set Ω).restrict F = fun z => (z.1.1 : ℝ × ℝ) := by
    funext z
    have hzD : nullToMink.symm (F z.1) ∈ D := hVW _ z.2
    rw [hFnull] at hzD
    have hz1 : p.1 / 2 < z.1.1.1 := hzD.2
    have hz0 : z.1.1.1 ≠ 0 := ne_of_gt (lt_trans (by linarith) hz1)
    simp only [comp_apply, restrict_apply, hψ, hFnull]
    simp only [btzPaperNull, max_eq_left hz1.le]
    refine Prod.ext rfl ?_
    simp only; field_simp
  rw [heq]
  exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal

/-- The open strip `0 < r < R`. -/
def openStrip (R : ℝ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < R}

/-- **A `C¹` spacelike graph over the strip has a spacelike development over the open strip**
(the strongest true form of the bridge: at the rim it fails, `spacelikeDevelopment_graphDev_iff`). -/
theorem spacelikeDevelopment_openStrip {g : ℝ × ℝ → ℝ} {R : ℝ} (hg : IsSpacelikeGraph g R)
    (hC1 : ContDiffOn ℝ 1 g (stripSet R)) :
    Causal.Flat.SpacelikeDevelopment (graphDevOn g (openStrip R)) := by
  refine spacelikeDevelopment_graphDevOn
    ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const))
    (fun p hp => hp.1) (hC1.mono fun p hp => ⟨hp.1, hp.2.le⟩) fun p hp => hg.deriv p hp.1 hp.2.le

/-! ### Lemma 2.6(ii)'s cusp -/

/-- **Lemma 2.6(ii)'s cusp** (`lem_curve_extension_ii_complete`): its development is a spacelike
development over the whole half-plane `r > 0`, its pulled length over the strip is complete, it
goes to `+∞` at the axis; and its development over the strip is *not* a spacelike development. -/
theorem cusp_spacelikeDevelopment {τR : ℝ → ℝ} {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hτ : ContDiff ℝ n τR) (hper : Periodic τR (2 * π)) (hpos : ∀ θ, 0 < τR θ) {R : ℝ}
    (hR : 0 < R) :
    ∃ τ : ℝ × ℝ → ℝ, (∀ θ, τ (R, θ) = τR θ) ∧ IsSpacelikeGraph τ R ∧
      Causal.Flat.SpacelikeDevelopment (graphDevOn τ {p | 0 < p.1}) ∧
      CompleteSpace (Causal.Flat.PulledLength (graphDev τ R)) ∧
      Tendsto τ (comap Prod.fst (𝓝[>] 0)) atTop ∧
      ¬ Causal.Flat.SpacelikeDevelopment (graphDev τ R) := by
  obtain ⟨τ, hrim, hp, hpos', hC, hδ, hlim⟩ := lem_curve_extension_ii hn hτ hper hpos (R := R)
  have hδ1 : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ R → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt τ L p ∧
      (1 : ℝ) ^ 2 / p.1 ^ 2 ≤ spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := fun p hp0 _ => by
    obtain ⟨L, hL, h⟩ := hδ p hp0
    exact ⟨L, hL, by simpa using h⟩
  have hδpos : ∀ p : ℝ × ℝ, 0 < p.1 → ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt τ L p ∧
      0 < spacelikeDelta (L (1, 0)) (L (0, 1)) p.1 := fun p hp0 => by
    obtain ⟨L, hL, h⟩ := hδ p hp0
    exact ⟨L, hL, (by positivity : (0 : ℝ) < 1 / p.1 ^ 2).trans_le h⟩
  have hC1 : ContDiffOn ℝ 1 τ (stripSet R) := (hC.of_le hn).mono fun p hp => hp.1
  exact ⟨τ, hrim, ⟨hp, fun p hp0 _ => hδpos p hp0⟩,
    spacelikeDevelopment_graphDevOn (isOpen_lt continuous_const continuous_fst) (fun _ h => h)
      (hC.of_le hn) hδpos,
    (lem_surface_complete_one hR one_pos hp hC1 hδ1).2, hlim, lem_surface_complete_two_lip_hyp_false hR⟩

end E0Surgery

end GX
