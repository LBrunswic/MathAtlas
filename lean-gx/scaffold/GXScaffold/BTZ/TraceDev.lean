import GX.BTZ.BluntSpear
import GX.BTZ.IsomE0
import GX.BTZ.SurfaceCompleteLip
import GXScaffold.BTZ.C1SpacelikeDevLip

/-!
# The trace of a spacelike-Lipschitz surface on a blunt spear chart develops spacelike

`btzthm:BTZ_Cauchy-completness` — `BTZ_1.tex:1582` (theorem), Step 1 of its proof, the first half
of l.1601, read in the flat setting of `GX.E0BluntSpear.lem_blunt_spear` (`BTZ_1.tex:693–701`).
Unmarked: a step of the proof, not the theorem; and the step's conclusion as planned is false
(see SCOPE). Target T-btz-trace-development.

> By Lemma \ref{lem:blunt_spear_neighborhood}, one can reduce the size of $\S$ in such a way
> $\phi(\Sigma_0\cap \S)$ is the graph of a some function $\tau_0:\mathbb D_R^*\rightarrow \RR$
> in $\mass{0}$ with $\tau_0$. Since $\Sigma_0$ is complete, by Lemma \ref{lem:surface_complete}
> $ \lim_{(\r,\theta)\rightarrow 0}\tau_0(\r,\theta) = +\infty$. (l.1601)

What is built is the input of `lem:surface_complete` (ii) that the trace `τ_Σ` of the flat
`lem_blunt_spear` must provide: `g(r, θ) = τ_Σ(r e^{iθ})` is `2π`-periodic and its development
`D(g(r, θ), r, θ)` (`GX.E0Surgery.graphDev`) is locally a spacelike Lipschitz hypersurface.

* `GX.E0TraceDev.trace_spacelikeDevelopment` — periodicity; `graphDev g R` is an embedding of the
  closed strip `(0, R] × ℝ`; at every point with `r < R` it is locally (open `U` inside `r < R`)
  an embedded spacelike Lipschitz hypersurface; `openGraphDev g R` (the open strip `(0, R) × ℝ`)
  is a `Causal.Flat.SpacelikeDevelopment`.
* `GX.E0TraceDev.trace_spacelikeDevelopment_openStrip`, `GX.E0TraceDev.trace_tendsto_atTop` — the
  same in the form of `E0Surgery.lem_surface_complete_two_lipOn` (`Ω = openStrip R`), and the
  chain to `τ_Σ → +∞` for `R″ < R` given the completeness of the pulled length over `(0, R″]`.
* `GX.E0TraceDev.lem_blunt_spear_trace` — the same, chained after `lem_blunt_spear`, for its `R′`
  and `τ_Σ` (with `Σ` Cauchy and spacelike Lipschitz).
* `GX.E0TraceDev.not_spacelikeDevelopment_graphDev` — **for `R > 0` no `g` has
  `SpacelikeDevelopment (graphDev g R)`**: at a point of the rim `r = R` the image is a surface
  with boundary, while `IsSpacelikeLipschitzIn` asks, around each of its points, a full Lipschitz
  graph over an open set. Proof: `ℓ(q) = q₀ − q₁` reads `r` off the development, so
  `ℓ ≤ R` on the image with equality at the rim; in the frame of the local graph `(f(x), x)`,
  `ℓ` is `α t + β(x) + const` with `ℓ`'s kernel containing a null vector, so some direction `e`
  has `β(e) > c |α| ‖e‖ ≥ |α (f(x₀ + s e) − f(x₀))| / s`, and `ℓ` exceeds `R` along `x₀ + s e`.
* `GX.E0TraceDev.flatE0_regChart` — the one new chart lemma: the `FlatE0 N` analogue of
  `SpearSurgeryDatum.eventually_regChart` (on a connected open neighbourhood of an off-axis point
  of a sector, the chart of `N` read through an `𝔼₀`-morphism `ψ` is `g •` the sector chart; the
  rigidity `E0.exists_eqOn_sectorSmulInl`, as in `flat_vertical_noLimit`).

## Hypothesis checklist

| hypothesis (the target's setting) | here |
|---|---|
| `N` flat, `ψ : E0Y → FlatE0 N`, `IsE0Mor ψ W`, `W` open, `bspearY v R ⊆ W` | ✓ carried |
| `InjOn ψ W` | ⚠ weakened: not used (only `lem_blunt_spear_trace`, which calls `lem_blunt_spear`, carries it) |
| `Σ ⊆ N` `Causal.Flat.IsSpacelikeLipschitz 2` | ✓ carried; Cauchy not used (carried in `lem_blunt_spear_trace`, which `lem_blunt_spear` needs) |
| `τ_Σ` continuous on `{0 < ‖z‖ ≤ R}` | ✓ carried |
| `ψ(paperInY x) ∈ Σ ↔ x.1 = τ_Σ x.2` on `bspear v R` | ✓ carried |
| (unprinted in the target) the graph lies in the spear: `v + ‖z‖/2 < τ_Σ z` | ⚠ strengthened (an added hypothesis): without it the graph equivalence says nothing at the points `(τ_Σ z, z)` outside `bspear v R`, and `τ_Σ` need not be the trace there; `lem_blunt_spear` returns the stronger `v + R′/2 < τ_Σ z` (used so in `lem_blunt_spear_trace`) |
| conclusion `SpacelikeDevelopment (graphDev g R)` | ✗ false for `R > 0` (`not_spacelikeDevelopment_graphDev`); proved over the open strip and locally at `r < R` |

## SCOPE (disclosed)

* **Finding.** `Causal.Flat.SpacelikeDevelopment (graphDev g R)` is unsatisfiable for `R > 0`
  (`not_spacelikeDevelopment_graphDev`, every `g`; found independently of the concurrent
  `E0Surgery.spacelikeDevelopment_graphDev_iff` of T-btz-c1-spacelike-development, which states
  the same as an iff). So the strict `GX.E0Surgery.lem_surface_complete_two_lip`
  (`GX/BTZ/SurfaceCompleteLip.lean:361`), whose hypothesis `hF` is exactly that, is vacuous. The
  goal was moved (master's correction, 2026-11-28) to the corrected
  `E0Surgery.lem_surface_complete_two_lipOn` (`GXScaffold/BTZ/C1SpacelikeDevLip.lean`), whose
  hypothesis over an open `Ω ⊇ (0, R″] × ℝ` the trace meets with `Ω = openStrip R`, `R″ < R`
  (`trace_spacelikeDevelopment_openStrip`, `trace_tendsto_atTop`): the radius is shrunk once,
  as the paper's « reduce the size of `S` » allows. Over `Ω ⊇ (0, R] × ℝ` itself it is not
  proved: the hypotheses know `Σ` as the graph of `τ_Σ` only on `bspear v R` (`r ≤ R`).
* The target's conclusion as planned is false; the strongest true form is proved
  (`trace_spacelikeDevelopment`), so the row is `partial`.
* Completeness of the pulled length is not addressed (T-btz-trace-complete).
* No example of the setting is built (kb/0011: not cheap); the refutation does not need one, as
  it holds for every `g`.
* 0 `sorry`; standard axioms only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; imports the strict
`GX.BTZ.BluntSpear`, `GX.BTZ.IsomE0`, `GX.BTZ.SurfaceCompleteLip` and the scaffold
`GXScaffold.BTZ.C1SpacelikeDevLip` (T-btz-c1-spacelike-development; graduates before or with this file). Written by
T-btz-trace-development (2026-11-28).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real Pointwise

namespace E0TraceDev

open E0 E0CBG E0Spear E0BluntSpear E0Surgery E0AbsMax

/-! ### §1–§2 (restriction; the closed strip has no spacelike development) -/


theorem isSpacelikeLipschitzIn_inter {d : ℕ} {V V' : Opens (Causal.Minkowski d)}
    {S : Set (Causal.Minkowski d)} (h : Causal.Flat.IsSpacelikeLipschitzIn V S) (hV' : V' ≤ V) :
    Causal.Flat.IsSpacelikeLipschitzIn V' (S ∩ V') := by
  refine ⟨fun q hq => hq.2, fun p hp q hq hpq =>
    h.achronal p hp.1 q hq.1 ((Causal.minkowski d).lt_mono hV' hpq), fun p hp => ?_⟩
  obtain ⟨g, O, U, f, c, hc, hpO, -, hU, hf, hgr⟩ := h.locGraph p hp.1
  refine ⟨g, O ⊓ V', U, f, c, hc, ⟨hpO, hp.2⟩, inf_le_right, hU, hf, ?_⟩
  have e1 : S ∩ (V' : Set _) ∩ ((O ⊓ V' : Opens _) : Set (Causal.Minkowski d)) =
      (S ∩ O) ∩ V' := by
    ext; simp only [Opens.coe_inf, mem_inter_iff]; tauto
  rw [e1, Set.smul_set_inter, hgr, Opens.coe_inf, Set.smul_set_inter]
  ext; simp only [mem_inter_iff]; tauto

/-- `q₀ − q₁` reads the radius off the development. -/
theorem btzPaperDev_rad (p : ℝ × ℝ × ℝ) : (btzPaperDev p).1 - (btzPaperDev p).2 0 = p.2.1 := by
  simp [btzPaperDev]

/-- `q₀ − q₁` reads the radius off `graphDev`. -/
theorem graphDev_rad (g : ℝ × ℝ → ℝ) (R : ℝ) (p : Strip R) :
    (graphDev g R p).1 - (graphDev g R p).2 0 = p.1.1 :=
  btzPaperDev_rad _

/-- The radial functional `q ↦ q₀ − q₁` of `𝐌³`, linear. -/
noncomputable def radL : Causal.Minkowski 2 →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ _ -
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap.comp
      (LinearMap.snd ℝ ℝ _))

theorem radL_apply (q : Causal.Minkowski 2) : radL q = q.1 - q.2 0 := rfl

/-- **The closed strip has no spacelike development** (`R > 0`, every `g`): at the rim point
`(R, 0)` the image is a surface with boundary, never a full local Lipschitz graph. Refutes the
target's printed conclusion, and makes the hypothesis `hF` of the strict
`E0Surgery.lem_surface_complete_two_lip` unsatisfiable. -/
theorem not_spacelikeDevelopment_graphDev {g : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 < R) :
    ¬ Causal.Flat.SpacelikeDevelopment (graphDev g R) := by
  intro hF
  set F := graphDev g R with hFdef
  set x0 : Strip R := ⟨(R, 0), hR, le_rfl⟩
  obtain ⟨U, V, hx0, -, hS⟩ := hF.locally x0
  obtain ⟨k, O, U', f, c, hc, hpO, -, hU', hf, hgr⟩ := hS.locGraph (F x0) ⟨x0, hx0, rfl⟩
  have hℓS : ∀ q ∈ F '' U, radL q ≤ R := by
    rintro _ ⟨x, -, rfl⟩; rw [radL_apply, hFdef, graphDev_rad]; exact x.2.2
  have hℓ0 : radL (F x0) = R := by rw [radL_apply, hFdef, graphDev_rad]
  have hq0 : k • F x0 ∈ k • (O : Set (Causal.Minkowski 2)) ∩ Causal.Flat.graphOver U' f := by
    rw [← hgr]; exact ⟨F x0, ⟨⟨x0, hx0, rfl⟩, hpO⟩, rfl⟩
  set q0 := k • F x0 with hq0def
  obtain ⟨hq0O, hq0U, hq0f⟩ := hq0
  have key : ∀ x ∈ U', ((f x, x) : Causal.Minkowski 2) ∈ k • (O : Set (Causal.Minkowski 2)) →
      radL (k⁻¹ • ((f x, x) : Causal.Minkowski 2)) ≤ R := by
    intro x hx hxO
    have hm : ((f x, x) : Causal.Minkowski 2) ∈ k • (F '' U ∩ O) := by
      rw [hgr]; exact ⟨hxO, hx, rfl⟩
    obtain ⟨q, hq, hqe⟩ := hm
    rw [← hqe, inv_smul_smul]; exact hℓS q hq.1
  -- the linear part of `k⁻¹`, and `φ = radL ∘ L`
  set L : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2 :=
    ((k⁻¹ : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear with hL
  have hLl : L ∈ Causal.Flat.lorentz 2 := (k⁻¹ : Causal.Flat.isom 2).2
  have hdiff : ∀ a : Causal.Minkowski 2,
      radL (k⁻¹ • a) - radL (k⁻¹ • q0) = radL (L (a - q0)) := by
    intro a
    rw [← map_sub, Causal.Flat.isom_smul_def, Causal.Flat.isom_smul_def, Causal.Flat.isom_sub]
  set α : ℝ := radL (L ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 2)))) with hα
  set β : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    (radL.comp L.toLinearMap).comp (LinearMap.inr ℝ ℝ _) with hβ
  have hdec : ∀ (a : ℝ) (b : EuclideanSpace ℝ (Fin 2)),
      radL (L ((a, b) : Causal.Minkowski 2)) = a * α + β b := by
    intro a b
    have : ((a, b) : Causal.Minkowski 2) = a • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 2))) +
        ((0 : ℝ), b) := by ext <;> simp
    rw [this, map_add, map_add, map_smul, map_smul, smul_eq_mul, hα]
    rfl
  -- a direction of strict increase
  have hdir : ∃ e : EuclideanSpace ℝ (Fin 2), (c : ℝ) * |α| * ‖e‖ < β e := by
    set n : Causal.Minkowski 2 := ((1 : ℝ), EuclideanSpace.single 0 1) with hn
    set w := L.symm n with hw
    have hLw : L w = n := L.apply_symm_apply n
    have hφw : w.1 * α + β w.2 = 0 := by
      rw [← hdec, Prod.mk.eta, hLw, radL_apply]; simp [hn]
    have hQw : Causal.Flat.minkQ w = 0 := by
      rw [← Causal.Flat.lorentz.minkQ_apply hLl, hLw, Causal.Flat.minkQ, hn]; simp
    have hw0 : w.1 ≠ 0 := by
      intro h0
      have h2 : ‖w.2‖ ^ 2 = 0 := by rw [Causal.Flat.minkQ, h0] at hQw; linarith
      have h3 : w.2 = 0 := by simpa using h2
      have : w = 0 := Prod.ext h0 h3
      have hn0 : n = 0 := by rw [← hLw, this, map_zero]
      have := congrArg Prod.fst hn0
      simp [hn] at this
    have hnorm : ‖w.2‖ = |w.1| := by
      have h2 : ‖w.2‖ ^ 2 = w.1 ^ 2 := by rw [Causal.Flat.minkQ] at hQw; linarith
      rw [← sq_abs w.1] at h2
      exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2
    by_cases hα0 : α = 0
    · set m := L.symm ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 2))) with hm
      have h1 : m.1 * α + β m.2 = 1 := by
        rw [← hdec, Prod.mk.eta, hm, L.apply_symm_apply, radL_apply]; simp
      refine ⟨m.2, ?_⟩
      rw [hα0, mul_zero] at h1
      rw [hα0, abs_zero, mul_zero, zero_mul]; linarith
    · refine ⟨(-(α * w.1)) • w.2, ?_⟩
      rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_neg, hnorm, abs_mul]
      have hβw : β w.2 = -(w.1 * α) := by linarith
      rw [hβw]
      have hpos : 0 < |α| * |w.1| := mul_pos (abs_pos.2 hα0) (abs_pos.2 hw0)
      have hc1 : (c : ℝ) < 1 := by exact_mod_cast hc
      have e2 : -(α * w.1) * -(w.1 * α) = (|α| * |w.1|) ^ 2 := by
        rw [← abs_mul, sq_abs]; ring
      rw [e2]
      have : (c : ℝ) * |α| * (|α| * |w.1| * |w.1|) = c * (|α| * |w.1|) ^ 2 := by ring
      rw [this]
      exact mul_lt_of_lt_one_left (by positivity) hc1
  obtain ⟨e, he⟩ := hdir
  -- the points `x0' + s e` of the graph near `q0`
  set x0' := q0.2
  have hfc : ContinuousAt f x0' :=
    (hf.continuousOn.continuousAt (hU'.mem_nhds hq0U))
  have hpath : Tendsto (fun s : ℝ => x0' + s • e) (𝓝[>] 0) (𝓝 x0') := by
    have : Tendsto (fun s : ℝ => x0' + s • e) (𝓝 0) (𝓝 (x0' + (0 : ℝ) • e)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hgr' : Tendsto (fun x => ((f x, x) : Causal.Minkowski 2)) (𝓝 x0') (𝓝 q0) := by
    have h : Tendsto (fun x => ((f x, x) : Causal.Minkowski 2)) (𝓝 x0') (𝓝 (f x0', x0')) :=
      hfc.tendsto.prodMk_nhds tendsto_id
    rwa [show ((f x0', x0') : Causal.Minkowski 2) = q0 from Prod.ext hq0f.symm rfl] at h
  have hO' : IsOpen (k • (O : Set (Causal.Minkowski 2))) := O.isOpen.smul k
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), x0' + s • e ∈ U' ∧
      ((f (x0' + s • e), x0' + s • e) : Causal.Minkowski 2) ∈ k • (O : Set _) ∧ 0 < s := by
    filter_upwards [hpath.eventually (hU'.mem_nhds hq0U),
      (hgr'.comp hpath).eventually (hO'.mem_nhds hq0O), self_mem_nhdsWithin] with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨s, hsU, hsO, hs⟩ := hev.exists
  have hle := key _ hsU hsO
  have hq0R : radL (k⁻¹ • q0) = R := by rw [hq0def, inv_smul_smul, hℓ0]
  have hd := hdiff ((f (x0' + s • e), x0' + s • e) : Causal.Minkowski 2)
  have hsub' : ((f (x0' + s • e), x0' + s • e) : Causal.Minkowski 2) - q0 =
      ((f (x0' + s • e) - f x0', s • e) : Causal.Minkowski 2) := by
    ext
    · simp [x0', hq0f]
    · simp [x0']
  rw [hsub', hdec, β.map_smul, smul_eq_mul, hq0R] at hd
  have hlip : |f (x0' + s • e) - f x0'| ≤ c * (s * ‖e‖) := by
    have := hf.dist_le_mul _ hsU _ hq0U
    rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs] at this
  have h1 : -( (c : ℝ) * (s * ‖e‖)) * |α| ≤ (f (x0' + s • e) - f x0') * α := by
    have := abs_mul (f (x0' + s • e) - f x0') α
    have h3 : -|(f (x0' + s • e) - f x0') * α| ≤ (f (x0' + s • e) - f x0') * α := neg_abs_le _
    nlinarith [abs_nonneg α]
  have h2 : s * ((c : ℝ) * |α| * ‖e‖) < s * β e := mul_lt_mul_of_pos_left he hs
  linarith

/-! ### §3 The chart lemma in `FlatE0 N` -/

variable {N : Causal.Flat.FlatSpacetime.{0} 2}

/-- **The chart lemma in `FlatE0 N`** (the analogue of `SpearSurgeryDatum.eventually_regChart`):
near a point `x ∈ W` of the slit sector of `y`, an `𝔼₀`-morphism `ψ` into a flat `N`, read in the
chart of `N` at `ψ x`, is `g •` the sector chart, on an open neighbourhood `U ⊆ W ∩ sector`. -/
theorem flatE0_regChart {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hW : IsOpen W) (hψ : IsE0Mor ψ W)
    {y : E0} (hy : y.2 ≠ 0) {x : E0Y} (hxW : x ∈ W) (hxs : x ∈ paperInY '' sector y) :
    ∃ (U : Set E0Y) (g : Causal.Flat.isom 2), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∩ paperInY '' sector y ∧
      (∀ u ∈ U, (show N from ψ u) ∈ (chartAt (Causal.Minkowski 2) (show N from ψ x)).source) ∧
      ∀ u ∈ U, chartAt (Causal.Minkowski 2) (show N from ψ x) (show N from ψ u) =
        g • sectorChartY y hy u := by
  set κ := chartAt E0Y (ψ x) with hκ
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  set P : Set E0Y := paperInY '' sector y with hP
  have hPo : IsOpen P := isOpen_paperInY_image (isOpen_sector y)
  set V : Set E0Y := (W ∩ P) ∩ ψ ⁻¹' κ.source with hV
  have hVo : IsOpen V :=
    (hψc.mono inter_subset_left).isOpen_inter_preimage (hW.inter hPo) κ.open_source
  have hxV : x ∈ V := ⟨⟨hxW, hxs⟩, mem_chart_source E0Y (ψ x)⟩
  set U := connectedComponentIn V x with hU
  have hUo : IsOpen U := hVo.connectedComponentIn
  have hUV : U ⊆ V := connectedComponentIn_subset _ _
  have hUc : IsPreconnected U := isPreconnected_connectedComponentIn
  have hxU : x ∈ U := mem_connectedComponentIn hxV
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
  obtain ⟨g, hg⟩ := exists_eqOn_sectorSmulInl hy hUo hUc ⟨x, hxU⟩
    (fun x hx => (hUV hx).1.2) hfS hfinl
  refine ⟨U, g, hUo, hxU, fun u hu => (hUV hu).1, fun u hu => ?_, fun u hu => ?_⟩
  · have h := (hUV hu).2
    have e : κ.source = (chartAt (Causal.Minkowski 2) (show N from ψ x)).source := by
      show ((chartAt (Causal.Minkowski 2) (show N from ψ x)).trans e0Inl).source = _
      simp only [OpenPartialHomeomorph.trans_source, e0Inl_source, preimage_univ, inter_univ]
    rw [← e]; exact h
  · have h := hg hu
    rw [sectorSmulInl_apply] at h
    exact Sum.inl_injective h

/-! ### §4 The trace -/

/-- The trace `g(r, θ) = τ_Σ(r e^{iθ})` on the strip. -/
noncomputable def traceFun (τS : ℂ → ℝ) (p : ℝ × ℝ) : ℝ :=
  τS ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))

/-- **The trace is `2π`-periodic.** -/
theorem traceFun_periodic (τS : ℂ → ℝ) (r θ : ℝ) :
    traceFun τS (r, θ + 2 * π) = traceFun τS (r, θ) := by
  simp only [traceFun]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

open BTZIsom
/-- `‖r e^{iθ}‖ = r`. -/
theorem norm_polar {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

/-- `arg(r e^{iθ} / r₀ e^{iθ₀}) = θ − θ₀` for `|θ − θ₀| < π`. -/
theorem arg_div_polar {r r0 θ θ0 : ℝ} (hr : 0 < r) (hr0 : 0 < r0) (hθ : |θ - θ0| < π) :
    Complex.arg (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
      ((r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I))) = θ - θ0 := by
  have e : ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
      ((r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I)) =
      ((r / r0 : ℝ) : ℂ) * Complex.exp (((θ - θ0 : ℝ) : ℂ) * Complex.I) := by
    have h0 : Complex.exp ((θ0 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hr0' : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    push_cast
    rw [sub_mul, Complex.exp_sub]
    field_simp
  rw [e, Complex.arg_real_mul _ (div_pos hr hr0)]
  rw [abs_lt] at hθ
  have h1 : θ - θ0 ∈ Set.Ioc (-π) π := ⟨by linarith, by linarith⟩
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I h1

/-- `‖w‖ e^{i(θ₀ + arg(w / r₀e^{iθ₀}))} = w`. -/
theorem polar_arg_div {r0 θ0 : ℝ} (hr0 : 0 < r0) {w : ℂ} :
    ((‖w‖ : ℝ) : ℂ) * Complex.exp (((θ0 + Complex.arg (w / ((r0 : ℂ) *
      Complex.exp ((θ0 : ℂ) * Complex.I))) : ℝ) : ℂ) * Complex.I) = w := by
  set z0 : ℂ := (r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I) with hz0
  have hz0n : z0 ≠ 0 := mul_ne_zero (by exact_mod_cast hr0.ne') (Complex.exp_ne_zero _)
  have hnz : ‖z0‖ = r0 := norm_polar hr0.le θ0
  have h := Complex.norm_mul_exp_arg_mul_I (w / z0)
  rw [norm_div, hnz] at h
  have e : w = z0 * (w / z0) := by field_simp
  conv_rhs => rw [e, ← h]
  push_cast
  rw [add_mul, Complex.exp_add, hz0]
  have hr0' : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  field_simp

/-- The trace is continuous on the closed strip. -/
theorem continuous_traceFun {R : ℝ} {τS : ℂ → ℝ} (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R}) :
    Continuous fun q : Strip R => traceFun τS q.1 := by
  refine hc.comp_continuous (by fun_prop) fun q => ?_
  rw [mem_setOf_eq, norm_polar q.2.1.le]
  exact q.2

/-- The development of a graph continuous on the strip is continuous. -/
theorem continuous_graphDev {g : ℝ × ℝ → ℝ} {R : ℝ} (hg : Continuous fun q : Strip R => g q.1) :
    Continuous (graphDev g R) :=
  continuous_btzPaperDev.comp (hg.prodMk (by fun_prop))

/-- **The development of a continuous graph is an embedding of the strip**: `r = q₀ − q₁` and
`θ = −q₂ / r` read `(r, θ)` back off `D(g(r, θ), r, θ)`. -/
theorem isEmbedding_graphDev {g : ℝ × ℝ → ℝ} {R : ℝ} (hg : Continuous fun q : Strip R => g q.1) :
    IsEmbedding (graphDev g R) := by
  set F := graphDev g R
  set F' : Strip R → {q : Causal.Minkowski 2 // 0 < radL q} := fun p =>
    ⟨F p, by rw [radL_apply, graphDev_rad]; exact p.2.1⟩ with hF'
  have hF'c : Continuous F' := (continuous_graphDev hg).subtype_mk _
  have hradc : Continuous radL := radL.continuous_of_finiteDimensional
  set lam : {q : Causal.Minkowski 2 // 0 < radL q} → ℝ × ℝ := fun q =>
    (radL q.1, -(q.1.2 1) / radL q.1) with hlam
  have hlamc : Continuous lam := by
    refine (hradc.comp continuous_subtype_val).prodMk ?_
    refine Continuous.div ?_ (hradc.comp continuous_subtype_val) fun q => q.2.ne'
    exact ((PiLp.continuous_apply 2 _ (1 : Fin 2)).comp
      (continuous_snd.comp continuous_subtype_val)).neg
  have hcomp : lam ∘ F' = Subtype.val := by
    funext p
    have hr : radL (F p) = p.1.1 := by rw [radL_apply, graphDev_rad]
    simp only [comp_apply, hlam, hF', hr]
    refine Prod.ext rfl ?_
    simp only [F, graphDev, btzPaperDev, graphMap]
    simp
    field_simp [p.2.1.ne']
  have hF'e : IsEmbedding F' := IsEmbedding.of_comp hF'c hlamc (hcomp ▸ IsEmbedding.subtypeVal)
  exact IsEmbedding.subtypeVal.comp hF'e

/-- **The development read in a sector chart**: on the half-turn `|θ − θ₀| < π` around the angle
`θ₀` of `z₀ = r₀ e^{iθ₀}`, the development of a graph is the sector chart of `y` (`y.2 = z₀`) at the
point `(g(r, θ), r e^{iθ})`, moved by the isometry `gShift 0 (θ₀ − arg z₀)`
(`BTZIsom.btzPaperDev_shift_angle`). -/
theorem graphDev_eq_shift_sectorChartY {g : ℝ × ℝ → ℝ} {R r0 θ0 : ℝ} (hr0 : 0 < r0) {y : E0}
    (hy2 : y.2 = (r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I)) (hy : y.2 ≠ 0)
    (q : Strip R) (hq : |q.1.2 - θ0| < π) :
    graphDev g R q = gShift 0 (θ0 - Complex.arg y.2) •
      sectorChartY y hy (paperInY ((g q.1, (q.1.1 : ℂ) * Complex.exp ((q.1.2 : ℂ) * Complex.I)) :
        E0)) := by
  rw [sectorChartY_paperInY, ← btzPaperDev_shift_angle]
  have hrad : rad ((g q.1, (q.1.1 : ℂ) * Complex.exp ((q.1.2 : ℂ) * Complex.I)) : E0) = q.1.1 :=
    norm_polar q.2.1.le _
  have hang : angle y ((g q.1, (q.1.1 : ℂ) * Complex.exp ((q.1.2 : ℂ) * Complex.I)) : E0) =
      Complex.arg y.2 + (q.1.2 - θ0) := by
    simp only [angle]
    rw [hy2, arg_div_polar q.2.1 hr0 hq, ← hy2]
  rw [hrad, hang]
  simp only [graphDev, graphMap, add_zero]
  congr 1
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only
  ring

/-- The development over the open strip `(0, R) × ℝ`. -/
noncomputable def openGraphDev (g : ℝ × ℝ → ℝ) (R : ℝ) (p : {p : ℝ × ℝ // 0 < p.1 ∧ p.1 < R}) :
    Causal.Minkowski 2 :=
  btzPaperDev (graphMap g p.1)

/-- **Local spacelike structure at every point `r < R`**: the development of the trace, on an open
`U ⊆ {r < R}` around the point, is an embedding onto `k • (κ(Σ) ∩ V)`, `κ` the chart of `N` at
the point of `Σ`, `k ∈ Isom(𝐌³)` (`flatE0_regChart`, `graphDev_eq_shift_sectorChartY`),
hence spacelike Lipschitz (`IsSpacelikeLipschitzIn.smul`, `isSpacelikeLipschitzIn_inter`). -/
theorem traceDev_locally {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hW : IsOpen W)
    (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2))
    (p : Strip R) (hp : p.1.1 < R) :
    ∃ (U : Opens (Strip R)) (V : Opens (Causal.Minkowski 2)), p ∈ U ∧ (∀ q ∈ U, q.1.1 < R) ∧
      IsEmbedding ((U : Set (Strip R)).restrict (graphDev (traceFun τS) R)) ∧
      Causal.Flat.IsSpacelikeLipschitzIn V (graphDev (traceFun τS) R '' U) := by
  classical
  rcases p with ⟨⟨r0, θ0⟩, hr0, hr0R'⟩
  simp only at hp hr0
  set g := traceFun τS with hgdef
  set F := graphDev g R with hFdef
  have hgc : Continuous fun q : Strip R => g q.1 := continuous_traceFun hc
  have hFc : Continuous F := continuous_graphDev hgc
  set z0 : ℂ := (r0 : ℂ) * Complex.exp ((θ0 : ℂ) * Complex.I) with hz0
  have hz0n : ‖z0‖ = r0 := norm_polar hr0.le θ0
  set x0 : E0 := (τS z0, z0) with hx0
  have hy : x0.2 ≠ 0 := by
    intro h; have := congrArg norm h; rw [norm_zero] at this
    rw [show x0.2 = z0 from rfl, hz0n] at this; exact hr0.ne' this
  -- the open part `{f > v, 0 < r < R}` of the blunt spear
  set B : Set E0 := {x | v < fcoord x ∧ 0 < rad x ∧ rad x < R} with hB
  have hradc : Continuous rad := continuous_norm.comp continuous_snd
  have hBo : IsOpen B :=
    ((isOpen_lt continuous_const (continuous_fst.sub (hradc.div_const 2))).inter
      ((isOpen_lt continuous_const hradc).inter (isOpen_lt hradc continuous_const)))
  have hBsub : B ⊆ bspear v R := fun x hx => ⟨hx.1.le, hx.2.1, hx.2.2.le⟩
  have hgB : ∀ q : Strip R, q.1.1 < R →
      ((g q.1, (q.1.1 : ℂ) * Complex.exp ((q.1.2 : ℂ) * Complex.I)) : E0) ∈ B := by
    intro q hq
    have hn := norm_polar q.2.1.le q.1.2
    have h := hpos _ (by rw [hn]; exact q.2.1) (by rw [hn]; exact q.2.2)
    rw [hn] at h
    refine ⟨?_, ?_, ?_⟩
    · simp only [fcoord, rad]; rw [hn]; simp only [hgdef, traceFun]; linarith
    · simp only [rad]; rw [hn]; exact q.2.1
    · simp only [rad]; rw [hn]; exact hq
  have hx0B : x0 ∈ B := hgB ⟨(r0, θ0), hr0, hr0R'⟩ hp
  have hx0W : paperInY x0 ∈ W := hsub ⟨x0, hBsub hx0B, rfl⟩
  obtain ⟨U1, h, hU1o, hx0U1, hU1sub, hU1src, hU1eq⟩ :=
    flatE0_regChart (hW.inter (isOpen_paperInY_image hBo))
      (Causal.CBG.liftPropOn_mono_of_le hW (hW.inter (isOpen_paperInY_image hBo)) hψ
        (fun y hy => hy.1)) hy
      ⟨hx0W, x0, hx0B, rfl⟩ ⟨x0, mem_sector_self hy, rfl⟩
  set s0 : N := ψ (paperInY x0) with hs0def
  set κ := chartAt (Causal.Minkowski 2) s0 with hκ
  have hs0 : s0 ∈ Sig := (hgraph x0 (hBsub hx0B)).2 rfl
  obtain ⟨V0, hV0, -, hV0S⟩ := hSig s0 hs0
  set sC := sectorChartY x0 hy with hsC
  have hU1C : U1 ⊆ sC.source := fun u hu => image_sector_subset_source hy (hU1sub hu).2
  set O : Set (Causal.Minkowski 2) := h • (sC '' U1) with hO
  have hOo : IsOpen O := (sC.isOpen_image_of_subset_source hU1o hU1C).smul h
  set V : Opens (Causal.Minkowski 2) := V0 ⊓ ⟨O, hOo⟩ with hV
  set Q := gShift 0 (θ0 - Complex.arg x0.2) with hQ
  set k := Q * h⁻¹ with hk
  set Φ : Strip R → E0 := fun q => (g q.1, (q.1.1 : ℂ) * Complex.exp ((q.1.2 : ℂ) * Complex.I))
    with hΦ
  have hΦc : Continuous Φ := hgc.prodMk (by fun_prop)
  have hFq : ∀ q : Strip R, |q.1.2 - θ0| < π → F q = Q • sC (paperInY (Φ q)) :=
    fun q hq => graphDev_eq_shift_sectorChartY hr0 rfl hy q hq
  have hkF : ∀ q : Strip R, |q.1.2 - θ0| < π → paperInY (Φ q) ∈ U1 →
      k⁻¹ • F q = κ (ψ (paperInY (Φ q))) := by
    intro q hq hu
    rw [hFq q hq, hU1eq _ hu, hk, mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]
  set Us : Set (Strip R) := {q | q.1.1 < R ∧ |q.1.2 - θ0| < π ∧ paperInY (Φ q) ∈ U1 ∧
    k⁻¹ • F q ∈ (V0 : Set (Causal.Minkowski 2))} with hUs
  have hUso : IsOpen Us := by
    refine (isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const).inter
      ((isOpen_lt ((continuous_snd.comp continuous_subtype_val).sub continuous_const).abs
        continuous_const).inter ((hU1o.preimage (continuous_paperInY.comp hΦc)).inter
          (V0.isOpen.preimage ((continuous_const_smul _).comp hFc))))
  have hmem : (⟨(r0, θ0), hr0, hr0R'⟩ : Strip R) ∈ Us := by
    have h0 : |θ0 - θ0| < π := by rw [sub_self, abs_zero]; exact Real.pi_pos
    have hΦ0 : Φ ⟨(r0, θ0), hr0, hr0R'⟩ = x0 := rfl
    have hU0 : paperInY (Φ ⟨(r0, θ0), hr0, hr0R'⟩) ∈ U1 := by rw [hΦ0]; exact hx0U1
    refine ⟨hp, h0, hU0, ?_⟩
    rw [hkF _ h0 hU0, hΦ0]
    exact hV0
  refine ⟨⟨Us, hUso⟩, Causal.smulOpens k V, hmem, fun q hq => hq.1,
    (isEmbedding_graphDev hgc).comp IsEmbedding.subtypeVal, ?_⟩
  have himg : F '' Us =
      k • ((κ '' (Sig ∩ κ.source) ∩ (V0 : Set (Causal.Minkowski 2))) ∩ (V : Set _)) := by
    ext a
    constructor
    · rintro ⟨q, ⟨hqR, hqθ, hqU, hqV⟩, rfl⟩
      have hb := hBsub (hgB q hqR)
      have hsig : ψ (paperInY (Φ q)) ∈ Sig := (hgraph _ hb).2 rfl
      have e := hkF q hqθ hqU
      refine ⟨κ (ψ (paperInY (Φ q))), ⟨⟨⟨ψ (paperInY (Φ q)), ⟨hsig, hU1src _ hqU⟩, rfl⟩, ?_⟩,
        ?_, ?_⟩, ?_⟩
      · rw [← e]; exact hqV
      · rw [← e]; exact hqV
      · show κ (ψ (paperInY (Φ q))) ∈ O
        rw [hU1eq _ hqU]; exact ⟨sC (paperInY (Φ q)), ⟨_, hqU, rfl⟩, rfl⟩
      · show k • κ (ψ (paperInY (Φ q))) = F q
        rw [← e, smul_inv_smul]
    · rintro ⟨b, ⟨⟨⟨s, ⟨hsS, hsκ⟩, rfl⟩, hbV0⟩, -, hbO⟩, rfl⟩
      obtain ⟨_, ⟨u, hu, rfl⟩, hub⟩ := hbO
      have hψu : κ (ψ u) = κ s := by rw [hU1eq _ hu]; exact hub
      have hsu : ψ u = s := κ.injOn (hU1src u hu) hsκ hψu
      obtain ⟨w, hwB, rfl⟩ := (hU1sub hu).1.2
      obtain ⟨w', hw's, hw'⟩ := (hU1sub hu).2
      have hww : w' = w := paperInY.injOn (by simp) (by simp) hw'
      subst hww
      have hw1 : w'.1 = τS w'.2 := (hgraph w' (hBsub hwB)).1 (hsu ▸ hsS)
      have hw0 : w'.2 ≠ 0 := ne_zero_of_mem_sector hw's
      set θ : ℝ := θ0 + Complex.arg (w'.2 / z0) with hθ
      have hpol : ((‖w'.2‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = w'.2 :=
        polar_arg_div hr0
      have hslit : w'.2 / z0 ∈ Complex.slitPlane := hw's
      have hθπ : |θ - θ0| < π := by
        rw [hθ, add_sub_cancel_left, abs_lt]
        refine ⟨?_, lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.1 hslit).1⟩
        exact Complex.neg_pi_lt_arg _
      set q : Strip R := ⟨(‖w'.2‖, θ), hwB.2.1, hwB.2.2.le⟩ with hqdef
      have hΦq : Φ q = w' := by
        simp only [hΦ, hqdef]
        rw [hpol]
        refine Prod.ext ?_ rfl
        simp only [hgdef, traceFun]
        rw [hpol, hw1]
      have hqU : paperInY (Φ q) ∈ U1 := by rw [hΦq]; exact hu
      have e := hkF q hθπ hqU
      refine ⟨q, ⟨hwB.2.2, hθπ, hqU, ?_⟩, ?_⟩
      · rw [e, hΦq, hsu]; exact hbV0
      · show F q = k • κ s
        rw [← hsu, ← hΦq, ← e, smul_inv_smul]
  show Causal.Flat.IsSpacelikeLipschitzIn _ (F '' Us)
  rw [himg]
  exact (isSpacelikeLipschitzIn_inter hV0S inf_le_left).smul
    (fun g => Causal.Flat.isom_strongMorphism g) k

/-- The open strip `(0, R) × ℝ`, included in the closed one. -/
def openStripIncl (R : ℝ) (p : {p : ℝ × ℝ // 0 < p.1 ∧ p.1 < R}) : Strip R := ⟨p.1, p.2.1, p.2.2.le⟩

/-- The open strip embeds in the closed one. -/
theorem isEmbedding_openStripIncl (R : ℝ) : IsEmbedding (openStripIncl R) :=
  IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal

/-- `openGraphDev` is `graphDev` on the open strip. -/
theorem openGraphDev_eq (g : ℝ × ℝ → ℝ) (R : ℝ) :
    openGraphDev g R = graphDev g R ∘ openStripIncl R := rfl

/-- **The trace develops spacelike over the open strip** (`(0, R) × ℝ`): the strongest true form
of the target (over the closed strip it is false, `not_spacelikeDevelopment_graphDev`). -/
theorem spacelikeDevelopment_openGraphDev {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) :
    Causal.Flat.SpacelikeDevelopment (openGraphDev (traceFun τS) R) := by
  have hemb : IsEmbedding (openGraphDev (traceFun τS) R) := by
    rw [openGraphDev_eq]
    exact (isEmbedding_graphDev (continuous_traceFun hc)).comp (isEmbedding_openStripIncl R)
  refine ⟨hemb.continuous, fun x => ?_⟩
  obtain ⟨U, V, hxU, hUR, -, hS⟩ :=
    traceDev_locally hW hsub hψ hSig hc hpos hgraph (openStripIncl R x) x.2.2
  refine ⟨U.comap ⟨openStripIncl R, (isEmbedding_openStripIncl R).continuous⟩, V, hxU,
    hemb.comp IsEmbedding.subtypeVal, ?_⟩
  have himg : openGraphDev (traceFun τS) R ''
      (U.comap ⟨openStripIncl R, (isEmbedding_openStripIncl R).continuous⟩ : Set _) =
      graphDev (traceFun τS) R '' U := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨openStripIncl R y, hy, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q.1, q.2.1, hUR q hq⟩, show openStripIncl R _ ∈ U from hq, rfl⟩
  rw [himg]; exact hS

/-- **The target, in its strongest true form.** In the setting of `lem_blunt_spear` (flat `N`,
a blunt spear chart `ψ` on `W ⊇ bspearY v R`), let `Σ ⊆ N` be spacelike Lipschitz and `τ_Σ`
continuous on the punctured closed disc, above the shaft (`v + ‖z‖/2 < τ_Σ z`), with
`ψ(paperInY x) ∈ Σ ↔ x.1 = τ_Σ x.2` on `bspear v R`. Then `g(r, θ) = τ_Σ(r e^{iθ})` is
`2π`-periodic, its development `graphDev g R` is a continuous embedding of the closed strip, it is
locally a spacelike Lipschitz hypersurface at every point with `r < R`, and its restriction to the
open strip is a `Causal.Flat.SpacelikeDevelopment`. That `graphDev g R` itself is one is false
for `R > 0` (`not_spacelikeDevelopment_graphDev`). -/
theorem trace_spacelikeDevelopment {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) :
    (∀ r θ, traceFun τS (r, θ + 2 * π) = traceFun τS (r, θ)) ∧
      IsEmbedding (graphDev (traceFun τS) R) ∧
      (∀ p : Strip R, p.1.1 < R → ∃ (U : Opens (Strip R)) (V : Opens (Causal.Minkowski 2)),
        p ∈ U ∧ (∀ q ∈ U, q.1.1 < R) ∧
        IsEmbedding ((U : Set (Strip R)).restrict (graphDev (traceFun τS) R)) ∧
        Causal.Flat.IsSpacelikeLipschitzIn V (graphDev (traceFun τS) R '' U)) ∧
      Causal.Flat.SpacelikeDevelopment (openGraphDev (traceFun τS) R) :=
  ⟨traceFun_periodic τS, isEmbedding_graphDev (continuous_traceFun hc),
    traceDev_locally hW hsub hψ hSig hc hpos hgraph,
    spacelikeDevelopment_openGraphDev hW hsub hψ hSig hc hpos hgraph⟩

/-- **`lem_blunt_spear`, followed by the trace** (`BTZ_1.tex:1601–1602`, the first half): for a
globally hyperbolic flat `N`, a Cauchy surface `Σ` that is spacelike Lipschitz, and a blunt spear
chart `ψ` of `ψ(bspearY v R)`, the sub-spear `R′` and the graph `τ_Σ` of
`GX.E0BluntSpear.lem_blunt_spear` have a trace `g(r, θ) = τ_Σ(r e^{iθ})` as in
`trace_spacelikeDevelopment`. -/
theorem lem_blunt_spear_trace (hGH : Causal.Flat.GH N) {Sig : Set N}
    (hSig : (Causal.Flat.flatCausality 2 N).IsCauchySurface Sig)
    (hSigL : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {v R : ℝ} {W : Set E0Y}
    {ψ : E0Y → FlatE0 N} (hR : 0 < R) (hW : IsOpen W) (hsub : bspearY v R ⊆ W)
    (hψ : IsE0Mor ψ W) (hinj : InjOn ψ W) :
    ∃ R', 0 < R' ∧ R' ≤ R ∧ IsBluntSpearNbhd R' (ψ '' bspearY v R') ∧
      ∃ τS : ℂ → ℝ, ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R'} ∧
        (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + R' / 2 < τS z) ∧
        (∀ x ∈ bspear v R', (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) ∧
        (∀ r θ, traceFun τS (r, θ + 2 * π) = traceFun τS (r, θ)) ∧
        IsEmbedding (graphDev (traceFun τS) R') ∧
        (∀ p : Strip R', p.1.1 < R' → ∃ (U : Opens (Strip R')) (V : Opens (Causal.Minkowski 2)),
          p ∈ U ∧ (∀ q ∈ U, q.1.1 < R') ∧
          IsEmbedding ((U : Set (Strip R')).restrict (graphDev (traceFun τS) R')) ∧
          Causal.Flat.IsSpacelikeLipschitzIn V (graphDev (traceFun τS) R' '' U)) ∧
        Causal.Flat.SpacelikeDevelopment (openGraphDev (traceFun τS) R') := by
  obtain ⟨R', hR'0, hR'R, hS, -, -, -, τS, hc, hpos, hgraph⟩ :=
    lem_blunt_spear hGH hSig hR hW hsub hψ hinj
  have hsub' : bspearY v R' ⊆ W :=
    (image_mono (show bspear v R' ⊆ bspear v R from
      fun x hx => ⟨hx.1, hx.2.1, hx.2.2.trans hR'R⟩)).trans hsub
  have hpos' : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R' → v + ‖z‖ / 2 < τS z := fun z hz0 hz =>
    lt_of_le_of_lt (by linarith) (hpos z hz0 hz)
  exact ⟨R', hR'0, hR'R, hS, τS, hc, hpos, hgraph,
    trace_spacelikeDevelopment hW hsub' hψ hSigL hc hpos' hgraph⟩

/-- **The trace develops spacelike over the open strip, in the corrected lemma's form**:
`Causal.Flat.SpacelikeDevelopment (graphDevOn g (openStrip R))`, the hypothesis `hF` of
`E0Surgery.lem_surface_complete_two_lipOn` with `Ω = openStrip R`, which contains the closed strip
`(0, R″] × ℝ` of every `R″ < R`. -/
theorem trace_spacelikeDevelopment_openStrip {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2)) :
    Causal.Flat.SpacelikeDevelopment (graphDevOn (traceFun τS) (openStrip R)) :=
  spacelikeDevelopment_openGraphDev hW hsub hψ hSig hc hpos hgraph

/-- **l.1602 assembled, up to completeness**: in the setting of `trace_spacelikeDevelopment`, for
every `0 < R″ < R`, if the pulled length of the trace over `(0, R″] × ℝ` is complete then
`τ_Σ(r e^{iθ}) → +∞` at the axis (`E0Surgery.lem_surface_complete_two_lipOn` with
`Ω = openStrip R`). The completeness is T-btz-trace-complete. -/
theorem trace_tendsto_atTop {v R R'' : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N}
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {Sig : Set N}
    (hSig : Causal.Flat.IsSpacelikeLipschitz 2 Sig) {τS : ℂ → ℝ}
    (hc : ContinuousOn τS {z | 0 < ‖z‖ ∧ ‖z‖ ≤ R})
    (hpos : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R → v + ‖z‖ / 2 < τS z)
    (hgraph : ∀ x ∈ bspear v R, (ψ (paperInY x) ∈ Sig ↔ x.1 = τS x.2))
    (hR'' : 0 < R'') (hR''R : R'' < R)
    (hcomp : CompleteSpace (Causal.Flat.PulledLength (graphDev (traceFun τS) R''))) :
    Tendsto (traceFun τS) (comap Prod.fst (𝓝[>] 0)) atTop :=
  lem_surface_complete_two_lipOn hR'' (traceFun_periodic τS)
    (fun p (hp : p ∈ stripSet R'') => (⟨hp.1, hp.2.trans_lt hR''R⟩ : p ∈ openStrip R))
    (trace_spacelikeDevelopment_openStrip hW hsub hψ hSig hc hpos hgraph) hcomp

end E0TraceDev

end GX
