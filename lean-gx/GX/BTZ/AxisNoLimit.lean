import GX.BTZ.BluntSpear
import GX.BTZ.Admissible

/-!
# A blunt spear chart into a flat spacetime has no limit at the axis along any curve

Target T-btz-axis-nolimit. Paper `btz` (`papers/btz/legacy/labeled/BTZ_1.tex`), § 3.1 and § 5.
Row (unmarked: an auxiliary of the row, not its statement; 0 `sorry`):

* `btzlem:blunt_spear_neighborhood` — `BTZ_1.tex:693–701`, read where the proof of
  `theo:BTZ_Cauchy-completness` uses it (`BTZ_1.tex:1601–1602`):
  `GX.E0AxisNoLimit.flat_curve_noLimit`. For a blunt spear chart `ψ = φ⁻¹` of positive radius into
  a flat `N` (the data of `GX.E0BluntSpear.lem_blunt_spear`), `ψ(γ s)` has **no limit** in `N` as
  `s → 0⁺`, for **every** continuous curve `γ` of the blunt spear whose radius tends to `0`.
  Dispatch form `flat_axis_noLimit_Icc` (`γ : (0, 1] → bspear v R`, time in `[a₁, a₂]`, `v < a₁`)
  and `flat_axis_noLimit` (without the height bounds, which are not needed). The strict
  `GX.E0BluntSpear.flat_infall_noLimit_of_pos` (one in-falling ray, `v < a`) is the special case
  `flat_infall_noLimit_of_le`, which also allows `a = v`.

> By Lemma \ref{lem:blunt_spear_neighborhood}, one can reduce the size of $\S$ in such a way
> $\phi(\Sigma_0\cap \S)$ is the graph of a some function $\tau_0:\mathbb D_R^*\rightarrow \RR$
> in $\mass{0}$ with $\tau_0$. Since $\Sigma_0$ is complete, by Lemma \ref{lem:surface_complete}
> $ \lim_{(\r,\theta)\rightarrow 0}\tau_0(\r,\theta) = +\infty$. (l.1601–1602)

The second sentence needs exactly this file: the broken line of `lem_surface_complete_two_lip`'s
proof is a curve of the trace `τ₀` of finite length with radius `→ 0` and bounded height; its
image in a complete `Σ₀` would converge in `N`, and `flat_curve_noLimit` says it cannot.

## Hypothesis checklist

| hypothesis (the roadmap's statement) | here |
|---|---|
| `N` flat, `ψ`, `W`, `v`, `R` as in `lem_blunt_spear`, `0 < R` | ✓ carried: `IsOpen W`, `bspearY v R ⊆ W`, `IsE0Mor ψ W`, `0 < R`; injectivity of `ψ` is not used (`0 < R` is needed: `GX.E0BluntSpear.not_flat_infall_noLimit`) |
| `γ : (0, 1] → bspear v R` continuous | ⚠ weakened: continuous on some `(0, δ)`, off the axis (`0 < rad`) and with `v ≤ f = τ − r/2`; `rad ≤ R` is not assumed |
| `rad (γ s) → 0` as `s → 0⁺` | ✓ carried |
| time coordinate `(γ s).1 ∈ [a₁, a₂]`, `v < a₁` | ⚠ weakened: not assumed (`flat_axis_noLimit_Icc` carries and ignores them); convergence of `ψ ∘ γ` would itself bound the developed time `τ + ½ r θ²` |
| conclusion: `ψ (paperInY (γ s))` has no limit in `N` | ✓ for every `q : N`, `¬ Tendsto … (𝓝[>] 0) (𝓝 q)` |

## SCOPE (disclosed)

* Method (the strict in-falling proof, carried to the universal cover). Suppose `ψ(γ s) → q`, `κ`
  the chart of `N` at `q`. On the universal cover `(τ, r, θ) ↦ (τ, r e^{iθ})` (`cov`), the set
  `Õ` of points with `r > 0` that `ψ ∘ cov` sends into `W ∩ ψ⁻¹(dom κ)` is open and invariant under
  `θ ↦ θ + 2πk`. Local rigidity in slit sectors (`E0.exists_eqOn_sectorSmulInl`, the angle shift
  `BTZIsom.btzPaperDev_shift_angle`), spread by connectedness with `BTZAdm.isom_eq_of_eqOn`
  and `BTZAdm.isOpenMap_btzPaperDev_restrict`, gives one `g` with `κ ∘ ψ ∘ cov = g • D` on the
  component `Ũ` of `Õ` through one lift of the curve (`exists_eqOn_smul_dev`); the tail of `γ`
  lifts into `Ũ` (an open–closed argument with the local sections `sect`). The developed curve
  `D(τ, r, θ̃)` converges, so (null coordinates `(2τ + rθ̃² − r, r, −rθ̃)`) `rθ̃ → 0`, since
  `(rθ̃)² = r(2τ + rθ̃² − 2τ) ≤ r(u + r − 2v)`. At one late lift `(τ₀, r, θ̃)` the vertical segment
  up to `τ₀ + ½rπ²` and the arc `θ ↦ (τ₀ + ½rθ̃² + ½rπ² − ½rθ², r, θ)`, `|θ| ≤ max(|θ̃|, π)`, stay
  in the blunt spear and develop into `g⁻¹ • dom κ⁻¹`, so a closure argument puts them in `Ũ`.
  The arc's points at `θ = ±π` have one image in `𝔼₀` but developments differing by the
  parabolic holonomy (`btzPaperDev_add_pi_ne`): a contradiction.
* The file has no `sorry` and no axiom beyond mathlib's three.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal (imports
`Causal.*` through `GX.BTZ.BluntSpear`, DEC-33).
-/

namespace GX

namespace E0AxisNoLimit

open Set Filter Topology Function TopologicalSpace
open scoped Real
open E0 E0CBG E0Spear E0BluntSpear E0AbsMax

/-- **The universal-cover parametrisation** of `𝔼₀ ∖ axis`: `(τ, r, θ) ↦ (τ, r e^{iθ})`. -/
noncomputable def cov (p : ℝ × ℝ × ℝ) : E0 :=
  (p.1, (p.2.1 : ℂ) * Complex.exp (p.2.2 * Complex.I))

theorem continuous_cov : Continuous cov := by
  unfold cov; fun_prop

/-- `cov` is invariant under the deck translations `θ ↦ θ + 2πk`. -/
theorem cov_add (p : ℝ × ℝ × ℝ) (k : ℤ) : cov (p.1, p.2.1, p.2.2 + 2 * π * k) = cov p := by
  simp only [cov]
  congr 2
  rw [show ((p.2.2 + 2 * π * k : ℝ) : ℂ) * Complex.I = p.2.2 * Complex.I + k * (2 * π * Complex.I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem rad_cov {p : ℝ × ℝ × ℝ} (hp : 0 ≤ p.2.1) : rad (cov p) = p.2.1 := by
  simp only [rad, cov, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Two lifts of one point off the axis differ by a deck translation `θ ↦ θ + 2πk`. -/
theorem exists_eq_add_of_cov_eq {p p' : ℝ × ℝ × ℝ} (hp : 0 < p.2.1) (hp' : 0 < p'.2.1)
    (h : cov p = cov p') : ∃ k : ℤ, p' = (p.1, p.2.1, p.2.2 + 2 * π * k) := by
  have h1 : p.1 = p'.1 := by
    have := congrArg (fun x : E0 => x.1) h
    simpa [cov] using this
  have hr : p.2.1 = p'.2.1 := by
    have := congrArg rad h
    rwa [rad_cov hp.le, rad_cov hp'.le] at this
  have h2 := congrArg Prod.snd h
  simp only [cov] at h2
  rw [hr] at h2
  have h3 := mul_left_cancel₀ (by exact_mod_cast hp'.ne') h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3.symm
  refine ⟨n, ?_⟩
  have hθ : p'.2.2 = p.2.2 + 2 * π * n := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  ext <;> simp [h1, hr, hθ]

/-- **The local section of `cov` around the angle `θ`**:
`w ↦ (w.1, ‖w.2‖, θ + arg (w.2 e^{-iθ}))`. -/
noncomputable def sect (θ : ℝ) (w : E0) : ℝ × ℝ × ℝ :=
  (w.1, ‖w.2‖, θ + Complex.arg (w.2 * Complex.exp (-(θ * Complex.I))))

/-- `sect θ` is a section of `cov` (everywhere: on the axis both sides are `(τ, 0)`). -/
theorem cov_sect (θ : ℝ) (w : E0) : cov (sect θ w) = w := by
  simp only [cov, sect]
  refine Prod.ext rfl ?_
  simp only
  set z := w.2 * Complex.exp (-(θ * Complex.I)) with hz
  have hz' : w.2 = z * Complex.exp (θ * Complex.I) := by
    rw [hz, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hn : ‖w.2‖ = ‖z‖ := by
    rw [hz, norm_mul]; simp [Complex.norm_exp]
  rw [hn]
  push_cast
  rw [add_mul, Complex.exp_add, ← mul_assoc, mul_right_comm, Complex.norm_mul_exp_arg_mul_I, ← hz']

theorem sect_cov {p : ℝ × ℝ × ℝ} (hp : 0 < p.2.1) : sect p.2.2 (cov p) = p := by
  have hπ := Real.pi_pos
  simp only [sect, cov]
  have hz : (p.2.1 : ℂ) * Complex.exp (p.2.2 * Complex.I) * Complex.exp (-(p.2.2 * Complex.I)) =
      (p.2.1 : ℂ) := by
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  rw [hz, Complex.arg_ofReal_of_nonneg hp.le, add_zero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `sect θ` is continuous at a point `(τ, r e^{iθ})`, `r > 0`. -/
theorem continuousAt_sect_cov {p : ℝ × ℝ × ℝ} (hp : 0 < p.2.1) :
    ContinuousAt (sect p.2.2) (cov p) := by
  have hz : (cov p).2 * Complex.exp (-(p.2.2 * Complex.I)) = (p.2.1 : ℂ) := by
    simp only [cov]
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hslit : (cov p).2 * Complex.exp (-(p.2.2 * Complex.I)) ∈ Complex.slitPlane := by
    rw [hz]; exact Complex.ofReal_mem_slitPlane.2 hp
  unfold sect
  refine continuousAt_fst.prodMk (continuous_snd.norm.continuousAt.prodMk
    (continuousAt_const.add (ContinuousAt.comp (g := Complex.arg)
      (f := fun w : E0 => w.2 * Complex.exp (-(p.2.2 * Complex.I)))
      (Complex.continuousAt_arg hslit) ?_)))
  exact (continuous_snd.mul continuous_const).continuousAt

section Rigid

variable {N : Causal.Flat.FlatSpacetime.{0} 2} {W : Set E0Y} {ψ : E0Y → FlatE0 N}

/-- **Rigidity on a piece of a slit sector** (the first half of the strict
`flat_infall_noLimit_of_pos`): on a non-empty preconnected open `U ⊆ W` of the slit sector around
`y` that `ψ` maps into the domain of the chart `κ` of `N` at `q`, `κ ∘ ψ = g • sectorChartY y`. -/
theorem exists_eq_smul_sectorChartY (hW : IsOpen W) (hψ : IsE0Mor ψ W) (q : FlatE0 N) {y : E0}
    (hy : y.2 ≠ 0) {U : Set E0Y} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUW : U ⊆ W) (hUs : U ⊆ paperInY '' sector y)
    (hUκ : ∀ x ∈ U, ψ x ∈ (chartAt E0Y q).source) :
    ∃ g : Causal.Flat.isom 2, ∀ x ∈ U,
      chartAt (Causal.Minkowski 2) (show N from q) (ψ x) = g • sectorChartY y hy x := by
  set κ := chartAt E0Y q with hκ
  set f : E0Y → E0Y := κ ∘ ψ with hf
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hψU : IsE0Mor ψ U :=
    Causal.CBG.liftPropOn_mono_of_le hW hUo hψ (fun y hy => hUW hy)
  have hfU : IsE0Mor f U :=
    Causal.CBG.liftPropOn_comp hUo κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hψU
      (fun y hy => hUκ y hy)
  have hfS : ∀ x ∈ U, e0Groupoid.IsLocalStructomorphWithinAt f U x := by
    intro x hx
    have h := (hfU x hx).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
      preimage_id_eq] at h
    exact h
  have hfinl : ∀ x ∈ U, f x ∈ range Sum.inl := fun x _ => ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := exists_eqOn_sectorSmulInl hy hUo hUc hUne hUs hfS hfinl
  refine ⟨g, fun x hx => ?_⟩
  have h := hg hx
  rw [sectorSmulInl_apply] at h
  exact Sum.inl_injective h


theorem arg_real_mul_exp {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-π) π) :
    Complex.arg ((r : ℂ) * Complex.exp (θ * Complex.I)) = θ := by
  rw [Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> linarith [hθ.1, hθ.2]

theorem cov_div_exp (p : ℝ × ℝ × ℝ) (θ : ℝ) :
    (cov p).2 / Complex.exp (θ * Complex.I) = (p.2.1 : ℂ) * Complex.exp ((p.2.2 - θ : ℝ) * Complex.I) := by
  simp only [cov]
  rw [mul_div_assoc, ← Complex.exp_sub]
  push_cast; ring_nf

/-- **Local rigidity on the universal cover**: near a point `p = (τ, r, θ)`, `r > 0`, whose image
`ψ(τ, r e^{iθ})` lies in the domain of the chart `κ` of `N` at `q`, `κ ∘ ψ ∘ cov = g • D` for one
`g`, `D = btzPaperDev` the developing map. -/
theorem eventually_eq_smul_dev (hW : IsOpen W) (hψ : IsE0Mor ψ W) (q : FlatE0 N)
    {p : ℝ × ℝ × ℝ} (hp : 0 < p.2.1) (hpW : paperInY (cov p) ∈ W)
    (hpκ : ψ (paperInY (cov p)) ∈ (chartAt E0Y q).source) :
    ∃ g : Causal.Flat.isom 2, ∀ᶠ p' in 𝓝 p,
      chartAt (Causal.Minkowski 2) (show N from q) (ψ (paperInY (cov p'))) =
        g • btzPaperDev p' := by
  have hπ := Real.pi_pos
  set y : E0 := ((0 : ℝ), Complex.exp (p.2.2 * Complex.I)) with hydef
  have hy : y.2 ≠ 0 := Complex.exp_ne_zero _
  set κ := chartAt E0Y q with hκ
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  set V : Set E0Y := (W ∩ paperInY '' sector y) ∩ ψ ⁻¹' κ.source with hV
  have hVo : IsOpen V := (hψc.mono inter_subset_left).isOpen_inter_preimage
    (hW.inter (isOpen_paperInY_image (isOpen_sector y))) κ.open_source
  have hsec : ∀ p' : ℝ × ℝ × ℝ, 0 < p'.2.1 → p'.2.2 - p.2.2 ∈ Ioo (-π) π →
      cov p' ∈ sector y ∧ angle y (cov p') = p'.2.2 + (Complex.arg y.2 - p.2.2) := by
    intro p' hp' hθ
    have h1 : (cov p').2 / y.2 = (p'.2.1 : ℂ) * Complex.exp ((p'.2.2 - p.2.2 : ℝ) * Complex.I) :=
      cov_div_exp p' p.2.2
    have h2 := arg_real_mul_exp hp' hθ
    refine ⟨?_, ?_⟩
    · show (cov p').2 / y.2 ∈ Complex.slitPlane
      rw [h1, Complex.mem_slitPlane_iff_arg, h2]
      exact ⟨hθ.2.ne, mul_ne_zero (by exact_mod_cast hp'.ne') (Complex.exp_ne_zero _)⟩
    · show Complex.arg y.2 + Complex.arg ((cov p').2 / y.2) = _
      rw [h1, h2]; ring
  have hθ0 : p.2.2 - p.2.2 ∈ Ioo (-π) π := by rw [sub_self]; exact ⟨by linarith, hπ⟩
  have hpV : paperInY (cov p) ∈ V := ⟨⟨hpW, _, (hsec p hp hθ0).1, rfl⟩, hpκ⟩
  set U := connectedComponentIn V (paperInY (cov p)) with hU
  have hUo : IsOpen U := hVo.connectedComponentIn
  have hUV : U ⊆ V := connectedComponentIn_subset _ _
  obtain ⟨g, hg⟩ := exists_eq_smul_sectorChartY hW hψ q hy hUo isPreconnected_connectedComponentIn
    ⟨_, mem_connectedComponentIn hpV⟩ (fun x hx => (hUV hx).1.1) (fun x hx => (hUV hx).1.2)
    (fun x hx => (hUV hx).2)
  set c : ℝ := Complex.arg y.2 - p.2.2 with hc
  refine ⟨g * BTZIsom.gShift 0 c, ?_⟩
  have hcont : Continuous (fun p' => paperInY (cov p')) := continuous_paperInY.comp continuous_cov
  have hev1 : ∀ᶠ p' in 𝓝 p, paperInY (cov p') ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (hUo.mem_nhds (mem_connectedComponentIn hpV))
  have hev2 : ∀ᶠ p' in 𝓝 p, 0 < p'.2.1 :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds (lt_mem_nhds hp)
  have hev3 : ∀ᶠ p' in 𝓝 p, p'.2.2 - p.2.2 ∈ Ioo (-π) π :=
    ((continuous_snd.comp continuous_snd).sub continuous_const).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hθ0)
  filter_upwards [hev1, hev2, hev3] with p' h1 h2 h3
  rw [hg _ h1, sectorChartY_paperInY, (hsec p' h2 h3).2, rad_cov h2.le, mul_smul]
  congr 1
  have := BTZIsom.btzPaperDev_shift_angle 0 c p'
  rw [add_zero] at this
  rw [← this]
  rfl


/-- **Rigidity on the universal cover**: on a preconnected set `S` of `{r > 0}` which `ψ ∘ cov`
maps into `W ∩ ψ⁻¹(dom κ)`, `κ ∘ ψ ∘ cov = g • D` for a single `g ∈ Isom(𝐌³)`. -/
theorem exists_eqOn_smul_dev (hW : IsOpen W) (hψ : IsE0Mor ψ W) (q : FlatE0 N)
    {S : Set (ℝ × ℝ × ℝ)} (hSc : IsPreconnected S) (hSne : S.Nonempty)
    (hS : ∀ p ∈ S, 0 < p.2.1 ∧ paperInY (cov p) ∈ W ∧
      ψ (paperInY (cov p)) ∈ (chartAt E0Y q).source) :
    ∃ g : Causal.Flat.isom 2, ∀ p ∈ S,
      chartAt (Causal.Minkowski 2) (show N from q) (ψ (paperInY (cov p))) =
        g • btzPaperDev p := by
  set κN := chartAt (Causal.Minkowski 2) (show N from q) with hκN
  obtain ⟨p₀, hp₀⟩ := hSne
  obtain ⟨g, hg⟩ := eventually_eq_smul_dev hW hψ q (hS p₀ hp₀).1 (hS p₀ hp₀).2.1 (hS p₀ hp₀).2.2
  set A : Set (ℝ × ℝ × ℝ) :=
    interior {p' | κN (ψ (paperInY (cov p'))) = g • btzPaperDev p'} with hA
  have hpos : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.2.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  have hSA : S ⊆ A := by
    refine hSc.subset_of_closure_inter_subset isOpen_interior
      ⟨p₀, hp₀, mem_interior_iff_mem_nhds.2 hg⟩ ?_
    rintro p ⟨hpcl, hpS⟩
    obtain ⟨g', hg'⟩ := eventually_eq_smul_dev hW hψ q (hS p hpS).1 (hS p hpS).2.1 (hS p hpS).2.2
    set O : Set (ℝ × ℝ × ℝ) :=
      interior {p' | κN (ψ (paperInY (cov p'))) = g' • btzPaperDev p'} ∩ {p | 0 < p.2.1}
    have hOo : IsOpen O := isOpen_interior.inter hpos
    have hpO : p ∈ O := ⟨mem_interior_iff_mem_nhds.2 hg', (hS p hpS).1⟩
    obtain ⟨p₁, hp₁O, hp₁A⟩ := mem_closure_iff.1 hpcl O hOo hpO
    set O' : Set (ℝ × ℝ × ℝ) := O ∩ A
    have hO'o : IsOpen O' := hOo.inter isOpen_interior
    have himo : IsOpen (btzPaperDev '' O') := by
      have h := BTZAdm.isOpenMap_btzPaperDev_restrict hO'o (fun p hp => hp.1.2) univ isOpen_univ
      rwa [image_univ, show (range fun p : O' => btzPaperDev p.1) = btzPaperDev '' O' by
        ext m; simp] at h
    have hgg : g' = g := by
      refine BTZAdm.isom_eq_of_eqOn himo ⟨_, p₁, ⟨hp₁O, hp₁A⟩, rfl⟩ ?_
      rintro _ ⟨p', ⟨hp'O, hp'A⟩, rfl⟩
      have e1 : κN (ψ (paperInY (cov p'))) = g' • btzPaperDev p' :=
        (interior_subset hp'O.1 : p' ∈ {p' | _})
      have e2 : κN (ψ (paperInY (cov p'))) = g • btzPaperDev p' :=
        (interior_subset hp'A : p' ∈ {p' | _})
      exact e1.symm.trans e2
    rw [hgg] at hg'
    exact mem_interior_iff_mem_nhds.2 hg'
  exact ⟨g, fun p hp => (interior_subset (hSA hp) : p ∈ {p' | _})⟩

end Rigid

section Curve

variable {N : Causal.Flat.FlatSpacetime.{0} 2}

/-- **A blunt spear chart of positive radius into a flat `N` has no limit along any curve of the
blunt spear whose radius tends to `0`**: `γ` continuous on `(0, δ)`, off the axis, with
`f(γ s) = τ − r/2 ≥ v`, and `rad (γ s) → 0` as `s → 0⁺`; then `ψ(γ s)` converges to no `q`.
Injectivity of `ψ` and any bound on the height are not used. -/
theorem flat_curve_noLimit {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hR : 0 < R)
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {γ : ℝ → E0} {δ : ℝ}
    (hδ : 0 < δ) (hγc : ContinuousOn γ (Ioo 0 δ)) (hγr : ∀ s ∈ Ioo 0 δ, 0 < rad (γ s))
    (hγf : ∀ s ∈ Ioo 0 δ, v ≤ fcoord (γ s))
    (hrad : Tendsto (fun s => rad (γ s)) (𝓝[>] 0) (𝓝 0)) (q : FlatE0 N) :
    ¬ Tendsto (fun s => ψ (paperInY (γ s))) (𝓝[>] 0) (𝓝 q) := by
  intro hlim
  have hπ := Real.pi_pos
  set κ := chartAt E0Y q with hκ
  set κN := chartAt (Causal.Minkowski 2) (show N from q) with hκN
  have hκs : κ.source = κN.source := by
    show ((chartAt (Causal.Minkowski 2) (show N from q)).trans e0Inl).source = _
    simp only [OpenPartialHomeomorph.trans_source, e0Inl_source, preimage_univ, inter_univ]
    rfl
  have hψc : ContinuousOn ψ W := fun x hx => (hψ x hx).continuousWithinAt
  have hmemW : ∀ x : E0, 0 < rad x → rad x ≤ R → v ≤ x.1 - rad x / 2 → paperInY x ∈ W :=
    fun x h1 h2 h3 => hsub ⟨x, ⟨h3, h1, h2⟩, rfl⟩
  -- a first radius `δ₁`
  obtain ⟨δ₁, hδ₁, hδ₁δ, hev⟩ : ∃ δ₁ > 0, δ₁ ≤ δ ∧ ∀ s ∈ Ioo 0 δ₁,
      rad (γ s) < R ∧ ψ (paperInY (γ s)) ∈ κ.source := by
    have h := (hrad.eventually (gt_mem_nhds hR)).and
      (hlim.eventually (κ.open_source.mem_nhds (mem_chart_source E0Y q)))
    obtain ⟨δ', hδ', hδ's⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
    exact ⟨min δ' δ, lt_min hδ' hδ, min_le_right _ _, fun s hs =>
      hδ's ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
  have hIoo : ∀ s ∈ Ioo 0 δ₁, s ∈ Ioo 0 δ := fun s hs => ⟨hs.1, hs.2.trans_le hδ₁δ⟩
  have hγW : ∀ s ∈ Ioo 0 δ₁, paperInY (γ s) ∈ W := fun s hs => by
    exact hmemW _ (hγr s (hIoo s hs)) (hev s hs).1.le (hγf s (hIoo s hs))
  -- the open set `Õ` of the universal cover
  set V : Set E0Y := W ∩ ψ ⁻¹' κ.source with hV
  have hVo : IsOpen V := hψc.isOpen_inter_preimage hW κ.open_source
  set O : Set (ℝ × ℝ × ℝ) := {p | 0 < p.2.1} ∩ (fun p => paperInY (cov p)) ⁻¹' V with hO
  have hcont : Continuous (fun p => paperInY (cov p)) := continuous_paperInY.comp continuous_cov
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter (hVo.preimage hcont)
  have hOdeck : ∀ (k : ℤ) (p : ℝ × ℝ × ℝ), p ∈ O → (p.1, p.2.1, p.2.2 + 2 * π * k) ∈ O :=
    fun k p hp => by
      refine ⟨hp.1, ?_⟩
      show paperInY (cov (p.1, p.2.1, p.2.2 + 2 * π * k)) ∈ V
      rw [cov_add]; exact hp.2
  -- the lift of the curve
  set s₁ : ℝ := δ₁ / 2 with hs₁
  have hs₁I : s₁ ∈ Ioo 0 δ₁ := ⟨by positivity, by linarith⟩
  have hsectO : ∀ s ∈ Ioo 0 δ₁, sect 0 (γ s) ∈ O := fun s hs =>
    ⟨hγr s (hIoo s hs), by
      show paperInY (cov (sect 0 (γ s))) ∈ V
      rw [cov_sect]; exact ⟨hγW s hs, (hev s hs).2⟩⟩
  set U := connectedComponentIn O (sect 0 (γ s₁)) with hU
  have hUo : IsOpen U := hOo.connectedComponentIn
  have hUO : U ⊆ O := connectedComponentIn_subset _ _
  have hγca : ∀ s ∈ Ioo 0 δ₁, ContinuousAt γ s := fun s hs =>
    hγc.continuousAt (isOpen_Ioo.mem_nhds (hIoo s hs))
  have hlift : ∀ s ∈ Ioc 0 s₁, ∃ c ∈ U, cov c = γ s := by
    set A : Set ℝ := {s | s ∈ Ioo 0 δ₁ ∧ ∃ c ∈ U, cov c = γ s} with hA
    have hAo : IsOpen A := by
      refine isOpen_iff_mem_nhds.2 fun s ⟨hs, c, hcU, hc⟩ => ?_
      have hc0 : 0 < c.2.1 := (hUO hcU).1
      have hf : Tendsto (fun s' => sect c.2.2 (γ s')) (𝓝 s) (𝓝 c) := by
        have h1 := continuousAt_sect_cov hc0
        rw [hc] at h1
        have h2 := h1.tendsto.comp (hγca s hs).tendsto
        rwa [comp_def, ← hc, sect_cov hc0] at h2
      filter_upwards [hf.eventually (hUo.mem_nhds hcU), isOpen_Ioo.mem_nhds hs] with s' h1 h2
      exact ⟨h2, _, h1, cov_sect _ _⟩
    have hsub' := isPreconnected_Ioc.subset_of_closure_inter_subset hAo
      ⟨s₁, ⟨hs₁I.1, le_rfl⟩, hs₁I, _, mem_connectedComponentIn (hsectO s₁ hs₁I), cov_sect _ _⟩
      (by
        rintro s ⟨hscl, hsI⟩
        have hs : s ∈ Ioo 0 δ₁ := ⟨hsI.1, hsI.2.trans_lt hs₁I.2⟩
        set c := sect 0 (γ s) with hcdef
        have hcO : c ∈ O := hsectO s hs
        have hc0 : 0 < c.2.1 := hcO.1
        have hcγ : cov c = γ s := cov_sect _ _
        obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hOo c hcO
        have hf : Tendsto (fun s' => sect c.2.2 (γ s')) (𝓝 s) (𝓝 c) := by
          have h1 := continuousAt_sect_cov hc0
          rw [hcγ] at h1
          have h2 := h1.tendsto.comp (hγca s hs).tendsto
          rwa [comp_def, ← hcγ, sect_cov hc0] at h2
        obtain ⟨s', ⟨hs'b, hs'I⟩, hs'A⟩ := mem_closure_iff_nhds.1 hscl _
          ((hf.eventually (Metric.ball_mem_nhds c hη)).and (isOpen_Ioo.mem_nhds hs))
        obtain ⟨-, c', hc'U, hc'⟩ := hs'A
        have hb0 : 0 < (sect c.2.2 (γ s')).2.1 := (hball hs'b).1
        obtain ⟨k, hk⟩ := exists_eq_add_of_cov_eq hb0 (hUO hc'U).1
          ((cov_sect _ _).trans hc'.symm)
        set T : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (p.1, p.2.1, p.2.2 + 2 * π * k) with hT
        have hTc : Continuous T := by simp only [hT]; fun_prop
        have hpre : IsPreconnected (T '' Metric.ball c η) :=
          (convex_ball c η).isPreconnected.image _ hTc.continuousOn
        have hTsub : T '' Metric.ball c η ⊆ U := by
          have h := hpre.subset_connectedComponentIn (x := c') ⟨_, hs'b, hk.symm⟩
            (by rintro _ ⟨p, hp, rfl⟩; exact hOdeck k p (hball hp))
          rwa [← connectedComponentIn_eq hc'U] at h
        exact ⟨hs, T c, hTsub ⟨c, Metric.mem_ball_self hη, rfl⟩, by rw [cov_add, hcγ]⟩)
    exact fun s hs => (hsub' hs).2
  -- rigidity on `U`
  obtain ⟨g, hg⟩ := exists_eqOn_smul_dev hW hψ q isPreconnected_connectedComponentIn
    ⟨_, mem_connectedComponentIn (hsectO s₁ hs₁I)⟩
    (fun p hp => ⟨(hUO hp).1, (hUO hp).2.1, (hUO hp).2.2⟩)
  have hsrc : ∀ p ∈ U, ψ (paperInY (cov p)) ∈ κN.source := fun p hp => by
    rw [← hκs]; exact (hUO hp).2.2
  have hg' : ∀ p ∈ U, ψ (paperInY (cov p)) = κN.symm (g • btzPaperDev p) := fun p hp => by
    rw [← hg p hp, κN.left_inv (hsrc p hp)]
  choose! L hLU hLγ using hlift
  have hL1 : ∀ s ∈ Ioc 0 s₁, (L s).1 = (γ s).1 := fun s hs => by
    have := congrArg (fun x : E0 => x.1) (hLγ s hs); simpa [cov] using this
  have hL2 : ∀ s ∈ Ioc 0 s₁, (L s).2.1 = rad (γ s) := fun s hs => by
    rw [← hLγ s hs, rad_cov (hUO (hLU s hs)).1.le]
  have hIoc : Ioc 0 s₁ ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (hs₁I.1)
  -- the developed curve converges
  set n : ℝ × ℝ × ℝ := nullToMink.symm (g⁻¹ • κN q) with hn
  have hNull : Tendsto (fun s => btzPaperNull (L s)) (𝓝[>] 0) (𝓝 n) := by
    have h1 : Tendsto (fun s => κN (ψ (paperInY (γ s)))) (𝓝[>] 0) (𝓝 (κN q)) :=
      ((chartAt (Causal.Minkowski 2) (show N from q)).continuousAt
        (mem_chart_source _ (show N from q))).tendsto.comp hlim
    have h2 := ((nullToMinkHomeomorph.symm.continuous.comp (continuous_const_smul g⁻¹)).tendsto
      _).comp h1
    refine h2.congr' ?_
    filter_upwards [hIoc] with s hs
    simp only [comp_apply, coe_nullToMinkHomeomorph_symm]
    rw [← hLγ s hs, hg _ (hLU s hs), inv_smul_smul, btzPaperDev_eq_nullToMink,
      LinearEquiv.symm_apply_apply]
  have hr : Tendsto (fun s => (L s).2.1) (𝓝[>] 0) (𝓝 0) := by
    refine hrad.congr' ?_
    filter_upwards [hIoc] with s hs
    rw [hL2 s hs]
  have hu : Tendsto (fun s => (btzPaperNull (L s)).1) (𝓝[>] 0) (𝓝 n.1) :=
    (continuous_fst.tendsto _).comp hNull
  have hτ : ∀ᶠ s in 𝓝[>] (0 : ℝ), v ≤ (L s).1 - (L s).2.1 / 2 := by
    filter_upwards [hIoc] with s hs
    rw [hL1 s hs, hL2 s hs]; exact hγf s (hIoo s ⟨hs.1, hs.2.trans_lt hs₁I.2⟩)
  have hX2 : Tendsto (fun s => ((L s).2.1 * (L s).2.2) ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hR' : Tendsto (fun s => (L s).2.1 * ((btzPaperNull (L s)).1 + (L s).2.1 - 2 * v))
        (𝓝[>] 0) (𝓝 0) := by
      have := hr.mul ((hu.add hr).sub_const (2 * v))
      rwa [zero_mul] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR'
      (Eventually.of_forall fun s => sq_nonneg _) ?_
    filter_upwards [hτ, hIoc] with s hs hs'
    have hr0 : 0 ≤ (L s).2.1 := (hUO (hLU s hs')).1.le
    simp only [btzPaperNull]
    have hs2 : v ≤ (L s).1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hs2 hr0]
  have hX : Tendsto (fun s => (L s).2.1 * (L s).2.2) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have := hX2.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun s => ?_
    rw [Real.sqrt_sq_eq_abs]; rfl
  have hn3 : n.2.2 = 0 := by
    have h1 : Tendsto (fun s => (btzPaperNull (L s)).2.2) (𝓝[>] 0) (𝓝 n.2.2) :=
      ((continuous_snd.comp continuous_snd).tendsto _).comp hNull
    have h2 : Tendsto (fun s => (btzPaperNull (L s)).2.2) (𝓝[>] 0) (𝓝 0) := by
      have := hX.neg; rw [neg_zero] at this
      exact this.congr fun s => rfl
    exact tendsto_nhds_unique h1 h2
  -- a radius `ρ` around `n` developing into the chart at `q`
  have hqT : κN q ∈ κN.target := κN.map_source (mem_chart_source _ _)
  have hopen : IsOpen {x : ℝ × ℝ × ℝ | g • nullToMink x ∈ κN.target} :=
    κN.open_target.preimage ((continuous_const_smul g).comp nullToMinkHomeomorph.continuous)
  have hnmem : g • nullToMink n ∈ κN.target := by
    rw [hn, LinearEquiv.apply_symm_apply, smul_inv_smul]; exact hqT
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen n hnmem
  have hE4 : Tendsto (fun s => |(L s).2.1 * (L s).2.2| + π * (L s).2.1) (𝓝[>] 0) (𝓝 0) := by
    have := hX.abs.add (hr.const_mul π)
    rwa [abs_zero, mul_zero, add_zero] at this
  have hρ2 : 0 < ρ / 2 := by positivity
  have hE5 : Tendsto (fun s => π ^ 2 * (L s).2.1) (𝓝[>] 0) (𝓝 0) := by
    have := hr.const_mul (π ^ 2); rwa [mul_zero] at this
  obtain ⟨s, hs, hsB, hs4, hs5, hs6⟩ :=
    ((show ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc 0 s₁ from hIoc).and
      ((hNull.eventually (Metric.ball_mem_nhds n hρ2)).and
      ((hE4.eventually (gt_mem_nhds hρ)).and ((hE5.eventually (gt_mem_nhds hρ2)).and
        (hr.eventually (gt_mem_nhds hR)))))).exists
  -- the closure argument: a preconnected set of good points meeting `U` lies in `U`
  have hclose : ∀ K : Set (ℝ × ℝ × ℝ), IsPreconnected K → (K ∩ U).Nonempty →
      (∀ x ∈ K, 0 < x.2.1 ∧ paperInY (cov x) ∈ W ∧ g • btzPaperDev x ∈ κN.target) → K ⊆ U := by
    intro K hK hKU hgood
    refine hK.subset_of_closure_inter_subset hUo hKU ?_
    rintro x ⟨hxcl, hxK⟩
    obtain ⟨hx0, hxW, hT⟩ := hgood x hxK
    have h1 : Tendsto (fun p => ψ (paperInY (cov p))) (𝓝[U] x)
        (𝓝 (ψ (paperInY (cov x)))) :=
      ((hψc.continuousAt (hW.mem_nhds hxW)).tendsto.comp
        hcont.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun p => ψ (paperInY (cov p))) (𝓝[U] x)
        (𝓝 (κN.symm (g • btzPaperDev x))) := by
      have hc : ContinuousAt (fun p => κN.symm (g • btzPaperDev p)) x :=
        ContinuousAt.comp (f := fun p => g • btzPaperDev p) (κN.continuousAt_symm hT)
          ((continuous_const_smul g).comp continuous_btzPaperDev).continuousAt
      refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (hg' p hp).symm
    haveI := mem_closure_iff_nhdsWithin_neBot.1 hxcl
    have heq := tendsto_nhds_unique h1 h2
    have hxO : x ∈ O := ⟨hx0, hxW, by
      show ψ (paperInY (cov x)) ∈ κ.source
      rw [hκs, heq]; exact κN.map_target hT⟩
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hxcl _ hOo.connectedComponentIn
      (mem_connectedComponentIn hxO)
    show x ∈ connectedComponentIn O (sect 0 (γ s₁))
    rw [connectedComponentIn_eq hz2, ← connectedComponentIn_eq hz1]
    exact mem_connectedComponentIn hxO
  -- the good points near `L s`
  have hsU := hLU s hs
  set τ₀ := (L s).1 with hτ₀
  set r := (L s).2.1 with hrdef
  set θs := (L s).2.2 with hθs
  set u := (btzPaperNull (L s)).1 with hudef
  have hr0 : 0 < r := (hUO hsU).1
  have hτv : v ≤ τ₀ - r / 2 := by
    rw [hτ₀, hrdef, hL1 s hs, hL2 s hs]; exact hγf s (hIoo s ⟨hs.1, hs.2.trans_lt hs₁I.2⟩)
  have hgood : ∀ x : ℝ × ℝ × ℝ, x.2.1 = r → v ≤ x.1 - r / 2 → (btzPaperNull x).2.1 = r →
      |(btzPaperNull x).1 - u| ≤ π ^ 2 * r → |(btzPaperNull x).2.2| ≤ |r * θs| + π * r →
      0 < x.2.1 ∧ paperInY (cov x) ∈ W ∧ g • btzPaperDev x ∈ κN.target := by
    intro x hx1 hx2 hx3 hx4 hx5
    have hrad' : rad (cov x) = r := by rw [rad_cov (hx1 ▸ hr0.le), hx1]
    refine ⟨hx1 ▸ hr0, hmemW _ (by rw [hrad']; exact hr0) (by rw [hrad']; exact hs6.le)
      (by rw [hrad']; exact hx2), ?_⟩
    rw [btzPaperDev_eq_nullToMink]
    refine hball ?_
    have hB := hsB
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hB ⊢
    refine ⟨?_, ?_, ?_⟩
    · calc |(btzPaperNull x).1 - n.1| ≤ |(btzPaperNull x).1 - u| + |u - n.1| := abs_sub_le _ _ _
        _ < ρ := by linarith [hB.1]
    · have h0 : (btzPaperNull (L s)).2.1 = r := rfl
      rw [hx3]; rw [h0] at hB; linarith [hB.2.1]
    · rw [hn3, sub_zero]; linarith
  -- the vertical segment from `L s` up by `Δ = ½ r π²`
  set Δ : ℝ := 1 / 2 * r * π ^ 2 with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  set Q : ℝ → ℝ × ℝ × ℝ := fun t => (τ₀ + t * Δ, r, θs) with hQ
  have hQc : Continuous Q := by simp only [hQ]; fun_prop
  have hQ0 : Q 0 = L s := by simp only [hQ, zero_mul, add_zero]; rfl
  have hQU : Q '' Icc 0 1 ⊆ U := by
    refine hclose _ (isPreconnected_Icc.image _ hQc.continuousOn) ⟨L s, ⟨0, ⟨le_rfl, zero_le_one⟩,
      hQ0⟩, hsU⟩ ?_
    rintro _ ⟨t, ht, rfl⟩
    refine hgood _ rfl ?_ rfl ?_ ?_
    · show v ≤ τ₀ + t * Δ - r / 2
      linarith [mul_nonneg ht.1 hΔ0, hτv]
    · show |2 * (τ₀ + t * Δ) + r * θs ^ 2 - r - u| ≤ π ^ 2 * r
      rw [hudef]
      simp only [btzPaperNull, hτ₀, hrdef, hθs]
      rw [show 2 * ((L s).1 + t * Δ) + (L s).2.1 * (L s).2.2 ^ 2 - (L s).2.1 -
        (2 * (L s).1 + (L s).2.1 * (L s).2.2 ^ 2 - (L s).2.1) = 2 * t * Δ by ring,
        abs_of_nonneg (by have := mul_nonneg ht.1 hΔ0; linarith)]
      have : t * Δ ≤ Δ := mul_le_of_le_one_left hΔ0 ht.2
      simp only [hΔ] at this ⊢
      linarith
    · show |-(r * θs)| ≤ |r * θs| + π * r
      rw [abs_neg]; linarith [mul_pos hπ hr0]
  -- the arc `θ ↦ (T + Δ − ½ r θ², r, θ)` at constant developed time
  set Tt := τ₀ + 1 / 2 * r * θs ^ 2 with hTt
  set M := max |θs| π with hM
  set P : ℝ → ℝ × ℝ × ℝ := fun θ => (Tt + Δ - 1 / 2 * r * θ ^ 2, r, θ) with hP
  have hPc : Continuous P := by simp only [hP]; fun_prop
  have hPs : P θs = Q 1 := by
    simp only [hP, hQ, hTt, one_mul]; ext <;> simp only; ring
  have hsq : ∀ θ ∈ Icc (-M) M, θ ^ 2 ≤ θs ^ 2 + π ^ 2 := fun θ hθ => by
    have h1 : |θ| ≤ M := abs_le.2 hθ
    have h2 : θ ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rcases le_total |θs| π with h | h
    · rw [hM, max_eq_right h] at h2; linarith [sq_nonneg θs]
    · rw [hM, max_eq_left h, sq_abs] at h2; linarith [sq_nonneg π]
  have hθsM : θs ∈ Icc (-M) M := abs_le.1 (le_max_left _ _)
  have hArc : P '' Icc (-M) M ⊆ U := by
    refine hclose _ (isPreconnected_Icc.image _ hPc.continuousOn)
      ⟨P θs, ⟨θs, hθsM, rfl⟩, by rw [hPs]; exact hQU ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩⟩ ?_
    rintro _ ⟨θ, hθ, rfl⟩
    refine hgood _ rfl ?_ rfl ?_ ?_
    · show v ≤ Tt + Δ - 1 / 2 * r * θ ^ 2 - r / 2
      have h3 : r * θ ^ 2 ≤ r * (θs ^ 2 + π ^ 2) := mul_le_mul_of_nonneg_left (hsq θ hθ) hr0.le
      simp only [hTt, hΔ]
      linarith [h3, hτv]
    · show |2 * (Tt + Δ - 1 / 2 * r * θ ^ 2) + r * θ ^ 2 - r - u| ≤ π ^ 2 * r
      rw [hudef]
      simp only [btzPaperNull, hTt, hΔ, hτ₀, hrdef, hθs]
      rw [show 2 * ((L s).1 + 1 / 2 * (L s).2.1 * (L s).2.2 ^ 2 + 1 / 2 * (L s).2.1 * π ^ 2 -
        1 / 2 * (L s).2.1 * θ ^ 2) + (L s).2.1 * θ ^ 2 - (L s).2.1 -
        (2 * (L s).1 + (L s).2.1 * (L s).2.2 ^ 2 - (L s).2.1) = π ^ 2 * (L s).2.1 by ring,
        abs_of_nonneg (by positivity)]
    · show |-(r * θ)| ≤ |r * θs| + π * r
      rw [abs_neg, abs_mul, abs_of_pos hr0, abs_mul, abs_of_pos hr0]
      have h1 : |θ| ≤ |θs| + π := (abs_le.2 hθ).trans (max_le (by linarith) (by
        linarith [abs_nonneg θs]))
      have := mul_le_mul_of_nonneg_left h1 hr0.le
      linarith
  -- the two sides of the slit develop to different points
  have hπM : π ≤ M := le_max_right _ _
  have e1 := hg _ (hArc ⟨π, ⟨by linarith, hπM⟩, rfl⟩)
  have e2 := hg _ (hArc ⟨-π, ⟨by linarith, by linarith⟩, rfl⟩)
  have hcov : cov (P π) = cov (P (-π)) := by
    have := cov_add (P (-π)) 1
    rw [← this]
    simp only [hP]
    congr 2 <;> push_cast <;> ring_nf
  rw [hcov, e2] at e1
  have h5 := smul_left_cancel g e1
  have hne := btzPaperDev_add_pi_ne (τ := Tt + Δ - 1 / 2 * r * π ^ 2) (θ := 0) hr0
  rw [zero_add, zero_sub] at hne
  apply hne
  simp only [hP, neg_sq] at h5
  exact h5.symm

/-- **The curve form for `γ : (0, 1] → bspear v R`**, with `rad (γ s) → 0`. -/
theorem flat_axis_noLimit {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hR : 0 < R)
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {γ : ℝ → E0}
    (hγc : ContinuousOn γ (Ioc 0 1)) (hγS : ∀ s ∈ Ioc 0 1, γ s ∈ bspear v R)
    (hrad : Tendsto (fun s => rad (γ s)) (𝓝[>] 0) (𝓝 0)) (q : FlatE0 N) :
    ¬ Tendsto (fun s => ψ (paperInY (γ s))) (𝓝[>] 0) (𝓝 q) :=
  flat_curve_noLimit hR hW hsub hψ one_pos (hγc.mono Ioo_subset_Ioc_self)
    (fun s hs => (hγS s (Ioo_subset_Ioc_self hs)).2.1)
    (fun s hs => (hγS s (Ioo_subset_Ioc_self hs)).1) hrad q

/-- **The roadmap's statement** (T-btz-axis-nolimit): `γ : (0, 1] → bspear v R` continuous,
`rad (γ s) → 0`, time coordinate in `[a₁, a₂]`, `v < a₁`. The height bounds are not needed
(`flat_axis_noLimit`). -/
theorem flat_axis_noLimit_Icc {v R a₁ a₂ : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hR : 0 < R)
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {γ : ℝ → E0}
    (hγc : ContinuousOn γ (Ioc 0 1)) (hγS : ∀ s ∈ Ioc 0 1, γ s ∈ bspear v R)
    (_hγτ : ∀ s ∈ Ioc (0 : ℝ) 1, (γ s).1 ∈ Icc a₁ a₂) (_hva : v < a₁)
    (hrad : Tendsto (fun s => rad (γ s)) (𝓝[>] 0) (𝓝 0)) (q : FlatE0 N) :
    ¬ Tendsto (fun s => ψ (paperInY (γ s))) (𝓝[>] 0) (𝓝 q) :=
  flat_axis_noLimit hR hW hsub hψ hγc hγS hrad q

/-- **The strict in-falling lemma, as a corollary, with `v ≤ a`** (the strict
`flat_infall_noLimit_of_pos` asks `v < a`): `s ↦ ψ(a + s/2, s u)` has no limit as `s → 0⁺`. -/
theorem flat_infall_noLimit_of_le {v R : ℝ} {W : Set E0Y} {ψ : E0Y → FlatE0 N} (hR : 0 < R)
    (hW : IsOpen W) (hsub : bspearY v R ⊆ W) (hψ : IsE0Mor ψ W) {a : ℝ} (ha : v ≤ a)
    {u : ℂ} (hu : ‖u‖ = 1) (q : FlatE0 N) :
    ¬ Tendsto (fun s : ℝ => ψ (paperInY (a + s / 2, (s : ℂ) * u))) (𝓝[>] 0) (𝓝 q) := by
  have hrad : ∀ s : ℝ, 0 ≤ s → rad ((a + s / 2, (s : ℂ) * u) : E0) = s := fun s hs => by
    simp [rad, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, hu]
  refine flat_curve_noLimit (γ := fun s : ℝ => ((a + s / 2, (s : ℂ) * u) : E0)) hR hW hsub hψ
    one_pos (by fun_prop) (fun s hs => by rw [hrad s hs.1.le]; exact hs.1)
    (fun s hs => by simp only [fcoord]; rw [hrad s hs.1.le]; linarith) ?_ q
  have h : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hrad s (le_of_lt hs)).symm

end Curve
end E0AxisNoLimit

end GX
