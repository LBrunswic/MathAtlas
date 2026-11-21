import Causal.MaximalAEAtlasIso
import Causal.Model.EAlphaSectors
import Causal.Model.EAlphaContinuation

/-!
# `E_κ`, `κ > 0`, as a singular `(Isom(E^{1,2}), E^{1,2})`-manifold under DEC-25

`defi:causal_Ealpha` — `ETT.tex:1335`. **Not marked**: the row is about every `E_{≥0}`-manifold
and waits on OQ-34/OQ-35 (`E₀`) and OQ-82 (the group). This file builds, on every model
`E_κ = ℝ × C_κ`, `κ > 0`, the singular `(G,X)`-structure that the row's `(G,X)` sentence and
`def:singular_spacetime` presuppose of the models, and DEC-25's hypothesis `hreg` of
`Causal.existsUnique_causality_singularGX_dec25` at each of them. Target
`T-ett-ealpha-gx-structure`.

> For $\alpha>0$, $\mass{\alpha}$ is Minkowski space $\mass{}=\E^{1,2}$ with a cone singularity of
> angle $\alpha$ along a timelike line --- a massive particle --- and $\mass{2\pi}=\mass{}$ [...]
> We write $\sing(\mass{\alpha})$ for the singular line and $\reg(\mass{\alpha})$ for its
> complement, which is an $(\isom(\mass{}),\mass{})$-manifold. (`ETT.tex:1327–1333`)

> On any $\mass{\geq0}$-manifold $M$ there is then a unique causal structure inducing that of
> $\mass{\alpha}$ in every chart [...] (`defi:causal_Ealpha`, `ETT.tex:1339–1340`)

## What is proved (no `sorry`)

* **(1) The sector atlas, for every `κ > 0`.** `sectorAtlas κ`, the disc charts of
  `Causal.Model.EAlphaSectors`, is an a.e. `(Flat.isom 2, Minkowski 2)`-atlas
  (`isAEAtlas_sectorAtlas`): a `(G,X)`-atlas (`isGXAtlas_sectorAtlas`, one rotation per overlap)
  with support `reg(E_κ)` (`support_sectorAtlas`), portly (`isPortly_regPart`: about the line,
  the punctured box is the time interval times the image of `(0, ε) × ℝ/κℤ` in polar
  coordinates). **The singular structure** `singularGX κ` is its maximal a.e. atlas.
* **(2) `κ ≠ 2π`.** No chart of the maximal atlas meets the singular line
  (`source_inter_singLine_eq_empty`), by the continuation lemma of
  `Causal.Model.EAlphaContinuation`: such a chart would give `e^{iκ} = 1` and `2π ∈ κℤ`, i.e.
  `κ = 2π`. So `Reg = reg(E_κ)`, `Sing = sing(E_κ) ≠ ∅` (`reg_eq`, `sing_eq`, `sing_nonempty`),
  for `κ ∉ 2πℤ` and for `κ ∈ 2πℤ`, `κ ≥ 4π` alike, and `hreg` in DEC-25's form
  (`chartIso_of_mem_aeAtlas_of_ne`, by `forall_chartIso_aeAtlas_of_reg_subset`).
* **(3) `κ = 2π`.** The identification `E_{2π} → E^{1,2}` (`massiveTwoPiToMinkowski`) as an
  open partial homeomorphism, `twoPiChart`, is a `ChartIso` (`chartIso_twoPiChart`), differs from
  each sector chart by one rotation on its whole source (`twoPiChart_eq_rotIsom_smul`), and lies
  in the maximal atlas (`twoPiChart_mem_aeAtlas`). So `Reg = E_{2π}`, `Sing = ∅`
  (`reg_eq_univ_two_pi`, `sing_eq_empty_two_pi`), and `hreg` holds
  (`chartIso_of_mem_aeAtlas_two_pi`, by `chartIso_of_mem_maximalAEAtlas_of_agreeOn`, the agreement
  at the line supplied by `twoPiChart`).
* **Every `κ > 0`**: `hreg` (`chartIso_of_mem_aeAtlas`); the dichotomy (`reg_sing_cases`); a chart
  of the maximal atlas meets the line iff `κ = 2π` (`exists_mem_aeAtlas_inter_singLine_iff`);
  `Reg = reg(E_κ)` iff `κ ≠ 2π` (`reg_eq_regPart_iff`); `hreg` for the family of the models
  (`hreg_family`, over `singularGXFamily`).
* **(b′) of `existsUnique_causality_singularGX_dec25` where `hreg` gives it**: between any two
  models, an a.e. isomorphism chart `E_κ ⇀ E_κ'` with source in `Reg(E_κ)` is a chart isomorphism
  (`chartIso_of_isAEChart_of_subset_reg`); so every one from `E_{2π}`, its line included
  (`chartIso_of_isAEChart_two_pi`), and every one from `E_κ`, `κ ≠ 2π`, avoiding the line
  (`chartIso_of_isAEChart_of_subset_regPart`).
* Non-vacuity at `κ = π, 2π, 4π` (`nonvacuous`); the continuation lemma's hypotheses hold for
  `twoPiChart` (`continuation_nonvacuous`).

## Hypothesis checklist

| paper / roadmap | here |
|---|---|
| `α > 0` | ✓ carried (`[Fact (0 < α)]`); `α > 2π` included |
| `Isom(E^{1,2})` (l.1331) | ⚠ a reading: `Flat.isom 2` = SO₀(1,2) ⋉ ℝ³ (OQ-82). Stated for it only; the argument of (2) uses only the rotations about the time axis and the rigidity and faithfulness of the action (prose, SCOPE) |
| `reg(E_α)` an `(Isom(E), E)`-manifold (l.1331–1333) | ✓ at every `α`: the sector atlas, with support `reg(E_α)` (`isAEAtlas_sectorAtlas`, `support_sectorAtlas`); `Reg = reg(E_α)` for `α ≠ 2π`, and `Reg = E_{2π}` at `α = 2π`, a reading of l.1332 (SCOPE) |
| `sing(E_α)` the singular line (l.1332) | ✓ `Sing = sing(E_α)` for `α ≠ 2π`; `Sing = ∅` at `α = 2π`, as the paper itself reads `E_{2π}` (l.1328, l.2185; DEC-74) (SCOPE) |
| `E_α`'s causality absolutely minimal (l.1383) | ✓ `massive_causallyArcConnected`, used as `hmin` |
| a singular `(G,X)`-manifold (DEC-25) | ✓ `SingularGXStructure`, the maximal a.e. atlas of the sector atlas |

## SCOPE (disclosed)

* **At `κ = 2π` the singular line is not singular.** The paper writes `sing(E_α)` for the line
  `{r = 0}` for every `α` (l.1332) and `E_{2π} = E` (l.1328). Under DEC-25 the singular locus is
  the complement of the support of the maximal a.e. atlas, which at `κ = 2π` is empty: the
  model `E_{2π}` is a `(G,X)`-manifold, the line regular. The paper's notation and DEC-25's `Sing`
  part ways there only, and the paper itself reads `E_{2π}` as regular (l.1328 « `E_{2π} = E` »,
  l.2185 « `α = 2π` if `p` is regular »; DEC-74): a wording note at l.1332, not a question.
* `E₀` is not here (`Causal.Port.E0GXStructure`); the family `MassAModel` of
  `Causal.Remarks.MassADEC25` is not packaged with these structures, since that module imports
  the `E₀` model (kb 0047).
* (b′) at the models `E_κ` is proved only where `hreg` gives it (regular sources; every source
  from `E_{2π}`). An a.e. isomorphism chart from `E_κ`, `κ ≠ 2π`, whose source meets the line is
  not treated: T-ett-bprime-ealpha (the continuation lemma's box form,
  `EAlphaContinuation.exists_smul_devPt_of_ringBox`, asks no chart into `E^{1,2}` through the line).
* **The group.** Under a larger reading of `Isom(E^{1,2})` (OQ-82: O⁺(1,2) ⋉ ℝ³, spatial
  reflections added) the sector atlas is still an a.e. atlas, and the argument of (2) carries over
  unchanged (it chains rotations and uses rigidity and faithfulness only); this is prose, the Lean
  statements are for `Flat.isom 2`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The template is
`Causal.Port.E0GXStructure` (T-ett-e0-gx-structure); the model-free lemmas are imported from
`Causal.MaximalAEAtlasIso`, not from the `E₀` port.
-/

namespace Causal

open Set Real Metric Topology TopologicalSpace Filter

namespace EAlphaGX

open EAlphaSector EAlphaContinuation

/-! ### The punctured cone about the apex -/

section Cone

variable {α : ℝ}

theorem isClosed_singLine : IsClosed (singLine α) :=
  isClosed_singleton.preimage continuous_snd

private theorem isOpen_regPart : IsOpen (regPart α) := isClosed_singLine.isOpen_compl

/-- The apex is not an isolated point of `C_κ`. -/
theorem not_isOpen_apex : ¬ IsOpen ({Cone.apex} : Set (Cone α)) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h Cone.apex rfl
  set q : ConePoint α := ⟨ε / 2, 0, by positivity⟩
  have hy : Cone.mk q ∈ ball (Cone.apex : Cone α) ε := by
    rw [mem_ball, dist_comm]
    show Cone.rad (Cone.mk q) < ε
    rw [Cone.rad_mk]
    show ε / 2 < ε
    linarith
  have h2 : Cone.rad (Cone.mk q) = 0 := Cone.rad_eq_zero.2 (mem_singleton_iff.1 (hball hy))
  rw [Cone.rad_mk] at h2
  have : ε / 2 = 0 := h2
  linarith

theorem dense_regPart : Dense (regPart α) := by
  show Dense (Prod.snd ⁻¹' ({Cone.apex}ᶜ : Set (Cone α)))
  exact (dense_compl_singleton_iff_not_open.2 not_isOpen_apex).preimage isOpenMap_snd

/-- **A punctured ball about the apex is preconnected**: the image of `(0, ε) × ℝ/κℤ` in polar
coordinates. -/
theorem isPreconnected_ball_apex_diff (ε : ℝ) :
    IsPreconnected (ball (Cone.apex : Cone α) ε \ {Cone.apex}) := by
  have h : ball (Cone.apex : Cone α) ε \ {Cone.apex} = Cone.polar '' (Ioo 0 ε ×ˢ univ) := by
    ext y
    constructor
    · rintro ⟨hy, hy0⟩
      obtain ⟨q, rfl⟩ := Cone.mk_surjective y
      refine ⟨(q.r, q.θ), ⟨⟨?_, ?_⟩, trivial⟩, Cone.polar_rad_θ q⟩
      · exact lt_of_le_of_ne q.r_nonneg fun h0 => hy0 (Cone.mk_eq_apex h0.symm)
      · have h1 : dist (Cone.mk q) Cone.apex < ε := hy
        rw [dist_comm] at h1
        have h2 : Cone.rad (Cone.mk q) = q.r := Cone.rad_mk q
        unfold Cone.rad at h2
        linarith
    · rintro ⟨⟨u, θ⟩, ⟨⟨hu0, huε⟩, -⟩, rfl⟩
      have hr : Cone.rad (Cone.polar (u, θ)) = u := by
        unfold Cone.polar
        rw [Cone.rad_mk, ConePoint.of_r hu0.le]
      refine ⟨?_, fun h0 => ?_⟩
      · rw [mem_ball, dist_comm]
        show Cone.rad (Cone.polar (u, θ)) < ε
        rw [hr]
        exact huε
      · have h1 : Cone.rad (Cone.polar (u, θ)) = 0 := Cone.rad_eq_zero.2 (mem_singleton_iff.1 h0)
        rw [hr] at h1
        linarith
  rw [h]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ Cone.continuous_polar.continuousOn

end Cone

variable {α : ℝ} [hα : Fact (0 < α)]

/-! ### (1) The sector atlas -/

/-- **The sector atlas of `E_κ`**: the disc charts of `Causal.Model.EAlphaSectors`. -/
def sectorAtlas (α : ℝ) [Fact (0 < α)] : Set (OpenPartialHomeomorph (Massive α) (Minkowski 2)) :=
  range (chart (α := α))

theorem chart_mem_sectorAtlas (k : Index α) : chart k ∈ sectorAtlas α := ⟨k, rfl⟩

/-- The support of the sector atlas is `reg(E_κ)`. -/
theorem support_sectorAtlas : support (sectorAtlas α) = regPart α := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hx⟩
    exact chart_source_subset_regPart k hx
  · intro hx
    obtain ⟨k, hk⟩ := exists_mem_chart_source hx
    exact ⟨_, ⟨k, rfl⟩, hk⟩

/-- Two sector charts differ by one rotation on their whole overlap. -/
theorem isGXAtlas_sectorAtlas : IsGXAtlas (Flat.isom 2) (sectorAtlas α) := by
  rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ x -
  obtain ⟨c, hc⟩ := exists_rotation k k'
  exact ⟨rotIsom c, fun y hy => hc y (connectedComponentIn_subset _ _ hy)⟩

/-- **`reg(E_κ)` is portly**: open, dense, and removing the line from a connected open set
leaves it connected. -/
theorem isPortly_regPart : IsPortly (regPart α) := by
  refine ⟨isOpen_regPart, dense_regPart, fun W hW hWc => ?_⟩
  refine isPreconnected_of_local hWc inter_subset_left
    (fun x hx => hW.inter_closure ⟨hx, dense_regPart x⟩) fun x hx => ?_
  by_cases hxr : x ∈ regPart α
  · -- a regular point: the preimage of a ball under a sector chart, inside `W`
    obtain ⟨k, hk⟩ := exists_mem_chart_source hxr
    have hVo : IsOpen ((chart k).source ∩ W) := (chart k).open_source.inter hW
    have hVs : (chart k).source ∩ W ⊆ (chart k).source := inter_subset_left
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1
      ((chart k).isOpen_image_of_subset_source hVo hVs) (chart k x) ⟨x, ⟨hk, hx⟩, rfl⟩
    have hrt : ball (chart k x) r ⊆ (chart k).target := fun m hm => by
      obtain ⟨v, hv, rfl⟩ := hrV hm
      exact (chart k).map_source hv.1
    refine ⟨(chart k).symm '' ball (chart k x) r, ?_, ⟨chart k x, mem_ball_self hr,
      (chart k).left_inv hk⟩, ?_⟩
    · rw [(chart k).symm_image_eq_source_inter_preimage hrt]
      exact (chart k).continuousOn.isOpen_inter_preimage (chart k).open_source isOpen_ball
    · have hsub : (chart k).symm '' ball (chart k x) r ⊆ W ∩ regPart α := by
        rintro _ ⟨m, hm, rfl⟩
        obtain ⟨v, hv, rfl⟩ := hrV hm
        rw [(chart k).left_inv hv.1]
        exact ⟨hv.2, chart_source_subset_regPart k hv.1⟩
      rw [inter_eq_left.2 hsub]
      exact (convex_ball _ _).isPreconnected.image _ ((chart k).continuousOn_symm.mono hrt)
  · -- a point of the line: a punctured box
    have hx2 : x.2 = Cone.apex := not_not.1 hxr
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x hx
    refine ⟨ball x ε, isOpen_ball, mem_ball_self hε, ?_⟩
    have hb : ball x ε = ball x.1 ε ×ˢ ball x.2 ε := by rw [ball_prod_same]
    have heq : ball x ε ∩ (W ∩ regPart α) =
        ball x.1 ε ×ˢ (ball (Cone.apex : Cone α) ε \ {Cone.apex}) := by
      ext z
      constructor
      · rintro ⟨hz, -, hzr⟩
        rw [hb] at hz
        exact ⟨hz.1, by rw [← hx2]; exact hz.2, hzr⟩
      · rintro ⟨h1, h2, h3⟩
        have hz : z ∈ ball x ε := by rw [hb]; exact ⟨h1, by rw [hx2]; exact h2⟩
        exact ⟨hz, hεW hz, h3⟩
    rw [heq]
    exact (convex_ball _ _).isPreconnected.prod (isPreconnected_ball_apex_diff ε)

/-- **The sector charts form an a.e. `(Isom(E^{1,2}), E^{1,2})`-atlas of `E_κ`**, for every
`κ > 0`. -/
theorem isAEAtlas_sectorAtlas : IsAEAtlas (Flat.isom 2) (sectorAtlas α) :=
  ⟨isGXAtlas_sectorAtlas, by rw [support_sectorAtlas]; exact isPortly_regPart⟩

/-- **`E_κ` as a singular `(Isom(E^{1,2}), E^{1,2})`-manifold** (DEC-25): the maximal a.e. atlas
of its sector atlas, for every `κ > 0`. -/
noncomputable abbrev singularGX (α : ℝ) [Fact (0 < α)] :
    SingularGXStructure (Flat.isom 2) (Minkowski 2) (Massive α) :=
  ⟨maximalAEAtlas (Flat.isom 2) (sectorAtlas α),
    isAEAtlas_sectorAtlas.isMaximalAEAtlas_maximalAEAtlas⟩

attribute [local instance] singularGX

theorem aeAtlas_eq :
    aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α) =
      maximalAEAtlas (Flat.isom 2) (sectorAtlas α) := rfl

theorem sectorAtlas_subset_aeAtlas :
    sectorAtlas α ⊆ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α) :=
  isAEAtlas_sectorAtlas.subset_maximalAEAtlas

/-- Every chart of the maximal atlas is compatible with every sector chart. -/
theorem compatible_of_mem_aeAtlas {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)) :
    ∀ k : Index α, e.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2) := fun k =>
  (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)).1.1.symm_trans_mem he
    (sectorAtlas_subset_aeAtlas (chart_mem_sectorAtlas k))

theorem regPart_subset_reg : regPart α ⊆ Reg (Flat.isom 2) (Minkowski 2) (Massive α) := by
  rw [← support_sectorAtlas]
  exact support_mono sectorAtlas_subset_aeAtlas

/-! ### (2) `κ ≠ 2π`: the singular locus is the line -/

/-- **A chart of the maximal atlas meets the singular line only if `κ = 2π`** (the continuation
lemma `EAlphaContinuation.eq_two_pi_of_mem_source_singLine`). -/
theorem eq_two_pi_of_mem_aeAtlas {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)) {x : Massive α}
    (hx : x ∈ e.source) (hxs : x ∈ singLine α) : α = 2 * π :=
  eq_two_pi_of_mem_source_singLine (compatible_of_mem_aeAtlas he) hx hxs

/-- **For `κ ≠ 2π` no chart of the maximal atlas reaches the singular line.** -/
theorem source_inter_singLine_eq_empty (h : α ≠ 2 * π)
    {e : OpenPartialHomeomorph (Massive α) (Minkowski 2)}
    (he : e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α)) : e.source ∩ singLine α = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h (eq_two_pi_of_mem_aeAtlas he hx.1 hx.2)

/-- **`Reg(E_κ) = reg(E_κ)` for `κ ≠ 2π`.** -/
theorem reg_eq (h : α ≠ 2 * π) : Reg (Flat.isom 2) (Minkowski 2) (Massive α) = regPart α := by
  refine Subset.antisymm (fun x hx hxs => ?_) regPart_subset_reg
  obtain ⟨e, he, hxe⟩ := mem_support.1 hx
  exact h (eq_two_pi_of_mem_aeAtlas he hxe hxs)

/-- **`Sing(E_κ) = sing(E_κ)` for `κ ≠ 2π`**, the singular line. -/
theorem sing_eq (h : α ≠ 2 * π) : Sing (Flat.isom 2) (Minkowski 2) (Massive α) = singLine α := by
  rw [Sing, reg_eq h, regPart, compl_compl]

theorem sing_nonempty (h : α ≠ 2 * π) : (Sing (Flat.isom 2) (Minkowski 2) (Massive α)).Nonempty := by
  rw [sing_eq h]
  exact ⟨(0, Cone.apex), rfl⟩

/-- **`hreg` for `κ ≠ 2π`, DEC-25's form**: every chart of the maximal a.e. atlas of `E_κ` is a
chart isomorphism `massive κ → minkowski 2`. -/
theorem chartIso_of_mem_aeAtlas_of_ne (h : α ≠ 2 * π) :
    ∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α), ChartIso (massive α) (minkowski 2) r :=
  forall_chartIso_aeAtlas_of_reg_subset minkowski_causallyArcConnected.absolutelyMinimalOn_all
    Flat.isom_strongMorphism isAEAtlas_sectorAtlas (by rintro _ ⟨k, rfl⟩; exact chartIso_chart k)
    massive_causallyArcConnected.absolutelyMinimalOn_all aeAtlas_eq
    (by rw [reg_eq h, support_sectorAtlas])

/-! ### (3) `κ = 2π`: a chart through the line -/

/-- `C_{2π} → ℂ` in the polar position of a sector chart: `r e^{i(c + arg u)} = e^{ic} u`. -/
theorem planeMap_fromPlane (c : ℝ) (u : ℂ) :
    Cone.planeMap (fromPlane ((c : AddCircle (2 * π))) u) = Complex.exp (c * Complex.I) * u := by
  rw [fromPlane, Cone.planeMap_mk, Cone.toPlane]
  simp only
  rw [← AddCircle.coe_add, Cone.toCircle_coe_two_pi]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I u]
  rw [show ((c + Complex.arg u : ℝ) : ℂ) * Complex.I = c * Complex.I + Complex.arg u * Complex.I by
    push_cast; ring, Complex.exp_add]
  ring

/-- **The identification `E_{2π} → E^{1,2}` as a chart** (`massiveTwoPiToMinkowski`). -/
noncomputable def twoPiChart : OpenPartialHomeomorph (Massive (2 * π)) (Minkowski 2) :=
  (OpenPartialHomeomorph.refl ℝ).prod
    Cone.coneTwoPiIsoEuclidean.toHomeomorph.toOpenPartialHomeomorph

theorem twoPiChart_source : twoPiChart.source = univ := by
  simp [twoPiChart]

theorem twoPiChart_apply (x : Massive (2 * π)) : twoPiChart x = massiveTwoPiToMinkowski x := rfl

/-- `twoPiChart` is an isomorphism of topological spacetimes (`massiveTwoPi_iso`, as a chart). -/
theorem chartIso_twoPiChart : ChartIso (massive (2 * π)) (minkowski 2) twoPiChart :=
  staticCausality.chartIso_prod_isometricOn _ fun x _ y _ => Cone.coneTwoPiIsoEuclidean.dist_eq x y

/-- **`twoPiChart` is one rotation after each sector chart, on its whole source.** -/
theorem twoPiChart_eq_rotIsom_smul (k : Index (2 * π)) {c : ℝ}
    (hc : (c : AddCircle (2 * π)) = k.1.θ) :
    ∀ z ∈ (chart k).source, twoPiChart z = rotIsom c • chart k z := by
  intro z hz
  rw [chart_source] at hz
  have hz2 : z.2 ∈ (planeChart k).target := by rw [planeChart_target]; exact hz.2
  have hzu : z.2 = fromPlane (c : AddCircle (2 * π)) ((planeChart k).symm z.2) := by
    rw [hc, ← planeChart_apply, (planeChart k).right_inv hz2]
  rw [chart_apply, coneChart_apply, rotIsom_smul_repr]
  refine Prod.ext rfl ?_
  show Complex.orthonormalBasisOneI.repr (Cone.planeMap z.2) = _
  conv_lhs => rw [hzu, planeMap_fromPlane]

/-- **`twoPiChart` is a chart of the maximal a.e. atlas of `E_{2π}`.** -/
theorem twoPiChart_mem_aeAtlas :
    twoPiChart ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) := by
  have hrot : ∀ k : Index (2 * π), ∃ c : ℝ,
      ∀ z ∈ (chart k).source, twoPiChart z = rotIsom c • chart k z := fun k => by
    obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective k.1.θ
    exact ⟨c, twoPiChart_eq_rotIsom_smul k hc⟩
  have hGX : IsGXAtlas (Flat.isom 2) (insert twoPiChart (sectorAtlas (2 * π))) := by
    refine isGXAtlas_of_eventually fun e he e' he' x hx => ?_
    rcases he with rfl | ⟨k, rfl⟩ <;> rcases he' with rfl | ⟨k', rfl⟩
    · exact ⟨1, Eventually.of_forall fun _ => (one_smul _ _).symm⟩
    · obtain ⟨c, hc⟩ := hrot k'
      refine ⟨(rotIsom c)⁻¹, ?_⟩
      filter_upwards [(chart k').open_source.mem_nhds hx.2] with y hy
      rw [hc y hy, inv_smul_smul]
    · obtain ⟨c, hc⟩ := hrot k
      refine ⟨rotIsom c, ?_⟩
      filter_upwards [(chart k).open_source.mem_nhds hx.1] with y hy
      exact hc y hy
    · exact isGXAtlas_sectorAtlas.eventually_smul_eq ⟨k, rfl⟩ ⟨k', rfl⟩ hx.1 hx.2
  have hB : IsAEAtlas (Flat.isom 2) (insert twoPiChart (sectorAtlas (2 * π))) :=
    ⟨hGX, isAEAtlas_sectorAtlas.2.mono (support_mono (subset_insert _ _)) (isOpen_support _)⟩
  exact subset_maximalAEAtlas hB (hGX.isThinner_completion_of_subset (subset_insert _ _))
    (mem_insert _ _)

/-- **`Reg(E_{2π}) = E_{2π}`.** -/
theorem reg_eq_univ_two_pi : Reg (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) = univ :=
  eq_univ_of_forall fun x => mem_support.2 ⟨twoPiChart, twoPiChart_mem_aeAtlas, by
    rw [twoPiChart_source]; exact mem_univ x⟩

/-- **`Sing(E_{2π}) = ∅`.** -/
theorem sing_eq_empty_two_pi : Sing (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) = ∅ := by
  rw [Sing, reg_eq_univ_two_pi, compl_univ]

/-- **`hreg` at `κ = 2π`, DEC-25's form**: every chart of the maximal a.e. atlas of `E_{2π}` is a
chart isomorphism, by `chartIso_of_mem_maximalAEAtlas_of_agreeOn` with the agreement at the line
supplied by `twoPiChart`. -/
theorem chartIso_of_mem_aeAtlas_two_pi :
    ∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π)),
      ChartIso (massive (2 * π)) (minkowski 2) r := by
  intro r hr
  have hM : IsGXAtlas (Flat.isom 2) (aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π))) :=
    (isMaximalAEAtlas_aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π))).1.1
  refine chartIso_of_mem_maximalAEAtlas_of_agreeOn
    minkowski_causallyArcConnected.absolutelyMinimalOn_all Flat.isom_strongMorphism
    isAEAtlas_sectorAtlas (by rintro _ ⟨k, rfl⟩; exact chartIso_chart k) hr
    (massive_causallyArcConnected.absolutelyMinimalOn_all _) fun x hx _ => ?_
  obtain ⟨g, O, hxO, hO, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
    (hM.symm_trans_mem twoPiChart_mem_aeAtlas hr) (by rw [twoPiChart_source]; exact mem_univ x) hx
  exact ⟨O, hxO, chartIso_twoPiChart.agreeOn_of_smul Flat.isom_strongMorphism
    ((minkowski 2).chartTransport_chartIso r) hO heq⟩

/-! ### Every `κ > 0` -/

/-- **`hreg` at every `E_κ`, `κ > 0`, DEC-25's form.** -/
theorem chartIso_of_mem_aeAtlas :
    ∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α), ChartIso (massive α) (minkowski 2) r := by
  by_cases h : α = 2 * π
  · subst h
    exact chartIso_of_mem_aeAtlas_two_pi
  · exact chartIso_of_mem_aeAtlas_of_ne h

/-- **The two cases**: for `κ ≠ 2π` the singular locus is the line, for `κ = 2π` it is empty. -/
theorem reg_sing_cases :
    (α ≠ 2 * π ∧ Reg (Flat.isom 2) (Minkowski 2) (Massive α) = regPart α ∧
        Sing (Flat.isom 2) (Minkowski 2) (Massive α) = singLine α) ∨
      (α = 2 * π ∧ Reg (Flat.isom 2) (Minkowski 2) (Massive α) = univ ∧
        Sing (Flat.isom 2) (Minkowski 2) (Massive α) = ∅) := by
  by_cases h : α = 2 * π
  · right
    subst h
    exact ⟨rfl, reg_eq_univ_two_pi, sing_eq_empty_two_pi⟩
  · exact Or.inl ⟨h, reg_eq h, sing_eq h⟩

/-- **A chart of the maximal atlas of `E_κ` meets the singular line iff `κ = 2π`.** -/
theorem exists_mem_aeAtlas_inter_singLine_iff :
    (∃ e ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive α), (e.source ∩ singLine α).Nonempty) ↔
      α = 2 * π := by
  constructor
  · rintro ⟨e, he, x, hx, hxs⟩
    exact eq_two_pi_of_mem_aeAtlas he hx hxs
  · intro h
    subst h
    exact ⟨twoPiChart, twoPiChart_mem_aeAtlas, (0, Cone.apex),
      by rw [twoPiChart_source]; exact mem_univ _, rfl⟩

/-- **`Reg(E_κ) = reg(E_κ)` iff `κ ≠ 2π`.** -/
theorem reg_eq_regPart_iff :
    Reg (Flat.isom 2) (Minkowski 2) (Massive α) = regPart α ↔ α ≠ 2 * π := by
  refine ⟨fun hR h => ?_, reg_eq⟩
  subst h
  rw [reg_eq_univ_two_pi] at hR
  have : ((0 : ℝ), (Cone.apex : Cone (2 * π))) ∈ regPart (2 * π) := hR ▸ mem_univ _
  exact this rfl

/-! ### (b′) at regular sources, between the models -/

/-- **The models `E_κ`, `κ > 0`, as one family** with their singular structures. -/
noncomputable abbrev singularGXFamily (κ : {κ : ℝ // 0 < κ}) :
    SingularGXStructure (Flat.isom 2) (Minkowski 2) (Massive κ.1) :=
  @singularGX κ.1 ⟨κ.2⟩

attribute [local instance] singularGXFamily

/-- **`hreg` for the family of the models `E_κ`, `κ > 0`**, in the form of
`existsUnique_causality_singularGX_dec25`. -/
theorem hreg_family : ∀ κ : {κ : ℝ // 0 < κ}, ∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive κ.1),
    ChartIso (massiveOf κ) (minkowski 2) r :=
  fun κ => @chartIso_of_mem_aeAtlas κ.1 ⟨κ.2⟩

/-- **(b′) of `existsUnique_causality_singularGX_dec25` at regular sources, between any two models**
`E_κ`, `E_κ'`, `κ, κ' > 0`: an a.e. isomorphism chart `ψ : E_κ ⇀ E_κ'` whose source lies in
`Reg(E_κ)` is a chart isomorphism (`chartIso_model_of_subset_reg`, from `hreg`). -/
theorem chartIso_of_isAEChart_of_subset_reg {κ κ' : {κ : ℝ // 0 < κ}}
    {ψ : OpenPartialHomeomorph (Massive κ.1) (Massive κ'.1)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ)
    (hsub : ψ.source ⊆ Reg (Flat.isom 2) (Minkowski 2) (Massive κ.1)) :
    ChartIso (massiveOf κ) (massiveOf κ') ψ :=
  chartIso_model_of_subset_reg (Xα := fun κ : {κ : ℝ // 0 < κ} => Massive κ.1) (a := κ) (b := κ')
    (minkowski 2) massiveOf Flat.isom_strongMorphism
    (fun κ => @massive_causallyArcConnected κ.1 ⟨κ.2⟩) hreg_family hψ hsub

/-- **(b′) from `E_{2π}`, every source**: since `Reg(E_{2π}) = E_{2π}`, every a.e. isomorphism
chart `E_{2π} ⇀ E_κ'`, `κ' > 0`, is a chart isomorphism, the singular line of `E_{2π}` included. -/
theorem chartIso_of_isAEChart_two_pi {κ' : {κ : ℝ // 0 < κ}}
    {ψ : OpenPartialHomeomorph (Massive (2 * π)) (Massive κ'.1)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) :
    ChartIso (massive (2 * π)) (massiveOf κ') ψ :=
  chartIso_of_isAEChart_of_subset_reg (κ := ⟨2 * π, two_pi_pos⟩) hψ fun x _ => by
    have : x ∈ Reg (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) := by
      rw [reg_eq_univ_two_pi]; exact mem_univ x
    exact this

/-- **(b′) at regular sources, from `E_κ`, `κ ≠ 2π`**: an a.e. isomorphism chart
`ψ : E_κ ⇀ E_κ'` whose source avoids the singular line is a chart isomorphism. -/
theorem chartIso_of_isAEChart_of_subset_regPart {κ κ' : {κ : ℝ // 0 < κ}} (h : κ.1 ≠ 2 * π)
    {ψ : OpenPartialHomeomorph (Massive κ.1) (Massive κ'.1)}
    (hψ : IsAEChart (Flat.isom 2) (Minkowski 2) ψ) (hsub : ψ.source ⊆ regPart κ.1) :
    ChartIso (massiveOf κ) (massiveOf κ') ψ :=
  chartIso_of_isAEChart_of_subset_reg hψ (by
    have := @reg_eq κ.1 ⟨κ.2⟩ h
    exact hsub.trans this.ge)

/-! ### Non-vacuity -/

/-- **The continuation lemma's hypotheses are satisfiable**: at `κ = 2π`, `twoPiChart` is
compatible with every sector chart and its source contains the singular line
(`EAlphaContinuation.exists_smul_devPt` applies to it). -/
theorem continuation_nonvacuous :
    (∀ k : Index (2 * π), twoPiChart.symm.trans (chart k) ∈ gxGroupoid (Flat.isom 2) (Minkowski 2)) ∧
      ((0, Cone.apex) : Massive (2 * π)) ∈ twoPiChart.source :=
  ⟨compatible_of_mem_aeAtlas twoPiChart_mem_aeAtlas, by rw [twoPiChart_source]; exact mem_univ _⟩


/-- `π > 0`, an instance local to this file, for the witness at `κ = π`. -/
theorem fact_pi_pos : Fact (0 < π) := ⟨pi_pos⟩

/-- `4π > 0`, an instance local to this file, for the witness at `κ = 4π`. -/
theorem fact_four_pi_pos : Fact (0 < 4 * π) := ⟨by positivity⟩

attribute [local instance] fact_pi_pos fact_four_pi_pos

/-- **Non-vacuity**: at `κ = π` (deficit) and `κ = 4π` (excess) the singular locus is the line, not
empty; at `κ = 2π` it is empty and `twoPiChart` is a chart through the line; `hreg` holds at all
three, and (a), (b) of `existsUnique_causality_singularGX_dec25` hold at each model. -/
theorem nonvacuous :
    Sing (Flat.isom 2) (Minkowski 2) (Massive π) = singLine π ∧
    (Sing (Flat.isom 2) (Minkowski 2) (Massive π)).Nonempty ∧
    Sing (Flat.isom 2) (Minkowski 2) (Massive (4 * π)) = singLine (4 * π) ∧
    (Sing (Flat.isom 2) (Minkowski 2) (Massive (4 * π))).Nonempty ∧
    Reg (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) = univ ∧
    twoPiChart ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π)) ∧
    ((0, Cone.apex) : Massive (2 * π)) ∈ twoPiChart.source ∧
    (∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive π), ChartIso (massive π) (minkowski 2) r) ∧
    (∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (2 * π)),
      ChartIso (massive (2 * π)) (minkowski 2) r) ∧
    (∀ r ∈ aeAtlas (Flat.isom 2) (Minkowski 2) (Massive (4 * π)),
      ChartIso (massive (4 * π)) (minkowski 2) r) ∧
    -- (a)
    (minkowski 2).CausallyArcConnected ∧
    (∀ g : Flat.isom 2, StrongMorphism (minkowski 2) (minkowski 2) fun p => g • p) ∧
    -- (b)
    (massive π).CausallyArcConnected ∧ (massive (2 * π)).CausallyArcConnected ∧
    (massive (4 * π)).CausallyArcConnected := by
  have hπ : π ≠ 2 * π := by linarith [pi_pos]
  have h4π : 4 * π ≠ 2 * π := by linarith [pi_pos]
  exact ⟨sing_eq hπ, sing_nonempty hπ, sing_eq h4π, sing_nonempty h4π, reg_eq_univ_two_pi,
    twoPiChart_mem_aeAtlas, by rw [twoPiChart_source]; exact mem_univ _, chartIso_of_mem_aeAtlas,
    chartIso_of_mem_aeAtlas, chartIso_of_mem_aeAtlas, minkowski_causallyArcConnected,
    Flat.isom_strongMorphism, massive_causallyArcConnected, massive_causallyArcConnected,
    massive_causallyArcConnected⟩

end EAlphaGX

end Causal
