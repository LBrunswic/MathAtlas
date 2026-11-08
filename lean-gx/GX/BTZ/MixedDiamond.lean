import GX.BTZ.AbsMax

/-!
# `GX.BTZ.MixedDiamond` — the mixed diamonds of B21 Prop 2.17 (DEC-126), 0 `sorry`

Package WP-47d. `brunswic2021cauchy` (**B21**, `papers/gx/sources/2108.12631/src/BTZ_1.tex`), §2.4.
In the push-out `M̄ = M ∪_{Reg M} N` of a globally hyperbolic Cauchy-maximal `𝔼₀`-manifold `M` and a
globally hyperbolic flat spacetime `N` along an isometric embedding `f` of `Reg M`, every **mixed
diamond** `J(p, q)` (`p` BTZ, `q` regular) is compact — the one leaf of `GX.BTZ.AbsMax`
(`E0Pushout.isCompact_diamond_mixed`), built here IN GX (DEC-126) with neither a Lorentzian
volume nor a time separation: the Lorentz-invariant size is the **affine parameter of a null
geodesic**. No gx ledger label; cited results built here (DEC-23). Rows:

* **`brunswic2021cauchy:prop:abs_max`** (Prop 2.17, `A = {0}`) — `BTZ_1.tex:1078–1082`, proof
  l.1088–1117 (closed, DEC-107 / DEC-117 / DEC-125 (e)): the mixed diamonds
  `GX.E0MixedDiamond.isCompact_diamond_mixed` (the leaf's statement verbatim), the push-out GH
  `GX.E0MixedDiamond.globallyHyperbolic_pushout`, and the form of record with no `sorry` beneath
  `GX.E0MixedDiamond.prop_abs_max_C1_spear` (`absMax_e0RegM_spear`).
* **`brunswic2021cauchy:cor:abs_max`** (Cor 2.18) — `BTZ_1.tex:1083–1086` (closed, DEC-107 /
  DEC-117): `GX.E0MixedDiamond.cor_abs_max_C1_spear`, AbsMax's `cor_abs_max_C1` verbatim with no
  `sorry` beneath (DEC-28's input to the headline).

> We are then left with the case $p\in \sing_0(M)$ and $q\in N$. Consider a spear neighborhood
> $\mathcal S$ in $M$ of vertex $p$ […] The spear $\S$ can be chosen in such a way that $q\notin \S$.
> […] define $K := J^+(\mathcal C)\cap J^-(q)$. […] Define $K':=K\cap \partial S\subset M$, since
> $\partial S$ is closed, then $K'$ is compact. […]
> $$ J^+(p)\cap J^-(q) \subset \left[J^-_N(q)\cap J^+_N(K')\right] ~\cup~  \left[J^-_M( K' )\cap
> J^+_M(p)\right] $$ (l.1104–1115)

## The gap in the printed proof, and its repair (finding)

`∂𝒮` is closed in `M`, not in `M̄`: shaft points `ψ(τₙ, R, θₙ)`, `τₙ → ∞`, may converge in `M̄` to
a point of `N ∖ f(Reg M)`, so `K'` is not known compact (WP-46f) — equivalently nothing in the
printed argument excludes that the whole future BTZ ray of `p` lies below `q`. Repair:

1. **No vertical null line of an `𝔼₀`-morphism converges to a regular point** (`vertical_noLimit`):
   in a regular chart at the limit, `σ ↦ φ(σ, z)` reads near every `σ` as `k • D(σ, |z|, arg z)`,
   `k ∈ Isom(𝐌³)`, `D` the paper's developing map (`btzPaperDev`), AFFINE in `σ` with the null
   velocity `(1, (1, 0))` (`btzPaperDev_vertical`); a curve locally affine with nonzero velocity
   diverges (`affine_noLimit`).
2. **The BTZ ray of `p` is bounded below `q`** (`exists_bound_axis`): else regular points of the
   spear below `q' ≫ q` at every height (`exists_regular_le`) and their exits from truncated spears
   (`SpearChart.exit`) give points below `q'` at arbitrarily large height with radius bounded below;
   compactness of the annulus and closedness of `J⁻_N(q')` then put a WHOLE vertical null line
   below `q'` (`circle_trick`), which lies in a compact diamond of `N`, converges, and contradicts 1.
3. **Truncate the spear at a lid above the bound**: no lid point is below `q`; a relation from a
   point of `𝒬 = 𝒮 ∩ {τ ≤ T}` to a point outside leaves `𝒬` through the wall (`SpearChart.exit`:
   real induction along a causal curve with the chart's local isomorphism `exists_locIso`), and
   `J(p, q) = Φ(𝒬 ∩ J⁻(E)) ∪ ι₂(J⁺_N(E) ∩ J⁻_N(q))`, `E` the compact set of wall points below `q`.

## Hypothesis checklist

| paper | here |
|---|---|
| `M` GH Cauchy-compact Cauchy-maximal `𝔼_A`-manifold | GH + `IsE0CauchyMaximal` (DEC-77 (c)); `A = {0}` (DEC-125 (e)); Cauchy-compact read as a compact `C¹` spacelike Cauchy surface (DEC-107) in Prop 2.17 / Cor 2.18; the mixed diamonds do NOT use Cauchy-compactness |
| `N` GH `𝔼_{A*}`-manifold, `A* = ∅` | a GH flat spacetime (`Causal.Flat.GH`); connected targets (DEC-125 (e)) |
| `M̄` the push-out (Lemma 2.12) | `E0AbsMax.E0Pushout`, built by `exists_e0Pushout` |
| spear neighbourhood of vertex `p` (Lemma 2.3) | `E0Spear.lem_tube_e0` (strict), transported by `ι₁` (`exists_spearChart`) |

## SCOPE (0 `sorry`, standard axioms: `campaign/WP-47d/axioms.out`)

* The file imports `GX.BTZ.AbsMax` (its `E0Pushout`, Lemma 2.13(b), Prop 2.16), so AbsMax
  cannot import it: graduation either moves §1–§4 into AbsMax above the leaf (they use only
  AbsMax declarations stated before `E0Pushout.isCompact_diamond_mixed`) and closes the leaf by
  `E0MixedDiamond.isCompact_diamond_mixed _hGH _hmax _hN P _hp _hq`, or keeps this file and points
  `GX.BTZ.Uniformization`'s `E0MixedDiamondsCompact` at it; both discharges are
  typechecked in `campaign/WP-47d/Discharge.lean`.
* §5 restates AbsMax's `globallyHyperbolic` / `absMax_e0RegM` / `prop_abs_max_C1` /
  `cor_abs_max_C1` with the leaf discharged (suffix `_spear`), verbatim otherwise.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0MixedDiamond

/-! ### §0 A curve of a normed space that is locally affine with nonzero velocity diverges -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A locally affine curve with nonzero velocity has no limit at `+∞`.** If near every
`σ > σ₁` the curve `F` is `σ' ↦ F σ + (σ' − σ) • w` with `w ≠ 0` (the velocity may a priori vary
with `σ`), then the velocity is locally constant, hence constant on `]σ₁, +∞[`, so `F` is affine
there with nonzero velocity and diverges. -/
theorem affine_noLimit {F : ℝ → E} {σ₁ : ℝ}
    (hloc : ∀ σ, σ₁ < σ → ∃ w : E, w ≠ 0 ∧ ∀ᶠ σ' in 𝓝 σ, F σ' = F σ + (σ' - σ) • w)
    (L : E) : ¬ Tendsto F atTop (𝓝 L) := by
  intro hlim
  choose! w hw0 hw using hloc
  -- `F` has derivative `w σ'` at every `σ'` near `σ`
  have hder : ∀ σ, σ₁ < σ → ∀ᶠ σ' in 𝓝 σ, HasDerivAt F (w σ) σ' := by
    intro σ hσ
    filter_upwards [(hw σ hσ).eventually_nhds] with σ' hσ'
    have h1 : HasDerivAt (fun σ'' => F σ + (σ'' - σ) • w σ) (w σ) σ' := by
      have := (((hasDerivAt_id σ').sub_const σ).smul_const (w σ)).const_add (F σ)
      simpa using this
    exact h1.congr_of_eventuallyEq hσ'
  have hD : ∀ σ, σ₁ < σ → ∀ᶠ σ' in 𝓝 σ, deriv F σ' = w σ := fun σ hσ =>
    (hder σ hσ).mono fun σ' h => h.deriv
  -- the velocity `deriv F` is constant on `]σ₁, +∞[`
  have hDd : ∀ σ, σ₁ < σ → HasDerivAt (deriv F) 0 σ := fun σ hσ =>
    (hasDerivAt_const σ (w σ)).congr_of_eventuallyEq (hD σ hσ)
  have hconst : ∀ σ, σ₁ < σ → deriv F σ = deriv F (σ₁ + 1) := fun σ hσ =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hDd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hDd x hx).deriv) hσ (show σ₁ < σ₁ + 1 by linarith)
  set w₀ := deriv F (σ₁ + 1) with hw₀
  have hw₀ne : w₀ ≠ 0 := by
    rw [hw₀, (hD (σ₁ + 1) (by linarith)).self_of_nhds]; exact hw0 _ (by linarith)
  have hFd : ∀ σ, σ₁ < σ → HasDerivAt F w₀ σ := fun σ hσ => by
    have h := (hder σ hσ).self_of_nhds
    rw [← hconst σ hσ, (hD σ hσ).self_of_nhds]; exact h
  -- `G = F − σ • w₀` is constant on `]σ₁, +∞[`
  set G : ℝ → E := fun σ => F σ - σ • w₀ with hG
  have hGd : ∀ σ, σ₁ < σ → HasDerivAt G 0 σ := fun σ hσ => by
    have := (hFd σ hσ).sub ((hasDerivAt_id σ).smul_const w₀)
    simp only [one_smul, sub_self] at this
    exact this
  have hGc : ∀ σ, σ₁ < σ → G σ = G (σ₁ + 1) := fun σ hσ =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hGd x hx).deriv) hσ (show σ₁ < σ₁ + 1 by linarith)
  -- so `‖F σ − G₀‖ = |σ| ‖w₀‖` diverges, against the limit
  have h1 : Tendsto (fun σ => ‖F σ - G (σ₁ + 1)‖) atTop (𝓝 ‖L - G (σ₁ + 1)‖) :=
    (hlim.sub_const _).norm
  have h2 : Tendsto (fun σ => ‖F σ - G (σ₁ + 1)‖) atTop atTop := by
    have h3 : Tendsto (fun σ : ℝ => σ * ‖w₀‖) atTop atTop :=
      tendsto_id.atTop_mul_const (norm_pos_iff.2 hw₀ne)
    refine h3.congr' (eventually_atTop.2 ⟨max σ₁ 0 + 1, fun σ hσ => ?_⟩)
    have hσ₁ : σ₁ < σ := by linarith [le_max_left σ₁ 0]
    have hσ0 : 0 ≤ σ := by linarith [le_max_right σ₁ 0]
    have : F σ - G (σ₁ + 1) = σ • w₀ := by
      rw [← hGc σ hσ₁, hG]; simp
    show σ * ‖w₀‖ = ‖F σ - G (σ₁ + 1)‖
    rw [this, norm_smul, Real.norm_of_nonneg hσ0]
  exact not_tendsto_nhds_of_tendsto_atTop h2 _ h1

end Affine

/-! ### §1 Spear charts in an `𝔼₀`-manifold, and their local isomorphism -/

section Chart

open E0CBG E0Spear E0

/-- **A spear chart of vertex `p`** (the data of B21 Def 2.1's spear neighbourhood, `E0Spear.IsSpearNbhd`,
transported to any `𝔼₀`-manifold `X`): an injective `𝔼₀`-morphism `φ` on an open `W ⊇ spearY v R`
sending the vertex `(v, 0)` to `p`. -/
structure SpearChart (X : Type) [TopologicalSpace X] [ChartedSpace E0Y X] (p : X) where
  v : ℝ
  R : ℝ
  pos : 0 < R
  W : Set E0Y
  φ : E0Y → X
  isOpen : IsOpen W
  sub : spearY v R ⊆ W
  mor : IsE0Mor φ W
  inj : InjOn φ W
  vertex : φ (yVertex v) = p

namespace SpearChart

variable {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X] {p : X} (S : SpearChart X p)

/-- The chart read in the paper's coordinates `(τ, z)`. -/
noncomputable def Φ (x : E0) : X := S.φ (paperInY x)

/-- Its domain in the paper's coordinates. -/
def O : Set E0 := paperInY ⁻¹' S.W

theorem isOpen_O : IsOpen S.O := S.isOpen.preimage continuous_paperInY

/-- `O` as an open set. -/
def OO : Opens E0 := ⟨S.O, S.isOpen_O⟩

theorem spear_subset_O {ρ : ℝ} (hρ : ρ ≤ S.R) : spear S.v ρ ⊆ S.O := fun x hx =>
  S.sub ⟨x, spear_mono le_rfl hρ hx, rfl⟩

theorem continuousOn_φ : ContinuousOn S.φ S.W := fun y hy => (S.mor y hy).continuousWithinAt

theorem continuousOn : ContinuousOn S.Φ S.O :=
  S.continuousOn_φ.comp continuous_paperInY.continuousOn fun _ hx => hx

theorem injOn : InjOn S.Φ S.O := fun x hx y hy h =>
  paperInY.injOn (by simp) (by simp) (S.inj hx hy h)

theorem Φ_vertex : S.Φ (S.v, 0) = p := S.vertex

variable [HasGroupoid X e0Groupoid]

/-- **Relations of the spear transfer to `X`.** -/
theorem le_of_le {x y : E0} (hx : x ∈ spear S.v S.R) (hy : y ∈ spear S.v S.R)
    (h : causality.le ⊤ x y) : (CE X).le ⊤ (S.Φ x) (S.Φ y) :=
  le_of_isE0Mor_paper S.isOpen S.mor (U := S.OO) subset_rfl
    (le_of_le_top_of_mem_spear (S.spear_subset_O le_rfl) hx hy h)

omit [HasGroupoid X e0Groupoid] in
/-- **The BTZ points of the chart are its axis points.** -/
theorem mem_S0_iff {x : E0} (hx : x ∈ S.O) : S.Φ x ∈ S0 X ↔ x ∈ axis := by
  have h := Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem S.isOpen S.mor hx
    (le_refl (0 : ℝ))
  show S.φ (paperInY x) ∈ _ ↔ _
  rw [← h]
  show chartAt E0Y (paperInY x) (paperInY x) ∈ e0SingY 0 ↔ _
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  constructor
  · intro h'
    by_contra hax
    exact h'.2 (paperInY_mem_e0Reg_iff.2 hax)
  · intro hax
    exact ⟨rfl, fun h' => paperInY_mem_e0Reg_iff.1 h' hax⟩

/-- The image of an open subset of `O` is open. -/
theorem isOpen_image {U : Set E0} (hU : IsOpen U) (hUO : U ⊆ S.O) : IsOpen (S.Φ '' U) := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨S.W, S.isOpen⟩) S.mor
  have h := hE.isOpen_image (Causal.chartImage paperInY ⟨U, hU⟩) (by
    intro y hy
    rw [← SetLike.mem_coe, Causal.coe_chartImage] at hy
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
    exact hUO hx)
  convert h using 1
  rw [Causal.coe_chartImage, paperInY_source, univ_inter, image_image]
  rfl

/-- **The local isomorphism of a spear chart** (`IsEMorphismOn.locally`, read in the paper's
coordinates): every point of `O` has an open neighbourhood `U₀ ⊆ O` such that, for every open
`U ⊆ U₀`, a relation of `X` inside `Φ(U)` between two points of `Φ(U)` is a relation of `𝔼₀`. -/
theorem exists_locIso {y₀ : E0} (hy₀ : y₀ ∈ S.O) :
    ∃ U₀ : Opens E0, y₀ ∈ U₀ ∧ (U₀ : Set E0) ⊆ S.O ∧ ∀ U : Opens E0, U ≤ U₀ →
      ∀ V : Opens X, (V : Set X) = S.Φ '' U → ∀ a ∈ U, ∀ b ∈ U,
        (CE X).le V (S.Φ a) (S.Φ b) → causality.le ⊤ a b := by
  have hE := Causal.CBG.isEMorphismOn_of_liftPropOn E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ (W := ⟨S.W, S.isOpen⟩) S.mor
  obtain ⟨V₀, hV₀W, hyV₀, -, hiso⟩ := hE.locally (paperInY y₀) hy₀
  refine ⟨⟨paperInY ⁻¹' V₀, V₀.isOpen.preimage continuous_paperInY⟩, hyV₀,
    fun x hx => hV₀W hx, fun U hU V hV a ha b hb hab => ?_⟩
  set V' : Opens E0Y := Causal.chartImage paperInY U with hV'
  have hV'V₀ : V' ≤ V₀ := by
    intro y hy
    rw [← SetLike.mem_coe, hV', Causal.coe_chartImage] at hy
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
    exact hU hx
  have hVimg : (V : Set X) = S.φ '' V' := by
    rw [hV, hV', Causal.coe_chartImage, paperInY_source, univ_inter, image_image]
    rfl
  have haV' : paperInY a ∈ V' := Causal.mem_chartImage_of_mem (by simp) ha
  have hbV' : paperInY b ∈ V' := Causal.mem_chartImage_of_mem (by simp) hb
  have h1 := ((hiso V' hV'V₀ V hVimg _ haV' _ hbV').1).2 hab
  have h2 := (ceY_le_iff haV' hbV').1 h1
  have h3 := ((chartIso_paperInY U (fun z _ => by simp [Causal.chartSource]) a ha b hb).1).2 h2
  exact causality.le_mono le_top h3

/-- **A causal curve of `X` inside the image of a local-isomorphism neighbourhood is a relation of
`𝔼₀`.** -/
theorem le_of_curve {U₀ : Opens E0} (hU₀O : (U₀ : Set E0) ⊆ S.O)
    (hU₀ : ∀ U : Opens E0, U ≤ U₀ → ∀ V : Opens X, (V : Set X) = S.Φ '' U → ∀ a ∈ U, ∀ b ∈ U,
      (CE X).le V (S.Φ a) (S.Φ b) → causality.le ⊤ a b)
    {c : ℝ → X} {s s' : ℝ} (hss' : s ≤ s') (hc : (CE X).CausalCurveOn ⊤ c s s')
    (hmem : ∀ σ ∈ Icc s s', c σ ∈ S.Φ '' U₀) {a b : E0} (ha : a ∈ U₀) (hb : b ∈ U₀)
    (hca : c s = S.Φ a) (hcb : c s' = S.Φ b) : causality.le ⊤ a b := by
  rcases hss'.eq_or_lt with h | h
  · subst h
    have : a = b := S.injOn (hU₀O ha) (hU₀O hb) (hca.symm.trans hcb)
    subst this
    exact causality.le_refl trivial
  set V : Opens X := ⟨S.Φ '' U₀, S.isOpen_image U₀.isOpen hU₀O⟩
  have hcV : (CE X).CausalCurveOn V c s s' := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
  have hle : (CE X).le V (c s) (c s') :=
    Causal.CurveOn.rel_of_lt (CE X).isRelFamily_le hcV le_rfl h le_rfl
  rw [hca, hcb] at hle
  exact hU₀ U₀ le_rfl V rfl a ha b hb hle

/-- **Exit from a truncated spear** (the curve-exit step of B21 l.1110–1113, repaired: the spear is
truncated at the lid `τ = T`, so that its image is compact, hence closed in `X`). Let
`𝒬 = spear(v, ρ) ∩ {τ ≤ T}`. A relation `Φ a ≤ b` from a point of `𝒬` to a point outside `Φ(𝒬)`
passes through a point `Φ e` of the wall `{r = ρ}` or of the lid `{τ = T}` of `𝒬`, with `a ≤ e` in
`𝔼₀`. Along a causal curve, the last point of the first stretch inside `Φ(𝒬)` is reached from `a`
inside `𝔼₀` (real induction with the local isomorphism `exists_locIso`); there, no point of the
interior or of the head can be left, since `f = τ − r/2` is non-decreasing. -/
theorem exit [T2Space X] {ρ T : ℝ} (hρ : ρ ≤ S.R) {a : E0}
    (ha : a ∈ spear S.v ρ ∩ {x : E0 | x.1 ≤ T}) {b : X}
    (hb : b ∉ S.Φ '' (spear S.v ρ ∩ {x : E0 | x.1 ≤ T})) (hab : (CE X).le ⊤ (S.Φ a) b) :
    ∃ e ∈ spear S.v ρ ∩ {x : E0 | x.1 ≤ T}, (rad e = ρ ∨ e.1 = T) ∧ causality.le ⊤ a e ∧
      (CE X).le ⊤ (S.Φ e) b := by
  set Q := spear S.v ρ ∩ {x : E0 | x.1 ≤ T} with hQ
  have hQc : IsCompact Q := isCompact_spear_inter_le _ _ _
  have hQO : Q ⊆ S.O := fun x hx => S.spear_subset_O hρ hx.1
  have hKc : IsCompact (S.Φ '' Q) := hQc.image_of_continuousOn (S.continuousOn.mono hQO)
  have hK : IsClosed (S.Φ '' Q) := hKc.isClosed
  obtain ⟨c, hc, hc0, hc1⟩ := (E0LM.e0_causallyArcConnected (M := X) ⊤ le_rfl _ _).1.1 hab
  have hcont : ContinuousOn c (Icc 0 1) := hc.continuousOn (CE X).isRelFamily_le
  -- the first exit time `s₁`
  set Sx : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ c s ∉ S.Φ '' Q} with hSx
  have h1S : (1 : ℝ) ∈ Sx := ⟨right_mem_Icc.2 zero_le_one, by rw [hc1]; exact hb⟩
  have hSne : Sx.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow Sx := ⟨0, fun t ht => ht.1.1⟩
  set s₁ := sInf Sx with hs₁
  have hs₁0 : 0 ≤ s₁ := le_csInf hSne fun t ht => ht.1.1
  have hs₁1 : s₁ ≤ 1 := csInf_le hSbdd h1S
  have hlow : ∀ s ∈ Ico (0 : ℝ) s₁, c s ∈ S.Φ '' Q := fun s hs => by
    by_contra hsK
    exact absurd (csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hs₁1⟩, hsK⟩) (not_le.2 hs.2)
  have hc0K : c 0 ∈ S.Φ '' Q := by rw [hc0]; exact ⟨a, ha, rfl⟩
  have hs₁K : c s₁ ∈ S.Φ '' Q := by
    rcases hs₁0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hc0K
    · have hcw : ContinuousWithinAt c (Ico 0 s₁) s₁ :=
        (hcont s₁ ⟨hs₁0, hs₁1⟩).mono fun s hs => ⟨hs.1, hs.2.le.trans hs₁1⟩
      have hcl : c s₁ ∈ closure (c '' Ico 0 s₁) :=
        hcw.mem_closure_image (by rw [closure_Ico h0.ne]; exact right_mem_Icc.2 h0.le)
      exact closure_minimal (by rintro _ ⟨s, hs, rfl⟩; exact hlow s hs) hK hcl
  have hs₁lt : s₁ < 1 := by
    refine lt_of_le_of_ne hs₁1 fun h => hb ?_
    rw [← hc1, ← h]; exact hs₁K
  -- the local isomorphism along the curve
  have hstep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ e ∈ S.O, c s = S.Φ e → ∀ U : Opens E0, e ∈ U →
      (U : Set E0) ⊆ S.O → ∃ ε > 0, ∀ σ ∈ Icc (0 : ℝ) 1, |σ - s| < ε → c σ ∈ S.Φ '' U := by
    intro s hs e he hce U heU hUO
    have hopen := S.isOpen_image U.isOpen hUO
    have hmem : S.Φ '' U ∈ 𝓝 (c s) := hopen.mem_nhds (by rw [hce]; exact ⟨e, heU, rfl⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hcont s hs hmem)
    exact ⟨ε, hε, fun σ hσ hσs => hball ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact hσs, hσ⟩⟩
  -- real induction: `c s` stays in `Φ(𝒬 ∩ J⁺(a))` up to `s₁`
  set KA := Q ∩ causality.Jplus ⊤ {a} with hKA
  have hKAc : IsCompact (S.Φ '' KA) :=
    (hQc.inter_right (E0.isClosed_Jplus a)).image_of_continuousOn
      (S.continuousOn.mono (inter_subset_left.trans hQO))
  set G : Set ℝ := {s | c s ∈ S.Φ '' KA} with hG
  have hGcl : IsClosed (G ∩ Icc 0 s₁) := by
    rw [inter_comm]
    exact (hcont.mono (Icc_subset_Icc le_rfl hs₁1)).preimage_isClosed_of_isClosed isClosed_Icc
      hKAc.isClosed
  have hG0 : (0 : ℝ) ∈ G := by
    rw [hG, mem_setOf_eq, hc0]
    exact ⟨a, ⟨ha, Causal.Precausality.mem_Jplus_singleton.2 (causality.le_refl trivial)⟩, rfl⟩
  have hGs₁ : Icc 0 s₁ ⊆ G := by
    refine hGcl.Icc_subset_of_forall_exists_gt hG0 fun x hx y hy => ?_
    obtain ⟨e, ⟨heQ, hae⟩, hce⟩ := hx.1
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.2.1, hx.2.2.le.trans hs₁1⟩
    obtain ⟨U₀, heU₀, hU₀O, hU₀⟩ := S.exists_locIso (hQO heQ)
    obtain ⟨ε, hε, hball⟩ := hstep x hxI e (hQO heQ) hce.symm U₀ heU₀ hU₀O
    set σ := min y (min (x + ε / 2) ((x + s₁) / 2)) with hσ
    have hxs₁ := hx.2.2
    have hxσ : x < σ := lt_min hy (lt_min (by linarith) (by linarith))
    have hσy : σ ≤ y := min_le_left _ _
    have hσs₁ : σ < s₁ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
    have hσε : σ ≤ x + ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hseg : ∀ τ ∈ Icc x σ, c τ ∈ S.Φ '' U₀ := fun τ hτ =>
      hball τ ⟨hx.2.1.trans hτ.1, (hτ.2.trans hσs₁.le).trans hs₁1⟩
        (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])
    obtain ⟨e', he'Q, hce'⟩ := hlow σ ⟨by linarith [hx.2.1], hσs₁⟩
    obtain ⟨e'', he''U, hce''⟩ := hseg σ ⟨hxσ.le, le_rfl⟩
    have he' : e'' = e' := S.injOn (hU₀O he''U) (hQO he'Q) (hce''.trans hce'.symm)
    subst he'
    have hcurve : (CE X).CausalCurveOn ⊤ c x σ :=
      Causal.CurveOn.restrict hc hx.2.1 ((hσs₁.le.trans hs₁1)) le_rfl fun τ hτ =>
        hc.mem τ ⟨hx.2.1.trans hτ.1, (hτ.2.trans hσs₁.le).trans hs₁1⟩
    have hee' := S.le_of_curve hU₀O hU₀ hxσ.le hcurve hseg heU₀ he''U hce.symm hce''.symm
    refine ⟨σ, ⟨e'', ⟨he'Q, ?_⟩, hce''⟩, hxσ, hσy⟩
    exact Causal.Precausality.mem_Jplus_singleton.2
      (causality.le_trans (Causal.Precausality.mem_Jplus_singleton.1 hae) hee')
  obtain ⟨e, ⟨heQ, hae⟩, hce⟩ := hGs₁ ⟨hs₁0, le_rfl⟩
  have hae' := Causal.Precausality.mem_Jplus_singleton.1 hae
  refine ⟨e, heQ, ?_, hae', ?_⟩
  · -- the exit point is on the wall or the lid
    by_contra hwl
    push Not at hwl
    have her : rad e < ρ := lt_of_le_of_ne heQ.1.2 hwl.1
    have heT : e.1 < T := lt_of_le_of_ne heQ.2 hwl.2
    obtain ⟨U₀, heU₀, hU₀O, hU₀⟩ := S.exists_locIso (hQO heQ)
    set U₁ : Opens E0 := U₀ ⊓ ⟨{x : E0 | rad x < ρ ∧ x.1 < T},
      (isOpen_lt continuous_rad continuous_const).inter (isOpen_lt continuous_fst continuous_const)⟩
    have heU₁ : e ∈ U₁ := ⟨heU₀, her, heT⟩
    have hU₁O : (U₁ : Set E0) ⊆ S.O := fun x hx => hU₀O hx.1
    obtain ⟨ε, hε, hball⟩ := hstep s₁ ⟨hs₁0, hs₁1⟩ e (hQO heQ) hce.symm U₁ heU₁ hU₁O
    obtain ⟨σ, hσS, hσlt⟩ := exists_lt_of_csInf_lt hSne
      (show s₁ < min (s₁ + ε / 2) 1 from lt_min (by linarith) hs₁lt)
    have hs₁σ : s₁ ≤ σ := csInf_le hSbdd hσS
    have hσε : σ < s₁ + ε / 2 := hσlt.trans_le (min_le_left _ _)
    have hseg : ∀ τ ∈ Icc s₁ σ, c τ ∈ S.Φ '' U₁ := fun τ hτ =>
      hball τ ⟨hs₁0.trans hτ.1, hτ.2.trans hσS.1.2⟩
        (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])
    obtain ⟨e', he'U, hce'⟩ := hseg σ ⟨hs₁σ, le_rfl⟩
    have hcurve : (CE X).CausalCurveOn ⊤ c s₁ σ :=
      Causal.CurveOn.restrict hc hs₁0 hσS.1.2 le_rfl fun τ hτ =>
        hc.mem τ ⟨hs₁0.trans hτ.1, hτ.2.trans hσS.1.2⟩
    have hee' := S.le_of_curve hU₁O
      (fun U hU V hV a ha b hb h => hU₀ U (hU.trans inf_le_left) V hV a ha b hb h)
      hs₁σ hcurve hseg heU₁ he'U hce.symm hce'.symm
    have hf := (calculus_le hee').2.2.2.2.1
    have he'Q : e' ∈ Q := ⟨⟨heQ.1.1.trans hf, he'U.2.1.le⟩, he'U.2.2.le⟩
    exact hσS.2 ⟨e', he'Q, hce'⟩
  · rw [hce, ← hc1]
    exact hc.le_of_le hs₁0 hs₁1 le_rfl

omit [HasGroupoid X e0Groupoid] in
/-- **A radius avoiding a regular point**: a regular `x` lies outside the spear of some radius
`ρ ∈ ]0, R]` (the spear can be chosen with `q ∉ 𝒮`, B21 l.1107). -/
theorem exists_radius_avoiding {x : X} (hx : x ∉ S0 X) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ S.R ∧ x ∉ S.Φ '' spear S.v ρ := by
  by_cases h : x ∈ S.Φ '' spear S.v S.R
  · obtain ⟨e₁, he₁, rfl⟩ := h
    have hax : e₁ ∉ axis := fun hax => hx ((S.mem_S0_iff (S.spear_subset_O le_rfl he₁)).2 hax)
    have hr : 0 < rad e₁ := norm_pos_iff.2 hax
    have hR := he₁.2
    refine ⟨rad e₁ / 2, by linarith, by linarith, ?_⟩
    rintro ⟨e, he, hee⟩
    have := S.injOn (S.spear_subset_O (by linarith) he) (S.spear_subset_O le_rfl he₁) hee
    subst this
    linarith [he.2]
  · exact ⟨S.R, S.pos, le_rfl, h⟩

omit [HasGroupoid X e0Groupoid] in
/-- **Regular points of the chart below a regular `q'` above a BTZ point** (`I⁻(q')` is open). -/
theorem exists_regular_le {ρ : ℝ} (hρ0 : 0 < ρ) {t : ℝ} (ht : S.v + ρ ≤ t)
    {q' : X} (hlt : (CE X).lt ⊤ (S.Φ ((t, 0) : E0)) q') :
    ∃ w : ℂ, 0 < ‖w‖ ∧ ‖w‖ ≤ ρ ∧ (CE X).le ⊤ (S.Φ ((t, w) : E0)) q' := by
  have htO : ((t, 0) : E0) ∈ S.O := S.spear_subset_O le_rfl (axis_mem_spear S.pos.le (by linarith))
  have hc : ContinuousAt S.Φ ((t, 0) : E0) := S.continuousOn.continuousAt (S.isOpen_O.mem_nhds htO)
  have hev : ∀ᶠ x in 𝓝 ((t, 0) : E0), S.Φ x ∈ (CE X).Iminus ⊤ {q'} :=
    hc.eventually ((isOpen_Iminus {q'}).mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hlt))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set w : ℂ := ((min (ε / 2) ρ : ℝ) : ℂ) with hw
  have hwn : ‖w‖ = min (ε / 2) ρ := by
    rw [hw, Complex.norm_real, Real.norm_of_nonneg (le_min (by linarith) hρ0.le)]
  refine ⟨w, by rw [hwn]; exact lt_min (by linarith) hρ0, by rw [hwn]; exact min_le_right _ _, ?_⟩
  have hd : dist ((t, w) : E0) (t, 0) < ε := by
    rw [Prod.dist_eq, dist_self, dist_zero_right, hwn, max_eq_right (le_min (by linarith) hρ0.le)]
    linarith [min_le_left (ε / 2) ρ]
  exact (CE X).le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 (hball hd))

end SpearChart

/-! ### §2 No vertical null line of an `𝔼₀`-morphism converges to a regular point -/

/-- The velocity of the vertical null lines of `𝔼₀` under the paper's developing map. -/
noncomputable def vertU : Causal.Minkowski 2 := (1, WithLp.toLp 2 ![1, 0])

theorem vertU_ne_zero : vertU ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  simp [vertU] at this

/-- **The paper's developing map is affine along the vertical lines** (`btzPaperDev`,
`RamcovGX.tex:1947`): `D(σ', r, θ) = D(σ, r, θ) + (σ' − σ) • (1, (1, 0))`, a null velocity. -/
theorem btzPaperDev_vertical (σ σ' r θ : ℝ) :
    btzPaperDev (σ', r, θ) = btzPaperDev (σ, r, θ) + (σ' - σ) • vertU := by
  simp only [btzPaperDev, vertU]
  refine Prod.ext ?_ ?_
  · simp; ring
  · ext i; fin_cases i <;> simp; ring

attribute [local instance] btzE0Structure in
/-- **No vertical null line of an `𝔼₀`-morphism has a regular future endpoint** (the regular
analogue of `E0Spear.axis_noLimit`, the core of DEC-126's repair; no volume, no time separation).
Were `σ ↦ φ(σ, z)` (`z ≠ 0`) convergent to a regular `x₀`, then in a regular chart `c'` at the
chart image of `x₀`, `F(σ) = c'(κ(φ(σ, z)))` is near every `σ` of the form `k • D(σ, |z|, arg z)`,
`k ∈ Isom(𝐌³)` (the a.e.-isomorphism property of `κ ∘ φ`, `E0RegAt`, and
`btz_chart_eq_smul_btzPaperDev`): locally affine with the nonzero velocity `k.linear (1,(1,0))`;
`affine_noLimit` concludes. The Lorentz-invariant size is the affine parameter of the null line. -/
theorem vertical_noLimit {X : Type} [TopologicalSpace X] [ChartedSpace E0Y X]
    [HasGroupoid X e0Groupoid] {W : Set E0Y} {φ : E0Y → X} (hW : IsOpen W)
    (hφ : IsE0Mor φ W) {z : ℂ} (hz : z ≠ 0) {σ₀ : ℝ}
    (hmem : ∀ σ, σ₀ ≤ σ → paperInY ((σ, z) : E0) ∈ W) {x₀ : X} (hx₀ : x₀ ∉ S0 X) :
    ¬ Tendsto (fun σ : ℝ => φ (paperInY ((σ, z) : E0))) atTop (𝓝 x₀) := by
  intro hlim
  set κ := chartAt E0Y x₀ with hκ
  have hκreg : κ x₀ ∈ e0Reg := by
    by_contra h
    exact hx₀ ⟨rfl, h⟩
  obtain ⟨c', hc', hc'x⟩ := mem_support.1 hκreg
  have hN : IsOpen (κ.source ∩ κ ⁻¹' c'.source) := κ.isOpen_inter_preimage c'.open_source
  obtain ⟨σ₁', hev⟩ := eventually_atTop.1
    (hlim.eventually (hN.mem_nhds ⟨mem_chart_source E0Y x₀, hc'x⟩))
  set σ₁ := max σ₀ σ₁' with hσ₁
  set γ : ℝ → E0Y := fun σ => paperInY ((σ, z) : E0) with hγ
  have hγc : Continuous γ := continuous_paperInY.comp (continuous_id.prodMk continuous_const)
  set F : ℝ → Causal.Minkowski 2 := fun σ => c' (κ (φ (γ σ))) with hF
  have hFlim : Tendsto F atTop (𝓝 (c' (κ x₀))) :=
    ((c'.continuousAt hc'x).comp (κ.continuousAt (mem_chart_source E0Y x₀))).tendsto.comp hlim
  refine affine_noLimit (σ₁ := σ₁) (fun σ hσ => ?_) _ hFlim
  have hσ₀ : σ₀ ≤ σ := (le_max_left _ _).trans hσ.le
  have hσ₁' : σ₁' ≤ σ := (le_max_right _ _).trans hσ.le
  have hyW : γ σ ∈ W := hmem σ hσ₀
  -- `κ ∘ φ` is an `𝔼₀`-morphism near `γ σ`
  have hφc : ContinuousOn φ W := fun y hy => (hφ y hy).continuousWithinAt
  set U := W ∩ φ ⁻¹' κ.source with hU
  have hUo : IsOpen U := hφc.isOpen_inter_preimage hW κ.open_source
  have hyU : γ σ ∈ U := ⟨hyW, (hev σ hσ₁').1⟩
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, trivial⟩
  have hφU : IsE0Mor φ U := Causal.CBG.liftPropOn_mono_of_le hW hUo hφ inter_subset_left
  have hgU : IsE0Mor (κ ∘ φ) U :=
    Causal.CBG.liftPropOn_comp hUo κ.open_source
      (e0Groupoid.isLocalStructomorphWithinAt_localInvariantProp.liftPropOn_chart hQ) hφU
      (fun y hy => hy.2)
  have h := (hgU (γ σ) hyU).2
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    preimage_id_eq] at h
  obtain ⟨e, he, hge, hye⟩ := h hyU
  have hyreg : γ σ ∈ e0Reg := paperInY_mem_e0Reg_iff.2 fun h => hz h
  obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 he).1 (γ σ) hye).2 hyreg
  obtain ⟨c, hc, hyc⟩ := mem_support.1 hyreg
  have hgy : (κ ∘ φ) (γ σ) = e (γ σ) := hge ⟨hyU, hye⟩
  have hey : e (γ σ) ∈ c'.source := by rw [← hgy]; exact (hev σ hσ₁').2
  obtain ⟨k₀, hk₀⟩ := hch c hc c' hc' hyc hey
  -- the regular chart at `γ σ` is a chart of `𝔼₀`
  have hyb : γ σ = Sum.inr (E0.toPaper.symm ((σ, z) : E0)) := paperInY_apply _
  rw [hyb] at hyc
  obtain ⟨c₀, hc₀, rfl, hbc₀⟩ := exists_of_mem_e0Atlas_inr hc hyc
  have hev1 : ∀ᶠ σ' in 𝓝 σ, F σ' = k₀ • c₀ (E0.toPaper.symm ((σ', z) : E0)) := by
    have h1 := (hγc.tendsto σ).eventually hk₀
    have h2 : ∀ᶠ σ' in 𝓝 σ, (κ ∘ φ) (γ σ') = e (γ σ') :=
      (hγc.tendsto σ).eventually (Filter.eventually_of_mem
        ((hUo.inter e.open_source).mem_nhds ⟨hyU, hye⟩) fun y hy => hge hy)
    filter_upwards [h1, h2] with σ' h1 h2
    have h3 : F σ' = c' ((κ ∘ φ) (γ σ')) := rfl
    rw [h3, h2, h1]
    simp [γ, paperInY_apply]
  -- the paper's coordinates `(σ, r, θ)` of the line
  set r := ‖z‖ with hr
  set θ := Complex.arg z with hθ
  have hr0 : 0 < r := norm_pos_iff.2 hz
  have hpaper : ∀ σ' : ℝ, E0.toPaper.symm ((σ', z) : E0) =
      orbitMk (GammaA (2 * π)) (btzPaperCyl (σ', r, θ)) := by
    intro σ'
    rw [Homeomorph.symm_apply_eq, btzPaperCyl_of_pos (show 0 < ((σ', r, θ) : ℝ × ℝ × ℝ).2.1 from hr0)]
    rw [E0.toPaper_posEmb hr0 θ σ', hr, hθ, Complex.norm_mul_exp_arg_mul_I]
  have hbc : orbitMk (GammaA (2 * π)) (btzPaperCyl ((σ, r, θ) : ℝ × ℝ × ℝ)) ∈ c₀.source := by
    rw [← hpaper]; exact hbc₀
  obtain ⟨g₁, hg₁⟩ := btz_chart_eq_smul_btzPaperDev isBTZStructure_btzE0 hc₀
    (p := ((σ, r, θ) : ℝ × ℝ × ℝ)) hr0 hbc
  have hlin : Continuous (fun σ' : ℝ => ((σ', r, θ) : ℝ × ℝ × ℝ)) :=
    continuous_id.prodMk continuous_const
  have hev2 : ∀ᶠ σ' in 𝓝 σ, F σ' = (k₀ * g₁) • btzPaperDev (σ', r, θ) := by
    filter_upwards [hev1, (hlin.tendsto σ).eventually hg₁] with σ' h1 h2
    rw [h1, hpaper, h2, mul_smul]
  -- locally affine with the nonzero velocity `(k₀ g₁).linear (1, (1, 0))`
  set k := k₀ * g₁ with hk
  refine ⟨((k : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear) vertU, ?_, ?_⟩
  · intro hw
    exact vertU_ne_zero ((k : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).linear.injective
      (hw.trans (map_zero _).symm))
  · have hFσ : F σ = k • btzPaperDev (σ, r, θ) := hev2.self_of_nhds
    filter_upwards [hev2] with σ' h'
    rw [h', hFσ, btzPaperDev_vertical σ σ' r θ, Causal.Flat.isom_smul_def,
      Causal.Flat.isom_smul_def, add_comm, ← vadd_eq_add, AffineEquiv.map_vadd, vadd_eq_add,
      map_smul, add_comm]

end Chart

/-! ### §3 Two facts of globally hyperbolic causalities -/

section GH

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] {C : Causal.Causality Z}

/-- **`J⁺(K) ∩ J⁻(x)` is compact** for `K` compact in a tarentin globally hyperbolic Hausdorff
spacetime (the time dual of `E0Spear.isCompact_Jplus_singleton_inter_Jminus_of_isCompact`). -/
theorem isCompact_Jplus_inter_Jminus_singleton (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    {K : Set Z} (hK : IsCompact K) (x : Z) : IsCompact (C.Jplus ⊤ K ∩ C.Jminus ⊤ {x}) := by
  have hcl : IsClosed (C.Jplus ⊤ K ∩ C.Jminus ⊤ {x}) :=
    (Causal.Causality.isClosed_Jplus_of_isCompact (hG.isClosed_le hT) hK).inter
      (hG.isClosed_Jminus_singleton hT x)
  have hex : ∀ k : Z, ∃ ab : Z × Z, k ∈ C.openDiamond ⊤ ab.1 ab.2 := fun k => by
    obtain ⟨a, b, hk, -⟩ := hG.exists_diamond_subset hT k univ_mem
    exact ⟨(a, b), hk⟩
  choose ab hab using hex
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => C.openDiamond ⊤ (ab k).1 (ab k).2)
    fun k _ => isOpen_interior.mem_nhds (hab k)
  refine (t.isCompact_biUnion fun k _ => hG.2 (ab k).1 x).of_isClosed_subset hcl ?_
  rintro z ⟨⟨k₀, hk₀, hk₀z⟩, hzx⟩
  obtain ⟨k, hkt, hk₀k⟩ := mem_iUnion₂.1 (ht hk₀)
  have hak₀ : C.le ⊤ (ab k).1 k₀ := (Causal.Causality.mem_diamond.1 (interior_subset hk₀k)).1
  exact mem_iUnion₂.2 ⟨k, hkt, Causal.Causality.mem_diamond.2
    ⟨C.le_trans hak₀ hk₀z, Causal.Precausality.mem_Jminus_singleton.1 hzx⟩⟩

/-- **A future-monotone curve eventually in a compact set converges** (the abstract form of
`E0Spear.exists_tendsto_of_monotone`): cluster points are above the curve and below each other. -/
theorem exists_tendsto_of_monotone_gh (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    {γ : ℝ → Z} {t₀ : ℝ} (hmono : ∀ s t, t₀ ≤ s → s ≤ t → C.le ⊤ (γ s) (γ t))
    {K : Set Z} (hK : IsCompact K) (hKγ : ∀ t, t₀ ≤ t → γ t ∈ K) :
    ∃ q, Tendsto γ atTop (𝓝 q) := by
  have hev : ∀ᶠ t in atTop, γ t ∈ K := eventually_atTop.2 ⟨t₀, hKγ⟩
  obtain ⟨q, -, hq⟩ := hK.exists_mapClusterPt (f := atTop) (u := γ) (le_principal_iff.2 hev)
  have habove : ∀ q', MapClusterPt q' atTop γ → ∀ s, t₀ ≤ s → C.le ⊤ (γ s) q' := by
    intro q' hq' s hs
    have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jplus_singleton hT (γ s)) hq'
      (eventually_atTop.2 ⟨s, fun t ht => by simpa using hmono s t hs ht⟩)
    simpa using this
  have huniq : ∀ q', MapClusterPt q' atTop γ → q' = q := by
    intro q' hq'
    have h1 : C.le ⊤ q' q := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jminus_singleton hT q) hq'
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q hq t ht⟩)
      simpa using this
    have h2 : C.le ⊤ q q' := by
      have := E0Spear.mem_of_mapClusterPt_of_eventually (hG.isClosed_Jminus_singleton hT q') hq
        (eventually_atTop.2 ⟨t₀, fun t ht => by simpa using habove q' hq' t ht⟩)
      simpa using this
    exact hG.1 h1 h2
  exact ⟨q, hK.tendsto_nhds_of_unique_mapClusterPt hev fun x _ hx => huniq x hx⟩

end GH

/-! ### §4 The push-out of B21 Prop 2.17: its mixed diamonds -/

section Pushout

open E0CBG E0Spear E0 E0AbsMax

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
  {N : Causal.Flat.FlatSpacetime.{0} 2} {f : e0RegMFlat M → N}

omit [SecondCountableTopology M] in
/-- **The relations of `M̄` between points of `N` are those of `N`** (`N ↪ M̄` is a BTZ-extension
of a globally hyperbolic `N`, so `ι₂(N)` is causally convex, B21 Lemma 2.13(b)). -/
theorem le_top_ι₂_iff (hN : Causal.Flat.GH N) (P : E0Pushout M N f) (y y' : N) :
    (CE P.carrier).le ⊤ (P.ι₂ y) (P.ι₂ y') ↔ (Causal.Flat.flatCausality 2 N).le ⊤ y y' := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨-, -, hBc⟩ := P.pieces
  let B : Opens P.carrier := ⟨range P.ι₂, P.isOpenEmbedding_ι₂.isOpen_range⟩
  have hGB : (CE P.carrier).GloballyHyperbolicOn B :=
    globallyHyperbolicOn_of_le_iff hN P.isOpenEmbedding_ι₂.continuous rfl (P.le_ι₂ B rfl)
  have hconv := btzExt_causallyConvexIn_of_globallyHyperbolicOn hP hBc hGB
  rw [← P.le_ι₂ B rfl]
  exact (Causal.Causality.le_iff_of_causallyConvexIn hP.causallyArcConnected hconv
    (show P.ι₂ y' ∈ B from ⟨y', rfl⟩) (show P.ι₂ y ∈ B from ⟨y, rfl⟩)).symm

/-- **A spear chart of `M̄` at every BTZ point** (B21 Lemma 2.3 in `M`, `E0Spear.lem_tube_e0`,
pushed by `ι₁`). -/
theorem exists_spearChart (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    (P : E0Pushout M N f) {p : P.carrier} (hp : p ∈ S0 P.carrier) :
    Nonempty (SpearChart P.carrier p) := by
  obtain ⟨hA, hsA, -⟩ := P.pieces
  obtain ⟨p₀, rfl⟩ := hsA hp
  have hp₀ : p₀ ∈ S0 M := (P.sing_ι₁ p₀).1 hp
  obtain ⟨R, U, hU⟩ := lem_tube_e0 hGH hmax hp₀
  obtain ⟨v, W, ψ, hW, hsub, hψ, hinj, hv, -⟩ := hU.chart
  refine ⟨⟨v, R, hU.pos, W, P.ι₁ ∘ ψ, hW, hsub, ?_, ?_, by simp [hv]⟩⟩
  · exact Causal.CBG.liftPropOn_comp hW isOpen_univ P.isE0Mor_ι₁ hψ (mapsTo_univ _ _)
  · exact P.injective_ι₁.comp_injOn hinj

variable (P : E0Pushout M N f) {p : P.carrier} (S : SpearChart P.carrier p)

/-- The points of `N` read by the regular points of the chart. -/
noncomputable def toN (x : E0) : N := Function.invFun P.ι₂ (S.Φ x)

omit [SecondCountableTopology M] in
theorem ι₂_toN {x : E0} (hx : x ∈ S.O) (hax : x ∉ axis) : P.ι₂ (toN P S x) = S.Φ x := by
  have hreg : S.Φ x ∉ S0 P.carrier := fun h => hax ((S.mem_S0_iff hx).1 h)
  obtain ⟨-, -, hBc⟩ := P.pieces
  have hmem : S.Φ x ∈ range P.ι₂ := by_contra fun h => hreg (hBc h)
  exact Function.invFun_eq hmem

omit [SecondCountableTopology M] in
theorem continuousOn_toN : ContinuousOn (toN P S) (S.O ∩ axisᶜ) := by
  rw [P.isOpenEmbedding_ι₂.isInducing.continuousOn_iff]
  exact (S.continuousOn.mono inter_subset_left).congr fun x hx => ι₂_toN P S hx.1 hx.2


theorem isOpen_axis_compl : IsOpen (axisᶜ : Set E0) :=
  (isClosed_eq continuous_snd continuous_const).isOpen_compl

omit [SecondCountableTopology M] in
/-- **The circle trick** (B21 l.1104–1117 repaired, step 2): points of the spear below a regular
`q'` at arbitrarily large height and with radius bounded below are impossible. Compactness of the
annulus gives a limit radius-angle `z`; closedness of `J⁻_N(q')` puts the WHOLE vertical null line
of `z` below `q'`; it then lies in a compact diamond of `N`, so it converges, against
`vertical_noLimit`. -/
theorem circle_trick (hN : Causal.Flat.GH N) {ρ : ℝ} (hρ : ρ ≤ S.R) {q' : P.carrier}
    (hq' : q' ∉ S0 P.carrier) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hseq : ∀ H : ℝ, ∃ e ∈ spear S.v ρ, r₀ ≤ rad e ∧ H ≤ e.1 ∧ (CE P.carrier).le ⊤ (S.Φ e) q') :
    False := by
  obtain ⟨-, -, hBc⟩ := P.pieces
  obtain ⟨y', rfl⟩ : q' ∈ range P.ι₂ := by_contra fun h => hq' (hBc h)
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hT := Causal.Flat.flatCausality_tarentin (d := 2) (X := N)
  choose e he using fun n : ℕ => hseq n
  set A : Set ℂ := {w | r₀ ≤ ‖w‖ ∧ ‖w‖ ≤ ρ} with hA
  have hAc : IsCompact A :=
    (isCompact_closedBall (0 : ℂ) ρ).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun w hw => mem_closedBall_zero_iff.2 hw.2
  obtain ⟨z, hzA, ψ, hψ, hlim⟩ := hAc.tendsto_subseq (x := fun n => (e n).2)
    fun n => ⟨(he n).2.1, (he n).1.2⟩
  have hz0 : z ≠ 0 := fun h => by
    have := hzA.1; rw [h, norm_zero] at this; linarith
  have hzρ : ‖z‖ ≤ ρ := hzA.2
  set σ₀ := S.v + ρ / 2 with hσ₀
  have hmemsp : ∀ σ, σ₀ ≤ σ → ∀ w : ℂ, ‖w‖ ≤ ρ → ((σ, w) : E0) ∈ spear S.v ρ :=
    fun σ hσ w hw => ⟨by simp only [fcoord, rad]; linarith, hw⟩
  have hspR : spear S.v ρ ⊆ spear S.v S.R := spear_mono le_rfl hρ
  have hOz : ∀ σ, σ₀ ≤ σ → ((σ, z) : E0) ∈ S.O ∩ axisᶜ := fun σ hσ =>
    ⟨S.spear_subset_O hρ (hmemsp σ hσ z hzρ), fun h => hz0 h⟩
  -- the vertical line at `z` is below `q'`
  have hbelow : ∀ σ, σ₀ ≤ σ → (Causal.Flat.flatCausality 2 N).le ⊤ (toN P S (σ, z)) y' := by
    intro σ hσ
    have hcl := hN'.isClosed_Jminus_singleton hT y'
    have hcont : Tendsto (fun n => toN P S (σ, (e (ψ n)).2)) atTop (𝓝 (toN P S (σ, z))) := by
      have h1 : Tendsto (fun n => ((σ, (e (ψ n)).2) : E0)) atTop (𝓝 ((σ, z) : E0)) :=
        tendsto_const_nhds.prodMk_nhds hlim
      exact ((continuousOn_toN P S).continuousAt
        ((S.isOpen_O.inter isOpen_axis_compl).mem_nhds (hOz σ hσ))).tendsto.comp h1
    have hev : ∀ᶠ n in atTop,
        toN P S (σ, (e (ψ n)).2) ∈ (Causal.Flat.flatCausality 2 N).Jminus ⊤ {y'} := by
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge σ
      refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
      have hψn : (n₀ : ℝ) ≤ ψ n := by exact_mod_cast hn.trans (hψ.id_le n)
      have hen := he (ψ n)
      have hσen : σ ≤ (e (ψ n)).1 := hn₀.trans (hψn.trans hen.2.2.1)
      have hmem1 : ((σ, (e (ψ n)).2) : E0) ∈ spear S.v ρ := hmemsp σ hσ _ hen.1.2
      have hax1 : ((σ, (e (ψ n)).2) : E0) ∉ axis := fun h => by
        have h2 := hen.2.1
        have h3 : (e (ψ n)).2 = 0 := h
        simp only [rad, h3, norm_zero] at h2
        linarith
      have hle1 : causality.le ⊤ ((σ, (e (ψ n)).2) : E0) (e (ψ n)) := le_vertical_top hσen
      have hX := (CE P.carrier).le_trans (S.le_of_le (hspR hmem1) (hspR hen.1) hle1) hen.2.2.2
      rw [← ι₂_toN P S (S.spear_subset_O hρ hmem1) hax1] at hX
      exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 hX)
    exact Causal.Precausality.mem_Jminus_singleton.1 (hcl.mem_of_tendsto hcont hev)
  -- the line converges in `N`
  set ℓ : ℝ → N := fun σ => toN P S (σ, z) with hℓ
  have hmono : ∀ s t, σ₀ ≤ s → s ≤ t → (Causal.Flat.flatCausality 2 N).le ⊤ (ℓ s) (ℓ t) := by
    intro s t hs hst
    have ht : σ₀ ≤ t := hs.trans hst
    have h1 := S.le_of_le (hspR (hmemsp s hs z hzρ)) (hspR (hmemsp t ht z hzρ))
      (le_vertical_top hst)
    rw [← ι₂_toN P S (hOz s hs).1 (hOz s hs).2, ← ι₂_toN P S (hOz t ht).1 (hOz t ht).2] at h1
    exact (le_top_ι₂_iff hN P _ _).1 h1
  obtain ⟨y₁, hy₁⟩ := exists_tendsto_of_monotone_gh hT hN' hmono (hN'.2 (ℓ σ₀) y') fun t ht =>
    Causal.Causality.mem_diamond.2 ⟨hmono σ₀ t le_rfl ht, hbelow t ht⟩
  -- so does the vertical line of `M̄`, against `vertical_noLimit`
  have hlimX : Tendsto (fun σ : ℝ => S.φ (paperInY ((σ, z) : E0))) atTop (𝓝 (P.ι₂ y₁)) := by
    refine ((P.isOpenEmbedding_ι₂.continuous.tendsto y₁).comp hy₁).congr' ?_
    exact eventually_atTop.2 ⟨σ₀, fun σ hσ => ι₂_toN P S (hOz σ hσ).1 (hOz σ hσ).2⟩
  exact vertical_noLimit S.isOpen S.mor hz0 (fun σ hσ => (hOz σ hσ).1) (P.sing_ι₂ y₁) hlimX

omit [SecondCountableTopology M] in
/-- **The BTZ ray of the vertex is bounded below a regular `q`** (B21 l.1104–1117 repaired, step 2;
the fact the printed proof uses without proof when it takes `K' = K ∩ ∂𝒮` compact). Otherwise every
BTZ point of the chart is below `q ≪ q'`; regular points of the spear below `q'` start at every
height (`exists_regular_le`), and their exits from truncated spears (`SpearChart.exit`) feed the
circle trick: either wall points of radius `ρ` at every height, or, from one start of radius
`r₀ > 0`, lid points at every height of radius `≥ r₀`. -/
theorem exists_bound_axis (hN : Causal.Flat.GH N) (q : P.carrier) :
    ∃ H : ℝ, ∀ t : ℝ, H ≤ t → ¬ (CE P.carrier).le ⊤ (S.Φ ((t, 0) : E0)) q := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  by_contra hcon
  push Not at hcon
  obtain ⟨q', hqq', hq'reg⟩ := exists_lt_notMem_sing hP q
  obtain ⟨ρ, hρ0, hρ, hq'ρ⟩ := S.exists_radius_avoiding hq'reg
  have hstart : ∀ n : ℕ, ∃ a : E0, a ∈ spear S.v ρ ∧ a ∉ axis ∧ (n : ℝ) ≤ fcoord a ∧
      (CE P.carrier).le ⊤ (S.Φ a) q' := by
    intro n
    obtain ⟨t, ht, htq⟩ := hcon (max (n : ℝ) S.v + ρ)
    have hlt := hP.pushUp.lt_of_le_of_lt htq hqq'
    obtain ⟨w, hw0, hwρ, hwle⟩ :=
      S.exists_regular_le hρ0 (by linarith [le_max_right (n : ℝ) S.v]) hlt
    refine ⟨(t, w), ⟨?_, hwρ⟩, fun h => ?_, ?_, hwle⟩
    · simp only [fcoord, rad]; linarith [le_max_right (n : ℝ) S.v]
    · have h3 : w = 0 := h
      rw [h3, norm_zero] at hw0
      exact lt_irrefl _ hw0
    · simp only [fcoord, rad]; linarith [le_max_left (n : ℝ) S.v]
  by_cases hall : ∀ n : ℕ, ∃ e ∈ spear S.v ρ, rad e = ρ ∧ (n : ℝ) ≤ e.1 ∧
      (CE P.carrier).le ⊤ (S.Φ e) q'
  · refine circle_trick P S hN hρ hq'reg hρ0 fun H => ?_
    obtain ⟨e, he, her, hen, hle⟩ := hall ⌈H⌉₊
    exact ⟨e, he, her.ge, (Nat.le_ceil H).trans hen, hle⟩
  · push Not at hall
    obtain ⟨n, hn⟩ := hall
    obtain ⟨a, ha, hax, han, haq⟩ := hstart n
    have hra : 0 < rad a := norm_pos_iff.2 hax
    refine circle_trick P S hN hρ hq'reg hra fun H => ?_
    obtain ⟨e, heQ, hwl, hae, heq⟩ := S.exit hρ (a := a) (T := max H a.1)
      ⟨ha, show a.1 ≤ max H a.1 from le_max_right _ _⟩ (fun ⟨x, hx, hxe⟩ => hq'ρ ⟨x, hx.1, hxe⟩) haq
    have hcal := calculus_le hae
    rcases hwl with hr | hT
    · exfalso
      have hfe : fcoord e ≤ e.1 := by simp only [fcoord, rad]; linarith [norm_nonneg e.2]
      exact hn e heQ.1 hr (by linarith [hcal.2.2.2.2.1]) heq
    · exact ⟨e, heQ.1, hcal.2.2.2.1, by rw [hT]; exact le_max_left _ _, heq⟩

/-- **The mixed diamonds of the push-out are compact** (B21 Prop 2.17's last case,
`BTZ_1.tex:1104–1117`, DEC-126): `p ∈ sing₀(M̄)`, `q` regular. With the spear chart of vertex `p`
(`exists_spearChart`), a radius `ρ` with `q ∉ 𝒮` (`exists_radius_avoiding`), a lid `T` above the
bound of the BTZ points below `q` (`exists_bound_axis`) and `E` the compact set of wall points
below `q`: `J(p, q) = Φ(𝒬 ∩ J⁻(E)) ∪ ι₂(J⁺_N(E) ∩ J⁻_N(q))`, both compact. A point of `J(p, q)`
in `Φ(𝒬)` exits `𝒬` towards `q` through the wall (`SpearChart.exit`; the lid is not below `q`);
one outside `Φ(𝒬)` is reached from `p` through the wall, hence lies in `N`. -/
theorem isCompact_diamond_mixed (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M)
    (hN : Causal.Flat.GH N) (P : E0Pushout M N f) {p q : P.carrier} (hp : p ∈ S0 P.carrier)
    (hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨S⟩ := exists_spearChart hGH hmax P hp
  obtain ⟨-, -, hBc⟩ := P.pieces
  obtain ⟨yq, rfl⟩ : q ∈ range P.ι₂ := by_contra fun h => hq (hBc h)
  have hN' : (Causal.Flat.flatCausality 2 N).GloballyHyperbolic := hN
  have hT := Causal.Flat.flatCausality_tarentin (d := 2) (X := N)
  obtain ⟨ρ, hρ0, hρ, hqρ⟩ := S.exists_radius_avoiding hq
  obtain ⟨H, hH⟩ := exists_bound_axis P S hN (P.ι₂ yq)
  set T := max H S.v + ρ + 1 with hTdef
  set Q := spear S.v ρ ∩ {x : E0 | x.1 ≤ T} with hQ
  have hQc : IsCompact Q := isCompact_spear_inter_le _ _ _
  have hspR : spear S.v ρ ⊆ spear S.v S.R := spear_mono le_rfl hρ
  have hQO : Q ⊆ S.O := fun x hx => S.spear_subset_O hρ hx.1
  have hqQ : P.ι₂ yq ∉ S.Φ '' Q := fun ⟨x, hx, hxe⟩ => hqρ ⟨x, hx.1, hxe⟩
  -- no point of the lid is below `q`
  have hnolid : ∀ e ∈ spear S.v ρ, e.1 = T → ¬ (CE P.carrier).le ⊤ (S.Φ e) (P.ι₂ yq) := by
    intro e he heT hle
    have hax : ((fcoord e, 0) : E0) ∈ spear S.v S.R := axis_mem_spear S.pos.le he.1
    have h1 : causality.le ⊤ ((fcoord e, 0) : E0) e := by
      rw [le_top_iff, le_axis_iff rfl]
    refine hH (fcoord e) ?_ ((CE P.carrier).le_trans (S.le_of_le hax (hspR he) h1) hle)
    have := he.2
    simp only [fcoord, rad] at this ⊢
    rw [heT]; linarith [le_max_left H S.v]
  -- the wall `W_T` and its points `E` below `q`
  set WT : Set E0 := {x | rad x = ρ ∧ S.v + ρ / 2 ≤ x.1 ∧ x.1 ≤ T} with hWT
  have hWTc : IsCompact WT := by
    refine ((isCompact_Icc (a := S.v + ρ / 2) (b := T)).prod
      (isCompact_closedBall (0 : ℂ) ρ)).of_isClosed_subset ?_ ?_
    · exact (isClosed_eq continuous_rad continuous_const).inter
        ((isClosed_le continuous_const continuous_fst).inter
          (isClosed_le continuous_fst continuous_const))
    · rintro x ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h3⟩, mem_closedBall_zero_iff.2 h1.le⟩
  have hWTsp : WT ⊆ spear S.v ρ := fun x hx => ⟨by simp only [fcoord]; rw [hx.1]; linarith [hx.2.1],
    hx.1.le⟩
  have hWTreg : WT ⊆ S.O ∩ axisᶜ := fun x hx => ⟨S.spear_subset_O hρ (hWTsp hx), fun h => by
    have h1 := hx.1
    have h2 : x.2 = 0 := h
    simp only [rad, h2, norm_zero] at h1
    linarith⟩
  set E := WT ∩ toN P S ⁻¹' (Causal.Flat.flatCausality 2 N).Jminus ⊤ {yq} with hE
  have hEc : IsCompact E :=
    hWTc.of_isClosed_subset (((continuousOn_toN P S).mono hWTreg).preimage_isClosed_of_isClosed
      hWTc.isClosed (hN'.isClosed_Jminus_singleton hT yq)) inter_subset_left
  have hmemE : ∀ e ∈ WT, (CE P.carrier).le ⊤ (S.Φ e) (P.ι₂ yq) → e ∈ E := by
    intro e heWT heq
    refine ⟨heWT, ?_⟩
    rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2] at heq
    exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 heq)
  have hwall : ∀ e ∈ Q, rad e = ρ → e ∈ WT := fun e heQ hr =>
    ⟨hr, by have := heQ.1.1; simp only [fcoord] at this; rw [hr] at this; linarith, heQ.2⟩
  -- a point of `𝒬` below `q` is below a point of `E`
  have hkey : ∀ x ∈ Q, (CE P.carrier).le ⊤ (S.Φ x) (P.ι₂ yq) →
      ∃ e ∈ E, causality.le ⊤ x e := by
    intro x hx hxq
    obtain ⟨e, heQ, hwl, hxe, heq⟩ := S.exit hρ hx hqQ hxq
    rcases hwl with hr | hT'
    · exact ⟨e, hmemE e (hwall e heQ hr) heq, hxe⟩
    · exact absurd heq (hnolid e heQ.1 hT')
  set G := Q ∩ causality.Jminus ⊤ E with hG
  have hle_cl : IsClosed {z : E0 × E0 | causality.le ⊤ z.1 z.2} :=
    Causal.Causality.isClosed_le E0.tarentin E0.isClosed_Jplus E0.isClosed_Jminus
  have hGc : IsCompact G :=
    hQc.inter_right (Causal.Causality.isClosed_Jminus_of_isCompact hle_cl hEc)
  set KN := toN P S '' E with hKN
  have hKNc : IsCompact KN :=
    hEc.image_of_continuousOn ((continuousOn_toN P S).mono (inter_subset_left.trans hWTreg))
  have hvQ : ((S.v, 0) : E0) ∈ Q :=
    ⟨axis_mem_spear hρ0.le le_rfl, by show S.v ≤ T; linarith [le_max_right H S.v]⟩
  have hvle : ∀ x ∈ spear S.v ρ, (CE P.carrier).le ⊤ p (S.Φ x) := fun x hx => by
    have h1 : causality.le ⊤ ((S.v, 0) : E0) x := by
      rw [le_top_iff, le_axis_iff rfl]; exact hx.1
    have := S.le_of_le (axis_mem_spear S.pos.le le_rfl) (hspR hx) h1
    rwa [S.Φ_vertex] at this
  -- the decomposition
  have hEq : (CE P.carrier).diamond ⊤ p (P.ι₂ yq) = S.Φ '' G ∪
      P.ι₂ '' ((Causal.Flat.flatCausality 2 N).Jplus ⊤ KN ∩
        (Causal.Flat.flatCausality 2 N).Jminus ⊤ {yq}) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hpz, hzq⟩ := Causal.Causality.mem_diamond.1 hz
      by_cases hzQ : z ∈ S.Φ '' Q
      · obtain ⟨x, hx, rfl⟩ := hzQ
        obtain ⟨e, heE, hxe⟩ := hkey x hx hzq
        exact Or.inl ⟨x, ⟨hx, e, heE, hxe⟩, rfl⟩
      · have hpz' : (CE P.carrier).le ⊤ (S.Φ ((S.v, 0) : E0)) z := by
          rw [S.Φ_vertex]; exact hpz
        obtain ⟨e, heQ, hwl, -, hez⟩ := S.exit hρ hvQ hzQ hpz'
        have heq := (CE P.carrier).le_trans hez hzq
        rcases hwl with hr | hT'
        · have heWT := hwall e heQ hr
          have heE := hmemE e heWT heq
          have hzreg : z ∉ S0 P.carrier := fun hzs =>
            (hWTreg heWT).2 ((S.mem_S0_iff (hWTreg heWT).1).1 (hP.mem_sing_zero_of_le hzs hez))
          obtain ⟨y, rfl⟩ : z ∈ range P.ι₂ := by_contra fun h => hzreg (hBc h)
          refine Or.inr ⟨y, ⟨⟨toN P S e, ⟨e, heE, rfl⟩, ?_⟩, ?_⟩, rfl⟩
          · rw [← le_top_ι₂_iff hN P, ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2]
            exact hez
          · exact Causal.Precausality.mem_Jminus_singleton.2 ((le_top_ι₂_iff hN P _ _).1 hzq)
        · exact absurd heq (hnolid e heQ.1 hT')
    · rintro (⟨x, ⟨hxQ, e, heE, hxe⟩, rfl⟩ | ⟨y, ⟨⟨_, ⟨e, heE, rfl⟩, hey⟩, hyq⟩, rfl⟩)
      · have heWT := heE.1
        refine Causal.Causality.mem_diamond.2 ⟨hvle x hxQ.1, ?_⟩
        refine (CE P.carrier).le_trans (S.le_of_le (hspR hxQ.1) (hspR (hWTsp heWT)) hxe) ?_
        rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2, le_top_ι₂_iff hN P]
        exact Causal.Precausality.mem_Jminus_singleton.1 heE.2
      · have heWT := heE.1
        refine Causal.Causality.mem_diamond.2 ⟨?_, ?_⟩
        · have h1 := hvle e (hWTsp heWT)
          rw [← ι₂_toN P S (hWTreg heWT).1 (hWTreg heWT).2] at h1
          exact (CE P.carrier).le_trans h1 ((le_top_ι₂_iff hN P _ _).2 hey)
        · exact (le_top_ι₂_iff hN P _ _).2 (Causal.Precausality.mem_Jminus_singleton.1 hyq)
  rw [hEq]
  exact (hGc.image_of_continuousOn (S.continuousOn.mono (inter_subset_left.trans hQO))).union
    ((isCompact_Jplus_inter_Jminus_singleton hT hN' hKNc yq).image
      P.isOpenEmbedding_ι₂.continuous)

/-! ### §5 B21 Prop 2.17 and Cor 2.18 with the leaf discharged

`GX.BTZ.AbsMax`'s `E0Pushout.globallyHyperbolic`, `absMax_e0RegM`, `prop_abs_max_C1`,
`cor_abs_max_C1`, verbatim except that the mixed diamonds are `isCompact_diamond_mixed` above
instead of the tagged leaf `E0Pushout.isCompact_diamond_mixed`: standard axioms only. -/

/-- **The push-out is globally hyperbolic** (B21 Prop 2.17, `BTZ_1.tex:1098–1117`), the mixed
diamonds by `isCompact_diamond_mixed`. -/
theorem globallyHyperbolic_pushout (hGH : (CE M).GloballyHyperbolic)
    (hmax : IsE0CauchyMaximal M) (hN : Causal.Flat.GH N) (P : E0Pushout M N f) :
    (CE P.carrier).GloballyHyperbolic := by
  have hP := e0_sfa_of_globalBTZ P.carrier
  obtain ⟨hA, hsA, hBc⟩ := P.pieces
  let A : Opens P.carrier := ⟨range P.ι₁, hA⟩
  let B : Opens P.carrier := ⟨range P.ι₂, P.isOpenEmbedding_ι₂.isOpen_range⟩
  have hGA : (CE P.carrier).GloballyHyperbolicOn A :=
    globallyHyperbolicOn_of_le_iff hGH (continuous_of_isE0Mor P.isE0Mor_ι₁) rfl
      (le_iff_of_isE0Mor P.isE0Mor_ι₁ P.injective_ι₁ rfl)
  have hGB : (CE P.carrier).GloballyHyperbolicOn B :=
    globallyHyperbolicOn_of_le_iff hN P.isOpenEmbedding_ι₂.continuous rfl (P.le_ι₂ B rfl)
  exact globallyHyperbolic_of_twoOpens hP (A := A) (B := B) hsA hBc hGA hGB
    fun p hp q hq => isCompact_diamond_mixed hGH hmax hN P hp hq

/-- **B21 Prop 2.17, maximality of `Reg M`** (`BTZ_1.tex:1095–1117`, `A = {0}`): absolutely maximal
in Barbot's sense, with no `sorry` beneath. -/
theorem absMax_e0RegM_spear (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : (CE M).IsCauchySurface S) (hSc : IsCompact S) (hSac : (CE M).IsAcausal S)
    (hmax : IsE0CauchyMaximal M) : Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  have hE := isE0Maximal_of_isE0CauchyMaximal_e0 hGH hS hSc hSac hmax
  intro N hN _ f hf y
  obtain ⟨P⟩ := exists_e0Pushout hN hf
  have hbij := hE P.carrier P.ι₁ (globallyHyperbolic_pushout hGH hmax hN P) P.isE0Mor_ι₁
    P.injective_ι₁
  obtain ⟨x, hx⟩ := hbij.2 (P.ι₂ y)
  obtain ⟨w, -, hw⟩ := P.glue x y hx
  exact ⟨w, hw⟩

/-- **B21 Prop 2.17 under DEC-107** (`prop:abs_max`, `BTZ_1.tex:1078–1082`), the form of record of
`GX.BTZ.AbsMax` (`prop_abs_max_C1`) with no `sorry` beneath: for `M` a globally hyperbolic
Cauchy-maximal `𝔼₀`-manifold with a compact `C¹` spacelike Cauchy surface, `Reg M` is globally
hyperbolic, Cauchy-complete and absolutely maximal in Barbot's sense. -/
theorem prop_abs_max_C1_spear (hGH : (CE M).GloballyHyperbolic) {S : Set M}
    (hS : E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  ⟨gh_e0RegMFlat_e0 hGH, E0Surgery.regM_isCauchyComplete_of_C1 hGH hS hmax,
    absMax_e0RegM_spear hGH hS.cauchy hS.compact (isAcausal_of_isCauchySurface_e0 hGH hS.cauchy)
      hmax⟩

/-- **B21 Cor 2.18 under DEC-107** (`cor:abs_max`, `BTZ_1.tex:1083–1086`; DEC-28's input to the
headline), the form of record of `GX.BTZ.AbsMax` (`cor_abs_max_C1`) with no `sorry`
beneath. -/
theorem cor_abs_max_C1_spear (hGH : (CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) := by
  obtain ⟨S, hS⟩ := hCC
  exact prop_abs_max_C1_spear hGH hS hmax

end Pushout

end E0MixedDiamond

end GX
