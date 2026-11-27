import GXScaffold.BBS.HSClassification

/-!
# BBS `bbsdef:Hcausal`: causal singular HS-surfaces and causal singular lines; a Misner `𝔢(L)` has a closed causal curve, a time-like one has none

Target `T-bbs-hcausal` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx).
`papers/bbs/legacy/labeled/colI_v1.tex`. 3 `sorry` in 2 declarations (tagged, below). Imports
`GXScaffold.BBS.HSClassification` (the types of `(Γ_p, ℓ(p))`-circles: Misner, the degree), over
the strict `GX.BBS.HSSuspension` (`𝔢(L)`, singular HS-structures) and the scaffold
`GXScaffold.BBS.{HSSingularities, HSDegree, HSAntipodal, HSPositive}` (sorry-free).

* `bbsdef:Hcausal` — `colI_v1.tex:1114` — partial (unmarked: the « in other words » is imprecise in
  scope — read for arbitrary, non-compact singular HS-surfaces it fails — and the « if » of its form for singular lines rests
  on three tagged `sorry`s; readings (a)–(d) of SCOPE): the definitions
  `GX.SingularHSStructure.IsCausal` (first sentence) and `GX.GammaLinkCircle.IsCausalLine` (second
  sentence), through `GX.DSLe`, `GX.SingularHSStructure.IsFutureCausalCurve`, `…HasCCC`,
  `…HasHighDegreeAt`, `GX.LinkType.IsHighDegree`; the « in other words » for singular lines
  `GX.GammaLinkCircle.isCausalLine_iff` (and `…isCausalLine_iff_exists`); its counterexample for
  singular HS-surfaces `GX.exists_isSingularHSSurface_sing_empty_hasCCC`.

> A singular HS-surface is causal if it admits no singularity of degree $\geq 4$ and no CCC.
> A singular line is causal if the suspension $\mathfrak{e}(L)$ of the associated
> $(\Gamma_p, \ell(p))$-circle $L$ is causal. (l.1115–1117)
>
> In other words, a singular HS-surface is causal if the following singularity types are
> excluded: space-like or light-like singularities of degree $\geq 4$, Misner singularities.
> (l.1120–1125)
>
> Points in Misner singularities have no future, and no past. Besides, any neighborhood of such a
> point contains closed time-like curves (CTC in short). Indeed, in that case, $\mathfrak{e}(L)$ is
> obtained by glueing the two space-like sides of a bigon entirely contained in the de Sitter region
> $\dS^2$ by some isometry $g$, and for every point $x$ in the past side of this bigon, the image
> $gx$ lies in the future of $x$: any time-like curve joining $x$ to $gx$ induces a CTC in
> $\mathfrak{e}(L)$. (l.1059–1063)

## Main declarations

* **The causal relation of `dS²`** `GX.DSLe σ τ`: both in `dS²`, and `τ̂ − σ̂` future causal in
  `ℝ^{1,2}`, `σ̂ = GX.dsHat σ` the point of the hyperboloid `{Q = 1}` on the ray `σ`;
  `SO₀(1,2)`-invariant (`GX.dsLe_smul_iff`, `GX.dsHat_smul`).
* **Causal curves** `GX.SingularHSStructure.IsFutureCausalCurve`: continuous, and near every
  parameter in a chart of `Σ ∖ 𝒮` along which it reads as a future causal curve of `dS²`; in every
  chart then (`…IsFutureCausalCurve.forall_chart`); it avoids `𝒮` (`…notMem_sing`). A CCC
  (`…IsClosedCausalCurve`, `…HasCCC`): `1`-periodic, not constant.
* **The definition**: `GX.LinkType.IsHighDegree`, `GX.SingularHSStructure.HasHighDegreeAt`,
  `GX.SingularHSStructure.IsCausal`, `GX.GammaLinkCircle.IsCausalLine`.
* **Misner (l.1059–1063), proved**: `GX.GammaLinkCircle.DevData.hasCCC_of_misner`, for every
  developing data. The curve is the « equator » of the bigon, `s ↦ [E(±s), t(±s)]` developed onto
  `[u(s)]`, `u(s)` the projection on `p^⊥` of the lift `w(s)` (`…cccCurve`, `…eventually_chart_bPt`):
  a Misner circle develops into space-like directions (`…minkQ_uVec_pos_of_misner`), so `û(s)` runs
  on one branch of the unit hyperbola of the Lorentzian plane `p^⊥` (`GX.perp_decomp`,
  `…bC_mul_pos`), along which the causal order is the order of the `e₀`-coordinate
  (`GX.hyperbola_sq_le`, `…dsLe_yPt`); that coordinate is locally injective (the developing map is,
  `…d_locally_injOn`), hence monotone in one direction everywhere (`GX.exists_sign_strictMonoOn`).
* **No CCC, proved, for the time-like, light-like and BTZ-like types**
  (`GX.GammaLinkCircle.DevData.not_hasCCC_of_type`), through `Γ_p`-invariant time functions
  (`GX.SingularHSStructure.not_hasCCC_of_timeFunctionOn`, `…not_hasCCC_of_lexTime`,
  `GX.monotone_of_local`): time-like `p`, `GX.dsTime q`, `q = ±p` future time-like
  (`…not_hasCCC_of_timelike`, every cone angle); light-like `p`, `dsTime (±p)` then the height
  `∓t` along the steps parallel to `p` (`…not_hasCCC_of_null`, `…ht_step_null`, every degree);
  BTZ-like, `GX.btzTime`, the oriented square of the time-like distance to `±p` on the region
  where `π_p ŷ` is future (past) time-like (`…not_hasCCC_of_btz`, `…chart_mem_btzRegion`,
  `GX.btzTime_mono`).
* **Degree `≥ 4` (proved)**: `GX.GammaLinkCircle.DevData.not_isCausal_of_isHighDegree`.
* **The « in other words » for singular lines**: `GX.GammaLinkCircle.isCausalLine_iff`; its « only
  if » is sorry-free (`GX.GammaLinkCircle.DevData.not_misner_of_isCausal`), its « if » rests on three
  tagged `sorry`s: in `…not_hasCCC_of_deSitter`, no CCC for the space-like circles of degree `2`
  (tachyons) and of trivial holonomy `δ²` (the paper's claim, without an argument), and
  `…not_hasHighDegreeAt` (the degree of an apex link of `𝔢(L)` is the degree of `L`).
* **Finding**: `GX.exists_isSingularHSSurface_sing_empty_hasCCC`, a singular HS-surface without
  singular points with a CCC (`𝔢(L) ∖ {p̄, −p̄}`, `L` Misner; `…HasCCC.restrict_reg`).

## Hypothesis checklist

| BBS | here |
|---|---|
| « a singular HS-surface » (l.1116) | ✓ any `GX.SingularHSStructure` (`GX.IsSingularHSSurface` not needed) |
| « CCC » (l.1116) | ⚠ reading (SCOPE (a), (b)): a closed future causal curve of the regular de Sitter region, causal in the hyperboloid model of `dS²` |
| « a singularity of degree `≥ 4` » (l.1116) | ⚠ reading (SCOPE (c)): a point of `𝒮` with some link at `p̄` of degree `≥ 4` (space-like, light-like, or trivial holonomy `δᵏ`) |
| « the suspension `𝔢(L)` of the associated circle » (l.1117) | ⚠ for every developing data `Δ` (SCOPE (d)); for some: `isCausalLine_iff_exists` |
| « in other words » (l.1120–1125) | ✗ fails read for arbitrary non-compact singular HS-surfaces (`exists_isSingularHSSurface_sing_empty_hasCCC`; closed surfaces undecided); for `𝔢(L)`: `isCausalLine_iff`, « only if » proved, « if » on three tagged `sorry`s (tachyons, trivial holonomy, the apex degree) |
| « Misner singularities » (l.1124) | ✓ `C.linkType = .misner` (HSClassification) |
| the CTC of a Misner bigon (l.1059–1063) | ✓ `hasCCC_of_misner` (a CCC; that it is time-like is not stated) |

## SCOPE (disclosed)

* **(a) Causal curves.** BBS define causal curves only in AdS (l.1027–1033); in an HS-surface the
  only causal structure is the time orientation of the `dS²` regions (l.620–623). A causal curve is
  read: continuous, locally in a chart of `Σ ∖ 𝒮` with values in `dS²`, and future causal in the
  finite-difference sense on the hyperboloid model `{Q = 1}` of `dS²` (`s₁ ≤ s₂ ⇒ ŷ(s₂) − ŷ(s₁)`
  future causal or zero in `ℝ^{1,2}`), time-oriented by `ℝ^{1,2}` as in IPm SCOPE (a). For `C¹`
  curves of `dS²` it is the usual notion (the cone is closed and convex; argued, not formalized).
  Causal curves do not pass through points of `𝒮`: l.1032–1033 lets causal curves of AdS cross
  singular lines, which is a statement about `e(Σ)`, not about `Σ` (a question).
* **(b) CCC** is a `1`-periodic, non-constant, future causal curve (a past one, reversed, is one).
* **(c) Degree.** « Singularity of degree `≥ 4` » is read through the links at `p̄` of the point
  (`GX.SingularHSStructure.IsApexLink`): some link has a type of degree `≥ 4`. The types include
  `trivialHolonomy k` (holonomy `δᵏ`, degree `k`), outside the printed list (HSClassification
  SCOPE (b)); time-like and degree-`0` types have no degree `≥ 4`. That two links at `p̄` of one
  point have the same degree is not formalized (HSAntipodal SCOPE (b)); with « every link » read
  instead, the other direction of `isCausalLine_iff` would need it (a question).
* **(d) `𝔢(L)`** depends on developing data (HSSuspension SCOPE (b), OQ-126 (c)); `IsCausalLine`
  quantifies over all of them, and `isCausalLine_iff_exists` gives the same answer for some.
* **(e) Finding (l.1120–1125), a scope imprecision (AUDIT-1).** Read literally for every singular
  HS-surface (l.948–952 asks no compactness), « in other words » fails: the regular part of a Misner
  `𝔢(L)` is an HS-surface without singularities which has a CCC
  (`exists_isSingularHSSurface_sing_empty_hasCCC`). The example is the Misner neighbourhood with its
  singular point cut out; whether the sentence holds for closed surfaces or HS-spheres (l.780,
  l.1862) is not decided here. The intended reading is the singular-line form. Read for singular lines (the definition's second sentence, the
  context of l.1109–1112), it is `isCausalLine_iff`, whose « only if » is proved and whose « if »
  rests on `not_hasCCC_of_deSitter` (tachyons and trivial holonomy only) and `not_hasHighDegreeAt`.
  Light-like circles of degree `≥ 4` have no CCC either (`not_hasCCC_of_null` holds at every
  degree): for them only the degree clause makes `𝔢(L)` non-causal.
* **(f) Not formalized:** that the Misner curve is time-like; that a Misner singular point of a
  general `Σ` has CCCs in every neighbourhood (l.1059–1060; it needs the curves at heights
  `→ 0`, `cos τ p̂ + sin τ û(s)`); the AdS side (`bbslem:CTC`, `e(Σ)`, l.1066–1101).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The causal relation of `dS²` -/

/-- **The point of the hyperboloid `{Q = 1}` on the ray `σ`** (for `σ ∈ dS²`): `dS²` is the
Klein model of de Sitter space (l.592–593), whose hyperboloid model is `{Q = 1}`. -/
def dsHat (σ : HS 2) : 𝕄 := (Real.sqrt (Causal.Flat.minkQ (σ : 𝕄)))⁻¹ • (σ : 𝕄)

/-- **`τ` lies in the causal future of `σ` in `dS²`**: both are in `dS²` and the difference of
their points on the hyperboloid is future causal (or zero) in `ℝ^{1,2}`. -/
def DSLe (σ τ : HS 2) : Prop :=
  σ ∈ HS.piece 2 .deSitter ∧ τ ∈ HS.piece 2 .deSitter ∧
    Causal.Flat.IsFutureCausal (dsHat τ - dsHat σ)

theorem dsHat_smul (A : Causal.Flat.lorentz 2) {σ : HS 2} (hσ : σ ∈ HS.piece 2 .deSitter) :
    dsHat (A • σ) = (A : 𝕄 ≃ₗ[ℝ] 𝕄) (dsHat σ) := by
  have hQ : 0 < Causal.Flat.minkQ (σ : 𝕄) := hσ
  set A' : 𝕄 ≃ₗ[ℝ] 𝕄 := (A : 𝕄 ≃ₗ[ℝ] 𝕄)
  have hn : 0 < ‖A' σ‖ := norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff A').2 (raySphere_ne_zero σ))
  have hc : ((A • σ : HS 2) : 𝕄) = ‖A' σ‖⁻¹ • A' σ := coe_hs_smul A σ
  have hq : Causal.Flat.minkQ ((A • σ : HS 2) : 𝕄) = ‖A' σ‖⁻¹ ^ 2 * Causal.Flat.minkQ (σ : 𝕄) := by
    rw [hc, Causal.Flat.minkQ_smul, Causal.Flat.lorentz.minkQ_apply A.2]
  have hs : Real.sqrt (Causal.Flat.minkQ ((A • σ : HS 2) : 𝕄)) =
      ‖A' σ‖⁻¹ * Real.sqrt (Causal.Flat.minkQ (σ : 𝕄)) := by
    rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.2 hn).le]
  have hk : 0 < Real.sqrt (Causal.Flat.minkQ (σ : 𝕄)) := Real.sqrt_pos.2 hQ
  rw [dsHat, dsHat, hs, hc, map_smul, smul_smul, mul_inv, inv_inv]
  congr 1
  field_simp

theorem dsLe_smul_iff (A : Causal.Flat.lorentz 2) {σ τ : HS 2} :
    DSLe (A • σ) (A • τ) ↔ DSLe σ τ := by
  unfold DSLe
  rw [HS.smul_mem_piece_iff, HS.smul_mem_piece_iff]
  refine and_congr_right fun hσ => and_congr_right fun hτ => ?_
  rw [dsHat_smul A hσ, dsHat_smul A hτ, ← map_sub, Causal.Flat.lorentz.isFutureCausal_apply_iff A.2]

theorem dsHat_eq_iff {σ τ : HS 2} (hσ : σ ∈ HS.piece 2 .deSitter)
    (hτ : τ ∈ HS.piece 2 .deSitter) : dsHat σ = dsHat τ ↔ σ = τ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hσ' : 0 < Real.sqrt (Causal.Flat.minkQ (σ : 𝕄)) := Real.sqrt_pos.2 hσ
  have hτ' : 0 < Real.sqrt (Causal.Flat.minkQ (τ : 𝕄)) := Real.sqrt_pos.2 hτ
  have hn := congrArg norm h
  simp only [dsHat, norm_smul, norm_raySphere, mul_one, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hσ'), abs_of_pos (inv_pos.2 hτ')] at hn
  apply Subtype.ext
  have h' := h
  rw [dsHat, dsHat, hn] at h'
  exact smul_right_injective 𝕄 (inv_pos.2 hτ').ne' h'

/-! ## 2. The degree of a type -/

/-- **A type of degree `≥ 4`**: space-like or light-like of degree `k ≥ 4` (l.1123), and the trivial
holonomy `δᵏ`, `k ≥ 4`, outside the printed list (HSClassification SCOPE (b)). -/
def LinkType.IsHighDegree : LinkType → Prop
  | .spacelike _ k => 4 ≤ k
  | .lightlike _ _ k => 4 ≤ k
  | .trivialHolonomy k => 4 ≤ k
  | _ => False

/-! ## 3. Causal curves and closed causal curves in a singular HS-surface -/

namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] (A : SingularHSStructure M)

/-- **A future causal curve** of a singular HS-surface: a continuous `γ : ℝ → M` which, near every
parameter, lies in the source of a chart of `A` (so in `Σ ∖ 𝒮`) and reads in it as a future causal
curve of `dS²`. -/
def IsFutureCausalCurve (γ : ℝ → M) : Prop :=
  Continuous γ ∧ ∀ s, ∃ e ∈ A.atlas, ∃ ε > 0, ∀ s₁ ∈ Ioo (s - ε) (s + ε), γ s₁ ∈ e.source ∧
    ∀ s₂ ∈ Ioo (s - ε) (s + ε), s₁ ≤ s₂ → DSLe (e (γ s₁)) (e (γ s₂))

/-- **A closed causal curve** (CCC): a future causal curve of period `1`, not constant. -/
def IsClosedCausalCurve (γ : ℝ → M) : Prop :=
  A.IsFutureCausalCurve γ ∧ Function.Periodic γ 1 ∧ ∃ s₁ s₂, γ s₁ ≠ γ s₂

/-- `Σ` **has a CCC**. -/
def HasCCC : Prop := ∃ γ : ℝ → M, A.IsClosedCausalCurve γ

/-- **The chart does not matter**: a future causal curve reads as a future causal curve of `dS²`
near every parameter in every chart of `A` containing the point. -/
theorem IsFutureCausalCurve.forall_chart {A : SingularHSStructure M} {γ : ℝ → M}
    (h : A.IsFutureCausalCurve γ) {e' : OpenPartialHomeomorph M (HS 2)} (he' : e' ∈ A.atlas)
    {s : ℝ} (hs : γ s ∈ e'.source) : ∃ ε > 0, ∀ s₁ ∈ Ioo (s - ε) (s + ε), γ s₁ ∈ e'.source ∧
      ∀ s₂ ∈ Ioo (s - ε) (s + ε), s₁ ≤ s₂ → DSLe (e' (γ s₁)) (e' (γ s₂)) := by
  obtain ⟨hc, hγ⟩ := h
  obtain ⟨e, he, ε, hε, h'⟩ := hγ s
  have hse : γ s ∈ e.source := (h' s ⟨by linarith, by linarith⟩).1
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid (A.compatible e he e' he') hse hs
  have hg' := hc.continuousAt.eventually (hg.and (e'.open_source.mem_nhds hs))
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hg'
  have hmem : ∀ a ∈ Ioo (s - min ε ε₀) (s + min ε ε₀), a ∈ Ioo (s - ε) (s + ε) ∧
      e' (γ a) = g • e (γ a) ∧ γ a ∈ e'.source := fun a ha => by
    have hb : a ∈ Metric.ball s ε₀ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [ha.1, min_le_right ε ε₀], by linarith [ha.2, min_le_right ε ε₀]⟩
    exact ⟨⟨by linarith [ha.1, min_le_left ε ε₀], by linarith [ha.2, min_le_left ε ε₀]⟩,
      hball hb⟩
  refine ⟨min ε ε₀, lt_min hε hε₀, fun a ha => ⟨(hmem a ha).2.2, fun b hb hab => ?_⟩⟩
  rw [(hmem a ha).2.1, (hmem b hb).2.1, dsLe_smul_iff]
  exact (h' a (hmem a ha).1).2 b (hmem b hb).1 hab

/-- **`x ∈ 𝒮` is a singularity of degree `≥ 4`**: it has a link at `p̄` of degree `≥ 4`. -/
def HasHighDegreeAt (x : M) : Prop :=
  ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), A.IsApexLink x C ∧
    C.linkType.IsHighDegree

/-- **`bbsdef:Hcausal`, first sentence**: a singular HS-surface is causal if it admits no
singularity of degree `≥ 4` and no CCC. -/
def IsCausal : Prop := (∀ x ∈ A.sing, ¬ A.HasHighDegreeAt x) ∧ ¬ A.HasCCC

end SingularHSStructure

/-- **`bbsdef:Hcausal`, second sentence**: a singular line of type `L` is causal if `𝔢(L)` is
causal (for every developing data; `GammaLinkCircle.isCausalLine_iff_exists` for some). -/
def GammaLinkCircle.IsCausalLine {L : Type} [TopologicalSpace L] (C : GammaLinkCircle L) : Prop :=
  ∀ Δ : C.DevData, Δ.suspStructure.IsCausal

/-! ## 4. Time functions exclude closed causal curves -/

/-- A function on `ℝ` which is monotone near every point is monotone. -/
theorem monotone_of_local {f : ℝ → ℝ} (h : ∀ s, ∃ ε > 0, ∀ s₁ ∈ Ioo (s - ε) (s + ε),
    ∀ s₂ ∈ Ioo (s - ε) (s + ε), s₁ ≤ s₂ → f s₁ ≤ f s₂) : Monotone f := by
  intro a b hab
  choose ε hε hf using h
  obtain ⟨δ, hδ, hL⟩ := lebesgue_number_lemma_of_metric (s := Icc a b)
    (c := fun s => Ioo (s - ε s) (s + ε s)) isCompact_Icc (fun _ => isOpen_Ioo)
    (fun x _ => mem_iUnion.2 ⟨x, ⟨by linarith [hε x], by linarith [hε x]⟩⟩)
  have step : ∀ x ∈ Icc a b, ∀ y, x ≤ y → y < x + δ → f x ≤ f y := fun x hx y hxy hy => by
    obtain ⟨i, hi⟩ := hL x hx
    have hxi : x ∈ Ioo (i - ε i) (i + ε i) := hi (Metric.mem_ball_self hδ)
    have hyi : y ∈ Ioo (i - ε i) (i + ε i) := hi (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    exact hf i x hxi y hyi hxy
  have key : ∀ n : ℕ, a + n * (δ / 2) ≤ b → f a ≤ f (a + n * (δ / 2)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : a + m * (δ / 2) ≤ b := by push_cast at hm; linarith
      refine (ih hm').trans (step _ ⟨by nlinarith [m.cast_nonneg (α := ℝ)], hm'⟩ _ ?_ ?_)
      · push_cast; linarith
      · push_cast; linarith
  set N := ⌊(b - a) / (δ / 2)⌋₊
  have hδ2 : 0 < δ / 2 := by linarith
  have hN1 : (N : ℝ) * (δ / 2) ≤ b - a :=
    (le_div_iff₀ hδ2).1 (Nat.floor_le (div_nonneg (by linarith) hδ2.le))
  have hN2 : b - a < (N + 1 : ℝ) * (δ / 2) :=
    (div_lt_iff₀ hδ2).1 (Nat.lt_floor_add_one _)
  refine (key N (by linarith)).trans (step _ ⟨by nlinarith [N.cast_nonneg (α := ℝ)], by linarith⟩
    _ (by linarith) (by nlinarith))

namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] (A : SingularHSStructure M)

/-- **A time function excludes closed causal curves.** If `Φ : HS² → ℝ` reads the same in all
charts of `A` and is non-decreasing along the causal relation of `dS²`, strictly between distinct
points, then `A` has no CCC. -/
theorem not_hasCCC_of_timeFunctionOn (Φ : HS 2 → ℝ) (R : Set (HS 2))
    (hR : ∀ e ∈ A.atlas, ∀ x ∈ e.source, e x ∈ HS.piece 2 .deSitter → e x ∈ R)
    (hΦ : ∀ e ∈ A.atlas, ∀ e' ∈ A.atlas, ∀ x ∈ e.source, x ∈ e'.source → Φ (e x) = Φ (e' x))
    (hmono₀ : ∀ σ ∈ R, ∀ τ ∈ R, DSLe σ τ → Φ σ ≤ Φ τ ∧ (Φ σ = Φ τ → σ = τ)) : ¬ A.HasCCC := by
  have hmono : ∀ e ∈ A.atlas, ∀ x ∈ e.source, ∀ y ∈ e.source, DSLe (e x) (e y) →
      Φ (e x) ≤ Φ (e y) ∧ (Φ (e x) = Φ (e y) → e x = e y) := fun e he x hx y hy h =>
    hmono₀ _ (hR e he x hx h.1) _ (hR e he y hy h.2.1) h
  rintro ⟨γ, ⟨hγc, hγ⟩, hper, s₁, s₂, hne⟩
  classical
  let τ : M → ℝ := fun x => if h : ∃ e ∈ A.atlas, x ∈ e.source then Φ (h.choose x) else 0
  have hτ : ∀ e ∈ A.atlas, ∀ x ∈ e.source, τ x = Φ (e x) := fun e he x hx => by
    have h : ∃ e ∈ A.atlas, x ∈ e.source := ⟨e, he, hx⟩
    simp only [τ, dif_pos h]
    exact hΦ _ h.choose_spec.1 e he x h.choose_spec.2 hx
  have hmon : Monotone (τ ∘ γ) := monotone_of_local fun s => by
    obtain ⟨e, he, ε, hε, h⟩ := hγ s
    refine ⟨ε, hε, fun a ha b hb hab => ?_⟩
    show τ (γ a) ≤ τ (γ b)
    rw [hτ e he _ (h a ha).1, hτ e he _ (h b hb).1]
    exact (hmono e he _ (h a ha).1 _ (h b hb).1 ((h a ha).2 b hb hab)).1
  have hconst : ∀ s, τ (γ s) = τ (γ 0) := by
    have hp : Function.Periodic (τ ∘ γ) 1 := fun s => by
      show τ (γ (s + 1)) = τ (γ s); rw [hper s]
    intro s
    have h1 : τ (γ (s - ⌊s⌋)) = τ (γ s) := by
      have := hp.sub_int_mul_eq ⌊s⌋ (x := s)
      simpa using this
    have h0 : τ (γ 0) ≤ τ (γ (s - ⌊s⌋)) := hmon (by linarith [Int.floor_le s])
    have h2 : τ (γ (s - ⌊s⌋)) ≤ τ (γ 1) := hmon (by linarith [Int.lt_floor_add_one s])
    have h3 : τ (γ 1) = τ (γ 0) := by
      have := hp 0; simpa using this
    linarith
  have hlc : IsLocallyConstant γ := by
    refine (IsLocallyConstant.iff_eventually_eq γ).2 fun s => ?_
    obtain ⟨e, he, ε, hε, h⟩ := hγ s
    have hs : s ∈ Ioo (s - ε) (s + ε) := ⟨by linarith, by linarith⟩
    filter_upwards [isOpen_Ioo.mem_nhds hs] with a ha
    have hmin : min a s ∈ Ioo (s - ε) (s + ε) := by
      rcases min_choice a s with h' | h' <;> rw [h'] <;> assumption
    have hmax : max a s ∈ Ioo (s - ε) (s + ε) := by
      rcases max_choice a s with h' | h' <;> rw [h'] <;> assumption
    have heq : Φ (e (γ (min a s))) = Φ (e (γ (max a s))) := by
      rw [← hτ e he _ (h _ hmin).1, ← hτ e he _ (h _ hmax).1, hconst (min a s), hconst (max a s)]
    have he' := (hmono e he _ (h _ hmin).1 _ (h _ hmax).1 ((h _ hmin).2 _ hmax min_le_max)).2 heq
    have hγe := e.injOn (h _ hmin).1 (h _ hmax).1 he'
    rcases le_total a s with has | has
    · rwa [min_eq_left has, max_eq_right has] at hγe
    · rw [min_eq_right has, max_eq_left has] at hγe
      exact hγe.symm
  exact hne (hlc.apply_eq_of_preconnectedSpace s₁ s₂)

theorem not_hasCCC_of_timeFunction (Φ : HS 2 → ℝ)
    (hΦ : ∀ e ∈ A.atlas, ∀ e' ∈ A.atlas, ∀ x ∈ e.source, x ∈ e'.source → Φ (e x) = Φ (e' x))
    (hmono : ∀ σ τ, DSLe σ τ → Φ σ ≤ Φ τ ∧ (Φ σ = Φ τ → σ = τ)) : ¬ A.HasCCC :=
  A.not_hasCCC_of_timeFunctionOn Φ univ (fun _ _ _ _ _ => mem_univ _) hΦ
    fun σ _ τ _ h => hmono σ τ h

end SingularHSStructure

namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] (A : SingularHSStructure M)

/-- **A lexicographic time function excludes closed causal curves.** If `Φ` reads the same in all
charts and is non-decreasing along the causal relation of `dS²`, and `h : M → ℝ` is non-decreasing,
strictly between distinct points, along the causal steps on which `Φ` is constant, then `A` has no
CCC. -/
theorem not_hasCCC_of_lexTime (Φ : HS 2 → ℝ)
    (hΦ : ∀ e ∈ A.atlas, ∀ e' ∈ A.atlas, ∀ x ∈ e.source, x ∈ e'.source → Φ (e x) = Φ (e' x))
    (hmono : ∀ σ τ, DSLe σ τ → Φ σ ≤ Φ τ) (h : M → ℝ)
    (hh : ∀ e ∈ A.atlas, ∀ x ∈ e.source, ∀ y ∈ e.source, DSLe (e x) (e y) → Φ (e x) = Φ (e y) →
      h x ≤ h y ∧ (h x = h y → x = y)) : ¬ A.HasCCC := by
  rintro ⟨γ, ⟨hγc, hγ⟩, hper, s₁, s₂, hne⟩
  classical
  let τ : M → ℝ := fun x => if h : ∃ e ∈ A.atlas, x ∈ e.source then Φ (h.choose x) else 0
  have hτ : ∀ e ∈ A.atlas, ∀ x ∈ e.source, τ x = Φ (e x) := fun e he x hx => by
    have h : ∃ e ∈ A.atlas, x ∈ e.source := ⟨e, he, hx⟩
    simp only [τ, dif_pos h]
    exact hΦ _ h.choose_spec.1 e he x h.choose_spec.2 hx
  have hconst : ∀ {f : M → ℝ}, Monotone (f ∘ γ) → ∀ s, f (γ s) = f (γ 0) := fun {f} hmon s => by
    have hp : Function.Periodic (f ∘ γ) 1 := fun s => by
      show f (γ (s + 1)) = f (γ s); rw [hper s]
    have h1 : f (γ (s - ⌊s⌋)) = f (γ s) := by
      have := hp.sub_int_mul_eq ⌊s⌋ (x := s)
      simpa using this
    have h0 : f (γ 0) ≤ f (γ (s - ⌊s⌋)) := hmon (by linarith [Int.floor_le s])
    have h2 : f (γ (s - ⌊s⌋)) ≤ f (γ 1) := hmon (by linarith [Int.lt_floor_add_one s])
    have h3 : f (γ 1) = f (γ 0) := by
      have := hp 0; simpa using this
    linarith
  have hτc : ∀ s, τ (γ s) = τ (γ 0) := hconst (monotone_of_local fun s => by
    obtain ⟨e, he, ε, hε, h⟩ := hγ s
    refine ⟨ε, hε, fun a ha b hb hab => ?_⟩
    show τ (γ a) ≤ τ (γ b)
    rw [hτ e he _ (h a ha).1, hτ e he _ (h b hb).1]
    exact hmono _ _ ((h a ha).2 b hb hab))
  have hΦe : ∀ e ∈ A.atlas, ∀ a b, γ a ∈ e.source → γ b ∈ e.source →
      Φ (e (γ a)) = Φ (e (γ b)) := fun e he a b ha hb => by
    rw [← hτ e he _ ha, ← hτ e he _ hb, hτc a, hτc b]
  have hhc : ∀ s, h (γ s) = h (γ 0) := hconst (monotone_of_local fun s => by
    obtain ⟨e, he, ε, hε, h'⟩ := hγ s
    refine ⟨ε, hε, fun a ha b hb hab => ?_⟩
    exact (hh e he _ (h' a ha).1 _ (h' b hb).1 ((h' a ha).2 b hb hab)
      (hΦe e he a b (h' a ha).1 (h' b hb).1)).1)
  have hlc : IsLocallyConstant γ := by
    refine (IsLocallyConstant.iff_eventually_eq γ).2 fun s => ?_
    obtain ⟨e, he, ε, hε, h'⟩ := hγ s
    have hs : s ∈ Ioo (s - ε) (s + ε) := ⟨by linarith, by linarith⟩
    filter_upwards [isOpen_Ioo.mem_nhds hs] with a ha
    rcases le_total a s with has | has
    · exact (hh e he _ (h' a ha).1 _ (h' s hs).1 ((h' a ha).2 s hs has)
        (hΦe e he a s (h' a ha).1 (h' s hs).1)).2 (by rw [hhc a, hhc s])
    · exact ((hh e he _ (h' s hs).1 _ (h' a ha).1 ((h' s hs).2 a ha has)
        (hΦe e he s a (h' s hs).1 (h' a ha).1)).2 (by rw [hhc a, hhc s])).symm
  exact hne (hlc.apply_eq_of_preconnectedSpace s₁ s₂)

end SingularHSStructure

/-! ## 5. Time functions of time-like and light-like apices -/

theorem dsHat_eq_zero {σ : HS 2} (hσ : σ ∉ HS.piece 2 .deSitter) : dsHat σ = 0 := by
  have : Causal.Flat.minkQ (σ : 𝕄) ≤ 0 := not_lt.1 hσ
  rw [dsHat, Real.sqrt_eq_zero'.2 this, inv_zero, zero_smul]

/-- `−B(ŷ, q)`: for `q` future time-like, the time coordinate of `dS²` in a frame with `e₀ = q`. -/
def dsTime (q : 𝕄) (σ : HS 2) : ℝ := -Causal.Flat.minkB (dsHat σ) q

theorem dsTime_smul {q : 𝕄} (g : Causal.Flat.lorentz 2) (hg : (g : 𝕄 ≃ₗ[ℝ] 𝕄) q = q)
    (σ : HS 2) : dsTime q (g • σ) = dsTime q σ := by
  by_cases hσ : σ ∈ HS.piece 2 .deSitter
  · rw [dsTime, dsTime, dsHat_smul g hσ]
    conv_lhs => rw [← hg]
    rw [Causal.Flat.lorentz.minkB_apply g.2]
  · have hσ' : g • σ ∉ HS.piece 2 .deSitter := by rwa [HS.smul_mem_piece_iff]
    rw [dsTime, dsTime, dsHat_eq_zero hσ, dsHat_eq_zero hσ']

theorem dsTime_mono {q : 𝕄} (hq : Causal.Flat.IsFutureTimelike q) {σ τ : HS 2} (h : DSLe σ τ) :
    dsTime q σ ≤ dsTime q τ ∧ (dsTime q σ = dsTime q τ → σ = τ) := by
  obtain ⟨hσ, hτ, hv⟩ := h
  have hB := Causal.Flat.minkB_le_zero_of_isFutureCausal hv ⟨hq.1.le, hq.2.le⟩
  rw [Causal.Flat.minkB_sub_left] at hB
  refine ⟨by unfold dsTime; linarith, fun he => ?_⟩
  by_contra hne
  have h0 : dsHat τ - dsHat σ ≠ 0 := sub_ne_zero.2 fun h => hne ((dsHat_eq_iff hσ hτ).1 h.symm)
  have := Causal.Flat.minkB_neg_of_future hv h0 hq
  rw [Causal.Flat.minkB_sub_left] at this
  unfold dsTime at he
  linarith

/-! ### Light-like apices: the height along the segments tangent to `∂ℍ²±` -/

theorem div_sqrt_strictMono {b : ℝ} (hb : 0 < b) {x₁ x₂ : ℝ} (h : x₁ < x₂) :
    x₁ / Real.sqrt (x₁ ^ 2 + b ^ 2) < x₂ / Real.sqrt (x₂ ^ 2 + b ^ 2) := by
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have hS₁ : 0 < Real.sqrt (x₁ ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hS₂ : 0 < Real.sqrt (x₂ ^ 2 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  have e₁ := Real.sq_sqrt (show 0 ≤ x₁ ^ 2 + b ^ 2 by positivity)
  have e₂ := Real.sq_sqrt (show 0 ≤ x₂ ^ 2 + b ^ 2 by positivity)
  rw [div_lt_div_iff₀ hS₁ hS₂]
  set S₁ := Real.sqrt (x₁ ^ 2 + b ^ 2)
  set S₂ := Real.sqrt (x₂ ^ 2 + b ^ 2)
  rcases le_or_gt 0 x₁ with h1 | h1
  · have h2 : 0 < x₂ := by linarith
    have hsq : (x₁ * S₂) ^ 2 < (x₂ * S₁) ^ 2 := by
      have hx : x₁ ^ 2 < x₂ ^ 2 := by nlinarith
      rw [mul_pow, mul_pow, e₁, e₂]; nlinarith [mul_lt_mul_of_pos_left hx hb2]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  · rcases le_or_gt x₂ 0 with h2 | h2
    · have hsq : (-x₂ * S₁) ^ 2 < (-x₁ * S₂) ^ 2 := by
        have hx : x₂ ^ 2 < x₁ ^ 2 := by nlinarith
        rw [mul_pow, mul_pow, e₁, e₂]; nlinarith [mul_lt_mul_of_pos_left hx hb2]
      have := lt_of_pow_lt_pow_left₀ 2 (by nlinarith) hsq
      linarith
    · nlinarith

/-- `arg (a + b i)` decreases with `a`, for `b > 0`. -/
theorem arg_add_lt {a b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    Complex.arg (((a + μ : ℝ) : ℂ) + (b : ℂ) * Complex.I) <
      Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I) := by
  set z₁ : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  set z₂ : ℂ := ((a + μ : ℝ) : ℂ) + (b : ℂ) * Complex.I
  have him1 : z₁.im = b := by simp [z₁]
  have hre1 : z₁.re = a := by simp [z₁]
  have him2 : z₂.im = b := by simp [z₂]
  have hre2 : z₂.re = a + μ := by simp [z₂]
  have hn1 : ‖z₁‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre1, him1]; ring_nf
  have hn2 : ‖z₂‖ = Real.sqrt ((a + μ) ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hre2, him2]; ring_nf
  have hm1 := abs_le.1 (Complex.abs_re_div_norm_le_one z₁)
  have hm2 := abs_le.1 (Complex.abs_re_div_norm_le_one z₂)
  rw [Complex.arg_of_im_pos (by rw [him2]; exact hb), Complex.arg_of_im_pos (by rw [him1]; exact hb)]
  refine Real.strictAntiOn_arccos ⟨hm1.1, hm1.2⟩ ⟨hm2.1, hm2.2⟩ ?_
  rw [hre1, hre2, hn1, hn2]
  exact div_sqrt_strictMono hb (by linarith)

/-- The height on the segment through `w` of `[a p + b w]`, `b > 0`, is `arg (a + b i)`. -/
theorem arcAngle_rayNormalize {p : HS 2} {w : 𝕄} (hw : tpMk p w ≠ 0) {a b : ℝ} (hb : 0 < b) :
    arcAngle p (rayNormalize p (a • (p : 𝕄) + b • w)) w =
      Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I) := by
  set z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have him : z.im = b := by simp [z]
  have hre : z.re = a := by simp [z]
  have hz : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at him; linarith
  have hθ0 : 0 < Complex.arg z := lt_of_le_of_ne (Complex.arg_nonneg_iff.2 (him ▸ hb.le))
    fun h => by have := (Complex.arg_eq_zero_iff.1 h.symm).2; rw [him] at this; linarith
  have hθπ : Complex.arg z < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr (by rw [him]; exact hb.ne'))
  have hne : a • (p : 𝕄) + b • w ≠ 0 := fun h => by
    have : tpMk p (a • (p : 𝕄) + b • w) = b • tpMk p w := by
      show Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
      change a • tpMk p (p : 𝕄) + _ = _
      rw [tpMk_self, smul_zero, zero_add]
    rw [h] at this
    exact smul_ne_zero hb.ne' hw (this.symm.trans (Submodule.Quotient.mk_zero _))
  have hv : arcVec p w (Complex.arg z) = ‖z‖⁻¹ • (a • (p : 𝕄) + b • w) := by
    rw [arcVec, Complex.cos_arg hz, Complex.sin_arg, hre, him, smul_add, smul_smul, smul_smul,
      div_eq_inv_mul, div_eq_inv_mul]
  have h1 : arcPt p w (Complex.arg z) = rayNormalize p (a • (p : 𝕄) + b • w) := by
    rw [arcPt, hv, rayNormalize_smul_of_pos p hne (inv_pos.2 (norm_pos_iff.2 hz))]
  rw [← h1, arcAngle_arcPt p hw hθ0 hθπ]

/-- A future causal vector orthogonal to a future null `q ≠ 0` is a non-negative multiple of `q`. -/
theorem eq_smul_of_minkB_null {q v : 𝕄} (hq : Causal.Flat.IsFutureCausal q)
    (hq0 : Causal.Flat.minkQ q = 0) (hqne : q ≠ 0) (hv : Causal.Flat.IsFutureCausal v)
    (hB : Causal.Flat.minkB v q = 0) : ∃ c : ℝ, 0 ≤ c ∧ v = c • q := by
  have hq1 : 0 < q.1 := lt_of_le_of_ne hq.1 fun h => hqne (Causal.Flat.eq_zero_of_fst_eq_zero h.symm hq.2)
  have hqn : ‖q.2‖ = q.1 := by
    have : ‖q.2‖ ^ 2 = q.1 ^ 2 := by unfold Causal.Flat.minkQ at hq0; linarith
    nlinarith [norm_nonneg q.2, sq_nonneg (‖q.2‖ - q.1), sq_nonneg (‖q.2‖ + q.1)]
  have hvn : ‖v.2‖ ≤ v.1 := by
    have := Causal.Flat.minkQ_le_zero_iff.1 hv.2
    nlinarith [norm_nonneg v.2, hv.1]
  have hin := real_inner_le_norm v.2 q.2
  unfold Causal.Flat.minkB at hB
  have hv1 : v.1 ≤ ‖v.2‖ := by
    rw [hqn] at hin
    have : v.1 * q.1 ≤ ‖v.2‖ * q.1 := by linarith
    exact le_of_mul_le_mul_right this hq1
  have hQv : Causal.Flat.minkQ v = 0 := by
    unfold Causal.Flat.minkQ
    have : ‖v.2‖ = v.1 := le_antisymm hvn hv1
    rw [this]; ring
  by_cases hv0 : v = 0
  · exact ⟨0, le_rfl, by rw [hv0, zero_smul]⟩
  obtain ⟨c, hc⟩ := Causal.Flat.eq_smul_of_null_orth hq0 hqne hQv
    (by rw [Causal.Flat.minkB_comm]; unfold Causal.Flat.minkB; exact hB)
  refine ⟨c, ?_, hc⟩
  have : v.1 = c * q.1 := by rw [hc]; rfl
  by_contra hneg
  have : v.1 < 0 := by rw [this]; exact mul_neg_of_neg_of_pos (not_le.1 hneg) hq1
  linarith [hv.1]

/-! ## 6. The closed time-like curves of a Misner `𝔢(L)` -/

theorem dsHat_of_coe_eq {σ : HS 2} {v : 𝕄} {c : ℝ} (hc : 0 < c) (h : (σ : 𝕄) = c • v) :
    dsHat σ = (Real.sqrt (Causal.Flat.minkQ v))⁻¹ • v := by
  rw [dsHat, h, Causal.Flat.minkQ_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le,
    smul_smul, mul_inv]
  by_cases hq : Real.sqrt (Causal.Flat.minkQ v) = 0
  · simp [hq]
  · congr 1; field_simp

theorem tpMk_perpLin (p : HS 2) (w : 𝕄) :
    tpMk p (perpLin p w) = Causal.Flat.minkQ (p : 𝕄) • tpMk p w := by
  rw [perpLin_apply]
  show Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
  change _ - _ • tpMk p (p : 𝕄) = _
  rw [tpMk_self, smul_zero, sub_zero]

/-- At `p ∈ dS²`, a vector orthogonal to `p`, `dsU p` and `jVec p` is zero. -/
theorem eq_zero_of_minkB_frame {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {v : 𝕄}
    (h1 : Causal.Flat.minkB v (p : 𝕄) = 0) (h2 : Causal.Flat.minkB v (dsU p) = 0)
    (h3 : Causal.Flat.minkB v (jVec p) = 0) : v = 0 := by
  have hx := sum_sq_of_norm (norm_snd_of_deSitter hp)
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  rw [minkQ_two] at hQ
  rw [minkB_two] at h1 h2 h3
  simp only [dsU, jVec, jRot_zero, jRot_one, PiLp.smul_apply, smul_eq_mul] at h2 h3
  set t := (p : 𝕄).1
  set x := (p : 𝕄).2
  have ht : t ^ 2 < 1 := by linarith
  have ha : v.1 = 0 := by
    have : v.1 * (1 - t ^ 2) = 0 := by linear_combination (-1 : ℝ) * h2 + t * h1
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by linarith)
  have hb : v.2 0 = 0 := by
    linear_combination x 0 * h1 - x 1 * h3 + x 0 * t * ha - v.2 0 * hx
  have hc : v.2 1 = 0 := by
    linear_combination x 1 * h1 + x 0 * h3 + x 1 * t * ha - v.2 1 * hx
  refine Prod.ext ha ?_
  ext i
  fin_cases i
  · exact hb
  · exact hc

theorem continuous_minkB_left (w : 𝕄) : Continuous fun v : 𝕄 => Causal.Flat.minkB v w := by
  unfold Causal.Flat.minkB; fun_prop

/-- **`p^⊥` is the Lorentzian plane spanned by `e₀ = GammaP.dsE₀ p` and `j = jVec p`**, at `p ∈ dS²`. -/
theorem perp_decomp {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {u : 𝕄}
    (hu : Causal.Flat.minkB (p : 𝕄) u = 0) :
    u = (-Causal.Flat.minkB u (GammaP.dsE₀ p)) • GammaP.dsE₀ p + Causal.Flat.minkB u (jVec p) • jVec p := by
  obtain ⟨h0, h1, h01, hp0, hp1, -⟩ := GammaP.dsFrame hp
  have h0' : Causal.Flat.minkB (GammaP.dsE₀ p) (GammaP.dsE₀ p) = -1 := by rw [← Causal.Flat.minkQ_eq_minkB, h0]
  have h1' : Causal.Flat.minkB (jVec p) (jVec p) = 1 := by rw [← Causal.Flat.minkQ_eq_minkB, h1]
  have h10 : Causal.Flat.minkB (jVec p) (GammaP.dsE₀ p) = 0 := by rw [Causal.Flat.minkB_comm, h01]
  have hk : 0 < Real.sqrt (Causal.Flat.minkQ (p : 𝕄)) := Real.sqrt_pos.2 hp
  have hU : dsU p = Real.sqrt (Causal.Flat.minkQ (p : 𝕄)) • GammaP.dsE₀ p := by
    rw [GammaP.dsE₀, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  rw [← sub_eq_zero]
  set v := u - ((-Causal.Flat.minkB u (GammaP.dsE₀ p)) • GammaP.dsE₀ p + Causal.Flat.minkB u (jVec p) • jVec p)
  have hv0 : Causal.Flat.minkB v (GammaP.dsE₀ p) = 0 := by
    simp only [v, Causal.Flat.minkB_sub_left, Causal.Flat.minkB_add_left,
      Causal.Flat.minkB_smul_left, h0', h10]; ring
  refine eq_zero_of_minkB_frame hp ?_ ?_ ?_
  · rw [Causal.Flat.minkB_comm] at hu
    simp only [v, Causal.Flat.minkB_sub_left, Causal.Flat.minkB_add_left,
      Causal.Flat.minkB_smul_left, hu, Causal.Flat.minkB_comm (GammaP.dsE₀ p), Causal.Flat.minkB_comm (jVec p),
      hp0, hp1]; ring
  · rw [hU, Causal.Flat.minkB_smul_right, hv0, mul_zero]
  · simp only [v, Causal.Flat.minkB_sub_left, Causal.Flat.minkB_add_left,
      Causal.Flat.minkB_smul_left, h1', h01]; ring

/-- `α e₀ + β j` is future causal when `|β| ≤ α`. -/
theorem isFutureCausal_frame {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : β ^ 2 ≤ α ^ 2) :
    Causal.Flat.IsFutureCausal (α • GammaP.dsE₀ p + β • jVec p) := by
  obtain ⟨h0, h1, h01, -, -, hf⟩ := GammaP.dsFrame hp
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, jVec, mul_zero, add_zero]
    exact mul_nonneg hα hf.1.le
  · rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul,
      Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_right, h0, h1, h01]
    nlinarith

/-- On one branch of the unit hyperbola `b² − a² = 1`, the order of `a` is the causal order. -/
theorem hyperbola_sq_le {a₁ a₂ b₁ b₂ : ℝ} (h₁ : b₁ ^ 2 = 1 + a₁ ^ 2) (h₂ : b₂ ^ 2 = 1 + a₂ ^ 2)
    (hb : 0 < b₁ * b₂) : (b₂ - b₁) ^ 2 ≤ (a₂ - a₁) ^ 2 := by
  have hsq : (1 + a₁ * a₂) ^ 2 ≤ (b₁ * b₂) ^ 2 := by
    rw [mul_pow, h₁, h₂]; nlinarith [sq_nonneg (a₁ - a₂)]
  have := (abs_le_of_sq_le_sq' hsq hb.le).2
  nlinarith

/-- **A continuous, locally injective `f : ℝ → ℝ` is locally increasing everywhere or locally
decreasing everywhere**; read through `κ = ±1`, it is locally increasing everywhere. -/
theorem exists_sign_strictMonoOn {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : ∀ s, ∃ ε > 0, InjOn f (Ioo (s - ε) (s + ε))) :
    ∃ κ : ℝ, (κ = 1 ∨ κ = -1) ∧
      ∀ s, ∃ ε > 0, StrictMonoOn (fun x => f (κ * x)) (Ioo (s - ε) (s + ε)) := by
  let U : Set ℝ := {s | ∃ ε > 0, StrictMonoOn f (Ioo (s - ε) (s + ε))}
  let V : Set ℝ := {s | ∃ ε > 0, StrictAntiOn f (Ioo (s - ε) (s + ε))}
  have shrink : ∀ {s ε s' : ℝ}, s' ∈ Ioo (s - ε) (s + ε) → ∃ ε' > 0,
      Ioo (s' - ε') (s' + ε') ⊆ Ioo (s - ε) (s + ε) := fun {s ε s'} hs' =>
    ⟨min (s' - (s - ε)) (s + ε - s'), lt_min (by linarith [hs'.1]) (by linarith [hs'.2]),
      fun y hy => ⟨by linarith [hy.1, min_le_left (s' - (s - ε)) (s + ε - s')],
        by linarith [hy.2, min_le_right (s' - (s - ε)) (s + ε - s')]⟩⟩
  have hU : IsOpen U := isOpen_iff_mem_nhds.2 fun s ⟨ε, hε, h⟩ =>
    Filter.mem_of_superset (Ioo_mem_nhds (by linarith : s - ε < s) (by linarith : s < s + ε))
      fun s' hs' => by
        obtain ⟨ε', hε', hsub⟩ := shrink hs'
        exact ⟨ε', hε', h.mono hsub⟩
  have hV : IsOpen V := isOpen_iff_mem_nhds.2 fun s ⟨ε, hε, h⟩ =>
    Filter.mem_of_superset (Ioo_mem_nhds (by linarith : s - ε < s) (by linarith : s < s + ε))
      fun s' hs' => by
        obtain ⟨ε', hε', hsub⟩ := shrink hs'
        exact ⟨ε', hε', h.mono hsub⟩
  have hUV : Disjoint U V := Set.disjoint_left.2 fun s ⟨ε, hε, h⟩ ⟨ε', hε', h'⟩ => by
    set m := min ε ε'
    have hm : 0 < m := lt_min hε hε'
    have h1 : s ∈ Ioo (s - ε) (s + ε) := ⟨by linarith, by linarith⟩
    have h2 : s + m / 2 ∈ Ioo (s - ε) (s + ε) :=
      ⟨by linarith, by linarith [min_le_left ε ε']⟩
    have h1' : s ∈ Ioo (s - ε') (s + ε') := ⟨by linarith, by linarith⟩
    have h2' : s + m / 2 ∈ Ioo (s - ε') (s + ε') :=
      ⟨by linarith, by linarith [min_le_right ε ε']⟩
    have := h h1 h2 (by linarith)
    have := h' h1' h2' (by linarith)
    linarith
  have hcov : (univ : Set ℝ) ⊆ U ∪ V := fun s _ => by
    obtain ⟨ε, hε, hi⟩ := hinj s
    rcases hf.continuousOn.strictMonoOn_of_injOn_Ioo (by linarith : s - ε < s + ε) hi with h | h
    · exact Or.inl ⟨ε, hε, h⟩
    · exact Or.inr ⟨ε, hε, h⟩
  rcases hcov (mem_univ 0) with h0 | h0
  · have hall := isPreconnected_univ.subset_left_of_subset_union hU hV hUV hcov ⟨0, mem_univ 0, h0⟩
    refine ⟨1, Or.inl rfl, fun s => ?_⟩
    obtain ⟨ε, hε, h⟩ := hall (mem_univ s)
    exact ⟨ε, hε, fun x hx y hy hxy => by simpa using h hx hy hxy⟩
  · have hall := isPreconnected_univ.subset_left_of_subset_union hV hU hUV.symm
      (by rw [union_comm]; exact hcov) ⟨0, mem_univ 0, h0⟩
    refine ⟨-1, Or.inr rfl, fun s => ?_⟩
    obtain ⟨ε, hε, h⟩ := hall (mem_univ (-s))
    refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
    have hx' : -1 * x ∈ Ioo (-s - ε) (-s + ε) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : -1 * y ∈ Ioo (-s - ε) (-s + ε) := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    exact h hy' hx' (by linarith)

namespace GammaLinkCircle.DevData

variable {L : Type} [TopologicalSpace L] {C : GammaLinkCircle L} (Δ : C.DevData)

/-- The projection of the lift `w(s)` on `p^⊥` (times `Q(p)`). -/
def uVec (s : ℝ) : 𝕄 := perpLin C.pt (Δ.vlift s)

/-- The point `[u(s)]` of `HS²`: on the segment `𝔢(d(s))`, the point of `p^⊥`. -/
def yPt (s : ℝ) : HS 2 := rayNormalize C.pt (Δ.uVec s)

/-- Its height on the segment of the cone chart. -/
def tAng (s : ℝ) : ℝ := arcAngle C.pt (Δ.yPt s) (Δ.vlift s)

/-- **The curve of the Misner bigon**: `s ↦ [E(κ s), t(κ s)]`, the points of `𝔢(L)` developed
on `p^⊥` (`κ = ±1` chooses the time orientation). -/
def cccCurve (κ : ℝ) (s : ℝ) : BiSusp L :=
  BiSusp.mk (Δ.E (κ * s)) (projIcc 0 Real.pi Real.pi_pos.le (Δ.tAng (κ * s)))

variable {Δ}

theorem tpMk_uVec (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) : tpMk C.pt (Δ.uVec s) ≠ 0 := by
  rw [uVec, tpMk_perpLin]
  exact smul_ne_zero (ne_of_gt hp) (Δ.tpMk_vlift_ne s)

theorem uVec_ne_zero (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) : Δ.uVec s ≠ 0 := fun h =>
  tpMk_uVec hp s (by rw [h]; rfl)

theorem coe_yPt (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    (Δ.yPt s : 𝕄) = ‖Δ.uVec s‖⁻¹ • Δ.uVec s :=
  coe_rayNormalize _ (uVec_ne_zero hp s)

theorem tpMk_yPt (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    tpMk C.pt (Δ.yPt s : 𝕄) = (‖Δ.uVec s‖⁻¹ * Causal.Flat.minkQ (C.pt : 𝕄)) • tpMk C.pt (Δ.vlift s) := by
  rw [coe_yPt hp, mul_smul, ← tpMk_perpLin]
  rfl

theorem tpMk_yPt_ne (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) : tpMk C.pt (Δ.yPt s : 𝕄) ≠ 0 := by
  rw [tpMk_yPt hp]
  exact smul_ne_zero (mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 (uVec_ne_zero hp s)))
    (ne_of_gt hp)) (Δ.tpMk_vlift_ne s)

theorem dirOf_yPt (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    dirOf C.pt (Δ.yPt s : 𝕄) = Δ.d s := by
  have hc : 0 < ‖Δ.uVec s‖⁻¹ * Causal.Flat.minkQ (C.pt : 𝕄) :=
    mul_pos (inv_pos.2 (norm_pos_iff.2 (uVec_ne_zero hp s))) hp
  rw [← Δ.dirOf_vlift s, ← dirOf_smul_of_pos C.pt (Δ.tpMk_vlift_ne s) hc]
  show rayNormalize _ (tpMk C.pt _) = rayNormalize _ (tpMk C.pt _)
  rw [tpMk_yPt hp s]
  rfl

theorem arcPt_tAng (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    arcPt C.pt (Δ.vlift s) (Δ.tAng s) = Δ.yPt s :=
  arcPt_arcAngle C.pt (tpMk_yPt_ne hp s) (Δ.tpMk_vlift_ne s)
    ((dirOf_yPt hp s).trans (Δ.dirOf_vlift s).symm)

theorem tAng_mem (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    0 < Δ.tAng s ∧ Δ.tAng s < Real.pi :=
  arcAngle_mem C.pt (tpMk_yPt_ne hp s) (Δ.tpMk_vlift_ne s)

theorem uVec_add_one (s : ℝ) :
    Δ.uVec (s + 1) = ((Δ.hol : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.uVec s) := by
  rw [uVec, uVec, Δ.vlift_add_one, perpLin_gammaP]

theorem rayNormalize_lorentz (B : Causal.Flat.lorentz 2) {v : 𝕄} (hv : v ≠ 0) (σ₀ : HS 2) :
    rayNormalize σ₀ ((B : 𝕄 ≃ₗ[ℝ] 𝕄) v) = B • rayNormalize σ₀ v := by
  have hBv : (B : 𝕄 ≃ₗ[ℝ] 𝕄) v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hv
  symm
  rw [hs_smul_def, linRaySmul_eq_iff]
  refine ⟨‖v‖⁻¹ * ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) v‖, mul_pos (inv_pos.2 (norm_pos_iff.2 hv))
    (norm_pos_iff.2 hBv), ?_⟩
  rw [coe_rayNormalize _ hv, coe_rayNormalize _ hBv, map_smul, smul_smul, mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 hBv), mul_one]

theorem yPt_add_one (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) :
    Δ.yPt (s + 1) = (Δ.hol : Causal.Flat.lorentz 2) • Δ.yPt s := by
  rw [yPt, yPt, uVec_add_one, rayNormalize_lorentz _ (uVec_ne_zero hp s)]

theorem tAng_add_one (hp : C.pt ∈ HS.piece 2 .deSitter) (s : ℝ) : Δ.tAng (s + 1) = Δ.tAng s := by
  have h : Δ.yPt (s + 1) = arcPt C.pt (Δ.vlift (s + 1)) (Δ.tAng s) := by
    rw [yPt_add_one hp, ← arcPt_tAng hp s, smul_arcPt _ _ (Δ.tpMk_vlift_ne s), Δ.vlift_add_one]
  obtain ⟨h0, hπ⟩ := tAng_mem (Δ := Δ) hp s
  rw [tAng, h, arcAngle_arcPt C.pt (Δ.tpMk_vlift_ne _) h0 hπ]

theorem tAng_add_sign (hp : C.pt ∈ HS.piece 2 .deSitter) {κ : ℝ} (hκ : κ = 1 ∨ κ = -1) (x : ℝ) :
    Δ.tAng (x + κ) = Δ.tAng x := by
  rcases hκ with rfl | rfl
  · exact tAng_add_one hp x
  · rw [← tAng_add_one hp (x + -1)]; ring_nf

theorem E_add_sign {κ : ℝ} (hκ : κ = 1 ∨ κ = -1) (x : ℝ) : Δ.E (x + κ) = Δ.E x := by
  rcases hκ with rfl | rfl
  · exact Δ.periodic.add_one x
  · rw [← Δ.periodic.add_one (x + -1)]; ring_nf

theorem continuous_uVec : Continuous Δ.uVec :=
  (LinearMap.continuous_of_finiteDimensional (perpLin C.pt)).comp Δ.continuous_vlift

theorem continuous_yPt (hp : C.pt ∈ HS.piece 2 .deSitter) : Continuous Δ.yPt :=
  continuous_iff_continuousAt.2 fun s =>
    (continuousAt_rayNormalize _ (uVec_ne_zero hp s)).comp continuous_uVec.continuousAt

theorem continuous_tAng (hp : C.pt ∈ HS.piece 2 .deSitter) : Continuous Δ.tAng :=
  continuous_iff_continuousAt.2 fun s =>
    (continuousAt_arcAngle C.pt (tpMk_yPt_ne hp s) (Δ.tpMk_vlift_ne s)).comp
      (f := fun s => ((Δ.yPt s : 𝕄), Δ.vlift s))
      ((continuous_subtype_val.comp (continuous_yPt hp)).prodMk Δ.continuous_vlift).continuousAt

theorem continuous_cccCurve (hp : C.pt ∈ HS.piece 2 .deSitter) (κ : ℝ) :
    Continuous (Δ.cccCurve κ) :=
  BiSusp.continuous_mk'.comp
    ((Δ.periodic.isCoveringMap.continuous.comp (continuous_const_mul κ)).prodMk
      (continuous_projIcc.comp ((continuous_tAng hp).comp (continuous_const_mul κ))))

theorem cccCurve_periodic (hp : C.pt ∈ HS.piece 2 .deSitter) {κ : ℝ} (hκ : κ = 1 ∨ κ = -1) :
    Function.Periodic (Δ.cccCurve κ) 1 := fun s => by
  rw [cccCurve, cccCurve, mul_add, mul_one, E_add_sign hκ, tAng_add_sign hp hκ]

theorem cccCurve_notMem_poles (hp : C.pt ∈ HS.piece 2 .deSitter) (κ s : ℝ) :
    Δ.cccCurve κ s ∉ BiSusp.poles L := by
  rw [BiSusp.notMem_poles_iff]
  obtain ⟨h0, hπ⟩ := tAng_mem (Δ := Δ) hp (κ * s)
  rw [cccCurve, BiSusp.ht_mk, coe_projIcc_of_mem ⟨h0.le, hπ.le⟩]
  exact ⟨h0, hπ⟩

variable (Δ) in
/-- The point `[E(x), t(x)]` of `𝔢(L)`. -/
def bPt (x : ℝ) : BiSusp L :=
  BiSusp.mk (Δ.E x) (projIcc 0 Real.pi Real.pi_pos.le (Δ.tAng x))

theorem cccCurve_eq (κ s : ℝ) : Δ.cccCurve κ s = Δ.bPt (κ * s) := rfl

theorem continuous_bPt (hp : C.pt ∈ HS.piece 2 .deSitter) : Continuous Δ.bPt := by
  have := continuous_cccCurve (Δ := Δ) hp 1
  have e : Δ.cccCurve 1 = Δ.bPt := funext fun s => by rw [cccCurve_eq, one_mul]
  rwa [e] at this

/-- **The curve read in a cone chart**: near every parameter, a chart of `𝔢(L)` sends `[E(x), t(x)]`
to `g · [u(x)]` for one `g ∈ Γ_p`. -/
theorem eventually_chart_bPt (hp : C.pt ∈ HS.piece 2 .deSitter)
    {e : OpenPartialHomeomorph (BiSusp L) (HS 2)} (he : e ∈ Δ.suspAtlas) {x : ℝ}
    (hx : Δ.bPt x ∈ e.source) : ∃ g : GammaP C.pt, ∀ᶠ x' in 𝓝 x,
      Δ.bPt x' ∈ e.source ∧ e (Δ.bPt x') = (g : Causal.Flat.lorentz 2) • Δ.yPt x' := by
  have hsrc : ∀ᶠ x' in 𝓝 x, Δ.bPt x' ∈ e.source :=
    (continuous_bPt hp).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hx)
  obtain ⟨c, W, hW, hl, rfl⟩ := he
  obtain ⟨q, hq, hqx⟩ := hx
  obtain ⟨h0, hπ⟩ := tAng_mem (Δ := Δ) hp x
  have hreg : (Δ.E x, projIcc 0 Real.pi Real.pi_pos.le (Δ.tAng x)) ∈ BiSusp.regSet (univ : Set L) :=
    ⟨trivial, by rw [coe_projIcc_of_mem ⟨h0.le, hπ.le⟩]; exact ⟨h0, hπ⟩⟩
  have hqe := BiSusp.mk'_injOn_regSet ⟨trivial, hq.2⟩ hreg hqx
  have hEx : Δ.E x ∈ c.source := by
    have := hq.1; rw [hqe] at this; exact this
  obtain ⟨s₀, hs₀, A, hA⟩ := hl (Δ.E x) hEx
  obtain ⟨n, hn⟩ := Δ.periodic.fiber s₀ x hs₀
  refine ⟨A * Δ.hol ^ (-n), ?_⟩
  have ht : Tendsto (fun x' => x' + ((-n : ℤ) : ℝ)) (𝓝 x) (𝓝 s₀) := by
    have : x + ((-n : ℤ) : ℝ) = s₀ := by rw [hn]; push_cast; ring
    rw [← this]
    exact (continuous_add_const _).tendsto x
  filter_upwards [hsrc, ht.eventually hA] with x' h1 h2
  refine ⟨h1, ?_⟩
  obtain ⟨h0', hπ'⟩ := tAng_mem (Δ := Δ) hp x'
  have hW' : W (Δ.E x') = (((A * Δ.hol ^ (-n) : GammaP C.pt) : Causal.Flat.lorentz 2) :
      𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift x') := by
    rw [← Δ.periodic.add_int x' (-n), h2, Δ.vlift_add_int, gammaP_coe_mul_apply]
  show arcPt C.pt (W (Δ.E x')) (projIcc 0 Real.pi Real.pi_pos.le (Δ.tAng x') : ℝ) = _
  rw [coe_projIcc_of_mem ⟨h0'.le, hπ'.le⟩, hW', ← smul_arcPt _ _ (Δ.tpMk_vlift_ne x'),
    arcPt_tAng hp]

/-- **The developing map is locally injective.** -/
theorem d_locally_injOn (s : ℝ) : ∃ ε > 0, InjOn Δ.d (Ioo (s - ε) (s + ε)) := by
  letI := C.atlas
  obtain ⟨A, hA⟩ := Δ.dev s
  obtain ⟨φ, hsφ, hφ⟩ := Δ.periodic.isCoveringMap.isLocalHomeomorph s
  have hc : ∀ᶠ s' in 𝓝 s, Δ.E s' ∈ (chartAt (Link C.pt) (Δ.E s)).source :=
    Δ.periodic.isCoveringMap.continuous.continuousAt.preimage_mem_nhds
      ((chartAt (Link C.pt) (Δ.E s)).open_source.mem_nhds (mem_chart_source _ _))
  have hall := hA.and (hc.and (φ.open_source.mem_nhds hsφ))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hall
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  have hx' : x ∈ Metric.ball s ε := by rw [Real.ball_eq_Ioo]; exact hx
  have hy' : y ∈ Metric.ball s ε := by rw [Real.ball_eq_Ioo]; exact hy
  obtain ⟨hx1, hx2, hx3⟩ := hball hx'
  obtain ⟨hy1, hy2, hy3⟩ := hball hy'
  rw [hx1, hy1] at hxy
  have h1 := (chartAt (Link C.pt) (Δ.E s)).injOn hx2 hy2 (smul_left_cancel _ hxy)
  rw [hφ] at h1
  exact φ.injOn hx3 hy3 h1

/-- **A Misner circle develops into space-like directions**, along any developing data. -/
theorem minkQ_uVec_pos_of_misner (h : C.HasType .misner) (s : ℝ) :
    0 < Causal.Flat.minkQ (Δ.uVec s) := by
  obtain ⟨θ, -, E', D', f, hl, hr, -, -, himg⟩ := h
  have hp : C.pt ∈ HS.piece 2 .deSitter := HS.mem_piece_iff_region.2 hr
  obtain ⟨ψ, -, -, -, hψ⟩ := Δ.periodic.exists_rel hl.1
  have hEψ : Δ.E ∘ ψ = E' := funext fun s => (hψ s).symm
  have dev1 : C.IsDevAlong E' (Δ.d ∘ ψ) := by
    have := Δ.dev.comp_reparam ψ.continuous
    rwa [hEψ] at this
  obtain ⟨A, hA, -⟩ := GammaLinkCircle.IsDevAlong.existsUnique_eq_smul
    hl.1.isCoveringMap.isLocalHomeomorph hl.2.2.2.1 dev1
  have hs : Δ.d s = A • linkCover C.pt θ (D' (ψ.symm s)) := by
    have := hA (ψ.symm s)
    simpa using this
  have hσ : 0 < Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ (D' (ψ.symm s)))) :=
    himg ⟨D' (ψ.symm s), mem_range_self _, rfl⟩
  have h1 : 0 < Causal.Flat.minkQ (dsProj C.pt (Δ.d s)) := by
    rw [hs, dsProj_smul, Causal.Flat.minkQ_smul, Causal.Flat.lorentz.minkQ_apply
      (A : Causal.Flat.lorentz 2).2]
    exact mul_pos (pow_pos (inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero C.pt A _))) 2) hσ
  rw [← Δ.dirOf_vlift s, dsProj_dirOf C.pt (Δ.tpMk_vlift_ne s), Causal.Flat.minkQ_smul] at h1
  exact pos_of_mul_pos_right h1 (sq_nonneg _)

variable (Δ) in
/-- `u(s)` normalised on the hyperboloid. -/
def uHat (s : ℝ) : 𝕄 := (Real.sqrt (Causal.Flat.minkQ (Δ.uVec s)))⁻¹ • Δ.uVec s

variable (Δ) in
/-- The `e₀`-coordinate of `û(s)` in `p^⊥`. -/
def aC (s : ℝ) : ℝ := -Causal.Flat.minkB (Δ.uHat s) (GammaP.dsE₀ C.pt)

variable (Δ) in
/-- The `j`-coordinate of `û(s)` in `p^⊥`. -/
def bC (s : ℝ) : ℝ := Causal.Flat.minkB (Δ.uHat s) (jVec C.pt)

section Spacelike

variable (hp : C.pt ∈ HS.piece 2 .deSitter) (hQu : ∀ s, 0 < Causal.Flat.minkQ (Δ.uVec s))
include hp hQu

theorem dsHat_yPt (s : ℝ) : dsHat (Δ.yPt s) = Δ.uHat s :=
  dsHat_of_coe_eq (inv_pos.2 (norm_pos_iff.2 (uVec_ne_zero hp s))) (coe_yPt hp s)

theorem yPt_mem (s : ℝ) : Δ.yPt s ∈ HS.piece 2 .deSitter := by
  show 0 < Causal.Flat.minkQ (Δ.yPt s : 𝕄)
  rw [coe_yPt hp, Causal.Flat.minkQ_smul]
  exact mul_pos (pow_pos (inv_pos.2 (norm_pos_iff.2 (uVec_ne_zero hp s))) 2) (hQu s)

theorem minkQ_uHat (s : ℝ) : Causal.Flat.minkQ (Δ.uHat s) = 1 := by
  rw [uHat, Causal.Flat.minkQ_smul, inv_pow, Real.sq_sqrt (hQu s).le, inv_mul_cancel₀ (hQu s).ne']

theorem uHat_eq (s : ℝ) : Δ.uHat s = Δ.aC s • GammaP.dsE₀ C.pt + Δ.bC s • jVec C.pt := by
  have hB : Causal.Flat.minkB (C.pt : 𝕄) (Δ.uHat s) = 0 := by
    rw [uHat, Causal.Flat.minkB_smul_right, uVec, minkB_perpLin, mul_zero]
  exact perp_decomp hp hB

theorem bC_sq (s : ℝ) : Δ.bC s ^ 2 = 1 + Δ.aC s ^ 2 := by
  obtain ⟨h0, h1, h01, -, -, -⟩ := GammaP.dsFrame hp
  have h := minkQ_uHat hp hQu s
  rw [uHat_eq hp hQu s, Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul,
    Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_right, h0, h1, h01] at h
  linarith

theorem continuous_uHat : Continuous Δ.uHat := by
  have hc := Causal.Flat.continuous_minkQ.comp (continuous_uVec (Δ := Δ))
  exact ((Real.continuous_sqrt.comp hc).inv₀ fun s => (Real.sqrt_pos.2 (hQu s)).ne').smul
    continuous_uVec

theorem continuous_aC : Continuous Δ.aC :=
  ((continuous_minkB_left _).comp (continuous_uHat hp hQu)).neg

theorem continuous_bC : Continuous Δ.bC :=
  (continuous_minkB_left _).comp (continuous_uHat hp hQu)

theorem bC_mul_pos (s₁ s₂ : ℝ) : 0 < Δ.bC s₁ * Δ.bC s₂ := by
  have hne : ∀ s, Δ.bC s ≠ 0 := fun s h => by
    have := bC_sq hp hQu s; rw [h] at this; nlinarith [sq_nonneg (Δ.aC s)]
  have hivt := intermediate_value_univ s₁ s₂ (continuous_bC hp hQu)
  have hivt' := intermediate_value_univ s₂ s₁ (continuous_bC hp hQu)
  rcases lt_or_gt_of_ne (hne s₁) with h1 | h1 <;> rcases lt_or_gt_of_ne (hne s₂) with h2 | h2
  · exact mul_pos_of_neg_of_neg h1 h2
  · obtain ⟨s, hs⟩ := hivt ⟨h1.le, h2.le⟩; exact absurd hs (hne s)
  · obtain ⟨s, hs⟩ := hivt' ⟨h2.le, h1.le⟩; exact absurd hs (hne s)
  · exact mul_pos h1 h2

/-- **The order of `a` is the causal order** along the curve. -/
theorem dsLe_yPt {s₁ s₂ : ℝ} (h : Δ.aC s₁ ≤ Δ.aC s₂) : DSLe (Δ.yPt s₁) (Δ.yPt s₂) := by
  refine ⟨yPt_mem hp hQu s₁, yPt_mem hp hQu s₂, ?_⟩
  rw [dsHat_yPt hp hQu, dsHat_yPt hp hQu, uHat_eq hp hQu s₁, uHat_eq hp hQu s₂]
  have : Δ.aC s₂ • GammaP.dsE₀ C.pt + Δ.bC s₂ • jVec C.pt -
      (Δ.aC s₁ • GammaP.dsE₀ C.pt + Δ.bC s₁ • jVec C.pt) =
      (Δ.aC s₂ - Δ.aC s₁) • GammaP.dsE₀ C.pt + (Δ.bC s₂ - Δ.bC s₁) • jVec C.pt := by module
  rw [this]
  exact isFutureCausal_frame hp (by linarith)
    (hyperbola_sq_le (bC_sq hp hQu s₁) (bC_sq hp hQu s₂) (bC_mul_pos hp hQu s₁ s₂))

theorem d_eq_of_aC_eq {s₁ s₂ : ℝ} (h : Δ.aC s₁ = Δ.aC s₂) : Δ.d s₁ = Δ.d s₂ := by
  have hb : Δ.bC s₁ = Δ.bC s₂ := by
    have h1 := bC_sq hp hQu s₁
    have h2 := bC_sq hp hQu s₂
    have hpos := bC_mul_pos hp hQu s₁ s₂
    have : (Δ.bC s₁ - Δ.bC s₂) * (Δ.bC s₁ + Δ.bC s₂) = 0 := by rw [h] at h1; linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · nlinarith
  have hu : Δ.uHat s₁ = Δ.uHat s₂ := by rw [uHat_eq hp hQu, uHat_eq hp hQu, h, hb]
  have hy : ∀ s, Δ.yPt s = rayNormalize C.pt (Δ.uHat s) := fun s => by
    rw [uHat, rayNormalize_smul_of_pos _ (uVec_ne_zero hp s) (inv_pos.2 (Real.sqrt_pos.2 (hQu s)))]
    rfl
  rw [← dirOf_yPt hp, ← dirOf_yPt hp, hy, hy, hu]

/-- `a` is locally injective. -/
theorem aC_locally_injOn (s : ℝ) : ∃ ε > 0, InjOn Δ.aC (Ioo (s - ε) (s + ε)) := by
  obtain ⟨ε, hε, h⟩ := Δ.d_locally_injOn s
  exact ⟨ε, hε, fun x hx y hy hxy => h hx hy (d_eq_of_aC_eq hp hQu hxy)⟩

end Spacelike

end GammaLinkCircle.DevData

/-! ## 7. The time function of a BTZ-like `𝔢(L)` -/

theorem isFutureTimelike_smul {c : ℝ} (hc : 0 < c) {v : 𝕄} (hv : Causal.Flat.IsFutureTimelike v) :
    Causal.Flat.IsFutureTimelike (c • v) :=
  ⟨by simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos hc hv.1,
    by rw [Causal.Flat.minkQ_smul]; exact mul_neg_of_pos_of_neg (pow_pos hc 2) hv.2⟩

/-- A causal vector pairing non-positively with a future time-like one is future causal. -/
theorem isFutureCausal_of_minkB_nonpos {w e : 𝕄} (hw : Causal.Flat.minkQ w ≤ 0)
    (he : Causal.Flat.IsFutureTimelike e) (hB : Causal.Flat.minkB w e ≤ 0) :
    Causal.Flat.IsFutureCausal w := by
  refine ⟨le_of_not_gt fun h => ?_, hw⟩
  have hw' : Causal.Flat.IsFutureCausal (-w) := ⟨by simp; linarith, by simpa using hw⟩
  have h0 : -w ≠ 0 := fun h' => by
    have := congrArg Prod.fst h'; simp at this; linarith
  have := Causal.Flat.minkB_neg_of_future hw' h0 he
  rw [Causal.Flat.minkB_neg_left] at this
  linarith

/-- **The projection on `p^⊥` keeps future causal vectors**, at `p ∈ dS²`. -/
theorem isFutureCausal_perpLin {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {v : 𝕄}
    (hv : Causal.Flat.IsFutureCausal v) : Causal.Flat.IsFutureCausal (perpLin p v) := by
  obtain ⟨-, -, -, hpe₀, -, hf⟩ := GammaP.dsFrame hp
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  refine isFutureCausal_of_minkB_nonpos ?_ hf ?_
  · rw [perpLin_apply, sub_eq_add_neg, ← neg_smul, Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul,
      Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_right,
      Causal.Flat.minkB_comm v]
    nlinarith [hv.2, sq_nonneg (Causal.Flat.minkB (p : 𝕄) v)]
  · rw [perpLin_apply, Causal.Flat.minkB_sub_left, Causal.Flat.minkB_smul_left,
      Causal.Flat.minkB_smul_left, hpe₀, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hQ.le
      (Causal.Flat.minkB_le_zero_of_isFutureCausal hv ⟨hf.1.le, hf.2.le⟩)

/-- **The BTZ time function** `−ε Q(π_p ŷ)` (`ε = 1`: future time-like projections, `ε = −1`: past
ones): the square of the time-like distance to `±p`, oriented. -/
def btzTime (p : HS 2) (ε : ℝ) (σ : HS 2) : ℝ := -ε * Causal.Flat.minkQ (perpLin p (dsHat σ))

/-- Its domain: the points whose projection on `p^⊥` is `ε` times future time-like. -/
def btzRegion (p : HS 2) (ε : ℝ) : Set (HS 2) :=
  {σ | Causal.Flat.IsFutureTimelike (ε • perpLin p (dsHat σ))}

theorem btzTime_smul {p : HS 2} (ε : ℝ) (g : GammaP p) (σ : HS 2) :
    btzTime p ε ((g : Causal.Flat.lorentz 2) • σ) = btzTime p ε σ := by
  by_cases hσ : σ ∈ HS.piece 2 .deSitter
  · rw [btzTime, btzTime, dsHat_smul _ hσ, perpLin_gammaP,
      Causal.Flat.lorentz.minkQ_apply (g : Causal.Flat.lorentz 2).2]
  · have hσ' : (g : Causal.Flat.lorentz 2) • σ ∉ HS.piece 2 .deSitter := by
      rwa [HS.smul_mem_piece_iff]
    rw [btzTime, btzTime, dsHat_eq_zero hσ, dsHat_eq_zero hσ']

theorem btzTime_mono {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {σ τ : HS 2} (hσR : σ ∈ btzRegion p ε) (hτR : τ ∈ btzRegion p ε) (h : DSLe σ τ) :
    btzTime p ε σ ≤ btzTime p ε τ ∧ (btzTime p ε σ = btzTime p ε τ → σ = τ) := by
  obtain ⟨hσ, hτ, hv⟩ := h
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  set v := dsHat τ - dsHat σ
  have hd := isFutureCausal_perpLin hp hv
  have hsplit : perpLin p (dsHat τ) = perpLin p (dsHat σ) + perpLin p v := by
    simp only [v, map_sub]; abel
  have key : perpLin p v = 0 → σ = τ := fun h0 => by
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 ((perpLin_eq_zero_iff p hQ.ne').1 h0)
    have hQv := hv.2
    rw [hc, Causal.Flat.minkQ_smul] at hQv
    have hc2 : c ^ 2 ≤ 0 := by
      by_contra hh
      have := mul_pos (lt_of_not_ge hh) hQ
      linarith
    have hc0 : c = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm hc2 (sq_nonneg c))
    have : v = 0 := by rw [hc, hc0, zero_smul]
    exact (dsHat_eq_iff hσ hτ).1 (sub_eq_zero.1 this).symm
  have hBd : ∀ {a : 𝕄}, Causal.Flat.IsFutureTimelike a →
      Causal.Flat.minkB a (perpLin p v) ≤ 0 ∧
        (Causal.Flat.minkB a (perpLin p v) = 0 → perpLin p v = 0) := fun {a} ha => by
    refine ⟨Causal.Flat.minkB_le_zero_of_isFutureCausal ⟨ha.1.le, ha.2.le⟩ hd, fun h0 => ?_⟩
    by_contra hne
    have := Causal.Flat.minkB_neg_of_future hd hne ha
    rw [Causal.Flat.minkB_comm] at this
    linarith
  rcases hε with rfl | rfl
  · simp only [btzRegion, one_smul, mem_setOf_eq] at hσR hτR
    obtain ⟨hB1, hB2⟩ := hBd hσR
    have hQd := hd.2
    have e : Causal.Flat.minkQ (perpLin p (dsHat τ)) = Causal.Flat.minkQ (perpLin p (dsHat σ)) +
        2 * Causal.Flat.minkB (perpLin p (dsHat σ)) (perpLin p v) + Causal.Flat.minkQ (perpLin p v) := by
      rw [hsplit, Causal.Flat.minkQ_add]
    simp only [btzTime]
    refine ⟨by nlinarith, fun heq => key (hB2 (by nlinarith))⟩
  · simp only [btzRegion, neg_one_smul, mem_setOf_eq] at hσR hτR
    obtain ⟨hB1, hB2⟩ := hBd hτR
    have hQd := hd.2
    have e : Causal.Flat.minkQ (-perpLin p (dsHat σ)) = Causal.Flat.minkQ (-perpLin p (dsHat τ)) +
        2 * Causal.Flat.minkB (-perpLin p (dsHat τ)) (perpLin p v) + Causal.Flat.minkQ (perpLin p v) := by
      rw [← Causal.Flat.minkQ_add, hsplit]; congr 1; abel
    rw [Causal.Flat.minkQ_neg, Causal.Flat.minkQ_neg] at e
    simp only [btzTime]
    refine ⟨by nlinarith, fun heq => key (hB2 (by nlinarith))⟩

namespace GammaLinkCircle.DevData

variable {L : Type} [TopologicalSpace L] {C : GammaLinkCircle L} (Δ : C.DevData)

/-- **The developed image of `Δ` lies in a `Γ_p`-invariant set** containing the image of one lifted
developing pair. -/
theorem d_mem_of_image {S : Set (Link C.pt)} (hS : ∀ A : GammaP C.pt, ∀ σ ∈ S, A • σ ∈ S)
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E' : ℝ → L} {D' : ℝ → ℝ} {f : GTilde} (hl : C.IsLiftedDev θ E' D' f)
    (himg : linkCover C.pt θ '' range D' ⊆ S) (s : ℝ) : Δ.d s ∈ S := by
  obtain ⟨ψ, -, -, -, hψ⟩ := Δ.periodic.exists_rel hl.1
  have hEψ : Δ.E ∘ ψ = E' := funext fun s => (hψ s).symm
  have dev1 : C.IsDevAlong E' (Δ.d ∘ ψ) := by
    have := Δ.dev.comp_reparam ψ.continuous
    rwa [hEψ] at this
  obtain ⟨A, hA, -⟩ := GammaLinkCircle.IsDevAlong.existsUnique_eq_smul
    hl.1.isCoveringMap.isLocalHomeomorph hl.2.2.2.1 dev1
  have hs : Δ.d s = A • linkCover C.pt θ (D' (ψ.symm s)) := by
    have := hA (ψ.symm s)
    simpa using this
  rw [hs]
  exact hS A _ (himg ⟨D' (ψ.symm s), mem_range_self _, rfl⟩)

variable {Δ}

/-- **The chart values of a BTZ-like `𝔢(L)` in `dS²` lie in the BTZ region.** -/
theorem chart_mem_btzRegion {ε : ℝ}
    (hS : ∀ s, Causal.Flat.IsFutureTimelike (ε • dsProj C.pt (Δ.d s)))
    {e : OpenPartialHomeomorph (BiSusp L) (HS 2)} (he : e ∈ Δ.suspAtlas) {x : BiSusp L}
    (hx : x ∈ e.source) (hxd : e x ∈ HS.piece 2 .deSitter) : e x ∈ btzRegion C.pt ε := by
  obtain ⟨c', W, hW, hl, rfl⟩ := he
  obtain ⟨⟨σ, t⟩, ⟨hσ, ht0, htπ⟩, rfl⟩ := hx
  set p := C.pt
  have hex : suspChart c' W hW (BiSusp.mk' (σ, t)) = arcPt p (W σ) t := rfl
  rw [hex] at hxd ⊢
  obtain ⟨s₀, hs₀, A, hA⟩ := hl σ hσ
  have hWσ : W σ = ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Δ.vlift s₀) := by
    rw [← hs₀]; exact hA.self_of_nhds
  have hw : tpMk p (W σ) ≠ 0 := hW.tpMk_ne σ hσ
  set V := arcVec p (W σ) (t : ℝ)
  have hV : V ≠ 0 := arcVec_ne_zero p hw t
  have hxc : ((arcPt p (W σ) t : HS 2) : 𝕄) = ‖V‖⁻¹ • V := coe_rayNormalize _ hV
  have hQV : 0 < Causal.Flat.minkQ V := by
    have h := (show 0 < Causal.Flat.minkQ ((arcPt p (W σ) t : HS 2) : 𝕄) from hxd)
    rw [hxc, Causal.Flat.minkQ_smul] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  have hk : 0 < (Real.sqrt (Causal.Flat.minkQ V))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hQV)
  have hxh : dsHat (arcPt p (W σ) t) = (Real.sqrt (Causal.Flat.minkQ V))⁻¹ • V :=
    dsHat_of_coe_eq (inv_pos.2 (norm_pos_iff.2 hV)) hxc
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htπ
  have hpV : perpLin p V = Real.sin t • perpLin p (W σ) := by
    simp only [V, arcVec, map_add, map_smul, perpLin_self, smul_zero, zero_add]
  have hdp : dsProj p (Δ.d s₀) = ‖tpMk p (Δ.vlift s₀)‖⁻¹ • perpLin p (Δ.vlift s₀) := by
    rw [← Δ.dirOf_vlift s₀, dsProj_dirOf p (Δ.tpMk_vlift_ne s₀)]
  have hn : 0 < ‖tpMk p (Δ.vlift s₀)‖ := norm_pos_iff.2 (Δ.tpMk_vlift_ne s₀)
  have key : ε • perpLin p (dsHat (arcPt p (W σ) t)) =
      ((Real.sqrt (Causal.Flat.minkQ V))⁻¹ * Real.sin t * ‖tpMk p (Δ.vlift s₀)‖) •
        ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (ε • dsProj p (Δ.d s₀)) := by
    rw [hxh, map_smul, hpV, hWσ, perpLin_gammaP, hdp, map_smul, map_smul, smul_smul, smul_smul,
      smul_smul, smul_smul]
    congr 1
    field_simp
  show Causal.Flat.IsFutureTimelike _
  rw [key]
  exact isFutureTimelike_smul (mul_pos (mul_pos hk hsin) hn)
    (Causal.Flat.lorentz.isFutureTimelike_apply (A : Causal.Flat.lorentz 2).2 (hS s₀))

/-- **A BTZ-like `𝔢(L)` has no CCC**: `btzTime` is a time function on its de Sitter region. -/
theorem not_hasCCC_of_btz (hp : C.pt ∈ HS.piece 2 .deSitter) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hS : ∀ s, Causal.Flat.IsFutureTimelike (ε • dsProj C.pt (Δ.d s))) :
    ¬ Δ.suspStructure.HasCCC := by
  refine Δ.suspStructure.not_hasCCC_of_timeFunctionOn (btzTime C.pt ε) (btzRegion C.pt ε)
    (fun e he x hx hxd => chart_mem_btzRegion hS he hx hxd)
    (fun e he e' he' x hx hx' => ?_) (fun σ hσ τ hτ h => btzTime_mono hp hε hσ hτ h)
  obtain ⟨g, hg⟩ := Δ.suspAtlas_eventually_eq_smul he he' ⟨hx, hx'⟩
  rw [hg.self_of_nhds, btzTime_smul]

end GammaLinkCircle.DevData

/-! ## 8. Main statements -/

section Main

variable {L : Type} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- **A Misner `𝔢(L)` has a closed time-like curve** (l.1059–1063). -/
theorem GammaLinkCircle.DevData.hasCCC_of_misner (Δ : C.DevData) (h : C.linkType = .misner) :
    Δ.suspStructure.HasCCC := by
  have hm : C.HasType .misner := C.hasType_iff.2 h
  have hp : C.pt ∈ HS.piece 2 .deSitter := by
    obtain ⟨θ, -, E', D', f, -, hr, -⟩ := hm
    exact HS.mem_piece_iff_region.2 hr
  have hQu := Δ.minkQ_uVec_pos_of_misner hm
  obtain ⟨κ, hκ, hmono⟩ :=
    exists_sign_strictMonoOn (continuous_aC hp hQu) (aC_locally_injOn hp hQu)
  have hloc : ∀ s, ∃ e ∈ Δ.suspAtlas, ∃ g : GammaP C.pt, ∃ ε > 0,
      StrictMonoOn (fun x => Δ.aC (κ * x)) (Ioo (s - ε) (s + ε)) ∧
      ∀ s' ∈ Ioo (s - ε) (s + ε), Δ.cccCurve κ s' ∈ e.source ∧
        e (Δ.cccCurve κ s') = (g : Causal.Flat.lorentz 2) • Δ.yPt (κ * s') := by
    intro s
    have hx : Δ.bPt (κ * s) ∈ support Δ.suspAtlas := by
      rw [Δ.support_suspAtlas]; exact cccCurve_notMem_poles hp κ s
    obtain ⟨e, he, hxe⟩ := mem_support.1 hx
    obtain ⟨g, hg⟩ := eventually_chart_bPt hp he hxe
    have hg' := ((continuous_const_mul κ).tendsto s).eventually hg
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hg'
    obtain ⟨ε₁, hε₁, hm₁⟩ := hmono s
    refine ⟨e, he, g, min ε₀ ε₁, lt_min hε₀ hε₁,
      hm₁.mono fun y hy => ⟨by linarith [hy.1, min_le_right ε₀ ε₁],
        by linarith [hy.2, min_le_right ε₀ ε₁]⟩, fun s' hs' => ?_⟩
    have : s' ∈ Metric.ball s ε₀ := by
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [hs'.1, min_le_left ε₀ ε₁], by linarith [hs'.2, min_le_left ε₀ ε₁]⟩
    exact hball this
  refine ⟨Δ.cccCurve κ, ⟨continuous_cccCurve hp κ, fun s => ?_⟩, cccCurve_periodic hp hκ, ?_⟩
  · obtain ⟨e, he, g, ε, hε, hm, hd⟩ := hloc s
    refine ⟨e, he, ε, hε, fun s₁ h₁ => ⟨(hd s₁ h₁).1, fun s₂ h₂ h12 => ?_⟩⟩
    rw [(hd s₁ h₁).2, (hd s₂ h₂).2, dsLe_smul_iff]
    exact dsLe_yPt hp hQu (hm.monotoneOn h₁ h₂ h12)
  · obtain ⟨e, he, g, ε, hε, hm, hd⟩ := hloc 0
    have h0 : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
    have h1 : ε / 2 ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
    refine ⟨0, ε / 2, fun heq => ?_⟩
    have hy : Δ.yPt (κ * 0) = Δ.yPt (κ * (ε / 2)) := by
      have := congrArg e heq
      rw [(hd 0 h0).2, (hd _ h1).2] at this
      exact smul_left_cancel _ this
    have ha : Δ.aC (κ * 0) = Δ.aC (κ * (ε / 2)) := by
      simp only [aC]
      rw [← dsHat_yPt hp hQu, ← dsHat_yPt hp hQu, hy]
    exact absurd ha (hm h0 h1 (by linarith)).ne

/-- `𝔢(L)` is not causal when `L` has degree `≥ 4`. -/
theorem GammaLinkCircle.DevData.not_isCausal_of_isHighDegree (Δ : C.DevData)
    (h : C.linkType.IsHighDegree) : ¬ Δ.suspStructure.IsCausal := by
  haveI := C.nonempty
  rintro ⟨hdeg, -⟩
  have hn : BiSusp.north L ∈ Δ.suspStructure.sing := Or.inl rfl
  exact hdeg _ hn ⟨L, inferInstance, C, Δ.isApexLink_north, h⟩

/-- **A time-like `𝔢(L)` has no CCC.** -/
theorem GammaLinkCircle.DevData.not_hasCCC_of_timelike (Δ : C.DevData)
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) < 0) : ¬ Δ.suspStructure.HasCCC := by
  obtain ⟨q, hq, hpq⟩ : ∃ q : 𝕄, Causal.Flat.IsFutureTimelike q ∧
      ∀ g : GammaP C.pt, ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) q = q := by
    rcases Causal.Flat.isFutureTimelike_or_neg hp with h | h
    · exact ⟨_, h, fun g => g.2⟩
    · exact ⟨_, h, fun g => by rw [map_neg, g.2]⟩
  refine Δ.suspStructure.not_hasCCC_of_timeFunction (dsTime q) (fun e he e' he' x hx hx' => ?_)
    (fun σ τ h => dsTime_mono hq h)
  obtain ⟨g, hg⟩ := Δ.suspAtlas_eventually_eq_smul he he' ⟨hx, hx'⟩
  rw [hg.self_of_nhds, dsTime_smul _ (hpq g)]

theorem minkQ_dsHat {σ : HS 2} (hσ : σ ∈ HS.piece 2 .deSitter) : Causal.Flat.minkQ (dsHat σ) = 1 := by
  have hQ : 0 < Causal.Flat.minkQ (σ : 𝕄) := hσ
  rw [dsHat, Causal.Flat.minkQ_smul, inv_pow, Real.sq_sqrt hQ.le, inv_mul_cancel₀ hQ.ne']

/-- **The causal steps along `q = ±p`, `p` light-like, move the height monotonically.** In a cone
chart of `𝔢(L)`, if `e y` is in the causal future of `e x` with the same `dsTime q`, then `e y` is
`e x` moved along `q`, on the segment of `x`, and the height `t` decreases (`q = p`) or increases
(`q = −p`) strictly unless `y = x`. -/
theorem GammaLinkCircle.DevData.ht_step_null {L : Type} [TopologicalSpace L] {C : GammaLinkCircle L}
    (Δ : C.DevData) (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hq : Causal.Flat.IsFutureCausal (ε • (C.pt : 𝕄)))
    {e : OpenPartialHomeomorph (BiSusp L) (HS 2)} (he : e ∈ Δ.suspAtlas) {x y : BiSusp L}
    (hx : x ∈ e.source) (hy : y ∈ e.source) (hxy : DSLe (e x) (e y))
    (hΦ : dsTime (ε • (C.pt : 𝕄)) (e x) = dsTime (ε • (C.pt : 𝕄)) (e y)) :
    -ε * BiSusp.ht x ≤ -ε * BiSusp.ht y ∧ (-ε * BiSusp.ht x = -ε * BiSusp.ht y → x = y) := by
  set q : 𝕄 := ε • (C.pt : 𝕄)
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hq0 : Causal.Flat.minkQ q = 0 := by rw [Causal.Flat.minkQ_smul, hp, mul_zero]
  have hqne : q ≠ 0 := smul_ne_zero hε0 (raySphere_ne_zero C.pt)
  obtain ⟨hxd, hyd, hv⟩ := hxy
  have hB : Causal.Flat.minkB (dsHat (e y) - dsHat (e x)) q = 0 := by
    unfold dsTime at hΦ; rw [Causal.Flat.minkB_sub_left]; linarith
  obtain ⟨c, hc0, hc⟩ := eq_smul_of_minkB_null hq hq0 hqne hv hB
  have hyx : dsHat (e y) = dsHat (e x) + c • q := by rw [← hc]; abel
  have hcB : c * Causal.Flat.minkB (dsHat (e x)) q = 0 := by
    have h1 := minkQ_dsHat hyd
    rw [hyx, Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, hq0, minkQ_dsHat hxd,
      Causal.Flat.minkB_smul_right] at h1
    linarith
  rcases eq_or_lt_of_le hc0 with hc' | hc'
  · -- `c = 0`: the same point
    have hxy' : x = y := by
      have : dsHat (e y) = dsHat (e x) := by rw [hyx, ← hc', zero_smul, add_zero]
      exact e.injOn hx hy ((dsHat_eq_iff hxd hyd).1 this.symm)
    subst hxy'
    exact ⟨le_rfl, fun _ => rfl⟩
  have hBx : Causal.Flat.minkB (dsHat (e x)) q = 0 := (mul_eq_zero.1 hcB).resolve_left hc'.ne'
  obtain ⟨c', W, hW, hl, rfl⟩ := he
  obtain ⟨⟨σ, t⟩, ⟨hσ, ht0, htπ⟩, rfl⟩ := hx
  obtain ⟨⟨σ', t'⟩, ⟨hσ', ht0', htπ'⟩, rfl⟩ := hy
  set p := C.pt
  set w := W σ
  have hw : tpMk p w ≠ 0 := hW.tpMk_ne σ hσ
  have hex : suspChart c' W hW (BiSusp.mk' (σ, t)) = arcPt p w t := rfl
  have hey : suspChart c' W hW (BiSusp.mk' (σ', t')) = arcPt p (W σ') t' := rfl
  rw [hex, hey] at hyx
  rw [hex] at hxd
  set V := arcVec p w (t : ℝ)
  have hV : V ≠ 0 := arcVec_ne_zero p hw t
  have hxc : ((arcPt p w t : HS 2) : 𝕄) = ‖V‖⁻¹ • V := coe_rayNormalize _ hV
  have hQV : 0 < Causal.Flat.minkQ V := by
    have h := (show 0 < Causal.Flat.minkQ ((arcPt p w t : HS 2) : 𝕄) from hxd)
    rw [hxc, Causal.Flat.minkQ_smul] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  set k := (Real.sqrt (Causal.Flat.minkQ V))⁻¹
  have hk : 0 < k := inv_pos.2 (Real.sqrt_pos.2 hQV)
  have hxh : dsHat (arcPt p w t) = k • V := dsHat_of_coe_eq (inv_pos.2 (norm_pos_iff.2 hV)) hxc
  set a : ℝ := k * Real.cos t + c * ε
  set b : ℝ := k * Real.sin t
  have hb : 0 < b := mul_pos hk (Real.sin_pos_of_pos_of_lt_pi ht0 htπ)
  have hyv : dsHat (arcPt p (W σ') t') = a • (p : 𝕄) + b • w := by
    rw [hyx, hxh]; simp only [V, arcVec, a, b, q]; module
  -- `e y` is the ray of `a p + b w`
  have hyr : arcPt p (W σ') t' = rayNormalize p (a • (p : 𝕄) + b • w) := by
    rw [← hyv, dsHat, rayNormalize_smul_of_pos p (raySphere_ne_zero _)
      (inv_pos.2 (Real.sqrt_pos.2 (show 0 < Causal.Flat.minkQ ((arcPt p (W σ') t' : HS 2) : 𝕄)
        from by rw [← hey]; exact hyd))), rayNormalize_raySphere]
  have htpv : tpMk p (a • (p : 𝕄) + b • w) = b • tpMk p w := by
    show Submodule.Quotient.mk _ = _
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    change a • tpMk p (p : 𝕄) + _ = _
    rw [tpMk_self, smul_zero, zero_add]
  have hv0 : a • (p : 𝕄) + b • w ≠ 0 := fun h => by
    rw [h] at htpv
    exact smul_ne_zero hb.ne' hw (htpv.symm.trans (Submodule.Quotient.mk_zero _))
  -- the same segment
  have hσσ : σ' = σ := by
    have h1 : dirOf p (arcPt p (W σ') t' : 𝕄) = c' σ' := by
      rw [dirOf_arcPt p (hW.tpMk_ne σ' hσ') ht0' htπ', hW.dirOf_eq σ' hσ']
    have h2 : dirOf p (arcPt p (W σ') t' : 𝕄) = c' σ := by
      rw [hyr, coe_rayNormalize _ hv0, ← hW.dirOf_eq σ hσ,
        dirOf_smul_of_pos p (by rw [htpv]; exact smul_ne_zero hb.ne' hw)
          (inv_pos.2 (norm_pos_iff.2 hv0))]
      show rayNormalize _ (tpMk p _) = rayNormalize _ (tpMk p _)
      rw [htpv, rayNormalize_smul_of_pos _ hw hb]
    exact c'.injOn hσ' hσ (h1.symm.trans h2)
  subst hσσ
  have ht' : (t' : ℝ) = Complex.arg ((a : ℂ) + (b : ℂ) * Complex.I) := by
    rw [← arcAngle_rayNormalize hw hb, ← hyr, arcAngle_arcPt p hw ht0' htπ']
  have ht : (t : ℝ) = Complex.arg (((k * Real.cos t : ℝ) : ℂ) + (b : ℂ) * Complex.I) := by
    rw [show ((k * Real.cos t : ℝ) : ℂ) + (b : ℂ) * Complex.I =
        (k : ℂ) * (Complex.cos t + Complex.sin t * Complex.I) by simp only [b]; push_cast; ring,
      Complex.arg_real_mul _ hk, Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], htπ.le⟩]
  have hhx : BiSusp.ht (BiSusp.mk' (σ', t)) = t := rfl
  have hhy : BiSusp.ht (BiSusp.mk' (σ', t')) = t' := rfl
  rw [hhx, hhy]
  rcases hε with rfl | rfl
  · have hlt : (t' : ℝ) < t := by
      rw [ht', ht]
      exact arg_add_lt (a := k * Real.cos t) hb (by simpa using hc')
    exact ⟨by linarith, fun h => absurd h (by intro h; linarith)⟩
  · have hlt : (t : ℝ) < t' := by
      rw [ht', ht]
      have := arg_add_lt (a := k * Real.cos t + c * (-1)) (μ := c) hb hc'
      rwa [show k * Real.cos t + c * (-1) + c = k * Real.cos t by ring] at this
    exact ⟨by linarith, fun h => absurd h (by intro h; linarith)⟩

/-- **A light-like `𝔢(L)` has no CCC** (the paper's claim for cuspidal, extreme BTZ-like and
light-like lines of degree `2`, l.1120–1125; it holds at every degree). The lexicographic time
function: `dsTime q`, `q = ±p` future null, then the height `∓t` along the steps parallel to `q`
(`GX.GammaLinkCircle.DevData.ht_step_null`). -/
theorem GammaLinkCircle.DevData.not_hasCCC_of_null (Δ : C.DevData)
    (hp : Causal.Flat.minkQ (C.pt : 𝕄) = 0) : ¬ Δ.suspStructure.HasCCC := by
  obtain ⟨ε, hε, hq⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ Causal.Flat.IsFutureCausal (ε • (C.pt : 𝕄)) := by
    have h1 : (C.pt : 𝕄).1 ≠ 0 := fun h =>
      raySphere_ne_zero C.pt (Causal.Flat.eq_zero_of_fst_eq_zero h hp.le)
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨-1, Or.inr rfl, by simp only [neg_smul, one_smul]; exact ⟨by simp; linarith, by simpa using hp.le⟩⟩
    · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact ⟨h.le, hp.le⟩⟩
  have hfix : ∀ g : GammaP C.pt, ((g : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (ε • (C.pt : 𝕄)) =
      ε • (C.pt : 𝕄) := fun g => by rw [map_smul, g.2]
  refine Δ.suspStructure.not_hasCCC_of_lexTime (dsTime (ε • (C.pt : 𝕄)))
    (fun e he e' he' x hx hx' => ?_) (fun σ τ h => ?_) (fun x => -ε * BiSusp.ht x)
    (fun e he x hx y hy hxy hΦ => Δ.ht_step_null hp hε hq he hx hy hxy hΦ)
  · obtain ⟨g, hg⟩ := Δ.suspAtlas_eventually_eq_smul he he' ⟨hx, hx'⟩
    rw [hg.self_of_nhds, dsTime_smul _ (hfix g)]
  · have hB := Causal.Flat.minkB_le_zero_of_isFutureCausal h.2.2 hq
    rw [Causal.Flat.minkB_sub_left] at hB
    unfold dsTime; linarith

/-- **A space-like `𝔢(L)` other than Misner, of degree `< 4`, has no CCC** (the paper's claim,
l.1120–1125): proved for the BTZ-like types (`not_hasCCC_of_btz`); for tachyons of degree `2` and
for the trivial holonomy `δ²` it rests on two tagged `sorry`s. -/
theorem GammaLinkCircle.DevData.not_hasCCC_of_deSitter (Δ : C.DevData)
    (hp : C.pt ∈ HS.piece 2 .deSitter) (h₁ : C.linkType ≠ .misner)
    (h₂ : ¬ C.linkType.IsHighDegree) : ¬ Δ.suspStructure.HasCCC := by
  have hreg : HS.region C.pt = .deSitter := HS.region_eq_of_mem hp
  have ht := C.hasType_linkType
  generalize hT : C.linkType = T at ht h₁ h₂
  obtain ⟨θ, -, E', D', f, hl, hpt⟩ := ht
  rcases T with ⟨b, a⟩ | _ | _ | _ | b | b | ⟨b, k⟩ | ⟨b, b', k⟩ | k
  · cases b <;> (have := hpt.1; rw [hreg] at this; cases this)
  · obtain ⟨-, -, -, himg⟩ := hpt
    refine Δ.not_hasCCC_of_btz hp (Or.inl rfl) fun s => ?_
    rw [one_smul]
    exact Δ.d_mem_of_image (S := dsFutureDirs C.pt) (fun A σ hσ => (smul_mem_dsFutureDirs_iff C.pt A).2 hσ)
      hl (by rw [himg, iPlus_of_deSitter hp]) s
  · obtain ⟨-, -, -, himg⟩ := hpt
    refine Δ.not_hasCCC_of_btz hp (Or.inr rfl) fun s => ?_
    rw [neg_one_smul]
    exact Δ.d_mem_of_image (S := dsPastDirs C.pt) (fun A σ hσ => (smul_mem_dsPastDirs_iff C.pt A).2 hσ)
      hl (by rw [himg, iMinus_of_deSitter hp]) s
  · exact absurd rfl h₁
  · cases b <;> (have := hpt.1; rw [hreg] at this; cases this)
  · cases b <;> (have := hpt.1; rw [hreg] at this; cases this)
  · sorry -- SORRY(bbsdef:Hcausal): space-like circles of degree k (tachyons, k = 2: the case of the paper): the developed image is all of ℓ(p) (range D = ℝP̃¹), so no region of dS² carries a Γ_p-invariant time function (Γ_p is the boost group of the Lorentzian plane p^⊥; its invariants B(·, p) and B(·, n₊)B(·, n₋) are time functions only on the regions I^±(p), used here for the BTZ-like types); a time function on the de Sitter region of 𝔢(L) must be built through the gluing by the hyperbolic holonomy; the paper gives no argument (l.1120–1125 assert the equivalence; the proof of bbslem:CTC only reduces CCCs of e(Σ) to CCCs of the de Sitter region of Σ), and none is formalized
  · cases b <;> cases b' <;> (have := hpt.1; rw [hreg] at this; cases this)
  · sorry -- SORRY(bbsdef:Hcausal): trivial holonomy δᵏ at p ∈ dS² (k = 2: 𝔢(ℓ(p)) ≅ HS², whose de Sitter region has the time function of HS² itself, not Γ_p-invariant; transporting it needs regular_susp's identification chart by chart); the developed image is all of ℓ(p) and the same obstruction as for tachyons applies; not formalized

/-- No CCC in `𝔢(L)` unless `L` is Misner or of degree `≥ 4`. -/
theorem GammaLinkCircle.DevData.not_hasCCC (Δ : C.DevData) (h₁ : C.linkType ≠ .misner)
    (h₂ : ¬ C.linkType.IsHighDegree) : ¬ Δ.suspStructure.HasCCC := by
  rcases lt_trichotomy (Causal.Flat.minkQ (C.pt : 𝕄)) 0 with h | h | h
  · exact Δ.not_hasCCC_of_timelike h
  · exact Δ.not_hasCCC_of_null h
  · exact Δ.not_hasCCC_of_deSitter h h₁ h₂

/-- The apices of `𝔢(L)` are of degree `< 4` when `L` is. -/
theorem GammaLinkCircle.DevData.not_hasHighDegreeAt (Δ : C.DevData)
    (h₂ : ¬ C.linkType.IsHighDegree) : ∀ x ∈ Δ.suspStructure.sing,
      ¬ Δ.suspStructure.HasHighDegreeAt x := by
  sorry -- SORRY(bbsdef:Hcausal): an apex link of a point of 𝒮 is any (Γ_q, ℓ(q))-circle C' whose 𝔢(C') is HS-isomorphic near p̄' to a neighbourhood of the point; that C' is then isomorphic to L (at p̄) or to its antipodal circle (at −p̄) through a move q ↦ C.pt, and that the degree is invariant under moved isomorphisms, is the developing argument on the punctured neighbourhood left open by HSAntipodal SCOPE (b) (l.850–852, « determine the HS-singular point up to HS-isomorphism »), not formalized

/-- **The « only if » of the « in other words », sorry-free**: a causal singular line is neither
Misner nor of degree `≥ 4`, already when `𝔢(L)` is causal for one developing data. -/
theorem GammaLinkCircle.DevData.not_misner_of_isCausal (Δ : C.DevData)
    (h : Δ.suspStructure.IsCausal) : C.linkType ≠ .misner ∧ ¬ C.linkType.IsHighDegree :=
  ⟨fun hm => h.2 (Δ.hasCCC_of_misner hm), fun hd => Δ.not_isCausal_of_isHighDegree hd h⟩

/-- **No CCC in `𝔢(L)` for the time-like, light-like and BTZ-like types, sorry-free.** -/
theorem GammaLinkCircle.DevData.not_hasCCC_of_type (Δ : C.DevData)
    (h : Causal.Flat.minkQ (C.pt : 𝕄) ≤ 0 ∨ C.linkType = .btzPast ∨ C.linkType = .btzFuture) :
    ¬ Δ.suspStructure.HasCCC := by
  rcases h with h | h | h
  · rcases h.lt_or_eq with h | h
    · exact Δ.not_hasCCC_of_timelike h
    · exact Δ.not_hasCCC_of_null h
  all_goals
    obtain ⟨θ, -, E', D', f, hl, hr, -, -, himg⟩ := C.hasType_iff.2 h
    have hp : C.pt ∈ HS.piece 2 .deSitter := HS.mem_piece_iff_region.2 hr
  · refine Δ.not_hasCCC_of_btz hp (Or.inl rfl) fun s => ?_
    rw [one_smul]
    exact Δ.d_mem_of_image (S := dsFutureDirs C.pt)
      (fun A σ hσ => (smul_mem_dsFutureDirs_iff C.pt A).2 hσ) hl
      (by rw [himg, iPlus_of_deSitter hp]) s
  · refine Δ.not_hasCCC_of_btz hp (Or.inr rfl) fun s => ?_
    rw [neg_one_smul]
    exact Δ.d_mem_of_image (S := dsPastDirs C.pt)
      (fun A σ hσ => (smul_mem_dsPastDirs_iff C.pt A).2 hσ) hl
      (by rw [himg, iMinus_of_deSitter hp]) s

/-- **`bbsdef:Hcausal`, « in other words », for singular lines**: `L` is causal iff it is neither
Misner nor of degree `≥ 4`. -/
theorem GammaLinkCircle.isCausalLine_iff :
    C.IsCausalLine ↔ C.linkType ≠ .misner ∧ ¬ C.linkType.IsHighDegree := by
  obtain ⟨Δ₀⟩ := C.nonempty_devData
  refine ⟨fun h => ⟨fun hm => (h Δ₀).2 (Δ₀.hasCCC_of_misner hm),
    fun hd => Δ₀.not_isCausal_of_isHighDegree hd (h Δ₀)⟩,
    fun ⟨h₁, h₂⟩ Δ => ⟨Δ.not_hasHighDegreeAt h₂, Δ.not_hasCCC h₁ h₂⟩⟩

/-- The same, for some developing data. -/
theorem GammaLinkCircle.isCausalLine_iff_exists :
    (∃ Δ : C.DevData, Δ.suspStructure.IsCausal) ↔
      C.linkType ≠ .misner ∧ ¬ C.linkType.IsHighDegree := by
  refine ⟨fun ⟨Δ, h⟩ => ⟨fun hm => h.2 (Δ.hasCCC_of_misner hm),
    fun hd => Δ.not_isCausal_of_isHighDegree hd h⟩, fun h => ?_⟩
  obtain ⟨Δ₀⟩ := C.nonempty_devData
  exact ⟨Δ₀, isCausalLine_iff.2 h Δ₀⟩

end Main

/-! ## 9. The « in other words » read for arbitrary (non-compact) singular HS-surfaces -/

namespace SingularHSStructure

variable {M : Type*} [TopologicalSpace M] {A : SingularHSStructure M}

/-- A causal curve stays in the regular part `Σ ∖ 𝒮`. -/
theorem IsFutureCausalCurve.notMem_sing {γ : ℝ → M} (h : A.IsFutureCausalCurve γ) (s : ℝ) :
    γ s ∉ A.sing := by
  obtain ⟨e, he, ε, hε, h'⟩ := h.2 s
  have : γ s ∈ support A.atlas := mem_support.2 ⟨e, he, (h' s ⟨by linarith, by linarith⟩).1⟩
  rwa [A.support_eq] at this

/-- **A CCC of `Σ` is a CCC of its regular part** `Σ ∖ 𝒮`, a singular HS-surface without singular
points. -/
theorem HasCCC.restrict_reg (h : A.HasCCC) : (A.restrictTo A.regOpens).HasCCC := by
  obtain ⟨γ, ⟨hc, hγ⟩, hper, s₁, s₂, hne⟩ := h
  have hreg : ∀ s, γ s ∈ A.regOpens := fun s => IsFutureCausalCurve.notMem_sing ⟨hc, hγ⟩ s
  refine ⟨fun s => ⟨γ s, hreg s⟩, ⟨hc.subtype_mk _, fun s => ?_⟩, fun s => ?_,
    s₁, s₂, fun h' => hne (congrArg Subtype.val h')⟩
  · obtain ⟨e, he, ε, hε, h'⟩ := hγ s
    refine ⟨e.subtypeRestr ⟨⟨γ s, hreg s⟩⟩, ⟨e, he, _, rfl⟩, ε, hε, fun a ha => ⟨?_, fun b hb hab => ?_⟩⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]; exact (h' a ha).1
    · exact (h' a ha).2 b hb hab
  · exact Subtype.ext (hper s)

theorem sing_restrictTo_reg (A : SingularHSStructure M) :
    (A.restrictTo A.regOpens).sing = ∅ :=
  eq_empty_of_forall_notMem fun x hx => x.2 hx

end SingularHSStructure

/-- **The « in other words » of l.1120–1125 fails for singular HS-surfaces in general**: there is a
singular HS-surface with no singular point at all (so no singularity of degree `≥ 4` and no Misner
singularity) which has a closed causal curve, hence is not causal. It is the regular part
`𝔢(L) ∖ {p̄, −p̄}` of a Misner `𝔢(L)` (an annulus). -/
theorem exists_isSingularHSSurface_sing_empty_hasCCC :
    ∃ (M : Type) (_ : TopologicalSpace M) (A : SingularHSStructure M),
      IsSingularHSSurface M A ∧ A.sing = ∅ ∧ A.HasCCC ∧ ¬ A.IsCausal := by
  obtain ⟨L, _, C, -, hm⟩ :=
    (exists_hasType_listed.1 _ (HS.base_mem (by norm_num : 1 ≤ 2) .deSitter)).1
  obtain ⟨Δ⟩ := C.nonempty_devData
  set A := Δ.suspStructure
  have he := A.sing_restrictTo_reg
  have hc : (A.restrictTo A.regOpens).HasCCC :=
    (Δ.hasCCC_of_misner (C.hasType_iff.1 hm)).restrict_reg
  refine ⟨A.regOpens, inferInstance, A.restrictTo A.regOpens, ⟨?_, ?_, ?_⟩, he, hc,
    fun h => h.2 hc⟩
  · exact C.isTopologicalSurface_susp.ofOpens _
  · rw [he]; infer_instance
  · intro x hx; rw [he] at hx; exact absurd hx (notMem_empty x)

end GX
