import GX.BBS.HSSuspension
import GX.BBS.PhotonCircles
import GXScaffold.BBS.HSSingularities

/-!
# BBS § 3.3: the two apices of `𝔢(L)` (`bbsrem:p_p`): the link at `−p̄`, its type, and the space-like sentence, false for Misner singularities and true for every other link

Target `T-bbs-p-p` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx). `papers/bbs/legacy/labeled/colI_v1.tex`.
Imports the strict `GX.BBS.HSSuspension` (`𝔢(L)`) and `GX.BBS.PhotonCircles` (`vol3`), and
`GXScaffold.BBS.HSSingularities` (the lifted developing pairs and the types of the links).

* `bbsrem:p_p` — `colI_v1.tex:934` — partial (unmarked: the space-like sentence, l.936–937, is
  false as printed for Misner singularities, in the reading of « isomorphic » taken here, OQ-120 (a),
  and true for every other space-like link; every other sentence is proved): the assembly
  `GX.GammaLinkCircle.bbsrem_p_p`; the link at `−p̄` `GX.GammaLinkCircle.DevData.isIso_flip`; the
  space-like sentence in its strongest true form `GX.GammaLinkCircle.IsLiftedDev.isIsoVia_antipode_iff`
  (isomorphic through a move iff not Misner); the counterexample
  `GX.exists_misner_not_isIsoVia_antipode`.

> Let $L$ be a $(\Gamma_p, \ell(p))$-circle. The suspension $\mathfrak{e}(L)$ admits two singular
> points $\bar{p}$, $-\bar{p}$, corresponding to $p$ and $-p$. Observe that when $p$ is
> space-like, $\bar{p}$ and $-\bar{p}$, as HS-singularities, are always isomorphic. When $p$ is
> time-like, one of the singularities is future time-like and the other is past time-like. If
> $\bar{p}$ is a future light-like singularity of degree $k \geq 1$, then $-\bar{p}$ is a
> \textit{past} light-like singularity of degree $k$, and \textit{vice versa}.
> Finally, if $\bar{p}$ is a future cuspidal singularity, then $-\bar{p}$ is a past extreme
> BTZ-like singularity. (l.935–942)

## Main declarations (all proved, 0 `sorry`)

* **`Γ_{−p} = Γ_p` and the antipodal circle.** `GX.gammaP_neg`; `T_p HS² = T_{−p} HS²` isometrically
  (`GX.tpNeg`), `GX.linkNeg : ℓ(p) ≃ₜ ℓ(−p)`, `Γ_p`-equivariant (`GX.linkNeg_smul`). The antipodal
  circle `GX.GammaLinkCircle.antipode L` (charts of `L` followed by `linkNeg`, a
  `(Γ_{−p}, ℓ(−p))`-circle on the same space) and its developing data
  `GX.GammaLinkCircle.DevData.antipode` (the same covering and the same lift `w`).
* **The link at `−p̄`.** The flip `GX.BiSusp.flip : [σ, t] ↦ [σ, π − t]` is an HS-isomorphism
  `𝔢(L) ≅ 𝔢(L⁻)`, reading as the identity of `HS²` in the cone charts
  (`GX.GammaLinkCircle.DevData.isIso_flip`, from `cos(π − t)(−p) + sin(π − t) w = cos t p + sin t w`,
  `GX.arcPt_negPt`), with `−p̄ ↦ p̄⁻` (`GX.GammaLinkCircle.flip_south_north`).
* **The types at `−p̄`.** Positions (`GX.GammaLinkCircle.antipode_timelike`, `…antipode_lightlike_pos`).
  The oriented identification at `−p` is `GX.tangentNeg` (`T_p = T_{−p}` reverses the orientations,
  complex conjugation restores it, `GX.isOrientedTangent_tangentNeg`); then
  `linkCover_{−p}(t) = linkNeg(linkCover_p(−t))` (`GX.linkCover_tangentNeg`) and the lifted
  developing pair of `L⁻` is `(E(−·), −D(−·), mirror f⁻¹)` (`GX.GammaLinkCircle.IsLiftedDev.antipode`),
  `GX.GTilde.mirror f = (x ↦ −f(−x))` the reflection of `ℝP̃¹`. Degree kept and well defined
  (`…antipode_degree`, `…degree_unique`); light-like images exchanged (`…antipode_bdPlus_image`,
  `…antipode_bdMinus_image`); **cuspidal ↦ extreme BTZ-like past**
  (`GX.GammaLinkCircle.IsLiftedDev.antipode_cuspidal`); space-like images kept
  (`…antipode_deSitter_image`), signs kept (`…IsSpacelikePositive.antipode`,
  `…IsSpacelikeNegative.antipode`, `…IsLightlikePositive.antipode`, `…IsLightlikeNegative.antipode`).
* **Moved-`p` isomorphisms and chirality.** `GX.GammaLinkCircle.IsIsoVia` (through `B ∈ SO₀(1,2)`,
  `B • p = p'`, via `GX.linkMove`); the chirality `GX.chirality p σ = vol3 p (π_p σ) e_t` of a
  space-like direction: its sign does not depend on the future time-like vector
  (`GX.vol3_pos_iff_of_spacelike`, through the Lorentzian cross product `GX.lcross`), `linkNeg`
  reverses it (`GX.chirality_linkNeg`), a move followed by `Γ_{−p}` keeps it
  (`GX.chirality_smul_linkMove_pos_iff`). Hence **a Misner link is isomorphic to its antipodal link
  through no move** (`GX.GammaLinkCircle.IsLiftedDev.not_isIsoVia_antipode`); Misner links exist at
  every `p ∈ dS²` (`GX.exists_misner`), moves `p ↦ −p` exist (`GX.exists_smul_eq_neg`), and the
  notion is not empty (`GX.regular_isIsoVia_antipode`).
* **A move `p ↦ −p` conjugates `Γ_p` by inversion.** At `p ∈ dS²`, every `N ∈ SO₀(1,2)` with
  `N p = −p` is an involution (`GX.mul_self_eq_one_of_apply_neg`: on `T_p HS²`, `[N]` reverses the
  area, `GX.linkArea_tpReflect`, and keeps `Q ∘ π_p`, so it exchanges the two light-like lines and
  squares to `1`), hence `B ρ B⁻¹ = ρ⁻¹` for `ρ ∈ Γ_p` (`GX.conj_eq_inv_of_neg`).
* **Every non-Misner link is isomorphic to its antipodal link, through every move**
  (`GX.GammaLinkCircle.IsLiftedDev.exists_isIsoVia_antipode`). The reflection
  `GX.linkReflect B = ℓ(−p)^{-1} ∘ B` of `ℓ(p)` conjugates `ρ` to `ρ⁻¹` (`GX.linkReflect_smul`) and
  keeps `i^±` (`GX.linkReflect_mem_dsFutureDirs`, `…_dsPastDirs`); through the oriented
  identification `GX.tangentMove` it lifts to `t ↦ −F t`, `F ∈ G̃` (`GX.exists_linkReflect_linkCover`);
  `−F ∘ f = f⁻¹ ∘ −F` (both lift `ρ⁻¹`, and agree on a light-like lift); `−F − 2j` maps the developed
  interval onto itself (`D` onto at degree `≠ 0`; at degree `0`, BTZ-like, the developed interval
  and its image are open intervals between consecutive light-like lifts, `GX.Ioo_eq_of_ends`); and
  `D⁻¹ ∘ (−F − 2j) ∘ D` descends to `L`. With the Misner half: **the links of `p̄` and `−p̄` are
  isomorphic through a move iff `L` is not Misner** (`GX.GammaLinkCircle.IsLiftedDev.isIsoVia_antipode_iff`).

## Hypothesis checklist

| BBS | here |
|---|---|
| « a `(Γ_p, ℓ(p))`-circle `L` » (l.935) | ✓ `GX.GammaLinkCircle`, any `p ∈ HS²`; `𝔢(L)` for any developing data `Δ` (OQ-126 (c)) |
| « two singular points corresponding to `p` and `−p` » (l.935–936) | ✓ the apices of `GX.BiSusp L`; the singularity at `−p̄` is the one of `L⁻` (`isIso_flip`); « singular » is not claimed (they are regular for `L = ℓ(p)`, HSSuspension's finding) |
| « as HS-singularities, isomorphic » (l.937) | ⚠ reading (OQ-120 (a), moved `p`): the links are isomorphic through a `B ∈ SO₀(1,2)`, `B p = −p` (`IsIsoVia`); the singularity is determined by its link (l.850–852, argued, not formalized) |
| « future / past time-like » (l.938–939) | ✓ `p ∈ ℍ²₊` / `ℍ²₋` |
| « future light-like of degree `k ≥ 1` » (l.939–940) | ⚠ weakened: `p ∈ ∂ℍ²₊` and an oriented lifted holonomy `δᵏ g`, `g` with a fixed point; `k ≥ 1` not used (every `k`) |
| « future cuspidal », « past extreme BTZ-like » (l.941–942) | ⚠ the two degree-`0` cases of `bdPlus_degree_zero` / `bdMinus_degree_zero` (HSSingularities), the extreme BTZ-like image being `i^± ∖ T` (OQ-116 (b)) |
| « always isomorphic » for space-like `p` (l.937) | ✗ false for Misner singularities (`exists_misner_not_isIsoVia_antipode`), ✓ for every other link, through every move (`exists_isIsoVia_antipode`); exactly `isIsoVia_antipode_iff`; the types are kept |

## SCOPE (disclosed)

* **(a) The space-like sentence (l.936–937) is false as printed** for Misner singularities (l.876–878):
  the chirality of the developed space-like arc is reversed at `−p̄` and kept by every move, so the
  links of `p̄` and `−p̄` are isomorphic through no `B ∈ SO₀(1,2)` with `B p = −p`. The two
  apices of a Misner `𝔢(L)` are both Misner, of opposite chiralities. For every other space-like
  link (BTZ-like past/future, or of degree `k ≠ 0`) the sentence holds, through every move
  (`isIsoVia_antipode_iff`). The type is kept in all cases (BTZ-like past/future, Misner,
  positive/negative of degree `k`, the degree).
* **(b) Not formalized:** that an HS-isomorphism of the singularities `p̄`, `−p̄` of `𝔢(L)` induces
  a moved-`p` isomorphism of their links (the developing argument on the punctured neighbourhood;
  with it the counterexample holds for HS-singularities, argued), and conversely that a moved-`p`
  isomorphism of the links induces one of the singularities (l.850–852, « determine … the
  HS-singular point up to HS-isomorphism », argued); the Δ-independence of `𝔢(L)` (OQ-126 (c)).
* **(c) Readings carried:** OQ-104 and OQ-126 (`𝔢(L)`, `IsSingularHSStructure.IsIso`), OQ-113
  (orientations: `HS²` outward normal first, `θ` oriented; `tangentNeg` is the oriented choice at
  `−p`), OQ-116 (a) (time-like `i^±` at `dS²`; the Misner image is a space-like open arc) and (b)
  (`i^± ∖ T` at `∂ℍ²±`), OQ-120 (a) (isomorphisms with a moving point: `IsIsoVia`), OQ-120 (c) and
  OQ-124 (positive/negative in the l.915 form, `IsSpacelikePositive`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. `Γ_{−p} = Γ_p` and `T_p HS² = T_{−p} HS²` -/

section Neg

variable (p : HS 2)

theorem coe_neg_hs : ((-p : HS 2) : 𝕄) = -(p : 𝕄) := coe_neg_sphere p

/-- `ℝ(−p) = ℝp`. -/
theorem span_neg_hs : (ℝ ∙ ((-p : HS 2) : 𝕄)) = (ℝ ∙ (p : 𝕄)) := by
  rw [coe_neg_hs, ← Set.neg_singleton, Submodule.span_neg]

/-- **`T_p HS² = T_{−p} HS²`**: both are `ℝ^{1,2}/ℝp`. -/
def tpNeg : TpHS p ≃ₗ[ℝ] TpHS (-p) :=
  Submodule.quotEquivOfEq _ _ (span_neg_hs p).symm

theorem tpNeg_mk (w : 𝕄) : tpNeg p (tpMk p w) = tpMk (-p) w := rfl

theorem norm_quotEquivOfEq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {S S' : Submodule ℝ V} (h : S = S') (x : V ⧸ S) :
    ‖Submodule.quotEquivOfEq S S' h x‖ = ‖x‖ := by
  subst h
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

/-- `T_p HS² = T_{−p} HS²` is an isometry (the same quotient). -/
theorem norm_tpNeg (x : TpHS p) : ‖tpNeg p x‖ = ‖x‖ :=
  norm_quotEquivOfEq _ x

/-- **`ℓ(p) ≅ ℓ(−p)`**: a direction at `p` is a direction at `−p`. -/
def linkNeg : Link p ≃ₜ Link (-p) := raySphereHomeomorph (tpNeg p)

theorem coe_linkNeg (σ : Link p) : ((linkNeg p σ : Link (-p)) : TpHS (-p)) = tpNeg p σ := by
  show ‖tpNeg p σ‖⁻¹ • tpNeg p σ = tpNeg p σ
  rw [norm_tpNeg, norm_raySphere, inv_one, one_smul]

/-- **`Γ_{−p} = Γ_p`** (l.935, « corresponding to `p` and `−p` »): fixing `p` is fixing `−p`. -/
theorem gammaP_neg : GammaP (-p) = GammaP p := by
  ext A
  show (A : 𝕄 ≃ₗ[ℝ] 𝕄) ((-p : HS 2) : 𝕄) = ((-p : HS 2) : 𝕄) ↔ (A : 𝕄 ≃ₗ[ℝ] 𝕄) p = p
  rw [coe_neg_hs, map_neg, neg_inj]

/-- `Γ_p ≃ Γ_{−p}`, the identity of `SO₀(1,2)`. -/
def gammaNeg : GammaP p ≃* GammaP (-p) := MulEquiv.subgroupCongr (gammaP_neg p).symm

@[simp] theorem coe_gammaNeg (A : GammaP p) :
    ((gammaNeg p A : GammaP (-p)) : Causal.Flat.lorentz 2) = A := rfl

@[simp] theorem coe_gammaNeg_symm (A : GammaP (-p)) :
    (((gammaNeg p).symm A : GammaP p) : Causal.Flat.lorentz 2) = A := rfl

theorem tpNeg_tangent (A : GammaP p) (z : TpHS p) :
    tpNeg p (GammaP.tangent A z) = GammaP.tangent (gammaNeg p A) (tpNeg p z) := by
  induction z using Submodule.Quotient.induction_on with
  | H v => rfl

/-- `ℓ(p) ≅ ℓ(−p)` is `Γ_p`-equivariant. -/
theorem linkNeg_smul (A : GammaP p) (σ : Link p) :
    linkNeg p (A • σ) = gammaNeg p A • linkNeg p σ := by
  apply Subtype.ext
  rw [coe_linkNeg, gammaP_smul_def, gammaP_smul_def, coe_linRaySmul, coe_linRaySmul,
    coe_linkNeg, map_smul, tpNeg_tangent, ← tpNeg_tangent, norm_tpNeg]

theorem tpMk_neg_ne_zero_iff {w : 𝕄} : tpMk (-p) w ≠ 0 ↔ tpMk p w ≠ 0 := by
  rw [← tpNeg_mk, LinearEquiv.map_ne_zero_iff]

/-- The direction of `w` at `−p` is its direction at `p`. -/
theorem dirOf_negPt {w : 𝕄} (hw : tpMk p w ≠ 0) : dirOf (-p) w = linkNeg p (dirOf p w) := by
  apply Subtype.ext
  rw [coe_linkNeg, coe_dirOf p hw, coe_dirOf (-p) ((tpMk_neg_ne_zero_iff p).2 hw), map_smul,
    ← tpNeg_mk, norm_tpNeg]

/-- `p^⊥` is `(−p)^⊥`, and the projections agree. -/
theorem perpLin_neg (w : 𝕄) : perpLin (-p) w = perpLin p w := by
  rw [perpLin_apply, perpLin_apply, coe_neg_hs, Causal.Flat.minkQ_neg,
    Causal.Flat.minkB_neg_left, neg_smul, smul_neg, neg_neg]

theorem dsProj_tpNeg (z : TpHS p) : dsProj (-p) (tpNeg p z) = dsProj p z := by
  induction z using Submodule.Quotient.induction_on with
  | H v => exact perpLin_neg p v

theorem nullPairing_tpNeg (z : TpHS p) : nullPairing (-p) (tpNeg p z) = -nullPairing p z := by
  by_cases hQ : Causal.Flat.minkQ (p : 𝕄) = 0
  · have hQ' : Causal.Flat.minkQ ((-p : HS 2) : 𝕄) = 0 := by
      rw [coe_neg_hs, Causal.Flat.minkQ_neg, hQ]
    induction z using Submodule.Quotient.induction_on with
    | H v =>
      show nullPairing (-p) (tpMk (-p) v) = -nullPairing p (tpMk p v)
      rw [nullPairing_mk _ hQ', nullPairing_mk _ hQ, coe_neg_hs, Causal.Flat.minkB_neg_left]
  · have hQ' : ¬ Causal.Flat.minkQ ((-p : HS 2) : 𝕄) = 0 := by
      rw [coe_neg_hs, Causal.Flat.minkQ_neg]; exact hQ
    rw [nullPairing, dif_neg hQ', nullPairing, dif_neg hQ]
    simp

end Neg

/-! ## 2. The antipodal circle: the link at `−p̄` -/

section Antipode

variable {L : Type*} [TopologicalSpace L]

/-- `ℓ(−p)` charted over `ℓ(p)` by the single chart `ℓ(p) ≅ ℓ(−p)`. -/
@[reducible] def linkNegChartedSpace (p : HS 2) : ChartedSpace (Link (-p)) (Link p) :=
  (linkNeg p).toOpenPartialHomeomorph.singletonChartedSpace (by simp)

theorem linkNeg_chart_eq (p : HS 2) :
    ∀ c ∈ @ChartedSpace.atlas (Link (-p)) _ (Link p) _ (linkNegChartedSpace p), ⇑c = linkNeg p := by
  rintro c rfl
  rfl

/-- **The antipodal circle** (l.935–936): the `(Γ_{−p}, ℓ(−p))`-circle with the charts of `L`
followed by `ℓ(p) ≅ ℓ(−p)`. It is the link of `𝔢(L)` at `−p̄`
(`GX.GammaLinkCircle.DevData.isIso_flip`). -/
def GammaLinkCircle.antipode (C : GammaLinkCircle L) : GammaLinkCircle L where
  pt := -C.pt
  atlas := @ChartedSpace.comp (Link (-C.pt)) _ (Link C.pt) _ L _ (linkNegChartedSpace C.pt) C.atlas
  hasGroupoid :=
    @hasGroupoid_comp_of_equivariant (GammaP C.pt) (GammaP (-C.pt)) (Link C.pt) (Link (-C.pt)) L
      _ _ _ _ _ _ _ _ _ C.atlas C.hasGroupoid (linkNegChartedSpace C.pt) (linkNeg C.pt)
      (linkNeg_chart_eq C.pt) (gammaNeg C.pt) (linkNeg_smul C.pt)
  isCircle := C.isCircle

@[simp] theorem GammaLinkCircle.antipode_pt (C : GammaLinkCircle L) : C.antipode.pt = -C.pt := rfl

theorem GammaLinkCircle.antipode_chartAt (C : GammaLinkCircle L) (x y : L) :
    @chartAt (Link C.antipode.pt) _ L _ C.antipode.atlas x y =
      linkNeg C.pt (@chartAt (Link C.pt) _ L _ C.atlas x y) := rfl

/-- A developing map of `C`, followed by `ℓ(p) ≅ ℓ(−p)`, is a developing map of the antipodal
circle. -/
theorem GammaLinkCircle.IsDevAlong.antipode {C : GammaLinkCircle L} {M : Type*} [TopologicalSpace M]
    {E : M → L} {d : M → Link C.pt} (hd : C.IsDevAlong E d) :
    C.antipode.IsDevAlong E (linkNeg C.pt ∘ d) := fun s => by
  obtain ⟨A, hA⟩ := hd s
  refine ⟨gammaNeg C.pt A, hA.mono fun s' hs' => ?_⟩
  show linkNeg C.pt (d s') = _
  rw [C.antipode_chartAt, hs', linkNeg_smul]
  rfl

/-- **The developing data of the antipodal circle**: the same covering and the same lift
`w : ℝ → ℝ^{1,2}`, read at `−p`. -/
def GammaLinkCircle.DevData.antipode {C : GammaLinkCircle L} (Δ : C.DevData) :
    C.antipode.DevData where
  E := Δ.E
  periodic := Δ.periodic
  d := linkNeg C.pt ∘ Δ.d
  dev := Δ.dev.antipode
  hol := gammaNeg C.pt Δ.hol
  d_add_one s := by
    show linkNeg C.pt (Δ.d (s + 1)) = _
    rw [Δ.d_add_one, linkNeg_smul]; rfl
  vlift := Δ.vlift
  continuous_vlift := Δ.continuous_vlift
  tpMk_vlift_ne s := (tpMk_neg_ne_zero_iff C.pt).2 (Δ.tpMk_vlift_ne s)
  dirOf_vlift s := by
    show dirOf (-C.pt) (Δ.vlift s) = linkNeg C.pt (Δ.d s)
    rw [dirOf_negPt C.pt (Δ.tpMk_vlift_ne s), Δ.dirOf_vlift]
  vlift_add_one s := Δ.vlift_add_one s

end Antipode

/-! ## 3. The flip `[σ, t] ↦ [σ, π − t]` of `𝔢(L)` -/

section Flip

variable {S : Type*} [TopologicalSpace S]

/-- `t ↦ π − t` on `[0, π]`. -/
def iccFlip (t : Icc (0 : ℝ) Real.pi) : Icc (0 : ℝ) Real.pi :=
  ⟨Real.pi - t, by linarith [t.2.2], by linarith [t.2.1]⟩

@[simp] theorem coe_iccFlip (t : Icc (0 : ℝ) Real.pi) : (iccFlip t : ℝ) = Real.pi - t := rfl

theorem iccFlip_iccFlip (t : Icc (0 : ℝ) Real.pi) : iccFlip (iccFlip t) = t :=
  Subtype.ext (by simp)

theorem continuous_iccFlip : Continuous iccFlip :=
  (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- The flip on `S × [0, π]`. -/
def flipFun (q : S × Icc (0 : ℝ) Real.pi) : S × Icc (0 : ℝ) Real.pi := (q.1, iccFlip q.2)

theorem continuous_flipFun : Continuous (flipFun : S × Icc (0 : ℝ) Real.pi → _) :=
  continuous_fst.prodMk (continuous_iccFlip.comp continuous_snd)

theorem flipFun_rel {a b : S × Icc (0 : ℝ) Real.pi} (h : (biSuspSetoid S).r a b) :
    (biSuspSetoid S).r (flipFun a) (flipFun b) := by
  rcases h with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl rfl
  · refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> simp [flipFun, h1, h2]
  · refine Or.inr (Or.inl ⟨?_, ?_⟩) <;> simp [flipFun, h1, h2]

/-- The flip of the two-apex suspension, as a map. -/
def BiSusp.flipMap : BiSusp S → BiSusp S :=
  Quotient.map flipFun fun _ _ h => flipFun_rel h

theorem BiSusp.flipMap_mk (σ : S) (t : Icc (0 : ℝ) Real.pi) :
    flipMap (mk σ t) = mk σ (iccFlip t) := rfl

theorem BiSusp.flipMap_mk' (q : S × Icc (0 : ℝ) Real.pi) : flipMap (mk' q) = mk' (flipFun q) := rfl

theorem BiSusp.flipMap_flipMap (x : BiSusp S) : flipMap (flipMap x) = x := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  rw [flipMap_mk, flipMap_mk, iccFlip_iccFlip]

theorem BiSusp.continuous_flipMap : Continuous (flipMap : BiSusp S → BiSusp S) :=
  continuous_quot_lift _ (continuous_quot_mk.comp continuous_flipFun)

/-- **The flip `[σ, t] ↦ [σ, π − t]`**, an involutive homeomorphism of `S × [0, π]/∼` exchanging
the two apices. -/
def BiSusp.flip : BiSusp S ≃ₜ BiSusp S where
  toFun := flipMap
  invFun := flipMap
  left_inv := flipMap_flipMap
  right_inv := flipMap_flipMap
  continuous_toFun := continuous_flipMap
  continuous_invFun := continuous_flipMap

theorem BiSusp.flip_mk (σ : S) (t : Icc (0 : ℝ) Real.pi) : flip (mk σ t) = mk σ (iccFlip t) := rfl

theorem BiSusp.ht_flip (x : BiSusp S) : ht (flip x) = Real.pi - ht x := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  rw [flip_mk, ht_mk, ht_mk, coe_iccFlip]

theorem BiSusp.flip_north [Nonempty S] : flip (north S) = south S := by
  show mk _ (iccFlip _) = mk _ _
  rw [mk_eq_mk]
  exact Or.inr (Or.inr ⟨by simp, rfl⟩)

theorem BiSusp.flip_south [Nonempty S] : flip (south S) = north S := by
  show mk _ (iccFlip _) = mk _ _
  rw [mk_eq_mk]
  exact Or.inr (Or.inl ⟨by simp, rfl⟩)

theorem BiSusp.flip_mem_poles_iff (x : BiSusp S) : flip x ∈ poles S ↔ x ∈ poles S := by
  show ht (flip x) = 0 ∨ ht (flip x) = Real.pi ↔ ht x = 0 ∨ ht x = Real.pi
  rw [ht_flip]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by rw [h, sub_zero])
    · exact Or.inl (by rw [h, sub_self])

theorem BiSusp.flipFun_mem_regSet {U : Set S} {q : S × Icc (0 : ℝ) Real.pi}
    (hq : q ∈ regSet U) : flipFun q ∈ regSet U :=
  ⟨hq.1, by show 0 < Real.pi - (q.2 : ℝ); linarith [hq.2.2],
    by show Real.pi - (q.2 : ℝ) < Real.pi; linarith [hq.2.1]⟩

end Flip

/-! ## 4. The link at `−p̄`: the flip is an HS-isomorphism `𝔢(L) ≅ 𝔢(L⁻)` -/

section FlipIso

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- The segment from `−p` through `w`, at angle `π − t`, is the segment from `p` through `w`, at
angle `t`: `cos(π − t)(−p) + sin(π − t) w = cos t p + sin t w`. -/
theorem arcPt_negPt (p : HS 2) {w : 𝕄} (hw : tpMk p w ≠ 0) (t : ℝ) :
    arcPt (-p) w (Real.pi - t) = arcPt p w t := by
  have hv : arcVec (-p) w (Real.pi - t) = arcVec p w t := by
    rw [arcVec, arcVec, coe_neg_hs, Real.cos_pi_sub, Real.sin_pi_sub, neg_smul, smul_neg, neg_neg]
  apply Subtype.ext
  rw [arcPt, arcPt, hv, coe_rayNormalize _ (arcVec_ne_zero p hw t),
    coe_rayNormalize _ (arcVec_ne_zero p hw t)]

/-- A cone lift over a chart of `ℓ(−p)` is a cone lift over the corresponding chart of `ℓ(p)`. -/
theorem isConeLift_negPt {p : HS 2} {c : OpenPartialHomeomorph L (Link (-p))} {W : L → 𝕄}
    (hW : IsConeLift c W) : IsConeLift (c.trans (linkNeg p).symm.toOpenPartialHomeomorph) W where
  continuousOn := hW.continuousOn.mono inter_subset_left
  tpMk_ne σ hσ := (tpMk_neg_ne_zero_iff p).1 (hW.tpMk_ne σ hσ.1)
  dirOf_eq σ hσ := by
    show dirOf p (W σ) = (linkNeg p).symm (c σ)
    rw [← hW.dirOf_eq σ hσ.1, dirOf_negPt p ((tpMk_neg_ne_zero_iff p).1 (hW.tpMk_ne σ hσ.1)),
      Homeomorph.symm_apply_apply]

theorem GammaLinkCircle.DevData.isLiftOf_of_antipode (Δ : C.DevData)
    {c : OpenPartialHomeomorph L (Link (-C.pt))} {W : L → 𝕄} (hl : Δ.antipode.IsLiftOf c W) :
    Δ.IsLiftOf (c.trans (linkNeg C.pt).symm.toOpenPartialHomeomorph) W := by
  intro σ hσ
  obtain ⟨s, hs, A, hA⟩ := hl σ hσ.1
  exact ⟨s, hs, (gammaNeg C.pt).symm A, hA⟩

/-- **The link at `−p̄` is the antipodal circle** (`colI_v1.tex:935–936`, « two singular points
`p̄`, `−p̄`, corresponding to `p` and `−p` »): the flip `[σ, t] ↦ [σ, π − t]` is an HS-isomorphism
from `𝔢(L)` onto `𝔢(L⁻)`, `L⁻ = GX.GammaLinkCircle.antipode L` (a `(Γ_{−p}, ℓ(−p))`-circle,
`Γ_{−p} = Γ_p`), which reads as the identity of `HS²` in the cone charts. It sends `−p̄` to the apex
`p̄⁻` of `𝔢(L⁻)` (`GX.BiSusp.flip_south`): the singularity `−p̄` of `𝔢(L)` is the singularity of
`𝔢(L⁻)` at its apex over `−p`. -/
theorem GammaLinkCircle.DevData.isIso_flip (Δ : C.DevData) :
    Δ.suspStructure.IsIso Δ.antipode.suspStructure (BiSusp.flip (S := L)).toOpenPartialHomeomorph := by
  refine ⟨fun x _ => BiSusp.flip_mem_poles_iff x, fun x _ _ e he hxe e' he' hxe' => ?_⟩
  obtain ⟨c', W', hW', hl', rfl⟩ := he'
  have hW'' : IsConeLift (c'.trans (linkNeg C.pt).symm.toOpenPartialHomeomorph) W' :=
    isConeLift_negPt hW'
  have hχ : suspChart _ W' hW'' ∈ Δ.suspAtlas := ⟨_, W', hW'', Δ.isLiftOf_of_antipode hl', rfl⟩
  obtain ⟨q, hq, hqx⟩ := hxe'
  have hxq : x = BiSusp.mk' (flipFun q) := by
    rw [← BiSusp.flipMap_mk', ← BiSusp.flipMap_flipMap x]
    exact congrArg BiSusp.flipMap hqx.symm
  have hx'' : x ∈ (suspChart _ W' hW'').source :=
    ⟨flipFun q, BiSusp.flipFun_mem_regSet (U := (c'.trans _).source) ⟨⟨hq.1, trivial⟩, hq.2⟩,
      hxq.symm⟩
  obtain ⟨g, hg⟩ := Δ.suspAtlas_eventually_eq_smul he hχ ⟨hxe, hx''⟩
  refine ⟨(g : Causal.Flat.lorentz 2), ?_⟩
  filter_upwards [hg, (suspChart _ W' hW'').open_source.mem_nhds hx''] with y hy hys
  rw [← hy]
  obtain ⟨r, hr, rfl⟩ := hys
  show suspMap (-C.pt) W' (BiSusp.flipMap (BiSusp.mk' r)) = suspMap C.pt W' (BiSusp.mk' r)
  rw [BiSusp.flipMap_mk']
  exact arcPt_negPt C.pt (hW''.tpMk_ne r.1 hr.1) r.2

/-- The flip sends the apex `−p̄` of `𝔢(L)` to the apex `p̄⁻` of `𝔢(L⁻)`, and `p̄` to `−p̄⁻`. -/
theorem GammaLinkCircle.flip_south_north (C : GammaLinkCircle L) :
    haveI := C.nonempty
    BiSusp.flip (BiSusp.south L) = BiSusp.north L ∧ BiSusp.flip (BiSusp.north L) = BiSusp.south L := by
  haveI := C.nonempty
  exact ⟨BiSusp.flip_south, BiSusp.flip_north⟩

end FlipIso

/-! ## 5. The positions of `p` and `−p` -/

section Positions

theorem neg_mem_hypPlus_iff' {σ : HS 2} : -σ ∈ HS.piece 2 .hypPlus ↔ σ ∈ HS.piece 2 .hypMinus := by
  rw [← HS.neg_mem_hypMinus_iff, neg_neg]

theorem neg_mem_bdPlus_iff' {σ : HS 2} : -σ ∈ HS.piece 2 .bdPlus ↔ σ ∈ HS.piece 2 .bdMinus := by
  rw [← HS.neg_mem_bdMinus_iff, neg_neg]

theorem neg_mem_deSitter_iff' {σ : HS 2} : -σ ∈ HS.piece 2 .deSitter ↔ σ ∈ HS.piece 2 .deSitter := by
  show 0 < Causal.Flat.minkQ ((-σ : HS 2) : 𝕄) ↔ 0 < Causal.Flat.minkQ (σ : 𝕄)
  rw [coe_neg_hs, Causal.Flat.minkQ_neg]

end Positions

/-! ## 6. The mirror `x ↦ −f(−x)` of `G̃` -/

section Mirror

namespace RP1

open ComplexConjugate

theorem mk_conj (z : ℂ) : mk (conj z) = (mk z)⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, map_zero, mk, dif_pos rfl, inv_one]
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  apply Circle.ext
  rw [coe_mk hz', Circle.coe_inv, coe_mk hz, Complex.conj_conj, inv_div]

theorem proj_neg (t : ℝ) : proj (-t) = (proj t)⁻¹ := by
  rw [proj, proj, mul_neg, Circle.exp_neg]

end RP1

/-- The conjugate `[[a, −b], [−c, d]]` of `g ∈ SL(2,ℝ)` by the reflection `diag(1, −1)`. -/
def slMirror (A : SL(2, ℝ)) : SL(2, ℝ) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) ℝ) 0 0, -(A : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1], by
    have := A.2
    rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two_of]
    linear_combination this⟩

open ComplexConjugate in
theorem slMirror_smul (A : SL(2, ℝ)) (w : RP1) : slMirror A • w = (A • w⁻¹)⁻¹ := by
  rw [← RP1.mk_rep w]
  have hz := RP1.rep_ne_zero w
  set z := RP1.rep w
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  rw [← RP1.mk_conj, RP1.sl_smul_mk _ hz', RP1.sl_smul_mk _ hz, ← RP1.mk_conj]
  congr 1
  apply Complex.ext
  · simp [slLin_apply, slMirror]
  · simp [slLin_apply, slMirror]
    ring

theorem trace_slMirror (A : SL(2, ℝ)) :
    Matrix.trace ((slMirror A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp [slMirror, Matrix.trace_fin_two]

namespace GTilde

/-- `x ↦ −f(−x)`, the conjugate of a lift by the reflection of `ℝP̃¹ = ℝ`. -/
def mirrorLift (f : CircleDeg1Lift) : CircleDeg1Lift where
  toFun x := -f (-x)
  monotone' a b h := neg_le_neg (f.monotone (neg_le_neg h))
  map_add_one' x := by
    have h := f.map_add_one (-(x + 1))
    rw [show -(x + 1) + 1 = -x by ring] at h
    show -f (-(x + 1)) = -f (-x) + 1
    linarith

theorem mirrorLift_apply (f : CircleDeg1Lift) (x : ℝ) : mirrorLift f x = -f (-x) := rfl

/-- The mirror, a monoid endomorphism of `CircleDeg1Lift`. -/
def mirrorHom : CircleDeg1Lift →* CircleDeg1Lift where
  toFun := mirrorLift
  map_one' := CircleDeg1Lift.ext fun x => by
    rw [mirrorLift_apply, CircleDeg1Lift.coe_one, id, neg_neg]
    rfl
  map_mul' f g := CircleDeg1Lift.ext fun x => by
    rw [CircleDeg1Lift.mul_apply, mirrorLift_apply, mirrorLift_apply, mirrorLift_apply,
      CircleDeg1Lift.mul_apply, neg_neg]

theorem mirror_mem (f : GTilde) :
    Units.map mirrorHom (f : CircleDeg1Liftˣ) ∈ GTilde := by
  obtain ⟨A, hA⟩ := pslMk_surjective (toPSL f)
  refine ⟨pslMk (slMirror A), fun t => ?_⟩
  show RP1.proj (-f (-t)) = _
  rw [RP1.proj_neg, proj_apply, ← hA, pslMk_smul, pslMk_smul, slMirror_smul, RP1.proj_neg]

/-- **The mirror of `G̃`**: `f ↦ (x ↦ −f(−x))`, the conjugation by the reflection of `ℝP̃¹`; it
lifts the conjugation of `PSL(2,ℝ)` by `diag(1, −1)`. -/
def mirror : GTilde →* GTilde :=
  ((Units.map mirrorHom).comp GTilde.subtype).codRestrict GTilde mirror_mem

theorem mirror_apply (f : GTilde) (x : ℝ) : mirror f x = -f (-x) := rfl

theorem mirror_mirror (f : GTilde) : mirror (mirror f) = f :=
  ext' fun x => by rw [mirror_apply, mirror_apply, neg_neg, neg_neg]

theorem mirror_delta : mirror delta = delta⁻¹ :=
  ext' fun x => by
    rw [mirror_apply, delta_apply]
    have h := delta_zpow_apply (-1) x
    rw [zpow_neg_one] at h
    rw [h]; push_cast; ring

theorem mirror_delta_zpow_mul_inv (k : ℤ) (g : GTilde) :
    mirror (delta ^ k * g)⁻¹ = delta ^ k * mirror g⁻¹ := by
  have hc : g⁻¹ * delta ^ (-k) = delta ^ (-k) * g⁻¹ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ delta_mem_center (-k))) g⁻¹
  have hc' : mirror g⁻¹ * delta ^ k = delta ^ k * mirror g⁻¹ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ delta_mem_center k)) (mirror g⁻¹)
  rw [mul_inv_rev, ← zpow_neg, map_mul, map_zpow, mirror_delta, inv_zpow', neg_neg, hc']

theorem mirror_fixed {g : GTilde} {x : ℝ} (hx : g x = x) : mirror g⁻¹ (-x) = -x := by
  rw [mirror_apply, neg_neg]
  conv_lhs => rw [← hx]
  rw [inv_apply_apply]

theorem toPSL_mirror_eq_one_iff (f : GTilde) : toPSL (mirror f) = 1 ↔ toPSL f = 1 := by
  have key : ∀ f : GTilde, toPSL f = 1 → toPSL (mirror f) = 1 := fun f h => by
    rw [toPSL_eq_iff] at h ⊢
    intro t
    rw [one_smul, mirror_apply, RP1.proj_neg, h, one_smul, RP1.proj_neg, inv_inv]
  refine ⟨fun h => ?_, key f⟩
  have := key _ h
  rwa [mirror_mirror] at this

theorem trSq_toPSL_mirror (f : GTilde) : PSL2.trSq (toPSL (mirror f)) = PSL2.trSq (toPSL f) := by
  obtain ⟨A, hA⟩ := pslMk_surjective (toPSL f)
  have h : toPSL (mirror f) = pslMk (slMirror A) := toPSL_eq_iff.2 fun t => by
    show RP1.proj (-f (-t)) = _
    rw [RP1.proj_neg, proj_apply, ← hA, pslMk_smul, pslMk_smul, slMirror_smul, RP1.proj_neg]
  rw [h, ← hA, PSL2.trSq_mk, PSL2.trSq_mk, trace_slMirror]

theorem trSq_inv (g : PSL(2, ℝ)) : PSL2.trSq g⁻¹ = PSL2.trSq g := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  show PSL2.trSq (pslMk A⁻¹) = _
  rw [PSL2.trSq_mk, PSL2.trSq_mk, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem isParabolic_mirror_inv_iff (g : GTilde) : IsParabolic (mirror g⁻¹) ↔ IsParabolic g := by
  unfold IsParabolic PSL2.IsParabolic
  rw [trSq_toPSL_mirror, Ne, toPSL_mirror_eq_one_iff, map_inv, trSq_inv, inv_eq_one]

theorem isHyperbolic_mirror_inv_iff (g : GTilde) : IsHyperbolic (mirror g⁻¹) ↔ IsHyperbolic g := by
  unfold IsHyperbolic PSL2.IsHyperbolic
  rw [trSq_toPSL_mirror, map_inv, trSq_inv]

end GTilde

end Mirror

/-! ## 7. The oriented tangent at `−p` and the lifted developing pair of the antipodal circle -/

section LiftedAntipode

open ComplexConjugate

/-- Complex conjugation, `ℝ`-linear. -/
def conjLE : ℂ ≃ₗ[ℝ] ℂ := Complex.conjAe.toLinearEquiv

theorem conjLE_apply (z : ℂ) : conjLE z = conj z := rfl

theorem conjLE_symm_apply (z : ℂ) : conjLE.symm z = conj z := by
  rw [LinearEquiv.symm_apply_eq, conjLE_apply, Complex.conj_conj]

variable (p : HS 2)

/-- **The oriented identification at `−p`**: `T_{−p} HS² = T_p HS² ≃ ℂ` followed by complex
conjugation. `T_p HS² = T_{−p} HS²` reverses the orientations (outward normals `p` and `−p`). -/
def tangentNeg (θ : TpHS p ≃ₗ[ℝ] ℂ) : TpHS (-p) ≃ₗ[ℝ] ℂ :=
  ((tpNeg p).symm.trans θ).trans conjLE

theorem tangentNeg_symm_apply (θ : TpHS p ≃ₗ[ℝ] ℂ) (z : ℂ) :
    (tangentNeg p θ).symm z = tpNeg p (θ.symm (conj z)) := by
  simp only [tangentNeg, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, conjLE_symm_apply]

theorem vol3_neg_left (u v w : 𝕄) : vol3 (-u) v w = -vol3 u v w := by
  simp only [vol3, Matrix.det_fin_three, Prod.fst_neg, Prod.snd_neg, PiLp.neg_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  ring

theorem vol3_neg_right (u v w : 𝕄) : vol3 u v (-w) = -vol3 u v w := by
  simp only [vol3, Matrix.det_fin_three, Prod.fst_neg, Prod.snd_neg, PiLp.neg_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- `tangentNeg` is oriented at `−p` when `θ` is oriented at `p`. -/
theorem isOrientedTangent_tangentNeg {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ) :
    IsOrientedTangent (-p) (tangentNeg p θ) := by
  intro w₁ w₂ h₁ h₂
  rw [tangentNeg_symm_apply, map_one] at h₁
  rw [tangentNeg_symm_apply, Complex.conj_I, map_neg, map_neg] at h₂
  have h₁' : tpMk p w₁ = θ.symm 1 := (tpNeg p).injective h₁
  have h₂' : tpMk p (-w₂) = θ.symm Complex.I := (tpNeg p).injective (by
    rw [tpNeg_mk, show tpMk (-p) (-w₂) = -tpMk (-p) w₂ from Submodule.Quotient.mk_neg _]
    exact neg_eq_iff_eq_neg.2 h₂)
  have := hθ w₁ (-w₂) h₁' h₂'
  rw [coe_neg_hs, vol3_neg_left]
  rw [vol3_neg_right] at this
  exact this

/-- **The universal covering at `−p`, read through `tangentNeg`**, is the one at `p` reversed:
`linkCover_{−p}(t) = linkCover_p(−t)`, as directions. -/
theorem linkCover_tangentNeg (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    linkCover (-p) (tangentNeg p θ) t = linkNeg p (linkCover p θ (-t)) := by
  apply Subtype.ext
  have hc : conj ((Circle.exp (Real.pi * t) : Circle) : ℂ) =
      ((Circle.exp (Real.pi * -t) : Circle) : ℂ) := by
    rw [← Circle.coe_inv_eq_conj, mul_neg, Circle.exp_neg]
  rw [coe_linkNeg, coe_linkCover, coe_linkCover, tangentNeg_symm_apply, hc, map_smul, norm_tpNeg]

end LiftedAntipode

section LiftedAntipode2

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
  {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

theorem IsPeriodicCover.comp_neg {E : ℝ → L} (hE : IsPeriodicCover E) :
    IsPeriodicCover (E ∘ Neg.neg) := by
  refine ⟨hE.isCoveringMap.comp_homeomorph (Homeomorph.neg ℝ),
    hE.surjective.comp neg_surjective, fun s => ?_, fun s t hst => ?_⟩
  · simp only [Function.comp_apply]
    rw [← hE.add_one (-(s + 1)), show -(s + 1) + 1 = -s by ring]
  · obtain ⟨m, hm⟩ := hE.fiber _ _ hst
    exact ⟨-m, by push_cast; linarith⟩

/-- **The lifted developing pair of the antipodal circle**: `E'(s) = E(−s)`, `D'(s) = −D(−s)`,
through `tangentNeg`, with lifted holonomy the mirror of `f⁻¹`. -/
theorem GammaLinkCircle.IsLiftedDev.antipode (h : C.IsLiftedDev θ E D f) :
    C.antipode.IsLiftedDev (tangentNeg C.pt θ) (E ∘ Neg.neg) (fun s => -D (-s))
      (GTilde.mirror f⁻¹) := by
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  refine ⟨hE.comp_neg, (hDc.comp continuous_neg).neg, fun a b hab => neg_lt_neg (hDm (neg_lt_neg hab)),
    ?_, fun s => ?_⟩
  · have hfun : (linkCover C.antipode.pt (tangentNeg C.pt θ) ∘ fun s => -D (-s)) =
        linkNeg C.pt ∘ ((linkCover C.pt θ ∘ D) ∘ Neg.neg) := funext fun s => by
      show linkCover (-C.pt) (tangentNeg C.pt θ) (-D (-s)) = _
      rw [linkCover_tangentNeg, neg_neg]; rfl
    rw [hfun]
    exact (hd.comp_reparam continuous_neg).antipode
  · rw [GTilde.mirror_apply, neg_neg]
    have := hDf (-(s + 1))
    rw [show -(s + 1) + 1 = -s by ring] at this
    rw [this, GTilde.inv_apply_apply]

/-- The developed image of the antipodal pair is the image of the developed image by
`ℓ(p) ≅ ℓ(−p)`. -/
theorem GammaLinkCircle.antipode_image (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (D : ℝ → ℝ) :
    linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
      linkNeg C.pt '' (linkCover C.pt θ '' range D) := by
  ext τ
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨_, ⟨D (-s), ⟨-s, rfl⟩, rfl⟩, by
      show _ = linkCover (-C.pt) (tangentNeg C.pt θ) (-D (-s))
      rw [linkCover_tangentNeg, neg_neg]⟩
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩
    exact ⟨-D s, ⟨-s, by simp only [neg_neg]⟩, by
      show linkCover (-C.pt) (tangentNeg C.pt θ) (-D s) = _
      rw [linkCover_tangentNeg, neg_neg]⟩

/-- **The degree is the same at `p̄` and `−p̄`**: `f = δᵏ g` gives `mirror f⁻¹ = δᵏ mirror g⁻¹`,
and `mirror g⁻¹` has a fixed point when `g` has one. -/
theorem GTilde.mirror_inv_degree {k : ℤ} {g : GTilde} (hfg : f = GTilde.delta ^ k * g)
    (hg : ∃ x, g x = x) :
    GTilde.mirror f⁻¹ = GTilde.delta ^ k * GTilde.mirror g⁻¹ ∧ ∃ x, GTilde.mirror g⁻¹ x = x := by
  obtain ⟨x, hx⟩ := hg
  exact ⟨by rw [hfg, GTilde.mirror_delta_zpow_mul_inv], -x, GTilde.mirror_fixed hx⟩

/-- **The degree is well defined**: two oriented lifted developing pairs of the same circle,
`f = δᵏ g` and `f' = δ^{k'} g'` with `g`, `g'` having fixed points, have `k = k'`. -/
theorem GammaLinkCircle.IsLiftedDev.degree_unique {θ' : TpHS C.pt ≃ₗ[ℝ] ℂ} {E' : ℝ → L}
    {D' : ℝ → ℝ} {f' : GTilde} (hθ : IsOrientedTangent C.pt θ) (hθ' : IsOrientedTangent C.pt θ')
    (h : C.IsLiftedDev θ E D f) (h' : C.IsLiftedDev θ' E' D' f') {k k' : ℤ} {g g' : GTilde}
    (hg : ∃ x, g x = x) (hg' : ∃ x, g' x = x) (hfg : f = GTilde.delta ^ k * g)
    (hfg' : f' = GTilde.delta ^ k' * g') : k' = k := by
  obtain ⟨-, κ, -, -, hf⟩ := h.relate hθ hθ' h'
  have hc : κ * GTilde.delta ^ k = GTilde.delta ^ k * κ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center k)) κ
  have e : f' = GTilde.delta ^ k * (κ * g * κ⁻¹) := by
    rw [hf, hfg, ← mul_assoc, hc, mul_assoc, mul_assoc, mul_assoc]
  obtain ⟨x, hx⟩ := hg
  have hfix : (κ * g * κ⁻¹) (κ x) = κ x := by
    rw [GTilde.coe_mul_apply, GTilde.coe_mul_apply, GTilde.inv_apply_apply, hx]
  exact GTilde.delta_zpow_mul_unique hg' ⟨κ x, hfix⟩ (hfg'.symm.trans e)

end LiftedAntipode2

/-! ## 8. The types at `−p̄` -/

section Types

theorem linkNeg_mem_dsFutureDirs_iff (p : HS 2) (σ : Link p) :
    linkNeg p σ ∈ dsFutureDirs (-p) ↔ σ ∈ dsFutureDirs p := by
  show Causal.Flat.IsFutureTimelike (dsProj (-p) (linkNeg p σ)) ↔
    Causal.Flat.IsFutureTimelike (dsProj p σ)
  rw [coe_linkNeg, dsProj_tpNeg]

theorem linkNeg_mem_dsPastDirs_iff (p : HS 2) (σ : Link p) :
    linkNeg p σ ∈ dsPastDirs (-p) ↔ σ ∈ dsPastDirs p := by
  show Causal.Flat.IsFutureTimelike (-dsProj (-p) (linkNeg p σ)) ↔
    Causal.Flat.IsFutureTimelike (-dsProj p σ)
  rw [coe_linkNeg, dsProj_tpNeg]

theorem minkQ_dsProj_linkNeg (p : HS 2) (σ : Link p) :
    Causal.Flat.minkQ (dsProj (-p) (linkNeg p σ)) = Causal.Flat.minkQ (dsProj p σ) := by
  rw [coe_linkNeg, dsProj_tpNeg]

theorem nullPairing_linkNeg (p : HS 2) (σ : Link p) :
    nullPairing (-p) (linkNeg p σ) = -nullPairing p σ := by
  rw [coe_linkNeg, nullPairing_tpNeg]

theorem linkNeg_image_eq {p : HS 2} {S : Set (Link p)} {T : Set (Link (-p))}
    (h : ∀ σ, linkNeg p σ ∈ T ↔ σ ∈ S) : linkNeg p '' S = T := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (h σ).2 hσ
  · intro hτ
    refine ⟨(linkNeg p).symm τ, (h _).1 ?_, Homeomorph.apply_symm_apply _ _⟩
    rwa [Homeomorph.apply_symm_apply]

/-- At `p ∈ dS²`, `ℓ(p) ≅ ℓ(−p)` matches the future directions, the past directions and the
space-like directions. -/
theorem linkNeg_image_iPlus {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    linkNeg p '' iPlus p = iPlus (-p) := by
  rw [iPlus_of_deSitter hp, iPlus_of_deSitter (neg_mem_deSitter_iff'.2 hp)]
  exact linkNeg_image_eq fun σ => linkNeg_mem_dsFutureDirs_iff p σ

theorem linkNeg_image_iMinus {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    linkNeg p '' iMinus p = iMinus (-p) := by
  rw [iMinus_of_deSitter hp, iMinus_of_deSitter (neg_mem_deSitter_iff'.2 hp)]
  exact linkNeg_image_eq fun σ => linkNeg_mem_dsPastDirs_iff p σ

theorem linkNeg_image_spacelike (p : HS 2) :
    linkNeg p '' {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} =
      {τ : Link (-p) | 0 < Causal.Flat.minkQ (dsProj (-p) τ)} :=
  linkNeg_image_eq fun σ => by
    show 0 < Causal.Flat.minkQ (dsProj (-p) (linkNeg p σ)) ↔ _
    rw [minkQ_dsProj_linkNeg]; rfl

/-- At a light-like `p`, `ℓ(p) ≅ ℓ(−p)` exchanges the two open arcs `{B(p,·) < 0}` and
`{B(p,·) > 0}` (`B(−p, ·) = −B(p, ·)`). -/
theorem linkNeg_image_nullNeg (p : HS 2) :
    linkNeg p '' {σ : Link p | nullPairing p σ < 0} = {τ : Link (-p) | 0 < nullPairing (-p) τ} :=
  linkNeg_image_eq fun σ => by
    show 0 < nullPairing (-p) (linkNeg p σ) ↔ _
    rw [nullPairing_linkNeg, Left.neg_pos_iff]; rfl

theorem linkNeg_image_nullPos (p : HS 2) :
    linkNeg p '' {σ : Link p | 0 < nullPairing p σ} = {τ : Link (-p) | nullPairing (-p) τ < 0} :=
  linkNeg_image_eq fun σ => by
    show nullPairing (-p) (linkNeg p σ) < 0 ↔ _
    rw [nullPairing_linkNeg, neg_lt_zero]; rfl

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}

/-- At `p ∈ dS²`, `i⁺(L⁻) = i⁺(L)` and `i⁻(L⁻) = i⁻(L)`. -/
theorem GammaLinkCircle.antipode_iPlusL (hp : C.pt ∈ HS.piece 2 .deSitter) :
    C.antipode.iPlusL = C.iPlusL := by
  ext x
  show linkNeg C.pt (@chartAt (Link C.pt) _ L _ C.atlas x x) ∈ iPlus (-C.pt) ↔
    @chartAt (Link C.pt) _ L _ C.atlas x x ∈ iPlus C.pt
  rw [iPlus_of_deSitter hp, iPlus_of_deSitter (neg_mem_deSitter_iff'.2 hp)]
  exact linkNeg_mem_dsFutureDirs_iff _ _

theorem GammaLinkCircle.antipode_iMinusL (hp : C.pt ∈ HS.piece 2 .deSitter) :
    C.antipode.iMinusL = C.iMinusL := by
  ext x
  show linkNeg C.pt (@chartAt (Link C.pt) _ L _ C.atlas x x) ∈ iMinus (-C.pt) ↔
    @chartAt (Link C.pt) _ L _ C.atlas x x ∈ iMinus C.pt
  rw [iMinus_of_deSitter hp, iMinus_of_deSitter (neg_mem_deSitter_iff'.2 hp)]
  exact linkNeg_mem_dsPastDirs_iff _ _

/-- **Time-like** (l.938–939): when `p` is time-like, one apex is future time-like and the other
past time-like: `p ∈ ℍ²₊ ⇒ −p ∈ ℍ²₋` and `p ∈ ℍ²₋ ⇒ −p ∈ ℍ²₊`. -/
theorem GammaLinkCircle.antipode_timelike (C : GammaLinkCircle L) :
    (C.pt ∈ HS.piece 2 .hypPlus → C.antipode.pt ∈ HS.piece 2 .hypMinus) ∧
      (C.pt ∈ HS.piece 2 .hypMinus → C.antipode.pt ∈ HS.piece 2 .hypPlus) :=
  ⟨fun h => HS.neg_mem_hypMinus_iff.2 h, fun h => neg_mem_hypPlus_iff'.2 h⟩

/-- `−p` is light-like (space-like) iff `p` is, with the future and past exchanged. -/
theorem GammaLinkCircle.antipode_lightlike_pos (C : GammaLinkCircle L) :
    (C.pt ∈ HS.piece 2 .bdPlus → C.antipode.pt ∈ HS.piece 2 .bdMinus) ∧
      (C.pt ∈ HS.piece 2 .bdMinus → C.antipode.pt ∈ HS.piece 2 .bdPlus) ∧
      (C.pt ∈ HS.piece 2 .deSitter → C.antipode.pt ∈ HS.piece 2 .deSitter) :=
  ⟨fun h => HS.neg_mem_bdMinus_iff.2 h, fun h => neg_mem_bdPlus_iff'.2 h,
    fun h => neg_mem_deSitter_iff'.2 h⟩

variable {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- **Light-like, degree `k`** (l.939–941): a lifted holonomy `f = δᵏ g` at `p̄` gives the lifted
holonomy `δᵏ (mirror g⁻¹)` at `−p̄`, through an oriented identification at `−p`; the degree is
the same (and well defined, `GX.GammaLinkCircle.IsLiftedDev.degree_unique`), parabolic stays
parabolic, and `−p` is past light-like when `p` is future light-like, and vice versa. -/
theorem GammaLinkCircle.IsLiftedDev.antipode_degree (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) {k : ℤ} {g : GTilde} (hg : ∃ x, g x = x)
    (hfg : f = GTilde.delta ^ k * g) :
    IsOrientedTangent C.antipode.pt (tangentNeg C.pt θ) ∧
      C.antipode.IsLiftedDev (tangentNeg C.pt θ) (E ∘ Neg.neg) (fun s => -D (-s))
        (GTilde.mirror f⁻¹) ∧
      GTilde.mirror f⁻¹ = GTilde.delta ^ k * GTilde.mirror g⁻¹ ∧
      (∃ x, GTilde.mirror g⁻¹ x = x) ∧
      (GTilde.IsParabolic (GTilde.mirror g⁻¹) ↔ GTilde.IsParabolic g) ∧
      (GTilde.IsHyperbolic (GTilde.mirror g⁻¹) ↔ GTilde.IsHyperbolic g) ∧
      ∀ (θ' : TpHS C.antipode.pt ≃ₗ[ℝ] ℂ) (E' : ℝ → L) (D' : ℝ → ℝ) (f' : GTilde) (k' : ℤ)
        (g' : GTilde), IsOrientedTangent C.antipode.pt θ' → C.antipode.IsLiftedDev θ' E' D' f' →
        (∃ x, g' x = x) → f' = GTilde.delta ^ k' * g' → k' = k := by
  obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
  have hθ' : IsOrientedTangent C.antipode.pt (tangentNeg C.pt θ) :=
    isOrientedTangent_tangentNeg C.pt hθ
  have ha := h.antipode
  refine ⟨hθ', ha, hf', hg', GTilde.isParabolic_mirror_inv_iff g,
    GTilde.isHyperbolic_mirror_inv_iff g, fun θ'' E'' D'' f'' k'' g'' hθ'' h'' hg'' hfg'' => ?_⟩
  exact GammaLinkCircle.IsLiftedDev.degree_unique (C := C.antipode) (θ := tangentNeg C.pt θ)
    (θ' := θ'') hθ' hθ'' ha h'' hg' hg'' hf' hfg''

/-- The light-like sign is kept: `g x ≥ x` everywhere gives `mirror g⁻¹ x ≥ x` everywhere. -/
theorem GTilde.le_mirror_inv_apply {g : GTilde} (hg : ∀ x, x ≤ g x) (x : ℝ) :
    x ≤ GTilde.mirror g⁻¹ x := by
  rw [GTilde.mirror_apply, le_neg]
  have := (GTilde.strictMono g⁻¹).monotone (hg (-x))
  rwa [GTilde.inv_apply_apply] at this

theorem GTilde.mirror_inv_apply_le {g : GTilde} (hg : ∀ x, g x ≤ x) (x : ℝ) :
    GTilde.mirror g⁻¹ x ≤ x := by
  rw [GTilde.mirror_apply, neg_le]
  have := (GTilde.strictMono g⁻¹).monotone (hg (-x))
  rwa [GTilde.inv_apply_apply] at this

/-- A positive light-like singularity of degree `k ≥ 1` at `p̄` gives a positive one at `−p̄`
(not stated in the paper; the sign is kept). -/
theorem GammaLinkCircle.IsLightlikePositive.antipode (hC : C.IsLightlikePositive) :
    C.antipode.IsLightlikePositive := by
  obtain ⟨hQ, θ, hθ, E, D, f, k, g, h, hk, hg, hpar, hfg, hpos⟩ := hC
  obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
  refine ⟨?_, tangentNeg C.pt θ, isOrientedTangent_tangentNeg C.pt hθ, E ∘ Neg.neg,
    fun s => -D (-s), GTilde.mirror f⁻¹, k, GTilde.mirror g⁻¹, h.antipode, hk, hg',
    (GTilde.isParabolic_mirror_inv_iff g).2 hpar, hf', GTilde.le_mirror_inv_apply hpos⟩
  show Causal.Flat.minkQ ((-C.pt : HS 2) : 𝕄) = 0
  rw [coe_neg_hs, Causal.Flat.minkQ_neg, hQ]

theorem GammaLinkCircle.IsLightlikeNegative.antipode (hC : C.IsLightlikeNegative) :
    C.antipode.IsLightlikeNegative := by
  obtain ⟨hQ, θ, hθ, E, D, f, k, g, h, hk, hg, hpar, hfg, hneg⟩ := hC
  obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
  refine ⟨?_, tangentNeg C.pt θ, isOrientedTangent_tangentNeg C.pt hθ, E ∘ Neg.neg,
    fun s => -D (-s), GTilde.mirror f⁻¹, k, GTilde.mirror g⁻¹, h.antipode, hk, hg',
    (GTilde.isParabolic_mirror_inv_iff g).2 hpar, hf', GTilde.mirror_inv_apply_le hneg⟩
  show Causal.Flat.minkQ ((-C.pt : HS 2) : 𝕄) = 0
  rw [coe_neg_hs, Causal.Flat.minkQ_neg, hQ]

/-- **Cuspidal ↔ extreme BTZ-like** (l.941–942): the light-like degree-`0` images at `p̄` and at
`−p̄` correspond, `p ∈ ∂ℍ²₊`: future cuspidal (`I = i⁺(ℓ(p))`) at `p̄` gives extreme BTZ-like
past (`i⁺(ℓ(−p))` minus its tangent directions, OQ-116 (b)) at `−p̄`, and extreme BTZ-like future
at `p̄` gives past cuspidal at `−p̄`. -/
theorem GammaLinkCircle.antipode_bdPlus_image (hp : C.pt ∈ HS.piece 2 .bdPlus) :
    (linkCover C.pt θ '' range D = iPlus C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iPlus C.antipode.pt \ tangentDirs C.antipode.pt) ∧
    (linkCover C.pt θ '' range D = iMinus C.pt \ tangentDirs C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iMinus C.antipode.pt) := by
  have hQ : Causal.Flat.minkQ (C.pt : 𝕄) = 0 := hp.1
  have hp' : -C.pt ∈ HS.piece 2 .bdMinus := HS.neg_mem_bdMinus_iff.2 hp
  have hQ' : Causal.Flat.minkQ ((-C.pt : HS 2) : 𝕄) = 0 := hp'.1
  rw [GammaLinkCircle.antipode_image]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · show _ = iPlus (-C.pt) \ tangentDirs (-C.pt)
    rw [h, iPlus_of_bdPlus hp, lightDomain_hypPlus_eq hp, linkNeg_image_nullNeg,
      iPlus_of_bdMinus hp', lightDomain_deSitter_eq hQ', nullNonneg_sdiff]
  · show _ = iMinus (-C.pt)
    rw [h, iMinus_of_bdPlus hp, lightDomain_deSitter_eq hQ, nullNonneg_sdiff,
      linkNeg_image_nullPos, iMinus_of_bdMinus hp', lightDomain_hypMinus_eq hp']

/-- The same at `p ∈ ∂ℍ²₋` (« and vice versa »): past cuspidal at `p̄` gives extreme BTZ-like
future at `−p̄`, extreme BTZ-like past at `p̄` gives future cuspidal at `−p̄`. -/
theorem GammaLinkCircle.antipode_bdMinus_image (hp : C.pt ∈ HS.piece 2 .bdMinus) :
    (linkCover C.pt θ '' range D = iMinus C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iMinus C.antipode.pt \ tangentDirs C.antipode.pt) ∧
    (linkCover C.pt θ '' range D = iPlus C.pt \ tangentDirs C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iPlus C.antipode.pt) := by
  have hQ : Causal.Flat.minkQ (C.pt : 𝕄) = 0 := hp.1
  have hp' : -C.pt ∈ HS.piece 2 .bdPlus := neg_mem_bdPlus_iff'.2 hp
  have hQ' : Causal.Flat.minkQ ((-C.pt : HS 2) : 𝕄) = 0 := hp'.1
  rw [GammaLinkCircle.antipode_image]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · show _ = iMinus (-C.pt) \ tangentDirs (-C.pt)
    rw [h, iMinus_of_bdMinus hp, lightDomain_hypMinus_eq hp, linkNeg_image_nullNeg,
      iMinus_of_bdPlus hp', lightDomain_deSitter_eq hQ', nullNonneg_sdiff]
  · show _ = iPlus (-C.pt)
    rw [h, iPlus_of_bdMinus hp, lightDomain_deSitter_eq hQ, nullNonneg_sdiff,
      linkNeg_image_nullPos, iPlus_of_bdPlus hp', lightDomain_hypPlus_eq hp']

/-- `bbsrem:p_p`, **the last sentence** (l.941–942): if `p̄` is a future cuspidal singularity, then
`−p̄` is a past extreme BTZ-like singularity: `−p ∈ ∂ℍ²₋`, the antipodal circle has an oriented
lifted developing pair of degree `0` with parabolic holonomy, whose developed image is `i⁺(ℓ(−p))`
minus its two tangent directions (the second case of
`GX.GammaLinkCircle.IsLiftedDev.bdMinus_degree_zero`, OQ-116 (b)), and `i⁺(L⁻) = L⁻`,
`i⁻(L⁻) = ∅`. -/
theorem GammaLinkCircle.IsLiftedDev.antipode_cuspidal (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .bdPlus) (hpar : GTilde.IsParabolic f)
    (hfix : ∃ x, f x = x) (hcusp : linkCover C.pt θ '' range D = iPlus C.pt) :
    C.antipode.pt ∈ HS.piece 2 .bdMinus ∧ IsOrientedTangent C.antipode.pt (tangentNeg C.pt θ) ∧
      C.antipode.IsLiftedDev (tangentNeg C.pt θ) (E ∘ Neg.neg) (fun s => -D (-s))
        (GTilde.mirror f⁻¹) ∧
      GTilde.IsParabolic (GTilde.mirror f⁻¹) ∧ (∃ x, GTilde.mirror f⁻¹ x = x) ∧
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iPlus C.antipode.pt \ tangentDirs C.antipode.pt ∧
      C.antipode.iPlusL = univ ∧ C.antipode.iMinusL = ∅ := by
  have hp' : -C.pt ∈ HS.piece 2 .bdMinus := HS.neg_mem_bdMinus_iff.2 hp
  have himg := (GammaLinkCircle.antipode_bdPlus_image (θ := θ) (D := D) hp).1 hcusp
  have ha := h.antipode
  obtain ⟨x, hx⟩ := hfix
  have hin := GammaLinkCircle.linkCover_mem_of_image_eq _ himg
  refine ⟨hp', isOrientedTangent_tangentNeg C.pt hθ, ha,
    (GTilde.isParabolic_mirror_inv_iff f).2 hpar, ⟨-x, GTilde.mirror_fixed hx⟩, himg,
    ha.iPlusL_eq_univ fun s => (hin s).1, ha.iMinusL_eq_empty fun s hs => ?_⟩
  have h1 := hin s
  have hQ' : Causal.Flat.minkQ ((-C.pt : HS 2) : 𝕄) = 0 := hp'.1
  change _ ∈ iPlus (-C.pt) \ tangentDirs (-C.pt) at h1
  change _ ∈ iMinus (-C.pt) at hs
  rw [iPlus_of_bdMinus hp', lightDomain_deSitter_eq hQ', nullNonneg_sdiff] at h1
  rw [iMinus_of_bdMinus hp', lightDomain_hypMinus_eq hp'] at hs
  exact lt_asymm (show 0 < nullPairing (-C.pt) _ from h1) hs

/-- **Space-like, the types** (l.936–937, the type-level reading): at `p ∈ dS²` the developed
images at `p̄` and `−p̄` have the same type: `i⁺(ℓ(p))` (BTZ-like past) gives `i⁺(ℓ(−p))`,
`i⁻(ℓ(p))` (BTZ-like future) gives `i⁻(ℓ(−p))`, a space-like arc (Misner) gives a space-like arc. -/
theorem GammaLinkCircle.antipode_deSitter_image (hp : C.pt ∈ HS.piece 2 .deSitter) :
    (linkCover C.pt θ '' range D = iPlus C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iPlus C.antipode.pt) ∧
    (linkCover C.pt θ '' range D = iMinus C.pt →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) =
        iMinus C.antipode.pt) ∧
    (linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} →
      linkCover C.antipode.pt (tangentNeg C.pt θ) '' range (fun s => -D (-s)) ⊆
        {τ | 0 < Causal.Flat.minkQ (dsProj C.antipode.pt τ)}) := by
  rw [GammaLinkCircle.antipode_image]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h]; exact linkNeg_image_iPlus hp
  · rw [h]; exact linkNeg_image_iMinus hp
  · have := image_mono (f := linkNeg C.pt) h
    rwa [linkNeg_image_spacelike] at this

/-- **Positive space-like singularities stay positive** across the apices (degree `k ≥ 1`). -/
theorem GammaLinkCircle.IsSpacelikePositive.antipode (hC : C.IsSpacelikePositive) :
    C.antipode.IsSpacelikePositive := by
  obtain ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hpos⟩ := hC
  obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
  refine ⟨neg_mem_deSitter_iff'.2 hp, tangentNeg C.pt θ, isOrientedTangent_tangentNeg C.pt hθ,
    E ∘ Neg.neg, fun s => -D (-s), GTilde.mirror f⁻¹, k, GTilde.mirror g⁻¹, h.antipode, hk, hg',
    (GTilde.isHyperbolic_mirror_inv_iff g).2 hh, hf', fun s hs => ?_⟩
  rw [GammaLinkCircle.antipode_iPlusL hp] at hs
  have h1 := hpos (-s) hs
  show -D (-s) ≤ GTilde.mirror g⁻¹ (-D (-s))
  rw [GTilde.mirror_apply, neg_neg, neg_le_neg_iff]
  have := (GTilde.strictMono g⁻¹).monotone h1
  rwa [GTilde.inv_apply_apply] at this

/-- **Negative space-like singularities stay negative.** -/
theorem GammaLinkCircle.IsSpacelikeNegative.antipode (hC : C.IsSpacelikeNegative) :
    C.antipode.IsSpacelikeNegative := by
  obtain ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hneg⟩ := hC
  obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
  refine ⟨neg_mem_deSitter_iff'.2 hp, tangentNeg C.pt θ, isOrientedTangent_tangentNeg C.pt hθ,
    E ∘ Neg.neg, fun s => -D (-s), GTilde.mirror f⁻¹, k, GTilde.mirror g⁻¹, h.antipode, hk, hg',
    (GTilde.isHyperbolic_mirror_inv_iff g).2 hh, hf', fun s hs => ?_⟩
  rw [GammaLinkCircle.antipode_iPlusL hp] at hs
  have h1 := hneg (-s) hs
  show GTilde.mirror g⁻¹ (-D (-s)) ≤ -D (-s)
  rw [GTilde.mirror_apply, neg_neg, neg_le_neg_iff]
  have := (GTilde.strictMono g⁻¹).monotone h1
  rwa [GTilde.inv_apply_apply] at this

end Types

/-! ## 9. Moved-`p` isomorphisms, and the chirality of a Misner link -/

section Moved

theorem normalize_smul_pos {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {c : ℝ}
    (hc : 0 < c) (x : V) : ‖c • x‖⁻¹ • (c • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, mul_inv, mul_right_comm,
    inv_mul_cancel₀ hc.ne', one_mul]

/-- `B ∈ SO₀(1,2)` maps the line `ℝp` onto the line `ℝ(B • p)`. -/
theorem map_span_hs (B : Causal.Flat.lorentz 2) (p : HS 2) :
    (ℝ ∙ (p : 𝕄)).map ((B : 𝕄 ≃ₗ[ℝ] 𝕄) : 𝕄 →ₗ[ℝ] 𝕄) = ℝ ∙ ((B • p : HS 2) : 𝕄) := by
  have hB : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero p)
  rw [Submodule.map_span, Set.image_singleton, coe_hs_smul,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (norm_ne_zero_iff.2 hB)))]
  rfl

/-- **`T_p HS² ≃ T_{p'} HS²` induced by `B ∈ SO₀(1,2)` with `B • p = p'`.** -/
def tpMove (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') : TpHS p ≃ₗ[ℝ] TpHS p' :=
  Submodule.Quotient.equiv _ _ (B : 𝕄 ≃ₗ[ℝ] 𝕄) (by rw [map_span_hs, h])

theorem tpMove_mk (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (w : 𝕄) :
    tpMove B h (tpMk p w) = tpMk p' ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) := rfl

/-- **`ℓ(p) ≅ ℓ(p')` induced by `B`.** -/
def linkMove (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') : Link p ≃ₜ Link p' :=
  raySphereHomeomorph (tpMove B h)

theorem coe_linkMove (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (σ : Link p) :
    ((linkMove B h σ : Link p') : TpHS p') = ‖tpMove B h σ‖⁻¹ • tpMove B h σ := rfl

theorem lorentz_apply_inv (M : Causal.Flat.lorentz 2) (v : 𝕄) :
    (M : 𝕄 ≃ₗ[ℝ] 𝕄) (((M⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v) = v := by
  show ((M * M⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v = v
  rw [mul_inv_cancel]; rfl

theorem lorentz_inv_apply (M : Causal.Flat.lorentz 2) (v : 𝕄) :
    ((M⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((M : 𝕄 ≃ₗ[ℝ] 𝕄) v) = v := by
  show ((M⁻¹ * M : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) v = v
  rw [inv_mul_cancel]; rfl

/-- `B Γ_p B⁻¹ = Γ_{p'}`: the conjugate of `A ∈ Γ_p`. -/
def gammaMove (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (A : GammaP p) :
    GammaP p' :=
  ⟨B * (A : Causal.Flat.lorentz 2) * B⁻¹, by
    show (B : 𝕄 ≃ₗ[ℝ] 𝕄) (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (((B⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) p')) = p'
    rw [← h, coe_hs_smul, map_smul, map_smul, lorentz_inv_apply,
      show ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) p = p from A.2, map_smul]⟩

theorem coe_gammaMove (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (A : GammaP p) :
    ((gammaMove B h A : GammaP p') : Causal.Flat.lorentz 2) = B * (A : Causal.Flat.lorentz 2) * B⁻¹ :=
  rfl

theorem tpMove_tangent (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (A : GammaP p)
    (z : TpHS p) :
    tpMove B h (GammaP.tangent A z) = GammaP.tangent (gammaMove B h A) (tpMove B h z) := by
  induction z using Submodule.Quotient.induction_on with
  | H w =>
    show tpMk p' ((B : 𝕄 ≃ₗ[ℝ] 𝕄) (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w)) =
      tpMk p' ((B : 𝕄 ≃ₗ[ℝ] 𝕄) (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
        (((B⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w))))
    rw [lorentz_inv_apply]

/-- `ℓ(p) ≅ ℓ(p')` intertwines `Γ_p` and `Γ_{p'}`. -/
theorem linkMove_smul (B : Causal.Flat.lorentz 2) {p p' : HS 2} (h : B • p = p') (A : GammaP p)
    (σ : Link p) : linkMove B h (A • σ) = gammaMove B h A • linkMove B h σ := by
  apply Subtype.ext
  rw [coe_linkMove, gammaP_smul_def, gammaP_smul_def, coe_linRaySmul, coe_linRaySmul, coe_linkMove,
    map_smul, map_smul, tpMove_tangent,
    normalize_smul_pos (inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero p A σ))),
    normalize_smul_pos (inv_pos.2 (norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff _).2
      (raySphere_ne_zero σ))))]

variable {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']

/-- **A moved-`p` isomorphism** (OQ-120 (a), the reading with a moving point): `φ : L ≃ₜ L'` is an
isomorphism of the `(Γ_p, ℓ(p))`-circle `C` onto the `(Γ_{p'}, ℓ(p'))`-circle `C'` through
`B ∈ SO₀(1,2)` with `B • p = p'`: in the charts, near every point, `φ` reads as `B` (acting on
directions, `GX.linkMove`) followed by an element of `Γ_{p'}`. -/
def GammaLinkCircle.IsIsoVia (C : GammaLinkCircle L) (C' : GammaLinkCircle L')
    (B : Causal.Flat.lorentz 2) (h : B • C.pt = C'.pt) (φ : L ≃ₜ L') : Prop :=
  ∀ x, ∃ A : GammaP C'.pt, ∀ᶠ y in 𝓝 x,
    @chartAt (Link C'.pt) _ L' _ C'.atlas (φ x) (φ y) =
      A • linkMove B h (@chartAt (Link C.pt) _ L _ C.atlas x y)

end Moved

section Chirality

/-- The Lorentzian cross product: `B(u ×ₗ v, w) = vol3 u v w`. -/
def lcross (u v : 𝕄) : 𝕄 :=
  mink3 (-(u.2 0 * v.2 1 - u.2 1 * v.2 0)) (-(u.1 * v.2 1 - u.2 1 * v.1))
    (u.1 * v.2 0 - u.2 0 * v.1)

theorem minkB_lcross (u v w : 𝕄) : Causal.Flat.minkB (lcross u v) w = vol3 u v w := by
  rw [minkB_two, vol3_eq]
  simp only [lcross, mink3_fst, mink3_snd_zero, mink3_snd_one]
  ring

theorem minkQ_lcross (u v : 𝕄) :
    Causal.Flat.minkQ (lcross u v) =
      Causal.Flat.minkB u v ^ 2 - Causal.Flat.minkQ u * Causal.Flat.minkQ v := by
  rw [minkQ_two, minkB_two, minkQ_two, minkQ_two]
  simp only [lcross, mink3_fst, mink3_snd_zero, mink3_snd_one]
  ring

theorem vol3_smul_mid (u v w : 𝕄) (c : ℝ) : vol3 u (c • v) w = c * vol3 u v w := by
  rw [vol3_eq, vol3_eq]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The sign of `vol3 q w T` does not depend on the future time-like `T`** when `q, w` span a
space-like plane (`q ⊥ w`, both space-like): `vol3 q w · = B(q ×ₗ w, ·)` and `q ×ₗ w` is
time-like. -/
theorem vol3_pos_iff_of_spacelike {q w T T' : 𝕄} (hq : 0 < Causal.Flat.minkQ q)
    (hw : 0 < Causal.Flat.minkQ w) (hqw : Causal.Flat.minkB q w = 0)
    (hT : Causal.Flat.IsFutureTimelike T) (hT' : Causal.Flat.IsFutureTimelike T') :
    vol3 q w T ≠ 0 ∧ (0 < vol3 q w T ↔ 0 < vol3 q w T') := by
  have hn : Causal.Flat.minkQ (lcross q w) < 0 := by
    rw [minkQ_lcross, hqw]; nlinarith [mul_pos hq hw]
  have hn0 : ∀ v : 𝕄, Causal.Flat.minkQ v < 0 → v ≠ 0 := fun v hv h0 => by
    rw [h0] at hv; simp [Causal.Flat.minkQ] at hv
  rw [← minkB_lcross, ← minkB_lcross]
  rcases Causal.Flat.isFutureTimelike_or_neg hn with hf | hf
  · have h1 := Causal.Flat.minkB_neg_of_future ⟨hf.1.le, hf.2.le⟩ (hn0 _ hf.2) hT
    have h2 := Causal.Flat.minkB_neg_of_future ⟨hf.1.le, hf.2.le⟩ (hn0 _ hf.2) hT'
    exact ⟨h1.ne, ⟨fun h => absurd h1 (not_lt.2 h.le), fun h => absurd h2 (not_lt.2 h.le)⟩⟩
  · have h1 := Causal.Flat.minkB_neg_of_future ⟨hf.1.le, hf.2.le⟩ (hn0 _ hf.2) hT
    have h2 := Causal.Flat.minkB_neg_of_future ⟨hf.1.le, hf.2.le⟩ (hn0 _ hf.2) hT'
    rw [Causal.Flat.minkB_neg_left] at h1 h2
    exact ⟨by linarith, ⟨fun _ => by linarith, fun _ => by linarith⟩⟩

theorem isFutureTimelike_timeUnit : Causal.Flat.IsFutureTimelike (Causal.Flat.timeUnit 2) :=
  ⟨by simp [Causal.Flat.timeUnit], by simp⟩

/-- The chirality of a direction `σ ∈ ℓ(p)`, `p ∈ dS²`: `vol3 p (π σ) e_t`, `π` the projection
onto `p^⊥`. On the space-like directions its sign tells on which side of `p` the plane of `σ`
turns (`vol3_pos_iff_of_spacelike`). -/
def chirality (p : HS 2) (σ : Link p) : ℝ := vol3 (p : 𝕄) (dsProj p σ) (Causal.Flat.timeUnit 2)

theorem continuous_vol3_mid (u w : 𝕄) : Continuous fun v : 𝕄 => vol3 u v w := by
  have : (fun v : 𝕄 => vol3 u v w) = fun v => u.1 * (v.2 0 * w.2 1 - v.2 1 * w.2 0) -
      u.2 0 * (v.1 * w.2 1 - v.2 1 * w.1) + u.2 1 * (v.1 * w.2 0 - v.2 0 * w.1) :=
    funext fun v => vol3_eq u v w
  rw [this]
  fun_prop

theorem continuous_chirality (p : HS 2) : Continuous (chirality p) :=
  (continuous_vol3_mid _ _).comp (continuous_dsProj p)

/-- The chirality of a space-like direction at `p ∈ dS²` is not zero. -/
theorem chirality_ne_zero {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {σ : Link p}
    (hσ : 0 < Causal.Flat.minkQ (dsProj p σ)) : chirality p σ ≠ 0 :=
  (vol3_pos_iff_of_spacelike hp hσ (minkB_dsProj p σ) isFutureTimelike_timeUnit
    isFutureTimelike_timeUnit).1

/-- **`ℓ(p) ≅ ℓ(−p)` reverses the chirality.** -/
theorem chirality_linkNeg (p : HS 2) (σ : Link p) :
    chirality (-p) (linkNeg p σ) = -chirality p σ := by
  rw [chirality, chirality, coe_linkNeg, dsProj_tpNeg, coe_neg_hs, vol3_neg_left]

/-- **A move `B` with `B p = −p`, followed by `Γ_{−p}`, keeps the sign of the chirality.** -/
theorem chirality_smul_linkMove_pos_iff {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    {B : Causal.Flat.lorentz 2} (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    (A : GammaP (-p)) {σ : Link p} (hσ : 0 < Causal.Flat.minkQ (dsProj p σ)) :
    0 < chirality (-p) (A • linkMove B h σ) ↔ 0 < chirality p σ := by
  set w := liftT p σ
  have hσw : (σ : TpHS p) = tpMk p w := (tpMk_liftT p σ).symm
  have hx : tpMove B h σ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero σ)
  -- `π_{−p}(B σ) = B π_p(σ)`
  have hBw : Causal.Flat.minkB (p : 𝕄) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = -Causal.Flat.minkB (p : 𝕄) w := by
    have := Causal.Flat.lorentz.minkB_apply B.2 p w
    rw [hBp, Causal.Flat.minkB_neg_left] at this
    linarith
  have hproj : dsProj (-p) (tpMove B h σ) = (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p σ) := by
    rw [hσw, tpMove_mk, dsProj_mk, dsProj_mk, perpLin_neg,
      perpLin_apply, perpLin_apply, map_sub, map_smul, map_smul, hBw, hBp, neg_smul, smul_neg,
      sub_neg_eq_add]
  set M : Causal.Flat.lorentz 2 := (A : Causal.Flat.lorentz 2) * B
  have hMp : (M : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄) := by
    show ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) p) = -(p : 𝕄)
    have hA : ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((-p : HS 2) : 𝕄) = ((-p : HS 2) : 𝕄) := A.2
    rw [coe_neg_hs, map_neg, neg_inj] at hA
    rw [hBp, map_neg, hA]
  obtain ⟨c, hc, hτ⟩ : ∃ c : ℝ, 0 < c ∧
      dsProj (-p) ((A • linkMove B h σ : Link (-p)) : TpHS (-p)) =
        c • (M : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p σ) := by
    have h1 := dsProj_smul (-p) A (linkMove B h σ)
    have h2 : dsProj (-p) ((linkMove B h σ : Link (-p)) : TpHS (-p)) =
        ‖tpMove B h σ‖⁻¹ • (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p σ) := by
      rw [coe_linkMove, map_smul, hproj]
    refine ⟨‖GammaP.tangent A (linkMove B h σ)‖⁻¹ * ‖tpMove B h σ‖⁻¹,
      mul_pos (inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero _ A _))) (inv_pos.2 (norm_pos_iff.2 hx)),
      ?_⟩
    rw [h1, h2, map_smul, smul_smul]
    rfl
  have hT' : Causal.Flat.IsFutureTimelike
      (((M⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2)) :=
    (Causal.Flat.lorentz.isFutureTimelike_apply_iff (M⁻¹).2).2 isFutureTimelike_timeUnit
  have hvol : chirality (-p) (A • linkMove B h σ) =
      c * vol3 p (dsProj p σ) (((M⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (Causal.Flat.timeUnit 2)) := by
    rw [chirality, hτ, vol3_smul_mid, coe_neg_hs, ← hMp]
    conv_lhs => rw [← lorentz_apply_inv M (Causal.Flat.timeUnit 2)]
    rw [vol3_lorentz]
  rw [hvol, mul_pos_iff_of_pos_left hc]
  exact ((vol3_pos_iff_of_spacelike hp hσ (minkB_dsProj p σ) isFutureTimelike_timeUnit hT').2).symm

end Chirality

/-! ## 10. The space-like sentence fails for Misner singularities -/

section Misner

/-- A nowhere-vanishing continuous function on `ℝ` has a constant sign. -/
theorem pos_iff_pos_of_ne_zero {g : ℝ → ℝ} (hg : Continuous g) (hne : ∀ s, g s ≠ 0) (a b : ℝ) :
    0 < g a ↔ 0 < g b := by
  have key : ∀ a b, 0 < g a → 0 < g b := fun a b ha => by
    by_contra hb
    have hb' : g b < 0 := lt_of_le_of_ne (not_lt.1 hb) (hne b)
    obtain ⟨c, hc⟩ := intermediate_value_univ b a hg ⟨hb'.le, ha.le⟩
    exact hne c hc
  exact ⟨key a b, key b a⟩

/-- A move `B ∈ SO₀(1,2)` sending the ray of `p ∈ dS²` to the ray of `−p` sends the vector `p` to
`−p` (`Q(B p) = Q(p) ≠ 0`). -/
theorem apply_eq_neg_of_smul_eq_neg {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    {B : Causal.Flat.lorentz 2} (h : B • p = -p) : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄) := by
  have h1 : ((B • p : HS 2) : 𝕄) = ((-p : HS 2) : 𝕄) := congrArg Subtype.val h
  rw [coe_hs_smul, coe_neg_hs] at h1
  have hne : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero p)
  have hc : 0 < ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ := norm_pos_iff.2 hne
  have hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ • (-(p : 𝕄)) := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hQ := Causal.Flat.lorentz.minkQ_apply B.2 (p : 𝕄)
  rw [hBp, Causal.Flat.minkQ_smul, Causal.Flat.minkQ_neg] at hQ
  have hQp : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hc2 : ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ ^ 2 = 1 :=
    mul_right_cancel₀ hQp.ne' (hQ.trans (one_mul _).symm)
  have h3 : (‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ - 1) * (‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ + 1) = 0 := by
    linear_combination hc2
  have hc1 : ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖ = 1 := by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · linarith
    · linarith
  rw [hBp, hc1, one_smul]

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
  {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- **A Misner link is not isomorphic to its antipodal link, through any move**: at `p ∈ dS²`, if
the developed image of `L` is space-like (a Misner singularity, l.876–878), then for no
`B ∈ SO₀(1,2)` with `B • p = −p` and no homeomorphism `φ : L → L` is `φ` an isomorphism of `L`
onto the antipodal circle `L⁻` (the link of `−p̄`, `GX.GammaLinkCircle.DevData.isIso_flip`)
through `B`. The chirality `vol3 p (π σ) e_t` has a constant sign on the developed image; `ℓ(p) ≅
ℓ(−p)` reverses it (`GX.chirality_linkNeg`) while a move followed by `Γ_{−p}` keeps it
(`GX.chirality_smul_linkMove_pos_iff`). -/
theorem GammaLinkCircle.IsLiftedDev.not_isIsoVia_antipode (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter)
    (hS : linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)})
    (B : Causal.Flat.lorentz 2) (hB : B • C.pt = C.antipode.pt) (φ : L ≃ₜ L) :
    ¬ C.IsIsoVia C.antipode B hB φ := by
  intro hiso
  obtain ⟨hE, -, -, hd, -⟩ := h
  have hEc := hE.isCoveringMap.continuous
  have hdc : Continuous (linkCover C.pt θ ∘ D) := hd.continuous hEc
  have hdS : ∀ s, 0 < Causal.Flat.minkQ (dsProj C.pt ((linkCover C.pt θ ∘ D) s)) := fun s =>
    hS ⟨D s, mem_range_self s, rfl⟩
  have hB' : B • C.pt = -C.pt := hB
  have hBp := apply_eq_neg_of_smul_eq_neg hp hB'
  -- the lift of `φ`
  obtain ⟨e₀, he₀⟩ := hE.surjective (φ (E 0))
  obtain ⟨ψ, ⟨-, hψ⟩, -⟩ := hE.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨φ ∘ E, φ.continuous.comp hEc⟩ 0 e₀ he₀
  have hψE : E ∘ ψ = φ ∘ E := hψ
  have hl : IsLocalHomeomorph (φ ∘ E) :=
    φ.isLocalHomeomorph.comp hE.isCoveringMap.isLocalHomeomorph
  -- two developing maps of the antipodal circle along `φ ∘ E`
  have hd₁ : C.antipode.IsDevAlong (φ ∘ E) (linkMove B hB ∘ (linkCover C.pt θ ∘ D)) := fun s => by
    obtain ⟨A₀, hA₀⟩ := hiso (E s)
    obtain ⟨A₁, hA₁⟩ := hd s
    refine ⟨gammaMove B hB A₁ * A₀⁻¹, ?_⟩
    filter_upwards [hA₁, hEc.continuousAt.eventually hA₀] with s' h1 h2
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, linkMove_smul, mul_smul, h2, inv_smul_smul]
  have hd₂ : C.antipode.IsDevAlong (φ ∘ E) (linkNeg C.pt ∘ ((linkCover C.pt θ ∘ D) ∘ ψ)) := by
    rw [← hψE]
    exact (hd.comp_reparam ψ.continuous).antipode
  obtain ⟨A, hA, -⟩ := hd₁.existsUnique_eq_smul hl hd₂
  have h0 := hA 0
  simp only [Function.comp_apply] at h0
  -- the chirality
  have hc : chirality (-C.pt) (linkNeg C.pt (linkCover C.pt θ (D (ψ 0)))) =
      chirality (-C.pt) (A • linkMove B hB (linkCover C.pt θ (D 0))) := congrArg _ h0
  rw [chirality_linkNeg] at hc
  have key := chirality_smul_linkMove_pos_iff hp hB' hBp A (hdS 0)
  have hcst := pos_iff_pos_of_ne_zero ((continuous_chirality C.pt).comp hdc)
    (fun s => chirality_ne_zero hp (hdS s)) 0 (ψ 0)
  have hne0 := chirality_ne_zero hp (hdS 0)
  have hne1 := chirality_ne_zero hp (hdS (ψ 0))
  simp only [Function.comp_apply] at hcst hne0 hne1
  have key' : 0 < -chirality C.pt (linkCover C.pt θ (D (ψ 0))) ↔
      0 < chirality C.pt (linkCover C.pt θ (D 0)) := by
    rw [hc]; exact key
  rcases lt_or_gt_of_ne hne0 with h0' | h0'
  · have h1 : ¬ 0 < chirality C.pt (linkCover C.pt θ (D (ψ 0))) := fun h => (not_lt.2 h0'.le)
      (hcst.2 h)
    have h2 : ¬ 0 < -chirality C.pt (linkCover C.pt θ (D (ψ 0))) := fun h => (not_lt.2 h0'.le)
      (key'.1 h)
    exact hne1 (le_antisymm (not_lt.1 h1) (by linarith [not_lt.1 h2]))
  · have h1 := hcst.1 h0'
    have h2 := key'.2 h0'
    linarith

/-- **There is a Misner singularity at every `p ∈ dS²`**: the quotient of a space-like component of
`{x | x < f x}` by `f`, `f` the lift with a fixed point of some `ρ ∈ Γ_p ∖ {1}` or of its
inverse (`GX.exists_gammaLinkCircle_quotient_of_lt_apply`). -/
theorem exists_misner {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
      ∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde),
        IsOrientedTangent C.pt θ ∧ C.IsLiftedDev θ E D f ∧ GTilde.IsHyperbolic f ∧
        (∃ x, f x = x) ∧
        linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  obtain ⟨A, g, hA1, hg, hfix, hh⟩ := exists_gammaP_lift_fixed hp θ
  -- a space-like direction and a lift of it
  have hp1 := norm_snd_of_deSitter hp
  have hj := tpMk_jVec_ne_zero p hp1
  have hσ₀ : 0 < Causal.Flat.minkQ (dsProj p (dirOf p (jVec p))) := by
    have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
    have hc : 0 < ‖tpMk p (jVec p)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hj)
    rw [dsProj_dirOf p hj, perpLin_apply, Causal.Flat.minkB_comm, minkB_jVec, zero_smul, sub_zero,
      Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul, minkQ_jVec, hp1]
    positivity
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective p θ (dirOf p (jVec p))
  have hS₀ : 0 < Causal.Flat.minkQ (dsProj p (linkCover p θ t₀)) := ht₀ ▸ hσ₀
  -- the quotient of the component of `{x < f x}` through `t₀`
  have main : ∀ (ρ : GammaP p) (f : GTilde), ρ ≠ 1 →
      (∀ t, linkCover p θ (f t) = ρ • linkCover p θ t) → (∃ x, f x = x) →
      GTilde.IsHyperbolic f → t₀ < f t₀ →
      ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
        ∃ (θ' : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f' : GTilde),
          IsOrientedTangent C.pt θ' ∧ C.IsLiftedDev θ' E D f' ∧ GTilde.IsHyperbolic f' ∧
          (∃ x, f' x = x) ∧
          linkCover C.pt θ' '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} := by
    intro ρ f hρ1 hf hfix' hh' hlt
    obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψr, hψf, hdev⟩ :=
      exists_gammaLinkCircle_quotient_of_lt_apply p (isCoveringMap_linkCover p θ).isLocalHomeomorph
        hlt hf
    refine ⟨L, inferInstance, ⟨p, cs, hcs, hL⟩, rfl, θ, E, ψ, f, hθ, ⟨hE, hψc, hψm, hdev, hψf⟩, hh',
      hfix', ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hψr] at hx
    have hqc : Continuous fun t => Causal.Flat.minkQ (dsProj p (linkCover p θ t)) :=
      Causal.Flat.continuous_minkQ.comp
        ((continuous_dsProj p).comp (isCoveringMap_linkCover p θ).continuous)
    by_contra hneg
    have hqx : Causal.Flat.minkQ (dsProj p (linkCover p θ x)) ≤ 0 := not_lt.1 hneg
    obtain ⟨y, hy, hy0⟩ := isPreconnected_connectedComponentIn.intermediate_value hx
      (mem_connectedComponentIn hlt) hqc.continuousOn ⟨hqx, hS₀.le⟩
    have hfy := (fixed_iff_null hp hρ1 hf hfix' y).2 hy0
    have hy' : y ∈ {x : ℝ | x < f x} := connectedComponentIn_subset _ _ hy
    change y < f y at hy'
    rw [hfy] at hy'
    exact lt_irrefl _ hy'
  have hne : g t₀ ≠ t₀ := fun h => hS₀.ne' ((fixed_iff_null hp hA1 hg hfix t₀).1 h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine main A⁻¹ g⁻¹ (inv_ne_one.2 hA1) (fun t => ?_) ?_ ?_ ?_
    · have := hg (g⁻¹ t)
      rw [GTilde.apply_inv_apply] at this
      rw [this, inv_smul_smul]
    · obtain ⟨x, hx⟩ := hfix
      refine ⟨x, ?_⟩
      conv_lhs => rw [← hx]
      exact GTilde.inv_apply_apply g x
    · unfold GTilde.IsHyperbolic PSL2.IsHyperbolic
      rw [map_inv, GTilde.trSq_inv]
      exact hh
    · have := (GTilde.strictMono g⁻¹) hlt
      rwa [GTilde.inv_apply_apply] at this
  · exact main A g hA1 hg hfix hh hlt

/-- `bbsrem:p_p`, **the space-like sentence, is false as printed** (l.936–937, « when `p` is
space-like, `p̄` and `−p̄`, as HS-singularities, are always isomorphic »), in the moved-`p` reading
of « isomorphic » (OQ-120 (a)): at every `p ∈ dS²` there is a Misner `(Γ_p, ℓ(p))`-circle `L`
whose antipodal circle `L⁻` (the link of `−p̄` in `𝔢(L)`, `GX.GammaLinkCircle.DevData.isIso_flip`)
is isomorphic to `L` through no `B ∈ SO₀(1,2)` with `B • p = −p`. Such moves exist
(`GX.exists_smul_eq_neg`), and the notion is not empty (`GX.regular_isIsoVia_antipode`). -/
theorem exists_misner_not_isIsoVia_antipode {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
      (∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde),
        IsOrientedTangent C.pt θ ∧ C.IsLiftedDev θ E D f ∧ GTilde.IsHyperbolic f ∧
        (∃ x, f x = x) ∧
        linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)}) ∧
      ∀ (B : Causal.Flat.lorentz 2) (hB : B • C.pt = C.antipode.pt) (φ : L ≃ₜ L),
        ¬ C.IsIsoVia C.antipode B hB φ := by
  obtain ⟨L, _, C, hCp, θ, E, D, f, hθ, h, hh, hfix, hS⟩ := exists_misner hp
  exact ⟨L, inferInstance, C, hCp, ⟨θ, E, D, f, hθ, h, hh, hfix, hS⟩,
    fun B hB φ => h.not_isIsoVia_antipode (hCp ▸ hp) hS B hB φ⟩

/-- **A move sending `p ∈ dS²` to `−p`**: the half-turn about the time-like normal
`π_p(e_t)` of `p` (`GX.gammaHalfTurn` at the ray of that normal). -/
theorem exists_smul_eq_neg {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ B : Causal.Flat.lorentz 2, B • p = -p := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hn := isFutureTimelike_perpLin_timeUnit p hQ
  have hn0 : perpLin p (Causal.Flat.timeUnit 2) ≠ 0 := fun h0 => by
    rw [h0] at hn; exact lt_irrefl _ hn.1
  set q : HS 2 := rayNormalize p (perpLin p (Causal.Flat.timeUnit 2))
  have hq : (q : 𝕄) = ‖perpLin p (Causal.Flat.timeUnit 2)‖⁻¹ • perpLin p (Causal.Flat.timeUnit 2) :=
    coe_rayNormalize p hn0
  have hqQ : Causal.Flat.minkQ (q : 𝕄) < 0 := by
    rw [hq, Causal.Flat.minkQ_smul]
    have : 0 < (‖perpLin p (Causal.Flat.timeUnit 2)‖⁻¹) ^ 2 :=
      pow_pos (inv_pos.2 (norm_pos_iff.2 hn0)) 2
    nlinarith [hn.2]
  refine ⟨(gammaHalfTurn (p := q) hqQ : Causal.Flat.lorentz 2), ?_⟩
  have hBp : (((gammaHalfTurn (p := q) hqQ : GammaP q) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) p =
      -(p : 𝕄) := by
    show halfTurnLin q p = -(p : 𝕄)
    rw [halfTurnLin_apply, hq, Causal.Flat.minkB_smul_left, Causal.Flat.minkB_comm,
      minkB_perpLin, mul_zero, mul_zero, zero_div, zero_smul, add_zero]
  apply Subtype.ext
  rw [coe_hs_smul, hBp, coe_neg_hs, norm_neg, norm_raySphere, inv_one, one_smul]

theorem GammaLinkCircle.regular_chartAt (p : HS 2) (x y : Link p) :
    @chartAt (Link (GammaLinkCircle.regular p).pt) _ (Link p) _ (GammaLinkCircle.regular p).atlas
      x y = y := rfl

/-- The moved-`p` notion is not empty: the link `ℓ(p)` of a regular point is isomorphic to its
antipodal circle through every move `B` with `B • p = −p`. -/
theorem regular_isIsoVia_antipode (p : HS 2) (B : Causal.Flat.lorentz 2)
    (hB : B • (GammaLinkCircle.regular p).pt = (GammaLinkCircle.regular p).antipode.pt) :
    ∃ φ : Link p ≃ₜ Link p,
      (GammaLinkCircle.regular p).IsIsoVia (GammaLinkCircle.regular p).antipode B hB φ := by
  refine ⟨(linkMove B hB).trans (linkNeg p).symm, fun x => ⟨1, Eventually.of_forall fun y => ?_⟩⟩
  rw [one_smul, GammaLinkCircle.antipode_chartAt, GammaLinkCircle.regular_chartAt,
    GammaLinkCircle.regular_chartAt]
  exact (linkNeg p).apply_symm_apply (linkMove B hB y)

end Misner

/-! ## 11. A move `p ↦ −p` is an involution and conjugates `Γ_p` by inversion -/

section NonMisner

/-- **`vol3 p` is a fixed non-zero multiple of the area form of `T_p HS²`.** -/
theorem exists_vol3_eq_linkArea (p : HS 2) :
    ∃ K : ℝ, K ≠ 0 ∧ ∀ w₁ w₂ : 𝕄, vol3 p w₁ w₂ = linkArea p (tpMk p w₁) (tpMk p w₂) * K := by
  set θ := tpHSEquiv p
  obtain ⟨v₁, hv₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm 1)
  obtain ⟨v₂, hv₂⟩ := Submodule.Quotient.mk_surjective _ (θ.symm Complex.I)
  refine ⟨vol3 p v₁ v₂, vol3_ne_zero p θ hv₁ hv₂, fun w₁ w₂ => ?_⟩
  have hdecomp : ∀ w : 𝕄, (Submodule.Quotient.mk w : TpHS p) =
      Submodule.Quotient.mk ((θ (tpMk p w)).re • v₁ + (θ (tpMk p w)).im • v₂) := fun w => by
    apply θ.injective
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, hv₁, hv₂,
      map_add, map_smul, map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    apply Complex.ext <;> simp
  rw [vol3_eq_of_mk_eq p (hdecomp w₁) (hdecomp w₂), vol3_lin, linkArea_eq]

/-- The map `R = T_{−p}^{-1} ∘ B` of `T_p HS²` induced by a move `B` with `B p = −p`. -/
def tpReflect {p : HS 2} (B : Causal.Flat.lorentz 2) (h : B • p = -p) : TpHS p ≃ₗ[ℝ] TpHS p :=
  (tpMove B h).trans (tpNeg p).symm

theorem tpReflect_mk {p : HS 2} (B : Causal.Flat.lorentz 2) (h : B • p = -p) (w : 𝕄) :
    tpReflect B h (tpMk p w) = tpMk p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) := rfl

/-- **`R` reverses the area** (`B` preserves the orientation of `ℝ^{1,2}` and sends `p` to `−p`). -/
theorem linkArea_tpReflect {p : HS 2} {B : Causal.Flat.lorentz 2} (h : B • p = -p)
    (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) (x y : TpHS p) :
    linkArea p (tpReflect B h x) (tpReflect B h y) = -linkArea p x y := by
  obtain ⟨K, hK, hvol⟩ := exists_vol3_eq_linkArea p
  induction x using Submodule.Quotient.induction_on with
  | H w₁ =>
  induction y using Submodule.Quotient.induction_on with
  | H w₂ =>
  have e1 := hvol ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₁) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₂)
  have e2 := hvol w₁ w₂
  have e3 : vol3 p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₁) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₂) = -vol3 p w₁ w₂ := by
    have := vol3_lorentz B p w₁ w₂
    rw [hBp, vol3_neg_left] at this
    linarith
  change linkArea p (tpMk p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₁)) (tpMk p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₂)) =
    -linkArea p (tpMk p w₁) (tpMk p w₂)
  have : (linkArea p (tpMk p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₁)) (tpMk p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₂)) +
      linkArea p (tpMk p w₁) (tpMk p w₂)) * K = 0 := by
    rw [add_mul, ← e1, ← e2, e3]; ring
  have := (mul_eq_zero.1 this).resolve_right hK
  linarith

/-- `π_p ∘ R = B ∘ π_p`: `R` is an isometry of `Q ∘ π_p`. -/
theorem dsProj_tpReflect {p : HS 2} {B : Causal.Flat.lorentz 2} (h : B • p = -p)
    (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) (x : TpHS p) :
    dsProj p (tpReflect B h x) = (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p x) := by
  induction x using Submodule.Quotient.induction_on with
  | H w =>
  have hBw : Causal.Flat.minkB (p : 𝕄) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = -Causal.Flat.minkB (p : 𝕄) w := by
    have := Causal.Flat.lorentz.minkB_apply B.2 p w
    rw [hBp, Causal.Flat.minkB_neg_left] at this
    linarith
  show perpLin p ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = (B : 𝕄 ≃ₗ[ℝ] 𝕄) (perpLin p w)
  rw [perpLin_apply, perpLin_apply, map_sub, map_smul, map_smul, hBw, hBp, neg_smul, smul_neg,
    sub_neg_eq_add]

/-- The area of two combinations of `u, v` in `T_p HS²`. -/
theorem linkArea_comb (p : HS 2) (u v : TpHS p) (a c a' c' : ℝ) :
    linkArea p (a • u + c • v) (a' • u + c' • v) = (a * c' - c * a') * linkArea p u v := by
  simp only [linkArea_eq, map_add, map_smul, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  ring

/-- The Minkowski product of two combinations of two null vectors. -/
theorem minkB_comb_of_null {x y : 𝕄} (hx : Causal.Flat.minkQ x = 0) (hy : Causal.Flat.minkQ y = 0)
    (a c a' c' : ℝ) :
    Causal.Flat.minkB (a • x + c • y) (a' • x + c' • y) =
      (a * c' + c * a') * Causal.Flat.minkB x y := by
  rw [Causal.Flat.minkQ_eq_minkB] at hx hy
  simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_left,
    Causal.Flat.minkB_smul_right, hx, hy, Causal.Flat.minkB_comm y x]
  ring

/-- **A move sending `p ∈ dS²` to `−p` is an involution**: `N p = −p` gives `N² = 1`. On
`T_p HS²`, `R = [N]` reverses the area and preserves `Q ∘ π_p`, so it exchanges the two light-like
lines, `R n₁ = c n₂`, `R n₂ = a n₁` with `a c = 1`; then `R² = 1`, and `N² ∈ Γ_p` acts trivially on
`T_p HS²`. -/
theorem mul_self_eq_one_of_apply_neg {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    {N : Causal.Flat.lorentz 2} (hNp : (N : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) : N * N = 1 := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have h : N • p = -p := by
    apply Subtype.ext
    rw [coe_hs_smul, hNp, coe_neg_hs, norm_neg, norm_raySphere, inv_one, one_smul]
  set R := tpReflect N h
  have hω : ∀ x y, linkArea p (R x) (R y) = -linkArea p x y := linkArea_tpReflect h hNp
  have hD : ∀ x, dsProj p (R x) = (N : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p x) := dsProj_tpReflect h hNp
  obtain ⟨n₁, n₂, h₁, h₂, h12⟩ := exists_two_null hp
  set u : TpHS p := (n₁ : TpHS p)
  set v : TpHS p := (n₂ : TpHS p)
  have hu0 : dsProj p u ≠ 0 := dsProj_ne_zero p hQ.ne' n₁
  -- `u, v` is a basis, and `B(π u, π v) ≠ 0`
  have hωuv : linkArea p u v ≠ 0 := fun h0 => by
    obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero p (raySphere_ne_zero n₁) h0
    exact h12 r hr
  have hbuv : Causal.Flat.minkB (dsProj p u) (dsProj p v) ≠ 0 := fun h0 => by
    obtain ⟨c, hc⟩ := Causal.Flat.eq_smul_of_null_orth h₁ hu0 h₂ h0
    exact h12 c (dsProj_injective p hQ.ne' (by rw [hc, map_smul]))
  -- `R u` and `R v` in the basis `u, v`
  have hcr : ∀ z, ∃ a c : ℝ, z = a • u + c • v := fun z =>
    ⟨_, _, eq_add_of_linkArea_ne_zero p hωuv z⟩
  obtain ⟨a₁, c₁, e₁⟩ := hcr (R u)
  obtain ⟨a₂, c₂, e₂⟩ := hcr (R v)
  have hdcomb : ∀ a c : ℝ, dsProj p (a • u + c • v) = a • dsProj p u + c • dsProj p v := fun a c => by
    rw [map_add, map_smul, map_smul]
  -- `R` maps null vectors to null vectors
  have hnull : ∀ {z : TpHS p} {a c : ℝ}, Causal.Flat.minkQ (dsProj p z) = 0 → R z = a • u + c • v →
      a * c = 0 := fun {z a c} hz hRz => by
    have e := Causal.Flat.lorentz.minkQ_apply N.2 (dsProj p z)
    rw [← hD, hRz, hdcomb, Causal.Flat.minkQ_eq_minkB, minkB_comb_of_null h₁ h₂, hz] at e
    have : a * c * (2 * Causal.Flat.minkB (dsProj p u) (dsProj p v)) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right (mul_ne_zero two_ne_zero hbuv)
  have h1 : a₁ * c₁ = 0 := hnull h₁ e₁
  have h2 : a₂ * c₂ = 0 := hnull h₂ e₂
  have h3 : a₁ * c₂ - c₁ * a₂ = -1 := by
    have e := hω u v
    rw [e₁, e₂, linkArea_comb] at e
    have : (a₁ * c₂ - c₁ * a₂ + 1) * linkArea p u v = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hωuv
    linarith
  have h4 : a₁ * c₂ + c₁ * a₂ = 1 := by
    have e := Causal.Flat.lorentz.minkB_apply N.2 (dsProj p u) (dsProj p v)
    rw [← hD, ← hD, e₁, e₂, hdcomb, hdcomb, minkB_comb_of_null h₁ h₂] at e
    have : (a₁ * c₂ + c₁ * a₂ - 1) * Causal.Flat.minkB (dsProj p u) (dsProj p v) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hbuv
    linarith
  have ha₁ : a₁ = 0 := by linear_combination (-a₁ / 2) * (h4 - h3) + a₂ * h1
  have hc₂ : c₂ = 0 := by linear_combination (-c₂ / 2) * (h4 - h3) + c₁ * h2
  have hca : c₁ * a₂ = 1 := by rw [ha₁, zero_mul, zero_sub] at h3; linarith
  -- `R² = 1`
  have hRu : R u = c₁ • v := by rw [e₁, ha₁, zero_smul, zero_add]
  have hRv : R v = a₂ • u := by rw [e₂, hc₂, zero_smul, add_zero]
  have hRR : ∀ z, R (R z) = z := fun z => by
    obtain ⟨α, β, hz⟩ := hcr z
    have hRRu : R (R u) = u := by rw [hRu, map_smul, hRv, smul_smul, hca, one_smul]
    have hRRv : R (R v) = v := by rw [hRv, map_smul, hRu, smul_smul, mul_comm, hca, one_smul]
    rw [hz, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hRRu, hRRv]
  -- `N² ∈ Γ_p` acts trivially on `T_p HS²`
  have hmem : N * N ∈ GammaP p := by
    show (N : 𝕄 ≃ₗ[ℝ] 𝕄) ((N : 𝕄 ≃ₗ[ℝ] 𝕄) p) = p
    rw [hNp, map_neg, hNp, neg_neg]
  have hone : (⟨N * N, hmem⟩ : GammaP p) = 1 := gammaP_eq_one_of_tangent p fun z => by
    induction z using Submodule.Quotient.induction_on with
    | H w => exact hRR (tpMk p w)
  exact congrArg Subtype.val hone

/-- **`B Γ_p B⁻¹ = Γ_p` by inversion** at `p ∈ dS²`: for a move `B` with `B p = −p` and `ρ ∈ Γ_p`,
`B ρ B⁻¹ = ρ⁻¹`. `B` and `B ρ` both send `p` to `−p`, so both are involutions
(`GX.mul_self_eq_one_of_apply_neg`). -/
theorem conj_eq_inv_of_neg {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {B : Causal.Flat.lorentz 2}
    (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) (ρ : GammaP p) :
    B * (ρ : Causal.Flat.lorentz 2) * B⁻¹ = (ρ : Causal.Flat.lorentz 2)⁻¹ := by
  have hB := mul_self_eq_one_of_apply_neg hp hBp
  have hBρ := mul_self_eq_one_of_apply_neg hp (N := B * (ρ : Causal.Flat.lorentz 2)) (by
    show (B : 𝕄 ≃ₗ[ℝ] 𝕄) (((ρ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) p) = -(p : 𝕄)
    rw [show ((ρ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) p = p from ρ.2, hBp])
  have hBi : B⁻¹ = B := (eq_inv_of_mul_eq_one_left hB).symm
  rw [hBi]
  calc B * (ρ : Causal.Flat.lorentz 2) * B
      = B * (ρ : Causal.Flat.lorentz 2) * B * (ρ : Causal.Flat.lorentz 2) *
          (ρ : Causal.Flat.lorentz 2)⁻¹ := by group
    _ = (ρ : Causal.Flat.lorentz 2)⁻¹ := by
      rw [show B * (ρ : Causal.Flat.lorentz 2) * B * (ρ : Causal.Flat.lorentz 2) =
        (B * (ρ : Causal.Flat.lorentz 2)) * (B * (ρ : Causal.Flat.lorentz 2)) by group, hBρ,
        one_mul]

end NonMisner

/-! ## 12. Non-Misner links: the antipodal link through a move -/

section NonMisnerIso

/-- `ℓ(−p) ≅ ℓ(p)` reads as `T_{−p} HS² = T_p HS²`. -/
theorem coe_linkNeg_symm (p : HS 2) (τ : Link (-p)) :
    (((linkNeg p).symm τ : Link p) : TpHS p) = (tpNeg p).symm τ := by
  have h := coe_linkNeg p ((linkNeg p).symm τ)
  rw [Homeomorph.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]

variable {p : HS 2} {B : Causal.Flat.lorentz 2}

/-- `π_{−p} ∘ [B] = B ∘ π_p` for a move `B` with `B p = −p`. -/
theorem dsProj_tpMove_neg (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    (z : TpHS p) : dsProj (-p) (tpMove B h z) = (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p z) := by
  induction z using Submodule.Quotient.induction_on with
  | H w =>
  have hBw : Causal.Flat.minkB (p : 𝕄) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = -Causal.Flat.minkB (p : 𝕄) w := by
    have := Causal.Flat.lorentz.minkB_apply B.2 p w
    rw [hBp, Causal.Flat.minkB_neg_left] at this
    linarith
  show perpLin (-p) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = (B : 𝕄 ≃ₗ[ℝ] 𝕄) (perpLin p w)
  rw [perpLin_neg, perpLin_apply, perpLin_apply, map_sub, map_smul, map_smul, hBw, hBp, neg_smul,
    smul_neg, sub_neg_eq_add]

/-- **The reflection `R̂ = ℓ(−p)^{-1} ∘ B` of `ℓ(p)`** induced by a move `B` with `B • p = −p`:
a direction at `p`, moved by `B` to `−p`, read back at `p`. -/
def linkReflect (B : Causal.Flat.lorentz 2) (h : B • p = -p) : Link p ≃ₜ Link p :=
  (linkMove B h).trans (linkNeg p).symm

theorem linkReflect_apply (h : B • p = -p) (σ : Link p) :
    linkReflect B h σ = (linkNeg p).symm (linkMove B h σ) := rfl

/-- At `p ∈ dS²`, `B Γ_p B⁻¹ = Γ_p` by inversion, read in `Γ_{−p}`. -/
theorem gammaMove_eq_gammaNeg_inv (hp : p ∈ HS.piece 2 .deSitter) (h : B • p = -p)
    (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) (A : GammaP p) :
    gammaMove B h A = gammaNeg p A⁻¹ := by
  apply Subtype.ext
  rw [coe_gammaMove, coe_gammaNeg, conj_eq_inv_of_neg hp hBp A]
  rfl

/-- **`R̂` conjugates `Γ_p` by inversion**: `R̂ (A σ) = A⁻¹ R̂ σ`. -/
theorem linkReflect_smul (hp : p ∈ HS.piece 2 .deSitter) (h : B • p = -p)
    (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄)) (A : GammaP p) (σ : Link p) :
    linkReflect B h (A • σ) = A⁻¹ • linkReflect B h σ := by
  rw [linkReflect_apply, linkReflect_apply, linkMove_smul, gammaMove_eq_gammaNeg_inv hp h hBp,
    Homeomorph.symm_apply_eq, linkNeg_smul, Homeomorph.apply_symm_apply]

theorem dsProj_linkReflect (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    (σ : Link p) :
    dsProj p (linkReflect B h σ) = ‖tpMove B h σ‖⁻¹ • (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p σ) := by
  rw [linkReflect_apply, coe_linkNeg_symm, ← dsProj_tpNeg p, LinearEquiv.apply_symm_apply,
    coe_linkMove, map_smul, dsProj_tpMove_neg h hBp]

/-- `R̂` keeps the light-like directions. -/
theorem minkQ_dsProj_linkReflect (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    (σ : Link p) :
    Causal.Flat.minkQ (dsProj p (linkReflect B h σ)) =
      (‖tpMove B h σ‖⁻¹) ^ 2 * Causal.Flat.minkQ (dsProj p σ) := by
  rw [dsProj_linkReflect h hBp, Causal.Flat.minkQ_smul, Causal.Flat.lorentz.minkQ_apply B.2]

theorem isFutureTimelike_smul_lorentz {c : ℝ} (hc : 0 < c) {v : 𝕄}
    (hv : Causal.Flat.IsFutureTimelike v) :
    Causal.Flat.IsFutureTimelike (c • (B : 𝕄 ≃ₗ[ℝ] 𝕄) v) := by
  have hBv := Causal.Flat.lorentz.isFutureTimelike_apply B.2 hv
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos hc hBv.1
  · rw [Causal.Flat.minkQ_smul]; exact mul_neg_of_pos_of_neg (pow_pos hc 2) hBv.2

/-- **`R̂` keeps `i⁺` and `i⁻`** (`B` is orthochronous, `T_p = T_{−p}` keeps the time-like
directions). -/
theorem linkReflect_mem_dsFutureDirs (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    {σ : Link p} (hσ : σ ∈ dsFutureDirs p) : linkReflect B h σ ∈ dsFutureDirs p := by
  show Causal.Flat.IsFutureTimelike (dsProj p (linkReflect B h σ))
  rw [dsProj_linkReflect h hBp]
  exact isFutureTimelike_smul_lorentz (inv_pos.2 (norm_pos_iff.2
    ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero σ)))) hσ

theorem linkReflect_mem_dsPastDirs (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    {σ : Link p} (hσ : σ ∈ dsPastDirs p) : linkReflect B h σ ∈ dsPastDirs p := by
  show Causal.Flat.IsFutureTimelike (-dsProj p (linkReflect B h σ))
  rw [dsProj_linkReflect h hBp, ← smul_neg, ← map_neg]
  exact isFutureTimelike_smul_lorentz (inv_pos.2 (norm_pos_iff.2
    ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero σ)))) hσ

/-- The identification `θ_B = θ⁻ ∘ [B]` of `T_p HS²` (`θ⁻ = tangentNeg θ` at `−p`). -/
def tangentMove (B : Causal.Flat.lorentz 2) (h : B • p = -p) (θ : TpHS p ≃ₗ[ℝ] ℂ) :
    TpHS p ≃ₗ[ℝ] ℂ :=
  (tpMove B h).trans (tangentNeg p θ)

/-- `θ_B` is oriented when `θ` is (`B` keeps `vol3` and sends `p` to `−p`). -/
theorem isOrientedTangent_tangentMove (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ) :
    IsOrientedTangent p (tangentMove B h θ) := by
  intro w₁ w₂ h₁ h₂
  have h₁' : tpMk (-p) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₁) = (tangentNeg p θ).symm 1 := by
    rw [← tpMove_mk B h, show tpMk p w₁ = _ from h₁, tangentMove, LinearEquiv.symm_trans_apply,
      LinearEquiv.apply_symm_apply]
  have h₂' : tpMk (-p) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w₂) = (tangentNeg p θ).symm Complex.I := by
    rw [← tpMove_mk B h, show tpMk p w₂ = _ from h₂, tangentMove, LinearEquiv.symm_trans_apply,
      LinearEquiv.apply_symm_apply]
  have := isOrientedTangent_tangentNeg p hθ _ _ h₁' h₂'
  rwa [coe_neg_hs, ← hBp, vol3_lorentz] at this

/-- `B` reads `linkCover` through `θ_B` at `p` as `linkCover` through `θ⁻` at `−p`. -/
theorem linkMove_linkCover (h : B • p = -p) (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    linkMove B h (linkCover p (tangentMove B h θ) t) = linkCover (-p) (tangentNeg p θ) t := by
  apply Subtype.ext
  have hne : (tangentNeg p θ).symm (Circle.exp (Real.pi * t)) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 (Circle.coe_ne_zero _)
  have hne' : (tpMove B h).symm ((tangentNeg p θ).symm (Circle.exp (Real.pi * t))) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 hne
  rw [coe_linkMove, coe_linkCover, coe_linkCover, tangentMove, LinearEquiv.symm_trans_apply,
    map_smul, LinearEquiv.apply_symm_apply,
    normalize_smul_pos (inv_pos.2 (norm_pos_iff.2 hne'))]

/-- **`R̂` read on `ℝP̃¹`**: for `θ` oriented there is `F ∈ G̃` (the lift of the change of
identification `θ → θ_B`, `GX.exists_rayLift`) with `R̂ (linkCover θ t) = linkCover θ (−F t)`, so
`R̂` lifts to the decreasing homeomorphism `t ↦ −F t` of `ℝP̃¹`. -/
theorem exists_linkReflect_linkCover (h : B • p = -p) (hBp : (B : 𝕄 ≃ₗ[ℝ] 𝕄) p = -(p : 𝕄))
    {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ) :
    ∃ F : GTilde, ∀ t, linkReflect B h (linkCover p θ t) = linkCover p θ (-F t) := by
  obtain ⟨g₀, hg₀⟩ := linkToRP1_eq_smul p hθ (isOrientedTangent_tangentMove h hBp hθ)
  obtain ⟨F, hF⟩ := exists_rayLift p hg₀ 1
  refine ⟨F, fun t => ?_⟩
  rw [← one_smul (GammaP p) (linkCover p θ t), ← hF, linkReflect_apply, linkMove_linkCover,
    linkCover_tangentNeg, Homeomorph.symm_apply_apply]

/-- Two open intervals whose ends satisfy `P`, with no point satisfying `P` inside, and which
meet, are equal. -/
theorem Ioo_eq_of_ends {P : ℝ → Prop} {a b c d : ℝ} (ha : P a) (hb : P b) (hc : P c) (hd : P d)
    (hab : ∀ t ∈ Ioo a b, ¬ P t) (hcd : ∀ t ∈ Ioo c d, ¬ P t) {t : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t ∈ Ioo c d) : Ioo a b = Ioo c d := by
  have h1 : a = c := by
    rcases lt_trichotomy a c with h | h | h
    · exact absurd hc (hab c ⟨h, by linarith [ht'.1, ht.2]⟩)
    · exact h
    · exact absurd ha (hcd a ⟨h, by linarith [ht.1, ht'.2]⟩)
  have h2 : b = d := by
    rcases lt_trichotomy b d with h | h | h
    · exact absurd hb (hcd b ⟨by linarith [ht'.1, ht.2], h⟩)
    · exact h
    · exact absurd hd (hab d ⟨by linarith [ht.1, ht'.2], h⟩)
  rw [h1, h2]

variable {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
  {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- **A non-Misner link is isomorphic to its antipodal link through every move** (l.936–937, the
strongest true form of the space-like sentence): at `p ∈ dS²`, if the developed image of `L` is
not space-like (`L` BTZ-like, l.870–875, or of degree `k ≠ 0`, l.893–915), then for every
`B ∈ SO₀(1,2)` with `B • p = −p` there is a homeomorphism `φ : L → L` which is an isomorphism of
`L` onto the antipodal circle `L⁻` (the link of `−p̄`) through `B`. The reflection `R̂` of `ℓ(p)`
induced by `B` conjugates the holonomy `ρ` to `ρ⁻¹` (`GX.linkReflect_smul`) and keeps `i^±`; its
lift `t ↦ −F t` conjugates the lifted holonomy `f` to `f⁻¹` (both lift `ρ⁻¹`, and they agree on a
light-like lift), and maps the developed image onto itself up to `δ^{2j}`; `φ` descends
`D⁻¹ ∘ (−F − 2j) ∘ D`. -/
theorem GammaLinkCircle.IsLiftedDev.exists_isIsoVia_antipode (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .deSitter)
    (hS : ¬ linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)})
    (B : Causal.Flat.lorentz 2) (hB : B • C.pt = C.antipode.pt) :
    ∃ φ : L ≃ₜ L, C.IsIsoVia C.antipode B hB φ := by
  have hB' : B • C.pt = -C.pt := hB
  have hBp := apply_eq_neg_of_smul_eq_neg hp hB'
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  obtain ⟨F, hRF⟩ := exists_linkReflect_linkCover hB' hBp hθ
  obtain ⟨ρ, hρ⟩ := GammaLinkCircle.IsLiftedDev.exists_linkCover_apply ⟨hE, hDc, hDm, hd, hDf⟩
  have hρi : ∀ t, linkCover C.pt θ (f⁻¹ t) = ρ⁻¹ • linkCover C.pt θ t := fun t => by
    rw [eq_inv_smul_iff, ← hρ, GTilde.apply_inv_apply]
  have hFc : Continuous fun t => -F t := (GTilde.continuous F).neg
  -- 1. `−F (f t) = f⁻¹ (−F t) + 2n`
  obtain ⟨n, hn⟩ := linkCover_lift_eq C.pt (θ := θ) (g₁ := fun t => -F (f t))
    (g₂ := fun t => f⁻¹ (-F t)) (hFc.comp (GTilde.continuous f))
    ((GTilde.continuous f⁻¹).comp hFc) (fun t => by
      rw [← hRF (f t), hρ t, linkReflect_smul hp hB' hBp, hRF t, hρi])
  -- 2. `f` moves every light-like lift by the same `2m`
  obtain ⟨n₁, -, hn₁, -, -⟩ := exists_two_null hp
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective C.pt θ n₁
  have hnull0 : Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ t₀)) = 0 := ht₀ ▸ hn₁
  obtain ⟨m, hm⟩ := (linkCover_eq_linkCover_iff C.pt θ).1
    (show linkCover C.pt θ t₀ = linkCover C.pt θ (f t₀) by rw [hρ, smul_eq_of_deSitter hp hnull0])
  have hfnull : ∀ t, Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ t)) = 0 →
      f t = t + 2 * m := fun t ht => by
    set g : GTilde := GTilde.delta ^ (-(2 * m)) * f with hg_def
    have hgt : ∀ x, g x = f x - 2 * m := fun x => by
      rw [hg_def, GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
    have hgl : ∀ x, linkCover C.pt θ (g x) = ρ • linkCover C.pt θ x := fun x => by
      rw [hgt, ← hρ, show f x - 2 * (m : ℝ) = f x + 2 * ((-m : ℤ) : ℝ) by push_cast; ring,
        linkCover_add_two_mul]
    have hg0 : g t₀ = t₀ := by rw [hgt, hm]; ring
    have hgfix : g t = t := by
      by_cases hρ1 : ρ = 1
      · obtain ⟨k, hk⟩ := linkCover_lift_eq C.pt (θ := θ) (g₁ := fun x => g x) (g₂ := id)
          (GTilde.continuous g) continuous_id (fun x => by
            simp only [id]; rw [hgl, hρ1, one_smul])
        have hk0 : (k : ℝ) = 0 := by have := hk t₀; simp only [id] at this; linarith
        have := hk t
        simp only [id] at this
        rw [this, hk0, mul_zero, add_zero]
      · exact (fixed_iff_null hp hρ1 hgl ⟨t₀, hg0⟩ t).2 ht
    rw [hgt] at hgfix
    linarith
  -- 3. hence `−F ∘ f = f⁻¹ ∘ −F`
  have hK0 : Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ (-F t₀))) = 0 := by
    rw [← hRF, minkQ_dsProj_linkReflect hB' hBp, hnull0, mul_zero]
  have hn0 : (n : ℝ) = 0 := by
    have e := hn t₀
    have e1 : F (f t₀) = F t₀ + 2 * m := by
      rw [hm]; have := GTilde.map_add_int F t₀ (2 * m); push_cast at this; exact this
    have e2 : f⁻¹ (-F t₀) = -F t₀ - 2 * m := by
      have h1 := hfnull _ hK0
      have h2 : f (-F t₀ - 2 * m) = -F t₀ := by
        have := GTilde.map_add_int f (-F t₀) (-(2 * m))
        push_cast at this
        rw [sub_eq_add_neg, this, h1]; ring
      conv_lhs => rw [← h2]
      exact GTilde.inv_apply_apply _ _
    rw [e1, e2] at e
    linarith
  have hstar : ∀ t, -F (f t) = f⁻¹ (-F t) := fun t => by rw [hn t, hn0, mul_zero, add_zero]
  -- 4. `−F − 2j` maps the developed interval `range D` onto itself
  have hFi : ∀ y, -F (F⁻¹ (-y)) = y := fun y => by rw [GTilde.apply_inv_apply, neg_neg]
  have hFa : StrictAnti fun t => -F t := fun a b hab => neg_lt_neg (GTilde.strictMono F hab)
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (fun t => -F t - 2 * j) '' range D = range D := by
    letI := C.rp1ChartedSpace θ
    haveI := C.rp1_hasGroupoid θ
    have hsurj : (fun t => -F t - 2 * ((0 : ℤ) : ℝ)) '' univ = univ := by
      refine eq_univ_of_forall fun y => ⟨F⁻¹ (-y), mem_univ _, ?_⟩
      simp only [Int.cast_zero, mul_zero, sub_zero]
      exact hFi y
    rcases (GammaLinkCircle.IsLiftedDev.isLiftedDevPair ⟨hE, hDc, hDm, hd, hDf⟩).exhaust with
      ⟨-, hD⟩ | ⟨-, -, -, -, -, -, hD⟩ | ⟨hpf, x₀, x₁, -, hx₀, hx₁, hD, -, -⟩
    · exact ⟨0, by rw [hD]; exact hsurj⟩
    · exact ⟨0, by rw [hD]; exact hsurj⟩
    -- degree `0`: BTZ-like, the developed image is `i⁺` or `i⁻`
    have hne1 : GTilde.toPSL f ≠ 1 := by
      rcases hpf with hpar | hh
      · exact hpar.2
      · exact hh.toPSL_ne_one
    have hh := GammaLinkCircle.IsLiftedDev.isHyperbolic_of_deSitter ⟨hE, hDc, hDm, hd, hDf⟩ hp hne1
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      exact hne1 (by rw [toPSL_eq_of_linkCover hρ, map_one]; rfl)
    have hfn := fixed_iff_null hp hρ1 hρ ⟨x₀, hx₀⟩
    -- the image `T`: kept by `R̂`, time-like
    obtain ⟨T, hT, hRT, hTneg⟩ : ∃ T : Set (Link C.pt), linkCover C.pt θ '' range D = T ∧
        (∀ σ ∈ T, linkReflect B hB' σ ∈ T) ∧ ∀ σ ∈ T, Causal.Flat.minkQ (dsProj C.pt σ) < 0 := by
      rcases GammaLinkCircle.IsLiftedDev.spacelike_degree_zero hθ ⟨hE, hDc, hDm, hd, hDf⟩ hp hh
          ⟨x₀, hx₀⟩ with ⟨hI, -⟩ | ⟨hI, -⟩ | ⟨hI, -⟩
      · rw [iPlus_of_deSitter hp] at hI
        exact ⟨_, hI, fun σ hσ => linkReflect_mem_dsFutureDirs hB' hBp hσ,
          fun σ hσ => minkQ_neg_of_timelike (Or.inl hσ)⟩
      · rw [iMinus_of_deSitter hp] at hI
        exact ⟨_, hI, fun σ hσ => linkReflect_mem_dsPastDirs hB' hBp hσ,
          fun σ hσ => minkQ_neg_of_timelike (Or.inr hσ)⟩
      · exact absurd hI hS
    let P : ℝ → Prop := fun t => Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ t)) = 0
    have hP2 : ∀ (t : ℝ) (i : ℤ), P (t - 2 * i) ↔ P t := fun t i => by
      show Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ (t - 2 * i))) = 0 ↔
        Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ t)) = 0
      rw [show t - 2 * (i : ℝ) = t + 2 * ((-i : ℤ) : ℝ) by push_cast; ring, linkCover_add_two_mul]
    have hTin : ∀ t ∈ Ioo x₀ x₁, linkCover C.pt θ t ∈ T := fun t ht => by
      rw [← hT, hD]; exact mem_image_of_mem _ ht
    have hnotP : ∀ t ∈ Ioo x₀ x₁, ¬ P t := fun t ht h0 => (hTneg _ (hTin t ht)).ne h0
    have hKT : ∀ t ∈ Ioo x₀ x₁, linkCover C.pt θ (-F t) ∈ T := fun t ht => by
      rw [← hRF]; exact hRT _ (hTin t ht)
    have hPK : ∀ t, P t → P (-F t) := fun t ht => by
      show Causal.Flat.minkQ (dsProj C.pt (linkCover C.pt θ (-F t))) = 0
      rw [← hRF, minkQ_dsProj_linkReflect hB' hBp, show Causal.Flat.minkQ
        (dsProj C.pt (linkCover C.pt θ t)) = 0 from ht, mul_zero]
    have hP₀ : P x₀ := (hfn x₀).1 hx₀
    have hP₁ : P x₁ := (hfn x₁).1 hx₁
    -- `−F (D 0) = t' + 2i` with `t' ∈ ]x₀, x₁[`
    have hD0 : D 0 ∈ Ioo x₀ x₁ := hD ▸ mem_range_self 0
    obtain ⟨t', ht', hlc⟩ : linkCover C.pt θ (-F (D 0)) ∈ linkCover C.pt θ '' Ioo x₀ x₁ := by
      rw [← hD, hT]; exact hKT _ hD0
    obtain ⟨i, hi⟩ := (linkCover_eq_linkCover_iff C.pt θ).1 hlc
    refine ⟨i, ?_⟩
    -- the image of `]x₀, x₁[` is `]−F x₁ − 2i, −F x₀ − 2i[`
    have himg : (fun t => -F t - 2 * i) '' Ioo x₀ x₁ = Ioo (-F x₁ - 2 * i) (-F x₀ - 2 * i) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨by linarith [hFa ht.2], by linarith [hFa ht.1]⟩
      · intro hy
        refine ⟨F⁻¹ (-(y + 2 * i)), ⟨?_, ?_⟩, ?_⟩
        · by_contra hc
          have := hFa.antitone (not_lt.1 hc)
          rw [hFi] at this
          linarith [hy.2]
        · by_contra hc
          have := hFa.antitone (not_lt.1 hc)
          rw [hFi] at this
          linarith [hy.1]
        · simp only
          rw [hFi]; ring
    rw [hD, himg]
    refine Ioo_eq_of_ends (P := P) ((hP2 _ _).2 (hPK _ hP₁)) ((hP2 _ _).2 (hPK _ hP₀)) hP₀ hP₁
      (fun t ht hPt => ?_) hnotP (t := t') ?_ ht'
    · rw [← himg] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      exact (hTneg _ (hKT u hu)).ne ((hP2 _ _).1 hPt)
    · rw [← himg]
      exact ⟨D 0, hD0, by simp only; rw [hi]; ring⟩
  -- 5. `Φ = D⁻¹ ∘ K ∘ D`, `K = −F − 2j`, decreasing, `Φ (s + 1) = Φ s − 1`
  set K : ℝ → ℝ := fun t => -F t - 2 * j with hK_def
  have hKa : StrictAnti K := fun a b hab => by
    simp only [K]; linarith [GTilde.strictMono F hab]
  have hKlc : ∀ t, linkCover C.pt θ (K t) = linkReflect B hB' (linkCover C.pt θ t) := fun t => by
    rw [hRF]
    simp only [K]
    rw [show -F t - 2 * (j : ℝ) = -F t + 2 * ((-j : ℤ) : ℝ) by push_cast; ring,
      linkCover_add_two_mul]
  have hKf : ∀ t, K (f t) = f⁻¹ (K t) := fun t => by
    simp only [K]
    rw [hstar, show -F t - 2 * (j : ℝ) = -F t + ((-(2 * j) : ℤ) : ℝ) by push_cast; ring,
      GTilde.map_add_int]
    push_cast; ring
  have hKfi : ∀ t, K (f⁻¹ t) = f (K t) := fun t => by
    have := hKf (f⁻¹ t)
    rw [GTilde.apply_inv_apply] at this
    rw [this, GTilde.apply_inv_apply]
  have hDi : ∀ s, D (s - 1) = f⁻¹ (D s) := fun s => by
    have := hDf (s - 1)
    rw [sub_add_cancel] at this
    rw [this, GTilde.inv_apply_apply]
  have hex : ∀ s, ∃ s', D s' = K (D s) := fun s => by
    have : K (D s) ∈ range D := hj ▸ mem_image_of_mem K (mem_range_self s)
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  have hex' : ∀ t, ∃ s, K (D s) = D t := fun t => by
    have : D t ∈ K '' range D := hj.symm ▸ mem_range_self t
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := this
    exact ⟨s, hs⟩
  choose Φ hΦ using hex
  choose Ψ hΨ using hex'
  have hΦΨ : ∀ t, Φ (Ψ t) = t := fun t => hDm.injective (by rw [hΦ, hΨ])
  have hΨΦ : ∀ s, Ψ (Φ s) = s := fun s => hDm.injective (hKa.injective (by rw [hΨ, hΦ]))
  have hΦa : StrictAnti Φ := fun a b hab => by
    rw [← hDm.lt_iff_lt, hΦ, hΦ]; exact hKa (hDm hab)
  have hΨa : StrictAnti Ψ := fun a b hab => by
    rw [← hKa.lt_iff_gt.trans hDm.lt_iff_lt, hΨ, hΨ]; exact hDm hab
  have hΦc : Continuous Φ := by
    have hm : Monotone fun s => -Φ s := fun a b hab => neg_le_neg (hΦa.antitone hab)
    have := hm.continuous_of_surjective fun y => ⟨Ψ (-y), by simp only [hΦΨ, neg_neg]⟩
    simpa using this.neg
  have hΨc : Continuous Ψ := by
    have hm : Monotone fun t => -Ψ t := fun a b hab => neg_le_neg (hΨa.antitone hab)
    have := hm.continuous_of_surjective fun y => ⟨Φ (-y), by simp only [hΨΦ, neg_neg]⟩
    simpa using this.neg
  have hΦ1 : ∀ s, -Φ (s + 1) = -Φ s + 1 := fun s => by
    have : Φ (s + 1) = Φ s - 1 := hDm.injective (by rw [hΦ, hDf, hKf, ← hΦ, hDi])
    rw [this]; ring
  have hΨ1 : ∀ t, -Ψ (t + 1) = -Ψ t + 1 := fun t => by
    have : Ψ (t + 1) = Ψ t - 1 := hDm.injective (hKa.injective (by
      rw [hΨ, hDi, hKfi, hΨ, hDf]))
    rw [this]; ring
  have hΦn : ∀ s (m : ℤ), Φ (s + m) = Φ s + ((-m : ℤ) : ℝ) := fun s m => by
    have := map_add_int_of_add_one (Φ := fun s => -Φ s) hΦ1 s m
    push_cast; linarith
  have hΨn : ∀ t (m : ℤ), Ψ (t + m) = Ψ t + ((-m : ℤ) : ℝ) := fun t m => by
    have := map_add_int_of_add_one (Φ := fun t => -Ψ t) hΨ1 t m
    push_cast; linarith
  -- 6. descend `Φ` and `Ψ` to `L`
  let φ₀ : L → L := fun x => E (Φ (Classical.choose (hE.surjective x)))
  let ψ₀ : L → L := fun y => E (Ψ (Classical.choose (hE.surjective y)))
  have hφ₀ : ∀ s, φ₀ (E s) = E (Φ s) := fun s => by
    have hs := Classical.choose_spec (hE.surjective (E s))
    show E (Φ (Classical.choose (hE.surjective (E s)))) = E (Φ s)
    generalize Classical.choose (hE.surjective (E s)) = s₀ at hs ⊢
    obtain ⟨m, hm⟩ := hE.fiber _ s hs
    rw [hm, hΦn, hE.add_int]
  have hψ₀ : ∀ t, ψ₀ (E t) = E (Ψ t) := fun t => by
    have ht := Classical.choose_spec (hE.surjective (E t))
    show E (Ψ (Classical.choose (hE.surjective (E t)))) = E (Ψ t)
    generalize Classical.choose (hE.surjective (E t)) = t₀ at ht ⊢
    obtain ⟨m, hm⟩ := hE.fiber _ t ht
    rw [hm, hΨn, hE.add_int]
  have hqE := hE.isCoveringMap.isQuotientMap hE.surjective
  have hφc : Continuous φ₀ := hqE.continuous_iff.2 (by
    have : φ₀ ∘ E = E ∘ Φ := funext hφ₀
    rw [this]; exact hE.isCoveringMap.continuous.comp hΦc)
  have hψc : Continuous ψ₀ := hqE.continuous_iff.2 (by
    have : ψ₀ ∘ E = E ∘ Ψ := funext hψ₀
    rw [this]; exact hE.isCoveringMap.continuous.comp hΨc)
  let φ : L ≃ₜ L :=
    { toFun := φ₀
      invFun := ψ₀
      left_inv := fun x => by
        obtain ⟨s, rfl⟩ := hE.surjective x
        rw [hφ₀, hψ₀, hΨΦ]
      right_inv := fun y => by
        obtain ⟨t, rfl⟩ := hE.surjective y
        rw [hψ₀, hφ₀, hΦΨ]
      continuous_toFun := hφc
      continuous_invFun := hψc }
  -- 7. in the charts, `φ` reads as `B` followed by an element of `Γ_{−p}`
  refine ⟨φ, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := hE.surjective x
  obtain ⟨A₁, hA₁⟩ := hd s
  obtain ⟨A₂, hA₂⟩ := hd (Φ s)
  let A : GammaP C.antipode.pt := gammaNeg C.pt (A₂⁻¹ * A₁⁻¹)
  have hev : ∀ᶠ s' in 𝓝 s,
      @chartAt (Link C.antipode.pt) _ L _ C.antipode.atlas (φ (E s)) (φ (E s')) =
        A • linkMove B hB (@chartAt (Link C.pt) _ L _ C.atlas (E s) (E s')) := by
    filter_upwards [hA₁, hΦc.continuousAt.eventually hA₂] with s' h1 h2
    simp only [Function.comp_apply] at h1 h2
    rw [C.antipode_chartAt]
    show linkNeg C.pt (@chartAt (Link C.pt) _ L _ C.atlas (φ₀ (E s)) (φ₀ (E s'))) = _
    rw [hφ₀, hφ₀, eq_inv_smul_iff.2 h2.symm, hΦ, hKlc, h1, linkReflect_smul hp hB' hBp,
      smul_smul, linkNeg_smul, linkReflect_apply, Homeomorph.apply_symm_apply]
    rfl
  exact ⟨A, Filter.mem_of_superset
    (hE.isCoveringMap.isOpenMap.image_mem_nhds hev) (by rintro _ ⟨s', hs', rfl⟩; exact hs')⟩

/-- **The space-like sentence of `bbsrem:p_p`, exactly**: at `p ∈ dS²`, the link `L` and the
antipodal link `L⁻` (the links of `p̄` and `−p̄`) are isomorphic through a move `B` with
`B • p = −p` (any such `B`) iff `L` is not a Misner link. -/
theorem GammaLinkCircle.IsLiftedDev.isIsoVia_antipode_iff (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .deSitter) (B : Causal.Flat.lorentz 2)
    (hB : B • C.pt = C.antipode.pt) :
    (∃ φ : L ≃ₜ L, C.IsIsoVia C.antipode B hB φ) ↔
      ¬ linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} :=
  ⟨fun ⟨φ, hφ⟩ hS => h.not_isIsoVia_antipode hp hS B hB φ hφ,
    fun hS => h.exists_isIsoVia_antipode hθ hp hS B hB⟩

end NonMisnerIso

/-! ## 13. Assembly: `bbsrem:p_p` in its strongest true form -/

section Assembly

/-- `bbsrem:p_p` (`colI_v1.tex:934–942`): **every sentence in its strongest true form** (the label
is partial: the space-like sentence holds exactly for non-Misner links).
* « `𝔢(L)` admits two singular points `p̄`, `−p̄`, corresponding to `p` and `−p` »: `Γ_{−p} = Γ_p`,
  and for every developing data `Δ` the flip is an HS-isomorphism of `𝔢(L)` onto `𝔢(L⁻)` sending
  `−p̄` to the apex over `−p`: the singularity `−p̄` is the one of the antipodal
  `(Γ_{−p}, ℓ(−p))`-circle `L⁻` (determined by `L`).
* time-like: `p ∈ ℍ²₊` gives `−p ∈ ℍ²₋` and conversely;
* light-like of degree `k`: `p ∈ ∂ℍ²₊` gives `−p ∈ ∂ℍ²₋` (and conversely), with an oriented lifted
  developing pair of `L⁻` of the same degree `k` (`δᵏ g'`, `g'` with a fixed point, parabolic iff
  `g` is); the degree of `L⁻` is well defined;
* future cuspidal at `p̄` gives past extreme BTZ-like at `−p̄` (image `i⁺(ℓ(−p))` minus its tangent
  directions, OQ-116 (b));
* space-like: the type is kept (positive stays positive, negative stays negative; BTZ-like
  past/future and Misner images are kept, `GX.GammaLinkCircle.antipode_deSitter_image`); moves
  `B ∈ SO₀(1,2)` with `B • p = −p` exist, and for each of them the links of `p̄` and `−p̄` are
  isomorphic through `B` **iff `L` is not a Misner link**
  (`GX.GammaLinkCircle.IsLiftedDev.isIsoVia_antipode_iff`). The printed « always isomorphic »
  fails for Misner singularities, which exist at every `p ∈ dS²`:
  `GX.exists_misner_not_isIsoVia_antipode`. -/
theorem GammaLinkCircle.bbsrem_p_p {L : Type*} [TopologicalSpace L] (C : GammaLinkCircle L) :
    GammaP C.antipode.pt = GammaP C.pt ∧
    (∀ Δ : C.DevData,
      Δ.suspStructure.IsIso Δ.antipode.suspStructure (BiSusp.flip (S := L)).toOpenPartialHomeomorph) ∧
    (haveI := C.nonempty
     BiSusp.flip (BiSusp.south L) = BiSusp.north L ∧ BiSusp.flip (BiSusp.north L) = BiSusp.south L) ∧
    ((C.pt ∈ HS.piece 2 .hypPlus → C.antipode.pt ∈ HS.piece 2 .hypMinus) ∧
      (C.pt ∈ HS.piece 2 .hypMinus → C.antipode.pt ∈ HS.piece 2 .hypPlus)) ∧
    ((C.pt ∈ HS.piece 2 .bdPlus → C.antipode.pt ∈ HS.piece 2 .bdMinus) ∧
      (C.pt ∈ HS.piece 2 .bdMinus → C.antipode.pt ∈ HS.piece 2 .bdPlus) ∧
      (C.pt ∈ HS.piece 2 .deSitter → C.antipode.pt ∈ HS.piece 2 .deSitter)) ∧
    (∀ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde),
      IsOrientedTangent C.pt θ → C.IsLiftedDev θ E D f → (∃ x, g x = x) →
      f = GTilde.delta ^ k * g →
      ∃ (θ' : TpHS C.antipode.pt ≃ₗ[ℝ] ℂ) (E' : ℝ → L) (D' : ℝ → ℝ) (f' g' : GTilde),
        IsOrientedTangent C.antipode.pt θ' ∧ C.antipode.IsLiftedDev θ' E' D' f' ∧
        (∃ x, g' x = x) ∧ f' = GTilde.delta ^ k * g' ∧
        (GTilde.IsParabolic g' ↔ GTilde.IsParabolic g) ∧
        (GTilde.IsHyperbolic g' ↔ GTilde.IsHyperbolic g) ∧
        ∀ (θ'' : TpHS C.antipode.pt ≃ₗ[ℝ] ℂ) (E'' : ℝ → L) (D'' : ℝ → ℝ) (f'' : GTilde) (k'' : ℤ)
          (g'' : GTilde), IsOrientedTangent C.antipode.pt θ'' →
          C.antipode.IsLiftedDev θ'' E'' D'' f'' → (∃ x, g'' x = x) →
          f'' = GTilde.delta ^ k'' * g'' → k'' = k) ∧
    (∀ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde),
      IsOrientedTangent C.pt θ → C.IsLiftedDev θ E D f → C.pt ∈ HS.piece 2 .bdPlus →
      GTilde.IsParabolic f → (∃ x, f x = x) → linkCover C.pt θ '' range D = iPlus C.pt →
      ∃ (θ' : TpHS C.antipode.pt ≃ₗ[ℝ] ℂ) (E' : ℝ → L) (D' : ℝ → ℝ) (f' : GTilde),
        IsOrientedTangent C.antipode.pt θ' ∧ C.antipode.IsLiftedDev θ' E' D' f' ∧
        GTilde.IsParabolic f' ∧ (∃ x, f' x = x) ∧
        linkCover C.antipode.pt θ' '' range D' = iPlus C.antipode.pt \ tangentDirs C.antipode.pt ∧
        C.antipode.iPlusL = univ ∧ C.antipode.iMinusL = ∅) ∧
    (C.IsSpacelikePositive → C.antipode.IsSpacelikePositive) ∧
    (C.IsSpacelikeNegative → C.antipode.IsSpacelikeNegative) ∧
    (C.pt ∈ HS.piece 2 .deSitter →
      (∃ B : Causal.Flat.lorentz 2, B • C.pt = C.antipode.pt) ∧
      ∀ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde),
        IsOrientedTangent C.pt θ → C.IsLiftedDev θ E D f →
        ∀ (B : Causal.Flat.lorentz 2) (hB : B • C.pt = C.antipode.pt),
          (∃ φ : L ≃ₜ L, C.IsIsoVia C.antipode B hB φ) ↔
            ¬ linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)}) := by
  refine ⟨gammaP_neg C.pt, fun Δ => Δ.isIso_flip, C.flip_south_north, C.antipode_timelike,
    C.antipode_lightlike_pos, fun θ E D f k g hθ h hg hfg => ?_,
    fun θ E D f hθ h hp hpar hfix hcusp => ?_, fun hC => hC.antipode, fun hC => hC.antipode,
    fun hp => ⟨exists_smul_eq_neg hp, fun θ E D f hθ h B hB => h.isIsoVia_antipode_iff hθ hp B hB⟩⟩
  · obtain ⟨hθ', ha, hf', hg', hpar, hhyp, huniq⟩ := h.antipode_degree hθ hg hfg
    exact ⟨_, _, _, _, _, hθ', ha, hg', hf', hpar, hhyp, huniq⟩
  · obtain ⟨-, hθ', ha, hpar, hfix', himg, hP, hM⟩ := h.antipode_cuspidal hθ hp hpar hfix hcusp
    exact ⟨_, _, _, _, hθ', ha, hpar, hfix', himg, hP, hM⟩

end Assembly

end GX
