import GXScaffold.BBS.HSAntipodal
import GXScaffold.BBS.HSPositive

/-!
# BBS § 3.3: `bbsrem:previous_section_observed_only` under both readings of OQ-120 (a) and (c)

Target `T-bbs-remark-readings` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx).
`papers/bbs/legacy/labeled/colI_v1.tex`. Imports `GX.BBS.HSSingularities` (through the two
files below; the remark in the readings « same `p` » and « l.915 »), `GXScaffold.BBS.HSAntipodal`
(moved-`p` isomorphisms `GX.GammaLinkCircle.IsIsoVia`, `GX.linkMove`) and
`GXScaffold.BBS.HSPositive` (the trivial-holonomy circle of degree `4`).

* `bbsrem:previous_section_observed_only` — `colI_v1.tex:926` — partial (unmarked: the mark waits
  on OQ-120 (b), OQ-124 and OQ-116 (a); this file removes OQ-120 (a) and (c) from the list of what
  the mark depends on): (iii) and « does not extend » are proved under each of the four
  combinations of readings — isomorphisms with the same `p` (`GX.GammaLinkCircle.IsIso`) or
  through a move `B ∈ SO₀(1,2)` (`GX.GammaLinkCircle.IsIsoVia`), positivity in the form of l.915
  (`GX.GammaLinkCircle.IsSpacelikePositive`) or of l.908–913
  (`GX.GammaLinkCircle.IsSpacelikePositiveRep`): the assembly
  `GX.bbsrem_previous_section_observed_only_readings`.

> In the previous section we observed that there is only one $\R\PP^1$ hyperbolic circle of
> holonomy $\langle g \rangle$ up to $\R\PP^1$-isomorphism, but this remark does not extend to
> hyperbolic $(\Gamma_p, \ell(p))$-circles since a real projective conjugacy between $g$ and
> $g^{-1}$, if preserving the orientation, must permute time-like and space-like components. Hence
> positive hyperbolic $(\Gamma_p, \ell(p))$-circles and negative hyperbolic
> $(\Gamma_p, \ell(p))$-circles are not isomorphic. (l.927–931)
>
> If, for every integer $i$, the point $x_{2i}$ (i.e. the left extremities of the components of
> $I^+$) is a repelling fixed point of $g$, then the singularity is a positive space-like
> singularity of degree $k$. In the other case, i.e. if the left extremities of the components of
> $I^+$ are attracting fixed point of $g$, then the singularity is a negative space-like
> singularity of degree $k$. In other words, the singularity is positive if and only if for every
> $x$ in $I^+$ we have $gx \geq x$. (l.906–915)

## Main declarations (all proved, 0 `sorry`)

* **Moves `B ∈ SO₀(1,2)`, `B • p = p'`.** `GX.smul_mem_deSitter_iff` (a move keeps `dS²`),
  `GX.dsProj_tpMove` (`π_{p'} ∘ [B] = ‖B p‖⁻² · B ∘ π_p`), **a move keeps `i⁺`**
  (`GX.linkMove_mem_iPlus_iff`, `B` orthochronous), the transported oriented identification
  `GX.tangentAlong B h θ = θ ∘ [B]⁻¹` (`GX.isOrientedTangent_tangentAlong`, `B` of determinant `1`)
  and `GX.linkMove_linkCover_along` (`B` reads `linkCover` at `p` as `linkCover` at `p'`).
* **(iii) under moved-`p` isomorphisms (OQ-120 (a)).** A moved-`p` isomorphism carries a lifted
  developing pair `(θ, E, D, f)` to `(θ ∘ [B]⁻¹, φ ∘ E, D, f)`
  (`GX.GammaLinkCircle.IsIsoVia.isLiftedDev`: same `D`, same lifted holonomy) and keeps `i⁺(L)`
  (`…IsIsoVia.mem_iPlusL_iff`), so positivity and negativity are invariant
  (`…IsIsoVia.isSpacelikePositive`, `…IsIsoVia.isSpacelikeNegative`) and **positive and negative
  are isomorphic through no move** (`GX.not_isIsoVia_of_positive_of_negative`). The same-`p`
  notion is the case `B = 1` (`GX.GammaLinkCircle.IsIso.isIsoVia_one`, `GX.linkMove_one`), so the
  moved form implies the same-`p` form.
* **The repelling-endpoint form (OQ-120 (c)).** `I⁺ = D(E⁻¹ i⁺(L)) ⊆ ℝP̃¹`
  (`GX.GammaLinkCircle.iPlusTilde`; the whole `linkCover⁻¹ i⁺(ℓ(p))` in degree `≠ 0`,
  `…IsLiftedDev.iPlusTilde_eq`); l.908–910 `GX.GammaLinkCircle.IsSpacelikePositiveRep` (the left
  extremity `sInf` of every component of `I⁺` is a repelling fixed point of `g`,
  `GX.GTilde.IsRepellingAt`), l.911–913 `GX.GammaLinkCircle.IsSpacelikeNegativeAtt` (attracting).
  On `ℝP̃¹`: `GX.GTilde.forms_iff_of_consecutive` (`a < b < a + 1` consecutive fixed points of a
  hyperbolic `g`). Per lifted pair `GX.GammaLinkCircle.IsLiftedDev.forms_iff`; **the definitions
  agree** `GX.GammaLinkCircle.isSpacelikePositive_iff_rep`, `…isSpacelikeNegative_iff_att`, in
  every degree `k ≥ 1`; the dichotomy in the l.908–913 form `…IsLiftedDev.rep_dichotomy`.
* **Where the forms part (OQ-128).** Without the guard « `g` hyperbolic », for a lifted pair at
  `p ∈ dS²` with `f = δᵏ g`, `k ≥ 1`, `g` with a fixed point: l.915's inequality ⇔ the repelling
  form **iff `g ≠ 1`** (`GX.GammaLinkCircle.IsLiftedDev.forms_iff_iff_ne_one`; `g ≠ 1` forces `g`
  hyperbolic there). At `g = 1` l.915 holds and no fixed point is repelling
  (`GX.GTilde.not_isRepellingAt_one`); the degree-`4` instance `GX.exists_forms_differ`.
* **The assembly** `GX.bbsrem_previous_section_observed_only_readings`: (iii) in the l.908–913
  form and in the l.915 form, for same-`p` and for moved-`p` isomorphisms; the two forms equal;
  « does not extend » at every `p ∈ dS²` with the examples positive / negative in both forms and
  isomorphic through no move, their `ℝP¹`-circles isomorphic.

## Hypothesis checklist

| BBS | here |
|---|---|
| « isomorphic » (l.931) | ✓ both readings: same `p` (`GX.GammaLinkCircle.IsIso`) and through any move `B ∈ SO₀(1,2)` (`GX.GammaLinkCircle.IsIsoVia`, HSAntipodal) |
| positive / negative (l.908–915) | ✓ both forms: l.915 (`IsSpacelikePositive`) and l.908–913 (`IsSpacelikePositiveRep`, `IsSpacelikeNegativeAtt`), proved equal |
| « the left extremities of the components of `I⁺` » (l.909, l.912) | ✓ `sInf (connectedComponentIn I⁺ t)` for every `t ∈ I⁺`, `I⁺ = D(E⁻¹ i⁺(L))` |
| « repelling / attracting fixed point » (l.909, l.912) | ✓ `GX.GTilde.IsRepellingAt`, `IsAttractingAt` (HSSingularities: fixed, and nearby points moved away / towards) |
| `g` hyperbolic, `k ≥ 1`, `f = δᵏ g`, `θ` oriented (l.893–895) | ✓ as in HSSingularities' definitions (the guard is the paper's « hyperbolic circle of degree `k ≥ 1` ») |
| `SO₀(1,2)` (l.616–623) | ✓ the moves are orthochronous of determinant `1` (`Causal.Flat.lorentz 2`); both properties are used |
| holonomy `⟨g⟩`, time-like components (l.927–930) | ⚠ unchanged: OQ-120 (b) (lifted holonomy in `G̃`), OQ-116 (a) (time-like `i^±`), OQ-124 (« does not extend ») |

## SCOPE (disclosed)

* **(a)** This file settles OQ-120 (a) and (c) for the remark only in the sense that each answer
  is proved: (iii) and « does not extend » hold under both readings of each. OQ-120 (b), OQ-124 and
  OQ-116 (a) are untouched, and (i), (ii) of the remark (`GX.rp1Iso_of_zpowers_eq`,
  `GX.conj_inv_swaps_timelike_spacelike`) do not involve (a) or (c).
* **(b)** The equivalence of the two forms needs the guard « `g` hyperbolic », which is the paper's
  own setting (l.893–895: « `L` is a hyperbolic circle of degree `k ≥ 1` »); in it, it holds in
  every degree (the degree is then even). Unguarded, the forms differ exactly at trivial
  `Γ_p`-holonomy (`g = 1`), whenever such a pair exists (`IsLiftedDev.forms_iff_iff_ne_one`);
  built in degree `4` (`GX.exists_forms_differ`), argued, not formalized, in every even degree,
  the regular link `ℓ(p)` (degree `2`) included; this is OQ-128's finding, read at the level of a single lifted pair.
* **(c)** Moves are elements of `SO₀(1,2)`. A time-reversing `B ∈ SO(1,2)` exchanges `i⁺` and
  `i⁻` (argued, not formalized) and is not covered (`GX.linkMove_mem_iPlus_iff` uses
  orthochronicity), nor is the
  converse question whether an HS-isomorphism of singularities induces a moved isomorphism of
  links (HSAntipodal SCOPE (b)).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. Moves `B ∈ SO₀(1,2)`, `B • p = p'`: de Sitter, `i⁺`, the oriented identification -/

section Move

variable {p p' : HS 2} (B : Causal.Flat.lorentz 2)

/-- The norm factor of a move: `(B • q : 𝕄) = c · B q`, `c = ‖B q‖⁻¹ > 0`. -/
theorem moveFactor_pos (q : HS 2) : 0 < ‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) q‖⁻¹ :=
  inv_pos.2 (norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero q)))

/-- A move keeps de Sitter space. -/
theorem smul_mem_deSitter_iff {q : HS 2} :
    B • q ∈ HS.piece 2 .deSitter ↔ q ∈ HS.piece 2 .deSitter := by
  show 0 < Causal.Flat.minkQ ((B • q : HS 2) : 𝕄) ↔ 0 < Causal.Flat.minkQ (q : 𝕄)
  rw [coe_hs_smul, Causal.Flat.minkQ_smul, Causal.Flat.lorentz.minkQ_apply B.2]
  exact ⟨fun h => pos_of_mul_pos_right h (sq_nonneg _),
    fun h => mul_pos (pow_pos (moveFactor_pos B q) 2) h⟩

/-- `π_{p'} ∘ [B] = c² · B ∘ π_p`, `c = ‖B p‖⁻¹ > 0`. -/
theorem dsProj_tpMove (h : B • p = p') (z : TpHS p) :
    dsProj p' (tpMove B h z) =
      (‖(B : 𝕄 ≃ₗ[ℝ] 𝕄) p‖⁻¹) ^ 2 • (B : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p z) := by
  subst h
  induction z using Submodule.Quotient.induction_on with
  | H w =>
  show perpLin (B • p) ((B : 𝕄 ≃ₗ[ℝ] 𝕄) w) = _ • (B : 𝕄 ≃ₗ[ℝ] 𝕄) (perpLin p w)
  have hBw := Causal.Flat.lorentz.minkB_apply B.2 p w
  rw [perpLin_apply, perpLin_apply, coe_hs_smul, Causal.Flat.minkQ_smul,
    Causal.Flat.lorentz.minkQ_apply B.2, Causal.Flat.minkB_smul_left, hBw, map_sub, map_smul,
    map_smul, smul_sub, smul_smul, smul_smul, smul_smul]
  congr 1
  ring_nf

/-- **A move keeps `i⁺`** at de Sitter points. -/
theorem linkMove_mem_iPlus_iff (hp : p ∈ HS.piece 2 .deSitter) (h : B • p = p') (σ : Link p) :
    linkMove B h σ ∈ iPlus p' ↔ σ ∈ iPlus p := by
  have hp' : p' ∈ HS.piece 2 .deSitter := h ▸ (smul_mem_deSitter_iff B).2 hp
  rw [iPlus_of_deSitter hp, iPlus_of_deSitter hp']
  show Causal.Flat.IsFutureTimelike (dsProj p' (linkMove B h σ : TpHS p')) ↔
    Causal.Flat.IsFutureTimelike (dsProj p σ)
  have hc := moveFactor_pos B p
  have hc' : 0 < ‖tpMove B h σ‖⁻¹ :=
    inv_pos.2 (norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero σ)))
  rw [coe_linkMove, map_smul, dsProj_tpMove, smul_smul]
  have key : ∀ {c : ℝ}, 0 < c → ∀ v : 𝕄,
      Causal.Flat.IsFutureTimelike (c • v) ↔ Causal.Flat.IsFutureTimelike v := by
    intro c hc v
    simp only [Causal.Flat.IsFutureTimelike, Prod.smul_fst, smul_eq_mul, Causal.Flat.minkQ_smul]
    exact ⟨fun ⟨a, b⟩ => ⟨pos_of_mul_pos_right a hc.le, neg_of_mul_neg_right b (by positivity)⟩,
      fun ⟨a, b⟩ => ⟨mul_pos hc a, mul_neg_of_pos_of_neg (by positivity) b⟩⟩
  rw [key (mul_pos hc' (pow_pos hc 2)), Causal.Flat.lorentz.isFutureTimelike_apply_iff B.2]

/-- The identification of `T_{p'} HS²` transported by `B`: `θ ∘ [B]⁻¹`. -/
def tangentAlong (h : B • p = p') (θ : TpHS p ≃ₗ[ℝ] ℂ) : TpHS p' ≃ₗ[ℝ] ℂ :=
  (tpMove B h).symm.trans θ

theorem isOrientedTangent_tangentAlong (h : B • p = p') {θ : TpHS p ≃ₗ[ℝ] ℂ}
    (hθ : IsOrientedTangent p θ) : IsOrientedTangent p' (tangentAlong B h θ) := by
  intro w₁ w₂ h₁ h₂
  set v₁ := ((B⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w₁
  set v₂ := ((B⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w₂
  have hv : ∀ (w v : 𝕄), v = ((B⁻¹ : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w → ∀ z : ℂ,
      (Submodule.Quotient.mk w : TpHS p') = (tangentAlong B h θ).symm z →
      (Submodule.Quotient.mk v : TpHS p) = θ.symm z := by
    intro w v hvw z hz
    apply (tpMove B h).injective
    rw [show (Submodule.Quotient.mk v : TpHS p) = tpMk p v from rfl, tpMove_mk, hvw,
      lorentz_apply_inv]
    rw [tangentAlong, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm] at hz
    exact hz
  have := hθ v₁ v₂ (hv w₁ v₁ rfl 1 h₁) (hv w₂ v₂ rfl Complex.I h₂)
  subst h
  rw [coe_hs_smul, vol3_smul_left, ← lorentz_apply_inv B w₁, ← lorentz_apply_inv B w₂,
    vol3_lorentz]
  exact mul_pos (moveFactor_pos B p) this

theorem linkMove_linkCover_along (h : B • p = p') (θ : TpHS p ≃ₗ[ℝ] ℂ) (t : ℝ) :
    linkMove B h (linkCover p θ t) = linkCover p' (tangentAlong B h θ) t := by
  apply Subtype.ext
  have hne : θ.symm (Circle.exp (Real.pi * t)) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 (Circle.coe_ne_zero _)
  rw [coe_linkMove, coe_linkCover, coe_linkCover, tangentAlong, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, map_smul, normalize_smul_pos (inv_pos.2 (norm_pos_iff.2 hne))]

end Move

/-! ## 2. (iii) for moved-`p` isomorphisms (OQ-120 (a), the reading with a moving point) -/

section MovedIso

variable {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']

variable {C : GammaLinkCircle L} {C' : GammaLinkCircle L'} {B : Causal.Flat.lorentz 2}
  {h : B • C.pt = C'.pt} {φ : L ≃ₜ L'}

/-- A moved-`p` isomorphism carries a lifted developing pair `(θ, E, D, f)` of `C` to the lifted
developing pair `(θ ∘ [B]⁻¹, φ ∘ E, D, f)` of `C'`: the same `D`, the same lifted holonomy. -/
theorem GammaLinkCircle.IsIsoVia.isLiftedDev (hφ : C.IsIsoVia C' B h φ)
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde} (h0 : C.IsLiftedDev θ E D f) :
    C'.IsLiftedDev (tangentAlong B h θ) (φ ∘ E) D f := by
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h0
  refine ⟨⟨hE.isCoveringMap.homeomorph_comp φ, φ.surjective.comp hE.surjective,
    fun s => by simp only [Function.comp_apply, hE.add_one], fun s t e =>
      hE.fiber s t (φ.injective e)⟩, hDc, hDm, fun s => ?_, hDf⟩
  obtain ⟨A₁, h₁⟩ := hd s
  obtain ⟨A₂, h₂⟩ := hφ (E s)
  refine ⟨gammaMove B h A₁ * A₂⁻¹, ?_⟩
  filter_upwards [h₁, hE.isCoveringMap.continuous.continuousAt.eventually h₂] with s' hs1 hs2
  simp only [Function.comp_apply] at hs1 hs2 ⊢
  rw [hs2, ← linkMove_linkCover_along, hs1, linkMove_smul, mul_smul, inv_smul_smul]

/-- A moved-`p` isomorphism keeps `i⁺` at de Sitter points. -/
theorem GammaLinkCircle.IsIsoVia.mem_iPlusL_iff (hφ : C.IsIsoVia C' B h φ)
    (hp : C.pt ∈ HS.piece 2 .deSitter) (x : L) : φ x ∈ C'.iPlusL ↔ x ∈ C.iPlusL := by
  obtain ⟨A, hA⟩ := hφ x
  have e := hA.self_of_nhds
  show @chartAt (Link C'.pt) _ L' _ C'.atlas (φ x) (φ x) ∈ iPlus C'.pt ↔
    @chartAt (Link C.pt) _ L _ C.atlas x x ∈ iPlus C.pt
  rw [e, smul_mem_iPlus_iff, linkMove_mem_iPlus_iff B hp h]

/-- **Positivity (l.915 form) is invariant under moved-`p` isomorphisms.** -/
theorem GammaLinkCircle.IsIsoVia.isSpacelikePositive (hφ : C.IsIsoVia C' B h φ)
    (hC : C.IsSpacelikePositive) : C'.IsSpacelikePositive := by
  obtain ⟨hp, θ, hθ, E, D, f, k, g, h0, hk, hg, hh, hfg, hpos⟩ := hC
  exact ⟨h ▸ (smul_mem_deSitter_iff B).2 hp, tangentAlong B h θ,
    isOrientedTangent_tangentAlong B h hθ, φ ∘ E, D, f, k, g, hφ.isLiftedDev h0, hk, hg, hh, hfg,
    fun s hs => hpos s ((hφ.mem_iPlusL_iff hp (E s)).1 hs)⟩

/-- **Negativity (l.915 form) is invariant under moved-`p` isomorphisms.** -/
theorem GammaLinkCircle.IsIsoVia.isSpacelikeNegative (hφ : C.IsIsoVia C' B h φ)
    (hC : C.IsSpacelikeNegative) : C'.IsSpacelikeNegative := by
  obtain ⟨hp, θ, hθ, E, D, f, k, g, h0, hk, hg, hh, hfg, hneg⟩ := hC
  exact ⟨h ▸ (smul_mem_deSitter_iff B).2 hp, tangentAlong B h θ,
    isOrientedTangent_tangentAlong B h hθ, φ ∘ E, D, f, k, g, hφ.isLiftedDev h0, hk, hg, hh, hfg,
    fun s hs => hneg s ((hφ.mem_iPlusL_iff hp (E s)).1 hs)⟩

omit [TopologicalSpace L] in
/-- A circle is not both positive and negative (l.915 form). -/
theorem GammaLinkCircle.not_positive_and_negative [TopologicalSpace L] {D₀ : GammaLinkCircle L}
    (hpos : D₀.IsSpacelikePositive) (hneg : D₀.IsSpacelikeNegative) : False :=
  not_isIso_of_positive_of_negative hpos hneg (Homeomorph.refl L)
    ⟨rfl, by letI := D₀.atlas; exact isGXMorphism_id⟩

/-- **(iii), moved-`p` reading** (l.930–931): a positive and a negative hyperbolic
`(Γ_p, ℓ(p))`-circle are isomorphic through no move `B ∈ SO₀(1,2)`. -/
theorem not_isIsoVia_of_positive_of_negative (hC : C.IsSpacelikePositive)
    (hC' : C'.IsSpacelikeNegative) (B : Causal.Flat.lorentz 2) (h : B • C.pt = C'.pt)
    (φ : L ≃ₜ L') : ¬ C.IsIsoVia C' B h φ := fun hφ =>
  GammaLinkCircle.not_positive_and_negative (hφ.isSpacelikePositive hC) hC'

/-- The move `B = 1` is the identity of `ℓ(p)`. -/
theorem linkMove_one {p : HS 2} (h : (1 : Causal.Flat.lorentz 2) • p = p) (σ : Link p) :
    linkMove 1 h σ = σ := by
  apply Subtype.ext
  have e : ∀ z : TpHS p, tpMove 1 h z = z := fun z => by
    induction z using Submodule.Quotient.induction_on with
    | H w => rfl
  rw [coe_linkMove, e, norm_raySphere, inv_one, one_smul]

/-- **The same-`p` notion is the case `B = 1`**: an isomorphism with the same `p` is a moved-`p`
isomorphism through the identity. -/
theorem GammaLinkCircle.IsIso.isIsoVia_one {C : GammaLinkCircle L} {C' : GammaLinkCircle L'}
    {φ : L ≃ₜ L'} (hφ : C.IsIso C' φ) (h : (1 : Causal.Flat.lorentz 2) • C.pt = C'.pt) :
    C.IsIsoVia C' 1 h φ := by
  obtain ⟨hpt, hmor⟩ := hφ
  obtain ⟨q, atl, hgr, hcirc⟩ := C'
  simp only at hpt h ⊢
  subst hpt
  letI := C.atlas
  letI : ChartedSpace (Link C.pt) L' := atl
  have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
  intro x
  obtain ⟨A, hA⟩ := hmor'.exists_smul_eq x
  refine ⟨A, ?_⟩
  filter_upwards [hA] with y hy
  rw [linkMove_one]
  exact hy

end MovedIso

/-! ## 3. The repelling-endpoint form of l.908–913 (OQ-120 (c)) -/

section Rep

variable {L : Type*} [TopologicalSpace L]

/-! ### Repelling and attracting fixed points read off the sign of `g − id` -/

namespace GTilde

/-- `g − id` is `1`-periodic. -/
theorem apply_add_int_sub (g : GTilde) (y : ℝ) (n : ℤ) : g (y + n) - (y + n) = g y - y := by
  rw [map_add_int]; ring

/-- A fixed point `a` with `g` above the identity on its right and below on its left (down to the
previous fixed point `b − 1`) is repelling. -/
theorem isRepellingAt_of_dir {g : GTilde} {a b : ℝ} (hab : a < b) (hb : b < a + 1)
    (ha : g a = a) (hR : ∀ y ∈ Ioo a b, y < g y) (hL : ∀ y ∈ Ioo (b - 1) a, g y < y) :
    IsRepellingAt g a := by
  refine ⟨ha, eventually_nhdsWithin_iff.2 ?_⟩
  filter_upwards [Ioo_mem_nhds (show b - 1 < a by linarith) hab] with y hy hne
  rcases lt_or_gt_of_ne (show y ≠ a from hne) with hlt | hgt
  · have h1 := hL y ⟨hy.1, hlt⟩
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  · have h1 := hR y ⟨hgt, hy.2⟩
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-- The mirror statement: below the identity on the right, above on the left: attracting. -/
theorem isAttractingAt_of_dir {g : GTilde} {a b : ℝ} (hab : a < b) (hb : b < a + 1)
    (ha : g a = a) (hR : ∀ y ∈ Ioo a b, g y < y) (hL : ∀ y ∈ Ioo (b - 1) a, y < g y) :
    IsAttractingAt g a := by
  refine ⟨ha, eventually_nhdsWithin_iff.2 ?_⟩
  filter_upwards [Ioo_mem_nhds (show b - 1 < a by linarith) hab] with y hy hne
  rcases lt_or_gt_of_ne (show y ≠ a from hne) with hlt | hgt
  · have h1 := hL y ⟨hy.1, hlt⟩
    have h2 : g y < a := ha ▸ GTilde.strictMono g hlt
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  · have h1 := hR y ⟨hgt, hy.2⟩
    have h2 : a < g y := ha ▸ GTilde.strictMono g hgt
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

/-- Below the identity just right of a fixed point `a`: not repelling. -/
theorem not_isRepellingAt_of_lt {g : GTilde} {a b : ℝ} (hab : a < b)
    (hR : ∀ y ∈ Ioo a b, g y < y) : ¬ IsRepellingAt g a := by
  rintro ⟨ha, hrep⟩
  obtain ⟨y, hy, hyI⟩ := ((hrep.filter_mono (nhdsWithin_mono a
    (show Ioi a ⊆ {a}ᶜ from fun y hy => ne_of_gt hy))).and (Ioo_mem_nhdsGT hab)).exists
  have h1 := hR y hyI
  have h2 : a < g y := ha ▸ GTilde.strictMono g hyI.1
  rw [abs_of_pos (by linarith [hyI.1]), abs_of_pos (by linarith)] at hy
  linarith

/-- Above the identity just right of a fixed point `a`: not attracting. -/
theorem not_isAttractingAt_of_lt {g : GTilde} {a b : ℝ} (hab : a < b)
    (hR : ∀ y ∈ Ioo a b, y < g y) : ¬ IsAttractingAt g a := by
  rintro ⟨ha, hatt⟩
  obtain ⟨y, hy, hyI⟩ := ((hatt.filter_mono (nhdsWithin_mono a
    (show Ioi a ⊆ {a}ᶜ from fun y hy => ne_of_gt hy))).and (Ioo_mem_nhdsGT hab)).exists
  have h1 := hR y hyI
  rw [abs_of_pos (by linarith [hyI.1]), abs_of_pos (by linarith [hyI.1])] at hy
  linarith

/-- The identity has no repelling fixed point. -/
theorem not_isRepellingAt_one (x : ℝ) : ¬ IsRepellingAt 1 x := fun ⟨_, h⟩ => by
  obtain ⟨y, hy⟩ := h.exists
  rw [one_apply] at hy
  exact lt_irrefl _ hy

/-- **The two forms on `ℝP̃¹`**: `a < b < a + 1` consecutive fixed points of a hyperbolic `g`,
`U = ⋃ᵢ ]a + 2i, b + 2i[`: `g ≥ id` on `U` iff the left extremities of the components of `U` are
repelling, `g ≤ id` on `U` iff they are attracting. -/
theorem forms_iff_of_consecutive {g : GTilde} (hh : IsHyperbolic g) {a b : ℝ} (hab : a < b)
    (hb : b < a + 1) (ha : g a = a) (hbf : g b = b) :
    ((∀ y ∈ ⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i), y ≤ g y) ↔
        ∀ t ∈ ⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i), IsRepellingAt g
          (sInf (connectedComponentIn (⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i)) t))) ∧
      ((∀ y ∈ ⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i), g y ≤ y) ↔
        ∀ t ∈ ⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i), IsAttractingAt g
          (sInf (connectedComponentIn (⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i)) t))) := by
  set U := ⋃ i : ℤ, Ioo (a + 2 * i) (b + 2 * i)
  -- the left extremity of the component of `t`
  have hcomp : ∀ t ∈ U, ∃ i : ℤ, t ∈ Ioo (a + 2 * i) (b + 2 * i) ∧
      sInf (connectedComponentIn U t) = a + 2 * i := fun t ht => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 ht
    refine ⟨i, hi, ?_⟩
    rw [connectedComponentIn_iUnion_Ioo_two (by linarith) hi, csInf_Ioo (by linarith)]
  have hmid : a + (b - a) / 2 ∈ U :=
    mem_iUnion.2 ⟨0, by simp only [Int.cast_zero, mul_zero, add_zero]; constructor <;> linarith⟩
  have hmidI : a + (b - a) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hc0 : sInf (connectedComponentIn U (a + (b - a) / 2)) = a := by
    obtain ⟨i, hi, e⟩ := hcomp _ hmid
    have : i = 0 := by
      have h1 : (a + 2 * i : ℝ) < a + (b - a) / 2 := hi.1
      have h2 : a + (b - a) / 2 < b + 2 * i := hi.2
      have : (i : ℝ) < 1 / 2 := by linarith
      have : (-1 / 2 : ℝ) < i := by linarith
      have : i < 1 := by exact_mod_cast (show (i : ℝ) < 1 by linarith)
      have : -1 < i := by exact_mod_cast (show (-1 : ℝ) < i by linarith)
      omega
    rw [e, this]; simp
  obtain ⟨c₁, hc₁I, hc₁, huniq, hdir⟩ := hh.fixed_structure ha
  have hbc : b = c₁ := huniq b ⟨hab, hb⟩ hbf
  subst hbc
  -- the signs, shifted by integers
  have shift : ∀ {P : ℝ → Prop}, (∀ y ∈ Ioo a b, P (g y - y)) → ∀ (n : ℤ) (y : ℝ),
      y ∈ Ioo (a + n) (b + n) → P (g y - y) := fun {P} hP n y hy => by
    have := hP (y - n) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rwa [← apply_add_int_sub g (y - n) n, sub_add_cancel] at this
  have shift' : ∀ {P : ℝ → Prop}, (∀ y ∈ Ioo b (a + 1), P (g y - y)) → ∀ (n : ℤ) (y : ℝ),
      y ∈ Ioo (b + n) (a + 1 + n) → P (g y - y) := fun {P} hP n y hy => by
    have := hP (y - n) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rwa [← apply_add_int_sub g (y - n) n, sub_add_cancel] at this
  have hfix2 : ∀ i : ℤ, g (a + 2 * i) = a + 2 * i := fun i => by
    have := map_add_int g a (2 * i); push_cast at this; rw [this, ha]
  have hIoo2 : ∀ (i : ℤ) {y : ℝ}, y ∈ Ioo (a + 2 * i) (b + 2 * i) →
      y ∈ Ioo (a + ((2 * i : ℤ) : ℝ)) (b + ((2 * i : ℤ) : ℝ)) := fun i y hy => by
    push_cast; exact hy
  have hIoo2' : ∀ (i : ℤ) {y : ℝ}, y ∈ Ioo (b + 2 * i - 1) (a + 2 * i) →
      y ∈ Ioo (b + ((2 * i - 1 : ℤ) : ℝ)) (a + 1 + ((2 * i - 1 : ℤ) : ℝ)) := fun i y hy => by
    push_cast; constructor <;> linarith [hy.1, hy.2]
  rcases hdir with ⟨hR, hL⟩ | ⟨hR, hL⟩
  · -- `g > id` on `]a, b[`: positive and repelling; neither negative nor attracting
    have hR' : ∀ (i : ℤ) y, y ∈ Ioo (a + 2 * i) (b + 2 * i) → y < g y := fun i y hy => by
      have := shift (P := fun z => 0 < z) (fun y hy => sub_pos.2 (hR y hy)) _ y (hIoo2 i hy)
      linarith
    have hL' : ∀ (i : ℤ) y, y ∈ Ioo (b + 2 * i - 1) (a + 2 * i) → g y < y := fun i y hy => by
      have := shift' (P := fun z => z < 0) (fun y hy => sub_neg.2 (hL y hy)) _ y (hIoo2' i hy)
      linarith
    refine ⟨⟨fun _ t ht => ?_, fun _ y hy => ?_⟩, ⟨fun hneg => ?_, fun hatt => ?_⟩⟩
    · obtain ⟨i, hi, e⟩ := hcomp t ht
      rw [e]
      exact isRepellingAt_of_dir (b := b + 2 * i) (by linarith) (by linarith) (hfix2 i)
        (fun y hy => hR' i y hy) (fun y hy => hL' i y (by simpa using hy))
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      exact (hR' i y hi).le
    · exact absurd (hneg _ hmid) (not_le.2 (hR _ hmidI))
    · exact absurd (hc0 ▸ hatt _ hmid) (not_isAttractingAt_of_lt hab hR)
  · -- `g < id` on `]a, b[`: negative and attracting; neither positive nor repelling
    have hR' : ∀ (i : ℤ) y, y ∈ Ioo (a + 2 * i) (b + 2 * i) → g y < y := fun i y hy => by
      have := shift (P := fun z => z < 0) (fun y hy => sub_neg.2 (hR y hy)) _ y (hIoo2 i hy)
      linarith
    have hL' : ∀ (i : ℤ) y, y ∈ Ioo (b + 2 * i - 1) (a + 2 * i) → y < g y := fun i y hy => by
      have := shift' (P := fun z => 0 < z) (fun y hy => sub_pos.2 (hL y hy)) _ y (hIoo2' i hy)
      linarith
    refine ⟨⟨fun hpos => ?_, fun hrep => ?_⟩, ⟨fun _ t ht => ?_, fun _ y hy => ?_⟩⟩
    · exact absurd (hpos _ hmid) (not_le.2 (hR _ hmidI))
    · exact absurd (hc0 ▸ hrep _ hmid) (not_isRepellingAt_of_lt hab hR)
    · obtain ⟨i, hi, e⟩ := hcomp t ht
      rw [e]
      exact isAttractingAt_of_dir (b := b + 2 * i) (by linarith) (by linarith) (hfix2 i)
        (fun y hy => hR' i y hy) (fun y hy => hL' i y (by simpa using hy))
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      exact (hR' i y hi).le

end GTilde

/-- `I⁺ ⊆ ℝP̃¹` (l.898): the preimage of `i⁺(ℓ(p))` in `L̃_p`, read in `ℝP̃¹` through `D`. -/
def GammaLinkCircle.iPlusTilde (C : GammaLinkCircle L) (E : ℝ → L) (D : ℝ → ℝ) : Set ℝ :=
  D '' {s | E s ∈ C.iPlusL}

/-- **A positive space-like singularity of degree `k ≥ 1`, l.908–910 form**: the left extremity
of every component of `I⁺` is a repelling fixed point of `g`. -/
def GammaLinkCircle.IsSpacelikePositiveRep (C : GammaLinkCircle L) : Prop :=
  C.pt ∈ HS.piece 2 .deSitter ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsRepellingAt g (sInf (connectedComponentIn (C.iPlusTilde E D) t))

/-- **A negative space-like singularity of degree `k ≥ 1`, l.911–913 form**: the left extremity
of every component of `I⁺` is an attracting fixed point of `g`. -/
def GammaLinkCircle.IsSpacelikeNegativeAtt (C : GammaLinkCircle L) : Prop :=
  C.pt ∈ HS.piece 2 .deSitter ∧ ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde) (k : ℤ) (g : GTilde), C.IsLiftedDev θ E D f ∧ 1 ≤ k ∧
      (∃ x, g x = x) ∧ GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsAttractingAt g (sInf (connectedComponentIn (C.iPlusTilde E D) t))

variable {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

omit [TopologicalSpace L] in
theorem GammaLinkCircle.forall_iPlusL_iff [TopologicalSpace L] {C : GammaLinkCircle L}
    {E : ℝ → L} {D : ℝ → ℝ} {P : ℝ → Prop} :
    (∀ s, E s ∈ C.iPlusL → P (D s)) ↔ ∀ y ∈ C.iPlusTilde E D, P y := by
  rw [GammaLinkCircle.iPlusTilde, forall_mem_image]; rfl

/-- In degree `k ≠ 0`, `D` is onto (`GX.GTilde.IsComp.eq_univ`). -/
theorem GammaLinkCircle.IsLiftedDev.range_eq_univ (h : C.IsLiftedDev θ E D f) {k : ℤ}
    (hk : k ≠ 0) {g : GTilde} (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ k * g) :
    range D = univ := by
  letI := C.rp1ChartedSpace θ
  haveI := C.rp1_hasGroupoid θ
  exact h.isLiftedDevPair.isComp.eq_univ (GTilde.apply_ne_of_degree_ne_zero hk hg hfg)

/-- In degree `≠ 0` (`D` onto), `I⁺` is the whole preimage of `i⁺(ℓ(p))` in `ℝP̃¹`. -/
theorem GammaLinkCircle.IsLiftedDev.iPlusTilde_eq (h : C.IsLiftedDev θ E D f)
    (hD : range D = univ) : C.iPlusTilde E D = linkCover C.pt θ ⁻¹' iPlus C.pt := by
  have e := h.2.2.2.1.preimage_iPlus
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : s ∈ E ⁻¹' C.iPlusL := hs
    rw [← e] at this
    exact this
  · intro hy
    obtain ⟨s, rfl⟩ : y ∈ range D := hD ▸ mem_univ y
    refine ⟨s, ?_, rfl⟩
    have : s ∈ (linkCover C.pt θ ∘ D) ⁻¹' iPlus C.pt := hy
    rw [e] at this
    exact this

/-- **The two forms agree for one lifted developing pair** (hyperbolic `g`, every degree
`k ≥ 1`): l.915's `g x ≥ x` on `I⁺` iff the left extremities are repelling, and `g x ≤ x` on `I⁺`
iff they are attracting. -/
theorem GammaLinkCircle.IsLiftedDev.forms_iff (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter) {k : ℤ} (hk : 1 ≤ k) {g : GTilde} (hg : ∃ x, g x = x)
    (hh : GTilde.IsHyperbolic g) (hfg : f = GTilde.delta ^ k * g) :
    ((∀ s, E s ∈ C.iPlusL → D s ≤ g (D s)) ↔ ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsRepellingAt g (sInf (connectedComponentIn (C.iPlusTilde E D) t))) ∧
      ((∀ s, E s ∈ C.iPlusL → g (D s) ≤ D s) ↔ ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsAttractingAt g (sInf (connectedComponentIn (C.iPlusTilde E D) t))) := by
  have hD : range D = univ := h.range_eq_univ (by omega) hg hfg
  obtain ⟨x₀, x₁, h01, h10, hx₀, hx₁, -, hIp, -⟩ := h.iPlus_components hp hk hg hh hfg
  rw [GammaLinkCircle.forall_iPlusL_iff (P := fun y => y ≤ g y),
    GammaLinkCircle.forall_iPlusL_iff (P := fun y => g y ≤ y), h.iPlusTilde_eq hD, hIp]
  exact GTilde.forms_iff_of_consecutive hh h01 h10 hx₀ hx₁

/-- **OQ-120 (c): the two definitions of positivity agree** (l.908–910 and l.915). -/
theorem GammaLinkCircle.isSpacelikePositive_iff_rep :
    C.IsSpacelikePositive ↔ C.IsSpacelikePositiveRep := by
  constructor
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hpos⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      ((h.forms_iff hp hk hg hh hfg).1.1 hpos)⟩
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hrep⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      ((h.forms_iff hp hk hg hh hfg).1.2 hrep)⟩

/-- **OQ-120 (c): the two definitions of negativity agree** (l.911–913 and l.915). -/
theorem GammaLinkCircle.isSpacelikeNegative_iff_att :
    C.IsSpacelikeNegative ↔ C.IsSpacelikeNegativeAtt := by
  constructor
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hneg⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      ((h.forms_iff hp hk hg hh hfg).2.1 hneg)⟩
  · rintro ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hatt⟩
    exact ⟨hp, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      ((h.forms_iff hp hk hg hh hfg).2.2 hatt)⟩

/-- **The dichotomy in the l.908–913 form** (l.906–913): a space-like circle of degree `k ≥ 1`
with hyperbolic `g` has repelling left extremities or attracting ones, and not both kinds of
circle at once. -/
theorem GammaLinkCircle.IsLiftedDev.rep_dichotomy (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : C.pt ∈ HS.piece 2 .deSitter) {k : ℤ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hh : GTilde.IsHyperbolic g)
    (hfg : f = GTilde.delta ^ k * g) :
    (C.IsSpacelikePositiveRep ∨ C.IsSpacelikeNegativeAtt) ∧
      ¬ (C.IsSpacelikePositiveRep ∧ C.IsSpacelikeNegativeAtt) := by
  rw [← GammaLinkCircle.isSpacelikePositive_iff_rep, ← GammaLinkCircle.isSpacelikeNegative_iff_att]
  exact h.spacelike_dichotomy hθ hp hk hg hh hfg

/-- **Where the two forms part (OQ-128)**: without the guard « `g` hyperbolic », for a lifted
pair at `p ∈ dS²` of degree `k ≥ 1` (`f = δᵏ g`, `g` with a fixed point), l.915's inequality is
equivalent to the repelling form **iff `g ≠ 1`**; for `g = 1` (trivial `Γ_p`-holonomy) l.915's
inequality holds and no left extremity is repelling. -/
theorem GammaLinkCircle.IsLiftedDev.forms_iff_iff_ne_one (h : C.IsLiftedDev θ E D f)
    (hp : C.pt ∈ HS.piece 2 .deSitter) {k : ℤ} (hk : 1 ≤ k) {g : GTilde} (hg : ∃ x, g x = x)
    (hfg : f = GTilde.delta ^ k * g) :
    ((∀ s, E s ∈ C.iPlusL → D s ≤ g (D s)) ↔ ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsRepellingAt g (sInf (connectedComponentIn (C.iPlusTilde E D) t))) ↔ g ≠ 1 := by
  by_cases hg1 : g = 1
  · subst hg1
    have hpos : ∀ s, E s ∈ C.iPlusL → D s ≤ (1 : GTilde) (D s) := fun s _ => by
      rw [GTilde.one_apply]
    have hD := h.range_eq_univ (by omega) hg hfg
    obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
    obtain ⟨t, rfl⟩ := linkCover_surjective C.pt θ σ
    have ht : t ∈ C.iPlusTilde E D := by
      rw [h.iPlusTilde_eq hD, mem_preimage, iPlus_of_deSitter hp]; exact hσ
    simp only [ne_eq, not_true_eq_false, iff_false]
    intro hiff
    exact GTilde.not_isRepellingAt_one _ ((hiff.1 hpos) t ht)
  · refine iff_of_true ?_ hg1
    have hq : 0 < Causal.Flat.minkQ (C.pt : 𝕄) := hp
    obtain ⟨ρ, hρ⟩ := h.exists_linkCover_apply
    obtain ⟨m, hm⟩ := h.even_of_nonneg hq.le hg hfg
    have hgl : ∀ t, linkCover C.pt θ (g t) = ρ • linkCover C.pt θ t := fun t => by
      have e : f t = g t + k := by rw [hfg, GTilde.coe_mul_apply, GTilde.delta_zpow_apply]
      rw [← hρ, e, hm, show g t + ((m + m : ℤ) : ℝ) = g t + 2 * (m : ℝ) by push_cast; ring,
        linkCover_add_two_mul]
    have hpsl : GTilde.toPSL g ≠ 1 := fun h1 => by
      have hker : g ∈ GTilde.toPSL.ker := h1
      rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hker
      obtain ⟨j, rfl⟩ := hker
      obtain ⟨x, hx⟩ := hg
      rw [GTilde.delta_zpow_apply] at hx
      have hj : j = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
      exact hg1 (by rw [hj, zpow_zero])
    exact (h.forms_iff hp hk hg (isHyperbolic_of_linkCover hp hgl hpsl) hfg).1

omit [TopologicalSpace L] in
/-- **The two forms part at trivial holonomy, at every `p ∈ dS²`**: the degree-`4` cyclic cover of
`ℓ(p)` (`GX.exists_isPositive_delta_four`, lifted holonomy `δ⁴`, `g = 1`) satisfies l.915's
inequality and has no repelling left extremity. -/
theorem exists_forms_differ {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
      (E : ℝ → L) (D : ℝ → ℝ), C.pt = p ∧ IsOrientedTangent C.pt θ ∧
      C.IsLiftedDev θ E D (GTilde.delta ^ (4 : ℤ) * 1) ∧
      (∀ s, E s ∈ C.iPlusL → D s ≤ (1 : GTilde) (D s)) ∧
      ¬ ∀ t ∈ C.iPlusTilde E D,
        GTilde.IsRepellingAt 1 (sInf (connectedComponentIn (C.iPlusTilde E D) t)) := by
  obtain ⟨L, _, C, hC, -, -, -, -, -, θ, E, D, hθ, h⟩ := exists_isPositive_delta_four hp
  rw [← mul_one (GTilde.delta ^ (4 : ℤ))] at h
  have hpos : ∀ s, E s ∈ C.iPlusL → D s ≤ (1 : GTilde) (D s) := fun s _ => by
    rw [GTilde.one_apply]
  have key := h.forms_iff_iff_ne_one (hC ▸ hp) (k := 4) (by norm_num) ⟨0, GTilde.one_apply 0⟩
    rfl
  simp only [ne_eq, not_true_eq_false, iff_false] at key
  exact ⟨L, inferInstance, C, θ, E, D, hC, hθ, h, hpos, fun hrep => key ⟨fun _ => hrep,
    fun _ => hpos⟩⟩

end Rep

/-! ## 4. The remark under the four readings -/

section Assembly

variable {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']

/-- **`bbsrem:previous_section_observed_only` (iii) and « does not extend », under both readings
of OQ-120 (a) and (c).** (1) Positive and negative are not isomorphic, with the same `p` or
through any move, in l.915's form or in l.908–913's (the forms being equivalent, (2)); (3) at
every `p ∈ dS²` a positive and a negative circle, positive and negative in both forms, with
isomorphic `ℝP¹`-circles and isomorphic through no move. -/
theorem bbsrem_previous_section_observed_only_readings :
    (∀ (C : GammaLinkCircle L) (C' : GammaLinkCircle L'), C.IsSpacelikePositiveRep →
      C'.IsSpacelikeNegativeAtt → (∀ φ, ¬ C.IsIso C' φ) ∧
        ∀ B h φ, ¬ C.IsIsoVia C' B h φ) ∧
    (∀ (C : GammaLinkCircle L) (C' : GammaLinkCircle L'), C.IsSpacelikePositive →
      C'.IsSpacelikeNegative → (∀ φ, ¬ C.IsIso C' φ) ∧
        ∀ B h φ, ¬ C.IsIsoVia C' B h φ) ∧
    (∀ C : GammaLinkCircle L, (C.IsSpacelikePositive ↔ C.IsSpacelikePositiveRep) ∧
      (C.IsSpacelikeNegative ↔ C.IsSpacelikeNegativeAtt)) ∧
    ∀ p : HS 2, p ∈ HS.piece 2 .deSitter →
    ∃ (M M' : Type) (_ : TopologicalSpace M) (_ : TopologicalSpace M') (C : GammaLinkCircle M)
      (C' : GammaLinkCircle M'), C.pt = p ∧ C'.pt = p ∧ C.IsSpacelikePositive ∧
      C.IsSpacelikePositiveRep ∧ C'.IsSpacelikeNegative ∧ C'.IsSpacelikeNegativeAtt ∧
      (∀ B h φ, ¬ C.IsIsoVia C' B h φ) ∧ (∀ φ, ¬ C.IsIso C' φ) ∧
      ∃ (θ : TpHS C.pt ≃ₗ[ℝ] ℂ) (θ' : TpHS C'.pt ≃ₗ[ℝ] ℂ),
        letI := C.rp1ChartedSpace θ
        letI := C'.rp1ChartedSpace θ'
        haveI := C.rp1_hasGroupoid θ
        haveI := C'.rp1_hasGroupoid θ'
        ∃ φ : M ≃ₜ M', IsRP1Iso φ := by
  refine ⟨fun C C' hC hC' => ?_, fun C C' hC hC' => ?_, fun C =>
    ⟨GammaLinkCircle.isSpacelikePositive_iff_rep, GammaLinkCircle.isSpacelikeNegative_iff_att⟩,
    fun p hp => ?_⟩
  · rw [← GammaLinkCircle.isSpacelikePositive_iff_rep] at hC
    rw [← GammaLinkCircle.isSpacelikeNegative_iff_att] at hC'
    exact ⟨fun φ => not_isIso_of_positive_of_negative hC hC' φ,
      fun B h φ => not_isIsoVia_of_positive_of_negative hC hC' B h φ⟩
  · exact ⟨fun φ => not_isIso_of_positive_of_negative hC hC' φ,
      fun B h φ => not_isIsoVia_of_positive_of_negative hC hC' B h φ⟩
  · obtain ⟨M, M', _, _, C, C', hC, hC', hpos, hneg, hnot, θ, θ', hrp⟩ :=
      exists_rp1Iso_not_isIso hp
    exact ⟨M, M', inferInstance, inferInstance, C, C', hC, hC', hpos,
      GammaLinkCircle.isSpacelikePositive_iff_rep.1 hpos, hneg,
      GammaLinkCircle.isSpacelikeNegative_iff_att.1 hneg,
      fun B h φ => not_isIsoVia_of_positive_of_negative hpos hneg B h φ, hnot, θ, θ', hrp⟩

end Assembly

end GX
