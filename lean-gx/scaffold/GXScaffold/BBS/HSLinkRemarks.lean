import GXScaffold.BBS.HSClassification
import GXScaffold.BBS.HSRemarkReadings

/-!
# BBS § 3.3, two link remarks: cutting `dS²` along a light-like ray (`bbsrem:cuttachyon2`) and the absent sign of BTZ-like singularities (`bbsrem:however_no_positive_negative`)

Target `T-bbs-link-remarks` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx, DEC-192).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`. Imports `GXScaffold.BBS.HSClassification` (the types,
`GX.GammaLinkCircle.HasType`) and `GXScaffold.BBS.HSRemarkReadings` (the l.908–913 form of
positivity), over the sorry-free scaffold `GXScaffold.BBS.{HSSingularities, HSDegree, HSPositive}`.

* `bbsrem:cuttachyon2` — `colI_v1.tex:1299` — partial (unmarked: the two printed clauses cannot
  both hold under any single side-of-line gluing rule, a finding, SCOPE (c); which one fails
  depends on the holonomy sign convention; the surgery is read on the link, SCOPE (a)): the link of the surgery `GX.GammaLinkCircle.IsCutGlueLink`, built by
  `GX.exists_isCutGlueLink`; space-like of degree `2` `GX.GammaLinkCircle.IsCutGlueLink.hasType`;
  in the library's convention (`D (s + 1) = f (D s)`, holonomy = gluing map⁻¹), **positive iff `γ`
  sends every point of `r` into its own past, whatever the orientation of `r`**, under the rule (l.1303–1304: the future copy of `r` glued into the past copy)
  `GX.GammaLinkCircle.IsCutGlueLink.isPositive_iff_past`, and iff into its future under the other
  rule `…isPositive_iff_future`; the printed statement under the one reading that makes both its
  clauses true `GX.GammaLinkCircle.IsCutGlueLink.bbsrem_cuttachyon2_reading`; relative to the
  library's convention and the rule l.1303–1304, a link where the future-oriented clause fails
  `GX.not_cuttachyon2_future_printed`.
* `bbsrem:however_no_positive_negative` — `colI_v1.tex:1480` — partial (unmarked: « no
  dichotomy » is a reading, SCOPE (d), and the types rest on OQ-116 (b), OQ-135): the assembly
  `GX.GammaLinkCircle.bbsrem_however_no_positive_negative`; a degree-`0` circle is positive and
  none of the four signed notions of l.906–922 applies to it
  `GX.GammaLinkCircle.isPositive_of_fixed`, `GX.GammaLinkCircle.not_signed_of_fixed`; the sign of
  l.915 read at degree `0` is forced by the orientation (`GX.GammaLinkCircle.IsLiftedDev.lt_apply`
  of HSSingularities).

> As a corollary we get the following description space-like HS-singularities of degree $2$:
> consider a small disk $U$ in $\dS^2$ and a point $x$ in $U$. Let $r$ be one light-like geodesic
> ray contained in $U$ issued from $x$, cut along it and glue back by a hyperbolic
> $\dS^2$-isometry $\gamma$ like described in figure~\ref{fig.tachyon} (be careful that in this
> figure, the isometry, glueing the future copy of $r$ in the boundary of $U \setminus r$ into the
> past copy of $r$; hence $\gamma$ is the inverse of the holonomy). Observe that one cannot match
> one side on the other, but the resulting space is still homeomorphic to the disk. The resulting
> HS-singularity is space-like, of degree $2$. If $r$ is future oriented, the singularity is
> positive if and only if for every $y$ in $r$ the image $\gamma y$ lies in the future of $y$. If
> $r$ is past oriented, the singularity is positive if and only if $\gamma y$ lies in the past of
> $y$ for every $y$ in $r$. (l.1301–1311)
>
> However, there is no positive/negative dichotomy for BTZ-like singularities, extreme or not.
> (l.1481)

## Main declarations (all proved, 0 `sorry`)

* **The surgery link.** `GX.IsNullTangent`, `GX.rayPt` (the ray `[x + s w]`), `GX.FutureSide`
  (the future side of the line `ℝ w`, by a sign `GX.futureSide_iff`), `GX.SourceFirst` and
  `GX.cutGlueHol` (the rule and the holonomy it gives; by a sign `GX.CutGlue.sourceFirst_iff`,
  `GX.CutGlue.cutGlueHol_dsBoost`), `GX.GammaLinkCircle.IsCutGlueLink`, `GX.exists_isCutGlueLink`.
* **Orientation of `ℓ(x)`.** `GX.CutGlue.vol3_linkCover_pos` (`linkCover` turns in the sense of
  `vol3 x`), `GX.CutGlue.sign_of_lift` (a lift with a fixed point moves `t` up iff the pair
  (direction, image) is direct), `GX.CutGlue.future_up_iff` (the boost of rapidity `ζ` moves the
  future time-like directions up iff `ζ · vol3 x e₀ j > 0`).
* **The push.** `GX.CutGlue.push_iff`: `γ [x + s w]` is in the causal past of `[x + s w]` iff
  `⟨w, j⟩ ζ < 0` (`GX.CutGlue.IsCausalPast`, the order of `GX.DSLe`).
* **The remark.** `GX.GammaLinkCircle.IsCutGlueLink.core`, `…hasType`, `…isPositive_iff_past`,
  `…isPositive_iff_future`, `…bbsrem_cuttachyon2_reading`, `GX.not_cuttachyon2_future_printed`.
* **Degree `0`.** `GX.GammaLinkCircle.IsLiftedDev.fixed_of_fixed`, `…isPositive_of_fixed`,
  `…not_signed_of_fixed`, `GX.LinkType.IsBTZLike`, `…bbsrem_however_no_positive_negative`.

## Hypothesis checklist

| BBS | here |
|---|---|
| `x ∈ U ⊆ dS²`, `r` a light-like ray from `x` in `U` | ✓ `x = C.pt ∈ dS²`, `r = {[x + s w] : 0 < s < ε}`, `w` a non-zero null vector of `x^⊥` (`GX.IsNullTangent`), every `ε > 0` |
| « a hyperbolic `dS²`-isometry `γ` » gluing `r` to itself | ⚠ read: `γ ∈ Γ_x ∖ {1}` (it must fix `x` for the result to be a cone point at `x`; every such `γ` is hyperbolic, `GX.GammaP.exists_eq_dsBoost`) |
| « cut along it and glue back » | ⚠ read on the link (SCOPE (a)): `ℓ(x)` cut at the direction of `r`, glued by `γ` (`GX.GammaLinkCircle.IsCutGlueLink`) |
| « the future copy of `r` glued into the past copy » (l.1303–1304) | ⚠ read: the future copy bounds the side of `r` lying in the future of the line of `r` (`GX.FutureSide`); the rule is the parameter `src` (`true` = printed) |
| « `γ` is the inverse of the holonomy » (l.1304) | ⚠ read: replaced by the derived holonomy `GX.cutGlueHol` (in the library's convention `D (s + 1) = f (D s)`, `γ⁻¹` when the positive sense crosses from the glued copy into the other one, `γ` otherwise); the paper's sentence is a convention statement tied to the figure and to the holonomy convention of SCOPE (c) |
| « space-like, of degree 2 » | ✓ `GX.GammaLinkCircle.IsCutGlueLink.hasType` (and not regular) |
| « positive » | ✓ both forms: l.915 (`IsPositive`) and l.908–913 (`IsSpacelikePositiveRep`) |
| « `γ y` lies in the future / past of `y` » | ✓ the causal order of `dS²` (`GX.CutGlue.IsCausalPast`, the definition of `GX.DSLe`) |
| the two clauses (future- and past-oriented `r`) | ⚠ not both true under one side-of-line rule (SCOPE (c)); in the library's convention the future-oriented clause fails under the rule l.1303–1304 (`GX.not_cuttachyon2_future_printed`), in the convention of the paper's worked examples the past-oriented one does |
| « homeomorphic to the disk » | ✗ not stated (SCOPE (b)) |
| « BTZ-like singularities, extreme or not » | ✓ the types `btzPast`, `btzFuture`, `extremeBTZ` of `GX.LinkType` (and every degree-`0` circle) |
| « no positive/negative dichotomy » | ⚠ read (SCOPE (d)) |

## SCOPE (disclosed)

* **(a) The surgery is read on its link.** Near `x`, cutting `U` along `r` and gluing back by
  `γ ∈ Γ_x` gives, by definition of a singular HS-surface (l.948–953), a neighbourhood of the
  apex of `𝔢(L)` where `L` is `ℓ(x)` cut at the direction `d` of `r` and glued by `γ` (the
  suspension of `d` is the light-like geodesic through `x` in the direction of `r`). That `L` is
  `ℝ/⟨δ² g⟩`, `g` the lift with a fixed point of the holonomy `h` of the positive loop: crossing
  the cut from the glued copy into the other one the developing map is composed with `γ⁻¹`, so
  `h = γ⁻¹` if the positive sense of `ℓ(x)` crosses the cut from the glued copy, `γ` otherwise
  (`GX.cutGlueHol`, `GX.SourceFirst`). The identification of the surgered surface with an open set
  of `𝔢(L)` is argued, not formalized; the AdS derivation of l.1287–1297 is not claimed.
* **(b) Not stated:** « one cannot match one side on the other, but the resulting space is still
  homeomorphic to the disk ».
* **(c) Finding (the sign), convention-free form.** For any single side-of-line gluing rule,
  positivity of the surgery link does not depend on the orientation of `r`: it depends only on the
  rule and on the direction in which `γ` pushes `r` (`…isPositive_iff_past`,
  `…isPositive_iff_future`). Hence the two printed clauses (future-oriented: « future »,
  past-oriented: « past ») cannot both hold under one rule; they hold together exactly when the
  copy glued by `γ` is the one facing the space-like quadrant at `x`
  (`…bbsrem_cuttachyon2_reading`). **Which clause fails depends on the holonomy sign convention.**
  In the library's convention (`IsLiftedDev`: `D (s + 1) = f (D s)`, so the developing holonomy is
  the gluing map⁻¹, and positivity in the form of l.908–915 read with it, HSPositive), under the
  rule l.1303–1304 read literally the future-oriented clause fails
  (`GX.not_cuttachyon2_future_printed`) and the past-oriented one holds. In the convention of the
  paper's worked examples (the holonomy is the gluing map: `T_m`, l.1229–1233;
  `bbsrem:positive_negative`, l.1239–1246; the AdS sentence l.1290–1296), every sign flips, and it
  is the past-oriented clause that fails. Which convention is of record is an open question
  (extending OQ-120 (c)); no restatement should follow before it is ruled.
* **(d) « No positive/negative dichotomy »** is read: every circle of these types (indeed every
  `(Γ_p, ℓ(p))`-circle of degree `0`, `f` with a fixed point) is positive in the sense of
  `GX.GammaLinkCircle.IsPositive` (its clauses are about degree `≥ 2`), and none is positive or
  negative in any of the four signed senses of l.906–922 (they need a degree `k ≥ 1`); the
  inequality of l.915 read at degree `0` (`g = f`) holds for every oriented lifted pair, its
  reverse never on a non-empty `I⁺`, so no sign splits a type. That such circles occur is not
  formalized (OQ-135 (c)).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The causal order of `dS²` -/

namespace CutGlue

/-- The point of the hyperboloid `{Q = 1}` on the ray `σ` (for `σ ∈ dS²`). -/
def hyp (σ : HS 2) : 𝕄 := (Real.sqrt (Causal.Flat.minkQ (σ : 𝕄)))⁻¹ • (σ : 𝕄)

/-- **`τ` lies in the causal past of `σ` in `dS²`**: both in `dS²`, and the difference of their
points on the hyperboloid is future causal (or zero). This is `GX.DSLe τ σ` of
`GXScaffold.BBS.HSCausal`, restated so that this module does not depend on it (HSCausal rests on
a tagged `sorry`, so an import would hold this sorry-free module back from graduating). The
identities are stated there, by `rfl`/`Iff.rfl`: `GX.CutGlue.isCausalPast_iff_dsLe`,
`GX.CutGlue.isCausalFuture_iff_dsLe`, `GX.CutGlue.hyp_eq_dsHat` (T-gx-btz-cleanup). -/
def IsCausalPast (τ σ : HS 2) : Prop :=
  τ ∈ HS.piece 2 .deSitter ∧ σ ∈ HS.piece 2 .deSitter ∧ Causal.Flat.IsFutureCausal (hyp σ - hyp τ)

/-- `τ` lies in the causal future of `σ` in `dS²`. -/
def IsCausalFuture (τ σ : HS 2) : Prop := IsCausalPast σ τ

end CutGlue

/-! ## 2. Light-like rays issued from `x ∈ dS²` -/

/-- **A light-like tangent vector at `x`**: a non-zero null vector of `x^⊥`. -/
structure IsNullTangent (x : HS 2) (w : 𝕄) : Prop where
  perp : Causal.Flat.minkB (x : 𝕄) w = 0
  null : Causal.Flat.minkQ w = 0
  ne : w ≠ 0

/-- The point `[x + s w]` of the light-like ray issued from `x` in the direction `w`. -/
def rayPt (x : HS 2) (w : 𝕄) (s : ℝ) : HS 2 := rayNormalize x ((x : 𝕄) + s • w)

/-- **`v` points to the future side of the line `ℝ w`**: some `v + t w` is future time-like. -/
def FutureSide (w v : 𝕄) : Prop := ∃ t : ℝ, Causal.Flat.IsFutureTimelike (v + t • w)

/-- **The gluing rule.** `src = true`: `γ` glues the copy of `r` on the future side of the line of
`r` into the other copy (l.1303–1304 as printed); `src = false`: the copy on the past side.
`SourceFirst x w src`: the side `{v | vol3 x w v < 0}`, the one the positive sense of `ℓ(x)`
crosses before the cut, is the glued one. -/
def SourceFirst (x : HS 2) (w : 𝕄) (src : Bool) : Prop :=
  ∀ v : 𝕄, Causal.Flat.minkB (x : 𝕄) v = 0 → vol3 x w v < 0 → (FutureSide w v ↔ src = true)

open Classical in
/-- **The holonomy of the positive loop** around the cut-and-glued point: `γ⁻¹` if the positive
sense crosses the cut from the glued copy into the other one, `γ` otherwise, in the library's
convention (`D(s+1) = f(D s)`: the holonomy is the gluing map⁻¹). It replaces l.1304's « `γ` is
the inverse of the holonomy », which holds in the paper's convention (OQ-144); a reading, not a
proof of that sentence. -/
def cutGlueHol (x : HS 2) (w : 𝕄) (γ : GammaP x) (src : Bool) : GammaP x :=
  if SourceFirst x w src then γ⁻¹ else γ

variable {L : Type*} [TopologicalSpace L]

/-- **`C` is the link at `x` of the surgery** cutting along the light-like ray of `w` and gluing
back by `γ` with the rule `src`: an oriented lifted developing pair with lifted holonomy `δ² g`,
`g` the lift with a fixed point of `cutGlueHol x w γ src` (the circle `ℓ(x)` cut at the direction
of `w` and glued: `ℝ/⟨δ² g⟩`, `GX.exists_isCutGlueLink`). -/
def GammaLinkCircle.IsCutGlueLink (C : GammaLinkCircle L) (w : 𝕄) (γ : GammaP C.pt)
    (src : Bool) : Prop :=
  ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧ ∃ (E : ℝ → L) (D : ℝ → ℝ) (g : GTilde),
    C.IsLiftedDev θ E D (GTilde.delta ^ (2 : ℤ) * g) ∧
    (∀ t, linkCover C.pt θ (g t) = cutGlueHol C.pt w γ src • linkCover C.pt θ t) ∧
    ∃ t, g t = t

/-- **The surgery link exists** (`ℝ/⟨δ² g⟩`, `GX.exists_isLiftedDev_delta_sq_mul`). -/
theorem exists_isCutGlueLink {x : HS 2} (hx : x ∈ HS.piece 2 .deSitter) (w : 𝕄) (γ : GammaP x)
    (src : Bool) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link x) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
      (GammaLinkCircle.mk x cs hcs hL).IsCutGlueLink w γ src := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent x
  obtain ⟨g, hg, hfix⟩ := exists_lift_fixed (le_of_lt hx) θ (cutGlueHol x w γ src)
  obtain ⟨L, _, cs, hcs, hL, E, D, hl⟩ := exists_isLiftedDev_delta_sq_mul x θ hg hfix
  exact ⟨L, inferInstance, cs, hcs, hL, θ, hθ, E, D, g, hl, hg, hfix⟩

/-! ## 2'. Computations in the frame `(GammaP.dsE₀ x, jVec x)` of `x^⊥` -/

namespace CutGlue

theorem vol3_smul_right (u v w : 𝕄) (c : ℝ) : vol3 u v (c • w) = c * vol3 u v w := by
  rw [vol3_eq, vol3_eq]
  simp only [Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul]
  ring

theorem vol3_add_right (u v w w' : 𝕄) : vol3 u v (w + w') = vol3 u v w + vol3 u v w' := by
  rw [vol3_eq, vol3_eq, vol3_eq]
  simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply]
  ring

theorem vol3_self (u v : 𝕄) : vol3 u v v = 0 := by
  rw [vol3_eq]; ring

theorem vol3_swap (u v w : 𝕄) : vol3 u w v = -vol3 u v w := by
  rw [vol3_eq, vol3_eq]; ring

theorem vol3_comb (u v w : 𝕄) (a b c d : ℝ) :
    vol3 u (a • v + b • w) (c • v + d • w) = (a * d - b * c) * vol3 u v w :=
  vol3_lin u v w a b c d

variable {x : HS 2}

/-- The frame of `x^⊥` at `x ∈ dS²`, as one hypothesis. -/
theorem frame (hx : x ∈ HS.piece 2 .deSitter) :
    Causal.Flat.minkB (GammaP.dsE₀ x) (GammaP.dsE₀ x) = -1 ∧ Causal.Flat.minkB (jVec x) (jVec x) = 1 ∧
      Causal.Flat.minkB (GammaP.dsE₀ x) (jVec x) = 0 ∧ Causal.Flat.minkB (x : 𝕄) (GammaP.dsE₀ x) = 0 ∧
      Causal.Flat.minkB (x : 𝕄) (jVec x) = 0 ∧ 0 < (GammaP.dsE₀ x).1 ∧ (jVec x).1 = 0 := by
  obtain ⟨h0, h1, h01, hx0, hx1, hfe⟩ := GammaP.dsFrame hx
  exact ⟨by rw [← Causal.Flat.minkQ_eq_minkB, h0], by rw [← Causal.Flat.minkQ_eq_minkB, h1],
    h01, hx0, hx1, hfe.1, rfl⟩

/-- `vol3 x e₀ j ≠ 0`: `(x, e₀, j)` is a basis. -/
theorem vol3_frame_ne (hx : x ∈ HS.piece 2 .deSitter) : vol3 x (GammaP.dsE₀ x) (jVec x) ≠ 0 := by
  obtain ⟨h00, h11, h01, hx0, hx1, -, -⟩ := frame hx
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  obtain ⟨K, hK, hvol⟩ := exists_vol3_eq_linkArea x
  rw [hvol]
  refine mul_ne_zero ?_ hK
  intro h0
  have hne : tpMk x (GammaP.dsE₀ x) ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff x).1 h
    have := congrArg (fun v => Causal.Flat.minkB v (GammaP.dsE₀ x)) hc
    simp only [Causal.Flat.minkB_smul_left, h00] at this
    simp only [hx0, mul_zero] at this
    norm_num at this
  obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero x hne h0
  obtain ⟨c, hc⟩ := (tpMk_eq_tpMk_iff x).1 (hr.trans (Submodule.Quotient.mk_smul _ r _).symm)
  have := congrArg (fun v => Causal.Flat.minkB v (jVec x)) hc
  simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01, hx1] at this
  norm_num at this

/-- Every vector of `x^⊥` is a combination of `e₀, j`. -/
theorem exists_frame_comb (hx : x ∈ HS.piece 2 .deSitter) {v : 𝕄}
    (hv : Causal.Flat.minkB (x : 𝕄) v = 0) : ∃ a b : ℝ, v = a • GammaP.dsE₀ x + b • jVec x := by
  obtain ⟨h00, h11, h01, hx0, hx1, -, -⟩ := frame hx
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  obtain ⟨K, hK, hvol⟩ := exists_vol3_eq_linkArea x
  have harea : linkArea x (tpMk x (GammaP.dsE₀ x)) (tpMk x (jVec x)) ≠ 0 := fun h0 => by
    apply vol3_frame_ne hx; rw [hvol, h0, zero_mul]
  have hz := eq_add_of_linkArea_ne_zero x harea (tpMk x v)
  set a := linkArea x (tpMk x v) (tpMk x (jVec x)) / linkArea x (tpMk x (GammaP.dsE₀ x)) (tpMk x (jVec x))
  set b := linkArea x (tpMk x (GammaP.dsE₀ x)) (tpMk x v) / linkArea x (tpMk x (GammaP.dsE₀ x)) (tpMk x (jVec x))
  obtain ⟨c, hc⟩ := (tpMk_eq_tpMk_iff x).1 (show tpMk x v = tpMk x (a • GammaP.dsE₀ x + b • jVec x) from by
    rw [hz]; rfl)
  have hc0 : c = 0 := by
    have := congrArg (fun u => Causal.Flat.minkB (x : 𝕄) u) hc
    simp only [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, hx0, hx1, hv,
      ← Causal.Flat.minkQ_eq_minkB] at this
    have h' : c * Causal.Flat.minkQ (x : 𝕄) = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_right hQ.ne'
  exact ⟨a, b, by rw [hc, hc0, zero_smul, add_zero]⟩

/-- **A light-like tangent vector at `x`** is `a e₀ + b j` with `b² = a²`, `a ≠ 0`. -/
theorem IsNullTangent.decomp (hx : x ∈ HS.piece 2 .deSitter) {w : 𝕄} (hw : IsNullTangent x w) :
    ∃ a b : ℝ, w = a • GammaP.dsE₀ x + b • jVec x ∧ b ^ 2 = a ^ 2 ∧ a ≠ 0 := by
  obtain ⟨h00, h11, h01, -, -, -, -⟩ := frame hx
  obtain ⟨a, b, rfl⟩ := exists_frame_comb hx hw.perp
  have hQ := hw.null
  rw [Causal.Flat.minkQ_eq_minkB] at hQ
  simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_left,
    Causal.Flat.minkB_smul_right, h00, h11, h01, Causal.Flat.minkB_comm (jVec x) (GammaP.dsE₀ x)] at hQ
  have hab : b ^ 2 = a ^ 2 := by linarith
  refine ⟨a, b, rfl, hab, fun ha => hw.ne ?_⟩
  have hb : b = 0 := by
    rw [ha] at hab; exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by rw [hab]; norm_num)
  rw [ha, hb, zero_smul, zero_smul, add_zero]

end CutGlue

/-- **The future side of a null line, by a sign** (`w` null, non-zero): `v + t w` is future
time-like for some `t` iff `w₀ ⟨v, w⟩ < 0`. -/
theorem futureSide_iff {w : 𝕄} (hw0 : Causal.Flat.minkQ w = 0) (hwne : w ≠ 0) (v : 𝕄) :
    FutureSide w v ↔ w.1 * Causal.Flat.minkB v w < 0 := by
  have hw1 : w.1 ≠ 0 := fun h => hwne (Causal.Flat.eq_zero_of_fst_eq_zero h hw0.le)
  -- the case `w₀ > 0`
  have key : ∀ w : 𝕄, Causal.Flat.minkQ w = 0 → w ≠ 0 → 0 < w.1 →
      (FutureSide w v ↔ Causal.Flat.minkB v w < 0) := by
    intro w hw0 hwne hpos
    have hwf : Causal.Flat.IsFutureCausal w := ⟨hpos.le, hw0.le⟩
    constructor
    · rintro ⟨t, ht⟩
      have h := Causal.Flat.minkB_neg_of_future hwf hwne ht
      rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, ← Causal.Flat.minkQ_eq_minkB,
        hw0, mul_zero, add_zero, Causal.Flat.minkB_comm] at h
      exact h
    · intro hB
      refine ⟨(|Causal.Flat.minkQ v| + 1) / (-2 * Causal.Flat.minkB v w) + (|v.1| + 1) / w.1,
        ?_, ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have h1 : 0 ≤ (|Causal.Flat.minkQ v| + 1) / (-2 * Causal.Flat.minkB v w) :=
          div_nonneg (by positivity) (by linarith)
        have h2 : ((|v.1| + 1) / w.1) * w.1 = |v.1| + 1 := div_mul_cancel₀ _ hpos.ne'
        nlinarith [neg_abs_le v.1, mul_nonneg h1 hpos.le]
      · rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, hw0, Causal.Flat.minkB_smul_right]
        set t₁ := (|Causal.Flat.minkQ v| + 1) / (-2 * Causal.Flat.minkB v w)
        have ht₁ : t₁ * (-2 * Causal.Flat.minkB v w) = |Causal.Flat.minkQ v| + 1 :=
          div_mul_cancel₀ _ (by linarith)
        have h2 : 0 ≤ (|v.1| + 1) / w.1 := div_nonneg (by positivity) hpos.le
        nlinarith [le_abs_self (Causal.Flat.minkQ v), mul_nonneg h2 (show 0 ≤ -Causal.Flat.minkB v w by linarith)]
  rcases lt_or_gt_of_ne hw1 with hneg | hpos
  · have e : FutureSide w v ↔ FutureSide (-w) v := by
      constructor
      · rintro ⟨t, ht⟩; exact ⟨-t, by rwa [smul_neg, neg_smul, neg_neg]⟩
      · rintro ⟨t, ht⟩; exact ⟨-t, by rwa [neg_smul, ← smul_neg]⟩
    rw [e, key (-w) (by rw [Causal.Flat.minkQ_neg, hw0]) (neg_ne_zero.2 hwne)
      (by simp only [Prod.fst_neg]; linarith)]
    rw [Causal.Flat.minkB_comm v (-w), Causal.Flat.minkB_neg_left, Causal.Flat.minkB_comm]
    constructor
    · intro h; nlinarith
    · intro h
      have : 0 < Causal.Flat.minkB v w := by
        by_contra hc; push Not at hc; nlinarith
      linarith
  · rw [key w hw0 hwne hpos]
    constructor
    · intro h; nlinarith
    · intro h
      by_contra hc; push Not at hc; nlinarith

/-! ## 2''. The orientation of `ℓ(x)` and the sign of a lift -/

namespace CutGlue

variable {x : HS 2}

/-- A lift of `linkCover x θ t` to `ℝ^{1,2}`, through lifts `w₁, w₂` of `θ⁻¹ 1, θ⁻¹ i`. -/
theorem exists_tpMk_linkCover (θ : TpHS x ≃ₗ[ℝ] ℂ) {w₁ w₂ : 𝕄} (h₁ : tpMk x w₁ = θ.symm 1)
    (h₂ : tpMk x w₂ = θ.symm Complex.I) (t : ℝ) :
    ∃ k : ℝ, 0 < k ∧ ((linkCover x θ t : Link x) : TpHS x) =
      tpMk x (k • (Real.cos (Real.pi * t) • w₁ + Real.sin (Real.pi * t) • w₂)) := by
  have he : ((Circle.exp (Real.pi * t) : Circle) : ℂ) =
      (Real.cos (Real.pi * t)) • (1 : ℂ) + (Real.sin (Real.pi * t)) • Complex.I := by
    rw [Circle.coe_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.real_smul, mul_one]
  refine ⟨‖θ.symm (Circle.exp (Real.pi * t))‖⁻¹, inv_pos.2 (norm_pos_iff.2 ?_), ?_⟩
  · exact (LinearEquiv.map_ne_zero_iff _).2 (by simp)
  · rw [coe_linkCover]
    conv_lhs => rw [he]
    rw [he, map_add, map_smul, map_smul, ← h₁, ← h₂]
    simp only [tpMk, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_add]

/-- **`linkCover` turns in the positive sense of `vol3 x`** (`θ` oriented): for
`t < t' < t + 1`, lifts of `linkCover t`, `linkCover t'` form a direct pair. -/
theorem vol3_linkCover_pos {θ : TpHS x ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent x θ) {t t' : ℝ}
    (h1 : t < t') (h2 : t' < t + 1) {v v' : 𝕄}
    (hv : tpMk x v = ((linkCover x θ t : Link x) : TpHS x))
    (hv' : tpMk x v' = ((linkCover x θ t' : Link x) : TpHS x)) : 0 < vol3 x v v' := by
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm 1)
  obtain ⟨w₂, hw₂⟩ := Submodule.Quotient.mk_surjective _ (θ.symm Complex.I)
  have hV := hθ w₁ w₂ hw₁ hw₂
  obtain ⟨k, hk, e⟩ := exists_tpMk_linkCover θ hw₁ hw₂ t
  obtain ⟨k', hk', e'⟩ := exists_tpMk_linkCover θ hw₁ hw₂ t'
  rw [vol3_eq_of_mk_eq x (hv.trans e) (hv'.trans e'), smul_add, smul_add, smul_smul, smul_smul,
    smul_smul, smul_smul, vol3_comb]
  have hs : 0 < Real.sin (Real.pi * t' - Real.pi * t) := Real.sin_pos_of_pos_of_lt_pi
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [Real.sin_sub] at hs
  have : k * Real.cos (Real.pi * t) * (k' * Real.sin (Real.pi * t')) -
      k * Real.sin (Real.pi * t) * (k' * Real.cos (Real.pi * t')) =
      k * k' * (Real.sin (Real.pi * t') * Real.cos (Real.pi * t) - Real.cos (Real.pi * t') * Real.sin (Real.pi * t)) := by
    ring
  rw [this]
  exact mul_pos (mul_pos (mul_pos hk hk') hs) hV

/-- A lift with a fixed point moves every point by less than a half-turn of `linkCover`. -/
theorem GTilde.sub_lt_one_of_fixed {g : GTilde} (hfix : ∃ c, g c = c) (t : ℝ) :
    t - 1 < g t ∧ g t < t + 1 := by
  obtain ⟨c, hc⟩ := hfix
  set n := ⌊t - c⌋
  have hn1 : c + n ≤ t := by have := Int.floor_le (t - c); linarith
  have hn2 : t < c + n + 1 := by have := Int.lt_floor_add_one (t - c); linarith
  have g1 : g (c + n) = c + n := by rw [GTilde.map_add_int, hc]
  have g2 : g (c + (n + 1 : ℤ)) = c + (n + 1 : ℤ) := by rw [GTilde.map_add_int, hc]
  push_cast at g2
  have a1 : g (c + n) ≤ g t := (GTilde.strictMono g).monotone hn1
  have a2 : g t < g (c + (n + 1)) := GTilde.strictMono g (by linarith)
  constructor <;> linarith

/-- **The sign of a lift on a direction**: if `g` lifts `A ∈ Γ_x` with a fixed point, `g` moves
`t` up iff a lift of `linkCover t` and a lift of its image by `A` form a direct pair. -/
theorem sign_of_lift {θ : TpHS x ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent x θ) {A : GammaP x} {g : GTilde}
    (hg : ∀ t, linkCover x θ (g t) = A • linkCover x θ t) (hfix : ∃ c, g c = c) {t : ℝ}
    {v v' : 𝕄} (hv : tpMk x v = ((linkCover x θ t : Link x) : TpHS x))
    (hv' : tpMk x v' = ((A • linkCover x θ t : Link x) : TpHS x)) :
    (t < g t → 0 < vol3 x v v') ∧ (g t < t → vol3 x v v' < 0) := by
  rw [← hg t] at hv'
  obtain ⟨b1, b2⟩ := GTilde.sub_lt_one_of_fixed hfix t
  refine ⟨fun h => vol3_linkCover_pos hθ h b2 hv hv', fun h => ?_⟩
  have := vol3_linkCover_pos hθ h (by linarith) hv' hv
  rw [vol3_swap] at this
  linarith

theorem tpMk_dsE₀_ne (hx : x ∈ HS.piece 2 .deSitter) : tpMk x (GammaP.dsE₀ x) ≠ 0 := fun h => by
  obtain ⟨h00, -, -, hx0, -, -, -⟩ := frame hx
  obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff x).1 h
  have := congrArg (fun v => Causal.Flat.minkB v (GammaP.dsE₀ x)) hc
  simp only [Causal.Flat.minkB_smul_left, h00, hx0, mul_zero] at this
  norm_num at this

/-- The direction of `e₀` at `x`: a future time-like direction. -/
theorem dirOf_dsE₀_mem (hx : x ∈ HS.piece 2 .deSitter) :
    dirOf x (GammaP.dsE₀ x) ∈ dsFutureDirs x := by
  obtain ⟨h00, -, -, hx0, -, hpos, -⟩ := frame hx
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  show Causal.Flat.IsFutureTimelike (dsProj x (dirOf x (GammaP.dsE₀ x)))
  rw [dsProj_dirOf x (tpMk_dsE₀_ne hx), perpLin_apply, hx0, zero_smul, sub_zero, smul_smul]
  have hk : 0 < ‖tpMk x (GammaP.dsE₀ x)‖⁻¹ * Causal.Flat.minkQ (x : 𝕄) :=
    mul_pos (inv_pos.2 (norm_pos_iff.2 (tpMk_dsE₀_ne hx))) hQ
  refine ⟨?_, ?_⟩
  · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos hk hpos
  · rw [Causal.Flat.minkQ_smul, Causal.Flat.minkQ_eq_minkB (GammaP.dsE₀ x), h00]; nlinarith

/-- The boost of rapidity `ζ` on `e₀`. -/
theorem dsBoost_dsE₀ (hx : x ∈ HS.piece 2 .deSitter) (ζ : ℝ) :
    (((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (GammaP.dsE₀ x) =
      Real.cosh ζ • GammaP.dsE₀ x + Real.sinh ζ • jVec x := by
  obtain ⟨h00, -, h01, -, -, -, -⟩ := frame hx
  rw [GammaP.dsBoost_apply, Causal.Flat.boostLin_apply, h00, h01]
  module

/-- The boost of rapidity `ζ` on `e₀ ± j`... on a combination `a e₀ + b j`. -/
theorem dsBoost_comb (hx : x ∈ HS.piece 2 .deSitter) (ζ a b : ℝ) :
    (((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
        (a • GammaP.dsE₀ x + b • jVec x) =
      (a * Real.cosh ζ + b * Real.sinh ζ) • GammaP.dsE₀ x +
        (a * Real.sinh ζ + b * Real.cosh ζ) • jVec x := by
  obtain ⟨h00, h11, h01, -, -, -, -⟩ := frame hx
  have h10 : Causal.Flat.minkB (jVec x) (GammaP.dsE₀ x) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact h01
  rw [GammaP.dsBoost_apply, Causal.Flat.boostLin_apply]
  simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h00, h11, h01, h10]
  module

theorem dsBoost_ne_one (hx : x ∈ HS.piece 2 .deSitter) {ζ : ℝ} (hζ : ζ ≠ 0) :
    GammaP.dsBoost hx ζ ≠ 1 := fun h => by
  obtain ⟨-, h11, h01, -, -, -, -⟩ := frame hx
  have e := dsBoost_dsE₀ hx ζ
  rw [h] at e
  have := congrArg (fun v => Causal.Flat.minkB v (jVec x)) e
  simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01] at this
  have h0 : Real.sinh ζ = 0 := by
    have : Causal.Flat.minkB ((((1 : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (GammaP.dsE₀ x)) (jVec x) = 0 := by
      show Causal.Flat.minkB (GammaP.dsE₀ x) (jVec x) = 0; exact h01
    linarith
  exact hζ (Real.sinh_eq_zero.1 h0)

/-- **The core sign** at `x ∈ dS²`: the lift with a fixed point of the boost of rapidity
`ζ ≠ 0` moves the future time-like directions up iff `0 < ζ · vol3 x e₀ j`, down iff `< 0`. -/
theorem future_up_iff (hx : x ∈ HS.piece 2 .deSitter) {θ : TpHS x ≃ₗ[ℝ] ℂ}
    (hθ : IsOrientedTangent x θ) {ζ : ℝ} (hζ : ζ ≠ 0) {g : GTilde}
    (hg : ∀ t, linkCover x θ (g t) = GammaP.dsBoost hx ζ • linkCover x θ t)
    (hfix : ∃ c, g c = c) :
    ((∀ t, linkCover x θ t ∈ dsFutureDirs x → t < g t) ↔
        0 < ζ * vol3 x (GammaP.dsE₀ x) (jVec x)) ∧
      ((∀ t, linkCover x θ t ∈ dsFutureDirs x → g t < t) ↔
        ζ * vol3 x (GammaP.dsE₀ x) (jVec x) < 0) := by
  set A := GammaP.dsBoost hx ζ
  set V := vol3 x (GammaP.dsE₀ x) (jVec x)
  have hA1 : A ≠ 1 := dsBoost_ne_one hx hζ
  set σ₀ := dirOf x (GammaP.dsE₀ x)
  have hσ₀ := dirOf_dsE₀_mem hx
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective x θ σ₀
  set k := ‖tpMk x (GammaP.dsE₀ x)‖⁻¹
  have hk : 0 < k := inv_pos.2 (norm_pos_iff.2 (tpMk_dsE₀_ne hx))
  have hv : tpMk x (k • GammaP.dsE₀ x) = ((linkCover x θ t₀ : Link x) : TpHS x) := by
    rw [ht₀, coe_dirOf x (tpMk_dsE₀_ne hx)]; rfl
  have hT : GammaP.tangent A ((σ₀ : Link x) : TpHS x) =
      tpMk x (k • (((A : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (GammaP.dsE₀ x)) := by
    rw [coe_dirOf x (tpMk_dsE₀_ne hx), map_smul]
    simp only [tpMk, GammaP.tangent_mk, Submodule.Quotient.mk_smul]
    rfl
  have hTne : tpMk x (k • (((A : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (GammaP.dsE₀ x)) ≠ 0 := hT ▸ tangent_ne_zero x A σ₀
  set k' := ‖tpMk x (k • (((A : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (GammaP.dsE₀ x))‖⁻¹
  have hk' : 0 < k' := inv_pos.2 (norm_pos_iff.2 hTne)
  have hv' : tpMk x (k' • k • (((A : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      (GammaP.dsE₀ x)) = ((A • linkCover x θ t₀ : Link x) : TpHS x) := by
    rw [ht₀, gammaP_smul_def, coe_linRaySmul, hT]
    simp only [tpMk, Submodule.Quotient.mk_smul]
    rfl
  have hvol : vol3 x (k • GammaP.dsE₀ x) (k' • k • (((A : GammaP x) : Causal.Flat.lorentz 2) :
      𝕄 ≃ₗ[ℝ] 𝕄) (GammaP.dsE₀ x)) = k * (k' * (k * (Real.sinh ζ * V))) := by
    rw [vol3_smul_mid, vol3_smul_right, vol3_smul_right, dsBoost_dsE₀ hx ζ, vol3_add_right,
      vol3_smul_right, vol3_smul_right, vol3_self]
    ring
  obtain ⟨s1, s2⟩ := sign_of_lift hθ hg hfix hv hv'
  rw [hvol] at s1 s2
  have hkk : 0 < k * (k' * k) := mul_pos hk (mul_pos hk' hk)
  have pos_iff : 0 < k * (k' * (k * (Real.sinh ζ * V))) ↔ 0 < ζ * V := by
    rw [show k * (k' * (k * (Real.sinh ζ * V))) = (k * (k' * k)) * (Real.sinh ζ * V) by ring,
      mul_pos_iff_of_pos_left hkk]
    rcases lt_or_gt_of_ne hζ with h | h
    · have := Real.sinh_neg_iff.2 h
      constructor <;> intro hh <;> nlinarith
    · have := Real.sinh_pos_iff.2 h
      constructor <;> intro hh <;> nlinarith
  have neg_iff : k * (k' * (k * (Real.sinh ζ * V))) < 0 ↔ ζ * V < 0 := by
    rw [show k * (k' * (k * (Real.sinh ζ * V))) = (k * (k' * k)) * (Real.sinh ζ * V) by ring]
    have e : (k * (k' * k)) * (Real.sinh ζ * V) < 0 ↔ Real.sinh ζ * V < 0 :=
      ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_neg_of_pos_of_neg hkk h⟩
    rw [e]
    rcases lt_or_gt_of_ne hζ with h | h
    · have := Real.sinh_neg_iff.2 h
      constructor <;> intro hh <;> nlinarith
    · have := Real.sinh_pos_iff.2 h
      constructor <;> intro hh <;> nlinarith
  rw [pos_iff] at s1
  rw [neg_iff] at s2
  have hσt : linkCover x θ t₀ ∈ dsFutureDirs x := ht₀ ▸ hσ₀
  rcases timelike_spacelike_dir hx hA1 hg hfix with ⟨hT, -⟩ | ⟨hT, -⟩
  · have hup := hT t₀ (Or.inl hσt)
    have hp := s1 hup
    refine ⟨⟨fun _ => hp, fun _ t ht => hT t (Or.inl ht)⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact absurd (h t₀ hσt) (not_lt.2 hup.le)
    · exact absurd h (not_lt.2 hp.le)
  · have hdn := hT t₀ (Or.inl hσt)
    have hn := s2 hdn
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun _ => hn, fun _ t ht => hT t (Or.inl ht)⟩⟩
    · exact absurd (h t₀ hσt) (not_lt.2 hdn.le)
    · exact absurd h (not_lt.2 hn.le)

end CutGlue

/-! ## 2c. The gluing rule, the ray, and the push of `γ` -/

namespace CutGlue

variable {x : HS 2} {w : 𝕄}

/-- In the frame: `w = a e₀ + b j`, `v = a' e₀ + b' j`, the two linear forms of the rule. -/
theorem futureSide_iff_of_vol3_neg (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w)
    {v : 𝕄} (hv : Causal.Flat.minkB (x : 𝕄) v = 0) (hvol : vol3 x w v < 0) :
    FutureSide w v ↔ 0 < Causal.Flat.minkB w (jVec x) * vol3 x (GammaP.dsE₀ x) (jVec x) := by
  obtain ⟨h00, h11, h01, -, -, hpos, hj1⟩ := frame hx
  have h10 : Causal.Flat.minkB (jVec x) (GammaP.dsE₀ x) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact h01
  have hV := vol3_frame_ne hx
  set V := vol3 x (GammaP.dsE₀ x) (jVec x)
  have hwne := hw.ne
  have hw0 := hw.null
  obtain ⟨a, b, rfl, hab, ha⟩ := IsNullTangent.decomp hx hw
  obtain ⟨a', b', rfl⟩ := exists_frame_comb hx hv
  rw [futureSide_iff hw0 hwne]
  rw [vol3_comb] at hvol
  have hw1 : (a • GammaP.dsE₀ x + b • jVec x).1 = a * (GammaP.dsE₀ x).1 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hj1, mul_zero, add_zero]
  have hB : Causal.Flat.minkB (a' • GammaP.dsE₀ x + b' • jVec x) (a • GammaP.dsE₀ x + b • jVec x)
      = -(a' * a) + b' * b := by
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_left,
      Causal.Flat.minkB_smul_right, h00, h11, h01, h10]
    ring
  have hb : Causal.Flat.minkB (a • GammaP.dsE₀ x + b • jVec x) (jVec x) = b := by
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01]
    ring
  rw [hw1, hB, hb]
  -- `a (b b' − a a') = b (a b' − b a')`
  have key : a * (GammaP.dsE₀ x).1 * (-(a' * a) + b' * b) =
      (GammaP.dsE₀ x).1 * (b * (a * b' - b * a')) := by
    have : b * (a * b' - b * a') = a * (b * b' - a * a') := by
      have e : b * b = a * a := by nlinarith
      linear_combination (-a') * e
    rw [this]; ring
  rw [key]
  set m := a * b' - b * a'
  constructor
  · intro h
    have hbm : b * m < 0 := by
      by_contra hc; push Not at hc; nlinarith
    rcases lt_or_gt_of_ne hV with hV' | hV'
    · have : 0 < m := by by_contra hc; push Not at hc; nlinarith
      nlinarith
    · have : m < 0 := by by_contra hc; push Not at hc; nlinarith
      nlinarith
  · intro h
    have hbm : b * m < 0 := by
      rcases lt_or_gt_of_ne hV with hV' | hV'
      · have hm : 0 < m := by by_contra hc; push Not at hc; nlinarith
        have : b < 0 := by by_contra hc; push Not at hc; nlinarith
        nlinarith
      · have hm : m < 0 := by by_contra hc; push Not at hc; nlinarith
        have : 0 < b := by by_contra hc; push Not at hc; nlinarith
        nlinarith
    nlinarith

/-- **The gluing rule, by a sign**: the glued copy is crossed first in the positive sense iff
`(⟨w, j⟩ · vol3 x e₀ j > 0) ↔ src`. -/
theorem sourceFirst_iff (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) (src : Bool) :
    SourceFirst x w src ↔
      (0 < Causal.Flat.minkB w (jVec x) * vol3 x (GammaP.dsE₀ x) (jVec x) ↔ src = true) := by
  obtain ⟨-, -, -, -, hx1, -, -⟩ := frame hx
  constructor
  · intro h
    obtain ⟨a, b, hwab, hab, ha⟩ := IsNullTangent.decomp hx hw
    set V := vol3 x (GammaP.dsE₀ x) (jVec x)
    have hV := vol3_frame_ne hx
    set v₀ : 𝕄 := (-(a * V)) • jVec x
    have hv₀ : Causal.Flat.minkB (x : 𝕄) v₀ = 0 := by
      simp only [v₀, Causal.Flat.minkB_smul_right, hx1, mul_zero]
    have hvol : vol3 x w v₀ < 0 := by
      have : v₀ = (0 : ℝ) • GammaP.dsE₀ x + (-(a * V)) • jVec x := by simp [v₀]
      rw [this, hwab, vol3_comb]
      have : 0 < (a * V) ^ 2 := by positivity
      nlinarith
    rw [← futureSide_iff_of_vol3_neg hx hw hv₀ hvol]
    exact h v₀ hv₀ hvol
  · intro h v hv hvol
    rw [futureSide_iff_of_vol3_neg hx hw hv hvol]
    exact h

theorem dsBoost_neg (hx : x ∈ HS.piece 2 .deSitter) (ζ : ℝ) :
    GammaP.dsBoost hx (-ζ) = (GammaP.dsBoost hx ζ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← GammaP.dsBoost_add, neg_add_cancel, GammaP.dsBoost_zero]

/-- **The holonomy of the surgery** for `γ` the boost of rapidity `ζ`. -/
theorem cutGlueHol_dsBoost (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) (ζ : ℝ)
    (src : Bool) :
    cutGlueHol x w (GammaP.dsBoost hx ζ) src = GammaP.dsBoost hx
      (if (0 < Causal.Flat.minkB w (jVec x) * vol3 x (GammaP.dsE₀ x) (jVec x) ↔ src = true)
        then -ζ else ζ) := by
  unfold cutGlueHol
  by_cases h : 0 < Causal.Flat.minkB w (jVec x) * vol3 x (GammaP.dsE₀ x) (jVec x) ↔ src = true
  · rw [if_pos ((sourceFirst_iff hx hw src).2 h), if_pos h, dsBoost_neg]
  · rw [if_neg (fun h' => h ((sourceFirst_iff hx hw src).1 h')), if_neg h]

/-- `hyp` on a positive multiple. -/
theorem hyp_of_coe {σ : HS 2} {u : 𝕄} {k : ℝ} (hk : 0 < k) (hσ : (σ : 𝕄) = k • u)
    (hu : 0 < Causal.Flat.minkQ u) : hyp σ = (Real.sqrt (Causal.Flat.minkQ u))⁻¹ • u := by
  rw [hyp, hσ, Causal.Flat.minkQ_smul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le, smul_smul]
  congr 1
  have : 0 < Real.sqrt (Causal.Flat.minkQ u) := Real.sqrt_pos.2 hu
  field_simp

theorem minkQ_add_ray (hw : IsNullTangent x w) (c : ℝ) :
    Causal.Flat.minkQ ((x : 𝕄) + c • w) = Causal.Flat.minkQ (x : 𝕄) := by
  rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_right, hw.perp, hw.null]
  ring

theorem ray_ne_zero (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) (c : ℝ) :
    (x : 𝕄) + c • w ≠ 0 := fun h => by
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  have := minkQ_add_ray hw c
  rw [h, Causal.Flat.minkQ_zero] at this
  linarith

theorem coe_rayPt (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) (s : ℝ) :
    ((rayPt x w s : HS 2) : 𝕄) = ‖(x : 𝕄) + s • w‖⁻¹ • ((x : 𝕄) + s • w) :=
  coe_rayNormalize _ (ray_ne_zero hx hw s)

theorem rayPt_mem (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) (s : ℝ) :
    rayPt x w s ∈ HS.piece 2 .deSitter := by
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  show 0 < Causal.Flat.minkQ ((rayPt x w s : HS 2) : 𝕄)
  rw [coe_rayPt hx hw s, Causal.Flat.minkQ_smul, minkQ_add_ray hw]
  have : 0 < ‖(x : 𝕄) + s • w‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (ray_ne_zero hx hw s))
  positivity

/-- **The boost moves the ray along itself**: `γ (x + s w) = x + s λ w`,
`λ = ch ζ + (b/a) sh ζ` (`w = a e₀ + b j`). -/
theorem dsBoost_ray (hx : x ∈ HS.piece 2 .deSitter) {a b : ℝ} (hab : b ^ 2 = a ^ 2) (ha : a ≠ 0)
    (ζ s : ℝ) :
    (((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
        ((x : 𝕄) + s • (a • GammaP.dsE₀ x + b • jVec x)) =
      (x : 𝕄) + (s * (Real.cosh ζ + b / a * Real.sinh ζ)) •
        (a • GammaP.dsE₀ x + b • jVec x) := by
  rw [map_add, map_smul, (GammaP.dsBoost hx ζ).2, dsBoost_comb]
  congr 1
  have e1 : a * Real.cosh ζ + b * Real.sinh ζ = (Real.cosh ζ + b / a * Real.sinh ζ) * a := by
    field_simp
  have e2 : a * Real.sinh ζ + b * Real.cosh ζ = (Real.cosh ζ + b / a * Real.sinh ζ) * b := by
    rw [show (Real.cosh ζ + b / a * Real.sinh ζ) * b = b * Real.cosh ζ + (b * b / a) * Real.sinh ζ
      by ring, show b * b / a = a by rw [div_eq_iff ha]; nlinarith]
    ring
  rw [e1, e2, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

/-- The sign of the push. -/
theorem push_sign {a b ζ : ℝ} (hab : b ^ 2 = a ^ 2) (ha : a ≠ 0) (hζ : ζ ≠ 0) :
    (0 ≤ (1 - (Real.cosh ζ + b / a * Real.sinh ζ)) * a ↔ b * ζ < 0) ∧
      (0 ≤ ((Real.cosh ζ + b / a * Real.sinh ζ) - 1) * a ↔ 0 < b * ζ) := by
  have hb : b = a ∨ b = -a := by
    have : (b - a) * (b + a) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hb with rfl | rfl
  · rw [div_self ha, one_mul, Real.cosh_add_sinh]
    have hsgn : (Real.exp ζ < 1 ∧ ζ < 0) ∨ (1 < Real.exp ζ ∧ 0 < ζ) := by
      rcases lt_or_gt_of_ne hζ with hz | hz
      · exact Or.inl ⟨Real.exp_lt_one_iff.2 hz, hz⟩
      · exact Or.inr ⟨Real.one_lt_exp_iff.2 hz, hz⟩
    rcases hsgn with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rcases lt_or_gt_of_ne ha with ha' | ha' <;>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;> nlinarith
  · rw [neg_div, div_self ha, neg_one_mul, ← sub_eq_add_neg, Real.cosh_sub_sinh]
    have hsgn : (Real.exp (-ζ) < 1 ∧ 0 < ζ) ∨ (1 < Real.exp (-ζ) ∧ ζ < 0) := by
      rcases lt_or_gt_of_ne hζ with hz | hz
      · exact Or.inr ⟨Real.one_lt_exp_iff.2 (by linarith), hz⟩
      · exact Or.inl ⟨Real.exp_lt_one_iff.2 (by linarith), hz⟩
    rcases hsgn with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rcases lt_or_gt_of_ne ha with ha' | ha' <;>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩ <;> nlinarith

/-- **`γ y` in the past of `y`, on the ray, by a sign**: for the boost of rapidity `ζ ≠ 0` and
`s > 0`, `γ [x + s w]` lies in the causal past of `[x + s w]` iff `⟨w, j⟩ ζ < 0`, in its causal
future iff `⟨w, j⟩ ζ > 0`. -/
theorem push_iff (hx : x ∈ HS.piece 2 .deSitter) (hw : IsNullTangent x w) {ζ : ℝ} (hζ : ζ ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    (IsCausalPast (((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2) • rayPt x w s)
        (rayPt x w s) ↔ Causal.Flat.minkB w (jVec x) * ζ < 0) ∧
      (IsCausalFuture (((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2) • rayPt x w s)
        (rayPt x w s) ↔ 0 < Causal.Flat.minkB w (jVec x) * ζ) := by
  obtain ⟨-, h11, h01, -, -, hpos, hj1⟩ := frame hx
  have hQ : 0 < Causal.Flat.minkQ (x : 𝕄) := hx
  obtain ⟨a, b, hwab, hab, ha⟩ := IsNullTangent.decomp hx hw
  have hb : Causal.Flat.minkB w (jVec x) = b := by
    rw [hwab]
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01]
    ring
  rw [hb]
  set A := ((GammaP.dsBoost hx ζ : GammaP x) : Causal.Flat.lorentz 2)
  set lam := Real.cosh ζ + b / a * Real.sinh ζ
  have hy := coe_rayPt hx hw s
  have hk : 0 < ‖(x : 𝕄) + s • w‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (ray_ne_zero hx hw s))
  have hyhyp : hyp (rayPt x w s) =
      (Real.sqrt (Causal.Flat.minkQ (x : 𝕄)))⁻¹ • ((x : 𝕄) + s • w) := by
    rw [hyp_of_coe hk hy (by rw [minkQ_add_ray hw]; exact hQ), minkQ_add_ray hw]
  have hAy : ((A • rayPt x w s : HS 2) : 𝕄) =
      (‖(A : 𝕄 ≃ₗ[ℝ] 𝕄) (rayPt x w s)‖⁻¹ * ‖(x : 𝕄) + s • w‖⁻¹) •
        ((x : 𝕄) + (s * lam) • w) := by
    rw [coe_hs_smul, hy, map_smul, smul_smul]
    congr 1
    rw [hwab]
    exact dsBoost_ray hx hab ha ζ s
  have hk2 : 0 < ‖(A : 𝕄 ≃ₗ[ℝ] 𝕄) (rayPt x w s)‖⁻¹ * ‖(x : 𝕄) + s • w‖⁻¹ :=
    mul_pos (inv_pos.2 (norm_pos_iff.2 ((LinearEquiv.map_ne_zero_iff _).2
      (raySphere_ne_zero _)))) hk
  have hAyhyp : hyp (A • rayPt x w s) =
      (Real.sqrt (Causal.Flat.minkQ (x : 𝕄)))⁻¹ • ((x : 𝕄) + (s * lam) • w) := by
    rw [hyp_of_coe hk2 hAy (by rw [minkQ_add_ray hw]; exact hQ), minkQ_add_ray hw]
  have hmem := rayPt_mem hx hw s
  have hAmem : A • rayPt x w s ∈ HS.piece 2 .deSitter := (HS.smul_mem_piece_iff A).2 hmem
  have hsq : 0 < (Real.sqrt (Causal.Flat.minkQ (x : 𝕄)))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hQ)
  have hw1 : w.1 = a * (GammaP.dsE₀ x).1 := by
    rw [hwab]; simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hj1, mul_zero, add_zero]
  have hfc : ∀ c : ℝ, Causal.Flat.IsFutureCausal (c • w) ↔ 0 ≤ c * a := by
    intro c
    unfold Causal.Flat.IsFutureCausal
    rw [Causal.Flat.minkQ_smul, hw.null, mul_zero]
    simp only [Prod.smul_fst, smul_eq_mul, hw1, le_refl, and_true]
    constructor
    · intro h; by_contra hc; push Not at hc; nlinarith
    · intro h; nlinarith
  obtain ⟨p1, p2⟩ := push_sign hab ha hζ
  have hc := mul_pos hsq hs
  refine ⟨?_, ?_⟩
  · unfold IsCausalPast
    rw [hyhyp, hAyhyp, ← smul_sub, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, hfc, ← p1]
    constructor
    · rintro ⟨-, -, h⟩
      by_contra hn; push Not at hn; nlinarith
    · intro h
      exact ⟨hAmem, hmem, by nlinarith⟩
  · unfold IsCausalFuture IsCausalPast
    rw [hyhyp, hAyhyp, ← smul_sub, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, hfc, ← p2]
    constructor
    · rintro ⟨-, -, h⟩
      by_contra hn; push Not at hn; nlinarith
    · intro h
      exact ⟨hmem, hAmem, by nlinarith⟩

end CutGlue

/-! ## 3. `bbsrem:cuttachyon2` -/

variable {C : GammaLinkCircle L} {w : 𝕄} {γ : GammaP C.pt} {src : Bool}

/-- The sign of the rule (algebra). -/
theorem CutGlue.sign_rule {b V ζ : ℝ} (hb : b ≠ 0) (hV : V ≠ 0) (src : Bool) :
    0 < (if (0 < b * V ↔ src = true) then -ζ else ζ) * V ↔
      (if src = true then b * ζ < 0 else 0 < b * ζ) := by
  have hbV : b * V ≠ 0 := mul_ne_zero hb hV
  cases src <;> by_cases h : 0 < b * V <;> simp only [h, if_true, if_false, iff_true, iff_false,
    Bool.false_eq_true, not_true_eq_false] <;>
  · rcases lt_or_gt_of_ne hb with hb' | hb' <;> rcases lt_or_gt_of_ne hV with hV' | hV' <;>
      constructor <;> intro h' <;> nlinarith

/-- **The core of `bbsrem:cuttachyon2`**: for the surgery link of `γ`, the boost of rapidity
`ζ ≠ 0`, positivity (in both forms) is the sign of `ζ' · vol3 x e₀ j`, `ζ' = ∓ζ` by the rule;
the link is not regular and has a space-like type of degree `2`. -/
theorem GammaLinkCircle.IsCutGlueLink.core (h : C.IsCutGlueLink w γ src)
    (hx : C.pt ∈ HS.piece 2 .deSitter) (hw : IsNullTangent C.pt w) (hγ : γ ≠ 1) :
    ∃ ζ : ℝ, γ = GammaP.dsBoost hx ζ ∧ ζ ≠ 0 ∧
      (C.IsPositive ↔ 0 < (if (0 < Causal.Flat.minkB w (jVec C.pt) *
          vol3 C.pt (GammaP.dsE₀ C.pt) (jVec C.pt) ↔ src = true) then -ζ else ζ) *
          vol3 C.pt (GammaP.dsE₀ C.pt) (jVec C.pt)) ∧
      (C.IsSpacelikePositiveRep ↔ 0 < (if (0 < Causal.Flat.minkB w (jVec C.pt) *
          vol3 C.pt (GammaP.dsE₀ C.pt) (jVec C.pt) ↔ src = true) then -ζ else ζ) *
          vol3 C.pt (GammaP.dsE₀ C.pt) (jVec C.pt)) ∧
      ¬ C.IsRegular ∧ (C.HasType (.spacelike true 2) ∨ C.HasType (.spacelike false 2)) := by
  obtain ⟨θ, hθ, E, D, g, hl, hg, hfix⟩ := h
  obtain ⟨ζ, rfl⟩ := GammaP.exists_eq_dsBoost hx γ
  have hζ : ζ ≠ 0 := fun h0 => hγ (by rw [h0, GammaP.dsBoost_zero])
  rw [CutGlue.cutGlueHol_dsBoost hx hw ζ src] at hg
  set V := vol3 C.pt (GammaP.dsE₀ C.pt) (jVec C.pt)
  set ζ' := if (0 < Causal.Flat.minkB w (jVec C.pt) * V ↔ src = true) then -ζ else ζ
  have hζ' : ζ' ≠ 0 := by
    simp only [ζ']; split_ifs
    · exact neg_ne_zero.2 hζ
    · exact hζ
  have hV := CutGlue.vol3_frame_ne hx
  have hζV : ζ' * V ≠ 0 := mul_ne_zero hζ' hV
  obtain ⟨up, dn⟩ := CutGlue.future_up_iff hx hθ hζ' hg hfix
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective C.pt θ (dirOf C.pt (GammaP.dsE₀ C.pt))
  have hσt : linkCover C.pt θ t₀ ∈ dsFutureDirs C.pt := ht₀ ▸ CutGlue.dirOf_dsE₀_mem hx
  have hg1 : g ≠ 1 := by
    rintro rfl
    rcases lt_or_gt_of_ne hζV with hn | hp
    · exact (lt_irrefl t₀) (dn.2 hn t₀ hσt)
    · exact (lt_irrefl t₀) (up.2 hp t₀ hσt)
  have hh : GTilde.IsHyperbolic g := (isHyperbolic_iff_ne_one_of_lift hx hg hfix).2 hg1
  have hD : range D = univ := hl.range_eq_univ (k := 2) (by norm_num) hfix rfl
  have hiP : ∀ s, E s ∈ C.iPlusL ↔ linkCover C.pt θ (D s) ∈ dsFutureDirs C.pt := fun s => by
    rw [hl.mem_iPlusL_iff s, iPlus_of_deSitter hx]
  have key : (∀ s, E s ∈ C.iPlusL → D s ≤ g (D s)) ↔ 0 < ζ' * V := by
    constructor
    · intro hle
      by_contra hn
      have hn' : ζ' * V < 0 := lt_of_le_of_ne (not_lt.1 hn) hζV
      obtain ⟨s₀, hs₀⟩ : t₀ ∈ range D := hD ▸ mem_univ t₀
      have h1 := hle s₀ ((hiP s₀).2 (hs₀ ▸ hσt))
      have h2 := dn.2 hn' (D s₀) (hs₀ ▸ hσt)
      linarith
    · intro hp s hs
      exact (up.2 hp (D s) ((hiP s).1 hs)).le
  have hpos : C.IsSpacelikePositive ↔ 0 < ζ' * V := by
    rw [← key]
    exact ⟨fun hC => hC.forall hθ hl hfix rfl,
      fun hk => ⟨hx, θ, hθ, E, D, _, 2, g, hl, by norm_num, hfix, hh, rfl, hk⟩⟩
  have hP : C.IsPositive ↔ C.IsSpacelikePositive :=
    GammaLinkCircle.isPositive_iff_of_deSitter hx hθ hl (by norm_num) hfix hh rfl
  refine ⟨ζ, rfl, hζ, hP.trans hpos, GammaLinkCircle.isSpacelikePositive_iff_rep.symm.trans hpos,
    ?_⟩
  rcases lt_or_gt_of_ne hζV with hn | hp
  · have hneg : C.IsSpacelikeNegative := ⟨hx, θ, hθ, E, D, _, 2, g, hl, by norm_num, hfix, hh, rfl,
      fun s hs => (dn.2 hn (D s) ((hiP s).1 hs)).le⟩
    refine ⟨fun hreg => hneg.not_isPositive hreg.isPositive, Or.inr ⟨θ, hθ, E, D, _, hl,
      HS.region_eq_of_mem hx, by norm_num, g, hfix, hh, rfl, fun s hs => ?_⟩⟩
    rw [iPlus_of_deSitter hx] at hs
    exact (dn.2 hn (D s) hs).le
  · have hC : C.IsSpacelikePositive := hpos.2 hp
    refine ⟨hC.not_isRegular, Or.inl ⟨θ, hθ, E, D, _, hl,
      HS.region_eq_of_mem hx, by norm_num, g, hfix, hh, rfl, fun s hs => ?_⟩⟩
    rw [iPlus_of_deSitter hx] at hs
    exact (up.2 hp (D s) hs).le

/-- **« The resulting HS-singularity is space-like, of degree 2 »**: not regular, of type
space-like of degree `2` (positive or negative). -/
theorem GammaLinkCircle.IsCutGlueLink.hasType (h : C.IsCutGlueLink w γ src)
    (hx : C.pt ∈ HS.piece 2 .deSitter) (hw : IsNullTangent C.pt w) (hγ : γ ≠ 1) :
    ¬ C.IsRegular ∧ (C.HasType (.spacelike true 2) ∨ C.HasType (.spacelike false 2)) := by
  obtain ⟨-, -, -, -, -, h⟩ := h.core hx hw hγ
  exact h

/-- **Positivity under the rule l.1303–1304** (the future copy of `r` glued into the past copy),
in the library's holonomy convention (`D (s + 1) = f (D s)`): the
singularity is positive iff `γ y` lies in the causal past of `y` for every `y ∈ r`, whatever the
orientation of `r`; in the l.915 form and in the l.908–913 form. -/
theorem GammaLinkCircle.IsCutGlueLink.isPositive_iff_past (h : C.IsCutGlueLink w γ true)
    (hx : C.pt ∈ HS.piece 2 .deSitter) (hw : IsNullTangent C.pt w) (hγ : γ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) :
    (C.IsPositive ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalPast ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s)) ∧
      (C.IsSpacelikePositiveRep ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalPast ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s)) := by
  obtain ⟨ζ, rfl, hζ, hP, hR, -⟩ := h.core hx hw hγ
  obtain ⟨a, b, hwab, hab, ha⟩ := CutGlue.IsNullTangent.decomp hx hw
  have hb : Causal.Flat.minkB w (jVec C.pt) ≠ 0 := by
    obtain ⟨-, h11, h01, -, -, -, -⟩ := CutGlue.frame hx
    rw [hwab]
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01, mul_zero,
      zero_add, mul_one]
    intro hb0; rw [hb0] at hab; exact ha (pow_eq_zero_iff two_ne_zero |>.1 (by rw [← hab]; ring))
  have hpush : (∀ s ∈ Ioo 0 ε, CutGlue.IsCausalPast
      (((GammaP.dsBoost hx ζ : GammaP C.pt) : Causal.Flat.lorentz 2) • rayPt C.pt w s)
        (rayPt C.pt w s)) ↔ Causal.Flat.minkB w (jVec C.pt) * ζ < 0 :=
    ⟨fun H => (CutGlue.push_iff hx hw hζ (half_pos hε)).1.1 (H _ ⟨half_pos hε, half_lt_self hε⟩),
      fun H s hs => (CutGlue.push_iff hx hw hζ hs.1).1.2 H⟩
  have hrule := CutGlue.sign_rule (ζ := ζ) hb (CutGlue.vol3_frame_ne hx) true
  rw [if_pos rfl] at hrule
  exact ⟨hP.trans (hrule.trans hpush.symm), hR.trans (hrule.trans hpush.symm)⟩

/-- **Positivity under the other rule** (the past copy glued into the future copy): positive iff
`γ y` lies in the causal future of `y` for every `y ∈ r`, whatever the orientation of `r`. -/
theorem GammaLinkCircle.IsCutGlueLink.isPositive_iff_future (h : C.IsCutGlueLink w γ false)
    (hx : C.pt ∈ HS.piece 2 .deSitter) (hw : IsNullTangent C.pt w) (hγ : γ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) :
    (C.IsPositive ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalFuture ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s)) ∧
      (C.IsSpacelikePositiveRep ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalFuture ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s)
          (rayPt C.pt w s)) := by
  obtain ⟨ζ, rfl, hζ, hP, hR, -⟩ := h.core hx hw hγ
  obtain ⟨a, b, hwab, hab, ha⟩ := CutGlue.IsNullTangent.decomp hx hw
  have hb : Causal.Flat.minkB w (jVec C.pt) ≠ 0 := by
    obtain ⟨-, h11, h01, -, -, -, -⟩ := CutGlue.frame hx
    rw [hwab]
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01, mul_zero,
      zero_add, mul_one]
    intro hb0; rw [hb0] at hab; exact ha (pow_eq_zero_iff two_ne_zero |>.1 (by rw [← hab]; ring))
  have hpush : (∀ s ∈ Ioo 0 ε, CutGlue.IsCausalFuture
      (((GammaP.dsBoost hx ζ : GammaP C.pt) : Causal.Flat.lorentz 2) • rayPt C.pt w s)
        (rayPt C.pt w s)) ↔ 0 < Causal.Flat.minkB w (jVec C.pt) * ζ :=
    ⟨fun H => (CutGlue.push_iff hx hw hζ (half_pos hε)).2.1 (H _ ⟨half_pos hε, half_lt_self hε⟩),
      fun H s hs => (CutGlue.push_iff hx hw hζ hs.1).2.2 H⟩
  have hrule := CutGlue.sign_rule (ζ := ζ) hb (CutGlue.vol3_frame_ne hx) false
  rw [if_neg (by decide : ¬ (false = true))] at hrule
  exact ⟨hP.trans (hrule.trans hpush.symm), hR.trans (hrule.trans hpush.symm)⟩

/-- **`bbsrem:cuttachyon2` as printed, in the reading that makes both clauses true**: the copy of
`r` glued by `γ` is the one on the past side of the line of `r` when `r` is future oriented and the
one on its future side when `r` is past oriented (`src = !(w future)`). Then the singularity is
space-like of degree `2`, and positive iff `γ y` lies in the future of `y` for every `y ∈ r` (`r`
future oriented), iff in the past of `y` (`r` past oriented). -/
theorem GammaLinkCircle.IsCutGlueLink.bbsrem_cuttachyon2_reading
    (hx : C.pt ∈ HS.piece 2 .deSitter) (hw : IsNullTangent C.pt w) (hγ : γ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) :
    (Causal.Flat.IsFutureCausal w → C.IsCutGlueLink w γ false →
      (¬ C.IsRegular ∧ (C.HasType (.spacelike true 2) ∨ C.HasType (.spacelike false 2))) ∧
      (C.IsPositive ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalFuture ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s)) ∧
      (C.IsSpacelikePositiveRep ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalFuture ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s))) ∧
    (Causal.Flat.IsFutureCausal (-w) → C.IsCutGlueLink w γ true →
      (¬ C.IsRegular ∧ (C.HasType (.spacelike true 2) ∨ C.HasType (.spacelike false 2))) ∧
      (C.IsPositive ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalPast ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s)) ∧
      (C.IsSpacelikePositiveRep ↔ ∀ s ∈ Ioo 0 ε,
        CutGlue.IsCausalPast ((γ : Causal.Flat.lorentz 2) • rayPt C.pt w s) (rayPt C.pt w s))) :=
  ⟨fun _ h => ⟨h.hasType hx hw hγ, h.isPositive_iff_future hx hw hγ hε⟩,
    fun _ h => ⟨h.hasType hx hw hγ, h.isPositive_iff_past hx hw hγ hε⟩⟩

/-- **Relative to the library's holonomy convention** (`IsLiftedDev`: `D (s + 1) = f (D s)`, the
developing holonomy being the gluing map⁻¹) and to the rule l.1303–1304 read literally
(`src = true`), the future-oriented clause does not hold: at every `x ∈ dS²` and every
future-oriented light-like `w`, some `γ ∈ Γ_x ∖ {1}` sends every point of the ray into its own
future while the surgery link is not positive, in either form. In the convention of the paper's
worked examples (holonomy = gluing map) the signs flip and it is the past-oriented clause that
fails (SCOPE (c)). -/
theorem not_cuttachyon2_future_printed {x : HS 2} (hx : x ∈ HS.piece 2 .deSitter) {w : 𝕄}
    (hw : IsNullTangent x w) (_hwf : Causal.Flat.IsFutureCausal w) :
    ∃ γ : GammaP x, γ ≠ 1 ∧ (∀ s, 0 < s →
        CutGlue.IsCausalFuture ((γ : Causal.Flat.lorentz 2) • rayPt x w s) (rayPt x w s)) ∧
      ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link x) L)
        (hcs : HasGroupoid L (gxGroupoid (GammaP x) (Link x))) (hL : IsCircle L),
        (GammaLinkCircle.mk x cs hcs hL).IsCutGlueLink w γ true ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsPositive ∧
        ¬ (GammaLinkCircle.mk x cs hcs hL).IsSpacelikePositiveRep := by
  obtain ⟨a, b, hwab, hab, ha⟩ := CutGlue.IsNullTangent.decomp hx hw
  have hb : Causal.Flat.minkB w (jVec x) ≠ 0 := by
    obtain ⟨-, h11, h01, -, -, -, -⟩ := CutGlue.frame hx
    rw [hwab]
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h11, h01, mul_zero,
      zero_add, mul_one]
    intro hb0; rw [hb0] at hab; exact ha (pow_eq_zero_iff two_ne_zero |>.1 (by rw [← hab]; ring))
  set b' := Causal.Flat.minkB w (jVec x)
  have hγ : GammaP.dsBoost hx b' ≠ 1 := CutGlue.dsBoost_ne_one hx hb
  have hbb : 0 < b' * b' := mul_self_pos.2 hb
  refine ⟨GammaP.dsBoost hx b', hγ, fun s hs => (CutGlue.push_iff hx hw hb hs).2.2 hbb, ?_⟩
  obtain ⟨L, _, cs, hcs, hL, hC⟩ := exists_isCutGlueLink hx w (GammaP.dsBoost hx b') true
  obtain ⟨hP, hR⟩ := hC.isPositive_iff_past hx hw hγ one_pos
  have hnot : ¬ ∀ s ∈ Ioo (0 : ℝ) 1, CutGlue.IsCausalPast
      (((GammaP.dsBoost hx b' : GammaP x) : Causal.Flat.lorentz 2) • rayPt x w s) (rayPt x w s) :=
    fun H => (lt_asymm hbb) ((CutGlue.push_iff hx hw hb (by norm_num : (0 : ℝ) < 1 / 2)).1.1
      (H _ ⟨by norm_num, by norm_num⟩))
  exact ⟨L, inferInstance, cs, hcs, hL, hC, fun h => hnot (hP.1 h), fun h => hnot (hR.1 h)⟩

/-! ## 4. `bbsrem:however_no_positive_negative` -/

variable {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}

/-- Every oriented lifted holonomy of a circle with one fixed-point lifted holonomy has a fixed
point (they are conjugate, `GX.GammaLinkCircle.IsLiftedDev.relate`). -/
theorem GammaLinkCircle.IsLiftedDev.fixed_of_fixed (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hfix : ∃ x, f x = x) {θ' : TpHS C.pt ≃ₗ[ℝ] ℂ}
    (hθ' : IsOrientedTangent C.pt θ') {E' : ℝ → L} {D' : ℝ → ℝ} {f' : GTilde}
    (h' : C.IsLiftedDev θ' E' D' f') : ∃ x, f' x = x := by
  obtain ⟨-, κ, -, -, hf⟩ := h.relate hθ hθ' h'
  rw [hf]
  exact GTilde.fixed_conj hfix κ

/-- **A degree-`0` circle at a non-time-like `p` is positive** (`GX.GammaLinkCircle.IsPositive`:
its clauses concern time-like points and degrees `≥ 2`): some oriented lifted pair has a lifted
holonomy with a fixed point. -/
theorem GammaLinkCircle.isPositive_of_fixed (hp : 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄))
    (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) (hfix : ∃ x, f x = x) :
    C.IsPositive := by
  refine ⟨fun hq => absurd hq (not_lt.2 hp), fun _ θ' hθ' E' D' f' h' k g hg hfg hk => ?_,
    fun _ θ' hθ' E' D' f' h' k g hg hfg hk => ?_⟩
  · exact (GTilde.degree_clash (h.fixed_of_fixed hθ hfix hθ' h') (by omega) hfg hg).elim
  · exact (GTilde.degree_clash (h.fixed_of_fixed hθ hfix hθ' h') (by omega) hfg hg).elim

/-- **None of the four signed notions of l.906–922 applies in degree `0`.** -/
theorem GammaLinkCircle.not_signed_of_fixed (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hfix : ∃ x, f x = x) :
    ¬ C.IsSpacelikePositive ∧ ¬ C.IsSpacelikeNegative ∧ ¬ C.IsLightlikePositive ∧
      ¬ C.IsLightlikeNegative := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rintro ⟨-, θ₁, hθ₁, E₁, D₁, f₁, k, g, h₁, hk, hg, -, hfg, -⟩
    exact GTilde.degree_clash (h.fixed_of_fixed hθ hfix hθ₁ h₁) hk hfg hg

/-- The BTZ-like types, extreme or not (l.873–876, l.886–891). -/
def LinkType.IsBTZLike : LinkType → Prop
  | .btzPast => True
  | .btzFuture => True
  | .extremeBTZ _ => True
  | _ => False

/-- A BTZ-like type is read on a pair with a fixed-point lifted holonomy at a non-time-like `p`. -/
theorem LinkType.IsBTZLike.pairType {t : LinkType} (ht : t.IsBTZLike) {p : HS 2}
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {D : ℝ → ℝ} {f : GTilde} (hP : PairType p θ D f t) :
    0 ≤ Causal.Flat.minkQ (p : 𝕄) ∧ ∃ x, f x = x := by
  have hreg : ∀ k : HSPiece, HS.region p = k → k = .deSitter ∨ k = .bdPlus ∨ k = .bdMinus →
      0 ≤ Causal.Flat.minkQ (p : 𝕄) := by
    intro k hk hk'
    have hm := HS.mem_piece_iff_region.2 hk
    rcases hk' with rfl | rfl | rfl
    · exact (show (0 : ℝ) < Causal.Flat.minkQ (p : 𝕄) from hm).le
    · exact (show Causal.Flat.minkQ (p : 𝕄) = 0 ∧ _ from hm).1.ge
    · exact (show Causal.Flat.minkQ (p : 𝕄) = 0 ∧ _ from hm).1.ge
  rcases t with _ | _ | _ | _ | _ | b | _ | _ | _
  all_goals first
    | exact absurd ht id
    | skip
  · exact ⟨hreg _ hP.1 (Or.inl rfl), hP.2.2.1⟩
  · exact ⟨hreg _ hP.1 (Or.inl rfl), hP.2.2.1⟩
  · cases b
    · exact ⟨hreg _ hP.1 (Or.inr (Or.inr rfl)), hP.2.2.1⟩
    · exact ⟨hreg _ hP.1 (Or.inr (Or.inl rfl)), hP.2.2.1⟩

/-- **`bbsrem:however_no_positive_negative`** (l.1481), in the reading of SCOPE (d): a BTZ-like
circle, extreme or not, is positive, none of the four signed notions applies to it, and for every
oriented lifted pair the lifted holonomy has a fixed point (degree `0`) and the inequality of
l.915 read at degree `0` holds everywhere; its reverse holds on `I⁺` only when `I⁺` is empty. So no
sign splits a BTZ-like type. -/
theorem GammaLinkCircle.bbsrem_however_no_positive_negative {t : LinkType} (ht : t.IsBTZLike)
    (hC : C.HasType t) :
    C.IsPositive ∧ ¬ C.IsSpacelikePositive ∧ ¬ C.IsSpacelikeNegative ∧
      ¬ C.IsLightlikePositive ∧ ¬ C.IsLightlikeNegative ∧
      ∀ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ → ∀ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde),
        C.IsLiftedDev θ E D f → (∃ x, f x = x) ∧ (∀ s, D s < f (D s)) ∧
          ((∀ s, E s ∈ C.iPlusL → f (D s) ≤ D s) ↔ ∀ s, E s ∉ C.iPlusL) := by
  obtain ⟨θ₀, hθ₀, E₀, D₀, f₀, h₀, hP⟩ := hC
  obtain ⟨hp, hfix⟩ := ht.pairType hP
  obtain ⟨n1, n2, n3, n4⟩ := GammaLinkCircle.not_signed_of_fixed hθ₀ h₀ hfix
  refine ⟨GammaLinkCircle.isPositive_of_fixed hp hθ₀ h₀ hfix, n1, n2, n3, n4,
    fun θ hθ E D f h => ⟨h₀.fixed_of_fixed hθ₀ hfix hθ h, h.lt_apply, ?_⟩⟩
  exact ⟨fun hle s hs => (h.lt_apply s).not_ge (hle s hs), fun hno s hs => absurd hs (hno s)⟩

end GX
