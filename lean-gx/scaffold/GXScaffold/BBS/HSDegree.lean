import GX.BBS.HSSingularities
import GX.BBS.HSSuspension
import GX.Branched.Universality
import GX.Spherical.TroyanovTriangle

/-!
# BBS § 3.5: a space-like or light-like singularity of degree `2k` is the `k`-fold branched cover of one of degree `2` (the link and HS halves)

Target `T-bbs-degk` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx, DEC-192).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`. Imports `GX.BBS.HSSingularities`
(sorry-free: lifted developing pairs, positive/negative), `GX.BBS.HSSuspension` (`𝔢(L)`),
`GX.Branched.Universality` (gx's branched coverings) and `GX.Spherical.TroyanovTriangle` (portly
complements in `𝕊²`).

* `bbsrem:degk` — `colI_v1.tex:1332` — partial (unmarked: the AdS sentence l.1335–1336 waits on
  `T-bbs-q8`; « `k`-branched cover » and « constructed as » are readings, SCOPE (a)–(c)): the
  assembly `GX.bbsrem_degk_link_hs`, from `GX.GammaLinkCircle.IsLiftedDev.exists_degree_two_cover`
  (every degree `2k` is a `k`-fold cover of a degree `2`), `…exists_kfold_cover_of_degree_two`
  (the `k`-fold cover of a degree `2` has degree `2k`), `…kfold_sign` and `GX.isHyperbolic_pow_iff`
  (type and sign kept), `GX.susp_kfold_branched_cover` (`𝔢` of the cover is a `k`-branched cover
  of `𝔢(L₁)`, branched exactly at the two apices for `k ≥ 2`), and the existence of both signs in
  every degree `GX.exists_spacelike_degree_two_mul`.
* `bbsrem:case_tachyons_see_remark` — `colI_v1.tex:1466` — partial (unmarked: its only sentence is
  the AdS wedge, `T-bbs-q8`; the link and HS content is read as for `bbsrem:degk`): the same
  theorems at a light-like `p` (`0 ≤ Q(p)` covers both), and
  `GX.exists_lightlike_degree_two_mul` (positive and negative light-like singularities of every
  degree `2k`).

> space-like singularity of any (even) degree $2k$ can be constructed as $k$-branched cover of a
> space-like singularity of degree $2$. In other words, they are obtained by identifying $P_1$ and
> $P_2$, but now seen as the boundaries of a wedge turning $k$ times around $c$. (l.1334–1336)
>
> As in the case of tachyons (see Remark~\ref{rk:degk}) one can construct light-like singularities
> of any degree $2k$ by considering a wedge turning $k$ times around $c$ before glueing its
> boundaries. (l.1467–1469)

## Main declarations (all proved)

* **`Γ_p` is the image of `ℝ` at a non-time-like `p`** (injectivity not stated). At `p ∈ dS²` every element of `Γ_p` is a boost of `p^⊥`
  (`GX.GammaP.exists_eq_dsBoost`, `GX.GammaP.dsBoost_add`), at a light-like `p` a null rotation
  (`GX.GammaP.exists_eq_nullBoost`); hence **`k`-th roots** (`GX.GammaP.exists_pow_eq`) and the
  `k`-th root of a lift with a fixed point (`GX.exists_root_lift`: `g₁ᵏ = g`).
* **The `k`-fold cover** (`GX.GammaLinkCircle.IsLiftedDev.exists_kfold_cover`): `f = f₁ᵏ` with
  `f₁` fixed-point-free gives a `k`-sheeted covering `pr : L → L₁` which is a
  `(Γ_p, ℓ(p))`-morphism, `pr (E' s) = E₁ (k s)`, `L` having the lifted pair `(E', D₁(k ·))`.
* **The `k`-fold cover of `ℓ(p)`** (`GX.exists_kfold_cover_regular`): lifted holonomy `δ^{2k}`,
  neither hyperbolic nor parabolic, a degree-`2k` link over a regular point (SCOPE (d)).
* **`𝔢` of the cover.** `GX.BiSusp.map pr : [σ, t] ↦ [pr σ, t]`; the pulled-back developing data
  (`GX.GammaLinkCircle.DevData.exists_pullback`, any `Δ₁`); `GX.susp_map_isMorphism` (an
  HS-morphism, `GX.SingularHSStructure.IsMorphism`, a local homeomorphism off the apices);
  `GX.isBranchedCovering_susp_map`, `GX.notMem_ordY_susp_map`.

## Hypothesis checklist

| BBS | here |
|---|---|
| « space-like singularity » (l.1334), « light-like » (l.1467) | ⚠ weakened: `C.pt ∈ dS²`, `Q(C.pt) = 0`; the cover theorems at `0 ≤ Q(p)` (both at once) |
| « of any (even) degree `2k` » | ✓ lifted holonomy `δ^{2k} g`, `g` with a fixed point, `k ≥ 1` (HSSingularities' degree) |
| hyperbolic / parabolic `ℝP¹`-circle (the type, l.794–800) | ⚠ weakened: not assumed; kept both ways (`GX.isHyperbolic_pow_iff`, `GX.isParabolic_pow_iff`) |
| « `k`-branched cover » | ⚠ reading, SCOPE (a) |
| « of a space-like singularity of degree `2` » | ✓ `L₁` at the same `p`, lifted holonomy `δ² g₁` |
| `θ` oriented (the canonical orientation, l.729–731) | ✓ carried by the assembly (the sign needs it); the cover theorems take any `θ` |
| « identifying `P₁` and `P₂` … a wedge turning `k` times around `c` » (l.1335–1336, l.1468) | ✗ not formalized: AdS, `T-bbs-q8` |

## SCOPE (disclosed)

* **(a) « `k`-branched cover ».** Read at the link as a `k`-sheeted covering `L → L₁` which is a
  `(Γ_p, ℓ(p))`-morphism, and at the HS level as `GX.BiSusp.map pr : 𝔢(L) → 𝔢(L₁)` being an
  HS-morphism and a branched covering in gx's sense (`GX.IsBranchedCovering`), branched exactly at
  the two apices for `k ≥ 2`, `k`-to-one off them and one-to-one over each. The paper does not
  define a branched cover of singular HS-surfaces or AdS-spacetimes.
* **(b) « can be constructed as »** is read three ways, all proved: every degree `2k` is the
  `k`-fold cover of a degree `2` (`…exists_degree_two_cover`), the `k`-fold cover of a degree `2`
  has degree `2k` (`…exists_kfold_cover_of_degree_two`, at every `p`), and both signs occur in
  every degree (`GX.exists_spacelike_degree_two_mul`, `GX.exists_lightlike_degree_two_mul`). « With
  its sign kept » (the target's) is `…kfold_sign`, positive and negative in the l.915 form
  (OQ-120 (c)), `i^±` in the time-like reading (OQ-116 (a)).
* **(c) `𝔢(L)` from developing data** (OQ-126 (c)): stated for every `Δ₁` of `L₁`, with the
  pulled-back `Δ` of `L` (`Δ.E` over `Δ₁.E(k ·)`); `𝔢(L)` for another `Δ` is not compared.
* **(d) Trivial holonomy, and divisibility.** For `g = 1` the base `L₁` has lifted holonomy
  `δ²`, that of the link of a regular point (`GX.regular_not_isHyperbolic`), and `L`, like the
  `k`-fold cover of `ℓ(p)` itself (`GX.exists_kfold_cover_regular`), has degree `2k` but is neither
  hyperbolic nor parabolic: the base is « a space-like singularity of degree `2` » in the
  hyperbolic sense exactly when `g` is hyperbolic (the assembly's `g` hyperbolic iff `g₁`). The
  `k`-th root needs `Γ_p` divisible: l.794–795 and l.798 say `Γ_p` is « generated by » a
  hyperbolic, resp. parabolic, element; a cyclic `Γ_p` would have no `k`-th root of its generator
  (argued). Proved: `Γ_p` is the image of the one-parameter group of boosts, resp. null rotations
  (OQ-122 (a)).
* **(e) Not formalized:** the AdS sentences (l.1335–1336, l.1467–1469; `T-bbs-q8`, no AdS₃ at the
  pin); the time-like case (not in the remark).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology Real

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. `k`-th roots in `Γ_p` at a non-time-like `p` -/

namespace GammaP

variable {p : HS 2}

/-- Two elements of `Γ_p` whose tangent actions agree on two independent vectors are equal
(`GX.gammaP_eq_one_of_tangent`). -/
theorem eq_of_tangent_eq {A B : GammaP p} {u v : TpHS p} (huv : linkArea p u v ≠ 0)
    (hu : GammaP.tangent A u = GammaP.tangent B u)
    (hv : GammaP.tangent A v = GammaP.tangent B v) : A = B := by
  have key : ∀ z, GammaP.tangent A z = GammaP.tangent B z := fun z => by
    rw [eq_add_of_linkArea_ne_zero p huv z, map_add, map_smul, map_smul, map_add, map_smul,
      map_smul, hu, hv]
  have h1 : B⁻¹ * A = 1 := gammaP_eq_one_of_tangent p fun z => by
    rw [GammaP.tangent_mul, LinearEquiv.mul_apply, key, ← LinearEquiv.mul_apply,
      ← GammaP.tangent_mul, inv_mul_cancel, GammaP.tangent_one]
    rfl
  exact (inv_mul_eq_one.1 h1).symm

/-! ### `p ∈ dS²`: the boosts of the Lorentzian plane `p^⊥` -/

/-- The future time-like unit vector `Q(p)^{-1/2} (1, t p₁)` of `p^⊥`, at `p ∈ dS²`. -/
def dsE₀ (p : HS 2) : 𝕄 := (Real.sqrt (Causal.Flat.minkQ (p : 𝕄)))⁻¹ • dsU p

/-- The frame `(dsE₀ p, jVec p)` of `p^⊥`, at `p ∈ dS²`. -/
theorem dsFrame (hp : p ∈ HS.piece 2 .deSitter) :
    Causal.Flat.minkQ (dsE₀ p) = -1 ∧ Causal.Flat.minkQ (jVec p) = 1 ∧
      Causal.Flat.minkB (dsE₀ p) (jVec p) = 0 ∧ Causal.Flat.minkB (p : 𝕄) (dsE₀ p) = 0 ∧
      Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 ∧ Causal.Flat.IsFutureTimelike (dsE₀ p) := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hp1 := norm_snd_of_deSitter hp
  have hk : 0 < Real.sqrt (Causal.Flat.minkQ (p : 𝕄)) := Real.sqrt_pos.2 hQ
  have hk2 : Real.sqrt (Causal.Flat.minkQ (p : 𝕄)) ^ 2 = Causal.Flat.minkQ (p : 𝕄) :=
    Real.sq_sqrt hQ.le
  have h0 : Causal.Flat.minkQ (dsE₀ p) = -1 := by
    rw [dsE₀, Causal.Flat.minkQ_smul, minkQ_dsU hp1, inv_pow, hk2]; field_simp
  refine ⟨h0, by rw [minkQ_jVec, hp1, one_pow], ?_, ?_, ?_, ⟨?_, by rw [h0]; norm_num⟩⟩
  · rw [dsE₀, Causal.Flat.minkB_smul_left, minkB_dsU_jVec, mul_zero]
  · rw [dsE₀, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_comm, minkB_dsU_self hp1, mul_zero]
  · rw [Causal.Flat.minkB_comm]; exact minkB_jVec p
  · simp only [dsE₀, dsU, Prod.smul_fst, smul_eq_mul, mul_one]
    exact inv_pos.2 hk

theorem dsBoost_mem (hp : p ∈ HS.piece 2 .deSitter) (ζ : ℝ) :
    Causal.Flat.boost (dsFrame hp).1 (dsFrame hp).2.1 (dsFrame hp).2.2.1 ζ ∈
      Causal.Flat.lorentz 2 := by
  obtain ⟨h0, h1, h01, -, -, hfe⟩ := dsFrame hp
  set Bt := Causal.Flat.boost h0 h1 h01 ζ
  have hQB : ∀ v, Causal.Flat.minkQ (Bt v) = Causal.Flat.minkQ v :=
    Causal.Flat.minkQ_boostLin h0 h1 h01 ζ
  have hdet : LinearMap.det (Bt : 𝕄 →ₗ[ℝ] 𝕄) = 1 :=
    Causal.Flat.det_eq_one_of_eq_sq hQB (B := Causal.Flat.boostLin (dsE₀ p) (jVec p) (ζ / 2)) (by
      rw [Causal.Flat.boostLin_comp h0 h1 h01, add_halves]; rfl)
  have hfe0 : dsE₀ p ≠ 0 := fun h => by rw [h] at hfe; exact lt_irrefl _ hfe.1
  have hBt0 : Causal.Flat.IsFutureTimelike (Bt (dsE₀ p)) := by
    refine isFutureTimelike_of_minkB_neg (by rw [hQB, h0]; norm_num) ⟨hfe.1.le, hfe.2.le⟩ hfe0 ?_
    rw [Causal.Flat.minkB_comm, Causal.Flat.boost_apply, Causal.Flat.minkB_boostLin_e₀ h0 h01,
      ← Causal.Flat.minkQ_eq_minkB, h0, h01]
    nlinarith [Real.cosh_pos ζ]
  exact Causal.Flat.mem_lorentz_of_future hQB hfe hBt0 hdet

theorem dsBoost_fix (hp : p ∈ HS.piece 2 .deSitter) (ζ : ℝ) :
    Causal.Flat.boost (dsFrame hp).1 (dsFrame hp).2.1 (dsFrame hp).2.2.1 ζ (p : 𝕄) = p := by
  obtain ⟨-, -, -, hpe₀, hpe₁, -⟩ := dsFrame hp
  rw [Causal.Flat.boost_apply, Causal.Flat.boostLin_apply, hpe₀, hpe₁]
  simp

/-- **The boost of rapidity `ζ` fixing `p ∈ dS²`**, as an element of `Γ_p`. -/
def dsBoost (hp : p ∈ HS.piece 2 .deSitter) (ζ : ℝ) : GammaP p :=
  ⟨⟨Causal.Flat.boost (dsFrame hp).1 (dsFrame hp).2.1 (dsFrame hp).2.2.1 ζ, dsBoost_mem hp ζ⟩,
    dsBoost_fix hp ζ⟩

theorem dsBoost_apply (hp : p ∈ HS.piece 2 .deSitter) (ζ : ℝ) (x : 𝕄) :
    (((dsBoost hp ζ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x =
      Causal.Flat.boostLin (dsE₀ p) (jVec p) ζ x := rfl

theorem dsBoost_add (hp : p ∈ HS.piece 2 .deSitter) (ζ η : ℝ) :
    dsBoost hp (ζ + η) = dsBoost hp ζ * dsBoost hp η := by
  obtain ⟨h0, h1, h01, -, -, -⟩ := dsFrame hp
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  show (((dsBoost hp (ζ + η) : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x =
    (((dsBoost hp ζ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      ((((dsBoost hp η : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x)
  rw [dsBoost_apply, dsBoost_apply, dsBoost_apply, ← Causal.Flat.boostLin_comp h0 h1 h01]
  rfl

theorem dsBoost_zero (hp : p ∈ HS.piece 2 .deSitter) : dsBoost hp 0 = 1 := by
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  show (((dsBoost hp 0 : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x = x
  rw [dsBoost_apply, Causal.Flat.boostLin_zero]
  rfl

theorem dsBoost_pow (hp : p ∈ HS.piece 2 .deSitter) (ζ : ℝ) (n : ℕ) :
    dsBoost hp ζ ^ n = dsBoost hp (n * ζ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, dsBoost_zero]
  | succ m ih => rw [pow_succ, ih, ← dsBoost_add]; congr 1; push_cast; ring

/-- **`Γ_p` is the one-parameter group of boosts**, at `p ∈ dS²` (l.794–795). -/
theorem exists_eq_dsBoost (hp : p ∈ HS.piece 2 .deSitter) (A : GammaP p) :
    ∃ ζ : ℝ, A = dsBoost hp ζ := by
  obtain ⟨h0, h1, h01, hpe₀, hpe₁, -⟩ := dsFrame hp
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have h0' : Causal.Flat.minkB (dsE₀ p) (dsE₀ p) = -1 := by rw [← Causal.Flat.minkQ_eq_minkB, h0]
  have h1' : Causal.Flat.minkB (jVec p) (jVec p) = 1 := by rw [← Causal.Flat.minkQ_eq_minkB, h1]
  have h10 : Causal.Flat.minkB (jVec p) (dsE₀ p) = 0 := by rw [Causal.Flat.minkB_comm, h01]
  have hp0 : Causal.Flat.minkB (p : 𝕄) (dsE₀ p) = 0 := hpe₀
  have hp1 : Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 := hpe₁
  -- the two null vectors `(dsE₀ p) ± (jVec p)` of `p^⊥`
  have hB : ∀ (ε : ℝ) (ζ : ℝ), ε = 1 ∨ ε = -1 →
      (((dsBoost hp ζ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) ((dsE₀ p) + ε • (jVec p)) =
        Real.exp (ε * ζ) • ((dsE₀ p) + ε • (jVec p)) := by
    intro ε ζ hε
    rw [dsBoost_apply, Causal.Flat.boostLin_apply]
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h0', h1', h01, h10]
    rcases hε with rfl | rfl
    · simp only [one_mul]; rw [← Real.cosh_add_sinh]; module
    · rw [show (-1 : ℝ) * ζ = -ζ by ring, ← Real.cosh_sub_sinh]; module
  have hne : ∀ ε : ℝ, tpMk p ((dsE₀ p) + ε • (jVec p)) ≠ 0 := fun ε h => by
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h
    have := congrArg (fun v => Causal.Flat.minkB v (dsE₀ p)) hc
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h0', h10, hp0] at this
    linarith
  have hTB : ∀ (ζ ε : ℝ), ε = 1 ∨ ε = -1 →
      GammaP.tangent (dsBoost hp ζ) (tpMk p ((dsE₀ p) + ε • (jVec p))) =
        Real.exp (ε * ζ) • tpMk p ((dsE₀ p) + ε • (jVec p)) := fun ζ ε hε => by
    rw [GammaP.tangent_mk]
    exact (congrArg (tpMk p) (hB ε ζ hε)).trans (Submodule.Quotient.mk_smul _ _ _)
  -- `A` fixes the two null directions, with positive factors
  have hfix : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → ∃ c : ℝ, 0 < c ∧
      GammaP.tangent A (tpMk p ((dsE₀ p) + ε • (jVec p))) =
        c • tpMk p ((dsE₀ p) + ε • (jVec p)) := by
    intro ε hε
    have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hw := hne ε
    have hQw : Causal.Flat.minkQ ((dsE₀ p) + ε • (jVec p)) = 0 := by
      rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_right, h0,
        h1, h01, hε2]; ring
    have hBpw : Causal.Flat.minkB (p : 𝕄) ((dsE₀ p) + ε • (jVec p)) = 0 := by
      rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, hp0, hp1]; ring
    generalize (dsE₀ p) + ε • (jVec p) = w at hw hQw hBpw ⊢
    have hσ := coe_dirOf p hw
    have h0σ : Causal.Flat.minkQ (dsProj p (dirOf p w)) = 0 := by
      rw [hσ, map_smul, dsProj_mk, perpLin_apply, hBpw, zero_smul, sub_zero,
        Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul, hQw, mul_zero, mul_zero]
    obtain ⟨c, hc, hT⟩ := (gammaP_smul_eq_iff A (dirOf p w)).1 (smul_eq_of_deSitter hp h0σ A)
    rw [hσ, map_smul] at hT
    have hr : ‖tpMk p w‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 hw)
    exact ⟨c, hc, smul_right_injective (TpHS p) hr (by simp only; rw [hT, smul_comm])⟩
  obtain ⟨cp, hcp, hTp⟩ := hfix 1 (Or.inl rfl)
  obtain ⟨cm, hcm, hTm⟩ := hfix (-1) (Or.inr rfl)
  have harea : linkArea p (tpMk p ((dsE₀ p) + (1 : ℝ) • (jVec p)))
      (tpMk p ((dsE₀ p) + (-1 : ℝ) • (jVec p))) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero p (hne 1) h
    obtain ⟨c, hc⟩ := (tpMk_eq_tpMk_iff p).1 (hr.trans (Submodule.Quotient.mk_smul _ r _).symm)
    have ha := congrArg (fun v => Causal.Flat.minkB v (dsE₀ p)) hc
    have hb := congrArg (fun v => Causal.Flat.minkB v (jVec p)) hc
    simp only [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, h0', h1', h01, h10,
      hp0, hp1] at ha hb
    linarith
  have hprod : cp * cm = 1 := by
    have h := linkArea_tangent p A (tpMk p ((dsE₀ p) + (1 : ℝ) • (jVec p)))
      (tpMk p ((dsE₀ p) + (-1 : ℝ) • (jVec p)))
    rw [hTp, hTm, linkArea_smul_left, linkArea_smul_right] at h
    have h' : (cp * cm - 1) *
        linkArea p (tpMk p ((dsE₀ p) + (1 : ℝ) • (jVec p)))
          (tpMk p ((dsE₀ p) + (-1 : ℝ) • (jVec p))) = 0 := by
      linear_combination h
    linarith [(mul_eq_zero.1 h').resolve_right harea]
  refine ⟨Real.log cp, eq_of_tangent_eq harea ?_ ?_⟩
  · rw [hTp, hTB _ 1 (Or.inl rfl), one_mul, Real.exp_log hcp]
  · rw [hTm, hTB _ (-1) (Or.inr rfl), neg_one_mul, Real.exp_neg, Real.exp_log hcp,
      eq_inv_of_mul_eq_one_right hprod]

/-! ### `p ∈ ∂ℍ²±`: the null rotations about `p` -/

/-- `jVec p` is a unit space-like vector orthogonal to `p`, at a light-like `p`. -/
theorem nullFrame (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    Causal.Flat.minkQ (jVec p) = 1 ∧ Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 :=
  ⟨by rw [minkQ_jVec, norm_snd_of_null hp, one_pow], by
    rw [Causal.Flat.minkB_comm]; exact minkB_jVec p⟩

theorem nullBoost_mem (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (s : ℝ) :
    Causal.Flat.nullRot hp (nullFrame hp).1 (nullFrame hp).2 s ∈ Causal.Flat.lorentz 2 ∧
      Causal.Flat.nullRot hp (nullFrame hp).1 (nullFrame hp).2 s (p : 𝕄) = p := by
  obtain ⟨he, hue⟩ := nullFrame hp
  set N := Causal.Flat.nullRot hp he hue s
  have hQN : ∀ v, Causal.Flat.minkQ (N v) = Causal.Flat.minkQ v :=
    Causal.Flat.minkQ_nullRotLin hp he hue s
  have hdet : LinearMap.det (N : 𝕄 →ₗ[ℝ] 𝕄) = 1 :=
    Causal.Flat.det_eq_one_of_eq_sq hQN (B := Causal.Flat.nullRotLin (p : 𝕄) (jVec p) (s / 2)) (by
      rw [Causal.Flat.nullRotLin_comp hp he hue, add_halves]; rfl)
  have hfix : N (p : 𝕄) = p := by
    rw [Causal.Flat.nullRot_apply, Causal.Flat.nullRotLin_apply, ← Causal.Flat.minkQ_eq_minkB, hp,
      hue]
    simp
  exact ⟨mem_lorentz_of_fix hQN hdet hp.le (raySphere_ne_zero p) hfix, hfix⟩

/-- **The null rotation of parameter `s` about a light-like `p`**, as an element of `Γ_p`. -/
def nullBoost (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (s : ℝ) : GammaP p :=
  ⟨⟨Causal.Flat.nullRot hp (nullFrame hp).1 (nullFrame hp).2 s, (nullBoost_mem hp s).1⟩,
    (nullBoost_mem hp s).2⟩

theorem nullBoost_apply (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (s : ℝ) (x : 𝕄) :
    (((nullBoost hp s : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x =
      Causal.Flat.nullRotLin (p : 𝕄) (jVec p) s x := rfl

theorem nullBoost_add (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (s t : ℝ) :
    nullBoost hp (s + t) = nullBoost hp s * nullBoost hp t := by
  obtain ⟨he, hue⟩ := nullFrame hp
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  show (((nullBoost hp (s + t) : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x =
    (((nullBoost hp s : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
      ((((nullBoost hp t : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x)
  rw [nullBoost_apply, nullBoost_apply, nullBoost_apply, ← Causal.Flat.nullRotLin_comp hp he hue]
  rfl

theorem nullBoost_zero (hp : Causal.Flat.minkQ (p : 𝕄) = 0) : nullBoost hp 0 = 1 := by
  refine Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  show (((nullBoost hp 0 : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) x = x
  rw [nullBoost_apply, Causal.Flat.nullRotLin_zero]
  rfl

theorem nullBoost_pow (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (s : ℝ) (n : ℕ) :
    nullBoost hp s ^ n = nullBoost hp (n * s) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, nullBoost_zero]
  | succ m ih => rw [pow_succ, ih, ← nullBoost_add]; congr 1; push_cast; ring

/-- **`Γ_p` is the one-parameter group of null rotations**, at a light-like `p` (l.797–798). -/
theorem exists_eq_nullBoost (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (A : GammaP p) :
    ∃ s : ℝ, A = nullBoost hp s := by
  obtain ⟨he, hue⟩ := nullFrame hp
  have hp1 := norm_snd_of_null hp
  set τ := tpMk p (jVec p)
  have hτ : τ ≠ 0 := tpMk_jVec_ne_zero p hp1
  have hτ0 : nullPairing p τ = 0 := by rw [nullPairing_mk p hp]; exact hue
  obtain ⟨w₀, -, hB₀⟩ := exists_minkB_neg hp
  set ê := tpMk p w₀
  have hφe : nullPairing p ê ≠ 0 := by rw [nullPairing_mk p hp]; exact hB₀.ne
  have harea : linkArea p τ ê ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero p hτ h
    apply hφe
    rw [hr, map_smul, hτ0, smul_zero]
  obtain ⟨c, hc⟩ := GammaP.eq_smul_of_nullPairing_eq_zero hp hτ hτ0
    (z := GammaP.tangent A ê - ê) (by rw [map_sub, nullPairing_tangent, sub_self])
  have hBw : Causal.Flat.minkB w₀ (p : 𝕄) ≠ 0 := by
    rw [Causal.Flat.minkB_comm]; exact hB₀.ne
  refine ⟨c / Causal.Flat.minkB w₀ (p : 𝕄), eq_of_tangent_eq harea ?_ ?_⟩
  · rw [GammaP.tangent_eq_self_of_null hp A hτ0, GammaP.tangent_eq_self_of_null hp _ hτ0]
  · have e1 : Causal.Flat.nullRotLin (p : 𝕄) (jVec p) (c / Causal.Flat.minkB w₀ (p : 𝕄)) w₀ =
        w₀ + c • jVec p + (-(c / Causal.Flat.minkB w₀ (p : 𝕄) * Causal.Flat.minkB w₀ (jVec p)) -
          (c / Causal.Flat.minkB w₀ (p : 𝕄)) ^ 2 / 2 * Causal.Flat.minkB w₀ (p : 𝕄)) • (p : 𝕄) := by
      rw [Causal.Flat.nullRotLin_apply, div_mul_cancel₀ c hBw]
    have e2 : GammaP.tangent A ê = ê + c • τ := by rw [← hc]; abel
    have e3 : tpMk p (w₀ + c • jVec p + (-(c / Causal.Flat.minkB w₀ (p : 𝕄) *
        Causal.Flat.minkB w₀ (jVec p)) - (c / Causal.Flat.minkB w₀ (p : 𝕄)) ^ 2 / 2 *
          Causal.Flat.minkB w₀ (p : 𝕄)) • (p : 𝕄)) = tpMk p (w₀ + c • jVec p) :=
      (tpMk_eq_tpMk_iff p).2 ⟨_, rfl⟩
    rw [e2]
    show _ = tpMk p ((((nullBoost hp _ : GammaP p) : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w₀)
    rw [nullBoost_apply, e1, e3]
    show _ = (ℝ ∙ (p : 𝕄)).mkQ (w₀ + c • jVec p)
    rw [map_add, map_smul]
    rfl

/-- **`k`-th roots in `Γ_p`** at a non-time-like `p`: `Γ_p` is the image of `ℝ`. -/
theorem exists_pow_eq (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄)) (A : GammaP p) {k : ℕ}
    (hk : k ≠ 0) : ∃ B : GammaP p, B ^ k = A := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rcases hp.lt_or_eq with hq | hq
  · obtain ⟨ζ, rfl⟩ := exists_eq_dsBoost hq A
    exact ⟨dsBoost hq (ζ / k), by rw [dsBoost_pow, mul_div_cancel₀ _ hk']⟩
  · obtain ⟨s, rfl⟩ := exists_eq_nullBoost hq.symm A
    exact ⟨nullBoost hq.symm (s / k), by rw [nullBoost_pow, mul_div_cancel₀ _ hk']⟩

end GammaP

/-! ## 2. The `k`-th root of a lifted holonomy -/

/-- At a non-time-like `p`, some direction of `ℓ(p)` is fixed by all of `Γ_p`. -/
theorem exists_dir_fixed_gammaP {p : HS 2} (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄)) :
    ∃ σ : Link p, ∀ A : GammaP p, A • σ = σ := by
  rcases hp.lt_or_eq with hq | hq
  · obtain ⟨n₁, -, h₁, -⟩ := exists_two_null (p := p) hq
    exact ⟨n₁, fun A => smul_eq_of_deSitter hq h₁ A⟩
  · have hne : (tangentDirs p).Nonempty := by
      by_contra h0
      rw [not_nonempty_iff_eq_empty] at h0
      have := ncard_tangentDirs (p := p) hq.symm
      rw [h0, ncard_empty] at this
      exact absurd this (by norm_num)
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, fun A => smul_eq_of_null hq.symm hn A⟩

namespace GTilde

/-- Powers of an element of `G̃` act by iteration. -/
theorem pow_succ_apply (g : GTilde) (n : ℕ) (x : ℝ) : (g ^ (n + 1)) x = (g ^ n) (g x) := by
  rw [pow_succ, GTilde.coe_mul_apply]

theorem le_pow_apply_of_le_apply {g : GTilde} {x : ℝ} (hx : x ≤ g x) (n : ℕ) :
    x ≤ (g ^ n) x := by
  induction n with
  | zero => rw [pow_zero, GTilde.one_apply]
  | succ m ih => rw [pow_succ_apply]; exact ih.trans ((GTilde.strictMono (g ^ m)).monotone hx)

theorem pow_apply_le_of_apply_le {g : GTilde} {x : ℝ} (hx : g x ≤ x) (n : ℕ) :
    (g ^ n) x ≤ x := by
  induction n with
  | zero => rw [pow_zero, GTilde.one_apply]
  | succ m ih => rw [pow_succ_apply]; exact ((GTilde.strictMono (g ^ m)).monotone hx).trans ih

/-- `x ≤ g x` iff `x ≤ gᵏ x`, `k ≥ 1`. -/
theorem le_apply_iff_le_pow_apply (g : GTilde) {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    x ≤ g x ↔ x ≤ (g ^ k) x := by
  refine ⟨fun hx => le_pow_apply_of_le_apply hx k, fun h => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ_apply] at h
  have := (GTilde.strictMono (g ^ m)) hlt
  linarith [pow_apply_le_of_apply_le hlt.le m]

/-- `g x ≤ x` iff `gᵏ x ≤ x`, `k ≥ 1`. -/
theorem apply_le_iff_pow_apply_le (g : GTilde) {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    g x ≤ x ↔ (g ^ k) x ≤ x := by
  refine ⟨fun hx => pow_apply_le_of_apply_le hx k, fun h => ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ_apply] at h
  have := (GTilde.strictMono (g ^ m)) hlt
  linarith [le_pow_apply_of_le_apply hlt.le m]

/-- An element of `G̃` with `gᵏ = 1`, `k ≥ 1`, is `1`. -/
theorem eq_one_of_pow_eq_one {g : GTilde} {k : ℕ} (hk : k ≠ 0) (h : g ^ k = 1) : g = 1 := by
  refine GTilde.ext' fun x => le_antisymm ?_ ?_
  · exact (apply_le_iff_pow_apply_le g hk x).2 (by rw [h, GTilde.one_apply])
  · exact (le_apply_iff_le_pow_apply g hk x).2 (by rw [h, GTilde.one_apply])

/-- An element of `G̃` with a fixed point is `1` iff its image in `PSL(2,ℝ)` is. -/
theorem toPSL_eq_one_iff_of_fixed {g : GTilde} (hg : ∃ x, g x = x) : toPSL g = 1 ↔ g = 1 := by
  refine ⟨fun h1 => ?_, fun h => by rw [h, map_one]⟩
  have hk : g ∈ GTilde.toPSL.ker := h1
  rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨j, hj⟩ := hk
  obtain ⟨x, hx⟩ := hg
  rw [← hj, GTilde.delta_zpow_apply] at hx
  have hj0 : j = 0 := by exact_mod_cast (show (j : ℝ) = 0 by linarith)
  rw [← hj, hj0, zpow_zero]

/-- A fixed point of `g` is one of `gⁿ`. -/
theorem pow_apply_of_fixed {g : GTilde} {x : ℝ} (hx : g x = x) (n : ℕ) : (g ^ n) x = x := by
  induction n with
  | zero => rw [pow_zero, GTilde.one_apply]
  | succ m ih => rw [pow_succ_apply, hx, ih]

/-- `(δ² g)ᵏ = δ^{2k} gᵏ` (`δ` is central). -/
theorem delta_sq_mul_pow (g : GTilde) (k : ℕ) :
    (GTilde.delta ^ (2 : ℤ) * g) ^ k = GTilde.delta ^ (2 * k : ℤ) * g ^ k := by
  have hc : Commute (GTilde.delta ^ (2 : ℤ)) g :=
    ((Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ GTilde.delta_mem_center 2)) g).symm
  rw [hc.mul_pow, ← zpow_natCast, ← zpow_mul]

end GTilde

/-- **The `k`-th root of a lift with a fixed point**: for `h ∈ G̃` with a fixed point lifting
`ρ ∈ Γ_p` through `linkCover`, `p` non-time-like, there are a `k`-th root `ρ'` of `ρ` in `Γ_p` and
its lift `g` with a fixed point, and `g^k = h`. -/
theorem exists_root_lift {p : HS 2} (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄))
    (θ : TpHS p ≃ₗ[ℝ] ℂ) {ρ : GammaP p} {h : GTilde}
    (hh : ∀ t, linkCover p θ (h t) = ρ • linkCover p θ t) (hfix : ∃ x, h x = x) {k : ℕ}
    (hk : k ≠ 0) :
    ∃ (ρ' : GammaP p) (g : GTilde), ρ' ^ k = ρ ∧
      (∀ t, linkCover p θ (g t) = ρ' • linkCover p θ t) ∧ (∃ x, g x = x) ∧ g ^ k = h := by
  obtain ⟨ρ', hρ'⟩ := GammaP.exists_pow_eq hp ρ hk
  obtain ⟨σ₀, hσ₀⟩ := exists_dir_fixed_gammaP hp
  obtain ⟨F, hF⟩ := exists_rayLift p (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) ρ'
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective p θ σ₀
  obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1
    (show linkCover p θ t₀ = linkCover p θ (F t₀) by rw [hF, ht₀, hσ₀])
  set g : GTilde := GTilde.delta ^ (-(2 * n)) * F
  have hgapp : ∀ t, g t = F t + 2 * ((-n : ℤ) : ℝ) := fun t => by
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
  have hg : ∀ t, linkCover p θ (g t) = ρ' • linkCover p θ t := fun t => by
    rw [hgapp, linkCover_add_two_mul, hF]
  have hgfix : g t₀ = t₀ := by rw [hgapp, hn]; push_cast; ring
  have hpow : ∀ m : ℕ, ∀ t, linkCover p θ ((g ^ m) t) = (ρ' ^ m) • linkCover p θ t := by
    intro m
    induction m with
    | zero => intro t; rw [pow_zero, pow_zero, GTilde.one_apply, one_smul]
    | succ m ih => intro t; rw [GTilde.pow_succ_apply, ih, hg, pow_succ, mul_smul]
  obtain ⟨m, hm⟩ := linkCover_lift_eq p (GTilde.continuous (g ^ k)) (GTilde.continuous h)
    (fun t => by rw [hpow k, hρ', hh])
  have hm0 : m = 0 := by
    have e := hm t₀
    rw [GTilde.pow_apply_of_fixed hgfix] at e
    have h1 := GTilde.sub_one_lt_apply_of_fixed hfix t₀
    have h2 := GTilde.apply_lt_delta_of_fixed hfix t₀
    rw [GTilde.delta_apply] at h2
    have h3 : (m : ℝ) < 1 := by linarith
    have h4 : (-1 : ℝ) < m := by linarith
    have : m < 1 := by exact_mod_cast h3
    have : -1 < m := by exact_mod_cast h4
    omega
  refine ⟨ρ', g, hρ', hg, ⟨t₀, hgfix⟩, GTilde.ext' fun t => ?_⟩
  rw [hm, hm0]; simp

/-! ## 3. The `k`-fold cover of a `(Γ_p, ℓ(p))`-circle -/

section PeriodicCover

variable {L L₁ : Type*} [TopologicalSpace L] [TopologicalSpace L₁]

/-- An eventual property along a periodic covering `E` near `s` holds near `E s`. -/
theorem IsPeriodicCover.eventually_of_eventually {E : ℝ → L} (hE : IsPeriodicCover E)
    {P : L → Prop} {s : ℝ} (h : ∀ᶠ s' in 𝓝 s, P (E s')) : ∀ᶠ y in 𝓝 (E s), P y := by
  filter_upwards [hE.isCoveringMap.isLocalHomeomorph.isOpenMap.image_mem_nhds h] with y hy
  obtain ⟨s', hs', rfl⟩ := hy
  exact hs'

/-- `χ (s + n) = χ s + ε n` from `χ (s + 1) = χ s + ε`. -/
theorem add_int_of_add_one {χ : ℝ → ℝ} {ε : ℝ} (hχ : ∀ s, χ (s + 1) = χ s + ε) (n : ℤ) (s : ℝ) :
    χ (s + n) = χ s + ε * n := by
  induction n using Int.induction_on generalizing s with
  | zero => simp
  | succ m ih =>
    have e : s + (((m : ℤ) + 1 : ℤ) : ℝ) = (s + ((m : ℤ) : ℝ)) + 1 := by push_cast; ring
    rw [e, hχ, ih]; push_cast; ring
  | pred m ih =>
    have := hχ (s + ((-(m : ℤ) - 1 : ℤ) : ℝ))
    rw [show s + ((-(m : ℤ) - 1 : ℤ) : ℝ) + 1 = s + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring,
      ih] at this
    push_cast at this ⊢
    linarith

/-- **Reparametrising a periodic covering** by a homeomorphism `χ` of `ℝ` with
`χ (s + 1) = χ s ± 1`. -/
theorem IsPeriodicCover.comp_homeomorph' {E : ℝ → L} (hE : IsPeriodicCover E) (χ : ℝ ≃ₜ ℝ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hχ : ∀ s, χ (s + 1) = χ s + ε) :
    IsPeriodicCover (E ∘ χ) := by
  have hε2 : (ε : ℝ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  refine ⟨hE.isCoveringMap.comp_homeomorph χ, hE.surjective.comp χ.surjective, fun s => ?_,
    fun s t hst => ?_⟩
  · simp only [Function.comp_apply]
    rw [hχ, hE.add_int]
  · obtain ⟨n, hn⟩ := hE.fiber _ _ hst
    refine ⟨ε * n, χ.injective ?_⟩
    rw [hn, add_int_of_add_one hχ]
    push_cast
    rw [← mul_assoc, hε2, one_mul]

/-- **The `k`-fold map** `π : L → L₁`, `π (E s) = E₁ (k s)`, for periodic coverings `E`, `E₁`. -/
theorem exists_kfold_map {E : ℝ → L} {E₁ : ℝ → L₁} (hE : IsPeriodicCover E)
    (hE₁ : IsPeriodicCover E₁) (k : ℕ) :
    ∃ pr : L → L₁, Continuous pr ∧ ∀ s, pr (E s) = E₁ (k * s) := by
  classical
  let pr : L → L₁ := fun y => E₁ (k * (hE.surjective y).choose)
  have hpr : ∀ s, pr (E s) = E₁ (k * s) := fun s => by
    obtain ⟨n, hn⟩ := hE.fiber _ _ (hE.surjective (E s)).choose_spec
    show E₁ (k * (hE.surjective (E s)).choose) = E₁ (k * s)
    generalize (hE.surjective (E s)).choose = c at hn ⊢
    subst hn
    rw [mul_add, show (k : ℝ) * n = ((k * n : ℤ) : ℝ) by push_cast; ring, hE₁.add_int]
  refine ⟨pr, ?_, hpr⟩
  rw [(hE.isCoveringMap.isQuotientMap hE.surjective).continuous_iff]
  have : pr ∘ E = E₁ ∘ fun s => (k : ℝ) * s := funext hpr
  rw [this]
  exact hE₁.isCoveringMap.continuous.comp (continuous_const_mul _)

/-- **The `k`-fold map has `k` points in each fibre.** -/
theorem card_fiber_of_kfold {E : ℝ → L} {E₁ : ℝ → L₁} (hE : IsPeriodicCover E)
    (hE₁ : IsPeriodicCover E₁) {k : ℕ} (hk : k ≠ 0) {pr : L → L₁}
    (hpr : ∀ s, pr (E s) = E₁ (k * s)) (y : L₁) : Nat.card (pr ⁻¹' {y}) = k := by
  obtain ⟨u₀, rfl⟩ := hE₁.surjective y
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hmem : ∀ j : Fin k, E ((u₀ + (j : ℕ)) / k) ∈ pr ⁻¹' {E₁ u₀} := fun j => by
    show pr _ = _
    rw [hpr, mul_div_cancel₀ _ hk',
      show u₀ + ((j : ℕ) : ℝ) = u₀ + (((j : ℕ) : ℤ) : ℝ) by push_cast; rfl, hE₁.add_int]
  let e : Fin k → pr ⁻¹' {E₁ u₀} := fun j => ⟨_, hmem j⟩
  have hinj : Function.Injective e := by
    intro i j hij
    have h := congrArg Subtype.val hij
    obtain ⟨n, hn⟩ := hE.fiber _ _ h
    have h1 : ((j : ℕ) : ℝ) = (i : ℕ) + k * n := by
      field_simp at hn
      linarith
    have hz : ((j : ℕ) : ℤ) = (i : ℕ) + k * n := by exact_mod_cast h1
    have hi := i.2
    have hj := j.2
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with hlt | heq | hgt
      · have : (k : ℤ) * n ≤ -k := by nlinarith
        omega
      · exact heq
      · have : (k : ℤ) ≤ k * n := by nlinarith
        omega
    exact Fin.ext (by rw [hn0, mul_zero, add_zero] at hz; exact_mod_cast hz.symm)
  have hsurj : Function.Surjective e := by
    rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := hE.surjective x
    have hx' : E₁ u₀ = E₁ (k * s) := by rw [← hpr]; exact hx.symm
    obtain ⟨m, hm⟩ := hE₁.fiber _ _ hx'
    have hkz : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hr0 : 0 ≤ m % k := Int.emod_nonneg _ hkz.ne'
    have hrk : m % k < k := Int.emod_lt_of_pos _ hkz
    have hdm : (k : ℤ) * (m / k) + m % k = m := Int.mul_ediv_add_emod m k
    refine ⟨⟨(m % k).toNat, by omega⟩, Subtype.ext ?_⟩
    show E ((u₀ + (((m % k).toNat : ℕ) : ℝ)) / k) = E s
    have hcast : (((m % k).toNat : ℕ) : ℝ) = ((m % k : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
    have hs : s = (u₀ + (((m % k).toNat : ℕ) : ℝ)) / k + ((m / k : ℤ) : ℝ) := by
      rw [hcast]
      have : (m : ℝ) = (k : ℝ) * ((m / k : ℤ) : ℝ) + ((m % k : ℤ) : ℝ) := by exact_mod_cast hdm.symm
      field_simp
      linarith
    rw [hs, hE.add_int]
  rw [← Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

end PeriodicCover

section Cover

variable {p : HS 2} {θ : TpHS p ≃ₗ[ℝ] ℂ} {L L₁ : Type*} [TopologicalSpace L]
  [TopologicalSpace L₁] {cs : ChartedSpace (Link p) L}
  {hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))} {hL : IsCircle L}
  {cs₁ : ChartedSpace (Link p) L₁} {hcs₁ : HasGroupoid L₁ (gxGroupoid (GammaP p) (Link p))}
  {hL₁ : IsCircle L₁}

/-- `D (s + k) = fᵏ (D s)` for a lifted developing pair. -/
theorem add_nat_of_add_one {D : ℝ → ℝ} {f : GTilde} (hDf : ∀ s, D (s + 1) = f (D s)) (n : ℕ)
    (s : ℝ) : D (s + n) = (f ^ n) (D s) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, hDf, ih, pow_succ', GTilde.coe_mul_apply]

theorem lt_pow_apply_of_forall_lt {f : GTilde} (hlt : ∀ x, x < f x) {k : ℕ} (hk : k ≠ 0)
    (x : ℝ) : x < (f ^ k) x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [GTilde.pow_succ_apply]
  exact lt_of_lt_of_le (hlt x) (GTilde.le_pow_apply_of_le_apply (hlt (f x)).le m)

/-- **The `k`-fold cover** (the core of `bbsrem:degk`): if the lifted holonomies satisfy
`f = f₁ᵏ` and `f₁` has no fixed point, then `L` is the `k`-fold cyclic cover of `L₁`: there is a
`k`-sheeted covering map `pr : L → L₁` which is a `(Γ_p, ℓ(p))`-morphism, unwrapping one turn of
`L` onto `k` turns of `L₁` (`pr (E' s) = E₁ (k s)`), and `L` has the lifted developing pair
`(E', D₁(k ·))`. -/
theorem GammaLinkCircle.IsLiftedDev.exists_kfold_cover {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E D f) {E₁ : ℝ → L₁} {D₁ : ℝ → ℝ}
    {f₁ : GTilde} (h₁ : (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLiftedDev θ E₁ D₁ f₁)
    (hlt : ∀ x, x < f₁ x) {k : ℕ} (hk : k ≠ 0) (hf : f = f₁ ^ k) :
    ∃ (pr : L → L₁) (E' : ℝ → L),
      (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E' (fun s => D₁ (k * s)) f ∧
      (∀ s, pr (E' s) = E₁ (k * s)) ∧ IsCoveringMap pr ∧ (∀ y, Nat.card (pr ⁻¹' {y}) = k) ∧
      (letI := cs; letI := cs₁; IsGXMorphism (GammaP p) (Link p) pr) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hltk := lt_pow_apply_of_forall_lt hlt hk
  -- the developed images are all of `ℝP̃¹`
  have hr : range D = univ := by
    letI := (GammaLinkCircle.mk p cs hcs hL).rp1ChartedSpace θ
    haveI := (GammaLinkCircle.mk p cs hcs hL).rp1_hasGroupoid θ
    exact h.isLiftedDevPair.isComp.eq_univ (fun x => by rw [hf]; exact (hltk x).ne')
  have hr₁ : range D₁ = univ := by
    letI := (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).rp1ChartedSpace θ
    haveI := (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).rp1_hasGroupoid θ
    exact h₁.isLiftedDevPair.isComp.eq_univ (fun x => (hlt x).ne')
  obtain ⟨hE, hDc, hDm, hd, hDf⟩ := h
  obtain ⟨hE₁, hD₁c, hD₁m, hd₁, hD₁f⟩ := h₁
  set Do : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective D hDm (range_eq_univ.1 hr)
  set D₁o : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective D₁ hD₁m (range_eq_univ.1 hr₁)
  have hDo : ∀ z, Do z = D z := fun z => rfl
  have hD₁o : ∀ z, D₁o z = D₁ z := fun z => rfl
  set χo : ℝ ≃o ℝ := (OrderIso.mulLeft₀ (k : ℝ) hkpos).trans (D₁o.trans Do.symm)
  have hχo : ∀ s, χo s = Do.symm (D₁ (k * s)) := fun s => rfl
  have hDχ : ∀ s, D (χo s) = D₁ (k * s) := fun s => by
    rw [hχo, ← hDo, OrderIso.apply_symm_apply]
  have hD₁k : ∀ u, D₁ (u + k) = f (D₁ u) := fun u => by
    rw [add_nat_of_add_one hD₁f, hf]
  have hχ1 : ∀ s, χo (s + 1) = χo s + 1 := fun s => by
    have e : ∀ z, Do.symm (D z) = z := fun z => Do.symm_apply_apply z
    rw [hχo, hχo, mul_add, mul_one, hD₁k, ← hDχ, ← hDf, e, e]
  set χ : ℝ ≃ₜ ℝ := χo.toHomeomorph
  have hχ : ∀ s, χ s = χo s := fun s => rfl
  have hE' : IsPeriodicCover (E ∘ χ) :=
    hE.comp_homeomorph' χ (ε := 1) (Or.inl rfl) (fun s => by
      rw [hχ, hχ, hχ1]; push_cast; ring)
  have hd' : (GammaLinkCircle.mk p cs hcs hL).IsDevAlong (E ∘ χ)
      (linkCover p θ ∘ fun s => D₁ (k * s)) := by
    have := hd.comp_reparam χ.continuous
    have e : (linkCover p θ ∘ D) ∘ χ = linkCover p θ ∘ fun s => D₁ (k * s) :=
      funext fun s => by simp only [Function.comp_apply]; rw [hχ, hDχ]
    rwa [e] at this
  have h' : (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ (E ∘ χ) (fun s => D₁ (k * s)) f :=
    ⟨hE', hD₁c.comp (continuous_const_mul _), hD₁m.comp (strictMono_mul_left_of_pos hkpos), hd',
      fun s => by simp only; rw [mul_add, mul_one, hD₁k]⟩
  obtain ⟨pr, hprc, hpr⟩ := exists_kfold_map hE' hE₁ k
  have hmor : (letI := cs; letI := cs₁; IsGXMorphism (GammaP p) (Link p) pr) := by
    letI := cs
    letI := cs₁
    refine ⟨hprc, fun y => ?_⟩
    obtain ⟨s, rfl⟩ := hE'.surjective y
    obtain ⟨A, hA⟩ := hd' s
    obtain ⟨A₁, hA₁⟩ := hd₁ (k * s)
    have hA₁' : ∀ᶠ s' in 𝓝 s, linkCover p θ (D₁ (k * s')) =
        A₁ • chartAt (Link p) (E₁ (k * s)) (E₁ (k * s')) :=
      ((continuous_const_mul (k : ℝ)).tendsto s).eventually hA₁
    refine ⟨A₁⁻¹ * A, hE'.eventually_of_eventually ?_⟩
    filter_upwards [hA, hA₁'] with s' h1 h2
    rw [hpr, hpr, mul_smul]
    change linkCover p θ (D₁ (k * s')) = _ at h1
    rw [← h1, h2, inv_smul_smul]
  obtain ⟨φ⟩ := hL
  obtain ⟨φ₁⟩ := hL₁
  haveI : CompactSpace L := φ.symm.compactSpace
  haveI : T2Space L := φ.isEmbedding.t2Space
  haveI : T2Space L₁ := φ₁.isEmbedding.t2Space
  have hlh : IsLocalHomeomorph pr := by
    letI := cs
    letI := cs₁
    exact hmor.isLocalHomeomorph
  have hcov : IsCoveringMap pr := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    exact IsCoveringMapOn.of_openPartialHomeomorph hprc fun e _ => by
      obtain ⟨ψ, he, hψ⟩ := hlh e
      exact ⟨ψ, he, hψ.symm⟩
  exact ⟨pr, E ∘ χ, h', hpr, hcov, card_fiber_of_kfold hE' hE₁ hk hpr, hmor⟩

end Cover

/-! ## 4. `bbsrem:degk` and `bbsrem:case_tachyons_see_remark`, the link half -/

/-- **A singularity of degree `2k` is the `k`-fold cover of one of degree `2`** (l.1334–1335,
l.1467–1468; the link half): every `(Γ_p, ℓ(p))`-circle at a space-like or light-like `p` with
lifted holonomy `δ^{2k} g`, `g` with a fixed point, `k ≥ 1`, is the `k`-fold cover of the
`(Γ_p, ℓ(p))`-circle `ℝ/⟨δ² g₁⟩` (developed by `linkCover`), where `g₁` lifts a `k`-th root in `Γ_p`
of the holonomy and `g₁ᵏ = g`. -/
theorem GammaLinkCircle.IsLiftedDev.exists_degree_two_cover {L : Type*} [TopologicalSpace L]
    {C : GammaLinkCircle L} {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : C.IsLiftedDev θ E D f) (hp : 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄)) {k : ℕ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ (2 * k : ℤ) * g) :
    ∃ (L₁ : Type) (_ : TopologicalSpace L₁) (cs₁ : ChartedSpace (Link C.pt) L₁)
      (hcs₁ : HasGroupoid L₁ (gxGroupoid (GammaP C.pt) (Link C.pt))) (hL₁ : IsCircle L₁)
      (E₁ : ℝ → L₁) (D₁ : ℝ → ℝ) (g₁ : GTilde) (pr : L → L₁) (E' : ℝ → L),
      (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsLiftedDev θ E₁ D₁ (GTilde.delta ^ (2 : ℤ) * g₁) ∧
      (∃ x, g₁ x = x) ∧ g₁ ^ k = g ∧
      C.IsLiftedDev θ E' (fun s => D₁ (k * s)) f ∧ (∀ s, pr (E' s) = E₁ (k * s)) ∧
      IsCoveringMap pr ∧ (∀ y, Nat.card (pr ⁻¹' {y}) = k) ∧
      (letI := C.atlas; letI := cs₁; IsGXMorphism (GammaP C.pt) (Link C.pt) pr) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨ρ, hρf⟩ := h.exists_linkCover_apply
  have hgρ : ∀ t, linkCover C.pt θ (g t) = ρ • linkCover C.pt θ t := fun t => by
    rw [← hρf, hfg, GTilde.coe_mul_apply, GTilde.delta_zpow_apply,
      show ((2 * k : ℤ) : ℝ) = 2 * ((k : ℤ) : ℝ) by push_cast; ring, linkCover_add_two_mul]
  obtain ⟨ρ', g₁, -, hg₁ρ, hg₁fix, hg₁k⟩ := exists_root_lift hp θ hgρ hg hk0
  obtain ⟨L₁, _, cs₁, hcs₁, hL₁, E₁, D₁, h₁⟩ := exists_isLiftedDev_delta_sq_mul C.pt θ hg₁ρ hg₁fix
  have hlt : ∀ x, x < (GTilde.delta ^ (2 : ℤ) * g₁) x := fun x => by
    have := GTilde.sub_one_lt_apply_of_fixed hg₁fix x
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; linarith
  have hf : f = (GTilde.delta ^ (2 : ℤ) * g₁) ^ k := by
    rw [hfg, GTilde.delta_sq_mul_pow, hg₁k]
  obtain ⟨pr, E', h', hpr, hcov, hcard, hmor⟩ :=
    GammaLinkCircle.IsLiftedDev.exists_kfold_cover (p := C.pt) (cs := C.atlas)
      (hcs := C.hasGroupoid) (hL := C.isCircle) h h₁ hlt hk0 hf
  exact ⟨L₁, inferInstance, cs₁, hcs₁, hL₁, E₁, D₁, g₁, pr, E', h₁, hg₁fix, hg₁k, h', hpr, hcov,
    hcard, hmor⟩

/-- **The `k`-fold cover of a singularity of degree `2` has degree `2k`** (l.1334–1335, the
construction): for a `(Γ_p, ℓ(p))`-circle `L₁` with lifted holonomy `δ² g₁`, `g₁` with a fixed
point, and `k ≥ 1`, the quotient `ℝ/⟨(δ² g₁)ᵏ⟩` is a `(Γ_p, ℓ(p))`-circle of lifted holonomy
`δ^{2k} g₁ᵏ` (`g₁ᵏ` with a fixed point: degree `2k`), the `k`-fold cover of `L₁`. -/
theorem GammaLinkCircle.IsLiftedDev.exists_kfold_cover_of_degree_two {L₁ : Type*}
    [TopologicalSpace L₁] {C₁ : GammaLinkCircle L₁} {θ : TpHS C₁.pt ≃ₗ[ℝ] ℂ} {E₁ : ℝ → L₁}
    {D₁ : ℝ → ℝ} {g₁ : GTilde} (h₁ : C₁.IsLiftedDev θ E₁ D₁ (GTilde.delta ^ (2 : ℤ) * g₁))
    (hg₁ : ∃ x, g₁ x = x) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link C₁.pt) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP C₁.pt) (Link C₁.pt))) (hL : IsCircle L)
      (E : ℝ → L) (pr : L → L₁),
      (GammaLinkCircle.mk C₁.pt cs hcs hL).IsLiftedDev θ E (fun s => D₁ (k * s))
        (GTilde.delta ^ (2 * k : ℤ) * g₁ ^ k) ∧ (∃ x, (g₁ ^ k) x = x) ∧
      (∀ s, pr (E s) = E₁ (k * s)) ∧ IsCoveringMap pr ∧ (∀ y, Nat.card (pr ⁻¹' {y}) = k) ∧
      (letI := cs; letI := C₁.atlas; IsGXMorphism (GammaP C₁.pt) (Link C₁.pt) pr) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨ρ₁, hρ₁⟩ := h₁.exists_linkCover_apply
  have hlt : ∀ x, x < (GTilde.delta ^ (2 : ℤ) * g₁) x := fun x => by
    have := GTilde.sub_one_lt_apply_of_fixed hg₁ x
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; linarith
  have hltk := lt_pow_apply_of_forall_lt hlt hk0
  have hpow : ∀ m : ℕ, ∀ t, linkCover C₁.pt θ (((GTilde.delta ^ (2 : ℤ) * g₁) ^ m) t) =
      (ρ₁ ^ m) • linkCover C₁.pt θ t := by
    intro m
    induction m with
    | zero => intro t; rw [pow_zero, pow_zero, GTilde.one_apply, one_smul]
    | succ m ih => intro t; rw [GTilde.pow_succ_apply, ih, hρ₁, pow_succ, mul_smul]
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient_of_forall_lt C₁.pt
      (isCoveringMap_linkCover C₁.pt θ).isLocalHomeomorph hltk (hpow k)
  have h : (GammaLinkCircle.mk C₁.pt cs hcs hL).IsLiftedDev θ E ψ
      ((GTilde.delta ^ (2 : ℤ) * g₁) ^ k) := ⟨hE, hψc, hψm, hdev, hψf⟩
  obtain ⟨pr, E', h', hpr, hcov, hcard, hmor⟩ :=
    GammaLinkCircle.IsLiftedDev.exists_kfold_cover (p := C₁.pt) (cs₁ := C₁.atlas)
      (hcs₁ := C₁.hasGroupoid) (hL₁ := C₁.isCircle) h h₁ hlt hk0 rfl
  obtain ⟨x, hx⟩ := hg₁
  refine ⟨L, inferInstance, cs, hcs, hL, E', pr, ?_, ⟨x, GTilde.pow_apply_of_fixed hx k⟩, hpr,
    hcov, hcard, hmor⟩
  rw [← GTilde.delta_sq_mul_pow]
  exact h'

theorem GTilde.conj_apply_le_self {f : GTilde} (hf : ∀ y, f y ≤ y) (h : GTilde) (x : ℝ) :
    (h * f * h⁻¹) x ≤ x := by
  rw [GTilde.coe_mul_apply, GTilde.coe_mul_apply]
  have := (GTilde.strictMono h).monotone (hf (h⁻¹ x))
  rwa [GTilde.apply_inv_apply] at this

/-- At `p ∈ dS²`, a lift with a fixed point of an element of `Γ_p` is hyperbolic iff it is not
`1`. -/
theorem isHyperbolic_iff_ne_one_of_lift {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter)
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {ρ : GammaP p} {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = ρ • linkCover p θ t) (hfix : ∃ x, g x = x) :
    GTilde.IsHyperbolic g ↔ g ≠ 1 := by
  refine ⟨fun hh h1 => hh.toPSL_ne_one (by rw [h1, map_one]), fun h1 => ?_⟩
  exact isHyperbolic_of_linkCover hp hg fun h2 => h1 ((GTilde.toPSL_eq_one_iff_of_fixed hfix).1 h2)

/-- At a light-like `p`, a lift with a fixed point of an element of `Γ_p` is parabolic iff it is
not `1`. -/
theorem isParabolic_iff_ne_one_of_lift {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) = 0)
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {ρ : GammaP p} {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = ρ • linkCover p θ t) (hfix : ∃ x, g x = x) :
    GTilde.IsParabolic g ↔ g ≠ 1 := by
  have e := toPSL_eq_of_linkCover hg
  rw [GTilde.IsParabolic, e, GammaP.isParabolic_iff_of_null hp θ ρ, ne_eq, ne_eq,
    ← GTilde.toPSL_eq_one_iff_of_fixed hfix, e, GammaP.pslMk_gammaToSL_eq_one_iff_of_null hp θ ρ]

/-- `g ≠ 1` iff `gᵏ ≠ 1`, `k ≥ 1`. -/
theorem GTilde.ne_one_iff_pow_ne_one {g : GTilde} {k : ℕ} (hk : k ≠ 0) : g ≠ 1 ↔ g ^ k ≠ 1 :=
  ⟨fun h1 h2 => h1 (GTilde.eq_one_of_pow_eq_one hk h2), fun h1 h2 => h1 (by rw [h2, one_pow])⟩

/-- **« with its sign kept »**: a `(Γ_p, ℓ(p))`-circle with the lifted developing pair
`(E, D₁(k ·))` of lifted holonomy `δ^{2k} g₁ᵏ` and one with `(E₁, D₁)` of lifted holonomy `δ² g₁`
(the two circles of `…exists_degree_two_cover` and `…exists_kfold_cover_of_degree_two`), `θ`
oriented, are positive (negative) together, space-like and light-like. -/
theorem GammaLinkCircle.IsLiftedDev.kfold_sign {L L₁ : Type*} [TopologicalSpace L]
    [TopologicalSpace L₁] {p : HS 2} {cs : ChartedSpace (Link p) L}
    {hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))} {hL : IsCircle L}
    {cs₁ : ChartedSpace (Link p) L₁} {hcs₁ : HasGroupoid L₁ (gxGroupoid (GammaP p) (Link p))}
    {hL₁ : IsCircle L₁} {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ) {E : ℝ → L}
    {E₁ : ℝ → L₁} {D₁ : ℝ → ℝ} {g₁ : GTilde} {k : ℕ} (hk : 1 ≤ k) (hg₁ : ∃ x, g₁ x = x)
    (h : (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E (fun s => D₁ (k * s))
      (GTilde.delta ^ (2 * k : ℤ) * g₁ ^ k))
    (h₁ : (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLiftedDev θ E₁ D₁
      (GTilde.delta ^ (2 : ℤ) * g₁)) :
    ((GammaLinkCircle.mk p cs hcs hL).IsSpacelikePositive ↔
        (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsSpacelikePositive) ∧
      ((GammaLinkCircle.mk p cs hcs hL).IsSpacelikeNegative ↔
        (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsSpacelikeNegative) ∧
      ((GammaLinkCircle.mk p cs hcs hL).IsLightlikePositive ↔
        (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLightlikePositive) ∧
      ((GammaLinkCircle.mk p cs hcs hL).IsLightlikeNegative ↔
        (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLightlikeNegative) := by
  have hk0 : k ≠ 0 := by omega
  have hk2 : (1 : ℤ) ≤ 2 * k := by omega
  have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  obtain ⟨x₁, hx₁⟩ := hg₁
  have hg₁k : ∃ x, (g₁ ^ k) x = x := ⟨x₁, GTilde.pow_apply_of_fixed hx₁ k⟩
  have hg₁' : ∃ x, g₁ x = x := ⟨x₁, hx₁⟩
  -- the lifts of the holonomies
  obtain ⟨ρ₁, hρ₁⟩ := h₁.exists_linkCover_apply
  have hg₁ρ : ∀ t, linkCover p θ (g₁ t) = ρ₁ • linkCover p θ t := fun t => by
    rw [← hρ₁, GTilde.coe_mul_apply, GTilde.delta_zpow_apply,
      show ((2 : ℤ) : ℝ) = 2 * ((1 : ℤ) : ℝ) by norm_num, linkCover_add_two_mul]
  have hgkρ : ∀ t, linkCover p θ ((g₁ ^ k) t) = (ρ₁ ^ k) • linkCover p θ t := by
    have : ∀ m : ℕ, ∀ t, linkCover p θ ((g₁ ^ m) t) = (ρ₁ ^ m) • linkCover p θ t := by
      intro m
      induction m with
      | zero => intro t; rw [pow_zero, pow_zero, GTilde.one_apply, one_smul]
      | succ m ih => intro t; rw [GTilde.pow_succ_apply, ih, hg₁ρ, pow_succ, mul_smul]
    exact this k
  -- the future time-like directions correspond
  have hiff : ∀ s, E s ∈ (GammaLinkCircle.mk p cs hcs hL).iPlusL ↔
      E₁ (k * s) ∈ (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).iPlusL := fun s => by
    have a := Set.ext_iff.1 h.2.2.2.1.preimage_iPlus s
    have b := Set.ext_iff.1 h₁.2.2.2.1.preimage_iPlus (k * s)
    simp only [mem_preimage, Function.comp_apply] at a b
    rw [← a, ← b]
  have hdiv : ∀ u : ℝ, (k : ℝ) * (u / k) = u := fun u => mul_div_cancel₀ u hkpos
  -- `g₁ᵏ ≠ 1` and `g₁ ≠ 1` from any witness of the other circle
  have hne₁ : ∀ {θ₀ : TpHS p ≃ₗ[ℝ] ℂ} {E₀ : ℝ → L₁} {D₀ : ℝ → ℝ} {f₀ g₀ : GTilde} {k₀ : ℤ},
      IsOrientedTangent p θ₀ → (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLiftedDev θ₀ E₀ D₀ f₀ →
      (∃ x, g₀ x = x) → f₀ = GTilde.delta ^ k₀ * g₀ → g₀ ≠ 1 → g₁ ≠ 1 := by
    intro θ₀ E₀ D₀ f₀ g₀ k₀ hθ₀ h₀ hg₀ hfg₀ hg₀1 hg1
    obtain ⟨ψ, κ, -, -, hf⟩ := GammaLinkCircle.IsLiftedDev.relate
      (C := GammaLinkCircle.mk p cs₁ hcs₁ hL₁) (θ := θ₀) (θ' := θ) hθ₀ hθ h₀ h₁
    have hgg := GTilde.conj_factor hg₀ hg₁' hfg₀ rfl hf
    apply hg₀1
    have : κ * g₀ * κ⁻¹ = 1 := by rw [← hgg, hg1]
    calc g₀ = κ⁻¹ * (κ * g₀ * κ⁻¹) * κ := by group
      _ = 1 := by rw [this]; group
  have hne : ∀ {θ₀ : TpHS p ≃ₗ[ℝ] ℂ} {E₀ : ℝ → L} {D₀ : ℝ → ℝ} {f₀ g₀ : GTilde} {k₀ : ℤ},
      IsOrientedTangent p θ₀ → (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ₀ E₀ D₀ f₀ →
      (∃ x, g₀ x = x) → f₀ = GTilde.delta ^ k₀ * g₀ → g₀ ≠ 1 → g₁ ^ k ≠ 1 := by
    intro θ₀ E₀ D₀ f₀ g₀ k₀ hθ₀ h₀ hg₀ hfg₀ hg₀1 hg1
    obtain ⟨ψ, κ, -, -, hf⟩ := GammaLinkCircle.IsLiftedDev.relate
      (C := GammaLinkCircle.mk p cs hcs hL) (θ := θ₀) (θ' := θ) hθ₀ hθ h₀ h
    have hgg := GTilde.conj_factor hg₀ hg₁k hfg₀ rfl hf
    apply hg₀1
    have : κ * g₀ * κ⁻¹ = 1 := by rw [← hgg, hg1]
    calc g₀ = κ⁻¹ * (κ * g₀ * κ⁻¹) * κ := by group
      _ = 1 := by rw [this]; group
  -- the relation of two witnesses: `g₁ᵏ` or `g₁` is a conjugate
  have hconj : ∀ {θ₀ : TpHS p ≃ₗ[ℝ] ℂ} {E₀ : ℝ → L} {D₀ : ℝ → ℝ} {f₀ g₀ : GTilde} {k₀ : ℤ},
      IsOrientedTangent p θ₀ → (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ₀ E₀ D₀ f₀ →
      (∃ x, g₀ x = x) → f₀ = GTilde.delta ^ k₀ * g₀ → ∃ κ, g₁ ^ k = κ * g₀ * κ⁻¹ := by
    intro θ₀ E₀ D₀ f₀ g₀ k₀ hθ₀ h₀ hg₀ hfg₀
    obtain ⟨ψ, κ, -, -, hf⟩ := GammaLinkCircle.IsLiftedDev.relate
      (C := GammaLinkCircle.mk p cs hcs hL) (θ := θ₀) (θ' := θ) hθ₀ hθ h₀ h
    exact ⟨κ, GTilde.conj_factor hg₀ hg₁k hfg₀ rfl hf⟩
  have hconj₁ : ∀ {θ₀ : TpHS p ≃ₗ[ℝ] ℂ} {E₀ : ℝ → L₁} {D₀ : ℝ → ℝ} {f₀ g₀ : GTilde} {k₀ : ℤ},
      IsOrientedTangent p θ₀ → (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).IsLiftedDev θ₀ E₀ D₀ f₀ →
      (∃ x, g₀ x = x) → f₀ = GTilde.delta ^ k₀ * g₀ → ∃ κ, g₁ = κ * g₀ * κ⁻¹ := by
    intro θ₀ E₀ D₀ f₀ g₀ k₀ hθ₀ h₀ hg₀ hfg₀
    obtain ⟨ψ, κ, -, -, hf⟩ := GammaLinkCircle.IsLiftedDev.relate
      (C := GammaLinkCircle.mk p cs₁ hcs₁ hL₁) (θ := θ₀) (θ' := θ) hθ₀ hθ h₀ h₁
    exact ⟨κ, GTilde.conj_factor hg₀ hg₁' hfg₀ rfl hf⟩
  refine ⟨⟨fun hC => ?_, fun hC => ?_⟩, ⟨fun hC => ?_, fun hC => ?_⟩, ⟨fun hC => ?_, fun hC => ?_⟩,
    ⟨fun hC => ?_, fun hC => ?_⟩⟩
  · -- space-like positive, `L ⇒ L₁`
    have hpos := hC.forall hθ h hg₁k rfl
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, -⟩ := hC
    have hg1 : g₁ ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).2
      (hne hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.toPSL_ne_one (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E₁, D₁, _, 2, g₁, h₁, by norm_num, hg₁', (isHyperbolic_iff_ne_one_of_lift hp
      hg₁ρ hg₁').2 hg1, rfl, fun u hu => ?_⟩
    have := hpos (u / k) ((hiff (u / k)).2 (by rw [hdiv]; exact hu))
    simp only [hdiv] at this
    exact (GTilde.le_apply_iff_le_pow_apply g₁ hk0 _).2 this
  · -- space-like positive, `L₁ ⇒ L`
    have hpos := hC.forall hθ h₁ hg₁' rfl
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, -⟩ := hC
    have hg1 : g₁ ^ k ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).1
      (hne₁ hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.toPSL_ne_one (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E, _, _, (2 * k : ℤ), g₁ ^ k, h, hk2, hg₁k,
      (isHyperbolic_iff_ne_one_of_lift hp hgkρ hg₁k).2 hg1, rfl, fun s hs => ?_⟩
    exact (GTilde.le_apply_iff_le_pow_apply g₁ hk0 _).1 (hpos (k * s) ((hiff s).1 hs))
  · -- space-like negative, `L ⇒ L₁`
    have hneg := hC.forall hθ h hg₁k rfl
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, -⟩ := hC
    have hg1 : g₁ ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).2
      (hne hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.toPSL_ne_one (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E₁, D₁, _, 2, g₁, h₁, by norm_num, hg₁', (isHyperbolic_iff_ne_one_of_lift hp
      hg₁ρ hg₁').2 hg1, rfl, fun u hu => ?_⟩
    have := hneg (u / k) ((hiff (u / k)).2 (by rw [hdiv]; exact hu))
    simp only [hdiv] at this
    exact (GTilde.apply_le_iff_pow_apply_le g₁ hk0 _).2 this
  · -- space-like negative, `L₁ ⇒ L`
    have hneg := hC.forall hθ h₁ hg₁' rfl
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, -⟩ := hC
    have hg1 : g₁ ^ k ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).1
      (hne₁ hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.toPSL_ne_one (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E, _, _, (2 * k : ℤ), g₁ ^ k, h, hk2, hg₁k,
      (isHyperbolic_iff_ne_one_of_lift hp hgkρ hg₁k).2 hg1, rfl, fun s hs => ?_⟩
    exact (GTilde.apply_le_iff_pow_apply_le g₁ hk0 _).1 (hneg (k * s) ((hiff s).1 hs))
  · -- light-like positive, `L ⇒ L₁`
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, hle⟩ := hC
    obtain ⟨κ, hκ⟩ := hconj hθ₀ h₀ hg₀ hfg₀
    have hg1 : g₁ ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).2
      (hne hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.2 (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E₁, D₁, _, 2, g₁, h₁, by norm_num, hg₁',
      (isParabolic_iff_ne_one_of_lift hp hg₁ρ hg₁').2 hg1, rfl, fun x => ?_⟩
    exact (GTilde.le_apply_iff_le_pow_apply g₁ hk0 x).2
      (by rw [hκ]; exact GTilde.le_conj_apply hle κ x)
  · -- light-like positive, `L₁ ⇒ L`
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, hle⟩ := hC
    obtain ⟨κ, hκ⟩ := hconj₁ hθ₀ h₀ hg₀ hfg₀
    have hg1 : g₁ ^ k ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).1
      (hne₁ hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.2 (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E, _, _, (2 * k : ℤ), g₁ ^ k, h, hk2, hg₁k,
      (isParabolic_iff_ne_one_of_lift hp hgkρ hg₁k).2 hg1, rfl, fun x => ?_⟩
    exact (GTilde.le_apply_iff_le_pow_apply g₁ hk0 x).1
      (by rw [hκ]; exact GTilde.le_conj_apply hle κ x)
  · -- light-like negative, `L ⇒ L₁`
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, hle⟩ := hC
    obtain ⟨κ, hκ⟩ := hconj hθ₀ h₀ hg₀ hfg₀
    have hg1 : g₁ ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).2
      (hne hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.2 (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E₁, D₁, _, 2, g₁, h₁, by norm_num, hg₁',
      (isParabolic_iff_ne_one_of_lift hp hg₁ρ hg₁').2 hg1, rfl, fun x => ?_⟩
    exact (GTilde.apply_le_iff_pow_apply_le g₁ hk0 x).2
      (by rw [hκ]; exact GTilde.conj_apply_le_self hle κ x)
  · -- light-like negative, `L₁ ⇒ L`
    obtain ⟨hp, θ₀, hθ₀, E₀, D₀, f₀, k₀, g₀, h₀, -, hg₀, hh₀, hfg₀, hle⟩ := hC
    obtain ⟨κ, hκ⟩ := hconj₁ hθ₀ h₀ hg₀ hfg₀
    have hg1 : g₁ ^ k ≠ 1 := (GTilde.ne_one_iff_pow_ne_one hk0).1
      (hne₁ hθ₀ h₀ hg₀ hfg₀ fun h1 => hh₀.2 (by rw [h1, map_one]))
    refine ⟨hp, θ, hθ, E, _, _, (2 * k : ℤ), g₁ ^ k, h, hk2, hg₁k,
      (isParabolic_iff_ne_one_of_lift hp hgkρ hg₁k).2 hg1, rfl, fun x => ?_⟩
    exact (GTilde.apply_le_iff_pow_apply_le g₁ hk0 x).1
      (by rw [hκ]; exact GTilde.conj_apply_le_self hle κ x)

/-! ### The type is kept, and singularities of every degree `2k` exist -/

/-- Lifts of powers: `gᵐ` lifts `ρᵐ`. -/
theorem linkCover_pow_apply {p : HS 2} {θ : TpHS p ≃ₗ[ℝ] ℂ} {ρ : GammaP p} {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = ρ • linkCover p θ t) (m : ℕ) (t : ℝ) :
    linkCover p θ ((g ^ m) t) = (ρ ^ m) • linkCover p θ t := by
  induction m generalizing t with
  | zero => rw [pow_zero, pow_zero, GTilde.one_apply, one_smul]
  | succ m ih => rw [GTilde.pow_succ_apply, ih, hg, pow_succ, mul_smul]

/-- **The type is kept** at `p ∈ dS²`: `gᵏ` is hyperbolic iff `g` is. -/
theorem isHyperbolic_pow_iff {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {θ : TpHS p ≃ₗ[ℝ] ℂ}
    {ρ : GammaP p} {g : GTilde} (hg : ∀ t, linkCover p θ (g t) = ρ • linkCover p θ t)
    (hfix : ∃ x, g x = x) {k : ℕ} (hk : k ≠ 0) :
    GTilde.IsHyperbolic (g ^ k) ↔ GTilde.IsHyperbolic g := by
  obtain ⟨x, hx⟩ := hfix
  rw [isHyperbolic_iff_ne_one_of_lift hp (linkCover_pow_apply hg k)
    ⟨x, GTilde.pow_apply_of_fixed hx k⟩, isHyperbolic_iff_ne_one_of_lift hp hg ⟨x, hx⟩]
  exact (GTilde.ne_one_iff_pow_ne_one hk).symm

/-- **The type is kept** at a light-like `p`: `gᵏ` is parabolic iff `g` is. -/
theorem isParabolic_pow_iff {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) = 0)
    {θ : TpHS p ≃ₗ[ℝ] ℂ} {ρ : GammaP p} {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = ρ • linkCover p θ t) (hfix : ∃ x, g x = x) {k : ℕ}
    (hk : k ≠ 0) : GTilde.IsParabolic (g ^ k) ↔ GTilde.IsParabolic g := by
  obtain ⟨x, hx⟩ := hfix
  rw [isParabolic_iff_ne_one_of_lift hp (linkCover_pow_apply hg k)
    ⟨x, GTilde.pow_apply_of_fixed hx k⟩, isParabolic_iff_ne_one_of_lift hp hg ⟨x, hx⟩]
  exact (GTilde.ne_one_iff_pow_ne_one hk).symm

/-- At a non-time-like `p`, every element of `Γ_p` has a lift with a fixed point. -/
theorem exists_lift_fixed {p : HS 2} (hp : 0 ≤ Causal.Flat.minkQ (p : 𝕄)) (θ : TpHS p ≃ₗ[ℝ] ℂ)
    (A : GammaP p) : ∃ g : GTilde, (∀ t, linkCover p θ (g t) = A • linkCover p θ t) ∧
      ∃ x, g x = x := by
  obtain ⟨σ₀, hσ₀⟩ := exists_dir_fixed_gammaP hp
  obtain ⟨F, hF⟩ := exists_rayLift p (θ := θ) (θ' := θ) (g₀ := 1)
    (fun σ => (one_smul _ _).symm) A
  obtain ⟨t₀, ht₀⟩ := linkCover_surjective p θ σ₀
  obtain ⟨n, hn⟩ := (linkCover_eq_linkCover_iff p θ).1
    (show linkCover p θ t₀ = linkCover p θ (F t₀) by rw [hF, ht₀, hσ₀])
  have happ : ∀ t, (GTilde.delta ^ (-(2 * n)) * F) t = F t + 2 * ((-n : ℤ) : ℝ) := fun t => by
    rw [GTilde.coe_mul_apply, GTilde.delta_zpow_apply]; push_cast; ring
  refine ⟨GTilde.delta ^ (-(2 * n)) * F, fun t => ?_, t₀, ?_⟩
  · rw [happ, linkCover_add_two_mul, hF]
  · rw [happ, hn]; push_cast; ring

/-- The degree-`2k` cover of `ℝ/⟨δ² g⟩`, with the sign of `g` on the time-like directions. -/
theorem exists_kfold_signed {p : HS 2} {θ : TpHS p ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent p θ)
    {k : ℕ} (hk : 1 ≤ k) {A : GammaP p} {g : GTilde}
    (hg : ∀ t, linkCover p θ (g t) = A • linkCover p θ t) (hfix : ∃ x, g x = x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L) (E : ℝ → L)
      (D : ℝ → ℝ), (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E D
        (GTilde.delta ^ (2 * k : ℤ) * g ^ k) ∧
      (p ∈ HS.piece 2 .deSitter → GTilde.IsHyperbolic g →
        ((∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → t < g t) →
          (GammaLinkCircle.mk p cs hcs hL).IsSpacelikePositive) ∧
        ((∀ t, linkCover p θ t ∈ dsFutureDirs p ∪ dsPastDirs p → g t < t) →
          (GammaLinkCircle.mk p cs hcs hL).IsSpacelikeNegative)) ∧
      (Causal.Flat.minkQ (p : 𝕄) = 0 → GTilde.IsParabolic g →
        ((∀ x, x ≤ g x) → (GammaLinkCircle.mk p cs hcs hL).IsLightlikePositive) ∧
        ((∀ x, g x ≤ x) → (GammaLinkCircle.mk p cs hcs hL).IsLightlikeNegative)) := by
  obtain ⟨L₁, _, cs₁, hcs₁, hL₁, E₁, D₁, h₁⟩ := exists_isLiftedDev_delta_sq_mul p θ hg hfix
  obtain ⟨L, _, cs, hcs, hL, E, pr, h, -, -, -, -, -⟩ :=
    GammaLinkCircle.IsLiftedDev.exists_kfold_cover_of_degree_two (C₁ := GammaLinkCircle.mk p cs₁
      hcs₁ hL₁) h₁ hfix hk
  have hsign := GammaLinkCircle.IsLiftedDev.kfold_sign hθ hk hfix h h₁
  refine ⟨L, inferInstance, cs, hcs, hL, E, _, h, fun hp hh => ⟨fun hT => ?_, fun hT => ?_⟩,
    fun hp hpar => ⟨fun hle => ?_, fun hge => ?_⟩⟩
  · exact hsign.1.2 ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, by norm_num, hfix, hh, rfl,
      fun s hs => (hT _ (Or.inl (h₁.mem_dsFutureDirs hp hs))).le⟩
  · exact hsign.2.1.2 ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, by norm_num, hfix, hh, rfl,
      fun s hs => (hT _ (Or.inl (h₁.mem_dsFutureDirs hp hs))).le⟩
  · exact hsign.2.2.1.2 ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, by norm_num, hfix, hpar, rfl, hle⟩
  · exact hsign.2.2.2.2 ⟨hp, θ, hθ, E₁, D₁, _, 2, g, h₁, by norm_num, hfix, hpar, rfl, hge⟩

/-- **Space-like singularities of every degree `2k`, positive and negative, exist**
(`bbsrem:degk`, « can be constructed », l.1334): at every `p ∈ dS²` and for every `k ≥ 1` there are
a positive and a negative space-like `(Γ_p, ℓ(p))`-circle of degree `2k` (lifted holonomy
`δ^{2k} g`, `g` hyperbolic with a fixed point, `θ` oriented); by
`GX.GammaLinkCircle.IsLiftedDev.exists_degree_two_cover` each is the `k`-fold cover of one of
degree `2`, of the same sign by `GX.GammaLinkCircle.IsLiftedDev.kfold_sign`. -/
theorem exists_spacelike_degree_two_mul {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) {k : ℕ}
    (hk : 1 ≤ k) :
    (∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
        (E : ℝ → L) (D : ℝ → ℝ) (g : GTilde), C.pt = p ∧ IsOrientedTangent C.pt θ ∧
        C.IsLiftedDev θ E D (GTilde.delta ^ (2 * k : ℤ) * g) ∧ (∃ x, g x = x) ∧
        GTilde.IsHyperbolic g ∧ C.IsSpacelikePositive) ∧
      (∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
        (E : ℝ → L) (D : ℝ → ℝ) (g : GTilde), C.pt = p ∧ IsOrientedTangent C.pt θ ∧
        C.IsLiftedDev θ E D (GTilde.delta ^ (2 * k : ℤ) * g) ∧ (∃ x, g x = x) ∧
        GTilde.IsHyperbolic g ∧ C.IsSpacelikeNegative) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  obtain ⟨A, g, hA1, hg, hfix, hh⟩ := exists_gammaP_lift_fixed hp θ
  have hgi : ∀ t, linkCover p θ (g⁻¹ t) = A⁻¹ • linkCover p θ t := fun t => by
    rw [eq_inv_smul_iff, ← hg, GTilde.apply_inv_apply]
  have hfixi : ∃ x, g⁻¹ x = x := by
    obtain ⟨x, hx⟩ := hfix
    exact ⟨x, by have := GTilde.inv_apply_apply g x; rwa [hx] at this⟩
  have hhi : GTilde.IsHyperbolic g⁻¹ := isHyperbolic_of_linkCover hp hgi (by
    rw [map_inv]; exact inv_ne_one.2 hh.toPSL_ne_one)
  have hfk : ∀ {g' : GTilde}, (∃ x, g' x = x) → ∃ x, (g' ^ k) x = x := fun ⟨x, hx⟩ =>
    ⟨x, GTilde.pow_apply_of_fixed hx k⟩
  obtain ⟨L, _, cs, hcs, hL, E, D, h, hs, -⟩ := exists_kfold_signed hθ hk hg hfix
  obtain ⟨L', _, cs', hcs', hL', E', D', h', hs', -⟩ := exists_kfold_signed hθ hk hgi hfixi
  have hhk := (isHyperbolic_pow_iff hp hg hfix hk0).2 hh
  have hhik := (isHyperbolic_pow_iff hp hgi hfixi hk0).2 hhi
  rcases timelike_spacelike_dir hp hA1 hg hfix with ⟨hT, -⟩ | ⟨hT, -⟩
  · refine ⟨⟨L, inferInstance, GammaLinkCircle.mk p cs hcs hL, θ, E, D, g ^ k, rfl, hθ, h, hfk hfix,
      hhk, (hs hp hh).1 hT⟩, ⟨L', inferInstance, GammaLinkCircle.mk p cs' hcs' hL', θ, E', D',
      g⁻¹ ^ k, rfl, hθ, h', hfk hfixi, hhik, (hs' hp hhi).2 fun t ht => ?_⟩⟩
    have := GTilde.strictMono g⁻¹ (hT t ht)
    rwa [GTilde.inv_apply_apply] at this
  · refine ⟨⟨L', inferInstance, GammaLinkCircle.mk p cs' hcs' hL', θ, E', D', g⁻¹ ^ k, rfl, hθ, h',
      hfk hfixi, hhik, (hs' hp hhi).1 fun t ht => ?_⟩, ⟨L, inferInstance,
      GammaLinkCircle.mk p cs hcs hL, θ, E, D, g ^ k, rfl, hθ, h, hfk hfix, hhk, (hs hp hh).2 hT⟩⟩
    have := GTilde.strictMono g⁻¹ (hT t ht)
    rwa [GTilde.inv_apply_apply] at this

/-- **Light-like singularities of every degree `2k`, positive and negative, exist**
(`bbsrem:case_tachyons_see_remark`, « one can construct light-like singularities of any degree
`2k` », l.1467–1468): at every light-like `p` and for every `k ≥ 1` there are a positive and a
negative light-like `(Γ_p, ℓ(p))`-circle of degree `2k` (lifted holonomy `δ^{2k} g`, `g` parabolic
with a fixed point, `θ` oriented); each is the `k`-fold cover of one of degree `2`
(`GX.GammaLinkCircle.IsLiftedDev.exists_degree_two_cover`), of the same sign. -/
theorem exists_lightlike_degree_two_mul {p : HS 2} (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {k : ℕ}
    (hk : 1 ≤ k) :
    (∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
        (E : ℝ → L) (D : ℝ → ℝ) (g : GTilde), C.pt = p ∧ IsOrientedTangent C.pt θ ∧
        C.IsLiftedDev θ E D (GTilde.delta ^ (2 * k : ℤ) * g) ∧ (∃ x, g x = x) ∧
        GTilde.IsParabolic g ∧ C.IsLightlikePositive) ∧
      (∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L) (θ : TpHS C.pt ≃ₗ[ℝ] ℂ)
        (E : ℝ → L) (D : ℝ → ℝ) (g : GTilde), C.pt = p ∧ IsOrientedTangent C.pt θ ∧
        C.IsLiftedDev θ E D (GTilde.delta ^ (2 * k : ℤ) * g) ∧ (∃ x, g x = x) ∧
        GTilde.IsParabolic g ∧ C.IsLightlikeNegative) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  set A := GammaP.nullBoost hp 1
  have hA1 : A ≠ 1 := fun h1 => by
    have h := congrArg (fun B : GammaP p => ((B : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)) h1
    exact Causal.Flat.nullRot_ne_one hp (GammaP.nullFrame hp).1 (GammaP.nullFrame hp).2
      (raySphere_ne_zero p) one_ne_zero h
  obtain ⟨g, hg, hfix⟩ := exists_lift_fixed hp.symm.le θ A
  have hg1 : g ≠ 1 := fun h1 => hA1 ((GammaP.pslMk_gammaToSL_eq_one_iff_of_null hp θ A).1 (by
    rw [← toPSL_eq_of_linkCover hg, h1, map_one]))
  have hpar : GTilde.IsParabolic g := (isParabolic_iff_ne_one_of_lift hp hg hfix).2 hg1
  have hgi : ∀ t, linkCover p θ (g⁻¹ t) = A⁻¹ • linkCover p θ t := fun t => by
    rw [eq_inv_smul_iff, ← hg, GTilde.apply_inv_apply]
  have hfixi : ∃ x, g⁻¹ x = x := by
    obtain ⟨x, hx⟩ := hfix
    exact ⟨x, by have := GTilde.inv_apply_apply g x; rwa [hx] at this⟩
  have hpari : GTilde.IsParabolic g⁻¹ :=
    (isParabolic_iff_ne_one_of_lift hp hgi hfixi).2 (inv_ne_one.2 hg1)
  have hfk : ∀ {g' : GTilde}, (∃ x, g' x = x) → ∃ x, (g' ^ k) x = x := fun ⟨x, hx⟩ =>
    ⟨x, GTilde.pow_apply_of_fixed hx k⟩
  obtain ⟨L, _, cs, hcs, hL, E, D, h, -, hs⟩ := exists_kfold_signed hθ hk hg hfix
  obtain ⟨L', _, cs', hcs', hL', E', D', h', -, hs'⟩ := exists_kfold_signed hθ hk hgi hfixi
  have hpk := (isParabolic_pow_iff hp hg hfix hk0).2 hpar
  have hpik := (isParabolic_pow_iff hp hgi hfixi hk0).2 hpari
  rcases (hpar.le_or_ge hfix).1 with hle | hge
  · refine ⟨⟨L, inferInstance, GammaLinkCircle.mk p cs hcs hL, θ, E, D, g ^ k, rfl, hθ, h, hfk hfix,
      hpk, (hs hp hpar).1 hle⟩, ⟨L', inferInstance, GammaLinkCircle.mk p cs' hcs' hL', θ, E', D',
      g⁻¹ ^ k, rfl, hθ, h', hfk hfixi, hpik, (hs' hp hpari).2 fun x => ?_⟩⟩
    have := hle (g⁻¹ x)
    rwa [GTilde.apply_inv_apply] at this
  · refine ⟨⟨L', inferInstance, GammaLinkCircle.mk p cs' hcs' hL', θ, E', D', g⁻¹ ^ k, rfl, hθ, h',
      hfk hfixi, hpik, (hs' hp hpari).1 fun x => ?_⟩, ⟨L, inferInstance,
      GammaLinkCircle.mk p cs hcs hL, θ, E, D, g ^ k, rfl, hθ, h, hfk hfix, hpk,
      (hs hp hpar).2 hge⟩⟩
    have := hge (g⁻¹ x)
    rwa [GTilde.apply_inv_apply] at this

/-- **The `k`-fold cover of the regular link** (built; `GX.regular_not_isHyperbolic` argues it):
at every `p` and for every `k ≥ 1` the `k`-fold cover of `ℓ(p)` is a `(Γ_p, ℓ(p))`-circle of
lifted holonomy `δ^{2k}` (trivial `Γ_p`-holonomy), neither hyperbolic nor parabolic: a degree-`2k`
link which is the `k`-fold cover of a regular point's link (that it is the cover of no singular
one is argued, not stated). -/
theorem exists_kfold_cover_regular (p : HS 2) (θ : TpHS p ≃ₗ[ℝ] ℂ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L) (E : ℝ → L)
      (D : ℝ → ℝ) (pr : L → Link p),
      (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E D (GTilde.delta ^ (2 * k : ℤ)) ∧
      IsCoveringMap pr ∧ (∀ y, Nat.card (pr ⁻¹' {y}) = k) ∧
      (letI := cs; IsGXMorphism (GammaP p) (Link p) pr) ∧
      ¬ GTilde.IsHyperbolic (GTilde.delta ^ (2 * k : ℤ)) ∧
      ¬ GTilde.IsParabolic (GTilde.delta ^ (2 * k : ℤ)) := by
  obtain ⟨E₁, D₁, h₁, -⟩ := regular_not_isHyperbolic (p := p) θ
  have h₁' : (GammaLinkCircle.regular p).IsLiftedDev θ E₁ D₁ (GTilde.delta ^ (2 : ℤ) * 1) := by
    rw [mul_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
    exact h₁
  obtain ⟨L, _, cs, hcs, hL, E, pr, h, -, -, hcov, hcard, hmor⟩ :=
    GammaLinkCircle.IsLiftedDev.exists_kfold_cover_of_degree_two
      (C₁ := GammaLinkCircle.regular p) h₁' ⟨0, rfl⟩ hk
  rw [one_pow, mul_one] at h
  have h1 : GTilde.toPSL (GTilde.delta ^ (2 * k : ℤ)) = 1 := by
    rw [map_zpow, GTilde.toPSL_delta, one_zpow]
  refine ⟨L, inferInstance, cs, hcs, hL, E, _, pr, h, hcov, hcard, hmor, fun hh => ?_,
    fun hh => hh.2 h1⟩
  have : (4 : ℝ) < PSL2.trSq (GTilde.toPSL (GTilde.delta ^ (2 * k : ℤ))) := hh
  rw [h1, PSL2.trSq_one] at this
  exact lt_irrefl _ this

/-! ## 5. The HS half: `𝔢` of the `k`-fold cover is a `k`-branched cover at the apices -/

namespace BiSusp

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]

/-- `[σ, t] ↦ [pr σ, t]`. -/
def map (pr : S → T) : BiSusp S → BiSusp T :=
  lift (fun σ t => mk (pr σ) (projIcc 0 Real.pi Real.pi_pos.le t))
    (fun _ _ => mk_eq_mk.2 (Or.inr (Or.inl ⟨by simp [projIcc_left], by simp [projIcc_left]⟩)))
    (fun _ _ => mk_eq_mk.2 (Or.inr (Or.inr ⟨by simp [projIcc_right], by simp [projIcc_right]⟩)))

theorem map_mk (pr : S → T) (σ : S) (t : Icc (0 : ℝ) Real.pi) :
    map pr (mk σ t) = mk (pr σ) t := by
  rw [map, lift_mk, projIcc_val]

theorem ht_map (pr : S → T) (x : BiSusp S) : ht (map pr x) = ht x := by
  obtain ⟨σ, t, rfl⟩ := mk_surjective x
  rw [map_mk, ht_mk, ht_mk]

theorem map_mem_poles_iff (pr : S → T) (x : BiSusp S) : map pr x ∈ poles T ↔ x ∈ poles S := by
  simp only [poles, mem_setOf_eq, ht_map]

theorem continuous_map {pr : S → T} (hπ : Continuous pr) : Continuous (map pr) :=
  continuous_lift _ _ (continuous_mk'.comp ((hπ.comp continuous_fst).prodMk
    (continuous_projIcc.comp (continuous_subtype_val.comp continuous_snd))))

/-- `(σ, t) ↦ [σ, t]` on `S × ℝ`, through `projIcc`. -/
theorem continuous_mk_projIcc :
    Continuous fun q : S × ℝ => mk q.1 (projIcc 0 Real.pi Real.pi_pos.le q.2) :=
  continuous_mk'.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))

/-- The neighbourhoods `{t < ε}` of the apex `p̄` are preconnected. -/
theorem isPreconnected_ht_lt [PreconnectedSpace S] (ε : ℝ) :
    IsPreconnected {z : BiSusp S | ht z < ε} := by
  have e : {z : BiSusp S | ht z < ε} = (fun q : S × ℝ => mk q.1 (projIcc 0 Real.pi
      Real.pi_pos.le q.2)) '' (univ ×ˢ (Icc 0 Real.pi ∩ Iio ε)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨σ, t, rfl⟩ := mk_surjective z
      exact ⟨(σ, t), ⟨trivial, t.2, hz⟩, by simp only [projIcc_val]⟩
    · rintro ⟨⟨σ, t⟩, ⟨-, ht, htε⟩, rfl⟩
      show ((projIcc 0 Real.pi Real.pi_pos.le t : Icc (0 : ℝ) Real.pi) : ℝ) < ε
      rw [projIcc_of_mem _ ht]
      exact htε
  rw [e]
  exact (isPreconnected_univ.prod
    ((convex_Icc 0 Real.pi).inter (convex_Iio ε)).isPreconnected).image
    _ continuous_mk_projIcc.continuousOn

/-- The neighbourhoods `{t > π − ε}` of the apex `−p̄` are preconnected. -/
theorem isPreconnected_ht_gt [PreconnectedSpace S] (ε : ℝ) :
    IsPreconnected {z : BiSusp S | Real.pi - ε < ht z} := by
  have e : {z : BiSusp S | Real.pi - ε < ht z} = (fun q : S × ℝ => mk q.1 (projIcc 0 Real.pi
      Real.pi_pos.le q.2)) '' (univ ×ˢ (Icc 0 Real.pi ∩ Ioi (Real.pi - ε))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨σ, t, rfl⟩ := mk_surjective z
      exact ⟨(σ, t), ⟨trivial, t.2, hz⟩, by simp only [projIcc_val]⟩
    · rintro ⟨⟨σ, t⟩, ⟨-, ht, htε⟩, rfl⟩
      show Real.pi - ε < ((projIcc 0 Real.pi Real.pi_pos.le t : Icc (0 : ℝ) Real.pi) : ℝ)
      rw [projIcc_of_mem _ ht]
      exact htε
  rw [e]
  exact (isPreconnected_univ.prod
    ((convex_Icc 0 Real.pi).inter (convex_Ioi _)).isPreconnected).image
    _ continuous_mk_projIcc.continuousOn

/-- Every neighbourhood of an apex contains a neighbourhood `{t < ε}` or `{t > π − ε}` (`S`
compact: the tube lemma). -/
theorem exists_ht_subset [CompactSpace S] {O : Set (BiSusp S)} (hO : IsOpen O) {x : BiSusp S}
    (hxO : x ∈ O) {t₀ : Icc (0 : ℝ) Real.pi} (hx : ht x = t₀)
    (ht₀ : (t₀ : ℝ) = 0 ∨ (t₀ : ℝ) = Real.pi) :
    ∃ ε > 0, ∀ y, |ht y - t₀| < ε → y ∈ O := by
  have hall : ∀ σ : S, (σ, t₀) ∈ (mk' : S × Icc (0 : ℝ) Real.pi → BiSusp S) ⁻¹' O := fun σ => by
    obtain ⟨σ₀, t₁, rfl⟩ := mk_surjective x
    rw [ht_mk] at hx
    have : mk σ t₀ = mk σ₀ t₁ := mk_eq_mk.2 (by
      rcases ht₀ with h | h
      · exact Or.inr (Or.inl ⟨h, hx.trans h⟩)
      · exact Or.inr (Or.inr ⟨h, hx.trans h⟩))
    show mk σ t₀ ∈ O
    rw [this]
    exact hxO
  obtain ⟨u, v, -, hv, hsu, h0v, huv⟩ := generalized_tube_lemma isCompact_univ
    (isCompact_singleton (x := t₀)) (hO.preimage continuous_mk') (by
      rintro ⟨σ, t⟩ ⟨-, ht⟩
      rw [mem_singleton_iff] at ht
      subst ht
      exact hall σ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hv _ (h0v rfl)
  refine ⟨ε, hε, fun y hy => ?_⟩
  obtain ⟨σ, t, rfl⟩ := mk_surjective y
  rw [ht_mk] at hy
  exact huv ⟨hsu (mem_univ σ),
    hball (by rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]; exact hy)⟩

end BiSusp

/-- **A topological surface is locally path-connected**: its charts into `ℝ²`. -/
theorem IsTopologicalSurface.locPathConnectedSpace {M : Type*} [TopologicalSpace M]
    (h : IsTopologicalSurface M) : LocPathConnectedSpace M := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) M :=
    { atlas := range fun x => (h.exists_chart x).choose
      chartAt := fun x => (h.exists_chart x).choose
      mem_chart_source := fun x => (h.exists_chart x).choose_spec
      chart_mem_atlas := fun x => ⟨x, rfl⟩ }
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) M

/-- **An HS-morphism** of singular HS-structures: a continuous map matching the singular sets,
which reads, in the charts of the two HS-structures, near every regular point, as an element of
`SO₀(1,2)` (the morphism form of `GX.SingularHSStructure.IsIso`). -/
def SingularHSStructure.IsMorphism {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (A : SingularHSStructure M) (B : SingularHSStructure N) (F : M → N) : Prop :=
  Continuous F ∧ (∀ x, F x ∈ B.sing ↔ x ∈ A.sing) ∧
    ∀ x, x ∉ A.sing → ∀ e ∈ A.atlas, x ∈ e.source → ∀ e' ∈ B.atlas, F x ∈ e'.source →
      ∃ g : Causal.Flat.lorentz 2, ∀ᶠ y in 𝓝 x, e' (F y) = g • e y

/-- **An HS-morphism is a local homeomorphism off the singular set.** -/
theorem SingularHSStructure.IsMorphism.isLocalHomeomorphOn {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] {A : SingularHSStructure M} {B : SingularHSStructure N} {F : M → N}
    (hF : A.IsMorphism B F) : IsLocalHomeomorphOn F A.singᶜ := by
  refine IsLocalHomeomorphOn.mk F _ fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := A.exists_chart hx
  have hFx : F x ∉ B.sing := fun h => hx ((hF.2.1 x).1 h)
  obtain ⟨e', he', hxe'⟩ := B.exists_chart hFx
  obtain ⟨g, hg⟩ := hF.2.2 x hx e he hxe e' he' hxe'
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ F y ∈ e'.source ∧ e' (F y) = g • e y :=
    (show ∀ᶠ y in 𝓝 x, y ∈ e.source from e.open_source.mem_nhds hxe).and
      ((hF.1.continuousAt.eventually (e'.open_source.mem_nhds hxe')).and hg)
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 hev
  refine ⟨((e.transHomeomorph (Homeomorph.smul g)).trans e'.symm).restrOpen O hOo, ?_,
    fun y hy => ?_⟩
  · show (x ∈ e.source ∧ g • e x ∈ e'.target) ∧ x ∈ O
    refine ⟨⟨hxe, ?_⟩, hxO⟩
    rw [← (hO hxO).2.2]
    exact e'.map_source (hO hxO).2.1
  · have hyO : y ∈ O := hy.2
    show F y = e'.symm (g • e y)
    rw [← (hO hyO).2.2, e'.left_inv (hO hyO).2.1]

/-- **Two periodic coverings of the same space** differ by a homeomorphism `ψ` of `ℝ` with
`ψ (s + 1) = ψ s ± 1`. -/
theorem IsPeriodicCover.exists_rel {L : Type*} [TopologicalSpace L] {E E' : ℝ → L}
    (hE : IsPeriodicCover E) (hE' : IsPeriodicCover E') :
    ∃ (ψ : ℝ ≃ₜ ℝ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (∀ s, ψ (s + 1) = ψ s + ε) ∧
      ∀ s, E' s = E (ψ s) := by
  obtain ⟨e₀, he₀⟩ := hE.surjective (E' 0)
  obtain ⟨ψ, ⟨-, hψ0⟩, -⟩ := hE.isCoveringMap.existsUnique_continuousMap_lifts
    ⟨E', hE'.isCoveringMap.continuous⟩ 0 e₀ he₀
  have hψ : ∀ s, E (ψ s) = E' s := fun s => congrFun hψ0 s
  obtain ⟨ε, hε⟩ := hE.fiber (ψ 0) (ψ (0 + 1)) (by rw [hψ, hψ, hE'.add_one])
  have hψ1 : ∀ s, ψ (s + 1) = ψ s + ε := fun s => congrFun
    (hE.isCoveringMap.eq_of_comp_eq (g₁ := fun s => ψ (s + 1)) (g₂ := fun s => ψ s + ε)
      (ψ.continuous.comp (continuous_add_const 1)) (ψ.continuous.add continuous_const)
      (funext fun s => by
        simp only [Function.comp_apply]
        rw [hψ, hE.add_int, hψ, hE'.add_one]) 0 hε) s
  have hψl : IsLocalHomeomorph ψ := IsLocalHomeomorph.of_comp (by
      have : E ∘ ψ = E' := funext hψ
      rw [this]
      exact hE'.isCoveringMap.isLocalHomeomorph) hE.isCoveringMap.isLocalHomeomorph ψ.continuous
  have hinj := injective_of_isOpenMap_real ψ.continuous hψl.isOpenMap
  have hψn := add_int_of_add_one hψ1
  have hε1 : ε = 1 ∨ ε = -1 := by
    have hε0 : ε ≠ 0 := fun h0 => by
      have := hψ1 0
      rw [h0, Int.cast_zero, add_zero, zero_add] at this
      exact one_ne_zero (hinj this)
    by_contra hne
    push Not at hne
    have h01 : ψ 1 = ψ 0 + ε := by simpa using hψ1 0
    obtain ⟨t, ht, η, hη, hψt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, ∃ η : ℤ, (η = 1 ∨ η = -1) ∧
        ψ t = ψ 0 + η := by
      rcases lt_or_gt_of_ne hε0 with hneg | hpos
      · have h2 : (ε : ℝ) ≤ -2 := by exact_mod_cast (show ε ≤ -2 by omega)
        obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc' zero_le_one ψ.continuous.continuousOn
          (show ψ 0 + ((-1 : ℤ) : ℝ) ∈ Icc (ψ 1) (ψ 0) from ⟨by push_cast; linarith, by
            push_cast; linarith⟩)
        exact ⟨t, ht, -1, Or.inr rfl, hψt⟩
      · have h2 : (2 : ℝ) ≤ ε := by exact_mod_cast (show 2 ≤ ε by omega)
        obtain ⟨t, ht, hψt⟩ := intermediate_value_Icc zero_le_one ψ.continuous.continuousOn
          (show ψ 0 + ((1 : ℤ) : ℝ) ∈ Icc (ψ 0) (ψ 1) from ⟨by push_cast; linarith, by
            push_cast; linarith⟩)
        exact ⟨t, ht, 1, Or.inl rfl, hψt⟩
    have hEt : E' 0 = E' t := by rw [← hψ, ← hψ, hψt, hE.add_int]
    obtain ⟨m, hm⟩ := hE'.fiber 0 t hEt
    rw [zero_add] at hm
    have hm0 : (0 : ℝ) ≤ m := hm ▸ ht.1
    have hm1 : (m : ℝ) ≤ 1 := hm ▸ ht.2
    have hm0' : (0 : ℤ) ≤ m := by exact_mod_cast hm0
    have hm1' : m ≤ (1 : ℤ) := by exact_mod_cast hm1
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · rw [hm, Int.cast_zero] at hψt
      have : (η : ℝ) = 0 := by linarith
      rcases hη with rfl | rfl <;> norm_num at this
    · rw [hm, Int.cast_one, h01] at hψt
      have : (ε : ℝ) = η := by linarith
      have : ε = η := by exact_mod_cast this
      omega
  have hsurj : Function.Surjective ψ := by
    intro y
    rcases hε1 with rfl | rfl
    · set n := ⌊y - ψ 0⌋
      have h1 := Int.floor_le (y - ψ 0)
      have h2 := Int.lt_floor_add_one (y - ψ 0)
      have e1 := hψn n 0
      have e2 := hψn (n + 1) 0
      rw [zero_add] at e1 e2
      push_cast at e1 e2
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc (show (n : ℝ) ≤ n + 1 by linarith)
        ψ.continuous.continuousOn (show y ∈ Icc (ψ n) (ψ (n + 1)) from
          ⟨by rw [e1]; linarith, by rw [e2]; linarith⟩)
      exact ⟨t, ht⟩
    · set n := ⌊y - ψ 0⌋
      have h1 := Int.floor_le (y - ψ 0)
      have h2 := Int.lt_floor_add_one (y - ψ 0)
      have e1 := hψn (-n) 0
      have e2 := hψn (-n - 1) 0
      rw [zero_add] at e1 e2
      push_cast at e1 e2
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (show (-n - 1 : ℝ) ≤ -n by linarith)
        ψ.continuous.continuousOn (show y ∈ Icc (ψ (-n)) (ψ (-n - 1)) from
          ⟨by rw [e1]; linarith, by rw [e2]; linarith⟩)
      exact ⟨t, ht⟩
  exact ⟨(Equiv.ofBijective ψ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen ψ.continuous
    hψl.isOpenMap, ε, hε1, hψ1, fun s => (hψ s).symm⟩

section Susp

/-- The near-apex sets `{|t − t₀| < ε}`, `t₀ ∈ {0, π}`, are preconnected. -/
theorem BiSusp.isPreconnected_ht_near {S : Type*} [TopologicalSpace S] [PreconnectedSpace S]
    {t₀ : ℝ} (ht₀ : t₀ = 0 ∨ t₀ = Real.pi) (ε : ℝ) :
    IsPreconnected {z : BiSusp S | |ht z - t₀| < ε} := by
  rcases ht₀ with rfl | rfl
  · convert BiSusp.isPreconnected_ht_lt (S := S) ε using 1
    ext z
    have := ht_mem z
    simp only [mem_setOf_eq, sub_zero, abs_of_nonneg this.1]
  · convert BiSusp.isPreconnected_ht_gt (S := S) ε using 1
    ext z
    have := ht_mem z
    simp only [mem_setOf_eq, abs_sub_lt_iff]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; constructor <;> linarith [this.2]

/-- The regular part `𝔢(L) ∖ {p̄, −p̄}` is portly. -/
theorem BiSusp.isPortly_compl_poles {S : Type*} [TopologicalSpace S] (φ : S ≃ₜ Circle) :
    IsPortly (BiSusp.poles S)ᶜ := by
  haveI : Nonempty S := ⟨φ.symm 1⟩
  haveI : LocPathConnectedSpace (BiSusp S) :=
    (BiSusp.isTopologicalSurface φ).locPathConnectedSpace
  set h := BiSusp.homeomorphSph2 φ
  have e : (BiSusp.poles S)ᶜ = h ⁻¹' ({h (BiSusp.north S)}ᶜ ∩ {h (BiSusp.south S)}ᶜ) := by
    rw [BiSusp.poles_eq]
    ext x
    simp [h.injective.eq_iff]
  rw [e]
  exact ((isPortly_compl_singleton_sph2 _).inter
    (isPortly_compl_singleton_sph2 _)).preimage_of_isLocalHomeomorph h.isLocalHomeomorph

/-- **`𝔢` of a `k`-sheeted covering of circles is a `k`-branched cover at the apices**: for a
`k`-sheeted covering `pr : L → L₁` of circles, `BiSusp.map pr` is, if it is a local homeomorphism
off the apices, a branched covering in gx's sense, possibly branched over the two apices,
`k`-to-one off them and one-to-one over each. -/
theorem isBranchedCovering_susp_map {L L₁ : Type*} [TopologicalSpace L] [TopologicalSpace L₁]
    (hL : IsCircle L) (hL₁ : IsCircle L₁) {pr : L → L₁} (hprc : Continuous pr)
    (hsurj : Function.Surjective pr) {k : ℕ} (hk : k ≠ 0)
    (hcard : ∀ y, Nat.card (pr ⁻¹' {y}) = k)
    (hlh : IsLocalHomeomorphOn (BiSusp.map pr) (BiSusp.poles L)ᶜ) :
    IsBranchedCovering (BiSusp.map pr) ∧
      IsPossiblyBranchedOver (BiSusp.map pr) (BiSusp.poles L₁) ∧
      (∀ y ∉ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = k) ∧
      (∀ y ∈ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = 1) := by
  obtain ⟨φ⟩ := hL
  obtain ⟨φ₁⟩ := hL₁
  haveI : CompactSpace L := φ.symm.compactSpace
  haveI : CompactSpace L₁ := φ₁.symm.compactSpace
  haveI : ConnectedSpace L := φ.symm.surjective.connectedSpace φ.symm.continuous
  haveI : ConnectedSpace L₁ := φ₁.symm.surjective.connectedSpace φ₁.symm.continuous
  haveI : Nonempty L := ⟨φ.symm 1⟩
  haveI : Nonempty L₁ := ⟨φ₁.symm 1⟩
  haveI : T2Space (BiSusp L) := BiSusp.t2Space_of_homeomorph φ
  haveI : T2Space (BiSusp L₁) := BiSusp.t2Space_of_homeomorph φ₁
  haveI : CompactSpace (BiSusp L) := (BiSusp.homeomorphSph2 φ).symm.compactSpace
  haveI : ConnectedSpace (BiSusp L) := (BiSusp.homeomorphSph2 φ).symm.surjective.connectedSpace
    (BiSusp.homeomorphSph2 φ).symm.continuous
  haveI : LocPathConnectedSpace (BiSusp L) :=
    (BiSusp.isTopologicalSurface φ).locPathConnectedSpace
  haveI : LocPathConnectedSpace (BiSusp L₁) :=
    (BiSusp.isTopologicalSurface φ₁).locPathConnectedSpace
  haveI : FirstCountableTopology (BiSusp L₁) :=
    (BiSusp.homeomorphSph2 φ₁).isInducing.firstCountableTopology
  set F := BiSusp.map pr with hF
  have hc : Continuous F := BiSusp.continuous_map hprc
  have hpoles : ∀ x, F x ∈ BiSusp.poles L₁ ↔ x ∈ BiSusp.poles L := BiSusp.map_mem_poles_iff pr
  -- the fibres
  have hfib_reg : ∀ y ∉ BiSusp.poles L₁, Nat.card (F ⁻¹' {y}) = k := by
    intro y hy
    obtain ⟨σ₁, t, rfl⟩ := BiSusp.mk_surjective y
    have ht := BiSusp.notMem_poles_iff.1 hy
    rw [BiSusp.ht_mk] at ht
    have hmem : ∀ σ : pr ⁻¹' {σ₁}, BiSusp.mk (σ : L) t ∈ F ⁻¹' {BiSusp.mk σ₁ t} := fun σ => by
      show F (BiSusp.mk (σ : L) t) = BiSusp.mk σ₁ t
      rw [hF, BiSusp.map_mk, show pr σ = σ₁ from σ.2]
    let e : pr ⁻¹' {σ₁} → F ⁻¹' {BiSusp.mk σ₁ t} := fun σ => ⟨_, hmem σ⟩
    have hinj : Function.Injective e := by
      intro σ σ' h
      have h' := congrArg Subtype.val h
      rcases BiSusp.mk_eq_mk.1 h' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Subtype.ext h1
      · exact absurd h1 ht.1.ne'
      · exact absurd h1 ht.2.ne
    have hsurj' : Function.Surjective e := by
      rintro ⟨z, hz⟩
      obtain ⟨σ, t', rfl⟩ := BiSusp.mk_surjective z
      have hz' : BiSusp.mk (pr σ) t' = BiSusp.mk σ₁ t := by
        rw [← BiSusp.map_mk]; exact hz
      rcases BiSusp.mk_eq_mk.1 hz' with ⟨h1, h2⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
      · exact ⟨⟨σ, h1⟩, Subtype.ext (show BiSusp.mk σ t = BiSusp.mk σ t' by rw [h2])⟩
      · exact absurd h1 ht.1.ne'
      · exact absurd h1 ht.2.ne
    rw [← hcard σ₁]
    exact Nat.card_congr (Equiv.ofBijective e ⟨hinj, hsurj'⟩).symm
  have hfib_pole : ∀ y ∈ BiSusp.poles L₁, Nat.card (F ⁻¹' {y}) = 1 := by
    intro y hy
    obtain ⟨σ₁, t, rfl⟩ := BiSusp.mk_surjective y
    have ht : (t : ℝ) = 0 ∨ (t : ℝ) = Real.pi := hy
    obtain ⟨σ, -⟩ := hsurj σ₁
    have key : F ⁻¹' {BiSusp.mk σ₁ t} = {BiSusp.mk σ t} := by
      ext z
      obtain ⟨σ', t', rfl⟩ := BiSusp.mk_surjective z
      simp only [mem_preimage, mem_singleton_iff, hF, BiSusp.map_mk, BiSusp.mk_eq_mk,
        Subtype.ext_iff]
      constructor
      · rintro (⟨-, h⟩ | h | h)
        · rcases ht with h0 | h0
          · exact Or.inr (Or.inl ⟨h.trans h0, h0⟩)
          · exact Or.inr (Or.inr ⟨h.trans h0, h0⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (⟨-, h⟩ | h | h)
        · rcases ht with h0 | h0
          · exact Or.inr (Or.inl ⟨h.trans h0, h0⟩)
          · exact Or.inr (Or.inr ⟨h.trans h0, h0⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    rw [key]
    exact Nat.card_unique
  -- covering off the apices
  have hpre : F ⁻¹' (BiSusp.poles L₁)ᶜ = (BiSusp.poles L)ᶜ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, hpoles]
  have hcovOn : IsCoveringMapOn F (BiSusp.poles L₁)ᶜ := by
    refine hc.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph (fun y hy => ?_) fun x hx => ?_
    · haveI := Nat.finite_of_card_ne_zero (by rw [hfib_reg y hy]; exact hk)
      exact Set.toFinite _
    · rw [hpre] at hx
      obtain ⟨ψ, hxψ, hψ⟩ := hlh x hx
      exact ⟨ψ, hxψ, hψ.symm⟩
  have hmaps : MapsTo F (BiSusp.poles L)ᶜ (BiSusp.poles L₁)ᶜ := fun x hx => by
    rwa [mem_compl_iff, hpoles]
  have hres : hmaps.restrict F _ _ = (BiSusp.poles L₁)ᶜ.restrictPreimage F ∘
      Homeomorph.setCongr hpre.symm := funext fun _ => rfl
  have hcov : IsCoveringMap (hmaps.restrict F _ _) := hres ▸
    (hcovOn.isCoveringMap_restrictPreimage).comp_homeomorph _
  have hsurjR : Function.Surjective (hmaps.restrict F _ _) := by
    rintro ⟨y, hy⟩
    obtain ⟨σ₁, t, rfl⟩ := BiSusp.mk_surjective y
    obtain ⟨σ, hσ⟩ := hsurj σ₁
    refine ⟨⟨BiSusp.mk σ t, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_compl_iff, ← hpoles, hF, BiSusp.map_mk, hσ]; exact hy
    · show F (BiSusp.mk σ t) = BiSusp.mk σ₁ t
      rw [hF, BiSusp.map_mk, hσ]
  -- `F` is open
  have hnear : ∀ (σ : L) (t : Icc (0 : ℝ) Real.pi), BiSusp.mk σ t ∈ BiSusp.poles L →
      ∀ O : Set (BiSusp L), IsOpen O → BiSusp.mk σ t ∈ O → ∃ ε > 0,
        {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} ⊆ F '' O ∧
          F ⁻¹' {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} ⊆ O := by
    intro σ t hx O hO hxO
    obtain ⟨ε, hε, hεO⟩ := BiSusp.exists_ht_subset hO hxO (BiSusp.ht_mk σ t) hx
    refine ⟨ε, hε, fun y hy => ?_, fun z hz => hεO z (by
      simpa only [mem_preimage, mem_setOf_eq, hF, BiSusp.ht_map] using hz)⟩
    obtain ⟨σ₁, t₁, rfl⟩ := BiSusp.mk_surjective y
    obtain ⟨σ', hσ'⟩ := hsurj σ₁
    have hy' : |BiSusp.ht (BiSusp.mk σ₁ t₁) - t| < ε := hy
    refine ⟨BiSusp.mk σ' t₁, hεO _ (by rw [BiSusp.ht_mk] at hy' ⊢; exact hy'), ?_⟩
    rw [hF, BiSusp.map_mk, hσ']
  have hopen_near : ∀ (t : ℝ) (ε : ℝ), IsOpen {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} :=
    fun t ε => isOpen_lt ((BiSusp.continuous_ht.sub continuous_const).abs) continuous_const
  have ho : IsOpenMap F := by
    intro O hO
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hxO, rfl⟩
    by_cases hx : x ∈ BiSusp.poles L
    · obtain ⟨σ, t, rfl⟩ := BiSusp.mk_surjective x
      obtain ⟨ε, hε, hεO, -⟩ := hnear σ t hx O hO hxO
      refine mem_of_superset ((hopen_near t ε).mem_nhds ?_) hεO
      show |BiSusp.ht (F (BiSusp.mk σ t)) - t| < ε
      rw [hF, BiSusp.ht_map, BiSusp.ht_mk, sub_self, abs_zero]
      exact hε
    · obtain ⟨e, hxe, hFe⟩ := hlh x hx
      refine mem_of_superset ((e.isOpen_image_source_inter hO).mem_nhds
        ⟨x, ⟨hxe, hxO⟩, by rw [hFe]⟩) ?_
      rintro _ ⟨z, ⟨-, hzO⟩, rfl⟩
      exact ⟨z, hzO, by rw [hFe]⟩
  -- `F` is a spread
  have hsp : IsSpread F := by
    refine isSpread_iff_of_locallyConnectedSpace.2 ⟨hc, fun x O hO hxO => ?_⟩
    by_cases hx : x ∈ BiSusp.poles L
    · obtain ⟨σ, t, rfl⟩ := BiSusp.mk_surjective x
      obtain ⟨ε, hε, -, hεO⟩ := hnear σ t hx O hO hxO
      refine ⟨_, hopen_near t ε, ?_, (connectedComponentIn_subset _ _).trans hεO⟩
      show |BiSusp.ht (F (BiSusp.mk σ t)) - t| < ε
      rw [hF, BiSusp.ht_map, BiSusp.ht_mk, sub_self, abs_zero]
      exact hε
    · exact exists_cc_subset_of_isEvenlyCovered ho
        (hcovOn (F x) (by rwa [mem_compl_iff, hpoles])) hO hxO
  have hX₁ := BiSusp.isPortly_compl_poles φ
  have hY₁ := BiSusp.isPortly_compl_poles φ₁
  obtain ⟨hY, -, -⟩ := spread_partial_covering hc hX₁ BiSusp.isClosed_poles.isOpen_compl hmaps
    hcov hsurjR
  -- `F` is complete
  have hcomp : IsCompleteSpread F := by
    rw [isCompleteSpread_iff]
    intro e
    by_cases he : e.base ∈ BiSusp.poles L₁
    · obtain ⟨σ₁, t, hb⟩ := BiSusp.mk_surjective e.base
      have ht : (t : ℝ) = 0 ∨ (t : ℝ) = Real.pi := by rw [← hb] at he; exact he
      obtain ⟨σ, hσ⟩ := hsurj σ₁
      refine ⟨BiSusp.mk σ t, fun U hU => ?_⟩
      obtain ⟨ε, hε, hεU⟩ :=
        BiSusp.exists_ht_subset hU.isOpen hU.mem (by rw [← hb, BiSusp.ht_mk]) ht
      have hV : IsCNbhd e.base {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} :=
        ⟨hopen_near t ε, BiSusp.isPreconnected_ht_near ht ε, by
          show |BiSusp.ht e.base - t| < ε
          rw [← hb, BiSusp.ht_mk, sub_self, abs_zero]; exact hε⟩
      have hpreV : IsPreconnected (F ⁻¹' {z : BiSusp L₁ | |BiSusp.ht z - t| < ε}) := by
        have : F ⁻¹' {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} =
            {z : BiSusp L | |BiSusp.ht z - t| < ε} := by
          ext z; simp only [mem_preimage, mem_setOf_eq, hF, BiSusp.ht_map]
        rw [this]
        exact BiSusp.isPreconnected_ht_near ht ε
      obtain ⟨x, hx, hxe⟩ := e.isCompOf _ hV
      have heV : e {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} =
          F ⁻¹' {z : BiSusp L₁ | |BiSusp.ht z - t| < ε} := by
        rw [hxe, hpreV.connectedComponentIn hx]
      refine e.mono _ U hV hU (fun z hz => hεU z hz) ?_
      rw [heV]
      show |BiSusp.ht (F (BiSusp.mk σ t)) - t| < ε
      rw [hF, BiSusp.ht_map, BiSusp.ht_mk, sub_self, abs_zero]
      exact hε
    · obtain ⟨U, hU, heU, -, hcov'⟩ := hY (show e.base ∈ (BiSusp.poles L₁)ᶜ from he)
      exact e.exists_mem_of_isEvenlyCoveredSet hU heU hcov'
  have hbc := ((complete_path_carac.{0} hsp hX₁ hY₁ hmaps hcov hsurjR).out 1 0).1 hcomp
  refine ⟨hbc, fun z hz => ?_, hfib_reg, hfib_pole⟩
  by_contra h0
  exact hz (hY h0)

/-- **The apices are branch points when `k ≥ 2`**: no neighbourhood of an apex of `𝔢(L₁)` is
evenly covered by `BiSusp.map pr` (one preimage over the apex, `k ≥ 2` over the points next to
it, all in one connected component). -/
theorem notMem_ordY_susp_map {L L₁ : Type*} [TopologicalSpace L] [TopologicalSpace L₁]
    (hL : IsCircle L) (hL₁ : IsCircle L₁) {pr : L → L₁} (hsurj : Function.Surjective pr)
    {k : ℕ} (hk : 2 ≤ k)
    (hfib : ∀ y ∉ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = k) :
    ∀ y ∈ BiSusp.poles L₁, y ∉ ordY (BiSusp.map pr) := by
  obtain ⟨φ⟩ := hL
  obtain ⟨φ₁⟩ := hL₁
  haveI : ConnectedSpace L := φ.symm.surjective.connectedSpace φ.symm.continuous
  haveI : CompactSpace L₁ := φ₁.symm.compactSpace
  intro y hy hord
  obtain ⟨U, hU, hyU, -, hev⟩ := hord
  obtain ⟨σ₁, t, rfl⟩ := BiSusp.mk_surjective y
  have ht : (t : ℝ) = 0 ∨ (t : ℝ) = Real.pi := hy
  obtain ⟨σ, hσ⟩ := hsurj σ₁
  have hx₀ : BiSusp.mk σ t ∈ BiSusp.map pr ⁻¹' U := by
    show BiSusp.map pr (BiSusp.mk σ t) ∈ U
    rw [BiSusp.map_mk, hσ]
    exact hyU
  obtain ⟨e, he⟩ := hev _ hx₀
  have hinj : InjOn (BiSusp.map pr) (connectedComponentIn (BiSusp.map pr ⁻¹' U) (BiSusp.mk σ t)) :=
    fun a ha b hb hab => by
      have : e ⟨a, ha⟩ = e ⟨b, hb⟩ := Subtype.ext (by rw [he, he]; exact hab)
      exact congrArg Subtype.val (e.injective this)
  obtain ⟨ε, hε, hεU⟩ := BiSusp.exists_ht_subset hU hyU (BiSusp.ht_mk σ₁ t) ht
  have hsub : {z : BiSusp L | |BiSusp.ht z - t| < ε} ⊆
      connectedComponentIn (BiSusp.map pr ⁻¹' U) (BiSusp.mk σ t) :=
    (BiSusp.isPreconnected_ht_near ht ε).subset_connectedComponentIn
      (by show |BiSusp.ht (BiSusp.mk σ t) - t| < ε; rw [BiSusp.ht_mk, sub_self, abs_zero]; exact hε)
      (fun z hz => hεU _ (by rw [BiSusp.ht_map]; exact hz))
  -- a regular point next to the apex
  set δ := min (ε / 2) (Real.pi / 2) with hδ_def
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδπ : δ < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  obtain ⟨t', ht'0, ht'π, ht'ε⟩ : ∃ t' : ℝ, 0 < t' ∧ t' < Real.pi ∧ |t' - t| < ε := by
    rcases ht with h0 | hπ
    · exact ⟨δ, hδ0, hδπ, by rw [h0, sub_zero, abs_of_pos hδ0]; exact hδε⟩
    · refine ⟨Real.pi - δ, by linarith, by linarith, ?_⟩
      rw [hπ, show Real.pi - δ - Real.pi = -δ by ring, abs_neg, abs_of_pos hδ0]
      exact hδε
  set y' := BiSusp.mk σ₁ (⟨t', ht'0.le, ht'π.le⟩ : Icc (0 : ℝ) Real.pi)
  have hy' : y' ∉ BiSusp.poles L₁ := BiSusp.notMem_poles_iff.2 (by
    rw [BiSusp.ht_mk]; exact ⟨ht'0, ht'π⟩)
  have hcard := hfib y' hy'
  haveI : Finite (BiSusp.map pr ⁻¹' {y'}) := Nat.finite_of_card_ne_zero (by omega)
  have h1 : 1 < Nat.card (BiSusp.map pr ⁻¹' {y'}) := by omega
  haveI := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne (BiSusp.map pr ⁻¹' {y'})
  have hht : ∀ z ∈ BiSusp.map pr ⁻¹' {y'}, z ∈ {z : BiSusp L | |BiSusp.ht z - t| < ε} := by
    intro z hz
    have : BiSusp.ht (BiSusp.map pr z) = t' := by
      rw [show BiSusp.map pr z = y' from hz, BiSusp.ht_mk]
    show |BiSusp.ht z - t| < ε
    rw [← BiSusp.ht_map pr, this]
    exact ht'ε
  exact hab (Subtype.ext (hinj (hsub (hht a ha)) (hsub (hht b hb))
    ((show BiSusp.map pr a = y' from ha).trans (show BiSusp.map pr b = y' from hb).symm)))

variable {p : HS 2} {L L₁ : Type*} [TopologicalSpace L] [TopologicalSpace L₁]
  {cs : ChartedSpace (Link p) L} {hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))}
  {hL : IsCircle L} {cs₁ : ChartedSpace (Link p) L₁}
  {hcs₁ : HasGroupoid L₁ (gxGroupoid (GammaP p) (Link p))} {hL₁ : IsCircle L₁}

/-- **The pulled-back developing data** along a `k`-fold `(Γ_p, ℓ(p))`-covering. -/
theorem GammaLinkCircle.DevData.exists_pullback {pr : L → L₁} {E : ℝ → L} {E₁ : ℝ → L₁}
    (hE : IsPeriodicCover E) (hE₁ : IsPeriodicCover E₁) {k : ℕ} (hk : k ≠ 0)
    (hπE : ∀ s, pr (E s) = E₁ (k * s))
    (hπm : letI := cs; letI := cs₁; IsGXMorphism (GammaP p) (Link p) pr)
    (Δ₁ : (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).DevData) :
    ∃ Δ : (GammaLinkCircle.mk p cs hcs hL).DevData,
      (∀ s, pr (Δ.E s) = Δ₁.E (k * s)) ∧ (∀ s, Δ.d s = Δ₁.d (k * s)) ∧ Δ.hol = Δ₁.hol ^ k ∧
      (∀ s, Δ.vlift s = Δ₁.vlift (k * s)) := by
  obtain ⟨ψ, ε, hε, hψ1, hψE⟩ := hE₁.exists_rel Δ₁.periodic
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hψk : ∀ u, ψ (u + k) = ψ u + ε * k := fun u => by
    have := add_int_of_add_one hψ1 (k : ℤ) u
    push_cast at this
    exact this
  set χ : ℝ ≃ₜ ℝ := ((Homeomorph.mulLeft₀ (k : ℝ) hk').trans ψ).trans
    (Homeomorph.mulLeft₀ ((k : ℝ)⁻¹) (inv_ne_zero hk'))
  have hχ : ∀ s, χ s = (k : ℝ)⁻¹ * ψ (k * s) := fun s => rfl
  have hχ1 : ∀ s, χ (s + 1) = χ s + ε := fun s => by
    rw [hχ, hχ, mul_add, mul_one, hψk]
    field_simp
  have hΔE : IsPeriodicCover (E ∘ χ) := hE.comp_homeomorph' χ hε hχ1
  have hprΔ : ∀ s, pr ((E ∘ χ) s) = Δ₁.E (k * s) := fun s => by
    simp only [Function.comp_apply]
    rw [hπE, hχ, ← mul_assoc, mul_inv_cancel₀ hk', one_mul, hψE]
  have hd₁n : ∀ (n : ℕ) u, Δ₁.d (u + n) = Δ₁.hol ^ n • Δ₁.d u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ m ih => intro u; rw [Nat.cast_succ, ← add_assoc, Δ₁.d_add_one, ih, pow_succ', mul_smul]
  have hdev : (GammaLinkCircle.mk p cs hcs hL).IsDevAlong (E ∘ χ) (fun s => Δ₁.d (k * s)) := by
    letI := cs
    letI := cs₁
    intro s
    obtain ⟨A₁, hA₁⟩ := Δ₁.dev (k * s)
    obtain ⟨g, hg⟩ := hπm.exists_smul_eq ((E ∘ χ) s)
    refine ⟨A₁ * g, ?_⟩
    have h1 : ∀ᶠ s' in 𝓝 s, Δ₁.d (k * s') =
        A₁ • chartAt (Link p) (Δ₁.E (k * s)) (Δ₁.E (k * s')) :=
      ((continuous_const_mul (k : ℝ)).tendsto s).eventually hA₁
    have h2 : ∀ᶠ s' in 𝓝 s, chartAt (Link p) (pr ((E ∘ χ) s)) (pr ((E ∘ χ) s')) =
        g • chartAt (Link p) ((E ∘ χ) s) ((E ∘ χ) s') :=
      hΔE.isCoveringMap.continuous.continuousAt.eventually hg
    filter_upwards [h1, h2] with s' e1 e2
    show Δ₁.d (k * s') = (A₁ * g) • chartAt (Link p) ((E ∘ χ) s) ((E ∘ χ) s')
    rw [e1, ← hprΔ, ← hprΔ, e2, mul_smul]
  refine ⟨{
    E := E ∘ χ
    periodic := hΔE
    d := fun s => Δ₁.d (k * s)
    dev := hdev
    hol := Δ₁.hol ^ k
    d_add_one := fun s => by simp only; rw [mul_add, mul_one, hd₁n]
    vlift := fun s => Δ₁.vlift (k * s)
    continuous_vlift := Δ₁.continuous_vlift.comp (continuous_const_mul _)
    tpMk_vlift_ne := fun s => Δ₁.tpMk_vlift_ne _
    dirOf_vlift := fun s => Δ₁.dirOf_vlift _
    vlift_add_one := fun s => by
      have := Δ₁.vlift_add_int (k : ℤ) (k * s)
      rw [Int.cast_natCast, zpow_natCast] at this
      simp only
      rw [mul_add, mul_one]
      exact this }, hprΔ, fun _ => rfl, rfl, fun _ => rfl⟩

/-- **`BiSusp.map pr` is an HS-morphism** `𝔢(L) → 𝔢(L₁)` for developing data related by `pr`. -/
theorem susp_map_isMorphism {pr : L → L₁} (hprc : Continuous pr) {k : ℕ}
    {Δ : (GammaLinkCircle.mk p cs hcs hL).DevData}
    {Δ₁ : (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).DevData}
    (hE : ∀ s, pr (Δ.E s) = Δ₁.E (k * s)) (hv : ∀ s, Δ.vlift s = Δ₁.vlift (k * s)) :
    Δ.suspStructure.IsMorphism Δ₁.suspStructure (BiSusp.map pr) := by
  refine ⟨BiSusp.continuous_map hprc, fun x => BiSusp.map_mem_poles_iff pr x, ?_⟩
  intro x _ e he hxe e' he' hxe'
  obtain ⟨c, W, hW, hl, rfl⟩ := he
  obtain ⟨c₁, W₁, hW₁, hl₁, rfl⟩ := he'
  obtain ⟨q, hq, rfl⟩ := hxe
  obtain ⟨q', hq', hqq'⟩ := hxe'
  have hmq : BiSusp.map pr (BiSusp.mk' q) = BiSusp.mk' (pr q.1, q.2) := BiSusp.map_mk pr q.1 q.2
  have hqe : q' = (pr q.1, q.2) :=
    BiSusp.mk'_injOn_regSet ⟨trivial, hq'.2⟩ ⟨trivial, hq.2⟩ (hqq'.trans hmq)
  have hc₁ : pr q.1 ∈ c₁.source := by
    have := hq'.1
    rwa [hqe] at this
  obtain ⟨s, hs, A, hA⟩ := hl q.1 hq.1
  obtain ⟨u, hu, A₁, hA₁⟩ := hl₁ (pr q.1) hc₁
  obtain ⟨n, hn⟩ := Δ₁.periodic.fiber (k * s) u (by rw [← hE, hs, hu])
  set G : GammaP p := A₁ * Δ₁.hol ^ n * A⁻¹ with hG
  have hev : ∀ᶠ s' in 𝓝 s, W₁ (pr (Δ.E s')) =
      ((G : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W (Δ.E s')) := by
    have ht : Tendsto (fun s' : ℝ => k * s' + (n : ℝ)) (𝓝 s) (𝓝 u) := by
      rw [hn]
      exact ((continuous_const_mul _).add continuous_const).tendsto s
    have hA₁' := ht.eventually hA₁
    filter_upwards [hA, hA₁'] with s' h1 h2
    rw [hE, show Δ₁.E (k * s') = Δ₁.E (k * s' + n) by rw [Δ₁.periodic.add_int], h2,
      Δ₁.vlift_add_int n, ← hv, h1, hG, gammaP_coe_mul_apply, gammaP_coe_mul_apply,
      gammaP_coe_inv_apply]
  have hevσ : ∀ᶠ σ' in 𝓝 q.1, W₁ (pr σ') =
      ((G : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W σ') := by
    rw [← hs]
    exact Δ.eventually_of_eventually_E hev
  refine ⟨(G : Causal.Flat.lorentz 2), ?_⟩
  rw [BiSusp.nhds_mk ⟨trivial, hq.2⟩, eventually_map]
  have hqc : ∀ᶠ q'' in 𝓝 q, q''.1 ∈ c.source :=
    continuous_fst.continuousAt.eventually (c.open_source.mem_nhds hq.1)
  have hσ' : ∀ᶠ q'' in 𝓝 q, W₁ (pr q''.1) =
      ((G : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (W q''.1) :=
    continuous_fst.continuousAt.eventually hevσ
  filter_upwards [hqc, hσ'] with q'' h1 h2
  show suspMap p W₁ (BiSusp.map pr (BiSusp.mk q''.1 q''.2)) =
    (G : Causal.Flat.lorentz 2) • suspMap p W (BiSusp.mk q''.1 q''.2)
  rw [BiSusp.map_mk, suspMap_mk, suspMap_mk, h2, smul_arcPt _ G (hW.tpMk_ne _ h1)]

/-- **`𝔢` of the `k`-fold cover is a `k`-branched cover of `𝔢(L₁)` at its apices** (l.1334–1335,
the HS half): for a `k`-sheeted covering `pr : L → L₁` which is a `(Γ_p, ℓ(p))`-morphism unwrapping
one turn of `L` onto `k` turns of `L₁`, and for every developing data `Δ₁` of `L₁`, the pulled-back
developing data `Δ` of `L` (`Δ.E` over `Δ₁.E(k ·)`, `d`, `w` read at `k s`, holonomy `Δ₁.holᵏ`)
make `BiSusp.map pr : 𝔢(L) → 𝔢(L₁)` an HS-morphism, a branched covering in gx's sense
(`GX.IsBranchedCovering`) possibly branched over the two apices only, and branched exactly there
when `k ≥ 2`, `k`-to-one off the apices and one-to-one over each apex. -/
theorem susp_kfold_branched_cover {pr : L → L₁} {E : ℝ → L} {E₁ : ℝ → L₁}
    (hE : IsPeriodicCover E) (hE₁ : IsPeriodicCover E₁) {k : ℕ} (hk : k ≠ 0)
    (hπE : ∀ s, pr (E s) = E₁ (k * s)) (hπc : IsCoveringMap pr)
    (hπk : ∀ y, Nat.card (pr ⁻¹' {y}) = k)
    (hπm : letI := cs; letI := cs₁; IsGXMorphism (GammaP p) (Link p) pr)
    (Δ₁ : (GammaLinkCircle.mk p cs₁ hcs₁ hL₁).DevData) :
    ∃ Δ : (GammaLinkCircle.mk p cs hcs hL).DevData,
      (∀ s, pr (Δ.E s) = Δ₁.E (k * s)) ∧ (∀ s, Δ.d s = Δ₁.d (k * s)) ∧ Δ.hol = Δ₁.hol ^ k ∧
      (∀ s, Δ.vlift s = Δ₁.vlift (k * s)) ∧
      Δ.suspStructure.IsMorphism Δ₁.suspStructure (BiSusp.map pr) ∧
      IsBranchedCovering (BiSusp.map pr) ∧
      IsPossiblyBranchedOver (BiSusp.map pr) (BiSusp.poles L₁) ∧
      (2 ≤ k → branchingLocus (BiSusp.map pr) = BiSusp.poles L₁) ∧
      (∀ y ∉ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = k) ∧
      (∀ y ∈ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = 1) := by
  obtain ⟨Δ, hΔE, hΔd, hΔh, hΔv⟩ := GammaLinkCircle.DevData.exists_pullback hE hE₁ hk hπE hπm Δ₁
  have hmor := susp_map_isMorphism hπc.continuous hΔE hΔv
  have hsurj : Function.Surjective pr := fun y => by
    obtain ⟨u, rfl⟩ := hE₁.surjective y
    exact ⟨E (u / k), by rw [hπE, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hk)]⟩
  obtain ⟨hbc, hpb, hfib, hfibp⟩ := isBranchedCovering_susp_map hL hL₁ hπc.continuous hsurj hk
    hπk hmor.isLocalHomeomorphOn
  exact ⟨Δ, hΔE, hΔd, hΔh, hΔv, hmor, hbc, hpb, fun h2 => subset_antisymm hpb
    (fun y hy => notMem_ordY_susp_map hL hL₁ hsurj h2 hfib y hy), hfib, hfibp⟩

/-- **`bbsrem:degk` and `bbsrem:case_tachyons_see_remark`, the link and HS halves, assembled**
(l.1334–1335, l.1467–1468): a space-like (`p ∈ dS²`) or light-like (`p ∈ ∂ℍ²±`)
`(Γ_p, ℓ(p))`-circle `L` of degree `2k`, `k ≥ 1` (lifted holonomy `δ^{2k} g`, `g` with a fixed
point, `θ` oriented), is the `k`-fold cover of a `(Γ_p, ℓ(p))`-circle `L₁` of degree `2`
(lifted holonomy `δ² g₁`, `g₁ᵏ = g`, `g₁` lifting a `k`-th root in `Γ_p` of the holonomy of `L`),
of the same type and the same sign; and for every developing data `Δ₁` of `L₁`, `𝔢(L)` with the
pulled-back developing data is a `k`-branched cover of `𝔢(L₁)` at its apices (an HS-morphism, a
branched covering in gx's sense possibly branched over the apices only, `k`-to-one off them,
one-to-one over each). -/
theorem bbsrem_degk_link_hs {L : Type*} [TopologicalSpace L] {C : GammaLinkCircle L}
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent C.pt θ) {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : C.IsLiftedDev θ E D f) (hp : 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄)) {k : ℕ} (hk : 1 ≤ k)
    {g : GTilde} (hg : ∃ x, g x = x) (hfg : f = GTilde.delta ^ (2 * k : ℤ) * g) :
    ∃ (L₁ : Type) (_ : TopologicalSpace L₁) (cs₁ : ChartedSpace (Link C.pt) L₁)
      (hcs₁ : HasGroupoid L₁ (gxGroupoid (GammaP C.pt) (Link C.pt))) (hL₁ : IsCircle L₁)
      (E₁ : ℝ → L₁) (D₁ : ℝ → ℝ) (g₁ : GTilde) (pr : L → L₁) (E' : ℝ → L),
      (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsLiftedDev θ E₁ D₁ (GTilde.delta ^ (2 : ℤ) * g₁) ∧
      (∃ x, g₁ x = x) ∧ g₁ ^ k = g ∧
      C.IsLiftedDev θ E' (fun s => D₁ (k * s)) f ∧ (∀ s, pr (E' s) = E₁ (k * s)) ∧
      IsCoveringMap pr ∧ (∀ y, Nat.card (pr ⁻¹' {y}) = k) ∧
      (letI := C.atlas; letI := cs₁; IsGXMorphism (GammaP C.pt) (Link C.pt) pr) ∧
      (C.pt ∈ HS.piece 2 .deSitter → (GTilde.IsHyperbolic g ↔ GTilde.IsHyperbolic g₁)) ∧
      (Causal.Flat.minkQ (C.pt : 𝕄) = 0 → (GTilde.IsParabolic g ↔ GTilde.IsParabolic g₁)) ∧
      (C.IsSpacelikePositive ↔ (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsSpacelikePositive) ∧
      (C.IsSpacelikeNegative ↔ (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsSpacelikeNegative) ∧
      (C.IsLightlikePositive ↔ (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsLightlikePositive) ∧
      (C.IsLightlikeNegative ↔ (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).IsLightlikeNegative) ∧
      ∀ Δ₁ : (GammaLinkCircle.mk C.pt cs₁ hcs₁ hL₁).DevData, ∃ Δ : C.DevData,
        (∀ s, pr (Δ.E s) = Δ₁.E (k * s)) ∧ (∀ s, Δ.d s = Δ₁.d (k * s)) ∧ Δ.hol = Δ₁.hol ^ k ∧
        (∀ s, Δ.vlift s = Δ₁.vlift (k * s)) ∧
        Δ.suspStructure.IsMorphism Δ₁.suspStructure (BiSusp.map pr) ∧
        IsBranchedCovering (BiSusp.map pr) ∧
        IsPossiblyBranchedOver (BiSusp.map pr) (BiSusp.poles L₁) ∧
        (2 ≤ k → branchingLocus (BiSusp.map pr) = BiSusp.poles L₁) ∧
        (∀ y ∉ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = k) ∧
        (∀ y ∈ BiSusp.poles L₁, Nat.card (BiSusp.map pr ⁻¹' {y}) = 1) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨L₁, _, cs₁, hcs₁, hL₁, E₁, D₁, g₁, pr, E', h₁, hg₁, hg₁k, h', hpr, hcov, hcard, hmor⟩ :=
    h.exists_degree_two_cover hp hk hg hfg
  have h'' : (GammaLinkCircle.mk C.pt C.atlas C.hasGroupoid C.isCircle).IsLiftedDev θ E'
      (fun s => D₁ (k * s)) (GTilde.delta ^ (2 * k : ℤ) * g₁ ^ k) := by
    rw [hg₁k, ← hfg]
    exact h'
  have hsign := GammaLinkCircle.IsLiftedDev.kfold_sign hθ hk hg₁ h'' h₁
  obtain ⟨ρ₁, hρ₁⟩ := h₁.exists_linkCover_apply
  have hg₁ρ : ∀ t, linkCover C.pt θ (g₁ t) = ρ₁ • linkCover C.pt θ t := fun t => by
    rw [← hρ₁, GTilde.coe_mul_apply, GTilde.delta_zpow_apply,
      show ((2 : ℤ) : ℝ) = 2 * ((1 : ℤ) : ℝ) by norm_num, linkCover_add_two_mul]
  refine ⟨L₁, inferInstance, cs₁, hcs₁, hL₁, E₁, D₁, g₁, pr, E', h₁, hg₁, hg₁k, h', hpr, hcov,
    hcard, hmor, fun hq => ?_, fun hq => ?_, hsign.1, hsign.2.1, hsign.2.2.1, hsign.2.2.2,
    fun Δ₁ => ?_⟩
  · rw [← hg₁k]
    exact isHyperbolic_pow_iff hq hg₁ρ hg₁ hk0
  · rw [← hg₁k]
    exact isParabolic_pow_iff hq hg₁ρ hg₁ hk0
  · exact susp_kfold_branched_cover (cs := C.atlas) (hcs := C.hasGroupoid) (hL := C.isCircle)
      h'.1 h₁.1 hk0 hpr hcov hcard hmor Δ₁

end Susp

end GX
