import Causal.Flat.Isometries
import Causal.Flat.Develop
import GX.Singular.Quotient
import GX.Structure.Developing

/-!
# `GX.Lorentz.Bridge` — gx's Minkowski space and `(G,X)`-vocabulary, bridged to `lean-causal`

Package WP-41a (WAVE5-PLAN.md, WP-39a). **Infrastructure for Section 4: no ledger label is
certified here, so nothing is marked.** It makes gx's null-coordinate model of `𝔼^{1,2}`
(`GX.nullQ`, `GX.NullIsom0`, `GX/Singular/Quotient.lean`, used by the BTZ white hole
`GX.btz_whitehole_isom0`) and gx's `(G,X)`-vocabulary (`GX.Structure.Basic`,
`GX.Topology.UniversalCover`, `GX.Structure.Developing`) usable against the ETT library's
`Causal.Minkowski 2`, `Causal.Flat.isom 2`, `Causal.UniversalCover` and
`Causal.Flat.IsDevelopingPair` (lean-causal pinned at `731ed99`; DEC-33: `Causal.*` names are
qualified, never opened).

> […] a couple $(G,X)$ where $X$ is a locally path-connected Hausdorff topological space and $G$ a
> group acting analytically on $X$ by homeomorphisms. […] The existence of a developing map from
> the universal covering of such a manifold $M$ to the model space $X$ and of an holonomy from its
> fundamental group to the model group $G$ is a general property as long as the universal
> covering exists. (`RamcovGX.tex:293`)

> […] $(P_\theta)_{\theta\in \RR}$ the 1-parameter family of parabolic isometries fixing point
> wise $x_0+\RR u$ some future lightlike vector and $\langle v|u\rangle<0$. (`RamcovGX.tex:672`)

## Main declarations

* **The isometry** `GX.nullToMink : (ℝ³, nullQ) ≃ₗ[ℝ] (𝐌³, minkQ)`, `(a, b, x) ↦ ((a+b)/2, ((a−b)/2, x))`:
  `minkQ_nullToMink` (`minkQ ∘ nullToMink = nullQ`), `fst_nullToMink` (time = `nullτ / 2`),
  `isFutureTimelike_nullToMink_iff`; `nullToMinkHomeomorph`; `nullToMink_nullU`.
* **The groups** `GX.nullIsom0EquivIsom : NullIsom0 ≃* Causal.Flat.isom 2` (conjugation,
  `nullAffConj`; `nullAffConj_mem_isom_iff`), equivariant: `nullToMink_smul`,
  `nullToMink_symm_smul`; the white-hole holonomy `nullIsom0EquivIsom_parab_smul` fixes
  `nullToMink (x₀ + ℝ u)`. Lemma of general use: `isFutureCausal_apply_of_isFutureTimelike`.
* **Actions**: `isRigidAction_iff_causal`, `isAnalyticAction_iff_causal`,
  `analyticStructure_iff_causal`; instances `GX.isAnalyticAction_flatIsom` (gx's
  `IsAnalyticAction (Causal.Flat.isom d) (Causal.Minkowski d)`, hence `IsRigidAction`) and
  `GX.isAnalyticAction_nullIsom0`; `analyticStructure_flatIsom`; transport along an equivariant
  homeomorphism `IsRigidAction.of_equivariantHomeomorph`, `IsAnalyticAction.of_equivariantHomeomorph`.
* **Groupoid**: `gxGroupoid_eq_causal` (`rfl`), `hasGroupoid_iff_causal`, `isGXMorphism_iff_causal`,
  `isGXAtlas_iff_causal`; transport of a structure along `e : X ≃ₜ X'` and `ψ : G →* G'`:
  `transportChartedSpace`, `hasGroupoid_transport`, `isGXMorphism_transport_comp`;
  `hasGroupoid_nullToMink` / `hasGroupoid_minkToNull` (null-coordinate manifolds ⇄ flat spacetimes).
* **Universal cover**: `semilocallySimplyConnected_iff_causal` (`Iff.rfl`);
  `GX.UniversalCover.toCausal : GX.UniversalCover Y y₀ ≃ₜ Causal.UniversalCover Y y₀`
  (`proj_toCausal`, `toCausal_base`); `GX.UniversalCover.deckToCausal` (`Deck ≃* Causal.Deck`),
  `deckToCausal_deckHom` (the `π₁`-actions agree).
* **Developing**: `isGXMorphism_coverChartedSpace_iff`, `isGXMorphism_causalCover_iff` (morphisms on
  either cover, intrinsically: no choice of local inverse), `isGXMorphism_cover_iff_causal`;
  `GX.isDevelopingPair_of_gx` (gx developing pair ⇒ `Causal.Flat.IsDevelopingPair`),
  `GX.gx_of_isDevelopingPair` (converse), `GX.exists_isDevelopingPair_of_developing_theorem` (via
  `GX.developing_theorem`), `GX.isDevelopingPair_of_null` (an `(Isom₀, ℝ³)` developing pair, as for
  the BTZ white hole, is a flat developing pair of the transported structure).

## Hypothesis checklist

| item | here |
|---|---|
| `Isom₀(𝔼^{1,2})` in null coordinates (gx: `Q`, `det > 0`, open future cone) vs `Isom(𝐌³)` (Barbot/ETT: `minkQ`, closed future cone, `det = 1`) | ✓ equal under conjugation: `det² = 1` for a `minkQ`-isometry (`Causal.Flat.det_sq_of_minkQ`), and open-cone preservation implies closed-cone preservation |
| `IsAnalyticAction` for `isom d` | ✓ from `Causal.Flat.isAnalyticAction_isom` (same fields) |
| universal cover | ✓ gx's and `lean-causal`'s are homeomorphic over `M`, by the identity on points |
| developing pair | ✓ for flat spacetimes, no hypothesis beyond the charted space (`LocPathConnectedSpace`, semilocal simple connectedness from charts) |

## SCOPE (disclosed)

* **(a)** The two universal covers are distinct types (the port is a copy, not an import); the
  bridge is the homeomorphism `toCausal`, not a definitional equality. The groupoids, the action
  classes, `SemilocallySimplyConnected`, `IsGXAtlas` *are* definitionally equal.
* **(b)** The pulled-back charts on the two covers differ by choices of local inverses; they are
  compared only through `isGXMorphism_*_iff`, which are choice-free.
* **(c)** The norm on `ℝ × ℝ × ℝ` (sup) and on `Causal.Minkowski 2` (product) are unrelated; only the
  topology (finite dimension) and the quadratic forms are bridged.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `731ed99`.
-/

namespace GX

open Set Filter Topology

/-! ### The linear isometry `(ℝ³, nullQ) ≃ (𝐌³, minkQ)` -/

section NullMinkowski

/-- **Null coordinates to Minkowski coordinates**: `(a, b, x) ↦ (t, (y, x))` with
`t = (a + b)/2`, `y = (a − b)/2` (`GX.nullQ`'s docstring: `a = t + y`, `b = t − y`). -/
noncomputable def nullToMink : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] Causal.Minkowski 2 where
  toFun y := ((y.1 + y.2.1) / 2, WithLp.toLp 2 ![(y.1 - y.2.1) / 2, y.2.2])
  invFun v := (v.1 + v.2 0, v.1 - v.2 0, v.2 1)
  map_add' y y' := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add]; ring
    · ext i
      fin_cases i
      · simp; ring
      · simp
  map_smul' c y := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring
    · ext i
      fin_cases i
      · simp; ring
      · simp
  left_inv y := by
    show ((y.1 + y.2.1) / 2 + (y.1 - y.2.1) / 2, (y.1 + y.2.1) / 2 - (y.1 - y.2.1) / 2, y.2.2) = y
    ext <;> simp <;> ring
  right_inv v := by
    refine Prod.ext ?_ ?_
    · simp
    · ext i; fin_cases i <;> simp

theorem nullToMink_apply (y : ℝ × ℝ × ℝ) :
    nullToMink y = ((y.1 + y.2.1) / 2, WithLp.toLp 2 ![(y.1 - y.2.1) / 2, y.2.2]) := rfl

theorem nullToMink_symm_apply (v : Causal.Minkowski 2) :
    nullToMink.symm v = (v.1 + v.2 0, v.1 - v.2 0, v.2 1) := rfl

/-- The time coordinate of `nullToMink y` is half of gx's time function `nullτ y = a + b`. -/
theorem fst_nullToMink (y : ℝ × ℝ × ℝ) : (nullToMink y).1 = nullτ y / 2 := rfl

/-- **`nullToMink` is an isometry**: `minkQ ∘ nullToMink = nullQ`. -/
theorem minkQ_nullToMink (y : ℝ × ℝ × ℝ) : Causal.Flat.minkQ (nullToMink y) = nullQ y := by
  simp only [Causal.Flat.minkQ, nullToMink_apply, EuclideanSpace.real_norm_sq_eq, nullQ]
  simp [Fin.sum_univ_two]
  ring

theorem minkQ_eq_nullQ_symm (v : Causal.Minkowski 2) :
    Causal.Flat.minkQ v = nullQ (nullToMink.symm v) := by
  rw [← minkQ_nullToMink, LinearEquiv.apply_symm_apply]

/-- The future timelike cone in null coordinates: `nullQ < 0` and `nullτ > 0`. -/
theorem isFutureTimelike_nullToMink_iff (y : ℝ × ℝ × ℝ) :
    Causal.Flat.IsFutureTimelike (nullToMink y) ↔ nullQ y < 0 ∧ 0 < nullτ y := by
  rw [Causal.Flat.IsFutureTimelike, fst_nullToMink, minkQ_nullToMink]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩

/-- `nullToMink` as a homeomorphism. -/
noncomputable def nullToMinkHomeomorph : (ℝ × ℝ × ℝ) ≃ₜ Causal.Minkowski 2 :=
  nullToMink.toContinuousLinearEquiv.toHomeomorph

@[simp] theorem coe_nullToMinkHomeomorph : ⇑nullToMinkHomeomorph = nullToMink := rfl

@[simp] theorem coe_nullToMinkHomeomorph_symm : ⇑nullToMinkHomeomorph.symm = nullToMink.symm :=
  rfl

end NullMinkowski

/-! ### `NullIsom0 ≃* Isom(𝐌³)` -/

section NullIsom

/-- **Conjugation by `nullToMink`** of affine automorphisms. -/
noncomputable def nullAffConj :
    ((ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) ≃* (Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) where
  toFun f := (nullToMink.symm.toAffineEquiv.trans f).trans nullToMink.toAffineEquiv
  invFun g := (nullToMink.toAffineEquiv.trans g).trans nullToMink.symm.toAffineEquiv
  left_inv f := AffineEquiv.ext fun y => by
    show nullToMink.symm (nullToMink (f (nullToMink.symm (nullToMink y)))) = f y
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv g := AffineEquiv.ext fun v => by
    show nullToMink (nullToMink.symm (g (nullToMink (nullToMink.symm v)))) = g v
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  map_mul' f g := AffineEquiv.ext fun v => by
    show nullToMink (f (g (nullToMink.symm v))) =
      nullToMink (f (nullToMink.symm (nullToMink (g (nullToMink.symm v)))))
    rw [LinearEquiv.symm_apply_apply]

theorem nullAffConj_apply (f : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (v : Causal.Minkowski 2) :
    nullAffConj f v = nullToMink (f (nullToMink.symm v)) := rfl

theorem nullAffConj_apply_nullToMink (f : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) (y : ℝ × ℝ × ℝ) :
    nullAffConj f (nullToMink y) = nullToMink (f y) := by
  rw [nullAffConj_apply, LinearEquiv.symm_apply_apply]

theorem nullAffConj_linear (f : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) :
    (nullAffConj f).linear = (nullToMink.symm.trans f.linear).trans nullToMink := rfl

/-- A `minkQ`-preserving linear map preserving the open future cone preserves the closed one
(approximate a future causal `v` by the future timelike `v + ε e₀`). -/
theorem isFutureCausal_apply_of_isFutureTimelike {d : ℕ}
    (A : Causal.Minkowski d →ₗ[ℝ] Causal.Minkowski d)
    (hQ : ∀ v, Causal.Flat.minkQ (A v) = Causal.Flat.minkQ v)
    (hT : ∀ v, Causal.Flat.IsFutureTimelike v → Causal.Flat.IsFutureTimelike (A v))
    {v : Causal.Minkowski d} (hv : Causal.Flat.IsFutureCausal v) :
    Causal.Flat.IsFutureCausal (A v) := by
  refine ⟨?_, by rw [hQ]; exact hv.2⟩
  set e := Causal.Flat.timeUnit d
  have hpos : ∀ ε : ℝ, 0 < ε → 0 < (A v).1 + ε * (A e).1 := by
    intro ε hε
    have hT' : Causal.Flat.IsFutureTimelike (v + ε • e) := by
      have hn := Causal.Flat.minkQ_le_zero_iff.1 hv.2
      refine ⟨?_, ?_⟩
      · simp [e, Causal.Flat.timeUnit]; linarith [hv.1]
      · rw [Causal.Flat.minkQ_lt_zero_iff]
        simp only [e, Causal.Flat.timeUnit, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, mul_one, smul_zero, add_zero]
        nlinarith [hv.1]
    have := (hT _ hT').1
    rw [map_add, map_smul] at this
    simpa using this
  by_contra h
  push Not at h
  set a := (A v).1
  set c := (A e).1
  have hc : 0 < |c| + 1 := by positivity
  have hε : 0 < -a / (2 * (|c| + 1)) := div_pos (by linarith) (by positivity)
  have h1 := hpos _ hε
  have h2 : -a / (2 * (|c| + 1)) * c ≤ -a / (2 * (|c| + 1)) * |c| :=
    mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have h3 : -a / (2 * (|c| + 1)) * (|c| + 1) = -a / 2 := by field_simp
  nlinarith

/-- **Membership**: `f ∈ NullIsom0 ↔ nullAffConj f ∈ Isom(𝐌³)`. The determinant of a
`minkQ`-preserving map is `±1` (`Causal.Flat.det_sq_of_minkQ`), so `det > 0` is `det = 1`; and
for such a map, preserving the open future cone is preserving the closed one. -/
theorem nullAffConj_mem_isom_iff (f : (ℝ × ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ × ℝ)) :
    nullAffConj f ∈ Causal.Flat.isom 2 ↔ f ∈ NullIsom0 := by
  rw [Causal.Flat.mem_isom_iff, nullAffConj_linear]
  set L := f.linear
  set L' := (nullToMink.symm.trans L).trans nullToMink
  have hL' : ∀ v, L' v = nullToMink (L (nullToMink.symm v)) := fun v => rfl
  have hQiff : (∀ v, Causal.Flat.minkQ (L' v) = Causal.Flat.minkQ v) ↔ ∀ w, nullQ (L w) = nullQ w := by
    constructor
    · intro h w
      have := h (nullToMink w)
      rwa [hL', LinearEquiv.symm_apply_apply, minkQ_nullToMink, minkQ_nullToMink] at this
    · intro h v
      rw [hL', minkQ_nullToMink, h, minkQ_eq_nullQ_symm]
  have hdet : LinearMap.det (L' : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) =
      ((LinearEquiv.det L : ℝˣ) : ℝ) := by
    rw [LinearEquiv.coe_det]
    exact LinearMap.det_conj (L : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) nullToMink
  constructor
  · rintro ⟨hQ', hC, hD⟩
    refine ⟨hQiff.1 hQ', by rw [← hdet, hD]; exact one_pos, fun w hw hτ => ?_⟩
    have := Causal.Flat.lorentz.isFutureTimelike_apply ⟨hQ', hC, hD⟩ (v := nullToMink w)
      ((isFutureTimelike_nullToMink_iff w).2 ⟨hw, hτ⟩)
    rw [hL', LinearEquiv.symm_apply_apply, isFutureTimelike_nullToMink_iff] at this
    exact this.2
  · rintro ⟨hQ, hD, hC⟩
    have hQ' := hQiff.2 hQ
    have hT : ∀ v, Causal.Flat.IsFutureTimelike v → Causal.Flat.IsFutureTimelike (L' v) := by
      intro v hv
      have hw := (isFutureTimelike_nullToMink_iff (nullToMink.symm v)).1
        (by rwa [LinearEquiv.apply_symm_apply])
      rw [hL', isFutureTimelike_nullToMink_iff]
      exact ⟨by rw [hQ]; exact hw.1, hC _ hw.1 hw.2⟩
    have h2 := Causal.Flat.det_sq_of_minkQ
      (A := (L' : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2)) fun v => hQ' v
    have hpos : 0 < LinearMap.det (L' : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) := by
      rw [hdet]; exact hD
    refine ⟨hQ', fun v hv => isFutureCausal_apply_of_isFutureTimelike
      (L' : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) (fun v => hQ' v) hT hv, ?_⟩
    nlinarith

/-- **`Isom₀(𝔼^{1,2})` in null coordinates is `Isom(𝐌³)`**: `NullIsom0 ≃* Causal.Flat.isom 2`,
by conjugation with `nullToMink`. -/
noncomputable def nullIsom0EquivIsom : NullIsom0 ≃* Causal.Flat.isom 2 where
  toFun f := ⟨nullAffConj f, (nullAffConj_mem_isom_iff f).2 f.2⟩
  invFun g := ⟨nullAffConj.symm g, by
    rw [← nullAffConj_mem_isom_iff, MulEquiv.apply_symm_apply]; exact g.2⟩
  left_inv f := Subtype.ext (nullAffConj.symm_apply_apply _)
  right_inv g := Subtype.ext (nullAffConj.apply_symm_apply _)
  map_mul' f g := Subtype.ext (map_mul nullAffConj _ _)

theorem coe_nullIsom0EquivIsom (f : NullIsom0) :
    ((nullIsom0EquivIsom f : Causal.Flat.isom 2) : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2) =
      nullAffConj f := rfl

/-- **Equivariance**: `nullToMink (f • y) = (nullIsom0EquivIsom f) • nullToMink y`. -/
theorem nullToMink_smul (f : NullIsom0) (y : ℝ × ℝ × ℝ) :
    nullToMink (f • y) = nullIsom0EquivIsom f • nullToMink y := by
  rw [Causal.Flat.isom_smul_def, coe_nullIsom0EquivIsom, nullAffConj_apply_nullToMink]
  rfl

/-- `nullToMink` of gx's lightlike vector `nullU = (1, 0, 0)`: `(1/2, (1/2, 0))`, future
lightlike. -/
theorem nullToMink_nullU : nullToMink nullU = ((1 : ℝ) / 2, WithLp.toLp 2 ![(1 : ℝ) / 2, 0]) := by
  rw [nullToMink_apply]; simp [nullU]

/-- **The parabolic holonomy of the white hole, in `Isom(𝐌³)`**: the image of `P_θ = parabAff x₀ θ`
(`GX.parab_mem`) fixes the lightlike line `nullToMink (x₀ + ℝ nullU)` pointwise. -/
theorem nullIsom0EquivIsom_parab_smul (x₀ : ℝ × ℝ × ℝ) (θ s : ℝ) :
    nullIsom0EquivIsom ⟨parabAff x₀ θ, parab_mem x₀ θ⟩ • nullToMink (x₀ + s • nullU) =
      nullToMink (x₀ + s • nullU) := by
  rw [← nullToMink_smul]
  congr 1
  show parabAff x₀ θ (x₀ + s • nullU) = x₀ + s • nullU
  rw [parabAff_apply, add_sub_cancel_left, map_smul, parab_nullU]

end NullIsom

/-! ### Analytic and rigid actions: gx's classes against `lean-causal`'s -/

section Actions

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]

/-- gx's `IsRigidAction` is `lean-causal`'s (`Causal.Port.GXBasic`, ported from gx). -/
theorem isRigidAction_iff_causal : IsRigidAction G X ↔ Causal.IsRigidAction G X :=
  ⟨fun h => ⟨h.smul_eq_of_eqOn⟩, fun h => ⟨h.smul_eq_of_eqOn⟩⟩

/-- gx's `IsAnalyticAction` is `lean-causal`'s. -/
theorem isAnalyticAction_iff_causal : IsAnalyticAction G X ↔ Causal.IsAnalyticAction G X :=
  ⟨fun h => { toFaithfulSMul := h.toFaithfulSMul, smul_eq_of_eqOn := h.smul_eq_of_eqOn },
    fun h => { toFaithfulSMul := h.toFaithfulSMul, smul_eq_of_eqOn := h.smul_eq_of_eqOn }⟩

/-- gx's `AnalyticStructure` is `lean-causal`'s. -/
theorem analyticStructure_iff_causal : AnalyticStructure G X ↔ Causal.AnalyticStructure G X :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, isAnalyticAction_iff_causal.1 h.5⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, isAnalyticAction_iff_causal.2 h.5⟩⟩

/-- **Rigidity transports along an equivariant homeomorphism**: if `e : X ≃ₜ X'` intertwines
`ψ : G →* G'` (`e (g • x) = ψ g • e x`) and `G'` acts rigidly on `X'`, so does `G` on `X`. -/
theorem IsRigidAction.of_equivariantHomeomorph {G' X' : Type*} [TopologicalSpace X'] [Group G']
    [MulAction G' X'] [IsRigidAction G' X'] (e : X ≃ₜ X') (ψ : G →* G')
    (he : ∀ (g : G) (x : X), e (g • x) = ψ g • e x) : IsRigidAction G X where
  smul_eq_of_eqOn {g h U} hU hne heq p := by
    have hU' : IsOpen (e '' U) := e.isOpenMap U hU
    have heq' : EqOn (fun q : X' => ψ g • q) (fun q => ψ h • q) (e '' U) := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [← he]
      exact congrArg e (heq hx)
    have := IsRigidAction.smul_eq_of_eqOn hU' (hne.image e) heq' (e p)
    rw [← he, ← he] at this
    exact e.injective this

/-- **Analyticity transports along an equivariant homeomorphism** with an injective `ψ`. -/
theorem IsAnalyticAction.of_equivariantHomeomorph {G' X' : Type*} [TopologicalSpace X'] [Group G']
    [MulAction G' X'] [IsAnalyticAction G' X'] (e : X ≃ₜ X') (ψ : G →* G')
    (hψ : Function.Injective ψ) (he : ∀ (g : G) (x : X), e (g • x) = ψ g • e x) :
    IsAnalyticAction G X :=
  { toFaithfulSMul := ⟨fun {g h} hgh => hψ (FaithfulSMul.eq_of_smul_eq_smul (α := X') fun q => by
      rw [← e.apply_symm_apply q, ← he, ← he, hgh])⟩
    smul_eq_of_eqOn := (IsRigidAction.of_equivariantHomeomorph e ψ he).smul_eq_of_eqOn }

/-- **`Isom(𝐌ⁿ)` acts analytically on `𝐌ⁿ`, in gx's sense** (`Causal.Flat.isAnalyticAction_isom`,
transported along `isAnalyticAction_iff_causal`). -/
instance isAnalyticAction_flatIsom (d : ℕ) :
    IsAnalyticAction (Causal.Flat.isom d) (Causal.Minkowski d) :=
  isAnalyticAction_iff_causal.2 Causal.Flat.isAnalyticAction_isom

/-- `(Isom(𝐌ⁿ), 𝐌ⁿ)` is an analytical structure in gx's sense. -/
theorem analyticStructure_flatIsom (d : ℕ) :
    AnalyticStructure (Causal.Flat.isom d) (Causal.Minkowski d) :=
  analyticStructure_iff_causal.2 Causal.Flat.analyticStructure_isom

/-- **`NullIsom0` acts analytically on `ℝ³`**, transported from `Isom(𝐌³)` along `nullToMink`. -/
instance isAnalyticAction_nullIsom0 : IsAnalyticAction NullIsom0 (ℝ × ℝ × ℝ) :=
  IsAnalyticAction.of_equivariantHomeomorph nullToMinkHomeomorph
    nullIsom0EquivIsom.toMonoidHom nullIsom0EquivIsom.injective nullToMink_smul

end Actions

/-! ### The `(G,X)`-groupoid, atlases and morphisms: gx's against `lean-causal`'s -/

section Groupoid

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type*} [TopologicalSpace M]

/-- **The two `(G,X)`-groupoids are the same** (`Causal.GXStructure`'s is gx's, character for
character): definitional. -/
theorem gxGroupoid_eq_causal : gxGroupoid G X = Causal.gxGroupoid G X := rfl

/-- A `(G,X)`-manifold in gx's sense is one in `lean-causal`'s, and conversely. -/
theorem hasGroupoid_iff_causal [ChartedSpace X M] :
    HasGroupoid M (gxGroupoid G X) ↔ HasGroupoid M (Causal.gxGroupoid G X) := Iff.rfl

omit [ContinuousConstSMul G X] in
/-- gx's `(G,X)`-morphisms are `lean-causal`'s. -/
theorem isGXMorphism_iff_causal {N : Type*} [TopologicalSpace N] [ChartedSpace X M]
    [ChartedSpace X N] {f : M → N} : IsGXMorphism G X f ↔ Causal.IsGXMorphism G X f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

omit [ContinuousConstSMul G X] in
/-- gx's `(G,X)`-atlases are `lean-causal`'s. -/
theorem isGXAtlas_iff_causal {A : Set (OpenPartialHomeomorph M X)} :
    IsGXAtlas G A ↔ Causal.IsGXAtlas G A := Iff.rfl

end Groupoid

/-! ### Transport of a `(G,X)`-structure along an equivariant homeomorphism `X ≃ₜ X'` -/

section Transport

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  {G' : Type*} {X' : Type*} [TopologicalSpace X'] [Group G'] [MulAction G' X']
  {M : Type*} [TopologicalSpace M]

/-- **The transported charted space**: the charts of `M` followed by `e : X ≃ₜ X'`. -/
@[reducible] def transportChartedSpace (e : X ≃ₜ X') (_ : ChartedSpace X M) : ChartedSpace X' M where
  atlas := (fun c => c.transHomeomorph e) '' atlas X M
  chartAt x := (chartAt X x).transHomeomorph e
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.transHomeomorph_source]; exact mem_chart_source X x
  chart_mem_atlas x := ⟨_, chart_mem_atlas X x, rfl⟩

theorem transportChartedSpace_chartAt_apply (e : X ≃ₜ X') (hM : ChartedSpace X M) (x y : M) :
    @chartAt X' _ M _ (transportChartedSpace e hM) x y = e (chartAt X x y) := rfl

/-- The transition maps of the transported atlas are, near every point, `e ∘ g ∘ e⁻¹ = ψ g`. -/
theorem eventually_transport_trans [ContinuousConstSMul G X] [ChartedSpace X M]
    [HasGroupoid M (gxGroupoid G X)] (e : X ≃ₜ X') (ψ : G →* G')
    (he : ∀ (g : G) (x : X), e (g • x) = ψ g • e x) {c c' : OpenPartialHomeomorph M X}
    (hc : c ∈ atlas X M) (hc' : c' ∈ atlas X M) {p : X'}
    (hp : p ∈ ((c.transHomeomorph e).symm.trans (c'.transHomeomorph e)).source) :
    ∃ g' : G', ((c.transHomeomorph e).symm.trans (c'.transHomeomorph e)) =ᶠ[𝓝 p]
      fun y => g' • y := by
  have hT : c.symm.trans c' ∈ gxGroupoid G X := HasGroupoid.compatible hc hc'
  have hq : e.symm p ∈ (c.symm.trans c').source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.transHomeomorph_target, OpenPartialHomeomorph.transHomeomorph_source,
      mem_inter_iff, mem_preimage] at hp ⊢
    exact ⟨hp.1, by simpa using hp.2⟩
  obtain ⟨g, hg⟩ := (mem_gxGroupoid_iff.1 hT).1 _ hq
  refine ⟨ψ g, ?_⟩
  have hcont : Tendsto e.symm (𝓝 p) (𝓝 (e.symm p)) := e.symm.continuous.tendsto p
  filter_upwards [hcont.eventually hg] with y hy
  have : ((c.transHomeomorph e).symm.trans (c'.transHomeomorph e)) y =
      e ((c.symm.trans c') (e.symm y)) := rfl
  rw [this, hy, he, e.apply_symm_apply]

/-- **The transported structure is a `(G',X')`-structure.** -/
theorem hasGroupoid_transport [ContinuousConstSMul G X] [ContinuousConstSMul G' X']
    [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)] (e : X ≃ₜ X') (ψ : G →* G')
    (he : ∀ (g : G) (x : X), e (g • x) = ψ g • e x) :
    @HasGroupoid X' _ M _ (transportChartedSpace e ‹_›) (gxGroupoid G' X') := by
  letI := transportChartedSpace e ‹ChartedSpace X M›
  refine ⟨?_⟩
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  refine mem_gxGroupoid_iff.2 ⟨fun p hp => eventually_transport_trans e ψ he hc hc' hp,
    fun p hp => ?_⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] at hp
  exact eventually_transport_trans e ψ he hc' hc hp

/-- **A developing-type map transports**: if `D : M → X` is a `(G,X)`-morphism into the model,
`e ∘ D : M → X'` is a `(G',X')`-morphism for the transported structure. -/
theorem isGXMorphism_transport_comp [ChartedSpace X M] (e : X ≃ₜ X') (ψ : G →* G')
    (he : ∀ (g : G) (x : X), e (g • x) = ψ g • e x) {D : M → X} (hD : IsGXMorphism G X D) :
    @IsGXMorphism G' X' _ _ _ M _ X' _ (transportChartedSpace e ‹_›) _ (e ∘ D) := by
  letI := transportChartedSpace e ‹ChartedSpace X M›
  obtain ⟨hc, hD⟩ := isGXMorphism_iff_model.1 hD
  refine isGXMorphism_iff_model.2 ⟨e.continuous.comp hc, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hD x
  refine ⟨ψ g, ?_⟩
  filter_upwards [hg] with y hy
  rw [Function.comp_apply, hy, he]; rfl

/-- The transport along `nullToMink`: an `(Isom₀, ℝ³)`-manifold in null coordinates is a flat
spacetime of `lean-causal` (`(Isom(𝐌³), 𝐌³)`-manifold). -/
theorem hasGroupoid_nullToMink [ChartedSpace (ℝ × ℝ × ℝ) M]
    [HasGroupoid M (gxGroupoid NullIsom0 (ℝ × ℝ × ℝ))] :
    @HasGroupoid _ _ M _ (transportChartedSpace nullToMinkHomeomorph ‹_›)
      (Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) :=
  hasGroupoid_transport nullToMinkHomeomorph nullIsom0EquivIsom.toMonoidHom nullToMink_smul

/-- Inverse equivariance: `nullToMink.symm (g • v) = nullIsom0EquivIsom.symm g • nullToMink.symm v`. -/
theorem nullToMink_symm_smul (g : Causal.Flat.isom 2) (v : Causal.Minkowski 2) :
    nullToMink.symm (g • v) = nullIsom0EquivIsom.symm g • nullToMink.symm v := by
  apply nullToMink.injective
  rw [LinearEquiv.apply_symm_apply, nullToMink_smul, MulEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **Conversely**, a flat spacetime of `lean-causal` (`(Isom(𝐌³), 𝐌³)`-manifold) is an
`(Isom₀, ℝ³)`-manifold in null coordinates, with the atlas `nullToMink⁻¹ ∘ chart`. -/
theorem hasGroupoid_minkToNull {N : Type*} [TopologicalSpace N] [ChartedSpace (Causal.Minkowski 2) N]
    [HasGroupoid N (Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2))] :
    @HasGroupoid _ _ N _ (transportChartedSpace nullToMinkHomeomorph.symm ‹_›)
      (gxGroupoid NullIsom0 (ℝ × ℝ × ℝ)) :=
  haveI : HasGroupoid N (gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) := ‹_›
  hasGroupoid_transport nullToMinkHomeomorph.symm nullIsom0EquivIsom.symm.toMonoidHom
    nullToMink_symm_smul

end Transport

/-! ### The universal cover: gx's against `lean-causal`'s -/

section Cover

variable {Y : Type*} [TopologicalSpace Y]

/-- Semilocal simple connectedness: gx's is `lean-causal`'s (definitional). -/
theorem semilocallySimplyConnected_iff_causal :
    SemilocallySimplyConnected Y ↔ Causal.SemilocallySimplyConnected Y := Iff.rfl

namespace UniversalCover

variable {y₀ : Y}

/-- The basic sets correspond. -/
theorem preimage_causal_basic (c : Causal.UniversalCover Y y₀) (U : Set Y) :
    (fun c' : UniversalCover Y y₀ => (⟨c'.pt, c'.cls⟩ : Causal.UniversalCover Y y₀)) ⁻¹'
      Causal.UniversalCover.basic c U = basic ⟨c.pt, c.cls⟩ U := rfl

theorem preimage_basic (c : UniversalCover Y y₀) (U : Set Y) :
    (fun c' : Causal.UniversalCover Y y₀ => (⟨c'.pt, c'.cls⟩ : UniversalCover Y y₀)) ⁻¹'
      basic c U = Causal.UniversalCover.basic ⟨c.pt, c.cls⟩ U := rfl

/-- **gx's universal cover is `lean-causal`'s**: the identity on points `⟨y, [γ]⟩`, a
homeomorphism (the basic sets correspond). -/
def toCausal (Y : Type*) [TopologicalSpace Y] (y₀ : Y) :
    UniversalCover Y y₀ ≃ₜ Causal.UniversalCover Y y₀ where
  toFun c := ⟨c.pt, c.cls⟩
  invFun c := ⟨c.pt, c.cls⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨c, U, hU, rfl⟩
    rw [preimage_causal_basic]
    exact isOpen_basic _ hU
  continuous_invFun := by
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨c, U, hU, rfl⟩
    rw [preimage_basic]
    exact Causal.UniversalCover.isOpen_basic _ hU

@[simp] theorem toCausal_pt (c : UniversalCover Y y₀) : (toCausal Y y₀ c).pt = c.pt := rfl

@[simp] theorem toCausal_symm_pt (c : Causal.UniversalCover Y y₀) :
    ((toCausal Y y₀).symm c).pt = c.pt := rfl

theorem proj_toCausal (c : UniversalCover Y y₀) :
    Causal.UniversalCover.proj Y y₀ (toCausal Y y₀ c) = proj Y y₀ c := rfl

theorem toCausal_base : toCausal Y y₀ (base y₀) = Causal.UniversalCover.base y₀ := rfl

/-- **The deck groups correspond**: conjugation by `toCausal`. -/
def deckToCausal (Y : Type*) [TopologicalSpace Y] (y₀ : Y) :
    Deck (proj Y y₀) ≃* Causal.Deck (Causal.UniversalCover.proj Y y₀) where
  toFun γ := ⟨((toCausal Y y₀).symm.trans γ.1).trans (toCausal Y y₀), by
    funext c; exact congrFun γ.2 ((toCausal Y y₀).symm c)⟩
  invFun γ := ⟨((toCausal Y y₀).trans γ.1).trans (toCausal Y y₀).symm, by
    funext c; exact congrFun γ.2 (toCausal Y y₀ c)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem deckToCausal_apply (γ : Deck (proj Y y₀)) (c : Causal.UniversalCover Y y₀) :
    (deckToCausal Y y₀ γ).1 c = toCausal Y y₀ (γ.1 ((toCausal Y y₀).symm c)) := rfl

theorem deckToCausal_symm_apply (γ : Causal.Deck (Causal.UniversalCover.proj Y y₀))
    (c : UniversalCover Y y₀) :
    ((deckToCausal Y y₀).symm γ).1 c = (toCausal Y y₀).symm (γ.1 (toCausal Y y₀ c)) := rfl

/-- **The actions of `π₁` correspond**: `deckToCausal ∘ deckHom = Causal.UniversalCover.deckHom`. -/
theorem deckToCausal_deckHom (a : FundamentalGroup Y y₀) :
    deckToCausal Y y₀ (deckHom a) = Causal.UniversalCover.deckHom a := rfl

end UniversalCover

end Cover

/-! ### The developing theorem: gx's against `lean-causal`'s `IsDevelopingPair` -/

section Developing

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type*} [TopologicalSpace M] [ChartedSpace X M] [LocPathConnectedSpace M]

/-- **A morphism on gx's universal cover, intrinsically**: for the pulled-back structure,
`D : M̃ → X` is a `(G,X)`-morphism iff it is continuous and near every `z` a translate of the
chart of `M` at `z.pt` read through the endpoint map. (No choice of local inverse appears.) -/
theorem isGXMorphism_coverChartedSpace_iff (hM : SemilocallySimplyConnected M) (x₀ : M)
    {D : UniversalCover M x₀ → X} :
    (letI := coverChartedSpace X hM x₀; IsGXMorphism G X D) ↔
      Continuous D ∧ ∀ z : UniversalCover M x₀, ∃ g : G,
        ∀ᶠ y in 𝓝 z, D y = g • chartAt X z.pt y.pt := by
  letI := coverChartedSpace X hM x₀
  rw [isGXMorphism_iff_model]
  refine and_congr Iff.rfl (forall_congr' fun z => exists_congr fun g => ?_)
  refine Filter.eventually_congr (Eventually.of_forall fun y => ?_)
  rw [pullback_chartAt_apply]

/-- The same characterization on `lean-causal`'s universal cover, with its pulled-back structure
(`Causal.coverChartedSpace`). -/
theorem isGXMorphism_causalCover_iff (hM : Causal.SemilocallySimplyConnected M) (x₀ : M)
    {D : Causal.UniversalCover M x₀ → X} :
    (letI := Causal.coverChartedSpace X hM x₀; Causal.IsGXMorphism G X D) ↔
      Continuous D ∧ ∀ z : Causal.UniversalCover M x₀, ∃ g : G,
        ∀ᶠ y in 𝓝 z, D y = g • chartAt X z.pt y.pt := by
  letI := Causal.coverChartedSpace X hM x₀
  rw [Causal.isGXMorphism_iff_model]
  refine and_congr Iff.rfl (forall_congr' fun z => exists_congr fun g => ?_)
  refine Filter.eventually_congr (Eventually.of_forall fun y => ?_)
  rw [Causal.pullback_chartAt_apply]

/-- **Developing maps correspond**: `D` is a `(G,X)`-morphism on gx's cover iff `D ∘ toCausal⁻¹`
is one on `lean-causal`'s. -/
theorem isGXMorphism_cover_iff_causal (hM : SemilocallySimplyConnected M) (x₀ : M)
    {D : UniversalCover M x₀ → X} :
    (letI := coverChartedSpace X hM x₀; IsGXMorphism G X D) ↔
      (letI := Causal.coverChartedSpace X hM x₀;
        Causal.IsGXMorphism G X (D ∘ (UniversalCover.toCausal M x₀).symm)) := by
  rw [isGXMorphism_coverChartedSpace_iff, isGXMorphism_causalCover_iff]
  set Φ := UniversalCover.toCausal M x₀
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc.comp Φ.symm.continuous, fun z => ?_⟩
    obtain ⟨g, hg⟩ := h (Φ.symm z)
    exact ⟨g, (Φ.symm.continuous.tendsto z).eventually hg⟩
  · rintro ⟨hc, h⟩
    have hc' : Continuous D := by
      have := hc.comp Φ.continuous
      simpa [Function.comp_def] using this
    refine ⟨hc', fun z => ?_⟩
    obtain ⟨g, hg⟩ := h (Φ z)
    refine ⟨g, ?_⟩
    have := (Φ.continuous.tendsto z).eventually hg
    simpa [Function.comp_def, Φ] using this

end Developing

/-! ### Flat spacetimes: gx's developing theorem gives `Causal.Flat.IsDevelopingPair` -/

section Flat

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Causal.Minkowski d) M]

/-- **A gx developing pair is a `lean-causal` developing pair**: for a flat spacetime `M`
(`(Isom(𝐌ⁿ), 𝐌ⁿ)`-manifold), a developing pair `(dev, hol)` on gx's universal cover — `dev` a
morphism for the structure `GX.coverChartedSpace` pulled back along `proj`, equivariant for
`hol : Deck →* Isom(𝐌ⁿ)` — gives `Causal.Flat.IsDevelopingPair x₀ (dev ∘ toCausal⁻¹) ρ` with
`ρ = hol ∘ deckToCausal⁻¹`. -/
theorem isDevelopingPair_of_gx (x₀ : M) {dev : UniversalCover M x₀ → Causal.Minkowski d}
    {hol : Deck (UniversalCover.proj M x₀) →* Causal.Flat.isom d}
    (hdev : haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
      letI := coverChartedSpace (Causal.Minkowski d)
        (Causal.Flat.semilocallySimplyConnected_of_flat d M) x₀
      IsGXMorphism (Causal.Flat.isom d) (Causal.Minkowski d) dev)
    (hhol : ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
      dev (γ.1 z) = hol γ • dev z) :
    Causal.Flat.IsDevelopingPair x₀ (dev ∘ (UniversalCover.toCausal M x₀).symm)
      (hol.comp (UniversalCover.deckToCausal M x₀).symm.toMonoidHom) := by
  haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
  refine ⟨(isGXMorphism_cover_iff_causal (Causal.Flat.semilocallySimplyConnected_of_flat d M)
    x₀).1 hdev, fun γ z => ?_⟩
  set δ := (UniversalCover.deckToCausal M x₀).symm γ
  have h1 : (UniversalCover.toCausal M x₀).symm (γ.1 z) =
      δ.1 ((UniversalCover.toCausal M x₀).symm z) := rfl
  simp only [Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  rw [h1, hhol]

/-- **Conversely**, a `lean-causal` developing pair is a gx developing pair on gx's cover. -/
theorem gx_of_isDevelopingPair (x₀ : M) {D : Causal.UniversalCover M x₀ → Causal.Minkowski d}
    {ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d}
    (h : Causal.Flat.IsDevelopingPair x₀ D ρ) :
    haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
    letI := coverChartedSpace (Causal.Minkowski d)
      (Causal.Flat.semilocallySimplyConnected_of_flat d M) x₀
    IsGXMorphism (Causal.Flat.isom d) (Causal.Minkowski d) (D ∘ UniversalCover.toCausal M x₀) ∧
    ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
      (D ∘ UniversalCover.toCausal M x₀) (γ.1 z) =
        (ρ.comp (UniversalCover.deckToCausal M x₀).toMonoidHom) γ •
          (D ∘ UniversalCover.toCausal M x₀) z := by
  haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
  refine ⟨(isGXMorphism_cover_iff_causal (Causal.Flat.semilocallySimplyConnected_of_flat d M)
    x₀).2 h.gx, fun γ z => ?_⟩
  have h1 : UniversalCover.toCausal M x₀ (γ.1 z) =
      (UniversalCover.deckToCausal M x₀ γ).1 (UniversalCover.toCausal M x₀ z) := rfl
  simp only [Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  rw [h1, h.equiv]

/-- **`Causal.Flat.exists_isDevelopingPair` from gx's classical developing theorem**: every flat
spacetime (`HasGroupoid` for `lean-causal`'s groupoid, which is gx's) has a developing pair in
`lean-causal`'s sense, obtained from `GX.developing_theorem` through the bridge. -/
theorem exists_isDevelopingPair_of_developing_theorem
    [HasGroupoid M (Causal.gxGroupoid (Causal.Flat.isom d) (Causal.Minkowski d))] (x₀ : M) :
    ∃ (D : Causal.UniversalCover M x₀ → Causal.Minkowski d)
      (ρ : Causal.Deck (Causal.UniversalCover.proj M x₀) →* Causal.Flat.isom d),
      Causal.Flat.IsDevelopingPair x₀ D ρ := by
  haveI := Causal.Flat.locPathConnectedSpace_of_flat d M
  haveI : HasGroupoid M (gxGroupoid (Causal.Flat.isom d) (Causal.Minkowski d)) := ‹_›
  obtain ⟨dev, hol, hdev, -, hhol⟩ := developing_theorem (G := Causal.Flat.isom d)
    (X := Causal.Minkowski d) (Causal.Flat.semilocallySimplyConnected_of_flat d M) x₀
  exact ⟨_, _, isDevelopingPair_of_gx x₀ hdev hhol⟩

end Flat

/-! ### Null coordinates: an `(Isom₀, ℝ³)`-developing pair is a flat developing pair -/

section Null

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ × ℝ) M] [LocPathConnectedSpace M]

/-- **The null-coordinate developing pair, transported**: for `M` an `(Isom₀, ℝ³)`-manifold in null
coordinates (the BTZ white hole's structure, `GX.btz_whitehole_isom0`) and a gx developing pair
`(dev, hol)` on its universal cover, `M` with the transported atlas (`nullToMink ∘ chart`) is a
flat spacetime of `lean-causal` (`hasGroupoid_nullToMink`) and
`(nullToMink ∘ dev ∘ toCausal⁻¹, nullIsom0EquivIsom ∘ hol ∘ deckToCausal⁻¹)` is a
`Causal.Flat.IsDevelopingPair`. -/
theorem isDevelopingPair_of_null (hM : SemilocallySimplyConnected M) (x₀ : M)
    {dev : UniversalCover M x₀ → ℝ × ℝ × ℝ} {hol : Deck (UniversalCover.proj M x₀) →* NullIsom0}
    (hdev : letI := coverChartedSpace (ℝ × ℝ × ℝ) hM x₀; IsGXMorphism NullIsom0 (ℝ × ℝ × ℝ) dev)
    (hhol : ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
      dev (γ.1 z) = hol γ • dev z) :
    letI := transportChartedSpace nullToMinkHomeomorph ‹ChartedSpace (ℝ × ℝ × ℝ) M›
    Causal.Flat.IsDevelopingPair x₀ (nullToMink ∘ dev ∘ (UniversalCover.toCausal M x₀).symm)
      ((nullIsom0EquivIsom.toMonoidHom.comp hol).comp
        (UniversalCover.deckToCausal M x₀).symm.toMonoidHom) := by
  letI hT := transportChartedSpace nullToMinkHomeomorph ‹ChartedSpace (ℝ × ℝ × ℝ) M›
  refine ⟨?_, fun γ z => ?_⟩
  · refine (isGXMorphism_causalCover_iff (G := Causal.Flat.isom 2)
      (Causal.Flat.semilocallySimplyConnected_of_flat 2 M) x₀).2 ?_
    obtain ⟨hc, h⟩ := (isGXMorphism_coverChartedSpace_iff hM x₀).1 hdev
    refine ⟨nullToMinkHomeomorph.continuous.comp
      (hc.comp (UniversalCover.toCausal M x₀).symm.continuous), fun z => ?_⟩
    obtain ⟨g, hg⟩ := h ((UniversalCover.toCausal M x₀).symm z)
    refine ⟨nullIsom0EquivIsom g, ?_⟩
    filter_upwards [((UniversalCover.toCausal M x₀).symm.continuous.tendsto z).eventually hg]
      with y hy
    simp only [Function.comp_apply]
    rw [hy, nullToMink_smul]
    rfl
  · set δ := (UniversalCover.deckToCausal M x₀).symm γ
    have h1 : (UniversalCover.toCausal M x₀).symm (γ.1 z) =
        δ.1 ((UniversalCover.toCausal M x₀).symm z) := rfl
    simp only [Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    rw [h1, hhol, nullToMink_smul]

end Null

/-! ### Inhabitants and instance checks -/

/-- The action of `Isom(𝐌ⁿ)` seen from namespace `GX` is `lean-causal`'s (no diamond). -/
example (d : ℕ) (g : Causal.Flat.isom d) (p : Causal.Minkowski d) :
    g • p = (g : Causal.Minkowski d ≃ᵃ[ℝ] Causal.Minkowski d) p := rfl

example (d : ℕ) : IsRigidAction (Causal.Flat.isom d) (Causal.Minkowski d) := inferInstance

example : IsRigidAction NullIsom0 (ℝ × ℝ × ℝ) := inferInstance

/-- The flat bridge applies to `𝐌ⁿ` itself (the hypotheses are inhabited). -/
example (d : ℕ) (x₀ : Causal.Minkowski d) :=
  exists_isDevelopingPair_of_developing_theorem (d := d) (M := Causal.Minkowski d) x₀

end GX
