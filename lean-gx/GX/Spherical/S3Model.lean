import GX.Suspension.Affine
import GX.SingularII.Unloopable
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The spherical models `(SO(n+1), 𝕊ⁿ)`, `(SO(4), 𝕊³)`, and Thurston's suspension `𝕊ⁿ → 𝕊ⁿ⁺¹`

Target `T-gx-spherical-cone` (`roadmap/roadmap.toml`; DEC-136, its first step). `papers/gx`: the
model of `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930–1937`) and Thurston's
suspension method (`sec:susp`, l.689–703). **No label is marked here**; 0 `sorry`.

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial (row stays partial
  until `T-gx-troyanov`): this file builds the model `(SO(4), 𝕊³)` the cex works in and the
  Thurston suspension it applies (l.1931); the angle-tied statement is in
  `GXScaffold.Spherical.TroyanovAngles`.
* **The model `(SO(V), 𝕊(V))`**, `V` a real inner product space: `GX.SpecialOrth V` (the linear
  isometries of determinant `1`) acting on the unit sphere `GX.RaySphere V`
  (`GX.specialOrthAction`) by isometries (`GX.dist_specialOrth_smul`) and homeomorphisms,
  **rigidly** (`GX.isRigidAction_specialOrth`, through `GX.eq_of_eqOn_sphere`) and faithfully
  (`GX.faithfulSMul_specialOrth`): analytical (`GX.isAnalyticAction_specialOrth`,
  `GX.analyticStructure_sphere`, `dim V ≥ 2`), and **locally unloopable**
  (`GX.isLocallyUnloopable_raySphere`).
* **`(SO(4), 𝕊³)` and `(SO(3), 𝕊²)`**: `GX.Euc3 = ℝ ⊕ ℂ`, `GX.Euc4 = ℝ ⊕ ℝ³` (`GX.PolarSum`, the
  `L²` product), `GX.Sph2`, `GX.Sph3`, `GX.SO3`, `GX.SO4`; `GX.analyticStructure_SO4`,
  `GX.analyticStructure_SO3`, `GX.isLocallyUnloopable_sph3`, `GX.isLocallyUnloopable_sph2`;
  `ℝ⁴` is the Euclidean `4`-space: `GX.finrank_euc4`, `GX.euc4Isometry`, `GX.sph3Homeomorph`.
* **Thurston's suspension `𝕊ⁿ → 𝕊ⁿ⁺¹`** (l.694–700), for any finite-dimensional `W`: the
  stabiliser embedding `GX.liftSO : SO(W) →* SO(ℝ ⊕ W)`, `A ↦ 1 ⊕ A`; the stereographic chart
  from the south pole `GX.stereoChart` (`GX.stereoInv`, `GX.liftSO_smul_stereoInv`); the full
  conic chart of `𝕊(ℝ ⊕ W)` at the north pole with link `𝕊(W)`, `GX.sphConic`
  (`GX.sphConic_isFull`), radius preserving (`GX.sphConic_symm_smul`); for a singular
  `(SO(W), 𝕊(W))`-manifold `Σ`, the cone atlas `GX.thurstonAtlas` on `susp(Σ)`, whose chart
  changes lie in `SO(ℝ ⊕ W)` (`GX.thurston_eventually_eq_smul`), an **a.e. atlas**
  (`GX.isAEAtlas_thurstonAtlas`, the support by `prop:susp_portly`), the singular structure
  `GX.thurstonStructure`, the rays over regular points regular (`GX.thurston_mk_mem_reg`).

> Apply the Thurston suspension method described in Section \ref{sec:susp}, the constructed
> manifold $M$ is a singular $(\SO(4),\SS^3)$-manifold (we may either apply by Proposition
> \ref{prop:susp_portly} or check that directly). We call $O$ its center. (l.1931)
>
> We give ourselves some analytical structure $(G,X)$, ie a connected, locally connected,
> Hausdorff topological space $X$ together with a faithful action of a group $G$ by
> homeomorphisms such that for all $\phi_1,\phi_2\in G$ and all non trivial open subset
> $\U\subset X$, if the action of $\phi_1$ and $\phi_1$ agree on $\U$ they agree on $X$. (l.341)
>
> Take a $(\SS^n,\SO(n+1))$-manifold $M$ with conical singularities and with $M$ homeomorphic to
> $\SS^n$, denote its Riemannian metric by $\mathbf{g}$ which is defined on the complement of the
> singularities; Define the {\it suspension} of $M$ by $\widehat M = (M\times \RR_+)/\sim$ the set
> of $(\theta,r)$ where $(\theta_1,0)\sim (\theta_2,0)$ for all $\theta_1,\theta_2\in M$; Endow
> $\widehat M$ with a Riemannian metric
> $\widehat{\mathbf{g}}(\theta,r) = \mathbf{d r}\otimes \mathbf{d r}+ \sin(r)^2 \mathbf{g}(\theta)$
> which is "regular", eg locally isometric to $\SS^{n+1}$, on rays through "regular" points of
> $M$. (l.697–700)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X)` analytical (l.341): `X` connected, locally connected, Hausdorff; `G` faithful, rigid, by homeomorphisms | ✓ carried: all proved for `(SO(V), 𝕊(V))` (`analyticStructure_sphere`; connected for `dim V ≥ 2`) |
| `X` locally unloopable (§2.5's standing assumption, l.1660) | ✓ proved (`isLocallyUnloopable_raySphere`, `dim V = n + 1`) |
| `SO(4)` acting on `𝕊³` (l.1931) | ✓ `SO4 = SpecialOrth Euc4` on `Sph3`, `Euc4 = ℝ ⊕ ℝ ⊕ ℂ` with the `L²` inner product, isometric to `EuclideanSpace ℝ (Fin 4)` (SCOPE (a)) |
| the suspension `(M × ℝ₊)/∼` with `dr² + sin²r g` (l.698–700) | ⚠ read through charts (SCOPE (b)) |
| "or check that directly" (l.1931): `susp(M)` is a singular `(SO(4), 𝕊³)`-manifold | ✓ `isAEAtlas_thurstonAtlas`, `thurstonStructure`, for `M` connected and locally connected |

## SCOPE (disclosed)

* **(a)** `ℝ⁴` is presented as `ℝ ⊕ ℝ³`, `ℝ³ = ℝ ⊕ ℂ` (`PolarSum`): the polar axes are split
  off, so that the suspension and the rotations about an axis are coordinate formulas. `SO(V)`
  is the group of linear isometries of determinant `1` of `V` (for `V = ℝ⁴`, `SO(4)` by
  definition); `Euc4` is isometric to `EuclideanSpace ℝ (Fin 4)` (`euc4Isometry`) and `Sph3` to
  its unit sphere (`sph3Homeomorph`).
* **(b)** Thurston's suspension is formalized through its `(SO(n+2), 𝕊ⁿ⁺¹)`-charts, not through
  a Riemannian metric (there is no Riemannian metric on singular spaces at this pin): the cone
  chart of a chart `e` of `M` sends `(σ, r) ∈ susp(M) = (M × ℝ≥0)/∼` (`GX.Susp`, RamcovGX's
  topology, l.710) to the point of `𝕊ⁿ⁺¹` at spherical distance `ρ = 2 arctan r` from the north
  pole in the direction `e(σ)`. With `r` over all of `ℝ₊`, the paper's `dr² + sin²r g`
  degenerates at `r = π` (and at every `kπ`; it is locally spherical again on each band between),
  so `(M × ℝ₊)/∼` with it is not a Riemannian (cone-)manifold; the intended model is `r ∈ [0, π)`
  (one centre) or `r ∈ [0, π]` with both ends collapsed (two centres). The reading taken is the
  open ball `ρ < π` about `O`, which `r = tan(ρ/2) ∈ [0, ∞)` parametrises (a question for the
  author). Its structure is the maximal
  a.e. atlas generated by the cone charts (`cor:maximal_atlas`).
* **(c)** Not proved here: the rays over singular points of `Σ` are singular, and `O` is singular
  unless `Σ` is the round sphere (`GX.ConicStructure.mk_mem_sing` proves the first for a
  `ConicStructure`; the Thurston atlas is not packaged as one, because the link action there is
  of a subgroup of `SO(ℝ ⊕ W)` — the image of `liftSO` — not of `SO(W)`). These belong to
  `T-gx-troyanov-suspension`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Suspension.Affine` (`RaySphere`, `sphereSusp`), `GX.Suspension.Celestial`
(`ConicChart.coneChart`), `GX.Singular.Suspension` (`Susp`, `prop:susp_portly`),
`GX.SingularII.Unloopable`.
-/

noncomputable section

open Set Filter Topology NNReal Metric

namespace GX

set_option linter.unusedSectionVars false

/-! ### `SO(V)` acting on the unit sphere `𝕊(V)` -/

section SpecialOrth

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`SO(V)`**, the special orthogonal group of a real inner product space: the linear
isometries of determinant `1`. For `V = ℝ⁴` it is `SO(4)`. -/
def SpecialOrth : Subgroup (V ≃ₗᵢ[ℝ] V) where
  carrier := {L | LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1}
  mul_mem' {a b} ha hb := by
    simp only [mem_setOf_eq] at ha hb ⊢
    have : ((a * b).toLinearEquiv : V →ₗ[ℝ] V) =
        (a.toLinearEquiv : V →ₗ[ℝ] V) ∘ₗ (b.toLinearEquiv : V →ₗ[ℝ] V) := by
      ext v; rfl
    rw [this, LinearMap.det_comp, ha, hb, one_mul]
  one_mem' := by
    simp only [mem_setOf_eq]
    have : ((1 : V ≃ₗᵢ[ℝ] V).toLinearEquiv : V →ₗ[ℝ] V) = LinearMap.id := by ext v; rfl
    rw [this, LinearMap.det_id]
  inv_mem' {a} ha := by
    simp only [mem_setOf_eq] at ha ⊢
    have h1 : (a.toLinearEquiv : V →ₗ[ℝ] V) ∘ₗ ((a⁻¹).toLinearEquiv : V →ₗ[ℝ] V) =
        LinearMap.id := by
      ext v; show a (a⁻¹ v) = v; exact a.apply_symm_apply v
    have := congrArg LinearMap.det h1
    rw [LinearMap.det_comp, ha, one_mul, LinearMap.det_id] at this
    exact this

variable {V}

theorem mem_specialOrth {L : V ≃ₗᵢ[ℝ] V} :
    L ∈ SpecialOrth V ↔ LinearMap.det (L.toLinearEquiv : V →ₗ[ℝ] V) = 1 := Iff.rfl

/-- `SO(V)` acts on the unit sphere `𝕊(V) = RaySphere V` by restriction. -/
instance specialOrthAction : MulAction (SpecialOrth V) (RaySphere V) where
  smul L σ := ⟨(L : V ≃ₗᵢ[ℝ] V) σ, mem_sphere_zero_iff_norm.2 (by
    rw [LinearIsometryEquiv.norm_map, norm_raySphere])⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem coe_specialOrth_smul (L : SpecialOrth V) (σ : RaySphere V) :
    ((L • σ : RaySphere V) : V) = (L : V ≃ₗᵢ[ℝ] V) σ := rfl

instance : ContinuousConstSMul (SpecialOrth V) (RaySphere V) :=
  ⟨fun L => ((L : V ≃ₗᵢ[ℝ] V).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- `SO(V)` acts on `𝕊(V)` **by isometries** (of the chordal distance, hence of the round
one, which is a function of it). -/
theorem dist_specialOrth_smul (L : SpecialOrth V) (σ τ : RaySphere V) :
    dist (L • σ) (L • τ) = dist σ τ := by
  rw [Subtype.dist_eq, Subtype.dist_eq, coe_specialOrth_smul, coe_specialOrth_smul,
    LinearIsometryEquiv.dist_map]

/-- Two linear maps agreeing on a nonempty open subset of the unit sphere are equal: they agree on
the open cone over it, whose affine span is everything. -/
theorem eq_of_eqOn_sphere {f g : V →ₗ[ℝ] V} {U : Set (RaySphere V)} (hU : IsOpen U)
    (hne : U.Nonempty) (heq : ∀ σ ∈ U, f σ = g σ) : f = g := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
  set C : Set V := {v | v ≠ 0} ∩ (fun v : V => ‖v‖⁻¹ • v) ⁻¹' W
  have hC : IsOpen C := by
    refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_ne hW
    exact (continuous_norm.continuousOn.inv₀ fun v hv => norm_ne_zero_iff.2 hv).smul
      continuousOn_id
  obtain ⟨σ, hσ⟩ := hne
  have hCne : C.Nonempty := ⟨σ, raySphere_ne_zero σ, by
    show ‖(σ : V)‖⁻¹ • (σ : V) ∈ W
    rw [norm_raySphere, inv_one, one_smul]; exact hσ⟩
  have hEq : EqOn f g C := by
    rintro v ⟨hv, hvW⟩
    have h1 := heq ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.2 (norm_inv_smul_self hv)⟩ hvW
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hf : f v = ‖v‖ • f (‖v‖⁻¹ • v) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have hg : g v = ‖v‖ • g (‖v‖⁻¹ • v) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [hf, hg]
    exact congrArg (‖v‖ • ·) h1
  have := AffineMap.ext_on (hC.affineSpan_eq_top hCne) (f := f.toAffineMap)
    (g := g.toAffineMap) hEq
  ext v
  exact congrArg (fun F : V →ᵃ[ℝ] V => F v) this

/-- **`SO(V)` acts rigidly on `𝕊(V)`** (gx's "analytically", `RamcovGX.tex:341`): two elements
whose actions agree on a nonempty open set are equal. -/
instance isRigidAction_specialOrth : IsRigidAction (SpecialOrth V) (RaySphere V) :=
  ⟨fun {g h} {U} hU hne heq p => by
    have := eq_of_eqOn_sphere (f := ((g : V ≃ₗᵢ[ℝ] V).toLinearEquiv : V →ₗ[ℝ] V))
      (g := ((h : V ≃ₗᵢ[ℝ] V).toLinearEquiv : V →ₗ[ℝ] V)) hU hne fun σ hσ =>
        congrArg Subtype.val (heq hσ)
    exact Subtype.ext (congrArg (fun F : V →ₗ[ℝ] V => F p) this)⟩

/-- `SO(V)` acts faithfully on `𝕊(V)`. -/
instance faithfulSMul_specialOrth : FaithfulSMul (SpecialOrth V) (RaySphere V) :=
  ⟨fun {g h} H => by
    refine Subtype.ext (LinearIsometryEquiv.ext fun v => ?_)
    by_cases hv : v = 0
    · rw [hv, map_zero, map_zero]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
      have h1 := congrArg Subtype.val
        (H ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.2 (norm_inv_smul_self hv)⟩)
      simp only [coe_specialOrth_smul] at h1
      have hf : (g : V ≃ₗᵢ[ℝ] V) v = ‖v‖ • (g : V ≃ₗᵢ[ℝ] V) (‖v‖⁻¹ • v) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
      have hg : (h : V ≃ₗᵢ[ℝ] V) v = ‖v‖ • (h : V ≃ₗᵢ[ℝ] V) (‖v‖⁻¹ • v) := by
        rw [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
      rw [hf, hg, h1]⟩

/-- **`(SO(V), 𝕊(V))` is analytical** in gx's sense: faithful and rigid. -/
instance isAnalyticAction_specialOrth : IsAnalyticAction (SpecialOrth V) (RaySphere V) where

/-- `𝕊(V)` is connected in dimension `≥ 2`. -/
theorem connectedSpace_raySphere (hdim : 2 ≤ Module.finrank ℝ V) [FiniteDimensional ℝ V] :
    ConnectedSpace (RaySphere V) := by
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]; exact_mod_cast hdim
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact { toPreconnectedSpace := preconnectedSpace_raySphere (V := V) hrank
          toNonempty := ⟨⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.2 (norm_inv_smul_self hv)⟩⟩ }

/-- **The analytical structure `(SO(V), 𝕊(V))`** (`RamcovGX.tex:341`: `X` connected, locally
connected, Hausdorff, `G` acting faithfully and rigidly by homeomorphisms), `dim V ≥ 2`. -/
theorem analyticStructure_sphere (hdim : 2 ≤ Module.finrank ℝ V) [FiniteDimensional ℝ V] :
    AnalyticStructure (SpecialOrth V) (RaySphere V) where
  connectedSpace := connectedSpace_raySphere hdim
  locallyConnectedSpace := inferInstance
  t2Space := inferInstance
  continuousConstSMul := inferInstance
  isAnalyticAction := inferInstance

/-- **`𝕊(V)` is locally unloopable** (`def:topological_space_locally_unloopable`,
`RamcovGX.tex:1650`, the standing assumption on the model of §2.5, l.1660): it is a manifold,
covered by stereographic charts into `ℝⁿ`. -/
theorem isLocallyUnloopable_raySphere {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] :
    IsLocallyUnloopable (RaySphere V) := by
  haveI : LocPathConnectedSpace (RaySphere V) :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin n)) _
  refine ⟨inferInstance, fun x U hU => ?_⟩
  refine ⟨interior U, interior_subset, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, ?_⟩
  refine (isLocallyUnloopable_of_normedSpace
    (EuclideanSpace ℝ (Fin n))).semilocallySimplyConnected_of_charts
    fun y hy => ⟨(chartAt (EuclideanSpace ℝ (Fin n)) y).restrOpen _ isOpen_interior,
      ⟨mem_chart_source _ y, hy⟩, fun z hz => hz.2⟩

end SpecialOrth

/-! ### The polar sum `ℝ ⊕ W`, the lift `SO(W) → SO(ℝ ⊕ W)`, and `ℝ³`, `ℝ⁴`, `𝕊²`, `𝕊³` -/

section Polar

variable (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **The polar sum `ℝ ⊕ W`**: `ℝ × W` with the Euclidean (`L²`) inner product
`⟨(t, w), (t', w')⟩ = t t' + ⟨w, w'⟩`; the first factor is the polar axis. -/
abbrev PolarSum : Type _ := WithLp 2 (ℝ × W)

/-- `ℝ³ = ℝ ⊕ ℂ` (the polar axis and the equatorial plane `ℂ`). -/
abbrev Euc3 : Type := PolarSum ℂ

/-- `ℝ⁴ = ℝ ⊕ ℝ³`. -/
abbrev Euc4 : Type := PolarSum Euc3

/-- **The round sphere `𝕊²`**, the unit sphere of `ℝ³`. -/
abbrev Sph2 : Type := RaySphere Euc3

/-- **The round sphere `𝕊³`**, the unit sphere of `ℝ⁴`. -/
abbrev Sph3 : Type := RaySphere Euc4

/-- **`SO(3)`**, acting on `𝕊²`. -/
abbrev SO3 : Type := SpecialOrth Euc3

/-- **`SO(4)`**, acting on `𝕊³`. -/
abbrev SO4 : Type := SpecialOrth Euc4

variable {W}

theorem norm_polarSum_sq (x : PolarSum W) : ‖x‖ ^ 2 = x.fst ^ 2 + ‖x.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem norm_toLp_sq (t : ℝ) (w : W) :
    ‖(WithLp.toLp 2 (t, w) : PolarSum W)‖ ^ 2 = t ^ 2 + ‖w‖ ^ 2 := by
  rw [norm_polarSum_sq]; rfl

theorem finrank_polarSum [FiniteDimensional ℝ W] :
    Module.finrank ℝ (PolarSum W) = Module.finrank ℝ W + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × W)).finrank_eq, Module.finrank_prod, Module.finrank_self,
    add_comm]

theorem finrank_euc3 : Module.finrank ℝ Euc3 = 3 := by
  rw [finrank_polarSum, Complex.finrank_real_complex]

theorem finrank_euc4 : Module.finrank ℝ Euc4 = 4 := by
  rw [finrank_polarSum, finrank_euc3]

instance fact_finrank_euc3 : Fact (Module.finrank ℝ Euc3 = 2 + 1) := ⟨finrank_euc3⟩

instance fact_finrank_euc4 : Fact (Module.finrank ℝ Euc4 = 3 + 1) := ⟨finrank_euc4⟩

instance : ConnectedSpace Sph2 := connectedSpace_raySphere (by rw [finrank_euc3]; norm_num)

instance : ConnectedSpace Sph3 := connectedSpace_raySphere (by rw [finrank_euc4]; norm_num)

/-- **`(SO(4), 𝕊³)` is an analytical structure** (`RamcovGX.tex:341`, the model of
`cex:start_singular_manifold_homeomorphic`, l.1931). -/
theorem analyticStructure_SO4 : AnalyticStructure SO4 Sph3 :=
  analyticStructure_sphere (by rw [finrank_euc4]; norm_num)

/-- **`(SO(3), 𝕊²)` is an analytical structure** (the model of spherical surfaces). -/
theorem analyticStructure_SO3 : AnalyticStructure SO3 Sph2 :=
  analyticStructure_sphere (by rw [finrank_euc3]; norm_num)

/-- `𝕊³` is locally unloopable (the standing assumption of §2.5, `RamcovGX.tex:1660`). -/
theorem isLocallyUnloopable_sph3 : IsLocallyUnloopable Sph3 :=
  isLocallyUnloopable_raySphere (n := 3)

/-- `𝕊²` is locally unloopable. -/
theorem isLocallyUnloopable_sph2 : IsLocallyUnloopable Sph2 :=
  isLocallyUnloopable_raySphere (n := 2)

/-- **`ℝ⁴ = ℝ ⊕ ℝ³` is the Euclidean `4`-space**: a linear isometry onto `EuclideanSpace ℝ (Fin 4)`
(an orthonormal basis, `finrank_euc4`). -/
def euc4Isometry : Euc4 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((stdOrthonormalBasis ℝ Euc4).reindex (finCongr finrank_euc4)).repr

/-- **`𝕊³` is the unit sphere of `ℝ⁴`**: `euc4Isometry` restricts to a homeomorphism (an isometry)
onto the unit sphere of `EuclideanSpace ℝ (Fin 4)`. -/
def sph3Homeomorph : Sph3 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 where
  toFun x := ⟨euc4Isometry x, mem_sphere_zero_iff_norm.2 (by
    rw [LinearIsometryEquiv.norm_map, norm_raySphere])⟩
  invFun y := ⟨euc4Isometry.symm y, mem_sphere_zero_iff_norm.2 (by
    rw [LinearIsometryEquiv.norm_map]; exact mem_sphere_zero_iff_norm.1 y.2)⟩
  left_inv x := Subtype.ext (euc4Isometry.symm_apply_apply x)
  right_inv y := Subtype.ext (euc4Isometry.apply_symm_apply y)
  continuous_toFun := (euc4Isometry.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (euc4Isometry.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The linear isometry `1 ⊕ A` of `ℝ ⊕ W`. -/
def liftIsom (A : W ≃ₗᵢ[ℝ] W) : PolarSum W ≃ₗᵢ[ℝ] PolarSum W where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × W)).trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr A.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℝ (ℝ × W)).symm)
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp

theorem liftIsom_apply (A : W ≃ₗᵢ[ℝ] W) (x : PolarSum W) :
    liftIsom A x = WithLp.toLp 2 (x.fst, A x.snd) := rfl

theorem liftIsom_fst (A : W ≃ₗᵢ[ℝ] W) (x : PolarSum W) : (liftIsom A x).fst = x.fst := rfl

theorem liftIsom_snd (A : W ≃ₗᵢ[ℝ] W) (x : PolarSum W) : (liftIsom A x).snd = A x.snd := rfl

theorem det_liftIsom [FiniteDimensional ℝ W] (A : W ≃ₗᵢ[ℝ] W) :
    LinearMap.det ((liftIsom A).toLinearEquiv : PolarSum W →ₗ[ℝ] PolarSum W) =
      LinearMap.det (A.toLinearEquiv : W →ₗ[ℝ] W) := by
  set e := (WithLp.linearEquiv 2 ℝ (ℝ × W)).symm
  have : ((liftIsom A).toLinearEquiv : PolarSum W →ₗ[ℝ] PolarSum W) =
      (e : (ℝ × W) →ₗ[ℝ] PolarSum W) ∘ₗ
        (LinearMap.prodMap LinearMap.id (A.toLinearEquiv : W →ₗ[ℝ] W)) ∘ₗ
          (e.symm : PolarSum W →ₗ[ℝ] (ℝ × W)) := by
    ext x; rfl
  rw [this, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

variable (W) in
/-- **The embedding `SO(W) → SO(ℝ ⊕ W)`**, `A ↦ 1 ⊕ A`: the stabiliser of the north pole (for
`W = ℝ³`: `SO(3) ⊆ SO(4)`). -/
def liftSO [FiniteDimensional ℝ W] : SpecialOrth W →* SpecialOrth (PolarSum W) where
  toFun A := ⟨liftIsom (A : W ≃ₗᵢ[ℝ] W), by
    rw [mem_specialOrth, det_liftIsom]; exact A.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem liftSO_apply [FiniteDimensional ℝ W] (A : SpecialOrth W) (x : PolarSum W) :
    ((liftSO W A : SpecialOrth (PolarSum W)) : PolarSum W ≃ₗᵢ[ℝ] PolarSum W) x =
      WithLp.toLp 2 (x.fst, (A : W ≃ₗᵢ[ℝ] W) x.snd) := rfl

end Polar

/-! ### The stereographic projection from the south pole, and the conic chart at the north pole -/

section Stereo

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The north pole `(1, 0)` of `𝕊(ℝ ⊕ W)`. -/
def northPole : RaySphere (PolarSum W) :=
  ⟨WithLp.toLp 2 (1, 0), mem_sphere_zero_iff_norm.2 (by
    have := norm_toLp_sq (1 : ℝ) (0 : W)
    rw [norm_zero] at this
    nlinarith [norm_nonneg (WithLp.toLp 2 ((1 : ℝ), (0 : W)) : PolarSum W)])⟩

theorem fst_add_one_pos_of_ne (y : RaySphere (PolarSum W)) (hy : (y : PolarSum W).fst ≠ -1) :
    0 < 1 + (y : PolarSum W).fst := by
  have h := norm_polarSum_sq (y : PolarSum W)
  rw [norm_raySphere] at h
  have hle : |(y : PolarSum W).fst| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg ‖(y : PolarSum W).snd‖]
  have := neg_abs_le (y : PolarSum W).fst
  rcases lt_or_eq_of_le (show -1 ≤ (y : PolarSum W).fst by linarith) with h1 | h1
  · linarith
  · exact absurd h1.symm hy

/-- The inverse stereographic projection `W → 𝕊(ℝ ⊕ W)` from the south pole `(-1, 0)`:
`v ↦ ((1 - |v|²)/(1 + |v|²), 2v/(1 + |v|²))`. -/
def stereoInv (v : W) : RaySphere (PolarSum W) :=
  ⟨WithLp.toLp 2 ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2), (2 / (1 + ‖v‖ ^ 2)) • v),
    mem_sphere_zero_iff_norm.2 (by
      have hp : 0 < 1 + ‖v‖ ^ 2 := by positivity
      have h := norm_toLp_sq ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2)) ((2 / (1 + ‖v‖ ^ 2)) • v)
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 2 / (1 + ‖v‖ ^ 2) by positivity)] at h
      have h1 : ‖(WithLp.toLp 2 ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2), (2 / (1 + ‖v‖ ^ 2)) • v) :
          PolarSum W)‖ ^ 2 = 1 := by
        rw [h]; field_simp; ring
      have hn := norm_nonneg (WithLp.toLp 2 ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2),
        (2 / (1 + ‖v‖ ^ 2)) • v) : PolarSum W)
      nlinarith)⟩

theorem stereoInv_fst (v : W) :
    (stereoInv v : PolarSum W).fst = (1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2) := rfl

theorem stereoInv_snd (v : W) :
    (stereoInv v : PolarSum W).snd = (2 / (1 + ‖v‖ ^ 2)) • v := rfl

theorem continuous_stereoInv : Continuous (stereoInv : W → RaySphere (PolarSum W)) := by
  refine Continuous.subtype_mk ?_ _
  refine (WithLp.prod_continuous_toLp 2 ℝ W).comp (Continuous.prodMk ?_ ?_)
  · exact (continuous_const.sub (continuous_norm.pow 2)).div
      (continuous_const.add (continuous_norm.pow 2)) fun v => by positivity
  · exact (continuous_const.div (continuous_const.add (continuous_norm.pow 2))
      fun v => (add_pos_of_pos_of_nonneg one_pos (sq_nonneg ‖v‖)).ne').smul continuous_id

/-- The stereographic projection `𝕊(ℝ ⊕ W) ∖ {S} → W` from the south pole:
`(t, w) ↦ w / (1 + t)`. -/
def stereoFun (y : RaySphere (PolarSum W)) : W :=
  (1 + (y : PolarSum W).fst)⁻¹ • (y : PolarSum W).snd

theorem stereoFun_stereoInv (v : W) : stereoFun (stereoInv v) = v := by
  have hp : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [stereoFun, stereoInv_fst, stereoInv_snd, smul_smul]
  have : (1 + (1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2))⁻¹ * (2 / (1 + ‖v‖ ^ 2)) = 1 := by
    field_simp; ring
  rw [this, one_smul]

theorem stereoInv_stereoFun (y : RaySphere (PolarSum W)) (hy : (y : PolarSum W).fst ≠ -1) :
    stereoInv (stereoFun y) = y := by
  have hpos := fst_add_one_pos_of_ne y hy
  have h := norm_polarSum_sq (y : PolarSum W)
  rw [norm_raySphere] at h
  set t := (y : PolarSum W).fst
  set w := (y : PolarSum W).snd
  have hn : ‖stereoFun y‖ ^ 2 = (1 - t) / (1 + t) := by
    rw [stereoFun, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), mul_pow]
    have : ‖w‖ ^ 2 = (1 - t) * (1 + t) := by nlinarith
    rw [this]; field_simp
  refine Subtype.ext ?_
  show WithLp.toLp 2 ((1 - ‖stereoFun y‖ ^ 2) / (1 + ‖stereoFun y‖ ^ 2),
    (2 / (1 + ‖stereoFun y‖ ^ 2)) • stereoFun y) = (y : PolarSum W)
  rw [hn]
  have e1 : (1 - (1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) = t := by
    field_simp; ring
  have e2 : (2 / (1 + (1 - t) / (1 + t))) • stereoFun y = w := by
    rw [stereoFun, smul_smul]
    have : 2 / (1 + (1 - t) / (1 + t)) * (1 + t)⁻¹ = 1 := by field_simp; ring
    rw [this, one_smul]
  rw [e1, e2]
  rfl

theorem stereoInv_fst_ne (v : W) : (stereoInv v : PolarSum W).fst ≠ -1 := by
  rw [stereoInv_fst]
  have hp : 0 < 1 + ‖v‖ ^ 2 := by positivity
  intro h
  rw [div_eq_iff hp.ne'] at h
  linarith

theorem continuousOn_stereoFun :
    ContinuousOn (stereoFun : RaySphere (PolarSum W) → W) {y | (y : PolarSum W).fst ≠ -1} := by
  have hfst : Continuous fun y : RaySphere (PolarSum W) => (y : PolarSum W).fst :=
    (WithLp.prod_continuous_ofLp 2 ℝ W |>.fst).comp continuous_subtype_val
  have hsnd : Continuous fun y : RaySphere (PolarSum W) => (y : PolarSum W).snd :=
    (WithLp.prod_continuous_ofLp 2 ℝ W |>.snd).comp continuous_subtype_val
  refine ContinuousOn.smul ?_ hsnd.continuousOn
  exact (continuous_const.add hfst).continuousOn.inv₀ fun y hy =>
    (fst_add_one_pos_of_ne y hy).ne'

/-- **The stereographic chart from the south pole**, `𝕊(ℝ ⊕ W) ∖ {S} ≅ W`. -/
def stereoChart : OpenPartialHomeomorph (RaySphere (PolarSum W)) W where
  toFun := stereoFun
  invFun := stereoInv
  source := {y | (y : PolarSum W).fst ≠ -1}
  target := univ
  map_source' _ _ := trivial
  map_target' v _ := stereoInv_fst_ne v
  left_inv' y hy := stereoInv_stereoFun y hy
  right_inv' v _ := stereoFun_stereoInv v
  open_source := isOpen_ne_fun
    ((WithLp.prod_continuous_ofLp 2 ℝ W |>.fst).comp continuous_subtype_val) continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_stereoFun
  continuousOn_invFun := continuous_stereoInv.continuousOn

theorem stereoChart_source :
    (stereoChart : OpenPartialHomeomorph (RaySphere (PolarSum W)) W).source =
      {y : RaySphere (PolarSum W) | (y : PolarSum W).fst ≠ -1} := rfl

theorem stereoChart_target :
    (stereoChart : OpenPartialHomeomorph (RaySphere (PolarSum W)) W).target = univ := rfl

theorem stereoChart_symm_apply (v : W) :
    (stereoChart : OpenPartialHomeomorph (RaySphere (PolarSum W)) W).symm v = stereoInv v := rfl

theorem stereoInv_zero : stereoInv (0 : W) = northPole := by
  refine Subtype.ext ?_
  show WithLp.toLp 2 ((1 - ‖(0 : W)‖ ^ 2) / (1 + ‖(0 : W)‖ ^ 2),
      (2 / (1 + ‖(0 : W)‖ ^ 2)) • (0 : W)) =
    WithLp.toLp 2 (1, 0)
  simp

variable [FiniteDimensional ℝ W]

/-- **Equivariance** of the inverse stereographic projection:
`(1 ⊕ A) · stereoInv v = stereoInv (A v)`. -/
theorem liftSO_smul_stereoInv (A : SpecialOrth W) (v : W) :
    liftSO W A • stereoInv v = stereoInv ((A : W ≃ₗᵢ[ℝ] W) v) := by
  refine Subtype.ext ?_
  rw [coe_specialOrth_smul, liftSO_apply]
  show WithLp.toLp 2 ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2), (A : W ≃ₗᵢ[ℝ] W) ((2 / (1 + ‖v‖ ^ 2)) • v)) =
    WithLp.toLp 2 ((1 - ‖(A : W ≃ₗᵢ[ℝ] W) v‖ ^ 2) / (1 + ‖(A : W ≃ₗᵢ[ℝ] W) v‖ ^ 2),
      (2 / (1 + ‖(A : W ≃ₗᵢ[ℝ] W) v‖ ^ 2)) • (A : W ≃ₗᵢ[ℝ] W) v)
  rw [LinearIsometryEquiv.norm_map, map_smul]

end Stereo

/-! ### The conic chart of `𝕊(ℝ ⊕ W)` at the north pole, and Thurston's suspension -/

section Thurston

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **The full conic chart of `𝕊(ℝ ⊕ W)` at the north pole, with link `𝕊(W)`**
(`RamcovGX.tex:698–700`, the suspension of `𝕊ⁿ` is `𝕊ⁿ⁺¹`): the stereographic projection from the
south pole followed by the polar homeomorphism `W ≃ₜ susp(𝕊(W))` (`GX.sphereSusp`). The point
`(σ, r)` of the cone is the point at spherical distance `2 arctan r` from the north pole in the
direction `σ`; `σ₀` is the direction assigned to the apex, immaterial since the apex is one
point. -/
def sphConic (σ₀ : RaySphere W) :
    ConicChart (RaySphere (PolarSum W)) northPole (RaySphere W) where
  φ := stereoChart.transHomeomorph (sphereSusp σ₀).symm
  mem_source := by
    show (northPole : RaySphere (PolarSum W)).1.fst ≠ -1
    show (1 : ℝ) ≠ -1
    norm_num
  map_mem_O := by
    show ‖stereoFun (northPole : RaySphere (PolarSum W))‖₊ = 0
    rw [← stereoInv_zero, stereoFun_stereoInv, nnnorm_zero]

theorem sphConic_isFull (σ₀ : RaySphere W) : (sphConic σ₀).IsFull := by
  show (sphereSusp σ₀).symm.symm ⁻¹' stereoChart.target = univ
  rw [stereoChart_target, preimage_univ]

theorem sphConic_source (σ₀ : RaySphere W) :
    (sphConic σ₀).φ.source = {y : RaySphere (PolarSum W) | (y : PolarSum W).fst ≠ -1} := rfl

theorem sphConic_symm_mk (σ₀ : RaySphere W) (q : RaySphere W × ℝ≥0) :
    (sphConic σ₀).φ.symm (Susp.mk q) = stereoInv ((q.2 : ℝ) • (q.1 : W)) := rfl

variable [FiniteDimensional ℝ W]

/-- **Radius preservation**: the inverse conic chart intertwines `A ∈ SO(W)` acting radially on
the cone and `1 ⊕ A ∈ SO(ℝ ⊕ W)`. -/
theorem sphConic_symm_smul (σ₀ : RaySphere W) (A : SpecialOrth W) (σ : RaySphere W) (t : ℝ≥0) :
    (sphConic σ₀).φ.symm (Susp.mk (A • σ, t)) =
      liftSO W A • (sphConic σ₀).φ.symm (Susp.mk (σ, t)) := by
  rw [sphConic_symm_mk, sphConic_symm_mk, liftSO_smul_stereoInv, map_smul]
  rfl

variable (σ₀ : RaySphere W) (S : Type*) [TopologicalSpace S]
  [SingularGXStructure (SpecialOrth W) (RaySphere W) S]

/-- **The cone atlas of Thurston's suspension** (`RamcovGX.tex:694–700`): the cone charts
`(σ, r) ↦ φ⁻¹(e(σ), r)` of the charts `e` of the maximal a.e. `(SO(W), 𝕊(W))`-atlas of `Σ`. -/
def thurstonAtlas : Set (OpenPartialHomeomorph (Susp S) (RaySphere (PolarSum W))) :=
  (sphConic σ₀).coneChart '' aeAtlas (SpecialOrth W) (RaySphere W) S

variable {σ₀ S}

/-- **The chart changes of Thurston's cone atlas lie in `SO(ℝ ⊕ W)`**: near every point of the
overlap of the cone charts of `e, e'`, they differ by `1 ⊕ A`, `A ∈ SO(W)` the element by which
`e` and `e'` differ. -/
theorem thurston_eventually_eq_smul {e e' : OpenPartialHomeomorph S (RaySphere W)}
    (he : e ∈ aeAtlas (SpecialOrth W) (RaySphere W) S)
    (he' : e' ∈ aeAtlas (SpecialOrth W) (RaySphere W) S) {z : Susp S}
    (hz : z ∈ ((sphConic σ₀).coneChart e).source ∩ ((sphConic σ₀).coneChart e').source) :
    ∃ A : SpecialOrth W, ∀ᶠ y in 𝓝 z,
      (sphConic σ₀).coneChart e' y = liftSO W A • (sphConic σ₀).coneChart e y := by
  rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀),
    (sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)] at hz
  obtain ⟨⟨q, ⟨hq1, hq2⟩, rfl⟩, ⟨q', ⟨hq1', hq2'⟩, hqq'⟩⟩ := hz
  obtain rfl := Susp.eq_of_mk_eq_of_pos hqq' hq2'
  obtain ⟨A, hA⟩ :=
    (isMaximalAEAtlas_aeAtlas (SpecialOrth W) (RaySphere W) S).1.1.eventually_smul_eq
      he he' hq1 hq1'
  refine ⟨A, ?_⟩
  rw [Susp.nhds_mk_of_pos hq2, Filter.eventually_map]
  filter_upwards [continuous_fst.continuousAt.eventually hA] with y hy
  rw [(sphConic σ₀).coneChart_apply, (sphConic σ₀).coneChart_apply, hy, sphConic_symm_smul]

/-- Thurston's cone atlas is a `(SO(ℝ ⊕ W), 𝕊(ℝ ⊕ W))`-atlas. -/
theorem isGXAtlas_thurstonAtlas :
    IsGXAtlas (SpecialOrth (PolarSum W)) (thurstonAtlas σ₀ S) := by
  refine isGXAtlas_of_eventually ?_
  rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ z hz
  obtain ⟨A, hA⟩ := thurston_eventually_eq_smul he he' hz
  exact ⟨liftSO W A, hA⟩

/-- The support of Thurston's cone atlas is `susp*(Reg Σ)`, the rays over the regular points. -/
theorem support_thurstonAtlas :
    support (thurstonAtlas σ₀ S) = Susp.mk '' (Reg (SpecialOrth W) (RaySphere W) S ×ˢ Ioi 0) := by
  ext z
  rw [mem_support]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hz⟩
    rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)] at hz
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hz
    exact ⟨q, ⟨mem_support.2 ⟨e, he, hq1⟩, hq2⟩, rfl⟩
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    obtain ⟨e, he, hqe⟩ := mem_support.1 hq1
    refine ⟨(sphConic σ₀).coneChart e, ⟨e, he, rfl⟩, ?_⟩
    rw [(sphConic σ₀).coneChart_source_of_isFull (sphConic_isFull σ₀)]
    exact ⟨q, ⟨hqe, hq2⟩, rfl⟩

/-- **Thurston's suspension of a singular `(SO(W), 𝕊(W))`-manifold is an almost everywhere
`(SO(ℝ ⊕ W), 𝕊(ℝ ⊕ W))`-atlas** on `susp(Σ)` (`RamcovGX.tex:694–700` and l.1931: "we may either
apply Proposition `prop:susp_portly` or check that directly"): its chart changes lie in the group
(`thurston_eventually_eq_smul`) and its support `susp*(Reg Σ)` is portly by `prop:susp_portly`
(`GX.Susp.isPortly_image_mk`), `Σ` connected and locally connected. -/
theorem isAEAtlas_thurstonAtlas [PreconnectedSpace S] [LocallyConnectedSpace S] :
    IsAEAtlas (SpecialOrth (PolarSum W)) (thurstonAtlas σ₀ S) := by
  refine ⟨isGXAtlas_thurstonAtlas, ?_⟩
  rw [support_thurstonAtlas]
  exact Susp.isPortly_image_mk (isPortly_reg (SpecialOrth W) (RaySphere W) S)

variable (σ₀ S) in
/-- **Thurston's suspension** `susp(Σ)` of a connected, locally connected singular
`(SO(W), 𝕊(W))`-manifold, as a singular `(SO(ℝ ⊕ W), 𝕊(ℝ ⊕ W))`-manifold: the maximal a.e. atlas
generated by the cone atlas (`cor:maximal_atlas`). For `W = ℝ³` it is a singular
`(SO(4), 𝕊³)`-manifold (`RamcovGX.tex:1931`). -/
@[reducible] def thurstonStructure [PreconnectedSpace S] [LocallyConnectedSpace S] :
    SingularGXStructure (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) :=
  ⟨maximalAEAtlas (SpecialOrth (PolarSum W)) (thurstonAtlas σ₀ S),
    isAEAtlas_thurstonAtlas.isMaximalAEAtlas_maximalAEAtlas⟩

/-- **The ray over a regular point is regular** in Thurston's suspension:
`susp*(Reg Σ) ⊆ Reg(susp Σ)` (`RamcovGX.tex:740`, "the image of regular manifolds are regular
except possibly at `O`"). -/
theorem thurston_mk_mem_reg [PreconnectedSpace S] [LocallyConnectedSpace S] {x : S}
    (hx : x ∈ Reg (SpecialOrth W) (RaySphere W) S) {t : ℝ≥0} (ht : 0 < t) :
    letI := thurstonStructure σ₀ S
    Susp.mk (x, t) ∈ Reg (SpecialOrth (PolarSum W)) (RaySphere (PolarSum W)) (Susp S) := by
  letI := thurstonStructure σ₀ S
  refine support_mono (isAEAtlas_thurstonAtlas (σ₀ := σ₀) (S := S)).subset_maximalAEAtlas ?_
  rw [support_thurstonAtlas]
  exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩

end Thurston

end GX
