import GX.Spherical.S3Model
import GX.SingularII.Models

/-!
# Spherical cone surfaces: the cone `C_θ` and cone points of angle `θ`

Target `T-gx-spherical-cone` (`roadmap/roadmap.toml`; DEC-136, its first step). `papers/gx`: the
surfaces `Σ` of `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930`) and the local
models of Thurston's method in dimension `2` (`sec:susp`, l.693–703). **No label is marked
here**; 0 `sorry`.

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial (row stays partial
  until `T-gx-troyanov`): the objects "singular `𝕊²`-manifold homeomorphic to a sphere with `s`
  conical singularities of respective angles `θ_i`" are defined here, `GX.IsConeSphere`.
* **The polar cone** (a port of `GX.conical`, `ex:conical`, l.347, from the model `ℂ × Z` to any
  analytical `(G, X)` with an open embedding `j : ℂ → X` conjugating the rotation of angle `α` to
  some `ρ ∈ G`): `GX.polarCone` — `Γ₁\𝔻_∞` carries a unique maximal a.e. `(G,X)`-structure
  developed by `GX.polarConeDev j α` (holonomy `ρ`, `GX.polarConeDev_smul`), regular off the apex,
  **the apex singular iff `α ≠ 2π`**.
* **The spherical cone `C_θ`**, `θ > 0` (`GX.ConeAngle`): `GX.SphCone θ`, homeomorphic to `ℂ`
  (`GX.SphCone.homeoComplex`; Hausdorff, connected, locally connected, second countable), with the
  singular `(SO(3), 𝕊²)`-structure developed by `GX.sphConeDev θ = stereoInv(r e^{iθφ})`, holonomy
  the rotation `GX.rotSO3 (e^{iθ})` about the polar axis: `GX.SphCone.mk_mem_reg`,
  `GX.SphCone.apex_mem_sing_iff` (the apex is singular iff `θ ≠ 2π`), `GX.SphCone.sing_eq`
  (`sing C_θ = {apex}`, `θ ≠ 2π`), `GX.SphCone.sing_eq_empty` (`C_{2π}` is regular).
* **Cone points of angle `θ`**: `GX.IsConePoint θ x`, gx's `HasXAType` (`def:atlas`, l.1905) for
  the family `(C_θ)` with `S_θ = {apex}`; `GX.isConePoint_apex`; `GX.IsConePoint.mem_sing`,
  `GX.IsConePoint.mem_reg`, `GX.IsConePoint.mem_sing_iff` (singular iff `θ ≠ 2π`); **the angle is
  unique**, `GX.IsConePoint.angle_eq`.
* **The cone angle is an invariant of the apex**: `GX.sphCone_eq_of_iso` (an a.e. isomorphism of
  open subsets of `C_θ`, `C_θ'` whose domain contains the apex of `C_θ`, `θ ≠ 2π`, forces
  `θ = θ'`: the `eq_of_iso` half of the analyticity of `(C_θ)_{θ ≠ 2π}`), through
  `GX.sphCone_exists_int_mul` (the isomorphism, lifted through `exp` on a punctured neighbourhood
  and read by the developing maps, gives `θ ∈ θ'ℤ`); the tools `GX.exists_rot_of_smul_northPole`
  (an element of `SO(3)` fixing the north pole is a rotation about the polar axis),
  `GX.sphCone_chart_dev` (the charts of `C_θ` read on its cover are translates of `sphConeDev θ`),
  `GX.eq_of_continuous_intValued`.
* **Cone surfaces**: `GX.IsSphericalConeSurface M` (every singular point a cone point);
  `GX.IsConeSphere M θ p` (`M ≃ₜ 𝕊²`, distinct cone points `p_i` of angles `θ_i`, no other
  singular point); `GX.IsConeSphere.sing_eq` (`sing M = {p_i : θ_i ≠ 2π}`),
  `GX.IsConeSphere.isConePoint_iff` (the angles are invariants),
  `GX.IsConeSphere.isSphericalConeSurface`, `.connectedSpace`, `.locallyConnectedSpace`,
  `.t2Space`, `.compactSpace`; witness `GX.isConeSphere_sph2` (the round sphere, `s = 0`).

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. (l.1930)
>
> Assume you have constructed local models of singularities in $(\SS^n,\SO(n+1))$-manifolds. A
> $(\SS^n,\SO(n+1))$-manifolds with conical singularities is then a metric space locally isometric
> to either of local models. (l.694)
>
> This way, we obtain usual conical singularities in dimension 2, then so-called "collisions" of
> conical lines in dimension 3, etc. (l.703)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| "singular `𝕊²`-manifold" (l.1930) | ✓ a singular `(SO(3), 𝕊²)`-manifold, `[SingularGXStructure SO3 Sph2 M]` |
| "conical singularity of angle `θ`" / "locally isometric to either of local models" (l.694) | ✓ read (SCOPE (a)): a chart onto a neighbourhood of the apex of `C_θ`, an a.e. isomorphism (`IsConePoint`) |
| the local model: suspension of a circle of length `θ`, `dr² + sin²r dφ²` (l.693–700, `n = 1`) | ⚠ read (SCOPE (b)): `Γ₁\𝔻_∞` developed by the spherical cone map |
| "homeomorphic to a sphere" (l.1930) | ✓ `M ≃ₜ 𝕊²` |
| the angles are well defined (implicit in "of respective angles") | ✓ proved: `IsConePoint.angle_eq`, from `sphCone_eq_of_iso` |
| `def:family_singular_manifolds_endowed`: `U₁`, `U₂` connected | ⚠ weakened: not used by `sphCone_eq_of_iso` |

## SCOPE (disclosed)

* **(a)** "Conical singularity of angle `θ`" is read in gx's framework (the dispatch's "singular
  `(SO(3), 𝕊²)`-structures with cone points"): `x` has an `X_θ`-chart (`def:atlas`) for the family
  of spherical cones. The regular part is locally `𝕊²` through the a.e. `(SO(3), 𝕊²)`-atlas, whose
  chart changes are isometries; the metric itself is not formalized. The family `(C_θ)_{θ > 0}`,
  `S_θ = {apex}`, is not an analytic family in the sense of l.1899 (`S_{2π} ⊄ sing C_{2π} = ∅`;
  the `exists_aut` half is unproved), so `IsConePoint` is the chart condition of `def:atlas`
  without its standing hypothesis; restricted to `θ ≠ 2π`, the `eq_of_iso` half is
  `sphCone_eq_of_iso`.
* **(b)** `C_θ` is the quotient `Γ₁\𝔻_∞` of `ex:quotient_base`, developed by the inverse
  stereographic image of the Euclidean cone of angle `θ` (`GX.conicalDev`): the point at radius
  `r` and angle `φ` goes to the point of `𝕊²` at spherical distance `2 arctan r` from the north
  pole, at longitude `θφ` — the paper's suspension of a circle of length `θ` with
  `ρ = 2 arctan r ∈ [0, π)` (the reading of `GX.Spherical.S3Model`, SCOPE (b)). It is not
  built as `GX.thurstonStructure` of a circle, which would need the `(SO(2), 𝕊¹)`-structure of the
  circle of length `θ`.
* **(c)** An angle `θ_i = 2π` is allowed and marks a regular point (`IsConePoint.mem_reg`):
  Troyanov's condition admits it (`GX.troyanovAngleCondition_two_pi`, in
  `GXScaffold.Spherical.TroyanovAngles`), though the paper speaks of "`s` conical singularities".
* **(d)** `GX.sphCone_eq_of_iso` is the `eq_of_iso` half of the analyticity of the family
  `(C_θ)_{θ ≠ 2π}` (`def:family_singular_manifolds_endowed`), proved directly (the lifting step of
  B21 Prop 1.3, `GX.cyl_lift`, is built for Minkowski space only; here the lift goes through the
  covering `exp : ℂ → ℂ*`, mathlib's `IsCoveringMapOn.existsUnique_continuousMap_lifts`). The
  `exists_aut` half (every such isomorphism is the restriction of a rotation about the apex) is
  not stated, so `IsAnalyticModelFamily` for the spherical cones is not stated either.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.S3Model`, `GX.Singular.Quotient` (`𝔻_∞`, `quotientBase`, `conicalDev`),
`GX.SingularII.Models` (`XAChart`, `HasXAType`).
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### Conical models over a polar chart (a port of `GX.conical` to any model `X`) -/

section PolarCone

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- **The developing map of a cone of angle `α` read through a polar chart `j : ℂ → X`**: on the
universal cover `{r > 0} ⊆ 𝔻_∞` of the punctured cone, `(r, θ) ↦ j(r e^{iαθ})` (with `θ ∈ ℝ`
the angle unrolled, period `1`). For `j` the inverse stereographic projection `ℂ → 𝕊²`, this is
the spherical cone of angle `α`. -/
def polarConeDev (j : ℂ → X) (α : ℝ) (x : DInfty × Unit) : X := j (conicalDev α Unit x).1

theorem isLocalHomeomorphOn_polarConeDev {j : ℂ → X} (hj : IsOpenEmbedding j) {α : ℝ}
    (hα : α ≠ 0) : IsLocalHomeomorphOn (polarConeDev j α) (cylPos Unit) := by
  have hg : IsLocalHomeomorph (fun w : ℂ × Unit => j w.1) :=
    hj.isLocalHomeomorph.comp (Homeomorph.prodPUnit ℂ).isLocalHomeomorph
  exact (hg.isLocalHomeomorphOn (s := univ)).comp (isLocalHomeomorphOn_conicalDev hα)
    (mapsTo_univ _ _)

/-- The powers of the rotation `ρ` read in the polar chart. -/
theorem zpow_smul_polar {j : ℂ → X} {α : ℝ} {ρ : G}
    (hρ : ∀ w : ℂ, ρ • j w = j (Complex.exp (α * Complex.I) * w)) (n : ℤ) (w : ℂ) :
    (ρ ^ n) • j w = j (Complex.exp ((n * α : ℝ) * Complex.I) * w) := by
  induction n using Int.induction_on generalizing w with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, mul_smul, hρ, ih, ← mul_assoc, ← Complex.exp_add]
    congr 3; push_cast; ring
  | pred n ih =>
    rw [zpow_sub_one, mul_smul]
    have hinv : ρ⁻¹ • j w = j (Complex.exp (-(α * Complex.I)) * w) := by
      rw [inv_smul_eq_iff, hρ, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
        one_mul]
    rw [hinv, ih, ← mul_assoc, ← Complex.exp_add]
    congr 3; push_cast; ring

/-- The holonomy of the polar cone: the deck generator `θ ↦ θ + 1` is read as `ρ`. -/
theorem polarConeDev_smul {j : ℂ → X} {α : ℝ} (hα : α ≠ 0) {ρ : G}
    (hρ : ∀ w : ℂ, ρ • j w = j (Complex.exp (α * Complex.I) * w)) (k : GammaA 1)
    (x : DInfty × Unit) :
    polarConeDev j α (k • x) = (ρ ^ k.toInt) • polarConeDev j α x := by
  rw [polarConeDev, polarConeDev, conicalDev_smul hα, zpow_smul_polar hρ]

/-- The pulled-back a.e. atlas of the polar cone's cover. -/
abbrev polarConeAtlas (G : Type*) [Group G] [MulAction G X] (j : ℂ → X) (α : ℝ) :
    Set (OpenPartialHomeomorph (DInfty × Unit) X) :=
  maximalAEAtlas G (devAtlas G (polarConeDev j α) (cylPos Unit))

variable [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]

/-- `Γ_1` acts on the cover of the polar cone by a.e. `(G,X)`-morphisms. -/
theorem polarCone_isAEMorphism_smul {j : ℂ → X} (hj : IsOpenEmbedding j) {α : ℝ} (hα : α ≠ 0)
    {ρ : G} (hρ : ∀ w : ℂ, ρ • j w = j (Complex.exp (α * Complex.I) * w)) (k : GammaA 1) :
    IsAEMorphismOf G (polarConeAtlas G j α) (polarConeAtlas G j α)
      fun x : DInfty × Unit => k • x :=
  isAEMorphismOf_devStructure (DInfty.isPortly_pos Unit) (isLocalHomeomorphOn_polarConeDev hj hα)
    (DInfty.continuous_smul_prod k)
    (fun x hx => by
      show 0 < (k • x.1).r
      rw [DInfty.smul_def, DInfty.rot_r]; exact hx)
    fun x _ => ⟨ρ ^ k.toInt, Eventually.of_forall fun y => polarConeDev_smul hα hρ k y⟩

/-- **The polar cone of angle `α`** (`ex:conical`, `RamcovGX.tex:347`, read in a polar chart of
any analytical `(G, X)`): the quotient `Γ_1\(𝔻_∞ × {*}) ≅ ℂ` carries a unique maximal a.e.
`(G,X)`-structure making the projection an a.e. morphism; its regular locus contains
`{r > 0}`; and **the apex is singular iff `α ≠ 2π`**. A port of `GX.conical`, whose model is
`ℂ × Z` itself; here `j : ℂ → X` is any open embedding conjugating the rotation of angle `α` to
some `ρ ∈ G`. -/
theorem polarCone {j : ℂ → X} (hj : IsOpenEmbedding j) {α : ℝ} (hα : 0 < α) (ρ : G)
    (hρ : ∀ w : ℂ, ρ • j w = j (Complex.exp (α * Complex.I) * w)) :
    (∃! B : Set (OpenPartialHomeomorph (Orbits (GammaA 1) (DInfty × Unit)) X),
      IsMaximalAEAtlas G B ∧ IsAEMorphismOf G (polarConeAtlas G j α) B (orbitMk (GammaA 1))) ∧
    ∀ B : Set (OpenPartialHomeomorph (Orbits (GammaA 1) (DInfty × Unit)) X),
      IsMaximalAEAtlas G B → IsAEMorphismOf G (polarConeAtlas G j α) B (orbitMk (GammaA 1)) →
      orbitMk (GammaA 1) '' cylPos Unit ⊆ support B ∧
      (orbitMk (GammaA 1) (DInfty.apex, ()) ∈ support B ↔ α = 2 * π) := by
  have hα0 : α ≠ 0 := hα.ne'
  have hP := DInfty.isPortly_pos Unit
  have hD := isLocalHomeomorphOn_polarConeDev hj hα0
  have hΓ := polarCone_isAEMorphism_smul (G := G) hj hα0 hρ
  have hex := quotientBase one_ne_zero hD hΓ
  refine ⟨hex, fun B hB hπ => ?_⟩
  have hsub : orbitMk (GammaA 1) '' cylPos Unit ⊆ support B := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra h
    obtain ⟨y, hy, hxy⟩ := quotientBase_sing_subset one_ne_zero hD hB hπ h
    obtain ⟨k, rfl⟩ := exists_smul_eq_of_orbitMk_eq hxy
    have : (k • y).1.r = y.1.r := by rw [DInfty.smul_prod_def, DInfty.smul_def, DInfty.rot_r]
    have hy' : y.1.r = 0 := hy
    exact absurd hx (by show ¬ 0 < (k • y).1.r; rw [this, hy']; exact lt_irrefl 0)
  refine ⟨hsub, ⟨fun hmem => ?_, fun h2 => ?_⟩⟩
  · -- the apex is singular when `α ≠ 2π`
    by_contra hα2
    obtain ⟨φ, hφ, hφs⟩ := mem_support.1 hmem
    have hO : orbitMk (GammaA 1) ⁻¹' φ.source ∈ 𝓝 ((DInfty.apex, ()) : DInfty × Unit) :=
      continuous_quot_mk.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hφs)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hO
    obtain ⟨ε, hε, hεu⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 hu
    set S : Set (DInfty × Unit) := {p : DInfty | 0 < p.r ∧ p.r < ε} ×ˢ univ
    have hSc : IsPreconnected S :=
      (DInfty.isPreconnected_pos_r_lt ε).prod isPreconnected_univ
    have hSP : S ⊆ cylPos Unit := fun y hy => hy.1.1
    have hvU : ∀ z : Unit, z ∈ v := fun z => by
      cases z; exact mem_of_mem_nhds hv
    have hSO : ∀ y ∈ S, orbitMk (GammaA 1) y ∈ φ.source := fun y hy =>
      huv ⟨hεu hy.1.2, hvU y.2⟩
    have hdev := isAEAtlas_devAtlas (G := G) hP hD
    have hreg := hπ.regLocusOf_eq hdev.maximalAEAtlas hB.1
    have hloc : ∀ y ∈ S, ∃ g : G, ∀ᶠ y' in 𝓝 y,
        φ (orbitMk (GammaA 1) y') = g • polarConeDev j α y' := by
      intro y hy
      have hyR : y ∈ regLocusOf G (polarConeAtlas G j α) B (orbitMk (GammaA 1)) := by
        rw [hreg]
        exact ⟨subset_support_devStructure hP hD (hSP hy), mem_support.2 ⟨φ, hφ, hSO y hy⟩⟩
      have hys : y ∈ support (devAtlas G (polarConeDev j α) (cylPos Unit)) := by
        rw [support_devAtlas hP.isOpen hD]; exact hSP hy
      obtain ⟨e, he, hye⟩ := mem_support.1 hys
      obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := G) _ _ _).exists_smul_eq y hyR e
        (hdev.subset_maximalAEAtlas he) φ hφ hye (hSO y hy)
      obtain ⟨h, hh⟩ := he.2 y hye
      refine ⟨g * h⁻¹, ?_⟩
      filter_upwards [hg, hh] with y' h1 h2
      rw [h1, h2, mul_smul, inv_smul_smul]
    obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn hP.isOpen hD hSc hSP hloc
    have hr : (0 : ℝ) < ε / 2 := half_pos hε
    have hmemS : ∀ θ : ℝ, (DInfty.posEmb ⟨(ε / 2, θ), hr⟩, ()) ∈ S := fun θ =>
      ⟨⟨hr, show ε / 2 < ε by linarith⟩, mem_univ _⟩
    have hφS : ∀ θ : ℝ, φ (orbitMk (GammaA 1) (DInfty.posEmb ⟨(ε / 2, θ), hr⟩, ())) =
        g • j ((((ε / 2 : ℝ) : ℂ) * Complex.exp ((α * θ : ℝ) * Complex.I))) := fun θ => by
      rw [hg _ (hmemS θ), polarConeDev, conicalDev_posEmb hα0]
    -- step 1: `e^{iα} = 1`
    have h1 : orbitMk (GammaA 1) (DInfty.posEmb ⟨(ε / 2, 0 + ((GammaA.ofInt 1 : GammaA 1).toInt
        : ℝ)), hr⟩, ()) = orbitMk (GammaA 1) (DInfty.posEmb ⟨(ε / 2, 0), hr⟩, ()) := by
      rw [← gammaOne_smul_posEmb, orbitMk_smul]
    have h1' := congrArg φ h1
    rw [hφS, hφS, smul_left_cancel_iff] at h1'
    have h1'' := hj.injective h1'
    have hne : (((ε / 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have he1 : Complex.exp (α * Complex.I) = 1 := by
      simp only [GammaA.toInt_ofInt, Int.cast_one, zero_add, mul_one, mul_zero,
        Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1''
      exact mul_left_cancel₀ hne (by rw [mul_one]; exact h1'')
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 he1
    have hm' : α = m * (2 * π) := by
      have := congrArg Complex.im hm
      simpa using this
    have hm1 : 1 ≤ m := by
      by_contra hlt
      have : (m : ℝ) ≤ 0 := by exact_mod_cast (by omega : m ≤ 0)
      nlinarith [Real.pi_pos]
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : m = 1 := by omega
      exact hα2 (by rw [hm', this]; simp)
    -- step 2: the points at angles `0` and `1/m` have the same image under `φ`
    have hθ : α * (1 / m : ℝ) = 2 * π := by
      rw [hm']; field_simp
    have h2 : φ (orbitMk (GammaA 1) (DInfty.posEmb ⟨(ε / 2, 1 / m), hr⟩, ())) =
        φ (orbitMk (GammaA 1) (DInfty.posEmb ⟨(ε / 2, 0), hr⟩, ())) := by
      rw [hφS, hφS, hθ]
      simp [Complex.exp_two_pi_mul_I]
    have h3 := φ.injOn (hSO _ (hmemS _)) (hSO _ (hmemS _)) h2
    obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq h3.symm
    rw [gammaOne_smul_posEmb, Prod.mk.injEq, DInfty.ext_iff] at hk
    have hk2 : (k.toInt : ℝ) = 1 / m := by simpa using hk.1.2
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlt1 : (k.toInt : ℝ) < 1 := by
      rw [hk2, div_lt_one hmpos]; exact_mod_cast (by omega : 1 < m)
    have hgt0 : (0 : ℝ) < k.toInt := by rw [hk2]; positivity
    have : k.toInt < 1 := by exact_mod_cast hlt1
    have : 0 < k.toInt := by exact_mod_cast hgt0
    omega
  · -- the apex is regular when `α = 2π`: the developing map descends to the open embedding
    -- `ψ = j ∘ (cylindrical coordinates)`
    have hβ : 2 * π / α = 1 := by rw [h2, div_self (by positivity)]
    set c := cylHomeomorph (one_ne_zero : (1 : ℝ) ≠ 0) Unit
    have hψe : IsOpenEmbedding (fun q : Orbits (GammaA 1) (DInfty × Unit) => j (c q).1) :=
      hj.comp ((Homeomorph.prodPUnit ℂ).isOpenEmbedding.comp c.isOpenEmbedding)
    haveI : Nonempty (Orbits (GammaA 1) (DInfty × Unit)) := ⟨orbitMk (GammaA 1) (DInfty.apex, ())⟩
    set ψ := hψe.toOpenPartialHomeomorph _
    have hψs : ψ.source = univ := hψe.toOpenPartialHomeomorph_source _
    have hψ : ∀ x ∈ cylPos Unit, ψ (orbitMk (GammaA 1) x) = polarConeDev j α x := by
      intro x _
      rw [hψe.toOpenPartialHomeomorph_apply]
      show j (c (orbitMk (GammaA 1) x)).1 = j (conicalDev α Unit x).1
      rw [cylHomeomorph_apply, conicalDev, hβ]
    set A₁ : Set (OpenPartialHomeomorph (Orbits (GammaA 1) (DInfty × Unit)) X) := {ψ}
    have hA₁s : support A₁ = univ :=
      eq_univ_of_forall fun x => mem_support.2 ⟨_, rfl, by rw [hψs]; exact mem_univ x⟩
    have hA₁ : IsAEAtlas G A₁ := by
      refine ⟨isGXAtlas_of_eventually fun e he e' he' x _ => ?_, by rw [hA₁s]; exact isPortly_univ⟩
      rw [mem_singleton_iff] at he he'
      subst he he'
      exact ⟨1, Eventually.of_forall fun _ => (one_smul _ _).symm⟩
    have hdev := isAEAtlas_devAtlas (G := G) hP hD
    have hm := hdev.maximalAEAtlas
    have hmor₁ : IsAEMorphismOf G (polarConeAtlas G j α) (maximalAEAtlas G A₁)
        (orbitMk (GammaA 1)) := by
      refine (isAEMorphismOf_iff hA₁.maximalAEAtlas).2 ⟨continuous_quot_mk, cylPos Unit, hP,
        IsRegularOn.of_exists hm.1 hA₁.maximalAEAtlas.1 hP.isOpen
          (subset_support_devStructure hP hD) (fun x _ => support_mono hA₁.subset_maximalAEAtlas
            (by rw [hA₁s]; exact mem_univ _)) continuous_quot_mk.continuousOn fun x hx => ?_⟩
      have hxs : x ∈ support (devAtlas G (polarConeDev j α) (cylPos Unit)) := by
        rw [support_devAtlas hP.isOpen hD]; exact hx
      obtain ⟨e, he, hxe⟩ := mem_support.1 hxs
      obtain ⟨g, hg⟩ := he.2 x hxe
      refine ⟨e, hdev.subset_maximalAEAtlas he, _, hA₁.subset_maximalAEAtlas rfl, hxe,
        by rw [hψs]; exact mem_univ _, g, ?_⟩
      filter_upwards [hg, hP.isOpen.mem_nhds hx] with y hy hyP
      rw [← hy]; exact hψ y hyP
    have heq : B = maximalAEAtlas G A₁ :=
      hex.unique ⟨hB, hπ⟩ ⟨hA₁.isMaximalAEAtlas_maximalAEAtlas, hmor₁⟩
    rw [heq]
    exact support_mono hA₁.subset_maximalAEAtlas (by rw [hA₁s]; exact mem_univ _)

end PolarCone

/-! ### The spherical cone `C_θ` -/

section SphCone

/-- The rotation `w ↦ a w` of `ℂ`, as an element of `SO(ℂ) = SO(2)`. -/
def rotSO2 (a : Circle) : SpecialOrth ℂ := ⟨rotation a, det_rotation a⟩

/-- **The rotation of `𝕊²` of angle `arg a` about the polar axis**, `1 ⊕ rot(a) ∈ SO(3)`. -/
def rotSO3 (a : Circle) : SO3 := liftSO ℂ (rotSO2 a)

theorem rotSO3_smul_stereoInv (a : Circle) (w : ℂ) :
    rotSO3 a • stereoInv w = stereoInv ((a : ℂ) * w) := by
  rw [rotSO3, liftSO_smul_stereoInv]; rfl

theorem isOpenEmbedding_stereoInv {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    IsOpenEmbedding (stereoInv : W → RaySphere (PolarSum W)) :=
  (stereoChart (W := W)).symm.to_isOpenEmbedding stereoChart_target

/-- The cone angles: the positive reals. -/
abbrev ConeAngle : Type := {θ : ℝ // 0 < θ}

/-- **The spherical cone `C_θ`** (`RamcovGX.tex:694–700` for `n = 1`: the suspension of a circle of
length `θ` with the metric `dr² + sin²r dφ²`, `r < π`), as a space: `Γ₁\𝔻_∞ ≅ ℂ`, the same for all
`θ`; the angle is carried by its singular `(SO(3), 𝕊²)`-structure, developed by
`(r, φ) ↦ stereoInv(r e^{iθφ})` (`sphConeDev`). -/
def SphCone (_θ : ConeAngle) : Type := Orbits (GammaA 1) (DInfty × Unit)

instance (θ : ConeAngle) : TopologicalSpace (SphCone θ) :=
  inferInstanceAs (TopologicalSpace (Orbits (GammaA 1) (DInfty × Unit)))

/-- The developing map of `C_θ` on its cover: the spherical cone of angle `θ`, the inverse
stereographic image of the Euclidean cone `GX.conicalDev`. -/
abbrev sphConeDev (θ : ℝ) : DInfty × Unit → Sph2 := polarConeDev stereoInv θ

/-- The model facts of `C_θ`, from `polarCone`: `ρ_θ` is the rotation of angle `θ` about the
polar axis. -/
theorem sphCone_spec (θ : ConeAngle) :
    (∃! B : Set (OpenPartialHomeomorph (Orbits (GammaA 1) (DInfty × Unit)) Sph2),
      IsMaximalAEAtlas SO3 B ∧
        IsAEMorphismOf SO3 (polarConeAtlas SO3 stereoInv θ.1) B (orbitMk (GammaA 1))) ∧
    ∀ B : Set (OpenPartialHomeomorph (Orbits (GammaA 1) (DInfty × Unit)) Sph2),
      IsMaximalAEAtlas SO3 B →
      IsAEMorphismOf SO3 (polarConeAtlas SO3 stereoInv θ.1) B (orbitMk (GammaA 1)) →
      orbitMk (GammaA 1) '' cylPos Unit ⊆ support B ∧
      (orbitMk (GammaA 1) (DInfty.apex, ()) ∈ support B ↔ θ.1 = 2 * π) :=
  polarCone (G := SO3) isOpenEmbedding_stereoInv θ.2 (rotSO3 (Circle.exp θ.1)) fun w => by
    rw [rotSO3_smul_stereoInv, Circle.coe_exp]

/-- The maximal a.e. `(SO(3), 𝕊²)`-atlas of `C_θ`: the unique one making the projection
`𝔻_∞ → C_θ` an a.e. morphism for the structure developed by `sphConeDev θ`. -/
def sphConeAtlas (θ : ConeAngle) : Set (OpenPartialHomeomorph (SphCone θ) Sph2) :=
  (sphCone_spec θ).1.exists.choose

instance (θ : ConeAngle) : SingularGXStructure SO3 Sph2 (SphCone θ) :=
  ⟨sphConeAtlas θ, (sphCone_spec θ).1.exists.choose_spec.1⟩

/-- The projection `𝔻_∞ × {*} → C_θ`. -/
def SphCone.mk (θ : ConeAngle) (x : DInfty × Unit) : SphCone θ := orbitMk (GammaA 1) x

/-- **The apex** of `C_θ`. -/
def SphCone.apex (θ : ConeAngle) : SphCone θ := SphCone.mk θ (DInfty.apex, ())

/-- The projection is an a.e. `(SO(3), 𝕊²)`-morphism from the developed structure of the cover:
`C_θ` is developed by `sphConeDev θ`. -/
theorem sphCone_isAEMorphism_mk (θ : ConeAngle) :
    IsAEMorphismOf SO3 (polarConeAtlas SO3 stereoInv θ.1) (aeAtlas SO3 Sph2 (SphCone θ))
      (SphCone.mk θ) :=
  (sphCone_spec θ).1.exists.choose_spec.2

/-- **The points off the apex are regular** in `C_θ`. -/
theorem SphCone.mk_mem_reg (θ : ConeAngle) {x : DInfty × Unit} (hx : 0 < x.1.r) :
    SphCone.mk θ x ∈ Reg SO3 Sph2 (SphCone θ) :=
  ((sphCone_spec θ).2 _ (isMaximalAEAtlas_aeAtlas SO3 Sph2 (SphCone θ))
    (sphCone_isAEMorphism_mk θ)).1 ⟨x, hx, rfl⟩

/-- **The apex of `C_θ` is singular iff `θ ≠ 2π`** (`ex:conical`'s "cannot be extended except for
`α = 2π`", in `𝕊²`). -/
theorem SphCone.apex_mem_sing_iff (θ : ConeAngle) :
    SphCone.apex θ ∈ Sing SO3 Sph2 (SphCone θ) ↔ θ.1 ≠ 2 * π :=
  not_congr ((sphCone_spec θ).2 _ (isMaximalAEAtlas_aeAtlas SO3 Sph2 (SphCone θ))
    (sphCone_isAEMorphism_mk θ)).2

theorem SphCone.eq_apex_of_not_pos (θ : ConeAngle) (x : DInfty × Unit) (hx : ¬ 0 < x.1.r) :
    SphCone.mk θ x = SphCone.apex θ := by
  obtain ⟨p, u⟩ := x
  have : p = DInfty.apex := DInfty.eq_apex_of_not_pos hx
  subst this; cases u; rfl

/-- **`sing(C_θ) = {apex}` for `θ ≠ 2π`.** -/
theorem SphCone.sing_eq (θ : ConeAngle) (hθ : θ.1 ≠ 2 * π) :
    Sing SO3 Sph2 (SphCone θ) = {SphCone.apex θ} := by
  ext y
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
  constructor
  · intro hy
    by_cases hx : 0 < x.1.r
    · exact absurd (SphCone.mk_mem_reg θ hx) hy
    · exact SphCone.eq_apex_of_not_pos θ x hx
  · intro hy
    rw [mem_singleton_iff] at hy
    rw [hy]
    exact (SphCone.apex_mem_sing_iff θ).2 hθ

/-- **`C_{2π}` is regular**: `sing(C_{2π}) = ∅`. -/
theorem SphCone.sing_eq_empty (θ : ConeAngle) (hθ : θ.1 = 2 * π) :
    Sing SO3 Sph2 (SphCone θ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
  by_cases hx : 0 < x.1.r
  · exact hy (SphCone.mk_mem_reg θ hx)
  · have h := SphCone.eq_apex_of_not_pos θ x hx
    have : SphCone.apex θ ∈ Sing SO3 Sph2 (SphCone θ) := h ▸ hy
    exact (SphCone.apex_mem_sing_iff θ).1 this hθ

/-- `C_θ ≅ ℂ`, the apex to `0` (cylindrical coordinates). -/
def SphCone.homeoComplex (θ : ConeAngle) : SphCone θ ≃ₜ ℂ :=
  (cylHomeomorph (one_ne_zero : (1 : ℝ) ≠ 0) Unit).trans (Homeomorph.prodPUnit ℂ)

instance (θ : ConeAngle) : T2Space (SphCone θ) := (SphCone.homeoComplex θ).isEmbedding.t2Space

instance (θ : ConeAngle) : LocallyConnectedSpace (SphCone θ) :=
  (SphCone.homeoComplex θ).locallyConnectedSpace

instance (θ : ConeAngle) : SecondCountableTopology (SphCone θ) :=
  (SphCone.homeoComplex θ).isEmbedding.secondCountableTopology

instance (θ : ConeAngle) : ConnectedSpace (SphCone θ) :=
  (SphCone.homeoComplex θ).symm.surjective.connectedSpace (SphCone.homeoComplex θ).symm.continuous

end SphCone

/-! ### The cone angle is an invariant of the apex -/

section AngleInvariance

/-- An element of `SO(3)` fixing the north pole is a rotation about the polar axis. -/
theorem exists_rot_of_smul_northPole {g : SO3} (hg : g • (northPole : Sph2) = northPole) :
    ∃ a : Circle, ∀ v : ℂ, g • stereoInv v = stereoInv ((a : ℂ) * v) := by
  set L : Euc3 ≃ₗᵢ[ℝ] Euc3 := (g : Euc3 ≃ₗᵢ[ℝ] Euc3)
  have hN : L (WithLp.toLp 2 ((1 : ℝ), (0 : ℂ))) = WithLp.toLp 2 (1, 0) :=
    congrArg Subtype.val hg
  have hfst : ∀ w : ℂ, (L (WithLp.toLp 2 ((0 : ℝ), w))).fst = 0 := by
    intro w
    have h := L.inner_map_map (WithLp.toLp 2 ((0 : ℝ), w)) (WithLp.toLp 2 ((1 : ℝ), (0 : ℂ)))
    rw [hN] at h
    simpa using h
  -- the restriction `A` of `L` to the equatorial plane
  let A₀ : ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun w => (L (WithLp.toLp 2 ((0 : ℝ), w))).snd
      map_add' := fun w w' => by
        rw [show (WithLp.toLp 2 ((0 : ℝ), w + w') : Euc3) =
          WithLp.toLp 2 ((0 : ℝ), w) + WithLp.toLp 2 ((0 : ℝ), w') by simp [← WithLp.toLp_add],
          map_add]
        rfl
      map_smul' := fun c w => by
        rw [show (WithLp.toLp 2 ((0 : ℝ), c • w) : Euc3) = c • WithLp.toLp 2 ((0 : ℝ), w) by
          simp [← WithLp.toLp_smul], map_smul]
        rfl }
  have hnorm : ∀ w, ‖A₀ w‖ = ‖w‖ := by
    intro w
    have h1 := norm_polarSum_sq (L (WithLp.toLp 2 ((0 : ℝ), w)))
    rw [LinearIsometryEquiv.norm_map, norm_toLp_sq, hfst] at h1
    have h2 : ‖A₀ w‖ ^ 2 = ‖w‖ ^ 2 := by
      show ‖(L (WithLp.toLp 2 ((0 : ℝ), w))).snd‖ ^ 2 = _
      linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  let A₁ : ℂ →ₗᵢ[ℝ] ℂ := ⟨A₀, hnorm⟩
  let A : ℂ ≃ₗᵢ[ℝ] ℂ := A₁.toLinearIsometryEquiv rfl
  have hA : ∀ w, A w = (L (WithLp.toLp 2 ((0 : ℝ), w))).snd := fun w => rfl
  have hL : L = liftIsom A := by
    refine LinearIsometryEquiv.ext fun x => ?_
    have hx : x = (x.fst) • WithLp.toLp 2 ((1 : ℝ), (0 : ℂ)) + WithLp.toLp 2 ((0 : ℝ), x.snd) := by
      apply WithLp.ofLp_injective 2
      refine Prod.ext ?_ ?_ <;> simp
    rw [liftIsom_apply, hx, map_add, map_smul, hN]
    apply WithLp.ofLp_injective 2
    refine Prod.ext ?_ ?_
    · simp [hfst]
    · simp [hA]
  have hdet : LinearMap.det (A.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
    rw [← det_liftIsom, ← hL]; exact g.2
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex A
  · refine ⟨a, fun v => Subtype.ext ?_⟩
    rw [coe_specialOrth_smul]
    show L (stereoInv v : Euc3) = (stereoInv ((a : ℂ) * v) : Euc3)
    have hav : ‖(a : ℂ) * v‖ = ‖v‖ := by rw [norm_mul, Circle.norm_coe, one_mul]
    rw [hL, liftIsom_apply]
    show WithLp.toLp 2 ((1 - ‖v‖ ^ 2) / (1 + ‖v‖ ^ 2), A ((2 / (1 + ‖v‖ ^ 2)) • v)) =
      WithLp.toLp 2 ((1 - ‖(a : ℂ) * v‖ ^ 2) / (1 + ‖(a : ℂ) * v‖ ^ 2),
        (2 / (1 + ‖(a : ℂ) * v‖ ^ 2)) • ((a : ℂ) * v))
    rw [hav, map_smul, ha, rotation_apply]
  · exfalso
    have : LinearMap.det (A.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 := by
      rw [ha]
      have : ((Complex.conjLIE.trans (rotation a)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
          ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
            (Complex.conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) := by
        ext; rfl
      rw [this, LinearMap.det_comp, det_rotation, Complex.det_conjLIE, one_mul]
    rw [hdet] at this; norm_num at this
instance (θ : ConeAngle) : LocPathConnectedSpace (SphCone θ) :=
  (SphCone.homeoComplex θ).isOpenEmbedding.locPathConnectedSpace

theorem continuous_sphCone_mk (θ : ConeAngle) : Continuous (SphCone.mk θ) := continuous_quot_mk

/-- The charts of `C_θ` read on its cover: near a point off the apex, a chart of the maximal
a.e. atlas composed with the projection is a translate of the developing map. -/
theorem sphCone_chart_dev (θ : ConeAngle) {y : DInfty × Unit} (hy : 0 < y.1.r)
    {c : OpenPartialHomeomorph (SphCone θ) Sph2} (hc : c ∈ aeAtlas SO3 Sph2 (SphCone θ))
    (hyc : SphCone.mk θ y ∈ c.source) :
    ∃ k : SO3, ∀ᶠ y' in 𝓝 y, c (SphCone.mk θ y') = k • sphConeDev θ.1 y' := by
  have hP := DInfty.isPortly_pos Unit
  have hD := isLocalHomeomorphOn_polarConeDev (isOpenEmbedding_stereoInv (W := ℂ)) θ.2.ne'
  have hdev := isAEAtlas_devAtlas (G := SO3) hP hD
  have hreg := (sphCone_isAEMorphism_mk θ).regLocusOf_eq hdev.maximalAEAtlas
    (isMaximalAEAtlas_aeAtlas SO3 Sph2 (SphCone θ)).1
  have hyR : y ∈ regLocusOf SO3 (polarConeAtlas SO3 stereoInv θ.1)
      (aeAtlas SO3 Sph2 (SphCone θ)) (SphCone.mk θ) := by
    rw [hreg]
    exact ⟨subset_support_devStructure hP hD hy, mem_support.2 ⟨c, hc, hyc⟩⟩
  have hys : y ∈ support (devAtlas SO3 (sphConeDev θ.1) (cylPos Unit)) := by
    rw [support_devAtlas hP.isOpen hD]; exact hy
  obtain ⟨e, he, hye⟩ := mem_support.1 hys
  obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := SO3) _ _ _).exists_smul_eq y hyR e
    (hdev.subset_maximalAEAtlas he) c hc hye hyc
  obtain ⟨h, hh⟩ := he.2 y hye
  refine ⟨g * h⁻¹, ?_⟩
  filter_upwards [hg, hh] with y' h1 h2
  rw [h1, h2, mul_smul, inv_smul_smul]
/-- Integer-valued continuous functions on a preconnected space are constant. -/
theorem eq_of_continuous_intValued {Q : Type*} [TopologicalSpace Q] [PreconnectedSpace Q]
    {G : Q → ℝ} (hG : Continuous G) (hZ : ∀ q, ∃ n : ℤ, G q = n) (q₁ q₂ : Q) : G q₁ = G q₂ := by
  have hlc : IsLocallyConstant G := by
    refine (IsLocallyConstant.iff_eventually_eq G).2 fun q => ?_
    have h := hG.continuousAt (x := q)
    have hb : ∀ᶠ q' in 𝓝 q, G q' ∈ Metric.ball (G q) (1 / 2) :=
      h.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
    filter_upwards [hb] with q' hq'
    obtain ⟨n, hn⟩ := hZ q
    obtain ⟨n', hn'⟩ := hZ q'
    rw [Metric.mem_ball, Real.dist_eq, hn, hn'] at hq'
    have : |((n' - n : ℤ) : ℝ)| < 1 := by push_cast; linarith
    have h0 : n' - n = 0 := by
      rw [← Int.cast_abs] at this
      have : |n' - n| < 1 := by exact_mod_cast this
      rw [abs_lt] at this; omega
    rw [hn, hn']; congr 1; omega
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ _) (mem_univ _)

/-- **The angle of the source is an integer multiple of the angle of the target**: an a.e.
isomorphism of open subsets of `C_θ` and `C_θ'` sending the apex to the apex, `θ ≠ 2π`. Lift it
on a punctured neighbourhood to the covers (through `exp`), compare the developing maps by
rigidity: the lift is `(r, φ) ↦ (r, (θφ + c)/θ')` up to the rotation about the axis, and the deck
generator `φ ↦ φ + 1` goes to an integer translation. -/
theorem sphCone_exists_int_mul {θ θ' : ConeAngle} (hθ : θ.1 ≠ 2 * π)
    {U₁ : Opens (SphCone θ)} {U₂ : Opens (SphCone θ')} (φ : U₁ ≃ₜ U₂)
    (hφ : IsAEMorphism SO3 Sph2 (φ : U₁ → U₂)) (hS : SphCone.apex θ ∈ U₁)
    (hφa : (φ ⟨_, hS⟩ : SphCone θ') = SphCone.apex θ') : ∃ m : ℤ, θ.1 = m * θ'.1 := by
  set F := chartExt φ with hFdef
  have hFa : F (SphCone.apex θ) = SphCone.apex θ' := by rw [hFdef, chartExt_apply φ hS, hφa]
  -- a ball `{r < ε}` of the cover maps into `U₁`
  have hO : SphCone.mk θ ⁻¹' (U₁ : Set (SphCone θ)) ∈ 𝓝 ((DInfty.apex, ()) : DInfty × Unit) :=
    (continuous_sphCone_mk θ).continuousAt.preimage_mem_nhds (U₁.isOpen.mem_nhds hS)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hO
  obtain ⟨ε, hε, hεu⟩ := DInfty.hasBasis_nhds_apex.mem_iff.1 hu
  have hvU : ∀ z : Unit, z ∈ v := fun z => by cases z; exact mem_of_mem_nhds hv
  -- the strip `Q = ]0, ε[ × ℝ`, simply connected
  set Q : Set (ℝ × ℝ) := Ioo 0 ε ×ˢ univ with hQdef
  have hQc : Convex ℝ Q := (convex_Ioo 0 ε).prod convex_univ
  have hQo : IsOpen Q := isOpen_Ioo.prod isOpen_univ
  have hq₀ : ((ε / 2, (0 : ℝ)) : ℝ × ℝ) ∈ Q := ⟨⟨half_pos hε, half_lt_self hε⟩, trivial⟩
  have hq₁ : ((ε / 2, (1 : ℝ)) : ℝ × ℝ) ∈ Q := ⟨⟨half_pos hε, half_lt_self hε⟩, trivial⟩
  haveI : ContractibleSpace Q := hQc.contractibleSpace ⟨_, hq₀⟩
  haveI : SimplyConnectedSpace Q := SimplyConnectedSpace.ofContractible Q
  haveI : LocPathConnectedSpace Q := hQo.locPathConnectedSpace
  haveI : PreconnectedSpace Q := Subtype.preconnectedSpace hQc.isPreconnected
  have hQpos : ∀ q : Q, 0 < q.1.1 := fun q => q.2.1.1
  set σ : Q → DInfty × Unit := fun q => (DInfty.posEmb ⟨q.1, hQpos q⟩, ()) with hσdef
  have hσc : Continuous σ :=
    (DInfty.continuous_posEmb.comp (continuous_subtype_val.subtype_mk _)).prodMk continuous_const
  have hσU : ∀ q : Q, SphCone.mk θ (σ q) ∈ U₁ := fun q =>
    huv ⟨hεu (show (DInfty.posEmb ⟨q.1, hQpos q⟩).r < ε from q.2.1.2), hvU _⟩
  have hσreg : ∀ q : Q, SphCone.mk θ (σ q) ∈ Reg SO3 Sph2 (SphCone θ) := fun q =>
    SphCone.mk_mem_reg θ (hQpos q)
  have hσne : ∀ q : Q, SphCone.mk θ (σ q) ≠ SphCone.apex θ := fun q h =>
    (SphCone.apex_mem_sing_iff θ).2 hθ (h ▸ hσreg q)
  have hFne : ∀ q : Q, F (SphCone.mk θ (σ q)) ≠ SphCone.apex θ' := fun q h =>
    hσne q (injOn_chartExt φ (hσU q) hS (h.trans hFa.symm))
  -- `f = h' ∘ F ∘ π ∘ σ : Q → ℂ ∖ {0}`
  set h' := SphCone.homeoComplex θ'
  have hh'a : h' (SphCone.apex θ') = 0 := by
    show DInfty.cplx 1 DInfty.apex = 0
    exact DInfty.cplx_apex 1
  have hFc : Continuous fun q : Q => F (SphCone.mk θ (σ q)) :=
    (continuousOn_chartExt φ).comp_continuous ((continuous_sphCone_mk θ).comp hσc) hσU
  let f : C(Q, ℂ) := ⟨fun q => h' (F (SphCone.mk θ (σ q))), h'.continuous.comp hFc⟩
  have hf0 : ∀ q : Q, f q ≠ 0 := fun q h => hFne q (h'.injective (h.trans hh'a.symm))
  -- the lift through `exp`
  obtain ⟨L, ⟨-, hL⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨_, hq₀⟩) (e₀ := Complex.log (f ⟨_, hq₀⟩)) (Complex.exp_log (hf0 _))
    (fun q => hf0 q)
  have hLf : ∀ q, Complex.exp (L q) = f q := fun q => congrFun hL q
  -- the lifted map `F̃ : Q → {r > 0}`
  have hfpos : ∀ q : Q, 0 < ‖f q‖ := fun q => norm_pos_iff.2 (hf0 q)
  set Ft : Q → DInfty × Unit := fun q =>
    (DInfty.posEmb ⟨(‖f q‖, (L q).im / (2 * π)), hfpos q⟩, ()) with hFtdef
  have hFtc : Continuous Ft :=
    (DInfty.continuous_posEmb.comp (Continuous.subtype_mk
      ((continuous_norm.comp f.continuous).prodMk
        ((Complex.continuous_im.comp L.continuous).div_const _)) _)).prodMk continuous_const
  have hFtpos : ∀ q : Q, 0 < (Ft q).1.r := hfpos
  have hFtπ : ∀ q : Q, SphCone.mk θ' (Ft q) = F (SphCone.mk θ (σ q)) := by
    intro q
    apply h'.injective
    show DInfty.cplx 1 (DInfty.posEmb ⟨(‖f q‖, (L q).im / (2 * π)), hfpos q⟩) = f q
    simp only [DInfty.cplx, DInfty.posEmb_r, DInfty.posEmb_θ]
    have : (2 * π / 1 * ((L q).im / (2 * π)) : ℝ) = (L q).im := by field_simp
    rw [this]
    have hn : ‖f q‖ = Real.exp (L q).re := by rw [← hLf q, Complex.norm_exp]
    rw [hn]
    conv_rhs => rw [← hLf q, ← Complex.re_add_im (L q), Complex.exp_add]
    rw [Complex.ofReal_exp]
  -- locally, `D' ∘ F̃` is a translate of `D ∘ σ`
  have hloc : ∀ q ∈ (univ : Set Q), ∃ g : SO3, ∀ᶠ q' in 𝓝 q,
      sphConeDev θ'.1 (Ft q') = g • sphConeDev θ.1 (σ q') := by
    intro q _
    have hFreg : F (SphCone.mk θ (σ q)) ∈ Reg SO3 Sph2 (SphCone θ') :=
      (chartExt_mem_reg_iff hφ (hσU q)).2 (hσreg q)
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hFreg
    have huc : ((φ ⟨_, hσU q⟩ : U₂) : SphCone θ') ∈ c.source := by
      rw [← chartExt_apply φ (hσU q)]; exact hxc
    obtain ⟨c', hc', hxc', g₀, hg₀⟩ :=
      eventually_chartExt_eq_smul hφ (u := ⟨_, hσU q⟩) (hσreg q) hc huc
    obtain ⟨k, hk⟩ := sphCone_chart_dev θ (y := σ q) (hQpos q) hc' hxc'
    obtain ⟨k', hk'⟩ := sphCone_chart_dev θ' (y := Ft q) (hFtpos q) hc
      (by rw [hFtπ q]; exact hxc)
    refine ⟨k'⁻¹ * g₀ * k, ?_⟩
    have h1 := hσc.continuousAt.eventually hk
    have h2 := ((continuous_sphCone_mk θ).comp hσc).continuousAt.eventually hg₀
    have h3 := hFtc.continuousAt.eventually hk'
    filter_upwards [h1, h2, h3] with q' e1 e2 e3
    rw [hFtπ q'] at e3
    have e2' : c (F (SphCone.mk θ (σ q'))) = g₀ • c' (SphCone.mk θ (σ q')) := e2
    rw [e2', e1] at e3
    rw [mul_smul, mul_smul, e3, inv_smul_smul]
  -- rigidity on the strip
  have hDσ : IsLocalHomeomorphOn (fun q : Q => sphConeDev θ.1 (σ q)) univ := by
    have hD := isLocalHomeomorphOn_polarConeDev (isOpenEmbedding_stereoInv (W := ℂ)) θ.2.ne'
    have hι : IsOpenEmbedding (fun q : Q => (⟨q.1, hQpos q⟩ : {q : ℝ × ℝ // 0 < q.1})) :=
      isOpenEmbedding_codRestrict hQo.isOpenEmbedding_subtypeVal (s := {q : ℝ × ℝ | 0 < q.1})
        hQpos
    have hσe : IsOpenEmbedding σ :=
      (Homeomorph.prodPUnit DInfty).symm.isOpenEmbedding.comp
        (DInfty.isOpenEmbedding_posEmb.comp hι)
    exact hD.comp hσe.isLocalHomeomorph.isLocalHomeomorphOn (fun q _ => hQpos q)
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isLocalHomeomorphOn isOpen_univ hDσ
    isPreconnected_univ subset_rfl hloc
  -- `g` fixes the north pole: let `r → 0` along the ray `φ = 0`
  have hnormDev : ∀ (α : ℝ) (x : DInfty × Unit), ‖(conicalDev α Unit x).1‖ = x.1.r :=
    fun α x => DInfty.norm_cplx _ x.1
  set t : ℕ → ℝ := fun n => ε / 2 * (1 / ((n : ℝ) + 1)) with htdef
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
    rw [mul_zero] at this
    exact this
  have htpos : ∀ n, 0 < t n := fun n => by positivity
  have htlt : ∀ n, t n < ε := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc t n ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < ε := by linarith
  set qs : ℕ → Q := fun n => ⟨(t n, 0), ⟨htpos n, htlt n⟩, trivial⟩ with hqsdef
  have hσqs : Tendsto (fun n => σ (qs n)) atTop (𝓝 ((DInfty.apex, ()) : DInfty × Unit)) := by
    refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
    refine DInfty.hasBasis_nhds_apex.tendsto_right_iff.2 fun ε' hε' => ?_
    filter_upwards [ht0.eventually (gt_mem_nhds hε')] with n hn
    exact hn
  have hFt0 : Tendsto (fun n => sphConeDev θ'.1 (Ft (qs n))) atTop (𝓝 northPole) := by
    rw [← stereoInv_zero]
    refine (continuous_stereoInv.tendsto 0).comp (tendsto_zero_iff_norm_tendsto_zero.2 ?_)
    have hlim : Tendsto (fun n => ‖f (qs n)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => F (SphCone.mk θ (σ (qs n)))) atTop (𝓝 (SphCone.apex θ')) := by
        rw [← hFa]
        exact ((continuousOn_chartExt φ).continuousAt (U₁.isOpen.mem_nhds hS)).tendsto.comp
          ((continuous_sphCone_mk θ).continuousAt.tendsto.comp hσqs)
      have h2 := (continuous_norm.comp h'.continuous).continuousAt.tendsto.comp h1
      rw [Function.comp_def] at h2
      have h3 : Tendsto (fun x => ‖h' (F (SphCone.mk θ (σ (qs x))))‖) atTop (𝓝 0) := by
        simpa [hh'a] using h2
      exact h3
    refine hlim.congr fun n => ?_
    exact (hnormDev θ'.1 (Ft (qs n))).symm
  have hD0 : Tendsto (fun n => sphConeDev θ.1 (σ (qs n))) atTop (𝓝 northPole) := by
    rw [← stereoInv_zero]
    refine (continuous_stereoInv.tendsto 0).comp (tendsto_zero_iff_norm_tendsto_zero.2 ?_)
    refine ht0.congr fun n => ?_
    exact (hnormDev θ.1 (σ (qs n))).symm
  have hgN : g • (northPole : Sph2) = northPole := by
    have h1 : Tendsto (fun n => g • sphConeDev θ.1 (σ (qs n))) atTop (𝓝 (g • northPole)) :=
      ((continuous_const_smul g).tendsto _).comp hD0
    have h2 : Tendsto (fun n => g • sphConeDev θ.1 (σ (qs n))) atTop (𝓝 northPole) :=
      hFt0.congr fun n => hg (qs n) (mem_univ _)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨a, ha⟩ := exists_rot_of_smul_northPole hgN
  set β : ℝ := Complex.arg (a : ℂ) with hβdef
  have haβ : (a : ℂ) = Complex.exp ((β : ℂ) * Complex.I) := by
    rw [← Circle.coe_exp, Circle.exp_arg]
  -- the angle relation, up to `2πℤ`
  set ψ : Q → ℝ := fun q => (L q).im / (2 * π) with hψdef
  have hint : ∀ q : Q, ∃ n : ℤ,
      (θ'.1 * ψ q - β - θ.1 * q.1.2) / (2 * π) = n := by
    intro q
    have e := hg q (mem_univ _)
    simp only [sphConeDev, polarConeDev] at e
    rw [ha] at e
    have e' := congrArg stereoFun e
    rw [stereoFun_stereoInv, stereoFun_stereoInv] at e'
    have e1 : (conicalDev θ'.1 Unit (Ft q)).1 =
        ((‖f q‖ : ℝ) : ℂ) * Complex.exp (((θ'.1 * ψ q : ℝ) : ℂ) * Complex.I) := by
      show (conicalDev θ'.1 Unit (DInfty.posEmb ⟨(‖f q‖, ψ q), hfpos q⟩, ())).1 = _
      rw [conicalDev_posEmb θ'.2.ne']
    have e2 : (conicalDev θ.1 Unit (σ q)).1 =
        ((q.1.1 : ℝ) : ℂ) * Complex.exp (((θ.1 * q.1.2 : ℝ) : ℂ) * Complex.I) := by
      show (conicalDev θ.1 Unit (DInfty.posEmb ⟨(q.1.1, q.1.2), hQpos q⟩, ())).1 = _
      rw [conicalDev_posEmb θ.2.ne']
    rw [e1, e2, haβ] at e'
    -- norms: `‖f q‖ = r`
    have hn := congrArg norm e'
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, one_mul,
      Real.norm_eq_abs, abs_of_pos (hfpos q), abs_of_pos (hQpos q)] at hn
    rw [hn] at e'
    have hr0 : ((q.1.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hQpos q).ne'
    have e3 : Complex.exp (((θ'.1 * ψ q : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((β + θ.1 * q.1.2 : ℝ) : ℂ) * Complex.I) := by
      have : ((q.1.1 : ℝ) : ℂ) * Complex.exp (((θ'.1 * ψ q : ℝ) : ℂ) * Complex.I) =
          ((q.1.1 : ℝ) : ℂ) * Complex.exp (((β + θ.1 * q.1.2 : ℝ) : ℂ) * Complex.I) := by
        rw [e']
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
      exact mul_left_cancel₀ hr0 this
    obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.1 e3
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn'
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, sub_zero, zero_mul, zero_add] at him
    have hπ : (2 * π) ≠ 0 := by positivity
    rw [div_eq_iff hπ]
    have h2 : Complex.re 2 = 2 := by norm_num
    rw [h2] at him
    linarith
  -- `G` is constant
  have hψc : Continuous ψ := (Complex.continuous_im.comp L.continuous).div_const _
  have hGc : Continuous fun q : Q => (θ'.1 * ψ q - β - θ.1 * q.1.2) / (2 * π) :=
    (((continuous_const.mul hψc).sub continuous_const).sub
      (continuous_const.mul (continuous_snd.comp continuous_subtype_val))).div_const _
  have hG := eq_of_continuous_intValued hGc hint ⟨_, hq₀⟩ ⟨_, hq₁⟩
  -- the deck generator: `σ q₁ = 1 · σ q₀`, so `F̃ q₁ = k · F̃ q₀`
  have hσ01 : σ ⟨_, hq₁⟩ = (GammaA.ofInt 1 : GammaA 1) • σ ⟨_, hq₀⟩ := by
    show (DInfty.posEmb ⟨(ε / 2, 1), _⟩, ()) = (GammaA.ofInt 1 : GammaA 1) •
      (DInfty.posEmb ⟨(ε / 2, 0), _⟩, ())
    rw [gammaOne_smul_posEmb]
    congr 2
    simp
  have hπ01 : SphCone.mk θ' (Ft ⟨_, hq₀⟩) = SphCone.mk θ' (Ft ⟨_, hq₁⟩) := by
    rw [hFtπ, hFtπ, hσ01]
    show F (orbitMk (GammaA 1) (σ ⟨_, hq₀⟩)) = F (orbitMk (GammaA 1) (_ • σ ⟨_, hq₀⟩))
    rw [orbitMk_smul]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_orbitMk_eq hπ01
  have hk' : ψ ⟨_, hq₀⟩ + k.toInt = ψ ⟨_, hq₁⟩ := by
    have := congrArg (fun x : DInfty × Unit => x.1.θ) hk
    simp only [hFtdef] at this
    rw [gammaOne_smul_posEmb] at this
    simpa using this
  refine ⟨k.toInt, ?_⟩
  have hπ : (2 * π) ≠ 0 := by positivity
  rw [div_left_inj' hπ] at hG
  simp only at hG
  rw [← hk'] at hG
  linarith
/-- **The spherical cones of angle `θ ≠ 2π` are pairwise non-isomorphic at their apex** (the
`eq_of_iso` half of the analyticity of the family `(C_θ)_{θ ≠ 2π}`,
`def:family_singular_manifolds_endowed`; the spherical analogue of `GX.mass_to_mass`, B21
Prop 1.3): an a.e. isomorphism of open subsets of `C_θ` and `C_θ'` whose domain contains the apex
forces `θ = θ'`. It sends the apex to the apex (the only singular points), so `θ' ≠ 2π`; then
`θ ∈ θ'ℤ` and `θ' ∈ θℤ` (`sphCone_exists_int_mul`), and the angles are positive. (The paper's
connectedness of the open sets is not used.) -/
theorem sphCone_eq_of_iso {θ θ' : ConeAngle} (hθ : θ.1 ≠ 2 * π) (U₁ : Opens (SphCone θ))
    (U₂ : Opens (SphCone θ')) (φ : U₁ ≃ₜ U₂)
    (hφ : IsAEMorphism SO3 Sph2 (φ : U₁ → U₂)) (hS : SphCone.apex θ ∈ U₁) : θ = θ' := by
  set u : U₁ := ⟨_, hS⟩
  have hpre := (IsAEMorphism.preimage_reg_sing hφ φ.isLocalHomeomorph).2
  have huS : u ∈ Sing SO3 Sph2 U₁ := by
    rw [sing_opensSingular]; exact (SphCone.apex_mem_sing_iff θ).2 hθ
  have hφS : φ u ∈ Sing SO3 Sph2 U₂ := by
    have : u ∈ (φ : U₁ → U₂) ⁻¹' Sing SO3 Sph2 U₂ := by rw [hpre]; exact huS
    exact this
  have hφS' : (φ u : SphCone θ') ∈ Sing SO3 Sph2 (SphCone θ') := by
    rw [sing_opensSingular] at hφS; exact hφS
  have hθ' : θ'.1 ≠ 2 * π := fun h => by
    rw [SphCone.sing_eq_empty θ' h] at hφS'; exact hφS'
  have hφa : (φ u : SphCone θ') = SphCone.apex θ' := by
    rw [SphCone.sing_eq θ' hθ'] at hφS'; exact hφS'
  obtain ⟨m, hm⟩ := sphCone_exists_int_mul hθ φ hφ hS hφa
  have hS' : SphCone.apex θ' ∈ U₂ := hφa ▸ (φ u).2
  have hφa' : (φ.symm ⟨_, hS'⟩ : SphCone θ) = SphCone.apex θ := by
    have : (⟨_, hS'⟩ : U₂) = φ u := Subtype.ext hφa.symm
    rw [this, φ.symm_apply_apply]
  obtain ⟨m', hm'⟩ := sphCone_exists_int_mul hθ' φ.symm
    (IsAEMorphism.symm_of_homeomorph hφ) hS' hφa'
  have hθp := θ.2
  have hθ'p := θ'.2
  have hmm : ((m * m' : ℤ) : ℝ) = 1 := by
    have h1 : θ.1 = ((m * m' : ℤ) : ℝ) * θ.1 := by
      push_cast; rw [mul_assoc, ← hm', ← hm]
    have h2 : (((m * m' : ℤ) : ℝ) - 1) * θ.1 = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · linarith
  have hmm' : m * m' = 1 := by exact_mod_cast hmm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm' with h | h
  · exact Subtype.ext (by rw [hm, h]; simp)
  · exfalso
    rw [h] at hm
    push_cast at hm
    linarith

end AngleInvariance

/-! ### Cone points of angle `θ`, spherical cone surfaces, cone spheres -/

section ConePoints

/-- The distinguished singular point `S_θ = {apex}` of the model `C_θ`
(`def:family_singular_manifolds_endowed`, `RamcovGX.tex:1899`). -/
def sphConeS (θ : ConeAngle) : Set (SphCone θ) := {SphCone.apex θ}

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- **`x` is a cone point of angle `θ`** (`RamcovGX.tex:694–695`: "a metric space locally
isometric to either of local models", read in gx's framework): `x` has type `θ` for the family of
spherical cones (`def:atlas`, `RamcovGX.tex:1905`, `GX.HasXAType`) — a homeomorphism `φ` of an open
neighbourhood `U` of `x` onto a connected open neighbourhood of the apex of `C_θ`, an a.e.
`(SO(3), 𝕊²)`-isomorphism, with `φ x` the apex. For `θ = 2π` such an `x` is regular
(`IsConePoint.mem_reg`), otherwise singular (`IsConePoint.mem_sing`). -/
def IsConePoint (θ : ConeAngle) (x : M) : Prop :=
  HasXAType (G := SO3) (X := Sph2) (Xα := SphCone) (S := sphConeS) θ x

/-- The apex of `C_θ` is a cone point of angle `θ` (the chart `(C_θ, C_θ, id)`). -/
theorem isConePoint_apex (θ : ConeAngle) : IsConePoint θ (SphCone.apex θ) :=
  ⟨modelChartSelf SO3 Sph2 sphConeS θ (mem_singleton _)⟩

theorem XAChart.sphCone_apex {θ : ConeAngle} {x : M}
    (c : XAChart SO3 Sph2 SphCone sphConeS θ x) :
    (c.φ ⟨x, c.mem⟩ : SphCone θ) = SphCone.apex θ := c.mem_S

/-- A cone point of angle `θ ≠ 2π` is singular. -/
theorem IsConePoint.mem_sing {θ : ConeAngle} {x : M} (h : IsConePoint θ x) (hθ : θ.1 ≠ 2 * π) :
    x ∈ Sing SO3 Sph2 M := by
  obtain ⟨c⟩ := h
  have h := (IsAEMorphism.preimage_reg_sing c.isAEMorphism c.φ.isLocalHomeomorph).2
  have hV : c.φ ⟨x, c.mem⟩ ∈ Sing SO3 Sph2 c.V := by
    rw [sing_opensSingular]
    show ((c.φ ⟨x, c.mem⟩ : SphCone θ)) ∈ Sing SO3 Sph2 (SphCone θ)
    rw [c.sphCone_apex]; exact (SphCone.apex_mem_sing_iff θ).2 hθ
  have hU : (⟨x, c.mem⟩ : c.U) ∈ Sing SO3 Sph2 c.U := by rw [← h]; exact hV
  rw [sing_opensSingular] at hU
  exact hU

/-- A cone point of angle `2π` is regular. -/
theorem IsConePoint.mem_reg {θ : ConeAngle} {x : M} (h : IsConePoint θ x) (hθ : θ.1 = 2 * π) :
    x ∈ Reg SO3 Sph2 M := by
  obtain ⟨c⟩ := h
  have h := (IsAEMorphism.preimage_reg_sing c.isAEMorphism c.φ.isLocalHomeomorph).1
  have hV : c.φ ⟨x, c.mem⟩ ∈ Reg SO3 Sph2 c.V := by
    rw [reg_opensSingular]
    show ((c.φ ⟨x, c.mem⟩ : SphCone θ)) ∈ Reg SO3 Sph2 (SphCone θ)
    by_contra hn
    have : ((c.φ ⟨x, c.mem⟩ : SphCone θ)) ∈ Sing SO3 Sph2 (SphCone θ) := hn
    rw [SphCone.sing_eq_empty θ hθ] at this
    exact this
  have hU : (⟨x, c.mem⟩ : c.U) ∈ Reg SO3 Sph2 c.U := by rw [← h]; exact hV
  rw [reg_opensSingular] at hU
  exact hU

/-- A cone point is singular iff its angle is not `2π`. -/
theorem IsConePoint.mem_sing_iff {θ : ConeAngle} {x : M} (h : IsConePoint θ x) :
    x ∈ Sing SO3 Sph2 M ↔ θ.1 ≠ 2 * π :=
  ⟨fun hs hθ => hs (h.mem_reg hθ), h.mem_sing⟩

/-- **The cone angle is well defined**: a point is a cone point of at most one angle
(`rem:singular_point_manifold_has`, `RamcovGX.tex:1921`, for the spherical cones). The cases
where one angle is `2π` are proved (a regular point is no cone point of angle `≠ 2π`); the
others rest on `sphCone_eq_of_iso`. -/
theorem IsConePoint.angle_eq [LocallyConnectedSpace M] {θ θ' : ConeAngle} {x : M}
    (h : IsConePoint θ x) (h' : IsConePoint θ' x) : θ = θ' := by
  by_cases hθ : θ.1 = 2 * π
  · by_cases hθ' : θ'.1 = 2 * π
    · exact Subtype.ext (hθ.trans hθ'.symm)
    · exact absurd (h.mem_reg hθ) (h'.mem_sing hθ')
  obtain ⟨c₁⟩ := h
  obtain ⟨c₂⟩ := h'
  set W : Opens M := ⟨connectedComponentIn ((c₁.U : Set M) ∩ c₂.U) x,
    (c₁.U.isOpen.inter c₂.U.isOpen).connectedComponentIn⟩
  have hxW : x ∈ W := mem_connectedComponentIn ⟨c₁.mem, c₂.mem⟩
  have hW₁ : W ≤ c₁.U := fun y hy => (connectedComponentIn_subset _ _ hy).1
  have hW₂ : W ≤ c₂.U := fun y hy => (connectedComponentIn_subset _ _ hy).2
  have hWc : IsConnected (W : Set M) := isConnected_connectedComponentIn_iff.2 ⟨c₁.mem, c₂.mem⟩
  set d₁ := c₁.restrict W hxW hW₁ hWc
  set d₂ := c₂.restrict W hxW hW₂ hWc
  set ψ : d₁.V ≃ₜ d₂.V := d₁.φ.symm.trans d₂.φ
  have hψ : IsAEMorphism SO3 Sph2 (ψ : d₁.V → d₂.V) :=
    d₂.isAEMorphism.comp (IsAEMorphism.symm_of_homeomorph d₁.isAEMorphism)
  refine sphCone_eq_of_iso hθ d₁.V d₂.V ψ hψ ?_
  have := (d₁.φ ⟨x, hxW⟩).2
  rwa [d₁.sphCone_apex] at this

variable (M) in
/-- **A spherical cone surface** (`RamcovGX.tex:694–695`, `n = 2`: "a `(𝕊², SO(3))`-manifold with
conical singularities is a metric space locally isometric to either of local models"): a singular
`(SO(3), 𝕊²)`-manifold — locally `𝕊²` at its regular points — every singular point of which is a
cone point of some angle. -/
def IsSphericalConeSurface : Prop :=
  ∀ x ∈ Sing SO3 Sph2 M, ∃ θ : ConeAngle, IsConePoint θ x

variable (M) in
/-- **A spherical cone sphere with cone points `p_i` of angles `θ_i`**
(`cex:start_singular_manifold_homeomorphic`, `RamcovGX.tex:1930`: "a singular `𝕊²`-manifold
homeomorphic to a sphere with `s` conical singularities of respective angles `θ_i`"): `M` is
homeomorphic to `𝕊²`, the `p_i` are distinct, `p_i` is a cone point of angle `θ_i > 0`, and there
is no other singular point. A `θ_i = 2π` marks a regular point (`IsConeSphere.sing_eq`). -/
structure IsConeSphere {s : ℕ} (θ : Fin s → ℝ) (p : Fin s → M) : Prop where
  homeomorphic : Nonempty (M ≃ₜ Sph2)
  injective : Injective p
  pos : ∀ i, 0 < θ i
  isConePoint : ∀ i, IsConePoint ⟨θ i, pos i⟩ (p i)
  sing_subset : Sing SO3 Sph2 M ⊆ range p

namespace IsConeSphere

variable {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}

/-- **The singular locus of a cone sphere** is the set of its cone points of angle `≠ 2π`. -/
theorem sing_eq (h : IsConeSphere M θ p) :
    Sing SO3 Sph2 M = p '' {i | θ i ≠ 2 * π} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := h.sing_subset hx
    exact ⟨i, fun h2 => hx ((h.isConePoint i).mem_reg h2), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact (h.isConePoint i).mem_sing hi

theorem isSphericalConeSurface (h : IsConeSphere M θ p) : IsSphericalConeSurface M := by
  intro x hx
  obtain ⟨i, rfl⟩ := h.sing_subset hx
  exact ⟨_, h.isConePoint i⟩

theorem connectedSpace (h : IsConeSphere M θ p) : ConnectedSpace M :=
  let e := h.homeomorphic.some
  e.symm.surjective.connectedSpace e.symm.continuous

theorem locallyConnectedSpace (h : IsConeSphere M θ p) : LocallyConnectedSpace M :=
  h.homeomorphic.some.locallyConnectedSpace

theorem t2Space (h : IsConeSphere M θ p) : T2Space M :=
  h.homeomorphic.some.isEmbedding.t2Space

theorem compactSpace (h : IsConeSphere M θ p) : CompactSpace M :=
  h.homeomorphic.some.symm.compactSpace

/-- **The angles of a cone sphere are invariants**: `p_i` is a cone point of angle `θ'` iff
`θ' = θ_i` (`IsConePoint.angle_eq`). -/
theorem isConePoint_iff (h : IsConeSphere M θ p) (i : Fin s) (θ' : ConeAngle) :
    IsConePoint θ' (p i) ↔ θ'.1 = θ i := by
  haveI := h.locallyConnectedSpace
  refine ⟨fun h' => congrArg Subtype.val ((h.isConePoint i).angle_eq h').symm, fun h' => ?_⟩
  have : θ' = ⟨θ i, h.pos i⟩ := Subtype.ext h'
  rw [this]; exact h.isConePoint i

end IsConeSphere

/-- **The round sphere `𝕊²` is a cone sphere with no cone point** (`s = 0`; the regular
`(SO(3), 𝕊²)`-manifold, `SingularGXStructure.ofHasGroupoid`, has empty singular locus). -/
theorem isConeSphere_sph2 :
    letI : SingularGXStructure SO3 Sph2 Sph2 := SingularGXStructure.ofHasGroupoid SO3 Sph2 Sph2
    IsConeSphere Sph2 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Sph2) := by
  letI : SingularGXStructure SO3 Sph2 Sph2 := SingularGXStructure.ofHasGroupoid SO3 Sph2 Sph2
  refine ⟨⟨Homeomorph.refl _⟩, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  intro x hx
  exact absurd (show x ∈ Reg SO3 Sph2 Sph2 by
    show x ∈ support ((gxGroupoid SO3 Sph2).maximalAtlas Sph2)
    rw [support_maximalAtlas]; exact mem_univ x) hx

end ConePoints

end GX
