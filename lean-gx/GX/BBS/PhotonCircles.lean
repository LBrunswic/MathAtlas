import GX.BBS.RP1Circles

/-!
# Circles of photons: `SO₀(1,2) ≅ PSL(2,ℝ)`, `∂ℍ²± ≅ ℝP¹`, the isotropic foliations of `dS²`

Research target `T-bbs-photon-circles` (`roadmap/roadmap.toml`), BBS § 5.1 and its uses at
l.763 and l.2979–2990 of `papers/bbs/legacy/labeled/colI_v1.tex`. No ledger label: pseudo-labels
below, **none marked** (the master records research results). 0 `sorry`.

* `BBS:l763:SO0=PSL` — `GX.pslEquivLorentz : PSL(2,ℝ) ≃* SO₀(1,2)`, through the spinor
  representation `GX.spinLorentz` (`X ↦ g X gᵀ`); kernel `{±1}` (`GX.ker_spinLorentz`), onto
  (`GX.spinLorentz_surjective`, by `GX.HS.boostRot_eq_top`). Proved, as groups (SCOPE (a)).
* `BBS:l1903:bd=RP1` — `GX.rp1ToBdPlus : ℝP¹ ≃ₜ ∂ℍ²₊`, the spinor map `ℝz ↦ [(|z|², z²)]`
  (`GX.coe_rp1ToBdPlus_mk`), equivariant (`GX.smul_rp1ToBdPlus`); `∂ℍ²₋ = −∂ℍ²₊`,
  `GX.rp1ToBdMinus` (`GX.smul_rp1ToBdMinus`). Proved.
* `BBS:l1903:hyperbolic-side` — a regular circle of photons `C` (`GX.IsPhotonCircle`; photons
  `GX.IsPhoton`, l.1866) carries the `ℝP¹`-structure whose charts are the HS-charts restricted to
  `C` composed with `∂ℍ²± ≅ ℝP¹` (`GX.photonChartOf`, `GX.photonChartedSpace`). It is a
  `(PSL(2,ℝ), ℝP¹)`-structure (`GX.IsPhotonCircle.rp1_hasGroupoid`), independent of the atlas
  (`GX.photonChartOf_mem_maximalAtlas`), with a lifted holonomy and a real angle
  (`GX.IsPhotonCircle.exists_hasLiftedHolonomy`, `GX.IsPhotonCircle.exists_hasRealAngle`).
  Proved in the readings of SCOPE (b), (c).
* `BBS:l1907:isotropic-foliations` — in `HS²`: through each point of `dS²` pass exactly two
  lightlike projective lines (`GX.null_orth_cases`, `GX.iotaL_ne_iotaR`, `GX.leafPt_eq`). The
  left and right foliations of `dS²` have as leaves the fibres of `ι_L`, `ι_R` (`GX.leafOver`,
  `GX.leafOver_eq`, `GX.mem_leafOver_iff`). Proved in `HS²` (SCOPE (d)); left and right are a
  convention (SCOPE (e)).
* `BBS:l2983:iota-L` — in `HS²`: `ι_L : dS² ∪ ∂ℍ²± → ∂ℍ²₊` (`GX.iotaL`, `GX.iota`) is
  continuous, proper and `SO₀(1,2)`-equivariant (`GX.continuous_iota`, `GX.isProperMap_iota`,
  `GX.iota_smul`). It is a trivial bundle `≃ₜ ∂ℍ²₊ × [−1, 1]` (`GX.iotaChart`). Each leaf runs
  from `∂ℍ²₋` to `∂ℍ²₊`, and each point of `∂ℍ²₋` (of `∂ℍ²₊`) is the `α`-limit (`ω`-limit) of
  exactly one leaf (`GX.closure_leafOver`, `GX.existsUnique_alpha`, `GX.existsUnique_omega`).
  `ι_L` is projective on `∂ℍ²₋`: the identity of `ℝP¹` (`GX.iota_rp1ToBdMinus`). Proved in `HS²`.
  `d̃S²` with `R±` is left to `T-3p1-theorem-m-theta` (SCOPE (d)).

> The classification of elements of $\SO_0(1,2) \approx \op{PSL}(2,\R)$ is presumably
> well-known (l.598) […] Let $\Gamma_p$ be the \textit{pointwise} stabilizer in
> $\SO_0(1,2)\approx \op{PSL}(2, \R)$ of $p$ (l.763)
>
> a photon is a point corresponding in every HS-chart to points in $\partial\HH^2_\pm$.
> (l.1866–1867)
>
> Let $C$ be a circle of photons. It admits two natural $\R\PP^1$-structures, which may not
> coincide if $C$ contains light-like singularities. (l.1895–1896) […] Since the conformal
> boundary of $\HH^2$ is naturally $\R\PP^1$ and that hyperbolic isometries are restrictions of
> real projective transformations, $C$ inherits, as conformal boundary of $A_{H}$, a
> $\R\PP^1$-structure that we call \textit{$\R\PP^1$-structure on $C$ from the hyperbolic side.}
> (l.1903–1905)
>
> Consider now the component $A_{S}$ in the de Sitter region adjacent to $C$. It is is foliated
> by the light-like lines. Actually, there are two such foliations (l.1907–1909)
>
> Consider the left isotropic foliation of $\tilde {dS}_2$. Each leaf has an $\alpha$-limit in
> $R_-$ and an $\omega$-limit on $R_+$. Moreover every point of $R_-$ (resp. $R_+$) is an
> $\alpha$-limit (resp. $\omega$-limit) of exactly one leaf of each foliation. Thus we have a
> continuous projection $\iota_L:\tilde{dS_2}\cup R_-\cup R_+\rightarrow R_+$, obtained by sending
> a point $x$ to the $\omega$-limit of the leaf of the left foliation trough it. The map
> $\iota_L$ is a proper submersion. (l.2983–2990)

## Main declarations

* **Coordinates.** `GX.mink3 t x y`, `GX.vol3_map` (`vol3` is the determinant through the basis
  `GX.basis3`), `GX.vol3_lorentz` (`SO₀(1,2)` preserves `vol3`).
* **The spinor map** `GX.spinor z = (|z|², Re z², Im z²)` (the planner's
  `(a, b) ↦ (a² + b², a² − b², 2ab)`); `GX.spinL` is `X ↦ M X Mᵀ` on
  `X = [[t + x, y], [y, t − x]]`, with `GX.minkQ_spinL` and `GX.det_spinL`
  (`det = (det M)³`); `GX.spinLorentz_spinor`: `g · S(z) = S(g z)`.
* **Boosts and rotations**: `diag(e^{ζ/2}, e^{−ζ/2}) ↦` the boost of rapidity `ζ`
  (`GX.spinLorentz_boostSL`); every rotation of `ℝ²` is reached by half its angle
  (`GX.rot_mem_range_spinLorentz`, through `GX.exists_circle_of_specialOrth`).
* **`dS² ∪ ∂ℍ²±`** is `GX.HS.closedDS` (`minkQ ≥ 0`). The null directions are
  `GX.nullDir ε σ = (1, t x + ε s y, t y − ε s x)`, `s = √(1 − t²)`. Each is characterised by
  being future, null, orthogonal to `σ` and on the `ε` side (`GX.eq_smul_nullDir`,
  `GX.vol3_nullDir_nonneg`). The closed leaves are `GX.leafPtHS`, and `GX.leafCurve` is the leaf
  as a curve.
* **Photons.** `GX.hsRegion` (chart-independent, `GX.region_eq_hsRegion`), `GX.isPhoton_iff`. A
  circle of photons is made of future photons only or of past photons only
  (`GX.IsPhotonCircle.exists_bdPiece`). `GX.restrictMatch` restricts a chart to matching subsets.

## Hypothesis checklist

| BBS | here |
|---|---|
| `SO₀(1,2)` (l.594–595) | ✓ `Causal.Flat.lorentz 2` (`GX.BBS.HSModel`) |
| `PSL(2,ℝ)` acting on `ℝP¹` (l.679) | ✓ mathlib's `PSL(2, ℝ)` on `GX.RP1` (`GX.BBS.RP1Circles`) |
| `SO₀(1,2) ≈ PSL(2,ℝ)` (l.598, l.763) | ✓ `pslEquivLorentz`, with `ℝP¹ ≅ ∂ℍ²₊` equivariant; ⚠ groups only, SCOPE (a) |
| `∂ℍ²±` (l.589–590) | ✓ `HS.piece 2 .bdPlus`, `.bdMinus` |
| `Σ` closed, connected, positive, causal HS-surface (l.1861) | ⚠ weakened: any `(SO₀(1,2), HS²)`-manifold `M`. No compactness, connectedness, Hausdorffness, positivity or causality is used |
| photon (l.1866–1867) | ✓ `IsPhoton`: every chart of the maximal atlas sends it into `∂ℍ²±` |
| `C` a circle of photons (l.1895–1896; the paper allows light-like singularities on `C`) | ⚠ narrowed to regular circles (the dispatch's scope) and read, SCOPE (b): `IsPhotonCircle C` |
| the `ℝP¹`-structure from the hyperbolic side (l.1898–1905) | ⚠ read, SCOPE (c): the HS-charts restricted to `C`, composed with `∂ℍ²± ≅ ℝP¹` |
| the two foliations by light-like lines (l.1907–1909) | ⚠ `HS²` model only (`ε = ±1`); left/right a convention, SCOPE (e) |
| `ι_L` continuous, a proper submersion (l.2987–2990) | ⚠ `HS²` model only: continuous, proper, a trivial bundle with fibre `[−1, 1]` (`iotaChart`). `d̃S²`: SCOPE (d) |

## SCOPE (disclosed)

* **(a) The isomorphism.** `GX.pslEquivLorentz` is an isomorphism of groups. There is no topology
  on `lorentz 2` at this pin (`GX.BBS.HSModel`, SCOPE (b)). It is the spinor isomorphism, and
  `ℝP¹ ≅ ∂ℍ²₊` intertwines it (`GX.smul_rp1ToBdPlus`). That this is the only equivariant
  identification of `∂ℍ²₊` with `ℝP¹` is not proved.
* **(b) Circle of photons.** The reading is `GX.IsPhotonCircle`: a set of photons, open in the set
  `𝒫` of photons, homeomorphic to the circle. For a Hausdorff `M` this is a connected component
  of `𝒫` homeomorphic to the circle, since `𝒫` is locally a circle by the charts built here; that
  equivalence is not formalized. *Regular* (no light-like singularity on `C`) is read by taking
  `M` non-singular. For a singular HS-surface `Σ`, take `M = Reg Σ`, which contains `C`.
* **(c) The hyperbolic side.** BBS obtain the structure from `C` as the conformal boundary of
  `A_H` (l.1898–1905). Here it comes from the charts (the planner's scope (2)). Near a photon a
  chart is the Klein model, with `C` on `∂ℍ²± = frontier ℍ²±` (`GX.HS.frontier_hypPlus`), and
  `SO₀(1,2)` acts there through `PSL(2,ℝ)` (`GX.smul_rp1ToBd`). The annulus `A`, `A_H`, and the
  claims on lengths and accumulation (l.1899–1903) are not formalized. Past photons use
  `GX.rp1ToBdMinus`.
* **(d) `HS²` only.** BBS's `ι_L` lives on `d̃S² ∪ R₋ ∪ R₊` (l.2979–2990). Its `HS²` form is
  proved here: the leaves, their limits, `ι_ε`, `iotaChart`. Left to `T-3p1-theorem-m-theta`:
  the universal cover `d̃S²` with `R±` (l.2979–2981); the structure from the de Sitter side
  (l.1906–1922, through Mess's Prop. 17); « transversely projective » (l.1913) beyond
  `GX.iota_rp1ToBdMinus`; the coincidence of the two sides (l.1923) and its failure at light-like
  singularities (l.1924–1926).
* **(e) Left and right.** The paper does not say which foliation is the left one. Here `ε = 1` is
  left: `vol3 σ w n_L = −s ⟨n_L | w⟩ ≥ 0` for every future causal `w` (`GX.vol3_nullDir`,
  `GX.vol3_nullDir_nonneg`). On `dS²` and for `w` future timelike it is `> 0`
  (`GX.vol3_nullDir_pos`), so `(w, n_L)` is a direct basis of `T_σ HS²` for HS²'s orientation (`GX.vol3`, outward normal
  first, `GX.BBS.RP1Circles` SCOPE (c)): `n_L` lies to the left of the future. With the opposite
  convention L and R swap. Every theorem is proved for both `ε = ±1`, and the antipodal map swaps
  them (`GX.nullDir_neg`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; builds on
`GX.BBS.HSModel` and `GX.BBS.RP1Circles` (lean-causal `Causal.Flat` through `GX.Lorentz.Bridge`;
no `Causal.*` import, DEC-33).
-/

noncomputable section

open Set Filter Topology Real ComplexConjugate
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-! ### Coordinates `(t, x, y)` on `ℝ^{1,2}` -/

/-- The vector `(t, x, y)` of `ℝ^{1,2} = Causal.Minkowski 2`. -/
def mink3 (t x y : ℝ) : Causal.Minkowski 2 := (t, !₂[x, y])

@[simp] theorem mink3_fst (t x y : ℝ) : (mink3 t x y).1 = t := rfl

@[simp] theorem mink3_snd_zero (t x y : ℝ) : (mink3 t x y).2 0 = x := by simp [mink3]

@[simp] theorem mink3_snd_one (t x y : ℝ) : (mink3 t x y).2 1 = y := by simp [mink3]

theorem mink3_ext {v w : Causal.Minkowski 2} (h0 : v.1 = w.1) (h1 : v.2 0 = w.2 0)
    (h2 : v.2 1 = w.2 1) : v = w := by
  refine Prod.ext h0 ?_
  ext i
  fin_cases i
  · exact h1
  · exact h2

theorem eq_mink3 (v : Causal.Minkowski 2) : v = mink3 v.1 (v.2 0) (v.2 1) :=
  mink3_ext rfl (by simp) (by simp)

theorem norm_sq_snd_two (v : Causal.Minkowski 2) : ‖v.2‖ ^ 2 = v.2 0 ^ 2 + v.2 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem minkQ_coords (v : Causal.Minkowski 2) :
    Causal.Flat.minkQ v = -v.1 ^ 2 + v.2 0 ^ 2 + v.2 1 ^ 2 := by
  rw [Causal.Flat.minkQ, norm_sq_snd_two]; ring

theorem minkB_coords (v w : Causal.Minkowski 2) :
    Causal.Flat.minkB v w = -(v.1 * w.1) + v.2 0 * w.2 0 + v.2 1 * w.2 1 := by
  rw [Causal.Flat.minkB, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem vol3_eq (u v w : Causal.Minkowski 2) : vol3 u v w =
    u.1 * (v.2 0 * w.2 1 - v.2 1 * w.2 0) - u.2 0 * (v.1 * w.2 1 - v.2 1 * w.1) +
      u.2 1 * (v.1 * w.2 0 - v.2 0 * w.1) := by
  simp only [vol3, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  ring

/-- The coordinates `(t, x, y)`, a linear equivalence `ℝ^{1,2} ≃ ℝ³`. -/
def coord3 : Causal.Minkowski 2 ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v.1, v.2 0, v.2 1]
  invFun f := mink3 (f 0) (f 1) (f 2)
  map_add' v w := by funext i; fin_cases i <;> simp
  map_smul' r v := by funext i; fin_cases i <;> simp
  left_inv v := (eq_mink3 v).symm
  right_inv f := by funext i; fin_cases i <;> simp

/-- The basis `e_t, e_x, e_y` of `ℝ^{1,2}`. -/
def basis3 : Module.Basis (Fin 3) ℝ (Causal.Minkowski 2) := Module.Basis.ofEquivFun coord3

theorem vol3_eq_det (u v w : Causal.Minkowski 2) : vol3 u v w = basis3.det ![u, v, w] := by
  rw [Module.Basis.det_apply, Matrix.det_fin_three, vol3_eq]
  simp only [Module.Basis.toMatrix_apply, basis3, Module.Basis.ofEquivFun_repr_apply, coord3,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **`vol3` is the determinant**: `vol3 (f u) (f v) (f w) = det f · vol3 u v w`. -/
theorem vol3_map (f : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) (u v w : Causal.Minkowski 2) :
    vol3 (f u) (f v) (f w) = LinearMap.det f * vol3 u v w := by
  rw [vol3_eq_det, vol3_eq_det, ← Module.Basis.det_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem vol3_basis : vol3 (mink3 1 0 0) (mink3 0 1 0) (mink3 0 0 1) = 1 := by
  rw [vol3_eq]; simp

/-- The determinant of a linear map of `ℝ^{1,2}`, read on the images of `e_t, e_x, e_y`. -/
theorem det_eq_vol3 (f : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) :
    LinearMap.det f = vol3 (f (mink3 1 0 0)) (f (mink3 0 1 0)) (f (mink3 0 0 1)) := by
  rw [vol3_map, vol3_basis, mul_one]

/-- `SO₀(1,2)` preserves `vol3`. -/
theorem vol3_lorentz (A : Causal.Flat.lorentz 2) (u v w : Causal.Minkowski 2) :
    vol3 ((A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) u)
      ((A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v)
      ((A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) w) = vol3 u v w := by
  have := vol3_map ((A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) :
    Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2) u v w
  rw [Causal.Flat.lorentz.det_eq_one A.2, one_mul] at this
  exact this

theorem vol3_smul_left (c : ℝ) (u v w : Causal.Minkowski 2) :
    vol3 (c • u) v w = c * vol3 u v w := by
  rw [vol3_eq, vol3_eq]; simp; ring

theorem timeUnit_eq : Causal.Flat.timeUnit 2 = mink3 1 0 0 :=
  mink3_ext (by simp [Causal.Flat.timeUnit]) (by simp [Causal.Flat.timeUnit])
    (by simp [Causal.Flat.timeUnit])

/-! ### The spinor map and `SL(2,ℝ) → SO₀(1,2)` -/

/-- **The spinor map** `(a, b) ↦ (a² + b², a² − b², 2ab)`, `z = a + ib` (the planner's scope (1)):
`ℝ² → ℝ^{1,2}`, onto the closed future light cone. -/
def spinor (z : ℂ) : Causal.Minkowski 2 :=
  mink3 (z.re ^ 2 + z.im ^ 2) (z.re ^ 2 - z.im ^ 2) (2 * z.re * z.im)

theorem minkQ_spinor (z : ℂ) : Causal.Flat.minkQ (spinor z) = 0 := by
  rw [minkQ_coords]; simp only [spinor, mink3_fst, mink3_snd_zero, mink3_snd_one]; ring

/-- `M = [[a, b], [c, d]]` acting on `ℝ^{1,2}` by `X ↦ M X Mᵀ`, with `(t, x, y)` read as the
symmetric matrix `X = [[t + x, y], [y, t − x]]`, `det X = −minkQ`. -/
def spinL (a b c d : ℝ) : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2 where
  toFun v := mink3
    (v.1 * ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2) + v.2 0 * ((a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) / 2) +
      v.2 1 * (a * b + c * d))
    (v.1 * ((a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) / 2) + v.2 0 * ((a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) / 2) +
      v.2 1 * (a * b - c * d))
    (v.1 * (a * c + b * d) + v.2 0 * (a * c - b * d) + v.2 1 * (a * d + b * c))
  map_add' v w := by
    apply mink3_ext <;> simp only [mink3_fst, mink3_snd_zero, mink3_snd_one, Prod.fst_add,
      Prod.snd_add, PiLp.add_apply] <;> ring
  map_smul' r v := by
    apply mink3_ext <;> simp only [mink3_fst, mink3_snd_zero, mink3_snd_one, Prod.smul_fst,
      Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem spinL_apply (a b c d : ℝ) (v : Causal.Minkowski 2) : spinL a b c d v = mink3
    (v.1 * ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2) + v.2 0 * ((a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2) / 2) +
      v.2 1 * (a * b + c * d))
    (v.1 * ((a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) / 2) + v.2 0 * ((a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) / 2) +
      v.2 1 * (a * b - c * d))
    (v.1 * (a * c + b * d) + v.2 0 * (a * c - b * d) + v.2 1 * (a * d + b * c)) := rfl

/-- **The spinor map is equivariant**: `M · S(z) = S(M z)`. -/
theorem spinL_spinor (a b c d : ℝ) (z : ℂ) :
    spinL a b c d (spinor z) = spinor ⟨a * z.re + b * z.im, c * z.re + d * z.im⟩ := by
  apply mink3_ext <;> simp only [spinL_apply, spinor, mink3_fst, mink3_snd_zero,
    mink3_snd_one] <;> ring

theorem spinL_comp (a b c d a' b' c' d' : ℝ) :
    (spinL a b c d).comp (spinL a' b' c' d') =
      spinL (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply]
  apply mink3_ext <;> simp only [spinL_apply, mink3_fst, mink3_snd_zero, mink3_snd_one] <;> ring

theorem spinL_one : spinL 1 0 0 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  apply mink3_ext <;> simp only [spinL_apply, mink3_fst, mink3_snd_zero, mink3_snd_one,
    LinearMap.id_apply] <;> ring

theorem spinL_neg (a b c d : ℝ) : spinL (-a) (-b) (-c) (-d) = spinL a b c d := by
  refine LinearMap.ext fun v => ?_
  apply mink3_ext <;> simp only [spinL_apply, mink3_fst, mink3_snd_zero, mink3_snd_one] <;> ring

/-- `det (M X Mᵀ) = (det M)² det X`. -/
theorem minkQ_spinL (a b c d : ℝ) (v : Causal.Minkowski 2) :
    Causal.Flat.minkQ (spinL a b c d v) = (a * d - b * c) ^ 2 * Causal.Flat.minkQ v := by
  rw [minkQ_coords, minkQ_coords]
  simp only [spinL_apply, mink3_fst, mink3_snd_zero, mink3_snd_one]
  ring

theorem det_spinL (a b c d : ℝ) : LinearMap.det (spinL a b c d) = (a * d - b * c) ^ 3 := by
  rw [det_eq_vol3, vol3_eq]
  simp only [spinL_apply, mink3_fst, mink3_snd_zero, mink3_snd_one]
  ring

/-- The linear map `X ↦ g X gᵀ` of `g ∈ SL(2,ℝ)`. -/
def spinLinL (g : SL(2, ℝ)) : Causal.Minkowski 2 →ₗ[ℝ] Causal.Minkowski 2 :=
  spinL ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)

theorem sl_det (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

theorem spinLinL_mul (g h : SL(2, ℝ)) : spinLinL (g * h) = (spinLinL g).comp (spinLinL h) := by
  rw [spinLinL, spinLinL, spinLinL, spinL_comp]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem spinLinL_one : spinLinL 1 = LinearMap.id := by
  rw [spinLinL, ← spinL_one]
  simp

/-- **`g ∈ SL(2,ℝ)` acting on `ℝ^{1,2}`**, a linear automorphism. -/
def spinLin (g : SL(2, ℝ)) : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2 :=
  LinearEquiv.ofLinear (spinLinL g) (spinLinL g⁻¹)
    (by rw [← spinLinL_mul, mul_inv_cancel, spinLinL_one])
    (by rw [← spinLinL_mul, inv_mul_cancel, spinLinL_one])

theorem spinLin_apply (g : SL(2, ℝ)) (v : Causal.Minkowski 2) : spinLin g v = spinLinL g v := rfl

theorem spinLin_mem (g : SL(2, ℝ)) : spinLin g ∈ Causal.Flat.lorentz 2 := by
  have hd := sl_det g
  refine Causal.Flat.mem_lorentz_of (fun v => ?_) ?_ ?_
  · rw [spinLin_apply, spinLinL, minkQ_spinL, hd, one_pow, one_mul]
  · rw [spinLin_apply, spinLinL, timeUnit_eq, spinL_apply]
    simp only [mink3_fst, mink3_snd_zero, mink3_snd_one, one_mul]
    nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1),
      sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0)]
  · show LinearMap.det (spinLinL g) = 1
    rw [spinLinL, det_spinL, hd, one_pow]

/-- **`SL(2,ℝ) → SO₀(1,2)`**, `g ↦ (X ↦ g X gᵀ)`. -/
def spinLorentz : SL(2, ℝ) →* Causal.Flat.lorentz 2 where
  toFun g := ⟨spinLin g, spinLin_mem g⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun v => by
    show spinLinL 1 v = v
    rw [spinLinL_one, LinearMap.id_apply])
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun v => by
    show spinLinL (g * h) v = spinLinL g (spinLinL h v)
    rw [spinLinL_mul, LinearMap.comp_apply])

theorem spinLorentz_apply (g : SL(2, ℝ)) (v : Causal.Minkowski 2) :
    (spinLorentz g : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) v = spinLinL g v := rfl

theorem spinLorentz_spinor (g : SL(2, ℝ)) (z : ℂ) :
    (spinLorentz g : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) (spinor z) =
      spinor (slLin g z) := by
  rw [spinLorentz_apply, spinLinL, spinL_spinor, slLin_apply]

theorem spinor_fst (z : ℂ) : (spinor z).1 = Complex.normSq z := by
  rw [spinor, mink3_fst, Complex.normSq_apply]; ring

/-! ### `ℝP¹ ≅ ∂ℍ²₊` through the spinor map -/

theorem repr_circle_mem (w : Circle) :
    Complex.orthonormalBasisOneI.repr (w : ℂ) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.1 w.2

/-- The unit circle of `ℂ` onto the unit circle of `ℝ²`, `w ↦ (Re w, Im w)`. -/
def circleToPenrose : Circle ≃ₜ Causal.Flat.PenroseSphere 2 where
  toFun w := ⟨Complex.orthonormalBasisOneI.repr (w : ℂ), repr_circle_mem w⟩
  invFun u := ⟨Complex.orthonormalBasisOneI.repr.symm (u : EuclideanSpace ℝ (Fin 2)), by
    show _ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
    exact Causal.Flat.norm_penroseSphere u⟩
  left_inv w := Circle.ext (LinearIsometryEquiv.symm_apply_apply _ _)
  right_inv u := Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
  continuous_toFun :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp RP1.continuous_coe).subtype_mk
      repr_circle_mem
  continuous_invFun := RP1.isInducing_coe.continuous_iff.2
    (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val)

/-- **`ℝP¹ ≅ ∂ℍ²₊`** (BBS l.763, the planner's scope (1)): the line `ℝ z` goes to the null ray of
the spinor `S(z) = (|z|², z²)`; on the circle model `ℝP¹ = 𝕊¹` of `GX.RP1` this is
`w ↦ [(1, Re w, Im w)]` (`GX.coe_rp1ToBdPlus`, `GX.coe_rp1ToBdPlus_mk`). -/
def rp1ToBdPlus : RP1 ≃ₜ HS.piece 2 .bdPlus := circleToPenrose.trans HS.bdPlusHomeomorph.symm

theorem coe_rp1ToBdPlus (w : RP1) :
    ((rp1ToBdPlus w : HS 2) : Causal.Minkowski 2) = mink3 1 (w : ℂ).re (w : ℂ).im := by
  have h : ((rp1ToBdPlus w : HS 2) : Causal.Minkowski 2) =
      (1, Complex.orthonormalBasisOneI.repr (w : ℂ)) := rfl
  rw [h]
  apply mink3_ext
  · rfl
  · simp [Complex.orthonormalBasisOneI_repr_apply]
  · simp [Complex.orthonormalBasisOneI_repr_apply]

/-- `rp1ToBdPlus (mk z)` is the null ray of the spinor `S(z)`. -/
theorem coe_rp1ToBdPlus_mk {z : ℂ} (hz : z ≠ 0) :
    ((rp1ToBdPlus (RP1.mk z) : HS 2) : Causal.Minkowski 2) = (Complex.normSq z)⁻¹ • spinor z := by
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  rw [coe_rp1ToBdPlus, RP1.coe_mk hz]
  apply mink3_ext
  · simp only [mink3_fst, Prod.smul_fst, smul_eq_mul, spinor_fst, inv_mul_cancel₀ hn]
  · simp only [mink3_snd_zero, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, spinor,
      Complex.div_re, Complex.conj_re, Complex.conj_im, Complex.normSq_conj]
    rw [Complex.normSq_apply] at hn ⊢
    field_simp
    ring
  · simp only [mink3_snd_one, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, spinor,
      Complex.div_im, Complex.conj_re, Complex.conj_im, Complex.normSq_conj]
    rw [Complex.normSq_apply] at hn ⊢
    field_simp
    ring

theorem isFutureCausal_rp1ToBdPlus (w : RP1) :
    Causal.Flat.IsFutureCausal ((rp1ToBdPlus w : HS 2) : Causal.Minkowski 2) :=
  (HS.mem_bdPlus_iff'.1 (rp1ToBdPlus w).2).2

/-- **Equivariance** (BBS l.763): `g · [S(z)] = [S(g z)]` for `g ∈ SL(2,ℝ)`. -/
theorem spinLorentz_smul_rp1ToBdPlus (g : SL(2, ℝ)) (w : RP1) :
    spinLorentz g • (rp1ToBdPlus w : HS 2) = rp1ToBdPlus (g • w) := by
  obtain ⟨z, hz, rfl⟩ : ∃ z, z ≠ 0 ∧ RP1.mk z = w := ⟨RP1.rep w, RP1.rep_ne_zero w, RP1.mk_rep w⟩
  have hgz := slLin_ne_zero g hz
  rw [RP1.sl_smul_mk g hz]
  apply Subtype.ext
  rw [HS.coe_smul_of_isFutureCausal _ (isFutureCausal_rp1ToBdPlus _), coe_rp1ToBdPlus_mk hz,
    coe_rp1ToBdPlus_mk hgz, map_smul, spinLorentz_spinor, Prod.smul_fst, spinor_fst, smul_eq_mul,
    smul_smul]
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  congr 1
  field_simp

/-! ### `SO₀(1,2) ≅ PSL(2,ℝ)` (BBS l.763) -/

/-- `±1` acts trivially on `ℝ^{1,2}`. -/
theorem center_le_ker_spinLorentz : Subgroup.center SL(2, ℝ) ≤ spinLorentz.ker := fun g hg => by
  rw [MonoidHom.mem_ker]
  obtain ⟨r, hr, hgr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  simp only [Fintype.card_fin] at hr
  have e : ∀ i j, (g : Matrix (Fin 2) (Fin 2) ℝ) i j = if i = j then r else 0 := by
    intro i j
    rw [← hgr, Matrix.scalar_apply, Matrix.diagonal_apply]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  show spinLinL g v = v
  rw [spinLinL, e, e, e, e]
  simp only [if_true, Fin.isValue, zero_ne_one, one_ne_zero, if_false]
  apply mink3_ext
  · simp only [spinL_apply, mink3_fst]; linear_combination v.1 * hr
  · simp only [spinL_apply, mink3_snd_zero]; linear_combination v.2 0 * hr
  · simp only [spinL_apply, mink3_snd_one]; linear_combination v.2 1 * hr

/-- **The kernel of `SL(2,ℝ) → SO₀(1,2)` is `{±1}`.** -/
theorem ker_spinLorentz : spinLorentz.ker = Subgroup.center SL(2, ℝ) := by
  refine le_antisymm (fun g hg => ?_) center_le_ker_spinLorentz
  rw [MonoidHom.mem_ker] at hg
  refine RP1.mem_center_of_eqOn isOpen_univ univ_nonempty fun w _ => ?_
  have h := spinLorentz_smul_rp1ToBdPlus g w
  rw [hg, one_smul] at h
  exact (rp1ToBdPlus.injective (Subtype.ext h)).symm

/-- The hyperbolic element `diag(e^{ζ/2}, e^{−ζ/2})` of `SL(2,ℝ)`. -/
def boostSL (ζ : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (ζ / 2), 0; 0, Real.exp (-(ζ / 2))], by
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, ← Real.exp_add, add_neg_cancel, Real.exp_zero]⟩

/-- `diag(e^{ζ/2}, e^{−ζ/2})` acts on `ℝ^{1,2}` as the boost of rapidity `ζ` along `x`. -/
theorem spinLorentz_boostSL (ζ : ℝ) : spinLorentz (boostSL ζ) = HS.boost (d := 2) 0 ζ := by
  have h1 : Real.exp (ζ / 2) ^ 2 = Real.exp ζ := by rw [sq, ← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(ζ / 2)) ^ 2 = Real.exp (-ζ) := by rw [sq, ← Real.exp_add]; ring_nf
  have h3 : Real.exp (ζ / 2) * Real.exp (-(ζ / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  show spinLinL (boostSL ζ) v = _
  rw [HS.boost_apply, Real.cosh_eq, Real.sinh_eq]
  apply mink3_ext
  · simp [spinLinL, boostSL, spinL_apply]
    linear_combination (v.1 / 2 + v.2 0 / 2) * h1 + (v.1 / 2 - v.2 0 / 2) * h2
  · simp [spinLinL, boostSL, spinL_apply]
    linear_combination (v.1 / 2 + v.2 0 / 2) * h1 + (v.2 0 / 2 - v.1 / 2) * h2
  · simp [spinLinL, boostSL, spinL_apply]
    linear_combination v.2 1 * h3

/-- Every rotation of `ℝ²` (an element of `SO(2)`) is `z ↦ a z` for some `a` in the circle. -/
theorem exists_circle_of_specialOrth (R : SpecialOrth (EuclideanSpace ℝ (Fin 2))) :
    ∃ a : Circle, ∀ x : EuclideanSpace ℝ (Fin 2),
      (R : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) x =
        Complex.orthonormalBasisOneI.repr ((a : ℂ) * Complex.orthonormalBasisOneI.repr.symm x) := by
  set e := Complex.orthonormalBasisOneI.repr
  set R' : ℂ ≃ₗᵢ[ℝ] ℂ :=
    (e.trans (R : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))).trans e.symm
  have hdet : LinearMap.det (R'.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
    have h : (R'.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
        (e.symm.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ) ∘ₗ
          ((R : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearEquiv :
            EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
          (e.symm.toLinearEquiv.symm : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) :=
      LinearMap.ext fun z => rfl
    rw [h, LinearMap.det_conj]
    exact R.2
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex R'
  · refine ⟨a, fun x => ?_⟩
    have h := congrArg (fun f : ℂ ≃ₗᵢ[ℝ] ℂ => f (e.symm x)) ha
    simp only [R', LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
      rotation_apply] at h
    rw [← h, LinearIsometryEquiv.apply_symm_apply]
  · exfalso
    rw [ha] at hdet
    have h : ((Complex.conjLIE.trans (rotation a)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
        ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
          (Complex.conjAe.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) :=
      LinearMap.ext fun z => rfl
    have hc : LinearMap.det (Complex.conjAe.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 := Complex.det_conjAe
    rw [h, LinearMap.det_comp, det_rotation, hc] at hdet
    norm_num at hdet

/-- A spatial rotation of `ℝ^{1,2}` is the image of a rotation of `SL(2,ℝ)` (by half the angle). -/
theorem rot_mem_range_spinLorentz (R : SpecialOrth (EuclideanSpace ℝ (Fin 2))) :
    HS.rot R ∈ spinLorentz.range := by
  obtain ⟨a, ha⟩ := exists_circle_of_specialOrth R
  set v : Circle := Circle.exp (Complex.arg (a : ℂ) / 2)
  have hv : (v : ℂ) ^ 2 = a := by
    have : v ^ 2 = a := by
      rw [← Circle.exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero,
        Circle.exp_arg]
    rw [← Circle.coe_pow, this]
  have hn : (v : ℂ).re ^ 2 + (v : ℂ).im ^ 2 = 1 := by
    have := Circle.normSq_coe v
    rw [Complex.normSq_apply] at this
    linear_combination this
  have hre : (a : ℂ).re = (v : ℂ).re ^ 2 - (v : ℂ).im ^ 2 := by
    rw [← hv, sq, Complex.mul_re]; ring
  have him : (a : ℂ).im = 2 * (v : ℂ).re * (v : ℂ).im := by
    rw [← hv, sq, Complex.mul_im]; ring
  let g : SL(2, ℝ) := ⟨!![(v : ℂ).re, -(v : ℂ).im; (v : ℂ).im, (v : ℂ).re], by
    rw [Matrix.det_fin_two_of]; linear_combination hn⟩
  refine ⟨g, Subtype.ext (LinearEquiv.ext fun w => ?_)⟩
  show spinLinL g w = (HS.rot R : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2) w
  rw [HS.rot_apply, ha]
  apply mink3_ext
  · simp [spinLinL, g, spinL_apply]
    linear_combination w.1 * hn
  · simp [spinLinL, g, spinL_apply, Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, hre, him]
    ring
  · simp [spinLinL, g, spinL_apply, Complex.orthonormalBasisOneI_repr_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, hre, him]
    ring

/-- **`SL(2,ℝ) → SO₀(1,2)` is onto**: its image contains the rotations and the boosts, which
generate `SO₀(1,2)` (`GX.HS.boostRot_eq_top`). -/
theorem spinLorentz_surjective : Function.Surjective spinLorentz := by
  intro A
  have hA : A ∈ HS.boostRot (d := 2) le_rfl := by rw [HS.boostRot_eq_top]; trivial
  have hle : HS.boostRot (d := 2) le_rfl ≤ spinLorentz.range := by
    rw [HS.boostRot, Subgroup.closure_le]
    rintro _ (⟨R, rfl⟩ | ⟨ζ, rfl⟩)
    · exact rot_mem_range_spinLorentz R
    · exact ⟨boostSL ζ, spinLorentz_boostSL ζ⟩
  exact hle hA

/-- `PSL(2,ℝ) → SO₀(1,2)`. -/
def pslToLorentz : PSL(2, ℝ) →* Causal.Flat.lorentz 2 :=
  QuotientGroup.lift (Subgroup.center SL(2, ℝ)) spinLorentz center_le_ker_spinLorentz

theorem pslToLorentz_mk (g : SL(2, ℝ)) : pslToLorentz (pslMk g) = spinLorentz g := rfl

theorem pslToLorentz_injective : Function.Injective pslToLorentz := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  obtain ⟨g, rfl⟩ := pslMk_surjective g
  rw [pslToLorentz_mk, ← MonoidHom.mem_ker, ker_spinLorentz] at hg
  exact (QuotientGroup.eq_one_iff g).2 hg

theorem pslToLorentz_surjective : Function.Surjective pslToLorentz := fun A => by
  obtain ⟨g, hg⟩ := spinLorentz_surjective A
  exact ⟨pslMk g, hg⟩

/-- **`SO₀(1,2) ≈ PSL(2,ℝ)`** (BBS l.763), through the spinor map. -/
def pslEquivLorentz : PSL(2, ℝ) ≃* Causal.Flat.lorentz 2 :=
  MulEquiv.ofBijective pslToLorentz ⟨pslToLorentz_injective, pslToLorentz_surjective⟩

theorem pslEquivLorentz_mk (g : SL(2, ℝ)) : pslEquivLorentz (pslMk g) = spinLorentz g := rfl

/-- **`ℝP¹ ≅ ∂ℍ²₊` is `PSL(2,ℝ) ≅ SO₀(1,2)`-equivariant** (BBS l.763). -/
theorem smul_rp1ToBdPlus (A : Causal.Flat.lorentz 2) (w : RP1) :
    A • (rp1ToBdPlus w : HS 2) = rp1ToBdPlus (pslEquivLorentz.symm A • w) := by
  obtain ⟨g, hg⟩ := pslMk_surjective (pslEquivLorentz.symm A)
  have hA : A = spinLorentz g := by rw [← pslEquivLorentz_mk, hg, MulEquiv.apply_symm_apply]
  rw [← hg, pslMk_smul, hA, spinLorentz_smul_rp1ToBdPlus]

/-- The antipodal map `∂ℍ²₊ ≃ₜ ∂ℍ²₋` (`∂ℍ²₋ = −∂ℍ²₊`). -/
def bdNegHomeomorph : HS.piece 2 .bdPlus ≃ₜ HS.piece 2 .bdMinus where
  toFun σ := ⟨-(σ : HS 2), HS.neg_mem_bdMinus_iff.2 σ.2⟩
  invFun τ := ⟨-(τ : HS 2), HS.neg_mem_bdMinus_iff.1 (by rw [neg_neg]; exact τ.2)⟩
  left_inv σ := Subtype.ext (neg_neg _)
  right_inv τ := Subtype.ext (neg_neg _)
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

/-- **`ℝP¹ ≅ ∂ℍ²₋`**: the antipode of `ℝP¹ ≅ ∂ℍ²₊`. -/
def rp1ToBdMinus : RP1 ≃ₜ HS.piece 2 .bdMinus := rp1ToBdPlus.trans bdNegHomeomorph

theorem coe_rp1ToBdMinus (w : RP1) :
    (rp1ToBdMinus w : HS 2) = -(rp1ToBdPlus w : HS 2) := rfl

/-- **`ℝP¹ ≅ ∂ℍ²₋` is equivariant.** -/
theorem smul_rp1ToBdMinus (A : Causal.Flat.lorentz 2) (w : RP1) :
    A • (rp1ToBdMinus w : HS 2) = rp1ToBdMinus (pslEquivLorentz.symm A • w) := by
  rw [coe_rp1ToBdMinus, coe_rp1ToBdMinus, hs_smul_neg, smul_rp1ToBdPlus]

/-! ### The isotropic foliations of `dS²` and the projections `ι_L`, `ι_R` -/

/-- **`dS² ∪ ∂ℍ²₊ ∪ ∂ℍ²₋`** (`GX.HS.mem_closedDS_iff`): the rays with `minkQ ≥ 0`, the closed
annulus of `HS²` between the two circles of photons. -/
def HS.closedDS : Set (HS 2) := {σ | 0 ≤ Causal.Flat.minkQ (σ : Causal.Minkowski 2)}

theorem HS.mem_closedDS_iff {σ : HS 2} : σ ∈ HS.closedDS ↔
    σ ∈ HS.piece 2 .deSitter ∨ σ ∈ HS.piece 2 .bdPlus ∨ σ ∈ HS.piece 2 .bdMinus := by
  constructor
  · intro h
    have h' : 0 ≤ Causal.Flat.minkQ (σ : Causal.Minkowski 2) := h
    rcases h'.lt_or_eq with h | h
    · exact Or.inl h
    · rcases (HS.fst_ne_zero_of_minkQ_nonpos σ h.symm.le).lt_or_gt with hn | hp
      · exact Or.inr (Or.inr ⟨h.symm, hn⟩)
      · exact Or.inr (Or.inl ⟨h.symm, hp⟩)
  · rintro (h | h | h)
    · have h' : 0 < Causal.Flat.minkQ (σ : Causal.Minkowski 2) := h
      exact h'.le
    · exact h.1.symm.le
    · exact h.1.symm.le

theorem HS.smul_mem_closedDS_iff (A : Causal.Flat.lorentz 2) {σ : HS 2} :
    A • σ ∈ HS.closedDS ↔ σ ∈ HS.closedDS := by
  rw [HS.mem_closedDS_iff, HS.mem_closedDS_iff, HS.smul_mem_piece_iff, HS.smul_mem_piece_iff,
    HS.smul_mem_piece_iff]

theorem HS.isClosed_closedDS : IsClosed HS.closedDS :=
  isClosed_le continuous_const (Causal.Flat.continuous_minkQ.comp continuous_subtype_val)

/-- On `dS² ∪ ∂ℍ²±` the sup norm puts the ray at `(t, x, y)` with `x² + y² = 1`, `t² ≤ 1`. -/
theorem HS.closedDS_coord {σ : HS 2} (h : σ ∈ HS.closedDS) :
    (σ : Causal.Minkowski 2).2 0 ^ 2 + (σ : Causal.Minkowski 2).2 1 ^ 2 = 1 ∧
      (σ : Causal.Minkowski 2).1 ^ 2 ≤ 1 := by
  have hm := HS.max_abs_fst_norm_snd σ
  have h1 : (σ : Causal.Minkowski 2).1 ^ 2 ≤ ‖(σ : Causal.Minkowski 2).2‖ ^ 2 := by
    have : 0 ≤ Causal.Flat.minkQ (σ : Causal.Minkowski 2) := h
    rw [Causal.Flat.minkQ] at this
    linarith
  have h2 : |(σ : Causal.Minkowski 2).1| ≤ ‖(σ : Causal.Minkowski 2).2‖ := by
    have := sq_le_sq.1 h1
    rwa [abs_norm] at this
  rw [max_eq_right h2] at hm
  have h3 := norm_sq_snd_two (σ : Causal.Minkowski 2)
  rw [hm, one_pow] at h3
  refine ⟨h3.symm, ?_⟩
  rw [hm, one_pow] at h1
  exact h1

/-- **The null direction** `n_ε(v) = (1, t x + ε s y, t y − ε s x)`, `s = √(1 − t²)`, at
`v = (t, x, y)`; `ε = 1` is the left one, `ε = −1` the right one. -/
def nullDir (ε : ℝ) (v : Causal.Minkowski 2) : Causal.Minkowski 2 :=
  mink3 1 (v.1 * v.2 0 + ε * √(1 - v.1 ^ 2) * v.2 1) (v.1 * v.2 1 - ε * √(1 - v.1 ^ 2) * v.2 0)

section NullDir

variable {ε : ℝ} {v : Causal.Minkowski 2}

theorem nullDir_fst (ε : ℝ) (v : Causal.Minkowski 2) : (nullDir ε v).1 = 1 := rfl

theorem nullDir_sq (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1) :
    (nullDir ε v).2 0 ^ 2 + (nullDir ε v).2 1 ^ 2 = 1 := by
  have hs : √(1 - v.1 ^ 2) ^ 2 = 1 - v.1 ^ 2 := Real.sq_sqrt (by linarith)
  simp only [nullDir, mink3_snd_zero, mink3_snd_one]
  linear_combination (v.1 ^ 2 + ε ^ 2 * √(1 - v.1 ^ 2) ^ 2) * hx + hs + √(1 - v.1 ^ 2) ^ 2 * hε

theorem minkQ_nullDir (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1) :
    Causal.Flat.minkQ (nullDir ε v) = 0 := by
  rw [minkQ_coords, nullDir_fst]
  linear_combination nullDir_sq hε hx ht

theorem minkB_nullDir (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) : Causal.Flat.minkB v (nullDir ε v) = 0 := by
  rw [minkB_coords]
  simp only [nullDir, mink3_fst, mink3_snd_zero, mink3_snd_one]
  linear_combination v.1 * hx

theorem norm_nullDir_snd (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1) :
    ‖(nullDir ε v).2‖ = 1 := by
  have h := norm_sq_snd_two (nullDir ε v)
  rw [nullDir_sq hε hx ht] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem isFutureCausal_nullDir (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1)
    (ht : v.1 ^ 2 ≤ 1) : Causal.Flat.IsFutureCausal (nullDir ε v) :=
  ⟨zero_le_one, (minkQ_nullDir hε hx ht).le⟩

theorem nullDir_ne_zero (ε : ℝ) (v : Causal.Minkowski 2) : nullDir ε v ≠ 0 := fun h => by
  have := congrArg Prod.fst h
  rw [nullDir_fst] at this
  exact one_ne_zero this

/-- **The orientation of `n_ε`**: `vol3 v w n_ε = −ε s ⟨n_ε | w⟩`. -/
theorem vol3_nullDir (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1)
    (w : Causal.Minkowski 2) :
    vol3 v w (nullDir ε v) = -(ε * √(1 - v.1 ^ 2)) * Causal.Flat.minkB (nullDir ε v) w := by
  have hs : √(1 - v.1 ^ 2) ^ 2 = 1 - v.1 ^ 2 := Real.sq_sqrt (by linarith)
  rw [vol3_eq, minkB_coords]
  simp only [nullDir, mink3_fst, mink3_snd_zero, mink3_snd_one]
  linear_combination (ε * √(1 - v.1 ^ 2) * w.1) * hx +
    (w.2 0 * v.2 1 - w.2 1 * v.2 0) * hs + (w.2 0 * v.2 1 - w.2 1 * v.2 0) * √(1 - v.1 ^ 2) ^ 2 * hε

/-- **`n_ε` is on the `ε` side of every future causal `w`**: `ε vol3 v w n_ε ≥ 0`. For `ε = 1`,
`(w, n_L)` is a direct basis of `T_v HS²` (`vol3 v w n_L > 0` off the boundary): `n_L` lies to the
left of the future. -/
theorem vol3_nullDir_nonneg (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1)
    {w : Causal.Minkowski 2} (hw : Causal.Flat.IsFutureCausal w) :
    0 ≤ ε * vol3 v w (nullDir ε v) := by
  rw [vol3_nullDir hε hx ht]
  have hB := Causal.Flat.minkB_nonpos_of_future (isFutureCausal_nullDir hε hx ht) hw
  have hs := Real.sqrt_nonneg (1 - v.1 ^ 2)
  have : ε * (-(ε * √(1 - v.1 ^ 2)) * Causal.Flat.minkB (nullDir ε v) w) =
      -(√(1 - v.1 ^ 2) * Causal.Flat.minkB (nullDir ε v) w) := by
    linear_combination (-(√(1 - v.1 ^ 2) * Causal.Flat.minkB (nullDir ε v) w)) * hε
  rw [this]
  nlinarith

/-- **Strictly on the `ε` side off the boundary**: for `v ∈ dS²` (`t² < 1`) and `w` future
timelike, `ε vol3 v w n_ε > 0`, i.e. `(w, n_L)` is a direct basis of `T_v HS²` for `ε = 1`. -/
theorem vol3_nullDir_pos (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 < 1)
    {w : Causal.Minkowski 2} (hw : Causal.Flat.IsFutureTimelike w) :
    0 < ε * vol3 v w (nullDir ε v) := by
  rw [vol3_nullDir hε hx ht.le]
  have hs : 0 < √(1 - v.1 ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hN := nullDir_sq hε hx ht.le
  obtain ⟨hw0, hwq⟩ := hw
  rw [minkQ_coords] at hwq
  have hB : Causal.Flat.minkB (nullDir ε v) w < 0 := by
    rw [minkB_coords, nullDir_fst]
    set p := (nullDir ε v).2 0
    set q := (nullDir ε v).2 1
    have hcs : (p * w.2 0 + q * w.2 1) ^ 2 ≤ w.2 0 ^ 2 + w.2 1 ^ 2 := by
      nlinarith [sq_nonneg (p * w.2 1 - q * w.2 0)]
    nlinarith [sq_nonneg (p * w.2 0 + q * w.2 1 - w.1)]
  have : ε * (-(ε * √(1 - v.1 ^ 2)) * Causal.Flat.minkB (nullDir ε v) w) =
      -(√(1 - v.1 ^ 2) * Causal.Flat.minkB (nullDir ε v) w) := by
    linear_combination (-(√(1 - v.1 ^ 2) * Causal.Flat.minkB (nullDir ε v) w)) * hε
  rw [this]
  nlinarith

/-- **Uniqueness of `n_ε`**: a future null `n ≠ 0` orthogonal to `v`, on the `ε` side of the time
axis, is a positive multiple of `n_ε(v)`. -/
theorem eq_smul_nullDir (hε : ε ^ 2 = 1) (hx : v.2 0 ^ 2 + v.2 1 ^ 2 = 1) (ht : v.1 ^ 2 ≤ 1)
    {n : Causal.Minkowski 2} (hn : Causal.Flat.IsFutureCausal n) (hnq : Causal.Flat.minkQ n = 0)
    (hn0 : n ≠ 0) (horth : Causal.Flat.minkB v n = 0)
    (hvol : 0 ≤ ε * vol3 v (mink3 1 0 0) n) : n = n.1 • nullDir ε v := by
  have hn1 : 0 < n.1 := (HS.fst_pos_iff_isFutureCausal hn0 hnq).2 hn
  have hs : √(1 - v.1 ^ 2) ^ 2 = 1 - v.1 ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ √(1 - v.1 ^ 2) := Real.sqrt_nonneg _
  rw [minkQ_coords] at hnq
  rw [minkB_coords] at horth
  have hv3 : vol3 v (mink3 1 0 0) n = -(v.2 0 * n.2 1 - v.2 1 * n.2 0) := by
    rw [vol3_eq]; simp only [mink3_fst, mink3_snd_zero, mink3_snd_one]; ring
  rw [hv3] at hvol
  have ha : v.2 0 * n.2 0 + v.2 1 * n.2 1 = v.1 * n.1 := by linarith
  have hb2 : (v.2 0 * n.2 1 - v.2 1 * n.2 0) ^ 2 = (n.1 * √(1 - v.1 ^ 2)) ^ 2 := by
    linear_combination (n.2 0 ^ 2 + n.2 1 ^ 2) * hx
      - (v.2 0 * n.2 0 + v.2 1 * n.2 1 + v.1 * n.1) * ha + hnq - n.1 ^ 2 * hs
  have hεb : ε * (v.2 0 * n.2 1 - v.2 1 * n.2 0) = -(n.1 * √(1 - v.1 ^ 2)) := by
    have hsq : (ε * (v.2 0 * n.2 1 - v.2 1 * n.2 0) + n.1 * √(1 - v.1 ^ 2)) *
        (ε * (v.2 0 * n.2 1 - v.2 1 * n.2 0) - n.1 * √(1 - v.1 ^ 2)) = 0 := by
      linear_combination (v.2 0 * n.2 1 - v.2 1 * n.2 0) ^ 2 * hε + hb2
    have hnn : 0 ≤ n.1 * √(1 - v.1 ^ 2) := mul_nonneg hn1.le hs0
    rcases mul_eq_zero.1 hsq with h | h
    · linarith
    · nlinarith
  have hb : v.2 0 * n.2 1 - v.2 1 * n.2 0 = -(ε * n.1 * √(1 - v.1 ^ 2)) := by
    linear_combination ε * hεb - (v.2 0 * n.2 1 - v.2 1 * n.2 0) * hε
  apply mink3_ext
  · simp [nullDir]
  · simp only [nullDir, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, mink3_snd_zero]
    linear_combination (-n.2 0) * hx + v.2 0 * ha - v.2 1 * hb
  · simp only [nullDir, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, mink3_snd_one]
    linear_combination (-n.2 1) * hx + v.2 1 * ha + v.2 0 * hb

end NullDir

theorem continuous_mink3 {X : Type*} [TopologicalSpace X] {f g h : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) : Continuous fun a => mink3 (f a) (g a) (h a) := by
  unfold mink3; fun_prop

theorem continuous_nullDir (ε : ℝ) : Continuous (nullDir ε) := by
  unfold nullDir
  refine continuous_mink3 continuous_const ?_ ?_ <;>
  · have h0 : Continuous fun v : Causal.Minkowski 2 => v.2 0 :=
      (PiLp.continuous_apply 2 _ 0).comp continuous_snd
    have h1 : Continuous fun v : Causal.Minkowski 2 => v.2 1 :=
      (PiLp.continuous_apply 2 _ 1).comp continuous_snd
    have hs : Continuous fun v : Causal.Minkowski 2 => √(1 - v.1 ^ 2) :=
      Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2))
    fun_prop

/-! #### `ι_L`, `ι_R : dS² ∪ ∂ℍ²± → ∂ℍ²₊` -/

instance lorentzClosedDSAction : MulAction (Causal.Flat.lorentz 2) HS.closedDS where
  smul A σ := ⟨A • (σ : HS 2), (HS.smul_mem_closedDS_iff A).2 σ.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

theorem coe_smul_closedDS (A : Causal.Flat.lorentz 2) (σ : HS.closedDS) :
    ((A • σ : HS.closedDS) : HS 2) = A • (σ : HS 2) := rfl

/-- `SO₀(1,2)` acts on each piece of `HS²`. -/
instance lorentzPieceAction (k : HSPiece) : MulAction (Causal.Flat.lorentz 2) (HS.piece 2 k) where
  smul A σ := ⟨A • (σ : HS 2), (HS.smul_mem_piece_iff A).2 σ.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

theorem coe_smul_piece {k : HSPiece} (A : Causal.Flat.lorentz 2) (σ : HS.piece 2 k) :
    ((A • σ : HS.piece 2 k) : HS 2) = A • (σ : HS 2) := rfl

section Iota

variable {ε : ℝ}

theorem nullDir_mem_sphere (hε : ε ^ 2 = 1) (σ : HS.closedDS) :
    (nullDir ε ((σ : HS 2) : Causal.Minkowski 2)).2 ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  mem_sphere_zero_iff_norm.2
    (norm_nullDir_snd hε (HS.closedDS_coord σ.2).1 (HS.closedDS_coord σ.2).2)

/-- **`ι_ε`** (BBS l.2983–2990, in `HS²`): a point of `dS² ∪ ∂ℍ²±` goes to the end in `∂ℍ²₊` of
its `ε`-leaf, the null ray `[n_ε]` orthogonal to it on the `ε` side (`ε = 1`: `GX.iotaL`). -/
def iota (ε : ℝ) (hε : ε ^ 2 = 1) (σ : HS.closedDS) : HS.piece 2 .bdPlus :=
  HS.bdPlusHomeomorph.symm
    ⟨(nullDir ε ((σ : HS 2) : Causal.Minkowski 2)).2, nullDir_mem_sphere hε σ⟩

theorem coe_iota (hε : ε ^ 2 = 1) (σ : HS.closedDS) :
    (((iota ε hε σ : HS.piece 2 .bdPlus) : HS 2) : Causal.Minkowski 2) =
      nullDir ε ((σ : HS 2) : Causal.Minkowski 2) := rfl

/-- **`ι_L`**: the projection along the left isotropic foliation (BBS l.2983–2990). -/
def iotaL : HS.closedDS → HS.piece 2 .bdPlus := iota 1 (one_pow 2)

/-- **`ι_R`**: the projection along the right isotropic foliation. -/
def iotaR : HS.closedDS → HS.piece 2 .bdPlus := iota (-1) neg_one_sq

/-- **`ι_ε` is continuous.** -/
theorem continuous_iota (hε : ε ^ 2 = 1) : Continuous (iota ε hε) :=
  HS.bdPlusHomeomorph.symm.continuous.comp (Continuous.subtype_mk (continuous_snd.comp
    ((continuous_nullDir ε).comp (continuous_subtype_val.comp continuous_subtype_val))) _)

/-- **`ι_ε` is proper** (BBS l.2989: "a proper submersion"; `dS² ∪ ∂ℍ²±` is compact). -/
theorem isProperMap_iota (hε : ε ^ 2 = 1) : IsProperMap (iota ε hε) := by
  haveI : CompactSpace HS.closedDS := isCompact_iff_compactSpace.1 HS.isClosed_closedDS.isCompact
  exact (continuous_iota hε).isProperMap

/-- **`ι_ε` is `SO₀(1,2)`-equivariant.** -/
theorem iota_smul (hε : ε ^ 2 = 1) (A : Causal.Flat.lorentz 2) (σ : HS.closedDS) :
    iota ε hε (A • σ) = A • iota ε hε σ := by
  set A' : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2 := A.1
  set N := nullDir ε ((σ : HS 2) : Causal.Minkowski 2)
  obtain ⟨hx, ht⟩ := HS.closedDS_coord σ.2
  have hNf : Causal.Flat.IsFutureCausal N := isFutureCausal_nullDir hε hx ht
  have hAN : Causal.Flat.IsFutureCausal (A' N) := Causal.Flat.lorentz.isFutureCausal_apply A.2 hNf
  have hANq : Causal.Flat.minkQ (A' N) = 0 := by
    rw [Causal.Flat.lorentz.minkQ_apply A.2, minkQ_nullDir hε hx ht]
  have hAN0 : A' N ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 (nullDir_ne_zero ε _)
  obtain ⟨c, hc, hcA⟩ := HS.exists_coe_smul A (σ : HS 2)
  obtain ⟨hx', ht'⟩ := HS.closedDS_coord (A • σ).2
  rw [coe_smul_closedDS] at hx' ht'
  have horth : Causal.Flat.minkB ((A • (σ : HS 2) : HS 2) : Causal.Minkowski 2) (A' N) = 0 := by
    rw [hcA, Causal.Flat.minkB_smul_left, Causal.Flat.lorentz.minkB_apply A.2, minkB_nullDir hx,
      mul_zero]
  have hvol : 0 ≤ ε * vol3 ((A • (σ : HS 2) : HS 2) : Causal.Minkowski 2) (mink3 1 0 0) (A' N) := by
    rw [hcA, vol3_smul_left]
    have he : mink3 1 0 0 = A' (A'.symm (mink3 1 0 0)) := (A'.apply_symm_apply _).symm
    rw [he, vol3_lorentz]
    have hw : Causal.Flat.IsFutureCausal (A'.symm (mink3 1 0 0)) := by
      have := Causal.Flat.lorentz.isFutureCausal_apply ((Causal.Flat.lorentz 2).inv_mem A.2)
        (v := mink3 1 0 0) ⟨by simp, by rw [minkQ_coords]; simp⟩
      exact this
    have := vol3_nullDir_nonneg hε hx ht hw
    nlinarith
  have huniq := eq_smul_nullDir hε hx' ht' hAN hANq hAN0 horth hvol
  have hpos : 0 < (A' N).1 := (HS.fst_pos_iff_isFutureCausal hAN0 hANq).2 hAN
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_smul_piece, HS.coe_smul_of_isFutureCausal A (by rw [coe_iota]; exact hNf), coe_iota,
    coe_iota, coe_smul_closedDS]
  conv_rhs => rw [huniq]
  rw [smul_smul, Prod.smul_fst, nullDir_fst, smul_eq_mul, mul_one, inv_mul_cancel₀ hpos.ne',
    one_smul]

/-- **`ι_ε` is the identity on `∂ℍ²₊`.** -/
theorem iota_of_mem_bdPlus (hε : ε ^ 2 = 1) {σ : HS.closedDS}
    (h : (σ : HS 2) ∈ HS.piece 2 .bdPlus) : (iota ε hε σ : HS 2) = σ := by
  obtain ⟨h1, h2⟩ := HS.mem_bdPlus_iff.1 h
  refine Subtype.ext ?_
  rw [coe_iota]
  apply mink3_ext
  · exact h1.symm
  · simp [nullDir, h1]
  · simp [nullDir, h1]

/-- **`ι_ε` is the antipodal map on `∂ℍ²₋`.** -/
theorem iota_of_mem_bdMinus (hε : ε ^ 2 = 1) {σ : HS.closedDS}
    (h : (σ : HS 2) ∈ HS.piece 2 .bdMinus) : (iota ε hε σ : HS 2) = -(σ : HS 2) := by
  obtain ⟨h1, h2⟩ := HS.mem_bdMinus_iff.1 h
  refine Subtype.ext ?_
  rw [coe_iota, coe_neg_sphere]
  apply mink3_ext
  · simp [nullDir, h1]
  · simp [nullDir, h1]
  · simp [nullDir, h1]

theorem rp1ToBdPlus_mem_closedDS (w : RP1) : (rp1ToBdPlus w : HS 2) ∈ HS.closedDS :=
  HS.mem_closedDS_iff.2 (Or.inr (Or.inl (rp1ToBdPlus w).2))

theorem rp1ToBdMinus_mem_closedDS (w : RP1) : (rp1ToBdMinus w : HS 2) ∈ HS.closedDS :=
  HS.mem_closedDS_iff.2 (Or.inr (Or.inr (rp1ToBdMinus w).2))

/-- **`ι_ε` is projective on `∂ℍ²₋`** (BBS l.3013–3016's `ῑ : C₋ → C₊` in the model): read
through `ℝP¹ ≅ ∂ℍ²₋` and `ℝP¹ ≅ ∂ℍ²₊`, it is the identity of `ℝP¹`. -/
theorem iota_rp1ToBdMinus (hε : ε ^ 2 = 1) (w : RP1) :
    iota ε hε ⟨rp1ToBdMinus w, rp1ToBdMinus_mem_closedDS w⟩ = rp1ToBdPlus w := by
  refine Subtype.ext ?_
  rw [iota_of_mem_bdMinus hε (rp1ToBdMinus w).2, coe_rp1ToBdMinus, neg_neg]

theorem iota_rp1ToBdPlus (hε : ε ^ 2 = 1) (w : RP1) :
    iota ε hε ⟨rp1ToBdPlus w, rp1ToBdPlus_mem_closedDS w⟩ = rp1ToBdPlus w :=
  Subtype.ext (iota_of_mem_bdPlus hε (rp1ToBdPlus w).2)

end Iota

/-! #### The two foliations: `dS² ∪ ∂ℍ²± ≅ ∂ℍ²₊ × [−1, 1]`, leaves, lightlike lines -/

/-- The point at height `t` of the `ε`-leaf ending at `u = (1, p, q)`:
`(t, t p − ε s q, t q + ε s p)`, `s = √(1 − t²)`, i.e. `t u + s m_ε(u)` (`GX.leafPt_eq`). -/
def leafPt (ε : ℝ) (u : Causal.Minkowski 2) (t : ℝ) : Causal.Minkowski 2 :=
  mink3 t (t * u.2 0 - ε * √(1 - t ^ 2) * u.2 1) (t * u.2 1 + ε * √(1 - t ^ 2) * u.2 0)

/-- The spacelike unit normal `m_ε(u) = (0, −ε q, ε p)` of the lightlike plane of the leaf. -/
def leafNormal (ε : ℝ) (u : Causal.Minkowski 2) : Causal.Minkowski 2 :=
  mink3 0 (-(ε * u.2 1)) (ε * u.2 0)

section Leaves

variable {ε : ℝ}

theorem sq_le_one_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : t ^ 2 ≤ 1 := by
  nlinarith [ht.1, ht.2]

theorem mem_Icc_of_sq_le_one {t : ℝ} (ht : t ^ 2 ≤ 1) : t ∈ Icc (-1 : ℝ) 1 :=
  ⟨by nlinarith [sq_nonneg (t + 1)], by nlinarith [sq_nonneg (t - 1)]⟩

theorem bdPlus_coord {u : HS 2} (hu : u ∈ HS.piece 2 .bdPlus) :
    (u : Causal.Minkowski 2).1 = 1 ∧
      (u : Causal.Minkowski 2).2 0 ^ 2 + (u : Causal.Minkowski 2).2 1 ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := HS.mem_bdPlus_iff.1 hu
  refine ⟨h1, ?_⟩
  rw [← norm_sq_snd_two, h2, one_pow]

/-- **The leaf lies on a lightlike projective line**: `leafPt = t u + s m`, with `u` null, `m`
spacelike unit and `u ⊥ m`, so `u` spans the radical of the plane `⟨u, m⟩`. -/
theorem leafPt_eq {u : Causal.Minkowski 2} (hu1 : u.1 = 1) (t : ℝ) :
    leafPt ε u t = t • u + √(1 - t ^ 2) • leafNormal ε u := by
  apply mink3_ext
  · simp [leafPt, leafNormal, hu1]
  · simp only [leafPt, leafNormal, mink3_snd_zero, Prod.snd_add, Prod.smul_snd, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [leafPt, leafNormal, mink3_snd_one, Prod.snd_add, Prod.smul_snd, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]; ring

theorem minkB_leafNormal {u : Causal.Minkowski 2} : Causal.Flat.minkB u (leafNormal ε u) = 0 := by
  rw [minkB_coords]; simp only [leafNormal, mink3_fst, mink3_snd_zero, mink3_snd_one]; ring

theorem minkQ_leafNormal (hε : ε ^ 2 = 1) {u : Causal.Minkowski 2}
    (hu : u.2 0 ^ 2 + u.2 1 ^ 2 = 1) : Causal.Flat.minkQ (leafNormal ε u) = 1 := by
  rw [minkQ_coords]; simp only [leafNormal, mink3_fst, mink3_snd_zero, mink3_snd_one]
  linear_combination ε ^ 2 * hu + hε

theorem leafPt_sq (hε : ε ^ 2 = 1) {u : Causal.Minkowski 2} (hu : u.2 0 ^ 2 + u.2 1 ^ 2 = 1)
    {t : ℝ} (ht : t ^ 2 ≤ 1) : (leafPt ε u t).2 0 ^ 2 + (leafPt ε u t).2 1 ^ 2 = 1 := by
  have hs : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  simp only [leafPt, mink3_snd_zero, mink3_snd_one]
  linear_combination (t ^ 2 + ε ^ 2 * √(1 - t ^ 2) ^ 2) * hu + hs + √(1 - t ^ 2) ^ 2 * hε

theorem norm_leafPt (hε : ε ^ 2 = 1) {u : Causal.Minkowski 2} (hu : u.2 0 ^ 2 + u.2 1 ^ 2 = 1)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : ‖leafPt ε u t‖ = 1 := by
  have h := norm_sq_snd_two (leafPt ε u t)
  rw [leafPt_sq hε hu (sq_le_one_of_mem_Icc ht)] at h
  have h2 : ‖(leafPt ε u t).2‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  rw [Prod.norm_def, h2, Real.norm_eq_abs]
  exact max_eq_right (abs_le.2 ht)

theorem minkQ_leafPt (hε : ε ^ 2 = 1) {u : Causal.Minkowski 2} (hu : u.2 0 ^ 2 + u.2 1 ^ 2 = 1)
    {t : ℝ} (ht : t ^ 2 ≤ 1) : Causal.Flat.minkQ (leafPt ε u t) = 1 - t ^ 2 := by
  rw [minkQ_coords]
  have := leafPt_sq hε hu ht
  simp only [leafPt, mink3_fst] at this ⊢
  linear_combination this

/-- The point at height `t ∈ [−1, 1]` of the `ε`-leaf ending at `u ∈ ∂ℍ²₊`, a point of
`dS² ∪ ∂ℍ²±`. -/
def leafPtHS (ε : ℝ) (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) (t : Icc (-1 : ℝ) 1) :
    HS.closedDS :=
  ⟨⟨leafPt ε ((u : HS 2) : Causal.Minkowski 2) t,
      mem_sphere_zero_iff_norm.2 (norm_leafPt hε (bdPlus_coord u.2).2 t.2)⟩, by
    show 0 ≤ Causal.Flat.minkQ (leafPt ε ((u : HS 2) : Causal.Minkowski 2) t)
    rw [minkQ_leafPt hε (bdPlus_coord u.2).2 (sq_le_one_of_mem_Icc t.2)]
    linarith [sq_le_one_of_mem_Icc t.2]⟩

theorem coe_leafPtHS (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) (t : Icc (-1 : ℝ) 1) :
    (((leafPtHS ε hε u t : HS.closedDS) : HS 2) : Causal.Minkowski 2) =
      leafPt ε ((u : HS 2) : Causal.Minkowski 2) t := rfl

theorem nullDir_leafPt (hε : ε ^ 2 = 1) (u : Causal.Minkowski 2) {t : ℝ} (ht : t ^ 2 ≤ 1) :
    nullDir ε (leafPt ε u t) = mink3 1 (u.2 0) (u.2 1) := by
  have hs : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  apply mink3_ext
  · rfl
  · simp only [nullDir, leafPt, mink3_fst, mink3_snd_zero, mink3_snd_one]
    linear_combination u.2 0 * hs + u.2 0 * √(1 - t ^ 2) ^ 2 * hε
  · simp only [nullDir, leafPt, mink3_fst, mink3_snd_zero, mink3_snd_one]
    linear_combination u.2 1 * hs + u.2 1 * √(1 - t ^ 2) ^ 2 * hε

theorem leafPt_nullDir (hε : ε ^ 2 = 1) {v : Causal.Minkowski 2} (ht : v.1 ^ 2 ≤ 1) :
    leafPt ε (nullDir ε v) v.1 = v := by
  have hs : √(1 - v.1 ^ 2) ^ 2 = 1 - v.1 ^ 2 := Real.sq_sqrt (by linarith)
  apply mink3_ext
  · rfl
  · simp only [nullDir, leafPt, mink3_snd_zero, mink3_snd_one]
    linear_combination v.2 0 * hs + v.2 0 * √(1 - v.1 ^ 2) ^ 2 * hε
  · simp only [nullDir, leafPt, mink3_snd_zero, mink3_snd_one]
    linear_combination v.2 1 * hs + v.2 1 * √(1 - v.1 ^ 2) ^ 2 * hε

theorem continuous_leafPt (ε : ℝ) :
    Continuous fun p : Causal.Minkowski 2 × ℝ => leafPt ε p.1 p.2 := by
  unfold leafPt
  have h0 : Continuous fun p : Causal.Minkowski 2 × ℝ => p.1.2 0 :=
    (PiLp.continuous_apply 2 _ 0).comp (continuous_snd.comp continuous_fst)
  have h1 : Continuous fun p : Causal.Minkowski 2 × ℝ => p.1.2 1 :=
    (PiLp.continuous_apply 2 _ 1).comp (continuous_snd.comp continuous_fst)
  have hs : Continuous fun p : Causal.Minkowski 2 × ℝ => √(1 - p.2 ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_snd.pow 2))
  exact continuous_mink3 continuous_snd (by fun_prop) (by fun_prop)

/-- **`ι_ε` is a trivial bundle** (BBS l.2983–2990, in `HS²`): `σ ↦ (ι_ε σ, t(σ))` is a
homeomorphism `dS² ∪ ∂ℍ²± ≃ₜ ∂ℍ²₊ × [−1, 1]`, so `ι_ε` is the projection of `∂ℍ²₊ × [−1, 1]`:
its fibres, the closed leaves, are arcs `t ↦ leafPtHS u t` from `−u ∈ ∂ℍ²₋` (`t = −1`) to
`u ∈ ∂ℍ²₊` (`t = 1`) through `dS²` (`|t| < 1`). -/
def iotaChart (ε : ℝ) (hε : ε ^ 2 = 1) : HS.closedDS ≃ₜ HS.piece 2 .bdPlus × Icc (-1 : ℝ) 1 where
  toFun σ := (iota ε hε σ,
    ⟨((σ : HS 2) : Causal.Minkowski 2).1, mem_Icc_of_sq_le_one (HS.closedDS_coord σ.2).2⟩)
  invFun ut := leafPtHS ε hε ut.1 ut.2
  left_inv σ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_leafPtHS, coe_iota]
    exact leafPt_nullDir hε (HS.closedDS_coord σ.2).2
  right_inv ut := by
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext rfl)
    rw [coe_iota, coe_leafPtHS, nullDir_leafPt hε _ (sq_le_one_of_mem_Icc ut.2.2)]
    exact mink3_ext (bdPlus_coord ut.1.2).1.symm rfl rfl
  continuous_toFun := (continuous_iota hε).prodMk ((continuous_fst.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (continuous_leafPt ε).comp ((continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_fst)).prodMk (continuous_subtype_val.comp continuous_snd))

theorem iotaChart_apply_fst (hε : ε ^ 2 = 1) (σ : HS.closedDS) :
    (iotaChart ε hε σ).1 = iota ε hε σ := rfl

theorem iota_leafPtHS (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) (t : Icc (-1 : ℝ) 1) :
    iota ε hε (leafPtHS ε hε u t) = u :=
  congrArg Prod.fst ((iotaChart ε hε).apply_symm_apply (u, t))

/-- The closed leaf ends at `u` (`t = 1`). -/
theorem leafPtHS_one (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    ((leafPtHS ε hε u ⟨1, by norm_num, le_rfl⟩ : HS.closedDS) : HS 2) = u := by
  refine Subtype.ext ?_
  rw [coe_leafPtHS]
  apply mink3_ext
  · exact (bdPlus_coord u.2).1.symm
  · simp [leafPt]
  · simp [leafPt]

/-- The closed leaf starts at `−u ∈ ∂ℍ²₋` (`t = −1`). -/
theorem leafPtHS_neg_one (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    ((leafPtHS ε hε u ⟨-1, le_rfl, by norm_num⟩ : HS.closedDS) : HS 2) = -(u : HS 2) := by
  refine Subtype.ext ?_
  rw [coe_leafPtHS, coe_neg_sphere]
  apply mink3_ext
  · simp [leafPt, (bdPlus_coord u.2).1]
  · simp [leafPt]
  · simp [leafPt]

theorem leafPtHS_mem_deSitter (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) {t : Icc (-1 : ℝ) 1}
    (ht : (t : ℝ) ∈ Ioo (-1 : ℝ) 1) :
    ((leafPtHS ε hε u t : HS.closedDS) : HS 2) ∈ HS.piece 2 .deSitter := by
  show 0 < Causal.Flat.minkQ (leafPt ε ((u : HS 2) : Causal.Minkowski 2) t)
  rw [minkQ_leafPt hε (bdPlus_coord u.2).2 (sq_le_one_of_mem_Icc t.2)]
  nlinarith [ht.1, ht.2]

/-- **The leaf of the `ε`-foliation of `dS²` ending at `u ∈ ∂ℍ²₊`** (BBS l.1907–1909,
l.2026–2027: the foliations by light-like lines): the rays of `dS²` whose `ι_ε` is `u`. -/
def leafOver (ε : ℝ) (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) : Set (HS 2) :=
  {τ | ∃ h : τ ∈ HS.closedDS, τ ∈ HS.piece 2 .deSitter ∧ iota ε hε ⟨τ, h⟩ = u}

/-- **The leaves are the open arcs `|t| < 1`** of the closed leaves: each runs from `−u ∈ ∂ℍ²₋`
to `u ∈ ∂ℍ²₊` (`GX.leafPtHS_neg_one`, `GX.leafPtHS_one`), inside a lightlike projective line
(`GX.leafPt_eq`). -/
theorem leafOver_eq (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    leafOver ε hε u = (fun t => ((leafPtHS ε hε u t : HS.closedDS) : HS 2)) ''
      {t | (t : ℝ) ∈ Ioo (-1 : ℝ) 1} := by
  ext τ
  constructor
  · rintro ⟨h, hτ, hι⟩
    refine ⟨⟨((τ : Causal.Minkowski 2)).1, mem_Icc_of_sq_le_one (HS.closedDS_coord h).2⟩,
      abs_lt.1 (HS.mem_deSitter_iff.1 hτ).1, ?_⟩
    have := (iotaChart ε hε).symm_apply_apply ⟨τ, h⟩
    rw [← hι]
    exact congrArg Subtype.val this
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(leafPtHS ε hε u t).2, leafPtHS_mem_deSitter hε u ht, iota_leafPtHS hε u t⟩

/-- **The leaves partition `dS²`**: every ray of `dS²` lies on exactly one `ε`-leaf, the one over
`ι_ε σ`. -/
theorem mem_leafOver_iff (hε : ε ^ 2 = 1) {σ : HS.closedDS}
    (hσ : (σ : HS 2) ∈ HS.piece 2 .deSitter) (u : HS.piece 2 .bdPlus) :
    (σ : HS 2) ∈ leafOver ε hε u ↔ iota ε hε σ = u :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨σ.2, hσ, h⟩⟩

/-- **The two lightlike lines through a point of `dS²`**: a future null `n ≠ 0` orthogonal to
`σ ∈ dS² ∪ ∂ℍ²±` is a positive multiple of `n_L(σ)` or of `n_R(σ)`. -/
theorem null_orth_cases {σ : HS.closedDS} {n : Causal.Minkowski 2}
    (hn : Causal.Flat.IsFutureCausal n) (hnq : Causal.Flat.minkQ n = 0) (hn0 : n ≠ 0)
    (horth : Causal.Flat.minkB ((σ : HS 2) : Causal.Minkowski 2) n = 0) :
    n = n.1 • nullDir 1 ((σ : HS 2) : Causal.Minkowski 2) ∨
      n = n.1 • nullDir (-1) ((σ : HS 2) : Causal.Minkowski 2) := by
  obtain ⟨hx, ht⟩ := HS.closedDS_coord σ.2
  rcases le_total 0 (vol3 ((σ : HS 2) : Causal.Minkowski 2) (mink3 1 0 0) n) with h | h
  · exact Or.inl (eq_smul_nullDir (one_pow 2) hx ht hn hnq hn0 horth (by rw [one_mul]; exact h))
  · exact Or.inr (eq_smul_nullDir neg_one_sq hx ht hn hnq hn0 horth (by linarith))

/-- **The two lightlike lines through a point of `dS²` are distinct**: `ι_L σ ≠ ι_R σ`. -/
theorem iotaL_ne_iotaR {σ : HS.closedDS} (hσ : (σ : HS 2) ∈ HS.piece 2 .deSitter) :
    iotaL σ ≠ iotaR σ := by
  intro h
  obtain ⟨hx, ht⟩ := HS.closedDS_coord σ.2
  have ht1 := (HS.mem_deSitter_iff.1 hσ).1
  have hs : 0 < √(1 - ((σ : HS 2) : Causal.Minkowski 2).1 ^ 2) := by
    apply Real.sqrt_pos.2
    have := abs_lt.1 ht1
    nlinarith [this.1, this.2]
  have h' := congrArg (fun τ : HS.piece 2 .bdPlus => ((τ : HS 2) : Causal.Minkowski 2)) h
  simp only [iotaL, iotaR, coe_iota] at h'
  have e0 := congrArg (fun v : Causal.Minkowski 2 => v.2 0) h'
  have e1 := congrArg (fun v : Causal.Minkowski 2 => v.2 1) h'
  simp only [nullDir, mink3_snd_zero, mink3_snd_one] at e0 e1
  have hy : ((σ : HS 2) : Causal.Minkowski 2).2 1 = 0 := by
    have : 2 * √(1 - ((σ : HS 2) : Causal.Minkowski 2).1 ^ 2) *
        ((σ : HS 2) : Causal.Minkowski 2).2 1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · nlinarith
    · exact h
  have hx0 : ((σ : HS 2) : Causal.Minkowski 2).2 0 = 0 := by
    have : 2 * √(1 - ((σ : HS 2) : Causal.Minkowski 2).1 ^ 2) *
        ((σ : HS 2) : Causal.Minkowski 2).2 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · nlinarith
    · exact h
  rw [hy, hx0] at hx
  norm_num at hx

/-- **The closed `ε`-leaf over `u`**, as a curve `ℝ → HS²` (constant outside `[−1, 1]`). -/
def leafCurve (ε : ℝ) (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) (t : ℝ) : HS 2 :=
  (leafPtHS ε hε u (projIcc (-1) 1 (by norm_num) t) : HS 2)

theorem continuous_leafCurve (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    Continuous (leafCurve ε hε u) :=
  continuous_subtype_val.comp ((iotaChart ε hε).symm.continuous.comp
    (continuous_const.prodMk (continuous_projIcc (a := (-1 : ℝ)) (b := 1) (h := by norm_num))))

theorem leafCurve_of_mem (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : leafCurve ε hε u t = (leafPtHS ε hε u ⟨t, ht⟩ : HS 2) := by
  rw [leafCurve, projIcc_of_mem _ ht]

theorem leafOver_eq_image (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    leafOver ε hε u = leafCurve ε hε u '' Ioo (-1 : ℝ) 1 := by
  rw [leafOver_eq]
  ext τ
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, leafCurve_of_mem hε u t.2⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, Ioo_subset_Icc_self ht⟩, ht, (leafCurve_of_mem hε u _).symm⟩

/-- **Each leaf runs from `∂ℍ²₋` to `∂ℍ²₊`** (BBS l.2983–2984, in `HS²`): the closure of the
`ε`-leaf over `u ∈ ∂ℍ²₊` adds exactly its `α`-limit `−u ∈ ∂ℍ²₋` and its `ω`-limit `u`. -/
theorem closure_leafOver (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    closure (leafOver ε hε u) = leafOver ε hε u ∪ {(u : HS 2), -(u : HS 2)} := by
  have hc := continuous_leafCurve hε u
  have h1 : leafCurve ε hε u 1 = u := by
    rw [leafCurve_of_mem hε u ⟨by norm_num, le_rfl⟩]; exact leafPtHS_one hε u
  have hm1 : leafCurve ε hε u (-1) = -(u : HS 2) := by
    rw [leafCurve_of_mem hε u ⟨le_rfl, by norm_num⟩]; exact leafPtHS_neg_one hε u
  have hcl : closure (Ioo (-1 : ℝ) 1) = Icc (-1) 1 := closure_Ioo (by norm_num)
  rw [leafOver_eq_image]
  apply subset_antisymm
  · refine closure_minimal ?_ (((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image hc).isClosed)
      |>.trans ?_
    · exact image_mono Ioo_subset_Icc_self
    · rintro _ ⟨t, ht, rfl⟩
      rcases eq_or_lt_of_le ht.1 with h | h
      · right; rw [← h, hm1]; exact Or.inr rfl
      · rcases eq_or_lt_of_le ht.2 with h' | h'
        · right; rw [h', h1]; exact Or.inl rfl
        · exact Or.inl ⟨t, ⟨h, h'⟩, rfl⟩
  · refine union_subset subset_closure ?_
    rintro _ (rfl | rfl)
    · rw [← h1]
      exact map_mem_closure hc (by rw [hcl]; exact ⟨by norm_num, le_rfl⟩) (mapsTo_image _ _)
    · rw [← hm1]
      exact map_mem_closure hc (by rw [hcl]; exact ⟨le_rfl, by norm_num⟩) (mapsTo_image _ _)

theorem leafOver_subset_deSitter (hε : ε ^ 2 = 1) (u : HS.piece 2 .bdPlus) :
    leafOver ε hε u ⊆ HS.piece 2 .deSitter := fun _ ⟨_, h, _⟩ => h

/-- **Every point of `∂ℍ²₊` is the `ω`-limit of exactly one leaf of each foliation**
(BBS l.2984–2985). -/
theorem existsUnique_omega (hε : ε ^ 2 = 1) {v : HS 2} (hv : v ∈ HS.piece 2 .bdPlus) :
    ∃! u : HS.piece 2 .bdPlus, v ∈ closure (leafOver ε hε u) := by
  refine ⟨⟨v, hv⟩, ?_, fun u hu => ?_⟩
  · show v ∈ closure (leafOver ε hε ⟨v, hv⟩)
    rw [closure_leafOver]; exact Or.inr (Or.inl rfl)
  have hu : v ∈ closure (leafOver ε hε u) := hu
  rw [closure_leafOver] at hu
  rcases hu with hu | hu | hu
  · exact absurd (leafOver_subset_deSitter hε u hu) fun h =>
      HS.pairwise_disjoint_piece (by decide : HSPiece.deSitter ≠ .bdPlus)
        |>.ne_of_mem h hv rfl
  · exact Subtype.ext hu.symm
  · exfalso
    have : -(u : HS 2) ∈ HS.piece 2 .bdMinus := HS.neg_mem_bdMinus_iff.2 u.2
    rw [← hu] at this
    exact HS.pairwise_disjoint_piece (by decide : HSPiece.bdPlus ≠ .bdMinus) |>.ne_of_mem hv this rfl

/-- **Every point of `∂ℍ²₋` is the `α`-limit of exactly one leaf of each foliation**
(BBS l.2984–2985). -/
theorem existsUnique_alpha (hε : ε ^ 2 = 1) {v : HS 2} (hv : v ∈ HS.piece 2 .bdMinus) :
    ∃! u : HS.piece 2 .bdPlus, v ∈ closure (leafOver ε hε u) := by
  have hv' : -v ∈ HS.piece 2 .bdPlus := HS.neg_mem_bdMinus_iff.1 (by rw [neg_neg]; exact hv)
  refine ⟨⟨-v, hv'⟩, ?_, fun u hu => ?_⟩
  · show v ∈ closure (leafOver ε hε ⟨-v, hv'⟩)
    rw [closure_leafOver]; exact Or.inr (Or.inr (neg_neg v).symm)
  have hu : v ∈ closure (leafOver ε hε u) := hu
  rw [closure_leafOver] at hu
  rcases hu with hu | hu | hu
  · exact absurd (leafOver_subset_deSitter hε u hu) fun h =>
      HS.pairwise_disjoint_piece (by decide : HSPiece.deSitter ≠ .bdMinus)
        |>.ne_of_mem h hv rfl
  · exfalso
    rw [hu] at hv
    exact HS.pairwise_disjoint_piece (by decide : HSPiece.bdPlus ≠ .bdMinus)
      |>.ne_of_mem u.2 hv rfl
  · refine Subtype.ext ?_
    show (u : HS 2) = -v
    have hu' : v = -(u : HS 2) := hu
    rw [hu', neg_neg]

/-- **The antipodal map exchanges the two foliations**: `ι_R (−σ) = ι_L σ`. -/
theorem nullDir_neg (ε : ℝ) (v : Causal.Minkowski 2) : nullDir (-ε) (-v) = nullDir ε v := by
  apply mink3_ext
  · rfl
  · simp only [nullDir, mink3_snd_zero, Prod.fst_neg, Prod.snd_neg, PiLp.neg_apply, neg_sq]; ring
  · simp only [nullDir, mink3_snd_one, Prod.fst_neg, Prod.snd_neg, PiLp.neg_apply, neg_sq]; ring

end Leaves

/-! ### Restricting a chart to matching subsets -/

section RestrictMatch

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Classical in
/-- **The restriction of a partial homeomorphism to subsets it matches**: if `x ∈ s ↔ e x ∈ t` on
`e.source`, then `e` restricts to a partial homeomorphism `s → t` (the points `x₀`, `y₀` are junk
values off the source and target). -/
def restrictMatch (e : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) (x₀ : s) (y₀ : t) : OpenPartialHomeomorph s t where
  toFun x := if hx : (x : X) ∈ e.source then ⟨e x, (h x hx).1 x.2⟩ else y₀
  invFun y := if hy : (y : Y) ∈ e.target then
    ⟨e.symm y, (h _ (e.map_target hy)).2 (by rw [e.right_inv hy]; exact y.2)⟩ else x₀
  source := Subtype.val ⁻¹' e.source
  target := Subtype.val ⁻¹' e.target
  map_source' x hx := by
    have hx' : (x : X) ∈ e.source := hx
    simp only [mem_preimage, dif_pos hx']
    exact e.map_source hx'
  map_target' y hy := by
    have hy' : (y : Y) ∈ e.target := hy
    simp only [mem_preimage, dif_pos hy']
    exact e.map_target hy'
  left_inv' x hx := by
    have hx' : (x : X) ∈ e.source := hx
    apply Subtype.ext
    simp only [dif_pos hx', dif_pos (e.map_source hx')]
    exact e.left_inv hx'
  right_inv' y hy := by
    have hy' : (y : Y) ∈ e.target := hy
    apply Subtype.ext
    simp only [dif_pos hy', dif_pos (e.map_target hy')]
    exact e.right_inv hy'
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun x : s => e x)
      (e.continuousOn.comp continuous_subtype_val.continuousOn fun x hx => hx) fun x hx => ?_
    have hx' : (x : X) ∈ e.source := hx
    simp only [Function.comp_apply, dif_pos hx']
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun y : t => e.symm y)
      (e.symm.continuousOn.comp continuous_subtype_val.continuousOn fun y hy => hy) fun y hy => ?_
    have hy' : (y : Y) ∈ e.target := hy
    simp only [Function.comp_apply, dif_pos hy']

theorem restrictMatch_source (e : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) (x₀ : s) (y₀ : t) :
    (restrictMatch e s t h x₀ y₀).source = Subtype.val ⁻¹' e.source := rfl

open Classical in
theorem coe_restrictMatch_apply (e : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) (x₀ : s) (y₀ : t) {x : s} (hx : (x : X) ∈ e.source) :
    ((restrictMatch e s t h x₀ y₀ x : t) : Y) = e x := by
  show (((restrictMatch e s t h x₀ y₀).toFun x : t) : Y) = e x
  simp only [restrictMatch, dif_pos hx]

end RestrictMatch

/-! ### Photons of an HS-surface and the `ℝP¹`-structure of a circle of photons -/

section Photons

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (HS 2) M]
  [HasGroupoid M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2))]

/-- The piece of `HS²` that a point of an HS-surface corresponds to, read in its preferred chart
(chart-independent: `GX.region_eq_hsRegion`). -/
def hsRegion (x : M) : HSPiece := HS.region (chartAt (HS 2) x x)

/-- **The piece of a point does not depend on the chart**: chart changes are locally elements of
`SO₀(1,2)`, which preserve the five pieces. -/
theorem region_eq_hsRegion {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    {x : M} (hx : x ∈ e.source) : HS.region (e x) = hsRegion x := by
  obtain ⟨A, hA⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas x) he
    (mem_chart_source (HS 2) x) hx
  rw [hA.self_of_nhds, HS.region_smul]
  rfl

/-- **A photon** (BBS l.1866–1867): « a point corresponding in every HS-chart to points in
`∂ℍ²±` ». -/
def IsPhoton (x : M) : Prop :=
  ∀ e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)),
    x ∈ e.source → e x ∈ HS.piece 2 .bdPlus ∪ HS.piece 2 .bdMinus

theorem isPhoton_iff {x : M} : IsPhoton x ↔ hsRegion x = .bdPlus ∨ hsRegion x = .bdMinus := by
  constructor
  · intro h
    rcases h _ ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas x)
      (mem_chart_source (HS 2) x) with h | h
    · exact Or.inl (HS.region_eq_of_mem h)
    · exact Or.inr (HS.region_eq_of_mem h)
  · intro h e he hx
    rw [← region_eq_hsRegion he hx] at h
    rcases h with h | h
    · exact Or.inl (HS.mem_piece_iff_region.2 h)
    · exact Or.inr (HS.mem_piece_iff_region.2 h)

/-- `true ↦ ∂ℍ²₊` (future photons), `false ↦ ∂ℍ²₋` (past photons). -/
def bdPiece : Bool → HSPiece
  | true => .bdPlus
  | false => .bdMinus

/-- `ℝP¹ ≅ ∂ℍ²₊` or `ℝP¹ ≅ ∂ℍ²₋`. -/
def rp1ToBd : (b : Bool) → RP1 ≃ₜ HS.piece 2 (bdPiece b)
  | true => rp1ToBdPlus
  | false => rp1ToBdMinus

theorem smul_rp1ToBd (b : Bool) (A : Causal.Flat.lorentz 2) (w : RP1) :
    A • (rp1ToBd b w : HS 2) = rp1ToBd b (pslEquivLorentz.symm A • w) := by
  cases b
  · exact smul_rp1ToBdMinus A w
  · exact smul_rp1ToBdPlus A w

section Chart

variable (b : Bool) (C : Set M) (hC : ∀ x ∈ C, hsRegion x = bdPiece b)
  (hCo : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, hsRegion y = bdPiece b → y ∈ C)

/-- An open set `W` with `C = W ∩ {hsRegion = bdPiece b}`. -/
def photonNbhd : Set M := interior {y | hsRegion y = bdPiece b → y ∈ C}

theorem isOpen_photonNbhd : IsOpen (photonNbhd b C) := isOpen_interior

include hCo in
theorem subset_photonNbhd : C ⊆ photonNbhd b C := fun x hx =>
  mem_interior_iff_mem_nhds.2 (hCo x hx)

include hC in
theorem photon_match {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2))) :
    ∀ y ∈ (e.restrOpen (photonNbhd b C) (isOpen_photonNbhd b C)).source,
      y ∈ C ↔ (e.restrOpen (photonNbhd b C) (isOpen_photonNbhd b C)) y ∈
        HS.piece 2 (bdPiece b) := by
  intro y hy
  rw [OpenPartialHomeomorph.restrOpen_source] at hy
  rw [OpenPartialHomeomorph.coe_restrOpen, HS.mem_piece_iff_region, region_eq_hsRegion he hy.1]
  exact ⟨hC y, fun h => interior_subset hy.2 h⟩

/-- **The `ℝP¹`-chart of `C` given by an HS-chart `e`** (BBS l.1903–1905): `e`, restricted to `C`
and read through `∂ℍ²± ≅ ℝP¹`. -/
def photonChartOf {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (x₀ : C) : OpenPartialHomeomorph C RP1 :=
  (restrictMatch (e.restrOpen (photonNbhd b C) (isOpen_photonNbhd b C)) C (HS.piece 2 (bdPiece b))
    (photon_match b C hC he) x₀ (rp1ToBd b 1)).trans (rp1ToBd b).symm.toOpenPartialHomeomorph

include hCo in
theorem photonChartOf_source {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (x₀ : C) : (photonChartOf b C hC he x₀).source = {y : C | (y : M) ∈ e.source} := by
  ext y
  simp only [photonChartOf, OpenPartialHomeomorph.trans_source, restrictMatch_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, mem_preimage,
    OpenPartialHomeomorph.restrOpen_source, mem_inter_iff, mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, subset_photonNbhd b C hCo y.2⟩⟩

include hCo in
theorem rp1ToBd_photonChartOf {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (x₀ : C) {y : C} (hy : (y : M) ∈ e.source) :
    ((rp1ToBd b (photonChartOf b C hC he x₀ y) : HS 2)) = e y := by
  simp only [photonChartOf, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply]
  rw [coe_restrictMatch_apply _ _ _ _ _ _ (by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact ⟨hy, subset_photonNbhd b C hCo y.2⟩),
    OpenPartialHomeomorph.coe_restrOpen]

include hCo in
/-- **The chart changes are projective** (BBS l.1904: « hyperbolic isometries are restrictions of
real projective transformations »): two such charts differ, near every point, by the element of
`PSL(2,ℝ)` corresponding (`GX.pslEquivLorentz`) to the HS-chart change. -/
theorem photonChartOf_compatible {e e' : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (he' : e' ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (x₀ x₀' : C) :
    (photonChartOf b C hC he x₀).symm.trans (photonChartOf b C hC he' x₀') ∈
      gxGroupoid PSL(2, ℝ) RP1 := by
  refine symm_trans_mem_gxGroupoid fun y hy => ?_
  rw [photonChartOf_source b C hC hCo, photonChartOf_source b C hC hCo] at hy
  obtain ⟨A, hA⟩ := eventually_smul_eq_of_mem_maximalAtlas he he' hy.1 hy.2
  refine ⟨pslEquivLorentz.symm A, ?_⟩
  have hev := (continuous_subtype_val.continuousAt (x := y)).eventually hA
  have ho : IsOpen {z : C | (z : M) ∈ e.source ∩ e'.source} :=
    (e.open_source.inter e'.open_source).preimage continuous_subtype_val
  filter_upwards [hev, ho.mem_nhds hy] with z hz hz'
  apply (rp1ToBd b).injective
  apply Subtype.ext
  rw [rp1ToBd_photonChartOf b C hC hCo he' x₀' hz'.2, ← smul_rp1ToBd,
    rp1ToBd_photonChartOf b C hC hCo he x₀ hz'.1]
  exact hz

include hCo in
/-- **The `ℝP¹`-structure of a set of photons of type `b`, open among them** (BBS l.1903–1905, the
structure « from the hyperbolic side »): the charts of `C` are the HS-charts of `M` composed with
`∂ℍ²± ≅ ℝP¹`. -/
@[reducible] def photonChartedSpace : ChartedSpace RP1 C where
  atlas := range fun x : C => photonChartOf b C hC
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas (x : M)) x
  chartAt x := photonChartOf b C hC
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas (x : M)) x
  mem_chart_source x := by
    rw [photonChartOf_source b C hC hCo]
    exact mem_chart_source (HS 2) (x : M)
  chart_mem_atlas x := ⟨x, rfl⟩

/-- **The structure is a `(PSL(2,ℝ), ℝP¹)`-structure.** -/
theorem photon_hasGroupoid :
    @HasGroupoid RP1 _ C _ (photonChartedSpace b C hC hCo) (gxGroupoid PSL(2, ℝ) RP1) := by
  refine @HasGroupoid.mk RP1 _ C _ (photonChartedSpace b C hC hCo) _ ?_
  rintro _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
  exact photonChartOf_compatible b C hC hCo _ _ x x'

/-- **The structure does not depend on the atlas of `M`**: the chart given by any HS-chart of the
maximal atlas lies in the maximal atlas of `C`. -/
theorem photonChartOf_mem_maximalAtlas {e : OpenPartialHomeomorph M (HS 2)}
    (he : e ∈ StructureGroupoid.maximalAtlas M (gxGroupoid (Causal.Flat.lorentz 2) (HS 2)))
    (x₀ : C) :
    photonChartOf b C hC he x₀ ∈ @StructureGroupoid.maximalAtlas RP1 C _ _
      (photonChartedSpace b C hC hCo) (gxGroupoid PSL(2, ℝ) RP1) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨photonChartOf_compatible b C hC hCo he _ x₀ x,
    photonChartOf_compatible b C hC hCo _ he x x₀⟩

end Chart

/-- **A regular circle of photons** (BBS l.1868–1871, l.1894): a set of photons, open in the set
`𝒫` of photons, homeomorphic to the circle (a circle component of `𝒫`; reading, SCOPE). -/
structure IsPhotonCircle (C : Set M) : Prop where
  isPhoton : ∀ x ∈ C, IsPhoton x
  relOpen : ∀ x ∈ C, ∀ᶠ y in 𝓝 x, IsPhoton y → y ∈ C
  isCircle : IsCircle C

/-- Near a future photon, every photon is a future photon. -/
theorem eventually_hsRegion_bdPlus {x : M} (hx : hsRegion x = .bdPlus) :
    ∀ᶠ y in 𝓝 x, IsPhoton y → hsRegion y = .bdPlus := by
  have hc : ContinuousAt (chartAt (HS 2) x) x :=
    (chartAt (HS 2) x).continuousAt (mem_chart_source (HS 2) x)
  have hopen : IsOpen {σ : HS 2 | 0 < (σ : Causal.Minkowski 2).1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_subtype_val)
  have hmem : chartAt (HS 2) x x ∈ {σ : HS 2 | 0 < (σ : Causal.Minkowski 2).1} :=
    (HS.mem_piece_iff_region.2 hx).2
  filter_upwards [hc.preimage_mem_nhds (hopen.mem_nhds hmem),
    (chartAt (HS 2) x).open_source.mem_nhds (mem_chart_source (HS 2) x)] with y hy hys hph
  have hreg := region_eq_hsRegion
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas x) hys
  rcases isPhoton_iff.1 hph with h | h
  · exact h
  · exfalso
    rw [← hreg] at h
    have := (HS.mem_piece_iff_region.2 h).2
    exact absurd hy (not_lt.2 this.le)

/-- Near a past photon, every photon is a past photon. -/
theorem eventually_hsRegion_bdMinus {x : M} (hx : hsRegion x = .bdMinus) :
    ∀ᶠ y in 𝓝 x, IsPhoton y → hsRegion y = .bdMinus := by
  have hc : ContinuousAt (chartAt (HS 2) x) x :=
    (chartAt (HS 2) x).continuousAt (mem_chart_source (HS 2) x)
  have hopen : IsOpen {σ : HS 2 | (σ : Causal.Minkowski 2).1 < 0} :=
    isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const
  have hmem : chartAt (HS 2) x x ∈ {σ : HS 2 | (σ : Causal.Minkowski 2).1 < 0} :=
    (HS.mem_piece_iff_region.2 hx).2
  filter_upwards [hc.preimage_mem_nhds (hopen.mem_nhds hmem),
    (chartAt (HS 2) x).open_source.mem_nhds (mem_chart_source (HS 2) x)] with y hy hys hph
  have hreg := region_eq_hsRegion
    ((gxGroupoid (Causal.Flat.lorentz 2) (HS 2)).chart_mem_maximalAtlas x) hys
  rcases isPhoton_iff.1 hph with h | h
  · exfalso
    rw [← hreg] at h
    have := (HS.mem_piece_iff_region.2 h).2
    exact absurd hy (not_lt.2 this.le)
  · exact h

/-- **A circle of photons is made of future photons only, or of past photons only.** -/
theorem IsPhotonCircle.exists_bdPiece {C : Set M} (hC : IsPhotonCircle C) :
    ∃ b : Bool, (∀ x ∈ C, hsRegion x = bdPiece b) ∧
      ∀ x ∈ C, ∀ᶠ y in 𝓝 x, hsRegion y = bdPiece b → y ∈ C := by
  obtain ⟨φ⟩ := hC.isCircle
  haveI : ConnectedSpace C := φ.symm.surjective.connectedSpace φ.symm.continuous
  obtain ⟨x₀⟩ : Nonempty C := ⟨φ.symm 1⟩
  -- the type of photon is locally constant on `C`
  have hlc : IsLocallyConstant fun x : C => decide (hsRegion (x : M) = .bdPlus) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hph := isPhoton_iff.1 (hC.isPhoton x x.2)
    have hev : ∀ᶠ y in 𝓝 (x : M), y ∈ C → hsRegion y = hsRegion (x : M) := by
      rcases hph with h | h
      · filter_upwards [eventually_hsRegion_bdPlus h] with y hy hyC
        rw [hy (hC.isPhoton y hyC), h]
      · filter_upwards [eventually_hsRegion_bdMinus h] with y hy hyC
        rw [hy (hC.isPhoton y hyC), h]
    filter_upwards [(continuous_subtype_val.continuousAt (x := x)).eventually hev] with y hy
    rw [hy y.2]
  refine ⟨decide (hsRegion (x₀ : M) = .bdPlus), fun x hx => ?_, fun x hx => ?_⟩
  · have := hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ x₀
    simp only at this
    rcases isPhoton_iff.1 (hC.isPhoton x hx) with h | h
    · rw [← this, h]; rfl
    · rw [← this, h]; rfl
  · filter_upwards [hC.relOpen x hx] with y hy hyb
    refine hy (isPhoton_iff.2 ?_)
    cases hb : decide (hsRegion (x₀ : M) = .bdPlus) <;> rw [hb] at hyb
    · exact Or.inr hyb
    · exact Or.inl hyb

/-- **The `ℝP¹`-structure on a circle of photons from the hyperbolic side** (BBS l.1903–1905). -/
@[reducible] noncomputable def IsPhotonCircle.rp1ChartedSpace {C : Set M} (hC : IsPhotonCircle C) :
    ChartedSpace RP1 C :=
  photonChartedSpace hC.exists_bdPiece.choose C hC.exists_bdPiece.choose_spec.1
    hC.exists_bdPiece.choose_spec.2

theorem IsPhotonCircle.rp1_hasGroupoid {C : Set M} (hC : IsPhotonCircle C) :
    @HasGroupoid RP1 _ C _ hC.rp1ChartedSpace (gxGroupoid PSL(2, ℝ) RP1) :=
  photon_hasGroupoid _ C _ _

/-- **A circle of photons has a lifted holonomy in `G̃`** (the holonomy of the `ℝP¹`-structure on
`C` from the hyperbolic side, which Lemma F of NOTES-3+1 N9 uses), unique up to conjugacy
(`GX.HasLiftedHolonomy.conj`). -/
theorem IsPhotonCircle.exists_hasLiftedHolonomy {C : Set M} (hC : IsPhotonCircle C) :
    ∃ f : GTilde, @HasLiftedHolonomy C _ hC.rp1ChartedSpace f := by
  letI := hC.rp1ChartedSpace
  haveI := hC.rp1_hasGroupoid
  exact GX.exists_hasLiftedHolonomy hC.isCircle

/-- **A circle of photons has a real angle** (`GX.HasRealAngle.unique`: it is unique). -/
theorem IsPhotonCircle.exists_hasRealAngle {C : Set M} (hC : IsPhotonCircle C) :
    ∃ θ : ℝ, @HasRealAngle C _ hC.rp1ChartedSpace θ := by
  letI := hC.rp1ChartedSpace
  haveI := hC.rp1_hasGroupoid
  exact GX.exists_hasRealAngle hC.isCircle

end Photons

end GX
