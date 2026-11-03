import GX.Suspension.Celestial

/-!
# Links in locally affine spaces: the ray sphere `S(V)` and the conic structure at `0`

Package BBS-Affine (layer L1 of `papers/bbs/REVIEW.md` §B). **No ledger label is marked.** This
layer has no single source statement: it instantiates the corrected conic structure
(`GX.Suspension.Conic`) and suspension céleste (`GX.Suspension.Celestial`) of
L0 — NEW THEORY built under the author's ruling from draft material commented out in
`these.tex` (l.3560–3677; here l.3569 and l.3631), not part of the thesis — at a point of a
real vector space `V`, for `(G,X) = (V ≃ᵃ[ℝ] V, V)` (the affine group,
`GX.affineEquivMulAction`, rigid by `GX.isRigidAction_affineEquiv`, `Quotient.lean`).

* **The ray space `S(V)` (BBS-Q3)** — `GX.RaySphere V`, the unit sphere of `‖·‖`, with the
  normalised action `k · σ = k σ / ‖k σ‖` of the linear automorphisms (`GX.raySphereAction`, a
  `MulAction` of the stabiliser of `0` in the affine group). Chosen over the quotient
  `(V∖0)/ℝ₊*` because `susp(S(V)) ≃ₜ V` is then the explicit `(σ, r) ↦ r σ`
  (`GX.sphereSusp`), whose radius is the norm, so the topology of `GX.Susp`
  (`RamcovGX.tex:710`) is matched ball for ball. The two models are homeomorphic by
  normalisation (classical; NOT formalized here — a reading).
* **The conic structure at `0`** — `GX.affineConic σ₀ : ConicStructure (V ≃ᵃ[ℝ] V) 0
  (linIsom V) (RaySphere V)`, full (`GX.affineConic_isFull`), for `H = GX.linIsom V` the LINEAR
  ISOMETRIES (affine maps fixing `0` and preserving `‖·‖`): `ConicStructure` asks radius
  preservation (BBS-Conic's sufficient correction), and for linear maps the radius is the norm.
  Its chart satisfies the draft's ray condition for the whole `G_p = GL(V)`
  (`GX.affineConic_isRayCompatible`).
* The analyticity lemma of the commented-out draft (row key `draft:lem_analytique`), read
  literally, fails — `GX.lem_analytique_counterexample` (for BBS-Conic; the counterexample
  motivating radius preservation in `ConicStructure`, a design note, not a claim about the
  thesis): with that chart and `G_p = GL(V)`, the induced action on `S(V)` is not faithful
  (`2·id` acts trivially), although `(Aff(V), V)` is analytic.
* **Obstruction** — `GX.not_conicStructure_of_contraction` (`G = Aff(V)`) and
  `GX.not_conicStructure_of_ray_contraction` (any `G` acting on `V`): no RADIUS-PRESERVING conic
  structure at `0` exists, for any chart and any link, when `H` contains an element acting on a
  line as multiplication by `c ∈ ]0, 1[`. Instances: `GX.not_conicStructure_nullBoost`
  (`SO₀(1,1)` on `ℝ²`), `GX.isEmpty_conicStructure_affine_stabilizer` (`H = G_p` in `Aff(V)`)
  and, for BBS's own group, `GX.isEmpty_conicStructure_nullIsom0_stabilizer`: `G = GX.NullIsom0
  = Isom₀(𝔼^{1,2})` (null coordinates, `GX.Singular.Quotient`), `H = G_p = SO₀(1,2)`, which
  contains the boost `GX.nullIsom0Boost = (a, b, x) ↦ (2a, b/2, x)`. What is NOT proved:
  anything about the draft's ray-only notion, or about the weaker radial-lift correction
  (BBS-Celestial). For `G ⊆ Isom`, e.g. `Isom₀(𝔼^{1,2})`, with the sphere chart, a radial lift
  `g_h` of `h ∈ G_p` fixes `0`, so is linear, and has the ray map of `h`, so is a positive
  multiple of `h`, hence `h` (determinant `1`): the obstruction then extends to the minimal
  correction (prose argument, not formalized). So, as far as proved here, L1 for BBS cannot use
  a radius-preserving conic structure; a scale-equivariant variant of the suspension is the
  natural candidate (a finding).
* **Linear chart changes** — `GX.affine_coneChart_linear`: the cone charts of an
  `(H, S(V))`-manifold differ, near every point, by a LINEAR isometry (`h.linear`, `h ∈ H`);
  `S(V)` is locally connected (`GX.locallyConnectedSpace_raySphere`, through
  `GX.Susp.locallyConnectedSpace_of`) and connected in dimension `≥ 2`;
  the suspension `GX.affineSuspension`; the apex over the model sphere is regular
  (`GX.affine_apex_mem_reg`, `dim V ≥ 2`).

## Hypothesis checklist

| BBS / REVIEW §B L1 | here |
|---|---|
| `X = V` affine, `G ≤ Aff(V)` | ✓ `G = V ≃ᵃ[ℝ] V`, `V` a finite-dimensional real normed space (1) |
| `L` the linear part of the stabiliser | ⚠ strengthened: `H` = linear ISOMETRIES of `‖·‖` (2) |
| `S(V) = (V∖0)/ℝ₊*` | ⚠ represented by the unit sphere (BBS-Q3), homeomorphic (not formalized) |

1. The whole affine group; BBS's `G = Isom₀(𝔼^{1,2})` appears only in the obstruction
   (`GX.NullIsom0`).
2. Forced for a RADIUS-PRESERVING conic structure (`not_conicStructure_of_contraction`); not
   claimed necessary for the draft's construction, which the weaker radial-lift correction
   also serves. The normalised action of all linear automorphisms on `S(V)` is built
   (`raySphereAction`).

## SCOPE (disclosed)

* The bridge "celestial suspension ≅ `quotientBase` models" (REVIEW §B L1, last gap) is NOT
  attempted: next step.
* Subgroups `H' ≤ linIsom V` (e.g. `SO(n)`) are not given their own conic structure; restricting
  the action is routine but not written.
* The `(Aff(ℝ), ℝ)` example of BBS-Celestial is formalized only in its "no radius-preserving
  conic structure" half (`isEmpty_conicStructure_affine_stabilizer`); its "the cone préatlas is
  a `(G,X)`-atlas" half is not.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology NNReal Metric

namespace GX

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The ray sphere and `susp(S(V)) ≃ₜ V` -/

variable (V) in
/-- **The ray space `S(V)`** (BBS-Q3), represented by the unit sphere of `‖·‖`. -/
abbrev RaySphere : Type _ := Metric.sphere (0 : V) 1

omit [NormedSpace ℝ V] in
theorem norm_raySphere (σ : RaySphere V) : ‖(σ : V)‖ = 1 := mem_sphere_zero_iff_norm.1 σ.2

omit [NormedSpace ℝ V] in
theorem raySphere_ne_zero (σ : RaySphere V) : (σ : V) ≠ 0 := by
  intro h; have := norm_raySphere σ; rw [h, norm_zero] at this; exact zero_ne_one this

theorem norm_inv_smul_self {v : V} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

open Classical in
/-- Normalisation `v ↦ v / ‖v‖`, with the value `σ₀` at `0`. -/
def rayNormalize (σ₀ : RaySphere V) (v : V) : RaySphere V :=
  if hv : v = 0 then σ₀ else ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.2 (norm_inv_smul_self hv)⟩

theorem coe_rayNormalize (σ₀ : RaySphere V) {v : V} (hv : v ≠ 0) :
    (rayNormalize σ₀ v : V) = ‖v‖⁻¹ • v := by
  rw [rayNormalize, dif_neg hv]

theorem continuousAt_rayNormalize (σ₀ : RaySphere V) {v : V} (hv : v ≠ 0) :
    ContinuousAt (rayNormalize σ₀) v := by
  rw [IsInducing.subtypeVal.continuousAt_iff]
  have h : ContinuousAt (fun w : V => ‖w‖⁻¹ • w) v :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.2 hv)).smul continuousAt_id
  refine h.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hv] with w hw
  exact (coe_rayNormalize σ₀ hw).symm

/-- The cone map `susp(S(V)) → V`, `(σ, r) ↦ r σ`. -/
def sphereConeMap : Susp (RaySphere V) → V :=
  Quotient.lift (fun q : RaySphere V × ℝ≥0 => ((q.2 : ℝ)) • (q.1 : V)) fun a b h => by
    rcases (h : a = b ∨ (a.2 = 0 ∧ b.2 = 0)) with rfl | ⟨ha, hb⟩
    · rfl
    · simp [ha, hb]

theorem sphereConeMap_mk (q : RaySphere V × ℝ≥0) :
    sphereConeMap (Susp.mk q) = (q.2 : ℝ) • (q.1 : V) := rfl

theorem norm_sphereConeMap (a : Susp (RaySphere V)) : ‖sphereConeMap a‖ = (a.r : ℝ) := by
  obtain ⟨q, rfl⟩ := Susp.mk_surjective a
  rw [sphereConeMap_mk, norm_smul, norm_raySphere, mul_one, Real.norm_eq_abs, NNReal.abs_eq]
  rfl

theorem continuous_sphereConeMap : Continuous (sphereConeMap : Susp (RaySphere V) → V) := by
  refine Susp.continuous_of (fun q _ => ?_) fun x hx W hW => ?_
  · exact ((NNReal.continuous_coe.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).continuousAt
  · have h0 : sphereConeMap x = 0 := by
      rw [← norm_eq_zero, norm_sphereConeMap, show x.r = 0 from hx, NNReal.coe_zero]
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
    refine ⟨⟨δ, hδ.le⟩, hδ, fun y hy => hball ?_⟩
    rw [mem_ball, h0, dist_zero_right, norm_sphereConeMap]
    exact hy

/-- The inverse `v ↦ (v/‖v‖, ‖v‖)`. -/
def sphereConeInv (σ₀ : RaySphere V) (v : V) : Susp (RaySphere V) :=
  Susp.mk (rayNormalize σ₀ v, ‖v‖₊)

theorem continuous_sphereConeInv (σ₀ : RaySphere V) : Continuous (sphereConeInv σ₀) := by
  refine continuous_iff_continuousAt.2 fun v => ?_
  by_cases hv : v = 0
  · subst hv
    have hO : sphereConeInv σ₀ (0 : V) ∈ (Susp.O : Set (Susp (RaySphere V))) :=
      show ‖(0 : V)‖₊ = 0 from nnnorm_zero
    refine (Susp.hasBasis_nhds_O hO).tendsto_right_iff.2 fun ε hε => ?_
    have : Tendsto (fun w : V => ‖w‖₊) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_nnnorm.tendsto (0 : V))
    filter_upwards [this (Iio_mem_nhds hε)] with w hw
    exact hw
  · exact Susp.continuous_mk.continuousAt.comp
      ((continuousAt_rayNormalize σ₀ hv).prodMk continuous_nnnorm.continuousAt)

theorem sphereConeMap_sphereConeInv (σ₀ : RaySphere V) (v : V) :
    sphereConeMap (sphereConeInv σ₀ v) = v := by
  by_cases hv : v = 0
  · subst hv; simp [sphereConeInv, sphereConeMap_mk]
  · rw [sphereConeInv, sphereConeMap_mk, coe_rayNormalize σ₀ hv, coe_nnnorm, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]

theorem sphereConeInv_sphereConeMap (σ₀ : RaySphere V) (a : Susp (RaySphere V)) :
    sphereConeInv σ₀ (sphereConeMap a) = a := by
  obtain ⟨q, rfl⟩ := Susp.mk_surjective a
  rcases eq_zero_or_pos q.2 with h | h
  · refine Susp.eq_of_mem_O ?_ (show q.2 = 0 from h)
    show ‖sphereConeMap (Susp.mk q)‖₊ = 0
    rw [sphereConeMap_mk, h]; simp
  · have hne : sphereConeMap (Susp.mk q) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sphereConeMap]; exact_mod_cast h.ne'
    have hn : ‖sphereConeMap (Susp.mk q)‖₊ = q.2 := by
      ext; rw [coe_nnnorm, norm_sphereConeMap]; rfl
    show Susp.mk (rayNormalize σ₀ _, _) = Susp.mk q
    rw [hn]
    congr 1
    refine Prod.ext (Subtype.ext ?_) rfl
    rw [coe_rayNormalize σ₀ hne, norm_sphereConeMap, sphereConeMap_mk, smul_smul, Susp.r_mk,
      inv_mul_cancel₀ (by exact_mod_cast h.ne'), one_smul]

/-- **`susp(S(V)) ≃ₜ V`**, `(σ, r) ↦ r σ` (the apex to `0`). -/
def sphereSusp (σ₀ : RaySphere V) : Susp (RaySphere V) ≃ₜ V where
  toFun := sphereConeMap
  invFun := sphereConeInv σ₀
  left_inv := sphereConeInv_sphereConeMap σ₀
  right_inv := sphereConeMap_sphereConeInv σ₀
  continuous_toFun := continuous_sphereConeMap
  continuous_invFun := continuous_sphereConeInv σ₀

theorem sphereConeInv_mem_O_iff (σ₀ : RaySphere V) {v : V} :
    sphereConeInv σ₀ v ∈ (Susp.O : Set (Susp (RaySphere V))) ↔ v = 0 :=
  nnnorm_eq_zero

theorem dir_sphereConeInv (σ₀ : RaySphere V) {v : V} (hv : v ≠ 0) :
    (sphereConeInv σ₀ v).dir = rayNormalize σ₀ v :=
  Susp.dir_mk_of_pos (show (0 : ℝ≥0) < ‖v‖₊ from nnnorm_pos.2 hv)

/-- Normalisation forgets a positive factor. -/
theorem rayNormalize_smul_of_pos (σ₀ : RaySphere V) {v : V} (hv : v ≠ 0) {c : ℝ} (hc : 0 < c) :
    rayNormalize σ₀ (c • v) = rayNormalize σ₀ v := by
  have hcv : c • v ≠ 0 := smul_ne_zero hc.ne' hv
  refine Subtype.ext ?_
  rw [coe_rayNormalize σ₀ hcv, coe_rayNormalize σ₀ hv, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, smul_smul]
  congr 1
  field_simp

theorem rayNormalize_raySphere (σ₀ σ : RaySphere V) : rayNormalize σ₀ (σ : V) = σ := by
  refine Subtype.ext ?_
  rw [coe_rayNormalize σ₀ (raySphere_ne_zero σ), norm_raySphere, inv_one, one_smul]

/-! ### Linear automorphisms acting on `S(V)` -/

theorem affine_apply_eq_linear {g : V ≃ᵃ[ℝ] V} (hg : g 0 = 0) (v : V) : g v = g.linear v := by
  have := g.toAffineMap.linearMap_vsub v 0
  simp only [vsub_eq_sub, sub_zero, AffineEquiv.coe_toAffineMap, AffineEquiv.linear_toAffineMap,
    hg] at this
  exact this.symm

theorem affine_map_smul_of_fix {g : V ≃ᵃ[ℝ] V} (hg : g 0 = 0) (c : ℝ) (v : V) :
    g (c • v) = c • g v := by
  rw [affine_apply_eq_linear hg, affine_apply_eq_linear hg, map_smul]

theorem affine_ne_zero_of_fix {g : V ≃ᵃ[ℝ] V} (hg : g 0 = 0) {v : V} (hv : v ≠ 0) : g v ≠ 0 :=
  fun h => hv (g.injective (h.trans hg.symm))

/-- The normalised action `k · σ = k σ / ‖k σ‖` (BBS's action on `S(V)`). -/
def raySmul (k : V ≃ᵃ[ℝ] V) (hk : k 0 = 0) (σ : RaySphere V) : RaySphere V :=
  ⟨‖k σ‖⁻¹ • k σ, mem_sphere_zero_iff_norm.2
    (norm_inv_smul_self (affine_ne_zero_of_fix hk (raySphere_ne_zero σ)))⟩

/-- **`S(V)` with its action of the linear automorphisms** (REVIEW §B L1, first gap): the
normalised action of the stabiliser of `0` in the affine group (= the linear group). -/
@[reducible] def raySphereAction :
    MulAction (MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) (RaySphere V) where
  smul k σ := raySmul (k : V ≃ᵃ[ℝ] V) k.2 σ
  one_smul σ := by
    refine Subtype.ext ?_
    show ‖(σ : V)‖⁻¹ • (σ : V) = σ
    rw [norm_raySphere, inv_one, one_smul]
  mul_smul k k' σ := by
    refine Subtype.ext ?_
    have hk : (k : V ≃ᵃ[ℝ] V) 0 = 0 := k.2
    have hk' : (k' : V ≃ᵃ[ℝ] V) 0 = 0 := k'.2
    show ‖(k : V ≃ᵃ[ℝ] V) ((k' : V ≃ᵃ[ℝ] V) σ)‖⁻¹ • (k : V ≃ᵃ[ℝ] V) ((k' : V ≃ᵃ[ℝ] V) σ) =
      ‖(k : V ≃ᵃ[ℝ] V) (‖(k' : V ≃ᵃ[ℝ] V) σ‖⁻¹ • (k' : V ≃ᵃ[ℝ] V) σ)‖⁻¹ •
        (k : V ≃ᵃ[ℝ] V) (‖(k' : V ≃ᵃ[ℝ] V) σ‖⁻¹ • (k' : V ≃ᵃ[ℝ] V) σ)
    have hne : ‖(k' : V ≃ᵃ[ℝ] V) σ‖ ≠ 0 :=
      norm_ne_zero_iff.2 (affine_ne_zero_of_fix hk' (raySphere_ne_zero σ))
    rw [affine_map_smul_of_fix hk, norm_smul, norm_inv, norm_norm, smul_smul, mul_inv,
      inv_inv, mul_assoc, mul_left_comm, mul_inv_cancel₀ hne, mul_one]

/-! ### The conic structure at `0` for the linear isometries -/

variable (V) in
/-- The **linear isometries** of `‖·‖`, as affine maps: those fixing `0` and preserving the norm. -/
def linIsom : Subgroup (V ≃ᵃ[ℝ] V) where
  carrier := {g | g 0 = 0 ∧ ∀ v, ‖g v‖ = ‖v‖}
  one_mem' := ⟨rfl, fun _ => rfl⟩
  mul_mem' {a b} ha hb := ⟨show a (b 0) = 0 by rw [hb.1, ha.1],
    fun v => show ‖a (b v)‖ = ‖v‖ by rw [ha.2, hb.2]⟩
  inv_mem' {a} ha := by
    refine ⟨?_, fun v => ?_⟩
    · show a.symm 0 = 0
      exact a.injective (by rw [a.apply_symm_apply, ha.1])
    · show ‖a.symm v‖ = ‖v‖
      rw [← ha.2 (a.symm v), a.apply_symm_apply]

theorem linIsom_fix (h : linIsom V) : (h : V ≃ᵃ[ℝ] V) 0 = 0 := h.2.1

theorem norm_linIsom (h : linIsom V) (v : V) : ‖(h : V ≃ᵃ[ℝ] V) v‖ = ‖v‖ := h.2.2 v

/-- The action of the linear isometries on `S(V)` (`h · σ = h σ`; the normalised action
`raySphereAction`, restricted, since `‖h σ‖ = 1`). -/
instance linIsomAction : MulAction (linIsom V) (RaySphere V) where
  smul h σ := ⟨(h : V ≃ᵃ[ℝ] V) σ, mem_sphere_zero_iff_norm.2 (by
    rw [norm_linIsom, norm_raySphere])⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem coe_linIsom_smul (h : linIsom V) (σ : RaySphere V) :
    ((h • σ : RaySphere V) : V) = (h : V ≃ᵃ[ℝ] V) σ := rfl

/-- The isometric action is the normalised one. -/
theorem linIsom_smul_eq_raySmul (h : linIsom V) (σ : RaySphere V) :
    h • σ = raySmul (h : V ≃ᵃ[ℝ] V) (linIsom_fix h) σ := by
  refine Subtype.ext ?_
  show (h : V ≃ᵃ[ℝ] V) σ = ‖(h : V ≃ᵃ[ℝ] V) σ‖⁻¹ • (h : V ≃ᵃ[ℝ] V) σ
  rw [norm_linIsom, norm_raySphere, inv_one, one_smul]

theorem sphereConeInv_smul (σ₀ : RaySphere V) (h : linIsom V) (x : V) :
    sphereConeInv σ₀ ((h : V ≃ᵃ[ℝ] V) x) =
      Susp.map (fun σ : RaySphere V => h • σ) (sphereConeInv σ₀ x) := by
  by_cases hx : x = 0
  · subst hx
    rw [linIsom_fix]
    exact Susp.eq_of_mem_O (show ‖(0 : V)‖₊ = 0 from nnnorm_zero)
      ((Susp.map_mem_O_iff _).2 (show ‖(0 : V)‖₊ = 0 from nnnorm_zero))
  · have hhx : (h : V ≃ᵃ[ℝ] V) x ≠ 0 := affine_ne_zero_of_fix (linIsom_fix h) hx
    rw [sphereConeInv, sphereConeInv, Susp.map_mk]
    have hn : ‖(h : V ≃ᵃ[ℝ] V) x‖₊ = ‖x‖₊ :=
      NNReal.eq (by rw [coe_nnnorm, coe_nnnorm, norm_linIsom])
    rw [hn]
    congr 1
    refine Prod.ext (Subtype.ext ?_) rfl
    show (rayNormalize σ₀ ((h : V ≃ᵃ[ℝ] V) x) : V) = (h : V ≃ᵃ[ℝ] V) (rayNormalize σ₀ x)
    rw [coe_rayNormalize σ₀ hhx, coe_rayNormalize σ₀ hx, affine_map_smul_of_fix (linIsom_fix h),
      norm_linIsom]

/-- **The conic structure of `V` at `0`** for the affine group and the linear isometries, with
link `S(V)` (`draft:structure_conique`, the commented-out draft's `these.tex:3569`, in its
corrected form): `φ = (σ, r) ↦
r σ` inverted. -/
def affineConic (σ₀ : RaySphere V) :
    ConicStructure (V ≃ᵃ[ℝ] V) (0 : V) (linIsom V) (RaySphere V) where
  φ := (sphereSusp σ₀).symm.toOpenPartialHomeomorph
  mem_source := trivial
  map_mem_O := show ‖(0 : V)‖₊ = 0 from nnnorm_zero
  le_stabilizer _ hh := MulAction.mem_stabilizer_iff.2 hh.1
  map_smul h x _ _ := sphereConeInv_smul σ₀ h x

theorem affineConic_isFull (σ₀ : RaySphere V) : (affineConic σ₀).IsFull :=
  Homeomorph.toOpenPartialHomeomorph_target _

theorem affineConic_symm_mk (σ₀ : RaySphere V) (q : RaySphere V × ℝ≥0) :
    (affineConic σ₀).φ.symm (Susp.mk q) = (q.2 : ℝ) • (q.1 : V) := rfl

theorem affineConic_apply (σ₀ : RaySphere V) (v : V) :
    (affineConic σ₀).φ v = sphereConeInv σ₀ v := rfl

/-- **The sphere chart at `0` satisfies the draft's ray condition for the FULL stabiliser**
`G_p = GL(V)` (`these.tex:3574`; not only for `linIsom V`): a linear map sends rays to rays. -/
theorem affineConic_isRayCompatible (σ₀ : RaySphere V) :
    (affineConic σ₀).toConicChart.IsRayCompatible
      (MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) := by
  intro h hh x _ y _ _ _ hx hy hxy
  have h0 : h 0 = 0 := hh
  simp only [affineConic_apply, sphereConeInv_mem_O_iff, affineEquiv_smul_def] at hx hy hxy ⊢
  rw [dir_sphereConeInv σ₀ hx, dir_sphereConeInv σ₀ hy] at hxy
  rw [dir_sphereConeInv σ₀ (affine_ne_zero_of_fix h0 hx),
    dir_sphereConeInv σ₀ (affine_ne_zero_of_fix h0 hy)]
  have e := congrArg Subtype.val hxy
  rw [coe_rayNormalize σ₀ hx, coe_rayNormalize σ₀ hy] at e
  have hyx : y = (‖y‖ * ‖x‖⁻¹) • x := by
    rw [← smul_smul, e, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hy), one_smul]
  have hpos : 0 < ‖y‖ * ‖x‖⁻¹ := mul_pos (norm_pos_iff.2 hy) (inv_pos.2 (norm_pos_iff.2 hx))
  rw [hyx, affine_map_smul_of_fix h0,
    rayNormalize_smul_of_pos σ₀ (affine_ne_zero_of_fix h0 hx) hpos]

/-! ### Obstruction: no contraction in `H` -/

/-- **No RADIUS-PRESERVING conic structure at `0` admits a contraction in `H`** (a finding, from
`GX.ConicStructure.eq_of_tendsto_pow`): if some `h ∈ H` fixes `0` and has an eigenvector with
eigenvalue in `]0, 1[`, then there is no `ConicStructure (V ≃ᵃ[ℝ] V) 0 H L`, whatever the
chart, the link `L` and its action. Nothing is claimed about the draft's ray-only notion or
about the weaker radial-lift correction. -/
theorem not_conicStructure_of_contraction {H : Subgroup (V ≃ᵃ[ℝ] V)} {L : Type*}
    [TopologicalSpace L] [MulAction H L] (h : H) {v : V} (hv : v ≠ 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (hh : (h : V ≃ᵃ[ℝ] V) v = c • v)
    (cs : ConicStructure (V ≃ᵃ[ℝ] V) (0 : V) H L) : False := by
  have h0 : (h : V ≃ᵃ[ℝ] V) 0 = 0 := cs.le_stabilizer h.2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 cs.φ.open_source 0 cs.mem_source
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set x : V := (δ / (2 * ‖v‖)) • v with hxdef
  have hxn : ‖x‖ = δ / 2 := by
    rw [hxdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hx0 : x ≠ 0 := by
    intro hx; rw [hx, norm_zero] at hxn; linarith
  have hpow : ∀ n : ℕ, ((h : V ≃ᵃ[ℝ] V) ^ n) • x = c ^ n • x := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
    | succ n ih =>
      rw [pow_succ', mul_smul, ih, affineEquiv_smul_def, affine_map_smul_of_fix h0, hxdef,
        affine_map_smul_of_fix h0, hh, pow_succ, smul_comm (δ / (2 * ‖v‖)) c v, smul_smul]
  have hmem : ∀ n : ℕ, ((h : V ≃ᵃ[ℝ] V) ^ n) • x ∈ cs.φ.source := by
    intro n
    refine hball ?_
    rw [hpow, mem_ball, dist_zero_right, norm_smul, hxn, Real.norm_eq_abs,
      abs_of_pos (pow_pos hc0 n)]
    calc c ^ n * (δ / 2) ≤ 1 * (δ / 2) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hc0.le hc1.le) (by positivity)
      _ < δ := by linarith
  have hlim : Tendsto (fun n : ℕ => ((h : V ≃ᵃ[ℝ] V) ^ n) • x) atTop (𝓝 0) := by
    simp only [hpow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).smul_const x
  exact hx0 (cs.eq_of_tendsto_pow h (by simpa using hmem 0) hmem hlim)

/-- **A witness of the obstruction: the null boost** `(a, b) ↦ (2a, b/2)` of `ℝ²`, the boost of
`SO₀(1,1)` written in null coordinates (it preserves `a·b`). It has the eigenvalue `1/2` on the
null line `0 × ℝ`. For BBS's own group `SO₀(1,2)` see `nullIsom0Boost`. -/
def nullBoost : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) :=
  ((LinearEquiv.smulOfNeZero ℝ ℝ 2 two_ne_zero).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ 2⁻¹ (inv_ne_zero two_ne_zero))).toAffineEquiv

theorem nullBoost_apply (a b : ℝ) : nullBoost (a, b) = (2 * a, 2⁻¹ * b) := rfl

/-- `nullBoost` preserves the null quadratic form `a·b`: it is a Lorentz boost. -/
theorem nullBoost_mul (a b : ℝ) : (nullBoost (a, b)).1 * (nullBoost (a, b)).2 = a * b := by
  rw [nullBoost_apply]; field_simp

/-- **No RADIUS-PRESERVING conic structure at `0` of `ℝ²` for any `H` containing a boost** (here
`nullBoost`, in `SO₀(1,1)`, for `G = Aff(ℝ²)`). This is not a statement about the draft's
ray-only notion; the BBS case is `isEmpty_conicStructure_nullIsom0_stabilizer`. -/
theorem not_conicStructure_nullBoost {H : Subgroup ((ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ))} (hB : nullBoost ∈ H)
    {L : Type*} [TopologicalSpace L] [MulAction H L] :
    IsEmpty (ConicStructure ((ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) ((0 : ℝ × ℝ)) H L) := by
  refine ⟨fun cs => not_conicStructure_of_contraction ⟨nullBoost, hB⟩ (v := ((0 : ℝ), (1 : ℝ)))
    (by simp) (c := 2⁻¹) (by norm_num) (by norm_num) ?_ cs⟩
  show nullBoost (0, 1) = (2⁻¹ : ℝ) • ((0 : ℝ), (1 : ℝ))
  rw [nullBoost_apply]; ext <;> simp

/-- **The obstruction for any group** `G` acting on `V` (`G` plays no role in the proof): if
`h ∈ H` acts on the line `ℝ v` as multiplication by `c ∈ ]0, 1[`, there is no RADIUS-PRESERVING
conic structure `ConicStructure G 0 H L`, whatever the chart, the link and its action. -/
theorem not_conicStructure_of_ray_contraction {G : Type*} [Group G] [MulAction G V]
    {H : Subgroup G} {L : Type*} [TopologicalSpace L] [MulAction H L] (h : H) {v : V}
    (hv : v ≠ 0) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hh : ∀ s : ℝ, (h : G) • (s • v) = (c * s) • v)
    (cs : ConicStructure G (0 : V) H L) : False := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 cs.φ.open_source 0 cs.mem_source
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set a : ℝ := δ / (2 * ‖v‖) with hadef
  have ha : 0 < a := by positivity
  have hxn : ‖a • v‖ = δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hadef]
    field_simp
  have hx0 : a • v ≠ 0 := smul_ne_zero ha.ne' hv
  have hpow : ∀ n : ℕ, ((h : G) ^ n) • (a • v) = (c ^ n * a) • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul, one_mul]
    | succ n ih => rw [pow_succ', mul_smul, ih, hh, pow_succ', mul_assoc]
  have hmem : ∀ n : ℕ, ((h : G) ^ n) • (a • v) ∈ cs.φ.source := by
    intro n
    refine hball ?_
    rw [hpow, mem_ball, dist_zero_right, mul_smul, norm_smul, hxn, Real.norm_eq_abs,
      abs_of_pos (pow_pos hc0 n)]
    calc c ^ n * (δ / 2) ≤ 1 * (δ / 2) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hc0.le hc1.le) (by positivity)
      _ < δ := by linarith
  have hlim : Tendsto (fun n : ℕ => ((h : G) ^ n) • (a • v)) atTop (𝓝 0) := by
    simp only [hpow, mul_smul]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).smul_const (a • v)
  exact hx0 (cs.eq_of_tendsto_pow h (by simpa using hmem 0) hmem hlim)

/-- **No radius-preserving conic structure for the full affine stabiliser** `G_p = GL(V)`
(`V ≠ 0`): it contains the contraction `v ↦ v/2`. With `V = ℝ` this is the half of the
`(Aff(ℝ), ℝ)` example (BBS-Celestial) showing radius preservation is not NECESSARY for the
draft's suspension proposition: there the cone préatlas IS a `(G,X)`-atlas (not formalized). -/
theorem isEmpty_conicStructure_affine_stabilizer [Nontrivial V] {L : Type*} [TopologicalSpace L]
    [MulAction (MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) L] :
    IsEmpty (ConicStructure (V ≃ᵃ[ℝ] V) (0 : V) (MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) L) := by
  refine ⟨fun cs => ?_⟩
  set T : V ≃ᵃ[ℝ] V :=
    (LinearEquiv.smulOfNeZero ℝ V 2⁻¹ (inv_ne_zero two_ne_zero)).toAffineEquiv with hT
  have hT0 : T • (0 : V) = 0 := by simp [hT, affineEquiv_smul_def]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine not_conicStructure_of_ray_contraction ⟨T, hT0⟩ hv (c := 2⁻¹) (by norm_num)
    (by norm_num) (fun s => ?_) cs
  show (2⁻¹ : ℝ) • (s • v) = (2⁻¹ * s) • v
  rw [smul_smul]

/-- **The boost of BBS's group**: `B = (a, b, x) ↦ (2a, b/2, x)`, the boost `GX.boost (log 2)` of
`GX.NullIsom0 = Isom₀(𝔼^{1,2})` in null coordinates (`GX.Singular.Quotient`); it fixes `0` and
has the eigenvalue `1/2` on the null line `0 × ℝ × 0`. -/
noncomputable def nullIsom0Boost : NullIsom0 :=
  ⟨(boost (Real.log 2)).toAffineEquiv, boost_lin_mem _⟩

theorem nullIsom0Boost_smul (y : ℝ × ℝ × ℝ) :
    nullIsom0Boost • y = (2 * y.1, 2⁻¹ * y.2.1, y.2.2) := by
  show boost (Real.log 2) y = _
  rw [boost_apply, Real.exp_neg, Real.exp_log two_pos]

theorem nullIsom0Boost_mem_stabilizer :
    nullIsom0Boost ∈ MulAction.stabilizer NullIsom0 (0 : ℝ × ℝ × ℝ) := by
  rw [MulAction.mem_stabilizer_iff, nullIsom0Boost_smul]; simp

/-- **No RADIUS-PRESERVING conic structure at `0` for BBS's group** `G = Isom₀(𝔼^{1,2})`
(`GX.NullIsom0`) and any `H ≤ G_p` containing the boost `nullIsom0Boost`, whatever the chart,
the link `L` and its action. -/
theorem isEmpty_conicStructure_nullIsom0 {H : Subgroup NullIsom0} (hB : nullIsom0Boost ∈ H)
    {L : Type*} [TopologicalSpace L] [MulAction H L] :
    IsEmpty (ConicStructure NullIsom0 (0 : ℝ × ℝ × ℝ) H L) := by
  refine ⟨fun cs => not_conicStructure_of_ray_contraction ⟨nullIsom0Boost, hB⟩
    (v := ((0 : ℝ), (1 : ℝ), (0 : ℝ))) (by simp) (c := 2⁻¹) (by norm_num) (by norm_num)
    (fun s => ?_) cs⟩
  show nullIsom0Boost • (s • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) =
    (2⁻¹ * s) • ((0 : ℝ), (1 : ℝ), (0 : ℝ))
  rw [nullIsom0Boost_smul]; ext <;> simp

/-- **The BBS case, with the draft's `G_p`**: no RADIUS-PRESERVING conic structure at `0` for
`G = Isom₀(𝔼^{1,2})` and `H = G_p = SO₀(1,2)`. -/
theorem isEmpty_conicStructure_nullIsom0_stabilizer {L : Type*} [TopologicalSpace L]
    [MulAction (MulAction.stabilizer NullIsom0 (0 : ℝ × ℝ × ℝ)) L] :
    IsEmpty (ConicStructure NullIsom0 (0 : ℝ × ℝ × ℝ)
      (MulAction.stabilizer NullIsom0 (0 : ℝ × ℝ × ℝ)) L) :=
  isEmpty_conicStructure_nullIsom0 nullIsom0Boost_mem_stabilizer

/-! ### Local connectedness of the link, and the suspension of `(H, S(V))`-manifolds -/

/-- A space whose suspension is locally connected is locally connected (projecting a connected
neighbourhood of `(σ, 1)` by `π`). -/
theorem Susp.locallyConnectedSpace_of {S : Type*} [TopologicalSpace S]
    [LocallyConnectedSpace (Susp S)] : LocallyConnectedSpace S := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun σ U hU => ?_
  obtain ⟨U', hU'U, hU'o, hσU'⟩ := mem_nhds_iff.1 hU
  set B : Set (Susp S) := Susp.mk '' (U' ×ˢ Ioi 0) with hB
  have hBo : IsOpen B := Susp.isOpen_image_mk (hU'o.prod isOpen_Ioi) fun q hq => hq.2
  have hσB : Susp.mk (σ, 1) ∈ B := ⟨(σ, 1), ⟨hσU', show (0 : ℝ≥0) < 1 from one_pos⟩, rfl⟩
  obtain ⟨C, hCB, hCo, hσC, hCc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 ‹_› _ B (hBo.mem_nhds hσB)
  have hpos : ∀ c ∈ C, 0 < c.r := fun c hc => by
    obtain ⟨q, ⟨-, hq2⟩, rfl⟩ := hCB hc; exact hq2
  refine ⟨Susp.dir '' C, ?_, ?_, ⟨Susp.mk (σ, 1), hσC, Susp.dir_mk_of_pos one_pos⟩, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hCB hc
    rw [Susp.dir_mk_of_pos hq2]; exact hU'U hq1
  · have e : Susp.dir '' C = Prod.fst '' (Susp.mk ⁻¹' C) := by
      ext τ
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨q, ⟨-, hq2⟩, rfl⟩ := hCB hc
        exact ⟨q, hc, (Susp.dir_mk_of_pos hq2).symm⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨q', ⟨-, hq2'⟩, hq'⟩ := hCB hq
        obtain rfl := Susp.eq_of_mk_eq_of_pos hq' hq2'
        exact ⟨Susp.mk q', hq, Susp.dir_mk_of_pos hq2'⟩
    rw [e]
    exact isOpenMap_fst _ (hCo.preimage Susp.continuous_mk)
  · exact hCc.image _ fun c hc => (Susp.continuousAt_dir (hpos c hc)).continuousWithinAt

/-- `S(V)` is locally connected. -/
instance locallyConnectedSpace_raySphere : LocallyConnectedSpace (RaySphere V) := by
  rcases isEmpty_or_nonempty (RaySphere V) with h | ⟨⟨σ₀⟩⟩
  · exact ⟨fun x => (h.false x).elim⟩
  · haveI : LocallyConnectedSpace (Susp (RaySphere V)) := (sphereSusp σ₀).locallyConnectedSpace
    exact Susp.locallyConnectedSpace_of

/-- `S(V)` is connected in dimension `≥ 2`. -/
theorem preconnectedSpace_raySphere (hdim : 1 < Module.rank ℝ V) :
    PreconnectedSpace (RaySphere V) :=
  Subtype.preconnectedSpace (isConnected_sphere hdim 0 zero_le_one).isPreconnected

variable [FiniteDimensional ℝ V]

/-- **The cone of an `S(V)`-chart has LINEAR chart changes** (REVIEW §B L1, second gap): near
every point of the overlap of two cone charts of `(H, S(V))`-charts `e, e'` of `Σ`, the second is
a linear map (the linear part of some `h ∈ linIsom V`, an isometry) applied to the first. -/
theorem affine_coneChart_linear (σ₀ : RaySphere V) {S : Type*} [TopologicalSpace S]
    [SingularGXStructure (linIsom V) (RaySphere V) S] {e e' : OpenPartialHomeomorph S (RaySphere V)}
    (he : e ∈ aeAtlas (linIsom V) (RaySphere V) S) (he' : e' ∈ aeAtlas (linIsom V) (RaySphere V) S)
    {z : Susp S}
    (hz : z ∈ ((affineConic σ₀).coneChart e).source ∩ ((affineConic σ₀).coneChart e').source) :
    ∃ A : V ≃ₗ[ℝ] V, (∀ v, ‖A v‖ = ‖v‖) ∧
      ∀ᶠ y in 𝓝 z, (affineConic σ₀).coneChart e' y = A ((affineConic σ₀).coneChart e y) := by
  obtain ⟨h, hh⟩ := (affineConic σ₀).eventually_coneChart_eq_smul (affineConic_isFull σ₀) he he' hz
  refine ⟨(h : V ≃ᵃ[ℝ] V).linear, fun v => ?_, ?_⟩
  · rw [← affine_apply_eq_linear (linIsom_fix h), norm_linIsom]
  · filter_upwards [hh] with y hy
    rw [hy, affineEquiv_smul_def, affine_apply_eq_linear (linIsom_fix h)]

/-- **The `(Aff(V), V)`-suspension céleste of an `(H, S(V))`-manifold** (`H` the linear
isometries): `draft:defi_suspension_celeste` at the conic structure `affineConic`. -/
@[reducible] def affineSuspension (σ₀ : RaySphere V) (S : Type*) [TopologicalSpace S]
    [PreconnectedSpace S] [LocallyConnectedSpace S]
    [SingularGXStructure (linIsom V) (RaySphere V) S] :
    SingularGXStructure (V ≃ᵃ[ℝ] V) V (Susp S) :=
  (affineConic σ₀).celestialStructure S (affineConic_isFull σ₀)

/-- **The apex over the model sphere is regular** (`dim V ≥ 2`): the suspension of `S(V)` with
its tautological `(H, S(V))`-structure is regular at `O` — the cone over the round sphere is `V`. -/
theorem affine_apex_mem_reg (hdim : 1 < Module.rank ℝ V) (σ₀ σ : RaySphere V) :
    haveI := preconnectedSpace_raySphere hdim
    haveI := (affineConic σ₀).continuousConstSMul
    haveI := (affineConic σ₀).isRigidAction
    letI : SingularGXStructure (linIsom V) (RaySphere V) (RaySphere V) :=
      SingularGXStructure.ofHasGroupoid (linIsom V) (RaySphere V) (RaySphere V)
    letI := affineSuspension σ₀ (RaySphere V)
    Susp.mk (σ, 0) ∈ Reg (V ≃ᵃ[ℝ] V) V (Susp (RaySphere V)) :=
  haveI := preconnectedSpace_raySphere hdim
  (affineConic σ₀).apex_mem_reg_model (affineConic_isFull σ₀) σ

/-! ### The draft's `draft:lem_analytique`, read literally, fails: a counterexample -/

/-- **The draft's lemma (`draft:lem_analytique`, the commented-out `these.tex:3606`, not part of
the thesis), read literally, fails**; this counterexample motivates radius preservation in
`ConicStructure`. `(G,X) = (Aff(V), V)` is analytic (faithful and rigid), and the sphere chart at
`0` satisfies the draft's ray condition for `G_p = GL(V)` (`affineConic_isRayCompatible`); but
the induced action of `G_p` on the link `S(V)` (`ConicChart.linkAction`) is NOT faithful, so
`(G_p, X_p)` is not analytic: the homothety `2·id ≠ 1` acts trivially on `S(V)`. -/
theorem lem_analytique_counterexample [Nontrivial V] (σ₀ : RaySphere V) :
    IsAnalyticAction (V ≃ᵃ[ℝ] V) V ∧
      letI := (affineConic σ₀).toConicChart.linkAction le_rfl (affineConic_isRayCompatible σ₀)
      ¬ FaithfulSMul (MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) (RaySphere V) := by
  have hF : FaithfulSMul (V ≃ᵃ[ℝ] V) V := ⟨fun {f g} hfg => AffineEquiv.ext fun v => hfg v⟩
  refine ⟨{ toFaithfulSMul := hF, toIsRigidAction := inferInstance }, ?_⟩
  letI := (affineConic σ₀).toConicChart.linkAction le_rfl (affineConic_isRayCompatible σ₀)
  intro hF
  set T : V ≃ᵃ[ℝ] V := (LinearEquiv.smulOfNeZero ℝ V 2 two_ne_zero).toAffineEquiv with hT
  have hT0 : T • (0 : V) = 0 := by simp [hT, affineEquiv_smul_def]
  set k : MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V) := ⟨T, hT0⟩
  -- `2·id` acts trivially on the link
  have hk : ∀ σ : RaySphere V, k • σ = (1 : MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V)) • σ := by
    intro σ
    have e := (affineConic σ₀).toConicChart.dir_smul_linkAction le_rfl
      (affineConic_isRayCompatible σ₀) k (x := (σ : V)) trivial trivial
      (by rw [show (affineConic σ₀).toConicChart.φ (σ : V) = sphereConeInv σ₀ σ from rfl,
          sphereConeInv_mem_O_iff]; exact raySphere_ne_zero σ)
    rw [one_smul]
    change (sphereConeInv σ₀ (T • (σ : V))).dir = k • (sphereConeInv σ₀ (σ : V)).dir at e
    have hTσ : T • (σ : V) = (2 : ℝ) • (σ : V) := rfl
    rw [hTσ, dir_sphereConeInv σ₀ (smul_ne_zero two_ne_zero (raySphere_ne_zero σ)),
      dir_sphereConeInv σ₀ (raySphere_ne_zero σ),
      rayNormalize_smul_of_pos σ₀ (raySphere_ne_zero σ) two_pos, rayNormalize_raySphere] at e
    exact e.symm
  have hk1 : k = 1 := hF.eq_of_smul_eq_smul hk
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have e : T • v = v := by
    have := congrArg (fun g : MulAction.stabilizer (V ≃ᵃ[ℝ] V) (0 : V) => (g : V ≃ᵃ[ℝ] V) • v) hk1
    simpa using this
  have e2 : (2 : ℝ) • v = v := e
  have : (1 : ℝ) • v = 0 := by
    rw [show (1 : ℝ) = 2 - 1 by norm_num, sub_smul, e2, one_smul, sub_self]
  exact hv (by simpa using this)

end GX
