import Causal.Flat.Externals

/-!
# A non-elliptic element commuting with `N` on a timelike subspace gives a fixed isotropic direction of a finite-index subgroup

The non-elliptic step of Barbot's Prop 10.4 (`bprop:U_timelike`, `GHFspace.tex` l.3346–3362),
served to `bprop_U_timelike` (`Flat/Loxodromic.lean`, route R3), and the same move as the centre
step of Prop 10.5 (`bprop:LU_discrete`, l.3380–3388): a generalisation of
`Lox.exists_finiteIndex_fix_of_central_nonElliptic` (`Flat/Lox/CentralFix.lean`) in which `z`
commutes with `N` only on a `G`- and `N`-invariant subspace `W` containing a timelike vector. If a
group `N ≤ SO₀(1, d)` normalised by `G` has such an element `z`, non-elliptic, a finite-index
subgroup of `G` fixes a point of `𝒮`. **No label is marked**: this is one step of two proofs, not
a statement of the paper.

* `bprop:U_timelike`, `GHFspace.tex:3356–3358`, partial (the non-elliptic branch, with
  commutation only on a timelike `W`; **no `sorry`**):
  `exists_finiteIndex_fix_of_commuteOn_nonElliptic`.
* `bprop:LU_discrete`, `GHFspace.tex:3381–3388`, partial (the centre step; **no `sorry`**): the
  same theorem (with `W = ⊤` it is the `CentralFix` theorem).

> If it contains a parabolic element $\gamma_{0}$, the unique
> isotropic direction of $\gamma_{0}$ is $L_{U}(\Gamma)$-invariant, and
> thus $L(\Gamma)$-invariant. Contradiction.
>
> If the center contains a hyperbolic element $\gamma_{0}$, then the
> two isotropic fixed points of $L(\gamma_{0})$
> has to be exchanged by every element of $L(\Gamma)$. Contradiction. (l.3382–3388)

> Now, an abelian subgroup
> of $SO_{0}(1,n-1)$ fixes a pair of isotropic directions, except
> if it consists only one elliptic elements fixing one and
> only one timelike vector $v_{0}$. (l.3356–3359)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `γ₀` central in the (nilpotent) identity component | ⚠ weakened: `z ∈ N` commutes with `N` on `W` only (`hzc`); nilpotency unused |
| `U` timelike, `L(Γ)`- and `L(Γ_nd)`-invariant | ✓ as `W` with a timelike vector (`hWt`), `G`- and `N`-stable (`hGW`, `hNW`) |
| `N` normalised by `L(Γ)` | ✓ carried (`hnorm`; `N ≤ G` not required) |
| `γ₀` parabolic or hyperbolic | ✓ carried as `¬IsElliptic` (`hne`; trichotomy) |
| conclusion "invariant / exchanged" | ✓ as: a subgroup of index `≤ 2` fixes a point of `𝒮` |

## SCOPE (disclosed)

Only this step is proved; producing `z` (l.3372–3380) is not treated here.

Proof: `𝐌ⁿ = W ⊕ W^⊥` with `W^⊥` spacelike (`W` holds a timelike vector). A null eigenvector
`e = w + w'` of `z` splits along it (`z` preserves both); `w' ≠ 0` forces eigenvalue `1`, then `w`
is a fixed timelike vector and `z` is elliptic. So every null eigenline of `z` lies in `W`, and so
do its `G`-images. For `A ∈ G` and `u ∈ F(z)`, `z' = A z A⁻¹ ∈ N` is non-elliptic with null
eigenvector `e' = nullVec [A]u ∈ W`; `z e'` is an eigenvector of `z'` with the same eigenvalue
(`hzc`), hence proportional to `e'`: `[A]u ∈ F(z)`. Then `G` permutes `F(z)`, which has one or two
points, and the stabiliser has index `≤ 2` (the finish of `CentralFix`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (R3 for `bprop_U_timelike`). The auxiliaries `cof_*` are private copies of
`Flat/Lox/CentralFix.lean`'s private `cfx_*` (no public-name collision with the other `Flat/Lox/`
files).
-/

namespace Causal.Flat.Lox
open Set
variable {d : ℕ}

private theorem cof_exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
    ∃ (u : PenroseSphere d) (c : ℝ), c ≠ 0 ∧ nullVec u = c • e := by
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 he.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := he; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  refine ⟨⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩, e.1⁻¹, inv_ne_zero he1, ?_⟩
  refine Prod.ext ?_ rfl
  simp [nullVec, inv_mul_cancel₀ he1]

private theorem cof_lorentzSphere_one (u : PenroseSphere d) :
    lorentzSphere (1 : lorentz d) u = u :=
  lorentzSphere_eq_of_eigen (c := 1) (by simp)

private theorem cof_lorentzSphere_mul (A B : lorentz d) (u : PenroseSphere d) :
    lorentzSphere (A * B) u = lorentzSphere A (lorentzSphere B u) := by
  have hA := (lorentzScale_pos A (lorentzSphere B u)).ne'
  have hB := (lorentzScale_pos B u).ne'
  have hAB := (lorentzScale_pos (A * B) u).ne'
  refine nullVec_injective_smul
    (c := (lorentzScale (A * B) u)⁻¹ * (lorentzScale A (lorentzSphere B u) * lorentzScale B u)) ?_
  rw [nullVec_lorentzSphere, nullVec_lorentzSphere A, nullVec_lorentzSphere B, map_smul,
    smul_smul, smul_smul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  congr 1
  field_simp

private theorem cof_eigen_of_fixed {A : lorentz d} {u : PenroseSphere d}
    (h : lorentzSphere A u = u) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u := by
  have := nullVec_lorentzSphere A u
  rw [h] at this
  calc (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)
      = lorentzScale A u • ((lorentzScale A u)⁻¹ •
          (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) := by
        rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]
    _ = lorentzScale A u • nullVec u := by rw [← this]

private theorem cof_minkB_neg {u u' : PenroseSphere d} (h : u ≠ u') :
    minkB (nullVec u) (nullVec u') < 0 := by
  rw [minkB_nullVec_nullVec]
  have h0 : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h' => h (Subtype.ext h')
  have := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) 2
  linarith

private theorem cof_mul_eq_one {A : lorentz d} {u u' : PenroseSphere d} (hne : u ≠ u')
    {c c' : ℝ} (hc : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hc' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c' • nullVec u') : c * c' = 1 := by
  have h := lorentz.minkB_apply A.2 (nullVec u) (nullVec u')
  rw [hc, hc', minkB_smul_left, minkB_smul_right] at h
  have h0 := (cof_minkB_neg hne).ne
  have : (c * c' - 1) * minkB (nullVec u) (nullVec u') = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)

private theorem cof_fixed_unique {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = nullVec u') : u = u' := by
  by_contra h
  have e0 : minkB (nullVec u) (nullVec u) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have e0' : minkB (nullVec u') (nullVec u') = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hq : minkQ (nullVec u + nullVec u') < 0 := by
    rw [minkQ_eq_minkB, minkB_add_left, minkB_add_right, minkB_add_right, e0, e0',
      minkB_comm (nullVec u') (nullVec u)]
    linarith [cof_minkB_neg h]
  exact hne (isElliptic_of_fixed_timelike (fun v => lorentz.minkQ_apply A.2 v) hq
    (by rw [map_add, hu, hu']))

private theorem cof_same_eigen {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d} {c : ℝ}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c • nullVec u') : u = u' := by
  by_contra h
  have h1 := cof_mul_eq_one h hu hu'
  have hc := lorentz.eigen_pos_of_null A.2 (nullVec_ne_zero u) (minkQ_nullVec u) hu
  have hc1 : c = 1 := (mul_self_eq_one_iff.1 h1).resolve_right (by intro h'; linarith)
  rw [hc1, one_smul] at hu hu'
  exact h (cof_fixed_unique hne hu hu')

private theorem cof_eq_or_eq {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' x : PenroseSphere d}
    (huu' : u ≠ u') (hu : lorentzSphere A u = u) (hu' : lorentzSphere A u' = u')
    (hx : lorentzSphere A x = x) : x = u ∨ x = u' := by
  by_contra h
  push Not at h
  have e := cof_eigen_of_fixed hu
  have e' := cof_eigen_of_fixed hu'
  have ex := cof_eigen_of_fixed hx
  have h1 := cof_mul_eq_one h.1 ex e
  have h2 := cof_mul_eq_one h.2 ex e'
  have hs : lorentzScale A u = lorentzScale A u' :=
    mul_left_cancel₀ (lorentzScale_pos A x).ne' (h1.trans h2.symm)
  rw [hs] at e
  exact huu' (cof_same_eigen hne e e')

private theorem cof_not_isElliptic_conj {A z : lorentz d}
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ¬IsElliptic ((A * z * A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact fun h => hne ((classes_conj_iff A.2).1.1 h)

private theorem cof_conj_fixed {A z : lorentz d} {u : PenroseSphere d}
    (hu : lorentzSphere z u = u) :
    lorentzSphere (A * z * A⁻¹) (lorentzSphere A u) = lorentzSphere A u := by
  rw [cof_lorentzSphere_mul, cof_lorentzSphere_mul, ← cof_lorentzSphere_mul A⁻¹ A,
    inv_mul_cancel, cof_lorentzSphere_one, hu]

private theorem cof_exists_fixed {z : lorentz d}
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ u : PenroseSphere d, lorentzSphere z u = u := by
  rcases lorentz.exists_null_eigen_or_fixed_timelike z.2 with ⟨e, he0, hq, c, hc⟩ | ⟨v, hv, hzv⟩
  · obtain ⟨u, a, -, hu⟩ := cof_exists_nullVec_eq_smul he0 hq
    exact ⟨u, lorentzSphere_eq_of_eigen (c := c) (by rw [hu, map_smul, hc, smul_comm])⟩
  · exact absurd (isElliptic_of_fixed_timelike (fun w => lorentz.minkQ_apply z.2 w) hv hzv) hne

/-- A subspace holding a timelike vector is complementary to its `minkB`-orthogonal. -/
private theorem cof_isCompl {W : Submodule ℝ (Minkowski d)} {w₀ : Minkowski d} (hw₀ : w₀ ∈ W)
    (hq : minkQ w₀ < 0) : IsCompl W (minkOrth W) := by
  rw [minkOrth, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint minkForm_isRefl,
    Submodule.disjoint_def]
  intro v hvW hvO
  have hvO' : v ∈ minkOrth W := hvO
  by_contra hv0
  have hpos := minkQ_pos_of_orth_timelike hq ((mem_minkOrth.1 hvO') w₀ hw₀) hv0
  rw [minkQ_eq_minkB, (mem_minkOrth.1 hvO') v hvW] at hpos
  exact lt_irrefl _ hpos

/-- **Step (a)**: a null eigenvector of a non-elliptic `z` preserving a subspace `W` that holds a
timelike vector lies in `W`. -/
private theorem cof_null_eigen_mem {W : Submodule ℝ (Minkowski d)}
    (hWt : ∃ w ∈ W, minkQ w < 0) {z : lorentz d}
    (hzW : ∀ w ∈ W, (z : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ W)
    (hzW' : ∀ w ∈ W, ((z⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ W)
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) {e : Minkowski d} (he0 : e ≠ 0)
    (heq : minkQ e = 0) {c : ℝ} (hc : (z : Minkowski d ≃ₗ[ℝ] Minkowski d) e = c • e) : e ∈ W := by
  obtain ⟨w₀, hw₀, hq₀⟩ := hWt
  have hcompl := cof_isCompl hw₀ hq₀
  have hmem : e ∈ W ⊔ minkOrth W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hmem
  set Z := (z : Minkowski d ≃ₗ[ℝ] Minkowski d) with hZ
  -- `z` preserves `W^⊥`
  have hzw' : Z w' ∈ minkOrth W := by
    rw [mem_minkOrth]
    intro x hx
    have hx' : Z (((z⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) x) = x := by
      rw [hZ, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
      rfl
    rw [← hx', lorentz.minkB_apply z.2]
    exact (mem_minkOrth.1 hw') _ (hzW' x hx)
  -- the two components are eigenvectors
  have hsplit : Z w - c • w = c • w' - Z w' := by
    have : Z w + Z w' = c • w + c • w' := by rw [← map_add, hc, smul_add]
    rw [sub_eq_sub_iff_add_eq_add]; rw [this]; abel
  have hdisj := hcompl.disjoint
  have hzero : Z w - c • w = 0 := by
    rw [Submodule.disjoint_def] at hdisj
    refine hdisj _ (W.sub_mem (hzW w hw) (W.smul_mem c hw)) ?_
    rw [hsplit]; exact (minkOrth W).sub_mem ((minkOrth W).smul_mem c hw') hzw'
  have hZw : Z w = c • w := sub_eq_zero.1 hzero
  have hZw' : Z w' = c • w' := by
    have := hzero; rw [hsplit, sub_eq_zero] at this; exact this.symm
  by_cases hw'0 : w' = 0
  · rw [hw'0, add_zero]; exact hw
  exfalso
  have hpos : 0 < minkQ w' := minkQ_pos_of_orth_timelike hq₀ ((mem_minkOrth.1 hw') w₀ hw₀) hw'0
  have hcpos : 0 < c := lorentz.eigen_pos_of_null z.2 he0 heq hc
  have hc1 : c = 1 := by
    have h1 := lorentz.minkQ_apply z.2 w'
    rw [← hZ, hZw', minkQ_smul] at h1
    have : (c ^ 2 - 1) * minkQ w' = 0 := by linear_combination h1
    have h2 : c ^ 2 = 1 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hpos.ne')
    nlinarith
  have hB : minkB w w' = 0 := (mem_minkOrth.1 hw') w hw
  have hqw : minkQ w < 0 := by
    have := heq; rw [minkQ_add, hB] at this; linarith
  rw [hc1, one_smul] at hZw
  exact hne (isElliptic_of_fixed_timelike (fun v => lorentz.minkQ_apply z.2 v) hqw hZw)

/-- **The non-elliptic step of Prop 10.4** (l.3356–3358; the move of l.3381–3388): if `N` is
normalised by `G`, both preserve a subspace `W` holding a timelike vector, and the non-elliptic
`z ∈ N` commutes with every element of `N` on `W`, then `G` permutes the (one or two) fixed points
of `z` on `𝒮`, so the stabiliser `H` of one of them has index `≤ 2` in `G`. -/
theorem exists_finiteIndex_fix_of_commuteOn_nonElliptic {d : ℕ} {G N : Subgroup (lorentz d)}
    {W : Submodule ℝ (Minkowski d)} (hWt : ∃ w ∈ W, minkQ w < 0)
    (hGW : ∀ A ∈ G, ∀ w ∈ W, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ W)
    (hNW : ∀ B ∈ N, ∀ w ∈ W, (B : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ W)
    (hnorm : ∀ A ∈ G, ∀ B ∈ N, A * B * A⁻¹ ∈ N) {z : lorentz d} (hz : z ∈ N)
    (hzc : ∀ B ∈ N, ∀ w ∈ W,
      (B : Minkowski d ≃ₗ[ℝ] Minkowski d) ((z : Minkowski d ≃ₗ[ℝ] Minkowski d) w) =
        (z : Minkowski d ≃ₗ[ℝ] Minkowski d) ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) w))
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ H : Subgroup (lorentz d), H ≤ G ∧ H.relIndex G ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u := by
  obtain ⟨u, hu⟩ := cof_exists_fixed hne
  -- step (a): the null eigenlines of `z` lie in `W`
  have hfixW : ∀ x, lorentzSphere z x = x → nullVec x ∈ W := fun x hx =>
    cof_null_eigen_mem hWt (hNW z hz) (hNW _ (N.inv_mem hz)) hne (nullVec_ne_zero x)
      (minkQ_nullVec x) (cof_eigen_of_fixed hx)
  -- step (b): `G` preserves the fixed set of `z`
  have hpres : ∀ A ∈ G, ∀ x, lorentzSphere z x = x →
      lorentzSphere z (lorentzSphere A x) = lorentzSphere A x := by
    intro A hA x hx
    set z' : lorentz d := A * z * A⁻¹ with hz'
    have hz'N : z' ∈ N := hnorm A hA z hz
    have hz'ne : ¬IsElliptic (z' : Minkowski d ≃ₗ[ℝ] Minkowski d) := cof_not_isElliptic_conj hne
    set y := lorentzSphere A x with hy
    have hyfix : lorentzSphere z' y = y := cof_conj_fixed hx
    have e' := cof_eigen_of_fixed hyfix
    have hyW : nullVec y ∈ W := by
      rw [hy, nullVec_lorentzSphere]
      exact W.smul_mem _ (hGW A hA _ (hfixW x hx))
    set Z := (z : Minkowski d ≃ₗ[ℝ] Minkowski d) with hZ
    -- `z e'` is an eigenvector of `z'` with the same eigenvalue
    have hcomm := hzc z' hz'N _ hyW
    rw [e', map_smul] at hcomm
    have hZ0 : Z (nullVec y) ≠ 0 := fun h0 =>
      nullVec_ne_zero y (Z.injective (h0.trans (map_zero Z).symm))
    have hZq : minkQ (Z (nullVec y)) = 0 := by
      rw [hZ, lorentz.minkQ_apply z.2, minkQ_nullVec]
    obtain ⟨v, a, ha, hv⟩ := cof_exists_nullVec_eq_smul hZ0 hZq
    have hv' : (z' : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec v) =
        lorentzScale z' y • nullVec v := by
      rw [hv, map_smul, hcomm, smul_comm]
    have hvy : v = y := cof_same_eigen hz'ne hv' e'
    rw [hvy] at hv
    refine lorentzSphere_eq_of_eigen (c := a⁻¹) ?_
    conv_rhs => rw [hv]
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  let H : Subgroup (lorentz d) :=
    { carrier := {A | A ∈ G ∧ lorentzSphere A u = u}
      mul_mem' := fun {a b} ha hb =>
        ⟨G.mul_mem ha.1 hb.1, by rw [cof_lorentzSphere_mul, hb.2, ha.2]⟩
      one_mem' := ⟨G.one_mem, cof_lorentzSphere_one u⟩
      inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, by
        have := congrArg (lorentzSphere a⁻¹) ha.2
        rw [← cof_lorentzSphere_mul, inv_mul_cancel, cof_lorentzSphere_one] at this
        exact this.symm⟩ }
  have hmem : ∀ A, A ∈ H ↔ A ∈ G ∧ lorentzSphere A u = u := fun _ => Iff.rfl
  -- every element of `G` is in `H` or in `A₀ H`
  have key : ∃ A₀ ∈ G, ∀ A ∈ G, lorentzSphere A u = u ∨ lorentzSphere (A₀⁻¹ * A) u = u := by
    by_cases h : ∃ A₀ ∈ G, lorentzSphere A₀ u ≠ u
    · obtain ⟨A₀, hA₀, hne₀⟩ := h
      refine ⟨A₀, hA₀, fun A hA => ?_⟩
      rcases cof_eq_or_eq hne (Ne.symm hne₀) hu (hpres A₀ hA₀ u hu) (hpres A hA u hu) with
        h1 | h1
      · exact Or.inl h1
      · right
        rw [cof_lorentzSphere_mul, h1, ← cof_lorentzSphere_mul, inv_mul_cancel,
          cof_lorentzSphere_one]
    · push Not at h
      exact ⟨1, G.one_mem, fun A hA => Or.inl (h A hA)⟩
  obtain ⟨A₀, hA₀, hkey⟩ := key
  refine ⟨H, fun A hA => hA.1, ?_, u, fun A hA => hA.2⟩
  show (H.subgroupOf G).index ≠ 0
  rw [Subgroup.index_ne_zero_iff_finite]
  refine Finite.of_surjective (fun b : Bool => if b then ((⟨A₀, hA₀⟩ : G) : G ⧸ H.subgroupOf G)
    else ((1 : G) : G ⧸ H.subgroupOf G)) ?_
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rcases hkey a a.2 with h1 | h1
  · refine ⟨false, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hmem]
    exact ⟨by simp, by simpa using h1⟩
  · refine ⟨true, ?_⟩
    simp only [ite_true]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hmem]
    exact ⟨G.mul_mem (G.inv_mem hA₀) a.2, by simpa using h1⟩

end Causal.Flat.Lox
