import CausalScaffold.Flat.Externals

/-!
# A central non-elliptic element gives a fixed isotropic direction of a finite-index subgroup

Centre step of Barbot's Prop 10.4 and Prop 10.5 (`bprop:U_timelike`, `bprop:LU_discrete`,
`GHFspace.tex` l.3346–3388), served to `bprop_U_timelike` and `bprop_LU_discrete`
(`Flat/Loxodromic.lean`): if a group `N ≤ SO₀(1, d)` normalised by `G` has a central non-elliptic
element `z`, a finite-index subgroup of `G` fixes a point of `𝒮`. **No label is marked**: this is
one step of two proofs, not a statement of the paper.

* `bprop:LU_discrete`, `GHFspace.tex:3381–3388`, partial (the centre step only; **no `sorry`**):
  `exists_finiteIndex_fix_of_central_nonElliptic`.
* `bprop:U_timelike`, `GHFspace.tex:3356–3358`, partial (the non-elliptic branch of the folklore,
  in its true form; **no `sorry`**): the same theorem.

> In particular, if it
> is not trivial, its center contains a parabolic or hyperbolic
> element. If it contains a parabolic element $\gamma_{0}$, the unique
> isotropic direction of $\gamma_{0}$ is $L_{U}(\Gamma)$-invariant, and
> thus $L(\Gamma)$-invariant. Contradiction.
>
> If the center contains a hyperbolic element $\gamma_{0}$, then the
> two isotropic fixed points of $L(\gamma_{0})$
> has to be exchanged by every element of $L(\Gamma)$. Contradiction. (l.3380–3388)

> Now, an abelian subgroup
> of $SO_{0}(1,n-1)$ fixes a pair of isotropic directions, except
> if it consists only one elliptic elements fixing one and
> only one timelike vector $v_{0}$. (l.3356–3359)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `γ₀` central in the (nilpotent) identity component | ⚠ weakened: central in any `N` (`hz`, `hzc`); nilpotency unused |
| `N` normalised by `L(Γ)` | ✓ carried (`hnorm`; `N ≤ G` not required) |
| `γ₀` parabolic or hyperbolic | ✓ carried as `¬IsElliptic` (`hne`; trichotomy) |
| conclusion "invariant / exchanged" | ✓ as: a subgroup of index `≤ 2` fixes a point of `𝒮` |

## SCOPE (disclosed)

Only the centre step is proved. That the centre of the identity component of the closure of
`L_U(Γ)` contains a non-elliptic element (l.3372–3380) is not treated here.

Proof: `F(A) = {u | [A]u = u}` is the set of null eigenlines of `A`. For non-elliptic `z`: two
points of `F(z)` with distinct directions have eigenvalues of product `1` (`minkB` is preserved
and nonzero between distinct null directions); two with the same eigenvalue coincide (equal to
`1` they would give a fixed timelike sum, making `z` elliptic). Hence `F(z)` is nonempty with at
most two points. An element commuting with `z` maps each eigenline into the eigenspace of the
same eigenvalue, so fixes `F(z)` pointwise; `A z A⁻¹ ∈ N` is non-elliptic and commutes with `z`,
so `[A]` maps `F(z)` into `F(A z A⁻¹) ⊆ F(z)`: `G` permutes a set of at most two
points, and the stabiliser of `u ∈ F(z)` has index `≤ 2` (cosets of `1` and of one `A₀`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (`/tmp/loxplan/LU1_CentralFix.lean`); `cfx_exists_nullVec_eq_smul` reproves
`exists_nullVec_eq_smul` (`Flat/Loxodromic.lean`), which this module may not import. All
auxiliaries are `private` (no public-name collision with the other `Flat/Lox/` files).
-/

namespace Causal.Flat.Lox
open Set
variable {d : ℕ}

/-- A nonzero null vector spans the null direction of a point of `𝒮` (a copy of
`Loxodromic.exists_nullVec_eq_smul`). -/
private theorem cfx_exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
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

private theorem cfx_lorentzSphere_one (u : PenroseSphere d) :
    lorentzSphere (1 : lorentz d) u = u :=
  lorentzSphere_eq_of_eigen (c := 1) (by simp)

/-- The action on `𝒮` is an action: `[A B] = [A] ∘ [B]`. -/
private theorem cfx_lorentzSphere_mul (A B : lorentz d) (u : PenroseSphere d) :
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

/-- A fixed point of `[A]` is a null eigenline of `A`, with eigenvalue `lorentzScale A u`. -/
private theorem cfx_eigen_of_fixed {A : lorentz d} {u : PenroseSphere d}
    (h : lorentzSphere A u = u) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u := by
  have := nullVec_lorentzSphere A u
  rw [h] at this
  calc (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)
      = lorentzScale A u • ((lorentzScale A u)⁻¹ •
          (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) := by
        rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]
    _ = lorentzScale A u • nullVec u := by rw [← this]

/-- Distinct points of `𝒮` have non-orthogonal null vectors: `⟨(1,u) | (1,u')⟩ < 0`. -/
private theorem cfx_minkB_neg {u u' : PenroseSphere d} (h : u ≠ u') :
    minkB (nullVec u) (nullVec u') < 0 := by
  rw [minkB_nullVec_nullVec]
  have h0 : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h' => h (Subtype.ext h')
  have := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) 2
  linarith

/-- Eigenvalues on two distinct null eigenlines of a Lorentz map multiply to `1`. -/
private theorem cfx_mul_eq_one {A : lorentz d} {u u' : PenroseSphere d} (hne : u ≠ u')
    {c c' : ℝ} (hc : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hc' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c' • nullVec u') : c * c' = 1 := by
  have h := lorentz.minkB_apply A.2 (nullVec u) (nullVec u')
  rw [hc, hc', minkB_smul_left, minkB_smul_right] at h
  have h0 := (cfx_minkB_neg hne).ne
  have : (c * c' - 1) * minkB (nullVec u) (nullVec u') = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h0)

/-- A non-elliptic Lorentz map fixes at most one null direction pointwise: two fixed null
vectors in distinct directions would sum to a fixed timelike vector. -/
private theorem cfx_fixed_unique {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = nullVec u') : u = u' := by
  by_contra h
  have e0 : minkB (nullVec u) (nullVec u) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have e0' : minkB (nullVec u') (nullVec u') = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
  have hq : minkQ (nullVec u + nullVec u') < 0 := by
    rw [minkQ_eq_minkB, minkB_add_left, minkB_add_right, minkB_add_right, e0, e0',
      minkB_comm (nullVec u') (nullVec u)]
    linarith [cfx_minkB_neg h]
  exact hne (isElliptic_of_fixed_timelike (fun v => lorentz.minkQ_apply A.2 v) hq
    (by rw [map_add, hu, hu']))

/-- For non-elliptic `A`, two null eigenlines with the same eigenvalue coincide. -/
private theorem cfx_same_eigen {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' : PenroseSphere d} {c : ℝ}
    (hu : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = c • nullVec u)
    (hu' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') = c • nullVec u') : u = u' := by
  by_contra h
  have h1 := cfx_mul_eq_one h hu hu'
  have hc := lorentz.eigen_pos_of_null A.2 (nullVec_ne_zero u) (minkQ_nullVec u) hu
  have hc1 : c = 1 := (mul_self_eq_one_iff.1 h1).resolve_right (by intro h'; linarith)
  rw [hc1, one_smul] at hu hu'
  exact h (cfx_fixed_unique hne hu hu')

/-- **At most two fixed points**: a non-elliptic `A` has no three distinct fixed points on `𝒮`. -/
private theorem cfx_eq_or_eq {A : lorentz d}
    (hne : ¬IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) {u u' x : PenroseSphere d}
    (huu' : u ≠ u') (hu : lorentzSphere A u = u) (hu' : lorentzSphere A u' = u')
    (hx : lorentzSphere A x = x) : x = u ∨ x = u' := by
  by_contra h
  push Not at h
  have e := cfx_eigen_of_fixed hu
  have e' := cfx_eigen_of_fixed hu'
  have ex := cfx_eigen_of_fixed hx
  have h1 := cfx_mul_eq_one h.1 ex e
  have h2 := cfx_mul_eq_one h.2 ex e'
  have hs : lorentzScale A u = lorentzScale A u' :=
    mul_left_cancel₀ (lorentzScale_pos A x).ne' (h1.trans h2.symm)
  rw [hs] at e
  exact huu' (cfx_same_eigen hne e e')

/-- An element commuting with a non-elliptic `z` fixes every fixed point of `z` on `𝒮`: it maps
each null eigenline of `z` to a null eigenline of the same eigenvalue. -/
private theorem cfx_fixed_of_commute {z w : lorentz d}
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) (hc : w * z = z * w)
    {u : PenroseSphere d} (hu : lorentzSphere z u = u) : lorentzSphere w u = u := by
  have e := cfx_eigen_of_fixed hu
  have e2 : (z : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec (lorentzSphere w u)) =
      lorentzScale z u • nullVec (lorentzSphere w u) := by
    rw [nullVec_lorentzSphere, map_smul, smul_comm (lorentzScale z u)]
    congr 1
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← hc, Subgroup.coe_mul,
      LinearEquiv.mul_apply, e, map_smul]
  exact cfx_same_eigen hne e2 e

private theorem cfx_not_isElliptic_conj {A z : lorentz d}
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ¬IsElliptic ((A * z * A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact fun h => hne ((classes_conj_iff A.2).1.1 h)

/-- `[A]` carries the fixed points of `z` to those of `A z A⁻¹`. -/
private theorem cfx_conj_fixed {A z : lorentz d} {u : PenroseSphere d}
    (hu : lorentzSphere z u = u) :
    lorentzSphere (A * z * A⁻¹) (lorentzSphere A u) = lorentzSphere A u := by
  rw [cfx_lorentzSphere_mul, cfx_lorentzSphere_mul, ← cfx_lorentzSphere_mul A⁻¹ A,
    inv_mul_cancel, cfx_lorentzSphere_one, hu]

/-- A non-elliptic element of `SO₀(1, d)` fixes a point of `𝒮` (it has a null eigenvector, a
fixed timelike vector making it elliptic). -/
private theorem cfx_exists_fixed {z : lorentz d}
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ u : PenroseSphere d, lorentzSphere z u = u := by
  rcases lorentz.exists_null_eigen_or_fixed_timelike z.2 with ⟨e, he0, hq, c, hc⟩ | ⟨v, hv, hzv⟩
  · obtain ⟨u, a, -, hu⟩ := cfx_exists_nullVec_eq_smul he0 hq
    exact ⟨u, lorentzSphere_eq_of_eigen (c := c) (by rw [hu, map_smul, hc, smul_comm])⟩
  · exact absurd (isElliptic_of_fixed_timelike (fun w => lorentz.minkQ_apply z.2 w) hv hzv) hne

/-- **The centre step of Prop 10.4/10.5** (l.3356–3358, l.3381–3388): if `N` is normalised by
`G` and has a central non-elliptic element `z`, then `G` permutes the (one or two) fixed points of
`z` on `𝒮`, so the stabiliser `H` of one of them has index `≤ 2` in `G`. -/
theorem exists_finiteIndex_fix_of_central_nonElliptic {G N : Subgroup (lorentz d)}
    (hnorm : ∀ A ∈ G, ∀ B ∈ N, A * B * A⁻¹ ∈ N) {z : lorentz d} (hz : z ∈ N)
    (hzc : ∀ B ∈ N, B * z = z * B)
    (hne : ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ H : Subgroup (lorentz d), H ≤ G ∧ H.relIndex G ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u := by
  obtain ⟨u, hu⟩ := cfx_exists_fixed hne
  -- `G` preserves the fixed set of `z`
  have hpres : ∀ A ∈ G, ∀ x, lorentzSphere z x = x →
      lorentzSphere z (lorentzSphere A x) = lorentzSphere A x := fun A hA x hx =>
    cfx_fixed_of_commute (cfx_not_isElliptic_conj hne) (hzc _ (hnorm A hA z hz)).symm
      (cfx_conj_fixed hx)
  let H : Subgroup (lorentz d) :=
    { carrier := {A | A ∈ G ∧ lorentzSphere A u = u}
      mul_mem' := fun {a b} ha hb =>
        ⟨G.mul_mem ha.1 hb.1, by rw [cfx_lorentzSphere_mul, hb.2, ha.2]⟩
      one_mem' := ⟨G.one_mem, cfx_lorentzSphere_one u⟩
      inv_mem' := fun {a} ha => ⟨G.inv_mem ha.1, by
        have := congrArg (lorentzSphere a⁻¹) ha.2
        rw [← cfx_lorentzSphere_mul, inv_mul_cancel, cfx_lorentzSphere_one] at this
        exact this.symm⟩ }
  have hmem : ∀ A, A ∈ H ↔ A ∈ G ∧ lorentzSphere A u = u := fun _ => Iff.rfl
  -- every element of `G` is in `H` or in `A₀ H`
  have key : ∃ A₀ ∈ G, ∀ A ∈ G, lorentzSphere A u = u ∨ lorentzSphere (A₀⁻¹ * A) u = u := by
    by_cases h : ∃ A₀ ∈ G, lorentzSphere A₀ u ≠ u
    · obtain ⟨A₀, hA₀, hne₀⟩ := h
      refine ⟨A₀, hA₀, fun A hA => ?_⟩
      rcases cfx_eq_or_eq hne (Ne.symm hne₀) hu (hpres A₀ hA₀ u hu) (hpres A hA u hu) with
        h1 | h1
      · exact Or.inl h1
      · right
        rw [cfx_lorentzSphere_mul, h1, ← cfx_lorentzSphere_mul, inv_mul_cancel,
          cfx_lorentzSphere_one]
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
