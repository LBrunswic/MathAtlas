import GX.Spherical.TroyanovTriangle

/-!
# Troyanov's theorem: a regular point is a cone point of angle `2π`, so the angles `2π` drop out

Target `T-gx-troyanov-two-pi` (`roadmap/roadmap.toml`; DEC-136, Troyanov's theorem proved, not
assumed). `papers/gx`, 0 `sorry`, standard axioms only. **No label is marked here.**

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial, not marked: the
  row needs Troyanov's theorem for every `s ≥ 3` and the Thurston suspension facts
  (`GX.thurstonSuspensionFacts`), both outside this module. Here the cited theorem (`MR1005085`),
  in the shape of `GX.TroyanovTheorem` (`GXScaffold.Spherical.TroyanovAngles`, restated inline),
  is reduced to angles all `≠ 2π`: **`GX.troyanovTheorem_of_ne_two_pi`**; with
  `GX.troyanovTheorem_three`, to `s ≥ 4` angles all `≠ 2π`:
  **`GX.troyanovTheorem_of_four_le_of_ne_two_pi`**, and the reduction is an equivalence,
  `GX.troyanovTheorem_iff_four_le_ne_two_pi`.
* **A regular point is a cone point of angle `2π`**: `GX.IsConePoint.of_mem_reg` (every regular
  point of a singular `(SO(3), 𝕊²)`-manifold has an `X_{2π}`-chart onto a connected open
  neighbourhood of the apex of `C_{2π}`), the converse of `GX.IsConePoint.mem_reg`; together
  `GX.isConePoint_iff_mem_reg`. Its tools: `GX.isAEMorphism_of_chart_eq` (a map out of an open
  subset reading a chart of the source as a translate of a chart of the target is an a.e.
  morphism) and `GX.exists_specialOrth_smul_eq` (`SO(V)` is transitive on the unit sphere,
  `dim V ≥ 2`: two reflections).
* **A cone point of angle `2π` can be added or removed**: `GX.IsConeSphere.insertNth` (any point
  off the cone points, `GX.IsConeSphere.exists_notMem_range`), `GX.IsConeSphere.removeNth`;
  Troyanov's condition survives the deletion of an angle `2π`,
  `GX.TroyanovAngleCondition.removeNth` (with
  `GX.TroyanovAngleCondition.three_le_card_filter_ne_two_pi`: at least three angles are `≠ 2π`);
  for `s = 3` every angle is `< 2π`, `GX.TroyanovAngleCondition.three_lt_two_pi`.

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. We know from
> Troyanov \cite{MR1005085}  that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> (l.1930)

## The argument

A regular point `x` lies in a chart `e` of `M`; the apex of `C_{2π}` is regular
(`GX.SphCone.sing_eq_empty`), so it lies in a chart `a` of `C_{2π}`; a rotation `g` sends `e(x)`
to `a(apex)`. Then `a⁻¹ ∘ g ∘ e`, restricted to the preimage of the connected component of the
apex in its target, is an `X_{2π}`-chart at `x`. An angle `θ_k = 2π` contributes `0` to
`∑ (θ_i − 2π)` and leaves the bounds `χ' ≤ θ_j`; the cone sphere of the other angles is `𝕊²` as a
space, infinite, so it has a point `q` off its cone points, regular since its singular points are
cone points; `q` is the cone point of angle `2π`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s ≥ 3` conical singularities of angles `θ_i` (l.1930) | ✓ `GX.IsConeSphere`; SCOPE (b) |
| Troyanov's condition (l.1930) | ✓ carried, verbatim (`GX.TroyanovAngleCondition`, DEC-69's) |
| Troyanov's theorem (`MR1005085`), cited | reduced: to `s ≥ 4`, all `θ_i ≠ 2π` |

## SCOPE (disclosed)

* **(a)** Reductions only: no label assertion is proved here beyond them. What remains of
  Troyanov's theorem is `s ≥ 4` angles all `≠ 2π` (`T-gx-troyanov-polygon` for all `< 2π`,
  `T-gx-troyanov` for some `> 2π`); the row also needs `GX.thurstonSuspensionFacts`.
* **(b)** An angle `θ_i = 2π` is a marked regular point (the library's reading,
  `GX.Spherical.ConeSurface` SCOPE (c)); it is now exactly that: a point is a cone point of angle
  `2π` iff it is regular (`isConePoint_iff_mem_reg`). The `X_{2π}`-chart is `def:atlas`'s
  (`GX.IsConePoint`): onto a connected open neighbourhood of the apex of `C_{2π}`, not onto all
  of `C_{2π}`. `IsConePoint.of_mem_reg` assumes nothing of `M` beyond its singular
  `(SO(3), 𝕊²)`-structure.
* **(c)** `GX.TroyanovTheorem` is restated inline (its body), as in
  `GX.Spherical.TroyanovTriangle`: the scaffold `TroyanovAngles` is not imported.
  `TroyanovAngleCondition.three_le_card_filter_ne_two_pi` is that module's
  `TroyanovAngleCondition.three_le_card_ne_two_pi`, re-proved under its own name.
* **(d)** `M : Type`, as in `GX.TroyanovTheorem`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.TroyanovTriangle` (`troyanovTheorem_three`, `TroyanovAngleCondition.three_half`),
`GX.Spherical.ConeSurface` (`SphCone`, `IsConePoint`, `IsConeSphere`), `GX.SingularII.Models`
(`isAEMorphism_of_val_comp`), `GX.SingularII.Tame` (open subsets), mathlib's
`Submodule.reflection`.
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### A chart read as a translate of a chart is an a.e. morphism -/

section ChartRead

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]
  {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N]

/-- **A map out of an open subset that reads, on all of it, a chart of the source as a translate
of a chart of the target is an a.e. `(G,X)`-morphism**: if `U ⊆ e.source` for a chart `e` of `M`,
`f : U → N` is continuous with values in `a.source` for a chart `a` of `N`, and `a ∘ f = g • e` on
`U`, then `f` is an a.e. `(G,X)`-morphism (indeed regular everywhere). -/
theorem isAEMorphism_of_chart_eq (U : Opens M) {f : U → N} (hf : Continuous f)
    {e : OpenPartialHomeomorph M X} (he : e ∈ aeAtlas G X M)
    {a : OpenPartialHomeomorph N X} (ha : a ∈ aeAtlas G X N) (g : G)
    (hU : (U : Set M) ⊆ e.source) (hfa : ∀ u, f u ∈ a.source)
    (heq : ∀ u : U, a (f u) = g • e u) : IsAEMorphism G X f := by
  have hBU := isMaximalAEAtlas_aeAtlas G X U
  have hBM := isMaximalAEAtlas_aeAtlas G X M
  have hBN := isMaximalAEAtlas_aeAtlas G X N
  have hregU : ∀ u : U, u ∈ Reg G X U := fun u => by
    rw [reg_opensSingular]; exact mem_support.2 ⟨e, he, hU u.2⟩
  have hvalreg := isRegularOn_regLocusOf (G := G) (aeAtlas G X U) (aeAtlas G X M)
    (Subtype.val : U → M)
  have hvaleq := IsAEMorphismOf.regLocusOf_eq hBU.1 hBM.1
    (isAEMorphism_opensSingular_val (G := G) (X := X) U)
  refine (isAEMorphismOf_iff hBN.1).2 ⟨hf, univ, isPortly_univ,
    IsRegularOn.of_exists hBU.1.1 hBN.1.1 isOpen_univ (fun u _ => hregU u)
      (fun u _ => mem_support.2 ⟨a, ha, hfa u⟩) hf.continuousOn fun u _ => ?_⟩
  obtain ⟨b, hb, hub⟩ := mem_support.1 (hregU u)
  have huR : u ∈ regLocusOf G (aeAtlas G X U) (aeAtlas G X M) Subtype.val := by
    rw [hvaleq]; exact ⟨hregU u, mem_support.2 ⟨e, he, hU u.2⟩⟩
  obtain ⟨k, hk⟩ := hvalreg.exists_smul_eq u huR b hb e he hub (hU u.2)
  refine ⟨b, hb, a, ha, hub, hfa u, g * k, ?_⟩
  filter_upwards [hk] with y hy
  rw [heq, mul_smul, ← hy]

end ChartRead

/-! ### `SO(V)` is transitive on the unit sphere -/

section Transitive

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The reflection in the hyperplane orthogonal to `u ≠ 0` has determinant `−1`. -/
theorem det_reflection_orthogonal_singleton {u : V} (hu : u ≠ 0) :
    LinearMap.det (((ℝ ∙ u)ᗮ.reflection.toLinearEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) = -1 := by
  have := Submodule.det_reflection (𝕜 := ℝ) (ℝ ∙ u)ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hu, pow_one] at this
  exact this

/-- **`SO(V)` acts transitively on the unit sphere** of a finite-dimensional real inner product
space of dimension `≥ 2`: the product of the reflection exchanging `y` and `z` and of a reflection
fixing `z`. -/
theorem exists_specialOrth_smul_eq (hdim : 2 ≤ Module.finrank ℝ V) (y z : RaySphere V) :
    ∃ g : SpecialOrth V, g • y = z := by
  by_cases hyz : (y : V) = z
  · exact ⟨1, by rw [one_smul]; exact Subtype.ext hyz⟩
  have hv : (y : V) - z ≠ 0 := sub_ne_zero.2 hyz
  have hz : (z : V) ≠ 0 := by
    intro h0; have := norm_raySphere z; rw [h0, norm_zero] at this; norm_num at this
  -- a nonzero `w ⊥ z`
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ (ℝ ∙ (z : V))ᗮ, w ≠ 0 := by
    refine (Submodule.ne_bot_iff _).1 fun hbot => ?_
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ (z : V))
    rw [hbot, finrank_bot, finrank_span_singleton hz] at h
    omega
  set R₁ := (ℝ ∙ ((y : V) - z))ᗮ.reflection
  set R₂ := (ℝ ∙ w)ᗮ.reflection
  have h₁ : R₁ y = z := Submodule.reflection_sub (by rw [norm_raySphere, norm_raySphere])
  have h₂ : R₂ z = z := by
    refine Submodule.reflection_mem_subspace_eq_self ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    rw [real_inner_comm]; exact hw
  set L : V ≃ₗᵢ[ℝ] V := R₁.trans R₂
  have hL : L ∈ SpecialOrth V := by
    rw [mem_specialOrth]
    have : ((L.toLinearEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) =
        ((R₂.toLinearEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) ∘ₗ
          ((R₁.toLinearEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) := by
      ext v; rfl
    rw [this, LinearMap.det_comp, det_reflection_orthogonal_singleton hw0,
      det_reflection_orthogonal_singleton hv]
    norm_num
  refine ⟨⟨L, hL⟩, Subtype.ext ?_⟩
  rw [coe_specialOrth_smul]
  show R₂ (R₁ y) = z
  rw [h₁, h₂]

end Transitive

/-! ### A regular point is a cone point of angle `2π` -/

section TwoPi

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- **Every regular point of a singular `(SO(3), 𝕊²)`-manifold is a cone point of angle `2π`**:
it has an `X_{2π}`-chart onto a connected open neighbourhood of the apex of `C_{2π}`. The converse
of `GX.IsConePoint.mem_reg`. -/
theorem IsConePoint.of_mem_reg {θ : ConeAngle} (hθ : θ.1 = 2 * π) {x : M}
    (hx : x ∈ Reg SO3 Sph2 M) : IsConePoint θ x := by
  obtain ⟨e, he, hxe⟩ := mem_support.1 hx
  -- the apex of `C_{2π}` is regular: a chart `a` of `C_{2π}` at the apex
  have hapex : SphCone.apex θ ∈ Reg SO3 Sph2 (SphCone θ) := by
    by_contra h
    exact (SphCone.apex_mem_sing_iff θ).1 h hθ
  obtain ⟨a, ha, hapa⟩ := mem_support.1 hapex
  -- a rotation `g` sending `e x` to `a (apex)`
  obtain ⟨g, hg⟩ := exists_specialOrth_smul_eq (V := Euc3) (by rw [finrank_euc3]; norm_num)
    (e x) (a (SphCone.apex θ))
  -- `Ψ = a⁻¹ ∘ g ∘ e`, sending `x` to the apex
  set Ψ : OpenPartialHomeomorph M (SphCone θ) :=
    (e.transHomeomorph (Homeomorph.smul g)).trans a.symm
  have hΨapp : ∀ y, Ψ y = a.symm (g • e y) := fun y => rfl
  have hxΨ : x ∈ Ψ.source :=
    ⟨hxe, show g • e x ∈ a.target by rw [hg]; exact a.map_source hapa⟩
  have hΨx : Ψ x = SphCone.apex θ := by rw [hΨapp, hg, a.left_inv hapa]
  have hapT : SphCone.apex θ ∈ Ψ.target := hΨx ▸ Ψ.map_source hxΨ
  -- restricted to the connected component of the apex in its target
  set V₀ := connectedComponentIn Ψ.target (SphCone.apex θ)
  have hV₀o : IsOpen V₀ := Ψ.open_target.connectedComponentIn
  have hV₀t : V₀ ⊆ Ψ.target := connectedComponentIn_subset _ _
  set Ψ' := (Ψ.symm.restrOpen V₀ hV₀o).symm
  have htgt : Ψ'.target = V₀ := inter_eq_right.2 hV₀t
  refine ⟨{ U := ⟨Ψ'.source, Ψ'.open_source⟩
            V := ⟨Ψ'.target, Ψ'.open_target⟩
            φ := Ψ'.toHomeomorphSourceTarget
            mem := ⟨hxΨ, show Ψ x ∈ V₀ by rw [hΨx]; exact mem_connectedComponentIn hapT⟩
            isConnected_V := ?_
            isAEMorphism := ?_
            mem_S := ?_ }⟩
  · show IsConnected Ψ'.target
    rw [htgt]; exact isConnected_connectedComponentIn_iff.2 hapT
  · apply isAEMorphism_of_val_comp
    refine isAEMorphism_of_chart_eq _
      (continuous_subtype_val.comp Ψ'.toHomeomorphSourceTarget.continuous) he ha g
      (fun y hy => hy.1.1) (fun u => ?_) (fun u => ?_)
    · show a.symm (g • e u) ∈ a.source
      exact a.map_target u.2.1.2
    · show a (a.symm (g • e u)) = g • e u
      exact a.right_inv u.2.1.2
  · show Ψ x ∈ sphConeS θ
    rw [hΨx]; exact mem_singleton _

/-- **A point is a cone point of angle `2π` iff it is regular.** -/
theorem isConePoint_iff_mem_reg {θ : ConeAngle} (hθ : θ.1 = 2 * π) {x : M} :
    IsConePoint θ x ↔ x ∈ Reg SO3 Sph2 M :=
  ⟨fun h => h.mem_reg hθ, IsConePoint.of_mem_reg hθ⟩

end TwoPi

/-! ### Adding and removing a cone point of angle `2π` -/

section AddPoint

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- A cone sphere is infinite, so it has a point off any finite family. -/
theorem IsConeSphere.exists_notMem_range {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M}
    (h : IsConeSphere M θ p) : ∃ q, q ∉ range p := by
  haveI : Infinite M := Infinite.of_injective _
    (h.homeomorphic.some.symm.injective.comp (isOpenEmbedding_stereoInv (W := ℂ)).injective)
  exact (Set.finite_range p).infinite_compl.nonempty

/-- **A cone sphere with one more cone point, of angle `2π`**: if `θ_k = 2π` and `M` is a cone
sphere with the cone points `p` of the angles `θ` with `θ_k` removed, then for any `q` off the
range of `p`, `M` is a cone sphere with the cone points `p` with `q` inserted at `k`, of the
angles `θ`. -/
theorem IsConeSphere.insertNth {n : ℕ} {θ : Fin (n + 1) → ℝ} {k : Fin (n + 1)} (hk : θ k = 2 * π)
    {p : Fin n → M} (h : IsConeSphere M (k.removeNth θ) p) {q : M} (hq : q ∉ range p) :
    IsConeSphere M θ (Fin.insertNth (α := fun _ => M) k q p) := by
  have hqreg : q ∈ Reg SO3 Sph2 M := by
    by_contra hqs
    exact hq (h.sing_subset hqs)
  have hpos : ∀ i, 0 < θ i := fun i => by
    rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨i', rfl⟩
    · rw [hk]; positivity
    · exact h.pos i'
  refine ⟨h.homeomorphic, fun i j hij => ?_, hpos, fun i => ?_, fun x hx => ?_⟩
  · rcases Fin.eq_self_or_eq_succAbove k i with hi | ⟨i', hi⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove k j with hj | ⟨j', hj⟩ <;>
      rw [hi, hj] at hij ⊢
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hij
      exact absurd ⟨j', hij.symm⟩ hq
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hij
      exact absurd ⟨i', hij⟩ hq
    · simp only [Fin.insertNth_apply_succAbove] at hij
      rw [h.injective hij]
  · rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨i', rfl⟩
    · rw [Fin.insertNth_apply_same]
      exact IsConePoint.of_mem_reg hk hqreg
    · rw [Fin.insertNth_apply_succAbove]
      exact h.isConePoint i'
  · obtain ⟨i, rfl⟩ := h.sing_subset hx
    exact ⟨k.succAbove i, Fin.insertNth_apply_succAbove _ _ _ _⟩

/-- **Removing a cone point of angle `2π`** leaves a cone sphere. -/
theorem IsConeSphere.removeNth {n : ℕ} {θ : Fin (n + 1) → ℝ} {k : Fin (n + 1)} (hk : θ k = 2 * π)
    {p : Fin (n + 1) → M} (h : IsConeSphere M θ p) :
    IsConeSphere M (k.removeNth θ) (k.removeNth p) := by
  refine ⟨h.homeomorphic, h.injective.comp Fin.succAbove_right_injective,
    fun i => h.pos _, fun i => h.isConePoint _, fun x hx => ?_⟩
  obtain ⟨i, rfl⟩ := h.sing_subset hx
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨i', rfl⟩
  · exact absurd ((h.isConePoint i).mem_reg hk) hx
  · exact ⟨i', rfl⟩

end AddPoint

/-! ### Troyanov's condition without an angle `2π` -/

section Angles

/-- **Troyanov's condition forces at least three angles `≠ 2π`** (a copy, under its own name, of
`GX.TroyanovAngleCondition.three_le_card_ne_two_pi` of the scaffold `TroyanovAngles`, which this
module does not import). -/
theorem TroyanovAngleCondition.three_le_card_filter_ne_two_pi {s : ℕ} {θ : Fin s → ℝ}
    (h : TroyanovAngleCondition θ) : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card := by
  set F := Finset.univ.filter fun i => θ i ≠ 2 * π
  have hsum : ∑ i, (θ i - 2 * π) = ∑ i ∈ F, (θ i - 2 * π) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ i ≠ 2 * π)]
    have : ∑ i ∈ Finset.univ.filter (fun i => ¬ θ i ≠ 2 * π), (θ i - 2 * π) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter, not_not] at hi; rw [hi.2, sub_self]
    rw [this, add_zero]
  have hχ := h.2.2.2
  have hpos := h.pos
  rw [hsum] at hχ
  by_contra hlt
  rw [not_le] at hlt
  interval_cases hc : F.card
  · rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.sum_empty, zero_add] at hχ
    have hs : 0 < s := by have := h.1; omega
    have h0 : θ ⟨0, hs⟩ = 2 * π := by
      by_contra hne
      have : (⟨0, hs⟩ : Fin s) ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
      rw [hc] at this; exact Finset.notMem_empty _ this
    have := hχ ⟨0, hs⟩
    rw [h0] at this
    linarith [Real.pi_pos]
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    rw [ha, Finset.sum_singleton] at hχ
    linarith [hχ a, Real.pi_pos]
  · obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hc
    rw [hF, Finset.sum_pair hab] at hχ
    linarith [hχ a, hpos b]

/-- **Deleting an angle `2π` keeps Troyanov's condition**: its term `θ_k − 2π` vanishes, the bounds
`χ' ≤ θ_j` for `j ≠ k` stay, and at least three angles `≠ 2π` remain, so `s − 1 ≥ 3`. -/
theorem TroyanovAngleCondition.removeNth {n : ℕ} {θ : Fin (n + 1) → ℝ}
    (h : TroyanovAngleCondition θ) {k : Fin (n + 1)} (hk : θ k = 2 * π) :
    TroyanovAngleCondition (k.removeNth θ) := by
  have hsum : ∑ i, (θ i - 2 * π) = ∑ i, (k.removeNth θ i - 2 * π) := by
    rw [Fin.sum_univ_succAbove _ k, hk, sub_self, zero_add]; rfl
  have hcard : (Finset.univ.filter fun i => θ i ≠ 2 * π) ⊆ Finset.univ.erase k := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_erase.2 ⟨fun e => hi.2 (e ▸ hk), Finset.mem_univ _⟩
  have h3 := (h.three_le_card_filter_ne_two_pi).trans (Finset.card_le_card hcard)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h3
  refine ⟨by omega, hsum ▸ h.2.1, hsum ▸ h.2.2.1, fun j => ?_⟩
  rw [← hsum]
  exact h.2.2.2 (k.succAbove j)

/-- For `s = 3`, Troyanov's condition forces every angle below `2π` (`θ_i / 2 < π`,
`GX.TroyanovAngleCondition.three_half`). -/
theorem TroyanovAngleCondition.three_lt_two_pi {θ : Fin 3 → ℝ} (h : TroyanovAngleCondition θ)
    (i : Fin 3) : θ i < 2 * π := by
  have := (h.three_half i).2
  linarith

end Angles

/-! ### The reductions of Troyanov's theorem -/

section Main

/-- **Troyanov's theorem from its restriction to angles all `≠ 2π`**: an angle `θ_k = 2π` is
deleted (`TroyanovAngleCondition.removeNth`), the cone sphere of the remaining angles is built, and
any point off its cone points is added as a cone point of angle `2π` (`IsConeSphere.insertNth`).
(The conclusion is the body of `GX.TroyanovTheorem`, `GXScaffold.Spherical.TroyanovAngles`, which
this module does not import.) -/
theorem troyanovTheorem_of_ne_two_pi
    (h : ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ → (∀ i, θ i ≠ 2 * π) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p := by
  intro s
  induction s with
  | zero => intro θ hθ; exact absurd hθ.1 (by norm_num)
  | succ n ih =>
    intro θ hθ
    by_cases hne : ∀ i, θ i ≠ 2 * π
    · exact h θ hθ hne
    obtain ⟨k, hk⟩ : ∃ k, θ k = 2 * π := by
      by_contra hc
      exact hne fun i hi => hc ⟨i, hi⟩
    obtain ⟨M, _, _, p, hp⟩ := ih (k.removeNth θ) (hθ.removeNth hk)
    obtain ⟨q, hq⟩ := hp.exists_notMem_range
    exact ⟨M, _, _, _, hp.insertNth hk hq⟩

/-- **Troyanov's theorem from its restriction to `s ≥ 4` angles all `≠ 2π`**: with
`troyanovTheorem_of_ne_two_pi` and `troyanovTheorem_three` (`s = 3`). -/
theorem troyanovTheorem_of_four_le_of_ne_two_pi
    (h4 : ∀ {s : ℕ}, 4 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleCondition θ → (∀ i, θ i ≠ 2 * π) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p :=
  troyanovTheorem_of_ne_two_pi fun {s} θ hθ hne => by
    rcases Nat.lt_or_ge s 4 with hs | hs
    · obtain rfl : s = 3 := by have := hθ.1; omega
      exact troyanovTheorem_three θ hθ
    · exact h4 hs θ hθ hne

/-- **The reduction is an equivalence**: Troyanov's theorem (the body of `GX.TroyanovTheorem`)
holds iff it holds for `s ≥ 4` angles all `≠ 2π`. -/
theorem troyanovTheorem_iff_four_le_ne_two_pi :
    (∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) ↔
    (∀ {s : ℕ}, 4 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleCondition θ → (∀ i, θ i ≠ 2 * π) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :=
  ⟨fun h _ _ θ hθ _ => h θ hθ, troyanovTheorem_of_four_le_of_ne_two_pi⟩

end Main

end GX
