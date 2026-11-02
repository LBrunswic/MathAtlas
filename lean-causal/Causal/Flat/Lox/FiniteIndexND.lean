import CausalScaffold.Flat.Externals

/-!
# The non-discrete part does not change on a finite-index subgroup containing it

A step of Barbot's [10.G] (`GHFspace.tex` l.3339–3396, the nonelementary loxodromic case), served
to `loxo_generic_centralExtension` (`Flat/Loxodromic.lean`): the reduction to the maximal unipotent
subspace `U` (`blem:suspendre`) passes to the index-`≤ 2` subgroup `Γ₂ ≤ Γ` restricting to `U`
(`Flat.Lox.RestrictOrient`), and Prop 10.5 (`bprop_LU_discrete`) is then applied to `Γ₂`, whose
hypothesis `IsMaxUnipotent (nonDiscretePart Γ₂) U` is the one known for `Γ` once
`nonDiscretePart Γ₂ = nonDiscretePart Γ` (`nonDiscretePart_eq_of_le`). **No label is marked**:
the paper uses this silently ("replacing `Γ` by a finite index subgroup", l.3418).

* `[10.G]`, `GHFspace.tex:3339–3344` and l.3418, partial (the finite-index invariance of `Γ_nd`;
  **no `sorry`**): `continuous_lorentz_inv`, `lorentz_isTopologicalGroup`,
  `connectedComponentIn_closure_subset_of_relIndex`, `relIndex_map_ne_zero`,
  `linClosureIdentityComponent_eq_of_relIndex`, `nonDiscretePart_eq_of_le`.

> Let $\Gamma_{nd}$ be the non-discrete part of $\Gamma$: according to Theorem \ref{ausl}, it is
> nilpotent. (l.3339–3340 of the labelled file)

Barbot's `n` is `d + 1`: `Minkowski d` has `d` spatial dimensions.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (silent) `Γ_nd` is unchanged by a finite-index subgroup containing it | ✓ proved: the identity component of the closure of `L(Γ')` is that of `L(Γ)` for every finite-index `Γ' ≤ Γ` (`linClosureIdentityComponent_eq_of_relIndex`) |

## SCOPE (disclosed)

* `SO₀(1, d)` is a topological group in `Externals`' `lorentzTopology` (`lorentz_isTopologicalGroup`):
  `Externals` provides `ContinuousMul` only; the continuity of the inverse is proved here from
  `NormedRing.inverse_continuousAt` in the complete normed ring of operators. It is a theorem, not an
  instance (the topology is scoped; callers use `haveI`).
* The identity component argument: the closure of a finite-index subgroup `K₂ ≤ K` is a closed
  subgroup whose finitely many cosets cover the closure of `K`, so it is clopen there and contains
  the component of `1`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 7, package WP-34d-Loxodromic.
-/

namespace Causal.Flat.Lox
open Set Topology Pointwise

variable {d : ℕ}

/-! ### `SO₀(1, d)` is a topological group -/

/-- **Inversion is continuous on `SO₀(1, d)`** (`lorentzTopology`): `linToCLM (A⁻¹)` is the ring
inverse of `linToCLM A` in the complete normed ring `End(𝐌ⁿ)`, which is continuous at units. -/
theorem continuous_lorentz_inv : Continuous (fun A : lorentz d => A⁻¹) := by
  rw [isEmbedding_lorentz_linToCLM.isInducing.continuous_iff]
  have hunit : ∀ A : lorentz d, linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
      Ring.inverse (linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) := by
    intro A
    have h1 : linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) *
        linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 := by
      rw [← linToCLM_mul, ← linToCLM_one]; congr 1
      show ((A * A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1
      rw [mul_inv_cancel]; rfl
    have h2 : linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) *
        linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 := by
      rw [← linToCLM_mul, ← linToCLM_one]; congr 1
      show ((A⁻¹ * A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1
      rw [inv_mul_cancel]; rfl
    let u : (Minkowski d →L[ℝ] Minkowski d)ˣ := ⟨_, _, h1, h2⟩
    exact (Ring.inverse_unit u).symm
  have e : (fun A : lorentz d =>
      linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)) =
      Ring.inverse ∘ fun A : lorentz d => linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
    funext hunit
  rw [Function.comp_def] at e ⊢
  rw [e]
  refine continuous_iff_continuousAt.2 fun A => ?_
  have h1 : linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) *
      linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 := by
    rw [← linToCLM_mul, ← linToCLM_one]; congr 1
    show ((A * A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1
    rw [mul_inv_cancel]; rfl
  have h2 : linToCLM ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) *
      linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1 := by
    rw [← linToCLM_mul, ← linToCLM_one]; congr 1
    show ((A⁻¹ * A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = 1
    rw [inv_mul_cancel]; rfl
  let u : (Minkowski d →L[ℝ] Minkowski d)ˣ := ⟨_, _, h1, h2⟩
  exact ContinuousAt.comp (g := Ring.inverse) (f := fun B : lorentz d =>
    linToCLM (B : Minkowski d ≃ₗ[ℝ] Minkowski d)) (x := A)
    (NormedRing.inverse_continuousAt u) continuous_lorentz_linToCLM.continuousAt

/-- **`SO₀(1, d)` is a topological group** in `lorentzTopology`. -/
theorem lorentz_isTopologicalGroup : IsTopologicalGroup (lorentz d) :=
  { toContinuousInv := ⟨continuous_lorentz_inv⟩ }

/-! ### Closures of finite-index subgroups -/

section TopGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The component of `1` in the closure of `K` lies in the closure of any finite-index subgroup
`K₂` of `K`** (`K₂ ≤ K` is not needed: `relIndex` is read through `K₂ ⊓ K`): the closed subgroup `cl K₂` has finitely many cosets covering `cl K`, each closed and
either inside `cl K₂` or disjoint from it, so `cl K₂` is clopen in `cl K`. -/
theorem connectedComponentIn_closure_subset_of_relIndex {K K₂ : Subgroup G}
    (hidx : K₂.relIndex K ≠ 0) :
    connectedComponentIn (closure (K : Set G)) 1 ⊆ closure (K₂ : Set G) := by
  classical
  set T : Subgroup G := K₂.topologicalClosure
  have hT : (T : Set G) = closure (K₂ : Set G) := rfl
  have hTc : IsClosed (T : Set G) := K₂.isClosed_topologicalClosure
  haveI : (K₂.subgroupOf K).FiniteIndex := ⟨hidx⟩
  haveI : Finite (K ⧸ K₂.subgroupOf K) := Subgroup.finite_quotient_of_finiteIndex
  set r : (K ⧸ K₂.subgroupOf K) → G := fun q => ((Quotient.out q : K) : G)
  -- `K ⊆ ⋃_q r q • K₂`
  have hcov : (K : Set G) ⊆ ⋃ q, r q • (K₂ : Set G) := by
    intro k hk
    set q : K ⧸ K₂.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    have hq : (Quotient.out q : K)⁻¹ * ⟨k, hk⟩ ∈ K₂.subgroupOf K :=
      QuotientGroup.leftRel_apply.1 (Quotient.exact (Quotient.out_eq q))
    rw [Subgroup.mem_subgroupOf] at hq
    refine mem_iUnion.2 ⟨q, ⟨_, hq, ?_⟩⟩
    show r q * (((Quotient.out q : K)⁻¹ * ⟨k, hk⟩ : K) : G) = k
    simp [r]
  have hclK : closure (K : Set G) ⊆ ⋃ q, r q • (T : Set G) := by
    refine (closure_mono hcov).trans ?_
    rw [closure_iUnion_of_finite]
    refine iUnion_mono fun q => ?_
    rw [closure_smul, hT]
  -- the cosets disjoint from `T`
  set F : Set G := closure (K : Set G) ∩ ⋃ q ∈ {q | r q ∉ T}, r q • (T : Set G)
  have hFc : IsClosed F := by
    exact isClosed_closure.inter ((Set.toFinite {q | r q ∉ T}).isClosed_biUnion
      fun q _ => hTc.smul (r q))
  have hdisj : Disjoint (T : Set G) F := by
    rw [Set.disjoint_left]
    rintro x hxT ⟨-, hxF⟩
    obtain ⟨q, hq, t, ht, rfl⟩ := mem_iUnion₂.1 hxF
    refine hq ?_
    have : r q = (r q * t) * t⁻¹ := by group
    rw [this]
    exact T.mul_mem hxT (T.inv_mem ht)
  have hsub : closure (K : Set G) ⊆ (T : Set G) ∪ F := by
    intro x hx
    obtain ⟨q, t, ht, rfl⟩ := mem_iUnion.1 (hclK hx)
    by_cases hq : r q ∈ T
    · exact Or.inl (T.mul_mem hq ht)
    · exact Or.inr ⟨hx, mem_iUnion₂.2 ⟨q, hq, t, ht, rfl⟩⟩
  have h1K : (1 : G) ∈ closure (K : Set G) := subset_closure K.one_mem
  have hC := isPreconnected_connectedComponentIn (F := closure (K : Set G)) (x := (1 : G))
  have hCsub : connectedComponentIn (closure (K : Set G)) 1 ⊆ (T : Set G) ∪ F :=
    (connectedComponentIn_subset _ _).trans hsub
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hC _ _ hTc hFc hCsub
    (by rw [Set.disjoint_iff_inter_eq_empty.1 hdisj, Set.inter_empty]) with h | h
  · exact h
  · exfalso
    have h1 := h (mem_connectedComponentIn h1K)
    exact Set.disjoint_left.1 hdisj T.one_mem h1

end TopGroup

/-- **The image of a finite-index subgroup has finite index in the image.** -/
theorem relIndex_map_ne_zero {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {H K : Subgroup G} (hidx : H.relIndex K ≠ 0) : (H.map f).relIndex (K.map f) ≠ 0 := by
  rw [← Subgroup.relIndex_comap]
  exact fun h0 => hidx (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K
    (Subgroup.le_comap_map f H)))

/-- **`G₀` is unchanged by a finite-index subgroup**: the identity component of the closure of
`L(Γ')` is that of `L(Γ)`. -/
theorem linClosureIdentityComponent_eq_of_relIndex {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) :
    linClosureIdentityComponent Γ' = linClosureIdentityComponent Γ := by
  haveI := lorentz_isTopologicalGroup (d := d)
  have hle' : linearImage Γ' ≤ linearImage Γ := Subgroup.map_mono hle
  have hidx' := relIndex_map_ne_zero linearPart hidx
  apply Subset.antisymm
  · exact connectedComponentIn_mono 1 (closure_mono hle')
  · have h1 : (1 : lorentz d) ∈ closure (linearImage Γ : Set (lorentz d)) :=
      subset_closure (linearImage Γ).one_mem
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn h1)
      (connectedComponentIn_closure_subset_of_relIndex hidx')

/-- **`Γ_nd` is unchanged on a finite-index subgroup containing it**: if
`nonDiscretePart Γ ≤ Γ' ≤ Γ` with `Γ'` of finite index, `nonDiscretePart Γ' = nonDiscretePart Γ`. -/
theorem nonDiscretePart_eq_of_le {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) (hnd : nonDiscretePart Γ ≤ Γ') :
    nonDiscretePart Γ' = nonDiscretePart Γ := by
  have e := linClosureIdentityComponent_eq_of_relIndex hle hidx
  ext x
  simp only [nonDiscretePart, Subgroup.mem_inf, Subgroup.mem_comap, e]
  exact ⟨fun h => ⟨hle h.1, h.2⟩, fun h => ⟨hnd ⟨h.1, h.2⟩, h.2⟩⟩

end Causal.Flat.Lox
