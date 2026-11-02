import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Externals

/-!
# A nontrivial nilpotent unipotent group of `SO₀(1, d)` has a central non-elliptic element

Centre step of Barbot's Prop 10.5 (`bprop:LU_discrete`, `GHFspace.tex` l.3367–3388), served to
`bprop_LU_discrete` (`Flat/Loxodromic.lean`, the inner `obtain`): when
`L_U(Γ_nd) ≠ {1}`, the group `N = L_U(Γ_nd)` is normalised by `L_U(Γ)` and has a central
non-elliptic (indeed parabolic) member. **No label is marked**: this is one step of a proof, not a
statement of the paper.

* `bprop:LU_discrete`, `GHFspace.tex:3374–3381`, partial (the centre step, on the branch
  `L_U(Γ_nd) ≠ ⊥`, with `L_U(Γ_nd)` in place of the neutral component of the closure; **no
  `sorry`**): `exists_central_nonElliptic_of_unipotent`, `exists_normal_central_nonElliptic_restrict`.

> Hence, the neutral component of this
> closure is contained in $L_{U}(\Gamma_{nd})$, proving that this closure
> is nilpotent and its elements
> does not have elliptic parts: it contains only hyperbolic or
> unipotent elements. In particular, if it
> is not trivial, its center contains a parabolic or hyperbolic
> element.

Barbot's `n` is `d + 1` (resp. `d₁ + 1` for `U`): `Minkowski d` has `d` spatial dimensions.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` discrete (for `bthm:ausl`) | ✓ carried (`hΓ`, through `hA : AuslanderCarriereDalbo d`) |
| `U` the maximal unipotent subspace of `Γ_nd` (`bthm:unip`) | ✓ carried (`hmax`) |
| `Γ` restricts to isometries of `U` | ✓ carried (`hres`, `RestrictsIn`) |
| "if it is not trivial" | ✓ carried (`hnt`), for `L_U(Γ_nd)` |
| conclusion "centre contains a parabolic or hyperbolic element" | ✓ a central non-elliptic (in fact parabolic) element |

## SCOPE (disclosed)

The group used is `N = L_U(Γ_nd)` itself, not the neutral component of the closure of `L_U(Γ)`:
`N` is nilpotent (image of `Γ_nd`, nilpotent by `bthm:ausl`), unipotent on `U` (`IsMaxUnipotent`,
`bthm:unip`), and normal in `L_U(Γ)` (`conj_mem_nonDiscretePart`). The closure argument
(l.3372–3376), which is what links `hnd` (non-discreteness) to `L_U(Γ_nd) ≠ ⊥`, is not treated
here: the branch `L_U(Γ_nd) = ⊥` stays with the caller. The core lemma: a nontrivial nilpotent
group has a nontrivial centre (`Group.IsNilpotent.center_ne_bot`), and a nontrivial unipotent
element of `SO₀(1, d)` is parabolic (`IsUnipotent.isParabolic`), hence not elliptic
(`IsParabolic.not_isElliptic`). Only the parabolic alternative of the paper occurs.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan; `ucHom` reproves `RestrictFix`'s private `rfxHom` (composed with `L`).
-/

namespace Causal.Flat.Lox
open Set
variable {d d₁ : ℕ}

/-- **Core lemma.** A nontrivial nilpotent subgroup of `SO₀(1, d)` all of whose members are
unipotent has a central non-elliptic member (l.3378–3379: "if it is not trivial, its center
contains a parabolic or hyperbolic element"; here parabolic). -/
theorem exists_central_nonElliptic_of_unipotent {d : ℕ} {N : Subgroup (lorentz d)}
    (hnil : Group.IsNilpotent N) (hN : N ≠ ⊥)
    (huni : ∀ B ∈ N, IsUnipotent (B : Minkowski d ≃ₗ[ℝ] Minkowski d)) :
    ∃ z ∈ N, (∀ B ∈ N, B * z = z * B) ∧ ¬IsElliptic (z : Minkowski d ≃ₗ[ℝ] Minkowski d) := by
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hN
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.center_ne_bot N)
  refine ⟨((z : N) : lorentz d), (z : N).2, fun B hB => ?_, ?_⟩
  · have := (Subgroup.mem_center_iff.1 z.2) ⟨B, hB⟩
    exact congrArg Subtype.val this
  · have h1 : (((z : N) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) ≠ 1 := fun h =>
      hz1 (Subtype.ext (Subtype.ext (Subtype.ext h)))
    exact (IsUnipotent.isParabolic ((z : N) : lorentz d).2 (huni _ (z : N).2) h1).not_isElliptic

private theorem uc_restricts (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (γ : Γ) :
    ι.Restricts (γ : isom d) (Classical.choose (hres γ γ.2)) :=
  Classical.choose_spec (hres γ γ.2)

/-- The restriction hom followed by `L`: `Γ →* L_U(Γ)`, `γ ↦ L(g)` with `ι ∘ g = γ ∘ ι`. -/
private noncomputable def ucHom (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : Γ →* linearImage (ι.restrictGroup Γ) where
  toFun γ := ⟨linearPart (Classical.choose (hres γ γ.2)),
    Classical.choose (hres γ γ.2), ⟨γ, γ.2, uc_restricts ι hres γ⟩, rfl⟩
  map_one' := by
    refine Subtype.ext ?_
    simp only [OneMemClass.coe_one]
    rw [(uc_restricts ι hres 1).unique AffineMinkEmbedding.Restricts.one, map_one]
  map_mul' γ γ' := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [(uc_restricts ι hres (γ * γ')).unique
      ((uc_restricts ι hres γ).mul (uc_restricts ι hres γ')), map_mul]

private theorem ucHom_surjective (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : Function.Surjective (ucHom ι hres) := by
  rintro ⟨_, ⟨g, hg, rfl⟩⟩
  obtain ⟨γ, hγ, h⟩ := hg
  refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
  show linearPart (Classical.choose (hres γ hγ)) = linearPart g
  rw [(uc_restricts ι hres ⟨γ, hγ⟩).unique h]

/-- `ι.lin ∘ pOf(L g)^m = pOf(L γ)^m ∘ ι.lin` when `g` restricts `γ`. -/
private theorem uc_lin_pow {ι : AffineMinkEmbedding d₁ d} {γ : isom d} {g : isom d₁}
    (h : ι.Restricts γ g) (m : ℕ) (u : Minkowski d₁) :
    ι.lin ((pOf (linOf g) ^ m) u) = (pOf (linOf γ) ^ m) (ι.lin u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    rw [pOf_apply, pOf_apply, map_sub, h.lin]

/-- **The restricted lemma** (Prop 10.5, l.3374–3379, on the branch `L_U(Γ_nd) ≠ ⊥`):
`N = L_U(Γ_nd)` is normalised by `L_U(Γ)` and has a central non-elliptic member. Nilpotent by
`bthm:ausl` (`hA`), unipotent by `bthm:unip` (`hmax`). -/
theorem exists_normal_central_nonElliptic_restrict {d d₁ : ℕ} (hA : AuslanderCarriereDalbo d)
    {Γ : Subgroup (isom d)} (hΓ : DiscreteTopology Γ) (ι : AffineMinkEmbedding d₁ d)
    (hmax : IsMaxUnipotent (nonDiscretePart Γ) ι.range) (hres : ι.RestrictsIn Γ)
    (hnt : linearImage (ι.restrictGroup (nonDiscretePart Γ)) ≠ ⊥) :
    ∃ N : Subgroup (lorentz d₁),
      (∀ A ∈ linearImage (ι.restrictGroup Γ), ∀ B ∈ N, A * B * A⁻¹ ∈ N) ∧
      ∃ z ∈ N, (∀ B ∈ N, B * z = z * B) ∧
        ¬IsElliptic (z : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) := by
  set N := linearImage (ι.restrictGroup (nonDiscretePart Γ)) with hNdef
  have hres' : ι.RestrictsIn (nonDiscretePart Γ) := fun γ hγ => hres γ (nonDiscretePart_le Γ hγ)
  -- (i) nilpotent: the image of the nilpotent `Γ_nd`
  have hnil : Group.IsNilpotent N := by
    haveI := (hA Γ hΓ).2
    exact Group.nilpotent_of_surjective (ucHom ι hres') (ucHom_surjective ι hres')
  -- (ii) unipotent: `hmax` on `U = range ι`, pulled back by the injective `ι.lin`
  have huni : ∀ B ∈ N, IsUnipotent (B : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) := by
    rintro _ ⟨g, ⟨γ, hγ, h⟩, rfl⟩
    obtain ⟨m, hm⟩ := hmax.1.2 γ hγ
    refine ⟨m, LinearMap.ext fun u => ι.lin_injective ?_⟩
    have hdir : ι.lin u ∈ ι.range.direction := by
      rw [AffineMinkEmbedding.range, AffineSubspace.map_direction, AffineSubspace.direction_top]
      exact Submodule.mem_map_of_mem Submodule.mem_top
    have e := uc_lin_pow h m u
    rw [hm _ hdir] at e
    rw [LinearMap.zero_apply, map_zero]
    exact e
  -- (iii) normalised by `L_U(Γ)`
  have hnorm : ∀ A ∈ linearImage (ι.restrictGroup Γ), ∀ B ∈ N, A * B * A⁻¹ ∈ N := by
    rintro _ ⟨g, ⟨γ, hγ, hg⟩, rfl⟩ _ ⟨k, ⟨η, hη, hk⟩, rfl⟩
    exact ⟨g * k * g⁻¹, ⟨γ * η * γ⁻¹, conj_mem_nonDiscretePart hγ hη, (hg.mul hk).mul hg.inv⟩,
      by simp only [map_mul, map_inv]⟩
  -- (iv) the core lemma
  exact ⟨N, hnorm, exists_central_nonElliptic_of_unipotent hnil hnt huni⟩

end Causal.Flat.Lox
