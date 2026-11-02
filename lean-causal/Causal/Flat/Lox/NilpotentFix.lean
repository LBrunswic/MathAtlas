import Causal.Flat.Externals
import Causal.Flat.Lox.EllipticCommonFix
import Causal.Flat.Lox.CommuteOnFix

/-!
# A nilpotent group normalised by `G` with no nonzero non-spacelike fixed vector gives a fixed point of `𝒮` for a finite-index subgroup of `G`

Spacelike step of Barbot's Prop 10.4 (`bprop:U_timelike`, `GHFspace.tex` l.3346–3362), served to
`bprop_U_timelike` (`Flat/Loxodromic.lean`): if `N ≤ SO₀(1, d)` is nilpotent and normalised by
`G`, and every nonzero vector fixed by all of `N` is spacelike, then a finite-index subgroup of
`G` fixes a point of `𝒮`. With `G = L(Γ)`, `N = L(Γ_nd)` (nilpotent by Auslander–Carrière–Dal'bo,
`bthm:ausl`, l.3339–3344) and the common fixed space of `L(Γ_nd)` spacelike, this contradicts the
standing hypothesis that no finite-index subgroup of `L(Γ)` fixes an isotropic direction.
**No label is marked**: this is one step of a proof, not a statement of the paper.
Barbot's `𝐌ⁿ` is `Minkowski d` with `n = d + 1`.

* `bprop:U_timelike`, `GHFspace.tex:3346–3362`, partial (the spacelike case, by a route
  replacing the paper's; **no `sorry`** in this file): `exists_finiteIndex_fix_of_nilpotent_normal`.

> Apply Theorems
> \ref{ausl}, \ref{unip}: the non-discrete part
> $\Gamma_{nd}$ is nilpotent; and there is a unique maximal ${\bf U}$
> on which the action of $\Gamma_{nd}$ is unipotent. (l.3339–3342)

> If ${\bf U}$ is spacelike, then, according to corollary
> \ref{abel}, a finite index subgroup of $\Gamma$ is abelian. Now, an abelian subgroup
> of $SO_{0}(1,n-1)$ fixes a pair of isotropic directions, except
> if it consists only one elliptic elements fixing one and
> only one timelike vector $v_{0}$. The first case is excluded by hypothesis,
> and the second case is forbidden too, since in this case $v_{0}$ has to be
> fixed by the entire group $\Gamma$, and, thus, to belong to ${\bf U}$, which
> is a contradiction with the definition of ${\bf U}$. (l.3354–3362)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| a finite-index subgroup of `Γ` abelian (Cor 8.4, `bcor:abel`) | ⚠ replaced: `N` nilpotent (`hnil`, from `bthm:ausl`); Cor 8.4 is false as printed (finding, `Flat/Loxodromic.lean` l.2369) |
| `Γ_nd` normal in `Γ` | ✓ carried as `hnorm` (`N ≤ G` not required) |
| `U` spacelike, `v₀` "has to belong to `U`" | ✓ carried as `hfix`: a nonzero vector fixed by all of `N` is spacelike |
| conclusion "fixes a pair of isotropic directions" | ✓ as: a finite-index subgroup of `G` fixes a point of `𝒮` |

## SCOPE (disclosed)

The paper's abelian route is not followed (Cor 8.4 is false as printed, and so is the folklore
"an abelian subgroup fixes a pair of isotropic directions", `not_abelianPairAsPrinted`). The
nilpotency of `L(Γ_nd)` is the external `AuslanderCarriereDalbo` (`Flat/Externals.lean`); the
`example` at the end derives it in the form used here.

Proof: by induction along the upper central series `Z₀ = 1 ≤ Z₁ ≤ … ≤ Z_c = N`, with `Wᵢ` the
vectors fixed by `Zᵢ` (invariant under `N` since `Zᵢ` is normal, and under `G` since `Zᵢ` is
characteristic and conjugation by `A ∈ G` is an automorphism of `N`): either the conclusion holds
or `Wᵢ` contains a timelike vector. Elements of `Zᵢ₊₁` commute on `Wᵢ` with all of `N` (their
commutators lie in `Zᵢ`). If some `z ∈ Zᵢ₊₁` is non-elliptic, `exists_finiteIndex_fix_of_commuteOn_nonElliptic`
(`Lox.CommuteOnFix`) gives the conclusion; if all are elliptic,
`exists_fixed_timelike_of_commuteOn` (`Lox.EllipticCommonFix`) gives a timelike vector of `Wᵢ₊₁`.
At `i = c` a timelike vector fixed by all of `N` contradicts `hfix`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (`/tmp/loxplan/R3_NilpotentFix.lean`). All auxiliaries are `private` (prefix
`nfx`; no public-name collision with the other `Flat/Lox/` files).
-/

namespace Causal.Flat.Lox

variable {d : ℕ}

private theorem nfx_mul_apply (A B : lorentz d) (v : Minkowski d) :
    ((A * B : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) v =
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) v) := rfl

private theorem nfx_inv_apply_apply (A : lorentz d) (v : Minkowski d) :
    ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v) = v := by
  rw [← nfx_mul_apply, inv_mul_cancel]; rfl

private theorem nfx_apply_inv_apply (A : lorentz d) (v : Minkowski d) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) v) = v := by
  rw [← nfx_mul_apply, mul_inv_cancel]; rfl

/-- The vectors fixed by every element of the `i`-th term of the upper central series of `N`. -/
private def nfxFix (N : Subgroup (lorentz d)) (i : ℕ) : Submodule ℝ (Minkowski d) where
  carrier := {w | ∀ h ∈ Subgroup.upperCentralSeries N i,
    (((h : N) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w}
  add_mem' := by
    intro a b ha hb h hh
    simp only [map_add, ha h hh, hb h hh]
  zero_mem' := by intro h _; simp
  smul_mem' := by
    intro c a ha h hh
    simp only [map_smul, ha h hh]

private theorem nfx_mem_fix {N : Subgroup (lorentz d)} {i : ℕ} {w : Minkowski d} :
    w ∈ nfxFix N i ↔ ∀ h ∈ Subgroup.upperCentralSeries N i,
      (((h : N) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w := Iff.rfl

/-- If `A⁻¹ h A` fixes `w`, then `h` fixes `A w`. -/
private theorem nfx_fix_conj {A h : lorentz d} {w : Minkowski d}
    (hw : ((A⁻¹ * h * A : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w = w) :
    (h : Minkowski d ≃ₗ[ℝ] Minkowski d) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) w) =
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w := by
  have := congrArg (A : Minkowski d ≃ₗ[ℝ] Minkowski d) hw
  rw [nfx_mul_apply, nfx_mul_apply, nfx_apply_inv_apply] at this
  exact this

/-- `nfxFix N i` is invariant under `N` (the upper central series is normal). -/
private theorem nfx_fix_N {N : Subgroup (lorentz d)} (i : ℕ) {B : lorentz d} (hB : B ∈ N)
    {w : Minkowski d} (hw : w ∈ nfxFix N i) :
    (B : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ nfxFix N i := by
  intro h hh
  have hc : (⟨B, hB⟩ : N)⁻¹ * h * (⟨B, hB⟩ : N)⁻¹⁻¹ ∈ Subgroup.upperCentralSeries N i :=
    (inferInstance : (Subgroup.upperCentralSeries N i).Normal).conj_mem h hh _
  have := hw _ hc
  rw [inv_inv] at this
  exact nfx_fix_conj this

/-- Conjugation by `A⁻¹`, for `A` normalising `N`, as an automorphism of `N`. -/
private noncomputable def nfxConj {G N : Subgroup (lorentz d)} (hnorm : ∀ A ∈ G, ∀ B ∈ N, A * B * A⁻¹ ∈ N)
    {A : lorentz d} (hA : A ∈ G) : N ≃* N where
  toFun n := ⟨A⁻¹ * n * A, by simpa using hnorm A⁻¹ (G.inv_mem hA) n n.2⟩
  invFun n := ⟨A * n * A⁻¹, hnorm A hA n n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])

/-- `nfxFix N i` is invariant under every `A` normalising `N` (the upper central series is
characteristic). -/
private theorem nfx_fix_G {G N : Subgroup (lorentz d)} (hnorm : ∀ A ∈ G, ∀ B ∈ N, A * B * A⁻¹ ∈ N)
    (i : ℕ) {A : lorentz d} (hA : A ∈ G) {w : Minkowski d} (hw : w ∈ nfxFix N i) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) w ∈ nfxFix N i := by
  intro h hh
  have hc : nfxConj hnorm hA h ∈ Subgroup.upperCentralSeries N i := by
    have : h ∈ (Subgroup.upperCentralSeries N i).comap (nfxConj hnorm hA : N →* N) := by
      rw [Subgroup.comap_upperCentralSeries]; exact hh
    exact this
  exact nfx_fix_conj (hw _ hc)

/-- Elements of the `(i+1)`-th term commute, on `nfxFix N i`, with every element of `N`. -/
private theorem nfx_commute {N : Subgroup (lorentz d)} {i : ℕ} {x : N}
    (hx : x ∈ Subgroup.upperCentralSeries N (i + 1)) {B : lorentz d} (hB : B ∈ N) {w : Minkowski d}
    (hw : w ∈ nfxFix N i) :
    ((x : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) w) =
      (B : Minkowski d ≃ₗ[ℝ] Minkowski d) (((x : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) w) := by
  have hc := (Subgroup.mem_upperCentralSeries_succ_iff.1 hx) ⟨B, hB⟩
  have hw' := nfx_fix_N i hB (nfx_fix_N i x.2 hw)
  have := hw' _ hc
  have e : ((x * ⟨B, hB⟩ * x⁻¹ * (⟨B, hB⟩ : N)⁻¹ : N) : lorentz d) =
      (x : lorentz d) * B * (x : lorentz d)⁻¹ * B⁻¹ := rfl
  rw [commutatorElement_def, e, nfx_mul_apply, nfx_mul_apply, nfx_mul_apply, nfx_inv_apply_apply,
    nfx_inv_apply_apply] at this
  exact this

/-- Spacelike step of Prop 10.4 (`bprop:U_timelike`, l.3354–3362), through the nilpotency of
`Γ_nd` (`bthm:ausl`, l.3339–3344) in place of Cor 8.4: a nilpotent `N ≤ SO₀(1, d)` normalised by
`G`, whose nonzero common fixed vectors are all spacelike, yields a finite-index subgroup of `G`
fixing a point of `𝒮`. -/
theorem exists_finiteIndex_fix_of_nilpotent_normal {d : ℕ} {G N : Subgroup (lorentz d)}
    (hnorm : ∀ A ∈ G, ∀ B ∈ N, A * B * A⁻¹ ∈ N) (hnil : Group.IsNilpotent N)
    (hfix : ∀ v : Minkowski d, (∀ B ∈ N, (B : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v) →
      v ≠ 0 → 0 < minkQ v) :
    ∃ H : Subgroup (lorentz d), H ≤ G ∧ H.relIndex G ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u := by
  classical
  -- `P i`: the conclusion, or a timelike vector fixed by the `i`-th term of the upper central
  -- series of `N`.
  have key : ∀ i : ℕ, (∃ H : Subgroup (lorentz d), H ≤ G ∧ H.relIndex G ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u) ∨
      ∃ w ∈ nfxFix N i, minkQ w < 0 := by
    intro i
    induction i with
    | zero =>
      refine Or.inr ⟨timeUnit d, ?_, by simp⟩
      intro h hh
      rw [Subgroup.upperCentralSeries_zero, Subgroup.mem_bot] at hh
      subst hh; rfl
    | succ i ih =>
      rcases ih with hc | hWt
      · exact Or.inl hc
      by_cases hall : ∀ x ∈ Subgroup.upperCentralSeries N (i + 1),
          IsElliptic (((x : N) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d)
      · -- every element of the `(i+1)`-th term is elliptic: a common fixed timelike vector
        let S : Set (lorentz d) := {g | ∃ x ∈ Subgroup.upperCentralSeries N (i + 1), (x : lorentz d) = g}
        obtain ⟨v, hvW, hvt, hvS⟩ := exists_fixed_timelike_of_commuteOn (S := S)
          (W := nfxFix N i) hWt
          (by rintro A ⟨x, -, rfl⟩ w hw; exact nfx_fix_N i x.2 hw)
          (by rintro A ⟨x, hx, rfl⟩; exact hall x hx)
          (by rintro A ⟨x, hx, rfl⟩ B ⟨y, -, rfl⟩ w hw; exact nfx_commute hx y.2 hw)
        exact Or.inr ⟨v, fun x hx => hvS _ ⟨x, hx, rfl⟩, hvt⟩
      · -- a non-elliptic element, commuting with `N` on `nfxFix N i`
        push Not at hall
        obtain ⟨x, hx, hne⟩ := hall
        exact Or.inl (exists_finiteIndex_fix_of_commuteOn_nonElliptic (W := nfxFix N i) hWt
          (fun A hA w hw => nfx_fix_G hnorm i hA hw) (fun B hB w hw => nfx_fix_N i hB hw)
          hnorm x.2 (fun B hB w hw => (nfx_commute hx hB hw).symm) hne)
  haveI := hnil
  rcases key (Group.nilpotencyClass N) with hc | ⟨v, hv, hvt⟩
  · exact hc
  · exfalso
    rw [nfx_mem_fix, Subgroup.upperCentralSeries_nilpotencyClass] at hv
    have hv0 : v ≠ 0 := by rintro rfl; simp [minkQ] at hvt
    have := hfix v (fun B hB => hv ⟨B, hB⟩ (Subgroup.mem_top _)) hv0
    linarith

/-- Integration check: the nilpotency input, `L(Γ_nd)` nilpotent, from `bthm:ausl`. -/
example {d : ℕ} {Γ : Subgroup (isom d)} (hA : AuslanderCarriereDalbo d) (hΓ : DiscreteTopology Γ) :
    Group.IsNilpotent (linearImage (nonDiscretePart Γ)) := by
  haveI := (hA Γ hΓ).2
  have e : (linearPart.comp (nonDiscretePart Γ).subtype).range = linearImage (nonDiscretePart Γ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← e]
  exact Group.nilpotent_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
end Causal.Flat.Lox
