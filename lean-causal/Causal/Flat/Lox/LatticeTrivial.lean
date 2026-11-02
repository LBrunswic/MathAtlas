import Causal.Flat.Externals

/-!
# `Causal.Flat.Lox.LatticeTrivial` — a finite-index subgroup acting trivially on `E = span 𝒩`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
item **[10.G]** of `docs/BARBOT.md` (`GHFspace.tex` l.3406–3418). **No ledger label is certified
here** (no `**` mark): this is one step of the prose of [10.G], served to
`loxo_generic_centralExtension` (`Flat/Loxodromic.lean`), namely "the finite-index subgroup on
which `L(Γ)|_E` is trivial". The consumer instantiates `N := kerTranslations Γ`,
`hsp := span_kerTranslations_spacelike`, `hfin := kerTranslations_ballFinite`,
`hstab := linOf_mem_kerTranslations`; the conclusion is the field
`∀ γ ∈ Γ', ∀ v ∈ E, linOf γ v = v` of `IsCHCentralExtensionOf`.

> The action of $\Gamma$ on $\mathcal N$ by conjugacy
> is linear; more precisely, the conjugacy by $\gamma$
> maps the translation by vector $v$ to the translation
> by vector $L(\gamma)v$. Hence, it extends to
> an isometric action on the euclidean space $E$,
> which moreover preserves the lattice $\mathcal N$.
> Hence, replacing $\Gamma$ by some finite index subgroup,
> we can assume that this action is trivial. (l.3410–3417)

The proof does not go through Bieberbach's `finite_latticeStab` (which needs an `IsZLattice`
structure on `𝒩`): `minkQ` is positive definite on the finite-dimensional `E`, hence coercive
(`exists_mul_norm_sq_le_minkQ`, compactness of the unit sphere of `E`); a basis `b ⊆ 𝒩` of `E`
lies in the finite set `F = 𝒩 ∩ {minkQ ≤ r}`, which `L(Γ)` permutes; the kernel of
`Γ →* Perm F` has finite index and fixes `b`, hence `E`, pointwise.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `E` spacelike ("euclidean space `E`") | ✓ carried: `hsp`, `minkQ > 0` on `span N ∖ 0` |
| `𝒩` a lattice in `E` | ⚠ weakened: only discreteness (`hfin`, ball-finite); cocompactness in `E` is not used |
| `L(Γ)` preserves `𝒩` | ✓ carried: `hstab` (`L(γ) ∈ SO₀(1,d)` preserves `minkQ` by definition) |

## SCOPE (disclosed)
Nothing is left unproved. The finite-index subgroup is produced as a subgroup of `isom d` below
`Γ`, with finiteness stated as `Γ'.relIndex Γ ≠ 0`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written by a prover
of the Barbot campaign (round 5, `Lox/` split of `loxo_generic_centralExtension`), from the
planner's sketch `/tmp/loxplan/G1_LatticeTrivial.lean`.
-/

namespace Causal.Flat.Lox
open Set
variable {d : ℕ}

/-- `minkQ` positive definite on a (finite-dimensional) subspace `E` of `Minkowski d` is coercive\non `E`: `c ‖v‖² ≤ minkQ v` for some `c > 0`. -/
theorem exists_mul_norm_sq_le_minkQ (E : Submodule ℝ (Minkowski d))
    (hpos : ∀ v ∈ E, v ≠ 0 → 0 < minkQ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ E, c * ‖v‖ ^ 2 ≤ minkQ v := by
  have hS : IsCompact ((E : Set (Minkowski d)) ∩ Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).inter_left E.closed_of_finiteDimensional
  have hunit : ∀ v ∈ E, v ≠ 0 → ‖v‖⁻¹ • v ∈ (E : Set (Minkowski d)) ∩ Metric.sphere 0 1 := by
    intro v hv hv0
    refine ⟨E.smul_mem _ hv, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
  have h0 : minkQ (0 : Minkowski d) = 0 := by simp [minkQ]
  rcases (E : Set (Minkowski d)) ∩ Metric.sphere 0 1 |>.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · simp [hv0, h0]
    · exact absurd (hunit v hv hv0) (he ▸ Set.notMem_empty _)
  · obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hne continuous_minkQ.continuousOn
    have hx0 : x ≠ 0 := by
      rintro rfl; simpa using hx.2
    refine ⟨minkQ x, hpos x hx.1 hx0, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · simp [hv0, h0]
    · have hle : minkQ x ≤ minkQ (‖v‖⁻¹ • v) := hmin (hunit v hv hv0)
      have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have hv' : v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      calc minkQ x * ‖v‖ ^ 2 ≤ minkQ (‖v‖⁻¹ • v) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = minkQ v := by
          conv_rhs => rw [hv', minkQ_smul]
          ring

/-- **[10.G], l.3412–3417**: if `L(Γ)` preserves a ball-finite set `N` spanning a spacelike\nsubspace `E`, a finite-index subgroup `Γ' ≤ Γ` has `L(γ)|_E = id`. -/
theorem exists_finiteIndex_linOf_eq_on_span {Γ : Subgroup (isom d)} {N : Set (Minkowski d)}
    (hsp : ∀ v ∈ Submodule.span ℝ N, v ≠ 0 → 0 < minkQ v)
    (hfin : ∀ R : ℝ, (N ∩ Metric.closedBall 0 R).Finite)
    (hstab : ∀ γ ∈ Γ, ∀ v ∈ N, linOf γ v ∈ N) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∀ γ ∈ Γ', ∀ v ∈ Submodule.span ℝ N, linOf γ v = v := by
  classical
  obtain ⟨c, hc, hcoer⟩ := exists_mul_norm_sq_le_minkQ _ hsp
  obtain ⟨b, hbN, hbspan, hbli⟩ := exists_linearIndependent ℝ N
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨r, hr⟩ := (hbfin.image minkQ).bddAbove
  -- the finite `L(Γ)`-invariant set `F`
  set F : Set (Minkowski d) := N ∩ {v | minkQ v ≤ r} with hFdef
  have hFfin : F.Finite := by
    refine (hfin (Real.sqrt (r / c))).subset fun v hv => ⟨hv.1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hvE : v ∈ Submodule.span ℝ N := Submodule.subset_span hv.1
    have h1 : c * ‖v‖ ^ 2 ≤ r := (hcoer v hvE).trans hv.2
    have h2 : ‖v‖ ^ 2 ≤ r / c := by rw [le_div_iff₀ hc]; linarith
    simpa [abs_of_nonneg (norm_nonneg v)] using Real.abs_le_sqrt h2
  haveI : Finite F := hFfin.to_subtype
  have hmaps : ∀ γ : Γ, ∀ v ∈ F, linOf (γ : isom d) v ∈ F := fun γ v hv =>
    ⟨hstab γ γ.2 v hv.1, by
      show minkQ _ ≤ r; rw [lorentz.minkQ_apply (linOf_mem _)]; exact hv.2⟩
  letI act : MulAction Γ F :=
    { smul := fun γ v => ⟨linOf (γ : isom d) v, hmaps γ v v.2⟩
      one_smul := fun v => rfl
      mul_smul := fun _ _ _ => rfl }
  let φ : Γ →* Equiv.Perm F := MulAction.toPermHom Γ F
  refine ⟨φ.ker.map Γ.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have : (φ.ker.map Γ.subtype).relIndex Γ = φ.ker.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective]
    rw [this, Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · rintro _ ⟨γ, hγ, rfl⟩ v hv
    have hfix : ∀ w ∈ b, linOf (γ : isom d) w = w := by
      intro w hw
      have hwF : w ∈ F := ⟨hbN hw, hr ⟨w, hw, rfl⟩⟩
      have := congrArg Subtype.val (Equiv.ext_iff.1 (MonoidHom.mem_ker.1 hγ) ⟨w, hwF⟩)
      exact this
    have hle : Submodule.span ℝ b ≤
        LinearMap.eqLocus (linOf (γ : isom d) : Minkowski d →ₗ[ℝ] Minkowski d) LinearMap.id :=
      Submodule.span_le.2 fun w hw => hfix w hw
    rw [← hbspan] at hv
    exact hle hv
end Causal.Flat.Lox
