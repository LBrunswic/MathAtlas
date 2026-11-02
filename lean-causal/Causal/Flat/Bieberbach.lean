import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# `Causal.Flat.Bieberbach` — the elementary part of Bieberbach's theory

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.1
"Non discrete linear parts and Auslander's Theorem" (`GHFspace.tex` l.1688–1749, label `bieb`),
the prose item **[5.B]** of `docs/BARBOT.md`. Package WP-33a (DEC-36's "Bieberbach-light", run
early). **No ledger label is certified here**: [5.B] is prose; the two cited theorems of §5.1,
bthm:ausl (l.1698) and bthm:unip (l.1711), belong to `Externals`.

> As an application of these theorems, it is easy for example to recover the following version
> of Bieberbach's Theorem: *If Γ is discrete group of isometries of the euclidean space of
> dimension n, it contains a finite index free abelian subgroup of finite rank.* (l.1720–1725)
>
> The proof goes as follows: if `L(Γ) ⊂ SO(n)` is discrete, it is finite; the kernel of `L|Γ` is
> a finite index subgroup of translations. If `L(Γ)` is not discrete, we consider the unique
> maximal unipotent affine subspace associated to `Γ_nd`: `Γ_nd` is a finite index subgroup of
> `Γ`, and the kernel of the restriction morphism `Γ → Isom(U)` is a finite index subgroup of
> `Γ_nd`. The proof is completed by the observation that unipotent elements of `Isom(U)` are
> translations. (l.1727–1735)

The uses downstream, and the form of the theorem each one consumes (see "Item 4" below):
* l.2305 (corollary 8.4, "the lemma then follows from Bieberbach's Theorem"): virtually `ℤᵏ`
  only — `virtuallyFree_of_bieberbachI`.
* l.2611–2614 ("up to finite index, there is a unique maximal affine subspace U on which Γ acts
  by translations. Moreover, `SO(n−1)` … preserves a timelike direction `Δ₀`: it follows that
  `U` is timelike"): **maximality** is spent — a non-maximal `U` (a spacelike line for `Γ ≅ ℤ`
  acting by spacelike translations) need not contain `Δ₀`. Served by `BieberbachMaxConclusion`
  and `mem_direction_of_fixed`.
* l.2877–2879 ("up to finite index, Γ acts effectively by translations on some affine
  subspace") together with l.2889–2891 ("since `𝒰̄₀` is the *maximal* `λ(Γ)`-unipotent subspace,
  it must contain every `𝒰̄_t`"): **maximality** again, for the `U` produced at l.2877. Served by
  `BieberbachMaxConclusion` (the greatest translation subspace of `Γ'`, for which
  `actsByTranslationsOn_of_unipotent` identifies "unipotent" with "by translations").
* l.1737–1749 (the crystallographic corollary, which reasons with `dim U`) and l.1772–1775 ("a
  twisted product of a flat torus `Γ \ U` by `ℝⁿ / U`"): **cocompactness** is spent — for `Γ = ℤ`
  acting by translations on `ℝ²`, the maximal `U = ℝ²` gives a cylinder, not a torus. Served by
  `BieberbachCocompactConclusion` and `virtuallyFree_of_bieberbachCocompactConclusion`
  (`Γ' ≅ ℤ^{dim U}`). l.3327 ("an appropriate use of Bieberbach's theorem leads to … a linear
  twisted product") is a twisted product too, hence the cocompact form.
The maximal and the cocompact `U` are in general **different** subspaces (the example above), so
no single `U` serves all three.

**Dimension (kb/0024).** This module is about a Euclidean space `E` (Barbot's `ℝⁿ`, or
`EuclideanSpace ℝ (Fin n)`), not about `Minkowski d`; it imports mathlib only. Where it is
applied to a spacelike subspace of `𝐌ⁿ = Minkowski d`, Barbot's `n` is `d + 1`.

* **Item 1 — discrete subgroups are lattices.** `discreteSubmodule_free`, `discreteSubmodule_finite`,
  `discreteSubmodule_finrank` (`ℤ`-rank = `dim_ℝ span`), `spanLattice` with instances
  `spanLattice.discreteTopology` and `spanLattice.isZLattice` (`IsZLattice` in the span),
  `spanLatticeEquiv`; `discreteTopology_of_finite_ball`; `exists_addEquiv_finsupp_span`,
  `exists_addEquiv_finsupp`.
* **Item 2 — finite orthogonal groups.** `orthToCLM`, `IsOpDiscrete` (discrete in the
  operator-norm topology of `E →L[ℝ] E`); `finite_of_isOpDiscrete` (a discrete subgroup of `O(E)`
  is finite); `finite_maps_lattice`, `latticeStab`, `finite_latticeStab` (the isometries
  preserving a full-rank lattice form a finite group).
* **Item 3 — `Isom(E) = E ≃ᵃⁱ[ℝ] E`.** The scoped action `instMulActionAffineIsometryEquiv`;
  `euclLinearPart` (Barbot's `L`), `euclTranslations` (its kernel), `mem_euclTranslations_iff`,
  `translationVectors`, `translationsEquiv`; `IsDiscreteEucl` (the chosen discreteness),
  `isDiscreteEucl_iff_exists`, `isDiscreteEucl_iff_properlyDiscontinuousSMul`;
  `discreteTopology_translationVectors`, `translationVectors_isZLattice`,
  `finrank_translationVectors`; `finiteIndex_euclTranslations`,
  `finite_linearParts_of_isOpDiscrete`; witnesses `isDiscreteEucl_zpowers_constVAdd`,
  `not_isDiscreteEucl_euclTranslations`.
* **Item 4 — `BieberbachI`**, a named `Prop` (DEC-36), stated with the WEAKEST conclusion
  `BieberbachConclusion` (an invariant `U`, a finite-index `Γ'` acting effectively by
  translations on it), so that the hypothesis downstream files carry is as weak as possible
  (kb/0007); with `IsInvariantSubspace`, `ActsByTranslationsOn`, `ActsEffectivelyOn`,
  `translationVectorsOn`. **The two forms the uses consume are PROVED from it**, with no
  discreteness: `BieberbachMaxConclusion` (`Γ'` normal in `Γ`; `U` the greatest affine subspace
  on which `Γ'` acts by translations, hence unique for that `Γ'`, and `Γ`-invariant) by
  `bieberbachMaxConclusion_of_bieberbachConclusion`, and `BieberbachCocompactConclusion` (same,
  with the translation vectors spanning `U`'s direction instead of maximality) by
  `bieberbachCocompactConclusion_of_bieberbachMaxConclusion`; the packaged
  `bieberbachMaxConclusion_of_bieberbachI`, `bieberbachCocompactConclusion_of_bieberbachI`.
  Tools: `pow_apply_of_translation`, `eq_of_pow_apply`, `translation_vector_unique`,
  `conj_mem_of_normal`, `translationLocus`, `mem_translationLocus`, `mem_direction_of_fixed`.
  Witnesses (kb/0012): `bieberbachConclusion_of_finite_linearParts`, `bieberbachI_of_finite`,
  `finite_linearIsometryEquiv_of_finrank_le_one`, `bieberbachI_of_finrank_le_one`,
  `bieberbachI_euclideanSpace_fin_one`, `bieberbachMaxConclusion_of_finite_linearParts`,
  `bieberbachCocompactConclusion_of_finite_linearParts`.
* **Item 5 — the rest of [5.B] that is elementary.** `virtuallyFree_of_actsByTranslationsOn`
  (`Γ' ≅ ℤᵏ`, `k = dim span` of its translation vectors, inside `U`'s direction),
  `virtuallyFree_le_finrank_direction` (`k ≤ dim U`), `virtuallyFree_of_bieberbachConclusion`,
  `virtuallyFree_of_bieberbachI` (Barbot's "version of Bieberbach's Theorem", l.1723–1725,
  conditional), `virtuallyFree_of_bieberbachCocompactConclusion` (`Γ' ≅ ℤ^{dim U}`),
  `virtuallyFree_of_isOpDiscrete_linearParts` (the first case of the proof, unconditional);
  `linearIsometry_apply_eq_self_of_unipotent`, `linearIsometryEquiv_eq_one_of_unipotent`,
  `mem_euclTranslations_of_unipotent`, `actsByTranslationsOn_of_unipotent` (the closing
  observation). Small helpers: `orthToCLM_apply`, `orthToCLM_injective`,
  `affineIsometryEquiv_smul_def`, `euclLinearPart_apply`, `constVAdd_add`, `constVAdd_neg`,
  `constVAdd_mem_euclTranslations`, `apply_eq_add_of_mem_euclTranslations`.

**Discreteness, the choice made.** `IsDiscreteEucl Γ` : for every `x` and `R`, finitely many
`γ ∈ Γ` satisfy `dist (γ x) x ≤ R`. It is equivalent to mathlib's `ProperlyDiscontinuousSMul Γ E`
(proved), and one point suffices (proved). It is the usual meaning of "discrete group of
isometries" (discrete in the compact-open topology of `Isom(E)`), which is not stated here
because mathlib puts no topology on `E ≃ᵃⁱ[ℝ] E`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| Γ discrete (l.1723) | ✓ carried, as `IsDiscreteEucl` (a choice, disclosed above) |
| `L(Γ) ⊂ SO(n)` discrete (l.1727) | ⚠ weakened to `L(Γ) ⊂ O(E)`. Not an erratum: Barbot reserves "isometry" for orientation-preserving maps (l.476–481), so `SO(n)` is right in his convention; `O(E)` is taken because the restriction of an `SO₀(1, n−1)` element to a spacelike `U` (l.2305) can reverse `U`'s orientation |
| finite dimension | ✓ carried (`FiniteDimensional ℝ E`); dropped where unused (`IsDiscreteEucl` criteria, the unipotent lemmas, the two upgrades) |
| `L(Γ)` finite ⇒ translations of finite index | ⚠ weakened: discreteness is not used |

## SCOPE (disclosed)
* **`BieberbachI` is NOT proved.** It is the `Prop` the downstream files take as a hypothesis
  (DEC-36). It is proved when the linear parts are finite, hence in dimension `≤ 1`; it is NOT
  reduced to the finite-linear-parts case in general: a screw motion of `ℝ³` by an irrational
  angle generates a discrete `Γ` with infinite `L(Γ)` (not formalized).
* The maximal and cocompact forms are proved FROM `BieberbachConclusion` (no further external
  input); their content beyond it is elementary (normal core; translation vectors are
  well-defined, `eq_of_pow_apply`; the barycentre of a finite orbit modulo `W`).
* "Cocompact" is stated as "the translation vectors of `Γ'` span `U.direction`"; with
  discreteness this gives `Γ' ≅ ℤ^{dim U}` (`virtuallyFree_of_bieberbachCocompactConclusion`).
  Compactness of the quotient space `Γ' \ U` itself is not formalized.
* "Unique maximal" (l.1730, l.2612): formalized for a FIXED `Γ'` (`BieberbachMaxConclusion`'s
  `U` is the greatest, hence unique). "Up to finite index" alone does not determine `U` (the
  screw example in the REPORT); the paper's `U` at l.1729–1730 is the one of bthm:unip for the
  specific subgroup `Γ_nd`, which is not formalized here (bthm:unip is an External).
* The second case of Barbot's proof (l.1729–1733) rests on bthm:ausl and bthm:unip (Externals);
  only its last sentence is proved (`actsByTranslationsOn_of_unipotent`).
* The crystallographic corollary (l.1737–1749) and its homological argument are not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written in the Barbot
campaign, WP-33a (wave 4, run early alongside wave 1b, DEC-36); fixed after audit (the maximal
and cocompact upgrades). Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

open Module Submodule Set Metric

/-! ### 1. Discrete subgroups of a finite-dimensional real vector space -/

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A discrete `ℤ`-submodule of a finite-dimensional real normed space is a free `ℤ`-module. -/
theorem discreteSubmodule_free (L : Submodule ℤ E) [DiscreteTopology L] : Module.Free ℤ L :=
  inferInstance

/-- A discrete `ℤ`-submodule of a finite-dimensional real normed space is finitely generated. -/
theorem discreteSubmodule_finite (L : Submodule ℤ E) [DiscreteTopology L] : Module.Finite ℤ L :=
  inferInstance

/-- The `ℤ`-rank of a discrete `ℤ`-submodule is the real dimension of its `ℝ`-span. -/
theorem discreteSubmodule_finrank (L : Submodule ℤ E) [DiscreteTopology L] :
    finrank ℤ L = finrank ℝ (span ℝ (L : Set E)) := by
  have hL : DiscreteTopology (span ℤ (L : Set E)) := by rw [span_eq]; infer_instance
  have h := Real.finrank_eq_int_finrank_of_discrete hL
  rw [Set.finrank, Set.finrank, span_eq] at h
  exact h.symm

/-- `L` read inside its own `ℝ`-span. -/
abbrev spanLattice (L : Submodule ℤ E) : Submodule ℤ (span ℝ (L : Set E)) :=
  comap ((span ℝ (L : Set E)).restrictScalars ℤ).subtype L

instance spanLattice.discreteTopology (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (spanLattice L) := by
  refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_ (injective_subtype _)
  exact LinearMap.continuous_of_finiteDimensional (span ℝ (L : Set E)).subtype

/-- **A discrete subgroup is a `ℤ`-lattice in its `ℝ`-span.** -/
instance spanLattice.isZLattice (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (spanLattice L) :=
  ⟨span_span_coe_preimage⟩

/-- `spanLattice L` is `L`, as a `ℤ`-module. -/
noncomputable def spanLatticeEquiv (L : Submodule ℤ E) : spanLattice L ≃ₗ[ℤ] L :=
  comapSubtypeEquivOfLe (p := L) (q := (span ℝ (L : Set E)).restrictScalars ℤ)
    fun _ hx => subset_span hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- An additive subgroup of `E` meeting the closed unit ball in a finite set is discrete. -/
theorem discreteTopology_of_finite_ball (S : AddSubgroup E)
    (h : {v | v ∈ S ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology S := by
  set F := {v | v ∈ S ∧ ‖v‖ ≤ 1} \ {0} with hFdef
  have hF : IsClosed F := (h.subset sdiff_subset).isClosed
  have hU : IsOpen (ball (0 : E) 1 ∩ Fᶜ) := isOpen_ball.inter hF.isOpen_compl
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val using 1
  ext ⟨v, hv⟩
  simp only [mem_singleton_iff, mem_preimage, mem_inter_iff, mem_ball, dist_zero_right,
    mem_compl_iff, hFdef, mem_sdiff, mem_setOf_eq, not_and, not_not]
  constructor
  · intro h0
    have hv0 : v = 0 := congrArg Subtype.val h0
    subst hv0
    simp
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (h2 ⟨hv, h1.le⟩)

/-- A group with an injective additive morphism `φ` to `E` whose fibres over balls are finite is
free abelian of rank `dim_ℝ (span (range φ))`. -/
theorem exists_addEquiv_finsupp_span {G : Type*} [Group G] (φ : Additive G →+ E)
    (hinj : Function.Injective φ) (hfin : ∀ R : ℝ, {g : G | ‖φ (Additive.ofMul g)‖ ≤ R}.Finite) :
    Nonempty (Additive G ≃+ (Fin (finrank ℝ (span ℝ (Set.range φ))) →₀ ℤ)) := by
  classical
  have hS : DiscreteTopology φ.range := by
    refine discreteTopology_of_finite_ball _ (((hfin 1).image
      (fun g : G => φ (Additive.ofMul g))).subset ?_)
    rintro v ⟨⟨g, rfl⟩, hv⟩
    exact ⟨Additive.toMul g, hv, rfl⟩
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule φ.range
  haveI : DiscreteTopology L := hS
  have hk : finrank ℤ L = finrank ℝ (span ℝ (Set.range φ)) := by
    rw [discreteSubmodule_finrank L]
    rfl
  let e1 : Additive G ≃+ φ.range := AddMonoidHom.ofInjective hinj
  let e2 : φ.range ≃+ L := AddEquiv.refl _
  let e3 : L ≃+ (Fin (finrank ℤ L) →₀ ℤ) := (Module.finBasis ℤ L).repr.toAddEquiv
  exact ⟨e1.trans (e2.trans (e3.trans (Finsupp.domCongr (finCongr hk))))⟩

/-- A group with an injective additive morphism to `E` whose fibres over balls are finite is free
abelian of finite rank `k ≤ dim E`. -/
theorem exists_addEquiv_finsupp {G : Type*} [Group G] (φ : Additive G →+ E)
    (hinj : Function.Injective φ) (hfin : ∀ R : ℝ, {g : G | ‖φ (Additive.ofMul g)‖ ≤ R}.Finite) :
    ∃ k ≤ finrank ℝ E, Nonempty (Additive G ≃+ (Fin k →₀ ℤ)) :=
  ⟨_, Submodule.finrank_le _, exists_addEquiv_finsupp_span φ hinj hfin⟩

end Lattice

/-! ### 2. Finite groups of linear isometries -/

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A linear isometry, as a continuous linear map (the operator-norm topology lives there). -/
def orthToCLM (g : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E := g.toLinearIsometry.toContinuousLinearMap

@[simp] theorem orthToCLM_apply (g : E ≃ₗᵢ[ℝ] E) (x : E) : orthToCLM g x = g x := rfl

theorem orthToCLM_injective : Function.Injective (orthToCLM (E := E)) := by
  intro g h hgh
  ext x
  rw [← orthToCLM_apply, hgh, orthToCLM_apply]

/-- A set of linear isometries is **discrete in the operator-norm topology** if its image in
`E →L[ℝ] E` is a discrete subspace. -/
def IsOpDiscrete (G : Set (E ≃ₗᵢ[ℝ] E)) : Prop := DiscreteTopology (orthToCLM '' G : Set (E →L[ℝ] E))

variable [FiniteDimensional ℝ E]

/-- **A discrete subgroup of `O(E)` is finite** (compactness of the unit ball of `End E`). -/
theorem finite_of_isOpDiscrete (G : Subgroup (E ≃ₗᵢ[ℝ] E)) (hG : IsOpDiscrete (G : Set (E ≃ₗᵢ[ℝ] E))) :
    (G : Set (E ≃ₗᵢ[ℝ] E)).Finite := by
  classical
  set S : Set (E →L[ℝ] E) := orthToCLM '' (G : Set (E ≃ₗᵢ[ℝ] E)) with hSdef
  haveI : DiscreteTopology S := hG
  have h1S : orthToCLM 1 ∈ S := ⟨1, G.one_mem, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_discrete ({⟨orthToCLM 1, h1S⟩} : Set S)) ⟨orthToCLM 1, h1S⟩ rfl
  have hiso : ∀ g ∈ G, dist (orthToCLM g) (orthToCLM 1) < ε → g = 1 := by
    intro g hg hd
    have hmem : (⟨orthToCLM g, g, hg, rfl⟩ : S) ∈ ball (⟨orthToCLM 1, h1S⟩ : S) ε := hd
    exact orthToCLM_injective (congrArg Subtype.val (hball hmem))
  have hdist : ∀ g h : E ≃ₗᵢ[ℝ] E,
      dist (orthToCLM g) (orthToCLM h) = dist (orthToCLM (h⁻¹ * g)) (orthToCLM 1) := by
    intro g h
    rw [dist_eq_norm, dist_eq_norm]
    have : orthToCLM g - orthToCLM h =
        (h.toLinearIsometry.toContinuousLinearMap).comp (orthToCLM (h⁻¹ * g) - orthToCLM 1) := by
      ext x
      simp [orthToCLM]
    rw [this, LinearIsometry.norm_toContinuousLinearMap_comp]
  have hball1 : ∀ g : E ≃ₗᵢ[ℝ] E, orthToCLM g ∈ closedBall (0 : E →L[ℝ] E) 1 := by
    intro g
    rw [mem_closedBall, dist_zero_right]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : E →L[ℝ] E) 1).totallyBounded (ε / 2) (half_pos hε)
  have hpick : ∀ g : E ≃ₗᵢ[ℝ] E, ∃ y ∈ t, orthToCLM g ∈ ball y (ε / 2) := by
    intro g
    simpa using hcov (hball1 g)
  choose y hyt hyb using hpick
  refine Set.Finite.of_finite_image (f := y) (htf.subset ?_) ?_
  · rintro _ ⟨g, -, rfl⟩
    exact hyt g
  · intro g hg h hh hgh
    have hlt : dist (orthToCLM g) (orthToCLM h) < ε := by
      calc dist (orthToCLM g) (orthToCLM h) ≤ dist (orthToCLM g) (y g) + dist (y g) (orthToCLM h) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add (hyb g) ?_
            rw [hgh, dist_comm]
            exact hyb h
        _ = ε := add_halves ε
    rw [hdist] at hlt
    have := hiso _ (G.mul_mem (G.inv_mem hh) hg) hlt
    exact (inv_mul_eq_one.mp this).symm

/-- **Only finitely many linear isometries map a full-rank lattice into itself.** -/
theorem finite_maps_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    {g : E ≃ₗᵢ[ℝ] E | ∀ x ∈ L, g x ∈ L}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let b' := b.ofZLatticeBasis ℝ L
  let f : (E ≃ₗᵢ[ℝ] E) → (Module.Free.ChooseBasisIndex ℤ L → E) := fun g i => g (b i)
  have hdL : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hdL' : DiscreteTopology (L : Set E) := (inferInstance : DiscreteTopology L)
  have hc : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hpi : (Set.pi univ fun i => closedBall (0 : E) ‖(b i : E)‖ ∩ (L : Set E)).Finite := by
    refine Set.Finite.pi fun i => ?_
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall hc
  refine Set.Finite.of_finite_image (f := f) (hpi.subset ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩ i -
    exact ⟨by simp [f], hg _ (b i).2⟩
  · intro g _ h _ hgh
    have : (g.toLinearEquiv : E →ₗ[ℝ] E) = h.toLinearEquiv := b'.ext fun i => by
      simpa [b', f, Basis.ofZLatticeBasis_apply] using congrFun hgh i
    ext x
    exact LinearMap.congr_fun this x

/-- The stabiliser of a lattice in `O(E)`. -/
def latticeStab (L : Submodule ℤ E) : Subgroup (E ≃ₗᵢ[ℝ] E) where
  carrier := {g | ∀ x, g x ∈ L ↔ x ∈ L}
  one_mem' := fun x => by simp
  mul_mem' := by
    intro g h hg hh x
    simp only [mem_setOf_eq] at hg hh ⊢
    rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hg, hh]
  inv_mem' := by
    intro g hg x
    simp only [mem_setOf_eq] at hg ⊢
    rw [← hg (g⁻¹ x), LinearIsometryEquiv.coe_inv, LinearIsometryEquiv.apply_symm_apply]

/-- **The group of linear isometries preserving a full-rank lattice is finite.** -/
theorem finite_latticeStab (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    (latticeStab L : Set (E ≃ₗᵢ[ℝ] E)).Finite :=
  (finite_maps_lattice L).subset fun _ hg x hx => (hg x).2 hx

end Orthogonal

/-! ### Unipotent isometries -/

section Unipotent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A linear isometry fixes every vector it moves unipotently**: if `(A − 1)ᵐ x = 0`, then
`A x = x`. (The kernels of the powers of `A − 1` do not grow: if `(A − 1)² x = 0`, then
`y = A x − x` is fixed by `A`, and `⟪y, y⟫ = ⟪A y, A x⟫ − ⟪y, x⟫ = 0`.) -/
theorem linearIsometry_apply_eq_self_of_unipotent (A : E →ₗᵢ[ℝ] E) (m : ℕ) (x : E)
    (h : ((A.toLinearMap - 1) ^ m) x = 0) : A x = x := by
  set N : E →ₗ[ℝ] E := A.toLinearMap - 1 with hN
  have hNx : ∀ x, N x = A x - x := fun x => rfl
  have key : ∀ x, N (N x) = 0 → N x = 0 := by
    intro x hx
    have hAy : A (N x) = N x := by
      rw [hNx (N x)] at hx
      exact sub_eq_zero.mp hx
    have h0 : inner ℝ (N x) (N x) = (0 : ℝ) := by
      calc inner ℝ (N x) (N x) = inner ℝ (N x) (A x) - inner ℝ (N x) x := by
            rw [← inner_sub_right, ← hNx]
        _ = inner ℝ (A (N x)) (A x) - inner ℝ (N x) x := by rw [hAy]
        _ = 0 := by rw [LinearIsometry.inner_map_map, sub_self]
    exact inner_self_eq_zero.mp h0
  have hpow : ∀ k x, (N ^ (k + 1)) x = 0 → N x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply key
      apply ih
      rw [pow_succ, Module.End.mul_apply] at hx
      exact hx
  cases m with
  | zero =>
    have hx : x = 0 := by simpa using h
    rw [hx, map_zero]
  | succ m =>
    have := hpow m x h
    rw [hNx, sub_eq_zero] at this
    exact this

/-- **A unipotent linear isometry is the identity.** -/
theorem linearIsometryEquiv_eq_one_of_unipotent (A : E ≃ₗᵢ[ℝ] E) (m : ℕ)
    (h : ((A.toLinearEquiv : E →ₗ[ℝ] E) - 1) ^ m = 0) : A = 1 := by
  ext x
  exact linearIsometry_apply_eq_self_of_unipotent A.toLinearIsometry m x
    (by rw [show A.toLinearIsometry.toLinearMap = (A.toLinearEquiv : E →ₗ[ℝ] E) from rfl, h]; rfl)

end Unipotent

/-! ### 3. The Euclidean isometry group, its linear part and its translations -/

section Isom

open AffineIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Isom(E)` acts on `E` by evaluation. **Scoped** to `Causal.Flat` (mathlib at this pin has no
such instance; a global one would be a latent diamond if mathlib or another file adds one). -/
noncomputable scoped instance instMulActionAffineIsometryEquiv : MulAction (E ≃ᵃⁱ[ℝ] E) E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem affineIsometryEquiv_smul_def (g : E ≃ᵃⁱ[ℝ] E) (x : E) : g • x = g x := rfl

/-- **Barbot's `L`** for Euclidean isometries: the linear part, as a morphism of groups
`Isom(E) → O(E)`. -/
noncomputable def euclLinearPart : (E ≃ᵃⁱ[ℝ] E) →* (E ≃ₗᵢ[ℝ] E) where
  toFun g := g.linearIsometryEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem euclLinearPart_apply (g : E ≃ᵃⁱ[ℝ] E) :
    euclLinearPart g = g.linearIsometryEquiv := rfl

/-- The **translation subgroup** of `Isom(E)`: the kernel of the linear part. -/
noncomputable def euclTranslations : Subgroup (E ≃ᵃⁱ[ℝ] E) := (euclLinearPart (E := E)).ker

theorem constVAdd_add (v w : E) :
    constVAdd ℝ E (v + w) = constVAdd ℝ E v * constVAdd ℝ E w := by
  ext x
  simp [add_assoc]

theorem constVAdd_neg (v : E) : constVAdd ℝ E (-v) = (constVAdd ℝ E v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← constVAdd_add, neg_add_cancel, constVAdd_zero]
  rfl

theorem constVAdd_mem_euclTranslations (v : E) : constVAdd ℝ E v ∈ euclTranslations := by
  rw [euclTranslations, MonoidHom.mem_ker]
  ext x
  rfl

/-- A translation `g` is `x ↦ x + g 0`. -/
theorem apply_eq_add_of_mem_euclTranslations {g : E ≃ᵃⁱ[ℝ] E} (hg : g ∈ euclTranslations)
    (x : E) : g x = x + g 0 := by
  have h1 : g.linearIsometryEquiv = 1 := hg
  have := g.map_vadd 0 x
  simpa [h1] using this

theorem mem_euclTranslations_iff {g : E ≃ᵃⁱ[ℝ] E} :
    g ∈ euclTranslations ↔ ∃ v : E, g = constVAdd ℝ E v := by
  refine ⟨fun hg => ⟨g 0, ?_⟩, ?_⟩
  · ext x
    rw [apply_eq_add_of_mem_euclTranslations hg x]
    simp [add_comm]
  · rintro ⟨v, rfl⟩
    exact constVAdd_mem_euclTranslations v

/-- **Unipotent elements of `Isom(E)` are translations** (Barbot l.1733–1734). -/
theorem mem_euclTranslations_of_unipotent (g : E ≃ᵃⁱ[ℝ] E) (m : ℕ)
    (h : ((g.linearIsometryEquiv.toLinearEquiv : E →ₗ[ℝ] E) - 1) ^ m = 0) :
    g ∈ euclTranslations :=
  linearIsometryEquiv_eq_one_of_unipotent _ m h

/-- The translation vectors of a subgroup `Γ`: `{v | (x ↦ x + v) ∈ Γ}`. -/
def translationVectors (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : AddSubgroup E where
  carrier := {v | constVAdd ℝ E v ∈ Γ}
  zero_mem' := by
    simp only [mem_setOf_eq, constVAdd_zero]
    exact Γ.one_mem
  add_mem' := fun ha hb => by
    simp only [mem_setOf_eq, constVAdd_add] at ha hb ⊢
    exact Γ.mul_mem ha hb
  neg_mem' := fun ha => by
    simp only [mem_setOf_eq, constVAdd_neg] at ha ⊢
    exact Γ.inv_mem ha

/-- **Discreteness.** A subgroup `Γ` of `Isom(E)` is discrete when every orbit is uniformly
locally finite: for every point `x` and radius `R`, only finitely many `γ ∈ Γ` move `x` by at
most `R`. In a finite-dimensional `E` this is `ProperlyDiscontinuousSMul Γ E`
(`isDiscreteEucl_iff_properlyDiscontinuousSMul`), and one point suffices
(`isDiscreteEucl_iff_exists`). -/
def IsDiscreteEucl (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  ∀ x : E, ∀ R : ℝ, {γ | γ ∈ Γ ∧ dist (γ x) x ≤ R}.Finite

theorem isDiscreteEucl_iff_exists (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) :
    IsDiscreteEucl Γ ↔ ∃ x : E, ∀ R : ℝ, {γ | γ ∈ Γ ∧ dist (γ x) x ≤ R}.Finite := by
  refine ⟨fun h => ⟨0, h 0⟩, ?_⟩
  rintro ⟨x, hx⟩ y R
  refine (hx (R + 2 * dist y x)).subset ?_
  rintro γ ⟨hγ, hd⟩
  refine ⟨hγ, ?_⟩
  have h4 := dist_triangle4 (γ x) (γ y) y x
  rw [γ.dist_map, dist_comm x y] at h4
  linarith

theorem isDiscreteEucl_iff_properlyDiscontinuousSMul [ProperSpace E]
    (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : IsDiscreteEucl Γ ↔ ProperlyDiscontinuousSMul Γ E := by
  constructor
  · intro h
    refine ⟨fun {K L} hK hL => ?_⟩
    rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    obtain ⟨r, hr⟩ := (hK.isBounded.union hL.isBounded).subset_closedBall x
    refine ((h x (2 * r)).preimage Subtype.val_injective.injOn).subset ?_
    rintro γ ⟨_, ⟨k, hk, rfl⟩, hkL⟩
    refine ⟨γ.2, ?_⟩
    have h1 : dist k x ≤ r := hr (Or.inl hk)
    have h2 : dist ((γ : E ≃ᵃⁱ[ℝ] E) k) x ≤ r := hr (Or.inr hkL)
    have h3 := dist_triangle ((γ : E ≃ᵃⁱ[ℝ] E) x) ((γ : E ≃ᵃⁱ[ℝ] E) k) x
    rw [AffineIsometryEquiv.dist_map, dist_comm x k] at h3
    show dist ((γ : E ≃ᵃⁱ[ℝ] E) x) x ≤ 2 * r
    linarith
  · intro h x R
    have := h.finite_disjoint_inter_image (isCompact_singleton (x := x))
      (isCompact_closedBall x R)
    refine (this.image Subtype.val).subset ?_
    rintro γ ⟨hγ, hd⟩
    exact ⟨⟨γ, hγ⟩, ⟨γ x, ⟨x, rfl, rfl⟩, mem_closedBall.mpr hd⟩, rfl⟩

/-- The translation vectors of a discrete `Γ` form a discrete subgroup of `E`. -/
theorem discreteTopology_translationVectors {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hΓ : IsDiscreteEucl Γ) : DiscreteTopology (translationVectors Γ) := by
  refine discreteTopology_of_finite_ball _ (((hΓ 0 1).image fun γ => γ 0).subset ?_)
  rintro v ⟨hv, hn⟩
  exact ⟨constVAdd ℝ E v, ⟨hv, by simpa using hn⟩, by simp⟩

/-- `Γ ∩ translations` is the group of translation vectors of `Γ`. -/
noncomputable def translationsEquiv (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) :
    Additive (euclTranslations.subgroupOf Γ) ≃+ translationVectors Γ := by
  refine AddEquiv.ofBijective
    ({ toFun := fun γ => ⟨((Additive.toMul γ : euclTranslations.subgroupOf Γ) : E ≃ᵃⁱ[ℝ] E) 0, ?_⟩
       map_zero' := rfl
       map_add' := ?_ } : Additive (euclTranslations.subgroupOf Γ) →+ translationVectors Γ)
    ⟨?_, ?_⟩
  · have hT := Subgroup.mem_subgroupOf.mp (Additive.toMul γ).2
    show constVAdd ℝ E _ ∈ Γ
    obtain ⟨v, hv⟩ := mem_euclTranslations_iff.mp hT
    rw [hv]
    convert (Additive.toMul γ).1.2
    · simp [hv]
  · intro a b
    apply Subtype.ext
    have ha := Subgroup.mem_subgroupOf.mp (Additive.toMul a).2
    simp only [toMul_add, Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply,
      AddSubgroup.coe_add]
    rw [apply_eq_add_of_mem_euclTranslations ha, add_comm]
  · intro a b hab
    have ha := Subgroup.mem_subgroupOf.mp (Additive.toMul a).2
    have hb := Subgroup.mem_subgroupOf.mp (Additive.toMul b).2
    have h0 := congrArg Subtype.val hab
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h0
    have : (Additive.toMul a : euclTranslations.subgroupOf Γ) = Additive.toMul b := by
      apply Subtype.ext
      apply Subtype.ext
      ext x
      rw [apply_eq_add_of_mem_euclTranslations ha, apply_eq_add_of_mem_euclTranslations hb, h0]
    simpa using congrArg Additive.ofMul this
  · rintro ⟨v, hv⟩
    refine ⟨Additive.ofMul ⟨⟨constVAdd ℝ E v, hv⟩, ?_⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (constVAdd_mem_euclTranslations v)
    · apply Subtype.ext
      simp

/-- **The translation vectors of a discrete `Γ` form a `ℤ`-lattice in their `ℝ`-span.** -/
theorem translationVectors_isZLattice {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} [FiniteDimensional ℝ E]
    (hΓ : IsDiscreteEucl Γ) :
    letI : DiscreteTopology (AddSubgroup.toIntSubmodule (translationVectors Γ)) :=
      discreteTopology_translationVectors hΓ
    IsZLattice ℝ (spanLattice (AddSubgroup.toIntSubmodule (translationVectors Γ))) := by
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule (translationVectors Γ)) :=
    discreteTopology_translationVectors hΓ
  infer_instance

/-- **… of `ℤ`-rank the dimension of that span.** -/
theorem finrank_translationVectors {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} [FiniteDimensional ℝ E]
    (hΓ : IsDiscreteEucl Γ) :
    finrank ℤ (AddSubgroup.toIntSubmodule (translationVectors Γ)) =
      finrank ℝ (span ℝ (translationVectors Γ : Set E)) := by
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule (translationVectors Γ)) :=
    discreteTopology_translationVectors hΓ
  exact discreteSubmodule_finrank _

/-- **Inhabitant (kb/0011):** the cyclic group generated by a translation is discrete. -/
theorem isDiscreteEucl_zpowers_constVAdd (v : E) :
    IsDiscreteEucl (Subgroup.zpowers (constVAdd ℝ E v)) := by
  intro x R
  have hpow : ∀ k : ℤ, constVAdd ℝ E v ^ k = constVAdd ℝ E (k • v) := by
    intro k
    let f : Multiplicative E →* (E ≃ᵃⁱ[ℝ] E) :=
      { toFun := fun w => constVAdd ℝ E (Multiplicative.toAdd w)
        map_one' := constVAdd_zero
        map_mul' := fun a b => constVAdd_add _ _ }
    have := map_zpow f (Multiplicative.ofAdd v) k
    simpa [f] using this.symm
  by_cases hv : v = 0
  · refine (Set.finite_singleton (1 : E ≃ᵃⁱ[ℝ] E)).subset ?_
    rintro γ ⟨hγ, -⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
    rw [hpow, hv, smul_zero, constVAdd_zero]
    rfl
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ((Set.finite_Icc (-⌈R / ‖v‖⌉) ⌈R / ‖v‖⌉).image
      fun k => constVAdd ℝ E v ^ k).subset ?_
    rintro γ ⟨hγ, hd⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
    refine ⟨k, ?_, rfl⟩
    rw [hpow, coe_constVAdd] at hd
    simp only [vadd_eq_add] at hd
    rw [dist_add_self_left, norm_zsmul ℝ, Real.norm_eq_abs] at hd
    have hk : |(k : ℝ)| ≤ R / ‖v‖ := (le_div_iff₀ hn).mpr hd
    have hc := Int.le_ceil (R / ‖v‖)
    rw [abs_le] at hk
    constructor
    · have : (-(⌈R / ‖v‖⌉ : ℝ)) ≤ k := by linarith
      exact_mod_cast this
    · have : (k : ℝ) ≤ ⌈R / ‖v‖⌉ := by linarith
      exact_mod_cast this

/-- **Sanity check of the definition:** the full translation group of a nontrivial `E` is not
discrete. -/
theorem not_isDiscreteEucl_euclTranslations [Nontrivial E] :
    ¬ IsDiscreteEucl (euclTranslations (E := E)) := by
  intro h
  have hinf : (closedBall (0 : E) 1).Infinite :=
    infinite_of_mem_nhds 0 (closedBall_mem_nhds 0 one_pos)
  refine hinf (((h 0 1).image fun γ => γ 0).subset fun v hv => ?_)
  exact ⟨constVAdd ℝ E v, ⟨constVAdd_mem_euclTranslations v, by simpa using hv⟩, by simp⟩

/-- **If the linear parts of `Γ` form a finite group, `Γ ∩ translations` has finite index
in `Γ`.** -/
theorem finiteIndex_euclTranslations {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hfin : (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E)).Finite) :
    (euclTranslations.subgroupOf Γ).FiniteIndex := by
  haveI : Finite (euclLinearPart.restrict Γ).range := by
    rw [MonoidHom.restrict_range]
    exact hfin.to_subtype
  rw [euclTranslations, ← MonoidHom.ker_restrict]
  infer_instance

/-- **Discrete linear parts are finite** (Barbot l.1727: "if `L(Γ)` is discrete, it is finite"). -/
theorem finite_linearParts_of_isOpDiscrete [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (h : IsOpDiscrete (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E))) :
    (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E)).Finite :=
  finite_of_isOpDiscrete _ h

end Isom

/-! ### 4. Bieberbach's first theorem, as a named hypothesis -/

section BieberbachI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `U` is `Γ`-invariant. -/
def IsInvariantSubspace (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) (U : AffineSubspace ℝ E) : Prop :=
  ∀ γ ∈ Γ, ∀ x, γ x ∈ U ↔ x ∈ U

/-- Every element of `Γ'` acts on `U` as a translation by a vector of `U`'s direction. -/
def ActsByTranslationsOn (Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)) (U : AffineSubspace ℝ E) : Prop :=
  ∀ γ ∈ Γ', ∃ v ∈ U.direction, ∀ x ∈ U, γ x = v +ᵥ x

/-- `Γ'` acts effectively on `U`: only the identity fixes `U` pointwise. -/
def ActsEffectivelyOn (Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)) (U : AffineSubspace ℝ E) : Prop :=
  ∀ γ ∈ Γ', (∀ x ∈ U, γ x = x) → γ = 1

/-- The translation vectors of `Γ'` on `U`: the `v` such that some `γ ∈ Γ'` is `x ↦ v +ᵥ x` on
`U`. -/
def translationVectorsOn (Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)) (U : AffineSubspace ℝ E) : Set E :=
  {v | ∃ γ ∈ Γ', ∀ y ∈ U, γ y = v +ᵥ y}

/-- The conclusion of Bieberbach's first theorem for `Γ`, in its WEAKEST form (l.2305,
l.2877–2879): a nonempty `Γ`-invariant affine subspace `U` and a finite-index subgroup `Γ'`
acting effectively by translations on `U`. The uses at l.2611–2614 and l.2889–2891 need the
maximal form, those at l.1737–1749 and l.1772–1775 the cocompact one; both are proved from this
one (`bieberbachMaxConclusion_of_bieberbachConclusion`,
`bieberbachCocompactConclusion_of_bieberbachMaxConclusion`). -/
def BieberbachConclusion (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ IsInvariantSubspace Γ U ∧
    ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ActsByTranslationsOn Γ' U ∧ ActsEffectivelyOn Γ' U

variable (E) in
/-- **Bieberbach's first theorem** (external, DEC-36; NOT proved here): every discrete subgroup
of `Isom(E)` satisfies `BieberbachConclusion`. -/
def BieberbachI [FiniteDimensional ℝ E] : Prop :=
  ∀ Γ : Subgroup (E ≃ᵃⁱ[ℝ] E), IsDiscreteEucl Γ → BieberbachConclusion Γ

/-- **"Unipotent elements of `Isom(U)` are translations"** (Barbot l.1733–1734), in the ambient
space: if `Γ'` preserves `U` and the linear part of every `γ ∈ Γ'` is unipotent on the direction
of `U`, then `Γ'` acts on `U` by translations. -/
theorem actsByTranslationsOn_of_unipotent {Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)} {U : AffineSubspace ℝ E}
    (hU : IsInvariantSubspace Γ' U)
    (hunip : ∀ γ ∈ Γ', ∃ m : ℕ, ∀ w ∈ U.direction,
      (((γ.linearIsometryEquiv.toLinearEquiv : E →ₗ[ℝ] E) - 1) ^ m) w = 0) :
    ActsByTranslationsOn Γ' U := by
  intro γ hγ
  rcases (U : Set E).eq_empty_or_nonempty with hE | ⟨x₀, hx₀⟩
  · refine ⟨0, U.direction.zero_mem, fun x hx => ?_⟩
    exact absurd hx (by simp [← SetLike.mem_coe, hE])
  obtain ⟨m, hm⟩ := hunip γ hγ
  have hγx₀ : γ x₀ ∈ U := (hU γ hγ x₀).2 hx₀
  refine ⟨γ x₀ -ᵥ x₀, AffineSubspace.vsub_mem_direction hγx₀ hx₀, fun x hx => ?_⟩
  have hfix : γ.linearIsometryEquiv (x -ᵥ x₀) = x -ᵥ x₀ :=
    linearIsometry_apply_eq_self_of_unipotent γ.linearIsometryEquiv.toLinearIsometry m _
      (hm _ (AffineSubspace.vsub_mem_direction hx hx₀))
  have := γ.map_vadd x₀ (x -ᵥ x₀)
  rw [vsub_vadd, hfix] at this
  rw [this]
  simp only [vsub_eq_sub, vadd_eq_add]
  abel

/-- **The case of finite linear parts**, proved: `U = E` and `Γ' = Γ ∩ translations`.
Discreteness is not used. -/
theorem bieberbachConclusion_of_finite_linearParts {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hfin : (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E)).Finite) : BieberbachConclusion Γ := by
  refine ⟨⊤, ⟨0, AffineSubspace.mem_top ℝ E 0⟩, fun _ _ _ => by simp, Γ ⊓ euclTranslations,
    inf_le_left, ?_, ?_, ?_⟩
  · rw [Subgroup.inf_subgroupOf_left]
    exact finiteIndex_euclTranslations hfin
  · intro γ hγ
    refine ⟨γ 0, by simp, fun x _ => ?_⟩
    rw [apply_eq_add_of_mem_euclTranslations hγ.2 x, vadd_eq_add, add_comm]
  · intro γ hγ hfix
    ext x
    exact hfix x (AffineSubspace.mem_top ℝ E x)

/-- `BieberbachI` holds whenever `O(E)` is finite. -/
theorem bieberbachI_of_finite [FiniteDimensional ℝ E] (h : Finite (E ≃ₗᵢ[ℝ] E)) : BieberbachI E :=
  fun _ _ => bieberbachConclusion_of_finite_linearParts (Set.toFinite _)

/-- In dimension at most one, `O(E)` is finite (it is `{± 1}`). -/
theorem finite_linearIsometryEquiv_of_finrank_le_one [FiniteDimensional ℝ E]
    (h : finrank ℝ E ≤ 1) : Finite (E ≃ₗᵢ[ℝ] E) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · have hz := (finrank_zero_iff_forall_zero (K := ℝ) (V := E)).mp h0
    haveI : Subsingleton (E ≃ₗᵢ[ℝ] E) := ⟨fun g g' => by ext x; rw [hz (g x), hz (g' x)]⟩
    infer_instance
  · obtain ⟨x₀, hx₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := E)).mp
      (by rw [h1]; exact one_pos)
    have hinj : Function.Injective (fun g : E ≃ₗᵢ[ℝ] E => g x₀) := by
      intro g g' hgg
      ext y
      obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hx₀ y
      simp only at hgg
      rw [map_smul, map_smul, hgg]
    have himg : range (fun g : E ≃ₗᵢ[ℝ] E => g x₀) ⊆ {x₀, -x₀} := by
      rintro _ ⟨g, rfl⟩
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one h1 hx₀ (g x₀)
      have hn : ‖c‖ * ‖x₀‖ = ‖x₀‖ := by rw [← norm_smul, hc, LinearIsometryEquiv.norm_map]
      have hc1 : |c| = 1 := by
        have := norm_ne_zero_iff.mpr hx₀
        rw [Real.norm_eq_abs] at hn
        field_simp at hn
        exact hn
      rcases (abs_eq zero_le_one).mp hc1 with rfl | rfl
      · left; simp only at hc ⊢; rw [← hc, one_smul]
      · right; simp only at hc ⊢; rw [← hc, neg_one_smul]; exact mem_singleton _
    haveI : Finite (range (fun g : E ≃ₗᵢ[ℝ] E => g x₀)) :=
      ((Set.toFinite {x₀, -x₀}).subset himg).to_subtype
    exact Finite.of_injective_finite_range hinj

/-- **Non-vacuity witness (kb/0012):** `BieberbachI` holds in dimension at most one — in
particular on the line `EuclideanSpace ℝ (Fin 1)`. -/
theorem bieberbachI_of_finrank_le_one [FiniteDimensional ℝ E] (h : finrank ℝ E ≤ 1) :
    BieberbachI E :=
  bieberbachI_of_finite (finite_linearIsometryEquiv_of_finrank_le_one h)

theorem bieberbachI_euclideanSpace_fin_one : BieberbachI (EuclideanSpace ℝ (Fin 1)) :=
  bieberbachI_of_finrank_le_one (by simp)

/-- **A discrete group acting effectively by translations on `U` is `ℤᵏ`, `k` the dimension of
the span of its translation vectors**, which lies in the direction of `U`. -/
theorem virtuallyFree_of_actsByTranslationsOn [FiniteDimensional ℝ E]
    {Γ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hle : Γ' ≤ Γ)
    {U : AffineSubspace ℝ E} (hU : (U : Set E).Nonempty) (htr : ActsByTranslationsOn Γ' U)
    (heff : ActsEffectivelyOn Γ' U) :
    Nonempty (Additive Γ' ≃+ (Fin (finrank ℝ (span ℝ (translationVectorsOn Γ' U))) →₀ ℤ)) ∧
      span ℝ (translationVectorsOn Γ' U) ≤ U.direction := by
  obtain ⟨x₀, hx₀⟩ := hU
  have hdisp : ∀ γ ∈ Γ', ∀ x ∈ U, γ x = (γ x₀ -ᵥ x₀) +ᵥ x := by
    intro γ hγ x hx
    obtain ⟨v, -, hv⟩ := htr γ hγ
    rw [hv x hx, hv x₀ hx₀, vadd_vsub]
  have hmem : ∀ γ ∈ Γ', γ x₀ ∈ U := by
    intro γ hγ
    obtain ⟨v, hv, hvx⟩ := htr γ hγ
    rw [hvx x₀ hx₀]
    exact AffineSubspace.vadd_mem_of_mem_direction hv hx₀
  have htv : translationVectorsOn Γ' U = {v | ∃ γ ∈ Γ', v = γ x₀ -ᵥ x₀} := by
    ext v
    constructor
    · rintro ⟨γ, hγ, hv⟩
      refine ⟨γ, hγ, ?_⟩
      rw [hv x₀ hx₀, vadd_vsub]
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, hdisp γ hγ⟩
  refine ⟨?_, ?_⟩
  swap
  · rw [htv, span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    exact AffineSubspace.vsub_mem_direction (hmem γ hγ) hx₀
  let φ : Additive Γ' →+ E :=
    { toFun := fun γ => ((Additive.toMul γ : Γ') : E ≃ᵃⁱ[ℝ] E) x₀ -ᵥ x₀
      map_zero' := by simp
      map_add' := by
        intro a b
        simp only [toMul_add, Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply]
        rw [hdisp _ (Additive.toMul a).2 _ (hmem _ (Additive.toMul b).2)]
        simp only [vsub_eq_sub, vadd_eq_add]
        abel }
  have hφ : ∀ γ, φ γ = ((Additive.toMul γ : Γ') : E ≃ᵃⁱ[ℝ] E) x₀ -ᵥ x₀ := fun _ => rfl
  have hrange : Set.range φ = translationVectorsOn Γ' U := by
    rw [htv]
    ext v
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨_, (Additive.toMul γ).2, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨Additive.ofMul ⟨γ, hγ⟩, rfl⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hφ, vsub_eq_zero_iff_eq] at ha
    have h1 := heff _ (Additive.toMul a).2 (fun x hx => by
      rw [hdisp _ (Additive.toMul a).2 x hx, ha, vsub_self, zero_vadd])
    have : Additive.toMul a = 1 := Subtype.ext h1
    simpa using congrArg Additive.ofMul this
  have hfin : ∀ R : ℝ, {g : Γ' | ‖φ (Additive.ofMul g)‖ ≤ R}.Finite := by
    intro R
    refine ((hΓ x₀ R).preimage Subtype.val_injective.injOn).subset ?_
    intro g hg
    refine ⟨hle g.2, ?_⟩
    simpa [hφ, dist_eq_norm, vsub_eq_sub] using hg
  rw [← hrange]
  exact exists_addEquiv_finsupp_span φ hinj hfin

/-- **From the conclusion of Bieberbach's theorem to "virtually `ℤᵏ`"**, with the sharp bound:
if `Γ` is discrete and satisfies `BieberbachConclusion`, it has a finite-index subgroup
isomorphic to `ℤᵏ`, `k ≤ dim U` for a nonempty `Γ`-invariant affine subspace `U` (l.1745–1749
reasons with `dim U`). -/
theorem virtuallyFree_le_finrank_direction [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hC : BieberbachConclusion Γ) :
    ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ IsInvariantSubspace Γ U ∧
      ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
        ∃ k ≤ finrank ℝ U.direction, Nonempty (Additive Γ' ≃+ (Fin k →₀ ℤ)) := by
  obtain ⟨U, hU, hinv, Γ', hle, hfi, htr, heff⟩ := hC
  obtain ⟨he, hspan⟩ := virtuallyFree_of_actsByTranslationsOn hΓ hle hU htr heff
  exact ⟨U, hU, hinv, Γ', hle, hfi, _, Submodule.finrank_mono hspan, he⟩

/-- **From the conclusion of Bieberbach's theorem to "virtually `ℤᵏ`"**: if `Γ` is discrete and
satisfies `BieberbachConclusion`, it has a finite-index subgroup isomorphic to `ℤᵏ`,
`k ≤ dim E`. -/
theorem virtuallyFree_of_bieberbachConclusion [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hC : BieberbachConclusion Γ) :
    ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ k ≤ finrank ℝ E, Nonempty (Additive Γ' ≃+ (Fin k →₀ ℤ)) := by
  obtain ⟨U, -, -, Γ', hle, hfi, k, hk, he⟩ := virtuallyFree_le_finrank_direction hΓ hC
  exact ⟨Γ', hle, hfi, k, hk.trans (Submodule.finrank_le _), he⟩

/-- **Barbot's "version of Bieberbach's Theorem"** (l.1723–1725), conditional on `BieberbachI`:
a discrete group of isometries of a Euclidean space contains a finite-index free abelian
subgroup of finite rank. -/
theorem virtuallyFree_of_bieberbachI [FiniteDimensional ℝ E] (hB : BieberbachI E)
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) :
    ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ k ≤ finrank ℝ E, Nonempty (Additive Γ' ≃+ (Fin k →₀ ℤ)) :=
  virtuallyFree_of_bieberbachConclusion hΓ (hB Γ hΓ)

/-- **The first case of Barbot's proof, unconditional** (l.1727–1729): if `Γ` is discrete and
`L(Γ)` is discrete in `O(E)`, then `L(Γ)` is finite, `Γ ∩ translations` has finite index, and
`Γ` is virtually `ℤᵏ`. -/
theorem virtuallyFree_of_isOpDiscrete_linearParts [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ)
    (hL : IsOpDiscrete (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E))) :
    ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ k ≤ finrank ℝ E, Nonempty (Additive Γ' ≃+ (Fin k →₀ ℤ)) :=
  virtuallyFree_of_bieberbachConclusion hΓ
    (bieberbachConclusion_of_finite_linearParts (finite_linearParts_of_isOpDiscrete hL))


/-! ### 5. The upgrades the downstream uses need: normal, maximal, cocompact -/

/-- **The maximal form** (for l.2611–2614 and l.2889–2891): a finite-index subgroup `Γ'`,
**normal** in `Γ`, and a nonempty `Γ`-invariant affine subspace `U` on which `Γ'` acts
effectively by translations, which is the **greatest** affine subspace on which `Γ'` acts by
translations. -/
def BieberbachMaxConclusion (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).Normal ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
    ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ IsInvariantSubspace Γ U ∧
      ActsByTranslationsOn Γ' U ∧ ActsEffectivelyOn Γ' U ∧
      ∀ U' : AffineSubspace ℝ E, ActsByTranslationsOn Γ' U' → U' ≤ U

/-- **The cocompact form** (for l.1737–1749 and l.1772–1775): a finite-index subgroup `Γ'`,
normal in `Γ`, and a nonempty `Γ`-invariant affine subspace `U` on which `Γ'` acts effectively by
translations whose vectors **span** the direction of `U`. -/
def BieberbachCocompactConclusion (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Prop :=
  ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).Normal ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
    ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧ IsInvariantSubspace Γ U ∧
      ActsByTranslationsOn Γ' U ∧ ActsEffectivelyOn Γ' U ∧
      U.direction = span ℝ (translationVectorsOn Γ' U)

/-- A translation of `U` by `v` iterates: `γ ^ k = (k • v) +ᵥ ·` on `U`. -/
theorem pow_apply_of_translation {γ : E ≃ᵃⁱ[ℝ] E} {U : AffineSubspace ℝ E} {v : E}
    (hv : v ∈ U.direction) (h : ∀ x ∈ U, γ x = v +ᵥ x) :
    ∀ k : ℕ, ∀ x ∈ U, (γ ^ k) x = (k • v) +ᵥ x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    rw [pow_succ, AffineIsometryEquiv.coe_mul, Function.comp_apply, h x hx,
      ih _ (AffineSubspace.vadd_mem_of_mem_direction hv hx)]
    simp only [vadd_eq_add, succ_nsmul]
    abel

/-- **The translation vector of an isometry is unique**: if `γ` translates the orbit of `y` by
`v` and the orbit of `x` by `w`, then `v = w` (the difference grows linearly, while `γ ^ k`
preserves `dist y x`). -/
theorem eq_of_pow_apply {γ : E ≃ᵃⁱ[ℝ] E} {x y v w : E}
    (hy : ∀ k : ℕ, (γ ^ k) y = (k • v) +ᵥ y) (hx : ∀ k : ℕ, (γ ^ k) x = (k • w) +ᵥ x) :
    v = w := by
  by_contra hne
  have hpos : 0 < ‖v - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * ‖y - x‖ / ‖v - w‖)
  have hd := (γ ^ k).dist_map y x
  rw [hy k, hx k, dist_eq_norm, dist_eq_norm] at hd
  have h1 : (k • v +ᵥ y) - (k • w +ᵥ x) = (k : ℝ) • (v - w) + (y - x) := by
    simp only [vadd_eq_add, smul_sub, Nat.cast_smul_eq_nsmul]
    abel
  have h2 : ‖(k : ℝ) • (v - w)‖ ≤ 2 * ‖y - x‖ := by
    calc ‖(k : ℝ) • (v - w)‖ = ‖((k : ℝ) • (v - w) + (y - x)) - (y - x)‖ := by
          rw [add_sub_cancel_right]
      _ ≤ ‖(k : ℝ) • (v - w) + (y - x)‖ + ‖y - x‖ := norm_sub_le _ _
      _ = 2 * ‖y - x‖ := by rw [← h1, hd]; ring
  rw [norm_smul, Real.norm_natCast] at h2
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- The translation vectors on two subspaces on which `γ` acts by translations agree. -/
theorem translation_vector_unique {γ : E ≃ᵃⁱ[ℝ] E} {U U' : AffineSubspace ℝ E} {v w x y : E}
    (hv : v ∈ U.direction) (hU : ∀ z ∈ U, γ z = v +ᵥ z) (hy : y ∈ U)
    (hw : w ∈ U'.direction) (hU' : ∀ z ∈ U', γ z = w +ᵥ z) (hx : x ∈ U') : v = w :=
  eq_of_pow_apply (fun k => pow_apply_of_translation hv hU k y hy)
    (fun k => pow_apply_of_translation hw hU' k x hx)

/-- Conjugation inside `Γ` preserves a subgroup `N ≤ Γ` normal in `Γ`. -/
theorem conj_mem_of_normal {Γ N : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hle : N ≤ Γ)
    (hN : (N.subgroupOf Γ).Normal) {g γ : E ≃ᵃⁱ[ℝ] E} (hg : g ∈ Γ) (hγ : γ ∈ N) :
    g * γ * g⁻¹ ∈ N := by
  have := hN.conj_mem ⟨γ, hle hγ⟩ (Subgroup.mem_subgroupOf.mpr hγ) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp this

/-- **The translation locus** of `N` through `x₀`: the points that every `γ ∈ N` moves by the
same vector as `x₀`. It is an affine subspace (the intersection of the `Min`-sets). -/
def translationLocus (N : Subgroup (E ≃ᵃⁱ[ℝ] E)) (x₀ : E) : AffineSubspace ℝ E where
  carrier := {x | ∀ γ ∈ N, γ x = (γ x₀ -ᵥ x₀) +ᵥ x}
  smul_vsub_vadd_mem := by
    intro c p1 p2 p3 h1 h2 h3 γ hγ
    have h12 : γ.linearIsometryEquiv (p1 -ᵥ p2) = p1 -ᵥ p2 := by
      rw [AffineIsometryEquiv.map_vsub, h1 γ hγ, h2 γ hγ, vadd_vsub_vadd_cancel_left]
    rw [AffineIsometryEquiv.map_vadd, h3 γ hγ, map_smul, h12]
    simp only [vadd_eq_add]
    abel

theorem mem_translationLocus {N : Subgroup (E ≃ᵃⁱ[ℝ] E)} {x₀ x : E} :
    x ∈ translationLocus N x₀ ↔ ∀ γ ∈ N, γ x = (γ x₀ -ᵥ x₀) +ᵥ x := Iff.rfl

/-- **Upgrade 1 (maximal and normal).** The weak conclusion yields the maximal form: replace
`Γ'` by its normal core in `Γ`, and `U` by the translation locus of that core. Discreteness is
not used. -/
theorem bieberbachMaxConclusion_of_bieberbachConclusion {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (h : BieberbachConclusion Γ) : BieberbachMaxConclusion Γ := by
  obtain ⟨U, ⟨x₀, hx₀⟩, hUinv, Γ', hle, hfi, htr, heff⟩ := h
  set H := Γ'.subgroupOf Γ with hH
  set N : Subgroup (E ≃ᵃⁱ[ℝ] E) := H.normalCore.map Γ.subtype with hNdef
  have hNΓ : N ≤ Γ := Subgroup.map_subtype_le _
  have hNΓ' : N ≤ Γ' := by
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (H.normalCore_le hg)
  have hNsub : N.subgroupOf Γ = H.normalCore :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hnorm : (N.subgroupOf Γ).Normal := by rw [hNsub]; infer_instance
  have hfiN : (N.subgroupOf Γ).FiniteIndex := by rw [hNsub]; infer_instance
  set M := translationLocus N x₀ with hMdef
  have hγx₀ : ∀ γ ∈ N, γ x₀ ∈ U := fun γ hγ => (hUinv γ (hNΓ hγ) x₀).2 hx₀
  have hUM : ∀ x ∈ U, x ∈ M := by
    intro x hx γ hγ
    obtain ⟨v, -, hv⟩ := htr γ (hNΓ' hγ)
    rw [hv x hx, hv x₀ hx₀, vadd_vsub]
  have hx₀M : x₀ ∈ M := hUM x₀ hx₀
  have hτM : ∀ γ ∈ N, γ x₀ -ᵥ x₀ ∈ M.direction := fun γ hγ =>
    AffineSubspace.vsub_mem_direction (hUM _ (hγx₀ γ hγ)) hx₀M
  have htrM : ActsByTranslationsOn N M := fun γ hγ => ⟨_, hτM γ hγ, fun x hx => hx γ hγ⟩
  have hgreat : ∀ U' : AffineSubspace ℝ E, ActsByTranslationsOn N U' → U' ≤ M := by
    intro U' h' y hy γ hγ
    obtain ⟨v, hv, hvy⟩ := h' γ hγ
    have := translation_vector_unique hv hvy hy (hτM γ hγ) (fun z hz => hz γ hγ) hx₀M
    rw [hvy y hy, this]
  have hmap : ∀ g ∈ Γ, ∀ x ∈ M, g x ∈ M := by
    intro g hg x hx γ hγ
    have hδ : g⁻¹ * γ * g⁻¹⁻¹ ∈ N := conj_mem_of_normal hNΓ hnorm (Γ.inv_mem hg) hγ
    rw [inv_inv] at hδ
    have hpow : ∀ k : ℕ, (γ ^ k) (g x) =
        (k • g.linearIsometryEquiv ((g⁻¹ * γ * g) x₀ -ᵥ x₀)) +ᵥ g x := by
      intro k
      have e : γ ^ k * g = g * (g⁻¹ * γ * g) ^ k := by
        have := conj_pow (a := g⁻¹) (b := γ) (i := k)
        rw [inv_inv] at this
        rw [this]
        group
      have : (γ ^ k) (g x) = (g * (g⁻¹ * γ * g) ^ k) x := by
        rw [← e, AffineIsometryEquiv.coe_mul, Function.comp_apply]
      rw [this, AffineIsometryEquiv.coe_mul, Function.comp_apply,
        pow_apply_of_translation (hτM _ hδ) (fun z hz => hz _ hδ) k x hx,
        AffineIsometryEquiv.map_vadd, map_nsmul]
    have hpow₀ := fun k => pow_apply_of_translation (hτM γ hγ) (fun z hz => hz γ hγ) k x₀ hx₀M
    have := eq_of_pow_apply hpow hpow₀
    have h1 := hpow 1
    simp only [pow_one, one_smul] at h1
    rw [h1, this]
  refine ⟨N, hNΓ, hnorm, hfiN, M, ⟨x₀, hx₀M⟩, ?_, htrM, ?_, hgreat⟩
  · intro g hg x
    refine ⟨fun hgx => ?_, hmap g hg x⟩
    have := hmap g⁻¹ (Γ.inv_mem hg) _ hgx
    rwa [AffineIsometryEquiv.coe_inv, AffineIsometryEquiv.symm_apply_apply] at this
  · intro γ hγ hfix
    exact heff γ (hNΓ' hγ) fun x hx => hfix x (hUM x hx)

/-- **The maximal subspace contains every direction fixed by `L(Γ')`** — the step of l.2612–2614
("`SO(n−1)` … preserves a timelike direction `Δ₀`: it follows that `U` is timelike"). -/
theorem mem_direction_of_fixed {Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)} {U : AffineSubspace ℝ E}
    (hU : (U : Set E).Nonempty) (htr : ActsByTranslationsOn Γ' U)
    (hmax : ∀ U' : AffineSubspace ℝ E, ActsByTranslationsOn Γ' U' → U' ≤ U) {w : E}
    (hw : ∀ γ ∈ Γ', γ.linearIsometryEquiv w = w) : w ∈ U.direction := by
  obtain ⟨x, hx⟩ := hU
  set D := U.direction ⊔ span ℝ {w}
  have hfixU : ∀ γ ∈ Γ', ∀ u ∈ U.direction, γ.linearIsometryEquiv u = u := by
    intro γ hγ u hu
    obtain ⟨v, -, hv⟩ := htr γ hγ
    have hux : u +ᵥ x ∈ U := AffineSubspace.vadd_mem_of_mem_direction hu hx
    have := γ.map_vadd x u
    rw [hv _ hux, hv x hx] at this
    simp only [vadd_eq_add] at this
    have : γ.linearIsometryEquiv u = u := by
      have h' : γ.linearIsometryEquiv u + (v + x) = v + (u + x) := this.symm
      calc γ.linearIsometryEquiv u = (γ.linearIsometryEquiv u + (v + x)) - (v + x) := by abel
        _ = (v + (u + x)) - (v + x) := by rw [h']
        _ = u := by abel
    exact this
  have hfixD : ∀ γ ∈ Γ', ∀ d ∈ D, γ.linearIsometryEquiv d = d := by
    intro γ hγ d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hd
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, map_smul, hfixU γ hγ a ha, hw γ hγ]
  have htr' : ActsByTranslationsOn Γ' (AffineSubspace.mk' x D) := by
    intro γ hγ
    obtain ⟨v, hv, hvx⟩ := htr γ hγ
    refine ⟨v, ?_, fun y hy => ?_⟩
    · rw [AffineSubspace.direction_mk']
      exact Submodule.mem_sup_left hv
    · rw [AffineSubspace.mem_mk'] at hy
      have := γ.map_vadd x (y -ᵥ x)
      rw [vsub_vadd, hfixD γ hγ _ hy, hvx x hx] at this
      rw [this]
      simp only [vsub_eq_sub, vadd_eq_add]
      abel
  have hle := hmax _ htr'
  have hwx : w +ᵥ x ∈ U :=
    hle (AffineSubspace.vadd_mem_mk' x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)))
  simpa using AffineSubspace.vsub_mem_direction hwx hx


/-- **Upgrade 2 (cocompact).** The maximal form yields the cocompact form, for the same `Γ'`:
`U` is the translate of `W = span (Γ'-translation vectors)` through the barycentre of one
`Γ`-orbit of representatives of `Γ / Γ'`, which is `Γ`-invariant modulo `W`. Discreteness is not
used. -/
theorem bieberbachCocompactConclusion_of_bieberbachMaxConclusion {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (h : BieberbachMaxConclusion Γ) : BieberbachCocompactConclusion Γ := by
  classical
  obtain ⟨N, hle, hnorm, hfi, M, ⟨x₀, hx₀⟩, hinv, htr, heff, -⟩ := h
  have hτ : ∀ γ ∈ N, ∀ y ∈ M, γ y = (γ x₀ -ᵥ x₀) +ᵥ y := by
    intro γ hγ y hy
    obtain ⟨v, -, hv⟩ := htr γ hγ
    rw [hv y hy, hv x₀ hx₀, vadd_vsub]
  have hmemM : ∀ g ∈ Γ, ∀ y ∈ M, g y ∈ M := fun g hg y hy => (hinv g hg y).2 hy
  set W : Submodule ℝ E := span ℝ {v | ∃ γ ∈ N, v = γ x₀ -ᵥ x₀} with hW
  have hgen : ∀ γ ∈ N, γ x₀ -ᵥ x₀ ∈ W := fun γ hγ => subset_span ⟨γ, hγ, rfl⟩
  have hWM : W ≤ M.direction := span_le.mpr (by
    rintro _ ⟨γ, hγ, rfl⟩
    exact AffineSubspace.vsub_mem_direction (hmemM γ (hle hγ) x₀ hx₀) hx₀)
  have hLW : ∀ g ∈ Γ, ∀ w ∈ W, g.linearIsometryEquiv w ∈ W := by
    intro g hg w hw
    have hmap : W.map (g.linearIsometryEquiv.toLinearEquiv : E →ₗ[ℝ] E) ≤ W := by
      rw [hW, Submodule.map_span_le]
      rintro _ ⟨γ, hγ, rfl⟩
      have hδ := conj_mem_of_normal hle hnorm hg hγ
      have e1 : (g * γ * g⁻¹) (g x₀) = g (γ x₀) := by
        simp [AffineIsometryEquiv.coe_mul, AffineIsometryEquiv.coe_inv]
      rw [hτ _ hδ _ (hmemM g hg x₀ hx₀), hτ γ hγ x₀ hx₀, AffineIsometryEquiv.map_vadd] at e1
      have e2 : g.linearIsometryEquiv (γ x₀ -ᵥ x₀) = (g * γ * g⁻¹) x₀ -ᵥ x₀ :=
        (vadd_right_cancel _ e1).symm
      show g.linearIsometryEquiv (γ x₀ -ᵥ x₀) ∈ W
      rw [e2]
      exact hgen _ hδ
    exact hmap ⟨w, hw, rfl⟩
  set K := N.subgroupOf Γ with hK
  haveI := hfi
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  set y : Γ ⧸ K → E := fun q => ((q.out : Γ) : E ≃ᵃⁱ[ℝ] E) x₀ with hy
  have hyM : ∀ q, y q ∈ M := fun q => hmemM _ q.out.2 x₀ hx₀
  have hm : (Fintype.card (Γ ⧸ K) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set a : ℝ := (Fintype.card (Γ ⧸ K) : ℝ)⁻¹ with ha
  have hav : ∀ z : E, a • (Fintype.card (Γ ⧸ K) • z) = z := by
    intro z
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ha, inv_mul_cancel₀ hm, one_smul]
  set c : E := a • ∑ q, y q with hc
  have hc' : c = (a • ∑ q, (y q -ᵥ x₀)) +ᵥ x₀ := by
    simp only [hc, vsub_eq_sub, vadd_eq_add, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, smul_sub, hav]
    abel
  have hcM : c ∈ M := by
    rw [hc']
    exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun q _ => AffineSubspace.vsub_mem_direction (hyM q) hx₀)) hx₀
  have haff : ∀ g : E ≃ᵃⁱ[ℝ] E, g c = a • ∑ q, g (y q) := by
    intro g
    have hz : ∀ z : E, g z = g.linearIsometryEquiv z + g 0 := by
      intro z
      have := g.map_vadd 0 z
      simpa using this
    rw [hz c, hc, map_smul, map_sum, Finset.sum_congr rfl (fun q _ => hz (y q)),
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_add, hav]
  have hkey : ∀ g ∈ Γ, g c -ᵥ c ∈ W := by
    intro g hg
    set g' : Γ := ⟨g, hg⟩ with hg'
    have hq : ∀ q : Γ ⧸ K, g (y q) -ᵥ y (g' • q) ∈ W := by
      intro q
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (g' * q.out)
      have hout : ((g' • q).out : Γ) = g' * q.out * h := by
        have : g' • q = (QuotientGroup.mk (g' * q.out) : Γ ⧸ K) := by
          calc g' • q = g' • (QuotientGroup.mk q.out : Γ ⧸ K) := by rw [QuotientGroup.out_eq']
            _ = _ := rfl
        rw [this]
        exact hh
      have hhN : ((h : Γ) : E ≃ᵃⁱ[ℝ] E) ∈ N := Subgroup.mem_subgroupOf.mp h.2
      have e : y (g' • q) = g.linearIsometryEquiv (((q.out : Γ) : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv
          (((h : Γ) : E ≃ᵃⁱ[ℝ] E) x₀ -ᵥ x₀)) +ᵥ g (y q) := by
        simp only [hy]
        rw [hout]
        simp only [Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply, hg']
        rw [hτ _ hhN x₀ hx₀, AffineIsometryEquiv.map_vadd, AffineIsometryEquiv.map_vadd,
          vadd_vsub]
      rw [e, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
      exact W.neg_mem (hLW g hg _ (hLW _ q.out.2 _ (hgen _ hhN)))
    have hsum : ∑ q, y (g' • q) = ∑ q, y q :=
      Fintype.sum_equiv (MulAction.toPerm g') _ _ (fun q => rfl)
    have e3 : g c -ᵥ c = a • ∑ q, (g (y q) -ᵥ y (g' • q)) := by
      rw [haff g, hc]
      simp only [vsub_eq_sub, Finset.sum_sub_distrib, hsum, smul_sub]
    rw [e3]
    exact W.smul_mem _ (W.sum_mem fun q _ => hq q)
  set U' := AffineSubspace.mk' c W with hU'
  have hU'M : ∀ z ∈ U', z ∈ M := by
    intro z hz
    rw [AffineSubspace.mem_mk'] at hz
    have := AffineSubspace.vadd_mem_of_mem_direction (hWM hz) hcM
    rwa [vsub_vadd] at this
  have hmapU' : ∀ g ∈ Γ, ∀ z ∈ U', g z ∈ U' := by
    intro g hg z hz
    rw [AffineSubspace.mem_mk'] at hz ⊢
    have : g z -ᵥ c = g.linearIsometryEquiv (z -ᵥ c) + (g c -ᵥ c) := by
      rw [AffineIsometryEquiv.map_vsub]
      simp only [vsub_eq_sub]
      abel
    rw [this]
    exact W.add_mem (hLW g hg _ hz) (hkey g hg)
  refine ⟨N, hle, hnorm, hfi, U', AffineSubspace.mk'_nonempty c W, ?_, ?_, ?_, ?_⟩
  · intro g hg z
    refine ⟨fun hgz => ?_, hmapU' g hg z⟩
    have := hmapU' g⁻¹ (Γ.inv_mem hg) _ hgz
    rwa [AffineIsometryEquiv.coe_inv, AffineIsometryEquiv.symm_apply_apply] at this
  · intro γ hγ
    refine ⟨γ x₀ -ᵥ x₀, ?_, fun z hz => hτ γ hγ z (hU'M z hz)⟩
    rw [AffineSubspace.direction_mk']
    exact hgen γ hγ
  · intro γ hγ hfix
    have h0 : γ x₀ -ᵥ x₀ = 0 := by
      have := hfix c (AffineSubspace.self_mem_mk' c W)
      rw [hτ γ hγ c hcM] at this
      simpa [vadd_eq_add] using this
    exact heff γ hγ fun z hz => by rw [hτ γ hγ z hz, h0, zero_vadd]
  · rw [AffineSubspace.direction_mk']
    apply le_antisymm
    · refine span_mono ?_
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, fun z hz => hτ γ hγ z (hU'M z hz)⟩
    · refine span_le.mpr ?_
      rintro v ⟨γ, hγ, hv⟩
      have := hv c (AffineSubspace.self_mem_mk' c W)
      rw [hτ γ hγ c hcM] at this
      rw [(vadd_right_cancel c this).symm]
      exact hgen γ hγ

/-- **`BieberbachI` delivers the maximal form** (for l.2611–2614, l.2877–2891). -/
theorem bieberbachMaxConclusion_of_bieberbachI [FiniteDimensional ℝ E] (hB : BieberbachI E)
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) : BieberbachMaxConclusion Γ :=
  bieberbachMaxConclusion_of_bieberbachConclusion (hB Γ hΓ)

/-- **`BieberbachI` delivers the cocompact form** (for l.1737–1749, l.1772–1775). -/
theorem bieberbachCocompactConclusion_of_bieberbachI [FiniteDimensional ℝ E]
    (hB : BieberbachI E) {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) :
    BieberbachCocompactConclusion Γ :=
  bieberbachCocompactConclusion_of_bieberbachMaxConclusion
    (bieberbachMaxConclusion_of_bieberbachI hB hΓ)

/-- **The rank of the cocompact form is `dim U`** (the "flat torus `Γ' \ U`" of l.1772–1775, in
rank form): for a discrete `Γ` with `BieberbachCocompactConclusion`, a normal finite-index
`Γ' ≅ ℤ^{dim U}` acts effectively by translations on a `Γ`-invariant `U`. -/
theorem virtuallyFree_of_bieberbachCocompactConclusion [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hC : BieberbachCocompactConclusion Γ) :
    ∃ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).Normal ∧
      (Γ'.subgroupOf Γ).FiniteIndex ∧ ∃ U : AffineSubspace ℝ E, (U : Set E).Nonempty ∧
        IsInvariantSubspace Γ U ∧ ActsByTranslationsOn Γ' U ∧
        Nonempty (Additive Γ' ≃+ (Fin (finrank ℝ U.direction) →₀ ℤ)) := by
  obtain ⟨Γ', hle, hn, hfi, U, hU, hinv, htr, heff, hdir⟩ := hC
  obtain ⟨he, -⟩ := virtuallyFree_of_actsByTranslationsOn hΓ hle hU htr heff
  rw [← hdir] at he
  exact ⟨Γ', hle, hn, hfi, U, hU, hinv, htr, he⟩

/-- **Witness (kb/0012)** for the maximal and cocompact forms: they hold whenever the linear
parts are finite, in particular in dimension `≤ 1`. -/
theorem bieberbachMaxConclusion_of_finite_linearParts {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hfin : (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E)).Finite) : BieberbachMaxConclusion Γ :=
  bieberbachMaxConclusion_of_bieberbachConclusion (bieberbachConclusion_of_finite_linearParts hfin)

theorem bieberbachCocompactConclusion_of_finite_linearParts {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (hfin : (Γ.map euclLinearPart : Set (E ≃ₗᵢ[ℝ] E)).Finite) : BieberbachCocompactConclusion Γ :=
  bieberbachCocompactConclusion_of_bieberbachMaxConclusion
    (bieberbachMaxConclusion_of_finite_linearParts hfin)

end BieberbachI

end Causal.Flat
