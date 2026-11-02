import CausalScaffold.Flat.Lox.RestrictOrient
import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Externals
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Restricting to the maximal unipotent subspace: orientation, loxodromics, properness

Steps of Barbot's [10.G] (`GHFspace.tex` l.3389–3403, "up to a linear twisted product, we can
assume that `U` is the entire Minkowski space"), served to `loxo_generic_centralExtension` and
`loxo_generic_torusProduct` (`Flat/Loxodromic.lean`). **No label is marked**: these are steps the
paper takes silently.

* `[10.G]`, `GHFspace.tex:3389–3396`, partial (the restriction steps; **no `sorry`**):
  - `det_eq_one_of_isNilpotent_sub_one`, `det_restrictLin_eq_one_of_unipotent`: a group acting
    unipotently on `U` keeps the orientation of `U`;
  - `exists_restrictsIn_ge`: the index-`≤ 2` subgroup restricting to `U`
    (`Flat.Lox.RestrictOrient`) can be taken to contain any subgroup acting unipotently on `U` —
    in particular `Γ_nd` (`IsMaxUnipotent`);
  - `Restricts.isLoxodromic`: the restriction of a loxodromic element to a timelike invariant `U`
    is loxodromic (its expanding null eigenline lies in `U`);
  - `restrictHom`, `exists_le_restrictGroup_le`: pulling back a finite-index subgroup of the
    restricted group;
  - `proper_restrictGroup`: the restricted group acts properly on `ι⁻¹ Ω`;
  - `le_of_affineMinkEmbedding`: `d₁ ≤ d`;
  - `ccAction_discreteTopology`, `ccAction_mono`: the §8 data make `Γ` discrete, and pass to
    subgroups.

> Assume that $\Gamma$ preserves a timelike affine subspace $\bf U$ […] Then, the quotient of
> ${\bf U} \cap \Omega$ by $\Gamma$ is a flat spacetime $M$ (l.1838–1843, `blem:suspendre`)

Barbot's `n` is `d + 1` (resp. `d₁ + 1` for `U`): `Minkowski d` has `d` spatial dimensions.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (silent) `Γ` acts on `U` by orientation-preserving isometries of `U` | ⚠ on a subgroup `Γ₂` of index `≤ 2` (`exists_restrictsIn_ge`), containing every subgroup unipotent on `U` |

## SCOPE (disclosed)

* `ccAction_discreteTopology` and `continuous_isom_smul_apply'` reprove
  `Flat.Nonloxodromic`'s `discreteTopology_of_ccAction` and `continuous_isom_smul_apply`, which are
  not in this module's import closure (the Nonlox track's file).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
wave 7, package WP-34d-Loxodromic.
-/

namespace Causal.Flat.Lox
open Set Topology Pointwise

variable {d d₁ : ℕ}

/-! ### Unipotent maps have determinant one -/

/-- **A unipotent endomorphism has determinant `1`**: if `f − 1` is nilpotent, the
characteristic polynomial of `f = (f − 1) − (−1)·1` is `(X − 1)ⁿ`. -/
theorem det_eq_one_of_isNilpotent_sub_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {f : Module.End ℝ V} (h : IsNilpotent (f - 1)) :
    LinearMap.det f = 1 := by
  have hc := _root_.IsNilpotent.charpoly_eq_X_pow_finrank h
  have e : f = (f - 1) - (-1 : ℝ) • 1 := by rw [neg_one_smul, sub_neg_eq_add, sub_add_cancel]
  have hcf : f.charpoly = (Polynomial.X - 1) ^ Module.finrank ℝ V := by
    rw [e, LinearMap.charpoly_sub_smul, hc]
    simp [sub_eq_add_neg]
  rw [LinearMap.det_eq_sign_charpoly_coeff, hcf, Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    zero_sub]
  rw [← mul_pow]; norm_num

/-- **A `γ` acting unipotently on `U = range ι` keeps the orientation of `U`**: the restricted
linear part `L_γ` (`restrictLin`) has determinant `1`. -/
theorem det_restrictLin_eq_one_of_unipotent {ι : AffineMinkEmbedding d₁ d} {γ : isom d}
    (h : (fun p => γ • p) '' Set.range ι = Set.range ι)
    (hu : ∃ m : ℕ, ∀ w ∈ ι.range.direction, (pOf (linOf γ) ^ m) w = 0) :
    LinearMap.det (restrictLin ι γ) = 1 := by
  obtain ⟨m, hm⟩ := hu
  refine det_eq_one_of_isNilpotent_sub_one ⟨m, LinearMap.ext fun v => ?_⟩
  have key : ∀ k : ℕ, ∀ v : Minkowski d₁,
      ι.lin (((restrictLin ι γ - 1) ^ k) v) = (pOf (linOf γ) ^ k) (ι.lin v) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, pOf_apply]
      rw [lin_restrictLin h]
  have hdir : ι.lin v ∈ ι.range.direction := by
    rw [AffineMinkEmbedding.range, AffineSubspace.map_direction, AffineSubspace.direction_top,
      Submodule.map_top]
    exact LinearMap.mem_range_self _ _
  apply ι.lin_injective
  rw [key, hm _ hdir, LinearMap.zero_apply, map_zero]

/-- **The restricting subgroup contains every subgroup unipotent on `U`** (the step of
`Flat.Lox.RestrictOrient` refined): if `Γ` preserves `U = range ι` and every element of `N ≤ Γ`
acts unipotently on `U`, there is `Γ₂ ≤ Γ` of finite index (`≤ 2`), restricting to `U`, with
`N ≤ Γ₂` — the kernel of `γ ↦ det L_γ`. -/
theorem exists_restrictsIn_ge (ι : AffineMinkEmbedding d₁ d) {Γ N : Subgroup (isom d)}
    (hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι) (hN : N ≤ Γ)
    (hu : ∀ γ ∈ N, ∃ m : ℕ, ∀ w ∈ ι.range.direction, (pOf (linOf γ) ^ m) w = 0) :
    ∃ Γ₂ : Subgroup (isom d), Γ₂ ≤ Γ ∧ Γ₂.relIndex Γ ≠ 0 ∧ ι.RestrictsIn Γ₂ ∧ N ≤ Γ₂ := by
  classical
  set φ := (restrictDet ι hpres).toHomUnits
  have hφ : ∀ γ : Γ, (φ γ : ℝ) = LinearMap.det (restrictLin ι γ.1) := fun _ => rfl
  have hrange : (φ.range : Set ℝˣ) ⊆ {1, -1} := by
    rintro _ ⟨γ, rfl⟩
    have h2 := det_sq_of_minkQ_preserving (minkQ_restrictLin (hpres _ γ.2))
    rw [← hφ] at h2
    rcases sq_eq_one_iff.1 h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h]; rfl))
  have hfin : (φ.range : Set ℝˣ).Finite := (Set.toFinite _).subset hrange
  have hpos : Nat.card φ.range ≠ 0 := by
    haveI : Finite φ.range := hfin.to_subtype
    exact Nat.card_pos.ne'
  have hrel : (φ.ker.map Γ.subtype).relIndex Γ = φ.ker.index := by
    rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective]
  refine ⟨φ.ker.map Γ.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [hrel, Subgroup.index_ker]; exact hpos
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 : (φ γ : ℝ) = 1 := by rw [(MonoidHom.mem_ker).1 hγ]; rfl
    rw [hφ] at h1
    exact exists_restricts_of_det_eq_one (hpres _ γ.2) h1
  · intro η hη
    have hdet := det_restrictLin_eq_one_of_unipotent (hpres _ (hN hη)) (hu η hη)
    refine ⟨⟨η, hN hη⟩, ?_, rfl⟩
    show φ ⟨η, hN hη⟩ = 1
    exact Units.ext (by rw [hφ]; exact hdet)

/-! ### Loxodromic elements restrict to loxodromic elements -/

/-- **The restriction of a loxodromic element to an invariant timelike `U` is loxodromic**: its
null eigenvector `u` for `λ ≠ 1` splits as `ι.lin a + b`, `b ∈ U^⊥`; `L(γ)` preserves the splitting
and is an isometry of the euclidean `U^⊥`, so `b = 0`, and `a` is a null eigenvector of `L_g`. -/
theorem Restricts.isLoxodromic {ι : AffineMinkEmbedding d₁ d} {γ : isom d} {g : isom d₁}
    (hr : ι.Restricts γ g) (hlox : IsLoxodromic (linOf γ)) : IsLoxodromic (linOf g) := by
  obtain ⟨u, hu0, hq, l, hl, hl1, hAu⟩ := hlox.exists_eigen
  set a := ι.coproj u
  set b := u - ι.lin a
  have hb : b ∈ ι.perp := ι.sub_lin_coproj_mem_perp u
  have hub : u = ι.lin a + b := by simp [b]
  have hLa : linOf γ (ι.lin a) = ι.lin (linOf g a) := (hr.lin a).symm
  have hLb : linOf γ b ∈ ι.perp := hr.linear_mem_perp hb
  -- compare the two decompositions of `L(γ) u = λ u`
  have e : ι.lin (linOf g a) + linOf γ b = ι.lin (l • a) + l • b := by
    rw [← hLa, ← map_add, ← hub, hAu, hub, smul_add, map_smul]
  have e1 : linOf g a = l • a := by
    have := congrArg ι.coproj e
    rw [map_add, map_add, ι.coproj_lin, ι.coproj_lin, ι.coproj_eq_zero_of_mem_perp hLb,
      ι.coproj_eq_zero_of_mem_perp (ι.smul_mem_perp l hb), add_zero, add_zero] at this
    exact this
  have e2 : linOf γ b = l • b := by
    rw [e1] at e; exact add_left_cancel e
  have hb0 : b = 0 := by
    have hQ : minkQ (linOf γ b) = minkQ b := (linOf_mem γ).1 b
    rw [e2, minkQ_smul] at hQ
    have hl2 : l ^ 2 ≠ 1 := fun h2 => hl1 (by
      rcases sq_eq_one_iff.1 h2 with h | h
      · exact h
      · linarith)
    have hQb : minkQ b = 0 := by
      have : (l ^ 2 - 1) * minkQ b = 0 := by rw [sub_mul, one_mul, hQ, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl2)
    by_contra hb0
    exact (ι.minkQ_pos_of_mem_perp hb hb0).ne' hQb
  have hua : u = ι.lin a := by rw [hub, hb0, add_zero]
  have ha0 : a ≠ 0 := fun h0 => hu0 (by rw [hua, h0, map_zero])
  have hqa : minkQ a = 0 := by rw [← ι.minkQ_lin, ← hua, hq]
  exact isLoxodromic_of_null_eigen (linOf_mem g) ha0 hqa hl hl1 e1

/-! ### The restriction hom, and pulling back finite-index subgroups -/

theorem restricts_choose (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (γ : Γ) :
    ι.Restricts (γ : isom d) (Classical.choose (hres γ γ.2)) :=
  Classical.choose_spec (hres γ γ.2)

/-- **The restriction hom** `Γ →* Isom(𝐌^{d₁+1})`, `γ ↦ g` with `ι ∘ g = γ ∘ ι`. -/
noncomputable def restrictHom (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : Γ →* isom d₁ where
  toFun γ := Classical.choose (hres γ γ.2)
  map_one' := (restricts_choose ι hres 1).unique AffineMinkEmbedding.Restricts.one
  map_mul' γ γ' := (restricts_choose ι hres (γ * γ')).unique
    ((restricts_choose ι hres γ).mul (restricts_choose ι hres γ'))

theorem restrictHom_restricts (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (γ : Γ) : ι.Restricts (γ : isom d) (restrictHom ι hres γ) :=
  restricts_choose ι hres γ

theorem range_restrictHom (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : (restrictHom ι hres).range = ι.restrictGroup Γ := by
  ext g
  constructor
  · rintro ⟨γ, rfl⟩; exact ⟨γ, γ.2, restrictHom_restricts ι hres γ⟩
  · rintro ⟨γ, hγ, h⟩
    exact ⟨⟨γ, hγ⟩, (restrictHom_restricts ι hres ⟨γ, hγ⟩).unique h⟩

/-- **Pulling back a finite-index subgroup of the restricted group**: for `H ≤ Γ_U` of finite
index there is a finite-index `Γ' ≤ Γ` with `Γ'_U ≤ H`. -/
theorem exists_le_restrictGroup_le (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) {H : Subgroup (isom d₁)}
    (hidx : H.relIndex (ι.restrictGroup Γ) ≠ 0) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧ ι.restrictGroup Γ' ≤ H := by
  set r := restrictHom ι hres
  refine ⟨(H.comap r).map Γ.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective, Subgroup.index_comap,
      range_restrictHom]
    exact hidx
  · rintro g ⟨γ, ⟨γ', hγ', rfl⟩, hg⟩
    have : r γ' = g := (restrictHom_restricts ι hres γ').unique hg
    rw [← this]; exact hγ'

/-- `Γ' ≤ Γ` restricts when `Γ` does. -/
theorem restrictsIn_mono {ι : AffineMinkEmbedding d₁ d} {Γ Γ' : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (hle : Γ' ≤ Γ) : ι.RestrictsIn Γ' :=
  fun γ hγ => hres γ (hle hγ)

/-- `Γ'_U ≤ Γ_U` for `Γ' ≤ Γ`. -/
theorem restrictGroup_mono (ι : AffineMinkEmbedding d₁ d) {Γ Γ' : Subgroup (isom d)}
    (hle : Γ' ≤ Γ) : ι.restrictGroup Γ' ≤ ι.restrictGroup Γ :=
  fun _ ⟨γ, hγ, h⟩ => ⟨γ, hle hγ, h⟩

/-! ### Properness of the restricted action -/

/-- **The restricted group acts properly on `ι⁻¹ Ω`** when `Γ` acts properly on `Ω`: `ι` maps a
compact `K ⊆ ι⁻¹ Ω` to a compact `ι K ⊆ Ω`, and `g K ∩ K ≠ ∅` gives `γ ι K ∩ ι K ≠ ∅` for any `γ`
which `g` restricts. -/
theorem proper_restrictGroup (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    {Ω : Set (Minkowski d)}
    (hprop : ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite) :
    ∀ K ⊆ ι ⁻¹' Ω, IsCompact K →
      {g : isom d₁ | g ∈ ι.restrictGroup Γ ∧ (g • K ∩ K).Nonempty}.Finite := by
  classical
  intro K hK hKc
  set f : isom d → isom d₁ := fun γ => if h : ∃ g, ι.Restricts γ g then Classical.choose h else 1
  have hf : ∀ γ g, ι.Restricts γ g → f γ = g := by
    intro γ g h
    have hex : ∃ g, ι.Restricts γ g := ⟨g, h⟩
    simp only [f, dif_pos hex]
    exact (Classical.choose_spec hex).unique h
  refine ((hprop (ι '' K) (by rintro _ ⟨x, hx, rfl⟩; exact hK hx)
    (hKc.image ι.continuous)).image f).subset ?_
  rintro g ⟨⟨γ, hγ, hr⟩, _, ⟨x, hx, rfl⟩, hxK⟩
  refine ⟨γ, ⟨hγ, γ • ι x, Set.smul_mem_smul_set ⟨x, hx, rfl⟩, ⟨g • x, hxK, hr x⟩⟩, hf γ g hr⟩

/-! ### Dimension -/

/-- **`d₁ ≤ d`** for an isometric affine embedding `𝐌^{d₁+1} → 𝐌^{d+1}`. -/
theorem le_of_affineMinkEmbedding (ι : AffineMinkEmbedding d₁ d) : d₁ ≤ d := by
  have := LinearMap.finrank_le_finrank_of_injective ι.lin_injective
  rw [finrank_minkowski, finrank_minkowski] at this
  omega

/-! ### The §8 data: discreteness, subgroups -/

/-- `γ ↦ γ • x` is continuous on `Isom(𝐌ⁿ)` (`isomTopology`); `Flat.Nonloxodromic`'s
`continuous_isom_smul_apply`, reproved. -/
theorem continuous_isom_smul_apply' (x : Minkowski d) :
    Continuous (fun γ : isom d => γ • x) := by
  have e : (fun γ : isom d => γ • x) =
      (fun p : (Minkowski d →L[ℝ] Minkowski d) × Minkowski d => p.1 x + p.2) ∘ isomPair := by
    funext γ
    simp only [Function.comp_apply, isomPair, linToCLM, LinearMap.coe_toContinuousLinearMap']
    rw [smul_eq_lin_add]
    rfl
  rw [e]
  exact ((continuous_fst.clm_apply continuous_const).add continuous_snd).comp
    continuous_induced_dom

/-- **The §8 data make `Γ` discrete** (`isomTopology`); `Flat.Nonloxodromic`'s
`discreteTopology_of_ccAction`, reproved. -/
theorem ccAction_discreteTopology {Γ : Subgroup (isom d)} {St : Set (Minkowski d)}
    (h : CCAction Γ St) : DiscreteTopology Γ := by
  haveI : T2Space (isom d) :=
    (show IsEmbedding (isomPair (d := d)) from ⟨⟨rfl⟩, isomPair_injective⟩).t2Space
  obtain ⟨x, hx⟩ := h.nonempty
  have hcl : IsClosed St := by
    obtain ⟨g, hg, hS⟩ := isEntireAcausalGraph_iff.1 h.cc.entire
    rw [hS]; exact isClosed_graph hg.lipschitzWith.continuous
  rw [discreteTopology_iff_isOpen_singleton]
  intro γ₀
  set K : Set (Minkowski d) :=
    St ∩ Metric.closedBall x 1 ∪ St ∩ Metric.closedBall ((γ₀ : isom d) • x) 1 with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall x 1).inter_left hcl).union
      ((isCompact_closedBall _ 1).inter_left hcl)
  have hKS : K ⊆ St := union_subset inter_subset_left inter_subset_left
  have hfin := h.proper K hKS hKc
  set U : Set Γ := {γ | dist ((γ : isom d) • x) ((γ₀ : isom d) • x) < 1} with hU
  have hUo : IsOpen U :=
    isOpen_lt (((continuous_isom_smul_apply' x).comp continuous_subtype_val).dist
      continuous_const) continuous_const
  have hUfin : U.Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, ?_⟩
    refine ⟨(γ : isom d) • x, smul_mem_smul_set (Or.inl ⟨hx, Metric.mem_closedBall_self zero_le_one⟩),
      Or.inr ⟨h.smul_mem γ.2 hx, ?_⟩⟩
    exact Metric.mem_closedBall.2 (le_of_lt hγ)
  have hγ₀ : γ₀ ∈ U := by
    show dist _ _ < 1
    rw [dist_self]; exact zero_lt_one
  rw [← Set.sdiff_sdiff_cancel_left (singleton_subset_iff.2 hγ₀)]
  exact hUo.sdiff ((hUfin.subset sdiff_subset).isClosed)

/-- **`CCAction` passes to subgroups.** -/
theorem ccAction_mono {Γ Γ' : Subgroup (isom d)} {St : Set (Minkowski d)} (h : CCAction Γ St)
    (hle : Γ' ≤ Γ) : CCAction Γ' St :=
  ⟨h.cc, fun γ hγ => h.inv γ (hle hγ), fun γ hγ => h.free γ (hle hγ),
    fun K hK hKc => (h.proper K hK hKc).subset fun _ hγ => ⟨hle hγ.1, hγ.2⟩⟩

end Causal.Flat.Lox
