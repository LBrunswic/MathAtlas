import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend

/-!
# `Causal.Flat.Cla.LTPEnlarge` — enlarging the base of a linear twisted product (G3)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.S
"Twisted product by euclidean manifolds" (`GHFspace.tex` l.1751–1797 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`), Lemma 5.5 `blem:suspendre` (l.1834), used for gap
**G3** of [11.i] (l.3565–3571, l.3662–3666; `docs/BARBOT-THEOREMS.md` §6 G3:
`B₂ = Γ\(Ω_{M₂} ⊕ U^⊥)`). **No label is marked**: this file proves an auxiliary step the paper
leaves implicit, not a statement of the paper.

* `exists_isLTPData_enlarge` — if `B = Γ\Ω` is a linear twisted product over `M₁ = Γ_U\(U ∩ Ω)`
  (`IsLTPData B M₁ Γ Ω ι`) and `M₂ = Γ_U\Ω₂` for an open `Ω₂ ⊇ ι⁻¹ Ω`, then
  `Ω' := q⁻¹ Ω₂ = Ω₂ ⊕ U^⊥` (`q` the retraction onto `U` along `U^⊥`) contains `Ω`, satisfies
  `ι⁻¹ Ω' = Ω₂`, is convex when `Ω₂` is, and `B₂ := Γ\Ω'` is a linear twisted product over `M₂`
  with the same `Γ` and `ι`. **Proved, no `sorry`.**

> When $N$ is an euclidean linear space and $r$ takes value in linear isometries (i.e.,
> $r(\Gamma)$ admits a global fixed point in $N$), then we say that $B$ is a
> \emph{linear twisted product over $M$.}

> Let $B$ be a flat spacetime, quotient of an open subset $\Omega$ of \mink by a group of
> isometries acting freely and properly discontinuously. Assume that $\Gamma$ preserves a
> timelike affine subspace $\bf U$, and that $\Omega$ is invariant by translations by vectors
> contained in the orthogonal linear space ${\bf U}^{\perp}$. Then, the quotient of
> ${\bf U} \cap \Omega$ by $\Gamma$ is a flat spacetime $M$, and $B$ is the linear twisted
> product of $M$ by the euclidean space ${\bf U}^{\perp}$.

> (i) Translation spacetimes, Misner spacetimes, and twisted products of Cauchy-hyperbolic
> spacetimes by flat torii are absolutely maximal, and any unipotent spacetime can be tamely
> embedded in some absolutely maximal unipotent spacetime.

> Then, since $y_{+} \leq Y_{+}$, $M_{0}$ tamely embedds in the quotient
> $\Gamma_{0}\backslash\Omega$.

Barbot's `n` is `d + 1` (the library's `Minkowski d` has `d` spatial dimensions); `U = range ι`
has dimension `d₁ + 1`.

## Hypothesis checklist

| hypothesis (G3, BARBOT-THEOREMS §6) | here |
|---|---|
| `B = Γ\Ω` a linear twisted product over `M₁ = Γ_U\(U ∩ Ω)` | ✓ carried (`IsLTPData B M₁ Γ Ω ι`) |
| `M₂ = Γ_U\Ω₂` with `U ∩ Ω ⊆ Ω₂` (the tame embedding `M₁ ↪ M₂` of [11.i]) | ✓ carried (`hle`, `hM₂`) |
| `Ω₂` convex (for the convexity of `Ω'`) | ✓ asked only for that conjunct |
| `Ω₂` connected | ⚠ weakened: not asked (`Γ\Ω'` is connected because `M₂` is) |

## SCOPE (disclosed)

* The proof: `q (γ p) = g (q p)` when `γ` restricts to `g` on `U` (`Restricts.retract_smul`), so
  `Ω'` is `Γ`-invariant; freeness and proper discontinuity on `Ω'` descend from those of `Γ_U` on
  `Ω₂` (Hausdorff `M₂`) along `q`, because `γ ↦ γ|_U` is injective on `Γ`: an element restricting
  to the identity of `U` fixes the nonempty `U ∩ Ω` (`B` is nonempty), hence is `1` by freeness on
  `Ω`. `Γ\Ω'` is connected: every class is joined, along a `U^⊥`-segment, to the image of the
  connected `Γ_U\Ω₂ ≅ M₂` under `x ↦ [ι x]`.
* The tame embedding `B ↪ B₂` (induced by `Ω ≤ Ω'`) and the absolute maximality of `M₂` are not
  part of this statement; they are the consumer's (`Classification.exists_absMax_unipotent_ltp`).
* The covering-presentation lemmas (`isCancelSMul_of_isCoveringMap`,
  `properlyDiscontinuousSMul_of_isCoveringMap` of `Flat.Classification`, which imports this file)
  are reproduced here as private copies.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace
open Causal.Flat Causal.Flat.FlatQuotient

universe u v w

variable {d : ℕ}

/-! ### Covering presentations act freely and properly discontinuously (private copies) -/

section Covering

private theorem lE_exists_injOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {π : X → Y} (h : IsCoveringMap π) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn π U := by
  obtain ⟨e, hx, he⟩ := h.isLocalHomeomorph x
  exact ⟨e.source, e.open_source, hx, fun a ha b hb hab => by
    rw [he] at hab; exact e.injOn ha hb hab⟩

private theorem lE_isCancelSMul {X : Type*} [TopologicalSpace X] {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X} (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) : IsCancelSMul Γ Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro γ p hp
  obtain ⟨U, hUo, hpU, hinj⟩ := lE_exists_injOn hcov p
  have hc : Continuous fun q : Ω => γ • q := continuous_const_smul γ
  have hU' : IsOpen (U ∩ (fun q : Ω => γ • q) ⁻¹' U) := hUo.inter (hUo.preimage hc)
  have hfix : ∀ q ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U, γ • q = q := by
    rintro q ⟨hq1, hq2⟩
    exact hinj hq2 hq1 ((hfib q (γ • q)).2 ⟨γ, γ.2, rfl⟩).symm
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hU'
  have hpU' : p ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U :=
    ⟨hpU, by simp only [mem_preimage, hp]; exact hpU⟩
  rw [← hV] at hpU'
  have hpV : (p : Minkowski d) ∈ V ∩ Ω := ⟨hpU', p.2⟩
  apply Subtype.ext
  refine Causal.eq_of_eqOn (hVo.inter Ω.isOpen) ⟨_, hpV⟩ fun x hx => ?_
  have hx' : (⟨x, hx.2⟩ : Ω) ∈ U ∩ (fun q : Ω => γ • q) ⁻¹' U := by rw [← hV]; exact hx.1
  have := congrArg Subtype.val (hfix _ hx')
  simpa using this

private theorem lE_properlyDiscontinuousSMul {X : Type*} [TopologicalSpace X] [T2Space X]
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} [FlatQuotient.Invariant Γ Ω] {π : Ω → X}
    (hcov : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q) :
    ProperlyDiscontinuousSMul Γ Ω := by
  haveI := lE_isCancelSMul hcov hfib
  refine ⟨fun {K L} hK hL => ?_⟩
  by_contra hinf
  set T := {γ : Γ | ((γ • ·) '' K ∩ L).Nonempty}
  let e := Set.Infinite.natEmbedding T hinf
  have hmem : ∀ n, ∃ k ∈ K, ((e n : Γ)) • k ∈ L := fun n => by
    obtain ⟨_, ⟨k, hk, rfl⟩, hl⟩ := (e n).2
    exact ⟨k, hk, hl⟩
  choose k hkK hkL using hmem
  obtain ⟨a, -, φ, hφ, ha⟩ := hK.tendsto_subseq hkK
  obtain ⟨b, -, ψ, hψ, hb⟩ := hL.tendsto_subseq (fun n => hkL (φ n))
  set c : ℕ → Ω := fun n => k (φ (ψ n))
  set γn : ℕ → Γ := fun n => (e (φ (ψ n)) : Γ)
  have hc : Tendsto c atTop (𝓝 a) := ha.comp hψ.tendsto_atTop
  have hb' : Tendsto (fun n => γn n • c n) atTop (𝓝 b) := hb
  have hπ : ∀ n, π (γn n • c n) = π (c n) := fun n =>
    ((hfib (c n) (γn n • c n)).2 ⟨_, (γn n).2, rfl⟩).symm
  have h1 : Tendsto (fun n => π (c n)) atTop (𝓝 (π a)) := (hcov.continuous.tendsto a).comp hc
  have h2 : Tendsto (fun n => π (c n)) atTop (𝓝 (π b)) := by
    have := (hcov.continuous.tendsto b).comp hb'
    simpa only [comp_def, hπ] using this
  obtain ⟨γ, hγ, hγab⟩ := (hfib a b).1 (tendsto_nhds_unique h1 h2)
  set g : Γ := ⟨γ, hγ⟩
  have hga : g • a = b := Subtype.ext hγab
  obtain ⟨U, hUo, hbU, hinj⟩ := lE_exists_injOn hcov b
  have h3 : Tendsto (fun n => g • c n) atTop (𝓝 b) := by
    have := ((continuous_const_smul g).tendsto a).comp hc
    rwa [hga] at this
  have hev : ∀ᶠ n in atTop, γn n = g := by
    filter_upwards [h3.eventually (hUo.mem_nhds hbU), hb'.eventually (hUo.mem_nhds hbU)] with n
      hu1 hu2
    have hπ' : π (γn n • c n) = π (g • c n) := by
      rw [hπ, ((hfib (c n) (g • c n)).2 ⟨_, g.2, rfl⟩)]
    exact IsCancelSMul.right_cancel _ _ _ (hinj hu2 hu1 hπ')
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hEq : e (φ (ψ N)) = e (φ (ψ (N + 1))) :=
    Subtype.ext ((hN N le_rfl).trans (hN (N + 1) (by omega)).symm)
  have := hψ.injective (hφ.injective (e.injective hEq))
  omega

private theorem lE_isCancelSMul_of_isQuotientOf {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf M Γ Ω) [FlatQuotient.Invariant Γ Ω] : IsCancelSMul Γ Ω :=
  let ⟨_, hcov, _, _, hfib⟩ := hq.quot
  lE_isCancelSMul hcov hfib

private theorem lE_pd_of_isQuotientOf {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Minkowski d) M] {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)}
    (hq : IsQuotientOf M Γ Ω) [FlatQuotient.Invariant Γ Ω] : ProperlyDiscontinuousSMul Γ Ω :=
  let ⟨_, hcov, _, _, hfib⟩ := hq.quot
  lE_properlyDiscontinuousSMul hcov hfib

end Covering

/-! ### The enlarged domain `Ω' = q⁻¹ Ω₂` -/

section Enlarge

variable {d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d)

private theorem lE_retract_add_perp (p : Minkowski d) {w : Minkowski d} (hw : w ∈ ι.perp) :
    ι.retract (p + w) = ι.retract p := by
  rw [AffineMinkEmbedding.retract, AffineMinkEmbedding.retract,
    show p + w - ι 0 = (p - ι 0) + w by abel, map_add, ι.coproj_eq_zero_of_mem_perp hw, add_zero]

/-- `Ω' := q⁻¹ Ω₂`, the open set `Ω₂ ⊕ U^⊥`. -/
private def lE_opens (Ω₂ : Opens (Minkowski d₁)) : Opens (Minkowski d) :=
  ⟨ι.retract ⁻¹' (Ω₂ : Set (Minkowski d₁)), Ω₂.isOpen.preimage ι.continuous_retract⟩

private theorem lE_mem_opens {Ω₂ : Opens (Minkowski d₁)} {p : Minkowski d} :
    p ∈ lE_opens ι Ω₂ ↔ ι.retract p ∈ Ω₂ := Iff.rfl

private theorem lE_preimage_opens (Ω₂ : Opens (Minkowski d₁)) :
    ι.preimageOpens (lE_opens ι Ω₂) = Ω₂ :=
  SetLike.ext fun x => by
    rw [AffineMinkEmbedding.mem_preimageOpens, lE_mem_opens, ι.retract_apply]

private theorem lE_convex {Ω₂ : Opens (Minkowski d₁)} (hcv : Convex ℝ (Ω₂ : Set (Minkowski d₁))) :
    Convex ℝ (lE_opens ι Ω₂ : Set (Minkowski d)) := by
  have h := (hcv.linear_preimage ι.coproj).translate_preimage_right (-ι 0)
  have he : (lE_opens ι Ω₂ : Set (Minkowski d)) =
      (fun x => -ι 0 + x) ⁻¹' (ι.coproj ⁻¹' (Ω₂ : Set (Minkowski d₁))) := by
    ext p
    show ι.retract p ∈ Ω₂ ↔ ι.coproj (-ι 0 + p) ∈ Ω₂
    rw [AffineMinkEmbedding.retract, neg_add_eq_sub]
  rw [he]
  exact h

/-- `Γ\Ω'` is connected when `Γ_U\Ω₂` is: every class `[p]` is joined, along the segment
`t ↦ [q p + t (p − q p)]`, to the connected image of `Γ_U\Ω₂` under `x ↦ [ι x]`. -/
private theorem lE_connectedSpace {Γ : Subgroup (isom d)} {Ω₂ : Opens (Minkowski d₁)}
    [Invariant (ι.restrictGroup Γ) Ω₂] [Invariant Γ (lE_opens ι Ω₂)]
    [ConnectedSpace (FlatQuotient (ι.restrictGroup Γ) Ω₂)] :
    ConnectedSpace (FlatQuotient Γ (lE_opens ι Ω₂)) := by
  set Ω' := lE_opens ι Ω₂
  have hmem : ∀ (x : Minkowski d₁) (w : Minkowski d), w ∈ ι.perp → x ∈ Ω₂ → ι x + w ∈ Ω' :=
    fun x w hw hx => by
      show ι.retract (ι x + w) ∈ Ω₂
      rwa [ι.retract_apply_add x hw]
  have hmem0 : ∀ x : Minkowski d₁, x ∈ Ω₂ → ι x ∈ Ω' := fun x hx => by
    simpa using hmem x 0 ι.zero_mem_perp hx
  let s : Ω₂ → FlatQuotient Γ Ω' := fun x => proj Γ Ω' ⟨ι x, hmem0 x x.2⟩
  have hs : Continuous s := (continuous_proj Γ Ω').comp
    ((ι.continuous.comp continuous_subtype_val).subtype_mk _)
  have hrel : ∀ a b : Ω₂, (MulAction.orbitRel (ι.restrictGroup Γ) Ω₂) a b → s a = s b := by
    intro a b hab
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    obtain ⟨γ, hγ, h⟩ := g.2
    refine proj_eq_proj_iff'.2 ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
    show γ⁻¹ • ι (a : Minkowski d₁) = ι (b : Minkowski d₁)
    rw [← hg, coe_smul, h, inv_smul_smul]
  let σ : FlatQuotient (ι.restrictGroup Γ) Ω₂ → FlatQuotient Γ Ω' := Quotient.lift s hrel
  have hσ : Continuous σ := hs.quotient_lift hrel
  obtain ⟨c₀⟩ := (inferInstance : Nonempty (FlatQuotient (ι.restrictGroup Γ) Ω₂))
  refine { isPreconnected_univ := ?_, toNonempty := ⟨σ c₀⟩ }
  refine isPreconnected_of_forall (σ c₀) fun y _ => ?_
  obtain ⟨p, rfl⟩ := proj_surjective Γ Ω' y
  have hw : (p : Minkowski d) - ι (ι.retract p) ∈ ι.perp := ι.sub_apply_retract_mem_perp p
  have hx : ι.retract p ∈ Ω₂ := p.2
  let f : ℝ → FlatQuotient Γ Ω' := fun t =>
    proj Γ Ω' ⟨ι (ι.retract p) + t • ((p : Minkowski d) - ι (ι.retract p)),
      hmem _ _ (ι.smul_mem_perp t hw) hx⟩
  have hf : Continuous f := (continuous_proj Γ Ω').comp
    (Continuous.subtype_mk (continuous_const.add (continuous_id.smul continuous_const)) _)
  have h0 : f 0 = σ (proj _ _ ⟨ι.retract p, hx⟩) :=
    congrArg (proj Γ Ω') (Subtype.ext (by simp))
  have h1 : f 1 = proj Γ Ω' p :=
    congrArg (proj Γ Ω') (Subtype.ext (by simp))
  refine ⟨range σ ∪ f '' Icc 0 1, subset_univ _, Or.inl ⟨c₀, rfl⟩,
    Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩, ?_⟩
  exact IsPreconnected.union (f 0) (h0 ▸ ⟨_, rfl⟩) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    (isPreconnected_range hσ) (isPreconnected_Icc.image f hf.continuousOn)

end Enlarge

/-! ### The enlargement -/

/-- **Enlarging the base of a linear twisted product** (G3 of [11.i], BARBOT-THEOREMS §6;
§5.S l.1751–1797, `blem:suspendre` l.1834): if `B = Γ\Ω` is a linear twisted product over
`M₁ = Γ_U\(U ∩ Ω)` and `M₂ = Γ_U\Ω₂` with `ι⁻¹ Ω ⊆ Ω₂`, then `Ω' := Ω₂ ⊕ U^⊥` (the preimage of
`Ω₂` under the retraction onto `U` along `U^⊥`) contains `Ω`, meets `U` in `Ω₂`, is convex when
`Ω₂` is, and `B₂ := Γ\Ω'` is a linear twisted product over `M₂` with the same `Γ` and `ι`. -/
theorem exists_isLTPData_enlarge {d₁ : ℕ} {B : FlatSpacetime.{u} d} {M₁ : FlatSpacetime.{v} d₁}
    {Γ : Subgroup (isom d)} {Ω : Opens (Minkowski d)} {ι : AffineMinkEmbedding d₁ d}
    (hB : IsLTPData B M₁ Γ Ω ι) {Ω₂ : Opens (Minkowski d₁)} (hle : ι.preimageOpens Ω ≤ Ω₂)
    {M₂ : FlatSpacetime.{w} d₁} (hM₂ : IsQuotientOf M₂ (ι.restrictGroup Γ) Ω₂) :
    ∃ Ω' : Opens (Minkowski d), Ω ≤ Ω' ∧ ι.preimageOpens Ω' = Ω₂ ∧
      (Convex ℝ (Ω₂ : Set (Minkowski d₁)) → Convex ℝ (Ω' : Set (Minkowski d))) ∧
      ∃ B₂ : FlatSpacetime.{0} d, IsLTPData B₂ M₂ Γ Ω' ι := by
  haveI hiΩ := hB.quotient.invariant
  haveI hfΩ : IsCancelSMul Γ Ω := lE_isCancelSMul_of_isQuotientOf hB.quotient
  haveI hi₂ := hM₂.invariant
  haveI hf₂ : IsCancelSMul (ι.restrictGroup Γ) Ω₂ := lE_isCancelSMul_of_isQuotientOf hM₂
  haveI hp₂ : ProperlyDiscontinuousSMul (ι.restrictGroup Γ) Ω₂ := lE_pd_of_isQuotientOf hM₂
  have hperp := hB.perp_invariant
  have hres := hB.restricts
  -- an element of `Γ` restricting to the identity of `U` is `1`
  have hker : ∀ γ ∈ Γ, ι.Restricts γ 1 → γ = 1 := by
    intro γ hγ h
    obtain ⟨π, -, -, hsurj, -⟩ := hB.quotient.quot
    obtain ⟨p, -⟩ := hsurj (Classical.arbitrary B)
    have hx : ι (ι.retract p) ∈ Ω := (ι.mem_iff_retract_mem hperp).1 p.2
    have hfix : (⟨γ, hγ⟩ : Γ) • (⟨ι (ι.retract p), hx⟩ : Ω) = ⟨ι (ι.retract p), hx⟩ :=
      Subtype.ext (by
        rw [coe_smul]
        show γ • ι (ι.retract p) = ι (ι.retract p)
        rw [← h, one_smul])
    exact congrArg Subtype.val (isCancelSMul_iff_eq_one_of_smul_eq.1 hfΩ _ _ hfix)
  have hinj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ∀ g : isom d₁, ι.Restricts γ g → ι.Restricts γ' g → γ = γ' := by
    intro γ hγ γ' hγ' g h h'
    have h2 := h.inv.mul h'
    rw [inv_mul_cancel] at h2
    exact inv_mul_eq_one.1 (hker _ (Γ.mul_mem (Γ.inv_mem hγ) hγ') h2)
  set Ω' := lE_opens ι Ω₂ with hΩ'
  haveI hi' : Invariant Γ Ω' := ⟨fun γ p hp => by
    obtain ⟨g, hg⟩ := hres γ γ.2
    show ι.retract ((γ : isom d) • p) ∈ Ω₂
    rw [hg.retract_smul]
    exact Invariant.smul_mem (⟨g, γ, γ.2, hg⟩ : ι.restrictGroup Γ) _ hp⟩
  haveI hf' : IsCancelSMul Γ Ω' := by
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro γ p hp
    obtain ⟨g, hg⟩ := hres γ γ.2
    have hfix : (⟨g, γ, γ.2, hg⟩ : ι.restrictGroup Γ) • (⟨ι.retract p, p.2⟩ : Ω₂) =
        ⟨ι.retract p, p.2⟩ := Subtype.ext (by
      rw [coe_smul]
      show g • ι.retract p = ι.retract p
      rw [← hg.retract_smul]
      exact congrArg (fun q : Ω' => ι.retract (q : Minkowski d)) hp)
    have hg1 : g = 1 :=
      congrArg Subtype.val (isCancelSMul_iff_eq_one_of_smul_eq.1 hf₂ _ _ hfix)
    subst hg1
    exact Subtype.ext (hker γ γ.2 hg)
  haveI hp' : ProperlyDiscontinuousSMul Γ Ω' := by
    refine ⟨fun {K L} hK hL => ?_⟩
    let φ : Ω' → Ω₂ := fun p => ⟨ι.retract p, p.2⟩
    have hφ : Continuous φ := (ι.continuous_retract.comp continuous_subtype_val).subtype_mk _
    have hS := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (Γ := ι.restrictGroup Γ) (hK.image hφ) (hL.image hφ)
    let ρ : Γ → ι.restrictGroup Γ := fun γ =>
      ⟨Classical.choose (hres γ γ.2), γ, γ.2, Classical.choose_spec (hres γ γ.2)⟩
    have hρ : ∀ γ : Γ, ι.Restricts (γ : isom d) (ρ γ : isom d₁) := fun γ =>
      Classical.choose_spec (hres γ γ.2)
    have hρi : Injective ρ := fun γ γ' h =>
      Subtype.ext (hinj _ γ.2 _ γ'.2 _ (hρ γ) (by rw [h]; exact hρ γ'))
    refine Set.Finite.of_injOn (f := ρ) ?_ hρi.injOn hS
    rintro γ ⟨_, ⟨k, hk, rfl⟩, hl⟩
    refine ⟨φ (γ • k), ⟨φ k, ⟨k, hk, rfl⟩, Subtype.ext ?_⟩, ⟨γ • k, hl, rfl⟩⟩
    show (ρ γ : isom d₁) • ι.retract (k : Minkowski d) =
      ι.retract ((γ : isom d) • (k : Minkowski d))
    rw [(hρ γ).retract_smul]
  haveI hc₂ : ConnectedSpace (FlatQuotient (ι.restrictGroup Γ) Ω₂) := by
    obtain ⟨-, -, -, Φ, -⟩ := hM₂.exists_homeomorph
    exact Φ.symm.surjective.connectedSpace Φ.symm.continuous
  haveI hc' : ConnectedSpace (FlatQuotient Γ Ω') := lE_connectedSpace ι
  have hpre : ι.preimageOpens Ω' = Ω₂ := lE_preimage_opens ι Ω₂
  refine ⟨Ω', ?_, hpre, fun hcv => lE_convex ι hcv, FlatSpacetime.of (FlatQuotient Γ Ω'), ?_⟩
  · intro p hp
    exact hle ((ι.mem_iff_retract_mem hperp).1 hp)
  · refine ⟨hB.timelike, hB.orthochronous, hB.preserves, hres, ?_, FlatQuotient.isQuotientOf Γ Ω',
      ?_⟩
    · intro w hw p hp
      show ι.retract (p + w) ∈ Ω₂
      rw [lE_retract_add_perp ι p hw]
      exact hp
    · rw [hpre]; exact hM₂

end Causal.Flat.Cla
