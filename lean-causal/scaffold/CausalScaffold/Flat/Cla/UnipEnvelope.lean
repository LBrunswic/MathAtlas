import CausalScaffold.Flat.Nonloxodromic
import CausalScaffold.Flat.TitsNull
import CausalScaffold.Flat.Loxodromic
import CausalScaffold.CompactCauchy
import CausalScaffold.CurvesExtend

/-!
# `CausalScaffold.Flat.Cla.UnipEnvelope` — the maximal unipotent envelope of [11.i] (G1)

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11.3
[11.i] for the unipotent family (`maxi`, l.3629–3679 of the **labelled**
`papers/barbot/legacy/labeled/GHFspace.tex`), the gap **G1** of `docs/BARBOT-THEOREMS.md` §6.
No label is certified (the prose item [11.i] has no environment, and the main theorem rests on
one tagged `sorry`). It serves `Flat/Classification`'s `exists_absMax_unipotent_ltp` (G1: the
envelope and its maximality; the lifting glue turning the last conjunct into `AbsMax` stays there).

* `exists_unipotent_envelope` — **stated, reduced, partial**: Step 0 (rigidity of convex
  presentations) and the translation case are proved; the parabolic case is the one `sorry`.

> Consider first the case where
> $I_{0}$ is a bounded interval $]y_{-}, y_{+}[$. As previously,
> we assume without loss of generality the equality
> $y_{+} = -y_{-}$. In proposition \ref{limites}, we proved that
> the operator norm of $T_{0}$ is less than $\frac{1}{y_{+}}$.
> Denote by $Y_{+}$ the inverse of this operator norm.
> Then, proposition \ref{extension} implies that $T$ extends to some
> symetric operator $\widehat{T}$, which provides some
> abelian Lie group $A$ containing $\Gamma_{0}$ and
> for which $\Omega  = \pi_{1}^{-1}(]-Y_{+}, Y_{+}[)$ is a connected
> component of $\Omega(A)$. (l.3654–3664)

> Then, since $y_{+} \leq Y_{+}$, $M_{0}$ tamely embedds in
> the quotient $\Gamma_{0}\backslash\Omega$. On the other hand,
> we claim that this last quotient is absolutely maximal. (l.3666–3668)

> Consider $\pi_{1}(\Omega_{1}) = ] y'_{-}, y'_{+}[$. Since
> $\Gamma_{1}$ contains $\Gamma_{0}$, proposition \ref{limites}
> implies $-Y_{+} \leq y'_{-}$ and $y'_{+} \leq Y_{+}$,
> i.e., the equality  $\Omega_{0} = \Omega_{1}$ establishing
> the absolute maximality of $M_{0}$. (l.3672–3676)

> The case where $I_{0}$ is not bounded can be treated
> in a similar way. (l.3678–3679)

**Finding (G1, the construction is wrong as printed).** When `I₀` is bounded, the slab
`]−Y₊, Y₊[` need not be a component of `Ω(A)`, and when it is one it need not be maximal. In `𝐌⁴`
(`λ = (1, −1)`, `Γ₀ = ℤ·(1, 0)`, so `E = ℝe₁`, `T₀e₁ = e₁`, `y₊ = Y₊ = 1`: the very case
l.3670–3671 calls absolutely maximal) `Γ₀` acts identically through `λ' = (1, 0)`
(`unipAction_congr`), whose component `]−1, +∞[` strictly contains `]−1, 1[`
(`slab_not_maximal_e2`). The mechanism: a symmetric extension of norm `1/Y₊` has `+1/Y₊` or
`−1/Y₊` as an eigenvalue, but not necessarily both, so its component is `]−Y₊, Y'[` or
`]−Y', Y₊[` with `Y' ≥ Y₊`, possibly infinite; and Prop 9.3, normalised to symmetric intervals,
does **not** give "`−Y₊ ≤ y'₋` and `y'₊ ≤ Y₊`" for a non-symmetric `]y'₋, y'₊[` (for `]−1, +∞[`
its one-sided inequality `⟨u | Tu⟩ ≥ |Tu|²` holds, with equality). In `𝐌³` (`e = 1`) a bounded
`I₀` never occurs and every component is a half-space (`not_isUnipComponent_slab_e1`), so the
"similar" unbounded case cannot be the same formula. **Correction** (§5): take for the envelope a
**maximal admissible** interval `]a, b[ ⊇ ]α, β[` — admissible meaning
`⟨u + yTu | u + y'Tu⟩ ≥ 0` for `u ∈ E`, `a < y ≤ y' < b`, which is what Prop 9.3 proves in each of
its cases (`unipAdmissible_of_limitesIneq`) — and extend `T` at `]a, b[`; a maximal admissible
interval of the diagonalised extension is a component of `Ω(Â)` (`isUnipComponent_of_maximal`).
Also: 9.3 gives `‖T₀‖ ≤ 1/y₊` (with equality in the example), not "less than".

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, Barbot's `n` is `d + 1`. Here `𝐌ⁿ = Minkowski (e + 1)`, `n = e + 2`, and the
unipotent parameters live in `ℝᵉ = ℝ^{n−2}` (`Fin e → ℝ`).

## What is proved (no `sorry`)

* **Step 0, rigidity** — `exists_frame_of_isQuotientOf_convex`: two convex presentations
  `Γ\Ω = Γ'\Ω'` of one flat spacetime differ by one `h ∈ Isom(𝐌ⁿ)`, `hΩ = Ω'`, `hΓh⁻¹ = Γ'`
  (lifts through the coverings, `exists_lift_isom_of_convex`; `mem_of_preserves_fibres`). So the
  main theorem reduces to the canonical presentation `ψΓ₀ψ⁻¹`, `ψ(]α, β[)` of `IsUnipotentSpacetime`
  (`exists_unipotent_envelope_frame`), which is how `exists_unipotent_envelope` is assembled.
* **The translation case** (`λᵢtᵢ = 0` for all `t ∈ L`): `Γ₀` is the horizontal group of the
  lattice `(0, L)` (`eq_horizGroup_of_mul_eq_zero`), the envelope is `𝐌ⁿ` itself, a unipotent
  spacetime with `λ = 0`, `]−∞, +∞[`, and trivially maximal (`envelopeMaximal_top`). This covers
  every unipotent spacetime the library has an inhabitant of (Examples' SCOPE: trivial `Γ`).
* **The corrected interval** (§5): `UnipAdmissible`, `exists_maximal_unipAdmissible`,
  `unipAdmissible_diag_iff`, `isUnipComponent_of_maximal`, `unipAdmissible_of_limitesIneq`,
  `unipAdmissible_of_isUnipComponent`.
* The finding's witnesses: `not_isUnipComponent_slab_e1`, `slab_not_maximal_e2`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M₀` unipotent, `Γ₀\Ω₀` | ✓ carried: `IsUnipotentSpacetime M₁` and a **convex** presentation `IsQuotientOf M₁ Γ Ω` (the one `Flat/Classification` holds; rigidity identifies it with the canonical one) |
| "tamely embeds in `Γ₀\Ω`" | ✓ in the form `Ω ≤ Ω₂`, same `Γ`, `Ω₂` convex (tameness is `Flat/Cla/TameNested`) |
| absolute maximality of `Γ₀\Ω` | ⚠ in the form consumed by Classification's glue: the developing image of a (CC′) target containing `gΩ₂`, `gΓg⁻¹ ≤ ρ(Deck)`, is `gΩ₂` (`EnvelopeMaximal`) |
| the unbounded case "similar" (G1) | ✓ included in the statement (no boundedness hypothesis) |

## SCOPE (disclosed)

* **One `sorry`**, in `exists_unipotent_envelope_frame`, the parabolic case (some `t ∈ L` with
  `λ t ≠ 0`); its tag lists exactly what is missing: the extension at the maximal interval after a
  change of origin, the diagonalisation and the frame, the free proper action of the lattice on
  the component (not upstream), and the maximality argument (Prop 9.3 on `gΓg⁻¹`, plus the step
  `range 𝒟 ⊆ π₁⁻¹(π₁ Σ_N)` which Nonloxodromic also lacks).
* No `Flat/Lox/*`, `Flat/Nonlox/*` import. `Flat/Classification` is not imported (it is
  downstream); `isLocalIsometry_of_comp_left` is a **private** copy of its
  `IsLocalIsometry.of_comp_left_of_continuous` (as in the sibling `Cla/LTPConvex`,
  `Cla/FiniteCover`), and `isom_ext'` is private too.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace

universe u w

variable {d : ℕ}

/-! ## §1 Step 0: rigidity of convex presentations -/

section Rigidity

/-- A local copy of `Flat/Classification`'s `IsLocalIsometry.of_comp_left_of_continuous`
(Classification is downstream of this module): if `h ∘ f` and `h` are local isometries and `f` is
continuous, `f` is a local isometry. -/
private theorem isLocalIsometry_of_comp_left {X M N : Type*} [TopologicalSpace X]
    [ChartedSpace (Minkowski d) X] [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [TopologicalSpace N] [ChartedSpace (Minkowski d) N] {f : X → M} {h : M → N}
    (hh : IsLocalIsometry d h) (hfc : Continuous f) (hhf : IsLocalIsometry d (h ∘ f)) :
    IsLocalIsometry d f := by
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- **The lift between two presentations of the same quotient is an isometry**: if `π : Ω → M`
is a local isometry with `Ω` convex and nonempty and `π' : Ω' → M` a surjective covering map and
local isometry, then `π` lifts through `π'` (`Ω` is simply connected) and the lift is the
restriction of one `h ∈ Isom(𝐌ⁿ)` (uniqueness of developing maps on the connected `Ω`). -/
theorem exists_lift_isom_of_convex {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {Ω Ω' : Opens (Minkowski d)}
    (hcv : Convex ℝ (Ω : Set (Minkowski d))) (hne : (Ω : Set (Minkowski d)).Nonempty)
    {π : Ω → M} (hπl : IsLocalIsometry d π) {π' : Ω' → M} (hπ'c : IsCoveringMap π')
    (hπ'l : IsLocalIsometry d π') (hπ's : Surjective π') :
    ∃ h : isom d, ∀ p : Ω, ∃ hp : h • (p : Minkowski d) ∈ (Ω' : Set (Minkowski d)),
      π' ⟨_, hp⟩ = π p := by
  haveI : Nonempty Ω := hne.to_subtype
  haveI : ContractibleSpace Ω := hcv.contractibleSpace hne
  haveI : LocPathConnectedSpace Ω := locPathConnectedSpace_of_flat d Ω
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hcv.isPreconnected
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨e₀, he₀⟩ := hπ's (π a₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hπ'c.existsUnique_continuousMap_lifts ⟨π, hπl.continuous⟩ a₀ e₀ he₀
  have hFl : IsLocalIsometry d F :=
    isLocalIsometry_of_comp_left hπ'l F.continuous (by rw [hF]; exact hπl)
  have hvl : IsLocalIsometry d (Subtype.val : Ω → Minkowski d) :=
    (isIsometricEmbedding_subtype_val Ω).1
  have hvl' : IsLocalIsometry d (Subtype.val ∘ F) :=
    (isIsometricEmbedding_subtype_val Ω').1.comp hFl
  obtain ⟨h, hh, -⟩ := developing_unique_of_preconnected (G := isom d) (X := Minkowski d)
    (N := Ω) (D := Subtype.val) (D' := Subtype.val ∘ F)
    (isLocalIsometry_iff_eventually.1 hvl |> fun h' => ⟨h'.1, h'.2⟩)
    (isLocalIsometry_iff_eventually.1 hvl' |> fun h' => ⟨h'.1, h'.2⟩)
  have hFp : ∀ p : Ω, ((F p : Ω') : Minkowski d) = h • (p : Minkowski d) := fun p => hh p
  refine ⟨h, fun p => ⟨by rw [← hFp p]; exact (F p).2, ?_⟩⟩
  have : (⟨h • (p : Minkowski d), by rw [← hFp p]; exact (F p).2⟩ : Ω') = F p :=
    Subtype.ext (hFp p).symm
  rw [this]
  exact congrFun hF p

/-- **An isometry preserving the fibres of a presentation lies in its group**: if `π : Ω → M` is
a covering map whose fibres are the `Γ`-orbits, `Ω` preconnected and nonempty, and `g` maps `Ω`
into itself with `π ∘ g = π`, then `g ∈ Γ` (`g` and the `γ ∈ Γ` agreeing with it at one point
are two lifts of `π`, hence equal on `Ω`, hence equal: `Causal.eq_of_eqOn`). -/
theorem mem_of_preserves_fibres {M : Type*} [TopologicalSpace M] {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} (hcon : IsPreconnected (Ω : Set (Minkowski d)))
    (hne : (Ω : Set (Minkowski d)).Nonempty) {π : Ω → M} (hπc : IsCoveringMap π)
    (hfib : ∀ p q : Ω, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), γ • p ∈ (Ω : Set (Minkowski d)))
    {g : isom d}
    (hg : ∀ p : Ω, ∃ hp : g • (p : Minkowski d) ∈ (Ω : Set (Minkowski d)), π ⟨_, hp⟩ = π p) :
    g ∈ Γ := by
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hcon
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨hgp₀, hπp₀⟩ := hg ⟨p₀, hp₀⟩
  obtain ⟨γ, hγ, hγp⟩ := (hfib ⟨p₀, hp₀⟩ ⟨_, hgp₀⟩).1 hπp₀.symm
  set A : Ω → Ω := fun p => ⟨g • (p : Minkowski d), (hg p).1⟩ with hA
  set B : Ω → Ω := fun p => ⟨γ • (p : Minkowski d), hinv γ hγ _ p.2⟩ with hB
  have hAc : Continuous A :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _
  have hBc : Continuous B :=
    ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _
  have hAB : A = B := hπc.eq_of_comp_eq hAc hBc (funext fun p => by
      simp only [comp_apply]
      rw [(hg p).2]
      exact (hfib p (B p)).2 ⟨γ, hγ, rfl⟩) ⟨p₀, hp₀⟩ (Subtype.ext hγp.symm)
  have hgγ : g = γ := Causal.eq_of_eqOn Ω.isOpen ⟨p₀, hp₀⟩ fun x hx =>
    congrArg Subtype.val (congrFun hAB ⟨x, hx⟩)
  exact hgγ ▸ hγ

theorem mem_frameConj_iff {h γ : isom d} {Γ : Subgroup (isom d)} :
    γ ∈ frameConj h Γ ↔ h⁻¹ * γ * h ∈ Γ := by
  constructor
  · rintro ⟨γ₀, hγ₀, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hγ₀
  · intro hγ
    refine ⟨h⁻¹ * γ * h, hγ, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem frameConj_mul' (a b : isom d) (Γ : Subgroup (isom d)) :
    frameConj (a * b) Γ = frameConj a (frameConj b Γ) := by
  ext γ
  rw [mem_frameConj_iff, mem_frameConj_iff, mem_frameConj_iff]
  simp only [mul_inv_rev, mul_assoc]

theorem frameConj_inv_frameConj (h : isom d) (Γ : Subgroup (isom d)) :
    frameConj h⁻¹ (frameConj h Γ) = Γ := by
  rw [← frameConj_mul', inv_mul_cancel, frameConj_one]

/-- **Step 0: rigidity of convex presentations.** Two presentations `M = Γ\Ω = Γ'\Ω'` of the
same flat spacetime by convex open sets differ by one isometry: `hΩ = Ω'`, `hΓh⁻¹ = Γ'`. (Both
`Ω` and `Ω'` are simply connected, so each projection lifts through the other; the lifts are
isometries, their composite preserves the fibres of `π`, hence lies in `Γ`.) -/
theorem exists_frame_of_isQuotientOf_convex {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Minkowski d) M] {Γ Γ' : Subgroup (isom d)} {Ω Ω' : Opens (Minkowski d)}
    (hq : IsQuotientOf M Γ Ω) (hq' : IsQuotientOf M Γ' Ω')
    (hcv : Convex ℝ (Ω : Set (Minkowski d))) (hcv' : Convex ℝ (Ω' : Set (Minkowski d)))
    (hne : (Ω : Set (Minkowski d)).Nonempty) :
    ∃ h : isom d, isomImage h Ω = Ω' ∧ frameConj h Γ = Γ' := by
  obtain ⟨π, hπc, hπl, hπs, hfib⟩ := hq.quot
  obtain ⟨π', hπ'c, hπ'l, hπ's, hfib'⟩ := hq'.quot
  have hne' : (Ω' : Set (Minkowski d)).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    obtain ⟨q, -⟩ := hπ's (π ⟨p, hp⟩)
    exact ⟨q, q.2⟩
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), γ • p ∈ (Ω : Set (Minkowski d)) :=
    fun γ hγ p hp => by rw [← hq.inv γ hγ]; exact ⟨p, hp, rfl⟩
  have hinv' : ∀ γ ∈ Γ', ∀ p ∈ (Ω' : Set (Minkowski d)), γ • p ∈ (Ω' : Set (Minkowski d)) :=
    fun γ hγ p hp => by rw [← hq'.inv γ hγ]; exact ⟨p, hp, rfl⟩
  obtain ⟨h, hh⟩ := exists_lift_isom_of_convex hcv hne hπl hπ'c hπ'l hπ's
  obtain ⟨k, hk⟩ := exists_lift_isom_of_convex hcv' hne' hπ'l hπc hπl hπs
  have hkh : k * h ∈ Γ := mem_of_preserves_fibres hcv.isPreconnected hne hπc hfib hinv
    fun p => by
      obtain ⟨h1, h2⟩ := hh p
      obtain ⟨h3, h4⟩ := hk ⟨_, h1⟩
      refine ⟨by rw [mul_smul]; exact h3, ?_⟩
      rw [← h2, ← h4]
      congr 1
  have hmem : ∀ q ∈ (Ω' : Set (Minkowski d)), h⁻¹ • q ∈ (Ω : Set (Minkowski d)) := by
    intro q hq
    have h2 := hinv _ (Γ.inv_mem hkh) _ (hk ⟨q, hq⟩).1
    rwa [mul_inv_rev, mul_smul, inv_smul_smul] at h2
  have hΩ : isomImage h Ω = Ω' := by
    apply SetLike.coe_injective
    ext q
    rw [coe_isomImage]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact (hh ⟨p, hp⟩).1
    · intro hq
      exact ⟨h⁻¹ • q, hmem q hq, smul_inv_smul h q⟩
  refine ⟨h, hΩ, ?_⟩
  ext γ'
  rw [mem_frameConj_iff]
  constructor
  · intro hγ
    have key : h * (h⁻¹ * γ' * h) * h⁻¹ ∈ Γ' := by
      refine mem_of_preserves_fibres hcv'.isPreconnected hne' hπ'c hfib' hinv' fun q => ?_
      set γ := h⁻¹ * γ' * h
      set p : Ω := ⟨h⁻¹ • (q : Minkowski d), hmem _ q.2⟩
      set r : Ω := ⟨γ • (p : Minkowski d), hinv γ hγ _ p.2⟩
      have hr : (h * γ * h⁻¹) • (q : Minkowski d) = h • (r : Minkowski d) := by
        simp only [r, p, mul_smul]
      refine ⟨by rw [hr]; exact (hh r).1, ?_⟩
      have e1 : (⟨(h * γ * h⁻¹) • (q : Minkowski d), by rw [hr]; exact (hh r).1⟩ : Ω') =
          ⟨h • (r : Minkowski d), (hh r).1⟩ := Subtype.ext hr
      have e2 : (⟨h • (p : Minkowski d), (hh p).1⟩ : Ω') = q :=
        Subtype.ext (smul_inv_smul h (q : Minkowski d))
      rw [e1, (hh r).2, ← (hfib p r).2 ⟨γ, hγ, rfl⟩, ← (hh p).2, e2]
    simpa [mul_assoc] using key
  · intro hγ'
    refine mem_of_preserves_fibres hcv.isPreconnected hne hπc hfib hinv fun p => ?_
    set q' : Ω' := ⟨h • (p : Minkowski d), (hh p).1⟩
    have hq'' : γ' • (q' : Minkowski d) ∈ (Ω' : Set (Minkowski d)) := hinv' γ' hγ' _ q'.2
    have hr : (h⁻¹ * γ' * h) • (p : Minkowski d) = h⁻¹ • (γ' • (q' : Minkowski d)) := by
      simp only [q', mul_smul]
    refine ⟨by rw [hr]; exact hmem _ hq'', ?_⟩
    set r : Ω := ⟨(h⁻¹ * γ' * h) • (p : Minkowski d), by rw [hr]; exact hmem _ hq''⟩
    have e1 : (⟨h • (r : Minkowski d), (hh r).1⟩ : Ω') = ⟨γ' • (q' : Minkowski d), hq''⟩ :=
      Subtype.ext (by simp only [r, hr, smul_inv_smul])
    rw [← (hh r).2, e1, ← (hfib' q' ⟨_, hq''⟩).2 ⟨γ', hγ', rfl⟩, (hh p).2]

end Rigidity


/-! ## §2 The unipotent action, and the translation case -/

section Unip

variable {e : ℕ}

/-- **The action of `t` depends on `ℓ` only through `(ℓᵢ tᵢ)ᵢ`**: `unipAction ℓ t = unipAction ℓ' t`
as soon as `ℓᵢ tᵢ = ℓ'ᵢ tᵢ` for every `i` (Barbot's `u = ∑ tᵢ eᵢ`, `v = ∑ tᵢ λᵢ eᵢ`, l.649–652:
an element of `A` is determined by `u` and `v = T u`, so only `T` on the span of the `u`'s matters). -/
theorem unipAction_congr {ℓ ℓ' : Fin e → ℝ} {t : EuclideanSpace ℝ (Fin e)}
    (h : ∀ i, ℓ i * t i = ℓ' i * t i) (p : Minkowski (e + 1)) :
    unipAction ℓ t p = unipAction ℓ' t p := by
  have h1 : ∀ i, ℓ i / 2 * t i ^ 2 = ℓ' i / 2 * t i ^ 2 := fun i => by
    have := h i; linear_combination (t i / 2) * this
  have h2 : ∀ i, ℓ i * nullZ p i * t i = ℓ' i * nullZ p i * t i := fun i => by
    have := h i; linear_combination (nullZ p i) * this
  have h3 : ∀ i, ℓ i ^ 2 * t i ^ 2 = ℓ' i ^ 2 * t i ^ 2 := fun i => by
    have := h i; linear_combination (ℓ i * t i + ℓ' i * t i) * this
  have h4 : ∀ i, nullZ p i + t i * (1 + nullY p * ℓ i) = nullZ p i + t i * (1 + nullY p * ℓ' i) :=
    fun i => by have := h i; linear_combination (nullY p) * this
  simp only [unipAction, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i,
    Finset.sum_congr rfl fun i _ => h3 i, h4]

/-- The embedding `ℝᵉ → ℝ^{e+1}`, `t ↦ (0, t)`: the `z`-coordinates of Barbot's null frame. -/
noncomputable def zEmbed (e : ℕ) : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin (e + 1)) where
  toFun t := WithLp.toLp 2 (Fin.cons 0 fun i => t i)
  map_add' x y := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem norm_zEmbed (t : EuclideanSpace ℝ (Fin e)) : ‖zEmbed e t‖ = ‖t‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  simp [zEmbed]

/-- In null coordinates, a `z`-translation is the horizontal translation by `(0, t)`. -/
theorem ofNull_add_z (x y : ℝ) (z t : EuclideanSpace ℝ (Fin e)) :
    ofNull x y (z + t) = ((0 : ℝ), zEmbed e t) + ofNull x y z := by
  refine Prod.ext ?_ ?_
  · simp [ofNull]
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ofNull, zEmbed]
    · simp [ofNull, zEmbed, add_comm]

/-- **With `ℓᵢ tᵢ = 0` for all `i`, `t` acts by the spacelike translation `(0, t)`.** -/
theorem unipAction_eq_add_of_mul_eq_zero {ℓ : Fin e → ℝ} {t : EuclideanSpace ℝ (Fin e)}
    (h : ∀ i, ℓ i * t i = 0) (p : Minkowski (e + 1)) :
    unipAction ℓ t p = ((0 : ℝ), zEmbed e t) + p := by
  rw [unipAction_congr (ℓ' := 0) (fun i => by simp [h i]) p]
  have hz : (WithLp.toLp 2 fun i => nullZ p i + t i * (1 + nullY p * (0 : Fin e → ℝ) i) :
      EuclideanSpace ℝ (Fin e)) = nullZ p + t := by
    ext i; simp
  simp only [unipAction, Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hz ⊢
  rw [hz, ofNull_add_z]
  congr 1
  exact nolToMink_minkToNol p

/-- An isometry is determined by its action. -/
private theorem isom_ext' {g g' : isom d} (h : ∀ p : Minkowski d, g • p = g' • p) : g = g' :=
  Subtype.ext (AffineEquiv.ext fun p => by
    have := h p
    rwa [isom_smul_def, isom_smul_def] at this)

/-- The lattice `(0, L)` of horizontal translations. -/
noncomputable def zLattice (L : AddSubgroup (EuclideanSpace ℝ (Fin e))) :
    AddSubgroup (EuclideanSpace ℝ (Fin (e + 1))) :=
  L.map (zEmbed e).toAddMonoidHom

theorem ballFinite_zLattice {L : AddSubgroup (EuclideanSpace ℝ (Fin e))} (hL : BallFinite L) :
    BallFinite (zLattice L) := by
  refine ⟨fun R => ((hL.finite_ball R).image (zEmbed e)).subset ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hR⟩
  refine ⟨t, ⟨ht, ?_⟩, rfl⟩
  simpa [norm_zEmbed] using hR

/-- **The translation case: `Γ₀` is the horizontal group of `(0, L)`.** -/
theorem eq_horizGroup_of_mul_eq_zero {ℓ : Fin e → ℝ} {L : AddSubgroup (EuclideanSpace ℝ (Fin e))}
    {Γ₀ : Subgroup (isom (e + 1))} (h1 : ∀ γ ∈ Γ₀, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    (h2 : ∀ t ∈ L, ∃ γ ∈ Γ₀, ∀ p, γ • p = unipAction ℓ t p)
    (htr : ∀ t ∈ L, ∀ i, ℓ i * t i = 0) : Γ₀ = horizGroup (zLattice L) := by
  ext γ
  rw [mem_horizGroup]
  constructor
  · intro hγ
    obtain ⟨t, ht, hγt⟩ := h1 γ hγ
    refine ⟨zEmbed e t, ⟨t, ht, rfl⟩, isom_ext' fun p => ?_⟩
    rw [horizTranslation_smul, hγt, unipAction_eq_add_of_mul_eq_zero (htr t ht)]
    rfl
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨γ', hγ', hγ't⟩ := h2 t ht
    have : γ' = horizTranslation (e + 1) (Multiplicative.ofAdd (zEmbed e t)) :=
      isom_ext' fun p => by
        rw [hγ't, horizTranslation_smul, unipAction_eq_add_of_mul_eq_zero (htr t ht)]
        rfl
    exact this ▸ hγ'

theorem unipDomain_bot_top : unipDomain (d := e) ⊥ ⊤ = ⊤ := by
  apply SetLike.coe_injective
  rw [Opens.coe_top]
  ext p
  exact ⟨fun _ => trivial, fun _ => ⟨EReal.bot_lt_coe _, EReal.coe_lt_top _⟩⟩

theorem isUnipComponent_zero : IsUnipComponent (0 : Fin e → ℝ) ⊥ ⊤ :=
  ⟨bot_lt_top, fun y _ _ i => by simp, Or.inl rfl, Or.inl rfl⟩

end Unip


/-! ## §3 The envelope -/

section Envelope

variable {e : ℕ}

/-- **The maximality conjunct of the envelope** (l.3668–3676, in the form the lifting glue of
`Flat/Classification` consumes): for every flat spacetime `N` carrying (CC′) data (a developing
pair `(𝒟, ρ)`, causal, `DevelopsCC`) and every `g ∈ Isom(𝐌ⁿ)` with `gΓg⁻¹ ≤ ρ(Deck)`, if the
developing image contains `gΩ₂` then it equals `gΩ₂`. -/
def EnvelopeMaximal (Γ : Subgroup (isom (e + 1))) (Ω₂ : Opens (Minkowski (e + 1))) : Prop :=
  ∀ (N : FlatSpacetime.{w} (e + 1)) {y₀ : N} {D : UniversalCover N y₀ → Minkowski (e + 1)}
    {ρ : Deck (UniversalCover.proj N y₀) →* isom (e + 1)}, IsDevelopingPair y₀ D ρ →
    (flatCausality (e + 1) N).IsCausal → ∀ {S : Set N}, DevelopsCC y₀ D S →
    ∀ g : isom (e + 1), (∀ γ ∈ Γ, g * γ * g⁻¹ ∈ ρ.range) →
      (fun p => g • p) '' (Ω₂ : Set (Minkowski (e + 1))) ⊆ range D →
      range D ⊆ (fun p => g • p) '' (Ω₂ : Set (Minkowski (e + 1)))

/-- The envelope `𝐌ⁿ` is maximal for every group: its translates are all of `𝐌ⁿ`. -/
theorem envelopeMaximal_top (Γ : Subgroup (isom (e + 1))) : EnvelopeMaximal.{w} Γ ⊤ := by
  intro N y₀ D ρ _ _ S _ g _ _ x _
  exact ⟨g⁻¹ • x, trivial, smul_inv_smul g x⟩

/-- **The envelope, in the canonical presentation** `Γ = ψΓ₀ψ⁻¹`, `Ω = ψ(]α, β[)`, `Γ₀` acting on
the component `]α, β[` of `Ω(A)` through the lattice `L` (`unipAction ℓ t`, `t ∈ L`). -/
theorem exists_unipotent_envelope_frame (ψ : isom (e + 1)) {ℓ : Fin e → ℝ} {α β : EReal}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin e))} {Γ₀ : Subgroup (isom (e + 1))}
    (hL : BallFinite L) (hc : IsUnipComponent ℓ α β)
    (h1 : ∀ γ ∈ Γ₀, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    (h2 : ∀ t ∈ L, ∃ γ ∈ Γ₀, ∀ p, γ • p = unipAction ℓ t p) :
    ∃ Ω₂ : Opens (Minkowski (e + 1)), isomImage ψ (unipDomain α β) ≤ Ω₂ ∧
      Convex ℝ (Ω₂ : Set (Minkowski (e + 1))) ∧
      (∃ M₂ : FlatSpacetime.{0} (e + 1), IsQuotientOf M₂ (frameConj ψ Γ₀) Ω₂ ∧
        IsUnipotentSpacetime M₂) ∧ EnvelopeMaximal.{w} (frameConj ψ Γ₀) Ω₂ := by
  by_cases htr : ∀ t ∈ L, ∀ i, ℓ i * t i = 0
  · -- the translation case: `Γ₀` is a lattice of spacelike translations, the envelope is `𝐌ⁿ`
    have hΓ := eq_horizGroup_of_mul_eq_zero h1 h2 htr
    haveI : BallFinite (zLattice L) := ballFinite_zLattice hL
    refine ⟨⊤, le_top, by rw [Opens.coe_top]; exact convex_univ, ?_, envelopeMaximal_top _⟩
    refine ⟨FlatQuotient.toFlatSpacetime (frameConj ψ (horizGroup (zLattice L))) ⊤
      FlatQuotient.isConnected_top, ?_, ?_⟩
    · rw [hΓ]; exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _
    · refine ⟨ψ, 0, ⊥, ⊤, L, Γ₀, hL, isUnipComponent_zero, fun γ hγ => ?_, fun t ht => ?_, ?_⟩
      · obtain ⟨t, ht, hγt⟩ := h1 γ hγ
        exact ⟨t, ht, fun p => by
          rw [hγt, unipAction_congr (ℓ' := 0) (fun i => by simp [htr t ht i])]⟩
      · obtain ⟨γ, hγ, hγt⟩ := h2 t ht
        exact ⟨γ, hγ, fun p => by
          rw [hγt, unipAction_congr (ℓ' := 0) (fun i => by simp [htr t ht i])]⟩
      · rw [unipDomain_bot_top, isomImage_top, hΓ]
        exact FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _
  · sorry -- SORRY([11.i] unipotent, G1, parabolic case): `Γ₀` contains a parabolic (some `t ∈ L` with `λ t ≠ 0`). Proved here: Step 0 (the reduction to this frame), the translation case, and the corrected interval — `]α, β[` is admissible for `T = diag(λ)` on `E = span L` (`unipAdmissible_of_isUnipComponent`), a maximal admissible `]a, b[ ⊇ ]α, β[` exists (`exists_maximal_unipAdmissible`), Prop 9.3's normalised conclusions are admissibility (`unipAdmissible_of_limitesIneq`), a maximal admissible interval of a diagonal `T̂` on `ℝᵉ` is a component of `Ω(Â)` (`isUnipComponent_of_maximal`); Barbot's `]−Y₊, Y₊[` must not be used (`slab_not_maximal_e2`). Missing: (1) the extension at `]a, b[` (finite at one end at least, since `T ≠ 0` on `E` forbids `]−∞, +∞[`): change of origin `y ↦ y − m` (`m` the midpoint, any `m ∈ ]a, b[` if one end is infinite), which replaces `E, T` by `(1 + mT)E`, `T(1 + mT)⁻¹` (`1 + mT` injective on `E` by admissibility) and normalises the interval, then `bprop_extension` and `unipAdmissible_of_limitesIneq` give a symmetric `T̂` on `ℝᵉ` with the shifted interval admissible on all of `ℝᵉ`; (2) the diagonalisation `T̂ = R diag(λ₂) R⁻¹` (`LinearMap.IsSymmetric.eigenvectorBasis`, `R ∈ SO(e)` after one sign change) and the frame `φ₂ = ψ ∘ (null translation by m) ∘ R ∈ Isom(𝐌ⁿ)`, with each element of `Γ₀` read as `unipAction λ₂ (R⁻¹(1 + mT)t)` (the `μ`-normalisation of `choixcoord`) and `IsUnipComponent λ₂ (a − m) (b − m)` (`isUnipComponent_of_maximal`: maximality for `T̂` on `ℝᵉ` follows from maximality for `T` on `E`); (3) `M₂ := Γ\φ₂(]a − m, b − m[)` as a `FlatQuotient`: freeness and proper discontinuity of a ball-finite lattice of `Â` on a component of `Ω(Â)` (not upstream: Examples' unipotent family is inhabited only for trivial `Γ`), `Ω ≤ Ω₂`, convexity (a slab); (4) maximality (l.3668–3676), read in the frame `gφ₂`: `Σ_N = 𝒟(S̃_N)` is acausal (`DevelopsCC.cc.entire`) and `gΓg⁻¹`-invariant (`holonomy_smul_eq`), preconnected (`ccAction_of_developsCC`); `range 𝒟 ⊆ π₁⁻¹(π₁ Σ_N)` (each null line `y = const` of the open `range 𝒟`, in which `Σ_N` is Cauchy — step 2 of `bprop_danom` — meets `Σ_N`; the same step Nonloxodromic's `nonloxodromic_parabolic` lists as missing, item (7)); `π₁(Σ_N)` is an interval containing `]a, b[` (from `gΩ₂ ⊆ range 𝒟`) and every open sub-interval is admissible (`bprop_limites` for `gΓg⁻¹` alone, shifted to the sub-interval's midpoint — no loxodromic exclusion is needed), so maximality gives `π₁(Σ_N) ⊆ [a, b]` and, `range 𝒟` being open, `range 𝒟 ⊆ gΩ₂`

end Envelope

/-- **[11.i] for the unipotent family, G1: the maximal unipotent envelope** (l.3629–3679). A
unipotent spacetime `M₁`, presented as `Γ\Ω` with `Ω` convex, embeds (`Ω ≤ Ω₂`, same `Γ`) in a
unipotent spacetime `M₂ = Γ\Ω₂`, `Ω₂` convex, which is maximal in the sense consumed by
`Flat/Classification`'s lifting glue: the developing image of a (CC′) target containing `gΩ₂`
with `gΓg⁻¹` in its holonomy is `gΩ₂`. -/
theorem exists_unipotent_envelope {e : ℕ} {M₁ : FlatSpacetime.{u} (e + 1)}
    (hU : IsUnipotentSpacetime M₁) {Γ : Subgroup (isom (e + 1))} {Ω : Opens (Minkowski (e + 1))}
    (hq : IsQuotientOf M₁ Γ Ω) (hcv : Convex ℝ (Ω : Set (Minkowski (e + 1)))) :
    ∃ Ω₂ : Opens (Minkowski (e + 1)), Ω ≤ Ω₂ ∧ Convex ℝ (Ω₂ : Set (Minkowski (e + 1))) ∧
      (∃ M₂ : FlatSpacetime.{0} (e + 1), IsQuotientOf M₂ Γ Ω₂ ∧ IsUnipotentSpacetime M₂) ∧
      ∀ (N : FlatSpacetime.{w} (e + 1)) {y₀ : N} {D : UniversalCover N y₀ → Minkowski (e + 1)}
        {ρ : Deck (UniversalCover.proj N y₀) →* isom (e + 1)}, IsDevelopingPair y₀ D ρ →
        (flatCausality (e + 1) N).IsCausal → ∀ {S : Set N}, DevelopsCC y₀ D S →
        ∀ g : isom (e + 1), (∀ γ ∈ Γ, g * γ * g⁻¹ ∈ ρ.range) →
          (fun p => g • p) '' (Ω₂ : Set (Minkowski (e + 1))) ⊆ range D →
          range D ⊆ (fun p => g • p) '' (Ω₂ : Set (Minkowski (e + 1))) := by
  obtain ⟨φ, ℓ, α, β, L, Γ₀, hL, hc, h1, h2, hq'⟩ := hU
  have hcv' : Convex ℝ (isomImage φ (unipDomain α β) : Set (Minkowski (e + 1))) :=
    convex_isomImage convex_unipDomain
  have hne : (Ω : Set (Minkowski (e + 1))).Nonempty := by
    obtain ⟨π, -, -, hπs, -⟩ := hq.quot
    obtain ⟨x⟩ : Nonempty M₁ := inferInstance
    obtain ⟨p, -⟩ := hπs x
    exact ⟨p, p.2⟩
  obtain ⟨h, hΩ, hΓ⟩ := exists_frame_of_isQuotientOf_convex hq hq' hcv hcv' hne
  have hΓ' : Γ = frameConj (h⁻¹ * φ) Γ₀ := by
    rw [frameConj_mul', ← hΓ, frameConj_inv_frameConj]
  have hΩ' : Ω = isomImage (h⁻¹ * φ) (unipDomain α β) := by
    rw [isomImage_mul, ← hΩ, isomImage_inv_isomImage]
  subst hΓ' hΩ'
  exact exists_unipotent_envelope_frame (h⁻¹ * φ) hL hc h1 h2


/-! ## §4 Finding: Barbot's envelope `π₁⁻¹(]−Y₊, Y₊[)` is neither a component nor maximal -/

section Finding

/-- **In `𝐌³` (`e = 1`) every component of `Ω(A)` is a half-space**: for `λ₁ = 1` (`T₀ = 1` on
`E = ℝ`, `1/‖T₀‖ = 1`) the slab `]−1, 1[` is not a component, the half-space `]−1, +∞[` is. So the
unbounded case of l.3678–3679 cannot be "the same" formula `π₁⁻¹(]−Y₊, Y₊[)`. -/
theorem not_isUnipComponent_slab_e1 :
    ¬ IsUnipComponent (![1] : Fin 1 → ℝ) ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) ∧
      IsUnipComponent (![1] : Fin 1 → ℝ) ((-1 : ℝ) : EReal) ⊤ := by
  refine ⟨fun ⟨_, _, _, hβ⟩ => ?_, ⟨EReal.coe_lt_top _, fun y hy _ i => ?_, Or.inr ⟨0, by simp,
    by norm_num⟩, Or.inl rfl⟩⟩
  · rcases hβ with h | ⟨i, -, h⟩
    · exact EReal.coe_ne_top _ h
    · fin_cases i
      have := EReal.coe_injective h
      norm_num at this
  · have hy' : (-1 : ℝ) < y := EReal.coe_lt_coe_iff.1 hy
    fin_cases i
    simp only [Matrix.cons_val_fin_one, mul_one]
    linarith

/-- **In `𝐌⁴` (`e = 2`) the slab `]−Y₊, Y₊[` can be a component and still not be maximal.**
Take `λ = (1, −1)`, the component `]−1, 1[`, and `Γ₀` generated by `t = (1, 0)` (any `t` with
`t₂ = 0`). Then `E = ℝ e₁`, `T₀ e₁ = e₁`, `‖T₀‖ = 1`, so `y₊ = Y₊ = 1`: this is exactly the case
"`M₀ = Γ₀\Ω`, i.e., `y₊ = Y₊`" which l.3668–3676 claims absolutely maximal. But `Γ₀` acts
identically through `λ' = (1, 0)` (`unipAction_congr`), for which the component of `Ω(A')`
containing `]−1, 1[` is the half-space `]−1, +∞[` — strictly larger. The envelope must be a
maximal interval admissible for `T₀` on `E`, not the symmetric slab of radius `1/‖T₀‖`. -/
theorem slab_not_maximal_e2 :
    (∀ t : EuclideanSpace ℝ (Fin 2), t 1 = 0 → ∀ p : Minkowski (2 + 1),
      unipAction (![1, -1] : Fin 2 → ℝ) t p = unipAction (![1, 0] : Fin 2 → ℝ) t p) ∧
    IsUnipComponent (![1, -1] : Fin 2 → ℝ) ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) ∧
    IsUnipComponent (![1, 0] : Fin 2 → ℝ) ((-1 : ℝ) : EReal) ⊤ ∧
    unipDomain (d := 2) ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) < unipDomain ((-1 : ℝ) : EReal) ⊤ := by
  refine ⟨fun t ht p => unipAction_congr (fun i => ?_) p, ?_, ?_, ?_⟩
  · fin_cases i
    · simp
    · simp [ht]
  · refine ⟨EReal.coe_lt_coe_iff.2 (by norm_num), fun y hy hy' i => ?_,
      Or.inr ⟨0, by simp, by norm_num⟩, Or.inr ⟨1, by simp, by norm_num⟩⟩
    have h1 : (-1 : ℝ) < y := EReal.coe_lt_coe_iff.1 hy
    have h2 : y < 1 := EReal.coe_lt_coe_iff.1 hy'
    fin_cases i
    · simp; linarith
    · simp; linarith
  · refine ⟨EReal.coe_lt_top _, fun y hy _ i => ?_, Or.inr ⟨0, by simp, by norm_num⟩, Or.inl rfl⟩
    have h1 : (-1 : ℝ) < y := EReal.coe_lt_coe_iff.1 hy
    fin_cases i
    · simp; linarith
    · simp
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun p hp => ⟨hp.1, EReal.coe_lt_top _⟩, ofNull 0 2 0, ?_, ?_⟩
    · show _ < ((nullY (ofNull (d := 2) 0 2 0) : ℝ) : EReal) ∧ _
      rw [nullY_ofNull]
      exact ⟨EReal.coe_lt_coe_iff.2 (by norm_num), EReal.coe_lt_top _⟩
    · rintro ⟨-, h⟩
      change ((nullY (ofNull (d := 2) 0 2 0) : ℝ) : EReal) < _ at h
      rw [nullY_ofNull] at h
      have := EReal.coe_lt_coe_iff.1 h
      norm_num at this

end Finding


/-! ## §5 The corrected envelope interval: maximal admissible intervals

The repair of l.3657–3666 (`docs`: SCOPE, finding). For `T` given on `E = span L` (`v = T u`),
an open interval `]a, b[ ⊆ [−∞, +∞]` is **admissible** when
`⟨u + y T u | u + y' T u⟩ ≥ 0` for all `u ∈ E` and all `a < y ≤ y' < b`: in Barbot's three
normalised cases this is exactly the conclusion of Prop 9.3 (`LimitesIneq`: `y = −y' = −a`
gives `|u|² − a²|T u|² ≥ 0`; `y' → +∞` gives `⟨u + y T u | T u⟩ ≥ 0`), and a sub-pair of an
admissible pair is admissible (the ball on a sub-diameter lies in the ball). The envelope's
interval is a **maximal** admissible interval containing `]α, β[` (`exists_maximal_unipAdmissible`),
and for a diagonal `T̂ = diag(λ)` on all of `ℝᵉ` admissibility is "no pole `−1/λᵢ` inside"
(`unipAdmissible_diag_iff`), so a maximal admissible interval of `T̂` is a component of `Ω(Â)`
(`isUnipComponent_of_maximal`). -/

section Admissible

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Admissibility of `]a, b[` for `T` on `E`** (the inequalities of Prop 9.3, unnormalised). -/
def UnipAdmissible (E : Submodule ℝ V) (T : V →ₗ[ℝ] V) (a b : EReal) : Prop :=
  ∀ y y' : ℝ, a < y → y ≤ y' → (y' : EReal) < b → ∀ u ∈ E, 0 ≤ ⟪u + y • T u, u + y' • T u⟫

theorem UnipAdmissible.mono {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} {a b a' b' : EReal}
    (h : UnipAdmissible E T a b) (ha : a ≤ a') (hb : b' ≤ b) : UnipAdmissible E T a' b' :=
  fun y y' hy hyy' hy' u hu => h y y' (ha.trans_lt hy) hyy' (hy'.trans_le hb) u hu

theorem UnipAdmissible.restrict {E F : Submodule ℝ V} {T : V →ₗ[ℝ] V} {a b : EReal}
    (h : UnipAdmissible F T a b) (hEF : E ≤ F) : UnipAdmissible E T a b :=
  fun y y' hy hyy' hy' u hu => h y y' hy hyy' hy' u (hEF hu)

/-- Admissibility depends on `T` on `E` only. -/
theorem UnipAdmissible.congr {E : Submodule ℝ V} {T T' : V →ₗ[ℝ] V} {a b : EReal}
    (h : UnipAdmissible E T a b) (hT : ∀ u ∈ E, T' u = T u) : UnipAdmissible E T' a b :=
  fun y y' hy hyy' hy' u hu => by rw [hT u hu]; exact h y y' hy hyy' hy' u hu

/-- **A maximal admissible interval exists** around any admissible one: first push `b` to the
supremum, then `a` to the infimum (admissibility is a condition on pairs, so it passes to
increasing unions). -/
theorem exists_maximal_unipAdmissible {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} {α β : EReal}
    (h : UnipAdmissible E T α β) :
    ∃ a b : EReal, a ≤ α ∧ β ≤ b ∧ UnipAdmissible E T a b ∧
      ∀ a' b' : EReal, a' ≤ a → b ≤ b' → UnipAdmissible E T a' b' → a' = a ∧ b' = b := by
  set B := {b : EReal | UnipAdmissible E T α b}
  set b := sSup B
  have hb : UnipAdmissible E T α b := by
    intro y y' hy hyy' hy' u hu
    obtain ⟨b₁, hb₁, hlt⟩ := lt_sSup_iff.1 hy'
    exact hb₁ y y' hy hyy' hlt u hu
  set A := {a : EReal | UnipAdmissible E T a b}
  set a := sInf A
  have ha : UnipAdmissible E T a b := by
    intro y y' hy hyy' hy' u hu
    obtain ⟨a₁, ha₁, hlt⟩ := sInf_lt_iff.1 hy
    exact ha₁ y y' hlt hyy' hy' u hu
  have haα : a ≤ α := sInf_le hb
  have hβb : β ≤ b := le_sSup h
  refine ⟨a, b, haα, hβb, ha, fun a' b' ha' hb' h' => ?_⟩
  have hb'B : b' ∈ B := h'.mono (ha'.trans haα) le_rfl
  have hbb : b' = b := le_antisymm (le_sSup hb'B) hb'
  subst hbb
  exact ⟨le_antisymm ha' (sInf_le h'), rfl⟩

variable {e : ℕ}

theorem inner_diagLin (ℓ : Fin e → ℝ) (y y' : ℝ) (u : EuclideanSpace ℝ (Fin e)) :
    ⟪u + y • diagLin ℓ u, u + y' • diagLin ℓ u⟫ =
      ∑ i, (1 + y * ℓ i) * (1 + y' * ℓ i) * u i ^ 2 := by
  simp only [diagLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **For a diagonal `T̂ = diag(λ)` on all of `ℝᵉ`, admissibility of `]a, b[` is the absence of a
pole `y = −1/λᵢ` in `]a, b[`** (Barbot's `Ω(A) = {1 + yλᵢ ≠ 0 ∀ i}`, l.661–662). -/
theorem unipAdmissible_diag_iff {ℓ : Fin e → ℝ} {a b : EReal} :
    UnipAdmissible ⊤ (diagLin ℓ) a b ↔
      ∀ y : ℝ, a < y → (y : EReal) < b → ∀ i, 1 + y * ℓ i ≠ 0 := by
  constructor
  · intro h y₀ hy₀ hy₀' i hpole
    obtain ⟨y₁, h1, h1'⟩ := EReal.lt_iff_exists_real_btwn.1 hy₀
    obtain ⟨y₂, h2, h2'⟩ := EReal.lt_iff_exists_real_btwn.1 hy₀'
    have h1r : y₁ < y₀ := EReal.coe_lt_coe_iff.1 h1'
    have h2r : y₀ < y₂ := EReal.coe_lt_coe_iff.1 h2
    have hℓ : ℓ i ≠ 0 := by rintro h0; rw [h0, mul_zero, add_zero] at hpole; exact one_ne_zero hpole
    have := h y₁ y₂ h1 (h1r.trans h2r).le h2' (EuclideanSpace.single i 1) trivial
    rw [inner_diagLin] at this
    simp only [PiLp.single_apply, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    have e1 : 1 + y₁ * ℓ i = (y₁ - y₀) * ℓ i := by linear_combination hpole
    have e2 : 1 + y₂ * ℓ i = (y₂ - y₀) * ℓ i := by linear_combination hpole
    rw [e1, e2] at this
    have hneg : (y₁ - y₀) * ℓ i * ((y₂ - y₀) * ℓ i) < 0 := by
      have : (y₁ - y₀) * ℓ i * ((y₂ - y₀) * ℓ i) = ((y₁ - y₀) * (y₂ - y₀)) * (ℓ i * ℓ i) := by ring
      rw [this]
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
        (mul_self_pos.2 hℓ)
    linarith
  · intro h y y' hy hyy' hy' u _
    rw [inner_diagLin]
    refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (sq_nonneg _)
    by_contra hneg
    push Not at hneg
    have hℓ : ℓ i ≠ 0 := by rintro h0; simp [h0] at hneg; linarith
    set z := -1 / ℓ i
    have ez : ∀ s : ℝ, 1 + s * ℓ i = (s - z) * ℓ i := fun s => by
      simp only [z]; field_simp; ring
    rw [ez, ez] at hneg
    have hprod : (y - z) * (y' - z) < 0 := by
      have : (y - z) * ℓ i * ((y' - z) * ℓ i) = ((y - z) * (y' - z)) * (ℓ i * ℓ i) := by ring
      rw [this] at hneg
      exact (neg_of_mul_neg_left hneg (mul_self_nonneg _))
    have hz1 : y < z := by nlinarith
    have hz2 : z < y' := by nlinarith
    exact h z (hy.trans (EReal.coe_lt_coe_iff.2 hz1)) ((EReal.coe_lt_coe_iff.2 hz2).trans hy') i
      (by rw [ez, sub_self, zero_mul])

/-- **A maximal admissible interval of a diagonal `T̂` is a component of `Ω(Â)`**: every finite
end is a pole (otherwise, the poles being finitely many, the interval extends past it). -/
theorem isUnipComponent_of_maximal {ℓ : Fin e → ℝ} {a b : EReal} (hab : a < b)
    (hadm : UnipAdmissible ⊤ (diagLin ℓ) a b)
    (hmax : ∀ a' b' : EReal, a' ≤ a → b ≤ b' → UnipAdmissible ⊤ (diagLin ℓ) a' b' →
      a' = a ∧ b' = b) :
    IsUnipComponent ℓ a b := by
  have hno := unipAdmissible_diag_iff.1 hadm
  -- the poles are finitely many
  set P : Set ℝ := {y | ∃ i, 1 + y * ℓ i = 0}
  have hP : P.Finite := by
    refine (Set.finite_range fun i => -1 / ℓ i).subset ?_
    rintro y ⟨i, hi⟩
    have hℓ : ℓ i ≠ 0 := by rintro h0; rw [h0, mul_zero, add_zero] at hi; exact one_ne_zero hi
    exact ⟨i, by field_simp; linarith⟩
  have hPo : IsOpen Pᶜ := hP.isClosed.isOpen_compl
  have pole_of : ∀ r : ℝ, r ∈ P → ∃ i, ℓ i ≠ 0 ∧ ((r : ℝ) : EReal) = ((-1 / ℓ i : ℝ) : EReal) := by
    rintro r ⟨i, hi⟩
    have hℓ : ℓ i ≠ 0 := by rintro h0; rw [h0, mul_zero, add_zero] at hi; exact one_ne_zero hi
    exact ⟨i, hℓ, by congr 1; field_simp; linarith⟩
  refine ⟨hab, hno, ?_, ?_⟩
  · -- the left end
    by_contra hcon
    push Not at hcon
    obtain ⟨hbot, hnp⟩ := hcon
    induction a using EReal.rec with
    | bot => exact hbot rfl
    | top => exact absurd hab (not_lt.2 le_top)
    | coe s =>
      have hsP : s ∉ P := fun hs => by
        obtain ⟨i, hi, hi'⟩ := pole_of s hs
        exact hnp i hi hi'
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hPo s hsP
      have hadm' : UnipAdmissible ⊤ (diagLin ℓ) ((s - ε / 2 : ℝ) : EReal) b := by
        refine unipAdmissible_diag_iff.2 fun y hy hy' i => ?_
        by_cases hys : s < y
        · exact hno y (EReal.coe_lt_coe_iff.2 hys) hy' i
        · push Not at hys
          have hy1 : s - ε / 2 < y := EReal.coe_lt_coe_iff.1 hy
          have hyb : y ∈ Metric.ball s ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
          exact fun h0 => hball hyb ⟨i, h0⟩
      have := (hmax _ b (EReal.coe_le_coe_iff.2 (by linarith)) le_rfl hadm').1
      have := EReal.coe_injective this
      linarith
  · -- the right end
    by_contra hcon
    push Not at hcon
    obtain ⟨htop, hnp⟩ := hcon
    induction b using EReal.rec with
    | bot => exact absurd hab (not_lt.2 bot_le)
    | top => exact htop rfl
    | coe r =>
      have hrP : r ∉ P := fun hr => by
        obtain ⟨i, hi, hi'⟩ := pole_of r hr
        exact hnp i hi hi'
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hPo r hrP
      have hadm' : UnipAdmissible ⊤ (diagLin ℓ) a ((r + ε / 2 : ℝ) : EReal) := by
        refine unipAdmissible_diag_iff.2 fun y hy hy' i => ?_
        by_cases hyr : y < r
        · exact hno y hy (EReal.coe_lt_coe_iff.2 hyr) i
        · push Not at hyr
          have hy1 : y < r + ε / 2 := EReal.coe_lt_coe_iff.1 hy'
          have hyb : y ∈ Metric.ball r ε := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
          exact fun h0 => hball hyb ⟨i, h0⟩
      have := (hmax a _ le_rfl (EReal.coe_le_coe_iff.2 (by linarith)) hadm').2
      have := EReal.coe_injective this
      linarith


/-- The form `⟨u + yTu | u + y'Tu⟩ = |u|² + (y + y')⟨u | Tu⟩ + yy'|Tu|²`. -/
theorem inner_add_smul_expand (T : V →ₗ[ℝ] V) (y y' : ℝ) (u : V) :
    ⟪u + y • T u, u + y' • T u⟫ = ‖u‖ ^ 2 + (y + y') * ⟪u, T u⟫ + y * y' * ‖T u‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, conj_trivial]
  rw [real_inner_comm (T u) u]
  ring

/-- **Prop 9.3's three normalised conclusions are admissibility** (`LimitesIneq` ⇒
`UnipAdmissible`): the one-sided cases because `⟨u + yTu | u + y'Tu⟩ = |u + yTu|² +
(y' − y)⟨u + yTu | Tu⟩`, the bounded case because the form is affine in each of `y`, `y'` and
nonnegative at the corners of `{−a ≤ y ≤ y' ≤ a}`. -/
theorem unipAdmissible_of_limitesIneq {E : Submodule ℝ V} {T : V →ₗ[ℝ] V} {ylo yhi : EReal}
    (hlo : ylo < 0) (hhi : 0 < yhi) (hnorm : ylo = -yhi ∨ yhi = ⊤ ∨ ylo = ⊥)
    (hfin : ¬(ylo = ⊥ ∧ yhi = ⊤)) (h : LimitesIneq E T ylo yhi) :
    UnipAdmissible E T ylo yhi := by
  intro y y' hy hyy' hy' u hu
  rw [inner_add_smul_expand]
  have hsq : ∀ s : ℝ, 0 ≤ ‖u‖ ^ 2 + 2 * s * ⟪u, T u⟫ + s ^ 2 * ‖T u‖ ^ 2 := fun s => by
    have := inner_add_smul_expand T s s u
    rw [real_inner_self_eq_norm_sq] at this
    nlinarith [sq_nonneg ‖u + s • T u‖]
  have hk : 0 ≤ ‖T u‖ ^ 2 := sq_nonneg _
  induction yhi using EReal.rec with
  | bot => exact absurd hhi (not_lt.2 bot_le)
  | top =>
    induction ylo using EReal.rec with
    | bot => exact absurd ⟨rfl, rfl⟩ hfin
    | top => exact absurd hlo (not_lt.2 le_top)
    | coe b =>
      have hb := h.2.1 b rfl rfl u hu
      have hyb : b < y := EReal.coe_lt_coe_iff.1 hy
      have e1 : ‖u‖ ^ 2 + (y + y') * ⟪u, T u⟫ + y * y' * ‖T u‖ ^ 2 =
          (‖u‖ ^ 2 + 2 * y * ⟪u, T u⟫ + y ^ 2 * ‖T u‖ ^ 2) +
            (y' - y) * (⟪u, T u⟫ + y * ‖T u‖ ^ 2) := by ring
      rw [e1]
      refine add_nonneg (hsq y) (mul_nonneg (by linarith) ?_)
      nlinarith
  | coe a =>
    have ha : 0 < a := by exact_mod_cast hhi
    have hya : y' < a := EReal.coe_lt_coe_iff.1 hy'
    rcases hnorm with hn | hn | hn
    · have hyl : ylo = ((-a : ℝ) : EReal) := by rw [hn]; rfl
      have h1 := h.1 a rfl hyl u hu
      have hU : 0 ≤ ‖u‖ ^ 2 - a ^ 2 * ‖T u‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h1
        nlinarith [norm_nonneg (T u), norm_nonneg u, mul_nonneg ha.le (norm_nonneg (T u))]
      have hay : -a < y := by rw [hyl] at hy; exact EReal.coe_lt_coe_iff.1 hy
      set U := ‖u‖ ^ 2
      set c := ⟪u, T u⟫
      set k := ‖T u‖ ^ 2
      have hψ : 0 ≤ U + (y' - a) * c - a * y' * k := by
        have h1 : 0 ≤ (a - y') * (U + 2 * (-a) * c + (-a) ^ 2 * k) :=
          mul_nonneg (by linarith) (hsq (-a))
        have h2 : 0 ≤ (y' + a) * (U - a ^ 2 * k) := mul_nonneg (by linarith) hU
        have e : (2 * a) * (U + (y' - a) * c - a * y' * k) =
            (a - y') * (U + 2 * (-a) * c + (-a) ^ 2 * k) + (y' + a) * (U - a ^ 2 * k) := by ring
        nlinarith
      have h1 : 0 ≤ (y' - y) * (U + (y' - a) * c - a * y' * k) := mul_nonneg (by linarith) hψ
      have h2 : 0 ≤ (y + a) * (U + 2 * y' * c + y' ^ 2 * k) := mul_nonneg (by linarith) (hsq y')
      have e : (y' + a) * (U + (y + y') * c + y * y' * k) =
          (y' - y) * (U + (y' - a) * c - a * y' * k) + (y + a) * (U + 2 * y' * c + y' ^ 2 * k) := by
        ring
      nlinarith
    · exact absurd hn (EReal.coe_ne_top a)
    · have h1 := h.2.2 a rfl hn u hu
      have e1 : ‖u‖ ^ 2 + (y + y') * ⟪u, T u⟫ + y * y' * ‖T u‖ ^ 2 =
          (‖u‖ ^ 2 + 2 * y' * ⟪u, T u⟫ + y' ^ 2 * ‖T u‖ ^ 2) -
            (y' - y) * (⟪u, T u⟫ + y' * ‖T u‖ ^ 2) := by ring
      rw [e1]
      have : ⟪u, T u⟫ + y' * ‖T u‖ ^ 2 ≤ 0 := by nlinarith
      nlinarith [hsq y', mul_nonneg (sub_nonneg.2 hyy') (neg_nonneg.2 this)]

/-- **The starting point**: the given component `]α, β[` of `Ω(A)` is admissible for `T = diag(λ)`
on `E = span L` (indeed on all of `ℝᵉ`). -/
theorem unipAdmissible_of_isUnipComponent {ℓ : Fin e → ℝ} {α β : EReal}
    (hc : IsUnipComponent ℓ α β) (E : Submodule ℝ (EuclideanSpace ℝ (Fin e))) :
    UnipAdmissible E (diagLin ℓ) α β :=
  (unipAdmissible_diag_iff.2 hc.2.1).restrict le_top

end Admissible

end Causal.Flat.Cla
