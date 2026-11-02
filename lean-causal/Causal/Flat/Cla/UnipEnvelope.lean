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
No label is certified: the prose item [11.i] has no environment. It serves `Flat/Classification`'s
`exists_absMax_unipotent_ltp` (G1: the envelope and its maximality; the lifting glue turning the
last conjunct into `AbsMax` stays there).

* `exists_unipotent_envelope` — **proved, no `sorry`**, in a **corrected** form: the envelope is
  `ψ(]a, b[)` for a **maximal admissible** interval `]a, b[ ⊇ ]α, β[`, not Barbot's slab
  `π₁⁻¹(]−Y₊, Y₊[)`, which is neither a component nor maximal in general (finding below).
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.

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
does **not** give "`−Y₊ ≤ y'₋` and `y'₊ ≤ Y₊`" for a non-symmetric `]y'₋, y'₊[`. In `𝐌³`
(`e = 1`) a bounded `I₀` never occurs and every component is a half-space
(`not_isUnipComponent_slab_e1`), so the "similar" unbounded case cannot be the same formula. Also:
9.3 gives `‖T₀‖ ≤ 1/y₊` (with equality in the example), not "less than".
**Correction (proved here).** Call `]a, b[` *admissible* when `⟨u + yTu | u + y'Tu⟩ ≥ 0` for
`u ∈ E = span L`, `a < y ≤ y' < b` (Prop 9.3's leading coefficient, l.2974–2979, unnormalised).
Take a maximal admissible `]a, b[ ⊇ ]α, β[`; after the change of origin to an interior `m`
(Barbot's "without loss of generality"), Prop 9.5 extends `T` at `]a, b[`, the extension
diagonalises in a positively oriented frame, and `]a, b[` is a component of its `Ω(Â)`.
**Finding (maximality, l.3668–3676).** No exclusion of loxodromic elements of `Γ₁` and no
normalisation of `π₁(Ω₁)` is needed: Prop 9.3's leading coefficient for `gΓ₀g⁻¹` alone, on the
acausal `Σ_N`, makes the interior of `π₁(Σ_N)` admissible, and maximality closes it.

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, Barbot's `n` is `d + 1`. Here `𝐌ⁿ = Minkowski (e + 1)`, `n = e + 2`, and the
unipotent parameters live in `ℝᵉ = ℝ^{n−2}` (`Fin e → ℝ`).

## What is proved (no `sorry`)

* **§1 Step 0, rigidity** — `exists_frame_of_isQuotientOf_convex`: two convex presentations
  `Γ\Ω = Γ'\Ω'` of one flat spacetime differ by one `h ∈ Isom(𝐌ⁿ)`, `hΩ = Ω'`, `hΓh⁻¹ = Γ'`;
  the main theorem reduces to the canonical presentation (`exists_unipotent_envelope_frame`).
* **§2 The translation case** (`λᵢtᵢ = 0` for all `t ∈ L`): the envelope is `𝐌ⁿ`.
* **§5 Admissible intervals**: `UnipAdmissible`, `exists_maximal_unipAdmissible`,
  `unipAdmissible_diag_iff`, `isUnipComponent_of_maximal`, `unipAdmissible_of_limitesIneq`.
* **§6 The extension at the maximal interval** (l.3654–3664, repaired): `exists_shift_extension`
  (change of origin, `limitesIneq_of_unipAdmissible`, `bprop_extension`, maximality transported),
  `exists_rot_diag` (`Ŝ = R diag(λ₂) R⁻¹`, `det R = 1`).
* **§7 The new frame** `φ₂ = ψ ∘ τ_m ∘ ρ_R`: `nullShift`, `rotIsom` (an element of `Isom(𝐌ⁿ)`,
  `rotLin_mem_lorentz`), `conj_unipAction` (`Γ₀` acts by `unipAction λ₂ (R⁻¹(t + mTt))`).
* **§8 The quotient**: freeness and proper discontinuity on the component (local copies),
  `ballFinite_map_of_injOn` (the new lattice is discrete).
* **§9 Maximality** (l.3668–3676, repaired): `unipAdmissible_of_achronal`,
  `mem_unipDomain_of_isOpen`, `envelopeMaximal_of_maximal`, through
  `range_subset_dependenceDomain_of_developsCC` (every null line of `𝒟(Ñ)` meets `Σ_N`).
* **§10 Assembly**, **§11**: `exists_normalisation`, `not_bot_top_of_unipAdmissible`,
  `unipAdmissible_rot_iff`, the slabs in the new frame; `exists_unipotent_envelope_frame`.
* The finding's witnesses: `not_isUnipComponent_slab_e1`, `slab_not_maximal_e2`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M₀` unipotent, `Γ₀\Ω₀` | ✓ carried: `IsUnipotentSpacetime M₁` and a **convex** presentation `IsQuotientOf M₁ Γ Ω` (the one `Flat/Classification` holds; rigidity identifies it with the canonical one) |
| "tamely embeds in `Γ₀\Ω`" | ✓ in the form `Ω ≤ Ω₂`, same `Γ`, `Ω₂` convex (tameness is `Flat/Cla/TameNested`) |
| absolute maximality of `Γ₀\Ω` | ⚠ in the form consumed by Classification's glue: the developing image of a (CC′) target containing `gΩ₂`, `gΓg⁻¹ ≤ ρ(Deck)`, is `gΩ₂` (`EnvelopeMaximal`) |
| `Ω = π₁⁻¹(]−Y₊, Y₊[)` | ⚠ corrected: `Ω₂ = ψ(]a, b[)`, `]a, b[` maximal admissible (finding) |
| the unbounded case "similar" (G1) | ✓ included in the statement (no boundedness hypothesis) |

## SCOPE (disclosed)

* **No `sorry`.** The theorem is the corrected envelope, not Barbot's slab (finding); the
  maximality conjunct is the `EnvelopeMaximal` form, from which Classification's glue
  (`exists_lift_of_isQuotientOf`, `exists_deck_of_lift`, `surjective_of_lift_of_range_subset`)
  derives `AbsMax` for Cauchy-complete targets.
* No `Flat/Lox/*`, `Flat/Nonlox/*` import. `Flat/Classification` and the sibling
  `Flat/Cla/UnipComplete` are not imported; `isLocalIsometry_of_comp_left`, `isom_ext'` and the
  §8 freeness/properness lemmas (`env_unip_*`) are **private** copies.

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


/-! ## §3 The maximality conjunct -/

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

end Envelope
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


/-! ## §6 The extension at the maximal interval (the repaired l.3654–3664)

After a change of origin `y ↦ y − m` (`m` interior to the maximal admissible `]a, b[`), the
vectors `u` of `Γ₀` become `u + m T u` and `v = T u` is unchanged, so `T` is replaced on
`E' = (1 + mT)E` by `S` with `S (u + m T u) = T u`; the interval is normalised (`]−r, r[`, or
one end infinite), Prop 9.5 (`bprop_extension`) extends `S` to a symmetric `Ŝ` on `ℝᵉ`, still
admissible on the shifted interval and maximal there; then `Ŝ = R diag(λ₂) R⁻¹`. -/

section Extension

open scoped RealInnerProductSpace

variable {e : ℕ}

theorem ereal_add_coe_lt_coe_iff (c : EReal) (m y : ℝ) :
    c + (m : EReal) < (y : EReal) ↔ c < ((y - m : ℝ) : EReal) := by
  induction c using EReal.rec with
  | bot => exact iff_of_true (by rw [EReal.bot_add]; exact EReal.bot_lt_coe _) (EReal.bot_lt_coe _)
  | top => exact iff_of_false (by rw [EReal.top_add_coe]; exact not_lt.2 le_top) (not_lt.2 le_top)
  | coe c =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

theorem coe_lt_ereal_add_coe_iff (c : EReal) (m y : ℝ) :
    (y : EReal) < c + (m : EReal) ↔ ((y - m : ℝ) : EReal) < c := by
  induction c using EReal.rec with
  | bot => exact iff_of_false (by rw [EReal.bot_add]; exact not_lt.2 bot_le) (not_lt.2 bot_le)
  | top => exact iff_of_true (by rw [EReal.top_add_coe]; exact EReal.coe_lt_top _) (EReal.coe_lt_top _)
  | coe c =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

theorem ereal_add_coe_cancel {c c' : EReal} (m : ℝ) (h : c + (m : EReal) = c' + m) : c = c' := by
  induction c using EReal.rec with
  | bot =>
    induction c' using EReal.rec with
    | bot => rfl
    | top => simp at h
    | coe c' => rw [EReal.bot_add, ← EReal.coe_add] at h; exact absurd h.symm (EReal.coe_ne_bot _)
  | top =>
    induction c' using EReal.rec with
    | bot => simp at h
    | top => rfl
    | coe c' => rw [EReal.top_add_coe, ← EReal.coe_add] at h; exact absurd h.symm (EReal.coe_ne_top _)
  | coe c =>
    induction c' using EReal.rec with
    | bot => rw [EReal.bot_add, ← EReal.coe_add] at h; exact absurd h (EReal.coe_ne_bot _)
    | top => rw [EReal.top_add_coe, ← EReal.coe_add] at h; exact absurd h (EReal.coe_ne_top _)
    | coe c' =>
      rw [← EReal.coe_add, ← EReal.coe_add] at h
      have := EReal.coe_injective h
      congr 1; linarith

/-- **Undoing the change of origin**: an interval admissible for `S` on `E'` gives, shifted by
`m`, an interval admissible for `T` on `E`. -/
theorem UnipAdmissible.unshift {E E' : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T S : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} {m : ℝ}
    (hE : ∀ u ∈ E, u + m • T u ∈ E') (hS : ∀ u ∈ E, S (u + m • T u) = T u) {c d : EReal}
    (h : UnipAdmissible E' S c d) : UnipAdmissible E T (c + m) (d + m) := by
  intro y y' hy hyy' hy' u hu
  have := h (y - m) (y' - m) ((ereal_add_coe_lt_coe_iff c m y).1 hy) (by linarith)
    ((coe_lt_ereal_add_coe_iff d m y').1 hy') _ (hE u hu)
  rw [hS u hu] at this
  have e1 : u + y • T u = u + m • T u + (y - m) • T u := by rw [sub_smul]; abel
  have e2 : u + y' • T u = u + m • T u + (y' - m) • T u := by rw [sub_smul]; abel
  rw [e1, e2]; exact this

/-- **The change of origin**: the converse direction. -/
theorem UnipAdmissible.shift {E E' : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T S : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} {m : ℝ}
    (hE' : ∀ u' ∈ E', ∃ u ∈ E, u' = u + m • T u) (hS : ∀ u ∈ E, S (u + m • T u) = T u)
    {c d : EReal} (h : UnipAdmissible E T (c + m) (d + m)) : UnipAdmissible E' S c d := by
  intro y y' hy hyy' hy' u' hu'
  obtain ⟨u, hu, rfl⟩ := hE' u' hu'
  have := h (y + m) (y' + m) ((ereal_add_coe_lt_coe_iff c m (y + m)).2 (by simpa using hy))
    (by linarith) ((coe_lt_ereal_add_coe_iff d m (y' + m)).2 (by simpa using hy')) u hu
  rw [hS u hu]
  have e1 : u + m • T u + y • T u = u + (y + m) • T u := by rw [add_smul]; abel
  have e2 : u + m • T u + y' • T u = u + (y' + m) • T u := by rw [add_smul]; abel
  rw [e1, e2]; exact this

/-- **Prop 9.3's normalised conclusions from admissibility** (the converse of
`unipAdmissible_of_limitesIneq`, through `limites_of_leading`). -/
theorem limitesIneq_of_unipAdmissible {E : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} {ylo yhi : EReal}
    (hlo : ylo < 0) (hhi : 0 < yhi) (h : UnipAdmissible E T ylo yhi) (hpar : ∃ u ∈ E, T u ≠ 0) :
    LimitesIneq E T ylo yhi := by
  have := limites_of_leading (L := E.toAddSubgroup) hlo hhi (fun u hu y y' hy hy₁ hy' hy₁' => by
    rcases le_total y y' with hyy | hyy
    · exact h y y' hy hyy hy₁' u hu
    · rw [real_inner_comm]; exact h y' y hy' hyy hy₁ u hu) hpar
  simpa [Submodule.coe_toAddSubgroup, Submodule.span_eq] using this.2

/-- **`1 + mT` is injective on `E` at an interior point `m` of an admissible interval.** -/
theorem eq_zero_of_add_smul_eq_zero {E : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} {a b : EReal} {m : ℝ}
    (h : UnipAdmissible E T a b) (ha : a < m) (hb : (m : EReal) < b) {u : EuclideanSpace ℝ (Fin e)}
    (hu : u ∈ E) (h0 : u + m • T u = 0) : u = 0 := by
  obtain ⟨y, hy, hym⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  obtain ⟨y', hmy', hy'⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  have hym' : y < m := EReal.coe_lt_coe_iff.1 hym
  have hmy'' : m < y' := EReal.coe_lt_coe_iff.1 hmy'
  have := h y y' hy (by linarith) hy' u hu
  have e1 : u + y • T u = (y - m) • T u := by
    rw [show u + y • T u = (u + m • T u) + (y - m) • T u by rw [sub_smul]; abel, h0, zero_add]
  have e2 : u + y' • T u = (y' - m) • T u := by
    rw [show u + y' • T u = (u + m • T u) + (y' - m) • T u by rw [sub_smul]; abel, h0, zero_add]
  rw [e1, e2, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq] at this
  simp only [conj_trivial] at this
  have hneg : (y - m) * (y' - m) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hT : ‖T u‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖T u‖]
  have hT0 : T u = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hT (sq_nonneg _)))
  rw [hT0, smul_zero, add_zero] at h0
  exact h0

/-- **The extension at the maximal interval** (the repaired l.3654–3664). Let `]a₂ + m, b₂ + m[`
be a maximal admissible interval for `T` (symmetric) on `E`, with `a₂ < 0 < b₂` normalised as in
Prop 9.3 and `T` nonzero on `E`. Then `S`, defined on `E' = (1 + mT)E` by `S(u + mTu) = Tu`,
extends to a symmetric `Ŝ` on `ℝᵉ` for which `]a₂, b₂[` is admissible on all of `ℝᵉ`, and
maximal there. -/
theorem exists_shift_extension {E : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} (hT : IsSymmOn ⊤ T)
    {a₂ b₂ : EReal} {m : ℝ} (hlo : a₂ < 0) (hhi : 0 < b₂) (hnorm : a₂ = -b₂ ∨ b₂ = ⊤ ∨ a₂ = ⊥)
    (hfin : ¬(a₂ = ⊥ ∧ b₂ = ⊤)) (hadm : UnipAdmissible E T (a₂ + m) (b₂ + m))
    (hmax : ∀ a' b' : EReal, a' ≤ a₂ + m → b₂ + m ≤ b' → UnipAdmissible E T a' b' →
      a' = a₂ + m ∧ b' = b₂ + m)
    (hpar : ∃ u ∈ E, T u ≠ 0) :
    ∃ Ŝ : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e),
      (∀ u ∈ E, Ŝ (u + m • T u) = T u) ∧ IsSymmOn ⊤ Ŝ ∧ UnipAdmissible ⊤ Ŝ a₂ b₂ ∧
      ∀ a' b' : EReal, a' ≤ a₂ → b₂ ≤ b' → UnipAdmissible ⊤ Ŝ a' b' → a' = a₂ ∧ b' = b₂ := by
  have ham : a₂ + (m : EReal) < (m : EReal) :=
    (ereal_add_coe_lt_coe_iff a₂ m m).2 (by rw [sub_self]; exact_mod_cast hlo)
  have hbm : (m : EReal) < b₂ + (m : EReal) :=
    (coe_lt_ereal_add_coe_iff b₂ m m).2 (by rw [sub_self]; exact_mod_cast hhi)
  -- the shift `u ↦ u + m T u` on `E`, injective
  set f : E →ₗ[ℝ] EuclideanSpace ℝ (Fin e) := (LinearMap.id + m • T).domRestrict E with hf
  have hfapp : ∀ u : E, f u = (u : EuclideanSpace ℝ (Fin e)) + m • T u := fun u => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hfapp] at hu
    exact Subtype.ext (eq_zero_of_add_smul_eq_zero hadm ham hbm u.2 hu)
  set E' : Submodule ℝ (EuclideanSpace ℝ (Fin e)) := LinearMap.range f with hE'
  set eqv : E ≃ₗ[ℝ] E' := LinearEquiv.ofInjective f hinj
  obtain ⟨S, hS⟩ := LinearMap.exists_extend ((T.domRestrict E) ∘ₗ eqv.symm.toLinearMap)
  have hSf : ∀ u : E, S (f u) = T u := by
    intro u
    have := congrArg (fun g => g (eqv u)) hS
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply] at this
    rw [← this]; rfl
  have hSE : ∀ u ∈ E, S (u + m • T u) = T u := fun u hu => hSf ⟨u, hu⟩
  have hmemE' : ∀ u ∈ E, u + m • T u ∈ E' := fun u hu => ⟨⟨u, hu⟩, rfl⟩
  have hE'E : ∀ u' ∈ E', ∃ u ∈ E, u' = u + m • T u := by
    rintro _ ⟨u, rfl⟩; exact ⟨u, u.2, rfl⟩
  -- `S` is symmetric on `E'`
  have hSsym : IsSymmOn E' S := by
    intro u' hu' w' hw'
    obtain ⟨u, hu, rfl⟩ := hE'E u' hu'
    obtain ⟨w, hw, rfl⟩ := hE'E w' hw'
    rw [hSE u hu, hSE w hw, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
      hT u trivial w trivial, real_inner_comm (T u) (T w)]
  have hadm' : UnipAdmissible E' S a₂ b₂ := UnipAdmissible.shift hE'E hSE hadm
  have hpar' : ∃ u ∈ E', S u ≠ 0 := by
    obtain ⟨u, hu, hTu⟩ := hpar
    exact ⟨_, hmemE' u hu, by rw [hSE u hu]; exact hTu⟩
  obtain ⟨Ŝ, hext, hsym, hlim⟩ := bprop_extension hSsym hlo hhi hnorm hfin
    (limitesIneq_of_unipAdmissible hlo hhi hadm' hpar')
  refine ⟨Ŝ, fun u hu => by rw [hext _ (hmemE' u hu), hSE u hu], hsym,
    unipAdmissible_of_limitesIneq hlo hhi hnorm hfin hlim, fun a' b' ha' hb' h' => ?_⟩
  have h1 : UnipAdmissible E' S a' b' := (h'.restrict le_top).congr fun u hu => (hext u hu).symm
  have h2 := UnipAdmissible.unshift hmemE' hSE h1
  obtain ⟨e1, e2⟩ := hmax _ _ (add_le_add ha' le_rfl) (add_le_add hb' le_rfl) h2
  exact ⟨ereal_add_coe_cancel m e1, ereal_add_coe_cancel m e2⟩

/-- **Diagonalisation in a positively oriented orthonormal frame** (`Ŝ = R diag(λ₂) R⁻¹`,
`det R = 1`; for `e ≥ 1`, through `adjustToOrientation`). -/
theorem exists_rot_diag (he : 0 < e)
    {Ŝ : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)} (hS : IsSymmOn ⊤ Ŝ) :
    ∃ (R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)) (ℓ₂ : Fin e → ℝ),
      LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1 ∧
        ∀ t, Ŝ (R t) = R (diagLin ℓ₂ t) := by
  have hsym : Ŝ.IsSymmetric := fun x y => by
    rw [real_inner_comm]; exact hS y trivial x trivial
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin e)) = e := finrank_euclideanSpace_fin
  haveI : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  set s := EuclideanSpace.basisFun (Fin e) ℝ
  set b := (hsym.eigenvectorBasis hn).adjustToOrientation s.toBasis.orientation
  set ev := hsym.eigenvalues hn
  have hb : ∀ i, Ŝ (b i) = ev i • b i := by
    intro i
    rcases (hsym.eigenvectorBasis hn).adjustToOrientation_apply_eq_or_eq_neg
      s.toBasis.orientation i with h | h
    · rw [h, hsym.apply_eigenvectorBasis]; rfl
    · rw [h, map_neg, hsym.apply_eigenvectorBasis, smul_neg]; rfl
  refine ⟨b.repr.symm, ev, ?_, fun t => ?_⟩
  · have hpos : 0 < s.toBasis.det b := by
      have := (Module.Basis.orientation_eq_iff_det_pos s.toBasis b.toBasis).1
        ((hsym.eigenvectorBasis hn).orientation_adjustToOrientation _).symm
      simpa using this
    have h1 : s.toBasis.det b = 1 := by
      rcases s.det_to_matrix_orthonormalBasis_real b with h | h
      · exact h
      · rw [h] at hpos; norm_num at hpos
    have h2 := s.toBasis.det_comp (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) s
    have h3 : ((b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) ∘ s) = b := by
      funext i
      simp [s, EuclideanSpace.basisFun_apply]
    have h4 : s.toBasis.det s = 1 := by simpa using s.toBasis.det_self
    rw [h3, h4, mul_one] at h2
    rw [← h2]; exact_mod_cast h1
  · apply b.repr.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext i
    rw [OrthonormalBasis.repr_apply_apply, ← hsym, hb i, inner_smul_left, ← OrthonormalBasis.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    simp [diagLin]

end Extension


/-! ## §7 The new frame: a null translation and a rotation of the `z`-coordinates

The frame of the envelope is `φ₂ = ψ ∘ τ_m ∘ ρ_R`: `τ_m` the translation by the null vector
`ofNull 0 m 0` (`y ↦ y + m`, Barbot's change of origin in `y`), `ρ_R` the rotation `z ↦ R z` of
the `z`-coordinates (`R ∈ SO(e)`, which diagonalises `Ŝ`). In Barbot's coordinates they act by
`(x, z, y) ↦ (x, z, y + m)` and `(x, z, y) ↦ (x, R z, y)`. -/

section Frames

open scoped RealInnerProductSpace

variable {e : ℕ}

/-- **The null translation** `τ_m`, by `ofNull 0 m 0`. -/
noncomputable def nullShift (m : ℝ) : isom (e + 1) :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski (e + 1)) (ofNull 0 m 0), constVAdd_mem_isom _⟩

theorem nullShift_smul (m : ℝ) (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    (nullShift m : isom (e + 1)) • nolToMink X = nolToMink (X.1, X.2.1, X.2.2 + m) := by
  rw [isom_smul_def]
  show AffineEquiv.constVAdd ℝ (Minkowski (e + 1)) (ofNull 0 m 0) (nolToMink X) = _
  rw [AffineEquiv.constVAdd_apply, vadd_eq_add]
  have h0 : (ofNull 0 m 0 : Minkowski (e + 1)) = nolToMinkₗ ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin e)), m) :=
    rfl
  have h1 : nolToMink X = nolToMinkₗ X := rfl
  have h2 : nolToMink (X.1, X.2.1, X.2.2 + m) = nolToMinkₗ (X.1, X.2.1, X.2.2 + m) := rfl
  rw [h0, h1, h2, ← map_add]
  congr 1
  obtain ⟨x, z, y⟩ := X
  simp [add_comm]

theorem nullShift_inv_smul (m : ℝ) (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    (nullShift m : isom (e + 1))⁻¹ • nolToMink X = nolToMink (X.1, X.2.1, X.2.2 - m) := by
  rw [inv_smul_eq_iff, nullShift_smul]
  simp

/-- Barbot's coordinates as a linear equivalence. -/
noncomputable def nolEquiv : (ℝ × EuclideanSpace ℝ (Fin e) × ℝ) ≃ₗ[ℝ] Minkowski (e + 1) :=
  LinearEquiv.ofLinear nolToMinkₗ minkToNolₗ (LinearMap.ext fun p => nolToMink_minkToNol p)
    (LinearMap.ext fun X => minkToNol_nolToMink X)

/-- The block map `(x, z, y) ↦ (x, R z, y)`. -/
noncomputable def rotBlock (R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)) :
    (ℝ × EuclideanSpace ℝ (Fin e) × ℝ) ≃ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :=
  (LinearEquiv.refl ℝ ℝ).prodCongr (R.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ))

/-- **The rotation of the `z`-coordinates**, `ρ_R`. -/
noncomputable def rotLin (R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)) :
    Minkowski (e + 1) ≃ₗ[ℝ] Minkowski (e + 1) :=
  nolEquiv.symm ≪≫ₗ rotBlock R ≪≫ₗ nolEquiv

theorem rotLin_nolToMink (R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e))
    (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    rotLin R (nolToMink X) = nolToMink (X.1, R X.2.1, X.2.2) := by
  have : nolEquiv.symm (nolToMink X) = X := minkToNol_nolToMink X
  simp only [rotLin, LinearEquiv.trans_apply, this]
  rfl

theorem fst_nolToMink (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    (nolToMink X).1 = (X.1 - X.2.2) / √2 := rfl

theorem rotLin_mem_lorentz {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1) :
    rotLin R ∈ lorentz (e + 1) := by
  have hX : ∀ v : Minkowski (e + 1), ∃ X, v = nolToMink X :=
    fun v => ⟨minkToNol v, (nolToMink_minkToNol v).symm⟩
  refine mem_lorentz_of (fun v => ?_) ?_ ?_
  · obtain ⟨X, rfl⟩ := hX v
    rw [rotLin_nolToMink, minkQ_nolToMink, minkQ_nolToMink]
    simp [nolQ]
  · obtain ⟨X, hX'⟩ := hX (timeUnit (e + 1))
    rw [hX', rotLin_nolToMink, fst_nolToMink]
    have : (nolToMink X).1 = 1 := by rw [← hX']; rfl
    rw [fst_nolToMink] at this
    rw [this]; exact one_pos
  · have e1 : (rotLin R : Minkowski (e + 1) →ₗ[ℝ] Minkowski (e + 1)) =
        (nolEquiv (e := e)).toLinearMap ∘ₗ (rotBlock R).toLinearMap ∘ₗ
          (nolEquiv (e := e)).symm.toLinearMap :=
      LinearMap.ext fun _ => rfl
    rw [e1, LinearMap.det_conj, rotBlock, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
      LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, hR]
    simp

/-- **`ρ_R` as an isometry.** -/
noncomputable def rotIsom (R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e))
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1) : isom (e + 1) :=
  ⟨(rotLin R).toAffineEquiv, mem_isom_iff.2 (rotLin_mem_lorentz hR)⟩

theorem rotIsom_smul {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1)
    (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    rotIsom R hR • nolToMink X = nolToMink (X.1, R X.2.1, X.2.2) := by
  rw [isom_smul_def]
  exact rotLin_nolToMink R X

theorem rotIsom_inv_smul {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1)
    (X : ℝ × EuclideanSpace ℝ (Fin e) × ℝ) :
    (rotIsom R hR)⁻¹ • nolToMink X = nolToMink (X.1, R.symm X.2.1, X.2.2) := by
  rw [inv_smul_eq_iff, rotIsom_smul]
  simp

/-- **The action of `Γ₀` read in the new frame** (Barbot's `μ`-normalisation, l.3113–3118, is
automatic here): `ρ⁻¹τ⁻¹ (unipAction λ t) τρ = unipAction λ₂ (R⁻¹(t + m T t))` as soon as
`diag(λ₂) R⁻¹(t + mTt) = R⁻¹ T t` (`T = diag(λ)`). -/
theorem conj_unipAction {ℓ ℓ₂ : Fin e → ℝ} {m : ℝ}
    {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1)
    {t : EuclideanSpace ℝ (Fin e)}
    (hv : diagLin ℓ₂ (R.symm (t + m • diagLin ℓ t)) = R.symm (diagLin ℓ t))
    {γ : isom (e + 1)} (hγ : ∀ p, γ • p = unipAction ℓ t p) (p : Minkowski (e + 1)) :
    ((rotIsom R hR)⁻¹ * (nullShift m)⁻¹ * γ * nullShift m * rotIsom R hR) • p =
      unipAction ℓ₂ (R.symm (t + m • diagLin ℓ t)) p := by
  obtain ⟨X, rfl⟩ : ∃ X, p = nolToMink X := ⟨minkToNol p, (nolToMink_minkToNol p).symm⟩
  obtain ⟨x, z, y⟩ := X
  simp only [mul_smul, rotIsom_smul, nullShift_smul, hγ, unipAction_nolToMink, nullShift_inv_smul,
    rotIsom_inv_smul]
  congr 1
  simp only [NolParam.act, nolA, LinearIsometryEquiv.coe_refl, id, LinearMap.zero_apply, hv]
  set w := diagLin ℓ t
  have i1 : ⟪R.symm w, z⟫ = ⟪w, R z⟫ := by
    rw [← LinearIsometryEquiv.inner_map_map R, LinearIsometryEquiv.apply_symm_apply]
  have i2 : ⟪R.symm (t + m • w), R.symm w⟫ = ⟪t, w⟫ + m * ‖w‖ ^ 2 := by
    rw [LinearIsometryEquiv.inner_map_map, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [i1, i2, LinearIsometryEquiv.norm_map]
    ring
  · simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
    module
  · simp

end Frames


/-! ## §8 The quotient of a component by a lattice of `A`

Local copies (Classification is downstream, and the sibling `Cla/UnipComplete` is not imported):
freeness and proper discontinuity of a group acting through `A` on a component of `Ω(A)`. -/

section UnipQuot

variable {e : ℕ} {ℓ : Fin e → ℝ} {α β : EReal}

private theorem env_norm_le_sum_abs (t : EuclideanSpace ℝ (Fin e)) : ‖t‖ ≤ ∑ i, |t i| := by
  have h : t = ∑ i, EuclideanSpace.single i (t i) := by
    ext j; simp
  calc ‖t‖ = ‖∑ i, EuclideanSpace.single i (t i)‖ := by rw [← h]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (t i)‖ := norm_sum_le _ _
    _ = ∑ i, |t i| := by simp

private theorem env_nullZ_unipAction_apply (ℓ : Fin e → ℝ) (t : EuclideanSpace ℝ (Fin e))
    (p : Minkowski (e + 1)) (i : Fin e) :
    nullZ (unipAction ℓ t p) i = nullZ p i + t i * (1 + nullY p * ℓ i) := by
  simp [unipAction, nullZ_ofNull]

private theorem env_unipAction_zero (ℓ : Fin e → ℝ) (p : Minkowski (e + 1)) :
    unipAction ℓ 0 p = p := by
  refine eq_of_null ?_ ?_ ?_
  · simp [unipAction, nullX_ofNull]
  · simp [unipAction, nullY_ofNull]
  · intro i; simp [unipAction, nullZ_ofNull]

private theorem env_eq_nullZ_smul_zero {γ : isom (e + 1)} {t : EuclideanSpace ℝ (Fin e)}
    (h : ∀ p, γ • p = unipAction ℓ t p) : t = nullZ (γ • (0 : Minkowski (e + 1))) := by
  ext i
  rw [h, env_nullZ_unipAction_apply]
  simp [nullZ, nullY]

private theorem env_isom_eq_of_unipAction {γ γ' : isom (e + 1)} {t : EuclideanSpace ℝ (Fin e)}
    (h : ∀ p, γ • p = unipAction ℓ t p) (h' : ∀ p, γ' • p = unipAction ℓ t p) : γ = γ' :=
  Causal.eq_of_eqOn (X := Minkowski (e + 1)) isOpen_univ univ_nonempty fun p _ => by
    simp only [h, h']

variable (Γ : Subgroup (isom (e + 1))) (L : AddSubgroup (EuclideanSpace ℝ (Fin e)))

private theorem env_unip_invariant (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p) :
    FlatQuotient.Invariant Γ (unipDomain (d := e) α β) :=
  ⟨fun γ p hp => by
    obtain ⟨t, -, ht⟩ := hΓ γ γ.2
    rw [ht]; exact unipAction_mem_unipDomain ℓ t hp⟩

private theorem env_unip_isCancelSMul (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    [FlatQuotient.Invariant Γ (unipDomain (d := e) α β)] :
    IsCancelSMul Γ (unipDomain (d := e) α β) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  rintro ⟨γ, hγ⟩ p hp
  obtain ⟨t, -, ht⟩ := hΓ γ hγ
  have hpv := congrArg Subtype.val hp
  simp only [FlatQuotient.coe_smul] at hpv
  rw [ht] at hpv
  have ht0 : t = 0 := by
    ext i
    have h1 := congrArg (fun q => nullZ q i) hpv
    simp only [env_nullZ_unipAction_apply] at h1
    have h2 := hℓ.2.1 _ p.2.1 p.2.2 i
    have : t i * (1 + nullY (p : Minkowski (e + 1)) * ℓ i) = 0 := by linarith
    simpa [h2] using this
  subst ht0
  apply Subtype.ext
  exact env_isom_eq_of_unipAction (ℓ := ℓ) ht fun q => by
    rw [env_unipAction_zero]; exact one_smul _ q

private theorem env_unip_finite_of_bound [BallFinite L]
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p) (R : ℝ) :
    {γ : Γ | ‖nullZ ((γ : isom (e + 1)) • (0 : Minkowski (e + 1)))‖ ≤ R}.Finite := by
  set F : Γ → EuclideanSpace ℝ (Fin e) := fun γ => nullZ ((γ : isom (e + 1)) • 0)
  have hF : InjOn F univ := by
    rintro ⟨γ, hγ⟩ - ⟨γ', hγ'⟩ - he
    obtain ⟨t, -, ht⟩ := hΓ γ hγ
    obtain ⟨t', -, ht'⟩ := hΓ γ' hγ'
    have e1 := env_eq_nullZ_smul_zero ht
    have e2 := env_eq_nullZ_smul_zero ht'
    have htt : t = t' := by rw [e1, e2]; exact he
    subst htt
    exact Subtype.ext (env_isom_eq_of_unipAction ht ht')
  refine ((BallFinite.finite_ball (Λ := L) R).preimage (hF.mono (subset_univ _))).subset ?_
  rintro ⟨γ, hγ⟩ hR
  obtain ⟨t, htL, ht⟩ := hΓ γ hγ
  refine ⟨?_, hR⟩
  change nullZ (γ • 0) ∈ L
  rw [← env_eq_nullZ_smul_zero ht]; exact htL

private theorem env_unip_properlyDiscontinuousSMul [BallFinite L] (hℓ : IsUnipComponent ℓ α β)
    (hΓ : ∀ γ ∈ Γ, ∃ t ∈ L, ∀ p, γ • p = unipAction ℓ t p)
    [FlatQuotient.Invariant Γ (unipDomain (d := e) α β)] :
    ProperlyDiscontinuousSMul Γ (unipDomain (d := e) α β) := by
  refine ⟨fun {K K'} hK hK' => ?_⟩
  have hz : ∀ i, Continuous fun q : unipDomain (d := e) α β => |nullZ (q : Minkowski (e + 1)) i| :=
    fun i => (((EuclideanSpace.proj i.succ).continuous.comp continuous_snd).comp
      continuous_subtype_val).abs
  have hs : ∀ i, Continuous fun q : unipDomain (d := e) α β =>
      |1 + nullY (q : Minkowski (e + 1)) * ℓ i| := fun i =>
    (continuous_const.add ((continuous_nullY.comp continuous_subtype_val).mul continuous_const)).abs
  choose R hR using fun i => hK.exists_bound_of_continuousOn (hz i).continuousOn
  choose R' hR' using fun i => hK'.exists_bound_of_continuousOn (hz i).continuousOn
  have hc : ∀ i, ∃ c > 0, ∀ q ∈ K, c ≤ |1 + nullY (q : Minkowski (e + 1)) * ℓ i| := fun i => by
    rcases K.eq_empty_or_nonempty with hKe | hKn
    · exact ⟨1, one_pos, by simp [hKe]⟩
    obtain ⟨q₀, hq₀, hmin⟩ := hK.exists_isMinOn hKn (hs i).continuousOn
    refine ⟨|1 + nullY (q₀ : Minkowski (e + 1)) * ℓ i|,
      abs_pos.2 (hℓ.2.1 _ q₀.2.1 q₀.2.2 i), fun q hq => hmin hq⟩
  choose c hc0 hcK using hc
  refine (env_unip_finite_of_bound Γ L hΓ (∑ i, (R' i + R i) / c i)).subset ?_
  rintro ⟨γ, hγ⟩ ⟨_, ⟨k, hk, rfl⟩, hl⟩
  obtain ⟨t, -, ht⟩ := hΓ γ hγ
  change ‖nullZ (γ • (0 : Minkowski (e + 1)))‖ ≤ _
  rw [← env_eq_nullZ_smul_zero ht]
  refine (env_norm_le_sum_abs t).trans (Finset.sum_le_sum fun i _ => ?_)
  have h1 := hR i k hk
  have h2 := hR' i _ hl
  simp only [Real.norm_eq_abs, abs_abs, FlatQuotient.coe_smul, ht, env_nullZ_unipAction_apply] at h1 h2
  have h3 := hcK i k hk
  rw [le_div_iff₀ (hc0 i)]
  have h4 : |t i| * c i ≤ |t i * (1 + nullY (k : Minkowski (e + 1)) * ℓ i)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have h5 : t i * (1 + nullY (k : Minkowski (e + 1)) * ℓ i) =
      (nullZ (k : Minkowski (e + 1)) i + t i * (1 + nullY (k : Minkowski (e + 1)) * ℓ i)) -
        nullZ (k : Minkowski (e + 1)) i := by ring
  rw [h5] at h4
  linarith [abs_sub (nullZ (k : Minkowski (e + 1)) i + t i * (1 + nullY (k : Minkowski (e + 1)) * ℓ i))
    (nullZ (k : Minkowski (e + 1)) i)]

/-- **A lattice stays ball-finite under a linear map injective on its span.** -/
theorem ballFinite_map_of_injOn {L : AddSubgroup (EuclideanSpace ℝ (Fin e))} [BallFinite L]
    (f : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e))
    (hf : ∀ u ∈ Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin e))), f u = 0 → u = 0) :
    BallFinite (L.map f.toAddMonoidHom) := by
  set E := Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin e)))
  set g : E →ₗ[ℝ] EuclideanSpace ℝ (Fin e) := f.domRestrict E
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact Subtype.ext (hf u u.2 hu)
  set ce := (LinearEquiv.ofInjective g hg).toContinuousLinearEquiv
  set C := ‖(ce.symm : LinearMap.range g →L[ℝ] E)‖
  have hbound : ∀ u ∈ E, ‖u‖ ≤ C * ‖f u‖ := by
    intro u hu
    have h1 : ce.symm (ce ⟨u, hu⟩) = ⟨u, hu⟩ := ce.symm_apply_apply _
    have h2 := (ce.symm : LinearMap.range g →L[ℝ] E).le_opNorm (ce ⟨u, hu⟩)
    rw [ContinuousLinearEquiv.coe_coe, h1] at h2
    have h3 : ‖ce ⟨u, hu⟩‖ = ‖f u‖ := rfl
    rw [h3] at h2
    exact h2
  refine ⟨fun r => ?_⟩
  refine ((BallFinite.finite_ball (Λ := L) (C * r)).image f).subset ?_
  rintro _ ⟨⟨t, ht, rfl⟩, htr⟩
  refine ⟨t, ⟨ht, (hbound t (Submodule.subset_span ht)).trans ?_⟩, rfl⟩
  exact mul_le_mul_of_nonneg_left htr (norm_nonneg (ce.symm : LinearMap.range g →L[ℝ] E))

end UnipQuot


/-! ## §9 Maximality (the repaired l.3668–3676)

Given a (CC′) target `N` with `gΓg⁻¹ ≤ ρ(Deck)` and `gΩ₂ ⊆ 𝒟(Ñ)`, read everything in the frame
`φ = gψ`: `Σ = 𝒟(S̃)` is acausal and `Γ₀`-invariant, and `J = π₁(φ⁻¹Σ)` is an interval
(`Σ` is connected) containing `]a, b[`; every null line `{y, z fixed}` through a point of
`𝒟(Ñ)` meets `Σ` (`range_subset_dependenceDomain_of_developsCC`, l.3123–3125), so
`π₁(φ⁻¹𝒟(Ñ)) ⊆ J`. Prop 9.3's leading coefficient (`leading_nonneg_of_achronal`, unnormalised:
no change of origin and no exclusion of loxodromic elements is needed) makes the interior of `J`
admissible for `T` on `E`, so it is `]a, b[` by maximality; `𝒟(Ñ)` being open, `π₁` of it lies
in `]a, b[`, i.e. `𝒟(Ñ) ⊆ gΩ₂`. -/

section Maximal

open scoped RealInnerProductSpace

variable {e : ℕ}

theorem nullY_add_smul (q v : Minkowski (e + 1)) (s : ℝ) :
    nullY (q + s • v) = nullY q + s * nullY v := by
  simp only [nullY, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

theorem minkQ_ofNull_one_zero : minkQ (ofNull (d := e) 1 0 0) = 0 := by
  have : (ofNull (d := e) 1 0 0) = nolToMink (1, 0, 0) := rfl
  rw [this, minkQ_nolToMink]; simp [nolQ]

/-- **Prop 9.3's leading coefficient on an interval of heights** (l.2974–2979, unnormalised):
for an achronal `St` invariant under `A_{diag λ}` restricted to `L`, and an interval `J` of heights
taken on `St`, the interior of `J` is admissible for `diag λ` on `span L`. -/
theorem unipAdmissible_of_achronal {ℓ : Fin e → ℝ} {L : AddSubgroup (EuclideanSpace ℝ (Fin e))}
    {St : Set (ℝ × EuclideanSpace ℝ (Fin e) × ℝ)} (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X'))
    (hinv : ∀ t ∈ L, ∀ X ∈ St, (nolA (diagLin ℓ) 0 t).act X ∈ St) {J : Set ℝ}
    (hJo : J.OrdConnected) (hJ : ∀ y ∈ J, ∃ X ∈ St, X.2.2 = y) :
    UnipAdmissible (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin e)))) (diagLin ℓ)
      (sInf ((fun y : ℝ => (y : EReal)) '' J)) (sSup ((fun y : ℝ => (y : EReal)) '' J)) := by
  intro y y' hy hyy' hy' u hu
  obtain ⟨_, ⟨j₁, hj₁, rfl⟩, hj₁y⟩ := sInf_lt_iff.1 hy
  obtain ⟨_, ⟨j₂, hj₂, rfl⟩, hyj₂⟩ := lt_sSup_iff.1 hy'
  have hj₁y' : j₁ < y := EReal.coe_lt_coe_iff.1 hj₁y
  have hyj₂' : y' < j₂ := EReal.coe_lt_coe_iff.1 hyj₂
  obtain ⟨X, hX, rfl⟩ := hJ y (hJo.out hj₁ hj₂ ⟨hj₁y'.le, by linarith⟩)
  obtain ⟨X', hX', rfl⟩ := hJ y' (hJo.out hj₁ hj₂ ⟨by linarith, hyj₂'.le⟩)
  have hL : ∀ t ∈ L, 0 ≤ ⟪t + X.2.2 • diagLin ℓ t, t + X'.2.2 • diagLin ℓ t⟫ := fun t ht =>
    leading_nonneg_of_achronal hach (nolA_isA (diagLin ℓ) 0 t) (hinv t ht) hX hX'
  have hTc : Continuous (diagLin ℓ) := LinearMap.continuous_of_finiteDimensional _
  have hhom : ∀ (c : ℝ) (x : EuclideanSpace ℝ (Fin e)),
      ⟪c • x + X.2.2 • diagLin ℓ (c • x), c • x + X'.2.2 • diagLin ℓ (c • x)⟫ =
        c ^ 2 * ⟪x + X.2.2 • diagLin ℓ x, x + X'.2.2 • diagLin ℓ x⟫ := by
    intro c x
    have e1 : c • x + X.2.2 • diagLin ℓ (c • x) = c • (x + X.2.2 • diagLin ℓ x) := by
      rw [map_smul, smul_add, smul_comm]
    have e2 : c • x + X'.2.2 • diagLin ℓ (c • x) = c • (x + X'.2.2 • diagLin ℓ x) := by
      rw [map_smul, smul_add, smul_comm]
    rw [e1, e2, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]; ring
  have hqc : Continuous fun x : EuclideanSpace ℝ (Fin e) =>
      ⟪x + X.2.2 • diagLin ℓ x, x + X'.2.2 • diagLin ℓ x⟫ :=
    (continuous_id.add (continuous_const.smul hTc)).inner
      (continuous_id.add (continuous_const.smul hTc))
  exact nonneg_on_span_of_addSubgroup hqc hhom hL u hu

/-- **Openness**: if the heights `π₁(φ⁻¹p)` of the points `p` of an open set `RD` all lie in `J`,
they lie in the interior `]inf J, sup J[`. -/
theorem mem_unipDomain_of_isOpen {RD : Set (Minkowski (e + 1))} (hopenD : IsOpen RD)
    (φ : isom (e + 1)) {J : Set ℝ} (hJ : ∀ p ∈ RD, nullY (φ⁻¹ • p) ∈ J) {p : Minkowski (e + 1)}
    (hp : p ∈ RD) :
    φ⁻¹ • p ∈ unipDomain (sInf ((fun y : ℝ => (y : EReal)) '' J))
      (sSup ((fun y : ℝ => (y : EReal)) '' J)) := by
  set q := φ⁻¹ • p
  set vn : Minkowski (e + 1) := ofNull 0 1 0
  have hvn : nullY vn = 1 := nullY_ofNull _ _ _
  have hc : Continuous fun s : ℝ => φ • (q + s • vn) :=
    (continuous_const_smul φ).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hopen : IsOpen ((fun s : ℝ => φ • (q + s • vn)) ⁻¹' RD) := hopenD.preimage hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 (by
    show φ • (q + (0 : ℝ) • vn) ∈ RD; rw [zero_smul, add_zero, smul_inv_smul]; exact hp)
  have hside : ∀ s : ℝ, |s| < ε → nullY q + s ∈ J := by
    intro s hs
    have hmem : φ • (q + s • vn) ∈ RD :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hs)
    have := hJ _ hmem
    simpa only [inv_smul_smul, nullY_add_smul, hvn, mul_one] using this
  have hup := hside (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hdn := hside (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have h_up := le_sSup (show ((nullY q + ε / 2 : ℝ) : EReal) ∈ (fun y : ℝ => (y : EReal)) '' J
    from ⟨_, hup, rfl⟩)
  have h_dn := sInf_le (show ((nullY q + -(ε / 2) : ℝ) : EReal) ∈ (fun y : ℝ => (y : EReal)) '' J
    from ⟨_, hdn, rfl⟩)
  refine ⟨h_dn.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)),
    (EReal.coe_lt_coe_iff.2 (by linarith)).trans_le h_up⟩

/-- **The envelope over a maximal admissible interval is maximal** (`EnvelopeMaximal`). -/
theorem envelopeMaximal_of_maximal (ψ : isom (e + 1)) {ℓ : Fin e → ℝ}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin e))} {Γ₀ : Subgroup (isom (e + 1))}
    (h2 : ∀ t ∈ L, ∃ γ ∈ Γ₀, ∀ p, γ • p = unipAction ℓ t p) {a b : EReal} (hab : a < b)
    (hmax : ∀ a' b' : EReal, a' ≤ a → b ≤ b' →
      UnipAdmissible (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin e)))) (diagLin ℓ) a' b' →
        a' = a ∧ b' = b) :
    EnvelopeMaximal.{w} (frameConj ψ Γ₀) (isomImage ψ (unipDomain a b)) := by
  intro N y₀ D ρ hpair hcaus S hS g hg hsub
  have hquo := bcor_quo hpair hS
  have hDD := range_subset_dependenceDomain_of_developsCC hpair hcaus hS
  have hac : (minkowski (e + 1)).IsAcausal (D '' (UniversalCover.proj N y₀ ⁻¹' S)) :=
    hS.cc.entire.acausal
  have hpre := (ccAction_of_developsCC hpair hS).isPreconnected
  have hopenD : IsOpen (range D) := by
    letI := flatCoverChartedSpace (e + 1) N y₀
    exact hpair.gx.isOpenMap.isOpen_range
  have hinvS := hquo.2.1
  clear hquo
  generalize D '' (UniversalCover.proj N y₀ ⁻¹' S) = Sg at hDD hac hpre hinvS
  generalize hRD : range D = RD at hDD hopenD hsub ⊢
  have hRD' : ∀ p ∈ RD, p ∈ dependenceDomain (minkowski (e + 1)) ⊤ Sg := fun p hp => hDD hp
  clear hDD hpair hcaus hS
  generalize hφ : g * ψ = φ
  have hsub' : ∀ x ∈ unipDomain a b, φ • x ∈ RD := fun x hx =>
    hsub ⟨ψ • x, by rw [coe_isomImage]; exact ⟨x, hx, rfl⟩, by rw [← hφ, mul_smul]⟩
  have hg' : ∀ γ₀ ∈ Γ₀, φ * γ₀ * φ⁻¹ ∈ ρ.range := by
    intro γ₀ hγ₀
    have hmem : ψ * γ₀ * ψ⁻¹ ∈ frameConj ψ Γ₀ := by
      rw [mem_frameConj_iff]
      have : ψ⁻¹ * (ψ * γ₀ * ψ⁻¹) * ψ = γ₀ := by group
      rw [this]; exact hγ₀
    have e1 : φ * γ₀ * φ⁻¹ = g * (ψ * γ₀ * ψ⁻¹) * g⁻¹ := by rw [← hφ]; group
    rw [e1]; exact hg _ hmem
  set f : Minkowski (e + 1) → ℝ := fun p => nullY (φ⁻¹ • p) with hf
  set J : Set ℝ := f '' Sg with hJdef
  -- the null direction `v₀` and its image
  set v₀ : Minkowski (e + 1) := ofNull 1 0 0 with hv₀
  set lv : Minkowski (e + 1) := (φ : Minkowski (e + 1) ≃ᵃ[ℝ] Minkowski (e + 1)).linear v₀
  have hlvQ : minkQ lv = 0 := by
    rw [lorentz.minkQ_apply (mem_isom_iff.1 φ.2)]; exact minkQ_ofNull_one_zero
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have := congrArg nullX h
    rw [hv₀, nullX_ofNull] at this
    simp [nullX] at this
  have hlv0 : lv ≠ 0 := fun h => hv₀ne ((φ : Minkowski (e + 1) ≃ᵃ[ℝ] Minkowski (e + 1)).linear
    |>.injective (h.trans (map_zero _).symm))
  have hmove : ∀ (q : Minkowski (e + 1)) (s : ℝ), φ • (q + s • v₀) = φ • q + s • lv := by
    intro q s
    have h := (φ : Minkowski (e + 1) ≃ᵃ[ℝ] Minkowski (e + 1)).map_vadd q (s • v₀)
    rw [vadd_eq_add, vadd_eq_add, map_smul] at h
    rw [isom_smul_def, isom_smul_def, show q + s • v₀ = s • v₀ + q from add_comm _ _, h]
    exact add_comm _ _
  -- (ii) the `y`-coordinate of every point of `𝒟(Ñ)` is taken on `Σ`
  have hJ : ∀ p ∈ RD, f p ∈ J := by
    intro p hp
    obtain ⟨s, hs⟩ := exists_mem_nullLine_of_mem_dependenceDomain (hRD' p hp) hlv0 hlvQ
    refine ⟨_, hs, ?_⟩
    have : φ⁻¹ • (p + s • lv) = φ⁻¹ • p + s • v₀ := by
      rw [inv_smul_eq_iff, hmove, smul_inv_smul]
    simp only [hf, this, nullY_add_smul, hv₀, nullY_ofNull, mul_zero, add_zero]
  -- (i) `]a, b[ ⊆ J`
  have hab' : ∀ y : ℝ, a < y → (y : EReal) < b → y ∈ J := by
    intro y hy hy'
    have hmem : φ • (ofNull 0 y 0 : Minkowski (e + 1)) ∈ RD := by
      refine hsub' _ ?_
      show a < ((nullY (ofNull (d := e) 0 y 0) : ℝ) : EReal) ∧ ((nullY (ofNull (d := e) 0 y 0) : ℝ) : EReal) < b
      rw [nullY_ofNull]; exact ⟨hy, hy'⟩
    have := hJ _ hmem
    simpa only [hf, inv_smul_smul, nullY_ofNull] using this
  -- (iii) `J` is an interval
  have hJc : IsPreconnected J :=
    hpre.image f
      ((continuous_nullY.comp (continuous_const_smul φ⁻¹)).continuousOn)
  have hJo : J.OrdConnected := hJc.ordConnected
  set J' : Set EReal := (fun y : ℝ => (y : EReal)) '' J with hJ'
  -- (iv) the interior of `J` is admissible
  have hacSt : (minkowski (e + 1)).IsAcausal ((fun q => φ • q) ⁻¹' Sg) := by
    intro x hx x' hx' hle
    exact MulAction.injective φ (hac _ hx _ hx' ((isom_le_top_iff φ).2 hle))
  have hadm := unipAdmissible_of_achronal (L := L) (St := {X | φ • nolToMink X ∈ Sg})
    (fun X hX X' hX' => nolQ_nonneg_of_isAcausal hacSt hX hX') (fun t ht X hX => by
      obtain ⟨γ₀, hγ₀, hγt⟩ := h2 t ht
      show φ • nolToMink _ ∈ Sg
      rw [← unipAction_nolToMink ℓ t X, ← hγt]
      have h3 : φ • γ₀ • nolToMink X = (φ * γ₀ * φ⁻¹) • (φ • nolToMink X) := by
        simp only [mul_smul, inv_smul_smul]
      rw [h3, ← hinvS _ (hg' γ₀ hγ₀)]
      exact Set.smul_mem_smul_set hX) hJo (fun y hy => by
      obtain ⟨p, hp, rfl⟩ := hy
      refine ⟨minkToNol (φ⁻¹ • p), ?_, rfl⟩
      show φ • nolToMink _ ∈ Sg; rw [nolToMink_minkToNol, smul_inv_smul]; exact hp)
  -- (v) maximality
  have hlo : sInf J' ≤ a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hy'⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_min hcon hab)
    have hyJ := hab' y hy (hy'.trans_le (min_le_right _ _))
    exact absurd (sInf_le (show (y : EReal) ∈ J' from ⟨y, hyJ, rfl⟩)) (not_le.2 (hy'.trans_le (min_le_left _ _)))
  have hhi : b ≤ sSup J' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hy'⟩ := EReal.lt_iff_exists_real_btwn.1 (max_lt hcon hab)
    have hyJ := hab' y ((le_max_right _ _).trans_lt hy) hy'
    exact absurd (le_sSup (show (y : EReal) ∈ J' from ⟨y, hyJ, rfl⟩)) (not_le.2 ((le_max_left _ _).trans_lt hy))
  obtain ⟨hJa, hJb⟩ := hmax _ _ hlo hhi hadm
  -- (vi) openness of `𝒟(Ñ)`
  intro p hp
  refine ⟨ψ • (φ⁻¹ • p), ?_, by show g • ψ • (φ⁻¹ • p) = p; rw [← mul_smul g ψ, hφ, smul_inv_smul]⟩
  rw [coe_isomImage]
  refine ⟨φ⁻¹ • p, ?_, rfl⟩
  rw [← hJa, ← hJb]
  exact mem_unipDomain_of_isOpen hopenD φ hJ hp

end Maximal


/-! ## §10 Assembling the parabolic case: normalisation, components and slabs in the new frame -/

section Assembly

open scoped RealInnerProductSpace

variable {e : ℕ}

/-- **With `T ≠ 0` on `E`, `]−∞, +∞[` is not admissible** (Prop 9.3's first conclusion). -/
theorem not_bot_top_of_unipAdmissible {E : Submodule ℝ (EuclideanSpace ℝ (Fin e))}
    {T : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)}
    (h : UnipAdmissible E T ⊥ ⊤) (hpar : ∃ u ∈ E, T u ≠ 0) : False := by
  have := limites_of_leading (L := E.toAddSubgroup) (ylo := ⊥) (yhi := ⊤) EReal.bot_lt_zero
    EReal.zero_lt_top (fun u hu y y' hy hy₁ hy' hy₁' => by
      rcases le_total y y' with hyy | hyy
      · exact h y y' hy hyy hy₁' u hu
      · rw [real_inner_comm]; exact h y' y hy' hyy hy₁ u hu) hpar
  exact this.1 ⟨rfl, rfl⟩

/-- **Barbot's normalisation of the interval** (l.3651–3653, "we assume without loss of
generality the equality `y₊ = −y₋`"): a change of origin `m` makes `]a, b[` symmetric, or puts
`0` inside when one end is infinite. -/
theorem exists_normalisation {a b : EReal} (hab : a < b) (hfin : ¬(a = ⊥ ∧ b = ⊤)) :
    ∃ (a₂ b₂ : EReal) (m : ℝ), a₂ < 0 ∧ 0 < b₂ ∧ (a₂ = -b₂ ∨ b₂ = ⊤ ∨ a₂ = ⊥) ∧
      ¬(a₂ = ⊥ ∧ b₂ = ⊤) ∧ a = a₂ + m ∧ b = b₂ + m := by
  induction a using EReal.rec with
  | top => exact absurd hab (not_lt.2 le_top)
  | bot =>
    induction b using EReal.rec with
    | bot => exact absurd hab (lt_irrefl _)
    | top => exact absurd ⟨rfl, rfl⟩ hfin
    | coe r =>
      refine ⟨⊥, ((1 : ℝ) : EReal), r - 1, EReal.bot_lt_zero, by exact_mod_cast one_pos,
        Or.inr (Or.inr rfl), fun h => EReal.coe_ne_top _ h.2, by rw [EReal.bot_add], ?_⟩
      rw [← EReal.coe_add]; congr 1; ring
  | coe s =>
    induction b using EReal.rec with
    | bot => exact absurd hab (not_lt.2 bot_le)
    | top =>
      refine ⟨((-1 : ℝ) : EReal), ⊤, s + 1, by exact_mod_cast (by norm_num : (-1 : ℝ) < 0),
        EReal.zero_lt_top, Or.inr (Or.inl rfl), fun h => EReal.coe_ne_bot _ h.1, ?_,
        by rw [EReal.top_add_coe]⟩
      rw [← EReal.coe_add]; congr 1; ring
    | coe r =>
      have hsr : s < r := EReal.coe_lt_coe_iff.1 hab
      refine ⟨((-((r - s) / 2) : ℝ) : EReal), (((r - s) / 2 : ℝ) : EReal), (s + r) / 2,
        by exact_mod_cast (by linarith : -((r - s) / 2) < 0),
        by exact_mod_cast (by linarith : (0 : ℝ) < (r - s) / 2), Or.inl (EReal.coe_neg _),
        fun h => EReal.coe_ne_bot _ h.1, ?_, ?_⟩
      · rw [← EReal.coe_add]; congr 1; ring
      · rw [← EReal.coe_add]; congr 1; ring

/-- **Admissibility is invariant under the rotation diagonalising `Ŝ`.** -/
theorem unipAdmissible_rot_iff {Ŝ : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e)}
    {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)} {ℓ₂ : Fin e → ℝ}
    (hRd : ∀ t, Ŝ (R t) = R (diagLin ℓ₂ t)) {c d : EReal} :
    UnipAdmissible ⊤ Ŝ c d ↔ UnipAdmissible ⊤ (diagLin ℓ₂) c d := by
  have key : ∀ (y y' : ℝ) (t : EuclideanSpace ℝ (Fin e)),
      ⟪R t + y • Ŝ (R t), R t + y' • Ŝ (R t)⟫ = ⟪t + y • diagLin ℓ₂ t, t + y' • diagLin ℓ₂ t⟫ := by
    intro y y' t
    rw [hRd, show R t + y • R (diagLin ℓ₂ t) = R (t + y • diagLin ℓ₂ t) by rw [map_add, map_smul],
      show R t + y' • R (diagLin ℓ₂ t) = R (t + y' • diagLin ℓ₂ t) by rw [map_add, map_smul],
      LinearIsometryEquiv.inner_map_map]
  constructor
  · intro h y y' hy hyy hy' t _
    rw [← key]; exact h y y' hy hyy hy' _ trivial
  · intro h y y' hy hyy hy' x _
    have := key y y' (R.symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    rw [this]; exact h y y' hy hyy hy' _ trivial

theorem nullY_rotIsom_inv_smul {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1)
    (q : Minkowski (e + 1)) : nullY ((rotIsom R hR)⁻¹ • q) = nullY q := by
  rw [← nolToMink_minkToNol q, rotIsom_inv_smul, nullY_nolToMink, nullY_nolToMink]

theorem nullY_nullShift_inv_smul (m : ℝ) (q : Minkowski (e + 1)) :
    nullY ((nullShift m : isom (e + 1))⁻¹ • q) = nullY q - m := by
  rw [← nolToMink_minkToNol q, nullShift_inv_smul, nullY_nolToMink, nullY_nolToMink]

theorem isomImage_rotIsom_unipDomain {R : EuclideanSpace ℝ (Fin e) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin e)}
    (hR : LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] _) = 1) (c d : EReal) :
    isomImage (rotIsom R hR) (unipDomain c d) = unipDomain c d := by
  apply SetLike.coe_injective
  ext q
  rw [SetLike.mem_coe, mem_isomImage, SetLike.mem_coe]
  show c < ((nullY _ : ℝ) : EReal) ∧ ((nullY _ : ℝ) : EReal) < d ↔
    c < ((nullY q : ℝ) : EReal) ∧ ((nullY q : ℝ) : EReal) < d
  rw [nullY_rotIsom_inv_smul]

theorem isomImage_nullShift_unipDomain (m : ℝ) (c d : EReal) :
    isomImage (nullShift m : isom (e + 1)) (unipDomain c d) = unipDomain (c + m) (d + m) := by
  apply SetLike.coe_injective
  ext q
  rw [SetLike.mem_coe, mem_isomImage, SetLike.mem_coe]
  show c < ((nullY _ : ℝ) : EReal) ∧ ((nullY _ : ℝ) : EReal) < d ↔
    c + m < ((nullY q : ℝ) : EReal) ∧ ((nullY q : ℝ) : EReal) < d + m
  rw [nullY_nullShift_inv_smul, ereal_add_coe_lt_coe_iff, coe_lt_ereal_add_coe_iff]

theorem unipDomain_mono {a b α β : EReal} (ha : a ≤ α) (hb : β ≤ b) :
    unipDomain (d := e) α β ≤ unipDomain a b :=
  fun _ hp => ⟨ha.trans_lt hp.1, hp.2.trans_le hb⟩

end Assembly
/-! ## §11 The envelope -/

section EnvelopeFrame

variable {e : ℕ}

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
  · -- the parabolic case: the maximal admissible interval, the extension, the new frame
    push Not at htr
    obtain ⟨t₀, ht₀, i₀, hi₀⟩ := htr
    haveI : BallFinite L := hL
    set E := Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin e))) with hEdef
    set T := diagLin ℓ with hTdef
    have hpar : ∃ u ∈ E, T u ≠ 0 := ⟨t₀, Submodule.subset_span ht₀, fun h => hi₀ (by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin e) => v i₀) h
      simpa [hTdef, diagLin] using this)⟩
    have he : 0 < e := Fin.pos i₀
    obtain ⟨a, b, haα, hβb, hadm, hmax⟩ :=
      exists_maximal_unipAdmissible (unipAdmissible_of_isUnipComponent hc E)
    have hab : a < b := haα.trans_lt (hc.1.trans_le hβb)
    have hfin : ¬(a = ⊥ ∧ b = ⊤) := by
      rintro ⟨rfl, rfl⟩; exact not_bot_top_of_unipAdmissible hadm hpar
    obtain ⟨a₂, b₂, m, hlo, hhi, hnorm, hfin₂, rfl, rfl⟩ := exists_normalisation hab hfin
    have ham : a₂ + (m : EReal) < (m : EReal) :=
      (ereal_add_coe_lt_coe_iff a₂ m m).2 (by rw [sub_self]; exact_mod_cast hlo)
    have hbm : (m : EReal) < b₂ + (m : EReal) :=
      (coe_lt_ereal_add_coe_iff b₂ m m).2 (by rw [sub_self]; exact_mod_cast hhi)
    obtain ⟨Ŝ, hSE, hSsym, hSadm, hSmax⟩ :=
      exists_shift_extension (isSymmOn_diagLin ℓ) hlo hhi hnorm hfin₂ hadm hmax hpar
    obtain ⟨R, ℓ₂, hRdet, hRd⟩ := exists_rot_diag he hSsym
    -- the component of `Ω(A₂)`
    have hcomp : IsUnipComponent ℓ₂ a₂ b₂ :=
      isUnipComponent_of_maximal (hlo.trans hhi) ((unipAdmissible_rot_iff hRd).1 hSadm)
        fun a' b' h h' hd => hSmax a' b' h h' ((unipAdmissible_rot_iff hRd).2 hd)
    -- the frame, the group, the lattice
    set τ : isom (e + 1) := nullShift m with hτ
    set ρ₂ : isom (e + 1) := rotIsom R hRdet with hρ₂
    set φ₂ : isom (e + 1) := ψ * τ * ρ₂ with hφ₂
    set Γ₂ : Subgroup (isom (e + 1)) := frameConj (φ₂⁻¹ * ψ) Γ₀ with hΓ₂
    set f : EuclideanSpace ℝ (Fin e) →ₗ[ℝ] EuclideanSpace ℝ (Fin e) :=
      R.symm.toLinearEquiv.toLinearMap ∘ₗ (LinearMap.id + m • T) with hf
    have hfapp : ∀ t, f t = R.symm (t + m • T t) := fun t => rfl
    set L₂ : AddSubgroup (EuclideanSpace ℝ (Fin e)) := L.map f.toAddMonoidHom with hL₂
    have hL₂f : BallFinite L₂ := ballFinite_map_of_injOn f fun u hu h0 => by
      rw [hfapp, LinearIsometryEquiv.map_eq_zero_iff] at h0
      exact eq_zero_of_add_smul_eq_zero hadm ham hbm hu h0
    haveI := hL₂f
    have hv : ∀ t ∈ L, diagLin ℓ₂ (R.symm (t + m • diagLin ℓ t)) = R.symm (diagLin ℓ t) := by
      intro t ht
      have h3 := hRd (R.symm (t + m • diagLin ℓ t))
      rw [LinearIsometryEquiv.apply_symm_apply] at h3
      have h5 : R (diagLin ℓ₂ (R.symm (t + m • diagLin ℓ t))) = diagLin ℓ t :=
        h3.symm.trans (hSE t (Submodule.subset_span ht))
      calc diagLin ℓ₂ (R.symm (t + m • diagLin ℓ t))
          = R.symm (R (diagLin ℓ₂ (R.symm (t + m • diagLin ℓ t)))) := (R.symm_apply_apply _).symm
        _ = R.symm (diagLin ℓ t) := by rw [h5]
    have hconj : ∀ γ₀ : isom (e + 1), (φ₂⁻¹ * ψ) * γ₀ * (φ₂⁻¹ * ψ)⁻¹ =
        ρ₂⁻¹ * τ⁻¹ * γ₀ * τ * ρ₂ := fun γ₀ => by rw [hφ₂]; group
    have h1₂ : ∀ γ ∈ Γ₂, ∃ t' ∈ L₂, ∀ p, γ • p = unipAction ℓ₂ t' p := by
      intro γ hγ
      rw [hΓ₂, mem_frameConj_iff] at hγ
      obtain ⟨t, ht, hγt⟩ := h1 _ hγ
      refine ⟨f t, AddSubgroup.mem_map_of_mem _ ht, fun p => ?_⟩
      have e1 : γ = (φ₂⁻¹ * ψ) * ((φ₂⁻¹ * ψ)⁻¹ * γ * (φ₂⁻¹ * ψ)) * (φ₂⁻¹ * ψ)⁻¹ := by group
      rw [e1, hconj, hfapp]
      exact conj_unipAction hRdet (hv t ht) hγt p
    have h2₂ : ∀ t' ∈ L₂, ∃ γ ∈ Γ₂, ∀ p, γ • p = unipAction ℓ₂ t' p := by
      intro t' ht'
      obtain ⟨t, ht, rfl⟩ := AddSubgroup.mem_map.1 ht'
      obtain ⟨γ₀, hγ₀, hγ₀t⟩ := h2 t ht
      refine ⟨ρ₂⁻¹ * τ⁻¹ * γ₀ * τ * ρ₂, ?_, fun p => ?_⟩
      · rw [hΓ₂, mem_frameConj_iff, ← hconj]
        have : (φ₂⁻¹ * ψ)⁻¹ * ((φ₂⁻¹ * ψ) * γ₀ * (φ₂⁻¹ * ψ)⁻¹) * (φ₂⁻¹ * ψ) = γ₀ := by group
        rw [this]; exact hγ₀
      · exact (conj_unipAction hRdet (hv t ht) hγ₀t p).trans (by rw [← hfapp]; rfl)
    -- the quotient
    haveI : FlatQuotient.Invariant Γ₂ (unipDomain (d := e) a₂ b₂) := env_unip_invariant Γ₂ L₂ h1₂
    haveI : IsCancelSMul Γ₂ (unipDomain (d := e) a₂ b₂) := env_unip_isCancelSMul Γ₂ L₂ hcomp h1₂
    haveI : ProperlyDiscontinuousSMul Γ₂ (unipDomain (d := e) a₂ b₂) :=
      env_unip_properlyDiscontinuousSMul Γ₂ L₂ hcomp h1₂
    have hconn : IsConnected (isomImage φ₂ (unipDomain (d := e) a₂ b₂) : Set (Minkowski (e + 1))) := by
      rw [coe_isomImage]
      exact (isConnected_unipDomain hcomp.1).image _ (continuous_const_smul φ₂).continuousOn
    have hq₂ := FlatQuotient.isQuotientOf_toFlatSpacetime (frameConj φ₂ Γ₂)
      (isomImage φ₂ (unipDomain (d := e) a₂ b₂)) hconn
    have hΓeq : frameConj φ₂ Γ₂ = frameConj ψ Γ₀ := by
      rw [hΓ₂, ← frameConj_mul', mul_inv_cancel_left]
    have hΩeq : isomImage φ₂ (unipDomain (d := e) a₂ b₂) = isomImage ψ (unipDomain (a₂ + m) (b₂ + m)) := by
      rw [hφ₂, isomImage_mul, isomImage_mul, hρ₂, isomImage_rotIsom_unipDomain, hτ,
        isomImage_nullShift_unipDomain]
    refine ⟨isomImage ψ (unipDomain (a₂ + m) (b₂ + m)), isomImage_mono (unipDomain_mono haα hβb),
      convex_isomImage convex_unipDomain, ⟨_, ?_, φ₂, ℓ₂, a₂, b₂, L₂, Γ₂, hL₂f, hcomp, h1₂, h2₂, hq₂⟩,
      envelopeMaximal_of_maximal ψ h2 hab hmax⟩
    rw [← hΓeq, ← hΩeq]; exact hq₂

end EnvelopeFrame

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

end Causal.Flat.Cla
