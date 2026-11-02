import Causal.Flat.Classification

/-!
# `Causal.Flat.Lox.PastProper` — Barbot Cor 10.3 on the past side, and both sides together

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10;
line numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. This file
supplies the **past case** of `bcor:loxo_proper` (Cor 10.3, `GHFspace.tex:3214`), which
`Causal.Flat.Loxodromic`'s `bcor_loxo_proper` states for the future case only (DEC-89), and the
statement as printed, both time orientations at once. The label is marked here and in
`Causal.Flat.Loxodromic`'s module docstring, where its checklist row lives; this module cannot
be imported there (it needs `Causal.Flat.Classification`'s time reversal and `Cla.RegularComplete`, both
downstream of `Loxodromic`).

* **`bcor:loxo_proper`** — `GHFspace.tex:3214` (Cor 10.3), marked (DEC-89, as in
  `Causal.Flat.Loxodromic`): `bcor_loxo_proper_past` (the past case:
  `Ω(S̃) = Ω⁻(Λ(Γ))`, Lemma 10.2's second alternative), `bcor_loxo_proper_both` (the printed
  statement, no case split: free, properly discontinuous, and `M(S) = Γ\Ω(S̃)` a flat spacetime,
  globally hyperbolic, Cauchy-complete, with an acausal Cauchy surface); **no `sorry`**.

> The action of $\Gamma$ on $\Omega(\widetilde{S})$ is free and properly discontinuous, and the
> quotient space $M(S) = \Gamma \backslash \Omega(\widetilde{S})$ is a Cauchy-complete globally
> hyperbolic spacetime. (l.3215–3218)

> According to propositions \ref{loxregular} and \ref{agissons}, the action of $\Gamma$ on
> $\Omega(\widetilde{S})$ is properly discontinuous. By definition of $\Omega(\widetilde{S})$,
> this action is free. The corollary thus follows from proposition \ref{agissons}. (l.3222–3227)

## How the past case is proved

Freeness and proper discontinuity are `Loxodromic`'s `loxo_free` and `loxo_properlyDiscontinuous`,
which already cover both orientations. On `Ω⁻ = Ω⁻(Λ(Γ))`, write `Λ' = negS⁻¹ Λ(Γ)`, so that
`σ(p) = −p` maps `Ω⁻` onto the future regular domain `Ω⁺(Λ')` (`mem_omegaMinus_iff_neg`,
`cosmoRegular_negS`), and `σγσ = negConj γ` preserves `Ω⁺(Λ')` (`preimage_negConj_omegaPlus`).

* **Acausality** of `Γ` on `Ω⁻` (`actsAcausally_limitOpensMinus`): `x ≤ γx` gives
  `σγσ(−x) ≤ −x` in `Ω⁺(Λ')`, against the strict monotonicity and the invariance of the
  cosmological time `T'` of `Ω⁺(Λ')`.
* **GH** (`gh_of_isQuotientOf_limitOpensMinus_of_lox`): `Classification`'s
  `gh_of_isQuotientOf_limitOpensMinus` with its loxodromic element given directly instead of
  derived from Benoist's theorem (the time reversal `τ(t, x) = (−t, x)`, `revConj`).
* **The Cauchy surface**: `−S₁(Λ')`, the reflected level set of `T'`, is a `Γ`-invariant acausal
  Cauchy surface of `Ω⁻` (`Cla.rC_isCauchySurfaceOn_neg`, `isAcausal_cosmoLevel`), so its image is
  an acausal Cauchy surface of the quotient (`FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn`,
  `FlatQuotient.isAcausal_image`).
* **Cauchy-completeness**: `Cla.isCauchyComplete_of_isQuotientOf_regular`, which is stated for
  both time orientations.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §8's standing hypotheses on `Γ`, `S̃` | ✓ carried, as `CCAction Γ S` (DEC-83's reading, as for the future case) |
| `Γ` contains a loxodromic element (§10) | ✓ carried |
| Lemma 10.2's two alternatives (future / past regular) | ✓ both: `bcor_loxo_proper` (future), `bcor_loxo_proper_past` (past), `bcor_loxo_proper_both` (the printed statement) |
| "Cauchy-complete" | ✓ in DEC-35's reading (`IsCauchyComplete`, the induced length) |
| "globally hyperbolic" | ✓ both ETT's `GH` and Barbot's (an acausal Cauchy surface, l.498–507) |

## SCOPE (disclosed)

* The quotient is constructed (`FlatQuotient.toFlatSpacetime`) and is an `IsQuotientOf` of
  `Γ` on `Ω(S̃)`; Cauchy-completeness is in the induced-length reading of DEC-35.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-89 (the past case before the mark).
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter

universe u

variable {d : ℕ}

namespace Lox

section PastProper

variable {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- `σγσ` preserves `Ω⁺(−Λ(Γ))` for `γ ∈ Γ` (`σ(p) = −p`). -/
theorem preimage_negConj_omegaPlus {γ : isom d} (hγ : γ ∈ Γ) :
    (fun p => negConj γ • p) ⁻¹' omegaPlus (negS d ⁻¹' limitSetJ Γ) =
      omegaPlus (negS d ⁻¹' limitSetJ Γ) := by
  ext q
  rw [mem_preimage, negConj_smul, ← neg_neg q, ← mem_omegaMinus_iff_neg, neg_neg,
    ← mem_omegaMinus_iff_neg]
  constructor
  · intro hx
    have := smul_mem_omegaMinus_limitSetJ (Γ.inv_mem hγ) hx
    rwa [inv_smul_smul] at this
  · exact fun hx => smul_mem_omegaMinus_limitSetJ hγ hx

/-- `Γ` preserves `Ω⁻(Λ(Γ))`, as the class `FlatQuotient.Invariant`. -/
theorem invariant_limitOpensMinus : FlatQuotient.Invariant Γ (limitOpensMinus Γ) :=
  ⟨fun γ _ hp => smul_mem_omegaMinus_limitSetJ γ.2 hp⟩

/-- **A free action on `Ω⁻(Λ(Γ))` is acausal**, by the point reflection: `x ≤ γx` gives
`σγσ(−x) ≤ −x` in `Ω⁺(−Λ(Γ))`, against the invariance and the strict monotonicity of its
cosmological time. -/
theorem actsAcausally_limitOpensMinus (hP : PastRegular (limitSetJ Γ))
    (htwo : ∃ w₁ ∈ limitSetJ Γ, ∃ w₂ ∈ limitSetJ Γ, w₁.1 ≠ w₂.1)
    [FlatQuotient.Invariant Γ (limitOpensMinus Γ)] [IsCancelSMul Γ (limitOpensMinus Γ)] :
    FlatQuotient.ActsAcausally Γ (limitOpensMinus Γ) := by
  intro γ hne x hle
  have hle' := (minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle)
  by_cases hx : (x : Minkowski d) = ((γ • x : limitOpensMinus Γ) : Minkowski d)
  · apply hne
    have : γ • x = (1 : Γ) • x := by rw [one_smul]; exact (Subtype.ext hx).symm
    exact IsCancelSMul.right_cancel γ 1 x this
  · have hc' := cosmoRegular_negS hP htwo
    have hpre := preimage_negConj_omegaPlus (Γ := Γ) γ.2
    rw [FlatQuotient.coe_smul] at hle' hx
    have hy : -(x : Minkowski d) ∈ omegaPlus (negS d ⁻¹' limitSetJ Γ) :=
      mem_omegaMinus_iff_neg.1 x.2
    have he : -((γ : isom d) • (x : Minkowski d)) = negConj (γ : isom d) • -(x : Minkowski d) := by
      rw [negConj_smul, neg_neg]
    have hle2 := Cla.rC_le_top_neg hle'
    rw [he] at hle2
    have hy' : negConj (γ : isom d) • -(x : Minkowski d) ∈ omegaPlus (negS d ⁻¹' limitSetJ Γ) := by
      rw [← mem_preimage (f := fun p => negConj (γ : isom d) • p), hpre]; exact hy
    have hne' : negConj (γ : isom d) • -(x : Minkowski d) ≠ -(x : Minkowski d) := by
      rw [← he, Ne, neg_inj]; exact fun e => hx e.symm
    have h1 := cosmoTime_lt_of_le hc' hy' hle2 hne'
    rw [cosmoTime_smul hpre] at h1
    exact lt_irrefl _ h1

/-- **GH of `Γ\Ω⁻(Λ(Γ))`, in the `IsQuotientOf` form, from a loxodromic element**: the proof of
`Classification`'s `gh_of_isQuotientOf_limitOpensMinus`, whose only use of Benoist's theorem is
to produce the loxodromic element given here. -/
theorem gh_of_isQuotientOf_limitOpensMinus_of_lox {M₁ : FlatSpacetime.{u} d}
    (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ))
    (hq : IsQuotientOf M₁ Γ (limitOpensMinus Γ)) : GH M₁ := by
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨π, hcov, -, hπs, hfib⟩ := hq.quot
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M₁)
  obtain ⟨p₀, -⟩ := hπs m₀
  haveI := hq.invariant
  haveI := isCancelSMul_of_isCoveringMap hcov hfib
  haveI := properlyDiscontinuousSMul_of_isCoveringMap hcov hfib
  have hmem : ∀ γ ∈ Γ, ∀ x, γ • x ∈ ((limitOpensMinus Γ) : Set (Minkowski d)) ↔
      x ∈ ((limitOpensMinus Γ) : Set (Minkowski d)) :=
    fun γ hγ x => by
      constructor
      · intro hx
        have := (hq.inv γ⁻¹ (Γ.inv_mem hγ)).subset ⟨_, hx, rfl⟩
        simpa using this
      · intro hx; exact (hq.inv γ hγ).subset ⟨x, hx, rfl⟩
  -- the time-reversed data `Λ' = −Λ`, `Γ' = τΓτ`, `Ω⁺(Λ') = τ Ω⁻(Λ)`
  set Λ' : Set (PenroseSphere d × ℝ) := (fun w => (penroseNeg w.1, -w.2)) '' limitSetJ Γ
  have hΛ' : ∀ p, p ∈ omegaPlus Λ' ↔ timeRev d p ∈ omegaMinus (limitSetJ Γ) := fun p => by
    rw [mem_omegaPlus, mem_omegaMinus]
    constructor
    · intro h w hw
      have := h _ ⟨w, hw, rfl⟩
      simp only [minkB_nullVec, penroseNeg, inner_neg_left, timeRev_apply] at this ⊢
      linarith
    · rintro h _ ⟨w, hw, rfl⟩
      have := h w hw
      simp only [minkB_nullVec, penroseNeg, inner_neg_left, timeRev_apply] at this ⊢
      linarith
  have hF' : FutureRegular Λ' := by
    refine ⟨⟨timeRev d p₀, (hΛ' _).2 (by rw [timeRev_timeRev]; exact p₀.2)⟩, ?_⟩
    rw [show omegaPlus Λ' = timeRev d ⁻¹' omegaMinus (limitSetJ Γ) from Set.ext hΛ']
    exact (isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)).preimage continuous_timeRev
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  have hc' : CosmoRegular Λ' := ⟨hF', _, ⟨w₁, subset_closure hw₁, rfl⟩, _,
    ⟨w₂, subset_closure hw₂, rfl⟩, fun h => hne (Subtype.ext (neg_injective
      (congrArg Subtype.val h)))⟩
  set Γ' := Γ.map (revConj d) with hΓ'
  have hP' : PreservesOmega Λ' Γ' := by
    rintro _ ⟨γ, hγ, rfl⟩
    ext p
    simp only [mem_preimage]
    rw [hΛ', hΛ', revConj_smul, timeRev_timeRev]
    exact hmem γ hγ _
  haveI : FlatQuotient.Invariant Γ' hc'.regular.opens := hP'.invariant (h := hc')
  -- `τ : Ω⁺(Λ') ≃ₜ Ω⁻(Λ)`, and the presentation it induces
  let τh : Minkowski d ≃ₜ Minkowski d :=
    { toFun := timeRev d, invFun := timeRev d, left_inv := timeRev_timeRev,
      right_inv := timeRev_timeRev, continuous_toFun := continuous_timeRev,
      continuous_invFun := continuous_timeRev }
  let ρ : hc'.regular.opens ≃ₜ (limitOpensMinus Γ) := τh.subtype fun p => hΛ' p
  have hρ : ∀ z, (ρ z : Minkowski d) = timeRev d z := fun _ => rfl
  have hcov' : IsCoveringMap (π ∘ ρ) := hcov.comp_homeomorph ρ
  have hfib' : ∀ a b : hc'.regular.opens, (π ∘ ρ) a = (π ∘ ρ) b ↔
      ∃ γ' ∈ Γ', γ' • (a : Minkowski d) = b := by
    intro a b
    rw [comp_apply, comp_apply, hfib]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨revConj d γ, ⟨γ, hγ, rfl⟩, ?_⟩
      rw [revConj_smul, ← hρ a, h, hρ, timeRev_timeRev]
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, h⟩
      refine ⟨γ, hγ, ?_⟩
      rw [hρ, hρ, ← h, revConj_smul, timeRev_timeRev]
  haveI := isCancelSMul_of_isCoveringMap hcov' hfib'
  haveI := properlyDiscontinuousSMul_of_isCoveringMap hcov' hfib'
  -- `Ω⁺(Λ')` is future complete, so `≤` of `𝐌ⁿ` between its points is its own
  have hlift : ∀ a b : hc'.regular.opens, (minkowski d).le ⊤ (a : Minkowski d) b →
      (flatCausality d hc'.regular.opens).le ⊤ a b := fun a b h =>
    (flat_le_top_subtype_iff _ _ _).2 (le_of_le_top_of_segment_subset h fun y hy =>
      Jplus_omegaPlus_subset Λ' ⟨a, a.2, (le_top_of_mem_segment h hy).1⟩)
  have hinvConj : ∀ γ : isom d, (revConj d γ)⁻¹ = revConj d γ⁻¹ := fun γ => (map_inv _ γ).symm
  -- acausality of `Γ` on `Ω⁻`, from that of `Γ'` on `Ω⁺(Λ')`
  have hac : FlatQuotient.ActsAcausally Γ (limitOpensMinus Γ) := by
    rintro ⟨γ, hγ⟩ hne x hle
    have h1 := le_top_timeRev ((minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hle))
    set γ' : Γ' := ⟨revConj d γ, γ, hγ, rfl⟩
    have hne' : γ'⁻¹ ≠ 1 := by
      rw [ne_eq, inv_eq_one]
      intro h
      apply hne
      apply Subtype.ext
      apply revConj_injective
      have h' : revConj d γ = 1 := congrArg Subtype.val h
      simpa using h'
    set y : hc'.regular.opens := ρ.symm ((⟨γ, hγ⟩ : Γ) • x)
    have hy : ((γ'⁻¹ • y : hc'.regular.opens) : Minkowski d) = timeRev d x := by
      rw [FlatQuotient.coe_smul]
      change (revConj d γ)⁻¹ • timeRev d (γ • (x : Minkowski d)) = _
      rw [hinvConj, revConj_smul, timeRev_timeRev, inv_smul_smul]
    refine actsAcausally_of_preservesOmega (h := hc') hP' γ'⁻¹ hne' y (hlift _ _ ?_)
    rw [hy]
    exact h1
  -- finiteness of `{γ | x ≤ γ y}` on `Ω⁻`
  have hfin : ∀ x y : (limitOpensMinus Γ),
      {γ : Γ | (flatCausality d (limitOpensMinus Γ)).le ⊤ x (γ • y)}.Finite := by
    intro x y
    have hF := finite_le_of_preservesOmega (h := hc') hP' (ρ.symm y) (ρ.symm x)
    refine (hF.preimage (f := fun γ : Γ => (⟨revConj d γ, γ, γ.2, rfl⟩ : Γ')⁻¹)
      fun a _ b _ h => ?_).subset fun γ hγ => ?_
    · have := congrArg Subtype.val (inv_injective h)
      exact Subtype.ext (revConj_injective this)
    · have h1 := le_top_timeRev ((minkowski d).le_mono le_top
        ((flat_le_top_subtype_iff _ _ _).1 hγ))
      refine hlift _ _ ?_
      have h2 := (isom_le_iff (revConj d γ)⁻¹ ⊤ _ _).2 h1
      rw [isomImage_top] at h2
      convert h2 using 1
      · change timeRev d (y : Minkowski d) = _
        rw [FlatQuotient.coe_smul, hinvConj, revConj_smul, timeRev_timeRev, inv_smul_smul]
      · rw [FlatQuotient.coe_smul]; rfl
  have hPR : PastRegular (limitSetJ Γ) :=
    ⟨⟨p₀, p₀.2⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩
  have hconn : IsConnected ((limitOpensMinus Γ) : Set (Minkowski d)) :=
    (convex_omegaMinus _).isConnected ⟨p₀, p₀.2⟩
  exact gh_of_isQuotientOf hq (FlatQuotient.gh_toFlatSpacetime Γ (limitOpensMinus Γ) hconn hac
    (globallyHyperbolic_subtype _ hPR.globallyHyperbolicOn) hfin)

/-- **`bcor:loxo_proper` (Cor 10.3), the past case** (l.3213–3228; DEC-89): `Γ` acts freely and
properly discontinuously on `Ω(S̃)` and, when `Ω(S̃) = Ω⁻(Λ(Γ))` (Lemma 10.2's second
alternative, the time reversal of the future case), the quotient `M(S) = Γ\Ω(S̃)` is a flat
spacetime, globally hyperbolic in ETT's sense, Cauchy-complete, with an acausal Cauchy surface:
the image of the reflected level set `−S₁(−Λ(Γ))`. -/
theorem bcor_loxo_proper_past (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ActsFreelyProperlyOn Γ (omegaS Γ S) ∧
      (omegaS Γ S = omegaMinus (limitSetJ Γ) →
        ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ (omegaSOpens Γ S) ∧ GH M ∧
          IsCauchyComplete d M ∧
          ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
            (flatCausality d M).IsAcausal Sc) := by
  refine ⟨⟨loxo_free h, loxo_properlyDiscontinuous h hlox⟩, fun heq => ?_⟩
  obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
  obtain ⟨x₀, hx₀⟩ := h.nonempty
  have hx₀' : x₀ ∈ omegaMinus (limitSetJ Γ) := heq ▸ subset_omegaS h hx₀
  have hP : PastRegular (limitSetJ Γ) :=
    ⟨⟨x₀, hx₀'⟩, isOpen_omegaMinus_of_isClosed (isClosed_limitSetJ Γ)⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, hne⟩ := exists_two_loxRepSet hγ₀ hlox₀
  have htwo : ∃ w₁ ∈ limitSetJ Γ, ∃ w₂ ∈ limitSetJ Γ, w₁.1 ≠ w₂.1 :=
    ⟨w₁, subset_closure hw₁, w₂, subset_closure hw₂, hne⟩
  set Ω := limitOpensMinus Γ with hΩdef
  have hΩ : ((Ω : Opens (Minkowski d)) : Set (Minkowski d)) = omegaS Γ S := heq.symm
  haveI : FlatQuotient.Invariant Γ Ω := invariant_limitOpensMinus
  haveI : IsCancelSMul Γ Ω :=
    isCancelSMul_of_free fun γ hγ h1 x hx => loxo_free h γ hγ h1 x (hΩ ▸ hx)
  haveI : ProperlyDiscontinuousSMul Γ Ω :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc =>
      loxo_properlyDiscontinuous h ⟨γ₀, hγ₀, hlox₀⟩ K (hΩ ▸ hK) hKc
  have hconn : IsConnected (Ω : Set (Minkowski d)) := (convex_omegaMinus _).isConnected ⟨x₀, hx₀'⟩
  have hopens : omegaSOpens Γ S = Ω := Opens.ext hΩ.symm
  have hq : IsQuotientOf (FlatQuotient.toFlatSpacetime Γ Ω hconn) Γ Ω :=
    FlatQuotient.isQuotientOf_toFlatSpacetime _ _ _
  -- the Cauchy surface `−S₁(Λ')`, `Λ' = negS⁻¹ Λ(Γ)`
  set Λ' := negS d ⁻¹' limitSetJ Γ with hΛ'
  have hc' : CosmoRegular Λ' := cosmoRegular_negS hP htwo
  set Sn : Set (Minkowski d) := (fun p => -p) '' cosmoLevel Λ' 1 with hSn
  have hmemS : ∀ q, q ∈ Sn ↔ -q ∈ cosmoLevel Λ' 1 := fun q => by
    constructor
    · rintro ⟨p, hp, rfl⟩; rwa [neg_neg]
    · intro hq; exact ⟨-q, hq, neg_neg q⟩
  have hSΩ : Sn ⊆ Ω := fun q hq =>
    mem_omegaMinus_iff_neg.2 (cosmoLevel_subset 1 ((hmemS q).1 hq))
  have hneg : Cla.rC_negOpens hc'.regular.opens = Ω := SetLike.ext fun p => by
    rw [Cla.rC_mem_negOpens]
    exact mem_omegaMinus_iff_neg.symm
  have hC : (minkowski d).IsCauchySurfaceOn Ω Sn := by
    rw [← hneg]
    exact Cla.rC_isCauchySurfaceOn_neg (cosmoLevel_subset 1) (isCauchySurfaceOn_cosmoLevel hc' one_pos)
  have hinv : ∀ γ ∈ Γ, ∀ p ∈ Sn, γ • p ∈ Sn := fun γ hγ p hp => by
    rw [hmemS] at hp ⊢
    have : -(γ • p) = negConj γ • -p := by rw [negConj_smul, neg_neg]
    rw [this]
    exact (smul_mem_cosmoLevel_iff (preimage_negConj_omegaPlus hγ)).2 hp
  have hac := actsAcausally_limitOpensMinus hP htwo (Γ := Γ)
  refine ⟨FlatQuotient.toFlatSpacetime Γ Ω hconn, by rw [hopens]; exact hq,
    gh_of_isQuotientOf_limitOpensMinus_of_lox ⟨γ₀, hγ₀, hlox₀⟩ hq, ?_, _,
    FlatQuotient.isCauchySurface_image_of_isCauchySurfaceOn Γ Ω hac hSΩ hinv hC, ?_⟩
  · refine Cla.isCauchyComplete_of_isQuotientOf_regular (Λ := limitSetJ Γ) (Γ := Γ) (Ω := Ω)
      (Or.inr ⟨hP, htwo, fun _ => Iff.rfl⟩) 1 ?_
    rw [frameConj_one, isomImage_one]; exact hq
  · refine FlatQuotient.isAcausal_image _ _ (fun γ p hp => hinv γ γ.2 p hp) ?_
    intro a ha b hb hab
    have hle := (minkowski d).le_mono le_top ((flat_le_top_subtype_iff _ _ _).1 hab)
    have h1 := Cla.rC_le_top_neg hle
    have := isAcausal_cosmoLevel hc' 1 _ ((hmemS _).1 hb) _ ((hmemS _).1 ha) h1
    exact Subtype.ext (neg_injective this).symm

/-- **`bcor:loxo_proper` (Cor 10.3) as printed** (l.3215–3218), both time orientations: `Γ` acts
freely and properly discontinuously on `Ω(S̃)`, and `M(S) = Γ\Ω(S̃)` is a flat spacetime,
globally hyperbolic (ETT's sense, and Barbot's: an acausal Cauchy surface) and Cauchy-complete.
Lemma 10.2 (`blem_loxregular`) puts `Ω(S̃)` on the future side (`Loxodromic`'s
`bcor_loxo_proper`, with `Cla.isCauchyComplete_of_isQuotientOf_regular`) or the past side
(`bcor_loxo_proper_past`). -/
theorem bcor_loxo_proper_both (h : CCAction Γ S) (hlox : ∃ γ ∈ Γ, IsLoxodromic (linOf γ)) :
    ActsFreelyProperlyOn Γ (omegaS Γ S) ∧
      ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ (omegaSOpens Γ S) ∧ GH M ∧
        IsCauchyComplete d M ∧
        ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
          (flatCausality d M).IsAcausal Sc := by
  refine ⟨⟨loxo_free h, loxo_properlyDiscontinuous h hlox⟩, ?_⟩
  rcases blem_loxregular h hlox with ⟨hF, he⟩ | ⟨-, he⟩
  · obtain ⟨M, hq, hgh, Sc, hSc, hac⟩ := (bcor_loxo_proper h hlox).2 he
    obtain ⟨γ₀, hγ₀, hlox₀⟩ := hlox
    have hc := cosmoRegular_limitSetJ hγ₀ hlox₀ hF
    refine ⟨M, hq, hgh, ?_, Sc, hSc, hac⟩
    refine Cla.isCauchyComplete_of_isQuotientOf_regular (Λ := limitSetJ Γ) (Γ := Γ) (Ω := omegaSOpens Γ S)
      (Or.inl ⟨hc, fun p => ?_⟩) 1 ?_
    · change p ∈ omegaS Γ S ↔ _
      rw [he]
    · rw [frameConj_one, isomImage_one]; exact hq
  · exact (bcor_loxo_proper_past h hlox).2 he

end PastProper

end Lox

end Causal.Flat
