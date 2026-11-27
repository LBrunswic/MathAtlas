import GXScaffold.BBS.HSAntipodal
import GXScaffold.BBS.HSPositive
import GXScaffold.BBS.HSDegree

/-!
# BBS `bbsprop:classising`, the link half: every `(Γ_p, ℓ(p))`-circle has exactly one type of l.855–922, isomorphic circles have the same type, and the singular-line types are these up to the pairing of the two apices

Target `T-bbs-classising-types` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`. Imports `GXScaffold.BBS.HSAntipodal` (the
apex `−p̄`), `GXScaffold.BBS.HSPositive` (the cone angle) and `GXScaffold.BBS.HSDegree`
(examples of every degree), all sorry-free scaffold modules over `GXScaffold.BBS.HSSingularities`.

* `bbsprop:classising` — `colI_v1.tex:531` — partial (unmarked: the causal clauses of the
  proposition are not stated here, and the list of l.855–922 is not exhaustive as printed; the
  link half is proved in the readings below): the assembly
  `GX.GammaLinkCircle.bbsprop_classising_types`; exactly one type
  `GX.GammaLinkCircle.existsUnique_hasType`; isomorphism invariance
  `GX.GammaLinkCircle.IsIso.hasType`, `GX.GammaLinkCircle.not_isIso_of_hasType`; the type at
  `−p̄` `GX.GammaLinkCircle.HasType.antipode`; the line types `GX.LinkType.toLine`,
  `GX.LinkType.toLine_antipode`; the counterexample to exhaustiveness
  `GX.exists_hasType_trivialHolonomy_four`.

> The various types of singular lines in $\AdS$ spacetimes are: time-like lines; light-like lines
> of degree $2$; space-like lines of degree $2$; future BTZ-like singular lines [...] space-like,
> but has no future; past BTZ-like singular lines [...] no past; (past or future) extreme BTZ-like
> singular lines: they look like past/future BTZ-like singular lines, except that they are
> light-like; Misner lines [...]; light-like or space-like lines of degree $k \geq 4$ [...]
> (l.533–545, abridged)

> There are several types of singularity, mutually non isomorphic (l.785). The classification of
> singular lines, i.e. of $(\Gamma_p, \ell(p))$-circles, follows from the classification of
> singularities of singular HS-surfaces [...] Indeed, according to Remark~\ref{rk:p-p}, what could
> have been called a cuspidal singular line, is actually included an extreme BTZ-like singular
> line. (l.999–1012)

## Main declarations (all proved, 0 `sorry`)

* **The types.** `GX.LinkType`: time-like (future/past, with the cone angle, l.862–864), BTZ-like
  past (`I = i⁺`), BTZ-like future (`I = i⁻`), Misner (a space-like arc), cuspidal and extreme
  BTZ-like (future at `∂ℍ²₊`, past at `∂ℍ²₋`), space-like of degree `k` (positive/negative),
  light-like of degree `k` (future/past, positive/negative), and `trivialHolonomy k`, **outside the
  printed list**. `GX.PairType` reads the type on one oriented lifted developing pair (the
  definitions of l.866–922 as printed, with `i^± ∖ T` for the extreme BTZ-like images, OQ-116 (b),
  and the l.915 form of the sign); `GX.GammaLinkCircle.HasType`: some pair reads it.
* **Every circle has exactly one type.** `…IsLiftedDev.exists_pairType` (from
  `GX.IsLiftedDevPair.exhaust` and the § 3.3 theorems of HSSingularities); the type does not depend
  on the pair (`GX.GammaLinkCircle.HasType.pairType`: through `…IsLiftedDev.relate`, the degree-`0`
  images being read on `i^±(L)`, `…deSitter_degree_zero_iff`, `…bdPlus_degree_zero_iff`,
  `…bdMinus_degree_zero_iff`); one pair reads one type (`…IsLiftedDev.pairType_unique`);
  `GX.GammaLinkCircle.existsUnique_hasType`, `GX.GammaLinkCircle.linkType`.
* **Isomorphisms.** `GX.GammaLinkCircle.IsIso.hasType`, `…IsIso.linkType_eq`,
  `GX.GammaLinkCircle.not_isIso_of_hasType` (« mutually non isomorphic »).
* **The two apices.** `GX.LinkType.antipode` (an involution), `GX.GammaLinkCircle.HasType.antipode`
  (the real angle of `mirror f⁻¹` is that of `f`: `GX.GTilde.angle_mirror_inv`),
  `GX.GammaLinkCircle.linkType_antipode`.
* **The lines.** `GX.LineType` (the printed list, plus `trivialHolonomy`), `GX.LinkType.toLine`,
  constant on `{t, t.antipode}` (`GX.LinkType.toLine_antipode`), cuspidal ↦ extreme BTZ-like
  (`GX.LinkType.toLine_cuspidal`); degrees even and `≥ 2` (`…HasType.degree_even`); `i^±(L)` of the
  degree-`0` types (`…HasType.iPlusL_iMinusL`); bridges to `IsSpacelikePositive` and the like.
* **Occurrence.** `GX.exists_hasType_listed` (Misner; space-like and light-like of every degree
  `2k`, both signs); `GX.exists_hasType_trivialHolonomy_four`; `GX.hasType_regular`.

## Hypothesis checklist

| BBS | here |
|---|---|
| « singular lines », « types » (l.533) | ⚠ reading: the line types are the types of the `(Γ_p, ℓ(p))`-circle at one apex (l.983–986), modulo the pairing of the two apices (`LinkType.toLine`); singular lines of AdS spacetimes themselves are not formalized |
| the list of types (l.855–922) | ⚠ completed: `trivialHolonomy k` (non-time-like `p`, trivial `Γ_p`-holonomy) is in no printed case (l.794–800 assume a hyperbolic/parabolic circle); at `k = 2` it is the regular link, at `k = 4` a singular circle (`exists_hasType_trivialHolonomy_four`) |
| time-like « characterized by their cone angle and future/past quality » (l.862–864) | ⚠ one direction: angle and future/past are invariants (part of the type); that they determine the circle is not formalized |
| Misner « I a component of ℓ(p) ∖ (i⁺ ∪ i⁻) » (l.877) | ⚠ the image is a space-like arc (HSSingularities' strongest true form, OQ-116 (a)) |
| extreme BTZ-like « I = i^∓(ℓ(p)) » (l.887–888, l.889–891) | ⚠ `i^∓ ∖ T` (OQ-116 (b)) |
| positive / negative (l.908–922) | ⚠ the l.915 form (OQ-120 (c)) |
| « isomorphic » (l.785) | ⚠ the same `p`, `GX.GammaLinkCircle.IsIso` (OQ-120 (a)); moved-`p` isomorphisms are not treated |
| « no future », « no past », CTCs, « non-connected future » (l.537–545) | ✗ not stated (the causal half, T-bbs-layer-home / T-bbs-q8) |

## SCOPE (disclosed)

* **(a) Not formalized:** the causal clauses (local futures of `e(Σ)`, § 3.6); that the BTZ-like
  and cuspidal / extreme BTZ-like types occur (Misner, space-like and light-like do:
  `exists_hasType_listed`); that time-like circles with equal angle and position are isomorphic.
* **(b) Finding:** l.855–922 omit non-time-like circles with trivial `Γ_p`-holonomy (lifted
  holonomy `δᵏ`, `k ≥ 4` even); they are singular and have none of the printed types
  (`exists_hasType_trivialHolonomy_four`, with OQ-128's finding on l.794–795).
* **(c)** Misner is one type here; by `bbsrem:p_p`'s finding (OQ-131 (b)) it splits by chirality
  up to moved-`p` isomorphism; under the same-`p` `IsIso` the type is invariant either way.
* **(d)** The light-like types record future/past (`∂ℍ²₊` / `∂ℍ²₋`, l.800 « we still have to
  distinguish »); `toLine` forgets it, and the sign, and the cone angle, as the proposition does.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ## 1. The types of l.855–922 -/

/-- **The types of `(Γ_p, ℓ(p))`-circles** (l.855–922). -/
inductive LinkType
  /-- time-like (l.862–864), future (`p ∈ ℍ²₊`) or past (`p ∈ ℍ²₋`), with its cone angle -/
  | timelike (future : Bool) (angle : ℝ)
  /-- space-like of degree `0`, `I = i⁺(ℓ(p))` (l.873–874) -/
  | btzPast
  /-- space-like of degree `0`, `I = i⁻(ℓ(p))` (l.875–876) -/
  | btzFuture
  /-- space-like of degree `0`, `I` a space-like arc (l.877–878) -/
  | misner
  /-- light-like of degree `0`, `I = i^±(ℓ(p))` on the side of `p` (l.882–885, l.889–891) -/
  | cuspidal (future : Bool)
  /-- light-like of degree `0`, the other side (l.886–891) -/
  | extremeBTZ (future : Bool)
  /-- space-like of degree `k ≥ 1`, positive or negative (l.893–915) -/
  | spacelike (positive : Bool) (k : ℤ)
  /-- light-like of degree `k ≥ 1`, future or past, positive or negative (l.917–922) -/
  | lightlike (future : Bool) (positive : Bool) (k : ℤ)
  /-- **not in the paper's list**: non-time-like `p`, trivial `Γ_p`-holonomy, lifted holonomy `δᵏ` -/
  | trivialHolonomy (k : ℤ)
  deriving DecidableEq

/-- `ℍ²₊` or `ℍ²₋`. -/
def hypPiece : Bool → HSPiece
  | true => .hypPlus
  | false => .hypMinus

/-- **The type read on one lifted developing pair** `(D, f)` through `θ`, at `p`. -/
def PairType (p : HS 2) (θ : TpHS p ≃ₗ[ℝ] ℂ) (D : ℝ → ℝ) (f : GTilde) : LinkType → Prop
  | .timelike b a => HS.region p = hypPiece b ∧ GTilde.angle f / 2 = a
  | .btzPast => HS.region p = .deSitter ∧ GTilde.IsHyperbolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iPlus p
  | .btzFuture => HS.region p = .deSitter ∧ GTilde.IsHyperbolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iMinus p
  | .misner => HS.region p = .deSitter ∧ GTilde.IsHyperbolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj p σ)}
  | .cuspidal true => HS.region p = .bdPlus ∧ GTilde.IsParabolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iPlus p
  | .cuspidal false => HS.region p = .bdMinus ∧ GTilde.IsParabolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iMinus p
  | .extremeBTZ true => HS.region p = .bdPlus ∧ GTilde.IsParabolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iMinus p \ tangentDirs p
  | .extremeBTZ false => HS.region p = .bdMinus ∧ GTilde.IsParabolic f ∧ (∃ x, f x = x) ∧
      linkCover p θ '' range D = iPlus p \ tangentDirs p
  | .spacelike true k => HS.region p = .deSitter ∧ 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ s, linkCover p θ (D s) ∈ iPlus p → D s ≤ g (D s)
  | .spacelike false k => HS.region p = .deSitter ∧ 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      GTilde.IsHyperbolic g ∧ f = GTilde.delta ^ k * g ∧
      ∀ s, linkCover p θ (D s) ∈ iPlus p → g (D s) ≤ D s
  | .lightlike b true k => HS.region p = bdPiece b ∧ 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      GTilde.IsParabolic g ∧ f = GTilde.delta ^ k * g ∧ ∀ x, x ≤ g x
  | .lightlike b false k => HS.region p = bdPiece b ∧ 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      GTilde.IsParabolic g ∧ f = GTilde.delta ^ k * g ∧ ∀ x, g x ≤ x
  | .trivialHolonomy k => HS.region p ≠ .hypPlus ∧ HS.region p ≠ .hypMinus ∧
      f = GTilde.delta ^ k

variable {L L' : Type*} [TopologicalSpace L] [TopologicalSpace L']

/-- **`C` has type `t`**: some oriented lifted developing pair reads `t`. -/
def GammaLinkCircle.HasType (C : GammaLinkCircle L) (t : LinkType) : Prop :=
  ∃ θ : TpHS C.pt ≃ₗ[ℝ] ℂ, IsOrientedTangent C.pt θ ∧
    ∃ (E : ℝ → L) (D : ℝ → ℝ) (f : GTilde), C.IsLiftedDev θ E D f ∧ PairType C.pt θ D f t

variable {C : GammaLinkCircle L}

/-! ## 2. Elementary facts -/

theorem GammaLinkCircle.IsLiftedDev.mem_iPlusL_iff {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L}
    {D : ℝ → ℝ} {f : GTilde} (h : C.IsLiftedDev θ E D f) (s : ℝ) :
    E s ∈ C.iPlusL ↔ linkCover C.pt θ (D s) ∈ iPlus C.pt :=
  (Set.ext_iff.1 h.2.2.2.1.preimage_iPlus s).symm

namespace GTilde

theorem toPSL_eq_of_delta_mul {f g : GTilde} {k : ℤ} (hfg : f = delta ^ k * g) :
    toPSL g = toPSL f := by
  rw [hfg, map_mul, map_zpow, toPSL_delta, one_zpow, one_mul]

theorem toPSL_delta_zpow (k : ℤ) : toPSL (delta ^ k) = 1 := by
  rw [map_zpow, toPSL_delta, one_zpow]

theorem not_isHyperbolic_delta_zpow (k : ℤ) : ¬ IsHyperbolic (delta ^ k) := fun hh =>
  hh.toPSL_ne_one (toPSL_delta_zpow k)

theorem not_isParabolic_delta_zpow (k : ℤ) : ¬ IsParabolic (delta ^ k) := fun hp =>
  hp.2 (toPSL_delta_zpow k)

theorem isHyperbolic_iff_of_delta_mul {f g : GTilde} {k : ℤ} (hfg : f = delta ^ k * g) :
    IsHyperbolic g ↔ IsHyperbolic f := by
  unfold IsHyperbolic; rw [toPSL_eq_of_delta_mul hfg]

theorem isParabolic_iff_of_delta_mul {f g : GTilde} {k : ℤ} (hfg : f = delta ^ k * g) :
    IsParabolic g ↔ IsParabolic f := by
  unfold IsParabolic; rw [toPSL_eq_of_delta_mul hfg]

theorem isHyperbolic_conj_iff (κ f : GTilde) : IsHyperbolic (κ * f * κ⁻¹) ↔ IsHyperbolic f := by
  unfold IsHyperbolic PSL2.IsHyperbolic
  rw [map_mul, map_mul, map_inv, PSL2.trSq_conj]

theorem isParabolic_conj_iff (κ f : GTilde) : IsParabolic (κ * f * κ⁻¹) ↔ IsParabolic f := by
  unfold IsParabolic PSL2.IsParabolic
  rw [map_mul, map_mul, map_inv, PSL2.trSq_conj, ne_eq, conj_eq_one_iff]

theorem fixed_conj {f : GTilde} (hf : ∃ x, f x = x) (κ : GTilde) :
    ∃ x, (κ * f * κ⁻¹) x = x := by
  obtain ⟨x, hx⟩ := hf
  exact ⟨κ x, by rw [coe_mul_apply, coe_mul_apply, inv_apply_apply, hx]⟩

theorem conj_delta_mul {f g : GTilde} {k : ℤ} (hfg : f = delta ^ k * g) (κ : GTilde) :
    κ * f * κ⁻¹ = delta ^ k * (κ * g * κ⁻¹) := by
  have hc : κ * delta ^ k = delta ^ k * κ :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ delta_mem_center k)) κ
  rw [hfg, ← mul_assoc, hc, mul_assoc, mul_assoc, mul_assoc]

theorem conj_delta_zpow (k : ℤ) (κ : GTilde) : κ * delta ^ k * κ⁻¹ = delta ^ k := by
  have := conj_delta_mul (f := delta ^ k) (g := 1) (k := k) (by rw [mul_one]) κ
  rwa [mul_one, mul_inv_cancel, mul_one] at this

theorem conj_apply_le {f : GTilde} (hf : ∀ y, f y ≤ y) (h : GTilde) (x : ℝ) :
    (h * f * h⁻¹) x ≤ x := by
  rw [coe_mul_apply, coe_mul_apply]
  have := (GTilde.strictMono h).monotone (hf (h⁻¹ x))
  rwa [apply_inv_apply] at this

theorem delta_zpow_injective {k k' : ℤ} (h : delta ^ k = delta ^ k') : k = k' := by
  have := congrArg (fun g : GTilde => g 0) h
  simp only [delta_zpow_apply, zero_add] at this
  exact_mod_cast this

theorem degree_clash {f g : GTilde} {k : ℤ} (hfix : ∃ x, f x = x) (hk : 1 ≤ k)
    (hfg : f = delta ^ k * g) (hg : ∃ x, g x = x) : False := by
  obtain ⟨x, hx⟩ := hfix
  exact apply_ne_of_degree_ne_zero (by omega) hg hfg x hx

/-- The real angle of the mirror: `τ(x ↦ −g(−x)) = −τ(g)`. -/
theorem translationNumber_mirror (g : GTilde) :
    CircleDeg1Lift.translationNumber (((mirror g : GTilde) : CircleDeg1Liftˣ) : CircleDeg1Lift) =
      -CircleDeg1Lift.translationNumber ((g : CircleDeg1Liftˣ) : CircleDeg1Lift) := by
  have e : ∀ (h : GTilde) (n : ℕ),
      ((((h : CircleDeg1Liftˣ) : CircleDeg1Lift)) ^ n) 0 = (h ^ n) 0 := by
    intro h n
    show _ = (((h ^ n : GTilde) : CircleDeg1Liftˣ) : CircleDeg1Lift) 0
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  refine tendsto_nhds_unique
    (CircleDeg1Lift.tendsto_translation_number₀ (((mirror g : GTilde) : CircleDeg1Liftˣ) :
      CircleDeg1Lift)) ?_
  refine (CircleDeg1Lift.tendsto_translation_number₀
    ((g : CircleDeg1Liftˣ) : CircleDeg1Lift)).neg.congr fun n => ?_
  rw [e, e, ← map_pow, mirror_apply, neg_zero, neg_div]

/-- **The mirror of `f⁻¹` has the real angle of `f`.** -/
theorem angle_mirror_inv (f : GTilde) : angle (mirror f⁻¹) = angle f := by
  unfold angle
  rw [translationNumber_mirror]
  have : (((f⁻¹ : GTilde) : CircleDeg1Liftˣ) : CircleDeg1Lift) =
      (((f : CircleDeg1Liftˣ)⁻¹ : CircleDeg1Liftˣ) : CircleDeg1Lift) := rfl
  rw [this, CircleDeg1Lift.translationNumber_units_inv, neg_neg]

end GTilde

/-- A nonempty developed image cannot lie in two disjoint sets. -/
theorem image_clash {p : HS 2} {θ : TpHS p ≃ₗ[ℝ] ℂ} {D : ℝ → ℝ} {S T : Set (Link p)}
    (hS : linkCover p θ '' range D ⊆ S) (hT : linkCover p θ '' range D ⊆ T)
    (hST : ∀ σ ∈ S, σ ∉ T) : False :=
  hST _ (hS ⟨D 0, mem_range_self 0, rfl⟩) (hT ⟨D 0, mem_range_self 0, rfl⟩)

section Disj

variable {p : HS 2}

theorem iPlus_not_iMinus_ds (hp : HS.region p = .deSitter) : ∀ σ ∈ iPlus p, σ ∉ iMinus p := by
  have hp' := HS.mem_piece_iff_region.2 hp
  intro σ h1 h2
  rw [iPlus_of_deSitter hp'] at h1
  rw [iMinus_of_deSitter hp'] at h2
  have a := h1.1; have b := h2.1
  simp only [Prod.fst_neg] at b
  linarith

theorem iPlus_not_spacelike_ds (hp : HS.region p = .deSitter) :
    ∀ σ ∈ iPlus p, σ ∉ {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} := by
  have hp' := HS.mem_piece_iff_region.2 hp
  intro σ h1 h2
  rw [iPlus_of_deSitter hp'] at h1
  exact (minkQ_neg_of_timelike (Or.inl h1)).not_gt h2

theorem iMinus_not_spacelike_ds (hp : HS.region p = .deSitter) :
    ∀ σ ∈ iMinus p, σ ∉ {σ : Link p | 0 < Causal.Flat.minkQ (dsProj p σ)} := by
  have hp' := HS.mem_piece_iff_region.2 hp
  intro σ h1 h2
  rw [iMinus_of_deSitter hp'] at h1
  exact (minkQ_neg_of_timelike (Or.inr h1)).not_gt h2

theorem iPlus_not_iMinus_sdiff_bdPlus (hp : HS.region p = .bdPlus) :
    ∀ σ ∈ iPlus p, σ ∉ iMinus p \ tangentDirs p := by
  have hp' := HS.mem_piece_iff_region.2 hp
  have hQ : Causal.Flat.minkQ (p : 𝕄) = 0 := hp'.1
  intro σ h1 h2
  rw [iPlus_of_bdPlus hp', lightDomain_hypPlus_eq hp'] at h1
  rw [iMinus_of_bdPlus hp', lightDomain_deSitter_eq hQ, nullNonneg_sdiff] at h2
  exact lt_asymm (show nullPairing p σ < 0 from h1) h2

theorem iMinus_not_iPlus_sdiff_bdMinus (hp : HS.region p = .bdMinus) :
    ∀ σ ∈ iMinus p, σ ∉ iPlus p \ tangentDirs p := by
  have hp' := HS.mem_piece_iff_region.2 hp
  have hQ : Causal.Flat.minkQ (p : 𝕄) = 0 := hp'.1
  intro σ h1 h2
  rw [iMinus_of_bdMinus hp', lightDomain_hypMinus_eq hp'] at h1
  rw [iPlus_of_bdMinus hp', lightDomain_deSitter_eq hQ, nullNonneg_sdiff] at h2
  exact lt_asymm (show nullPairing p σ < 0 from h1) h2

end Disj

/-! ## 3. Degree `0`: the type is read on `i^±(L)` -/

/-- **Space-like, degree `0`** (l.873–878): the three images are characterised by `i^±(L)`, which
does not depend on the developing pair. -/
theorem GammaLinkCircle.IsLiftedDev.deSitter_degree_zero_iff {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
    {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde} (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : HS.region C.pt = .deSitter) (hh : GTilde.IsHyperbolic f)
    (hfix : ∃ x, f x = x) :
    (linkCover C.pt θ '' range D = iPlus C.pt ↔ C.iPlusL = univ) ∧
    (linkCover C.pt θ '' range D = iMinus C.pt ↔ C.iMinusL = univ) ∧
    (linkCover C.pt θ '' range D ⊆ {σ | 0 < Causal.Flat.minkQ (dsProj C.pt σ)} ↔
      C.iPlusL = ∅ ∧ C.iMinusL = ∅) := by
  have hne : (univ : Set L) ≠ ∅ := by haveI := C.nonempty; exact univ_nonempty.ne_empty
  rcases h.spacelike_degree_zero hθ (HS.mem_piece_iff_region.2 hp) hh hfix with
    ⟨hi, hP, hM⟩ | ⟨hi, hM, hP⟩ | ⟨hi, hP, hM⟩
  · refine ⟨⟨fun _ => hP, fun _ => hi⟩, ⟨fun h' => (image_clash hi.le h'.le
      (iPlus_not_iMinus_ds hp)).elim, fun h' => absurd (h'.symm.trans hM) hne⟩,
      ⟨fun h' => (image_clash hi.le h' (iPlus_not_spacelike_ds hp)).elim,
       fun h' => absurd (hP.symm.trans h'.1) hne⟩⟩
  · refine ⟨⟨fun h' => (image_clash h'.le hi.le (iPlus_not_iMinus_ds hp)).elim,
      fun h' => absurd (h'.symm.trans hP) hne⟩, ⟨fun _ => hM, fun _ => hi⟩,
      ⟨fun h' => (image_clash hi.le h' (iMinus_not_spacelike_ds hp)).elim,
       fun h' => absurd (hM.symm.trans h'.2) hne⟩⟩
  · refine ⟨⟨fun h' => (image_clash h'.le hi (iPlus_not_spacelike_ds hp)).elim,
      fun h' => absurd (h'.symm.trans hP) hne⟩,
      ⟨fun h' => (image_clash h'.le hi (iMinus_not_spacelike_ds hp)).elim,
      fun h' => absurd (h'.symm.trans hM) hne⟩, ⟨fun _ => ⟨hP, hM⟩, fun _ => hi⟩⟩

/-- **Light-like at `∂ℍ²₊`, degree `0`** (l.880–888): cuspidal iff `i⁺(L) = L`, extreme BTZ-like
iff `i⁻(L) = L`. -/
theorem GammaLinkCircle.IsLiftedDev.bdPlus_degree_zero_iff {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
    {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde} (hθ : IsOrientedTangent C.pt θ)
    (h : C.IsLiftedDev θ E D f) (hp : HS.region C.pt = .bdPlus) (hpar : GTilde.IsParabolic f)
    (hfix : ∃ x, f x = x) :
    (linkCover C.pt θ '' range D = iPlus C.pt ↔ C.iPlusL = univ) ∧
    (linkCover C.pt θ '' range D = iMinus C.pt \ tangentDirs C.pt ↔ C.iMinusL = univ) := by
  have hne : (univ : Set L) ≠ ∅ := by haveI := C.nonempty; exact univ_nonempty.ne_empty
  rcases h.bdPlus_degree_zero hθ (HS.mem_piece_iff_region.2 hp) hpar hfix with
    ⟨hi, hP, hM⟩ | ⟨hi, hM, hP⟩
  · exact ⟨⟨fun _ => hP, fun _ => hi⟩, ⟨fun h' => (image_clash hi.le h'.le
      (iPlus_not_iMinus_sdiff_bdPlus hp)).elim, fun h' => absurd (h'.symm.trans hM) hne⟩⟩
  · exact ⟨⟨fun h' => (image_clash h'.le hi.le (iPlus_not_iMinus_sdiff_bdPlus hp)).elim,
      fun h' => absurd (h'.symm.trans hP) hne⟩, ⟨fun _ => hM, fun _ => hi⟩⟩

/-- **Light-like at `∂ℍ²₋`, degree `0`** (l.889–891). -/
theorem GammaLinkCircle.IsLiftedDev.bdMinus_degree_zero_iff {θ : TpHS C.pt ≃ₗ[ℝ] ℂ}
    {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : C.IsLiftedDev θ E D f) (hp : HS.region C.pt = .bdMinus) (hpar : GTilde.IsParabolic f)
    (hfix : ∃ x, f x = x) :
    (linkCover C.pt θ '' range D = iMinus C.pt ↔ C.iMinusL = univ) ∧
    (linkCover C.pt θ '' range D = iPlus C.pt \ tangentDirs C.pt ↔ C.iPlusL = univ) := by
  have hne : (univ : Set L) ≠ ∅ := by haveI := C.nonempty; exact univ_nonempty.ne_empty
  rcases h.bdMinus_degree_zero (HS.mem_piece_iff_region.2 hp) hpar hfix with
    ⟨hi, hM, hP⟩ | ⟨hi, hP, hM⟩
  · exact ⟨⟨fun _ => hM, fun _ => hi⟩, ⟨fun h' => (image_clash hi.le h'.le
      (iMinus_not_iPlus_sdiff_bdMinus hp)).elim, fun h' => absurd (h'.symm.trans hP) hne⟩⟩
  · exact ⟨⟨fun h' => (image_clash h'.le hi.le (iMinus_not_iPlus_sdiff_bdMinus hp)).elim,
      fun h' => absurd (h'.symm.trans hM) hne⟩, ⟨fun _ => hP, fun _ => hi⟩⟩

/-! ## 4. Every circle has a type (l.855–922) -/

theorem GTilde.exists_eq_delta_zpow {f : GTilde} (h1 : GTilde.toPSL f = 1) :
    ∃ n : ℤ, f = GTilde.delta ^ n := by
  have hk : f ∈ GTilde.toPSL.ker := h1
  rw [GTilde.ker_toPSL, Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, hn⟩ := hk
  exact ⟨n, hn.symm⟩

/-- The exhaustion of `ℝP¹`-circles (`GX.IsLiftedDevPair.exhaust`), read on a non-elliptic
non-trivial holonomy: degree `0` (a fixed point) or degree `k ≥ 1`. -/
theorem GammaLinkCircle.IsLiftedDev.degree_cases {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L}
    {D : ℝ → ℝ} {f : GTilde} (h : C.IsLiftedDev θ E D f) (hne : ¬ GTilde.IsElliptic f)
    (h1 : GTilde.toPSL f ≠ 1) :
    (∃ x, f x = x) ∨ ∃ k : ℤ, 1 ≤ k ∧ ∃ g : GTilde, (∃ x, g x = x) ∧
      f = GTilde.delta ^ k * g := by
  letI := C.rp1ChartedSpace θ
  haveI := C.rp1_hasGroupoid θ
  rcases h.isLiftedDevPair.exhaust with ⟨he, -⟩ | ⟨k, hk, g, hg, -, hfg, -⟩ |
    ⟨-, x₀, -, -, hx₀, -⟩
  · rcases he with he | he
    · exact absurd he hne
    · exact absurd he h1
  · exact Or.inr ⟨k, hk, g, hg, hfg⟩
  · exact Or.inl ⟨x₀, hx₀⟩

/-- **Every oriented lifted developing pair reads some type** (l.855–922). -/
theorem GammaLinkCircle.IsLiftedDev.exists_pairType {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L}
    {D : ℝ → ℝ} {f : GTilde} (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f) :
    ∃ t, PairType C.pt θ D f t := by
  have triv : GTilde.toPSL f = 1 → HS.region C.pt ≠ .hypPlus → HS.region C.pt ≠ .hypMinus →
      ∃ t, PairType C.pt θ D f t := fun h1 a b => by
    obtain ⟨n, hn⟩ := GTilde.exists_eq_delta_zpow h1
    exact ⟨.trivialHolonomy n, a, b, hn⟩
  cases hr : HS.region C.pt
  · exact ⟨.timelike true (GTilde.angle f / 2), hr, rfl⟩
  · exact ⟨.timelike false (GTilde.angle f / 2), hr, rfl⟩
  · -- `p ∈ dS²`
    by_cases h1 : GTilde.toPSL f = 1
    · exact triv h1 (by rw [hr]; decide) (by rw [hr]; decide)
    have hp := HS.mem_piece_iff_region.2 hr
    have hh := h.isHyperbolic_of_deSitter hp h1
    rcases h.degree_cases hh.not_isElliptic h1 with hfix | ⟨k, hk, g, hg, hfg⟩
    · rcases h.spacelike_degree_zero hθ hp hh hfix with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
      · exact ⟨.btzPast, hr, hh, hfix, hi⟩
      · exact ⟨.btzFuture, hr, hh, hfix, hi⟩
      · exact ⟨.misner, hr, hh, hfix, hi⟩
    · have hhg := (GTilde.isHyperbolic_iff_of_delta_mul hfg).2 hh
      rcases (h.spacelike_dichotomy hθ hp hk hg hhg hfg).1 with hC | hC
      · exact ⟨.spacelike true k, hr, hk, g, hg, hhg, hfg, fun s hs =>
          hC.forall hθ h hg hfg s ((h.mem_iPlusL_iff s).2 hs)⟩
      · exact ⟨.spacelike false k, hr, hk, g, hg, hhg, hfg, fun s hs =>
          hC.forall hθ h hg hfg s ((h.mem_iPlusL_iff s).2 hs)⟩
  · -- `p ∈ ∂ℍ²₊`
    by_cases h1 : GTilde.toPSL f = 1
    · exact triv h1 (by rw [hr]; decide) (by rw [hr]; decide)
    have hQ : Causal.Flat.minkQ (C.pt : 𝕄) = 0 := (HS.mem_piece_iff_region.2 hr).1
    have hpar := h.isParabolic_of_null hQ h1
    rcases h.degree_cases hpar.not_isElliptic h1 with hfix | ⟨k, hk, g, hg, hfg⟩
    · rcases h.bdPlus_degree_zero hθ (HS.mem_piece_iff_region.2 hr) hpar hfix with
        ⟨hi, -⟩ | ⟨hi, -⟩
      · exact ⟨.cuspidal true, hr, hpar, hfix, hi⟩
      · exact ⟨.extremeBTZ true, hr, hpar, hfix, hi⟩
    · have hpg := (GTilde.isParabolic_iff_of_delta_mul hfg).2 hpar
      rcases (hpg.le_or_ge hg).1 with hle | hge
      · exact ⟨.lightlike true true k, hr, hk, g, hg, hpg, hfg, hle⟩
      · exact ⟨.lightlike true false k, hr, hk, g, hg, hpg, hfg, hge⟩
  · -- `p ∈ ∂ℍ²₋`
    by_cases h1 : GTilde.toPSL f = 1
    · exact triv h1 (by rw [hr]; decide) (by rw [hr]; decide)
    have hQ : Causal.Flat.minkQ (C.pt : 𝕄) = 0 := (HS.mem_piece_iff_region.2 hr).1
    have hpar := h.isParabolic_of_null hQ h1
    rcases h.degree_cases hpar.not_isElliptic h1 with hfix | ⟨k, hk, g, hg, hfg⟩
    · rcases h.bdMinus_degree_zero (HS.mem_piece_iff_region.2 hr) hpar hfix with
        ⟨hi, -⟩ | ⟨hi, -⟩
      · exact ⟨.cuspidal false, hr, hpar, hfix, hi⟩
      · exact ⟨.extremeBTZ false, hr, hpar, hfix, hi⟩
    · have hpg := (GTilde.isParabolic_iff_of_delta_mul hfg).2 hpar
      rcases (hpg.le_or_ge hg).1 with hle | hge
      · exact ⟨.lightlike false true k, hr, hk, g, hg, hpg, hfg, hle⟩
      · exact ⟨.lightlike false false k, hr, hk, g, hg, hpg, hfg, hge⟩

/-- **Every `(Γ_p, ℓ(p))`-circle has a type.** -/
theorem GammaLinkCircle.exists_hasType (C : GammaLinkCircle L) : ∃ t, C.HasType t := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent C.pt
  obtain ⟨E, D, f, h⟩ := C.exists_isLiftedDev θ
  obtain ⟨t, ht⟩ := h.exists_pairType hθ
  exact ⟨t, θ, hθ, E, D, f, h, ht⟩

/-! ## 5. The type does not depend on the developing pair -/

/-- **The type is read on every oriented lifted developing pair.** -/
theorem GammaLinkCircle.HasType.pairType {t : LinkType} (ht : C.HasType t)
    {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} (hθ : IsOrientedTangent C.pt θ) {E : ℝ → L} {D : ℝ → ℝ} {f : GTilde}
    (h : C.IsLiftedDev θ E D f) : PairType C.pt θ D f t := by
  obtain ⟨θ₁, hθ₁, E₁, D₁, f₁, h₁, ht₁⟩ := ht
  obtain ⟨ψ, κ, -, -, hf⟩ := h₁.relate hθ₁ hθ h
  subst hf
  rcases t with ⟨_ | _, a⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k⟩ | ⟨b, _ | _, k⟩ | k
  · exact ⟨ht₁.1, by rw [GTilde.angle_conj]; exact ht₁.2⟩
  · exact ⟨ht₁.1, by rw [GTilde.angle_conj]; exact ht₁.2⟩
  all_goals first
    | (obtain ⟨hr, hh, hfix, hi⟩ := ht₁
       first
        | (have hh' := (GTilde.isHyperbolic_conj_iff κ f₁).2 hh
           have hfix' := GTilde.fixed_conj hfix κ
           have e₁ := h₁.deSitter_degree_zero_iff hθ₁ hr hh hfix
           have e := h.deSitter_degree_zero_iff hθ hr hh' hfix'
           first
            | exact ⟨hr, hh', hfix', e.1.2 (e₁.1.1 hi)⟩
            | exact ⟨hr, hh', hfix', e.2.1.2 (e₁.2.1.1 hi)⟩
            | exact ⟨hr, hh', hfix', e.2.2.2 (e₁.2.2.1 hi)⟩)
        | (have hh' := (GTilde.isParabolic_conj_iff κ f₁).2 hh
           have hfix' := GTilde.fixed_conj hfix κ
           first
            | (have e₁ := h₁.bdPlus_degree_zero_iff hθ₁ hr hh hfix
               have e := h.bdPlus_degree_zero_iff hθ hr hh' hfix'
               first
                | exact ⟨hr, hh', hfix', e.1.2 (e₁.1.1 hi)⟩
                | exact ⟨hr, hh', hfix', e.2.2 (e₁.2.1 hi)⟩)
            | (have e₁ := h₁.bdMinus_degree_zero_iff hr hh hfix
               have e := h.bdMinus_degree_zero_iff hr hh' hfix'
               first
                | exact ⟨hr, hh', hfix', e.1.2 (e₁.1.1 hi)⟩
                | exact ⟨hr, hh', hfix', e.2.2 (e₁.2.1 hi)⟩)))
    | (obtain ⟨hr, hk, g, hg, hgh, hfg, hs⟩ := ht₁
       have hfg' := GTilde.conj_delta_mul hfg κ
       have hg' := GTilde.fixed_conj hg κ
       first
        | exact ⟨hr, hk, _, hg', (GTilde.isParabolic_conj_iff κ g).2 hgh, hfg',
            GTilde.le_conj_apply hs κ⟩
        | exact ⟨hr, hk, _, hg', (GTilde.isParabolic_conj_iff κ g).2 hgh, hfg',
            GTilde.conj_apply_le hs κ⟩
        | (have hC : C.IsSpacelikePositive := ⟨HS.mem_piece_iff_region.2 hr, θ₁, hθ₁, E₁, D₁, _, k,
             g, h₁, hk, hg, hgh, hfg, fun s hs' => hs s ((h₁.mem_iPlusL_iff s).1 hs')⟩
           exact ⟨hr, hk, _, hg', (GTilde.isHyperbolic_conj_iff κ g).2 hgh, hfg',
             fun s hs' => hC.forall hθ h hg' hfg' s ((h.mem_iPlusL_iff s).2 hs')⟩)
        | (have hC : C.IsSpacelikeNegative := ⟨HS.mem_piece_iff_region.2 hr, θ₁, hθ₁, E₁, D₁, _, k,
             g, h₁, hk, hg, hgh, hfg, fun s hs' => hs s ((h₁.mem_iPlusL_iff s).1 hs')⟩
           exact ⟨hr, hk, _, hg', (GTilde.isHyperbolic_conj_iff κ g).2 hgh, hfg',
             fun s hs' => hC.forall hθ h hg' hfg' s ((h.mem_iPlusL_iff s).2 hs')⟩))
    | (obtain ⟨a, b, hfk⟩ := ht₁
       subst hfk
       exact ⟨a, b, GTilde.conj_delta_zpow k κ⟩)

/-! ## 6. Exactly one type -/

section Clash

variable {f g g' : GTilde} {k k' : ℤ}

theorem triv_hyp (hf : f = GTilde.delta ^ k) (hh : GTilde.IsHyperbolic f) : False :=
  GTilde.not_isHyperbolic_delta_zpow k (hf ▸ hh)

theorem triv_par (hf : f = GTilde.delta ^ k) (hh : GTilde.IsParabolic f) : False :=
  GTilde.not_isParabolic_delta_zpow k (hf ▸ hh)

theorem triv_hypg (hf : f = GTilde.delta ^ k) (hfg : f = GTilde.delta ^ k' * g)
    (hh : GTilde.IsHyperbolic g) : False :=
  triv_hyp hf ((GTilde.isHyperbolic_iff_of_delta_mul hfg).1 hh)

theorem triv_parg (hf : f = GTilde.delta ^ k) (hfg : f = GTilde.delta ^ k' * g)
    (hh : GTilde.IsParabolic g) : False :=
  triv_par hf ((GTilde.isParabolic_iff_of_delta_mul hfg).1 hh)

theorem factor_eq (hg : ∃ x, g x = x) (hg' : ∃ x, g' x = x) (hfg : f = GTilde.delta ^ k * g)
    (hfg' : f = GTilde.delta ^ k' * g') : k = k' ∧ g = g' := by
  have hk := GTilde.delta_zpow_mul_unique hg hg' (hfg.symm.trans hfg')
  subst hk
  exact ⟨rfl, mul_left_cancel (hfg.symm.trans hfg')⟩

theorem light_sign_clash (hg : ∃ x, g x = x) (hg' : ∃ x, g' x = x)
    (hfg : f = GTilde.delta ^ k * g) (hfg' : f = GTilde.delta ^ k' * g')
    (hpar : GTilde.IsParabolic g) (hle : ∀ x, x ≤ g x) (hge : ∀ x, g' x ≤ x) : False := by
  obtain ⟨-, rfl⟩ := factor_eq hg hg' hfg hfg'
  have h1 : g = 1 := GTilde.ext' fun x => le_antisymm (hge x) (hle x)
  exact hpar.2 (by rw [h1, map_one])

theorem space_sign_clash {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ}
    (h : C.IsLiftedDev θ E D f) (hθ : IsOrientedTangent C.pt θ) (hr : HS.region C.pt = .deSitter)
    (hk : 1 ≤ k) (hk' : 1 ≤ k') (hg : ∃ x, g x = x) (hg' : ∃ x, g' x = x)
    (hh : GTilde.IsHyperbolic g) (hh' : GTilde.IsHyperbolic g')
    (hfg : f = GTilde.delta ^ k * g) (hfg' : f = GTilde.delta ^ k' * g')
    (hpos : ∀ s, linkCover C.pt θ (D s) ∈ iPlus C.pt → D s ≤ g (D s))
    (hneg : ∀ s, linkCover C.pt θ (D s) ∈ iPlus C.pt → g' (D s) ≤ D s) : False :=
  not_isIso_of_positive_of_negative
    ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
      fun s hs => hpos s ((h.mem_iPlusL_iff s).1 hs)⟩
    ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k', g', h, hk', hg', hh', hfg',
      fun s hs => hneg s ((h.mem_iPlusL_iff s).1 hs)⟩ (Homeomorph.refl L)
    ⟨rfl, by letI := C.atlas; exact isGXMorphism_id⟩

end Clash

/-- **One pair reads one type.** -/
theorem GammaLinkCircle.IsLiftedDev.pairType_unique {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L}
    {D : ℝ → ℝ} {f : GTilde} (hθ : IsOrientedTangent C.pt θ) (h : C.IsLiftedDev θ E D f)
    {t t' : LinkType} (ht : PairType C.pt θ D f t) (ht' : PairType C.pt θ D f t') : t = t' := by
  rcases t with ⟨_ | _, a⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k⟩ | ⟨_ | _, _ | _, k⟩ | k <;>
  rcases t' with ⟨_ | _, a'⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k'⟩ | ⟨_ | _, _ | _, k'⟩ |
    k' <;>
  dsimp only [PairType, hypPiece, bdPiece] at ht ht' <;>
  first
    | rfl
    | exact absurd (ht.1.symm.trans ht'.1) (by decide)
    | exact absurd ht'.1 ht.1
    | exact absurd ht'.1 ht.2.1
    | exact absurd ht.1 ht'.1
    | exact absurd ht.1 ht'.2.1
    | (obtain ⟨-, rfl⟩ := ht; obtain ⟨-, rfl⟩ := ht'; rfl)
    | exact congrArg _ (GTilde.delta_zpow_injective (ht.2.2.symm.trans ht'.2.2))
    | exact (triv_hyp ht.2.2 ht'.2.1).elim
    | exact (triv_hyp ht'.2.2 ht.2.1).elim
    | exact (triv_par ht.2.2 ht'.2.1).elim
    | exact (triv_par ht'.2.2 ht.2.1).elim
    | (obtain ⟨-, hk, g, hg, hgh, hfg, -⟩ := ht'
       first
        | exact (GTilde.degree_clash ht.2.2.1 hk hfg hg).elim
        | exact (triv_hypg ht.2.2 hfg hgh).elim
        | exact (triv_parg ht.2.2 hfg hgh).elim
        | (obtain ⟨-, -, g₀, hg₀, -, hfg₀, -⟩ := ht
           rw [(factor_eq hg₀ hg hfg₀ hfg).1]; done))
    | (obtain ⟨-, hk, g, hg, hgh, hfg, -⟩ := ht
       first
        | exact (GTilde.degree_clash ht'.2.2.1 hk hfg hg).elim
        | exact (triv_hypg ht'.2.2 hfg hgh).elim
        | exact (triv_parg ht'.2.2 hfg hgh).elim)
      | exact (image_clash (subset_of_eq ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_iMinus_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (ht'.2.2.2) (iPlus_not_iMinus_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_iMinus_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (ht'.2.2.2) (iPlus_not_iMinus_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_iMinus_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (ht.2.2.2) (iPlus_not_iMinus_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_iMinus_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (ht.2.2.2) (iPlus_not_iMinus_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (ht'.2.2.2) (iPlus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (ht'.2.2.2) (iPlus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (ht.2.2.2) (iPlus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (ht.2.2.2) (iPlus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (subset_of_eq ht'.2.2.2) (iMinus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (ht'.2.2.2) (iMinus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (subset_of_eq ht'.2.2.2) (iMinus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (ht.2.2.2) (ht'.2.2.2) (iMinus_not_spacelike_ds ht.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (subset_of_eq ht.2.2.2) (iMinus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (ht.2.2.2) (iMinus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (subset_of_eq ht.2.2.2) (iMinus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (ht.2.2.2) (iMinus_not_spacelike_ds ht'.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (ht'.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht.1)).elim
      | exact (image_clash (ht.2.2.2) (subset_of_eq ht'.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht.1)).elim
      | exact (image_clash (ht.2.2.2) (ht'.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht'.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (ht.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (subset_of_eq ht.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (ht.2.2.2) (iPlus_not_iMinus_sdiff_bdPlus ht'.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (subset_of_eq ht'.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht.1)).elim
      | exact (image_clash (subset_of_eq ht.2.2.2) (ht'.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht.1)).elim
      | exact (image_clash (ht.2.2.2) (subset_of_eq ht'.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht.1)).elim
      | exact (image_clash (ht.2.2.2) (ht'.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (subset_of_eq ht.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht'.1)).elim
      | exact (image_clash (subset_of_eq ht'.2.2.2) (ht.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (subset_of_eq ht.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht'.1)).elim
      | exact (image_clash (ht'.2.2.2) (ht.2.2.2) (iMinus_not_iPlus_sdiff_bdMinus ht'.1)).elim
    | (obtain ⟨hr, hk, g, hg, hgh, hfg, hs⟩ := ht
       obtain ⟨-, hk', g', hg', hgh', hfg', hs'⟩ := ht'
       first
        | exact (light_sign_clash hg hg' hfg hfg' hgh hs hs').elim
        | exact (light_sign_clash hg' hg hfg' hfg hgh' hs' hs).elim
        | exact (space_sign_clash h hθ hr hk hk' hg hg' hgh hgh' hfg hfg' hs hs').elim
        | exact (space_sign_clash h hθ hr hk' hk hg' hg hgh' hgh hfg' hfg hs' hs).elim)

/-- **The type is unique.** -/
theorem GammaLinkCircle.HasType.unique {t t' : LinkType} (ht : C.HasType t) (ht' : C.HasType t') :
    t = t' := by
  obtain ⟨θ, hθ, E, D, f, h, hp⟩ := ht
  exact h.pairType_unique hθ hp (ht'.pairType hθ h)

/-- **Every `(Γ_p, ℓ(p))`-circle has exactly one type** (l.855–922). -/
theorem GammaLinkCircle.existsUnique_hasType (C : GammaLinkCircle L) : ∃! t, C.HasType t := by
  obtain ⟨t, ht⟩ := C.exists_hasType
  exact ⟨t, ht, fun t' ht' => (ht.unique ht').symm⟩

/-- **The type of `C`.** -/
def GammaLinkCircle.linkType (C : GammaLinkCircle L) : LinkType := C.exists_hasType.choose

theorem GammaLinkCircle.hasType_linkType (C : GammaLinkCircle L) : C.HasType C.linkType :=
  C.exists_hasType.choose_spec

theorem GammaLinkCircle.hasType_iff {t : LinkType} : C.HasType t ↔ C.linkType = t :=
  ⟨fun ht => C.hasType_linkType.unique ht, fun e => e ▸ C.hasType_linkType⟩

/-! ## 7. Isomorphic circles have the same type (« mutually non isomorphic », l.785) -/

/-- **The type is an isomorphism invariant** (`GX.GammaLinkCircle.IsIso`, the same `p`). -/
theorem GammaLinkCircle.IsIso.hasType {C' : GammaLinkCircle L'} {φ : L ≃ₜ L'}
    (hφ : C.IsIso C' φ) {t : LinkType} (ht : C.HasType t) : C'.HasType t := by
  obtain ⟨hpt, hmor⟩ := hφ
  obtain ⟨q, atl, hgr, hcirc⟩ := C'
  simp only at hpt
  subst hpt
  letI := C.atlas
  letI : ChartedSpace (Link C.pt) L' := atl
  have hmor' : IsGXMorphism (GammaP C.pt) (Link C.pt) φ := hmor
  obtain ⟨θ, hθ, E, D, f, ⟨hE, hDc, hDm, hd, hDf⟩, hpt⟩ := ht
  refine ⟨θ, hθ, φ ∘ E, D, f, ⟨⟨hE.isCoveringMap.homeomorph_comp φ,
    φ.surjective.comp hE.surjective, fun s => by simp only [Function.comp_apply, hE.add_one],
    fun s t h => hE.fiber s t (φ.injective h)⟩, hDc, hDm, fun s => ?_, hDf⟩, hpt⟩
  obtain ⟨A₁, h₁⟩ := hd s
  obtain ⟨A₂, h₂⟩ := hmor'.exists_smul_eq (E s)
  refine ⟨A₁ * A₂⁻¹, ?_⟩
  filter_upwards [h₁, hE.isCoveringMap.continuous.continuousAt.eventually h₂] with s' hs1 hs2
  show (linkCover C.pt θ ∘ D) s' = (A₁ * A₂⁻¹) • chartAt (Link C.pt) (φ (E s)) (φ (E s'))
  rw [hs2, mul_smul, inv_smul_smul, hs1]

/-- Isomorphic circles have the same type. -/
theorem GammaLinkCircle.IsIso.linkType_eq {C' : GammaLinkCircle L'} {φ : L ≃ₜ L'}
    (hφ : C.IsIso C' φ) : C'.linkType = C.linkType :=
  hasType_iff.1 (hφ.hasType C.hasType_linkType)

/-- **Circles of different types are not isomorphic** (« mutually non isomorphic », l.785). -/
theorem GammaLinkCircle.not_isIso_of_hasType {C' : GammaLinkCircle L'} {t t' : LinkType}
    (ht : C.HasType t) (ht' : C'.HasType t') (hne : t ≠ t') (φ : L ≃ₜ L') : ¬ C.IsIso C' φ :=
  fun hφ => hne ((hφ.hasType ht).unique ht')

/-! ## 8. The degree, and `i^±(L)` -/

/-- **The degree of a space-like or light-like type is even and at least `2`** (l.905, l.918;
« Recall that the degree is necessarily even », l.1008). -/
theorem GammaLinkCircle.HasType.degree_even {b c : Bool} {k : ℤ}
    (ht : C.HasType (.spacelike b k) ∨ C.HasType (.lightlike b c k)) : Even k ∧ 2 ≤ k := by
  have key : ∀ {θ : TpHS C.pt ≃ₗ[ℝ] ℂ} {E : ℝ → L} {D : ℝ → ℝ} {f g : GTilde},
      C.IsLiftedDev θ E D f → 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄) → 1 ≤ k → (∃ x, g x = x) →
      f = GTilde.delta ^ k * g → Even k ∧ 2 ≤ k := fun h hQ hk hg hfg => by
    have he := h.even_of_nonneg hQ hg hfg
    refine ⟨he, ?_⟩
    obtain ⟨m, rfl⟩ := he
    omega
  rcases ht with ⟨θ, -, E, D, f, h, ht⟩ | ⟨θ, -, E, D, f, h, ht⟩
  · have hQ : 0 ≤ Causal.Flat.minkQ (C.pt : 𝕄) := by
      cases b <;> exact (show 0 < Causal.Flat.minkQ (C.pt : 𝕄) from
        HS.mem_piece_iff_region.2 ht.1).le
    cases b <;> (obtain ⟨-, hk, g, hg, -, hfg, -⟩ := ht; exact key h hQ hk hg hfg)
  · cases b <;> cases c <;>
      (obtain ⟨hr, hk, g, hg, -, hfg, -⟩ := ht
       exact key h (HS.mem_piece_iff_region.2 hr).1.ge hk hg hfg)

/-- **`i^±(L)` for the degree-`0` types** (l.873–888): BTZ-like past and future cuspidal have
`L = i⁺(L)`, `i⁻(L) = ∅`; BTZ-like future and future extreme BTZ-like have `L = i⁻(L)`,
`i⁺(L) = ∅`; Misner has `i⁺(L) = i⁻(L) = ∅`; at `∂ℍ²₋` past cuspidal has `L = i⁻(L)` and past
extreme BTZ-like `L = i⁺(L)`. -/
theorem GammaLinkCircle.HasType.iPlusL_iMinusL :
    (C.HasType .btzPast → C.iPlusL = univ ∧ C.iMinusL = ∅) ∧
    (C.HasType .btzFuture → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
    (C.HasType .misner → C.iPlusL = ∅ ∧ C.iMinusL = ∅) ∧
    (C.HasType (.cuspidal true) → C.iPlusL = univ ∧ C.iMinusL = ∅) ∧
    (C.HasType (.extremeBTZ true) → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
    (C.HasType (.cuspidal false) → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
    (C.HasType (.extremeBTZ false) → C.iPlusL = univ ∧ C.iMinusL = ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨θ, hθ, E, D, f, h, hr, hh, hfix, hi⟩
  · rcases h.spacelike_degree_zero hθ (HS.mem_piece_iff_region.2 hr) hh hfix with
      ⟨-, e⟩ | ⟨hi', -⟩ | ⟨hi', -⟩
    · exact e
    · exact (image_clash (subset_of_eq hi) (subset_of_eq hi') (iPlus_not_iMinus_ds hr)).elim
    · exact (image_clash (subset_of_eq hi) hi' (iPlus_not_spacelike_ds hr)).elim
  · rcases h.spacelike_degree_zero hθ (HS.mem_piece_iff_region.2 hr) hh hfix with
      ⟨hi', -⟩ | ⟨-, e⟩ | ⟨hi', -⟩
    · exact (image_clash (subset_of_eq hi') (subset_of_eq hi) (iPlus_not_iMinus_ds hr)).elim
    · exact e
    · exact (image_clash (subset_of_eq hi) hi' (iMinus_not_spacelike_ds hr)).elim
  · exact ((h.deSitter_degree_zero_iff hθ hr hh hfix).2.2.1 hi)
  · exact ⟨(h.bdPlus_degree_zero_iff hθ hr hh hfix).1.1 hi, by
      rcases h.bdPlus_degree_zero hθ (HS.mem_piece_iff_region.2 hr) hh hfix with
        ⟨-, -, e⟩ | ⟨hi', -⟩
      · exact e
      · exact (image_clash (subset_of_eq hi) (subset_of_eq hi')
          (iPlus_not_iMinus_sdiff_bdPlus hr)).elim⟩
  · exact ⟨(h.bdPlus_degree_zero_iff hθ hr hh hfix).2.1 hi, by
      rcases h.bdPlus_degree_zero hθ (HS.mem_piece_iff_region.2 hr) hh hfix with
        ⟨hi', -⟩ | ⟨-, -, e⟩
      · exact (image_clash (subset_of_eq hi') (subset_of_eq hi)
          (iPlus_not_iMinus_sdiff_bdPlus hr)).elim
      · exact e⟩
  · exact ⟨(h.bdMinus_degree_zero_iff hr hh hfix).1.1 hi, by
      rcases h.bdMinus_degree_zero (HS.mem_piece_iff_region.2 hr) hh hfix with
        ⟨-, -, e⟩ | ⟨hi', -⟩
      · exact e
      · exact (image_clash (subset_of_eq hi) (subset_of_eq hi')
          (iMinus_not_iPlus_sdiff_bdMinus hr)).elim⟩
  · exact ⟨(h.bdMinus_degree_zero_iff hr hh hfix).2.1 hi, by
      rcases h.bdMinus_degree_zero (HS.mem_piece_iff_region.2 hr) hh hfix with
        ⟨hi', -⟩ | ⟨-, -, e⟩
      · exact (image_clash (subset_of_eq hi') (subset_of_eq hi)
          (iMinus_not_iPlus_sdiff_bdMinus hr)).elim
      · exact e⟩

/-- **Positive / negative** in the sense of `GX.GammaLinkCircle.IsSpacelikePositive` (l.915). -/
theorem GammaLinkCircle.HasType.isSpacelikePositive {k : ℤ} (ht : C.HasType (.spacelike true k)) :
    C.IsSpacelikePositive := by
  obtain ⟨θ, hθ, E, D, f, h, hr, hk, g, hg, hh, hfg, hs⟩ := ht
  exact ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
    fun s hs' => hs s ((h.mem_iPlusL_iff s).1 hs')⟩

theorem GammaLinkCircle.HasType.isSpacelikeNegative {k : ℤ}
    (ht : C.HasType (.spacelike false k)) : C.IsSpacelikeNegative := by
  obtain ⟨θ, hθ, E, D, f, h, hr, hk, g, hg, hh, hfg, hs⟩ := ht
  exact ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg,
    fun s hs' => hs s ((h.mem_iPlusL_iff s).1 hs')⟩

theorem GammaLinkCircle.HasType.isLightlikePositive {b : Bool} {k : ℤ}
    (ht : C.HasType (.lightlike b true k)) : C.IsLightlikePositive := by
  obtain ⟨θ, hθ, E, D, f, h, hr, hk, g, hg, hh, hfg, hs⟩ := ht
  cases b <;>
    exact ⟨(HS.mem_piece_iff_region.2 hr).1, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hs⟩

theorem GammaLinkCircle.HasType.isLightlikeNegative {b : Bool} {k : ℤ}
    (ht : C.HasType (.lightlike b false k)) : C.IsLightlikeNegative := by
  obtain ⟨θ, hθ, E, D, f, h, hr, hk, g, hg, hh, hfg, hs⟩ := ht
  cases b <;>
    exact ⟨(HS.mem_piece_iff_region.2 hr).1, θ, hθ, E, D, f, k, g, h, hk, hg, hh, hfg, hs⟩

/-! ## 9. The two apices (`bbsrem:p_p`): the type at `−p̄` -/

/-- The type at `−p̄` of a circle of type `t` at `p̄` (`bbsrem:p_p`, l.935–942). -/
def LinkType.antipode : LinkType → LinkType
  | .timelike b a => .timelike (!b) a
  | .btzPast => .btzPast
  | .btzFuture => .btzFuture
  | .misner => .misner
  | .cuspidal true => .extremeBTZ false
  | .cuspidal false => .extremeBTZ true
  | .extremeBTZ true => .cuspidal false
  | .extremeBTZ false => .cuspidal true
  | .spacelike s k => .spacelike s k
  | .lightlike b s k => .lightlike (!b) s k
  | .trivialHolonomy k => .trivialHolonomy k

theorem LinkType.antipode_antipode (t : LinkType) : t.antipode.antipode = t := by
  rcases t with ⟨_ | _, a⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k⟩ | ⟨_ | _, _ | _, k⟩ | k <;>
    rfl

/-- The antipodal piece. -/
def HSPiece.swap : HSPiece → HSPiece
  | .hypPlus => .hypMinus
  | .hypMinus => .hypPlus
  | .deSitter => .deSitter
  | .bdPlus => .bdMinus
  | .bdMinus => .bdPlus

theorem HS.region_neg (p : HS 2) : HS.region (-p) = (HS.region p).swap := by
  apply HS.region_eq_of_mem
  cases hr : HS.region p <;> have hp := HS.mem_piece_iff_region.2 hr
  · exact HS.neg_mem_hypMinus_iff.2 hp
  · exact neg_mem_hypPlus_iff'.2 hp
  · exact neg_mem_deSitter_iff'.2 hp
  · exact HS.neg_mem_bdMinus_iff.2 hp
  · exact neg_mem_bdPlus_iff'.2 hp

theorem HSPiece.swap_ne {X : HSPiece} (a : X ≠ .hypPlus) (b : X ≠ .hypMinus) :
    X.swap ≠ .hypPlus ∧ X.swap ≠ .hypMinus := by
  revert a b; cases X <;> decide

theorem GTilde.mirror_inv_delta_zpow (k : ℤ) :
    GTilde.mirror (GTilde.delta ^ k)⁻¹ = GTilde.delta ^ k := by
  have := GTilde.mirror_delta_zpow_mul_inv k 1
  rwa [mul_one, inv_one, map_one, mul_one] at this

/-- **The type at `−p̄`** (`bbsrem:p_p`): time-like future and past are exchanged (the cone angle
kept), the space-like types are kept (sign and degree included), light-like future and past of
degree `k` are exchanged (sign kept), future cuspidal gives past extreme BTZ-like and future
extreme BTZ-like gives past cuspidal (and vice versa), trivial holonomy is kept. -/
theorem GammaLinkCircle.HasType.antipode {t : LinkType} (ht : C.HasType t) :
    C.antipode.HasType t.antipode := by
  obtain ⟨θ, hθ, E, D, f, h, hp⟩ := ht
  have hθ' := isOrientedTangent_tangentNeg C.pt hθ
  refine ⟨tangentNeg C.pt θ, hθ', E ∘ Neg.neg, fun s => -D (-s), GTilde.mirror f⁻¹,
    h.antipode, ?_⟩
  have hreg : HS.region C.antipode.pt = (HS.region C.pt).swap := HS.region_neg C.pt
  rcases t with ⟨_ | _, a⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k⟩ | ⟨_ | _, _ | _, k⟩ | k <;>
    dsimp only [PairType, LinkType.antipode, hypPiece, bdPiece, Bool.not_true, Bool.not_false]
      at hp ⊢
  · exact ⟨by rw [hreg, hp.1]; rfl, by rw [GTilde.angle_mirror_inv]; exact hp.2⟩
  · exact ⟨by rw [hreg, hp.1]; rfl, by rw [GTilde.angle_mirror_inv]; exact hp.2⟩
  all_goals first
    | (obtain ⟨hr, hh, ⟨x, hx⟩, hi⟩ := hp
       have hpm := HS.mem_piece_iff_region.2 hr
       first
        | (have e := GammaLinkCircle.antipode_deSitter_image (θ := θ) (D := D) hpm
           have hh' := (GTilde.isHyperbolic_mirror_inv_iff f).2 hh
           first
            | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.1 hi⟩
            | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.2.1 hi⟩
            | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.2.2 hi⟩)
        | (have hh' := (GTilde.isParabolic_mirror_inv_iff f).2 hh
           first
            | (have e := GammaLinkCircle.antipode_bdPlus_image (θ := θ) (D := D) hpm
               first
                | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.1 hi⟩
                | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.2 hi⟩)
            | (have e := GammaLinkCircle.antipode_bdMinus_image (θ := θ) (D := D) hpm
               first
                | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.1 hi⟩
                | exact ⟨by rw [hreg, hr]; rfl, hh', ⟨-x, GTilde.mirror_fixed hx⟩, e.2 hi⟩)))
    | (obtain ⟨hr, hk, g, hg, hgh, hfg, hs⟩ := hp
       obtain ⟨hf', hg'⟩ := GTilde.mirror_inv_degree hfg hg
       first
        | exact ⟨by rw [hreg, hr]; rfl, hk, _, hg', (GTilde.isParabolic_mirror_inv_iff g).2 hgh,
            hf', GTilde.le_mirror_inv_apply hs⟩
        | exact ⟨by rw [hreg, hr]; rfl, hk, _, hg', (GTilde.isParabolic_mirror_inv_iff g).2 hgh,
            hf', GTilde.mirror_inv_apply_le hs⟩
        | (have hC : C.IsSpacelikePositive := ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k,
             g, h, hk, hg, hgh, hfg, fun s hs' => hs s ((h.mem_iPlusL_iff s).1 hs')⟩
           exact ⟨by rw [hreg, hr]; rfl, hk, _, hg', (GTilde.isHyperbolic_mirror_inv_iff g).2 hgh,
             hf', fun s hs' => hC.antipode.forall hθ' h.antipode hg' hf' s
               ((h.antipode.mem_iPlusL_iff s).2 hs')⟩)
        | (have hC : C.IsSpacelikeNegative := ⟨HS.mem_piece_iff_region.2 hr, θ, hθ, E, D, f, k,
             g, h, hk, hg, hgh, hfg, fun s hs' => hs s ((h.mem_iPlusL_iff s).1 hs')⟩
           exact ⟨by rw [hreg, hr]; rfl, hk, _, hg', (GTilde.isHyperbolic_mirror_inv_iff g).2 hgh,
             hf', fun s hs' => hC.antipode.forall hθ' h.antipode hg' hf' s
               ((h.antipode.mem_iPlusL_iff s).2 hs')⟩))
    | (obtain ⟨a, b, rfl⟩ := hp
       obtain ⟨a', b'⟩ := HSPiece.swap_ne a b
       exact ⟨by rw [hreg]; exact a', by rw [hreg]; exact b', GTilde.mirror_inv_delta_zpow k⟩)

theorem GammaLinkCircle.linkType_antipode (C : GammaLinkCircle L) :
    C.antipode.linkType = C.linkType.antipode :=
  hasType_iff.1 C.hasType_linkType.antipode

/-! ## 10. The singular lines of the proposition (l.531–546, l.997–1012) -/

/-- **The types of singular lines** of `bbsprop:classising` (l.534–545), with `trivialHolonomy`
outside the printed list. The degree of `lightlike`, `spacelike` is `2` (photons, tachyons) or
`≥ 4`. -/
inductive LineType
  | timelike
  | lightlike (k : ℤ)
  | spacelike (k : ℤ)
  | btzFuture
  | btzPast
  | extremeBTZ (future : Bool)
  | misner
  | trivialHolonomy (k : ℤ)
  deriving DecidableEq

/-- The type of the singular line whose link (at one apex) has type `t`; « a cuspidal singular
line is actually included in an extreme BTZ-like singular line » (l.1011–1012). -/
def LinkType.toLine : LinkType → LineType
  | .timelike _ _ => .timelike
  | .btzPast => .btzPast
  | .btzFuture => .btzFuture
  | .misner => .misner
  | .cuspidal true => .extremeBTZ false
  | .cuspidal false => .extremeBTZ true
  | .extremeBTZ b => .extremeBTZ b
  | .spacelike _ k => .spacelike k
  | .lightlike _ _ k => .lightlike k
  | .trivialHolonomy k => .trivialHolonomy k

/-- **The line type does not depend on the apex** (`bbsrem:p_p`'s pairing). -/
theorem LinkType.toLine_antipode (t : LinkType) : t.antipode.toLine = t.toLine := by
  rcases t with ⟨_ | _, a⟩ | _ | _ | _ | (_ | _) | (_ | _) | ⟨_ | _, k⟩ | ⟨_ | _, _ | _, k⟩ | k <;>
    rfl

/-- The line type is constant on each pair `{t, t.antipode}` and the cuspidal types are sent to
extreme BTZ-like lines. -/
theorem LinkType.toLine_cuspidal (b : Bool) :
    (LinkType.cuspidal b).toLine = (LinkType.cuspidal b).antipode.toLine ∧
      (LinkType.cuspidal b).toLine = .extremeBTZ (!b) := by
  cases b <;> exact ⟨rfl, rfl⟩

theorem GammaLinkCircle.linkType_antipode_toLine (C : GammaLinkCircle L) :
    C.antipode.linkType.toLine = C.linkType.toLine := by
  rw [C.linkType_antipode, LinkType.toLine_antipode]

/-! ## 11. Outside the printed list: trivial holonomy -/

/-- **The list of l.855–922 is not exhaustive** (with OQ-128's finding on l.794–795): at every
`p ∈ dS²` there is a non-regular `(Γ_p, ℓ(p))`-circle (the 2-fold cover of `ℓ(p)`, lifted holonomy
`δ⁴`) whose only type is `trivialHolonomy 4`, none of the printed types. -/
theorem exists_hasType_trivialHolonomy_four {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
      C.HasType (.trivialHolonomy 4) ∧ ¬ C.IsRegular ∧
      ∀ t, C.HasType t → t = .trivialHolonomy 4 := by
  obtain ⟨L, _, C, rfl, -, hreg, -, -, -, θ, E, D, hθ, h⟩ := exists_isPositive_delta_four hp
  have ht : C.HasType (.trivialHolonomy 4) :=
    ⟨θ, hθ, E, D, _, h, by rw [HS.region_eq_of_mem hp]; decide,
      by rw [HS.region_eq_of_mem hp]; decide, rfl⟩
  exact ⟨L, inferInstance, C, rfl, ht, hreg, fun t ht' => ht'.unique ht⟩

/-- At a non-time-like `p`, the regular link `ℓ(p)` has type `trivialHolonomy 2`. -/
theorem hasType_regular {p : HS 2} (hp : HS.region p ≠ .hypPlus ∧ HS.region p ≠ .hypMinus) :
    (GammaLinkCircle.regular p).HasType (.trivialHolonomy 2) := by
  obtain ⟨θ, hθ⟩ := exists_isOrientedTangent p
  obtain ⟨E, D, h, -⟩ := regular_not_isHyperbolic θ
  exact ⟨θ, hθ, E, D, _, h, hp.1, hp.2, rfl⟩

/-! ## 12. Some printed types occur -/

/-- **Misner, and the space-like and light-like types of every degree `2k`, both signs, occur**
(from `GX.exists_misner` and `GX.exists_spacelike_degree_two_mul`,
`GX.exists_lightlike_degree_two_mul`). That the BTZ-like, cuspidal and extreme BTZ-like types
occur is not formalized here. -/
theorem exists_hasType_listed :
    (∀ p : HS 2, p ∈ HS.piece 2 .deSitter →
      (∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L), C.pt = p ∧
        C.HasType .misner) ∧
      ∀ (s : Bool) (k : ℕ), 1 ≤ k → ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L),
        C.pt = p ∧ C.HasType (.spacelike s (2 * k))) ∧
    (∀ (b : Bool) (p : HS 2), HS.region p = bdPiece b → ∀ (s : Bool) (k : ℕ), 1 ≤ k →
      ∃ (L : Type) (_ : TopologicalSpace L) (C : GammaLinkCircle L),
        C.pt = p ∧ C.HasType (.lightlike b s (2 * k))) := by
  refine ⟨fun p hp => ⟨?_, fun s k hk => ?_⟩, fun b p hr s k hk => ?_⟩
  · obtain ⟨L, _, C, rfl, θ, E, D, f, hθ, h, hh, hfix, hi⟩ := exists_misner hp
    exact ⟨L, inferInstance, C, rfl, θ, hθ, E, D, f, h, HS.region_eq_of_mem hp, hh, hfix, hi⟩
  · have hr := HS.region_eq_of_mem hp
    obtain ⟨⟨L, _, C, θ, E, D, g, e, hθ, h, hg, hh, hC⟩,
      ⟨L', _, C', θ', E', D', g', e', hθ', h', hg', hh', hC'⟩⟩ :=
      exists_spacelike_degree_two_mul hp hk
    cases s
    · exact ⟨L', inferInstance, C', e', θ', hθ', E', D', _, h', by rw [e']; exact hr, by omega,
        g', hg', hh', rfl, fun s hs => hC'.forall hθ' h' hg' rfl s ((h'.mem_iPlusL_iff s).2 hs)⟩
    · exact ⟨L, inferInstance, C, e, θ, hθ, E, D, _, h, by rw [e]; exact hr, by omega, g, hg, hh,
        rfl, fun s hs => hC.forall hθ h hg rfl s ((h.mem_iPlusL_iff s).2 hs)⟩
  · have hQ : Causal.Flat.minkQ (p : 𝕄) = 0 := by
      cases b <;> exact (HS.mem_piece_iff_region.2 hr).1
    obtain ⟨⟨L, _, C, θ, E, D, g, e, hθ, h, hg, hpar, hC⟩,
      ⟨L', _, C', θ', E', D', g', e', hθ', h', hg', hpar', hC'⟩⟩ :=
      exists_lightlike_degree_two_mul hQ hk
    cases s
    · refine ⟨L', inferInstance, C', e', θ', hθ', E', D', _, h', ?_⟩
      have hle : ∀ x, g' x ≤ x := by
        obtain ⟨-, θ₂, hθ₂, E₂, D₂, f₂, k₂, g₂, h₂, -, hg₂, -, hfg₂, hge₂⟩ := hC'
        obtain ⟨-, κ, -, -, hf⟩ := h₂.relate hθ₂ hθ' h'
        have hgg := (factor_eq (GTilde.fixed_conj hg₂ κ) hg'
          (GTilde.conj_delta_mul hfg₂ κ) hf.symm).2
        intro x; rw [← hgg]; exact GTilde.conj_apply_le hge₂ κ x
      have hr' : HS.region C'.pt = bdPiece b := by rw [e']; exact hr
      cases b <;> exact ⟨hr', by omega, g', hg', hpar', rfl, hle⟩
    · refine ⟨L, inferInstance, C, e, θ, hθ, E, D, _, h, ?_⟩
      have hle : ∀ x, x ≤ g x := by
        obtain ⟨-, θ₂, hθ₂, E₂, D₂, f₂, k₂, g₂, h₂, -, hg₂, -, hfg₂, hle₂⟩ := hC
        obtain ⟨-, κ, -, -, hf⟩ := h₂.relate hθ₂ hθ h
        have hgg := (factor_eq (GTilde.fixed_conj hg₂ κ) hg
          (GTilde.conj_delta_mul hfg₂ κ) hf.symm).2
        intro x; rw [← hgg]; exact GTilde.le_conj_apply hle₂ κ x
      have hr' : HS.region C.pt = bdPiece b := by rw [e]; exact hr
      cases b <;> exact ⟨hr', by omega, g, hg, hpar, rfl, hle⟩

/-! ## 13. Assembly -/

/-- **`bbsprop:classising`, the link half** (l.531–546, § 3.3 l.855–922, § 3.5 l.997–1012):
every `(Γ_p, ℓ(p))`-circle has exactly one type; isomorphic circles have the same type, and
circles of different types are not isomorphic (« mutually non isomorphic », l.785); the type at
`−p̄` is `LinkType.antipode` of the type at `p̄` (`bbsrem:p_p`), so the line type
`LinkType.toLine` does not depend on the apex, and a cuspidal end is an extreme BTZ-like line
(l.1011–1012); the degree of a space-like or light-like type is even and `≥ 2` (degree `2` or
`k ≥ 4`); the degree-`0` types are read on `i^±(L)`. The causal clauses of the proposition (no
future, no past, CTCs near Misner lines, non-connected futures in degree `≥ 4`) are not stated
here (T-bbs-layer-home / T-bbs-q8). -/
theorem GammaLinkCircle.bbsprop_classising_types {L' : Type*} [TopologicalSpace L']
    (C : GammaLinkCircle L) :
    (∃! t, C.HasType t) ∧
    (∀ (C' : GammaLinkCircle L') (φ : L ≃ₜ L'), C.IsIso C' φ → C'.linkType = C.linkType) ∧
    (∀ (C' : GammaLinkCircle L') (t t' : LinkType), C.HasType t → C'.HasType t' → t ≠ t' →
      ∀ φ : L ≃ₜ L', ¬ C.IsIso C' φ) ∧
    C.antipode.linkType = C.linkType.antipode ∧
    C.antipode.linkType.toLine = C.linkType.toLine ∧
    (∀ (b : Bool), (LinkType.cuspidal b).toLine = .extremeBTZ (!b)) ∧
    (∀ (b c : Bool) (k : ℤ), C.HasType (.spacelike b k) ∨ C.HasType (.lightlike b c k) →
      Even k ∧ 2 ≤ k) ∧
    ((C.HasType .btzPast → C.iPlusL = univ ∧ C.iMinusL = ∅) ∧
      (C.HasType .btzFuture → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
      (C.HasType .misner → C.iPlusL = ∅ ∧ C.iMinusL = ∅) ∧
      (C.HasType (.cuspidal true) → C.iPlusL = univ ∧ C.iMinusL = ∅) ∧
      (C.HasType (.extremeBTZ true) → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
      (C.HasType (.cuspidal false) → C.iMinusL = univ ∧ C.iPlusL = ∅) ∧
      (C.HasType (.extremeBTZ false) → C.iPlusL = univ ∧ C.iMinusL = ∅)) :=
  ⟨C.existsUnique_hasType, fun _ _ hφ => hφ.linkType_eq,
    fun _ _ _ ht ht' hne φ => GammaLinkCircle.not_isIso_of_hasType ht ht' hne φ,
    C.linkType_antipode, C.linkType_antipode_toLine, fun b => (LinkType.toLine_cuspidal b).2,
    fun _ _ _ h => GammaLinkCircle.HasType.degree_even h, GammaLinkCircle.HasType.iPlusL_iMinusL⟩

end GX
