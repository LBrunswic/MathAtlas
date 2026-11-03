import Causal.Flat.GromovBounded
import Causal.Flat.GromovUnbounded
import Causal.Flat.BieberbachProof

/-!
# `Causal.Flat.GromovProof` — Barbot's Prop 9.1 external `BenoistNoLox`, proved by Gromov's classification

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §9, the
external `BenoistNoLox` (DEC-36) of `bprop:sanloxo` — `GHFspace.tex:2573` (Prop 9.1) — is
**proved, for every `d`** (DEC-111), in a stronger form: no finite-index subgroup is needed. The
label is not re-certified here (it is marked in `Flat/Nonloxodromic`, DEC-97); what changes is
that its external is now a theorem, `benoistNoLox d`.

> If $\Gamma$ does not contain loxodromic elements, it is elementary; i.e., up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), or its linear part
> stabilizes an isotropic vector. (l.2575–2577)

The paper's `Γ` is a subgroup of the isometry group of Minkowski space with linear part
`L(Γ) ≤ SO₀(1, n−1)`; the Lean object is the linear group `G ≤ lorentz d` itself.

The route is the author's (DEC-111: "Gromov's classification"; after "Zariski topology is not a
very complicated theory"), not the paper's (Zariski closure + Benoist, l.2580–2597): either the
orbit of `o` in `ℍᵈ` is bounded, and `G` fixes a timelike vector (`Flat/GromovBounded`), or it is
not, and `G` fixes a nonzero null vector (`Flat/GromovUnbounded`).

* `fixesTimelikeOrNull_of_noLox` (the stronger form), `benoistNoLox`;
  `bprop_sanloxo_proved` (`bprop_sanloxo` without its external).
* Corollaries for Theorems A/B (existing statements unchanged): `BarbotExternalsNoBenoist d`
  (the bundle without Benoist), `BarbotExternalsMin d` (without Benoist and Bieberbach: only
  `AuslanderCarriereDalbo` and `MaxUnipotentSubspace`), their `iff`s with `BarbotExternals d`,
  the bridge to `Flat/BieberbachProof`'s `BarbotExternalsNoBieb d` (`BarbotExternalsMin.toNoBieb`,
  `barbotExternalsNoBieb_iff_min`),
  and `barbot_A_noBenoist`, `barbot_B_noBenoist`, `barbot_B_geroch_noBenoist`, `barbot_A_min`,
  `barbot_B_min`, `barbot_B_geroch_min`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| linear part `L(Γ) ≤ SO₀(1, n−1)` (l.2576) | ✓ carried: `G : Subgroup (lorentz d)` (the linear group itself) |
| "does not contain loxodromic elements" (l.2575) | ✓ carried |
| (Barbot's proof) Benoist's theorem, Zariski closure (l.2580–2597) | ✓ not needed: Gromov's dichotomy bounded / unbounded orbit |
| "up to finite index" (l.2576) | ⚠ weakened (stronger conclusion): `G` itself; `benoistNoLox` takes `H = G` |
| "contained in $SO(n-1)$ (up to conjugacy)" (l.2576) | ✓ as in `FixesTimelikeOrNull`: fixes a timelike vector |
| "stabilizes an isotropic vector" (l.2577) | ✓ as in `FixesTimelikeOrNull`: fixes a nonzero null vector |

## SCOPE (disclosed)

* Nothing open: the three step modules `Flat/GromovBase`, `Flat/GromovBounded`,
  `Flat/GromovUnbounded` and this one are sorry-free and axiom-free.
* No discreteness and no finite generation are used, so both uses of `BenoistNoLox` in
  `Flat/Classification` (an indiscrete `L(Γ)` in `caseOutput_nonloxodromic`, and the family-(b)
  loxodromic element of `exists_loxodromic_of_not_hasGlobalFixedPoint`) are discharged by
  `benoistNoLox d`; their statements are unchanged and still take `hB : BenoistNoLox d`.
* The remaining externals of Theorems A/B are `AuslanderCarriereDalbo`, `MaxUnipotentSubspace`
  (the bundle `BarbotExternalsMin`) and, for B, `SelbergLemma` (and Lemma K's data for
  `barbot_B_min`). Since DEC-115 (2026-11-03) `SelbergLemma` is proved (`selbergLemma`,
  `Flat/SelbergProof`, which imports this file); `barbot_B_final` and `barbot_B_geroch_final`
  there are B under `BarbotExternalsMin d` alone. The statements here are unchanged.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-111 (integrator of the Gromov route: `Flat/GromovBase`, `…Bounded`, `…Unbounded`). Line
numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

universe u

variable {d : ℕ}

/-- **Prop 9.1's conclusion for `G` itself** (stronger than `BenoistNoLox`): a subgroup of
`SO₀(1, d)` with no loxodromic element fixes a timelike vector or a nonzero null vector. -/
theorem fixesTimelikeOrNull_of_noLox {G : Subgroup (lorentz d)}
    (hG : ∀ A ∈ G, ¬IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) : FixesTimelikeOrNull G := by
  by_cases hb : ∃ M : ℝ, ∀ A ∈ G, orbitCosh A ≤ M
  · obtain ⟨M, hM⟩ := hb
    exact Or.inl (exists_fixed_timelike_of_bounded hM)
  · push Not at hb
    exact Or.inr (exists_fixed_null_of_unbounded hG hb)

variable (d) in
/-- **Barbot's Prop 9.1 external, proved** (DEC-111; was the named external of DEC-36). -/
theorem benoistNoLox : BenoistNoLox d := fun G hG =>
  ⟨G, le_rfl, by rw [Subgroup.relIndex_self]; exact one_ne_zero, fixesTimelikeOrNull_of_noLox hG⟩

/-- **Prop 9.1** (`bprop_sanloxo`) without its external. -/
theorem bprop_sanloxo_proved {Γ : Subgroup (isom d)} (hΓ : ∀ γ ∈ Γ, ¬IsLoxodromic (linOf γ)) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ((∃ v : Minkowski d, minkQ v < 0 ∧ ∀ γ ∈ Γ', linOf γ v = v ∧ IsElliptic (linOf γ)) ∨
        ∃ v₀ : Minkowski d, v₀ ≠ 0 ∧ minkQ v₀ = 0 ∧ (∀ γ ∈ Γ', linOf γ v₀ = v₀) ∧
          ((∃ γ ∈ Γ', IsParabolic (linOf γ)) ∨ ∀ γ ∈ Γ', IsElliptic (linOf γ))) :=
  bprop_sanloxo (benoistNoLox d) hΓ

/-! ### Theorems A/B without the Benoist component -/

variable (d) in
/-- **`BarbotExternals` without its Benoist component** (DEC-111). -/
structure BarbotExternalsNoBenoist : Prop where
  bieberbach : ∀ k ≤ d + 1, BieberbachI (EuclideanSpace ℝ (Fin k))
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k

theorem BarbotExternalsNoBenoist.toBarbotExternals (h : BarbotExternalsNoBenoist d) :
    BarbotExternals d :=
  ⟨fun k _ => benoistNoLox k, h.bieberbach, h.auslander, h.unipotent⟩

theorem barbotExternals_iff_noBenoist : BarbotExternals d ↔ BarbotExternalsNoBenoist d :=
  ⟨fun h => ⟨h.bieberbach, h.auslander, h.unipotent⟩, BarbotExternalsNoBenoist.toBarbotExternals⟩

variable (d) in
/-- **`BarbotExternals` without Benoist and Bieberbach** (DEC-110, DEC-111): only
Auslander–Carrière–Dal'bo and Carrière–Dal'bo's maximal unipotent subspace remain. -/
structure BarbotExternalsMin : Prop where
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k

theorem BarbotExternalsMin.toBarbotExternals (h : BarbotExternalsMin d) : BarbotExternals d :=
  ⟨fun k _ => benoistNoLox k, fun k _ => bieberbachI_euclideanSpace k, h.auslander, h.unipotent⟩

theorem barbotExternals_iff_min : BarbotExternals d ↔ BarbotExternalsMin d :=
  ⟨fun h => ⟨h.auslander, h.unipotent⟩, BarbotExternalsMin.toBarbotExternals⟩

/-- **`Flat/BieberbachProof`'s reduced bundle, further reduced** (DEC-110, DEC-111): the
Benoist component of `BarbotExternalsNoBieb d` is `benoistNoLox`, so the `_noBieb` forms of
Theorems A/B need only `BarbotExternalsMin d`. -/
theorem BarbotExternalsMin.toNoBieb (h : BarbotExternalsMin d) : BarbotExternalsNoBieb d :=
  ⟨fun k _ => benoistNoLox k, h.auslander, h.unipotent⟩

theorem barbotExternalsNoBieb_iff_min : BarbotExternalsNoBieb d ↔ BarbotExternalsMin d :=
  ⟨fun h => ⟨h.auslander, h.unipotent⟩, BarbotExternalsMin.toNoBieb⟩

theorem barbot_A_noBenoist (hE : BarbotExternalsNoBenoist d) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f :=
  barbot_A hE.toBarbotExternals M hGH hCC

theorem barbot_B_noBenoist (hE : BarbotExternalsNoBenoist d) (hSel : SelbergLemma (Minkowski d))
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B hE.toBarbotExternals hSel hK M hGH hC hM

theorem barbot_B_geroch_noBenoist (hE : BarbotExternalsNoBenoist d)
    (hSel : SelbergLemma (Minkowski d)) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_geroch hE.toBarbotExternals hSel M hGH hC hM

/-- **Theorem A with only Auslander–Carrière–Dal'bo and the maximal unipotent subspace.** -/
theorem barbot_A_min (hE : BarbotExternalsMin d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f :=
  barbot_A hE.toBarbotExternals M hGH hCC

theorem barbot_B_min (hE : BarbotExternalsMin d) (hSel : SelbergLemma (Minkowski d))
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B hE.toBarbotExternals hSel hK M hGH hC hM

/-- **Theorem B (Geroch form) with only Auslander–Carrière–Dal'bo, the maximal unipotent
subspace and Selberg's lemma.** -/
theorem barbot_B_geroch_min (hE : BarbotExternalsMin d) (hSel : SelbergLemma (Minkowski d))
    (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_geroch hE.toBarbotExternals hSel M hGH hC hM

end Causal.Flat
