import Causal.Flat.BieberbachZassenhaus
import Causal.Flat.BieberbachAbelian
import Causal.Flat.BieberbachMinSet
import Causal.Flat.BieberbachEffective
import Causal.Flat.GerochFlat


/-!
# `Causal.Flat.BieberbachProof` — Bieberbach's first theorem, proved through virtual abelianity

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.1,
the prose item **[5.B]** of `docs/BARBOT.md` (l.1720–1725): the "version of Bieberbach's Theorem",
which DEC-36 had made the named external `BieberbachI`. It is now **proved, unconditionally**
(DEC-110). **No ledger label is certified here**: [5.B] is prose, not a labelled statement.

> As an application of these theorems, it is easy for example to recover the following version
> of Bieberbach's Theorem: *If Γ is discrete group of isometries of the euclidean space of
> dimension n, it contains a finite index free abelian subgroup of finite rank.* (l.1720–1725)

The route is the author's (DEC-110: "There is a quick proof of Bieberbach with the reading that
any discrete subgroup of affine isometric group of Rn is virtually Abelian"), not the paper's
(which goes through bthm:ausl and bthm:unip, l.1727–1734):
* (1a) `Flat/BieberbachZassenhaus`: a finite-index subgroup with pairwise commuting linear parts
  (`exists_finiteIndex_commute_linearPart`: Zassenhaus near the identity, compactness of `O(E)`);
* (1b) `Flat/BieberbachAbelian`: from commuting linear parts, a finite-index abelian subgroup
  (`exists_finiteIndex_commute_of_commute_linearPart`); together,
  `virtuallyAbelian_of_isDiscreteEucl`;
* (2) `Flat/BieberbachMinSet`: an abelian group of isometries acts by translations on a nonempty
  invariant affine subspace (`exists_actsByTranslationsOn_of_commute`, a min-set argument);
* (3) `Flat/BieberbachEffective`: a finite-index subgroup acting effectively, hence
  `BieberbachConclusion` (`bieberbachConclusion_of_commute_of_actsByTranslationsOn`).
`bieberbachI : BieberbachI E` assembles them; `bieberbachI_euclideanSpace k` is the form
`BarbotExternals.bieberbach` takes.

Corollaries for Theorems A/B (existing statements unchanged): `BarbotExternalsNoBieb d`, the
bundle without its Bieberbach component, `barbotExternals_iff_noBieb`, and `barbot_A_noBieb`,
`barbot_B_noBieb`, `barbot_B_geroch_noBieb`, whose statements are those of `barbot_A`, `barbot_B`,
`barbot_B_geroch` with the reduced bundle.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| Γ discrete (l.1723) | ✓ carried, as `IsDiscreteEucl` (Flat/Bieberbach's choice) |
| `E = ℝⁿ` | ⚠ weakened: any finite-dimensional real inner product space |
| "finite index free abelian subgroup of finite rank" | ✓ in the form `BieberbachConclusion` (DEC-36); free abelian of finite rank is `virtuallyFree_of_bieberbachI` (Flat/Bieberbach) |

## SCOPE (disclosed)
* Nothing open: the four step modules and this one are sorry-free and axiom-free.
* The remaining externals of Theorems A/B are `BenoistNoLox`, `AuslanderCarriereDalbo`,
  `MaxUnipotentSubspace` (the reduced bundle) and, for B, `SelbergLemma` (and Lemma K's data for
  `barbot_B_noBieb`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-110 (integrator of WP-Bieb-1…4). Line numbers are those of
`papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

open Module

section Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Discreteness passes to subgroups. -/
theorem isDiscreteEucl_of_le {Γ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ)
    (hle : Γ' ≤ Γ) : IsDiscreteEucl Γ' :=
  fun x R => (hΓ x R).subset fun _ ⟨h1, h2⟩ => ⟨hle h1, h2⟩

/-- Finite index is transitive along `Γ₂ ≤ Γ₁ ≤ Γ`. -/
theorem finiteIndex_subgroupOf_trans {Γ Γ₁ Γ₂ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    (h₂ : (Γ₂.subgroupOf Γ₁).FiniteIndex) (h₁ : (Γ₁.subgroupOf Γ).FiniteIndex) :
    (Γ₂.subgroupOf Γ).FiniteIndex :=
  ⟨Subgroup.relIndex_ne_zero_trans h₂.index_ne_zero h₁.index_ne_zero⟩

/-- **A discrete group of isometries of a finite-dimensional Euclidean space is virtually
abelian** (DEC-110's reading of Bieberbach I). -/
theorem virtuallyAbelian_of_isDiscreteEucl [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) :
    ∃ A : Subgroup (E ≃ᵃⁱ[ℝ] E), A ≤ Γ ∧ (A.subgroupOf Γ).FiniteIndex ∧
      ∀ g ∈ A, ∀ h ∈ A, Commute g h := by
  obtain ⟨Γ₁, h₁, hfi₁, hc₁⟩ := exists_finiteIndex_commute_linearPart hΓ
  obtain ⟨Γ₂, h₂, hfi₂, hc₂⟩ :=
    exists_finiteIndex_commute_of_commute_linearPart (isDiscreteEucl_of_le hΓ h₁) hc₁
  exact ⟨Γ₂, h₂.trans h₁, finiteIndex_subgroupOf_trans hfi₂ hfi₁, hc₂⟩

/-- **Bieberbach's first theorem, proved** (DEC-110; was the named external of DEC-36). -/
theorem bieberbachI [FiniteDimensional ℝ E] : BieberbachI E := by
  intro Γ hΓ
  obtain ⟨A, hle, hfi, hA⟩ := virtuallyAbelian_of_isDiscreteEucl hΓ
  obtain ⟨U, hU, htr⟩ := exists_actsByTranslationsOn_of_commute hA
  exact bieberbachConclusion_of_commute_of_actsByTranslationsOn hΓ hle hfi hA hU htr

theorem bieberbachI_euclideanSpace (k : ℕ) : BieberbachI (EuclideanSpace ℝ (Fin k)) :=
  bieberbachI

end Proof

universe u

variable {d : ℕ}

variable (d) in
/-- **`BarbotExternals` without its Bieberbach component** (DEC-110). -/
structure BarbotExternalsNoBieb : Prop where
  benoist : ∀ k ≤ d, BenoistNoLox k
  auslander : ∀ k ≤ d, AuslanderCarriereDalbo k
  unipotent : ∀ k ≤ d, MaxUnipotentSubspace k

theorem BarbotExternalsNoBieb.toBarbotExternals (h : BarbotExternalsNoBieb d) :
    BarbotExternals d :=
  ⟨h.benoist, fun k _ => bieberbachI_euclideanSpace k, h.auslander, h.unipotent⟩

theorem barbotExternals_iff_noBieb : BarbotExternals d ↔ BarbotExternalsNoBieb d :=
  ⟨fun h => ⟨h.benoist, h.auslander, h.unipotent⟩, BarbotExternalsNoBieb.toBarbotExternals⟩

theorem barbot_A_noBieb (hE : BarbotExternalsNoBieb d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f :=
  barbot_A hE.toBarbotExternals M hGH hCC

theorem barbot_B_noBieb (hE : BarbotExternalsNoBieb d) (hSel : SelbergLemma (Minkowski d))
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B hE.toBarbotExternals hSel hK M hGH hC hM

theorem barbot_B_geroch_noBieb (hE : BarbotExternalsNoBieb d)
    (hSel : SelbergLemma (Minkowski d)) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_geroch hE.toBarbotExternals hSel M hGH hC hM

end Causal.Flat
