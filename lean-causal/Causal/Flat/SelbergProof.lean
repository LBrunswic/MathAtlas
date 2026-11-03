import Causal.Flat.SelbergResidue
import Causal.Flat.SelbergTorsion
import Causal.Flat.SelbergMatrix
import Causal.Flat.GromovProof

/-!
# `Causal.Flat.SelbergProof` — Selberg's lemma, proved (DEC-115), and Theorem B without it

The named external `SelbergLemma` (DEC-36, DEC-44; `Flat/Externals.lean` §5) is **proved** for
every finite-dimensional real vector space, by the congruence-subgroup argument (DEC-115).
**No label is marked**: Selberg's lemma has no paper environment (Barbot cites it, [10.G]);
Theorem B (`bthm:cauclo`) stays marked where it is (DEC-72), and loses its Selberg component.

* `selbergLemma V` — `SelbergLemma V`, from `residueCharsStatement` (`Flat/SelbergResidue`),
  `congrStatement` (`Flat/SelbergTorsion`) and `selbergLemma_of_statements` (`Flat/SelbergMatrix`).
* Corollaries (existing statements unchanged): `barbot_B_final` (with lemma K's data `hK`) and
  `barbot_B_geroch_final` (`hK` discharged, `Flat/GerochFlat`): Theorem B under
  `BarbotExternalsMin d` only, i.e. `AuslanderCarriereDalbo` and `MaxUnipotentSubspace`.

> Selberg's lemma: a finitely generated subgroup of $GL(n, \mathbb{R})$ has a torsion-free
> subgroup of finite index. (cited by Barbot, [10.G]; the form of DEC-44)

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| finitely generated linear group in characteristic 0 | ✓ carried as in `SelbergLemma` (over `ℝ`, finite-dimensional `V`) |

## SCOPE (disclosed)
* Nothing open once the three step modules are sorry-free.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. DEC-115.
-/

namespace Causal.Flat

universe u

variable {d : ℕ}

/-- **Selberg's lemma, proved** (DEC-115; was the named external of DEC-36/44). -/
theorem selbergLemma (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    SelbergLemma V :=
  selbergLemma_of_statements residueCharsStatement congrStatement V

/-- **Theorem B with only Auslander–Carrière–Dal'bo and the maximal unipotent subspace** (and
lemma K's data). -/
theorem barbot_B_final (hE : BarbotExternalsMin d)
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_min hE (selbergLemma _) hK M hGH hC hM

/-- **Theorem B (Geroch form) with only Auslander–Carrière–Dal'bo and the maximal unipotent
subspace.** -/
theorem barbot_B_geroch_final (hE : BarbotExternalsMin d) (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_geroch_min hE (selbergLemma _) M hGH hC hM

end Causal.Flat
