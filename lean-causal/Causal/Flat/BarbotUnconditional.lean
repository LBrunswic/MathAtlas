import Causal.Flat.ACDProof
import Causal.Flat.MaxUnipProof
import Causal.Flat.SelbergProof

/-!
# `Causal.Flat.BarbotUnconditional` — Barbot's Theorems A and B with no external hypothesis

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11,
Theorems A and B. **No label is marked here**: `bthm:caucomp` and `bthm:cauclo` stay marked in
`Flat/Classification` (DEC-72), whose statements are unchanged. What changes is that the last
two named externals of DEC-36 are now theorems (DEC-121): `auslanderCarriereDalbo d`
(`Flat/ACDProof`) and `maxUnipotentSubspace d` (`Flat/MaxUnipProof`). With Benoist
(`benoistNoLox`, DEC-111), Bieberbach I (`bieberbachI`, DEC-110) and Selberg (`selbergLemma`,
DEC-115) already proved, the bundle `BarbotExternalsMin d` is discharged:

* `barbotExternalsMin d`, `barbotExternals d` — the bundles, proved.
* `barbot_A_unconditional` — `barbot_A_min` without `hE`.
* `barbot_B_unconditional` — `barbot_B_final` without `hE`; it still carries lemma K's data
  `hK` (DEC-44), exactly as `barbot_B_final` does.
* `barbot_B_geroch_unconditional` — `barbot_B_geroch_final` without `hE`: Theorem B with **no
  hypothesis beyond the paper's** (`hK` discharged by Geroch, `Flat/GerochFlat`, DEC-65).

> Every Cauchy-complete GH flat spacetime is, up to finite coverings and linear twisted products,
> … (Theorem A, read as R1, DEC-43; Theorem B as G4, DEC-43/44 — see `Flat/Classification`)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| (DEC-36) the cited group theory: Benoist, Bieberbach I, Auslander–Carrière–Dal'bo, Carrière–Dal'bo, Selberg | ✓ not needed: all five proved (DEC-110, -111, -115, -121) |
| Theorem A: `M` GH, Cauchy-complete | ✓ carried, as in `barbot_A` |
| Theorem B: `M` GH, Cauchy-compact, maximal | ✓ carried, as in `barbot_B` |

## SCOPE (disclosed)

* The readings of Theorems A and B are those of `Flat/Classification` (DEC-43, DEC-44, DEC-72),
  disclosed there; nothing is re-read here.
* `barbot_B_unconditional` carries `hK : ∀ N, GH N → FlatLemmaKData N` (lemma K's data), as
  `barbot_B` does; `barbot_B_geroch_unconditional` is the form without it.
* The externals are consumed in their `Isom(𝐌ⁿ)` form (the form Barbot uses); they are also proved
  in the printed `Aff(n, ℝ)` generality (`Flat/AffACDProof`, `Flat/AffUnipProof`, DEC-123).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121.
-/

namespace Causal.Flat

universe u

variable {d : ℕ}

variable (d) in
/-- **`BarbotExternalsMin d`, proved** (DEC-121). -/
theorem barbotExternalsMin : BarbotExternalsMin d :=
  ⟨fun k _ => auslanderCarriereDalbo k, fun k _ => maxUnipotentSubspace k⟩

variable (d) in
/-- **`BarbotExternals d`, proved**: all four cited group-theoretic inputs of DEC-36. -/
theorem barbotExternals : BarbotExternals d :=
  (barbotExternalsMin d).toBarbotExternals

/-- **Theorem A, unconditional** (`barbot_A_min` with the bundle proved). -/
theorem barbot_A_unconditional (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hCC : IsCauchyComplete d M) :
    ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧
      ∃ (d₁ : ℕ) (_ : d₁ ≤ d) (M₁ : FlatSpacetime.{0} d₁) (B : FlatSpacetime.{0} d),
        AMGH (CauchyCompleteClass d₁) M₁ ∧
        (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d₁ M₁ ∨ IsUnipotentFamily d₁ M₁ ∨
          IsCHCentralExtension M₁) ∧
        IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding d f :=
  barbot_A_min (barbotExternalsMin d) M hGH hCC

/-- **Theorem B with no external** (`barbot_B_final` with the bundle proved; lemma K's data `hK`
is kept, as in `barbot_B`). -/
theorem barbot_B_unconditional
    (hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N) (M : FlatSpacetime.{u} d)
    (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_final (barbotExternalsMin d) hK M hGH hC hM

/-- **Theorem B (Geroch form), unconditional** (`barbot_B_geroch_final` with the bundle proved):
no hypothesis beyond the paper's. -/
theorem barbot_B_geroch_unconditional (M : FlatSpacetime.{u} d) (hGH : GH M)
    (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_geroch_final (barbotExternalsMin d) M hGH hC hM

end Causal.Flat
