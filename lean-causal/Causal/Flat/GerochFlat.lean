import Causal.Flat.TheoremBInputs
import Causal.Flat.Geroch.ConeNull
import Causal.Flat.Geroch.Reach
import Causal.Flat.Geroch.ChartNull
import Causal.Flat.Geroch.ChartMeasure

/-!
# `Causal.Flat.GerochFlat` — every GH flat spacetime carries admissible measures, hence a Cauchy surface, hence Theorem B without lemma K's input

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257); ruling
DEC-65 (`registers/DECISIONS.md`). **No label is marked here**: this discharges the named input
`FlatGerochGH` of `Flat/TheoremBInputs.lean`. Theorem B (`bthm:cauclo`, `GHFspace.tex:353`) is
marked on `barbot_B` in `Flat/Classification.lean` (DEC-72): no `sorry` lies beneath it, and it
rests on the named externals `BarbotExternals`, `SelbergLemma`.

* `exists_admissible_measure`: on every GH flat spacetime with its Borel σ-algebra, **one**
  measure `μ` admissible both in the future and in the past for `flatCausality`
  (`defi:mesure_dieckmann`, ETT.tex:1032). The flat case of `prop:mesure_dieckmann_Lorentz`
  (ETT.tex:1054).
* `flatAdmissibleMeasures : FlatAdmissibleMeasures d`, `flatGerochGH : FlatGerochGH d` (through
  `flatGerochGH_of_admissible`, i.e. ETT's `geroch_i_imp_iii`): ETT-GH (causal, compact diamonds)
  flat spacetimes are GH in Barbot's sense (l.498–507).
* `barbot_B_geroch`: `barbot_B` with its `hK` discharged (`forall_flatLemmaKData_iff`);
  `barbot_B_zero_geroch`: at `d = 0`, with every input discharged.
* `exists_frontier_null_measure`, `minkowski_frontier_null_measure`, `minkowski_admissible_pair`:
  the Minkowski instance. `minkowski_frontier_null_measure` is **the statement of ETT's `sorry`
  `minkowski_exists_measure`** (`CausalScaffold/MinkowskiMeasure.lean`,
  `SORRY(prop:mesure_dieckmann_Lorentz)`), proved here sorry-free, and `minkowski_admissible_pair`
  is that of `minkowski_mesure_dieckmann`: both are offered to the ETT campaign (DEC-65), which
  owns that file; it is not edited from here.

> 3. for all $p,q\in M$, if $p<q$ then $\mu(J^-(q)\setminus J^-(p))>0$ [...] 4. for every
> $A \subset M$, $\mu(J^-(A)\setminus K^-(A))=0$ (ETT.tex, `defi:mesure_dieckmann`)

> Let $M$ be a strongly causal Lorentzian manifold. Then $M$ admits a measure which is admissible
> both in the past and in the future. (ETT.tex, `prop:mesure_dieckmann_Lorentz`)

> Up to finite coverings, every maximal Cauchy-compact globally hyperbolic flat spacetime is
> isometric to a translation spacetime, a Misner spacetime, or the twisted product of a standart
> spacetime (Cauchy-compact Cauchy-hyperbolic GH spacetime) by an euclidean torus. (l.355–359)

Route. `μ` is the chart measure of `exists_chart_measure` (ChartMeasure: finite, regular, positive
on non-empty opens, null on every closed set whose chart images are Lebesgue-null). Property 3:
`J^∓(q) ∖ J^∓(p)` contains a non-empty open set (Reach, under GH and tarentin). Property 4:
`J^∓(A) ∖ K^∓(A) ⊆ frontier I^∓(A)` (Reach), a closed set whose chart images are Lebesgue-null
(ChartNull, from the vertical-section argument of ConeNull: the frontier of a cone-closed set
meets each vertical line in at most one point, Fubini).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:mesure_dieckmann_Lorentz`: `M` strongly causal Lorentzian | ⚠ strengthened to a GH flat spacetime (GH ⇒ strongly causal) for the admissible pair; the frontier-null measure `exists_frontier_null_measure` needs no causal hypothesis |
| `defi:mesure_dieckmann` 1.: regular Borel | ✓ carried: Borel σ-algebra (`borel N`, or `[BorelSpace N]`), mathlib's `Measure.Regular` |
| `defi:mesure_dieckmann` 4.: "for every `A ⊂ M`" | ✓ carried, for the outer measure (`rem:mesure_bord`) |
| B: maximal Cauchy-compact GH `M`; `BarbotExternals d`, `SelbergLemma (Minkowski d)` | ✓ carried as in `barbot_B`; discharged at `d = 0` |
| B: lemma K's data on every GH target (`hK`) | ✓ **discharged**: `flatGerochGH` |

## SCOPE (disclosed)

* **No `sorry` in this file or in the four `Geroch.*` modules, and none beneath them.**
  `barbot_B_geroch` and `barbot_B_zero_geroch` inherit none from `barbot_B`: the upstream
  `sorry`s they once inherited (Classification / Cla / Loxodromic: `cauclo_from_embedding` and
  what it uses) are closed, and `#print axioms` of `barbot_B`, `barbot_B_geroch`,
  `barbot_B_zero_geroch` gives `[propext, Classical.choice, Quot.sound]` (re-derived
  2026-11-02). `flatAdmissibleMeasures`, `flatGerochGH`, `exists_admissible_measure` and the
  two Minkowski theorems are **sorry-free**: `#print axioms` gives `[propext, Classical.choice,
  Quot.sound]` (so `flatGerochGH_of_admissible`, `geroch_i_imp_iii` included, carries no `sorry`).
* One measure serves both directions; `defi:mesure_dieckmann` asks one per direction.
* Universes: `FlatAdmissibleMeasures`, `FlatGerochGH` are proved universe-polymorphically and used
  at `.{0}`, where `barbot_B`'s `hK` ranges.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
ruling DEC-65, integrator of `Flat/Geroch/{ConeNull,Reach,ChartNull,ChartMeasure}`.
-/

namespace Causal.Flat

open Set MeasureTheory

universe u

variable {d : ℕ}

/-! ## §1 One measure, frontier-null, on every flat spacetime -/

/-- **A frontier-null measure on every flat spacetime**: finite, regular, positive on non-empty
open sets, and charging neither the frontier of `I^-(A)` nor that of `I^+(A)`, for every `A`.
No causal hypothesis: the flat case of ETT's `minkowski_exists_measure`. -/
theorem exists_frontier_null_measure (N : FlatSpacetime.{u} d) [MeasurableSpace N]
    [BorelSpace N] :
    ∃ μ : Measure N, μ.Regular ∧ μ univ < ⊤ ∧
      (∀ O : Set N, IsOpen O → O.Nonempty → 0 < μ O) ∧
      ∀ A : Set N, μ (frontier ((flatCausality d N).Iminus ⊤ A)) = 0 ∧
        μ (frontier ((flatCausality d N).Iplus ⊤ A)) = 0 := by
  obtain ⟨μ, hreg, hfin, hpos, hnull⟩ := exists_chart_measure N
  exact ⟨μ, hreg, hfin, hpos, fun A =>
    ⟨hnull _ isClosed_frontier fun x =>
        volume_chart_frontier_Iminus_null volume_frontier_inter_null_of_pastCone N A x,
      hnull _ isClosed_frontier fun x =>
        volume_chart_frontier_Iplus_null volume_frontier_inter_null_of_futureCone N A x⟩⟩

/-- **Admissible measures on a GH flat spacetime** (`defi:mesure_dieckmann`, flat case of
`prop:mesure_dieckmann_Lorentz`): one measure, admissible in the future and in the past, for any
Borel σ-algebra instance. -/
theorem exists_admissible_measure (N : FlatSpacetime.{u} d) [MeasurableSpace N] [BorelSpace N]
    (hN : GH N) :
    ∃ μ : Measure N, (flatCausality d N).AdmissibleFuture μ ∧
      (flatCausality d N).AdmissiblePast μ := by
  obtain ⟨μ, hreg, hfin, hpos, hnull⟩ := exists_frontier_null_measure N
  have hT := flatCausality_tarentin (d := d) (X := N)
  refine ⟨μ, ⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨hreg, hfin, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · obtain ⟨O, hO, hne', hsub⟩ := flatCausality_exists_isOpen_subset_Jplus_diff hT hN hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (flatCausality_Jplus_diff_Kplus_subset_frontier A) (hnull A).2
  · obtain ⟨O, hO, hne', hsub⟩ := flatCausality_exists_isOpen_subset_Jminus_diff hT hN hpq hne
    exact (hpos O hO hne').trans_le (measure_mono hsub)
  · exact measure_mono_null (flatCausality_Jminus_diff_Kminus_subset_frontier A) (hnull A).1

/-! ## §2 `FlatAdmissibleMeasures`, `FlatGerochGH`, Theorem B -/

/-- **Admissible measures exist on every GH flat spacetime** (`FlatAdmissibleMeasures`, DEC-65):
the same Borel measure is admissible in the future and in the past. -/
theorem flatAdmissibleMeasures : FlatAdmissibleMeasures.{u} d := by
  intro N hN
  letI : MeasurableSpace N := borel N
  haveI : BorelSpace N := ⟨rfl⟩
  obtain ⟨μ, hf, hp⟩ := exists_admissible_measure N hN
  exact ⟨μ, μ, hf, hp⟩

/-- **Geroch's existence theorem for flat spacetimes** (`theo:geroch` (i)⇒(iii), flat case):
every ETT-GH flat spacetime has a Cauchy surface (Barbot's GH, l.498–507). -/
theorem flatGerochGH : FlatGerochGH.{u} d :=
  flatGerochGH_of_admissible flatAdmissibleMeasures

/-- **Theorem B** (`bthm:cauclo`, l.353–359) with lemma K's data discharged
(`forall_flatLemmaKData_iff`, `flatGerochGH`). Unmarked here (`bthm:cauclo` is marked on
`barbot_B`, `Flat/Classification.lean`, DEC-72). No `sorry` beneath it (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`); it rests on the named externals `BarbotExternals d` and
`SelbergLemma (Minkowski d)`. -/
theorem barbot_B_geroch (hE : BarbotExternals d) (hSel : SelbergLemma (Minkowski d))
    (M : FlatSpacetime.{u} d) (hGH : GH M) (hC : CauchyCompact M) (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} d) (p : M₁ → M), IsFiniteCover d p ∧
      AMGH (CauchyCompleteClass d) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily d M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B hE hSel (forall_flatLemmaKData_iff.2 flatGerochGH) M hGH hC hM

/-- **Theorem B in `𝐌¹`** (`d = 0`) with every named input discharged (`barbotExternals_zero`,
`selbergLemma_minkowski_zero`, `flatGerochGH`). No `sorry` beneath it and no named input left
(`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`). -/
theorem barbot_B_zero_geroch (M : FlatSpacetime.{u} 0) (hGH : GH M) (hC : CauchyCompact M)
    (hM : MGH M) :
    ∃ (M₁ : FlatSpacetime.{0} 0) (p : M₁ → M), IsFiniteCover 0 p ∧
      AMGH (CauchyCompleteClass 0) M₁ ∧
      (IsTranslationSpacetime M₁ ∨ IsMisnerFamily 0 M₁ ∨
        (IsCHTorusProduct M₁ ∧ CauchyCompact M₁)) :=
  barbot_B_zero flatGerochGH M hGH hC hM

/-! ## §3 Minkowski space (offered to the ETT campaign) -/

/-- **The statement of ETT's `minkowski_exists_measure`, proved** (`prop:mesure_dieckmann_Lorentz`
on `ℝ^{1,n}`, `CausalScaffold/MinkowskiMeasure.lean`'s `sorry`): a finite regular measure on
`Minkowski n`, positive on non-empty open sets, charging the frontier of no `I^±(A)`. Offered to
the ETT campaign (DEC-65); `MinkowskiMeasure.lean` is not edited from here. -/
theorem minkowski_frontier_null_measure (n : ℕ) :
    ∃ μ : Measure (Minkowski n), μ.Regular ∧ μ univ < ⊤ ∧
      (∀ O : Set (Minkowski n), IsOpen O → O.Nonempty → 0 < μ O) ∧
      ∀ A : Set (Minkowski n), μ (frontier ((minkowski n).Iminus ⊤ A)) = 0 ∧
        μ (frontier ((minkowski n).Iplus ⊤ A)) = 0 := by
  letI : MeasurableSpace (FlatSpacetime.minkowskiSpace n) :=
    (inferInstance : MeasurableSpace (Minkowski n))
  haveI : BorelSpace (FlatSpacetime.minkowskiSpace n) :=
    (inferInstance : BorelSpace (Minkowski n))
  have h := exists_frontier_null_measure (FlatSpacetime.minkowskiSpace n)
  rw [flatCausality_minkowskiSpace] at h
  exact h

/-- **An admissible pair on Minkowski space** (`prop:mesure_dieckmann_Lorentz` on `ℝ^{1,n}`): one
measure admissible in the past and in the future for `minkowski n` — the statement of ETT's
`minkowski_mesure_dieckmann`, here sorry-free. Offered to the ETT campaign (DEC-65). -/
theorem minkowski_admissible_pair (n : ℕ) :
    ∃ μ : Measure (Minkowski n), (minkowski n).AdmissiblePast μ ∧
      (minkowski n).AdmissibleFuture μ := by
  letI : MeasurableSpace (FlatSpacetime.minkowskiSpace n) :=
    (inferInstance : MeasurableSpace (Minkowski n))
  haveI : BorelSpace (FlatSpacetime.minkowskiSpace n) :=
    (inferInstance : BorelSpace (Minkowski n))
  have h := exists_admissible_measure (FlatSpacetime.minkowskiSpace n) gh_minkowskiSpace
  rw [flatCausality_minkowskiSpace] at h
  obtain ⟨μ, hf, hp⟩ := h
  exact ⟨μ, hp, hf⟩

end Causal.Flat
