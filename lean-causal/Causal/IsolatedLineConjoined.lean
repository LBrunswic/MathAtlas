import Causal.SCOpenWithoutTarentin
import Causal.ChronalTarentin
import Causal.GluingModels.Minimal
import Causal.Ladder.Rules

/-!
# The isolated line's full form: one conjoined witness that decides every causality node of the ladder

No label of `ETT.tex` is certified here. The file is the programme target
`T-abs-isolated-line-conjoined` (layer 1, `programme/roadmap.toml`). The line with a
chronologically isolated origin (`Causal.isolatedLine`, `Causal.LocateExtension`, kb/0050) has two
`[[fails]]` entries in `programme/ladder.toml`. Both have the `from`
`[causally_arc_connected, causally_plain, strongly_causal, strongly_causal_open, causally_open]`,
and their `to` are `tarentin` and `has_chronal_neighbour`. Each cites a witness that carries only
part of the `from`:

> The witness stays the half carrying causally_arc_connected and causally_plain.
> (`programme/ladder.toml:1799–1800`, the entry `→ tarentin`, witness
> `Causal.tarentin_and_plain_needed`)

> Since T-lad-record-sc-open-edge (2026-11-23) `from` also has strongly_causal and
> strongly_causal_open: Causal.isolatedLine_scOpen_without_tarentin
> (Causal.SCOpenWithoutTarentin) states StronglyCausal ∧ CausallyOpen ∧
> StronglyCausalOpen of the line (with ¬ Tarentin) (`programme/ladder.toml:2021–2023`, the entry
> `→ has_chronal_neighbour`, witness `Causal.isolatedLine_separates_chronalNeighbours`)

* **`Causal.isolatedLine_separates`** is the full form. It decides every one of the ladder's 19
  causality-sort nodes, positive ones first, and adds the hereditary reading of minimality:
  causally arc-connected, causally open, causally plain, strongly causal in both forms,
  absolutely minimal, absolutely minimal on every open set (`∀ W, AbsolutelyMinimalOn W`, DEC-167),
  push-up and locally push-up, causally open in the future and locally (both local forms), causal,
  curves extend, causally compact, globally hyperbolic, with a time function; and
  `¬ Tarentin`, `¬ HasChronalNeighbourEverywhere`, `¬ ChronalNeighbours`. Each of the two entries'
  `from` ids is a conjunct, and so is the negation of each `to`.
* Four facts new to the library, each from `isolatedLine_le_top` (`≤_M` lies in the order of
  `ℝ`): `isolatedLine_isCausal`, `isolatedLine_hasTimeFunction` (the identity of `ℝ`),
  `isolatedLine_causallyCompact` and `isolatedLine_globallyHyperbolic`. A diamond `J_M(p, q)` is
  `[p, q]` when the segment misses `0`, and lies in `{p}` otherwise. The ladder argued them in
  words only:

> the conjunctions it alone refutes in Lean, causally_plain ∧ globally_hyperbolic ⇒ tarentin and its
> like (with causally_compact, is_causal, time_function, strong causality), the isolated line
> refutes too, argued: it is causal, a time function is the identity, and its diamonds are compact,
> empty across 0 (0 is related to itself only, Causal.isolatedLine), none of which is in Lean.
> (`programme/ladder.toml:2530–2534`, "it" the notched plane's `¬ Tarentin`)

## Hypothesis checklist

| target's assertion | here |
|---|---|
| CausallyArcConnected, CausallyOpen, CausallyPlain, StronglyCausal, StronglyCausalOpen | ✓ conjuncts 1–5 |
| absolutely minimal on every open set | ✓ conjuncts 6 (`AbsolutelyMinimal`, the node) and 7 (`∀ W, AbsolutelyMinimalOn W`) |
| ¬ Tarentin, ¬ HasChronalNeighbourEverywhere, ¬ ChronalNeighbours | ✓ the last three conjuncts |
| every further ladder fact the library proves of the line | ✓ the eight nodes of the ladder's closure of `from` on `ℝ`: seven by `causal_ladder`, absolute minimality by `GluingModels.isolatedLine_minimal` |
| instance arguments | none: every statement is closed, on `ℝ` |

## SCOPE (disclosed)

* **Layer 1.** The imports are `Causal.SCOpenWithoutTarentin`, `Causal.ChronalTarentin`,
  `Causal.GluingModels.Minimal` and `Causal.Ladder.Rules`. `tools/ladder.py`'s `model_path` is
  `None` for each, checked one at a time in memory (kb/0247), and `None` for this module with
  those imports. The 64 Causal modules of its closure hold no module of the model layer. No
  statement mentions a metric. This module is a leaf: `Causal.Ladder.Rules` imports
  `Causal.SCOpenWithoutTarentin` and `Causal.ChronalTarentin`, and `Causal.GluingModels.Minimal`
  imports `Causal.Ladder.Rules` (through `Causal.HalfLitDual`). Nothing imports this module, so
  there is no cycle (kb/0221).
* **Beyond the target's list.** Its nine conjuncts are all here. Eleven more are added. Eight are
  the nodes the ladder's closure gives the entries' `from` on `ℝ`: absolutely_minimal, push_up,
  locally_push_up, causally_open_future, locally_causally_open_future, locally_causally_open,
  is_causal, curves_extend. The other three are new facts: causally_compact,
  globally_hyperbolic, time_function. An in-memory simulation (the report) adds them to both
  entries' `from`. No pair of the matrix changes and no contradiction appears.
* **Either reading.** The line is absolutely minimal on every open set
  (`Causal.GluingModels.isolatedLine_hereditary`), so the witness stands with or without gluing
  (DEC-167).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

/-- The diamonds of the line with an isolated origin, in `M`, are compact. -/
theorem isolatedLine_causallyCompact : isolatedLine.CausallyCompact := by
  intro p q
  by_cases h : Icc p q ⊆ ({0}ᶜ : Set ℝ)
  · have hd : isolatedLine.diamond ⊤ p q = Icc p q := by
      ext x
      rw [Causality.mem_diamond]
      refine ⟨fun hx => ⟨isolatedLine_le_top hx.1, isolatedLine_le_top hx.2⟩, fun hx => ⟨?_, ?_⟩⟩
      · rcases hx.1.eq_or_lt with rfl | hpx
        · exact Or.inl ⟨rfl, trivial⟩
        · exact Or.inr ⟨hpx, fun z hz => ⟨trivial, h ⟨hz.1, hz.2.trans hx.2⟩⟩⟩
      · rcases hx.2.eq_or_lt with rfl | hxq
        · exact Or.inl ⟨rfl, trivial⟩
        · exact Or.inr ⟨hxq, fun z hz => ⟨trivial, h ⟨hx.1.trans hz.1, hz.2⟩⟩⟩
    rw [hd]
    exact isCompact_Icc
  · have hsub : isolatedLine.diamond ⊤ p q ⊆ {p} := by
      intro x hx
      rw [Causality.mem_diamond] at hx
      obtain ⟨h1, h2⟩ := hx
      rcases h1 with ⟨rfl, -⟩ | ⟨-, hpx⟩
      · rfl
      refine absurd (fun z hz => ?_) h
      rcases h2 with ⟨rfl, -⟩ | ⟨-, hxq⟩
      · exact (hpx hz).2
      · exact (Icc_subset_Icc_union_Icc.trans (union_subset hpx hxq) hz).2
    exact (subsingleton_singleton.anti hsub).isCompact

/-- The line with an isolated origin is causal: `≤_M` lies in the order of `ℝ`. -/
theorem isolatedLine_isCausal : isolatedLine.IsCausal := fun _ _ h₁ h₂ =>
  le_antisymm (isolatedLine_le_top h₁) (isolatedLine_le_top h₂)

/-- The line with an isolated origin is globally hyperbolic. -/
theorem isolatedLine_globallyHyperbolic : isolatedLine.GloballyHyperbolic :=
  ⟨isolatedLine_isCausal, isolatedLine_causallyCompact⟩

/-- The line with an isolated origin has a time function: the identity of `ℝ`. -/
theorem isolatedLine_hasTimeFunction : isolatedLine.HasTimeFunction :=
  ⟨id, continuous_id, fun _ _ h hne => lt_of_le_of_ne (isolatedLine_le_top h) hne⟩

/-- **The isolated line's full form**: every causality-sort node of the ladder decided on the line
with a chronologically isolated origin, and absolute minimality on every open set. Positive
conjuncts: causally arc-connected, causally open, causally plain, strongly causal in both forms
(the entries' `from`), absolutely minimal (also on every open set), push-up (also locally), causally
open in the future (also locally), locally causally open, causal, curves extend, causally compact,
globally hyperbolic, with a time function. Negative conjuncts: not tarentin, not a chronal neighbour
at every point (some point has none; it is `0`, `isolatedLine_not_hasChronalNeighbour_zero`, not
stated here), no chronal neighbours. The ladder steps (`causal_ladder`): absolutely_minimal ∧
causally_plain ⇒ push_up (T1), push_up ⇒ locally_push_up, causally_open ⇒ causally_open_future,
causally_open_future ⇒ locally_causally_open_future, causally_open ⇒ locally_causally_open,
strongly_causal ⇒ is_causal (T1), and the fact curves_extend (T1, second countable). -/
theorem isolatedLine_separates :
    isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyOpen ∧
      isolatedLine.CausallyPlain ∧ isolatedLine.StronglyCausal ∧
      isolatedLine.StronglyCausalOpen ∧ isolatedLine.AbsolutelyMinimal ∧
      (∀ W : Opens ℝ, isolatedLine.AbsolutelyMinimalOn W) ∧
      isolatedLine.PushUp ∧ isolatedLine.LocallyPushUp ∧ isolatedLine.CausallyOpenFuture ∧
      isolatedLine.LocallyCausallyOpenFuture ∧ isolatedLine.LocallyCausallyOpen ∧
      isolatedLine.IsCausal ∧ isolatedLine.CurvesExtend ∧
      isolatedLine.CausallyCompact ∧ isolatedLine.GloballyHyperbolic ∧
      isolatedLine.HasTimeFunction ∧
      ¬ isolatedLine.Tarentin ∧ ¬ isolatedLine.HasChronalNeighbourEverywhere ∧
      ¬ isolatedLine.ChronalNeighbours := by
  obtain ⟨hAC, hCO, hCP, hNH, hNCN⟩ := isolatedLine_separates_chronalNeighbours
  obtain ⟨hSC, -, hNT, hSCO⟩ := isolatedLine_scOpen_without_tarentin
  have hAM : isolatedLine.AbsolutelyMinimal := GluingModels.isolatedLine_minimal
  have hPU : isolatedLine.PushUp := by causal_ladder
  have hCOF : isolatedLine.CausallyOpenFuture := by causal_ladder
  exact ⟨hAC, hCO, hCP, hSC, hSCO, hAM, GluingModels.isolatedLine_hereditary, hPU,
    by causal_ladder, hCOF, by causal_ladder, by causal_ladder, by causal_ladder,
    by causal_ladder, isolatedLine_causallyCompact, isolatedLine_globallyHyperbolic,
    isolatedLine_hasTimeFunction, hNT, hNH, hNCN⟩

end Causal
