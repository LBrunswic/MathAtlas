import Causal.SingularGeroch
import CausalScaffold.GerochEquiv

/-!
# Geroch's theorem for strongly causal singular flat spacetimes: the equivalence (scaffold remainder)

`theo:geroch_sing` — `ETT.tex:1771`, principal statement `geroch_sing_of_stronglyCausal`. Not
marked: the equivalence rests on `theo:geroch`'s cited (iii)⇒(i) (`CausalScaffold.GerochEquiv`),
the model facts are the fields of `SingularFlatAxioms` (`Causal.SingularFlat`) and the local
measures in charts are the hypothesis `ModelMeasures` (`Causal.SingularGeroch`). The author ruled
(DEC-18) that `theo:geroch_sing` assumes `M` strongly causal; that hypothesis is carried.

**Split (DEC-78, 2026-11-02).** This file was `CausalScaffold.SingularGeroch` in full; its
sorry-free part (`SingularFlatSpacetime`, `VecteurFlow`, `ModelMeasures`, `mesure_admissible`,
`not_open_subset_singleton`, `Jplus_ne_singleton`, `Jminus_ne_singleton`,
`geroch_hypotheses_of_singularFlat`, `geroch_hypotheses`, `geroch_sing_i_imp_ii`,
`geroch_sing_i_imp_iii`, `geroch_sing_split`, `CupCapBTZAsPrinted`,
`cupCapBTZAsPrinted_of_globallyHyperbolic` and the timelike-line witnesses; the labels
`rem:singular_flat_spacetime_therefore`, `prop:mesure_admissible`, `def:singular_spacetime`, and
`theo:geroch_sing`'s (i)⇒(ii), (i)⇒(iii) and splitting) moved verbatim to the strict module
`Causal.SingularGeroch`, which this file imports. What stays here, verbatim, with the same
namespace, sections and variables, is exactly what uses `CausalScaffold.GerochEquiv`:
`SingularFlatAxioms.geroch_sing_of_stronglyCausal` and its witness `timelikeLine_geroch_sing`. No
statement changed.

> `theo:geroch_sing`. Let $M$ be a singular flat spacetime. The following are equivalent:
> (i) $M$ is globally hyperbolic; (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a
> Cauchy hypersurface. Moreover, if $\Sigma$ is a Cauchy surface of $M$, then $M$ is
> homeomorphic to $\Sigma\times \RR$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `E_{≥0}`-manifold, singular flat spacetime | ⚠ strengthened: `SingularFlatAxioms C sing` |
| `theo:geroch_sing`: strongly causal (DEC-18), the equivalence | ✓ carried (`geroch_sing_of_stronglyCausal`, the principal statement); the measures ⚠ strengthened: `ModelMeasures`; rests on `theo:geroch`'s cited (iii)⇒(i) (`CausalScaffold.GerochEquiv`) |
| — (i)⇒(ii), (i)⇒(iii), "homeomorphic to `Σ × ℝ`" | not here: in `Causal.SingularGeroch` (`geroch_sing_i_imp_ii`, `geroch_sing_i_imp_iii`, `geroch_sing_split`), with their checklist |
| (ii) "a Cauchy time function" | ⚠ reading: strictly increasing along `≤` (DEC-15) |

## SCOPE (disclosed)

* **The equivalence rests on `theo:geroch`'s cited (iii)⇒(i)**, the one `sorry` of
  `CausalScaffold.GerochEquiv` (O'Neill, Prop. 8 and Thm 35); there is no `sorry` of this file
  beneath `geroch_sing_of_stronglyCausal`. That citation is why these two declarations stay in
  the scaffold while the rest of the former file is strict.
* **Strong causality is a hypothesis of `theo:geroch_sing` (DEC-18), and this finding is why**
  (it is also the finding behind `rem:singular_flat_spacetime_therefore`, `Causal.SingularGeroch`,
  SCOPE). `theo:geroch` asks `M` locally causally convex (read as strong causality, DEC-7) and a
  pair of admissible measures; `prop:mesure_admissible` gives the measures only for strongly
  causal `M`, and nothing in Section 3 makes a singular flat spacetime strongly causal. By hand
  (not formalized: the library has no `E_α`): for `α > 0`, `E_α` modulo a translation along its
  (timelike) singular line is a connected singular flat spacetime with a non-empty singular
  locus; its singular line closes into a closed timelike curve, it is totally vicious
  (`J^-(q) = M` for every `q`), and it carries no measure admissible in the past. `E^{1,2}` modulo
  a timelike translation is the same example if an empty singular locus is allowed. The proof of
  `theo:geroch_sing` (l.1781–1785) needs strong causality for (ii)⇒(iii) and (iii)⇒(i). Under
  DEC-18 the statement is `geroch_sing_of_stronglyCausal`; the form without strong causality is
  not stated.
* **Satisfiability.** The timelike line instantiates `geroch_sing_of_stronglyCausal`
  (`timelikeLine_geroch_sing`), with the witnesses of `Causal.SingularGeroch`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {sing : ℝ → Set M} {p : M}

/-! ### `theo:geroch_sing`, the equivalence (the rest of the former file is `Causal.SingularGeroch`) -/

namespace SingularFlatAxioms

/-- **`theo:geroch_sing`, the equivalence** — its principal statement: `M` is strongly causal,
as the author ruled the theorem assumes (DEC-18), and the measure pair is `ModelMeasures`
(⚠ strengthened). By `theo:geroch` (`CausalScaffold.GerochEquiv`, whose (iii)⇒(i) is cited by
the paper); no `sorry` of this file. -/
theorem geroch_sing_of_stronglyCausal [MeasurableSpace M] [BorelSpace M]
    (h : C.SingularFlatAxioms sing) (hSC : C.StronglyCausal) (hM : C.ModelMeasures) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  haveI := h.metrizable
  haveI := h.locallyCompact
  obtain ⟨⟨μm, hμm⟩, ⟨μp, hμp⟩⟩ := h.mesure_admissible hSC.isCausal hM
  exact geroch h.tarentin h.causallyArcConnected hSC h.Jminus_ne_singleton h.Jplus_ne_singleton
    hμp hμm

end SingularFlatAxioms

end Causality

/-! ### Satisfiability -/

section Witness

open Causality

/-- **Witness of `geroch_sing_of_stronglyCausal`**. -/
theorem timelikeLine_geroch_sing :
    List.TFAE [timelikeLine.GloballyHyperbolic,
      ∃ T : ℝ → ℝ, timelikeLine.IsCauchyTimeFunction T ∧
        ∀ x y, timelikeLine.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set ℝ, timelikeLine.IsCauchySurface S] :=
  timelikeLine_singularFlatAxioms.geroch_sing_of_stronglyCausal timelikeLine_stronglyCausal
    timelikeLine_modelMeasures

end Witness

end Causal
