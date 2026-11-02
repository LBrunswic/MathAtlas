import Causal.LemmaKSCLocal

/-!
# Lemma K, the bare DEC-44 form with second countability — OPEN

No label is marked. This module holds one tagged `sorry`: the bare form of Lemma K
(`CausalScaffold.CompactCauchy.isCauchySurface_of_isLocallyCauchy`) with
`[SecondCountableTopology M]` added, which is ETT's own definition of a spacetime and so is
faithful to the paper rather than a weakening of it:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:255`)

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected, `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected, locally Cauchy | ✓ carried |
| separation | ⚠ `T2Space M` (as in the stub) |
| — | ⚠ added, as in the stub: `C.Tarentin`, `C.CausallyArcConnected`, `J^±(p) ≠ {p}` |
| second countability (`ETT.tex:255`) | ✓ carried: `SecondCountableTopology M` |

## SCOPE (disclosed)

* **Not proved**: one `sorry -- SORRY(DEC-44)`. Nothing may depend on it, and no declaration does.
* **The gap, narrowed (round 3, `Causal.LemmaKSCLocal`).** In exactly this setting:
  - `CurvesExtend` is PROVED (`Causality.curvesExtend_of_secondCountable`, `Causal.LevinUtility`:
    Levin's theorem gives a continuous time function);
  - two-sidedness of the charts is PROVED (`Causality.isLocallyCauchyTwoSided_of_secondCountable`,
    from `Causal.LemmaKLocal`);
  - this statement is EQUIVALENT to the openness of `J^+(O^+)` and `J^-(O^-)`, `O^±` the open
    chart sides of `Σ`
    (`Causality.isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable`), and holds
    under causal openness (`J^±(V)` open for `V` open,
    `Causality.isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable`).
  So the whole residue is causal openness of `≤` at two specific open sets; second countability
  has done what it visibly can (it supplied `CurvesExtend`), and no counterexample is known
  (`Causal.LemmaKObstruction`: it may be taken lightlike, without branching).
* Earlier rounds: `Causal.LemmaKSC` (SC ⇒ locally compact, σ-compact, metrizable; countable
  well-ordered causal chains; the characterisations `isCauchySurface_iff_local` and
  `isCauchySurface_iff_isOpen_strictJplus`), `Causal.LemmaKReduction`, `Causal.LemmaKBare`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **Lemma K, the bare DEC-44 form with second countability — OPEN, tagged `sorry`; nothing may
depend on it.** The stub `isCauchySurface_of_isLocallyCauchy` (`CausalScaffold.CompactCauchy`),
with `[SecondCountableTopology M]` added (ETT's definition of a spacetime, `ETT.tex:255`) and
otherwise its exact hypotheses. -/
theorem isCauchySurface_of_isLocallyCauchy_of_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  sorry -- SORRY(DEC-44): open with second countability. CurvesExtend and two-sidedness are proved here (Causal.LevinUtility, Causal.LemmaKLocal); the statement is equivalent (Causal.LemmaKSCLocal: isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable) to the openness of J^+(O^+) and J^-(O^-), O^± the open chart sides of Σ — causal openness of ≤ at two open sets, which neither tarentin, global hyperbolicity, causal arc-connectedness nor second countability is known to imply.

end Causality

end Causal
