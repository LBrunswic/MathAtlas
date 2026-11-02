import Causal.LemmaKSC

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
* What is proved is in the strict module `Causal.LemmaKSC`: second countability makes `M` locally
  compact, σ-compact and metrizable and kills the long ray (well-ordered causal chains are
  countable), but it does not touch the residue: where curves extend, this statement is
  equivalent to the two local conditions (1')+(2') of `Causality.isCauchySurface_iff_local`,
  equivalently to the openness of the strict causal future and past
  (`Causality.isCauchySurface_iff_isOpen_strictJplus`). Second countability could only supply
  `CurvesExtend` (through a time function, Levin's theorem — not in mathlib, not proved here).

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
  sorry -- SORRY(DEC-44): open with second countability. SC gives local compactness, σ-compactness, metrizability and countable well-ordered causal chains (Causal.LemmaKSC), hence plausibly CurvesExtend through a Levin time function (not formalized); but where curves extend the statement is equivalent (isCauchySurface_iff_local) to (1') lower semicontinuity along Σ of "Σ meets J^-(w) outside w" and (2') J^+(Σ) ∪ J^-(Σ) being a neighbourhood of its points off Σ — both properties of ≤ alone, which fail to follow from ≤ where J^-(w) has empty interior near w (BTZ lines, Z^- fails), and on which SC has no visible bearing.

end Causality

end Causal
