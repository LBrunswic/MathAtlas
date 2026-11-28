import GX.BTZ.LineStructure

/-!
# btz § 5.3: the maximal BTZ-extension on the narrowed cited input « countably many BTZ lines »

Target `T-btz-richards-split` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`.
None of the three rows is marked: `𝔼₀` only (T-btz-scope), `M` connected is added (as in
`GX.BTZMax.btz_ext`), and the second bullet of the proof is carried as the named cited input
`GX.BTZLine.CountableLinesInput` (Richards' theorem MR143186 with l.1544's line-to-puncture
association: countably many BTZ lines). The second countability of each line, which
`GX.BTZMax.RichardsInput` also packed, is proved (`GX.BTZLine.secondCountable_line`), and
`GX.BTZLine.richardsInput_iff_countableLines` shows nothing is lost. The `RichardsInput` forms in
`GX.BTZ.MaxExtension` are kept; the forms here sit beside them.

* `btzthm:BTZ_ext` — `BTZ_1.tex:1528` (proof l.1535–1554) — `GX.BTZMax.btz_ext_of_countableLines`
  (existence of a globally hyperbolic BTZ-extension maximal among such, inextensible, universal,
  unique up to equivalence; under `CountableLinesInput`), with
  `GX.BTZMax.chainsInherit_of_countableLines` (the union of a coherent chain).
* `btzthm:maximal_btz_extension` — `BTZ_1.tex:1269` — the same
  `GX.BTZMax.btz_ext_of_countableLines` (« unique up to isomorphism »: an equivalence is an
  isomorphism over `M`).
* `btzthm:globally_hyperbolic_manifolds_exists` — `BTZ_1.tex:331` — the same
  `GX.BTZMax.btz_ext_of_countableLines` (the introduction's statement, verbatim l.1529–1532).

> Let $M$ be globally hyperbolic $\mass{\geq 0}$-manifolds, there exists a globally hyperbolic
> BTZ-extension $M\xrightarrow{\iota} N$ which is maximal among such extensions. Moreover,
> $M\xrightarrow{\iota}N$ is unique up to equivalence. (l.1529–1530)
>
> Let $\Sigma$ be a Cauchy surface of $M$. Each BTZ line of $\overline M\setminus M$ is associated
> to a puncture of $\Sigma$ ie an end which admits a disc neighborhood. By Richards Theorem
> \cite{MR143186}, a surface can only have countably many such ends. Therefore,
> $\sing_0(\overline M)$ has at most countably many connected components. (l.1544)

## Hypothesis checklist (`btz_ext_of_countableLines`)

| paper hypothesis | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (T-btz-scope) |
| `M` globally hyperbolic | ✓ carried |
| `M` Hausdorff, second countable (l.261) | ✓ carried |
| (none) | ⚠ strengthened: `M` connected (as in `GX.BTZMax.btz_ext`) |
| Richards' theorem MR143186 and the line-to-puncture association (l.1544) | ⚠ named cited input `GX.BTZLine.CountableLinesInput M`: in a Hausdorff connected `𝔼₀`-manifold with a BTZ-embedding of `M`, any two points of which lie in one open, second countable, globally hyperbolic BTZ-extension of `M`, the connected components of `sing₀` are countably many. That is the paper's « Therefore, `sing₀(M̄)` has at most countably many connected components » |
| « Δ admits a Riemannian metric and is thus second countable » (l.1546) | ✓ proved, not assumed (`GX.BTZLine.secondCountable_line`, `isLindelof_line`) |
| « maximal among such extensions » | ✓ carried as `AbstractDev.IsMaximal`, strengthened: inextensible and universal |
| « unique up to equivalence » | ✓ carried: every maximal one is equivalent to it |

## SCOPE (disclosed)

* **The cited input.** Richards' classification of non-compact surfaces is not in mathlib (its
  only ends are those of `SimpleGraph`), nor is the association of a BTZ line with a puncture of a
  Cauchy surface. Their consequence, « countably many lines », is the hypothesis
  `CountableLinesInput M`, never an axiom. It is equivalent to `RichardsInput M`
  (`GX.BTZLine.richardsInput_iff_countableLines`), so the theorem here and `GX.BTZMax.btz_ext`
  have the same strength; this one names only what the paper cites.
* **The route** is `GX.BTZMax.btz_ext`'s (Zorn, `Causal.AbstractDev`), through
  `GX.BTZLine.richardsInput_of_countableLines`. Universality and uniqueness
  (`isUniversal_of_isMaximal`, `equivalent_of_isMaximal`) use no cited input.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Function TopologicalSpace
open E0CBG E0Spear

namespace BTZMax

open BTZLine

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M]

/-- **Chain inheritance on the narrowed input** (`BTZ_1.tex:1535–1550`, for a chain): the union of
a non-empty coherent chain of globally hyperbolic BTZ-extensions of a connected `M` is one, and an
upper bound, given countably many BTZ lines. -/
theorem chainsInherit_of_countableLines [ConnectedSpace M] (hL : CountableLinesInput M) :
    Causal.AbstractDev.ChainsInherit.{1} (carrier := fun X : GHExt M => (X.N : Type))
      (extMor M) :=
  chainsInherit (richardsInput_of_countableLines hL)

/-- **`btzthm:BTZ_ext` on the narrowed input** (unmarked: `𝔼₀` only, `M` connected added,
`CountableLinesInput` named) (`BTZ_1.tex:1528–1532`; also `btzthm:maximal_btz_extension`, l.1269,
and `btzthm:globally_hyperbolic_manifolds_exists`, l.331): a globally hyperbolic `𝔼₀`-manifold `M`
has a globally hyperbolic BTZ-extension `E` maximal among such extensions — inextensible, and every
globally hyperbolic BTZ-extension of `M` maps into it — unique up to equivalence, given that the
BTZ lines are countably many (Richards MR143186, l.1544). -/
theorem btz_ext_of_countableLines [T2Space M] [SecondCountableTopology M]
    [HasGroupoid M e0Groupoid] [ConnectedSpace M] (hG : (CE M).GloballyHyperbolic)
    (hL : CountableLinesInput M) :
    ∃ E : GHExt M,
      Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E ∧
      Causal.AbstractDev.IsInextensible (carrier := fun X : GHExt M => (X.N : Type)) (extMor M)
        E ∧
      (∀ Y : GHExt M, ∃ f : Y.N → E.N, extMor M Y E f) ∧
      ∀ E' : GHExt M,
        Causal.AbstractDev.IsMaximal (carrier := fun X : GHExt M => (X.N : Type)) (extMor M) E' →
          Equivalent M E E' :=
  btz_ext hG (richardsInput_of_countableLines hL)

end BTZMax

end GX
