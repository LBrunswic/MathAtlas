import Causal.Geroch

/-!
# The generalised Geroch theorem, assembled

`theo:geroch` — `ETT.tex:1256`, as the theorem `geroch`, with (ii) as the author ruled it
(DEC-15): a Cauchy time function strictly increasing along `≤`. Not marked: (iii)⇒(i) is cited by
the paper and not proved here; it is the one `sorry` the theorem rests on. (i)⇒(ii) and
(ii)⇒(iii) are proved in full (`Causal.Geroch`). `theo:geroch_mr` (`ETT.tex:1002`,
Geroch's theorem for Lorentzian manifolds) is cited by the paper and not formalized: the library
has no Lorentzian manifolds.

> Let $M$ be a metrizable, locally compact topological spacetime. Assume moreover that $M$ is
> tarentin, causally arc-connected and locally causally convex, and that $J^\pm(p)\neq \{p\}$ for
> every $p\in M$. If $M$ admits a pair $(\mu_+,\mu_-)$ of measures admissible respectively in the
> future and in the past, then the following are equivalent: (i) $M$ is globally hyperbolic;
> (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.

DEC-15: (ii) asks a Cauchy time function strictly increasing: `x ≤ y`, `x ≠ y` ⇒ `T x < T y`.

> \underline{$(iii)\Rightarrow(i)$} This step is technical and uses the notion of quasi-limit of a
> sequence of causal curves (Definition 7, p.~407 of \cite{oneil}). The proof is the object of
> Proposition 8 and of Theorem 35, p.~415 of \cite{oneil}. That proof carries over verbatim under
> the hypotheses of metrizability and local compactness.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| metrizable, locally compact | ✓ carried: `MetrizableSpace M`, `LocallyCompactSpace M` |
| tarentin, causally arc-connected, `J^±(p) ≠ {p}` | ✓ carried |
| locally causally convex | ⚠ reading: `StronglyCausal` (DEC-7, neighbourhoods not necessarily open); `ETT.tex:1215–1216` suggests *open* causally convex neighbourhoods, which is stronger, so the Lean hypothesis is weaker |
| a pair `(μ₊, μ₋)` admissible in the future, in the past | ✓ carried; `BorelSpace M` for "regular Borel measure" |
| (ii) a Cauchy time function, strictly increasing along `≤` (DEC-15) | ✓ carried |
| (iii) a Cauchy surface: met exactly once by every inextensible causal curve (DEC-14) | ✓ carried (`IsCauchySurface`) |

## SCOPE (disclosed)

* **(iii)⇒(i) is cited** (`geroch_iii_imp_i`): its one `sorry` mirrors the paper's citation of
  O'Neill. Quasi-limits of causal curves are not in the library.
* Nothing in the library proves that an inextensible causal curve passes through every point. If
  some `M` under these hypotheses had none, `S = ∅` would be a Cauchy surface vacuously, and the
  cited step would claim `M` globally hyperbolic: the citation carries that existence too.
* `geroch` is the principal statement; `geroch_tfae_strict` is the same theorem under the name it
  had before DEC-15 was ruled.
* **Why DEC-15** (finding, `Causal.Geroch`, SCOPE): with a time function in the sense of
  DEC-10 alone, the sketch's `S = T⁻¹(0)` can contain a null segment (on 1+1 Minkowski,
  `T = t − g(x)` with `g` bounded, `|g'| ≤ 1`, `g(x) = x` on `[0, 1]`), so it is not a Cauchy
  surface. The DEC-10-only form of (ii)⇒(iii) is not stated.
* The hypotheses are jointly satisfiable: the timelike line with the standard Gaussian measure
  satisfies all of them (`timelikeLine_geroch_tfae`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

universe u

variable {M : Type u} [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

namespace Causality

variable {C : Causality M} {μp μm : Measure M}

/-- **`theo:geroch`, (iii)⇒(i)**, cited by the paper (O'Neill, Prop. 8 and Thm 35). -/
theorem geroch_iii_imp_i (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (h : ∃ S : Set M, C.IsCauchySurface S) :
    C.GloballyHyperbolic := by
  sorry -- SORRY(theo:geroch): (iii)⇒(i) is cited (O'Neill, Prop. 8 and Thm 35); quasi-limits of causal curves are not in the library

/-- `theo:geroch`, with (ii) as ruled (DEC-15), under the name it had before the ruling: the
three conditions are equivalent. (i)⇒(ii) and (ii)⇒(iii) are proved; (iii)⇒(i) is cited. -/
theorem geroch_tfae_strict (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_i_imp_ii hμp hμm hT hC hJm hJp
  tfae_have 2 → 3 := geroch_ii_imp_iii hC hSC hJm hJp
  tfae_have 3 → 1 := geroch_iii_imp_i hT hC hSC hJm hJp hμp hμm
  tfae_finish

/-- `theo:geroch` (DEC-15): on a metrizable, locally compact, tarentin, causally
arc-connected, locally causally convex spacetime with `J^±(p) ≠ {p}` and a pair of admissible
measures, the following are equivalent: (i) `M` is globally hyperbolic; (ii) `M` admits a Cauchy
time function strictly increasing along `≤`; (iii) `M` admits a Cauchy surface. -/
theorem geroch (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] :=
  geroch_tfae_strict hT hC hSC hJm hJp hμp hμm

end Causality

/-- **The hypotheses of `theo:geroch` are jointly satisfiable**: the timelike line, with the
standard Gaussian measure as both `μ₊` and `μ₋`. -/
theorem timelikeLine_geroch_tfae :
    List.TFAE [timelikeLine.GloballyHyperbolic,
      ∃ T : ℝ → ℝ, timelikeLine.IsCauchyTimeFunction T ∧
        ∀ x y, timelikeLine.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set ℝ, timelikeLine.IsCauchySurface S] :=
  Causality.geroch timelikeLine_tarentin timelikeLine_causallyArcConnected
    timelikeLine_stronglyCausal timelikeLine_Jminus_ne timelikeLine_Jplus_ne
    timelikeLine_admissible_past_and_future.2 timelikeLine_admissible_past_and_future.1

end Causal
