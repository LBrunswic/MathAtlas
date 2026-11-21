import Causal.Remarks.SingularRowsGeroch

/-!
# `theo:geroch_sing`, the equivalence at a genuine `E_{≥0}`-manifold (one tagged `sorry`)

The scaffold remainder of target `T-ett-singular-rows-geroch`, split at graduation; the rest is the
strict `Causal.Remarks.SingularRowsGeroch`, and the full names stay in
`Causal.SingularRowsGeroch`. Cited, unmarked: `theo:geroch_sing` — `ETT.tex:1772–1778`.

* `geroch_sing_iii_imp_i`: (iii)⇒(i) at a strongly causal (DEC-18), connected, Hausdorff, second
  countable `E_{≥0}`-manifold, stated, resting on one tagged `sorry` (OQ-32; target
  T-ett-geroch-iii-i).
* `geroch_sing`, `geroch_sing_of_isAtlasCausalityDEC25`: the equivalence (i)⇔(ii)⇔(iii), resting on
  it; the other directions are the strict module's.

## Hypothesis checklist

| paper | here |
|---|---|
| connected, strongly causal (DEC-18), Hausdorff, second countable `E_{≥0}`-manifold | ✓ carried (`[ConnectedSpace M]`, `hSC`, `[T2Space M]`, `[SecondCountableTopology M]`), `C` absolutely minimal with `IsoChartsCoverDEC25` (⚠ read: DEC-25, OQ-18) |
| (ii) a Cauchy time function; (iii) a Cauchy hypersurface | ⚠ reading: DEC-15, DEC-14 |

## SCOPE (disclosed)

* **The `sorry`** is (iii)⇒(i), `theo:geroch`'s cited step, false for topological spacetimes as
  formalized (OQ-32). At an `E_{≥0}`-manifold it needs quasi-limits of causal curves with the local
  closedness of the models' relations (`lem:densite_modele`, proved in the models, not transported
  to `M`) and compactness of `J⁻(q) ∩ J⁺(S)` for a Cauchy surface `S`; the library has neither.
  OQ-33's witness against the abstract form is not an `E_{≥0}`-manifold (the strict module's SCOPE).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

universe u

namespace SingularRowsGeroch

/-! ### `theo:geroch_sing`, the equivalence at a genuine `E_{≥0}`-manifold (one `sorry`) -/

section GerochEquivalence

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- `theo:geroch_sing` (unmarked), **(iii)⇒(i), at a strongly causal (DEC-18), connected,
Hausdorff, second countable `E_{≥0}`-manifold.** Stated, not proved: the paper's step is
`theo:geroch`'s cited (iii)⇒(i). -/
theorem geroch_sing_iii_imp_i [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) (h : ∃ S : Set M, C.IsCauchySurface S) :
    C.GloballyHyperbolic := by
  sorry -- SORRY(theo:geroch_sing): (iii)⇒(i) is theo:geroch's cited step (O'Neill, Prop. 8, Thm 35), false for topological spacetimes (OQ-32: chronoMinkowski, which is not an E≥0-manifold with an isomorphic chart at each point); at an E≥0-manifold it needs quasi-limits of causal curves with the local closedness of the models' relations (lem:densite_modele, OQ-33), and compactness of J⁻(q) ∩ J⁺(S) for a Cauchy surface S (CausalScaffold.GerochCauchy's sorry); the library has neither

/-- `theo:geroch_sing` (unmarked), **the equivalence, at a strongly causal (DEC-18), connected,
Hausdorff, second countable `E_{≥0}`-manifold**: (i)⇒(ii)⇒(iii) proved, (iii)⇒(i) is
`geroch_sing_iii_imp_i`. -/
theorem geroch_sing [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_sing_i_imp_ii hmin hC
  tfae_have 2 → 3 := geroch_sing_ii_imp_iii hmin hC hSC
  tfae_have 3 → 1 := geroch_sing_iii_imp_i hmin hC hSC
  tfae_finish

/-- `theo:geroch_sing` (unmarked) **for the natural causality**: a strongly causal singular flat
spacetime, read through DEC-25 and OQ-18. -/
theorem geroch_sing_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hSC : C.StronglyCausal) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  exact geroch_sing (SFALocal.of_isAtlasCausalityDEC25 hcov hC).1
    (SFALocal.of_isAtlasCausalityDEC25 hcov hC).2 hSC

end GerochEquivalence

end SingularRowsGeroch

end Causal
