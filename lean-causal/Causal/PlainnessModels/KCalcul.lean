import Causal.Port.SFABTZ
import Causal.Port.E0ModelRows
import Causal.Model.EAlphaPlain

/-!
# `prop:K_calcul` through causal plainness, the paper's route (DEC-168)

Target `T-ett-plainness-models` (`roadmap/roadmap.toml`; DEC-168 on OQ-16, OQ-28: keep causal
plainness, prove it for the models). **`prop:K_calcul`** — `ETT.tex:1557`.

> Let $M$ be a $\mass{\geq 0}$-manifold and let $p\in M$.
> (a) $K^\pm(p)=I^\pm(p)$ if $p\notin \sing_0(M)$;
> (b) $K^+(p)=I^+(p)$ if $p\in \sing_0(M)$;
> (c) if $M$ is causal and $p\in \sing_0(M)$, then $K^-(p)=J^-(p)\setminus \{p\}$.
> (`prop:K_calcul`, `ETT.tex:1557–1563`)
>
> Only the third case is not a direct consequence of Proposition \ref{prop:tarentin_fort_K}.
> (`ETT.tex:1565`)

## What is here (no `sorry`)

* `PlainnessModels.K_calcul`: the three assertions at every `E_{≥0}`-manifold, (a) and (b) by
  the paper's own route, `prop:tarentin_fort_K` (`Causality.Kminus_eq_Iminus_of_mem_Zminus`,
  `rem:comparable_property_obviously_holds`, `Causality.Kplus_eq_Iplus_of_mem_Zplus`), whose
  hypothesis « causally plain » is the model theorem `SFALocal.causallyPlain` (plainness at every
  `E_{≥0}`-manifold, from push-up and local `Z^±`, `Causality.causallyPlain_of_locZ`); `p` strongly
  tarentin in the future everywhere (`SFALocal.mem_Zplus`) and in the past off `sing₀`
  (`SFALocal.mem_Zminus_of_notMem`). (c) is `SFABTZ.K_calcul`'s third assertion (the paper's own
  proof, `lem:K_facile` along the BTZ line). The push-up route of `SFABTZ.K_calcul` (OQ-16's
  repair) is no longer the one used.
* `PlainnessModels.K_calcul_nonvacuous`: the hypotheses hold at `E₀` with a BTZ point
  (`SFABTZ.nonvacuous_e0`), kb/0011.
* `PlainnessModels.models_causallyPlain`: DEC-168's models in one statement, by reuse only
  (`massive_causallyPlain` for every `E_α`, `α > 0`; `cosmicString_causallyPlain`, DEC-188;
  `E0.causallyPlain`; `SFALocal.causallyPlain` at every `E_{≥0}`-manifold). Nothing is re-proved.

## Hypothesis checklist

| paper | here |
|---|---|
| `M` a `E_{≥0}`-manifold | ✓ carried, in the ruled readings: a singular `(Isom(𝔼^{1,2}), 𝔼^{1,2})`-manifold (DEC-25), the group `SO₀(1,2) ⋉ ℝ³` (`Flat.isom 2`, DEC-152), with a causality `C` that is absolutely minimal (DEC-167: every ETT causality is) and has an isomorphic chart at each point onto an open subset of `E₀` or of an `E_κ` (`IsoChartsCoverDEC25 … massAModelCausality`, OQ-18's reading), `E₀` as DEC-150/DEC-151 read it |
| causally plain (used through `prop:tarentin_fort_K`, l.1565) | ✓ proved, not assumed: `SFALocal.causallyPlain` |
| `p ∉ sing₀(M)` (a); `p ∈ sing₀(M)` (b), (c); `M` causal (c) | ✓ carried |
| Hausdorff, second countable | ⚠ weakened: not used (first countability comes from the charts) |

## SCOPE (disclosed)

* The statement is `SFABTZ.K_calcul`'s; the gain is the route: (a) and (b) now follow the printed
  proof, `prop:tarentin_fort_K` with causal plainness, which DEC-168 keeps, instead of push-up.
* Readings, all ruled: DEC-25 (the atlas), DEC-150, DEC-151 (`E₀`), DEC-152 (the group), DEC-167
  (absolute minimality, OQ-18), DEC-168 (plainness, OQ-16).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u

namespace PlainnessModels

attribute [local instance] E0GX.singularGX

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **`prop:K_calcul`**, at every `E_{≥0}`-manifold, (a) and (b) through `prop:tarentin_fort_K`
and causal plainness (the paper's route, DEC-168), (c) at a causal one. -/
theorem K_calcul (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (∀ p ∉ SFALocal.sing M 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p}) ∧
      (∀ p ∈ SFALocal.sing M 0, C.Kplus ⊤ {p} = C.Iplus ⊤ {p}) ∧
      (C.IsCausal → ∀ p ∈ SFALocal.sing M 0, C.Kminus ⊤ {p} = C.Jminus ⊤ {p} \ {p}) := by
  haveI := SFABTZ.firstCountableTopology_of_isoChartsCover hC
  have hP : C.CausallyPlain := SFALocal.causallyPlain hmin hC
  refine ⟨fun p hp => ⟨?_, ?_⟩, fun p _ => ?_, (SFABTZ.K_calcul hmin hC).2.2⟩
  · exact Causality.Kplus_eq_Iplus_of_mem_Zplus hP (SFALocal.mem_Zplus hC p)
  · exact Causality.Kminus_eq_Iminus_of_mem_Zminus hP (SFALocal.mem_Zminus_of_notMem hC hp)
  · exact Causality.Kplus_eq_Iplus_of_mem_Zplus hP (SFALocal.mem_Zplus hC p)

end Manifold

/-- **Non-vacuity at `E₀`** (kb/0011): the hypotheses of `K_calcul` hold at `E₀` with its natural
causality, which has a BTZ point, and is causal. -/
theorem K_calcul_nonvacuous :
    E0.causality.AbsolutelyMinimal ∧
      IsoChartsCoverDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      (SFALocal.sing E0 0).Nonempty :=
  ⟨(SFABTZ.nonvacuous_e0).1, (SFABTZ.nonvacuous_e0).2.1, (SFABTZ.nonvacuous_e0).2.2.1⟩

/-- **DEC-168's singular models are causally plain**, by reuse only: every `E_α`, `α > 0`
(`massive_causallyPlain`), Hörmann's 3+1 cosmic string of record (`cosmicString_causallyPlain`,
DEC-188), `E₀` (`E0.causallyPlain`), and every `E_{≥0}`-manifold (`SFALocal.causallyPlain`). -/
theorem models_causallyPlain :
    (∀ α : ℝ, ∀ _ : Fact (0 < α), (massive α).CausallyPlain ∧ (cosmicString α).CausallyPlain) ∧
      E0.causality.CausallyPlain ∧
      (∀ (M : Type u) [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
        (C : Causality M), C.AbsolutelyMinimal →
        IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality →
        C.CausallyPlain) :=
  ⟨fun _ _ => ⟨massive_causallyPlain, cosmicString_causallyPlain⟩, E0.causallyPlain,
    fun _ _ _ _ hmin hC => SFALocal.causallyPlain hmin hC⟩

end PlainnessModels

end Causal
