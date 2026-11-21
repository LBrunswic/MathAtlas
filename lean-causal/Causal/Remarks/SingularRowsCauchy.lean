import Causal.SingularCauchy
import Causal.Remarks.SingularRowsK
import Causal.Remarks.SingularRowsGeroch

/-!
# A Cauchy surface separates at every `E_{≥0}`-manifold; `K⁻ ∩ J⁺(Σ)` orders `J⁺(Σ) ∖ Σ`; Cauchy embeddings carry every Cauchy surface

Target `T-ett-sigma-separe`, parts (b) and (c). Cited, all unmarked (SCOPE):
`lem:Sigma_separe` — `ETT.tex:2062`, its « In particular » with no `ψ`;
`cor:K_ordre_Sigma` — `ETT.tex:2082`, for every Cauchy surface, no hypothesis left;
`lem:Cauchy_plongement_toutes` — `ETT.tex:1865`, with no hypothesis left.

For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25), Hausdorff and second countable, and every
absolutely minimal causality `C` with an isomorphic chart at each point over the family `E_{≥0}`
(`IsoChartsCoverDEC25 … massAModelCausality`; the natural causality is one), the theorems of
`Causal.SingularCauchy` are applied to `SFAManifolds.singularFlatAxioms`.

> In particular $J^\pm(\Sigma)$ are closed, $J^+(\Sigma)\cap J^-(\Sigma)=\Sigma$, and
> $J^+(\Sigma)$ is a neighbourhood of each of its points outside $\Sigma$.
> (`lem:Sigma_separe`, `ETT.tex:2067–2068`; `M` globally hyperbolic, `Σ` a Cauchy surface)

> Let $M$ be a globally hyperbolic singular flat spacetime, let $\Sigma$ be a Cauchy surface of
> $M$ and let $x,y\in J^+(\Sigma)\setminus \Sigma$. If
> $K^-(x)\cap J^+(\Sigma)\subset K^-(y)\cap J^+(\Sigma)$, then $x\leq y$. In particular
> $x\mapsto K^-(x)\cap J^+(\Sigma)$ is injective on $J^+(\Sigma)\setminus \Sigma$.
> (`cor:K_ordre_Sigma`, `ETT.tex:2082–2087`)

> Let $M$ and $N$ be globally hyperbolic singular flat spacetimes and let
> $\phi:M\rightarrow N$ be an injective $\mass{\geq0}$-morphism. The following are equivalent:
> (i) there exists a Cauchy surface $\Sigma$ of $M$ whose image $\phi(\Sigma)$ is a Cauchy
> surface of $N$; (ii) for every Cauchy surface $\Sigma$ of $M$, the image $\phi(\Sigma)$ is a
> Cauchy surface of $N$. (`lem:Cauchy_plongement_toutes`, `ETT.tex:1865–1872`)

## What is proved (no `sorry` in this file)

* `lem:Sigma_separe` (unmarked), its « In particular »: `sigma_separe` at every globally
  hyperbolic `M`, for every Cauchy surface; `sigma_separe_of_isCausal` at every causal `M`, with
  the time-reversed neighbourhood fact, `M = J⁺(Σ) ∪ J⁻(Σ)`, `J^±(Σ) ∖ Σ` open and `Σ` closed.
  A BTZ point in `J⁺(Σ) ∖ Σ` whenever `sing₀(M) ≠ ∅` (`exists_btz_Jplus_diff`).
* `cor:K_ordre_Sigma` (unmarked): `K_ordre_Sigma`, `SingularRowsK.K_ordre_Sigma` with its
  neighbourhood hypothesis `hS` discharged by `sigma_separe`, for every Cauchy surface.
* `lem:Cauchy_plongement_toutes` (unmarked): `cauchy_plongement_toutes`, for an injective
  `IsEMorphism` (DEC-17) into any Hausdorff causal `N`, with `hex` of
  `IsEMorphism.cauchy_plongement_toutes` from `SingularRowsGeroch.geroch_sing_i_imp_iii`;
  `cauchy_plongement_toutes_manifolds`, between two such manifolds, as printed.
* **The natural causality** (`IsAtlasCausalityDEC25`): `rows_of_isAtlasCausalityDEC25`.
* **Witnesses** (kb/0011), each conclusion out of this file's theorems: `nonvacuous_e0` (`E₀`, a
  Cauchy surface `S` from `SingularRowsGeroch.nonvacuous_e0_geroch`, a BTZ point
  `p ∈ J⁺(S) ∖ S` with `I⁻(p) = ∅` and `J⁺(S) ∈ 𝓝 p`: the BTZ case of step (3); the separation
  facts and `cor:K_ordre_Sigma` at `S`); `nonvacuous_e0_plongement` (the identity of `E₀`,
  `IsEMorphism.id`); `nonvacuous_e0_natural` (the natural causality of `E₀`); `nonvacuous_epi`
  (`E_π`, a massive line and no BTZ point).

## Hypothesis checklist

| paper | here |
|---|---|
| singular flat spacetime, `E_{≥0}`-manifold | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `rows_of_isAtlasCausalityDEC25` |
| — Hausdorff, second countable (« manifold », `ETT.tex:254`) | ✓ carried |
| — connected (l.1502) | ⚠ weakened: not used |
| `lem:Sigma_separe`: `M` globally hyperbolic | ✓ carried by `sigma_separe`; ⚠ weakened: causal (`sigma_separe_of_isCausal`) |
| `lem:Sigma_separe`: `ψ` of `theo:geroch_sing` | ⚠ weakened: not used |
| `cor:K_ordre_Sigma`: `M` globally hyperbolic, `Σ` a Cauchy surface | ✓ carried; nothing else (the former named `hS` is proved) |
| `lem:Cauchy_plongement_toutes`: `𝕄≥0`-morphism | ✓ as ruled (DEC-17): `IsEMorphism` |
| — `φ` injective, `M` globally hyperbolic | ✓ carried |
| — `N` a globally hyperbolic singular flat spacetime | ✓ carried by `cauchy_plongement_toutes_manifolds` (its `E_{≥0}` hypotheses unused); ⚠ weakened in `cauchy_plongement_toutes`: `N` Hausdorff, `D` causal |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** Every row rests on DEC-25 and the readings OQ-18 (the causality of a
  singular spacetime), OQ-34/OQ-35 (`E₀`) and OQ-82 (the group). `lem:Sigma_separe` is proved
  in its « In particular » only: the equalities `J^±(Σ) = ψ(Σ × ℝ_±)` need the flow of
  `lem:vecteur` (T-ett-geroch-split-flow). No row is marked.
* On `cor:K_ordre_Sigma`. Its proof (l.2090) takes from `lem:Sigma_separe` only that `J⁺(Σ)` is a
  neighbourhood of `x`. That holds with no `ψ`, so the corollary does not depend on
  `theo:geroch_sing`'s splitting. `SingularRowsK.K_ordre_Sigma_of_splitting` stays as it is.
* On `lem:Cauchy_plongement_toutes`. (i)⇒(ii) is `IsEMorphism.isCauchySurface_image`, which asks
  of `N` only Hausdorff and causal. (ii)⇒(i) needs a Cauchy surface of `M`, which
  `theo:geroch_sing` (i)⇒(iii) gives, `M` being globally hyperbolic.
* **Witnesses.** `E₀` has BTZ points only and `E_π` massive points only (`Causal.SFALocal`
  SCOPE). The Cauchy surfaces are existential (out of `theo:geroch_sing`); the BTZ point of
  `nonvacuous_e0` is on the axis, above the point where the axis meets `S`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.SingularCauchy` (part (a)), the strict `Causal.Remarks.SingularRowsK`
(`K_ordre_Sigma`, through it `Causal.Port.SFAManifolds`) and `Causal.Remarks.SingularRowsGeroch`
(`geroch_sing_i_imp_iii`, `nonvacuous_e0_geroch`, `nonvacuous_epi_geroch`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u v

namespace SingularRowsCauchy

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- `lem:Sigma_separe`'s « In particular » at every causal, Hausdorff, second countable
`E_{≥0}`-manifold. -/
theorem sigma_separe_of_isCausal [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {S : Set M} (hS : C.IsCauchySurface S) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      (∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
      (∀ y ∈ C.Jminus ⊤ S \ S, C.Jminus ⊤ S ∈ 𝓝 y) ∧
      (∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) ∧
      IsOpen (C.Jplus ⊤ S \ S) ∧ IsOpen (C.Jminus ⊤ S \ S) ∧ IsClosed S :=
  (SFAManifolds.singularFlatAxioms hmin hC).sigma_separe_of_isCausal hc hS

/-- `lem:Sigma_separe`'s « In particular » at every globally hyperbolic, Hausdorff, second
countable `E_{≥0}`-manifold. -/
theorem sigma_separe [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y :=
  (SFAManifolds.singularFlatAxioms hmin hC).sigma_separe hG hS

/-- A BTZ point in `J⁺(S) ∖ S`. -/
theorem exists_btz_Jplus_diff [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) {S : Set M} (hS : C.IsCauchySurface S)
    (hne : (SFALocal.sing M 0).Nonempty) :
    ∃ p ∈ SFALocal.sing M 0, p ∈ C.Jplus ⊤ S \ S :=
  (SFAManifolds.singularFlatAxioms hmin hC).exists_mem_sing_zero_Jplus_diff hc hS hne

/-- `cor:K_ordre_Sigma` for every Cauchy surface. -/
theorem K_ordre_Sigma [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) :
    (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
      C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
    InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S) :=
  SingularRowsK.K_ordre_Sigma hmin hC hG (sigma_separe hmin hC hG hS).2.2.2

/-- `lem:Cauchy_plongement_toutes`, `N` any Hausdorff causal spacetime. -/
theorem cauchy_plongement_toutes [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {N : Type v} [TopologicalSpace N] [T2Space N]
    {D : Causality N} (hD : D.IsCausal) {φ : M → N} (hφ : IsEMorphism C D φ)
    (hinj : Injective φ) :
    (∃ S : Set M, C.IsCauchySurface S ∧ D.IsCauchySurface (φ '' S)) ↔
      ∀ S : Set M, C.IsCauchySurface S → D.IsCauchySurface (φ '' S) :=
  hφ.cauchy_plongement_toutes hinj hD (SingularRowsGeroch.geroch_sing_i_imp_iii hmin hC hG)

/-- `lem:Cauchy_plongement_toutes` between two such manifolds. -/
theorem cauchy_plongement_toutes_manifolds [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {N : Type v} [TopologicalSpace N]
    [SingularGXStructure (Flat.isom 2) (Minkowski 2) N] [T2Space N] [SecondCountableTopology N]
    {D : Causality N} (_hminN : D.AbsolutelyMinimal)
    (_hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hGN : D.GloballyHyperbolic) {φ : M → N} (hφ : IsEMorphism C D φ) (hinj : Injective φ) :
    (∃ S : Set M, C.IsCauchySurface S ∧ D.IsCauchySurface (φ '' S)) ↔
      ∀ S : Set M, C.IsCauchySurface S → D.IsCauchySurface (φ '' S) :=
  cauchy_plongement_toutes hmin hC hG hGN.1 hφ hinj

/-! ### The natural causality -/

/-- The three rows for the natural causality. -/
theorem rows_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (C.IsCausal → ∀ S : Set M, C.IsCauchySurface S →
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
        (∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
        (∀ y ∈ C.Jminus ⊤ S \ S, C.Jminus ⊤ S ∈ 𝓝 y) ∧
        (∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) ∧
        IsOpen (C.Jplus ⊤ S \ S) ∧ IsOpen (C.Jminus ⊤ S \ S) ∧ IsClosed S) ∧
    (C.GloballyHyperbolic → ∀ S : Set M, C.IsCauchySurface S →
      (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
        C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
      InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S)) ∧
    (C.GloballyHyperbolic → ∀ {N : Type v} [TopologicalSpace N] [T2Space N] {D : Causality N},
      D.IsCausal → ∀ {φ : M → N}, IsEMorphism C D φ → Injective φ →
        ((∃ S : Set M, C.IsCauchySurface S ∧ D.IsCauchySurface (φ '' S)) ↔
          ∀ S : Set M, C.IsCauchySurface S → D.IsCauchySurface (φ '' S))) := by
  obtain ⟨hmin, hC'⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hC
  exact ⟨fun hc _ hS => sigma_separe_of_isCausal hmin hC' hc hS,
    fun hG _ hS => K_ordre_Sigma hmin hC' hG hS,
    fun hG _ _ _ _ hD _ hφ hinj => cauchy_plongement_toutes hmin hC' hG hD hφ hinj⟩

end Manifold

/-! ### Witnesses (kb/0011) -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- Non-vacuity at `E₀`, with a BTZ point in `J⁺(S) ∖ S`. -/
theorem nonvacuous_e0 :
    ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
      ∃ p ∈ SFALocal.sing E0 0, p ∈ E0.causality.Jplus ⊤ S \ S ∧
        E0.causality.Iminus ⊤ {p} = ∅ ∧ E0.causality.Jplus ⊤ S ∈ 𝓝 p ∧
        IsClosed (E0.causality.Jplus ⊤ S) ∧ IsClosed (E0.causality.Jminus ⊤ S) ∧
        E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ S = S ∧
        (∀ x ∈ E0.causality.Jplus ⊤ S \ S, ∀ y ∈ E0.causality.Jplus ⊤ S \ S,
          E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S ⊆
            E0.causality.Kminus ⊤ {y} ∩ E0.causality.Jplus ⊤ S → E0.causality.le ⊤ x y) ∧
        InjOn (fun x => E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S)
          (E0.causality.Jplus ⊤ S \ S) := by
  obtain ⟨hmin, hC, -, hG, -, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_e0_geroch
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨p, hp0, hp⟩ := exists_btz_Jplus_diff hmin hC hG.1 hS hne
  obtain ⟨h1, h2, h3, h4⟩ := sigma_separe hmin hC hG hS
  obtain ⟨h5, h6⟩ := K_ordre_Sigma hmin hC hG hS
  exact ⟨S, hS, p, hp0, hp, SFALocal.Iminus_eq_empty hmin hC p hp0, h4 p hp, h1, h2, h3, h5, h6⟩

/-- `lem:Cauchy_plongement_toutes` at the identity of `E₀`. -/
theorem nonvacuous_e0_plongement :
    (∃ S : Set E0, E0.causality.IsCauchySurface S ∧ E0.causality.IsCauchySurface (id '' S)) ∧
      ∀ S : Set E0, E0.causality.IsCauchySurface S → E0.causality.IsCauchySurface (id '' S) := by
  obtain ⟨hmin, hC, -, hG, -, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_e0_geroch
  have h := cauchy_plongement_toutes_manifolds hmin hC hG hmin hC hG IsEMorphism.id injective_id
  have hi : ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
      E0.causality.IsCauchySurface (id '' S) := ⟨S, hS, by rw [image_id]; exact hS⟩
  exact ⟨hi, h.1 hi⟩

/-- Non-vacuity of `rows_of_isAtlasCausalityDEC25` at `E₀` with its natural causality over the
family (`EModelsBPrime.massA_dec25_models_e0_sing`): a Cauchy surface (out of
`SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25`), the separation facts and
`lem:Cauchy_plongement_toutes` at the identity, out of the assembly. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        IsClosed (E0.causality.Jplus ⊤ S) ∧ IsClosed (E0.causality.Jminus ⊤ S) ∧ IsClosed S ∧
        E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ S = S ∧
        ∀ S' : Set E0, E0.causality.IsCauchySurface S' →
          E0.causality.IsCauchySurface (id '' S') := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨hr1, -, hr3⟩ := rows_of_isAtlasCausalityDEC25 hcov hC
  obtain ⟨S, hS⟩ := SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 hcov hC
    E0.globallyHyperbolic
  obtain ⟨h1, h2, h3, -, -, -, -, -, h9⟩ := hr1 E0.globallyHyperbolic.1 S hS
  have hpl := hr3 E0.globallyHyperbolic E0.globallyHyperbolic.1 IsEMorphism.id injective_id
  exact ⟨hcov, hC, S, hS, h1, h2, h9, h3, hpl.1 ⟨S, hS, by rw [image_id]; exact hS⟩⟩

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- Non-vacuity at `E_π` (a massive line, no BTZ point: the regular branch of step (3) at every
point), out of `sigma_separe`, with a Cauchy surface from
`SingularRowsGeroch.nonvacuous_epi_geroch`. -/
theorem nonvacuous_epi :
    SFALocal.sing (Massive Real.pi) 0 = ∅ ∧ (SFALocal.sing (Massive Real.pi) Real.pi).Nonempty ∧
      ∃ S : Set (Massive Real.pi), (massive Real.pi).IsCauchySurface S ∧
        IsClosed ((massive Real.pi).Jplus ⊤ S) ∧ IsClosed ((massive Real.pi).Jminus ⊤ S) ∧
        (massive Real.pi).Jplus ⊤ S ∩ (massive Real.pi).Jminus ⊤ S = S ∧
        ∀ y ∈ (massive Real.pi).Jplus ⊤ S \ S, (massive Real.pi).Jplus ⊤ S ∈ 𝓝 y := by
  obtain ⟨hmin, hC, -, hG, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_epi_geroch
  obtain ⟨-, -, -, hne, h0⟩ := SFALocal.nonvacuous_epi
  exact ⟨h0, hne, S, hS, sigma_separe hmin hC hG hS⟩

end WitnessEPi

end SingularRowsCauchy

end Causal
