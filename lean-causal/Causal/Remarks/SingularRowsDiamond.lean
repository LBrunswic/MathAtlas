import Causal.Flat.CBG
import Causal.Remarks.SingularRowsCauchy

/-!
# Diamonds and reachable pasts through a Cauchy extension, at every pair of `E_{≥0}`-manifolds

Target `T-ett-diamant-rows`. Cited, all unmarked (SCOPE):
`lem:image_diamant` — `ETT.tex:2024`, with no hypothesis left;
`lem:passe_pgcd` — `ETT.tex:2042`, with no hypothesis left, both explicit forms with
`Sing = sing₀(N)`.

For singular `(Isom(𝐌³), 𝐌³)`-manifolds `M`, `N` (DEC-25), Hausdorff and second countable, each
with an absolutely minimal causality having an isomorphic chart at each point over the family
`E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`; the natural causality is one), the four
theorems of `Causal.CauchyDiamond` are applied with every named hypothesis proved:
`J⁺(Σ) ∩ J⁻(p)` compact, `M = J⁺(Σ) ∪ J⁻(Σ)`, `N` causally arc-connected, curves of `N` extend,
and `prop:K_calcul`'s two values of `K⁻` on `sing₀(N)`.

> Let $M$ be a globally hyperbolic singular flat spacetime with Cauchy surface $\Sigma$, let
> $i:M\rightarrow N$ be a Cauchy extension and let $p\in J^+_M(\Sigma)$. Then
> $$i\left(J_M(\Sigma,p)\right)=J_N\left(i(\Sigma),i(p)\right).$$
> (`lem:image_diamant`, `ETT.tex:2025–2027`)

> Since $M$ is globally hyperbolic $K$ is compact, hence so is $K'$ (`ETT.tex:2032–2033`)

> Let $M$ be a globally hyperbolic singular flat spacetime with Cauchy surface $\Sigma$, let
> $i:M\rightarrow N$ be a Cauchy extension and let $p\in \partial i(M)\cap J^+\left(i(\Sigma)\right)$.
> Then $$K^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M);$$ explicitly,
> $I^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M)$ if $p\notin \sing_0(N)$, and
> $J_N\left(i(\Sigma),p\right)\setminus \{p\}\subset i(M)$ if $p\in \sing_0(N)$.
> (`lem:passe_pgcd`, `ETT.tex:2043–2048`)

## What is proved (no `sorry` in this file)

* **`J⁻` of open sets is open** (model-free): `Causality.isOpen_Jminus_of_pushUp`, under push-up
  and `Z⁺ = M`; hence `SingularFlatAxioms.isOpen_Jminus`.
* **`J⁺(Σ) ∩ J⁻(p)` is compact** for every Cauchy surface `Σ` and every `p`:
  `SingularFlatAxioms.isCompact_Jplus_inter_Jminus` (globally hyperbolic, `τ` a hypothesis),
  `…_of_modelMeasures`; at `M`, with no hypothesis left, `isCompact_Jplus_inter_Jminus` and
  `isCompact_Jplus_inter_Jminus_of_isAtlasCausalityDEC25`.
* `lem:image_diamant` (unmarked): `image_diamant`, for `p ∈ J⁺(Σ)`; `diamond_subset_range`, at
  every point of `M`.
* `lem:passe_pgcd` (unmarked): `passe_pgcd_printed`, as printed (`p ∈ ∂ i(M) ∩ J⁺(i Σ)`, the
  inclusion and both explicit forms); `passe_pgcd` and `passe_pgcd_explicit`, for every
  `p ∈ closure (range i)`, which contains `∂ i(M) ∩ J⁺(i Σ)`.
* **The natural causalities** (`IsAtlasCausalityDEC25`): `rows_of_isAtlasCausalityDEC25`.
* **Witnesses** (kb/0011), each conclusion out of this file's theorems: `nonvacuous_e0` (the
  identity of `E₀`, a Cauchy surface `S`, a BTZ point `p ∈ J⁺(S) ∖ S` with `I⁻(p) = ∅`:
  compactness, `lem:image_diamant`, the BTZ branch of `lem:passe_pgcd`); `nonvacuous_e0_natural`;
  `nonvacuous_epi` (`E_π`, the regular branch at a point of `S`).

## Hypothesis checklist

| paper | here |
|---|---|
| singular flat spacetime, `E_{≥0}`-manifold (`M` and `N`) | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) _]`, the causality absolutely minimal with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `rows_of_isAtlasCausalityDEC25` |
| — Hausdorff, second countable (« manifold », `ETT.tex:254`) | ✓ carried, for `M` and `N` |
| — connected (l.1502) | ⚠ weakened: not used |
| `M` globally hyperbolic, `Σ` a Cauchy surface of `M` | ✓ carried (`IsCauchyEmbedding.globallyHyperbolic_source`) |
| `i` a Cauchy extension (`def:cauchy_embedding_cauchy_extension`) | ✓ as ruled (DEC-17): `IsCauchyEmbedding` (both GH, injective `IsEMorphism`, some Cauchy surface onto one) |
| `K = J_M(Σ, p)` compact, « since `M` is globally hyperbolic » | ✓ proved (`isCompact_Jplus_inter_Jminus`), for every `p`, by a route the paper does not give (finding) |
| `M = J⁺(Σ) ∪ J⁻(Σ)` (used at l.2036–2037) | ✓ proved, T1 and second countable only (finding) |
| `p ∈ J⁺_M(Σ)` (image_diamant) | ✓ carried |
| `p ∈ ∂ i(M) ∩ J⁺(i Σ)` (passe_pgcd) | ✓ carried in `passe_pgcd_printed`; ⚠ weakened in `passe_pgcd`: `p ∈ closure (range i)` |
| `prop:K_calcul` on `sing₀(N)` | ✓ proved (`SFABTZ.K_calcul`, `N` causal) |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** Every row rests on DEC-25 and the readings OQ-18 (the causality of a
  singular spacetime), OQ-34/OQ-35 (`E₀`) and OQ-82 (the group). No row is marked.
* `J_M(Σ, p)` is read `J⁺(Σ) ∩ J⁻(p)`, as in `Causal.CauchyDiamond`; `∂ i(M)` is
  `frontier (range i)` in `N`; `i(M)` is `range i`.
* **The compactness** of `J⁺(Σ) ∩ J⁻(p)` is not the paper's argument: `J⁻(W)` is open for every
  open `W` (`Z⁺ = M` and push-up), so `CBGCompact`'s Zorn on time graphs gives `J⁻(p) ∩ Σ`
  compact, with `J^±(Σ)` closed (`SingularFlatAxioms.sigma_separe`) and a continuous `τ`
  strictly increasing along `≤` (the Geroch time of `SingularRowsGeroch.geroch_sing_i_imp_ii`);
  then `CBG.isCompact_Jplus_inter_Jminus_of_isCompact`. At the `SingularFlatAxioms` level `τ`
  is a hypothesis (or `ModelMeasures`). The time-reversed `J⁻(Σ) ∩ J⁺(p)` is not attempted
  here (`lem:image_diamant` does not use it): the dual of the openness argument needs `Z⁻ = M`,
  which fails at a BTZ point (`mem_Zminus_iff`). It holds by another route, `J⁺` of open sets
  being open at BTZ points too: `Causal.SingularRowsDiamondPast.isCompact_Jminus_inter_Jplus`.
* **Witnesses** (kb/0011) at `E₀` and `E_π` with the identity: `range id` is everything, so the
  hypothesis of `passe_pgcd` is met only at points of `range i`, where its conclusion is trivial,
  and that of `passe_pgcd_printed` (`frontier univ = ∅`) never, as for `Causal.CauchyDiamond`'s
  own witnesses. No Cauchy extension that is not onto is built here; one is in
  `Causal.Remarks.SingularRowsCauchyExt` (`cauchyExtension`), with witnesses off the identity.
* **Findings.** (1) `ETT.tex:2032–2033`: « since `M` is globally hyperbolic `K` is compact » is a
  gap in the argument (`def:globally_hyperbolic` gives compact diamonds between two points); the
  compactness holds at every Hausdorff, second countable `E_{≥0}`-manifold, by the route above.
  (2) `ETT.tex:2036–2037`: « it stays above `Σ` » uses `M = J⁺(Σ) ∪ J⁻(Σ)`, which holds on every
  T1, second countable space (`IsCauchySurface.cover_of_t1_secondCountable`), with no
  `lem:Sigma_separe`; and the acausality of `i(Σ)` in `N`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.Flat.CBG` (`CBG.isCompact_Jplus_inter_Jminus_of_isCompact`, and through it
`Causal.Flat.CBGCompact`) and `Causal.Remarks.SingularRowsCauchy` (through it
`Causal.SingularCauchy`, `Causal.CauchyDiamond`, `Causal.Remarks.SingularRowsGeroch`).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u v

namespace Causality

section General

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **`J⁻(W)` is open for every open `W`** in a spacetime with push-up whose points are all
strongly tarentin in the future (`Z⁺ = M`): for `x ≤ w ∈ W`, some `w' ∈ I⁺(w) ∩ W`, push-up gives
`x ≪ w'`, and the open `I⁻(w')` lies in `J⁻(W)`. -/
theorem isOpen_Jminus_of_pushUp (hP : C.PushUp) (hZ : ∀ p, p ∈ C.Zplus) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jminus ⊤ W) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hw, hxw⟩
  obtain ⟨w', hw'I, hw'W⟩ := hZ w W (hW.mem_nhds hw)
  have hww' : C.lt ⊤ w w' := Precausality.mem_Iplus_singleton.1 hw'I
  have hx : x ∈ C.Iminus ⊤ {w'} :=
    (hP ⊤ w').1.2 ⟨w, Precausality.mem_Iminus_singleton.2 hww', hxw⟩
  exact Filter.mem_of_superset (C.isOpen_Iminus.mem_nhds hx) fun y hy =>
    ⟨w', hw'W, C.le_of_lt (Precausality.mem_Iminus_singleton.1 hy)⟩

end General

section SFA

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {sing : ℝ → Set M}

/-- Under `SingularFlatAxioms`, `J⁻(W)` is open for every open `W` (`pushUp`, `mem_Zplus`). -/
theorem SingularFlatAxioms.isOpen_Jminus (h : C.SingularFlatAxioms sing) {W : Set M}
    (hW : IsOpen W) : IsOpen (C.Jminus ⊤ W) :=
  isOpen_Jminus_of_pushUp h.pushUp h.mem_Zplus hW

/-- `J⁻(p) ∩ S` is compact for a Cauchy surface `S` of a globally hyperbolic `SingularFlatAxioms`
spacetime with a continuous `τ` strictly increasing along `≤`. -/
theorem SingularFlatAxioms.isCompact_Jminus_inter_of_isCauchySurface
    (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y) {S : Set M} (hS : C.IsCauchySurface S)
    (p : M) : IsCompact (C.Jminus ⊤ {p} ∩ S) := by
  haveI := h.t2
  haveI := h.secondCountable
  haveI := h.locallyCompact
  obtain ⟨h1, h2, -, -⟩ := h.sigma_separe hG hS
  exact GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface h.tarentin hG
    h.causallyArcConnected hτc hτ (fun _ hW => h.isOpen_Jminus hW) hS
    (hS.isAcausal_of_t1_secondCountable h.causallyArcConnected) h1 h2 p

/-- **`J⁺(S) ∩ J⁻(p)` is compact** for a Cauchy surface `S` of a globally hyperbolic
`SingularFlatAxioms` spacetime with a continuous `τ` strictly increasing along `≤`. -/
theorem SingularFlatAxioms.isCompact_Jplus_inter_Jminus (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) {τ : M → ℝ} (hτc : Continuous τ)
    (hτ : ∀ x y, C.le ⊤ x y → x ≠ y → τ x < τ y) {S : Set M} (hS : C.IsCauchySurface S)
    (p : M) : IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) := by
  haveI := h.t2
  exact CBG.isCompact_Jplus_inter_Jminus_of_isCompact h.tarentin hG (h.sigma_separe hG hS).1
    (h.isCompact_Jminus_inter_of_isCauchySurface hG hτc hτ hS p)

/-- The same, with `τ` out of the model measures (`SingularFlatAxioms.geroch_sing_i_imp_ii`). -/
theorem SingularFlatAxioms.isCompact_Jplus_inter_Jminus_of_modelMeasures [MeasurableSpace M]
    [BorelSpace M] (h : C.SingularFlatAxioms sing) (hM : C.ModelMeasures)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) := by
  obtain ⟨T, hT, hTs⟩ := h.geroch_sing_i_imp_ii hM hG
  exact h.isCompact_Jplus_inter_Jminus hG hT.1.continuous hTs hS p

end SFA

end Causality

namespace SingularRowsDiamond

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **`J⁺(S) ∩ J⁻(p)` is compact** at every globally hyperbolic, Hausdorff, second countable
`E_{≥0}`-manifold, for every Cauchy surface `S` and every `p` (`ETT.tex:2032–2033`). -/
theorem isCompact_Jplus_inter_Jminus [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) := by
  obtain ⟨T, hT, hTs⟩ := SingularRowsGeroch.geroch_sing_i_imp_ii hmin hC hG
  exact (SFAManifolds.singularFlatAxioms hmin hC).isCompact_Jplus_inter_Jminus hG
    hT.1.continuous hTs hS p

variable {N : Type v} [TopologicalSpace N] [SingularGXStructure (Flat.isom 2) (Minkowski 2) N]
  {D : Causality N} {i : M → N}

/-- `lem:image_diamant` at every pair of Hausdorff, second countable `E_{≥0}`-manifolds:
`i(J⁺(S) ∩ J⁻(p)) = J⁺(i S) ∩ J⁻(i p)` for `p ∈ J⁺(S)`, no hypothesis left. -/
theorem image_diamant [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hminN : D.AbsolutelyMinimal)
    (hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) {p : M}
    (hp : p ∈ C.Jplus ⊤ S) :
    i '' (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) = D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i p} :=
  hi.image_diamant hS (fun x => hS.cover_of_t1_secondCountable x)
    (SFAManifolds.singularFlatAxioms hminN hCN).causallyArcConnected
    (Causality.curvesExtend_of_t1_secondCountable D) hp
    (isCompact_Jplus_inter_Jminus hmin hC hi.globallyHyperbolic_source hS p)

/-- The diamond from `i(S)` to the image of any point of `M` lies in `i(M)`. -/
theorem diamond_subset_range [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hminN : D.AbsolutelyMinimal)
    (hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) (m : M) :
    D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i m} ⊆ range i :=
  hi.diamond_subset_range hS (fun x => hS.cover_of_t1_secondCountable x)
    (SFAManifolds.singularFlatAxioms hminN hCN).causallyArcConnected
    (Causality.curvesExtend_of_t1_secondCountable D)
    (fun m _ => isCompact_Jplus_inter_Jminus hmin hC hi.globallyHyperbolic_source hS m) m

/-- `lem:passe_pgcd`, `K⁻_N(p) ∩ J⁺(i S) ⊆ i(M)`, for every `p` in the closure of `i(M)` (the
paper's `p ∈ ∂ i(M) ∩ J⁺(i S)` is a special case: `passe_pgcd_printed`). -/
theorem passe_pgcd [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hminN : D.AbsolutelyMinimal)
    (hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) {p : N}
    (hp : p ∈ closure (range i)) :
    D.Kminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i :=
  hi.passe_pgcd hS (fun x => hS.cover_of_t1_secondCountable x)
    (SFAManifolds.singularFlatAxioms hminN hCN).causallyArcConnected
    (Causality.curvesExtend_of_t1_secondCountable D)
    (fun m _ => isCompact_Jplus_inter_Jminus hmin hC hi.globallyHyperbolic_source hS m) hp

/-- The two explicit forms of `lem:passe_pgcd`, with `Sing = sing₀(N)`, for every `p` in the
closure of `i(M)`. -/
theorem passe_pgcd_explicit [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hminN : D.AbsolutelyMinimal)
    (hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) {p : N}
    (hp : p ∈ closure (range i)) :
    (p ∉ SFALocal.sing N 0 → D.Iminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i) ∧
      (p ∈ SFALocal.sing N 0 → (D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {p}) \ {p} ⊆ range i) :=
  hi.passe_pgcd_explicit hS (fun x => hS.cover_of_t1_secondCountable x)
    (SFAManifolds.singularFlatAxioms hminN hCN).causallyArcConnected
    (Causality.curvesExtend_of_t1_secondCountable D)
    (fun m _ => isCompact_Jplus_inter_Jminus hmin hC hi.globallyHyperbolic_source hS m)
    (SFALocal.sing N 0) (fun q hq => ((SFABTZ.K_calcul hminN hCN).1 q hq).2)
    (fun q hq => (SFABTZ.K_calcul hminN hCN).2.2 hi.globallyHyperbolic_target.1 q hq) hp

/-- `lem:passe_pgcd` **as printed**: `p ∈ ∂ i(M) ∩ J⁺(i S)`; the inclusion and both explicit
forms, `Sing = sing₀(N)`. -/
theorem passe_pgcd_printed [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hminN : D.AbsolutelyMinimal)
    (hCN : IsoChartsCoverDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) {p : N}
    (hp : p ∈ frontier (range i) ∩ D.Jplus ⊤ (i '' S)) :
    D.Kminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i ∧
      (p ∉ SFALocal.sing N 0 → D.Iminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i) ∧
      (p ∈ SFALocal.sing N 0 → (D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {p}) \ {p} ⊆ range i) := by
  have hcl : p ∈ closure (range i) := frontier_subset_closure hp.1
  exact ⟨passe_pgcd hmin hC hminN hCN hi hS hcl, passe_pgcd_explicit hmin hC hminN hCN hi hS hcl⟩

/-! ### The natural causality -/

/-- The rows for the natural causalities of `M` and `N`. -/
theorem rows_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] (hcov : SFALocal.MassACovered M)
    (hCM : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hcovN : SFALocal.MassACovered N)
    (hCN : IsAtlasCausalityDEC25 (Flat.isom 2) D (minkowski 2) massAModelCausality)
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S) :
    (∀ p, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p})) ∧
      (∀ p ∈ C.Jplus ⊤ S,
        i '' (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) = D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i p}) ∧
      (∀ m, D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i m} ⊆ range i) ∧
      (∀ p ∈ closure (range i), D.Kminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i ∧
        (p ∉ SFALocal.sing N 0 → D.Iminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i) ∧
        (p ∈ SFALocal.sing N 0 → (D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {p}) \ {p} ⊆ range i)) := by
  obtain ⟨hmin, hC⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hCM
  obtain ⟨hminN, hCN'⟩ := SFALocal.of_isAtlasCausalityDEC25 hcovN hCN
  exact ⟨fun p => isCompact_Jplus_inter_Jminus hmin hC hi.globallyHyperbolic_source hS p,
    fun _ hp => image_diamant hmin hC hminN hCN' hi hS hp,
    fun m => diamond_subset_range hmin hC hminN hCN' hi hS m,
    fun _ hp => ⟨passe_pgcd hmin hC hminN hCN' hi hS hp,
      passe_pgcd_explicit hmin hC hminN hCN' hi hS hp⟩⟩

/-- The compactness of `J⁺(S) ∩ J⁻(p)` for the natural causality of a globally hyperbolic `M`. -/
theorem isCompact_Jplus_inter_Jminus_of_isAtlasCausalityDEC25 [T2Space M]
    [SecondCountableTopology M] (hcov : SFALocal.MassACovered M)
    (hCM : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) := by
  obtain ⟨hmin, hC⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hCM
  exact isCompact_Jplus_inter_Jminus hmin hC hG hS p

end Manifold

/-! ### Witnesses (kb/0011) -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **Non-vacuity at `E₀`** with the identity, a Cauchy extension: a Cauchy surface `S` and a BTZ
point `p ∈ J⁺(S) ∖ S` with `I⁻(p) = ∅`, where `J⁺(S) ∩ J⁻(p)` is compact, `lem:image_diamant`
holds and the BTZ branch of `lem:passe_pgcd` applies, out of this file's theorems. At the
identity the inclusions themselves are trivial (`range id` is everything): the witness shows that
the hypotheses can all be met, a BTZ point and the compactness there included. -/
theorem nonvacuous_e0 :
    IsCauchyEmbedding E0.causality E0.causality id ∧
      (∀ W : Set E0, IsOpen W → IsOpen (E0.causality.Jminus ⊤ W)) ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        ∃ p ∈ SFALocal.sing E0 0, p ∈ E0.causality.Jplus ⊤ S \ S ∧
          E0.causality.Iminus ⊤ {p} = ∅ ∧
          IsCompact (E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ {p}) ∧
          id '' (E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ {p}) =
            E0.causality.Jplus ⊤ (id '' S) ∩ E0.causality.Jminus ⊤ {id p} ∧
          E0.causality.Kminus ⊤ {p} ∩ E0.causality.Jplus ⊤ (id '' S) ⊆ range id ∧
          (E0.causality.Jplus ⊤ (id '' S) ∩ E0.causality.Jminus ⊤ {p}) \ {p} ⊆ range id := by
  obtain ⟨hmin, hC, -, hG, -, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_e0_geroch
  have hi : IsCauchyEmbedding E0.causality E0.causality id :=
    ⟨hG, hG, IsEMorphism.id, injective_id, ⟨S, hS, by rw [image_id]; exact hS⟩⟩
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨p, hp0, hp⟩ := SingularRowsCauchy.exists_btz_Jplus_diff hmin hC hG.1 hS hne
  have hcl : p ∈ closure (range (id : E0 → E0)) := subset_closure ⟨p, rfl⟩
  exact ⟨hi, fun _ hW => (SFAManifolds.singularFlatAxioms hmin hC).isOpen_Jminus hW, S, hS, p,
    hp0, hp, SFALocal.Iminus_eq_empty hmin hC p hp0,
    isCompact_Jplus_inter_Jminus hmin hC hG hS p, image_diamant hmin hC hmin hC hi hS hp.1,
    passe_pgcd hmin hC hmin hC hi hS hcl, (passe_pgcd_explicit hmin hC hmin hC hi hS hcl).2 hp0⟩

/-- **Non-vacuity of the natural forms at `E₀`** (`EModelsBPrime.massA_dec25_models_e0_sing`): a
Cauchy surface out of `SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25`, the
identity a Cauchy extension, and the first two rows out of `rows_of_isAtlasCausalityDEC25`. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        (∀ p, IsCompact (E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ {p})) ∧
        ∀ p ∈ E0.causality.Jplus ⊤ S,
          id '' (E0.causality.Jplus ⊤ S ∩ E0.causality.Jminus ⊤ {p}) =
            E0.causality.Jplus ⊤ (id '' S) ∩ E0.causality.Jminus ⊤ {id p} := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨S, hS⟩ := SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 hcov hC
    E0.globallyHyperbolic
  have hi : IsCauchyEmbedding E0.causality E0.causality id :=
    ⟨E0.globallyHyperbolic, E0.globallyHyperbolic, IsEMorphism.id, injective_id,
      ⟨S, hS, by rw [image_id]; exact hS⟩⟩
  obtain ⟨h1, h2, -, -⟩ := rows_of_isAtlasCausalityDEC25 hcov hC hcov hC hi hS
  exact ⟨hcov, hC, S, hS, h1, h2⟩

end WitnessE0

section WitnessEPi

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

/-- **Non-vacuity at `E_π`** (no BTZ point) with the identity: the regular branch of
`lem:passe_pgcd` at a point of a Cauchy surface. -/
theorem nonvacuous_epi :
    IsCauchyEmbedding (massive Real.pi) (massive Real.pi) id ∧
      ∃ S : Set (Massive Real.pi), (massive Real.pi).IsCauchySurface S ∧
        ∃ p ∈ S, p ∉ SFALocal.sing (Massive Real.pi) 0 ∧
          IsCompact ((massive Real.pi).Jplus ⊤ S ∩ (massive Real.pi).Jminus ⊤ {p}) ∧
          (massive Real.pi).Iminus ⊤ {p} ∩ (massive Real.pi).Jplus ⊤ (id '' S) ⊆ range id := by
  obtain ⟨hmin, hC, -, hG, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_epi_geroch
  obtain ⟨-, -, -, ⟨x, -⟩, h0⟩ := SFALocal.nonvacuous_epi
  have hi : IsCauchyEmbedding (massive Real.pi) (massive Real.pi) id :=
    ⟨hG, hG, IsEMorphism.id, injective_id, ⟨S, hS, by rw [image_id]; exact hS⟩⟩
  obtain ⟨σ, hσ⟩ : S.Nonempty := by
    rcases hS.cover_of_t1_secondCountable x with ⟨σ, hσ, -⟩ | ⟨σ, hσ, -⟩ <;> exact ⟨σ, hσ⟩
  have hσ0 : σ ∉ SFALocal.sing (Massive Real.pi) 0 := by rw [h0]; exact notMem_empty σ
  have hcl : σ ∈ closure (range (id : Massive Real.pi → Massive Real.pi)) :=
    subset_closure ⟨σ, rfl⟩
  exact ⟨hi, S, hS, σ, hσ, hσ0, isCompact_Jplus_inter_Jminus hmin hC hG hS σ,
    (passe_pgcd_explicit hmin hC hmin hC hi hS hcl).1 hσ0⟩

end WitnessEPi

end SingularRowsDiamond

end Causal
