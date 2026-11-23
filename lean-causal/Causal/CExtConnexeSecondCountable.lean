import Causal.CurvesExtendSecondCountable
import Causal.CBG.Injective
import Causal.CorrespondingPoints
import Causal.CauchySeparation

/-!
# The Cauchy-embedding lemmas on second countable spaces, without their curve hypotheses

Programme target `T-abs-c-ext-connexe-second-countable` (`programme/roadmap.toml`; layer 1: it
imports `Causal.CurvesExtendSecondCountable`, `Causal.CBG.Injective`, `Causal.CorrespondingPoints`
and `Causal.CauchySeparation`, all ETT-layer; no model; no metric notion in a statement). **No label
is marked** (SCOPE). The labels served, unmarked: `lem:C_ext_connexe` — `ETT.tex:1932`;
`lem:image_diamant` — `ETT.tex:2024`; `lem:passe_pgcd` — `ETT.tex:2042`; `lem:Sigma_separe` —
`ETT.tex:2062`; Sbierski 1309.7591 `mghdcor:welldefined` (Cor 3.2, `Maximal_GHD2.tex:452`),
`mghdlem:IsoDiffeo` (Lemma 3.3, `:463`), `mghdthm:ExMCGHD` (Thm 3.4, `:485`).

Each library form of these carries the extension of curves as a named hypothesis (kb/0012): `hDext :
D.CurvesExtend` on the target `N`, or `hext : C.CurvesExtendOn B` on an open `B`. On a T1, second
countable space it is a theorem (`Causality.curvesExtend_of_t1_secondCountable`,
`curvesExtendOn_of_t1_secondCountable`, kb/0142), and DEC-190 drops it everywhere; ETT's
spacetimes are Hausdorff and second countable:

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

> Let $M$ be a connected globally hyperbolic singular flat spacetime and let
> $\phi:M\rightarrow N$ be a Cauchy extension. If $A$ and $B$ are open subsets of $N$ containing
> $\phi(M)$ and such that the inclusions $\phi(M)\rightarrow A$ and $\phi(M)\rightarrow B$ are
> Cauchy embeddings, then $A\cap B$ is connected. (`ETT.tex:1933–1936`)

> let $i:M\rightarrow N$ be a Cauchy extension and let $p\in J^+_M(\Sigma)$. Then
> $i\left(J_M(\Sigma,p)\right)=J_N\left(i(\Sigma),i(p)\right)$. (`ETT.tex:2026–2027`)

> let $p\in \partial i(M)\cap J^+\left(i(\Sigma)\right)$. Then
> $K^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M)$ (`ETT.tex:2044–2046`)

> Then $$J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)\qquad\text{and}\qquad
> J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right).$$ In particular $J^\pm(\Sigma)$ are closed,
> $J^+(\Sigma)\cap J^-(\Sigma)=\Sigma$, and $J^+(\Sigma)$ is a neighbourhood of each of its points
> outside $\Sigma$. (`ETT.tex:2065–2068`)

> Note that $\gamma$ cannot meet $\iota(\overline{M})$ more than once, since $\gamma$ is also a
> segment of an inextendible timelike curve in $M$ - and $M$ is globally hyperbolic.
> (Sbierski, proof of Thm 3.4, `Maximal_GHD2.tex:502`)

## What is proved (no `sorry`)

Each theorem is a library theorem with its curve hypothesis discharged by one term and the
instance `[SecondCountableTopology _]` added (`[T1Space M]` where the original has no separation
axiom); its name is the original's suffixed `_of_secondCountable` (`_of_t1_secondCountable`).
Two are not of that form: `eq_of_mem_image_inter_of_secondCountable` also drops `hDac`, and
`sigma_separe_of_t1_secondCountable` asks `Σ` Cauchy in the causally arc-connected `M` in place of
`Σ` acausal, so it is a corollary of `Causality.sigma_separe`, nearer the paper but narrower than
the library form (the row keeps `sigma_separe`).

0. A Cauchy embedding is an open embedding (`IsCauchyEmbedding.isOpenEmbedding`), so `M` inherits
   T2 (T1) and second countability from `N` (`.t2Space`, `.secondCountableTopology`); hence
   `M = J⁺(Σ) ∪ J⁻(Σ)` from instances on `N` only (`.mem_Jplus_union_Jminus_of_secondCountable`).
1. `lem:C_ext_connexe` (`Causal.CBG.CausalConvex`, `Causal.SubExtension`):
   `exists_inextensible_inf`, `isPreconnected_inf`, `c_ext_connexe_of_isConnected`,
   `c_ext_connexe'`, `isPreconnected_inf_of_preconnectedSpace`, `c_ext_connexe_of_connectedSpace`,
   `isCauchySurfaceOn_inf_iff`, `inf_causallyConvexIn` without `hDext`; `eq_of_mem_image_inter`
   without `hDext` and without `hDac`. `c_ext_connexe_of_connectedSpace_of_secondCountable` has no
   named hypothesis left.
2. Sbierski Lemma 3.3 (`Causal.CBG.Injective`): `CBG.injective_of_mapsTo_cauchy`,
   `CBG.sbierski_lemma_3_3` without `hDext`.
3. Thm 3.4's union and convexity (`Causal.CBG.CausalConvex`):
   `Causality.causallyConvexIn_of_isCauchySurfaceOn`, `IsCauchyInclusion.causallyConvexIn`,
   `Causality.isCauchySurfaceOn_iSup`, `isCauchyInclusion_iSup_of_common`, `isCauchyInclusion_iSup`,
   `isCauchyInclusion_sSup` without `hext`.
4. `lem:Sigma_separe` (`Causal.CauchyDiamond`, `Causal.CorrespondingPoints`): `sigma_separe` with
   `Σ` a Cauchy surface of the causally arc-connected `M` in place of `Σ` acausal;
   `Jplus_mem_nhds_of_isCauchySurface`, `Jminus_mem_nhds_of_isCauchySurface` without `hext` (with
   the library's `hdense` and `hcpt`, which the paper does not assume).
5. `lem:image_diamant`, `lem:passe_pgcd` (`Causal.CauchyDiamond`): `image_diamant`,
   `diamond_subset_range`, `passe_pgcd`, `passe_pgcd_explicit` without `hDext` and `hcover`, under
   `[T2Space N] [SecondCountableTopology N]` (nothing on `M`; first countability follows).
6. Witnesses (kb/0011): `timelikeLine_cExtConnexe_secondCountable` (the identity of the timelike
   line) and `timelikeLine_gateArc_secondCountable` (`gateArc : ℝ → ]-1, 1[`, not onto: a Cauchy
   embedding by the new Lemma 3.3, `lem:image_diamant`, and `lem:passe_pgcd` at the frontier point
   `1` of its range).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| singular flat spacetimes, `𝕄≥0`-morphisms | ⚠ weakened: any causality, `IsEMorphism` (a reading, SCOPE) |
| — second countable Hausdorff (`ETT.tex:255`) | ✓ carried as instances; on `N` only where `φ` transfers them to `M` |
| `M` connected, GH; `φ` a Cauchy extension; `A`, `B` Cauchy-including `φ(M)` | ✓ carried (`ConnectedSpace`, `IsCauchyEmbedding`, `IsCauchyInclusion`) |
| "since `M` is GH, `K` is compact" (`lem:image_diamant`, l.2032–2033) | ⚠ strengthened: `hK` named, as in the library |
| a causal curve from `q` to `i(p)` (l.2031: `N` causally arc-connected) | ⚠ strengthened: `hDac` named; ⚠ weakened: unused by `eq_of_mem_image_inter` |
| `p ∈ ∂ i(M) ∩ J⁺(i Σ)` (`lem:passe_pgcd`) | ⚠ weakened: `p ∈ closure (range i)` |
| `prop:K_calcul` on `sing₀(N)` | ⚠ strengthened: named `Sing`, `hreg`, `hsing` |
| `Σ` Cauchy, `ψ` of `theo:geroch_sing` (`lem:Sigma_separe`) | ✓ `Σ` Cauchy carried; ⚠ strengthened: `ψ` named (`IsCauchySplitting`), `M` causally arc-connected |
| `M` GH (`lem:Sigma_separe`) | ⚠ weakened: causal |
| (none) `lem:Sigma_separe`'s neighbourhood forms | ⚠ strengthened: `hdense` (`J∓(x) ⊆ closure K∓(x)`) and `hcpt` (`J∓(Σ) ∩ J±(x)` compact) named, inherited from `Jplus_mem_nhds_of_isCauchySurface`, `Jminus_…`; not principals |
| GH `M`, `M'`; `ψ|Σ` onto `Σ'` (Lemma 3.3) | ✓ carried (`InjOn`, `φ(Σ)` Cauchy); ⚠ strengthened: a time function of `M`, `N` causally arc-connected |
| curves extend, `M = J⁺(Σ) ∪ J⁻(Σ)` (the library's `hDext`, `hext`, `hcover`) | ⚠ weakened: discharged (T2 gives T1) |

## SCOPE (disclosed)

* **Nothing marked.** Each form is a library form less a named hypothesis, in the abstract
  setting: any causality, `IsEMorphism` (the reading of `Causal/SubExtension.lean:42`). Whether
  that setting may anchor the ETT rows was OQ-86, ruled by DEC-190, whose text drops
  `CurvesExtend` and does not say whether the abstract forms anchor: the master's to read. Of the
  labels' principals, only `c_ext_connexe_of_connectedSpace_of_secondCountable` has no named
  hypothesis left (five step lemmas of §1 have none either). The Sbierski
  rows' smooth-vacuum layer 3 is not built.
* **What stays named**: `lem:image_diamant`, `lem:passe_pgcd` the compactness of `J⁺(Σ) ∩ J⁻(p)`
  (`hK`) and `N` causally arc-connected (`hDac`); `lem:passe_pgcd` the `sing₀` facts;
  `lem:Sigma_separe` the splitting `ψ`; `inf_causallyConvexIn` `hDac` (needed for non-local
  causalities, `gateLine_cauchyInclusion_not_causallyConvex`; open under DEC-167's reading); Lemma
  3.3 the time function of `M`; the union `CausallyArcConnectedOn B`.
* **Not here**: `lem:C_ext_connexe`'s middle step, "`φ(Σ)` is a Cauchy surface of `A ∩ B`"
  (`T-abs-c-ext-connexe-cauchy`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology Function TopologicalSpace

universe u v

/-! ## 0. A Cauchy embedding is an open embedding -/

section Embedding

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- **A Cauchy embedding is an open embedding**: an abstract `𝕄≥0`-morphism is continuous and
open, and a Cauchy embedding is injective. -/
theorem IsCauchyEmbedding.isOpenEmbedding (hφ : IsCauchyEmbedding C D φ) : IsOpenEmbedding φ := by
  have hc : Continuous φ := by
    have := hφ.isEMorphism.continuousOn
    rwa [Opens.coe_top, continuousOn_univ] at this
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hc hφ.injective fun U hU =>
    hφ.isEMorphism.isOpen_image ⟨U, hU⟩ le_top

/-- The source of a Cauchy embedding into a Hausdorff space is Hausdorff. -/
theorem IsCauchyEmbedding.t2Space [T2Space N] (hφ : IsCauchyEmbedding C D φ) : T2Space M := by
  exact hφ.isOpenEmbedding.isEmbedding.t2Space

/-- The source of a Cauchy embedding into a second countable space is second countable. -/
theorem IsCauchyEmbedding.secondCountableTopology [SecondCountableTopology N]
    (hφ : IsCauchyEmbedding C D φ) : SecondCountableTopology M := by
  exact hφ.isOpenEmbedding.isInducing.secondCountableTopology

end Embedding

/-! ## 1. `lem:C_ext_connexe` without `hDext` -/

section CExtConnexe

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- `IsCauchyEmbedding.exists_inextensible_inf` without `hDext`, `N` second countable: every
point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B` meeting `φ(Σ)`. -/
theorem IsCauchyEmbedding.exists_inextensible_inf_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) {x : N} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧
      (c '' I ∩ φ '' S).Nonempty := by
  exact hφ.exists_inextensible_inf hA hB hS (Causality.curvesExtend_of_t1_secondCountable D) hx

/-- `IsCauchyEmbedding.isPreconnected_inf` without `hDext`: `Σ` preconnected ⟹ `A ∩ B`
preconnected. -/
theorem IsCauchyEmbedding.isPreconnected_inf_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) (hSc : IsPreconnected S) :
    IsPreconnected ((A ⊓ B : Opens N) : Set N) := by
  exact hφ.isPreconnected_inf hA hB hS hSc (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.c_ext_connexe_of_isConnected` without `hDext`: `Σ` connected ⟹ `A ∩ B`
connected. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_isConnected_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) (hSc : IsConnected S) :
    IsConnected ((A ⊓ B : Opens N) : Set N) := by
  exact hφ.c_ext_connexe_of_isConnected hA hB hS hSc
    (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.c_ext_connexe'` (with the splitting `ψ`) without `hDext`. -/
theorem IsCauchyEmbedding.c_ext_connexe'_of_secondCountable [T2Space N]
    [SecondCountableTopology N] [ConnectedSpace M] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (ψ : S × ℝ ≃ₜ M) : IsConnected ((A ⊓ B : Opens N) : Set N) := by
  exact hφ.c_ext_connexe' hA hB hS ψ (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace` without `hDext`: `M`
preconnected ⟹ `A ∩ B` preconnected. -/
theorem IsCauchyEmbedding.isPreconnected_inf_of_preconnectedSpace_of_secondCountable [T2Space N]
    [SecondCountableTopology N] [PreconnectedSpace M] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) : IsPreconnected ((A ⊓ B : Opens N) : Set N) := by
  exact hφ.isPreconnected_inf_of_preconnectedSpace hA hB
    (Causality.curvesExtend_of_t1_secondCountable D)

/-- **`lem:C_ext_connexe` with no named hypothesis** (`ETT.tex:1932`): `M` connected, `φ` a
Cauchy embedding (`IsCauchyEmbedding`, DEC-17), `A, B` open with `φ(M) → A`, `φ(M) → B` Cauchy
inclusions, `N` Hausdorff and second countable (`ETT.tex:255`) ⟹ `A ∩ B` is connected.
`IsCauchyEmbedding.c_ext_connexe_of_connectedSpace` with `hDext` discharged. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_connectedSpace_of_secondCountable [T2Space N]
    [SecondCountableTopology N] [ConnectedSpace M] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) : IsConnected ((A ⊓ B : Opens N) : Set N) := by
  exact hφ.c_ext_connexe_of_connectedSpace hA hB (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.isCauchySurfaceOn_inf_iff` without `hDext`: `φ(Σ)` is a Cauchy surface of
`A ∩ B` iff every inextensible curve of `A ∩ B` meets it. -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_inf_iff_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} {S : Set M}
    (hS : C.IsCauchySurface S) :
    D.IsCauchySurfaceOn (A ⊓ B) (φ '' S) ↔
      ∀ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c → (c '' I ∩ φ '' S).Nonempty := by
  exact hφ.isCauchySurfaceOn_inf_iff hS (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.inf_causallyConvexIn` without `hDext`: with `N` causally arc-connected,
`A ∩ B` is causally convex in `N` and globally hyperbolic. -/
theorem IsCauchyEmbedding.inf_causallyConvexIn_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    (hDac : D.CausallyArcConnected) :
    D.CausallyConvexIn ((A ⊓ B : Opens N) : Set N) ⊤ ∧ D.GloballyHyperbolicOn (A ⊓ B) := by
  exact hφ.inf_causallyConvexIn hA hB hDac (Causality.curvesExtend_of_t1_secondCountable D)

/-- `IsCauchyEmbedding.eq_of_mem_image_inter` without `hDext` **and without `hDac`**: a causal
curve of any open set meets `φ(Σ)` at most once. `φ(Σ)` is a Cauchy surface of `N`, so it meets
every inextensible curve of `N` at most once, and every causal curve lies on one
(`inter_subsingleton_of_curvesExtend`); no causal arc-connectedness is needed. -/
theorem IsCauchyEmbedding.eq_of_mem_image_inter_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {S : Set M}
    (hS : C.IsCauchySurface S) {W : Opens N} {I : Set ℝ} {c : ℝ → N}
    (hc : D.CausalCurveIn W I c) : ∀ x ∈ c '' I ∩ φ '' S, ∀ y ∈ c '' I ∩ φ '' S, x = y := by
  intro x hx y hy
  exact Causality.inter_subsingleton_of_curvesExtend
    (Causality.curvesExtend_of_t1_secondCountable D)
    (hφ.isCauchySurface_image hS).inter_subsingleton hc hx hy

end CExtConnexe

/-! ## 2. Sbierski Lemma 3.3 without `hDext` -/

namespace CBG

section Injective

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N} {T : M → ℝ} {S : Set M}

/-- `CBG.injective_of_mapsTo_cauchy` without `hDext`, `N` second countable: `φ(Σ) ⊆ Σ'` for a
Cauchy surface `Σ'` of the causal, causally arc-connected `N` makes `φ` injective. -/
theorem injective_of_mapsTo_cauchy_of_secondCountable [T2Space M] [T2Space N]
    [SecondCountableTopology N] (hφ : IsEMorphism C D φ) (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hS : C.IsCauchySurface S) (hinj : InjOn φ S)
    {S' : Set N} (hS' : D.IsCauchySurface S') (hmaps : MapsTo φ S S') (hD : D.IsCausal)
    (hDC : D.CausallyArcConnected) : Injective φ := by
  exact injective_of_mapsTo_cauchy hφ hTc hT hS hinj hS' hmaps hD hDC
    (Causality.curvesExtend_of_t1_secondCountable D)

/-- **Sbierski, Lemma 3.3, with its printed conclusion, without `hDext`** (`Maximal_GHD2.tex:463`):
`CBG.sbierski_lemma_3_3` on a second countable `N`. -/
theorem sbierski_lemma_3_3_of_secondCountable [T2Space M] [T2Space N] [SecondCountableTopology N]
    (hGM : C.GloballyHyperbolic) (hGN : D.GloballyHyperbolic) (hφ : IsEMorphism C D φ)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hS : C.IsCauchySurface S)
    (hS' : D.IsCauchySurface (φ '' S)) (hinj : InjOn φ S) (hDC : D.CausallyArcConnected) :
    IsCauchyEmbedding C D φ := by
  exact sbierski_lemma_3_3 hGM hGN hφ hTc hT hS hS' hinj hDC
    (Causality.curvesExtend_of_t1_secondCountable D)

end Injective

end CBG

/-! ## 3. Thm 3.4's union and convexity without `hext` -/

section Inclusion

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- `Causality.causallyConvexIn_of_isCauchySurfaceOn` without `hext`, `M` second countable: a
Cauchy inclusion is causally convex. -/
theorem Causality.causallyConvexIn_of_isCauchySurfaceOn_of_secondCountable [T2Space M]
    [SecondCountableTopology M] {A B : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hC : C.CausallyArcConnectedOn B)
    (hAB : A ≤ B) {S : Set M} (hSA : S ⊆ A) (hA : C.IsCauchySurfaceOn A S)
    (hB : C.IsCauchySurfaceOn B S) : C.CausallyConvexIn (A : Set M) B := by
  exact Causality.causallyConvexIn_of_isCauchySurfaceOn hanti hC
    (Causality.curvesExtendOn_of_t1_secondCountable C B) hAB hSA hA hB

/-- `IsCauchyInclusion.causallyConvexIn` without `hext`. -/
theorem IsCauchyInclusion.causallyConvexIn_of_secondCountable [T2Space M]
    [SecondCountableTopology M] {A B : Opens M} (h : IsCauchyInclusion C A B)
    (hC : C.CausallyArcConnectedOn B) : C.CausallyConvexIn (A : Set M) B := by
  exact h.causallyConvexIn hC (Causality.curvesExtendOn_of_t1_secondCountable C B)

/-- `Causality.isCauchySurfaceOn_iSup` without `hext`: the union of open sets `W i ≤ B` with a
common Cauchy surface `S`, Cauchy in `B`, has `S` as a Cauchy surface (Sbierski, Thm 3.4,
step 2). -/
theorem Causality.isCauchySurfaceOn_iSup_of_secondCountable [T2Space M]
    [SecondCountableTopology M] {ι : Sort*} {B : Opens M} {W : ι → Opens M} {S : Set M}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hWB : ∀ i, W i ≤ B)
    (hSW : ∀ i, C.IsCauchySurfaceOn (W i) S) (hSB : C.IsCauchySurfaceOn B S) :
    C.IsCauchySurfaceOn (⨆ i, W i) S := by
  exact Causality.isCauchySurfaceOn_iSup hanti (Causality.curvesExtendOn_of_t1_secondCountable C B)
    hWB hSW hSB

/-- `isCauchyInclusion_iSup_of_common` without `hext`. -/
theorem isCauchyInclusion_iSup_of_common_of_secondCountable [T2Space M]
    [SecondCountableTopology M] {ι : Sort*} [Nonempty ι] {B : Opens M} {W : ι → Opens M}
    {S : Set M} (hC : C.CausallyArcConnectedOn B) (hGB : C.GloballyHyperbolicOn B)
    (hWB : ∀ i, W i ≤ B) (hSsub : ∀ i, S ⊆ W i) (hSW : ∀ i, C.IsCauchySurfaceOn (W i) S)
    (hSB : C.IsCauchySurfaceOn B S) :
    IsCauchyInclusion C (⨆ i, W i) B ∧ C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B ∧
      C.IsCauchySurfaceOn (⨆ i, W i) S := by
  exact isCauchyInclusion_iSup_of_common hC (Causality.curvesExtendOn_of_t1_secondCountable C B) hGB
    hWB hSsub hSW hSB

/-- **Thm 3.4's union without `hext`** (`Maximal_GHD2.tex:485`): `isCauchyInclusion_iSup` on a
second countable `M`. Inside an open `B` causally arc-connected into which `A` is
Cauchy-included, a non-empty family of Cauchy inclusions `A → W i` (`W i ≤ B`) has union `U`
with `A → U` a Cauchy inclusion and `U` causally convex in `B`. -/
theorem isCauchyInclusion_iSup_of_secondCountable [T2Space M] [SecondCountableTopology M]
    {ι : Sort*} [Nonempty ι] {A B : Opens M} {W : ι → Opens M} (hC : C.CausallyArcConnectedOn B)
    (hB : IsCauchyInclusion C A B) (hW : ∀ i, IsCauchyInclusion C A (W i)) (hWB : ∀ i, W i ≤ B) :
    IsCauchyInclusion C A (⨆ i, W i) ∧ C.CausallyConvexIn ((⨆ i, W i : Opens M) : Set M) B := by
  exact isCauchyInclusion_iSup hC (Causality.curvesExtendOn_of_t1_secondCountable C B) hB hW hWB

/-- `isCauchyInclusion_sSup` without `hext`. -/
theorem isCauchyInclusion_sSup_of_secondCountable [T2Space M] [SecondCountableTopology M]
    {A B : Opens M} {𝒲 : Set (Opens M)} (hne : 𝒲.Nonempty) (hC : C.CausallyArcConnectedOn B)
    (hB : IsCauchyInclusion C A B) (hW : ∀ W ∈ 𝒲, IsCauchyInclusion C A W)
    (hWB : ∀ W ∈ 𝒲, W ≤ B) :
    IsCauchyInclusion C A (sSup 𝒲) ∧ C.CausallyConvexIn ((sSup 𝒲 : Opens M) : Set M) B := by
  exact isCauchyInclusion_sSup hne hC (Causality.curvesExtendOn_of_t1_secondCountable C B) hB hW
    hWB

end Inclusion

/-! ## 4. `lem:Sigma_separe` from a Cauchy surface -/

namespace Causality

section SigmaSepare

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **`lem:Sigma_separe` for a Cauchy surface** (`ETT.tex:2062`): `sigma_separe` with `Σ` a Cauchy
surface of the causal, causally arc-connected, T1, second countable `M` in place of `Σ` acausal
(`IsCauchySurface.isAcausal_of_t1_secondCountable`). The splitting `ψ` stays named. -/
theorem sigma_separe_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) {S : Set M} (hS : C.IsCauchySurface S)
    {ψ : S × ℝ ≃ₜ M} (hψ : IsCauchySplitting C S ψ) :
    C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y := by
  exact sigma_separe hcaus (hS.isAcausal_of_t1_secondCountable hC) hψ

/-- `Jplus_mem_nhds_of_isCauchySurface` (`lem:Sigma_separe`'s neighbourhood clause, no splitting)
without `hext`, `M` second countable. -/
theorem Jplus_mem_nhds_of_isCauchySurface_of_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) {S : Set M}
    (hS : C.IsCauchySurface S) (hdense : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x})) {y : M}
    (hy : y ∈ C.Jplus ⊤ S \ S) : C.Jplus ⊤ S ∈ 𝓝 y := by
  exact Jplus_mem_nhds_of_isCauchySurface hcaus hC (curvesExtend_of_t1_secondCountable C) hS hdense
    hcpt hy

/-- `Jminus_mem_nhds_of_isCauchySurface` without `hext`, `M` second countable. -/
theorem Jminus_mem_nhds_of_isCauchySurface_of_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal) (hC : C.CausallyArcConnected) {S : Set M}
    (hS : C.IsCauchySurface S) (hdense : ∀ x, C.Jplus ⊤ {x} ⊆ closure (C.Kplus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {x})) {y : M}
    (hy : y ∈ C.Jminus ⊤ S \ S) : C.Jminus ⊤ S ∈ 𝓝 y := by
  exact Jminus_mem_nhds_of_isCauchySurface hcaus hC (curvesExtend_of_t1_secondCountable C) hS
    hdense hcpt hy

end SigmaSepare

end Causality

/-! ## 5. `lem:image_diamant` and `lem:passe_pgcd` without `hDext` and `hcover` -/

section Diamond

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {i : M → N}

/-- **`M = J⁺(Σ) ∪ J⁻(Σ)` from instances on `N` only** (the `hcover` of `image_diamant` and
`passe_pgcd`), for the source of a Cauchy embedding into a T1, second countable `N`: `M` is T1 and
second countable through the open embedding, and the cover on `M` itself is
`Causality.IsCauchySurface.cover_of_t1_secondCountable` (`Causal.CauchySeparation`, ETT-layer
since T-abs-hoist-dual-cover). -/
theorem IsCauchyEmbedding.mem_Jplus_union_Jminus_of_secondCountable [T1Space N]
    [SecondCountableTopology N] (hi : IsCauchyEmbedding C D i) {S : Set M}
    (hS : C.IsCauchySurface S) (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  haveI : T1Space M := hi.isOpenEmbedding.isEmbedding.t1Space
  haveI := hi.secondCountableTopology
  exact hS.cover_of_t1_secondCountable x

/-- **`lem:image_diamant` without `hDext` and `hcover`** (`ETT.tex:2024`): `i` a Cauchy extension
into a T2, second countable `N`, `Σ` a Cauchy surface of `M`, `p ∈ J⁺(Σ)` ⟹
`i(J⁺(Σ) ∩ J⁻(p)) = J⁺(i Σ) ∩ J⁻(i p)`. Still named: `N` causally arc-connected and the
compactness of `J⁺(Σ) ∩ J⁻(p)`. -/
theorem IsCauchyEmbedding.image_diamant_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hi : IsCauchyEmbedding C D i) {S : Set M}
    (hS : C.IsCauchySurface S) (hDac : D.CausallyArcConnected) {p : M}
    (hp : p ∈ C.Jplus ⊤ S) (hK : IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p})) :
    i '' (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) = D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i p} := by
  exact hi.image_diamant hS (hi.mem_Jplus_union_Jminus_of_secondCountable hS) hDac
    (Causality.curvesExtend_of_t1_secondCountable D) hp hK

/-- `IsCauchyEmbedding.diamond_subset_range` without `hDext` and `hcover`. -/
theorem IsCauchyEmbedding.diamond_subset_range_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hi : IsCauchyEmbedding C D i) {S : Set M}
    (hS : C.IsCauchySurface S) (hDac : D.CausallyArcConnected)
    (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m})) (m : M) :
    D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i m} ⊆ range i := by
  exact hi.diamond_subset_range hS (hi.mem_Jplus_union_Jminus_of_secondCountable hS) hDac
    (Causality.curvesExtend_of_t1_secondCountable D) hK m

/-- **`lem:passe_pgcd` without `hDext` and `hcover`** (`ETT.tex:2042`): `K⁻_N(p) ∩ J⁺(i Σ) ⊆ i(M)`
for every `p` in the closure of `i(M)`, `N` T2 and second countable (first countability follows). -/
theorem IsCauchyEmbedding.passe_pgcd_of_secondCountable [T2Space N] [SecondCountableTopology N]
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S)
    (hDac : D.CausallyArcConnected)
    (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m})) {p : N}
    (hp : p ∈ closure (range i)) : D.Kminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i := by
  exact hi.passe_pgcd hS (hi.mem_Jplus_union_Jminus_of_secondCountable hS) hDac
    (Causality.curvesExtend_of_t1_secondCountable D) hK hp

/-- `IsCauchyEmbedding.passe_pgcd_explicit` without `hDext` and `hcover`: the two explicit forms,
the `prop:K_calcul` facts on `Sing` still named. -/
theorem IsCauchyEmbedding.passe_pgcd_explicit_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hi : IsCauchyEmbedding C D i) {S : Set M}
    (hS : C.IsCauchySurface S) (hDac : D.CausallyArcConnected)
    (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m}))
    (Sing : Set N) (hreg : ∀ q ∉ Sing, D.Kminus ⊤ {q} = D.Iminus ⊤ {q})
    (hsing : ∀ q ∈ Sing, D.Kminus ⊤ {q} = D.Jminus ⊤ {q} \ {q})
    {p : N} (hp : p ∈ closure (range i)) :
    (p ∉ Sing → D.Iminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i) ∧
      (p ∈ Sing → (D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {p}) \ {p} ⊆ range i) := by
  exact hi.passe_pgcd_explicit hS (hi.mem_Jplus_union_Jminus_of_secondCountable hS) hDac
    (Causality.curvesExtend_of_t1_secondCountable D) hK Sing hreg hsing hp

end Diamond

/-! ## 6. Witness on the timelike line (kb/0011) -/

/-- **The new forms apply with no curve hypothesis supplied**: on the timelike line (`ℝ`, T2 and
second countable), along `id` with `A = B = ℝ` and `Σ = {0}`, `ℝ ∩ ℝ` is connected
(`c_ext_connexe_of_connectedSpace_of_secondCountable`), the constant family `ℝ` has `ℝ` as a
Cauchy-including union (`isCauchyInclusion_iSup_of_secondCountable`), `lem:Sigma_separe` holds
(`sigma_separe_of_t1_secondCountable`, the splitting `timelikeLineSplitting`), and the diamond
`J⁺(0) ∩ J⁻(1)` is its own image (`image_diamant_of_secondCountable`). -/
theorem timelikeLine_cExtConnexe_secondCountable :
    IsConnected (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) ∧
      IsCauchyInclusion timelikeLine ⊤ (⨆ _ : Unit, ⊤) ∧
      timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {0} = {0} ∧
      id '' (timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {1}) =
        timelikeLine.Jplus ⊤ (id '' {0}) ∩ timelikeLine.Jminus ⊤ {id 1} := by
  have h₁ := timelikeLine_isCauchyInclusion_top
  have hA : IsCauchyInclusion timelikeLine timelikeLine_isCauchyEmbedding_id.rangeOpens ⊤ := by
    rw [timelikeLine_rangeOpens_id]; exact h₁
  have hp : (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} := by
    rw [Precausality.mem_Jplus_singleton, timelikeLine_le]
    exact ⟨zero_le_one, fun _ _ => trivial⟩
  refine ⟨timelikeLine_isCauchyEmbedding_id.c_ext_connexe_of_connectedSpace_of_secondCountable hA
      hA,
    (isCauchyInclusion_iSup_of_secondCountable timelikeLine_causallyArcConnected h₁ (fun _ => h₁)
      fun _ => le_rfl).1,
    (Causality.sigma_separe_of_t1_secondCountable timelikeLine_isCausal
      timelikeLine_causallyArcConnected timelikeLine_isCauchySurface_zero
      timelikeLine_isCauchySplitting).2.2.2.2.1,
    timelikeLine_isCauchyEmbedding_id.image_diamant_of_secondCountable
      timelikeLine_isCauchySurface_zero timelikeLine_causallyArcConnected hp ?_⟩
  rw [timelikeLine_Jplus_zero_inter]
  exact isCompact_Icc


/-- The range of `gateArc` is `]-1, 1[`. -/
theorem range_gateArc : range gateArc = Ioo (-1 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (orderIsoIooNegOneOne ℝ x).2
  · intro hy
    refine ⟨(orderIsoIooNegOneOne ℝ).symm ⟨y, hy⟩, ?_⟩
    simp [gateArc]

/-- **The new forms off the identity** (kb/0011): on the timelike line, `gateArc : ℝ → ]-1, 1[`
is a Cauchy embedding **by the new Lemma 3.3** (`sbierski_lemma_3_3_of_secondCountable`, time
function `id`, `Σ = {0}`), with no curve hypothesis supplied; it is not onto; with
`A = φ(M)`, `B = ℝ`, `A ∩ B` is connected (`c_ext_connexe_of_connectedSpace_of_secondCountable`);
`lem:image_diamant` holds at `p = 1` (`image_diamant_of_secondCountable`); and `lem:passe_pgcd`
holds at the frontier point `1` of the range, which lies in `J⁺(φ Σ)`
(`passe_pgcd_of_secondCountable`). The witness shows the hypotheses met by a Cauchy embedding that
is not onto; on the line each conclusion is also elementary. -/
theorem timelikeLine_gateArc_secondCountable :
    IsCauchyEmbedding timelikeLine timelikeLine gateArc ∧ range gateArc ≠ univ ∧
      (∀ hφ : IsCauchyEmbedding timelikeLine timelikeLine gateArc,
        IsConnected ((hφ.rangeOpens ⊓ ⊤ : Opens ℝ) : Set ℝ)) ∧
      gateArc '' (timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {1}) =
        timelikeLine.Jplus ⊤ (gateArc '' {0}) ∩ timelikeLine.Jminus ⊤ {gateArc 1} ∧
      (1 : ℝ) ∈ frontier (range gateArc) ∧ (1 : ℝ) ∈ timelikeLine.Jplus ⊤ (gateArc '' {0}) ∧
      timelikeLine.Kminus ⊤ {1} ∩ timelikeLine.Jplus ⊤ (gateArc '' {0}) ⊆ range gateArc := by
  have hS' : timelikeLine.IsCauchySurface (gateArc '' {0}) := by
    rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _
  have hφ : IsCauchyEmbedding timelikeLine timelikeLine gateArc :=
    CBG.sbierski_lemma_3_3_of_secondCountable (T := id) timelikeLine_globallyHyperbolic
      timelikeLine_globallyHyperbolic timelikeLine_isEMorphism_gateArc continuous_id
      (fun x y h hne => lt_of_le_of_ne (timelikeLine_le.1 h).1 hne)
      timelikeLine_isCauchySurface_zero hS' gateArc_strictMono.injective.injOn
      timelikeLine_causallyArcConnected
  have hK : ∀ m ∈ timelikeLine.Jplus ⊤ {0},
      IsCompact (timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {m}) := fun m _ => by
    rw [timelikeLine_Jplus_zero_inter]; exact isCompact_Icc
  have h1 : (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} := by
    rw [Precausality.mem_Jplus_singleton, timelikeLine_le]
    exact ⟨zero_le_one, fun _ _ => trivial⟩
  have hfr : (1 : ℝ) ∈ frontier (range gateArc) := by
    rw [range_gateArc, frontier_Ioo (by norm_num)]
    exact Or.inr rfl
  have hne : range gateArc ≠ univ := fun h => by
    obtain ⟨x, hx⟩ : (1 : ℝ) ∈ range gateArc := h ▸ mem_univ _
    exact (gateArc_lt_one x).ne hx
  refine ⟨hφ, hne, fun hφ => ?_,
    hφ.image_diamant_of_secondCountable timelikeLine_isCauchySurface_zero
      timelikeLine_causallyArcConnected h1 (hK 1 h1), hfr, ?_,
    hφ.passe_pgcd_of_secondCountable timelikeLine_isCauchySurface_zero
      timelikeLine_causallyArcConnected hK (frontier_subset_closure hfr)⟩
  · have hCA : timelikeLine.IsCauchySurfaceOn hφ.rangeOpens (gateArc '' {0}) :=
      (hφ.isEMorphism.isCauchySurface_iff hφ.injective {0}).1 timelikeLine_isCauchySurface_zero
    have hsub : gateArc '' {0} ⊆ (hφ.rangeOpens : Set ℝ) := by
      rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range _ _
    have hA : IsCauchyInclusion timelikeLine hφ.rangeOpens hφ.rangeOpens :=
      ⟨le_rfl, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
        hCA, hCA⟩
    have hB : IsCauchyInclusion timelikeLine hφ.rangeOpens ⊤ :=
      ⟨le_top, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
        hCA, hS'⟩
    exact hφ.c_ext_connexe_of_connectedSpace_of_secondCountable hA hB
  · rw [image_singleton, Precausality.mem_Jplus_singleton, timelikeLine_le]
    exact ⟨(gateArc_lt_one 0).le, fun _ _ => trivial⟩

end Causal
