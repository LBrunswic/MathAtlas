import Causal.SingularSplitting
import Causal.Remarks.SingularRowsCauchy

/-!
# Geroch's « Moreover » and the equalities of `lem:Sigma_separe` at every causal `E_{≥0}`-manifold; the τ-flow of `E₀`

Target `T-ett-geroch-split-flow`, the `M`-level part and SCOPE (d) of the target. Cited, unmarked
(SCOPE): `theo:geroch_sing` — `ETT.tex:1771`, its « Moreover » (l.1778); `lem:Sigma_separe` —
`ETT.tex:2062`, its equalities (l.2066). For a singular `(Isom(𝐌³), 𝐌³)`-manifold `M` (DEC-25),
Hausdorff and second countable, and every absolutely minimal causality `C` with an isomorphic
chart at each point over the family `E_{≥0}` (`IsoChartsCoverDEC25 … massAModelCausality`; the
natural causality is one), the theorems of `Causal.SingularSplitting` are applied to
`SFAManifolds.singularFlatAxioms`.

> Moreover, if $\Sigma$ is a Cauchy surface of $M$, then $M$ is homeomorphic to
> $\Sigma\times \RR$. (`theo:geroch_sing`, `ETT.tex:1778`)

> For $\kappa\geq 0$ the vertical vector field $X_\kappa$ of $\mass{\kappa}$ is $\CC^1$,
> non-singular, future causal and parallel to the singular direction at every singular point.
> (proof of `lem:vecteur`, `ETT.tex:1763–1764`)

> Then $J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)$ and
> $J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right)$. (`lem:Sigma_separe`, `ETT.tex:2065–2066`)

## What is proved (no `sorry` in this file)

* **At `M`.** `geroch_sing_split_of_isCausalFlow` (the « Moreover », a causal flow `φ`, `ψ (x, t) =
  φ t x`, `IsCauchySplitting`), `nonempty_homeomorph_of_isCausalFlow`; the `VecteurFlow` form with
  no connectedness and its openness unused (`geroch_sing_split_of_vecteurFlow`), that openness
  proved (`isOpenMap_of_vecteurFlow`); `nonempty_vecteurFlow_iff`; the equalities of
  `lem:Sigma_separe` for `ψ` (`sigma_separe_of_isCausalFlow`, `exists_sigma_separe_of_isCausalFlow`);
  `cor:K_ordre_Sigma` through the flow splitting (`K_ordre_Sigma_of_isCausalFlow`, which
  instantiates `SingularRowsK.K_ordre_Sigma_of_splitting`). Causal, Hausdorff, second countable;
  no global hyperbolicity but in `cor:K_ordre_Sigma`; no connectedness.
* **The natural causality**: `rows_of_isAtlasCausalityDEC25`.
* **(d) `E₀`.** The τ-translation `tauFlow` (`(τ, z) ↦ (τ + t, z)`, `E0.tauShift`) is a causal
  flow (`isCausalFlow_tauFlow`): its orbits are causal curves over `ℝ` (`causalCurveIn_tauFlow`,
  `ClosedLe` with equal radii and angles), with no fixed point, hence inextensible. Its orbits are
  null: no two of their points are chronologically related (`not_lt_tauFlow`, as `≪` asks
  `r₁ < r₂`), so it is not a chronal flow (`not_isChronalFlow_tauFlow`); no causal flow of `E₀` is
  chronal (`e0_not_hasChronalCausalFlow`, from `not_hasChronalCausalFlow`: none at any `E_{≥0}`-manifold
  with a BTZ point). It keeps the axis (`tauFlow_mem_axis`). It splits `E₀` along every Cauchy
  surface (`tauFlow_split`). `VecteurFlow` is inhabited at `E₀` (`vecteurFlow_e0`). `nonvacuous_e0`: a Cauchy surface `S` with a BTZ point
  `p ∈ J⁺(S) ∖ S`, `I⁻(p) = ∅`, the flow splitting, the two equalities,
  `K_ordre_Sigma_of_splitting` instantiated, and the strict `SingularRowsGeroch.geroch_sing_split`
  instantiated with `vecteurFlow_e0`. `nonvacuous_e0_natural`: the same rows for the natural
  causality.

## Hypothesis checklist

| paper | here |
|---|---|
| singular flat spacetime, `E_{≥0}`-manifold | ⚠ read (DEC-25, OQ-18): `[SingularGXStructure (Flat.isom 2) (Minkowski 2) M]`, `C` absolutely minimal with `IsoChartsCoverDEC25` over `massAModelCausality`; the natural causality in `rows_of_isAtlasCausalityDEC25` |
| — Hausdorff, second countable (« manifold », `ETT.tex:254`) | ✓ carried |
| — connected (l.1502) | ⚠ weakened: not used |
| — strongly causal (DEC-18) | ⚠ weakened: causal |
| `lem:Sigma_separe`: `M` globally hyperbolic | ⚠ weakened: causal; ✓ carried by `K_ordre_Sigma_of_isCausalFlow` (`cor:K_ordre_Sigma`) |
| `Σ` a Cauchy surface | ✓ carried (DEC-14) |
| the flow of `lem:vecteur` | ⚠ named: `IsCausalFlow C φ` (`Causal.SingularSplitting`); equivalent to `VecteurFlow` here (`nonempty_vecteurFlow_iff`) |
| `E₀`'s vertical field `X_0` (l.1763) | ⚠ read: the τ-translation of `Causal.E0` (OQ-34, OQ-35) |
| `E₀`, `Isom(E^{1,2})` | ⚠ read: `Causal.E0` (OQ-34, OQ-35), `Flat.isom 2` (OQ-82) |

## SCOPE (disclosed)

* **Why unmarked.** The rows rest on DEC-25 and the readings OQ-18, OQ-34/OQ-35 and OQ-82. The
  flow of `lem:vecteur` stays a named hypothesis at a general `M` (`IsCausalFlow`):
  `lem:vecteur` is not formalized. It is discharged at `E₀` only. The equivalence of
  `theo:geroch_sing` rests on OQ-32's tagged `sorry` (`CausalScaffold.SingularRowsGerochEquiv`).
* **The τ-flow is null.** Along an orbit `r` is constant, and `≪` asks `r₁ < r₂` (`ClosedLt`).
  No other flow helps: a chronal flow gives every point a chronological past, and a BTZ point has
  none. So the chronal-flow route (`IsCausalFlow.exists_isCauchySplitting_of_isChronalFlow`,
  `HasChronalCausalFlow.nonempty_isCauchySplitting`) applies at no `E_{≥0}`-manifold with a BTZ
  point. The closedness of `J^±(S)` comes from `SingularFlatAxioms.sigma_separe_of_isCausal`
  (T-ett-sigma-separe).
* **The τ-flow as `X_0`.** It is read as the flow of the paper's vertical field of `E₀` (l.1763,
  `∂_τ` in the coordinates of `Causal.E0`); that reading is not used by any proof here.
* **Witnesses.** The Cauchy surfaces are existential (out of `theo:geroch_sing` (i)⇒(iii)); the
  BTZ point of `nonvacuous_e0` is on the axis above the point where the axis meets `S`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports
`Causal.SingularSplitting` and the strict `Causal.Remarks.SingularRowsCauchy` (through it
`Causal.Remarks.SingularRowsK`, `Causal.Remarks.SingularRowsGeroch`, `Causal.Port.SFAManifolds`
and the `E₀` ports).
-/

namespace Causal

open Set Filter Topology TopologicalSpace Function

universe u

namespace SingularRowsSplitting

section Manifold

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M} {φ : Flow ℝ M}

/-- `theo:geroch_sing`'s « Moreover » (unmarked) **at every causal, Hausdorff, second countable
`E_{≥0}`-manifold, from any causal flow**: `ψ (x, t) = φ t x` is a homeomorphism `S × ℝ ≃ₜ M`,
a Cauchy splitting. No global hyperbolicity, no connectedness. -/
theorem geroch_sing_split_of_isCausalFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hφ : C.IsCausalFlow φ) {S : Set M} (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ :=
  (SFAManifolds.singularFlatAxioms hmin hC).geroch_sing_split_of_isCausalFlow hc hφ hS

/-- The « Moreover » as printed, `M ≃ₜ S × ℝ`, given a causal flow. -/
theorem nonempty_homeomorph_of_isCausalFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hφ : C.IsCausalFlow φ) {S : Set M} (hS : C.IsCauchySurface S) :
    Nonempty (S × ℝ ≃ₜ M) :=
  (SFAManifolds.singularFlatAxioms hmin hC).nonempty_homeomorph_of_isCausalFlow hc hφ hS

/-- The `VecteurFlow` form, with no connectedness and `F.isOpenMap` unused (it strengthens the
strict `SingularRowsGeroch.geroch_sing_split`). -/
theorem geroch_sing_split_of_vecteurFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (F : C.VecteurFlow) {S : Set M} (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = F.flow x t) ∧ C.IsCauchySplitting S ψ :=
  (SFAManifolds.singularFlatAxioms hmin hC).geroch_sing_split_of_vecteurFlow hc F hS

/-- `VecteurFlow.isOpenMap`, the openness the paper asserts (l.1792), is a theorem at `M`. -/
theorem isOpenMap_of_vecteurFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (F : C.VecteurFlow) {S : Set M} (hS : C.IsCauchySurface S) :
    IsOpenMap fun q : S × ℝ => F.flow q.1 q.2 :=
  (SFAManifolds.singularFlatAxioms hmin hC).isOpenMap_of_vecteurFlow hc F hS

/-- At a causal `E_{≥0}`-manifold a `VecteurFlow` is exactly a causal flow. -/
theorem nonempty_vecteurFlow_iff [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) : Nonempty C.VecteurFlow ↔ ∃ φ : Flow ℝ M, C.IsCausalFlow φ :=
  (SFAManifolds.singularFlatAxioms hmin hC).nonempty_vecteurFlow_iff hc

/-- `lem:Sigma_separe` (unmarked) **for the homeomorphism `ψ` of the « Moreover »**, at every
causal, Hausdorff, second countable `E_{≥0}`-manifold: `J⁺(S) = ψ(S × ℝ₊)`, `J⁻(S) = ψ(S × ℝ₋)`
and the « In particular ». -/
theorem sigma_separe_of_isCausalFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hφ : C.IsCausalFlow φ) {S : Set M} (hS : C.IsCauchySurface S)
    {ψ : S × ℝ ≃ₜ M} (hψ : ∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) :
    C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y :=
  (SFAManifolds.singularFlatAxioms hmin hC).sigma_separe_of_isCausalFlow hc hφ hS hψ

/-- The « Moreover » and `lem:Sigma_separe` at once, at `M`. -/
theorem exists_sigma_separe_of_isCausalFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hc : C.IsCausal) (hφ : C.IsCausalFlow φ) {S : Set M} (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ ∧
      C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y :=
  (SFAManifolds.singularFlatAxioms hmin hC).exists_sigma_separe_of_isCausalFlow hc hφ hS

/-- `cor:K_ordre_Sigma` through the flow splitting: `SingularRowsK.K_ordre_Sigma_of_splitting`
with the `ψ` of `geroch_sing_split_of_isCausalFlow`, at every globally hyperbolic `M`. -/
theorem K_ordre_Sigma_of_isCausalFlow [T2Space M] [SecondCountableTopology M]
    (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hG : C.GloballyHyperbolic) (hφ : C.IsCausalFlow φ) {S : Set M} (hS : C.IsCauchySurface S) :
    (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
      C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
    InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S) := by
  obtain ⟨ψ, -, hψ⟩ := geroch_sing_split_of_isCausalFlow hmin hC hG.1 hφ hS
  exact SingularRowsK.K_ordre_Sigma_of_splitting hmin hC hG hS hψ

/-- **No chronal flow at an `E_{≥0}`-manifold with a BTZ point** (`I⁻(p) = ∅` there,
`SFALocal.Iminus_eq_empty`): the chronal-flow splitting of `Causal.Splitting` never applies.
Neither Hausdorff nor second countable. -/
theorem not_hasChronalCausalFlow (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hne : (SFALocal.sing M 0).Nonempty) : ¬ C.HasChronalCausalFlow := by
  rintro ⟨ψ, -, hch⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨y, hy⟩ := hch.Iminus_nonempty p
  rw [SFALocal.Iminus_eq_empty hmin hC p hp] at hy
  exact hy

/-! ### The natural causality -/

/-- The rows for the natural causality. -/
theorem rows_of_isAtlasCausalityDEC25 [T2Space M] [SecondCountableTopology M]
    (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    (C.IsCausal → ∀ φ : Flow ℝ M, C.IsCausalFlow φ → ∀ S : Set M, C.IsCauchySurface S →
      ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ ∧
        C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
        IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
        ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
    (C.IsCausal → (Nonempty C.VecteurFlow ↔ ∃ φ : Flow ℝ M, C.IsCausalFlow φ)) ∧
    (C.GloballyHyperbolic → ∀ φ : Flow ℝ M, C.IsCausalFlow φ → ∀ S : Set M,
      C.IsCauchySurface S →
      (∀ x ∈ C.Jplus ⊤ S \ S, ∀ y ∈ C.Jplus ⊤ S \ S,
        C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S ⊆ C.Kminus ⊤ {y} ∩ C.Jplus ⊤ S → C.le ⊤ x y) ∧
      InjOn (fun x => C.Kminus ⊤ {x} ∩ C.Jplus ⊤ S) (C.Jplus ⊤ S \ S)) := by
  obtain ⟨hmin, hC'⟩ := SFALocal.of_isAtlasCausalityDEC25 hcov hC
  exact ⟨fun hc _ hφ _ hS => exists_sigma_separe_of_isCausalFlow hmin hC' hc hφ hS,
    fun hc => nonempty_vecteurFlow_iff hmin hC' hc,
    fun hG _ hφ _ hS => K_ordre_Sigma_of_isCausalFlow hmin hC' hG hφ hS⟩

end Manifold

/-! ### (d) The τ-flow of `E₀` -/

section WitnessE0

attribute [local instance] E0GX.singularGX

/-- **The τ-translation of `E₀`** as a flow: `t • (τ, z) = (τ + t, z)` (`E0.tauShift`). -/
noncomputable def tauFlow : Flow ℝ E0 where
  toFun t x := E0.tauShift t x
  cont' := by
    show Continuous fun q : ℝ × E0 => ((q.2.1 + q.1, q.2.2) : E0)
    fun_prop
  map_add' t₁ t₂ x := by
    show ((x.1 + (t₁ + t₂), x.2) : E0) = ((x.1 + t₂ + t₁, x.2) : E0)
    rw [add_comm t₁ t₂, add_assoc]
  map_zero' x := by
    show ((x.1 + 0, x.2) : E0) = x
    rw [add_zero]

theorem tauFlow_apply (t : ℝ) (x : E0) : tauFlow t x = (x.1 + t, x.2) := rfl

/-- Along an orbit of the τ-flow the local relation `Le` holds in the order of the parameter:
`ClosedLe` with equal radii and equal angles. -/
theorem le_tauFlow (x : E0) {s t : ℝ} (hst : s ≤ t) : E0.Le (tauFlow s x) (tauFlow t x) := by
  refine E0.le_iff_closed.2 ⟨Complex.arg x.2, Complex.arg x.2, E0.polar_arg x, E0.polar_arg x, ?_⟩
  show E0.ClosedLe (x.1 + s) (E0.rad x) (x.1 + t) (E0.rad x) (Complex.arg x.2 - Complex.arg x.2)
  refine ⟨by linarith, le_rfl, by simp⟩

/-- The orbits of the τ-flow are causal curves of `E₀` over `ℝ`. -/
theorem causalCurveIn_tauFlow (x : E0) :
    E0.causality.CausalCurveIn ⊤ univ (fun t => tauFlow t x) where
  nonempty := univ_nonempty
  ordConnected := ordConnected_univ
  curve _ _ _ _ := E0.causalCurveOn_of_curveOn (E0.curveOn_of_continuousOn
    (tauFlow.continuous continuous_id continuous_const).continuousOn (fun _ _ => trivial)
    fun _ _ _ _ hss' => le_tauFlow x hss'.le)

/-- **The τ-flow is a causal flow of `E₀`**: causal orbits, no fixed point, hence inextensible. -/
theorem isCausalFlow_tauFlow : E0.causality.IsCausalFlow tauFlow :=
  Causality.IsCausalFlow.of_causalCurveIn causalCurveIn_tauFlow fun x => ⟨1, fun h => by
    have h1 : x.1 + 1 = x.1 := congrArg Prod.fst h
    linarith⟩

/-- The τ-flow keeps the axis `sing₀(E₀)`: at a BTZ point it is along the singular line. -/
theorem tauFlow_mem_axis {t : ℝ} {x : E0} : tauFlow t x ∈ E0.axis ↔ x ∈ E0.axis :=
  E0.tauShift_axis

/-- **The orbits of the τ-flow are null**: no two of their points are chronologically related
(`≪` asks `r₁ < r₂`, and `r` is constant along an orbit). -/
theorem not_lt_tauFlow (x : E0) (s t : ℝ) : ¬ E0.causality.lt ⊤ (tauFlow s x) (tauFlow t x) := by
  intro h
  have hr : E0.rad x < E0.rad x := (E0.lt_top_iff.1 h).closed.1
  exact lt_irrefl _ hr

/-- **The τ-flow is not a chronal flow**, so the chronal-flow splitting does not apply. -/
theorem not_isChronalFlow_tauFlow : ¬ E0.causality.IsChronalFlow tauFlow := fun h =>
  not_lt_tauFlow 0 0 1 ((h 0 0 1).lt_of_lt le_rfl zero_lt_one le_rfl)

/-- **`E₀` has no chronal causal flow** (a BTZ point has `I⁻ = ∅`). -/
theorem e0_not_hasChronalCausalFlow : ¬ E0.causality.HasChronalCausalFlow := by
  obtain ⟨hmin, hC, -, hne⟩ := SFALocal.nonvacuous_e0
  exact not_hasChronalCausalFlow hmin hC hne

/-- **The τ-flow splits `E₀` along every Cauchy surface**, with `lem:Sigma_separe`'s equalities. -/
theorem tauFlow_split {S : Set E0} (hS : E0.causality.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ E0, (∀ (x : S) (t : ℝ), ψ (x, t) = ((x : E0).1 + t, (x : E0).2)) ∧
      E0.causality.IsCauchySplitting S ψ ∧
      E0.causality.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧
      E0.causality.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) := by
  obtain ⟨hmin, hC, -, -⟩ := SFALocal.nonvacuous_e0
  obtain ⟨ψ, hψ, hsplit, hp, hm, -⟩ :=
    exists_sigma_separe_of_isCausalFlow hmin hC E0.isCausal isCausalFlow_tauFlow hS
  exact ⟨ψ, hψ, hsplit, hp, hm⟩

/-- **A `VecteurFlow` at `E₀`**: the τ-flow, its openness proved. -/
noncomputable def vecteurFlow_e0 : E0.causality.VecteurFlow :=
  isCausalFlow_tauFlow.toVecteurFlow
    (SFAManifolds.singularFlatAxioms SFALocal.nonvacuous_e0.1 SFALocal.nonvacuous_e0.2.1)
    E0.isCausal

theorem vecteurFlow_e0_flow (x : E0) (t : ℝ) : vecteurFlow_e0.flow x t = (x.1 + t, x.2) := rfl

/-- **Non-vacuity at `E₀`** (kb/0011): the τ-flow is causal and not chronal, and `E₀` has no
chronal flow; a Cauchy surface `S`
with a BTZ point `p ∈ J⁺(S) ∖ S`, `I⁻(p) = ∅`; the flow splitting along `S`, the equalities of
`lem:Sigma_separe`, `SingularRowsK.K_ordre_Sigma_of_splitting` instantiated with it, and the
strict `SingularRowsGeroch.geroch_sing_split` instantiated with `vecteurFlow_e0`. -/
theorem nonvacuous_e0 :
    E0.causality.IsCausalFlow tauFlow ∧ ¬ E0.causality.IsChronalFlow tauFlow ∧
      ¬ E0.causality.HasChronalCausalFlow ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        (∃ p ∈ SFALocal.sing E0 0, p ∈ E0.causality.Jplus ⊤ S \ S ∧
          E0.causality.Iminus ⊤ {p} = ∅) ∧
        ∃ ψ : S × ℝ ≃ₜ E0, (∀ (x : S) (t : ℝ), ψ (x, t) = tauFlow t x) ∧
          E0.causality.IsCauchySplitting S ψ ∧
          E0.causality.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧
          E0.causality.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
          ((∀ x ∈ E0.causality.Jplus ⊤ S \ S, ∀ y ∈ E0.causality.Jplus ⊤ S \ S,
              E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S ⊆
                E0.causality.Kminus ⊤ {y} ∩ E0.causality.Jplus ⊤ S → E0.causality.le ⊤ x y) ∧
            InjOn (fun x => E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S)
              (E0.causality.Jplus ⊤ S \ S)) ∧
          Nonempty (S × ℝ ≃ₜ E0) := by
  obtain ⟨hmin, hC, -, hG, -, -, S, hS⟩ := SingularRowsGeroch.nonvacuous_e0_geroch
  obtain ⟨-, -, -, hne⟩ := SFALocal.nonvacuous_e0
  obtain ⟨p, hp0, hp⟩ := SingularRowsCauchy.exists_btz_Jplus_diff hmin hC hG.1 hS hne
  obtain ⟨ψ, hψ, hsplit, hJp, hJm, -⟩ :=
    exists_sigma_separe_of_isCausalFlow hmin hC hG.1 isCausalFlow_tauFlow hS
  exact ⟨isCausalFlow_tauFlow, not_isChronalFlow_tauFlow, e0_not_hasChronalCausalFlow, S, hS,
    ⟨p, hp0, hp, SFALocal.Iminus_eq_empty hmin hC p hp0⟩, ψ, hψ, hsplit, hJp, hJm,
    SingularRowsK.K_ordre_Sigma_of_splitting hmin hC hG hS hsplit,
    SingularRowsGeroch.geroch_sing_split hmin hC hG.1 vecteurFlow_e0 hS⟩

/-- **Non-vacuity of `rows_of_isAtlasCausalityDEC25` at `E₀`** with its natural causality over the
family: a Cauchy surface `S`, the τ-flow splitting along it with the equalities, `VecteurFlow`
inhabited, and `cor:K_ordre_Sigma` at `S`, out of the assembly. -/
theorem nonvacuous_e0_natural :
    SFALocal.MassACovered E0 ∧
      IsAtlasCausalityDEC25 (Flat.isom 2) E0.causality (minkowski 2) massAModelCausality ∧
      Nonempty E0.causality.VecteurFlow ∧
      ∃ S : Set E0, E0.causality.IsCauchySurface S ∧
        ∃ ψ : S × ℝ ≃ₜ E0, (∀ (x : S) (t : ℝ), ψ (x, t) = tauFlow t x) ∧
          E0.causality.IsCauchySplitting S ψ ∧
          E0.causality.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧
          E0.causality.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
          InjOn (fun x => E0.causality.Kminus ⊤ {x} ∩ E0.causality.Jplus ⊤ S)
            (E0.causality.Jplus ⊤ S \ S) := by
  obtain ⟨-, hcov, hC, -⟩ := EModelsBPrime.massA_dec25_models_e0_sing
  obtain ⟨hr1, hr2, hr3⟩ := rows_of_isAtlasCausalityDEC25 hcov hC
  obtain ⟨S, hS⟩ := SingularRowsGeroch.geroch_sing_i_imp_iii_of_isAtlasCausalityDEC25 hcov hC
    E0.globallyHyperbolic
  obtain ⟨ψ, hψ, hsplit, hJp, hJm, -⟩ := hr1 E0.isCausal tauFlow isCausalFlow_tauFlow S hS
  exact ⟨hcov, hC, (hr2 E0.isCausal).2 ⟨tauFlow, isCausalFlow_tauFlow⟩, S, hS, ψ, hψ, hsplit,
    hJp, hJm, (hr3 E0.globallyHyperbolic tauFlow isCausalFlow_tauFlow S hS).2⟩

end WitnessE0

end SingularRowsSplitting

end Causal
