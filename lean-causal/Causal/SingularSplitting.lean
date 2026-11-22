import Causal.Splitting
import Causal.SingularCauchy

/-!
# Geroch's « Moreover » from any causal flow, and the equalities of `lem:Sigma_separe`, under `SingularFlatAxioms`

Target `T-ett-geroch-split-flow`, the abstract part: SCOPE (a), (b), (c) of the target. Cited,
unmarked (SCOPE): `theo:geroch_sing` — `ETT.tex:1771`, its « Moreover » (l.1778, proof
l.1787–1795); `lem:Sigma_separe` — `ETT.tex:2062`, its two equalities (l.2066) for the `ψ` of
the « Moreover ». This module imports no model directly.

> Moreover, if $\Sigma$ is a Cauchy surface of $M$, then $M$ is homeomorphic to
> $\Sigma\times \RR$. (`theo:geroch_sing`, `ETT.tex:1778`)

> Let $X$ be a vector field given by Lemma \ref{lem:vecteur}; up to multiplying it by a positive
> scalar field we may assume its flow to be complete. [...] Since $X$ is non-singular, $\psi$ is a
> local diffeomorphism. Moreover $X$ is causal, so the curves $c_x:t\mapsto \psi(x,t)$,
> $x\in \Sigma$, are inextensible causal curves. They therefore meet $\Sigma$ exactly once. Hence
> $\psi$ is bijective, and so it is a diffeomorphism. (`ETT.tex:1788–1795`)

> let $\psi:\Sigma\times \RR\rightarrow M$ be the homeomorphism of Theorem
> \ref{theo:geroch_sing}. Then
> $J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)$ and
> $J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right)$. (`lem:Sigma_separe`, `ETT.tex:2063–2066`)

## What is proved (no `sorry` in this file)

* (a) **A `VecteurFlow` is a causal flow.** `VecteurFlow.toFlow` (mathlib's `Flow ℝ M`),
  `VecteurFlow.isCausalFlow` (`C` causal). Conversely, at a causal `SingularFlatAxioms`
  spacetime every causal flow is a `VecteurFlow`, openness included
  (`IsCausalFlow.toVecteurFlow`, `SingularFlatAxioms.nonempty_vecteurFlow_iff`). So the forms
  below, which ask for `IsCausalFlow`, are at least the `VecteurFlow` forms.
  `IsCausalFlow.of_causalCurveIn`: the paper's « non-singular, causal » suffices, inextensibility
  being a consequence (Hausdorff).
* (b) **The « Moreover », with no openness hypothesis.**
  `SingularFlatAxioms.geroch_sing_split_of_isCausalFlow`: for a causal singular flat spacetime,
  a causal flow `φ` and a Cauchy surface `S`, the map `ψ (x, t) = φ t x` is a homeomorphism
  `S × ℝ ≃ₜ M` with `IsCauchySplitting`. `J^±(S)` closed comes from
  `SingularFlatAxioms.sigma_separe_of_isCausal`, `S` acausal from
  `IsCauchySurface.isAcausal_of_t1_secondCountable`. No global hyperbolicity, no connectedness.
  `geroch_sing_split_of_vecteurFlow` is the `VecteurFlow` form, its field `isOpenMap` unused;
  `isOpenMap_of_vecteurFlow` proves that field.
* (c) **The equalities of `lem:Sigma_separe` for that `ψ`.** Model-free, without closedness:
  `IsCausalFlow.Jplus_eq_image`, `IsCausalFlow.Jminus_eq_image` (`C` causal, `S` an acausal
  Cauchy surface). Under the structure: `SingularFlatAxioms.sigma_separe_of_isCausalFlow`, for
  every homeomorphism `ψ` with `ψ (x, t) = φ t x`, the two equalities and the « In particular »;
  `exists_sigma_separe_of_isCausalFlow`, (b) and (c) at once.
* **Why the route.** A chronal flow gives every point a chronological past
  (`IsChronalFlow.Iminus_nonempty`), so a singular flat spacetime with a BTZ point has none
  (`SingularFlatAxioms.not_isChronalFlow`, `not_hasChronalCausalFlow`): the chronal-flow
  splitting of `Causal.Splitting` never applies there.
* **Witness** (kb/0011): the timelike line, `S = {0}`, the flow `x ↦ x + t`
  (`timelikeLine_geroch_sing_split_of_isCausalFlow`), regular branch only. The BTZ branch is at
  `E₀`, `Causal.Remarks.SingularRowsSplitting`.

## Hypothesis checklist

| paper | here |
|---|---|
| `M` a singular flat spacetime | ⚠ strengthened: `SingularFlatAxioms C sing` (kb/0012), through `sigma_separe_of_isCausal`; discharged at every `E_{≥0}`-manifold in `Causal.Remarks.SingularRowsSplitting` |
| — connected (l.1502) | ⚠ weakened: not used |
| — strongly causal (DEC-18) | ⚠ weakened: causal (`IsCausal`) |
| `lem:Sigma_separe`: `M` globally hyperbolic | ⚠ weakened: causal |
| `Σ` a Cauchy surface | ✓ carried (DEC-14) |
| the complete flow `Φ` of `X` (`lem:vecteur`) | ⚠ named (kb/0012, kb/0022): `IsCausalFlow C φ`, a `Flow ℝ M` whose orbits are inextensible causal curves, with no fixed point; ⚠ weakened against `VecteurFlow`: no openness, no injectivity field |
| — `X` `C¹`, parallel to the singular lines | ⚠ weakened: not used |
| « `ψ` is a local diffeomorphism » (l.1792) | derived, `C⁰` content: `ψ` is open (`isOpenMap_of_isCausalFlow`) |
| « homeomorphic to `Σ × ℝ` » | ✓ carried, by `ψ` itself (`ψ (x, t) = φ t x`), with `IsCauchySplitting` |
| `ψ`, « the homeomorphism of `theo:geroch_sing` » (l.2064) | ✓ carried: any `ψ : S × ℝ ≃ₜ M` with `ψ (x, t) = φ t x` |

## SCOPE (disclosed)

* **Why unmarked.** The flow of `lem:vecteur` stays a named hypothesis, now `IsCausalFlow` (a
  `C¹` field and its flow need a differentiable structure the library does not have). The setting
  is `SingularFlatAxioms`, whose instance at `E_{≥0}`-manifolds rests on OQ-18, OQ-34, OQ-35 and
  OQ-82. The equivalence of `theo:geroch_sing` is not here (its (iii)⇒(i) is OQ-32's tagged `sorry`).
* **The route.** The topological content of l.1792 is the continuity of the hitting time, which
  is `J^±(Σ)` closed (`IsCausalFlow.isClosed_iff_exists_isCauchySplitting`). The paper derives
  that closedness from `ψ` (l.2067, l.2079). Here it comes first, with no `ψ`, from T-ett-sigma-separe.
  The flow need not be chronal, and with a BTZ point none is (`SingularFlatAxioms.not_isChronalFlow`,
  from `IsChronalFlow.Iminus_nonempty`).
* **(a) uses causality** for « no fixed point ». A `VecteurFlow` gives injective orbits only on a
  causal `M` (its field `injective`). Every form below assumes `C` causal anyway.
* **Imports.** `Causal.Splitting` is the home of `IsCausalFlow` and of the hitting-time splitting.
  It also holds the Minkowski witnesses and the flat flow, so it brings in, transitively,
  `Causal.Flat.Form`, `Causal.Flat.IsomCausal`, `Causal.GXStructure`, `Causal.Minkowski`,
  `Causal.Static`, `Causal.Chains` and mathlib's manifold and ODE modules. None of them is used
  here. This module imports no model directly; re-deriving `IsCausalFlow` would duplicate it.
  Hoisting `IsCausalFlow` and the hitting-time splitting out of `Causal.Splitting` (kb/0047) would
  drop those modules from the closure; it would not make it model-free in the sense of
  `tools/ladder.py`, which counts `Causal.SingularFlat`, reached through `Causal.SingularCauchy`,
  as model layer.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.Splitting` (`IsCausalFlow`, `IsCausalFlow.exists_isCauchySplitting`,
`Causality.inextensible_of_flow`) and `Causal.SingularCauchy` (`sigma_separe_of_isCausal`, and
through it `Causal.SingularGeroch`'s `VecteurFlow`).
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {φ : Flow ℝ M} {S : Set M}

/-! ### (a) A `VecteurFlow` is a causal flow -/

/-- The flow of a `VecteurFlow`, as a mathlib `Flow ℝ M`: `t • x = F.flow x t`. -/
def VecteurFlow.toFlow (F : C.VecteurFlow) : Flow ℝ M where
  toFun t x := F.flow x t
  cont' := F.continuous_flow.comp continuous_swap
  map_add' t₁ t₂ x := by
    show F.flow x (t₁ + t₂) = F.flow (F.flow x t₂) t₁
    rw [F.flow_add, add_comm]
  map_zero' x := F.flow_zero x

theorem VecteurFlow.toFlow_apply (F : C.VecteurFlow) (t : ℝ) (x : M) :
    F.toFlow t x = F.flow x t := rfl

/-- (a) **A `VecteurFlow` of a causal `C` is a causal flow**: its orbits are the inextensible
causal curves of the field, and none is stationary (orbits are injective on a causal `M`). -/
theorem VecteurFlow.isCausalFlow (F : C.VecteurFlow) (hc : C.IsCausal) :
    C.IsCausalFlow F.toFlow where
  inextensible x := F.inextensible x
  nonstationary x := ⟨1, fun h1 => by
    have h : F.flow x 1 = F.flow x 0 := by rw [F.flow_zero]; exact h1
    exact one_ne_zero (F.injective hc x h)⟩

/-- **The paper's « non-singular, causal » is enough** (l.1792–1793): on a Hausdorff space, a flow
whose orbits are causal curves over `ℝ` and which has no fixed point is a causal flow, its orbits
being inextensible (`inextensible_of_flow`). -/
theorem IsCausalFlow.of_causalCurveIn [T2Space M]
    (hcurve : ∀ x, C.CausalCurveIn ⊤ univ (fun t => φ t x)) (hns : ∀ x, ∃ t, φ t x ≠ x) :
    C.IsCausalFlow φ where
  inextensible := inextensible_of_flow hcurve hns
  nonstationary := hns

/-- **A chronal flow leaves no point without a chronological past**: `φ (-1) x ≪ x`. So no
spacetime with a point `p`, `I⁻(p) = ∅` (a BTZ point), has a chronal flow. -/
theorem IsChronalFlow.Iminus_nonempty (hch : C.IsChronalFlow φ) (x : M) :
    (C.Iminus ⊤ {x}).Nonempty := by
  have h := (hch x (-1) 0).lt_of_lt le_rfl (by norm_num) le_rfl
  rw [Flow.map_zero_apply] at h
  exact ⟨φ (-1) x, x, rfl, h⟩

/-! ### (c), model-free: the equalities of `lem:Sigma_separe`, without closedness -/

/-- **The causal future of `S` is the future half of its flow tube**, for every causal flow of a causal `C`
and every acausal Cauchy surface `S`, with no closedness: `J⁺(S) = {φ t x | x ∈ S, t ≥ 0}`. -/
theorem IsCausalFlow.Jplus_eq_image (hc : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    C.Jplus ⊤ S = (fun q : S × ℝ => φ q.2 q.1) '' (univ ×ˢ Ici 0) := by
  ext y
  constructor
  · intro hy
    have hτ := hφ.apply_hitTime_mem hS y
    have h0 : hφ.hitTime hS y ≤ 0 :=
      (hφ.apply_mem_Jplus_iff hc hac hτ 0).1 (by rwa [Flow.map_zero_apply])
    refine ⟨(⟨_, hτ⟩, -hφ.hitTime hS y), ⟨trivial, ?_⟩, ?_⟩
    · show (0 : ℝ) ≤ -hφ.hitTime hS y
      linarith
    · show φ (-hφ.hitTime hS y) (φ (hφ.hitTime hS y) y) = y
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    refine ⟨x, x.2, ?_⟩
    have := hφ.le (x : M) (show (0 : ℝ) ≤ t from ht)
    rwa [Flow.map_zero_apply] at this

/-- **The causal past of `S` is the past half of its flow tube**: `J⁻(S) = {φ t x | x ∈ S, t ≤ 0}`. -/
theorem IsCausalFlow.Jminus_eq_image (hc : C.IsCausal) (hφ : C.IsCausalFlow φ)
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) :
    C.Jminus ⊤ S = (fun q : S × ℝ => φ q.2 q.1) '' (univ ×ˢ Iic 0) := by
  ext y
  constructor
  · intro hy
    have hτ := hφ.apply_hitTime_mem hS y
    have h0 : 0 ≤ hφ.hitTime hS y :=
      (hφ.apply_mem_Jminus_iff hc hac hτ 0).1 (by rwa [Flow.map_zero_apply])
    refine ⟨(⟨_, hτ⟩, -hφ.hitTime hS y), ⟨trivial, ?_⟩, ?_⟩
    · show -hφ.hitTime hS y ≤ 0
      linarith
    · show φ (-hφ.hitTime hS y) (φ (hφ.hitTime hS y) y) = y
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    refine ⟨x, x.2, ?_⟩
    have := hφ.le (x : M) (show t ≤ 0 from ht)
    rwa [Flow.map_zero_apply] at this

/-! ### (b) The « Moreover » under `SingularFlatAxioms` -/

variable {sing : ℝ → Set M}

namespace SingularFlatAxioms

/-- (b) `theo:geroch_sing`'s « Moreover » (unmarked), **from any causal flow**: at a causal
singular flat spacetime, a causal flow `φ` and a Cauchy surface `S` give the homeomorphism
`ψ (x, t) = φ t x` of `S × ℝ` onto `M`, a Cauchy splitting. `J^±(S)` closed from
`sigma_separe_of_isCausal`; no global hyperbolicity, no connectedness, no openness hypothesis. -/
theorem geroch_sing_split_of_isCausalFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ := by
  haveI := h.t2
  haveI := h.secondCountable
  obtain ⟨hJp, hJm, -⟩ := h.sigma_separe_of_isCausal hc hS
  exact hφ.exists_isCauchySplitting hc hS
    (hS.isAcausal_of_t1_secondCountable h.causallyArcConnected) hJp hJm

/-- **No chronal flow at a singular flat spacetime with a BTZ point** (`I⁻(p) = ∅` there), so
`IsCausalFlow.exists_isCauchySplitting_of_isChronalFlow` never applies to it: the closedness of
`J^±(S)` in (b) has to come from `sigma_separe_of_isCausal`. No causality used. -/
theorem not_isChronalFlow (h : C.SingularFlatAxioms sing) (hne : (sing 0).Nonempty)
    (φ : Flow ℝ M) : ¬ C.IsChronalFlow φ := fun hch => by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨y, hy⟩ := hch.Iminus_nonempty p
  rw [h.Iminus_eq_empty p hp] at hy
  exact hy

/-- The same for `HasChronalCausalFlow` (`Causal.Splitting`): it fails once `sing₀ ≠ ∅`. -/
theorem not_hasChronalCausalFlow (h : C.SingularFlatAxioms sing) (hne : (sing 0).Nonempty) :
    ¬ C.HasChronalCausalFlow := fun ⟨ψ, _, hch⟩ => h.not_isChronalFlow hne ψ hch

/-- (b) **The « Moreover » as printed**: `M` is homeomorphic to `S × ℝ`, given a causal flow. -/
theorem nonempty_homeomorph_of_isCausalFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) : Nonempty (S × ℝ ≃ₜ M) := by
  obtain ⟨ψ, -⟩ := h.geroch_sing_split_of_isCausalFlow hc hφ hS
  exact ⟨ψ⟩

/-- **The openness the paper asserts (l.1792) is a theorem**: for a causal flow of a causal
singular flat spacetime and a Cauchy surface `S`, `(x, t) ↦ φ t x` is open on `S × ℝ`. -/
theorem isOpenMap_of_isCausalFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) :
    IsOpenMap fun q : S × ℝ => φ q.2 q.1 := by
  obtain ⟨ψ, hψ, -⟩ := h.geroch_sing_split_of_isCausalFlow hc hφ hS
  have he : (fun q : S × ℝ => φ q.2 q.1) = ψ := funext fun q => (hψ q.1 q.2).symm
  rw [he]
  exact ψ.isOpenMap

/-- (b) **The `VecteurFlow` form, its openness unused**: the strict `geroch_sing_split` with
`SingularFlatAxioms` for `SingularFlatSpacetime` and `ψ` named; `F.isOpenMap` is not read. -/
theorem geroch_sing_split_of_vecteurFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (F : C.VecteurFlow) (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = F.flow x t) ∧ C.IsCauchySplitting S ψ :=
  h.geroch_sing_split_of_isCausalFlow hc (F.isCausalFlow hc) hS

/-- **The field `VecteurFlow.isOpenMap` follows from the others** at a causal singular flat
spacetime. -/
theorem isOpenMap_of_vecteurFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (F : C.VecteurFlow) (hS : C.IsCauchySurface S) :
    IsOpenMap fun q : S × ℝ => F.flow q.1 q.2 :=
  h.isOpenMap_of_isCausalFlow hc (F.isCausalFlow hc) hS

end SingularFlatAxioms

/-- (a) **A causal flow of a causal singular flat spacetime is a `VecteurFlow`**, its field
`isOpenMap` proved (`SingularFlatAxioms.isOpenMap_of_isCausalFlow`). -/
def IsCausalFlow.toVecteurFlow (hφ : C.IsCausalFlow φ) (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) : C.VecteurFlow where
  flow x t := φ t x
  continuous_flow := φ.continuous continuous_snd continuous_fst
  flow_zero x := Flow.map_zero_apply φ x
  flow_add x s t := by
    show φ t (φ s x) = φ (s + t) x
    rw [← Flow.map_add, add_comm]
  inextensible x := hφ.inextensible x
  injective hc' x := hφ.injective hc' x
  isOpenMap _ hS := h.isOpenMap_of_isCausalFlow hc hφ hS

theorem IsCausalFlow.toVecteurFlow_flow (hφ : C.IsCausalFlow φ) (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) (x : M) (t : ℝ) : (hφ.toVecteurFlow h hc).flow x t = φ t x := rfl

namespace SingularFlatAxioms

/-- (a) **At a causal singular flat spacetime, `VecteurFlow` is exactly a causal flow.** -/
theorem nonempty_vecteurFlow_iff (h : C.SingularFlatAxioms sing) (hc : C.IsCausal) :
    Nonempty C.VecteurFlow ↔ ∃ φ : Flow ℝ M, C.IsCausalFlow φ :=
  ⟨fun ⟨F⟩ => ⟨F.toFlow, F.isCausalFlow hc⟩, fun ⟨_, hφ⟩ => ⟨hφ.toVecteurFlow h hc⟩⟩

/-! ### (c) The equalities of `lem:Sigma_separe` for the `ψ` of the « Moreover » -/

/-- (c) `lem:Sigma_separe` (unmarked), **for the homeomorphism `ψ` of the « Moreover »**: for a
causal flow `φ` of a causal singular flat spacetime, a Cauchy surface `S` and any homeomorphism
`ψ : S × ℝ ≃ₜ M` with `ψ (x, t) = φ t x`, `J⁺(S) = ψ(S × ℝ₊)`, `J⁻(S) = ψ(S × ℝ₋)`, and the
« In particular ». Causal only (⚠ weakened from globally hyperbolic). -/
theorem sigma_separe_of_isCausalFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) {ψ : S × ℝ ≃ₜ M}
    (hψ : ∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) :
    C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y := by
  haveI := h.t2
  haveI := h.secondCountable
  have hac := hS.isAcausal_of_t1_secondCountable h.causallyArcConnected
  have he : ⇑ψ = fun q : S × ℝ => φ q.2 q.1 := funext fun q => hψ q.1 q.2
  obtain ⟨hJp, hJm, hcap, hnhds, -⟩ := h.sigma_separe_of_isCausal hc hS
  refine ⟨?_, ?_, hJp, hJm, hcap, hnhds⟩
  · rw [he]; exact hφ.Jplus_eq_image hc hS hac
  · rw [he]; exact hφ.Jminus_eq_image hc hS hac

/-- (b) and (c) at once: the splitting of the « Moreover » exists, and `lem:Sigma_separe` holds
for it. -/
theorem exists_sigma_separe_of_isCausalFlow (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hφ : C.IsCausalFlow φ) (hS : C.IsCauchySurface S) :
    ∃ ψ : S × ℝ ≃ₜ M, (∀ (x : S) (t : ℝ), ψ (x, t) = φ t x) ∧ C.IsCauchySplitting S ψ ∧
      C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y := by
  obtain ⟨ψ, hψ, hsplit⟩ := h.geroch_sing_split_of_isCausalFlow hc hφ hS
  exact ⟨ψ, hψ, hsplit, h.sigma_separe_of_isCausalFlow hc hφ hS hψ⟩

end SingularFlatAxioms

/-! ### Witness on the timelike line (kb/0011) -/

/-- **Witness**: the timelike line, its flow `x ↦ x + t` (`timelikeLine_vecteurFlow`) and the
Cauchy surface `{0}` satisfy the hypotheses of `geroch_sing_split_of_isCausalFlow` and of
`sigma_separe_of_isCausalFlow`; the conclusions out of them. Regular branch only (`sing = ∅`). -/
theorem _root_.Causal.timelikeLine_geroch_sing_split_of_isCausalFlow :
    timelikeLine.IsCausalFlow (timelikeLine_vecteurFlow.toFlow) ∧
      ∃ ψ : ({0} : Set ℝ) × ℝ ≃ₜ ℝ, (∀ (x : ({0} : Set ℝ)) (t : ℝ), ψ (x, t) = (x : ℝ) + t) ∧
        timelikeLine.IsCauchySplitting {0} ψ ∧
        timelikeLine.Jplus ⊤ ({0} : Set ℝ) = ψ '' (univ ×ˢ Ici 0) ∧
        timelikeLine.Jminus ⊤ ({0} : Set ℝ) = ψ '' (univ ×ˢ Iic 0) := by
  have hφ := timelikeLine_vecteurFlow.isCausalFlow timelikeLine_isCausal
  obtain ⟨ψ, hψ, hsplit, hp, hm, -⟩ :=
    timelikeLine_singularFlatAxioms.exists_sigma_separe_of_isCausalFlow timelikeLine_isCausal hφ
      timelikeLine_isCauchySurface_zero
  exact ⟨hφ, ψ, hψ, hsplit, hp, hm⟩

end Causality

end Causal
