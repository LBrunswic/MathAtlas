import Causal.SingularGeroch
import Causal.CurvesExtendSecondCountable
import Causal.CauchyDual
import Causal.ChronalNeighbourBridge

/-!
# A Cauchy surface separates, without the splitting: the « In particular » of `lem:Sigma_separe` under `SingularFlatAxioms`

Target `T-ett-sigma-separe`, part (a). Cited, unmarked (SCOPE): `lem:Sigma_separe` —
`ETT.tex:2062`, its « In particular » (l.2067–2068), for every Cauchy surface and with no
homeomorphism `ψ`. The two equalities `J^±(Σ) = ψ(Σ × ℝ_±)` are not stated here: they stay
`Causality.sigma_separe` (`Causal.CauchyDiamond`), under a named `ψ`. This module imports no model.

> Let $M$ be a globally hyperbolic singular flat spacetime, let $\Sigma$ be a Cauchy surface of
> $M$ and let $\psi:\Sigma\times \RR\rightarrow M$ be the homeomorphism of Theorem
> \ref{theo:geroch_sing}. Then
> $$J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)\qquad\text{and}\qquad
> J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right).$$
> In particular $J^\pm(\Sigma)$ are closed, $J^+(\Sigma)\cap J^-(\Sigma)=\Sigma$, and
> $J^+(\Sigma)$ is a neighbourhood of each of its points outside $\Sigma$.
> (`lem:Sigma_separe`, `ETT.tex:2062–2069`)

## What is proved (no `sorry` in this file)

* `SingularFlatAxioms.sigma_separe`: the « In particular » as printed, `M` globally hyperbolic,
  for every Cauchy surface `S`: `J^±(S)` closed, `J⁺(S) ∩ J⁻(S) = S`, `J⁺(S)` a neighbourhood of
  each point of `J⁺(S) ∖ S`.
* `SingularFlatAxioms.sigma_separe_of_isCausal`: the same with `M` **causal only** (global
  hyperbolicity is not used), and more: `J⁻(S)` a neighbourhood of each point of `J⁻(S) ∖ S`,
  `M = J⁺(S) ∪ J⁻(S)`, `J^±(S) ∖ S` open, `S` closed.
* The steps, model-free. (1) `IsCauchySurface.cover_of_t1_secondCountable`: `M = J⁺(S) ∪ J⁻(S)`
  on every T1, second countable space, for any causality (the `hcover` of `lem:image_diamant`).
  (2) `IsAcausal.Jplus_inter_Jminus`. The connectedness step
  `CausalCurveIn.mem_image_of_between`, Hausdorff and causal only. (3) at a point with a
  chronological past, `IsCauchySurface.exists_isOpen_of_Iminus_nonempty` and
  `isOpen_Jplus_diff_of_Iminus_nonempty`. (5) `IsCauchySurface.sigma_separe_of_isOpen`. The
  regular case in one statement: `IsCauchySurface.sigma_separe_of_nonemptyChronalCones` (causal,
  causally arc-connected, `NoPastEndpoint`, `NonemptyChronalCones`).
* Under the structure. (3) at a BTZ point, `SingularFlatAxioms.exists_isOpen_of_mem_sing_zero`
  (tarentin and the BTZ line); chronology, `SingularFlatAxioms.not_lt_self`;
  `isOpen_Jplus_diff`; (4) `isOpen_Jminus_diff`, with no BTZ case (every point is in `Z⁺`); for
  every Cauchy surface, a BTZ point in `J⁺(S) ∖ S` once `sing₀ ≠ ∅`
  (`exists_mem_sing_zero_Jplus_diff`).
* Witnesses (kb/0011): the timelike line with `S = {0}` (`timelikeLine_sigma_separe`,
  `timelikeLine_sigma_separe_of_nonemptyChronalCones`), regular branch only. The BTZ branch is
  instantiated at `E₀` in `Causal.Remarks.SingularRowsCauchy` (`nonvacuous_e0`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` a singular flat spacetime | ⚠ strengthened: `SingularFlatAxioms C sing` (kb/0012); used: `t2`, `secondCountable`, `causallyArcConnected`, `tarentin`, `mem_Zplus`, `mem_Zminus_iff`, `noIsolated`, `isClosed_sing`, `singularPastAt`, `past_local`, `line`. Discharged at every `E_{≥0}`-manifold in `Causal.Remarks.SingularRowsCauchy` |
| — connected (`def:singular_spacetime`, l.1502) | ⚠ weakened: not used |
| `M` globally hyperbolic | ✓ carried by `sigma_separe`; ⚠ weakened: `sigma_separe_of_isCausal` asks `M` causal only |
| `Σ` a Cauchy surface of `M` | ✓ carried (DEC-14) |
| `ψ : Σ × ℝ → M`, the homeomorphism of `theo:geroch_sing` | ⚠ weakened: not used (the « In particular » only) |

## SCOPE (disclosed)

* **Why unmarked.** Only the « In particular » is proved; the equalities `J^±(Σ) = ψ(Σ × ℝ_±)`
  need `ψ`, the flow of `lem:vecteur`, which the library does not have (T-ett-geroch-split-flow).
  The setting is the abstraction `SingularFlatAxioms`, whose `E_{≥0}`-manifold instance rests on
  the readings OQ-18, OQ-34, OQ-35 and OQ-82.
* **The route.** (1) The constant curve at `x`, extended to an inextensible one
  (`exists_inextensible_of_t1_secondCountable`), meets `S` at a point comparable with `x`.
  (2) `S` is acausal (`IsCauchySurface.isAcausal_of_t1_secondCountable`) and `C` causal. (3) At a
  regular `p` take `q ≪ p`, a chronal curve `c` from `q` to `p`, and an inextensible `γ ⊇ c`, meeting
  `S` at `x = γ s₀`. Either `x ≤ q`, and `I⁺(q)` is the open set, or `q ≤ x ≤ p` and `x` lies on
  `c` before its end, and `I⁺(x)` is the open set. At a BTZ point `p` the line `γ` through `p`
  meets `S` at `γ s₀`, `s₀ < 0`. Tarentin gives `a ≤ p` with `p ∈ Int J⁺(a)` outside the closed set
  `γ(]-∞, s₀])`, and `Int J⁺(a)` is the open set. Each of these open sets misses `S`, using
  acausality, causality, chronology at `S` and the injectivity of `γ`. Hence `J⁺(S) ∖ S` is open.
  (4) is (3)'s first case on `C.dual`. (5) `(J^±(S))ᶜ = J^∓(S) ∖ S`.
* **No closedness of `J^±(x)`.** The planner's route used global hyperbolicity
  (`GloballyHyperbolic.isClosed_Jplus_singleton`) to put `x` on `c([0, 1])`.
  `CausalCurveIn.mem_image_of_between` avoids it. With `γ τ₀ = c 0`, `γ τ₁ = c 1`,
  `τ₀ ≤ s₀ ≤ τ₁`, the compact pieces `γ([τ₀, s₀])` and `γ([s₀, τ₁])` are closed in a Hausdorff
  space. They cover `c([0, 1])`, and they meet only at `x` (`M` causal). So the connected
  `c([0, 1])` contains `x`.
* **Chronology at `S`.** That the open sets miss `S` uses `¬ x ≪ x` at the points of `S`
  (`hchr`). Under the structure it is `SingularFlatAxioms.not_lt_self` (`Jplus_not_mem_nhds`,
  `Jminus_ne_singleton`).
* **The BTZ case cannot be avoided.** At a BTZ point `I⁻(p) = ∅`, so the regular argument has no
  `q`. Every Cauchy surface of a causal singular flat spacetime with `sing₀ ≠ ∅` has a BTZ point
  in `J⁺(S) ∖ S` (`exists_mem_sing_zero_Jplus_diff`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Imports the strict
`Causal.SingularGeroch` (`Jminus_ne_singleton`, through `Causal.Geroch` `Jplus_not_mem_nhds`),
`Causal.CurvesExtendSecondCountable`, `Causal.CauchyDual` and `Causal.ChronalNeighbourBridge`
(`NonemptyChronalCones`); not `Causal.Splitting`, which imports a model (`Causal.Flat.IsomCausal`).
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

/-! ### Model-free steps -/

/-- Step (1): in a T1, second countable space, every point lies on an inextensible causal curve (the
constant one, extended), which meets a Cauchy surface `S` at a point comparable with it, so
`M = J⁺(S) ∪ J⁻(S)`. No causality, no global hyperbolicity. -/
theorem IsCauchySurface.cover_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurface S) (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  have hconst : C.CausalCurveIn ⊤ (Icc 0 1) (fun _ => x) :=
    (causalCurveOn_const (a := 0) (b := 1) (show x ∈ (⊤ : Opens M) from trivial)).causalCurveIn_Icc
      zero_le_one
  obtain ⟨J, γ, hγ, hsub⟩ := exists_inextensible_of_t1_secondCountable hconst
  obtain ⟨t, ht, htx⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have htx' : γ t = x := htx
  obtain ⟨σ, ⟨⟨s, hs, rfl⟩, hσS⟩, -⟩ := hS J γ hγ
  rcases le_total s t with hst | hts
  · left
    refine ⟨γ s, hσS, ?_⟩
    rw [← htx']
    exact hγ.1.le_of_le hs ht hst
  · right
    refine ⟨γ s, hσS, ?_⟩
    rw [← htx']
    exact hγ.1.le_of_le ht hs hts

/-- Step (2): an acausal set of a causal spacetime is `J⁺(S) ∩ J⁻(S)`. -/
theorem IsAcausal.Jplus_inter_Jminus (hc : C.IsCausal) (hS : C.IsAcausal S) :
    C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S := by
  apply Subset.antisymm
  · rintro y ⟨⟨σ, hσ, hσy⟩, ⟨σ', hσ', hyσ'⟩⟩
    have h1 : σ = σ' := hS σ hσ σ' hσ' (C.le_trans hσy hyσ')
    rw [← h1] at hyσ'
    rw [← hc hσy hyσ']
    exact hσ
  · intro x hx
    exact ⟨⟨x, hx, C.le_refl trivial⟩, ⟨x, hx, C.le_refl trivial⟩⟩

/-- The connectedness step of (3), with no closedness of `J^±(x)`: if a causal curve `c` over
`[0, 1]` lies on a causal curve `γ` over an interval `J`, and `γ s₀` sits between `c 0 = γ τ₀` and
`c 1 = γ τ₁` in the parameter, then `γ s₀` is on `c`. Hausdorff and causal only: the pieces
`γ([τ₀, s₀])`, `γ([s₀, τ₁])` are compact, hence closed, and would disconnect `c([0, 1])`. -/
theorem CausalCurveIn.mem_image_of_between [T2Space M] (hc : C.IsCausal) {c γ : ℝ → M}
    {J : Set ℝ} (hcc : C.CausalCurveOn ⊤ c 0 1) (hγ : C.CausalCurveIn ⊤ J γ)
    (hsub : c '' Icc 0 1 ⊆ γ '' J) {τ₀ s₀ τ₁ : ℝ} (hτ₀ : τ₀ ∈ J) (hτ₁ : τ₁ ∈ J)
    (h0 : γ τ₀ = c 0) (h1 : γ τ₁ = c 1) (hτs : τ₀ ≤ s₀) (hsτ : s₀ ≤ τ₁) :
    γ s₀ ∈ c '' Icc 0 1 := by
  by_contra hx
  have hs₀ : s₀ ∈ J := hγ.ordConnected.out hτ₀ hτ₁ ⟨hτs, hsτ⟩
  have hJ₁ : Icc τ₀ s₀ ⊆ J := hγ.ordConnected.out hτ₀ hs₀
  have hJ₂ : Icc s₀ τ₁ ⊆ J := hγ.ordConnected.out hs₀ hτ₁
  have hK₁ : IsClosed (γ '' Icc τ₀ s₀) :=
    (isCompact_Icc.image_of_continuousOn
      ((hγ.curve τ₀ hτ₀ s₀ hs₀).continuousOn C.isRelFamily_le)).isClosed
  have hK₂ : IsClosed (γ '' Icc s₀ τ₁) :=
    (isCompact_Icc.image_of_continuousOn
      ((hγ.curve s₀ hs₀ τ₁ hτ₁).continuousOn C.isRelFamily_le)).isClosed
  have hcont : ContinuousOn c (Icc 0 1) := hcc.continuousOn C.isRelFamily_le
  have hA : IsClosed (Icc (0 : ℝ) 1 ∩ c ⁻¹' (γ '' Icc τ₀ s₀)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc hK₁
  have hB : IsClosed (Icc (0 : ℝ) 1 ∩ c ⁻¹' (γ '' Icc s₀ τ₁)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc hK₂
  have hcover : Icc (0 : ℝ) 1 ⊆
      (Icc (0 : ℝ) 1 ∩ c ⁻¹' (γ '' Icc τ₀ s₀)) ∪ (Icc (0 : ℝ) 1 ∩ c ⁻¹' (γ '' Icc s₀ τ₁)) := by
    intro u hu
    obtain ⟨t, ht, hct⟩ := hsub ⟨u, hu, rfl⟩
    have hc0u : C.le ⊤ (c 0) (c u) := hcc.le_of_le le_rfl hu.1 hu.2
    have hcu1 : C.le ⊤ (c u) (c 1) := hcc.le_of_le hu.1 hu.2 le_rfl
    rcases lt_or_ge t τ₀ with htτ | hτt
    · have hle : C.le ⊤ (γ t) (γ τ₀) := hγ.le_of_le ht hτ₀ htτ.le
      rw [hct, h0] at hle
      have heq : c u = c 0 := hc hle hc0u
      exact Or.inl ⟨hu, τ₀, ⟨le_rfl, hτs⟩, h0.trans heq.symm⟩
    · rcases le_or_gt t s₀ with hts | hst
      · exact Or.inl ⟨hu, t, ⟨hτt, hts⟩, hct⟩
      · rcases le_or_gt t τ₁ with htτ₁ | hτ₁t
        · exact Or.inr ⟨hu, t, ⟨hst.le, htτ₁⟩, hct⟩
        · have hle : C.le ⊤ (γ τ₁) (γ t) := hγ.le_of_le hτ₁ ht hτ₁t.le
          rw [hct, h1] at hle
          have heq : c u = c 1 := hc hcu1 hle
          exact Or.inr ⟨hu, τ₁, ⟨hsτ, le_rfl⟩, h1.trans heq.symm⟩
  obtain ⟨u, hu, ⟨-, t, ht, hct⟩, ⟨-, t', ht', hct'⟩⟩ :=
    isPreconnected_closed_iff.1 isPreconnected_Icc _ _ hA hB hcover
      ⟨0, ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩, τ₀, ⟨le_rfl, hτs⟩, h0⟩
      ⟨1, ⟨zero_le_one, le_rfl⟩, ⟨zero_le_one, le_rfl⟩, τ₁, ⟨hsτ, le_rfl⟩, h1⟩
  have h1' : C.le ⊤ (c u) (γ s₀) := by
    rw [← hct]; exact hγ.le_of_le (hJ₁ ht) hs₀ ht.2
  have h2' : C.le ⊤ (γ s₀) (c u) := by
    rw [← hct']; exact hγ.le_of_le hs₀ (hJ₂ ht') ht'.1
  exact hx ⟨u, hu, hc h1' h2'⟩

/-- Step (3) at a point with a chronological past: if `p ∈ J⁺(S) ∖ S` has some `q ≪ p`, an open
set around `p` lies in `J⁺(S) ∖ S`. `S` is a Cauchy surface of a causal, causally arc-connected
spacetime on a Hausdorff, second countable space, chronological at its points. -/
theorem IsCauchySurface.exists_isOpen_of_Iminus_nonempty [T2Space M] [SecondCountableTopology M]
    (hc : C.IsCausal) (hac : C.CausallyArcConnected) (hS : C.IsCauchySurface S)
    (hchr : ∀ x ∈ S, ¬ C.lt ⊤ x x) {p : M} (hp : p ∈ C.Jplus ⊤ S \ S)
    (hq : (C.Iminus ⊤ {p}).Nonempty) :
    ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ O ⊆ C.Jplus ⊤ S \ S := by
  have hSa : C.IsAcausal S := hS.isAcausal_of_t1_secondCountable hac
  have hcap := IsAcausal.Jplus_inter_Jminus hc hSa
  obtain ⟨q, hqp⟩ := hq
  have hqp' : C.lt ⊤ q p := by simpa using hqp
  obtain ⟨c, hcc, hc0, hc1⟩ := (hac ⊤ le_rfl q p).2.1 hqp'
  obtain ⟨J, γ, hγ, hsub⟩ := exists_inextensible_of_t1_secondCountable
    (hcc.causalCurveOn.causalCurveIn_Icc zero_le_one)
  obtain ⟨x, ⟨⟨s₀, hs₀, rfl⟩, hxS⟩, -⟩ := hS J γ hγ
  obtain ⟨τ₀, hτ₀, h0⟩ := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  obtain ⟨τ₁, hτ₁, h1⟩ := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have hpS : p ∉ S := hp.2
  -- `γ s₀ ≤ p`: otherwise `p ∈ J⁻(S)`, and `p ∈ J⁺(S) ∩ J⁻(S) = S`
  have hsτ : s₀ ≤ τ₁ := by
    by_contra hlt
    have hle : C.le ⊤ (γ τ₁) (γ s₀) := hγ.1.le_of_le hτ₁ hs₀ (not_le.1 hlt).le
    rw [h1, hc1] at hle
    have hmem : p ∈ C.Jplus ⊤ S ∩ C.Jminus ⊤ S := ⟨hp.1, γ s₀, hxS, hle⟩
    rw [hcap] at hmem
    exact hpS hmem
  -- a point `z` with `γ s₀ ≤ z ≪ p`
  obtain ⟨z, hxz, hzp⟩ : ∃ z, C.le ⊤ (γ s₀) z ∧ C.lt ⊤ z p := by
    rcases le_total s₀ τ₀ with hsτ₀ | hτ₀s
    · refine ⟨q, ?_, hqp'⟩
      have hle := hγ.1.le_of_le hs₀ hτ₀ hsτ₀
      rwa [h0, hc0] at hle
    · obtain ⟨s, hs, hcs⟩ :=
        CausalCurveIn.mem_image_of_between hc hcc.causalCurveOn hγ.1 hsub hτ₀ hτ₁ h0 h1 hτ₀s hsτ
      have hs1 : s < 1 := by
        refine lt_of_le_of_ne hs.2 ?_
        rintro rfl
        rw [hc1] at hcs
        exact hpS (by rw [hcs]; exact hxS)
      refine ⟨γ s₀, C.le_refl trivial, ?_⟩
      have hlt := hcc.lt_of_lt hs.1 hs1 le_rfl
      rwa [hcs, hc1] at hlt
  refine ⟨{y | C.lt ⊤ z y}, C.isOpen_lt_right ⊤ z, hzp, ?_⟩
  intro y hy
  have hzy : C.lt ⊤ z y := hy
  have hxy : C.le ⊤ (γ s₀) y := C.le_trans hxz (C.le_of_lt hzy)
  refine ⟨⟨γ s₀, hxS, hxy⟩, fun hyS => ?_⟩
  -- `y ∈ S` forces `y = γ s₀ = z`, and `z ≪ z`
  have hxy' : γ s₀ = y := hSa _ hxS _ hyS hxy
  have hzx : C.le ⊤ z (γ s₀) := by rw [hxy']; exact C.le_of_lt hzy
  have hzeq : γ s₀ = z := hc hxz hzx
  apply hchr _ hxS
  rw [← hzeq, ← hxy'] at hzy
  exact hzy

/-- Steps (1), (2) and (5), assembled: once `J⁺(S) ∖ S` and `J⁻(S) ∖ S` are open, `J^±(S)` are
closed (their complements are `J^∓(S) ∖ S`, by (1) and (2)), `J⁺(S) ∩ J⁻(S) = S`, each `J^±(S)` is
a neighbourhood of its points outside `S`, `M = J⁺(S) ∪ J⁻(S)` and `S` is closed. -/
theorem IsCauchySurface.sigma_separe_of_isOpen [T1Space M] [SecondCountableTopology M]
    (hS : C.IsCauchySurface S) (hc : C.IsCausal) (hac : C.CausallyArcConnected)
    (hP : IsOpen (C.Jplus ⊤ S \ S)) (hM : IsOpen (C.Jminus ⊤ S \ S)) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      (∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
      (∀ y ∈ C.Jminus ⊤ S \ S, C.Jminus ⊤ S ∈ 𝓝 y) ∧
      (∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) ∧
      IsOpen (C.Jplus ⊤ S \ S) ∧ IsOpen (C.Jminus ⊤ S \ S) ∧ IsClosed S := by
  have hSa : C.IsAcausal S := hS.isAcausal_of_t1_secondCountable hac
  have hcap := IsAcausal.Jplus_inter_Jminus hc hSa
  have hcov := hS.cover_of_t1_secondCountable
  have hPc : (C.Jplus ⊤ S)ᶜ = C.Jminus ⊤ S \ S := by
    ext x
    constructor
    · intro hx
      exact ⟨(hcov x).resolve_left hx, fun hxS => hx ⟨x, hxS, C.le_refl trivial⟩⟩
    · rintro ⟨hx, hxS⟩ hxP
      exact hxS (by rw [← hcap]; exact ⟨hxP, hx⟩)
  have hMc : (C.Jminus ⊤ S)ᶜ = C.Jplus ⊤ S \ S := by
    ext x
    constructor
    · intro hx
      exact ⟨(hcov x).resolve_right hx, fun hxS => hx ⟨x, hxS, C.le_refl trivial⟩⟩
    · rintro ⟨hx, hxS⟩ hxM
      exact hxS (by rw [← hcap]; exact ⟨hx, hxM⟩)
  have hPcl : IsClosed (C.Jplus ⊤ S) := by rw [← isOpen_compl_iff, hPc]; exact hM
  have hMcl : IsClosed (C.Jminus ⊤ S) := by rw [← isOpen_compl_iff, hMc]; exact hP
  refine ⟨hPcl, hMcl, hcap, fun y hy => mem_of_superset (hP.mem_nhds hy) sdiff_subset,
    fun y hy => mem_of_superset (hM.mem_nhds hy) sdiff_subset, hcov, hP, hM, ?_⟩
  rw [← hcap]
  exact hPcl.inter hMcl

/-- Step (3), model-free, at every point: `J⁺(S) ∖ S` is open as soon as each of its points has
a chronological past. -/
theorem IsCauchySurface.isOpen_Jplus_diff_of_Iminus_nonempty [T2Space M]
    [SecondCountableTopology M] (hS : C.IsCauchySurface S) (hc : C.IsCausal)
    (hac : C.CausallyArcConnected) (hchr : ∀ x ∈ S, ¬ C.lt ⊤ x x)
    (hI : ∀ p ∈ C.Jplus ⊤ S \ S, (C.Iminus ⊤ {p}).Nonempty) : IsOpen (C.Jplus ⊤ S \ S) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨O, hO, hpO, hOs⟩ := hS.exists_isOpen_of_Iminus_nonempty hc hac hchr hp (hI p hp)
  exact ⟨O, hOs, hO, hpO⟩

/-- **The model-free form**: in a causal, causally arc-connected spacetime on a Hausdorff, second
countable space with no past endpoint (`J⁻(x) ≠ {x}`) and non-empty chronological cones, the
conclusions of `sigma_separe_of_isOpen` hold for every Cauchy surface. This is the regular case
of the singular one: no BTZ point. -/
theorem IsCauchySurface.sigma_separe_of_nonemptyChronalCones [T2Space M]
    [SecondCountableTopology M] (hS : C.IsCauchySurface S) (hc : C.IsCausal)
    (hac : C.CausallyArcConnected) (hJ : C.NoPastEndpoint) (hI : C.NonemptyChronalCones) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      (∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
      (∀ y ∈ C.Jminus ⊤ S \ S, C.Jminus ⊤ S ∈ 𝓝 y) ∧
      (∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) ∧
      IsOpen (C.Jplus ⊤ S \ S) ∧ IsOpen (C.Jminus ⊤ S \ S) ∧ IsClosed S := by
  have hchr : ∀ x : M, ¬ C.lt ⊤ x x := fun x hxx => by
    apply Jplus_not_mem_nhds hac hc (hJ x)
    refine mem_of_superset ((C.isOpen_lt_right ⊤ x).mem_nhds hxx) fun z hz => ?_
    simpa using C.le_of_lt hz
  exact hS.sigma_separe_of_isOpen hc hac
    (hS.isOpen_Jplus_diff_of_Iminus_nonempty hc hac (fun x _ => hchr x) fun p _ => (hI p).2)
    (IsCauchySurface.isOpen_Jplus_diff_of_Iminus_nonempty (C := C.dual)
      (dual_isCauchySurfaceOn.2 hS) (dual_isCausal.2 hc)
      (dual_causallyArcConnectedOn.2 hac) (fun x _ => hchr x) fun p _ => (hI p).1)

/-! ### Under `SingularFlatAxioms` -/

variable {sing : ℝ → Set M}

/-- Chronology at every point of a causal singular flat spacetime: `x ≪ x` would make `J⁺(x)` a
neighbourhood of `x`, against `Jplus_not_mem_nhds` (`J⁻(x) ≠ {x}`, `Jminus_ne_singleton`). -/
theorem SingularFlatAxioms.not_lt_self (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (x : M) : ¬ C.lt ⊤ x x := by
  haveI := h.t2
  intro hxx
  apply Jplus_not_mem_nhds h.causallyArcConnected hc (h.Jminus_ne_singleton x)
  refine mem_of_superset ((C.isOpen_lt_right ⊤ x).mem_nhds hxx) fun z hz => ?_
  simpa using C.le_of_lt hz

/-- Step (3) at a BTZ point `p ∈ J⁺(S) ∖ S`, where `I⁻(p) = ∅`: the BTZ line `γ` through `p`
(`γ 0 = p`, a closed embedding, `J⁻(p) = γ(]-∞, 0])`) meets `S` at `γ s₀`, `s₀ < 0`; tarentin in
the open set `M ∖ γ(]-∞, s₀])` gives `a = γ t`, `s₀ < t ≤ 0`, with `p ∈ Int J⁺(a)`, and
`Int J⁺(a) ⊆ J⁺(S) ∖ S` (acausality, causality, injectivity of `γ`). -/
theorem SingularFlatAxioms.exists_isOpen_of_mem_sing_zero (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) (hS : C.IsCauchySurface S) {p : M} (hp : p ∈ C.Jplus ⊤ S \ S)
    (hp0 : p ∈ sing 0) :
    ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ O ⊆ C.Jplus ⊤ S \ S := by
  haveI := h.t2
  haveI := h.secondCountable
  have hSa : C.IsAcausal S := hS.isAcausal_of_t1_secondCountable h.causallyArcConnected
  obtain ⟨γ, hγ0, hγe, hγi, hγr⟩ := h.line p hp0
  have hγe' := hγe hc
  have hJm := h.Jminus_eq_image hc hp0 hγ0 hγe' hγi.1 hγr
  obtain ⟨σ, ⟨⟨s₀, -, rfl⟩, hσS⟩, huniq⟩ := hS univ γ hγi
  -- the line meets `S` below `p`: `s₀ < 0`
  have hs₀ : s₀ ≤ 0 := by
    obtain ⟨σ', hσ'S, hσ'p⟩ := hp.1
    have hσ'mem : σ' ∈ C.Jminus ⊤ {p} := by simpa using hσ'p
    rw [hJm] at hσ'mem
    obtain ⟨t', ht', rfl⟩ := hσ'mem
    have heq : t' = s₀ := hγe'.injective (huniq _ ⟨⟨t', trivial, rfl⟩, hσ'S⟩)
    rw [← heq]
    exact ht'
  have hs0 : s₀ < 0 := lt_of_le_of_ne hs₀ fun h0 => hp.2 (by rw [← hγ0, ← h0]; exact hσS)
  -- a neighbourhood of `p` avoiding `γ(]-∞, s₀])`
  have hF : IsClosed (γ '' Iic s₀) := hγe'.isClosedMap _ isClosed_Iic
  have hpF : p ∉ γ '' Iic s₀ := by
    rintro ⟨t, ht, hγt⟩
    have ht0 : t = 0 := hγe'.injective (hγt.trans hγ0.symm)
    rw [ht0] at ht
    exact absurd (lt_of_le_of_lt ht hs0) (lt_irrefl 0)
  obtain ⟨a, ha, b, -, hpab⟩ := h.tarentin p _ (hF.isOpen_compl.mem_nhds hpF)
  have hpa : p ∈ interior (C.Jplus ⊤ {a}) := interior_mono diamond_subset_Jplus hpab
  have hap : C.le ⊤ a p := by simpa using interior_subset hpa
  have haJ : a ∈ C.Jminus ⊤ {p} := by simpa using hap
  rw [hJm] at haJ
  obtain ⟨t, -, rfl⟩ := haJ
  have hst : s₀ < t := by
    by_contra hle
    exact ha ⟨t, not_lt.1 hle, rfl⟩
  have hσa : C.le ⊤ (γ s₀) (γ t) := hγi.1.le_of_le trivial trivial hst.le
  refine ⟨interior (C.Jplus ⊤ {γ t}), isOpen_interior, hpa, ?_⟩
  intro y hy
  have hay : C.le ⊤ (γ t) y := by simpa using interior_subset hy
  refine ⟨⟨γ s₀, hσS, C.le_trans hσa hay⟩, fun hyS => ?_⟩
  have h1 : γ s₀ = y := hSa _ hσS _ hyS (C.le_trans hσa hay)
  rw [← h1] at hay
  have h2 : γ t = γ s₀ := hc hay hσa
  exact hst.ne' (hγe'.injective h2)

/-- Step (3) at every point: `J⁺(S) ∖ S` is open, by the BTZ case at `sing₀` and the regular
case elsewhere (`Z⁻ = M ∖ sing₀`). -/
theorem SingularFlatAxioms.isOpen_Jplus_diff (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hS : C.IsCauchySurface S) : IsOpen (C.Jplus ⊤ S \ S) := by
  haveI := h.t2
  haveI := h.secondCountable
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  by_cases hp0 : p ∈ sing 0
  · obtain ⟨O, hO, hpO, hOs⟩ := h.exists_isOpen_of_mem_sing_zero hc hS hp hp0
    exact ⟨O, hOs, hO, hpO⟩
  · obtain ⟨O, hO, hpO, hOs⟩ := hS.exists_isOpen_of_Iminus_nonempty hc h.causallyArcConnected
      (fun x _ => h.not_lt_self hc x) hp
      (Iminus_nonempty_of_mem_Zminus ((h.mem_Zminus_iff p).2 hp0))
    exact ⟨O, hOs, hO, hpO⟩

/-- Step (4): `J⁻(S) ∖ S` is open, by the regular case of (3) on `C.dual`, every point being in
`Z⁺`: no BTZ case. -/
theorem SingularFlatAxioms.isOpen_Jminus_diff (h : C.SingularFlatAxioms sing) (hc : C.IsCausal)
    (hS : C.IsCauchySurface S) : IsOpen (C.Jminus ⊤ S \ S) := by
  haveI := h.t2
  haveI := h.secondCountable
  exact IsCauchySurface.isOpen_Jplus_diff_of_Iminus_nonempty (C := C.dual)
    (dual_isCauchySurfaceOn.2 hS) (dual_isCausal.2 hc)
    (dual_causallyArcConnectedOn.2 h.causallyArcConnected) (fun x _ => h.not_lt_self hc x)
    fun p _ => Iplus_nonempty_of_mem_Zplus (h.mem_Zplus p)

/-- `lem:Sigma_separe`'s « In particular » at every causal `E_{≥0}`-manifold, for every Cauchy
surface `S`: no splitting `ψ`, no global hyperbolicity. -/
theorem SingularFlatAxioms.sigma_separe_of_isCausal (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) (hS : C.IsCauchySurface S) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      (∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y) ∧
      (∀ y ∈ C.Jminus ⊤ S \ S, C.Jminus ⊤ S ∈ 𝓝 y) ∧
      (∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) ∧
      IsOpen (C.Jplus ⊤ S \ S) ∧ IsOpen (C.Jminus ⊤ S \ S) ∧ IsClosed S := by
  haveI := h.t2
  haveI := h.secondCountable
  exact hS.sigma_separe_of_isOpen hc h.causallyArcConnected (h.isOpen_Jplus_diff hc hS)
    (h.isOpen_Jminus_diff hc hS)

/-- `lem:Sigma_separe`'s « In particular », as printed: `M` globally hyperbolic. -/
theorem SingularFlatAxioms.sigma_separe (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) (hS : C.IsCauchySurface S) :
    IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h.sigma_separe_of_isCausal hG.1 hS
  exact ⟨h1, h2, h3, h4⟩

/-- A BTZ point in `J⁺(S) ∖ S`: the BTZ line through a point of `sing₀` meets `S` once, and its
points above that one are in `J⁺(S) ∖ S`. -/
theorem SingularFlatAxioms.exists_mem_sing_zero_Jplus_diff (h : C.SingularFlatAxioms sing)
    (hc : C.IsCausal) (hS : C.IsCauchySurface S) (hne : (sing 0).Nonempty) :
    ∃ p ∈ sing 0, p ∈ C.Jplus ⊤ S \ S := by
  obtain ⟨p, hp0⟩ := hne
  obtain ⟨γ, -, hγe, hγi, hγr⟩ := h.line p hp0
  have hγe' := hγe hc
  obtain ⟨σ, ⟨⟨s₀, -, rfl⟩, hσS⟩, huniq⟩ := hS univ γ hγi
  refine ⟨γ (s₀ + 1), ?_, ⟨γ s₀, hσS, hγi.1.le_of_le trivial trivial (by linarith)⟩,
    fun hS1 => ?_⟩
  · have hr : γ (s₀ + 1) ∈ range γ := ⟨_, rfl⟩
    rw [hγr] at hr
    exact connectedComponentIn_subset _ _ hr
  · have heq := hγe'.injective (huniq _ ⟨⟨s₀ + 1, trivial, rfl⟩, hS1⟩)
    linarith

/-! ### Witnesses on the timelike line (kb/0011) -/

/-- The hypotheses of `SingularFlatAxioms.sigma_separe` hold on the timelike line with `S = {0}`,
every `sing α` empty: its regular branch only (the BTZ branch is witnessed at `E₀`,
`Causal.Remarks.SingularRowsCauchy`). -/
theorem _root_.Causal.timelikeLine_sigma_separe :
    IsClosed (timelikeLine.Jplus ⊤ ({0} : Set ℝ)) ∧ IsClosed (timelikeLine.Jminus ⊤ ({0} : Set ℝ)) ∧
      timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∩ timelikeLine.Jminus ⊤ {0} = {0} ∧
      ∀ y ∈ timelikeLine.Jplus ⊤ ({0} : Set ℝ) \ {0}, timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∈ 𝓝 y :=
  timelikeLine_singularFlatAxioms.sigma_separe timelikeLine_globallyHyperbolic
    timelikeLine_isCauchySurface_zero

/-- The hypotheses of the model-free `IsCauchySurface.sigma_separe_of_nonemptyChronalCones` hold
on the timelike line with `S = {0}`. -/
theorem _root_.Causal.timelikeLine_sigma_separe_of_nonemptyChronalCones :
    IsClosed (timelikeLine.Jplus ⊤ ({0} : Set ℝ)) ∧ IsClosed (timelikeLine.Jminus ⊤ ({0} : Set ℝ)) ∧
      timelikeLine.Jplus ⊤ ({0} : Set ℝ) ∩ timelikeLine.Jminus ⊤ {0} = {0} ∧
      IsOpen (timelikeLine.Jplus ⊤ ({0} : Set ℝ) \ {0}) ∧
      IsOpen (timelikeLine.Jminus ⊤ ({0} : Set ℝ) \ {0}) := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, -⟩ :=
    timelikeLine_isCauchySurface_zero.sigma_separe_of_nonemptyChronalCones timelikeLine_isCausal
      timelikeLine_causallyArcConnected timelikeLine_Jminus_ne timelikeLine_nonemptyChronalCones
  exact ⟨h1, h2, h3, h7, h8⟩

end Causality

end Causal
