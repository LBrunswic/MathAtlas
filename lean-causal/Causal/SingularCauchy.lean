import Causal.SingularGeroch
import Causal.CauchySeparation

/-!
# A Cauchy surface separates, without the splitting: the « In particular » of `lem:Sigma_separe` under `SingularFlatAxioms`

Target `T-ett-sigma-separe`, part (a). Cited, unmarked (SCOPE): `lem:Sigma_separe` —
`ETT.tex:2062`, its « In particular » (l.2067–2068), for every Cauchy surface and with no
homeomorphism `ψ`. The two equalities `J^±(Σ) = ψ(Σ × ℝ_±)` are not stated here: they stay
`Causality.sigma_separe` (`Causal.CauchyDiamond`), under a named `ψ`. This module imports no model
space, but it is of the model layer (`tools/ladder.py`) through `Causal.SingularGeroch`, which
imports `Causal.SingularFlat`; its model-free steps are in the ETT-layer `Causal.CauchySeparation`.

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
* The steps, model-free, in the ETT-layer `Causal.CauchySeparation` (moved there verbatim, same
  full names, T-abs-hoist-dual-cover), imported here.
  (1) `IsCauchySurface.cover_of_t1_secondCountable`: `M = J⁺(S) ∪ J⁻(S)` on every T1, second
  countable space, for any causality (the `hcover` of `lem:image_diamant`).
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
* Witnesses (kb/0011): the timelike line with `S = {0}` (`timelikeLine_sigma_separe`; the
  model-free form's, `timelikeLine_sigma_separe_of_nonemptyChronalCones`, is in
  `Causal.CauchySeparation`), regular branch only. The BTZ branch is
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
`Causal.SingularGeroch` (`Jminus_ne_singleton`, through `Causal.Geroch` `Jplus_not_mem_nhds`) and
`Causal.CauchySeparation` (the model-free steps; through it `Causal.CurvesExtendSecondCountable`,
`Causal.CauchyDual` and `Causal.ChronalNeighbourBridge`, which this module imported directly until
T-abs-hoist-dual-cover); not `Causal.Splitting`, which imports a model (`Causal.Flat.IsomCausal`).
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

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

end Causality

end Causal
