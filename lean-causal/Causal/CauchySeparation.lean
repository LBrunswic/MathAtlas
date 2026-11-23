import Causal.CurvesExtendSecondCountable
import Causal.CauchyDual
import Causal.ChronalNeighbourBridge

/-!
# A Cauchy surface separates: the model-free steps of `lem:Sigma_separe`'s « In particular »

No label is marked (SCOPE). Cited, unmarked: `lem:Sigma_separe` — `ETT.tex:2062`, its « In
particular » (l.2067–2068), and the cover `M = J⁺(Σ) ∪ J⁻(Σ)` that the proof of
`lem:image_diamant` (`ETT.tex:2024`) uses. These are the model-free steps of
`Causal.SingularCauchy`, moved here verbatim with the same full names (T-abs-hoist-dual-cover), so
that a layer-1 module may use them. This module imports `Causal.CurvesExtendSecondCountable`,
`Causal.CauchyDual` and `Causal.ChronalNeighbourBridge`, all ETT-layer: no model, transitively.
`Causal.SingularCauchy` keeps the steps under `SingularFlatAxioms`; it reaches
`Causal.SingularFlat` through `Causal.SingularGeroch`.

> Let $M$ be a globally hyperbolic singular flat spacetime, let $\Sigma$ be a Cauchy surface of
> $M$ and let $\psi:\Sigma\times \RR\rightarrow M$ be the homeomorphism of Theorem
> \ref{theo:geroch_sing}. Then
> $$J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)\qquad\text{and}\qquad
> J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right).$$
> In particular $J^\pm(\Sigma)$ are closed, $J^+(\Sigma)\cap J^-(\Sigma)=\Sigma$, and
> $J^+(\Sigma)$ is a neighbourhood of each of its points outside $\Sigma$.
> (`lem:Sigma_separe`, `ETT.tex:2062–2069`)

## What is proved (no `sorry` in this file)

Steps numbered as in `Causal.SingularCauchy`.

* (1) `IsCauchySurface.cover_of_t1_secondCountable`: `M = J⁺(S) ∪ J⁻(S)` for every Cauchy surface
  `S`, on every T1, second countable space, for any causality.
* (2) `IsAcausal.Jplus_inter_Jminus`: `J⁺(S) ∩ J⁻(S) = S` for an acausal `S` of a causal
  spacetime.
* The connectedness step `CausalCurveIn.mem_image_of_between`, Hausdorff and causal only.
* (3) at a point with a chronological past, `IsCauchySurface.exists_isOpen_of_Iminus_nonempty`; at
  every point of `J⁺(S) ∖ S` that has one, `isOpen_Jplus_diff_of_Iminus_nonempty`.
* (5) `IsCauchySurface.sigma_separe_of_isOpen`: once `J^±(S) ∖ S` are open, `J^±(S)` are closed,
  `J⁺(S) ∩ J⁻(S) = S`, each `J^±(S)` is a neighbourhood of its points outside `S`,
  `M = J⁺(S) ∪ J⁻(S)` and `S` is closed.
* The regular case in one statement: `IsCauchySurface.sigma_separe_of_nonemptyChronalCones`
  (causal, causally arc-connected, `NoPastEndpoint`, `NonemptyChronalCones`). Its witness
  (kb/0011) is the timelike line with `S = {0}`
  (`timelikeLine_sigma_separe_of_nonemptyChronalCones`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` a singular flat spacetime | ⚠ weakened: any causality on a topological space; step (2) asks nothing of the space, the connectedness step that it be Hausdorff, (1) and (5) T1 and second countable, (3) and the regular form Hausdorff and second countable; causal and causally arc-connected where a step says so |
| `M` globally hyperbolic | ⚠ weakened: not used |
| `Σ` a Cauchy surface of `M` | ✓ carried (DEC-14) |
| `ψ : Σ × ℝ → M`, the homeomorphism of `theo:geroch_sing` | ⚠ weakened: not used (the « In particular » only) |
| — (step (3)) | ⚠ strengthened: `hchr : ∀ x ∈ S, ¬ x ≪ x` (`Σ` chronological at its points), asked by `IsCauchySurface.exists_isOpen_of_Iminus_nonempty` and `isOpen_Jplus_diff_of_Iminus_nonempty`; in the regular form it is derived from causality, causal arc-connectedness and `NoPastEndpoint` |
| — (in the regular form) | ⚠ strengthened: `NoPastEndpoint` and `NonemptyChronalCones`, which fail at a BTZ point; the singular case is `SingularFlatAxioms.sigma_separe_of_isCausal` (`Causal.SingularCauchy`) |

## SCOPE (disclosed)

* **Moved, not restated** (T-abs-hoist-dual-cover, 2026-11-23): the section "Model-free steps" of
  `Causal.SingularCauchy` and its witness `timelikeLine_sigma_separe_of_nonemptyChronalCones`,
  verbatim. The route, and why no closedness of `J^±(x)` is needed, are disclosed in
  `Causal.SingularCauchy`'s SCOPE.
* **Why unmarked.** Only the « In particular » is in reach, and here only through the openness of
  `J^±(S) ∖ S` (step (5)) or in the regular case. The BTZ case and the singular assembly are in
  `Causal.SingularCauchy`; the equalities `J^±(Σ) = ψ(Σ × ℝ_±)` stay `Causality.sigma_separe`
  (`Causal.CauchyDiamond`), under a named `ψ`.
* **Twins, kept under their names.** `IsCauchyEmbedding.mem_Jplus_union_Jminus_of_secondCountable`
  (`Causal.CExtConnexeSecondCountable`), the cover on the source of a Cauchy embedding, now cites
  step (1). `Causality.mem_Jplus_union_Jminus_of_isCauchySurface` (`Causal.CorrespondingPoints`)
  is step (1) under a named `CurvesExtend`. `Causality.Jplus_inter_Jminus_eq` (`Causal.CBG.Ppcm`,
  which imports a model) states step (2).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
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

/-! ### Witness on the timelike line (kb/0011) -/

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
