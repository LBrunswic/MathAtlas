import GX.Spherical.ConeSurface

/-!
# Troyanov's theorem with the Thurston suspension, at `(SO(4), 𝕊³)`, tied to the cone angles

Target `T-gx-spherical-cone` (`roadmap/roadmap.toml`; DEC-136, its first step: the objects and
the angle-tied statement, not the proof of Troyanov's theorem). `papers/gx`,
`cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930–1937`). **No label is marked**;
two tagged `sorry`s, the obligations of `T-gx-troyanov` and `T-gx-troyanov-suspension`.

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial. Its statement, at
  the paper's `(SO(4), 𝕊³)` and **tied to the angles**, is the `Prop`
  `GX.TroyanovSuspensionTheoremS3`: for `s ≥ 3` pairwise distinct angles satisfying Troyanov's
  condition there is a cone sphere `Σ` with cone points `p_i` of angles `θ_i`
  (`GX.IsConeSphere`), and its Thurston suspension `susp(Σ)` (`GX.thurstonSuspension`, a singular
  `(SO(4), 𝕊³)`-manifold) has singular locus its centre and the rays over the `p_i` of angle
  `≠ 2π`, and the facts the cex derives at the centre (`GX.ThurstonCexFacts`). It splits as
  `GX.TroyanovTheorem` (MR1005085) and `GX.ThurstonSuspensionFacts` (l.1931–1937):
  `GX.troyanovSuspensionTheoremS3_of` (0 `sorry`). **Relation to DEC-69's named `Prop`**: it
  implies `GX.TroyanovSuspensionTheorem SO4 Sph3`
  (`GX.TroyanovSuspensionTheoremS3.troyanovSuspensionTheorem`, 0 `sorry`), whose
  `GX.SuspensionCexFacts` it carries at the centre. The cex's conclusion at `(SO(4), 𝕊³)`:
  `GX.cex_start_singular_manifold_homeomorphic_S3` (0 `sorry` from the `Prop`).
  The obligations, stated with tagged `sorry`: `GX.troyanovTheorem`,
  `GX.thurstonSuspensionFacts`; hence `GX.troyanovSuspensionTheoremS3`.
* The angle condition: `GX.troyanovAngleCondition_two_pi` (it admits an angle `2π`, a marked
  regular point), `GX.TroyanovAngleCondition.three_le_card_ne_two_pi` (it forces at least
  three angles `≠ 2π`, so at least three genuine cone points), and
  `GX.TroyanovAngleCondition.subcritical` (`0 < χ' < 4π`, `χ' < 2θᵢ`: the subcritical
  hypothesis of `MR1005085` as recalled, unchecked against the source).

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. We know from
> Troyanov \cite{MR1005085} that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> Apply the Thurston suspension method described in Section \ref{sec:susp}, the constructed
> manifold $M$ is a singular $(\SO(4),\SS^3)$-manifold (we may either apply by Proposition
> \ref{prop:susp_portly} or check that directly). We call $O$ its center. (l.1930–1931)
>
> An automorphism of $M$ has to fix $O$ since singular locus is homeomorphic to a line except at
> $O$, furthermore it preserves distances and geodesics. By considering the sphere of some radius
> $\varepsilon>0$ centered at $O$ we see that the natural map $\Aut(\Sigma)\rightarrow \Aut(M)$
> is a group isomorphism. As a consequence, except for very particular $\Sigma$, $\Aut(M)$ is
> trivial. For instance, if all the $\theta_i$ are different then $\Aut(M)=\{Id\}$. These remarks
> hold for all neighborhoods of $O$. (l.1933)
>
> For a generic $\Sigma$, since locally we may construct a rotation around any of the axes and
> since those cannot be extended as automorphism of $M$, we conclude that for
> $S\subset \sing(M)$, $(M,S)$ is analytic if and only if $S=\{O\}$. (l.1935)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` a singular `𝕊²`-manifold homeomorphic to a sphere, `s ≥ 3` conical singularities of angles `θ_i` (l.1930) | ✓ `IsConeSphere M θ p` (`GX.Spherical.ConeSurface`); `s ≥ 3` is in `TroyanovAngleCondition`; an angle `2π` is a marked regular point (SCOPE (c)) |
| Troyanov's condition (l.1930) | ✓ `GX.TroyanovAngleCondition`, verbatim (DEC-69's) |
| Troyanov's theorem (MR1005085) | stated: `TroyanovTheorem`; to be proved (DEC-136), `troyanovTheorem` is a tagged `sorry` |
| the Thurston suspension, a singular `(SO(4), 𝕊³)`-manifold (l.1931) | ✓ built: `thurstonSuspension` (`GX.thurstonStructure`, an a.e. atlas proved, 0 `sorry`) |
| "generic `Σ`" (l.1935) | ✓ read as DEC-69 read it: the `θ_i` pairwise distinct (the paper's instance, l.1933) |
| the facts of l.1933–1935 | stated: `ThurstonCexFacts` (singular locus, `SuspensionCexFacts` at `O`); `thurstonSuspensionFacts` is a tagged `sorry` |

## SCOPE (disclosed)

* **(a)** "As the paper means it": the cex is a statement about the suspension of a surface with
  the PRESCRIBED angles; the `Prop` asserts the surface (`IsConeSphere M θ p`, angles `θ_i` at
  the `p_i`, no other singular point) and the facts for ITS suspension, so the angles enter
  through `Σ` and through the singular locus of `M` (`ThurstonCexFacts.sing_eq`). The facts at
  `O` are DEC-69's `SuspensionCexFacts` (the paper's `Aut(Σ) ≅ Aut(M)` is not stated; the local
  rigidity `rigid` is the form the cex's conclusion uses, "these remarks hold for all
  neighborhoods of `O`").
* **(b)** The suspension is read as the open ball of radius `π` about `O`
  (`GX.Spherical.S3Model`, SCOPE (b)): a single centre `O`, and the singular locus is
  "homeomorphic to a line except at `O`", as l.1933 says; the closed suspension (`r ∈ [0, π]`,
  both ends collapsed) would have a second centre. (With `r` over all of `ℝ₊` the printed metric
  degenerates at every `r = kπ` and is locally spherical again between: not a Riemannian
  cone-manifold, so one of these two models is meant.)
* **(c)** Troyanov's condition admits `θ_i = 2π` (`troyanovAngleCondition_two_pi`), a marked
  regular point; it forces at least three angles `≠ 2π`
  (`TroyanovAngleCondition.three_le_card_ne_two_pi`). `ThurstonCexFacts.sing_eq` takes the rays
  over the cone points of angle `≠ 2π` only.
* **(d)** The universes: `Σ : Type` (as DEC-69's `Prop`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.ConeSurface`, `GX.Spherical.S3Model`, `GX.SingularII.Models`
(`TroyanovAngleCondition`, `SuspensionCexFacts`, `TroyanovSuspensionTheorem`).
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace NNReal

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### Troyanov's condition and the angle `2π` -/

section Angles

/-- **Troyanov's condition admits an angle `2π`**, which marks a regular point: `s = 4` pairwise
distinct angles `(9π/10, 19π/20, π, 2π)` satisfy it (`∑ (θ_i − 2π) + 4π = 17π/20`). So the
paper's "`s` conical singularities" (l.1930) are `s` cone points, one of which may be regular. -/
theorem troyanovAngleCondition_two_pi :
    TroyanovAngleCondition ![9 * π / 10, 19 * π / 20, π, 2 * π] ∧
      Pairwise fun i j => ![9 * π / 10, 19 * π / 20, π, 2 * π] i ≠
        ![9 * π / 10, 19 * π / 20, π, 2 * π] j := by
  have hπ := Real.pi_pos
  refine ⟨⟨by norm_num, ?_, ?_, fun j => ?_⟩, fun i j hij => ?_⟩
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linarith
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linarith
  · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    fin_cases j <;> simp <;> linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

/-- **Troyanov's condition forces at least three angles `≠ 2π`**: whatever the number of marked
regular points (`θ_i = 2π`), a cone sphere with angles satisfying the condition has at least three
genuine conical singularities — the paper's "`s ≥ 3` conical singularities" (l.1930) holds for
the singular ones. -/
theorem TroyanovAngleCondition.three_le_card_ne_two_pi {s : ℕ} {θ : Fin s → ℝ}
    (h : TroyanovAngleCondition θ) : 3 ≤ (Finset.univ.filter fun i => θ i ≠ 2 * π).card := by
  set F := Finset.univ.filter fun i => θ i ≠ 2 * π
  have hsum : ∑ i, (θ i - 2 * π) = ∑ i ∈ F, (θ i - 2 * π) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ i ≠ 2 * π)]
    have : ∑ i ∈ Finset.univ.filter (fun i => ¬ θ i ≠ 2 * π), (θ i - 2 * π) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter, not_not] at hi; rw [hi.2, sub_self]
    rw [this, add_zero]
  have hχ := h.2.2.2
  have hpos := h.pos
  rw [hsum] at hχ
  by_contra hlt
  rw [not_le] at hlt
  interval_cases hc : F.card
  · rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.sum_empty, zero_add] at hχ
    have hs : 0 < s := by have := h.1; omega
    have h0 : θ ⟨0, hs⟩ = 2 * π := by
      by_contra hne
      have : (⟨0, hs⟩ : Fin s) ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
      rw [hc] at this; exact Finset.notMem_empty _ this
    have := hχ ⟨0, hs⟩
    rw [h0] at this
    linarith [Real.pi_pos]
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    rw [ha, Finset.sum_singleton] at hχ
    linarith [hχ a, Real.pi_pos]
  · obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.1 hc
    rw [hF, Finset.sum_pair hab] at hχ
    linarith [hχ a, hpos b]

/-- **The paper's condition is subcritical**: with `χ' = ∑ (θᵢ − 2π) + 4π`, it gives
`0 < χ' < 4π` and `χ' < 2θᵢ` — the bound `χ' ≤ 4π` of l.1930 is never attained (it would force
`θᵢ ≥ 4π` for all `i`). This is the hypothesis `0 < χ < min(2, 2 + 2 min βᵢ)` (`χ = χ'/2π`,
`θᵢ = 2π(1 + βᵢ)`) under which, as recalled here, `MR1005085` proves the existence of a spherical
cone metric; the recollection is NOT checked against the source, which is not in
`papers/gx/sources` (for `T-gx-troyanov` to verify). -/
theorem TroyanovAngleCondition.subcritical {s : ℕ} {θ : Fin s → ℝ} (h : TroyanovAngleCondition θ) :
    0 < ∑ i, (θ i - 2 * π) + 4 * π ∧ ∑ i, (θ i - 2 * π) + 4 * π < 4 * π ∧
      ∀ j, ∑ i, (θ i - 2 * π) + 4 * π < 2 * θ j := by
  refine ⟨h.2.1, lt_of_le_of_ne h.2.2.1 fun heq => ?_, fun j => ?_⟩
  · have hge : ∀ j, 4 * π ≤ θ j := fun j => heq ▸ h.2.2.2 j
    have hsum : ∑ i : Fin s, (2 * π) ≤ ∑ i, (θ i - 2 * π) :=
      Finset.sum_le_sum fun i _ => by linarith [hge i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hs : (3 : ℝ) ≤ s := by exact_mod_cast h.1
    nlinarith [Real.pi_pos]
  · linarith [h.2.2.2 j, h.pos j]

end Angles

/-! ### The Thurston suspension of a spherical surface, as a singular `(SO(4), 𝕊³)`-manifold -/

section Suspension

/-- The direction assigned to the apex by the conic chart (immaterial: the apex is one point). -/
abbrev sph2Base : Sph2 := northPole

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- **The Thurston suspension `susp(M)` of a connected, locally connected singular
`(SO(3), 𝕊²)`-manifold `M`, as a singular `(SO(4), 𝕊³)`-manifold** (`RamcovGX.tex:1931`, method of
`sec:susp`, l.694–700): the maximal a.e. atlas generated by the cone charts
`(σ, r) ↦ φ⁻¹(e(σ), r) ∈ 𝕊³` of the charts `e` of `M`, `φ` the conic chart of `𝕊³` at the north
pole (`GX.thurstonStructure`, `GX.sphConic`). The point `(σ, r)` sits at spherical distance
`2 arctan r` from the centre `O = {r = 0}`. -/
@[reducible] def thurstonSuspension [PreconnectedSpace M] [LocallyConnectedSpace M] :
    SingularGXStructure SO4 Sph3 (Susp M) :=
  thurstonStructure sph2Base M

/-- The rays over the regular points of `M` are regular in its Thurston suspension. -/
theorem thurstonSuspension_mk_mem_reg [PreconnectedSpace M] [LocallyConnectedSpace M] {x : M}
    (hx : x ∈ Reg SO3 Sph2 M) {t : ℝ≥0} (ht : 0 < t) :
    letI := thurstonSuspension (M := M)
    Susp.mk (x, t) ∈ Reg SO4 Sph3 (Susp M) :=
  thurston_mk_mem_reg hx ht

/-- **The facts of `cex:start_singular_manifold_homeomorphic` for the Thurston suspension `M̂` of a
cone sphere `(M, p, θ)`, tied to the angles** (`RamcovGX.tex:1933–1937`):
* `sing_eq`: the singular locus of `M̂` is its centre `O` and the open rays over the cone points of
  angle `θ_i ≠ 2π` (l.1933: "singular locus is homeomorphic to a line except at `O`");
* `cexFacts`: at the centre, the facts the cex derives (`GX.SuspensionCexFacts`: `M̂` connected,
  `O` singular with another singular point, every a.e. isomorphism of connected open sets whose
  domain contains `O` the identity, a non-extendable local isomorphism around every other singular
  point). -/
structure ThurstonCexFacts [PreconnectedSpace M] [LocallyConnectedSpace M] {s : ℕ}
    (θ : Fin s → ℝ) (p : Fin s → M) : Prop where
  sing_eq : letI := thurstonSuspension (M := M)
    Sing SO4 Sph3 (Susp M) = Susp.O ∪ Susp.mk '' ((p '' {i | θ i ≠ 2 * π}) ×ˢ Ioi 0)
  cexFacts : letI := thurstonSuspension (M := M)
    ∀ O ∈ (Susp.O : Set (Susp M)), SuspensionCexFacts SO4 Sph3 (Susp M) O

end Suspension

/-! ### The three statements -/

section Statements

/-- **Troyanov's theorem** (`MR1005085`, as cited at `RamcovGX.tex:1930`): for `s ≥ 3` angles
`θ_i` with `0 < ∑ (θ_i − 2π) + 4π ≤ min(4π, θ_i)` (`GX.TroyanovAngleCondition`), there is a
spherical cone sphere with cone points of angles `θ_1, …, θ_s` (`GX.IsConeSphere`). -/
def TroyanovTheorem : Prop :=
  ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p

/-- **The Thurston suspension facts** (`RamcovGX.tex:1931–1937`): the Thurston suspension of every
cone sphere whose angles satisfy Troyanov's condition and are pairwise distinct (the paper's
"generic `Σ`", read through its instance "all the `θ_i` different", l.1935) has the facts of the
cex, tied to the angles (`ThurstonCexFacts`). -/
def ThurstonSuspensionFacts : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M] {s : ℕ} (θ : Fin s → ℝ)
    (p : Fin s → M) (h : IsConeSphere M θ p), TroyanovAngleCondition θ →
    Pairwise (fun i j => θ i ≠ θ j) →
      haveI := h.connectedSpace
      haveI := h.locallyConnectedSpace
      ThurstonCexFacts θ p

/-- **Troyanov's theorem with the Thurston suspension, at `(SO(4), 𝕊³)`, tied to the cone angles**
(`cex:start_singular_manifold_homeomorphic`, `RamcovGX.tex:1930–1937`, as the paper means it):
for `s ≥ 3` pairwise distinct angles satisfying Troyanov's condition there is a spherical cone
sphere `Σ` with cone points `p_i` of angles `θ_i`, and its Thurston suspension `M = susp(Σ)`, a
singular `(SO(4), 𝕊³)`-manifold, has singular locus the centre and the rays over the `p_i` of angle
`≠ 2π`, and the facts the cex derives at its centre. The angle-free form at a general `(G, X)` is
`GX.TroyanovSuspensionTheorem` (DEC-69); this one implies it at `(SO(4), 𝕊³)`
(`TroyanovSuspensionTheoremS3.troyanovSuspensionTheorem`). -/
def TroyanovSuspensionTheoremS3 : Prop :=
  ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ → Pairwise (fun i j => θ i ≠ θ j) →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M)
      (h : IsConeSphere M θ p),
        haveI := h.connectedSpace
        haveI := h.locallyConnectedSpace
        ThurstonCexFacts θ p

/-- The tied statement is Troyanov's theorem followed by the suspension facts. -/
theorem troyanovSuspensionTheoremS3_of (hT : TroyanovTheorem) (hS : ThurstonSuspensionFacts) :
    TroyanovSuspensionTheoremS3 := by
  intro s θ hθ hd
  obtain ⟨M, _, _, p, h⟩ := hT θ hθ
  exact ⟨M, _, _, p, h, hS M θ p h hθ hd⟩

/-- **The tied statement implies DEC-69's named `Prop` at `(SO(4), 𝕊³)`**: forgetting `Σ` and the
angles, `susp(Σ)` with its centre is a witness of `GX.TroyanovSuspensionTheorem SO4 Sph3`. -/
theorem TroyanovSuspensionTheoremS3.troyanovSuspensionTheorem (h : TroyanovSuspensionTheoremS3) :
    TroyanovSuspensionTheorem SO4 Sph3 := by
  intro s θ hθ hd
  obtain ⟨M, _, _, p, hM, hF⟩ := h θ hθ hd
  haveI := hM.connectedSpace
  haveI := hM.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  have hs : 0 < s := by have := hθ.1; omega
  exact ⟨Susp M, inferInstance, inferInstance, thurstonSuspension (M := M),
    Susp.mk (p ⟨0, hs⟩, 0), hF.cexFacts _ rfl⟩

/-- **`cex:start_singular_manifold_homeomorphic` at `(SO(4), 𝕊³)`, tied to the angles**
(`RamcovGX.tex:1930–1937`), from the tied statement: for `s ≥ 3` pairwise distinct angles satisfying
Troyanov's condition there is a cone sphere `Σ` with cone points of angles `θ_i` whose Thurston
suspension `M` is connected, has singular locus its centre `O` and the rays over the cone points of
angle `≠ 2π`, and for `S ⊆ sing(M)`, `(M, S)` is analytic iff `S = {O}` — in particular
`(M, sing M)` is not analytic. -/
theorem cex_start_singular_manifold_homeomorphic_S3 (h : TroyanovSuspensionTheoremS3) {s : ℕ}
    (θ : Fin s → ℝ) (hθ : TroyanovAngleCondition θ) (hd : Pairwise fun i j => θ i ≠ θ j) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M)
      (hM : IsConeSphere M θ p),
        haveI := hM.connectedSpace
        haveI := hM.locallyConnectedSpace
        letI := thurstonSuspension (M := M)
        Sing SO4 Sph3 (Susp M) = Susp.O ∪ Susp.mk '' ((p '' {i | θ i ≠ 2 * π}) ×ˢ Ioi 0) ∧
        ∀ O ∈ (Susp.O : Set (Susp M)), ConnectedSpace (Susp M) ∧ O ∈ Sing SO4 Sph3 (Susp M) ∧
          (∃ y ∈ Sing SO4 Sph3 (Susp M), y ≠ O) ∧
          (¬ IsAnalyticModelFamily SO4 Sph3 (fun _ : Unit => Susp M)
            (fun _ => Sing SO4 Sph3 (Susp M))) ∧
          ∀ S ⊆ Sing SO4 Sph3 (Susp M),
            (IsAnalyticModelFamily SO4 Sph3 (fun _ : Unit => Susp M) (fun _ => S) ↔ S = {O}) := by
  obtain ⟨M, _, _, p, hM, hF⟩ := h θ hθ hd
  haveI := hM.connectedSpace
  haveI := hM.locallyConnectedSpace
  letI := thurstonSuspension (M := M)
  refine ⟨M, _, _, p, hM, hF.sing_eq, fun O hO => ?_⟩
  have hO' := hF.cexFacts O hO
  refine ⟨hO'.connected, hO'.mem_sing, hO'.exists_ne, fun ha => ?_,
    fun S hS => hO'.isAnalyticModelFamily_unit_iff hS⟩
  obtain ⟨t, ht, htO⟩ := hO'.exists_ne
  have hsO := (hO'.isAnalyticModelFamily_unit_iff subset_rfl).1 ha
  exact htO (by rw [hsO] at ht; exact ht)

end Statements

/-! ### The obligations (DEC-136): stated, not proved here -/

section Obligations

/-- **Troyanov's theorem**, to be proved (DEC-136, target `T-gx-troyanov`). -/
theorem troyanovTheorem : TroyanovTheorem := by
  sorry -- SORRY(cex:start_singular_manifold_homeomorphic): Troyanov's existence theorem for
  -- spherical cone metrics on `S²` with prescribed angles (MR1005085, cited at l.1930), DEC-136;
  -- target `T-gx-troyanov`. The library has the cone `C_θ` and cone spheres
  -- (`GX.Spherical.ConeSurface`), not yet a construction of one with `s ≥ 3` cone points
  -- (e.g. by gluing spherical triangles, or the variational method).

/-- **The Thurston suspension facts**, to be proved (target `T-gx-troyanov-suspension`). -/
theorem thurstonSuspensionFacts : ThurstonSuspensionFacts := by
  sorry -- SORRY(cex:start_singular_manifold_homeomorphic): the facts of l.1933–1937 for
  -- `susp(Σ)`: the rays over singular points are singular (as `GX.ConicStructure.mk_mem_sing`, for
  -- the Thurston atlas, compact link), `O` is singular (in the closure of the singular rays); an
  -- isomorphism near `O` fixes `O` (the singular locus is a star at `O`, an arc elsewhere), is an
  -- isometry and induces an automorphism of `Σ` (the `ε`-sphere about `O`), trivial when the angles
  -- are distinct and `s ≥ 3`; the rotations about a singular ray do not extend. Target
  -- `T-gx-troyanov-suspension`.

/-- The tied statement, from the two obligations. -/
theorem troyanovSuspensionTheoremS3 : TroyanovSuspensionTheoremS3 :=
  troyanovSuspensionTheoremS3_of troyanovTheorem thurstonSuspensionFacts

end Obligations

end GX
