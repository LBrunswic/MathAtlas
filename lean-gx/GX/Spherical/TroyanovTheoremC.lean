import GX.Spherical.TroyanovFour

/-!
# Troyanov's theorem under the condition of his Theorem C (DEC-174); the paper cites less

Target `T-gx-troyanov-theorem-c` (`roadmap/roadmap.toml`; DEC-174, ruling OQ-59; DEC-136).
`papers/gx`, `cex:start_singular_manifold_homeomorphic` (`RamcovGX.tex:1930`). **No label is
marked**. This module is `sorry`-free; the obligation, Troyanov's existence theorem in the case no
construction of the library reaches, is `GX.troyanovTheoremC`, a tagged `sorry` in the scaffold
`GXScaffold.Spherical.TroyanovAngles` (target `T-gx-troyanov`).

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial, not marked. The
  cited theorem (`MR1005085`) with the condition of record ruled by DEC-174, Theorem C's
  `0 < 2πχ(𝕊²) + ∑ (θ_i − 2π) < min{4π, 2θ_min}`: the predicate **`GX.TroyanovAngleConditionC`**
  and the `Prop` **`GX.TroyanovTheoremC`**, the statement of record (DEC-174); the scaffold's
  `GX.TroyanovTheorem` (`GXScaffold.Spherical.TroyanovAngles`, the printed condition) now follows
  from its obligation `GX.troyanovTheoremC`.
* **The paper's citation is narrower** (OQ-59's finding as Lean facts, 0 `sorry`): the printed
  condition (`GX.TroyanovAngleCondition`, DEC-69's verbatim reading) is Theorem C's together with
  `χ' ≤ θ_j` for every `j` (`GX.troyanovAngleCondition_iff_troyanovAngleConditionC`), so it implies
  it (`GX.TroyanovAngleCondition.troyanovAngleConditionC`) and `GX.TroyanovTheoremC` implies the
  body of `GX.TroyanovTheorem` (`GX.TroyanovTheoremC.troyanovTheorem`); the converse of the
  conditions fails, with a cone sphere (`GX.troyanovAngleConditionC_three_not_printed`,
  `(7π/5, 13π/10, π)`, and `GX.troyanovAngleConditionC_four_not_printed`, `(5π/2, 9π/10, π,
  11π/10)`, one angle above `2π`).
* Theorem C's condition read off the source: its verbatim form, the minimum of the angles,
  `GX.troyanovAngleConditionC_iff_inf'`; with `θ_1 ≤ ⋯ ≤ θ_n` and `θ_1` the least,
  `GX.troyanovAngleConditionC_iff_of_monotone`; the minimum over the angles `≠ 2π` is the same
  condition, `GX.troyanovAngleConditionC_iff_ne_two_pi`, and a marked point of angle `2π` can be
  removed or added, `GX.troyanovAngleConditionC_removeNth_iff`. It forces `s ≥ 3`
  (`GX.TroyanovAngleConditionC.three_le`) and positive angles (`.pos`); it is sufficient, not
  necessary (`GX.exists_isConeSphere_not_troyanovAngleConditionC`, the football).
* **What the strict library already proves under Theorem C's condition** (0 `sorry`): every angle
  `≤ 2π`, any `s` (`GX.troyanovTheoremC_of_le_two_pi`); `s = 3` (`GX.troyanovTheoremC_three`);
  `s = 4` (`GX.troyanovTheoremC_four`, the dart for an angle above `2π`). So `GX.TroyanovTheoremC`
  is equivalent to its case `s ≥ 5`, every `θ_i ≠ 2π`, some `θ_i > 2π`
  (`GX.troyanovTheoremC_iff_five_le_of_exists_gt_two_pi`), a case strictly wider than the printed
  one (`GX.troyanovAngleConditionC_five_not_printed`).

> **Theorem C.** Let $S$ be a compact Riemann surface. Let $p_1, p_2, \dots, p_n$ be points of
> $S$ and $\theta_1 \le \theta_2 \le \cdots \le \theta_n$ be positive numbers. Assume
> $$0 < 2\pi\chi(S) + \sum_{i=1}^{n} (\theta_i - 2\pi) < \min\{4\pi, 2\theta_1\}.$$
> Then any smooth function on $S$, which is positive at some point is the curvature of a
> conformal metric having at $p_i$ a conical singularity of angle $\theta_i$.
> (`MR1005085`, p. 795, transcribed in `papers/gx/sources/MR1005085/NOTE.md`)
>
> We know from Troyanov \cite{MR1005085} that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> (`RamcovGX.tex:1930`)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `S` a compact Riemann surface (Th. C) | ⚠ narrowed to `S = 𝕊²` (`2πχ(S) = 4π`), what l.1930 cites it for (SCOPE (a)) |
| a sphere (l.1930) | ✓ `S = 𝕊²` |
| l.1930's printed condition `0 < ∑(θ_i − 2π) + 4π ≤ min(4π, θ_i)` | ⚠ weakened to Theorem C's (DEC-174): the printed one is C plus `χ' ≤ θ_j` (`troyanovAngleCondition_iff_troyanovAngleConditionC`) |
| `θ_1 ≤ ⋯ ≤ θ_n` positive (Th. C) | ⚠ weakened: unordered (`_iff_of_monotone`), `> 0` derived |
| `0 < 2πχ(S) + ∑ (θ_i − 2π) < min{4π, 2θ_1}` (Th. C) | ✓ `TroyanovAngleConditionC` |
| `s ≥ 3` (l.1930) | ⚠ weakened: derived (`TroyanovAngleConditionC.three_le`) |
| Troyanov's theorem, cited | proved for `s ≤ 4` or all `θ_i ≤ 2π`; the rest: SCOPE (e) |

## SCOPE (disclosed)

* **(a)** `TroyanovTheoremC` is Theorem C at `S = 𝕊²` and constant curvature `1` with the points
  not prescribed: it asserts a spherical cone sphere with the angles `θ_i` exists, which is what
  l.1930 uses ("one can construct such a surface"). The conformal position of the `p_i` and the
  prescribed curvature function are not stated (the library has no conformal structure).
* **(b)** "Conical singularity of angle `θ`" is the library's `GX.IsConePoint` (an `X_θ`-chart,
  OQ-37 (b)), an angle `2π` a marked regular point, as in `GX.TroyanovTheorem`.
* **(c)** The conclusion is the body of `GX.TroyanovTheorem` with the condition replaced; the
  scaffold `TroyanovAngles` is not imported (it imports this module), so
  `GX.TroyanovTheoremC.troyanovTheorem` states its conclusion inline: it typechecks as
  `GX.TroyanovTheorem` by unfolding.
* **(d)** The suspension statements of `TroyanovAngles` (`GX.ThurstonSuspensionFacts`,
  `GX.TroyanovSuspensionTheoremS3`) keep the printed condition; DEC-174 names `GX.TroyanovTheorem`
  only (a question in the REPORT).
* **(e)** The case `s ≥ 5`, no `θ_i = 2π`, some `θ_i > 2π` of Troyanov's theorem is not proved:
  it is the tagged `sorry` of `GX.troyanovTheoremC` in the scaffold `TroyanovAngles` (DEC-136,
  target `T-gx-troyanov`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.TroyanovPolygon` (`exists_isConeSphere_of_subcritical`, `IsConeSphere.comp_equiv`),
`GX.Spherical.TroyanovFour` (`exists_isConeSphere_dart`), `GX.Spherical.TroyanovTwoPi`
(`IsConeSphere.insertNth`, `.exists_notMem_range`), `GX.Spherical.Football`
(`exists_isConeSphere_two`), `GX.SingularII.Models` (`TroyanovAngleCondition`).
-/

noncomputable section

open Set Function

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### Troyanov's Theorem C condition on the sphere -/

section ConditionC

/-- **Troyanov's Theorem C condition on the sphere** (`MR1005085`, Theorem C, p. 795; DEC-174):
for angles `θ_1, …, θ_s`, with `χ' = 2πχ(𝕊²) + ∑ (θ_i − 2π) = ∑ (θ_i − 2π) + 4π`,
`0 < χ' < min{4π, 2θ_min}`, the minimum written as one bound per angle
(`troyanovAngleConditionC_iff_inf'`). Positivity of the angles and `s ≥ 3` follow
(`TroyanovAngleConditionC.pos`, `.three_le`). -/
def TroyanovAngleConditionC {s : ℕ} (θ : Fin s → ℝ) : Prop :=
  0 < ∑ i, (θ i - 2 * π) + 4 * π ∧ ∑ i, (θ i - 2 * π) + 4 * π < 4 * π ∧
    ∀ j, ∑ i, (θ i - 2 * π) + 4 * π < 2 * θ j

namespace TroyanovAngleConditionC

variable {s : ℕ} {θ : Fin s → ℝ}

/-- Theorem C's angles are positive: `0 < χ' < 2θ_j`. -/
theorem pos (h : TroyanovAngleConditionC θ) (j : Fin s) : 0 < θ j := by
  have := h.2.2 j
  linarith [h.1]

/-- **Theorem C's condition forces at least three angles on the sphere**: at `s = 0`, `χ' = 4π`;
at `s = 1`, `θ_1 < 2π < θ_1`; at `s = 2`, `θ_1 + θ_2 < 2 min(θ_1, θ_2)`. -/
theorem three_le (h : TroyanovAngleConditionC θ) : 3 ≤ s := by
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hs
  push Not at hs
  interval_cases s
  · simp at h2
  · simp only [Fin.sum_univ_one] at h2 h3
    linarith [h3 0]
  · simp only [Fin.sum_univ_two] at h2 h3
    linarith [h3 0, h3 1]

end TroyanovAngleConditionC

/-- **Theorem C's condition, verbatim**: `0 < χ' < min{4π, 2θ_min}`, `θ_min` the least angle. -/
theorem troyanovAngleConditionC_iff_inf' {s : ℕ} (θ : Fin s → ℝ)
    (hs : (Finset.univ : Finset (Fin s)).Nonempty) :
    TroyanovAngleConditionC θ ↔ 0 < ∑ i, (θ i - 2 * π) + 4 * π ∧
      ∑ i, (θ i - 2 * π) + 4 * π < min (4 * π) (2 * Finset.univ.inf' hs θ) := by
  have key : ∀ c : ℝ, c < 2 * Finset.univ.inf' hs θ ↔ ∀ j, c < 2 * θ j := by
    intro c
    have e : c < 2 * Finset.univ.inf' hs θ ↔ c / 2 < Finset.univ.inf' hs θ :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [e, Finset.lt_inf'_iff]
    exact ⟨fun h j => by linarith [h j (Finset.mem_univ j)], fun h j _ => by linarith [h j]⟩
  unfold TroyanovAngleConditionC
  rw [lt_min_iff, key]

/-- **Theorem C's condition as printed**, with `θ_1 ≤ θ_2 ≤ ⋯ ≤ θ_n`:
`0 < χ' < min{4π, 2θ_1}`. -/
theorem troyanovAngleConditionC_iff_of_monotone {s : ℕ} (θ : Fin s → ℝ) (hs : 0 < s)
    (hθ : Monotone θ) :
    TroyanovAngleConditionC θ ↔ 0 < ∑ i, (θ i - 2 * π) + 4 * π ∧
      ∑ i, (θ i - 2 * π) + 4 * π < min (4 * π) (2 * θ ⟨0, hs⟩) := by
  have h0 : ∀ j, θ ⟨0, hs⟩ ≤ θ j := fun j => hθ (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
  unfold TroyanovAngleConditionC
  rw [lt_min_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3 _⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j => h3.trans_le (by linarith [h0 j])⟩

/-- **The least angle may be taken over the angles `≠ 2π`**: a bound `χ' < 2θ_j = 4π` at an angle
`2π` is the bound `χ' < 4π`. So the two readings of `θ_min` give one condition. -/
theorem troyanovAngleConditionC_iff_ne_two_pi {s : ℕ} (θ : Fin s → ℝ) :
    TroyanovAngleConditionC θ ↔ 0 < ∑ i, (θ i - 2 * π) + 4 * π ∧
      ∑ i, (θ i - 2 * π) + 4 * π < 4 * π ∧
      ∀ j, θ j ≠ 2 * π → ∑ i, (θ i - 2 * π) + 4 * π < 2 * θ j := by
  unfold TroyanovAngleConditionC
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j _ => h3 j⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j => ?_⟩
    by_cases hj : θ j = 2 * π
    · rw [hj]
      linarith
    · exact h3 j hj

/-- **A marked point of angle `2π` can be removed or added**: Theorem C's condition for `θ` with
`θ_k = 2π` is the condition for `θ` with `θ_k` removed. -/
theorem troyanovAngleConditionC_removeNth_iff {n : ℕ} {θ : Fin (n + 1) → ℝ} {k : Fin (n + 1)}
    (hk : θ k = 2 * π) :
    TroyanovAngleConditionC (k.removeNth θ) ↔ TroyanovAngleConditionC θ := by
  have hsum : ∑ i, (θ i - 2 * π) = ∑ i, (k.removeNth θ i - 2 * π) := by
    rw [Fin.sum_univ_succAbove _ k, hk, sub_self, zero_add]
    rfl
  unfold TroyanovAngleConditionC
  rw [← hsum]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove k j with hj | ⟨j', hj⟩
    · rw [hj, hk]
      linarith
    · rw [hj]
      exact h3 j'
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun j => h3 (k.succAbove j)⟩

/-- Deleting an angle `2π` keeps Theorem C's condition. -/
theorem TroyanovAngleConditionC.removeNth {n : ℕ} {θ : Fin (n + 1) → ℝ}
    (h : TroyanovAngleConditionC θ) {k : Fin (n + 1)} (hk : θ k = 2 * π) :
    TroyanovAngleConditionC (k.removeNth θ) :=
  (troyanovAngleConditionC_removeNth_iff hk).2 h

/-- At `s = 3`, Theorem C's condition forces every angle below `2π`. -/
theorem TroyanovAngleConditionC.three_lt_two_pi {θ : Fin 3 → ℝ} (h : TroyanovAngleConditionC θ)
    (i : Fin 3) : θ i < 2 * π := by
  have h3 := h.2.2
  simp only [Fin.sum_univ_three] at h3
  have j0 := h3 0
  have j1 := h3 1
  have j2 := h3 2
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

/-- **At `s = 4`, Theorem C's condition allows at most one angle above `2π`, and it is below
`4π`** (as the printed condition does, `GX.TroyanovAngleCondition.four_of_gt_two_pi`). -/
theorem TroyanovAngleConditionC.four_of_gt_two_pi {θ : Fin 4 → ℝ} (hθ : TroyanovAngleConditionC θ)
    {k : Fin 4} (hk : 2 * π < θ k) : θ k < 4 * π ∧ ∀ j, j ≠ k → θ j < 2 * π := by
  have p0 := hθ.pos 0
  have p1 := hθ.pos 1
  have p2 := hθ.pos 2
  have p3 := hθ.pos 3
  have hj := hθ.2.2
  simp only [Fin.sum_univ_four] at hj
  have j0 := hj 0
  have j1 := hj 1
  have j2 := hj 2
  have j3 := hj 3
  have hπ := Real.pi_pos
  constructor
  · match k with
    | 0 => linarith
    | 1 => linarith
    | 2 => linarith
    | 3 => linarith
  · intro j hjk
    match k, j with
    | 0, 0 => exact absurd rfl hjk
    | 0, 1 => linarith
    | 0, 2 => linarith
    | 0, 3 => linarith
    | 1, 0 => linarith
    | 1, 1 => exact absurd rfl hjk
    | 1, 2 => linarith
    | 1, 3 => linarith
    | 2, 0 => linarith
    | 2, 1 => linarith
    | 2, 2 => exact absurd rfl hjk
    | 2, 3 => linarith
    | 3, 0 => linarith
    | 3, 1 => linarith
    | 3, 2 => linarith
    | 3, 3 => exact absurd rfl hjk

end ConditionC

/-! ### The paper's condition against Theorem C's -/

section Compare

/-- **The printed condition implies Theorem C's** (l.1930 against `MR1005085`, p. 795): `χ' ≤ 4π`
is never attained (it would force `θ_j ≥ 4π` for all `j`), and `χ' ≤ θ_j < 2θ_j`. (The argument of
the scaffold's `GX.TroyanovAngleCondition.subcritical`, re-proved here.) -/
theorem TroyanovAngleCondition.troyanovAngleConditionC {s : ℕ} {θ : Fin s → ℝ}
    (h : TroyanovAngleCondition θ) : TroyanovAngleConditionC θ := by
  refine ⟨h.2.1, lt_of_le_of_ne h.2.2.1 fun heq => ?_, fun j => ?_⟩
  · have hge : ∀ j, 4 * π ≤ θ j := fun j => heq ▸ h.2.2.2 j
    have hsum : ∑ i : Fin s, (2 * π) ≤ ∑ i, (θ i - 2 * π) :=
      Finset.sum_le_sum fun i _ => by linarith [hge i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hs : (3 : ℝ) ≤ s := by exact_mod_cast h.1
    nlinarith [Real.pi_pos]
  · linarith [h.2.2.2 j, h.pos j]

/-- **The exact relation**: the printed condition (DEC-69's `GX.TroyanovAngleCondition`) is
Theorem C's condition together with `χ' ≤ θ_j` for every `j` — the bound `2θ_min` of Theorem C
replaced by `θ_min` (and `<` by `≤`, which changes nothing once `χ' ≤ θ_j < 2θ_j`). -/
theorem troyanovAngleCondition_iff_troyanovAngleConditionC {s : ℕ} (θ : Fin s → ℝ) :
    TroyanovAngleCondition θ ↔
      TroyanovAngleConditionC θ ∧ ∀ j, ∑ i, (θ i - 2 * π) + 4 * π ≤ θ j :=
  ⟨fun h => ⟨h.troyanovAngleConditionC, h.2.2.2⟩,
    fun ⟨h, hle⟩ => ⟨h.three_le, h.1, h.2.1.le, hle⟩⟩

end Compare

/-! ### Troyanov's theorem with Theorem C's condition -/

section TheoremC

/-- **Troyanov's theorem with Theorem C's condition** (`MR1005085`, Theorem C at `S = 𝕊²` and
curvature `1`; the condition of record ruled by DEC-174): for angles `θ_1, …, θ_s` with
`0 < ∑ (θ_i − 2π) + 4π < min{4π, 2θ_min}` (`GX.TroyanovAngleConditionC`), there is a spherical cone
sphere with cone points of angles `θ_1, …, θ_s` (`GX.IsConeSphere`). Meant to replace
`GX.TroyanovTheorem` (`GXScaffold.Spherical.TroyanovAngles`), whose condition is the paper's
narrower citation (`troyanovAngleCondition_iff_troyanovAngleConditionC`). -/
def TroyanovTheoremC : Prop :=
  ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleConditionC θ →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p

/-- **Theorem C's form implies the paper's** (the conclusion is the body of `GX.TroyanovTheorem`,
`GXScaffold.Spherical.TroyanovAngles`, which this module does not import). -/
theorem TroyanovTheoremC.troyanovTheorem (h : TroyanovTheoremC) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p :=
  fun θ hθ => h θ hθ.troyanovAngleConditionC

/-- **Theorem C's condition is sufficient, not necessary**: the football with two cone points of
angle `π` is a cone sphere (`GX.exists_isConeSphere_two`), and Theorem C's condition fails at
`s = 2`. -/
theorem exists_isConeSphere_not_troyanovAngleConditionC :
    ∃ (θ : Fin 2 → ℝ) (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M)
      (p : Fin 2 → M), IsConeSphere M θ p ∧ ¬ TroyanovAngleConditionC θ := by
  obtain ⟨M, _, _, -, -, -, p, hp, -⟩ := exists_isConeSphere_two π Real.pi_pos
  exact ⟨_, M, _, _, p, hp, fun h => absurd h.three_le (by norm_num)⟩

end TheoremC

/-! ### What the strict library proves under Theorem C's condition -/

section Reductions

/-- **Troyanov's theorem under Theorem C's condition, every angle below `2π`**: the double of a
convex spherical polygon (`GX.exists_isConeSphere_of_subcritical`, whose hypotheses are Theorem
C's). -/
theorem troyanovTheoremC_of_lt_two_pi {s : ℕ} (θ : Fin s → ℝ) (hθ : TroyanovAngleConditionC θ)
    (hlt : ∀ i, θ i < 2 * π) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p :=
  exists_isConeSphere_of_subcritical hθ.three_le θ hθ.pos hlt hθ.1 hθ.2.2

/-- **Troyanov's theorem under Theorem C's condition, every angle at most `2π`**: the angles `2π`
are removed (`TroyanovAngleConditionC.removeNth`) and put back as marked regular points
(`GX.IsConeSphere.insertNth`). -/
theorem troyanovTheoremC_of_le_two_pi :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleConditionC θ → (∀ i, θ i ≤ 2 * π) →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p := by
  intro s
  induction s with
  | zero => intro θ hθ; exact absurd hθ.three_le (by norm_num)
  | succ n ih =>
    intro θ hθ hle
    by_cases hne : ∀ i, θ i ≠ 2 * π
    · exact troyanovTheoremC_of_lt_two_pi θ hθ fun i => lt_of_le_of_ne (hle i) (hne i)
    obtain ⟨k, hk⟩ : ∃ k, θ k = 2 * π := by
      by_contra hc
      exact hne fun i hi => hc ⟨i, hi⟩
    obtain ⟨M, _, _, p, hp⟩ := ih (k.removeNth θ) (hθ.removeNth hk) fun i => hle _
    obtain ⟨q, hq⟩ := hp.exists_notMem_range
    exact ⟨M, _, _, _, hp.insertNth hk hq⟩

/-- **Troyanov's theorem under Theorem C's condition from its restriction to angles all `≠ 2π`**
(as `GX.troyanovTheorem_of_ne_two_pi` for the printed condition). -/
theorem troyanovTheoremC_of_ne_two_pi
    (h : ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleConditionC θ → (∀ i, θ i ≠ 2 * π) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    TroyanovTheoremC := by
  intro s
  induction s with
  | zero => intro θ hθ; exact absurd hθ.three_le (by norm_num)
  | succ n ih =>
    intro θ hθ
    by_cases hne : ∀ i, θ i ≠ 2 * π
    · exact h θ hθ hne
    obtain ⟨k, hk⟩ : ∃ k, θ k = 2 * π := by
      by_contra hc
      exact hne fun i hi => hc ⟨i, hi⟩
    obtain ⟨M, _, _, p, hp⟩ := ih (k.removeNth θ) (hθ.removeNth hk)
    obtain ⟨q, hq⟩ := hp.exists_notMem_range
    exact ⟨M, _, _, _, hp.insertNth hk hq⟩

/-- **Troyanov's theorem under Theorem C's condition at `s = 3`**: every angle is below `2π`
(`TroyanovAngleConditionC.three_lt_two_pi`). -/
theorem troyanovTheoremC_three (θ : Fin 3 → ℝ) (hθ : TroyanovAngleConditionC θ) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 3 → M),
      IsConeSphere M θ p :=
  troyanovTheoremC_of_lt_two_pi θ hθ hθ.three_lt_two_pi

/-- **Troyanov's theorem under Theorem C's condition at `s = 4` with an angle above `2π`**: the
double of the spherical dart with angles `θ_i / 2` (`GX.exists_isConeSphere_dart`), the reflex
vertex at the angle above `2π`; Theorem C's condition implies every hypothesis of the dart. -/
theorem troyanovTheoremC_four_of_exists_gt_two_pi (θ : Fin 4 → ℝ)
    (hθ : TroyanovAngleConditionC θ) (hgt : ∃ i, 2 * π < θ i) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M θ p := by
  obtain ⟨k, hk⟩ := hgt
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 k
  set θ' : Fin 4 → ℝ := θ ∘ σ with hθ'
  have hπ := Real.pi_pos
  have hsum' : ∑ i, (θ' i - 2 * π) = ∑ i, (θ i - 2 * π) :=
    Equiv.sum_comp σ (fun i => θ i - 2 * π)
  have c1 : 0 < ∑ i, (θ' i - 2 * π) + 4 * π := hsum' ▸ hθ.1
  have c2 : ∀ j, ∑ i, (θ' i - 2 * π) + 4 * π < 2 * θ' j := fun j => hsum' ▸ hθ.2.2 (σ j)
  have cp : ∀ j, 0 < θ' j := fun j => hθ.pos (σ j)
  simp only [Fin.sum_univ_four] at c1 c2
  have q0 : θ' 0 = θ k := by simp only [hθ', σ, Function.comp_apply, Equiv.swap_apply_left]
  have j0 := c2 0
  have j1 := c2 1
  have j2 := c2 2
  have j3 := c2 3
  have p0 := cp 0
  have p1 := cp 1
  have p2 := cp 2
  have p3 := cp 3
  rw [q0] at j0 j1 j2 j3 c1 p0
  obtain ⟨M, _, _, p, hp⟩ := exists_isConeSphere_dart (fun i => θ' i / 2)
    (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by positivity) (by positivity) (by positivity)
    (by linarith) (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by simp only [q0]; linarith) (by simp only [q0]; linarith) (by simp only [q0]; linarith)
    (by simp only [q0]; linarith)
  have hθσ : (fun i => 2 * (fun i => θ' i / 2) i) = θ ∘ σ := by
    funext i; simp only [hθ', Function.comp_apply]; ring
  rw [hθσ] at hp
  have h' := hp.comp_equiv σ.symm
  have e : θ ∘ σ ∘ σ.symm = θ := by funext i; simp
  rw [Function.comp_assoc, e] at h'
  exact ⟨M, _, _, _, h'⟩

/-- **Troyanov's theorem under Theorem C's condition at `s = 4`**, every angle. -/
theorem troyanovTheoremC_four (θ : Fin 4 → ℝ) (hθ : TroyanovAngleConditionC θ) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
      IsConeSphere M θ p := by
  by_cases h : ∃ i, 2 * π < θ i
  · exact troyanovTheoremC_four_of_exists_gt_two_pi θ hθ h
  · push Not at h
    exact troyanovTheoremC_of_le_two_pi θ hθ h

/-- **What remains of Troyanov's theorem under Theorem C's condition**: its case `s ≥ 5`, every
angle `≠ 2π`, some angle `> 2π` (as `GX.troyanovTheorem_of_five_le_of_exists_gt_two_pi` for the
printed condition). -/
theorem troyanovTheoremC_of_five_le_of_exists_gt_two_pi
    (h : ∀ {s : ℕ}, 5 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleConditionC θ → (∀ i, θ i ≠ 2 * π) →
      (∃ i, 2 * π < θ i) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    TroyanovTheoremC :=
  troyanovTheoremC_of_ne_two_pi fun {s} θ hθ hne => by
    by_cases hgt : ∃ i, 2 * π < θ i
    · rcases Nat.lt_or_ge s 5 with h5 | h5
      · have h3 := hθ.three_le
        obtain rfl | rfl : s = 3 ∨ s = 4 := by omega
        · exact troyanovTheoremC_three θ hθ
        · exact troyanovTheoremC_four_of_exists_gt_two_pi θ hθ hgt
      · exact h h5 θ hθ hne hgt
    · push Not at hgt
      exact troyanovTheoremC_of_le_two_pi θ hθ hgt

/-- **The reduction is an equivalence**: `GX.TroyanovTheoremC` holds iff it holds for `s ≥ 5`
angles, none equal to `2π`, some above `2π`. -/
theorem troyanovTheoremC_iff_five_le_of_exists_gt_two_pi :
    TroyanovTheoremC ↔
    (∀ {s : ℕ}, 5 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleConditionC θ → (∀ i, θ i ≠ 2 * π) →
      (∃ i, 2 * π < θ i) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :=
  ⟨fun h _ _ θ hθ _ _ => h θ hθ, troyanovTheoremC_of_five_le_of_exists_gt_two_pi⟩

end Reductions

/-! ### The paper's citation is narrower: the witnesses -/

section Witnesses

/-- **Theorem C's condition does not imply the printed one, at `s = 3`**: the pairwise distinct
angles `(7π/5, 13π/10, π)` satisfy Theorem C's condition (`χ' = 17π/10 < 2π = 2θ_min`), violate
l.1930's (`χ' > π = θ_2`), and a cone sphere with these angles exists. -/
theorem troyanovAngleConditionC_three_not_printed :
    TroyanovAngleConditionC ![7 * π / 5, 13 * π / 10, π] ∧
      ¬ TroyanovAngleCondition ![7 * π / 5, 13 * π / 10, π] ∧
      Pairwise (fun i j => ![7 * π / 5, 13 * π / 10, π] i ≠ ![7 * π / 5, 13 * π / 10, π] j) ∧
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 3 → M),
        IsConeSphere M ![7 * π / 5, 13 * π / 10, π] p := by
  have hπ := Real.pi_pos
  have hχ : ∑ i, (![7 * π / 5, 13 * π / 10, π] i - 2 * π) + 4 * π = 17 * π / 10 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hc : TroyanovAngleConditionC ![7 * π / 5, 13 * π / 10, π] := by
    refine ⟨by rw [hχ]; positivity, by rw [hχ]; linarith, fun j => ?_⟩
    rw [hχ]
    fin_cases j <;> simp <;> linarith
  refine ⟨hc, fun h => ?_, fun i j hij => ?_, troyanovTheoremC_three _ hc⟩
  · have h2 := h.2.2.2 2
    rw [hχ] at h2
    simp at h2
    linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

/-- **Theorem C's condition does not imply the printed one, at `s = 4` with an angle above `2π`**:
the pairwise distinct angles `(5π/2, 9π/10, π, 11π/10)` satisfy Theorem C's condition
(`χ' = 3π/2 < 9π/5 = 2θ_min`), violate l.1930's (`χ' > 9π/10 = θ_1`), and a cone sphere with
these angles exists (the dart, `troyanovTheoremC_four_of_exists_gt_two_pi`). -/
theorem troyanovAngleConditionC_four_not_printed :
    TroyanovAngleConditionC ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] ∧
      ¬ TroyanovAngleCondition ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] ∧
      Pairwise (fun i j => ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] i ≠
        ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] j) ∧
      2 * π < ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] 0 ∧
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
        IsConeSphere M ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] p := by
  have hπ := Real.pi_pos
  have hχ : ∑ i, (![5 * π / 2, 9 * π / 10, π, 11 * π / 10] i - 2 * π) + 4 * π = 3 * π / 2 := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hc : TroyanovAngleConditionC ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] := by
    refine ⟨by rw [hχ]; positivity, by rw [hχ]; linarith, fun j => ?_⟩
    rw [hχ]
    fin_cases j <;> simp <;> linarith
  have h0 : 2 * π < ![5 * π / 2, 9 * π / 10, π, 11 * π / 10] 0 := by simp; linarith
  refine ⟨hc, fun h => ?_, fun i j hij => ?_, h0,
    troyanovTheoremC_four_of_exists_gt_two_pi _ hc ⟨0, h0⟩⟩
  · have h1 := h.2.2.2 1
    rw [hχ] at h1
    simp at h1
    linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

/-- **The case left under Theorem C's condition is strictly wider than under the printed one**:
the pairwise distinct angles `(5π/2, 7π/5, 3π/2, 8π/5, 17π/10)` (`s = 5`, none `2π`, one above
`2π`) satisfy Theorem C's condition (`χ' = 27π/10 < 14π/5 = 2θ_min`) and violate l.1930's
(`χ' > 7π/5 = θ_1`). No cone sphere with these angles is built in the library: this datum is in
the tagged `sorry` of `troyanovTheoremC` and not in that of the printed form. -/
theorem troyanovAngleConditionC_five_not_printed :
    TroyanovAngleConditionC ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] ∧
      ¬ TroyanovAngleCondition ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] ∧
      Pairwise (fun i j => ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] i ≠
        ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] j) ∧
      (∀ i, ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] i ≠ 2 * π) ∧
      2 * π < ![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] 0 := by
  have hπ := Real.pi_pos
  have hχ : ∑ i, (![5 * π / 2, 7 * π / 5, 3 * π / 2, 8 * π / 5, 17 * π / 10] i - 2 * π) +
      4 * π = 27 * π / 10 := by
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    ring
  refine ⟨⟨by rw [hχ]; positivity, by rw [hχ]; linarith, fun j => ?_⟩, fun h => ?_,
    fun i j hij => ?_, fun i => ?_, by simp; linarith⟩
  · rw [hχ]
    fin_cases j <;> simp <;> linarith
  · have h1 := h.2.2.2 1
    rw [hχ] at h1
    simp at h1
    linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith
  · fin_cases i <;> simp <;> intro h <;> linarith

end Witnesses

end GX
