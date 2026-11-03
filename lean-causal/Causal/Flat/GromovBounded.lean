import Causal.Flat.GromovBase
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# `Causal.Flat.GromovBounded` — a bounded orbit in `ℍᵈ` gives a fixed timelike vector

The bounded half of Gromov's classification for `SO₀(1, d)` acting on `ℍᵈ` (DEC-111): if the
orbit of `o` under `G ≤ lorentz d` is bounded (`orbitCosh` bounded on `G`), `G` fixes a timelike
vector. **No ledger label is certified here**: the module is a step of `Flat/GromovProof`, which
discharges the external `BenoistNoLox` of `bprop:sanloxo` (`GHFspace.tex:2573`).

> […] up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), […] (l.2576)

The paper's `Γ` is a subgroup of the isometry group of Minkowski space with linear part
`L(Γ) ≤ SO₀(1, n−1)`; the Lean object is the linear group `G ≤ lorentz d` itself.

The circumcentre is replaced by a maximiser of the Lorentzian norm on an invariant compact convex
set, which needs no hyperbolic distance and no Haar measure:

1. `orbitHull G = closure (convexHull ℝ (G · o))` is convex (`Convex.closure`), `G`-invariant
   (`LinearMap.image_convexHull`, `image_closure_subset_closure_image`, `G · o` is `G`-stable),
   compact when `orbitCosh` is bounded (closed, inside a closed ball — the orbit lies in
   `{x.1 ≤ M, ‖x.2‖ ≤ M}` because `‖x.2‖² = x.1² − 1`), contains `o`, and lies in `{x.1 ≥ 0}`.
2. `−minkQ` attains its maximum `m ≥ −minkQ o = 1` on it at some `y` (`IsCompact.exists_isMaxOn`).
3. **Uniqueness without reverse Cauchy–Schwarz** (`eq_of_isMaxOn`): for two maximisers `y₁, y₂`,
   maximality at the midpoint gives `−⟨y₁ | y₂⟩ ≤ m`, so `minkQ (y₁ − y₂) = −2m − 2⟨y₁|y₂⟩ ≤ 0`;
   and `⟨y₁ − y₂ | y₁ + y₂⟩ = minkQ y₁ − minkQ y₂ = 0` with `y₁ + y₂` timelike, so
   `y₁ − y₂ = 0` (`minkQ_pos_of_orth_timelike`).
4. `A ∈ G` maps maximisers to maximisers (`minkQ` invariant, `orbitHull G` invariant), so `A y = y`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| linear part `L(Γ) ≤ SO₀(1, n−1)` (l.2576) | ✓ carried: `G : Subgroup (lorentz d)` |
| no loxodromic element | ⚠ weakened: not used in this case |
| (case of the proof) a bounded orbit | ✓ the case hypothesis `∀ A ∈ G, orbitCosh A ≤ M` |
| "up to finite index, its linear part is either contained in $SO(n-1)$ (up to conjugacy)" (l.2576) | ⚠ weakened (stronger conclusion): `G` itself fixes a timelike vector |

## SCOPE (disclosed)

* Nothing of the paper is certified here; the timelike fixed vector is the conclusion's first
  alternative (`FixesTimelikeOrNull`, `Flat/Externals`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-111 (Gromov route). Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

open Filter Topology

variable {d : ℕ}

/-- The orbit of `o` under `G`. -/
def orbitSet (G : Subgroup (lorentz d)) : Set (Minkowski d) :=
  (fun A : lorentz d => (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)) '' (G : Set (lorentz d))

/-- The closed convex hull (closure of the convex hull) of the orbit of `o`. -/
noncomputable def orbitHull (G : Subgroup (lorentz d)) : Set (Minkowski d) :=
  closure (convexHull ℝ (orbitSet G))

theorem timeUnit_mem_orbitHull (G : Subgroup (lorentz d)) : timeUnit d ∈ orbitHull G := by
  exact subset_closure (subset_convexHull ℝ _ ⟨1, G.one_mem, rfl⟩)

theorem convex_orbitHull (G : Subgroup (lorentz d)) : Convex ℝ (orbitHull G) := by
  exact (convex_convexHull ℝ _).closure

/-- `G` preserves the orbit hull. -/
theorem apply_mem_orbitHull {G : Subgroup (lorentz d)} {A : lorentz d} (hA : A ∈ G)
    {x : Minkowski d} (hx : x ∈ orbitHull G) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) x ∈ orbitHull G := by
  set f : Minkowski d →ₗ[ℝ] Minkowski d := (A : Minkowski d ≃ₗ[ℝ] Minkowski d).toLinearMap
  have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have horb : f '' orbitSet G ⊆ orbitSet G := by
    rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨A * B, G.mul_mem hA hB, rfl⟩
  have h1 : f '' orbitHull G ⊆ orbitHull G := by
    unfold orbitHull
    refine (image_closure_subset_closure_image hf).trans (closure_mono ?_)
    rw [LinearMap.image_convexHull]
    exact convexHull_mono horb
  exact h1 ⟨x, hx, rfl⟩

/-- The orbit hull lies in the closed half-space `{x.1 ≥ 0}`. -/
theorem fst_nonneg_of_mem_orbitHull {G : Subgroup (lorentz d)} {x : Minkowski d}
    (hx : x ∈ orbitHull G) : 0 ≤ x.1 := by
  have hconv : Convex ℝ {w : Minkowski d | (0 : ℝ) ≤ w.1} :=
    convex_halfSpace_ge (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d))).isLinear 0
  have hclosed : IsClosed {w : Minkowski d | (0 : ℝ) ≤ w.1} :=
    isClosed_le continuous_const continuous_fst
  have horb : orbitSet G ⊆ {w : Minkowski d | (0 : ℝ) ≤ w.1} := by
    rintro _ ⟨B, -, rfl⟩
    exact (orbitCosh_pos B).le
  exact closure_minimal (convexHull_min horb hconv) hclosed hx

/-- A bounded `orbitCosh` makes the orbit hull compact. -/
theorem isCompact_orbitHull {G : Subgroup (lorentz d)} {M : ℝ}
    (hM : ∀ A ∈ G, orbitCosh A ≤ M) : IsCompact (orbitHull G) := by
  -- `K = {x | |x.1| ≤ M ∧ ‖x.2‖ ≤ M}` is the closed ball of radius `M` for the sup norm.
  have horb : orbitSet G ⊆ Metric.closedBall (0 : Minkowski d) M := by
    rintro _ ⟨B, hB, rfl⟩
    rw [mem_closedBall_zero_iff, norm_prod_le_iff]
    have hc1 := one_le_orbitCosh B
    have hcM := hM B hB
    have hq := minkQ_apply_timeUnit B
    unfold minkQ at hq
    change -(orbitCosh B) ^ 2 + ‖((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).2‖ ^ 2 = -1
      at hq
    refine ⟨?_, ?_⟩
    · change ‖orbitCosh B‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_pos (orbitCosh_pos B)]; exact hcM
    · have h2 : ‖((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).2‖ ^ 2 ≤ M ^ 2 := by
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 h2
  exact (isCompact_closedBall (0 : Minkowski d) M).of_isClosed_subset isClosed_closure
    (closure_minimal (convexHull_min horb (convex_closedBall _ _)) Metric.isClosed_closedBall)

/-- **Uniqueness of the maximiser of `−minkQ`** on a convex set of the closed future half-space
containing a timelike vector: no reverse Cauchy–Schwarz needed. -/
theorem eq_of_isMaxOn {C : Set (Minkowski d)} (hC : Convex ℝ C) (hC0 : ∀ x ∈ C, 0 ≤ x.1)
    {y₁ y₂ : Minkowski d} (h₁ : y₁ ∈ C) (h₂ : y₂ ∈ C) (hneg : minkQ y₁ < 0)
    (hmax₁ : IsMaxOn (fun x => -minkQ x) C y₁) (hmax₂ : IsMaxOn (fun x => -minkQ x) C y₂) :
    y₁ = y₂ := by
  rw [isMaxOn_iff] at hmax₁ hmax₂
  have hq12 : minkQ y₁ = minkQ y₂ := by
    have := hmax₁ y₂ h₂; have := hmax₂ y₁ h₁; linarith
  -- the midpoint
  have hmid : (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ ∈ C := hC h₁ h₂ (by norm_num) (by norm_num)
    (by norm_num)
  have hQmid : minkQ ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) =
      (minkQ y₁ + minkB y₁ y₂) / 2 := by
    rw [minkQ_add, minkQ_smul, minkQ_smul, minkB_smul_left, minkB_smul_right, ← hq12]; ring
  have hB : minkQ y₁ ≤ minkB y₁ y₂ := by
    have := hmax₁ _ hmid; rw [hQmid] at this; linarith
  have hsub : minkQ (y₁ - y₂) ≤ 0 := by
    rw [sub_eq_add_neg, minkQ_add, minkQ_neg, minkB_neg_right, ← hq12]; linarith
  -- `y₁`, `y₂` are future timelike
  have hft : ∀ {y : Minkowski d}, y ∈ C → minkQ y < 0 → IsFutureTimelike y := by
    intro y hy hyq
    refine ⟨lt_of_le_of_ne (hC0 y hy) fun h => ?_, hyq⟩
    exact absurd (minkQ_nonneg_of_fst_eq_zero h.symm) (not_le.2 hyq)
  have hf₁ := hft h₁ hneg
  have hf₂ := hft h₂ (hq12 ▸ hneg)
  have hy₁0 : y₁ ≠ 0 := by rintro rfl; simp at hneg
  have hB0 : minkB y₁ y₂ < 0 :=
    minkB_neg_of_future ⟨hf₁.1.le, hf₁.2.le⟩ hy₁0 hf₂
  have hsum : minkQ (y₁ + y₂) < 0 := by
    rw [minkQ_add, ← hq12]; linarith
  have horth : minkB (y₁ + y₂) (y₁ - y₂) = 0 := by
    rw [minkB_add_left, minkB_sub_right, minkB_sub_right, minkB_comm y₂ y₁, ← minkQ_eq_minkB,
      ← minkQ_eq_minkB, hq12]; ring
  by_contra hne
  have hpos := minkQ_pos_of_orth_timelike hsum horth (sub_ne_zero.2 hne)
  linarith

/-- **Gromov's bounded case for `SO₀(1, d)`.** A subgroup with a bounded orbit of `o` fixes a
timelike vector. -/
theorem exists_fixed_timelike_of_bounded {G : Subgroup (lorentz d)} {M : ℝ}
    (hM : ∀ A ∈ G, orbitCosh A ≤ M) :
    ∃ v : Minkowski d, minkQ v < 0 ∧ ∀ A ∈ G, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v = v := by
  obtain ⟨y, hy, hmax⟩ := (isCompact_orbitHull hM).exists_isMaxOn
    ⟨_, timeUnit_mem_orbitHull G⟩ (continuous_minkQ (d := d)).neg.continuousOn
  have hy1 : minkQ y ≤ -1 := by
    have := (isMaxOn_iff.1 hmax) _ (timeUnit_mem_orbitHull G)
    simp only [minkQ_timeUnit] at this; linarith
  have hneg : minkQ y < 0 := by linarith
  refine ⟨y, hneg, fun A hA => ?_⟩
  have hAy := apply_mem_orbitHull hA hy
  have hQ : minkQ ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) y) = minkQ y := lorentz.minkQ_apply A.2 y
  have hmaxA : IsMaxOn (fun x => -minkQ x) (orbitHull G)
      ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) y) := by
    rw [isMaxOn_iff]; intro x hx; rw [hQ]; exact (isMaxOn_iff.1 hmax) x hx
  exact (eq_of_isMaxOn (convex_orbitHull G) (fun _ => fst_nonneg_of_mem_orbitHull) hy hAy hneg
    hmax hmaxA).symm

end Causal.Flat
