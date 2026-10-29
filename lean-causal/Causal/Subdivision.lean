import Mathlib.Topology.UnitInterval

/-!
# Subdividing a segment along an open cover

A utility: an open cover of a segment `[a, b]` of the real line is refined by a finite
subdivision. This is the "Lebesgue number" step of the proofs of `prop:cac_engendre`,
`lem:pushup_local` and `cexemple:point_transparent`. It is mathlib's
`exists_monotone_Icc_subset_open_cover_Icc`, restated for open subsets of `ℝ` rather than of the
subtype `Icc a b`.

No paper label is certified by this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set

/-- An open cover of `[a, b]` is refined by a subdivision `a = t 0 ≤ t 1 ≤ ⋯`, stationary at
`b`, each segment `[t n, t (n+1)]` lying in a member of the cover. -/
theorem exists_subdivision_Icc {ι : Type*} {a b : ℝ} (hab : a ≤ b) {O : ι → Set ℝ}
    (hO : ∀ i, IsOpen (O i)) (hcover : Icc a b ⊆ ⋃ i, O i) :
    ∃ t : ℕ → ℝ, t 0 = a ∧ Monotone t ∧ (∃ m, ∀ n ≥ m, t n = b) ∧ (∀ n, t n ∈ Icc a b) ∧
      ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ O i := by
  let c : ι → Set (Icc a b) := fun i => Subtype.val ⁻¹' O i
  have hc₁ : ∀ i, IsOpen (c i) := fun i => (hO i).preimage continuous_subtype_val
  have hc₂ : univ ⊆ ⋃ i, c i := by
    rintro ⟨z, hz⟩ -
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover hz)
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, ht⟩ := exists_monotone_Icc_subset_open_cover_Icc hab hc₁ hc₂
  refine ⟨fun n => (t n : ℝ), ht0, fun _ _ h => hmono h, ⟨m, hm⟩, fun n => (t n).2, fun n => ?_⟩
  obtain ⟨i, hi⟩ := ht n
  refine ⟨i, ?_⟩
  rintro z ⟨hz1, hz2⟩
  have hz : z ∈ Icc a b := ⟨(t n).2.1.trans hz1, hz2.trans (t (n + 1)).2.2⟩
  exact hi (show (⟨z, hz⟩ : Icc a b) ∈ Icc (t n) (t (n + 1)) from ⟨hz1, hz2⟩)

end Causal
