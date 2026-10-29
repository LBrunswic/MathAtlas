import Causal.ArcConnected
import Causal.Lines

/-!
# The timelike line is causally arc-connected

A check that the definition of `Causal.Curves` is inhabited: on the timelike line of
`ex:causalities_lines` the affine map from `p` to `q` is a future chronal curve, so the timelike
line is causally arc-connected, and the results of `Causal.ArcConnected` apply to it.
No paper label is certified by this file.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

/-- On the timelike line, the affine map from `p` to `q > p` is a future chronal curve of every
open set containing the segment. -/
theorem timelikeLine_chronalCurveOn_affine {U : Opens ℝ} {p q : ℝ} (hpq : p < q)
    (hsub : Icc p q ⊆ (U : Set ℝ)) :
    timelikeLine.ChronalCurveOn U (fun t => p + t * (q - p)) 0 1 where
  mem t ht := hsub ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  rel t ht N _ htN := by
    have hd : 0 < q - p := sub_pos.2 hpq
    obtain ⟨l', u', ⟨hl', hu'⟩, hsub'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    refine ⟨(l' - p) / (q - p), (u' - p) / (q - p), ?_, ?_, fun s _ s' _ h1 h2 h3 => ?_⟩
    · rw [div_lt_iff₀ hd]; linarith
    · rw [lt_div_iff₀ hd]; linarith
    · rw [div_lt_iff₀ hd] at h1
      rw [lt_div_iff₀ hd] at h3
      refine ⟨by nlinarith, ?_⟩
      rintro z ⟨hz1, hz2⟩
      exact hsub' ⟨by linarith, by linarith⟩

/-- The timelike line is causally arc-connected. -/
theorem timelikeLine_causallyArcConnected : timelikeLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  constructor
  · rintro ⟨hpq, hsub⟩
    rcases hpq.eq_or_lt with h | h
    · subst h
      exact ⟨fun _ => p, Causality.causalCurveOn_const (hsub (left_mem_Icc.2 le_rfl)), rfl, rfl⟩
    · exact ⟨fun t => p + t * (q - p),
        (timelikeLine_chronalCurveOn_affine h hsub).causalCurveOn, by simp, by simp⟩
  · rintro ⟨hpq, hsub⟩
    exact ⟨fun t => p + t * (q - p), timelikeLine_chronalCurveOn_affine hpq hsub, by simp,
      by simp⟩

/-- `cor:causalement_connexe_minimal`, read on the timelike line: it gives back
`timelikeLine_absolutelyMinimal`, which `Causal.Lines` proves directly. -/
theorem timelikeLine_absolutelyMinimal' : timelikeLine.AbsolutelyMinimal :=
  timelikeLine_causallyArcConnected.absolutelyMinimal

end Causal
