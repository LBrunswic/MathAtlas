import Causal.StrongCausalityHull
import Causal.Lines
import Causal.LadderLocal
import Causal.NestedTransfer
import Causal.LocateExtension
import Causal.OneWayMembrane

/-!
# Strong causality and two-sided causal openness give the open form, without tarentin: the witnesses

No label is certified here. The file bears on `def:strongly_causal_spacetime` — `ETT.tex:662`
(its two readings, DEC-7), on `def:causally_open_spacetime_open` — `ETT.tex:694` (the two-sided
reading, DEC-8, the ladder node `causally_open`, DEC-163) and on the open form of
`prop:GH_fortement_causal` — `ETT.tex:1199`; none of them is marked.

**Moved out** (programme target `T-abs-sc-open-hoist`): the model-free half of this module — the
causal hull `J⁺_M(A) ∩ J⁻_M(A)`, strong causality's open form
(`Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen`, the ladder witness, and its weaker
forms) and the shape of a counterexample to `strongly_causal → strongly_causal_open`
(`Causality.StronglyCausal.exists_not_isOpen_hull`,
`StronglyCausal.not_causallyOpen_of_not_stronglyCausalOpen`) — is now `Causal.StrongCausalityHull`,
byte for byte under the same full names, with its statement, its proof, its hypothesis checklist
and its SCOPE. This module imports it (in place of `Causal.GlobalHyperbolicity`, which it reaches
through it) and keeps the witnesses, which need the lines and the one-way membrane.

## Witnesses (kb/0011)

* `timelikeLine_scOpen_of_causallyOpen`: the timelike line meets every hypothesis (and tarentin).
* `spacelikeLine_scOpen_without_tarentin`: strongly causal, causally open, **not tarentin**; the
  old witness does not apply, the new one does.
* `isolatedLine_scOpen_without_tarentin`: the line with a chronologically isolated origin
  (`Causal.isolatedLine`, kb/0050) is strongly causal by **closed** intervals
  (`isolatedLine_stronglyCausal`, new), causally open and not tarentin; the theorem gives its open
  form, which the library did not have (open intervals would give it directly: the closed ones are
  chosen so that the theorem does the work).
* `oneWayMembrane_hull_not_isOpen`: **the future half of causal openness alone does not open the
  hull** (DEC-163). On the one-way membrane, causally open in the future, strongly causal and not
  causally open, the hull `H` built from a causally convex neighbourhood `V` of `(0, 1)` is not
  open. The membrane is strongly causal in the open form all the same
  (`oneWayMembrane_stronglyCausalOpen`, by balls), so this refutes the argument, not the statement:
  whether `strongly_causal ∧ causally_open_future ⇒ strongly_causal_open` holds is **open**
  (`Causal.StrongCausalityHull`, "Which causal openness").

## Hypothesis checklist

| the witnesses | here |
|---|---|
| the theorem's hypotheses, jointly satisfiable | ✓ on the timelike, spacelike and isolated lines |
| tarentin not needed | ✓ the spacelike and isolated lines are not tarentin |

## SCOPE (disclosed)

* The theorem, its weaker forms, its hypothesis checklist and its SCOPE are in
  `Causal.StrongCausalityHull`.
* The membrane witness reads a neighbourhood through the sup distance of `ℝ × ℝ`, as
  `Causal.OneWayMembrane` does; no Lorentzian notion enters.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

/-! ### Witnesses -/

/-- The timelike line meets every hypothesis (tarentin too): the theorem gives its open form. -/
theorem timelikeLine_scOpen_of_causallyOpen :
    timelikeLine.StronglyCausal ∧ timelikeLine.CausallyOpen ∧ timelikeLine.StronglyCausalOpen := by
  exact ⟨timelikeLine_stronglyCausal, timelikeLine_causallyOpen_of_chronalNeighbours,
    timelikeLine_stronglyCausal.stronglyCausalOpen_of_causallyOpen
      timelikeLine_causallyOpen_of_chronalNeighbours⟩

/-- **The spacelike line**: strongly causal, causally open and not tarentin. The old witness
`StronglyCausal.stronglyCausalOpen` does not apply; `stronglyCausalOpen_of_causallyOpen` does. -/
theorem spacelikeLine_scOpen_without_tarentin :
    spacelikeLine.StronglyCausal ∧ spacelikeLine.CausallyOpen ∧ ¬ spacelikeLine.Tarentin ∧
      spacelikeLine.StronglyCausalOpen := by
  exact ⟨spacelikeLine_stronglyCausal, spacelikeLine_causallyOpen, spacelikeLine_not_tarentin,
    spacelikeLine_stronglyCausal.stronglyCausalOpen_of_causallyOpen spacelikeLine_causallyOpen⟩

/-- On the line with a chronologically isolated origin `≤_M` lies in the order of `ℝ`. -/
theorem isolatedLine_le_top {x y : ℝ} (h : isolatedLine.le ⊤ x y) : x ≤ y := by
  rcases h with ⟨rfl, -⟩ | ⟨h, -⟩
  · exact le_rfl
  · exact h.le

/-- Every closed interval is causally convex in `M` for the line with an isolated origin. -/
theorem isolatedLine_causallyConvexIn_Icc (a b : ℝ) :
    isolatedLine.CausallyConvexIn (Icc a b) ⊤ := by
  refine ⟨fun _ _ => trivial, fun x hx y hy z hz => ?_⟩
  rw [Causality.mem_diamond] at hz
  exact ⟨hx.1.trans (isolatedLine_le_top hz.1), (isolatedLine_le_top hz.2).trans hy.2⟩

/-- **The line with a chronologically isolated origin is strongly causal**, by closed intervals. -/
theorem isolatedLine_stronglyCausal : isolatedLine.StronglyCausal := by
  intro p N hN
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨Icc ((l + p) / 2) ((p + u) / 2), Icc_mem_nhds (by linarith) (by linarith),
    fun z hz => hsub ⟨by linarith [hz.1], by linarith [hz.2]⟩,
    isolatedLine_causallyConvexIn_Icc _ _⟩

/-- **The line with a chronologically isolated origin** (kb/0050): strongly causal, causally open,
not tarentin; the theorem gives the open form. -/
theorem isolatedLine_scOpen_without_tarentin :
    isolatedLine.StronglyCausal ∧ isolatedLine.CausallyOpen ∧ ¬ isolatedLine.Tarentin ∧
      isolatedLine.StronglyCausalOpen := by
  exact ⟨isolatedLine_stronglyCausal, isolatedLine_causallyOpen,
    tarentin_and_plain_needed.2.1.2.2.1,
    isolatedLine_stronglyCausal.stronglyCausalOpen_of_causallyOpen isolatedLine_causallyOpen⟩

/-- **The future half of causal openness alone does not open the hull.** The one-way membrane is causally
open in the future, strongly causal and not causally open; for the neighbourhood
`V = {−1 < u < 3, 0 < v < 4, u ≤ v}` of `(0, 1)`, causally convex in `M`, the hull
`J⁺_M(˚V) ∩ J⁻_M(˚V)` contains the membrane point `(1, 1)` and no point `(1 + ε, 1)` of `R`, so it
is not open. The membrane is `StronglyCausalOpen` all the same (`oneWayMembrane_stronglyCausalOpen`):
the argument fails, not the statement. -/
theorem oneWayMembrane_hull_not_isOpen :
    oneWayMembrane.CausallyOpenFuture ∧ oneWayMembrane.StronglyCausal ∧
      ¬ oneWayMembrane.CausallyOpen ∧
      ∃ V ∈ 𝓝 ((0, 1) : ℝ × ℝ), oneWayMembrane.CausallyConvexIn V ⊤ ∧
        ¬ IsOpen (oneWayMembrane.Jplus ⊤ (interior V) ∩ oneWayMembrane.Jminus ⊤ (interior V)) := by
  set V : Set (ℝ × ℝ) := {z | -1 < z.1 ∧ z.1 < 3 ∧ 0 < z.2 ∧ z.2 < 4 ∧ z.1 ≤ z.2}
  set O : Set (ℝ × ℝ) := {z | -1 < z.1 ∧ z.1 < 3 ∧ 0 < z.2 ∧ z.2 < 4 ∧ z.1 < z.2}
  have hOopen : IsOpen O :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          ((isOpen_lt continuous_snd continuous_const).inter
            (isOpen_lt continuous_fst continuous_snd))))
  have hOV : O ⊆ V := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.le⟩
  have hOint : O ⊆ interior V := interior_maximal hOV hOopen
  refine ⟨oneWayMembrane_causallyOpenFuture, oneWayMembrane_stronglyCausalOpen.stronglyCausal,
    oneWayMembrane_not_causallyOpen, V,
    Filter.mem_of_superset (hOopen.mem_nhds ⟨by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩) hOV, ⟨fun _ _ => trivial, fun a _ b hb z hz => ?_⟩, fun hopen => ?_⟩
  · -- `V` is causally convex in `M`
    have hb' : -1 < b.1 ∧ b.1 < 3 ∧ 0 < b.2 ∧ b.2 < 4 ∧ b.1 ≤ b.2 := hb
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := oneWayMembrane_diamond_subset_Icc ⊤ a b hz
    have ha' : -1 < a.1 ∧ a.1 < 3 ∧ 0 < a.2 ∧ a.2 < 4 ∧ a.1 ≤ a.2 := by assumption
    refine ⟨by linarith [ha'.1], by linarith [hb'.2.1], by linarith [ha'.2.2.1],
      by linarith [hb'.2.2.2.1], not_lt.1 fun hzR => ?_⟩
    have hbR : b ∈ membraneRight :=
      oneWayMembrane_mem_right (Causality.mem_diamond.1 hz).2 hzR
    exact absurd hb'.2.2.2.2 (not_le.2 hbR)
  · -- the hull of `˚V` contains `(1, 1)` and no point of `R` near it
    have h11 : ((1, 1) : ℝ × ℝ) ∈
        oneWayMembrane.Jplus ⊤ (interior V) ∩ oneWayMembrane.Jminus ⊤ (interior V) := by
      refine ⟨⟨(0, 1), hOint ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
        oneWayMembrane_le_top_iff.2 ⟨⟨by norm_num, le_rfl⟩, fun h => ?_⟩⟩,
        ⟨(2, 3), hOint ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩,
        oneWayMembrane_le_top_iff.2 ⟨⟨by norm_num, by norm_num⟩, fun h => ?_⟩⟩⟩
      · exact absurd (show (1 : ℝ) < 0 from h) (by norm_num)
      · exact absurd (show (1 : ℝ) < 1 from h) (lt_irrefl 1)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen _ h11
    have hw : ((1 + ε / 2, 1) : ℝ × ℝ) ∈ Metric.ball ((1, 1) : ℝ × ℝ) ε := by
      simp [Metric.mem_ball, Prod.dist_eq, abs_of_pos hε]
      linarith
    obtain ⟨b, hb, hwb⟩ := (hball hw).2
    have hbR : b ∈ membraneRight :=
      oneWayMembrane_mem_right hwb (show (1 : ℝ) < 1 + ε / 2 by linarith)
    have hbV : b.1 ≤ b.2 := (interior_subset hb : b ∈ V).2.2.2.2
    exact absurd hbV (not_le.2 hbR)

end Causal
