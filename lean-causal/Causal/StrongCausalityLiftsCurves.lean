import Causal.StrongCausalityLifts
import Causal.GXStructure
import Causal.FutureOneConnectedVacuous
import Causal.GluingModels.NonMinimal

/-!
# The lifting of strong causality with `≤` realised by causal curves, and the glued refutation

No label of `ETT.tex` is certified here, and none is marked. ETT programme, layer 1, target
`T-abs-lift-curves-forms` (`programme/roadmap.toml:2018`), proposed by the auditor of
`T-abs-strong-causality-lifts` (`campaign/T-abs-strong-causality-lifts/AUDIT-1.json`, findings
1–2). OQ-145 (OPEN) asks whether the amended lifting statement is the statement of record. This
file gives the amendment in its harc form and decides nothing. The target, as recorded
(`programme/roadmap.toml:2019`):

> The lifting theorems with harc, and the glued refutation: stronglyCausal_lift and its
> Alexandrov, open and weak-morphism forms with ≤ at ⊤ realised by causal curves over [0, 1] in
> place of CausallyArcConnected; one declaration refuting the printed form with gluing (∀ W,
> AbsolutelyMinimalOn W of N, M and X) and continuity of p and D inside the negated statement;
> symmRationalLine not causal and not tarentin

`harc` is `∀ a z, C.le ⊤ a z → ∃ c, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z`: `≤` at `⊤`
realised by causal curves of `⊤` over `[0, 1]`. The bridges `mem_connectedComponentIn_diamond_of_curves`
and `le_top_map_of_curves` (`Causal.StrongCausalityLifts`) take it.

## What is proved

* **The harc forms** `Causality.stronglyCausal_lift_of_le_realised`,
  `alexandrovTopology_eq_lift_of_le_realised`, `stronglyCausalOpen_lift_of_le_realised`,
  `stronglyCausal_lift_of_weakMorphism_of_le_realised`, `stronglyCausal_lift_self_of_le_realised`.
  Each is its original with `hC : C.CausallyArcConnected` replaced by `harc`, nothing else
  changed. Five `example`s, typed by the originals' own types (`type_of%`), derive each original
  through `CausallyArcConnected.exists_causalCurveOn_top`. The suffix is not `_of_curves`, so
  `not_stronglyCausal_lift_of_curves` (the printed form refuted) does not read as their negation.
* **Strictly weaker than arc-connectedness**: `orderLine_strongCausalityLift_of_le_realised`.
  `orderLine` is not causally arc-connected, meets `harc` and the other hypotheses, and the harc
  forms give its strong causality. It is not absolutely minimal: no-gluing reading only.
* **The glued refutation** `not_stronglyCausal_lift_of_curves_glued`, one statement: inside the
  negated `∀`, `∀ W, AbsolutelyMinimalOn W` for `N`, `M`, `X` (hereditary gluing, DEC-167; it
  implies the whole-space form `AbsolutelyMinimal` by `GluingModels.absolutelyMinimal_of_forall`), `Continuous p`,
  `Continuous D`. Witness: `symmRationalLine` into the timelike line, `p = D = id`.
* **The line**: `symmRationalLine_not_isCausal`, `symmRationalLine_not_tarentin` (cited from
  `symmRationalLine_separates_futureOneConnected`) and `symmRationalLine_not_le_realised`.
  `symmRationalLine_separates_lift_glued` conjoins them with what the refutation discharges.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `harc` | ⚠ strengthened against the printed form (refuted without it: `not_stronglyCausal_lift_of_curves`, and with gluing `not_stronglyCausal_lift_of_curves_glued`); ⚠ weakened against the originals (`CausallyArcConnected`) |
| curves to curves, `M`, `X` strongly causal, basis, `τ ≤ τc`, tarentin | ✓ carried, as in the originals |
| refutation: gluing of `N`, `M`, `X`; `p`, `D` continuous | ✓ inside the negated statement |

## SCOPE (disclosed)

* The harc forms are the amendment of OQ-145, not the printed form, which is false
  (`not_stronglyCausal_lift_of_curves`; here also under gluing and continuity).
* The witness `N` is not causal and not tarentin: the refutation says nothing about a causal
  or tarentin `N`. Whether `harc` is strictly weaker than arc-connectedness under gluing is
  not treated (`orderLine` does not glue).
* Layer 1: the four imports are ETT-layer (`tools/ladder.py` `model_path`, kb/0247).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set TopologicalSpace Topology Filter

universe u v w

section Lift

variable {M : Type v} {X : Type w} [TopologicalSpace M] [TopologicalSpace X]

namespace Causality

variable {CM : Causality M} {CX : Causality X}

/-! ### The harc forms -/

/-- **Strong causality lifts, with `≤` realised by causal curves.** `stronglyCausal_lift` with
`hC : C.CausallyArcConnected` replaced by `harc`: two points with `a ≤_N z` are joined by a
causal curve of `N` over `[0, 1]`. -/
theorem stronglyCausal_lift_of_le_realised {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc)
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  exact stronglyCausal_of_lift τc (mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (le_top_map_of_curves harc hp) (le_top_map_of_curves harc hD) hM hX hB

/-- **With tarentin, the topology of `N` is its Alexandrov topology**, `≤` realised by causal
curves. -/
theorem alexandrovTopology_eq_lift_of_le_realised {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc)
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hT : C.Tarentin)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.alexandrovTopology = ‹TopologicalSpace N› := by
  exact (stronglyCausal_lift_of_le_realised τc hτ harc hp hD hM hX hB).alexandrovTopology_eq hT

/-- The open form of the lift, `≤` realised by causal curves. -/
theorem stronglyCausalOpen_lift_of_le_realised {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc)
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausalOpen) (hX : CX.StronglyCausalOpen)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausalOpen := by
  exact stronglyCausalOpen_of_lift τc (mem_connectedComponentIn_diamond_of_curves τc hτ harc)
    (le_top_map_of_curves harc hp) (le_top_map_of_curves harc hD) hM hX hB

/-- The lift for weak morphisms `p`, `D`, `≤` realised by causal curves. -/
theorem stronglyCausal_lift_of_weakMorphism_of_le_realised {N : Type u}
    (τc : TopologicalSpace N) [TopologicalSpace N] {C : Causality N} {p : N → M} {D : N → X}
    (hτ : ‹TopologicalSpace N› ≤ τc)
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hp : WeakMorphism C CM p) (hD : WeakMorphism C CX D)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  exact stronglyCausal_lift_of_le_realised τc hτ harc
    (fun _ hc => hp.causalCurveOn_comp (V := ⊤) (U := ⊤) (fun _ _ => trivial) hc)
    (fun _ hc => hD.causalCurveOn_comp (V := ⊤) (U := ⊤) (fun _ _ => trivial) hc) hM hX hB

/-- The lift with the components taken in the topology of `N`, `≤` realised by causal
curves. -/
theorem stronglyCausal_lift_self_of_le_realised {N : Type u} [TopologicalSpace N]
    {C : Causality N} {p : N → M} {D : N → X}
    (harc : ∀ a z : N, C.le ⊤ a z → ∃ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z)
    (hp : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CM.CausalCurveOn ⊤ (p ∘ c) 0 1)
    (hD : ∀ c : ℝ → N, C.CausalCurveOn ⊤ c 0 1 → CX.CausalCurveOn ⊤ (D ∘ c) 0 1)
    (hM : CM.StronglyCausal) (hX : CX.StronglyCausal)
    (hB : ∀ x : N, (𝓝 x).HasBasis
      (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
      (fun WV => connectedComponentIn (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) :
    C.StronglyCausal := by
  exact stronglyCausal_lift_of_le_realised ‹TopologicalSpace N› le_rfl harc hp hD hM hX hB

end Causality

end Lift

/-! ### The causally arc-connected forms follow

Each `example` has its original's own type (`type_of%`), and proves it from the harc form
through `CausallyArcConnected.exists_causalCurveOn_top`. -/

example : type_of% @Causality.stronglyCausal_lift := by
  intro M X _ _ CM CX N τc _ C p D hτ hC hp hD hM hX hB
  exact Causality.stronglyCausal_lift_of_le_realised τc hτ
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hC) hp hD hM hX hB

example : type_of% @Causality.alexandrovTopology_eq_lift := by
  intro M X _ _ CM CX N τc _ C p D hτ hC hT hp hD hM hX hB
  exact Causality.alexandrovTopology_eq_lift_of_le_realised τc hτ
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hC) hT hp hD hM hX hB

example : type_of% @Causality.stronglyCausalOpen_lift := by
  intro M X _ _ CM CX N τc _ C p D hτ hC hp hD hM hX hB
  exact Causality.stronglyCausalOpen_lift_of_le_realised τc hτ
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hC) hp hD hM hX hB

example : type_of% @Causality.stronglyCausal_lift_of_weakMorphism := by
  intro M X _ _ CM CX N τc _ C p D hτ hC hp hD hM hX hB
  exact Causality.stronglyCausal_lift_of_weakMorphism_of_le_realised τc hτ
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hC) hp hD hM hX hB

example : type_of% @Causality.stronglyCausal_lift_self := by
  intro M X _ _ CM CX N _ C p D hC hp hD hM hX hB
  exact Causality.stronglyCausal_lift_self_of_le_realised
    (Causality.CausallyArcConnected.exists_causalCurveOn_top hC) hp hD hM hX hB

/-! ### The harc forms reach beyond causal arc-connectedness: `orderLine` -/

/-- A causal curve of the timelike line is one of `orderLine`: `≤_U` of the timelike line lies
in `orderLine`'s. -/
theorem orderLine_causalCurveOn_of_timelikeLine {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hc : timelikeLine.CausalCurveOn W c a b) : orderLine.CausalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht N hN htN
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
    obtain ⟨hle, hsub⟩ := timelikeLine_le.1 (h s hs s' hs' h1 h2 h3)
    exact ⟨hle, hsub (left_mem_Icc.2 hle), hsub (right_mem_Icc.2 hle)⟩

/-- A causal curve of `orderLine` at `⊤` is one of the timelike line: near `c t` it is
non-decreasing inside an open interval around `c t`, which is convex. -/
theorem timelikeLine_causalCurveOn_of_orderLine {c : ℝ → ℝ} {a b : ℝ}
    (hc : orderLine.CausalCurveOn ⊤ c a b) : timelikeLine.CausalCurveOn ⊤ c a b where
  mem _ _ := trivial
  rel t ht N _ htN := by
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    obtain ⟨l', u', hl', hu', h⟩ := hc.rel t ht ⟨Ioo l u, isOpen_Ioo⟩ le_top ⟨hl, hu⟩
    refine ⟨l', u', hl', hu', fun s hs s' hs' h1 h2 h3 => ?_⟩
    obtain ⟨hle, hs1, hs2⟩ := h s hs s' hs' h1 h2 h3
    have hs1' : c s ∈ Ioo l u := hs1
    have hs2' : c s' ∈ Ioo l u := hs2
    exact timelikeLine_le.2 ⟨hle, fun z hz => hsub ⟨hs1'.1.trans_le hz.1, hz.2.trans_lt hs2'.2⟩⟩

/-- **`≤` of `orderLine` at `⊤` is realised by causal curves**: `a ≤ z` is joined by the
segment `t ↦ a + t (z - a)`. -/
theorem orderLine_le_realised :
    ∀ a z : ℝ, orderLine.le ⊤ a z →
      ∃ c : ℝ → ℝ, orderLine.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z := by
  intro a z haz
  have hza : 0 ≤ z - a := sub_nonneg.2 haz.1
  refine ⟨fun t => a + t * (z - a), orderLine_causalCurveOn_of_timelikeLine
    (timelikeLine_causalCurveOn_of_monotone (fun s t hst => ?_) (by fun_prop) 0 1),
    by simp, by ring⟩
  exact add_le_add_right (mul_le_mul_of_nonneg_right hst hza) a

/-- **`orderLine` is not causally arc-connected**: `0 ≤ 2` in `ℝ ∖ {1}`, and no curve of
`ℝ ∖ {1}` joins them. -/
theorem orderLine_not_causallyArcConnected : ¬ orderLine.CausallyArcConnected := by
  intro h
  let U : Opens ℝ := ⟨{1}ᶜ, isOpen_compl_singleton⟩
  have h02 : orderLine.le U 0 2 :=
    ⟨by norm_num, show (0 : ℝ) ∈ ({1}ᶜ : Set ℝ) by norm_num,
      show (2 : ℝ) ∈ ({1}ᶜ : Set ℝ) by norm_num⟩
  obtain ⟨c, hc, h0, h1⟩ := (h U le_top 0 2).1.1 h02
  have hcont : ContinuousOn c (Icc 0 1) := CurveOn.continuousOn orderLine.isRelFamily_le hc
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc zero_le_one hcont
    (show (1 : ℝ) ∈ Icc (c 0) (c 1) by rw [h0, h1]; norm_num)
  have hmem : c t ∈ ({1}ᶜ : Set ℝ) := hc.mem t ht
  exact hmem hct

/-- **The harc forms apply where the causally arc-connected forms do not.** `orderLine` (the
order of `ℝ` restricted to each open set) is not causally arc-connected, but its `≤` at `⊤` is
realised by causal curves. `id` into the timelike line sends its causal curves to causal curves,
and the basis holds with the components in `ℝ`. So `stronglyCausal_lift_self_of_le_realised` and
`stronglyCausalOpen_lift_of_le_realised` give its strong causality in both forms. It is not
absolutely minimal (`GluingModels.orderLine_not_minimal`): a witness of the no-gluing reading only. -/
theorem orderLine_strongCausalityLift_of_le_realised :
    ¬ orderLine.CausallyArcConnected ∧
      (∀ a z : ℝ, orderLine.le ⊤ a z →
        ∃ c : ℝ → ℝ, orderLine.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z) ∧
      (∀ c : ℝ → ℝ, orderLine.CausalCurveOn ⊤ c 0 1 →
        timelikeLine.CausalCurveOn ⊤ (id ∘ c) 0 1) ∧
      ¬ orderLine.AbsolutelyMinimal ∧ orderLine.StronglyCausal ∧ orderLine.StronglyCausalOpen := by
  obtain ⟨-, -, -, hsc, hsco, -⟩ := timelikeLine_strongCausalityLift
  have hp : ∀ c : ℝ → ℝ, orderLine.CausalCurveOn ⊤ c 0 1 →
      timelikeLine.CausalCurveOn ⊤ (id ∘ c) 0 1 := fun _ hc =>
    timelikeLine_causalCurveOn_of_orderLine hc
  exact ⟨orderLine_not_causallyArcConnected, orderLine_le_realised, hp,
    GluingModels.orderLine_not_minimal,
    Causality.stronglyCausal_lift_self_of_le_realised orderLine_le_realised hp hp hsc hsc
      real_hasBasis_connectedComponentIn_inter,
    Causality.stronglyCausalOpen_lift_of_le_realised _ le_rfl orderLine_le_realised hp hp hsco
      hsco real_hasBasis_connectedComponentIn_inter⟩

/-! ### The symmetric rational line: not causal, not tarentin, `≤` not realised by curves -/

/-- **The symmetric rational line is not causal**: `0 ≤_ℝ 1 ≤_ℝ 0`. Cited from
`symmRationalLine_separates_futureOneConnected`, where it is a conjunct. -/
theorem symmRationalLine_not_isCausal : ¬ symmRationalLine.IsCausal := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := symmRationalLine_separates_futureOneConnected
  exact h

/-- **The symmetric rational line is not tarentin**: an irrational point of `J_ℝ(p, q)` is `p`,
so no diamond has interior. Cited from `symmRationalLine_separates_futureOneConnected`. -/
theorem symmRationalLine_not_tarentin : ¬ symmRationalLine.Tarentin := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    symmRationalLine_separates_futureOneConnected
  exact h

/-- **`≤` of the symmetric rational line is not realised by causal curves** (`harc` fails):
`0 ≤_ℝ 1`, and its causal curves are constant. -/
theorem symmRationalLine_not_le_realised :
    ¬ ∀ a z : ℝ, symmRationalLine.le ⊤ a z →
      ∃ c : ℝ → ℝ, symmRationalLine.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z := by
  intro h
  have h01 : symmRationalLine.le ⊤ 0 1 :=
    Or.inr ⟨⟨0, by simp⟩, ⟨1, by simp⟩, fun _ _ => trivial⟩
  obtain ⟨c, hc, h0, h1⟩ := h 0 1 h01
  have := symmRationalLine_causalCurveOn_eq hc (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [h0, h1] at this
  norm_num at this

/-- **The conjoined witness of the glued refutation.** The symmetric rational line and the
timelike line are absolutely minimal on every open set (hereditary gluing, DEC-167), `id` is
continuous and sends each causal curve of the symmetric rational line in any open `U` to a causal
curve of the timelike line in every open `U' ⊇ U`, the timelike line is strongly causal, and the
basis holds with the components in `ℝ`. The symmetric rational line is not strongly causal, not
causally arc-connected, not causal, not tarentin, and its `≤` is not realised by causal curves. -/
theorem symmRationalLine_separates_lift_glued :
    (∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W) ∧
      (∀ W : Opens ℝ, timelikeLine.AbsolutelyMinimalOn W) ∧ Continuous (id : ℝ → ℝ) ∧
      (∀ (U U' : Opens ℝ), MapsTo (id : ℝ → ℝ) U U' → ∀ (c : ℝ → ℝ) (a b : ℝ),
        symmRationalLine.CausalCurveOn U c a b → timelikeLine.CausalCurveOn U' (id ∘ c) a b) ∧
      timelikeLine.StronglyCausal ∧
      (∀ x : ℝ, (𝓝 x).HasBasis
        (fun WV : Set ℝ × Set ℝ => IsOpen WV.1 ∧ id x ∈ WV.1 ∧ IsOpen WV.2 ∧ id x ∈ WV.2)
        (fun WV => connectedComponentIn (id ⁻¹' WV.1) x ∩ id ⁻¹' WV.2)) ∧
      ¬ symmRationalLine.StronglyCausal ∧ ¬ symmRationalLine.CausallyArcConnected ∧
      ¬ symmRationalLine.IsCausal ∧ ¬ symmRationalLine.Tarentin ∧
      ¬ (∀ a z : ℝ, symmRationalLine.le ⊤ a z →
        ∃ c : ℝ → ℝ, symmRationalLine.CausalCurveOn ⊤ c 0 1 ∧ c 0 = a ∧ c 1 = z) := by
  obtain ⟨hAM, hcurve, hsc, hB, hNSC, hNAC⟩ := symmRationalLine_separates_lift
  exact ⟨hAM, Causality.CausallyArcConnected.absolutelyMinimalOn_all
    timelikeLine_causallyArcConnected, continuous_id, hcurve, hsc, hB, hNSC, hNAC,
    symmRationalLine_not_isCausal, symmRationalLine_not_tarentin,
    symmRationalLine_not_le_realised⟩

/-! ### The glued refutation -/

/-- **The printed form is false under gluing, with `p` and `D` continuous.** Inside the negated
statement: `N`, `M` and `X` are absolutely minimal on every open set (the hereditary gluing of
DEC-167, which implies the whole-space form `AbsolutelyMinimal`), `p` and `D` are continuous, and the rest is
`not_stronglyCausal_lift_of_curves`'s. -/
theorem not_stronglyCausal_lift_of_curves_glued :
    ¬ ∀ (N M X : Type) (τc : TopologicalSpace N) [TopologicalSpace N] [TopologicalSpace M]
      [TopologicalSpace X] (C : Causality N) (CM : Causality M) (CX : Causality X) (p : N → M)
      (D : N → X),
      (∀ W : Opens N, C.AbsolutelyMinimalOn W) → (∀ W : Opens M, CM.AbsolutelyMinimalOn W) →
      (∀ W : Opens X, CX.AbsolutelyMinimalOn W) → Continuous p → Continuous D →
      ‹TopologicalSpace N› ≤ τc →
      (∀ (U : Opens N) (U' : Opens M), MapsTo p U U' → ∀ (c : ℝ → N) (a b : ℝ),
        C.CausalCurveOn U c a b → CM.CausalCurveOn U' (p ∘ c) a b) →
      (∀ (U : Opens N) (U' : Opens X), MapsTo D U U' → ∀ (c : ℝ → N) (a b : ℝ),
        C.CausalCurveOn U c a b → CX.CausalCurveOn U' (D ∘ c) a b) →
      CM.StronglyCausal → CX.StronglyCausal →
      (∀ x : N, (𝓝 x).HasBasis
        (fun WV : Set M × Set X => IsOpen WV.1 ∧ p x ∈ WV.1 ∧ IsOpen WV.2 ∧ D x ∈ WV.2)
        (fun WV => @connectedComponentIn N τc (p ⁻¹' WV.1) x ∩ D ⁻¹' WV.2)) →
      C.StronglyCausal := by
  intro h
  obtain ⟨hAM, hTL, hid, hcurve, hsc, hB, hNSC, -⟩ := symmRationalLine_separates_lift_glued
  exact hNSC (h ℝ ℝ ℝ _ symmRationalLine timelikeLine timelikeLine id id hAM hTL hTL hid hid
    le_rfl hcurve hcurve hsc hsc hB)

end Causal
