import Causal.GluingModels.Tools
import Causal.Lines
import Causal.LinesCurves
import Causal.LinesReachable
import Causal.NestedCausalities
import Causal.NestedConverse
import Causal.NestedTransfer
import Causal.PushUpOfMinimalLocal
import Causal.LocateExtension
import Causal.Dec8MinimalWitness
import Causal.HalfLitDual
import Causal.OneWayMembrane
import Causal.OneWayMembraneChronal
import Causal.GHWithoutTarentin
import Causal.ChronalNeighbourBridge
import Causal.Chains
import Causal.SubExtension
import Causal.RationalJumpPlane
import Causal.RationalLineExtras
import Causal.NotchedPlane
import Causal.TransparentLine
import Causal.DeuxPushup
import Causal.Galileo
import Causal.Subdivision

/-!
# Gluing inventory (DEC-167), ETT layer: the concrete causalities that glue

No paper label is certified by this file. For every concrete causality of the ETT layer that is
absolutely minimal, the inventory of `T-abs-gluing-models` needs both forms of gluing
(`Causal.GluingModels`, `Tools`): **hereditary**, `∀ W, C.AbsolutelyMinimalOn W`, and **on `M`**,
`C.AbsolutelyMinimal` (`def:topological_space_causality_absolutely`, `ETT.tex:397`). This file
proves the forms the strict library lacks; the forms it has are cited in the inventory table
(`lean-causal/campaign/T-abs-gluing-models/REPORT.json`).

* From causal arc-connectedness (`cor:causalement_connexe_minimal`, `ETT.tex:458`, on every open):
  `spacelikeLine`, `halfChronoLine`, `isolatedLine`, `closedHalfLine`, the duals of the membranes.
* By hand, without arc-connectedness: `cutLine a` (a timelike chain, the step across `a` taken in
  one member of the cover), `veeCausality` and `sierpinskiCausality` (the opens of a finite
  space), `diagonalCausality`, `pointSpace`, and Galileo's spacetime with a point as space
  (`galileo 0`, `ex:causalities_lines` item 4 at `n = 0`; a subdivision of the time segment).
* The transparent-point line (`cexemple:point_transparent`, `ETT.tex:472`) is glued on `M`
  (`transparentLine_absolutelyMinimal`) and not hereditarily (`transparentLine_not_hereditary`):
  it is the object that separates the two forms of OQ-95.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used (the vee and the Sierpiński space are not `T1`) |

## SCOPE (disclosed)

* No definition changes. The inventory does not decide the field's form (OQ-95) nor the fate of
  the non-minimal objects (OQ-96); those are in `GluingModels.NonMinimal`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-! ### Lines -/

/-- The spacelike line glues hereditarily (it is causally arc-connected). -/
theorem spacelikeLine_hereditary : ∀ W : Opens ℝ, spacelikeLine.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected spacelikeLine_causallyArcConnected

/-- The half-chronological line glues hereditarily. -/
theorem halfChronoLine_hereditary : ∀ W : Opens ℝ, halfChronoLine.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected halfChronoLine_causallyArcConnected

/-- The line with an isolated origin glues hereditarily. -/
theorem isolatedLine_hereditary : ∀ W : Opens ℝ, isolatedLine.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected isolatedLine_causallyArcConnected

theorem isolatedLine_minimal : isolatedLine.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall isolatedLine_hereditary

/-- The closed half-line glues hereditarily. -/
theorem closedHalfLine_hereditary :
    ∀ W : Opens ClosedHalfLine, closedHalfLine.AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected closedHalfLine_causallyArcConnected

theorem closedHalfLine_minimal : closedHalfLine.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall closedHalfLine_hereditary

/-- The time-reversed half-lit line glues on `M`. -/
theorem halfLightLine_dual_minimal : halfLightLine.dual.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall halfLightLine_dual_absolutelyMinimalOn

/-- The causality of the order of `ℝ` is the lightlike line, which glues hereditarily. -/
theorem linearCausality_real_hereditary :
    ∀ W : Opens ℝ, (linearCausality ℝ).AbsolutelyMinimalOn W :=
  lightlikeLine_absolutelyMinimalOn

/-- The transparent-point line does **not** glue hereditarily: it is not absolutely minimal on
`ℝ ∖ {0}` (`cexemple:point_transparent`); it glues on `M` (`transparentLine_absolutelyMinimal`). -/
theorem transparentLine_not_hereditary :
    ¬ ∀ W : Opens ℝ, transparentLine.AbsolutelyMinimalOn W := fun h =>
  transparentLine_not_absolutelyMinimalOn (h _)

/-! ### The cut line, by hand -/

section CutLine

variable {a : ℝ} {S : Set (Opens ℝ)} {V : Opens ℝ}

/-- A chain of timelike steps from `u` to `v` whose right ends avoid `a` is a chain of steps of
the line cut at `a`. -/
theorem cutLine_chain_of_timelike {u : ℝ} : ∀ v : ℝ,
    TransGen (fun p q => ∃ O ∈ S, timelikeLine.lt (V ⊓ O) p q) u v → a ∉ Ioc u v →
    TransGen (fun p q => ∃ O ∈ S, (cutLine a).lt (V ⊓ O) p q) u v := by
  intro v h
  induction h with
  | single hl =>
    intro ha
    obtain ⟨O, hO, hlt, hsub⟩ := hl
    exact TransGen.single ⟨O, hO, hlt, fun hb => ha (hb ▸ ⟨hlt, le_rfl⟩), hsub⟩
  | @tail b c hc hl ih =>
    intro ha
    obtain ⟨O, hO, hlt, hsub⟩ := hl
    have hub : u < b := (Precausality.lt_of_transGen hc).1
    refine (ih fun h' => ha ⟨h'.1, h'.2.trans hlt.le⟩).tail ⟨O, hO, hlt, fun hb => ?_, hsub⟩
    exact ha (hb ▸ ⟨hub.trans hlt, le_rfl⟩)

/-- The chronological half of the cut line's hereditary gluing. -/
theorem cutLine_lt_chain {W : Opens ℝ} (hS : ∀ x ∈ W, ∃ O ∈ S, x ∈ O) (hV : V ≤ W) {x y : ℝ}
    (hxy : (cutLine a).lt V x y) :
    TransGen (fun p q => ∃ O ∈ S, (cutLine a).lt (V ⊓ O) p q) x y := by
  obtain ⟨hlt, hya, hsub⟩ := hxy
  have htl : ∀ u v, u < v → Icc u v ⊆ (V : Set ℝ) →
      TransGen (fun p q => ∃ O ∈ S, timelikeLine.lt (V ⊓ O) p q) u v := fun u v huv hs =>
    ((timelikeLine_absolutelyMinimalOn W) S hS V hV u v).2 ⟨huv, hs⟩
  by_cases ha : a ∈ Ioc x y
  · -- the step across `a`, inside one member of the cover
    have hay : a < y := lt_of_le_of_ne ha.2 (Ne.symm hya)
    have haV : a ∈ V := hsub ⟨ha.1.le, ha.2⟩
    obtain ⟨O₀, hO₀, haO₀⟩ := hS a (hV haV)
    obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 ((V ⊓ O₀).isOpen.mem_nhds ⟨haV, haO₀⟩)
    set u := (max l x + a) / 2 with hu
    set w := (a + min r y) / 2 with hw
    have hlx : max l x < a := max_lt hl ha.1
    have hry : a < min r y := lt_min hr hay
    have hxu : x < u := by have := le_max_right l x; rw [hu]; linarith
    have hua : u < a := by rw [hu]; linarith
    have haw : a < w := by rw [hw]; linarith
    have hwy : w < y := by have := min_le_right r y; rw [hw]; linarith
    have hlu : l < u := by have := le_max_left l x; rw [hu]; linarith
    have hwr : w < r := by have := min_le_left r y; rw [hw]; linarith
    have h₁ := cutLine_chain_of_timelike (a := a) u
      (htl x u hxu (fun z hz => hsub ⟨hz.1, hz.2.trans (hua.trans hay).le⟩))
      (fun h => absurd (h.2.trans_lt hua) (lt_irrefl a))
    have h₂ : ∃ O ∈ S, (cutLine a).lt (V ⊓ O) u w :=
      ⟨O₀, hO₀, hua.trans haw, haw.ne', fun z hz => hlr ⟨hlu.trans_le hz.1, hz.2.trans_lt hwr⟩⟩
    have h₃ := cutLine_chain_of_timelike (a := a) (u := w) y
      (htl w y hwy (fun z hz => hsub ⟨(hxu.trans (hua.trans haw)).le.trans hz.1, hz.2⟩))
      (fun h => absurd (haw.trans h.1) (lt_irrefl a))
    exact (h₁.tail h₂).trans h₃
  · exact cutLine_chain_of_timelike y (htl x y hlt hsub) ha

/-- **The line cut at `a` glues hereditarily**, by hand rather than from causal arc-connectedness
(which is argued to fail, no causal curve crossing `a` upwards, but is not proved here): a timelike
chain whose right ends avoid `a`, the step across `a` taken in one member of the cover. -/
theorem cutLine_hereditary (a : ℝ) : ∀ W : Opens ℝ, (cutLine a).AbsolutelyMinimalOn W := by
  intro W S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => cutLine_lt_chain hS hV hxy⟩
  rcases hxy with ⟨rfl, hx⟩ | hlt
  · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩
  · exact TransGen.mono (fun p q ⟨O, hO, h⟩ => ⟨O, hO, (cutLine a).le_of_lt h⟩)
      (cutLine_lt_chain hS hV hlt)

theorem cutLine_minimal (a : ℝ) : (cutLine a).AbsolutelyMinimal :=
  absolutelyMinimal_of_forall (cutLine_hereditary a)

end CutLine

/-! ### Planes, arcs, membranes -/

/-- The time-reversed chronal membrane glues on `M`. -/
theorem chronalMembrane_dual_minimal : chronalMembrane.dual.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall chronalMembrane_dual_absolutelyMinimalOn

/-- The fork glues on `M`. -/
theorem fork_minimal : forkCausality.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall fork_absolutelyMinimalOn

/-- The loop fan glues on `M`. -/
theorem loopFan_minimal : loopFan.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall loopFan_absolutelyMinimalOn

/-! ### Finite and discrete spaces -/

/-- **The vee glues hereditarily**: in each open `W`, a cover of `W` has a member containing
`left` (hence `mid`) when `left ∈ W`, and one containing `right` (hence `mid`) when `right ∈ W`. -/
theorem veeCausality_hereditary : ∀ W : Opens Vee, veeCausality.AbsolutelyMinimalOn W := by
  intro W S hS V hV x y
  have step : ∀ {O : Opens Vee}, O ∈ S → ∀ {a b : Vee}, a ∈ V → b ∈ V → a ∈ O → b ∈ O →
      a.rank ≤ b.rank →
      TransGen (fun a b => ∃ O ∈ S, veeCausality.le (V ⊓ O) a b) a b :=
    fun hO _ _ ha hb haO hbO hab => TransGen.single ⟨_, hO, ⟨ha, haO⟩, ⟨hb, hbO⟩, hab⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, hy, hxy⟩
    cases x <;> cases y
    · obtain ⟨O, hO, h⟩ := hS _ (hV hx); exact step hO hx hy h h le_rfl
    · obtain ⟨O, hO, h⟩ := hS _ (hV hx)
      exact step hO hx hy h (Vee.mid_mem_of_left_mem O h) (by decide)
    · have hmV : Vee.mid ∈ V := Vee.mid_mem_of_left_mem V hx
      obtain ⟨Ol, hOl, hl⟩ := hS _ (hV hx)
      obtain ⟨Or, hOr, hr⟩ := hS _ (hV hy)
      exact (step hOl hx hmV hl (Vee.mid_mem_of_left_mem Ol hl) (by decide)).trans
        (step hOr hmV hy (Vee.mid_mem_of_right_mem Or hr) hr (by decide))
    · exact absurd hxy (by decide)
    · obtain ⟨O, hO, h⟩ := hS _ (hV hx); exact step hO hx hy h h le_rfl
    · obtain ⟨O, hO, h⟩ := hS _ (hV hy)
      exact step hO hx hy (Vee.mid_mem_of_right_mem O h) h (by decide)
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · obtain ⟨O, hO, h⟩ := hS _ (hV hx); exact step hO hx hy h h le_rfl
  · rintro ⟨hlV, hx, rfl⟩
    obtain ⟨Ol, hOl, hl⟩ := hS _ (hV hlV)
    exact TransGen.single ⟨Ol, hOl, ⟨hlV, hl⟩, hx, rfl⟩

/-- **The Sierpiński causality glues hereditarily**: on `M` by `sierpinskiCausality_absolutelyMinimal`;
on an open `W ≠ ⊤` every open `V ≤ W` differs from `⊤`, so `≤_V` is the diagonal and `≪_V` empty. -/
theorem sierpinskiCausality_hereditary :
    ∀ W : Opens Prop, sierpinskiCausality.AbsolutelyMinimalOn W := by
  intro W
  by_cases hW : W = ⊤
  · subst hW
    exact Precausality.absolutelyMinimal_iff.1 sierpinskiCausality_absolutelyMinimal
  · intro S hS V hV x y
    have hVt : V ≠ ⊤ := fun h => hW (top_le_iff.1 (h ▸ hV))
    refine ⟨fun hxy => ?_, fun hxy => absurd hxy hVt⟩
    rcases hxy with ⟨rfl, hx⟩ | h
    · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
      exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩
    · exact absurd h hVt

/-- The diagonal causality of a discrete space glues hereditarily. -/
theorem diagonalCausality_hereditary (M : Type*) [TopologicalSpace M] [DiscreteTopology M] :
    ∀ W : Opens M, (diagonalCausality M).AbsolutelyMinimalOn W := by
  intro W S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩ <;>
  · obtain ⟨hx, -, rfl⟩ := hxy
    obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    exact TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hx, hxO⟩, rfl⟩

theorem diagonalCausality_minimal (M : Type*) [TopologicalSpace M] [DiscreteTopology M] :
    (diagonalCausality M).AbsolutelyMinimal :=
  absolutelyMinimal_of_forall (diagonalCausality_hereditary M)

/-- The point space glues hereditarily. -/
theorem pointSpace_hereditary : ∀ W : Opens Unit, pointSpace.AbsolutelyMinimalOn W := by
  intro W S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => hxy.2.2.elim⟩
  obtain ⟨hx, hy, -⟩ := hxy
  obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
  have hyO : y ∈ O := Subsingleton.elim x y ▸ hxO
  exact TransGen.single ⟨O, hO, ⟨hx, hxO⟩, ⟨hy, hyO⟩, trivial⟩

theorem pointSpace_minimal : pointSpace.AbsolutelyMinimal :=
  absolutelyMinimal_of_forall pointSpace_hereditary

/-! ### Galileo's spacetime with a point as space -/

section GalileoPoint

variable {X : Type*} [TopologicalSpace X] [Subsingleton X] [LocallyConnectedSpace (ℝ × X)]

omit [LocallyConnectedSpace (ℝ × X)] in
/-- With a point as space, `p ≪_V q` puts the whole time segment `[p.1, q.1]` (at the one point of
space) inside the component of `p` in `V`. -/
theorem galileo_point_segment {V : Opens (ℝ × X)} {p q : ℝ × X}
    (hq : q ∈ connectedComponentIn (V : Set (ℝ × X)) p) :
    ∀ s ∈ Icc p.1 q.1, ((s, p.2) : ℝ × X) ∈ connectedComponentIn (V : Set (ℝ × X)) p := by
  intro s hs
  have hpV : p ∈ (V : Set (ℝ × X)) := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hq
    exact hq
  have hpre : IsPreconnected (Prod.fst '' connectedComponentIn (V : Set (ℝ × X)) p) :=
    isPreconnected_connectedComponentIn.image _ continuous_fst.continuousOn
  obtain ⟨r, hr, hrs⟩ := hpre.Icc_subset ⟨p, mem_connectedComponentIn hpV, rfl⟩ ⟨q, hq, rfl⟩ hs
  have : r = (s, p.2) := Prod.ext hrs (Subsingleton.elim _ _)
  exact this ▸ hr

/-- **Galileo's spacetime with a point as space glues hereditarily** (`n = 0` in
`ex:causalities_lines` item 4): a chronological relation runs along the time segment, which a
subdivision cuts into steps inside the members of the cover. -/
theorem galileoOn_point_hereditary : ∀ W : Opens (ℝ × X), (galileoOn X).AbsolutelyMinimalOn W := by
  intro W S hS V hV
  -- the chronological half
  have hlt : ∀ p q : ℝ × X, (galileoOn X).lt V p q →
      TransGen (fun a b => ∃ O ∈ S, (galileoOn X).lt (V ⊓ O) a b) p q := by
    rintro p q ⟨hpV, hpq, hqc⟩
    let φ : ℝ → ℝ × X := fun s => (s, p.2)
    have hφ : Continuous φ := continuous_id.prodMk continuous_const
    have hseg := galileo_point_segment hqc
    have hsegV : ∀ s ∈ Icc p.1 q.1, φ s ∈ (V : Set (ℝ × X)) := fun s hs =>
      connectedComponentIn_subset _ _ (hseg s hs)
    have hcover : Icc p.1 q.1 ⊆ ⋃ i : S, φ ⁻¹' ((V ⊓ i.1 : Opens (ℝ × X)) : Set (ℝ × X)) := by
      intro s hs
      obtain ⟨O, hO, hsO⟩ := hS (φ s) (hV (hsegV s hs))
      exact mem_iUnion.2 ⟨⟨O, hO⟩, ⟨hsegV s hs, hsO⟩⟩
    obtain ⟨t, ht0, hmono, ⟨m, hm⟩, -, hsub⟩ := exists_subdivision_Icc hpq.le
      (fun i : S => (V ⊓ i.1).isOpen.preimage hφ) hcover
    have key : ∀ n, ReflTransGen (fun a b => ∃ O ∈ S, (galileoOn X).lt (V ⊓ O) a b) p (φ (t n)) := by
      intro n
      induction n with
      | zero =>
        have : φ (t 0) = p := Prod.ext (by simp [φ, ht0]) rfl
        rw [this]
      | succ n ih =>
        obtain ⟨i, hi⟩ := hsub n
        rcases (hmono (Nat.le_succ n)).eq_or_lt with heq | hlt'
        · rwa [← heq]
        refine ih.tail ⟨i.1, i.2, hi ⟨le_rfl, hlt'.le⟩, hlt', ?_⟩
        have hT : IsPreconnected (φ '' Icc (t n) (t (n + 1))) :=
          isPreconnected_Icc.image _ hφ.continuousOn
        exact hT.subset_connectedComponentIn ⟨t n, ⟨le_rfl, hlt'.le⟩, rfl⟩
          (by rintro _ ⟨r, hr, rfl⟩; exact hi hr) ⟨t (n + 1), ⟨hlt'.le, le_rfl⟩, rfl⟩
    have hend : φ (t m) = q := Prod.ext (by simp [φ, hm m le_rfl]) (Subsingleton.elim _ _)
    have hpq' := key m
    rw [hend] at hpq'
    rcases reflTransGen_iff_eq_or_transGen.1 hpq' with h | h
    · exact absurd (congrArg Prod.fst h) (ne_of_gt hpq)
    · exact h
  intro x y
  refine ⟨fun hxy => ?_, hlt x y⟩
  rcases hxy with h | ⟨rfl, hx⟩
  · exact TransGen.mono (fun a b ⟨O, hO, hab⟩ => ⟨O, hO, Or.inl hab⟩) (hlt x y h)
  · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    exact TransGen.single ⟨O, hO, Or.inr ⟨rfl, hx, hxO⟩⟩

/-- Galileo's spacetime `ℝ^{0+1}` glues hereditarily. -/
theorem galileo_zero_hereditary : ∀ W, (galileo 0).AbsolutelyMinimalOn W :=
  galileoOn_point_hereditary

end GalileoPoint

end GluingModels

end Causal
