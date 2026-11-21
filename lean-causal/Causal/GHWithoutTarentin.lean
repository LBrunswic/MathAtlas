import Causal.Ladder.Rules

/-!
# Global hyperbolicity without tarentin gives neither a time function nor strong causality: the fork and the loop fan

Programme target `T-abs-gh-without-tarentin` (its block in `programme/roadmap.toml`; layer 1, no
label of `ETT.tex`). Imports: `Causal.Ladder.Rules` only (the `causal_ladder` tactic; ETT layer: no
model, no CBG, Splitting, LemmaK* or LevinUtility module, transitively). Each property is the
ladder's definition (the `lean` field of its `[[property]]` in `programme/ladder.toml`). Two
subspaces of `ℝ × ℝ`, each carrying the causality of a family of oriented arcs (`arcCausality`:
`x ≤_U y` iff `x = y ∈ U` or a chain of steps along the arcs inside `U` runs from `x` to `y`; `≪`
empty), which for coherent arcs (`ArcCoherent`) is "`y` follows `x` along one arc, the piece
between them inside `U`" (`ArcCoherent.le_iff`). The planner's sketch is confirmed in every claim;
nothing is refuted; the coordinates are changed (SCOPE).

* **`T-abs-gh-without-tarentin/1-arcs`** — `arcCausality`: causally arc-connected
  (`arcCausality_causallyArcConnected`), absolutely minimal, and on every open set for every cover
  (`arcCausality_absolutelyMinimalOn`), push-up, no chronal neighbours; for coherent arcs one step
  (`ArcCoherent.le_iff`, `le_top_iff`), causal, diamonds the arc pieces
  (`ArcCoherent.diamond_eq_image`), causally compact, globally hyperbolic, a time function from a
  continuous `T` strictly increasing along each arc (`ArcCoherent.hasTimeFunction`), and causal
  convexity of a set convex along each arc (`ArcCoherent.causallyConvexIn`).
* **`T-abs-gh-without-tarentin/2-fork`** — `forkCausality` on `forkSet`: arcs `a → w → x_n` and
  `b → y_n`, `x_n → b`, `y_n → a` (`tendsto_forkX`, `tendsto_forkY`); coherent (`forkγ_coherent`),
  globally hyperbolic; every open box causally convex (`fork_causallyConvexIn_box`), hence strongly
  causal with open causally convex neighbourhoods (`fork_stronglyCausalOpen`); no time function
  (`fork_not_hasTimeFunction`: `T a < T w ≤ T b ≤ T a`); not tarentin (`causal_ladder`, Levin's edge
  read backwards); `J⁺(w)` and `≤_M` not closed (`fork_not_isClosed_Jplus`, `fork_not_isClosed_le`).
* **`T-abs-gh-without-tarentin/3-loop-fan`** — `loopFan` on `loopSet`: the origin `a` and tents
  `γ_n` from `p_n = (ε_n, 0)` through `(0, 1 + ε_n)` to `q_n = (−ε_n, 0)`, `p_n, q_n → a`;
  coherent (`loopγ_coherent`), globally hyperbolic, a time function (`−x`,
  `loopFan_hasTimeFunction`); not strongly causal at `a` (`loopFan_not_stronglyCausalAt`), in
  either form; not tarentin (`causal_ladder`, `prop:GH_fortement_causal`'s edge read backwards).
* **`T-abs-gh-without-tarentin/4-separation`** — `fork_separates`, `loopFan_separates` (the keeper's
  conjoined witnesses); `not_hasTimeFunction_of_globallyHyperbolic_bare`,
  `not_stronglyCausal_of_globallyHyperbolic_bare`, `not_isClosed_le_of_globallyHyperbolic_bare`
  (Levin's edge, `prop:GH_fortement_causal` and `prop:GH_Jferme` are sharp in tarentin).

> Global hyperbolicity without tarentin gives neither a time function nor strong causality: two
> absolutely minimal comb spacetimes in ℝ² (oriented segments, ≤_U along them inside U, ≪ empty) —
> the fork (a → w → x_n, b → y_n with x_n → b, y_n → a): causal, causally compact, strongly causal
> with open convex neighbourhoods, no time function; the loop fan (arcs γ_n from p_n to q_n through
> height 1, p_n, q_n → a): causal, causally compact, with a time function, not strongly causal at a
> (the target's title, `programme/roadmap.toml`)

> $M$ is globally hyperbolic if $M$ is causal and if $J_M(p,q)$ is compact for all $p,q\in M$.
> (`def:globally_hyperbolic`, `ETT.tex:995–996`) Let $M$ be a tarentin topological spacetime. If
> $M$ is globally hyperbolic, then $M$ is strongly causal. (`prop:GH_fortement_causal`,
> `ETT.tex:1199–1200`) If $M$ is tarentin and globally hyperbolic, then $\leq_M$ is closed in
> $M\times M$ and $J^\pm(K)$ is closed for every compact $K\subset M$. (`prop:GH_Jferme`,
> `ETT.tex:1178–1180`)

## Hypothesis checklist

| target claim | here |
|---|---|
| a causality of oriented arcs, `≤_U` along them inside `U`, `≪` empty | ✓ proved, every field; one step for coherent arcs |
| both absolutely minimal (causally arc-connected) | ✓ proved, on every open set for every cover too |
| both causal and causally compact (hence GH) | ✓ proved (`ArcCoherent`) |
| the fork strongly causal with open convex neighbourhoods | ✓ proved: every open box is causally convex |
| (beyond) the fork's `J⁺(w)` and `≤_M` not closed | ✓ proved: `prop:GH_Jferme` needs tarentin |
| the fork has no time function | ✓ proved |
| the loop fan has a time function | ✓ proved (`−x`, the planner's `s/n` replaced) |
| the loop fan is not strongly causal at `a` | ✓ proved (hence in neither form) |

## SCOPE (disclosed)

* **Coordinates changed, combinatorics kept.** The fork: `a = (0, 0)`, `w = (1/2, 1)`,
  `x_n = (1, 1 + ε_n)`, `b = (1, 1)`, `y_n = (0, −ε_n)`, `ε_n = 1/(n + 1)` (`n ≥ 0`), in place of
  the sketch's `x_n = (1, 1/n)`, `b = (1, 0)`: both coordinates are then monotone along every arc,
  so every open box is causally convex. The loop fan: tents (the graph of `1 + ε_n − (n + 2)|x|` over
  `[−ε_n, ε_n]`, from right to left) in place of the three-sided rectangles: `−x` is then a time
  function. Same incidences, limits and local pictures; homeomorphic, argued, not formalised.
* **Either reading of `defi:causalite`** (OQ-18): both are absolutely minimal on every open set
  for every cover of it (`fork_absolutelyMinimalOn`, `loopFan_absolutelyMinimalOn`).
* Both carriers are subspaces of `ℝ × ℝ`, Hausdorff and second countable (mathlib instances,
  conjoined in the witnesses). No metric notion appears in a statement (coordinates, open
  intervals, `|x|` in the tents' formula); balls and `dist` appear inside proofs only.
* Not proved here (not asked, no pair moved, simulated): the fork's curves extending, causal
  openness in the future, plainness; the loop fan's causal openness, the closedness of its `≤_M`.
* `prop:GH_fortement_causal` and `prop:GH_Jferme` are not marked: nothing of them is certified
  here; the bare theorems show that their tarentin hypothesis cannot be dropped (a finding for
  the ETT ledger's notes, the master's call).
* Names checked unique against `Causal/`, the scaffold, `lean-gx/` and `lean-benzecri/`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v

/-! ## A causality carried by a family of arcs -/

section Arcs

variable {M : Type u} [TopologicalSpace M] {ι : Type v}

/-- One step along the arcs `γ` in the open set `U`: `y` follows `x` along one arc `γ i`, both
parameters in `[0, 1]`, the piece of the arc between them inside `U`. -/
def arcStep (γ : ι → ℝ → M) (U : Opens M) (x y : M) : Prop :=
  ∃ i s t, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ γ i s = x ∧ γ i t = y ∧ ∀ r ∈ Icc s t, γ i r ∈ U

variable {γ : ι → ℝ → M} {U V : Opens M} {x y z : M}

theorem arcStep.mem_left (h : arcStep γ U x y) : x ∈ U := by
  obtain ⟨i, s, t, -, hst, -, rfl, -, hU⟩ := h
  exact hU s ⟨le_rfl, hst⟩

theorem arcStep.mem_right (h : arcStep γ U x y) : y ∈ U := by
  obtain ⟨i, s, t, -, hst, -, -, rfl, hU⟩ := h
  exact hU t ⟨hst, le_rfl⟩

theorem arcStep.mono (hUV : U ≤ V) (h : arcStep γ U x y) : arcStep γ V x y := by
  obtain ⟨i, s, t, h0, hst, h1, hx, hy, hU⟩ := h
  exact ⟨i, s, t, h0, hst, h1, hx, hy, fun r hr => hUV (hU r hr)⟩

variable (γ) in
/-- **The causality carried by the arcs `γ`**: `x ≤_U y` iff `x = y ∈ U` or a chain of steps
along the arcs inside `U` runs from `x` to `y`; `≪` empty. Reflexivity, transitivity and
monotonicity are free (`TransGen`); the reflexive clause serves the points on no arc. -/
def arcCausality : Causality M where
  le U x y := (x ∈ U ∧ x = y) ∨ TransGen (arcStep γ U) x y
  lt _ _ _ := False
  le_mem_left h := by
    rcases h with ⟨hx, -⟩ | h
    · exact hx
    · obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
      exact h.mem_left
  le_mem_right h := by
    rcases h with ⟨hx, rfl⟩ | h
    · exact hx
    · obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
      exact h.mem_right
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨hx, rfl⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨-, rfl⟩ | h₁
    · exact h₂
    · rcases h₂ with ⟨-, rfl⟩ | h₂
      · exact Or.inr h₁
      · exact Or.inr (h₁.trans h₂)
  lt_trans h _ := h
  le_mono h _ _ h' := by
    rcases h' with ⟨hx, rfl⟩ | h'
    · exact Or.inl ⟨h hx, rfl⟩
    · exact Or.inr (h'.mono fun _ _ hab => hab.mono h)
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem arcCausality_le :
    (arcCausality γ).le U x y ↔ (x ∈ U ∧ x = y) ∨ TransGen (arcStep γ U) x y := Iff.rfl

theorem arcCausality_not_lt : ¬ (arcCausality γ).lt U x y := id

theorem arcStep.le (h : arcStep γ U x y) : (arcCausality γ).le U x y :=
  Or.inr (TransGen.single h)

/-- Along an arc, the later point follows the earlier one in `M`. -/
theorem arcCausality_le_arc (i : ι) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (arcCausality γ).le ⊤ (γ i s) (γ i t) :=
  arcStep.le ⟨i, s, t, hs, hst, ht, rfl, rfl, fun _ _ => trivial⟩

/-- A step is realised by its arc, reparametrised over `[0, 1]`: a causal curve of `U`. -/
theorem arcStep.exists_causalCurveOn (hγ : ∀ i, Continuous (γ i)) (h : arcStep γ U x y) :
    ∃ c : ℝ → M, (arcCausality γ).CausalCurveOn U c 0 1 ∧ c 0 = x ∧ c 1 = y := by
  obtain ⟨i, s, t, h0, hst, h1, rfl, rfl, hU⟩ := h
  rcases hst.lt_or_eq with hlt | heq
  · have hc : (arcCausality γ).CausalCurveOn U (γ i) s t := by
      refine ⟨hU, fun r _ N _ hrN => ?_⟩
      obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1
        ((hγ i).continuousAt.preimage_mem_nhds (N.isOpen.mem_nhds hrN))
      refine ⟨l, u, hl, hu, fun σ hσ σ' hσ' h1' h2 h3 =>
        arcStep.le ⟨i, σ, σ', by linarith [hσ.1], h2.le, by linarith [hσ'.2], rfl, rfl,
          fun ρ hρ => hlu ⟨by linarith [hρ.1], by linarith [hρ.2]⟩⟩⟩
    have hc' : CurveOn (arcCausality γ).le U (γ i) ((t - s) * 0 + s) ((t - s) * 1 + s) := by
      rw [mul_zero, zero_add, mul_one, sub_add_cancel]; exact hc
    exact ⟨_, CurveOn.comp_affine (sub_pos.2 hlt) hc', by simp, by simp⟩
  · subst heq
    exact ⟨fun _ => γ i s, Causality.causalCurveOn_const (hU s ⟨le_rfl, le_rfl⟩), rfl, rfl⟩

/-- **The arc causality is causally arc-connected** (`def:causal_arc_connectedness`): a chain of
steps is realised by the concatenation of their arcs (`CurveOn.exists_concat`); `≪` is empty. -/
theorem arcCausality_causallyArcConnected (hγ : ∀ i, Continuous (γ i)) :
    (arcCausality γ).CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun h => False.elim h⟩
  rcases hpq with ⟨hp, rfl⟩ | hpq
  · exact ⟨fun _ => p, Causality.causalCurveOn_const hp, rfl, rfl⟩
  · induction hpq with
    | single h => exact h.exists_causalCurveOn hγ
    | tail _ h ih =>
      obtain ⟨c₁, hc₁, h0, h1⟩ := ih
      obtain ⟨c₂, hc₂, h2, h3⟩ := h.exists_causalCurveOn hγ
      obtain ⟨c, hc, hc0, hc1⟩ := CurveOn.exists_concat (arcCausality γ).isRelFamily_le hc₁
        hc₂ (h1.trans h2.symm)
      exact ⟨c, hc, hc0.trans h0, hc1.trans h3⟩

theorem arcCausality_causallyArcConnectedOn (hγ : ∀ i, Continuous (γ i)) (W : Opens M) :
    (arcCausality γ).CausallyArcConnectedOn W :=
  Causality.CausallyArcConnectedOn.mono (arcCausality_causallyArcConnected hγ) le_top

/-- **The arc causality is absolutely minimal** (`cor:causalement_connexe_minimal`). -/
theorem arcCausality_absolutelyMinimal (hγ : ∀ i, Continuous (γ i)) :
    (arcCausality γ).AbsolutelyMinimal :=
  (arcCausality_causallyArcConnected hγ).absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it (the gluing reading of
`defi:causalite`, OQ-18). -/
theorem arcCausality_absolutelyMinimalOn (hγ : ∀ i, Continuous (γ i)) (W : Opens M) :
    (arcCausality γ).AbsolutelyMinimalOn W :=
  (arcCausality_causallyArcConnectedOn hγ W).absolutelyMinimalOn

/-- Push-up holds vacuously: `≪` is empty. -/
theorem arcCausality_pushUp : (arcCausality γ).PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- No chronal neighbours: `≪` is empty. -/
theorem arcCausality_not_chronalNeighbours [Nonempty M] :
    ¬ (arcCausality γ).ChronalNeighbours := fun h =>
  let ⟨_, _, hp⟩ := h.1 ⊤ (Classical.arbitrary M) trivial
  hp

variable (γ) in
/-- **Coherent arcs**: two arcs through one point reach it at the same parameter and agree
before it. Then a chain of steps is one step (`ArcCoherent.le_iff`). -/
def ArcCoherent : Prop :=
  ∀ i j s s', s ∈ Icc (0 : ℝ) 1 → s' ∈ Icc (0 : ℝ) 1 → γ i s = γ j s' →
    s = s' ∧ ∀ r ∈ Icc 0 s, γ i r = γ j r

theorem ArcCoherent.arcStep_trans (hc : ArcCoherent γ) (h₁ : arcStep γ U x y)
    (h₂ : arcStep γ U y z) : arcStep γ U x z := by
  obtain ⟨i, s, t, hs, hst, ht, rfl, rfl, hU⟩ := h₁
  obtain ⟨j, s', t', hs', hst', ht', hy, rfl, hU'⟩ := h₂
  obtain ⟨heq, hagree⟩ := hc i j t s' ⟨hs.trans hst, ht⟩ ⟨hs', hst'.trans ht'⟩ hy.symm
  refine ⟨j, s, t', hs, by linarith, ht', (hagree s ⟨hs, hst⟩).symm, rfl, fun r hr => ?_⟩
  rcases le_total r t with hrt | hrt
  · rw [← hagree r ⟨hs.trans hr.1, hrt⟩]; exact hU r ⟨hr.1, hrt⟩
  · exact hU' r ⟨by linarith, hr.2⟩

theorem ArcCoherent.transGen_iff (hc : ArcCoherent γ) :
    TransGen (arcStep γ U) x y ↔ arcStep γ U x y := by
  refine ⟨fun h => ?_, TransGen.single⟩
  induction h with
  | single h => exact h
  | tail _ h ih => exact hc.arcStep_trans ih h

/-- **For coherent arcs `≤_U` is the planner's**: `x = y ∈ U`, or `y` follows `x` along one arc
whose piece between them lies in `U`. -/
theorem ArcCoherent.le_iff (hc : ArcCoherent γ) :
    (arcCausality γ).le U x y ↔ (x ∈ U ∧ x = y) ∨ arcStep γ U x y := by
  rw [arcCausality_le, hc.transGen_iff]

/-- `≤_M` for coherent arcs: equal, or along one arc in the order of the parameters. -/
theorem ArcCoherent.le_top_iff (hc : ArcCoherent γ) :
    (arcCausality γ).le ⊤ x y ↔
      x = y ∨ ∃ i s t, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ γ i s = x ∧ γ i t = y := by
  rw [hc.le_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨i, s, t, h0, hst, h1, hx, hy, -⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, s, t, h0, hst, h1, hx, hy⟩
  · rintro (h | ⟨i, s, t, h0, hst, h1, hx, hy⟩)
    · exact Or.inl ⟨trivial, h⟩
    · exact Or.inr ⟨i, s, t, h0, hst, h1, hx, hy, fun _ _ => trivial⟩

/-- **Coherent arcs give a causal spacetime** (`def:causal_spacetime`): `x ≤ y ≤ x` along arcs
reaches both points at the same parameters. -/
theorem ArcCoherent.isCausal (hc : ArcCoherent γ) : (arcCausality γ).IsCausal := by
  intro x y hxy hyx
  rcases hc.le_top_iff.1 hxy with h | ⟨i, s, t, hs, hst, ht, rfl, rfl⟩
  · exact h
  rcases hc.le_top_iff.1 hyx with h | ⟨j, s', t', hs', hst', ht', hy, hx⟩
  · exact h.symm
  have e1 := (hc i j t s' ⟨hs.trans hst, ht⟩ ⟨hs', hst'.trans ht'⟩ hy.symm).1
  have e2 := (hc i j s t' ⟨hs, hst.trans ht⟩ ⟨hs'.trans hst', ht'⟩ hx.symm).1
  have : s = t := by linarith
  rw [this]

theorem ArcCoherent.mem_diamond (hc : ArcCoherent γ) {p q : M}
    (hz : z ∈ (arcCausality γ).diamond ⊤ p q) :
    z = p ∨ ∃ i s r t, 0 ≤ s ∧ s ≤ r ∧ r ≤ t ∧ t ≤ 1 ∧ γ i s = p ∧ γ i r = z ∧ γ i t = q := by
  obtain ⟨hpz, hzq⟩ := Causality.mem_diamond.1 hz
  rcases hc.le_top_iff.1 hpz with h | ⟨i, s, r, hs, hsr, hr, rfl, rfl⟩
  · exact Or.inl h.symm
  rcases hc.le_top_iff.1 hzq with h | ⟨j, s', t, hs', hs't, ht, hz', rfl⟩
  · exact Or.inr ⟨i, s, r, r, hs, hsr, le_rfl, hr, rfl, rfl, h⟩
  · obtain ⟨e, hagree⟩ := hc i j r s' ⟨hs.trans hsr, hr⟩ ⟨hs', hs't.trans ht⟩ hz'.symm
    exact Or.inr ⟨j, s, r, t, hs, hsr, by linarith, ht, (hagree s ⟨hs, hsr⟩).symm,
      (hagree r ⟨hs.trans hsr, le_rfl⟩).symm, rfl⟩

/-- **The diamond between two points of an arc is the piece of the arc between them.** -/
theorem ArcCoherent.diamond_eq_image (hc : ArcCoherent γ) (i : ι) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ 1) :
    (arcCausality γ).diamond ⊤ (γ i s) (γ i t) = γ i '' Icc s t := by
  ext z
  constructor
  · intro hz
    rcases hc.mem_diamond hz with rfl | ⟨j, s₁, r, t₁, hs₁, hs₁r, hrt₁, ht₁, hp, rfl, hq⟩
    · exact ⟨s, ⟨le_rfl, hst⟩, rfl⟩
    · obtain ⟨e₁, -⟩ := hc i j s s₁ ⟨hs, hst.trans ht⟩ ⟨hs₁, hs₁r.trans (hrt₁.trans ht₁)⟩ hp.symm
      obtain ⟨e₂, hagree⟩ := hc i j t t₁ ⟨hs.trans hst, ht⟩ ⟨hs₁.trans (hs₁r.trans hrt₁), ht₁⟩
        hq.symm
      exact ⟨r, ⟨by linarith, by linarith⟩, hagree r ⟨hs₁.trans hs₁r, by linarith⟩⟩
  · rintro ⟨r, hr, rfl⟩
    exact Causality.mem_diamond.2 ⟨arcCausality_le_arc i hs hr.1 (hr.2.trans ht),
      arcCausality_le_arc i (hs.trans hr.1) hr.2 ht⟩

/-- **Coherent continuous arcs give a causally compact spacetime** (`def:causally_compact`): a
diamond is empty, a point, or a compact piece of an arc. -/
theorem ArcCoherent.causallyCompact (hc : ArcCoherent γ) (hγ : ∀ i, Continuous (γ i)) :
    (arcCausality γ).CausallyCompact := by
  intro p q
  by_cases hpq : (arcCausality γ).le ⊤ p q
  · rcases hc.le_top_iff.1 hpq with rfl | ⟨i, s, t, hs, hst, ht, rfl, rfl⟩
    · have hsub : (arcCausality γ).diamond ⊤ p p ⊆ {p} := fun z hz => by
        obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz
        exact hc.isCausal h2 h1
      exact ((Set.finite_singleton p).subset hsub).isCompact
    · rw [hc.diamond_eq_image i hs hst ht]
      exact isCompact_Icc.image (hγ i)
  · have : (arcCausality γ).diamond ⊤ p q = ∅ := by
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨h1, h2⟩ := Causality.mem_diamond.1 hz
      exact hpq ((arcCausality γ).le_trans h1 h2)
    rw [this]
    exact isCompact_empty

/-- **Coherent continuous arcs give a globally hyperbolic spacetime** (`def:globally_hyperbolic`). -/
theorem ArcCoherent.globallyHyperbolic (hc : ArcCoherent γ) (hγ : ∀ i, Continuous (γ i)) :
    (arcCausality γ).GloballyHyperbolic :=
  ⟨hc.isCausal, hc.causallyCompact hγ⟩

/-- A continuous function strictly increasing along each arc is a time function (the ladder's
`time_function`). -/
theorem ArcCoherent.hasTimeFunction (hc : ArcCoherent γ) {T : M → ℝ} (hT : Continuous T)
    (hmono : ∀ i, StrictMonoOn (fun r => T (γ i r)) (Icc 0 1)) :
    (arcCausality γ).HasTimeFunction := by
  refine ⟨T, hT, fun x y hxy hne => ?_⟩
  rcases hc.le_top_iff.1 hxy with h | ⟨i, s, t, hs, hst, ht, rfl, rfl⟩
  · exact absurd h hne
  rcases hst.lt_or_eq with hlt | heq
  · exact hmono i ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hlt
  · exact absurd (by rw [heq]) hne

/-- A set convex along each arc is causally convex in `M` (`defi:convexite_causale`). -/
theorem ArcCoherent.causallyConvexIn (hc : ArcCoherent γ) {V : Set M}
    (hV : ∀ i s r t, 0 ≤ s → s ≤ r → r ≤ t → t ≤ 1 → γ i s ∈ V → γ i t ∈ V → γ i r ∈ V) :
    (arcCausality γ).CausallyConvexIn V ⊤ := by
  refine ⟨fun _ _ => trivial, fun p hp q hq z hz => ?_⟩
  rcases hc.mem_diamond hz with rfl | ⟨i, s, r, t, hs, hsr, hrt, ht, rfl, rfl, rfl⟩
  · exact hp
  · exact hV i s r t hs hsr hrt ht hp hq

end Arcs

/-! ## Coordinates -/

/-- `ε_n = 1 / (n + 1)`, the spacing of the combs. -/
noncomputable def combEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem combEps_pos (n : ℕ) : 0 < combEps n := by unfold combEps; positivity

theorem combEps_le_one (n : ℕ) : combEps n ≤ 1 := by
  unfold combEps
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem combEps_strictAnti : StrictAnti combEps := fun n m h => by
  unfold combEps
  exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.add_lt_add_right h 1)

theorem tendsto_combEps : Tendsto combEps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

theorem combEps_mul (n : ℕ) : ((n : ℝ) + 2) * combEps n = 1 + combEps n := by
  unfold combEps
  field_simp
  ring

/-- The parameter clamped to `[0, 1]`. -/
noncomputable def clampUnit (t : ℝ) : ℝ := max 0 (min t 1)

theorem clampUnit_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampUnit t = t := by
  unfold clampUnit; rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_id.min continuous_const)

theorem monotone_clampUnit : Monotone clampUnit := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

/-- A function monotone or antitone sends a parameter between two parameters landing in an open
interval into that interval. -/
theorem mem_Ioo_of_monotone {g : ℝ → ℝ} (hg : Monotone g ∨ Antitone g) {a b s r t : ℝ}
    (hsr : s ≤ r) (hrt : r ≤ t) (hs : g s ∈ Ioo a b) (ht : g t ∈ Ioo a b) : g r ∈ Ioo a b := by
  rcases hg with hg | hg
  · exact ordConnected_Ioo.out hs ht ⟨hg hsr, hg hrt⟩
  · exact ordConnected_Ioo.out ht hs ⟨hg hrt, hg hsr⟩

/-! ## The fork -/

/-- The fork's arcs in `ℝ²`, the parameter clamped to `[0, 1]`: `inl n` runs
`a = (0, 0) → w = (1/2, 1)` (the common segment, `t ≤ 1/2`) `→ x_n = (1, 1 + ε_n)`; `inr n` runs
`b = (1, 1) → y_n = (0, −ε_n)`. Both coordinates increase along `inl n` and decrease along
`inr n`. -/
noncomputable def forkArc : ℕ ⊕ ℕ → ℝ → ℝ × ℝ
  | Sum.inl n, t => (clampUnit t, min (2 * clampUnit t) (1 + (2 * clampUnit t - 1) * combEps n))
  | Sum.inr n, t => (1 - clampUnit t, 1 - clampUnit t * (1 + combEps n))

/-- **The fork**, a subspace of `ℝ²`: `[a, w] ∪ ⋃ₙ [w, x_n] ∪ ⋃ₙ [b, y_n]`, the union of its
arcs. -/
def forkSet : Set (ℝ × ℝ) := ⋃ i, range (forkArc i)

/-- The fork's arcs, as maps into the fork. -/
noncomputable def forkγ (i : ℕ ⊕ ℕ) (t : ℝ) : forkSet :=
  ⟨forkArc i t, mem_iUnion.2 ⟨i, mem_range_self t⟩⟩

/-- **The fork's causality**: `≤_U` along the oriented arcs inside `U`, `≪` empty. -/
noncomputable def forkCausality : Causality forkSet := arcCausality forkγ

theorem forkArc_inl {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    forkArc (Sum.inl n) t = (t, min (2 * t) (1 + (2 * t - 1) * combEps n)) := by
  simp only [forkArc, clampUnit_of_mem ht]

theorem forkArc_inr {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    forkArc (Sum.inr n) t = (1 - t, 1 - t * (1 + combEps n)) := by
  simp only [forkArc, clampUnit_of_mem ht]

/-- On `[0, 1/2]` the arcs `inl n` climb the common segment `[a, w]`. -/
theorem forkMin_of_le (n : ℕ) {t : ℝ} (ht : t ≤ 1 / 2) :
    min (2 * t) (1 + (2 * t - 1) * combEps n) = 2 * t := by
  refine min_eq_left ?_
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * t)
    (by linarith [combEps_le_one n] : (0 : ℝ) ≤ 1 - combEps n)]

/-- On `[1/2, 1]` they leave `w` towards `x_n`. -/
theorem forkMin_of_ge (n : ℕ) {t : ℝ} (ht : 1 / 2 ≤ t) :
    min (2 * t) (1 + (2 * t - 1) * combEps n) = 1 + (2 * t - 1) * combEps n := by
  refine min_eq_right ?_
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t - 1)
    (by linarith [combEps_le_one n] : (0 : ℝ) ≤ 1 - combEps n)]

theorem continuous_forkArc (i : ℕ ⊕ ℕ) : Continuous (forkArc i) := by
  have hc := continuous_clampUnit
  cases i with
  | inl n =>
    exact hc.prodMk ((continuous_const.mul hc).min (continuous_const.add
      (((continuous_const.mul hc).sub continuous_const).mul continuous_const)))
  | inr n =>
    exact (continuous_const.sub hc).prodMk (continuous_const.sub (hc.mul continuous_const))

theorem continuous_forkγ (i : ℕ ⊕ ℕ) : Continuous (forkγ i) :=
  (continuous_forkArc i).subtype_mk _

/-- The arcs from `a` and the arcs from `b` are disjoint. -/
theorem forkArc_inl_ne_inr (n m : ℕ) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) : forkArc (Sum.inl n) s ≠ forkArc (Sum.inr m) s' := by
  rw [forkArc_inl hs, forkArc_inr hs']
  intro h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  simp only at h1 h2
  have hε := combEps_pos n
  have hε' := combEps_pos m
  have hε1 := combEps_le_one n
  have hε1' := combEps_le_one m
  rcases le_total s (1 / 2) with hle | hge
  · rw [forkMin_of_le n hle] at h2
    nlinarith [mul_nonneg hs.1 (by linarith : (0 : ℝ) ≤ 1 - combEps m)]
  · rw [forkMin_of_ge n hge] at h2
    nlinarith [mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
      (by linarith : (0 : ℝ) ≤ 1 - combEps n), mul_pos hε (by linarith : (0 : ℝ) < s),
      mul_nonneg hε'.le (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)]

/-- **The fork's arcs are coherent**: `inl n`, `inl m` meet on the common segment only (or are
equal), `inr n`, `inr m` at `b` only, `inl` and `inr` never. -/
theorem forkγ_coherent : ArcCoherent forkγ := by
  intro i j s s' hs hs' h
  have h' : forkArc i s = forkArc j s' := congrArg Subtype.val h
  cases i with
  | inl n =>
    cases j with
    | inl m =>
      rw [forkArc_inl hs, forkArc_inl hs'] at h'
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h'
      simp only at h1 h2
      subst h1
      refine ⟨rfl, fun r hr => Subtype.ext ?_⟩
      have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hs.2⟩
      show forkArc (Sum.inl n) r = forkArc (Sum.inl m) r
      rw [forkArc_inl hr1, forkArc_inl hr1]
      rcases le_total r (1 / 2) with hle | hge
      · rw [forkMin_of_le n hle, forkMin_of_le m hle]
      · have hs2 : 1 / 2 ≤ s := hge.trans hr.2
        rw [forkMin_of_ge n hs2, forkMin_of_ge m hs2] at h2
        rcases hs2.lt_or_eq with hlt | heq
        · have : combEps n = combEps m :=
            mul_left_cancel₀ (by linarith : (2 * s - 1) ≠ 0)
              (by linarith : (2 * s - 1) * combEps n = (2 * s - 1) * combEps m)
          rw [this]
        · have : r = 1 / 2 := le_antisymm (hr.2.trans heq.ge) hge
          rw [this, forkMin_of_le n le_rfl, forkMin_of_le m le_rfl]
    | inr m => exact absurd h' (forkArc_inl_ne_inr n m hs hs')
  | inr n =>
    cases j with
    | inl m => exact absurd h'.symm (forkArc_inl_ne_inr m n hs' hs)
    | inr m =>
      rw [forkArc_inr hs, forkArc_inr hs'] at h'
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h'
      simp only at h1 h2
      have e : s = s' := by linarith
      subst e
      refine ⟨rfl, fun r hr => Subtype.ext ?_⟩
      have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans hs.2⟩
      show forkArc (Sum.inr n) r = forkArc (Sum.inr m) r
      rw [forkArc_inr hr1, forkArc_inr hr1]
      rcases hs.1.lt_or_eq with hlt | heq
      · have : combEps n = combEps m := by
          have := mul_left_cancel₀ hlt.ne'
            (by linarith : s * (1 + combEps n) = s * (1 + combEps m))
          linarith
        rw [this]
      · have : r = 0 := le_antisymm (hr.2.trans heq.ge) hr.1
        rw [this]; simp

/-- `≤_U` of the fork, as the planner states it: `x = y ∈ U`, or `y` follows `x` along one
oriented arc whose piece between them lies in `U`. -/
theorem fork_le_iff {U : Opens forkSet} {x y : forkSet} :
    forkCausality.le U x y ↔ (x ∈ U ∧ x = y) ∨ arcStep forkγ U x y :=
  forkγ_coherent.le_iff

theorem fork_causallyArcConnected : forkCausality.CausallyArcConnected :=
  arcCausality_causallyArcConnected continuous_forkγ

/-- **The fork is absolutely minimal on every open set, for every cover of it** (the gluing
reading of `defi:causalite`). -/
theorem fork_absolutelyMinimalOn (W : Opens forkSet) : forkCausality.AbsolutelyMinimalOn W :=
  arcCausality_absolutelyMinimalOn continuous_forkγ W

/-- **The fork is globally hyperbolic**: causal and causally compact. -/
theorem fork_globallyHyperbolic : forkCausality.GloballyHyperbolic :=
  forkγ_coherent.globallyHyperbolic continuous_forkγ

/-- Along each arc of the fork both coordinates are monotone. -/
theorem forkArc_monotone (i : ℕ ⊕ ℕ) :
    (Monotone (fun t => (forkArc i t).1) ∨ Antitone (fun t => (forkArc i t).1)) ∧
      (Monotone (fun t => (forkArc i t).2) ∨ Antitone (fun t => (forkArc i t).2)) := by
  have hm := monotone_clampUnit
  cases i with
  | inl n =>
    refine ⟨Or.inl hm, Or.inl fun a b hab => ?_⟩
    have h := hm hab
    have hε := combEps_pos n
    exact min_le_min (by linarith) (by nlinarith)
  | inr n =>
    refine ⟨Or.inr fun a b hab => ?_, Or.inr fun a b hab => ?_⟩
    · have h := hm hab
      show 1 - clampUnit b ≤ 1 - clampUnit a
      linarith
    · have h := hm hab
      have hε := combEps_pos n
      show 1 - clampUnit b * (1 + combEps n) ≤ 1 - clampUnit a * (1 + combEps n)
      nlinarith

/-- An open box of the fork: the points with coordinates in `(a, b) × (c, d)`. -/
def forkBox (a b c d : ℝ) : Set forkSet := {z | z.val.1 ∈ Ioo a b ∧ z.val.2 ∈ Ioo c d}

theorem isOpen_forkBox (a b c d : ℝ) : IsOpen (forkBox a b c d) :=
  (isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))

/-- **Every open box of the fork is causally convex in the fork**: a diamond is the piece of one
arc between two points of the box, and both coordinates are monotone along the arcs. -/
theorem fork_causallyConvexIn_box (a b c d : ℝ) :
    forkCausality.CausallyConvexIn (forkBox a b c d) ⊤ :=
  forkγ_coherent.causallyConvexIn fun i _ _ _ _ hsr hrt _ hs ht =>
    ⟨mem_Ioo_of_monotone (forkArc_monotone i).1 hsr hrt hs.1 ht.1,
      mem_Ioo_of_monotone (forkArc_monotone i).2 hsr hrt hs.2 ht.2⟩

/-- **The fork is strongly causal with open causally convex neighbourhoods**
(`def:strongly_causal_spacetime`, `V` open): small open boxes. -/
theorem fork_stronglyCausalOpen : forkCausality.StronglyCausalOpen := by
  intro p U hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨⟨_, isOpen_forkBox (p.val.1 - δ) (p.val.1 + δ) (p.val.2 - δ) (p.val.2 + δ)⟩,
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, fun z hz => hball ?_,
    fork_causallyConvexIn_box _ _ _ _⟩
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  rw [Metric.mem_ball, Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
    abs_sub_lt_iff, abs_sub_lt_iff]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The point `a = (0, 0)` of the fork. -/
noncomputable def forkA : forkSet := forkγ (Sum.inl 0) 0

/-- The point `w = (1/2, 1)` of the fork. -/
noncomputable def forkW : forkSet := forkγ (Sum.inl 0) (1 / 2)

/-- The point `b = (1, 1)` of the fork. -/
noncomputable def forkB : forkSet := forkγ (Sum.inr 0) 0

theorem forkγ_inl_half (n : ℕ) : forkγ (Sum.inl n) (1 / 2) = forkW := by
  have h : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine Subtype.ext ?_
  show forkArc (Sum.inl n) (1 / 2) = forkArc (Sum.inl 0) (1 / 2)
  rw [forkArc_inl h, forkArc_inl h, forkMin_of_le n le_rfl, forkMin_of_le 0 le_rfl]

theorem forkγ_inl_zero (n : ℕ) : forkγ (Sum.inl n) 0 = forkA := by
  have h : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine Subtype.ext ?_
  show forkArc (Sum.inl n) 0 = forkArc (Sum.inl 0) 0
  rw [forkArc_inl h, forkArc_inl h, forkMin_of_le n (by norm_num), forkMin_of_le 0 (by norm_num)]

theorem forkγ_inr_zero (n : ℕ) : forkγ (Sum.inr n) 0 = forkB := by
  have h : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine Subtype.ext ?_
  show forkArc (Sum.inr n) 0 = forkArc (Sum.inr 0) 0
  rw [forkArc_inr h, forkArc_inr h]; simp

theorem forkA_val : forkA.val = (0, 0) := by
  show forkArc (Sum.inl 0) 0 = (0, 0)
  rw [forkArc_inl ⟨le_rfl, zero_le_one⟩, forkMin_of_le 0 (by norm_num)]; simp

theorem forkW_val : forkW.val = (1 / 2, 1) := by
  show forkArc (Sum.inl 0) (1 / 2) = (1 / 2, 1)
  rw [forkArc_inl ⟨by norm_num, by norm_num⟩, forkMin_of_le 0 le_rfl]; norm_num

theorem forkB_val : forkB.val = (1, 1) := by
  show forkArc (Sum.inr 0) 0 = (1, 1)
  rw [forkArc_inr ⟨le_rfl, zero_le_one⟩]; simp

/-- The end `x_n = (1, 1 + ε_n)` of the arc `inl n`. -/
theorem forkX_val (n : ℕ) : (forkγ (Sum.inl n) 1).val = (1, 1 + combEps n) := by
  show forkArc (Sum.inl n) 1 = _
  rw [forkArc_inl ⟨zero_le_one, le_rfl⟩, forkMin_of_ge n (by norm_num)]; norm_num

/-- The end `y_n = (0, −ε_n)` of the arc `inr n`. -/
theorem forkY_val (n : ℕ) : (forkγ (Sum.inr n) 1).val = (0, -combEps n) := by
  show forkArc (Sum.inr n) 1 = _
  rw [forkArc_inr ⟨zero_le_one, le_rfl⟩]; ring_nf

/-- `x_n → b` in the fork. -/
theorem tendsto_forkX : Tendsto (fun n => forkγ (Sum.inl n) 1) atTop (𝓝 forkB) := by
  rw [tendsto_subtype_rng, forkB_val]
  simp only [forkX_val]
  exact tendsto_const_nhds.prodMk_nhds (by simpa using tendsto_const_nhds.add tendsto_combEps)

/-- `y_n → a` in the fork. -/
theorem tendsto_forkY : Tendsto (fun n => forkγ (Sum.inr n) 1) atTop (𝓝 forkA) := by
  rw [tendsto_subtype_rng, forkA_val]
  simp only [forkY_val]
  exact tendsto_const_nhds.prodMk_nhds (by simpa using tendsto_combEps.neg)

/-- **The fork has no time function** (the ladder's `time_function`): a continuous `T` strictly
increasing along `≤` would give `T a < T w`, `T w < T x_n → T b` and `T b < T y_n → T a`, so
`T a < T w ≤ T b ≤ T a`. -/
theorem fork_not_hasTimeFunction : ¬ forkCausality.HasTimeFunction := by
  rintro ⟨T, hT, hlt⟩
  have hne : ∀ x y : forkSet, x.val.1 ≠ y.val.1 → x ≠ y := fun x y h e => h (by rw [e])
  have hAW : T forkA < T forkW := by
    refine hlt _ _ (arcCausality_le_arc (Sum.inl 0) le_rfl (by norm_num) (by norm_num))
      (hne _ _ ?_)
    rw [forkA_val, forkW_val]; norm_num
  have hWX : ∀ n, T forkW < T (forkγ (Sum.inl n) 1) := fun n => by
    rw [← forkγ_inl_half n]
    refine hlt _ _ (arcCausality_le_arc (Sum.inl n) (by norm_num) (by norm_num) le_rfl)
      (hne _ _ ?_)
    rw [forkγ_inl_half n, forkW_val, forkX_val]; norm_num
  have hBY : ∀ n, T forkB < T (forkγ (Sum.inr n) 1) := fun n => by
    rw [← forkγ_inr_zero n]
    refine hlt _ _ (arcCausality_le_arc (Sum.inr n) le_rfl zero_le_one le_rfl) (hne _ _ ?_)
    rw [forkγ_inr_zero n, forkB_val, forkY_val]; norm_num
  have h1 : T forkW ≤ T forkB :=
    ge_of_tendsto' ((hT.tendsto _).comp tendsto_forkX) fun n => (hWX n).le
  have h2 : T forkB ≤ T forkA :=
    ge_of_tendsto' ((hT.tendsto _).comp tendsto_forkY) fun n => (hBY n).le
  linarith

/-- `w ≰ b` in the fork: `b` lies on no arc from `a`, and `w` on no arc from `b`. -/
theorem fork_not_le_W_B : ¬ forkCausality.le ⊤ forkW forkB := by
  intro h
  rcases forkγ_coherent.le_top_iff.1 h with h | ⟨i, s, t, hs, hst, ht, hw, hb⟩
  · have := congrArg (fun z : forkSet => z.val.1) h
    simp only [forkW_val, forkB_val] at this
    norm_num at this
  · have hw' := congrArg Subtype.val hw
    have hb' := congrArg Subtype.val hb
    rw [forkW_val] at hw'
    rw [forkB_val] at hb'
    cases i with
    | inl n =>
      have h1 : forkArc (Sum.inl n) t = (1, 1) := hb'
      rw [forkArc_inl ⟨hs.trans hst, ht⟩] at h1
      obtain ⟨h1a, h1b⟩ := Prod.ext_iff.1 h1
      simp only at h1a h1b
      rw [h1a, forkMin_of_ge n (by norm_num)] at h1b
      have := combEps_pos n
      linarith
    | inr n =>
      have h1 : forkArc (Sum.inr n) s = (1 / 2, 1) := hw'
      rw [forkArc_inr ⟨hs, hst.trans ht⟩] at h1
      obtain ⟨h1a, h1b⟩ := Prod.ext_iff.1 h1
      simp only at h1a h1b
      have hs2 : s = 1 / 2 := by linarith
      rw [hs2] at h1b
      have := combEps_pos n
      linarith

/-- **The fork's `J⁺(w)` is not closed**: `x_n ∈ J⁺(w)` and `x_n → b ∉ J⁺(w)`. So
`GloballyHyperbolic.isClosed_Jplus_singleton` needs tarentin. -/
theorem fork_not_isClosed_Jplus : ¬ IsClosed (forkCausality.Jplus ⊤ {forkW}) := fun h =>
  fork_not_le_W_B (Precausality.mem_Jplus_singleton.1 (h.mem_of_tendsto tendsto_forkX
    (Eventually.of_forall fun n => Precausality.mem_Jplus_singleton.2 (by
      rw [← forkγ_inl_half n]
      exact arcCausality_le_arc (Sum.inl n) (by norm_num) (by norm_num) le_rfl))))

/-- **The fork's `≤_M` is not closed in `M × M`** (`prop:GH_Jferme` without tarentin): `w ≤ x_n`,
`x_n → b`, `w ≰ b`. -/
theorem fork_not_isClosed_le :
    ¬ IsClosed {z : forkSet × forkSet | forkCausality.le ⊤ z.1 z.2} := fun h => by
  have e : forkCausality.Jplus ⊤ {forkW} =
      (fun x : forkSet => (forkW, x)) ⁻¹' {z : forkSet × forkSet | forkCausality.le ⊤ z.1 z.2} := by
    ext x; simp [Precausality.mem_Jplus_singleton]
  exact fork_not_isClosed_Jplus (e ▸ h.preimage (continuous_const.prodMk continuous_id))

/-! ## The loop fan -/

/-- The loop fan's arcs, the parameter clamped to `[0, 1]`: the tent `γ_n`, the graph of
`1 + ε_n − (n + 2)|x|` over `[−ε_n, ε_n]` run from `p_n = (ε_n, 0)` through `(0, 1 + ε_n)` to
`q_n = (−ε_n, 0)`. The tents are nested and disjoint. -/
noncomputable def loopArc (n : ℕ) (t : ℝ) : ℝ × ℝ :=
  (combEps n * (1 - 2 * clampUnit t),
    1 + combEps n - ((n : ℝ) + 2) * |combEps n * (1 - 2 * clampUnit t)|)

/-- **The loop fan**, a subspace of `ℝ²`: `a = (0, 0)` and the tents. -/
def loopSet : Set (ℝ × ℝ) := insert (0, 0) (⋃ n, range (loopArc n))

/-- The loop fan's arcs, as maps into the loop fan. -/
noncomputable def loopγ (n : ℕ) (t : ℝ) : loopSet :=
  ⟨loopArc n t, mem_insert_of_mem _ (mem_iUnion.2 ⟨n, mem_range_self t⟩)⟩

/-- The point `a = (0, 0)` of the loop fan, on no arc. -/
def loopA : loopSet := ⟨(0, 0), mem_insert _ _⟩

/-- **The loop fan's causality**: `≤_U` along the oriented arcs inside `U`, `≪` empty. -/
noncomputable def loopFan : Causality loopSet := arcCausality loopγ

theorem loopArc_of_mem {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    loopArc n t = (combEps n * (1 - 2 * t),
      1 + combEps n - ((n : ℝ) + 2) * |combEps n * (1 - 2 * t)|) := by
  simp only [loopArc, clampUnit_of_mem ht]

theorem continuous_loopArc (n : ℕ) : Continuous (loopArc n) := by
  have hc := continuous_clampUnit
  have hx : Continuous fun t => combEps n * (1 - 2 * clampUnit t) :=
    continuous_const.mul (continuous_const.sub (continuous_const.mul hc))
  exact hx.prodMk (continuous_const.sub (continuous_const.mul hx.abs))

theorem continuous_loopγ (n : ℕ) : Continuous (loopγ n) :=
  (continuous_loopArc n).subtype_mk _

/-- **The loop fan's arcs are coherent**: the tents are disjoint and injectively parametrised. -/
theorem loopγ_coherent : ArcCoherent loopγ := by
  intro n m s s' hs hs' h
  have h' : loopArc n s = loopArc m s' := congrArg Subtype.val h
  rw [loopArc_of_mem hs, loopArc_of_mem hs'] at h'
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h'
  simp only at h1 h2
  rw [h1] at h2
  have hnm : n = m := by
    by_contra hne
    set X := |combEps m * (1 - 2 * s')|
    have hX : 0 ≤ X := abs_nonneg _
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := combEps_strictAnti hlt
      have hc : (n : ℝ) < m := by exact_mod_cast hlt
      nlinarith
    · have := combEps_strictAnti hlt
      have hc : (m : ℝ) < n := by exact_mod_cast hlt
      nlinarith
  subst hnm
  have e : s = s' := by
    have := mul_left_cancel₀ (combEps_pos n).ne' h1
    linarith
  subst e
  exact ⟨rfl, fun _ _ => rfl⟩

/-- `≤_U` of the loop fan, as the planner states it. -/
theorem loopFan_le_iff {U : Opens loopSet} {x y : loopSet} :
    loopFan.le U x y ↔ (x ∈ U ∧ x = y) ∨ arcStep loopγ U x y :=
  loopγ_coherent.le_iff

theorem loopFan_causallyArcConnected : loopFan.CausallyArcConnected :=
  arcCausality_causallyArcConnected continuous_loopγ

/-- **The loop fan is absolutely minimal on every open set, for every cover of it.** -/
theorem loopFan_absolutelyMinimalOn (W : Opens loopSet) : loopFan.AbsolutelyMinimalOn W :=
  arcCausality_absolutelyMinimalOn continuous_loopγ W

/-- **The loop fan is globally hyperbolic**: causal and causally compact. -/
theorem loopFan_globallyHyperbolic : loopFan.GloballyHyperbolic :=
  loopγ_coherent.globallyHyperbolic continuous_loopγ

theorem loopA_val : loopA.val = (0, 0) := rfl

/-- The start `p_n = (ε_n, 0)` of `γ_n`. -/
theorem loopP_val (n : ℕ) : (loopγ n 0).val = (combEps n, 0) := by
  show loopArc n 0 = _
  rw [loopArc_of_mem ⟨le_rfl, zero_le_one⟩]
  simp only [mul_zero, sub_zero, mul_one, abs_of_pos (combEps_pos n), combEps_mul]
  ring_nf

/-- The end `q_n = (−ε_n, 0)` of `γ_n`. -/
theorem loopQ_val (n : ℕ) : (loopγ n 1).val = (-combEps n, 0) := by
  show loopArc n 1 = _
  rw [loopArc_of_mem ⟨zero_le_one, le_rfl⟩]
  have : combEps n * (1 - 2 * 1) = -combEps n := by ring
  rw [this, abs_neg, abs_of_pos (combEps_pos n), combEps_mul]
  ring_nf

/-- The top `(0, 1 + ε_n)` of `γ_n`, above height `1`. -/
theorem loopPeak_val (n : ℕ) : (loopγ n (1 / 2)).val = (0, 1 + combEps n) := by
  show loopArc n (1 / 2) = _
  rw [loopArc_of_mem ⟨by norm_num, by norm_num⟩]
  norm_num

/-- `p_n → a` in the loop fan. -/
theorem tendsto_loopP : Tendsto (fun n => loopγ n 0) atTop (𝓝 loopA) := by
  rw [tendsto_subtype_rng, loopA_val]
  simp only [loopP_val]
  exact tendsto_combEps.prodMk_nhds tendsto_const_nhds

/-- `q_n → a` in the loop fan. -/
theorem tendsto_loopQ : Tendsto (fun n => loopγ n 1) atTop (𝓝 loopA) := by
  rw [tendsto_subtype_rng, loopA_val]
  simp only [loopQ_val]
  exact (by simpa using tendsto_combEps.neg :
    Tendsto (fun n => -combEps n) atTop (𝓝 0)).prodMk_nhds tendsto_const_nhds

/-- **The loop fan has a time function** (the ladder's `time_function`): `−x`, continuous and
strictly increasing along each tent. -/
theorem loopFan_hasTimeFunction : loopFan.HasTimeFunction := by
  refine loopγ_coherent.hasTimeFunction (T := fun z => -z.val.1)
    (continuous_fst.comp continuous_subtype_val).neg fun n s hs t ht hst => ?_
  show -(loopArc n s).1 < -(loopArc n t).1
  rw [loopArc_of_mem hs, loopArc_of_mem ht]
  have := combEps_pos n
  simp only
  nlinarith

/-- **The loop fan is not strongly causal at `a`**: below height `1` no neighbourhood of `a` is
causally convex, since it holds `p_n` and `q_n` for `n` large and `J_M(p_n, q_n) = γ_n` reaches
height `1 + ε_n`. -/
theorem loopFan_not_stronglyCausalAt : ∃ U ∈ 𝓝 loopA, ∀ V ∈ 𝓝 loopA, V ⊆ U →
    ¬ loopFan.CausallyConvexIn V ⊤ := by
  refine ⟨{z : loopSet | z.val.2 < 1},
    (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const).mem_nhds
      (by show loopA.val.2 < 1; rw [loopA_val]; norm_num), fun V hV hVU hconv => ?_⟩
  obtain ⟨n, hpn, hqn⟩ := ((tendsto_loopP.eventually hV).and (tendsto_loopQ.eventually hV)).exists
  have hpeak : loopγ n (1 / 2) ∈ loopFan.diamond ⊤ (loopγ n 0) (loopγ n 1) :=
    Causality.mem_diamond.2 ⟨arcCausality_le_arc n le_rfl (by norm_num) (by norm_num),
      arcCausality_le_arc n (by norm_num) (by norm_num) le_rfl⟩
  have h1 : (loopγ n (1 / 2)).val.2 < 1 := hVU (hconv.2 _ hpn _ hqn hpeak)
  rw [loopPeak_val] at h1
  have := combEps_pos n
  simp only at h1
  linarith

/-- **The loop fan is not strongly causal** (`def:strongly_causal_spacetime`). -/
theorem loopFan_not_stronglyCausal : ¬ loopFan.StronglyCausal := fun h => by
  obtain ⟨U, hU, hno⟩ := loopFan_not_stronglyCausalAt
  obtain ⟨V, hV, hVU, hconv⟩ := h loopA U hU
  exact hno V hV hVU hconv

/-! ## The separations -/

/-- **Global hyperbolicity and strong causality, without tarentin, do not give a time function**
(`globally_hyperbolic`, `is_causal`, `strongly_causal`, `strongly_causal_open ⇏ time_function`,
with every positive conjunct in the `from`). The fork, Hausdorff and second countable, is
absolutely minimal, causally arc-connected, push-up (hence locally), causal, causally compact,
globally hyperbolic, strongly causal in both forms; it has no time function, is not tarentin
(Levin's edge `globally_hyperbolic ∧ tarentin ⇒ time_function`, read backwards by
`causal_ladder`) and has no chronal neighbours. -/
theorem fork_separates :
    T2Space forkSet ∧ SecondCountableTopology forkSet ∧
      forkCausality.AbsolutelyMinimal ∧ forkCausality.CausallyArcConnected ∧
      forkCausality.PushUp ∧ forkCausality.LocallyPushUp ∧
      forkCausality.IsCausal ∧ forkCausality.CausallyCompact ∧
      forkCausality.GloballyHyperbolic ∧ forkCausality.StronglyCausalOpen ∧
      forkCausality.StronglyCausal ∧
      ¬ forkCausality.HasTimeFunction ∧ ¬ forkCausality.Tarentin ∧
      ¬ forkCausality.ChronalNeighbours := by
  have hAC : forkCausality.CausallyArcConnected := fork_causallyArcConnected
  have hAM : forkCausality.AbsolutelyMinimal := hAC.absolutelyMinimal
  have hPU : forkCausality.PushUp := arcCausality_pushUp
  have hGH : forkCausality.GloballyHyperbolic := fork_globallyHyperbolic
  have hSCO : forkCausality.StronglyCausalOpen := fork_stronglyCausalOpen
  have hNT : ¬ forkCausality.HasTimeFunction := fork_not_hasTimeFunction
  haveI : Nonempty forkSet := ⟨forkA⟩
  -- the ladder steps (`causal_ladder`): push_up ⇒ locally_push_up, globally_hyperbolic ⇒
  -- is_causal, causally_compact, strongly_causal_open ⇒ strongly_causal; and, read backwards,
  -- globally_hyperbolic ∧ tarentin ⇒ time_function (T2, second countable)
  exact ⟨inferInstance, inferInstance, hAM, hAC, hPU, by causal_ladder, by causal_ladder,
    by causal_ladder, hGH, hSCO, by causal_ladder, hNT, fun _ => hNT (by causal_ladder),
    arcCausality_not_chronalNeighbours⟩

/-- **Global hyperbolicity and a time function, without tarentin, do not give strong causality**
(`globally_hyperbolic`, `time_function`, `is_causal ⇏ strongly_causal`, `strongly_causal_open`,
with every positive conjunct in the `from`). The loop fan, Hausdorff and second countable, is
absolutely minimal, causally arc-connected, push-up (hence locally), causal, causally compact,
globally hyperbolic, with a time function (hence curves extend); it is strongly causal in neither
form, not tarentin (`prop:GH_fortement_causal`'s edge `globally_hyperbolic ∧ tarentin ⇒
strongly_causal`, read backwards by `causal_ladder`) and has no chronal neighbours. -/
theorem loopFan_separates :
    T2Space loopSet ∧ SecondCountableTopology loopSet ∧
      loopFan.AbsolutelyMinimal ∧ loopFan.CausallyArcConnected ∧
      loopFan.PushUp ∧ loopFan.LocallyPushUp ∧
      loopFan.IsCausal ∧ loopFan.CausallyCompact ∧ loopFan.GloballyHyperbolic ∧
      loopFan.HasTimeFunction ∧ loopFan.CurvesExtend ∧
      ¬ loopFan.StronglyCausal ∧ ¬ loopFan.StronglyCausalOpen ∧ ¬ loopFan.Tarentin ∧
      ¬ loopFan.ChronalNeighbours := by
  have hAC : loopFan.CausallyArcConnected := loopFan_causallyArcConnected
  have hAM : loopFan.AbsolutelyMinimal := hAC.absolutelyMinimal
  have hPU : loopFan.PushUp := arcCausality_pushUp
  have hGH : loopFan.GloballyHyperbolic := loopFan_globallyHyperbolic
  have hTF : loopFan.HasTimeFunction := loopFan_hasTimeFunction
  have hNSC : ¬ loopFan.StronglyCausal := loopFan_not_stronglyCausal
  haveI : Nonempty loopSet := ⟨loopA⟩
  -- the ladder steps (`causal_ladder`): push_up ⇒ locally_push_up, globally_hyperbolic ⇒
  -- is_causal, causally_compact, time_function ⇒ curves_extend; and, read backwards,
  -- strongly_causal_open ⇒ strongly_causal and globally_hyperbolic ∧ tarentin ⇒ strongly_causal
  -- (T2)
  exact ⟨inferInstance, inferInstance, hAM, hAC, hPU, by causal_ladder, by causal_ladder,
    by causal_ladder, hGH, hTF, by causal_ladder, hNSC, fun _ => hNSC (by causal_ladder),
    fun _ => hNSC (by causal_ladder), arcCausality_not_chronalNeighbours⟩

/-- **Levin's edge is sharp in tarentin**: on a Hausdorff, second countable space, a globally
hyperbolic, strongly causal (open form), causally arc-connected causality need not have a time
function (the fork). -/
theorem not_hasTimeFunction_of_globallyHyperbolic_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), C.GloballyHyperbolic → C.StronglyCausalOpen → C.CausallyArcConnected →
        C.HasTimeFunction := fun h =>
  fork_not_hasTimeFunction
    (h forkSet forkCausality fork_globallyHyperbolic fork_stronglyCausalOpen
      fork_causallyArcConnected)

/-- **`prop:GH_fortement_causal` is sharp in tarentin**: on a Hausdorff, second countable space, a
globally hyperbolic, causally arc-connected causality with a time function need not be strongly
causal (the loop fan). -/
theorem not_stronglyCausal_of_globallyHyperbolic_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), C.GloballyHyperbolic → C.HasTimeFunction → C.CausallyArcConnected →
        C.StronglyCausal := fun h =>
  loopFan_not_stronglyCausal
    (h loopSet loopFan loopFan_globallyHyperbolic loopFan_hasTimeFunction
      loopFan_causallyArcConnected)

/-- **`prop:GH_Jferme` is sharp in tarentin**: on a Hausdorff, second countable space, a globally
hyperbolic, strongly causal (open form), causally arc-connected causality need not have `≤_M`
closed (the fork). -/
theorem not_isClosed_le_of_globallyHyperbolic_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), C.GloballyHyperbolic → C.StronglyCausalOpen → C.CausallyArcConnected →
        IsClosed {z : M × M | C.le ⊤ z.1 z.2} := fun h =>
  fork_not_isClosed_le
    (h forkSet forkCausality fork_globallyHyperbolic fork_stronglyCausalOpen
      fork_causallyArcConnected)

end Causal
