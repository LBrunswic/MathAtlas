import Causal.LadderLocal
import Causal.CurvesExtend

/-!
# Local push-up gives push-up under absolute minimality on a T1 space; T1 and local push-up cannot be dropped

Programme target `T-abs-pushup-of-minimal-local` (`programme/roadmap.toml:749`; layer 1, no label
of `ETT.tex`; ETT-layer imports only, no model, no metric notion).

**`T-abs-pushup-of-minimal-local/1-edge`** — `Causality.AbsolutelyMinimal.pushUp_of_locallyPushUp`
(the edge `absolutely_minimal ∧ locally_push_up ⇒ push_up`, standing `T1`); its form on an open
subset, `Causality.AbsolutelyMinimalOn.pushUpOn_of_locallyPushUpOn`; the clause
`x ≪ y ≤ z ⇒ x ≪ z`, `Causality.AbsolutelyMinimalOn.lt_of_lt_of_le_of_locallyPushUpOn`; the last
step of a localised chronological chain, `Precausality.AbsolutelyMinimalOn.exists_lt_inf_last`.
**`T-abs-pushup-of-minimal-local/2-local-global`** — under absolute minimality local and global
coincide: `AbsolutelyMinimal.pushUp_iff_locallyPushUp` (`T1`),
`AbsolutelyMinimal.causallyOpenFuture_iff_locallyCausallyOpenFuture`,
`AbsolutelyMinimal.causallyOpen_iff_locallyCausallyOpen` (no separation axiom).
**`T-abs-pushup-of-minimal-local/3-t1-necessary`** — the vee (`Vee`, `veeCausality`), three
points, `T0` and not `T1`, absolutely minimal, locally push-up, not push-up:
`veeCausality_separates_pushUp`, `not_pushUp_of_absolutelyMinimal_of_locallyPushUp_T0`.
**`T-abs-pushup-of-minimal-local/4-local-push-up-necessary`** — the half-chronological line
`halfChronoLine` (`Causal/LinesReachable.lean:236`) is causally arc-connected, absolutely minimal,
globally hyperbolic, causal, strongly causal (both forms), causally open, tarentin, has a time
function and extending causal curves, and is neither locally push-up nor push-up:
`halfChronoLine_separates_pushUp`; also `halfChronoLine_causallyArcConnected`,
`halfChronoLine_not_pushUpOn` (push-up fails on every open containing `-1`).

> Local push-up gives push-up under absolute minimality on a T1 space (the auditor's claim at
> T-abs-gateline-local): AbsolutelyMinimal.pushUp_of_locallyPushUp, a new edge absolutely_minimal ∧
> locally_push_up ⇒ push_up (standing T1) that weakens lem:pushup_local's causal arc-connectedness
> to absolute minimality — proved, or refuted by a T1, absolutely minimal, locally push-up causality
> without push-up (`programme/roadmap.toml:750`)

> Let $M$ be a causally arc-connected topological spacetime and let $(\U_i)_{i\in I}$ be a cover
> of $M$ by open subsets each having the push-up property. Then $M$ has the push-up property.
> (`lem:pushup_local`, `ETT.tex:557–560`)

> Let $M$ be a topological spacetime. If $M$ is absolutely minimal and if for every $p\in M$ there
> exists a neighbourhood $\U$ of $p$ whose causality is open, then the causality of $M$ is open.
> (`prop:topological_spacetime_absolutely_minimal`, `ETT.tex:698–701`)

## Hypothesis checklist

| hypothesis | here |
|---|---|
| target: absolutely minimal | ✓ carried (`AbsolutelyMinimal`; on `W`, `AbsolutelyMinimalOn W`) |
| target: locally push-up | ✓ carried (`LocallyPushUp`; on `W`, every point of `W` has an open neighbourhood with push-up) |
| target: `T1` | ✓ carried (`[T1Space M]`); necessary, `T0` does not suffice (the vee) |
| target: push-up, both clauses | ✓ proved, `x ≪_U y ≤_U z` and `x ≤_U y ≪_U z`, in every open `U` |
| `lem:pushup_local`: causally arc-connected | ⚠ weakened to absolutely minimal, at the price of `T1` (ETT's spacetimes are Hausdorff, `ETT.tex:255`) |
| `lem:pushup_local`: a cover by push-up opens | ✓ carried (`LocallyPushUp`); necessary even under causal arc-connectedness (the half-chronological line) |

## SCOPE (disclosed)

* **Proved, as the planner sketched it.** `y ≤_U z` is expanded over the cover of `W` by the opens
  with push-up: `y = b₀ ≤ b₁ ≤ ⋯ ≤ bₙ = z`, each step in `U ⊓ O_i`. Given `x ≪_U b_{i-1}`, the chain
  of `x ≪_U b_{i-1}` over the two-set cover `{O_i, M ∖ {b_{i-1}}}` (open by `T1`) ends with a step
  `r ≪_{U ⊓ O_i} b_{i-1}`, the end point lying in no other member; push-up in `O_i` gives
  `r ≪_{U ⊓ O_i} b_i`, hence `x ≪_U b_i`. The other clause is the first for `C.dual`. `T1` is used
  once, for `{b}ᶜ` open.
* **Why the siblings need no `T1` and this edge does.** `J⁺_U(V)` is reached by `≤`-chains alone,
  so local causal openness propagates along the expansion of `≤` over any cover
  (`AbsolutelyMinimal.causallyOpenFuture`). Push-up mixes `≪` and `≤`: the step needs the last
  `≪`-step into `b` to lie in `b`'s push-up neighbourhood, which absolute minimality grants only
  against a cover in which that neighbourhood is the one member containing `b`. In the vee every
  non-empty open contains `mid`, and `left ≪ mid ≤ right` while nothing is `≪ right`.
* **The three hypotheses are sharp.** `T1`: the vee (not a topological spacetime of ETT, which
  are Hausdorff: sharpness of the standing only). Local push-up: the half-chronological line, an
  ETT spacetime in either reading of `defi:causalite` (causally arc-connected, hence absolutely
  minimal); it is the first witness of the ladder lacking local push-up (whose `[[open]]` notes
  read "no Lean model lacks local push-up"), and it also shows that `lem:pushup_local`'s cover
  cannot be dropped. Absolute minimality: the gated line
  (`gateLine_separates_pushUp`, `Causal/GateLineLocal.lean`), in the reading without gluing only.
* **What follows for the gluing reading** (OQ-18, OQ-67 (b); not a ruling): if every causality is
  absolutely minimal, local and global push-up coincide on `T1` spaces, and local and global causal
  openness (both forms) coincide outright, so the gated and jump lines separate them only without
  gluing (kb/0073). The half-chronological line's separations hold in either reading.
* **Properties of the half-chronological line reading `≤` only** are the timelike line's by
  definitional equality (kb/0052), except those passing through the structure `CausalCurveIn`,
  which is indexed by the causality: `halfChronoLine_inextensible_id` re-proves the timelike
  line's one-line argument. It is not causally plain (`halfChronoLine_not_causallyPlain`), as it
  must not be (`pushUp_of_causallyPlain_of_absolutelyMinimal`), and has no chronal neighbours
  (`halfChronoLine_not_chronalNeighbours`: nothing is `≪ -1`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Precausality

variable {Q : Precausality M} {W V : Opens M} {x : M}

/-- The **last step** of a chronological chain, localised in a chosen open set: under absolute
minimality on a `T1` space, if `x ≪_V p` and `p ∈ O`, the chain from `x` to `p` over the cover
`{O, M ∖ {p}}` ends with a step `r ≪_{V ⊓ O} p`. The time reversal of
`AbsolutelyMinimalOn.exists_lt_inf`. -/
theorem AbsolutelyMinimalOn.exists_lt_inf_last [T1Space M] (h : Q.AbsolutelyMinimalOn W)
    (hV : V ≤ W) (O : Opens M) {p : M} (hpO : p ∈ O) (hxp : Q.lt V x p) :
    ∃ r, Q.lt (V ⊓ O) r p ∧ (r = x ∨ Q.lt V x r) :=
  (dual_absolutelyMinimalOn.2 h).exists_lt_inf hV O hpO (show Q.dual.lt V p x from hxp)

end Precausality

namespace Causality

variable {C : Causality M} {W : Opens M}

/-- **One clause of push-up from local push-up**, under absolute minimality of `W` on a `T1`
space: `x ≪_U y ≤_U z` gives `x ≪_U z` for every open `U ⊆ W`. -/
theorem AbsolutelyMinimalOn.lt_of_lt_of_le_of_locallyPushUpOn [T1Space M]
    (h : C.AbsolutelyMinimalOn W) (hloc : ∀ x ∈ W, ∃ W' : Opens M, x ∈ W' ∧ C.PushUpOn W')
    {U : Opens M} (hU : U ≤ W) {x y z : M} (hxy : C.lt U x y) (hyz : C.le U y z) :
    C.lt U x z := by
  -- the cover of `W` by the opens with push-up
  have hS : ∀ b ∈ W, ∃ O ∈ {O : Opens M | C.PushUpOn O}, b ∈ O := fun b hb => by
    obtain ⟨W', hbW', hW'⟩ := hloc b hb
    exact ⟨W', hW', hbW'⟩
  -- one step: `x ≪_U b` and `b ≤_{U ⊓ O} c` with `O` push-up give `x ≪_U c`
  have step : ∀ {b c : M}, C.lt U x b →
      (∃ O ∈ {O : Opens M | C.PushUpOn O}, C.le (U ⊓ O) b c) → C.lt U x c := by
    rintro b c hxb ⟨O, hO, hbc⟩
    have hbO : b ∈ O := (inf_le_right : U ⊓ O ≤ O) (C.le_mem_left hbc)
    -- the last step of `x ≪_U b` over the cover `{O, M ∖ {b}}` lies in `O`
    obtain ⟨r, hrb, hr⟩ :=
      Precausality.AbsolutelyMinimalOn.exists_lt_inf_last h hU O hbO hxb
    have hrc : C.lt U r c := C.lt_mono inf_le_left ((hO (U ⊓ O) inf_le_right).1 hrb hbc)
    rcases hr with rfl | hxr
    · exact hrc
    · exact C.lt_trans hxr hrc
  -- expand `y ≤_U z` over the cover and push `x ≪` along the chain
  have hchain := (h _ hS U hU y z).1 hyz
  clear hyz
  induction hchain with
  | single hl => exact step hxy hl
  | tail _ hl ih => exact step ih hl

/-- **Local push-up gives push-up on an absolutely minimal open subset** of a `T1` space. -/
theorem AbsolutelyMinimalOn.pushUpOn_of_locallyPushUpOn [T1Space M]
    (h : C.AbsolutelyMinimalOn W) (hloc : ∀ x ∈ W, ∃ W' : Opens M, x ∈ W' ∧ C.PushUpOn W') :
    C.PushUpOn W := by
  intro U hU x y z
  refine ⟨fun hxy hyz => lt_of_lt_of_le_of_locallyPushUpOn h hloc hU hxy hyz,
    fun hxy hyz => ?_⟩
  -- the other clause is the first one for the time-reversed causality
  have hd : C.dual.AbsolutelyMinimalOn W := Precausality.dual_absolutelyMinimalOn.2 h
  have hlocd : ∀ x ∈ W, ∃ W' : Opens M, x ∈ W' ∧ C.dual.PushUpOn W' := fun x hx => by
    obtain ⟨W', hxW', hW'⟩ := hloc x hx
    exact ⟨W', hxW', dual_pushUpOn.2 hW'⟩
  exact lt_of_lt_of_le_of_locallyPushUpOn (C := C.dual) hd hlocd hU
    (show C.dual.lt U z y from hyz) (show C.dual.le U y x from hxy)

/-- **`absolutely_minimal ∧ locally_push_up ⇒ push_up`** (standing `T1`): on a `T1` space an
absolutely minimal causality with local push-up has push-up. It weakens the causal
arc-connectedness of `lem:pushup_local` (`CausallyArcConnected.pushUp_of_locallyPushUp`) to
absolute minimality, at the price of `T1`. -/
theorem AbsolutelyMinimal.pushUp_of_locallyPushUp [T1Space M] (h : C.AbsolutelyMinimal)
    (hloc : C.LocallyPushUp) : C.PushUp :=
  pushUpOn_top.1 (AbsolutelyMinimalOn.pushUpOn_of_locallyPushUpOn
    (Precausality.absolutelyMinimal_iff.1 h) fun x _ => hloc x)

/-! ## Under absolute minimality, local and global coincide -/

/-- On a `T1` space, an absolutely minimal causality has push-up iff it has local push-up. -/
theorem AbsolutelyMinimal.pushUp_iff_locallyPushUp [T1Space M] (h : C.AbsolutelyMinimal) :
    C.PushUp ↔ C.LocallyPushUp :=
  ⟨PushUp.locallyPushUp, AbsolutelyMinimal.pushUp_of_locallyPushUp h⟩

/-- An absolutely minimal causality is causally open in the future iff it is so locally (no
separation axiom). -/
theorem AbsolutelyMinimal.causallyOpenFuture_iff_locallyCausallyOpenFuture
    (h : C.AbsolutelyMinimal) : C.CausallyOpenFuture ↔ C.LocallyCausallyOpenFuture :=
  ⟨CausallyOpenFuture.locallyCausallyOpenFuture,
    AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture h⟩

/-- An absolutely minimal causality is causally open (two-sided, DEC-8) iff it is so locally (no
separation axiom). -/
theorem AbsolutelyMinimal.causallyOpen_iff_locallyCausallyOpen (h : C.AbsolutelyMinimal) :
    C.CausallyOpen ↔ C.LocallyCausallyOpen :=
  ⟨CausallyOpen.locallyCausallyOpen, AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen h⟩

end Causality

/-! ## `T1` cannot be dropped: the vee

Three points `left`, `mid`, `right`; a set is open iff it contains `mid` as soon as it contains
`left` or `right` (the opens are `∅`, `{mid}`, `{left, mid}`, `{mid, right}` and the whole space),
a `T0` space that is not `T1` (`{mid}` is not closed). `x ≤_U y` iff `x, y ∈ U` and
`x ≤ y` in the order `left < mid < right`; `x ≪_U y` iff `left ∈ U`, `x ≠ right` and `y = mid`. -/

/-- The three points of the vee. -/
inductive Vee
  | left
  | mid
  | right
  deriving DecidableEq

namespace Vee

/-- The rank of a point in the order `left < mid < right`. -/
def rank : Vee → ℕ
  | left => 0
  | mid => 1
  | right => 2

/-- The topology of the vee: an open set containing `left` or `right` contains `mid`. -/
instance : TopologicalSpace Vee where
  IsOpen s := (left ∈ s → mid ∈ s) ∧ (right ∈ s → mid ∈ s)
  isOpen_univ := ⟨fun _ => trivial, fun _ => trivial⟩
  isOpen_inter s t hs ht := ⟨fun h => ⟨hs.1 h.1, ht.1 h.2⟩, fun h => ⟨hs.2 h.1, ht.2 h.2⟩⟩
  isOpen_sUnion S hS := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨s, hs, hx⟩ := Set.mem_sUnion.1 h
      exact Set.mem_sUnion.2 ⟨s, hs, (hS s hs).1 hx⟩
    · obtain ⟨s, hs, hx⟩ := Set.mem_sUnion.1 h
      exact Set.mem_sUnion.2 ⟨s, hs, (hS s hs).2 hx⟩

theorem isOpen_iff {s : Set Vee} :
    IsOpen s ↔ (left ∈ s → mid ∈ s) ∧ (right ∈ s → mid ∈ s) := Iff.rfl

theorem mid_mem_of_left_mem (U : Opens Vee) (h : left ∈ U) : mid ∈ U :=
  (isOpen_iff.1 U.isOpen).1 h

theorem mid_mem_of_right_mem (U : Opens Vee) (h : right ∈ U) : mid ∈ U :=
  (isOpen_iff.1 U.isOpen).2 h

/-- The open set `{left, mid}`. -/
def lower : Opens Vee := ⟨{right}ᶜ, isOpen_iff.2 ⟨fun _ => by simp, fun h => absurd rfl h⟩⟩

/-- The open set `{mid, right}`. -/
def upper : Opens Vee := ⟨{left}ᶜ, isOpen_iff.2 ⟨fun h => absurd rfl h, fun _ => by simp⟩⟩

/-- The vee is not `T1`: `{mid}` is not closed. -/
theorem not_t1Space : ¬ T1Space Vee := by
  intro h
  have ho : IsOpen ({mid}ᶜ : Set Vee) := isOpen_compl_iff.2 isClosed_singleton
  have := (isOpen_iff.1 ho).1 (by simp)
  simp at this

/-- The vee is `T0`. -/
theorem t0Space : T0Space Vee := by
  rw [t0Space_iff_inseparable]
  intro x y hxy
  rw [inseparable_iff_forall_isOpen] at hxy
  have hm : IsOpen ({mid} : Set Vee) :=
    isOpen_iff.2 ⟨fun h => by simp at h, fun h => by simp at h⟩
  have hl := hxy _ lower.isOpen
  have hmid := hxy _ hm
  cases x <;> cases y <;> first | rfl | simp [lower] at hl hmid

end Vee

/-- **The vee's causality.** -/
def veeCausality : Causality Vee where
  le U x y := x ∈ U ∧ y ∈ U ∧ x.rank ≤ y.rank
  lt U x y := Vee.left ∈ U ∧ x ≠ Vee.right ∧ y = Vee.mid
  le_mem_left h := h.1
  le_mem_right h := h.2.1
  lt_mem_left := by
    rintro U x y ⟨hl, hx, -⟩
    cases x
    · exact hl
    · exact Vee.mid_mem_of_left_mem U hl
    · exact absurd rfl hx
  lt_mem_right := by
    rintro U x y ⟨hl, -, rfl⟩
    exact Vee.mid_mem_of_left_mem U hl
  le_refl hx := ⟨hx, hx, le_rfl⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₁.2.1, h₂.2.2⟩
  le_mono h _ _ h' := ⟨h h'.1, h h'.2.1, h'.2.2⟩
  lt_mono h _ _ h' := ⟨h h'.1, h'.2⟩
  le_of_lt := by
    rintro U x y ⟨hl, hx, rfl⟩
    refine ⟨?_, Vee.mid_mem_of_left_mem U hl, ?_⟩
    · cases x
      · exact hl
      · exact Vee.mid_mem_of_left_mem U hl
      · exact absurd rfl hx
    · cases x
      · decide
      · decide
      · exact absurd rfl hx
  isOpen_lt_right U x := by
    rw [Vee.isOpen_iff]
    exact ⟨fun h => absurd h.2.2 (by decide), fun h => absurd h.2.2 (by decide)⟩
  isOpen_lt_left U y := by
    rw [Vee.isOpen_iff]
    exact ⟨fun h => ⟨h.1, by decide, h.2.2⟩, fun h => absurd rfl h.2.1⟩

theorem veeCausality_le {U : Opens Vee} {x y : Vee} :
    veeCausality.le U x y ↔ x ∈ U ∧ y ∈ U ∧ x.rank ≤ y.rank := Iff.rfl

theorem veeCausality_lt {U : Opens Vee} {x y : Vee} :
    veeCausality.lt U x y ↔ Vee.left ∈ U ∧ x ≠ Vee.right ∧ y = Vee.mid := Iff.rfl

/-- The vee is absolutely minimal: a cover contains an open containing `left`, hence `{left, mid}`,
and one containing `right`, hence `{mid, right}`. -/
theorem veeCausality_absolutelyMinimal : veeCausality.AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff]
  intro S hS V _ x y
  obtain ⟨Ol, hOl, hl⟩ := hS Vee.left trivial
  obtain ⟨Or, hOr, hr⟩ := hS Vee.right trivial
  obtain ⟨Om, hOm, hm⟩ := hS Vee.mid trivial
  have hml : Vee.mid ∈ Ol := Vee.mid_mem_of_left_mem Ol hl
  have hmr : Vee.mid ∈ Or := Vee.mid_mem_of_right_mem Or hr
  have step : ∀ {O : Opens Vee}, O ∈ S → ∀ {a b : Vee}, a ∈ V → b ∈ V → a ∈ O → b ∈ O →
      a.rank ≤ b.rank →
      TransGen (fun a b => ∃ O ∈ S, veeCausality.le (V ⊓ O) a b) a b :=
    fun hO _ _ ha hb haO hbO hab => TransGen.single ⟨_, hO, ⟨ha, haO⟩, ⟨hb, hbO⟩, hab⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, hy, hxy⟩
    cases x <;> cases y
    · exact step hOl hx hy hl hl le_rfl
    · exact step hOl hx hy hl hml (by decide)
    · have hmV : Vee.mid ∈ V := Vee.mid_mem_of_left_mem V hx
      exact (step hOl hx hmV hl hml (by decide)).trans (step hOr hmV hy hmr hr (by decide))
    · exact absurd hxy (by decide)
    · exact step hOm hx hy hm hm le_rfl
    · exact step hOr hx hy hmr hr (by decide)
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · exact step hOr hx hy hr hr le_rfl
  · rintro ⟨hlV, hx, rfl⟩
    exact TransGen.single ⟨Ol, hOl, ⟨hlV, hl⟩, hx, rfl⟩

/-- Push-up on `{left, mid}`. -/
theorem veeCausality_pushUpOn_lower : veeCausality.PushUpOn Vee.lower := by
  intro U hU x y z
  refine ⟨fun hxy hyz => ⟨hxy.1, hxy.2.1, ?_⟩, fun hxy hyz => ⟨hyz.1, ?_, hyz.2.2⟩⟩
  · obtain ⟨-, hzU, hyz⟩ := hyz
    rw [hxy.2.2] at hyz
    have hz : z ∈ Vee.lower := hU hzU
    cases z
    · exact absurd hyz (by decide)
    · rfl
    · exact absurd rfl hz
  · exact hU hxy.1

/-- Push-up on `{mid, right}`, vacuously: an open subset misses `left`, so has no chronology. -/
theorem veeCausality_pushUpOn_upper : veeCausality.PushUpOn Vee.upper := by
  intro U hU x y z
  exact ⟨fun hxy _ => absurd rfl (hU hxy.1 : Vee.left ∈ Vee.upper),
    fun _ hyz => absurd rfl (hU hyz.1 : Vee.left ∈ Vee.upper)⟩

/-- The vee is locally push-up. -/
theorem veeCausality_locallyPushUp : veeCausality.LocallyPushUp := by
  intro x
  cases x
  · exact ⟨Vee.lower, show Vee.left ∈ ({Vee.right}ᶜ : Set Vee) by simp,
      veeCausality_pushUpOn_lower⟩
  · exact ⟨Vee.lower, show Vee.mid ∈ ({Vee.right}ᶜ : Set Vee) by simp,
      veeCausality_pushUpOn_lower⟩
  · exact ⟨Vee.upper, show Vee.right ∈ ({Vee.left}ᶜ : Set Vee) by simp,
      veeCausality_pushUpOn_upper⟩

/-- The vee is not push-up: `left ≪ mid ≤ right` and nothing is `≪ right`. -/
theorem veeCausality_not_pushUp : ¬ veeCausality.PushUp := by
  intro h
  have hlt : veeCausality.lt ⊤ Vee.left Vee.mid := ⟨trivial, by decide, rfl⟩
  have hle : veeCausality.le ⊤ Vee.mid Vee.right := ⟨trivial, trivial, by decide⟩
  exact absurd ((Causality.pushUp_iff.1 h ⊤).1 hlt hle).2.2 (by decide)

/-- **`T1` cannot be dropped from `AbsolutelyMinimal.pushUp_of_locallyPushUp`**, nor weakened to
`T0`: the vee is `T0`, not `T1`, absolutely minimal and locally push-up, and not push-up. -/
theorem veeCausality_separates_pushUp :
    T0Space Vee ∧ ¬ T1Space Vee ∧ veeCausality.AbsolutelyMinimal ∧ veeCausality.LocallyPushUp ∧
      ¬ veeCausality.PushUp :=
  ⟨Vee.t0Space, Vee.not_t1Space, veeCausality_absolutelyMinimal, veeCausality_locallyPushUp,
    veeCausality_not_pushUp⟩

/-- The edge with `T0` in place of `T1` is false. -/
theorem not_pushUp_of_absolutelyMinimal_of_locallyPushUp_T0 :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T0Space X] (C : Causality X),
      C.AbsolutelyMinimal → C.LocallyPushUp → C.PushUp := fun h =>
  veeCausality_not_pushUp (@h Vee _ Vee.t0Space veeCausality veeCausality_absolutelyMinimal
    veeCausality_locallyPushUp)

/-! ## Local push-up cannot be dropped: the half-chronological line

`Causal.halfChronoLine` (`Causal/LinesReachable.lean`) is the timelike line whose chronology is
kept only after `-1`: absolutely minimal (`halfChronoLine_absolutelyMinimal`), and, as shown here,
causally arc-connected; push-up fails in every neighbourhood of `-1`
(`-1 ≤ y ≪ z` without `-1 ≪ z`). -/

/-- Push-up fails on every open set containing `-1`. -/
theorem halfChronoLine_not_pushUpOn {W : Opens ℝ} (hW : (-1 : ℝ) ∈ W) :
    ¬ halfChronoLine.PushUpOn W := by
  intro h
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (W.isOpen.mem_nhds hW)
  have hε : 0 < (u + 1) / 3 := by linarith
  have hsub : Icc (-1) (-1 + 2 * ((u + 1) / 3)) ⊆ (W : Set ℝ) := fun z hz =>
    hlu ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hle : halfChronoLine.le W (-1) (-1 + (u + 1) / 3) :=
    ⟨by linarith, (Icc_subset_Icc_right (by linarith)).trans hsub⟩
  have hlt : halfChronoLine.lt W (-1 + (u + 1) / 3) (-1 + 2 * ((u + 1) / 3)) :=
    ⟨by linarith, by linarith, (Icc_subset_Icc_left (by linarith)).trans hsub⟩
  exact lt_irrefl _ ((h W le_rfl).2 hle hlt).1

/-- The half-chronological line is not locally push-up. -/
theorem halfChronoLine_not_locallyPushUp : ¬ halfChronoLine.LocallyPushUp := fun h =>
  let ⟨_, hW, hp⟩ := h (-1)
  halfChronoLine_not_pushUpOn hW hp

/-- The half-chronological line is not push-up. -/
theorem halfChronoLine_not_pushUp : ¬ halfChronoLine.PushUp := fun h =>
  halfChronoLine_not_pushUpOn (W := ⊤) trivial (Causality.pushUpOn_top.2 h)

/-- On the half-chronological line, the affine map from `p > -1` to `q > p` is a future chronal
curve of every open set containing the segment. -/
theorem halfChronoLine_chronalCurveOn_affine {U : Opens ℝ} {p q : ℝ} (hp : -1 < p)
    (hpq : p < q) (hsub : Icc p q ⊆ (U : Set ℝ)) :
    halfChronoLine.ChronalCurveOn U (fun t => p + t * (q - p)) 0 1 := by
  have h := timelikeLine_chronalCurveOn_affine hpq hsub
  exact
    { mem := h.mem
      rel := fun t ht N hN htN => by
        obtain ⟨l, u, hl, hu, hrel⟩ := h.rel t ht N hN htN
        refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
        have hpos : 0 ≤ s * (q - p) := mul_nonneg hs.1 (sub_pos.2 hpq).le
        exact halfChronoLine_lt.2 ⟨by linarith, timelikeLine_lt.1 (hrel s hs s' hs' h1 h2 h3)⟩ }

/-- **The half-chronological line is causally arc-connected**: its causal relation and causal
curves are the timelike line's, and a chronological relation `p ≪_U q` (so `p > -1`) is realised
by the affine curve, which stays after `p`. -/
theorem halfChronoLine_causallyArcConnected : halfChronoLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U hU p q
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · exact ((Causality.causallyArcConnectedOn_iff.1 timelikeLine_causallyArcConnected) U hU p q).1
      hpq
  · obtain ⟨hp, hpq, hsub⟩ := hpq
    exact ⟨fun t => p + t * (q - p), halfChronoLine_chronalCurveOn_affine hp hpq hsub, by simp,
      by simp⟩

/-- On the half-chronological line, the identity of `ℝ` is an inextensible causal curve, as on the
timelike line: `CausalCurveIn` is a structure indexed by the causality, so this is not a
definitional transfer, but its proof is the timelike line's. -/
theorem halfChronoLine_inextensible_id : halfChronoLine.Inextensible ⊤ univ id :=
  ⟨⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ =>
      (timelikeLine_causalCurveIn_id (I := univ) ⟨0, trivial⟩ ordConnected_univ).curve a trivial
        b trivial⟩,
    fun ⟨_, c', _, _, ⟨t', _, hgrow⟩⟩ => hgrow (c' t') trivial rfl⟩

/-- On the half-chronological line, causal curves extend. -/
theorem halfChronoLine_curvesExtend : halfChronoLine.CurvesExtend := fun _ _ _ _ _ =>
  ⟨univ, id, halfChronoLine_inextensible_id, fun x _ => ⟨x, trivial, rfl⟩⟩

/-- The half-chronological line has no chronal neighbours: nothing is `≪ -1`. -/
theorem halfChronoLine_not_chronalNeighbours : ¬ halfChronoLine.ChronalNeighbours := fun h => by
  obtain ⟨p, -, hp, hp1, -⟩ := h.1 ⊤ (-1) trivial
  linarith

/-- The half-chronological line is strongly causal in the open form. -/
theorem halfChronoLine_stronglyCausalOpen : halfChronoLine.StronglyCausalOpen :=
  Causality.StronglyCausal.stronglyCausalOpen (C := halfChronoLine) halfChronoLine_tarentin
    timelikeLine_causallyOpen_of_chronalNeighbours timelikeLine_stronglyCausal

/-- The half-chronological line has a time function, `id`. -/
theorem halfChronoLine_hasTimeFunction : halfChronoLine.HasTimeFunction :=
  ⟨id, continuous_id, fun _ _ h hne => lt_of_le_of_ne h.1 hne⟩

/-- **Local push-up cannot be dropped**, from `AbsolutelyMinimal.pushUp_of_locallyPushUp` nor from
`lem:pushup_local` (`CausallyArcConnected.pushUp_of_locallyPushUp`): the half-chronological line
on `ℝ` is causally arc-connected (hence absolutely minimal), globally hyperbolic (hence causal),
strongly causal in both forms, causally open, tarentin, has a time function, and its causal curves
extend; it is neither locally push-up nor push-up. The properties reading `≤` only are the timelike
line's, by definitional equality where they do not pass through the structure `CausalCurveIn`
(kb/0052). -/
theorem halfChronoLine_separates_pushUp :
    halfChronoLine.CausallyArcConnected ∧ halfChronoLine.AbsolutelyMinimal ∧
      halfChronoLine.GloballyHyperbolic ∧ halfChronoLine.IsCausal ∧
      halfChronoLine.StronglyCausal ∧ halfChronoLine.StronglyCausalOpen ∧
      halfChronoLine.CausallyOpen ∧ halfChronoLine.Tarentin ∧ halfChronoLine.HasTimeFunction ∧
      halfChronoLine.CurvesExtend ∧ ¬ halfChronoLine.LocallyPushUp ∧ ¬ halfChronoLine.PushUp :=
  ⟨halfChronoLine_causallyArcConnected, halfChronoLine_absolutelyMinimal,
    timelikeLine_globallyHyperbolic, halfChronoLine_isCausal, timelikeLine_stronglyCausal,
    halfChronoLine_stronglyCausalOpen, timelikeLine_causallyOpen_of_chronalNeighbours,
    halfChronoLine_tarentin, halfChronoLine_hasTimeFunction, halfChronoLine_curvesExtend,
    halfChronoLine_not_locallyPushUp, halfChronoLine_not_pushUp⟩

end Causal
