import Causal.LadderLocal
import Causal.CurvesExtend
import Causal.Ladder.Rules

/-!
# Push-up and local causal openness do not give causal openness: the jump line

Programme target `T-abs-pushup-not-open` (`programme/roadmap.toml:586`; layer 1, no label of
`ETT.tex`). Imports: `Causal.LadderLocal`, `Causal.CurvesExtend`, `Causal.Ladder.Rules` (ETT
layer, no model, transitively). On `ℝ`, the **jump line** `jumpLine` has `≪` empty and `≤_U` the
diagonal of `U` together with the one pair `0 ≤_U 1` in every open `U` containing `0` and `1`.

* **`T-abs-pushup-not-open/line`** — `jumpLine`, a `Causality ℝ`, every field discharged
  (`le_mono`: `0 ≤_V 1` needs `0, 1 ∈ V ⊆ U`); `jumpLine_le`; in an open set missing `0` or `1`
  the order is the diagonal (`jumpLine_le_of_not`, `jumpLine_Jplus_of_not`,
  `jumpLine_Jminus_of_not`).
* **`T-abs-pushup-not-open/push-up`** — `jumpLine_pushUp`, vacuously.
* **`T-abs-pushup-not-open/locally-causally-open`** — `jumpLine_locallyCausallyOpen`, two-sided
  (the ladder node `LocallyCausallyOpen`): `{1}ᶜ` and `{0}ᶜ` are causally open in both time
  directions as spacetimes (`jumpLine_causallyOpenFutureOn_of_not`).
* **`T-abs-pushup-not-open/not-open`** — `jumpLine_Jplus_Ioo` (`J⁺((−1, 1)) = (−1, 1]`),
  `jumpLine_not_isOpen_Jplus_Ioo`, `jumpLine_not_causallyOpenFuture`, `jumpLine_not_causallyOpen`.
* **`T-abs-pushup-not-open/not-absolutely-minimal`** — `jumpLine_not_absolutelyMinimal`, by the
  ladder (`causal_ladder`, through `absolutely_minimal ∧ locally_causally_open_future ⇒
  causally_open_future`), and `jumpLine_not_absolutelyMinimalOn_top`, directly (in the cover by
  `{1}ᶜ` and `{0}ᶜ` every localised relation is an equality).
* **`T-abs-pushup-not-open/separation`** — the conjoined witness
  `jumpLine_separates_causallyOpenFuture`; the bare forms
  `not_causallyOpenFuture_of_pushUp_of_locallyCausallyOpen_bare` and, for
  `prop:topological_spacetime_absolutely_minimal` (`ETT.tex:698`) with absolute minimality
  dropped, `not_causallyOpenFuture_of_locallyCausallyOpenFuture_bare` (as printed) and
  `not_causallyOpen_of_locallyCausallyOpen_bare` (DEC-8).
* **`T-abs-pushup-not-open/beyond`** (beyond the target) — `jumpLine_isCausal`,
  `jumpLine_globallyHyperbolic`, `jumpLine_stronglyCausalOpen`, `jumpLine_hasTimeFunction`;
  `jumpLine_not_chronalNeighbours`, `jumpLine_not_tarentin`, `jumpLine_not_causallyPlain`,
  `jumpLine_not_causallyArcConnected`.

> If $M$ is absolutely minimal and if for every $p\in M$ there exists a neighbourhood $\U$ of
> $p$ whose causality is open, then the causality of $M$ is open.
> (`prop:topological_spacetime_absolutely_minimal`, `ETT.tex:698`)

> The causality of $M$ is open, and $M$ is causally open, if for every open subset $\U$ of $M$
> and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is open.
> (`def:causally_open_spacetime_open`, `ETT.tex:694`)

> Push-up and local causal openness do not give causal openness: on ℝ, the causality with ≪ empty
> and ≤_U the diagonal plus 0 ≤ 1 in every open U containing 0 and 1 has push-up and is two-sided
> locally causally open, while J⁺((−1, 1)) = (−1, 1] is not open: not causally open in the future,
> hence not causally open, and (by the ladder) not absolutely minimal
> (`programme/roadmap.toml:587`)

## Hypothesis checklist

| hypothesis of the target | here |
|---|---|
| a causality on `ℝ`, `≪` empty, `≤_U` the diagonal plus `0 ≤_U 1` when `0, 1 ∈ U` | ✓ carried: `jumpLine`, `jumpLine_le` (`Iff.rfl`) |
| push-up | ✓ carried: `PushUp` |
| two-sided local causal openness | ✓ carried: `LocallyCausallyOpen` (kb/0053), with open neighbourhoods |
| `J⁺((−1, 1)) = (−1, 1]` not open; not causally open (in the future) | ✓ carried, `J⁺` taken in `U = ℝ` |
| not absolutely minimal, by the ladder | ✓ carried, and directly |

## SCOPE (disclosed)

* **The jump line is not absolutely minimal, and must not be**: by
  `prop:topological_spacetime_absolutely_minimal` every witness of `locally_causally_open ⇏
  causally_open_future` fails absolute minimality. It is a causality in the library's reading of
  `defi:causalite` (the "equivalently" form, no gluing axiom, kb/0014); under a gluing reading of
  "sheaf" (OQ-18) every causality is absolutely minimal, the jump line is not one of ETT's
  spacetimes, and local causal openness would give causal openness. It is causal and globally
  hyperbolic. `push_up ⇏ causally_open_future` alone holds in both readings: the rational line
  (`Causal.rationalLine_separates_absolutelyMinimal`) is absolutely minimal.
* **The space is `ℝ`**, Hausdorff and second countable (`def:category_topological_spacetimes`,
  `ETT.tex:254`). No metric notion enters a statement: `ℝ`'s order and topology only.
* **"Neighbourhood" in `ETT.tex:698`** may be read as not necessarily open; the jump line's are
  open, which satisfies either reading.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set TopologicalSpace Topology

/-! ## The jump line -/

/-- **The jump line**: on `ℝ`, `x ≤_U y` iff `x = y ∈ U`, or `x = 0`, `y = 1` and `0, 1 ∈ U`;
no chronology. Push-up holds vacuously; an open set missing `0` or `1` carries the diagonal
order, so the line is locally causally open; `J⁺((−1, 1)) = (−1, 1]` is not open. -/
def jumpLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (x = 0 ∧ y = 1 ∧ (0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U)
  lt _ _ _ := False
  le_mem_left h := h.elim (fun h => h.2) fun h => h.1 ▸ h.2.2.1
  le_mem_right h := h.elim (fun h => h.1 ▸ h.2) fun h => h.2.1 ▸ h.2.2.2
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨rfl, rfl, h0, h1⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨h, -, -, -⟩
    · exact Or.inr ⟨rfl, rfl, h0, h1⟩
    · exact absurd h one_ne_zero
  lt_trans h _ := h
  le_mono h _ _ h' := h'.elim (fun h' => Or.inl ⟨h'.1, h h'.2⟩)
    fun h' => Or.inr ⟨h'.1, h'.2.1, h h'.2.2.1, h h'.2.2.2⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

theorem jumpLine_le {U : Opens ℝ} {x y : ℝ} :
    jumpLine.le U x y ↔ (x = y ∧ x ∈ U) ∨ (x = 0 ∧ y = 1 ∧ (0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U) :=
  Iff.rfl

/-- In an open set missing `0` or `1` the jump line's order is the diagonal. -/
theorem jumpLine_le_of_not {U : Opens ℝ} (hU : ¬ ((0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U)) {x y : ℝ} :
    jumpLine.le U x y ↔ x = y ∧ x ∈ U := by
  rw [jumpLine_le]
  exact ⟨fun h => h.resolve_right fun h' => hU ⟨h'.2.2.1, h'.2.2.2⟩, Or.inl⟩

theorem jumpLine_Jplus_of_not {U V : Opens ℝ} (hU : ¬ ((0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U))
    (hVU : V ≤ U) : jumpLine.Jplus U V = V := by
  ext y
  rw [Precausality.mem_Jplus]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact (jumpLine_le_of_not hU).1 hxy |>.1 ▸ hx
  · exact fun hy => ⟨y, hy, (jumpLine_le_of_not hU).2 ⟨rfl, hVU hy⟩⟩

theorem jumpLine_Jminus_of_not {U V : Opens ℝ} (hU : ¬ ((0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U))
    (hVU : V ≤ U) : jumpLine.Jminus U V = V := by
  ext y
  rw [Precausality.mem_Jminus]
  constructor
  · rintro ⟨x, hx, hyx⟩
    exact ((jumpLine_le_of_not hU).1 hyx).1 ▸ hx
  · exact fun hy => ⟨y, hy, (jumpLine_le_of_not hU).2 ⟨rfl, hVU hy⟩⟩

/-! ## Push-up and local causal openness -/

/-- **The jump line has push-up**, vacuously: `≪` is empty. -/
theorem jumpLine_pushUp : jumpLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- An open set missing `0` or `1` is causally open in both time directions, as a spacetime. -/
theorem jumpLine_causallyOpenFutureOn_of_not {W : Opens ℝ}
    (hW : ¬ ((0 : ℝ) ∈ W ∧ (1 : ℝ) ∈ W)) :
    jumpLine.CausallyOpenFutureOn W ∧ jumpLine.dual.CausallyOpenFutureOn W := by
  have hU : ∀ U : Opens ℝ, U ≤ W → ¬ ((0 : ℝ) ∈ U ∧ (1 : ℝ) ∈ U) :=
    fun U hUW h => hW ⟨hUW h.1, hUW h.2⟩
  refine ⟨fun U V hUW hVU => ?_, fun U V hUW hVU => ?_⟩
  · rw [jumpLine_Jplus_of_not (hU U hUW) hVU]
    exact V.isOpen
  · have h : jumpLine.dual.Jplus U V = jumpLine.Jminus U V := rfl
    rw [h, jumpLine_Jminus_of_not (hU U hUW) hVU]
    exact V.isOpen

/-- **The jump line is locally causally open, in both time directions**: `{1}ᶜ` is an open
neighbourhood of every point but `1`, `{0}ᶜ` one of `1`, and neither contains both `0` and `1`. -/
theorem jumpLine_locallyCausallyOpen : jumpLine.LocallyCausallyOpen := by
  rw [Causality.locallyCausallyOpen_iff]
  intro x
  by_cases hx : x = 1
  · refine ⟨⟨{0}ᶜ, isOpen_compl_singleton⟩, ?_, jumpLine_causallyOpenFutureOn_of_not ?_⟩
    · show x ∈ ({0}ᶜ : Set ℝ)
      rw [hx]
      exact one_ne_zero
    · exact fun h => (h.1 : (0 : ℝ) ∈ ({0}ᶜ : Set ℝ)) rfl
  · refine ⟨⟨{1}ᶜ, isOpen_compl_singleton⟩, hx, jumpLine_causallyOpenFutureOn_of_not ?_⟩
    exact fun h => (h.2 : (1 : ℝ) ∈ ({1}ᶜ : Set ℝ)) rfl

/-! ## Not causally open -/

/-- **`J⁺((−1, 1)) = (−1, 1]`** in `ℝ`: `1` is reached from `0`. -/
theorem jumpLine_Jplus_Ioo : jumpLine.Jplus ⊤ (Ioo (-1) 1) = Ioc (-1) 1 := by
  ext y
  rw [Precausality.mem_Jplus]
  constructor
  · rintro ⟨x, hx, ⟨rfl, -⟩ | ⟨-, rfl, -, -⟩⟩
    · exact ⟨hx.1, hx.2.le⟩
    · exact ⟨by norm_num, le_rfl⟩
  · rintro ⟨hy1, hy2⟩
    rcases hy2.lt_or_eq with hy | rfl
    · exact ⟨y, ⟨hy1, hy⟩, Or.inl ⟨rfl, trivial⟩⟩
    · exact ⟨0, ⟨by norm_num, by norm_num⟩, Or.inr ⟨rfl, rfl, trivial, trivial⟩⟩

theorem jumpLine_not_isOpen_Jplus_Ioo : ¬ IsOpen (jumpLine.Jplus ⊤ (Ioo (-1) 1)) := by
  rw [jumpLine_Jplus_Ioo]
  intro h
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (h.mem_nhds (⟨by norm_num, le_rfl⟩ : (1 : ℝ) ∈ Ioc (-1) 1))
  have hm : (1 + u) / 2 ∈ Ioc (-1 : ℝ) 1 := hlu ⟨by linarith, by linarith⟩
  linarith [hm.2]

/-- **The jump line is not causally open in the future** (`def:causally_open_spacetime_open` as
printed): `J⁺_ℝ((−1, 1))` is not open. -/
theorem jumpLine_not_causallyOpenFuture : ¬ jumpLine.CausallyOpenFuture := fun h =>
  jumpLine_not_isOpen_Jplus_Ioo (h ⊤ ⟨Ioo (-1) 1, isOpen_Ioo⟩ le_top)

/-- **The jump line is not causally open** (DEC-8, two-sided). -/
theorem jumpLine_not_causallyOpen : ¬ jumpLine.CausallyOpen := fun h =>
  jumpLine_not_causallyOpenFuture h.future

/-! ## Not absolutely minimal -/

/-- **The jump line is not absolutely minimal, by the ladder**: absolute minimality and local
causal openness in the future would give causal openness in the future
(`prop:topological_spacetime_absolutely_minimal`, the `causal_ladder` rule
`AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture`). -/
theorem jumpLine_not_absolutelyMinimal : ¬ jumpLine.AbsolutelyMinimal := by
  intro hmin
  have hloc := jumpLine_locallyCausallyOpen
  have hopen : jumpLine.CausallyOpenFuture := by causal_ladder
  exact jumpLine_not_causallyOpenFuture hopen

/-- **The jump line is not absolutely minimal, directly**: in the cover of `ℝ` by `{1}ᶜ` and
`{0}ᶜ` every localised relation is an equality, so `0 ≤_ℝ 1` is no chain of them. -/
theorem jumpLine_not_absolutelyMinimalOn_top :
    ¬ jumpLine.toPrecausality.AbsolutelyMinimalOn ⊤ := by
  intro h
  let O₁ : Opens ℝ := ⟨{1}ᶜ, isOpen_compl_singleton⟩
  let O₀ : Opens ℝ := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let S : Set (Opens ℝ) := {O₁, O₀}
  have hS : ∀ x ∈ (⊤ : Opens ℝ), ∃ O ∈ S, x ∈ O := by
    intro x _
    by_cases hx : x = 1
    · refine ⟨O₀, Or.inr rfl, ?_⟩
      show x ∈ ({0}ᶜ : Set ℝ)
      rw [hx]
      exact one_ne_zero
    · exact ⟨O₁, Or.inl rfl, hx⟩
  -- each member of the cover misses `0` or `1`, so each localised relation is an equality
  have hmiss : ∀ O ∈ S, ¬ ((0 : ℝ) ∈ (⊤ ⊓ O : Opens ℝ) ∧ (1 : ℝ) ∈ (⊤ ⊓ O : Opens ℝ)) := by
    rintro O (rfl | rfl) ⟨h0, h1⟩
    · exact (h1.2 : (1 : ℝ) ∈ ({1}ᶜ : Set ℝ)) rfl
    · exact (h0.2 : (0 : ℝ) ∈ ({0}ᶜ : Set ℝ)) rfl
  have hstep : ∀ a b : ℝ, (∃ O ∈ S, jumpLine.le (⊤ ⊓ O) a b) → a = b := by
    rintro a b ⟨O, hO, hab⟩
    exact ((jumpLine_le_of_not (hmiss O hO)).1 hab).1
  have hchain : ∀ {a b : ℝ},
      Relation.TransGen (fun a b => ∃ O ∈ S, jumpLine.le (⊤ ⊓ O) a b) a b → a = b := by
    intro a b hab
    induction hab with
    | single hl => exact hstep _ _ hl
    | tail _ hl ih => exact ih.trans (hstep _ _ hl)
  have h01 : jumpLine.le ⊤ 0 1 := Or.inr ⟨rfl, rfl, trivial, trivial⟩
  exact zero_ne_one (hchain ((h S hS ⊤ le_rfl 0 1).1 h01))

/-! ## Beyond the target: what else the jump line has and lacks -/

/-- **The jump line is causal**: `1 ≤ 0` holds in no open set. -/
theorem jumpLine_isCausal : jumpLine.IsCausal := by
  intro x y hxy hyx
  rcases hxy with ⟨h, -⟩ | ⟨rfl, rfl, -, -⟩
  · exact h
  · rcases hyx with ⟨h, -⟩ | ⟨h, -, -, -⟩
    · exact h.symm
    · exact absurd h one_ne_zero

/-- Every diamond of the jump line lies in its two vertices. -/
theorem jumpLine_diamond_subset (U : Opens ℝ) (p q : ℝ) :
    jumpLine.diamond U p q ⊆ {p, q} := by
  intro x hx
  obtain ⟨hpx, hxq⟩ := Causality.mem_diamond.1 hx
  rcases hpx with ⟨rfl, -⟩ | ⟨rfl, rfl, -, -⟩
  · exact Or.inl rfl
  · rcases hxq with ⟨rfl, -⟩ | ⟨h, -, -, -⟩
    · exact Or.inr rfl
    · exact absurd h one_ne_zero

/-- **The jump line is globally hyperbolic**: causal, with finite diamonds. -/
theorem jumpLine_globallyHyperbolic : jumpLine.GloballyHyperbolic :=
  ⟨jumpLine_isCausal, fun p q =>
    ((Set.toFinite ({p, q} : Set ℝ)).subset (jumpLine_diamond_subset ⊤ p q)).isCompact⟩

/-- Every subset of `ℝ` is causally convex in `ℝ` for the jump line. -/
theorem jumpLine_causallyConvexIn (V : Set ℝ) : jumpLine.CausallyConvexIn V ⊤ := by
  refine ⟨fun _ _ => trivial, fun p hp q hq x hx => ?_⟩
  rcases jumpLine_diamond_subset ⊤ p q hx with rfl | rfl
  · exact hp
  · exact hq

/-- **The jump line is strongly causal, with open causally convex neighbourhoods.** -/
theorem jumpLine_stronglyCausalOpen : jumpLine.StronglyCausalOpen := fun _ U hU =>
  ⟨⟨interior U, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hU, interior_subset,
    jumpLine_causallyConvexIn _⟩

/-- **The jump line has a time function** (the ladder node `time_function`): the identity. -/
theorem jumpLine_hasTimeFunction : jumpLine.HasTimeFunction := by
  refine ⟨id, continuous_id, fun x y hxy hne => ?_⟩
  rcases hxy with ⟨h, -⟩ | ⟨rfl, rfl, -, -⟩
  · exact absurd h hne
  · exact zero_lt_one

/-- The jump line has no chronal neighbours: its chronological relation is empty. -/
theorem jumpLine_not_chronalNeighbours : ¬ jumpLine.ChronalNeighbours := fun h =>
  let ⟨_, _, hp⟩ := h.1 ⊤ 0 trivial
  hp

/-- **The jump line is not tarentin**: its diamonds are finite, with empty interior. -/
theorem jumpLine_not_tarentin : ¬ jumpLine.Tarentin := by
  intro h
  obtain ⟨p, -, q, -, hx⟩ := h 0 univ Filter.univ_mem
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 hx)
  exact (Set.Ioo_infinite (hl.trans hu)) ((Set.toFinite ({p, q} : Set ℝ)).subset
    (hlu.trans (jumpLine_diamond_subset ⊤ p q)))

/-- **The jump line is not causally plain**: `Int J⁺(ℝ) = ℝ` while `I⁺(ℝ) = ∅`. -/
theorem jumpLine_not_causallyPlain : ¬ jumpLine.CausallyPlain := by
  intro h
  have hJ : jumpLine.Jplus ⊤ univ = univ :=
    eq_univ_of_forall fun y => ⟨y, trivial, jumpLine.le_refl trivial⟩
  have hI : jumpLine.Iplus ⊤ univ = ∅ := eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h
  have h0 := (h ⊤ univ).1 (show (0 : ℝ) ∈ interior (jumpLine.Jplus ⊤ univ) by
    rw [hJ, interior_univ]; trivial)
  rw [hI, closure_empty] at h0
  exact h0

/-- The jump line is not causally arc-connected: it is not absolutely minimal
(`cor:causalement_connexe_minimal`). -/
theorem jumpLine_not_causallyArcConnected : ¬ jumpLine.CausallyArcConnected := fun h =>
  jumpLine_not_absolutelyMinimal (Causality.CausallyArcConnected.absolutelyMinimal h)

/-! ## The separation -/

/-- **Push-up and local causal openness do not give causal openness in the future**: the jump
line has push-up, is two-sided locally causally open, globally hyperbolic, strongly causal with
open convex neighbourhoods and has a time function, and it is neither causally open in the
future, nor causally open, nor absolutely minimal, nor causally arc-connected; it has no chronal
neighbours and is neither tarentin nor causally plain. The conjoined witness for the ladder. -/
theorem jumpLine_separates_causallyOpenFuture :
    jumpLine.PushUp ∧ jumpLine.LocallyCausallyOpen ∧ jumpLine.GloballyHyperbolic ∧
      jumpLine.StronglyCausalOpen ∧ jumpLine.HasTimeFunction ∧
      ¬ jumpLine.CausallyOpenFuture ∧ ¬ jumpLine.CausallyOpen ∧
      ¬ jumpLine.AbsolutelyMinimal ∧ ¬ jumpLine.CausallyArcConnected ∧
      ¬ jumpLine.ChronalNeighbours ∧ ¬ jumpLine.Tarentin ∧ ¬ jumpLine.CausallyPlain :=
  ⟨jumpLine_pushUp, jumpLine_locallyCausallyOpen, jumpLine_globallyHyperbolic,
    jumpLine_stronglyCausalOpen, jumpLine_hasTimeFunction, jumpLine_not_causallyOpenFuture,
    jumpLine_not_causallyOpen, jumpLine_not_absolutelyMinimal, jumpLine_not_causallyArcConnected,
    jumpLine_not_chronalNeighbours, jumpLine_not_tarentin, jumpLine_not_causallyPlain⟩

/-- **Push-up and two-sided local causal openness together do not give causal openness in the
future**, on `ℝ`. -/
theorem not_causallyOpenFuture_of_pushUp_of_locallyCausallyOpen_bare :
    ¬ ∀ C : Causality ℝ, C.PushUp → C.LocallyCausallyOpen → C.CausallyOpenFuture := fun h =>
  jumpLine_not_causallyOpenFuture (h _ jumpLine_pushUp jumpLine_locallyCausallyOpen)

/-- **`prop:topological_spacetime_absolutely_minimal` without absolute minimality, as printed,
is false** in the library's reading of `defi:causalite` (no gluing, kb/0014, OQ-18): local causal openness in the future does not give causal openness in the future. -/
theorem not_causallyOpenFuture_of_locallyCausallyOpenFuture_bare :
    ¬ ∀ C : Causality ℝ, C.LocallyCausallyOpenFuture → C.CausallyOpenFuture := fun h =>
  jumpLine_not_causallyOpenFuture (h _ jumpLine_locallyCausallyOpen.future)

/-- **`prop:topological_spacetime_absolutely_minimal` without absolute minimality, DEC-8
reading, is false** in the library's reading of `defi:causalite` (no gluing, kb/0014, OQ-18): two-sided local causal openness does not give causal openness. -/
theorem not_causallyOpen_of_locallyCausallyOpen_bare :
    ¬ ∀ C : Causality ℝ, C.LocallyCausallyOpen → C.CausallyOpen := fun h =>
  jumpLine_not_causallyOpen (h _ jumpLine_locallyCausallyOpen)

end Causal
