import Causal.GlobalHyperbolicity
import Causal.Lines
import Causal.LadderLocal
import Causal.NestedTransfer
import Causal.LocateExtension
import Causal.OneWayMembrane

/-!
# Strong causality and two-sided causal openness give the open form, without tarentin

No label is certified here. The file bears on `def:strongly_causal_spacetime` — `ETT.tex:662`
(its two readings, DEC-7), on `def:causally_open_spacetime_open` — `ETT.tex:694` (the two-sided
reading, DEC-8, the ladder node `causally_open`, DEC-163) and on the open form of
`prop:GH_fortement_causal` — `ETT.tex:1199`; none of them is marked.

> $M$ is strongly causal if for every $p\in M$ and every neighbourhood $\U$ of $p$ there exists a
> neighbourhood $\V\subset \U$ of $p$ which is causally convex in $M$.

> The open set $\V$ is causally convex in $\U$ if for all $p,q\in \V$ the full diamond
> $J_\U(p,q)$ is contained in $\V$.

> The causality of $M$ is open, and $M$ is causally open, if for every open subset $\U$ of $M$
> and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is open.

The library's `StronglyCausal.stronglyCausalOpen` (`Causal.GlobalHyperbolicity`) derives the open
form `StronglyCausalOpen` from `StronglyCausal` under tarentin and two-sided causal openness;
tarentin there only finds an open diamond about `p` inside the causally convex neighbourhood.
This file removes tarentin. Given a neighbourhood `V` of `p` causally convex in `M`, let
`O := interior V` and `H := J⁺_M(O) ∩ J⁻_M(O)`, the causal hull of `O`. Then `p ∈ O ⊆ H`
(reflexivity), `H ⊆ V` (`z ∈ H` lies in a diamond `J_M(a, b)` with `a, b ∈ O ⊆ V`), `H` is
causally convex in `M` (transitivity of `≤_M`), and `H` is open as soon as `J^±_M(O)` are. So
`H` is the open causally convex neighbourhood.

* `Causality.StronglyCausal.stronglyCausalOpen_of_causallyOpen` — **the ladder witness**:
  `strongly_causal ∧ causally_open ⇒ strongly_causal_open`, no instance argument.
* `Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_Jplus_Jminus` — the same with causal
  openness at `M` only: `J^±_M(O)` open for every open `O` (no `J^±_U` for `U ≠ M`).
* `Causality.StronglyCausal.stronglyCausalOpen_of_isOpen_hull` — the weakest form proved: the hull
  `J⁺_M(O) ∩ J⁻_M(O)` of every open `O` is open.
* `Causality.stronglyCausalOpen_iff_stronglyCausal_of_causallyOpen` — the two readings of
  `def:strongly_causal_spacetime` agree on causally open spacetimes.
* `Causality.GloballyHyperbolic.stronglyCausalOpen_of_isOpen_Jplus_Jminus` — the open form of
  `prop:GH_fortement_causal` with causal openness at `M` only (the library's form asks
  `CausallyOpen`).
* `Causality.StronglyCausal.exists_not_isOpen_hull` — what a counterexample to
  `strongly_causal → strongly_causal_open` must look like: a point `p` and a neighbourhood `N` such
  that no open `W ∋ p` inside `N` is its own hull, and the hull of **every** open `O ∋ p` whose hull
  lies in `N` is not open (and such `O` exist). `not_causallyOpen_of_not_stronglyCausalOpen` is the
  contrapositive in the ladder's words.

## Which causal openness (DEC-163)

The theorem takes the two-sided node `causally_open` (`C.CausallyOpen`, DEC-8's reading), and the
proof uses both halves, at `U = M` only: `J⁺_M(O)` open for the upper half of the hull, `J⁻_M(O)`
open for the lower. The future form `causally_open_future` alone does not make the hull open:
on the one-way membrane, causally open in the future, strongly causal and not causally open, the
hull `H` built from a causally convex neighbourhood `V` of `(0, 1)` is not open
(`oneWayMembrane_hull_not_isOpen`). The membrane is strongly causal in the open form all the same
(`oneWayMembrane_stronglyCausalOpen`, by balls), so this refutes the argument, not the statement:
whether `strongly_causal ∧ causally_open_future ⇒ strongly_causal_open` holds is **open**, and a
counterexample to it would separate the [[open]] pair `strongly_causal → strongly_causal_open`.

## Witnesses (kb/0011)

* `timelikeLine_scOpen_of_causallyOpen`: the timelike line meets every hypothesis (and tarentin).
* `spacelikeLine_scOpen_without_tarentin`: strongly causal, causally open, **not tarentin**; the
  old witness does not apply, the new one does.
* `isolatedLine_scOpen_without_tarentin`: the line with a chronologically isolated origin
  (`Causal.isolatedLine`, kb/0050) is strongly causal by **closed** intervals
  (`isolatedLine_stronglyCausal`, new), causally open and not tarentin; the theorem gives its open
  form, which the library did not have (open intervals would give it directly: the closed ones are
  chosen so that the theorem does the work).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` strongly causal (`def:strongly_causal_spacetime`, `V` any neighbourhood, DEC-7) | ✓ carried |
| `M` causally open (`def:causally_open_spacetime_open`, read with `J^±`, DEC-8) | ✓ carried by the ladder witness; ⚠ weakened in the two other forms: `J^±_M` of open sets only, or the hull only |
| `M` tarentin (the old witness) | ⚠ weakened: dropped |
| `prop:GH_fortement_causal` (« Let $M$ be a tarentin topological spacetime. If $M$ is globally hyperbolic, then $M$ is strongly causal. », `ETT.tex:1199–1200`), its open form: tarentin, globally hyperbolic, Hausdorff | ⚠ strengthened against the paper, which assumes no causal openness: `J^±_M(O)` open for every open `O` (weaker than the library's `CausallyOpen`, which the old open-form route used); the row itself is closed by the full diamond (DEC-7), so this form is auxiliary |

## SCOPE (disclosed)

* No ETT statement asserts `strongly_causal ∧ causally_open ⇒ strongly_causal_open`; it is a ladder
  edge (programme/ladder.toml, the edge whose `from` was `[strongly_causal, tarentin,
  causally_open]`). The old witness `StronglyCausal.stronglyCausalOpen` stays.
* The hull is taken in `M` (`U = ⊤`); causal convexity "in `M`" is `CausallyConvexIn · ⊤`, as in
  `StronglyCausal` and `StronglyCausalOpen`.
* Whether the future half `causally_open_future` suffices is not settled here (above).
* Strong causality, its open form and two-sided causal openness are each invariant under time
  reversal (`dual_stronglyCausal`, `dual_stronglyCausalOpen`, `dual_causallyOpen`), so the theorem
  is its own dual.
* The membrane witness reads a neighbourhood through the sup distance of `ℝ × ℝ`, as
  `Causal.OneWayMembrane` does; no Lorentzian notion enters.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {A V : Set M} {p : M}

/-! ### The causal hull `J⁺_M(A) ∩ J⁻_M(A)` -/

/-- A set lies in its causal hull in `M`: reflexivity of `≤_M`. -/
theorem subset_Jplus_top_inter_Jminus_top (A : Set M) : A ⊆ C.Jplus ⊤ A ∩ C.Jminus ⊤ A := by
  intro x hx
  exact ⟨⟨x, hx, C.le_refl (show x ∈ (⊤ : Opens M) from trivial)⟩,
    ⟨x, hx, C.le_refl (show x ∈ (⊤ : Opens M) from trivial)⟩⟩

/-- The causal hull in `M` of any set is causally convex in `M`: transitivity of `≤_M`. -/
theorem causallyConvexIn_Jplus_top_inter_Jminus_top (A : Set M) :
    C.CausallyConvexIn (C.Jplus ⊤ A ∩ C.Jminus ⊤ A) ⊤ := by
  refine ⟨fun _ _ => trivial, ?_⟩
  rintro x ⟨⟨a, ha, hax⟩, -⟩ y ⟨-, ⟨b, hb, hyb⟩⟩ z hz
  rw [mem_diamond] at hz
  exact ⟨⟨a, ha, C.le_trans hax hz.1⟩, ⟨b, hb, C.le_trans hz.2 hyb⟩⟩

/-- A set is causally convex in `M` iff it contains its causal hull in `M`. -/
theorem causallyConvexIn_top_iff : C.CausallyConvexIn V ⊤ ↔ C.Jplus ⊤ V ∩ C.Jminus ⊤ V ⊆ V := by
  constructor
  · rintro ⟨-, h⟩ z ⟨⟨a, ha, haz⟩, ⟨b, hb, hzb⟩⟩
    exact h a ha b hb (mem_diamond.2 ⟨haz, hzb⟩)
  · intro h
    refine ⟨fun _ _ => trivial, fun a ha b hb z hz => h ?_⟩
    rw [mem_diamond] at hz
    exact ⟨⟨a, ha, hz.1⟩, ⟨b, hb, hz.2⟩⟩

/-- The causal hull in `M` of a subset of a set causally convex in `M` stays in it. -/
theorem CausallyConvexIn.Jplus_top_inter_Jminus_top_subset (hV : C.CausallyConvexIn V ⊤)
    (hAV : A ⊆ V) : C.Jplus ⊤ A ∩ C.Jminus ⊤ A ⊆ V := by
  intro z hz
  exact causallyConvexIn_top_iff.1 hV
    ⟨Precausality.Jplus_mono hAV hz.1, Precausality.Jminus_mono hAV hz.2⟩

/-- **The core step.** If `V` is a neighbourhood of `p` causally convex in `M` and the causal hull
of `interior V` is open, that hull is an open neighbourhood of `p` inside `V`, causally convex in
`M`. -/
theorem exists_opens_causallyConvexIn_of_isOpen_hull (hV : V ∈ 𝓝 p)
    (hconv : C.CausallyConvexIn V ⊤)
    (hH : IsOpen (C.Jplus ⊤ (interior V) ∩ C.Jminus ⊤ (interior V))) :
    ∃ W : Opens M, p ∈ W ∧ (W : Set M) ⊆ V ∧ C.CausallyConvexIn W ⊤ := by
  refine ⟨⟨_, hH⟩, ?_, ?_, ?_⟩
  · exact subset_Jplus_top_inter_Jminus_top _ (mem_interior_iff_mem_nhds.2 hV)
  · exact hconv.Jplus_top_inter_Jminus_top_subset interior_subset
  · exact causallyConvexIn_Jplus_top_inter_Jminus_top _

/-! ### Strong causality gives the open form -/

/-- **Strong causality gives the open form once causal hulls of open sets are open**, with no
tarentin and no causal openness in a proper open subset. -/
theorem StronglyCausal.stronglyCausalOpen_of_isOpen_hull
    (hH : ∀ O : Opens M, IsOpen (C.Jplus ⊤ O ∩ C.Jminus ⊤ O)) (h : C.StronglyCausal) :
    C.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨V, hV, hVN, hconv⟩ := h p N hN
  obtain ⟨W, hpW, hWV, hW⟩ := exists_opens_causallyConvexIn_of_isOpen_hull hV hconv
    (hH ⟨interior V, isOpen_interior⟩)
  exact ⟨W, hpW, hWV.trans hVN, hW⟩

/-- **Strong causality gives the open form under causal openness at `M`**: `J⁺_M(O)` and
`J⁻_M(O)` open for every open `O`. No tarentin. -/
theorem StronglyCausal.stronglyCausalOpen_of_isOpen_Jplus_Jminus
    (hJ : ∀ O : Opens M, IsOpen (C.Jplus ⊤ O) ∧ IsOpen (C.Jminus ⊤ O)) (h : C.StronglyCausal) :
    C.StronglyCausalOpen := by
  exact h.stronglyCausalOpen_of_isOpen_hull fun O => (hJ O).1.inter (hJ O).2

/-- Two-sided causal openness gives causal openness at `M`. -/
theorem CausallyOpen.isOpen_Jplus_top_Jminus_top (hO : C.CausallyOpen) (O : Opens M) :
    IsOpen (C.Jplus ⊤ O) ∧ IsOpen (C.Jminus ⊤ O) := by
  exact ⟨hO.1 ⊤ O le_top, hO.2 ⊤ O le_top⟩

/-- **Strong causality and causal openness give the open form, without tarentin**:
`strongly_causal ∧ causally_open ⇒ strongly_causal_open`. The ladder
node is `causally_open`, two-sided (DEC-8, DEC-163): the proof opens the hull `J⁺_M(O) ∩ J⁻_M(O)`
with both halves, at `U = M` only. The future half alone does not open the hull
(`oneWayMembrane_hull_not_isOpen`); whether it suffices for the conclusion is open. -/
theorem StronglyCausal.stronglyCausalOpen_of_causallyOpen (hO : C.CausallyOpen)
    (h : C.StronglyCausal) : C.StronglyCausalOpen := by
  exact h.stronglyCausalOpen_of_isOpen_Jplus_Jminus hO.isOpen_Jplus_top_Jminus_top

/-- On a causally open spacetime the two readings of `def:strongly_causal_spacetime` agree, with
no tarentin (the library's `stronglyCausal_iff_alexandrovTopology_eq` route asks it). -/
theorem stronglyCausalOpen_iff_stronglyCausal_of_causallyOpen (hO : C.CausallyOpen) :
    C.StronglyCausalOpen ↔ C.StronglyCausal := by
  exact ⟨StronglyCausalOpen.stronglyCausal, StronglyCausal.stronglyCausalOpen_of_causallyOpen hO⟩

/-- `prop:GH_fortement_causal`, open form, under causal openness at `M` only: the library's
`GloballyHyperbolic.stronglyCausalOpen` asks `CausallyOpen`. Tarentin stays: it gives strong
causality (kb/0115). -/
theorem GloballyHyperbolic.stronglyCausalOpen_of_isOpen_Jplus_Jminus [T2Space M]
    (hT : C.Tarentin) (hJ : ∀ O : Opens M, IsOpen (C.Jplus ⊤ O) ∧ IsOpen (C.Jminus ⊤ O))
    (hG : C.GloballyHyperbolic) : C.StronglyCausalOpen := by
  exact (hG.stronglyCausal hT).stronglyCausalOpen_of_isOpen_Jplus_Jminus hJ

/-! ### What a counterexample to `strongly_causal → strongly_causal_open` must look like -/

/-- **The bad point of a counterexample.** If `C` is strongly causal and not in the open form,
there are a point `p` and a neighbourhood `N` of `p` such that: some open `O ∋ p` has its causal
hull in `N` (the interior of a causally convex neighbourhood in `N`); the causal hull of every
open `O ∋ p` whose hull lies in `N` is not open; and no open `W ∋ p` inside `N` contains its own
hull. -/
theorem StronglyCausal.exists_not_isOpen_hull (h : C.StronglyCausal)
    (hn : ¬ C.StronglyCausalOpen) :
    ∃ p : M, ∃ N ∈ 𝓝 p,
      (∃ O : Opens M, p ∈ O ∧ C.Jplus ⊤ O ∩ C.Jminus ⊤ O ⊆ N) ∧
      (∀ O : Opens M, p ∈ O → C.Jplus ⊤ O ∩ C.Jminus ⊤ O ⊆ N →
        ¬ IsOpen (C.Jplus ⊤ O ∩ C.Jminus ⊤ O)) ∧
      ∀ W : Opens M, p ∈ W → (W : Set M) ⊆ N → ¬ C.Jplus ⊤ W ∩ C.Jminus ⊤ W ⊆ W := by
  unfold StronglyCausalOpen at hn
  push Not at hn
  obtain ⟨p, N, hN, hbad⟩ := hn
  have hnot : ∀ W : Opens M, p ∈ W → (W : Set M) ⊆ N → ¬ C.Jplus ⊤ W ∩ C.Jminus ⊤ W ⊆ W :=
    fun W hpW hWN hsub => hbad W hpW hWN (causallyConvexIn_top_iff.2 hsub)
  refine ⟨p, N, hN, ?_, fun O hpO hON hopen => ?_, hnot⟩
  · obtain ⟨V, hV, hVN, hconv⟩ := h p N hN
    exact ⟨⟨interior V, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hV,
      (hconv.Jplus_top_inter_Jminus_top_subset interior_subset).trans hVN⟩
  · exact hbad ⟨_, hopen⟩ (subset_Jplus_top_inter_Jminus_top _ hpO) hON
      (causallyConvexIn_Jplus_top_inter_Jminus_top _)

/-- A counterexample to `strongly_causal → strongly_causal_open` is not causally open
(`causally_open`), and not even causally open at `M`. -/
theorem StronglyCausal.not_causallyOpen_of_not_stronglyCausalOpen (h : C.StronglyCausal)
    (hn : ¬ C.StronglyCausalOpen) :
    ¬ C.CausallyOpen ∧ ¬ ∀ O : Opens M, IsOpen (C.Jplus ⊤ O) ∧ IsOpen (C.Jminus ⊤ O) := by
  have hJ : ¬ ∀ O : Opens M, IsOpen (C.Jplus ⊤ O) ∧ IsOpen (C.Jminus ⊤ O) := fun hJ =>
    hn (h.stronglyCausalOpen_of_isOpen_Jplus_Jminus hJ)
  exact ⟨fun hO => hJ hO.isOpen_Jplus_top_Jminus_top, hJ⟩

end Causality

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
