import Causal.GlobalHyperbolicity

/-!
# The causal hull, and strong causality's open form under two-sided causal openness

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

**Moved in** (programme target `T-abs-sc-open-hoist`): this module is the model-free half of
`Causal.SCOpenWithoutTarentin` (T-abs-sc-open-without-tarentin), its sections "The causal hull",
"Strong causality gives the open form" and "What a counterexample … must look like", moved byte
for byte under the same full names. It imports `Causal.GlobalHyperbolicity` only (for
`GloballyHyperbolic.stronglyCausal`; `Causal.Properties` and `Causal.StrongCausality` come with
it), so that `Causal.Ladder.Rules` can register the ladder witness without the witnesses' modules
(`Causal.Lines`, `Causal.LadderLocal`, `Causal.NestedTransfer`, `Causal.LocateExtension`,
`Causal.OneWayMembrane`). The witnesses stay in `Causal.SCOpenWithoutTarentin`, which imports
this module.

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
* The hull lemmas: `subset_Jplus_top_inter_Jminus_top`,
  `causallyConvexIn_Jplus_top_inter_Jminus_top`, `causallyConvexIn_top_iff`,
  `CausallyConvexIn.Jplus_top_inter_Jminus_top_subset` and the core step
  `exists_opens_causallyConvexIn_of_isOpen_hull`.

## Which causal openness (DEC-163)

The theorem takes the two-sided node `causally_open` (`C.CausallyOpen`, DEC-8's reading), and the
proof uses both halves, at `U = M` only: `J⁺_M(O)` open for the upper half of the hull, `J⁻_M(O)`
open for the lower. The future form `causally_open_future` alone does not make the hull open:
on the one-way membrane, causally open in the future, strongly causal and not causally open, the
hull `H` built from a causally convex neighbourhood `V` of `(0, 1)` is not open
(`oneWayMembrane_hull_not_isOpen`, which stays with the witnesses in
`Causal.SCOpenWithoutTarentin`). The membrane is strongly causal in the open form all the same
(`oneWayMembrane_stronglyCausalOpen`, by balls), so this refutes the argument, not the statement:
whether `strongly_causal ∧ causally_open_future ⇒ strongly_causal_open` holds is **open**, and a
counterexample to it would separate the [[open]] pair `strongly_causal → strongly_causal_open`.

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
* No model is imported, and `causal_ladder` is not used (kb/0221): `Causal.Ladder.Rules` imports
  the module that holds its witness.
* Non-vacuity (kb/0011): the witnesses — the timelike, spacelike and isolated lines, and the
  one-way membrane — are in `Causal.SCOpenWithoutTarentin`.

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

end Causal
