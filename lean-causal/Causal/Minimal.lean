import Causal.Generated
import Mathlib.Topology.Sequences

/-!
# Consequences of absolute minimality

**`prop:topological_spacetime_absolutely_minimal`** — `ETT.tex:698`.
**`rem:absolutely_minimal_topological_spacetime`** — `ETT.tex:780`.
**`lem:cup_cap`** — `ETT.tex:962`. **`rem:same_notation_one_proves`** — `ETT.tex:987`.

> Let $M$ be a topological spacetime. If $M$ is absolutely minimal and if for every $p\in M$
> there exists a neighbourhood $\U$ of $p$ whose causality is open, then the causality of $M$ is
> open.

> If $M$ is an absolutely minimal topological spacetime, then a point is strongly tarentin in
> the past (resp. in the future) if and only if its chronological past (resp. future) is
> non-empty.

> Let $M$ be an absolutely minimal topological spacetime, let $p\in M$ and let
> $(p_n)_{n\in \N}\in M^\N$ be a sequence converging to $p$. If $J^+(x)$ is closed for every
> $x\in M$, then $$I^{-}(p)\subset \mathrm{Int}\left(\bigcup_{N\in \N}\bigcap_{n\geq N}
> I^-(p_n)\right)\subset \ring J^-(p) \cap Z^{+}(M).$$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:topological_spacetime_absolutely_minimal`: absolutely minimal | ✓ carried |
| — every point has a neighbourhood whose causality is open | ✓ carried, the neighbourhood taken open: `CausallyOpenFutureOn W` |
| — second countable, Hausdorff | ⚠ weakened: not used |
| `rem:absolutely_minimal_topological_spacetime`: absolutely minimal | ✓ carried |
| — Hausdorff | ⚠ weakened: `T1Space M` |
| — second countable | ⚠ weakened: not used |
| `lem:cup_cap`: absolutely minimal; `p_n → p`; `J^+(x)` closed for every `x` | ✓ carried |
| — Hausdorff | ⚠ weakened: `T1Space M` |
| — second countable | ⚠ weakened: not used |

## SCOPE (disclosed)

* `prop:topological_spacetime_absolutely_minimal` is proved for causal openness **as the paper
  defines it** (`CausallyOpenFuture`, `J^+_U(V)` open) and also for the two-sided form
  (`CausallyOpen`), each from the corresponding local hypothesis.
* In `lem:cup_cap` absolute minimality is used only for the inclusion in `Z^+(M)`, through
  `rem:absolutely_minimal_topological_spacetime`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Relation

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {p : M}

theorem dual_absolutelyMinimal : C.dual.AbsolutelyMinimal ↔ C.AbsolutelyMinimal := by
  rw [Precausality.absolutelyMinimal_iff, Precausality.absolutelyMinimal_iff]
  exact Precausality.dual_absolutelyMinimalOn (Q := C.toPrecausality)

/-! ### `rem:absolutely_minimal_topological_spacetime` -/

/-- **`rem:absolutely_minimal_topological_spacetime`**, future. -/
theorem AbsolutelyMinimal.mem_Zplus_iff [T1Space M] (h : C.AbsolutelyMinimal) :
    p ∈ C.Zplus ↔ (C.Iplus ⊤ {p}).Nonempty := by
  refine ⟨Iplus_nonempty_of_mem_Zplus, ?_⟩
  rintro ⟨y, hy⟩ N hN
  have hpy : C.lt ⊤ p y := by simpa using hy
  let O : Opens M := ⟨interior N, isOpen_interior⟩
  have hpO : p ∈ O := mem_interior_iff_mem_nhds.2 hN
  obtain ⟨r, hr, -⟩ :=
    (Precausality.absolutelyMinimal_iff.1 h).exists_lt_inf le_rfl O hpO hpy
  have hrO : r ∈ O := (inf_le_right : ⊤ ⊓ O ≤ O) (C.lt_mem_right hr)
  have hpr : C.lt ⊤ p r := C.lt_mono inf_le_left hr
  exact ⟨r, by simpa using hpr, interior_subset hrO⟩

/-- **`rem:absolutely_minimal_topological_spacetime`**, past. -/
theorem AbsolutelyMinimal.mem_Zminus_iff [T1Space M] (h : C.AbsolutelyMinimal) :
    p ∈ C.Zminus ↔ (C.Iminus ⊤ {p}).Nonempty :=
  AbsolutelyMinimal.mem_Zplus_iff (C := C.dual) (dual_absolutelyMinimal.2 h)

/-! ### `prop:topological_spacetime_absolutely_minimal` -/

/-- **`prop:topological_spacetime_absolutely_minimal`.** An absolutely minimal causality which is
locally open is open. -/
theorem AbsolutelyMinimal.causallyOpenFuture (h : C.AbsolutelyMinimal)
    (hloc : ∀ p : M, ∃ W : Opens M, p ∈ W ∧ C.CausallyOpenFutureOn W) :
    C.CausallyOpenFuture := by
  choose W hW hWopen using hloc
  intro U V _
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, hxy⟩
  have hchain := (Precausality.absolutelyMinimal_iff.1 h).linkLe_of_family W
    (fun x _ => ⟨x, hW x⟩) le_top hxy
  -- every point of the chain has an open neighbourhood inside `J^+_U(V)`
  have key : ∀ y, TransGen (Precausality.LinkLe W (fun _ => C.toPrecausality) U) x y →
      ∃ N : Opens M, y ∈ N ∧ (N : Set M) ⊆ C.Jplus U V := by
    intro y hy
    induction hy with
    | @single b hl =>
      obtain ⟨q, hq⟩ := hl
      have hxin : x ∈ V ⊓ (U ⊓ W q) := ⟨hx, C.le_mem_left hq⟩
      refine ⟨⟨C.Jplus (U ⊓ W q) ((V ⊓ (U ⊓ W q) : Opens M) : Set M),
        hWopen q _ _ inf_le_right inf_le_right⟩, ⟨x, hxin, hq⟩, ?_⟩
      rintro y' ⟨x', hx', hx'y'⟩
      exact ⟨x', hx'.1, C.le_mono inf_le_left hx'y'⟩
    | @tail b c _ hl ih =>
      obtain ⟨N, hbN, hN⟩ := ih
      obtain ⟨q, hq⟩ := hl
      have hbin : b ∈ N ⊓ (U ⊓ W q) := ⟨hbN, C.le_mem_left hq⟩
      refine ⟨⟨C.Jplus (U ⊓ W q) ((N ⊓ (U ⊓ W q) : Opens M) : Set M),
        hWopen q _ _ inf_le_right inf_le_right⟩, ⟨b, hbin, hq⟩, ?_⟩
      rintro y' ⟨z', hz', hz'y'⟩
      obtain ⟨x', hx', hx'z'⟩ := hN hz'.1
      exact ⟨x', hx', C.le_trans hx'z' (C.le_mono inf_le_left hz'y')⟩
  obtain ⟨N, hyN, hN⟩ := key y hchain
  exact mem_of_superset (N.isOpen.mem_nhds hyN) hN

/-- `prop:topological_spacetime_absolutely_minimal`, for two-sided causal openness. -/
theorem AbsolutelyMinimal.causallyOpen (h : C.AbsolutelyMinimal)
    (hloc : ∀ p : M, ∃ W : Opens M, p ∈ W ∧ C.CausallyOpenFutureOn W)
    (hloc' : ∀ p : M, ∃ W : Opens M, p ∈ W ∧ C.dual.CausallyOpenFutureOn W) :
    C.CausallyOpen :=
  causallyOpen_iff.2 ⟨AbsolutelyMinimal.causallyOpenFuture h hloc,
    AbsolutelyMinimal.causallyOpenFuture (C := C.dual) (dual_absolutelyMinimal.2 h) hloc'⟩

/-! ### `lem:cup_cap` -/

/-- **`lem:cup_cap`.** -/
theorem Iminus_subset_interior_and_subset [T1Space M] (h : C.AbsolutelyMinimal) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jplus ⊤ {x})) :
    C.Iminus ⊤ {p} ⊆ interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ∧
      interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ⊆
        interior (C.Jminus ⊤ {p}) ∩ C.Zplus := by
  constructor
  · refine interior_maximal ?_ isOpen_Iminus
    intro x hx
    have hxp : C.lt ⊤ x p := by simpa using hx
    have hev : ∀ᶠ n in atTop, u n ∈ C.Iplus ⊤ {x} :=
      hu.eventually (isOpen_Iplus.mem_nhds (by simpa using hxp))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine mem_iUnion.2 ⟨N, ?_⟩
    simp only [mem_iInter]
    intro n hn
    have : C.lt ⊤ x (u n) := by simpa using hN n hn
    simpa using this
  · -- the set itself is contained in `J^-(p)` and in `Z^+(M)`
    have hsub : (⋃ N : ℕ, ⋂ n ≥ N, C.Iminus ⊤ {u n}) ⊆ C.Jminus ⊤ {p} ∩ C.Zplus := by
      intro x hx
      obtain ⟨N, hN⟩ := mem_iUnion.1 hx
      simp only [mem_iInter] at hN
      have hxu : ∀ n ≥ N, C.lt ⊤ x (u n) := fun n hn => by simpa using hN n hn
      constructor
      · have hev : ∀ᶠ n in atTop, u n ∈ C.Jplus ⊤ {x} :=
          eventually_atTop.2 ⟨N, fun n hn => by simpa using C.le_of_lt (hxu n hn)⟩
        have hp : p ∈ C.Jplus ⊤ {x} := (hJ x).mem_of_tendsto hu hev
        have : C.le ⊤ x p := by simpa using hp
        simpa using this
      · exact (AbsolutelyMinimal.mem_Zplus_iff h).2 ⟨u N, by simpa using hxu N le_rfl⟩
    intro x hx
    exact ⟨interior_mono (hsub.trans inter_subset_left) hx,
      (hsub (interior_subset hx)).2⟩

/-- **`rem:same_notation_one_proves`**: `lem:cup_cap` for the chronological future. -/
theorem Iplus_subset_interior_and_subset [T1Space M] (h : C.AbsolutelyMinimal) {u : ℕ → M}
    (hu : Tendsto u atTop (𝓝 p)) (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) :
    C.Iplus ⊤ {p} ⊆ interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) ∧
      interior (⋃ N : ℕ, ⋂ n ≥ N, C.Iplus ⊤ {u n}) ⊆
        interior (C.Jplus ⊤ {p}) ∩ C.Zminus :=
  Iminus_subset_interior_and_subset (C := C.dual) (dual_absolutelyMinimal.2 h) hu hJ

end Causality

end Causal
