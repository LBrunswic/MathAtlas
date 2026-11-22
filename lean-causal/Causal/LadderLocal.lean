import Causal.ArcConnected
import Causal.Minimal
import Causal.PushUp
import Causal.LinesCurves
import Causal.LinesReachable
import Causal.NestedCausalities

/-!
# Named localisation properties for the causality ladder, and global hyperbolicity split into causal and causally compact

Programme target `T-abs-ladder-local-defs` (`programme/roadmap.toml`; layer 1, no label of
`ETT.tex`; ETT-layer imports only, no model). Each property below was an inline hypothesis of a
witness of `programme/ladder.toml`; it is defined here (namespace `Causal.Causality`), with its
dual and its global ⇒ local lemma, and each witness is restated with it as premise.

* **`T-abs-ladder-local-defs/locally-push-up`** — `LocallyPushUp`; `PushUp.locallyPushUp`;
  `CausallyArcConnected.pushUp_of_locallyPushUp` (`lem:pushup_local`, `ETT.tex:557`, the `under`
  of `causally_arc_connected ⇒ push_up`).
* **`T-abs-ladder-local-defs/locally-causally-open-future`** — `LocallyCausallyOpenFuture`;
  `CausallyOpenFuture.locallyCausallyOpenFuture`;
  `AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture`
  (`prop:topological_spacetime_absolutely_minimal`, `ETT.tex:698`, as printed).
* **`T-abs-ladder-local-defs/locally-causally-open`** — `LocallyCausallyOpen`;
  `CausallyOpen.locallyCausallyOpen`; `AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen`
  (the same, DEC-8 reading).
* **`T-abs-ladder-local-defs/chronal-neighbours`** — `ChronalPastNeighbours`,
  `ChronalNeighbours`; `PushUp.causallyOpen_of_chronalNeighbours`, a re-proof of
  `Causal.Causality.causallyOpen_of_pushUp` (`Causal.LemmaK`, ETT-layer since T-abs-hoist-lemma-k; the re-proof
  predates it).
* **`T-abs-ladder-local-defs/no-causal-endpoint`** — `NoPastEndpoint`, `NoCausalEndpoint`
  (`J^±(x) ≠ {x}`, `theo:geroch`, `ETT.tex:1259`);
  `GloballyHyperbolic.inextensibleNestedOn_top_of_noCausalEndpoint`,
  `inextensibleNestedOn_top_of_noCausalEndpoint` (`Causal.NestedCausalities`).
* **`T-abs-ladder-local-defs/one-sided-boundary`** — `OneSidedAt`, `OneSidedBoundary` (the
  topological content of ERS 1802.03020 (4.83)); `ers_theorem_4_82_of_oneSidedBoundary`.
* **`T-abs-ladder-local-defs/gh-causal`** — `GloballyHyperbolic.isCausal`,
  `GloballyHyperbolic.causallyCompact`, `globallyHyperbolic_iff`, `IsCausal.globallyHyperbolic`
  (`def:globally_hyperbolic`, `ETT.tex:995`; `def:causally_compact`, `ETT.tex:350`).

> Let $M$ be a causally arc-connected topological spacetime and let $(\U_i)_{i\in I}$ be a cover
> of $M$ by open subsets each having the push-up property. Then $M$ has the push-up property.
> (`lem:pushup_local`, `ETT.tex:557`)

> If $M$ is absolutely minimal and if for every $p\in M$ there exists a neighbourhood $\U$ of $p$
> whose causality is open, then the causality of $M$ is open.
> (`prop:topological_spacetime_absolutely_minimal`, `ETT.tex:698`)

> Assume moreover that $M$ is tarentin, causally arc-connected and locally causally convex, and
> that $J^\pm(p)\neq \{p\}$ for every $p\in M$. (`theo:geroch`, `ETT.tex:1258`)

> $M$ is globally hyperbolic if $M$ is causal and if $J_M(p,q)$ is compact for all $p,q\in M$.
> (`def:globally_hyperbolic`, `ETT.tex:995`) — $M$ is causally compact if the diamond $J(p,q)$
> is compact for all $p,q\in M$. (`def:causally_compact`, `ETT.tex:350`)

> for every p ∈ (∂U1 \ ∂S) there exists a neighbourhood V of p together with a chart
> ψ : V → (−ε, ε)^{d+1}, ε > 0, and a continuous function f : (−ε, ε)^d → (−ε, ε) such that
> ψ⁻¹(graph f) = ∂U1 ∩ V, all points below graph f in (−ε, ε)^{d+1} are mapped into U1 and all
> points above graph f in (−ε, ε)^{d+1} are mapped into R^{d+1} \ U1. (4.83)
> (`references/sbierski/text/eperon2018predictability.txt:2029–2033`)

The chronal-neighbours hypothesis (`under` of `push_up ⇒ causally_open`) has no paper sentence:
it is `hZm`/`hZp` of `causallyOpen_of_pushUp` (Lemma K, DEC-93).

## Hypothesis checklist

Each restated witness carries exactly the hypotheses of the original, the inline one replaced by
the named property, which is that hypothesis (definitionally, or up to `choose` for the cover of
`lem:pushup_local`, `locallyPushUp_of_cover`):

| inline hypothesis | here |
|---|---|
| `hcover`, `hO` of `CausallyArcConnected.pushUp` (a cover by `PushUpOn` opens) | ✓ `LocallyPushUp` (equivalent: `locallyPushUp_of_cover`, `choose`) |
| `hloc` of `AbsolutelyMinimal.causallyOpenFuture` | ✓ `LocallyCausallyOpenFuture`, definitionally |
| `hloc`, `hloc'` of `AbsolutelyMinimal.causallyOpen` | ✓ `LocallyCausallyOpen`, definitionally; one neighbourhood for both sides is equivalent (`locallyCausallyOpen_iff`) |
| `hZm`, `hZp` of `causallyOpen_of_pushUp` | ✓ `ChronalNeighbours`, definitionally (`.1` past, `.2` future) |
| `hpast`, `hfut` of `inextensibleNestedOn_top` and its GH form; `hJm`, `hJp` passim | ✓ `NoCausalEndpoint`, definitionally (`.1` past, `.2` future) |
| `honesided` of `ers_theorem_4_82` | ✓ `OneSidedBoundary (dom i₁) (closure S)`, definitionally |

## SCOPE (disclosed)

* **The past is the base of the one-sided chronal and endpoint notions** (`ChronalPastNeighbours`,
  `NoPastEndpoint`; the future ones are `C.dual.…`), unlike `CausallyOpenFuture`: the witnesses
  take the past hypothesis first, and past neighbours give *future* causal openness
  (`PushUp.causallyOpenFuture_of_chronalPastNeighbours`), so the future theorem is the base one
  (kb/0002).
* **"Local" is "every point has an open neighbourhood with the property"**, the form the
  witnesses use. For push-up and future causal openness, which pass to smaller opens
  (`PushUpOn.mono`, `CausallyOpenFutureOn.mono`), it is equivalent to the arbitrarily-small form
  of `LocallyCausallyArcConnected` (`locallyPushUp_iff_nhds`,
  `locallyCausallyOpenFuture_iff_nhds`).
* **`ChronalNeighbours` asks chronology inside each open `V`**, not in `M`. It makes every point
  strongly tarentin (`ChronalPastNeighbours.mem_Zminus`, `ChronalNeighbours.mem_Zplus`); under
  absolute minimality on a `T1` space it is exactly "`I^±(x) ≠ ∅` for every `x`"
  (`AbsolutelyMinimal.chronalPastNeighbours_iff`). It is not `HasChronalNeighbour` of the
  `Causal.LocateExtension` (one point, one side, chronology in `M`).
* **`OneSidedBoundary` is (4.83)'s topological content, not the chart condition**: `U` meets
  arbitrarily small neighbourhoods of each boundary point off `B` in a preconnected set, the
  form `ers_theorem_4_82` uses (its docstring: shrink the box so that each vertical fibre below
  the graph is an interval). It involves no causality: a property of an open set, not of `C`.
  Witnesses on `ℝ`: `(0, ∞)` has it at `0` (`oneSidedBoundary_Ioi_zero`), `ℝ ∖ {0}` has not
  (`not_oneSidedBoundary_compl_zero`).
* **`HasTimeFunction.isCausal` is not here**: it is in `Causal.CurvesExtend` since
  T-abs-hoist-time-function, which moved `Causal.Causality.HasTimeFunction` there out of the
  model-importing `Causal.CBG.Pgcd`.
* **Not restated: the witnesses of the model-importing `Causal.ChainsCurves`** —
  `Inextensible.not_forall_le_of_causallyCompact`, whose `hJm`, `hJp` are `NoCausalEndpoint`. Lemma K
  (`Causal.LemmaK`) is ETT-layer since T-abs-hoist-lemma-k; `causallyOpen_of_pushUp` was re-proved
  here before that (four lines, the same proof), a duplicate that can now cite the original.
* **Non-vacuity and separations**: the timelike line has every new property
  (`timelikeLine_locallyPushUp`, `timelikeLine_chronalNeighbours`,
  `timelikeLine_locallyCausallyOpen`, `timelikeLine_noCausalEndpoint`) and the restated witnesses
  apply to it (`timelikeLine_causallyOpen_of_chronalNeighbours`,
  `timelikeLine_inextensibleNestedOn_top_of_noCausalEndpoint`); the lightlike line has push-up,
  causal openness, global hyperbolicity and no causal endpoint, but no chronal neighbours
  (`lightlikeLine_separates_chronalNeighbours`); the spacelike line has push-up, causal openness
  and global hyperbolicity, but every point is a causal endpoint
  (`spacelikeLine_separates_noCausalEndpoint`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

/-! ## The definitions -/

section Defs

variable (C : Causality M)

/-- **Local push-up** (ladder `locally_push_up`): every point has an open neighbourhood `W` having
push-up as a spacetime (`PushUpOn W`). The side condition of `lem:pushup_local`
(`CausallyArcConnected.pushUp`), whose cover `(O i)` is this up to `choose`. -/
def LocallyPushUp : Prop := ∀ x : M, ∃ W : Opens M, x ∈ W ∧ C.PushUpOn W

/-- **Local causal openness in the future** (ladder `locally_causally_open_future`): every point
has an open neighbourhood `W` whose causality is open in the sense of
`def:causally_open_spacetime_open` as printed (`CausallyOpenFutureOn W`). The hypothesis of
`prop:topological_spacetime_absolutely_minimal`. -/
def LocallyCausallyOpenFuture : Prop :=
  ∀ x : M, ∃ W : Opens M, x ∈ W ∧ C.CausallyOpenFutureOn W

/-- **Local causal openness** (ladder `locally_causally_open`), two-sided as `CausallyOpen`
(DEC-8): local causal openness in the future and in the past. Equivalently, one open
neighbourhood serves both (`locallyCausallyOpen_iff`). -/
def LocallyCausallyOpen : Prop :=
  C.LocallyCausallyOpenFuture ∧ C.dual.LocallyCausallyOpenFuture

/-- **Chronal past neighbours in every open set**: every point `v` of every open `V` has a point
`p ∈ V` with `p ≪_V v`, chronology taken in `V`. Past neighbours give causal openness in the
future, under push-up (`PushUp.causallyOpenFuture_of_chronalPastNeighbours`). -/
def ChronalPastNeighbours : Prop := ∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V p v

/-- **Chronal neighbours in every open set** (ladder `chronal_neighbours`): every point `v` of
every open `V` has `p, p' ∈ V` with `p ≪_V v ≪_V p'`. The `under` of `push_up ⇒ causally_open`
(`hZm`, `hZp` of `causallyOpen_of_pushUp`, `Causal.LemmaK`). -/
def ChronalNeighbours : Prop := C.ChronalPastNeighbours ∧ C.dual.ChronalPastNeighbours

/-- **No past endpoint**: `J⁻(x) ≠ {x}` for every `x`, i.e. every point has a causal past point
other than itself (`noPastEndpoint_iff`). -/
def NoPastEndpoint : Prop := ∀ x : M, C.Jminus ⊤ {x} ≠ {x}

/-- **No causal endpoint** (ladder `no_causal_endpoint`): `J^±(x) ≠ {x}` for every `x`, a
hypothesis of `theo:geroch` (`ETT.tex:1259`), of Lemma K, and of the inextensible nesting on `M`
(`GloballyHyperbolic.inextensibleNestedOn_top`). -/
def NoCausalEndpoint : Prop := C.NoPastEndpoint ∧ C.dual.NoPastEndpoint

end Defs

/-- `U` is **one-sided at** `p`: every neighbourhood of `p` contains a neighbourhood `V` of `p`
with `V ∩ U` preconnected. Pure topology. At a boundary point of an open `U` lying below the graph
of a continuous function in a chart (ERS (4.83)) it holds — shrink the box so that each vertical
fibre of `V ∩ U` is a non-empty interval — but that step needs the chart and is not formalised
here (layer 3). -/
def OneSidedAt (U : Set M) (p : M) : Prop :=
  ∀ N ∈ 𝓝 p, ∃ V ∈ 𝓝 p, V ⊆ N ∧ IsPreconnected (V ∩ U)

/-- **One-sided boundary off `B`** (proposed ladder `one_sided_boundary`): `U` is one-sided at
each of its boundary points outside `B`. With `B = closure S` it is `honesided` of
`ers_theorem_4_82`, the topological content of ERS 1802.03020 (4.83). ERS's `∂U₁ ∖ ∂S` is
`frontier U₁ ∖ closure S` whether `∂S` is read as the frontier of the hypersurface `S` in
`ℝ^{d+1}` (`closure S`) or as its edge (`closure S ∖ S`): `S ⊆ U₁` misses `frontier U₁`, `U₁`
being open. No causality is involved. -/
def OneSidedBoundary (U : Opens M) (B : Set M) : Prop :=
  ∀ p ∈ frontier (U : Set M) \ B, OneSidedAt (U : Set M) p

variable {C : Causality M} {W W' : Opens M} {x : M}

/-! ## Local push-up -/

/-- Push-up of an open set passes to its open subsets. -/
theorem PushUpOn.mono (h : C.PushUpOn W) (hW : W' ≤ W) : C.PushUpOn W' :=
  fun U hU => h U (hU.trans hW)

theorem dual_locallyPushUp : C.dual.LocallyPushUp ↔ C.LocallyPushUp :=
  ⟨fun h x => let ⟨W, hx, hW⟩ := h x; ⟨W, hx, dual_pushUpOn.1 hW⟩,
    fun h x => let ⟨W, hx, hW⟩ := h x; ⟨W, hx, dual_pushUpOn.2 hW⟩⟩

/-- The hypothesis of `lem:pushup_local` as written, a cover by opens with push-up, is local
push-up (the converse is `choose`, in `CausallyArcConnected.pushUp_of_locallyPushUp`). -/
theorem locallyPushUp_of_cover {ι : Sort*} {O : ι → Opens M} (hcover : ∀ x : M, ∃ i, x ∈ O i)
    (hO : ∀ i, C.PushUpOn (O i)) : C.LocallyPushUp :=
  fun x => let ⟨i, hi⟩ := hcover x; ⟨O i, hi, hO i⟩

/-- Local push-up holds on arbitrarily small open neighbourhoods (the form of
`LocallyCausallyArcConnected`). -/
theorem locallyPushUp_iff_nhds : C.LocallyPushUp ↔
    ∀ x : M, ∀ N ∈ 𝓝 x, ∃ W : Opens M, x ∈ W ∧ (W : Set M) ⊆ N ∧ C.PushUpOn W := by
  constructor
  · intro h x N hN
    obtain ⟨W, hxW, hW⟩ := h x
    refine ⟨W ⊓ ⟨interior N, isOpen_interior⟩, ⟨hxW, mem_interior_iff_mem_nhds.2 hN⟩,
      fun y hy => interior_subset hy.2, PushUpOn.mono hW inf_le_left⟩
  · intro h x
    obtain ⟨W, hxW, -, hW⟩ := h x univ univ_mem
    exact ⟨W, hxW, hW⟩

/-- **Push-up is local push-up** (`push_up ⇒ locally_push_up`). -/
theorem PushUp.locallyPushUp (h : C.PushUp) : C.LocallyPushUp :=
  fun _ => ⟨⊤, trivial, pushUpOn_top.2 h⟩

/-- **`lem:pushup_local`, the side condition named** (`causally_arc_connected ∧ locally_push_up ⇒
push_up`): a causally arc-connected spacetime with local push-up has push-up. Corollary of
`CausallyArcConnected.pushUp`. -/
theorem CausallyArcConnected.pushUp_of_locallyPushUp (h : C.CausallyArcConnected)
    (hloc : C.LocallyPushUp) : C.PushUp := by
  choose W hW hWp using hloc
  exact CausallyArcConnected.pushUp h (O := W) (fun x => ⟨x, hW x⟩) hWp

/-! ## Local causal openness -/

/-- Causal openness in the future of an open set passes to its open subsets. -/
theorem CausallyOpenFutureOn.mono (h : C.CausallyOpenFutureOn W) (hW : W' ≤ W) :
    C.CausallyOpenFutureOn W' :=
  fun U V hU hVU => h U V (hU.trans hW) hVU

/-- Local causal openness in the future holds on arbitrarily small open neighbourhoods. -/
theorem locallyCausallyOpenFuture_iff_nhds : C.LocallyCausallyOpenFuture ↔
    ∀ x : M, ∀ N ∈ 𝓝 x, ∃ W : Opens M, x ∈ W ∧ (W : Set M) ⊆ N ∧ C.CausallyOpenFutureOn W := by
  constructor
  · intro h x N hN
    obtain ⟨W, hxW, hW⟩ := h x
    refine ⟨W ⊓ ⟨interior N, isOpen_interior⟩, ⟨hxW, mem_interior_iff_mem_nhds.2 hN⟩,
      fun y hy => interior_subset hy.2, CausallyOpenFutureOn.mono hW inf_le_left⟩
  · intro h x
    obtain ⟨W, hxW, -, hW⟩ := h x univ univ_mem
    exact ⟨W, hxW, hW⟩

/-- **Causal openness in the future is local** (`causally_open_future ⇒
locally_causally_open_future`). -/
theorem CausallyOpenFuture.locallyCausallyOpenFuture (h : C.CausallyOpenFuture) :
    C.LocallyCausallyOpenFuture :=
  fun _ => ⟨⊤, trivial, causallyOpenFutureOn_top.2 h⟩

/-- **`prop:topological_spacetime_absolutely_minimal`, the side condition named**
(`absolutely_minimal ∧ locally_causally_open_future ⇒ causally_open_future`). Corollary of
`AbsolutelyMinimal.causallyOpenFuture`. -/
theorem AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture
    (h : C.AbsolutelyMinimal) (hloc : C.LocallyCausallyOpenFuture) : C.CausallyOpenFuture :=
  AbsolutelyMinimal.causallyOpenFuture h hloc

theorem dual_locallyCausallyOpen : C.dual.LocallyCausallyOpen ↔ C.LocallyCausallyOpen :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `locally_causally_open ⇒ locally_causally_open_future`. -/
theorem LocallyCausallyOpen.future (h : C.LocallyCausallyOpen) : C.LocallyCausallyOpenFuture :=
  h.1

/-- Local two-sided causal openness with one neighbourhood for both time directions. -/
theorem locallyCausallyOpen_iff : C.LocallyCausallyOpen ↔
    ∀ x : M, ∃ W : Opens M, x ∈ W ∧ C.CausallyOpenFutureOn W ∧ C.dual.CausallyOpenFutureOn W := by
  constructor
  · rintro ⟨hf, hp⟩ x
    obtain ⟨W₁, hx₁, h₁⟩ := hf x
    obtain ⟨W₂, hx₂, h₂⟩ := hp x
    exact ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, CausallyOpenFutureOn.mono h₁ inf_le_left,
      CausallyOpenFutureOn.mono (C := C.dual) h₂ inf_le_right⟩
  · intro h
    exact ⟨fun x => let ⟨W, hx, hW, _⟩ := h x; ⟨W, hx, hW⟩,
      fun x => let ⟨W, hx, _, hW⟩ := h x; ⟨W, hx, hW⟩⟩

/-- **Causal openness is local** (`causally_open ⇒ locally_causally_open`). -/
theorem CausallyOpen.locallyCausallyOpen (h : C.CausallyOpen) : C.LocallyCausallyOpen :=
  ⟨CausallyOpenFuture.locallyCausallyOpenFuture h.future,
    CausallyOpenFuture.locallyCausallyOpenFuture (C := C.dual) (dual_causallyOpen.2 h).future⟩

/-- **`prop:topological_spacetime_absolutely_minimal` in the DEC-8 reading, the side condition
named** (`absolutely_minimal ∧ locally_causally_open ⇒ causally_open`). Corollary of
`AbsolutelyMinimal.causallyOpen`. -/
theorem AbsolutelyMinimal.causallyOpen_of_locallyCausallyOpen (h : C.AbsolutelyMinimal)
    (hloc : C.LocallyCausallyOpen) : C.CausallyOpen :=
  AbsolutelyMinimal.causallyOpen h hloc.1 hloc.2

/-! ## Chronal neighbours -/

theorem dual_chronalNeighbours : C.dual.ChronalNeighbours ↔ C.ChronalNeighbours :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- With chronal past neighbours, every point is strongly tarentin in the past. -/
theorem ChronalPastNeighbours.mem_Zminus (h : C.ChronalPastNeighbours) (x : M) :
    x ∈ C.Zminus := by
  intro N hN
  obtain ⟨p, hpV, hpx⟩ := h ⟨interior N, isOpen_interior⟩ x (mem_interior_iff_mem_nhds.2 hN)
  exact ⟨p, by simpa using C.lt_mono le_top hpx, interior_subset hpV⟩

/-- With chronal neighbours, every point is strongly tarentin in the future. -/
theorem ChronalNeighbours.mem_Zplus (h : C.ChronalNeighbours) (x : M) : x ∈ C.Zplus :=
  ChronalPastNeighbours.mem_Zminus (C := C.dual) h.2 x

/-- Under absolute minimality on a `T1` space, chronal past neighbours in every open set are just
a non-empty chronological past at every point (localisation by
`Precausality.AbsolutelyMinimalOn.exists_lt_inf`). -/
theorem AbsolutelyMinimal.chronalPastNeighbours_iff [T1Space M] (h : C.AbsolutelyMinimal) :
    C.ChronalPastNeighbours ↔ ∀ x : M, (C.Iminus ⊤ {x}).Nonempty := by
  constructor
  · intro hN x
    obtain ⟨p, -, hp⟩ := hN ⊤ x trivial
    exact ⟨p, by simpa using hp⟩
  · intro hI V v hv
    obtain ⟨y, hy⟩ := hI v
    have hvy : C.dual.lt ⊤ v y := by simpa using hy
    have hmin : C.dual.toPrecausality.AbsolutelyMinimalOn ⊤ :=
      Precausality.absolutelyMinimal_iff.1 (dual_absolutelyMinimal.2 h)
    obtain ⟨r, hvr, -⟩ := hmin.exists_lt_inf le_rfl V hv hvy
    have hrv : C.lt (⊤ ⊓ V) r v := hvr
    exact ⟨r, (inf_le_right : ⊤ ⊓ V ≤ V) (C.lt_mem_left hrv), C.lt_mono inf_le_right hrv⟩

/-- **Causal openness in the future from push-up and chronal past neighbours** (`push_up ∧
chronal_past_neighbours ⇒ causally_open_future`). The proof of `causallyOpenFuture_of_pushUp`
(`Causal.LemmaK`, ETT-layer since T-abs-hoist-lemma-k): `J^+_U(V)` contains `I^+_U(p)`, an open neighbourhood of
each of its points `x`, where `p ≪_V v ≤_U x`. -/
theorem PushUp.causallyOpenFuture_of_chronalPastNeighbours (h : C.PushUp)
    (hN : C.ChronalPastNeighbours) : C.CausallyOpenFuture := by
  intro U V hVU
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨v, hv, hvx⟩
  obtain ⟨p, hpV, hpv⟩ := hN V v hv
  exact mem_of_superset ((C.isOpen_lt_right U p).mem_nhds
    (h.lt_of_lt_of_le (C.lt_mono hVU hpv) hvx)) fun w hw => ⟨p, hpV, C.le_of_lt hw⟩

/-- **Causal openness from push-up, the side condition named** (`push_up ∧ chronal_neighbours ⇒
causally_open`). Re-proof of `causallyOpen_of_pushUp` (`Causal.LemmaK`, not importable in layer 1)
with `ChronalNeighbours` for `hZm`, `hZp`. -/
theorem PushUp.causallyOpen_of_chronalNeighbours (h : C.PushUp) (hN : C.ChronalNeighbours) :
    C.CausallyOpen :=
  ⟨PushUp.causallyOpenFuture_of_chronalPastNeighbours h hN.1,
    PushUp.causallyOpenFuture_of_chronalPastNeighbours (C := C.dual) (dual_pushUp.2 h) hN.2⟩

/-! ## No causal endpoint -/

/-- No past endpoint: every point has a causal past point other than itself. -/
theorem noPastEndpoint_iff : C.NoPastEndpoint ↔ ∀ x : M, ∃ y, y ≠ x ∧ C.le ⊤ y x := by
  constructor
  · intro h x
    by_contra hne
    push Not at hne
    refine h x (Set.ext fun y => ?_)
    rw [Precausality.mem_Jminus_singleton, mem_singleton_iff]
    exact ⟨fun hy => by_contra fun hyx => hne y hyx hy, fun hy => hy ▸ C.le_refl trivial⟩
  · intro h x hx
    obtain ⟨y, hyx, hy⟩ := h x
    have hyJ : y ∈ C.Jminus ⊤ {x} := by simpa using hy
    rw [hx] at hyJ
    exact hyx hyJ

theorem dual_noCausalEndpoint : C.dual.NoCausalEndpoint ↔ C.NoCausalEndpoint :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Inextensibility is nested on `M`**, the endpoint hypotheses named. Corollary of
`inextensibleNestedOn_top`. -/
theorem inextensibleNestedOn_top_of_noCausalEndpoint {C' : Causality M}
    (hnest : CurveNestedOn C C' ⊤) (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hSC : C.StronglyCausal) (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hE : C.NoCausalEndpoint) :
    InextensibleNestedOn C C' ⊤ :=
  inextensibleNestedOn_top hnest hC hcaus hSC hJp hJm hE.1 hE.2

/-- **Inextensibility is nested on `M`**, from global hyperbolicity (Hausdorff, tarentin, causally
arc-connected) and no causal endpoint. Corollary of `GloballyHyperbolic.inextensibleNestedOn_top`.
-/
theorem GloballyHyperbolic.inextensibleNestedOn_top_of_noCausalEndpoint [T2Space M]
    {C' : Causality M} (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hE : C.NoCausalEndpoint) (hnest : CurveNestedOn C C' ⊤) :
    InextensibleNestedOn C C' ⊤ :=
  GloballyHyperbolic.inextensibleNestedOn_top hT hG hC hE.1 hE.2 hnest

/-! ## One-sided boundary -/

/-- **ERS19 Theorem 4.82, causal-topological skeleton, (4.83) named** (`OneSidedBoundary (dom i₁)
(closure S)` for `honesided`). Corollary of `ers_theorem_4_82`; every other hypothesis is that
theorem's, documented there. -/
theorem ers_theorem_4_82_of_oneSidedBoundary [T2Space M] [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {S : Set M} {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hcaus : ∀ i ⦃x y : M⦄, (cau i).le (dom i) x y → (cau i).le (dom i) y x → x = y)
    (hsplit : ∀ i, ∀ q ∈ dom i, q ∈ (cau i).Jplus (dom i) S ∪ (cau i).Jminus (dom i) S)
    (hJm : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jminus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jminus (dom i) {x})
    (hJp : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jplus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jplus (dom i) {x})
    (hKm : ∀ i q, IsCompact ((cau i).Jminus (dom i) {q} ∩ (cau i).Jplus (dom i) S))
    (hKp : ∀ i q, IsCompact ((cau i).Jplus (dom i) {q} ∩ (cau i).Jminus (dom i) S))
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : OneSidedBoundary (dom i₁) (closure S))
    (hstep : ∀ i, ∀ p ∈ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) ∩ dom i,
      ((cau i).Jminus (dom i) {p} ∩ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀)
          ∩ (cau i).Jplus (dom i) S = {p} ∨
        (cau i).Jplus (dom i) {p} ∩ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀)
          ∩ (cau i).Jminus (dom i) S = {p}) →
      (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
      ∃ j, dom i₁ < dom j) :
    ∀ i, dom i ≤ dom i₁ :=
  ers_theorem_4_82 dom cau hs₀ i₁ hSU hmax hconn hcaus hsplit hJm hJp hKm hKp hSclosed honesided
    hstep

/-! ## Global hyperbolicity: causal and causally compact -/

/-- **A globally hyperbolic spacetime is causal** (`globally_hyperbolic ⇒ is_causal`), with no
tarentin hypothesis: `def:globally_hyperbolic` asks it. -/
theorem GloballyHyperbolic.isCausal (h : C.GloballyHyperbolic) : C.IsCausal :=
  h.1

/-- **A globally hyperbolic spacetime is causally compact** (`globally_hyperbolic ⇒
causally_compact`). -/
theorem GloballyHyperbolic.causallyCompact (h : C.GloballyHyperbolic) : C.CausallyCompact :=
  h.2

/-- `def:globally_hyperbolic` is `def:causal_spacetime` and `def:causally_compact`. -/
theorem globallyHyperbolic_iff : C.GloballyHyperbolic ↔ C.IsCausal ∧ C.CausallyCompact :=
  Iff.rfl

/-- **Causal and causally compact is globally hyperbolic** (`is_causal ∧ causally_compact ⇒
globally_hyperbolic`). -/
theorem IsCausal.globallyHyperbolic (h : C.IsCausal) (hK : C.CausallyCompact) :
    C.GloballyHyperbolic :=
  ⟨h, hK⟩

theorem dual_causallyCompact : C.dual.CausallyCompact ↔ C.CausallyCompact := by
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := h b a
    rwa [dual_diamond] at this
  · rw [dual_diamond]
    exact h b a

end Causality

/-! ## Witnesses -/

/-- The timelike line has local push-up. -/
theorem timelikeLine_locallyPushUp : timelikeLine.LocallyPushUp :=
  timelikeLine_pushUp.locallyPushUp

/-- The timelike line has chronal neighbours in every open set. -/
theorem timelikeLine_chronalNeighbours : timelikeLine.ChronalNeighbours := by
  refine ⟨fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    refine ⟨v - ε / 2, hball ?_, show v - ε / 2 < v ∧ _ from ⟨by linarith, fun z hz => hball ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2]
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    refine ⟨v + ε / 2, hball ?_, show v < v + ε / 2 ∧ _ from ⟨by linarith, fun z hz => hball ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2]

/-- `PushUp.causallyOpen_of_chronalNeighbours` applies to the timelike line: its hypotheses are
satisfiable. -/
theorem timelikeLine_causallyOpen_of_chronalNeighbours : timelikeLine.CausallyOpen :=
  timelikeLine_pushUp.causallyOpen_of_chronalNeighbours timelikeLine_chronalNeighbours

/-- The timelike line is locally causally open. -/
theorem timelikeLine_locallyCausallyOpen : timelikeLine.LocallyCausallyOpen :=
  timelikeLine_causallyOpen_of_chronalNeighbours.locallyCausallyOpen

/-- The timelike line has no causal endpoint. -/
theorem timelikeLine_noCausalEndpoint : timelikeLine.NoCausalEndpoint :=
  ⟨timelikeLine_Jminus_ne, timelikeLine_Jplus_ne⟩

/-- `GloballyHyperbolic.inextensibleNestedOn_top_of_noCausalEndpoint` applies to the timelike line
nested in itself: its hypotheses are satisfiable. -/
theorem timelikeLine_inextensibleNestedOn_top_of_noCausalEndpoint :
    Causality.InextensibleNestedOn timelikeLine timelikeLine ⊤ :=
  Causality.GloballyHyperbolic.inextensibleNestedOn_top_of_noCausalEndpoint timelikeLine_tarentin
    timelikeLine_globallyHyperbolic timelikeLine_causallyArcConnected timelikeLine_noCausalEndpoint
    ((Causality.LeNested.refl _).curveNestedOn ⊤)

/-- `(0, ∞)` has a one-sided boundary in `ℝ`. -/
theorem oneSidedBoundary_Ioi_zero :
    Causality.OneSidedBoundary (⟨Ioi (0 : ℝ), isOpen_Ioi⟩ : Opens ℝ) ∅ := by
  intro p hp
  have hp0 : p = 0 := by
    have : p ∈ frontier (Ioi (0 : ℝ)) := hp.1
    rwa [frontier_Ioi, mem_singleton_iff] at this
  subst hp0
  intro N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, hball, ?_⟩
  show IsPreconnected (Metric.ball (0 : ℝ) ε ∩ Ioi 0)
  rw [Real.ball_eq_Ioo]
  exact isPreconnected_iff_ordConnected.2 inferInstance

/-- `ℝ ∖ {0}` has not: every small neighbourhood of `0` meets it in two pieces. `OneSidedBoundary`
is not automatic. -/
theorem not_oneSidedBoundary_compl_zero :
    ¬ Causality.OneSidedBoundary (⟨{(0 : ℝ)}ᶜ, isOpen_compl_singleton⟩ : Opens ℝ) ∅ := by
  intro h
  have h0 : (0 : ℝ) ∈ frontier (({0}ᶜ : Set ℝ)) \ ∅ := by
    refine ⟨?_, notMem_empty 0⟩
    rw [frontier_compl, frontier, closure_singleton, interior_singleton, sdiff_empty]
    exact mem_singleton 0
  obtain ⟨V, hV, -, hconn⟩ := h 0 h0 univ univ_mem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hmem : ∀ t : ℝ, t ≠ 0 → |t| < ε → t ∈ V ∩ ({0}ᶜ : Set ℝ) := fun t ht htε =>
    ⟨hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact htε), ht⟩
  have hl := hmem (-(ε / 2)) (by linarith) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have hr := hmem (ε / 2) (by linarith) (by rw [abs_of_pos (by linarith)]; linarith)
  have h0' : (0 : ℝ) ∈ V ∩ ({0}ᶜ : Set ℝ) :=
    hconn.Icc_subset hl hr ⟨by linarith, by linarith⟩
  exact h0'.2 (mem_singleton 0)

/-! ### Separations: the new nodes are not consequences of the old ones -/

/-- The lightlike line has no causal endpoint. -/
theorem lightlikeLine_noCausalEndpoint : lightlikeLine.NoCausalEndpoint :=
  ⟨Causality.noPastEndpoint_iff.2 fun p =>
      ⟨p - 1, (sub_one_lt p).ne, show p - 1 ≤ p ∧ _ from ⟨by linarith, fun _ _ => trivial⟩⟩,
    Causality.noPastEndpoint_iff.2 fun p =>
      ⟨p + 1, (lt_add_one p).ne', show p ≤ p + 1 ∧ _ from ⟨by linarith, fun _ _ => trivial⟩⟩⟩

/-- The lightlike line has no chronal neighbours: its chronological relation is empty. -/
theorem lightlikeLine_not_chronalNeighbours : ¬ lightlikeLine.ChronalNeighbours := fun h =>
  let ⟨_, _, hp⟩ := h.1 ⊤ 0 trivial
  hp

/-- The lightlike line is causally open: its causal relation is that of the timelike line. -/
theorem lightlikeLine_causallyOpen : lightlikeLine.CausallyOpen :=
  timelikeLine_causallyOpen_of_chronalNeighbours

/-- The lightlike line is globally hyperbolic: its causal relation is that of the timelike line. -/
theorem lightlikeLine_globallyHyperbolic : lightlikeLine.GloballyHyperbolic :=
  timelikeLine_globallyHyperbolic

/-- The spacelike line (`≤` the diagonal) is globally hyperbolic. -/
theorem spacelikeLine_globallyHyperbolic : spacelikeLine.GloballyHyperbolic := by
  refine ⟨spacelikeLine_isCausal, fun p q => ?_⟩
  refine ((subsingleton_singleton (a := p)).anti fun x hx => ?_).isCompact
  exact (Causality.mem_diamond.1 hx).1.1.symm

/-- Every point of the spacelike line is a causal endpoint. -/
theorem spacelikeLine_not_noCausalEndpoint : ¬ spacelikeLine.NoCausalEndpoint := by
  intro h
  obtain ⟨y, hy, hle⟩ := Causality.noPastEndpoint_iff.1 h.1 0
  exact hy hle.1

/-- The spacelike line is causally open: `J^±_U(V) = V`. -/
theorem spacelikeLine_causallyOpen : spacelikeLine.CausallyOpen := by
  refine ⟨fun U V hVU => ?_, fun U V hVU => ?_⟩
  · have h : spacelikeLine.Jplus U V = V := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl, -⟩
        exact hx
      · intro hy
        exact ⟨y, hy, rfl, hVU hy⟩
    rw [h]
    exact V.isOpen
  · have h : spacelikeLine.Jminus U V = V := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl, -⟩
        exact hx
      · intro hy
        exact ⟨y, hy, rfl, hVU hy⟩
    rw [h]
    exact V.isOpen

/-- **Chronal neighbours are not implied** by push-up, causal openness, global hyperbolicity and
the absence of causal endpoints together: the lightlike line. -/
theorem lightlikeLine_separates_chronalNeighbours :
    lightlikeLine.PushUp ∧ lightlikeLine.CausallyOpen ∧ lightlikeLine.GloballyHyperbolic ∧
      lightlikeLine.NoCausalEndpoint ∧ ¬ lightlikeLine.ChronalNeighbours :=
  ⟨lightlikeLine_pushUp, lightlikeLine_causallyOpen, lightlikeLine_globallyHyperbolic,
    lightlikeLine_noCausalEndpoint, lightlikeLine_not_chronalNeighbours⟩

/-- **The absence of causal endpoints is not implied** by push-up, causal openness and global
hyperbolicity together: the spacelike line. -/
theorem spacelikeLine_separates_noCausalEndpoint :
    spacelikeLine.PushUp ∧ spacelikeLine.CausallyOpen ∧ spacelikeLine.GloballyHyperbolic ∧
      ¬ spacelikeLine.NoCausalEndpoint :=
  ⟨spacelikeLine_pushUp, spacelikeLine_causallyOpen, spacelikeLine_globallyHyperbolic,
    spacelikeLine_not_noCausalEndpoint⟩

end Causal
