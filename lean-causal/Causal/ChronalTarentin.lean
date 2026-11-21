import Causal.ChronalNeighbourBridge

/-!
# Chronal neighbours give the tarentin property, and so does chronology at strongly tarentin points

Programme target `T-abs-chronal-neighbours-tarentin` (`programme/roadmap.toml:767`; layer 1, no
label of `ETT.tex`; ETT-layer imports only, no model, no metric notion).

**`T-abs-chronal-neighbours-tarentin/1-edge`** — `Causality.ChronalNeighbours.tarentin`, the edge
`chronal_neighbours ⇒ tarentin`, with no separation or countability hypothesis; the keeper's
argument as stated, `Causality.ChronalNeighbours.exists_lt_lt`; its contrapositive
`Causality.not_chronalNeighbours_of_not_tarentin`.
**`T-abs-chronal-neighbours-tarentin/2-strongly-tarentin`** — the weakest hypothesis found:
chronology in `M` at every point, inside every neighbourhood, i.e. every point strongly tarentin in
the future and in the past (`Z⁺ = Z⁻ = M`): `Causality.tarentin_of_Zplus_Zminus`, pointwise
`Causality.exists_lt_lt_of_mem_Zplus_of_mem_Zminus`, from the chronological diamond
`Causality.Iplus_inter_Iminus_subset_openDiamond` (`I⁺_U(p) ∩ I⁻_U(q) ⊆ Int J_U(p, q)`) and
`Causality.mem_openDiamond_of_lt_of_lt`. Strictly weaker than chronal neighbours:
`globalLine_separates_Z`; neither is necessary for tarentin: `lightlikeLine_separates_Z`.
**`T-abs-chronal-neighbours-tarentin/3-separations`** —
`isolatedLine_separates_chronalNeighbours_tarentin` (causally arc-connected, causally plain, not
tarentin, hence without chronal neighbours: the evidence's second way to
`causally_plain ⇏ chronal_neighbours`, through `tarentin_and_plain_needed`);
`globalLine_separates_tarentin` (tarentin, push-up, causally open, causal, not absolutely minimal).

> Chronal neighbours give the tarentin property (ChronalNeighbours.tarentin): for N ∈ 𝓝 x and
> V = interior N, p ≪_V x ≪_V p' with p, p' ∈ V, and I⁺_V(p) ∩ I⁻_V(p') is an open
> neighbourhood of x inside J_M(p, p') — a new edge chronal_neighbours ⇒ tarentin
> (`programme/roadmap.toml:768`, the target's title)

> A topological spacetime $M$ is tarentin if for every $x\in M$ and every neighbourhood $\U$ of
> $x$ there exist $p,q\in \U$ such that $x\in \mathrm{Int}\left(J_M(p,q)\right)$.
> (`def:tarentin_spacetime`, `ETT.tex:677–679`)

> Let $M$ be a topological spacetime. A point $p\in M$ is strongly tarentin in the future (resp.
> in the past) if for every neighbourhood $\U$ of $p$ the set $I^+(p)\cap \U$ is non-empty (resp.
> $I^-(p)\cap \U$ is non-empty). (`def:strongly_tarentin_point`, `ETT.tex:774–776`)

> Every point of a Lorentzian manifold is strongly tarentin in the future and in the past.
> (`rem:lorentz_tarentin`, `ETT.tex:783–784`) — Lorentzian manifolds are tarentin
> (`rem:tarentin_exemples`, `ETT.tex:689`)

## Hypothesis checklist

| hypothesis | here |
|---|---|
| target: `ChronalNeighbours` (chronology in every open `V`, both sides) | ✓ carried in `ChronalNeighbours.tarentin`; ⚠ weakened in `tarentin_of_Zplus_Zminus` to `Z⁺ = Z⁻ = M` (chronology in `M`, inside each neighbourhood), strictly (`globalLine_separates_Z`) |
| separation, countability (ETT's spacetimes are `T2`, second countable, `ETT.tex:255`) | ⚠ weakened: none used, in any theorem of this file |

## SCOPE (disclosed)

* **The keeper's argument, checked against `openDiamond`.** `openDiamond ⊤ p q` is
  `interior (J⁻_M(q) ∩ J⁺_M(p))` (`Causal/Properties.lean:77`, `:80`). For `N ∈ 𝓝 x` and
  `V = interior N`, chronal neighbours give `p, p' ∈ V ⊆ N` with `p ≪_V x ≪_V p'`; the set
  `I⁺_V(p) ∩ I⁻_V(p')` is open in `M` (the axioms `isOpen_lt_right`, `isOpen_lt_left` are stated in
  `M`, `Causal/Causality.lean:81`, `:83`), contains `x`, and lies in `J_M(p, p')` by `le_of_lt` and
  `le_mono` (`V ≤ ⊤`). The argument is correct as stated and asks nothing more.
* **Chronology in `V` is used only to put `p, p'` in `N`.** By `lt_mono` the chronological diamond
  of `V` lies in that of `M`, so `p ≪_M x ≪_M p'` with `p, p' ∈ N` is enough: that is `x ∈ Z⁺ ∩ Z⁻`
  (`def:strongly_tarentin_point`), part 2. It is strictly weaker: `globalLine` (`≪` only in `ℝ`
  itself) has `Z⁺ = Z⁻ = ℝ` and no chronal neighbours. Under absolute minimality on a `T1` space the
  two hypotheses coincide (`AbsolutelyMinimal.chronalNeighbours_iff_Z`,
  `Causal/ChronalNeighbourBridge.lean:196`), so `globalLine`, not absolutely minimal, separates them
  in the reading without gluing only (kb/0014, OQ-18).
* **Neither hypothesis is necessary.** The lightlike line is tarentin (its `≤` is the timelike
  line's) with empty chronology, so `Z⁺ = Z⁻ = ∅` and no chronal neighbours: the edge does not
  reverse. It is causally arc-connected, hence absolutely minimal: this holds in either reading.
  The paper has the same phenomenon at BTZ points (`ETT.tex:1349–1350`: strongly tarentin in the
  future, not in the past, while `rem:sing_tarentin`, `ETT.tex:1365`, has every `E_{≥0}`-manifold
  tarentin); not formalised here.
* **For the paper (no label marked).** With `rem:lorentz_tarentin` (`ETT.tex:783–784`), part 2 gives
  the first claim of `rem:tarentin_exemples` (`ETT.tex:689`, Lorentzian manifolds are tarentin): the
  library has no Lorentzian manifold, so neither remark is touched; `tarentin_of_Zplus_Zminus` is
  the abstract step.
* **The separations.** The isolated line (`Causal/LocateExtension.lean:512`) is causally
  arc-connected, hence absolutely minimal: its entry holds in either reading; the ladder already
  records `causally_plain ⇏ chronal_neighbours` through `isolatedLine_separates_chronalNeighbours`,
  so this is the second way the evidence names. `globalLine_separates_tarentin` is not absolutely
  minimal: `tarentin ⇏ absolutely_minimal` (and `⇏ causally_arc_connected`) in the reading without
  gluing only (kb/0014, kb/0073, OQ-18, OQ-67 (b)).
* `causal_ladder` does not know the edge (checked: it fails on `C.ChronalNeighbours ⊢ C.Tarentin`),
  and no other ladder step occurs in this file. No `sorry`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {U : Opens M} {p q x : M}

/-! ## The chronological diamond lies in the open diamond -/

/-- **The chronological diamond `I⁺_U(p) ∩ I⁻_U(q)` lies in the open diamond `Int J_U(p, q)`**: it
is open (`isOpen_lt_right`, `isOpen_lt_left`, axioms of a causality) and contained in `J_U(p, q)`
by axiom (c) (`le_of_lt`). -/
theorem Iplus_inter_Iminus_subset_openDiamond (U : Opens M) (p q : M) :
    C.Iplus U {p} ∩ C.Iminus U {q} ⊆ C.openDiamond U p q := by
  have hopen : IsOpen (C.Iplus U {p} ∩ C.Iminus U {q}) := by
    have h₁ : C.Iplus U {p} = {y | C.lt U p y} :=
      Set.ext fun _ => Precausality.mem_Iplus_singleton
    have h₂ : C.Iminus U {q} = {y | C.lt U y q} :=
      Set.ext fun _ => Precausality.mem_Iminus_singleton
    rw [h₁, h₂]
    exact (C.isOpen_lt_right U p).inter (C.isOpen_lt_left U q)
  refine interior_maximal (fun y hy => ?_) hopen
  exact mem_diamond.2 ⟨C.le_of_lt (Precausality.mem_Iplus_singleton.1 hy.1),
    C.le_of_lt (Precausality.mem_Iminus_singleton.1 hy.2)⟩

/-- A point chronologically between `p` and `q` in `U` lies in the open diamond `Int J_U(p, q)`. -/
theorem mem_openDiamond_of_lt_of_lt (hpx : C.lt U p x) (hxq : C.lt U x q) :
    x ∈ C.openDiamond U p q :=
  Iplus_inter_Iminus_subset_openDiamond U p q
    ⟨Precausality.mem_Iplus_singleton.2 hpx, Precausality.mem_Iminus_singleton.2 hxq⟩

/-! ## Strongly tarentin points are tarentin -/

/-- **A point strongly tarentin in the future and in the past is tarentin**, chronologically: every
neighbourhood `N` of `x` contains `a ≪ x ≪ b`, and then `x ∈ Int J_M(a, b)`
(`def:strongly_tarentin_point`, `def:tarentin_spacetime`). -/
theorem exists_lt_lt_of_mem_Zplus_of_mem_Zminus (hp : x ∈ C.Zplus) (hm : x ∈ C.Zminus)
    {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ a ∈ N, ∃ b ∈ N, C.lt ⊤ a x ∧ C.lt ⊤ x b ∧ x ∈ C.openDiamond ⊤ a b := by
  obtain ⟨a, ha, haN⟩ := hm N hN
  obtain ⟨b, hb, hbN⟩ := hp N hN
  have hax : C.lt ⊤ a x := Precausality.mem_Iminus_singleton.1 ha
  have hxb : C.lt ⊤ x b := Precausality.mem_Iplus_singleton.1 hb
  exact ⟨a, haN, b, hbN, hax, hxb, mem_openDiamond_of_lt_of_lt hax hxb⟩

/-- **Every point strongly tarentin in the future and in the past gives the tarentin property**
(`Z⁺ = Z⁻ = M ⇒ tarentin`), with no separation axiom. The weakest hypothesis of this file: strictly
weaker than chronal neighbours (`globalLine_separates_Z`), and not necessary
(`lightlikeLine_separates_Z`). -/
theorem tarentin_of_Zplus_Zminus (hZp : C.Zplus = univ) (hZm : C.Zminus = univ) :
    C.Tarentin := by
  intro x N hN
  obtain ⟨a, ha, b, hb, -, -, hx⟩ := exists_lt_lt_of_mem_Zplus_of_mem_Zminus
    (hZp ▸ mem_univ x) (hZm ▸ mem_univ x) hN
  exact ⟨a, ha, b, hb, hx⟩

/-! ## Chronal neighbours are tarentin -/

/-- **The keeper's argument, as stated**: with chronal neighbours, every neighbourhood `N` of `x`
contains an open `V` (namely `interior N`) and `a, b ∈ V` with `a ≪_V x ≪_V b`, such that
`I⁺_V(a) ∩ I⁻_V(b)` is a neighbourhood of `x` inside `J_M(a, b)`. -/
theorem ChronalNeighbours.exists_lt_lt (h : C.ChronalNeighbours) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ V : Opens M, (V : Set M) ⊆ N ∧ ∃ a ∈ V, ∃ b ∈ V, C.lt V a x ∧ C.lt V x b ∧
      C.Iplus V {a} ∩ C.Iminus V {b} ∈ 𝓝 x ∧
      C.Iplus V {a} ∩ C.Iminus V {b} ⊆ C.diamond ⊤ a b := by
  let V : Opens M := ⟨interior N, isOpen_interior⟩
  have hxV : x ∈ V := mem_interior_iff_mem_nhds.2 hN
  obtain ⟨a, haV, hax⟩ := h.1 V x hxV
  obtain ⟨b, hbV, hxb⟩ := h.2 V x hxV
  have hxb' : C.lt V x b := hxb
  have hopen : IsOpen (C.Iplus V {a} ∩ C.Iminus V {b}) := by
    have h₁ : C.Iplus V {a} = {y | C.lt V a y} :=
      Set.ext fun _ => Precausality.mem_Iplus_singleton
    have h₂ : C.Iminus V {b} = {y | C.lt V y b} :=
      Set.ext fun _ => Precausality.mem_Iminus_singleton
    rw [h₁, h₂]
    exact (C.isOpen_lt_right V a).inter (C.isOpen_lt_left V b)
  refine ⟨V, interior_subset, a, haV, b, hbV, hax, hxb', hopen.mem_nhds
    ⟨Precausality.mem_Iplus_singleton.2 hax, Precausality.mem_Iminus_singleton.2 hxb'⟩,
    fun y hy => mem_diamond.2 ⟨?_, ?_⟩⟩
  · exact C.le_mono le_top (C.le_of_lt (Precausality.mem_Iplus_singleton.1 hy.1))
  · exact C.le_mono le_top (C.le_of_lt (Precausality.mem_Iminus_singleton.1 hy.2))

/-- **Chronal neighbours give the tarentin property** (`chronal_neighbours ⇒ tarentin`), with no
separation or countability hypothesis: `ChronalNeighbours.exists_lt_lt`, the neighbourhood
`I⁺_V(a) ∩ I⁻_V(b)` of `x` lying in `J_M(a, b)` with `a, b ∈ N`. The converse fails
(`lightlikeLine_separates_Z`). -/
theorem ChronalNeighbours.tarentin (h : C.ChronalNeighbours) : C.Tarentin := by
  intro x N hN
  obtain ⟨V, hVN, a, haV, b, hbV, -, -, hnhds, hsub⟩ := h.exists_lt_lt hN
  exact ⟨a, hVN haV, b, hVN hbV,
    mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hnhds hsub)⟩

/-- A causality which is not tarentin has no chronal neighbours. -/
theorem not_chronalNeighbours_of_not_tarentin (h : ¬ C.Tarentin) : ¬ C.ChronalNeighbours :=
  fun hN => h hN.tarentin

end Causality

/-! ## Sharpness: the globally chronological line and the lightlike line -/

/-- Every point of the globally chronological line is strongly tarentin in the future. -/
theorem globalLine_Zplus : globalLine.Zplus = univ := by
  refine eq_univ_of_forall fun x N hN => ?_
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨(x + u) / 2, Precausality.mem_Iplus_singleton.2 ⟨rfl, by linarith⟩, hsub ?_⟩
  constructor <;> linarith

/-- Every point of the globally chronological line is strongly tarentin in the past. -/
theorem globalLine_Zminus : globalLine.Zminus = univ := by
  refine eq_univ_of_forall fun x N hN => ?_
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hN
  refine ⟨(l + x) / 2, Precausality.mem_Iminus_singleton.2 ⟨rfl, by linarith⟩, hsub ?_⟩
  constructor <;> linarith

/-- The globally chronological line is tarentin (`tarentin_of_Zplus_Zminus`). -/
theorem globalLine_tarentin : globalLine.Tarentin :=
  Causality.tarentin_of_Zplus_Zminus globalLine_Zplus globalLine_Zminus

/-- **`Z⁺ = Z⁻ = M` is strictly weaker than chronal neighbours**: on `ℝ` (Hausdorff, second
countable), the globally chronological line has every point strongly tarentin in the future and in
the past, is therefore tarentin, and has no chronal neighbours. Not absolutely minimal
(`globalLine_not_absolutelyMinimal`): the two hypotheses agree under absolute minimality on a `T1`
space (`AbsolutelyMinimal.chronalNeighbours_iff_Z`). -/
theorem globalLine_separates_Z :
    globalLine.Zplus = univ ∧ globalLine.Zminus = univ ∧ globalLine.Tarentin ∧
      ¬ globalLine.ChronalNeighbours :=
  ⟨globalLine_Zplus, globalLine_Zminus, globalLine_tarentin, globalLine_not_chronalNeighbours⟩

/-- **A tarentin causality which is not absolutely minimal**: on `ℝ`, the globally chronological
line is tarentin, has push-up, is causally open and causal, and is not absolutely minimal (in the
reading of `defi:causalite` without gluing: kb/0014). -/
theorem globalLine_separates_tarentin :
    globalLine.Tarentin ∧ globalLine.PushUp ∧ globalLine.CausallyOpen ∧ globalLine.IsCausal ∧
      ¬ globalLine.ChronalNeighbours ∧ ¬ globalLine.AbsolutelyMinimal :=
  ⟨globalLine_tarentin, globalLine_pushUp, globalLine_causallyOpen, globalLine_isCausal,
    globalLine_not_chronalNeighbours, globalLine_not_absolutelyMinimal⟩

/-- No point of the lightlike line is strongly tarentin in the future: its chronology is empty. -/
theorem lightlikeLine_Zplus : lightlikeLine.Zplus = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨y, hy, -⟩ := hx univ Filter.univ_mem
  exact Precausality.mem_Iplus_singleton.1 hy

/-- No point of the lightlike line is strongly tarentin in the past. -/
theorem lightlikeLine_Zminus : lightlikeLine.Zminus = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨y, hy, -⟩ := hx univ Filter.univ_mem
  exact Precausality.mem_Iminus_singleton.1 hy

/-- **Neither chronal neighbours nor `Z⁺ = Z⁻ = M` is necessary for tarentin**: the lightlike line
is globally hyperbolic, has push-up, is causally open, causally arc-connected (hence absolutely
minimal) and tarentin, while no point is strongly tarentin on either side and it has no chronal
neighbours. -/
theorem lightlikeLine_separates_Z :
    lightlikeLine.GloballyHyperbolic ∧ lightlikeLine.PushUp ∧ lightlikeLine.CausallyOpen ∧
      lightlikeLine.CausallyArcConnected ∧ lightlikeLine.Tarentin ∧
      lightlikeLine.Zplus = ∅ ∧ lightlikeLine.Zminus = ∅ ∧ ¬ lightlikeLine.ChronalNeighbours :=
  ⟨lightlikeLine_globallyHyperbolic, lightlikeLine_pushUp, lightlikeLine_causallyOpen,
    lightlikeLine_causallyArcConnected, (timelikeLine_tarentin : lightlikeLine.Tarentin),
    lightlikeLine_Zplus, lightlikeLine_Zminus, lightlikeLine_not_chronalNeighbours⟩

/-! ## Causal plainness does not give chronal neighbours, through tarentin -/

/-- **A causally arc-connected, causally plain line which is not tarentin, hence has no chronal
neighbours**: the line with a chronologically isolated origin (`tarentin_and_plain_needed`) and
`not_chronalNeighbours_of_not_tarentin`. -/
theorem isolatedLine_separates_chronalNeighbours_tarentin :
    isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyPlain ∧
      ¬ isolatedLine.Tarentin ∧ ¬ isolatedLine.ChronalNeighbours := by
  obtain ⟨hC, hP, hT, -⟩ := tarentin_and_plain_needed.2.1
  exact ⟨hC, hP, hT, Causality.not_chronalNeighbours_of_not_tarentin hT⟩

end Causal
