import Causal.ArcConnected
import Causal.LadderLocal

/-!
# Causal plainness from push-up and local `Z^±`, and from push-up and chronal neighbours

Programme target `T-abs-hoist-plain-locz` (`programme/roadmap.toml:720`; layer 1, no label of
`ETT.tex`; ETT-layer imports only, no model, no metric, curve length or geodesic). Nothing is
marked: `defi:causalement_plat` is the definition `Causality.CausallyPlain` (`Causal.Properties`),
and this module proves criteria for it.

> A topological spacetime $M$ is \emph{causally plain} if for every open subset $\U$ of $M$ and
> every $A\subset \U$, $\mathrm{Int}\left(J^\pm_\U(A)\right)\subset \overline{I^\pm_\U(A)}$,
> equivalently if every non-empty open subset of $J^\pm_\U(A)$ meets $I^\pm_\U(A)$.
> (`defi:causalement_plat`, `ETT.tex:283–287`)

## What is here (no `sorry`)

* **Hoisted, same full names, same statements, text verbatim** (kb/0063):
  * from `Causal.Port.E0SingularFlat`'s section `Local` (gx's `LocalModel` §2, ported by
    T-ett-port-e0-sfa), any topological space `X` and causality `D`, namespace `Causal.E0LM` kept:
    `LocZplus`, `LocZminus`, `LocTarentin`, `LocNoPast`, `LocPastIn` (the local forms of `Z^±`,
    tarentin, empty past and closed past, in every open set), `rel_of_causallyConvex` (under causal
    arc-connectedness, the relations of `M` between two points of a causally convex `V ⊆ W` are
    those of `W`), `locZplus_of`, `locZminus_of`, `locTarentin_of` (causally arc-connected and
    strongly causal: the global forms give the local ones);
  * from `Causal.Port.E0ModelRows` (T-ett-e0-model-rows), namespace `Causal.Causality`:
    `Jplus_subset_closure_Iplus_of_locZplus`, `Jminus_diff_subset_closure_Iminus_of_locZminus` and
    **`causallyPlain_of_locZ`**: push-up, `Z⁺` in every open set and `Z⁻` in every open set off a set
    with empty interior give causal plainness.
* **New (T-abs-hoist-stranded-homes): `E0LM.LocZplus.chronalFutureNeighbours`**, `LocZplus D ⇒
  D.ChronalFutureNeighbours` (`N = V` in the definition), written after the hoisted section, which
  stays verbatim; `Causal.Model.E0ChronalNeighbour` cites it at `E₀`, `E_{≥0}`- and `E₀`-manifolds.
* **New: `Causality.PushUp.causallyPlain_of_chronalNeighbours`**, the ladder edge
  `push_up ∧ chronal_neighbours ⇒ causally_plain`, beside
  `PushUp.causallyOpen_of_chronalNeighbours` (`Causal.LadderLocal`). Chronal neighbours give
  `LocZplus C` and `LocZminus C ∅` (for `y ∈ W` and `N ∈ 𝓝 y`, apply them in the open
  `W ⊓ interior N` and carry the chronology to `W` by the axiom `lt_mono`), and `interior ∅ = ∅`.

## Hypothesis checklist (`PushUp.causallyPlain_of_chronalNeighbours`)

| hypothesis | here |
|---|---|
| push-up (`defi:pushup`) | ✓ carried (`PushUp`); cannot be dropped: `timelikeLineTop` (`Causal.Morphism`, `≤_ℝ` total, `≪` the timelike line's) has chronal neighbours, fails push-up (`1 ≪ 2 ≤_ℝ 0`) and is not plain (`J⁺_ℝ({0}) = ℝ`, `I⁺_ℝ({0}) = ]0, ∞[`); not in the library (T-abs-timelike-line-top); a causality without gluing only (kb/0014) |
| chronal neighbours in every open set | ✓ carried (`ChronalNeighbours`, kb/0053); cannot be dropped: the lightlike line has push-up and is not plain (`Causal.deux_pushup`) |
| separation, countability | none asked |

## SCOPE (disclosed)

* **A verbatim hoist.** The moved text is byte-identical to its source (`E0SingularFlat` HEAD
  `bd1fafb` l.302–380, `E0ModelRows` l.106–136); the two Port modules import this one. The
  namespace `E0LM` is kept so that the names do not change (as `Flat.dependenceDomain` kept
  `Flat` at its hoist, kb/0047, until DEC-198 renamed it `Causality.dependenceDomain`); a rename
  is a separate question. The `E₀` instances (`E0LM.e0_locZplus`, …)
  stay in `Causal.Port.E0SingularFlat`, and `SingularFlatAxioms.causallyPlain` and the
  `BTZAxioms` lemmas, stated over `Causal.SingularFlat`'s bundles, are in `Causal.SingularFlatPlain`.
* **What the ladder edge does not say.** It asks chronology in every open set at every point,
  which a BTZ point lacks (`I⁻(p) = ∅`); there `causallyPlain_of_locZ` with `S = sing₀` (empty
  interior) is the form that applies (`SingularFlatAxioms.causallyPlain`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The hoisted text was
ported from gx `c48aa45` (`GX/BTZ/LocalModel.lean` l.171–249; T-ett-port-e0-sfa, DEC-134) and
written by T-ett-e0-model-rows.
-/

namespace Causal

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0LM

/-! ### §2 Local forms of the model's causal facts, in every open set -/

section Local

variable {X : Type*} [TopologicalSpace X]

/-- `Z⁺` in every open set: at every `y ∈ W`, `I⁺_W(y)` meets every neighbourhood of `y`. -/
def LocZplus (D : Causal.Causality X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → ∀ N ∈ 𝓝 y, ∃ z ∈ N, D.lt W y z

/-- `Z⁻` off `S` in every open set. -/
def LocZminus (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → y ∉ S → ∀ N ∈ 𝓝 y, ∃ z ∈ N, D.lt W z y

/-- Tarentin in every open set: small open diamonds of `W` around every point. -/
def LocTarentin (D : Causal.Causality X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → ∀ N ∈ 𝓝 y, ∃ p ∈ N, ∃ q ∈ N, y ∈ D.openDiamond W p q

/-- No chronological past at the points of `S`, in every open set. -/
def LocNoPast (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ S → ∀ z, ¬ D.lt W z y

/-- The causal past of a point of `S` stays in `S`, in every open set. -/
def LocPastIn (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ S → ∀ z, D.le W z y → z ∈ S

variable {D : Causal.Causality X}

/-- In a causally arc-connected spacetime, the relations of `⊤` between two points of a causally
convex set `V ⊆ W` are relations of `W` (the realising curve stays in the diamond, so in `V`). -/
theorem rel_of_causallyConvex (hD : D.CausallyArcConnected) {V : Set X}
    (hV : D.CausallyConvexIn V ⊤) {W : Opens X} (hVW : V ⊆ W) {y z : X} (hy : y ∈ V)
    (hz : z ∈ V) : (D.le ⊤ y z → D.le W y z) ∧ (D.lt ⊤ y z → D.lt W y z) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc, h0, h1⟩ := (hD ⊤ le_rfl y z).1.1 h
    subst h0; subst h1
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ W := fun t ht =>
      hVW (hV.2 _ hy _ hz (Causal.Causality.mem_diamond.2
        ⟨hc.le_of_le le_rfl ht.1 ht.2, hc.le_of_le ht.1 ht.2 le_rfl⟩))
    have hcW : D.CausalCurveOn W c 0 1 := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
    exact hcW.le_of_le le_rfl zero_le_one le_rfl
  · obtain ⟨c, hc, h0, h1⟩ := (hD ⊤ le_rfl y z).2.1 h
    subst h0; subst h1
    have hc' := hc.causalCurveOn
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ W := fun t ht =>
      hVW (hV.2 _ hy _ hz (Causal.Causality.mem_diamond.2
        ⟨hc'.le_of_le le_rfl ht.1 ht.2, hc'.le_of_le ht.1 ht.2 le_rfl⟩))
    have hcW : D.ChronalCurveOn W c 0 1 := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
    exact hcW.lt_of_lt le_rfl zero_lt_one le_rfl

theorem locZplus_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal)
    (hZ : ∀ y, y ∈ D.Zplus) : LocZplus D := by
  intro W y hy N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨z, hzI, hzV⟩ := hZ y V hV
  exact ⟨z, (hVsub hzV).1, (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2)
    (mem_of_mem_nhds hV) hzV).2 (Causal.Precausality.mem_Iplus_singleton.1 hzI)⟩

theorem locZminus_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal) {S : Set X}
    (hZ : ∀ y, y ∉ S → y ∈ D.Zminus) : LocZminus D S := by
  intro W y hy hyS N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨z, hzI, hzV⟩ := hZ y hyS V hV
  exact ⟨z, (hVsub hzV).1, (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2)
    hzV (mem_of_mem_nhds hV)).2 (Causal.Precausality.mem_Iminus_singleton.1 hzI)⟩

theorem locTarentin_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal)
    (hT : D.Tarentin) : LocTarentin D := by
  intro W y hy N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨p, hp, q, hq, hyd⟩ := hT y V hV
  refine ⟨p, (hVsub hp).1, q, (hVsub hq).1, interior_mono (fun w hw => ?_) hyd⟩
  have hwV : w ∈ V := hVc.2 p hp q hq hw
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
  exact Causal.Causality.mem_diamond.2
    ⟨(rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2) hp hwV).1 h1,
      (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2) hwV hq).1 h2⟩

end Local

/-! ### `Z⁺` in every open set gives chronal future neighbours -/

/-- **`Z⁺` in every open set gives chronal future neighbours** (`LocZplus D ⇒
D.ChronalFutureNeighbours`): `LocZplus` read with the neighbourhood `N = V` of `v`
(T-abs-hoist-stranded-homes: the step the `E₀` closer wrote inline three times in
`Causal.Model.E0ChronalNeighbour`, which now cites it). -/
theorem LocZplus.chronalFutureNeighbours {X : Type*} [TopologicalSpace X]
    {D : Causal.Causality X} (h : LocZplus D) : D.ChronalFutureNeighbours :=
  fun V v hv => h V v hv V (V.isOpen.mem_nhds hv)

end E0LM

end Causal

namespace Causal

open Set TopologicalSpace Topology Filter

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-! ### Causal plainness from push-up and the local forms of `Z^±` -/

/-- With push-up and `Z⁺` in every open set, `J⁺_U(A) ⊂ closure I⁺_U(A)`. -/
theorem Jplus_subset_closure_Iplus_of_locZplus (hP : C.PushUp) (hZ : E0LM.LocZplus C)
    (U : Opens M) (A : Set M) : C.Jplus U A ⊆ closure (C.Iplus U A) := by
  rintro y ⟨a, ha, hay⟩
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨z, hzN, hyz⟩ := hZ U y (C.le_mem_right hay) N hN
  exact ⟨z, hzN, a, ha, (pushUp_iff.1 hP U).2 hay hyz⟩

/-- With push-up and `Z⁻` off `S` in every open set, `J⁻_U(A) ∖ S ⊂ closure I⁻_U(A)`. -/
theorem Jminus_diff_subset_closure_Iminus_of_locZminus {S : Set M} (hP : C.PushUp)
    (hZ : E0LM.LocZminus C S) (U : Opens M) (A : Set M) :
    C.Jminus U A \ S ⊆ closure (C.Iminus U A) := by
  rintro y ⟨⟨a, ha, hya⟩, hyS⟩
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨z, hzN, hzy⟩ := hZ U y (C.le_mem_left hya) hyS N hN
  exact ⟨z, hzN, a, ha, (pushUp_iff.1 hP U).1 hzy hya⟩

/-- **Causal plainness from the local model facts**: push-up, `Z⁺` in every open set, `Z⁻` off a
set `S` with empty interior in every open set. -/
theorem causallyPlain_of_locZ {S : Set M} (hP : C.PushUp) (hZp : E0LM.LocZplus C)
    (hZm : E0LM.LocZminus C S) (hS : interior S = ∅) : C.CausallyPlain := by
  intro U A
  refine ⟨interior_subset.trans (Jplus_subset_closure_Iplus_of_locZplus hP hZp U A),
    fun y hy => ?_⟩
  have hd : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hS
  refine closure_minimal (fun z hz => ?_) isClosed_closure
    (hd.open_subset_closure_inter isOpen_interior hy)
  exact Jminus_diff_subset_closure_Iminus_of_locZminus hP hZm U A
    ⟨interior_subset hz.1, hz.2⟩

/-! ### The ladder edge `push_up ∧ chronal_neighbours ⇒ causally_plain` -/

/-- **Causal plainness from push-up and chronal neighbours** (`push_up ∧ chronal_neighbours ⇒
causally_plain`). Chronal neighbours give `Z⁺` in every open set and `Z⁻` off `∅` in every open
set: for `y ∈ W` and `N ∈ 𝓝 y` they give a chronal neighbour of `y` in the open `W ⊓ interior N`,
and `lt_mono` carries the chronology to `W`. As `interior ∅ = ∅`, `causallyPlain_of_locZ`
concludes. -/
theorem PushUp.causallyPlain_of_chronalNeighbours (hP : C.PushUp) (hN : C.ChronalNeighbours) :
    C.CausallyPlain := by
  refine causallyPlain_of_locZ (S := ∅) hP (fun W y hy N hNy => ?_)
    (fun W y hy _ N hNy => ?_) interior_empty
  · obtain ⟨z, hzV, hyz⟩ := hN.2 (W ⊓ ⟨interior N, isOpen_interior⟩) y
      ⟨hy, mem_interior_iff_mem_nhds.2 hNy⟩
    exact ⟨z, interior_subset hzV.2, C.lt_mono inf_le_left hyz⟩
  · obtain ⟨z, hzV, hzy⟩ := hN.1 (W ⊓ ⟨interior N, isOpen_interior⟩) y
      ⟨hy, mem_interior_iff_mem_nhds.2 hNy⟩
    exact ⟨z, interior_subset hzV.2, C.lt_mono inf_le_left hzy⟩

end Causality

end Causal
