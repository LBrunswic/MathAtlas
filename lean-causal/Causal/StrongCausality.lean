import Causal.Properties

/-!
# Strong causality: causality, the injectivity of `x ↦ I^±(x)`, the Alexandrov topology

**`rem:topological_spacetime_strongly_causal`** — `ETT.tex:667`.
**`prop:FZenon_injectif`** — `ETT.tex:894`.
**`prop:tarentin_topological_spacetime_causality`** — `ETT.tex:713`.

> If $M$ is strongly causal then $M$ is causal.

> Let $M$ be a topological spacetime. If $M$ is strongly causal, then the map
> $Z^\pm(M)\to\mathcal{P}(M)$, $x\mapsto I^\pm(x)$ is injective.

`prop:tarentin_topological_spacetime_causality` is proved with causal openness read with `J^±`,
as the author ruled on 2026-09-27 (DEC-8).

> Let $M$ be a tarentin topological spacetime. If the causality of $M$ is open, then the
> following are equivalent: (i) $M$ is strongly causal; (ii) the Alexandrov topology on $M$
> coincides with the topology of $M$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `rem:topological_spacetime_strongly_causal`: `M` Hausdorff, second countable | ⚠ weakened: `T1Space M` (`StronglyCausal.isCausal`) |
| — strongly causal | ⚠ weakened: the neighbourhood form `StronglyCausal` |
| `prop:FZenon_injectif`: `M` Hausdorff | ✓ carried: `T2Space M` |
| — `M` second countable | ⚠ weakened: not used |
| — strongly causal | ⚠ weakened: the neighbourhood form `StronglyCausal` |
| `prop:tarentin_topological_spacetime_causality`: tarentin | ✓ carried for (i)⇒(ii); ⚠ weakened, not used, for (ii)⇒(i) |
| — the causality of `M` is open | ✓ carried for (ii)⇒(i): `CausallyOpen`, the definition read with `J^±` (DEC-8); ⚠ weakened, not used, for (i)⇒(ii) |
| — second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* `prop:tarentin_topological_spacetime_causality` is the theorem
  `stronglyCausal_iff_alexandrovTopology_eq`. The step `J^-(\ring J^-(b_i)) = \ring J^-(b_i)`
  of (ii)⇒(i) is where causal openness in the past is used. The equivalence is also proved for
  the auxiliary open form (`stronglyCausalOpen_iff_alexandrovTopology_eq`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **`rem:topological_spacetime_strongly_causal`.** A strongly causal spacetime is causal. -/
theorem StronglyCausal.isCausal [T1Space M] (h : C.StronglyCausal) : C.IsCausal := by
  intro x y hxy hyx
  by_contra hne
  have hN : ({y}ᶜ : Set M) ∈ 𝓝 x := isOpen_compl_singleton.mem_nhds hne
  obtain ⟨V, hV, hVN, -, hconv⟩ := h x _ hN
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hy : y ∈ C.diamond ⊤ x x := mem_diamond.2 ⟨hxy, hyx⟩
  exact hVN (hconv x hxV x hxV hy) rfl

/-- **`prop:FZenon_injectif`**, future. On a strongly causal Hausdorff spacetime `x ↦ I^+(x)` is
injective on the set `Z^+(M)` of points strongly tarentin in the future. -/
theorem Iplus_injOn_Zplus [T2Space M] (h : C.StronglyCausal) :
    Set.InjOn (fun x => C.Iplus ⊤ {x}) C.Zplus := by
  intro x hx y hy hxy
  have hI : C.Iplus ⊤ {x} = C.Iplus ⊤ {y} := hxy
  by_contra hne
  obtain ⟨Ux, Uy, hUx, hUy, hxUx, hyUy, hdisj⟩ := t2_separation hne
  obtain ⟨Vx, hVx, hVxU, -, hconvx⟩ := h x Ux (hUx.mem_nhds hxUx)
  obtain ⟨Vy, hVy, hVyU, -, -⟩ := h y Uy (hUy.mem_nhds hyUy)
  -- a point `a` of `I^+(x)` in `V_x`
  obtain ⟨a, haI, haV⟩ := hx Vx hVx
  have hya : C.lt ⊤ y a := by
    have : a ∈ C.Iplus ⊤ {y} := by rw [← hI]; exact haI
    simpa using this
  -- `I^-(a) ∩ V_y` is a neighbourhood of `y`, and `y` is strongly tarentin in the future
  have hN : C.Iminus ⊤ {a} ∩ Vy ∈ 𝓝 y :=
    Filter.inter_mem (isOpen_Iminus.mem_nhds (by simpa using hya)) hVy
  obtain ⟨b, hbI, hba, hbV⟩ := hy _ hN
  have hba' : C.lt ⊤ b a := by simpa using hba
  have hxb : C.lt ⊤ x b := by
    have : b ∈ C.Iplus ⊤ {x} := by rw [hI]; exact hbI
    simpa using this
  -- `b` lies in the diamond from `x` to `a`, hence in `V_x` by causal convexity
  have hbVx : b ∈ Vx := hconvx x (mem_of_mem_nhds hVx) a haV
    (mem_diamond.2 ⟨C.le_of_lt hxb, C.le_of_lt hba'⟩)
  exact Set.disjoint_left.1 hdisj (hVxU hbVx) (hVyU hbV)

/-- **`prop:FZenon_injectif`**, past. -/
theorem Iminus_injOn_Zminus [T2Space M] (h : C.StronglyCausal) :
    Set.InjOn (fun x => C.Iminus ⊤ {x}) C.Zminus :=
  C.dual.Iplus_injOn_Zplus (dual_stronglyCausal.2 h)

/-! ### The Alexandrov topology -/

/-- "Since open diamonds are open for the topology of `M`, the topology of `M` is finer than the
Alexandrov topology on `M`." -/
theorem le_alexandrovTopology : ‹TopologicalSpace M› ≤ C.alexandrovTopology := by
  refine le_generateFrom ?_
  rintro S ⟨p, q, rfl⟩
  exact isOpen_openDiamond

/-- On a causally open spacetime the causal future of the interior of a causal future stays
in that interior. -/
theorem CausallyOpen.Jplus_interior_Jplus_subset (hO : C.CausallyOpen) (U : Opens M)
    (A : Set M) : C.Jplus U (interior (C.Jplus U A)) ⊆ interior (C.Jplus U A) := by
  let O : Opens M := ⟨interior (C.Jplus U A), isOpen_interior⟩
  have hOU : O ≤ U := fun x hx => Precausality.Jplus_subset_carrier (interior_subset hx)
  have hopen : IsOpen (C.Jplus U (O : Set M)) := hO.1 U O hOU
  refine interior_maximal ?_ hopen
  exact (Precausality.Jplus_mono interior_subset).trans Precausality.Jplus_Jplus_subset

theorem CausallyOpen.Jminus_interior_Jminus_subset (hO : C.CausallyOpen) (U : Opens M)
    (A : Set M) : C.Jminus U (interior (C.Jminus U A)) ⊆ interior (C.Jminus U A) :=
  (dual_causallyOpen.2 hO).Jplus_interior_Jplus_subset U A

/-- On a causally open spacetime an open diamond is causally convex. -/
theorem CausallyOpen.causallyConvexIn_openDiamond (hO : C.CausallyOpen) (U : Opens M)
    (p q : M) : C.CausallyConvexIn (C.openDiamond U p q) U := by
  refine ⟨fun x hx => C.le_mem_right (mem_diamond.1 (openDiamond_subset_diamond hx)).1, ?_⟩
  intro a ha b hb z hz
  rw [mem_diamond] at hz
  have hsplit : C.openDiamond U p q =
      interior (C.Jminus U {q}) ∩ interior (C.Jplus U {p}) := interior_inter
  rw [hsplit] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · exact hO.Jminus_interior_Jminus_subset U {q} ⟨b, hb.1, hz.2⟩
  · exact hO.Jplus_interior_Jplus_subset U {p} ⟨a, ha.2, hz.1⟩

/-- `prop:tarentin_topological_spacetime_causality`, (i)⇒(ii). Causal openness is not used. -/
theorem StronglyCausal.alexandrovTopology_eq (hT : C.Tarentin) (h : C.StronglyCausal) :
    C.alexandrovTopology = ‹TopologicalSpace M› := by
  refine le_antisymm (fun O hO => ?_) le_alexandrovTopology
  refine (@isOpen_iff_forall_mem_open M C.alexandrovTopology O).2 fun x hx => ?_
  obtain ⟨V, hV, hVO, -, hconv⟩ := h x O (hO.mem_nhds hx)
  obtain ⟨a, ha, b, hb, hxab⟩ := hT x V hV
  refine ⟨C.openDiamond ⊤ a b, ?_, ?_, hxab⟩
  · exact (openDiamond_subset_diamond.trans (hconv a ha b hb)).trans hVO
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, b, rfl⟩

/-- `prop:tarentin_topological_spacetime_causality`, (ii)⇒(i), under two-sided causal openness,
and with the open form of strong causality as conclusion. The tarentin hypothesis is not
used. -/
theorem stronglyCausalOpen_of_alexandrovTopology_eq (hO : C.CausallyOpen)
    (h : C.alexandrovTopology = ‹TopologicalSpace M›) : C.StronglyCausalOpen := by
  intro p N hN
  have hb := TopologicalSpace.isTopologicalBasis_of_subbasis h.symm
  obtain ⟨W, ⟨f, ⟨hfin, hfs⟩, rfl⟩, hpW, hWN⟩ := hb.mem_nhds_iff.1 hN
  have hWopen : IsOpen (⋂₀ f) := hb.isOpen ⟨f, ⟨hfin, hfs⟩, rfl⟩
  refine ⟨⟨⋂₀ f, hWopen⟩, hpW, hWN, fun _ _ => trivial, ?_⟩
  intro a ha b hb' z hz D hD
  obtain ⟨u, v, rfl⟩ := hfs hD
  exact (hO.causallyConvexIn_openDiamond ⊤ u v).2 a (ha _ hD) b (hb' _ hD) hz

/-- `prop:tarentin_topological_spacetime_causality` for the neighbourhood form of strong
causality, under two-sided causal openness. -/
theorem stronglyCausal_iff_alexandrovTopology_eq (hT : C.Tarentin) (hO : C.CausallyOpen) :
    C.StronglyCausal ↔ C.alexandrovTopology = ‹TopologicalSpace M› :=
  ⟨fun h => h.alexandrovTopology_eq hT,
    fun h => (stronglyCausalOpen_of_alexandrovTopology_eq hO h).stronglyCausal⟩

/-- `prop:tarentin_topological_spacetime_causality` for the open form of strong causality, under
two-sided causal openness. -/
theorem stronglyCausalOpen_iff_alexandrovTopology_eq (hT : C.Tarentin) (hO : C.CausallyOpen) :
    C.StronglyCausalOpen ↔ C.alexandrovTopology = ‹TopologicalSpace M› :=
  ⟨fun h => h.stronglyCausal.alexandrovTopology_eq hT,
    stronglyCausalOpen_of_alexandrovTopology_eq hO⟩

end Causality

end Causal
