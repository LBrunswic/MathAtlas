import Causal.StrongCausality
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Global hyperbolicity: the causal relation is closed, and the spacetime is strongly causal

**`prop:relation_fermee`** — `ETT.tex:1148`. **`prop:GH_Jferme`** — `ETT.tex:1178`.
**`prop:GH_fortement_causal`** — `ETT.tex:1199`.

> Let $M$ be a tarentin topological spacetime. If $J^\pm(x)$ is closed for every $x\in M$, then
> the relation $\leq_M$ is closed in $M\times M$.

> Let $M$ be a topological spacetime. If $M$ is tarentin and globally hyperbolic, then $\leq_M$
> is closed in $M\times M$ and $J^\pm(K)$ is closed for every compact $K\subset M$.

`prop:GH_fortement_causal` is the theorem `GloballyHyperbolic.stronglyCausal`, strong causality
being `StronglyCausal` as the author ruled on 2026-09-27 (DEC-7).

> Let $M$ be a tarentin topological spacetime. If $M$ is globally hyperbolic, then $M$ is
> strongly causal.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `prop:relation_fermee`: tarentin; `J^±(x)` closed for every `x` | ✓ carried |
| — second countable, Hausdorff | ⚠ weakened: not used. The paper passes through sequential closedness; the proof here is by neighbourhoods |
| `prop:GH_Jferme`: tarentin, globally hyperbolic | ✓ carried |
| — Hausdorff | ✓ carried: `T2Space M` (a compact diamond is closed) |
| — second countable | ⚠ weakened: not used |
| `prop:GH_fortement_causal`: tarentin, globally hyperbolic, Hausdorff | ✓ carried |
| — second countable | ⚠ weakened: not used. The paper's decreasing sequence of compact sets is replaced by a directed family |
| — (none) | for the auxiliary open form only (`GloballyHyperbolic.stronglyCausalOpen`): `CausallyOpen` |

## SCOPE (disclosed)

* `prop:GH_fortement_causal`. The paper's proof ends: "The open set $\ring J_M(a,b)$ contains
  $p$, is contained in $\U$ and is causally convex in $M$." Causal convexity of an **open**
  diamond is not proved there and is not a consequence of the axioms used: for `x, y` in the
  interior of `J(a,b)` and `x ≤ z ≤ y` one gets `z ∈ J(a,b)`, not `z` in its interior. The
  proof here takes the full diamond `J(a,b)`, which is causally convex and is a neighbourhood
  of `p`: that is the statement, the neighbourhood of the definition not being asked open
  (DEC-7). `GloballyHyperbolic.stronglyCausalOpen` gives an open one under causal openness,
  where an open diamond is causally convex (`CausallyOpen.causallyConvexIn_openDiamond`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- **`prop:relation_fermee`.** On a tarentin spacetime whose causal futures and pasts of points
are closed, the causal relation is closed in `M × M`. -/
theorem isClosed_le (hT : C.Tarentin) (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x})) : IsClosed {z : M × M | C.le ⊤ z.1 z.2} := by
  refine isClosed_of_closure_subset ?_
  rintro ⟨k, q⟩ hkq
  -- every neighbourhood of `q` contains a point `b` with `k ≤ b`
  have key : ∀ N ∈ 𝓝 q, ∃ b ∈ N, C.le ⊤ k b := by
    intro N hN
    obtain ⟨a, -, b, hb, hqab⟩ := hT q N hN
    refine ⟨b, hb, ?_⟩
    have hk : k ∈ closure (C.Jminus ⊤ {b}) := by
      rw [mem_closure_iff_nhds]
      intro O hO
      have hprod : O ×ˢ C.openDiamond ⊤ a b ∈ 𝓝 (k, q) :=
        prod_mem_nhds hO (isOpen_openDiamond.mem_nhds hqab)
      obtain ⟨⟨k', q'⟩, ⟨hk'O, hq'D⟩, hk'q'⟩ := mem_closure_iff_nhds.1 hkq _ hprod
      have hq'b : C.le ⊤ q' b := (mem_diamond.1 (openDiamond_subset_diamond hq'D)).2
      have hk'b : C.le ⊤ k' b := C.le_trans hk'q' hq'b
      exact ⟨k', hk'O, by simpa using hk'b⟩
    rw [(hJm b).closure_eq] at hk
    simpa using hk
  have hq : q ∈ closure (C.Jplus ⊤ {k}) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨b, hb, hkb⟩ := key N hN
    exact ⟨b, hb, by simpa using hkb⟩
  rw [(hJp k).closure_eq] at hq
  simpa using hq

/-- `prop:GH_Jferme`, first step: on a tarentin globally hyperbolic Hausdorff spacetime the
causal future of a point is closed. -/
theorem GloballyHyperbolic.isClosed_Jplus_singleton [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (p : M) : IsClosed (C.Jplus ⊤ {p}) := by
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨a, -, b, -, hqab⟩ := hT q univ univ_mem
  have hclosed : IsClosed (C.diamond ⊤ p b) := (hG.2 p b).isClosed
  have hqd : q ∈ closure (C.diamond ⊤ p b) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hN' : N ∩ C.openDiamond ⊤ a b ∈ 𝓝 q :=
      inter_mem hN (isOpen_openDiamond.mem_nhds hqab)
    obtain ⟨q', ⟨hq'N, hq'D⟩, hq'J⟩ := mem_closure_iff_nhds.1 hq _ hN'
    refine ⟨q', hq'N, ?_⟩
    rw [mem_diamond]
    exact ⟨by simpa using hq'J, (mem_diamond.1 (openDiamond_subset_diamond hq'D)).2⟩
  rw [hclosed.closure_eq] at hqd
  exact diamond_subset_Jplus hqd

theorem GloballyHyperbolic.isClosed_Jminus_singleton [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (p : M) : IsClosed (C.Jminus ⊤ {p}) :=
  (dual_globallyHyperbolic.2 hG).isClosed_Jplus_singleton (dual_tarentin.2 hT) p

/-- `prop:GH_Jferme`, first assertion: the causal relation of a tarentin globally hyperbolic
spacetime is closed. -/
theorem GloballyHyperbolic.isClosed_le [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) : IsClosed {z : M × M | C.le ⊤ z.1 z.2} :=
  Causality.isClosed_le hT (hG.isClosed_Jplus_singleton hT) (hG.isClosed_Jminus_singleton hT)

/-- If the causal relation is closed, the causal future of a compact set is closed: "the
projection `K × M → M` is a closed map, `K` being compact". -/
theorem isClosed_Jplus_of_isCompact (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {K : Set M}
    (hK : IsCompact K) : IsClosed (C.Jplus ⊤ K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hcont : Continuous fun z : K × M => ((z.1 : M), z.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hR : IsClosed ((fun z : K × M => ((z.1 : M), z.2)) ⁻¹' {z : M × M | C.le ⊤ z.1 z.2}) :=
    hle.preimage hcont
  have himg : C.Jplus ⊤ K =
      Prod.snd '' ((fun z : K × M => ((z.1 : M), z.2)) ⁻¹' {z : M × M | C.le ⊤ z.1 z.2}) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(⟨x, hx⟩, y), hxy, rfl⟩
    · rintro ⟨⟨⟨x, hx⟩, y'⟩, hxy, rfl⟩
      exact ⟨x, hx, hxy⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace _ hR

theorem isClosed_Jminus_of_isCompact (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) {K : Set M}
    (hK : IsCompact K) : IsClosed (C.Jminus ⊤ K) := by
  have hswap : IsClosed {z : M × M | C.dual.le ⊤ z.1 z.2} :=
    hle.preimage continuous_swap
  exact C.dual.isClosed_Jplus_of_isCompact hswap hK

/-- **`prop:GH_Jferme`.** On a tarentin globally hyperbolic spacetime the causal relation is
closed in `M × M`, and the causal future and past of a compact set are closed. -/
theorem GloballyHyperbolic.isClosed_le_and_isClosed_J [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) :
    IsClosed {z : M × M | C.le ⊤ z.1 z.2} ∧
      ∀ K : Set M, IsCompact K → IsClosed (C.Jplus ⊤ K) ∧ IsClosed (C.Jminus ⊤ K) :=
  ⟨hG.isClosed_le hT, fun _ hK =>
    ⟨isClosed_Jplus_of_isCompact (hG.isClosed_le hT) hK,
      isClosed_Jminus_of_isCompact (hG.isClosed_le hT) hK⟩⟩

/-- `prop:GH_fortement_causal`, the core of the proof: around every point of a tarentin globally
hyperbolic spacetime, every neighbourhood contains a full diamond whose interior contains the
point. -/
theorem GloballyHyperbolic.exists_diamond_subset [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (p : M) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ a b, p ∈ C.openDiamond ⊤ a b ∧ C.diamond ⊤ a b ⊆ N := by
  obtain ⟨U, hUN, hUo, hpU⟩ := mem_nhds_iff.1 hN
  by_contra hcon
  have hall : ∀ a b, p ∈ C.openDiamond ⊤ a b → (C.diamond ⊤ a b \ U).Nonempty := by
    intro a b hp
    by_contra hempty
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hempty
    exact hcon ⟨a, b, hp, hempty.trans hUN⟩
  -- the family of the sets `J(a,b) ∖ U`, over the pairs whose open diamond contains `p`
  let ι := {ab : M × M // p ∈ C.openDiamond ⊤ ab.1 ab.2}
  have hne : Nonempty ι := by
    obtain ⟨a, -, b, -, hp⟩ := hT p univ univ_mem
    exact ⟨⟨(a, b), hp⟩⟩
  let t : ι → Set M := fun i => C.diamond ⊤ i.1.1 i.1.2 \ U
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hp'⟩
    have hW : C.openDiamond ⊤ a b ∩ C.openDiamond ⊤ a' b' ∈ 𝓝 p :=
      inter_mem (isOpen_openDiamond.mem_nhds hp) (isOpen_openDiamond.mem_nhds hp')
    obtain ⟨a'', ha'', b'', hb'', hp''⟩ := hT p _ hW
    refine ⟨⟨(a'', b''), hp''⟩, ?_, ?_⟩
    · show C.diamond ⊤ a'' b'' \ U ⊆ C.diamond ⊤ a b \ U
      exact sdiff_subset_sdiff_left (diamond_subset_diamond
        (openDiamond_subset_diamond ha''.1) (openDiamond_subset_diamond hb''.1))
    · show C.diamond ⊤ a'' b'' \ U ⊆ C.diamond ⊤ a' b' \ U
      exact sdiff_subset_sdiff_left (diamond_subset_diamond
        (openDiamond_subset_diamond ha''.2) (openDiamond_subset_diamond hb''.2))
  have hcompact : ∀ i, IsCompact (t i) := fun i => (hG.2 _ _).diff hUo
  have hclosed : ∀ i, IsClosed (t i) := fun i => (hcompact i).isClosed
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir
    (fun i => hall _ _ i.2) hcompact hclosed
  rw [mem_iInter] at hq
  have hqU : q ∉ U := (hq hne.some).2
  -- `p ≤ q`: the lower vertices accumulate at `p` and lie in the closed set `J^-(q)`
  have hpq : C.le ⊤ p q := by
    have hmem : p ∈ closure (C.Jminus ⊤ {q}) := by
      rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨a, ha, b, -, hp⟩ := hT p O hO
      have hqab := (hq ⟨(a, b), hp⟩).1
      exact ⟨a, ha, by simpa using (mem_diamond.1 hqab).1⟩
    rw [(hG.isClosed_Jminus_singleton hT q).closure_eq] at hmem
    simpa using hmem
  -- `q ≤ p`: the upper vertices accumulate at `p` and lie in the closed set `J^+(q)`
  have hqp : C.le ⊤ q p := by
    have hmem : p ∈ closure (C.Jplus ⊤ {q}) := by
      rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨a, -, b, hb, hp⟩ := hT p O hO
      have hqab := (hq ⟨(a, b), hp⟩).1
      exact ⟨b, hb, by simpa using (mem_diamond.1 hqab).2⟩
    rw [(hG.isClosed_Jplus_singleton hT q).closure_eq] at hmem
    simpa using hmem
  exact hqU (hG.1 hpq hqp ▸ hpU)

/-- `prop:GH_fortement_causal`, neighbourhood form: a tarentin globally hyperbolic spacetime is
strongly causal, a full diamond being the causally convex neighbourhood. -/
theorem GloballyHyperbolic.stronglyCausal [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) : C.StronglyCausal := by
  intro p N hN
  obtain ⟨a, b, hp, hsub⟩ := hG.exists_diamond_subset hT p hN
  exact ⟨C.diamond ⊤ a b,
    mem_of_superset (isOpen_openDiamond.mem_nhds hp) openDiamond_subset_diamond, hsub,
    causallyConvexIn_diamond⟩

/-- On a tarentin, causally open spacetime the two forms of strong causality agree. -/
theorem StronglyCausal.stronglyCausalOpen (hT : C.Tarentin) (hO : C.CausallyOpen)
    (h : C.StronglyCausal) : C.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨V, hV, hVN, -, hconv⟩ := h p N hN
  obtain ⟨a, ha, b, hb, hp⟩ := hT p V hV
  exact ⟨⟨C.openDiamond ⊤ a b, isOpen_openDiamond⟩, hp,
    (openDiamond_subset_diamond.trans (hconv a ha b hb)).trans hVN,
    hO.causallyConvexIn_openDiamond ⊤ a b⟩

/-- `prop:GH_fortement_causal`, open form, under two-sided causal openness. -/
theorem GloballyHyperbolic.stronglyCausalOpen [T2Space M] (hT : C.Tarentin)
    (hO : C.CausallyOpen) (hG : C.GloballyHyperbolic) : C.StronglyCausalOpen :=
  (hG.stronglyCausal hT).stronglyCausalOpen hT hO

end Causality

end Causal
