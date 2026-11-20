import Causal.Properties

/-!
# A compact set has a causally minimal point

No label of `ETT.tex` is certified. This module is the model-free core of Sbierski's Lemma 3.9
(1309.7591, p. 17), hoisted out of the model-importing `Causal.CBG.NoCorresponding` and out of
`Causal.NestedCausalities` (programme target `T-abs-hoist-model-free`, kb/0047), so that a layer-1
module may use it: it imports `Causal.Properties` and no model.

> Lemma 3.9. Let $U$ be a CGHD of $M$ and $M'$ with isometric embedding $\psi$. Assume that
> $C\cap J^+(\iota(M))$ is non-empty. Then there exists a point $p\in C$ with the property
> $J^-(p)\cap\partial U\cap J^+(\iota(M))=\{p\}$ (3.10). (Sbierski, p. 17)

The point of (3.10) is found as a `≤`-minimal point of a compact set, by Zorn on its non-empty
closed down-sets, in place of Sbierski's null geodesics in `∂U` and of the "Geroch time minimised
on `∂U ∩ J(Σ, p₀)`" of `docs/CBG-DESIGN.md` §3 step 4.

## What is proved (no `sorry` in this file)

* `Causality.exists_minimal_of_isCompact_on`: in an open `W` with `≤_W` antisymmetric, a
  non-empty compact `K ⊆ W` whose sets `J⁻_W(x) ∩ K` are closed has a point `p` with
  `J⁻_W(p) ∩ K = {p}` (`M` Hausdorff).
* `Causality.exists_minimal_of_isCompact`: its case `W = ⊤` in the form the proof of Lemma 3.9
  uses (`M` causal, every `J⁻(x)` closed): every `q ∈ K` with `q ≤ p` is `p`.

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| Lemma 3.9's proof: null geodesics in `∂U`; the design: a Geroch time | ⚠ weakened: neither; Zorn on the closed down-sets of `K` |
| `M` causal | ✓ carried: `≤_W` antisymmetric (`_on`), `C.IsCausal` (`W = ⊤`) |
| `J⁻(x)` closed | ✓ carried for `W = ⊤`; ⚠ weakened in `_on`: `J⁻_W(x)` closed inside `K` only |
| `M` Hausdorff | ✓ carried: `[T2Space M]` (a compact set is closed) |

## SCOPE (disclosed)

* Only the minimal-point step of Lemma 3.9 is here. The corresponding point and (3.10) are
  `Causal.CBG.NoCorresponding`'s (`IsCorrPair.exists_corresponds_of_le`,
  `CGHDData.exists_spacelike_corresponding`), and the open-set form of (3.10) on a closed set is
  `Causality.exists_spacelike_boundary_point` of `Causal.NestedCausalities` (ERS19 (4.85)).
* Moved, not restated: both theorems keep their names and statements.
  `exists_minimal_of_isCompact_on` comes verbatim from `Causal.NestedCausalities`;
  `exists_minimal_of_isCompact`, proved in `Causal.CBG.NoCorresponding` by the same Zorn argument
  at `W = ⊤`, is now derived from it. `Causal.CBG.NoCorresponding` and
  `Causal.NestedCausalities` import this module.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

universe u

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {W : Opens M}

/-- **A compact set has a causally minimal point** (`W` causal, `M` Hausdorff, the pasts closed in
the set). -/
theorem exists_minimal_of_isCompact_on [T2Space M]
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) {K : Set M} (hK : IsCompact K)
    (hKW : K ⊆ W) (hne : K.Nonempty) (hJ : ∀ x ∈ K, IsClosed (C.Jminus W {x} ∩ K)) :
    ∃ p ∈ K, C.Jminus W {p} ∩ K = {p} := by
  have hKcl : IsClosed K := hK.isClosed
  have hdown : ∀ x ∈ K, ∀ y ∈ C.Jminus W {x} ∩ K, C.Jminus W {y} ∩ K ⊆ C.Jminus W {x} ∩ K := by
    intro x _ y hy z hz
    have h1 : C.le W z y := by simpa using hz.1
    have h2 : C.le W y x := by simpa using hy.1
    exact ⟨by simpa using C.le_trans h1 h2, hz.2⟩
  have hself : ∀ x ∈ K, x ∈ C.Jminus W {x} ∩ K := fun x hx =>
    ⟨by simpa using C.le_refl (hKW hx), hx⟩
  let 𝒮 : Set (Set M) :=
    {A | A ⊆ K ∧ A.Nonempty ∧ IsClosed A ∧ ∀ x ∈ A, C.Jminus W {x} ∩ K ⊆ A}
  have hK𝒮 : K ∈ 𝒮 := ⟨subset_rfl, hne, hKcl, fun _ _ => inter_subset_right⟩
  have hchains : ∀ c ⊆ 𝒮, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ 𝒮, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain hcne
    have hdir : DirectedOn (· ⊇ ·) c := fun A hA B hB => by
      rcases eq_or_ne A B with rfl | hAB
      · exact ⟨A, hA, subset_rfl, subset_rfl⟩
      rcases hchain hA hB hAB with h | h
      · exact ⟨A, hA, subset_rfl, h⟩
      · exact ⟨B, hB, h, subset_rfl⟩
    haveI : Nonempty c := hcne.to_subtype
    refine ⟨⋂₀ c, ⟨?_, ?_, isClosed_sInter fun A hA => (hc hA).2.2.1, ?_⟩,
      fun A hA => sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (sInter_subset_of_mem hA).trans (hc hA).1
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
        (fun A hA => (hc hA).2.1) (fun A hA => hK.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    · intro x hx y hy
      exact mem_sInter.2 fun A hA => (hc hA).2.2.2 x (mem_sInter.1 hx A hA) hy
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty 𝒮 hchains K hK𝒮
  obtain ⟨hmK, ⟨p, hp⟩, -, hmdown⟩ := hm.prop
  have heq : ∀ x ∈ m, m = C.Jminus W {x} ∩ K := fun x hx => by
    have hx𝒮 : C.Jminus W {x} ∩ K ∈ 𝒮 :=
      ⟨inter_subset_right, ⟨x, hself x (hmK hx)⟩, hJ x (hmK hx), hdown x (hmK hx)⟩
    exact Subset.antisymm (hm.2 hx𝒮 (hmdown x hx)) (hmdown x hx)
  refine ⟨p, hmK hp, ?_⟩
  rw [← heq p hp]
  refine eq_singleton_iff_unique_mem.2 ⟨hp, fun z hz => ?_⟩
  have hzp : z ∈ C.Jminus W {p} ∩ K := by rw [← heq p hp]; exact hz
  have hpz : p ∈ C.Jminus W {z} ∩ K := by rw [← heq z hz]; exact hp
  have h1 : C.le W z p := by simpa using hzp.1
  have h2 : C.le W p z := by simpa using hpz.1
  exact hcaus h1 h2

/-- **A compact set has a `≤`-minimal point** (`M` causal, `J⁻(x)` closed, `M` Hausdorff): Zorn on
the non-empty closed down-sets of `K`, chains having non-empty intersection by compactness. This
replaces the design's "minimise a Geroch time" (no time function is needed). The case `W = ⊤` of
`exists_minimal_of_isCompact_on`. -/
theorem exists_minimal_of_isCompact [T2Space M] (hcaus : C.IsCausal)
    (hcl : ∀ x, IsClosed (C.Jminus ⊤ {x})) {K : Set M} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ p ∈ K, ∀ q ∈ K, C.le ⊤ q p → q = p := by
  obtain ⟨p, hpK, hp⟩ := exists_minimal_of_isCompact_on (W := ⊤) hcaus hK (fun _ _ => trivial)
    hne fun x _ => (hcl x).inter hK.isClosed
  refine ⟨p, hpK, fun q hq hqp => ?_⟩
  have hq' : q ∈ C.Jminus ⊤ {p} ∩ K := ⟨by simpa using hqp, hq⟩
  rw [hp] at hq'
  exact hq'

end Causality

end Causal
