import Causal.Cauchy

/-!
# Time reversal of Cauchy surfaces of an open set

No label is marked. A model-free fact hoisted out of `Causal.Splitting` (which imports
`Causal.Flat.IsomCausal`, a model) into the ETT layer, so that a layer-1 module, and Sbierski's
Lemma 3.3 (`Causal.CBG.Injective`), can use it (T-abs-hoist-time-function, kb/0047): a set is a
Cauchy surface of an open `W` for `C.dual` iff it is one for `C` (`dual_isCauchySurfaceOn`,
kb/0002), from the one direction `IsCauchySurfaceOn.of_dual`. Moved verbatim, same full names
(`Causal.Causality.*`), same statements; `Causal.Splitting` imports this module, so every former
user resolves them unchanged.

> A Cauchy surface in $M$ is a subset $S\subset M$ such that every causal curve of $M$ meets $S$
> exactly once. (`def:cauchy_surface`, `ETT.tex:999–1000`)

The definition does not orient the curves, so it is invariant under time reversal; this module is
that invariance for the library's reading of the definition (`Causal.Cauchy`, DEC-14: inextensible
curves of an open set), in the convention of `README.md` ("Past from future": every property has
its `dual_…` lemma).

## What is proved

* `IsCauchySurfaceOn.of_dual`: a Cauchy surface of `W` for `C.dual` is one for `C` (an
  inextensible curve of `C` run backwards is one of `C.dual`, `Inextensible.dual_reverse`, with
  the same image).
* `dual_isCauchySurfaceOn`: the equivalence (`C.dual.dual = C`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| none: any causality on any topological space, any open `W`, any `S` | ✓ |

## SCOPE (disclosed)

* The private helper `image_neg_reverse` (the image of `t ↦ c (-t)` over `-I` is `c '' I`) moves
  with `of_dual`, whose only user it is; as a private declaration its internal name records the
  module, so it is the one constant of the move whose name changes (it is not addressable from
  outside either module).
* Nothing else of `Causal.Splitting` is model-free and needed in layer 1 by this target; the rest
  stays there.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {S : Set M}

omit [TopologicalSpace M] in
private theorem image_neg_reverse (c : ℝ → M) (I : Set ℝ) : (fun t => c (-t)) '' (-I) = c '' I := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨-t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨-t, by simpa using ht, by simp⟩

theorem IsCauchySurfaceOn.of_dual {W : Opens M} (h : C.dual.IsCauchySurfaceOn W S) :
    C.IsCauchySurfaceOn W S := by
  intro I c hc
  have := h _ _ hc.dual_reverse
  rwa [image_neg_reverse] at this

/-- Time reversal preserves Cauchy surfaces of an open set. -/
theorem dual_isCauchySurfaceOn {W : Opens M} :
    C.dual.IsCauchySurfaceOn W S ↔ C.IsCauchySurfaceOn W S :=
  ⟨IsCauchySurfaceOn.of_dual, fun h => IsCauchySurfaceOn.of_dual (C := C.dual) h⟩

end Causality

end Causal
