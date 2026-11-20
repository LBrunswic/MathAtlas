import Causal.Cauchy

/-!
# The domain of dependence of a set in an open set, for any causality

No label is certified. The definition is the one the Barbot campaign gave in
`Causal.Flat.LipschitzGraph` (`docs/BARBOT-WAVE3.md` §1 D) for a general causality; it is hoisted
out of that model module with its model-free lemmas (programme target `T-abs-hoist-model-free`,
kb/0047), so that a layer-1 module may use it: this module imports `Causal.Cauchy` and no model.
The names keep their namespace `Causal.Flat`, so that every user resolves unchanged.

> […] the so-called Cauchy domain, or domain of
> dependence of the spacelike hypersurface $S$ as defined in
> \cite{mess}, \cite{ande} or \cite{bonsante}: it is the
> open set formed by points such that every lightlike geodesic through the
> point intersects $S$. (Barbot, `papers/barbot/legacy/labeled/GHFspace.tex:2519–2523`)

## What is proved (no `sorry` in this file)

* `Flat.dependenceDomain C W S`, **the domain of dependence `D(S)` of `S` in the open `W`**: the
  points of `W` every inextensible causal curve of `W` through which meets `S` (two-sided).
* `Flat.mem_dependenceDomain` (the defining property, by `Iff.rfl`), `Flat.dependenceDomain_subset`
  (`D(S) ⊆ W`), `Flat.subset_dependenceDomain` (`S ⊆ D(S)` for `S ⊆ W`),
  `Flat.dependenceDomain_eq_of_isCauchySurfaceOn` (a Cauchy surface of `W` has `D(S) = W`).

## Hypothesis checklist

| source | here |
|---|---|
| Barbot: `S` a spacelike hypersurface; "every lightlike geodesic" | ⚠ reading (the Barbot campaign's, as used in `Causal.Flat.Cla.CoverMax`): any set `S`, any causality; every inextensible causal curve of `W` (DEC-11, DEC-13), as in DEC-14's Cauchy surfaces; for an entire graph in `𝐌ⁿ` the causal-line form is proved (`Flat.meets_of_mem_dependenceDomain`, `Flat.mem_dependenceDomain_of_meets`) |
| Barbot: `D(S)` open | not stated in general (`Causal.Flat.LipschitzGraph` proves it for the hyperboloid and uses `interior` elsewhere) |

## SCOPE (disclosed)

* Moved verbatim from `Causal.Flat.LipschitzGraph` (§ D, the definition and its four general
  lemmas): names, statements and proofs unchanged. `Causal.Flat.LipschitzGraph` imports this
  module and keeps the Minkowski results on `D(S)`.
* `Causal.NestedCausalities` had re-defined it as `Causality.dependenceDomainOn`; that name is now
  an `abbrev` of `Flat.dependenceDomain`, so the statements written with it are unchanged.
* `D⁺(S)` and `D⁻(S)` are not defined.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat

open Set TopologicalSpace

/-- **The domain of dependence** `D(S)` of `S` in the open `W`, for a general causality: the
points `p ∈ W` such that every inextensible causal curve of `W` through `p` meets `S`. -/
def dependenceDomain {M : Type*} [TopologicalSpace M] (C : Causality M) (W : Opens M)
    (S : Set M) : Set M :=
  {p | p ∈ W ∧ ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → p ∈ c '' I →
    (c '' I ∩ S).Nonempty}

section dependence

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {W : Opens M} {S : Set M}

theorem mem_dependenceDomain {p : M} : p ∈ dependenceDomain C W S ↔ p ∈ W ∧
    ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → p ∈ c '' I → (c '' I ∩ S).Nonempty :=
  Iff.rfl

theorem dependenceDomain_subset : dependenceDomain C W S ⊆ W := fun _ hp => hp.1

theorem subset_dependenceDomain (hSW : S ⊆ W) : S ⊆ dependenceDomain C W S :=
  fun p hp => ⟨hSW hp, fun _ _ _ hpc => ⟨p, hpc, hp⟩⟩

/-- A Cauchy surface of `W` has all of `W` for domain of dependence. -/
theorem dependenceDomain_eq_of_isCauchySurfaceOn (h : C.IsCauchySurfaceOn W S) :
    dependenceDomain C W S = W :=
  Subset.antisymm dependenceDomain_subset fun _ hp => ⟨hp, fun I c hc _ => by
    obtain ⟨x, hx, -⟩ := h I c hc
    exact ⟨x, hx⟩⟩

end dependence

end Causal.Flat
