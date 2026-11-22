import Causal.GluingModels.Tools
import CausalScaffold.GerochCauchy

/-!
# Gluing inventory (DEC-167), model layer: the scaffold's chronological Minkowski space

No paper label is certified by this file. The one concrete causality of the scaffold is
chronological Minkowski space `chronoMinkowski n = (minkowski n).reflChrono`
(`CausalScaffold.GerochCauchy`, `x ≤ y` iff `x = y` or `x ≪ y`). It glues hereditarily, through a
generic fact: `reflChrono C` glues on `W` when `C` does (its chronological half is that of `C`,
its causal half the reflexive closure of it).

This module imports a scaffold module (`CausalScaffold.GerochCauchy`, which has an unproved,
tagged declaration elsewhere in its file); it is kept apart so that the rest of the inventory
graduates without it. The declarations here are proved in full (axioms: `propext`,
`Classical.choice`, `Quot.sound`).

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used |

## SCOPE (disclosed)

* No definition changes; OQ-95 and OQ-96 are not decided here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-- **The reflexive chronological causality glues on `W` when `C` does.** -/
theorem reflChrono_absolutelyMinimalOn {M : Type*} [TopologicalSpace M] {C : Causality M}
    {W : Opens M} (h : C.AbsolutelyMinimalOn W) : C.reflChrono.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  refine ⟨fun hxy => ?_, fun hxy => (h S hS V hV x y).2 hxy⟩
  rcases hxy with ⟨rfl, hx⟩ | hlt
  · obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
    exact TransGen.single ⟨O, hO, Or.inl ⟨rfl, hx, hxO⟩⟩
  · exact TransGen.mono (fun a b ⟨O, hO, hab⟩ => ⟨O, hO, Or.inr hab⟩) ((h S hS V hV x y).2 hlt)

theorem reflChrono_hereditary {M : Type*} [TopologicalSpace M] {C : Causality M}
    (h : ∀ W : Opens M, C.AbsolutelyMinimalOn W) :
    ∀ W : Opens M, C.reflChrono.AbsolutelyMinimalOn W := fun W =>
  reflChrono_absolutelyMinimalOn (h W)

/-- **Chronological Minkowski space glues hereditarily.** -/
theorem chronoMinkowski_hereditary (n : ℕ) :
    ∀ W : Opens (Minkowski n), (chronoMinkowski n).AbsolutelyMinimalOn W :=
  reflChrono_hereditary (forall_of_causallyArcConnected minkowski_causallyArcConnected)

theorem chronoMinkowski_minimal (n : ℕ) : (chronoMinkowski n).AbsolutelyMinimal :=
  absolutelyMinimal_of_forall (chronoMinkowski_hereditary n)

end GluingModels

end Causal
