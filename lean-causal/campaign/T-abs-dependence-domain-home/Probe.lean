import Causal.DependenceDomain
import Causal.NestedCausalities

/-!
Probe of T-abs-dependence-domain-home (DEC-198). Run from `lean-causal/`:
`taskset -c 0-11 lake env lean campaign/T-abs-dependence-domain-home/Probe.lean`.

1. The renamed declarations and the redirected `dependenceDomainOn` family: their statements and
   axioms (standard axioms only, or none).
2. The deprecated aliases: each has the type of its new name (the definition is `rfl`-equal to the
   new one), and each use of an old name is a deprecation warning (`#guard_msgs`), hence an error
   in the strict library.
3. Dot notation: `C.dependenceDomain W S` is `Causality.dependenceDomain C W S`.
-/

open Causal TopologicalSpace

/-! ### 1. The new names -/

#check @Causal.Causality.dependenceDomain
#check @Causal.Causality.mem_dependenceDomain
#check @Causal.Causality.dependenceDomain_subset
#check @Causal.Causality.subset_dependenceDomain
#check @Causal.Causality.dependenceDomain_eq_of_isCauchySurfaceOn
#check @Causal.Causality.dependenceDomainOn

#print axioms Causal.Causality.dependenceDomain
#print axioms Causal.Causality.mem_dependenceDomain
#print axioms Causal.Causality.dependenceDomain_subset
#print axioms Causal.Causality.subset_dependenceDomain
#print axioms Causal.Causality.dependenceDomain_eq_of_isCauchySurfaceOn
#print axioms Causal.Causality.dependenceDomainOn
#print axioms Causal.Causality.dependenceDomainOn_subset
#print axioms Causal.Causality.subset_dependenceDomainOn
#print axioms Causal.Causality.dependenceDomainOn_eq_of_isCauchySurfaceOn
#print axioms Causal.Causality.dependenceDomainOn_subset_of_nested
#print axioms Causal.Causality.GloballyHyperbolic.dependenceDomainOn_subset_of_nested
#print axioms Causal.not_dependenceDomain_nested_bare

/-! ### 2. The deprecated aliases -/

#print axioms Causal.Flat.dependenceDomain
#print axioms Causal.Flat.mem_dependenceDomain
#print axioms Causal.Flat.dependenceDomain_subset
#print axioms Causal.Flat.subset_dependenceDomain
#print axioms Causal.Flat.dependenceDomain_eq_of_isCauchySurfaceOn

set_option linter.deprecated false in
example : @Causal.Flat.dependenceDomain.{0} = @Causal.Causality.dependenceDomain.{0} := rfl

set_option linter.deprecated false in
example : @Causal.Flat.mem_dependenceDomain.{0} = @Causal.Causality.mem_dependenceDomain.{0} := rfl

set_option linter.deprecated false in
example : @Causal.Flat.dependenceDomain_subset.{0} =
    @Causal.Causality.dependenceDomain_subset.{0} := rfl

set_option linter.deprecated false in
example : @Causal.Flat.subset_dependenceDomain.{0} =
    @Causal.Causality.subset_dependenceDomain.{0} := rfl

set_option linter.deprecated false in
example : @Causal.Flat.dependenceDomain_eq_of_isCauchySurfaceOn.{0} =
    @Causal.Causality.dependenceDomain_eq_of_isCauchySurfaceOn.{0} := rfl

/--
warning: `Causal.Flat.dependenceDomain` has been deprecated: Use `Causal.Causality.dependenceDomain` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.dependenceDomain` to `Causality.dependenceDomain x`).
-/
#guard_msgs in
example {M : Type} [TopologicalSpace M] (C : Causality M) (W : Opens M) (S : Set M) :
    Causal.Flat.dependenceDomain C W S ⊆ W := fun _ hp => hp.1

/--
warning: `Causal.Flat.mem_dependenceDomain` has been deprecated: Use `Causal.Causality.mem_dependenceDomain` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.mem_dependenceDomain` to `Causality.mem_dependenceDomain x`).
-/
#guard_msgs in
example {M : Type} [TopologicalSpace M] (C : Causality M) (W : Opens M) (S : Set M) (p : M)
    (hp : p ∈ C.dependenceDomain W S) : p ∈ W :=
  (Causal.Flat.mem_dependenceDomain.1 hp).1

/-! ### 3. Dot notation -/

example {M : Type} [TopologicalSpace M] (C : Causality M) (W : Opens M) (S : Set M) :
    C.dependenceDomain W S = Causality.dependenceDomain C W S := rfl

example {M : Type} [TopologicalSpace M] (C : Causality M) (W : Opens M) (S : Set M) :
    C.dependenceDomainOn W S = C.dependenceDomain W S := rfl
