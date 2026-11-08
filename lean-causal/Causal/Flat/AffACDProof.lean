import Causal.Flat.AffACDTriang
import Causal.Flat.AffACDLocal

/-!
# `Causal.Flat.AffACDProof` — Auslander–Carrière–Dal'bo for discrete subgroups of `Aff(n, ℝ)`, and the Isom form as a corollary

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Theorem 5.1 (cited by Barbot as `cardal` Theorem 1.2.1), in the PRINTED generality (DEC-123).
Label certified (line in `papers/barbot/legacy/labeled/GHFspace.tex`):

* **`bthm:ausl`** — `GHFspace.tex:1697` (`affAuslanderCarriereDalbo_euclidean`: every discrete
  `Γ ≤ Aff(n, ℝ)`; `affAuslanderCarriereDalbo`: any finite-dimensional real normed `V`)

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent.
> In particular, $\Gamma_{nd} = L^{-1}(G_{0} \cap L(\Gamma))$
> is nilpotent. (l.1699–1703)

* `affAuslanderCarriereDalbo V`: for every finite-dimensional real normed space `V`, every
  discrete `Γ ≤ V ≃ᵃ[ℝ] V` has `G₀` and `Γ_nd` nilpotent (`AffAusConclusion`, `Flat/AffACDBase`).
* `affAuslanderCarriereDalbo_euclidean n`: the printed `Aff(n, ℝ)`, `V = EuclideanSpace ℝ (Fin n)`.
* `auslanderCarriereDalbo_viaAff d`: the DEC-36 external `AuslanderCarriereDalbo d` (Isom form,
  `Flat/Externals`), re-derived from the affine theorem (`auslanderCarriereDalbo_of_aff`); the
  DEC-121 Lorentz proof `auslanderCarriereDalbo` (`Flat/ACDProof`) is not touched.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` discrete in `Aff(n, ℝ)` (l.1699) | ✓ carried: `AffDiscrete Γ` (topology of `Aff(n, ℝ) ⊆ GL(n + 1, ℝ)`) |
| closure of `L(Γ)` in `GL(n, ℝ)` (l.1700–1701) | ✓ carried: closure in `(V →L[ℝ] V)ˣ` |
| `n` | ✓ any; any finite-dimensional real normed `V` |

## SCOPE (disclosed)

* Sorry-free, axiom-clean (`#print axioms affAuslanderCarriereDalbo`,
  `affAuslanderCarriereDalbo_euclidean`, `auslanderCarriereDalbo_viaAff`:
  `[propext, Classical.choice, Quot.sound]`); the leaves `Flat/AffACDTriang`, `Flat/AffACDLocal`
  are sorry-free (DEC-123 provers, 2026-11-08).
* `GL(n, ℝ)` carries the operator-norm topology (mathlib's units topology, equal to it for a
  complete normed ring), and `Aff(n, ℝ)` the topology of its embedding in `GL(n + 1, ℝ)`
  (`affTopology`, `Flat/AffACDBase`); the Isom discreteness of `AuslanderCarriereDalbo d` implies
  it (`affDiscrete_map_isom`, `Flat/AffACDLocal`).
* `G₀` is used through the subgroup it generates (`G₀` is a subgroup), as in `Flat/Externals`.
* The route is Zassenhaus' (survey §2.2 T2), with the uniform class bound proved by elementary
  linear algebra (`Flat/AffACDTriang`), not by a Lie-algebra log chart.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-123.
-/

namespace Causal.Flat

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Auslander–Carrière–Dal'bo** (`bthm:ausl`, printed generality): for every discrete subgroup
`Γ` of `Aff(V)`, the identity component `G₀` of the closure of `L(Γ)` in `GL(V)` is nilpotent,
and `Γ_nd = Γ ∩ L⁻¹(G₀)` is nilpotent. -/
theorem affAuslanderCarriereDalbo : AffAuslanderCarriereDalbo V :=
  affAuslanderCarriereDalbo_of_classBound (affNearOneClassBound (V × ℝ))

/-- **`bthm:ausl` for `Aff(n, ℝ)`**, as printed. -/
theorem affAuslanderCarriereDalbo_euclidean (n : ℕ) :
    AffAuslanderCarriereDalbo (EuclideanSpace ℝ (Fin n)) :=
  affAuslanderCarriereDalbo _

/-- **The DEC-36 Isom form, as a corollary of the printed affine form** (DEC-123). -/
theorem auslanderCarriereDalbo_viaAff (d : ℕ) : AuslanderCarriereDalbo d :=
  auslanderCarriereDalbo_of_aff (affAuslanderCarriereDalbo _)

end Causal.Flat
