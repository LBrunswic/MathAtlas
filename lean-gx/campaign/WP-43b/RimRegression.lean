import GXScaffold.BTZ.Surgery
/-! WP-43b round 2 — regression check for AUDIT-2 B1 (not a module; run with `lake env lean`).
The auditor's attack raised the vertex of a datum above `sup τ_Σ` and fed `rim` a discontinuous
`τ_Σ'`. Under the repaired antecedent this is impossible: at a raised vertex no `τ_Σ'` satisfies
both the shaft bound and the graph condition, so `rim` says nothing there. -/
open scoped Real
open Set
namespace GX.E0Surgery
open E0

theorem rim_regression_raised_vertex {M : Type} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    {S : Set M} (D : SpearSurgeryDatum M S) {v' : ℝ} (hvv : D.v ≤ v')
    (hT : ∀ z : ℂ, ‖z‖ ≤ D.R → D.τS z < v') (τS' : ℂ → ℝ)
    (hshaft : ∀ z : ℂ, ‖z‖ ≤ D.R → v' + D.R / 2 < τS' z)
    (hgraph : ∀ x ∈ E0Spear.spear v' D.R, (D.ψ (paperInY x) ∈ S ↔ x.1 = τS' x.2)) : False := by
  have hsub : E0Spear.spear v' D.R ⊆ E0Spear.spear D.v D.R := E0Spear.spear_mono hvv le_rfl
  have h := eqOn_closedBall_of_rim_antecedent M (fun x hx => D.graph x (hsub hx)) hgraph hshaft
    (z := 0) (by simp [D.pos.le])
  have h1 := hT 0 (by simp [D.pos.le])
  have h2 := hshaft 0 (by simp [D.pos.le])
  linarith [D.pos]

end GX.E0Surgery

#print axioms GX.E0Surgery.rim_regression_raised_vertex
