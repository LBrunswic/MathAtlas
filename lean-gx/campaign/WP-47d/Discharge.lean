import GXScaffold.BTZ.MixedDiamond

/-! WP-47d: the one-line discharges of the AbsMax leaf and of Uniformization's
`E0MixedDiamondsCompact` (its body, under the premises its consumers carry). Not a module. -/

namespace GX

open E0CBG E0Spear E0AbsMax

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- The statement of `GX.E0AbsMax.E0Pushout.isCompact_diamond_mixed`, verbatim. -/
example (_hGH : (CE M).GloballyHyperbolic)
    (_hmax : IsE0CauchyMaximal M) {N : Causal.Flat.FlatSpacetime.{0} 2} (_hN : Causal.Flat.GH N)
    {f : e0RegMFlat M → N} (P : E0Pushout M N f) {p q : P.carrier} (_hp : p ∈ S0 P.carrier)
    (_hq : q ∉ S0 P.carrier) : IsCompact ((CE P.carrier).diamond ⊤ p q) :=
  E0MixedDiamond.isCompact_diamond_mixed _hGH _hmax _hN P _hp _hq

/-- The body of `GX.E0MixedDiamondsCompact M` (`GXScaffold.BTZ.Uniformization`), under GH and
Cauchy-maximality of `M`. -/
example (hGH : (CE M).GloballyHyperbolic) (hmax : IsE0CauchyMaximal M) :
    ∀ {N : Causal.Flat.FlatSpacetime.{0} 2}, Causal.Flat.GH N → ∀ {f : e0RegMFlat M → N}
      (P : E0Pushout M N f) {p q : P.carrier}, p ∈ S0 P.carrier → q ∉ S0 P.carrier →
        IsCompact ((CE P.carrier).diamond ⊤ p q) :=
  fun {_N} hN {_f} P {_p _q} hp hq => E0MixedDiamond.isCompact_diamond_mixed hGH hmax hN P hp hq

/-- `cor_abs_max_C1` of AbsMax, its statement verbatim, with no `sorry` beneath. -/
example (hGH : (CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : IsE0CauchyMaximal M) :
    Causal.Flat.GH (e0RegMFlat M) ∧ Causal.Flat.IsCauchyComplete 2 (e0RegMFlat M) ∧
      Causal.Flat.AbsMax (fun _ => True) (e0RegMFlat M) :=
  E0MixedDiamond.cor_abs_max_C1_spear hGH hCC hmax

end GX

#print axioms GX.E0MixedDiamond.isCompact_diamond_mixed
#print axioms GX.E0MixedDiamond.prop_abs_max_C1_spear
#print axioms GX.E0MixedDiamond.cor_abs_max_C1_spear
#print axioms GX.E0MixedDiamond.vertical_noLimit
#print axioms GX.E0MixedDiamond.SpearChart.exit
#print axioms GX.E0MixedDiamond.affine_noLimit
#print axioms GX.E0MixedDiamond.circle_trick
#print axioms GX.E0MixedDiamond.exists_bound_axis
#print axioms GX.E0MixedDiamond.globallyHyperbolic_pushout
#print axioms GX.E0MixedDiamond.absMax_e0RegM_spear
