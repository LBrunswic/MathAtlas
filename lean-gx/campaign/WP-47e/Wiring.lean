import GXScaffold.BTZ.Uniformization
import GXScaffold.BTZ.FutureRay

/-! Wiring check (not a module): the statement of `GX.btzTilde_null_supset`
(`GXScaffold.BTZ.Uniformization`, whose body carries the file's tagged `sorry`) proved here from
`GX.futureRay_null_supset` and `GX.btzTilde_supset_of_reg`, with no `sorry`. The master session can
replace that body by the four lines below once `Uniformization` imports `GXScaffold.BTZ.FutureRay`. -/

namespace GX

open Set Function E0CBG E0Spear E0AbsMax

attribute [local instance] btzE0Structure in
theorem btzTilde_null_supset_wired {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    (_hGH : (CE M).GloballyHyperbolic)
    (_hmax : IsE0CauchyMaximal M) (x₀ : e0RegMFlat M)
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : Causal.Flat.IsDevelopingPair x₀ D ρ) (_hD : Injective D)
    (hfc : letI := Causal.Flat.flatCoverChartedSpace 2 (e0RegMFlat M) x₀
     haveI := Causal.Flat.hasGroupoid_flatCover (d := 2) (e0RegMFlat M) x₀
     IsFutureComplete (Causal.Flat.flatCausality 2 (Causal.UniversalCover (e0RegMFlat M) x₀)) D)
    (hrays : ∀ p ∈ S0 M, ∃ γ : ℝ → M, E0Spear.IsFullFutureBTZRay p γ) :
    letI := E0Bridge.e0SingularGXStructure M
    haveI := ChartedSpace.locPathConnectedSpace E0Y M
    ∀ {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
      {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ
        DInfty × ℝ}, (∀ e, orbitMk (GammaA (2 * Real.pi)) (Φ e) = e.base) →
      ∀ d : BTZTildeData M (E0Bridge.basePt x₀) Φ, d.IsChartwise →
        (∀ z : E0Bridge.regTilde (E0Bridge.basePt x₀),
          d.D (z : MaxBranchedCover (E0Bridge.sing M) (E0Bridge.basePt x₀)) =
            D (E0Bridge.regTildeHomeo (E0Bridge.basePt x₀) z)) →
        ∀ x : d.Space, (d.toNat x).base ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M →
          ∀ m ∈ (Causal.minkowski 2).Jplus ⊤ {d.D x}, m ∉ (Causal.minkowski 2).Iplus ⊤ {d.D x} →
            m ∈ d.D '' d.causality.Jplus ⊤ {x} := by
  letI := E0Bridge.e0SingularGXStructure M
  haveI := ChartedSpace.locPathConnectedSpace E0Y M
  intro yN Φ _hΦ d hch hd x hxs m hm hmI
  exact futureRay_null_supset hrays d hch
    (fun y hy => (btzTilde_supset_of_reg x₀ D ρ hpair hfc d hd y hy).1) x hxs m hm hmI

end GX

#print axioms GX.btzTilde_null_supset_wired
#print axioms GX.futureRay_halfLine
#print axioms GX.futureRay_null_supset
