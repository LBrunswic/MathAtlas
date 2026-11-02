# After wave 5: two items from the BBS session (papers/bbs/REVIEW.md §G–§H)

## (2) Shrinking the DEC-69 named external `TroyanovSuspensionTheorem` (GXScaffold.SingularII.Models:885)
It bundles (T) Troyanov's spherical cone S² with angles θ, (S) its suspension M a singular (G,X)-manifold with centre O,
(F) `SuspensionCexFacts` (:812). With BBS's L0 (GX.Suspension.Conic/Celestial) PLUS the spherical instance
(S³/SO(4), links S²/SO(3)): (S), (F).connected, (F).mem_sing, (F).exists_ne are discharged; (F).rigid, (F).rot are not.
The external shrinks to: "a singular (SO(3),S²)-surface ≅ S² with angles θ exists" + the two automorphism facts.

## (3) Tachyons and photons for `ex:quotient_base` (Quotient.lean:187–200) — a gx package
Γ = ℤ in `existsUnique_aeGXQuotient` (Quotient.lean:833), not GammaA. v spacelike (tachyon: g a boost fixing x₀+ℝv)
or null (photon: g a null rotation); w : ℝ → P∖0 a 2π-periodic Euclidean parametrisation of the rays of a complement P
of ℝv; ĝ the lift of g's ray action fixing the lifts of its fixed rays (4 / 2).
Action 1·(r,θ,z) = (r‖g w(θ)‖/‖w(ĝθ+2πm)‖, ĝθ+2πm, z); D(r,θ,z) = x₀ + z v + r w(θ), D(1·x) = g·D(x).
m ≠ 0: free on {r>0} (ĝθ−θ ∈ (−π/2,π/2) tachyon, (−π,π) photon); hdisc; unique maximal a.e. (Isom₀,E^{1,2})-structure,
sing ⊆ π{r=0}, holonomy g; BBS degree 2|m|; positive iff ĝθ ≥ θ on the lifted i⁺ arcs (l.908–922). m = ±1: tachyon,
photon; |m| ≥ 2 branched covers; m = 0 on one arc: BTZ-like/Misner (boost), extreme BTZ = E₀/cuspidal (null) — match
with gx's misner_btz/btz_* is the Affine bridge. Caveat: pin w's orientation to BBS l.1229–1233.
