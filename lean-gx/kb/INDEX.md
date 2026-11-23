# Knowledge base — working in `lean-gx`

Read `lean-causal/kb/INDEX.md` first: its house rules and pitfalls about mathlib at this pin apply
here (0004 names at this pin, 0005 build your own module, 0006 docstring contract, 0007
neighbourhoods not sequences, 0010 dot notation, 0011 never outrun the paper, 0015 graduation
checklist, 0016 namespace shadowing, 0018 charts and maximal atlases). The entries below are
gx-specific. One fact per entry; propose one when you finish.

| id | kind | entry |
|---|---|---|
| [0001](entries/0001-btz-terminology.md) | convention | gx's BTZ is BBS's *extreme* BTZ-like; BBS's BTZ-like is gx's `misner_btz` |
| [0002](entries/0002-pi1-product-order.md) | pitfall | mathlib's π₁ product runs the right factor first |
| [0003](entries/0003-polygonal-loops.md) | pattern | Relations among polygonal loops in a planar subspace need no explicit homotopy |
| [0004](entries/0004-annulus-and-winding.md) | pattern | The annulus lemma, and winding numbers as holonomies for counterexamples |
| [0005](entries/0005-cone-angle-invariance.md) | pattern | The cone angle of a conical model is an invariant of the apex |
| [0006](entries/0006-spherical-models.md) | pattern | The spherical models (`RaySphere`, `SpecialOrth`) and the Thurston suspension |
| [0007](entries/0007-thurston-atlas-transport.md) | pattern | Reusing `ConicStructure.mk_mem_sing` for the Thurston atlas: transport along `liftSO` |
| [0008](entries/0008-rw-motive-defeq-endpoints.md) | pitfall | `rw` fails on paths whose endpoints are defeq but not syntactic |
| [0009](entries/0009-van-kampen-chained.md) | pattern | A glued van Kampen invariant can be glued again: one gluing per bad point |
| [0010](entries/0010-infinitesimal-loops.md) | pattern | Detect an infinitesimal non-null loop with an invariant valued in a quotient group |
| [0011](entries/0011-maximal-atlas-morphism-tools.md) | pattern | Two tools for building cone spheres from charts of models (the football) |
| [0012](entries/0012-so3-from-frames.md) | pattern | Elements of SO(3) from matrices and orthonormal frames |
| [0013](entries/0013-chart-without-inverse.md) | pattern | A chart need not come with a continuous inverse: compactness gives it |
| [0014](entries/0014-xtheta-chart-on-open.md) | pattern | X_θ-charts onto a proper open subset of the model |
| [0015](entries/0015-doubled-convex-body.md) | pattern | A doubled convex body is 𝕊², through the gauge rescale |
| [0016](entries/0016-cone-charts-via-developing.md) | pattern | Comparing cone charts through the developing map |
| [0017](entries/0017-regular-is-cone-2pi.md) | pattern | A regular point is a cone point of angle 2π: rotate a chart onto the apex of C_{2π} |
| [0018](entries/0018-so-transitive-reflections.md) | pattern | SO(V) is transitive on the unit sphere (dim ≥ 2): compose two reflections |
| [0019](entries/0019-insertnth-removenth.md) | pitfall | Adding or removing a marked point: Fin.insertNth / Fin.removeNth, and one rfl per index |
| [0020](entries/0020-sph-polygon.md) | pattern | Convex spherical s-gons: GX.SphPolygon, built from the polar polygon inscribed in a circle |
| [0021](entries/0021-triangle-tools-are-generic.md) | pattern | TroyanovTriangle's generic lemmas sit in namespace GX.SphTriangle: reuse them for s-gons |
| [0022](entries/0022-star-polygon-double.md) | pattern | The double of a polygon, convex or not: GX.StarPolygon; reflex vertices via GX.StarFrames |
| [0023](entries/0023-union-of-convex-disc.md) | pattern | A union of two convex bodies with a common interior point is a closed disc |
| [0024](entries/0024-fin-cases-literal-pitfall.md) | pitfall | `fin_cases i` yields ⟨k, _⟩ indices that literal-index lemmas do not match |
| [0025](entries/0025-troyanov-condition-c.md) | pattern | Troyanov's condition of record is Theorem C's (GX.TroyanovAngleConditionC); the printed one is C plus χ' ≤ θ_j |
| [0026](entries/0026-troyanov-constructions-under-c.md) | pattern | The strict Troyanov constructions already work under Theorem C's condition; only s ≥ 5 with an angle above 2π is open |
| [0027](entries/0027-hs-d-is-gx-hs-d-raysphere-causal-minkows.md) | pattern | HS^d is GX.HS d = RaySphere (Causal.Minkowski d), acted on by Causal.Flat.lorentz d (GXScaffold.BBS. |
| [0028](entries/0028-rigidity-of-a-normalised-linear-action-o.md) | pattern | Rigidity of a normalised linear action on S(V): |
| [0029](entries/0029-transitivity-of-so-0-1-d-on-the-pieces-o.md) | pattern | Transitivity of SO_0(1,d) on the pieces of HS^d, d >= 2: |
| [0030](entries/0030-a-bbs-layer-module-outside-gx-btz-lorent.md) | pattern | A BBS-layer module outside GX/{BTZ,Lorentz}/ may not import Causal.* (scripts/causal_import_gate.py) |
| [0031](entries/0031-pitfall.md) | pitfall | Pitfall: |
| [0032](entries/0032-pitfall.md) | pitfall | Pitfall: |
| [0033](entries/0033-a-chartedspace-over-a-space-homeomorphic.md) | pattern | A ChartedSpace over a space homeomorphic to a charted one: |
| [0034](entries/0034-rays-over-singular-points-of-a-thurston.md) | pattern | Rays over singular points of a Thurston suspension are singular: |
| [0035](entries/0035-reading-a-e.md) | pattern | Reading a.e. |
| [0036](entries/0036-rotations-of-the-cone-c.md) | pattern | Rotations of the cone C_θ: |
| [0037](entries/0037-a-local-isomorphism-of-a-thurston-suspen.md) | pattern | A local isomorphism of a Thurston suspension fixing the centre is a suspension near O: |
| [0038](entries/0038-topological-rigidity-of-the-centre.md) | pattern | Topological rigidity of the centre: |
| [0039](entries/0039-what-remains-of-cex-start-singular-manif.md) | pattern | What remains of cex:start_singular_manifold_homeomorphic beyond Troyanov is exactly Aut(Σ) = {Id} (G |
| [0040](entries/0040-rp1-is-gx-rp1-mathlib-s-circle-the-line.md) | pattern | RP1 is GX.RP1 = mathlib's Circle, the line R z being z / conj z (GX.RP1.mk, mk_eq_mk_iff). |
| [0041](entries/0041-g-is-gx-gtilde-a-subgroup-of-circledeg1l.md) | pattern | G~ is GX.GTilde, a subgroup of CircleDeg1Lift units: |
| [0042](entries/0042-every-lift-of-g-in-sl-2-r-to-r-commutes.md) | pattern | Every lift of g in SL(2,R) to R commutes with t -> t + 1. |
| [0043](entries/0043-the-holonomy-of-an-rp1-circle-lifted-to.md) | pattern | The holonomy of an RP1-circle lifted to G~ is GX.HasLiftedHolonomy: |
| [0044](entries/0044-change-of-model-along-an-equivariant-map.md) | pattern | Change of model along an equivariant map q : |
| [0045](entries/0045-t-p-hs-2-is-causal-minkowski-2-quotiente.md) | pattern | T_p HS^2 is Causal.Minkowski 2 quotiented by R . |
| [0046](entries/0046-pitfall.md) | pitfall | Pitfall: |
| [0047](entries/0047-pitfall.md) | pitfall | Pitfall: |
| [0048](entries/0048-pitfall.md) | pitfall | Pitfall: |
| [0049](entries/0049-pitfall.md) | pitfall | Pitfall: |
| [0050](entries/0050-pitfall.md) | pitfall | Pitfall: |
| [0051](entries/0051-p-p-is-analytic-gx-isanalyticaction-link.md) | pattern | (Γ_p, ℓ(p)) is analytic (GX.isAnalyticAction_link, BBS/IPm). |
| [0052](entries/0052-2d-linear-algebra-in-t-p-hs-without-base.md) | pattern | 2D linear algebra in T_p HS² without bases: |
| [0053](entries/0053-explicit-elements-of-p-for-an-arbitrary.md) | pattern | Explicit elements of Γ_p for an arbitrary p. |
| [0054](entries/0054-pitfall.md) | pitfall | Pitfall: |
| [0055](entries/0055-pitfall.md) | pitfall | Pitfall: |
| [0056](entries/0056-coordinates-on-causal-minkowski-2.md) | pattern | Coordinates on Causal.Minkowski 2: |
| [0057](entries/0057-germs-at-0-of-s-p-s-w-in-hs-do-not-depen.md) | pattern | Germs at 0⁺ of s ↦ [p + s w] in HS² do not depend on the lift w (GX.eventually_rayNormalize_congr, r |
| [0058](entries/0058-s-has-two-components-reads-k-x-s-connect.md) | pattern | 'S has two components' reads {K / ∃ x ∈ S, connectedComponentIn S x = K} = {S₁, S₂}. |
| [0059](entries/0059-so-0-1-2-psl-2-r-is-gx-pslequivlorentz-t.md) | pattern | SO_0(1,2) ≅ PSL(2,R) is GX.pslEquivLorentz, through the spinor representation GX.spinLorentz (X ↦ g  |
| [0060](entries/0060-linearmap-det-on-causal-minkowski-2-is-v.md) | pattern | LinearMap.det on Causal.Minkowski 2 is vol3 of the images of e_t, e_x, e_y (GX.det_eq_vol3, through  |
| [0061](entries/0061-an-element-of-so-2-acting-on-euclideansp.md) | pattern | An element of SO(2) acting on EuclideanSpace ℝ (Fin 2) is multiplication by a unit complex number (G |
| [0062](entries/0062-to-restrict-a-chart-e.md) | pattern | To restrict a chart e : |
| [0063](entries/0063-which-piece-of-hs-a-point-of-an-hs-surfa.md) | pattern | Which piece of HS² a point of an HS-surface lies over is chart-independent: |
| [0064](entries/0064-in-hs-the-isotropic-projections-are-expl.md) | pattern | In HS² the isotropic projections are explicit. |
| [0065](entries/0065-pitfall.md) | pitfall | Pitfall: |
| [0066](entries/0066-pitfall.md) | pitfall | Pitfall: |
| [0067](entries/0067-pitfall.md) | pitfall | Pitfall: |
| [0068](entries/0068-lemma-f-s-g-toolkit-is-in-gxscaffold-int.md) | pattern | Lemma F's G~ toolkit is in GXScaffold.Interaction.FunnelGTilde: |
| [0069](entries/0069-a-parabolic-element-of-psl-2-r-has-exact.md) | pattern | A parabolic element of PSL(2,R) has exactly one fixed point on RP1: |
| [0070](entries/0070-pitfall.md) | pitfall | Pitfall: |
| [0071](entries/0071-pitfall.md) | pitfall | Pitfall: |
| [0072](entries/0072-a-continuous-integer-valued-function-on.md) | pattern | A continuous integer-valued function on R that vanishes at 0 vanishes everywhere: |
| [0073](entries/0073-d-s2-u-r-is-gx-dstilde-r-x-1-1-projected.md) | pattern | d~S2 u R+- is GX.DSTilde = R x [-1,1], projected by GX.dsCover |
| [0074](entries/0074-a-lifted-so0-1-2-equivariance-of-a-map-i.md) | pattern | A lifted equivariance into d~S2 u R+- acts by one element of G~ at every height |
| [0075](entries/0075-to-develop-a-map-of-a-simply-connected-s.md) | pattern | Developing a map of a simply connected space into an HS-surface |
| [0076](entries/0076-every-g-hs2-manifold-is-locally-path-con.md) | pattern | Every (G, HS2)-manifold is locally path-connected and semilocally simply connected |
| [0077](entries/0077-the-chart-of-isphotoncircle-rp1chartedsp.md) | pattern | The chart of IsPhotonCircle.rp1ChartedSpace is the HS-chart |
| [0078](entries/0078-projectively-isomorphic-rp1-circles-a-ho.md) | pattern | Projectively isomorphic RP1-circles have the same lifted holonomies and real angles |
| [0079](entries/0079-pitfall.md) | pitfall | Pitfall: |
