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
