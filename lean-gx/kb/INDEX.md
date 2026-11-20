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
