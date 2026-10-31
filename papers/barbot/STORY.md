# Barbot, *Globally hyperbolic flat space-times* — a reading map, not a story

*An external paper (arXiv math/0402257, J. Geom. Phys. 53, 2005), formalized on the ETT library in
`lean-causal/` (DEC-34). There is nothing to retell: this file only names what the formalization is
for, so the gates can count it. The campaign document is `lean-causal/docs/BARBOT.md`.*

## Objective

Classify flat spacetimes that are globally hyperbolic and admit a complete Cauchy hypersurface, as
a Lorentzian analogue of Bieberbach's theory, and certify the causal half of the argument inside
the topological-spacetime framework rather than smooth Lorentzian geometry.

## S-barbot-1 The headline

The classification of Cauchy-complete flat spacetimes up to finite covers and linear twisted
products, `bthm:caucomp`, and its Cauchy-compact form `bthm:cauclo`. The developing map is an
embedding onto a convex invariant domain, `bprop:danom`, which is where Cauchy-completeness is spent
(`bprop:project`, `bcor:quoiso`).

## S-barbot-2 The convex domains

Regular convex domains cut out by families of lightlike half-spaces, `bdef:regular_domain`,
`blem:closecool`, `bprop:regular_iff_bounded`, and the Cauchy-hyperbolic spacetimes built on them,
`bdef:definitioncauchyhyp`.
