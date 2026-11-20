# Barbot–Bonsante–Schlenker, *Collisions of particles in locally AdS spacetimes I* — a reading map, not a story

*An external paper (arXiv 1010.3602 v1, Comm. Math. Phys. 308, 2011), counted in this hub by DEC-132
as Barbot's was by DEC-34. There is nothing to retell: this file only names what reading and
formalizing it is for, so the gates can count it. Its research notes are `REVIEW.md` (the review
against gx, with the layered Lean roadmap), `NOTES-3+1.md` (the 3+1 programme) and
`SEPPI-READING.md`. Its Lean home is `lean-gx`.*

## Objective

Describe the singular points of 2+1 anti-de Sitter spacetimes with interacting particles through
their links, singular structures on the sphere of rays, and use that local picture as the first
layer of a programme that carries interacting particles to 3+1 dimensions.

## S-bbs-1 Singular lines and their links

The local theory: a singular point is the suspension of its link, an HS-surface whose own
singularities are suspensions of circles. Classifying those circles yields the list of singular
lines, `bbsprop:classising`, and causality removes the Misner and higher-degree ones,
`bbsdef:Hcausal`. This is the part `REVIEW.md` finds model-independent and which the conic and
celestial suspension layers of lean-gx rebuild.

## S-bbs-2 Interactions

Positive causal interactions are classified by the topology of their link, `bbsthm:thierry`,
through the de Sitter regions of the link (`bbscor:de_sitter_region_homeomorphic`,
`bbscor:Lclosed`, `bbsprop:hyphyp`); convex polyhedra produce interactions, and conversely in a
special case, `bbsthm:converse`.

## S-bbs-3 Global hyperbolicity

Time functions and Cauchy surfaces extended to singular spacetimes (`bbsprop:ghtime`,
`bbscor:splitting`), maximal globally hyperbolic extensions (`bbsprop:extension1`,
`bbsprop:extension2`), and the surgery that inserts an interaction into a spacetime,
`bbslem:surgery_key`.
