# Benzécri, *Sur les variétés localement affines et localement projectives* — a reading map, not a story

*An external paper (J.-P. Benzécri's thesis, Bull. SMF 88, 1960, 229–332), formalized in its own
package `lean-benzecri/` (DEC-112). There is nothing to retell: this file only names what the
formalization is for, so the gates can count it. The draft the ledger reads is a transcription of
the Numdam scan, Chapter 1 and the three headline results of the introduction
(`legacy/MANIFEST.json`); the campaign document is `lean-benzecri/docs/CAMPAIGN.md` and the
Chapter 1 plan is `lean-benzecri/campaign/WP-45-plan/CH1-PLAN.md`.*

## Objective

Formalize the classical theory of manifolds locally modelled on the projective sphere and on affine
space, up to the construction that turns a projective manifold into an affine cone over it, and its
first consequence: products with circles of projective manifolds carry affine and projective
structures. That construction is the home of the (singular) affine suspension the gx and BBS work
needs. The core imports Mathlib only; the generalisations come later and sit over `lean-gx`.

## S-benzecri-1 The headline results

Result A, `bzthm:intro_A`, is Chapter 1's: a compact projective manifold times a circle is affine,
and a product of projective manifolds times a torus of the right dimension is projective. Results B
and C, `bzthm:intro_B` and `bzthm:intro_C`, concern universal covers (convexity, and the rigidity of
convex bodies dividing a compact manifold); they are labelled now and terminal for this ledger until
Chapters 2 and 5 are transcribed.

## S-benzecri-2 The model geometry

The projective sphere is the space of rays of a vector space, not the projective space:
`bzdef:c1s1d3_sphere`. Its linear subvarieties, open hemispheres and their affine structure
(`bzdef:c1s1d4_sous_variete_lineaire`, `bzdef:c1s1d5_hemisphere`,
`bzdef:c1s1d6_structure_affine_hemisphere`) give the bridge between the two geometries; segments,
convex and strictly convex parts and convex bodies (`bzdef:c1s1d7_segment`,
`bzdef:c1s1d8_partie_convexe`, `bzdef:c1s1d9_convexe_strict`, `bzdef:c1s1d11_corps_convexe`) are
the vocabulary of results B and C. Affine spaces and maps open the section
(`bzdef:c1s1d1_espace_affin`, `bzdef:c1s1d2_application_affine`), and the quotient by a linear
subvariety closes it (`bzdef:c1s1d10_quotient`).

## S-benzecri-3 Locally projective and locally affine manifolds

A structure is an open set of jets into the model on whose fibres the group acts transitively,
`bzdef:c1s1d12_variete_localement_projective`; compatible charts, `bzdef:c1s1d13_carte_compatible`,
are unique up to the group (`bzprop:c1s1p1_cartes_compatibles`), an atlas with transitions in the
group defines a structure (`bzprop:c1s1p3_atlas`), an affine structure induces a projective one
(`bzrem:c1s1r1_affine_vers_projective`), and a simply connected manifold develops onto the model as
a spread (an étalé open set), `bzprop:c1s1p2_developpement`. Segments in a manifold, homogeneous,
sweepable and divisible manifolds, and maximal ones (`bzdef:c1s1d14_segment_variete`,
`bzdef:c1s1d15_homogene_balayable_divisible`, `bzdef:c1s1d16_maximale`) set up the later chapters.

## S-benzecri-4 Affine cones and the functorial isomorphism

Open cones and conical affine manifolds (`bzdef:c1s2d1_cone_ouvert`,
`bzdef:c1s2d2_variete_conique_affine`, `bzprop:c1s2p1_atlas_conique`) carry a free action of the
positive reals by homotheties (`bzdef:c1s2d3_homotheties_positives`), whose quotient is a projective
manifold, the base (`bzprop:c1s2p2_base_cone`). The centre of the chapter is
`bzthm:c1s2_isomorphisme_fonctoriel`: taking the base is an isomorphism from the category of
n-dimensional affine cones to that of (n−1)-dimensional projective manifolds, whose inverse F is
built from pairs of a projective jet and a vector over its target.

## S-benzecri-5 Applications: circles and products

F carries homogeneity, sweepability and divisibility from a projective manifold to its affine cone,
`bzprop:c1s3p1_F_homogene`, whence `bzcor:c1s3p1c_produit_cercle` (dividing the cone by a discrete
group of homotheties). Products of cones (`bzdef:c1s3d1_produit_cones`) are fibred over products of
bases (`bzprop:c1s3p2_fibre_produit`) and carry the same three properties back to the projective
side, `bzprop:c1s3p3_produit_homogene`, whence `bzcor:c1s3p3c_produit_projectif`. A partial converse
through the compatible automorphisms of a product, `bzdef:c1s3d2_automorphisme_compatible`, is
`bzprop:c1s3p4_reciproque`.
