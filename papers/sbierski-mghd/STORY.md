# Sbierski, *the maximal Cauchy development, dezornified* (arXiv 1309.7591) — a reading map, not a story

*An external paper (arXiv 1309.7591 v3, Ann. Henri Poincaré 17, 2016), ledgered for the ETT
programme as Barbot's was by DEC-34. There is nothing to retell: this file names what reading and
formalizing it is for, so the gates can count it. Its Lean home is `lean-causal`, whose CBG already
follows its order of proof (DEC-29); its binder (`certificate/binder.toml`, target
T-bind-sbierski-mghd) will split every row into the three layers of `programme/README.md`.*

## Objective

Build the maximal globally hyperbolic development of vacuum initial data without the axiom of
choice, by gluing two developments along their largest common one and showing that the gluing is
Hausdorff; then isolate which steps are causal topology (layer 1 of the programme) and which are
the smooth vacuum geometry (layer 3).

## S-sbierski-mghd-1 Developments and their common part

Developments, extensions and the two definitions of a common development
(`mghddef:globally_hyperbolic_development_ghd`, `mghddef:extension`, `mghddef:PreDefCGHD`,
`mghddef:DefCGHD`); local theory is taken from Choquet-Bruhat, `mghdthm:LocalTheory`. The largest
common development exists by a union, without Zorn (`mghdthm:ExMCGHD`), because isometries that
agree on the initial surface agree on connected overlaps (`mghdlem:IsoConnected`,
`mghdcor:welldefined`, `mghdlem:IsoDiffeo`). This union is the step Causal.CBG makes abstract.

## S-sbierski-mghd-2 No corresponding boundary points

The obstruction to a Hausdorff gluing is a pair of boundary points that are limits of one sequence
seen from both sides (`mghddef:DefBound`, recast with timelike curves in `mghdprop:EquivCha`).
The largest common development has none (`mghdthm:NotMCGHD`, `mghdthm:TNDVersion`): near such a pair
one extends the isometry past the boundary (`mghdlem:ExtendIso`, `mghdlem:SpacelikePoint`,
`mghdlem:FuturePoint`). This is the local, geometric step of the programme's synthesis
(references/sbierski/SYNTHESIS.md Q2), proved here with null geodesics and normal coordinates.

## S-sbierski-mghd-3 The two main theorems

Gluing two developments along their largest common one gives a common extension
(`mghdthm:CommonExtension`), and gluing all of them, over a set rather than a class, gives the
maximal development (`mghdthm:MGHD`). The Hausdorff half of both is the layer-1 target
T-abs-gluing-hausdorff.
