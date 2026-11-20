# Eperon–Reall–Sbierski, *predictability for wave equations with other cones* (arXiv 1802.03020) — a reading map, not a story

*An external paper (arXiv 1802.03020 v2, Commun. Math. Phys. 2019), ledgered for the ETT
programme as Barbot's was by DEC-34. There is nothing to retell: this file names what reading and
formalizing it is for, so the gates can count it. Its Lean home is `lean-causal`; its binder
(`certificate/binder.toml`, target T-bind-ers-predictability) will factor every row into the three
layers of `programme/README.md`.*

## Objective

Understand when a quasilinear wave equation, whose characteristic cones are those of a metric that
depends on the solution, has a unique maximal development; and read the answer as a statement
about two nested causalities on one space, the equation's and Minkowski's, which is the programme's
route to generalized Einstein equations (references/sbierski/SYNTHESIS.md Q3).

## S-ers-predictability-1 A two-dimensional counterexample

For the Born–Infeld scalar in two dimensions, solved explicitly through characteristic coordinates
(`ersthm:diffeo_theorem`, `ersthm:global_theorem`), two developments of the same data can disagree:
non-uniqueness of the maximal development, `ersthm:ThmNonUniqueness`. The lemmas before it
(`erslem:glob_hyp_lemma`, `erslem:sep_lemma`) are the global hyperbolicity and separation facts the
construction uses.

## S-ers-predictability-2 Uniqueness on connected overlaps

Two developments agree on their overlap as soon as it is connected (`ersthm:ThmUnique`, from local
uniqueness `ersprop:PropLocUniqueness`), so non-uniqueness needs a disconnected overlap,
`erscor:CorDisCon`. When one fixed vector field is timelike for every cone the equation can have,
and each of its integral curves meets the initial surface at most once, the overlap is connected
(`erslem:LemConnected`, `erscor:CorSupLum`, superluminal equations); for subluminal ones the
Minkowski cone plays that part, for developments that are globally hyperbolic for Minkowski
(`erscor:CorUniqueSub`). This is the layer-1 content of the target T-abs-nested-causalities.

## S-ers-predictability-3 Maximal developments

Local existence (`ersthm:ThmEx`) and the connected-overlap criterion give a unique maximal
development for superluminal equations (`ersthm:ThmUMGHD`); for subluminal ones, a largest
development on which the solution is unique (`ersthm:ThmMUGHD`) and a unique maximal one among
the developments globally hyperbolic for Minkowski
(`ersthm:consider_subluminal_quasilinear_wave`). The authors conjecture that some equations admit
no development with unique solution at all, `ersconj:ConUni`. A boundary that blocks no evolution makes the
maximal development unique, `ersthm:ThmNotBlocking`: a boundary-chart localisation property.
