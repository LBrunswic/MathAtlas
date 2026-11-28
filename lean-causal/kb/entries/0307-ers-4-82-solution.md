---
id: 0307
title: ERS Thm 4.82 over sol: the restart geometric, and where its content lies
kind: pattern
created: 2026-11-28
---
ERS Thm 4.82 over `sol` (`Causal.Ers482Solution`) has a geometric restart `Q`, `Causal.GluedRestartAt`: an open `O`, not inside `U₁`, in each one-sided neighbourhood of `p`, with `S` Cauchy in `U₁ ∪ O` for the glued solution (`Causal.glueSolutions`). The MGHD is `IsMaximalDevelopment` (l. 117), and solutions restrict (`Causal.SolutionRestricts`). At the maximal `U₁` any restart on `∂A ∩ U₂` is equivalent to the conclusion (`…_hstep_iff`): what has content is the restart step at non-maximal pairs (`Causal.ers_theorem_4_82_restart`, exercised by `Causal.Ers482Witness`). The forms of record are the uniform ones (`…_of_restarts`, `…_of_restarts_isCausal`), logically weaker than the fixed-`U₁` form, whose hypothesis names no maximal development.
