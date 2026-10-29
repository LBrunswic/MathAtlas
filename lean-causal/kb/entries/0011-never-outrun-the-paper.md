---
id: 0011
title: A Lean statement narrower than the paper's is never its certificate
kind: house-rule
created: 2026-09-27
---
## Do
* State what the paper states. Dropping a hypothesis you do not use is welcome (`⚠ weakened`).
* If your proof needs a hypothesis the paper does not have, that is `⚠ strengthened`: a finding,
  reported prominently, and the label is NOT marked `**`. Usually the paper has a gap or you
  mis-modelled something.
* Where the paper cites, sketches, or says a thing is open, mirror it: state with a tagged
  `sorry` and say so. Do not invent a proof the paper does not give unless you can close it.
* A definition the paper leaves ambiguous is a question for the author, not a choice to make
  silently: choose, disclose in SCOPE, report it as a question.
* A theorem about a predicate is worth what the predicate's inhabitants are worth: give an
  example satisfying your hypotheses when one is cheap (`Causal/Lines.lean` has the three lines;
  the timelike line satisfies every hypothesis of the library).
