# Context for readers: what "the ETT framework" is (answer Q2–Q4 against this)

- **ETT** = L. Brunswic, *Topological spacetimes (I): from scratch to Geroch's and Choquet-Bruhat–Geroch's
  theorems* (draft in /home/maxbrain/Dropbox/LeanArticles/papers/ett/legacy/labeled/ETT.tex). Causal theory
  on a topological space carrying a *causality* (a family of preorders on open sets, no metric, no smooth
  structure): J±, I±, the "continuously reachable" K±, push-up, strong causality, global hyperbolicity,
  causal curves defined order-theoretically, Cauchy surfaces, Geroch's splitting, admissible (Dieckmann)
  measures, time functions (Levin's theorem for closed preorders), and singular flat spacetimes modelled on
  cones E_α (conical singular lines, massive particles) and E_0 (BTZ lines), and a Choquet-Bruhat–Geroch
  theorem.
- **lean-causal** (Lean 4 library in the same repo) formalizes it, and proves a CBG theorem (universal
  maximal Cauchy development) over an ABSTRACT rigid singular (G,X)-geometry, following Sbierski's
  Zorn-free proof order (arXiv 1309.7591); design note lean-causal/docs/CBG-DESIGN.md says rigidity and a
  size bound are essential (counterexamples without them) and that Hausdorffness of the glued maximal
  development is the key theorem.
- Related library: lean-gx (branched coverings of singular (G,X)-manifolds, BTZ uniformization).
Answer, per paper: (i) what in it depends on smooth/C^k/C^0 metric structure and what is purely causal or
order-topological; (ii) whether ETT's notions (causality without metric; conical/BTZ singular lines;
CBG over rigid geometries) could state, weaken or generalize it; (iii) a concrete candidate statement for
formalization in lean-causal, if any. Put (i)–(iii) under "## Relevance to the questions" of the note.
