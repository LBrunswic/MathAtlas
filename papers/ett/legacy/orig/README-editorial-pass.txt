Topological spacetimes (I): from scratch to Geroch's and Choquet-Bruhat--Geroch's Theorems
Editorial passes of 2026-08-20, 2026-08-21 and 2026-08-22.
Backups: ETT.tex.bak-2026-08-20 (original), ETT.tex.bak-2026-08-21-pre-pushup,
         ETT.tex.bak-2026-08-22-pre-cbg.

=============================================================================
PASS 3 (2026-08-22): the map x -> K^-(x), and Choquet-Bruhat--Geroch
=============================================================================

WHY THE TWO REQUESTS ARE ONE.  The thesis's Choquet-Bruhat--Geroch section
(these.tex 6244-6900) is the only consumer of ETT's Corollary cor:K_injectif and
of the three orphan lemmas of Section 3.5 (lem:J_int, lem:cup_cap_sing,
lem:cup_cap_BTZ): they were extracted for it and had no use inside ETT. That
section invokes cor:K_injectif at exactly one point (lem:corresponding_K,
(ii)=>(i)) and also uses, without proof, the fact that "I^-(P_n) est dense dans
J^-(P_n)" at non-BTZ points. Strengthening cor:K_injectif is therefore the same
task as importing CBG.

(1) THE MAP x -> K^-(x)
  New DEFINITION defi:pushup (2.10), the RELATIONAL push-up
  J(I) subset I and I(J) subset I, with rem:deux_pushup (2.11) recording that it
  is logically independent of causal plainness (defi:causalement_plat): the
  lightlike line has push-up vacuously and is not plain; plainness is silent
  where Int(J) is empty. Push-up is NOT an axiom either -- it enters only through
  lem:pushup_local and holds in the model spaces.

  lem:pushup_local (2.33): push-up propagates from a cover by causally
  arc-connected open sets, with no Baire hypothesis, by a one-step argument
  (slide back along the chronal curve into the chart, apply local push-up,
  concatenate). cor:pushup_sing (3.4): every E^{1,2}_{>=0}-manifold has push-up.

  prop:K_plongement_ordre (2.69) is the criterion: if J^{+-}(x) is closed and
  K^{+-}(x) is DENSE in J^{+-}(x), then K^-(x) subset K^-(y) implies x <= y.
  Proof is four lines. Injectivity is the diagonal case. With monotonicity it
  upgrades to an order isomorphism onto its image.

  Verified for singular flat spacetimes in three steps:
    - lem:densite_modele (3.7): density in the model spaces (J is the closure of
      its interior; Sing is a 1-submanifold, hence removable).
    - prop:K_monotone (3.13): q <= p implies K^-(q) subset K^-(p). This is the
      four-case argument EXTRACTED verbatim from the old proof of
      prop:mesure_admissible, which now cites it in one line instead of
      repeating it.
    - prop:K_densite_sing (3.14): J^{+-}(x) subset closure(K^{+-}(x)) on any
      strongly causal E^{1,2}_{>=0}-manifold. Case analysis on whether x and y
      are BTZ; the BTZ cases are where I^- is empty and only K^- can be dense.
  cor:K_ordre (3.15) is the improvement asked for: on a GLOBALLY HYPERBOLIC
  E^{1,2}_{>=0}-manifold, x <= y iff K^-(x) subset K^-(y) iff K^+(y) subset
  K^+(x); x -> K^-(x) is an isomorphism of ordered sets onto its image.
  cor:K_injectif (3.12) is KEPT as is -- it needs only strong causality.

  cor:K_ordre_Sigma (4.14) is the form CBG actually uses: the same statement for
  K^-(x) intersected with J^+(Sigma), on J^+(Sigma) minus Sigma. It rests on
  lem:Sigma_separe (4.13), which computes J^{+-}(Sigma) = psi(Sigma x R_{+-})
  from the splitting of theo:geroch_sing -- hence J^{+-}(Sigma) closed and
  J^+(Sigma) a neighbourhood of each of its points off Sigma. Without this, the
  step "K^-(q) = K^-(q') above Sigma_2, therefore q = q'" is a gap; the thesis
  passes over it.

(2) CHOQUET-BRUHAT--GEROCH: new Section 4, sec:CBG, 11 pages
  Translated from these.tex 6244-6900. Structure: 4.1 Cauchy embeddings and
  extensions; 4.2 statement (theo:CBG, Theorem 5) and strategy; 4.3 the greatest
  common sub-extension (prop:Cauchy_pgcd, 4.6); 4.4 the least common
  over-extension and the Hausdorff property (prop:ppcm_Cauchy, 4.9, proved at the
  end of the subsection); 4.5 conclusion.

  The chain is: lem:image_diamant (4.11) -> lem:passe_pgcd (4.12) ->
  lem:corresponding_K (4.15) -> prop:Cauchy_non_max (4.18) + prop:C_connexe
  (4.19) + prop:Cauchy_point_min (4.20) -> C is empty for N = M_1 ^ M_2 -> the
  pushout is Hausdorff.

  Departures from the thesis, all deliberate:
   - lem:passe_pgcd is restated as one inclusion K^-_N(p) cap J^+(i(Sigma))
     subset i(M) with the two explicit forms as corollaries of prop:K_calcul.
     The thesis splits it into Sing_{>0} and Sing_0 and writes Sing(M) where
     Sing(N) is meant; the regular case was missing.
   - lem:corresponding_K (ii)=>(i) now concludes by cor:K_ordre_Sigma instead of
     by bare injectivity, and the existence of the increasing sequence inside N
     is justified by lem:passe_pgcd (the thesis takes it for granted).
   - cor:model_corresponding and cor:ext_continue had NO proof in the thesis;
     short ones are supplied, and their order is swapped so that
     cor:ext_continue comes first.
   - Einstein-equation uniqueness is replaced, as in the thesis, by the
     analyticity of (Isom(E), E, E_{>=0}) and the rigidity of E_{>=0}-morphisms;
     both are quoted from \cite{thesis} in rem:CBG_analytique, not reproved.

  STILL OPEN in Section 4 (rem:CBG_manquant, stated in the text):
   (i) second countability of the inductive limit is NOT proved -- this is
       verbatim the gap the thesis leaves ("Nous ne donnons pas de demonstration
       de ce dernier point"). It should follow Geroch's appendix, MR0234703.
   (ii) the small-skeleton point for the inductive limit is asserted, not
       detailed (it is routine: cardinality of the continuum).

A CLAIM THAT LOOKS WRONG AND WAS NOT TOUCHED
  rem:pas_plat (ii) and the abstract say that causal plainness FAILS at a BTZ
  point because I^-(p) is empty while J^-(p) is not. But defi:causalement_plat
  reads Int(J^{+-}(A)) subset closure(I^{+-}(A)), and at a BTZ point J^-(p) is a
  half-line in a 3-manifold, so Int(J^-(p)) is EMPTY and the condition holds
  vacuously. What actually fails at a BTZ point is STRONG TARENTINITY IN THE
  PAST, which is the hypothesis of prop:tarentin_fort_K -- so the mathematics is
  unaffected (K^- =/= I^- there for the stated reason), but the narrative in the
  abstract, in the introduction and in rem:pas_plat (ii) attributes it to the
  wrong failure. Deciding how to rephrase this is the author's call; nothing was
  changed. The low-regularity half of the argument (causal bubbles) is correct
  as written: a bubble is an open subset of J^+ disjoint from I^+, so there
  Int(J^+) is genuinely non-empty.

  17 NEW proofs/statements carry "% [editorial] ... 2026-08-22 -- verify".
  In order of how much they deserve a second reading:
     prop:K_densite_sing, lem:pushup_local, lem:densite_modele,
     prop:Cauchy_point_min, prop:Cauchy_non_max, lem:Sigma_separe,
     cor:ext_continue, prop:C_connexe, cor:K_ordre_Sigma,
     prop:K_plongement_ordre.

  BUILD after pass 3: 46 pages, no undefined reference or citation, no \gap
  boxes. Same command as below.

=============================================================================
PASS 2 (2026-08-21): the four gaps, and the push-up decision
=============================================================================

WHERE THE MISSING PROOFS WERE: nowhere.
  The thesis (~/Dropbox/Archive/these_2/these.tex; NNT 2017AVIG0420, tel-01818016)
  states all four without proof -- Lemme 3.1.15 and 3.1.16 (p.75) have no
  \begin{proof} at all, Prop. 3.1.58 (p.83) ends on "se verifie par recurrence",
  Prop. 3.1.59 (p.84) proves the point case and stops. The gaps were INHERITED,
  not introduced by the extraction. Three are now closed and one was false.

  Also established: ETT was transcribed from these.tex.backup (Dec 2017), NOT
  from the final these.tex (Mar 2020). That is why it carried a superseded
  measure definition.

THE PUSH-UP DECISION (the reason the paper had stalled)
  Thesis axiom (d) reads  Int(J±(A)) subset closure(I±(A)).  It is NOT an axiom
  here, and must not be restored. A causal bubble is by definition a non-empty
  open subset of J+ disjoint from I+, so (d) fails for every sub-Lipschitz
  metric (Chrusciel-Grant MR2949547; Samann MR3500220; survey arXiv:2404.18651,
  now in note.bib as samann2024nonregular). It fails again at BTZ points, where
  I-(p) is empty and J-(p) is not. The introduction already promised to cover
  both, so (d) as an axiom contradicted the paper's own scope.

  Instead: (d) is named "causally plain" (defi:causalement_plat) and carried as
  an explicit hypothesis by the only two statements that need it,
  lem:passe_coherent and prop:tarentin_fort_K. rem:K_neq_I records that
  prop:tarentin_fort_K is FALSE without it, bubbles being the counterexample --
  which is exactly why K± was introduced. The abstract and introduction were
  rewritten around this.

  Openness of << (axiom (c)) IS still assumed. Grant-Kunzinger-Samann
  (MR4047145, "The future is not always open") show it can fail below Lipschitz
  regularity too. By decision this is stated as a limitation, not repaired.

THE FOUR GAPS
  1. lem:precausalite_engendre_minimale -- TRUE. Proof supplied: decompose a
     chain, apply absolute minimality of <=^i ON U_i to the trace cover, and
     concatenate. Does not use lemma 2 below.
  2. lem:precausalite_restriction_minimale -- FALSE. cexemple:point_transparent
     (R with a transparent point at 0) is absolutely minimal on R but not on
     R\{0}. rem:minimalite_non_hereditaire explains why: absolute minimality is
     hereditary only for clopen subsets. The lemma is restated under local
     causal arc-connectedness, which is what every application actually has.
     Consequence: prop:GX_espace_temps_topo and prop:GX_sing_espace_temps_topo
     now hypothesise "causally arc-connected" instead of "absolutely minimal"
     (strictly stronger, and it makes the statements shorter). The causal
     arc-connectedness block was moved earlier so nothing forward-references.
  3. prop:GH_Jferme for compact K -- CLOSED, no new hypothesis. New
     prop:relation_fermee: tarentin + J±(x) closed implies <= closed in MxM;
     then the compact case by the tube lemma. Uses no curves, no I±, and no
     causal plainness -- which is why it survives the push-up decision. The
     POINT case was also reformulated: it previously chose q' in I+(q), which
     tarentin does not supply and which needs (d).
  4. Property 4 of the admissible measure -- CLOSED. New lem:restriction_convexe
     plus a direct argument from hypotheses (i),(ii). The thesis's own recursion
     K^{-,(n)} is not used and is mis-seeded anyway (rem:recursion_these).

ONE-SIDED MEASURES (correctness fix)
  rem:mesure_unilaterale proves the two-sided notion is VACUOUS on any causal
  E^{1,2}_{>=0}-manifold with a BTZ line: property 3 in the past forces
  mu(]p,q])>0 while property 4 in the future forces mu(]p,q])=0. So the old
  prop:mesure_admissible stated something false. Admissibility is now one-sided
  (as in the final thesis), theo:geroch takes a PAIR of measures, and it gained
  the hypothesis J±(p) != {p}. In theo:geroch's proof, t± now uses mu±(J±)
  rather than mu(I±) -- the latter is wrong exactly at BTZ points -- the step
  mu({p}) <= mu(dJ-(p)) = 0 was deleted (false for lambda_3+lambda_1), and a
  missing "c" was restored (the thesis has c(x_n); ETT had x_n, a curve
  parameter where a point of M was meant).

OTHER FIXES
  - The category C required << to be a PREORDER, hence reflexive, contradicting
    Minkowski and defi:causal_E0. Now "transitive".
  - lem:union_causalite's characterisation was not localised; as printed the
    family is not monotone in U, hence not a precausality. prop:cac_engendre
    silently depended on the localised reading.
  - prop:cac_engendre (ii)=>(i): the compactness/Lebesgue-number step is now
    written out. It carries the whole architecture after fix 2.
  - K±(A) for a SUBSET is now defined (union over points). It was used in
    property 4 but defined nowhere, in ETT or the thesis.
  - rem:K_borelien: K-(p) is an uncountable intersection yet inner regularity is
    applied to it; under tarentin lem:K_facile makes it Borel.
  - Examples 2 and 3 (lightlike/spacelike lines) are not causally plain -- now a
    useful illustration rather than a defect. Galileo's <= was undefined.
  - cor:massA_cac: every E^{1,2}_{>=0}-manifold is causally arc-connected,
    required by theo:geroch and previously invoked without proof.
  - "chronologically tame" was vacuous and unused; removed.

=============================================================================
STILL OPEN -- honest ledger
=============================================================================
  1. theo:geroch, (iii)=>(i) is a sketch delegating to O'Neill's quasi-limit
     construction, which needs convex normal neighbourhoods this setting does
     not have. THIS IS NOW THE LARGEST HOLE IN THE PAPER.
  2. Openness of << is assumed, excluding the MR4047145 examples. By decision.
  3. I+(p) = Reg(J+(p)) at a BTZ point is asserted without proof in the thesis
     and is not in brunswic2021cauchy; hypothesis (ii) of
     prop:mesure_dieckmann_topo depends on it for one case. Flagged in the source.
  4. "Locally causally convex" is a standing hypothesis of theo:geroch never
     verified for a general singular flat spacetime.
  5. prop:mesure_dieckmann_Lorentz still says "one checks easily".

  17 proofs carry "% [editorial] ... verify". The ones that are real arguments
  rather than one-liners, in order of how much they deserve a second reading:
     property 4 (in prop:mesure_dieckmann_topo), lem:restriction_convexe,
     prop:relation_fermee, cor:K_injectif, lem:IJ_calc,
     lem:precausalite_engendre_minimale, cexemple:point_transparent,
     rem:mesure_unilaterale, prop:mesure_admissible, cor:massA_cac.

=============================================================================
BUILD
=============================================================================
  pdflatex ETT; bibtex ETT; pdflatex ETT; pdflatex ETT
  (pass 2 figures) 32 pages, 27 bibliography entries, 39 statements / 37 proofs,
  no undefined reference or citation, no \gap boxes left.
  (The two statements without proofs are quoted results: Geroch's classical
  theorem and prop:GX_sing_dec = Cor. 1.7 of brunswic2021cauchy.)

  TRAPS IN THIS TREE
   - alias.tex redefines \S as \mathcal S, so \cite[\S1.2]{...} is a HARD ERROR.
     Write "Section~1.2".
   - bibstyle alpha lowercases unbraced titles; brace-protect {$(G,X)$}, {BTZ}.
   - note.bib backups: note.bib.bak-pre-gxramcover-fix, note.bib.bak-2026-08-21.
