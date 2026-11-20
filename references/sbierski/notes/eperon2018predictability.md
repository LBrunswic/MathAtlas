# eperon2018predictability — Predictability of subluminal and superluminal wave equations

Felicity C. Eperon, Harvey S. Reall, Jan J. Sbierski
Communications in Mathematical Physics 2018 (published 2019) · arXiv:1802.03020, doi:10.1007/s00220-019-03428-1 · `pdf/eperon2018predictability.pdf`

**Tier: T2** — peer-reviewed (CMP); rigorous theorems with complete proofs plus an explicit Born–Infeld counterexample; its uniqueness criterion (Thm 4.82) is used by [[abbrescia2025quasilinear]], but that paper shares an author, so not independent replication.
**Relevance: 3** — Q1 (MGHD theory for fixed-background quasilinear equations), Q2 (results are mostly causal/order-theoretic, with two cone structures), Q4 (several clean formalization targets).
**Read:** full text (v2, 2019); §3.5–3.6 computations skimmed, §4 read in full.

## Summary
For quasilinear wave equations g^{μν}(u,du)∂_μ∂_ν u = F on a fixed R^{d+1}, the authors ask whether there is a unique maximal globally hyperbolic development (MGHD), where global hyperbolicity is with respect to the solution-dependent metric g(u,du). Using the 1+1 Born–Infeld scalar, which has subluminal (c=+1) and superluminal (c=−1) forms related by swapping timelike and spacelike, they show that the subluminal theory admits two smooth GHDs of the same data that disagree at a point of their common domain, hence non-unique MGHDs (Thm 3.45). In general, two GHDs agree on U1 ∩ U2 whenever U1 ∩ U2 is connected (Thm 4.64); a vector field timelike for all g(u,du) (in particular any superluminal equation) forces connectedness and yields a unique MGHD as the union of all GHDs (Lemma 4.70, Thm 4.77). For subluminal equations they construct the maximal unique GHD (MUGHD, Thm 4.79) and prove that an MGHD lying locally on one side of its boundary (a graph condition) is the unique MGHD (Thm 4.82).

## Key points
- [V] Non-uniqueness: for the (subluminal) Born–Infeld equation there exist two GHDs of the same data on {x0=0} which differ at a point of U_a ∩ U_b (Thm 3.45, §3.6.2); both GHDs are smooth, so the mechanism is not a loss of regularity (Remark 3.55).
- [V] The existence of the two distinct MGHDs containing them is obtained by Zorn's lemma, and infinitely many distinct MGHDs are claimed with details left to the reader (Remark 3.56).
- [V] Global uniqueness reduces to connectedness: two GHDs of the same data on a connected S agree on U1 ∩ U2 if it is connected (Thm 4.64); equivalently, disagreement forces U1 ∩ U2 to be disconnected (Cor 4.68).
- [V] The 2013 "union of all GHDs" sketch (Sbierski 2013 §1.4.1) tacitly assumed connectedness of U1 ∩ U2 (§4.2).
- [P] Why Einstein is different: gluing two fixed-background GHDs along their MCGHD produces a manifold that projects onto U1 ∪ U2 ⊆ R^{d+1} and contains the other components of U1 ∩ U2 twice — not allowed on a fixed background (§4.2, p. 29–30).
- [P] Superluminal criterion: if a vector field T is timelike for g(u,du) for all (u,du) and S meets every maximal integral curve of T at most once, then U1 ∩ U2 is connected (Lemma 4.70) and a unique MGHD exists as the union of all GHDs (Thm 4.77). Remark 4.78: this union construction works whenever global uniqueness holds.
- [P] Subluminal partial uniqueness: if S is m-achronal (Minkowski) and U1 is also globally hyperbolic for m (an "m-GHD"), then U1 ∩ U2 is connected and u1 = u2 there (Lemma 4.72, Cor 4.73). The proof uses only that g-timelike curves are m-timelike, concatenation and achronality.
- [P] MUGHD exists for subluminal equations with data on an m-acausal hypersurface (Thm 4.79), and a unique m-MGHD exists (Thm 4.80); the m-MGHD is contained in the MUGHD, in general strictly (§4.7).
- [V] Conjecture 4.81: some quasilinear equations admit data with no UGHD at all.
- [P] Teleological uniqueness criterion: an MGHD whose boundary is locally the graph of a continuous function over a chart, with U1 below and the complement above, is the unique MGHD (Thm 4.82, condition (4.83)); applies only after the whole MGHD is constructed.
- [P] Appendix: in 1+1 dimensions one cannot form a time machine smoothly in a superluminal theory (Appendix, p. 25ff.).

## Verified quotes
> "For the subluminal theory, there can exist multiple maximal globally hyperbolic developments arising from the same initial data."

> "In particular, we prove that superluminal equations always admit a unique maximal globally hyperbolic development."

> "Theorem 3.45. For the equation (3.40) there exist two GHDs Φa : Ua → R and Φb : Ub → R of the same initial data posed on {x0 = 0} such that there exists an x ∈ Ua ∩Ub with Φa (x) 6= Φb (x)."

> "Hence, the non-uniqueness mechanism exhibited does not stem from a loss of regularity of the solution."

> "However, this sketch has the flaw that it tacitly assumes that given two globally hyperbolic developments u1 : U1 → R and u2 : U2 → R of the same initial data, that U1 ∩ U2 is then connected"

> "Theorem 4.64. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of (4.61) arising from the same initial data given on a connected hypersurface S ⊆ Rd+1 . Assume that U1 ∩ U2 is connected. Then u1 and u2 agree on U1 ∩ U2 ."

> "would yield a solution which is no longer defined on a subset of Rd+1 , but instead on a manifold which projects down on U1 ∪ U2 ⊆ Rd+1 and contains the other connected components of U1 ∩ U2 twice."

> "Remark 4.78. We note that the above construction of a unique maximal globally hyperbolic development is always possible provided the property of global uniqueness holds."

> "Conjecture 4.81. There are quasilinear wave equations of the form (4.61) for which there exists initial data such that there does not exist any UGHD."

> "Note that in order to apply this theorem to a concrete example one has to first construct a/the whole MGHD and is only then able to infer a posteriori that the evolution was indeed unique."

> "It is this rigidity which leads to non-uniqueness of MGHDs for subluminal equations."

## Methods and evidence
- Data / setting: smooth quasilinear scalar (or system) wave equations on fixed R^{d+1}; explicit Born–Infeld scalar in 1+1 via the Barbashov–Chernikov general solution (method of characteristics, Thm 3.22).
- Baselines: compared against CBG for Einstein (unique MGHD) and the linear wave equation.
- Evaluation: rigorous proofs; a numerical demonstration of non-uniqueness (§3.6.1) precedes the rigorous Thm 3.45.
- Artifacts: none.

## Limitations and caveats
- The abstract's "superluminal equations always admit a unique MGHD" holds under a hypothesis on the data hypersurface S (every maximal integral curve of T meets S at most once; any Minkowski Cauchy surface qualifies, footnote 23) — mildly more than the bare statement, hence `claims_exceed_evidence` (minor).
- The infinitely-many-MGHDs claim (Remark 3.56) is left to the reader; distinct MGHDs are obtained only via Zorn.
- Thm 4.82 is teleological: one must know the entire MGHD. The authors also concede (footnote cited in [[abbrescia2025quasilinear]]) that they wrongly believed Christodoulou had constructed the full MGHD and boundary in the relativistic Euler shock problem; that application of Thm 4.82 is therefore not established.
- Smoothness (C^∞) is assumed throughout; Thm 4.64's proof uses local uniqueness on a spacelike slice through a boundary point (metric construction).

## Relevance to the questions
**(i) Smooth vs. order-topological.** The paper's structural results are strikingly causal: Lemma 4.70 (connectedness via a common timelike vector field), Lemma 4.72 (connectedness via cone inclusion g ⊂ m plus m-achronality and m-global hyperbolicity), Thm 4.77/4.79/4.80 (union constructions, given global uniqueness, Remark 4.78), and Thm 4.82 (a *topological* one-sided boundary condition: locally the graph of a continuous function). The analytic input is Prop 4.63 (local uniqueness), Thm 4.75 (local existence), and the slice-restart step inside Thm 4.64.
**(ii) What ETT could state or generalise.** This is the natural home of "equations with several characteristic cones": a GHD carries two causalities, the solution's g(u,du) and the background m, and sub-/superluminality is an *inclusion of causal preorders* (J_g ⊆ J_m or J_m ⊆ J_g). ETT's causality-without-metric framework can state Lemma 4.72, Lemma 4.70 and Thm 4.82 verbatim for two nested causalities on one topological space. The contrast with Einstein (§4.2: gluing along the MCGHD produces a manifold *over* R^{d+1} that is not a subset) is exactly the distinction between a (G,X)-manifold and its developing-map image: the Einstein-style MGHD of a fixed-background equation exists as an étale space over R^{d+1}, and non-uniqueness of MGHDs is the failure of the developing map to be injective. That is directly in lean-gx's territory (branched/étale coverings of (G,X)-manifolds) and in CBG-DESIGN's remark that rigidity matters.
**(iii) Candidate statements for lean-causal.**
1. *Two-causality connectedness lemma* (Lemma 4.72, abstracted): on a topological space with causalities ≤_g ⊆ ≤_m, if S is ≤_m-achronal and U1 is ≤_m-globally hyperbolic with Cauchy set S, and U2 is ≤_g-globally hyperbolic with Cauchy set S, then U1 ∩ U2 is connected.
2. *Union construction under global uniqueness* (Thm 4.77 + Remark 4.78): abstract statement "if any two GHDs agree on their overlap, the union of all GHDs is a GHD and is the unique MGHD" — needs only the Cauchy-surface argument via inextendible curves; parallel to Thm 3.4 of [[sbierski2013existence]].
3. *Étale MGHD for fixed-background equations*: glue GHDs Einstein-style along MCGHDs to get a Hausdorff space with a local homeomorphism to R^{d+1}; uniqueness of the MGHD in the fixed-background sense ⇔ this map is injective. A natural bridge statement between lean-causal's abstract CBG and lean-gx's developing maps.
4. *One-sided boundary criterion* (Thm 4.82) as a statement about a maximal GH open set whose boundary is locally a topological graph — plausibly provable in ETT given local uniqueness as an axiom.

## Contradictions and tensions
- [[sbierski2013existence]] §1.4.1 sketch of the quasilinear MGHD is flawed (tacit connectedness) — corrected here, §4.2. The Einstein argument is unaffected.
- [[abbrescia2025quasilinear]] footnote 8 corrects this paper's belief (comment after Lemma 4.86) that Christodoulou's monograph constructed the full MGHD and its boundary.

## Open questions
- Conjecture 4.81 (no UGHD at all for some equations) — open as stated.
- Do equations with no nested cone structure (neither sub- nor superluminal) admit an MUGHD?
- In higher-dimensional superluminal theories, can a time machine form from generic data (Appendix, open)?

## Leads for next round
- term: maximal unique globally hyperbolic development (MUGHD); m-GHD; subluminal / superluminal; global uniqueness; teleological uniqueness; acoustical metric.
- cited: [7] Christodoulou, *The formation of shocks in 3-dimensional fluids* (2007); [5, 6] Barbashov–Chernikov Born–Infeld general solution; [9] Whitham *Linear and Nonlinear Waves*; [1] Adams et al. superluminality/causality argument; [12] Choquet-Bruhat–Geroch; [13] Sbierski 2013; [16] O'Neill Ch. 14; [8] Hawking compactly generated Cauchy horizons.
- author: Harvey Reall (follow-ups on predictability of modified gravity / Lovelock / Horndeski MGHDs); Felicity Eperon.
