# sbierski2013existence — On the Existence of a Maximal Cauchy Development for the Einstein Equations - a Dezornification

Jan Sbierski
Annales Henri Poincaré 2013 (journal version 2016) · arXiv:1309.7591, doi:10.1007/s00023-015-0401-5 · `pdf/sbierski2013existence.pdf`

**Tier: T1** — peer-reviewed (AHP); proof is complete, elementary and self-contained modulo cited black boxes (local well-posedness, O'Neill causality); it is the standard reference for the Zorn-free CBG proof, re-used as a template by [[eperon2018predictability]] (Thm 4.64 proof "based on ideas found in" it) and [[graf2023uniqueness]] (Remark 47 "dezornified version"), and followed by lean-causal's CBG proof.
**Relevance: 3** — Q1 (core method), Q2 (exactly which steps are smooth vs. order-topological), Q4 (the lean-causal CBG proof order follows it).
**Read:** full text (v3, 25 pp.)

## Summary
The paper re-proves the Choquet-Bruhat–Geroch theorem (existence and uniqueness up to isometry of the maximal globally hyperbolic development, MGHD, of vacuum initial data) without Zorn's lemma. The guiding analogy is a quasilinear wave equation on a fixed background, where the MGHD is literally the union of all GHDs once global uniqueness is known. For Einstein there is no ambient space, so "taking the union" is replaced by "gluing along the maximal common GHD (MCGHD)". The MCGHD of two GHDs is constructed as the literal union of all common GHDs inside the first one (Thm 3.4); the key analytic step shows the MCGHD has no "corresponding boundary points" (Thm 3.6/3.13), which is exactly Hausdorffness of the glued space (Thm 2.7). The MGHD is then the gluing of a *set* of representatives (GHDs whose manifold is an open subset of Σ×R), which avoids the proper-class issue (Thm 2.8).

## Key points
- [V] Main theorems: global uniqueness (Thm 2.7: any two GHDs have a common extension) and existence of the MGHD unique up to isometry (Thm 2.8); Thm 2.7 is proved first and Thm 2.8 follows (§2, p. 12).
- [V] The central new idea: the analogue of "taking the union" of two GHDs is gluing them along their MCGHD (§1.4.2, display (1.3)).
- [V] Thm 3.4: the MCGHD of two GHDs is the literal union of all CGHDs realised as subsets of the first; well-definedness of the embedding into the second comes from Cor 3.2 (isometric immersions agreeing on a Cauchy surface agree on overlaps) — a pure rigidity statement (§3.1).
- [V] Corresponding boundary points (Def 3.5) are defined purely topologically: p ∈ ∂U, p' ∈ ∂ψ(U) with ψ^{-1}(V' ∩ ψ(U)) ∩ V ≠ ∅ for all neighbourhoods; Thm 3.6 shows that if they exist, U is not maximal (§3.2).
- [P] Prop 3.7 recharacterises corresponding boundary points via timelike curves: limits along *every* timelike curve into p map to p' (uses only: openness of I, closedness of ≤ in a globally hyperbolic manifold, strong causality). Consequence: each p ∈ ∂U has at most one corresponding point (§3.2, Prop 3.7).
- [P] Smooth/metric ingredients of Thm 3.6: extension of ψ across C ⊆ ∂U by exponential maps in convex neighbourhoods (Lemma 3.8); null-geodesic structure of achronal boundary (Lemma 3.9, via O'Neill Prop 10.46); a smooth spacelike slice S built as a level set of the time separation τ_q and the Gauss lemma; local uniqueness (Thm 2.6) restarted on S (§3.2, proof of Thm 3.6).
- [P] Hausdorffness of the glued space M ⊔ M' / ∼ is shown to be *equivalent in the proof* to the absence of corresponding boundary points; the remaining GHD properties (charts, metric, time orientation, Cauchy surface) are routine, the Cauchy-surface argument using only inextendible timelike curves (§3.3, proof of Thm 2.7, items 1–5).
- [P] Size bound: only GHDs whose underlying manifold is an open neighbourhood of Σ×{0} in Σ×R are glued; every GHD is isometric to one of these via the flow of a timelike vector field (§3.3, proof of Thm 2.8, item 6). Second countability of the glued MGHD is from Geroch's theorem on manifolds carrying a Lorentzian metric (item 5).
- [V] Set-theoretic strength: existence of the MGHD is a theorem of ZF+DC; the paper's own steps need only countable choice (§1.2).
- [V] Regularity scope: smooth only; the technique depends on causality theory for C^2 metrics and goes through for GHDs of regularity at least C^2 (§2, first bullet).
- [V] Matter / cosmological constant add no difficulty "as long as a local existence and uniqueness statement holds" (§2, third bullet).

## Verified quotes
> "In the case of the Einstein equations, the appropriate analogue of 'taking the union' (1.3) of two GHDs is to glue them together along their MCGHD."

> "Theorem 2.7 (Global uniqueness). Given two GHDs M and M 0 of the same initial data, there exists a GHD M̃ that is an extension of M and M 0 ."

> "The much simpler method of taking the union of all CGHDs of M and M 0 however works"

> "Regarding the technique of the proof given in this paper, it heavily depends on the causality theory developed for at least C 2 -regular Lorentzian metrics. But as long as the initial data is such that it gives rise to a GHD of regularity at least C 2 , basically the same proof as given in this paper goes through."

> "We can thus conclude that the existence of the MGHD is a theorem of8 ZF+DC"

> "the inclusion of matter and/or of a cosmological constant does not pose any additional difficulty as long as a local existence and uniqueness statement holds. In fact, exactly the same proof applies."

> "This, however, implies that ψ −1 V 0 ∩ ψ(U ) ∩ V 6= ∅, i.e., p and q are corresponding boundary points of U - in contradiction to Theorem 3.13. Thus, M̃ is indeed Hausdorff."

> "Instead of considering all GHDs of given initial data (M , ḡ, k̄), we only consider those whose underlying manifold is a subset of M × R."

> "In particular it follows from ii) and iii) that p ∈ ∂U has at most one corresponding boundary point."

## Methods and evidence
- Data / setting: smooth vacuum Einstein equations, connected time-oriented Lorentzian manifolds of dimension d+1, d ≥ 1.
- Baselines: compared with the original Choquet-Bruhat–Geroch (1969) Zorn argument and Ringström's book (Ch. 23), on which most §3.2 proofs are based (§1.3, §1.5, §3.2).
- Evaluation: mathematical proof; black boxes are local existence/uniqueness (Thm 2.6) and O'Neill's causality theory.
- Artifacts: none (pure mathematics).

## Limitations and caveats
- Smooth (C^∞) setting only; author asserts but does not write out the C^2 version, and lower regularity is deferred to Chruściel's Zorn-based work [4] (§2).
- MGHD is maximal only among *smooth* GHDs (§2, first bullet).
- Several steps are explicitly metric: exponential-map extension (Lemma 3.8), time-separation slice and Gauss lemma (Thm 3.6), null geodesic generators of achronal boundaries (Lemma 3.9), timelike-flow normal form (Thm 2.8 item 6), Geroch's second-countability theorem (Thm 2.8 item 5).
- Lemma 3.9 / footnote 14 ("requires a bit of care"): the restart point must lie on a "spacelike" part of ∂U; in the quasilinear sketch of §1.4.1 connectedness of U1 ∩ U2 is tacitly assumed — a flaw later pointed out by [[eperon2018predictability]] (§4.2), which does not affect the Einstein argument.
- The abstract does not overstate the theorems.

## Relevance to the questions
**(i) Smooth vs. order-topological.**
- Purely order-topological / set-theoretic: Thm 3.4 (MCGHD = union of CGHDs) given the rigidity Corollary 3.2 as an axiom; Def 3.5 and the Hausdorff ⇔ no-corresponding-boundary-points argument (§3.3, Thm 2.7 proof and the analogue for the family in Thm 2.8 item 1); the Cauchy-surface verification of the glued space (item 4, only inextendible timelike curves and global hyperbolicity of the pieces); transitivity of the gluing relation (3.15); Prop 3.7 (needs open I, closed ≤ on a GH space, strong causality); the achronality of ∂U ∩ J+(Σ) (footnote 27).
- Metric/smooth: Lemma 3.1 (rigidity of isometric immersions via geodesics — in a (G,X) setting this is the rigidity axiom of the geometry), Lemma 3.3 (immersion ⇒ embedding, uses timelike geodesics), Lemma 3.8 (exp-map extension), Lemma 3.9 (null geodesic generators), the τ_q slice in Thm 3.6, the timelike-flow trivialisation of Thm 2.8, Geroch's second-countability.
**(ii) What ETT could state or generalise.** The proof is a template: [local existence + local uniqueness (Thm 2.6)] + [rigidity (Cor 3.2)] + [restart at a spacelike boundary point (Thm 3.6)] + [size bound (Σ×R)] ⇒ MGHD. In ETT, global hyperbolicity, Cauchy surfaces, I/J, strong causality and closedness of J are all available without a metric, so the gluing and Hausdorffness half is statable verbatim for spaces with a causality. For singular flat spacetimes with conical (E_α) or BTZ (E_0) lines, the rigidity is (G,X)-rigidity and the restart step is replaced by local (G,X)-developments — which is what lean-causal's abstract rigid singular (G,X) CBG does; the ETT draft's CBG theorem is precisely this paper's skeleton with Lemma 3.1/3.8 replaced by rigidity of (G,X)-charts. The step that genuinely needs extra structure in ETT is Thm 3.6 (finding a "spacelike" restart slice): one needs Lemma 3.9's "minimal" boundary point with J^-(p) ∩ ∂U ∩ J^+(Σ) = {p} — an order-theoretic statement whose proof uses null geodesics; in ETT it may follow from compactness of causal diamonds and closedness of J.
**(iii) Candidate statements for lean-causal.**
1. *Gluing-Hausdorff lemma* (topology only): for open embeddings ψ: U ⊆ M → M', the quotient (M ⊔ M')/∼ is Hausdorff iff there is no pair (p ∈ ∂U, p' ∈ ∂ψ(U)) with ψ^{-1}(V' ∩ ψ(U)) ∩ V ≠ ∅ for all neighbourhoods V, V' — and π∘j, π∘j' are open embeddings (3.14). No causal structure needed.
2. *MCGHD as a union* (Thm 3.4) in an abstract setting: given a rigidity axiom "two morphisms from GH sets with Cauchy surface Σ agreeing on Σ agree on overlaps", the union of all CGHDs is the maximum CGHD.
3. *Prop 3.7* in ETT: in a strongly causal space with closed J, corresponding boundary points are characterised by limits of timelike curves, hence each boundary point has at most one partner.
4. *Lemma 3.9 / 3.11* as order-theoretic statements on a globally hyperbolic causal space (existence of a J^- -minimal point of C ∩ J^+(Σ) in ∂U; shrinking J^-(q) ∩ U^c ∩ J^+(Σ) into any neighbourhood).

## Contradictions and tensions
- [[eperon2018predictability]] §4.2: the §1.4.1 quasilinear sketch here "tacitly assumes" U1 ∩ U2 is connected; false in general (their Born–Infeld example). Not a contradiction of the Einstein theorem, but the "union of all GHDs" analogy fails for fixed-background equations without extra hypotheses.
- [[graf2023uniqueness]] re-uses the gluing pattern; their obstruction to Hausdorffness ("intertwined timelike geodesics") plays the role that corresponding boundary points play here, but here the obstruction is *excluded by the PDE* (local uniqueness), whereas there it must be *assumed away*.

## Open questions
- Can the existence of the MGHD be proved in ZF+CC (the author's question about the black-box results)?
- Exact minimal regularity: does the argument go through for C^{1,1} or Lipschitz metrics (causality theory breaks below Lipschitz — see causal bubbles in [[abbrescia2025quasilinear]])?
- Is Thm 3.6's restart step provable in a purely topological causal setting (no null geodesics), given only local well-posedness on "spacelike" slices?

## Leads for next round
- term: maximal common globally hyperbolic development (MCGHD); corresponding boundary points; dezornification; global uniqueness.
- cited: [2] Choquet-Bruhat & Geroch 1969 (CMP 14); [4] Chruściel, "On maximal globally hyperbolic vacuum space-times", arXiv:1112.5779 (rough data, Zorn); [11] Ringström, *On the Topology and Future Stability of the Universe*, Ch. 23 (detailed CBG Hausdorff proof); [10] Planchon & Rodnianski, local uniqueness at regularity of local existence; [7] Klainerman–Rodnianski–Szeftel bounded L^2 curvature; [5] Geroch 1968 (second countability of Lorentzian manifolds).
- author: Marc Nardmann (pointed out proper-class issue); Mihalis Dafermos.
