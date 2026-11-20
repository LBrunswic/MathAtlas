# abbrescia2025quasilinear — A quasilinear wave with a supersonic shock in a weak solution interrupting the classical development

Leonardo Abbrescia, Pieter Blue, Jan Sbierski, Jared Speck
arXiv preprint 2025 · arXiv:2511.07594 · `pdf/abbrescia2025quasilinear.pdf`

**Tier: T3** — unreviewed preprint, but by established authors in shock formation and MGHD theory, with complete elementary proofs on an explicit model.
**Relevance: 2** — Q1 (recent Sbierski theme: MGHDs of shock-forming PDE), Q2 (causal bubbles in a continuous metric: where smooth causality fails), Q3 (weak solutions beyond the classical development; a continuous but non-Lipschitz metric on the boundary).
**Read:** full text (§1, §3.2–3.4, Appendices A–B read; Burgers computations in §2–3.1 skimmed).

## Summary
The authors study a 1+1 quasilinear wave equation, modelled on irrotational isentropic compressible Euler and reducible to Burgers' equation for Ψ = ∂_tΦ − 2∂_xΦ, with explicit C^∞ data Φ(0,x)=0, ∂_tΦ(0,x) = −arctan x. The classical solution's MGHD (with respect to the acoustical metric g(Ψ)) is constructed globally, and its boundary is described: an initial singularity S, a singular boundary B where second derivatives blow up while Φ and ∂Φ stay bounded, and a smooth null Cauchy horizon C. The MGHD is proved unique because its boundary satisfies the one-sided criterion of [[eperon2018predictability]] (Thm 4.82). They also build the global Oleinik entropy weak solution, which solves the shock development problem, and prove that it agrees with the classical solution before the shock but differs at points of the MGHD to the future of the first singularity. At B the extended metric is only C^{0,1/2}, and every point of B carries a "causal bubble".

## Key points
- [V] Main result (Thm 1.2): existence of a classical solution on Ω_C ⊊ R^{1+1}; Ω_C is the *unique* MGHD; its boundary is S ⊔ B ⊔ C, each connected, and B = {S(z) : z>0} with S(z) = (1+z^2, (2 − arctan z)(1+z^2)+z) (§1.2.2, Thm 1.2 (i)–(iii)).
- [V] Sharp boundary regularity: Φ_C extends as C^{1,1/3} on S and C^{1,1/2} on B; the acoustical metric extends as C^{0,1/3}, C^{0,1/2}, and smooth to S, B, C respectively (Thm 1.2 (iii)(e)–(f)).
- [P] B is intrinsically null for the extended metric but "extrinsically spacelike" (Thm 1.2 (iii)(g), (iv); §3.4).
- [V] Causal bubbles: every p ∈ B has J^-(p) \ I^-(p) with non-empty interior in cl(Ω_C), possible only below Lipschitz regularity (Cor 1.3, §3.4, citing Chruściel–Grant [CG12]).
- [V] Uniqueness of the MGHD is obtained from the one-sided boundary condition of [ERS19] (= [[eperon2018predictability]] Thm 4.82), which is "teleological" (§1.2.1).
- [P] Weak solution (Thm 1.10): unique global Oleinik entropy solution Φ_W on all of R^{1+1}; there is p ∈ Ω_C with Φ_W(p) ≠ Φ_C(p); the agreement set Ω_A is a GHD with Σ ⊊ Ω_A ⊊ Ω_C ⊊ Ω_W; Φ_W solves the shock development problem; it extends Φ_C in a C^1 way across C but its first derivatives are only C^{0,1/2} there.
- [P] Geometric determinism (Def 1.7 (v), Thm 1.10 (v)): the shock curve is spacelike for g(Ψ_C) (behind) and timelike for g(Ψ_SDP) (ahead), equivalent to the Lax entropy conditions — a curve whose causal type differs for the two causal cones on either side.
- [V] The paper corrects an error of [ERS19]: they believed Christodoulou had constructed the full MGHD and boundary (footnote 8).
- [P] Stability under small data perturbation is asserted "with minor additional effort" but not proved (end of §1.2.2).

## Verified quotes
> "Our main results provide the first example of a provably unique MGHD for a shock-forming quasilinear wave equation solution; it is provably unique because its boundary has a favorable global structure that we precisely describe."

> "Of particular interest is our proof that the classical and weak solutions agree before the shock but differ in a region to the future of the first singularity where both solutions are defined."

> "The solution ΦC extends as a C 1,1/3 function on S and as a C 1,1/2 function on B, and this regularity is sharp."

> "The acoustical metric g extends as a C 0,1/3 , a C 0,1/2 , and as a smooth Lorentzian metric to S, B, and C, respectively."

> "Then any point p ∈ B has a causal bubble with respect to the extended acoustical metric g."

> "Such behaviour can only happen for Lorentzian metrics below Lipschitz regularity (see [CG12]) and indeed does happen in our example at the singular boundary B"

> "The authors of [ERS19] were under the mistaken impression that the full MGHD and its boundary had been constructed in [Chr07], cf. the comment after [ERS19, Lemma 4.86]."

> "This result is teleological in the following sense: one must construct the MGHD in its entirety to guarantee the geometric condition, which requires that the MGHD must only lie on one side of its boundary, holds."

> "Then, with respect to g(ΨC ), the shock curve is spacelike. With respect to g(ΨSDP ), the shock curve is timelike. This is called the geometric determinism condition."

> "We close this subsection by stating that, with minor additional effort, the results of Theorem 1.2 could be proved to be stable."

## Methods and evidence
- Data / setting: explicit 1+1 model (1a)–(1b); reduction to Burgers' equation for Ψ; method of characteristics in the acoustical null frame {L, L̲}.
- Baselines: Christodoulou's relativistic Euler shock monographs [Chr07, Chr19]; Abbrescia–Speck [AS22]; Shkoller–Vicol [SV24]; Lebaud's 1D shock development.
- Evaluation: rigorous explicit proofs.
- Artifacts: none.

## Limitations and caveats
- One explicit model in 1+1 with one specific data choice; stability and other data regimes are claimed or listed as open (Appendix B), not proved.
- Uniqueness of the MGHD relies on the teleological one-sided criterion, not on a structural theorem.
- Abstract's headline claims match Theorems 1.2 and 1.10; no overstatement found (`claims_exceed_evidence=false`).
- Not about Einstein's equations: the "spacetime" is the acoustical geometry on a fixed R^{1+1}.

## Relevance to the questions
**(i) Smooth vs. order-topological.** The MGHD notion (Appendix A) uses C^1 timelike curves and a smooth metric; the uniqueness proof routes through [[eperon2018predictability]] Thm 4.82, whose hypothesis is topological (boundary locally a continuous graph). §3.4 deliberately leaves the smooth world: on cl(Ω_C) the metric is only continuous, causal curves are piecewise C^1, and I^- ≠ interior-of-J^- (causal bubbles). The shock-development geometric determinism condition compares *two* causal cones along a curve.
**(ii) What ETT could state or generalise.** Causal bubbles are exactly where the C^0 causal structure (J via causal curves) and the "continuously reachable"/topological closures diverge from I; ETT's K^± vs J^± vs I^± distinction is the natural language to state Cor 1.3 without a metric, and to ask whether an ETT causality on cl(Ω_C) (including the boundary) is still closed/strongly causal. The weak solution's spacetime is a piecewise-smooth Lorentzian structure with an interface (the shock K) across which the cone jumps; this is analogous in spirit to ETT's singular flat spacetimes, where the causality is defined on a topological space with a singular locus — but the singular locus here is codimension 1 (a hypersurface), not a conical/BTZ line. No holonomy or conical structure appears. Relevance to Q3 is via low-regularity Lorentzian geometry and weak solutions, not via singular flat spacetimes.
**(iii) Candidate statements for lean-causal.** Weak formalization targets: (a) an ETT definition of "causal bubble" (J^-(p) \ I^-(p) has non-empty interior) together with the theorem that it cannot occur for a causality coming from a Lipschitz cone field — a research statement, not a library one; (b) a "two-cone interface" causality on a topological space (two causalities on either side of a closed set, with a determinism condition on the interface) as a test case for ETT's gluing of causal structures. Neither is a near-term Lean target.

## Contradictions and tensions
- [[eperon2018predictability]]: this paper (footnote 8) corrects ERS19's claim that Christodoulou's [Chr07] MGHD and boundary were fully constructed; ERS19's uniqueness of the MGHD for Christodoulou's data therefore does not follow.
- [[sbierski2013existence]] claims the CBG technique works down to C^2; here the boundary metric is C^{0,1/2}, where causality theory itself changes (bubbles) — consistent, but shows where the dezornified argument would have to be rebuilt.

## Open questions
- Existence of smooth data with non-unique MGHDs for this model (Appendix B).
- Structure/regularity of MGHD boundaries for generic data; can they be non-rectifiable (Appendix B)?
- 1+1 isentropic compressible Euler analogue; global multi-D MGHD structure beyond the local pieces of [AS22, SV24].

## Leads for next round
- term: causal bubble; acoustical metric; singular boundary; shock development problem; geometric determinism; teleological uniqueness; Oleinik entropy solution.
- cited: [CG12] Chruściel & Grant, "On Lorentzian causality with continuous metrics"; [Chr07] Christodoulou 2007 shocks; [Chr19] Christodoulou 2019 *The shock development problem*; [AS22] Abbrescia–Speck singular boundary (C^{1,1/2}); [SV24] Shkoller–Vicol; [Kom13] Kommemi, global structure of spherically symmetric charged scalar field spacetimes; [GR24] Ginsberg–Rodnianski; [MRRS22a,b] Merle–Raphaël–Rodnianski–Szeftel implosion.
- author: Jared Speck, Leonardo Abbrescia, Pieter Blue (Edinburgh, Sbierski's group).
