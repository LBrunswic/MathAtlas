# cameron2026spherically — Spherically symmetric inextendibility of weak null singularities with Christoffel symbols in L^s_loc

Peter Cameron, Jan Sbierski
arXiv preprint 2026 · arXiv:2609.05167 · `pdf/cameron2026spherically.pdf`

**Tier: T3** — unreviewed preprint; complete proofs, includes a counterexample showing a hypothesis is necessary; builds on the authors' own (to appear, CAG) 1+1 rigidity paper.
**Relevance: 2** — Q1 (first sub-Lipschitz result, Christodoulou class reached in symmetry), Q2 (rests on a purely C^0/topological rigidity theorem in 1+1), Q3 (weak null singularities, low regularity; "corner" extensions), Q4 (1+1 C^0 rigidity is a plausible topological target).
**Read:** full text §1–2 closely; §3–4 statements

## Summary
Local pieces of a spherically symmetric black-hole interior near a weak null singularity {v=0} (metric continuous up to v=0, ∂_v r singular) are shown to admit no strongly spherically symmetric extension with C^0 metric and Christoffel symbols in L^s_loc, s>1, across {v=0}, under the integrated blow-up ∫|∂_v r|^s → ∞ and the condition that the extension is locally C^0-equivalent to the reference boundary extension (Thm 1.1). That last condition is necessary: §3.3 builds a "corner" C^0 ∩ W^{1,s} extension in which all outgoing null geodesics converge to one point. For RNV and DLO spacetimes, corners are excluded by the 1+1 rigidity theorem of [1] (dichotomy corner vs. local homeomorphism) plus a global infinite-volume argument (RNV) or strict monotonicity of r along the singularity (DLO), giving Corollaries 4.1, 4.2 — showing Dafermos' L¹_loc-Christoffel extension is optimal among spherically symmetric extensions.

## Key points
- [V] Result: inextendibility with C^0 metric and Christoffel symbols in L^s_loc, s>1, spherically symmetric (abstract; Thm 1.1).
- [V] Restriction: extensions are "strongly spherically symmetric" (ι = ι_Q × id_{S²}, fixed SO(3) orbits) (§1.1).
- [V] The C^0-equivalence hypothesis is necessary in general (corner example, §3.3).
- [V] For RNV the obstruction to corner extensions is "entirely global" (infinite spacetime volume, Prop 2.5); corner construction uses that r extends as a constant on the singularity (§1.1).
- [V] For DLO, r is generically strictly decreasing along the weak null singularity, ruling out corners locally (§1.1).
- [V] First geometric inextendibility at the level of L²-type Christoffel symbols (§1).
- [V] Hawking mass stays bounded at the RNV weak null singularity (§1).
- [P] Thm 2.4 (= [1] Thm 4.3, 1+1 C^0 rigidity): a C^0 extension of (Q,g_Q) with a limit point p̃ at (u*,0) either (a) sends the whole boundary segment to p̃ ("corner") or (b) extends locally as a homeomorphism (§2).
- [P] Lemma 1.2: in strongly spherically symmetric extensions, g⁻¹(dr,dr) is a scalar at first-derivative level, so mass inflation gives C^{0,1}_loc inextendibility at once (§1.2).
- [V] Local topological (C^0) structure of extensions had to be understood first, done in [1] (§1.2).
- [P] Claims result applies also to Poisson–Israel mass-inflation spacetimes and van de Moortel's charged scalar field spacetimes (§1.1), without detailed proof here.

## Verified quotes
> "we prove the inextendibility of spherically symmetric weak null singularities as spherically symmetric Lorentzian manifolds with a continuous metric and Christoffel symbols in Lsloc for s > 1."

> "extensions as strongly spherically symmetric. This restriction allows us to apply many of the results of [1]"

> "In Section 3.3, we show that this restriction is necessary in general"

> "In the case of the Reissner-Nordström-Vaidya spacetime, the obstruction to the existence of such C 0 -extensions is entirely global."

> "This construction crucially uses that the area radius function extends as a constant to the weak null singularity."

> "the area radius function is generically strictly monotonically decreasing along the weak null singularity which even rules out the corner extensions of the local spacetime pieces"

> "However, until now no geometric inextendibility results at the level of locally square-integrable Christoffel symbols have been available."

> "Note that the Hawking mass remains uniformly bounded at the weak null singularity of the Reissner-Nordström-Vaidya spacetime."

> "Thus, the local topological (C 0 ) structure of such extensions has to be understood (this has been achieved in [1])."

## Methods and evidence
- Data / setting: M = Q × S², Q ⊂ R² double null, Ω, r continuous to v=0; extensions of product form.
- Baselines: [[sbierski2020holonomy]] (unrestricted C^{0,1}_loc), Dafermos' explicit L¹ extension, Lemma 1.2 (mass inflation).
- Evaluation: proofs + explicit corner counterexample.
- Artifacts: n/a.

## Limitations and caveats
- Only strongly spherically symmetric extensions (fixed orbit structure) — much weaker than unrestricted inextendibility; the abstract says "as spherically symmetric Lorentzian manifolds", the body makes clear the stronger "strongly" restriction; not counted as overreach but must be cited with the qualifier.
- Needs local C^0-equivalence, discharged per example.
- Applications to Poisson–Israel and van de Moortel spacetimes asserted, not proved here.

## Contradictions and tensions
- Extends [[sbierski2020holonomy]] §4 below Lipschitz but in a restricted category; the unrestricted Lipschitz result for the same spacetimes remains [[sbierski2020holonomy]] Thm 4.31.
- Addresses the obstacle named in [[sbierski2024lipschitz]] Remark 3.38 (C¹-structure control below Lipschitz) by symmetry rather than in general.
- Cites [[luk2026formation]] and Gurriaran as independent proofs of weak null singularity formation in Kerr.

## Open questions
- Remove the symmetry restriction on extensions; reach s=1?
- Is the 1+1 corner/homeomorphism dichotomy a purely causal statement (valid for topological 2D spacetimes with a causality)?

## Relevance to the questions
- (i) Analytic part (L^s Christoffel, ∂_v r blow-up) is differential. Thm 2.4 ([1]'s 1+1 dichotomy) and the corner construction are C^0/topological; Prop 2.5 uses spacetime volume (measure). The "corner" phenomenon — a whole null boundary segment collapsing to one point of the extension — is a topological feature of the future boundary.
- (ii) ETT is well placed for the topological layer: in 1+1, a causality on a surface, the future boundary of an open causal embedding, and the corner/homeomorphism dichotomy could be stated without a metric; the infinite-volume obstruction resembles ETT's admissible (Dieckmann) measures. Flat conical/BTZ spacetimes are not spherically symmetric weak null singularities; no example/counterexample — but the 2D quotient of an E_0 (BTZ) neighbourhood by rotation has a null singular line, loosely analogous to a null boundary; speculative.
- (iii) Candidate: Thm 2.4 ([1] Thm 4.3) for a 1+1 topological spacetime with a causality: "an open causal embedding of a null-bounded 2D region with a limit point at a boundary point either collapses the whole boundary segment to that point or extends homeomorphically near it". Requires reading [1] (arXiv:2511.13422) in round 2 to see whether its proof uses only causal/topological structure.

## Leads for next round
- term: strongly spherically symmetric extension; corner extension; locally C^0-equivalent; continuous boundary extension
- cited: [1] Cameron–Sbierski, "On the uniqueness of continuous spacetime extensions in 1+1 dimensions with applications to weak null singularities", arXiv:2511.13422 (to appear CAG) — high priority for ETT; [22] Sbierski, "Uniqueness and non-uniqueness results for spacetime extensions", IMRN 2024; [8] Galloway–Ling; [9] Gautam mass inflation; [10] Gurriaran; [2] Christodoulou formation of black holes (C^0 ∩ W^{1,2} formulation)
- author: Peter Cameron, Ofek Gautam, Maxime Van de Moortel
