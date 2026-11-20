# cameron2025uniqueness — On the uniqueness of continuous spacetime extensions in 1+1 dimensions with applications to weak null singularities

Peter Cameron, Jan Sbierski
arXiv 2025 (v2 June 2026, mentions two anonymous referees) · arXiv:2511.13422 · `pdf/cameron2025uniqueness.pdf`

**Tier: T3** — preprint (v2 acknowledges referee reports but no venue recorded); full rigorous proofs and explicit examples by a group with an established record on extensions; builds directly on the T2 [[sbierski2022uniqueness]].
**Relevance: 3** — Q1 (extension uniqueness), Q2 (C^0 vs C^1 structure, purely topological dichotomy), Q3 (weak null singularities, Reissner–Nordström Cauchy horizon), Q4 (a 1+1 topological classification that is a plausible formal target).
**Read:** full text (§1, §2 statements, §4 in detail, §5 statements and Examples 5.1–5.3)

## Summary
The paper studies continuous extensions of a 1+1 toy model of a weak null singularity, M_t = (-1,1)×(-1,0) with g = -Ω²(du dv + dv du), Ω continuous and positive up to {v=0}, asking whether every C^0 extension across {v=0} is locally C^0- (resp. C^1-) equivalent to the obvious "reference" extension. At the C^0 level: no in general — the *corner extension* (Example 4.1) sends all constant-u null curves to a single boundary point — but Theorem 4.3 shows these are the only two possibilities (reference-like locally, or a global corner), and Prop 4.2 gives a local-to-global rigidity (two nearby constant-u curves sharing an endpoint forces all of them to). A global spacetime-volume argument (Prop 4.4) excludes corners when the volume near {V=0} is infinite, which holds for sub-extremal Reissner–Nordström, so strongly spherically symmetric C^0 extensions across the RN Cauchy horizon are locally C^0-equivalent to the reference one (Cor 4.6). At the C^1 level there is no rigidity at all: Examples 5.1–5.2 give C^0-equivalent but C^1-inequivalent extensions, and Example 5.3 lifts this to 3+1 weak null singularities with no symmetry.

## Key points
- [V] In general not even the C^0 structure of a continuous extension across a null boundary is unique (abstract; Example 4.1).
- [V] Classification (Thm 4.3): any C^0 extension across {v=0} is either a corner (all constant-u null curves end at one point) or locally C^0-equivalent (homeomorphic up to the boundary) to the reference extension (§4.1, Thm 4.3, p. 27).
- [V] Local-to-global: if two nearby constant-u curves terminate at the same point, all constant-u curves do (Prop 4.2; §1.3, pp. 4–5).
- [V] Corners are excluded by infinite spacetime volume (Prop 4.4); hence every strongly spherically symmetric C^0 extension across the sub-extremal RN Cauchy horizon is locally C^0-equivalent to the reference extension (Cor 4.6, pp. 28–30).
- [P] Corners exist for finite U-chunks of RN (Example 4.5) only because r is constant on the RN Cauchy horizon; for generic spherically symmetric weak null singularities r is strictly monotone in U, which "even rules out" the finite-chunk exotic extensions (§4.2.1, footnote 5, p. 31).
- [V] No C^1 rigidity: C^0-equivalent but C^1-inequivalent extensions exist, both for corners (Ex 5.1) and for the reference C^0 structure (Ex 5.2); the latter carries over to 3+1 weak null singularities of Dafermos–Luk type without symmetry (Ex 5.3; §1.3).
- [P] Structural result (Prop 3.2): the reference extension has the "richest" C^0 structure (adds the most boundary points); a non-point boundary piece is a C^1 null curve transverse to the constant-u curves (§1.4).
- [P] Auxiliary: in 1+1 with g ∈ C^0, a locally Lipschitz causal curve achronal w.r.t. smooth timelike curves can be reparametrised as a C^1 null curve (Prop 2.6).
- [P] Contrast with [[sbierski2022uniqueness]]: there two *Lipschitz* anchored extensions agree to C^{1,1}; here, for C^0 extensions, even the topology at the boundary can differ, and the Hölder counterexample of [25] has a different mechanism (null boundary approached tangentially by both null families) that does not transfer to weak null singularities (§1.1, p. 4).

## Verified quotes
> "Firstly, we find that in general not even the C 0 -structure of the extension is uniquely determined by the assumption that the metric extends continuously."

> "we construct a whole family of C 0 -extensions of (Mt , gt ) across {v = 0} which terminate all future-directed null curves of constant u at the same point!"

> "if two nearby curves of constant u terminate at the same point, then all other curves of constant u must also terminate at this point."

> "We then conclude in Theorem 4.3 that a C 0 -extension of (Mt , gt ) across {v = 0} is either locally C 0 -equivalent to the reference extension Mt or has the global C 0 -structure of a corner extension."

> "It thus follows that every strongly spherically symmetric C 0 -extension across the Cauchy horizon is locally C 0 -equivalent to the reference extension."

> "due to the infinite spacetime volume between the event horizon and Cauchy horizon, no such corner extension can exist."

> "Secondly, we construct continuous extensions which have the same C 0 -structure, but do not have equivalent C 1 -structures. This construction also carries over to weak null singularities in 3+1-dimensions."

> "However, the nonuniqueness mechanism of the counterexample does not transfer to the case of weak null singularities."

> "This can be thought of as the statement that the reference extension has the “richest” possible C 0 -structure in the sense that it adds the most boundary points."

> "The local uniqueness problem for continuous extensions in 3+1-dimensions, as set out earlier, is a very intricate problem about which literally nothing is known to the best knowledge of the authors."

> "For generic spherically symmetric weak null singularities r is strictly monotonically decreasing in u and thus this local construction is not possible."

## Methods and evidence
- Data / setting: 1+1 double-null toy model; global model Q = (-∞,0)² for the RN quotient; 3+1 weak null singularity local piece M_wns = (-1,1)×(-1,0)×S² of Dafermos–Luk type.
- Baselines: [25] = [[sbierski2022uniqueness]] (Lipschitz anchored uniqueness); [3] Chruściel; [23] spherically symmetric C^{0,1}-inextendibility via holonomy blow-up.
- Evaluation: rigorous; explicit metrics (corner metric g̃_β, β ∈ (1/2,1)); volume computation for RN.
- Artifacts: n/a.

## Limitations and caveats
- The C^0 classification (Thm 4.3) is proved only in 1+1 dimensions; the 3+1 C^0 question is stated to be wide open ("literally nothing is known").
- The 3+1 positive result (Cor 4.6) is restricted to *strongly* spherically symmetric extensions (extend the quotient and take × S²), a strong ansatz.
- The corner construction needs Ω continuous up to u = ±1, i.e. a finite u-chunk; globally it is excluded by volume.
- Abstract and theorems agree; "carries over to 3+1" refers to the C^1 non-uniqueness only (Ex 5.3), which is what the abstract says. No claims_exceed_evidence.

## Contradictions and tensions
- [[sbierski2022uniqueness]]: Lipschitz anchored extensions are locally unique to C^{1,1}; here C^0 extensions fail uniqueness already at C^0 (corners) and always at C^1. Consistent (different regularity classes), but it sharpens the earlier paper's §6: the earlier Hölder counterexample kept C^0 equivalence, this one breaks it. Mirror entry is in that note.

## Open questions
- 3+1 classification of C^0 structures of extensions across weak null singularities without symmetry.
- Does the dichotomy (corner vs reference) have a purely causal statement — e.g. "the endpoint map from the null generators {u = const} to the boundary is either constant or locally injective"? The proof of Thm 4.3 is essentially that (compactness + injectivity ⇒ homeomorphism), with metric input only in Prop 4.2.
- Is the volume obstruction (Prop 4.4) replaceable by an admissible-measure (Dieckmann-type) obstruction?

## Relevance to the questions
**(i) Smooth vs causal content.** The *conclusions* about C^0 structure are topological: Theorem 4.3's dichotomy is a statement about where null generators end and whether the endpoint map is a homeomorphism; its final step is pure point-set topology (continuous bijection from a compact set is a homeomorphism). Metric input enters through near-Minkowski charts with cone comparison ĝ_{-ζ/(1+ζ)} ≺ g ≺ ĝ_ζ (Lemma 2.2), causal homotopies, the timelike distance and its lower semicontinuity, and the corner metrics; the global obstruction (Prop 4.4) uses spacetime volume. The C^1 results are intrinsically about differentiable structure and are invisible to any topological framework — they show that "the" differentiable structure of a weak singularity is not well-defined from the metric's continuity alone.
**(ii) What ETT could do.** ETT can state the C^0 half with no metric: extensions as open causal embeddings, null generators as K⁺-curves, the dichotomy as a statement about the endpoint map; cone comparison ≺ is exactly a statement about inclusion of causalities (a narrower and a wider causality sandwiching g), which ETT's family-of-preorders formalism expresses directly. Spacetime volume in Prop 4.4 is a measure on the spacetime — a natural candidate for ETT's admissible (Dieckmann) measures, provided the needed property (an isometric embedding cannot place infinite volume into a compact corner neighbourhood) is reformulated as finiteness of an admissible measure on compact sets. On conical/BTZ lines: the paper's boundary is a null hypersurface where Ω extends continuously (a weak null singularity), not a codimension-2 line, so there is no direct analogue; however the corner phenomenon — a whole null family collapsing to one boundary point — is reminiscent of the E_0 (BTZ) model, where the singular line is lightlike and the null generators accumulate. Whether a corner extension is ever a flat singular (G,X) extension is a concrete question.
**(iii) Candidate formalisation.** A topological 1+1 theorem in lean-causal: "Let X be a 1+1 ETT spacetime containing (-1,1)×(-1,0) with its null product causality, and let the null curves {u = c} have endpoints on ∂X. If the endpoint map c ↦ p(c) is locally injective near c₀, it extends to a homeomorphism of [c₀-ε,c₀+ε]×[v*,0] onto a closed neighbourhood; if it is non-injective on a neighbourhood, it is constant" (Thm 4.3 minus the metric input of Prop 4.2, which would become a hypothesis). The first half is formalisable now (compact Hausdorff bijection lemma from Mathlib); the dichotomy needs the 1+1 causal ordering of boundary points.

## Leads for next round
- term: weak null singularity; corner extension; reference extension; strongly spherically symmetric extension; local C^0/C^1 equivalence; near Minkowski neighbourhood; causal homotopy; Kruskal coordinates; C^{0,1}_loc-inextendibility.
- cited: [7] Dafermos–Luk "The interior of dynamical vacuum black holes I: C^0-stability of the Kerr Cauchy horizon"; [23] Sbierski, spherically symmetric weak null singularities C^{0,1}_loc-inextendible via holonomy blow-up; [26] Sbierski, recent work on C^{0,1}_loc-inextendibility of weak null singularities without symmetry (combined with [25]); [43] Luk, weak null singularities in vacuum; [5] Chruściel–Grant; [11] Grant–Kunzinger–Sämann–Steinbauer; [8]/[9]/[10]/[27]/[28] ideal boundary constructions (causal boundary, b-boundary, abstract boundary); [15] Graf–Ling maximisers in Lipschitz spacetimes.
- author: Peter Cameron (Imperial); Jonathan Luk; Mihalis Dafermos; Maxime Van de Moortel (generic weak null singularities, r monotone).
