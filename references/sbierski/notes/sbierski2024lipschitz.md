# sbierski2024lipschitz — Lipschitz inextendibility of weak null singularities from curvature blow-up

Jan Sbierski
Inventiones mathematicae 2024 (published 2026, vol. 243, 961–991 per [[cameron2026spherically]] ref [23]) · arXiv:2409.18838 / doi:10.1007/s00222-025-01387-0 · `pdf/sbierski2024lipschitz.pdf`

**Tier: T2** — peer-reviewed (Inventiones), complete proofs, sharpness examples; used as a black box by [[luk2026formation]] (and per that paper by Gurriaran's concurrent result), but not independently re-proved.
**Relevance: 2** — Q1 (main theorem of the "no symmetry" line), Q2 (relies on uniqueness of C¹ structure of Lipschitz extensions — an inherently differential ingredient), Q3 (weak null singularities; low-regularity extensions), Q4 (little directly formalizable).
**Read:** full text (§1–3 closely, §4 examples skimmed)

## Summary
The paper proves that a local piece of a black-hole interior in double-null gauge (the Dafermos–Luk gauge for perturbed Kerr), whose metric extends continuously to a Cauchy horizon CH⁺ = {u̲=0}, admits no C^{0,1}_loc extension through which a timelike geodesic approaching CH⁺ leaves, provided (a) bounds on certain Ricci coefficients (3.7) and an angular-shift bound (3.15) hold and (b) an integrated curvature blow-up (3.16) holds for all continuous vector fields ε-close to given ones (Thm 3.14). The proof: reduce to a null geodesic (using the precursor uniqueness paper [34]); show the C¹ structure of any Lipschitz extension locally agrees with that of the Dafermos–Luk C^0 extension; then convert the divergent curvature integral via Stokes into a boundary integral of Christoffel symbols, which is bounded in a Lipschitz chart. No symmetry assumptions are made; the curvature blow-up is assumed, expected generically (later supplied by [[luk2026formation]]).

## Key points
- [V] First low-regularity inextendibility of singularities with no symmetry assumptions (§1).
- [V] New mechanism: curvature blow-up ⇒ low-regularity inextendibility (§1 outline, Step 3).
- [V] More parsimonious than the holonomy method of [[sbierski2020holonomy]]: only an integrated curvature blow-up is needed (§1).
- [P] Thm 3.14: setting of Prop 3.6 (metric (2.1) C², extends continuously to u̲=0; sup bounds on ω, η, η̲, χ̲ and an L¹_u̲ bound on χ) + (3.15) + (3.16) ⇒ no C^{0,1}_loc extension in which an affinely parametrised future-inextendible timelike geodesic with u̲→0 has a limit point (§3.2).
- [V] Condition (3.16) is sharp: Examples 4.7, 4.8 are counterexamples if the absolute value is moved inside or if only the fixed X_i are used (Remark 3.21).
- [V] Assumption (3.15) is not a formal statement of Dafermos–Luk and "requires some more work to establish" (Remark 3.17).
- [P] Step 2 rests on local uniqueness of C¹ structure for Lipschitz extensions ([34], "Uniqueness and non-uniqueness results for spacetime extensions", IMRN 2024); fails below Lipschitz (Remark 3.38).
- [V] Weak null singularities admit continuous extensions where the identification map is not a C¹ diffeomorphism to the boundary (Remark 3.38, citing [2] = Cameron–Sbierski uniqueness paper).
- [V] Lorentzian causality below Lipschitz "changes drastically" (§1, citing Chruściel–Grant [4]).
- [P] Remark 3.38 sketches a route to C^0 ∩ W^{1,2}_loc via a squared-and-integrated version, blocked by the missing analogue of Step 2.
- [P] Remark 3.20: global inextendibility combines this local theorem with timelike geodesic completeness of the exterior (Galloway–Ling–Sbierski [9]).

## Verified quotes
> "In particular, no symmetry assumptions on the spacetime are made."

> "The proof given here establishes for the first time an implication that curvature blow-up leads to"

> "The new approach presented here is more parsimonious in the sense that only an integrated blow-up bound on curvature is needed, which is easier to establish analytically."

> "Secondly, Lorentzian causality below Lipschitz regularity changes drastically in comparison to the familiar one of smooth metrics [4]."

> "Counterexamples to both formulations are presented in Examples 4.7 and 4.8 in Section 4."

> "The bound (3.15) is not contained as a formal statement in [7] and requires some more work to establish."

> "The main problem with implementing this idea of proof is that the analogue of Step 2 is not known to hold; below Lipschitz regularity the methods of [34] break down."

> "Indeed, in [2] it is shown that weak null singularities as considered here admit continuous extensions for which the identification map id does not extend as a C 1 -regular diffeomorphism to the boundary!"

> "All manifolds considered in this paper are assumed to be smooth."

> "Note that such a double null gauge as in (2.1) exists if, and only if, one can find two solutions u and u to the Eikonal equation such that the intersection of their level sets form topological two-spheres."

## Methods and evidence
- Data / setting: 3+1 Lorentzian metric in double-null gauge on (−1,1)×(−1,0)×S², g ∈ C², continuous up to u̲=0.
- Baselines: [[sbierski2020holonomy]] (spherical, holonomy); C^0 results based on geodesic completeness.
- Evaluation: rigorous proof; spherically symmetric toy examples (§4, Ex. 4.1) satisfying hypotheses, and counterexamples showing sharpness.
- Artifacts: n/a.

## Limitations and caveats
- Conditional: curvature blow-up (3.16) and the bound (3.15) are assumed; their verification for perturbed Kerr is deferred (supplied for (3.16) by [[luk2026formation]] and Gurriaran).
- Local theorem only; global SCS near Kerr also needs control of the interior beyond the weak null singularity, which is "still not well-understood" (Remark 3.20).
- Threshold C^{0,1}_loc; C^0 ∩ W^{1,p}_loc open.
- Abstract consistent with theorem: it says the blow-up is "assumed" and the SCS contribution "expected" — no overreach.

## Contradictions and tensions
- Complements [[sbierski2020holonomy]]: holonomy method would need pointwise blow-up of χ̲ outside symmetry.
- [[cameron2026spherically]] goes below Lipschitz but only in strongly spherically symmetric extensions, matching Remark 3.38's diagnosis that C¹-structure control is the obstacle.

## Open questions
- Can the C¹-structure-uniqueness step be replaced by a purely topological/causal rigidity statement (as Cameron–Sbierski do in 1+1 for C^0)?

## Relevance to the questions
- (i) Heavily differential: double-null gauge, Ricci coefficients, Stokes theorem on curvature, C¹ structure uniqueness. Causal/topological ingredients: Prop 1.3 (future boundary chart, achronal Lipschitz graph), the reduction "an extension exists ⇒ some inextendible timelike geodesic has a limit point", Remark 3.22's homeomorphic extension of a null flow (a topological statement).
- (ii) ETT could state the topological skeleton (future boundary of an open causal embedding; Cauchy horizon as boundary of a domain of dependence) but not the curvature mechanism. Flat ETT spacetimes have zero curvature on the regular part, so (3.16) never holds there: conical/BTZ lines are outside the theorem's scope, neither examples nor counterexamples.
- (iii) No direct formalization target; possible small target: "if ι: M ↪ M̃ is an open causal embedding of a globally hyperbolic ETT spacetime with ∂ι(M) ≠ ∅, then ∂⁺ι(M) ∪ ∂⁻ι(M) ≠ ∅" (the topological Lemma 2.5 of [[sbierski2020holonomy]], cited as the starting point here).

## Leads for next round
- term: double null gauge; Ricci coefficients; Cauchy horizon C^0-stability; local uniqueness of C¹ structure of extensions; integrated curvature blow-up
- cited: [7] Dafermos–Luk, "The interior of dynamical vacuum black holes I" (C^0 stability of Kerr CH); [34] Sbierski, "Uniqueness and non-uniqueness results for spacetime extensions" (IMRN 2024); [2] Cameron–Sbierski uniqueness of continuous extensions in 1+1 (arXiv:2511.13422); [12] synthetic curvature blow-up in extensions; [25] subtleties of curvature blow-up vs inextendibility; [9] Galloway–Ling–Sbierski; [23] Minguzzi–Suhr; [4] Chruściel–Grant; [27] extendibility under curvature bounds
- author: Mihalis Dafermos, Jonathan Luk, Sebastian Gurriaran, Peter Cameron
