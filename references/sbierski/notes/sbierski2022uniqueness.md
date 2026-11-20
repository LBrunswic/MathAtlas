# sbierski2022uniqueness — Uniqueness and non-uniqueness results for spacetime extensions

Jan Sbierski
International Mathematics Research Notices 2024 (arXiv 2022) · doi:10.1093/imrn/rnae194 · arXiv:2208.07752 · `pdf/sbierski2022uniqueness.pdf`

**Tier: T2** — peer-reviewed (IMRN), full proofs, single author with a track record on extensions; headline matches Theorem 5.24 exactly; not independently reproduced, but already used as the base result by [[cameron2025uniqueness]].
**Relevance: 3** — Q1 (extension theory), Q2 (the regularity threshold is the whole point), Q3 (weak null singularities, holonomy), Q4 (anchoring / Hausdorff-gluing statements).
**Read:** full text (§§1–3, 5.2, 6 and App. A in detail; §4–5.1 skimmed for statements)

## Summary
The paper asks when two extensions of a time-oriented globally hyperbolic Lorentzian manifold (M,g) agree "up to the boundary". Globally, they need not (Taub-NUT/Misner: both analytic, maximal, yet extend through different future boundaries). Sbierski localises the question: two extensions are *anchored* by a future-inextendible causal curve that has limit points in both, and he shows that anchored C^{0,1}_loc extensions are locally isometric up to the boundary, with the identification map extending as a C^{1,1}_loc diffeomorphism across a Lipschitz-graph piece of the future boundary (Thm 1.1 = Thm 5.24). The proof goes through (a) a characterisation of when two inextendible curves share a limit point via connecting curves of vanishing generalised affine (b-)length (Props 5.1, 5.7), and (b) parallel transport of a frame along a space-filling family of curves, which encodes the C^1 structure at the boundary (Prop 5.11). Section 6 shows sharpness: a 1+1 FLRW-type model with two anchored Hölder extensions whose identification map is a homeomorphism but not C^1. Appendix A gives a timelike-geodesic proof for C^2 extensions and answers Manchak: a C^∞-inextendible spacetime with a point removed only extends by reinserting the point (Thm A.5).

## Key points
- [V] Main theorem: anchored C^{0,1}_loc extensions of a globally hyperbolic (M,g), g ∈ C^1, agree locally up to the boundary; the identification extends as a C^{1,1}_loc isometric diffeomorphism (Thm 1.1 / Thm 5.24, pp. 4–5, 27).
- [V] The anchoring curve need only be causal with a mere limit point in each extension — not a null geodesic, not transversal, not differentiable at the boundary (§1.2 items 1 and 4, p. 6).
- [V] Sharpness: two anchored Hölder extensions, exponent arbitrarily close to 1, whose identification map is not C^1 (§1.2, §6, pp. 5, 28–30).
- [V] Improvement over Chruściel [4] (Thm 1.2, smooth/C^{1,1}, conformal, d ≥ 2, null-geodesic anchoring, smooth boundary): this result is isometric only but valid in d = 1 and optimal at Lipschitz (§1.2 items 1–3).
- [V] The future boundary of a globally hyperbolic spacetime in a C^0 extension is locally a Lipschitz achronal graph (future boundary chart, Prop 2.3, from Sbierski's earlier [19]); no boundary regularity is assumed (§1.2 item 3; Prop 2.3).
- [V] Global non-uniqueness is a Hausdorffness phenomenon: in Taub-NUT/Misner an endpoint cannot be added to the other extension "without making the manifold non-Hausdorff" (§1.1, p. 4).
- [P] For merely C^0 extensions, the future boundary defined via limit points of timelike curves is strictly larger than via smooth timelike curves extending into M̃; Example 3.10 (a causal bubble at the origin) shows Prop 3.5 fails in C^0 (§3, Example 3.10, pp. 15–16).
- [P] Same-limit-point criterion: two future-inextendible curves share a limit in a Lipschitz extension iff there are connecting curves with gap-length → 0 (b-boundary style; Props 5.1, 5.7, Remark 5.6.3).
- [V] Manchak's question: removing a point from a C^∞-inextendible spacetime admits only the trivial C^∞ extension (Thm A.5, p. 33).
- [V] Prop 5.11 is flagged as the key step for C^{0,1}_loc-inextendibility of weak null singularities without symmetry (footnote 8, p. 7).

## Verified quotes
> "any two extensions which are anchored by an inextendible causal curve ... in the sense that γ has limit points in both extensions, must agree locally around those limit points on the boundary as long as the extensions are at least locally Lipschitz continuous"

> "anchored extensions which are only Hölder continuous do in general not enjoy this local uniqueness result"

> "is a diffeomorphism and extends as a Cloc -regular isometric diffeomorphism to"

> "we give an example of a smooth time-oriented and globally hyperbolic Lorentzian manifold which admits two anchored Hölder continuous extensions with Hölder exponent 0 < α < 1 arbitrarily close to 1, but such that the identification map id does not extend as a C 1 -regular map"

> "Our result only considers isometric extensions and is also valid for d = 1."

> "The anchoring curve γ in Theorem 1.1 does not have to be a null geodesic nor does it have to meet the boundary transversally. Indeed, it does not even have to be differentiable at the boundary."

> "But at the same time an end point cannot be added to the extension M̂ without making the manifold non-Hausdorff."

> "no differentiability assumption on the boundary has to be made in Theorem 1.1, but it follows that the most general future boundary of a globally hyperbolic spacetime is locally Lipschitz regular"

> "Thus, the analogue of Proposition 3.5 for C 0 -extensions is false."

> "Let (M, g) be a connected time-oriented Lorentzian manifold with g ∈ C ∞ that is C ∞ inextendible. Let p ∈ M . Then every C ∞ -extension of M \ {p} is smoothly isometric to (M, g)."

> "Proposition 5.11 is a key step in future work on the C 0,1 -inextendibility of weak null singularities without any symmetry"

> "an analogue of Theorem 5.24 breaks down below Lipschitz regularity; it is not a matter of just sacrificing the same degree of regularity of the extension"

## Methods and evidence
- Data / setting: time-oriented globally hyperbolic (M,g), g ∈ C^1; extensions C^{0,1}_loc (main), C^0 (counterexamples), C^2/C^∞ (appendix). Manifolds always smooth.
- Baselines: Chruściel 2010 conformal boundary extensions (Thm 1.2 = [4, Thm 3.1]).
- Evaluation: rigorous proof; sharpness by explicit example (§6, 1+1 FLRW g = -dt² + a(t)² dx², a = t^p, two null straightenings giving Hölder exponent 2p/(p+1)).
- Artifacts: n/a (pure mathematics).

## Limitations and caveats
- Uniqueness is only **local and up to the boundary**; nothing beyond the boundary (footnote 4) and nothing global (Fig. 1 example; Taub-NUT).
- Requires (M,g) globally hyperbolic with g ∈ C^1 and both extensions locally Lipschitz; the C^0 case — the one relevant to strong cosmic censorship in C^0 — is left open, and §6 shows it fails in general below Lipschitz.
- Only isometric (not conformal) extensions; only the *future boundary* (points reached by timelike curves) is controlled. The obvious extension of an open set of Minkowski with rough boundary: local uniqueness "still open" (§1.2 item 3).
- Abstract matches the theorems; no claims_exceed_evidence.

## Contradictions and tensions
- [[cameron2025uniqueness]] builds on this result and notes that the §6 counterexample mechanism (null boundary approached tangentially by both null families) "does not transfer" to weak null singularities, where the reference boundary is a limit of the null hypersurfaces {v = const}; Cameron–Sbierski instead fix a reference C^0 extension and find non-uniqueness of the C^0 structure itself (corner extensions). Not a contradiction but a sharpening: below Lipschitz, failure can already occur at the C^0 level, not only C^1.

## Open questions
- Local uniqueness of anchored C^0 extensions with additional structure (e.g. Christoffel symbols in L²_loc) — the SCC-relevant class.
- Rough-boundary open subsets of Minkowski: is the obvious extension locally unique? (stated open, §1.2.3).
- Is there a purely causal/topological version of "anchored ⇒ locally homeomorphic up to the boundary"? The paper's C^0 counterexample (§3) shows the *set* of future boundary points depends on whether one uses limit points or smooth-timelike endpoints, i.e. on the curve class — exactly the kind of choice an order-theoretic causality fixes once.

## Relevance to the questions
**(i) Smooth vs causal content.** The *statement* of local uniqueness needs the differentiable structure (C^{1,1} extension of id) and the *proof* is irreducibly metric: generalised affine (b-)length of connecting curves, parallel transport of an orthonormal frame, Lipschitz bounds on Christoffel symbols (§§4–5). The purely causal/topological ingredients are: global hyperbolicity and Cauchy hypersurfaces of M; the future boundary as endpoints of future-inextendible causal curves; achronality of the boundary graph (Prop 2.3); the "same limit point" relation between inextendible curves; and the Hausdorff obstruction to gluing two extensions (Taub-NUT). At the C^0 level, the first part of the conclusion (id extends as a homeomorphism up to the boundary) is a topological statement, and §6 shows that it survives below Lipschitz while the C^1 part fails — so the C^0/causal skeleton is more robust than the differentiable one.
**(ii) What ETT could do.** ETT's causality-on-open-sets framework can *state* the topological half: "an extension" = open embedding of a globally hyperbolic (ETT) spacetime into a causal space compatible with the causality; "future boundary" = limit points of K⁺-inextendible causal curves; "anchored" = a common such curve; "locally C^0-equivalent up to the boundary" = id extends to a homeomorphism of closures near the limit points. It cannot recover the C^{1,1} conclusion (needs connection). It is also the natural home for the Hausdorff-gluing obstruction, which is exactly lean-causal's CBG design point (Hausdorffness of the glued maximal development) — the Taub-NUT discussion here is the extension-side mirror of the CBG Hausdorff theorem. For singular flat spacetimes (E_α / E_0 cones), the extension across a conical or BTZ line is *rigid* (G,X)-geometry, so the anchored-uniqueness question becomes: do two (G,X)-extensions anchored by the same curve agree near the endpoint? For rigid geometries this is analytic continuation of developing maps and should hold with no regularity hypothesis — a clean ETT analogue of Thm 5.24.
**(iii) Candidate formalisation.** (a) Topological: "If two ETT extensions of a globally hyperbolic ETT spacetime M are anchored by the same inextendible causal curve and the boundary is locally an achronal graph in both, then the gluing of the two along M is Hausdorff near the anchor points" — this is the anchored-curve lemma that also drives CBG's Hausdorffness. (b) Rigid-geometry version: for flat (or singular-flat, E_α/E_0-modelled) extensions, anchored extensions agree on a neighbourhood of the endpoint (developing-map uniqueness). (c) Theorem A.5 (punctured inextendible spacetime) in the rigid (G,X) category: a candidate small target, since there the timelike-geodesic argument becomes a statement about developing maps.

## Leads for next round
- term: anchored extension; future boundary chart; future boundary ∂⁺ι(M); generalised affine length / gap-length; b-boundary; causal bubble; near-Minkowskian chart; locally uniformly timelike curves.
- cited: [4] Chruściel 2010 "Conformal boundary extensions of Lorentzian manifolds" (JDG); [19] Sbierski "On the proof of the C^0-inextendibility of Schwarzschild" (source of Prop 2.3); [21] Sbierski "On holonomy singularities in general relativity and the C^{0,1}_loc-inextendibility of space-times" (Duke 2022) — holonomy, directly relevant to conical/BTZ; [18] Sbierski "Dezornification" (the CBG proof lean-causal follows); [3] Chruściel–Grant "Lorentzian causality with continuous metrics"; [11] Grant–Kunzinger–Sämann–Steinbauer "The future is not always open"; [9] Galloway–Ling–Sbierski "Timelike completeness as an obstruction to C^0-extensions"; [15] Misner "Taub-NUT"; [22] Schmidt b-boundary; [13] Manchak (hole-freeness).
- author: P. T. Chruściel; J. B. Manchak (hole-freeness, extensions); E. Ling; C. Sämann / R. Steinbauer (low-regularity causality).
