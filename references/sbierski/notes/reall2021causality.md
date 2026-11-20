# reall2021causality — Causality in gravitational theories with second order equations of motion

Harvey S. Reall
Phys. Rev. D 103 (2021) 084027 · arXiv:2101.11623, doi:10.1103/physrevd.103.084027 · `pdf/reall2021causality.pdf`

**Tier: T2** — peer-reviewed (PRD), the algebraic results are proved in full and widely cited (63). Some statements are explicitly heuristic ("I will argue"; genericity of triple points; the domain of dependence is cited to Reula, not proved). Nothing in it is independently reproduced in this KB.
**Relevance: 2** — Q2: it is the motivating case for "several cones on one spacetime" (the round-1 two-cone mechanism of [[eperon2018predictability]]). It is not about Sbierski, and it says nothing on MGHDs.
**Read:** full text (v2, 36 pp.), with the algebra of §§2–3 skimmed.

## Summary
Reall studies diffeomorphism-invariant theories of gravity coupled to matter with second-order equations of motion: Lovelock, Horndeski, and the leading parity-symmetric 4-derivative EFT corrections of Einstein–scalar and Einstein–Maxwell theory. He works gauge-invariantly with the principal symbol acting on physical polarisations. In d=4 Horndeski theories the characteristic polynomial is the product of a quadratic factor (the null cone of an "effective metric" C_μν, purely gravitational) and a quartic Q. At weak coupling Q splits into an inner and an outer cone that straddle the C-cone. The Gårding cone, the component of {p≠0} inside the inner quartic sheet, is convex. Its dual C_p^± in the tangent space is declared to be the causal cone of the theory, and capitalised "Causal/Timelike" curves, J^±, I^± and the black-hole region are defined from it. Further results: Killing horizons are characteristic with a special "triple direction" (no conical refraction inside the horizon), the zeroth law holds at weak coupling, and §4.8 argues that the difference between the 4-derivative and 2-derivative cones is not observable within EFT.

## Key points
- [V] Causality is governed by a degree-6 characteristic polynomial that factorises as (quadratic in C^{-1}) × (quartic Q) (Abstract; §1, eq. (4); §4).
- [V] At weak coupling the slowness surface has three sheets: the quadratic ellipsoid lies between the two sheets of the quartic (§1; §4.3).
- [P] The quartic cone is an "inner" cone inside (or on) the C^{-1} null cone and an "outer" cone outside it. The characteristic cone is the union of three double cones, all close to the null cone of g at weak coupling (§4.3, pp. 21–22).
- [V] The causal cone C_p^± is the dual of the Gårding cone. It is closed and convex, and in the general theory causality is determined by C_p^±, not by the metric null cone (§4.6, eq. (107)).
- [P] With no triple directions, ∂C_p^± is the set of tangents to bicharacteristics of the innermost cotangent sheet, i.e. the outermost ("fastest") sheet of the three-sheeted wave cone W_p. At a triple direction C_p^± is the convex hull of W_p^± (§4.6, eqs. (108)–(109), footnote 11).
- [V] In a factorised theory with concentric cones, the causal cone is the cone of the effective metric whose null cone is outermost. When the two cones cross, it is the convex hull of their union (§4.6).
- [P] Reader inference: because the Gårding cone lies inside the inner quartic sheet, which lies inside the C^{-1} null cone, duality gives C-causal ⊆ C_p. The theory's causality therefore always contains the effective-metric causality: a nested pair on one manifold. Reall makes **no** nesting claim between C_p and the null cone of the physical metric g. He only says that both are close at weak coupling. Footnote 5 notes that in factorised theories C is conformal to g (§4.3–4.6).
- [V] A bicharacteristic crossing from the inner to the outer quartic sheet at a triple point can be continued by gluing, and the resulting fastest curve is non-smooth (§4.5).
- [V] Causal and timelike curves are defined as **smooth** curves with tangents in C_p^± (respectively its interior). J^±, I^± and B = M \ J^-(I^+) are defined from them (§4.7).
- [P] The domain of dependence is described as the region inside the ingoing fastest characteristic surfaces, citing Reula [26] for "results in this direction". It is not proved here (§4.5).
- [V] Speculation (§5): the Kovács–Reall well-posed formulation might extend to strong coupling if its auxiliary metrics have null cones strictly outside the characteristic cone. That would be a nested chain of cones (§5).
- [V] Within EFT validity, geometric optics cannot tell the 4-derivative cone from the 2-derivative one. The cone is proposed as a technical tool for extending GR theorems instead (§4.8).
- [P] Predictability, global uniqueness and maximal developments are **not** discussed. Well-posedness is quoted from Kovács–Reall [6, 8] at weak coupling only (§1, §4.3, §5).

## Verified quotes
> "This dual cone governs causality in these theories, i.e., it provides the appropriate generalisation of the usual “light cone” of GR."

> "In a more general theory, causal properties of the theory are not determined by the null cone of the metric but instead by the cones"

> "Inside the inner cone and outside the outer cone we have"

> "with the quadratic surface lying between (or on) the sheets of the quartic surface"

> "is simply the causal cone of the effective metric with the outermost null cone. However, if the cones of the two effective metrics have a non-trivial intersection then"

> "The resulting curve will be non-smooth at the point where the curves are glued."

> "We say that a smooth curve is future-directed Causal (Timelike) iff its tangent vector is everywhere future-directed Causal (Timelike)."

> "the region of spacetime where the solution is uniquely determined by initial data on"

> "of this formulation are chosen so that their null cones lie strictly outside the characteristic cone"

> "Hence, within the regime of validity of EFT, geometric optics cannot distinguish between the characteristic cone of the 4-derivative theory and that of the"

> "This paper uses standard notions of causality from PDE theory."

## Methods and evidence
- Data / setting: smooth backgrounds, d=4 Horndeski (one scalar), with general results on the symmetries of the principal symbol in any d. Weak coupling is assumed for the cone structure.
- Baselines: GR (2-derivative) null cone; crystal optics (Fresnel surface) and anisotropic elasticity as analogies.
- Evaluation: algebraic proofs (principal-symbol symmetries, factorisation, Killing-horizon proposition). Genericity of triple points is argued, not proved.
- Artifacts: none.

## Limitations and caveats
- Causal curves are smooth by definition, yet the paper itself exhibits glued, non-smooth fastest curves (§4.5). The definition does not match the phenomenon. A Lipschitz or order-theoretic curve notion is what is needed.
- At triple points the cone field is a convex hull of non-smooth pieces. Regularity of the field p ↦ C_p is never discussed, and it depends on up to second derivatives of the background.
- All structure is established only at weak coupling. Away from it, C may be non-invertible and hyperbolicity may fail (§5).
- The domain-of-dependence claim is cited, not proved. There is no Cauchy-development or MGHD statement.
- The abstract does not overstate the theorems.

## Contradictions and tensions
- Confirms and refines [[eperon2018predictability]]: the round-1 reading "sub/superluminality = inclusion between two causal orders" applies here to the pair (effective-metric cone C) ⊆ (theory cone C_p), which is nested at weak coupling. It is **weaker** for the pair (g-cone, C_p): Reall gives no inclusion, the cones are only "close". So the ERS sub/superluminal dichotomy relative to the physical metric g can fail to be a clean nesting in generic Horndeski backgrounds. Some directions may be faster and others slower; that is plausible, but it is a reader inference, not in the text.
- Consistent with [[minguzzi2019causality]]: the theory's causality is a single closed convex cone per point (the convex hull of the fastest sheet), which is exactly a closed cone structure. Minguzzi's framework, and [[bernard2018lyapounov]]'s, then applies to C_p directly.
- Consistent with [[chrusciel2012lorentzian]] and [[abbrescia2025quasilinear]]: the low-regularity, non-smooth causal curves needed here are the regime where push-up and smooth-curve definitions break.

## Open questions
- Is C_p^± ⊇ (g-cone) or ⊆ (g-cone) for some class of Horndeski or EGB backgrounds, as needed for an ERS-type uniqueness statement relative to g? The text does not say.
- Is p ↦ C_p upper semicontinuous at triple points? If so, it is a closed cone field in the sense of Bernard–Suhr.
- Does an MGHD exist, and is it unique, for weakly coupled Horndeski with respect to J_{C_p}? Given ERS19, superluminality of C_p relative to the gauge cones (g̃, ĝ) may be the relevant one.

## Relevance to the questions
**(i) Smooth vs causal.** Everything that **defines** C_p is smooth PDE theory: the principal symbol, Gårding cones of hyperbolic polynomials, bicharacteristics and duality in T_pM. It needs a C^2 background. Once C_p is given, every use of it in the paper is purely order-theoretic: J^±, I^± from curves, the black-hole region M \ J^-(I^+), the event horizon as a boundary, and "domain of dependence = region uniquely determined by data". The paper's own non-smooth glued bicharacteristics show that the curve class has to be relaxed.

**(ii) What ETT could state or generalise.** The structure is precisely "several causalities on one topological space": J_C ⊆ J_{C_p} ⊆ J_{ĝ} (with the gauge metrics of §5). ETT's causality, a family of preorders, can carry each of these as a separate causality on the same space. The ERS19 lemmas of round 1 (two developments agree on every connected component of their overlap where they agree somewhere; uniqueness under superluminality) then apply to the pair (C, C_p), or (C_p, gauge cones), **not** to (g, C_p) without an extra nesting hypothesis. ETT's order-theoretic causal curves fix the mismatch between smooth Causal curves and the glued, non-smooth fastest curves. Conical and BTZ lines play no role here.

**(iii) Formalization candidate.** Abstract "nested causalities" record: a topological space with causalities K₁ ≤ K₂ (pointwise inclusion of the preorders on every open set), with lemmas that (a) K₂-global hyperbolicity implies K₁-global hyperbolicity, given that K₁-causal curves are K₂-causal, and (b) D_{K₂}(S) ⊆ D_{K₁}(S) for Cauchy domains. These are the order-theoretic shadows of "faster cone ⇒ smaller domain of dependence", and they are the plumbing that the ERS19 Lemmas 4.70/4.72 (round-1 Q4 item 3) need. For each, the hypothesis must state which pair is nested.

## Leads for next round
- term: Gårding cone; hyperbolic polynomial; wave cone; slowness surface; triple direction; conical refraction; regularly hyperbolic (Christodoulou); weak coupling.
- cited: [6] Kovács–Reall, well-posed formulation of scalar-tensor EFT; [8] Kovács–Reall, well-posed formulation of Lovelock and Horndeski (the auxiliary metrics g̃, ĝ); [15] Reall–Tanahashi–Way, causality and hyperbolicity of Lovelock; [16] shock formation in Lovelock; [26] Reula, strongly hyperbolic systems (domain of dependence); [29] Christodoulou, *The Action Principle and PDE* (causal cone of regularly hyperbolic systems); [28] Atiyah–Bott–Gårding, lacunas; [36] the detailed EFT-causality account.
- author: Aron Kovács; Harvey Reall; Gustavo Papallo.
