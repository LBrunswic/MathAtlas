# hormann2015conical — Conical spacetimes and global hyperbolicity

Günther Hörmann
Novi Sad Journal of Mathematics (2015) · 2015 · arXiv:1501.00672 (v3, 21 Apr 2015) / doi:10.30755/nsjom.gf14.02 · `pdf/hormann2015conical.pdf`

**Tier: T2** — peer-reviewed (refereed, minor venue), short, proofs complete for the modest claims made; claims proportionate (the author labels §4–§5 "preliminary"). Not independently confirmed; 2 citations.
**Relevance: 3** — Q3 (sharp statement of why the cone misses the Geroch–Traschen class; Cauchy-surface property of {t=0} with the axis included), Q2/Q4 (a causal statement proved by elementary monotonicity, directly comparable with ETT's E_α).
**Read:** full text (§1–§5)

## Summary
Hörmann revisits the static conical spacetime l_α = −dt² + dr² + α²r²dφ² + dz², 0 < α < 1, written in Cartesian coordinates on all of R⁴ as an L^∞ metric g_α (axis included, measure zero). He proves (Lemma 1.1) that the non-smooth coefficients f₁, f₂ are in L^∞_loc ∩ W^{1,1}_loc but not H¹_loc, so the metric narrowly fails the Geroch–Traschen ("gt-regular") class. He then shows a non-smooth Bernal–Sánchez-type splitting: g_α = −dt² + ρ with ρ an L^∞ Riemannian metric bounded below by α²(dx²+dy²)+dz², and that {t}×R³ is met exactly once by every inextendible C¹ timelike curve (with the axis included). In the Colombeau setting the splitting (Definition 3.2) holds for all α if the mollifier is nonnegative, otherwise only for α² > c_φ. §4 gives a "generalized Cauchy hypersurface" proposition for uniformly timelike generalized curves, and §5 proves that the compact-open and C⁰ (image) topologies on spaces of causal curves are related by a proper continuous surjection.

## Key points
- [V] Model: static cosmic string with parameter 0 < α < 1 (deficit only), from Minkowski with the fixed-point set of a rotation removed (§1).
- [P] Spacetime notion used: smooth manifold with a measurable, locally bounded, a.e. non-degenerate index-1 metric, time-oriented by a continuous a.e.-timelike field (§1).
- [V] gt-regularity (after Steinbauer–Vickers): metric components in L^∞_loc ∩ H¹_loc; the conical metric "narrowly" fails it (§1).
- [P] Lemma 1.1: f₁, f₂ are homogeneous of degree 0 and smooth off the axis, so ∂f are homogeneous of degree −1 in 2 transverse dimensions: L¹_loc but |∂f|² ~ r⁻² is not integrable near the axis; f ∈ (L^∞_loc ∩ W^{1,1}_loc) \ H¹_loc (§1). [Reader inference: this is the codimension mechanism — a degree-0 jump across a codimension-2 set gives ∂g ~ 1/r, which is L² only in codimension 1.]
- [V] Vickers–Wilson's result is called global hyperbolicity "in terms of well-posedness for the wave equation" (§1) and is "still not covered" by later wave-equation theory on non-smooth spacetimes (Grant–Mayerhofer–Steinbauer 2009; Hörmann–Kunzinger–Steinbauer 2012) (§2).
- [P] L^∞ splitting (§3): ρ(v,v) ≥ α²(v₁²+v₂²) + v₃², and {t}×R³ is a Cauchy hypersurface for C¹ curves timelike a.e., by monotonicity of t along the curve (proof uses only the cone-width bound: |γ̇₁| ≤ α⁻¹|γ̇₀|). The axis is part of M = R⁴.
- [P] Colombeau splitting (§3, Def. 3.2): holds with β = α² for nonnegative mollifiers (Variant A), only for α² > c_φ = (‖φ‖_{L¹}−1)/(‖φ‖_{L¹}+1) with standard moment-condition mollifiers (Variant B), for all α with strict delta nets (Variant C).
- [V] Ellis–Schmidt are quoted: with the axis treated as a singularity (removed), "there can be no global Cauchy surfaces in these space-times" (§4).
- [P] Prop. 4.1: a generalized curve with Euclidean-unit speed and uniformly strictly negative g_α(γ̇,γ̇) meets {0}×R³ in a unique compactly supported generalized point (§4). Explicitly preliminary: generalized inextendibility and generalized causal curves are not defined.
- [P] Prop. 5.1 (smooth/continuous causality, not conical-specific): for causal curves between p and q, the map from [0,1]-parametrized (∝ arclength) curves with compact-open topology onto image-classes with the C⁰ topology is surjective, continuous and proper (§5). Proof: Arzelà–Ascoli plus local Lipschitz bounds on causal curves.
- [P] Not treated: α > 1, moving/spinning strings, null (BTZ) lines, Einstein equations, extendibility (whole text).

## Verified quotes
> "the metric of which with parameter 0 < α < 1 can be specified in cylindrical coordinates"

> "As noted in [22] the conical spacetime metric is not gt-regular, but it narrowly it fails to be so."

> "In [26] Vickers and Wilson have shown that the conical spacetime may be called globally hyperbolic in the sense of [4], namely in terms of well-posedness for the wave equation."

> "A further remarkable fact about [26] is that the well-posedness result of Vickers and Wilson for the conical spacetime is still not covered by successive theoretical development on the Cauchy problem for wave equations in non-smooth spacetimes as in [9, 15]."

> "Thus Ellis and Schmidt concluded that “there can be no global Cauchy surfaces in these space-times”."

> "More systematic and deeper attempts to investigate appropriate notions of a generalized Cauchy hypersurface for generalized spacetimes will remain a future task."

## Methods and evidence
- Setting: one explicit L^∞ metric on R⁴ and its Colombeau embedding.
- Method: homogeneous-distribution argument (Hörmander Thm 3.2.3) for Lemma 1.1; eigenvalue bound for the splitting; monotonicity of t along timelike curves; Arzelà–Ascoli for Prop 5.1.
- Evaluation: elementary, complete proofs; §4 is explicitly preliminary.
- Artifacts: n/a.

## Limitations and caveats
- Conceded: generalized inextendible/causal curves are not defined; Prop 4.1 is parametrization-dependent.
- Noticed: the L^∞ Cauchy-surface statement only quantifies over C¹ curves that are timelike a.e.; whether curves may cross the axis is not discussed explicitly — the proof works because the axis is a measure-zero subset and only the cone-width bound is used. This is in substance the causal statement ETT would prove for E_α.
- Noticed: footnote 1 — "spacelike" for a hypersurface makes no sense for L^∞ metrics; the Cauchy property is purely about curves meeting it once.
- Noticed: the PDF date line reads "April 18, 2018" while arXiv v3 is 2015 — cosmetic.

## Contradictions and tensions
- [[vickers2000generalized]]: consistent and complementary; Hörmann adds the causal/splitting half VW lack.
- Ellis–Schmidt (no global Cauchy surfaces, axis removed) vs Hörmann (Cauchy surface {t=0}, axis included): not a contradiction; the answer depends on whether the axis belongs to M. This is the same point ETT makes by keeping the singular line in the topological spacetime.
- [[geroch1987strings]]: consistent — the cone is outside the gt-regular class, by a logarithmic margin.
- [[samann2015global]] / [[chrusciel2012lorentzian]]: those require C⁰ metrics; the conical metric in Cartesian coordinates is not C⁰ at the axis (direction-dependent limits), so their GH/Cauchy theory does not cover it either [reader inference].

## Open questions
- Does the C¹-curve Cauchy property extend to the ETT class of causal curves (order-theoretic, possibly running along the axis)?
- Is there any coordinate system in which the conical metric is C⁰ across the axis? (If not, the cone is outside every C⁰ causality theory, and ETT is the natural home.)

## Relevance to the questions
- (i) Smooth vs causal: Lemma 1.1 and the Colombeau splitting are analytic (Sobolev, mollifiers). The L^∞ Cauchy-surface proof is causal: it uses only that every timelike direction satisfies |dx|_{Eucl} ≤ α⁻¹|dt|, i.e. the cones are squeezed between the narrow cone of slope α⁻¹ and t-monotonicity — the same "squeezed cones" mechanism round 1 found in Sbierski's boundary charts. Prop 5.1 is pure topology (Arzelà–Ascoli) given local Lipschitz bounds.
- (ii) ETT: ETT's E_α causality makes Hörmann's Cauchy statement a theorem without measurability caveats and without the restriction α < 1 [reader inference: E_α with excess angle still has t-monotone causal curves and uniformly bounded spatial speed]. Consistency check: Hörmann's (and VW's) "generalized hyperbolicity" and ETT's causal GH of E_α agree on the Cauchy surface {t=0}; Ellis–Schmidt's negative verdict applies only to the axis-removed space, where ETT would also lose GH [reader inference: a timelike curve running into the removed axis before t = 0 is inextendible in the punctured space and never meets {t=0}].
- (iii) Lean candidate: "In E_α × R_z (any α > 0) with the ETT causality, every inextendible causal curve meets {t = 0} exactly once; hence E_α × R is globally hyperbolic" — and its contrapositive companion "in (E_α \ Λ) × R, {t = 0} is not Cauchy" (Ellis–Schmidt). Both are small, concrete, and the pair isolates why the singular line must be in the space. Optionally: Prop 5.1 as a topology lemma on spaces of causal curves.

## Leads for next round
- term: gt-regular metric; globally hyperbolic metric splitting (generalized); generalized Cauchy hypersurface; Colombeau generalized curves
- cited: [22] Steinbauer–Vickers, "The use of generalized functions and distributions in general relativity", CQG 23 (2006) R91 (arXiv gr-qc/0603078 — open account of Geroch–Traschen); [23] Steinbauer–Vickers, "On the Geroch–Traschen class of metrics", CQG 26 (2009); [7] Ellis–Schmidt GRG 8 (1977); [9] Grant–Mayerhofer–Steinbauer CMP 285 (2009); [14] Hörmann–Sämann JMAA 420 (2014); [24],[25] Vickers on generalized cosmic strings and quasi-regular singularities
- author: Günther Hörmann, Clemens Sämann, Roland Steinbauer (Vienna)
