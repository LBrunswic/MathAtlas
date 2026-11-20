# sbierski2020holonomy — On holonomy singularities in general relativity and the C^{0,1}_loc-inextendibility of spacetimes

Jan Sbierski
Duke Math. J. 171, no. 14 (2022), 2881-2942 · 2020 · arXiv:2007.12049 / doi:10.1215/00127094-2022-0040 · `pdf/sbierski2020holonomy.pdf`

**Tier: T2** — peer-reviewed (Duke), complete proofs, claims proportionate; used as a building block and baseline by later work (Cameron–Sbierski, Luk–Sbierski, Lipschitz paper) but only by the same author's line, so not independently replicated.
**Relevance: 3** — Q1 (core method: holonomy), Q2 (all arguments live in a C^{0,1} chart of the extension), Q3 (holonomy singularities vs conical/BTZ holonomy; Geroch–Traschen weak-solution class), Q4 (causal-homotopy localisation lemma is order-topological).
**Read:** full text (§1–§4 read closely; Appendix A skimmed)

## Summary
The paper studies spacetime singularities "at the level of the connection": it proves that certain spacetimes admit no extension with a locally Lipschitz metric by exhibiting families of loops whose parallel-transport (holonomy) maps are unbounded in the Lorentz group, whereas in a C^{0,1}_loc extension chart Christoffel symbols are bounded and parallel transport along "local" curves (bounded coordinate velocity and parameter domain) is uniformly bounded (Lemma 2.13). Applied to cosmological warped products −dt²+a(t)²ḡ with particle horizons (Thm 1.1 / Cor 3.17; FLRW in particular), the loops are broken null geodesics in a totally geodesic {t,χ}-plane and the holonomies form an unbounded family of boosts. For spherically symmetric weak null singularities (Thm 1.2 / 4.1 / 4.3) the loops are mixed angular-and-null and the blow-up of ∂_v r drives the holonomy. Applications: Reissner–Nordström–Vaidya (§4.2) and the Dafermos–Luk–Oh spacetimes, upgrading Luk–Oh's C²-strong cosmic censorship to a C^{0,1}_loc formulation (Thm 4.30, 4.31). Locality of the loops inside the extension chart is obtained from a causal-homotopy argument (Lemma 2.12).

## Key points
- [V] Main object: holonomy of the Levi-Civita connection used as an inextendibility obstruction; the paper "widens the geometric investigation of gravitational singularities to the level of the connection" (§1.3).
- [V] Weak null singularities do admit C^0 extensions; the obstruction is genuinely at connection level (§1, after Thm 1.2).
- [P] Thm 1.1: for g = −dt² + a(t)²ḡ on (0,∞)×M̄ with (M̄,ḡ) a complete Riemannian 3-manifold, a→0 at t→0, ∫₀¹ dt/a < ∞ (particle horizon) and ∫₁^∞ a/√(a²+1) dt = ∞ (future timelike completeness), (M,g) is C^{0,1}_loc-inextendible (§1, Thm 1.1; Cor 3.17; footnote 9 says it works in any dimension d ≥ 1).
- [V] Mechanism in the cosmological case: holonomies of a family of broken-null loops "form an unbounded family of boosts" (§1.3).
- [P] Thm 1.2/4.1/4.3: in double-null spherical symmetry with Ω, r continuous up to the boundary, ∂_v r → −∞ (and ∂_u r → −∞) and sign conditions, (M,g) is future C^{0,1}_loc-inextendible; no mass-inflation assumption (§4.1, Remark 4.2).
- [V] Hawking-mass blow-up is not needed (Remark 4.2.1).
- [P] Thm 4.30/4.31: generic small spherically symmetric perturbations of two-ended subextremal RN (Einstein–Maxwell–scalar field, Luk–Oh class) have C^{0,1}_loc-inextendible future developments — C^{0,1}_loc strong cosmic censorship in this class (§4.3, Appendix A for exterior timelike geodesic completeness).
- [V] Lemma 2.13 (key analytic input): parallel transport bounded by e^{C·T} with C depending on the curve only through a bound on its coordinate velocity; all that is needed is a uniform bound on the Euclidean norm of the tangent and the parameter domain (§2.3).
- [V] Lemma 2.12 (causal homotopy localisation) is used "to obtain topological information from Lorentzian causality": a causal homotopy with fixed endpoints of a curve in Ũ stays in Ũ if J⁺(γ̃(0),Ũ)∩J⁻(γ̃(1),Ũ) is compactly contained in Ũ (§2.2). Its proof is a pure connectedness/compactness argument.
- [P] Defines the "local causal holonomy" l.c.Hol(γ,s₀) ⊂ O(1,3): holonomies of loops γ|[s₀,s₁] followed by a causal homotopy back; non-compact closure for geodesics into Schwarzschild r=0 or (time-reversed) a big bang with particle horizons (§1.3).
- [V] No general definition of "holonomy singularity" is attempted (§1.3, end).
- [V] Schwarzschild r=0 is also a holonomy singularity (Remark 3.16), though C^0-inextendibility there is already known and strictly stronger.
- [V] Footnote 4: impulsive gravitational waves have delta-curvature but bounded Christoffel symbols — curvature blow-up need not imply connection blow-up.
- [P] Motivation (§1.1): the class g ∈ C^0, ∂g ∈ L²_loc (Geroch–Traschen [16]) is taken as the roughest class admitting weak solutions of Einstein's equations with good stability; C^{0,1}_loc results are "only one step" toward it.
- [V] Footnote 1 flags that the PDE-natural weakening g, g⁻¹ ∈ L^∞_loc "poses challenges for the physical interpretation and Lorentzian causality theory alike".
- [P] Conical singularities, cosmic strings, BTZ lines and flat spacetimes with nontrivial holonomy around a singular line are not mentioned anywhere; the only holonomies studied are unbounded families of boosts near curvature singularities (whole text searched for "conic", "string", "BTZ", "flat").

## Verified quotes
> "This paper widens the geometric investigation of gravitational singularities to the level of the connection."

> "We show how local holonomy transformations can be used to infer its blow-up."

> "Note that the spherically symmetric weak null singularities do admit future C 0 -extensions!"

> "One can now show that the holonomy transformations at the base point γ(−µ) associated with this family of loops form an unbounded family of boosts."

> "Note that the theorem does not require the Hawking mass to go to infinity for v → 0."

> "Note that all that is needed to do so is a uniform bound on the Euclidean norm of the tangent vector and the domain of definition of the curve."

> "The next lemma will be used in our later applications to obtain topological information from Lorentzian causality."

> "Let us conclude the introduction by remarking that we do not attempt in this paper to define precisely what we mean by a holonomy singularity in general, since we expect that they can come in various forms still to be explored."

> "We remark that the Schwarzschild singularity is also a holonomy singularity"

> "A simple illustration is provided by the well-known exact impulsive gravitational wave spacetimes [32] where curvature has a delta singularity across a hypersurface but the Christoffel symbols are uniformly bounded."

> "it clearly poses challenges for the physical interpretation and Lorentzian causality theory alike."

> "Note that all these definitions are independent of a distance function on M but only depend on the smooth structure."

> "Let (M , g) be a 3-dimensional complete Riemannian manifold"

## Methods and evidence
- Data / setting: smooth time-oriented Lorentzian manifolds; extensions ι: M ↪ M̃ into a smooth manifold with C^{0,1}_loc metric (Def 2.1). Remark 2.2: lowering the differentiable structure to C¹ gains nothing.
- Baselines: prior C^0-inextendibility results (Sbierski 2018 Schwarzschild; Galloway–Ling–Sbierski timelike completeness; Galloway–Ling Milne-like; Chruściel–Klinger).
- Evaluation: rigorous proofs by contradiction; explicit examples (FLRW, RNV, DLO).
- Artifacts: n/a (pure mathematics).

## Limitations and caveats
- Regularity threshold is C^{0,1}_loc, short of the conjectured C^0 ∩ W^{1,2}_loc class; author concedes this is "one step".
- Spherical symmetry needed for weak null singularities (removed later in [[sbierski2024lipschitz]], by a different method).
- Inextendibility is relative to extensions into smooth manifolds with Lorentzian metric of the given regularity; spacetimes with singular strata (cones, orbifold/BTZ lines) are not in the category at all — neither as M nor as M̃.
- The "holonomy singularity" notion is deliberately left undefined; only unbounded holonomy is used, never a fixed nontrivial holonomy around a codimension-2 defect.
- Abstract matches the theorems (no overreach found).

## Contradictions and tensions
- [[sbierski2024lipschitz]] states the holonomy method extends outside symmetry only with additional pointwise blow-up bounds on χ, and replaces it with an integrated curvature + Stokes argument — complementary, not contradictory.
- [[cameron2026spherically]] strengthens §4's spherically symmetric result to C^0 ∩ W^{1,s}_loc, s>1, but only in the strongly spherically symmetric extension category.

## Open questions
- Reviewer inference (not in the paper): Lemma 2.13 implies that, in any C^{0,1}_loc (indeed bounded-Christoffel) chart, holonomy of loops with coordinate length → 0 tends to the identity. A flat spacetime with a conical singular line of angle α ≠ 2π has holonomy around every small loop encircling the line equal to a fixed nontrivial rotation by 2π−α (BTZ line: a fixed parabolic element). If such loops could be made "local" in an extension chart (Lemma 2.12-type causal argument), this would show conical/BTZ lines are C^{0,1}_loc-inextendible as smooth Lorentzian manifolds — a "bounded but nontrivial" holonomy singularity distinct from Sbierski's "unbounded" type. Needs checking: whether a C^0 extension can have the line in its boundary with small loops shrinking in the chart (the loops are spacelike and not causally homotopic to timelike curves, so Lemma 2.12 does not directly apply).
- Are flat cone spacetimes even C^0-extendible across the singular line? Geroch–Traschen [16] is the natural source (cosmic strings are outside their class); not settled here.

## Relevance to the questions
- (i) Smooth vs causal: the holonomy estimate (Lemma 2.13), the definition of extension (Def 2.1) and the existence of geodesics leaving M (Prop 2.6, 2.11) require a smooth manifold with C^0/C^{0,1} metric and charts. Purely causal/order-topological pieces: Lemma 2.12 (continuity/compactness argument on causal homotopies using only J±(·,Ũ) and compact containment), the future/past boundary decomposition (Lemma 2.5), the achronal-graph structure of ∂⁺ι(M) in a boundary chart (Prop 2.6 iii), and the use of Cauchy surfaces / global hyperbolicity.
- (ii) ETT: "extension" and "future boundary" can be phrased for topological spacetimes with a causality (an open causal embedding with nonempty topological boundary, ∂⁺ via future inextendible causal curves with limit points). Holonomy needs a (G,X)-structure — exactly what ETT's singular flat spacetimes have: the regular part reg(E_α) is an (Isom(E),E)-manifold and the holonomy around the singular line is the cone-angle rotation (E_α) or the parabolic element (E_0). Sbierski's notion is unbounded holonomy at a curvature singularity; ETT's is fixed nontrivial holonomy at a codimension-2 flat defect. These are different singularity types; ETT examples are neither examples nor counterexamples to his theorems (his hypotheses — warped FLRW with a→0, or spherically symmetric weak null singularity — fail for flat cone spacetimes), but they are natural test cases for any general definition of "holonomy singularity" he leaves open.
- (iii) Lean candidate: Lemma 2.12 restated for a causality in the ETT sense — "if K := J⁺_U(x) ∩ J⁻_U(y) is compactly contained in U and H : [0,1]×[0,1] → M is a homotopy through future causal curves from x to y starting with a curve in U, then H lands in U" — provable by the same connectedness/compactness argument from ETT's causal-curve definitions. Second candidate (research): "a singular flat E_α-line, α ≠ 2π, admits no extension in which the regular part embeds with locally bounded connection" via holonomy of short loops.

## Leads for next round
- term: holonomy singularity; local causal holonomy; future boundary chart; causal homotopy; C^{0,1}_loc strong cosmic censorship; weak null singularity; particle horizon
- cited: [16] Geroch & Traschen, "Strings and other distributional sources in general relativity" (PRD 1987) — the cosmic-string / weak-solution class link to conical singularities; [15] Garfinkle, "Metrics with distributional curvature" (CQG 1999); [37] Sbierski, C^0-inextendibility of Schwarzschild (JDG 2018); [14] Galloway–Ling–Sbierski (CMP 2018); [13] Galloway–Ling (AHP 2017); [4] Chruściel–Grant, causality with continuous metrics; [19] Grant–Kunzinger–Sämann–Steinbauer "The future is not always open"; [18] Grant–Kunzinger–Sämann, inextendibility in Lorentzian length spaces; [32] Penrose impulsive waves
- author: Eric Ling, Greg Galloway, Clemens Sämann (synthetic/low-regularity inextendibility), Jonathan Luk, Sung-Jin Oh
