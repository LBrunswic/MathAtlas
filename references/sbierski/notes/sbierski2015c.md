# sbierski2015c — The $C^0$-inextendibility of the Schwarzschild spacetime and the spacelike diameter in Lorentzian Geometry

Jan Sbierski
arXiv 2015 (v2 Apr 2016); published J. Diff. Geom. 108, 2 (2018), 319–378 per reference [13] of [[sbierski2023c]] · arXiv:1507.00601 · `pdf/sbierski2015c.pdf`

**Tier: T1** — founding paper of the C^0-inextendibility programme: published in JDG (KB record says arXiv; venue taken from the reference list of [[sbierski2023c]]), and its methods are reused and extended by [[galloway2017timelike]], [[sbierski2017proof]], [[sbierski2023c]] and Galloway–Ling; fully proved.
**Relevance: 3** — Q1 (founding methods), Q2 (which steps are causal), Q4 (Prop 2.6, Lemma 2.17, timelike separation, Theorem 5.3).
**Read:** full text for §§1–3, 5 and main statements of §§4, 6; proofs of §6 skimmed.

## Summary
First proof that a Lorentzian manifold is inextendible with a merely continuous metric: Minkowski (Thm 3.1, warm-up) and the (d+1)-dimensional maximal analytic Schwarzschild spacetime, d ≥ 3 (Thm 4.9). The scheme: (1) Lemma 2.17 — any C^0 extension has a timelike curve leaving M ("locating the extension"); (2) a near-Minkowskian chart around the exit point (Lemma 2.4), in which timelike futures are sandwiched between Euclidean cones; (3) identify diamonds in the chart with diamonds in M, which needs future one-connectedness (timelike homotopies with fixed endpoints cannot escape a precompact chart diamond); (4) a geometric quantity bounded in the chart but infinite in M gives the contradiction — the timelike diameter (exterior/Minkowski: d(λ(0),λ(s)) → ∞, "future divergence") and the newly introduced spacelike diameter diam_s(N) = sup over Cauchy hypersurfaces of their intrinsic diameter (interior, near r=0). Theorem 5.3: a globally hyperbolic C^0 spacetime covered by finitely many "regular flow charts" has finite spacelike diameter.

## Relevance to the questions
- **(i) smooth vs causal/topological.** Causal/topological given openness of I^±: Prop 2.6 (I^±(p) open for C^0 metrics, with piecewise-smooth timelike curves) is the one causality input; Prop 2.7 (I⁻(γ(1)) = ∪_{s<1} I⁻(γ(s))); Lemma 2.17 (a timelike curve leaves M — uses only connectedness of M̃, openness of ι(M) and of I^±); Def 2.13 future one-connectedness (timelike homotopy — topological once "timelike curve" is given); Def 2.14 timelike separation and its reformulation via I^±(A, M∖K); the homotopy-confinement step (open–closed argument on the homotopy parameter). Metric: Lemma 2.4 near-Minkowskian chart; cone sandwich C⁺_{5/6} ⊂ I⁺ ⊂ C⁺_{5/8}; the timelike diameter (length); the spacelike diameter (induced Riemannian metric on Cauchy surfaces); regular flow charts (bounds |g_µν| ≤ C, g_00 ≤ c < 0); Schwarzschild computations. Smooth-structure note: the paper assumes manifolds smooth, conceding C^1 structure suffices.
- **(ii) ETT.** ETT's causality-on-open-sets framework matches the paper's explicit insistence (Remark 2.3) that I⁺(p,U) is computed in U, not in M — exactly ETT's "family of preorders on open sets". Future one-connectedness and timelike separation are statable in ETT. Both diameters are metric and not statable; a metric-free surrogate of the timelike diameter is "the diamonds I⁺(γ(s0))∩I⁻(γ(s)) are not eventually contained in a compact/chart" — but the paper's point is precisely that a quantitative invariant is needed because diamonds of M and of the chart are not a priori identified. The singularities here are curvature singularities (spacelike r=0), not conical/BTZ lines; for E_α lines the analogous obstruction is local holonomy, treated by Sbierski in later C^{0,1}_loc work (lead).
- **(iii) candidate statement.** (a) `exists_timelike_curve_leaving` (Lemma 2.17): for a connected causal space M̃ with open I^± and a proper open subset ι(M) with ∂ι(M) ≠ ∅, there is a timelike curve γ: [0,1] → M̃ with γ([0,1)) ⊆ ι(M) and γ(1) ∉ ι(M). (b) `diamond_identification_of_one_connected`: if M is future one-connected and the chart diamond D = I⁺(γ̃(s0),Ũ) ∩ I⁻(γ̃(0),Ũ) has closure in Ũ, then ι(I⁺(γ(s0),M) ∩ I⁻(γ(s),M)) ⊆ D-type sets (the "⊇" of (1.2)). (c) `minkowski_C0_inextendible` is too metric-heavy for ETT but the causal skeleton (a)+(b) is formalizable.

## Key points
- [V] Main theorem: (d+1)-dimensional maximal analytic Schwarzschild is C^0-inextendible for all d ≥ 3 (§1; Thm 4.9).
- [V] Minkowski spacetime is C^0-inextendible for every d ≥ 1 (Thm 3.1).
- [V] Claimed first C^0-inextendibility result: author unaware of any previous one (§1.1).
- [V] Only causality fact needed for continuous metrics: I^±(p) open (Prop 2.6; §2.1).
- [V] Smoothing preserves timelike but not causal curves: a continuous 1+1 metric may admit no smooth null curve (Remark 2.3).
- [V] Lemma 2.17: any C^k-extension has a timelike curve leaving ι(M) — "locates" the extension.
- [V] Spacelike diameter defined as sup over Cauchy hypersurfaces of their intrinsic diameter (Def 5.1); shortest spacelike curves do not work (zig-zag near-null paths) (§5).
- [V] Thm 5.3: finitely many regular flow charts covering N ⇒ diam_s(N) < ∞.
- [P] Thm 5.7: if N is open, globally hyperbolic and precompact in a C^0 spacetime M (with a ball Cauchy surface), then diam_s(N) < ∞ (§5).
- [P] Exterior obstruction: future one-connectedness (Prop 4.12) + infinite timelike diameter of diamonds along a curve to infinity (§4.3); interior obstruction: spacelike diameter of a spherically symmetric region near r=0 is infinite, contradicting Thm 5.3 via rotated regular flow charts (§6).
- [V] Example g = e^{2√t}(−dt² + dx²) on (0,∞)×R is C^0-extendible but C^2-inextendible (§1.1).
- [V] Open question: are there timelike geodesically complete Lorentzian manifolds that are C^0-extendible? (§1.3 iv) — answered negatively for globally hyperbolic ones by [[galloway2017timelike]].
- [V] Proposes FRW/big-bang C^0-inextendibility as a direction needing new techniques (§1.3 ii) — taken up in [[sbierski2023c]].

## Verified quotes
> "The (d + 1)-dimensional maximal analytic Schwarzschild spacetime is C 0 -inextendible for all d ≥ 3."

> "For every d ≥ 1, the (d+1)-dimensional Minkowski spacetime (MMink , m) is C 0 -inextendible."

> "we are not aware, however, of any previous results showing C 0 -inextendibility of a Lorentzian manifold."

> "In this paper, however, the only result in causality theory for merely continuous metrics we need is that the timelike future and past remains an open set."

> "It is an easy exercise to write down a merely continuous Lorentzian metric in 1 + 1 dimensions, which does not admit a single smooth null curve."

> "In particular, the lemma entails that if no timelike curve can leave M , then M must be inextendible."

> "an attempt to capture the notion of a spacelike diameter in direct analogy to the Riemannian case, i.e., by considering shortest spacelike curves, clearly fails, since one can connect any two points by a spacelike curve of arbitrarily short length by using a nearly null zig-zag path."

> "be a finite collection of regular flow charts for N with"

> "Then one has diams (N ) < ∞."

> "An interesting question is whether there are examples of (timelike) geodesically complete Lorentzian manifolds which are C 0 -extendible."

> "Here, new techniques are needed."

> "Hence, there might be a point q ∈ U which can be connected to p via a past directed timelike curve lying in M , which, however, cannot be connected to p via a past directed timelike curve lying entirely in U ."

> "However, since on the left we consider a causality relation with respect to a small neighbourhood of M̃ , and on the right with respect to Mmax , such an identification is not justified in general (and indeed, neither of the two inclusions is)!"

> "Clearly, this Lorentzian manifold can be continuously extended to [0, ∞) × R."

## Methods and evidence
- Data / setting: smooth M, C^0 extension M̃ (manifold assumed smooth for convenience, C^1 suffices); timelike curves piecewise smooth.
- Baselines: classical C^2-inextendibility via geodesic completeness / curvature blow-up; Christodoulou's spherically symmetric C^0 results; Dafermos–Luk C^0 stability of Kerr Cauchy horizon (motivation).
- Evaluation: rigorous proofs.
- Artifacts: none.

## Limitations and caveats
- Requires future one-connectedness (exterior and interior), which the author calls tedious to establish; later removed for complete regions by [[galloway2017timelike]].
- Interior argument relies on spherical symmetry to rotate regular flow charts; simplified in [[sbierski2017proof]].
- d ≥ 3 for Schwarzschild.
- Schwarzschild singularity not generic; author concedes it is an illustrative model.
- KB metadata lists venue as arXiv; publication in JDG 108 (2018) is known here from the reference list of [[sbierski2023c]] ([S] for venue).

## Contradictions and tensions
- [[galloway2017timelike]] replaces the exterior argument (timelike diameter + one-connectedness) by maximizers; [[sbierski2017proof]] replaces the global spacelike-diameter argument by a local single-chart one. Both are refinements, not contradictions.
- Open question §1.3 (iv) is answered (for globally hyperbolic M) by [[galloway2017timelike]].

## Open questions
- Spacelike diameter as an invariant: is there a synthetic (Lorentzian length space / metric-free) analogue?
- Kasner with negative p_i suggested amenable (§1.3 ii) — done later?
- C^0-inextendibility of Christodoulou's generic collapse spacetimes without symmetry (§1.3 iii).

## Leads for next round
- term: spacelike diameter; timelike diameter; regular flow chart; future divergence; future one-connectedness; timelike separation; Ori's C^0-extendible strong curvature singularity.
- cited: [6] Chruściel–Grant (light cones of continuous metrics not hypersurfaces); [18] Ori (strong curvature singularity with C^0 extension); [10] Hawking–Ellis local extension; [1] Beem on local extendibility; [7],[8] Dafermos (Einstein–Maxwell–scalar field); [9] Dafermos–Luk (Kerr Cauchy horizon C^0 stability); [12],[16] low-regularity local existence (Klainerman–Rodnianski–Szeftel L^2 curvature).
- author: Dafermos, Luk, Christodoulou, Ori.
