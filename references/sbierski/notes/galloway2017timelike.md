# galloway2017timelike — Timelike completeness as an obstruction to $C^0$-extensions

Gregory J. Galloway, Eric Ling, Jan Sbierski
Communications in Mathematical Physics 2017 · doi:10.1007/s00220-017-3019-2 · arXiv:1704.00353 · `pdf/galloway2017timelike.pdf`

**Tier: T1** — peer-reviewed (CMP); its Theorem 2 is reused as the starting point of [[sbierski2017proof]] and cited in [[sbierski2023c]] as the general completeness obstruction; short, fully proved, no published critique.
**Relevance: 3** — Q1 (method: maximizers + boundary geodesic), Q2 (which steps are causal vs metric), Q4 (clean formalization target).
**Read:** full text (arXiv v4)

## Summary
The paper proves that a smooth (C^2) time-oriented Lorentzian manifold which is globally hyperbolic and timelike geodesically complete admits no extension with a merely continuous metric. The key result (Thm 2 / Thm 3.3) is that any C^0-extension of a globally hyperbolic spacetime contains a timelike geodesic of M ending on the boundary; completeness then gives a contradiction because the geodesic has finite length in near-Minkowskian coordinates. The proof uses existence of length-maximizing causal curves in globally hyperbolic C^0 spacetimes (Sämann's result, reproved here via limit curves and upper semicontinuity of length), applied in a small globally hyperbolic "diamond" V around a future-boundary point; a delicate step rules out that the M-part of the maximizer is a null geodesic, using global hyperbolicity of M (Lemma 3.4, a triangle-sweeping compactness argument). It removes the "future one-connectedness" hypothesis of [[sbierski2015c]] for the asymptotically complete regions.

## Relevance to the questions
- **(i) smooth vs causal/topological.** Metric-dependent: Lorentzian length L, the distance d, upper semicontinuity of L (Prop 2.3, via Chruściel–Grant smooth approximating wider metrics g_ε), near-Minkowskian chart with |g_μν − η_μν| < ε, cone comparison η^(2) ≺ g_ext ≺ η^(1/2), and "maximizer in M is a geodesic" (needs C^2 inside M). Purely causal/topological: Lemma 3.2 (∂⁺M ∪ ∂⁻M ≠ ∅: uses only openness of I^± in the extension and connectedness); the global-hyperbolicity of V (strong causality from a wider cone structure, compactness of diamonds by limit-curve lemma); Lemma 3.4 (a timelike diamond of the narrow cone η^(2) lies in M) — a compactness/connectedness argument once the cones are given; the remark that only compactness of causal diamonds, not strong causality, is used.
- **(ii) ETT.** ETT has I/J/K, compact diamonds, limit-curve style compactness, but no length. The theorem is intrinsically metric (completeness is a length notion), so ETT cannot state Theorem 1 as is. What ETT can state: the "locate the extension" lemma (boundary point reached by a timelike curve), and "global hyperbolicity of a cone-sandwiched diamond" — i.e. if a causality is sandwiched between two causalities whose diamonds are compact, its diamonds are compact. A length-free analogue would replace "timelike complete" by an order-theoretic completeness (e.g. every future-inextendible timelike curve is not relatively compact in any chart), which is closer to a definition than a theorem. Not about conical/BTZ lines.
- **(iii) candidate statement.** (a) `boundary_reached_by_timelike_curve`: for an open embedding ι : M → M̃ of causal spaces with ι(M) a proper open subset of connected M̃ and I^± open, there is a timelike curve in M̃ starting in ι(M) and ending on ∂ι(M) (Lemma 3.2 / sbierski2015c Lemma 2.17). (b) `diamond_compact_of_sandwich`: if causality C is contained in a causality C' (wider cones) on U and C'-diamonds are relatively compact in U, and C-diamonds are closed in V, then C restricted to V is globally hyperbolic in ETT's sense. Both are metric-free.

## Key points
- [V] Main theorem: a smooth timelike geodesically complete, globally hyperbolic spacetime is C^0-inextendible (Thm 1, §1).
- [V] Key structural theorem: a C^0-extension of a globally hyperbolic spacetime yields a timelike geodesic of M with an endpoint on ∂M (Thm 2, §1; Thm 3.3).
- [V] Uses existence of length maximizers between causally related points in globally hyperbolic C^0 spacetimes (Thm 3 = Sämann Prop 6.4; reproved as Thm 2.4).
- [P] Proof of maximizer existence: finiteness of d via covering diamond by finitely many causally convex sets each with length bound 1, limit-curve lemma (Lemma 2.2), upper semicontinuity of length (Prop 2.3) using Chruściel–Grant smooth wider metrics g_ε (§2).
- [V] Lower semicontinuity of the Lorentzian distance fails in the C^0 setting (bubbling) and is not used (remark after Thm 2.4).
- [P] Core of Thm 3.3: in a near-Minkowskian chart around p ∈ ∂⁺M, a small set V (diamond of the wide metric η^(1/2)) is globally hyperbolic for g_ext; a maximizer α from q=γ(0) to p splits into σ ⊂ M and λ; σ is a geodesic; if it were null, then L(α)=L(λ)<L(γ), contradicting maximality, for ε small (§3).
- [V] Only compactness of causal diamonds is used, not strong causality (remark after proof of Thms 1–2).
- [V] Corollary 3.5: perturbed-Minkowski (Christodoulou–Klainerman) and perturbed-de Sitter developments are C^0-inextendible.
- [V] Corollary 3.7: for future timelike complete globally hyperbolic M, ∂⁻M is an achronal topological hypersurface (via Galloway–Ling Thm 2.6).
- [V] Weak solutions of Einstein equations require metric at least continuous with Christoffel symbols locally L^2 (§1), motivating C^0 as the threshold.

## Verified quotes
> "In this paper we show that a timelike complete and globally hyperbolic Lorentzian manifold is C 0 -inextendible."

> "Theorem 1. A smooth (at least C 2 ) time-oriented Lorentzian manifold that is timelike geodesically complete and globally hyperbolic is C 0 -inextendible."

> "If (M, g) admits a C 0 -extension, then it contains a timelike geodesic that has an end point on the boundary of M ."

> "Let (M, g) be a time-oriented globally hyperbolic Lorentzian manifold with a continuous metric. Let q ∈ J + (p). Then there is a causal curve γ from p to q which has length greater than or equal to that of all other causal curves from p to q."

> "For weak solutions to the Einstein equations, one requires that the metric is at least continuous and, in some coordinate system, the Christoffel symbols are locally in L2 ."

> "In fact, lower semicontinuity does not hold in the C 0 setting."

> "Indeed, nowhere in the proof of Theorem 3.3 is strong causality used, only the compactness of ‘causal diamonds’."

> "one has to rule out the subtle possiblility that the part of this length-maximizer that is contained in M , is a null geodesic"

> "The spacetimes constructed in [5] which arise dynamically from perturbed Minkowski initial data are C 0 -inextendible."

> "Then ∂ − M is an achronal (with respect to smooth timelike curves) topological hypersurface."

> "In this paper we circumvent the property of future one-connectedness by proving that the properties of global hyperbolicity and timelike geodesic completeness also ensure the C 0 -inextendibility of the spacetime"

## Methods and evidence
- Data / setting: smooth (C^2) globally hyperbolic M inside a C^0 Lorentzian M_ext; causal curves locally Lipschitz (Chruściel / Chruściel–Grant conventions).
- Baselines: classical C^2-inextendibility from timelike geodesic completeness (Beem–Ehrlich–Easley Prop 6.16); [[sbierski2015c]] methods needing future divergence + future one-connectedness.
- Evaluation: rigorous proof; no numerics.
- Artifacts: none (pure mathematics).

## Limitations and caveats
- M itself must be C^2 (to know maximizers in M are geodesics); only the extension is C^0.
- Says nothing about extensions through incomplete regions (singularities): needs completeness; the interior of Schwarzschild still needs [[sbierski2015c]]-type arguments.
- Abstract and theorems match; no overclaim.
- Uses Chruściel–Grant smoothing of cones; relies on choice of causal curve class (Lipschitz) — causal theory of C^0 metrics is subtle (light cones may not be hypersurfaces).

## Contradictions and tensions
- [[sbierski2015c]]: that paper proves C^0-inextendibility of the Schwarzschild exterior via timelike diameter + future one-connectedness; this paper makes the one-connectedness unnecessary in the complete region. Not a contradiction, a replacement of method. Mirrored in [[sbierski2017proof]].

## Open questions
- Is there a length-free (order-theoretic) version: "globally hyperbolic + every inextendible timelike curve unbounded in some order-theoretic sense ⇒ no extension of the causal space"?
- Does the null-geodesic exclusion step have a purely causal formulation (e.g. via K^+ / push-up)?

## Leads for next round
- term: future boundary ∂⁺M; future divergence; future one-connectedness; length maximizer in C^0 spacetimes; limit curve theorem; causal diamonds compactness; "bubbling" (Chruściel–Grant); non-total imprisonment.
- cited: [17] Sämann, "Global hyperbolicity for spacetimes with continuous metrics" (Prop 6.4); [7] Chruściel–Grant, "On Lorentzian causality with continuous metrics" CQG 2012; [6] Chruściel "Elements of causality theory" arXiv:1110.6706; [13] Galloway–Ling, "Some remarks on the C^0-(in)extendibility of spacetimes" (AHP 2017; Thm 2.6 achronal boundary; Milne-like); [14] Minguzzi limit curves; [18] Sbierski 2015.
- author: Clemens Sämann; Eric Ling; Piotr Chruściel; James Grant; Ettore Minguzzi.
- cited later: Lorentzian length spaces version of timelike-completeness inextendibility (Grant–Kunzinger–Sämann; cited as [8] in sbierski2023c).
