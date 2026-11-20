# bernard2018lyapounov — Lyapounov Functions of Closed Cone Fields: From Conley Theory to Time Functions

Patrick Bernard, Stefan Suhr
Commun. Math. Phys. (2018) · arXiv:1512.08410 (v3), doi:10.1007/s00220-018-3127-7 · `pdf/bernard2018lyapounov.pdf`

**Tier: T1** — peer-reviewed (CMP). Complete proofs. Several results were recovered independently by Minguzzi "using more traditional constructions" (stated in the paper; consistent with [[minguzzi2019causality]], which cites Bernard–Suhr). Well cited (80).
**Relevance: 2** — Q2 and Q4. It is the cone-field route to time functions and Cauchy time functions, the comparator for ETT's Levin route. It does not treat Sbierski, CBG or singular lines.
**Read:** full text. §§1, 5.2, 5.4 and 6 in detail; §§2–4 (Clarke differentials, limit curves, de Rham smoothing of trapping domains) skimmed.

## Summary
On a manifold with a complete Riemannian metric, the paper studies **closed cone fields**: subsets of TM, closed together with the zero section, that are fibrewise convex cones and may be regular, singular (C(x) = T_xM) or degenerate (empty). This covers continuous vector fields, differential inclusions, and C⁰ Lorentzian metrics. Relaxed orbits come from cone **enlargements**: open cone fields wider than C. The stable future F_C^+(x) is {x} together with the intersection of I_E^+(x) over all open enlargements E.
- Thm 1: F_C^+(x) is exactly the set where every smooth Lyapounov function is ≥ τ(x), and stable recurrence is exactly criticality of all Lyapounov functions.
- Thm 2: one smooth Lyapounov function is regular off the stably recurrent set and separates stable classes, a Conley-type result.
- Thm 3: C is hyperbolic (causal, no singular points, J_C(K,K') compact) iff it has a smooth Lyapounov function steep with respect to a complete Riemannian metric. Then J_C = F_C, and the function is a Cauchy temporal function. A smooth splitting M ≅ R × N follows (Cor 1.8).

## Key points
- [V] Setting: closed (equivalently semi-continuous) cone fields with singularities, more general than Fathi–Siconolfi's continuous cone fields (Abstract; §1).
- [V] The relaxation by enlargements avoids an auxiliary metric and the non-continuity of length (p. 2).
- [V] A manifold structure is imposed, and the Lyapounov or time functions are **smooth** (p. 3).
- [P] Definitions: E-timelike curves are piecewise smooth with tangents in an open cone field. C-causal curves are locally Lipschitz with γ̇ ∈ C a.e. (Def 1.3). A Lyapounov function is smooth, with dτ·v ≥ 0 on C and > 0 at its regular points (Def 1.4).
- [V] Thm 1 (a) and (b): F_C^+ is represented by smooth Lyapounov functions, and stable recurrence equals vanishing of all their differentials (§1, Thm 1; proved in §5.2).
- [P] Thm 2: a single Lyapounov function is regular on D(C) − R_C, constant exactly on stable classes, and strictly increasing from x to x' when x' ∈ F^+(x) and x ∉ F^+(x') (§1; proof in §5.2 by a C^∞-convergent weighted sum over a dense sequence).
- [V] So stable causality, meaning no stably recurrent point, is equivalent to the existence of a smooth temporal function, generalising Fathi–Siconolfi (§1, after Thm 2).
- [P] Prop 1.5: x is stably recurrent iff x is singular or F^+(x) ∩ F^-(x) ∋ y ≠ x. The proof is a finite-intersection compactness argument on a boundary sphere (§1).
- [V] Hyperbolicity is (GH1) causal with no singular points plus (GH2) compact J_C(K,K'). Neither stable nor strong causality is assumed (§1.1).
- [V] Thm 3: hyperbolic ⇔ there is a smooth Lyapounov function steep w.r.t. a complete Riemannian metric; then J_C = F_C (§1.1; proof §5.4).
- [P] Lemma 5.11: (GH2) implies that J_C^±(x) is closed, the analogue of causal simplicity. Cor 5.14: on hyperbolic fields, F_{C_K}(K₁,K₂) = J_C(K₁,K₂), by a limit-curve argument (§5.4).
- [V] Cor 1.7: every hyperbolic cone field has a hyperbolic enlargement, so global hyperbolicity is stable (§1.1).
- [P] Cor 1.8: a globally hyperbolic closed cone field gives a smooth splitting M ≅ R × N, built from the flow of ∇τ/|∇τ|² (§1.1).
- [V] Hyperbolicity with (GH3), compactness of J(x,y) only, is not enough without non-empty interior (counterexample: recurrent vector fields) (§1.1). Prop 1.6 recovers equivalence when C contains a non-degenerate open cone field.
- [P] Props 5.15–5.16 characterise hyperbolicity by a uniform length bound for causal curves returning to a compact set (GH4), or by (GH5)+(GH6), à la Minguzzi (§5.4).

## Verified quotes
> "We work in the setting of closed (or equivalently semi-continuous) cone fields with singularities."

> "This notion has the advantage of not resting on the choice of an auxiliary metric and it bypasses some technical difficulties related to the non continuity of the length."

> "We impose a manifold structure on the phase space, and directly deal with smooth Lyapounov (or time) functions."

> "Just before sending this second version, we received the preprint [21] of Minguzzi, where several of our results are recovered using more traditional constructions."

> "We work on a complete Riemannian manifold"

> "Our statement is more general, since we allow closed (equivalently : semi-continuous) cone fields with singularities. Our proof is entirely different."

> "We stress that neither stable causality nor strong causality is assumed here"

> "Theorem 3. The closed cone field C is hyperbolic if and only if it admits a (smooth) Lyapounov function which is steep with respect to a complete Riemannian metric."

> "Note that the definition of hyperbolicity does not involve the metric."

> "Each hyperbolic cone field admits a hyperbolic enlargement."

> "The conclusion of Theorem 3 is false if (GH2) is replaced by (GH3) without assuming that C has non empty interior."

## Methods and evidence
- Data / setting: smooth manifold M with a complete Riemannian metric; closed cone fields, possibly singular or degenerate.
- Baselines: Conley and Hurley (chain recurrence); Hawking and Seifert (stable causality ⇒ time function); Bernal–Sánchez (smooth time functions, splitting); Fathi–Siconolfi (continuous cone fields, weak KAM); Sullivan's lemma (recovered as Prop 1.10).
- Evaluation: mathematical proofs.
- Artifacts: none.

## Limitations and caveats
- Everything lives in TM: cones, enlargements, Lyapounov regularity (dτ·v > 0), steepness (dτ·v ≥ |v|) and the splitting. The base must be a smooth manifold carrying a complete Riemannian metric.
- Global hyperbolicity **excludes singular points** (GH1). A point where the cone is the whole tangent space is never allowed in a hyperbolic field.
- The relation that is represented is F_C, the "stable" relation defined through open enlargements. It equals J_C only under hyperbolicity (Thm 3).
- The abstract does not overstate the theorems.

## Contradictions and tensions
- **Confirms** [[minguzzi2019causality]]: Minguzzi recovers several of these results (acknowledged here). F_C plays the role of Minguzzi's Seifert relation J_S = K for closed cone structures, and Thm 3's J_C = F_C on hyperbolic fields matches Minguzzi's "global hyperbolicity ⇒ J closed (= K)". The two papers agree; they do not conflict.
- **Refines** round-1 [[chrusciel2012lorentzian]] note, (ii) ("ETT does not have the 'wider metric' trick … ETT replaces it by admissible measures + Levin"). Bernard–Suhr show the wider-cone trick is the whole engine of the smooth route: stable future, recurrence and hyperbolic enlargements all use it. That sharpens what ETT forgoes.
- **Consistent with** [[reall2021causality]]: Reall's causal cone C_p, the dual of the Gårding cone (closed and convex, possibly a convex hull at triple points), is a closed cone field in this sense as long as the field is semi-continuous, which Reall does not state. Thm 3 would then give Cauchy temporal functions for "Causal" in modified gravity under (GH1)+(GH2).

## Open questions
- Can ETT define "enlargement" order-theoretically, e.g. a causality K' ≥ K with K ⊆ interior(K')? Then F_K := ∩ I_{K'} would be defined in ETT and Thm 1(a) could be compared with Levin applied to the closure of K.
- Bernard–Suhr allow singular points (full cone) but exclude them from hyperbolicity. Is a BTZ point (E_0), where ETT has empty chronological future, a "degenerate" or a "singular" point in some smooth structure? Not addressed; flagged, not claimed.

## Relevance to the questions
**(i) Smooth vs order-topological.** The base is smooth: manifold, complete Riemannian metric, TM-valued cones, smooth Lyapounov functions, de Rham smoothing of trapping domains (§4), and the flow of ∇τ. Order-topological content:
- Thm 1(a) read as "a closed relation is represented by its monotone functions";
- Prop 1.5's compactness argument;
- Lemma 5.11 ((GH2) ⇒ J^±(x) closed);
- the limit-curve identities F = J of Cor 5.14;
- Prop 5.16's characterisation, which uses only compactness and boundedness.

**(ii) Levin (ETT) vs Bernard–Suhr: which is more general?** Neither contains the other. They trade generality of the base for strength of the conclusion.
- *Levin* (closed preorder on a second-countable locally compact Hausdorff space ⇒ continuous utilities that represent it; [[minguzzi2019causality]] Th 3.13) is more general in the **base and the relation**. It needs no manifold, no cones and no enlargements, so it applies to ETT spaces with conical and BTZ lines whenever the relation is closed. It gives only **continuous** functions. Strict increase along causal curves needs antisymmetry of the closed relation (K-causality).
- *Bernard–Suhr* is more general in the **cone field** (semi-continuous, with singular and degenerate points), and stronger in **conclusion**: smooth, temporal (dτ·v > 0), steep, hence Cauchy, plus the smooth splitting and stability of hyperbolicity. But it needs a smooth manifold and the enlargement structure, and it represents the specific relation F_C, not an arbitrary closed preorder.
- On a manifold with a closed cone field, the two routes give the same relation, since F_C = K by Minguzzi's Th. 2.30 (round-1 note). Bernard–Suhr then upgrades Levin's continuous utility to a smooth temporal one. For ETT's purposes (topological spaces, Cauchy surfaces, Geroch splitting up to homeomorphism) Levin is the right tool and Bernard–Suhr is not needed. Bernard–Suhr only matters if a smooth splitting is wanted on the regular part.

**(iii) Formalization candidate.** Two order-theoretic statements that sit naturally in lean-causal:
- (a) `closed_of_compact_diamonds`, from Lemma 5.11: if J^+(x) ∩ J^-(K) is compact for every compact K, then J^+(x) is closed. Same flavour as Minguzzi Th 2.38 (round-1 Q4 item 6), and provable from compactness alone.
- (b) a "stable recurrence" lemma, from Prop 1.5: for a family of relations R_E indexed by a directed set, with closed R_E(x) ∩ R_E^{-1}(x) connected, the finite-intersection property on a compact boundary yields a point y ≠ x in ∩_E R_E(x) ∩ R_E^{-1}(x).

Statement (b) is only meaningful once ETT has enlargements, so (a) is the ready one.

## Leads for next round
- term: closed cone field; enlargement C ≺ C'; stable future F_C; stably recurrent set; trapping domain; steep Lyapounov function; Clarke differential; hyperbolic (GH1–GH6).
- cited: [10] Fathi–Siconolfi, "On smooth time functions" (continuous cone fields, weak KAM); [21] Minguzzi arXiv:1709.06494 = [[minguzzi2019causality]] (the "traditional" recovery, confirmed by reference list); [24] Müller–Sánchez (steep temporal functions, isometric embedding into Minkowski); [18] Minguzzi, K-causality II; [29] Seifert 1971; [32] Sullivan's lemma; [8, 30, 31] converse Lyapounov theory for differential inclusions.
- author: Stefan Suhr (later Minguzzi–Suhr, Lorentzian metric spaces); Albert Fathi.
