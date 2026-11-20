# samann2015global — Global Hyperbolicity for Spacetimes with Continuous Metrics

Clemens Sämann
Annales Henri Poincaré 2015 (vol. 17, 2016) · doi:10.1007/s00023-015-0425-x · arXiv:1412.2408 · `pdf/samann2015global.pdf`

**Tier: T1** — peer-reviewed (AHP), standard reference for C^0 global hyperbolicity; its Th. 5.7 and Prop. 6.4 are used as black boxes by [[kunzinger2018lorentzian]] (Th. 5.12) and [[galloway2017timelike]] (Thm 3, reproved there), and its results are re-derived for closed cone structures in [[minguzzi2019causality]].
**Relevance: 2** — Q2 (GH equivalences at C^0, and which steps go through the smooth theory), Q1 (supplies the maximiser-existence result Sbierski's C^0-inextendibility line uses), Q4 (Cauchy hypersurface ⇒ GH is a clean ETT target).
**Read:** full text (arXiv v4), proofs of §2 (topologies on curve spaces) skimmed.

## Summary
For a time-oriented Lorentzian manifold with a continuous metric, Sämann defines global hyperbolicity as non-total imprisonment plus compactness of causal diamonds J⁺(p) ∩ J⁻(q) (Def. 3.1), with causal curves as locally Lipschitz curves causal a.e. He shows this is equivalent to compactness of the space of causal curves between two points (Th. 3.2), to compactness of J⁺(K₁) ∩ J⁻(K₂) (Cor. 3.4), and to the existence of a Cauchy hypersurface (Th. 5.7 and 5.9), with M homeomorphic to R × S. GH implies causal simplicity (J^± closed, Prop. 3.3), stable causality, and is stable: there is a smooth metric with strictly wider cones that is still GH (Th. 4.5, following Fathi–Siconolfi). The interior of the domain of dependence of an acausal set is GH with a smooth Cauchy time function (Cor. 5.8). Finally, length is upper semicontinuous on curve spaces, so GH gives maximal causal curves between causally related points (Th. 6.3, Prop. 6.4).

## Relevance to the questions
- **(i) metric vs causal/order-topological.** Metric-dependent: causal curves (a.e. tangent condition), the Riemannian background h, the length functional (Th. 6.3, Prop. 6.4), and — crucially — the step GH ⇒ Cauchy hypersurface/splitting, which goes through stability (a smooth wider GH metric, Th. 4.5) and then *the smooth theory* (Geroch, Bernal–Sánchez). Order-topological: Cauchy hypersurface ⇒ GH (Th. 5.7) uses only limit-curve compactness and the definition "met exactly once by every inextendible causal curve"; Cor. 3.4 (diamonds of points compact ⇒ diamonds of compacta compact, under non-imprisonment); GH ⇒ J^± closed (Prop. 3.3).
- **(ii) where ETT sits.** ETT proves Geroch's theorem *intrinsically* (admissible measures + continuously reachable K^±) on metrizable, locally compact, tarentin, causally arc-connected, locally causally convex topological spacetimes — so on its domain ETT is strictly more self-contained than Sämann, whose GH ⇒ splitting uses the smooth theory as a black box via a wider smooth metric, a move ETT cannot make (no wider causalities at a singular line). Sämann's framework does not contain singular flat spacetimes (metric must be continuous everywhere on a manifold); he only cites Vickers–Wilson for conical singularities and cosmic strings being GH in a *different* (field-evolution) sense. Maximal-curve existence (§6) is metric, outside ETT; it is however the input Sbierski's C^0-inextendibility line needs (via [[galloway2017timelike]]).
- **(iii) Lean candidates.** (a) `globallyHyperbolic_of_cauchy`: a set met exactly once by every inextendible causal curve ⇒ GH (Th. 5.7) in ETT (ETT has it as part of its Geroch theorem; check the library's statement matches this "causal curve" form). (b) `diamondCompacta_of_diamondPoints`: non-imprisoning + J⁺(p)∩J⁻(q) compact ∀p,q ⇒ J⁺(K₁)∩J⁻(K₂) compact ∀ compact K₁,K₂ (Cor. 3.4). (c) GH ⇒ J^± closed (Prop. 3.3), compare [[minguzzi2019causality]] Th. 2.38.

## Key points
- [V] Abstract: GH via compact causal diamonds + non-total imprisonment extends to continuous metrics retaining all equivalences.
- [V] Definition: GH = non-totally imprisoning + J(p,q) compact for all p, q (Def. 3.1).
- [P] Non-imprisoning: GH ⇔ C(p,q) compact for all p,q (Th. 3.2); GH ⇔ J⁺(K₁)∩J⁻(K₂) compact (Cor. 3.4); GH ⇒ J^± closed (Prop. 3.3).
- [P] GH ⇒ stably causal, with a smooth wider metric that is non-totally imprisoning (Th. 4.3).
- [V] Stability: GH ⇒ there is a smooth g′ ≻ g that is GH (Th. 4.5), idea from Fathi–Siconolfi.
- [V] Cauchy hypersurface defined as met exactly once by every inextendible causal curve (Def. 5.1); it is a closed acausal topological hypersurface (Prop. 5.2).
- [P] Cauchy hypersurface ⇒ GH (Th. 5.7), proved directly via limit curves.
- [V] GH ⇒ Cauchy hypersurface and M ≅ R × S (homeomorphic) (Th. 5.9), "directly from the stability of global hyperbolicity and the smooth theory".
- [P] Interior of D(S) for acausal S is GH with smooth Cauchy time function (Cor. 5.8).
- [V] GH ⇒ globally maximal causal curve between causally related points (Prop. 6.4).
- [V] Vickers–Wilson showed spacetimes with conical singularities and cosmic strings are GH in Clarke's field-evolution sense (§1).

## Verified quotes
> "We show that the definition of global hyperbolicity in terms of the compactness of the causal diamonds and non-total imprisonment can be extended to spacetimes with continuous metrics, while retaining all of the equivalences to other notions of global hyperbolicity."

> "Theorem 4.5. Let (M, g) be globally hyperbolic, then there is a smooth metric g ′ ≻ g such that (M, g ′ ) is globally hyperbolic."

> "Definition 5.1. A subset S of M is called a Cauchy hypersurface if it is met exactly once by every inextendible causal curve."

> "Conversely, global hyperbolicity implies the existence of a Cauchy hypersurface. This follows directly from the stability of global hyperbolicity and the smooth theory."

> "Theorem 5.9. Let (M, g) be globally hyperbolic, then there is a Cauchy hypersurface S in M and moreover, M is homeomorphic to R × S."

> "In particular, if (M, g) is globally hyperbolic, then there is a (globally) maximal curve connecting any two points in the spacetime which are causally related."

> "Vickers and Wilson ([VW00]) showed that spacetimes with conical singularities and cosmic strings are globally hyperbolic in this sense."

## Methods and evidence
- Data / setting: continuous Lorentzian metrics on smooth manifolds; spaces of causal curves with C^0 / uniform topologies.
- Baselines: smooth equivalences (Minguzzi–Sánchez, Bernal–Sánchez, Geroch), Chruściel–Grant C^0 theory, Fathi–Siconolfi stability.
- Evaluation (metrics, seeds, variance, held-out?): proofs.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- GH ⇒ Cauchy/splitting is not intrinsic: it imports the smooth theory through a wider smooth metric; the splitting is only topological.
- Continuous metric on a manifold everywhere; singular lines and non-manifold points excluded.
- The "conical singularities are GH" statement is Vickers–Wilson's, in a different (Clarke) notion of GH; not proved here.

## Contradictions and tensions
- [[minguzzi2019causality]]: same equivalences, but Minguzzi proves GH ⇒ Cauchy time function intrinsically (Geroch volume function on a wider cone structure) for closed cone structures, whereas Sämann defers to the smooth theory. Consistent results.
- [[galloway2017timelike]]: reproves Sämann's Prop. 6.4 (maximisers) and notes only compact diamonds are needed; consistent.

## Open questions
- Does ETT's Geroch theorem, specialised to a continuous-metric spacetime, recover Sämann's Th. 5.7/5.9 (i.e. does every continuous spacetime satisfy ETT's hypotheses: tarentin, causally arc-connected, locally causally convex, admissible measures)? Bubbling metrics are a test case.
- What precisely is Vickers–Wilson's "generalised hyperbolicity" for conical spacetimes, and does it agree with ETT's GH for E_α-lines?

## Leads for next round
- term: generalised hyperbolicity (Clarke), compactness of the space of causal curves, stable causality at C^0, compactly stably non-totally imprisoning.
- cited: [VW00] Vickers–Wilson, "Generalized hyperbolicity in conical spacetimes", CQG 17 (2000) 1333–1360 — the only existing hyperbolicity treatment of conical singularities in this cluster; [Cla98] Clarke, *The analysis of space-time singularities*; [HKS12] Hörmann–Kunzinger–Steinbauer (GH via metric splitting, wave equation on non-smooth spacetimes); [SW96] Sorkin–Woolgar K-causality; [FS12] Fathi–Siconolfi; [Chr13] Chruściel low-regularity Cauchy problem.
- author: C. Sämann, J. Vickers, J. Wilson, C. J. S. Clarke.
