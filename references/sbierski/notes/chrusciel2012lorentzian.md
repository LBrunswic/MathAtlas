# chrusciel2012lorentzian — On Lorentzian causality with continuous metrics

Piotr T. Chruściel, James D. E. Grant
Classical and Quantum Gravity 2012 · doi:10.1088/0264-9381/29/14/145001 · arXiv:1111.0400 · `pdf/chrusciel2012lorentzian.pdf`

**Tier: T1** — peer-reviewed (CQG), ~10 citations/yr, the standard reference for C^0 causality; its approximation scheme (Prop. 1.2) and causal-curve-based definitions are reused by [[samann2015global]], [[kunzinger2018lorentzian]] and [[galloway2017timelike]], and its bubbling question is answered in [[minguzzi2019causality]].
**Relevance: 3** — Q2 (exactly which causal facts need Lipschitz regularity: push-up, light-cones as hypersurfaces), Q3/Q4 (motivated by low-regularity Choquet-Bruhat–Geroch; I- vs J-domains of dependence matters for any CBG over ETT).
**Read:** full text §1 (all), §2 (domains of dependence, Th. 2.6–2.10); skimmed the explicit ODE computations of Examples 1.27–1.34.

## Summary
The paper builds causality theory for time-oriented Lorentzian metrics that are only continuous on a (smoothable) C^1 manifold. The key tool is sandwiching g between smooth metrics with strictly narrower and wider cones, ǧ ≺ g ≺ ĝ, arbitrarily close (Prop. 1.2). Timelike curves are refined to "locally uniformly timelike" (timelike for some smooth ǧ ≺ g), whose futures Ǐ^± are open. They exhibit *causal bubbling*: for C^{0,α} metrics (α<1) light-cones can have non-empty interior — an open region reachable by causal but not by timelike curves — so push-up and "a non-null causal curve can be deformed to a timelike one" fail. Lipschitz (C^{0,1}) metrics are causally plain, and all of the C^2 causality theory not addressing normal neighbourhoods or geodesics remains true for causally plain metrics (Th. 1.25, Cor. 1.26). In §2 they define domains of dependence with *causal* rather than timelike curves (the two differ under bubbling), prove that D_J(S) of an acausal spacelike C^1 hypersurface is globally hyperbolic, admits a smooth wider metric making it globally hyperbolic, and carries a smooth Cauchy time function (Th. 2.6–2.9), and characterise D⁺_J(S) by compactness of J⁻(p) ∩ S (Th. 2.10).

## Relevance to the questions
- **(i) metric vs causal/order-topological.** Metric-dependent: the whole construction relies on smooth approximating metrics with narrower/wider cones (convolution in charts), on a Riemannian background h, and on paracompactness imposed by hand (Geroch's paracompactness theorem needs the exponential map). Bubbling is an ODE phenomenon (non-uniqueness of null curves, Example 1.12). Order-topological content: the push-up lemmas as hypotheses (causal plainness is literally "∂Ǐ^±(p,U) = ∂J^±(p,U)"), the definition of D⁺_J and its characterisation (Th. 2.10: p ∈ D⁺(S) ⇔ J⁻(p) ∩ S non-empty and compact), and "Cauchy surface ⇒ GH" arguments using only limit curves.
- **(ii) where ETT sits.** ETT is designed for exactly the phenomenon C&G isolate: at singular lines of flat spacetimes push-up fails (ETT says K^± coincides with I^± "exactly where push-up holds"), and BTZ points have empty chronological future. ETT's K^± plays the rôle of C&G's Ǐ^±/"non-bubbling" part, and ETT's use of causal (J) curves for Cauchy developments matches C&G's choice of D_J over D_I. So ETT *generalises* the causally-plain part of C&G to non-manifolds, and gives a principled replacement for the timelike relation where it degenerates. ETT does not have the "wider metric" trick, so C&G's time-function proof (Th. 2.9 via a wider smooth metric) is not available; ETT replaces it by admissible measures + Levin. C&G's paper exists to supply causal tools for a low-regularity CBG (ref. [18], Chruściel arXiv:1112.5779) — the same goal as lean-causal's CBG over rigid singular geometries.
- **(iii) Lean candidates.** (a) `mem_cauchyDevelopment_iff`: for an acausal (closed) S, p ∈ D⁺_J(S) ⇔ J⁻(p) ∩ S is non-empty and compact (Th. 2.10) — statable in ETT. (b) "D_J(S) is globally hyperbolic" for an acausal Cauchy-type S (Th. 2.6), in ETT's sense (compact diamonds + causality). (c) A *bubbling witness* as a test fixture for lean-causal: a causality where J⁺(p) has non-empty interior not contained in the closure of I⁺(p), showing D_I ≠ D_J (Example 2.1) — a good regression example for which definition of Cauchy development the library uses.

## Key points
- [V] Motivation: the differentiability needed for causality arguments constrains the Choquet-Bruhat–Geroch theorem (§1).
- [V] For metrics that are merely continuous, light-cones need not be hypersurfaces: there are light-cones with non-empty interior (§1, Example 1.11).
- [V] C^{0,α} bubbling metrics exist for every α ∈ (0,1); C^{0,1} metrics are causally plain (Th. 1.20).
- [V] Causality theory of [16] not involving normal neighbourhoods or geodesics remains true for C^{0,1} (more generally causally plain) metrics (Cor. 1.26, Th. 1.25).
- [P] Smooth sandwich ǧ ≺ g ≺ ĝ with arbitrarily small distance exists for every continuous g (Prop. 1.2); l.u.-timelike futures are open (Prop. 1.4).
- [V] Domains of dependence are defined via causal curves because timelike-based definitions misbehave under bubbling (§2).
- [P] D_I(S) and D_J(S) differ for the bubbling metric: D_I includes the bubble region (Example 2.1, Fig. 2.1); bubbles can be refocussed so horizon generators are non-unique (Example 2.2).
- [P] D_J(S) of an acausal spacelike C^1 hypersurface is globally hyperbolic (Th. 2.6); it admits a smooth wider metric ĝ making it GH with Cauchy surface S (Th. 2.7) and a smooth Cauchy time function (Th. 2.9).
- [P] p ∈ D⁺_J(S) ⇔ J⁻(p) ∩ S non-empty and compact (Th. 2.10).
- [V] Paracompactness must be assumed by hand because Geroch's theorem uses the exponential map (Remark 1.1).

## Verified quotes
> "One of the factors that constrains the differentiability requirements of the proof of the celebrated Choquet-Bruhat–Geroch theorem [1], of existence and uniqueness of maximal globally hyperbolic vacuum developments of general relativistic initial data, is the degree of differentiability needed to carry out the Lorentzian causality arguments that arise."

> "Concerning point (i) above, we exhibit metrics with light-cones which have nonempty interior."

> "(i) For any α ∈ (0, 1) there exist C 0,α metrics which are causally bubbling."

> "(ii) C 0,1 metrics are causally plain."

> "Those parts of causality theory as described in [16] which do not explicitly address normal neighborhoods or geodesics remain true for C 0,1 metrics."

> "Therefore we develop here a theory for continuous metrics based on causal curves."

> "As such, we impose the condition that M be paracompact by hand."

## Methods and evidence
- Data / setting: continuous time-oriented Lorentzian metrics on C^1 (smoothable) manifolds; explicit 2-d examples g = −(du)² … built from ODEs with non-unique solutions.
- Baselines: Chruściel's "Elements of causality theory" (C^2), Hawking–Ellis, O'Neill.
- Evaluation (metrics, seeds, variance, held-out?): proofs and explicit counterexamples.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- Results involving geodesics or normal neighbourhoods are left open below C^{1,1} (stated explicitly, Cor. 1.26 discussion).
- Domain-of-dependence results assume a spacelike acausal C^1 hypersurface, not a general topological one.
- The authors defer the time-function result to Fathi–Siconolfi's more general method ([17]) and note theirs was found independently.
- Does not treat singular lines or non-manifold points; the continuous metric is defined everywhere.

## Contradictions and tensions
- [[minguzzi2019causality]]: Minguzzi presents C&G's theory as "seemed to work well only under locally Lipschitz regularity and did not include results involving lightlike geodesics", and shows that by using causal-curve definitions and local achronality the theory extends to upper semi-continuous cones, with Cauchy horizons generated by lightlike geodesics even in bubbling cases. A refinement rather than a contradiction.
- [[kunzinger2018lorentzian]] and [[galloway2017timelike]]: both depend on C&G's sandwich approximation (Prop. 1.2) for C^0 results; consistent.

## Open questions
- In ETT, which domain of dependence (via causal curves of J, or via the K/I relation) does lean-causal's CBG use, and does the C&G bubbling example separate them in ETT too?
- Does ETT's "push-up holds exactly where K^± = I^±" give an order-theoretic proof of C&G's Theorem 1.25 (causally plain ⇒ C^2 causality)?

## Leads for next round
- term: causal bubbling, causally plain, locally uniformly timelike, push-up lemma, D_J vs D_I domains of dependence, limit-geodesic.
- cited: [18] P. T. Chruściel, "On maximal globally hyperbolic vacuum space-times", arXiv:1112.5779 — the low-regularity CBG this paper serves (direct comparator for Sbierski 1309.7591 and lean-causal's CBG); [17] Fathi–Siconolfi "On smooth time functions" (C^0 cone structures, weak KAM); [16] Chruściel "Elements of causality theory" arXiv:1110.6706; [19] García-Parrado–Senovilla "Causal structures and causal boundaries"; [2] Klainerman–Rodnianski rough solutions.
- author: P. T. Chruściel, J. D. E. Grant.
