# sbierski2023c — The $C^0$-inextendibility of a class of FLRW spacetimes

Jan Sbierski
arXiv 2023 (v2, 15 Oct 2025; acknowledges two anonymous referees, so under/after review) · arXiv:2312.07443 · `pdf/sbierski2023c.pdf`

**Tier: T3** — preprint in the KB record (refereed per acknowledgements but venue not confirmed here); author with established track record in exactly this programme; complete proofs; builds on T1/T2 results ([[sbierski2015c]], [[sbierski2017proof]], [[galloway2017timelike]]).
**Relevance: 3** — Q1 (cosmological singularities), Q2 (Theorem 1.5's proof is almost purely causal), Q3 (big-bang singularity structure, Milne-like C^0-extensions), Q4 (Prop 3.6 + Thm 1.5 argument is a prime ETT target).
**Read:** full text §§1–2, 3.1, 4.1; §3.2 and §4.2 statements and outline.

## Summary
FLRW spacetimes g = −dt² + a(t)² g_K on (0,∞)×M_K (K ∈ {−1,0,1}, M_{+1} = S^d) without particle horizons (∫_0^1 dt/a = ∞). Theorem 1.5: for K = +1, d ≥ 2, every such spacetime is past C^0-inextendible with no further assumption on a. Theorem 1.6: for K = −1, d ≥ 2, past C^0-inextendible if additionally a(t)·exp(∫_t^1 dt'/a) → ∞ as t → 0, complementing Galloway–Ling's Milne-like C^0-extendibility (where that quantity converges). Method: past boundary chart with Lipschitz graph (from [[sbierski2017proof]]), future one-connectedness of FLRW (Prop 3.1, d ≥ 2 for K=+1), and for K=+1 a purely causal obstruction (Prop 3.6): the timelike future of any past-inextendible timelike curve is the whole spacetime, and the timelike past of any point contains an entire slice {t0}×S^d. For K=−1, a parametrisation of the past causal boundary (TIFs) by a null coordinate u and an angle, and a metric obstruction (Prop 3.13): intrinsic distance in Σ_t0 ∖ J⁻(q) between two curves generating distinct TIFs diverges.

## Relevance to the questions
- **(i) smooth vs causal/topological.** The K=+1 proof (§4.1) is causal except for the chart: inputs are (a) the boundary chart with achronal graph and "past-directed causal curves from below the graph stay below" (Prop 2.1, (2.4)) — causal given cone sandwich g̃_n ≺ g̃ ≺ g̃_w; (b) I⁺(p̃,Ũ) = ∪ I⁺(γ̃(s),Ũ) by openness of I⁺; (c) diamond identification via future one-connectedness + Lemma 2.8 (homotopy confinement); (d) Prop 3.6 (whole slice in a timelike past) — a statement about the conformal/causal structure only (no particle horizons + compact space); (e) final contradiction: a past-inextendible timelike curve meets I⁺(slice) but misses the Cauchy slice — pure Cauchy-surface logic. Metric enters only in: existence of near-Minkowskian chart, compactness of chart diamonds, Prop 3.1's proof (conformal factor, ||γ̇||<1), and K=−1's Prop 3.13 (intrinsic Riemannian distance) and Prop 2.5 (Rademacher differentiability + spacelike tangent, needs d ≥ 2). Prop 2.6 uses g̃ ∈ C^2 below the graph (null geodesics on ∂J⁺) and the push-up property.
- **(ii) ETT.** Theorem 1.5 is a natural theorem of ETT: define a "past extension" of a globally hyperbolic causal space as an open embedding into a causal space where some boundary point is reached by a past-directed timelike curve and which is locally cone-sandwiched (or just: locally has relatively compact diamonds and a local time function). Then "M future one-connected + every past-inextendible timelike curve's timelike future is all of M + every point's past contains a Cauchy surface ⇒ no past extension" is plausibly order-topological. The author himself says the proof "really only requires the future one-connectedness of the spacetime, the absence of particle horizons, and the compactness of the spacelike geometries". The conformal invariance of future one-connectedness (used in Prop 3.1) is exactly the kind of metric-free invariance ETT targets. Q3: the K=−1 Milne-like C^0-extensions are extensions through a big bang that look like a flat cone (Milne = interior of the light cone in Minkowski); this is the cosmological analogue of the regular E_α/E_0 cones of ETT, and BTZ-type quotients of Milne are natural singular flat spacetimes — a link to explore. The d = 1 case (all FLRW C^0-extendible, two inequivalent extensions via null coordinates u,v) is the 1+1 analogue of non-unique extensions.
- **(iii) candidate statement.** `past_inextendible_of_slice_in_past` (abstract Thm 1.5): Let M be a globally hyperbolic causal space (ETT) which is future one-connected and such that (A) for every past-inextendible timelike γ, ∪_s I⁺(γ(s)) = M, and (B) for every point x, I⁻(x) contains a Cauchy surface. Then M admits no past extension into a causal space with a past boundary chart (locally a product with achronal Lipschitz/continuous graph boundary and relatively compact diamonds). Plus Prop 3.6 itself for (0,∞)×S^d with conformal cone condition |σ̇|_{S^d} < 1/a(t) — a concrete Lean lemma: no particle horizons + diam S^d = π ⇒ each slice near 0 lies in I⁻(x).

## Key points
- [V] Theorem 1.5: d ≥ 2, K = +1, no particle horizons ⇒ past C^0-inextendible, with no further assumption on the scale factor (§1.1; abstract).
- [V] Theorem 1.6: d ≥ 2, K = −1, no particle horizons, plus a(t)·exp(∫_t^1 dt'/a(t')) → ∞ as t → 0 ⇒ past C^0-inextendible (§1.1).
- [V] In dimension d = 1 all FLRW spacetimes are past C^0-extendible, so d ≥ 2 is crucial (§1.2).
- [P] Galloway–Ling Milne-like condition (lim ȧ = 1 and a·exp(∫dt'/a) converging in (0,∞)) gives past C^0-extendibility for K=−1; the regime where that quantity is bounded but not convergent is left open (§1.2).
- [V] Lemma 1.8: any C^0-extension has ∂⁺ ∪ ∂⁻ ≠ ∅, so future+past C^0-inextendible ⇒ C^0-inextendible (§1.2).
- [V] Proof of Thm 1.5 needs only future one-connectedness, absence of particle horizons and compactness of the spatial geometry (§1.3).
- [V] Prop 3.1: every (d+1)-dim FLRW (d ≥ 2) is future one-connected; future one-connectedness is a conformal-class statement (§3).
- [V] Prop 3.6: for K=+1, I⁺ of a past-inextendible timelike curve's tail covers I⁻(γ(s0)) and some whole slice {t0}×S^d lies in I⁻(γ(s0)); remains true for any compact spatial geometry (§3.1).
- [P] Prop 2.5: for d ≥ 2 there is a future boundary point where f is differentiable with a spacelike direction in the tangent plane; impossible in 1+1 (boundary may be null everywhere) (§2).
- [P] Prop 3.13 (K=−1): for curves with distinct limit angles, intrinsic distance in Σ_t0 ∖ J⁻(q) diverges as t0 → 0; excluding J⁻(q) is essential (§1.3, §3.2).
- [P] K=−1 past causal boundary parametrised by null coordinate u and an angle; incomparable TIFs have finite u and distinct angles (Prop 3.8, §3.2).
- [V] Choice of topology of M_K affects future one-connectedness (footnote 1).

## Verified quotes
> "We show that in the case of constant spatial curvature K = +1, and without any further assumptions on the scale factor, the big bang singularity is sufficiently strong to exclude continuous spacetime extensions to the past."

> "Let d ≥ 2. Consider the class of (d + 1)-dimensional FLRW spacetimes without particle horizons and with K = +1 as defined above. Each such spacetime (M, g) is past C 0 -inextendible."

> "Then each such spacetime (M, g) is past C 0 -inextendible."

> "Firstly, in dimension d = 1 all FLRW spacetimes are past C 0 -extendible, which also shows that the assumption d ≥ 2 is crucial in our main theorems."

> "it leaves open the regime of scale factors"

> "Note that if a Lorentzian manifold is future and past C 0 -inextendible, then it is (globally) C 0 -inextendible."

> "For example, the proof of Theorem 1.5 really only requires the future one-connectedness of the spacetime, the absence of particle horizons, and the compactness of the spacelike geometries."

> "Any (d + 1)-dimensional FLRW spacetime as defined in the introduction is future one-connected."

> "We first note that future one-connectedness is a statement about the conformal class of the spacetime under consideration."

> "Furthermore for each such s0 ∈ (0, 1) there exists a t0 > 0 such that"

> "Note that this proposition remains true if we replace the spatial geometry of constant positive curvature by any compact spatial geometry."

> "The choice of topology affects whether the spacetime is future one-connected, a key element in the proofs presented here"

> "Note that the future boundary can of course be null everywhere which shows that the result cannot hold in two spacetime dimensions."

> "Note that the exclusion of J − (r, M ) in (1.9) is essential – otherwise the distance in Σt0 of the two points γ1 (t0 ) and γ2 (t0 ) would go to zero for t0 → 0."

> "The authors called such spacetimes Milne-like spacetimes."

> "This is a contradiction, which concludes the proof of Theorem 1.5."

## Methods and evidence
- Data / setting: FLRW with a ∈ C^2, a → 0 at t → 0, M_K simply connected space form; C^0 extensions; timelike curves piecewise smooth, causal piecewise C^1.
- Baselines: Galloway–Ling C^0-extendibility of Milne-like FLRW; Sbierski's C^{0,1}_loc-inextendibility of FLRW with particle horizons ([14] there); C^2-inextendibility via curvature.
- Evaluation: rigorous proofs.
- Artifacts: none.

## Limitations and caveats
- K = 0 (flat) case not treated; K=−1 needs an extra scale-factor condition; a gap regime remains between Thm 1.6 and Milne-like extendibility (conceded).
- Only simply connected spatial topologies; future one-connectedness depends on topology (conceded) — relevant for quotients (e.g. compact hyperbolic or BTZ-type).
- Abstract matches theorems; no overclaim.
- Preprint in KB metadata.

## Contradictions and tensions
- Complements (does not contradict) Galloway–Ling's C^0-extendibility of Milne-like K=−1 cosmologies: the dividing line is the behaviour of a(t)·exp(∫_t^1 dt'/a).
- Answers [[sbierski2015c]] §1.3 (ii) ("new techniques are needed" for FRW big bang) for K=+1 and part of K=−1.
- Uses [[sbierski2017proof]] Prop 2.2 (here Prop 2.1) and [[galloway2017timelike]] (future timelike completeness ⇒ future C^0-inextendible).

## Open questions
- Flat K=0 FLRW without particle horizons?
- Non-simply-connected spatial slices (compact hyperbolic quotients) where future one-connectedness may fail?
- Can Theorem 1.5 be proved for causal spaces (no metric) — i.e. is "past boundary chart" replaceable by a local causal condition?

## Leads for next round
- term: particle horizon; Milne-like spacetime; past boundary chart; terminal indecomposable future set (TIF); causal boundary; push-up property; future one-connectedness as conformal invariant.
- cited: [4] Galloway–Ling, "Some remarks on the C^0-(in)extendibility of spacetimes", AHP 18 (2017) (AdS, Milne-like); [14] Sbierski, "On holonomy singularities in general relativity and the C^{0,1}_loc-inextendibility of spacetimes", Duke Math. J. 171 (2022) — key for Q3 (holonomy/conical); [15] Sbierski, "Uniqueness and non-uniqueness results for spacetime extensions", arXiv:2208.07752; [3] Chruściel–Klinger, "The annoying null boundaries" (conditional C^0-inextendibility, expanding singularities); [11] Minguzzi–Suhr, Lorentz–Finsler regularity (timelike-completeness inextendibility); [8] Grant–Kunzinger–Sämann, "Inextendibility of spacetimes and Lorentzian length spaces" AGAG 2019; [1] Alexander–Graf–Kunzinger–Sämann, "Generalized cones as Lorentzian length spaces" arXiv:1909.09575 (cones! relevant to ETT E_α); [2] Cavalletti–Mondino synthetic timelike Ricci bounds; [6] Geroch–Kronheimer–Penrose, "Ideal points in space-time" (causal boundary/TIFs); [10] Ling, "The Big Bang is a coordinate singularity for k=−1 inflationary FLRW"; [7] Graf, [9] Kunzinger–Ohanyan–Schinnerl–Steinbauer (C^1 singularity theorems).
- author: Eric Ling; Galloway; Kunzinger–Sämann (Lorentzian length spaces); Graf (C^1 singularity theorems).
