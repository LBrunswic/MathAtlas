# kunzinger2018lorentzian — Lorentzian length spaces

Michael Kunzinger, Clemens Sämann
Annals of Global Analysis and Geometry 2018 · doi:10.1007/s10455-018-9633-1 · arXiv:1711.08990 · `pdf/kunzinger2018lorentzian.pdf`

**Tier: T1** — peer-reviewed (AGAG), ~20 citations/yr, founding paper of the Lorentzian length space programme that has since been widely extended; its examples rely on and agree with [[samann2015global]] and [[minguzzi2019causality]].
**Relevance: 2** — Q2 (synthetic, non-manifold causality: the main competitor of ETT), Q3 (explicitly lists conical singularities/cosmic strings as motivating low-regularity models; synthetic curvature singularities), Q1 (cites Sbierski's C^0-inextendibility as a driving application).
**Read:** full text for §1–3, §4.6, §5.1 (main theorem), §5.2; skimmed §4.1–4.5 (triangle comparison).

## Summary
Kunzinger and Sämann axiomatise Lorentzian geometry in the spirit of metric length spaces. A *causal space* is a set with a preorder ≤ and a transitive relation ≪ ⊂ ≤ (no causality condition required). A *Lorentzian pre-length space* adds a metric d and a lower semi-continuous time separation τ satisfying the reverse triangle inequality with τ > 0 ⇔ ≪. Causal curves are locally Lipschitz (for d) curves monotone for ≤. Adding causal path-connectedness, local causal closedness and "localizability" (local neighbourhoods with a continuous local time separation realised by maximal curves) and requiring τ to equal the sup of τ-lengths of causal curves gives a *Lorentzian length space*. They prove limit curve theorems, push-up, part of the causal ladder (GH ⇒ strongly causal ⇒ non-totally imprisoning ⇒ causal ⇒ chronological), finiteness and continuity of τ and the Avez–Seifert theorem under global hyperbolicity, then define timelike/causal curvature bounds by triangle comparison, non-branching of maximisers, and "curvature singularities" (detects the Schwarzschild r=0 singularity). Examples: continuous strongly causal causally plain spacetimes and locally Lipschitz strongly causal proper Lorentz–Finsler spaces are strongly localizable Lorentzian length spaces.

## Relevance to the questions
- **(i) metric vs order-topological.** The framework needs a *metric* d on X (for local Lipschitz curves, compactness, semicontinuity) and a *time separation* τ; the causal/chronological relations are primitive preorders, the topologies (Alexandrov, chronological) are derived and compared with d. Purely order-theoretic: causal spaces, I^±/J^±, Alexandrov and chronological topologies, push-up from the reverse triangle inequality (Lemma 2.10), causality conditions "chronological"/"causal" (Def. 2.35 i–ii). Metric-dependent: causal curves (Lipschitz in d), non-total imprisonment (bounded d-arclength), global hyperbolicity (non-totally imprisoning + compact diamonds), length L_τ, geodesics, curvature bounds. No Cauchy hypersurfaces, domains of dependence, time functions or splitting in this paper.
- **(ii) where ETT sits.** ETT and Lorentzian (pre-)length spaces are *incomparable*: both drop the manifold, but LLS keep a metric d and a time separation τ (needed for curvature, completeness, maximisers), while ETT keeps only topology + causality and, unlike this paper, proves Geroch (GH ⇔ Cauchy time function ⇔ Cauchy hypersurface) and CBG. ETT's causal curves are order-theoretic (no Lipschitz parametrisation), so ETT is closer to KS's "causal space + topology" layer. Conical/BTZ singular flat spacetimes are natural LLS examples (flat metric off the singular lines, the d of a Riemannian background), though not treated here; the paper only motivates by "conical singularities and cosmic strings". A curvature-bound statement (flatness = curvature bounded above and below by 0 away from singular lines; a conical line of angle α < 2π would show as a bound in one direction) is a possible bridge, unverified.
- **(iii) Lean candidates.** (a) Push-up from the reverse triangle inequality (Lemma 2.10) and openness of ≪ from lower semicontinuity of τ (Prop. 2.13) — trivial but a clean interface if lean-causal ever adds a time separation (e.g. from ETT's admissible measures). (b) The causal-space ladder fragment "causal + interpolative ⇒ chronological" (Lemma 2.38 i). (c) GH ⇒ τ finite and continuous (Th. 3.28) needs lengths; out of scope for ETT unless a time separation is added. Low priority overall: the payoff of LLS (curvature, Sbierski-type extension questions) needs τ.

## Key points
- [V] Goal includes situations "where there is only a causal structure not necessarily induced by a metric" (§1).
- [V] Lorentzian pre-length space = causal space + metric d + lower semicontinuous τ with reverse triangle inequality and τ>0 ⇔ ≪ (Def. 2.8).
- [P] Push-up (x ≤ y ≪ z ⇒ x ≪ z) follows from the reverse triangle inequality alone (Lemma 2.10); ≪ is open in X×X (Prop. 2.13).
- [V] Causal curves are d-locally Lipschitz ≤-monotone curves; a discrete d gives no causal curves (Def. 2.18 and remark).
- [V] Global hyperbolicity = non-totally imprisoning + compact causal diamonds (Def. 2.35 v).
- [P] Causal ladder fragment for LLS: GH ⇒ strong causality ⇒ non-total imprisonment ⇒ causality ⇒ chronology (Th. 3.26).
- [V] GH Lorentzian length spaces are geodesic (Avez–Seifert, Th. 3.30); τ finite and continuous (Th. 3.28).
- [V] Continuous, strongly causal, causally plain spacetimes are strongly localizable LLS (Th. 5.12), proof uses [[samann2015global]] Th. 5.7 and Prop. 6.4.
- [P] For continuous metrics τ need not be lower semicontinuous (Example 5.2 referenced in Example 2.11), hence causal plainness is needed.
- [P] Locally Lipschitz proper strongly causal Lorentz–Finsler spaces with F(∂C)=0 are strongly localizable LLS (Th. 5.16), built on [[minguzzi2019causality]].
- [V] Open: weakening local Lipschitz continuity of the cone structure via an analogue of causal plainness (§5.2).
- [V] Motivating low-regularity models include conical singularities and cosmic strings (§1).
- [P] Synthetic curvature singularity = local triangle-comparison failure for every K (Def. 4.20); detects Schwarzschild interior r=0 (Example 4.22).
- [P] Ties to Sbierski's C^0-inextendibility [Sbi18] and the follow-up [GKS18] (extendibility of LLS, timelike completeness ⇒ inextendibility, non-manifold extensions) (§1).

## Verified quotes
> "or even to situations where there is only a causal structure not necessarily induced by a metric."

> "Then (X, d, , ≤, τ ) is called a Lorentzian pre-length space and τ is called the time separation function."

> "Note that if d is the discrete metric on X, then there are no causal curves"

> "(v) globally hyperbolic if (X, d, , ≤, τ ) is non-totally imprisoning and for every x, y ∈ X the set J + (x) ∩ J − (y) is compact in X."

> "Theorem 3.30. Any globally hyperbolic Lorentzian length space (X, d, , ≤, τ ) is geodesic."

> "Let (M, g) be a spacetime with a continuous, strongly causal and causally plain metric. Then (M, dh , , ≤, τ ) is a strongly localizable Lorentzian length space."

> "Physically relevant models of even lower regularity include spacetimes with conical singularities and cosmic strings"

> "Finally, a natural open question is whether one can weaken the assumption of local Lipschitz continuity of the cone structure by an analogue of causal plainness"

> "In particular, both the original spacetime and the extension are now allowed to be of low regularity and indeed also non-manifold extensions can be considered."

## Methods and evidence
- Data / setting: pure mathematics; metric spaces with causal relations and a time separation; examples from continuous Lorentzian metrics, closed cone structures, causal sets / causal Fermion systems (non-rigorous outlook).
- Baselines: metric length spaces / Alexandrov and CAT(k) spaces; Kronheimer–Penrose causal spaces; Busemann timelike spaces; Sorkin–Woolgar.
- Evaluation (metrics, seeds, variance, held-out?): full proofs; examples (funnels, bubbling metric of §5.1).
- Artifacts (code / data / weights): none.

## Limitations and caveats
- No Cauchy hypersurfaces, time functions, domains of dependence or splitting in this paper: global causal structure is weaker than in [[minguzzi2019causality]] or ETT.
- Requires a metric d inducing the topology; causal curves must be d-Lipschitz, which ties the theory to a choice of background metric.
- Continuous spacetimes enter only under causal plainness (bubbling metrics excluded) and strong causality; closed cone structures only when locally Lipschitz.
- Conical singularities are mentioned only as motivation; no worked example of a conical or BTZ line.

## Contradictions and tensions
- [[galloway2017timelike]]: consistent — both note that τ (Lorentzian distance) fails lower semicontinuity for C^0 metrics; KS need causal plainness to recover it.
- [[minguzzi2019causality]]: KS rely on local Lipschitz continuity of the cone field (Th. 5.16), whereas Minguzzi's causality theory works for merely upper semi-continuous cone fields; KS flag the gap as an open question.

## Open questions
- Is a singular flat spacetime with conical lines (E_α) a (strongly localizable) Lorentzian length space with the induced τ? With BTZ lines (E_0), where I^±(p) of a singular point may be empty in ETT terms, does τ>0 ⇔ ≪ still give a pre-length space?
- Do ETT's causal curves (order-theoretic) coincide with KS's d-Lipschitz ≤-monotone curves in the presence of singular lines?

## Leads for next round
- term: Lorentzian pre-length space, localizability, causal plainness, timelike/causal curvature bounds, synthetic curvature singularity, null distance (Sormani–Vega), timelike funnel.
- cited: [GKS18] Grant–Kunzinger–Sämann, "Inextendibility of spacetimes and Lorentzian length spaces" (extension of Sbierski's C^0 programme to LLS and non-manifold extensions); [Vic90] Vickers, "Quasi-regular singularities and cosmic strings"; [VW00] Vickers–Wilson, generalised hyperbolicity in conical spacetimes, CQG 17 (2000) 1333–1360; [KP67] Kronheimer–Penrose; [SW96] Sorkin–Woolgar; [MP06] Martin–Panangaden (spacetime from causal order); [SV16] Sormani–Vega null distance; [Sbi18] Sbierski Schwarzschild C^0-inextendibility.
- author: M. Kunzinger, C. Sämann, R. Steinbauer, J. Grant, E. Ling (later LLS work: Cavalletti–Mondino synthetic Ricci bounds, Braun; "Lorentzian metric spaces" Minguzzi–Suhr).
