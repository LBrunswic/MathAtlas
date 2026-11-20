# luk2026formation — The formation of a weak null singularity in the interior of generic rotating black holes

Jonathan Luk, Jan Sbierski
arXiv preprint 2026 · arXiv:2604.04877 · `pdf/luk2026formation.pdf`

**Tier: T3** — unreviewed preprint (~135 pp.) by leading authors; concrete complete method; an independent concurrent preprint (Gurriaran, arXiv:2603.17911) proves "a very similar result", which is supporting but itself unreviewed.
**Relevance: 2** — Q1 (completes the Kerr-interior programme: formation + Lipschitz inextendibility), Q3 (weak null singularity; low-regularity extension). Little ETT content.
**Read:** sections 1, 1.2, statement of Thm 1.2 and Remark 4.8; Sections 5–8 (estimates) skimmed via headings only

## Summary
For the vacuum Einstein equations, characteristic data on a dynamical event horizon H⁺ settling to subextremal strictly rotating Kerr (0<|a|<M), plus a transversal null hypersurface, are considered. Upper bounds (as in Dafermos–Luk) give a Cauchy horizon CH⁺ to which the metric extends continuously; a new L²-averaged lower bound on the l=2 modes of the s=+2 Teukolsky field ψ₀ on H⁺ yields that CH⁺ is a weak null singularity: the metric is not Lipschitz extendible across it (Thm 1.2). The proof is a nonlinear stability argument showing ψ₀ is well approximated by a linear Teukolsky field whose instability was proved earlier (Sbierski [99]), then propagating the lower bound to CH⁺ and invoking the curvature-blow-up criterion of [[sbierski2024lipschitz]].

## Key points
- [V] Main result: weak null singularity forms; metric C^0-extendible but not Lipschitz-extendible across CH⁺ (abstract; Thm 1.2.3).
- [P] Thm 1.2 hypotheses: smooth (finite-regularity suffices) characteristic data on H⁺ ≅ [1,∞)×S² and H̲₁; (i),(ii) ε-closeness to Kerr with I₀ derivatives; (iii)(a) weighted L²-averaged lower bound on l=2 modes of ψ₀ on H⁺, (iii)(b) improved-decay upper bounds on l>2 modes and ∂_t ψ₀ (§1, Thm 1.2; precise form §4.1).
- [V] Strategy: dynamical Teukolsky field approximated by linear field; linear instability used "as a black box" (abstract; §1).
- [V] Subextremal Kerr has a smooth Cauchy horizon across which the metric extends smoothly but non-uniquely (§1).
- [V] Scope: "a suitably defined generic subclass" of data (§1).
- [V] Genericity of the lower bound is conjectural: Remark 4.8 ties q = 11 / q = 7 decay rates to generic data only "Conjecturally".
- [V] Independent concurrent result by Gurriaran [50] (§1.2.5).
- [V] Uniqueness of extensions fails for merely continuous extensions to weak null singularities (§1.2.4, citing [5]).
- [P] Positions Sbierski's [97] (= [[sbierski2020holonomy]]) as the first Lipschitz inextendibility result for weak null singularities and [101] (= [[sbierski2024lipschitz]]) as the geometric input (§1.2.4).

## Verified quotes
> "we prove that a weak null singularity forms, across which the spacetime metric is continuously extendible but not Lipschitz extendible."

> "The bulk of the proof is a stability argument showing that a dynamical Teukolsky field can be approximated by a linear Teukolsky field, whose linear instability was proved in previous works."

> "It is important to note that the linear result is used as a black box"

> "there is a smooth Cauchy horizon across which the metric can be extended smoothly — but non-uniquely!"

> "rigorously establish that for a suitably defined generic subclass of initial data, the Cauchy horizon is a weak null singularity"

> "Remark 4.8. Conjecturally, when q = 11, our assumptions correspond to the decay rate for generic solutions"

> "While finalizing the current paper, Gurriaran has posted a paper on the arXiv [50] proving a very similar result."

> "(Such uniqueness results for extensions fail to hold for merely continuous extensions to weak null singularities, see [5].)"

> "Fix M, a such that 0 < |a| < M ."

## Methods and evidence
- Data / setting: characteristic initial value problem, vacuum, double-null + principal null frame, Newman–Penrose & Christodoulou–Klainerman formalisms.
- Baselines: Dafermos–Luk C^0 stability [21]; linear instability [99] (or Gurriaran [49]).
- Evaluation: rigorous energy estimates (I₀ derivatives, ε small).
- Artifacts: n/a.

## Limitations and caveats
- Title says "generic rotating black holes", but the theorem is conditional on lower-bound assumption (iii) on the event horizon, whose genericity for Cauchy data is only conjectured (Remark 4.8) — the title/abstract slightly exceed what is proved (claims_exceed_evidence).
- Characteristic data on the event horizon, not Cauchy data; connection to the exterior stability problem is assumed rather than proven; small |a| caveats in exterior stability.
- Only Lipschitz inextendibility; C^0 ∩ W^{1,2}_loc formulation open.
- Local near CH⁺ near i⁺; interior beyond not described.

## Contradictions and tensions
- Consistent with [[sbierski2024lipschitz]] (supplies its hypothesis (3.16)) and [[sbierski2020holonomy]].
- [[cameron2026spherically]] cites this paper and Gurriaran as independent proofs of the weak null singularity.

## Open questions
- Does the result extend to Cauchy data (removal of horizon lower-bound assumption by a genericity theorem)?

## Relevance to the questions
- (i) Entirely hard-analytic (smooth metric, curvature, Teukolsky). The only causal structure used is the double-null foliation, the MGHD and the Cauchy horizon as boundary.
- (ii) ETT offers nothing for the analysis; it could at most phrase the conclusion's causal framing (MGHD; future-inextendible timelike curves reaching CH⁺). Flat conical/BTZ spacetimes are vacuum but flat with codimension-2 defects, far outside the perturbed-Kerr regime; no examples/counterexamples.
- (iii) No formalization target.

## Leads for next round
- term: Teukolsky field; principal null frame; characteristic initial value problem; Gajic–Kehrberger data; mass inflation
- cited: [50] Gurriaran, "Non-linear instability of the Kerr Cauchy horizon near i⁺", arXiv:2603.17911; [21] Dafermos–Luk; [99] Sbierski linear instability of Teukolsky at Kerr CH; [69] Luk weak null singularities in vacuum; [88] Ori–Flanagan; [105] Song Einstein–Euler weak null singularities; [74] Luk–Oh–Shlapentokh-Rothman scattering approach
- author: Sebastian Gurriaran, Maxime Van de Moortel, Christoph Kehrberger, Dejan Gajic
