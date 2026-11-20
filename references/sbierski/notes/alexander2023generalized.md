# alexander2023generalized — Generalized cones as Lorentzian length spaces: Causality, curvature, and singularity theorems

Stephanie B. Alexander, Melanie Graf, Michael Kunzinger, Clemens Sämann
Communications in Analysis and Geometry 31(6) 2023 · doi:10.4310/cag.2023.v31.n6.a5 · arXiv:1909.09575 (v2, 2021, read) · `pdf/alexander2023generalized.pdf`

**Tier: T2** — Peer-reviewed (CAG), with full proofs. Its causal-plainness result is already relied on by [[grant2019future]], but the paper is not otherwise independently reproduced. Claims are proportionate to the evidence; the singularity theorems are restricted to smooth warping functions, as the paper states.
**Relevance: 2** — Q3: it covers ETT's massive-particle models E_α as a special case (reader inference) but not BTZ E_0. Q2: an LLS family with optimal causality.
**Read:** full text of §1–4 and §6; §5 statements and Cor 5.5 table; appendix skimmed.

## Summary
The paper defines **generalized cones** Y = I ×_f X: an open interval I, a metric length space X, and a continuous positive warping function f, read as "−dt² + f² d_X²". Causal curves are absolutely continuous with strictly monotone time component. Results:
- The causality is optimal: push-up holds and I^± is open for every length space X (Prop 3.22). The authors note this amounts to causal plainness even for continuous f.
- Y is a strongly causal Lorentzian length space for locally compact X (Thm 4.8), regular for geodesic X (Cor 4.9), and globally hyperbolic for proper geodesic X (Prop 4.10).
- Maximisers project to minimising geodesics of X, with fibre independence (Thm 3.29).
- Timelike curvature bounds of Y follow from metric curvature bounds of X (Thm 5.3; table Cor 5.5) and conversely (Thm 5.7).
- §2 treats Minkowski cones Cone(X) over a space X; Thm 2.5 says Cone(X) has timelike curvature ≥ 0 iff X is Alexandrov ≥ −1.
- §6 proves Hawking- and Myers-type singularity theorems (Cor 6.4) and the absence of upper curvature bounds at a big bang or big crunch (Cor 6.7), but only for **smooth** f.

## Relevance to the questions
- **(i) Metric versus causal.** The construction is metric through and through: the fibre metric d_X, the metric derivative v_β, and the length functional. The causal facts are derived from that metric, not assumed:
  - I^± open and push-up (Prop 3.22, via the ODE h' = f∘h and the fibre-distance description of I^+);
  - J^± closed (Cor 3.24);
  - compact diamonds (Lemma 4.1).
  - The singularity theorems use smoothness of f (Thm 6.2 needs f'').
- **(ii) Conical and BTZ lines (Q3).**
  - **E_α is a generalized cone** [reader inference, unverified beyond the definitions]. ETT's E_α has metric −dt² + dr² + r²dθ² with θ of period α, so E_α = ℝ ×_1 C_α, where C_α is the 2D Euclidean cone of angle α. The singular line {vertex} × ℝ is *included*. C_α is a complete, locally compact geodesic length space. Hence:
    - E_α is a strongly causal, regular, globally hyperbolic Lorentzian length space (Thm 4.8, Cor 4.9, Cor 4.11), with I^± open and push-up holding through the line (Prop 3.22).
    - C_α is Alexandrov CBB 0 for α ≤ 2π and CAT(0) for α ≥ 2π. That is a standard metric-geometry fact, *not stated in this paper*.
    - The Cor 5.5 row (I = ℝ, f = 1, K = 0 ⇒ K' = 0) then gives timelike curvature bounded below by 0 for α ≤ 2π and above by 0 for α ≥ 2π.
    - So a massive particle of angle α < 2π is synthetically "curvature ≥ 0", not a curvature singularity in the sense of KS18.
  - **Spacetimes with several particles.** Similarly, §2's Minkowski cone Cone(X) over a hyperbolic surface X with cone points is a flat spacetime with massive particles emanating from a vertex. Thm 2.5 then reads: timelike curvature ≥ 0 iff X is Alexandrov ≥ −1, i.e. iff all cone angles are ≤ 2π [reader inference].
  - **BTZ E_0 is not covered.** Its singular line is lightlike and E_0 is not a product with a timelike base. Moreover, BTZ points have I^-(p) = ∅, which violates the localisability axiom of LLS (see [[grant2018inextendibility]]).
  - **Remark 3.32.** It discusses f with isolated zeros (cone vertices, big bang). It needs ∫1/f to diverge to keep I^± open, and leaves the case uninvestigated.
  - The paper's causality theorems are of the "causal ladder" kind: strong causality and global hyperbolicity. No Cauchy surfaces, Geroch splitting or CBG. ETT and lean-causal supply exactly those for E_α-manifolds that are *not* globally products, i.e. quotients and gluings of the models.
- **(iii) Lean candidate.** A modest one, below lean-causal's current altitude:
  - `ealpha_globallyHyperbolic_model`: the model E_α, with ETT's causality, is globally hyperbolic, and {t = 0} is a Cauchy surface.
  - Lemma 4.1 supplies the content in a metric-free form: J(p,q) ⊆ [t₀,t₁] × (fibre ball intersection).
  - Statable as "the product of the order ℝ with a proper geodesic fibre, with relation |Δt| ≥ d_X, has compact diamonds".
  - Higher value: cite this paper in the ETT draft as the LLS-side treatment of E_α, so that ETT's E_α results are positioned against it. LLS: curvature and inextendibility. ETT: Cauchy and CBG theory, plus BTZ lines, which LLS cannot host.

## Key points
- [V] Push-up and openness of I^± hold for every generalized cone over a length space (Prop 3.22, §3).
- [V] Generalized cones over locally compact length spaces are strongly causal Lorentzian length spaces (Thm 4.8, §4).
- [V] Over proper geodesic X they are globally hyperbolic (Prop 4.10, §4).
- [V] There is no causal bubbling even for merely continuous f (§1.1).
- [P] Maximisers have minimising fibre components; fibre independence (Thm 3.29, §3).
- [V] Thm 5.3: a curvature bound on X transfers to a timelike curvature bound on Y when the model I ×_f M²(K) has it (§5). [P] Table Cor 5.5 includes the static row I = ℝ, f = 1, K = 0 ⇒ K' = 0.
- [P] Thm 2.5: the Minkowski cone over X has timelike curvature ≥ 0 (≤ 0) iff X is Alexandrov ≥ −1 (≤ −1) (§2).
- [V] Singularity theorems need smooth f (Cor 6.4, §6). [P] Lower bound K < 0 ⇒ τ ≤ b − a (Myers type); K = 0 with f non-constant ⇒ past or future timelike incompleteness (Hawking type).
- [V] Non-positive lower timelike curvature bounds imply incomplete timelike geodesics (Abstract).
- [P] Cor 6.7: a big bang or big crunch precludes any upper timelike curvature bound (§6).
- [V] f with zeros is only sketched; the authors defer it (Remark 3.32).

## Verified quotes
> "length, i.e., push-up holds. Moreover, I ± (p) is open for any p ∈ Y ."

> "Any generalized cone I ×f X, where (X, d) is a locally compact length space, is a strongly causal Lorentzian length space."

> "Let I ×f X be a generalized cone, where (X, d) is a geodesic length space that is a proper metric space. Then I ×f X is globally hyperbolic."

> "we show that there is no causal bubbling in such spacetimes even if the warping function f , and hence the Lorentzian metric, is merely continuous"

> "Then Y = I ×f X has timelike curvature bounded below/above by K ′ if I ×f M2 (K) has timelike curvature bounded below/above by K ′ ."

> "Let X be a geodesic length space, Y = I ×f X with I = (a, b), f : I → (0, ∞) smooth."

> "showing that non-positive lower timelike curvature bounds imply the existence of incomplete timelike geodesics."

> "but this would need to be investigated more carefully."

## Methods and evidence
- Data / setting: pure mathematics. Metric length spaces as fibres, an interval base and a continuous warping function. Example 3.27 recovers the continuous Lorentzian warped products, and Example 3.31 the Minkowski cones.
- Baselines: Riemannian/Alexandrov warped products [AB98, BBI01]; Alexander–Bishop [AB08]; KS18 ([[kunzinger2018lorentzian]]).
- Evaluation (metrics, seeds, variance, held-out?): full proofs.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- Only a one-dimensional time base. General globally hyperbolic splittings −β dt² + h_t are mentioned only as future work.
- The singularity theorems and Thm 6.2 need smooth f. Remark 6.3 leaves the non-smooth case open.
- No conical, cosmic-string or BTZ example is discussed; the application to E_α above is my inference.
- No inextendibility result and no Cauchy development theory.

## Contradictions and tensions
- [[grant2019future]]: consistent. That paper cites this one ([AGKS19]) for causal plainness of continuous warped products, which complements its counterexamples.
- [[kunzinger2018lorentzian]]: answers part of that note's open question. E_α *is* a strongly causal regular LLS (by inference here). E_0 remains outside, because of empty I^- at BTZ points.
- [[sbierski2023c]]: FLRW is a generalized cone, so its K = +1 inextendibility setting sits in this class. This paper has no inextendibility result to compare.
- [[sbierski2020holonomy]]: by inference, E_α carries bounded timelike curvature (one-sided bound 0) in the synthetic sense, unlike the curvature blow-up behind Sbierski's holonomy singularities. This is consistent with round 1's "conical lines are outside his hypotheses".

## Open questions
- Is ETT's causality on E_α (curves in U, Def. "causal structure of the model spaces") the same as the generalized-cone ≤, ≪ on ℝ ×_1 C_α? Presumably yes, since both use causal curves; to verify.
- Does Remark 3.32's zero-of-f extension give a synthetic setting for big-bang vertices of Minkowski cones over hyperbolic cone-surfaces, the flat "particle" spacetimes?
- Is there a Lorentzian analogue for E_0 (lightlike singular line), perhaps a null-base warped product?

## Leads for next round
- term: generalized cone; Minkowski cone; fibre independence; Lorentzian length structure (Appendix).
- cited: [AB08] Alexander–Bishop, Lorentz and semi-Riemannian spaces with Alexandrov curvature bounds (CAG 2008); [GKS19] = [[grant2018inextendibility]]; [GKSS20] = [[grant2019future]]; [Gra20] Graf, singularity theorems for C¹ metrics.
- author: S. Alexander; M. Graf.
