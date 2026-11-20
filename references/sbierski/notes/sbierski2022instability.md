# sbierski2022instability — Instability of the Kerr Cauchy horizon under linearised gravitational perturbations

Jan Sbierski
Annals of PDE 2023 (arXiv 2022) · doi:10.1007/s40818-023-00146-9 · arXiv:2201.12295 · `pdf/sbierski2022instability.pdf`

**Tier: T2** — peer-reviewed (Annals of PDE), 100+ page complete proof; extends Luk–Sbierski (scalar waves) and Luk–Oh–Shlapentokh-Rothman's scattering method; hypotheses verified generically for slowly rotating Kerr by an independent group (Ma–Zhang). Not itself reproduced.
**Relevance: 2** — Q1 (black-hole interiors, strong cosmic censorship theme), Q3 (motivates weak null singularities / C^0 extensions); little direct bearing on Q2/Q4 (pure PDE analysis on a smooth background).
**Read:** §1 (introduction, main theorem, SCC discussion, outline) in full; §3 theorem statements; §§4–8 skimmed for structure only.

## Summary
The paper proves a linear blue-shift instability at the Cauchy horizon of sub-extremal Kerr for gravitational perturbations: if the s = +2 Teukolsky field satisfies integrated upper and lower polynomial-decay bounds along the event horizon (with an infinite weighted L² integral for some mode), then a weighted L² integral along any hypersurface Σ transversal to the Cauchy horizon is infinite (Thm 1.1 / Thm 3.9). In regular coordinates at CH⁺ this means the Teukolsky field measured in a frame regular at the Cauchy horizon blows up. The method follows Luk–Oh–Shlapentokh-Rothman: energy estimates in the interior, Teukolsky's separation of variables, and analysis of transmission/reflection coefficients at frequency ω = 0 via the Heun/hypergeometric equation and the Teukolsky–Starobinsky identities. The horizon hypotheses are satisfied generically for slowly rotating Kerr by Ma–Zhang, with p₀ = 7, l₀ = 2.

## Key points
- [V] Main result: conditions on the s=+2 Teukolsky field along the event horizon (integrated upper and lower decay bounds) imply blow-up of the Teukolsky field in a frame regular at the Cauchy horizon (abstract; Thm 1.1; Thm 3.9).
- [V] The horizon hypotheses hold generically for slowly rotating Kerr with compactly supported data, with p₀ = 7, l₀ = 2, m₀ ∈ {−2,−1,1,2}, and q̃ any value strictly less than 13 (§1, after (1.3), p. 5).
- [P] Method: scattering-theoretic proof after Luk–Oh–Shlapentokh-Rothman [48]; Teukolsky separation, ω=0 Heun → hypergeometric reduction, non-vanishing of a transmission coefficient T_{H⁺,0l}(0) ≠ 0 (Prop 6.48) (§1.4, §§5–7).
- [V] Context (Dafermos–Luk, Thm 1.4): the perturbed metric stays C^0-close to Kerr up to the Cauchy horizon, so any singularity is in the connection, not the metric — a weak null singularity (§1.1, pp. 5–6).
- [V] SCC formulation used: generic MGHD is inextendible with continuous metric and L²_loc Christoffel symbols (§1.2, p. 6).
- [V] Explicit limitation: the result only shows non-extendibility in a particular natural coordinate system, not coordinate-independent inextendibility — open (§1.2, p. 7).

## Verified quotes
> "This paper establishes a mathematical proof of the blue-shift instability at the sub-extremal Kerr Cauchy horizon for the linearised vacuum Einstein equations."

> "The conditions are in particular satisfied by solutions of the Teukolsky equation arising from generic and compactly supported initial data by the recent work [51] of Ma and Zhang for slowly rotating Kerr."

> "with p0 “ 7, l0 “ 2 and m0 P t´2, ´1, 1, 2u. The parameter qr can be chosen to be anything strictly less than 13."

> "Thus, if a singularity forms, it is not at the level of the metric itself, as is the case for example for the Schwarzschild singularity"

> "Such singularities have been termed ‘weak null singularities’."

> "The maximal globally hyperbolic development arising from generic asymptotically flat initial data for the vacuum Einstein equations is inextendible as a Lorentzian manifold with a continuous metric and locally square integrable Christoffel symbols."

> "the result does not contribute to developing methods which show that no matter what coordinate system is chosen for the extension, the metric cannot be extended in g P C 0 and Bg P L2loc . This is an open problem."

> "Let us also remark that we expect Theorem 1.1 to be an important ingredient in the analysis of the blue-shift instability at the Cauchy horizon for the full non-linear vacuum Einstein equations."

## Methods and evidence
- Data / setting: interior of sub-extremal Kerr, linearised vacuum Einstein via the s=+2 Teukolsky equation (Newman–Penrose), principal null frame, Boyer–Lindquist and ingoing/outgoing coordinates.
- Baselines: Luk–Sbierski [49] (scalar waves, energy method); Luk–Oh–Shlapentokh-Rothman [48] (scattering proof on RN, whose method is adopted); McNamara; Dafermos–Shlapentokh-Rothman.
- Evaluation: rigorous proof; genericity of hypotheses imported from Ma–Zhang [51] (slow rotation only).
- Artifacts: n/a.

## Limitations and caveats
- Linear only; the non-linear problem is not addressed (stated as future ingredient).
- Blow-up is in a specific (regular) frame and background differentiable structure; coordinate-independent C^0/L² inextendibility is explicitly open (§1.2) — this is exactly the gap the extension-uniqueness papers ([[sbierski2022uniqueness]], [[cameron2025uniqueness]]) attack.
- Genericity of the assumptions is known only for slowly rotating Kerr (via [51]); for the full sub-extremal range the theorem is conditional.
- Abstract says "conditions … ensure … becomes singular", which matches the theorem; no claims_exceed_evidence.

## Contradictions and tensions
- None with other notes. Complementary to [[cameron2025uniqueness]]: Cameron–Sbierski's Example 5.3 shows that the C^1 structure at a Dafermos–Luk weak null singularity is not determined by the C^0 extension — so "blow-up in a frame regular at CH⁺" (this paper) is relative to one chosen differentiable structure, which is precisely the caveat stated in §1.2 here.

## Open questions
- Non-linear instability for Kerr; coordinate-independent inextendibility with g ∈ C^0, ∂g ∈ L²_loc.
- Full sub-extremal range genericity of the event-horizon decay hypotheses.

## Relevance to the questions
**(i) Smooth vs causal content.** Entirely analytic: smooth Kerr background, Teukolsky PDE, spin-weighted harmonics, energy estimates, ODE scattering. The only causal ingredients are the Penrose-diagram structure (event/Cauchy horizons, bifurcation spheres, Σ transversal to CH⁺) and the global-hyperbolicity / MGHD framing of SCC.
**(ii) What ETT could do.** Nothing at the level of the theorem. Indirectly, the paper motivates the regularity hierarchy (C^0 metric, L² connection) in which SCC is posed; ETT's role would be at the "C^0 metric" end — stating what the maximal globally hyperbolic development and its extensions are without a metric (CBG over a rigid geometry gives the MGHD object whose extendibility SCC concerns). The Cauchy horizon is a null boundary of an MGHD; in singular flat 2+1 spacetimes (BTZ), the analogous object is the Cauchy horizon of a BTZ-type development, where no blue-shift analysis applies (flat, no local degrees of freedom).
**(iii) Candidate formalisation.** None directly. At most a statement-level target: the definition of "MGHD extendible across a Cauchy horizon" in lean-causal, as the object on which SCC-type theorems are stated.

## Leads for next round
- term: blue-shift instability; Teukolsky equation; strong cosmic censorship (Christodoulou formulation); weak null singularity; Cauchy horizon; Teukolsky–Starobinsky identities; transmission/reflection coefficients.
- cited: [17] Dafermos–Luk "C^0-stability of the Kerr Cauchy horizon"; [49] Luk–Sbierski (scalar waves on Kerr interior); [48] Luk–Oh–Shlapentokh-Rothman; [51] Ma–Zhang (Teukolsky decay, slowly rotating Kerr); [63] Sbierski on coordinate-independent inextendibility (likely the holonomy / C^{0,1} paper); [43] Luk "Weak null singularities in general relativity"; [62]/[61] Sbierski C^0-inextendibility of Schwarzschild; [10] Christodoulou, [11] Chruściel (SCC formulation).
- author: Jonathan Luk; Sung-Jin Oh; Yakov Shlapentokh-Rothman; Mihalis Dafermos; Siyuan Ma & Lin Zhang; Peter Hintz.
