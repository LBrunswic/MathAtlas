# sbierski2017proof — On the proof of the $C^0$-inextendibility of the Schwarzschild spacetime

Jan Sbierski
Journal of Physics: Conference Series 968 (2018) 012012 · doi:10.1088/1742-6596/968/1/012012 · arXiv:1711.11380 · `pdf/sbierski2017proof.pdf`

**Tier: T2** — peer-reviewed proceedings note, fully proved, explicitly a streamlining of the author's own JDG paper [[sbierski2015c]]; its Prop 2.2 (Lipschitz-graph boundary chart) is reused as the starting point of [[sbierski2023c]] (Prop 2.1 there), so it is in active use; conference venue and not self-contained (defers to [[sbierski2015c]]) keeps it at T2.
**Relevance: 3** — Q1 (method), Q2 (purely causal steps: boundary chart, timelike separation, homotopy confinement), Q4 (Prop 2.2 is a strong formalization target).
**Read:** full text (arXiv v2)

## Summary
A streamlined proof that maximal analytic Schwarzschild is C^0-inextendible. New ingredient 1: Proposition 2.2, a structural result — near any future boundary point of a globally hyperbolic M inside a C^0 extension there is a near-Minkowskian chart in which M contains the region below the graph of a Lipschitz function f, the graph lies in ∂⁺M and is achronal. New ingredient 2: the exterior case is dispatched by [[galloway2017timelike]] (a timelike geodesic leaves M; geodesics reaching infinity are complete, but in the chart they have bounded length). New ingredient 3: the interior case (r→0) is handled locally in a single chart: one shows I⁺(γ(−µ), M_int) sits inside the chart below the graph (Step 1, via future one-connectedness of the interior + timelike separation), so every Cauchy hypersurface of M_int meets it in a set of uniformly bounded intrinsic diameter (Step 2), whereas the slices {r=1/n} contain pairs of points at intrinsic distance → ∞ (Step 3). Spherical symmetry is no longer used to build multiple charts, though it is still used in Steps 1.2.2/1.4 (rotations in SO(d)).

## Relevance to the questions
- **(i) smooth vs causal/topological.** Purely causal/topological (given openness of I^± in the extension): the definition of ∂⁺; Prop 2.2's construction of f as a "sup of the points still in I⁺(Σ,M)" and the contradiction "a past-inextendible timelike curve contained in I⁺(Σ,M)" (only uses Σ Cauchy + openness); achronality of graph(f); Remark 2.5 (past-directed timelike curves from below the graph stay in M); Step 1.1 (homotopy confinement: a timelike homotopy with fixed endpoints cannot leave a precompact diamond — connectedness/open-closed argument); Step 1.2.1 (K timelike separates, uses only chronology + openness + I⁺=J⁺-closure relations); Step 1.3–1.4 compactness/positive-distance argument. Metric-dependent: near-Minkowskian chart (|g̃−m|<δ), cone sandwich C⁺_{5/6} ⊂ timelike ⊂ C⁺_{5/8}, Lipschitz bound on f, Step 2 bound on induced metric of Σ (needs g̃ components bounded), Step 3 explicit Schwarzschild computation, Lemma 3.4 integrability (d ≥ 3), and the use "g_int smooth (!)" for I⁺ = int J⁺.
- **(ii) ETT.** Prop 2.2 is essentially a statement about a causality on an open set of R^{d+1} sandwiched between two cone fields; ETT's causalities on open sets, Cauchy surfaces and K± can state "the boundary of a globally hyperbolic open sub-causal-space near a future boundary point is an achronal graph" provided a local product structure (time coordinate) is available. The interior obstruction (infinite spacelike diameter) is metric. The homotopy-confinement lemma and timelike-separation step are order-topological. Not about conical/BTZ lines, but the same "locate the extension through a boundary chart" scheme is what one would apply to E_α/E_0 lines (where the obstruction would be holonomy rather than diameter).
- **(iii) candidate statement.** `future_boundary_graph`: Let (M̃, C̃) be a causal space, U ⊂ M̃ a chart ≅ (−ε0,ε0)×B with C̃|U between the cone fields of two constant-cone Minkowski metrics (narrow ⊂ C̃ ⊂ wide), M ⊂ M̃ open, globally hyperbolic with Cauchy surface Σ, and p ∈ ∂⁺M. Then there is f : B → (−ε0, ε0) with {x0 < f(x)} ⊆ M ∩ U and graph f ⊆ ∂⁺M, graph f achronal (and f Lipschitz with constant given by the wide cone). Also `homotopy_confined`: a timelike homotopy with fixed endpoints in M whose ι-image starts inside a precompact diamond D ⊂⊂ Ũ stays in Ũ.

## Key points
- [V] Theorem 1.1: maximal analytic Schwarzschild is C^0-inextendible (§1).
- [V] Prop 2.2: near p ∈ ∂⁺ι(M) for globally hyperbolic M, a chart with |g̃_µν − m_µν| < δ and a Lipschitz f whose subgraph lies in ι(M) and whose graph lies in ∂⁺ι(M); the graph is achronal (§2).
- [V] Without global hyperbolicity the future/past boundaries need not be disjoint nor achronal (Figure 1 discussion, §2).
- [P] Prop 2.2 proof: f(x) := sup of s0 such that the vertical segment below lies in ϕ(ι(I⁺(Σ,M))); contradictions come from constructing a past-inextendible timelike curve in M lying in I⁺(Σ,M), impossible for Σ Cauchy (§2, Fig. 2).
- [V] Remark 2.7: the proof would simplify if some neighbourhood of p in M̃ avoided a Cauchy surface of M, which fails in general (point s in Fig. 1).
- [V] Thm 3.2: combining [[galloway2017timelike]] with Prop 2.2, the boundary geodesic ends in ∂⁺ι(M) on graph(f) (§3).
- [P] Exterior case: in the chart the geodesic has dx0-dominant tangent (cone C⁺_{5/8}), so its length is bounded; but geodesics escaping through infinity are complete (O'Neill) — contradiction (§4).
- [P] Interior case, Step 1: there is µ>0 with ι(I⁺(γ(−µ),M_int)) inside the subgraph region; uses future one-connectedness of M_int (Prop 3.6) and a timelike-separation set K (Def 2.14 of [[sbierski2015c]]) (§4).
- [P] Step 2: for any Cauchy surface Σ of M_int, the intrinsic distance of two points of I⁺(γ(−µ))∩Σ is ≤ C_d = ε1 d^{3/2} √C_g (§4).
- [V] Step 3: on Σ_n = {r=1/n}, d_Σn(p_n,q_n) = 2λ √(2m·n^{d−2} − 1) → ∞ (§4).
- [V] The overall proof still requires the future one-connectedness of the interior (§1).

## Verified quotes
> "given a C 0 extension of a globally hyperbolic spacetime, one can find a timelike geodesic that leaves this spacetime"

> "Theorem 1.1. The maximal analytic extension (Mmax , gmax ) of the Schwarzschild spacetime is C 0 inextendible."

> "Moreover, the set on the left hand side of (2.4), i.e. the graph of f , is achronal in"

> "There exists a Lipschitz continuous function f"

> "Again, the future and past boundaries are not disjoint. Moreover, the future (past) boundary is not achronal in the extension, nor in any small neighbourhood of the future boundary point s."

> "The proof would simplify drastically if one knew that one can find a neighbourhood of p in M̃ that is disjoint from a Cauchy hypersurface of M . In general this is however not the case"

> "to Σ being a Cauchy hypersurface of M , and thus we obtain"

> "dΣn (pn , qn ) = 2λ 2m · n(d−2) − 1 → ∞"

> "We should also point out that the proof overall still requires the future one-connectedness of the interior."

> "this part of the argument does not rely on spherical symmetry"

> "Since (Mint , gint ) is globally hyperbolic and gint is smooth (!)"

> "in contradiction to Step 2. This concludes the proof of Theorem 1.1."

> "The first case is now easily ruled out using the completeness of geodesics approaching timelike or null infinity – without the need of establishing the future oneconnectedness of the exterior."

## Methods and evidence
- Data / setting: (d+1)-dim maximal analytic Schwarzschild, d ≥ 3; C^0 extension with piecewise-smooth timelike curves.
- Baselines: original proof [[sbierski2015c]] (three steps, global spherically symmetric region covered by several regular flow charts).
- Evaluation: rigorous proof; not self-contained (defers to [[sbierski2015c]] for definitions and Prop 2.6 there).
- Artifacts: none.

## Limitations and caveats
- Still requires future one-connectedness of the interior and uses spherical symmetry in Steps 1.2.2 and 1.4 (rotations h ∈ SO(d)), despite "does not rely on spherical symmetry" being said of the local obstruction step only — the abstract's "more flexible" is fair but the symmetry is not fully eliminated. Not flagged as claims_exceed_evidence (the text concedes this).
- Lemma 3.4's integrability needs d ≥ 3.
- Not self-contained.

## Contradictions and tensions
- [[sbierski2015c]]: same theorem, different route; the 2017 note replaces the global spacelike diameter (multi-chart, spherical symmetry) by a single-chart local version, and the exterior one-connectedness by [[galloway2017timelike]]. No contradiction.
- [[sbierski2023c]] reuses Prop 2.2 (as its Prop 2.1) and refines it to a differentiable point with a spacelike tangent (its Prop 2.5).

## Open questions
- Can future one-connectedness of the interior be dropped (e.g. by a causal-boundary/TIF argument as in [[sbierski2023c]])?
- Prop 2.2 needs only openness of I⁺ and a Cauchy surface: does it hold for any causal space whose local cones are sandwiched (ETT setting)?

## Leads for next round
- term: future boundary chart; Lipschitz graph boundary; achronal boundary; timelike separation; future one-connectedness; homotopy confinement.
- cited: [1] Galloway–Ling, "Some remarks on the C^0-(in)extendibility of spacetimes", AHP 18 (2017) — origin of ∂± definitions; [2] [[galloway2017timelike]]; [4] [[sbierski2015c]]; [3] O'Neill.
- author: Galloway, Ling.
- follow-up: Sbierski "On holonomy singularities in general relativity & the C^{0,1}_loc-inextendibility of spacetimes" (cited as [14] in sbierski2023c) — the holonomy link relevant to Q3 (conical lines).
