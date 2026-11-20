# Round 1 summary

Round 1 read 19 papers: 13 by Sbierski or co-authored with him, and 6 context works on low-regularity causality.
All 19 are read, 247 of 247 quotes verify, and the KB is consistent.
Tiers: T1 ×8, T2 ×7, T3 ×4.

## Findings per research question

### Q1: Sbierski's results, by theme

1. **The maximal Cauchy development without Zorn.**
   - `sbierski2013existence` [P, T1], Thm 3.4, Def 3.5, Thm 3.13.
   - The maximal common development is the union of all common developments, which needs only the rigidity statement Cor 3.2.
   - Gluing two developments gives a Hausdorff space because no "corresponding boundary points" exist.
   - ZF+DC suffices.
2. **Predictability beyond the light cone.**
   - `eperon2018predictability` [V/P, T2]: subluminal equations can have several maximal developments from the same data. Superluminal ones have a unique maximal development, provided the initial hypersurface is suitable.
   - The mechanism (Thm 4.64): two developments agree on every connected component of their overlap where they agree somewhere. So non-uniqueness needs a disconnected overlap.
   - The development of a shock-forming wave is unique and has a singular boundary carrying causal bubbles: `abbrescia2025quasilinear` [P, T3].
3. **C⁰-inextendibility.** Minkowski and Schwarzschild: `sbierski2015c` [T1]. Timelike completeness plus global hyperbolicity: `galloway2017timelike` [T1]. Boundary charts: `sbierski2017proof` [T2]. FLRW with K=+1: `sbierski2023c` [T3].
4. **Below C⁰: Lipschitz inextendibility through holonomy.**
   - `sbierski2020holonomy` [T2, Duke]: in any locally Lipschitz chart, holonomy along short loops is bounded (Lemma 2.13). Unbounded holonomy therefore rules out a Lipschitz extension.
   - `sbierski2024lipschitz` [T2, Inventiones]: weak null singularities without symmetry, from integrated curvature blow-up.
   - Related: `luk2026formation` [T3, claims exceed evidence: "generic" rests on a conjectured bound] and `cameron2026spherically` [T3].
5. **Uniqueness of extensions.**
   - `sbierski2022uniqueness` [T2]: two extensions anchored by the same causal curve, with locally Lipschitz metrics, agree up to a C^{1,1} isometry. This is sharp: below Lipschitz only a homeomorphism survives.
   - `cameron2025uniqueness` [T3]: in 1+1 dimensions, every C⁰ extension either is the reference extension or is a "corner".
6. **Black-hole interiors.** Kerr Cauchy-horizon instability and wave blow-up, `sbierski2022instability` [T2]. Background only for this review.

### Q2: what topological causality (ETT) could take over

The papers separate cleanly. Each reader traced which steps are causal or topological and which need a metric.

**Purely causal or topological once I± is open:**
- the gluing and Hausdorffness lemma (`sbierski2013existence` Thm 2.7–2.8, reused by `graf2023uniqueness`);
- the union-of-developments construction, given rigidity;
- locating an extension: some timelike curve leaves M (`sbierski2015c` Lemma 2.17);
- the boundary chart, which is pure Cauchy-surface logic given cones squeezed between a narrow and a wide constant cone (`sbierski2017proof` Prop 2.2);
- homotopy confinement and future one-connectedness, which depend only on the conformal class (`sbierski2023c`);
- the whole K=+1 FLRW theorem (`sbierski2023c` §4.1, Prop 3.6);
- the C⁰ dichotomy of `cameron2025uniqueness` (Thm 4.3), whose last step is "a continuous bijection from a compact set is a homeomorphism".

**Genuinely metric:** the timelike and spacelike diameters, length maximizers, the C¹ structure of extensions, and holonomy bounds.

**The two-cone mechanism.** In `eperon2018predictability`, sub- and superluminality are an inclusion between two causal orders on one topological space. Lemma 4.72, Lemma 4.70, Thm 4.77 and Thm 4.82 are statable verbatim for two nested causalities. This is the "generalized equations" opening.

### Q3: singular spacetimes; conical and BTZ lines

- No paper in the KB treats conical or BTZ lines.
- Sbierski's holonomy singularities are **unbounded** families of boosts at curvature blow-up. Conical E_α and BTZ E_0 lines have **bounded, nontrivial, fixed** holonomy.
- They sit outside his hypotheses, which need curvature, while the regular part of E_α and E_0 is flat. So they are neither examples nor counterexamples to his theorems.
- Conjecture to examine [reader inference, unverified]: bounded nontrivial holonomy could make conical and BTZ lines Lipschitz-inextendible. The obstacle is that loops around the line are spacelike, so the causal-homotopy Lemma 2.12 does not apply directly.
- Geroch–Traschen's distributional-source theory (cited by `sbierski2020holonomy`) is where cosmic strings, that is conical lines, fall outside the weak-solution class.

### Q4: candidate lean-causal statements (consolidated, by readiness)

1. Gluing-Hausdorff lemma for an open embedding, and its family version (pure topology). Shared with lean-causal's CBG Hausdorffness theorem.
2. Locating an extension: ∂⁺ ∪ ∂⁻ ≠ ∅ for a proper open embedding into a connected causal space.
3. Nested causalities: Eperon–Reall–Sbierski Lemmas 4.70 and 4.72, Thm 4.77 and Thm 4.82.
4. An abstract FLRW-type inextendibility: a future one-connected, globally hyperbolic causal space with properties (A) and (B) has no past extension that admits a boundary chart.
5. The causal-homotopy confinement lemma, with compact causal diamonds.
6. Context results:
   - compact emeralds imply J closed (`minguzzi2019causality` Th 2.38);
   - a Cauchy set implies global hyperbolicity (`samann2015global` Th 5.7);
   - the characterisation of D⁺ by compact J⁻(p)∩S (`chrusciel2012lorentzian` Th 2.10).

## Consensus (at least two T1/T2 sources)

- Below Lipschitz regularity, causal bubbles appear and push-up fails, so J-based definitions are needed: `chrusciel2012lorentzian` and `sbierski2022uniqueness`. This supports ETT's choice of J and K±.
- Hausdorffness of the gluing is the crux of maximal-development existence: `sbierski2013existence`, `graf2023uniqueness`, `sbierski2022uniqueness`.
- The C¹ structure of an extension is the fragile layer, and topology is the robust one: `sbierski2022uniqueness`, `cameron2025uniqueness`, `sbierski2024lipschitz`.

## Contradictions

- None between sources.
- One correction: `abbrescia2025quasilinear` footnote 8 corrects ERS19's belief that Christodoulou had built the whole maximal development.
- One process note: the Minguzzi reader dropped a quote that crossed a page break rather than edit it.

## Gaps

- No treatment of conical or BTZ singularities in any low-regularity framework read.
- No causality theory for PDEs with several characteristic cones beyond ERS19.
- Reall's later work on modified-gravity causality is unread.
- Chruściel's low-regularity CBG (arXiv:1112.5779) is unread.

## Vocabulary learned

anchored extension; future/past boundary chart; corresponding boundary points; spacelike restart
point; causal bubble; causally plain; future one-connected; timelike separation; corner extension;
strongly spherically symmetric; intertwined geodesics; closed cone structure; emerald; Seifert
relation / K-causality; quasi-regular singularity; holonomy singularity; Milne-like.
