# Synthesis: Jan Sbierski's work, and what topological causality (ETT) can add

Two rounds, 29 papers read (21 by Sbierski and co-authors or directly about his results, plus 8
on causality frameworks), 279 verified quotes. Claim grades: [V] verified quote, [P] paraphrase of
a text read in full, [S] secondary. Confidence: **high** when several T1/T2 sources agree, **medium**
for one T2 or several T3, **low** for an inference or a contested point.

## Q1. What Sbierski proved, by theme

1. **Maximal Cauchy developments without Zorn** (`sbierski2013existence`, T1) [P]. Existence via
   the union of all common developments, given rigidity, and a Hausdorff gluing because no
   "corresponding boundary points" exist. *High*: the same architecture is used independently by
   `chrusciel2013maximal` (with Zorn, rough data) and `graf2023uniqueness` (maximal boundaries).
2. **Predictability for equations whose cones are not the light cone** (`eperon2018predictability`, T2).
   - [V] Subluminal equations can have several maximal developments of the same data.
   - [V] Superluminal ones have a unique maximal development, provided the initial hypersurface
     is suitable.
   - Mechanism [P]: two developments agree where their overlap is connected (Thm 4.64).
   - Extension [P]: a shock-forming wave has a unique maximal development whose singular boundary
     carries causal bubbles (`abbrescia2025quasilinear`, T3).

   *Medium–high*.
3. **C⁰-inextendibility** [P]:
   - Minkowski and Schwarzschild through the spacelike diameter (`sbierski2015c`, T1);
   - timelike completeness as an obstruction (`galloway2017timelike`, T1);
   - boundary charts (`sbierski2017proof`, T2);
   - FLRW with K=+1 (`sbierski2023c`, T3).

   *High*.
4. **Lipschitz inextendibility through holonomy and curvature blow-up** [P]:
   - holonomy singularities (`sbierski2020holonomy`, Duke, T2);
   - weak null singularities without symmetry (`sbierski2024lipschitz`, Inventiones, T2);
   - related: `luk2026formation`, `cameron2026spherically` (T3).

   *High* for the theorems. *Medium* for "generic" in Luk–Sbierski, which rests on a conjectured
   lower bound.
5. **Uniqueness of extensions** [P]: anchored extensions agree up to a C^{1,1} isometry at
   Lipschitz regularity, sharply (`sbierski2022uniqueness`, T2). In 1+1 dimensions, a C⁰ extension
   is either the reference one or a "corner" (`cameron2025uniqueness`, T3). *Medium–high*.

## Q2. What topological causality can take over

**Answer: the causal skeleton of almost every argument, with one recurring hard step.**
**Confidence: high.**

- **Purely causal or topological** [P; confirmed by two synthetic re-proofs, `grant2018inextendibility`
  and `beran2026curvature`]:
  - the gluing and Hausdorff lemma;
  - the union of developments, given rigidity;
  - locating an extension (some timelike curve leaves M);
  - the boundary chart, given cones squeezed between two constant cones;
  - homotopy confinement and future one-connectedness (conformally invariant);
  - the whole K=+1 FLRW theorem;
  - the 1+1 C⁰ dichotomy.
- **The hard step** in every maximal-development proof is the local one: excluding corresponding
  boundary points, or extending an isometry past a boundary point (Sbierski Lemmas 3.8–3.11;
  Chruściel A1–A2). Published proofs use null geodesics or harmonic coordinates. Proving them
  without geodesics, from closed J, strong causality and compact diamonds, is the genuinely new
  mathematics ETT would contribute. *Medium*: identified by two readers, not attempted.
- **Genuinely metric, so out of ETT's reach:** timelike and spacelike diameters, length maximizers,
  the C¹ structure of extensions, holonomy bounds. "Timelike complete" becomes a definition in ETT,
  not a theorem.
- **Curve class:** "I± open" is automatic for piecewise-C¹ timelike curves, which is Sbierski's
  convention (`grant2019future` Lemma 2.7) [P]. It is a real hypothesis for Lipschitz curves.
  ETT's open ≪ axiom fits Sbierski's setting.

## Q3. Generalized Einstein equations and singular lines

- **Your hunch is supported in a precise form.** *Medium–high*.
  - "Generalizations of Einstein equations" with several characteristic cones (Lovelock, Horndeski,
    EFT corrections; `reall2021causality`, T2 [P]) give several causal orders on one spacetime.
  - ERS19's predictability results are statements about two nested causalities: Lemmas
    4.70 and 4.72, Thm 4.77, Thm 4.82.
  - ETT, which takes a causality as primitive and needs no metric, can state them verbatim.
  - Caveat: Reall establishes the nesting only partly (effective-metric cone inside the causal
    cone; physical-metric cone only "close"), so the nesting must be a hypothesis.
- **Conical and BTZ sources lie outside the standard weak theory, and inside ETT.**
  - The Geroch–Traschen class needs ∂g ∈ L²_loc, so it covers sources in codimension ≤ 1
    (`geroch1987strings` [S], `hormann2015conical` [V]).
  - Conical lines narrowly fail it, by a logarithm.
  - Sbierski's holonomy singularities are unbounded boosts at curvature blow-up. E_α and E_0 have
    bounded, fixed, nontrivial holonomy and a flat regular part, so they are neither examples nor
    counterexamples to his theorems [P]. *High*.
  - Existing treatments of conical spacetimes are static deficit-angle cones only, by PDE and
    Colombeau methods (`vickers2000generalized`, `hormann2015conical`). They agree with ETT that
    the axis must be kept as points: well-posedness and a Cauchy slice hold only then.
  - BTZ (E_0) lines are excluded by every framework read: Lorentzian length spaces,
    curvature-bound inextendibility, Colombeau and distributional theory.
- **Open conjecture** (*low*, reader inference): bounded nontrivial holonomy makes conical and BTZ
  lines Lipschitz-inextendible. The obstruction is that loops around the line are spacelike, so
  Sbierski's causal-homotopy lemma does not apply directly.

## Q4. Targets for lean-causal, ranked

| # | statement | source | readiness |
|---|---|---|---|
| 1 | Gluing-Hausdorff lemma for an open embedding, and its family version; non-Hausdorff points closed in ∂O | sbierski2013existence Thm 2.7–2.8, chrusciel2013maximal | near-term; shares machinery with the CBG Hausdorffness proof |
| 2 | Locating an extension, one-sided (covers BTZ points where I⁻ = ∅) | sbierski2015c L2.17, grant2018inextendibility L3.8 | near-term |
| 3 | Two nested causalities: wider GH ⇒ narrower GH; nested D±; ERS19 L4.70, L4.72, Thm 4.77, 4.82 with the nesting as hypothesis | eperon2018predictability, reall2021causality | near-term, high value: your "generalized equations" programme |
| 4 | In E_α × ℝ, {t=0} is Cauchy for all α > 0; with the axis removed it is not; explicit J⁻(x) ∩ {t=0} through axis points | hormann2015conical, vickers2000generalized | near-term (after T-ett-port-e0); first theorems on conical spacetimes in any formal system |
| 5 | Abstract maximal development with Zorn (Chruściel Thm 2.2), next to the Zorn-free CBG | chrusciel2013maximal | medium |
| 6 | Abstract FLRW-type inextendibility (future one-connected, properties A and B, no boundary-chart extension) | sbierski2023c §4.1 | medium |
| 7 | Corresponding boundary points and spacelike restart point without geodesics | sbierski2013existence L3.7–3.11 | research: the genuinely new step |
| 8 | Lipschitz inextendibility of conical and BTZ lines through holonomy | sbierski2020holonomy L2.12–2.13 | research: open conjecture |

## What the literature does not settle

- Whether the physical light cone lies inside the causal cone in Horndeski or Lovelock theories, in
  general (Reall: only "close").
- Any causality theory or well-posedness on spacetimes with BTZ (null) singular lines, or spinning
  or excess-angle strings.
- Lipschitz (in)extendibility of conical lines.
- A geodesic-free proof of the local uniqueness step of the maximal development.

## Recommended reading order

1. `sbierski2013existence`
2. `eperon2018predictability`
3. `reall2021causality`
4. `sbierski2017proof`
5. `sbierski2020holonomy`
6. `hormann2015conical`
7. `chrusciel2013maximal`
8. `grant2018inextendibility`
