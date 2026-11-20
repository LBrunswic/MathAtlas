# grant2018inextendibility — Inextendibility of spacetimes and Lorentzian length spaces

James D. E. Grant, Michael Kunzinger, Clemens Sämann
Annals of Global Analysis and Geometry 2018 (vol. 55, 2019, as cited by [[beran2026curvature]]) · doi:10.1007/s10455-018-9637-x · arXiv:1804.10423 (v5 read) · `pdf/grant2018inextendibility.pdf`

**Tier: T1** — Peer-reviewed in AGAG. Its Lemma 3.8 and Thm 5.3 are reused and generalised by [[beran2026curvature]] (Thm 4.2) and its (TC) notion is used by [[alexander2023generalized]]. Caveat: [[beran2026curvature]] reports that, after a correction to KS18 Prop. 4.15, the curvature-blow-up result (Thm 5.4) rests on the "rather unnatural" local timelike geodesic connectedness hypothesis. Thm 5.4 states that hypothesis explicitly.
**Relevance: 3** — Q2: this is the synthetic counterpart of Sbierski-type inextendibility. Q4: Lemma 3.8 is a ready Lean target. Q1: it re-reads Galloway–Ling–Sbierski.
**Read:** full text.

## Summary
The paper defines extensions of Lorentzian pre-length spaces (Def 3.1). Such an extension need not be a manifold (Example 3.6). The paper proves the synthetic analogue of Sbierski's Lemma 2.17: an extension has a non-empty future or past boundary (Lemma 3.8). It defines geodesics as local maximisers and timelike completeness as property (TC). The main theorem (Thm 5.3) states that a strongly causal Lorentzian length space with (TC) is inextendible as a *regular* Lorentzian length space. If the extension also has causal curvature bounded above and is locally timelike geodesically connected, it is regular, so a timelike-complete space can only be extended by a space with unbounded upper causal curvature (Thm 5.4). For smooth spacetimes (Cor 5.5), this gives inextendibility within the continuous, strongly causal, causally plain and regular class. The class is narrower than Galloway–Ling–Sbierski's C⁰ class, but the original space need not be globally hyperbolic or smooth.

## Relevance to the questions
- **(i) What is metric and what is causal or topological.**
  - *Causal and topological:*
    - Lemma 3.8, which locates the extension. Its proof uses:
      - connectedness of X̃;
      - that ι(X) is open and proper;
      - that I^±(p̃) meets a neighbourhood of a boundary point p̃ (axiom (ii) of localisability);
      - openness of I^±, which here follows from lower semicontinuity of τ;
      - timelike path-connectedness.
    - The step in Thm 5.3 where a curve leaves ι(X) at a first exit point.
  - *Metric:*
    - the extension is a metric isometry d → d̃ (Def 3.1 ii);
    - the τ-length L_τ and geodesics as local maximisers;
    - property (TC) itself (infinite τ-length);
    - regularity (maximisers have a causal character);
    - synthetic curvature bounds.
  - *Not present:* Sbierski's boundary chart, homotopy confinement, future one-connectedness (only proposed as future work in §6), the spacelike diameter, Cauchy surfaces, global hyperbolicity of the original space, Geroch splitting and CBG.
  - *Minkowski:* Minkowski space is covered only through Cor 5.5, as a timelike-complete, strongly causal spacetime that is inextendible among *regular, causally plain* extensions. Schwarzschild is not covered, because it is timelike incomplete.
- **(ii) What ETT adds.**
  - Lemma 3.8 is statable in ETT verbatim. ETT already has an open chronological relation (axiom of Def. "category C") and causal arc-connectedness. Localisability's "I^±(y) ∩ Ω ≠ ∅" is needed only on one side: if I^-(p̃) = ∅, as at an ETT BTZ point, the proof's second case runs with q̃ ∈ I^+(p̃) and time reversed. This fits ETT's singular lines; the paper's axioms forbid them.
  - The LLS framework *excludes* BTZ points. Localisability requires I^±(y) ∩ Ω_x ≠ ∅ for every y, and a BTZ point has I^-(p) = ∅.
  - The analytic content of the theorem (TC, regularity, curvature) is metric and outside ETT unless a time separation is added.
  - ETT adds what is absent here: Cauchy surfaces, Geroch, CBG over rigid geometries, and singular lines as legitimate points of the space.
  - The paper's remark that only one property is needed is the bridge. That property: a maximal curve contained in the original space up to its boundary endpoint is timelike when its endpoints are timelike related. In ETT language this is "the exit curve is chronal", which is a causal condition once maximality is replaced by something order-theoretic.
- **(iii) Lean candidate.** `boundary_nonempty_of_extension`: let M̃ be a connected topological spacetime (ETT) with ≪ open and causally arc-connected. Let ι : M → M̃ be an open embedding of causal spaces with ι(M) proper, and let p̃ ∈ ∂ι(M) with I^+(p̃) ∪ I^-(p̃) ≠ ∅ (one side is enough). Then there is a chronal curve γ : [0,1] → M̃ with γ([0,1)) ⊆ ι(M) and γ(1) ∉ ι(M). This is the same target as round 1's `exists_timelike_curve_leaving` (from [[sbierski2015c]] and [[galloway2017timelike]]), here confirmed in a third, metric-free-ish framework. It is a strong first target.

## Key points
- [V] Extensions need not be manifolds; no coordinates or differentiability are used (§1).
- [V] Openness of I^±(x) is built into the axioms, via lower semicontinuity of τ (§2).
- [V] Localisability requires that I^±(y) meets the localising neighbourhood for every y (§2, (ii)). A point with empty chronological past, such as a BTZ point, violates it.
- [P] Def 3.1: an extension is a connected X̃ with a metric isometry ι onto a proper open subset that preserves ≪, ≤, causal and timelike curves, and τ-lengths. Prop 3.5: for smooth strongly causal spacetimes this is the same as a smooth isometric embedding (§3).
- [V] Lemma 3.8 (∂⁺ ∪ ∂⁻ ≠ ∅) is a direct analogue of Sbierski's Lemma 2.17 (§3).
- [V] Example 3.6: Minkowski minus a point extends to a non-manifold space with a branching half-ray, where maximal curves branch (§3). Via KS18 Cor. 4.13, the branching gives timelike curvature unbounded below.
- [P] Thm 4.4: synthetic geodesics are exactly causal pregeodesics in smooth strongly causal spacetimes. Prop 4.6: a geodesic extends as a geodesic iff it extends continuously (§4).
- [P] Thm 5.3: a strongly causal LLS with (TC) is inextendible as a regular LLS (§5).
- [V] Thm 5.4: under (TC), an extension that is strongly causal and locally timelike geodesically connected cannot have bounded upper causal curvature (§5). [C: vs beran2026curvature: this hypothesis is needed after the correction to KS18 Prop. 4.15]
- [V] Cor 5.5: a smooth, strongly causal, timelike-complete spacetime is inextendible among continuous, strongly causal, causally plain, regular spacetimes (§5).
- [V] Compared with Graf–Ling and Galloway–Ling–Sbierski, the known results are "slightly stronger" when restricted to spacetimes. This paper does not need global hyperbolicity and allows a low-regularity original space and non-manifold extensions (§6).
- [V] Only one property of the extension is used: an exit maximiser between timelike-related points is timelike (§6).
- [V] Open: whether (TC) characterises timelike geodesic completeness in LLS (§5).

## Verified quotes
> "In fact, the extensions that we consider need not even be manifolds."

> "Note that lower semicontinuity of τ implies that I ± (x) is open, for any x ∈ X."

> "y ∈ Ωx we have I ± (y) ∩ Ωx"

> "It is a direct analogue of [Sbi18, Lemma 2.17])."

> "In this space maximal curves branch"

> "Specifically, the extension cannot have bounded upper causal curvature."

> "inextendible in the class of continuous, strongly causal and causally plain spacetimes that are regular."

> "Thus, their result is slightly stronger than ours when restricted to spacetimes"

> "However, our approach does not need the original spacetime to be globally hyperbolic"

> "all that is needed is that a maximal causal curve γ that is contained in the original space except for its endpoint (which is on the boundary) is timelike whenever its starting point and endpoint are timelike related in the extension."

> "it is an interesting open question whether one can characterize completeness of timelike geodesics in Lorentzian length spaces via condition (T C)"

## Methods and evidence
- Data / setting: pure mathematics. The setting is the Lorentzian (pre-)length spaces of KS18 ([[kunzinger2018lorentzian]]); applications are smooth and continuous spacetimes.
- Baselines: [BEE96, Prop. 6.16] (geodesic completeness implies inextendibility); Sbierski's Lemma 2.17; Galloway–Ling–Sbierski; Graf–Ling.
- Evaluation (metrics, seeds, variance, held-out?): full proofs and one explicit non-manifold example.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- Extensions must be *regular* Lorentzian length spaces, and for spacetimes also causally plain. The paper concedes that it is weaker than Galloway–Ling–Sbierski's C⁰ result on spacetimes.
- Def 3.1(ii) demands a metric isometry d → d̃, which is stronger than a homeomorphism. [[beran2026curvature]] relaxes this to a homeomorphism preserving ℓ.
- Thm 5.4 needs local timelike geodesic connectedness, flagged as unnatural by [[beran2026curvature]].
- Nothing on singular lines, conical or BTZ. The axioms forbid points with empty I^- (localisability (ii)).

## Contradictions and tensions
- [[sbierski2015c]], [[galloway2017timelike]]: **confirmed.** Lemma 3.8 is their Lemma 2.17 / Lemma 3.2. The proof again uses only connectedness, openness and local non-emptiness of I^±. This independently supports round 1's "locating the extension is purely causal" claim.
- [[galloway2017timelike]]: the paper reinterprets it as follows. Global hyperbolicity plus timelike completeness make exit maximisers timelike, and that alone gives C⁰-inextendibility.
- [[beran2026curvature]]: Thm 5.4's hypothesis "locally timelike geodesically connected" is needed after a correction to KS18. Beran et al. replace upper bounds with lower curvature bounds and drop that hypothesis.
- [[kunzinger2018lorentzian]]: depends on KS18's Prop 4.15 (via Thm 5.4), which was later corrected (as reported by [[beran2026curvature]]).

## Open questions
- Is reg(E_α) ⊂ E_α, or a singular flat spacetime inside a larger one, ever an extension in the sense of Def 3.1? E_α itself is a regular LLS (see [[alexander2023generalized]]), but reg(E_α) is not (TC), so the theorem is silent.
- Can (TC) be replaced by an order-theoretic surrogate, so that Thm 5.3 lives in ETT? One candidate: "every inextendible chronal curve has unbounded measure-time" using ETT's admissible measures.

## Leads for next round
- term: property (TC); regular Lorentzian length space; locally timelike geodesically connected; future/past boundary of an extension; non-manifold extension.
- cited: [GL17] Galloway–Ling, "Some remarks on the C⁰-(in)extendibility of spacetimes" (AHP 2017; future one-connectedness + future divergence ⇒ empty future boundary, Thm 2.5); [GL18] Graf–Ling, "Maximizers in Lipschitz spacetimes are either timelike or null" (CQG 2018); [GT87] Geroch–Traschen (already plan #2).
- author: J. D. E. Grant; C. Sämann; E. Ling.
