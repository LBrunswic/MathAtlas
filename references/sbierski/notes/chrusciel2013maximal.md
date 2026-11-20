# chrusciel2013maximal — On maximal globally hyperbolic vacuum space-times

Piotr T. Chruściel
J. Fixed Point Theory Appl. (2013) · arXiv:1112.5779 (v2), doi:10.1007/s11784-013-0141-4 · `pdf/chrusciel2013maximal.pdf`

**Tier: T2** — peer-reviewed. The abstract part (Thm 2.2, Thm 3.1, Prop 3.2) is proved in full. The concrete Theorem 1.1 rests on checking hypotheses H1–A3, some of them by citation, notably the Planchon–Rodnianski uniqueness argument, "not available at the time of publication". It is cited as the low-regularity CBG reference by [[sbierski2013existence]] and [[chrusciel2012lorentzian]], but this KB has no independent re-proof.
**Relevance: 3** — Q2 and Q4: it is the direct comparator for Sbierski's Zorn-free CBG and for lean-causal's abstract CBG. It is itself stated over an abstract structure class W with a rigidity axiom.
**Read:** full text, §§1–3.1 in detail. §3.2 (Prop 3.7, Sobolev regularity of isometries) and the appendices were skimmed.

## Summary
The paper proves existence and uniqueness of the maximal globally hyperbolic vacuum development for data (γ, K) ∈ H^s_loc × H^{s-1}_loc with integer s > n/2 + 1, closing the gap between the smooth CBG theorem and the Sobolev local theory. The argument has two layers.
1. **An abstract existence theorem.** Thm 2.2: for any "chain-inheriting" class W of C¹ Lorentzian manifolds with a compatible embedding of S that satisfies the rigidity axiom (2.1), "an isometry that is the identity on a compatible hypersurface is the identity", maximal elements exist by Kuratowski–Zorn. The collection is made a set through the Whitney embedding.
2. **An abstract uniqueness theorem.** Thm 3.1 and Prop 3.2, under hypotheses H1, H2 and A0–A3: local existence, local uniqueness, rigidity, regularity gain of C¹ isometries, solvability of the linear wave equation, and invariance of the class under pull-back.

Uniqueness again uses Zorn, this time on pairs (U, Ψ_U). Its crux is Lemma 3.3: the gluing of M₁ and M₂ along a maximal isometry is Hausdorff. The proof picks a minimal non-Hausdorff point, again by Zorn, and extends the isometry past it in wave coordinates. The C⁰ causality theory of Chruściel–Grant replaces the C² tools. Where a causal curve can no longer be deformed to a timelike one, the argument uses a nested sequence of smooth metrics ĝ_i ≻ g with wider cones.

## Key points
- [V] Main result: existence and uniqueness of the MGHD for H^s × H^{s-1} vacuum data, N ∋ s > n/2+1, with uniqueness up to isometry within the H^s_{space,loc} class (Abstract; Thm 1.1).
- [V] Global hyperbolicity means that every inextendible causal curve meets i(S) exactly once (§1).
- [V] Previous proofs need C² for causality theory, and C^{1,1} wherever geodesics are used. The three causal facts needed are (1) accumulation curves, (2) deformation of a non-null causal curve to a timelike one, and (3) null generators of ∂D_J. Point (2) fails for C⁰ metrics, so (3) must be replaced (§1).
- [V] Thm 2.2 is abstract over a property W. Its hypotheses are (a) chain-inheritance, meaning that unions of chains stay in W, and (b) the rigidity axiom (2.1). Its conclusion is a W-inextendible development. Existence is by Kuratowski–Zorn (§2, Thm 2.2 and proof).
- [V] Size bound: C¹ is needed only because the Whitney embedding turns "all manifolds" into a set. The author does not know whether C¹ is necessary (§2, Remark 2.3.1).
- [V] Without global hyperbolicity, maximal W-manifolds need not be unique and may depend on W. For Robinson–Trautman spacetimes the threshold lies between C^{117,α} and C^{123} (§2, Remark 2.3.3).
- [P] Rigidity is proved in two regimes. For C^{1,1} metrics it is an ODE argument along rays, with three cases: S open, a point with Ψ_* = id, or a time-orientation-preserving hypersurface (Prop 2.4). For Lipschitz metrics in wave coordinates it is an energy estimate on domains of dependence plus an open–closed argument in a Cauchy time function (Prop 2.6, Lemma 2.8). Remark 2.5 says every condition in Prop 2.4 is necessary.
- [V] Role of each hypothesis: A0 (rigidity) gives existence; A1 (C¹ isometries gain regularity) lets isometries be extended in the uniqueness proof (§3.1).
- [P] Prop 3.2 (the key step): if M₂ is maximal and an isometry from a GH neighbourhood of S₁ exists, it extends to an injective isometry M₁ → M₂. Zorn applied to the family of pairs (U, Ψ_U) ordered by extension gives a maximal pair (§3.1).
- [V] Lemma 3.3: for a maximal pair, (M₁ ⊔ M₂)/Ψ_O is Hausdorff, hence a manifold (§3.1).
- [P] Proof of Lemma 3.3. Non-Hausdorff points lie in ∂O and form a closed set H. Zorn on causal paths gives p ∈ H with J^-(p) ∩ H ∩ I^+(S₁) = {p} (3.5). An argument using nested smooth metrics ĝ_i ≻ g gives the localisation (3.6). The isometry is then extended across p by solving □y = 0 with matched data (hypotheses A1, A2, H2), and injectivity is checked through achronality of Ψ(S₁). The steps are purely topological or causal except the extension, which is PDE (§3.1, pp. 13–18).
- [V] Lemma 3.5 needs Ǐ^-, built from locally uniformly timelike curves. Whether the same inclusion holds with I^- for merely continuous metrics is left open (§3.1, Remark 3.6).
- [P] With Hausdorffness in hand, the glued space has S₂ as Cauchy surface by a pure inextendible-curve argument. Maximality of M₂ then forces M₁ = Ũ (§3.1, end of proof of Prop 3.2).
- [V] The abstract theorem covers real s > n/2, provided H1–A3 hold (Thm 3.1). The paper expects extension to any quasilinear system of wave equations (§1).

## Verified quotes
> "We prove existence and uniqueness of maximal global hyperbolic developments of vacuum general relativistic initial data sets with initial data"

> "To avoid ambiguities, global hyperbolicity here is the requirement that every inextendible causal curve meets"

> "It is not obvious, but proved in [13] (see also [16]), that point (1) remains true for continuous metrics, but that point (2) is wrong for continuous metrics; then the usual arguments addressing (3) fail."

> "the only isometry of a W -manifold (M , g) which is the identity on a W -compatible hypersurface is the identity map."

> "The C 1 -differentiability threshold for S and M cannot be weakened in the proof below, since we are using the Whitney embedding theorem to turn the collection of manifolds into a set."

> "The maximal manifolds (Me, g̃) need not be unique, and may depend upon W ."

> "Hypothesis A0 is used in the proof of existence of maximal developments. The hypothesis A1 is used to extend isometries in the proof of uniqueness of maximal globally hyperbolic developments."

> "is Hausdorff, hence a manifold."

> "We do not know whether the inclusion"

> "a different line of thought is needed."

> "It is conceivable that the result generalises to more general classes of initial data for which local existence and uniqueness of solutions holds"

## Methods and evidence
- Data / setting: vacuum Einstein, n ≥ 3. The manifolds are C¹, Hausdorff, paracompact and connected, with metrics in H^s_{space,loc} (Def 2.1).
- Baselines: Choquet-Bruhat–Geroch 1969 (smooth, geodesics); Chruściel's earlier Killing-orbit proof [9] (smooth), adapted here.
- Evaluation: mathematical proof. Black boxes: local existence [20], the Planchon–Rodnianski uniqueness argument [30] (unavailable at publication; see [12, §4.3]), Chruściel–Grant C⁰ causality [13], and Fathi–Siconolfi smooth time functions [16].
- Artifacts: none.

## Limitations and caveats
- **Zorn is used three times**: Thm 2.2, the maximal pair in Prop 3.2, and the maximal causal path giving the minimal non-Hausdorff point in Lemma 3.3. The paper says nothing about the set-theoretic strength needed.
- The concrete theorem needs integer s. Real s is reduced to checking H1–A3, which is not done.
- Rigidity in the Lipschitz regime requires wave coordinates and an energy estimate, so it is PDE-specific, not geometric.
- The non-Hausdorff-point argument uses smooth wider metrics ĝ_i ≻ g. This tool exists because the space is a manifold with a continuous cone field; it is unavailable on a bare topological space.
- The inclusion question of Remark 3.6 is left open for C⁰ metrics, which is why the argument works with Ǐ.
- The abstract matches the theorem. No overstatement.

## Contradictions and tensions
- vs [[sbierski2013existence]], **complementary, not contradictory**. Sbierski removes Zorn but stays at C^∞ (C² asserted). Chruściel lowers regularity to H^s and C⁰ causality but keeps Zorn. Both put the crux in the same place: Hausdorffness of the gluing along a maximal common piece, i.e. "no corresponding boundary points" for Sbierski and "no non-Hausdorff pair" for Chruściel. **Confirms** the round-1 consensus that Hausdorffness is the core.
- Both extend the isometry past a boundary point with local, metric-specific tools: exponential maps and a time-separation slice for Sbierski, harmonic coordinates and the wave equation for Chruściel. **Confirms** round-1 Q2: this step is the non-order-theoretic layer in both.
- Both control size without proper classes: Sbierski glues only developments living in Σ×R; Chruściel uses Whitney embeddings into R^ℓ. **Confirms** lean-causal's CBG-DESIGN claim that a size bound is an essential, separate input.
- [[chrusciel2012lorentzian]]: this paper is the application that C&G was written for (§1). The failure of curve deformation and Remark 3.6's Ǐ vs I match C&G's bubbling and Ǐ, and the round-1 consensus "below Lipschitz use J and Ǐ".
- [[eperon2018predictability]]: Remark 2.3.3 (maximal W-developments non-unique without global hyperbolicity, and W-dependent) is the same phenomenon class as ERS19's non-unique MGHDs, there for subluminal systems. Here W-dependence is a regularity effect.

## Open questions
- Can Chruściel's Lemma 3.3 be dezornified the way Sbierski's is? The minimal non-Hausdorff point (3.5) needs a maximal causal path. Sbierski instead works with an arbitrary point of the boundary that is suitably "spacelike". The text does not say whether the minimal point can be dropped.
- Is "ĝ_i ≻ g" replaceable by an order-theoretic hypothesis, such as a nested family of causalities K_i decreasing to K with D_{K_i}(S) increasing? That would carry the argument to ETT.

## Relevance to the questions
**(i) Smooth vs order-topological.** The architecture is abstract. Thm 2.2 needs only chain-inheritance, rigidity (2.1) and a size bound (Whitney, needing C¹). Prop 3.2 is "Zorn on pairs + Hausdorff gluing + Cauchy-surface check". The Cauchy-surface check and the closedness of the non-Hausdorff set are purely topological and causal. Four inputs are metric or PDE:
- the rigidity proofs (ODE/geodesic for C^{1,1}; energy estimates in wave coordinates for Lipschitz);
- extension across a boundary point (A1, A2, H2);
- the wider smooth metrics ĝ_i ≻ g used to get (3.6);
- the existence of a smooth Cauchy time function (Fathi–Siconolfi [16]), used in Prop 2.6.

**(ii) ETT.** Thm 2.2 is already an abstract CBG-existence statement over a class W with a rigidity axiom, the shape of lean-causal's "CBG over an abstract rigid geometry". Compared with lean-causal:
- lean-causal follows Sbierski's Zorn-free order;
- Chruściel names rigidity as an explicit **axiom** (2.1), and so does lean-causal;
- his size bound (Whitney, C¹) is replaced in lean-causal by a size bound of its own;
- his uniqueness needs the extra axiom A1 (isometries are as regular as the metric) and a local extension mechanism.

In a rigid (G,X)-geometry, extension across a boundary point is analytic continuation of a chart, so A1 and A2 are replaced by rigidity of (G,X)-maps. Remark 2.3.3 (W-dependence) supports ETT's choice to fix the geometry first. Remark 3.6 and the failure of curve deformation for C⁰ metrics support ETT's K± in place of I±.

**(iii) Formalization candidate.** "Abstract maximal development (existence)": given a type of developments with an extension preorder, a rigidity axiom (an endomorphism fixing the initial surface is the identity), a size bound (every development is isomorphic to one carried by a fixed set), and closure under directed unions, a maximal development exists. Partial-order antisymmetry follows from rigidity, as in the proof of Thm 2.2. lean-causal can state this Zorn version as a sanity theorem next to its Zorn-free CBG, so that the two hypothesis sets can be compared. A second target is the purely topological half of Lemma 3.3: the non-Hausdorff set of (M₁ ⊔ M₂)/Ψ_O is closed and lies in ∂O. This is shared with round-1 Q4 item 1.

## Leads for next round
- term: chain-inheriting property; H^s_{space,loc} metric; non-Hausdorff pair; Ǐ^± (locally uniformly timelike); wider metric ĝ ≻ g.
- cited: [9] Chruściel, "On completeness of orbits of Killing vector fields" (the template proof); [12] Chruściel, Lectures/notes §4.3 (Planchon–Rodnianski argument); [13] Chruściel–Grant (in KB); [16] Fathi–Siconolfi, "On smooth time functions"; [14] Chruściel, Robinson–Trautman extensions (W-dependence of maximal extensions); [7] Choquet-Bruhat–Geroch 1969.
- author: P. T. Chruściel; Planchon–Rodnianski.
