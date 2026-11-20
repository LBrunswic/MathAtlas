# grant2019future — The future is not always open

James D. E. Grant, Michael Kunzinger, Clemens Sämann, Roland Steinbauer
Letters in Mathematical Physics 2019 · doi:10.1007/s11005-019-01213-8 · arXiv:1901.07996 (v2 read) · `pdf/grant2019future.pdf`

**Tier: T1** — Peer-reviewed (LMP). It answers open questions of [[chrusciel2012lorentzian]] with explicit, checkable 2D metrics. It agrees with Minguzzi's push-up/bubble equivalence (Remark 2.13, [[minguzzi2019causality]]). It is cited by ETT itself as the reason ≪-openness is a stated limitation of ETT.
**Relevance: 3** — Q2 (adversarial): it decides exactly when the "causal once I± is open" steps of round 1 are available. Q4: it determines which relation lean-causal should take as ≪.
**Read:** full text.

## Summary
For a continuous metric g, the paper compares chronological futures defined with absolutely continuous, locally Lipschitz, piecewise C¹ or smooth timelike curves. Causal curves of every class are equivalent: an AC causal curve has a Lipschitz reparametrisation (Lemma 2.9). Timelike curves differ.
- With piecewise C¹ or smooth curves, I^± equals Ǐ^± (the future of the narrower smooth metrics) and is **always open** (Lemma 2.7).
- With Lipschitz curves, I^±(p) can fail to be open (Example 3.1, an α-Hölder metric in 1+1 dimensions).
- The two can differ even when every I^± is open (Example 3.2).

The paper characterises openness, for chronological spacetimes, by achronality of ∂I^± (Thm 2.10). It shows push-up ⇔ no exterior bubbling (Thm 2.12), and that the curve classes agree iff there is no interior bubbling (Thm 2.15). Causal plainness is the watershed: it is equivalent to no bubbling of either kind (Cor 2.16), and Lipschitz metrics are causally plain.

## Relevance to the questions
- **(i) Metric versus causal.** Everything here is about a C⁰ metric g, but the dichotomy is about *which curve class defines ≪*. The key facts:
  - Ǐ^± (from piecewise C¹ curves, or from smooth metrics with narrower cones) is open for *every* continuous metric.
  - The Lipschitz I^± is what synthetic theories must use, because limit curves and metric spaces have no C¹ curves. It is open iff ∂I^± is achronal (Thm 2.10).
  - In the counterexamples the failure is localised on a line {x = 0}, where the metric is only Hölder. A Lipschitz-timelike curve reaches that line with a null tangent at one point.
- **(ii) Effect on round 1 and on ETT.**
  1. **Sbierski's papers use piecewise-smooth timelike curves.** The paper names [Sbi18a] as a work using Def 2.2 for continuous metrics, and [[sbierski2015c]] Prop 2.6 is exactly the openness of that I^±. So round 1's "causal once I± is open" steps are *unaffected* for Sbierski's own definitions: his I^± is always open.
  2. The hypothesis becomes non-trivial only if ≪ is defined by Lipschitz curves, as in LLS and Minguzzi's cone structures. Even then it holds for causally plain metrics (Lipschitz metrics, and warped products with continuous warping function, [[alexander2023generalized]]).
  3. **ETT** keeps ≪ open as an *axiom* and cites this paper as the limitation. ETT's K^± does **not** repair a non-open I^±; it repairs the failure of push-up. But the axiom costs little for continuous spacetimes. One can always take ≪ := Ǐ (open, by Lemma 2.7, and computed locally in each open set U) and ≤ := J_L (Lipschitz causal curves).
     - This pair is an ETT causality [reader inference, unverified: transitivity, ≪ ⊂ ≤ and the sheaf property are immediate; locality of Ǐ(p, U) is stated before Lemma 2.7].
     - The Lipschitz-only points of Examples 3.1 and 3.2, I \ Ǐ, then become a *failure of causal plainness* in ETT's sense (Int J ⊄ closure of Ǐ in Example 3.2). That is exactly the situation K^± was designed for.
  4. Net effect: ETT's design (open ≪ chosen as Ǐ, push-up dropped and replaced by K^±) absorbs every pathology in this paper. LLS's design (Lipschitz ≪ plus lower semicontinuous τ, which forces I^± open) instead *excludes* Example 3.1 from the theory.
- **(iii) Lean candidates.**
  - (a) `isOpen_I_iff_achronal_boundary` (Thm 2.10, (i) ⇔ (ii), chronological case). The direction (ii) ⇒ (i) is pure order topology. The proof: q ∈ I^+(p) ∩ ∂I^+(p) and p ∈ ∂I^+(p) are chronologically related, which contradicts achronality. It is statable for any topological space with a transitive irreflexive relation whose I^+(p) has p in its closure.
  - (b) A design note for lean-causal rather than a theorem: document that a continuous spacetime gives an ETT causality via (Ǐ, J_L). Without that, the "≪ open" axiom looks restrictive when it is not.

## Key points
- [V] Lipschitz-defined chronological futures may be non-open and may differ from the piecewise-C¹ ones (Abstract; Example 3.1).
- [P] Lemma 2.7: Ǐ^±(p) = I^±_{C^∞}(p) = I^±_{C¹pw}(p) for every continuous spacetime, so the piecewise C¹ future is always open (§2).
- [P] Lemma 2.9: AC causal curves have Lipschitz reparametrisations, so I_AC = I_L and J_AC = J_L (§2).
- [V] Piecewise C¹ timelike curves are used for continuous metrics "e.g. in [Sbi18a]" (§2, before Def 2.2).
- [P] Thm 2.10: for chronological continuous spacetimes, openness of all I^±(p) is equivalent to achronality of each ∂I^±(p), and to ∂I^±(p) being an achronal Lipschitz hypersurface (§2).
- [P] Thm 2.12: push-up ⇔ no exterior bubble ⇔ ∂I^±(p,U) = ∂J^±(p,U) in cylindrical charts (§2). [V] This equivalence was first observed by Minguzzi (Remark 2.13).
- [P] Thm 2.15 / Cor 2.16: the classes of curves agree iff there is no interior bubbling; causally plain ⇔ no interior and no exterior bubbling (§2).
- [V] Example 3.1: an α-Hölder, non-Lipschitz metric. Points with x < 0 have non-open I^+, which contains the t-axis segment above t₁ (§3). [P] Its finite reaching time of the t-axis needs α < 1.
- [P] Example 3.2: every I^+(q) is open, yet I^+(p) ≠ Ǐ^+(p), and Ǐ^+(p) is not dense in I^+(p). So openness does not imply curve-class independence (§3).
- [P] Example 3.3: interior and exterior bubbling coexist at the same point (§3).
- [V] The pathologies persist if one allows C¹ curves that are timelike except at finitely many null points (Remark 3.5).
- [V] Warped products with one-dimensional base are causally plain for continuous warping functions, citing [AGKS19] = [[alexander2023generalized]] (§4).
- [V] Non-open chronological futures are called the most drastic phenomenon (§4).

## Verified quotes
> "chronological futures (defined naturally using locally Lipschitz curves) may be non-open, and may differ from the corresponding sets defined via piecewise C 1 -curves."

> "The definition typically employed in the smooth case (cf. the above references), but sometimes also used for continuous metrics (e.g. in [Sbi18a]), is the following."

> "With this function θ, the metric (3.1) is α-Hölder continuous, but not Lipschitz."

> "We note that the equivalence between the push-up property and the absence of causal bubbles was first observed"

> "In the following section, we provide examples that answer all of these questions in the negative."

> "However, our examples show that in fact all of the pathologies exhibited above would persist if this definition were adopted."

> "are causally plain for continuous, not necessarily Lipschitz, warping functions f , cf. [AGKS19]."

> "The watershed in this chain of implications is the case of causally plain spacetimes."

> "The most drastic of these is the occurrence of non-open chronological futures/pasts."

> "Thus one needs a broad enough framework within which to address the problems highlighted by the examples given in Section 3 of the present paper."

## Methods and evidence
- Data / setting: continuous, time-oriented Lorentzian metrics on smooth manifolds. The examples are 2D metrics of the form (3.1) with a Hölder angle function θ.
- Baselines: [[chrusciel2012lorentzian]] (bubbling, causal plainness, open questions Q1 and Q2); [[minguzzi2019causality]] (cone structures, push-up ⇔ no bubbles).
- Evaluation (metrics, seeds, variance, held-out?): proofs plus explicit ODE computations for the null generators.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- All examples are 1+1 dimensional and non-Lipschitz on a line. No higher-dimensional or physically motivated example is given.
- Openness is characterised only for chronological spacetimes (Thm 2.10).
- The paper does not consider singular lines (conical or BTZ). In ETT's E_α-manifolds, I^± is open by construction (ETT Def. "causal structure of the model spaces"). The BTZ failure, an empty I^-(p), is a different defect from non-openness.

## Contradictions and tensions
- [[sbierski2015c]], [[sbierski2017proof]], [[galloway2017timelike]]: no contradiction. These works define I^± with piecewise-smooth curves, which this paper proves always open (Lemma 2.7). Round 1's "causal once I± is open" holds for their definitions. It becomes a genuine hypothesis only for Lipschitz-defined ≪.
- [[chrusciel2012lorentzian]]: answers its open questions (Q1, Q2) negatively and refines its bubble set into interior and exterior parts.
- [[kunzinger2018lorentzian]], [[grant2018inextendibility]]: LLS make I^± open by axiom (lower semicontinuous τ), so continuous metrics like Example 3.1 are not LLS. The authors note that the causally plain case is the optimal one for LLS.
- [[minguzzi2019causality]]: consistent. Remark 2.13 credits Minguzzi with push-up ⇔ no bubbles in closed cone structures.

## Open questions
- Is (Ǐ, J_L) always an ETT topological spacetime, in particular is ≪ := Ǐ transitive and ≪ ⊂ ≤ with the sheaf property? Does ETT's K^± then recover the Lipschitz I^± of Example 3.2 or something smaller?
- Can a non-open I^± arise in a singular *flat* spacetime, for example from a conical line of angle > 2π? ETT asserts openness for E_{≥0}-manifolds, so presumably not.

## Leads for next round
- term: interior/exterior bubble set; cylindrical neighbourhood; locally uniformly timelike (l.u.t.) curve; Ǐ^±.
- cited: [Lec16] Lechner, master's thesis (Thm 2.3.5, proof of (i)⇒(iv)); [Chr91] Chruściel (first observation of bubbling); [BS18] Bernard–Suhr (Clarke-differential timelike curves, Lem. 2.11), already plan #8.
- author: R. Steinbauer; E. Minguzzi.
