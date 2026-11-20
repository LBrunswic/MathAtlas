# beran2026curvature — Curvature bounds, regularity and inextendibility of spacetimes

Tobias Beran, John Harvey, Clemens Sämann
Classical and Quantum Gravity 2026 · doi:10.1088/1361-6382/ae82af · arXiv:2603.20802 (v2, 25 Jun 2026, read) · `pdf/beran2026curvature.pdf`

**Tier: T2** — Peer-reviewed (CQG; the acknowledgments thank anonymous reviewers). The proofs are short and complete. The paper is too recent for independent confirmation. Its claims match its theorems: the abstract's "significantly strengthening [GKS19]" corresponds to dropping local timelike geodesic connectedness and replacing upper bounds by lower bounds.
**Relevance: 2** — Q2: it tightens the synthetic inextendibility programme. Q3: it shows precisely which hypotheses BTZ lines violate. There is no direct application to flat conical spacetimes.
**Read:** full text.

## Summary
The paper works in Lorentzian pre-length spaces in McCann's style:
- an extended time separation ℓ with the reverse triangle inequality;
- ≪ and ≤ read off from ℓ;
- a metrizable topology finer than the chronological topology, so I^± is open by definition.

It proves that a **lower** curvature bound forces regularity, meaning maximisers are timelike or null, under mild causality assumptions. Thm 3.1 covers strict causal four-point CCBB with local distinguishing. Thm 3.2 and Cor 3.3 cover timelike and non-strict four-point conditions; they also need "not locally timelike isolating" and continuity of τ. Thm 3.4 covers triangle comparison with local distinguishing.

It then generalises the extension notion of [[grant2018inextendibility]] to a homeomorphism onto a proper open subset that preserves ℓ (Def 4.1). TC implies inextendibility as a regular, weakly normal pre-length space without spacelike boundary (Thm 4.2). Hence a locally distinguishing TC space has no locally distinguishing, weakly normal extension with causal curvature bounded below (Thm 4.4). This applies to all strongly causal, timelike-complete spacetimes. The paper also reports that a correction to KS18 Prop. 4.15 makes the main result of [GKS19] depend on local timelike geodesic connectedness.

## Relevance to the questions
- **(i) Metric versus causal.**
  - *Causal and topological:*
    - the hypotheses local distinguishing, not locally timelike isolating, and no spacelike boundary;
    - the first part of the proof of Thm 4.2: pick r̃ ∈ I^+(p̃) in a weakly normal neighbourhood, so that I^-(r̃) ∩ Ũ is an open neighbourhood of p̃, then find a curve leaving ι(X). This is again Sbierski's Lemma 2.17 step, now with one-sided I^+.
  - *Metric (time-separation):* the TC condition (length), maximisers, regularity and the curvature bounds.
  - *No smooth structure anywhere.* Not even a fixed metric d is needed, only a metrizable topology.
- **(ii) Flat spacetimes with conical lines.**
  - The theorems need the *original* space to be TC (timelike complete). Singular flat spacetimes are generally not: in E_α the radial timelike geodesics hit the line in finite time [reader inference, unverified]. So Thm 4.2 and Thm 4.4 do not say anything about extending reg(E_α) or an E_α-manifold.
  - The regularity half does apply. E_α with α ≤ 2π has timelike curvature bounded below by 0 (by inference from [[alexander2023generalized]]) and is locally distinguishing, so it is regular by Thm 3.4: no maximiser through the massive line mixes null and timelike pieces [reader inference].
  - **BTZ E_0 fails exactly the paper's hypotheses.**
    - A BTZ point has I^-(p) = ∅, so E_0 is locally timelike isolating.
    - An E_{≥0}-manifold with an extreme BTZ white hole is not past distinguishing (ETT Def. "causal structure at a BTZ point").
    - Both regularity theorems and the inextendibility theorems therefore exclude BTZ lines.
  - The paper's Example 3.5 is a non-regular space built from two Minkowski half-spaces joined by a null strip. It has curvature bounded above and below by 0 in the timelike and triangle senses, but fails the strict causal conditions. It is the closest thing in the KB to a flat space with a lightlike singular locus. It is a useful comparison for E_0, though not the same object.
  - What ETT adds: none of this involves Cauchy surfaces or developments. ETT's one-sided K^± (K^- of a BTZ point is J^- \ {p}) is precisely the tool for the one-sided non-isolation that this paper must assume away.
- **(iii) Lean candidate.**
  - The extension notion of Def 4.1 (connected X̃, homeomorphism onto a proper open subset, preserving the relation) is purely order-topological, once ℓ is replaced by the pair (≤, ≪). Together with "not locally timelike isolating on one side", it gives a cleaner hypothesis for `boundary_nonempty_of_extension` (see [[grant2018inextendibility]]).
  - A second target: "a locally distinguishing space has no spacelike boundary point". The remark after Def 4.1 says that distinguishing spaces allow at most one spacelike boundary point and that non-isolation excludes it. The statement is pure order theory and small.

## Key points
- [V] A Lorentzian pre-length space is (X, ℓ) with a metrizable topology finer than the chronological topology (Def 2.1). [P] I^±(x) are therefore open by definition (§2).
- [V] "Not locally timelike isolating": both I^+(x) ∩ U and I^-(x) ∩ U are non-empty for every neighbourhood U (§2).
- [V] The main result of [GKS19] depends, after a correction to KS18 Prop. 4.15, on the "rather unnatural" local timelike geodesic connectedness (§1).
- [V] Thm 3.4: locally distinguishing plus TLCBB (triangle comparison) implies regularity (§3). [P] Thm 3.1: the same with strict causal four-point CCBB. Thm 3.2: timelike four-point TLCBB, also assuming not locally timelike isolating and τ continuous.
- [V] Example 3.5: two Minkowski half-spaces joined by a null strip. It is non-regular, yet has timelike curvature bounded above and below by 0 in the timelike and triangle senses (§3). [P] It is not distinguishing and is locally isolating.
- [P] Def 4.1: an extension is a homeomorphism onto a proper open subset preserving ℓ. No metric isometry is required (§4).
- [V] Thm 4.2: TC implies inextendibility as a regular, weakly normal pre-length space without spacelike boundary (§4).
- [V] Thm 4.4: TC plus local distinguishing implies there is no locally distinguishing, weakly normal extension with CCBB (§4). [P] This applies to all strongly causal, timelike-complete spacetimes.
- [V] The authors state the synthetic programme of [GKS19] had no follow-up until this paper (§1).

## Verified quotes
> "implies that the main result of [GKS19] depends on the rather unnatural assumption of local timelike geodesic connectedness."

> "If X is given a metrizable topology that is finer than the chronological one, then (X, ℓ) is a Lorentzian pre-length space."

> "We call X not locally timelike isolating if for all neighbourhoods of all x ∈ X, both I + (x) ∩ U and I − (x) ∩ U are non-empty"

> "Theorem 3.4. A locally distinguishing Lorentzian pre-length space (X, ℓ) with TLCBB in the triangle comparison sense is regular."

> "Hence X has timelike curvature bounded above and below by 0 in the sense of timelike and causal triangle comparison and four-point comparison"

> "Then X is inextendible as a regular and weakly normal Lorentzian pre-length space without spacelike boundary."

> "A locally distinguishing Lorentzian pre-length space satisfying the TC-condition cannot be extended as a locally distinguishing weakly normal Lorentzian pre-length space having causal curvature bounded below"

> "A proof-of-concept of this was established in [GKS19] but there has not been any follow-up since then."

## Methods and evidence
- Data / setting: pure mathematics in Lorentzian pre-length spaces with an extended time separation (McCann). The curvature notions are triangle comparison and the four-point conditions of Beran–Kunzinger–Rott [BKR24].
- Baselines: [GKS19] = [[grant2018inextendibility]]; KS18 = [[kunzinger2018lorentzian]] (Prop. 4.15, corrected).
- Evaluation (metrics, seeds, variance, held-out?): proofs, plus one example showing that the strict conditions are needed.
- Artifacts (code / data / weights): none.

## Limitations and caveats
- The original space must satisfy TC. Results about incomplete originals, such as Schwarzschild or flat spaces with conical lines, are not addressed.
- The correction to KS18 Prop. 4.15 is cited to an updated arXiv version and not restated, so I could not check its content here.
- Example 3.5 is described in prose with a figure; claims about it are graded [P] except for the quoted curvature sentence.

## Contradictions and tensions
- [[grant2018inextendibility]]: **weakens** its Thm 5.4 (the curvature-blow-up result). That theorem now rests on the local timelike geodesic connectedness hypothesis. Thm 5.3 (TC ⇒ inextendible as regular LLS) stands and is generalised here (Thm 4.2, Cor 4.3).
- [[kunzinger2018lorentzian]]: reports that KS18 Prop. 4.15 was corrected after publication. Round 1's note on KS18 should carry that caveat.
- [[galloway2017timelike]], [[sbierski2015c]]: same first step (an exit curve from a boundary point), now with only one-sided timelike non-isolation in the proof. This confirms round 1's "locating the extension is causal".

## Open questions
- Is there a TC-free version, for example for spaces whose incomplete timelike geodesics all end on a singular line with bounded synthetic curvature, as in E_α? This would be the natural statement for singular flat spacetimes.
- Does a one-sided version of Thm 3.1 survive at BTZ points (future non-isolated, past isolated)?

## Leads for next round
- term: weakly normal neighbourhood; not locally timelike isolating; locally distinguishing; spacelike boundary [MS24]; strict causal four-point condition.
- cited: [BKR24] Beran–Kunzinger–Rott, On curvature bounds in Lorentzian length spaces (JLMS 2024); [BKOR25] equivalence of smooth and synthetic timelike sectional bounds (PAMS 2025); [MS24] Minguzzi–Suhr, bounded Lorentzian metric spaces; [Sbi26], [Sbi24], [GvdBS24] (newer Sbierski / boundary-extension papers); [Rot23] Rott (not locally timelike isolating).
- author: T. Beran; J. Harvey; F. Rott.
