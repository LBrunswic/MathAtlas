# geroch1987strings — Strings and other distributional sources in general relativity

Robert Geroch, Jennie Traschen
Phys. Rev. D 36 (1987) 1017–1031 · 1987 · doi:10.1103/physrevd.36.1017 · *no archived PDF: paywalled (APS). A web search (2026-11-20) found no open copy; read via abstract (KB record) and secondary accounts in vickers2000generalized, hormann2015conical, sbierski2020holonomy, grant2018inextendibility (all archived in `text/`)*

**Tier: T3** — capped: secondary_only (primary text unread). Absent the cap it would be T1 (PRD, 485 citations, the standard reference for the class; its exclusion of strings is repeated by every secondary source in the KB).
**Relevance: 3** — Q3 (the weak-solution class for Einstein's equations and why conical lines are excluded), Q2 (what "generalized Einstein equations" can mean for E_α/E_0).
**Read:** abstract only + four secondary accounts ⇒ capped at T3

## Summary
Known only second-hand. The paper isolates a class of metrics ("regular" / "gt-regular") for which the curvature tensor is a well-defined distribution, shows that thin shells can be described in this class but point particles and strings cannot, and quantifies the errors of naive mass-per-length and radiation computations for cosmic strings. The class, as reported by secondary sources, is: g and g⁻¹ locally bounded, ∂g ∈ L²_loc (Sbierski uses the stronger g ∈ C⁰, ∂g ∈ L²_loc); then products of Christoffel symbols are L¹_loc and the curvature is a distribution. Its key structural consequence is that distributional curvature in this class can be concentrated at most on a codimension-one submanifold.

## Key points
- [S: abstract, KB record] A class of metrics with distributionally well-defined curvature is isolated; shells are in it, "neither point particles nor strings" are.
- [S: abstract] Errors in determinations of a cosmic string's mass per unit length and in radiation calculations are estimated.
- [S: vickers2000generalized §1] In the GT class, distributional curvature must have support on a submanifold of codimension at most one; the cone (codimension-2 support) is therefore excluded.
- [S: hormann2015conical §1, after Steinbauer–Vickers] gt-regular = components in L^∞_loc ∩ H¹_loc; the conical metric narrowly fails (∂g ∈ L¹_loc \ L²_loc, Lemma 1.1 there).
- [S: sbierski2020holonomy §1.1, fn 1] The class g ∈ C⁰, ∂g ∈ L²_loc is "widely" taken as the roughest class admitting weak solutions with good stability (approximation theorems in GT); GT themselves allow g, g⁻¹ ∈ L^∞_loc, which Sbierski says poses challenges for causality theory. Requiring only that Christoffel products be L¹_loc (GT, Garfinkle) is wider but loses stability.
- [S: grant2018inextendibility intro] "Geroch–Traschen metrics" = Christoffel symbols L²_loc, curvature a distribution.
- [P — reader inference, not GT's text] Why codimension matters: a defect metric that is homogeneous of degree 0 transversally to a codimension-k set has ∂g ~ 1/r, and ∫₀ r⁻²·r^{k−1} dr is finite iff k ≥ 3. For k = 2 (strings; ETT's E_α and E_0 lines) it diverges logarithmically, so ∂g ∉ L²_loc; for a thin shell (k = 1) the metric is continuous with only a jump in ∂g, which is bounded. The quantitative k = 2 computation is Hörmann's Lemma 1.1 ([[hormann2015conical]]), not GT's.

## Verified quotes
<!-- Empty on purpose: no archived text of geroch1987strings exists in text/, so verify-quotes has nothing to check against. Verbatim secondary statements are quoted (and verified) in vickers2000generalized and hormann2015conical. -->

## Methods and evidence
- Unknown first-hand. Secondary sources indicate: a definition of the regular class, a stability/approximation theorem (curvature of smooth approximants converges), and a codimension theorem.
- Artifacts: n/a.

## Limitations and caveats
- Primary text not read; every claim is [S].
- The exact hypotheses (C⁰ vs L^∞ for g; non-degeneracy uniformity) are reported differently by Sbierski (C⁰ "in some references weakened to L^∞, cf. [16]") and by Hörmann (L^∞_loc ∩ H¹_loc). Which one GT state is not settled here.
- vickers2000generalized cites the paper as volume 38; the DOI gives volume 36.

## Contradictions and tensions
- None of substance among secondary sources: [[vickers2000generalized]], [[hormann2015conical]], [[sbierski2020holonomy]], [[grant2018inextendibility]] all agree strings are outside the class. Minor difference: C⁰ vs L^∞ for g (Sbierski fn 1 vs Hörmann).
- Tension with the round-1 framing of Sbierski's program [[sbierski2020holonomy]]: if "inextendible as a weak solution" means inextendible within the GT class, then conical/BTZ lines are *automatically* non-solutions at the line — they cannot be used as GT-class extensions at all. A conical spacetime is a weak solution only in Colombeau/regularized senses ([[vickers2000generalized]]).

## Open questions
- Exact statement of the GT codimension theorem and of their regularity class (needs the primary text or Steinbauer–Vickers 2009 / gr-qc/0603078).
- Does Garfinkle's widened class (gr-qc/9906053) admit strings? The search snippet says it still represents shells but not thin strings — unverified.

## Relevance to the questions
- (i) Entirely analytic: Sobolev regularity of a metric in coordinates; nothing causal.
- (ii) ETT: for E_α (conical) and E_0 (BTZ) lines the "generalized Einstein equation" cannot be GT-distributional: the curvature is a delta on a codimension-2 set, outside GT. Options for a generalized Einstein equation compatible with ETT: (a) Colombeau association (Clarke–Vickers–Wilson; [[vickers2000generalized]]), giving T ~ −2π(1−A)δ⁽²⁾; (b) the geometric (G,X)-route — flat regular part plus prescribed holonomy (rotation angle for E_α, parabolic for E_0) on the singular line, i.e. vacuum away from the line and the source encoded as holonomy, which is what ETT/lean-gx already carry. Option (b) is the natural "weak Einstein equation" for ETT: it needs no metric regularity at the line at all.
- (iii) No direct Lean target. Indirect: lean-gx could state "the singular line's holonomy class determines the delta-source mass" only after a distributional framework exists — not a near-term target.

## Leads for next round
- cited (via secondaries): Steinbauer–Vickers, "On the Geroch–Traschen class of metrics", CQG 26 (2009) 065001; Steinbauer–Vickers review, arXiv gr-qc/0603078 (open, covers GT in detail); Garfinkle, "Metrics with distributional curvature", arXiv gr-qc/9906053; LeFloch–Mardare 2007 (LM07 in grant2018)
- term: gt-regular; regular metric (GT sense); distributional curvature; thin shell; codimension of curvature support
