# Research brief: cocycle program literature review (shared by all literature agents)

## The commission
Leo's ask: "Consolidation and deepening of the co-cycle program. Proceed with a review of the
program and a literature review of surrounding ideas. Identify theoretical expansions and ideas from
the literature surrounding cocycle-grounded combinatorial identities and pigeonhole principles from
simplification in such cocycles. Limit of the cocycle approach given it applies to all Syracuse type
problems. Build an html report detailing potential directions for me to choose."

This is an **exhaustive** review: ≥150 verified sources in total across all agents. You are one of
several parallel agents, each with its own theme.

## The program in brief
Read `~/Syracuse/PROGRAM.md` first; it is a self-contained overview.

**Objects.**
- Gap word w = (d₀,…,d_{o−1}), with d_i ≥ 1 the halvings after the i-th odd step.
- e_k = Σ_{i<k} d_i and E = Σ d_i.
- S(w) = Σ_k X^{e_k} Y^{o−1−k} and D(w) = X^E − Y^o, both in ℤ[X,Y]; specialise to (X,Y) = (2,3).
- The concatenation cocycle: S(uv) = Y^{len v}·S(u) + X^{|u|}·S(v).
- The transfer matrix M(w) = [[Y^o, 0], [S, X^E]].
- Rotation sums S^{(j)} = S(w rotated by j).

**On a genuine cycle** with odd elements x₀,…,x_{o−1}: S^{(j)} = D·x_j, and
G := gcd_j S^{(j)} = |2^E − 3^o|.

**Method.** Simple word moves (frame strip, anchor split, combination rounds) build a small nonzero
element C of the rotation ideal. Then G ≤ sixfree(C), the 6-free part of C. This is squeezed against
Baker/Rhin lower bounds on |2^E − 3^o|.

**Status.**
- "Layer 1 (ℤ[X,Y] algebra) is closed": the cocycle's Alexander polynomial X^E − Y^o·t is a
  binomial. Syzygies, twists, Tietze moves and circulants all came back null.
- "Layer 2 is the (2,3)-arithmetic."
- The one working lever is the *bounded-defect lever*: for the word βd^L (a bounded arc β over one
  long run), G ≤ sixfree(S(βd) − S(dβ)), independent of o.

**Open problems.**
1. An explicit bound f(w).
2. Covering / pigeonhole: a finite menu of moves such that every word contains one. "Unavoidable
   patterns / Zimin words" was named, but no literature was read.
3. The no-go for ≥2 growing runs (cyclotomic collapse, Bang–Zsygmondy).
4. Normalising the AM–GM abelian estimator.

**Incubator.** `~/Syracuse/ideas/cocycle-combinatorics/`: STRUCTURE.md, LOG.md, THREADS.md (the
queue of wanted reads), `drafts/lit-*.md` (literature already read) and
`drafts/covering-reductions.md`.

## Reframing findings: use these to judge relevance
- **F1. G is a two-term gcd.** G(w) = gcd(S(w), D(w)), via the recursion 2^{d₀}S^{(1)} = 3S + D and
  D odd. Every positive word with D > 0 is a primitive positive cycle of the map
  x ↦ (3x + k)/2^{ν₂(3x+k)}, with k(w) = D/G and elements S^{(j)}/G. The 3x+1 no-cycle conjecture
  becomes "k(w) ≠ 1 for every nontrivial positive word". **The program is a gcd problem for
  S-unit expressions**: S is a sum of o S-units 2^a·3^b, and D = 2^E − 3^o.
- **F2. Fixed-slope families are already excluded.** Families with a fixed background run (βd^L,
  u^p·β) have a rational limiting slope E/o → d. A positive cycle needs
  log₂3 < E/o ≤ log₂(3 + 1/x_min) (the ratio sandwich; x_min > 2⁷¹ computationally). So these
  families are excluded elementarily. Every cycle-relevant word has slope → log₂3 and therefore
  unboundedly many runs, i.e. it is *balanced / Sturmian-like*.
- **F3. Thresholds.** Ellison 1971, |2^x − 3^y| > 2^x·e^{−x/10} for x > 27 (≈2.56^o), beats
  Rhin / Simons–de Weger (|2^E − 3^o| > 0.00219·3^o/o^{13.3}) for o ≲ 570.
- **F4. Limits.**
  - Every ℤ[X,Y] identity holds for every Syracuse-type map (px+q, 3x+k, 5x+1, negative cycles).
  - 5x+1 has positive cycles with D > 0: words (1,4), (1,1,5), (1,3,3).
  - 3x+1 has negative cycles −1, −5, −17.
  - Hence steps that use only generic identities, "D odd" and |D|-based ceilings are blind to
    3 vs 5, to q, and to the sign of D. They can prove at best "no cycle with o > o₀(q, family)".
  - The real limit is effectivity: o₀ against the cycle-length lower bounds that follow from N₀.
- **F5. Pigeonhole notes (analytic, to be checked against literature).**
  - A shared prefix of two rotations strips only a power of 2, so it is invisible on the 6-free
    axis. On a cycle it gives only x_i ≡ x_j mod 2^{|prefix|}.
  - The counting budget is thin: ln C(E−1, o−1)/o ≈ 1.04 nats/letter against ln 3 ≈ 1.099 at the
    critical slope.
  - Zimin patterns are probably the wrong tool, because variables can be single letters and the
    bounds are tower-type.
  - The right notion is *additive (χ-matched) powers*: consecutive blocks with equal length and
    equal sum, which is abelian equivalence over {1,2}. Additive cubes are avoidable
    (Cassaigne–Currie–Schaeffer–Shallit 2014). The avoidability of additive squares may be open
    (Pirillo–Varricchio).

## Already covered: do not re-report these as new (dedup)
Check these before adding an entry. You MAY add an entry for an already-cited source if you read
it and extract something new that bears on F1–F5, but tag it `"dup": true`.
- `~/Syracuse/approaches/cycle-literature/SURVEY.md`, `EXCLUDED_PATTERNS.md`
- `~/Syracuse/approaches/zero-sum-combination/LITERATURE-REVIEW.md`
- `~/Syracuse/approaches/cocycle-combine/structure/KNOWLEDGE_MAP.md`
- `~/Syracuse/ideas/cocycle-combinatorics/THREADS.md` and `drafts/lit-*.md`
- `~/syracuse_words/references/*.md`
- `~/syracuse_paper/literature/INDEX.md`

## Output format
1. **Your theme file**, `~/Syracuse/reports/cocycle-review/lit/<THEME>.md`:
   - **Executive summary** (≤ 300 words): what the literature says about the program, and the 3–5
     strongest hooks.
   - **Idea → hook map**: a table with columns idea | source(s) | which open problem or F-item it
     touches | what it would give | verdict (keep / kill / open) | cheapest first test.
   - **Annotated bibliography**, one entry per source:
     - full citation (authors, title, venue, year);
     - URL and/or DOI;
     - the verbatim key statement, quoted from the fetched page or PDF;
     - a 2–4 line note on relevance to the program;
     - a verdict.
   - **Leads for round 2**: papers to citation-chase, with the reason.
2. **Your bibliography lines**, `~/Syracuse/reports/cocycle-review/lit/bib-<THEME>.jsonl`, one JSON
   object per line, in this shape:
   `{"id":"<firstauthor><year><shortword>","theme":"<THEME>","authors":"…","title":"…","venue":"…","year":2003,"url":"…","doi":"…","quote":"<verbatim key statement>","hook":"<F-item/open problem>","verdict":"keep|kill|open","verified":true,"dup":false}`
   - Set `verified: true` ONLY if you fetched the page (abstract page, arXiv, publisher, MathSciNet
     review, or author PDF) and the quote comes from it. Otherwise set `verified: false` and say why.

## Rules
- Use WebSearch and WebFetch. Prefer arXiv abstract pages, publisher DOIs, zbMATH and author pages.
  **Never invent citations, years or quotes.** If unsure, mark the entry unverified.
- Write only inside `~/Syracuse/reports/cocycle-review/lit/`. Edit no other file. Run no
  experiments.
- Be quantitative wherever the literature allows: exponents, constants, effectivity, explicit
  bounds.
- Judge each idea against F1–F5. Say plainly when something cannot help, and why.
