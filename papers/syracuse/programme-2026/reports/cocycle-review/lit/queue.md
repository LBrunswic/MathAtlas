# Theme `queue`: resolving the incubator reading queue

Scope: every queued, wanted, unread, "FOLLOWUP" or "to read" item in
`ideas/cocycle-combinatorics/THREADS.md`, `ideas/cocycle-combinatorics/LEVERAGE-ROADMAP-L1.md` and
`approaches/cocycle-combine/structure/KNOWLEDGE_MAP.md`. The pass also covers the follow-up lines those
files point to: `LOG.md` FOLLOWUP entries, the "follow-up refs worth queuing" blocks in `drafts/lit-*.md`,
the "acquire next" lines in `structure/notes/`, and the Friedl–Vidussi survey that
`~/syracuse_words/references/ggt_universal_cocycle_survey.md` archived unread.
Bibliography lines: `bib-queue.jsonl` (78 entries). Every quote there was machine-checked as a verbatim
substring of the fetched page: arXiv API abstract, Crossref record, zbMATH Open review, or the author/talk PDF.

## 1. Executive summary

The queue holds **95 distinct items**: 12 belong to other themes, 5 were already read elsewhere, 1
cannot be identified, and **76 were fetched and judged here**. Most were read at abstract level; 13 only
as bibliographic records. Full text was read for arXiv:2512.05512, the balanced-word chapter of
Berstel–Lauve–Reutenauer–Saliola, and Martiny's slides.

**What the literature says.** The queue was built for two programmes that are now closed.
- **55 items are retired by F2.** They served the Layer-1 enrichment (R2, closed by the binomial wall)
  or the ≥2-growing-run no-go. That no-go concerns families d^a e₁ d^a e₂ d^a, whose slope tends to d.
- **19 are null.** S-unit counting (Evertse–Schlickewei–Schmidt) bounds counts, not sizes. Effective
  S-unit theory stops at 5 terms (Bajpai–Bennett). Pillai atlases touch only tiny o. Real dynamics
  (Misiurewicz–Rodrigues) *confirms F4*: every word is a real periodic orbit x = S/D.

**arXiv:2512.05512** (Kang–Matsusaka–Park, *On the Alexander polynomials of modular knots*) was queued
as an o-independent ceiling. It is not one:
- "Finitely many per degree" is #A_n ≤ p(n), because the degree grows linearly in the run lengths.
- The "long runs" are runs of same-sign *coefficients*, not of letters.

Verdict: null; its target (βd^L) is retired by F2 anyway.

**The one live hook (narrow, untested).** BLRS Thm 6.9, with Berstel–de Luca 1997: a binary word is a
Christoffel conjugate iff it is circularly balanced. Knight 2023 excludes the Christoffel parity words,
so **every remaining cycle has a circularly unbalanced parity word**, hence an explicit unbalance witness.
This sharpens the "balanced ⇒ pigeonhole" half of `drafts/covering-reductions.md` into:
- balanced: closed (Knight's C9 core);
- unbalanced: a canonical witness pair at which to anchor a two-rotation move.

The queue also contains **13 citation errors and stale statuses** (§3).

## 2. Disposition table (the resolved queue)

File aliases:
- **T** = `ideas/cocycle-combinatorics/THREADS.md`
- **R** = `…/LEVERAGE-ROADMAP-L1.md`
- **L** = `…/LOG.md`
- **K** = `approaches/cocycle-combine/structure/KNOWLEDGE_MAP.md`
- **N/** = `approaches/cocycle-combine/structure/notes/`
- **D/** = `ideas/cocycle-combinatorics/drafts/`

Verdict codes:
- **live**: a concrete lever, with a first test.
- **null**: no leverage (the reason is given).
- **F2-slope**: retired by F2, because it only addresses fixed-slope or bounded-run families.
- **F2-L1**: retired by F2, because it addresses a closed Layer-1 question.
- **→ theme**: covered by another theme (pointer only).
- **dup**: already read in a dedup file.
- **unverif.**: the item cannot be identified.

| # | Queued item | Source file:line | Verdict | One-line reason |
|---|---|---|---|---|
| 1 | Bilu–Hanrot–Voutier 2001 (+ Bang–Zsygmondy) | T:13, K:86, L:88, D/lit-filaseta-schinzel:195 | → arithmetic | primitive divisors / S-unit gcd |
| 2 | Schinzel 1974 / Stewart, greatest prime factor of aⁿ−bⁿ | T:15, L:88, D/lit-filaseta-schinzel:198 | → arithmetic | Stewart |
| 3 | Mason–Stothers on the C8 triple | T:16 | → arithmetic | Mason–Stothers |
| 4 | Brunault–Guilloux–Mehrabdollahei–Pengo, *Limits of Mahler measures in multiple variables* (AIF 2024) | T:17 | F2-slope | serves the ≥2-growing-run no-go (slope → d). Also the wrong object: a Mahler floor does not bound sixfree(Q_a(2,3)) |
| 5 | Dvornicich–Zannier 2007 | T:18 | → arithmetic | Dvornicich–Zannier |
| 6 | Filaseta–Kalogirou 2025 (arXiv:2508.12242) | T:19 | F2-slope | the ≥2-run no-go; the result holds for "almost all" exponent tuples of 0,1-polynomials, so it is silent on any given family |
| 7 | Brownawell–Masser 1986 | T:20 | → arithmetic | Brownawell–Masser |
| 8 | Hong–Yang, parametric gcd (arXiv:2401.00408) | T:21 | F2-slope | serves the ≥2-run no-go. Also an F1 mismatch: its parameters are coefficients (ours are exponents) and its gcd is a polynomial gcd (G is an integer gcd) |
| 9 | Eagon–Northcott 1962 | T:23, L:163, L:176 | F2-L1 | R3/R4 closed (Hilbert–Burch, pd E₀ ≤ 1) |
| 10 | Lascoux 1978 resolution | T:23 | F2-L1 | R3/R4 closed |
| 11 | Bruns–Conca–Varbaro (arXiv:1111.7263) | T:23, L:163 | F2-L1 | our cores are 2×2 maximal minors, i.e. the Plücker case (R3) |
| 12 | Christie–Dykema–Klep 2020 | T:24 | F2-slope | the {1,2,6} collapse list it served was itself corrected to the homogeneous gate {1} |
| 13 | Lam–Leung 2000 | T:24 | F2-slope | same as #12 |
| 14 | König–Neftin 2020 | T:25 | F2-slope | Hilbert-irreducibility fibres; our parameter sits in exponents, not in a fibre value |
| 15 | Evertse–Schlickewei–Schmidt 2002 | T:25, K:80, N/cocycle-complexity:63 | null | counts non-degenerate solutions, ≤ exp((6n)^{3n}(r+1)); with n = o this is vacuous, and it gives no size or gcd |
| 16 | Bajpai–Bennett 2023, effective 5-term S-unit | T:25 | F2-slope | a few-term S-unit relation exists only for bounded-run words (m-cycles; Hercher m ≤ 91) |
| 17 | Aliev–Smyth 2007 | T:25 | F2-slope | torsion cosets; (2,3) is not torsion; served the ≥2-run collapse |
| 18 | Sakasai 2012 survey | T:33, L:102 | F2-L1 | L1·1 done; rank-1 Magnus exhausted |
| 19 | Suzuki 2005 (Kobe J. Math. 22) | T:33, L:102 | F2-L1 | L1·1 done |
| 20 | **arXiv:2512.05512** Kang–Matsusaka–Park | T:34, R:91–94, L:73, L:186 | null (target F2-slope) | degree-counting finiteness (#A_n ≤ p(n)); the runs are coefficient-sign runs; see §5.1 |
| 21 | Gordon 1972 | T:36, L:218, D/lit-silver-williams:215 | F2-L1 | X^E−Y^o·t never divides tⁿ−1, already derived in L1·9 |
| 22 | "Davis–Ray" arXiv:1105.2590, actually **Bullock–Davis** | T:36, T:39, D/lit-silver-williams:217 | F2-L1 | polynomial strong coprimality of twist-knot Δ, not an integer gcd at (2,3) |
| 23 | Lind 2005, Lind–Lehmer constant | T:36, T:39, D/lit-silver-williams:219 | F2-L1 | a floor on ∏S(ζ), whereas the squeeze needs an upper bound; L1·9 circulant already done |
| 24 | arXiv:math/0412513, actually **Silver–Stoimenow–Williams** (AGT 6, 2006) | T:37 | F2-slope | "bounded arc over one run vs ≥2 runs" compares fixed-slope families |
| 25 | Champanerkar–Kofman, twisting (math/0404236, AGT 5, 2005) | T:37 | F2-slope | Jones polynomial; same fixed-slope analogy as #24 |
| 26 | Kitayama 2007, normalisation | T:38, R:97 | F2-L1 | L1·7 already resolved: det M(w) is a 6-unit |
| 27 | Conway–Estier 2017 | T:38, R:97 | F2-L1 | L1·7 resolved |
| 28 | Glasby–Lübeck–Niemeyer–Praeger 2017 | T:45, L:74 | → arithmetic | Glasby et al. |
| 29 | Laurent 2008 / Gouillon 2006 | T:46, L:74 | → arithmetic | two-log constants |
| 30 | Stewart 2013 / Bilu–Hong–Gun (arXiv:2108.09857) | T:47 | → arithmetic | Stewart |
| 31 | Iannucci 2019 | T:47, L:74 | null | **misattributed**: it is about *sums* 2^x+3^y; tiny o only |
| 32 | Bennett 2003, *Pillai's conjecture revisited* | T:47, K:80, N/cocycle-complexity:46,64 | null | exceptions (N,c) = (2,1),(2,5),(2,7),(2,13),(2,23),(3,13); tiny o only |
| 33 | Hillman–Silver–Williams 2010 | T:53 | F2-L1 | the reversal thread was closed (Gen-8, RE-3) |
| 34 | Knus–Merkurjev–Rost–Tignol, *Book of Involutions* | T:54 | F2-L1 | reversal thread closed |
| 35 | Adamczewski–Allouche 2007 | T:54 | F2-L1 | reversal thread closed; the palindromic regime is Knight's |
| 36 | Morier-Genoud–Ovsienko arXiv:1811.01229 (*Farey boat I*) | T:54 | F2-L1 | reversal thread closed |
| 37 | Morishita, *Knots and Primes* | T:61, L:151 | F2-L1 | R1 (Crowell module) closed |
| 38 | Mikhalev–Zolotykh 1998 | T:69, L:130 | F2-L1 | L1·3/L1·4 closed |
| 39 | Morifuji–Suzuki (arXiv:2311.15484) | T:93, D/lit-mcmullen-norm:239 | F2-L1 | R2 closed: the Cₙ product on X^E−Y^o·t gives the binomial X^{En}−Y^{on}tⁿ |
| 40 | Boyd 1981 | T:94, K:82 | F2-L1 | the M = 1 criterion; our binomial is never M = 1 |
| 41 | Dubickas–Smyth 2005 | T:94 | F2-L1 | R2 closed; Thm 2 needs a single base ω, not the pair (2,3) |
| 42 | McMullen 2000, Teichmüller polynomial | T:95 | F2-L1 | R2 closed (R says these follow-ups are now superfluous) |
| 43 | Koberda arXiv:1110.3746 | T:95 | F2-L1 | R2 closed |
| 44 | Suciu 2015/16, tangent cone | T:96 | F2-L1 | a binomial has a single translated-subtorus jump locus |
| 45 | Suciu 2014, characteristic varieties of free abelian covers | D/lit-mcmullen-norm:251, D/lit-boden-friedl:259 | F2-L1 | same as #44 |
| 46 | Hironaka–Kin 2006 | T:97 | F2-L1 | R2 template |
| 47 | Hironaka 2006, Salem–Boyd | T:97 | F2-L1 | R2 template |
| 48 | Hironaka 2002, 2,3,7 | T:98 | F2-L1 | Coxeter (2,3,7), unrelated to our (2,3) |
| 49 | Hillman–Livingston–Naik (AGT 6, 2006; math/0412380) | T:99 | F2-L1 | R2 closed; **wrong id and year** in T |
| 50 | Elliot 2009 (arXiv:0911.2273, queued under the HLN name) | T:99 | F2-L1 | R2 closed |
| 51 | Murasugi 1971 | T:99 | F2-L1 | R2 closed; the period Fox formula already has its Φ_d factors |
| 52 | Silver–Williams 2005 (math/0509068) | T:100 | F2-L1 | L1·9 already gave G^o growth |
| 53 | Squier 1987 + arXiv:1009.0381 (L1·4 "queued") | R:80 | F2-L1 | **stale status**: mined via Guiraud–Malbos 1011.0558; 1009.0381 is Segev (confirmed) |
| 54 | Squier–Otto–Kobayashi 1994 | L:176 | F2-L1 | no 3-cell (R4) |
| 55 | Labute 1970, LCS rank formula | L:186 | F2-slope | the weight-growth question is the ≥2-growing-run no-go |
| 56 | "a twisted/Massey-product holonomy ref" | L:186 | unverif. | no reference named; it would be Layer-1 anyway |
| 57 | Eisenbud–Neumann 1985, graph-link families | L:228 | F2-L1 | R2 templates |
| 58 | Boden–Friedl II and III | D/lit-boden-friedl:260 | F2-L1 | R2·2 closed |
| 59 | Berstel–Reutenauer, *Noncommutative Rational Series* ("unread") | K:74 | → frames | **stale**: note `N/berstel-reutenauer-…md` exists |
| 60 | López–Stoll 2009, 3x+1 conjugacy over a Sturmian word | K:75, N/lagarias-annotated-bibliography:37 | null | only irrational-slope mechanical words: the Christoffel limit, which Knight closed; 2-adic; no finite-cycle content |
| 61 | Bernstein–Lagarias 1996 | K:75, N/lagarias-annotated-bibliography:38 | → generalized-maps | — |
| 62 | Misiurewicz–Rodrigues 2005, *Real 3x+1* | K:76 | null | confirms F4: real periodic points are dense |
| 63 | Bergelson–Misiurewicz–Senti 2006 | K:76 | null | real density; blind to integrality |
| 64 | **Berstel–Lauve–Reutenauer–Saliola 2009** | K:77, N/knight2023-high-cycles:43, N/berstel-reutenauer…:43 | **live** | Thm 6.9: circularly balanced ⇔ Christoffel conjugate. Every non-Knight cycle has an unbalance witness (§5.2) |
| 65 | **Berstel–de Luca 1997** | K:77, N/cohn1972-markoff-forms:39 | **live** (same lever) | Christoffel ⇔ balanced Lyndon (Thm 6.4 in BLRS) |
| 66 | Series 1985 | K:77 | dup | verified in syracuse_words `ggt_universal_cocycle_survey.md` §3.1 |
| 67 | Eliahou 1993 | K:78 | dup | cycle-literature SURVEY |
| 68 | Simons–de Weger 2005 | K:78, N/eliahou…:33 | dup | PROGRAM §3 |
| 69 | Martiny 2015 | K:78, N/eliahou…:32, N/lagarias…:39 | null | the main theorem is F2's ratio sandwich; superseded by Hercher 2023; unrefereed talk |
| 70 | Steiner 1977/78 | K:78 | dup | cycle-literature |
| 71 | Rhin 1987 / Baker 1975 / Matveev 2000 | K:79 | → arithmetic | — |
| 72 | Evertse–Győry 2015, *Unit Equations* | K:80 | null | reference text; the o-term gcd question goes to the arithmetic theme |
| 73 | Stroeker–Tijdeman 1982 | K:80, N/cocycle-complexity:46 | null | Pillai for 3^x−2^y; tiny o |
| 74 | Bell–Smertnig 2021 | K:80, N/cocycle-complexity:47 | → frames | rational series |
| 75 | Everest–van der Poorten–Shparlinski–Ward, *Recurrence Sequences* | K:80 | null | reference text |
| 76 | Skolem–Mahler–Lech (Ouaknine–Worrell) | K:80, N/cocycle-complexity:41 | null | zero sets, not gcd or size; non-degeneracy already used |
| 77 | Cohn, *Free Ideal Rings* | K:81, N/cocycle-complexity:35 | F2-L1 | free-field factorisation is F4-blind |
| 78 | Schrempf (arXiv:1803.10627) | K:81 | F2-L1 | C10 already gives the minimal representation |
| 79 | Kronecker 1857 | K:82 | F2-L1 | binomial, never M = 1 |
| 80 | Smyth, Mahler measure survey | K:82, N/cocycle-complexity:62 | F2-L1 | Mahler complexity of ℤ[X,Y] objects is F4-blind |
| 81 | Everest–Ward 1999 | K:82 | F2-L1 | same as #80 |
| 82 | Lind–Schmidt–Ward 1990 | N/cocycle-complexity:18,62 | F2-L1 | same as #80 |
| 83 | Calegari, *scl* | K:83 | dup | syracuse_words (`calegari_scl_book.pdf`, GGT survey) |
| 84 | Frigerio, *Bounded cohomology* | K:83 | null | σ is a χ-twisted cocycle; no twisted bounded theory exists |
| 85 | Turaev 2002, 2-complex norm | K:84, N/thurston-alexander-norm:143,149 | F2-L1 | Layer-1 norm inequality, F4-blind |
| 86 | "Friedl survey" arXiv:2108.08645, actually **Kitayama**, *A survey of the Thurston norm* | K:84 | F2-L1 | misattributed; Layer-1 |
| 87 | Friedl–Vidussi, twisted Alexander survey (0905.0591) | ggt_universal_cocycle_survey.md:226 | F2-L1 | R2 closed |
| 88 | Fried 1982, cross sections | N/thurston-alexander-norm:143 | F2-L1 | words are already fibered (C11) |
| 89 | Hartnick–Talambutsa (arXiv:1508.03166) | K:85, N/cocycle-complexity:65 | null | counting functions mod bounded: no size or gcd content |
| 90 | arXiv:2407.10569, actually **Kiyashko–Talambutsa** | K:85 | null | algorithmic |
| 91 | Brown, *Cohomology of Groups* | K:87 | null | background; C5/C6 already certified |
| 92 | Serre, *Local Fields* | K:87 | null | background |
| 93 | Everett 1977 | K:88 | null | density result; nothing on cycles |
| 94 | Wirsching 1998, LNM 1681 | K:88 | null (dup) | already in syracuse_paper INDEX |
| 95 | Bang–Zsygmondy (listed separately at K:86) | K:86 | → arithmetic | merged with #1 |

**Counts.** 95 rows, 94 distinct (row 95 merges into row 1).

| Category | Rows | Count |
|---|---|---|
| Covered by other themes | 1, 2, 3, 5, 7, 28, 29, 30, 59, 61, 71, 74 | 12 |
| Dup, not re-read | 66, 67, 68, 70, 83 | 5 |
| Unverifiable | 56 | 1 |
| Read and judged | everything else | 76 |

The 76 read items break down as follows:

| Verdict | Count | Rows |
|---|---|---|
| live | 2 | 64, 65 |
| F2-slope | 11 | |
| F2-L1 | 44 | |
| null | 19 | includes #20, whose target is also F2 |

## 3. Citation errors and stale statuses found in the queue (not edited; the brief forbids it)

1. **T:37.** arXiv:math/0412513 is *Silver–Stoimenow–Williams*, "Euclidean Mahler measure and twisted links",
   AGT 6 (2006) 581–602. The Champanerkar–Kofman twisting paper is math/0404236, AGT 5 (2005) 1–22.
   The claim "bounded under parallel, blows up under anti-parallel twisting" appears in neither abstract.
2. **T:36, T:39.** arXiv:1105.2590 is *Bullock–Davis*, not "Davis–Ray".
3. **T:99.** arXiv:0911.2273 is *Ross Elliot* (2009). Hillman–Livingston–Naik is math/0412380, AGT 6 (2006) 145–169.
4. **T:47.** Iannucci (arXiv:1907.03347) counts integers with two representations as 2^x+3^y (*sums*).
   The difference list |2^a−3^b| ∈ {1,5,7,13,23} is Bennett 2003.
5. **K:84.** arXiv:2108.08645 is Kitayama, *A survey of the Thurston norm*, not a Friedl survey.
6. **K:85.** arXiv:2407.10569 is by Kiyashko–Talambutsa.
7. **K:76.** The author is Ana *Rodrigues*. The paper is *Real 3x+1*, PAMS 133 (2005) 1109–1118.
8. **R:80.** L1·4 still reads "queued (NEW ref)" with the wrong id 1009.0381 (Segev). It was mined via
   1011.0558 (THREADS:70).
9. **K:74.** Berstel–Reutenauer is marked "unread", but `notes/berstel-reutenauer-…md` exists.
10. **T:17.** The title is "Limits of Mahler measures in *multiple* variables", Ann. Inst. Fourier 74 (2024).
11. **T:19.** Filaseta–Kalogirou is an exposition of a Schinzel theorem on 1+x^{n₁}+…+x^{n_k}, valid for
    *almost all* exponent tuples.
12. **T:34, R:91–94.** The hook for arXiv:2512.05512 is a misreading (§5.1).
13. **T:54.** arXiv:1811.01229 is *Farey boat I* (Morier-Genoud–Ovsienko), on continued fractions and
    triangulations.

## 4. Idea → hook map

| Idea | Source(s) | Open problem / F-item | What it would give | Verdict | Cheapest first test |
|---|---|---|---|---|---|
| Christoffel ⇔ circularly balanced; non-Christoffel cycles carry an unbalance witness 0p0 / 1p1 (p a palindrome) | BLRS Thm 6.9; Berstel–de Luca 1997 (BLRS Thm 6.4); Lothaire Prop. 2.1.3 for the palindrome form (not fetched) | OP2 covering; F2, F5 | an exact two-case cover: (B) balanced → Knight C9 (closed); (U) unbalanced → a canonical pair of rotations to anchor a move | **open (live, narrow)** | engine: take 200 random critical words (o = 20–200); find the shortest circular witness pair; form the C9-analogue difference of the two rotations starting at 0p0 and 1p1; record log₁₀(sixfree/\|D\|) and compare with the existing anchored moves |
| "Finitely many Alexander polynomials per degree" as an o-independent ceiling | Kang–Matsusaka–Park 2025 | OP1; L1·6 | nothing: degree grows linearly with run length | kill | none (settled by reading) |
| Mahler-floor / cyclotomic-rigidity closers for ≥2 growing runs | Brunault et al.; Filaseta–Kalogirou; Christie–Dykema–Klep; Lam–Leung; König–Neftin; Aliev–Smyth; Hong–Yang | OP3 | at best a no-go for a fixed-slope family | kill (F2) | — |
| Few-term effective S-unit equations; Pillai atlas | Bajpai–Bennett; Bennett 2003; Stroeker–Tijdeman; Iannucci | F1, F3 | only bounded-run words or tiny o | kill | — |
| Uniform S-unit counting | Evertse–Schlickewei–Schmidt; Evertse–Győry | F1 | counts, not sizes; n = o terms | kill | — |
| Rank ≥2, twisted, periodic or Teichmüller enrichment | Morifuji–Suzuki; HLN / Elliot / Murasugi; Gordon; Boyd; Dubickas–Smyth; McMullen 2000; Koberda; Suciu ×2; Hironaka ×3; Silver–Williams 2005; Turaev; Kitayama 2021; Friedl–Vidussi; Fried; Boden–Friedl II/III; Eisenbud–Neumann | Layer-1 R2 | nothing past the binomial wall X^E − Y^o·t | kill | — |
| Normalisation of twisted invariants | Kitayama 2007; Conway–Estier | L1·7 | already resolved (det M(w) is a 6-unit) | kill | — |
| Syzygy / rewriting completion | Eagon–Northcott; Lascoux; Bruns–Conca–Varbaro; Squier; Squier–Otto–Kobayashi; Mikhalev–Zolotykh; Labute | L1·3–L1·5 | closed | kill | — |
| Real free-semigroup dynamics | Misiurewicz–Rodrigues; Bergelson–Misiurewicz–Senti | F4 | evidence for F4: every word is a real periodic orbit | kill (cite as F4 evidence) | — |
| 3x+1 conjugacy on Sturmian words | López–Stoll | F2 (Christoffel limit) | the Knight-closed limit case | kill | — |
| Ratio sandwich via continued fractions | Martiny 2015 | F2, F3 | already F2 | kill | — |
| Bounded cohomology / counting functions | Frigerio; Hartnick–Talambutsa; Kiyashko–Talambutsa | OP4 | no χ-twisted theory | kill | — |
| Free-field factorisation; Mahler complexity κ | Cohn; Schrempf; Kronecker; Smyth; Everest–Ward; Lind–Schmidt–Ward; Lind 2005 | cocycle-complexity §8 | F4-blind | kill | — |

## 5. Annotated bibliography

Each entry: citation; URL / DOI; verbatim quote (as in `bib-queue.jsonl`); note; verdict.
"[record]" means only the bibliographic record was fetched.

### 5.1 The flagged item

**Kang, S.-Y., Matsusaka, T., Park, K. — "On the Alexander polynomials of modular knots."**
arXiv:2512.05512 [math.GT, math.NT], 5 Dec 2025, 31 pp. https://arxiv.org/abs/2512.05512 ·
doi:10.48550/arXiv.2512.05512 · full text read.

> "On the one hand, for each fixed degree, only finitely many Alexander polynomials of modular knots
> occur. On the other hand, any integer appears as a coefficient of the Alexander polynomial of some
> modular knot, and coefficients of the same sign can occur in runs of arbitrarily long length."

- **Why it was queued.**
  - THREADS:34 queued it as "a Burau-word cocycle with a proven finitely many Alexander polys per
    fixed degree (any coefficient in long runs)", i.e. "a ceiling bounded by combinatorial type, not
    run length".
  - ROADMAP L1·6 asks whether exclusion is a "finite-weight phenomenon".
- **What it is.**
  - A modular knot is the closure of a positive (Lorenz) braid built from a primitive L/R word.
  - That word is the continued-fraction word of a real quadratic irrational. The braid joins the
    lexicographic ranks of consecutive rotations (Def. 2.10–2.13).
  - Thm 6.10 writes the (P_r+Q_r)-dimensional reduced Burau matrix explicitly.
  - Cor 6.12 gives the degree: deg Δ = Σ_{j<r}(P_j−1)q_j + (P_r−1)(q_r−1).
  - Thm 7.1, #A_n ≤ p(n), follows by counting tuples. The authors call it "already known to experts
    studying Lorenz knots".
  - Thm 8.2 builds words (LLR)ⁿ(LR)ⁿR whose Δ has long runs of *negative coefficients*.
- **Why it cannot help.**
  - The finiteness holds because degree (twice the genus of a positive braid) grows linearly with
    every run length q_j. Fixing the degree bounds the word, which is the opposite of an
    o-independent ceiling.
  - The "runs" are runs of coefficient signs, not runs of letters.
  - The representation has rank P_r+Q_r, growing with the word. It is not the 2×2 transfer matrix,
    and its Δ is not our binomial.
  - Thm 4.2 (Christoffel word ch_{p/q}(L,LR) ↦ (p,q)-torus knot) touches only the Christoffel case,
    already excluded by Knight 2023.
- **Verdict: null.** The intended target (βd^L ceiling) is also retired by F2.

### 5.2 The live lever

**Berstel, J., Lauve, A., Reutenauer, C., Saliola, F. V. — *Combinatorics on Words: Christoffel Words
and Repetitions in Words*.** CRM Monograph Series 27, AMS, 2009 (zbMATH 1161.68043).
doi:10.1090/crmm/027. The 2008 draft PDF was read:
https://ehess.modelisationsavoirs.fr/atiam/biblio/Berstel-Christoffel2009.pdf

> "Theorem 6.9 (folklore). A word w ∈ {x, y}∗ is a conjugate of a Christoffel word if and only if w and
> all of its conjugates are primitive and balanced1"

(Also Thm 6.8, Borel–Reutenauer: conjugate of a Christoffel word ⇔ the circular word has k+1 factors of
length k for all k < n.)

Note:
- Knight 2023 (KNOWLEDGE_MAP C9) excludes exactly the cycles whose parity word is a Christoffel
  conjugate. By Thm 6.9, these are exactly the cycles whose circular parity word is balanced.
- Hence every remaining cycle has two circular factors of equal length whose counts of odd steps
  differ by ≥ 2. The minimal such pair has the form 0p0 / 1p1 with p a palindrome (Lothaire 2002,
  Prop. 2.1.3; standard, not fetched here).
- This replaces the discrepancy heuristic of `covering-reductions.md` Part 3 with an exact dichotomy:
  - balanced → closed by Knight's monomial core;
  - unbalanced → a canonical witness pair.
- Whether the witness pair supports a C9-type core with small 6-free part is unknown. F5 warns that
  shared material between rotations tends to strip only powers of 2.
- This overlaps the `words` theme; coordinate there.

**Verdict: live (narrow).** First test: §4, row 1.

**Berstel, J., de Luca, A. — "Sturmian words, Lyndon words and trees."** Theoret. Comput. Sci. 178
(1997) 171–203. doi:10.1016/S0304-3975(96)00101-6 (zbMATH 0901.68155).

> "Theorem 6.4 (Berstel, de Luca [BdL1997]). A word w is a Christoffel word if and only if it is a
> balanced1 Lyndon word."

The quote is taken from the BLRS book, which states the theorem. The paper itself was verified only
through Crossref and zbMATH.

Note: this is the Lyndon-representative form of the same dichotomy. With Thm 6.9 it pins Knight's
exclusion to exactly the balanced class. **Verdict: live** (same lever).

### 5.3 Null items with a specific reason

- **Misiurewicz, M., Rodrigues, A. — "Real 3x+1."** PAMS 133 (2005) 1109–1118.
  doi:10.1090/S0002-9939-04-07696-8.
  > "We prove that this action is minimal (each trajectory is dense) and that the periodic points are dense."
  Note: over ℝ every gap word is a periodic orbit (x = S/D). The only obstruction is integrality,
  which is direct literature support for F4. **Null.**
- **Bergelson, V., Misiurewicz, M., Senti, S. — "Affine actions of a free semigroup on the real line."**
  ETDS 26 (2006) 1285–1305. doi:10.1017/S014338570600037X. zbMATH review:
  > "then under the action of \(G\) the orbit of any \(x\in \mathbb R^+ \) is dense in \(\mathbb R^+ \) (Theorem B in the paper)"
  **Null** (real density; blind to integrality).
- **López, J., Stoll, P. — "The 3x+1 conjugacy map over a Sturmian word."** Integers 9 (2009) A13,
  141–162. doi:10.1515/integ.2009.014. zbMATH summary:
  > "In this paper we compute \(\Phi(v)\) for a class of aperiodic infinite words \(v\) of minimal complexity, the mechanical words with irrational slope and intercept 0."
  Note: the slope-limit of the Christoffel (Knight) family; 2-adic infinite words; no finite-cycle
  statement. **Null.** Lead to the generalized-maps theme.
- **Martiny, T. I. — "New Lower Bound on Cycle Length for the 3n+1 Problem."** Pitt graduate-seminar
  slides, 9 Apr 2015; talk page https://mathematics.pitt.edu/node/2786.
  > "In this talk this lower bound is improved to 10,439,860,591 using an argument dependent upon continued fractions."
  Note: its theorem is the ratio sandwich log₂(3+M⁻¹) < E/o ≤ log₂(3+m⁻¹), the ingredient of F2.
  Unrefereed and superseded (Hercher 2023; N₀ ≈ 2⁷¹). **Null.**
- **Evertse, J.-H., Schlickewei, H. P., Schmidt, W. M. — "Linear equations in variables which lie in
  a multiplicative group."** Ann. of Math. 155 (2002) 807–836. doi:10.2307/3062133. zbMATH review:
  > "The main result of the paper is \[ A(a_1,\dots,a_n,\Gamma) \leq A(n,r) = \exp((6n)^{3n}(r+1)). \]"
  Note:
  - The theorem counts non-degenerate solutions; it gives neither a size nor a gcd.
  - For S(w) with n = o terms and rank r = 2, the bound is exp(3·(6o)^{3o}), which is vacuous.
  - On a cycle, S^{(j)} = D·x_j with x_j not an S-unit.
  **Null** against F1.
- **Bajpai, P., Bennett, M. A. — "Effective S-unit equations beyond 3 terms: Newman's conjecture."**
  arXiv:2308.05162 (2023).
  > "We show how to effectively solve 5-term $S$-unit equations when the set of primes $S$ has cardinality at most 3, …"
  Note:
  - Effectivity stops at 5 terms.
  - A gap word yields a few-term S-unit relation only when it has O(1) runs (the m-cycle regime), which
    F2 and Hercher's m ≤ 91 already settle.
  **Retired by F2** (bounded runs).
- **Bennett, M. A. — "Pillai's conjecture revisited."** JNT 98 (2003) 228–235.
  doi:10.1016/S0022-314X(02)00049-5. zbMATH review:
  > "then the equation \(|(N+ 1)^x- N^y|= c\) has at most one solution in positive integers \(x\) and \(y\), unless \((N, c)= (2, 1), (2, 5), (2, 7), (2, 13), (2, 23)\), or \((3, 13)\)."
  Note: this is the source of the "{1,5,7,13,23}" atlas, not Iannucci. It bears only on tiny o.
  **Null.**
- **Stroeker, R. J., Tijdeman, R. — "Diophantine equations."** Math. Centre Tracts 155 (1982)
  321–369; zbMATH 0521.10013. The statement comes from the Bennett review quoted above. **Null.**
- **Iannucci, D. E. — "On duplicate representations as 2^x+3^y …"** arXiv:1907.03347.
  > "there are exactly five positive integers that can be written in more than one way as the sum of a nonnegative power of 2 and a nonnegative power of 3."
  Note: about sums, so misattributed in the queue. **Null.**
- **Evertse, J.-H., Győry, K. — *Unit Equations in Diophantine Number Theory*.** CUP 2015.
  doi:10.1017/CBO9781316160749.
  > "… including effective results on unit equations over number fields, estimates on the number of solutions, …"
  **Null:** a reference text; the o-term gcd problem goes to the arithmetic theme.
- **Ouaknine, J., Worrell, J. — "Decision problems for linear recurrence sequences."** RP 2012, LNCS
  7550, 21–28. doi:10.1007/978-3-642-33512-9_3. The quote is from the EPiC talk abstract,
  doi:10.29007/tpxx:
  > "…the Skolem Problem (does a given LRS have a zero?)…"
  Note: Skolem–Mahler–Lech concerns zero sets. Our families need gcd or size statements, and their
  non-degeneracy (2^E/3^o not a root of unity) is already used. **Null.**
- **Everest, G., van der Poorten, A., Shparlinski, I., Ward, T. — *Recurrence Sequences*.** AMS SURV
  104 (2003). doi:10.1090/surv/104. [record] **Null** (reference text).
- **Frigerio, R. — *Bounded cohomology of discrete groups*.** arXiv:1610.08339.
  > "The aim of this monograph is to provide an introduction to bounded cohomology of discrete groups and of topological spaces."
  Note: our σ = S/Y^o is χ-twisted; the incubator's own note says no twisted defect theory exists.
  **Null.**
- **Hartnick, T., Talambutsa, A. — arXiv:1508.03166** and **Kiyashko, P., Talambutsa, A. —
  arXiv:2407.10569** (counting functions on free groups and monoids).
  > "…an algorithm to decide whether two sums of Brooks quasimorphisms on $F_n$ represent the same class in bounded cohomology."
  **Null:** a ℤ-valued shadow of S, with no gcd content.
- **Everett 1977** (Adv. Math. 25, 42–45; doi:10.1016/0001-8708(77)90087-1):
  > "The author shows that almost every integer \(m\) has an iterate \(f^k(m)<m\)."
  **Null.**
- **Wirsching 1998** (LNM 1681; doi:10.1007/BFb0095985) [record]: **null**, dup.
- **Brown, *Cohomology of Groups*** (GTM 87, 1982; doi:10.1007/978-1-4684-9327-6) and **Serre,
  *Local Fields*** (GTM 67, 1979; doi:10.1007/978-1-4757-5673-9) [records]: **null** (background for
  C5/C6, already certified).

### 5.4 Retired by F2 (≥2-growing-run no-go, i.e. fixed slope)

All of these served open problem 3 for families like d^a e₁ d^a e₂ d^a, whose slope tends to d. F2
excludes such families elementarily.

- **Brunault, F., Guilloux, A., Mehrabdollahei, M., Pengo, R.** — "Limits of Mahler measures in multiple
  variables." Ann. Inst. Fourier 74 (2024). doi:10.5802/aif.3611; arXiv:2203.12259.
  > "We provide moreover an explicit upper bound for the error term in this convergence, …"
  An effective Boyd–Lawton result. Even for its intended use it bounds M(P_a), not sixfree(P_a(2,3)).
- **Filaseta, M., Kalogirou, A.** — arXiv:2508.12242.
  > "For almost all choices of positive integers $n_{1} < \cdots < n_{k}$, we show that the polynomial $F(x) = 1 + x^{n_{1}} + \cdots + x^{n_{k}}$, removed of its cyclotomic factors, is irreducible."
- **Hong, H., Yang, J.** — arXiv:2401.00408.
  > "It amounts to partitioning the parameter space into ``cells'' so that the gcd has a uniform expression over each cell …"
  Also an F1 mismatch: the parameters are coefficients and the gcd is a polynomial gcd.
- **Christie, L., Dykema, K. J., Klep, I.** — arXiv:2008.11268.
  > "This paper classifies all minimal vanishing sums of roots of unity of weight at most 16 by hand, …"
- **Lam, T. Y., Leung, K. H.** — J. Algebra 224 (2000) 91–109; doi:10.1006/jabr.1999.8089. Quote from
  arXiv math/9511209:
  > "We prove that the answer is exactly the set of linear combinations with non-negative integer coefficients of the prime factors of $m$."
- **König, J., Neftin, D.** — arXiv:2001.03630.
  > "…the elements in the fiber $f^{-1}(a)$ are of degree $n$ over $\mathbb Q$ for most rational values $a$ by Hilbert's irreducibility theorem."
- **Aliev, I., Smyth, C.** — arXiv:0704.1747.
  > "We obtain new explicit upper bounds for the number of maximal torsion cosets on an algebraic subvariety of the complex algebraic $n$-torus …"
- **Silver, D. S., Stoimenow, A., Williams, S. G.** — AGT 6 (2006) 581–602; doi:10.2140/agt.2006.6.581.
  > "If the twist numbers of a collection of oriented alternating link diagrams are bounded, then the Alexander polynomials of the corresponding links have bounded euclidean Mahler measure (see Definition 1.2). The converse assertion does not hold."
- **Champanerkar, A., Kofman, I.** — AGT 5 (2005) 1–22; doi:10.2140/agt.2005.5.1.
  > "For pretzel links P(a_1,...,a_n), we show that the Mahler measure of the Jones polynomial converges if all a_i tend to infinity, and approaches infinity for a_i = constant if n tend to infinity, just as hyperbolic volume."
- **Labute, J. P.** — J. Algebra 14 (1970) 16–23; doi:10.1016/0021-8693(70)90130-4. [record] The
  "weight-growth ω → ∞" restatement is OP3.

### 5.5 Retired by F2 (Layer-1 closed)

These served R1–R4, L1·1–L1·7 or R2. That algebra is closed: every rank-1 or metabelian
(2,3)-enrichment stays binomial, its Newton polytope is a segment, and it has no M = 1 slice. All
ℤ[X,Y]-level statements are also F4-blind. Quotes are in the JSONL; one line each here.

- **Gordon 1972**, Trans. AMS 168, 357–370 (doi:10.1090/S0002-9947-1972-0295327-8). Periodic H₁ of
  cyclic covers ⇔ λ₁ | tⁿ−1. Our Δ fails this (L1·9).
- **Murasugi 1971**, CMH 46, 162–174; **Hillman–Livingston–Naik 2006**, AGT 6, 145–169;
  **Elliot 2009**, arXiv:0911.2273. Periodicity congruences; R2 closed.
- **Bullock–Davis 2011**, arXiv:1105.2590. Strong coprimality f(t^k), g(t^l); polynomial, not an integer gcd.
- **Lind 2005**, PAMS 133, 1411–1416. Lehmer constant for compact abelian groups: a floor, not a ceiling.
- **Kitayama 2007**, arXiv:0705.2371; **Conway–Estier 2017**, arXiv:1709.03479. Normalisation, which
  L1·7 already settled.
- **Hillman–Silver–Williams 2010**, AGT 10, 1017–1026; **KMRT 1998** [record]; **Adamczewski–Allouche
  2007** [record]; **Morier-Genoud–Ovsienko**, arXiv:1811.01229. Reversal thread (closed).
- **Morishita 2012** [record]; **Mikhalev–Zolotykh 1998**, IJAC 8; **Eagon–Northcott 1962**, Proc. R.
  Soc. A 269; **Lascoux 1978** [record]; **Bruns–Conca–Varbaro**, arXiv:1111.7263; **Squier 1987**, JPAA
  49; **Squier–Otto–Kobayashi 1994** [record]. R1, R3, R4 and L1·3/L1·4.
- **Sakasai 2012**, arXiv:1005.5501; **Suzuki 2005**, Kobe J. Math. 22, 39–47. L1·1.
- **Morifuji–Suzuki**, arXiv:2311.15484; **Boden–Friedl II**, PJM 249; **Boden–Friedl III**, QJM 65;
  **Friedl–Vidussi**, arXiv:0905.0591. Twisted / metabelian; R2·2 closed.
- **Boyd 1981**, JNT 13; **Dubickas–Smyth 2005**, Expo. Math. 23; **Kronecker 1857**, Crelle 53. The
  M = 1 criterion; our binomial is never M = 1.
- **McMullen 2000**, Ann. ENS 33, 519–560; **Koberda**, arXiv:1110.3746; **Fried 1982**, Topology 21;
  **Turaev 2002**, AGT 2; **Kitayama 2021**, arXiv:2108.08645. Teichmüller polynomial, fibered cone,
  norms.
- **Suciu 2016** (Springer INdAM 14); **Suciu 2014** (IMRN). Jump loci; a binomial has a single
  translated subtorus.
- **Hironaka–Kin**, math/0507012; **Hironaka**, math/0506602 and math/0204040; **Silver–Williams 2005**,
  math/0509068; **Eisenbud–Neumann 1985** [record]. R2 templates.
- **Cohn 2006**; **Schrempf**, arXiv:1803.10627; **Smyth** survey, math/0701397; **Everest–Ward 1999**
  [record]; **Lind–Schmidt–Ward 1990** [record]. Free-field factorisation and Mahler complexity κ.

## 6. Leads for round 2

1. **Lothaire, *Algebraic Combinatorics on Words* (2002), Prop. 2.1.3**, and **Jenkinson–Zamboni 2004**
   ("strongly balanced"; cited in BLRS Thm 6.9). Needed to state the circular unbalance-witness lemma
   exactly for the live lever. Cheap to fetch.
2. **Knight 2023** (hal-04261183). Re-read to see whether the C9 core uses the whole Christoffel
   structure or only the balanced pair (1u0, 0u1). This decides whether the witness extension is
   natural.
3. **Abelian/additive powers in Sturmian words** (e.g. Fici et al.): for the `words` theme. In a word
   whose length-L factors take only two sum values, additive squares are forced to cluster. Combine
   with the identity S(uv) − S(vu) = (Y^L − X^s)(S(u) − S(v)) for |u| = |v| = L and equal sum s.
4. **Dejesus 2026**, "Transcendence of the 3x+1 conjugacy map on Sturmian words" (SSRN 7584439). Seen
   only as a Crossref record, so unverified. For `generalized-maps` (Bernstein–Lagarias Φ on Sturmian
   words).
5. **Hercher 2023** (in cycle-literature): the current F3/F4 calibration; it supersedes Martiny and
   Eliahou.
6. *Low:* Dehornoy, zeros of Alexander polynomials of Lorenz knots (ref. [17] in Kang–Matsusaka–Park).
   Only relevant if anyone revisits the "cycle → positive braid via the rank permutation of rotations"
   construction. No exclusion lever is known.
