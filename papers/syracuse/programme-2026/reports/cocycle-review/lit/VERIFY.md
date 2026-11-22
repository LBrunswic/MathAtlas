# Verification of the cocycle-review bibliography

Checked on 2026-10-30: every entry marked `"verified": true` in the 7 `bib-*.jsonl` files (350 entries). The `bib-*.jsonl` files were not edited. There is one result line per entry in `verify.jsonl`.

## Method

- arXiv: the abs page metadata (title, authors, abstract). When a quote was not in the abstract, the full PDF text was searched.
- DOIs: the Crossref metadata (title, authors, year, venue). Every DOI was also confirmed as registered through the doi.org handle API. DataCite was used for Zenodo and ResearchGate DOIs.
- zbMATH: records from the zbMATH Open API, looked up by AN and by DOI (`en:`), including the review text. The OEIS and HAL APIs were used for those sites.
- Other URLs were fetched and their title checked. Linked PDFs were converted with pdftotext.
- Quotes were normalized (lowercase, TeX, accents and punctuation stripped) and matched as word 4-grams. Math symbols are not compared. A quote counts as located when at least 85% of its words are covered and no gap is longer than 4 words. Every residue was checked by hand.
- `unreachable_but_exists`: the publisher URL returned 403 or 429 to automated clients, but Crossref confirms the paper and the quote was located elsewhere. These entries can stay in the report.

## Counts per file

| file | ok | unreachable_but_exists | quote_not_found | title_mismatch | metadata_mismatch | url_dead | total |
|---|---|---|---|---|---|---|---|
| bib-arithmetic.jsonl | 49 | 1 | 0 | 11 | 1 | 0 | 62 |
| bib-chase-arithmetic.jsonl | 36 | 0 | 0 | 3 | 0 | 0 | 39 |
| bib-chase-words-limits.jsonl | 41 | 1 | 0 | 0 | 0 | 0 | 42 |
| bib-frames.jsonl | 34 | 1 | 0 | 0 | 0 | 0 | 35 |
| bib-generalized-maps.jsonl | 34 | 2 | 0 | 12 | 0 | 0 | 48 |
| bib-queue.jsonl | 76 | 0 | 1 | 0 | 1 | 0 | 78 |
| bib-words.jsonl | 46 | 0 | 0 | 0 | 0 | 0 | 46 |
| **total** | 316 | 5 | 1 | 26 | 2 | 0 | 350 |

## Entries to EXCLUDE (or fix before citing)

### Wrong link: the URL points to an unrelated paper (three EuDML IDs that look invented; the cited papers themselves are real) (3)

- `bib-generalized-maps.jsonl` line 20 `simons2008generalized`: WRONG LINK: eudml.org/doc/278329 is "An application of a lower bound for linear forms in two logarithms to the Terai-Jesmanowicz conjecture", a different paper. The cited paper exists (Crossref 10.4064/aa131-3-2, Acta Arith. 2008); quote is a tagged Lagarias annotation, verified in arXiv:math/0608208
- `bib-generalized-maps.jsonl` line 21 `simons2008exotic`: WRONG LINK: eudml.org/doc/278274 is Y. Sasaki, "Multiple zeta values for coordinatewise limits at non-positive integers" (Acta Arith. 136, 2009). The cited paper exists (Crossref 10.4064/aa134-3-1); quote is a tagged Lagarias annotation, verified
- `bib-generalized-maps.jsonl` line 22 `belaga2003perigees`: WRONG LINK: eudml.org/doc/278601 is "Sur les modules d'Iwasawa des Zp*/{+-1}-extensions", a different paper. The cited paper exists (Crossref 10.4064/aa106-2-9); quote is a tagged Lagarias annotation, verified

### Link is a secondary source: the paper and the quote are real, but the URL is another document (fix by linking the primary) (23)

- `bib-arithmetic.jsonl` line 1 `bugeaud2003gcd`: LINK IS A SECONDARY SOURCE: URL is arXiv:2207.14432 (Huang-Levin, "Greatest Common Divisors on the Complement of Numerically Parallel Divisors"), not the cited paper; quote is Huang-Levin's restatement (Thm 1.1), located in its full text. Paper itself exists: Math. Z. 243 (2003) 79-84, Zbl 1021.11001 (same paper is linked correctly in bib-frames line 33). Fix: point URL at the primary; same paper also at bib-frames.jsonl:33
- `bib-arithmetic.jsonl` line 3 `hernandez2003largest`: LINK IS A SECONDARY SOURCE: URL is arXiv:0907.2098 (Bilu, Bourbaki survey "The many faces of the Subspace Theorem"), not the cited paper; quote verbatim in that secondary source. Paper itself exists: Zbl 1108.11030 (linked correctly in bib-chase-arithmetic line 10). Fix: point URL at the primary; same paper also at bib-chase-arithmetic.jsonl:10
- `bib-arithmetic.jsonl` line 4 `levin2019gcd`: LINK IS A SECONDARY SOURCE: URL is arXiv:1903.03876 (Levin-Wang, "Greatest common divisors of analytic functions and Nevanlinna theory on algebraic tori" = levin2020analytic, line 10), not the cited paper; quote is the restatement of Thm 1.12(a), located in the Levin-Wang full text up to math symbols. Paper itself exists: Crossref 10.1007/s00222-018-0831-z, Invent. Math. 215 (2019). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 23 `gross2013factorization`: LINK IS A SECONDARY SOURCE: URL is arXiv:1708.08290 (Bugeaud-Evertse-Gyory 2018, "S-parts of values of univariate polynomials..."), not the cited paper; quote is from the BEG abstract. Paper itself exists: Crossref 10.1142/S179304211350022X (authors Samuel S. Gross, Andrew F. Vincent). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 26 `laurent1984equations`: LINK IS A SECONDARY SOURCE: URL is arXiv:0704.1747 (Aliev-Smyth, "Solving algebraic equations in roots of unity"), not the cited paper; quote is from the Aliev-Smyth abstract. Paper itself exists: Crossref 10.1007/BF01388597, Invent. Math. 78 (1984). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 28 `bombieri1999intersecting`: LINK IS A SECONDARY SOURCE: URL is the abstract of Bombieri-Masser-Zannier 2008 (Ann. SNS Pisa), a different paper, not the cited paper; quote verbatim in that secondary source. Paper itself exists: DOI 10.1155/S1073792899000628 registered (Crossref: BMZ, 1999; title missing in the deposit). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 32 `zsigmondy1892potenzreste`: LINK IS A SECONDARY SOURCE: URL is arXiv:1504.02598 (Glasby-Luebeck-Niemeyer-Praeger), not the cited paper; quote verbatim in that secondary source. Paper itself exists: Crossref 10.1007/BF01692444, Monatsh. Math. Phys. 3 (1892). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 34 `stewart1977divisors`: LINK IS A SECONDARY SOURCE: URL is arXiv:1008.1274 (Stewart 2013, "On divisors of Lucas and Lehmer numbers"); the automatic title check passed only because the titles overlap, not the cited paper; quote is from the 2013 paper's introduction. Paper itself exists: Crossref 10.1112/plms/s3-35.3.425, Proc. LMS 1977. Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 36 `schinzel1962primitive`: LINK IS A SECONDARY SOURCE: URL is arXiv:1008.1274 (Stewart 2013), not the cited paper; quote verbatim in that secondary source. Paper itself exists: Crossref 10.1017/S0305004100040561 (pages 556-562 per Crossref, entry says 555-562). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 44 `pillai1945equation`: LINK IS A SECONDARY SOURCE: URL is Bennett's PDF of "Pillai's conjecture revisited" (J. Number Theory 98 (2003)), not the cited paper; quote verbatim in that secondary source. Paper itself exists: Zbl 0063.06245, Bull. Calcutta Math. Soc. 37, 15-20 (1945). Fix: point URL at the primary.
- `bib-arithmetic.jsonl` line 45 `stroeker1982diophantine`: LINK IS A SECONDARY SOURCE: URL is Bennett's PDF of "Pillai's conjecture revisited"; the automatic check passed only because the generic title "Diophantine equations" occurs in it, not the cited paper; quote verbatim in that secondary source. Paper itself exists: Zbl 0521.10013 (linked correctly in bib-queue line 19). Fix: point URL at the primary; same paper also at bib-queue.jsonl:19
- `bib-chase-arithmetic.jsonl` line 33 `rozier1990circuits`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: attested only by Lagarias (not in zbMATH or Crossref). Fix: point URL at the primary.
- `bib-chase-arithmetic.jsonl` line 34 `rozier1991majorations`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: attested only by Lagarias (not in zbMATH or Crossref). Fix: point URL at the primary.
- `bib-chase-arithmetic.jsonl` line 35 `farruggia1996elimination`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Zbl 0863.11013, Pi Mu Epsilon J. 10 (1996) 275-280. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 6 `conway1972unpredictable`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Zbl 0337.10041, Proc. 1972 Number Theory Conf., Boulder. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 7 `conway1987fractran`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Crossref 10.1007/978-1-4612-4808-8_2. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 13 `franco1990thesis`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: attested only by Lagarias (thesis not in zbMATH or Crossref). Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 14 `moller1978hasse`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Crossref 10.4064/aa-34-3-219-226, Zbl 0329.10008. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 15 `matthews1984hasse`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Crossref 10.4064/aa-43-2-167-175. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 16 `matthews1985markov`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Crossref 10.4064/aa-45-1-29-42. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 27 `monks2002minus`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography II (arXiv:math/0608208), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: Zbl 1014.68094, DMTCS 5 (2002) 47-54. Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 29 `keller1999finite`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: attested only by Lagarias (not in zbMATH). Fix: point URL at the primary.
- `bib-generalized-maps.jsonl` line 46 `wirsching1998dynamical`: LINK IS A SECONDARY SOURCE: URL is Lagarias annotated bibliography I (arXiv:math/0309224), not the cited paper; quote is Lagarias's annotation, verified there. Paper itself exists: LNM 1681, Crossref 10.1007/BFb0095985 (linked correctly in bib-queue line 9). Fix: point URL at the primary; same paper also at bib-queue.jsonl:9

### Metadata mismatch: the link is right, but the title or venue disagrees with it (2)

- `bib-arithmetic.jsonl` line 70 `jha2026upper`: Repo, PDF and Zenodo DOI 10.5281/zenodo.23256301 are real, but the work is titled "Rational approximation to log2 3" (R. K. Jha, 2026), not the listed title; the quote is a truncated README fragment ("For theta = log(3)/log(2), the paper establishes"); unrefereed
- `bib-queue.jsonl` line 21 `ouaknine2012decision`: URL doi:10.29007/tpxx is the EPiC Series in Computing vol. 15 talk abstract (sole author Ouaknine), while the metadata cite RP 2012, LNCS 7550, 21-28 (Ouaknine & Worrell, DOI 10.1007/978-3-642-33512-9_3). The quote is verbatim in the EPiC abstract. Fix: make the URL and the venue agree

### Quote not found: the source is real, the quote is unverified (replace it) (1)

- `bib-queue.jsonl` line 8 `everett1977iteration`: Paper confirmed (Crossref, Zbl 0352.10001). The quote is not verbatim in any reachable text: the zbMATH review reads "It is shown that for almost all m (in the natural density sense) there exists an integer k such that f^k(m)<m"; Lagarias bib I #57 has different wording. Likely a paraphrase; use the zbMATH wording instead

## Reachable only indirectly (keep; link blocked to scripts)

- `bib-arithmetic.jsonl` line 57 `wu2003linear`: ams.org returns 403 to automated clients (path matches the DOI target); Crossref confirms title/author/venue; quote verbatim in the Crossref abstract
- `bib-chase-words-limits.jsonl` line 6 `reutenauer2019christoffel`: OUP DOI page returns 403; Crossref confirms the chapter "Conjugates and Factors" in From Christoffel Words to Markoff Numbers; quote verbatim in the Crossref abstract
- `bib-frames.jsonl` line 25 `bourgain2009effective`: EPFL returned HTTP 429 (rate limit) on every attempt; Crossref confirms; the quoted theorem is located in the Cambridge open PDF
- `bib-generalized-maps.jsonl` line 11 `crandall1978qx`: ams.org returns 403 to automated clients (path matches the DOI target); Crossref confirms; quote is a tagged Lagarias annotation, verified in arXiv:math/0309224
- `bib-generalized-maps.jsonl` line 19 `simons2007inductive`: sciencedirect returns 403 (PII matches the DOI target); Crossref confirms; quote is a tagged Lagarias annotation, verified in arXiv:math/0608208

## Other observations (entries are ok)

- Some `ok` quotes come from a secondary source, not from the paper itself. The notes say which: tagged Lagarias annotations (generalized-maps), zbMATH reviews, the Smyth 1981 abstract for kronecker1857zwei and boyd1981kronecker, the Hillman-Livingston-Naik abstract for murasugi1971periodic, the Berstel et al. book for berstel1997sturmian, and the zbMATH review of Bennett 2003 for queue:19.
- Cross-file duplicates (the same paper in several themes) are listed in the notes. The ones with different ids are yolcu2021automated/yolcu2023automated, lagarias2021overview/lagarias2010overview, bennett2003revisited/bennett2003pillai, aliev2007torsion/aliev2007solving, kontorovich2002structure/kontorovich2002sinai, tao2011collatzlo/tao2011collatz and lam1995vanishing/lam2000vanishing. kaneda2015two has year 2010 in chase-arithmetic and 2015 in chase-words-limits.
- Minor metadata differences, not excluded: schinzel1962 pages (Crossref: 556-562), crochemore1991twoway pages (Crossref: 650-674), jenkinson2006ergodic volume (zbMATH: 15, Crossref: 16), and the Crossref print or online year differing by one for a few entries.
- Unrefereed items that are cited correctly: m4cd4r42026spectral (claim retracted), merle2026nocycle (erratum), merle2026obstruction, and jha2026upper (excluded above for its wrong title).
