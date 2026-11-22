# 't Hooft 1993: the evolution of gravitating point particles in 2+1 dimensions

- **Source.** G. 't Hooft, *The evolution of gravitating point particles in 2+1 dimensions*,
  Class. Quantum Grav. 10 (1993) 1023–1038, doi:10.1088/0264-9381/10/5/019. Not on arXiv.
- **Why it is here.** It is not one of the references NOTES-3+1.md names. It is the second paper
  of CFGO's reference 17 (`../cfgo1994/NOTE.md`, quote 12), and it states 't Hooft's 1992 result
  (`../thooft1992`, whose PDF has no text layer) in text that pdftotext can read.
- **Where from.** Fetched 2026-11-22 on `node1` from Gerard 't Hooft's own publication list at
  Utrecht, <https://webspace.science.uu.nl/~hooft101/gthpub.html>, which links
  <https://webspace.science.uu.nl/~hooft101/gthpub/evolution_2plus1_dim.pdf>.
- **File.** `pdf/CQG-10-1023.pdf`, sha256 `a7832f19…b8b15e` (full hash in `../README.md`).
  17 pages. PDF p.1 is an IOPscience download sheet, which reads « The article was downloaded on
  03/12/2010 at 15:14 ». The article is a scan with an OCR text layer (Acrobat Capture 3.0).
- **Pages.** References below are to PDF pages. For n ≥ 2, PDF p.n is printed p.1021+n, so PDF
  p.2 is p.1023.
- **Checking.** Every quote was found with `pdftotext -q -f N -l N`, whitespace normalised. Where
  the OCR garbles a passage, the quote gives pdftotext's rendering as a code span, and the reading
  follows, marked [r].

## Verbatim quotes

1. PDF p.2, abstract: « A given universe may either continue to expand for ever or shrink to a
   point in a final crunch, »
2. PDF p.2, of Gott [2]: « who indicated that an isolated pair of point particles, moving rapidly
   with respect to each other, may generate a surrounding region where closed timelike »
   (the next word is rendered `CUN-`, [r] « curves »).
3. PDF p.2: « The reason why regions of spacetime with closed timelike curves cannot be generated
   in any universe with physically acceptable boundary conditions is that a Gott pair of
   particles leads to a ‘big crunch’ [3]: spacetime shrinks to a point ‘before’ any closed
   timelike curve has a chance of opening up. Any open universe with a Gott pair in it must have
   physically unacceptable boundary conditions (a closed timelike loop at the boundary). We here
   consider only closed spaces. »
4. PDF p.14: « What we have found in this way is a universe that has a finite timespan. »
5. PDF p.17, the reference list, as pdftotext renders it:
   `[31 'I Hoof1 G 1992 Class. Quantum grm. 9 1335`. [r] Reading: « [3] 't Hooft G 1992 Class.
   Quantum Grav. 9 1335 », that is, `../thooft1992`.

## What it bears on in `../../NOTES-3+1.md` [r]

These are the planner's readings, not the paper's.

- **N5, Theorem G's physical reading, « 't Hooft's resolution of Gott's time machine: the
  universe crunches before a CTC forms ».** Quote 3 is 't Hooft's own summary of his 1992 paper
  (reference [3], quote 5). It confirms N5's wording, with two qualifications.
  - It is about **closed** universes. In an open universe, a Gott pair forces unphysical
    boundary conditions instead. CFGO report the same (`../cfgo1994/NOTE.md`, quotes 7 and 11).
  - The crunch is global: the whole closed universe shrinks to a point. Theorem G's BTZ-like
    singularity is local to the interaction. The comparison in N5 is an analogy, not the same
    statement.
