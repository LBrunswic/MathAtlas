# Physics references for `papers/bbs/NOTES-3+1.md` (target T-bbs-archive, partial)

These are untrusted downloads, fetched on 2026-11-22 on `node1` and stored as data only. Nothing
here has been built or executed, and the PDFs were read with `pdftotext` only. Each source has its
own directory with the PDF under `pdf/` and a `NOTE.md` of verbatim quotes, each with its PDF page.
Quotes were checked against `pdftotext -q` output, page by page.

- `cfgo1994` and `matschull1999` come from `export.arxiv.org`.
- The four journal papers come from free, legitimate copies: an author's own site, or an
  institutional repository that marks the file open. Each `NOTE.md` names the URL and the access
  statement.
- `djh1984`, `djh1992` and `thooft1993` are scans whose text layer is OCR. Where the OCR garbles a
  symbol, the note gives pdftotext's rendering and a reading marked [r].
- `thooft1992` has no text layer at all, so it has no quotes yet (see its `NOTE.md`).

This directory sits beside `../sources/`, which holds BBS and Seppi. It was created here because
the run's lease covers `papers/bbs/references` and not `papers/bbs/sources`. Moving it under
`../sources/` is the master's call.

| key | what | sha256 |
|---|---|---|
| `cfgo1994/pdf/gr-qc-9404065.pdf` | S. M. Carroll, E. Farhi, A. H. Guth, K. D. Olum, *Energy-momentum restrictions on the creation of Gott time machines*, arXiv:gr-qc/9404065 v1 (1 May 1994); Phys. Rev. D 50 (1994) 6190, doi:10.1103/PhysRevD.50.6190. 21 PDF pages, two printed pages per PDF page | `64454951189c51a333a6de549d35fc841d196451446e7ecc99399ad88974592d` |
| `matschull1999/pdf/gr-qc-9809087.pdf` | H.-J. Matschull, *Black hole creation in 2+1 dimensions*, arXiv:gr-qc/9809087 v3 (11 Dec 1998); Class. Quantum Grav. 16 (1999) 1069, doi:10.1088/0264-9381/16/3/032. 34 pages | `11dafcbf610e94f4ce5c7fdd1211d089e3fedfd091d42b4c15d3d3d3c421b27d` |
| `djh1984/pdf/AnnPhys-152-220.pdf` | S. Deser, R. Jackiw, G. 't Hooft, *Three-dimensional Einstein gravity: dynamics of flat space*, Ann. Phys. 152 (1984) 220, doi:10.1016/0003-4916(84)90085-X. From 't Hooft's Utrecht page, <https://webspace.science.uu.nl/~hooft101/gthpub/Deser_Jack_tH_ThreeD_Grav_1984.pdf>. 16 pages, OCR scan | `3241aa50a793f30ea3045f0501e14b8c91a4db5e5657dbd3e87ee851201b6676` |
| `djh1992/pdf/PhysRevLett-68-267.pdf` | S. Deser, R. Jackiw, G. 't Hooft, *Physical cosmic strings do not generate closed timelike curves*, Phys. Rev. Lett. 68 (1992) 267, doi:10.1103/PhysRevLett.68.267. From CaltechAUTHORS, <https://authors.library.caltech.edu/records/mfa99-7vv21> (files public). 3 pages | `d3c147ce8e1a8e2d7d851bc6e7df54f51b6864f3be2ebc1932340a10094cb777` |
| `thooft1992/pdf/CQG-9-1335.pdf` | G. 't Hooft, *Causality in (2+1)-dimensional gravity*, Class. Quantum Grav. 9 (1992) 1335, doi:10.1088/0264-9381/9/5/015. From the Utrecht University Repository, <https://dspace.library.uu.nl/handle/1874/4627> (Open Access (free)). 15 pages, a repository cover sheet and 14 page images; **no text layer, no quotes** | `d901e86b79307f6d3f00c136d772c9c88bc43a483aef2be400e930f73c30fef9` |
| `thooft1993/pdf/CQG-10-1023.pdf` | G. 't Hooft, *The evolution of gravitating point particles in 2+1 dimensions*, Class. Quantum Grav. 10 (1993) 1023, doi:10.1088/0264-9381/10/5/019. The second paper of CFGO's reference 17; it states the 1992 crunch result in quotable text. From 't Hooft's Utrecht page, <https://webspace.science.uu.nl/~hooft101/gthpub/evolution_2plus1_dim.pdf>. 17 pages, OCR scan | `a7832f19535ba4412eb1b7e5b5157b2a6bc927590595d0ba728606bbe2b8b15e` |

**Not archived** (checked 2026-11-22). No free, legitimate copy was found. OpenAlex marks the
first two `closed`, they are not in CaltechAUTHORS, and INSPIRE lists no open file for them:

- J. R. Gott, *Closed timelike curves produced by pairs of moving cosmic strings: exact
  solutions*, Phys. Rev. Lett. 66 (1991) 1126, doi:10.1103/PhysRevLett.66.1126. APS paywall.
- S. M. Carroll, E. Farhi, A. H. Guth, *An obstacle to building a time machine*, Phys. Rev. Lett.
  68 (1992) 263, doi:10.1103/PhysRevLett.68.263, and its erratum 68 (1992) 3368,
  doi:10.1103/PhysRevLett.68.3368; report MIT-CTP-2009. APS paywall.
  - The OSTI record 5084442 is a citation only.
  - CERN CDS answers with a bot challenge, which was not passed.
  - Its result is restated, and sharpened, in `cfgo1994`.
- The 2+1 phase-space reference of N5-4. NOTES-3+1.md does not name it. N5 has only
  « *[standard, to verify against a reference]* » after the 2-body phase-space formula, so there
  is nothing to fetch until a source is chosen.

The citations of Gott and CFG as CFGO's reference list gives them are quoted in
`cfgo1994/NOTE.md`, quote 12. Gott's is also quoted in `djh1992/NOTE.md`, quote 10.
