# Deser, Jackiw, 't Hooft 1984: three-dimensional Einstein gravity, dynamics of flat space

- **Source.** S. Deser, R. Jackiw, G. 't Hooft, *Three-dimensional Einstein gravity: dynamics of
  flat space*, Ann. Phys. 152 (1984) 220–235, doi:10.1016/0003-4916(84)90085-X; report BRX-TH-137.
  Not on arXiv.
- **Where from.** Fetched 2026-11-22 on `node1` from Gerard 't Hooft's own publication list at
  Utrecht, <https://webspace.science.uu.nl/~hooft101/gthpub.html>, which links
  <https://webspace.science.uu.nl/~hooft101/gthpub/Deser_Jack_tH_ThreeD_Grav_1984.pdf>. OpenAlex
  also lists an open copy in the Utrecht University Repository, handle 1874/4772 (not fetched).
- **File.** `pdf/AnnPhys-152-220.pdf`, sha256 `3241aa50…6b6676` (full hash in `../README.md`).
  The publisher's scan (Academic Press) with an OCR text layer (Acrobat Capture). 16 pages.
- **Pages.** References below are to PDF pages. PDF p.n is printed p.219+n, so PDF p.1 is p.220.
- **Checking.** Every quote was found with `pdftotext -q -f N -l N` (quote 3 with `-layout`),
  whitespace normalised. The text layer is OCR. Where it garbles a symbol, the quote gives
  pdftotext's rendering exactly, as a code span, and the reading follows, marked [r].

## Verbatim quotes

1. PDF p.1, abstract: « In three spacetime dimensions, the Einstein equations imply that
   source-free regions are flat. Localized sources can therefore only affect geometry globally
   rather than locally. »
2. PDF p.1, of the static many-body solution: « whose total energy is additive and determines the
   Euler invariant of the spatial surface. »
3. PDF p.4, of the one-body metric: « and the space is a cone, the unique 2-space which is
   metrically flat except at one point-its vertex. »
4. PDF p.10, the caption of Fig. 1 (the excised wedge around a static particle), as pdftotext
   renders it: `The angle 2b is proportional to the mass: /3 = 4xGM = n( 1 - a).`
   [r] Reading: « The angle 2β is proportional to the mass: β = 4πGM = π(1 − α) », with
   α = 1 − 4Gm from eq. (2.8b) (PDF p.3, rendered `a=1-4Gm`).
5. PDF p.11: « The mass of a single point source must be less than 1/4G »
6. PDF p.11: « However, two (or more) particles may have a total mass equal or less than 1/2G. »
7. PDF p.11, of three particles closing space: « The sum of the three masses is 1/2G and space
   becomes compact »
8. PDF p.12, of eq. (5.12), the total mass of two moving particles: « it is our analog of the flat
   space relativistic mass addition formula »
9. PDF p.13: « We remark that a localized, pointlike, spinning particle would give rise to
   difficulties with causality: it would become possible to travel along a closed timelike
   contour. One can show that such closed timelike contours are not possible in a space with n
   moving spinless particles, where angular momentum is purely orbital. »
10. PDF p.13: « The most general boundary condition for spacetime surrounding any possible
    composite source can be written as » eq. (5.21), a Lorentz transformation followed by a
    translation.

## What it bears on in `../../NOTES-3+1.md` [r]

These are the planner's readings, not the paper's.

- **N5, « the deficit of a system at rest is 8πG × (its energy) (Deser–Jackiw–'t Hooft *[to
  verify]*) ».** Quote 4: the excised wedge is 2β with β = 4πGM, so the deficit is 8πGM (c = 1).
  N5's statement is DJH's normalisation.
  - Quotes 5–7 agree with it. A single mass below 1/4G is a deficit below 2π. Three masses summing
    to 1/2G give a total deficit of 4π, which is 2π·χ(S²): space closes into a sphere.
  - DJH 1992 (`../djh1992`) set G = 1/4, so there the deficit is 2πM.
- **N4, « non-additive total mass ».** Quote 8: eq. (5.12) composes two moving particles' masses
  non-additively, and DJH call it their analog of the relativistic mass addition formula. Quote 10
  says that the matching condition around any composite source is one Poincaré element. Together
  these are the 2+1 flat precursor of Theorem M's product of holonomies.
- **Gott context (N2 table, N4).** Quote 9 is the 1984 claim that Gott 1991 appeared to
  contradict. DJH 1992 say they had « stated without proof » it, and defend it by a boundary
  condition at spacelike infinity (`../djh1992/NOTE.md`).
